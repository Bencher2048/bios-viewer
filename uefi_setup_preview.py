# -*- coding: utf-8 -*-
"""UEFI Setup Preview / Validator v2.4.1-stable
Windows 7-friendly (Python 3.8 + Tkinter, no pip dependencies).
Reads IFR text directly or a BIOS image through UEFIExtract + IFRExtractor-RS.
Viewer/simulator only: it never writes to the BIOS image.
"""
from __future__ import print_function
import os, re, sys, hashlib, tempfile, shutil, subprocess, threading, traceback, time, struct, zlib, base64
try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox, simpledialog
except Exception:
    raise

APP = "UEFI Setup Preview / Validator"
VER = "2.4.1-stable"

RE_HEX = r"0x[0-9A-Fa-f]+"

def log(msg):
    try:
        print("[%s] %s" % (time.strftime("%H:%M:%S"), msg), flush=True)
    except Exception:
        pass

def hx(s, default=None):
    try: return int(s, 16)
    except Exception: return default

def _unescape_hii(s):
    """Decode only escapes used by IFR output, without unicode_escape warnings."""
    def repl(m):
        x=m.group(1)
        if x=='n': return '\n'
        if x=='r': return '\r'
        if x=='t': return '\t'
        if x=='"': return '"'
        if x=="'": return "'"
        if x=='\\': return '\\'
        if x.startswith('x') and len(x)==3:
            try: return chr(int(x[1:],16))
            except Exception: return '\\'+x
        return '\\'+x
    return re.sub(r'\\(x[0-9A-Fa-f]{2}|n|r|t|"|\'|\\|.)', repl, s)

def attr(line, name):
    m = re.search(r'\b'+re.escape(name)+r':\s*("(?:[^"\\]|\\.)*"|0x[0-9A-Fa-f]+|\d+)', line)
    if not m: return None
    v=m.group(1)
    if v.startswith('"'):
        return _unescape_hii(v[1:-1])
    return v

def quoted_after(line, key):
    m=re.search(re.escape(key)+r':\s*"((?:[^"\\]|\\.)*)"', line)
    if not m:return ""
    return _unescape_hii(m.group(1))

class Node(object):
    def __init__(self, kind, line_no, raw, depth=0):
        self.kind=kind; self.line_no=line_no; self.raw=raw; self.depth=depth
        self.offset=None; self.prompt=""; self.help=""; self.qid=None; self.form_id=None
        self.varstore=None; self.varoffset=None; self.size=None; self.min=None; self.max=None; self.step=None
        self.options=[]; self.children=[]; self.parent=None; self.condition=[]; self.hidden_always=False
        self.target_form=None; self.value=None; self.visibility_scopes=[]
        self.display_min=None; self.display_max=None; self.display_step=None; self.display_standard=None; self.display_unit=""
    def label(self): return self.prompt or ("Form 0x%X"%self.form_id if self.form_id is not None else self.kind)

class IFRModel(object):
    def __init__(self, text="", source=""):
        self.source=source; self.text=text; self.forms=[]; self.form_by_id={}; self.nodes=[]; self.varstores={}; self.warnings=[]
        self.values={}; self.question_by_id={}; self.bios_meta={}; self.modified_qids=set()
        if text: self.parse(text)

    def parse(self,text):
        lines=text.splitlines(); stack=[]; suppress_stack=[]; current_q=None
        records=[]; cur=None
        for i,raw in enumerate(lines,1):
            m=re.match(r'^(0x[0-9A-Fa-f]+):[ ]*(\t*)(.*)$',raw)
            if m:
                if cur: records.append(cur)
                cur=[i,m.group(1),m.group(2),m.group(3)]
            elif cur is not None:
                cur[3] += "\n" + raw
        if cur: records.append(cur)
        for i,offs,tabs,body0 in records:
            off=hx(offs); body=body0.strip(); depth=len(tabs)
            while stack and stack[-1][0] >= depth: stack.pop()
            while suppress_stack and suppress_stack[-1][0] >= depth: suppress_stack.pop()

            kind=None
            for k in ("FormSet","Form","SuppressIf","GrayOutIf","DisableIf","OneOfOption","OneOf","Numeric","CheckBox","String","Ref","Action","Text","Subtitle","OrderedList","Password","Date","Time","VarStore"):
                if body.startswith(k+" ") or body.startswith(k+"{") or body==k:
                    kind=k; break
            if body.startswith("End ") or body=="End":
                continue

            if kind=="VarStore":
                sid=attr(body,"VarStoreId"); name=attr(body,"Name")
                if sid: self.varstores[hx(sid)]=name or sid
                continue

            if kind in ("SuppressIf","GrayOutIf","DisableIf"):
                n=Node(kind,i,body,depth); n.offset=off; self.nodes.append(n)
                if stack: n.parent=stack[-1][1]; stack[-1][1].children.append(n)
                suppress_stack.append((depth,n)); stack.append((depth,n)); continue

            if suppress_stack and kind is None:
                op=body.split()[0] if body else ""
                if op in ("True","False","EqIdVal","EqIdValList","Not","And","Or","QuestionRef1","Uint8","Uint16","Uint32","Uint64","Equal","NotEqual","GreaterThan","GreaterEqual","LessThan","LessEqual"):
                    suppress_stack[-1][1].condition.append(body)
                continue

            if kind=="OneOfOption":
                if current_q is not None:
                    label=quoted_after(body,"Option"); mv=re.search(r'Value:\s*(0x[0-9A-Fa-f]+|\d+)',body)
                    val=int(mv.group(1),0) if mv else len(current_q.options)
                    current_q.options.append((label,val,"Default" in body))
                    if "Default" in body and current_q.qid is not None and current_q.qid not in self.values: self.values[current_q.qid]=val
                continue

            if kind is None: continue
            n=Node(kind,i,body,depth); n.offset=off
            n.prompt=quoted_after(body,"Prompt"); n.help=quoted_after(body,"Help")
            if kind in ("Form","FormSet") and not n.prompt:
                n.prompt=quoted_after(body,"Title")
            self._parse_display_range(n)
            for nm,field,conv in [("QuestionId","qid",hx),("FormId","form_id",hx),("VarStoreId","varstore",hx),("VarOffset","varoffset",hx),("VarStoreInfo","varoffset",hx),("Size","size",lambda x:int(x,0)),("Min","min",hx),("Max","max",hx),("Step","step",hx)]:
                v=attr(body,nm)
                if v is not None:
                    try:setattr(n,field,conv(v))
                    except Exception:pass
            if kind=="Ref":
                tf=attr(body,"FormId"); n.target_form=hx(tf) if tf else None
            n.visibility_scopes=[x[1] for x in suppress_stack]
            if any(self._cond_is_literal_true(s.condition) for s in n.visibility_scopes): n.hidden_always=True
            if stack: n.parent=stack[-1][1]; stack[-1][1].children.append(n)
            self.nodes.append(n)
            if kind=="Form":
                self.forms.append(n)
                if n.form_id is not None:self.form_by_id[n.form_id]=n
            if n.qid is not None:
                self.question_by_id[n.qid]=n
                if n.qid not in self.values:
                    if kind=="CheckBox": self.values[n.qid]=0
                    elif kind=="Numeric": self.values[n.qid]=n.min or 0
                    elif kind=="OneOf": self.values[n.qid]=n.min or 0
            current_q = n if kind in ("OneOf","Numeric","CheckBox","String","OrderedList") else None
            if kind in ("FormSet","Form","OneOf","Numeric","CheckBox","String","Ref","Action","Text","Subtitle","OrderedList","Password","Date","Time"):
                stack.append((depth,n))

        for n in self.nodes:
            if n.qid is not None and n.options:
                defaulted=False
                for lab,val,default in n.options:
                    if default:self.values[n.qid]=val;defaulted=True;break
                if not defaulted and n.qid not in self.values:self.values[n.qid]=n.options[0][1]
            if n.kind=="Ref" and n.target_form is not None and n.target_form not in self.form_by_id:
                self.warnings.append("Broken Ref at IFR line %d -> FormId 0x%X"%(n.line_no,n.target_form))
        if not self.forms:self.warnings.append("No Form opcodes found")

    @staticmethod
    def _parse_display_range(n):
        """Parse vendor Help strings such as Min.: 0.600V | Max.: 1.700V | Increment: 0.005V.
        These ranges are frequently the real user-facing limits for AMI String-backed controls.
        """
        txt=n.help or ''
        if not txt: return
        def grab(key):
            m=re.search(r'\b'+key+r'\s*[:=]\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+))\s*([^\s|,;]*)',txt,re.I)
            if not m:return None,None
            try:v=float(m.group(1))
            except Exception:return None,None
            return v,(m.group(2) or '')
        mn,u1=grab(r'(?:Min\.?|Minimum)')
        mx,u2=grab(r'(?:Max\.?|Maximum)')
        stp,u3=grab(r'(?:Increment|Step)')
        sm=re.search(r'\bStandard\s*:\s*([^|\r\n]+)',txt,re.I)
        if mn is not None:n.display_min=mn
        if mx is not None:n.display_max=mx
        if stp is not None:n.display_step=stp
        n.display_unit=u2 or u1 or u3 or ''
        if sm:n.display_standard=sm.group(1).strip()

    @staticmethod
    def _fmt_num(v):
        if v is None:return ''
        if abs(v-round(v)) < 1e-10:return str(int(round(v)))
        return ('%.8f'%v).rstrip('0').rstrip('.')

    def display_range_text(self,n):
        if n.display_min is not None and n.display_max is not None:
            u=n.display_unit or ''
            a=self._fmt_num(n.display_min)+u; b=self._fmt_num(n.display_max)+u
            st=''
            if n.display_step is not None: st='; step '+self._fmt_num(n.display_step)+u
            return a+' .. '+b+st
        if n.min is not None and n.max is not None:
            st='' if n.step is None else '; step '+str(n.step)
            return str(n.min)+' .. '+str(n.max)+st
        return ''

    @staticmethod
    def _cond_is_literal_true(ops):
        return len(ops)==1 and ops[0].startswith("True")

    def eval_condition(self, ops):
        """Evaluate the common IFR postfix expression operators used by SuppressIf/GrayOutIf/DisableIf.
        Returns None when an operator is unknown instead of inventing a result.
        """
        if not ops:return None
        st=[]
        try:
            for s in ops:
                op=s.split()[0]
                if op=='True': st.append(True)
                elif op=='False': st.append(False)
                elif op=='EqIdVal':
                    q=re.search(r'QuestionId:\s*(0x[0-9A-Fa-f]+)',s); v=re.search(r'Value:\s*(0x[0-9A-Fa-f]+|\d+)',s)
                    st.append(self.values.get(hx(q.group(1)))==int(v.group(1),0) if q and v else False)
                elif op=='EqIdValList':
                    q=re.search(r'QuestionId:\s*(0x[0-9A-Fa-f]+)',s); vs=re.search(r'Values:\s*\[([^\]]*)\]',s)
                    vals=[]
                    if vs:
                        for x in vs.group(1).split(','):
                            x=x.strip()
                            if x: vals.append(int(x,0))
                    st.append(self.values.get(hx(q.group(1))) in vals if q else False)
                elif op in ('QuestionRef1','QuestionRef2'):
                    q=re.search(r'QuestionId:\s*(0x[0-9A-Fa-f]+)',s)
                    if not q:return None
                    st.append(self.values.get(hx(q.group(1)),0))
                elif op in ('Uint8','Uint16','Uint32','Uint64'):
                    v=re.search(r'Value:\s*(0x[0-9A-Fa-f]+|\d+)',s)
                    if not v:return None
                    st.append(int(v.group(1),0))
                elif op=='Not' and st: st.append(not bool(st.pop()))
                elif op in ('And','Or') and len(st)>=2:
                    b=bool(st.pop());a=bool(st.pop());st.append(a and b if op=='And' else a or b)
                elif op in ('Equal','NotEqual','GreaterThan','GreaterEqual','LessThan','LessEqual') and len(st)>=2:
                    b=st.pop();a=st.pop()
                    if op=='Equal':v=(a==b)
                    elif op=='NotEqual':v=(a!=b)
                    elif op=='GreaterThan':v=(a>b)
                    elif op=='GreaterEqual':v=(a>=b)
                    elif op=='LessThan':v=(a<b)
                    else:v=(a<=b)
                    st.append(v)
                else:return None
            return bool(st[-1]) if st else None
        except Exception:return None

    def visibility(self,n):
        unknown=False
        for s in getattr(n,'visibility_scopes',[]):
            v=self.eval_condition(s.condition)
            if v is True:return "hidden"
            if v is None:unknown=True
        return "conditional" if unknown else "visible"

    def navigation_score(self):
        """Score how likely this IFR is the motherboard's primary Setup rather than an auxiliary HII app."""
        titles=[(f.label() or '').strip().lower() for f in self.forms]
        prompts=[(n.prompt or '').strip().lower() for n in self.nodes if n.prompt]
        corpus='\n'.join(titles+prompts[:8000])
        pos=(
            ('main',350),('advanced',320),('boot',300),('save & exit',320),('exit',100),
            ('monitor',180),('tool',160),('ai tweaker',420),('extreme tweaker',420),
            ('overclocking performance menu',350),('security',120),('chipset',100),
            ('cpu configuration',100),('dram',40),('bclk',40)
        )
        neg=(('intel(r) rapid storage',-900),('rapid storage technology',-900),('optane',-650),
             ('create raid volume',-500),('physical disk info',-350),('raid volume info',-350),
             ('network stack',-120),('nvme configuration',-60))
        score=0
        for k,w in pos:
            if k in corpus: score+=w
        for k,w in neg:
            if k in corpus: score+=w
        # Primary Setup normally has many forms/questions plus several recognizable top pages.
        score += min(len(self.forms),250)*4 + min(len(self.question_by_id),5000)//5
        distinct=sum(1 for k in ('main','advanced','boot','monitor','tool','save & exit','ai tweaker','extreme tweaker') if any(k in t for t in titles))
        score += distinct*120
        return score

    def primary_navigation(self):
        """Return ordered (caption, form) pages from a root Setup form when possible."""
        wanted=('my favorites','main','ai tweaker','extreme tweaker','advanced','monitor','boot','tool','save & exit','exit','security')
        candidates=[]
        for f in self.forms:
            items=[]
            def walk(n):
                for c in n.children:
                    if c.kind in ('SuppressIf','GrayOutIf','DisableIf'): walk(c)
                    elif c.kind=='Ref' and c.target_form in self.form_by_id: items.append(c)
            walk(f)
            if len(items)<3: continue
            names=[(r.prompt or self.form_by_id[r.target_form].label() or '').strip() for r in items]
            low=[x.lower() for x in names]
            hits=sum(1 for w in wanted if any((x==w or w in x) for x in low))
            # 'Setup' roots with many recognizable refs are preferred.
            sc=hits*200+len(items)*5+(150 if (f.label() or '').strip().lower()=='setup' else 0)
            if hits>=3:candidates.append((sc,f,items))
        if not candidates:return []
        _,root,items=max(candidates,key=lambda x:x[0])
        out=[];seen=set()
        for r in items:
            tf=self.form_by_id.get(r.target_form)
            if not tf or id(tf) in seen:continue
            cap=(r.prompt or tf.label() or '').strip()
            if not cap:continue
            seen.add(id(tf));out.append((cap,tf))
        return out

    def summary(self):
        qs=[n for n in self.nodes if n.qid is not None]
        refs=[n for n in self.nodes if n.kind=="Ref"]
        always=sum(1 for n in qs if self.visibility(n)=="hidden")
        cond=sum(1 for n in qs if self.visibility(n)=="conditional")
        return {"forms":len(self.forms),"questions":len(qs),"refs":len(refs),"hidden_now":always,"conditional":cond,"warnings":len(self.warnings)}

class ToolRunner(object):
    def __init__(self, app=None): self.app=app
    def status(self,s):
        log(s)
        if self.app is not None:
            try:self.app.after(0,lambda x=s:self.app.status.set(x))
            except Exception:pass
    @staticmethod
    def run(cmd,cwd=None,timeout=120):
        log("CMD: "+' '.join('"%s"'%x if ' ' in str(x) else str(x) for x in cmd))
        startup=None
        if os.name=='nt':
            startup=subprocess.STARTUPINFO(); startup.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        p=subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,universal_newlines=True,
                         errors='replace' if sys.version_info >= (3,6) else None,timeout=timeout,startupinfo=startup)
        out=p.stdout or ''
        log("Exit code: %s"%p.returncode)
        if out.strip():
            for line in out.rstrip().splitlines()[-25:]: log("  "+line)
        return p.returncode,out

class App(tk.Tk):
    def __init__(self):
        tk.Tk.__init__(self); self.title('MAXSUN / AMI BIOS Graphical Preview '+VER); self.geometry("1360x800"); self.minsize(960,600)
        self.model=None; self.path=None; self.show_hidden=tk.BooleanVar(value=False); self.status=tk.StringVar(value="Готово"); self.cache_dir=tempfile.mkdtemp(prefix="uefi_preview_cache_")
        self._build(); self.bind_all('<Control-o>',lambda e:self.open_any()); self.bind_all('<Control-f>',lambda e:self.focus_search()); self.bind_all('<F5>',lambda e:self.refresh_preview())
        log(APP+" "+VER+" started; Python "+sys.version.split()[0]); self.protocol("WM_DELETE_WINDOW", self._close_app)

    def _build(self):
        top=ttk.Frame(self); top.pack(fill='x',padx=6,pady=5)
        ttk.Button(top,text="Открыть BIOS / Setup / IFR",command=self.open_any).pack(side='left')
        ttk.Button(top,text="Открыть Setup PE32",command=self.open_setup).pack(side='left',padx=4)
        ttk.Button(top,text="Проверить инструменты",command=self.check_tools).pack(side='left',padx=4)
        ttk.Button(top,text="Отчёт",command=self.show_report).pack(side='left',padx=4)
        ttk.Button(top,text="Открыть графический BIOS",command=self.open_simulator).pack(side='left',padx=4)
        ttk.Checkbutton(top,text="Показывать скрытые (диагностика)",variable=self.show_hidden,command=self.refresh_preview).pack(side='left',padx=12)
        ttk.Label(top,text="Поиск:").pack(side='left',padx=(12,2)); self.search=tk.StringVar(); e=ttk.Entry(top,textvariable=self.search,width=32);e.pack(side='left');e.bind('<Return>',self.do_search);self.search_entry=e
        ttk.Label(top,textvariable=self.status).pack(side='right')
        pw=ttk.Panedwindow(self,orient='horizontal');pw.pack(fill='both',expand=True,padx=6,pady=(0,6))
        lf=ttk.Frame(pw);cf=ttk.Frame(pw);rf=ttk.Frame(pw);pw.add(lf,weight=2);pw.add(cf,weight=4);pw.add(rf,weight=3)
        ttk.Label(lf,text="Формы / разделы").pack(anchor='w'); self.tree=ttk.Treeview(lf,show='tree');self.tree.pack(fill='both',expand=True);self.tree.bind('<<TreeviewSelect>>',self.on_form)
        ttk.Label(cf,text="Предпросмотр страницы").pack(anchor='w'); self.preview=tk.Listbox(cf,activestyle='dotbox',font=('Segoe UI',10));self.preview.pack(fill='both',expand=True);self.preview.bind('<<ListboxSelect>>',self.on_item);self.preview.bind('<Double-Button-1>',self.activate);self.preview.bind('<Return>',self.activate);self.preview.bind('<space>',self.activate);self.preview.bind('<Right>',self.activate);self.preview.bind('<Left>',self.activate_reverse)
        ttk.Label(rf,text="Свойства").pack(anchor='w'); self.props=tk.Text(rf,wrap='word',state='disabled',font=('Consolas',9));self.props.pack(fill='both',expand=True)
        self.preview_nodes=[]; ttk.Label(self,text="Клавиши: ↑/↓ — выбор, Enter/Space — переключить, ←/→ — изменить, Ctrl+F — поиск, F5 — обновить",anchor='w').pack(fill='x',padx=8,pady=(0,5))

    def _close_app(self):
        try: shutil.rmtree(self.cache_dir)
        except Exception: pass
        self.destroy()

    @staticmethod
    def _extract_text_strings(data):
        out=[]
        try:
            out += [x.decode('latin1','ignore') for x in re.findall(rb'[ -~]{5,}', data)]
            # UTF-16LE readable strings
            for m in re.finditer(rb'(?:[ -~]\x00){5,}', data):
                try: out.append(m.group(0).decode('utf-16le','ignore'))
                except Exception: pass
        except Exception: pass
        return out

    def _detect_bios_identity(self, path, hint_name=""):
        meta={'source_type':'full_bios','vendor':'AMI','family':'Generic','board':'','assets':[], 'modules':[], 'theme_source':'generated'}
        try:
            data=open(path,'rb').read()
            meta['sha256']=hashlib.sha256(data).hexdigest(); meta['size']=len(data)
            strings=self._extract_text_strings(data)
            joined=('\n'.join(strings[:25000])+'\n'+str(hint_name)).upper()
            # Identity detection must cope with vendor filenames that omit spaces/hyphens
            # (for example MsB760MGamingWifiAceD4II_B2.3D.rom).
            compact=re.sub(r'[^A-Z0-9]+','',joined)
            hint_compact=re.sub(r'[^A-Z0-9]+','',str(hint_name).upper())
            maxsun_markers=('CHALLENGER','TERMINATOR','ICRAFT','ICAFE','ESPORT','PCFARM','MODT',
                            'GAMINGWIFIACE','GAMINGACE','GAMINGWIFIICE','GAMINGICE',
                            'WORKSTATION','AIMICROSTATION')
            # Official MAXSUN files usually begin with MS and may put the chipset between MS
            # and the series name (e.g. MSB760MGAMINGWIFIACE...). Prefer that filename signal
            # over incidental vendor strings embedded in option ROMs.
            if hint_compact.startswith('MS') and any(k in hint_compact for k in maxsun_markers):
                meta['vendor']='MAXSUN'
            else:
                tests=[
                    ('MAXSUN',('MAXSUN','MAXSUNCOMPUTER','MSCHALLENGER','MSTERMINATOR','MSICRAFT','MSICAFE',
                               'MSESPORT','MSPCFARM','MSMODT','MSGAMINGWIFIACE','MSGAMINGACE',
                               'MSGAMINGWIFIICE','MSGAMINGICE','MSWORKSTATION','MSAIMICROSTATION')),
                    ('ASUS',('ASUSTEK','ASUS','ROG','TUFGAMING','PRIME')),
                    ('MSI',('MICROSTAR','MSI','CLICKBIOS')),
                    ('GIGABYTE',('GIGABYTE','AORUS')),
                    ('ASROCK',('ASROCK','TAICHI','PHANTOMGAMING')),
                    ('BIOSTAR',('BIOSTAR',)),('COLORFUL',('COLORFUL',))]
                for vendor,keys in tests:
                    if any(re.sub(r'[^A-Z0-9]+','',k) in compact for k in keys):
                        meta['vendor']=vendor; break

            # Family detection is vendor-scoped so an unrelated string from an embedded
            # option ROM cannot turn a MAXSUN board into TUF/ROG/etc.
            fam='Generic'
            if meta['vendor']=='MAXSUN':
                famtests=[
                    ('iCraft',('ICRAFT',)),
                    ('Gaming ACE',('GAMINGWIFIACE','GAMINGACE')),
                    ('Gaming ICE',('GAMINGWIFIICE','GAMINGICE')),
                    ('Challenger',('CHALLENGER',)),('Terminator',('TERMINATOR',)),
                    ('i-Cafe',('ICAFE',)),('eSport',('ESPORT',)),('PC Farm',('PCFARM',)),
                    ('MoDT',('MODT',)),('Workstation',('WORKSTATION',)),
                    ('AI Micro Station',('AIMICROSTATION',))]
                source=hint_compact + compact
            elif meta['vendor']=='ASUS':
                famtests=[('ROG Maximus',('MAXIMUS',)),('ROG Strix',('ROGSTRIX','STRIX')),
                          ('TUF',('TUFGAMING','TUF')),('Prime',('PRIME',)),('ProArt',('PROART',))]
                source=compact
            elif meta['vendor']=='GIGABYTE': famtests=[('AORUS',('AORUS',))]; source=compact
            elif meta['vendor']=='MSI': famtests=[('MEG',('MEG',)),('MPG',('MPG',)),('MAG',('MAG',))]; source=compact
            elif meta['vendor']=='ASROCK': famtests=[('Taichi',('TAICHI',)),('Phantom Gaming',('PHANTOMGAMING',))]; source=compact
            else: famtests=[]; source=compact
            for name,keys in famtests:
                if any(k in source for k in keys): fam=name; break
            meta['family']=fam

            # Prefer the BIOS filename for MAXSUN because official ROM filenames often carry
            # the exact model while the firmware string table may only expose generic AMI text.
            def pretty_maxsun_filename(name):
                base=os.path.splitext(os.path.basename(str(name or '')))[0]
                # Ignore local modification labels, then drop the official BIOS revision.
                base=re.sub(r'[_-]MOD(?:[_-]?V?\d+)?$', '', base, flags=re.I)
                base=re.sub(r'[_-][A-Z]\d+(?:\.\d+)?[A-Z]?$', '', base, flags=re.I)
                u=base.upper()
                c=re.sub(r'[^A-Z0-9]+','',u)
                if not c.startswith('MS'): return ''
                # Require a known MAXSUN family/product marker before accepting an MS* filename.
                markers=('CHALLENGER','TERMINATOR','ICRAFT','ICAFE','ESPORT','PCFARM','MODT',
                         'GAMINGWIFIACE','GAMINGACE','GAMINGWIFIICE','GAMINGICE',
                         'WORKSTATION','AIMICROSTATION')
                if not any(x in c for x in markers): return ''
                s=c
                # Add separators around common model/marketing tokens.
                s=re.sub(r'^MS', 'MS-', s)
                for tok,rep in [
                    ('CHALLENGER',' CHALLENGER '),('TERMINATOR',' TERMINATOR '),
                    ('ICRAFT',' ICRAFT '),('ICAFE',' I-CAFE '),('ESPORT',' ESPORT '),
                    ('PCFARM',' PC FARM '),('MODT',' MODT '),
                    ('GAMINGWIFIACE',' GAMING WIFI ACE '),('GAMINGACE',' GAMING ACE '),
                    ('GAMINGWIFIICE',' GAMING WIFI ICE '),('GAMINGICE',' GAMING ICE '),
                    ('AIMICROSTATION',' AI MICRO STATION '),('WORKSTATION',' WORKSTATION ')]:
                    s=s.replace(tok,rep)
                # Split common memory/Wi-Fi/version suffixes for readability.
                s=re.sub(r'(D[45])(?=(?:II|V\d|WIFI|$))', r' \1 ', s)
                s=re.sub(r'WIFI(?=(?:6E|6|7|V\d|II|$))', ' WIFI ', s)
                s=re.sub(r'(?<![A-Z0-9])II(?![A-Z0-9])', ' II ', s)
                s=re.sub(r'(?<=D[45])II$', ' II', s)
                s=re.sub(r'(?<=ACE)D([45])', r' D\1', s)
                s=re.sub(r'(?<=ICE)D([45])', r' D\1', s)
                s=re.sub(r'(?<=D[45])II', ' II', s)
                s=re.sub(r'\s+', ' ', s).strip()
                s=s.replace('MS- ', 'MS-')
                return s[:64]

            if meta.get('vendor')=='MAXSUN':
                b=pretty_maxsun_filename(hint_name)
                if b: meta['board']=b

            # Fallback to readable strings in the image.
            if not meta.get('board'):
                patterns=[
                    r'(?:MS-|MAXSUN\s+)[A-Z0-9][A-Z0-9 _\-]{4,50}',
                    r'(?:ROG|TUF|PRIME|PROART)\s+[A-Z0-9][A-Z0-9 _\-]{4,40}']
                if meta.get('vendor') in ('ASUS','MAXSUN','MSI','GIGABYTE','ASROCK','BIOSTAR','COLORFUL'):
                    patterns += [r'Z\d{3}[- ][A-Z0-9][A-Z0-9 _\-]{3,35}', r'B\d{3}[A-Z0-9 _\-]{3,45}']
                scan_strings=[str(hint_name)]+strings
                for st in scan_strings:
                    up=st.upper().strip()
                    for pat in patterns:
                        mm=re.search(pat,up)
                        if mm:
                            meta['board']=mm.group(0).strip(' _-')[:64]; raise StopIteration
        except StopIteration: pass
        except Exception as e: log('BIOS identity detection warning: '+str(e))
        return meta

    @staticmethod
    def _png_end(blob,start):
        if blob[start:start+8] != b'\x89PNG\r\n\x1a\n': return None
        pos=start+8
        try:
            while pos+12 <= len(blob):
                ln=struct.unpack('>I',blob[pos:pos+4])[0]; typ=blob[pos+4:pos+8]
                pos += 12+ln
                if typ==b'IEND': return pos
        except Exception: return None
        return None

    @staticmethod
    def _png_accent(path):
        # Minimal 8-bit RGB/RGBA non-interlaced PNG sampler. Returns #RRGGBB or None.
        try:
            d=open(path,'rb').read(); pos=8; raw=b''; w=h=ct=None; bd=None; interlace=0
            while pos+12<=len(d):
                ln=struct.unpack('>I',d[pos:pos+4])[0]; typ=d[pos+4:pos+8]; chunk=d[pos+8:pos+8+ln]; pos += 12+ln
                if typ==b'IHDR': w,h,bd,ct,comp,filt,interlace=struct.unpack('>IIBBBBB',chunk)
                elif typ==b'IDAT': raw += chunk
                elif typ==b'IEND': break
            if not w or bd!=8 or interlace!=0 or ct not in (2,6): return None
            bpp=3 if ct==2 else 4; dec=zlib.decompress(raw); stride=w*bpp; prev=bytearray(stride); rows=[]; k=0
            for y in range(h):
                ft=dec[k]; k+=1; row=bytearray(dec[k:k+stride]); k+=stride
                for i in range(stride):
                    a=row[i-bpp] if i>=bpp else 0; b=prev[i]; c=prev[i-bpp] if i>=bpp else 0
                    if ft==1: row[i]=(row[i]+a)&255
                    elif ft==2: row[i]=(row[i]+b)&255
                    elif ft==3: row[i]=(row[i]+((a+b)//2))&255
                    elif ft==4:
                        p=a+b-c; pa=abs(p-a); pb=abs(p-b); pc=abs(p-c); pr=a if pa<=pb and pa<=pc else (b if pb<=pc else c)
                        row[i]=(row[i]+pr)&255
                if y % max(1,h//40)==0: rows.append(bytes(row))
                prev=row
            buckets={}
            for row in rows:
                for x in range(0,w,max(1,w//80)):
                    i=x*bpp; r,g,b=row[i],row[i+1],row[i+2]
                    mx=max(r,g,b); mn=min(r,g,b)
                    if mx<50 or mx-mn<28: continue
                    key=(r//32,g//32,b//32); buckets[key]=buckets.get(key,0)+1
            if not buckets:return None
            key=max(buckets,key=buckets.get); r=min(255,key[0]*32+16); g=min(255,key[1]*32+16); b=min(255,key[2]*32+16)
            return '#%02x%02x%02x'%(r,g,b)
        except Exception:return None

    def _scan_extracted_theme(self, td, meta):
        # Find AMITSE/setupdata hints and standard embedded PNG resources.
        candidates=[]; mods=set(); scanned_bytes=0; scanned_files=0; max_scan=160*1024*1024
        for root,dirs,files in os.walk(td):
            for fn in files:
                fp=os.path.join(root,fn); low=(root+'\\'+fn).lower(); scanned_files+=1
                if scanned_files>3500 or scanned_bytes>max_scan: break
                if 'amitse' in low: mods.add('AMITSE')
                if 'setupdata' in low or 'setup data' in low: mods.add('setupdata')
                try: sz=os.path.getsize(fp)
                except Exception: continue
                if sz<700000 and fn.lower().endswith(('.txt','.info','.json','.xml','.csv')):
                    try:
                        tt=open(fp,'r',encoding='utf-8',errors='ignore').read(700000)
                        uu=tt.upper()
                        if 'AMITSE' in uu: mods.add('AMITSE')
                        if 'SETUPDATA' in uu or 'SETUP DATA' in uu: mods.add('setupdata')
                        if meta.get('vendor')=='AMI':
                            for vv,kk in [('MAXSUN',('MAXSUN','CHALLENGER','TERMINATOR')),('ASUS',('ASUSTEK',' ASUS','ROG ','TUF GAMING')),('MSI',('MICRO-STAR','CLICK BIOS')),('GIGABYTE',('GIGABYTE','AORUS')),('ASROCK',('ASROCK',))]:
                                if any(x in uu for x in kk): meta['vendor']=vv; break
                    except Exception: pass
                if sz<128 or sz>8*1024*1024: continue
                scanned_bytes += sz
                if scanned_bytes>max_scan: break
                try: blob=open(fp,'rb').read()
                except Exception: continue
                # direct/embedded PNG; cap count to keep scans cheap
                start=0
                while len(candidates)<40:
                    j=blob.find(b'\x89PNG\r\n\x1a\n',start)
                    if j<0: break
                    e=self._png_end(blob,j)
                    if e and e-j>512:
                        candidates.append((e-j,blob[j:e],fn))
                    start=j+8
                if len(candidates)>=40 or scanned_files>3500 or scanned_bytes>max_scan: break
            if len(candidates)>=40 or scanned_files>3500 or scanned_bytes>max_scan: break
        meta['modules']=sorted(mods)
        if candidates:
            candidates.sort(key=lambda x:x[0],reverse=True)
            assets=[]
            for i,(sz,blob,src) in enumerate(candidates[:8]):
                out=os.path.join(self.cache_dir,'asset_%s_%02d.png'%(meta.get('sha256','x')[:8],i))
                try: open(out,'wb').write(blob); assets.append(out)
                except Exception: pass
            meta['assets']=assets
            if assets:
                meta['logo_path']=assets[0]; ac=self._png_accent(assets[0])
                if ac: meta['accent']=ac; meta['theme_source']='BIOS HII/PNG asset'
        return meta

    def focus_search(self): self.search_entry.focus_set(); self.search_entry.selection_range(0,'end')
    def open_any(self):
        p=filedialog.askopenfilename(
            title="Открыть BIOS, Setup PE32 или IFR",
            filetypes=[
                ("Поддерживаемые файлы","*.rom *.bin *.cap *.bio *.fd *.sct *.efi *.body *.raw *.txt *.ifr"),
                ("BIOS image","*.rom *.bin *.cap *.bio *.fd"),
                ("Setup PE32","*.sct *.efi *.body *.raw"),
                ("IFR text","*.txt *.ifr"),
                ("Все файлы","*.*")])
        if p:self.load_path(p)

    def open_setup(self):
        p=filedialog.askopenfilename(
            title="Открыть извлечённый Setup PE32 (Extract body)",
            filetypes=[("Setup PE32","*.sct *.efi *.bin *.body *.raw"),("Все файлы","*.*")])
        if p:self.load_setup_path(p)

    def load_path(self,p):
        self.status.set("Загрузка..."); self.update_idletasks(); log("Selected: "+p)
        low=p.lower()
        if low.endswith(('.txt','.ifr')):
            try:
                text=open(p,'r',encoding='utf-8',errors='replace').read(); self.set_model(IFRModel(text,p));return
            except Exception as e: messagebox.showerror(APP,str(e));return
        if low.endswith(('.sct','.efi','.body','.raw')):
            self.load_setup_path(p); return
        # .bin is ambiguous: default to BIOS image here. Use the dedicated Setup button for a PE32 .bin.
        threading.Thread(target=self._load_bios_worker,args=(p,),daemon=True).start()

    def load_setup_path(self,p):
        self.status.set("Setup PE32: IFRExtractor..."); self.update_idletasks(); log("Setup PE32 selected: "+p)
        threading.Thread(target=self._load_setup_worker,args=(p,),daemon=True).start()

    def _load_setup_worker(self,p):
        td=None
        try:
            tr=ToolRunner(self); ir=self._tool(['ifrextractor.exe','IFRExtractor.exe','ifrextractor'])
            if not ir: raise RuntimeError("Для открытия Setup PE32 нужен tools\\ifrextractor.exe")
            td=tempfile.mkdtemp(prefix='uefi_preview_setup_')
            ext=os.path.splitext(p)[1] or '.sct'
            inp=os.path.join(td,'Setup'+ext); shutil.copy2(p,inp)
            log("Setup temp directory: "+td)
            log("Setup SHA256: "+hashlib.sha256(open(inp,'rb').read()).hexdigest())
            tr.status("[Setup 1/2] IFRExtractor...")
            text,src=self._try_ifr(ir,inp,td)
            if not text:
                raise RuntimeError("IFRExtractor не смог извлечь IFR из этого Setup PE32.\n\nПроверь, что это именно PE32 image -> Extract body, а не целый FFS/section.")
            tr.status("[Setup 2/2] Построение меню...")
            m=IFRModel(text,p)
            corpus='\n'.join((x.prompt or '') for x in m.nodes[:9000]).upper()
            vend='ASUS' if ('AI TWEAKER' in corpus or 'DIGI+ VRM' in corpus) else ('MAXSUN' if 'OVERClocking Performance Menu'.upper() in corpus else 'AMI')
            m.bios_meta={'source_type':'setup_only','vendor':vend,'family':'Generic','board':'','theme_source':'Setup-only inferred'}; sm=m.summary()
            if sm['forms']==0 or sm['questions']==0:
                raise RuntimeError("IFR извлечён, но формы/настройки не найдены.")
            log("Direct Setup summary: "+str(sm))
            extra="Direct Setup PE32 | IFR: %s"%(os.path.basename(src) if src!='stdout' else 'stdout')
            self.after(0,lambda mm=m,ex=extra:self.set_model(mm,extra=ex))
            try: shutil.rmtree(td); td=None; log("Setup temp directory cleaned")
            except Exception as e: log("Setup temp cleanup warning: "+str(e))
        except Exception as e:
            log("SETUP FATAL: "+str(e)); traceback.print_exc()
            if td: log("Setup temp directory kept for diagnostics: "+td)
            self.after(0,lambda s=str(e):self._err(s))

    def _tool(self,names):
        base=os.path.dirname(os.path.abspath(__file__))
        for d in (os.path.join(base,'tools'),base):
            for n in names:
                p=os.path.join(d,n)
                if os.path.isfile(p):return p
        return None

    def check_tools(self):
        threading.Thread(target=self._check_tools_worker,daemon=True).start()
    def _check_tools_worker(self):
        try:
            tr=ToolRunner(self); ux=self._tool(['UEFIExtract.exe','uefiextract.exe','UEFIExtract']); ir=self._tool(['ifrextractor.exe','IFRExtractor.exe','ifrextractor'])
            if not ux: raise RuntimeError("UEFIExtract.exe не найден в папке tools")
            if not ir: raise RuntimeError("ifrextractor.exe не найден в папке tools")
            tr.status("Проверка UEFIExtract..."); rc1,o1=tr.run([ux],timeout=15)
            if 'UEFIExtract' not in o1 and 'Usage' not in o1: raise RuntimeError("UEFIExtract запускается, но не вывел ожидаемую справку")
            tr.status("Проверка IFRExtractor..."); rc2,o2=tr.run([ir],timeout=15)
            if 'IFR' not in o2 and 'Usage' not in o2 and 'ifrextractor' not in o2.lower(): raise RuntimeError("IFRExtractor запускается, но не вывел ожидаемую справку")
            tr.status("Инструменты OK")
            self.after(0,lambda:messagebox.showinfo(APP,"Оба инструмента запускаются нормально.\n\nСмотри CMD для версий и логов."))
        except Exception as e:self.after(0,lambda:self._err(str(e)))

    def _candidate_files(self,td,original):
        out=[]; setup_dirs=set(); metadata=[]
        for root,dirs,files in os.walk(td):
            for f in files:
                fp=os.path.join(root,f)
                if os.path.abspath(fp)==os.path.abspath(original): continue
                low=(root+'\\'+f).lower()
                try:sz=os.path.getsize(fp)
                except Exception:continue
                if sz<=0:continue
                if sz<1024*1024 and f.lower().endswith(('.txt','.info','.csv','.json')):
                    try:
                        t=open(fp,'r',encoding='utf-8',errors='ignore').read(200000).lower()
                        if 'setup' in t:
                            setup_dirs.add(root); metadata.append(fp)
                    except Exception:pass
        for root,dirs,files in os.walk(td):
            for f in files:
                fp=os.path.join(root,f); low=(root+'\\'+f).lower()
                try:sz=os.path.getsize(fp)
                except Exception:continue
                if sz<4096 or sz>24*1024*1024:continue
                if f.lower().endswith(('.txt','.info','.csv','.json','.xml','.log')):continue
                score=0
                if 'setup' in low:score+=100
                if any(root.startswith(d) or d.startswith(root) for d in setup_dirs):score+=70
                if 'pe32' in low:score+=40
                if 'body' in f.lower():score+=15
                if f.lower().endswith(('.efi','.sct','.bin','.body','.raw')):score+=10
                # HII/PE candidates are usually not tiny and not full-image sized
                if 50*1024 <= sz <= 4*1024*1024:score+=8
                out.append((score,sz,fp))
        out.sort(key=lambda x:(x[0], -abs(x[1]-1024*1024)),reverse=True)
        # de-duplicate exact paths
        seen=set(); res=[]
        for x in out:
            if x[2] not in seen:seen.add(x[2]);res.append(x)
        log("Candidate binaries found: %d (setup metadata files: %d)"%(len(res),len(metadata)))
        return res

    def _try_ifr(self,ir,fp,td):
        """Run IFRExtractor exactly once for a candidate.

        IFRExtractor-RS normally writes the decoded IFR to a text file next to
        the input and prints only progress to stdout. Older builds may emit the
        IFR itself to stdout. We support both without running the extractor a
        second time.
        """
        before = set()
        try:
            for rr, dd, ff in os.walk(td):
                for fn in ff:
                    full = os.path.join(rr, fn)
                    if fn.lower().endswith(('.txt', '.ifr')):
                        before.add(os.path.abspath(full))
        except Exception:
            pass

        # The user's IFRExtractor-RS 1.6.x accepts "verbose" and this is the
        # same command that was already proven to work manually.
        try:
            rc, out = ToolRunner.run([ir, fp, 'verbose'], cwd=td, timeout=60)
        except subprocess.TimeoutExpired:
            log('IFRExtractor timed out for: ' + fp)
            return None, None
        except Exception as e:
            log('IFRExtractor launch error for %s: %s' % (fp, e))
            return None, None

        # Some builds return 0 and write a file, while stdout contains only
        # "Extracting all UEFI HII...". If stdout itself is IFR, use it.
        if ('FormSet' in out or 'Form FormId:' in out) and re.search(r'^0x[0-9A-Fa-f]+:', out, re.M):
            log('IFR obtained directly from stdout')
            return out, 'stdout'

        # Search only files created/updated by this one invocation. Prefer
        # names derived from the input file, then newest files.
        created = []
        try:
            for rr, dd, ff in os.walk(td):
                for fn in ff:
                    if not fn.lower().endswith(('.txt', '.ifr')):
                        continue
                    full = os.path.abspath(os.path.join(rr, fn))
                    try:
                        if os.path.getsize(full) < 1000:
                            continue
                    except Exception:
                        continue
                    if full not in before:
                        created.append(full)
        except Exception:
            pass

        # IFRExtractor may overwrite an existing predictable output name.
        # Also inspect text files close to this input, newest first.
        base = os.path.dirname(fp)
        nearby = []
        try:
            for rr, dd, ff in os.walk(base):
                for fn in ff:
                    if fn.lower().endswith(('.txt', '.ifr')):
                        full = os.path.abspath(os.path.join(rr, fn))
                        try:
                            if os.path.getsize(full) > 1000:
                                nearby.append(full)
                        except Exception:
                            pass
                if rr != base and len(os.path.relpath(rr, base).split(os.sep)) >= 2:
                    dd[:] = []
        except Exception:
            pass

        inp_name = os.path.basename(fp).lower()
        inp_stem = os.path.splitext(inp_name)[0]
        candidates = list(dict.fromkeys(created + nearby))
        candidates.sort(key=lambda x: (
            1 if inp_stem in os.path.basename(x).lower() else 0,
            os.path.getmtime(x) if os.path.exists(x) else 0
        ), reverse=True)

        log('IFR output candidates after one run: %d' % len(candidates))
        for outp in candidates[:30]:
            # Try the common encodings used by IFRExtractor builds.
            text = None
            for enc in ('utf-8-sig', 'utf-8', 'utf-16', 'cp1252'):
                try:
                    with open(outp, 'r', encoding=enc, errors='strict') as fh:
                        text = fh.read()
                    break
                except Exception:
                    text = None
            if text is None:
                try:
                    text = open(outp, 'r', encoding='utf-8', errors='replace').read()
                except Exception:
                    continue
            if ('FormSet' in text or 'Form FormId:' in text) and re.search(r'^0x[0-9A-Fa-f]+:', text, re.M):
                log('IFR output selected: ' + outp)
                return text, outp

        log('IFR not found after one extractor run; exit code=%s' % rc)
        return None, None

    def _load_bios_worker(self,p):
        td=None
        try:
            tr=ToolRunner(self); ux=self._tool(['UEFIExtract.exe','uefiextract.exe','UEFIExtract']); ir=self._tool(['ifrextractor.exe','IFRExtractor.exe','ifrextractor'])
            if not ux or not ir:
                raise RuntimeError("Для открытия целого BIOS нужны tools\\UEFIExtract.exe и tools\\ifrextractor.exe.\n\nНажми 'Проверить инструменты'.")
            tr.status("[1/5] Подготовка BIOS...")
            td=tempfile.mkdtemp(prefix='uefi_preview_'); inp=os.path.join(td,'input'+os.path.splitext(p)[1]); shutil.copy2(p,inp)
            log("Temp directory: "+td); log("BIOS SHA256: "+hashlib.sha256(open(inp,'rb').read()).hexdigest()); meta=self._detect_bios_identity(inp, os.path.basename(p)); log("Detected BIOS identity: %s / %s / %s"%(meta.get("vendor"),meta.get("family"),meta.get("board") or "?"))
            tr.status("[2/5] UEFIExtract: распаковка...")
            rc,out=tr.run([ux,inp,'unpack'],cwd=td,timeout=180)
            if rc not in (0,1): raise RuntimeError("UEFIExtract завершился с кодом %s. Смотри CMD."%rc)
            # Even some successful builds use nonzero codes; actual extracted files are decisive.
            allfiles=sum(len(fs) for _,_,fs in os.walk(td))
            log("Files after unpack: %d"%allfiles)
            if allfiles<3: raise RuntimeError("UEFIExtract не создал распакованные файлы. Смотри CMD выше.")
            tr.status("[2/5] Анализ темы/HII ресурсов..."); meta=self._scan_extracted_theme(td,meta); log("Theme scan: modules=%s assets=%d source=%s"%(meta.get("modules"),len(meta.get("assets",[])),meta.get("theme_source")))
            tr.status("[3/5] Поиск Setup/PE32 кандидатов...")
            candidates=self._candidate_files(td,inp)
            if not candidates: raise RuntimeError("После UEFIExtract не найдено бинарных кандидатов для IFR.")
            tr.status("[4/5] IFRExtractor: поиск Setup...")
            best=None; tried=0
            # First pass: only candidates strongly associated with Setup/PE32.
            high=[c for c in candidates if c[0] >= 70]
            low=[c for c in candidates if c[0] < 70]
            scan=(high[:90] + low[:40]) if high else low[:140]
            if not scan: scan=candidates[:90]
            limit=len(scan)
            log("IFR scan plan: %d high-confidence + %d fallback = %d candidates"%(min(len(high),90),min(len(low),40 if high else 140),limit))
            for score,sz,fp in scan:
                tried+=1
                if tried==1 or tried%10==0:
                    tr.status("[4/5] IFRExtractor: %d/%d..."%(tried,limit))
                try:text,src=self._try_ifr(ir,fp,td)
                except Exception as e:
                    log("IFR error %s: %s"%(fp,e));continue
                if not text:continue
                try:
                    m=IFRModel(text,p); s=m.summary(); quality=s['questions']+s['forms']*30 + m.navigation_score()*3
                except Exception as e:
                    log("Parse failed for %s: %s"%(fp,e));continue
                log("IFR candidate OK: score=%d quality=%d forms=%d questions=%d file=%s"%(score,quality,s['forms'],s['questions'],fp))
                cand=(quality,score,m,fp,src)
                if best is None or cand[:2]>best[:2]:best=cand
            if not best:
                raise RuntimeError("IFR не найден автоматически после проверки %d файлов.\n\nСмотри CMD: там есть полный лог UEFIExtract/IFRExtractor."%tried)
            tr.status("[5/5] Построение меню...")
            quality,score,m,fp,src=best
            m.bios_meta=meta
            extra="Setup: %s | IFR: %s"%(os.path.basename(fp),os.path.basename(src) if src!='stdout' else 'stdout')
            log("Selected best candidate: "+fp); log("Summary: "+str(m.summary()))
            self.after(0,lambda mm=m,ex=extra:self.set_model(mm,extra=ex))
            # Keep temp only until parsing is done; model already holds IFR text.
            try:shutil.rmtree(td); td=None; log("Temp directory cleaned")
            except Exception as e:log("Temp cleanup warning: "+str(e))
        except Exception as e:
            log("FATAL: "+str(e)); traceback.print_exc()
            if td: log("Temp directory kept for diagnostics: "+td)
            self.after(0,lambda s=str(e):self._err(s))

    def _err(self,s): self.status.set("Ошибка"); messagebox.showerror(APP,s)
    def set_model(self,m,extra=""):
        self.model=m; self.path=m.source; self.tree.delete(*self.tree.get_children())
        roots={}
        for f in m.forms:
            iid='f%X'%f.form_id if f.form_id is not None else 'l%d'%f.line_no
            # avoid duplicate iid on malformed/duplicated forms
            base=iid; k=1
            while self.tree.exists(iid):k+=1;iid=base+'_%d'%k
            roots.setdefault(f.form_id,iid); self.tree.insert('', 'end', iid=iid, text=f.label())
        for f in m.forms:
            parent=roots.get(f.form_id)
            if not parent:continue
            for n in self._direct_items(f):
                if n.kind=='Ref' and n.target_form in m.form_by_id:
                    self.tree.insert(parent,'end',text='↳ '+(n.prompt or m.form_by_id[n.target_form].label()),values=('ref',n.target_form))
        if self.tree.get_children(): self.tree.selection_set(self.tree.get_children()[0]); self.tree.focus(self.tree.get_children()[0]); self.on_form()
        sm=m.summary(); self.status.set("Forms: {forms} | Questions: {questions} | Hidden: {hidden_now} | Warnings: {warnings}".format(**sm)+((' | '+extra) if extra else ''))
        log("Loaded model: "+str(sm))
        # Open the interactive BIOS-like view automatically after successful load.
        try: self.after(180, self.open_simulator)
        except Exception: pass

    def _direct_items(self,form):
        out=[]
        def walk(n):
            for c in n.children:
                if c.kind in ('SuppressIf','GrayOutIf','DisableIf'):walk(c)
                elif c.kind!='FormSet': out.append(c)
        walk(form); return out

    def selected_form(self):
        if not self.model:return None
        sel=self.tree.selection()
        if not sel:return None
        iid=sel[0]; vals=self.tree.item(iid,'values')
        if vals and len(vals)>1 and vals[0]=='ref':return self.model.form_by_id.get(int(vals[1]))
        m=re.match(r'^f([0-9A-Fa-f]+)',iid)
        if m:return self.model.form_by_id.get(int(m.group(1),16))
        return None

    def on_form(self,event=None): self.refresh_preview()
    def refresh_preview(self):
        f=self.selected_form(); self.preview.delete(0,'end');self.preview_nodes=[]
        if not f:return
        for n in self._direct_items(f):
            if n.kind in ('End','Form'):continue
            vis=self.model.visibility(n)
            if vis=='hidden' and not self.show_hidden.get():continue
            prefix={'hidden':'[H] ','conditional':'[?] ','visible':'    '}[vis]
            prompt=(n.prompt or '').replace('\n',' ').strip()
            if not prompt:
                continue
            val=self._value_text(n); text=prefix+prompt+(('    '+val) if val else '')
            self.preview.insert('end',text); self.preview_nodes.append(n)
        if self.preview.size(): self.preview.selection_set(0);self.preview.activate(0);self.on_item()

    def _value_text(self,n):
        if n.qid is None:return '→' if n.kind=='Ref' else ''
        v=self.model.values.get(n.qid)
        if n.kind=='CheckBox':return '[%s]'%('x' if v else ' ')
        if n.options:
            for lab,val,d in n.options:
                if val==v:return '<%s>'%(lab or str(val))
            return '<%s>'%v
        if n.kind=='Numeric':return '<%s>'%v
        return ''

    def current_node(self):
        s=self.preview.curselection(); return self.preview_nodes[s[0]] if s and s[0]<len(self.preview_nodes) else None
    def on_item(self,event=None):
        n=self.current_node()
        if not n:return
        vis=self.model.visibility(n); lines=["Тип: %s"%n.kind,"Название: %s"%((n.prompt or '').strip() or '-'),"Видимость: %s"%vis,"IFR line: %d"%n.line_no,"IFR offset: %s"%(('0x%X'%n.offset) if n.offset is not None else '-')]
        if n.qid is not None:lines += ["QuestionId: 0x%X"%n.qid,"Значение (симуляция): %s"%self.model.values.get(n.qid)]
        if n.varstore is not None:lines.append("VarStoreId: 0x%X (%s)"%(n.varstore,self.model.varstores.get(n.varstore,'?')))
        if n.varoffset is not None:lines.append("VarOffset/Info: 0x%X"%n.varoffset)
        if n.size is not None:lines.append("Size: %s"%n.size)
        if n.min is not None:lines.append("Min/Max/Step: %s / %s / %s"%(n.min,n.max,n.step))
        if n.options:lines.append("Опции:\n"+'\n'.join('  %s = %s%s'%(a,b,' [default]' if d else '') for a,b,d in n.options))
        if n.target_form is not None:lines.append("Target FormId: 0x%X"%n.target_form)
        scopes=getattr(n,'visibility_scopes',[])
        if scopes:
            lines.append("\nУсловия видимости:")
            for s in scopes: lines.append("%s @0x%X: %s"%(s.kind,s.offset or 0,' | '.join(s.condition) or '<unknown>'))
        if n.help: lines.append("\nHelp:\n"+n.help)
        self.props.config(state='normal');self.props.delete('1.0','end');self.props.insert('1.0','\n'.join(lines));self.props.config(state='disabled')

    def activate(self,event=None): return self._change(+1)
    def activate_reverse(self,event=None): return self._change(-1)
    def _change(self,d):
        n=self.current_node()
        if not n:return 'break'
        if n.kind=='Ref' and n.target_form in self.model.form_by_id:
            iid='f%X'%n.target_form
            if self.tree.exists(iid): self.tree.selection_set(iid);self.tree.see(iid);self.on_form()
        elif n.qid is not None and n.kind=='CheckBox':self.model.values[n.qid]=0 if self.model.values.get(n.qid) else 1;self.refresh_preview()
        elif n.qid is not None and n.options:
            vals=[x[1] for x in n.options];cur=self.model.values.get(n.qid);idx=vals.index(cur) if cur in vals else 0; self.model.values[n.qid]=vals[(idx+d)%len(vals)];self.refresh_preview()
        elif n.qid is not None and n.kind=='Numeric':
            cur=self.model.values.get(n.qid,n.min or 0);step=n.step or 1; nv=cur+d*step
            if n.min is not None:nv=max(n.min,nv)
            if n.max is not None:nv=min(n.max,nv)
            self.model.values[n.qid]=nv;self.refresh_preview()
        return 'break'

    def do_search(self,event=None):
        q=self.search.get().strip().lower()
        if not q or not self.model:return
        for f in self.model.forms:
            if q in (f.prompt or '').lower() or any(q in (n.prompt or '').lower() for n in self._direct_items(f)):
                iid='f%X'%f.form_id if f.form_id is not None else 'l%d'%f.line_no
                if self.tree.exists(iid):self.tree.selection_set(iid);self.tree.see(iid);self.on_form()
                for j,n in enumerate(self.preview_nodes):
                    if q in (n.prompt or '').lower():self.preview.selection_clear(0,'end');self.preview.selection_set(j);self.preview.see(j);self.on_item();break
                return
        messagebox.showinfo(APP,"Ничего не найдено")

    def open_simulator(self):
        if not self.model:
            messagebox.showinfo(APP,"Сначала открой Setup PE32 / IFR / BIOS.")
            return
        try:
            BiosSimulator(self, self.model, None)
        except Exception as e:
            log("BIOS Simulator error: "+str(e)); traceback.print_exc()
            messagebox.showerror(APP,"Не удалось открыть BIOS Simulator:\n"+str(e))

    def show_report(self):
        if not self.model:return
        s=self.model.summary(); txt=[APP+' '+VER,'Source: '+str(self.path),'SHA256(IFR text): '+hashlib.sha256(self.model.text.encode('utf-8',errors='replace')).hexdigest(),'']
        meta=getattr(self.model,'bios_meta',{}) or {}
        if meta: txt += ['BIOS source: '+str(meta.get('source_type','?')),'Detected vendor/family: %s / %s'%(meta.get('vendor','?'),meta.get('family','?')),'Detected board: '+str(meta.get('board') or '?'),'Theme source: '+str(meta.get('theme_source','generic')),'AMI modules: '+(', '.join(meta.get('modules',[])) or 'not detected'),'Extracted image assets: %d'%len(meta.get('assets',[])),'']
        txt += ['Primary Setup score: %d'%self.model.navigation_score(),'Forms: %d'%s['forms'],'Questions: %d'%s['questions'],'Refs: %d'%s['refs'],'Hidden with current simulated values: %d'%s['hidden_now'],'Runtime/unsupported conditions: %d'%s['conditional'],'Warnings: %d'%s['warnings'],'']
        txt += ['WARNINGS:']+(self.model.warnings or ['none'])
        w=tk.Toplevel(self);w.title('Validator report');t=tk.Text(w,wrap='word',font=('Consolas',9));t.pack(fill='both',expand=True);t.insert('1.0','\n'.join(txt));t.config(state='disabled');w.geometry('800x600')


class HardwareDialog(tk.Toplevel):
    def __init__(self, sim):
        tk.Toplevel.__init__(self,sim); self.sim=sim; self.title('Preview Hardware'); self.transient(sim); self.grab_set()
        self.configure(bg=sim.BG); self.geometry('700x560'); self.resizable(False,False)
        nb=ttk.Notebook(self); nb.pack(fill='both',expand=True,padx=10,pady=10)
        self._cpu(nb); self._ram(nb)
        bar=tk.Frame(self,bg=sim.BG); bar.pack(fill='x',padx=10,pady=(0,10))
        tk.Button(bar,text='OK',width=12,command=self.accept).pack(side='right')
        tk.Button(bar,text='Cancel',width=12,command=self.destroy).pack(side='right',padx=6)
        self.bind('<Escape>',lambda e:self.destroy()); self.bind('<Return>',lambda e:self.accept())
    def _row(self,parent,row,label,var,kind='entry',values=None):
        tk.Label(parent,text=label,anchor='w').grid(row=row,column=0,sticky='w',padx=10,pady=6)
        if kind=='combo': w=ttk.Combobox(parent,textvariable=var,state='readonly',values=values or [],width=26)
        else: w=tk.Entry(parent,textvariable=var,width=28)
        w.grid(row=row,column=1,sticky='ew',padx=10,pady=6); return w
    def _cpu(self,nb):
        f=tk.Frame(nb); nb.add(f,text='CPU'); f.grid_columnconfigure(1,weight=1); s=self.sim
        c=self._row(f,0,'Processor',s.cpu_profile,'combo',[x['name'] for x in s.cpu_profiles])
        def rebuild(event=None):
            s._apply_cpu_profile(False)
            # Re-open is not needed; topology-specific rows are enabled/disabled below.
            p=s._current_cpu_profile()
            try:self.e_entry.config(state='normal' if p.get('e',0)>0 else 'disabled')
            except Exception:pass
            try:self.ring_entry.config(state='disabled' if p.get('amd') else 'normal')
            except Exception:pass
            try:self.sp_entry.config(state='normal' if p.get('sp') else 'disabled')
            except Exception:pass
        c.bind('<<ComboboxSelected>>',rebuild)
        self._row(f,1,'BCLK (MHz)',s.cpu_bclk); self._row(f,2,'P/Core ratio',s.cpu_pr)
        self.e_entry=self._row(f,3,'E-core ratio',s.cpu_er); self.ring_entry=self._row(f,4,'Ring/Cache ratio',s.cpu_rr)
        self.sp_entry=self._row(f,5,'SP (simulation)',s.cpu_sp)
        rebuild()
    def _ram(self,nb):
        f=tk.Frame(nb); nb.add(f,text='Memory'); f.grid_columnconfigure(1,weight=1); s=self.sim
        self._row(f,0,'Capacity (GB)',s.hw_ram_gb); self._row(f,1,'Data rate (MT/s)',s.hw_ram_speed)
        tk.Label(f,text='Only capacity and memory frequency are injected into informational BIOS fields. Other telemetry remains hidden instead of being invented.',wraplength=560,justify='left').grid(row=3,column=0,columnspan=2,sticky='w',padx=10,pady=15)
    def _storage(self,nb):
        f=tk.Frame(nb); nb.add(f,text='Storage'); f.grid_columnconfigure(1,weight=1); s=self.sim
        self._row(f,0,'SSD model',s.hw_ssd_model); self._row(f,1,'Type',s.hw_ssd_type,'combo',['NVMe PCIe','SATA SSD','SATA HDD'])
        self._row(f,2,'Capacity (GB)',s.hw_ssd_size)
        tk.Label(f,text='This is a virtual device model. Firmware callbacks that enumerate real PCIe/SATA devices are not executed.',wraplength=560,justify='left').grid(row=4,column=0,columnspan=2,sticky='w',padx=10,pady=15)
    def _monitor(self,nb):
        f=tk.Frame(nb); nb.add(f,text='Sensors / Fans'); f.grid_columnconfigure(1,weight=1); s=self.sim
        self._row(f,0,'CPU temp (C)',s.hw_cpu_temp); self._row(f,1,'Board temp (C)',s.hw_board_temp)
        self._row(f,2,'CPU_FAN (RPM)',s.hw_cpu_fan); self._row(f,3,'SYS_FAN1 (RPM)',s.hw_sys_fan1); self._row(f,4,'SYS_FAN2 (RPM)',s.hw_sys_fan2)
    def accept(self):
        try:
            self.sim._apply_cpu_profile(False); self.sim._update_hw_summary(); self.sim.update_cpu_sim(); self.sim.render()
        except Exception as e: log('Virtual hardware update warning: '+str(e))
        self.destroy()

class ChoiceDialog(tk.Toplevel):
    def __init__(self, parent, title, options, current=None):
        tk.Toplevel.__init__(self, parent)
        self.result=None; self.options=options
        self.title(title); self.transient(parent); self.grab_set(); self.resizable(False,False)
        self.configure(bg='#0b1630')
        tk.Label(self,text=title,bg='#0b1630',fg='white',font=('Segoe UI',11,'bold'),padx=16,pady=10).pack(fill='x')
        self.lb=tk.Listbox(self,width=52,height=min(14,max(4,len(options))),font=('Segoe UI',10),
                           bg='#13264b',fg='white',selectbackground='#3977c9',selectforeground='white',
                           activestyle='none',highlightthickness=0,borderwidth=0)
        self.lb.pack(fill='both',expand=True,padx=10,pady=(0,10))
        sel=0
        for i,(label,value) in enumerate(options):
            self.lb.insert('end',label)
            if value==current: sel=i
        if options:
            self.lb.selection_set(sel); self.lb.activate(sel); self.lb.see(sel)
        bar=tk.Frame(self,bg='#0b1630');bar.pack(fill='x',padx=10,pady=(0,10))
        tk.Button(bar,text='Выбрать',command=self.accept,width=12).pack(side='left')
        tk.Button(bar,text='Отмена',command=self.cancel,width=12).pack(side='right')
        self.bind('<Return>',lambda e:self.accept()); self.bind('<Escape>',lambda e:self.cancel())
        self.lb.bind('<Double-Button-1>',lambda e:self.accept())
        self.protocol('WM_DELETE_WINDOW',self.cancel)
        self.update_idletasks()
        try:
            x=parent.winfo_rootx()+max(20,(parent.winfo_width()-self.winfo_width())//2)
            y=parent.winfo_rooty()+max(20,(parent.winfo_height()-self.winfo_height())//2)
            self.geometry('+%d+%d'%(x,y))
        except Exception: pass
        self.lb.focus_set(); self.wait_window(self)
    def accept(self):
        s=self.lb.curselection()
        if s and s[0] < len(self.options): self.result=self.options[s[0]][1]
        self.destroy()
    def cancel(self): self.destroy()

class BiosSimulator(tk.Toplevel):
    """Interactive AMI/MAXSUN-like front-end for parsed IFR.

    Dependencies are driven by the actual SuppressIf/GrayOutIf/DisableIf expressions.
    Vendor String-backed numeric controls use ranges parsed from their Help text.
    This is still a simulator: callbacks are not executed and the BIOS is never written.
    """
    BG='#09152d'; PANEL='#0e2145'; PANEL2='#102952'; FG='#f2f5fb'; MUTED='#9fb2d0'
    ACCENT='#2f72c5'; SEL='#1e5da9'; DISABLED='#6d7890'; WARN='#d8b35a'; TAB='#0a1b39'; TABSEL='#235f9f'
    TAB_KEYWORDS=(
        ('Main',('main','information','system information')),
        ('Advanced',('advanced','settings')),
        ('OC',('overclock','overclocking','tweaker','oc','performance')),
        ('Chipset',('chipset','pch','system agent')),
        ('Security',('security','trusted computing','secure boot')),
        ('Boot',('boot','csm')),
        ('Tool',('tool','utility','ez update','flash')),
        ('Save & Exit',('save & exit','save and exit','exit')),
    )
    @staticmethod
    def _hexrgb(c):
        c=(c or '#2f72c5').lstrip('#')
        try:return tuple(int(c[i:i+2],16) for i in (0,2,4))
        except Exception:return (47,114,197)
    @staticmethod
    def _rgbhex(rgb):
        return '#%02x%02x%02x'%tuple(max(0,min(255,int(x))) for x in rgb)
    @classmethod
    def _mix(cls,a,b,t):
        aa=cls._hexrgb(a);bb=cls._hexrgb(b);return cls._rgbhex(tuple(aa[i]*(1-t)+bb[i]*t for i in range(3)))

    def _apply_auto_theme(self):
        """Best-effort native-family skin. Full BIOS assets override accents/logos; Setup-only uses a neutral skin."""
        meta=getattr(self.model,'bios_meta',{}) or {}
        vendor=(meta.get('vendor') or 'AMI').upper(); fam=(meta.get('family') or 'Generic').upper(); board=(meta.get('board') or '').upper()
        # Layout palette families intentionally differ, instead of recoloring one universal theme.
        if vendor=='ASUS' and any(x in fam+board for x in ('ROG','MAXIMUS','STRIX')):
            pal=('#08090c','#111216','#18191e','#f0f0f2','#999ca4','#b10f1a','#8f1119','#07080b','#781017')
            self.SKIN='ASUS ROG'
        elif vendor=='ASUS':
            pal=('#16080a','#2a0d12','#381116','#f5eeee','#c7aeb0','#d0333f','#ae2631','#1b080b','#93232d')
            self.SKIN='ASUS UEFI'
        elif vendor=='MAXSUN':
            pal=('#13171b','#1b2228','#232d35','#eef3f7','#a8b4be','#3680b8','#2c6e9f','#171d22','#285f89')
            self.SKIN='MAXSUN UEFI'
        elif vendor=='MSI':
            pal=('#0d0d0f','#171719','#222225','#f3f3f3','#ababab','#ba1f24','#8f181c','#111113','#79161a')
            self.SKIN='MSI Click BIOS'
        elif vendor=='GIGABYTE':
            pal=('#0e1013','#171b20','#20262d','#f1f4f7','#aab1b8','#e17b21','#bd6217','#12161a','#9b5116')
            self.SKIN='GIGABYTE/AORUS'
        elif vendor=='ASROCK':
            pal=('#07151f','#0b2231','#103047','#eef5f8','#a6bbc5','#2586b8','#1d709d','#091b27','#175a7d')
            self.SKIN='ASRock UEFI'
        else:
            pal=('#09152d','#0e2145','#102952','#f2f5fb','#9fb2d0','#2f72c5','#1e5da9','#0a1b39','#235f9f')
            self.SKIN='Generic AMI'
        self.BG,self.PANEL,self.PANEL2,self.FG,self.MUTED,self.ACCENT,self.SEL,self.TAB,self.TABSEL=pal
        # If a real full-BIOS image asset yielded an accent, blend it lightly into selection only.
        accent=meta.get('accent')
        if accent:
            self.ACCENT=accent; self.SEL=self._mix(accent,'#000000',0.22); self.TABSEL=self._mix(accent,'#000000',0.35)
        self.DISABLED='#747982'; self.WARN='#d7b35b'

    def _meta_title(self):
        m=getattr(self.model,'bios_meta',{}) or {}; bits=[]
        if m.get('vendor'):bits.append(m.get('vendor'))
        if m.get('family') and m.get('family')!='Generic':bits.append(m.get('family'))
        if m.get('board'):bits.append(m.get('board'))
        return ' / '.join(bits) if bits else 'AMI UEFI BIOS'

    def __init__(self,parent,model,start_form=None):
        tk.Toplevel.__init__(self,parent); self.model=model; self.history=[]; self._apply_auto_theme(); self.logo_img=None
        self.current_form=self._pick_start_form() if start_form is None else start_form
        self.nodes=[]; self.row_map={}; self.selected_index=0; self.tab_buttons=[]; self.tab_forms=[]
        self.title('UEFI BIOS Simulator - '+(self.current_form.label() if self.current_form else 'Setup'))
        self.geometry('1320x780'); self.minsize(900,560); self.configure(bg=self.BG)
        self.protocol('WM_DELETE_WINDOW',self.close)
        self._build(); self._build_tabs(); self._bind_keys(); self.update_cpu_sim(); self.render()
        self.after(100,lambda:self.menu.focus_set())

    def _numeric_value_from_prompt(self, keywords):
        keys=[x.lower() for x in keywords]
        best=None
        for n in self.model.nodes:
            p=(n.prompt or '').lower()
            if not p or n.qid is None or not all(k in p for k in keys): continue
            if getattr(self.model,'modified_qids',set()) and n.qid not in self.model.modified_qids: continue
            v=self.model.values.get(n.qid)
            if isinstance(v,(int,float)): return float(v)
            if isinstance(v,str):
                mm=re.search(r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)',v.replace(',','.'))
                if mm:
                    try:return float(mm.group(0))
                    except Exception:pass
        return best

    def _cpu_profiles_for_bios(self):
        m=getattr(self.model,'bios_meta',{}) or {}; text=(' '.join([str(m.get('board','')),str(m.get('family','')),str(self.model.source)])).upper()
        # Board-name/chipset detection is intentionally conservative. Users can still choose Generic.
        if 'Z170' in text or 'H170' in text or 'B150' in text or 'H110' in text:
            return [
                {'name':'Core i7-6700K','p':4,'e':0,'threads':8,'pr':42,'er':0,'rr':41,'sp':False},
                {'name':'Core i5-6600K','p':4,'e':0,'threads':4,'pr':39,'er':0,'rr':39,'sp':False},
                {'name':'Core i7-6700','p':4,'e':0,'threads':8,'pr':40,'er':0,'rr':40,'sp':False},
                {'name':'Generic Skylake','p':4,'e':0,'threads':8,'pr':40,'er':0,'rr':40,'sp':False}]
        if any(x in text for x in ('Z790','B760','H770','Z690','B660','H670')):
            return [
                {'name':'Core i9-14900K','p':8,'e':16,'threads':32,'pr':57,'er':44,'rr':50,'sp':True},
                {'name':'Core i7-14700K','p':8,'e':12,'threads':28,'pr':56,'er':43,'rr':48,'sp':True},
                {'name':'Core i5-14600K','p':6,'e':8,'threads':20,'pr':53,'er':40,'rr':45,'sp':True},
                {'name':'Core i9-13900K','p':8,'e':16,'threads':32,'pr':55,'er':43,'rr':47,'sp':True},
                {'name':'Core i7-13700K','p':8,'e':8,'threads':24,'pr':54,'er':42,'rr':46,'sp':True},
                {'name':'Core i5-13600K','p':6,'e':8,'threads':20,'pr':51,'er':39,'rr':44,'sp':True},
                {'name':'Core i5-12400','p':6,'e':0,'threads':12,'pr':44,'er':0,'rr':40,'sp':False}]
        # Detect AMD-style IFR terminology.
        corpus='\n'.join((n.prompt or '') for n in self.model.nodes[:9000]).lower()
        if 'precision boost overdrive' in corpus or 'curve optimizer' in corpus or 'amd cbs' in corpus:
            return [{'name':'Generic Ryzen','p':8,'e':0,'threads':16,'pr':50,'er':0,'rr':0,'sp':False,'amd':True}]
        return [{'name':'Generic CPU','p':8,'e':0,'threads':16,'pr':45,'er':0,'rr':42,'sp':False}]

    def _current_cpu_profile(self):
        name=self.cpu_profile.get() if hasattr(self,'cpu_profile') else ''
        for p in getattr(self,'cpu_profiles',[]):
            if p['name']==name:return p
        return self.cpu_profiles[0] if getattr(self,'cpu_profiles',[]) else {'name':'Generic CPU','p':8,'e':0,'threads':16,'pr':45,'er':0,'rr':42,'sp':False}

    def _init_virtual_hardware(self):
        # CPU controls kept as Tk vars for compatibility with existing OC simulation code.
        self.cpu_profile=tk.StringVar(); self.cpu_sp=tk.IntVar(value=100); self.cpu_bclk=tk.DoubleVar(value=100.0)
        self.cpu_pr=tk.IntVar(value=45); self.cpu_er=tk.IntVar(value=0); self.cpu_rr=tk.IntVar(value=42)
        self.cpu_profiles=self._cpu_profiles_for_bios(); self.cpu_profile.set(self.cpu_profiles[0]['name'] if self.cpu_profiles else 'Generic CPU')
        self.hw_ram_gb=tk.IntVar(value=32); self.hw_ram_speed=tk.IntVar(value=3200); self.hw_ram_voltage=tk.DoubleVar(value=1.35)
        self.hw_ram_channels=tk.StringVar(value='Dual'); self.hw_ram_timings=tk.StringVar(value='16-18-18-36')
        self.hw_ssd_model=tk.StringVar(value='Generic NVMe SSD'); self.hw_ssd_size=tk.IntVar(value=1000); self.hw_ssd_type=tk.StringVar(value='NVMe PCIe')
        self.hw_cpu_temp=tk.IntVar(value=34); self.hw_board_temp=tk.IntVar(value=31); self.hw_vcore=tk.DoubleVar(value=1.20)
        self.hw_cpu_fan=tk.IntVar(value=1200); self.hw_sys_fan1=tk.IntVar(value=900); self.hw_sys_fan2=tk.IntVar(value=0)
        self._apply_cpu_profile(update_ui=False)

    def _update_hw_summary(self):
        if not hasattr(self,'hw_summary'): return
        p=self._current_cpu_profile(); name=p.get('name','CPU')
        e=(' + %dE'%p.get('e',0)) if p.get('e',0) else ''
        txt=(f"{name}  {p.get('p',0)}P{e}  {p.get('threads',0)}T\n"
             f"RAM {self.hw_ram_gb.get()} GB @ {self.hw_ram_speed.get()} MT/s\n"
             "Telemetry not emulated")
        self.hw_summary.config(text=txt)

    def open_hardware_dialog(self):
        HardwareDialog(self)

    def hardware_runtime_value(self,n):
        """Return only runtime values that are intentionally emulated.

        The preview does not invent CPU telemetry, voltages, temperatures, fan speeds
        or storage data.  Those values are normally supplied by board-specific DXE/SMM
        code and cannot be recovered reliably from IFR alone.  RAM capacity and memory
        data rate are the only synthetic information fields exposed in the GUI.
        """
        p=(n.prompt or '').lower().strip()
        if not p:return None
        # Be conservative: do not override editable voltage/timing controls that merely
        # contain the words "memory" or "dram".
        if any(k in p for k in ('total memory','memory size','system memory','installed memory','memory capacity')):
            return f"{self.hw_ram_gb.get()*1024} MB"
        if any(k in p for k in ('dram frequency','memory frequency','memory speed','ddr frequency')):
            return f"{self.hw_ram_speed.get()} MT/s"
        return None

    def _build_cpu_controls(self):
        if not hasattr(self,'cpu_control_frame'):
            return
        for w in self.cpu_control_frame.winfo_children():
            w.destroy()
        p=self._current_cpu_profile(); row=0
        controls=[('BCLK',self.cpu_bclk,50,250,0.01),('Core ratio',self.cpu_pr,1,100,1)]
        if p.get('e',0)>0:
            controls.append(('E ratio',self.cpu_er,1,100,1))
        if not p.get('amd'):
            controls.append(('Ring',self.cpu_rr,1,100,1))
        if p.get('sp'):
            controls.append(('SP',self.cpu_sp,1,250,1))
        for lab,var,lo,hi,inc in controls:
            tk.Label(self.cpu_control_frame,text=lab,bg=self.PANEL2,fg=self.MUTED,anchor='w').grid(row=row,column=0,sticky='w',padx=(10,3))
            sp=tk.Spinbox(self.cpu_control_frame,textvariable=var,from_=lo,to=hi,width=8,increment=inc,command=self.update_cpu_sim)
            sp.grid(row=row,column=1,sticky='w',pady=1)
            sp.bind('<KeyRelease>',lambda e:self.update_cpu_sim())
            row+=1

    def _apply_cpu_profile(self, update_ui=True):
        p=self._current_cpu_profile()
        self.cpu_pr.set(p.get('pr',45))
        self.cpu_er.set(p.get('er',0))
        self.cpu_rr.set(p.get('rr',42))
        if update_ui and hasattr(self,'cpu_control_frame'):
            self._build_cpu_controls()
        if update_ui:
            self.update_cpu_sim()
        if hasattr(self,'hw_summary'):
            self._update_hw_summary()

    def sync_cpu_from_bios(self):
        try:
            v=self._numeric_value_from_prompt(['bclk'])
            if v and 50<=v<=400:self.cpu_bclk.set(v)
            # Ratios are intentionally conservative: use only obvious direct numeric controls.
            for var,alts in ((self.cpu_pr,[['p-core','ratio'],['cpu core','ratio limit'],['core','ratio']]),(self.cpu_er,[['e-core','ratio'],['efficient','ratio']]),(self.cpu_rr,[['ring','ratio'],['cache','ratio']])):
                for ks in alts:
                    v=self._numeric_value_from_prompt(ks)
                    if v and 1<=v<=120:var.set(int(round(v)));break
        except Exception:pass
        self.update_cpu_sim()

    def _configured_vcore(self):
        # Prefer explicit Override/Manual fields. Adaptive values are reported as configured, not as measured voltage.
        modes=[]
        for n in self.model.nodes:
            p=(n.prompt or '').lower()
            if n.qid is not None and ('core' in p and 'voltage' in p and ('mode' in p or 'core/cache voltage' in p)) and n.options:
                val=self.model.values.get(n.qid); lab=''
                for a,b,d in n.options:
                    if b==val:lab=a;break
                modes.append(lab)
        mode=' / '.join(x for x in modes if x)[:40] or 'Unknown'
        for n in self.model.nodes:
            p=(n.prompt or '').lower()
            if n.qid is None:continue
            if 'cpu core voltage override' in p or ('core' in p and 'voltage override' in p):
                v=self.model.values.get(n.qid)
                if v not in (None,0,''):return mode,str(v)
                if n.display_standard:return mode,n.display_standard
        return mode,'CPU/VF dependent'

    def update_cpu_sim(self):
        if not hasattr(self,'cpu_out'):
            if hasattr(self,'hw_summary'): self._update_hw_summary()
            return
        try:
            p=self._current_cpu_profile(); b=float(self.cpu_bclk.get()); pr=int(self.cpu_pr.get()); er=int(self.cpu_er.get()); rr=int(self.cpu_rr.get()); sp=int(self.cpu_sp.get())
            pf=b*pr; ef=b*er if p.get('e',0)>0 else 0; rf=b*rr if not p.get('amd') else 0; mode,vcore=self._configured_vcore()
            lines=['%s'%p.get('name','CPU'),'%dC / %dT'%(p.get('p',0)+p.get('e',0),p.get('threads',0)),'Core   %7.1f MHz'%pf]
            if p.get('e',0)>0: lines.append('E-core %7.1f MHz'%ef)
            if not p.get('amd'): lines.append('Ring   %7.1f MHz'%rf)
            lines += ['', 'Vcore mode: %s'%mode,'Configured: %s'%vcore]
            if p.get('sp'):
                ghz=pf/1000.0; est=max(0.65,min(1.95,1.20+(ghz-5.0)*0.10-(sp-100)*0.0015)); lines.append('SP model: ~%.3f V'%est)
            lines.append('(simulation, not telemetry)')
            self.cpu_out.config(text='\n'.join(lines))
        except Exception:self.cpu_out.config(text='Enter valid CPU simulation values.')

    def _pick_start_form(self):
        nav=self.model.primary_navigation()
        if nav:
            # Real firmware usually opens Main in Advanced Mode; never expose technical FormSet "Setup" as a page.
            for cap,f in nav:
                if (cap or '').strip().lower()=='main': return f
            return nav[0][1]
        for want in ('Main','Advanced','Extreme Tweaker','Ai Tweaker','OverClocking Performance Menu','Boot'):
            for f in self.model.forms:
                if (f.label() or '').strip().lower()==want.lower(): return f
        return self.model.forms[0] if self.model.forms else None

    def _build(self):
        hdrbg=self._mix(self.ACCENT,'#000000',0.88)
        hdr=tk.Frame(self,bg=hdrbg,height=70);hdr.pack(fill='x');hdr.pack_propagate(False)
        meta=getattr(self.model,'bios_meta',{}) or {}
        lp=meta.get('logo_path')
        if lp and os.path.isfile(lp):
            try:
                self.logo_img=tk.PhotoImage(file=lp)
                # keep firmware logos from consuming the whole header
                while self.logo_img.width()>180 or self.logo_img.height()>52:self.logo_img=self.logo_img.subsample(2,2)
                tk.Label(hdr,image=self.logo_img,bg=hdrbg).pack(side='left',padx=(14,8))
            except Exception as e: log('Logo preview warning: '+str(e)); self.logo_img=None
        tk.Label(hdr,text=self._meta_title(),bg=hdrbg,fg=self.FG,font=('Segoe UI',18,'bold')).pack(side='left',padx=12)
        src=meta.get('theme_source','generic')
        self.mode=tk.Label(hdr,text='Advanced Mode  |  IFR/HII Preview  |  '+self.SKIN+'  |  assets: '+src,bg=hdrbg,fg=self.MUTED,font=('Segoe UI',9))
        self.mode.pack(side='right',padx=20)

        self.tabs=tk.Frame(self,bg=self.TAB,height=40); self.tabs.pack(fill='x'); self.tabs.pack_propagate(False)

        crumb=tk.Frame(self,bg=self.PANEL2,height=34);crumb.pack(fill='x');crumb.pack_propagate(False)
        self.breadcrumb=tk.Label(crumb,text='',anchor='w',bg=self.PANEL2,fg='white',font=('Segoe UI',9,'bold'))
        self.breadcrumb.pack(side='left',fill='both',expand=True,padx=16)
        self.clock=tk.Label(crumb,text='',anchor='e',bg=self.PANEL2,fg=self.MUTED,font=('Segoe UI',9));self.clock.pack(side='right',padx=16)

        main=tk.Frame(self,bg=self.BG); main.pack(fill='both',expand=True,padx=10,pady=9)
        main.grid_rowconfigure(0,weight=1); main.grid_columnconfigure(0,weight=7); main.grid_columnconfigure(1,weight=2)
        left=tk.Frame(main,bg=self.PANEL);right=tk.Frame(main,bg=self.PANEL)
        left.grid(row=0,column=0,sticky='nsew',padx=(0,6)); right.grid(row=0,column=1,sticky='nsew',padx=(6,0))

        self.form_title=tk.Label(left,text='',anchor='w',bg=self.PANEL,fg=self.FG,font=('Segoe UI',13,'bold'),padx=15,pady=9);self.form_title.pack(fill='x')
        self.menu=tk.Listbox(left,font=('Consolas',10),bg=self.PANEL,fg=self.FG,selectbackground=self.SEL,selectforeground='white',
                             activestyle='none',highlightthickness=0,borderwidth=0,exportselection=False)
        self.menu.pack(fill='both',expand=True,padx=8,pady=(0,8))
        self.menu.bind('<<ListboxSelect>>',self.on_select); self.menu.bind('<Double-Button-1>',lambda e:self.activate())
        self.menu.bind('<Button-1>',lambda e:self.after_idle(self.update_help))

        tk.Label(right,text='Description / Limits',anchor='w',bg=self.PANEL2,fg=self.FG,font=('Segoe UI',10,'bold'),padx=12,pady=7).pack(fill='x')
        self.help=tk.Text(right,wrap='word',bg=self.PANEL,fg=self.FG,insertbackground='white',font=('Segoe UI',9),
                          state='disabled',relief='flat',highlightthickness=0,padx=11,pady=11)
        self.help.pack(fill='both',expand=True)

        # Compact virtual-hardware summary. Full configuration lives in a separate dialog,
        # so the help pane stays close to the proportions used by real firmware UIs.
        self._init_virtual_hardware()
        hw=tk.Frame(right,bg=self.PANEL2,height=118); hw.pack(fill='x',side='bottom'); hw.pack_propagate(False)
        tk.Label(hw,text='Preview hardware',anchor='w',bg=self.PANEL2,fg=self.FG,font=('Segoe UI',9,'bold'),padx=10,pady=5).pack(fill='x')
        self.hw_summary=tk.Label(hw,text='',justify='left',anchor='nw',bg=self.PANEL2,fg=self.MUTED,font=('Consolas',8),padx=10)
        self.hw_summary.pack(fill='both',expand=True)
        btns=tk.Frame(hw,bg=self.PANEL2); btns.pack(fill='x',padx=8,pady=(0,6))
        tk.Button(btns,text='Hardware...',command=self.open_hardware_dialog,width=12).pack(side='left')
        tk.Button(btns,text='Sync BIOS',command=self.sync_cpu_from_bios,width=11).pack(side='left',padx=5)
        self._update_hw_summary()

        footbg=self._mix(self.ACCENT,'#000000',0.88)
        foot=tk.Frame(self,bg=footbg,height=50);foot.pack(fill='x');foot.pack_propagate(False)
        self.footer=tk.Label(foot,text='↑↓ Select   Enter Edit/Open   ←→ Change   Esc Back   Tab/Shift+Tab Section   F10 Close',anchor='w',bg=footbg,fg=self.MUTED,font=('Segoe UI',9))
        self.footer.pack(side='left',padx=16,fill='y')
        tk.Button(foot,text='Back (Esc)',command=self.go_back,width=12).pack(side='right',padx=(4,14),pady=9)

    def _build_tabs(self):
        for w in self.tabs.winfo_children(): w.destroy()
        self.tab_buttons=[]; self.tab_forms=[]
        # Highest fidelity path: preserve the exact order of Ref entries in the firmware's root Setup form.
        nav=self.model.primary_navigation()
        if nav:
            self.tab_forms=nav
        else:
            used=set()
            for caption,keys in self.TAB_KEYWORDS:
                best=None; score=-1
                for f in self.model.forms:
                    title=(f.label() or '').strip().lower()
                    if not title or id(f) in used: continue
                    sc=0
                    for k in keys:
                        if title==k: sc=max(sc,100)
                        elif k in title: sc=max(sc,50+len(k))
                    if sc>score and sc>0: best=f; score=sc
                if best is not None:
                    used.add(id(best)); self.tab_forms.append(((best.label() or caption).strip(),best))
        if not self.tab_forms:
            for f in self.model.forms[:7]: self.tab_forms.append((f.label()[:18],f))
        for caption,f in self.tab_forms:
            b=tk.Button(self.tabs,text=caption,bd=0,relief='flat',font=('Segoe UI',9,'bold'),fg='white',
                        bg=self.TAB,activebackground=self.TABSEL,activeforeground='white',command=lambda ff=f:self.open_tab(ff),padx=13)
            b.pack(side='left',fill='y'); self.tab_buttons.append((b,f))

    def _update_tabs(self):
        for b,f in self.tab_buttons:
            active=(f is self.current_form) or (self.history and f in self.history)
            try:b.config(bg=self.TABSEL if active else self.TAB)
            except Exception:pass

    def open_tab(self,f):
        if not f:return
        self.history=[]; self.current_form=f; self.selected_index=0; self.render(False); self.menu.focus_set()

    def _cycle_tab(self,d):
        if not self.tab_forms:return 'break'
        cur=0
        for i,(_,f) in enumerate(self.tab_forms):
            if f is self.current_form or f in self.history: cur=i; break
        self.open_tab(self.tab_forms[(cur+d)%len(self.tab_forms)][1]); return 'break'

    def _bind_keys(self):
        self.bind('<Escape>',lambda e:self.go_back())
        self.bind('<Return>',lambda e:self.activate())
        self.bind('<space>',lambda e:self.activate())
        self.bind('<Right>',lambda e:self.change(+1))
        self.bind('<Left>',lambda e:self.change(-1))
        self.bind('<plus>',lambda e:self.change(+1)); self.bind('<KP_Add>',lambda e:self.change(+1))
        self.bind('<minus>',lambda e:self.change(-1)); self.bind('<KP_Subtract>',lambda e:self.change(-1))
        self.bind('<F10>',lambda e:self.close())
        self.bind('<Home>',lambda e:self._select(0)); self.bind('<End>',lambda e:self._select(max(0,len(self.nodes)-1)))
        self.bind('<Tab>',lambda e:self._cycle_tab(+1)); self.bind('<Shift-Tab>',lambda e:self._cycle_tab(-1))

    def _direct_items(self,form):
        out=[]
        def walk(n):
            for c in n.children:
                if c.kind in ('SuppressIf','GrayOutIf','DisableIf'): walk(c)
                elif c.kind!='FormSet': out.append(c)
        walk(form); return out

    def state(self,n):
        unknown=False; disabled=False
        for s in getattr(n,'visibility_scopes',[]):
            v=self.model.eval_condition(s.condition)
            if v is True:
                if s.kind=='SuppressIf': return 'hidden'
                if s.kind in ('GrayOutIf','DisableIf'): disabled=True
            elif v is None: unknown=True
        if disabled:return 'disabled'
        if unknown:return 'conditional'
        return 'visible'

    def range_text(self,n):
        return self.model.display_range_text(n)

    def render(self,keep_index=True):
        if not self.current_form:return
        old=self.selected_index if keep_index else 0
        self.title('UEFI BIOS Simulator - '+self.current_form.label())
        self.form_title.config(text=self.current_form.label())
        path=[x.label() for x in self.history]+[self.current_form.label()]
        self.breadcrumb.config(text='  >  '.join(path[-6:]))
        self.clock.config(text=time.strftime('%H:%M:%S')); self._update_tabs()
        self.menu.delete(0,'end'); self.nodes=[]; self.row_map={}
        for n in self._direct_items(self.current_form):
            if n.kind in ('Form','FormSet'):continue
            st=self.state(n)
            if st=='hidden':continue
            label=(n.prompt or '').replace('\n',' ').strip()
            # Many AMI forms contain hidden/internal helper questions with an empty
            # prompt.  Real firmware does not render those as a literal <N/A> row.
            if not label:
                continue
            val=self.value_text(n); rng=self.range_text(n)
            runtime=self.hardware_runtime_value(n)
            if runtime and not val: val='<%s>'%runtime
            if n.kind=='Ref': text='  %-56s >'%label
            elif val and rng: text='  %-48s %-18s  [%s]'%(label,val,rng)
            elif val: text='  %-54s %s'%(label,val)
            elif rng: text='  %-54s [%s]'%(label,rng)
            else: text='  '+label
            if st=='disabled': text='  [LOCKED] '+text.strip()
            elif st=='conditional': text='  [?] '+text.strip()
            idx=self.menu.size(); self.menu.insert('end',text); self.nodes.append(n); self.row_map[idx]=st
            try:
                if st=='disabled':self.menu.itemconfig(idx,fg=self.DISABLED)
                elif st=='conditional':self.menu.itemconfig(idx,fg=self.WARN)
                elif n.kind=='Ref':self.menu.itemconfig(idx,fg='#cfe4ff')
            except Exception:pass
        if self.nodes:
            self.selected_index=min(old,len(self.nodes)-1); self._select(self.selected_index)
            self.update_cpu_sim()
        else:
            self.selected_index=0; self.set_help('В этой форме нет видимых элементов при текущих симулируемых значениях.')

    def value_text(self,n):
        if n.qid is None:return ''
        v=self.model.values.get(n.qid)
        if n.kind=='CheckBox':return '<Enabled>' if v else '<Disabled>'
        if n.options:
            for lab,val,d in n.options:
                if val==v:return '<%s>'%(lab or str(val))
            return '<%s>'%v
        if n.kind=='Numeric':return '<%s>'%v
        if n.kind=='String':
            if v not in (None,0,''):return '<%s>'%v
            if n.display_standard:return '<%s>'%n.display_standard
            return '<Auto>'
        return ''

    def _select(self,idx):
        if not self.nodes:return
        idx=max(0,min(idx,len(self.nodes)-1)); self.selected_index=idx
        self.menu.selection_clear(0,'end');self.menu.selection_set(idx);self.menu.activate(idx);self.menu.see(idx);self.update_help()
    def on_select(self,event=None):
        s=self.menu.curselection()
        if s:self.selected_index=s[0];self.update_help()
    def current_node(self):
        s=self.menu.curselection();return self.nodes[s[0]] if s and s[0]<len(self.nodes) else None
    def set_help(self,text):
        self.help.config(state='normal');self.help.delete('1.0','end');self.help.insert('1.0',text);self.help.config(state='disabled')

    def update_help(self):
        n=self.current_node()
        if not n:return
        st=self.state(n);lines=[]
        if n.help:lines.append(n.help.strip())
        else:lines.append('No help text is available for this item.')
        runtime=self.hardware_runtime_value(n)
        if runtime: lines.append('\nVirtual reading: '+runtime)
        rng=self.range_text(n)
        if rng:
            lines.append('\nLimits: '+rng)
            if n.display_standard:lines.append('Default/Standard: '+n.display_standard)
        lines.append('\nType: %s'%n.kind);lines.append('State: %s'%st)
        if st=='disabled':lines.append('This item is locked by the current value of another BIOS option.')
        elif st=='conditional':lines.append('Visibility depends on an IFR expression that this preview cannot fully evaluate yet.')
        if n.qid is not None:lines.append('QuestionId: 0x%X'%n.qid)
        if n.varstore is not None:lines.append('VarStoreId: 0x%X'%n.varstore)
        if n.varoffset is not None:lines.append('VarOffset/Info: 0x%X'%n.varoffset)
        if n.kind=='Ref':lines.append('\nEnter: open submenu')
        elif n.kind=='CheckBox':lines.append('\nEnter/Space: toggle')
        elif n.options:lines.append('\nEnter: option list   Left/Right: previous/next')
        elif n.kind in ('Numeric','String'):lines.append('\nEnter: type value   Left/Right: decrease/increase when numeric limits are known')
        self.set_help('\n'.join(lines))

    def _parse_user_numeric(self,n,s):
        s=(s or '').strip().replace(',','.')
        # accept a pasted unit suffix, e.g. 1.35V
        if n.display_unit and s.lower().endswith(n.display_unit.lower()): s=s[:-len(n.display_unit)].strip()
        try:v=float(s)
        except Exception:raise ValueError('Введите числовое значение.')
        mn=n.display_min;mx=n.display_max;step=n.display_step
        if mn is not None and v < mn-1e-12:raise ValueError('Минимум: %s%s'%(self.model._fmt_num(mn),n.display_unit))
        if mx is not None and v > mx+1e-12:raise ValueError('Максимум: %s%s'%(self.model._fmt_num(mx),n.display_unit))
        if step and mn is not None:
            slots=round((v-mn)/step); snapped=mn+slots*step
            if abs(v-snapped)>max(1e-9,abs(step)*1e-5):
                raise ValueError('Значение должно соответствовать шагу %s%s.'%(self.model._fmt_num(step),n.display_unit))
            v=snapped
        return self.model._fmt_num(v)+(n.display_unit or '')

    def _set_sim_value(self,qid,value):
        self.model.values[qid]=value
        try:self.model.modified_qids.add(qid)
        except Exception:pass

    def activate(self):
        n=self.current_node()
        if not n:return 'break'
        if self.state(n)=='disabled':self.bell();return 'break'
        if n.kind=='Ref' and n.target_form in self.model.form_by_id:
            self.history.append(self.current_form);self.current_form=self.model.form_by_id[n.target_form];self.selected_index=0;self.render(False);return 'break'
        if n.qid is None:return 'break'
        if n.kind=='CheckBox':
            self._set_sim_value(n.qid,0 if self.model.values.get(n.qid) else 1);self.render();return 'break'
        if n.options:
            options=[((lab or str(val)),val) for lab,val,d in n.options]
            dlg=ChoiceDialog(self,n.prompt or 'Select',options,self.model.values.get(n.qid))
            if dlg.result is not None:self._set_sim_value(n.qid,dlg.result);self.render()
            return 'break'
        if n.kind=='Numeric':
            cur=self.model.values.get(n.qid,n.min or 0);prompt='Введите значение'
            if n.min is not None:prompt+=' (%s .. %s, шаг %s)'%(n.min,n.max,n.step or 1)
            v=simpledialog.askinteger(n.prompt or 'Numeric',prompt,parent=self,initialvalue=cur,minvalue=n.min,maxvalue=n.max)
            if v is not None:
                step=n.step or 1
                if n.min is not None and step>1:v=n.min+round((v-n.min)/float(step))*step
                if n.min is not None:v=max(n.min,v)
                if n.max is not None:v=min(n.max,v)
                self._set_sim_value(n.qid,int(v));self.render()
            return 'break'
        if n.kind=='String':
            cur=self.model.values.get(n.qid,''); cur='' if cur==0 else cur
            if n.display_min is not None and n.display_max is not None:
                while True:
                    prompt='Введите значение\nДопустимо: %s'%(self.range_text(n))
                    v=simpledialog.askstring(n.prompt or 'Value',prompt,parent=self,initialvalue=str(cur or ''))
                    if v is None:return 'break'
                    try:self._set_sim_value(n.qid,self._parse_user_numeric(n,v));break
                    except ValueError as e:messagebox.showwarning(n.prompt or 'Value',str(e),parent=self)
                self.render();return 'break'
            v=simpledialog.askstring(n.prompt or 'String','Введите значение:',parent=self,initialvalue=str(cur))
            if v is not None:self._set_sim_value(n.qid,v);self.render()
            return 'break'
        return 'break'

    def change(self,d):
        n=self.current_node()
        if not n or self.state(n)=='disabled':return 'break'
        if n.qid is None:return 'break'
        if n.kind=='CheckBox':self._set_sim_value(n.qid,0 if self.model.values.get(n.qid) else 1);self.render();return 'break'
        if n.options:
            vals=[x[1] for x in n.options];cur=self.model.values.get(n.qid);idx=vals.index(cur) if cur in vals else 0
            self._set_sim_value(n.qid,vals[(idx+d)%len(vals)]);self.render();return 'break'
        if n.kind=='Numeric':
            cur=self.model.values.get(n.qid,n.min or 0);step=n.step or 1;nv=cur+d*step
            if n.min is not None:nv=max(n.min,nv)
            if n.max is not None:nv=min(n.max,nv)
            self._set_sim_value(n.qid,nv);self.render();return 'break'
        if n.kind=='String' and n.display_min is not None and n.display_max is not None:
            # Arrow keys also work for vendor String-backed numeric controls.
            step=n.display_step or 1.0
            cur=self.model.values.get(n.qid)
            try:
                raw=str(cur).replace(',','.');
                if n.display_unit and raw.lower().endswith(n.display_unit.lower()):raw=raw[:-len(n.display_unit)]
                v=float(raw)
            except Exception:
                v=n.display_min
            v=max(n.display_min,min(n.display_max,v+d*step))
            self._set_sim_value(n.qid,self.model._fmt_num(v)+(n.display_unit or ''));self.render();return 'break'
        return 'break'

    def go_back(self):
        if self.history:
            self.current_form=self.history.pop();self.selected_index=0;self.render(False);return 'break'
        self.close();return 'break'
    def close(self):
        try:self.grab_release()
        except Exception:pass
        self.destroy()

if __name__=='__main__':
    try: App().mainloop()
    except Exception:
        traceback.print_exc(); input("Press Enter to close...")
