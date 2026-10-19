"""Isolated Python contract tests; all native/deployment evidence is synthetic in memory."""
import copy
from contextlib import contextmanager
import importlib.util
import json
from pathlib import Path
import tempfile
import types
import unittest
from unittest.mock import patch
import ast

P = Path(__file__).with_name('chapter8_publication_core.py')
spec = importlib.util.spec_from_file_location('chapter8_publication_candidate', P)
core = importlib.util.module_from_spec(spec)
# Dataclasses require this private test-owned name; production uses normal imports.
import sys
sys.modules[spec.name] = core
spec.loader.exec_module(core)
with patch.dict(sys.modules, {'chapter8_publication_core':core}):
    rspec = importlib.util.spec_from_file_location('chapter8_publication_runtime_candidate',
        P.with_name('chapter8_publication_runtime.py'))
    runtime = importlib.util.module_from_spec(rspec)
    rspec.loader.exec_module(runtime)
S8, Q8 = '8'*40, '9'*40
NAMES = ['BC4lean.Assembly.BaumConnesProperty','BC4lean.Assembly.BaumConnesConjecture',
         'BC4lean.Chapter8Examples.baumConnesProperty_unit']
MODS = ['BC4lean.BaumConnesProperty','BC4lean.UnitAssemblyEquivalence']
FROZEN = core.BEGIN7 + '\n<section id="chapter7-source-index">retained bytes</section>\n' + core.END7 + '\n'


def audit():
    def item(kind, ready, names, required=None):
        return dict(statement_kind=kind, ready=ready, linked_declarations=names,
                    required_declarations=names if required is None else required)
    return dict(schema='chapter8.actual.native-milestone-audit.v1', schema_version=1,
        status='verified_milestone', milestone_verified=True, chapter_complete=False,
        general_conjecture_proved=False, source_revision=S8, modules=MODS,
        target_inventory={core.PROPERTY:item('definition',True,[NAMES[0]]),
                          core.CONJECTURE:item('conjecture',False,[NAMES[1]],[])},
        milestone_inventory={core.UNIT:item('theorem',True,[NAMES[2]])},
        statement_definition_declarations={core.CONJECTURE:[NAMES[1]]},
        blueprint_links=NAMES, linked_declarations={n:dict(name=n,module=MODS[0 if i<2 else 1]) for i,n in enumerate(NAMES)})


def tex():
    return '\n'.join([
        r'\begin{definition}\label{' + core.PROPERTY + r'}\leanok\lean{' + NAMES[0] + r'}\end{definition}',
        r'\begin{conjecture}\label{' + core.CONJECTURE + r'}\notready\uses{' + core.PROPERTY + r'}\lean{' + NAMES[1] + r'}\end{conjecture}',
        r'\begin{theorem}\label{' + core.UNIT + r'}\leanok\uses{' + core.PROPERTY + r'}\lean{' + NAMES[2] + r'}\end{theorem}',
        r'\begin{proof}\leanok By independently tested mathematical work.\end{proof}'])


def source_href(name):
    return 'https://ylsong1024.github.io/BC4lean/docs/find/#doc/' + name


def rendered():
    parts=[]
    for label,kind,name,ready in [(core.PROPERTY,'definition',NAMES[0],True),
          (core.CONJECTURE,'conjecture',NAMES[1],False),(core.UNIT,'theorem',NAMES[2],True)]:
        parts.append('<div class="'+kind+'_thmwrapper" id="'+label+'"><div class="thm_header_extras">'
                     + ('✓' if ready else '') + '</div><a href="'+source_href(name)+'">Lean</a></div>')
        if label==core.UNIT:
            parts.append('<div class="proof_content">Proof ✓</div>')
    return '\n'.join(parts)


def graph(extra='', document=False):
    dot='strict digraph "" { graph [bgcolor=transparent]; node [label="\\N",penwidth=1.8]; edge [arrowhead=vee]; '
    for label,kind,ready in [(core.PROPERTY,'definition',True),(core.CONJECTURE,'conjecture',False),(core.UNIT,'theorem',True)]:
        attrs='color=green,fillcolor="'+('#B0ECA3' if kind=='definition' else '#1CAC78')+'",style=filled' if ready else 'color="#FFAA33"'
        dot += '"'+label+'" ['+attrs+',label="'+label.split(':',1)[-1]+'",shape='+('box' if kind=='definition' else 'ellipse')+']; '
    dot += '"'+core.PROPERTY+'" -> "'+core.CONJECTURE+'"; "'+core.PROPERTY+'" -> "'+core.UNIT+'"; '+extra+'}'
    modals=''.join('<div class="dep-modal-container" id="'+label+'_modal"><a href="'+source_href(name)+'">Lean</a></div>'
                   for label,name in [(core.PROPERTY,NAMES[0]),(core.CONJECTURE,NAMES[1]),(core.UNIT,NAMES[2])])
    reference=json.loads((P.parents[1]/'docs/audits/chapter8/RendererScaffold.json').read_text())
    scripts=[]
    for script in reference['scripts']:
        attrs=' '.join(k+'=\"'+v+'\"' for k,v in script['attributes'].items())
        body=script['body'] if 'body' in script else script['prefix']+dot+script['suffix']
        scripts.append('<script '+attrs+'>'+body+'</script>')
    return ''.join(scripts)+modals


class Tests(unittest.TestCase):
    def setUp(self):
        scratch=P.parent/'isolated-temporary-work'; scratch.mkdir(exist_ok=True)
        self.t = tempfile.TemporaryDirectory(prefix='case-',dir=scratch); self.addCleanup(self.t.cleanup)
        self.root=Path(self.t.name); self.site=self.root/'site'; self.site.mkdir()
        self.events=[]; self.opened=False
        @contextmanager
        def fresh():
            self.assertFalse(self.opened); self.opened=True; self.events.append('open')
            try:
                yield {'check_website':types.SimpleNamespace(check_site=self.oldcheck),
                       'update_chapter5_finder':types.SimpleNamespace(code_only=lambda s:s,
                           declaration_lines=lambda s:{n:i+1 for i,n in enumerate(NAMES)})}
            finally:
                self.opened=False; self.events.append('close')
        self.retained=types.SimpleNamespace(audit={'source_revision':core.S7},audit_sha256='7'*64,
                  frozen_finder_block=FROZEN,helpers=types.SimpleNamespace(open=fresh))
        self.provider=types.SimpleNamespace(verify_published_chapter7=self.retainedcheck)
        self.a=audit()
        self.a['source_sha256']={core.TEX8:core.digest(tex().encode())}
        self.ctx=core.Context(self.root,self.a,'a'*64,S8,
            {n:(MODS[0 if i<2 else 1].replace('.','/')+'.lean',i+1) for i,n in enumerate(NAMES)},
            self.retained,self.provider)
        self.put(self.root,core.TEX7,'unchanged 7')
        self.put(self.root,core.TEX8,tex())
        self.put(self.site,'docs/find/index.html',core.render_finder(FROZEN,self.ctx))
        self.put(self.site,'index.html','Chapter 7 is verified. The general Baum-Connes conjecture remains unproved. '
                     'The trivial-group assembly map is verified in both degrees.')
        for rel,body in [('blueprint/ch-conjecture-and-examples.html',rendered()),
                ('blueprint/dep_graph_chapter_8.html',graph()),('blueprint/dep_graph_document.html',graph()),
                ('blueprint/ch-assembly-map.html','retained chapter7'),('blueprint/dep_graph_chapter_7.html','retained graph7')]:
            self.put(self.site,rel,body)
    def put(self,root,rel,text):
        p=root/rel; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(text); return p
    def oldcheck(self,site,q):
        self.assertTrue(self.opened); self.events.append('5/6'); self.assertEqual(q,Q8)
        return {'revision':q,'pages':{}}
    def retainedcheck(self,*args):
        self.assertFalse(self.opened); self.events.append('retained7-v3')
        return {'chapter7_retained_rendered_checks':{'chapter_complete':True},
                'current_general_conjecture_scope':{'general_conjecture_status':'pending'}}
    def test_full_isolated_contract(self):
        result=core.check_site(self.site,Q8,self.ctx)
        self.assertEqual(self.events,['open','5/6','close','retained7-v3'])
        self.assertFalse(result['chapter8']['chapter_complete'])
        self.assertFalse(result['chapter8']['general_conjecture_proved'])
        self.assertEqual(result['chapter7_mathematical_source_revision'],core.S7)
        self.assertEqual(result['chapter8_mathematical_source_revision'],S8)
    def test_finder_idempotent(self):
        text=(self.site/'docs/find/index.html').read_text()
        self.assertEqual(core.render_finder(text,self.ctx),text)
    def test_s7_preserved_exact(self):
        text=(self.site/'docs/find/index.html').read_text().replace('retained bytes','edited')
        with self.assertRaises(ValueError): core.verify_finder(text,self.ctx)
    def test_wrong_source_revision(self):
        text=(self.site/'docs/find/index.html').read_text().replace(S8,Q8)
        with self.assertRaises(ValueError): core.verify_finder(text,self.ctx)
    def test_wrong_source_line(self):
        text=(self.site/'docs/find/index.html').read_text().replace('#L1','#L99')
        with self.assertRaises(ValueError): core.verify_finder(text,self.ctx)
    def test_duplicate_source_link(self):
        text=(self.site/'docs/find/index.html').read_text(); start=text.rfind('<tr',0,text.index('data-chapter8-declaration')); end=text.index('</tr>',start)+5
        with self.assertRaises(ValueError): core.verify_finder(text+text[start:end],self.ctx)
    def test_duplicate_marker(self):
        with self.assertRaises(ValueError): core.render_finder(FROZEN+FROZEN,self.ctx)
    def test_general_claim_rejected(self):
        self.a['general_conjecture_proved']=True
        with self.assertRaises(ValueError): core.audit8_shape(self.a,S8)
    def test_general_ready_rejected(self):
        self.a['target_inventory'][core.CONJECTURE]['ready']=True
        with self.assertRaises(ValueError): core.audit8_shape(self.a,S8)
    def test_general_assumed_endpoint_rejected(self):
        self.a['target_inventory'][core.CONJECTURE]['required_declarations']=[NAMES[1]]
        with self.assertRaises(ValueError): core.audit8_shape(self.a,S8)
    def test_missing_statement_definition_rejected(self):
        self.a['statement_definition_declarations']={}
        with self.assertRaises(ValueError): core.audit8_shape(self.a,S8)
    def test_missing_unit_milestone(self):
        self.a['milestone_inventory']={}
        with self.assertRaises(ValueError): core.audit8_shape(self.a,S8)
    def test_general_source_leanok(self):
        with self.assertRaises(ValueError): core.tex_source(tex().replace(r'\notready',r'\leanok'), {**self.a['target_inventory'],**self.a['milestone_inventory']})
    def test_general_source_checked_proof(self):
        with self.assertRaises(ValueError): core.tex_source(tex().replace(r'\end{conjecture}',r'\end{conjecture}\begin{proof}\leanok\end{proof}'), {**self.a['target_inventory'],**self.a['milestone_inventory']})
    def test_unattached_source_proof(self):
        with self.assertRaises(ValueError): core.tex_source(tex()+r'\begin{proof}\leanok\end{proof}', {**self.a['target_inventory'],**self.a['milestone_inventory']})
    def test_source_link_mismatch(self):
        with self.assertRaises(ValueError): core.tex_source(tex().replace(NAMES[2],NAMES[0]), {**self.a['target_inventory'],**self.a['milestone_inventory']})
    def test_missing_rendered_wrapper(self):
        self.put(self.site,'blueprint/ch-conjecture-and-examples.html',rendered().replace('id="'+core.UNIT+'"','id="wrong"'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_false_conjecture_checkmark(self):
        self.put(self.site,'blueprint/ch-conjecture-and-examples.html',rendered().replace('id="'+core.CONJECTURE+'"><div class="thm_header_extras">','id="'+core.CONJECTURE+'"><div class="thm_header_extras">✓'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_duplicate_html_attribute(self):
        with self.assertRaises(ValueError): core.Page().finish('<a id="a" id="b"></a>')
    def test_pending_graph_filled(self):
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',graph().replace('color="#FFAA33"','color="#FFAA33",style=filled'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_pending_graph_any_fillcolor(self):
        self.put(self.site,'blueprint/dep_graph_document.html',graph().replace('color="#FFAA33"','color="#FFAA33",fillcolor="white"'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_graph_popup_missing_link(self):
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',graph().replace(source_href(NAMES[1]),'#broken'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_wrong_declaration_destination(self):
        self.put(self.site,'blueprint/ch-conjecture-and-examples.html',rendered().replace('https://ylsong1024.github.io','https://example.invalid'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_q_equals_s_rejected(self):
        with self.assertRaises(ValueError): core.check_site(self.site,S8,self.ctx)
    def test_homepage_false_flag(self):
        self.put(self.site,'index.html',(self.site/'index.html').read_text()+'<div data-general-baum-connes-proved="true"></div>')
        with self.assertRaises(ValueError): core.check_site(self.site,Q8,self.ctx)
    def test_unsafe_path(self):
        for path in ['../x','/tmp/x','a/../x','a\\x','./a','a//b']:
            with self.subTest(path=path), self.assertRaises(ValueError): core.safe_relative(path)
    def test_duplicate_json_key(self):
        with self.assertRaises(ValueError): core.object_json(b'{"a":1,"a":2}')
    def test_dot_full_parser_adversaries(self):
        bad=['digraph { "x" [color=red][color=green]; }',
             'digraph { "x" [color=red,color=green]; }',
             'digraph { "x" [color=red]; "x" [color=green]; }',
             'digraph { node [style=filled]; "x" [color=red]; }',
             'digraph { node [fillcolor=white]; "x" [color=red]; }',
             'digraph { node [color=red]; "x" [color=red]; }',
             'digraph { "x" [color=red]; } digraph {}',
             'digraph { "x" [color=red]; arbitrary = green; }',
             'digraph { "x" [color=red]; "x" -> "y"; }']
        for dot in bad:
            with self.subTest(dot=dot), self.assertRaises(ValueError): core.parse_dot(dot)
    def test_validate_before_helpers_and_audit(self):
        data=b'source'; self.a['source_sha256']={m.replace('.','/')+'.lean':core.digest(data) for m in MODS}
        for rel in self.a['source_sha256']: self.put(self.root,rel,data.decode())
        ap=self.put(self.root,core.AUDIT8,json.dumps(self.a))
        provider=types.SimpleNamespace(RepositoryReader=lambda root:root,validate=lambda r,m,n:self.validated(),
                                      verify_published_chapter7=self.retainedcheck)
        def loader(root,path,source_revision,retained_provider=None):
            self.assertEqual(self.events,['validate']); self.events.append('audit8-replay')
            self.assertIs(retained_provider,self.retained)
            return json.loads(ap.read_bytes()),core.digest(ap.read_bytes())
        value=core.context(self.root,ap,S8,provider,{},MODS,loader,lambda rev,path:data)
        self.assertEqual(self.events,['validate','audit8-replay','open','close'])
        self.assertEqual(len(value.locations),3)
    def validated(self):
        self.assertEqual(self.events,[]); self.assertFalse(self.opened); self.events.append('validate'); return self.retained
    def test_context_rejects_historical_origin(self):
        self.a['linked_declarations'][NAMES[0]]['module']='BC4lean.AssemblyColimit'
        ap=self.put(self.root,core.AUDIT8,json.dumps(self.a))
        provider=types.SimpleNamespace(RepositoryReader=lambda root:root,validate=lambda *a:self.retained)
        with self.assertRaises(ValueError): core.context(self.root,ap,S8,provider,{},MODS,
            lambda *a,**kw:(self.a,core.digest(ap.read_bytes())),lambda *a:b'')
    def test_context_rejects_loader_raw_mismatch(self):
        ap=self.put(self.root,core.AUDIT8,json.dumps(self.a))
        provider=types.SimpleNamespace(RepositoryReader=lambda root:root,validate=lambda *a:self.retained)
        with self.assertRaises(ValueError): core.context(self.root,ap,S8,provider,{},MODS,
            lambda *a,**kw:(self.a,'0'*64),lambda *a:b'')

    def test_all_candidate_python_parses(self):
        for filename in ['chapter8_publication_core.py','chapter8_publication_runtime.py',
                         'update_chapter8_finder.py','check_chapter8_website.py','verify_live_chapter8.py',
                         'test_chapter8_publication.py','run_chapter8_publication_tests.py']:
            path=P.parent/filename
            ast.parse(path.read_text(), filename=str(path))
    def test_project_only_http_urls(self):
        for url in ['https://ylsong1024.github.io/BC4lean/site-version.json',
                    'https://raw.githubusercontent.com/ylsong1024/BC4lean/'+S8+'/BC4lean/Test.lean',
                    'https://github.com/ylsong1024/BC4lean/blob/'+S8+'/BC4lean/Test.lean#L1']:
            runtime.allowed_url(url)
        for url in ['http://github.com/ylsong1024/BC4lean/', 'https://example.invalid/BC4lean/',
                    'https://github.com/other/repo/', 'https://user@github.com/ylsong1024/BC4lean/',
                    'https://github.com:443/ylsong1024/BC4lean/']:
            with self.subTest(url=url), self.assertRaises(ValueError): runtime.allowed_url(url)
    def test_verified_module_precise_bytes_and_cleanup(self):
        name='_isolated_candidate_dependency'
        with runtime.verified_module(self.root/'unread.py',b'value = 3',name) as module:
            self.assertIs(sys.modules[name],module); self.assertEqual(module.value,3)
        self.assertNotIn(name,sys.modules)
    def test_verified_module_rejects_existing_name(self):
        with patch.dict(sys.modules,{'_existing_candidate_dependency':types.ModuleType('existing')}):
            with self.assertRaises(ValueError):
                with runtime.verified_module(self.root/'unread.py',b'value=4','_existing_candidate_dependency'): pass
    def test_future_live_pending_deployment_has_no_success_receipt(self):
        output=self.root/'outside-evidence'
        class FakeHTTP:
            responses=[]
            def fetch(self,url,path,method='GET'):
                data=json.dumps({'revision':'0'*40}).encode()
                path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(data); return data
        def pure_git(root,*args): return Q8.encode() if args[0]=='rev-parse' else b''
        with patch.object(runtime,'git_bytes',pure_git), self.assertRaises(ValueError):
            runtime.fetch_actual_live(self.root,Q8,self.ctx,output,FakeHTTP())
        self.assertFalse((output/'receipt.json').exists())
    def test_future_live_dirty_checkout_no_fetch(self):
        def pure_git(root,*args): return Q8.encode() if args[0]=='rev-parse' else b'dirty'
        class NeverFetch:
            def fetch(self,*args,**kwargs): raise AssertionError('HTTP must not run')
        with patch.object(runtime,'git_bytes',pure_git), self.assertRaises(ValueError):
            runtime.fetch_actual_live(self.root,Q8,self.ctx,self.root/'never-evidence',NeverFetch())
    def test_provider_wrong_digest_before_git_import(self):
        self.put(self.root,core.AUDIT8,json.dumps(self.a))
        self.put(self.root,runtime.PROVIDER,'raise AssertionError("must not execute")')
        with patch.object(runtime,'git_bytes',side_effect=AssertionError('Git must not run')):
            with self.assertRaises(ValueError):
                with runtime.load_context(self.root,S8,'0'*64): pass
    def test_empty_provider_digest_rejected(self):
        with self.assertRaises(ValueError):
            with runtime.load_context(self.root,S8,''): pass
    def test_malformed_dot_rejects_missing_separator(self):
        with self.assertRaises(ValueError): core.parse_dot('digraph { "x" [color=red shape=ellipse]; }')
    def test_even_backslash_tex_comment_cannot_hide_pending_marker(self):
        source=tex().replace('\\notready',r'\\% comment'+'\n'+r'\notready')
        core.tex_source(source,{**self.a['target_inventory'],**self.a['milestone_inventory']})


    def test_effective_template_hex_quote_injection(self):
        payload=r'color="#FFAA33",label="baum-connes\x22,fillcolor=green,style=filled,comment=\x22"'
        poisoned=graph().replace('color="#FFAA33",label="baum-connes"',payload)
        nodes,_=core.parse_dot(core.effective_dot(poisoned))
        self.assertEqual(nodes[core.CONJECTURE]['fillcolor'],'green')
        self.assertEqual(nodes[core.CONJECTURE]['style'],'filled')
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',poisoned)
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_effective_template_unicode_quote_injection(self):
        payload=r'color="#FFAA33",label="baum-connes\u0022,fillcolor=green,style=filled,comment=\u0022"'
        self.put(self.site,'blueprint/dep_graph_document.html',graph().replace('color="#FFAA33",label="baum-connes"',payload))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_template_interpolation_rejected(self):
        with self.assertRaises(ValueError): core.effective_dot('g.renderDot(`digraph { ${value} }`)')
    def test_extra_nonliteral_graph_call_rejected(self):
        with self.assertRaises(ValueError): core.effective_dot(graph()+'<script>g.renderDot(other)</script>')
    def test_static_template_decode(self):
        self.assertEqual(core.decode_static_template(r'\x41\u0042\u{43}\N\`\$'), 'ABCN`$')
        self.assertEqual(core.decode_static_template('a\\\r\nb'), 'ab')
        self.assertEqual(core.decode_static_template('a\r\nb'), 'a\nb')
    def test_invalid_template_escapes(self):
        for raw in [r'\x2',r'\u002',r'\u{110000}',r'\uD800',r'\8',r'\01','trailing\\']:
            with self.subTest(raw=raw), self.assertRaises(ValueError): core.decode_static_template(raw)


    def test_swapped_declaration_ids_rejected(self):
        text=(self.site/'docs/find/index.html').read_text()
        text=text.replace('id="doc/'+NAMES[0]+'"','id="swap"')
        text=text.replace('id="doc/'+NAMES[1]+'"','id="doc/'+NAMES[0]+'"')
        text=text.replace('id="swap"','id="doc/'+NAMES[1]+'"')
        with self.assertRaises(ValueError): core.verify_finder(text,self.ctx)
    def test_new_anchor_outside_finder8_rejected(self):
        extra='<span id="doc/'+NAMES[0]+'"></span>'
        with self.assertRaises(ValueError): core.render_finder(FROZEN+extra,self.ctx)
    def test_bare_modal_id_rejected(self):
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',graph().replace(core.CONJECTURE+'_modal',core.CONJECTURE))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_proof_before_first_statement_rejected(self):
        self.put(self.site,'blueprint/ch-conjecture-and-examples.html','<div class="proof_content">Proof ✓</div>'+rendered())
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)


    def test_browser_script_end_in_label_rejected(self):
        poisoned=graph().replace('color="#FFAA33",label="baum-connes"','color="#FFAA33",label="before</script>after"')
        with self.assertRaises(ValueError): core.effective_dot(poisoned)
    def test_escaped_identifier_second_renderer_rejected(self):
        text=graph().replace('.on("end", interactive);',r'.on("end", interactive); graph.render\u0044ot(graphVariable);')
        with self.assertRaises(ValueError): core.effective_dot(text)
    def test_commented_renderer_rejected(self):
        text=graph().replace('.renderDot(`','// .renderDot(`')
        with self.assertRaises(ValueError): core.effective_dot(text)
    def test_extra_external_graph_script_rejected(self):
        with self.assertRaises(ValueError): core.effective_dot(graph()+'<script src="https://example.invalid/evil.js"></script>')


    def test_pending_checkmark_outside_header_rejected(self):
        text=rendered().replace('id="'+core.CONJECTURE+'">','id="'+core.CONJECTURE+'">✓')
        self.put(self.site,'blueprint/ch-conjecture-and-examples.html',text)
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_pending_node_hidden_by_attributes_rejected(self):
        text=graph().replace('color="#FFAA33"','color="#FFAA33",penwidth=0,fontcolor="#00000000"')
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',text)
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_checked_green_background_rejected(self):
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',graph().replace('bgcolor=transparent','bgcolor=green'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)


    def test_source8_mutation_after_replay_rejected(self):
        self.put(self.root,core.TEX8,tex()+'\nChanged prose.')
        with self.assertRaises(ValueError): core.check_site(self.site,Q8,self.ctx)
    def test_graph_caption_mismatch_rejected(self):
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',graph().replace('label="baum-connes"','label="already-proved"'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_invisible_graph_dependency_rejected(self):
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',graph().replace('"'+core.PROPERTY+'" -> "'+core.UNIT+'";',
             '"'+core.PROPERTY+'" -> "'+core.UNIT+'" [style=invis];'))
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)
    def test_pending_popup_checkmark_rejected(self):
        text=graph().replace('id="'+core.CONJECTURE+'_modal">','id="'+core.CONJECTURE+'_modal">✓')
        self.put(self.site,'blueprint/dep_graph_chapter_8.html',text)
        with self.assertRaises(ValueError): core.validate_rendered(self.site,tex(),self.ctx)


    def test_self_closing_script_rejected(self):
        text=graph().replace('<script src="js/jquery.min.js" type="text/javascript"></script>',
                             '<script src="js/jquery.min.js" type="text/javascript"/>')
        with self.assertRaises(ValueError): core.effective_dot(text)
    def test_inert_graph_container_rejected(self):
        for tag in ['template','noscript','textarea','plaintext','xmp','iframe','select']:
            with self.subTest(tag=tag),self.assertRaises(ValueError): core.effective_dot('<'+tag+'>'+graph()+'</'+tag+'>')
    def test_inert_finder_container_rejected(self):
        text=(self.site/'docs/find/index.html').read_text()
        with self.assertRaises(ValueError): core.verify_finder('<template>'+text+'</template>',self.ctx)
    def test_self_closing_statement_wrapper_rejected(self):
        text=rendered().replace('id="'+core.CONJECTURE+'">','id="'+core.CONJECTURE+'"/>')
        with self.assertRaises(ValueError): core.Page().finish(text)


if __name__=='__main__': unittest.main()
