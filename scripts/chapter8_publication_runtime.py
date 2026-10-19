"""Connect Chapter 8 publication commands to strictly verified native evidence."""
import argparse
from contextlib import contextmanager, ExitStack
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import types
from urllib.parse import quote, unquote, urlsplit
import urllib.request

import chapter8_publication_core as core

PROVIDER = 'scripts/check_chapter7_retained.py'
BASELINE = 'docs/audits/chapter8/Chapter7Baseline.json'
BASELINE_SHA = '1518087f749f7a6cf0b61b1cfae442ab34f22e4864371f96a1f8dee0454c3035'
REVIEWED_PROVIDER_SHA256 = 'dcc7a783f842e8196b71bd6e1499e00821e98214e8efbc81bc648ca41628d7d8'
AUDITOR = 'scripts/audit_chapter8.py'
INVENTORY = 'docs/audits/chapter8/inventory.json'
BASE = 'https://ylsong1024.github.io/BC4lean/'
RAW = 'https://raw.githubusercontent.com/ylsong1024/BC4lean/'
BLOB = 'https://github.com/ylsong1024/BC4lean/blob/'


def git_bytes(root, *arguments):
    result = subprocess.run(['git', *arguments], cwd=root, check=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    return result.stdout


def blob_reader(root):
    def read(revision, relative):
        core.require(core.REV.fullmatch(revision or ''), 'Invalid immutable source commit')
        core.safe_relative(relative)
        return git_bytes(root, 'show', revision + ':' + relative)
    return read


@contextmanager
def verified_module(path, data, name):
    """Execute precisely the captured reviewed bytes, then remove our own module."""
    core.require(name not in sys.modules, 'Pre-existing publication dependency module')
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ''
    sys.modules[name] = module
    try:
        exec(compile(data, str(path), 'exec'), module.__dict__)
        yield module
    finally:
        core.require(sys.modules.get(name) is module, 'Publication dependency module replaced')
        del sys.modules[name]


@contextmanager
def load_context(root, source_revision, provider_sha256):
    root = Path(root).resolve(strict=True)
    core.require(core.REV.fullmatch(source_revision or ''), 'Full S8 is required; no inferred pin')
    core.require(core.SHA.fullmatch(provider_sha256 or '')
                 and provider_sha256 == REVIEWED_PROVIDER_SHA256,
                 'Explicit digest must equal the independently reviewed v4 production adapter')
    audit_path = root / core.AUDIT8
    raw = core.read(root, core.AUDIT8)
    audit = core.object_json(raw)
    provider_bytes = core.read(root, PROVIDER)
    core.require(core.digest(provider_bytes) == provider_sha256
        and audit.get('source_sha256', {}).get(PROVIDER) == provider_sha256,
        'Reviewed v4 provider digest differs or is not audit8-bound')
    baseline_bytes = core.read(root, BASELINE)
    core.require(core.digest(baseline_bytes) == BASELINE_SHA
        and audit.get('source_sha256', {}).get(BASELINE) == BASELINE_SHA,
        'Immutable Chapter7 baseline manifest differs or is not audit8-bound')
    baseline = core.object_json(baseline_bytes)
    inventory = core.object_json(core.read(root, INVENTORY))
    modules = inventory.get('modules')
    core.require(isinstance(modules, list) and modules, 'Missing current Chapter8 modules')
    immutable = blob_reader(root)
    # Provider adoption and audit8 source are also required to be bytes at S8.
    core.require(immutable(source_revision, PROVIDER) == provider_bytes, 'Provider differs from S8')
    auditor_bytes = core.read(root, AUDITOR)
    core.require(immutable(source_revision, AUDITOR) == auditor_bytes
                 and audit.get('source_sha256', {}).get(AUDITOR) == core.digest(auditor_bytes),
                 'Audit8 replayer is absent from its audited S8 source bindings')
    with ExitStack() as stack:
        provider = stack.enter_context(verified_module(root/PROVIDER, provider_bytes, '_chapter8_retained_provider'))
        auditor = None
        def loader(*args, **kwargs):
            nonlocal auditor
            # Deliberately lazy: core.context first calls provider.validate().
            core.require(auditor is None, 'Repeated audit8 replay invocation')
            auditor = stack.enter_context(verified_module(root/AUDITOR, auditor_bytes, '_chapter8_auditor'))
            replay = getattr(auditor, 'load_verified_audit', None)
            core.require(callable(replay), 'Audit8 lacks strict raw-replay API')
            return replay(*args, **kwargs)
        ctx = core.context(root, audit_path, source_revision, provider, baseline, modules, loader, immutable)
        yield ctx


class FixedProjectRedirects(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, msg, headers, newurl):
        allowed_url(newurl)
        return super().redirect_request(request, fp, code, msg, headers, newurl)


def allowed_url(url):
    u = urlsplit(url)
    core.require(u.scheme == 'https' and not u.username and not u.password and not u.port,
                 'Noncanonical publication URL')
    allowed = ((u.netloc == 'ylsong1024.github.io' and u.path.startswith('/BC4lean/'))
        or (u.netloc == 'raw.githubusercontent.com' and u.path.startswith('/ylsong1024/BC4lean/'))
        or (u.netloc == 'github.com' and u.path.startswith('/ylsong1024/BC4lean/')))
    core.require(allowed, 'URL is outside the fixed project')


class ActualHTTP:
    """Bounded sequential project-only fetches; constructing it performs no I/O."""
    def __init__(self):
        self.responses = []
        self.total = 0
        self.opener = urllib.request.build_opener(FixedProjectRedirects())
    def fetch(self, url, path, method='GET'):
        allowed_url(url)
        core.require(method in {'GET','HEAD'} and len(self.responses) < 2048, 'HTTP method/request limit')
        request = urllib.request.Request(url, method=method, headers={'User-Agent':'BC4lean-chapter8-verification'})
        with self.opener.open(request, timeout=30) as response:
            core.require(response.status == 200, 'Actual project HTTP status is not 200')
            allowed_url(response.url)
            data = response.read(32*1024*1024+1)
            core.require(len(data) <= 32*1024*1024, 'Oversized HTTP input')
            self.total += len(data)
            core.require(self.total <= 256*1024*1024, 'HTTP total size limit')
            record = {'requested_url':url,'response_url':response.url,'http_status':response.status,
                      'method':method,'bytes':len(data),'sha256':core.digest(data)}
        path = Path(path); path.parent.mkdir(parents=True,exist_ok=True)
        core.require(not path.exists(), 'Refusing to overwrite an HTTP response')
        path.write_bytes(data)
        self.responses.append(record)
        return data


def fetch_actual_live(root, publication_revision, ctx, output, http):
    """Future actual retrieval. Output must be new; no success record on failure."""
    root, output = Path(root).resolve(strict=True), Path(output)
    core.require(core.REV.fullmatch(publication_revision or ''), 'Full Q8 is required')
    core.require(git_bytes(root, 'rev-parse','HEAD').decode().strip() == publication_revision,
                 'Live verification checkout HEAD is not Q8')
    core.require(not git_bytes(root,'status','--porcelain=v1').strip(), 'Live verification checkout is dirty')
    core.require(not output.exists(), 'Live output directory must be fresh')
    output.mkdir(parents=True)
    site = output/'site'; site.mkdir()
    query = '?chapter8=' + publication_revision
    raw = http.fetch(BASE+'site-version.json'+query, output/'published-site-version.json')
    manifest = core.object_json(raw)
    core.require(manifest.get('revision') == publication_revision, 'Live deployment is not Q8 yet')
    core.require(manifest.get('chapter8_mathematical_source_revision') == ctx.source_revision
        and manifest.get('chapter7_mathematical_source_revision') == core.S7
        and manifest.get('chapter8_core_audit_sha256') == ctx.audit_sha256
        and manifest.get('chapter7_core_audit_sha256') == ctx.retained.audit_sha256,
        'Actual Q8/S8/S7/audit pins differ')
    pages = manifest.get('pages')
    required = {'index.html','docs/find/index.html','blueprint/ch-conjecture-and-examples.html',
                'blueprint/dep_graph_chapter_8.html','blueprint/ch-assembly-map.html',
                'blueprint/dep_graph_chapter_7.html','blueprint/dep_graph_document.html'}
    core.require(isinstance(pages,dict) and required <= pages.keys() and len(pages) <= 256,
                 'Missing/oversized actual page manifest')
    for relative, record in pages.items():
        core.safe_relative(relative)
        core.require(isinstance(record,dict) and set(record) == {'sha256','bytes'}
                     and core.SHA.fullmatch(record['sha256']) and type(record['bytes']) is int
                     and record['bytes'] >= 0, 'Invalid page hash/size record')
        data = http.fetch(BASE+quote(relative,safe='/')+query, site/relative)
        core.require(core.digest(data) == record['sha256'] and len(data) == record['bytes'],
                     'Actual served page differs from deployment manifest')
    hp = core.Page().finish((site/'index.html').read_text())
    for href in hp.links:
        u = urlsplit(href)
        if u.scheme or u.netloc or not u.path:
            continue
        relative = unquote(u.path)
        directory = relative.endswith('/')
        core.safe_relative(relative[:-1] if directory else relative)
        target = relative.rstrip('/') + '/index.html' if directory or not Path(relative).suffix else relative
        if not (site/target).is_file():
            http.fetch(BASE+quote(relative,safe='/')+query, site/target)
    verified = core.check_site(site, publication_revision, ctx)
    core.require(verified == manifest, 'Live manifest differs from independently checked served content')
    checks=[]
    with ctx.retained.helpers.open() as helpers:
        locator = helpers['update_chapter5_finder']
        for chapter, source, a, locations in [(8,ctx.source_revision,ctx.audit,ctx.locations),
                (7,core.S7,ctx.retained.audit,ctx.retained.locations)]:
            modules = a.get('source_modules',a['modules'])
            files = sorted({m.replace('.','/')+'.lean' for m in modules} | {p for p,_ in locations.values()})
            for relative in files:
                core.safe_relative(relative)
                data = http.fetch(RAW+source+'/'+quote(relative,safe='/'), output/'sources'/str(chapter)/relative)
                core.require(core.digest(data) == a['source_sha256'][relative], 'Immutable source bytes differ')
                commands = locator.declaration_lines(locator.code_only(data.decode()))
                names={n:line for n,(path,line) in locations.items() if path == relative}
                core.require(all(commands.get(n) == line for n,line in names.items()), 'Downloaded source command/line differs')
                if names:
                    url = BLOB+source+'/'+quote(relative,safe='/')+'#L'+str(min(names.values()))
                    http.fetch(url,output/'source-page-heads'/str(chapter)/(Path(relative).name+'.head'),method='HEAD')
                checks.append({'chapter':chapter,'source_revision':source,'path':relative,'sha256':core.digest(data),
                               'source_lines_independently_checked':names,'github_source_page_http_200':bool(names)})
    receipt={'schema':'chapter8.actual.live-publication.v1','status':'verified_actual_live_content',
        'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'publication_revision':publication_revision,'mathematical_source_revision':ctx.source_revision,
        'retained_chapter7_source_revision':core.S7,'chapter8_audit_sha256':ctx.audit_sha256,
        'retained_chapter7_audit_sha256':ctx.retained.audit_sha256,
        'published_manifest_sha256':core.digest(raw),'independently_revalidated_manifest_matches':True,
        'general_conjecture_proved':False,'chapter_complete':False,'chapter8':verified['chapter8'],
        'pages':pages,'actual_source_files':checks,'network_responses':http.responses}
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def run(mode):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,required=True)
    p.add_argument('--source-revision',required=True,help='Full immutable audited S8; no inference')
    p.add_argument('--provider-sha256',required=True,help='Reviewed adapted v4 provider digest; no alias/fallback')
    if mode=='finder':
        p.add_argument('--check',action='store_true')
    else:
        p.add_argument('--revision',required=True,help='Full Q8 publication commit')
    if mode=='site':
        p.add_argument('site',type=Path)
    if mode=='live':
        p.add_argument('--output',type=Path,required=True,help='Fresh directory outside repository')
    a=p.parse_args()
    with load_context(a.root,a.source_revision,a.provider_sha256) as ctx:
        if mode=='finder':
            current=core.read(ctx.root,core.FINDER).decode()
            expected=core.render_finder(current,ctx)
            if a.check:
                core.verify_finder(current,ctx)
                core.require(current==expected,'Chapter8 finder is stale')
            else:
                (ctx.root/core.FINDER).write_text(expected)
            print('Checked' if a.check else 'Updated',len(ctx.locations),'actual audited Chapter8 source links at',ctx.source_revision)
        elif mode=='site':
            manifest=core.check_site(a.site,a.revision,ctx)
            (a.site/'site-version.json').write_text(json.dumps(manifest,indent=2)+'\n')
            print('Checked actual assembled Chapter8 milestone publication for',a.revision)
        elif mode=='live':
            core.require(not a.output.resolve().is_relative_to(ctx.root),'Live evidence must stay outside the repository')
            result=fetch_actual_live(ctx.root,a.revision,ctx,a.output,ActualHTTP())
            print(json.dumps({'status':result['status'],'publication_revision':a.revision,
                              'source_revision':ctx.source_revision,'receipt':str(a.output/'receipt.json')}))
        else:
            raise ValueError('Unknown publication command')
