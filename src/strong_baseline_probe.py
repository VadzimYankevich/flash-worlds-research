import sys, os, time, gc, json, hashlib, platform
from itertools import permutations
from statistics import median
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path('candidate_work').resolve()))
from flash_candidates import FlashRunner, make_backend
from candidate_sieves import _answer, _check_window

BASES=(2,3,5,7,11,13,17,19,23,29,31,37)
def mr12(n):
    if not 0<=n<2**64: raise ValueError('uint64 domain required')
    if n<2: return False
    for p in BASES:
        if n==p: return True
        if n%p==0: return False
    d=n-1; s=0
    while d%2==0: d//=2; s+=1
    for a in BASES:
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

class MRBackend:
    def __init__(self):
        self.facts={}
        self.candidates=0
    def search(self,B,L,R):
        _check_window(B,L,R)
        answer=None
        for n in range(R,L-1,-2):
            self.candidates+=1
            if n not in self.facts: self.facts[n]=mr12(n)
            if self.facts[n]: answer=n; break
        return _answer(answer,B,L,R,'deterministic MR12 within uint64 domain')

def signature(r):
    w=[(v['B'],v['L'],v['R'],v['address'],v['closed_suffix']['L'],v['closed_suffix']['R'],v['closed_suffix']['world_B'],v['closed_suffix']['exact_hole_mass']) for v in r['windows']]
    s=[(v['B'],v['R'],v['last_hole'],v['search_lower_bound'],v['closed_suffix']['L'],v['closed_suffix']['R']) for v in r['steps']]
    return r['anchors'],w,s

modes=('candidate_prime','segmented','mr12_candidates')
allowed=sorted(os.sched_getaffinity(0))
pin=8 if 8 in allowed else allowed[0]
os.sched_setaffinity(0,{pin})
rows=[]; reference=None; verified=0
for round_no,order in enumerate(list(permutations(modes))*2,1):
    for position,mode in enumerate(order,1):
        gc.collect()
        t=time.perf_counter_ns()
        backend=MRBackend() if mode=='mr12_candidates' else make_backend(mode,False)
        route=FlashRunner(backend).run(28)
        elapsed=(time.perf_counter_ns()-t)/1e9
        sig=signature(route)
        if reference is None: reference=sig
        assert sig==reference,(round_no,mode)
        verified+=len(route['windows'])
        rows.append({'round':round_no,'position':position,'mode':mode,'seconds':elapsed})
        del backend,route,sig
by_mode={m:median(r['seconds'] for r in rows if r['mode']==m) for m in modes}
pairs=[]
for round_no in range(1,13):
    values={r['mode']:r['seconds'] for r in rows if r['round']==round_no}
    pairs.append({'round':round_no,'prime_over_mr':values['candidate_prime']/values['mr12_candidates'],'segmented_over_mr':values['segmented']/values['mr12_candidates']})
result={'status':'PASS','classification':'short diagnostic, not full benchmark campaign',
 'flashes':28,'rounds':12,'observations':len(rows),'cold_backend_each_observation':True,
 'one_process_shared_imports':True,'all_six_orders_twice':True,'pinned_cpu':pin,
 'python':sys.version,'platform':platform.platform(),'automatic_gc_enabled':gc.isenabled(),
 'timing':'wall perf_counter_ns; includes backend construction and full shared controller route; excludes imports, pre-run gc, result comparison and object destruction',
 'MR':'12 bases 2..37, deterministic only within declared n<2^64; independent competitor implementation; no working import from validation module',
 'contract':'same maximum and closed suffix, identical short windows and anchor sequence, optional factor witnesses not required from competitors',
 'verification':'all route/window/suffix signatures compared after each timer; no reference answers enter the working backends',
 'window_answers_compared':verified,'distinct_windows':len(reference[1]),'final_anchor':reference[0][-1],
 'median_seconds':by_mode,'median_paired_speedup_vs_mr':{'candidate_prime':median(p['prime_over_mr'] for p in pairs),'segmented':median(p['segmented_over_mr'] for p in pairs)},
 'mr_wins_vs_prime':sum(p['prime_over_mr']>1 for p in pairs),'mr_wins_vs_segmented':sum(p['segmented_over_mr']>1 for p in pairs),
 'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path('candidate_work/flash_candidates.py'),Path('candidate_work/candidate_sieves.py'))},
 'observations_raw':rows,'pairs':pairs}
print(json.dumps(result,ensure_ascii=False,indent=2))