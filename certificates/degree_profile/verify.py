"""Independent semantic verification of frozen internal-pair support-flow dual.

Uses only the published rational dual coordinates. Does not import the LP
builder, numerical optimizer, or producer's certificate checker. Constructs
each column from graph-count meanings and independently named row families.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE/'certificate.json'
METADATA = json.loads(SOURCE.read_text())
GRID = tuple(map(Q,METADATA['model']['grid']))
N = len(GRID)-1
assert N == 152 and GRID[0] == 0 and GRID[-1] == 1
assert all(a < b for a,b in zip(GRID,GRID[1:]))
assert GRID[1] == Q(1,256)
A, W, P, D = Q(11,20), Q(550001,1000000), Q(9,20), Q(1,100)
LAMBDA = Q(1,100000000)


def model():
    centers = [(i,t) for i in range(N) for t in ('G','M','P','I','J')]
    outside = []
    for i in range(N):
        for t in ('S','T','A','O'):
            arms = 1 if t == 'O' and GRID[i+1] <= Q(1,2) else 2 if t == 'A' else 4
            outside += [(i,t,h) for h in range(arms)]
    eq = [('normalization',),('internal_count',)]
    eq += [('internal_center',c) for c,(_,t) in enumerate(centers) if t in ('I','J')]
    eq += [('root',x) if t == 'S' else ('missing_out',x)
           for x,(_,t,_) in enumerate(outside) if t in ('S','T')]
    eq += [('missing_center',c) for c,(_,t) in enumerate(centers) if t == 'M']
    eq += [('available_balance',)]
    ub = []
    ub += [(side,'c',c) for c in range(len(centers)) for side in ('lower','upper')]
    ub += [(side,'o',x) for x in range(len(outside)) for side in ('lower','upper')]
    ub += [('base_value',),('base_one',),('value_one',),('root_degree',),('missing_degree',),('total_mass',),('phase',)]
    return centers,outside,eq,ub


def column_data(centers,outside):
    for c,(i,t) in enumerate(centers):
        eq = {('normalization',):int(t in ('G','M'))}
        if t == 'M': eq['missing_center',c] = -1
        if t == 'G': eq['available_balance',] = 1
        if t in ('I','J'): eq['internal_center',c] = -1
        phase = (1+A)/2 if t == 'G' else (1-W)/2 if t == 'M' else Q(0)
        ub = {('lower','c',c):GRID[i],
              ('upper','c',c):-GRID[i+1],('base_value',):1,('base_one',):1,
              ('total_mass',):1,('phase',):phase}
        yield ('c',c),eq,ub,Q(0)
    for x,(i,t,h) in enumerate(outside):
        eq = {}
        if t == 'S': eq['root',x] = -1
        if t == 'T': eq['missing_out',x] = -1
        if t == 'A': eq['available_balance',] = -1
        caps = (P,) if t == 'A' else ((W,1) if t in ('S','T') else (1,1))
        credit = sum((cap for j,cap in enumerate(caps) if h & (1<<j)),Q(0))/2
        ub = {('lower','o',x):GRID[i],('upper','o',x):-GRID[i+1],
              ('total_mass',):int(not(i == 0 and t == 'O')),('phase',):credit}
        yield ('o',x),eq,ub,Q(0)
    for c,(j,t) in enumerate(centers):
        for x,(i,u,h) in enumerate(outside):
            if GRID[i]+GRID[j] > 1: continue
            denom = max(D,1-GRID[i])
            coeffs = ((W if t in ('M','J') else 1 if t == 'P' else 0),) if u == 'A' else (
                P if t == 'G' else 1,W if t in ('M','J') else 1 if t == 'P' else 0)
            credit = sum((v/denom for k,v in enumerate(coeffs) if not h & (1<<k)),Q(0))/2
            ub = {('lower','c',c):-1,('upper','c',c):1,
                  ('lower','o',x):-1,('upper','o',x):1,('total_mass',):1,('phase',):credit}
            ub['root_degree',] = -int(u == 'S')
            ub['missing_degree',] = -int(u == 'T')-int(t == 'M')
            yield ('e',c,x),{},ub,Q(0)
    for c,(i,_) in enumerate(centers):
        for d in range(c,len(centers)):
            if GRID[i]+GRID[centers[d][0]] > 1: continue
            ub = {('total_mass',):1}
            for v in (c,d):
                for side,sign in (('lower',-1),('upper',1)):
                    key=(side,'c',v)
                    ub[key]=ub.get(key,0)+sign
            ub['missing_degree',] = -int(centers[c][1] == 'M')-int(centers[d][1] == 'M')
            yield ('h',c,d),{},ub,Q(0)
    roots = [x for x,(_,t,_) in enumerate(outside) if t == 'S']
    for ii,x in enumerate(roots):
        for y in roots[ii:]:
            if GRID[outside[x][0]+1]+GRID[outside[y][0]+1] < 1-LAMBDA: continue
            eq={('normalization',):1}
            for v in (x,y): eq['root',v]=eq.get(('root',v),0)+1
            yield ('r',x,y),eq,{('total_mass',):1,('phase',):(1-W)/2,('root_degree',):1-LAMBDA},Q(0)
    missing = [x for x,(_,t,_) in enumerate(outside) if t == 'T']
    for c,(j,t) in enumerate(centers):
        if t != 'M': continue
        for x in missing:
            if GRID[j+1]+GRID[outside[x][0]+1] < 1-LAMBDA: continue
            yield ('m',c,x),{('missing_center',c):1,('missing_out',x):1},{('total_mass',):1,('missing_degree',):1-LAMBDA},Q(0)
    for c,(i,t) in enumerate(centers):
        if t not in ('I','J'): continue
        for d in range(c,len(centers)):
            j,u = centers[d]
            if u != t: continue
            if t == 'I' and GRID[i]+GRID[j] > 1: continue
            if t == 'J' and GRID[i+1]+GRID[j+1] < 1-LAMBDA: continue
            eq = {('internal_count',):1}
            for v in (c,d): eq['internal_center',v] = eq.get(('internal_center',v),0)+1
            yield ('i',c,d),eq,{('total_mass',):1,('phase',):Q(1,2) if t == 'I' else (1-W)/2},Q(0)
    yield ('z',),{('normalization',):1,('internal_count',):-1},{('total_mass',):1},Q(0)
    yield ('value',),{},{('base_value',):-1,('value_one',):1,('total_mass',):1,('phase',):-1},Q(1)


def main():
    start=time.time()
    data=json.loads(SOURCE.read_text())
    centers,outside,eqrows,ubrows=model()
    assert len(eqrows)==1675 and len(ubrows)==5327
    eqdict=dict(zip(eqrows,map(Q,data['dual_equalities']),strict=True))
    ubdict=dict(zip(ubrows,map(Q,data['dual_inequalities']),strict=True))
    assert all(y <= 0 for y in ubdict.values())
    assert {k:v for k,v in data['model'].items() if k != 'grid'} == {
        'q':152,'alpha':.55,'omega':.550001,'mode':'closed','initial':0,
        'interval':True,'cutoff':.99,'capped':True}
    counts=Counter()
    minimum=None
    unbounded=[]
    tight=[]
    for key,e,u,cost in column_data(centers,outside):
        # No floating arithmetic enters any mathematical coefficient.
        assert all(isinstance(v,(Q,int)) for v in list(e.values())+list(u.values()))
        value=sum(Q(v)*eqdict[k] for k,v in e.items())+sum(Q(v)*ubdict[k] for k,v in u.items())
        slack=cost-value
        assert slack >= 0,(key,str(slack))
        minimum=slack if minimum is None else min(minimum,slack)
        if not u.get(('total_mass',),0): unbounded.append({'key':key,'slack':str(slack)})
        if slack == 0: tight.append(key)
        counts[key[0]]+=1
    bound=eqdict['normalization',]+ubdict['base_one',]+ubdict['value_one',]+267*ubdict['total_mass',]
    assert bound==Q(2896371675910694789,4062500000000000000)
    assert bound > Q(71295,100000)
    assert sum(counts.values())==996325
    result={'status':'PASS independent exact semantic dual reconstruction',
            'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'variables':sum(counts.values()),'column_families':dict(counts),
            'equalities':len(eqrows),'inequalities':len(ubrows),
            'mass_bound':267,'lambda':str(LAMBDA),'minimum_exact_column_slack':str(minimum),'unbounded_columns':unbounded,
            'exact_lower_bound':str(bound),'exact_margin_over_71295':str(bound-Q(71295,100000)),
            'tight_columns':tight,'seconds':time.time()-start,
            'scope':'Finite deterministic profile dual; graph map and finite probability audited separately.'}
    (HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
