import numpy as np, pickle
from scipy.optimize import minimize, NonlinearConstraint
# reuse solve4 setup (defs up to the first minimize call)
src = open('solve4.py').read().split("nlc1 =")[0]
exec(src)
# now have: model, get_pt, edge_len_constraint, face_areas, neg_area, tj_names, tidx, idx

import json
x0 = np.array(json.load(open('solution_validceil.json'))['x'])  # warm start; see README.md
nfaces = len(all_faces)
ntj = len(tj_names)
print("dims: x=%d  faces=%d  tjs=%d  boundary_names=%d"%(x0.shape[0],nfaces,ntj,len(boundary_names)),flush=True)

def tparams(x): return np.array([x[tidx[n]] for n in tj_names])
def feasible(x, cap):
    return (np.max(np.abs(edge_len_constraint(x)))<1e-6
            and np.max(face_areas(x))<cap+1e-6
            and tparams(x).min()>1e-4 and tparams(x).max()<1-1e-4)

nlc_len = NonlinearConstraint(edge_len_constraint, 0, 0)

def run(cap, ntrials, seed, label):
    nlc_cap = NonlinearConstraint(face_areas, -np.inf, cap)
    cons=[nlc_len, nlc_cap]
    rng=np.random.default_rng(seed)
    # start from x0 solved at this cap
    r0=minimize(neg_area,x0,method='trust-constr',constraints=cons,
                options={'maxiter':3000,'gtol':1e-12,'xtol':1e-13})
    best=(-neg_area(r0.x) if feasible(r0.x,cap) else -1, r0.x)
    nf=int(feasible(r0.x,cap))
    for t in range(ntrials):
        scale=[0.02,0.04,0.07,0.12,0.2][t%5]
        xp=x0+rng.normal(scale=scale,size=x0.shape)
        try:
            r=minimize(neg_area,xp,method='trust-constr',constraints=cons,
                       options={'maxiter':2000,'gtol':1e-11,'xtol':1e-12})
        except Exception: continue
        if feasible(r.x,cap):
            nf+=1; ar=-neg_area(r.x)
            if ar>best[0]: best=(ar,r.x)
        print(f"[{label}] trial {t} scale={scale:.2f} best={best[0]:.7f}",flush=True)
    return best,nf

print("\n=== CAPPED (fields<=1) valid ceiling ===",flush=True)
(bc_area,bc_x),nfc = run(1.0, 40, 11, "cap")
np.save('solution_validceil.npy', bc_x)
print("CAPPED valid ceiling = %.9f  feasible=%d/41"%(bc_area,nfc),flush=True)
print("face areas:",np.round(face_areas(bc_x),6),flush=True)
print("t params in (0,1):", np.round(tparams(bc_x),4),flush=True)

print("\n=== UNCAPPED (fields unbounded) ===",flush=True)
(bu_area,bu_x),nfu = run(50.0, 30, 23, "unc")  # cap huge = effectively off
np.save('solution_uncapped.npy', bu_x)
print("UNCAPPED max = %.9f"%bu_area,flush=True)
fa=face_areas(bu_x)
print("face areas:",np.round(fa,4),"  max face=%.4f"%fa.max(),flush=True)

print("\n=== VERDICT ===",flush=True)
rec=7.69139
print("record            = %.5f"%rec,flush=True)
print("capped valid ceil = %.6f   (%s record, diff %.6f)"%(bc_area,">=" if bc_area>=rec else "BELOW",bc_area-rec),flush=True)
print("uncapped max      = %.6f   (%s record)"%(bu_area,">=" if bu_area>=rec else "below",),flush=True)
print("uncapped max face = %.4f  (how oversized a field it needs)"%face_areas(bu_x).max(),flush=True)
