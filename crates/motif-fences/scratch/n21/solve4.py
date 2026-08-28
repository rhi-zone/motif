import numpy as np, json
from scipy.optimize import minimize, NonlinearConstraint

# NOTE: original session used a pickle (model.pkl); this scratch copy uses the
# committed model.json instead (see README.md in this directory).
with open('model.json') as f:
    m = json.load(f)
boundary_names = m['boundary_names']; quad_names=m['quad_names']; tj_info=m['tj_info']
idx=m['idx']; tidx=m['tidx']
# original x0 came from solution2.npy (not salvaged verbatim); use
# solution_validceil.json's "x" field instead (area 7.682823659, same solve).
x0 = np.array(json.load(open('solution_validceil.json'))['x'])

def get_pt(x, name):
    if name in idx:
        return x[2*idx[name]:2*idx[name]+2]
    else:
        a,b,_ = tj_info[name]
        t = x[tidx[name]]
        return (1-t)*get_pt(x,a) + t*get_pt(x,b)

boundary_edges = [(boundary_names[i], boundary_names[(i+1)%10]) for i in range(10)]
quad_edges = [(quad_names[i], quad_names[(i+1)%4]) for i in range(4)]
tj_names = list(tj_info.keys())

def edge_len_constraint(x):
    out = []
    for a,b in boundary_edges + quad_edges:
        d = get_pt(x,a)-get_pt(x,b); out.append(np.dot(d,d)-1.0)
    for name in tj_names:
        a,b,chord = tj_info[name]
        d = get_pt(x,name)-get_pt(x,chord); out.append(np.dot(d,d)-1.0)
    return np.array(out)

def shoelace_signed(pts):
    s=0.0; n=len(pts)
    for i in range(n):
        x1,y1=pts[i]; x2,y2=pts[(i+1)%n]
        s += x1*y2-x2*y1
    return 0.5*s

def neg_area(x):
    return -abs(shoelace_signed([get_pt(x,name) for name in boundary_names]))

bcycle = ['J4','C5','J3','C9','J5','C1','J12','C7','C8','J6','C4','J1','C3','J13','C10']
qcycle = ['C6','J2','J10','J8','J7','C11','J0','J9','C12','J11']
seq = ['J4','J3','J5','J12','J6','J1','J13']
chord_target = {'J4':'J2','J3':'J10','J5':'J8','J12':'J7','J6':'J0','J1':'J9','J13':'J11'}
def path_between(cycle, a, b):
    ia = cycle.index(a); ib = cycle.index(b); n=len(cycle)
    path=[]; i=ia
    while True:
        path.append(cycle[i])
        if i==ib: break
        i=(i+1)%n
    return path
wedge_polys = []
for i in range(len(seq)):
    a = seq[i]; b = seq[(i+1)%len(seq)]
    bpath = path_between(bcycle, a, b)
    qa = chord_target[a]; qb = chord_target[b]
    qpath = list(reversed(path_between(qcycle, qa, qb)))
    wedge_polys.append(bpath+qpath)
all_faces = wedge_polys + [qcycle]

def face_areas(x):
    return np.array([abs(shoelace_signed([get_pt(x,n) for n in poly])) for poly in all_faces])

nlc1 = NonlinearConstraint(edge_len_constraint, 0, 0)
nlc2 = NonlinearConstraint(face_areas, -np.inf, 1.0)

print("start area:", -neg_area(x0), "face areas:", face_areas(x0))
res = minimize(neg_area, x0, method='trust-constr', constraints=[nlc1,nlc2],
               options={'maxiter':20000,'gtol':1e-15,'xtol':1e-16,'barrier_tol':1e-12})
print("done:", res.status, res.message)
print("area:", -res.fun)
print("edge resid:", np.max(np.abs(edge_len_constraint(res.x))))
print("face areas:", face_areas(res.x))
np.save('solution4.npy', res.x)

print("\n=== bigger multi-start ===")
rng = np.random.default_rng(7)
best = (-neg_area(res.x), res.x)
for trial in range(5):
    scale = 0.03 + 0.02*trial
    xp = x0 + rng.normal(scale=scale, size=x0.shape)
    try:
        r = minimize(neg_area, xp, method='trust-constr', constraints=[nlc1,nlc2],
                     options={'maxiter':2500,'gtol':1e-11,'xtol':1e-12})
        ok = np.max(np.abs(edge_len_constraint(r.x)))<1e-6 and np.max(face_areas(r.x))<1+1e-6
        ar = -neg_area(r.x) if ok else None
        print(f"trial scale={scale:.3f}: area={ar} feasible={ok}")
        if ok and ar and ar>best[0]:
            best = (ar, r.x)
    except Exception as e:
        print("fail", e)
print("\nOVERALL BEST:", best[0])
np.save('solution_final.npy', best[1])
