import numpy as np
from scipy.optimize import minimize

# Points: TL,TM,TR,U,Tip,D,BR,BM,BL,LM,RM,C
# Gauge: C=(0,0) fixed, RM.y = 0 fixed (rotation gauge: C-RM direction along +x axis)
# unknowns vector layout (22 numbers):
# TL(2) TM(2) TR(2) U(2) Tip(2) D(2) BR(2) BM(2) BL(2) LM(2) RM.x(1)
names = ['TL','TM','TR','U','Tip','D','BR','BM','BL','LM']
idx = {}
k=0
for nm in names:
    idx[nm]=(k,k+1); k+=2
idx['RM']=(k,None); k+=1  # only RM.x
NVAR = k

unit_px = 67.78384615384616
pts_px = dict(
 TL=(2.98,1.84), TM=(70.25,2.16), TR=(138.44,6.11), U=(147.00,36.31),
 Tip=(157.86,71.28), D=(147.00,103.42), BR=(136.41,135.69), BM=(69.16,137.29),
 BL=(1.04,135.70), LM=(11.47,70.03), RM=(147.00,71.04), C=(79.15,69.92),
)
Cpx = np.array(pts_px['C'])
def to_unit(p):
    return (np.array(p)-Cpx)/unit_px

x0 = np.zeros(NVAR)
for nm in names:
    u = to_unit(pts_px[nm])
    x0[idx[nm][0]] = u[0]; x0[idx[nm][1]] = u[1]
x0[idx['RM'][0]] = to_unit(pts_px['RM'])[0]

def unpack(x):
    P = {}
    for nm in names:
        i,j = idx[nm]
        P[nm] = np.array([x[i], x[j]])
    P['RM'] = np.array([x[idx['RM'][0]], 0.0])
    P['C'] = np.array([0.0, 0.0])
    return P

def dist(a,b): return np.linalg.norm(a-b)
def cross(o,a,b):
    oa=a-o; ob=b-o
    return oa[0]*ob[1]-oa[1]*ob[0]

edges = [('TL','TM'),('TM','TR'),('TR','Tip'),('Tip','BR'),('BR','BM'),
         ('BM','BL'),('BL','LM'),('LM','TL'),('LM','C'),('C','RM'),
         ('TM','C'),('C','BM'),('U','D')]

def eq_constraints(x):
    P = unpack(x)
    eqs = []
    for a,b in edges:
        eqs.append(dist(P[a],P[b]) - 1.0)
    # collinearity: U on line TR-Tip; D on line Tip-BR; RM on line U-D
    eqs.append(cross(P['TR'],P['Tip'],P['U']))
    eqs.append(cross(P['Tip'],P['BR'],P['D']))
    eqs.append(cross(P['U'],P['D'],P['RM']))
    return np.array(eqs)

def shoelace(poly):
    n=len(poly); a=0.0
    for i in range(n):
        x1,y1=poly[i]; x2,y2=poly[(i+1)%n]
        a += x1*y2-x2*y1
    return a/2.0  # signed

def faces(P):
    F1 = shoelace([P['TL'],P['TM'],P['C'],P['LM']])
    F2 = shoelace([P['LM'],P['C'],P['BM'],P['BL']])
    F3 = shoelace([P['TM'],P['TR'],P['U'],P['RM'],P['C']])
    F4 = shoelace([P['C'],P['RM'],P['D'],P['BR'],P['BM']])
    F5 = shoelace([P['U'],P['Tip'],P['D'],P['RM']])
    return F1,F2,F3,F4,F5

def neg_total_area(x):
    P = unpack(x)
    fs = faces(P)
    return -sum(abs(f) for f in fs)

def ineq_constraints(x):
    P = unpack(x)
    fs = faces(P)
    # 1 - |f| >= 0 for each face
    return np.array([1.0 - abs(f) for f in fs])

cons = [
  {'type':'eq', 'fun': eq_constraints},
  {'type':'ineq', 'fun': ineq_constraints},
]

res = minimize(neg_total_area, x0, constraints=cons, method='SLSQP',
               options={'maxiter':1000,'ftol':1e-12})
print(res.message, res.success, "area=", -res.fun)
P = unpack(res.x)
for nm,v in P.items():
    print(f"  {nm}: ({v[0]:.6f}, {v[1]:.6f})")
fs = faces(P)
print("faces:", [abs(f) for f in fs])
print("eq residuals max abs:", np.max(np.abs(eq_constraints(res.x))))
print("ineq min:", np.min(ineq_constraints(res.x)))

# check betweenness for T-junctions
def tparam(p,q,r):
    pq=q-p; pr=r-p
    return np.dot(pr,pq)/np.dot(pq,pq)
print("t(U on TR-Tip)=", tparam(P['TR'],P['Tip'],P['U']))
print("t(D on Tip-BR)=", tparam(P['Tip'],P['BR'],P['D']))
print("t(RM on U-D)=", tparam(P['U'],P['D'],P['RM']))

np.save('/tmp/fences-verify-n13-v3/solution_x.npy', res.x)
