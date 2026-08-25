import numpy as np

names = ['B','E','G','R','S1','S2','D','C','Q1','Q2','F','H1','H2']
coords_raw = {
 'B': (0.0, 0.0),
 'E': (1.0, 0.0),
 'G': (1.823186950926246, 0.5677704147142139),
 'R': (1.5451976715140148, 1.5283545914170518),
 'S1': (0.8079995672096562, 2.2040312559616106),
 'S2': (-0.07392359713025984, 1.7326380737870366),
 'D': (-0.534630666826967, 0.845085824096082),
 'C': (-0.2368227699437535, 0.3743435947856081),
 'Q1': (-0.20976669066959178, 1.4709363305184016),
 'Q2': (1.3210722790920153, 1.7337760333703467),
 'F': (1.250166787118965, 0.17254561714132796),
 'H1': (0.45144652866934915, 1.0997988812000283),
 'H2': (0.662256483448314, 0.9814717416038052),
}
idx = {n:i for i,n in enumerate(names)}
x0 = np.array([coords_raw[n] for n in names]).reshape(-1)  # 26 numbers

def P(x, n):
    i = idx[n]
    return x[2*i:2*i+2]

def shoelace(pts):
    a = 0.0
    n = len(pts)
    for i in range(n):
        x1,y1 = pts[i]; x2,y2=pts[(i+1)%n]
        a += x1*y2-x2*y1
    return a/2.0  # signed

def area_grad(x, poly_names):
    # gradient of signed shoelace area wrt each vertex in poly_names, others zero
    g = np.zeros_like(x)
    m = len(poly_names)
    for k,n in enumerate(poly_names):
        prev = P(x, poly_names[(k-1)%m])
        nxt = P(x, poly_names[(k+1)%m])
        # d(signed area)/d(vertex) = 0.5*perp(next-prev), perp(v)=(v_y,-v_x) for shoelace sum x_i y_{i+1}-x_{i+1}y_i
        dx = nxt[0]-prev[0]; dy = nxt[1]-prev[1]
        i = idx[n]
        g[2*i]   += 0.5*dy
        g[2*i+1] += -0.5*dx
    return g

fences = [('B','E'),('E','G'),('G','R'),('R','S1'),('S1','S2'),('S2','D'),('D','B'),
          ('C','H1'),('Q1','H2'),('Q2','H2'),('F','H2')]

tjs = [('C','D','B'), ('Q1','S2','D'), ('Q2','R','S1'), ('F','E','G'), ('H1','Q1','H2')]  # (foot, hosta, hostb)

faces = {
 'quad': ['C','H1','Q1','D'],
 'pent1': ['Q1','S2','S1','Q2','H2'],
 'pent2': ['Q2','R','G','F','H2'],
 'hexf': ['F','E','B','C','H1','H2'],
}
outer = ['B','E','G','R','S1','S2','D']

def length_grad(x, u, v):
    g = np.zeros_like(x)
    pu, pv = P(x,u), P(x,v)
    d = pu-pv
    iu, iv = idx[u], idx[v]
    g[2*iu:2*iu+2] += 2*d
    g[2*iv:2*iv+2] += -2*d
    return g, np.dot(d,d)-1.0

def cross_grad(x, p, a, b):
    # C = (b-a) x (p-a)
    pp,pa,pb = P(x,p), P(x,a), P(x,b)
    g = np.zeros_like(x)
    ip,ia,ib = idx[p],idx[a],idx[b]
    # C = (bx-ax)(py-ay) - (by-ay)(px-ax)
    bx,by = pb; ax,ay=pa; px,py=pp
    Cval = (bx-ax)*(py-ay) - (by-ay)*(px-ax)
    # dC/dp = (-(by-ay), (bx-ax))
    g[2*ip]   += -(by-ay)
    g[2*ip+1] += (bx-ax)
    # dC/da = derivative
    # C = (bx-ax)(py-ay)-(by-ay)(px-ax)
    # dC/dax = -(py-ay) + (by-ay)
    # dC/day = -(bx-ax)*(-1) ... let's just do numerically via sympy-like manual
    dCdax = -(py-ay) + (by-ay)
    dCday = (bx-ax) - (- (px-ax))  # recompute carefully below
    return g, Cval, (ip,ia,ib)

x = x0.copy()

# numeric gradient check instead of hand algebra for cross to avoid sign bugs
def cross_val(x, p,a,b):
    pp,pa,pb = P(x,p), P(x,a), P(x,b)
    return (pb[0]-pa[0])*(pp[1]-pa[1]) - (pb[1]-pa[1])*(pp[0]-pa[0])

def numgrad(f, x, eps=1e-7):
    g = np.zeros_like(x)
    for i in range(len(x)):
        xp = x.copy(); xp[i]+=eps
        xm = x.copy(); xm[i]-=eps
        g[i] = (f(xp)-f(xm))/(2*eps)
    return g

# Build full Jacobian rows: 11 length + 5 cross = 16 equality rows
rows = []
labels = []
for (u,v) in fences:
    g = numgrad(lambda xx,u=u,v=v: np.dot(P(xx,u)-P(xx,v),P(xx,u)-P(xx,v))-1.0, x)
    rows.append(g); labels.append(f'len_{u}{v}')
for (p,a,b) in tjs:
    g = numgrad(lambda xx,p=p,a=a,b=b: cross_val(xx,p,a,b), x)
    rows.append(g); labels.append(f'cross_{p}on{a}{b}')

# face areas at x
areas = {k: abs(shoelace([P(x,n) for n in v])) for k,v in faces.items()}
print("face areas:", areas)
total = sum(areas.values())
print("total area:", total)
heptA = abs(shoelace([P(x,n) for n in outer]))
print("heptagon area:", heptA)

active = [k for k,v in areas.items() if v > 1-1e-6]
print("active faces (area==1):", active)

for k in active:
    g = numgrad(lambda xx,k=k: abs(shoelace([P(xx,n) for n in faces[k]])), x)
    rows.append(g); labels.append(f'area_{k}')

J = np.array(rows)  # (16+A) x 26
gradA = numgrad(lambda xx: abs(shoelace([P(xx,n) for n in outer])), x)

# solve J^T v = gradA in least squares sense
v, res, rank, sv = np.linalg.lstsq(J.T, gradA, rcond=None)
resid = J.T @ v - gradA
print("rank(J.T):", rank, "shape J:", J.shape)
print("residual norm:", np.linalg.norm(resid))
print("multipliers:")
for lab, val in zip(labels, v):
    print(f"  {lab}: {val:.6f}")
