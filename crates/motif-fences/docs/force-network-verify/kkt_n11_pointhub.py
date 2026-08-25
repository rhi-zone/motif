import numpy as np

names = ['B','E','G','R','S1','S2','D','C','Q1','Q2','F','H']
coords_raw = {
 'B': (0.0,0.0), 'E': (1.0,0.0),
 'G': (1.87415651, 0.4856443), 'R': (1.69715395, 1.4698547),
 'S1': (1.03589883, 2.22001579), 'S2': (0.08273368, 1.91756547),
 'D': (-0.23948476, 0.97090012), 'C': (-0.15722473, 0.63740803),
 'Q1': (-0.01215386, 1.63878954), 'Q2': (1.46986927, 1.72769787),
 'F': (1.29395683, 0.16330995), 'H': (0.76898082, 1.01442698),
}
idx = {n:i for i,n in enumerate(names)}
x0 = np.array([coords_raw[n] for n in names]).reshape(-1)

def P(x,n):
    i=idx[n]; return x[2*i:2*i+2]

def shoelace(pts):
    a=0.0; n=len(pts)
    for i in range(n):
        x1,y1=pts[i]; x2,y2=pts[(i+1)%n]
        a += x1*y2-x2*y1
    return a/2.0

fences = [('B','E'),('E','G'),('G','R'),('R','S1'),('S1','S2'),('S2','D'),('D','B'),
          ('C','H'),('Q1','H'),('Q2','H'),('F','H')]
tjs = [('C','D','B'), ('Q1','S2','D'), ('Q2','R','S1'), ('F','E','G')]
faces = {
 'f1': ['C','H','Q1','D'],
 'f2': ['Q1','S2','S1','Q2','H'],
 'f3': ['Q2','R','G','F','H'],
 'f4': ['F','E','B','C','H'],
}
outer = ['B','E','G','R','S1','S2','D']

def cross_val(x,p,a,b):
    pp,pa,pb=P(x,p),P(x,a),P(x,b)
    return (pb[0]-pa[0])*(pp[1]-pa[1]) - (pb[1]-pa[1])*(pp[0]-pa[0])

def numgrad(f,x,eps=1e-7):
    g=np.zeros_like(x)
    for i in range(len(x)):
        xp=x.copy(); xp[i]+=eps
        xm=x.copy(); xm[i]-=eps
        g[i]=(f(xp)-f(xm))/(2*eps)
    return g

x=x0.copy()
rows=[]; labels=[]
for (u,v) in fences:
    g=numgrad(lambda xx,u=u,v=v: np.dot(P(xx,u)-P(xx,v),P(xx,u)-P(xx,v))-1.0, x)
    rows.append(g); labels.append(f'len_{u}{v}')
for (p,a,b) in tjs:
    g=numgrad(lambda xx,p=p,a=a,b=b: cross_val(xx,p,a,b), x)
    rows.append(g); labels.append(f'cross_{p}on{a}{b}')

areas = {k: abs(shoelace([P(x,n) for n in v])) for k,v in faces.items()}
print("face areas:", areas)
active = [k for k,v in areas.items() if v>1-1e-6]
print("active:", active)
for k in active:
    g=numgrad(lambda xx,k=k: abs(shoelace([P(xx,n) for n in faces[k]])), x)
    rows.append(g); labels.append(f'area_{k}')

J=np.array(rows)
gradA = numgrad(lambda xx: abs(shoelace([P(xx,n) for n in outer])), x)
v,res,rank,sv = np.linalg.lstsq(J.T, gradA, rcond=None)
resid = J.T@v - gradA
print("rank J.T:", rank, "shape:", J.shape)
print("residual norm:", np.linalg.norm(resid))
for lab,val in zip(labels,v):
    print(f"  {lab}: {val:.6f}")

# moduli dim check: 12 vertices*2=24 coords, minus 3 rigid motion = 21
# constraints: 11 length + 4 collinearity = 15 -> moduli before area caps = 21-15=6, matches n-3-(m-2)=8-2=6
