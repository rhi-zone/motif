import numpy as np

def L(mean,dir_):
    return (np.array(mean,dtype=float), np.array(dir_,dtype=float))

def intersect(l1,l2):
    m1,d1=l1; m2,d2=l2
    A=np.array([d1,-d2]).T
    b=m2-m1
    t=np.linalg.solve(A,b)
    return m1+t[0]*d1

lines = {
 'BM_BR':      L((104,136.46031746),(0.99971998,-0.02366341)),
 'BRtail_D':   L((142.23684211,117.5),(0.30488956,-0.95238771)),
 'LM_C':       L((45.5,69.328125),(-0.99978629,-0.02067318)),
 'BM_C':       L((74.65625,103.5),(0.13528381,-0.99080689)),
 'D_tip':      L((153.73076923,83.5),(0.32018116,-0.94735633)),   # near-D to tip
 'tip_Utail':  L((153.88,59.0),(-0.30854027,-0.95121128)),         # tip to near-U
 'RM_C':       L((113.0,70.41538462),(-0.99983064,-0.0184037)),
 'Utail_TR':   L((143.79487179,25.0),(-0.27271513,-0.96209483)),   # near-U to TR
 'TM_TR':      L((105.5,4.203125),(-0.99832438,-0.05786561)),
 'U_RM':       L((147.0,58.0),(0.0,-1.0)),
 'LM_TL':      L((7.10769231,35.0),(-0.12355232,-0.99233806)),
 'TL_TM':      L((36.5,2.0),(0.99998879,0.00473465)),
 'BM_BL':      L((35.5,136.5),(-0.99972802,-0.02332116)),
 'BL_LM':      L((6.23076923,103.0),(0.15691696,-0.9876118)),
 'D_RM':       L((147.0,84.0),(0.0,-1.0)),
 'TM_C':       L((75.5,36.5),(0.1059767,0.99436861)),
}

TL = intersect(lines['LM_TL'], lines['TL_TM'])
TM = intersect(lines['TL_TM'], lines['TM_TR'])
TR = intersect(lines['TM_TR'], lines['Utail_TR'])
U  = intersect(lines['Utail_TR'], lines['U_RM'])
Tip = intersect(lines['tip_Utail'], lines['D_tip'])
D  = intersect(lines['D_tip'], lines['D_RM'])
BR = intersect(lines['BM_BR'], lines['BRtail_D'])
BM = intersect(lines['BM_BR'], lines['BM_BL'])
BL = intersect(lines['BL_LM'], lines['BM_BL'])
LM = intersect(lines['LM_TL'], lines['BL_LM'])
RM = intersect(lines['RM_C'], lines['U_RM'])  # U_RM and D_RM are same vertical line x=147

# C: least squares point closest to 4 lines (LM_C, RM_C, TM_C, BM_C)
def point_line_normal_eqs(l):
    m,d = l
    n = np.array([-d[1], d[0]])  # normal
    n = n/np.linalg.norm(n)
    return n, np.dot(n, m)

rows=[]; rhs=[]
for key in ['LM_C','RM_C','TM_C','BM_C']:
    n,c = point_line_normal_eqs(lines[key])
    rows.append(n); rhs.append(c)
Amat = np.array(rows); bvec=np.array(rhs)
C, *_ = np.linalg.lstsq(Amat,bvec, rcond=None)

names = dict(TL=TL,TM=TM,TR=TR,U=U,Tip=Tip,D=D,BR=BR,BM=BM,BL=BL,LM=LM,RM=RM,C=C)
print("Vertices (pixel coords):")
for k,v in names.items():
    print(f"  {k}: ({v[0]:.2f}, {v[1]:.2f})")

def d(p,q): return np.linalg.norm(np.array(p)-np.array(q))

print()
print("Edge length checks (px), unit should be consistent ~65-68:")
edges = [
 ('TL-TM',TL,TM),('TM-TR',TM,TR),('TR-Tip? (should NOT be 1, TR is not endpoint)',TR,Tip),
 ('Tip-BR? (should NOT be 1 either)',Tip,BR),
 ('BR-BM',BR,BM),('BM-BL',BM,BL),('BL-LM',BL,LM),('LM-TL',LM,TL),
 ('LM-C',LM,C),('C-RM',C,RM),('TM-C',TM,C),('C-BM',C,BM),
 ('U-D (=S fence?)',U,D),
 ('TR-U',TR,U),('U-Tip',U,Tip),('Tip-D',Tip,D),('D-BR',D,BR),
 ('U-RM',U,RM),('RM-D',RM,D),
]
for name,p,q in edges:
    print(f"  {name}: {d(p,q):.2f}")

# check collinearity + betweenness: U on TR-Tip line? D on Tip-BR line? RM on U-D line?
def collinear_t(p,q,r):
    # param t such that r = p + t*(q-p); also perpendicular distance
    pq = np.array(q)-np.array(p)
    pr = np.array(r)-np.array(p)
    t = np.dot(pr,pq)/np.dot(pq,pq)
    perp = pr - t*pq
    return t, np.linalg.norm(perp)

print()
t,perp = collinear_t(TR,Tip,U)
print(f"U on TR-Tip: t={t:.4f} (0..1 expected), perp_dist={perp:.3f}px")
t,perp = collinear_t(Tip,BR,D)
print(f"D on Tip-BR: t={t:.4f}, perp_dist={perp:.3f}px")
t,perp = collinear_t(U,D,RM)
print(f"RM on U-D: t={t:.4f}, perp_dist={perp:.3f}px")
