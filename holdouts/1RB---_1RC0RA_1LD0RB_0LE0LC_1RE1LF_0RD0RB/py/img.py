import sys, numpy as np
from PIL import Image
# img.py in.pgm out.png W H : defect view (adjacent equal cells), max-pooled; head gray
im=np.array(Image.open(sys.argv[1])).astype(np.int16)
W,H=int(sys.argv[3]),int(sys.argv[4])
cells=(im==0).astype(np.int8); head=(im==128)
d=np.zeros_like(cells,dtype=bool); k=int(sys.argv[5]) if len(sys.argv)>5 else 0
if k==0: d[:,:-1]=(cells[:,:-1]==cells[:,1:])
else: d[:,:-k]=(cells[:,:-k]!=cells[:,k:])
# visited mask: treat beyond extent white anyway
h,w=d.shape; bx=max(1,-(-w//W)); by=max(1,-(-h//H))
pw=bx*(-(-w//bx)); ph=by*(-(-h//by))
D=np.zeros((ph,pw),bool); D[:h,:w]=d
Hd=np.zeros((ph,pw),bool); Hd[:h,:w]=head
D=D.reshape(ph//by,by,pw//bx,bx).any(axis=(1,3)); Hd=Hd.reshape(ph//by,by,pw//bx,bx).any(axis=(1,3))
out=np.where(D,0,255).astype(np.uint8); out[Hd]=160
Image.fromarray(out).save(sys.argv[2]); print(out.shape,bx,by)
