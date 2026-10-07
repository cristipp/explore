import random,sys
def mr(n):
    if n<2:return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%p==0:return n==p
    d=n-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x in(1,n-1):continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True
def rp(d):
    while True:
        p=random.randrange(10**(d-1),10**d)|1
        if mr(p):return p
d=int(sys.argv[1]);c=int(sys.argv[2]);random.seed(int(sys.argv[3]) if len(sys.argv)>3 else d*100+c)
for i in range(c):
    p=rp(d);q=rp(d)
    while q==p:q=rp(d)
    print('{"id": "d%d_%d", "n": %d}'%(d,i,p*q))
