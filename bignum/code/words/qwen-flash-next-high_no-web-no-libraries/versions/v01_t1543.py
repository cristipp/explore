import sys,json,time,signal

def alarm(*a): raise TimeoutError

def limit(argv):
 for i,x in enumerate(argv):
  if x=='--time-limit' and i+1<len(argv): s=argv[i+1]
  elif x.startswith('--time-limit='): s=x.split('=',1)[1]
  else: continue
  try:
   v=float(s); return v if v>=0 and v==v else 0.0
  except Exception: return 30.0
 return 30.0

ONES='zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen seventeen eighteen nineteen'.split()
TENS=['','','twenty','thirty','forty','fifty','sixty','seventy','eighty','ninety']
WORDS=['']*1000
for i in range(20): WORDS[i]=ONES[i]
for i in range(20,100):
 t,r=divmod(i,10); WORDS[i]=TENS[t]+('-'+ONES[r] if r else '')
for i in range(100,1000):
 h,r=divmod(i,100); WORDS[i]=ONES[h]+' hundred'+(' '+WORDS[r] if r else '')
SCALES=('','thousand','million','billion','trillion','quadrillion','quintillion')

def words(n):
 if n==0: return 'zero'
 if n<0: return 'minus '+words(-n)
 parts=[]; s=0
 while n:
  n,r=divmod(n,1000)
  if r:
   p=WORDS[r]
   if s: p+=' '+(SCALES[s] if s<len(SCALES) else 'scale'+str(s))
   parts.append(p)
  s+=1
 return ' '.join(reversed(parts))

def js(x):
 try: return json.dumps(x,separators=(',',':'),allow_nan=False)
 except Exception:
  try: return json.dumps(str(x),separators=(',',':'))
  except Exception: return '"null"'

def main():
 T=limit(sys.argv[1:])
 end=time.monotonic()+T
 armed=False
 if hasattr(signal,'SIGALRM') and hasattr(signal,'setitimer'):
  try:
   signal.signal(signal.SIGALRM,alarm)
   signal.setitimer(signal.ITIMER_REAL,max(1e-9,min(T,1e9)))
   armed=True
  except Exception: armed=False
 def arm():
  if armed:
   try: signal.setitimer(signal.ITIMER_REAL,max(1e-9,min(end-time.monotonic(),1e9)))
   except Exception: pass
 def disarm():
  if armed:
   try: signal.setitimer(signal.ITIMER_REAL,0)
   except Exception: pass
 def emit(s):
  disarm()
  try:
   sys.stdout.write(s); sys.stdout.flush()
  except Exception: pass
  arm()
 def timeout_line(line):
  try: ident=json.loads(line).get('id')
  except Exception: ident=None
  emit('{"id":'+js(ident)+',"answer":null,"timeout":true}\n')
 line=None; proc=False
 try:
  while True:
   line=sys.stdin.readline()
   if not line: break
   if not line.strip(): continue
   proc=True
   if time.monotonic()>=end:
    timeout_line(line); proc=False; break
   try:
    obj=json.loads(line)
    ident=obj['id']; ans=words(int(obj['a'])+int(obj['b']))
    if time.monotonic()>=end: timeout_line(line)
    else: emit('{"id":'+js(ident)+',"answer":'+js(ans)+'}\n')
   except TimeoutError:
    timeout_line(line); proc=False; break
   except Exception: timeout_line(line)
   proc=False
 except TimeoutError:
  if proc and line is not None: timeout_line(line)
 finally:
  disarm()
  try: sys.stdout.flush()
  except Exception: pass

if __name__=='__main__':
 try: main()
 except Exception: pass
 sys.exit(0)
