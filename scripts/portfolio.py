import os
import signal
import sys

binpath=sys.argv[1]

p_ic3_r, p_ic3_w = os.pipe()
os.set_inheritable(p_ic3_r,True)
id_ic3=os.fork()
if id_ic3==0:
    #os.close(p_ic3_w)
    sys.stdin.close()
    os.dup2(p_ic3_r, 0)
    os.execl(binpath+'vvt-verify','vvt-verify',
             '--backend=cons:'+binpath+'z3 -smt2 -in',
             '--backend=lifting:'+binpath+'z3 -smt2 -in',
             '--backend=domain:'+binpath+'z3 -smt2 -in',
             '--backend=init:'+binpath+'z3 -smt2 -in',
             '--backend=cons:'+binpath+'mathsat')
os.close(p_ic3_r)

p_bmc_r, p_bmc_w = os.pipe()
os.set_inheritable(p_bmc_r,True)
id_bmc=os.fork()
if id_bmc==0:
    os.close(p_bmc_w)
    sys.stdin.close()
    os.dup2(p_bmc_r, 0)
    os.execl(binpath+'vvt-bmc','vvt-bmc','--solver='+binpath+'z3 -smt2 -in','-i','-d','50')
os.close(p_bmc_r)
    
while True:
    inp = sys.stdin.buffer.read(1024)
    if len(inp)==0:
        os.close(p_ic3_w)
        os.close(p_bmc_w)
        break
    os.write(p_ic3_w,inp)
    os.write(p_bmc_w,inp)
    
id_exit,res = os.wait()

if id_exit==id_ic3:
    os.kill(id_bmc,signal.SIGKILL)
else:
    os.kill(id_ic3,signal.SIGKILL)
