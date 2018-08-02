import math

import z3
from miscs import Miscs, SMT, OctForm
import vu_common as CM

# Main
def generalize(f, ss, maxV, minV):
    assert z3.is_expr(f), f
    assert isinstance(ss, set) and all(z3.is_expr(x) for x in ss), ss

    ofs = Miscs.getTermsFixedCoefs(ss, 2)  
    ofs = [OctForm.convert(of) for of in ofs] #octagonal forms
    #fExprs = [f.expr for f in fs]

    ofs = [(of, of.mkUbExpr(maxV)) for of in ofs]
    rs = [(of, SMT.check(f, ubExpr)) for (of, ubExpr) in ofs]
    
    rs = [(of, cexs) for (of, (cexs, isSucc)) in rs
          if SMT.getStat(cexs, isSucc) != SMT.DISPROVED]

    def _f(octForm):
        statsd = {maxV: SMT.PROVED}
        boundV = gc(f, octForm, minV, maxV, statsd)
        if boundV not in statsd or statsd[boundV] != SMT.DISPROVED:
            return boundV
        else:
            return None

    print "compute upperbounds for {} oct terms".format(len(rs))
    ubVs = [(of, _f(of)) for (of, _) in rs]
    ubVs = [(of, v) for (of, v) in ubVs if v is not None]

    return ubVs

def gc(f, octForm, minV, maxV, statsd):
    assert z3.is_expr(f), f
    assert isinstance(octForm, OctForm), octForm
    assert minV <= maxV, (minV, maxV, octForm)
    assert isinstance(statsd, dict), statsd #{v: proved}

    if minV == maxV:
        return maxV
    elif maxV - minV == 1:
        if minV in statsd and stasd[minv] == SMT.DISPROVED:
            return maxV

        inv = octForm.mkUbExpr(minV)
        cexs, isSucc = SMT.check(f, inv)
        stat = SMT.getStat(cexs, isSucc)

        assert minV not in statsd
        statsd[minV] = stat
        
        if stat == SMT.DISPROVED:
            return maxV
        else:
            return minV
        

    v = int(math.ceil((maxV + minV) / 2.0))
    inv = octForm.mkUbExpr(v)
    cexs, isSucc = SMT.check(f, inv)
    stat = SMT.getStat(cexs, isSucc)
    assert v not in statsd
    statsd[v] = stat
    
    if stat  == SMT.DISPROVED:
        assert cexs
        tcs = [octForm.meval(cex) for cex in cexs]
        minV = max(tcs)
    else:
        maxV = v

    return gc(f, octForm, minV, maxV, statsd)


if __name__ == "__main__":
    #import doctest
    #doctest.testmod()

    x = z3.Int('x')
    y = z3.Int('y')
    f1 = x >= z3.IntVal('-13')
    f2 = x <= z3.IntVal('100')
    f3 = x + y <= 72
    f = z3.And(f1,f2,f3)

    octMaxV = 100
    maxV = octMaxV
    minV = -1*maxV
    
    rs = generalize(f, set([x, y]), maxV, minV)
    print "results"
    print '\n'.join("{} < {}".format(of, ub) for (of, ub) in rs)
    
