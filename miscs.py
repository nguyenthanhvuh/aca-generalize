import itertools
import z3

class OctForm(tuple):

    @classmethod
    def convert(cls, ts):
        #((1, x),)
        #((-1, y), (1, x))
        assert isinstance(ts ,tuple) and (len(ts) == 1 or len(ts) == 2)
        fst = OctFormOneVar.convert(ts[0])
        if len(ts) == 1:
            return fst
        else:
            snd = OctFormOneVar.convert(ts[1])
            return OctFormTwoVars(fst, snd)
        
    def mkUbExpr(self, c):
        assert isinstance(c, int), c
        return self.expr <= c
        
class OctFormOneVar(OctForm):
    """
    (-1, x)  (1, y)
    """
    def __new__(cls, c, s):
        assert c in {-1, 1},c 
        return super(OctFormOneVar, cls).__new__(cls, (c, s))

    def __init__(self, c, s):
        assert c in {-1, 1}, c
        self.c = c
        self.s = s

    def __str__(self):
        s = str(self.s)
        return s if self.c == 1 else '-' + s

    def meval(self, tc):
        assert isinstance(tc, dict)

        if not isinstance(self.s, str): s = str(self.s)
        assert s in tc
        v = tc[s]
        return v if self.c == 1 else self.c * v


    @property
    def expr(self):
        assert z3.is_expr(self.s), self.s
        return self.s if self.c == 1 else self.c * self.s

    @classmethod
    def convert(cls, t):
        return cls(t[0], t[1])

    
class OctFormTwoVars(OctForm):
    def __new__(cls, f1, f2):
        assert isinstance(f1, OctFormOneVar), f1
        assert isinstance(f2, OctFormOneVar), f2
        return super(OctForm, cls).__new__(cls, (f1, f2))
    
    def __init__(self, f1, f2):
        self.f1 = f1
        self.f2 = f2

    def __str__(self):
        return "{} + {}".format(self.f1,  self.f2)
        
    def meval(self, tc):
        return self.f1.meval(tc) + self.f2.meval(tc)

    @property
    def expr(self):
        return self.f1.expr + self.f2.expr

    @classmethod
    def convert(cls, t):
        return cls(OctFormOneVar(t[0]), octFormOneVar(t[1]))

    


class SMT:
    DISPROVED = 1
    PROVED = 2
    UNKNOWN = 3
    
    @classmethod
    def getStat(cls, models, isSucc):
        if models:
            return cls.DISPROVED
        elif isSucc:
            return cls.PROVED
        else:
            return cls.UNKNOWN
        

    @classmethod
    def check(cls, f, g):
        """
        Check if f => g,  if not return counterexample        
        """
        f = z3.Not(z3.Implies(f, g))
        models, stat = cls.getModels(f, 1)
        cexs, isSucc = cls.extract(models)
        return cexs, isSucc

    @classmethod
    def createSolver(cls):
        solver = z3.Solver()
        timeout= 3 * 1000  #3 secs
        solver.set(timeout=timeout)  #secs
        return solver

    @classmethod
    def extract(self, models):
        assert models is None or models is False \
            or (isinstance(models, list) and 
                all(isinstance(m, z3.ModelRef) for m in models)
                and models), models

        cexs = set()
        isSucc = models is not None
        if isSucc and models: #disproved
            cexs = [{str(s): int(str(model[s])) for s in model}
                    for model in models]
        return cexs, isSucc   

    @classmethod
    def getModels(cls, f, k):
        """
        Returns the first k models satisfiying f.
        If f is not satisfiable, returns False.
        If f cannot be solved, returns None
        If f is satisfiable, returns the first k models
        If f is a tautology, i.e., True, then the result is []
        """
        assert z3.is_expr(f), f
        assert k >= 1, k

        solver = cls.createSolver()
        solver.add(f)
        
        models = []
        i = 0
        while solver.check() == z3.sat and i < k:
            i = i + 1
            m = solver.model()
            if not m: #if m == []
                break
            models.append(m)
            #create new constraint to block the current model
            block = z3.Not(z3.And([v() == m[v] for v in m]))
            solver.add(block)

        stat = solver.check()
        
        if stat == z3.unknown:
            rs = None
        elif stat == z3.unsat and i==0:
            rs = False
        else:
            rs = models
        return rs, stat    


class Miscs:
    @staticmethod
    def getTermsFixedCoefs(ss, k):
        """
        >>> assert len(Miscs.getTermsFixedCoefs(range(3), 2)) == 18
        >>> assert len(Miscs.getTermsFixedCoefs(['x','y','z'], 4)) == 26
        >>> sorted(Miscs.getTermsFixedCoefs(['x','y'], 2))
        [((-1, 'x'),), ((-1, 'x'), (-1, 'y')), ((-1, 'x'), (1, 'y')), ((-1, 'y'),), ((1, 'x'),), ((1, 'x'), (-1, 'y')), ((1, 'x'), (1, 'y')), ((1, 'y'),)]
        """
        
        if len(ss) < k:
            k = len(ss)
        rs = []

        #[(0, -1), (0, 1), (-1, 0), (-1, -1), (-1, 1), (1, 0), (1, -1), (1, 1)]
        css = [cs for cs in itertools.product(*([[0, -1, 1]] * k))
               if not all(c == 0 for c in cs)]
        
        for ss_ in itertools.combinations(ss, k): # [(0,1), (0,2), (1,2)]
            r = [tuple((c,s) for c,s in zip(cs,ss_) if c)
                 for cs in css] #-1 * a
            rs.extend(r)
            
        return set(rs)
    
