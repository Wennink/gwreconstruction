RR.<PP,aa,bb,cc,dd,ee,ff,gg,hh,W> = PolynomialRing(QQ,10,order='lex')

def is_deg1(cohclass,Wonly):
    if Wonly:
        return cohclass == W
    return cohclass.degree() == 1

class symbol:
    def __init__(self,terms,nofractions=False):
        self.terms = terms
        self.consolidate()
        if nofractions:
            self.nofractions()

    def consolidate(self):
        new = deepcopy(self.terms)
        for term in new:
            term[0].sort()
            term[0].reverse()
        new.sort()
        for i in range(len(new)-1):
            if new[i][0] == new[i+1][0]:
                new[i+1][1] += new[i][1]
                new[i][1] = 0
        new = [sr for sr in new if sr[1] != 0]
        new.reverse()
        self.terms = new

    def __add__(self,other):
        new = deepcopy(self)
        new.terms += deepcopy(other.terms)
        new.consolidate()
        return new

    def __radd__(self,other):
        if other == _sage_const_0 :
            return deepcopy(self)
        else:
            return self + other  

    def __neg__(self):
        return (-1)*self

    def __sub__(self,other):
        return self+(-1)*other 

    def __mul__(self,other):
        return self.__rmul__(other)

    def __rmul__(self,other):
        new = deepcopy(self)
        for i in new.terms:
            i[1] *= other
        new.consolidate()
        return new

    def __repr__(self):
        s = ''
        m = 1
        for i in self.terms:
            if len(repr(i[1])) > m:
                m = len(repr(i[1]))
        for i in self.terms:
            s += repr(i[1]) + (m-len(repr(i[1]))+1)*' ' + repr(i[0]) + '\n'
        return s.rstrip('\n')

    def nofractions(self):
        f = 1
        for i in self.terms:
            f = lcm(f,denominator(i[1]))
        for i in self.terms:
            i[1] *= f

    def subs(self,ss):
        new = deepcopy(self)
        presub = [aa,bb,cc,dd,ee,ff,gg,hh]
        subdic = {}
        for i in range(len(ss)):
            subdic[presub[i]] = ss[i]
        for i in new.terms:
            for j in range(len(i[0])):
                i[0][j]=i[0][j].subs(subdic)
        new.consolidate()
        return new

    #this assumes all the psi classes are concentrated in a single point
    def kill_pts_below(self,nr):
        new = deepcopy(self)
        for i in new.terms:
            if len(i[0]) - i[0][0].degree(PP) < nr: 
                i[1] = 0
        new.consolidate()
        return new

    #this assumes all the psi classes are concentrated in a single point
    def applydivisor(self,Wonly = false):
        new = deepcopy(self)
        for t in new.terms:
            if t[0][0].degree(PP) == 0:
                if any(list(map(lambda x: is_deg1(x,Wonly),t[0]))):
                    t[1] = 0
                    continue
            for ind in range(1,len(t[0])):
                if is_deg1(t[0][ind],Wonly):
                    t[0][0] = RR.monomial_quotient(t[0][0]*t[0][ind],PP)
                    t[0] = [t[0][i] for i in range(len(t[0])) if i!=ind]
                    break
        new.consolidate()
        return new

    #this assumes all the psi classes are concentrated in a single point
    def applystring(self):
        new = deepcopy(self)
        for t in new.terms:
            if t[0][-1] == 1:
                if t[0][0].degree(PP) == 0:
                    t[1] = 0
                    continue
                t[0][0] = RR.monomial_quotient(t[0][0],PP)
                t[0] = [t[0][i] for i in range(len(t[0])-1)]
        new.consolidate()
        return new  

    #this assumes all the psi classes are concentrated in a single point
    def applydilaton(self,g):
        new = deepcopy(self)
        for t in new.terms:
            if t[0][0] == PP:
                tempt = [t[0][i] for i in range(1,len(t[0]))]
                t[0] = tempt
                t[1] *= len(tempt)+2*g-2
        new.consolidate()
        return new

    def kill_primitive(self):
        new = deepcopy(self)
        for i in new.terms:
            if i[0][0].degree(PP) == 0:
                i[1] = 0
        new.consolidate()
        return new

    def kill_isolated_W(self):
        new = deepcopy(self)
        for i in new.terms:
            for j in i[0]:
                if j == W^j.degree() or j == PP*W^j.degree(W):
                    i[1] = 0
        new.consolidate()
        return new

    def kill_double_W(self):
        new = deepcopy(self)
        for i in new.terms:
            if i[0][-1] == W^i[0][-1].degree() and i[0][-2] == W^i[0][-2].degree():
                i[1] = 0
        new.consolidate()
        return new

    def extend(self,ext):
        new = deepcopy(self)
        for i in new.terms:
            i[0] += ext
        new.consolidate()
        return new

    #this assumes all the psi classes are concentrated in a single point
    def pullback1(self,ext1):
        new = deepcopy(self)
        newterms = []
        for t in new.terms:
            nt = deepcopy(t)
            nt[0].append(ext1)
            newterms.append(nt)
            if t[0][0].degree(PP) >= 1:
                nt = deepcopy(t)
                nt[1] *= -1
                nt[0][0] = RR.monomial_quotient(nt[0][0]*ext1,PP)
                newterms.append(nt)
        new.terms = newterms
        new.consolidate()
        return new


#assumes the tautclass is already the primitive part with only monomial polynomials, does not work for g > 3
def symbol_from_tautclass(g,tc,inputlist=[aa,bb,cc,dd,ee,ff,gg,hh]):
    symbrel = []
    for decstr in tc.terms:
        gam = decstr.gamma
        for i,gen in enumerate(gam.genera()):
            if gen == g:
                termsym = [get_leg_input(inputlist,decstr,j) for j in gam.legs(i)]
                if decstr.poly[0][0][i] == [1]:
                    termsym.append(PP^2)
                symbrel.append([termsym,decstr.poly[0][2]])
    return symbol(symbrel)

def get_leg_input(inputlist,decstr,j):
    gam = decstr.gamma
    j = Integer(j)
    psipart = 1
    psis = decstr.poly[0][1]
    if j in psis.keys():
        psipart = PP^psis[j]
    if j <= gam.n():
        return psipart*inputlist[j-1]
    invj = gam.leginversion(j)
    ans = psipart
    for k in gam.legs(gam.vertex(invj)):
        if k != invj:
            ans *= get_leg_input(inputlist,decstr,k)
    return ans

