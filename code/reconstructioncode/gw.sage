from sage.symbolic.operators import add_vararg
from sage.misc.cachefunc import cached_function
from sage.combinat.integer_vector import integer_vectors_nk_fast_iter

#We compute Gromov-Witten invariants of X_r, the projective plane blown up in r points in general position


############################################################
# We specify which tautological relations we use
############################################################

#pullback of a psi-class to the moduli space of stable maps
def pullbackrel(rel):
    newterms = []
    for t in rel.terms:
        newterms.append(deepcopy(t))
        if t.poly[0][1] != {}:
            newt = deepcopy(t)
            #for now only case with one psi
            k = list(t.poly[0][1].keys())[0]
            v = t.gamma.vertex(k)
            ne = newt.gamma.newleg()
            newt.gamma._genera = [0] + newt.gamma._genera
            newt.gamma._edges.append(ne)
            newt.gamma._legs[v] = [ne[1] if l == k else l for l in newt.gamma._legs[v]]
            newt.gamma._legs = [[k,ne[0]]] + newt.gamma._legs
            newterms.append(decstratum(newt.gamma,poly = -newt.poly.coeff[0]))
    return tautclass(newterms)
                
#we use as input classes: -1 = pt, 0 = H, i (>0) = E_i

#besides these classes we store the formulas using the following formula:
#class: -2 = sum E_i (coming from a genus 1)
#class: < -2 := connected to dictionary entry
#we use ddd0 for the H part of the degree on the 0th component, ddd1 on the 1st component, etc.
#similarly we use aaa_ij for a_j on the i-th component
#we use bbb for things connected to dictionary entries

@func_persist
def getgenus1formulas():
    print("computing genus 1 formulas")
    rels = get_eche_fzm_tg(1,4,2,3,0)
    getzlerg1 = partial_to_tautclass(rels[0][17],rels[1])
    return simplifygwf(compute_gw_formula(getzlerg1*(4/3),[0]*4)),simplifygwf(compute_gw_formula(getzlerg1*(4/3),[1]*4))

@func_persist
def getgenus0formulas():
    print("computing genus 0 formulas")
    fzm, tg = get_eche_fzm_tg(0,4,1,3)
    WDVV = partial_to_tautclass(fzm[5],tg)
    return simplifygwf(compute_gw_formula(-WDVV,[0,0,-1,-1])),simplifygwf(compute_gw_formula(-WDVV,[0,0,1,1])),

    
@func_persist
def getgenus2formulas():
    print("computing genus 2 formulas")
    pbbp = pullbackrel(order_vertices(getLbp(3)))
    
    pbR243 = pullbackrel(order_vertices(getL24(3)))

    return simplifygwf(compute_gw_formula(-(1/3)*pbbp,[0,0,0])),simplifygwf(compute_gw_formula(-pbR243,[0,1,1,1])),simplifygwf(compute_gw_formula((1/2)*pbbp,[1,1,1]))


@func_persist
def extrag2forms():
    bp = getLbp(3)
    pbbp = pullbackrel(order_vertices(bp))
    e2f = simplifygwf(compute_gw_formula((3/2)*var('dall')*pbbp,[1,0,0])+compute_gw_formula(-pbbp,[1,1,0])+compute_gw_formula((1/2)*var('dall')*pbbp,[1,1,1]))
    return e2f[:-5]+e2f[-4:-1]

@func_persist
def g2BPform():
    bp = getLbp(3)
    pbbp = pullbackrel(order_vertices(bp))
    bpf = simplifygwf(restrictP2(compute_gw_formula((1/3)*pbbp,[-1,0,0])+compute_gw_formula(-(1/3)*(3*var('dall')+1)*pbbp,[-1,-1,0])+compute_gw_formula((1/2)*var('dall')*(3*var('dall')+1)*pbbp,[-1,-1,-1])))
    bpf1 = []
    bpf2 = []
    for f in bpf:
        if f[0] == [0,2]:
            bpf2.append(f)
        else:
            bpf1.append(f)
    return bpf1,bpf2

@func_persist
def g2BPformH():
    bp = getLbp(3)
    pbbp = pullbackrel(order_vertices(bp))
    bpf = simplifygwf(restrictP2(compute_gw_formula(-(1/2)*pbbp,[-1,-1,0])+compute_gw_formula(var('dall')*pbbp,[-1,-1,-1])))
    bpf1 = []
    bpf2 = []
    for f in bpf:
        if f[0] == [0,2] and f[1] != [[],[]]:
            bpf2.append(f)
        else:
            bpf1.append(f)
    return bpf1,bpf2

#####################################################################################################
# We specify how to calculate the Gromov-Witten invariants
#####################################################################################################

# edits and filters the input before computing using relations
def gw_inv(g,inputpsi,beta):
    degr = beta[0]
    alfa = beta[1:]
    psi = inputpsi
    if any(x > beta[0] for x in beta[1:]):
        return 0
    #genus-degree formula
    if degr^2 - 3*degr - sum([alfa[i]*(alfa[i]-1) for i in range(len(alfa))]) - 2*g + 2 < 0 and psi == [] and len(alfa) < 9:
        return 0
    if g == 2:
        if not psi in [[],[(1,0)],[(1,-1)],[(1,1)]]:
            p = psi[0][1] - 1
            if len(alfa) > p:
                alfa = [alfa[p]]+[alfa[i] if i != p else alfa[0] for i in range(1,len(alfa))]
            else:
                alfa = [0] + alfa
            psi = [(1,1)]

    if len(alfa) != 0:
        if psi == [(1,1)]:
            a1 = alfa[0]
            alfa = alfa[1:]
        if len(alfa) != 0:
            alfa.sort()
            while alfa[0] == 0 or (alfa[0] == 1 and len(alfa) < 9):
            #while alfa[0] == 0 or alfa[0] == 1:
                alfa = alfa[1:]
                if len(alfa) == 0:
                    break

        if psi == [(1,1)]:
            alfa = [a1] + alfa

    #cremona transform
    if len(alfa) >= 4:
        if psi == [(1,1)] and alfa[0] <= alfa[3]:
            if alfa[1] + alfa[2] + alfa[3] > degr:
                nbeta = [2*degr - alfa[1] - alfa[2] - alfa[3], alfa[0], degr - alfa[2] - alfa[3], degr - alfa[1] - alfa[3], degr - alfa[1] - alfa[2]] + alfa[4:]
                #print("cremona!",psi,beta, nbeta)
                return gw_inv(g,psi,nbeta)
    if len(alfa) >= 3:
        if alfa[0]+alfa[1]+alfa[2] > degr:
            nbeta = [2*degr - alfa[0] - alfa[1] - alfa[2], degr - alfa[1] - alfa[2], degr - alfa[0] - alfa[2], degr - alfa[0] - alfa[1]] + alfa[3:]
            #print("cremona!",psi,beta,nbeta)
            if psi in [[],[(1,-1)]]:
                return gw_inv(g,psi,nbeta)
            if psi == [(1,0)]:
                result = 2*gw_inv(g,[(1,0)],nbeta)
                for i in range(3):
                    result -= gw_inv(g,[(1,i+1)],nbeta)
                return result
            if psi == [(1,1)]:
                result = gw_inv(g,[(1,0)],nbeta)
                for i in range(1,3):
                    result -= gw_inv(g,[(1,i+1)],nbeta)
                return result

    return calculate_gw_inv(g,tuple(psi),tuple([degr]+alfa))
    
#computes the Gromov-Witten invariants of X_r using relations
@cached_function
def calculate_gw_inv(g,tuplepsi,tuplebeta):
    beta = list(tuplebeta)
    psi = list(tuplepsi)
    print("first time request for: ",g,psi,beta)
    if g == 0:
        if beta == [1]:
            return 1
        if beta == [0,-1]:
            return 1
        if any(x < 0 for x in beta[1:]):
            return 0
        n = beta[0]*3-sum(beta[1:])-1
        if n >= 3:
            return apply_form(getgenus0formulas()[0][1:],beta,0)
        if n >= 0:
            form = getgenus0formulas()[1]
            coeff = -form[1][-1]
            ddd = var('ddd0')
            a1 = var("aaa_{}{}".format(0,1))
            coeff = coeff.subs(ddd == beta[0], a1 == beta[1])
            beta[1] -= 1
            return apply_form([form[0]]+[form[2]],beta,1)/coeff
        print("have not considered this genus 0 case...")
    if g == 1:
        if beta[0] == 0:
            return 0
        if any(x < 0 for x in beta[1:]):
            return 0
        n = beta[0]*3-sum(beta[1:]) 
        if n >= 2:
            return apply_form(getgenus1formulas()[0][:-1],beta,0)
        if n >= 0:
            form = getgenus1formulas()[1]
            coeff = -form[-1][-1]
            a1 = var("aaa_{}{}".format(0,1))
            coeff = coeff.subs(a1 == beta[1])
            beta[1] -= 2
            return apply_form(form[:-1],beta,1)/coeff
        print("have not considered this genus 1 case...")
    if g == 2:
        n = beta[0]*3-sum(beta[1:])+1
        if psi == []:
            if len(beta) < 2:
                deg = beta[0]
                f1,f2 = g2BPform()
                for f in f1:
                    f[-1] = f[-1].subs(var('dall') == deg)
                for f in f2:
                    f[-1] = f[-1].subs(var('dall') == deg)
                return -(apply_form(f1,[deg+1],0)+apply_form_part_pp(f2,deg+1))/2
            if n >= 0:
                form = deepcopy(extrag2forms())
                for f in form:
                    f[-1] = f[-1].subs(var('dall') == beta[0])
                beta[1] -= 2
                return (1/(beta[1]+2)/beta[0])*apply_form(form,beta,1)
        if psi == [(1,-1)]:
            if beta == [0]:
                return 0
            if n >= 2:
                return -apply_form(getgenus2formulas()[0][:-2]+getgenus2formulas()[0][-1:],beta,0)/beta[0]
        if psi == [(1,0)]:
            if beta == [0]:
                return -1/960
            if len(beta) < 2:
                deg = beta[0]
                f1,f2 = g2BPformH()
                for f in f1:
                    f[-1] = f[-1].subs(var('dall') == deg)
                for f in f2:
                    f[-1] = f[-1].subs(var('dall') == deg)
                return apply_form(f1,[deg+1],0)+apply_form_part_pp(f2,deg+1)
            if n >= 1:
                beta[1] -= 2
                return apply_form(getgenus2formulas()[1][:-1],beta,1)/(beta[1]+2)
        if psi == [(1,1)]:
            if beta == [0]:
                return -1/2880
            if n >= 1:
                if len(beta) == 1:
                    return -gw_inv(2,[],beta)
                if beta[1] == 0:
                    return -gw_inv(2,[],beta)
                beta[1] -= 1
                return apply_form(getgenus2formulas()[2][:-1],beta,1)
    print("have not considered this case....")
    print(g,beta,psi)
    print("n = ",n)

#computes the invariants of X_1 using the method precribed by the reconstruction theorem
def gw_X1(g,inputpsi,beta):
    if g != 2:
        return gw_inv(g,inputpsi,beta)
    degr = beta[0]
    alfa = beta[1:]
    psi = inputpsi
    if any(x > beta[0] for x in beta[1:]):
        return 0
    if degr^2 - 3*degr - sum([alfa[i]*(alfa[i]-1) for i in range(len(alfa))]) - 2*g + 2 < 0 and psi == [] and len(alfa) < 9:
        return 0
    if len(alfa) != 0:
        if psi == [(1,1)]:
            a1 = alfa[0]
            alfa = alfa[1:]
        if len(alfa) != 0:
            alfa.sort()
            while alfa[0] == 0 or alfa[0] == 1:
                alfa = alfa[1:]
                if len(alfa) == 0:
                    break
        if psi == [(1,1)]:
            alfa = [a1] + alfa

    return calculate_gw_X1(tuple(psi),tuple([degr]+alfa))

@cached_function
def calculate_gw_X1(tuplepsi,tuplebeta):
    beta = list(tuplebeta)
    psi = list(tuplepsi)
    print("first time request for: ",g,psi,beta)
    n = beta[0]*3-sum(beta[1:])+1
    if psi == []:
        if n >= 3:
            return apply_form(getgenus2formulas()[2][:-1],beta,0)
    if psi == [(1,-1)]:
        if beta == [0]:
            return 0
        if n >= 3:
            return apply_form(getgenus2formulas()[1][:-1],beta,0)
    if psi == [(1,0)]:
        if beta == [0]:
            return -1/960
        if n >= 2:
            return apply_form(getgenus2formulas()[0][:-1],beta,0)
    if psi == [(1,1)]:
        if beta == [0]:
            return -1/2880
        if n >= 1:
            if len(beta) == 1:
                return -gw_inv(2,[],beta)
            if beta[1] == 0:
                return -gw_inv(2,[],beta)
            beta[1] -= 1
            return apply_form(getgenus2formulas()[3][:-1],beta,1)
    print("have not considered this case....")
    print(g,beta,psi)
    print("n = ",n)

#we evaluate the formula for computing Gromov-Witten invariants
def apply_form(formula,beta,nrexc):
    newbeta = beta + [0 for i in range(nrexc - len(beta) + 1)]
    result = 0
    for f in formula:
        result += pre_comp(f,newbeta,nrexc)
    return result

#we evaluate the formula for computing Gromov-Witten invariants of the projective plane, as done by Belorousski-Pandharipande
def apply_form_part_pp(formula,deg):
    result = 0
    for f in formula:
        for i in range(2,deg-2):
            result += compute_term(f,[[i,deg-i]],1)
    return result

## the following 4 functions recursively iterate over possible ways to split the degree
## it is optimized using the symmetric action on the blown up points

def splitbeta(t,beta,nrexc):
    #print(beta,nrexc)
    nrcomp = len(t[0])
    if isinstance(beta[0],sage.rings.integer.Integer) or isinstance(beta[0],sage.rings.rational.Rational):
        result = 0
        for iv in integer_vectors_nk_fast_iter(beta[0]-nrcomp,nrcomp):
            newbeta = deepcopy(beta)
            newbeta[0] = list(map(lambda x:x+1,iv))
            if any((newbeta[0][x] < 3 and t[0][x] > 0) for x in range(nrcomp)):
                continue
            result += splitbeta(t,newbeta,nrexc)
        return result
    alfas = arrayify(beta[nrexc+1:])
    if alfas == [[]]:
        splitbetas = [[1,[]]]
    else:
        splitbetas = splitbetamain(nrcomp,1,beta[0],alfas,range(len(beta)-1-nrexc),{})
    result = 0
    for sb in splitbetas:
        if nrexc == 1:
            for iv in integer_vectors_nk_fast_iter(beta[1],nrcomp):
                if any(beta[0][j] < iv[j] for j in range(nrcomp)):
                    continue
                result += compute_term(t,[beta[0],iv]+sb[1],sb[0])
        if nrexc == 2:
            for iv in integer_vectors_nk_fast_iter(beta[1],nrcomp):
                if any(beta[0][j] < iv[j] for j in range(nrcomp)):
                    continue
                for iv2 in integer_vectors_nk_fast_iter(beta[2],nrcomp):
                    if any(beta[0][j] < iv2[j] for j in range(nrcomp)):
                        continue
                    result += compute_term(t,[beta[0],iv,iv2]+sb[1],sb[0])
        if nrexc > 2:
            print("error!!!")
        if nrexc == 0:
            result += compute_term(t,[beta[0]]+sb[1],sb[0])
    return result

def arrayify(alfa):
    alfas = []
    alfat = []
    t2 = -1
    while alfa != []:
        t1 = alfa.pop()
        if t1 == t2 or t2 == -1:
            alfat.append(t1)
        else:
            alfas.append(deepcopy(alfat))
            alfat = [t1]
        t2 = t1
    alfas.append(alfat)
    return alfas

def splitbetamain(nrcomp,coeff,d,alfas,spots,dic):
    if alfas == []:
        return [[coeff,[dic[k] for k in range(len(dic))]]]
    result = []
    dcalfas = deepcopy(alfas)
    ap = dcalfas.pop()
    iv = [i for i in IntegerVectors(ap[0],nrcomp) if not any(d[j] < i[j] for j in range(nrcomp))]
    ss = [spots[i] for i in range(len(ap))]
    newspots = [spots[i] for i in range(len(ap),len(spots))]
    for p in Partitions(len(ap)):
        newcoeff = coeff * multinomial(p)
        arp = arrayify(p.to_list())
        sbs = splitbetasub(arp,0,ss,dic,iv)
        for subdic in sbs:
            result += splitbetamain(nrcomp,newcoeff,d,dcalfas,newspots,subdic)
    return result

def splitbetasub(arp,ind,spots,dic,iv):
    if len(arp) == ind:
        return [dic]
    result = []
    for piv in Combinations(iv,len(arp[ind])):
        dcs = deepcopy(spots)
        dcd = deepcopy(dic)
        for i in range(len(arp[ind])):
            for pi in range(arp[ind][i]):
                dcd[dcs.pop()] = piv[i]
        result += splitbetasub(arp,ind+1,dcs,dcd,[s for s in iv if not s in piv])
    return result

def pre_comp(t,beta,nrexc):
    nrcomp = len(t[0])
    for ind in range(len(t[1])):
        if t[1][ind] != []:
            nr = t[1][ind][0][1]
            if nr < -1:
                result = 0
                for p in range(1,len(beta)):
                    newt = deepcopy(t)
                    nr2 = nrexc
                    if p > nrexc:
                        nr2 += 1
                        newbeta = [beta[i] for i in range(nrexc + 1)] + [beta[p]] + [beta[i] if i != p else beta[nrexc + 1] for i in range(nrexc + 2,len(beta))]
                        newt[-1] = newt[-1].subs([var("bbb_{}{}".format(j,-nr)) == var("aaa_{}{}".format(j,nrexc + 1)) for j in range(nrcomp)])
                        newt[1][ind] = [(1,nrexc + 1)]
                    else:
                        newbeta = deepcopy(beta)
                        newt[-1] = newt[-1].subs([var("bbb_{}{}".format(j,-nr)) == var("aaa_{}{}".format(j,p)) for j in range(nrcomp)])
                        newt[1][ind] = [(1,p)]
                    result += pre_comp(newt,newbeta,max(1,nr2))
                return result
    if t[3] != {}:
        result = 0
        newbeta = deepcopy(beta)
        newt = deepcopy(t)
        for k in t[3].keys():
            if k > 0:
                if len(newbeta) <= k:
                    return 0
                newbeta[k] += t[3][k]
                del(newt[3][k])
            if k < -2:
                if k < -3:
                    print("erroooor")
                if t[3][k] == 1 and k == -3:
                    for p in range(1,len(beta)):
                        newestt = deepcopy(newt)
                        nr2 = nrexc
                        if p > nr2:
                            nr2 += 1
                            newestbeta = [newbeta[i] for i in range(nr2)] + [newbeta[p]] + [newbeta[i] if i != p else newbeta[nr2] for i in range(nr2 + 1,len(newbeta))]
                            newestt[-1] = newestt[-1].subs([var("bbb_{}{}".format(j,-k)) == var("aaa_{}{}".format(j,nr2)) for j in range(nrcomp)])
                            newestbeta[nr2] += t[3][k]
                        else:
                            newestt[-1] = newestt[-1].subs([var("bbb_{}{}".format(j,-k)) == var("aaa_{}{}".format(j,p)) for j in range(nrcomp)])
                            newestbeta = deepcopy(newbeta)
                            newestbeta[p] += t[3][k]
                        del(newestt[3][k])
                        result += pre_comp(newestt,newestbeta,nr2)
                else:
                    print("have not considered this case yet")
                return result
        return pre_comp(newt,newbeta,nrexc)
    if [(1,1)] in t[1]:
        return splitbeta(t,beta,1)
    return splitbeta(t,beta,nrexc)

def compute_term(t,beta,coeff):
    nrcomp = len(t[0])
    ddd = var('ddd', n = nrcomp)
    aaa = matrix(nrcomp, len(beta), [var("aaa_{}{}".format(i,j)) for i in range(nrcomp) for j in [0..len(beta)-1]])
    rr = var('rr')
    f = deepcopy(t)
    suma = [0]*nrcomp
    for i in range(nrcomp):
        for j in range(1,len(beta)):
            suma[i] += beta[j][i]

    for i in range(nrcomp):
        f[2][i] = f[2][i].subs([aaa[i][0] == suma[i] , ddd[i] == beta[0][i]])
    result = coeff*multinomial(f[2])
    if result == 0:
        return 0
    for i in range(nrcomp):
        f[-1] = f[-1].subs([aaa[i][0] == suma[i] , ddd[i] == beta[0][i] , rr == len(beta)-1] + [aaa[i][j] == beta[j][i] for j in range(1,len(beta))])

    nr = 3
    while not isRat(f[-1]):
        te = getTerms(f[-1])
        tei = [i for i in range(len(te)) if any(te[i].degree(var("bbb_{}{}".format(j,nr))) != 0 for j in range(nrcomp))]
        f[-1] = add_vararg(*[sum([te[i].subs([var("bbb_{}{}".format(j,nr)) == beta[k][j] for j in range(nrcomp)]) for k in range(1,len(beta))]) if i in tei else te[i] for i in range(len(te))])
        nr += 1
        if nr > 6:
            print(f[-1])
            print(t,beta)
            print("this doesn't seem good")
            break
    result *= f[-1]
    if result == 0:
        return 0
    for i in range(nrcomp):
        result *= gw_inv(f[0][i],f[1][i],[beta[j][i] for j in range(len(beta))])
        if result == 0:
            return 0
    return result

def getTerms(expr):
    if expr.operator() != add_vararg:
        return [expr]
    else:
        return expr.operands()

def isRat(mrat):
    try:
        QQ(mrat)
        return true
    except TypeError:
        return false

##################################################################
# computing the formula given a tautological relation
##################################################################

def compute_gw_formula(tc,classes):
    gwf = []
    for t in tc.terms:
        gwf += compdeg0(t,classes,0,{})
    return gwf

#this doesn't really work in general
def multipl(n1,n2,clasdic,excdict):
    a = min(n1,n2)
    b = max(n1,n2)
    if a == b:
        if a > -1:
            return (-1)**(a>0),{}
        if a <= -2:
            return var('rr'),{}
        if a < -2:
            if list(clasdic.values()).count(a) > 2 or a in excdict.keys():
                return -1,{}
            else:
                return -var('rr'),{}
    else:
        if b > 0 and a == -2:
            return -1,{}
        if b == -2:
            return -1,{}
        if b < -2:
            return -1,{a:b}
        if b > 0 and a < -2:
            return -1,{a:b}
    return 0,{}


def compdeg0(dec,classes,ind,excdict):
    nrcomp = len(dec.gamma.genera())
    if ind == nrcomp or nrcomp == 1:
        #print("a",dec,classes,ind,excdict)
        return compedges(dec,{i+1:classes[i] for i in range(len(classes))},0,excdict)
    result = []
    if dec.gamma.genera(ind) == 0:
        clas = [classes[j] for j in range(len(classes)) if dec.gamma.vertex(j+1) == ind]
        if len(dec.gamma.legs(ind)) == 3:
            h = [dec.gamma.leginversion(dec.gamma.legs(ind)[j]) for j in range(len(dec.gamma.legs(ind))) if dec.gamma.legs(ind)[j] > dec.gamma.n()]
            if len(clas) == 2:
                if clas[0] == clas[1]:
                    if clas[0] != -1:
                        result += getsubcase(dec,classes,ind,excdict,(-1)**(clas[0]>0),{h[0]:-1},false)
                else:
                    c0 = min(clas)
                    c1 = max(clas)
                    if c0 <= -3:
                        if c1 <= -3:
                            print("have not considered this case adsfew")
                        if c1 > 0:
                            ndic = deepcopy(excdict)
                            if c1 in ndic.keys():
                                ndic[c1] = ndic[c1] + ndic[c0]
                            else:
                                ndic[c1] = ndic[c0]
                            del ndic[c0]
                            nclas = [c1 if c == c0 else c for c in classes]
                            result += getsubcase(dec,nclas,ind,ndic,-1,{h[0]:-1},false)
            if len(clas) == 1:
                result += getsubcase(dec,classes,ind,excdict,1,{h[0]:-1,h[1]:clas[0]},false)
                if clas[0] != -1:
                    result += getsubcase(dec,classes,ind,excdict,1,{h[0]:clas[0],h[1]:-1},false)
            if len(clas) == 0:
                inters = [i for i in h if i in dec.gamma.legs(ind)]
                if len(inters) == 2:
                    skimmedh = [i for i in h if not i in inters]
                    rr = var('rr')
                    result += getsubcase(dec,classes,ind,excdict,rr+3,{skimmedh[0]:-1},false)
                if len(inters) == 0:
                    for i in range(3):
                        v = dec.gamma.vertex(h[i])
                        #this should be good enough until codim >= 5
                        if v > ind and dec.gamma.genera(v) == 0 and len(dec.gamma.legs(v)) == 3:
                            ndec = deepcopy(dec)
                            lv = deepcopy(ndec.gamma.legs(v))
                            lind = deepcopy(ndec.gamma.legs(ind))
                            ndec.gamma._legs[v] = lind
                            ndec.gamma._legs[v] = lv
                            return recurscgwf(ndec,classes,ind,excdict)
                    result += getsubcase(dec,classes,ind,excdict,1,{h[0]:0,h[1]:0,h[2]:-1},false)
                    result += getsubcase(dec,classes,ind,excdict,1,{h[0]:0,h[1]:-1,h[2]:0},false)
                    result += getsubcase(dec,classes,ind,excdict,1,{h[0]:-1,h[1]:0,h[2]:0},false)
                    newexc = getnr(classes,excdict)
                    result += getsubcase(dec,classes,ind,excdict,-1,{h[0]:newexc,h[1]:newexc,h[2]:-1},false)
                    result += getsubcase(dec,classes,ind,excdict,-1,{h[0]:newexc,h[1]:-1,h[2]:newexc},false)
                    result += getsubcase(dec,classes,ind,excdict,-1,{h[0]:-1,h[1]:newexc,h[2]:newexc},false)
                    decpsis = dec.poly[0][1]
                    if decpsis != {}:
                        p = list(decpsis.keys())[0]
                        for i in range(3):
                            v = dec.gamma.vertex(h[i])
                            if p in dec.gamma.legs(v):
                                ndec = decstratum(dec.gamma,poly = dec.poly.coeff[0])
                                if p == h[i]:
                                    ndec = ndec*(2*dec.gamma.genera(v)-3+len(dec.gamma.legs(v)))
                                result += getsubcase(ndec,classes,ind,excdict,1,{h[j]:-1 for j in range(3) if j!=i},false,[v,h[i]])
                if len(inters) > 2:
                    print("error, have not accounted for this case yet")
                    print(dec,classes,ind)
            #if len(clas) == 3 then the whole thing is zero for dimension reasons
        if len({i for i in set(clas) if i > 0}) <= 1 and (not -1 in clas) and (not 0 in clas):
            h = [dec.gamma.leginversion(dec.gamma.legs(ind)[j]) for j in range(len(dec.gamma.legs(ind))) if dec.gamma.legs(ind)[j] > dec.gamma.n()]
            skimmedh = [i for i in h if i not in dec.gamma.legs(ind)]
            ne = deepcopy(excdict)
            nc = deepcopy(classes)
            if len(set(clas)) > 2:
                print(dec,classes,ind,excdict)
                print("have not considered this case here yet PPP")
            if len(set(clas)) == 1:
                newexc = clas[0]
            if len(set(clas)) == 0:
                newexc = getnr(classes,excdict)
            if len(set(clas)) == 2:
                mic = min(clas)
                mac = max(clas)
                if mic == -2:
                    newexc = mac
                else:
                    if mac != -2:
                        nc = [i if i!=mic else mac for i in classes]
                        if mic in ne.keys():
                            if mac in ne.keys():
                                ne[mac] = ne[mac] + ne[mic]
                            else:
                                ne[mac] = ne[mic]
                            del(ne[mic])
                        newexc = mac
                    else:
                        newexc = mic
            result += getsubcase(dec,nc,ind,ne,(-1)^(len(dec.gamma.legs(ind))+len(skimmedh)+(len(skimmedh)-len(h))/2),{sh:newexc for sh in skimmedh},newexc)
    if dec.gamma.genera(ind) == 1:
        if len(dec.gamma.legs(ind)) == 1:
            #am doing this in a lazy way that should be good enough for now, at least when the genera are in ascending order
            clas = [classes[j] for j in range(len(classes)) if dec.gamma.vertex(j+1) == ind]
            if len(clas) == 1:
                if clas[0] == 0:
                    mult = -QQ((1,8))
                if clas[0] == -2:
                    mult = -var('rr')/24
                if clas[0] < -2:
                    if clas[0] in excdict.keys():
                        mult = -QQ((1,24))
                    else:
                        if classes.count(clas[0]) > 1:
                            mult = -QQ((1,24))
                        else:
                            mult = -var('rr')/24
                if clas[0] > 0:
                    mult = -QQ((1,24))
                if clas[0] != -1:
                    result += getsubcase(dec,classes,ind,excdict,mult,{},false)
            else:
                h = dec.gamma.leginversion(dec.gamma.legs(ind)[0])
                result += getsubcase(dec,classes,ind,excdict,-QQ((1,8)),{h:0},false) + getsubcase(dec,classes,ind,excdict,QQ((1,24)),{h:-2},false)
    if dec.gamma.genera(ind) == 2:
        if len(dec.gamma.legs(ind)) == 1:
            if dec.gamma.legs(ind)[0] in dec.poly[0][1].keys():
                clas = [classes[j] for j in range(len(classes)) if dec.gamma.vertex(j+1) == ind]
                if len(clas) == 1:
                    if clas[0] == 0:
                        mult = -QQ((1,960))
                    if clas[0] == -2:
                        mult = -var('rr')/2880
                    if clas[0] < -2:
                        if clas[0] in excdict.keys():
                            mult = -QQ((1,2880))
                        else:
                            if classes.count(clas[0]) > 1:
                                mult = -QQ((1,2880))
                            else:
                                mult = -var('rr')/2880
                    if clas[0] > 0:
                        mult = -QQ((1,2880))
                    if clas[0] != -1:
                        ndec = deepcopy(dec)
                        result += getsubcase(decstratum(ndec.gamma,poly = ndec.poly.coeff[0]),classes,ind,excdict,mult,{},false)
                else:
                    h = dec.gamma.leginversion(dec.gamma.legs(ind)[0])
                    ndec = deepcopy(dec)
                    ndec = decstratum(ndec.gamma,poly = ndec.poly.coeff[0])
                    result += getsubcase(ndec,classes,ind,excdict,-QQ((1,960)),{h:0},false) + getsubcase(ndec,classes,ind,excdict,QQ((1,2880)),{h:-2},false)


    result += compdeg0(dec,classes,ind+1,excdict)
    return result

def getsubcase(dec,classes,ind,excdict,mult,newclassdict,newexc,rempt = false):
    nrcomp = len(dec.gamma.genera())
    sub = dec.gamma.extract_subgraph([i for i in range(nrcomp) if not i == ind])
    decpsis = dec.poly[0][1]
    subdec = mult*dec.poly.coeff[0]*decstratum(sub[0],psi={sub[2][k]:decpsis[k] for k in decpsis.keys()})
    if rempt:
        subdec.gamma._legs[sub[1][rempt[0]]].remove(rempt[1])
    subclasses = [0]*(subdec.gamma.n())
    for k in range(1,dec.gamma.n()+1):
        if k in sub[2].keys():
            subclasses[sub[2][k]-1] = classes[k-1]
    for k in newclassdict:
        subclasses[sub[2][k]-1] = newclassdict[k]
    if newexc:
        dictcopy = deepcopy(excdict)
        if newexc in dictcopy.keys():
            dictcopy.update({newexc:excdict[newexc]+1})
        else:
            dictcopy.update({newexc:1})
    else:
        dictcopy = excdict
    return compdeg0(subdec,subclasses,ind,dictcopy)

def getnr(classes,excdict):
    nr = min(min(classes)-1,-3)
    if excdict != {}:
        nr = min(min(excdict.keys())-1,nr)
    return nr

def compedges(dec,clasdic,ind,excdict):
    if ind == len(dec.gamma.edges()):
        #print("b",dec,clasdic,ind,excdict)
        return comppoints(dec,clasdic,deepcopy(clasdic),excdict,[[] for i in range(len(dec.gamma.genera()))],[0]*len(dec.gamma.genera()))
    result = []
    e0 = dec.gamma.edges()[ind][0]
    e1 = dec.gamma.edges()[ind][1]
    cd = deepcopy(clasdic)
    cd[e0] = 0
    cd[e1] = 0 
    result += compedges(dec,cd,ind+1,excdict)
    cd = deepcopy(clasdic)
    nr = min(min(clasdic.values())-1,-3)
    cd[e0] = nr
    cd[e1] = nr
    result += compedges(-dec,cd,ind+1,excdict)
    decpsis = dec.poly[0][1]
    #assuming here that psi is at most 1
    if e0 in decpsis.keys():
        cd = deepcopy(clasdic)
        cd[e1] = -1
        ndec = deepcopy(dec)
        del(ndec.poly[0][1][e0])
        v = dec.gamma.vertex(e0)
        result += compedges((2*dec.gamma.genera(v)-3+len(dec.gamma.legs(v)))*ndec,cd,ind+1,excdict)
    if e1 in decpsis.keys():
        cd = deepcopy(clasdic)
        cd[e0] = -1
        ndec = deepcopy(dec)
        del(ndec.poly[0][1][e1])
        v = dec.gamma.vertex(e1)
        result += compedges((2*dec.gamma.genera(v)-3+len(dec.gamma.legs(v)))*ndec,cd,ind+1,excdict)
    if decpsis != {}:
        k = list(decpsis.keys())[0]
        if not k in [e0,e1]:
            v0 = dec.gamma.vertex(e0)
            v1 = dec.gamma.vertex(e1)
            if k in dec.gamma.legs(v0):
                cd = deepcopy(clasdic)
                cd[e1] = -1
                result += compedges(decstratum(dec.gamma,poly = dec.poly.coeff[0]),cd,ind+1,excdict)
            if k in dec.gamma.legs(v1):
                cd = deepcopy(clasdic)
                cd[e0] = -1
                result += compedges(decstratum(dec.gamma,poly = dec.poly.coeff[0]),cd,ind+1,excdict)
    return result


def comppoints(dec,clasdic,fulldic,excdict,psis,freepts):
    if clasdic == {}:
        return [[dec.gamma.genera(),psis,[3*var("ddd{}".format(i))-var("aaa_{}{}".format(i,0))+dec.gamma.genera(i)-1-freepts[i] for i in range(len(dec.gamma.genera()))],excdict,dec.poly.coeff[0]]]
    cd = deepcopy(clasdic)
    k = list(cd.keys())[0]
    val = cd[k]
    del(cd[k])
    v = dec.gamma.vertex(k)
    decpsis = dec.poly[0][1]
    if k in decpsis.keys():
        np = deepcopy(psis)
        np[v].append((decpsis[k],val))
        nf = deepcopy(freepts)
        if val == -1:
            nf[v] += 2
        else:
            nf[v] += 1
        return comppoints(dec,cd,fulldic,excdict,np,nf)
    if val == -1:
        nf = deepcopy(freepts)
        nf[v] += 1
        return comppoints(dec,cd,fulldic,excdict,psis,nf)
    ndec = deepcopy(dec)
    if val == 0:
        ndec.poly.coeff[0] *= var("ddd{}".format(v))
    if val == -2:
        ndec.poly.coeff[0] *= var("aaa_{}{}".format(v,0))
    if val < -2:
        ndec.poly.coeff[0] *= var("bbb_{}{}".format(v,-val))
    if val > 0:
        ndec.poly.coeff[0] *= var("aaa_{}{}".format(v,val)) 
    result = comppoints(ndec,cd,fulldic,excdict,psis,freepts)
    if decpsis != {}:
        p = list(decpsis.keys())[0]
        if p in dec.gamma.legs(v):
            mul,change = multipl(val,fulldic[p],clasdic,excdict)
            if mul != 0:
                ndec2 = decstratum(dec.gamma,poly = dec.poly.coeff[0])
                ndec2.poly.coeff[0] *= mul
                #relies on there being at most one psi
                np = deepcopy(psis)
                if np[v] != []:
                    np[v] = []
                ne = deepcopy(excdict)
                nc2 = deepcopy(cd)
                nf = deepcopy(freepts)
                nfd = deepcopy(fulldic)
                if p in nc2.keys():
                    del(nc2[p])
                    nf[v] += 1
                if change != {}:
                    ck = list(change.keys())[0]
                    if ck in ne.keys():
                        if change[ck] in ne.keys():
                            ne[change[ck]] = ne[change[ck]] + ne[ck]
                        else:
                            ne[change[ck]] = ne[ck]
                        del(ne[ck])
                    for k2 in nc2.keys():
                        if nc2[k2] == ck:
                            nc2[k2] = change[ck]
                    for k2 in nfd.keys():
                        if nfd[k2] == ck:
                            nfd[k2] = change[ck]
                    if change[ck] < -1:
                        ndec2.poly.coeff[0] = ndec2.poly.coeff[0].subs([var("bbb_{}{}".format(i,-ck)) == var("bbb_{}{}".format(i,-change[ck])) for i in range(len(dec.gamma.genera()))])
                    else:
                        ndec2.poly.coeff[0] = ndec2.poly.coeff[0].subs([var("bbb_{}{}".format(i,-ck)) == var("aaa_{}{}".format(i,change[ck])) for i in range(len(dec.gamma.genera()))])
                result += comppoints(ndec2,nc2,nfd,ne,np,nf)
    return result

        
def simplifygwf(gwf):
    for t in gwf:
        t[3] = [(i,t[3][i]) for i in t[3].keys()]
    gwf.sort()
    for i in range(len(gwf)-1):
        if gwf[i][:-1] == gwf[i+1][:-1]:
            gwf[i+1][-1] += gwf[i][-1]
            gwf[i][-1] = 0
    gwf = [i for i in gwf if i[-1] != 0]
    for t in gwf:
        t[3] = {i:j for (i,j) in t[3]}
    return gwf

def restrictP2(gwf):
    result = []
    for f in gwf:
        if f[3] == {} and not [(1,-3)] in f[1]:
            nf = deepcopy(f)
            for i in range(len(nf[0])):
                nf[2][i] = nf[2][i].subs(var("aaa_{}{}".format(i,0)) == 0)
                nf[-1] = nf[-1].subs(var("aaa_{}{}".format(i,0)) == 0)
                for j in range(3,6):
                    nf[-1] = nf[-1].subs(var("bbb_{}{}".format(i,j)) == 0)
            result.append(nf)
    return result

