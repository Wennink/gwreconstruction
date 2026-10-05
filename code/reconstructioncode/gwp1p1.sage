#conventions:
#classes: -1 = pt, 0 = S, 1 = F
from sage.symbolic.operators import add_vararg
from sage.misc.cachefunc import cached_function
from sage.combinat.integer_vector import integer_vectors_nk_fast_iter

def gw_P1xP1(g,inputpsi,beta):
    s = beta[0]
    f = beta[1]
    psi = inputpsi
    if s*f-s-f+1-g < 0 and psi == []:
        return 0
    if psi == [(1,1)]:
        psi = [(1,0)]
        s = beta[1]
        f = beta[0]
    if psi == [] and s < f:
        s = beta[1]
        f = beta[0]
    return calculate_gw_P1xP1(g,tuple(psi),tuple([s,f]))
    
@cached_function
def calculate_gw_P1xP1(g,tuplepsi,tuplebeta):
    beta = list(tuplebeta)
    psi = list(tuplepsi)
    print("first time request for: ",g,psi,beta)
    if g == 0:
        if beta == [1,0] or beta == [0,1]:
            return 1
        if beta == [0,0]:
            return 0
        return apply_form_P1xP1(getgenus0formulas_P1xP1()[0][1:],beta)
    if g == 1:
        if beta == [0,0]:
            return 0
        return apply_form_P1xP1(getgenus1formulas_P1xP1()[:-1],beta)
    if g == 2:
        if psi == []:
            if beta == [0,0]:
                return 0
            return apply_form_P1xP1(getgenus2formulas_P1xP1()[2][:-1],beta)
        if psi == [(1,-1)]:
            if beta == [0,0]:
                return 0
            return apply_form_P1xP1(getgenus2formulas_P1xP1()[1][:-1],beta)
        if psi == [(1,0)]:
            if beta == [0]:
                return -1/1440
            return apply_form_P1xP1(getgenus2formulas_P1xP1()[0][:-1],beta)
    print("have not considered this case....")
    print(g,beta,psi)
    print("n = ",n)

def apply_form_P1xP1(formula,beta):
    result = 0
    for f in formula:
        result += splitbeta_P1xP1(f,beta)
    return result

def splitbeta_P1xP1(t,beta):
    result = 0
    nrcomp = len(t[0])
    for bs in integer_vectors_nk_fast_iter(beta[0],nrcomp):
        for bf in integer_vectors_nk_fast_iter(beta[1],nrcomp):
            result += compute_term_P1xP1(t,[bs,bf])
    return result

def compute_term_P1xP1(t,beta):
    nrcomp = len(t[0])
    sss = var('sss', n = nrcomp)
    fff = var('fff', n = nrcomp)
    f = deepcopy(t)
    suma = [0]*nrcomp
    for i in range(nrcomp):
        for j in range(1,len(beta)):
            suma[i] += beta[j][i]

    for i in range(nrcomp):
        f[2][i] = f[2][i].subs([sss[i] == beta[0][i] , fff[i] == beta[1][i]])
    result = multinomial(f[2])
    if result == 0:
        return 0
    for i in range(nrcomp):
        f[-1] = f[-1].subs([sss[i] == beta[0][i] , fff[i] == beta[1][i]])

    result *= f[-1]
    if result == 0:
        return 0
    for i in range(nrcomp):
        result *= gw_P1xP1(f[0][i],f[1][i],[beta[j][i] for j in range(len(beta))])
        if result == 0:
            return 0
    return result

def compute_gw_formula_P1xP1(tc,classes):
    gwf = []
    for t in tc.terms:
        gwf += compdeg0_P1xP1(t,classes,0)
    return gwf


def compdeg0_P1xP1(dec,classes,ind):
    nrcomp = len(dec.gamma.genera())
    if ind == nrcomp or nrcomp == 1:
        return compedges_P1xP1(dec,{i+1:classes[i] for i in range(len(classes))},0)
    result = []
    if dec.gamma.genera(ind) == 0:
        clas = [classes[j] for j in range(len(classes)) if dec.gamma.vertex(j+1) == ind]
        if len(dec.gamma.legs(ind)) == 3:
            h = [dec.gamma.leginversion(dec.gamma.legs(ind)[j]) for j in range(len(dec.gamma.legs(ind))) if dec.gamma.legs(ind)[j] > dec.gamma.n()]
            if len(clas) == 2:
                if set(clas) == {0,1}:
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:-1})
            if len(clas) == 1:
                result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:-1,h[1]:clas[0]})
                if clas[0] != -1:
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:clas[0],h[1]:-1})
            if len(clas) == 0:
                inters = [i for i in h if i in dec.gamma.legs(ind)]
                if len(inters) == 2:
                    skimmedh = [i for i in h if not i in inters]
                    result += getsubcase_P1xP1(dec,classes,ind,4,{skimmedh[0]:-1})
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
                            print("errrrrrrrrorrrrrrrr")
                            return recurscgwf(ndec,classes,ind,excdict)
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:1,h[1]:0,h[2]:-1})
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:1,h[1]:-1,h[2]:0})
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:-1,h[1]:1,h[2]:0})
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:-1,h[1]:0,h[2]:1})
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:0,h[1]:1,h[2]:-1})
                    result += getsubcase_P1xP1(dec,classes,ind,1,{h[0]:0,h[1]:-1,h[2]:1})
                    decpsis = dec.poly[0][1]
                    if decpsis != {}:
                        p = list(decpsis.keys())[0]
                        for i in range(3):
                            v = dec.gamma.vertex(h[i])
                            if p in dec.gamma.legs(v):
                                ndec = decstratum(dec.gamma,poly = dec.poly.coeff[0])
                                if p == h[i]:
                                    ndec = ndec*(2*dec.gamma.genera(v)-3+len(dec.gamma.legs(v)))
                                result += getsubcase_P1xP1(ndec,classes,ind,1,{h[j]:-1 for j in range(3) if j!=i},[v,h[i]])
            #if len(clas) == 3 then the whole thing is zero for dimension reasons
    if dec.gamma.genera(ind) == 1:
        if len(dec.gamma.legs(ind)) == 1:
            #am doing this in a lazy way that should be good enough for now, at least when the genera are in ascending order
            clas = [classes[j] for j in range(len(classes)) if dec.gamma.vertex(j+1) == ind]
            if len(clas) == 1:
                if clas[0] >= 0:
                    result += getsubcase_P1xP1(dec,classes,ind,-QQ((1,12)),{})
            else:
                h = dec.gamma.leginversion(dec.gamma.legs(ind)[0])
                result += getsubcase_P1xP1(dec,classes,ind,-QQ((1,12)),{h:0}) + getsubcase_P1xP1(dec,classes,ind,-QQ((1,12)),{h:1})
    if dec.gamma.genera(ind) == 2:
        if len(dec.gamma.legs(ind)) == 1:
            if dec.gamma.legs(ind)[0] in dec.poly[0][1].keys():
                clas = [classes[j] for j in range(len(classes)) if dec.gamma.vertex(j+1) == ind]
                if len(clas) == 1:
                    if clas[0] >= 0:
                        ndec = deepcopy(dec)
                        result += getsubcase_P1xP1(decstratum(ndec.gamma,poly = ndec.poly.coeff[0]),classes,ind,-QQ((1,1440)),{})
                else:
                    h = dec.gamma.leginversion(dec.gamma.legs(ind)[0])
                    ndec = deepcopy(dec)
                    ndec = decstratum(ndec.gamma,poly = ndec.poly.coeff[0])
                    result += getsubcase_P1xP1(ndec,classes,ind,-QQ((1,1440)),{h:0}) + getsubcase_P1xP1(ndec,classes,ind,-QQ((1,1440)),{h:1})


    result += compdeg0_P1xP1(dec,classes,ind+1)
    return result

def getsubcase_P1xP1(dec,classes,ind,mult,newclassdict,rempt = false):
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
    return compdeg0_P1xP1(subdec,subclasses,ind)

def compedges_P1xP1(dec,clasdic,ind):
    if ind == len(dec.gamma.edges()):
        return comppoints_P1xP1(dec,clasdic,deepcopy(clasdic),[[] for i in range(len(dec.gamma.genera()))],[0]*len(dec.gamma.genera()))
    result = []
    e0 = dec.gamma.edges()[ind][0]
    e1 = dec.gamma.edges()[ind][1]
    cd = deepcopy(clasdic)
    cd[e0] = 0
    cd[e1] = 1 
    result += compedges_P1xP1(dec,cd,ind+1)
    cd = deepcopy(clasdic)
    cd[e0] = 1
    cd[e1] = 0
    result += compedges_P1xP1(dec,cd,ind+1)
    decpsis = dec.poly[0][1]
    #assuming here that psi is at most 1
    if e0 in decpsis.keys():
        cd = deepcopy(clasdic)
        cd[e1] = -1
        ndec = deepcopy(dec)
        del(ndec.poly[0][1][e0])
        v = dec.gamma.vertex(e0)
        result += compedges_P1xP1((2*dec.gamma.genera(v)-3+len(dec.gamma.legs(v)))*ndec,cd,ind+1)
    if e1 in decpsis.keys():
        cd = deepcopy(clasdic)
        cd[e0] = -1
        ndec = deepcopy(dec)
        del(ndec.poly[0][1][e1])
        v = dec.gamma.vertex(e1)
        result += compedges_P1xP1((2*dec.gamma.genera(v)-3+len(dec.gamma.legs(v)))*ndec,cd,ind+1)
    if decpsis != {}:
        k = list(decpsis.keys())[0]
        if not k in [e0,e1]:
            v0 = dec.gamma.vertex(e0)
            v1 = dec.gamma.vertex(e1)
            if k in dec.gamma.legs(v0):
                cd = deepcopy(clasdic)
                cd[e1] = -1
                result += compedges_P1xP1(decstratum(dec.gamma,poly = dec.poly.coeff[0]),cd,ind+1)
            if k in dec.gamma.legs(v1):
                cd = deepcopy(clasdic)
                cd[e0] = -1
                result += compedges_P1xP1(decstratum(dec.gamma,poly = dec.poly.coeff[0]),cd,ind+1)
    return result


def comppoints_P1xP1(dec,clasdic,fulldic,psis,freepts):
    if clasdic == {}:
        return [[dec.gamma.genera(),psis,[2*var("sss{}".format(i))+2*var("fff{}".format(i))+dec.gamma.genera(i)-1-freepts[i] for i in range(len(dec.gamma.genera()))],dec.poly.coeff[0]]]
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
        return comppoints_P1xP1(dec,cd,fulldic,np,nf)
    if val == -1:
        nf = deepcopy(freepts)
        nf[v] += 1
        return comppoints_P1xP1(dec,cd,fulldic,psis,nf)
    ndec = deepcopy(dec)
    if val == 0:
        ndec.poly.coeff[0] *= var("sss{}".format(v))
    if val == 1:
        ndec.poly.coeff[0] *= var("fff{}".format(v))
    result = comppoints_P1xP1(ndec,cd,fulldic,psis,freepts)
    #divisor equation:
    if decpsis != {}:
        p = list(decpsis.keys())[0]
        if p in dec.gamma.legs(v):
            if {val,fulldic[p]} == {0,1}:
                ndec2 = decstratum(dec.gamma,poly = dec.poly.coeff[0])
                np = deepcopy(psis)
                if np[v] != []:
                    np[v] = []
                nc2 = deepcopy(cd)
                nf = deepcopy(freepts)
                nfd = deepcopy(fulldic)
                if p in nc2.keys():
                    del(nc2[p])
                    nf[v] += 1
                result += comppoints_P1xP1(ndec2,nc2,nfd,np,nf)
    return result
                
@func_persist
def getgenus1formulas_P1xP1():
    print("computing genus 1 formulas")
    rels = get_eche_fzm_tg(1,4,2,3,0)
    getzlerg1 = order_vertices(smarter_unsym_tc(partial_to_tautclass(rels[0][17],rels[1]),4))
    return simplifygwf(compute_gw_formula_P1xP1(getzlerg1*2,[0,0,1,1]))

@func_persist
def getgenus0formulas_P1xP1():
    print("computing genus 0 formulas")
    fzm, tg = get_eche_fzm_tg(0,4,1,3)
    WDVV = partial_to_tautclass(fzm[5],tg)
    return simplifygwf(compute_gw_formula_P1xP1(-WDVV,[0,1,-1,-1])),simplifygwf(compute_gw_formula_P1xP1(-WDVV,[0,0,1,1])),

@func_persist
def getgenus2formulas_P1xP1():
    print("computing genus 2 formulas")

    pbbp = pullbackrel(order_vertices(getLbp(3)))
    
    pbR243 = pullbackrel(order_vertices(getL24(3)))

    pbR263 = pullbackrel(order_vertices(getL26(3)))

    return simplifygwf(compute_gw_formula_P1xP1(-(1/2)*pbbp,[0,0,1])),simplifygwf(compute_gw_formula_P1xP1((1/2)*pbR243,[0,0,1,1])),simplifygwf(compute_gw_formula_P1xP1(-(5/2)*pbR263,[0,0,0,1,1,1]))
