######################################################################
# Computing matrices of Faber-Zagier-Pixton relations
######################################################################

# the relevant moduli types are:
# MODULI_RT = 1 for rational tail
# MODULI_ST = 3 for stable curves
#
# symmetry actions act on the first n-unsym points
# use unsym = None for 'normal' nonsymmetric relations
# use unsym = 0 for fully symmetric relations

@func_persist
def pre_processed_fzm(g,n,r,moduli_type,unsym = None):
    if unsym in [None,n-1]:
        unsym = n
    print("calculating FZ matrix for g=%s, n=%s, r=%s, moduli type %s" % (g,n,r,moduli_type))
    drels = derived_rels_SS(g,r,n,unsym,moduli_type)
    pnrels = possibly_new_FZ(g,r,n,moduli_type)
    if unsym != 0:
        pnrels = [unsymmetrize_vec_SS(p,g,r,getmarks(n,unsym),getmarks(n,0),moduli_type) for p in pnrels]
    allrels = drels + pnrels
    reldic={}
    for i in range(len(allrels)):
        for j in range(len(allrels[i])):
            reldic[i,allrels[i][j][0]]=allrels[i][j][1]
    return Matrix(reldic,sparse=True)

@func_persist
def get_eche_fzm_tg(g,n,r,moduli_type,unsym = None):
    fzm = pre_processed_fzm(g,n,r,moduli_type,unsym)
    print("echelonizing FZ matrix for g=%s, n=%s, r=%s, moduli type %s" % (g,n,r,moduli_type))
    fzm.echelonize()
    if fzm.is_zero():
        return fzm,[]
    return dzr(fzm),general_tautgens(g,n,r,moduli_type,unsym)

#returns the tautological generators as a list decstratum classes
#the last points are the points not fixed by the symmetry action
def general_tautgens(g,n,r,moduli_type=MODULI_ST,unsym = None):
    if unsym == None or unsym == n-1:
        unsym = n
    strata = all_strata(g,r,getmarks(n,unsym),moduli_type)
    if unsym == n:
        return list(map(Graphtodecstratum,strata))
    #the following assumes that the points in ps_strata are ordered and all the edges are at the end, which seems to be the case
    st = []
    for ps in strata:
        dc = deepcopy(ps)
        for i in range(2,n+1):
            dc.M[0,i] = i
        st.append(Graphtodecstratum(dc))
    return st

#gives relations modulo some monomials in kappa and psi classes that are of high degree (relative to the genus)
@func_persist
def rem_kappapsi_fzm(g,n,r,moduli_type,unsym = None):
    fzm, tg = get_eche_fzm_tg(g,n,r,moduli_type,unsym)
    hkp = highkappapsi(tg)
    return nicely_remove_cols(fzm,tg,hkp)

def highkappapsi(taut_gens):
    hkp = []
    for i in range(len(taut_gens)):
        dec = taut_gens[i]
        allpsis = list(map(lambda x: x[0][1],dec.split()[0]))
        allkappas = list(map(lambda x: x[0][0][0],dec.split()[0]))
        for j in range(len(dec.gamma.genera())):
            g = dec.gamma.genera(j)
            kappas = allkappas[j]
            psis = list(allpsis[j].values())
            psis.sort()
            #if 3*len(kappas) > g:
            if len(kappas) > max(g - 2,0):
                hkp.append(i)
                break
            if sum(psis) >= g and sum(psis) != 0:
                hkp.append(i)
                break

            #proposition 3.3 in paper by Shadrin et al 'tautological ring via PPZ relations'
            if g > 4:
                if kappas == [1] and sum(psis) >= g - 2:
                    hkp.append(i)
                    break
                if kappas == [0] and sum(psis) >= g - 1:
                    if not (g - 1 in psis or g - 2 in psis):
                        hkp.append(i)
                        break
                continue

            if g <= 2:
                continue
            #psis have been sported so we need to list them in descending order
            for gkp in [(3,[2],[]),(3,[1],[1]),(3,[],[1,1]),
                    (4,[3],[]),(4,[2],[1]),(4,[1],[2]),(4,[1],[1,1]),(4,[0,2],[]),(4,[1,1],[]),(4,[0,1],[1])
                    ]:
                if gkp[0] != g or len(gkp[1]) > len(kappas) or len(gkp[2]) > len(psis):
                    continue
                stop = false
                for j in range(len(gkp[1])):
                    if gkp[1][j] > kappas[j]:
                        stop = true
                        break
                if stop:
                    continue
                for j in range(len(gkp[2])):
                    if gkp[2][j] > psis[j]:
                        stop = true
                        break
                if not stop:
                    hkp.append(i)
                    break
            if not stop:
                break
    return hkp

@func_persist
def get_eche_sym_rels_old(g,n,r,moduli_type):
    print("calculating old relations for g=%s, n=%s, r=%s, moduli type %s" % (g,n,r,moduli_type))
    allrels = derived_rels_SS(g,r,n,moduli_type)
    reldic={}
    for i in range(len(allrels)):
        for j in range(len(allrels[i])):
            reldic[i,allrels[i][j][0]]=allrels[i][j][1]
    mold=Matrix(reldic,sparse=True)
    tg=general_tautgens(g,n,r,moduli_type,0)
    print("echelonizing...")
    mold.echelonize()
    return dzr(mold),tg
    
#display a list of tautological generators with their indices
def list_tg(taut_gens, sub = None):
    if sub == None:
        sub = range(len(taut_gens))
    for i in sub:
        print('['+repr(i)+'] : '+repr(taut_gens[i]))

def partial_to_tautclass(vec,taut_gens):
    terms = []
    for i in range(len(vec)):
        if vec[i] != 0:
            terms.append(taut_gens[i]*vec[i])
    return tautclass(terms)

def nicely_remove_cols(ma,tg,columns,keepcols = None):
    if keepcols == None:
        keepcols = [i for i in range(ma.ncols()) if not i in columns]
    ordered_keep_ma = ma.matrix_from_columns(columns + keepcols)
    ordered_keep_ma.echelonize()
    reduced_ma = ordered_keep_ma.matrix_from_columns(range(len(columns)))
    zeros = [i for i,v in enumerate(reduced_ma.rows()) if v.is_zero()]
    return dzr(ordered_keep_ma.matrix_from_rows_and_columns(zeros,range(len(columns),ordered_keep_ma.ncols())).echelon_form()),[tg[i] for i in keepcols]

def only_monomials(tc):
    terms = []
    for ds in tc.terms:
        for mon in ds.poly:
            terms.append(mon[2]*decstratum(deepcopy(ds.gamma),deepcopy(mon[0]),deepcopy(mon[1])))
    return tautclass(terms)

#assumes only monomials
def order_vertices(tc):
    newterms = []
    for t in tc.terms:
        perm = Word(t.gamma._genera).standard_permutation().inverse()
        t.gamma._genera = [t.gamma._genera[i-1] for i in perm]
        t.gamma._legs = [t.gamma._legs[i-1] for i in perm]
        t.poly.monom = [([t.poly[0][0][i-1] for i in perm],t.poly[0][1])]
        newterms.append(t)
    return tautclass(newterms)

#cleans up a tautclass by mapping to a basis
def clean_tc(tc):
    gnr = tc.gnr_list()
    if gnr == []:
        return tc
    if len(gnr) > 1:
        print("ERROR")
        print(gnr)
        return -1
    g = gnr[0][0]
    n = gnr[0][1]
    r = gnr[0][2]
    return Tautv_to_tautclass(tc.toTautvect(g,n,r),g,n,r)

#delete zero rows from a matrix
def dzr(MA):
    zeros = [i for i,v in enumerate(MA.rows()) if v.is_zero()]
    s = set(zeros)
    nonzeros = [i for i in range(MA.nrows()) if not (i in s)]
    return MA.matrix_from_rows(nonzeros)


######################################################################
# Converting to low psi basis
######################################################################
# this is done by pulling back high degree monomials in psi (and kappa1) along gluing maps

# assumes there are no kappa or a kappa1, also assumes g<=3
# at the moment this only works for rational tail
def converttolowpsibasis(tc,moduli_type = MODULI_RT):
    newterms = []
    for ds in tc.terms:
        newterms += convertdstolpb(ds,moduli_type)
    return tautclass(newterms)

@cached_function
def hashablepsirel(g,n,kap,hashdic,moduli_type):
    return getpsirel(g,n,kap,{i[0]:i[1] for i in hashdic},moduli_type)

def cachedpsirel(g,n,kap,psidic,moduli_type):
    return hashablepsirel(g,n,kap,tuple([(k,psidic[k]) for k in psidic.keys()]),moduli_type)

def getpsirel(g,n,kap,psidic,moduli_type):
    r = sum(psidic.values())+kap
    if r+kap < g:
        print("error: codimension too low")
        return -1
    if dim_form(g,n,moduli_type) < r:
        return tautclass([])
    if kap == 0:
        kaps = [[]]
    else:
        kaps = [[kap]]

    G = Pixtongraph(tautgens(g,n,0)[0].terms[0].gamma,kaps,psidic)
    legdic = {}
    if len(psidic) < n:
        psinr = 1
        for i in range(1,n+1):
            if not i in psidic.keys():
                G.M[0,i] += 1 - i
            else:
                psinr += 1
                G.M[0,i] += psinr - i
                ps = n - len(psidic) + psinr - 1
                if ps == i:
                    continue
                if i in legdic.values() and ps in legdic.keys():
                    print("sderERROORRRRR")
                    return
                if ps in legdic.keys():
                    legdic[i] = legdic[ps]
                    legdic[ps] = i
                    continue
                if i in legdic.values():
                    for k in legdic:
                        if legdic[k] == i:
                            legdic[k] = ps
                    legdic[ps] = i
                    continue
                legdic[i] = ps
                legdic[ps] = i
    nos = num_of_stratum(G,g,r,getmarks(n,len(psidic)),moduli_type)
    fzm = get_eche_fzm_tg(g,n,r,moduli_type,unsym = len(psidic))[0]
    v = (-1)*copy(fzm[nos])
    v[nos] = 0
    if n!=len(psidic):
        w = [[i,v[i]] for i in range(len(v)) if not v[i] == 0]
        w = unsymmetrize_vec_SS(w,g,r,getmarks(n,n),getmarks(n,len(psidic)),moduli_type)
        v = [0 for _ in range(num_strata(g, r, getmarks(n,n), moduli_type))]
        for we in w:
            v[we[0]] = we[1]
    tc = partial_to_tautclass(v,general_tautgens(g,n,r,moduli_type))
    if n==(psidic):
        return tc
    return tc.rename_legs(legdic)

def convertdstolpb(ds,moduli_type):
    result = []
    psidics = list(map(lambda x: x[0][1],ds.split()[0]))
    kappas = list(map(lambda x: sum(x[0][0][0]),ds.split()[0]))
    for i in range(len(psidics)):
        if sum(psidics[i].values()) + kappas[i]*2 >= max(1,ds.gamma.genera(i)):
            pd = {ds.gamma.legs(i).index(k)+1:psidics[i][k] for k in psidics[i].keys()}
            pr = deepcopy(cachedpsirel(ds.gamma.genera(i),len(ds.gamma.legs(i)),kappas[i],pd,moduli_type))
            for t in pr.terms:
                nds = deepcopy(ds)
                nds = nds * t.poly.coeff[0]
                legdic = {j+1:ds.gamma.legs(i)[j] for j in range(len(ds.gamma.legs(i)))}
                for he in t.gamma.halfedges():
                    usednumbers = list(legdic.values()) + list(legdic.keys())
                    if he in usednumbers:
                        legdic.update({he:max(usednumbers)+1})
                t.rename_legs(legdic)
                gluedic = {}
                nds.gamma.glue_vertex(i,t.gamma,dil = gluedic)
                #return nds,gluedic,gluedicv,gluedicGr,t
                t.poly.rename_legs(gluedic)
                newpsidic = copy(nds.poly[0][1])
                for k in psidics[i].keys():
                    del newpsidic[k]
                newpsidic.update(t.poly[0][1])
                kapkap = [nds.poly[0][0][j] for j in range(len(nds.poly[0][0])) if not j==i] + t.poly[0][0]
                nds.poly = kppoly([(kapkap,newpsidic)],[nds.poly[0][2]])
                result = result + convertdstolpb(nds,moduli_type)
            return result
    return [ds]


#########################################################
# general verion of 'is_zero'
#########################################################
# checks if a linear combination of strata is equivalent to zero
# this code is copied from admcycles with only very minor changes in order to accomodate different moduli and symmetry types

#requires input to be in the correct moduli type
def general_is_zero(tc, moduli_type, unsym = None):
    return all(general_toTautbasis(tc,*gnr, moduli_type=moduli_type, unsym = unsym).is_zero() for gnr in tc.gnr_list())


def general_toTautbasis(tc,g,n,r,moduli_type,unsym = None):
    return general_Tautvecttobasis(general_converttoTautvect(tc,g,n,r,moduli_type,unsym),g,n,r,moduli_type,unsym)

def general_converttoTautvect(D,g,n,r,moduli_type,unsym = None):
    if unsym == None:
        unsym = n
    if isinstance(D,tautclass):
        if len(D.terms)==0:
            return vector(QQ,DR.num_strata(g,r,getmarks(n,unsym),moduli_type = moduli_type))
        result = general_converttoTautvect(D.terms[0],g,n,r,moduli_type,unsym)
        for i in range(1, len(D.terms)):
            result+=general_converttoTautvect(D.terms[i],g,n,r,moduli_type,unsym)
        return result
    if isinstance(D,decstratum):
        D.dimension_filter()
        if len(D.poly.monom)==0:
            if (r is None):
                print('Unable to identify r for empty decstratum')
                return 0
            else:
                return vector(QQ,DR.num_strata(g,r,getmarks(n,unsym),moduli_type = moduli_type))
        length=DR.num_strata(g,r,getmarks(n,unsym),moduli_type = moduli_type)
        markings=getmarks(n,unsym)
        result = vector(QQ,length)
        graphdegree = D.gamma.num_edges()
        for (kappa,psi,coeff) in D.poly:
            if graphdegree + sum([sum((j+1)*kvec[j] for j in range(len(kvec))) for kvec in kappa])+sum(psi.values()) == r:
                try:
                    pare=coeff.parent()
                except:
                    pare=QQ
                result+=vector(pare,length,{DR.num_of_stratum(Pixtongraph(D.gamma,kappa,psi),g,r,markings,moduli_type = moduli_type):coeff})
        return result

def general_Tautvecttobasis(v,g,n,r,moduli_type,unsym = None):
  if (2 *g-2 +n<=0) or (r<0) or (r>3 *g-3 +n):
    return vector([])
  vecs=general_genstobasis(g,n,r,moduli_type,unsym)
  res=vector(QQ,len(vecs[0]))
  for i in range(len(v)):
    if v[i]!=0:
      res+=v[i]*vecs[i]
  return res

@cached_function
def general_genstobasis(g, n, r, moduli_type,unsym = None):
    relconv=get_eche_fzm_tg(g,n,r,moduli_type,unsym)[0]
    reverseindices=list(range(relconv.ncols()))
    reverseindices.reverse()
    reordrelconv=relconv.matrix_from_columns(reverseindices)
    del(relconv)
    reordrelconv.echelonize() #(algorithm='classical')
    reordnongens=reordrelconv.pivots()
    nongens=[reordrelconv.ncols()-i-1  for i in reordnongens]
    gens = [i for i in range(reordrelconv.ncols()) if not i in nongens]

    # compute result of genstobasis here, for efficiency reasons
    gtob={gens[j]: vector(QQ,len(gens),{j:1}) for j in range(len(gens))}
    for i in range(len(reordnongens)):
      gtob[nongens[i]]=vector([-reordrelconv[i,reordrelconv.ncols()-j-1]  for j in gens])
    return [gtob[i] for i in range(reordrelconv.ncols())]

###############

def restrict_tautclass(tc,g,n,r,moduli_type):
    if moduli_type == 'st' or moduli_type == 3:
        def modtest(gr):
            return False
    if moduli_type == 'sm' or moduli_type == 0:
        def modtest(gr):
            return bool(gr.num_edges())
    if moduli_type == 'rt' or moduli_type == 1:
        def modtest(gr):
            return g not in gr.genera(copy = False)
    if moduli_type == 'ct' or moduli_type == 2:
        def modtest(gr):
            return gr.num_edges() - gr.num_verts() + 1 != 0
    restrictedterms = []
    for t in tc.terms:
        if not modtest(t.gamma):
            for i in range(len(t.poly.monom)):
                (kappa,psi)=t.poly.monom[i]
                for v in range(t.gamma.num_verts()):
                    if sum([(k+1)*kappa[v][k] for k in range(len(kappa[v]))]) + sum([psi[l] for l in t.gamma.legs(v, copy=False) if l in psi]) > dim_form(t.gamma.genera(v),t.gamma.num_legs(v),moduli_type):
                        t.poly.coeff[i]=0
                        break
            tcon = t.consolidate()
            if tcon.poly.coeff != []:
                restrictedterms.append(tcon)
    return tautclass(restrictedterms)

