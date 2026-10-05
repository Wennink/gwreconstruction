
def get_primitive_indices(g,n,r,taut_gens):
    pi = []
    for i in range(len(taut_gens)):
        gens = taut_gens[i].gamma.genera()
        if not g in gens:
            continue
        primlegs = [len(taut_gens[i].gamma.legs(j)) for j in range(len(gens)) if gens[j] == g][0]
        if primlegs - taut_gens[i].poly.deg() >= n-r:
            pi.append(i)
    return pi

@func_persist
def get_primitive_part_new_representatives(g,n,r):
    mold, tg = get_eche_sym_rels_old(g,n,r,1)
    hkp = highkappapsi(g,tg)
    mold, tg = nicely_remove_cols(mold,tg,hkp)
    pi = get_primitive_indices(g,n,r,tg)
    mold = dzr(mold.matrix_from_columns(pi))
    fzm, tg = get_primitive_part_fzm(g,n,r,false)
    oldrank = mold.rank()
    newrows = []
    for i in range(fzm.nrows()):
        mm = deepcopy(mold).stack(fzm.row(i))
        if mm.rank() != oldrank:
            newrows.append(i)
    return fzm.matrix_from_rows(newrows),tg

@func_persist
def get_primitive_part_fzm(g,n,r,unsym = None):
    fzm , tg = rem_kappapsi_fzm(g,n,r,1,unsym)
    pi = get_primitive_indices(g,n,r,tg)
    fzm = fzm.matrix_from_columns(pi)
    tg = [tg[i] for i in pi]
    fzm.echelonize()
    fzm = dzr(fzm)
    return fzm,tg

def get_deg_part_fzm(g,n,r,mindeg,maxdeg,unsym = None):
    fzm,tg = get_primitive_part_fzm(g,n,r,unsym)
    if mindeg == 0 and maxdeg >= g:
        return fzm,tg
    indices = []
    highindices = []
    for i in range(len(tg)):
        kpdeg = tg[i].poly.deg()
        if kpdeg >= mindeg:
            if kpdeg > maxdeg:
                highindices.append(i)
            else:
                indices.append(i)
    return nicely_remove_cols(fzm,tg,highindices,indices)

@func_persist
def get_unsymmetric_row(g,n,r,row,mindeg,maxdeg,nonsymbol):
    print("unsymmetrizing row ",row)
    if nonsymbol:
        ta = rem_kappapsi_fzm(g,n,r,1,0)
    else:
        ta = get_deg_part_fzm(g,n,r,mindeg,maxdeg,0)
    tc = partial_to_tautclass(ta[0][row],ta[1])
    return smarter_unsym_tc(tc,n)

def get_symbols(g,n,r,mindeg,maxdeg,unsym = None):
    ss = []
    m = get_deg_part_fzm(g,n,r,mindeg,maxdeg,unsym)
    for i in range(m[0].nrows()):
        if unsym == 0:
            tc = get_unsymmetric_row(g,n,r,i,mindeg,maxdeg,false)
        else:
            tc = partial_to_tautclass(m[0][i],m[1])
        ss.append(symbol_from_tautclass(g,tc))
    return ss

def echelonize_symbols(symbols):
    m,le = make_matrix(symbols)
    m.echelonize()
    m = dzr(m)
    ss = []
    for v in m.rows():
        ss.append(vec_to_symbol(v,le))
    return ss

## the inputs of consider_fixed_deg_matrix are:
# a list of symbols
# a list of lists of cohomology classes
# a degree 'deg'
# a range 'ran'
# a symmetry value that denotes after which point the cohomology classes are all the same
# and a truncation function
## the output is generated as follows:
# the first 'ran' cohomology classes are multiplied by omega (W) classes of total degree 'deg' and inserted into a symbol
# this is done for all symbols, all lists of cohomology classes, and all distributions of 'deg' omega (W) classes among the first 'ran' points
# the output is a matrix containing all these relations as rows together with a legend that lists the invariants corresponding to the columns
def consider_fixed_deg_matrix(symbols,subar,deg,ran,sympt,truncfunc = lambda x:x):
    subs = []
    for subb in subar:
        for iv in symiv(deg,ran,sympt):
            s = deepcopy(subb)
            for i in range(ran):
                s[i] *= W^iv[i]
            subs.append(s)
    subbedsymbols = [truncfunc(s.subs(sub)) for s in symbols for sub in subs]
    return make_matrix(subbedsymbols)

def get_legend(symbols):
    terms = []
    for s in symbols:
        st = deepcopy(s.terms)
        for t in st:
            t[1] = 1
        terms += st
    tst = symbol(terms).terms
    return [i[0] for i in tst]

def make_matrix(symbols):
    legend = get_legend(symbols)
    rows =[]
    for s in symbols:
        lnr = 0
        v = vector(QQ,len(legend))
        for t in s.terms:
            while t[0] != legend[lnr]:
                lnr += 1
            v[lnr] = t[1]
            if lnr > len(legend):
                print("ERRORRRRRRRRRRRRR")
        rows.append(v)
    return matrix(rows),legend
    
def symiv(d,r,sympt):
    result = []
    for iv in IntegerVectors(d,r):
        passable = true
        for i in range(sympt,r-1):
            if iv[i] < iv[i+1]:
                passable = false
                break
        if passable:
            result.append(iv)
    return result

def vec_to_symbol(v,legend):
    tt = []
    for i in range(len(v)):
        if v[i] != 0:
            tt.append([deepcopy(legend[i]),v[i]])
    return symbol(tt)
