# This file contains the computation of tautological relations using partially symmetric relations
# It is based on the code from DR.py that calculates symmetric relations

def kappa_multiple_SS(vec, which_kappa, g, r, n, unsym, moduli_type):
    vec2 = []
    for x in vec:
        for y in single_kappa_multiple_SS(x[0], which_kappa, g, r, n, unsym, moduli_type):
            vec2.append([y[0], x[1]*y[1]])
    vec2 = simplify_sparse(vec2)
    return vec2


def psi_multiple_SS(vec, g, r, n, ncur, unsym, moduli_type):
    vec2 = []
    for x in vec:
        for y in single_psi_multiple_SS(x[0], g, r, n, ncur, unsym, moduli_type):
            vec2.append([y[0], x[1]*y[1]])
    vec2 = simplify_sparse(vec2)
    return vec2

@cached_function
def single_psi_multiple_SS(num, g, r, n, ncur, unsym, moduli_type):
    markings = getmarks(n,unsym)
    G = single_stratum(num, g, r, markings, moduli_type)
    answer = []
    for j in range(1, G.M.ncols()):
        if G.M[0, j] == ncur:
            good_j = j
            break
    for i in range(1, G.M.nrows()):
        if G.M[i, good_j] != 0:
            deg = 0
            dim_used = 0
            for j in range(1, r+1):
                dim_used += j*G.M[i, 0][j]
            for j in range(1, G.M.ncols()):
                dim_used += G.M[i, j][1] + G.M[i, j][2]
                deg += G.M[i, j][0]
            if dim_used < dim_form(G.M[i, 0][0], deg, moduli_type):
                GG = Graph(G.M)
                GG.M[i, good_j] += X
                answer.append(
                    (num_of_stratum(GG, g, r+1, markings, moduli_type), 1))
            break
    return answer


@cached_function
def single_kappa_multiple_SS(num, which_kappa, g, r, n, unsym, moduli_type):
    markings = getmarks(n,unsym)
    G = single_stratum(num, g, r, markings, moduli_type)
    answer = []
    for i in range(1, G.M.nrows()):
        deg = 0
        dim_used = 0
        for j in range(1, r+1):
            dim_used += j*G.M[i, 0][j]
        for j in range(1, G.M.ncols()):
            dim_used += G.M[i, j][1] + G.M[i, j][2]
            deg += G.M[i, j][0]
        if dim_used + which_kappa <= dim_form(G.M[i, 0][0], deg, moduli_type):
            GG = Graph(G.M)
            GG.M[i, 0] += X**which_kappa
            answer.append((num_of_stratum(GG, g, r+which_kappa,
                                          markings, moduli_type), 1))
            for j in range(1, r+1):
                if G.M[i, 0][j] > 0:
                    GG = Graph(G.M)
                    GG.M[i, 0] += X**(j+which_kappa)
                    GG.M[i, 0] -= X**j
                    answer.append((num_of_stratum(
                        GG, g, r+which_kappa, markings, moduli_type), -G.M[i, 0][j]))
    return answer

@func_persist
def interior_derived_rels_SS(g, r, n, unsym, moduli_type):
    answer = copy(pullback_derived_rels_SS(g, r, n, unsym, moduli_type))
    for r0 in range(r):
        us = min(unsym + r-r0,n)
        if us > unsym:
            symm = symmetrize_map_SS(g,r,getmarks(n,us),getmarks(n,unsym),moduli_type)
        pullback_rels = [unsymmetrize_vec_SS(bs,g,r0,getmarks(n,us),getmarks(n,0),moduli_type) for bs in choose_basic_rels_SS(g, r0, n, moduli_type)]
        pullback_rels += copy(pullback_derived_rels_SS(g, r0, n, us, moduli_type))
        for rel in pullback_rels:
            for i in range(r-r0+1):
                for sigma in Partitions(i):
                    for tau in IntegerVectors(r-r0-i, us):
                        rel2 = copy(rel)
                        rcur = r0
                        for m in range(us):
                            for mm in range(tau[m]):
                                rel2 = psi_multiple_SS(
                                    rel2, g, rcur, n, getmarks(n,us)[-m-1], us, moduli_type)
                                rcur += 1
                        for m in sigma:
                            rel2 = kappa_multiple_SS(
                                rel2, m, g, rcur, n, us, moduli_type)
                            rcur += m
                        if us > unsym:
                            rel2 = [[symm[y[0]],y[1]] for y in rel2]
                        answer.append(rel2)
    return answer

def resolve_dic(G,olddic,old,new):
    dic = deepcopy(olddic)
    if new in dic.keys():
        if dic[new] < new:
            GG = Graph(G.M)
            for j in range(1, GG.M.ncols()):
                if GG.M[0, j][0] == dic[new]:
                    GG.M[0,j] += new - GG.M[0,j][0]
                    GG.M[0,old] += dic[new] - GG.M[0,old][0]
                    if dic[dic[new]] == new:
                        return GG
                    dic.update({new:dic[dic[new]]})
                    return resolve_dic(GG,dic,j,new)
    return G

@cached_function
def single_insertion_pullback_SS(num, g, r, n, new_mark, unsym, moduli_type):
    us = min(n-1, unsym)
    markings = getmarks(n,unsym)
    if new_mark == 1:
        new_markings =  getmarks(n+1,unsym)
    else:
        new_markings = getmarks(n+1,unsym+1)
    G = single_stratum(num, g, r, markings, moduli_type)
    answer = []
    for i in range(1, G.M.nrows()):
        GG = Graph(G.M)
        if (new_mark > 1 and new_mark <= us + 1) or (unsym == n and new_mark == 1):
            for j in range(1, G.M.ncols()):
                if GG.M[0, j][0] == new_mark:
                    GG.M[0, j] += us + 2 - GG.M[0, j][0]
                    break
        GG.add_edge(i, 0, min(new_mark,us+2))
        answer.append(
            (num_of_stratum(GG, g, r, new_markings, moduli_type), 1))
        for j in range(1, r+1):
            for k in range(GG.M[i, 0][j]):
                GGG = Graph(GG.M)
                GGG.M[i, 0] -= X**j
                GGG.M[i, -1] += j*X
                answer.append(
                    (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
        if moduli_type <= MODULI_SM:
            continue
        for j in range(1, G.M.ncols()):
            if G.M[i, j][0] == 1:
                if G.M[i, j][1] >= 1:
                    x = G.M[i, j][1]
                    GGG = Graph(GG.M)
                    row1 = [GG.M[i, k] for k in range(GG.M.ncols())]
                    row2 = [0 for k in range(GG.M.ncols())]
                    row1[j] = 0
                    row1[-1] = 0
                    row2[j] = 1
                    row2[-1] = 1
                    GGG.split_vertex(i, row1, row2)
                    GGG.M[-2, -
                          1] += (x-1)*X
                    answer.append(
                        (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
            if G.M[i, j][0] == 2:
                if G.M[i, j][1] >= 1 or G.M[i, j][2] >= 1:
                    x = G.M[i, j][1]
                    y = G.M[i, j][2]
                    row1 = [GG.M[i, k] for k in range(GG.M.ncols())]
                    row2 = [0 for k in range(GG.M.ncols())]
                    row1[j] = 0
                    row1[-1] = 0
                    row2[j] = 1
                    row2[-1] = 1
                    if y >= 1:
                        row1[j] = 1 + x*X
                        GGG = Graph(GG.M)
                        GGG.split_vertex(i, row1, row2)
                        GGG.M[-2, -
                              1] += (y-1)*X
                        answer.append(
                            (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
                    if x >= 1:
                        row1[j] = 1 + y*X
                        GGG = Graph(GG.M)
                        GGG.split_vertex(i, row1, row2)
                        GGG.M[-2, -
                              1] += (x-1)*X
                        answer.append(
                            (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
    return answer

@cached_function
def getmarks(n,unsym):
    if unsym == n:
        return tuple(range(1,n+1))
    return tuple([1 for i in range(n-unsym)]) + tuple(range(2,unsym+2))

@cached_function
def single_insertion_pullback2_SS(num, g, r, n, new_mark, unsym, moduli_type):
    us = min(n-1, unsym)
    markings = getmarks(n,unsym)
    if new_mark == 1:
        new_markings =  getmarks(n+1,unsym)
    else:
        new_markings = getmarks(n+1,unsym+1)
    G = single_stratum(num, g, r, markings, MODULI_SMALL)
    answer = []
    for i in range(1, G.M.nrows()):
        GG = Graph(G.M)
        if (new_mark > 1 and new_mark <= us + 1) or (unsym == n and new_mark == 1):
            for j in range(1, G.M.ncols()):
                if GG.M[0, j][0] == new_mark:
                    GG.M[0, j] += us + 2 - GG.M[0, j][0]
                    break
        GG.add_edge(i, 0, min(new_mark,us+2))
        answer.append(
            (num_of_stratum(GG, g, r, new_markings, moduli_type), 1))
        for j in range(1, r+1):
            for k in range(GG.M[i, 0][j]):
                GGG = Graph(GG.M)
                GGG.M[i, 0] -= X**j
                GGG.M[i, -1] += j*X
                answer.append(
                    (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
        if moduli_type <= MODULI_SM:
            continue
        for j in range(1, G.M.ncols()):
            if G.M[i, j][0] == 1:
                if G.M[i, j][1] >= 1:
                    x = G.M[i, j][1]
                    GGG = Graph(GG.M)
                    row1 = [GG.M[i, k] for k in range(GG.M.ncols())]
                    row2 = [0 for k in range(GG.M.ncols())]
                    row1[j] = 0
                    row1[-1] = 0
                    row2[j] = 1
                    row2[-1] = 1
                    GGG.split_vertex(i, row1, row2)
                    GGG.M[-2, -
                          1] += (x-1)*X
                    answer.append(
                        (num_of_stratum(GGG, g, r, new_markings, moduli_type), -1))
    return answer

#this is less efficient than the DR.py method but translating it more efficiently would probably mean needing more nonsymmetry
def subsequences_SS(n, l, us):
    if n <= us:
        return subsequences(getmarks(n,n),l)
    if l == 0:
        return [[]]
    answer = []
    for ss in range(max(l-us,0),min(l,n-us)+1):
        for uss in Subsets(tuple(range(2,us+2)), l-ss):
            for poss in Subsets(l,l-ss):
                myl = []
                j = 0
                for i in range(1,l+1):
                    if i in poss:
                        myl.append(uss[j])
                        j += 1
                    else:
                        myl.append(1)
                answer.append(myl)
    return answer

@func_persist
def pullback_derived_rels_SS(g, r, n, unsym, moduli_type):
    if r == 0:
        return []
    answer = []
    for n0 in range(n):
        if dim_form(g, n0, moduli_type) >= r:
            basic_rels = choose_basic_rels_SS(g, r, n0, moduli_type)
            for rel in basic_rels:
                for vec in subsequences_SS(n, n-n0, unsym):
                    #prob not most efficient way
                    left = [1 for _ in range(max(n-unsym,1)-vec.count(1))]+[s for s in getmarks(n,unsym) if not (s in vec or s == 1)]
                    #not the difference between curus = n and curus = n-1
                    curus = n0-left.count(1)
                    start = getmarks(n0,curus)
                    dic = {start[i]:left[i] for i in range(n0) if not left[i] == 1}
                    if curus > 0:
                        rel2 = unsymmetrize_vec_SS(rel,g,r,getmarks(n0,curus),getmarks(n0,0),moduli_type)
                    else:
                        rel2 = copy(rel)
                    for i in range(n-n0):
                        rel2, dic = insertion_pullback_SS(
                            rel2, g, r, n0+i, vec[i], dic, curus, moduli_type)
                        if vec[i] > 1:
                            curus += 1
                    answer.append(rel2)
        else:
            basic_rels = choose_basic_rels_SS(g, r, n0, MODULI_SMALL)
            k = r - dim_form(g, n0, moduli_type)
            for rel in basic_rels:
                for vec2 in subsequences_SS(n, n-n0-k+1, unsym):
                    left2 = [1 for _ in range(max(n-unsym,1)-vec2.count(1))]+[s for s in getmarks(n,unsym) if not (s in vec2 or s == 1)]
                    curus2 = n0+k-1-left2.count(1)
                    start2 = getmarks(n0+k-1,curus2)
                    dic2 = {start2[i]:left2[i] for i in range(n0+k-1) if not left2[i] == 1}
                    usk = curus2
                    for vec in subsequences_SS(n0+k-1, k-1, usk):
                        left = [1 for _ in range(max(n0+k-1-usk,1)-vec.count(1))]+[s for s in getmarks(n0+k-1,usk) if not (s in vec or s == 1)]
                        curus = n0-left.count(1)
                        start = getmarks(n0+k-1,curus)
                        dic = {start[i]:left[i] for i in range(n0) if not left[i] == 1}
                        if curus > 0:
                            rel2 = unsymmetrize_vec_SS(rel,g,r,getmarks(n0,curus),getmarks(n0,0),MODULI_SMALL)
                        else:
                            rel2 = copy(rel)
                        for i in range(k-1):
                            rel2, dic = insertion_pullback_SS(
                                rel2, g, r, n0+i, vec[i], dic, curus, MODULI_SMALL)
                            if vec[i] > 1:
                                curus += 1
                        curus = curus2
                        rel2, dic2 = insertion_pullback2_SS(
                            rel2, g, r, n0+k-1, vec2[0], dic2, curus, moduli_type)
                        if vec2[0] > 1:
                            curus += 1
                        for i in range(n-n0-k):
                            rel2, dic2 = insertion_pullback_SS(
                                rel2, g, r, n0+k+i, vec2[i+1], dic2, curus, moduli_type)
                            if vec2[i+1] > 1:
                                curus += 1
                        answer.append(rel2)
    return answer

def swap_pts(num, g, r, n, dic, unsym, moduli_type):
    markings = getmarks(n,unsym)
    G = single_stratum(num, g, r, markings, moduli_type)
    for i in range(1, G.M.nrows()):
        GG = Graph(G.M)
        for j in range(1, G.M.ncols()):
            if GG.M[0, j][0] == unsym + 1:
                GG = resolve_dic(GG,dic,j,unsym + 1) 
                return num_of_stratum(GG, g, r, markings, moduli_type)
    print("ERRRRRRRRRRRRORRRRRRRRRSSS")

@cached_function
def hashableswap(num, g, r, n, hashdic, unsym, moduli_type):
    return swap_pts(num, g, r, n, {i[0]:i[1] for i in hashdic}, unsym, moduli_type)

def cachedswap(num, g, r, n, dic, unsym, moduli_type):
    return hashableswap(num, g, r, n, tuple([(k,dic[k]) for k in dic.keys()]), unsym, moduli_type)

def insertion_pullback_SS(vec, g, r, n, new_mark, dic, unsym, moduli_type):
    us = min(unsym, n-1)
    vec2 = []
    for x in vec:
        for y in single_insertion_pullback_SS(x[0], g, r, n, new_mark, unsym, moduli_type):
            vec2.append([y[0], x[1]*y[1]])
    vec2 = simplify_sparse(vec2)
    if new_mark > us + 2:
        dic.update({us+2:new_mark})
    if new_mark in dic.keys():
        dic.update({us+2:dic[new_mark]})
        del(dic[new_mark])
        vec2 = [[cachedswap(x[0],g,r,n+1,dic,min(unsym+1-(new_mark==1),n),moduli_type),x[1]] for x in vec2]        
    return vec2, dic 

def insertion_pullback2_SS(vec, g, r, n, new_mark, dic, unsym, moduli_type):
    us = min(unsym, n-1)
    vec2 = []
    for x in vec:
        for y in single_insertion_pullback2_SS(x[0], g, r, n, new_mark, unsym, moduli_type):
            vec2.append([y[0], x[1]*y[1]])
    vec2 = simplify_sparse(vec2)
    if new_mark > us + 2:
        dic.update({us+2:new_mark})
    if new_mark in dic.keys():
        dic.update({us+2:dic[new_mark]})
        del(dic[new_mark])
        vec2 = [[cachedswap(x[0],g,r,n+1,dic,min(unsym+1-(new_mark==1),n),moduli_type),x[1]] for x in vec2]        
    return vec2, dic 

@cached_function
def symmetrize_map_SS(g, r, markings, symmedmarkings, moduli_type):
    gens = all_strata(g, r, markings, moduli_type)
    dif = markings.count(1) - 2
    mymap = []
    for G in gens:
        GG = Graph(G.M)
        for i in range(1, GG.M.ncols()):
            if GG.M[0, i][0] > 0:
                GG.M[0, i] = R(symmedmarkings[GG.M[0, i][0]+dif])
        mymap.append(num_of_stratum(GG, g, r, symmedmarkings, moduli_type))
    return mymap

@cached_function
def unsymmetrize_map_SS(g, r, markings, symmedmarkings, moduli_type):
    m1s = markings.count(1)
    ms1s = symmedmarkings.count(1)
    mn = len(markings)
    if ms1s == m1s:
        print("why is this even happening?")
        return -1
    if m1s + 1 < ms1s:
        return [unsymmetrize_vec_SS(us, g, r, markings,getmarks(mn,mn - m1s - 1), moduli_type) for us in unsymmetrize_map_SS(g,r,getmarks(mn,mn - m1s - 1),symmedmarkings,moduli_type)]
    gens = all_strata(g, r, markings, moduli_type)
    sym_map = symmetrize_map_SS(g, r, markings, symmedmarkings, moduli_type)
    mymap = [[] for i in range(num_strata(g, r, symmedmarkings, moduli_type))]
    usd = {}
    for i in range(len(gens)):
        if i in usd.keys():
            continue
        usd[i] = 1
        G = gens[i]
        for j in range(1, G.M.ncols()):
            if G.M[0,j][0] == 2:
                pt2 = j
                break
        for j in range(1, G.M.ncols()):
            if G.M[0,j][0] == 1:
                GG = Graph(G.M)
                GG.M[0,j] += 1
                GG.M[0,pt2] -= 1
                num = num_of_stratum(GG,g,r,markings,moduli_type)
                if num in usd.keys():
                    usd[num] = usd[num] + 1
                else:
                    usd[num] = 1
    for k in usd.keys():
        mymap[sym_map[k]].append([k,usd[k]])
    return mymap

def unsymmetrize_vec_SS(vec, g, r, markings, symmedmarkings, moduli_type):
    if markings == symmedmarkings:
        return vec
    unsym_map = unsymmetrize_map_SS(g, r, markings, symmedmarkings, moduli_type)
    vec2 = []
    for x in vec:
        aut = 0
        for j in unsym_map[x[0]]:
            aut += j[1]
        for j in unsym_map[x[0]]:
            vec2.append([j[0], QQ(x[1]*j[1]/aut)])
    vec2 = simplify_sparse(vec2)
    return vec2

@func_persist
def choose_basic_rels_SS(g, r, n, moduli_type):
    if 3 * r < g + n + 1:
        return []
    sym_ngen = num_strata(g, r, tuple([1 for i in range(n)]), moduli_type)
    if moduli_type == MODULI_SMALL and r > dim_form(g, n, MODULI_SM):
        sym_possible_rels = [[[i, 1]] for i in range(sym_ngen)]
    else:
        sym_possible_rels = possibly_new_FZ(g, r, n, moduli_type)
    if not sym_possible_rels:
        return []
    previous_rels = derived_rels_SS(g, r, n, 0, moduli_type)
    nrels = len(previous_rels)
    D = {}
    for i in range(nrels):
        for x in previous_rels[i]:
            D[i, x[0]] = x[1]
    if nrels > 0:
        row_order, col_order = choose_orders_sparse(D, nrels, sym_ngen)
        previous_rank = compute_rank_sparse(D, row_order, col_order)
    else:
        previous_rank = 0
        row_order = []
        col_order = list(range(sym_ngen))
    answer = []
    for j in range(len(sym_possible_rels)):
        for x in sym_possible_rels[j]:
            D[nrels, x[0]] = x[1]
        row_order.append(nrels)
        nrels += 1
        if compute_rank_sparse(D, row_order, col_order) > previous_rank:
            answer.append(sym_possible_rels[j])
            previous_rank += 1
#    if moduli_type > -1:
#        dsave("sparse-%s,%s,%s,%s|%s,%s,%s", g, r, n, moduli_type,
#              len(answer), sym_ngen-previous_rank, floor(get_memory_usage()))
    return answer


@func_persist
def derived_rels_SS(g, r, n, unsym, moduli_type):
    markings = getmarks(n,unsym)
    answer = [simplify_sparse(ss) for ss in deepcopy(interior_derived_rels_SS(g, r, n, unsym, moduli_type))]
    if moduli_type <= MODULI_SM:
        return answer
    for r0 in range(1, r):
        strata = all_strata(g, r0, markings, moduli_type)
        for G in strata:
            vertex_orbits = graph_count_automorphisms(G, True)
            for i in [orbit[0] for orbit in vertex_orbits]:
                good = True
                for j in range(G.M.ncols()):
                    if R(G.M[i, j][0]) != G.M[i, j]:
                        good = False
                        break
                if good:
                    g2 = G.M[i, 0][0]
                    if 3 * (r - r0) < g2 + 1:
                        continue
                    d = G.degree(i)
                    if dim_form(g2, d, moduli_type) < r-r0:
                        continue
                    strata2 = all_strata(
                        g2, r-r0, getmarks(d,d), moduli_type)
                    which_gen_list = [
                        -1 for num in range(len(strata2))]
                    for num in range(len(strata2)):
                        G_copy = Graph(G.M)
                        G_copy.replace_vertex_with_graph(i, strata2[num])
                        which_gen_list[num] = num_of_stratum(
                            G_copy, g, r, markings, moduli_type)
                    rel_list = [unsymmetrize_vec_SS(bs,g2,r-r0,getmarks(d,d),getmarks(d,0),moduli_type) for bs in choose_basic_rels_SS(g2, r-r0, d, moduli_type)]
                    rel_list += copy(interior_derived_rels_SS(g2, r-r0, d, d, moduli_type))
                    for rel0 in rel_list:
                        relation = []
                        for x0, x1 in rel0:
                            if which_gen_list[x0] != -1:
                                relation.append([which_gen_list[x0], x1])
                        relation = simplify_sparse(relation)
                        answer.append(relation)
    answer = remove_duplicates(answer)
    return answer

#####################################################
# unsymmetrizing from completely symmetric
#####################################################
# unlike unsymmetrize_vec approach this does not require one to calculate all strata

def unsym_graph(Gr,n):
    G = Graph(Gr.M)
    for i in range(1,n+1):
        if G.M[0,i] != 1:
            G.M[0,i] += 1 - G.M[0,i]
    dislis = []
    for i in range(1,G.M.nrows()):
        vlis = []
        psil = []
        for j in range(1,n+1):
            if G.M[i,j] == 1:
                vlis.append(j)
                continue
            if G.M[i,j] != 0:
                psil.append([G.M[i,j].coefficients()[1],j])
        if vlis != []:
            dislis.append(vlis)
        if psil != []:
            psil.sort()
            cur = psil[0][0]
            pl = []
            for p in psil:
                if cur != p[0]:
                    dislis.append(pl)
                    pl = [] 
                    cur = p[0]
                pl.append(p[1])
            dislis.append(pl)
    dic = {}
    unsym_cases(dic,list(range(1,n+1)),[],0,dislis,G,n)
    result = []
    for v in dic.values():
        for w in v:
            result.append(w.M)
    return result

def unsym_cases(dic,legsleft,legschosen,ind,legdis,G,n):
    if ind == len(legdis):
        GG = Graph(G.M)
        ldi1 = 0
        for i in range(1,GG.M.nrows()):
            entries = list({GG.M[i,j] for j in range(1,n+1) if not GG.M[i,j] == 0})
            entries.sort()
            for e in entries:
                ldi2 = 0
                for j in range(1,n+1):
                    if GG.M[i,j] == e:
                        GG.M[0,j] += legschosen[ldi1][ldi2]-1
                        ldi2 += 1
                ldi1 += 1
        GG.compute_invariant()
        if GG.invariant in dic.keys():
            for x in dic[GG.invariant]:
                if graph_isomorphic(x,GG):
                    return
            dic[GG.invariant] = dic[GG.invariant] + [GG]
            return
        dic[GG.invariant] = [GG]
        return       
    for comb in Combinations(legsleft,len(legdis[ind])):
        newlegsleft = [ll for ll in legsleft if not ll in comb]
        newlegschosen = deepcopy(legschosen)
        newlegschosen.append(comb)
        unsym_cases(dic,newlegsleft,newlegschosen,ind+1,legdis,G,n)

def smarter_unsym_tc(tc,n):
    dslist = []
    for t in tc.terms:
        ug = unsym_graph(admcycles.Pixtongraph(t.gamma,t.poly[0][0],t.poly[0][1]),n)
        aut = len(ug)
        for m in ug:
            dslist.append(Graphtodecstratum(Graph(m))*QQ(t.poly[0][2]/aut))
    return tautclass(dslist)
