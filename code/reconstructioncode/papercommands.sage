########################################################
# reconstruction in genus 2
########################################################

### get the primitive part of the relations in partially symmetric form (as displayed in the paper)

#symmetric in all points besides 2
def getprimsymmL24():
    prim = get_primitive_part_fzm(2,4,3,1)
    return 3*partial_to_tautclass(prim[0][0]-prim[0][3]-prim[0][5],prim[1]).rename_legs({2:4,4:2})

#symmetric in all points besides 1 and 2
def getprimsymmL25():
    prim = get_primitive_part_fzm(2,5,3,2)
    return partial_to_tautclass(2*prim[0][0]-2*prim[0][1]+prim[0][7]-prim[0][9]-2*prim[0][10]+prim[0][16]+prim[0][17]-2*prim[0][18]-prim[0][24]-3*prim[0][25]-prim[0][30]+2*prim[0][31],prim[1]).rename_legs({1:4,2:5,4:1,5:2}) 

#completely symmetric
def getprimsymmL26():
    prim = get_primitive_part_fzm(2,6,3,0)
    return -2*partial_to_tautclass(prim[0][4],prim[1])

### get the primitive part of the relations in nonsymmetric form

def getprimL24():
    prim = get_primitive_part_fzm(2,4,3)
    return partial_to_tautclass(prim[0][0]-prim[0][4],prim[1])

def getprimL25():
    prim = get_primitive_part_fzm(2,5,3)
    return -(1/3)*partial_to_tautclass(prim[0][58],prim[1])

def getL26symbol():
    return 60*symbol_from_tautclass(2,get_unsymmetric_row(2,6,3,4,0,1,false))

### the matrices we use in the proof of the genus 2 reconstruction theorem

def construct_matrix_a():
    fdm = consider_fixed_deg_matrix([getL26symbol()],[[aa*aa,W,W,W,W,W]],1,6,1,lambda x:x.applydivisor())
    RRR.<i> = PolynomialRing(ZZ,1)
    m = fdm[0].stack(matrix([[0,0,0,24],[6*(i^2-i-4),4*i*(i+2),-(i+1)*(i+2),0]]))
    return m, fdm[1]

def construct_matrix_ab():
    fdm = consider_fixed_deg_matrix([getL26symbol()],[[aa*aa,bb,W,W,W,W]],2,6,2,lambda x:x.applydivisor().kill_double_W())
    RRR.<i> = PolynomialRing(ZZ,1)
    m = fdm[0].stack(matrix([[0,0,0,0,0,0,-6,12,12,6],[6*((i+1)^2-(i+1)-4),0,4*(i+1)*(i+3),0,0,-(i+2)*(i+3),0,0,0,0],[0,6*(i^2-i-4),0,0,4*i*(i+2),0,0,0,-(i+1)*(i+2),0]]))
    return m, fdm[1]

def construct_matrix_abc():
    fdm = consider_fixed_deg_matrix([getL26symbol()],[[aa*aa,bb,cc,W,W,W]],2,6,3,lambda x:x.applydivisor().kill_isolated_W())
    RRR.<i> = PolynomialRing(ZZ,1)
    m = fdm[0].matrix_from_rows(range(8)).stack(matrix([[4*i*(i+1)*(i+2)/(i+3),6*(i^2-i-4),0,4*i*(i+2),0,0,-(i+1)*(i+2),0,0,0],[4*i*(i+1)*(i+2)/(i+3),0,6*(i^2-i-4),0,0,4*i*(i+2),0,0,0,-(i+1)*(i+2)]]))
    return m, fdm[1]

def calculate_matrix_ab_Psi1():
    return consider_fixed_deg_matrix([getL26symbol()],[[aa,bb,W,W,W,W]],1,6,2,lambda x:x.applydivisor().kill_double_W())

def calculate_matrix_abc_Psi1():
    return consider_fixed_deg_matrix([getL26symbol()],[[aa,bb,cc,W,W,W]],1,6,3,lambda x:x.applydivisor().kill_isolated_W())

### the determinants of the matrices

def calculate_discriminant_a():
    return factor(construct_matrix_a()[0].determinant())
def calculate_discriminant_ab():
    return factor(construct_matrix_ab()[0].determinant())
def calculate_discriminant_abc():
    return factor(construct_matrix_abc()[0].determinant())


########################################################################################
# full genus 2 relations (so not just the primitive part)
########################################################################################

def getL24(moduli_type):
    fzm, tg = rem_kappapsi_fzm(2,4,3,moduli_type)
    pi = get_primitive_indices(2,4,3,tg)
    cols = pi + [i for i in range(len(tg)) if not i in pi]
    fzm = fzm.matrix_from_columns(cols).echelon_form()
    return partial_to_tautclass(fzm[0]-fzm[4],[tg[i] for i in cols])

def getLbp(moduli_type):
    return clean_tc(getL24(moduli_type).rename_legs({2:4,4:2}).forgetful_pushforward([4]))

def getL25(moduli_type):
    fzm, tg = rem_kappapsi_fzm(2,5,3,moduli_type)
    pi = get_primitive_indices(2,5,3,tg)
    cols = pi + [i for i in range(len(tg)) if not i in pi]
    fzm = fzm.matrix_from_columns(cols).echelon_form()
    return -(1/3)*partial_to_tautclass(fzm[58],[tg[i] for i in cols])

def getL26sym(moduli_type):
    fzm, tg = rem_kappapsi_fzm(2,6,3,moduli_type,0)
    pi = get_primitive_indices(2,6,3,tg)
    cols = pi + [i for i in range(len(tg)) if not i in pi]
    fzm = fzm.matrix_from_columns(cols).echelon_form()
    return -2*partial_to_tautclass(fzm[4],[tg[i] for i in cols])

def getL26(moduli_type):
    return smarter_unsym_tc(getL26sym(moduli_type),6)


    
