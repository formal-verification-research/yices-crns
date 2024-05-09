from yices import *
real_t = Types.real_type()
int_t = Types.int_type()
bool_t = Types.bool_type()

# number of bits to represent values
BITS = 8 # 2^8 --> we have a range from 0 to 255
bv_t = Types.bv_type(BITS)

class Unroller(object):
    # def __init__(self, state_vars, nexts, inputs):
    def __init__(self, state_vars, nexts):    
        self.state_vars = state_vars
        self.nexts = nexts
        # self.inputs = inputs
        self.var_cache = dict()
        self.time_cache = []
    def at_time(self, term, k):
        cache = self._get_cache_at_time(k)
        term_k = Terms.subst(cache.keys(), cache.values(), term)
        return term_k
    def get_var(self, v , k):
        if (v, k) not in self.var_cache:
            v_k = Terms.new_uninterpreted_term(Terms.type_of_term(v),
                                               Terms.to_string(v) + "@" + str(k))
            self.var_cache[(v, k)] = v_k
        return self.var_cache[(v, k)]
    def _get_cache_at_time(self, k):
        assert(k >= 0)
        while len(self.time_cache) <= k:
            cache = dict()
            t = len(self.time_cache)
            for s in self.state_vars:
                s_t = self.get_var(s, t)
                n_t = self.get_var(s, t+1)
                cache[s] = s_t
                cache[self.nexts[s]] = n_t
            # for i in self.inputs:
            #     i_t = Terms.new_uninterpreted_term(Terms.type_of_term(i),
            #                                     Terms.to_string(i) + "@" + str(t))
            #     cache[i] = i_t
            self.time_cache.append(cache)
        return self.time_cache[k]

def val_term(v):
    #return Terms.integer(v)
    return Terms.bvconst_integer(BITS, v)

zero = val_term(0)
one = val_term(1)

def add_term(a, b):
    #return Terms.add(a, b)
    return Terms.bvadd(a, b)

def sub_term(a, b):
    #return Terms.sub(a, b)
    return Terms.bvsub(a, b)

def eq_term(a, b):
    #return Terms.eq(a, b)
    return Terms.bveq_atom(a, b)

def geq_term(a, b):
    #return Terms.arith_geq_atom(a, b)
    return Terms.bvge_atom(a, b)

# type
ty = bv_t
# state variables
R = Terms.new_uninterpreted_term(ty, 'R')
L = Terms.new_uninterpreted_term(ty, 'L')
RL = Terms.new_uninterpreted_term(ty, 'RL')
G = Terms.new_uninterpreted_term(ty, 'G')
GA = Terms.new_uninterpreted_term(ty, 'GA')
GBG = Terms.new_uninterpreted_term(ty, 'GBG')
GD = Terms.new_uninterpreted_term(ty, 'GD')
state_vars = [R, L, RL, G, GA, GBG, GD]
Rnext = Terms.new_uninterpreted_term(ty, 'Rnext')
Lnext = Terms.new_uninterpreted_term(ty, 'Lnext')
RLnext = Terms.new_uninterpreted_term(ty, 'RLnext')
Gnext = Terms.new_uninterpreted_term(ty, 'Gnext')
GAnext = Terms.new_uninterpreted_term(ty, 'GAnext')
GBGnext = Terms.new_uninterpreted_term(ty, 'GBGnext')
GDnext = Terms.new_uninterpreted_term(ty, 'GDnext')
nexts = dict()
nexts[R] = Rnext
nexts[L] = Lnext
nexts[RL] = RLnext
nexts[G] = Gnext
nexts[GA] = GAnext
nexts[GBG] = GBGnext
nexts[GD] = GDnext
# g1 = Terms.new_uninterpreted_term(bool_t, 'g1')
# g8 = Terms.new_uninterpreted_term(bool_t, 'g8')
# choice = [g1, g8]
def frame_cond(vars):
    res = Terms.true()
    for v in vars:
        res = Terms.yand([res, eq_term(nexts[v], v)])
    return res
# initial condition
INIT = Terms.yand([eq_term(R, val_term(50)),
                   eq_term(L, val_term(2)),
                   eq_term(RL, val_term(0)),
                   eq_term(G, val_term(50)),
                   eq_term(GA, val_term(0)),
                   eq_term(GBG, val_term(0)),
                   eq_term(GD, val_term(0))
                   ])
# INIT = Terms.yand([eq_term(R, Terms.rational(5, 1)),
#                    eq_term(L, Terms.rational(2, 1)),
#                    eq_term(RL, Terms.rational(0, 1)),
#                    eq_term(G, Terms.rational(5, 1)),
#                    eq_term(GA, Terms.rational(0, 1)),
#                    eq_term(GBG, Terms.rational(0, 1)),
#                    eq_term(GD, Terms.rational(0, 1))
#                    ])
R1 = Terms.yand([eq_term(nexts[R], add_term(R, one)), frame_cond([L, RL, G, GA, GBG, GD])])
R2 = Terms.yand([geq_term(R, one),
                   Terms.yand([eq_term(nexts[R], sub_term(R, one)), 
                               frame_cond([L, RL, G, GA, GBG, GD])])])
R3 = Terms.yand([Terms.yand([geq_term(L, one), geq_term(R, one)]),
                   Terms.yand([eq_term(nexts[R], sub_term(R, one)), 
                               eq_term(nexts[RL], add_term(RL, one)),     
                               frame_cond([L, G, GA, GBG, GD])])])
R4 = Terms.yand([geq_term(RL, one),
                   Terms.yand([eq_term(nexts[RL], sub_term(RL, one)), eq_term(nexts[R], add_term(R, one)),
                               frame_cond([L, G, GA, GBG, GD])])])
R5 = Terms.yand([Terms.yand([geq_term(RL, one), geq_term(G, one)]),
                   Terms.yand([eq_term(nexts[RL], sub_term(RL, one)), eq_term(nexts[G], sub_term(G, one)),
                               eq_term(nexts[GA], add_term(GA, one)), eq_term(nexts[GBG], add_term(GBG, one)),
                               frame_cond([R, L, GD])])])
R6 = Terms.yand([geq_term(GA, one),
                   Terms.yand([eq_term(nexts[GA], sub_term(GA, one)),
                               eq_term(nexts[GD], add_term(GD, one)),
                               frame_cond([R, L, RL, G, GBG])])])
R7 = Terms.yand([Terms.yand([geq_term(GD, one), geq_term(GBG, one)]),
                   Terms.yand([eq_term(nexts[GD], sub_term(GD, one)), eq_term(nexts[GBG], sub_term(GBG, one)),
                               eq_term(nexts[G], add_term(G, one)), 
                               frame_cond([R, L, RL, GA])])])
R8 = Terms.yand([eq_term(nexts[RL], add_term(RL, one)), frame_cond([R, L, G, GA, GBG, GD])])

# TRANS = Terms.yand([
#                     # Terms.yor([R1, R2]),
#                     # Terms.yor([R2, R4]),
#                     # Terms.yor([R3, R1]),
#                     # Terms.yor([R3, R4]),
#                     # Terms.yor([R4, R8])#,
#                     Terms.yor([R5, R8]),
#                     # Terms.yor([R5, R3]),
#                     # Terms.yor([R5, R7]),
#                     # Terms.yor([R5, R6]),
#                     # Terms.yor([R6, R7])
# ])

### Problematic Trans below ###
TRANS = Terms.yand([
                    Terms.yor([R1, R2]),
                    Terms.yor([R2, R4]),
                    Terms.yor([R3, R1]),
                    Terms.yor([R3, R4]),
                    Terms.yor([R4, R8]),
                    Terms.yor([R5, R8])#,
                    # Terms.yor([R5, R3]),
                    # Terms.yor([R5, R7]),
                    # Terms.yor([R5, R6]),
                  # Terms.yor([R6, R7])
])
# Pairs of reactions that cannot happen simultaneously: (R1, R2), (R2, R4), (R3, R1), (R3, R4), (R4, R8), (R5, R8), (R5, R3), (R5, R7), (R5, R6), (R6, R7)
GOAL = geq_term(GBG, val_term(50))
# GOAL = geq_term(GBG, Terms.rational(5, 1))
print("INIT := " + Terms.to_string(INIT))
print("TRANS := " + Terms.to_string(TRANS))
print("GOAL := " + Terms.to_string(GOAL))
#unroller
# unroller = Unroller(state_vars, nexts, choice)
unroller = Unroller(state_vars, nexts)
formula = Terms.yand([unroller.at_time(INIT, 0),
                      unroller.at_time(TRANS, 0),
                      unroller.at_time(GOAL, 1)])
print(Terms.to_string(formula))

# initialize yices context
cfg = Config()
#cfg.default_config_for_logic('QF_LIA')
#cfg.set_config("mode", "multi-checks")
yices_ctx = Context(cfg)

formula = unroller.at_time(INIT, 0)
# assert formula in the yices context
yices_ctx.assert_formula(formula)
status = yices_ctx.check_context()
if status == Status.ERROR:
    print("unknown")
if status == Status.UNKNOWN:
    print("unknown")
if status == Status.UNSAT:
    print("unsat")
if status == Status.SAT:
    print("sat")
k = 0
while True:
    print("-- TIME %3d --" % (k))
    # for assuming a goal at time k
    assump = Terms.new_uninterpreted_term(bool_t)
    #yices_ctx.push()
    yices_ctx.assert_formula(Terms.implies(assump,
                                           unroller.at_time(GOAL, k)))
    # check
    status = yices_ctx.check_context_with_assumptions(None, [assump])
    #status = yices_ctx.check_context()
    if status == Status.SAT:
        # remember the whole formula
        formula = Terms.yand([formula, unroller.at_time(GOAL, k)])
        model = Model.from_context(yices_ctx, True)
        model_string = model.to_string(80, k * 4, 0)
        print(model_string)
        print(Terms.to_string(formula))
        break
    else:
        #yices_ctx.pop()
        # forgetting goal at time k
        yices_ctx.assert_formula(Terms.ynot(assump))
        yices_ctx.assert_formula(unroller.at_time(TRANS, k))
        status = yices_ctx.status()
        if status == Status.ERROR:
            print("unknown")
        if status == Status.UNKNOWN:
            print("unknown")
        if status == Status.UNSAT:
            print("unsat")
        if status == Status.SAT:
            print("sat")
        formula = Terms.yand([formula, unroller.at_time(TRANS, k)])
        k = k + 1
