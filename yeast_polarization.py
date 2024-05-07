from yices import *
real_t = Types.real_type()
int_t = Types.int_type()
bool_t = Types.bool_type()
zero = Terms.rational(0, 1)
one = Terms.rational(1, 1)

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

# state variables
R = Terms.new_uninterpreted_term(int_t, 'R')
L = Terms.new_uninterpreted_term(int_t, 'L')
RL = Terms.new_uninterpreted_term(int_t, 'RL')
G = Terms.new_uninterpreted_term(int_t, 'G')
GA = Terms.new_uninterpreted_term(int_t, 'GA')
GBG = Terms.new_uninterpreted_term(int_t, 'GBG')
GD = Terms.new_uninterpreted_term(int_t, 'GD')
state_vars = [R, L, RL, G, GA, GBG, GD]
Rnext = Terms.new_uninterpreted_term(int_t, 'Rnext')
Lnext = Terms.new_uninterpreted_term(int_t, 'Lnext')
RLnext = Terms.new_uninterpreted_term(int_t, 'RLnext')
Gnext = Terms.new_uninterpreted_term(int_t, 'Gnext')
GAnext = Terms.new_uninterpreted_term(int_t, 'GAnext')
GBGnext = Terms.new_uninterpreted_term(int_t, 'GBGnext')
GDnext = Terms.new_uninterpreted_term(int_t, 'GDnext')
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
        res = Terms.yand([res, Terms.eq(nexts[v], v)])
    return res
# initial condition
INIT = Terms.yand([Terms.eq(R, Terms.rational(50, 1)),
                   Terms.eq(L, Terms.rational(2, 1)),
                   Terms.eq(RL, Terms.rational(0, 1)),
                   Terms.eq(G, Terms.rational(50, 1)),
                   Terms.eq(GA, Terms.rational(0, 1)),
                   Terms.eq(GBG, Terms.rational(0, 1)),
                   Terms.eq(GD, Terms.rational(0, 1))
                   ])
# INIT = Terms.yand([Terms.eq(R, Terms.rational(5, 1)),
#                    Terms.eq(L, Terms.rational(2, 1)),
#                    Terms.eq(RL, Terms.rational(0, 1)),
#                    Terms.eq(G, Terms.rational(5, 1)),
#                    Terms.eq(GA, Terms.rational(0, 1)),
#                    Terms.eq(GBG, Terms.rational(0, 1)),
#                    Terms.eq(GD, Terms.rational(0, 1))
#                    ])
R1 = Terms.yand([Terms.eq(nexts[R], Terms.add(R, one)), frame_cond([L, RL, G, GA, GBG, GD])])
R2 = Terms.yand([Terms.arith_geq_atom(R, one),
                   Terms.yand([Terms.eq(nexts[R], Terms.sub(R, one)), 
                               frame_cond([L, RL, G, GA, GBG, GD])])])
R3 = Terms.yand([Terms.yand([Terms.arith_geq_atom(L, one), Terms.arith_geq_atom(R, one)]),
                   Terms.yand([Terms.eq(nexts[R], Terms.sub(R, one)), 
                               Terms.eq(nexts[RL], Terms.add(RL, one)),     
                               frame_cond([L, G, GA, GBG, GD])])])
R4 = Terms.yand([Terms.arith_geq_atom(RL, one),
                   Terms.yand([Terms.eq(nexts[RL], Terms.sub(RL, one)), Terms.eq(nexts[R], Terms.add(R, one)),
                               frame_cond([L, G, GA, GBG, GD])])])
R5 = Terms.yand([Terms.yand([Terms.arith_geq_atom(RL, one), Terms.arith_geq_atom(G, one)]),
                   Terms.yand([Terms.eq(nexts[RL], Terms.sub(RL, one)), Terms.eq(nexts[G], Terms.sub(G, one)),
                               Terms.eq(nexts[GA], Terms.add(GA, one)), Terms.eq(nexts[GBG], Terms.add(GBG, one)),
                               frame_cond([R, L, GD])])])
R6 = Terms.yand([Terms.arith_geq_atom(GA, one),
                   Terms.yand([Terms.eq(nexts[GA], Terms.sub(GA, one)),
                               Terms.eq(nexts[GD], Terms.add(GD, one)),
                               frame_cond([R, L, RL, G, GBG])])])
R7 = Terms.yand([Terms.yand([Terms.arith_geq_atom(GD, one), Terms.arith_geq_atom(GBG, one)]),
                   Terms.yand([Terms.eq(nexts[GD], Terms.sub(GD, one)), Terms.eq(nexts[GBG], Terms.sub(GBG, one)),
                               Terms.eq(nexts[G], Terms.add(G, one)), 
                               frame_cond([R, L, RL, GA])])])
R8 = Terms.yand([Terms.eq(nexts[RL], Terms.add(RL, one)), frame_cond([R, L, G, GA, GBG, GD])])

TRANS = Terms.yand([
                    # Terms.yor([R1, R2]),
                    # Terms.yor([R2, R4]),
                    # Terms.yor([R3, R1]),
                    # Terms.yor([R3, R4]),
                    # Terms.yor([R4, R8])#,
                    Terms.yor([R5, R8]),
                    # Terms.yor([R5, R3]),
                    # Terms.yor([R5, R7]),
                    # Terms.yor([R5, R6]),
                    # Terms.yor([R6, R7])
])

### Problematic Trans below ###
# TRANS = Terms.yand([
#                     Terms.yor([R1, R2]),
#                     Terms.yor([R2, R4]),
#                     Terms.yor([R3, R1]),
#                     Terms.yor([R3, R4]),
#                     Terms.yor([R4, R8])#,
#                     # Terms.yor([R5, R8]),
#                     # Terms.yor([R5, R3]),
#                     # Terms.yor([R5, R7]),
#                     # Terms.yor([R5, R6]),
#                   # Terms.yor([R6, R7])
# ])
# Pairs of reactions that cannot happen simultaneously: (R1, R2), (R2, R4), (R3, R1), (R3, R4), (R4, R8), (R5, R8), (R5, R3), (R5, R7), (R5, R6), (R6, R7)
GOAL = Terms.arith_geq_atom(GBG, Terms.rational(50, 1))
# GOAL = Terms.arith_geq_atom(GBG, Terms.rational(5, 1))
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
# cfg = Config()
# cfg.default_config_for_logic(‘QF_LIA’)
yices_ctx = Context(Config().default_config_for_logic('QF_LIA'))
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
    print("-- TIME %d --", k)
    yices_ctx.push()
    yices_ctx.assert_formula(unroller.at_time(GOAL, k))
    # check
    status = yices_ctx.check_context()
    if status == Status.SAT:
        # remember the whole formula
        formula = Terms.yand([formula, unroller.at_time(GOAL, k)])
        model = Model.from_context(yices_ctx, True)
        model_string = model.to_string(80, k * 4, 0)
        print(model_string)
        print(Terms.to_string(formula))
        break
    else:
        yices_ctx.pop()
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
