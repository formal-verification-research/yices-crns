from yices import *
real_t = Types.real_type()
int_t = Types.int_type()
bool_t = Types.bool_type()
zero = Terms.rational(0, 1)
one = Terms.rational(1, 1)

class Unroller(object):
    def __init__(self, state_vars, nexts, inputs):
        self.state_vars = state_vars
        self.nexts = nexts
        self.inputs = inputs
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
            for i in self.inputs:
                i_t = Terms.new_uninterpreted_term(Terms.type_of_term(i),
                                                Terms.to_string(i) + "@" + str(t))
                cache[i] = i_t
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
c1 = Terms.new_uninterpreted_term(bool_t, 'c1')
c2 = Terms.new_uninterpreted_term(bool_t, 'c2')
choice = [c1, c2]
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
R1 = Terms.yand([Terms.implies(c1,
                    Terms.yand([Terms.eq(nexts[R], Terms.add(R, one)),
                                    frame_cond([L, RL, G, GA, GBG, GD])])),
                 Terms.implies(Terms.ynot(c1),
                               frame_cond([R, L, RL, G, GA, GBG, GD]))])
R2 = Terms.implies(Terms.arith_geq(R, one), Terms.sub(nexts[R], one))
R3 = Terms.implies(Terms.yand([Terms.arith_geq(L, one), Terms.arithm_geq(R, one)]),
                   Terms.yand([Terms.eq(nexts[L], L),
                               Terms.eq(nexts[R], Terms.sub(R, one)),
                               Terms.eq(nexts[RL], Terms.add(RL, one)),
                               Terms.eq(nexts[G], G),
                               Terms.eq(nexts[GA], GA),
                               Terms.eq(nexts[GBG], GBG),
                               Terms.eq(nexts[GD], GD)]))
TRANS = Terms.yand([R1, R2, R3])
GOAL = Terms.arith_geq_atom(GBG, Terms.rational(50, 1))
print("INIT := " + Terms.to_string(INIT))
print("TRANS := " + Terms.to_string(TRANS))
print("GOAL := " + Terms.to_string(GOAL))
  #unroller
unroller = Unroller(state_vars, nexts, choice)
formula = Terms.yand([unroller.at_time(INIT, 0),
                      unroller.at_time(TRANS, 0),
                      unroller.at_time(GOAL, 1)])
print(Terms.to_string(formula))
# initialize yices context
yices_ctx = Context(Config().default_config_for_logic('QF_LIA'))
formula = unroller.at_time(INIT, 0)
# assert formula in the yices context
yices_ctx.assert_formula(formula)
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
        formula = Terms.yand([formula, unroller.at_time(TRANS, k)])
        k = k + 1