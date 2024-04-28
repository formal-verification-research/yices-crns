from yices import *

real_t = Types.real_type()
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
S1 = Terms.new_uninterpreted_term(real_t, 'S1')
S2 = Terms.new_uninterpreted_term(real_t, 'S2')
state_vars = [S1, S2]

S1next = Terms.new_uninterpreted_term(real_t, 'S1next')
S2next = Terms.new_uninterpreted_term(real_t, 'S2next')
nexts = dict()
nexts[S1] = S1next
nexts[S2] = S2next

z = Terms.new_uninterpreted_term(bool_t, 'z')
choice = [z]

# initial condition
INIT = Terms.yand([Terms.eq(S1, one), Terms.eq(S2, Terms.rational(40, 1))])

gamma1 = Terms.yand([Terms.eq(nexts[S1], S1), Terms.eq(nexts[S2], Terms.add(S2, one))])
gamma4 = Terms.yand([Terms.eq(nexts[S1], S1), Terms.eq(nexts[S2], Terms.sub(S2, one))])
gamma2 = Terms.yor([gamma1, gamma4])
gamma3 = Terms.yand([Terms.eq(nexts[S1], S1), Terms.eq(nexts[S2], S2)])

TRANS = Terms.ite(Terms.ynot(z),
                  Terms.ite(Terms.arith_gt_atom(S1, zero),
                            Terms.ite(Terms.eq(S2, zero),
                                      gamma1,
                                      gamma2),
                            Terms.ite(Terms.eq(S2, zero),
                                      gamma3,
                                      gamma4)),
                  gamma3)

GOAL = Terms.arith_geq_atom(S2, Terms.rational(80, 1))

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
yices_ctx = Context(Config().default_config_for_logic('QF_LRA'))

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
        break
    else:
        yices_ctx.pop()
        yices_ctx.assert_formula(unroller.at_time(TRANS, k))
        formula = Terms.yand([formula, unroller.at_time(TRANS, k)])
        k = k + 1


