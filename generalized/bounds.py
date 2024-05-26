# built-in
import sys
import math

# local
from parse_model import *
from unroller import *
from yices_utils import *

# yices
from yices import *

# types for yices
real_t = Types.real_type()
int_t = Types.int_type()
bool_t = Types.bool_type()

print(80*"=")
print("CRN Variable Bound Calculator")
print(80*"=")

# get command line arguments
# command line instructions: python3 bounds.py model.crn (bv-bound)
# where bv-bound is optional and is the upper limit on variables.
if len(sys.argv) < 2:
    print("ERROR: NEED EXACTLY ONE ARGUMENT, THE NAME OF THE DESIRED FILE.")
    exit(1)
filename = str(sys.argv[1])

# find out how many bits if we added another command
BITS = 8
if len(sys.argv) == 3:
    BITS = math.ceil(math.log2(sys.argv[2]))

def val_term(v):
    #return Terms.integer(v)
    return Terms.bvconst_integer(BITS, v)

zero = val_term(0)
one = val_term(1)


# define the bitvector type
bv_t = Types.bv_type(BITS)

# start parsing the model
print(80*"-")
print("Parsing the model from", filename)
print(80*"-")

# parse the model, parse_model.py
init, target, reaction = parse_model(filename)
print("Parsed model. Results as follows.")
print(init)
print(target)
for r in reaction:
    print(reaction[r])

print(80*"-")
print("Building the yices model")
print(80*"-")

# leave our type as a bit vector
ty = bv_t

# build our vars and nexts,
# and fill initial values
state_vars = dict()
nexts = dict()
init_yand = []
for s in init:
    state_vars[s] = Terms.new_uninterpreted_term(ty, s)
    nexts[s] = Terms.new_uninterpreted_term(ty, s + "_next")
    init_yand.append(eq_term(state_vars[s], val_term(init[s])))

# now define our frame condition
def frame_cond(vars):
    res = Terms.true()
    for v in vars:
        res = Terms.yand([res, eq_term(nexts[v], state_vars[v])])
    return res

INIT = Terms.yand(init_yand)

encoded_reactions = []

for r in reaction:
    print("reaction", r)
    terms = []
    used_species = []
    catalysts = []
    # handle consumption
    for c in reaction[r].consume:
        terms.append(geq_term(state_vars[c[0]], one))
        # identify catalysts
        is_catalyst = False
        for p in reaction[r].produce:
            if c[0] == p[0]:
                print("is_catalyst", c[0], p[0])
                is_catalyst = True
                catalysts.append(c[0])
                if p[1] < c[1]:
                    # only subtract the net difference
                    print("sub net", p[1], c[1])
                    terms.append(eq_term(nexts[p[0]], sub_term(state_vars[p[0]],val_term(c[1] - p[1]))))
                    used_species.append(c[0])
                elif p[1] > c[1]:
                    # only add the net sum
                    print("add net", p[1], c[1])
                    terms.append(eq_term(nexts[p[0]], add_term(state_vars[p[0]],val_term(p[1] - c[1]))))
                    used_species.append(c[0])
                else:
                    print("net zero", p[1], c[1])
        if not is_catalyst:
            print("sub", c[0], c[1])
            terms.append(eq_term(nexts[c[0]], sub_term(state_vars[c[0]],val_term(c[1]))))
            used_species.append(c[0])
    # handle production
    for p in reaction[r].produce:
        if p[0] not in catalysts:
            print("add", p[0], p[1])
            terms.append(eq_term(nexts[p[0]], add_term(state_vars[p[0]],val_term(p[1]))))
            used_species.append(p[0])
    # handle unused species
    frame_cond_list = []
    for s in init:
        if s not in used_species:
            frame_cond_list.append(s)
    terms.append(frame_cond(frame_cond_list))
    # add the final reaction to the encoded reactions
    encoded_reactions.append((Terms.yand(terms)))
    
# TODO: Eventually this should be able to reduce down to our strictly necessary,
# using the dependency graph?
TRANS = Terms.yor(encoded_reactions)

# figure out the target
# TODO: Make it adaptable to the desired inequality
TARGET = geq_term(state_vars[target[0]], val_term(target[1]))

# print for debugging purposes
print("INIT := " + Terms.to_string(INIT))
print("TRANS := " + Terms.to_string(TRANS))
print("TARGET := " + Terms.to_string(TARGET))

# make the unroller
unroller = Unroller(state_vars, nexts)

# initialize yices context
cfg = Config()
yices_ctx = Context(cfg)

# initial formula
formula = unroller.at_time(INIT, 0)

# assert formula in the yices context
yices_ctx.assert_formula(formula)
status = yices_ctx.check_context()

# print current status to debug
if status == Status.ERROR:
    print("Status 1: ERROR")
if status == Status.UNKNOWN:
    print("Status 1: UNKNOWN")
if status == Status.UNSAT:
    print("Status 1: UNSAT")
if status == Status.SAT:
    print("Status 1: SAT")

# start the interesting bmc business
k = 0

while True:
    print("-- TIME %3d --" % (k))
    # for assuming a goal at time k
    assump = Terms.new_uninterpreted_term(bool_t)
    #yices_ctx.push()
    yices_ctx.assert_formula(Terms.implies(assump,
                                           unroller.at_time(TARGET, k)))
    # check
    status = yices_ctx.check_context_with_assumptions(None, [assump])
    #yices_ctx.assert_formula(assump)
    #status = yices_ctx.check_context()
    if status == Status.SAT:
        # remember the whole formula
        formula = Terms.yand([formula, unroller.at_time(TARGET, k)])
        model = Model.from_context(yices_ctx, True)
        model_string = model.to_string(80, k * 4, 0)
        #print(model_string)
        #print(Terms.to_string(formula))
        break
    else:
        #yices_ctx.pop()
        # forgetting goal at time k
        yices_ctx.assert_formula(Terms.ynot(assump))
        yices_ctx.assert_formula(unroller.at_time(TRANS, k))
        formula = Terms.yand([formula, unroller.at_time(TRANS, k)])
        k = k + 1

