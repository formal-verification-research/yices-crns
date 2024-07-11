
import math
import sys
from xmlrpc.client import MAXINT
from parse_model import *

DEBUG = True

class DepNode:
    def __init__(self, reaction):
        self.reaction = reaction # type Reaction
        self.dependencies = {}
        self.executions = 0
        self.parents = [] # array of DepNodes
        self.enabled = False
        self.species_desired = []

    def __str__(self) -> str:
        s = 50*"-"
        s = s+("\n")
        s = s+(str(self.reaction))
        s = s+(", ")
        s = s+("Executions " + str(self.executions))
        s = s+("\n")
        s = s+("Enabled " + str(self.enabled))
        s = s+("\n")
        for c in self.dependencies:
            s = s+"DEP "+str(c.reaction.name)
            s = s+("\n")
        for p in self.species_desired:
            s = s+"WANT "+str(p)
            s = s+("\n")
        s = s+(50*"-")
        s = s+("\n")
        return s


# init: species counts as if they were the initial state
# target: target tuple (limited to one target for now)
# reactions: parsed list of availble reactions
# node: current working node

def make_dependency_graph(init, target, reactions, INnode=None, parents=[], depth=0):
    
    lineStart = depth*"  "

    print(lineStart, 50*"=")

    # figure out how far away we are from the targets
    target_species = {}
    target_relation = {}
    target_count = {}
    init_count = {}
    for t in target:
        target_species[t] = target[t][0]
        target_relation[t] = target[t][1]
        target_count[t] = int(target[t][2])
        init_count[t] = init[target_species[t]]

    # make the target node on first run
    if INnode == None:
        node = DepNode(reaction=None)
    
        for t in target:
            if init_count[t] == target_count[t]:
                print(lineStart, "Target satisfied in the initial state!")
                node.enabled = True
                node.executions = 0
            elif target_relation[t] == "=" or target_relation[t] == "==":
                node.executions = target_count[t] - init_count[t]
            elif target_relation[t] == ">=":
                if init_count[t] >= target_count[t]:
                    print(lineStart, "Target satisfied in the initial state!")
                    node.enabled = True
                    node.executions = 0
                else:
                    node.executions = target_count[t] - init_count[t]
            elif target_relation[t] == "<=":
                if init_count[t] <= target_count[t]:
                    print(lineStart, "Target satisfied in the initial state!")
                    node.enabled = True
                    node.executions = 0
                else:
                    node.executions = target_count[t] - init_count[t]
            else:
                print(lineStart, "ERROR: Target incorrectly defined.")
            
            break # only consider one target in the initial node (csl rule???)

    else:
        node = INnode

    if DEBUG:
        if node.reaction:
            print(lineStart, str(node.reaction), ".executions", node.executions)
        else:
            print(lineStart, "target.executions", node.executions)

    # figure out if this reaction is enabled enough times in the initial/current state
    if DEBUG:
        print(lineStart, "init", init)

    modified_init = {}
    for i in init:
        modified_init[i] = init[i]
    modified_target = {}
    # for i in target:
    #     modified_target[i] = target[i]

    if node.reaction:
        # create a modified initial state based on this node's executions
        for s in init:
            for c in node.reaction.consume:
                if c[0] == s:
                    modified_init[s] = modified_init[s] - (node.executions * int(c[1]))
            for c in node.reaction.produce:
                if c[0] == s:
                    modified_init[s] = modified_init[s] + (node.executions * int(c[1]))
            if modified_init[s] < 0:
                modified_target[s] = (s, ">=", str(0-modified_init[s]))

        node.enabled = True
        for c in node.reaction.consume:
            if (node.reaction.dep_executions * int(c[1])) < int(init[c[0]]):
                node.enabled = False
                break
        for s in modified_init:
            if modified_init[s] < 0:
                node.enabled = False
                break

    if DEBUG:
            print(lineStart, "modified_init", modified_init)
            print(lineStart, "modified_target 1", modified_target)

    # base case
    if node.enabled:
        print(lineStart, "ENABLED")
        return True

    # handle cycles
    # TODO: make sure this works, might need to return something else?
    if node.reaction in node.parents:
        print(lineStart, "THERE WAS A CYCLIC DEPENDENCY")
        return False
    
    # figure out what reactions we need for each target
    for t in target:
        delta_target = int(target[t][2]) - modified_init[target_species[t]]
        if DEBUG:
            print(lineStart, "working on target", target[t])
            print(lineStart, "delta_target", delta_target)
        if delta_target <= 0:
            print(lineStart, "Found reactions to meet the target, now looking for their dependencies")
        else:
            if t in modified_target.keys():
                modified_target[t] = (modified_target[t][0], modified_target[t][1], str(int(modified_target[t][2]) + delta_target))
            else:
                modified_target[t] = (target[t][0], target[t][1], str(delta_target))
        if DEBUG:
            print(lineStart, "modified_target 2", modified_target)

    for t in modified_target:
        delta_target = int(modified_target[t][2]) - init[modified_target[t][0]]
        if DEBUG:
            print(lineStart, "modified_target[t][2]", modified_target[t][2])
            print(lineStart, "modified_init[modified_target[t][0]]", modified_init[modified_target[t][0]])
            print(lineStart, "delta_target", delta_target)
        for r in reactions:
            # if we need to generate a species
            if delta_target > 0: 
                for s in reactions[r].produce:
                    if modified_target[t][0] == s[0]:
                        if r not in node.dependencies.keys():
                            node.dependencies[r] = DepNode(reactions[r])
                        needed_execs = int(math.ceil(float(delta_target) / float(s[1])))
                            # s[1] is the stoichiometric constant for the species
                        node.dependencies[r].executions += needed_execs
                        node.dependencies[r].reaction.dep_executions += needed_execs
                        node.dependencies[r].parents += node.parents

                        if DEBUG:
                            print(lineStart, "Reaction", r, "generates", modified_target[t][0])
                            print(lineStart, "Added dependency", node.dependencies[r].reaction.name)
                            print(lineStart, "with executions", node.dependencies[r].executions)

    for d in node.dependencies:
        print(lineStart, "DEP", node.dependencies[d].reaction.name)
    
    # RECURSE
    for d in node.dependencies:
        make_dependency_graph(modified_init, modified_target, reactions, node.dependencies[d], parents, depth+1)
                        
                    
