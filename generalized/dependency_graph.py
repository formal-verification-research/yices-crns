
import math
import sys
from xmlrpc.client import MAXINT
from parse_model import *

DEBUG = True

class DepNode:
    def __init__(self, reaction):
        self.reaction = reaction # type Reaction
        self.dependencies = {}
        self.executions = MAXINT
        self.parents = [] # array of DepNodes
        self.enabled = False
        self.species_desired = []


# init: species counts as if they were the initial state
# target: dictionary of targets
# reactions: parsed list of availble reactions
# node: current working node

def make_dependency_graph(init, target, reactions, node=None):
    
    # pre-calculate couple of useful values
    # num_species = len(init)

    # make the target node on first run
    if node == None:
        node = DepNode(reaction=None)
    
        # figure out how far away we are from the target
        for t in target:
            target_species = target[t][0]
            target_relation = target[t][1]
            target_count = int(target[t][2])
        init_count = init[target_species]

        # TODO: Make this if statement less ugly
        if init_count == target_count:
            print("Target satisfied in the initial state!")
            node.enabled = True
            node.executions = 0
        elif target_relation == "=" or target_relation == "==":
            node.executions = target_count - init_count
        elif target_relation == ">=":
            if init_count >= target_count:
                print("Target satisfied in the initial state!")
                node.enabled = True
                node.executions = 0
            else:
                node.executions = target_count - init_count
        elif target_relation == "<=":
            if init_count <= target_count:
                print("Target satisfied in the initial state!")
                node.enabled = True
                node.executions = 0
            else:
                node.executions = target_count - init_count
        else:
            print("ERROR: Target incorrectly defined.")

        if DEBUG:
            print("node.executions", node.executions)
    
    # figure out if this reaction is enabled enough times in the initial/current state
    modified_init = {}
    for s in init:
        modified_init[s] = init[s]

    if node.reaction:
        # create a modified initial state based on this node's executions
        # for s in init:
        #     for c in node.reaction.consume:
        #         modified_init[c[0]] = init[c[0]] - (node.executions * c[1])
        #     for c in node.reaction.produce:
        #         modified_init[c[0]] = init[c[0]] + (node.executions * c[1])

        node.enabled = True
        for c in node.reaction.consume:
            if (node.reaction.dep_executions * c[1]) < init[c[0]]:
                node.enabled = False

    # base case
    if node.enabled:
        return node

    # handle cycles
    # TODO: make sure this works, might need to return something else?
    if node.reaction in node.parents:
        return None
    
    # figure out what reactions we need
    for t in target:
        delta_target = int(target[t][2]) - init[t]
        for r in reactions:
            # if we need to generate a species
            if delta_target > 0: 
                for s in reactions[r].produce:
                    if target_species == s[0]:
                        new_dependency = DepNode(r)
                        needed_execs = int(math.ceil(float(delta_target) / float(s[1])))
                            # s[1] is the stoichiometric constant for the species
                        node.dependencies[new_dependency].executions = needed_execs
                        node.dependencies[new_dependency].reaction.dep_executions += needed_execs
                        node.dependencies[new_dependency].parents = node.parents + [node]
                        
                if DEBUG:
                    print("Reaction", reactions[r], "generates", target_species)


        # # if we need to degrade a species
        # elif delta_target < 0: 
        #     for s in reactions[r].consume:
        #         if target_species == s[0]:
        #             new_dependency = DepNode(r)
        #             needed_execs = int(math.ceil(float(delta_target) / float(s[1])))
        #             node.dependencies[new_dependency].executions = needed_execs
        #             node.dependencies[new_dependency].parents = node.parents + [node]
        #     if DEBUG:
        #         print("Reaction", reactions[r], "consumes", target_species)
    
