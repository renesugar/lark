"""This module builds a LALR(1) transition-table for lalr_parser.py

For now, shift/reduce conflicts are automatically resolved as shifts.
"""

# Author: Erez Shinan (2017)
# Email : erezshin@gmail.com

import logging
from collections import defaultdict, deque

from ..utils import classify, classify_bool, bfs, fzset, Serialize, Enumerator
from ..exceptions import GrammarError

from .grammar_analysis import GrammarAnalyzer, Terminal, LR0ItemSet, RulePtrSet
from ..grammar import Rule

###{standalone

class Action:
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return self.name
    def __repr__(self):
        return str(self)

Shift = Action('Shift')
Reduce = Action('Reduce')


class ParseTable:
    def __init__(self, states, start_states, end_states):
        self.states = states
        self.start_states = start_states
        self.end_states = end_states

    def serialize(self, memo):
        tokens = Enumerator()
        rules = Enumerator()

        states = {
            state: {tokens.get(token): ((1, arg.serialize(memo)) if action is Reduce else (0, arg))
                    for token, (action, arg) in actions.items()}
            for state, actions in self.states.items()
        }

        return {
            'tokens': tokens.reversed(),
            'states': states,
            'start_states': self.start_states,
            'end_states': self.end_states,
        }

    @classmethod
    def deserialize(cls, data, memo):
        tokens = data['tokens']
        states = {
            state: {tokens[token]: ((Reduce, Rule.deserialize(arg, memo)) if action==1 else (Shift, arg))
                    for token, (action, arg) in actions.items()}
            for state, actions in data['states'].items()
        }
        return cls(states, data['start_states'], data['end_states'])


class IntParseTable(ParseTable):

    @classmethod
    def from_ParseTable(cls, parse_table):
        enum = list(parse_table.states)
        state_to_idx = {s:i for i,s in enumerate(enum)}
        int_states = {}

        for s, la in parse_table.states.items():
            la = {k:(v[0], state_to_idx[v[1]]) if v[0] is Shift else v
                  for k,v in la.items()}
            int_states[ state_to_idx[s] ] = la


        start_states = {start:state_to_idx[s] for start, s in parse_table.start_states.items()}
        end_states = {start:state_to_idx[s] for start, s in parse_table.end_states.items()}
        return cls(int_states, start_states, end_states)

###}


# digraph and traverse, see The Theory and Practice of Compiler Writing

# computes F(x) = G(x) union (union { G(y) | x R y })
# X: nodes
# R: relation (function mapping node -> list of nodes that satisfy the relation)
# G: set valued function
def digraph(nodes, R, G):
    F = {}
    stack = []
    weights = {node:0 for node in nodes}

    # G: set valued function
    # F: set valued function we are computing (map of input -> output)
    def traverse(node):
        stack.append(node)
        weights[node] = len(stack)
        F[node] = G[node]
        for r in R[node]:
            if weights[r] == 0:
                traverse(r)
            n_x = weights[node]
            n_y = weights[r]
            assert(n_x > 0)
            assert(n_y != 0)
            if 0 < n_y < n_x:
                weights[node] = n_y
            F[node].update(F[r])

        if weights[node] == len(stack):
            f_x = F[node]
            while True:
                top_node = stack.pop()
                weights[top_node] = -1
                F[top_node] = f_x
                if top_node == node:
                    break

    for x in nodes:
        if weights[x] == 0:
            traverse(x)
    return F


class LALR_Analyzer(GrammarAnalyzer):
    def __init__(self, parser_conf, debug=False):
        GrammarAnalyzer.__init__(self, parser_conf, debug)
        self.nonterminal_transitions = []
        self.directly_reads = defaultdict(set)
        self.reads = defaultdict(set)
        self.includes = defaultdict(set)


    def compute_lr0_states(self):
        """Generate a graph of all reachable LR0ItemSets, connected through transitions
        
        Returns the list of items (vertices of the graph)
        """
        cache = {}

        def step(state):
            d = classify(state.closure.only_unsatisfied(), lambda rp: rp.next)
            for sym, rps in d.items():
                kernel = RulePtrSet({rp.advance(sym) for rp in rps})
                if kernel not in cache:
                    closure = set(kernel)
                    for s in kernel.get_next_rules():
                        closure |= self.expanded_rules[s]
                    cache[kernel] = LR0ItemSet(kernel, closure)

                new_state = cache[kernel]
                state.transitions[sym] = new_state
                yield new_state

        return list(bfs(self.lr0_start_states.values(), step))

    def compute_reads_relations(self):

        for root in self.lr0_start_states.values():
            assert(len(root.kernel) == 1)
            for rp in root.kernel:
                assert(rp.index == 0)
                self.directly_reads[(root, rp.next)] = set([ Terminal('$END') ])

        for nt in self.nonterminal_transitions:
            state, s = nt
            next_state = state.transitions[s]
            dr = self.directly_reads[nt]
            r = self.reads[nt]
            for s2 in next_state.closure.get_next():
                if s2.is_term:
                    dr.add(s2)
                elif s2 in self.NULLABLE:
                    r.add((next_state, s2))

    def compute_includes_lookback(self):
        self.lookback = defaultdict(set)
        for nt in self.nonterminal_transitions:
            state, s = nt
            lookback = self.lookback[nt]
            for rp in state.closure.by_origin(s):

                # traverse the states for rp(.rule)
                state2 = state
                for i in range(rp.index, len(rp.rule.expansion)):
                    s = rp.rule.expansion[i]
                    nt2 = (state2, s)
                    if nt2 in self.reads:
                        if fzset(rp.rule.expansion[i+1:]) <= self.NULLABLE:
                            self.includes[nt2].add(nt)

                    state2 = state2.transitions[s]

                # state2 is at the final state for rp.rule
                if rp.index == 0:
                    for rp2 in state2.closure.by_rule(rp.rule).only_satisfied():
                        lookback.add((state2, rp2.rule))


    def compute_lookaheads(self):
        read_sets = digraph(self.nonterminal_transitions, self.reads, self.directly_reads)
        follow_sets = digraph(self.nonterminal_transitions, self.includes, read_sets)

        for nt, lookbacks in self.lookback.items():
            for state, rule in lookbacks:
                for s in follow_sets[nt]:
                    state.lookaheads[s].add(rule)

    def compute_lalr1_states(self):
        m = {}
        for state in self.lr0_states:
            actions = {la:(Shift, next_state.closure) for la, next_state in state.transitions.items()}
            for la, rules in state.lookaheads.items():
                if len(rules) > 1:
                    raise GrammarError('Collision in %s: %s' % (la, ', '.join([ str(r) for r in rules ])))
                if la in actions:
                    if self.debug:
                        logging.warning('Shift/reduce conflict for terminal %s: (resolving as shift)', la.name)
                        logging.warning(' * %s', list(rules)[0])
                else:
                    r ,= rules
                    actions[la] = (Reduce, r)
            m[state] = { k.name: v for k, v in actions.items() }

        self.states = { k.closure: v for k, v in m.items() }

        # compute end states
        end_states = {}
        for state in self.states:
            for rp in state:
                for start in self.lr0_start_states:
                    if rp.rule.origin.name == ('$root_' + start) and rp.is_satisfied:
                        assert(not start in end_states)
                        end_states[start] = state

        self._parse_table = ParseTable(self.states, { start: state.closure for start, state in self.lr0_start_states.items() }, end_states)

        if self.debug:
            self.parse_table = self._parse_table
        else:
            self.parse_table = IntParseTable.from_ParseTable(self._parse_table)

    def compute_lalr(self):
        self.lr0_states = self.compute_lr0_states()

        # Collect set of all reachable pairs of (state, s), where 's' is a non-terminal expected by state
        self.nonterminal_transitions = { (state, s) for state in self.lr0_states
                                                    for s in state.closure.get_next_rules() }

        self.compute_reads_relations()
        self.compute_includes_lookback()
        self.compute_lookaheads()
        self.compute_lalr1_states()