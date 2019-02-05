import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []


    def kb_retract(self, fact_rule):
        """Args: fact (Fact) - Fact to be retracted
            Returns: None
            never remove anything supported
            if it's asserted --> get_fact and remove only asserted fact, remove should remove anything as long as it's unasserted & unsupported
        """
        printv("Retracting {!r}", 0, verbose, [fact_rule])
        ####################################################
        # check if fact_rule is an asserted fact

        def remove_as_fact_support(kb, f_r):
            fa = self._get_fact(f_r)
            for f in fa.supports_facts:
                for pair in f.supported_by:
                    if fa in pair:
                        f_fact = self._get_fact(f)
                        f.supported_by.remove(pair)
                        if not f.supported_by and f_fact.asserted is False:
                            kb.facts.remove(f)
            '''if f previously supported by fact_rule 
            is now un-asserted and unsupported (aka supported_by is empty), remove f'''

        def remove_as_rule_support(kb, f_r):
            fa = self._get_fact(f_r)
            for r in fa.supports_rules:
                for pair in r.supported_by:
                    if fa in pair:
                        r_rule = self._get_rule(r)
                        r.supported_by.remove(pair)
                        if not r.supported_by and r_rule.asserted is False:
                            kb.rules.remove(r)
                            " if rule becomes unsupported, remove r"

        if isinstance(fact_rule, Rule):
            # if is Rule and asserted, do nothing
                return None

        if isinstance(fact_rule, Fact):
            # if fact is in kb
            if fact_rule in self.facts:
                fact = self._get_fact(fact_rule)
                if fact.supported_by:
                    # print("Fact/Rule is supported, can't be retracted:", fact_rule)
                    return None
                if fact.asserted:
                    remove_as_fact_support(self, fact_rule)
                    remove_as_rule_support(self, fact_rule)
                    self.facts.remove(fact_rule)

        else:
            return None


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        matching = match(rule.lhs[0], fact.statement)
        if matching:
            matchpair = [(fact, rule)]
            if len(rule.lhs) == 1:
                infer_f = Fact(instantiate(rule.rhs, matching), matchpair)
                # if matchpair not in infer_f.supported_by:
                #     infer_f.supported_by.append(matchpair)
                # add new fact
                rule.supports_facts.append(infer_f)
                fact.supports_facts.append(infer_f)
                kb.kb_assert(infer_f)
            else:
                infer_lhs = []
                for element in rule.lhs[1:len(rule.lhs)]:
                    infer_lhs = [instantiate(element, matching)]
                    # infer_left_component = [instantiate(element, matching)]
                    # infer_lhs.append(infer_left_component)
                infer_rhs = instantiate(rule.rhs, matching)
                infer_r = Rule([infer_lhs, infer_rhs], matchpair)
                # add new rule
                fact.supports_rules.append(infer_r)
                rule.supports_rules.append(infer_r)
                kb.kb_assert(infer_r)
