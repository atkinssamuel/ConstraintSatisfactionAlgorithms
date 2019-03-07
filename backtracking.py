from csp import Constraint, Variable, CSP
import random
import util

class UnassignedVars:
    '''class for holding the unassigned variables of a CSP. We can extract
       from, re-initialize it, and return variables to it.  Object is
       initialized by passing a select_criteria (to determine the
       order variables are extracted) and the CSP object.

       select_criteria = ['random', 'fixed', 'mrv'] with
       'random' == select a random unassigned variable
       'fixed'  == follow the ordering of the CSP variables (i.e.,
                   csp.variables()[0] before csp.variables()[1]
       'mrv'    == select the variable with minimum values in its current domain
                   break ties by the ordering in the CSP variables.
    '''
    def __init__(self, select_criteria, csp):
        if select_criteria not in ['random', 'fixed', 'mrv']:
            print("Error UnassignedVars given an illegal selection criteria {}. Must be one of 'random', 'stack', 'queue', or 'mrv'".format(select_criteria))
        self.unassigned = list(csp.variables())
        self.csp = csp
        self._select = select_criteria
        if select_criteria == 'fixed':
            #reverse unassigned list so that we can add and extract from the back
            self.unassigned.reverse()

    def extract(self):
        if not self.unassigned:
            print("Warning, extracting from empty unassigned list")
            return None
        if self._select == 'random':
            i = random.randint(0,len(self.unassigned)-1)
            nxtvar = self.unassigned[i]
            self.unassigned[i] = self.unassigned[-1]
            self.unassigned.pop()
            return nxtvar
        if self._select == 'fixed':
            return self.unassigned.pop()
        if self._select == 'mrv':
            nxtvar = min(self.unassigned, key=lambda v: v.curDomainSize())
            self.unassigned.remove(nxtvar)
            return nxtvar

    def empty(self):
        return len(self.unassigned) == 0

    def insert(self, var):
        if not var in self.csp.variables():
            print("Error, trying to insert variable {} in unassigned that is not in the CSP problem".format(var.name()))
        else:
            self.unassigned.append(var)

def bt_search(algo, csp, variableHeuristic, allSolutions, trace):
    '''Main interface routine for calling different forms of backtracking search
       algorithm is one of ['BT', 'FC', 'GAC']
       csp is a CSP object specifying the csp problem to solve
       variableHeuristic is one of ['random', 'fixed', 'mrv']
       allSolutions True or False. True means we want to find all solutions.
       trace True of False. True means turn on tracing of the algorithm

       bt_search returns a list of solutions. Each solution is itself a list
       of pairs (var, value). Where var is a Variable object, and value is
       a value from its domain.
    '''
    varHeuristics = ['random', 'fixed', 'mrv']
    algorithms = ['BT', 'FC', 'GAC']

    #statistics
    bt_search.nodesExplored = 0

    if variableHeuristic not in varHeuristics:
        print("Error. Unknown variable heursitics {}. Must be one of {}.".format(
            variableHeuristic, varHeuristics))
    if algo not in algorithms:
        print("Error. Unknown algorithm heursitics {}. Must be one of {}.".format(
            algo, algorithms))

    uv = UnassignedVars(variableHeuristic,csp)
    Variable.clearUndoDict()
    for v in csp.variables():
        v.reset()
    if algo == 'BT':
         solutions = BT(uv, csp, allSolutions, trace)
    elif algo == 'FC':
        for cnstr in csp.constraints():
            if cnstr.arity() == 1:
                FCCheck(cnstr, None, None)  #FC with unary constraints at the root
        solutions = FC(uv, csp, allSolutions, trace)
    elif algo == 'GAC':
        GacEnforce(csp.constraints(), csp, None, None) #GAC at the root
        solutions = GAC(uv, csp, allSolutions, trace)

    return solutions, bt_search.nodesExplored

def BT(unAssignedVars, csp, allSolutions, trace):
    '''Backtracking Search. unAssignedVars is the current set of
       unassigned variables.  csp is the csp problem, allSolutions is
       True if you want all solutionss trace if you want some tracing
       of variable assignments tried and constraints failed. Returns
       the set of solutions found.

      To handle finding 'allSolutions', at every stage we collect
      up the solutions returned by the recursive  calls, and
      then return a list of all of them.

      If we are only looking for one solution we stop trying
      further values of the variable currently being tried as
      soon as one of the recursive calls returns some solutions.
    '''
    if unAssignedVars.empty():
        if trace: print("{} Solution Found".format(csp.name()))
        soln = []
        for v in csp.variables():
            soln.append((v, v.getValue()))
        return [soln]  #each call returns a list of solutions found
    bt_search.nodesExplored += 1
    solns = []         #so far we have no solutions recursive calls
    nxtvar = unAssignedVars.extract()
    if trace: print("==>Trying {}".format(nxtvar.name()))
    for val in nxtvar.domain():
        if trace: print("==> {} = {}".format(nxtvar.name(), val))
        nxtvar.setValue(val)
        constraintsOK = True
        for cnstr in csp.constraintsOf(nxtvar):
            if cnstr.numUnassigned() == 0:
                if not cnstr.check():
                    constraintsOK = False
                    if trace: print("<==falsified constraint\n")
                    break
        if constraintsOK:
            new_solns = BT(unAssignedVars, csp, allSolutions, trace)
            if new_solns:
                solns.extend(new_solns)
            if len(solns) > 0 and not allSolutions:
                break #don't bother with other values of nxtvar
                      #as we found a soln.
    nxtvar.unAssign()
    unAssignedVars.insert(nxtvar)
    return solns

def FCCheck(cnstr, reasonVar, reasonVal):
    '''cnstr is the constraint where every variables but one are assigned.
       reasonVar is an assigned variable to check against the sole unassigned variable, var.
       reasonVal is the value assigned to reasonVar.

       When we prune val from var, reasonVar = reasonVal is the reason why the pruning occurred.
    '''

    if cnstr.numUnassigned() != 1:
        print("Error FCCheck called on constraint {} with {} neq 1 unassigned vars".format(cnstr.name(), cnstr.numUnassignedVars))
    var = cnstr.unAssignedVars()[0]
    for val in var.curDomain():
        var.setValue(val)
        if not cnstr.check():
            var.pruneValue(val, reasonVar, reasonVal)
        var.unAssign()  #NOTE WE MUST UNDO TRIAL ASSIGNMENT
    if var.curDomainSize() == 0:
        return "DWO"
    return "OK"

def FC(unAssignedVars, csp, allSolutions, trace):
    '''Forward checking search.
       unAssignedVars is the current set of
       unassigned variables.  csp is the csp
       problem, allSolutions is True if you want all solutionsl trace
       if you want some tracing of variable assignments tried and
       constraints failed.

       RETURNS LIST OF ALL SOLUTIONS FOUND.

       Finding allSolutions is handled just as it was in BT.  Except
       that when we are not looking for all solutions and we stop
       early because one of the recursive calls found a solution we
       must make sure that we restore all pruned values before
       returning.
    '''
    #your implementation for Question 2 goes in this function body.
    #you must not change the function parameters.
    #Implementing handling of the trace parameter is optional
    #but it can be useful for debugging
    

    ##################### Personal Notes: ##########################
    # Normally argument is "Level"
    # Arguments in this function are unAssignedVars, csp, allSolutions, trace

    solutions = []
    # If all variables are assigned return with the solution(s)
    if unAssignedVars.empty():
        for variable in csp.variables():
            solutions.append((variable, variable.getValue()))
        return [solutions]
    bt_search.nodesExplored += 1
    # Pick an unassigned variable
    variable = unAssignedVars.extract()
    # Loop through all possible values of the unassigned variable
    for value in variable.curDomain():
        variable.setValue(value)
        DWO = False
        #for each constraint C over V such that C has only one unassigned variable X in its scope
        for const in csp.constraintsOf(variable):
            if const.numUnassigned() == 1:
                if FCCheck(const, variable, value) == "DWO":
                    DWO = True
                    break
        # All constraints were okay
        if DWO == False:
        # FC(Level + 1)
            solutions.extend(FC(unAssignedVars, csp, allSolutions, trace))
            if len(solutions) > 0 and not allSolutions:
                variable.restoreValues(variable, value)
                break
        variable.restoreValues(variable, value)
    variable.setValue(None)
    unAssignedVars.insert(variable)
    return solutions

def GacEnforce(constraints, csp, reasonVar, reasonVal):
    '''Establish GAC on constraints by pruning values
       from the current domains of the variables.
       Return "OK" if completed "DWO" if found
       a domain wipe out.
       
       Similar to FCCheck, reasonVar is an assigned variable with value reasonVal.
       The pruning of the values from the variables are due to reasonVar = reasonVal
    '''
    #your implementation for Question 3 goes in this function body
    #you must not change the function parameters
    #ensure that you return one of "OK" or "DWO"

    # Pseudocode: 
    # while GACQueue not empty
    #     C = GACQueue.extract()
    #     for V := each member of scope(C)
    #         for d := CurDom[V]
    #             Find an assignment A for all other
    #             variables in scope(C) such that
    #             C(A ∪ V=d) = True
    #             if A not found
    #                 CurDom[V] = CurDom[V] – d
    #                 if CurDom[V] = ∅
    #                     empty GACQueue
    #                     return DWO //return immediately
    #                 else
    #                     push all constraints C’ such that
    #                     V ∈ scope(C’) and C’ ∉ GACQueue
    #                     on to GACQueue
    # return TRUE //while loop exited without DWO

    # While GAC queue not empty:
    while len(constraints) != 0:
        # Extract constraint
        const = constraints.pop(0)
        # for V := each member of scope(C)
        for variable in const.scope():
            # for d := CurDom[V]
            for value in variable.curDomain():
                # Find an assignment A for all other variables in scope(C) 
                # such that C(A ∪ V = d) == True
                if not const.hasSupport(variable, value):
                    # Prune value:
                    variable.pruneValue(value, reasonVar, reasonVal)
                    # If the variable has no current domain that means DWO
                    if variable.curDomainSize() == 0:
                        return "DWO"
                    for check in csp.constraintsOf(variable):
                        if check != const and not check in constraints:
                            constraints.append(check)
    return "OK"

def GAC(unAssignedVars, csp, allSolutions, trace):
    '''GAC search.
       unAssignedVars is the current set of
       unassigned variables.  csp is the csp
       problem, allSolutions is True if you want all solutionsl trace
       if you want some tracing of variable assignments tried and
       constraints failed.

       RETURNS LIST OF ALL SOLUTIONS FOUND.

       Finding allSolutions is handled just as it was in BT.  Except
       that when we are not looking for all solutions and we stop
       early because one of the recursive calls found a solution we
       must make sure that we restore all pruned values before
       returning.
    '''
    #your implementation for Question 3 goes in this function body
    #You must not change the function parameters.
    #implementing support for "trace" is optional, but it might
    #help you in debugging

    # Pseudocode:
    # If all variables are assigned
    #     PRINT Value of each Variable
    #     RETURN or EXIT (RETURN for more solutions)
    #                    (EXIT for only one solution)
    # V := PickAnUnassignedVariable()
    # Assigned[V] := TRUE
    # for d := each member of CurDom(V)
    #     Value[V] := d
    #     Prune all values of V ≠ d from CurDom[V]
    #     for each constraint C whose scope contains V
    #        Put C on GACQueue
    #     if(GAC_Enforce() != DWO)
    #        GAC(Level+1) /*all constraints were ok*/
    #     RestoreAllValuesPrunedFromCurDoms()
    # Assigned[V] := FALSE
    # return; 

    solutions = []
    # If all variables are assigned:
    if unAssignedVars.empty():
        for variable in csp.variables():
            solutions.append((variable, variable.getValue()))
        # Return solutions
        return [solutions]

    bt_search.nodesExplored += 1
    # Extract a variable:
    variable = unAssignedVars.extract()
    # For all of the values that the variable can adopt:
    for value in variable.curDomain():
        # Set the value of the variable to the current variable iteration
        variable.setValue(value)
        DWO = False
        if GacEnforce(csp.constraintsOf(variable), csp, variable, value) == "DWO":
            DWO = True
        if not DWO:
            # Just as in FC we recursively call GAC if there is no DWO
            # GAC(Level+1):
            solutions.extend(GAC(unAssignedVars, csp, allSolutions, trace))
            if len(solutions) > 0 and not allSolutions:
                variable.restoreValues(variable, value)
                break
        # This line will immediately execute if there is a DWO
        variable.restoreValues(variable, value)
    variable.setValue(None)
    unAssignedVars.insert(variable)
    return solutions


    