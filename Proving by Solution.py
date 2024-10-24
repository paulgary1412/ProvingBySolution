#Oca,Paul Gary & Muana Christian Albert
#ITE153 - IT3D
#Activity 4 - Proving by Resolution

def get_atoms():
    atoms = input("Enter variables separated by comma :\n for Exampe :\n q,r,s,t,u ")
    atoms_list = atoms.split(",")
    return [atom.strip() for atom in atoms_list]


def get_premises(atoms):
    
    print("'~' for NOT,\n'^' for AND,\n'+' for OR,\n'-' for IMPLIES,\n'=' for IFF")
    print("Enter the Premises, type 'stop' when you're done")
    print("\n")
    premises = []
    while True:
        try:
            x = input("Premise:")
            if x.lower() == 'stop' or x == 'Stop':
                break
            else:
                for i in x:
                    if i.isalpha() and i not in atoms:
                        raise Exception("Invalid Input")
                premises.append(x.replace(' ', ''))
        except Exception as e:
            print(e)
    return premises

def negate_clause(clause):
    operators = ['+', '^']
    result = ""
    literals = clause_splitter(clause, operators)

    for literal in literals:
        if literal[0] == '~' and len(literal) == 2:
            result += literal[1:]
        elif '+' in literal and len(literal) == 1:
            result += '^'
        elif '^' in literal and len(literal) == 1:
            result += '+'
        elif len(literal) > 2:
            result += negate_clause(literal)
        else:
            result += '~' + literal

    result = simplify(result)
    if len(result) > 2:
        result = '(' + result + ')'

    return result


def clause_splitter(clause, operators):
    inside_parenthesis = False
    literals = []
    current_literals = ""

    for c in clause:
        if c == '(':
            inside_parenthesis = True
        elif c == ')':
            inside_parenthesis = False
        elif c in operators and not inside_parenthesis:
            literals.append(current_literals)
            literals.append(c)
            current_literals = ""
        else:
            current_literals += c

    if current_literals:
        literals.append(current_literals)

    return literals


def evaluate(expression):
    stack = []
    i = 0
    while i < len(expression):
        if expression[i] in '(':
            stack.append(i)
        elif expression[i] in ')':
            start = stack.pop()
            inner_expression = expression[start + 1:i]
            value = evaluate(inner_expression)
            expression = expression[:start] + '(' + str(value) + ')' + expression[i + 1:]
            i = start + len(str(value)) + 2
            continue
        i += 1
    return remove_implications(expression)

def simplify(expression):
    stack = []
    i = 0
    left_coefficient = ""
    right_coefficient = ""
    result = ""
    negate = False

    while i < len(expression):
        if expression[i] in '(':
            if i - 1 >= 0:
                if expression[i - 1] == '~':
                    negate = True
                    expression = expression[:i - 1] + '(' + expression[i:]
                    i -= 1
                else:
                    stack.append(i)
            else:
                stack.append(i)
        elif expression[i] in ')':
            start = stack.pop()
            inner_expression = expression[start + 1:i]
            left_coefficient = expression[start - 2:start]
            right_coefficient = expression[i + 1:i + 3]

            if negate:
                inner_expression = negate_clause(inner_expression).strip('()')
                left_coefficient = expression[start - 3:start - 1]
                expression = expression[:start] + inner_expression + expression[i:]

            value = simplify(inner_expression)

            if len(left_coefficient) == 0:
                if '(' not in right_coefficient:
                    for operator in value:
                        if operator in '^+' and operator not in right_coefficient:
                            literals = value.split(operator)
                            parts = [literal + right_coefficient for literal in literals]
                            value = operator.join(parts)
                            expression = value
                    i = start + len(str(value)) + 2
                elif '(' in right_coefficient:
                    expression = expression[:start] + str(value) + ')' + expression[i + 1:]
                    i = start + len(str(value))

            else:
                if ')' not in left_coefficient:
                    for operator in value:
                        if operator in '^+' and operator not in left_coefficient:
                            literals = value.split(operator)
                            parts = [left_coefficient + literal for literal in literals]
                            value = operator.join(parts)
                            expression = value
                    i = start + len(str(value)) + 2
                elif ')' in left_coefficient:
                    expression = expression[:start] + '(' + value + expression[i + 1:]
                    i = start + len(str(value))

        i += 1

    result = expression.replace('(', '').replace(')', '')
    return result


def remove_implications(premises):
    clause = ""
    if '-' in premises:
        antecedent, consequent = premises.split('-')
        clause = negate_clause(antecedent) + '+' + consequent
        clause = simplify(clause)
    elif '=' in premises:
        antecedent, consequent = premises.split('=')
        left = '(' + negate_clause(antecedent) + '+' + consequent + ')'
        right = '(' + antecedent + '+' + negate_clause(consequent) + ')'
        left = simplify(left)
        right = simplify(right)
        clause = '(' + left + '^' + right + ')'
    elif '+' in premises:
        literals = premises.split('+')
        literals = [simplify(literal) for literal in literals]
        clause = '(' + '+'.join(literals) + ')'
    else:
        clause = premises

    return clause

def is_tautology(clause):
    for literal1 in clause:
        for literal2 in clause:
            if literal1 == '~' + literal2 or literal2 == '~' + literal1:
                return True
    return False


def resolve(clause1, clause2):
    for literal1 in clause1:
        for literal2 in clause2:
            if literal1 == '~' + literal2 or literal2 == '~' + literal1:
                resolvent = sorted(set(clause1 + clause2) - {literal1, literal2})
                print(f"\n{clause1} , {clause2} -> resolves to {resolvent}")
                return resolvent
    return None


def is_valid(clauses):
    new_clause = []
    while True:
        for i in range(len(clauses)):
            for j in range(i + 1, len(clauses)):
                resolvent = resolve(clauses[i], clauses[j])
                if resolvent is not None:
                    if not resolvent:
                        return True
                    if not is_tautology(resolvent) and resolvent not in clauses and resolvent not in new_clause:
                        new_clause.append(resolvent)
        if new_clause in clauses:
            return False
        if not new_clause:
            return False
        clauses += new_clause
        new_clause = []


def get_conclusion():
    print("\n")
    conclusion = input("Enter Conclusion: ")
    evaluated = evaluate(conclusion)
    negated = negate_clause(evaluated)
    simplified = simplify(negated)
    return simplified

def convert_to_clause_form(premises):
    clauses = []
    for premise in premises:
        clause = evaluate(premise)
        new_clause = simplify(clause)

        if '^' in new_clause:
            result = new_clause.split('^')
        else:
            result = [new_clause]

        clauses += list(set(result))

    return clauses


def print_clauses(clauses):
    print("\nClauses")
    i = 1
    for clause in clauses:
        print("Clause " + str(i) + ": " + clause)
        i += 1


def main():
    atoms = get_atoms()
    premises = get_premises(atoms)
    conclusion = get_conclusion()
    clauses = convert_to_clause_form(premises + [conclusion])
    print_clauses(clauses)
    new_clauses = []
    for clause in clauses:
        clause = clause.split('+')
        new_clauses.append(clause)

    if is_valid(new_clauses):
        print(" NIL")
        print("\nArgument is VALID")
    else:
        print("\nArgument is INVALID")

main()
