class Variable
    property name : String

    def initialize(name : String)
        @name = name
    end

    def to_s(io)
        io << @name
    end
end

class Negation
    property rhs : Term

    def initialize(rhs : Term)
        @rhs = rhs
    end

    def recurse(f : Term -> Term)
        Negation.new(f.call(@rhs))
    end

    def to_s(io)
        io << "(¬#{@rhs})"
    end

    def ==(other : Negation)
        @rhs == other.rhs
    end

    def ==(other)
        false
    end
end

class Implication
    property lhs : Term
    property rhs : Term

    def initialize(lhs : Term, rhs : Term)
        @lhs = lhs
        @rhs = rhs
    end

    def recurse(f : Term -> Term)
        Implication.new(f.call(@lhs), f.call(@rhs))
    end

    def to_s(io)
        io << "(#{lhs} ⇒ #{rhs})"
    end

    def ==(other : Implication)
        @lhs == other.lhs && @rhs == other.rhs
    end

    def ==(other)
        false
    end
end

class Disjunction
    property lhs : Term
    property rhs : Term

    def initialize(lhs : Term, rhs : Term)
        @lhs = lhs
        @rhs = rhs
    end

    def recurse(f : Term -> Term)
        Disjunction.new(f.call(@lhs), f.call(@rhs))
    end

    def to_s(io)
        io << "(#{lhs} ∨ #{rhs})"
    end

    def ==(other : Disjunction)
        @lhs == other.lhs && @rhs == other.rhs
    end

    def ==(other)
        false
    end
end

class Conjunction
    property lhs : Term
    property rhs : Term

    def initialize(lhs : Term, rhs : Term)
        @lhs = lhs
        @rhs = rhs
    end

    def recurse(f : Term -> Term)
        Conjunction.new(f.call(@lhs), f.call(@rhs))
    end

    def to_s(io)
        io << "(#{lhs} ∧ #{rhs})"
    end

    def ==(other : Conjunction)
        @lhs == other.lhs && @rhs == other.rhs
    end

    def ==(other)
        false
    end
end

class UniversalQuantification
    property variable : Variable
    property body : Term

    def initialize(variable : Variable, body : Term)
        @variable = variable
        @body = body
    end

    def recurse(f : Term -> Term)
        UniversalQuantification.new(@variable, f.call(@body))
    end

    def to_s(io)
        io << "(∀#{@variable}. #{@body})"
    end

    def ==(other : UniversalQuantification)
        @variable == other.variable && @body == other.body
    end

    def ==(other)
        false
    end
end

class ExistentialQuantification
    property variable : Variable
    property body : Term

    def initialize(variable : Variable, body : Term)
        @variable = variable
        @body = body
    end

    def recurse(f : Term -> Term)
        ExistentialQuantification.new(@variable, f.call(@body))
    end

    def to_s(io)
        io << "(∃#{@variable}. #{@body})"
    end

    def ==(other : ExistentialQuantification)
        @variable == other.variable && @body == other.body
    end

    def ==(other)
        false
    end
end

class Abstraction
    property origin = Set(Variable).new
    property variable : Variable
    property constraint : Term
    property body : Term

    def initialize(variable : Variable, constraint : Term, body : Term)
        @variable = variable
        @constraint = constraint
        @body = body
    end

    def recurse(f : Term -> Term)
        f = Abstraction.new(@variable, f.call(@constraint), f.call(@body))
        f.origin = @origin
        f
    end

    def to_s(io)
        io << "(#{origin.to_a.map { |e| e.to_s }} λ#{@variable}: #{@constraint}. #{@body})"
    end

    def ==(other : Abstraction)
        @variable == other.variable && @constraint == other.constraint && @body == other.body
    end

    def ==(other)
        false
    end
end

class Application
    property lhs : Term
    property rhs : Term

    def initialize(lhs : Term, rhs : Term)
        @lhs = lhs
        @rhs = rhs
    end

    def recurse(f : Term -> Term)
        Application.new(f.call(@lhs), f.call(@rhs))
    end

    def to_s(io)
        io << "(#{lhs} #{rhs})"
    end

    def ==(other : Application)
        @lhs == other.lhs && @rhs == other.rhs
    end

    def ==(other)
        false
    end
end

alias Term =
    Bool                        |
    Variable                    |
    Negation                    |
    Implication                 |
    Disjunction                 |
    Conjunction                 |
    UniversalQuantification     |
    ExistentialQuantification   |
    Abstraction                 |
    Application

def elim_impl(term : Term) : Term
    case term
    when Bool, Variable
        term
    when Implication
        Disjunction.new(Negation.new(elim_impl(term.lhs)), elim_impl(term.rhs))
    else
        term.recurse(->elim_impl(Term))
    end
end

def de_morgan(term : Term) : Term
    case term
    when Bool, Variable
        term
    when Negation
        term_rhs = term.rhs
        case term_rhs
        when Bool, Variable
            term
        when Negation
            term_rhs.rhs
        when Disjunction
            Conjunction.new(Negation.new(de_morgan(term_rhs.lhs)), Negation.new(de_morgan(term_rhs.rhs)))
        when Conjunction
            Disjunction.new(Negation.new(de_morgan(term_rhs.lhs)), Negation.new(de_morgan(term_rhs.rhs)))
        else
            Negation.new(term_rhs.recurse(->de_morgan(Term)))
        end
    else
        term.recurse(->de_morgan(Term))
    end
end

# P | (Q & R) == (P | Q) & (P | R)
def distribute(term : Term) : Term
    case term
    when Bool, Variable
        term
    when Disjunction
        term_rhs = term.rhs
        case term_rhs
        when Conjunction
            Conjunction.new(
                Disjunction.new(distribute(term.lhs), distribute(term_rhs.lhs)),
                Disjunction.new(distribute(term.lhs), distribute(term_rhs.rhs)))
        else
            term_lhs = term.lhs
            case term_lhs
            when Conjunction
                Conjunction.new(
                    Disjunction.new(distribute(term_lhs.lhs), distribute(term.rhs)),
                    Disjunction.new(distribute(term_lhs.rhs), distribute(term.rhs)))
            else
                term.recurse(->distribute(Term))
            end
        end
    else
        term.recurse(->distribute(Term))
    end
end

def apply_until_constant(term : Term, f : Term -> Term) : Term
    new_term = term
    loop do
        term = new_term
        new_term = f.call(term)
        break if new_term == term
    end
    new_term
end

class NegatableTerm
    property truth : Bool
    property variable : Term

    def initialize(truth : Bool, variable : Term)
        @truth = truth
        @variable = variable
    end

    def to_s(io)
        io << (truth ? variable : "¬#{variable}")
    end
end

alias AtomicTerm = Bool | NegatableTerm | Abstraction
alias ConjunctiveNormalForm = Set(Set(AtomicTerm))
alias ConjunctiveTree = Bool | Variable | Conjunction | Abstraction
alias DisjunctiveTree = Bool | Variable | Negation | Disjunction | Abstraction

def conjunctive_tree_to_set(tree : ConjunctiveTree) : Set(DisjunctiveTree)
    case tree
    when Bool
        Set(DisjunctiveTree) { tree }
    when Variable
        Set(DisjunctiveTree) { tree }
    when Disjunction
        Set(DisjunctiveTree) { tree }
    when Conjunction
        lhs = tree.lhs
        rhs = tree.rhs
        case lhs
        when DisjunctiveTree
            Set { lhs }
        when Conjunction
            conjunctive_tree_to_set(lhs)
        else
            Set(DisjunctiveTree).new
        end | case rhs
        when DisjunctiveTree
            Set { rhs }
        when Conjunction
            conjunctive_tree_to_set(rhs)
        else
            Set(DisjunctiveTree).new
        end
    else
        raise "Problem!"
    end
end

def disjunctive_tree_to_set(tree : DisjunctiveTree) : Set(AtomicTerm)
    case tree
    when Bool
        Set(AtomicTerm) { tree }
    when Variable
        Set(AtomicTerm) { NegatableTerm.new(true, tree) }
    when Abstraction
        Set(AtomicTerm).new() | tree.origin.map { |e| NegatableTerm.new(true, e) }.to_set
    when Negation
        rhs = tree.rhs
        case rhs
        when Variable
            Set(AtomicTerm) { NegatableTerm.new(false, rhs) }
        when Abstraction
            Set(AtomicTerm).new() | rhs.origin.map { |e| NegatableTerm.new(false, e) }.to_set
        when Bool
            Set(AtomicTerm) { !rhs }
        else
            raise "Problem1!"
        end
    when Disjunction
        lhs = tree.lhs
        rhs = tree.rhs
        case { lhs, rhs }
        when { DisjunctiveTree, DisjunctiveTree }
            disjunctive_tree_to_set(lhs) | disjunctive_tree_to_set(rhs)
        else
            raise "Problem2!"
        end
    else
        raise "Problem3!"
    end
end

def truth_value(disjunctive : Set(AtomicTerm)) : Bool?
    if disjunctive.all? { |e| e == false }
        return false
    end

    disjunctive.each { |atomic_term|
        case atomic_term
        when Bool
            if atomic_term
                return true
            end
        else
        end
    }

    disjunctive.each { |atomic_term|
        disjunctive.select { |x| x != atomic_term }.each { |t|
            if atomic_term.is_a? NegatableTerm
                if t.is_a? NegatableTerm
                    if atomic_term.variable == t.variable && atomic_term.truth != t.truth
                        return true
                    end
                end
            end
        }
    }
end

def truth_value(cnf : ConjunctiveNormalForm) : Bool?
    values = cnf.map { |e| truth_value(e) }
    if values.all? { |e| e == true }
        return true
    end

    if values.any? { |e| e == nil }
        return nil
    end

    return false
end

def apply_substitution(term : Term, variable : Variable, substitute : Term) : Term
    case term
    when Variable
        term == variable ? substitute : term
    when Bool
        term
    else
        term.recurse(->(t : Term) { apply_substitution(t, variable, substitute) })
    end
end

def beta_reduce(application : Application) : Term
    lhs = application.lhs
    rhs = application.rhs
    case lhs
    when Application
        beta_reduce(Application.new(beta_reduce(lhs), application.rhs))
    when Abstraction
        if reduce_fol(Implication.new(application.rhs, lhs.constraint))
            case rhs
            when Abstraction
                rhs.origin.add(lhs.variable)
            end
            apply_substitution(lhs.body, lhs.variable, application.rhs)
        else
            raise "Tried to apply #{lhs} to #{application.rhs}. Constraint not proven."
        end
    else
        application
    end
end

def reduce_fol(term : Term) : Bool?
    term = apply_until_constant(term, ->elim_impl(Term))
    term = apply_until_constant(term, ->de_morgan(Term))
    term = apply_until_constant(term, ->distribute(Term))
    
    case term
    when ConjunctiveTree
        set = conjunctive_tree_to_set term
        cnf = set.map { |e|
            case e
            when DisjunctiveTree
                disjunctive_tree_to_set(e)
            else
                raise "Problem!"
            end
        }.to_set
        truth_value(cnf)
    when DisjunctiveTree
        truth_value(disjunctive_tree_to_set(term))
    else
        return nil
    end
end

def abstraction(constraint : Term, name : String, &block : Variable -> Term)
    v = Variable.new(name)
    Abstraction.new(v, constraint, block.call(v))
end

macro lm(variable, constraint, block)
    abstraction({{ constraint }}, "{{ variable.name }}") { |{{ variable }}|
        {{ block }}
    }
end

macro make_term(expr)
    {% if expr.class_name == "Call" %}
        {% if expr.name == "-" %}
            {% lhs = expr.receiver %}
            {% rhs = expr.args[0] %}
            Implication.new(make_term({{ lhs }}), make_term({{ rhs }}))
        {% elsif expr.name == "+" %}
            Disjunction.new(make_term({{ expr.receiver }}), make_term({{ expr.args[0] }}))
        {% elsif expr.name == "*" %}
            Conjunction.new(make_term({{ expr.receiver }}), make_term({{ expr.args[0] }}))
        {% elsif expr.name == "|" %}
            Application.new(make_term({{ expr.receiver }}), make_term({{ expr.args[0] }}))
        {% elsif expr.name == "lm" %}
            lm({{ expr.args[0] }}, make_term({{ expr.args[1] }}), make_term({{ expr.args[2] }}))
        {% end %}
    {% elsif expr.class_name == "Not" %}
        Negation.new(make_term({{ expr.exp }}))
    {% elsif expr.class_name == "Expressions" %}
        make_term({{ expr.expressions[0] }})
    {% else %}
        {{ expr }}
    {% end %}
end

macro print_type(expr)
    {{ puts expr.class_name }}
end