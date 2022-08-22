-- slim logic --
/-

-- symbol --
s ::= [a-zA-Z]+


-- term --
t ::=
  $s                           -- unit variant (singleton)
  #s t                         -- variant (singleton)
  match t (case #s t => t ...) -- variant elimination
  .s t                         -- record (singleton)
  t.s                          -- record elimination
  t => t                       -- function abstraction
  t t                          -- function application
  fix                          -- fixpoint combinator


-- type --
T ::=
  s             -- symbol type
  ?s     -- unit variant type
  #s : T     -- variant type
  .s : T     -- record type
  T & T        -- intersection type
  T | T        -- union type
  T -> T        -- implication type
  ∀ T . T      -- universal type
  ∃ T . T      -- existential type
  μ T . T       -- inductive type
  { t | t : T } -- relational type

-- composite types defined in terms of subtyping combinators --
A /\ B = .left:A & .right:B -- product
A \/ B = #left:A | #right:B -- sum


-- kind --
K ::=


-- context --
Γ ::= 

-- examples --
def List T = ?nil | #cons:(T /\ List T)

def Nat = μ Nat . ?zero | #succ:Nat

def ListLen T = (?nil /\ ?zero) | {(#cons (_ : T, xs), #succ n) | (xs, n) : ListLen T}
Note: clauses based on typing membership in relational type
- obviate the need for SMT solving, 
- allow reusing definitions for both checking and refinement

def 4 = #succ (#succ (#succ (#succ $zero)))

def List4 = {xs | (xs, 4) : ListLen Nat}

%check 1 :: 2 :: 3 :: 4 :: $nil











-/