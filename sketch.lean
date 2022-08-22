/-
-- slim logic sketch --

-- symbol --
s ::= [a-zA-Zα-ζ]+


-- term --
t ::=
  $s                           -- unit variant
  #s t                         -- variant
  match t (case #s t => t ...) -- variant elimination
  .s t, ...                    -- record
  t.s                          -- record elimination
  t => t                       -- function abstraction
  t t                          -- function application
  fix t                        -- recursion

-- term sugar --
(t , t) = (.left t , .right t)

-- type --
T ::=
  s             -- symbol type
  ?s     -- unit variant type
  #s : T     -- variant type
  .s : T     -- record type
  T & T        -- intersection type
  T | T        -- union type
  T -> T        -- implication type
  ∀ s . T      -- universal type
  ∃ s . T      -- existential type
  μ s . T       -- inductive type
  { t | t : T } -- relational type

Notes: 
- universal and existential types quantify over types of kind *, resulting in types of kind **
- these type quantifiers are primitive in this weak logic
- in a stronger dependently typed / higher kinded logic, these types would be subsumed by implication 

-- composite types defined in terms of subtyping combinators --
A /\ B = .left:A & .right:B -- product
A \/ B = #left:A | #right:B -- sum


-- kind --
K ::=
  *      -- kind of ground types
  * -> K -- kind of type constructors

-- higher kind --
H ::= **


-- context --
Γ ::= 

-- examples --
def list α = μ list_α . ?nil | #cons:(α /\ list_α)

def nat = μ nat . ?zero | #succ:nat

def list_len α = μ list_lenα . (?nil /\ ?zero) | {(#cons (_ : α, xs), #succ n) | (xs, n) : list_len_α}
Note: clauses based on typing membership in relational type
- obviate the need for SMT solving, 
- allow reusing definitions for both checking and refinement

def 4 = #succ (#succ (#succ (#succ $zero)))

def list_4 = {xs | (xs, 4) : list_len nat}

%check 1 :: 2 :: 3 :: 4 :: $nil : list_4











-/