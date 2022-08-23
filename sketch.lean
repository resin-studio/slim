/-
-- slim logic sketch --

-- label --
l ::= [a-z_]+

-- identifier --
x ::= [a-zA-Zα-ζ][a-zA-Zα-ζ0-9_]*

-- term --
t ::=
  _                            -- irrelevant pattern / inferred expression
  t : τ                        -- typed pattern where τ : κ : **
  x                            -- variable expression / pattern
  $l                           -- unit variant expression / pattern
  #l t                         -- variant expression / pattern
  match t (case #l t => t ...) -- variant elimination
  .l t, ...                    -- record expression / pattern
  t.l                          -- record elimination 
  t => t                       -- function abstraction
  t t                          -- function application
  let t = t in t               -- binding
  fix t                        -- recursion
  τ                            -- type as term : *

-- term sugar --
⟦(t1 , t2)⟧  ~> (.left ⟦t1⟧, .right ⟦t2⟧)

-- term notes --
we collapse the notion of type with term to be consistent with Python's unstratified syntax
related work: 1ml by Andreas Rossberg - https://people.mpi-sws.org/~rossberg/1ml/1ml.pdf

-- type --
τ ::=
  x             -- variable type : *
  ?l            -- unit variant type : *
  #l : τ        -- variant type : *
  .l : τ        -- record type : *
  τ & τ         -- intersection type : *
  τ | τ         -- union type : *
  τ -> τ        -- implication type where τ : * or higher kind where τ : **
  μ x . τ       -- inductive type : * where x : κ : ** 
  { t | t : τ } -- relational type : * where τ : * 
  *             -- ground kind : **
  *<τ>          -- ground kind singleton : **
  ∀ x . τ       -- universal type : ** where x : κ : ** (predicative) or x : ** (impredicative)
  ∃ x . τ       -- existential type : ** where x : κ : ** (predicative) or x : ** (impredicative)

-- type notes --
A kind is a semantic notion
- a type belongs to a kind, which belongs to **
- κ where τ : κ : **

predicativity is recognized by placing treating quantifiers as large types of **

-- type notes --
- universal and existential types quantify over types of kind *, resulting in types of kind **
- these type quantifiers are primitive in this weak logic
- in a stronger dependently typed / higher kinded logic, these types would be subsumed by implication 

-- composite types defined in terms of subtyping combinators --
A /\ B = .left:A & .right:B -- product
A \/ B = #left:A | #right:B -- sum

-- TODO: get rid of kind syntax --
A kind is just a type of sort 1, rathern than sort 0 

-- lower kind --
L ::=
  *         -- kind of ground terms, type of types 
  * -> L    -- kind of type constructors

-- kind --
K ::=  
  L       -- lower kind 
  **      -- higher kind 


-- context --
Γ ::= 

-- examples --
let list = α : * => μ list α . ?nil | #cons:(α /\ list α)

let nat = μ nat . ?zero | #succ:nat

let list_len = α : * => μ list_len . (?nil /\ ?zero) | {(#cons (_ : α, xs), #succ n) | (xs, n) : list_len α}
Note: clauses based on typing membership in relational type
- obviate the need for outsourcing to SMT solver, 
- allow reusing definitions for both checking and refinement

let 4 = #succ (#succ (#succ (#succ $zero)))

let list_4 = {xs | (xs, 4) : list_len nat}

%check 1 :: 2 :: 3 :: 4 :: $nil : list_4











-/