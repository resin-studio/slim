/-
-- slim logic sketch --

-- label --
l ::= [a-z_]+

-- identifier --
x ::= [a-zA-Zα-ζ][a-zA-Zα-ζ0-9_]*

-- term --
t ::=
  _                            -- irrelevant pattern / inferred expression
  t : τ                        -- typed pattern
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
  τ                            -- type as a term of type * and sort **

-- term sugar --
⟦(t1 , t2)⟧  ~> (.left ⟦t1⟧, .right ⟦t2⟧)

-- term notes --
we collapse the notion of type with term to be consistent with Python 

-- type --
τ ::=
  x             -- variable type
  ?l            -- unit variant type
  #l : τ        -- variant type
  .l : τ        -- record type
  τ & τ         -- intersection type
  τ | τ         -- union type
  τ -> τ        -- implication type
  ∀ x . τ       -- universal type of sort ** with type param of any kind of universe 1
  ∃ x . τ       -- existential type of sort ** with type param of any kind of universe 1
  μ x . τ       -- inductive type of kind * with type param of kind *
  { t | t : τ } -- relational type
  L             -- kind as type of kind **



-- type notes --
- universal and existential types quantify over types of kind *, resulting in types of kind **
- these type quantifiers are primitive in this weak logic
- in a stronger dependently typed / higher kinded logic, these types would be subsumed by implication 

-- composite types defined in terms of subtyping combinators --
A /\ B = .left:A & .right:B -- product
A \/ B = #left:A | #right:B -- sum


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