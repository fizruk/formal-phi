inductive OptionalAttr where
  | void : OptionalAttr
  | attached : Attr → OptionalAttr

structure AttrTerm where
  attr : String
  term : Term

def sorted : (List AttrTerm) → Bool
| [] => true
| [_] => true
| (List.cons x (List.cons y zs)) => (x.attr < y.attr) && sorted (List.cons y zs)

inductive Object where
  | empty : Object
  | cons : (l : List AttrTerm) → sorted l → Object

inductive Term : Type where
  | loc : ℕ → Term
  | dot : Term → Attr → Term
  | app : Term → Attr → Term → Term
  | obj : Object → Term
open Term

-- def whnf : Term → Term
-- | loc n => loc n
-- | ...
