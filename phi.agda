module phi where

open import Relation.Nullary using (yes; no)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≥?_)
open import Data.Product using (Σ-syntax; _,_)
open import Data.String using (String; _≟_)

Id : Set
Id = String

data PartialObject : Set
data Term : Set
data AttrValue : Set

infixl 19 _,_↦_
infixl 21 _∙_

data AttrValue where
  ∅ : AttrValue
  !_ : Term → AttrValue

data PartialObject where
  ⟦ : PartialObject
  ⟦_↦_ : Id → AttrValue → PartialObject
  _,_↦_ : PartialObject → Id → AttrValue → PartialObject

data Term where
  _⟧ : PartialObject → Term
  _∙_ : Term → Id → Term
  _⟨_↦_⟩ : Term → Id → Term → Term
  ρ_ : ℕ → Term

pattern ⟦⟧ = ⟦ ⟧

data _∙_:=_ : PartialObject → Id → AttrValue → Set where
  head₁ : ∀{x t}
      ------------------
    → (⟦ x ↦ t) ∙ x := t

  head₂ : ∀{o x t}
      ------------------
    → (o , x ↦ t) ∙ x := t

  tail : ∀{o x y u t}
    → o ∙ x := t
      --------------------
    → (o , y ↦ u) ∙ x := t

data _-_:=_ : PartialObject → Id → PartialObject → Set where
  head-₁ : ∀{x}
      ------------------
    → (⟦ x ↦ ∅) - x := ⟦

  head-₂ : ∀{o x}
      ------------------
    → (o , x ↦ ∅) - x := o

  tail- : ∀{o o' x y u }
    → o - x := o'
      --------------------
    → (o , y ↦ u) - x := (o' , y ↦ u)

_[_++] : PartialObject → ℕ → PartialObject
_[_+] : Term → ℕ → Term

⟦ [ i ++] = ⟦
(⟦ x ↦ ∅) [ i ++] = ⟦ x ↦ ∅
(⟦ x ↦ (! t)) [ i ++] = ⟦ x ↦ (! (t [ i +]))
(o , x ↦ ∅) [ i ++] = (o [ i ++]) , x ↦ ∅
(o , x ↦ (! t)) [ i ++] = (o [ i ++]) , x ↦ (! (t [ i +]))

(o ⟧) [ i +] = (o [ (suc i) ++]) ⟧
(t ∙ x) [ i +] = (t [ i +]) ∙ x
(t ⟨ x ↦ u ⟩) [ i +] = (t [ i +]) ⟨ x ↦ (u [ i +]) ⟩
(ρ n) [ i +] with n ≥? i
... | yes _ = ρ (suc n)
... | no _ = ρ n

_[_↦↦_] : PartialObject → ℕ → Term → PartialObject
_[_↦_] : Term → ℕ → Term → Term

⟦ [ i ↦↦ u ] = ⟦
(⟦ x ↦ ∅) [ i ↦↦ u ] = ⟦ x ↦ ∅
(o , x ↦ ∅) [ i ↦↦ u ] = (o [ i ↦↦ u ]) , x ↦ ∅
(⟦ x ↦ (! t)) [ i ↦↦ u ] = ⟦ x ↦ (! (t [ i ↦ u ]))
(o , x ↦ (! t)) [ i ↦↦ u ] = (o [ i ↦↦ u ]) , x ↦ (! (t [ i ↦ u ]))

(o ⟧) [ i ↦ u ] = (o [ (suc i) ↦↦ (u [ zero +]) ]) ⟧
(t ∙ x) [ i ↦ u ] = (t [ i ↦ u ]) ∙ x
(t₁ ⟨ x ↦ t₂ ⟩) [ i ↦ u ] = (t₁ [ i ↦ u ]) ⟨ x ↦ (t₂ [ i ↦ u ]) ⟩
(ρ n) [ i ↦ u ] with n Data.Nat.≟ i
... | yes _ = u
... | no _  = ρ n

data _⇒_ : Term → Term → Set
data _⇒⇒_ : PartialObject → PartialObject → Set

data _⇒⇒_ where
  ξ′₁ :
      ------
      ⟦ ⇒⇒ ⟦

  ξ'₂ : ∀ {x t t'}
    → t ⇒ t'
      -----------------------
    → (⟦ x ↦ (! t)) ⇒⇒ (⟦ x ↦ (! t'))

  ξ'₃ : ∀{o x t t'}
    → t ⇒ t'
      -----------------------
    → (o , x ↦ (! t)) ⇒⇒ (o , x ↦ (! t'))

  ξ'₄ : ∀{o o' x t}
    → o ⇒⇒ o'
      -----------------------
    → (o , x ↦ t) ⇒⇒ (o' , x ↦ t)

data _⇒_ where
  ξₐ : ∀{x t t'}
    → (t ⇒ t')
      ------------------
    → (t ∙ x) ⇒ (t' ∙ x)

  ξᵢ₁ : ∀{x t t' u}
    → (t ⇒ t')
      -------------------
    → (t ⟨ x ↦ u ⟩) ⇒ (t' ⟨ x ↦ u ⟩)

  ξᵢ₂ : ∀{x t u u'}
    → (u ⇒ u')
      -------------------
    → (t ⟨ x ↦ u ⟩) ⇒ (t ⟨ x ↦ u' ⟩)

  ξₒ : ∀{o o'}
    → (o ⇒⇒ o')
      -------------------
    → (o ⟧) ⇒ (o' ⟧)

  βₐ : ∀{x o t}
    → (o ∙ x := (! t))
      ----------------------------------
    → ((o ⟧) ∙ x) ⇒ (t [ zero ↦ (o ⟧) ])

  βₐ' : ∀{x o t}
    → (o ∙ "𝜑" := t)
      ----------------------------------
    → ((o ⟧) ∙ x) ⇒ ((o ⟧) ∙ "𝜑") ∙ x

  βᵢ : ∀{o o' x u}
    → (o - x := o')
     --------------------
    → ((o ⟧) ⟨ x ↦ u ⟩) ⇒ ((o' , x ↦ (! (u [ 0 +]))) ⟧)

data _⇒*_ : Term → Term → Set where
  refl⇒* : ∀{t}
      ------
    → t ⇒* t

  _⇒⟨_⟩_ : ∀ t {t' t''}
    → t ⇒ t'
    → t' ⇒* t''
      ------------
    → t ⇒* t''

t⇒*u2t∙x⇒*u∙x : ∀{x t u}
  → t ⇒* u
    ------------------
  → (t ∙ x) ⇒* (u ∙ x)
t⇒*u2t∙x⇒*u∙x refl⇒* = refl⇒*
t⇒*u2t∙x⇒*u∙x {x} (t ⇒⟨ p ⟩ r) = (t ∙ x) ⇒⟨ ξₐ p ⟩ (t⇒*u2t∙x⇒*u∙x r)

_⇒*⟨_⟩_ : ∀ t {t' t''}
  → t ⇒* t'
  → t' ⇒ t''
    ---------
  → t ⇒* t''
t ⇒*⟨ refl⇒* ⟩ p₂ = t ⇒⟨ p₂ ⟩ refl⇒*
t ⇒*⟨ .t ⇒⟨ p ⟩ p₁ ⟩ p₂ = t ⇒⟨ p ⟩ (_ ⇒*⟨ p₁ ⟩ p₂ )

get : ∀(x : Id) (o : PartialObject) {t} -> Maybe (o ∙ x := t)
get x ⟦ = nothing
get x (⟦ y ↦ t) with x ≟ y
... | yes _ = just head₁
... | no _ = nothing
get x (o , y ↦ t) with x ≟ y
... | yes _ = just {!!}
... | no _ = {!!}

whnf : ∀(t : Term) → Σ[ t' ∈ Term ] t ⇒* t'
--
whnf (o ⟧) = o ⟧ , refl⇒*
--
whnf (t ∙ x) with whnf t
whnf (t ∙ x) | o ⟧ , p with get x o
whnf (t ∙ x) | o ⟧ , p | nothing with get "𝜑" o
whnf (t ∙ x) | o ⟧ , p | nothing | nothing = (o ⟧) ∙ x , t⇒*u2t∙x⇒*u∙x p
whnf (t ∙ x) | o ⟧ , p | nothing | just _ = ((o ⟧) ∙ "𝜑") ∙ x , (t ∙ x ⇒*⟨ t⇒*u2t∙x⇒*u∙x p ⟩ {!!})
whnf (t ∙ x) | o ⟧ , p | just ∅ = (o ⟧) ∙ x , t⇒*u2t∙x⇒*u∙x p
whnf (t ∙ x) | o ⟧ , p | just (! u) = u [ zero ↦ (o ⟧) ] , (t ∙ x ⇒*⟨ t⇒*u2t∙x⇒*u∙x p ⟩ (βₐ {!!}) )
whnf (t ∙ x) | t' , p = t' ∙ x , {!!}
--
whnf (t ⟨ x ↦ u ⟩) with whnf t
whnf (t ⟨ x ↦ u ⟩) | o ⟧ , p with get x o
whnf (t ⟨ x ↦ u ⟩) | o ⟧ , p | nothing = (o ⟧) ⟨ x ↦ u ⟩ , {!!}
whnf (t ⟨ x ↦ u ⟩) | o ⟧ , p | just ∅ = (o , x ↦ (! u)) ⟧ , {!!}
whnf (t ⟨ x ↦ u ⟩) | o ⟧ , p | just (! _) = (o ⟧) ⟨ x ↦ u ⟩ , {!!}
whnf (t ⟨ x ↦ u ⟩) | t' , p = t' ⟨ x ↦ u ⟩ , {!!}
--
whnf (ρ i) = ρ i , refl⇒*

-- FIXME: how to remove redundant parentheses?
example₁ : Term
example₁ =
  ((⟦ "x" ↦ (! (ρ 0) ∙ "y")
   , "y" ↦ (! ⟦⟧)
  )⟧) ∙ "x"
