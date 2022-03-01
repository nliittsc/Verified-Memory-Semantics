module Semantics where

open import Data.Bool
open import Data.Product
open import Data.List using (List)
open import Data.Vec using (Vec; _∷_; lookup; _[_]≔_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)



-- two transition systems (S₁, Actions, ⟶₁), (S₂, Actions, ⟶₂)
-- a relation R ⊂ S₁ × S₂ is a "weak simulation" (observation congruence) iff ∀(p, q) ∈ R
-- Actions ≡ { τ }
-- α ∈ Actions 
-- 1. if p ⟶₁ p' implies ∃q' such that q' ∈ S₂ : q ⟶₂* q'

-- R ≡ ≈
-- s ≈ (s' , cache) ⇔ s ≡ s'





private
  variable
    n m : ℕ


postulate
  --Memory : ℕ → Set
  Register : ℕ → Set
  --Address : Set
  
  --RegName : Set

Address : ℕ → Set
Address n = Fin n

MemVal : Set
MemVal = ℕ

RegFile : ℕ → Set
RegFile n = Vec MemVal n

RegName : ℕ → Set
RegName n = Fin n

-- A contiguous array of memory values
-- lookup is by "offset" (index of element)
Memory : ℕ → Set
Memory n = Vec MemVal n

-- These are abstract semantics
memlookup : Memory n → Address n → MemVal
memlookup = lookup

reglookup : RegFile n → RegName n → MemVal
reglookup = lookup



State : ℕ → ℕ → Set
State n m = Memory n × Register m




data ValidAddr : Address → Set where

data ValidName : RegName → Set where
    
data _⟶₁_ : State n m → State n m → Set where

  load : ∀ {addr : Address} {regname : RegName} {mem : Memory n} {reg : Register m}
    → ValidAddr addr
    → ValidName regname
      -----------------
    → (mem , reg) ⟶₁ (mem , reg [ regname ]≔ memlookup mem addr)

  
-- data _⟶₂_ : State n m × Cache → State n m × Cache → Set where
