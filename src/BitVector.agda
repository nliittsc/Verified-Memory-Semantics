module BitVector where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O -- only recurse on carry bit

b0 : Bin
b0 = ⟨⟩ O
b1 : Bin
b1 = ⟨⟩ I
b2 : Bin
b2 = ⟨⟩ I O
b3 : Bin
b3 = ⟨⟩ I I
b4 : Bin
b4 = ⟨⟩ I O O
b5 : Bin
b5 = ⟨⟩ I O I

_ : inc b0 ≡ b1
_ = refl
_ : inc b1 ≡ b2
_ = refl
_ : inc b2 ≡ b3
_ = refl
_ : inc b3 ≡ b4
_ = refl
_ : inc b4 ≡ b5
_ = refl
_ : inc (⟨⟩ O O I O O) ≡ ⟨⟩ O O I O I -- inc4≡5 with leading zeros
_ = refl
_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O -- inc11≡12
_ = refl

to   : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 0 ≡ b0
_ = refl
_ : to 1 ≡ b1
_ = refl
_ : to 2 ≡ b2
_ = refl
_ : to 3 ≡ b3
_ = refl
_ : to 4 ≡ b4
_ = refl

binlen : Bin → ℕ
binlen ⟨⟩ = zero
binlen (b O) = suc (binlen b)
binlen (b I) = suc (binlen b)

_ : binlen ⟨⟩ ≡ 0
_ = refl
_ : binlen (⟨⟩ O) ≡ 1
_ = refl
_ : binlen (⟨⟩ I O) ≡ 2
_ = refl
_ : binlen (⟨⟩ O O I) ≡ 3
_ = refl
_ : binlen (⟨⟩ O O I O O) ≡ 5
_ = refl

fromAtPow : ℕ -> Bin -> ℕ
fromAtPow _ ⟨⟩ = zero
fromAtPow p (b O) = fromAtPow (p + 1) b
fromAtPow p (b I) = fromAtPow (p + 1) b + 2 ^ p

from : Bin → ℕ
from = fromAtPow 0

_ : from b0 ≡ 0
_ = refl
_ : from b1 ≡ 1
_ = refl
_ : from b2 ≡ 2
_ = refl
_ : from b3 ≡ 3
_ = refl
_ : from b4 ≡ 4
_ = refl

_ : from ⟨⟩ ≡ 0 -- the empty bin
_ = refl
_ : from (⟨⟩ O O O) ≡ 0 -- zero with leading zeros
_ = refl
_ : from (⟨⟩ O I O) ≡ 2 -- two with leading zeros
_ = refl
