module Semantics where

open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; nothing; just)
open import Function using (case_of_)

import Data.Nat as Nat
open import Data.Nat using (ℕ; zero; suc)

import Data.Fin as Fin
open import Data.Fin using (Fin)

import Data.Vec as Vec
open import Data.Vec using (Vec; []; _∷_; _[_]=_; _[_]≔_)

--- --- ---

module BitWidth where
  data BitWidth : Set where
    BW : ℕ → BitWidth
  
  -- What range of decimal numbers is covered by a given bitwidth?
  bitWidthRange : BitWidth → ℕ
  bitWidthRange (BW w) = 2 Nat.^ w
  
  -- A ℕ which could be represented by a given BitWidth.
  FinBitWidth : BitWidth → Set
  FinBitWidth bw = Fin (bitWidthRange bw)

open BitWidth

module BitVector where
  data Bit : Set where
    i : Bit
    o : Bit
  -- empty (bitvec of zeros of inferred width)
  -- something to break a bitvec into pieces with
  -- something to squish them back together with
  -- function to measure the length of a bitvec
  -- conversions between bitvecs and nats
  BitVector : BitWidth → Set
  BitVector (BW w) = Vec Bit w

  private
    variable
      w : BitWidth

  empty : BitVector w
  empty {BW w} = Vec.replicate o

  inc : BitVector w → BitVector w
  inc = {!!}

  toBV : ℕ → BitVector w
  toBV zero = empty
  toBV (suc n) = inc (toBV n)

  fromBV : BitVector w → ℕ
  fromBV x = {!Vec.foldr ? ? ?!}

Word : Set
Word = ℕ

module Memory {addrWidth : BitWidth} where
  Address : Set
  Address = FinBitWidth addrWidth

  memWordCount : ℕ 
  memWordCount = bitWidthRange addrWidth

  Memory : Set
  Memory = Vec Word memWordCount

  memAccess : Memory → Address → Word
  memAccess = Vec.lookup

module RegFile {regCount : ℕ} where
  RegName : Set
  RegName = Fin regCount

  RegFile : Set
  RegFile = Vec Word regCount

  regAccess : RegFile → RegName → Word
  regAccess = Vec.lookup

module DirectMemoryAccess {addrWidth regCount} where
  open module Memory' = Memory {addrWidth}
  open module RegFile' = RegFile {regCount}

  State : Set
  State = Memory × RegFile
        
  data _⟶₁_ : State → State → Set where
  
    load : ∀ {mem : Memory} {addr : Address}
             {reg : RegFile} {regname : RegName}
             {val : Word}
         → val ≡ memAccess mem addr
           ------------------------
         → (mem , reg) ⟶₁ (mem , reg [ regname ]≔ val)

module DirectlyMappedCacheMemoryAccess
       {addrWidthℕ regCount indexWidthℕ offsetWidthℕ}
       {iw+ow≤aw : indexWidthℕ Nat.+ offsetWidthℕ Nat.≤ addrWidthℕ}
       where
  open module DMA = DirectMemoryAccess {BW addrWidthℕ} {regCount}

  tagWidthℕ : ℕ
  tagWidthℕ = addrWidthℕ Nat.∸ (indexWidthℕ Nat.+ offsetWidthℕ)

  Tag : Set
  Tag = FinBitWidth (BW tagWidthℕ)

  Index : Set
  Index = FinBitWidth (BW indexWidthℕ)

  Offset : Set
  Offset = FinBitWidth (BW offsetWidthℕ)

  -- also define Tag|Index (fetchrow arg)

  cacheLineCount : ℕ
  cacheLineCount = bitWidthRange (BW indexWidthℕ)

  cacheRowSlotCount : ℕ
  cacheRowSlotCount = bitWidthRange (BW offsetWidthℕ)

  record CacheLine : Set where
    constructor CL
    field
      valid : Bool
      tag : Tag
      row : Vec Word cacheRowSlotCount
      -- λ offset → Word

  Cache : Set
  Cache = Vec CacheLine cacheLineCount
  -- λ index → cacheLine

  data _[_﹐_﹐_]=_ : Cache → Tag → Index → Offset → Word → Set where
    cacheAccess : ∀ cache tag index offset {row} {val}
        → cache [ index ]= CL true tag row
        → row [ offset ]= val
        → cache [ tag ﹐ index ﹐ offset ]= val


