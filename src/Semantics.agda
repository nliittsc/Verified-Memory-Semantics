module Semantics where

open import Data.Bool
open import Data.Product
open import Data.List using (List)
open import Data.Vec using (Vec; _∷_; lookup; _[_]≔_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import BitVector

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

MemVal : Set
MemVal = ℕ








Address : ℕ → Set
Address n = Fin n

-- A contiguous array of memory values
-- lookup is by "offset" (index of element)
Memory : ℕ → Set
Memory n = Vec MemVal n

-- These are abstract semantics
memlookup : Memory n → Address n → MemVal
memlookup = lookup








RegName : ℕ → Set
RegName n = Fin n

RegFile : ℕ → Set
RegFile n = Vec MemVal n

reglookup : RegFile n → RegName n → MemVal
reglookup = lookup






State : ℕ → ℕ → Set
State n m = Memory n × RegFile m
    
-- Semantics for memory
data _⟶₁_ : State n m → State n m → Set where

  load : ∀ {mem : Memory n} {addr : Address n}
           {reg : RegFile m} {regname : RegName m}
           {val : MemVal}
    → memlookup mem addr ≡ val
      -----------------
    → (mem , reg) ⟶₁ (mem , reg [ regname ]≔ val)





record CacheLine (width : ℕ) : Set where
  constructor CL
  field
    valid : Bool
    tag : ℕ
    row : Vec MemVal width

-- Cache is a vector of vectors, with length-number of CacheLines each
-- containing width-number of memory values.
Cache : ℕ → ℕ → Set
Cache length width = Vec (CacheLine width) length

private
  variable
    l w : ℕ

    tag : ℕ
    index : Fin l
    offset : Fin w

postulate
  cachelookup : Cache l w → ℕ × Fin l × Fin w → Maybe MemVal
  -- Nathan: next let's prove that storing a thing in the cache means
  -- that we can look it up
  cachenamer : Address n → ℕ × Fin l × Fin w
  catbits : ℕ → Fin l → Address n
  fetchrow : Address n → ℕ → Vec MemVal w

-- Semantics for direct-mapped cache
data _⟶₂_ : State n m × Cache l w → State n m × Cache l w → Set where

  -- When a value is in the cache, a hit occurs and writes to the regfile.
  hit : ∀ {mem : Memory n} {addr : Address n}
          {reg : RegFile m} {regname : RegName m}
          {cache : Cache l w}
          {val : MemVal}
    → cachenamer addr ≡ (tag , index , offset)
    → cachelookup cache (tag , index , offset) ≡ just val
      ---------------------------------------------------
    → ((mem , reg) , cache) ⟶₂ ((mem , reg [ regname ]≔ val) , cache)

  -- When a value is not in the cache, a miss occurs and writes to the
  -- cache. It can be followed by a hit.
  miss : ∀ {mem : Memory n} {addr : Address n}
           {reg : RegFile m}
           {cache : Cache l w}
           {tag++index : Address n} -- Must be a multiple of w
    → cachenamer addr ≡ (tag , index , offset)
    → cachelookup cache (tag , index , offset) ≡ nothing
    → catbits tag index ≡ tag++index
      ------------------------------
    → ((mem , reg) , cache) ⟶₂
      ((mem , reg) , cache [ index ]≔ CL true tag (fetchrow tag++index w))

  -- get an address and a regname
  --
  -- (ABOVE IS ALSO IN MEMORY MODEL; BELOW IS ONLY IN CACHE)
  -- 
  -- break addr into tag|index|offset
  --
  -- log2n is width of addr in binary
  -- log2l is width of index in binary
  -- log2w is width of offset in binary
  -- log2n - log2l - log2w is width of tag in binary
  --
  -- hit or miss?
  --
  -- lookup the line for the index
  -- check whether the valid bit is set
  -- compare the tag in the line to the given tag
  -- valid bit set and same tag?
  -- hit: jump down to the hit case below
  -- miss: continue 
  --
  -- miss case:
  -- 
  -- set up cache line
  --    starting from (tag|index|00000)
  --    copy width MemVals
  --    store them into the CacheLine row field
  --    set the valid bit on the CacheLine
  --    set the tag on the CacheLine
  -- cache [ index ]≔ new_cache_line
  --    (if we cared about stores, we'd need to writeback the evicted data here)
  -- continue to hit case below
  -- 
  -- hit case:
  --
  -- val = lookup (row cacheline) offset
  -- 
  -- (ABOVE IS ONLY IN CACHE; BELOW IS ALSO IN MEMORY MODEL)
  -- 
  -- reg [ regname ]≔ val
