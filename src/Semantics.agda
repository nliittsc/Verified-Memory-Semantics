module Semantics where

open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Maybe using (Maybe; nothing; just)
open import Function using (case_of_)

import Data.Nat as Nat
open import Data.Nat using (ℕ; zero; suc)

import Data.Fin as Fin
open import Data.Fin using (Fin)

import Data.Vec as Vec
open import Data.Vec using (Vec; []; _∷_; _[_]=_; _[_]≔_)
open import Data.Vec.Properties

--- --- ---


-- This datatype will label our semantics, thus making our
-- relation a labeled transition relation. The Request
-- constructor can be seen as a command by the CPU to load
-- an address from memory to the register. τ is the "Silent"
-- transition (τ is used to denote this by convention)
data Label {Target Address : Set} : Set where

  -- This label indicates a load instruction
  Load : Target → Address → Label

  -- These labels are "background instructions" that
  -- are "unobservable"
  τ : Target → Address → Label


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
  inc  = {!!}

  toBV : ℕ → BitVector w
  toBV zero = empty
  toBV (suc n) = inc (toBV n)

  fromBV : BitVector w → ℕ
  fromBV x = {!Vec.foldr ? ? ?!}


  -- Unit Tests --
  test₁ : (toBV {BW 4} zero) ≡ o ∷ o ∷ o ∷ o ∷ []
  test₁ = refl

  test₂ : inc (toBV {BW 4} zero) ≡ o ∷ o ∷ o ∷ i ∷ []
  test₂ = {!!}

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
        
  data _⟶₁[_]_ : State → Label → State → Set where

    -- Nathan: `mem [ addr ]= val` is a weaking of `val ≡ memAccess mem addr`.
    -- IMO, it's better because we have a lemma in the stdlib that lets us
    -- recover `memAccess mem addr ≡ val`, and we can now also use
    -- `mem [ addr ]= val` in proofs which require that type.

    -- Nathan: Where does regname come from? Should it be included in the Request?
    load : ∀ {mem : Memory} {addr : Address}
             {reg : RegFile} {regname : RegName}
             {val : Word}
         --→ val ≡ memAccess mem addr
         → mem [ addr ]= val 
           ------------------------
         → (mem , reg) ⟶₁[ Load regname addr ] (mem , reg [ regname ]≔ val)

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


  RegName : Set
  RegName = DMA.RegFile'.RegName

  Address : Set
  Address = DMA.Memory'.Address

  Memory : Set
  Memory = DMA.Memory'.Memory

  RegFile : Set
  RegFile = DMA.RegFile'.RegFile

  rowAddrWidthℕ = tagWidthℕ Nat.+ indexWidthℕ
  RowAddress = FinBitWidth (BW rowAddrWidthℕ)

  -- The type of total functions from Addresses to Tag,Index,Offset
  AddressBitifier : Set
  AddressBitifier = Address → Tag × Index × Offset

  -- The type of total fucntions which concatenate the tag and index
  -- to an address
  Squasher : Set
  Squasher = Tag → Index → RowAddress

  -- The type of total functions which yield data from memory
  Fetcher : Set
  Fetcher = Memory → RowAddress → Vec Word cacheRowSlotCount

  -- Function that 


  -- We can use a state machine approach for ⟶₂
  -- A configuration is a combination of the mutable memory and registers
  -- along with a state variable that represents what "process" we are
  -- currently doing.
  data Process : Set where

    Idle : Process
    Access : Process
    Allocate : Process
    Write : Word → Process

  -- The 'signature' is an abstract set of functions
  -- that yield an abstract implementation of the algorithm
  -- which does the cache and address manipulation
  record Signature : Set where
    field
      bitify : AddressBitifier
      fetch : Fetcher
      catbits : Squasher

  open Signature
      
  
  Config : Set
  Config = Process × Memory × RegFile × Cache

  --pattern _,_,_ a b c = a , (b , c)

  private
    variable
      reg-name : RegName
      Σ₀ : Signature
      addr : Address
      𝑚 : Memory
      𝑟 𝑟' : RegFile
      σ σ' : Cache
      tag : Tag
      index : Index
      offset : Offset

  data _⟶₂[_,_]_ : Config → Label → Signature → Config → Set where

    -- processor requests to do something with the address
    req-rule :  (Idle , 𝑚 , 𝑟 , σ) ⟶₂[ Load reg-name addr , Σ₀ ] (Access , 𝑚 , 𝑟 , σ)

    -- If a hit, proceed to attemp to write the value to a register
    hit-rule : ∀ {val}
      → bitify Σ₀ addr ≡ (tag , index , offset)
      → σ [ tag ﹐ index ﹐ offset ]= val
      → (Access , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Write val , 𝑚 , 𝑟 , σ)

    -- Write the value to the target register, then return to waiting for next request
    write-rule : ∀{val target-register}
      → 𝑟 [ target-register ]≔ val ≡ 𝑟'
      → (Write val , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Idle , 𝑚 , 𝑟' , σ)

    -- We can't provide a proof of a cache hit, therefore we can only apply this reduction
    miss-rule :
      (Access , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Allocate , 𝑚 , 𝑟 , σ)

    -- We allocate a new line in the cache (thus updating it), then go back to
    -- comparing tags. The idea _now_ we can provide a proof of a cache hit and
    -- successfully move on to the write stage
    allocate-rule : ∀{row addr' line}
      → bitify Σ₀ addr ≡ (tag , index , offset)
      → catbits Σ₀ tag index ≡ addr'
      → fetch Σ₀ 𝑚 addr' ≡ row
      → CL true tag row ≡ line
      → σ [ index ]≔ line ≡ σ'
      → (Allocate , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Access , 𝑚 , 𝑟 , σ')


  -- This constructor represents a cache hit for a given address
  -- To construct it is to provide both the existence of
  -- the cache, address, signature, and a proof that we had a hit
  data ⟨_﹐_⟩⇓Hit : Cache → Address → Set where

    hittable : ∀{tag' row} (σ : Cache) (addr : Address) (Σ₀ : Signature)
      → bitify Σ₀ addr ≡ (tag , index , offset)
      → σ [ index ]= CL true tag' row
      → tag ≡ tag'
      → ⟨ σ ﹐ addr ⟩⇓Hit


  -- This lemma asserts that if we apply the miss-rule and allocate-rules
  -- in succession, then we can construct a proof of a cache hit for
  -- the appropriate line
  Lemma : ∀ {reg-name} addr σ' Σ₀
    → (Access , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Allocate , 𝑚 , 𝑟 , σ)
    → (Allocate , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Access , 𝑚 , 𝑟 , σ')
    → ⟨ σ' ﹐ addr ⟩⇓Hit
  Lemma addr σ' Σ₀ miss-rule
        (allocate-rule {tag = tag} {index} {offset} {row = row} {line = line}
        bitify-≡ f₁ f₂ ≡-newline σ[index]≔line≡σ') =
          let fact₀ : σ' [ index ]= line
              fact₀ = subst (λ s → s [ index ]= line) σ[index]≔line≡σ' ([]≔-updates _ index)

              fact₁ : σ' [ index ]= CL true tag row
              fact₁ = subst (λ l → σ' [ index ]= l) (sym (≡-newline)) fact₀

              proof : ⟨ σ' ﹐ addr ⟩⇓Hit
              proof = hittable σ' addr Σ₀ bitify-≡ fact₁ refl
          in proof
