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
  open module Memory' = Memory {addrWidth}  public
  open module RegFile' = RegFile {regCount} public

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

  tagWidthℕ = addrWidthℕ Nat.∸ (indexWidthℕ Nat.+ offsetWidthℕ)
  rowAddrWidthℕ = tagWidthℕ Nat.+ indexWidthℕ

  tagWidth = BW tagWidthℕ
  indexWidth = BW indexWidthℕ
  offsetWidth = BW offsetWidthℕ
  rowAddressWidth = BW rowAddrWidthℕ

  Tag = FinBitWidth tagWidth
  Index = FinBitWidth indexWidth
  Offset = FinBitWidth offsetWidth
  RowAddress = FinBitWidth rowAddressWidth

  cacheLineCount : ℕ
  cacheLineCount = bitWidthRange (BW indexWidthℕ)

  cacheRowSlotCount : ℕ
  cacheRowSlotCount = bitWidthRange (BW offsetWidthℕ)

  Row = Vec Word cacheRowSlotCount

  record CacheLine : Set where
    constructor CL
    field
      valid : Bool
      tag : Tag
      row : Row
      -- λ offset → Word

  Cache : Set
  Cache = Vec CacheLine cacheLineCount
  -- λ index → cacheLine

  data _[_﹐_﹐_]=_ : Cache → Tag → Index → Offset → Word → Set where
    cacheAccess : ∀ cache tag index offset {row} {val}
        → cache [ index ]= CL true tag row
        → row [ offset ]= val
        → cache [ tag ﹐ index ﹐ offset ]= val

  -- The 'signature' is an abstract set of functions
  -- that yield an abstract implementation of the algorithm
  -- which does the cache and address manipulation
  record Signature : Set where
    field
      bitify' : Address → Tag × Index × Offset
      catbits' : Tag → Index → RowAddress
      fetch' : Memory → RowAddress → Row

  open Signature

  -- think of fetching a row as a window into memory
  -- dropping all the values in memory up to the rowAddr
  -- from there, taking (bitWidthRange offsetWidth) values
  -- with that view, it's easier to see how offset points at the same value as mem[addr]=

  data lookupinator : Address → Tag × Index × Offset → RowAddress → Memory → Row → Set where
    lookupinated :
      ∀ {addr : Address} {tag : Tag} {index : Index} {offset : Offset} →
      --     tag ≡ addr / bitWidthRange offsetWidth / bitWidthRange indexWidth % bitWidthRange tagWidth
      --   index ≡ addr / bitWidthRange offsetWidth                            % bitWidthRange indexWidth
      --  offset ≡ addr                                                        % bitWidthRange offsetWidth
      ∀ {rowAddr : RowAddress} →
      -- rowAddr ≡ addr / bitWidthRange offsetWidth                            % bitWidthRange (tagWidth + indexWidth)
      ∀ {mem : Memory} {row : Row} →
      -- row [ offset ]= val →
      lookupinator addr (tag , index , offset) rowAddr mem row

  data bitify : Address → Tag × Index × Offset → Set where
    bitified : ∀ {addr : Address} {tag : Tag} {index : Index} {offset : Offset}
      --    tag ≡ addr / bitWidthRange offsetWidth / bitWidthRange indexWidth % bitWidthRange tagWidth
      --  index ≡ addr / bitWidthRange offsetWidth                            % bitWidthRange indexWidth
      -- offset ≡ addr                                                        % bitWidthRange offsetWidth
      → bitify addr (tag , index , offset)

  data catbits : Tag × Index → RowAddress → Set where
    cattedbits : ∀ {tag : Tag} {index : Index} {rowAddr : RowAddress}
      -- ...
      → catbits (tag , index) rowAddr

  data fetch : Memory → RowAddress → Row → Set where
    fetched : ∀ {mem : Memory} {rowAddr : RowAddress} {row : Row}
      -- ...
      → fetch mem rowAddr row

  -- We can use a state machine approach for ⟶₂
  -- A configuration is a combination of the mutable memory and registers
  -- along with a state variable that represents what "process" we are
  -- currently doing.
  data Process : Set where

    Idle : Process
    Access : Process
    Allocate : Process
    Write : Word → Process
      
  
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
      → bitify' Σ₀ addr ≡ (tag , index , offset)
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
      → bitify' Σ₀ addr ≡ (tag , index , offset)
      → catbits' Σ₀ tag index ≡ addr'
      → fetch' Σ₀ 𝑚 addr' ≡ row
      → CL true tag row ≡ line
      → σ [ index ]≔ line ≡ σ'
      → (Allocate , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Access , 𝑚 , 𝑟 , σ')


  -- This constructor represents a cache hit for a given address
  -- To construct it is to provide both the existence of
  -- the cache, address, signature, and a proof that we had a hit
  data ⟨_﹐_⟩⇓Hit : Cache → Address → Set where

    hittable : ∀{tag' row} (σ : Cache) (addr : Address) (Σ₀ : Signature)
      → bitify' Σ₀ addr ≡ (tag , index , offset)
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
