module Semantics where

open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Data.Maybe using (Maybe; nothing; just)
open import Function using (case_of_)
--open import Function.Bijection

open import Agda.Builtin.Nat
import Data.Nat as Nat
open import Data.Nat using (ℕ; zero; suc; _+_)

import Data.Fin as Fin
open import Data.Fin using (Fin; toℕ; fromℕ<; _<_)

import Data.Vec as Vec
open import Data.Vec using (Vec; []; _∷_; _[_]=_; _[_]≔_; take; drop)
open import Data.Vec.Properties

open import Level

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


  -- This function does a memory lookup with "more steps"
  lookup-with : (Address → Tag × Index × Offset) →
                (Memory → Tag → Index → Row) →
                Memory → Address → Word
  lookup-with 𝒇 𝒈 mem addr =
    let (tag , index , offset) = 𝒇 addr
        row = 𝒈 mem tag index
    in  Vec.lookup row offset

  -- The 'signature' is an abstract set of functions
  -- that yield an abstract implementation of the algorithm
  -- which does the cache and address manipulation
  record Signature : Set where
    field
      toBitVec : Address → Tag × Index × Offset
      fetchRow : Memory → Tag → Index → Row
      lemma₁ : ∀{mem : Memory} {addr : Address} {val : Word} →
                    mem [ addr ]= val →
                    let (tag , index , offset) = toBitVec addr
                        row = fetchRow mem tag index
                    in  row [ offset ]= val

      lemma₂ : ∀{mem : Memory} →
               (∀(addr : Address) → Vec.lookup mem addr ≡ lookup-with toBitVec fetchRow mem addr) 

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
    hit-rule : ∀ {val} →
               let (tag , index , offset) = toBitVec Σ₀ addr
               in σ [ tag ﹐ index ﹐ offset ]= val →
                  (Access , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Write val , 𝑚 , 𝑟 , σ)

    -- Write the value to the target register, then return to waiting for next request
    write-rule : let (tag , index , offset) = toBitVec Σ₀ addr
                     row = fetchRow Σ₀ 𝑚 tag index
                     val = Vec.lookup row offset
                     𝑟' = 𝑟 [ reg-name ]≔ val
                 in (Write val , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Idle , 𝑚 , 𝑟' , σ)

    -- We can't provide a proof of a cache hit, therefore we can only apply this reduction
    miss-rule : (Access , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Allocate , 𝑚 , 𝑟 , σ)

    -- We allocate a new line in the cache (thus updating it), then go back to
    -- comparing tags. The idea _now_ we can provide a proof of a cache hit and
    -- successfully move on to the write stage
    allocate-rule : let (tag , index , offset) = toBitVec Σ₀ addr
                        row = fetchRow Σ₀ 𝑚 tag index
                        line = CL true tag row
                        σ' = σ [ index ]≔ line
                    in (Allocate , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Access , 𝑚 , 𝑟 , σ')
                     
  

  -- Note : This lemma is similar to injectivity. It says that lookups directly in
  -- memory give the same value as the "lookup-with" some functions that do the
  -- splitting of the address into tag-index-offset then retreive the relevant row.
  equiv-lookups : ∀{val} (mem : Memory) Σ₀ addr →
           mem [ addr ]= val →
           let val' = lookup-with (toBitVec Σ₀) (fetchRow Σ₀) mem addr
           in mem [ addr ]= val'
  equiv-lookups mem Σ₀ addr mem[addr]=val = lookup⇒[]= addr mem (lemma₂ Σ₀ addr)

  -- Allocation gives a hit
  Lemma : ∀{reg-name val} addr 𝑚 Σ₀ σ σ' →
          𝑚 [ addr ]= val →
          (Allocate , 𝑚 , 𝑟 , σ) ⟶₂[ τ reg-name addr , Σ₀ ] (Access , 𝑚 , 𝑟 , σ') →
          let (tag , index , offset) = toBitVec Σ₀ addr
              row = fetchRow Σ₀ 𝑚 tag index
              val = Vec.lookup row offset
          in σ' [ tag ﹐ index ﹐ offset ]= val
  Lemma addr 𝑚 Σ₀ σ .(σ [ _ ]≔ CL true _ _) mem[addr]=val allocate-rule =
    let (tag , index , offset) = toBitVec Σ₀ addr
        row = fetchRow Σ₀ 𝑚 tag index
        val = Vec.lookup row offset
    in  cacheAccess (σ [ _ ]≔ CL true _ _) tag index offset
                    ([]≔-updates _ index)
                    (lemma₁ Σ₀ (equiv-lookups 𝑚 Σ₀ addr mem[addr]=val))
