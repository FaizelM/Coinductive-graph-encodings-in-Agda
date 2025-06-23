{-# OPTIONS --guardedness #-}
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Empty
open import Data.Fin
open import Function.Base
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

ilistn : Set → ℕ → Set
ilistn T n = Fin n → T

ilist : (T : Set) → Set
ilist T = Σ ℕ (ilistn T)

iniln : ∀ {T : Set} → Fin 0 → T
iniln ()

inil : ∀ {T : Set} → ilist T
inil = 0 , iniln

iconsn : ∀ {T : Set} {n : ℕ} → T → ilistn T n → ilistn T (suc n)
iconsn t ln zero = t 
iconsn t ln (suc i) = ln i

icons : ∀ {T : Set} → T → ilist T → ilist T
icons t l = suc (fst l) , iconsn t (snd l)


imap : ∀ {T U : Set} → (T → U) → ilist T → ilist U
imap f l = ((fst l) , (f ∘ (snd l)))

record Graph : Set where
    coinductive
    constructor g
    field
        cur : ℕ
        adj : ilist Graph


data isPresent : ℕ → Graph → Set where
    node-present : {n : ℕ} {g : Graph} → Graph.cur g ≡ n → isPresent n g 
    -- node-in-list : {n : ℕ} {g : Graph} → (or (imap (isPresent n) (Graph.adj g))) → isPresent n g

data isNotPresent : ℕ -> Graph -> Set where
    node-notPresent : {n : ℕ} {g : Graph} → isPresent n g → ⊥ → isNotPresent n g
    
     
open Graph public
g1 : Graph 
g1 .cur = 2
g1 .adj = inil 


-- This is the dummy function to test the map function on the ilist.
f : ℕ → ℕ
f n = suc n

-- This is the map function as described in the paper. It does not pass the termination checker.
-- applyF2G : ( ℕ → ℕ ) → Graph → Graph
-- applyF2G f g1 = (g (f (Graph.cur g1)) (imap (applyF2G f) (Graph.adj g1)))


-- Example manual proofs

proof1 : isPresent 2 g1 
proof1 = node-present refl