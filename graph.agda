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

record Node : Set where
    coinductive
    constructor g
    field
        cur : ℕ
        adj : ilist Node


data isPresent : ℕ → Node → Set where
    node-present : {n : ℕ} {g : Node} → Node.cur g ≡ n → isPresent n g 

data isNotPresent : ℕ -> Node -> Set where
    node-notPresent : {n : ℕ} {g : Node} → isPresent n g → ⊥ → isNotPresent n g
    
     
open Node public
g1 : Node 
g1 .cur = 2
g1 .adj = inil 

-- g2 : Node
-- g2 .cur = 0
-- g2 .adj = ( g 1 ( g2 ∷ [] ) ) ∷ []

-- g3 : ℕ → Node
-- g3 n .cur = n
-- g3 n .adj = g3 ( suc n ) ∷ []

-- nodeInList : List Node → Bool
-- nodeInList l = (or (map (isPresent 1) (Node.adj g2)))

f : ℕ → ℕ
f n = suc n

applyF2G : ( ℕ → ℕ ) → Node → Node
applyF2G f g1 = (g (f (Node.cur g1)) (imap (applyF2G f) (Node.adj g1)))

proof1 : isPresent 2 g1 
proof1 = node-present refl


        


-- map (A B : Set) : (A → B) → List A → List B
-- map f []        = []
-- map f (x :: xs) = f x :: map f xs


-- or : List Bool → Bool
-- or []        = false
-- or (x :: xs) = if x then true else 

-- find : Nat → Node → Bool
-- find n .cur = n == .cur
-- find n .adj = 

   