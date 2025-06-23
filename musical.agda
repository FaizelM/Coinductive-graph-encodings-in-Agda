{-# OPTIONS --guardedness #-}
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Empty
open import Data.Fin
open import Data.Maybe
open import Relation.Nullary
open import Function.Base
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma


data Node : Set where
    g : ℕ → (List Node) → Node

-- record Graph : Set where
--   coinductive
--   constructor g
--   field
--     cur : ℕ
--     adj : List (∞ Graph)

-- open Graph

-- data ListContains {A : Set} : A → List A → Set where
--   here  : ∀ {x xs} → ListContains x (x ∷ xs)
--   there : ∀ {x y xs} → ListContains x xs → ListContains x (y ∷ xs)

-- data Contains : Graph → ℕ → Set where
--   here : ∀ {g x} → Graph.cur g ≡ x → Contains g x
--   there : ∀ {g x} → (g' : Graph) → ListContains g' (Graph.adj g) → Contains g' x → Contains g x


-- mutual
--     data isPresentInList : ℕ → List (∞ Node) → Set where
--         here : {n : ℕ} {g : ∞ Node} {gs : List (∞ Node)} → isPresent n g → isPresentInList n (g ∷ gs)
--         there : {n : ℕ} {g : ∞ Node} {gs : List (∞ Node)} → isPresentInList n gs → isPresentInList n (g ∷ gs)

--     data isPresent : ℕ → ∞ Node → Set where
--         node-present : {n : ℕ} {g : ∞ Node} → (♭ g) ≡ n → isPresent n g
--         adj-present : {n : ℕ} {g : ∞ Node} → isPresentInList n (adj (♭ g)) → isPresent n g

mutual

  data isPresent : ℕ → Node → Set where
    node-present :
      ∀ {n m : ℕ} {adj : (List Node)} →
      n ≡ m →
      isPresent n (g m adj)

    adj-present :
      ∀ {n m : ℕ} {adj : (List Node)} →
      isPresentInList n (adj) →
      isPresent n (g m adj)

  data isPresentInList : ℕ → List Node → Set where
    here :
      ∀ {n : ℕ} {x : Node} {xs : List Node} →
      isPresent n x →
      isPresentInList n (x ∷ xs)

    there :
      ∀ {n : ℕ} {x : Node} {xs : List Node} →
      isPresentInList n xs →
      isPresentInList n (x ∷ xs)


myGraph : Node
myGraph = g 7 ( ((g 3 ( [])) ∷ []))

interleaved mutual 
  g1 : Node 
  g0 : Node

  g1 = g 1 ((g0) ∷ [])
  g0 = g 0 ((g1) ∷ [])

-- proof1 : isPresent 3 myGraph
-- proof1 = adj-present (here (node-present refl))



-- applyFunc : (ℕ → ℕ) → Node → Node
-- applyFunc f (g cur adj) = (g (f cur) adj)

-- gadjmap : (ℕ → ℕ) → List (∞ Node) → List (∞ Node)
-- gadjmap f [] = []
-- gadjmap f (x ∷ xs) = (♯ (applyFunc f (♭ x))) ∷ (gadjmap f xs)

-- gmap : (ℕ → ℕ) → (Node) → (Node)
-- gmap f (g cur adj) = g (f cur) (gadjmap f adj)

-- f : ℕ → ℕ
-- f a = (suc a)

-- proofmap : gmap f myGraph ≡ g 8 (♯ ((g 4 (♯ [])) ∷ []))
-- proofmap = refl

-- processhead : Maybe Graph -> List Graph
-- processhead (just a) = a ∷ []
-- processhead nothing = []

-- open Graph public

-- g1 : ∞ Graph 
-- g0 : ∞ Graph

-- g1 = ♯ record {cur = 1; adj = g0 ∷ []}
-- g0 = ♯ record {cur = 0; adj = g1 ∷ []}

-- graphlist : List (∞ Graph)
-- graphlist = g0 ∷ g1 ∷ []


-- g3 : ℕ → Graph
-- g3 n .cur = n
-- g3 n .adj = g3 ( suc n ) ∷ []

-- graphhead : Maybe Graph
-- graphhead = head graphlist

-- gcirc : Graph
-- gcirc .cur = 0
-- gcirc .adj = (g 1 (gcirc ∷ [])) ∷ (g 2 (processhead (head (adj gcirc)))) ∷ []

-- myGraph : ∞ Graph
-- myGraph = ♯ record {cur = 1; adj = (♯ (g 3 [])) ∷ (♯ (g 7 [])) ∷ []}

-- proof1 : isPresent 7 myGraph
-- proof1 = adj-present (there (here (node-present refl)))

 