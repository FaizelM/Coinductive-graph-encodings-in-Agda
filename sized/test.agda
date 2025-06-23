{-# OPTIONS --sized-types #-}
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Product
open import Agda.Builtin.Equality
open import Agda.Builtin.Size
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)

record Node (i : Size) : Set where
  coinductive
  constructor g
  field
    cur : ℕ
    adj : ∀{j : Size< i} → List (Node j)

open Node public

-- Functions on the graph encoding
rangeFrom1To : ℕ → List ℕ
rangeFrom1To zero    = []
rangeFrom1To (suc n) = rangeFrom1To n ++ ((suc n) ∷ [])

checkRes : List (Bool × (List ℕ)) → Bool
checkRes [] = false
checkRes (x ∷ xs) = if (proj₁ x) then true else checkRes xs

firstGood : List (Bool × (List ℕ)) → Bool × (List ℕ)
firstGood [] = true , []
firstGood (x ∷ xs) = if (proj₁ x) then (true , (proj₂ x)) else firstGood xs

dfs : {i : Size} → ℕ → ℕ → List ℕ → (Node i) → Bool × (List ℕ)
dfs zero target path graph = if (cur graph) ≡ᵇ target then (true , (path ++ (0 ∷ []))) else (false , [])
dfs (suc n) target path graph = if (cur graph) ≡ᵇ target then (true , (path ++ (0 ∷ []))) else
                            if checkRes (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (Data.List.zip (rangeFrom1To (length (adj graph))) (adj graph))) then 
                            firstGood (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (Data.List.zip (rangeFrom1To (length (adj graph))) (adj graph))) else (false , [])

lookupGraph : ∀{i j : Size} → ℕ → List (Node i) → (Node j)
lookupGraph (zero) (x ∷ xs) = x
lookupGraph (suc n) (x ∷ xs) = lookupGraph n xs 
lookupGraph n [] = g 0 []

findGraph : {i j : Size} → List ℕ → (Node i) → (Node j)
findGraph [] graph = graph
findGraph (zero ∷ []) graph = graph
findGraph (zero ∷ xs) graph = graph
findGraph ((suc x) ∷ xs) graph = findGraph xs (lookupGraph x (adj graph))

-- Properties as data types
mutual
    data isPresentInList : ∀{i : Size} → ℕ → List (Node i) → Set where
        here : {i : Size} {n : ℕ} {g : (Node i)} {gs : List (Node i)} → isPresent n g → isPresentInList n (g ∷ gs)
        there : {i : Size} {n : ℕ} {g : (Node i)} {gs : List (Node i)} → isPresentInList n gs → isPresentInList n (g ∷ gs)

    data isPresent : ∀{i : Size} → ℕ → (Node i) → Set where
        node-present : {i : Size} {n : ℕ} {g : (Node i)} → cur g ≡ n → isPresent n g
        adj-present : {i : Size} {n : ℕ} {g : (Node i)} → isPresentInList n (adj g) → isPresent n g

data hasCycle : {i : Size} → (Node i) → Set where
  cycle : {i : Size} {g : (Node i)} → isPresentInList (cur g) (adj g) → hasCycle g

data hasPath : {i : Size} → ℕ → ℕ → (Node i) → Set where
  path : {i : Size} {s t : ℕ} {g : (Node i)} → isPresent t (findGraph (proj₂ (dfs 10 s [] g)) g) → hasPath s t g

-- Example manual proofs
interleaved mutual 
  g1 : Node Agda.Builtin.Size.∞ 
  g0 : Node Agda.Builtin.Size.∞

  g1 .cur = 1
  g1 .adj = g0 ∷ []

  g0 .cur = 0
  g0 .adj = g1 ∷ []

g2 : {i : Size} → Node i
g2 .cur = 5 
g2 .adj = ( g 3 [] ) ∷ ( g 7 ((g 4 []) ∷ []) ) ∷ []

g3 : ℕ → Node Agda.Builtin.Size.∞
g3 n .cur = n
g3 n .adj = g3 ( suc n ) ∷ []

-- prove g2 has 5
proof1 : isPresent 5 g2
proof1 = node-present refl

-- prove g2 has 3
proof2 : isPresent 3 g2
proof2 = adj-present (here (node-present refl))

-- prove g2 has 7
proof3 : isPresent 7 g2
proof3 = adj-present (there (here (node-present refl)))

-- prove g2 has 4
proof4 : isPresent 4 g2
proof4 = adj-present (there (here (adj-present (here (node-present refl)))))

-- prove g0 is part of a cycle
proof5 : hasCycle g0
proof5 = cycle (here (adj-present (here (node-present refl))))

-- prove g2 has a path from 5 to 4
proof6 : hasPath 5 4 g2
proof6 = path
  (adj-present
   (there (here (adj-present (here (node-present refl))))))

-- prove g2 has a path from 7 to 4
proof7 : hasPath 7 4 g2
proof7 = path (adj-present (here (node-present refl)))

-- Automatic proofs

mutual
  getProof : {i : Size} → List ℕ → ℕ → (t : ℕ) → (g : (Node i)) → isPresent t g
  getProof [] zero target graph with cur graph Data.Nat.≟ target
  getProof [] zero target graph | yes eq = node-present eq
  getProof [] zero target graph | no _ = {!!}

  getProof (x ∷ xs) zero target graph = getProof xs x target graph
  getProof xs (suc n) target graph = adj-present (getListProof xs n target (adj graph))

  getListProof : ∀{i : Size} → List ℕ → ℕ → (t : ℕ) → (adj : List (Node i)) → isPresentInList t adj
  getListProof xs zero target (n ∷ ns) = here (getProof xs zero target n)
  getListProof xs (suc i) target (n ∷ ns) = there (getListProof xs i target ns)
  getListProof xs n target [] = {!!}
