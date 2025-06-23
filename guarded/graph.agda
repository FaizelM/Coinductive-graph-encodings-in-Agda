{-# OPTIONS --guardedness #-}
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Product
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)

record Node : Set where
  coinductive
  constructor g
  field
    cur : ℕ
    adj : List Node

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

dfs : ℕ → ℕ → List ℕ → Node → Bool × (List ℕ)
dfs zero target path graph = if (cur graph) ≡ᵇ target then (true , (path ++ (0 ∷ []))) else (false , [])
dfs (suc n) target path graph = if (cur graph) ≡ᵇ target then (true , (path ++ (0 ∷ []))) else
                            if checkRes (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (Data.List.zip (rangeFrom1To (length (adj graph))) (adj graph))) then 
                            firstGood (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (Data.List.zip (rangeFrom1To (length (adj graph))) (adj graph))) else (false , [])

lookupGraph : ℕ → List Node → Node
lookupGraph (zero) (x ∷ xs) = x
lookupGraph (suc n) (x ∷ xs) = lookupGraph n xs 
lookupGraph n [] = g 0 []

findGraph : List ℕ → Node → Node
findGraph [] graph = graph
findGraph (zero ∷ []) graph = graph
findGraph (zero ∷ xs) graph = graph
findGraph ((suc x) ∷ xs) graph = findGraph xs (lookupGraph x (adj graph))

-- Properties as data types
mutual
    data isPresentInList : ℕ → List Node → Set where
        here : {n : ℕ} {g : Node} {gs : List Node} → isPresent n g → isPresentInList n (g ∷ gs)
        there : {n : ℕ} {g : Node} {gs : List Node} → isPresentInList n gs → isPresentInList n (g ∷ gs)

    data isPresent : ℕ → Node → Set where
        node-present : {n : ℕ} {g : Node} → cur g ≡ n → isPresent n g
        adj-present : {n : ℕ} {g : Node} → isPresentInList n (adj g) → isPresent n g

mutual
  data CycleInList : List Node → Set where
    here : {g : Node} {gs : List Node} → hasCycle g → CycleInList (g ∷ gs)
    there : {g : Node} {gs : List Node} → CycleInList gs → CycleInList (g ∷ gs) 

  data hasCycle : Node → Set where
    node-cycle : {g : Node} → isPresentInList (cur g) (adj g) → hasCycle g
    adj-cycle : {g : Node} → CycleInList (adj g) → hasCycle g

data hasPath : ℕ → ℕ → Node → Set where
  path : {s t : ℕ} {g : Node} → isPresent t (findGraph (proj₂ (dfs 10 s [] g)) g) → hasPath s t g

-- Example manual proofs
mutual
  g1 : Node 
  g1 .cur = 1
  g1 .adj = g0 ∷ []

  g0 : Node
  g0 .cur = 0
  g0 .adj = g1 ∷ []

g2 : Node
g2 .cur = 5 
g2 .adj = ( g 3 [] ) ∷ ( g 7 ((g 4 []) ∷ []) ) ∷ []

g3 : ℕ → Node
g3 n .cur = n
g3 n .adj = g3 ( suc n ) ∷ []

g4 : Node
g4 .cur = 3
g4 .adj = ( g 2 [] ) ∷ ( g 7 ((g 4 (g1 ∷ [])) ∷ []) ) ∷ []

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

-- prove g0 has a cycle
proof5 : hasCycle g0
proof5 = node-cycle (here (adj-present (here (node-present refl))))

-- prove g4 has a cycle
proof6 : hasCycle g4
proof6 = adj-cycle
  (there
   (here
    (adj-cycle
     (here
      (adj-cycle
       (here
        (node-cycle (here (adj-present (here (node-present refl)))))))))))

-- prove g2 has a path from 5 to 4
proof7 : hasPath 5 4 g2
proof7 = path
  (adj-present
   (there (here (adj-present (here (node-present refl))))))

-- prove g2 has a path from 7 to 4
proof8 : hasPath 7 4 g2
proof8 = path (adj-present (here (node-present refl)))

-- Automatic proofs


{-# NON_COVERING #-}
mutual
  getProof : List ℕ → ℕ → (t : ℕ) → (g : Node) → isPresent t g
  getProof [] zero target graph with cur graph Data.Nat.≟ target
  getProof [] zero target graph | yes eq = node-present eq

  getProof (x ∷ xs) zero target graph = getProof xs x target graph
  getProof xs (suc n) target graph = adj-present (getListProof xs n target (adj graph))

  getListProof : List ℕ → ℕ → (t : ℕ) → (adj : List Node) → isPresentInList t adj
  getListProof xs zero target (n ∷ ns) = here (getProof xs zero target n)
  getListProof xs (suc i) target (n ∷ ns) = there (getListProof xs i target ns)
