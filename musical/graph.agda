{-# OPTIONS --guardedness #-}
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Product
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality


data Node : Set where
    g : ℕ → (List (∞ Node)) → Node

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

zipAdj : {A : Set} → List A → List (∞ Node) → List (A × Node)
zipAdj [] [] = []
zipAdj xs [] = []
zipAdj [] ys = []
zipAdj (x ∷ xs) (y ∷ ys) = (x , (♭ y)) ∷ zipAdj xs ys


dfs : ℕ → ℕ → List ℕ → Node → Bool × (List ℕ)
dfs zero target path (g cur adj) = if cur ≡ᵇ target then (true , (path ++ (0 ∷ []))) else (false , [])
dfs (suc n) target path (g cur adj) = if cur ≡ᵇ target then (true , (path ++ (0 ∷ []))) else
                            if checkRes (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (zipAdj (rangeFrom1To (length adj)) adj)) then 
                            firstGood (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (zipAdj (rangeFrom1To (length adj)) adj)) else (false , [])

lookupGraph : ℕ → List (∞ Node) → Node
lookupGraph (zero) (x ∷ xs) = (♭ x)
lookupGraph (suc n) (x ∷ xs) = lookupGraph n xs 
lookupGraph n [] = g 0 []

findGraph : List ℕ → Node → Node
findGraph [] graph = graph
findGraph (zero ∷ []) graph = graph
findGraph (zero ∷ xs) graph = graph
findGraph ((suc x) ∷ xs) (g n adj) = findGraph xs (lookupGraph x adj)

-- Properties as data types
mutual
    data isPresent : ℕ → Node → Set where
        node-present : {n m : ℕ} {adj : (List (∞ Node))} → n ≡ m → isPresent n (g m adj)
        adj-present : {n m : ℕ} {adj : (List (∞ Node))} → isPresentInList n (adj) → isPresent n (g m adj)
    
    data isPresentInList : ℕ → (List (∞ Node)) → Set where
        here : {n : ℕ} {x : (∞ Node)} {xs : (List (∞ Node))} → isPresent n (♭ x) → isPresentInList n (x ∷ xs)
        there : {n : ℕ} {x : (∞ Node)} {xs : (List (∞ Node))} → isPresentInList n xs → isPresentInList n (x ∷ xs)

mutual
  data CycleInList : List (∞ Node) → Set where
    here : {g : (∞ Node)} {gs : List (∞ Node)} → hasCycle (♭ g) → CycleInList (g ∷ gs)
    there : {g : (∞ Node)} {gs : List (∞ Node)} → CycleInList gs → CycleInList (g ∷ gs) 

  data hasCycle : Node → Set where
    node-cycle : {n : ℕ} {adj : (List (∞ Node))} → isPresentInList n adj → hasCycle (g n adj)
    adj-cycle : {n : ℕ} {adj : (List (∞ Node))} → CycleInList adj → hasCycle (g n adj)

data hasPath : ℕ → ℕ → Node → Set where
  path : {s t : ℕ} {g : Node} → isPresent t (findGraph (proj₂ (dfs 10 s [] g)) g) → hasPath s t g

-- Example manual proofs
mutual 
  g1 : Node 
  g1 = g 1 ((♯ g0) ∷ [])

  g0 : Node
  g0 = g 0 ((♯ g1) ∷ [])

g2 : Node
g2 = g 5 ( (♯ ( g 3 [] )) ∷ (♯ ( g 7 ((♯ (g 4 [])) ∷ []) )) ∷ [] )

g3 : ℕ → Node
g3 n = g n ((♯ (g3 (suc n))) ∷ [])

g4 : Node
g4 = g 3 ( (♯ ( g 2 [] )) ∷ (♯ ( g 7 ((♯ (g 4 ((♯ g1) ∷ [])) ) ∷ []) ) ) ∷ [] )

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

-- experimentatione
applyFunc : (ℕ → ℕ) → Node → Node
applyFunc f (g cur adj) = (g (f cur) adj)

gadjmap : (ℕ → ℕ) → List (∞ Node) → List (∞ Node)
gadjmap f [] = []
gadjmap f (x ∷ xs) = (♯ (applyFunc f (♭ x))) ∷ (gadjmap f xs)

gmap : (ℕ → ℕ) → (Node) → (Node)
gmap f (g cur adj) = g (f cur) (gadjmap f adj)

f : ℕ → ℕ
f a = (suc a)

nodeEquals : ℕ → Node → Bool
nodeEquals target (g cur _) = if target ≡ᵇ cur then true else false

data isPresentTest : ℕ → Node → Set where
        node-presentTest : {n m : ℕ} {adj : (List (∞ Node))} → n ≡ m → isPresentTest n (g m adj)
        adj-presentTest : {n m : ℕ} {adj : (List (∞ Node))} → (any (Data.List.map (λ x → nodeEquals n (♭ x)) adj)) ≡ true → isPresentTest n (g m adj)

-- -- prove g2 has 5
-- proof1₂ : isPresentTest 5 g2
-- proof1₂ = node-presentTest refl

-- -- prove g2 has 3
-- proof2₂ : isPresentTest 3 g2
-- proof2₂ = adj-presentTest refl

-- -- prove g2 has 7
-- proof3₂ : isPresentTest 7 g2
-- proof3₂ = adj-presentTest refl

-- -- prove g2 has 4
-- proof4₂ : isPresentTest 4 g2
-- proof4₂ = adj-presentTest refl

-- proofequiv : g2 ≡ g 5 ( (♯ ( g 3 [] )) ∷ (♯ ( g 7 ((♯ (g 4 [])) ∷ []) )) ∷ [] )
-- proofequiv = refl

-- proofmap : gmap f g2 ≡ g 6 (gadjmap f ( (♯ ( g 3 [] )) ∷ (♯ ( g 7 ((♯ (g 4 [])) ∷ []) )) ∷ [] ))
-- proofmap = refl