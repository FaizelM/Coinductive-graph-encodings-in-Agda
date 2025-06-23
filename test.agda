{-# OPTIONS --guardedness #-}
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Function.Base
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

open Node

Graph : Set 
Graph = List Node
  
-- data ListContains {A : Set} : A → List A → Set where
--   here  : ∀ {x xs} → ListContains x (x ∷ xs)
--   there : ∀ {x y xs} → ListContains x xs → ListContains x (y ∷ xs)

-- data Contains : Node → ℕ → Set where
--   here : ∀ {g x} → Node.cur g ≡ x → Contains g x
--   there : ∀ {g x} → (g' : Node) → ListContains g' (Node.adj g) → Contains g' x → Contains g x


mutual
  data isPresentInList : ℕ → List Node → Set where
    here : {n : ℕ} {g : Node} {gs : List Node} → isPresent n g → isPresentInList n (g ∷ gs)
    there : {n : ℕ} {g : Node} {gs : List Node} → isPresentInList n gs → isPresentInList n (g ∷ gs)

  data isPresent : ℕ → Node → Set where
    node-present : {n : ℕ} {g : Node} → cur g ≡ n → isPresent n g
    adj-present : {n : ℕ} {g : Node} → isPresentInList n (adj g) → isPresent n g


-- data PartOfCycle : Node → Set where
--   cycle : {g : Node} → isPresentInList (cur g) (adj g) → hasCycle g

mutual
  data CycleInList : List Node → Set where
    here : {g : Node} {gs : List Node} → hasCycle g → CycleInList (g ∷ gs)
    there : {g : Node} {gs : List Node} → CycleInList gs → CycleInList (g ∷ gs) 

  data hasCycle : Node → Set where
    node-cycle : {g : Node} → isPresentInList (cur g) (adj g) → hasCycle g
    adj-cycle : {g : Node} → CycleInList (adj g) → hasCycle g

processhead : Maybe Node -> List Node
processhead (just a) = a ∷ []
processhead nothing = []

open Node public
interleaved mutual 
  g1 : Node 
  g0 : Node
  graphlist : Graph

  g1 .cur = 1
  g1 .adj = g0 ∷ []


  g0 .cur = 0
  g0 .adj = g1 ∷ []

  graphlist = g0 ∷ g1 ∷ []

g3 : ℕ → Node
g3 n .cur = n
g3 n .adj = g3 ( suc n ) ∷ []

graphhead : Maybe Node
graphhead = head graphlist

-- gcirc : Node
-- gcirc .cur = 0
-- gcirc .adj = (g 1 (gcirc ∷ [])) ∷ (g 2 (processhead (head (adj gcirc)))) ∷ []

myGraph : Node
myGraph .cur = 5 
myGraph .adj = ( g 3 [] ) ∷ ( g 7 ((g 4 []) ∷ []) ) ∷ []

proof1 : isPresent 4 myGraph
proof1 = adj-present (there (here (adj-present (here (node-present refl)))))

rangeFrom1To : ℕ → List ℕ
rangeFrom1To zero    = []
rangeFrom1To (suc n) = rangeFrom1To n ++ ((suc n) ∷ [])

checkRes : List (Bool × (List ℕ)) → Bool
checkRes [] = false
checkRes (x ∷ xs) = if (proj₁ x) then true else checkRes xs

firstGood : List (Bool × (List ℕ)) → Bool × (List ℕ)
firstGood [] = true , []
firstGood (x ∷ xs) = if (proj₁ x) then (true , (proj₂ x)) else firstGood xs

nodeInList : List Node → Bool
nodeInList l = (or (Data.List.map (λ x → if isPresent 4 x ≡ true then true else false)) (Node.adj myGraph))


dfs : ℕ → ℕ → List ℕ → Node → Bool × (List ℕ)
dfs zero target path graph = if (cur graph) ≡ᵇ target then (true , (path ++ (0 ∷ []))) else (false , [])
dfs (suc n) target path graph = if (cur graph) ≡ᵇ target then (true , (path ++ (0 ∷ []))) else
                            if checkRes (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (Data.List.zip (rangeFrom1To (length (adj graph))) (adj graph))) then 
                            firstGood (Data.List.map (λ (i , x) → dfs n target (path ++ (i ∷ [])) x) (Data.List.zip (rangeFrom1To (length (adj graph))) (adj graph))) else (false , [])



-- myGraph : Node
-- myGraph .cur = 5 
-- myGraph .adj = ( g 3 [] ) ∷ ( g 7 ((g 4 []) ∷ []) ) ∷ []

lookupGraph : ℕ → List Node → Node
lookupGraph (zero) (x ∷ xs) = x
lookupGraph (suc n) (x ∷ xs) = lookupGraph n xs 
lookupGraph n [] = g 0 []


findGraph : List ℕ → Node → Node
findGraph [] graph = graph
findGraph (zero ∷ []) graph = graph
findGraph (zero ∷ xs) graph = graph
findGraph ((suc x) ∷ xs) graph = findGraph xs (lookupGraph x (adj graph))

checkdfs : (true , (2 ∷ 1 ∷ 0 ∷ [])) ≡ (dfs 2 4 [] myGraph)
checkdfs = refl

mutual
  getProof : List ℕ → ℕ → (t : ℕ) → (g : Node) → isPresent t g
  getProof [] zero target graph with cur graph Data.Nat.≟ target
  getProof [] zero target graph | yes eq = node-present eq
  getProof [] zero target graph | no _ = {!!}

  getProof (x ∷ xs) zero target graph = getProof xs x target graph
  getProof xs (suc n) target graph = adj-present (getListProof xs n target (adj graph))

  getListProof : List ℕ → ℕ → (t : ℕ) → (adj : List Node) → isPresentInList t adj
  getListProof xs zero target (n ∷ ns) = here (getProof xs zero target n)
  getListProof xs (suc i) target (n ∷ ns) = there (getListProof xs i target ns)
  getListProof xs n target [] = {!!}


testProver : proof1 ≡ (getProof (proj₂ (dfs 2 4 [] myGraph)) zero 4 myGraph)
testProver = refl

-- data Symbol : Set where
--   r : Symbol
--   n : Symbol
--   a : Symbol
--   h : Symbol
--   t : Symbol

-- processNumber : ℕ → List Symbol
-- processNumber zero = n ∷ r ∷ []
-- processNumber (suc zero) = a ∷ h ∷ []
-- processNumber (suc i) = a ∷ (replicate i t) ++ h ∷ []

-- unbox : List ℕ → List Symbol
-- unbox [] = []
-- unbox (x ∷ xs) = processNumber x ++ unbox xs

-- test : unbox (2 ∷ 1 ∷ 0 ∷ []) ≡ (a ∷ t ∷ h ∷ a ∷ h ∷ n ∷ r ∷ [])
-- test = refl


-- getProof : List ℕ → ∀ (n : ℕ) (g : Node) → (cur g ≡ n) → Maybe (isPresent n g)
-- getProof [] t graph refl = nothing
-- getProof (0 ∷ []) t graph refl = just (node-present refl)
-- getProof (x :: xs) t graph refl = 


-- provePresence : ℕ → (n : ℕ) → (g : Node) → Maybe isPresent n g
-- provePresence depth target graph with (proj₁ (dfs depth target [] graph)) 
-- ... | true = mapProof unbox (proj₂ (dfs depth target [] graph)) target graph
-- ... | false = nothing



-- data hasPath : ℕ → ℕ → Node → Set where
--   path : {s t : ℕ} {g : Node} → isPresent t (findGraph (proj₂ (dfs 10 s [] g)) g) → hasPath s t g

-- proofPath : hasPath 5 4 myGraph
-- proofPath = path
--   (adj-present
--    (there (here (adj-present (here (node-present refl))))))

-- data HasNode : ℕ → ℕ → Node → Set where
--   yesNode : {depth n : ℕ} {g : Node} → (cur (findGraph (proj₂ (dfs depth n [] g)) g)) ≡ n → HasNode depth n g

-- data PathExists :  ℕ → ℕ → Node → Set where
--   hasPath : 

-- proveGraph : (d : ℕ) → (n : ℕ) → (g : Node) → Maybe (HasNode d n g)
-- proveGraph depth target graph = if (cur (findGraph (proj₂ (dfs depth target [] graph)) graph)) ≡ᵇ target then just (yesNode refl) else nothing




