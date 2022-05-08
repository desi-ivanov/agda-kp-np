module NNF-CNF where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; s≤s; _≤_)
open import Data.Nat.Properties using (n≤m+n; m≤m+n; ≤-refl)
open import Data.Vec using (lookup)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Product using (_,_; _×_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin; inject≤; fromℕ; inject₁; raise; inject+)
open import SAT
open import CNF
open import NNF
open import BoolProps

distr-lit : ∀{n} → Literal n → CNF n → CNF n
distr-lit l (one c) = one (l , c)
distr-lit l (c , cs) = (l , c) , (distr-lit l cs)

distr-cls : ∀{n} → Clause n → CNF n → CNF n
distr-cls (one x) cnf = distr-lit x cnf
distr-cls (x , c) cnf = distr-lit x (distr-cls c cnf)

distr-cnf : ∀{n} → CNF n → CNF n → CNF n
distr-cnf (one a) b = distr-cls a b
distr-cnf (a , as) b = concat-cnf (distr-cls a b)  (distr-cnf as b)

nnf-to-cnf : ∀{n} → NNF n → CNF n
nnf-to-cnf (Pos x) = one (one (pos x))
nnf-to-cnf (Neg x) = one (one (neg x))
nnf-to-cnf (And a b) = concat-cnf (nnf-to-cnf a) (nnf-to-cnf b)
nnf-to-cnf (Or a b) = distr-cnf (nnf-to-cnf a) (nnf-to-cnf b)

postulate
  theorem1 : ∀{n} → (f : NNF n) → SatisfiableNNF f → SatisfiableCNF (nnf-to-cnf f)
  theorem2 : ∀{n} → (f : NNF n) → SatisfiableCNF (nnf-to-cnf f) → SatisfiableNNF f

concat-lemma1 : ∀{n} → (a b : CNF n) 
  → (ϕ : Interpretation n) 
  → eval-cnf a ϕ ≡ true
  → eval-cnf b ϕ ≡ true
  → eval-cnf ((concat-cnf) a b) ϕ ≡ true
concat-lemma1 (one x) b ϕ p1 p2 rewrite p1 | p2 = refl
concat-lemma1 (x , a) b ϕ p1 p2 with bool5 {eval-clause x ϕ} {eval-cnf a ϕ} p1 
... | fst , snd rewrite fst | concat-lemma1 a b ϕ snd p2 = refl 

distr-lit-lemma1 : ∀{n} → (a : Literal n) (b : CNF n)
  → (ϕ : Interpretation n)
  → eval-literal a ϕ ≡ true
  → eval-cnf (distr-lit a b) ϕ ≡ true
distr-lit-lemma1 a (one x) ϕ p rewrite p = refl
distr-lit-lemma1 a (x , b) ϕ p rewrite p = distr-lit-lemma1 a b ϕ p

distr-lit-lemma2 : ∀{n} → (a : Literal n) (b : CNF n)
  → (ϕ : Interpretation n)
  → eval-cnf b ϕ ≡ true
  → eval-cnf (distr-lit a b) ϕ ≡ true
distr-lit-lemma2 a (one x) ϕ p rewrite p = bool3 refl
distr-lit-lemma2 a (x , b) ϕ p with bool5 {eval-clause x ϕ} {eval-cnf b ϕ} p 
... | l , r rewrite distr-lit-lemma2 a b ϕ r | bool3 {eval-literal a ϕ} l  = refl

distr-cls-lemma1 : ∀{n} → (a : Clause n) (b : CNF n)
  → (ϕ : Interpretation n)
  → eval-clause a ϕ ≡ true
  → eval-cnf (distr-cls a b) ϕ ≡ true
distr-cls-lemma1 (one x) b ϕ p rewrite distr-lit-lemma1 x b ϕ p = refl
distr-cls-lemma1 (x , a) b ϕ p with bool6 {eval-literal x ϕ} {eval-clause a ϕ} p 
... | inj₁ q = distr-lit-lemma1 x (distr-cls a b) ϕ q
... | inj₂ y = 
  let ih = (distr-cls-lemma1 a b ϕ y )
  in distr-lit-lemma2 x (distr-cls a b) ϕ ih

distr-cls-lemma2 : ∀{n} → (a : Clause n) (b : CNF n)
  → (ϕ : Interpretation n)
  → eval-cnf b ϕ ≡ true
  → eval-cnf (distr-cls a b) ϕ ≡ true
distr-cls-lemma2 (one x) b ϕ p = distr-lit-lemma2 x b ϕ p
distr-cls-lemma2 (x , a) b ϕ p = 
  let ih = distr-cls-lemma2 a b ϕ p 
  in distr-lit-lemma2 x (distr-cls a b) ϕ (distr-cls-lemma2 a b ϕ p) 

distr-cnf-lemma1 : ∀{n} → (a b : CNF n)
  → (ϕ : Interpretation n)
  → eval-cnf a ϕ ≡ true
  → eval-cnf (distr-cnf a b) ϕ ≡ true
distr-cnf-lemma1 (one x) b ϕ p = distr-cls-lemma1 x b ϕ p
distr-cnf-lemma1 (x , a) b ϕ p with bool5 {eval-clause x ϕ} {eval-cnf a ϕ} p
... | o , i =
  let ih = distr-cnf-lemma1 a b ϕ i 
  in let prop = distr-cls-lemma1 x b ϕ o 
  in concat-lemma1 (distr-cls x b) (distr-cnf a b) ϕ prop ih

distr-cnf-lemma2 : ∀{n} → (a b : CNF n)
  → (ϕ : Interpretation n)
  → eval-cnf b ϕ ≡ true
  → eval-cnf (distr-cnf a b) ϕ ≡ true
distr-cnf-lemma2 (one x) b ϕ p = distr-cls-lemma2 x b ϕ p
distr-cnf-lemma2 (x , a) b ϕ p =
  let ih =  distr-cnf-lemma2 a b ϕ p
  in let prop = distr-cls-lemma2 x b ϕ p
  in concat-lemma1 ((distr-cls x b)) ((distr-cnf a b)) ϕ prop ih

lemma1 : ∀{n} → (f : NNF n)
  → (ϕ : Interpretation n)
  → eval-nnf f ϕ ≡ true 
  → eval-cnf (nnf-to-cnf f) ϕ ≡ true
lemma1 (Pos x) ϕ r = r
lemma1 (Neg x) ϕ r = r
lemma1 (And a b) ϕ r with bool5 {eval-nnf a ϕ} {eval-nnf b ϕ} r 
... | fst , snd with lemma1 a ϕ fst | lemma1 b ϕ snd
... | ih1 | ih2 = concat-lemma1 (nnf-to-cnf a) (nnf-to-cnf b) ϕ ih1 ih2
lemma1 (Or a b) ϕ r with bool6 {eval-nnf a ϕ} {eval-nnf b ϕ} r 
... | inj₁ x = let ih = lemma1 a ϕ x in distr-cnf-lemma1 (nnf-to-cnf a) (nnf-to-cnf b) ϕ ih
... | inj₂ y = let ih = lemma1 b ϕ y in distr-cnf-lemma2 (nnf-to-cnf a) (nnf-to-cnf b) ϕ ih
