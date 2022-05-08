module SAT-NNF where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; _≟_; zero; suc; _+_; _<′_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties using (m≤′m+n; n≤′m+n; s≤′s)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; lookup)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_;[]; [_]; map; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Product using (_,_; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Bool.Properties using (∨-zeroˡ)
open import Data.Empty using (⊥-elim)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no; _because_)
open import Induction.Nat
open import Induction.WellFounded
open import SAT
open import NNF
open import BoolProps 

sat-to-nnf : ∀{n} → SAT n → NNF n
sat-to-nnf (Atom x) = Pos x
sat-to-nnf (Not (Atom x)) = Neg x
sat-to-nnf (Not (Not x)) = sat-to-nnf x
sat-to-nnf (Not (And a b)) = Or (sat-to-nnf (Not a)) (sat-to-nnf (Not b))
sat-to-nnf (Not (Or a b)) = And (sat-to-nnf (Not a)) (sat-to-nnf (Not b))
sat-to-nnf (And a b) = And (sat-to-nnf a) (sat-to-nnf b)
sat-to-nnf (Or a b) = Or (sat-to-nnf a) (sat-to-nnf b)
to-wf : ∀ {n} (s : SAT n) 
  → Acc _<′_ (weight s)
  → (ϕ : Interpretation n)
  → eval-sat s ϕ ≡ true 
  → eval-nnf (sat-to-nnf s) ϕ ≡ true
to-wf (Atom x) wf ϕ r = r
to-wf (Not (Atom x)) wf ϕ r = r
to-wf (Not (Not s)) (acc go) ϕ r rewrite not-not-elim (eval-sat s ϕ) = to-wf s (go (weight s) (≤′-step ≤′-refl)) ϕ r
to-wf (Not (And a b)) (acc go) ϕ r with bool2 {eval-sat a ϕ} {eval-sat b ϕ} r
... | inj₁ x rewrite to-wf (Not a) (go (suc (weight a)) (m≤′m+n (suc (suc (weight a))) (weight b))) ϕ x = refl
... | inj₂ y rewrite to-wf (Not b) (go (suc (weight b)) (s≤′s (s≤′s (n≤′m+n (weight a) (weight b))))) ϕ y = bool3 refl 
to-wf (Not (Or a b)) (acc go) ϕ r with bool4 {eval-sat a ϕ} {eval-sat b ϕ} r 
... | p1 , p2 rewrite to-wf (Not a) (go (suc (weight a)) (m≤′m+n (suc (suc (weight a))) (weight b))) ϕ p1 | to-wf (Not b) (go (suc (weight b)) ((s≤′s (s≤′s (n≤′m+n (weight a) (weight b)))))) ϕ p2 = refl
to-wf (And a b) (acc go) ϕ r with bool5 {eval-sat a ϕ} {eval-sat b ϕ} r
... | p1 , p2 rewrite to-wf a (go (weight a) (s≤′s (m≤′m+n (weight a) (weight b)))) ϕ p1 | to-wf b (go (weight b) (s≤′s (n≤′m+n (weight a) (weight b)))) ϕ p2 = refl
to-wf (Or a b) (acc go) ϕ r with bool6 {eval-sat a ϕ} {eval-sat b ϕ} r 
... | inj₁ x rewrite to-wf a (go (weight a) (s≤′s (m≤′m+n (weight a) (weight b)))) ϕ x = refl
... | inj₂ y rewrite to-wf b (go (weight b) (s≤′s (n≤′m+n (weight a) (weight b)))) ϕ y = bool3 refl

from-wf : ∀ {n} (s : SAT n) 
  → Acc _<′_ (weight s)
  → (ϕ : Interpretation n)
  → eval-nnf (sat-to-nnf s) ϕ ≡ true
  → eval-sat s ϕ ≡ true 
from-wf (Atom x) wf ϕ r = r
from-wf (Not (Atom x)) wf ϕ r = r
from-wf (Not (Not s)) (acc go) ϕ r rewrite not-not-elim (eval-sat s ϕ) = from-wf s (go (weight s) (≤′-step ≤′-refl)) ϕ r
from-wf (Not (And a b)) (acc go) ϕ r with bool6 {eval-nnf (sat-to-nnf (Not a)) ϕ} {eval-nnf (sat-to-nnf (Not b)) ϕ} r 
... | inj₁ x rewrite de-morgan1 (eval-sat a ϕ) (eval-sat b ϕ) | from-wf (Not a) (go (suc (weight a)) (s≤′s (s≤′s (m≤′m+n (weight a) (weight b))))) ϕ x = refl
... | inj₂ y rewrite de-morgan1 (eval-sat a ϕ) (eval-sat b ϕ) | from-wf (Not b) (go (suc (weight b)) (s≤′s (s≤′s (n≤′m+n (weight a) (weight b))))) ϕ y = bool3 refl 
from-wf (Not (Or a b)) (acc go) ϕ r with bool5 {eval-nnf (sat-to-nnf (Not a)) ϕ} {eval-nnf (sat-to-nnf (Not b)) ϕ} r 
... | p1 , p2  rewrite de-morgan2 (eval-sat a ϕ) (eval-sat b ϕ) | from-wf  (Not a) (go (suc (weight a)) (m≤′m+n (suc (suc (weight a))) (weight b))) ϕ p1 | from-wf (Not b) (go (suc (weight b)) (s≤′s (s≤′s (n≤′m+n (weight a) (weight b))))) ϕ p2 = refl 
from-wf (And a b) (acc go) ϕ r with bool5 {eval-nnf (sat-to-nnf a) ϕ} {eval-nnf (sat-to-nnf b) ϕ} r
... | p1 , p2 rewrite from-wf a (go (weight a) (s≤′s (m≤′m+n (weight a) (weight b)))) ϕ p1 | from-wf b (go (weight b) (s≤′s (n≤′m+n (weight a) (weight b)))) ϕ p2 = refl
from-wf (Or a b) (acc go) ϕ r with bool6 {eval-nnf (sat-to-nnf a) ϕ} {eval-nnf (sat-to-nnf b) ϕ} r 
... | inj₁ x rewrite from-wf a (go (weight a) (m≤′m+n (suc (weight a)) (weight b))) ϕ x = refl
... | inj₂ y rewrite from-wf b (go (weight b) (s≤′s (n≤′m+n (weight a) (weight b)))) ϕ y = bool3 refl


to : ∀{n} (s : SAT n) → SatisfiableSAT s → SatisfiableNNF (sat-to-nnf s)
to s (fst , snd) = fst , to-wf s (<′-wellFounded (weight s)) fst snd

from : ∀{n} (s : SAT n) → SatisfiableNNF (sat-to-nnf s) → SatisfiableSAT s
from s (fst , snd) = fst , from-wf s (<′-wellFounded (weight s)) fst snd

