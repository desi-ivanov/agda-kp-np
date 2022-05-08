module SAT where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _<′_; _≤′_; ≤′-step; ≤′-refl)
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
open import Function.Equivalence using (_⇔_)
open import Relation.Nullary using (¬_; Dec; yes; no; _because_)
open import Induction.Nat
open import Induction.WellFounded

data SAT (n : ℕ) : Set where
  Atom : Fin n → SAT n
  Not : SAT n → SAT n
  And : SAT n → SAT n → SAT n
  Or : SAT n → SAT n → SAT n

Interpretation = Vec Bool

weight : ∀{n} → SAT n → ℕ
weight (Atom x) = 1
weight (Not s) = 1 + weight s
weight (And a b) = 1 + weight a + weight b
weight (Or a b) = 1 + weight a + weight b


eval-sat : ∀{n} →  SAT n → Interpretation n → Bool
eval-sat (Atom x) ϕ = lookup ϕ x
eval-sat (Not x) ϕ = not (eval-sat x ϕ)
eval-sat (And a b) ϕ = (eval-sat a ϕ) ∧ (eval-sat b ϕ)
eval-sat (Or a b) ϕ = (eval-sat a ϕ) ∨ (eval-sat b ϕ)

SatisfiableSAT : ∀{n} → SAT n → Set
SatisfiableSAT s = ∃[ ϕ ] (eval-sat s ϕ ≡ true)

Equivalent : ∀{n} → SAT n → SAT n → Set
Equivalent {n} a b = (ϕ : Interpretation n) → (eval-sat a ϕ ≡ eval-sat b ϕ)
