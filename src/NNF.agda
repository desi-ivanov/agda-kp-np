module NNF where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; lookup)
open import Data.Product using (_,_; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import SAT


data NNF (n : ℕ) : Set where
  Pos : (Fin n) → NNF n
  Neg : (Fin n) → NNF n
  And : NNF n → NNF n → NNF n
  Or : NNF n → NNF n → NNF n

eval-nnf : ∀{n} → NNF n → Interpretation n → Bool
eval-nnf (Pos x) ϕ = lookup ϕ x
eval-nnf (Neg x) ϕ = not (lookup ϕ x)
eval-nnf (And a b) ϕ = (eval-nnf a ϕ) ∧ (eval-nnf b ϕ)
eval-nnf (Or a b) ϕ = (eval-nnf a ϕ) ∨ (eval-nnf b ϕ)

SatisfiableNNF : ∀{n} → NNF n → Set
SatisfiableNNF s = ∃[ ϕ ] (eval-nnf s ϕ ≡ true)
