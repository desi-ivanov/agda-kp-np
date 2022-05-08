module BoolProps where
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

not-not-elim : (x : Bool) → not (not x) ≡ x
not-not-elim false = refl
not-not-elim true = refl 

bool2 : ∀{a b}  → not (a ∧ b) ≡ true → not a ≡ true ⊎ not b ≡ true
bool2 {false} {false} r = inj₁ refl
bool2 {false} {true} r = inj₁ refl
bool2 {true} {false} r = inj₂ refl

bool3 : ∀{a b} → b ≡ true → a ∨ b ≡ true
bool3 {false} {true} r = refl
bool3 {true} {true} r = refl

bool4 : ∀{a b} → not (a ∨ b) ≡ true → not a ≡ true × not b ≡ true
bool4 {false} {false} r = refl , refl

bool5 : ∀{a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
bool5 {true} {true} r = refl , refl

bool6 : ∀{a b} → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
bool6 {false} {true} r = inj₂ refl
bool6 {true} {false} r = inj₁ refl
bool6 {true} {true} r = inj₁ refl

de-morgan1 : (a b : Bool) → not (a ∧ b) ≡ not a ∨ not b
de-morgan1 false false = refl
de-morgan1 false true = refl
de-morgan1 true false = refl
de-morgan1 true true = refl 

de-morgan2 : (a b : Bool) → not (a ∨ b) ≡ not a ∧ not b
de-morgan2 false false = refl
de-morgan2 false true = refl
de-morgan2 true false = refl
de-morgan2 true true = refl

