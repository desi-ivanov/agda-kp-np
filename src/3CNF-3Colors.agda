module 3CNF-3Colors where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Vec using (Vec; lookup; zip; allFin; _∷_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_; _<′_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Product using (_,_; _×_; ∃; Σ-syntax; ∃-syntax; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Vec.Relation.Unary.All using (All; all)
open import 3CNF
open import 3Colors

postulate
  3CNF-to-3Colors : ∀{n} → 3CNF n → Σ ℕ Graph
  theorem1 : ∀{n} (f : 3CNF n) → Satisfiable3CNF f → ∃ (λ color → GoodColoring (proj₂ (3CNF-to-3Colors f) , color))
  