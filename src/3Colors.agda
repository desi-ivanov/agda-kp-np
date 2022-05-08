module 3Colors where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Vec using (Vec; lookup; zip; allFin)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_; _<′_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Product using (_,_; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Vec.Relation.Unary.All using (All; all)

Graph : (n : ℕ) → Set
Graph n = Vec (Vec Bool n) n

Coloring = Vec (Fin 3)

enumerate : ∀{n} {A : Set} → Vec A n → Vec (Fin n × A) n
enumerate {n} v = zip (allFin n) v

3Colors = λ n → Graph n × Coloring n

GoodColoring : ∀{n} → 3Colors n → Set
GoodColoring {n} (g , c) = All (λ{ (i , v) →  All (λ{ (j , u) →  i ≡ j ⊎ lookup v j ≡ false ⊎ ¬ (lookup c i) ≡ (lookup c j) }) (enumerate v) }) (enumerate g)

