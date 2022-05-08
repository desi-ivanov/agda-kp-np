module 3CNF where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _<′_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Vec using (Vec; lookup; _∷_; [])
open import Data.Product using (_,_; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Fin using (Fin)
open import SAT using (Interpretation)

data Literal (n : ℕ) : Set where
  pos : (Fin n) → Literal n
  neg : (Fin n) → Literal n

Clause : ℕ → Set
Clause n = Vec (Literal n) 3

data 3CNF (n : ℕ) : Set where
  one : Clause n → 3CNF n
  _,_ : Clause n → 3CNF n → 3CNF n

eval-literal : ∀{n} → Literal n → Interpretation n → Bool
eval-literal (pos x) ϕ = lookup ϕ x
eval-literal (neg x) ϕ = not (lookup ϕ x)

eval-clause : ∀{n} → Clause n → Interpretation n → Bool
eval-clause (a ∷ b ∷ c ∷ []) ϕ = eval-literal a ϕ ∨ eval-literal b ϕ ∨ eval-literal c ϕ

eval-cnf : ∀{n} → 3CNF n → Interpretation n → Bool
eval-cnf (one x) ϕ = eval-clause x ϕ
eval-cnf (x , xs) ϕ = eval-clause x ϕ ∧ eval-cnf xs ϕ


Satisfiable3CNF : ∀{n} → 3CNF n → Set
Satisfiable3CNF s = ∃[ ϕ ] (eval-cnf s ϕ ≡ true)

