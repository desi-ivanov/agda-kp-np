module CNF where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _<′_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Vec using (lookup)
open import Data.Product using (_,_; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Fin using (Fin)
open import SAT using (Interpretation)

data Literal (n : ℕ) : Set where
  pos : (Fin n) → Literal n
  neg : (Fin n) → Literal n

data Clause (n : ℕ) : Set where
  one : Literal n → Clause n
  _,_ : Literal n → Clause n → Clause n

data CNF (n : ℕ) : Set where
  one : Clause n → CNF n
  _,_ : Clause n → CNF n → CNF n

eval-literal : ∀{n} → Literal n → Interpretation n → Bool
eval-literal (pos x) ϕ = lookup ϕ x
eval-literal (neg x) ϕ = not (lookup ϕ x)

eval-clause : ∀{n} → Clause n → Interpretation n → Bool
eval-clause (one x) ϕ = eval-literal x ϕ
eval-clause (x , xs) ϕ = eval-literal x ϕ ∨ eval-clause xs ϕ 

eval-cnf : ∀{n} → CNF n → Interpretation n → Bool
eval-cnf (one x) ϕ = eval-clause x ϕ
eval-cnf (x , xs) ϕ = eval-clause x ϕ ∧ eval-cnf xs ϕ

concat-cnf : ∀{n} → CNF n → CNF n → CNF n
concat-cnf (one x) b = x , b
concat-cnf (x , a) b = x , (concat-cnf a b)

SatisfiableCNF : ∀{n} → CNF n → Set
SatisfiableCNF s = ∃[ ϕ ] (eval-cnf s ϕ ≡ true)


