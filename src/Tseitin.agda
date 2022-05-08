
-- Impl : ∀{n} → (a b : Fin n) → NNF n
-- Impl a b = Or (Neg a) (Pos b)

-- Iff : ∀{n} → (a b : Fin n) → NNF n
-- Iff a b = And (Impl a b) (Impl b a)


-- liftliteral : ∀{n} → Literal n → (m : ℕ) → n ≤ m → Literal m
-- liftliteral (pos x) m p = pos (inject≤ x p)
-- liftliteral (neg x) m p = neg (inject≤ x p)

-- lifclause : ∀{n} → Clause n → (m : ℕ) → n ≤ m → Clause m
-- lifclause (one x) m p = one (liftliteral x m p)
-- lifclause (x , c) m p = (liftliteral x m p) , (lifclause c m p)

-- liftcnf : ∀{n} → CNF n → (m : ℕ) → n ≤ m → CNF m
-- liftcnf (one x) m p = one (lifclause x m p)
-- liftcnf (x , c) m p = (lifclause x m p) , (liftcnf c m p)

-- -- x ⇔ a ∧ b
-- iff-and : ∀{n} → (x a b : Fin n) → CNF n
-- iff-and x a b = (neg x , one (pos a )) , (neg x , one (pos b)) , (pos x , one (neg a)) , one (pos x , one (pos b))

-- -- x ⇔ a ∨ b
-- -- (¬x ∨ a ∨ b) , (x ∨ ¬a) , (x ∨ ¬b)
-- iff-or : ∀{n} → (x a b : Fin n) → CNF n
-- iff-or x a b = (neg x , pos a , one (pos b)) , (pos x , one (neg a)) , one (pos x , one (pos b))



-- extend : ∀{n} → NNF n → Σ ℕ (λ m → Fin (m + n) × CNF (m + n))
-- extend {n} (Pos x) = 1 , fromℕ n , one (one (pos (inject₁ x)))
-- extend {n} (Neg x) = 1 , fromℕ n , one (one (neg (inject₁ x)))
-- extend {n} (And a b) with extend a | extend b 
-- ... | ma , va , fa | mb , vb , fb = 
--   let c = iff-and {1 + (mb + (ma + n))}  (fromℕ (mb + (ma + n))) (raise {ma + n} (1 + mb) va) {!   !} 
--   in 1 + (ma + mb) , {!   !} , concat-cnf {!  c !} {!   !}
-- extend (Or a b) with extend a | extend b
-- ... | ma , cnfa | mb , cnfb = {!   !}
-- -- extend (And a b) with extend a | extend b 
-- -- ... | m1 , p1 , cnfa | m2 , q1 , cnfb = 
-- --   let rw = Iff {1 + m1 + m2} (inject≤ (fromℕ m1) (s≤s (m≤m+n m1 m2))) (inject≤ (fromℕ m2) {!   !}) in 
-- --   let lfta = liftcnf cnfa (1 + m1 + m2) {!   !} in
-- --   let lftb = liftcnf cnfb (1 + m1 + m2) {!   !} in
-- --       1 + m1 + m2 , {!   !} , more {! rw  !} (concat-cnf lfta lftb)
-- -- extend (Or a b) = {!   !}

-- tseitin : ∀{n} → NNF n → Σ ℕ CNF 
-- tseitin {n} f = {!   !}  