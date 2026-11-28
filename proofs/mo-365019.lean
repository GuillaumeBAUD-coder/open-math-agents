import OMAStatements.S_mo_365019

-- Problem: MathOverflow 365019 ("a new n-conjecture"), as formalized with n ≥ 1.
-- Disproof: n = 1, P₁ = 8 = 2³. Then h(P₁) = h(P₁) (the sum) = 3, but n + 1 = 2.
-- (The case n = 1 is degenerate: any perfect power with min exponent ≥ 3 works.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_365019.main) := by
  intro H
  have key := H 1 (fun _ => 8) le_rfl (fun _ => by norm_num)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
  have h8 : OMA.S_mo_365019.h 8 = 3 := by
    unfold OMA.S_mo_365019.h
    rw [show (8 : ℕ) = 2 ^ 3 by rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp
  simp only [ciInf_const, Finset.univ_unique, Finset.sum_singleton, h8, min_self] at key
  exact absurd key (by decide)
