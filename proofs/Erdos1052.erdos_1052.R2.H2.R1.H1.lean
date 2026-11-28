import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R1
import Mathlib

-- Step Erdos1052.erdos_1052.R2.H2.R1.H1: hypothesis H1 of reduction Erdos1052.erdos_1052.R2.H2.R1
-- Jennifer DeBoer classified this case in Nonexistence of Certain Unitary Perfect Numbers (1993).
-- Credit: @ivillar. Uses Graham1052.core (Graham 1989), the accepted proof by @adammcarter
-- (proofs/Erdos1052.erdos_1052.R1.H1.lean) as inlined in the reduction file.
-- Strategy. For c = 9, u = 10 (2^a + 1). Then 5 divides the left side, so 5 is in S. Removing 5
-- (factor 6 / 5) and adding 3 (factor 4 / 3) turns the equation into Graham's squarefree
-- balance. Its prime set omits 5, so Graham forces a = 1, outside the required a ≥ 5.

/-- In Graham's squarefree balance a missing factor 5 forces the exponent to be one. -/
theorem OMA.exponent_one_of_five_absent {a : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P) (ha : 1 ≤ a)
    (hE : (2 ^ a + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (a + 1) * ∏ p ∈ P, p) : a = 1 := by
  rcases OMA.R_Erdos1052_erdos_1052_R2_H2_R1.Graham1052.core hP hE ha with
    ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact h
  all_goals exact (h5 (by decide)).elim

open Finset in
theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H1 := by
  unfold OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H1
  apply Set.finite_empty.subset
  rintro a ⟨h5, S, -, -, hS, hE⟩
  have ha0 : a ≠ 0 := by omega
  have h2m : (2 : ℕ) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  have hpf : (2 ^ a * 9).primeFactors = {2, 3} := by
    rw [Nat.primeFactors_mul h2m (by norm_num), Nat.primeFactors_prime_pow ha0 Nat.prime_two, h9,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    rfl
  have hf : (2 ^ a * 9).factorization = Finsupp.single 2 a + Finsupp.single 3 2 := by
    rw [Nat.factorization_mul h2m (by norm_num), h9,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three]
  have hf2 : (2 ^ a * 9).factorization 2 = a := by
    norm_num [hf, Finsupp.add_apply, Finsupp.single_apply]
  have hf3 : (2 ^ a * 9).factorization 3 = 2 := by
    norm_num [hf, Finsupp.add_apply, Finsupp.single_apply]
  rw [hpf, Finset.prod_pair (by norm_num), hf2, hf3] at hE
  -- hE : (1 + 2 ^ a) * (1 + 3 ^ 2) * ∏ (1 + p) = 2 * (2 ^ a * 9) * ∏ p
  have hb2 : 2 ∣ 2 ^ a * 9 := dvd_mul_of_dvd_left (dvd_pow_self 2 ha0) 9
  have hb3 : 3 ∣ 2 ^ a * 9 := dvd_mul_of_dvd_right (by norm_num) _
  -- 5 ∈ S
  have h5S : 5 ∈ S := by
    have hd : 5 ∣ 2 * (2 ^ a * 9) * ∏ p ∈ S, p := by
      rw [← hE]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by norm_num) _) _
    have h5p : Nat.Prime 5 := by norm_num
    have hpow : ¬ 5 ∣ 2 ^ a := fun h =>
      (by decide : ¬ (5 : ℕ) ∣ 2) (h5p.dvd_of_dvd_pow h)
    have hs : 5 ∣ ∏ p ∈ S, p := by
      simpa [h5p.dvd_mul, hpow, show ¬ (5 : ℕ) ∣ 2 by decide,
        show ¬ (5 : ℕ) ∣ 9 by decide] using hd
    obtain ⟨p, hp, hd⟩ := (Prime.dvd_finsetProd_iff h5p.prime _).mp hs
    exact ((Nat.prime_dvd_prime_iff_eq h5p (hS p hp).1).mp hd) ▸ hp
  set T := S.erase 5
  have h3T : 3 ∉ T := fun h => (hS 3 (Finset.mem_of_mem_erase h)).2 hb3
  have hP : ∀ p ∈ insert 3 T, p.Prime ∧ p ≠ 2 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨Nat.prime_three, by norm_num⟩
    · have := hS p (Finset.mem_of_mem_erase hp)
      exact ⟨this.1, fun h => this.2 (h ▸ hb2)⟩
  have e1 : ∏ p ∈ S, (1 + p) = 6 * ∏ p ∈ T, (p + 1) := by
    rw [← Finset.mul_prod_erase S _ h5S]
    congr 1
    exact Finset.prod_congr rfl fun p _ => add_comm 1 p
  rw [e1, ← Finset.mul_prod_erase S (fun p => p) h5S] at hE
  have ha : a = 1 := OMA.exponent_one_of_five_absent hP (by simp [T]) (by omega) (by
    rw [Finset.prod_insert h3T, Finset.prod_insert h3T, pow_succ]
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 15 by norm_num)
    convert hE using 1 <;> ring)
  change False
  omega
