import OMAStatements.S_mse_2259412
import Mathlib

-- Problem: mse-2259412, infinitely many primes divide some 1! + 2! + ... + n!.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Suppose only the primes of a finite set P divide some a(n), and let M be their product.
-- For m > n one has a(m) = a(n) + (n+1)! * (1 + (n+2) * V), so for a prime p dividing n + 2
-- the difference a(m) - a(n) has the same p-adic valuation as (n+1)!, which is at most n + 1.
-- Hence, for each p in P, as soon as p^(n0+2) divides a(n0) for one n0 with M | n0 + 2, the
-- power p^(n0+2) divides no later a(m). So for all large n with M | n + 2, no p^(n+2) with p
-- in P divides a(n), which forces a(n) to divide M^(n+1). But a(n) >= n! > M^(n+1) for large n.

namespace MSE2259412

open OMA.S_mse_2259412

lemma a_succ (n : ℕ) : a (n + 1) = a n + (n + 1).factorial := by
  simp [a, Finset.sum_Icc_succ_top]

lemma a_diff (n d : ℕ) : ∃ V, a (n + 1 + d) = a n + (n + 1).factorial * (1 + (n + 2) * V) := by
  induction d with
  | zero => exact ⟨0, by simp [a_succ]⟩
  | succ d ih =>
    obtain ⟨V, hV⟩ := ih
    obtain ⟨W, hW⟩ := Nat.factorial_dvd_factorial (show n + 2 ≤ n + 1 + d + 1 by omega)
    refine ⟨V + W, ?_⟩
    rw [← add_assoc, a_succ, hV, hW, Nat.factorial_succ (n + 1)]
    ring

lemma bound_exists (M p : ℕ) (hp : p.Prime) (hpM : p ∣ M) :
    ∃ B, ∀ n, B ≤ n → M ∣ n + 2 → ¬ p ^ (n + 2) ∣ a n := by
  by_cases h : ∃ n0, M ∣ n0 + 2 ∧ p ^ (n0 + 2) ∣ a n0
  · obtain ⟨n0, hM, hdiv⟩ := h
    refine ⟨n0 + 1, fun n hn _ hcon => ?_⟩
    obtain ⟨d, rfl⟩ : ∃ d, n = n0 + 1 + d := ⟨n - (n0 + 1), by omega⟩
    obtain ⟨V, hV⟩ := a_diff n0 d
    have h1 := (pow_dvd_pow p (by omega : n0 + 2 ≤ n0 + 1 + d + 2)).trans hcon
    rw [hV, Nat.dvd_add_right hdiv] at h1
    have h6 := (Nat.Coprime.pow_left (n0 + 2) ((hp.coprime_iff_not_dvd).2 fun h3 =>
      hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left
        ((hpM.trans hM).mul_right V)).mp h3)))).dvd_of_dvd_mul_right h1
    have := (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp h6
    have := Nat.factorization_factorial_le_div_pred hp (n0 + 1)
    have := Nat.div_le_self (n0 + 1) (p - 1)
    omega
  · exact ⟨0, fun n _ hM hcon => h ⟨n, hM, hcon⟩⟩

theorem main_proof : {p : ℕ | p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ p ∣ a n}.Infinite := by
  intro hfin
  have hPmem (p) : p ∈ hfin.toFinset ↔ (p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ p ∣ a n) := by simp
  generalize hfin.toFinset = P at hPmem
  have hprime (p) (hp : p ∈ P) : p.Prime := ((hPmem p).mp hp).1
  have hMpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  choose! f hf using fun p hp => bound_exists _ p (hprime p hp) (Finset.dvd_prod_of_mem id hp)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (Nat.eventually_pow_lt_factorial_sub (∏ p ∈ P, p) 1)
  have htM := Nat.le_mul_of_pos_right (P.sup f + N0 + 3) hMpos
  obtain ⟨n, hn2, hnB, hnN, hn1⟩ : ∃ n : ℕ, n + 2 = (P.sup f + N0 + 3) * (∏ p ∈ P, p) ∧
      P.sup f ≤ n ∧ N0 ≤ n + 1 ∧ 1 ≤ n := ⟨(P.sup f + N0 + 3) * (∏ p ∈ P, p) - 2, by omega, by omega, by omega, by omega⟩
  have hdvd : a n ∣ ∏ p ∈ P, p ^ (n + 1) := by
    refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2 fun p k hp hpk => ?_
    rcases k with _ | k
    · simp
    have hpP := (hPmem p).mpr ⟨hp, n, hn1, (dvd_pow_self p k.succ_ne_zero).trans hpk⟩
    refine (pow_dvd_pow p ?_).trans (Finset.dvd_prod_of_mem (fun q => q ^ (n + 1)) hpP)
    by_contra hcon
    exact hf p hpP n ((Finset.le_sup hpP).trans hnB) (hn2 ▸ dvd_mul_left _ _)
      ((pow_dvd_pow p (by omega)).trans hpk)
  have hle := Nat.le_of_dvd (Finset.prod_pos (fun p hp => pow_pos (hprime p hp).pos _)) hdvd
  rw [Finset.prod_pow] at hle
  have := hN0 (n + 1) hnN
  have := Finset.single_le_sum (f := Nat.factorial) (fun _ _ => Nat.zero_le _)
    (Finset.mem_Icc.2 ⟨hn1, le_rfl⟩)
  simp only [a] at *
  simp at *
  omega

end MSE2259412

theorem OMA.solution : type_of% @OMA.S_mse_2259412.main := MSE2259412.main_proof
