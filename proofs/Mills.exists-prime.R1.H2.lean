import OMAReductions.R_Mills_exists_prime_R1
import Mathlib

-- Step Mills.exists-prime.R1.H2: hypothesis H2 of reduction Mills.exists-prime.R1 (Mills' nested-interval lemma)
-- Credit: @ivillar (original proof), following W. H. Mills (1947).
-- Strategy. u n = (q n)^(1/3^(n+1)) increases and v n = (q n + 1)^(1/3^(n+1)) strictly decreases,
-- with u n < v n. A = sup u satisfies u n <= A < v n, so q n <= A^(3^(n+1)) < q n + 1.

theorem OMA.solution : OMA.R_Mills_exists_prime_R1.H2 := by
  intro q hq2 hlo hhi
  let k : ℕ → ℕ := fun n => 3 ^ (n + 1)
  have hk0 : ∀ n, k n ≠ 0 := fun n => pow_ne_zero _ (by norm_num)
  have hks : ∀ n, k (n + 1) = k n * 3 := fun n => by simp only [k]; ring
  let u : ℕ → ℝ := fun n => (q n : ℝ) ^ ((k n : ℝ)⁻¹)
  let v : ℕ → ℝ := fun n => ((q n : ℝ) + 1) ^ ((k n : ℝ)⁻¹)
  have hu0 : ∀ n, 0 ≤ u n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hv0 : ∀ n, 0 ≤ v n := fun n => Real.rpow_nonneg (by positivity) _
  have hupow : ∀ n, u n ^ k n = q n := fun n =>
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (hk0 n)
  have hvpow : ∀ n, v n ^ k n = (q n : ℝ) + 1 := fun n =>
    Real.rpow_inv_natCast_pow (by positivity) (hk0 n)
  have hustep : ∀ n, u n ≤ u (n + 1) := by
    intro n
    rw [← pow_le_pow_iff_left₀ (hu0 n) (hu0 (n + 1)) (hk0 (n + 1)), hupow (n + 1), hks, pow_mul,
      hupow n]
    exact_mod_cast hlo n
  have hvstep : ∀ n, v (n + 1) < v n := by
    intro n
    rw [← pow_lt_pow_iff_left₀ (hv0 (n + 1)) (hv0 n) (hk0 (n + 1)), hvpow (n + 1), hks, pow_mul,
      hvpow n]
    exact_mod_cast hhi n
  have huv : ∀ n, u n < v n := by
    intro n
    rw [← pow_lt_pow_iff_left₀ (hu0 n) (hv0 n) (hk0 n), hupow, hvpow]
    linarith
  have hmono : Monotone u := monotone_nat_of_le_succ hustep
  have hanti : Antitone v := antitone_nat_of_succ_le (fun n => (hvstep n).le)
  have hub : ∀ n m, u n ≤ v m := by
    intro n m
    calc u n ≤ u (max n m) := hmono (le_max_left _ _)
      _ ≤ v (max n m) := (huv _).le
      _ ≤ v m := hanti (le_max_right _ _)
  have hbdd : BddAbove (Set.range u) := ⟨v 0, by rintro _ ⟨n, rfl⟩; exact hub n 0⟩
  have hAu : ∀ n, u n ≤ ⨆ m, u m := fun n => le_ciSup hbdd n
  have hAv : ∀ n, (⨆ m, u m) ≤ v n := fun n => ciSup_le (fun m => hub m n)
  have hA0 : 0 ≤ ⨆ m, u m := (hu0 0).trans (hAu 0)
  refine ⟨⨆ m, u m, ?_, fun n => ?_⟩
  · have h0 : 1 < u 0 := by
      by_contra h
      push Not at h
      have h1 : u 0 ^ k 0 ≤ 1 := pow_le_one₀ (hu0 0) h
      rw [hupow] at h1
      have h2 : (2 : ℝ) ≤ q 0 := by exact_mod_cast hq2 0
      linarith
    exact h0.trans_le (hAu 0)
  · show ⌊(⨆ m, u m) ^ k n⌋₊ = q n
    rw [Nat.floor_eq_iff (pow_nonneg hA0 _)]
    constructor
    · have h1 := pow_le_pow_left₀ (hu0 n) (hAu n) (k n)
      rw [hupow] at h1
      exact h1
    · have h1 := pow_lt_pow_left₀ ((hAv (n + 1)).trans_lt (hvstep n)) hA0 (hk0 n)
      rw [hvpow] at h1
      exact h1
