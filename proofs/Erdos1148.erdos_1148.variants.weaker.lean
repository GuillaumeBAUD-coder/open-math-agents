import FormalConjectures.ErdosProblems.«1148»

-- Problem: Erdős Problem 1148 — weaker
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1148.lean:95 (declaration Erdos1148.erdos_1148.variants.weaker)
-- Credit: @jonas-klesen (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea. Let `m = ⌊√n⌋` and `e = n - m²`, so `0 ≤ e ≤ 2m`.
-- * `e = 0`:          `n = m² + 0² - 0²`.
-- * `e = 2j + 1`:     `n = m² + (j+1)² - j²` with `j + 1 ≤ m`, so all squares are at most `n`.
-- * `e = 2i`, `i ≥ 1`: with `k = m - i`, `n = (m+1)² + k² - (k+1)²`, and
--   `(m+1)² = m² + 2m + 1 ≤ n + 2√n` because `n ≥ m² + 1` and `√n ≥ m`.

namespace OMAErdos1148

lemma bound_small (n x : ℕ) (hx : x * x ≤ n) : ((x : ℝ)) ^ 2 ≤ n + 2 * Real.sqrt n := by
  have h0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h1 : ((x : ℝ)) ^ 2 ≤ n := by exact_mod_cast (by nlinarith : x ^ 2 ≤ n)
  linarith

lemma bound_big (n m x : ℕ) (hm : m * m + 1 ≤ n) (hx : x ≤ m + 1) :
    ((x : ℝ)) ^ 2 ≤ n + 2 * Real.sqrt n := by
  have hs : (m : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (by nlinarith : m ^ 2 ≤ n)
  have h1 : ((m : ℝ)) * m + 1 ≤ n := by exact_mod_cast hm
  have h2 : (x : ℝ) ≤ m + 1 := by exact_mod_cast hx
  have h3 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

end OMAErdos1148

open OMAErdos1148 in
theorem OMA.solution : type_of% @Erdos1148.erdos_1148.variants.weaker := by
  intro n
  unfold Erdos1148.erdos_1148_weaker_prop
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.sqrt n := ⟨_, rfl⟩
  have h1 : m * m ≤ n := hm ▸ Nat.sqrt_le n
  have h2 : n < (m + 1) * (m + 1) := hm ▸ Nat.lt_succ_sqrt n
  have h3 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  clear hm
  rcases Nat.even_or_odd (n - m * m) with ⟨i, hi⟩ | ⟨j, hj⟩
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · have hn : n = m * m := by omega
      refine ⟨m, 0, 0, ?_, bound_small n m h1, bound_small n 0 (by omega),
        bound_small n 0 (by omega)⟩
      rw [hn]
      simp [pow_two]
    · have hn : n = m * m + 2 * i := by omega
      have him : i ≤ m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, m = i + k := ⟨m - i, by omega⟩
      refine ⟨i + k + 1, k, k + 1, ?_, bound_big n (i + k) _ (by omega) le_rfl,
        bound_big n (i + k) _ (by omega) (by omega),
        bound_big n (i + k) _ (by omega) (by omega)⟩
      apply (Nat.sub_eq_of_eq_add _).symm
      rw [hn]
      ring
  · have hn : n = m * m + 2 * j + 1 := by omega
    have hjm : j + 1 ≤ m := by omega
    refine ⟨m, j + 1, j, ?_, bound_small n m h1,
      bound_small n (j + 1) (le_trans (Nat.mul_le_mul hjm hjm) h1),
      bound_small n j (le_trans (Nat.mul_le_mul (by omega) (by omega)) h1)⟩
    apply (Nat.sub_eq_of_eq_add _).symm
    rw [hn]
    ring
