import OMAReductions.R_Erdos686_erdos_686_R1
import Mathlib

-- Step Erdos686.erdos_686.R1.H1: hypothesis H1 of reduction Erdos686.erdos_686.R1
-- Credit: @ivillar
-- H1: every non-square N ≥ 2 is a ratio of products of k consecutive integers (here k = 2).
-- Proof: take a Pell solution u^2 = N v^2 + 1 with v ≥ 1, and put s = N v^2,
-- n + 1 = s + u v and m + 1 = s + N u v. Then (m+1)(m+2) = N (n+1)(n+2), because
-- the difference is (N - 1) N v^2 (N v^2 + 1 - u^2) = 0, and m - n = (N - 1) u v ≥ 2.

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1.H1 := by
  unfold OMA.R_Erdos686_erdos_686_R1.H1
  intro N hN hsq
  have hd : ¬ IsSquare (N : ℤ) := by rwa [Int.isSquare_natCast_iff]
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨x0, y0, hxy, hy0⟩ := Pell.exists_of_not_isSquare hN0 hd
  have h1 : (x0.natAbs : ℤ) ^ 2 = x0 ^ 2 := Int.natAbs_sq x0
  have h2 : (y0.natAbs : ℤ) ^ 2 = y0 ^ 2 := Int.natAbs_sq y0
  generalize hu : x0.natAbs = u at h1
  generalize hv : y0.natAbs = v at h2
  have huvZ : (u : ℤ) ^ 2 = (N : ℤ) * (v : ℤ) ^ 2 + 1 := by
    rw [h1, h2]
    linarith
  have huv : u ^ 2 = N * v ^ 2 + 1 := by exact_mod_cast huvZ
  have hv1 : 1 ≤ v := by
    rw [← hv]
    exact Int.natAbs_pos.mpr hy0
  have hu2 : 2 ≤ u := by nlinarith
  have huv2 : 2 ≤ u * v := by nlinarith
  obtain ⟨n, hn⟩ : ∃ n, n + 1 = N * v ^ 2 + u * v := ⟨N * v ^ 2 + u * v - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = N * v ^ 2 + N * u * v :=
    ⟨N * v ^ 2 + N * u * v - 1, by
      have : u * v ≤ N * u * v := by nlinarith
      omega⟩
  refine ⟨2, le_refl 2, n, m, ?_, ?_⟩
  · have h3 : 2 * (u * v) ≤ N * u * v := by nlinarith
    omega
  · rw [show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
      Finset.prod_pair (by norm_num), Finset.prod_pair (by norm_num)]
    have hnQ : (n : ℚ) = N * v ^ 2 + u * v - 1 := by
      have := congrArg (Nat.cast (R := ℚ)) hn
      push_cast at this
      linarith
    have hmQ : (m : ℚ) = N * v ^ 2 + N * u * v - 1 := by
      have := congrArg (Nat.cast (R := ℚ)) hm
      push_cast at this
      linarith
    have huvQ : (u : ℚ) ^ 2 = (N : ℚ) * (v : ℚ) ^ 2 + 1 := by exact_mod_cast huv
    have hpos : (0 : ℚ) < ((n : ℚ) + 1) * ((n : ℚ) + 2) := by positivity
    push_cast
    rw [eq_div_iff hpos.ne']
    rw [hnQ, hmQ]
    linear_combination (-((N : ℚ) - 1) * (N : ℚ) * (v : ℚ) ^ 2) * huvQ
