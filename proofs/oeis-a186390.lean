import OMAStatements.S_oeis_a186390
import Mathlib

namespace OMA.S_oeis_a186390

open PowerSeries

lemma a_eq (n : ℕ) : a n = (n : ℤ) + (((g n - 1) / 6 : ℕ) : ℤ) := by
  unfold a
  congr 2
  have : ((Finset.Icc 1 (g n)).filter fun i => f i < g n) = Finset.Icc 1 ((g n - 1) / 6) := by
    ext i; rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]; unfold f; omega
  rw [this]; simp

lemma g_shift (n : ℕ) : g (n + 12) = g n + 12 * n + 78 := by
  unfold g
  have h1 : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  have h2 : 2 ∣ (n + 12) * (n + 12 + 1) := (Nat.even_mul_succ_self _).two_dvd
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  rw [hk, hl]
  have : l = k + 12 * n + 78 := by nlinarith
  omega

lemma a_shift (n : ℕ) (hn : 1 ≤ n) : a (n + 12) = a n + 2 * n + 25 := by
  rw [a_eq, a_eq, g_shift]
  have : 1 ≤ g n := by
    unfold g
    have : 1 * 2 ≤ n * (n + 1) := by nlinarith
    omega
  have : (g n + 12 * n + 78 - 1) / 6 = (g n - 1) / 6 + 2 * n + 13 := by omega
  rw [this]; push_cast; ring

lemma rec_ok : ∀ n : ℕ, 7 < n →
      a n = 2 * a (n - 1) - 2 * a (n - 2) + 3 * a (n - 3) - 3 * a (n - 4) + 2 * a (n - 5) -
        2 * a (n - 6) + a (n - 7) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n < 20
    · interval_cases n <;> simp [a_eq, g] 
    · obtain ⟨q, rfl⟩ : ∃ q, n = q + 20 := ⟨n - 20, by omega⟩
      have h0 := ih (q + 8) (by omega) (by omega)
      have s0 := a_shift (q + 8) (by omega)
      have s1 := a_shift (q + 7) (by omega)
      have s2 := a_shift (q + 6) (by omega)
      have s3 := a_shift (q + 5) (by omega)
      have s4 := a_shift (q + 4) (by omega)
      have s5 := a_shift (q + 3) (by omega)
      have s6 := a_shift (q + 2) (by omega)
      have s7 := a_shift (q + 1) (by omega)
      have h0' : a (q + 8) = 2 * a (q + 7) - 2 * a (q + 6) + 3 * a (q + 5) - 3 * a (q + 4)
          + 2 * a (q + 3) - 2 * a (q + 2) + a (q + 1) := h0
      show a (q + 20) = 2 * a (q + 19) - 2 * a (q + 18) + 3 * a (q + 17) - 3 * a (q + 16)
          + 2 * a (q + 15) - 2 * a (q + 14) + a (q + 13)
      have t0 : q + 8 + 12 = q + 20 := rfl
      have t1 : q + 7 + 12 = q + 19 := rfl
      have t2 : q + 6 + 12 = q + 18 := rfl
      have t3 : q + 5 + 12 = q + 17 := rfl
      have t4 : q + 4 + 12 = q + 16 := rfl
      have t5 : q + 3 + 12 = q + 15 := rfl
      have t6 : q + 2 + 12 = q + 14 := rfl
      have t7 : q + 1 + 12 = q + 13 := rfl
      rw [t0] at s0; rw [t1] at s1; rw [t2] at s2; rw [t3] at s3
      rw [t4] at s4; rw [t5] at s5; rw [t6] at s6; rw [t7] at s7
      push_cast at *
      linarith

theorem gf_ok :
    ((X - 1) ^ 3 * (X ^ 2 + 1) * (X ^ 2 + X + 1) * PowerSeries.mk a =
      (X * (X ^ 6 - X ^ 2 - 1) : PowerSeries ℤ)) := by
  have hP : ((X - 1) ^ 3 * (X ^ 2 + 1) * (X ^ 2 + X + 1) : PowerSeries ℤ) =
      X ^ 7 - 2 * X ^ 6 + 2 * X ^ 5 - 3 * X ^ 4 + 3 * X ^ 3 - 2 * X ^ 2 + 2 * X - 1 := by ring
  rw [hP]
  ext n
  have key : ∀ k : ℕ, coeff n (X ^ k * PowerSeries.mk a) = if k ≤ n then a (n - k) else 0 := by
    intro k; rw [coeff_X_pow_mul']; simp
  have e : (X ^ 7 - 2 * X ^ 6 + 2 * X ^ 5 - 3 * X ^ 4 + 3 * X ^ 3 - 2 * X ^ 2 + 2 * X - 1 : PowerSeries ℤ) * PowerSeries.mk a
      = X ^ 7 * mk a - 2 * (X ^ 6 * mk a) + 2 * (X ^ 5 * mk a) - 3 * (X ^ 4 * mk a) + 3 * (X ^ 3 * mk a)
        - 2 * (X ^ 2 * mk a) + 2 * (X ^ 1 * mk a) - mk a := by ring
  rw [e]
  have r : (X * (X ^ 6 - X ^ 2 - 1) : PowerSeries ℤ) = X ^ 7 - X ^ 3 - X ^ 1 := by ring
  rw [r]
  have h2 : (2 : PowerSeries ℤ) = C 2 := (map_ofNat C 2).symm
  have h3 : (3 : PowerSeries ℤ) = C 3 := (map_ofNat C 3).symm
  rw [h2, h3]
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow, key, coeff_mk]
  have ha : ∀ k : ℕ, (if k ≤ n then a (n - k) else 0) = (if k ≤ n then a (n - k) else 0) := fun _ => rfl
  by_cases h7 : 7 ≤ n
  · by_cases h8 : n = 7
    · subst h8; simp [a_eq, g]
    · have := rec_ok n (by omega)
      simp only [h7, show 6 ≤ n by omega, show 5 ≤ n by omega, show 4 ≤ n by omega, show 3 ≤ n by omega,
        show 2 ≤ n by omega, show 1 ≤ n by omega, if_true, show ¬ n = 7 from h8, show ¬ n = 3 by omega,
        show ¬ n = 1 by omega, if_false]
      have e1 : n - 1 = n - 1 := rfl
      omega
  · interval_cases n <;> simp [a_eq, g]

end OMA.S_oeis_a186390

theorem OMA.solution : type_of% @OMA.S_oeis_a186390.main := by
  refine ⟨OMA.S_oeis_a186390.rec_ok, OMA.S_oeis_a186390.gf_ok⟩
