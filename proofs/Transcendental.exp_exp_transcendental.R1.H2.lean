import OMAReductions.R_Transcendental_exp_exp_transcendental_R1
import Mathlib

/-! Euler: `e` is irrational. If `e = a / b` with `b ≥ 1`, then `b! * (e - ∑_{m ≤ b} 1/m!)` is an integer;
the tail of the exponential series puts it strictly between `0` and `(b + 2) / (b + 1)^2 < 1`. -/

open Finset Nat in
theorem OMA.Step_Transcendental_exp_exp_R1_H2.exp_one_irrational : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  set b := q.den with hbdef
  have hb : 0 < b := q.den_pos
  set S : ℝ := ∑ m ∈ range (b + 1), ((m ! : ℕ) : ℝ)⁻¹ with hS
  have hup := Real.exp_bound (x := 1) (by norm_num) (n := b + 1) (by omega)
  have hlow := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) (b + 2)
  rw [Finset.sum_range_succ] at hlow
  simp only [one_pow, one_div, abs_one, one_mul] at hup hlow
  have hFpos : (0 : ℝ) < (b ! : ℕ) := by exact_mod_cast Nat.factorial_pos b
  have hfac : (((b + 1) ! : ℕ) : ℝ) = ((b : ℝ) + 1) * ((b ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  -- lower bound: e - S ≥ 1/(b+1)!
  have hD_pos : 0 < ((b ! : ℕ) : ℝ) * (Real.exp 1 - S) := by
    have h1 : (0 : ℝ) < (((b + 1) ! : ℕ) : ℝ)⁻¹ := by
      have : (0 : ℝ) < (((b + 1) ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
      exact inv_pos.mpr this
    exact mul_pos hFpos (by linarith)
  -- upper bound
  have hD_lt : ((b ! : ℕ) : ℝ) * (Real.exp 1 - S) < 1 := by
    have h := (abs_le.mp hup).2
    rw [hfac] at h
    push_cast at h
    calc ((b ! : ℕ) : ℝ) * (Real.exp 1 - S)
        ≤ ((b ! : ℕ) : ℝ) * (((b : ℝ) + 1 + 1) / (((b : ℝ) + 1) * ((b ! : ℕ) : ℝ) * ((b : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h hFpos.le
      _ = ((b : ℝ) + 2) / (((b : ℝ) + 1) * ((b : ℝ) + 1)) := by field_simp; ring
      _ < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  -- integrality
  set T : ℕ := ∑ m ∈ range (b + 1), b ! / m ! with hT
  have hTS : ((b ! : ℕ) : ℝ) * S = (T : ℝ) := by
    rw [hS, hT, Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmb : m ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [Nat.cast_div (Nat.factorial_dvd_factorial hmb) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)),
      div_eq_mul_inv]
  have hfb : b ! = b * (b - 1)! := by
    have := Nat.factorial_succ (b - 1)
    rwa [Nat.sub_add_cancel hb] at this
  have hE : ((b ! : ℕ) : ℝ) * Real.exp 1 = (((b - 1)! : ℕ) : ℝ) * (q.num : ℝ) := by
    rw [← hq, Rat.cast_def, hfb]
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    rw [hbdef]
    ring
  set z : ℤ := (((b - 1)! : ℕ) : ℤ) * q.num - (T : ℤ) with hz
  have hzR : (z : ℝ) = ((b ! : ℕ) : ℝ) * (Real.exp 1 - S) := by
    rw [hz, mul_sub, hE, hTS]
    push_cast
    ring
  have h1 : (0 : ℤ) < z := by exact_mod_cast (hzR ▸ hD_pos)
  have h2 : z < 1 := by exact_mod_cast (hzR ▸ hD_lt)
  omega

theorem OMA.solution : OMA.R_Transcendental_exp_exp_transcendental_R1.H2 :=
  OMA.Step_Transcendental_exp_exp_R1_H2.exp_one_irrational
