import OMAStatements.S_oeis_a167894
import Mathlib

namespace A167894Proof

open PowerSeries OMA.S_oeis_a167894

/-- H k is the series whose n-th coefficient is (n + k)! / k!. -/
noncomputable def H (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + k).factorial : ℚ) / (k.factorial : ℚ)

/-- G 0 = 1 and G (k + 1) = H k. -/
noncomputable def G : ℕ → PowerSeries ℚ
  | 0 => 1
  | k + 1 => H k

/-- The tails of the continued fraction: quotients of consecutive G. -/
noncomputable def Q (k : ℕ) : PowerSeries ℚ := G k * (G (k + 1))⁻¹

lemma H_const (k : ℕ) : PowerSeries.constantCoeff (H k) = 1 := by
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [H, PowerSeries.constantCoeff_mk, Nat.zero_add]
  exact div_self hk

lemma G_const (k : ℕ) : PowerSeries.constantCoeff (G k) = 1 := by
  cases k with
  | zero => exact map_one _
  | succ j => exact H_const j

lemma H_zero : H 0 = factorialSeries := by
  unfold H factorialSeries
  ext n
  simp

lemma H_rel0 : H 0 - PowerSeries.X * H 1 = 1 := by
  ext n
  cases n with
  | zero =>
    simp [H]
  | succ m =>
    rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero m)]
    simp [H]

lemma H_rel (j : ℕ) :
    H j = (1 + PowerSeries.C ((j + 1 : ℕ) : ℚ) * PowerSeries.X) * H (j + 1)
      - PowerSeries.C ((j + 2 : ℕ) : ℚ) * PowerSeries.X * H (j + 2) := by
  have hJ : (j.factorial : ℚ) ≠ 0 := by positivity
  have h1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((j : ℚ) + 2) ≠ 0 := by positivity
  have f1 : ((j + 1).factorial : ℚ) = ((j : ℚ) + 1) * (j.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : ((j + 2).factorial : ℚ) = ((j : ℚ) + 2) * (((j : ℚ) + 1) * (j.factorial : ℚ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  ext n
  cases n with
  | zero =>
    simp only [map_sub, add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_zero_X_mul, H, PowerSeries.coeff_mk, Nat.zero_add, mul_zero,
      add_zero, sub_zero]
    have hJ1 : ((j + 1).factorial : ℚ) ≠ 0 := by positivity
    rw [div_self hJ, div_self hJ1]
  | succ m =>
    simp only [map_sub, add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, H, PowerSeries.coeff_mk]
    have g1 : ((m + 1 + (j + 1)).factorial : ℚ)
        = ((m : ℚ) + (j : ℚ) + 2) * ((m + 1 + j).factorial : ℚ) := by
      rw [show m + 1 + (j + 1) = (m + 1 + j) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    have g2 : ((m + (j + 1)).factorial : ℚ) = ((m + 1 + j).factorial : ℚ) := by
      rw [show m + (j + 1) = m + 1 + j by omega]
    have g3 : ((m + (j + 2)).factorial : ℚ)
        = ((m : ℚ) + (j : ℚ) + 2) * ((m + 1 + j).factorial : ℚ) := by
      rw [show m + (j + 2) = (m + 1 + j) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    rw [g1, g2, g3, f1, f2]
    push_cast
    field_simp
    ring

lemma G_rel_zero :
    (1 : PowerSeries ℚ) = (1 + PowerSeries.C ((0 : ℕ) : ℚ) * PowerSeries.X) * H 0
      - PowerSeries.C ((0 + 1 : ℕ) : ℚ) * PowerSeries.X * H 1 := by
  have h := H_rel0
  have c0 : (PowerSeries.C ((0 : ℕ) : ℚ) : PowerSeries ℚ) = 0 := by simp
  have c1 : (PowerSeries.C ((0 + 1 : ℕ) : ℚ) : PowerSeries ℚ) = 1 := by simp
  rw [c0, c1]
  linear_combination -h

lemma G_rel (k : ℕ) :
    G k = (1 + PowerSeries.C (k : ℚ) * PowerSeries.X) * G (k + 1)
      - PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * G (k + 2) := by
  cases k with
  | zero => exact G_rel_zero
  | succ j => exact H_rel j

lemma G_inv (k : ℕ) : G k * (G k)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel (G k) (by rw [G_const]; exact one_ne_zero)

lemma Q_const (k : ℕ) : PowerSeries.constantCoeff (Q k) = 1 := by
  rw [Q, map_mul, PowerSeries.constantCoeff_inv, G_const, G_const]
  norm_num

lemma Q_inv (k : ℕ) : (Q k)⁻¹ = G (k + 1) * (G k)⁻¹ := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by rw [Q_const]; exact one_ne_zero), Q]
  have h1 := G_inv k
  have h2 := G_inv (k + 1)
  linear_combination (G (k + 1) * (G (k + 1))⁻¹) * h1 + h2

lemma Q_rec (k : ℕ) :
    Q k = 1 + PowerSeries.C (k : ℚ) * PowerSeries.X
      - PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * (Q (k + 1))⁻¹ := by
  rw [Q_inv, Q]
  have rel := G_rel k
  have h := G_inv (k + 1)
  linear_combination (G (k + 1))⁻¹ * rel + (1 + PowerSeries.C (k : ℚ) * PowerSeries.X) * h

lemma Q_zero : Q 0 = a167894Series := by
  show G 0 * (G 1)⁻¹ = factorialSeries⁻¹
  show (1 : PowerSeries ℚ) * (H 0)⁻¹ = factorialSeries⁻¹
  rw [one_mul, H_zero]

lemma cf_succ (k d : ℕ) :
    cfConv k (d + 1) = 1 + PowerSeries.C (k : ℚ) * PowerSeries.X
      - PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * (cfConv (k + 1) d)⁻¹ := by
  rw [cfConv]

lemma cf_const (k d : ℕ) : PowerSeries.constantCoeff (cfConv k d) = 1 := by
  cases d with
  | zero => rw [cfConv]; exact map_one _
  | succ d => rw [cf_succ]; simp

lemma agree (d : ℕ) : ∀ k : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ (d + 1) ∣ cfConv k d - Q k := by
  induction d with
  | zero =>
    intro k
    rw [zero_add, pow_one, PowerSeries.X_dvd_iff, map_sub, cf_const, Q_const, sub_self]
  | succ d ih =>
    intro k
    obtain ⟨c, hc⟩ := ih (k + 1)
    have hA := PowerSeries.mul_inv_cancel (cfConv (k + 1) d)
      (by rw [cf_const]; exact one_ne_zero)
    have hB := PowerSeries.mul_inv_cancel (Q (k + 1)) (by rw [Q_const]; exact one_ne_zero)
    have hQ := Q_rec k
    have key : (cfConv (k + 1) d)⁻¹ - (Q (k + 1))⁻¹
        = -((cfConv (k + 1) d)⁻¹ * (Q (k + 1))⁻¹ * (PowerSeries.X ^ (d + 1) * c)) := by
      rw [← hc]
      linear_combination (Q (k + 1))⁻¹ * hA - (cfConv (k + 1) d)⁻¹ * hB
    refine ⟨PowerSeries.C ((k + 1 : ℕ) : ℚ) * (cfConv (k + 1) d)⁻¹ * (Q (k + 1))⁻¹ * c, ?_⟩
    rw [cf_succ]
    linear_combination -hQ - (PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X) * key

end A167894Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a167894.main := by
  refine ⟨⟨A167894Proof.Q, A167894Proof.Q_zero, fun k => ⟨A167894Proof.Q_const k, A167894Proof.Q_rec k⟩⟩, ?_⟩
  intro d n hn
  have h := PowerSeries.X_pow_dvd_iff.mp (A167894Proof.agree d 0) n (by omega)
  rw [map_sub, sub_eq_zero] at h
  rw [h, A167894Proof.Q_zero]
