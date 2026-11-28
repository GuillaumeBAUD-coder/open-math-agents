import OMAStatements.S_oeis_a026765
import Mathlib

/-!
# Voznyy's generating function for the row sums of Kimberling's triangle A026758

Write d = n - 2k for the signed distance of the entry T(n,k) from the middle of row n.
In these coordinates the triangle counts walks on the integers with steps +1 and -1 of
length one and, at odd positive positions only, a stay of length two.

* The column series are found in closed form. With c = 1 + X^2 c^2 (Catalan series in X^2)
  and the pair A = 1 + X^2 A + X^2 A B, B = 1 + X^2 A B (excursions above an odd,
  respectively even, positive level), and E = 1 / (1 - X^2 A - X^2 c) (returns to the
  middle), the column at distance d is E (X c)^(-d) for d <= 0 and E times an alternating
  product of X A and X B for d > 0. These series satisfy the same recursion as the
  triangle, so their coefficients are the triangle entries (`tri`).
* Summing the recursion over a row gives r(n+2) = 2 r(n+1) + h(n), where h(n) is the mass
  on the positive side for odd n and zero for even n. Its series is the geometric sum
  H = E X A / (1 - X^2 A B), so G (1 - 2X) = 1 + X^2 H.
* Finally (1 - 2X)(1 + 2 X G) = 1 + 2 X^3 H, and the quadratic equations for c and A give
  (1 - 5 X^2)(1 + 2 X^3 H)^2 = (1 - 4 X^2)(1 - X^2) (`key_algebra`).
-/

namespace KimberlingA026765

open PowerSeries
open OMA.S_oeis_a026765

/-- The Catalan series over the rationals. -/
noncomputable def cat : PowerSeries ℚ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

theorem cat_eq : cat = 1 + X * cat ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h
  unfold cat
  linear_combination -h

/-- A solution of `g = 1 + w g ^ 2` for every series `w` without constant term. -/
theorem exists_quad (w : PowerSeries ℚ) (hw : constantCoeff w = 0) :
    ∃ g : PowerSeries ℚ, g = 1 + w * g ^ 2 := by
  have ha : HasSubst w := HasSubst.of_constantCoeff_zero' hw
  have h := congrArg (PowerSeries.subst w) cat_eq
  have h1 : (1 : PowerSeries ℚ).subst w = 1 := by
    rw [← coe_substAlgHom ha, map_one]
  rw [subst_add ha, subst_mul ha, subst_pow ha, subst_X ha, h1] at h
  exact ⟨_, h⟩

/-- The algebraic series used to describe the columns of the triangle. -/
theorem exists_series : ∃ c A B E D : PowerSeries ℚ,
    c = 1 + X ^ 2 * c ^ 2 ∧ A = 1 + X ^ 2 * A + X ^ 2 * A * B ∧ B = 1 + X ^ 2 * A * B ∧
    B = (1 - X ^ 2) * A ∧ E * (1 - X ^ 2 * A - X ^ 2 * c) = 1 ∧
    D * (1 - X ^ 2 * A * B) = 1 := by
  obtain ⟨c, hc⟩ := exists_quad (X ^ 2) (by simp)
  set I : PowerSeries ℚ := (1 - X ^ 2)⁻¹ with hI
  have hI1 : (1 - X ^ 2) * I = 1 := PowerSeries.mul_inv_cancel _ (by simp)
  obtain ⟨a, ha⟩ := exists_quad (X ^ 2 * I) (by simp)
  have hc0 : constantCoeff c = 1 := by
    have := congrArg constantCoeff hc
    simpa using this
  have ha0 : constantCoeff a = 1 := by
    have := congrArg constantCoeff ha
    simpa using this
  have hI0 : constantCoeff I = 1 := by
    have := congrArg constantCoeff hI1
    simpa using this
  refine ⟨c, a * I, a, (1 - X ^ 2 * (a * I) - X ^ 2 * c)⁻¹, (1 - X ^ 2 * (a * I) * a)⁻¹,
    hc, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination ha + a * hI1
  · linear_combination ha
  · linear_combination (-a) * hI1
  · exact PowerSeries.inv_mul_cancel _ (by simp)
  · exact PowerSeries.inv_mul_cancel _ (by simp)

/-- The algebraic identity behind the generating function. -/
theorem key_algebra (c A B E D : PowerSeries ℚ)
    (hc : c = 1 + X ^ 2 * c ^ 2) (hB : B = 1 + X ^ 2 * A * B)
    (hBA : B = (1 - X ^ 2) * A) (hE : E * (1 - X ^ 2 * A - X ^ 2 * c) = 1)
    (hD : D * (1 - X ^ 2 * A * B) = 1) :
    (1 - 5 * X ^ 2) * (1 + 2 * X ^ 3 * (E * X * A * D)) ^ 2 =
      (1 - 4 * X ^ 2) * (1 - X ^ 2) := by
  set q : PowerSeries ℚ := X ^ 2 with hq
  set s1 : PowerSeries ℚ := 1 - 2 * q * c with hs1d
  set s2 : PowerSeries ℚ := (1 - q) * (1 - 2 * q * A) with hs2d
  set W : PowerSeries ℚ := 1 + 2 * X ^ 3 * (E * X * A * D) with hWd
  have hR2 : (1 - q) * A = 1 + q * (1 - q) * A ^ 2 := by
    linear_combination hB - (1 - q * A) * hBA
  have hs1 : s1 ^ 2 = 1 - 4 * q := by linear_combination (-4 * q) * hc
  have hs2 : s2 ^ 2 = (1 - q) * (1 - 5 * q) := by
    linear_combination (-4 * q * (1 - q)) * hR2
  have hL1 : E * (s1 * (1 - q) + s2) = 2 * (1 - q) := by
    linear_combination 2 * (1 - q) * hE
  have hL2 : A * D * s2 = 1 := by
    linear_combination hD + D * hB - D * (1 - 2 * q * A) * hBA
  have hWs : W * s2 = s2 + 2 * q ^ 2 * E := by
    linear_combination 2 * q ^ 2 * E * hL2
  have hne : (2 * (1 - q) : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [hq, map_ofNat] at this
  have hne1 : ((1 - q) : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [hq] at this
  have hK : (2 * (1 - q)) * (s2 + 2 * q ^ 2 * E) = (2 * (1 - q)) * (s1 * (1 - q)) := by
    linear_combination E * hs2 - E * (1 - q) ^ 2 * hs1 - (s2 - s1 * (1 - q)) * hL1
  have hK' : W * s2 = s1 * (1 - q) := by
    rw [hWs]; exact mul_left_cancel₀ hne hK
  apply mul_left_cancel₀ hne1
  calc (1 - q) * ((1 - 5 * q) * W ^ 2) = (W * s2) ^ 2 := by
        linear_combination (-(W ^ 2)) * hs2
    _ = (s1 * (1 - q)) ^ 2 := by rw [hK']
    _ = (1 - q) * ((1 - 4 * q) * (1 - q)) := by linear_combination (1 - q) ^ 2 * hs1

/-- Path weights on the nonnegative side: alternate the factors `X * A` and `X * B`. -/
noncomputable def rho (A B : PowerSeries ℚ) : ℕ → PowerSeries ℚ
  | 0 => 1
  | j + 1 => rho A B j * X * (if j % 2 = 0 then A else B)

theorem rho_rec (A B : PowerSeries ℚ) (hA : A = 1 + X ^ 2 * A + X ^ 2 * A * B)
    (hB : B = 1 + X ^ 2 * A * B) (i : ℕ) :
    rho A B (i + 1) = X * (rho A B i + rho A B (i + 2)) +
      (if (i + 1) % 2 = 1 then X ^ 2 * rho A B (i + 1) else 0) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have h1 : (i + 1) % 2 = 1 := by omega
    simp only [rho, h, h1, if_true]
    simp only [show ¬ ((1 : ℕ) = 0) by decide, if_false]
    linear_combination (rho A B i * X) * hA
  · have h1 : (i + 1) % 2 = 0 := by omega
    simp only [rho, h, h1, if_true]
    simp only [show ¬ ((1 : ℕ) = 0) by decide, show ¬ ((0 : ℕ) = 1) by decide, if_false]
    linear_combination (rho A B i * X) * hB

theorem rho_odd (A B : PowerSeries ℚ) (m : ℕ) :
    rho A B (2 * m + 1) = (X ^ 2 * A * B) ^ m * (X * A) := by
  induction m with
  | zero => simp [rho]
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
    have h1 : (2 * m + 1 + 1) % 2 = 0 := by omega
    have h2 : ¬ ((2 * m + 1) % 2 = 0) := by omega
    rw [e, rho, rho, if_pos h1, if_neg h2, ih]
    ring

/-- The generating series of the column at signed distance `d` from the middle. -/
noncomputable def Phi (c A B E : PowerSeries ℚ) (d : ℤ) : PowerSeries ℚ :=
  if 0 ≤ d then E * rho A B d.toNat else E * (X * c) ^ (-d).toNat

theorem Phi_nat (c A B E : PowerSeries ℚ) (j : ℕ) : Phi c A B E (j : ℤ) = E * rho A B j := by
  simp [Phi]

theorem Phi_neg (c A B E : PowerSeries ℚ) (e : ℕ) :
    Phi c A B E (-(e : ℤ)) = E * (X * c) ^ e := by
  cases e with
  | zero => simp [Phi, rho]
  | succ e =>
    have h : ¬ ((0 : ℤ) ≤ -((e + 1 : ℕ) : ℤ)) := by omega
    simp only [Phi, if_neg h, neg_neg, Int.toNat_natCast]

theorem Phi_rec (c A B E : PowerSeries ℚ)
    (hc : c = 1 + X ^ 2 * c ^ 2) (hA : A = 1 + X ^ 2 * A + X ^ 2 * A * B)
    (hB : B = 1 + X ^ 2 * A * B) (hE : E * (1 - X ^ 2 * A - X ^ 2 * c) = 1) (d : ℤ) :
    Phi c A B E d = (if d = 0 then 1 else 0) + X * (Phi c A B E (d - 1) + Phi c A B E (d + 1)) +
      (if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * Phi c A B E d else 0) := by
  obtain ⟨m, rfl | rfl⟩ := d.eq_nat_or_neg
  · cases m with
    | zero =>
      have e1 : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
      have e2 : ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) := by norm_num
      rw [e1, e2, Phi_nat, Phi_nat, Phi_neg]
      simp [rho]
      linear_combination hE
    | succ i =>
      have e1 : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by push_cast; ring
      have e2 : ((i + 1 : ℕ) : ℤ) + 1 = ((i + 2 : ℕ) : ℤ) := by push_cast; ring
      have e0 : ¬ (((i + 1 : ℕ) : ℤ) = 0) := by omega
      have hr := rho_rec A B hA hB i
      rw [e1, e2, Phi_nat, Phi_nat, Phi_nat, if_neg e0]
      by_cases h : (i + 1) % 2 = 1
      · have h' : ((i + 1 : ℕ) : ℤ) % 2 = 1 ∧ 1 ≤ ((i + 1 : ℕ) : ℤ) := by omega
        rw [if_pos h] at hr
        rw [if_pos h']
        linear_combination E * hr
      · have h' : ¬ (((i + 1 : ℕ) : ℤ) % 2 = 1 ∧ 1 ≤ ((i + 1 : ℕ) : ℤ)) := by omega
        rw [if_neg h] at hr
        rw [if_neg h']
        linear_combination E * hr
  · cases m with
    | zero =>
      have e1 : -((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
      have e2 : -((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) := by norm_num
      have e3 : -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by norm_num
      rw [e1, e2, e3, Phi_nat, Phi_nat, Phi_neg]
      simp [rho]
      linear_combination hE
    | succ e =>
      have e1 : -((e + 1 : ℕ) : ℤ) - 1 = -((e + 2 : ℕ) : ℤ) := by push_cast; ring
      have e2 : -((e + 1 : ℕ) : ℤ) + 1 = -((e : ℕ) : ℤ) := by push_cast; ring
      have e0 : ¬ (-((e + 1 : ℕ) : ℤ) = 0) := by omega
      have h' : ¬ ((-((e + 1 : ℕ) : ℤ)) % 2 = 1 ∧ 1 ≤ -((e + 1 : ℕ) : ℤ)) := by omega
      rw [e1, e2, Phi_neg, Phi_neg, Phi_neg, if_neg e0, if_neg h']
      linear_combination (E * (X * c) ^ e * X) * hc

section Columns

variable (F : ℤ → PowerSeries ℚ)

theorem co0
    (hF : ∀ d, F d = (if d = 0 then 1 else 0) + X * (F (d - 1) + F (d + 1)) +
      (if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * F d else 0)) (d : ℤ) :
    coeff 0 (F d) = if d = 0 then 1 else 0 := by
  have h := congrArg (coeff 0) (hF d)
  rw [h]
  split_ifs <;> simp

theorem co1
    (hF : ∀ d, F d = (if d = 0 then 1 else 0) + X * (F (d - 1) + F (d + 1)) +
      (if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * F d else 0)) (d : ℤ) :
    coeff 1 (F d) = (if d = 1 then 1 else 0) + (if d = -1 then 1 else 0) := by
  have h := congrArg (coeff 1) (hF d)
  have hX : ∀ p : PowerSeries ℚ, coeff 1 (X * p) = coeff 0 p := fun p => coeff_succ_X_mul 0 p
  have hX2 : ∀ p : PowerSeries ℚ, coeff 1 (X ^ 2 * p) = 0 := fun p => by
    rw [coeff_X_pow_mul']; simp
  have hi : coeff 1 ((if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * F d else 0) : PowerSeries ℚ) = 0 := by
    split_ifs
    · exact hX2 _
    · simp
  have hj : coeff 1 ((if d = 0 then 1 else 0) : PowerSeries ℚ) = 0 := by
    split_ifs <;> simp [coeff_one]
  have e1 : d - 1 = 0 ↔ d = 1 := by omega
  have e2 : d + 1 = 0 ↔ d = -1 := by omega
  rw [h, map_add, map_add, hX, map_add, co0 F hF, co0 F hF, hi, hj]
  simp only [e1, e2]
  ring

theorem co2
    (hF : ∀ d, F d = (if d = 0 then 1 else 0) + X * (F (d - 1) + F (d + 1)) +
      (if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * F d else 0)) (n : ℕ) (d : ℤ) :
    coeff (n + 2) (F d) = coeff (n + 1) (F (d - 1)) + coeff (n + 1) (F (d + 1)) +
      (if d % 2 = 1 ∧ 1 ≤ d then coeff n (F d) else 0) := by
  have h := congrArg (coeff (n + 2)) (hF d)
  have hX : ∀ p : PowerSeries ℚ, coeff (n + 2) (X * p) = coeff (n + 1) p :=
    fun p => coeff_succ_X_mul (n + 1) p
  have hX2 : ∀ p : PowerSeries ℚ, coeff (n + 2) (X ^ 2 * p) = coeff n p := fun p => by
    rw [coeff_X_pow_mul']; simp
  have hi : coeff (n + 2) ((if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * F d else 0) : PowerSeries ℚ) =
      if d % 2 = 1 ∧ 1 ≤ d then coeff n (F d) else 0 := by
    split_ifs
    · exact hX2 _
    · simp
  have hj : coeff (n + 2) ((if d = 0 then 1 else 0) : PowerSeries ℚ) = 0 := by
    split_ifs <;> simp [coeff_one]
  rw [h, map_add, map_add, hX, map_add, hi, hj]
  ring

theorem tri
    (hF : ∀ d, F d = (if d = 0 then 1 else 0) + X * (F (d - 1) + F (d + 1)) +
      (if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * F d else 0)) (n : ℕ) :
    ∀ k : ℤ, ((triangle n k : ℕ) : ℚ) = coeff n (F ((n : ℤ) - 2 * k)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    intro k
    rw [co0 F hF]
    by_cases hk : k = 0
    · subst hk; simp [triangle]
    · have h : ¬ (((0 : ℕ) : ℤ) - 2 * k = 0) := by omega
      rw [if_neg h]
      simp [triangle, hk]
  | one =>
    intro k
    rw [co1 F hF]
    by_cases hk : k = 0
    · subst hk; simp [triangle]
    · by_cases hk1 : k = 1
      · subst hk1; simp [triangle]
      · have h1 : ¬ (((1 : ℕ) : ℤ) - 2 * k = 1) := by omega
        have h2 : ¬ (((1 : ℕ) : ℤ) - 2 * k = -1) := by omega
        rw [if_neg h1, if_neg h2]
        simp [triangle, hk, hk1]
  | more n ih0 ih1 =>
    intro k
    have e1 : ((n + 2 : ℕ) : ℤ) - 2 * k - 1 = ((n + 1 : ℕ) : ℤ) - 2 * k := by push_cast; ring
    have e2 : ((n + 2 : ℕ) : ℤ) - 2 * k + 1 = ((n + 1 : ℕ) : ℤ) - 2 * (k - 1) := by
      push_cast; ring
    have e3 : ((n + 2 : ℕ) : ℤ) - 2 * k = (n : ℤ) - 2 * (k - 1) := by push_cast; ring
    rw [co2 F hF, e1, e2, ← ih1 k, ← ih1 (k - 1)]
    simp only [triangle]
    by_cases h : n % 2 = 1 ∧ 2 * k ≤ ((n + 1 : ℕ) : ℤ)
    · have h' : (((n + 2 : ℕ) : ℤ) - 2 * k) % 2 = 1 ∧ 1 ≤ ((n + 2 : ℕ) : ℤ) - 2 * k := by omega
      rw [if_pos h, if_pos h', e3, ← ih0 (k - 1)]
      push_cast; ring
    · have h' : ¬ ((((n + 2 : ℕ) : ℤ) - 2 * k) % 2 = 1 ∧ 1 ≤ ((n + 2 : ℕ) : ℤ) - 2 * k) := by
        omega
      rw [if_neg h, if_neg h']
      push_cast; ring

theorem par
    (hF : ∀ d, F d = (if d = 0 then 1 else 0) + X * (F (d - 1) + F (d + 1)) +
      (if d % 2 = 1 ∧ 1 ≤ d then X ^ 2 * F d else 0)) (n : ℕ) :
    ∀ d : ℤ, ((n : ℤ) - d) % 2 = 1 → coeff n (F d) = 0 := by
  induction n using Nat.twoStepInduction with
  | zero =>
    intro d hd
    rw [co0 F hF, if_neg (by omega)]
  | one =>
    intro d hd
    rw [co1 F hF, if_neg (by omega), if_neg (by omega), add_zero]
  | more n ih0 ih1 =>
    intro d hd
    rw [co2 F hF, ih1 (d - 1) (by omega), ih1 (d + 1) (by omega)]
    split_ifs
    · rw [ih0 d (by omega)]; ring
    · ring

end Columns

theorem prefixSum_eq (f : ℕ → ℕ) (m : ℕ) : prefixSum f m = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp [prefixSum]
  | succ m ih => rw [prefixSum, ih, Finset.sum_range_succ]

theorem supp (n : ℕ) : ∀ k : ℤ, (k < 0 ∨ (n : ℤ) < k) → triangle n k = 0 := by
  induction n using Nat.twoStepInduction with
  | zero =>
    intro k hk
    have : ¬ (k = 0) := by omega
    simp [triangle, this]
  | one =>
    intro k hk
    have : ¬ (k = 0 ∨ k = 1) := by omega
    simp [triangle, this]
  | more n ih0 ih1 =>
    intro k hk
    simp only [triangle]
    rw [ih1 (k - 1) (by omega), ih1 k (by omega)]
    split_ifs
    · rw [ih0 (k - 1) (by omega)]
    · rfl

theorem rowSum_succ_succ (n : ℕ) :
    rowSum (n + 2) = 2 * rowSum (n + 1) + ∑ k ∈ Finset.range (n + 3),
      (if n % 2 = 1 ∧ 2 * (k : ℤ) ≤ ((n + 1 : ℕ) : ℤ) then triangle n ((k : ℤ) - 1) else 0) := by
  have h1 : ∑ k ∈ Finset.range (n + 3), triangle (n + 1) ((k : ℤ) - 1) =
      ∑ k ∈ Finset.range (n + 2), triangle (n + 1) (k : ℤ) := by
    rw [Finset.sum_range_succ']
    have h0 : triangle (n + 1) (((0 : ℕ) : ℤ) - 1) = 0 := supp _ _ (by omega)
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    push_cast; ring
  have h2 : ∑ k ∈ Finset.range (n + 3), triangle (n + 1) (k : ℤ) =
      ∑ k ∈ Finset.range (n + 2), triangle (n + 1) (k : ℤ) := by
    rw [Finset.sum_range_succ, supp (n + 1) _ (by omega), add_zero]
  unfold rowSum
  rw [prefixSum_eq, prefixSum_eq]
  simp only [triangle]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]
  ring

theorem Hs_coeff (c A B E D : PowerSeries ℚ) (hD : D * (1 - X ^ 2 * A * B) = 1) (n M : ℕ)
    (hM : n < 2 * M + 1) :
    coeff n (E * X * A * D) =
      ∑ m ∈ Finset.range M, coeff n (Phi c A B E ((2 * m + 1 : ℕ) : ℤ)) := by
  have hg : (1 - X ^ 2 * A * B) * ∑ m ∈ Finset.range M, (X ^ 2 * A * B) ^ m =
      1 - (X ^ 2 * A * B) ^ M := mul_neg_geom_sum _ M
  have hsum : ∑ m ∈ Finset.range M, Phi c A B E ((2 * m + 1 : ℕ) : ℤ) =
      E * X * A * ∑ m ∈ Finset.range M, (X ^ 2 * A * B) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Phi_nat, rho_odd]
    ring
  have hsplit : E * X * A * D = ∑ m ∈ Finset.range M, Phi c A B E ((2 * m + 1 : ℕ) : ℤ) +
      X ^ (2 * M + 1) * (E * A * (A * B) ^ M * D) := by
    rw [hsum]
    linear_combination (E * X * A * ∑ m ∈ Finset.range M, (X ^ 2 * A * B) ^ m) * hD -
      (E * X * A * D) * hg
  rw [hsplit, map_add, map_sum, coeff_X_pow_mul', if_neg (by omega), add_zero]

end KimberlingA026765

open PowerSeries OMA.S_oeis_a026765 KimberlingA026765 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026765.main := by
  obtain ⟨c, A, B, E, D, hc, hA, hB, hBA, hE, hD⟩ := exists_series
  have hF := Phi_rec c A B E hc hA hB hE
  have hG : rowGF * (1 - 2 * X) = 1 + X ^ 2 * (E * X * A * D) := by
    rw [show rowGF * (1 - 2 * X) = rowGF - (rowGF * X + rowGF * X) by ring]
    ext n
    rcases n with _ | _ | n
    · simp [rowGF, rowSum, prefixSum, triangle]
    · have h1 : coeff 1 (rowGF * X) = coeff 0 rowGF := coeff_succ_mul_X 0 rowGF
      have h2 : coeff 1 (X ^ 2 * (E * X * A * D)) = 0 := by rw [coeff_X_pow_mul']; simp
      rw [map_sub, map_add, map_add, h1, h2]
      simp [rowGF, rowSum, prefixSum, triangle, coeff_one]
    · have h1 : coeff (n + 2) (rowGF * X) = coeff (n + 1) rowGF := coeff_succ_mul_X (n + 1) rowGF
      have h2 : coeff (n + 2) (X ^ 2 * (E * X * A * D)) = coeff n (E * X * A * D) := by
        rw [coeff_X_pow_mul']; simp
      have h3 : coeff (n + 2) (1 : PowerSeries ℚ) = 0 := by simp [coeff_one]
      rw [map_sub, map_add, map_add, h1, h2, h3, zero_add]
      simp only [rowGF, coeff_mk]
      rw [rowSum_succ_succ n]
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
      · have hz : ∑ k ∈ Finset.range (2 * t + 3),
            (if (2 * t) % 2 = 1 ∧ 2 * (k : ℤ) ≤ ((2 * t + 1 : ℕ) : ℤ) then
              triangle (2 * t) ((k : ℤ) - 1) else 0) = 0 :=
          Finset.sum_eq_zero (fun k _ => if_neg (by omega))
        have he : coeff (2 * t) (E * X * A * D) = 0 := by
          rw [Hs_coeff c A B E D hD (2 * t) (t + 1) (by omega)]
          exact Finset.sum_eq_zero (fun m _ => par _ hF _ _ (by omega))
        rw [hz, he]
        push_cast; ring
      · have hz : ∑ k ∈ Finset.range (2 * t + 1 + 3),
            (if (2 * t + 1) % 2 = 1 ∧ 2 * (k : ℤ) ≤ ((2 * t + 1 + 1 : ℕ) : ℤ) then
              triangle (2 * t + 1) ((k : ℤ) - 1) else 0) =
            ∑ k ∈ Finset.range (t + 2), triangle (2 * t + 1) ((k : ℤ) - 1) := by
          have hsub : Finset.range (t + 2) ⊆ Finset.range (2 * t + 1 + 3) := by
            intro k hk
            simp only [Finset.mem_range] at hk ⊢
            omega
          rw [← Finset.sum_subset hsub (fun k _ hk => if_neg (by
            simp only [Finset.mem_range] at hk; omega))]
          exact Finset.sum_congr rfl (fun k hk => if_pos (by
            simp only [Finset.mem_range] at hk; omega))
        have ho : coeff (2 * t + 1) (E * X * A * D) =
            ∑ k ∈ Finset.range (t + 2), ((triangle (2 * t + 1) ((k : ℤ) - 1) : ℕ) : ℚ) := by
          rw [Hs_coeff c A B E D hD (2 * t + 1) (t + 2) (by omega), ← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          simp only [Finset.mem_range] at hk
          rw [tri _ hF]
          congr 2
          omega
        rw [hz, ho]
        push_cast; ring
  have hW := key_algebra c A B E D hc hB hBA hE hD
  have h12 : (1 - 2 * X : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have hY : (1 - 2 * X) * (1 + 2 * X * rowGF) = 1 + 2 * X ^ 3 * (E * X * A * D) := by
    linear_combination 2 * X * hG
  apply mul_left_cancel₀ h12
  calc (1 - 2 * X) * ((1 - 2 * X) * (1 - 5 * X ^ 2) * (1 + 2 * X * rowGF) ^ 2)
      = (1 - 5 * X ^ 2) * ((1 - 2 * X) * (1 + 2 * X * rowGF)) ^ 2 := by ring
    _ = (1 - 5 * X ^ 2) * (1 + 2 * X ^ 3 * (E * X * A * D)) ^ 2 := by rw [hY]
    _ = (1 - 4 * X ^ 2) * (1 - X ^ 2) := hW
    _ = (1 - 2 * X) * ((1 + 2 * X) * (1 - X ^ 2)) := by ring
