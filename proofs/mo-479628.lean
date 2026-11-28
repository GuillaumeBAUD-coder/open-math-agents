import OMAStatements.S_mo_479628

private theorem rescale_C {R : Type*} [CommSemiring R] (a r : R) :
    PowerSeries.rescale a (PowerSeries.C r) = PowerSeries.C r := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst h
    simp
  · simp

private theorem rescale_X' {R : Type*} [CommSemiring R] (a : R) :
    PowerSeries.rescale a (PowerSeries.X : PowerSeries R) = PowerSeries.C a * PowerSeries.X := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  split_ifs with h
  · subst h
    simp
  · simp

private noncomputable def H (G : PowerSeries (Polynomial ℕ)) : ℕ → PowerSeries (Polynomial ℕ)
  | 0 => 1 + PowerSeries.X * G
  | 1 => G
  | c + 2 => G * PowerSeries.rescale (Polynomial.X ^ 2) (H G c)

private theorem coeff_zero_G (G : PowerSeries (Polynomial ℕ))
    (hG : G = 1 + PowerSeries.X * G + PowerSeries.C (Polynomial.X : Polynomial ℕ) *
      PowerSeries.X * PowerSeries.rescale (Polynomial.X ^ 2) G * G) :
    PowerSeries.coeff 0 G = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  conv_lhs => rw [hG]
  simp [PowerSeries.constantCoeff_X]

private theorem coeff_zero_H (G : PowerSeries (Polynomial ℕ))
    (hG0 : PowerSeries.coeff 0 G = 1) :
    ∀ c : ℕ, PowerSeries.coeff 0 (H G c) = 1
  | 0 => by
    rw [H, PowerSeries.coeff_zero_eq_constantCoeff]
    simp [PowerSeries.constantCoeff_X]
  | 1 => hG0
  | c + 2 => by
    have ih := coeff_zero_H G hG0 c
    rw [H, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      pow_zero, one_mul, hG0, ih, one_mul]

private theorem H_rec (G : PowerSeries (Polynomial ℕ))
    (hG : G = 1 + PowerSeries.X * G + PowerSeries.C (Polynomial.X : Polynomial ℕ) *
      PowerSeries.X * PowerSeries.rescale (Polynomial.X ^ 2) G * G) :
    ∀ c : ℕ, 1 ≤ c →
      H G c = H G (c - 1) +
        PowerSeries.C ((Polynomial.X : Polynomial ℕ) ^ c) * PowerSeries.X *
          H G (c + 1 + c % 2)
  | 0, hc => by omega
  | 1, _ => by
    have h13 : 1 + 1 + 1 % 2 = 3 := rfl
    rw [h13]
    simp only [Nat.sub_self, H, pow_one]
    conv_lhs => rw [hG]
    ring
  | 2, _ => by
    have h23 : 2 + 1 + 2 % 2 = 3 := rfl
    rw [h23]
    simp only [Nat.add_one_sub_one, H]
    rw [map_add, map_one, map_mul, rescale_X', mul_add, mul_one]
    ring
  | k + 3, _ => by
    have ih := H_rec G hG (k + 1) (by omega)
    have hk1 : k + 1 - 1 = k := Nat.add_sub_cancel k 1
    have hk2 : k + 1 + 1 + (k + 1) % 2 = k + 2 + (k + 1) % 2 := by omega
    rw [hk1, hk2] at ih
    have hidx1 : (k + 3) - 1 = k + 2 := rfl
    have hidx2 : k + 3 + 1 + (k + 3) % 2 = (k + 2 + (k + 1) % 2) + 2 := by omega
    rw [hidx1, hidx2]
    simp only [H]
    conv_lhs => rw [ih]
    rw [map_add, map_mul, map_mul, rescale_C, rescale_X', mul_add]
    have hpow : (Polynomial.X : Polynomial ℕ) ^ (k + 3) =
        (Polynomial.X : Polynomial ℕ) ^ (k + 1) * (Polynomial.X : Polynomial ℕ) ^ 2 := by
      ring
    rw [hpow, map_mul]
    ring

private theorem P_add_eq_coeff_H (G : PowerSeries (Polynomial ℕ))
    (hG : G = 1 + PowerSeries.X * G + PowerSeries.C (Polynomial.X : Polynomial ℕ) *
      PowerSeries.X * PowerSeries.rescale (Polynomial.X ^ 2) G * G) :
    ∀ k c : ℕ, OMA.S_mo_479628.P (c + k) k = PowerSeries.coeff k (H G c) := by
  intro k
  induction k with
  | zero =>
    intro c
    rw [add_zero, OMA.S_mo_479628.P]
    exact (coeff_zero_H G (coeff_zero_G G hG) c).symm
  | succ k ih =>
    intro c
    induction c with
    | zero =>
      rw [zero_add, OMA.S_mo_479628.P, if_neg (Nat.lt_irrefl _)]
      have h0 : OMA.S_mo_479628.P k (k + 1) = 0 := by
        rw [OMA.S_mo_479628.P, if_pos (Nat.lt_succ_self k)]
      have hsub : k + 1 - (k + 1) = 0 := Nat.sub_self _
      rw [Nat.add_sub_cancel k 1, h0, zero_add, hsub, pow_zero, one_mul, Nat.zero_mod, add_zero]
      have h1 := ih 1
      rw [add_comm 1 k] at h1
      rw [h1, H, H, map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k), zero_add,
        PowerSeries.coeff_succ_X_mul]
    | succ c' ihc' =>
      have hlt : ¬ (c' + 1 + (k + 1) < k + 1) := by omega
      have hsub1 : c' + 1 + (k + 1) - 1 = c' + (k + 1) := by omega
      have hsub2 : c' + 1 + (k + 1) - (k + 1) = c' + 1 := by omega
      have hadd : c' + 1 + (k + 1) + (c' + 1) % 2 = (c' + 1 + 1 + (c' + 1) % 2) + k := by omega
      rw [OMA.S_mo_479628.P, if_neg hlt, hsub1, hsub2, hadd, ihc', ih (c' + 1 + 1 + (c' + 1) % 2)]
      have hrec := H_rec G hG (c' + 1) (by omega)
      conv_rhs => rw [hrec]
      simp only [Nat.add_one_sub_one, map_add, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]

theorem OMA.solution : type_of% @OMA.S_mo_479628.main := by
  intro G hG n
  have h := P_add_eq_coeff_H G hG (n + 1) 0
  rw [zero_add, H, map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n),
    zero_add, PowerSeries.coeff_succ_X_mul] at h
  exact h
