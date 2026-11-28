import OMAStatements.S_mo_475505

open PowerSeries OMA.S_mo_475505

namespace OMA.P_mo_475505

private lemma constantCoeff_primitive (f : PS) : constantCoeff (primitive f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, primitive, coeff_mk]

private lemma derivative_primitive (f : PS) : derivative ℚ (primitive f) = f := by
  ext n
  rw [coeff_derivative, primitive, coeff_mk]
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp

private lemma derivative_intCast (m : ℤ) : derivative ℚ (m : PS) = 0 := by
  have h : (m : PS) = C (R := ℚ) (m : ℚ) := (map_intCast (C (R := ℚ)) m).symm
  rw [h, derivative_C]

private lemma constantCoeff_intCast (m : ℤ) : constantCoeff (m : PS) = (m : ℚ) := by
  have h : (m : PS) = C (R := ℚ) (m : ℚ) := (map_intCast (C (R := ℚ)) m).symm
  rw [h, constantCoeff_C]

private lemma derivative_zpow (u : PSˣ) (a : ℤ) :
    derivative ℚ (↑(u ^ a) : PS) = (a : PS) * (↑(u ^ (a - 1)) : PS) * derivative ℚ (↑u : PS) := by
  cases a with
  | ofNat n =>
    cases n with
    | zero =>
      simp only [Int.ofNat_eq_natCast, Nat.cast_zero, zpow_zero, Units.val_one, derivative_one,
        Int.cast_zero, zero_mul]
    | succ k =>
      have h1 : (↑(u ^ (Int.ofNat (k + 1))) : PS) = (↑u : PS) ^ (k + 1) := by
        rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
      have h2 : (↑(u ^ (Int.ofNat (k + 1) - 1)) : PS) = (↑u : PS) ^ k := by
        have hk : (Int.ofNat (k + 1) - 1 : ℤ) = (k : ℤ) := by
          rw [Int.ofNat_eq_natCast]; omega
        rw [hk, zpow_natCast, Units.val_pow_eq_pow_val]
      rw [h1, h2, derivative_pow]
      simp only [Nat.add_sub_cancel, Int.ofNat_eq_natCast, Int.cast_natCast]
  | negSucc k =>
    have h1 : (↑(u ^ (Int.negSucc k)) : PS) = (↑(u⁻¹) : PS) ^ (k + 1) := by
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have h2 : (↑(u ^ (Int.negSucc k - 1)) : PS) = (↑(u⁻¹) : PS) ^ (k + 2) := by
      have hk : (Int.negSucc k - 1 : ℤ) = Int.negSucc (k + 1) := by omega
      rw [hk, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [h1, h2, derivative_pow, derivative_inv]
    simp only [Nat.add_sub_cancel, Int.cast_negSucc]
    ring

private lemma constantCoeff_zpow_eq_one (u : PSˣ) (hu : constantCoeff (↑u : PS) = 1) (a : ℤ) :
    constantCoeff (↑(u ^ a) : PS) = 1 := by
  have huinv : constantCoeff (↑(u⁻¹) : PS) = 1 := by
    have h1 : constantCoeff ((↑u : PS) * (↑(u⁻¹) : PS)) = 1 := by
      rw [Units.mul_inv, map_one]
    rw [map_mul, hu, one_mul] at h1
    exact h1
  cases a with
  | ofNat n =>
    simp [zpow_natCast, hu]
  | negSucc k =>
    rw [zpow_negSucc]
    have hpow : (↑((u ^ (k + 1))⁻¹) : PS) = (↑(u⁻¹) : PS) ^ (k + 1) := by
      rw [← inv_pow, Units.val_pow_eq_pow_val]
    rw [hpow, map_pow, huinv, one_pow]

private lemma row_eq_zero_of_lt (p q s : ℤ) : ∀ n k : ℕ, n < k → row p q s n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    simp [row, Nat.ne_of_gt hk]
  | succ m ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ j =>
      simp only [row]
      rw [ih (j + 1) (by omega), ih j (by omega)]
      ring

private lemma iterate_derivative_mul (U V : PSˣ) (p q s : ℤ)
    (hDU : derivative ℚ (↑U : PS) = (↑U : PS) * (↑V : PS))
    (hDV : derivative ℚ (↑V : PS) = (p : PS) * (↑(U ^ q) : PS) * (↑(V ^ s) : PS)) :
    ∀ n : ℕ,
      (derivative ℚ)^[n] ((↑U : PS) * (↑V : PS)) =
        ∑ k ∈ Finset.range (n + 1),
          (row p q s n k : PS) * (↑(U ^ (1 + q * (k : ℤ))) : PS) *
            (↑(V ^ ((n : ℤ) + 1 + (s - 2) * (k : ℤ))) : PS) := by
  intro n
  induction n with
  | zero =>
    simp [row]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    set T : ℕ → ℕ → PS := fun r k =>
      (↑(U ^ (1 + q * (k : ℤ))) : PS) * (↑(V ^ ((r : ℤ) + 1 + (s - 2) * (k : ℤ))) : PS)
    have hterm : ∀ k : ℕ,
        derivative ℚ ((row p q s m k : PS) * T m k) =
          (row p q s m k : PS) * ((1 + q * (k : ℤ) : ℤ) : PS) * T (m + 1) k +
          (row p q s m k : PS) * (p : PS) * (((m : ℤ) + 1 + (s - 2) * (k : ℤ) : ℤ) : PS) *
            T (m + 1) (k + 1) := by
      intro k
      set a : ℤ := 1 + q * (k : ℤ)
      set b : ℤ := (m : ℤ) + 1 + (s - 2) * (k : ℤ)
      have hDT : derivative ℚ (T m k) =
          (a : PS) * T (m + 1) k + (p : PS) * (b : PS) * T (m + 1) (k + 1) := by
        dsimp only [T]
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_zpow, derivative_zpow,
          hDU, hDV]
        have hU1 : (↑(U ^ (a - 1)) : PS) * (↑U : PS) = (↑(U ^ a) : PS) := by
          rw [← Units.val_mul, ← zpow_add_one]; congr 2; omega
        have hV1 : (↑V : PS) * (↑(V ^ b) : PS) = (↑(V ^ ((m + 1 : ℕ) + 1 + (s - 2) * (k : ℤ))) : PS) := by
          rw [← Units.val_mul, ← zpow_one_add]; congr 2; push_cast; ring
        have hU2 : (↑(U ^ a) : PS) * (↑(U ^ q) : PS) = (↑(U ^ (1 + q * ((k + 1 : ℕ) : ℤ))) : PS) := by
          rw [← Units.val_mul, ← zpow_add]; congr 2; push_cast [a]; ring
        have hV2 : (↑(V ^ (b - 1)) : PS) * (↑(V ^ s) : PS) =
            (↑(V ^ (((m + 1 : ℕ) : ℤ) + 1 + (s - 2) * ((k + 1 : ℕ) : ℤ))) : PS) := by
          rw [← Units.val_mul, ← zpow_add]; congr 2; push_cast [b]; ring
        calc
          (↑(U ^ a) : PS) * ((b : PS) * (↑(V ^ (b - 1)) : PS) * ((p : PS) * (↑(U ^ q) : PS) * (↑(V ^ s) : PS))) +
            (↑(V ^ b) : PS) * ((a : PS) * (↑(U ^ (a - 1)) : PS) * ((↑U : PS) * (↑V : PS)))
              = (a : PS) * (((↑(U ^ (a - 1)) : PS) * (↑U : PS)) * ((↑V : PS) * (↑(V ^ b) : PS))) +
                (p : PS) * (b : PS) * (((↑(U ^ a) : PS) * (↑(U ^ q) : PS)) * ((↑(V ^ (b - 1)) : PS) * (↑(V ^ s) : PS))) := by
                  ring
          _ = (a : PS) * ((↑(U ^ a) : PS) * (↑(V ^ (((m + 1 : ℕ) : ℤ) + 1 + (s - 2) * (k : ℤ))) : PS)) +
              (p : PS) * (b : PS) * ((↑(U ^ (1 + q * ((k + 1 : ℕ) : ℤ))) : PS) *
                (↑(V ^ (((m + 1 : ℕ) : ℤ) + 1 + (s - 2) * ((k + 1 : ℕ) : ℤ))) : PS)) := by
                  rw [hU1, hV1, hU2, hV2]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_intCast, mul_zero, add_zero, hDT]
      ring
    have hsum1 :
        ∑ k ∈ Finset.range (m + 1),
          derivative ℚ ((row p q s m k : PS) * (↑(U ^ (1 + q * (k : ℤ))) : PS) *
            (↑(V ^ ((m : ℤ) + 1 + (s - 2) * (k : ℤ))) : PS)) =
        (∑ k ∈ Finset.range (m + 1),
          (row p q s m k : PS) * ((1 + q * (k : ℤ) : ℤ) : PS) * T (m + 1) k) +
        (∑ k ∈ Finset.range (m + 1),
          (row p q s m k : PS) * (p : PS) * (((m : ℤ) + 1 + (s - 2) * (k : ℤ) : ℤ) : PS) *
            T (m + 1) (k + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hassoc :
          (row p q s m k : PS) * (↑(U ^ (1 + q * (k : ℤ))) : PS) *
            (↑(V ^ ((m : ℤ) + 1 + (s - 2) * (k : ℤ))) : PS) =
          (row p q s m k : PS) * T m k := by
        dsimp only [T]; ring
      rw [hassoc, hterm k]
    rw [hsum1]
    have hpad :
        (∑ k ∈ Finset.range (m + 1),
          (row p q s m k : PS) * ((1 + q * (k : ℤ) : ℤ) : PS) * T (m + 1) k) =
        ∑ k ∈ Finset.range (m + 2),
          (row p q s m k : PS) * ((1 + q * (k : ℤ) : ℤ) : PS) * T (m + 1) k := by
      symm
      rw [Finset.sum_range_succ, row_eq_zero_of_lt p q s m (m + 1) (Nat.lt_succ_self m)]
      simp
    rw [hpad, Finset.sum_range_succ', add_comm, ← add_assoc, ← Finset.sum_add_distrib]
    have hrhs :
        (∑ k ∈ Finset.range (m + 2),
          (row p q s (m + 1) k : PS) * (↑(U ^ (1 + q * (k : ℤ))) : PS) *
            (↑(V ^ (((m + 1 : ℕ) : ℤ) + 1 + (s - 2) * (k : ℤ))) : PS)) =
        (∑ k ∈ Finset.range (m + 1), (row p q s (m + 1) (k + 1) : PS) * T (m + 1) (k + 1)) +
          (row p q s (m + 1) 0 : PS) * T (m + 1) 0 := by
      have hcongr :
          ∑ k ∈ Finset.range (m + 2),
            (row p q s (m + 1) k : PS) * (↑(U ^ (1 + q * (k : ℤ))) : PS) *
              (↑(V ^ (((m + 1 : ℕ) : ℤ) + 1 + (s - 2) * (k : ℤ))) : PS) =
          ∑ k ∈ Finset.range (m + 2), (row p q s (m + 1) k : PS) * T (m + 1) k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp only [T]; ring
      rw [hcongr, Finset.sum_range_succ']
    rw [hrhs]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [row, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast, Int.cast_sub,
        Int.cast_ofNat, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [row, Nat.cast_zero, mul_zero, add_zero, Int.cast_one, mul_one]

private lemma sum_row_eq_constantCoeff_iterate (U V : PSˣ) (p q s : ℤ)
    (hU0 : constantCoeff (↑U : PS) = 1) (hV0 : constantCoeff (↑V : PS) = 1)
    (hDU : derivative ℚ (↑U : PS) = (↑U : PS) * (↑V : PS))
    (hDV : derivative ℚ (↑V : PS) = (p : PS) * (↑(U ^ q) : PS) * (↑(V ^ s) : PS))
    (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (row p q s n k : ℚ)) =
      constantCoeff ((derivative ℚ)^[n] ((↑U : PS) * (↑V : PS))) := by
  rw [iterate_derivative_mul U V p q s hDU hDV n, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, constantCoeff_intCast, constantCoeff_zpow_eq_one U hU0,
    constantCoeff_zpow_eq_one V hV0, mul_one, mul_one]

end OMA.P_mo_475505

open OMA.P_mo_475505 in
theorem OMA.solution : type_of% @OMA.S_mo_475505.main := by
  intro p q A B hA0 hB0 hAeq hBeq n
  constructor
  · -- Part 1: A and s = 0
    set g : PS := X + (p : PS) * primitive (primitive (↑(A ^ q) : PS))
    have hg0 : constantCoeff g = 0 := by
      simp [g, constantCoeff_primitive]
    have hg_subst : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
    set Wps : PS := 1 + (p : PS) * primitive (↑(A ^ q) : PS)
    have hW0 : constantCoeff Wps = 1 := by
      simp [Wps, constantCoeff_primitive]
    have hWunit : IsUnit Wps := isUnit_iff_constantCoeff.mpr (by rw [hW0]; exact isUnit_one)
    set W : PSˣ := hWunit.unit
    have hWval : (↑W : PS) = Wps := hWunit.unit_spec
    have hW0' : constantCoeff (↑W : PS) = 1 := by rw [hWval, hW0]
    have hDg : derivative ℚ g = (↑W : PS) := by
      rw [hWval]
      dsimp only [g, Wps]
      rw [map_add, derivative_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        derivative_intCast, mul_zero, add_zero, derivative_primitive]
    have hDA : derivative ℚ (↑A : PS) = (↑A : PS) * (↑W : PS) := by
      conv_lhs => rw [hAeq]
      rw [derivative_subst hg_subst, derivative_exp, ← hAeq, hDg]
    have hDW : derivative ℚ (↑W : PS) = (p : PS) * (↑(A ^ q) : PS) * (↑(W ^ (0 : ℤ)) : PS) := by
      rw [hWval]
      dsimp only [Wps]
      rw [map_add, derivative_one, zero_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        derivative_intCast, mul_zero, add_zero, derivative_primitive]
      simp
    have hsum := sum_row_eq_constantCoeff_iterate A W p q 0 hA0 hW0' hDA hDW n
    rw [hsum, ← hDA, ← Function.iterate_succ_apply (derivative ℚ) n (↑A : PS),
      constantCoeff_iterate_derivative]
  · -- Part 2: B and s = q
    set Ups : PS := 1 + primitive (↑B : PS)
    set Vps : PS := 1 + (p : PS) * primitive (↑(B ^ q) : PS)
    have hU0 : constantCoeff Ups = 1 := by simp [Ups, constantCoeff_primitive]
    have hV0 : constantCoeff Vps = 1 := by simp [Vps, constantCoeff_primitive]
    have hUunit : IsUnit Ups := isUnit_iff_constantCoeff.mpr (by rw [hU0]; exact isUnit_one)
    have hVunit : IsUnit Vps := isUnit_iff_constantCoeff.mpr (by rw [hV0]; exact isUnit_one)
    set U : PSˣ := hUunit.unit
    set V : PSˣ := hVunit.unit
    have hUval : (↑U : PS) = Ups := hUunit.unit_spec
    have hVval : (↑V : PS) = Vps := hVunit.unit_spec
    have hU0' : constantCoeff (↑U : PS) = 1 := by rw [hUval, hU0]
    have hV0' : constantCoeff (↑V : PS) = 1 := by rw [hVval, hV0]
    have hUV : U * V = B := by
      ext1
      rw [Units.val_mul, hUval, hVval, hBeq]
    have hUV_val : (↑U : PS) * (↑V : PS) = (↑B : PS) := by
      rw [← Units.val_mul, hUV]
    have hDU : derivative ℚ (↑U : PS) = (↑U : PS) * (↑V : PS) := by
      rw [hUV_val, hUval]
      dsimp only [Ups]
      rw [map_add, derivative_one, zero_add, derivative_primitive]
    have hDV : derivative ℚ (↑V : PS) = (p : PS) * (↑(U ^ q) : PS) * (↑(V ^ q) : PS) := by
      rw [hVval]
      dsimp only [Vps]
      rw [map_add, derivative_one, zero_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        derivative_intCast, mul_zero, add_zero, derivative_primitive, ← hUV, mul_zpow,
        Units.val_mul]
      ring
    have hsum := sum_row_eq_constantCoeff_iterate U V p q q hU0' hV0' hDU hDV n
    rw [hsum, hUV_val, constantCoeff_iterate_derivative]
