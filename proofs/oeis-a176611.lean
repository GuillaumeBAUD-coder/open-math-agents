import OMAStatements.S_oeis_a176611

/-! Generating identities for integer convolution sequences with affine forcing. -/

namespace OMA.A176Convolution

open PowerSeries

abbrev Series := ℚ⟦X⟧

/-- The initial coefficients and convolution with a degree-one forcing term. -/
structure HasConvolution (a : ℕ → ℤ) (initial slope : ℤ) : Prop where
  zero : a 0 = 1
  one : a 1 = initial
  step : ∀ n : ℕ,
    a (n+2) = (∑ p ∈ Finset.range (n+2), a p * a (n+1-p)) + slope*((n:ℤ)+2)+1

/-- Prefix-list implementation of the affine convolution. -/
theorem convolution_of_prefix (L : ℕ → List ℤ) (b d : ℤ)
    (h0 : L 0 = [1]) (h1 : L 1 = [1,b])
    (hstep : ∀ n : ℕ, L (n+2) = L (n+1) ++
      [(∑ p ∈ Finset.range (n+2), (L (n+1)).getD p 0 * (L (n+1)).getD (n+1-p) 0)
        + d*((n:ℤ)+2)+1]) :
    HasConvolution (fun n => (L n).getD n 0) b d := by
  let a (n : ℕ) := (L n).getD n 0
  have hAppend (n : ℕ) : ∃ z : ℤ, L (n+1) = L n ++ [z] := by
    cases n with
    | zero => exact ⟨b,by rw [h0,h1]; rfl⟩
    | succ n => exact ⟨_,hstep n⟩
  have hLen (n : ℕ) : (L n).length = n+1 := by
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      obtain ⟨z,hz⟩ := hAppend n
      simp [hz,ih]
  have hGet {i n : ℕ} (hi : i ≤ n) : (L n).getD i 0 = a i := by
    induction n with
    | zero =>
      have : i = 0 := by omega
      subst i
      rfl
    | succ n ih =>
      by_cases h : i = n+1
      · subst i
        rfl
      · obtain ⟨z,hz⟩ := hAppend n
        rw [hz, List.getD_append _ _ _ _ (by rw [hLen]; omega)]
        exact ih (by omega)
  constructor
  · change a 0 = 1
    dsimp only [a]
    rw [h0]
    rfl
  · change a 1 = b
    dsimp only [a]
    rw [h1]
    rfl
  · intro n
    change (L (n+2)).getD (n+2) 0 =
      (∑ p ∈ Finset.range (n+2), a p * a (n+1-p)) + d*((n:ℤ)+2)+1
    rw [hstep, List.getD_append_right _ _ _ _ (by rw [hLen]),hLen,Nat.sub_self]
    change (∑ p ∈ Finset.range (n+2), (L (n+1)).getD p 0 * (L (n+1)).getD (n+1-p) 0)
      + d*((n:ℤ)+2)+1 = _
    congr 2
    apply Finset.sum_congr rfl
    intro p hp
    rw [hGet (by have := Finset.mem_range.mp hp; omega),hGet (Nat.sub_le _ _)]

def series (a : ℕ → ℤ) : Series := PowerSeries.mk (fun n => (a n : ℚ))

theorem coeff_series (a : ℕ → ℤ) (n : ℕ) : coeff n (series a) = (a n : ℚ) :=
  PowerSeries.coeff_mk _ _

private noncomputable def residual (a : ℕ → ℤ) : Series :=
  series a - X*(series a)^2

private theorem coeff_residual_zero {a : ℕ → ℤ} {b d : ℤ} (h : HasConvolution a b d) :
    coeff 0 (residual a) = 1 := by
  rw [residual,map_sub,coeff_zero_X_mul,coeff_series,h.zero]
  norm_num

private theorem coeff_residual_one {a : ℕ → ℤ} {b d : ℤ} (h : HasConvolution a b d) :
    coeff 1 (residual a) = (b : ℚ)-1 := by
  rw [residual,map_sub,coeff_succ_X_mul 0,pow_two,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [coeff_series,h.zero,h.one]

private theorem coeff_residual_add_two {a : ℕ → ℤ} {b d : ℤ} (h : HasConvolution a b d) (n : ℕ) :
    coeff (n+2) (residual a) = (d:ℚ)*((n:ℚ)+2)+1 := by
  rw [residual,map_sub,coeff_succ_X_mul (n+1),pow_two,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,coeff_series,h.step]
  push_cast
  simp only [coeff_series]
  ring

private theorem constant_residual_relation {a : ℕ → ℤ} {b : ℤ} (h : HasConvolution a b 0) :
    (1-X)*residual a = 1 + C ((b:ℚ)-2)*X - C ((b:ℚ)-2)*X^2 := by
  ext n
  rw [sub_mul,one_mul]
  conv_lhs => rw [map_sub]
  conv_rhs => rw [map_sub,map_add,coeff_one,coeff_C_mul,coeff_C_mul,coeff_X,coeff_X_pow]
  rcases n with _ | _ | _ | n
  · norm_num [coeff_zero_X_mul,coeff_residual_zero h]
  · norm_num [coeff_succ_X_mul 0,coeff_residual_zero h,coeff_residual_one h] <;> ring
  · norm_num [coeff_succ_X_mul 1,coeff_residual_add_two h 0,coeff_residual_one h] <;> ring
  · rw [coeff_succ_X_mul (n+2),coeff_residual_add_two h (n+1),coeff_residual_add_two h n]
    simp [show n+3 ≠ 2 by omega]

private theorem linear_residual_relation {a : ℕ → ℤ} {b : ℤ} (h : HasConvolution a b 1) :
    (1-X)^2*residual a =
      1 + C ((b:ℚ)-3)*X + C (6-2*(b:ℚ))*X^2 + C ((b:ℚ)-3)*X^3 := by
  have he : (1-X)^2*residual a = residual a - C (2:ℚ)*(X*residual a) + X^2*residual a := by
    rw [map_ofNat C 2]
    ring
  rw [he]
  ext n
  conv_lhs => rw [map_add,map_sub,coeff_C_mul,coeff_X_pow_mul']
  conv_rhs => rw [map_add,map_add,map_add,coeff_one,coeff_C_mul,coeff_C_mul,coeff_C_mul,
    coeff_X,coeff_X_pow,coeff_X_pow]
  rcases n with _ | _ | _ | _ | n
  · norm_num [coeff_zero_X_mul,coeff_residual_zero h]
  · norm_num [coeff_succ_X_mul 0,coeff_residual_zero h,coeff_residual_one h] <;> ring
  · norm_num [coeff_succ_X_mul 1,coeff_residual_add_two h 0,
      coeff_residual_one h,coeff_residual_zero h]
    all_goals ring
  · norm_num [coeff_succ_X_mul 2,coeff_residual_add_two h 1,
      coeff_residual_add_two h 0,coeff_residual_one h] <;> ring
  · rw [coeff_succ_X_mul (n+3),if_pos (by omega : 2 ≤ n+4),
      show n+4-2 = n+2 by omega,
      coeff_residual_add_two h (n+2),coeff_residual_add_two h (n+1),coeff_residual_add_two h n]
    simp [show n+4 ≠ 2 by omega, show n+4 ≠ 3 by omega]
    ring

/-- Completed square for a constant convolution correction. -/
theorem square_constant {a : ℕ → ℤ} {b : ℤ} (h : HasConvolution a b 0) :
    (1-X)*(1-2*X*series a)^2 =
      1-5*X-4*C ((b:ℚ)-2)*X^2+4*C ((b:ℚ)-2)*X^3 := by
  calc
    _ = (1-X) - 4*X*((1-X)*residual a) := by
      unfold residual
      ring
    _ = _ := by
      rw [constant_residual_relation h]
      ring

/-- Completed square for a linear convolution correction. -/
theorem square_linear {a : ℕ → ℤ} {b : ℤ} (h : HasConvolution a b 1) :
    ((1-X)*(1-2*X*series a))^2 =
      (1-X)^2 - 4*X*(1 + C ((b:ℚ)-3)*X + C (6-2*(b:ℚ))*X^2 + C ((b:ℚ)-3)*X^3) := by
  calc
    _ = (1-X)^2 - 4*X*((1-X)^2*residual a) := by
      unfold residual
      ring
    _ = _ := by rw [linear_residual_relation h]

end OMA.A176Convolution

/-! The exact generating equation for A176611. -/

namespace OMA.A176611Proof

open OMA.S_oeis_a176611 OMA.A176Convolution PowerSeries

private theorem convolution : HasConvolution a 1 1 := by
  apply convolution_of_prefix aList 1 1 rfl rfl
  intro n
  simp only [one_mul]
  rfl

theorem square_relation :
    let A : Series := PowerSeries.mk (fun n => (a n : ℚ))
    ((1-X)*(1-2*X*A))^2 = 1-6*X+9*X^2-16*X^3+8*X^4 := by
  let A := series a
  change ((1-X)*(1-2*X*A))^2 = 1-6*X+9*X^2-16*X^3+8*X^4
  have h := square_linear convolution
  norm_num [map_neg, map_ofNat] at h
  linear_combination h

end OMA.A176611Proof

namespace OMA.ConvolutionLinearResidual

open PowerSeries

abbrev QPS := ℚ⟦X⟧

noncomputable def F (b : ℚ) : QPS :=
  1 - 6 * X + C (13 - 4*b) * X^2 + C (-24 + 8*b) * X^3 + C (12 - 4*b) * X^4

private noncomputable def E : QPS := 1 - C 5 * X + C 9 * X^2 - X^3

private noncomputable def D (b : ℚ) : QPS :=
  1 - C 7 * X + C (19 - 4*b) * X^2 + C (-37 + 12*b) * X^3
    + C (36 - 12*b) * X^4 + C (-12 + 4*b) * X^5

private noncomputable def R (b : ℚ) : QPS :=
  1 + C (-5 + 2*b) * X + C (18 - 6*b) * X^2 + C (-18 + 6*b) * X^3
    + C (6 - 2*b) * X^4

private theorem derivative_natCast (n : ℕ) : PowerSeries.derivative ℚ (n : QPS) = 0 := by
  rw [← map_natCast (C : ℚ →+* QPS)]
  simp

private theorem derivative_F (b : ℚ) : PowerSeries.derivative ℚ (F b) =
    -6 + C (13 - 4*b) * 2 * X + C (-24 + 8*b) * 3 * X^2
      + C (12 - 4*b) * 4 * X^3 := by
  unfold F
  simp [map_sub, map_add, Derivation.leibniz, smul_eq_mul,
    show PowerSeries.derivative ℚ (6 : QPS) = 0 by exact derivative_natCast 6]
  ring

private theorem factor_D (b : ℚ) : (1-X)*F b = D b := by
  simp only [F, D, map_add, map_sub, map_mul, map_neg, map_ofNat]
  ring

private theorem combine_F (b : ℚ) : 2*F b + (1-X)*PowerSeries.derivative ℚ (F b) = -4*R b := by
  rw [derivative_F]
  simp only [F, R, map_add, map_sub, map_mul, map_neg, map_ofNat]
  ring

private theorem combine_D (b : ℚ) : D b + 2*X*R b = E := by
  simp only [D, E, R, map_add, map_sub, map_mul, map_neg, map_ofNat]
  ring

private theorem differential (b : ℚ) (G : QPS)
    (h : ((1-X)*(1-2*X*G))^2 = F b) : D b * (X * PowerSeries.derivative ℚ G) + E*G = R b := by
  let S : QPS := (1-X)*(1-2*X*G)
  change S^2 = F b at h
  have hd : 2*S*PowerSeries.derivative ℚ S = PowerSeries.derivative ℚ (F b) := by
    simpa [derivative_pow, mul_assoc] using congrArg (PowerSeries.derivative ℚ) h
  have hcancel : 2*F b*PowerSeries.derivative ℚ S = PowerSeries.derivative ℚ (F b)*S := by
    rw [← hd, ← h]
    ring
  have hds : PowerSeries.derivative ℚ S = -(1-2*X*G) - 2*(1-X)*(G+X*PowerSeries.derivative ℚ G) := by
    unfold S
    simp [map_sub, Derivation.leibniz, smul_eq_mul,
      show PowerSeries.derivative ℚ (2 : QPS) = 0 by exact derivative_natCast 2]
    ring
  rw [hds] at hcancel
  have hidentity : -4 * ((1-X)*F b) * (G+X*PowerSeries.derivative ℚ G) =
      (2*F b + (1-X)*PowerSeries.derivative ℚ (F b)) * (1-2*X*G) := by
    change _ = PowerSeries.derivative ℚ (F b) * ((1-X)*(1-2*X*G)) at hcancel
    linear_combination hcancel
  rw [factor_D, combine_F] at hidentity
  have hscaled : (-4 : QPS) * (D b * (X * PowerSeries.derivative ℚ G) + E*G - R b) = 0 := by
    rw [← combine_D b]
    linear_combination hidentity
  have hfour : (-4 : QPS) ≠ 0 := by
    intro hz
    have hconstant := congrArg (constantCoeff : QPS →+* ℚ) hz
    rw [map_neg, map_ofNat, map_zero] at hconstant
    norm_num at hconstant
  exact sub_eq_zero.mp ((mul_eq_zero.mp hscaled).resolve_left hfour)

private theorem coeff_X_derivative (G : QPS) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * PowerSeries.derivative ℚ G) = (n : ℚ) * coeff n G := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]

private theorem coeff_shift_X (G : QPS) (n : ℕ) (h : 1 ≤ n) :
    coeff n (X * G) = coeff (n-1) G := by
  simpa [h] using coeff_X_pow_mul' G 1 n

theorem coefficients (b : ℤ) (a : ℕ → ℤ)
    (h : ((1-X)*(1-2*X*PowerSeries.mk (fun n => (a n : ℚ))))^2 = F b)
    (n : ℕ) (hn : 5 ≤ n) :
    ((n : ℤ) + 1) * a n + (2-7*(n : ℤ))*a (n-1)
      + ((19-4*b)*(n : ℤ)-29+8*b)*a (n-2)
      + ((-37+12*b)*(n : ℤ)+110-36*b)*a (n-3)
      + (36-12*b)*((n : ℤ)-4)*a (n-4)
      + (12-4*b)*(5-(n : ℤ))*a (n-5) = 0 := by
  have heq := differential (b : ℚ) (PowerSeries.mk fun n => (a n : ℚ)) h
  apply_fun coeff n at heq
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h0 : n ≠ 0 := by omega
  have hx : n ≠ 1 := by omega
  have hxx : n ≠ 2 := by omega
  have hxxx : n ≠ 3 := by omega
  have hxxxx : n ≠ 4 := by omega
  have hshift (j : ℕ) (hj : j ≤ n) :
      coeff n (X^j * (X * PowerSeries.derivative ℚ (PowerSeries.mk fun n => (a n : ℚ)))) =
        ((n-j : ℕ) : ℚ) * (a (n-j) : ℚ) := by
    rw [coeff_X_pow_mul', if_pos hj]
    by_cases hjn : j = n
    · subst j
      simp
    · rw [coeff_X_derivative _ _ (by omega), coeff_mk]
  have hshiftX :
      coeff n (X * (X * PowerSeries.derivative ℚ (PowerSeries.mk fun n => (a n : ℚ)))) =
        ((n-1 : ℕ) : ℚ) * (a (n-1) : ℚ) := by
    simpa using hshift 1 h1
  simp only [D, E, R, sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_one, coeff_X, coeff_X_pow, coeff_C_mul, if_neg h0, if_neg hx, if_neg hxx,
    if_neg hxxx, if_neg hxxxx, mul_zero, add_zero, coeff_mk] at heq
  rw [coeff_X_derivative _ _ h1, coeff_mk, hshiftX,
    hshift 2 h2, hshift 3 h3, hshift 4 h4, hshift 5 hn,
    coeff_shift_X _ _ h1, coeff_X_pow_mul' _ 2 _, if_pos h2,
    coeff_X_pow_mul' _ 3 _, if_pos h3, coeff_mk, coeff_mk, coeff_mk] at heq
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4,
    Nat.cast_sub hn] at heq
  have hq : ((n : ℚ) + 1) * (a n : ℚ) + (2-7*(n : ℚ))*(a (n-1) : ℚ)
      + ((19-4*(b : ℚ))*(n : ℚ)-29+8*(b : ℚ))*(a (n-2) : ℚ)
      + ((-37+12*(b : ℚ))*(n : ℚ)+110-36*(b : ℚ))*(a (n-3) : ℚ)
      + (36-12*(b : ℚ))*((n : ℚ)-4)*(a (n-4) : ℚ)
      + (12-4*(b : ℚ))*(5-(n : ℚ))*(a (n-5) : ℚ) = 0 := by
    push_cast at heq
    linear_combination heq
  exact_mod_cast hq


end OMA.ConvolutionLinearResidual

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a176611.main := by
  intro n hn
  let a := OMA.S_oeis_a176611.a
  have hs : ((1-X)*(1-2*X*PowerSeries.mk (fun j => (a j : ℚ))))^2 =
      OMA.ConvolutionLinearResidual.F 1 := by
    rw [show ((1-X)*(1-2*X*PowerSeries.mk (fun j => (a j : ℚ))))^2 =
        (1-6*X+9*X^2-16*X^3+8*X^4) from OMA.A176611Proof.square_relation]
    unfold OMA.ConvolutionLinearResidual.F
    norm_num [map_neg, map_ofNat]
    ring
  have h := OMA.ConvolutionLinearResidual.coefficients 1 a hs n hn
  dsimp only [a] at h
  norm_num at h
  linear_combination h
