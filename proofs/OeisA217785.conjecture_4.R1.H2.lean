import OMAReductions.R_OeisA217785_conjecture_4_R1

/-!
# Reducibility of the weighted geometric sum at indices `8 * k * (k + 1)`

Step H2 of @Andyi955's reduction #9764. Credit: @Medrov.
The even-degree discriminant argument is the Frobenius sign argument of Pellet / Stickelberger.
See R. G. Swan, *Factorization of polynomials over finite fields* (1962),
https://msp.org/pjm/1962/12-3/pjm-v12-n3-p27-p.pdf .
The Lean proofs and the calculations for this polynomial were written for this submission.
-/

namespace Astra217785

open OeisA217785 Polynomial

noncomputable abbrev modS (p n : ℕ) := (polyS n).map (Int.castRingHom (ZMod p))

lemma polyS_succ (n : ℕ) : polyS (n+1) = polyS n + C (n+2 : ℤ) * X^(n+1) := by
  simp [polyS, Finset.sum_range_succ, add_assoc]
  norm_num

lemma coeff_modS (p n i : ℕ) (hi : i ≤ n) : (modS p n).coeff i = (i : ZMod p) + 1 := by
  simp only [modS, Polynomial.coeff_map, polyS, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, if_pos (Nat.lt_succ_of_le hi)]
  simp

lemma modS_natDegree_ne_one (p n : ℕ) [Fact p.Prime] (hn : 3 ≤ n) :
    (modS p n).natDegree ≠ 1 := by
  intro h
  have h2 := coeff_eq_zero_of_natDegree_lt (p := modS p n) (n := 2) (by omega)
  have h3 := coeff_eq_zero_of_natDegree_lt (p := modS p n) (n := 3) (by omega)
  rw [coeff_modS _ _ _ (by omega)] at h2 h3
  norm_num at h2 h3
  apply one_ne_zero (α := ZMod p)
  linear_combination h3 - h2

lemma twice_eval_one (p n : ℕ) :
    2 * (modS p n).eval 1 = (n+1 : ZMod p) * (n+2) := by
  induction n with
  | zero => simp [modS, polyS]
  | succ n ih =>
    simp only [modS, polyS_succ, Polynomial.map_add, Polynomial.map_mul, map_C, map_X,
      Polynomial.map_pow, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
      map_add, Int.coe_castRingHom, Int.cast_ofNat, Int.cast_natCast, Nat.cast_succ] at *
    linear_combination ih

lemma not_irreducible_at_odd_exception (n p : ℕ) (hn : 3 ≤ n) (hp : p.Prime) (hodd : p ≠ 2)
    (hbad : p ∣ (n+1)*(n+2)) : ¬ Irreducible (modS p n) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hirr
  apply hirr.not_isRoot_of_natDegree_ne_one (modS_natDegree_ne_one p n hn) (x := 1)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  have hh := (ZMod.natCast_eq_zero_iff ((n+1)*(n+2)) p).2 hbad
  push_cast at hh
  exact (mul_eq_zero.mp ((twice_eval_one p n).trans hh)).resolve_left htwo

lemma modS_two_square (m : ℕ) : modS 2 (2*m) =
    (∑ i ∈ Finset.range (m+1), (X : (ZMod 2)[X]) ^ i)^2 := by
  induction m with
  | zero => simp [modS, polyS]
  | succ m ih =>
    rw [show 2 * (m+1) = 2*m+1+1 by omega]
    simp only [modS, polyS_succ, Polynomial.map_add, Polynomial.map_mul, map_C, map_X,
      Polynomial.map_pow, Int.coe_castRingHom, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
    rw [Finset.sum_range_succ _ (m+1)]
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo]
    simp only [zero_mul, zero_add, add_zero, map_zero]
    rw [ih, add_sq, show 2*m+1+1 = (m+1)*2 by omega, pow_mul]
    have hz : (2 : (ZMod 2)[X]) = 0 := by simpa only [map_ofNat, map_zero] using congrArg (C (R := ZMod 2)) htwo
    simp [hz]

lemma not_irreducible_at_two (m : ℕ) : ¬ Irreducible (modS 2 (2*m)) := by
  rw [modS_two_square, pow_two]
  intro hi
  have hu := hi.isUnit_or_isUnit rfl
  exact hi.not_isUnit ((hu.elim id id).mul (hu.elim id id))

end Astra217785

namespace Astra217785
open Matrix Algebra FiniteField Module

lemma discr_not_square (K L : Type*) [Field K] [Fintype K] [Field L] [Finite L]
    [Algebra K L] {m : ℕ} (hr : finrank K L = m + 1) (hm : Odd m)
    (h2 : (2 : L) ≠ 0) (b : Basis (Fin (m+1)) K L) : ¬ IsSquare (Algebra.discr K b) := by
  classical
  let f := frobeniusAlgEquivOfAlgebraic K L
  let M : Matrix (Fin (m+1)) (Fin (m+1)) L := fun i j => (f ^ i.val) (b j)
  have hen : Function.Bijective (fun i : Fin (m+1) => f ^ i.val) := by
    have h := bijective_frobeniusAlgEquivOfAlgebraic_pow K L
    rw [hr] at h
    exact h
  have gram : (Algebra.traceMatrix K b).map (algebraMap K L) = M.transpose * M := by
    ext i j
    simp only [Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      trace_eq_sum_automorphisms, Matrix.mul_apply, Matrix.transpose_apply]
    exact (Fintype.sum_bijective _ hen _ _ fun t => (map_mul (f ^ t.val) _ _).symm).symm
  have hdisc : algebraMap K L (Algebra.discr K b) = M.det ^ 2 := by
    rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply, gram,
      Matrix.det_mul, Matrix.det_transpose, pow_two]
  have hdet : M.det ≠ 0 := by
    intro h
    have bad : algebraMap K L (Algebra.discr K b) = 0 := by simp [hdisc, h]
    exact Algebra.discr_not_zero_of_basis K b ((map_eq_zero _).mp bad)
  have hrotate : M.map f = M.submatrix (finRotate (m+1)) id := by
    ext i j
    change f ((f ^ i.val) (b j)) = (f ^ (finRotate (m+1) i).val) (b j)
    rw [← AlgEquiv.mul_apply, ← pow_succ', coe_finRotate]
    split_ifs with hil
    · subst i
      have hord := pow_orderOf_eq_one f
      rw [show orderOf f = m+1 from (orderOf_frobeniusAlgEquivOfAlgebraic K L).trans hr] at hord
      rw [Fin.val_last, hord, pow_zero]
    · rfl
  have hanti : f M.det = -M.det := by
    change f.toRingHom M.det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    change (M.map f).det = _
    rw [hrotate, Matrix.det_permute, sign_finRotate]
    simp [hm.neg_one_pow]
  rintro ⟨a, ha⟩
  have hh : M.det ^ 2 = (algebraMap K L a)^2 := by
    rw [← hdisc, ha, map_mul, pow_two]
  have hfix : f M.det = M.det := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h | h <;> simp [h]
  apply hdet
  apply (mul_eq_zero.mp (show (2 : L)*M.det = 0 by linear_combination hanti - hfix)).resolve_left h2

lemma discr_not_square_of_even (K L : Type*) [Field K] [Fintype K] [Field L] [Finite L]
    [Algebra K L] {n : ℕ} (hr : finrank K L = n) (he : Even n)
    (h2 : (2 : L) ≠ 0) (b : Basis (Fin n) K L) : ¬ IsSquare (Algebra.discr K b) := by
  cases n with
  | zero => exact (Module.finrank_pos (R := K) (M := L)).ne' hr |>.elim
  | succ m =>
    exact discr_not_square K L hr (by rcases he with ⟨d, hd⟩; exact ⟨d-1, by omega⟩) h2 b

end Astra217785

namespace Astra217785
open OeisA217785 Polynomial Algebra Matrix Module

lemma modS_succ (p n : ℕ) : modS p (n+1) = modS p n + C (n+2 : ZMod p) * X^(n+1) := by
  simp only [modS, polyS_succ, Polynomial.map_add, Polynomial.map_mul, map_C, map_X,
    Polynomial.map_pow, Int.coe_castRingHom, Int.cast_add, Int.cast_natCast, Int.cast_ofNat]

lemma modS_differential (p n : ℕ) :
    (X-1) * (modS p n).derivative + 2 * modS p n = C ((n+1 : ZMod p)*(n+2)) * X^n := by
  induction n with
  | zero => simp [modS, polyS, map_ofNat]
  | succ n ih =>
    rw [modS_succ, derivative_add, derivative_C_mul_X_pow]
    simp only [Nat.add_sub_cancel, Nat.cast_succ, map_mul, map_add, map_one, map_ofNat,
      C_eq_natCast, pow_succ] at *
    linear_combination ih

lemma modS_natDegree (p n : ℕ) (h : (n+1 : ZMod p) ≠ 0) : (modS p n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ ((coeff_modS p n n le_rfl) ▸ h)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hin
  rw [Polynomial.coeff_map]
  simp only [polyS, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range,
    if_neg (show ¬ i < n+1 by omega), map_zero]

lemma norm_one_sub_gen {K L : Type*} [Field K] [Field L] [Algebra K L] (b : PowerBasis K L) :
    Algebra.norm K (1-b.gen) = (minpoly K b.gen).eval 1 := by
  rw [Algebra.norm_eq_matrix_det b.basis, map_sub, map_one, ← charpoly_leftMulMatrix b,
    Matrix.eval_charpoly, map_one]

end Astra217785

namespace Astra217785
open OeisA217785 Polynomial Algebra Matrix Module

lemma good_prime (n k p : ℕ) (hk : 0 < k) (hn : n = 8*k*(k+1)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hgood : ¬ p ∣ (n+1)*(n+2)) : ¬ Irreducible (modS p n) := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : (ZMod p)) ≠ 0 := by
    intro hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 hz))
  have hab : (n+1 : (ZMod p))*(n+2) ≠ 0 := by
    intro h
    exact hgood ((ZMod.natCast_eq_zero_iff _ p).1 (by push_cast; exact h))
  have ha : (n+1 : (ZMod p)) ≠ 0 := left_ne_zero_of_mul hab
  have hc : (n+2 : (ZMod p)) ≠ 0 := right_ne_zero_of_mul hab
  have hcs : (n+2 : (ZMod p)) = 2*(2*(k : (ZMod p))+1)^2 := by rw [hn]; push_cast; ring
  have hs : (2*(k : (ZMod p))+1) ≠ 0 := by intro h; simp [h] at hcs; exact hc hcs
  have even_n : Even n := ⟨4*k*(k+1), by rw [hn]; ring⟩
  have even_sign : Even (n*(n-1)/2) := by
    have he : n*(n-1) = 4*(2*k*(k+1)*(n-1)) := by
      conv_lhs => lhs; rw [hn]
      ring
    rw [he]
    exact ⟨2*k*(k+1)*(n-1), by omega⟩
  intro hf
  let f := modS p n
  let : Fact (Irreducible f) := ⟨hf⟩
  let L := AdjoinRoot f
  let b : PowerBasis (ZMod p) L := AdjoinRoot.powerBasis hf.ne_zero
  let : Module.Finite (ZMod p) L := Module.Finite.of_basis b.basis
  let : Finite L := Module.finite_of_finite (ZMod p)
  have hdeg : f.natDegree = n := modS_natDegree p n ha
  have hr : finrank (ZMod p) L = n := b.finrank.trans hdeg
  have hlead : f.leadingCoeff = (n+1 : (ZMod p)) := by
    rw [leadingCoeff, hdeg]; exact coeff_modS _ _ _ le_rfl
  have hmin : minpoly (ZMod p) b.gen = f * C (n+1 : (ZMod p))⁻¹ := by
    rw [← hlead]; exact AdjoinRoot.minpoly_powerBasis_gen hf.ne_zero
  have hroot : aeval b.gen f = 0 := by
    change aeval (AdjoinRoot.root f) f = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have heval : f.eval 1 = (n+1 : (ZMod p))*(2*(k:(ZMod p))+1)^2 := by
    apply mul_left_cancel₀ h2
    calc 2 * f.eval 1 = (n+1 : (ZMod p))*(n+2) := twice_eval_one p n
         _ = _ := by rw [hcs]; ring
  have hnorm1 : norm (ZMod p) (1-b.gen) = (2*(k:(ZMod p))+1)^2 := by
    rw [norm_one_sub_gen, hmin, eval_mul, eval_C, heval]; field_simp
  let D := aeval b.gen f.derivative
  have hdiff : (1-b.gen)*D = algebraMap (ZMod p) L (-((n+1 : (ZMod p))*(n+2))) * b.gen^n := by
    have hd := congrArg (aeval b.gen) (modS_differential p n)
    change aeval b.gen ((X-1)*f.derivative + 2*f) = _ at hd
    simp only [map_add, map_mul, map_sub, map_one, map_ofNat, hroot, mul_zero, add_zero,
      aeval_X, aeval_C, map_pow] at hd
    simp only [map_neg, map_mul, map_add, map_one, map_ofNat]
    linear_combination -hd
  have hnorm : norm (ZMod p) (1-b.gen) * norm (ZMod p) D =
      (-((n+1 : (ZMod p))*(n+2))) ^ n * (norm (ZMod p) b.gen)^n := by
    have h := congrArg (norm (ZMod p)) hdiff
    simpa only [map_mul, map_pow, Algebra.norm_algebraMap, hr] using h
  have hd_square : IsSquare (norm (ZMod p) D) := by
    rw [hnorm1] at hnorm
    have heq : norm (ZMod p) D = ((-((n+1 : (ZMod p))*(n+2))) ^ n * (norm (ZMod p) b.gen)^n) / (2*(k:(ZMod p))+1)^2 := by
      apply (eq_div_iff (pow_ne_zero 2 hs)).2
      rwa [mul_comm]
    rw [heq]
    exact ((even_n.isSquare_pow _).mul (even_n.isSquare_pow _)).div ((isSquare_iff_exists_sq _).2 ⟨_, rfl⟩)
  have hminD : aeval b.gen (minpoly (ZMod p) b.gen).derivative = D * algebraMap (ZMod p) L (n+1 : (ZMod p))⁻¹ := by
    rw [hmin, derivative_mul, derivative_C, mul_zero, add_zero, map_mul, aeval_C]
  have hnonsq := discr_not_square_of_even (ZMod p) L b.finrank (by change Even f.natDegree; rw [hdeg]; exact even_n)
    (show (2 : L) ≠ 0 from by simpa only [map_ofNat] using ((_root_.map_ne_zero (algebraMap (ZMod p) L)).2 h2)) b.basis
  apply hnonsq
  rw [Algebra.discr_powerBasis_eq_norm, hr, even_sign.neg_one_pow, one_mul, hminD,
    map_mul, Algebra.norm_algebraMap, hr]
  exact hd_square.mul (even_n.isSquare_pow _)

end Astra217785

theorem OMA.solution : OMA.R_OeisA217785_conjecture_4_R1.H2 := by
  intro n _hn hform p hp
  obtain ⟨k, hk, heq⟩ := hform
  by_cases htwo : p = 2
  · subst p
    rw [show n = 2*(4*k*(k+1)) by rw [heq]; ring]
    exact Astra217785.not_irreducible_at_two _
  by_cases hbad : p ∣ (n+1)*(n+2)
  · have hn : 3 ≤ n := by rw [heq]; nlinarith
    exact Astra217785.not_irreducible_at_odd_exception n p hn hp htwo hbad
  exact Astra217785.good_prime n k p hk heq hp htwo hbad
