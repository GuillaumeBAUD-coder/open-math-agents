import OMAStatements.S_oeis_a066933

namespace OMA.S_oeis_a066933

open Polynomial

/-- `a n`: determinant of the `n × n` matrix whose row `i` is `2, 3, 5, ..., prime(n)`
rotated left by `i`, i.e. entry `(i, j)` is `prime(1 + ((i + j) mod n))` (0-based). -/
lemma prod_neg_one_pow_range (n : ℕ) :
    ∏ i ∈ Finset.range n, ((-1 : ℤˣ) ^ i) = (-1) ^ (n / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [show (2*k)/2 = k by omega, show (2*k+1)/2 = k by omega, pow_mul]; simp
    · rw [show (2*k+1)/2 = k by omega, show (2*k+1+1)/2 = k+1 by omega, pow_succ, pow_mul]
      simp [pow_succ]

lemma sign_revPerm (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1) ^ (n / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  have h1 : ∀ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else -1) = (-1) ^ (n - 1 - (i : ℕ)) := by
    intro i
    rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℤˣ)), Finset.prod_const, Fin.card_Ioi]
    intro j hj
    simp only [Finset.mem_Ioi] at hj
    simp [Fin.revPerm_apply, Fin.rev_lt_rev, not_lt.mpr hj.le]
  rw [Finset.prod_congr rfl (fun i _ => h1 i)]
  rw [← prod_neg_one_pow_range, ← Fin.prod_univ_eq_prod_range]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp [Fin.val_rev]; congr 1; omega)

lemma neg_eq_rotate_rev (m : ℕ) :
    Equiv.neg (Fin (m + 1)) = (Fin.revPerm).trans (finRotate (m + 1)) := by
  ext i
  simp only [Equiv.neg_apply, Equiv.trans_apply, Fin.revPerm_apply, finRotate_apply]
  rw [Fin.val_neg', Fin.val_add, Fin.val_rev]
  have hi := i.isLt
  simp
  congr 1
  omega

lemma sign_neg_fin (m : ℕ) :
    Equiv.Perm.sign (Equiv.neg (Fin (m + 1))) = (-1) ^ m * (-1) ^ ((m + 1) / 2) := by
  rw [neg_eq_rotate_rev, Equiv.Perm.sign_trans, sign_finRotate, sign_revPerm]
  simp


lemma det_hankel_circ {K : Type*} [Field K] (m : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ (m + 1))
    (c : Fin (m + 1) → K) :
    (Matrix.of fun i j : Fin (m + 1) => c (i + j)).det =
      (Equiv.Perm.sign (Equiv.neg (Fin (m + 1))) : K) *
        ∏ l : Fin (m + 1), ∑ k : Fin (m + 1), c k * ζ ^ ((k : ℕ) * (l : ℕ)) := by
  set V : Matrix (Fin (m + 1)) (Fin (m + 1)) K := Matrix.of fun i l => ζ ^ ((i : ℕ) * (l : ℕ))
  have hV : V.det ≠ 0 := by
    have : V = Matrix.vandermonde (fun i : Fin (m + 1) => ζ ^ (i : ℕ)) := by
      ext i l; simp [V, Matrix.vandermonde_apply, pow_mul]
    rw [this, Matrix.det_vandermonde_ne_zero_iff]
    intro i j h
    exact Fin.ext (hζ.pow_inj i.isLt j.isLt h)
  have hmod : ∀ x : ℕ, ζ ^ x = ζ ^ (x % (m + 1)) := fun x => by
    conv_lhs => rw [← Nat.div_add_mod x (m + 1), pow_add, pow_mul, hζ.pow_eq_one, one_pow,
      one_mul]
  have hχ : ∀ (a b : Fin (m + 1)) (l : ℕ),
      ζ ^ (((a + b : Fin (m + 1)) : ℕ) * l) = ζ ^ ((a : ℕ) * l) * ζ ^ ((b : ℕ) * l) := by
    intro a b l
    rw [Fin.val_add, ← pow_add, ← add_mul, hmod ((_ % (m + 1)) * l), hmod ((_ + _) * l),
      Nat.mod_mul_mod]
  set F : Fin (m + 1) → K := fun l => ∑ k : Fin (m + 1), c k * ζ ^ ((k : ℕ) * (l : ℕ))
  have key : (Matrix.of fun i j : Fin (m + 1) => c (i + j)) * V =
      (V.submatrix (Equiv.neg (Fin (m + 1))) id) * Matrix.diagonal F := by
    ext i l
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.submatrix_apply,
      id, Equiv.neg_apply, V, F]
    rw [← Equiv.sum_comp (Equiv.addLeft i) (fun k => c k * ζ ^ ((k : ℕ) * (l : ℕ))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.coe_addLeft]
    have : ζ ^ ((j : ℕ) * l) = ζ ^ (((i + j : Fin (m + 1)) : ℕ) * l) * ζ ^ (((-i : Fin (m + 1)) : ℕ) * l) := by
      rw [← hχ]; congr 3; abel
    rw [this]; ring
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_permute, Matrix.det_diagonal] at this
  apply mul_right_cancel₀ hV
  rw [this]; ring


lemma sum_Icc_shift {R : Type*} [CommRing R] (q : ℕ → R) (x : R) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, q (k - 1) * x ^ k = x * ∑ k ∈ Finset.range n, q k * x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel]
    ring

lemma natDegree_f (m : ℕ) : (f (m + 1)).natDegree = m + 1 := by
  apply le_antisymm
  · unfold f
    apply natDegree_sum_le_of_forall_le
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact (natDegree_C_mul_X_pow_le _ _).trans hk.2
  · apply le_natDegree_of_ne_zero
    unfold f
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, le_refl, and_self, ↓reduceIte,
      Nat.add_sub_cancel]
    exact_mod_cast (Nat.prime_nth_prime m).ne_zero

end OMA.S_oeis_a066933

open Polynomial OMA.S_oeis_a066933

theorem OMA.solution : type_of% @OMA.S_oeis_a066933.main := by
  intro n
  rcases n with _ | m
  · simp [a, f]
  have hdegg : ((X : ℤ[X]) ^ (m + 1) - 1).natDegree = m + 1 := by
    simpa using natDegree_X_pow_sub_C (R := ℤ) (r := 1) (n := m + 1)
  rw [natDegree_f, hdegg]
  apply Int.cast_injective (α := ℂ)
  have hζ := Complex.isPrimitiveRoot_exp (m + 1) (by omega)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (m + 1 : ℕ)) with hζdef
  set c : Fin (m + 1) → ℂ := fun k => ((Nat.nth Nat.Prime k : ℕ) : ℂ)
  set G : Fin (m + 1) → ℂ := fun l => ∑ k : Fin (m + 1), c k * ζ ^ ((k : ℕ) * (l : ℕ))
  have hL : ((a (m + 1) : ℤ) : ℂ) =
      (Equiv.Perm.sign (Equiv.neg (Fin (m + 1))) : ℂ) * ∏ l, G l := by
    rw [← det_hankel_circ m ζ hζ c, a, ← eq_intCast (Int.castRingHom ℂ), RingHom.map_det]
    congr 1
  set F' : ℂ[X] := (f (m + 1)).map (Int.castRingHom ℂ)
  have hR : ((resultant (f (m + 1)) (X ^ (m + 1) - 1) (m + 1) (m + 1) : ℤ) : ℂ) =
      resultant F' (X ^ (m + 1) - C 1) (m + 1) (m + 1) := by
    rw [← eq_intCast (Int.castRingHom ℂ), ← resultant_map_map]
    congr 1; simp
  have hF'deg : F'.natDegree ≤ m + 1 := natDegree_map_le.trans (natDegree_f m).le
  have hsplit : Splits ((X : ℂ[X]) ^ (m + 1) - C 1) := X_pow_sub_one_splits hζ
  have hprod := resultant_eq_prod_eval ((X : ℂ[X]) ^ (m + 1) - C 1) F' (m + 1) hF'deg hsplit
  rw [natDegree_X_pow_sub_C, (monic_X_pow_sub_C (1 : ℂ) (by omega)).leadingCoeff, one_pow,
    one_mul] at hprod
  have hroots : ((X : ℂ[X]) ^ (m + 1) - C 1).roots =
      (Multiset.range (m + 1)).map (fun l => ζ ^ l * 1) := hζ.nthRoots_eq (one_pow _)
  have hvieta := hsplit.coeff_zero_eq_prod_roots_of_monic (monic_X_pow_sub_C (1 : ℂ) (by omega))
  rw [natDegree_X_pow_sub_C, hroots] at hvieta
  have heval : ∀ l : ℕ, F'.eval (ζ ^ l * 1) = (ζ ^ l * 1) * ∑ k ∈ Finset.range (m + 1), (Nat.nth Nat.Prime k : ℂ) * (ζ ^ l * 1) ^ k := by
    intro l
    rw [← sum_Icc_shift (fun k => (Nat.nth Nat.Prime k : ℂ))]
    simp [F', f, Polynomial.map_sum, eval_finsetSum]
  have hG : ∏ l, G l = ∏ l ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (m + 1), (Nat.nth Nat.Prime k : ℂ) * (ζ ^ l * 1) ^ k := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [G, c, mul_one]
    rw [← Fin.sum_univ_eq_sum_range (fun k => (Nat.nth Nat.Prime k : ℂ) * (ζ ^ (l : ℕ)) ^ k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul, mul_comm (k : ℕ)]
  rw [← Finset.range_val, ← Finset.prod_eq_multiset_prod] at hvieta
  have hP : ∏ l ∈ Finset.range (m + 1), (ζ ^ l * 1) = (-1) ^ (m + 1) * -1 := by
    have h2 : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
      rw [← mul_pow]; simp
    simp only [coeff_sub, coeff_X_pow, coeff_C_zero] at hvieta
    simp at hvieta
    simp only [mul_one]
    linear_combination (-((-1 : ℂ) ^ (m + 1))) * hvieta + (-(∏ l ∈ Finset.range (m + 1), ζ ^ l)) * h2
  push_cast
  rw [hL, hR, resultant_comm, hprod, hroots, Multiset.map_map, ← Finset.range_val,
    ← Finset.prod_eq_multiset_prod]
  simp only [Function.comp_apply, heval]
  rw [Finset.prod_mul_distrib, hP, ← hG, sign_neg_fin]
  have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have hmm : ((-1 : ℂ) ^ ((m + 1) * (m + 1))) = (-1) ^ (m + 1) := by
    rcases Nat.even_or_odd (m + 1) with h | h
    · rw [h.neg_one_pow, (h.mul_right _).neg_one_pow]
    · rw [h.neg_one_pow, (h.mul h).neg_one_pow]
  rw [hmm]
  push_cast
  rw [pow_add, pow_succ]
  linear_combination (-(((-1 : ℂ) ^ m) * (-1) ^ ((m + 1) / 2) * ∏ l, G l)) * hsq
