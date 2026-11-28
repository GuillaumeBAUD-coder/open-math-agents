import FormalConjectures.OEIS.«217785»
import Mathlib.RingTheory.Discriminant
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! Reduction of the prime-existence converse for OeisA217785.conjecture_4. -/

open Polynomial Algebra Module OeisA217785
open scoped Matrix

-- Credit: @MrSeizy
namespace OMA.R_OeisA217785_conjecture_4_R2

/-- An even-degree extension of a finite field of odd characteristic has nonsquare
  discriminant in a power basis. -/
private theorem evenDiscrNonsquare
    {K L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L] [Finite L]
    (h2 : (2 : K) ≠ 0) (he : Even (finrank K L)) (pb : PowerBasis K L) :
    ¬ IsSquare (Algebra.discr K pb.basis) := by
  classical
  let : FiniteDimensional K L := pb.finite
  let F := FiniteField.frobeniusAlgHom K L
  have hchar : F.toLinearMap.charpoly = X ^ finrank K L - 1 := by
    have hm := FiniteField.minpoly_frobeniusAlgHom K L
    have hp : (X ^ finrank K L - 1 : K[X]).Monic := by
      simpa using monic_X_pow_sub_C (1 : K) (Nat.ne_of_gt Module.finrank_pos)
    apply eq_of_monic_of_dvd_of_natDegree_le hp (LinearMap.charpoly_monic _)
    · rw [← hm]
      exact LinearMap.minpoly_dvd_charpoly _
    · rw [LinearMap.charpoly_natDegree]
      simpa [Nat.ne_of_gt Module.finrank_pos] using
        (natDegree_X_pow_sub_C (R := K) (n := finrank K L) (r := (1 : K))).ge
  have hdet : LinearMap.det F.toLinearMap = -1 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, hchar, he.neg_one_pow]
    simp [Ne.symm (Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))), coeff_X_pow]
  let e : Fin pb.dim ≃ (L ≃ₐ[K] L) :=
    (finCongr pb.finrank.symm).trans
      (Equiv.ofBijective _ (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L))
  let N : Matrix (Fin pb.dim) (Fin pb.dim) L := Matrix.of fun i j => e j (pb.basis i)
  have htrace : (traceMatrix K pb.basis).map (algebraMap K L) = N * Nᵀ := by
    ext i j
    simp only [Matrix.map_apply, traceMatrix_apply, traceForm_apply,
      trace_eq_sum_automorphisms, Matrix.mul_apply, Matrix.transpose_apply]
    exact (Fintype.sum_equiv e _ _ (fun k => (map_mul (e k) _ _).symm)).symm
  have hsquare' : algebraMap K L (Algebra.discr K pb.basis) = N.det ^ 2 := by
    rw [discr_def, RingHom.map_det, RingHom.mapMatrix_apply, htrace, Matrix.det_mul,
      Matrix.det_transpose, pow_two]
  let A := LinearMap.toMatrix pb.basis pb.basis F.toLinearMap
  have hmatrix : F.mapMatrix N = ((algebraMap K L).mapMatrix A)ᵀ * N := by
    ext i j
    dsimp only [A]
    simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.mul_apply, LinearMap.toMatrix_apply]
    change F (e j (pb.basis i)) =
      ∑ x, algebraMap K L (pb.basis.repr (F (pb.basis i)) x) * e j (pb.basis x)
    have hcomm : e j (F (pb.basis i)) = F (e j (pb.basis i)) := by
      change e j ((pb.basis i) ^ Fintype.card K) = (e j (pb.basis i)) ^ Fintype.card K
      exact map_pow _ _ _
    rw [← hcomm]
    calc
      _ = e j (∑ x, pb.basis.repr (F (pb.basis i)) x • pb.basis x) := by
        rw [pb.basis.sum_repr]
      _ = _ := by simp [Algebra.smul_def]
  have hchange : F N.det = -N.det := by
    rw [AlgHom.map_det, hmatrix, Matrix.det_mul, Matrix.det_transpose,
      ← RingHom.map_det, LinearMap.det_toMatrix, hdet, map_neg, map_one, neg_one_mul]
  intro ⟨x, hx⟩
  have hsq : N.det ^ 2 = (algebraMap K L x) ^ 2 := by
    rw [← hsquare', hx, map_mul, pow_two]
  have hfix : F N.det = N.det := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
    · rw [h, F.commutes]
    · rw [h, map_neg, F.commutes]
  have hn : N.det ≠ 0 := by
    intro hn
    have hd := discr_not_zero_of_basis K pb.basis
    have h : Algebra.discr K pb.basis = 0 :=
      (algebraMap K L).injective (by simpa only [hn, zero_pow (by decide : 2 ≠ 0), map_zero] using hsquare')
    exact hd h
  have htwo : (2 : L) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using (algebraMap K L).injective.ne h2
  rw [hfix] at hchange
  exact mul_ne_zero htwo hn (by linear_combination hchange)

private theorem series_expansion (K : Type*) [Ring K] (n : ℕ) :
    (polyS n).map (Int.castRingHom K) =
      ∑ j ∈ Finset.range (n + 1), C ((j : K) + 1) * X ^ j := by
  simp [polyS, Polynomial.map_sum]

private theorem series_succ (K : Type*) [Ring K] (n : ℕ) :
    (polyS (n + 1)).map (Int.castRingHom K) =
      (polyS n).map (Int.castRingHom K) + C ((n : K) + 2) * X ^ (n + 1) := by
  rw [series_expansion K (n + 1), Finset.sum_range_succ, series_expansion K n]
  push_cast
  norm_num [add_assoc]

private theorem series_coeff (K : Type*) [Ring K] (n i : ℕ) :
    ((polyS n).map (Int.castRingHom K)).coeff i = if i ≤ n then (i : K) + 1 else 0 := by
  classical
  simp only [series_expansion, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

private theorem series_degree_le (K : Type*) [Ring K] (n : ℕ) :
    ((polyS n).map (Int.castRingHom K)).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [series_coeff, if_neg (not_le.mpr hm)]

private theorem series_sparse (K : Type*) [CommRing K] (n : ℕ) :
    (1 - X)^2 * ((polyS n).map (Int.castRingHom K)) =
      1 - C ((n : K) + 2) * X^(n+1) + C ((n : K) + 1) * X^(n+2) := by
  induction n with
  | zero =>
    simp [series_expansion, pow_succ, map_ofNat]
    ring
  | succ n ih =>
    rw [series_succ, mul_add, ih]
    simp only [Nat.cast_succ, pow_succ, map_add, map_one, map_ofNat]
    ring

private theorem series_at_one (K : Type*) [CommRing K] (n : ℕ) :
    2 * ((polyS n).map (Int.castRingHom K)).eval 1 = ((n : K)+1) * ((n : K)+2) := by
  induction n with
  | zero =>
    rw [series_expansion]
    simp
  | succ n ih =>
    rw [series_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
      mul_add, ih, Nat.cast_succ]
    ring

private theorem not_irreducible_of_root [Field K] {f : K[X]} (hd : 1 < f.natDegree)
    {r : K} (hr : f.IsRoot r) : ¬ Irreducible f := by
  intro h
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hr
  have hf0 := h.ne_zero
  rw [hg] at h
  rcases h.isUnit_or_isUnit rfl with hu | hu
  · simpa [natDegree_X_sub_C] using Polynomial.natDegree_eq_zero_of_isUnit hu
  · have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : g ≠ 0 := by
      rintro rfl
      exact hf0 (by simp [hg])
    rw [hg, natDegree_mul (X_sub_C_ne_zero _) h2, natDegree_X_sub_C, h1, add_zero] at hd
    exact (lt_irrefl _ hd)

private theorem norm_sub_one_eq_eval [Field K] [Field L] [Algebra K L]
    (pb : PowerBasis K L) (he : Even pb.dim) :
    Algebra.norm K (pb.gen - 1) = (minpoly K pb.gen).eval 1 := by
  rw [← charpoly_leftMulMatrix pb, Matrix.eval_charpoly (Algebra.leftMulMatrix pb.basis pb.gen),
    Algebra.norm_eq_matrix_det pb.basis,
    map_sub, map_one]
  rw [show Matrix.scalar (Fin pb.dim) (1 : K) -
      Algebra.leftMulMatrix pb.basis pb.gen = -(Algebra.leftMulMatrix pb.basis pb.gen - 1) by
    simp]
  rw [Matrix.det_neg, Fintype.card_fin, he.neg_one_pow, one_mul]

private theorem series_derivative_at_root [Field K] [Field L] [Algebra K L]
    {n : ℕ} {r : L} (hr : aeval r ((polyS n).map (Int.castRingHom K)) = 0) :
    (r - 1)^2 * aeval r ((polyS n).map (Int.castRingHom K)).derivative =
      algebraMap K L (((n : K) + 1) * ((n : K) + 2)) * r^n * (r - 1) := by
  have h := congrArg (fun f : K[X] => aeval r f.derivative) (series_sparse K n)
  simp only [derivative_mul, derivative_one, derivative_C,
    zero_sub, zero_mul, zero_add, derivative_pow, derivative_X, mul_one, map_add, map_neg,
    map_sub, map_mul, map_pow, map_one, aeval_C, aeval_X, hr] at h
  simp only [Nat.add_sub_cancel, show ∀ t : ℕ, t + 2 - 1 = t + 1 by omega,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, zero_add, pow_succ,
    map_mul, map_add, map_one, map_ofNat] at h ⊢
  linear_combination h

/-- The norm form of the discriminant calculation for the good-prime case.
  Compare Filaseta and Moy, On the Galois group over Q of a truncated binomial
  expansion, Lemma 3, specialized to the first derivative of a geometric sum. -/
private theorem good_prime_obstruction
    {K : Type*} [Field K] [Fintype K] (h2 : (2 : K) ≠ 0) {n : ℕ}
    (h4 : 4 ∣ n) (ha : (n : K) + 1 ≠ 0) (hb : (n : K) + 2 ≠ 0)
    (hs : ∃ m : K, (n : K) + 2 = 2 * m ^ 2) :
    ¬ Irreducible ((polyS n).map (Int.castRingHom K)) := by
  classical
  intro hi
  let f := (polyS n).map (Int.castRingHom K)
  let a : K := (n : K) + 1
  let b : K := (n : K) + 2
  have hdeg : f.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero (series_degree_le K n)
    simpa only [f, series_coeff, le_refl, if_true] using ha
  have hlc : f.leadingCoeff = a := by
    change f.coeff f.natDegree = a
    rw [hdeg]
    change ((polyS n).map (Int.castRingHom K)).coeff n = a
    rw [series_coeff, if_pos le_rfl]
  let : Fact (Irreducible f) := ⟨hi⟩
  let L := AdjoinRoot f
  let pb : PowerBasis K L := AdjoinRoot.powerBasis hi.ne_zero
  let : FiniteDimensional K L := pb.finite
  let : Finite L := Module.finite_of_finite K
  have hd : pb.dim = n := (AdjoinRoot.powerBasis_dim hi.ne_zero).trans hdeg
  have hrank : finrank K L = n := pb.finrank.trans hd
  have he : Even n := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 4) h4)
  have hsign : Even (n * (n - 1) / 2) := by
    obtain ⟨t, ht⟩ := h4
    rw [show n * (n - 1) = 4 * (t * (n - 1)) by rw [ht]; ring]
    rw [even_iff_two_dvd]
    omega
  have hr : aeval pb.gen f = 0 := by
    rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hmin : minpoly K pb.gen = f * C a⁻¹ := by
    rw [AdjoinRoot.minpoly_powerBasis_gen, hlc]
  have hev : 2 * f.eval 1 = a * b := series_at_one K n
  have hrs : pb.gen - 1 ≠ 0 := by
    intro hr1
    have hroot : pb.gen = 1 := sub_eq_zero.mp hr1
    rw [hroot, ← map_one (algebraMap K L), aeval_algebraMap_apply_eq_algebraMap_eval] at hr
    have hf1 : f.eval 1 = 0 := (algebraMap K L).injective (by simpa using hr)
    exact mul_ne_zero ha hb (by simpa [hf1] using hev.symm)
  have hnorm : (Algebra.norm K) (pb.gen - 1) = b / 2 := by
    rw [norm_sub_one_eq_eval pb (hd ▸ he), hmin, eval_mul, eval_C]
    apply (eq_div_iff h2).mpr
    calc
      f.eval 1 * a⁻¹ * 2 = (2 * f.eval 1) * a⁻¹ := by ring
      _ = b := by rw [hev, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  have hder : (pb.gen - 1) * aeval pb.gen (minpoly K pb.gen).derivative =
      algebraMap K L b * pb.gen ^ n := by
    rw [hmin, derivative_mul, derivative_C, mul_zero, add_zero, map_mul, aeval_C]
    have h0 := series_derivative_at_root hr
    have h0' : (pb.gen - 1) * aeval pb.gen f.derivative =
        algebraMap K L (a * b) * pb.gen ^ n := by
      apply mul_right_cancel₀ hrs
      calc
        _ = (pb.gen - 1)^2 * aeval pb.gen f.derivative := by ring
        _ = _ := h0
    rw [← mul_assoc, h0', map_mul, map_inv₀]
    have ham : algebraMap K L a ≠ 0 := by
      simpa only [map_zero] using (algebraMap K L).injective.ne ha
    calc
      _ = (algebraMap K L a * (algebraMap K L a)⁻¹) *
          (algebraMap K L b * pb.gen ^ n) := by ring
      _ = _ := by rw [mul_inv_cancel₀ ham, one_mul]
  have hn := congrArg (Algebra.norm K) hder
  rw [map_mul, map_mul, map_pow, Algebra.norm_algebraMap, hrank, hnorm, ← mul_pow] at hn
  obtain ⟨m, hm⟩ := hs
  have hbm : b / 2 = m ^ 2 := (div_eq_iff h2).mpr (by rw [show b = _ from hm]; ring)
  have hm0 : m ≠ 0 := by
    intro hm0
    apply hb
    simpa [hm0] using hm
  rw [hbm] at hn
  have hdisc : IsSquare (Algebra.discr K pb.basis) := by
    rw [Algebra.discr_powerBasis_eq_norm, hrank, hsign.neg_one_pow, one_mul]
    obtain ⟨u, hu⟩ := he.isSquare_pow (b * (Algebra.norm K) pb.gen)
    refine ⟨u / m, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hm0)
    rw [hn, hu]
    field_simp
  exact evenDiscrNonsquare h2 (hrank ▸ he) pb hdisc

private theorem char_two_series_even [Field K] [CharP K 2] {n : ℕ} (he : Even n) :
    ¬ Irreducible ((polyS n).map (Int.castRingHom K)) := by
  obtain ⟨m, hm⟩ := he
  let g : K[X] := ∑ j ∈ Finset.range (m + 1), X ^ j
  have hgeom : g * (1 - X) = 1 - X ^ (m + 1) := geom_sum_mul_neg X (m + 1)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcast : (n : K) = 0 := by
    rw [hm, ← two_mul, Nat.cast_mul, Nat.cast_ofNat, h2, zero_mul]
  have hx : (1 - (X : K[X])) ≠ 0 := by
    simpa only [C_1] using sub_ne_zero.mpr (Ne.symm (X_ne_C (1 : K)))
  have hsq : ((polyS n).map (Int.castRingHom K)) = g ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hx)
    rw [series_sparse, hcast, zero_add, zero_add, h2, C_0, zero_mul, sub_zero, C_1, one_mul,
      ← mul_pow, mul_comm (1 - X) g, hgeom, sub_pow_expChar (p := 2) (1 : K[X]), one_pow, ← pow_mul,
      show (m + 1) * 2 = n + 2 by omega]
    have htwoP : (2 : K[X]) = 0 := CharP.cast_eq_zero _ 2
    linear_combination (X : K[X]) ^ (n + 2) * htwoP
  rw [hsq, pow_two]
  intro h
  rcases h.isUnit_or_isUnit rfl with hu | hu <;> exact h.not_isUnit (hu.mul hu)

private theorem char_two_series [Field K] [CharP K 2] (n : ℕ) :
    ¬ Irreducible ((polyS n).map (Int.castRingHom K)) := by
  rcases Nat.even_or_odd n with he | ho
  · exact char_two_series_even he
  · obtain ⟨m, rfl⟩ := ho
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [series_succ, Nat.cast_mul, Nat.cast_ofNat, h2, zero_mul, add_zero, C_0, zero_mul, add_zero]
    exact char_two_series_even (even_two_mul m)

private theorem bad_odd_prime_obstruction [Field K] {n : ℕ} (hn : 3 ≤ n)
    (h2 : (2 : K) ≠ 0) (hbad : (n : K) + 1 = 0 ∨ (n : K) + 2 = 0) :
    ¬ Irreducible ((polyS n).map (Int.castRingHom K)) := by
  have hr : ((polyS n).map (Int.castRingHom K)).IsRoot 1 := by
    have h := series_at_one K n
    rw [show ((n : K) + 1) * ((n : K) + 2) = 0 by exact mul_eq_zero.mpr hbad] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  refine not_irreducible_of_root ?_ hr
  have hne : ∀ i : ℕ, i ≤ n → (i : K) + 1 ≠ 0 → i ≤ ((polyS n).map (Int.castRingHom K)).natDegree := by
    intro i hi h
    apply le_natDegree_of_ne_zero
    simpa only [series_coeff, if_pos hi] using h
  rcases hbad with ha | hb
  · have hcast : ((n - 1 : ℕ) : K) + 1 = (n : K) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]
    have htop : (n : K) ≠ 0 := by
      intro h
      simp [h] at ha
    have h := hne (n - 1) (by omega) (hcast ▸ htop)
    omega
  · have ha : (n : K) + 1 ≠ 0 := by
      intro ha
      have h : (1 : K) = 0 := by linear_combination hb - ha
      exact one_ne_zero h
    have h := hne n le_rfl ha
    omega

/-- Every polynomial in an exceptional degree fails to be irreducible at every prime. -/
theorem exceptional_all_primes {n k : ℕ} (hk : 0 < k)
    (h : n = 8 * k * (k + 1)) (p : ℕ) (hp : p.Prime) :
    ¬ Irreducible ((polyS n).map (Int.castRingHom (ZMod p))) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases htwo : p = 2
  · subst p
    exact char_two_series n
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    exact htwo (by have := hp.two_le; omega)
  by_cases hbad : (n : ZMod p) + 1 = 0 ∨ (n : ZMod p) + 2 = 0
  · apply bad_odd_prime_obstruction _ h2 hbad
    rw [h]
    exact le_trans (by decide : 3 ≤ 8 * 1 * 2)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hk) (by omega))
  · push Not at hbad
    refine good_prime_obstruction h2 ?_ hbad.1 hbad.2 ?_
    · refine ⟨2 * k * (k + 1), ?_⟩
      rw [h]
      ring
    · refine ⟨2 * (k : ZMod p) + 1, ?_⟩
      rw [h]
      push_cast
      ring

private theorem series_irreducible_one_or_two {n : ℕ} (hn : 1 ≤ n) (h : n ≤ 2) :
    Irreducible ((polyS n).map (Int.castRingHom (ZMod 3))) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply irreducible_of_degree_eq_one
  change ((polyS n).map (Int.castRingHom (ZMod 3))).degree = ((1 : ℕ) : WithBot ℕ)
  rw [degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [series_coeff]
    split
    next hmn =>
      obtain rfl : m = 2 := by omega
      decide
    next => rfl
  · rw [series_coeff, if_pos hn]
    decide

private theorem series_irreducible_three :
    Irreducible ((polyS 3).map (Int.castRingHom (ZMod 3))) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc]
    have hd : ((polyS 3).map (Int.castRingHom (ZMod 3))).natDegree = 3 := by
      apply natDegree_eq_of_le_of_coeff_ne_zero (series_degree_le _ _)
      rw [series_coeff, if_pos le_rfl]
      decide
    rw [hd]
    decide
  · intro x
    have hx : x ^ 3 = x := by simpa only [ZMod.card] using FiniteField.pow_card x
    have h1 : (1 : ZMod 3) + 1 = 2 := by decide
    have h2 : ((2 : ℕ) : ZMod 3) + 1 = 0 := by decide
    have h3 : ((3 : ℕ) : ZMod 3) + 1 = 1 := by decide
    have hline : (2 : ZMod 3) * x + x = 0 := by
      calc
        _ = (3 : ZMod 3) * x := by ring
        _ = 0 := by rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
    simp only [IsRoot, series_expansion, eval_add, eval_one, eval_mul, eval_pow, eval_C, eval_X,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, zero_add,
      pow_zero, pow_one, h1, h2, h3, zero_mul, add_zero, one_mul, hx, add_assoc, hline,
      one_ne_zero]
    exact fun h => h

/-- An irreducible reduction in each odd degree greater than three. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n → Odd n →
    ∃ p : ℕ, p.Prime ∧
      Irreducible ((OeisA217785.polyS n).map (Int.castRingHom (ZMod p)))

/-- An irreducible reduction in each even nonexceptional degree greater than two. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n →
    (¬ ∃ k : ℕ, 0 < k ∧ n = 8 * k * (k + 1)) →
    ∃ p : ℕ, p.Prime ∧
      Irreducible ((OeisA217785.polyS n).map (Int.castRingHom (ZMod p)))

theorem main : H1 → H2 → type_of% @OeisA217785.conjecture_4 := by
  intro hodd heven n hn
  constructor
  · intro hall
    by_contra hform
    by_cases hs : n ≤ 2
    · exact hall 3 (by decide) (series_irreducible_one_or_two hn hs)
    by_cases ht : n = 3
    · subst n
      exact hall 3 (by decide) series_irreducible_three
    have hlarge : 4 ≤ n := by omega
    obtain ⟨p, hp, hi⟩ := (Nat.even_or_odd n).elim
      (fun he => heven n hlarge he hform) (fun ho => hodd n hlarge ho)
    exact hall p hp hi
  · rintro ⟨k, hk, h⟩ p hp
    exact exceptional_all_primes hk h p hp

end OMA.R_OeisA217785_conjecture_4_R2
