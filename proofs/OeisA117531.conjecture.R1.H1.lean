import OMAReductions.R_OeisA117531_conjecture_R1
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic

open Polynomial NumberField Matrix

namespace OMA.H1aux

lemma row_contra {p q s : ℕ} (hrow : ∀ t : ℕ, t + 1 < p → (t * (t + 1) + p).Prime)
    (hq : q.Prime) (hqp : q < p) (hs : s + 1 < p) (hdvd : q ∣ s * (s + 1) + p) : False := by
  rcases (hrow s hs).eq_one_or_self_of_dvd q hdvd with h | h
  · exact hq.one_lt.ne' h
  · have h2 : p ≤ q := h ▸ Nat.le_add_left _ _
    omega

lemma sqfree {p : ℕ} (hp : p.Prime) (h41 : 41 < p)
    (hrow : ∀ t : ℕ, t + 1 < p → (t * (t + 1) + p).Prime) :
    Squarefree ((1 : ℤ) - 4 * p) := by
  rw [← Int.squarefree_natAbs]
  have hna : ((1 : ℤ) - 4 * p).natAbs = 4 * p - 1 := by omega
  rw [hna, Nat.squarefree_iff_prime_squarefree]
  intro q hq hqq
  have hq' : q.Prime := hq
  have hle : q * q ≤ 4 * p - 1 := Nat.le_of_dvd (by omega) hqq
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : 2 ∣ 4 * p - 1 := (Dvd.intro 2 rfl).trans hqq
    omega
  obtain ⟨s, hs⟩ : ∃ s, q = 2 * s + 1 := by
    rcases hq'.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hq2
    · exact ⟨k, hk⟩
  have hqp : q < p := by
    by_contra hc
    have hc' := not_lt.mp hc
    have h1 := Nat.mul_le_mul hc' hc'
    have h2 : p * p < 4 * p := lt_of_le_of_lt (h1.trans hle) (by omega)
    nlinarith
  have hdvd4 : q ∣ 4 * (s * (s + 1) + p) := by
    have : 4 * (s * (s + 1) + p) = q * q + (4 * p - 1) := by
      subst hs; zify [show 1 ≤ 4 * p by omega]; ring
    rw [this]
    exact dvd_add (dvd_mul_right q q) ((Dvd.intro q rfl).trans hqq)
  have hcop : Nat.Coprime q 4 := by
    rw [Nat.coprime_comm, show (4 : ℕ) = 2 ^ 2 by norm_num]
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes Nat.prime_two hq').mpr (Ne.symm hq2)
  exact row_contra hrow hq' hqp (by omega) (hcop.dvd_of_dvd_mul_left hdvd4)

lemma irred {p : ℕ} (hp : p.Prime) : Irreducible (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ)) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  push_cast at hb
  have : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
  nlinarith [sq_nonneg b]


abbrev Kp (p : ℕ) := AdjoinRoot (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ))

section
variable (p : ℕ) [hF : Fact (Irreducible (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ)))]

lemma f_ne : (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ)) ≠ 0 := hF.out.ne_zero

lemma root_sq : (AdjoinRoot.root (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ))) ^ 2 =
    (1 : Kp p) - 4 * (p : Kp p) := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h, ← AdjoinRoot.algebraMap_eq]
  push_cast
  simp

lemma finrank_Kp : Module.finrank ℚ (Kp p) = 2 := by
  rw [(AdjoinRoot.powerBasis (f_ne p)).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

lemma trace_root : Algebra.trace ℚ (Kp p)
    (AdjoinRoot.root (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ))) = 0 := by
  have h := (AdjoinRoot.powerBasis (f_ne p)).trace_gen_eq_nextCoeff_minpoly
  rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root (f_ne p)] at h
  refine h.trans ?_
  rw [(monic_X_pow_sub_C _ two_ne_zero).leadingCoeff, inv_one, C_1, mul_one, nextCoeff,
    natDegree_X_pow_sub_C]
  simp [coeff_one]

noncomputable def om : Kp p := (1 + AdjoinRoot.root (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ))) / 2

lemma om_quad : om p ^ 2 - om p + (p : Kp p) = 0 := by
  have h := root_sq p
  unfold om
  linear_combination (1 / 4 : Kp p) * h

lemma trace_mul (a : ℚ) (x : Kp p) :
    Algebra.trace ℚ (Kp p) (algebraMap ℚ (Kp p) a * x) = a * Algebra.trace ℚ (Kp p) x := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

lemma trace_one' : Algebra.trace ℚ (Kp p) 1 = 2 := by
  have := Algebra.trace_algebraMap (S := Kp p) (1 : ℚ)
  rw [map_one, finrank_Kp] at this
  rw [this]; norm_num

lemma trace_om : Algebra.trace ℚ (Kp p) (om p) = 1 := by
  have : om p = algebraMap ℚ (Kp p) (1 / 2) *
      (1 + AdjoinRoot.root (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ))) := by
    rw [map_div₀, map_one, map_ofNat]; unfold om; ring
  rw [this, trace_mul, map_add, trace_one', trace_root]; norm_num

lemma trace_om_sq : Algebra.trace ℚ (Kp p) (om p * om p) = 1 - 2 * p := by
  have h : om p * om p = om p - algebraMap ℚ (Kp p) (p : ℚ) := by
    rw [map_natCast]; linear_combination om_quad p
  rw [h, map_sub, trace_om, Algebra.trace_algebraMap, finrank_Kp]; simp

lemma discr_om : Algebra.discr ℚ ![1, om p] = 1 - 4 * p := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, mul_one, trace_one', trace_om, trace_om_sq]
  ring

lemma om_int : IsIntegral ℤ (om p) := by
  refine ⟨X ^ 2 - X + C (p : ℤ), by monicity!, ?_⟩
  have := om_quad p
  simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
  rw [map_natCast]
  exact this

end


section
variable (p : ℕ) [hF : Fact (Irreducible (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ)))]

noncomputable def w : 𝓞 (Kp p) := ⟨om p, om_int p⟩

lemma w_quad : w p ^ 2 - w p + (p : 𝓞 (Kp p)) = 0 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (Kp p)) (Kp p)
  simp only [map_add, map_sub, map_pow, map_natCast, map_zero]
  exact om_quad p

lemma abs_discr_le (hp : 1 ≤ p) : |discr (Kp p)| ≤ 4 * (p : ℤ) - 1 := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 (Kp p))) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_Kp]
  let e := Fintype.equivFinOfCardEq hcard
  let Mz : Matrix (Fin 2) (Fin 2) ℤ := fun i j =>
    (RingOfIntegers.basis (Kp p)).repr ((![1, w p] : Fin 2 → 𝓞 (Kp p)) j) (e.symm i)
  have hsum : ∀ x : 𝓞 (Kp p), ∑ i, (integralBasis (Kp p) ∘ e.symm) i *
      algebraMap ℚ (Kp p) (((RingOfIntegers.basis (Kp p)).repr x (e.symm i) : ℤ) : ℚ) =
      algebraMap (𝓞 (Kp p)) (Kp p) x := by
    intro x
    refine (Equiv.sum_comp e.symm (fun k => integralBasis (Kp p) k *
      algebraMap ℚ (Kp p) (((RingOfIntegers.basis (Kp p)).repr x k : ℤ) : ℚ))).trans ?_
    conv_rhs => rw [← (RingOfIntegers.basis (Kp p)).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [integralBasis_apply, zsmul_eq_mul, map_mul, map_intCast]
    ring
  have hvec : (integralBasis (Kp p) ∘ e.symm) ᵥ* (Mz.map (Int.castRingHom ℚ)).map
      (algebraMap ℚ (Kp p)) = ![1, om p] := by
    funext j
    have hj : (![1, om p] : Fin 2 → Kp p) j =
        algebraMap (𝓞 (Kp p)) (Kp p) ((![1, w p] : Fin 2 → 𝓞 (Kp p)) j) := by
      fin_cases j
      · simp
      · simp; rfl
    rw [hj, ← hsum]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Int.coe_castRingHom, Mz]
    rfl
  have hdet := Algebra.discr_of_matrix_vecMul (integralBasis (Kp p) ∘ e.symm)
    (Mz.map (Int.castRingHom ℚ))
  rw [hvec, discr_om, Algebra.discr_reindex, ← coe_discr, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at hdet
  have hz : (1 : ℤ) - 4 * p = Mz.det ^ 2 * discr (Kp p) := by
    apply Int.cast_injective (α := ℚ)
    simp only [Int.coe_castRingHom] at hdet
    have e1 : (((1 : ℤ) - 4 * (p : ℤ) : ℤ) : ℚ) = 1 - 4 * (p : ℚ) := by push_cast; ring
    have e2 : ((Mz.det ^ 2 * discr (Kp p) : ℤ) : ℚ) = (Mz.det : ℚ) ^ 2 * (discr (Kp p) : ℚ) := by
      rw [Int.cast_mul, Int.cast_pow]
    exact e1.trans (hdet.trans e2.symm)
  have hD : Mz.det ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    omega
  have h1 : 1 ≤ Mz.det ^ 2 := by
    have := pow_pos (abs_pos.mpr hD) 2
    rw [sq_abs] at this
    omega
  have habs : |(1 : ℤ) - 4 * p| = Mz.det ^ 2 * |discr (Kp p)| := by
    rw [congrArg abs hz, abs_mul, abs_of_nonneg (sq_nonneg _)]
  rw [abs_of_neg (by omega)] at habs
  nlinarith [abs_nonneg (discr (Kp p))]

lemma mink_lt (hp : 41 < p) :
    (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces (Kp p) *
      (((Module.finrank ℚ (Kp p)).factorial : ℝ) / ((Module.finrank ℚ (Kp p) : ℕ) : ℝ) ^
        Module.finrank ℚ (Kp p) * √|((discr (Kp p) : ℤ) : ℝ)|) < p := by
  have hr : InfinitePlace.nrComplexPlaces (Kp p) ≤ 1 := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank (Kp p)
    rw [finrank_Kp] at this
    omega
  rw [finrank_Kp]
  have h1 : 1 ≤ 4 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
  have hpi : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces (Kp p) ≤ 4 / 3 := by
    calc (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces (Kp p) ≤ (4 / Real.pi) ^ 1 :=
          pow_le_pow_right₀ h1 hr
      _ ≤ 4 / 3 := by
          rw [pow_one, div_le_div_iff₀ Real.pi_pos (by norm_num)]; linarith [Real.pi_gt_three]
  have hd := abs_discr_le p (by omega)
  have hdR : |((discr (Kp p) : ℤ) : ℝ)| ≤ 4 * (p : ℝ) - 1 := by
    rw [← Int.cast_abs]; exact_mod_cast hd
  have hs0 := Real.sqrt_nonneg |((discr (Kp p) : ℤ) : ℝ)|
  have hs2 := Real.sq_sqrt (abs_nonneg ((discr (Kp p) : ℤ) : ℝ))
  have hp' : (41 : ℝ) < p := by exact_mod_cast hp
  have hs : √|((discr (Kp p) : ℤ) : ℝ)| < 3 * p / 2 := by nlinarith
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 2 := by
    norm_num [Nat.factorial]
  rw [hfac]
  have key := mul_le_mul_of_nonneg_right hpi
    (by positivity : (0 : ℝ) ≤ 1 / 2 * √|((discr (Kp p) : ℤ) : ℝ)|)
  linarith

lemma prime_principal (hp : p.Prime) (h41 : 41 < p)
    (hrow : ∀ t : ℕ, t + 1 < p → (t * (t + 1) + p).Prime)
    (P : Ideal (𝓞 (Kp p))) (hP : P.IsPrime) (hne : P ≠ ⊥) (hN : Ideal.absNorm P < p) :
    Submodule.IsPrincipal P := by
  classical
  haveI : P.IsMaximal := hP.isMaximal hne
  letI : Field (𝓞 (Kp p) ⧸ P) := Ideal.Quotient.field P
  have hN0 : Ideal.absNorm P ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne
  haveI : Finite (𝓞 (Kp p) ⧸ P) := Nat.finite_of_card_ne_zero
    (by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hN0)
  letI : Fintype (𝓞 (Kp p) ⧸ P) := Fintype.ofFinite _
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 (Kp p) ⧸ P)
  obtain ⟨n, hqp, hcard⟩ := FiniteField.card (𝓞 (Kp p) ⧸ P) q
  have hNc : Ideal.absNorm P = q ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hqle : q ≤ q ^ (n : ℕ) := Nat.le_self_pow n.ne_zero q
  have hq_lt : q < p := by omega
  have hqP : ((q : ℕ) : 𝓞 (Kp p)) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ q
  by_cases hn : (n : ℕ) = 1
  · exfalso
    have hcardq : Fintype.card (𝓞 (Kp p) ⧸ P) = q := by rw [hcard, hn, pow_one]
    haveI : Fact q.Prime := ⟨hqp⟩
    have hbij : Function.Bijective (ZMod.castHom (dvd_refl q) (𝓞 (Kp p) ⧸ P)) := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨(ZMod.castHom (dvd_refl q) (𝓞 (Kp p) ⧸ P)).injective, by rw [ZMod.card, hcardq]⟩
    obtain ⟨z, hz⟩ := hbij.2 (Ideal.Quotient.mk P (w p))
    have ht : ((z.val : ℕ) : 𝓞 (Kp p) ⧸ P) = Ideal.Quotient.mk P (w p) := by
      rw [ZMod.natCast_val, ← hz, ZMod.castHom_apply]
    have hzero : ((z.val : ℕ) : 𝓞 (Kp p) ⧸ P) ^ 2 - ((z.val : ℕ) : 𝓞 (Kp p) ⧸ P) +
        (p : 𝓞 (Kp p) ⧸ P) = 0 := by
      rw [ht, ← map_natCast (Ideal.Quotient.mk P) p, ← map_pow, ← map_sub, ← map_add, w_quad,
        map_zero]
    have hzlt : z.val < q := ZMod.val_lt z
    rcases hzv : z.val with _ | s
    · rw [hzv] at hzero
      simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sub_zero, zero_add] at hzero
      have hqd : q ∣ p := (CharP.cast_eq_zero_iff (𝓞 (Kp p) ⧸ P) q p).mp hzero
      have := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hqd
      omega
    · rw [hzv] at hzero
      have h2 : ((s * (s + 1) + p : ℕ) : 𝓞 (Kp p) ⧸ P) = 0 := by
        push_cast at hzero ⊢
        linear_combination hzero
      have hqd : q ∣ s * (s + 1) + p := (CharP.cast_eq_zero_iff (𝓞 (Kp p) ⧸ P) q _).mp h2
      exact row_contra hrow hqp hq_lt (by omega) hqd
  · have hn2 : q ^ 2 ≤ Ideal.absNorm P := by
      rw [hNc]; exact Nat.pow_le_pow_right hqp.pos (by have := n.pos; omega)
    have hle : Ideal.span {((q : ℕ) : 𝓞 (Kp p))} ≤ P :=
      (Ideal.span_singleton_le_iff_mem P).mpr hqP
    have hnq : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 (Kp p))}) = q ^ 2 := by
      rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 (Kp p))),
        Algebra.norm_algebraMap, RingOfIntegers.rank, finrank_Kp]
      simp [Int.natAbs_pow]
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hnq] at hdvd
    have heqN : Ideal.absNorm P = q ^ 2 :=
      le_antisymm (Nat.le_of_dvd (pow_pos hqp.pos 2) hdvd) hn2
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJ1 : Ideal.absNorm J = 1 := by
      have := congrArg Ideal.absNorm hJ
      rw [map_mul, hnq, heqN] at this
      have hq2 : 0 < q ^ 2 := pow_pos hqp.pos 2
      exact (Nat.eq_of_mul_eq_mul_left hq2 (this.symm.trans (mul_one _).symm))
    rw [Ideal.absNorm_eq_one_iff] at hJ1
    rw [hJ1, Ideal.mul_top] at hJ
    rw [← hJ]
    exact ⟨⟨_, rfl⟩⟩

lemma classNumber_Kp (hp : p.Prime) (h41 : 41 < p)
    (hrow : ∀ t : ℕ, t + 1 < p → (t * (t + 1) + p).Prime) : classNumber (Kp p) = 1 := by
  rw [classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
  intro I hI hN
  apply prime_principal p hp h41 hrow _ hI (nonZeroDivisors.coe_ne_zero I)
  have := lt_of_le_of_lt hN (mink_lt p h41)
  exact_mod_cast this

end

end OMA.H1aux

open OMA.H1aux in
lemma OMA.H1aux.mainH1 : ∀ p : ℕ, p.Prime → 41 < p →
  (∀ t : ℕ, t + 1 < p → (t * (t + 1) + p).Prime) →
    let d : ℤ := 1 - 4 * p
    Squarefree d ∧ ∃ h : Irreducible (X ^ 2 - C (d : ℚ)),
      letI : Fact (Irreducible (X ^ 2 - C (d : ℚ))) := ⟨h⟩
      NumberField.classNumber (AdjoinRoot (X ^ 2 - C (d : ℚ))) = 1 := by
  intro p hp h41 hrow d
  refine ⟨sqfree hp h41 hrow, irred hp, ?_⟩
  letI : Fact (Irreducible (X ^ 2 - C ((((1 : ℤ) - 4 * p : ℤ)) : ℚ))) := ⟨irred hp⟩
  exact classNumber_Kp p hp h41 hrow


theorem OMA.solution : OMA.R_OeisA117531_conjecture_R1.H1 := OMA.H1aux.mainH1
