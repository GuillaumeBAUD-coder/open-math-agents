import OMAStatements.S_oeis_a030433
import Mathlib

open Polynomial

namespace OMA030433

theorem aeval_Q {p : ℕ} {K : Type*} [CommRing K] [Algebra (ZMod p) K] (r : K) :
    aeval r (OMA.S_oeis_a030433.shiftedQuotient p) = ∑ j ∈ Finset.range 5, (r + 1) ^ j := by
  simp [OMA.S_oeis_a030433.shiftedQuotient]

theorem pow5 {K : Type*} [CommRing K] (r : K)
    (h : ∑ j ∈ Finset.range 5, (r + 1) ^ j = 0) : (r + 1) ^ 5 = 1 := by
  have := geom_sum_mul (r + 1) 5
  rw [h, zero_mul] at this
  exact (sub_eq_zero.mp this.symm)

theorem key {K : Type*} [Field K] [Fintype K] (r : K)
    (h : ∑ j ∈ Finset.range 5, (r + 1) ^ j = 0) (hr : r + 1 ≠ 1) :
    5 ∣ Fintype.card K - 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 := pow5 r h
  have hord : orderOf (r + 1) = 5 := orderOf_eq_prime h5 hr
  have hne : r + 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at h5
    exact zero_ne_one h5
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one _ hne)

theorem no_root (p : ℕ) [hp : Fact p.Prime] (h4 : p % 5 = 4) (a : ZMod p) :
    eval a (OMA.S_oeis_a030433.shiftedQuotient p) ≠ 0 := by
  intro h
  have h' : ∑ j ∈ Finset.range 5, (a + 1) ^ j = 0 := by
    simpa [OMA.S_oeis_a030433.shiftedQuotient, eval_finsetSum] using h
  by_cases ha : a + 1 = 1
  · rw [ha] at h'
    simp at h'
    have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h')
    have := Nat.prime_five.eq_one_or_self_of_dvd p hd
    omega
  · have := key a h' ha
    rw [ZMod.card] at this
    omega

theorem quad_imp (p : ℕ) [hp : Fact p.Prime] (f : (ZMod p)[X])
    (hf : f ∈ UniqueFactorizationMonoid.normalizedFactors (OMA.S_oeis_a030433.shiftedQuotient p))
    (hdeg : f.natDegree = 2) : p % 5 = 4 := by
  have hirr : Irreducible f := UniqueFactorizationMonoid.irreducible_of_normalized_factor f hf
  have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hf
  have : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  have : Module.Finite (ZMod p) (AdjoinRoot f) := pb.finite
  have : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod p)
  let _ : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot f) = p ^ 2 := by
    rw [Module.card_fintype pb.basis, ZMod.card, Fintype.card_fin, AdjoinRoot.powerBasis_dim, hdeg]
  have hroot : aeval (AdjoinRoot.root f) f = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hnot : ∀ c : ZMod p, AdjoinRoot.root f ≠ algebraMap (ZMod p) (AdjoinRoot f) c := by
    intro c hc
    rw [hc, aeval_algebraMap_apply_eq_algebraMap_eval] at hroot
    have h2 : f.eval c = 0 :=
      (map_eq_zero_iff _ (algebraMap (ZMod p) (AdjoinRoot f)).injective).mp hroot
    have := degree_eq_one_of_irreducible_of_root hirr (x := c) h2
    rw [degree_eq_natDegree hf0, hdeg] at this
    norm_num at this
  have hQ : ∑ j ∈ Finset.range 5, (AdjoinRoot.root f + 1) ^ j = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    rw [← aeval_Q (p := p), hg, map_mul, hroot, zero_mul]
  have hr1 : AdjoinRoot.root f + 1 ≠ 1 := by
    intro h
    apply hnot 0
    rw [map_zero]
    simpa using h
  have h5 := key _ hQ hr1
  rw [hcard] at h5
  have hmod : p % 5 = 1 ∨ p % 5 = 4 := by
    have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have e : p ^ 2 % 5 = 1 := by omega
    rw [Nat.pow_mod] at e
    have hm : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
    generalize p % 5 = m at e hm ⊢
    interval_cases m <;> simp_all
  rcases hmod with h1 | h4
  · exfalso
    have hd : 5 ∣ Fintype.card (ZMod p)ˣ := by rw [ZMod.card_units]; omega
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 5 hd
    have hprim : IsPrimitiveRoot (u : ZMod p) 5 :=
      IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
    have hprimK := hprim.map_of_injective (algebraMap (ZMod p) (AdjoinRoot f)).injective
    obtain ⟨i, -, hi⟩ := hprimK.eq_pow_of_pow_eq_one (pow5 _ hQ)
    apply hnot ((u : ZMod p) ^ i - 1)
    rw [map_sub, map_pow, hi, map_one]
    ring
  · exact h4

theorem forward (p : ℕ) [hp : Fact p.Prime] (h4 : p % 5 = 4) :
    (OMA.S_oeis_a030433.quadraticFactors p).card = 2 := by
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : IsSquare ((p : ℕ) : ZMod 5) := by
    rw [← ZMod.natCast_mod, h4]
    exact ⟨2, by norm_num⟩
  have hsq : IsSquare ((5 : ℕ) : ZMod p) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2).mp h5
  obtain ⟨s, hs⟩ := hsq
  have two : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.prime_two.eq_one_or_self_of_dvd p hd
    omega
  obtain ⟨α, hα⟩ : ∃ α : ZMod p, α ^ 2 = α + 1 := by
    refine ⟨(1 + s) * 2⁻¹, ?_⟩
    push_cast at hs
    field_simp
    linear_combination (-1) * hs
  set q1 : (ZMod p)[X] := X ^ 2 + C (2 + α) * X + C (2 + α) with hq1
  set q2 : (ZMod p)[X] := X ^ 2 + C (3 - α) * X + C (3 - α) with hq2
  have hC : (C α) ^ 2 = C α + 1 := by rw [← C_pow, hα, C_add, C_1]
  have hfac : OMA.S_oeis_a030433.shiftedQuotient p = q1 * q2 := by
    simp only [OMA.S_oeis_a030433.shiftedQuotient, Finset.sum_range_succ, Finset.sum_range_zero,
      hq1, hq2]
    rw [show C (2 + α) = 2 + C α by rw [C_add, map_ofNat], show C (3 - α) = 3 - C α by rw [C_sub, map_ofNat]]
    linear_combination ((X + 1) ^ 2) * hC
  have m1 : q1.Monic := by rw [hq1]; monicity!
  have m2 : q2.Monic := by rw [hq2]; monicity!
  have d1 : q1.natDegree = 2 := by rw [hq1]; compute_degree!
  have d2 : q2.natDegree = 2 := by rw [hq2]; compute_degree!
  have noroot : ∀ (q r : (ZMod p)[X]), OMA.S_oeis_a030433.shiftedQuotient p = q * r →
      q.Monic → q.natDegree = 2 → Irreducible q := by
    intro q r hqr hm hd
    rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    rw [mem_roots hm.ne_zero, IsRoot.def] at hx
    apply no_root p h4 x
    rw [hqr, eval_mul, hx, zero_mul]
  have i1 : Irreducible q1 := noroot q1 q2 hfac m1 d1
  have i2 : Irreducible q2 := noroot q2 q1 (by rw [hfac, mul_comm]) m2 d2
  have hne : q1 ≠ q2 := by
    intro h
    have hc := congrArg (fun q => q.coeff 0) h
    simp only [hq1, hq2, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X_zero, coeff_C_zero] at hc
    have h2a : 2 * α = 1 := by linear_combination hc
    have h50 : (5 : ZMod p) = 0 := by linear_combination (-4) * hα + (2 * α - 1) * h2a
    have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h50)
    have := Nat.prime_five.eq_one_or_self_of_dvd p hd
    omega
  have hnf : UniqueFactorizationMonoid.normalizedFactors (OMA.S_oeis_a030433.shiftedQuotient p) =
      {q1} + {q2} := by
    rw [hfac, UniqueFactorizationMonoid.normalizedFactors_mul i1.ne_zero i2.ne_zero,
      UniqueFactorizationMonoid.normalizedFactors_irreducible i1,
      UniqueFactorizationMonoid.normalizedFactors_irreducible i2,
      m1.normalize_eq_self, m2.normalize_eq_self]
  unfold OMA.S_oeis_a030433.quadraticFactors
  rw [hnf]
  simp only [Multiset.singleton_add, Multiset.toFinset_cons,
    Multiset.toFinset_singleton]
  rw [Finset.filter_true_of_mem, Finset.card_pair hne]
  intro x hx
  rcases Finset.mem_insert.mp hx with h | h
  · rw [h]; exact d1
  · rw [Finset.mem_singleton.mp h]; exact d2

end OMA030433

theorem OMA.solution : type_of% @OMA.S_oeis_a030433.main := by
  intro p hp
  constructor
  · intro h
    exact OMA030433.forward p (by omega)
  · intro hc
    have hpos : 0 < (OMA.S_oeis_a030433.quadraticFactors p).card := by omega
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
    unfold OMA.S_oeis_a030433.quadraticFactors at hf
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hf
    have := OMA030433.quad_imp p f hf.1 hf.2
    rcases hp.out.eq_two_or_odd with h | h <;> omega
