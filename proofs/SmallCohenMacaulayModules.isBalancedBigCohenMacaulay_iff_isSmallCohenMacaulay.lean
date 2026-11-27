import FormalConjectures.Wikipedia.SmallCohenMacaulayModules
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular

-- Problem: The small Cohen-Macaulay modules conjecture
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SmallCohenMacaulayModules.lean:140 (declaration SmallCohenMacaulayModules.isBalancedBigCohenMacaulay_iff_isSmallCohenMacaulay)
-- Credit: @Jakeybakeypants (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! # Balanced big Cohen-Macaulay vs small Cohen-Macaulay modules -/

namespace OMA.SmallCM

open IsLocalRing Module RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise

lemma exists_isSystemOfParameters (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ∃ rs : List R, IsSystemOfParameters R rs := by
  obtain ⟨s, hs_min, hs_card⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  refine ⟨s.toList, ?_⟩
  have hof : Ideal.ofList s.toList = Ideal.span (s : Set R) :=
    congrArg Ideal.span (Set.ext fun _ => Finset.mem_toList)
  refine ⟨?_, ?_⟩
  · rw [← maximalIdeal_height_eq_ringKrullDim, ← hs_card, Finset.length_toList]
    rfl
  · rw [hof]
    refine le_antisymm
      ((maximalIdeal.isMaximal R).isPrime.isRadical.radical_le_iff.mpr hs_min.le) ?_
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    intro q ⟨hle, hq⟩
    exact hs_min.2 ⟨hq, hle⟩ (le_maximalIdeal hq.ne_top)

lemma ringKrullDim_quotient_succ_le_of_lt {R : Type*} [CommRing R] {p q : Ideal R}
    [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) q) := ⟨⟨⟨q, inferInstance⟩, by simp⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) p) := ⟨⟨⟨p, inferInstance⟩, by simp⟩⟩
  rw [ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  let p₀ : PrimeSpectrum.zeroLocus (R := R) p := ⟨⟨p, inferInstance⟩, by simp⟩
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) p) :=
    l.map (fun x => ⟨x.1, hpq.le.trans x.2⟩) (fun _ _ h => h)
  have hlt : p₀ < l'.head := hpq.trans_le l.head.2
  have hlen : l.length = l'.length := rfl
  rw [hlen]
  exact le_trans (by simp)
    (le_iSup (fun s : LTSeries (PrimeSpectrum.zeroLocus (R := R) p) => (s.length : ℕ∞))
      (l'.cons p₀ hlt))

lemma length_le_ringKrullDim_quotient_of_isAssociatedPrime
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hreg : IsRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {p : Ideal R} (hp : IsAssociatedPrime p M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction rs generalizing M p with
  | nil =>
    have := hp.isPrime
    cases h : ringKrullDim (R ⧸ p) with
    | bot =>
      exfalso
      rw [ringKrullDim, Order.krullDim_eq_bot_iff, isEmpty_iff] at h
      have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr Ideal.IsPrime.ne_top'
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (R ⧸ p)
      exact h ⟨m, hm.isPrime⟩
    | coe d => exact WithBot.coe_le_coe.mpr zero_le
  | cons x rs' ih =>
    rw [isRegular_cons_iff] at hreg
    obtain ⟨hxreg, hreg'⟩ := hreg
    have hxmem : x ∈ maximalIdeal R := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ rs', r ∈ maximalIdeal R :=
      fun r hr => hmem r (List.mem_cons_of_mem x hr)
    obtain ⟨hp_prime, m, hm_eq⟩ := (isAssociatedPrime_iff).mp hp
    have hm_ne : m ≠ 0 := by
      intro h0
      apply hp_prime.ne_top
      rw [hm_eq, h0, Submodule.colon_singleton_zero]
    have hxp : x ∉ p := by
      intro hx
      have hxm : x • m = 0 := by
        rw [hm_eq, Submodule.mem_colon_singleton, Submodule.mem_bot] at hx
        exact hx
      exact hm_ne (hxreg (hxm.trans (smul_zero x).symm))
    let N : Submodule R M :=
      { carrier := {y : M | ∀ a ∈ p, a • y = 0}
        add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
        zero_mem' := fun _ _ => smul_zero _
        smul_mem' := fun c y hy a ha => by rw [smul_comm, hy a ha, smul_zero] }
    have : Module.Finite R N := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
    have hm_mem : m ∈ N := fun a ha => by
      rw [hm_eq, Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
      exact ha
    have : Nontrivial N := ⟨⟨⟨m, hm_mem⟩, 0, fun h => hm_ne (congrArg Subtype.val h)⟩⟩
    have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N hxmem
    let f : QuotSMulTop x N →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x N.subtype
    have hf_inj : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      induction u using Submodule.Quotient.induction_on with | _ y =>
      rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hu
      obtain ⟨z, -, hz⟩ := hu
      have hzN : z ∈ N := by
        intro a ha
        apply hxreg
        dsimp only
        rw [smul_comm, hz, Submodule.coe_subtype, y.2 a ha, smul_zero]
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨z, hzN⟩, trivial, Subtype.ext hz⟩
    obtain ⟨q, hq⟩ := associatedPrimes.nonempty R (QuotSMulTop x N)
    have hqM : IsAssociatedPrime q (QuotSMulTop x M) := hq.map_of_injective f hf_inj
    have hpq_le : p ≤ q := by
      intro a ha
      apply hq.annihilator_le
      rw [Submodule.mem_annihilator]
      intro u
      induction u using Submodule.Quotient.induction_on with | _ y =>
      intro _
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have : a • y = 0 := Subtype.ext (y.2 a ha)
      rw [this]
      exact Submodule.zero_mem _
    have hxq : x ∈ q := by
      apply hq.annihilator_le
      rw [Submodule.mem_annihilator]
      intro u
      induction u using Submodule.Quotient.induction_on with | _ y =>
      intro _
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_pointwise_smul y x ⊤ trivial
    have hpq : p < q := lt_of_le_of_ne hpq_le (fun h => hxp (h ▸ hxq))
    have ih_res := ih hreg' hmem' hqM
    have : p.IsPrime := hp_prime
    have : q.IsPrime := hq.isPrime
    have hdim := ringKrullDim_quotient_succ_le_of_lt hpq
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    exact (add_le_add ih_res le_rfl).trans hdim

set_option maxHeartbeats 800000 in
lemma exists_isRegular_quotSMulTop_cat
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Small.{w} R]
    (M : ModuleCat.{w} R) [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) {m : ℕ}
    (hdep : ∃ rs : List R, rs.length = m + 1 ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M rs) :
    ∃ rs' : List R, rs'.length = m ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular (QuotSMulTop x M) rs' := by
  have : Nontrivial M := by
    obtain ⟨rs, -, -, hreg⟩ := hdep
    exact hreg.nontrivial
  have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have hsmul_lt : maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _)).symm
  have hsmul_lt' : maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _)).symm
  let N : ModuleCat.{w} R := ModuleCat.of R (Shrink.{w} (R ⧸ maximalIdeal R))
  have h_tfae1 := (ModuleCat.exists_isRegular_tfae (maximalIdeal R) (m + 1) M hsmul_lt).out 3 1
  have h_ext : ∀ i < m + 1, Subsingleton (Ext N M i) := h_tfae1.mp hdep
  have h_ext' : ∀ i < m, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' N hxreg.smulShortComplex_shortExact) i (i + 1) rfl)
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  have h_tfae2 :=
    (ModuleCat.exists_isRegular_tfae (maximalIdeal R) m
      (ModuleCat.of R (QuotSMulTop x M)) hsmul_lt').out 1 3
  exact h_tfae2.mp h_ext'

lemma exists_isRegular_quotSMulTop
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) {m : ℕ}
    (hdep : ∃ rs : List R, rs.length = m + 1 ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M rs) :
    ∃ rs' : List R, rs'.length = m ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular (QuotSMulTop x M) rs' := by
  have : Small.{max u v} R := ⟨⟨ULift.{max u v, u} R, ⟨Equiv.ulift.symm⟩⟩⟩
  let e : ULift.{u} M ≃ₗ[R] M := ULift.moduleEquiv
  have : Module.Finite R (ULift.{u} M) := Module.Finite.equiv e.symm
  obtain ⟨rs, hrs_len, hrs_mem, hrs_reg⟩ := hdep
  have hrs_reg_u : IsRegular (ULift.{u} M) rs := (e.symm.isRegular_congr rs).mp hrs_reg
  have hxreg_u : IsSMulRegular (ULift.{u} M) x := (e.symm.isSMulRegular_congr x).mp hxreg
  obtain ⟨rs', hrs'_len, hrs'_mem, hrs'_reg⟩ :=
    exists_isRegular_quotSMulTop_cat (ModuleCat.of R (ULift.{u} M)) hx hxreg_u
      ⟨rs, hrs_len, hrs_mem, hrs_reg_u⟩
  exact ⟨rs', hrs'_len, hrs'_mem, ((QuotSMulTop.congr x e).isRegular_congr rs').mp hrs'_reg⟩

lemma supportDim_le_supportDim_quot_ofList_add_length
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ts : List R) (hts : ∀ t ∈ ts, t ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (M ⧸ (Ideal.ofList ts • (⊤ : Submodule R M))) + ts.length := by
  induction ts generalizing M with
  | nil =>
    rw [Ideal.ofList_nil, Submodule.bot_smul, List.length_nil, Nat.cast_zero, add_zero]
    exact (supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)).symm.le
  | cons y ts' ih =>
    have hy : y ∈ maximalIdeal R := hts y List.mem_cons_self
    have hts' : ∀ t ∈ ts', t ∈ maximalIdeal R := fun t ht => hts t (List.mem_cons_of_mem y ht)
    have h1 := supportDim_le_supportDim_quotSMulTop_succ (M := M) hy
    have h2 := ih (M := QuotSMulTop y M) hts'
    have h3 : supportDim R (M ⧸ (Ideal.ofList (y :: ts') • (⊤ : Submodule R M))) =
        supportDim R (QuotSMulTop y M ⧸ (Ideal.ofList ts' • (⊤ : Submodule R (QuotSMulTop y M)))) :=
      supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y ts')
    rw [h3]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    calc supportDim R M
        ≤ supportDim R (QuotSMulTop y M) + 1 := h1
      _ ≤ (supportDim R (QuotSMulTop y M ⧸ (Ideal.ofList ts' • (⊤ : Submodule R (QuotSMulTop y M))))
            + ts'.length) + 1 := add_le_add h2 le_rfl
      _ = supportDim R (QuotSMulTop y M ⧸ (Ideal.ofList ts' • (⊤ : Submodule R (QuotSMulTop y M))))
            + (ts'.length + 1) := add_assoc _ _ _

lemma isRegular_of_supportDim_quot_add_length_le
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ss : List R) (hss : ∀ s ∈ ss, s ∈ maximalIdeal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (n : ℕ)
    (hdep : ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M rs)
    (hquot : supportDim R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M))) + ss.length ≤ n) :
    IsRegular M ss := by
  induction ss generalizing M n with
  | nil =>
    obtain ⟨rs, -, -, hreg⟩ := hdep
    have := hreg.nontrivial
    exact IsRegular.nil R M
  | cons x ss' ih =>
    have hx : x ∈ maximalIdeal R := hss x List.mem_cons_self
    have hss' : ∀ s ∈ ss', s ∈ maximalIdeal R := fun s hs => hss s (List.mem_cons_of_mem x hs)
    have hM_nt : Nontrivial M := by
      obtain ⟨rs, -, -, hreg⟩ := hdep
      exact hreg.nontrivial
    have := hM_nt
    have hQ_nt : Nontrivial (M ⧸ (Ideal.ofList (x :: ss') • (⊤ : Submodule R M))) := by
      rw [Submodule.Quotient.nontrivial_iff]
      refine Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_)
      exact (Ideal.span_le.mpr hss).trans (maximalIdeal_le_jacobson _)
    have hne_bot :
        supportDim R (M ⧸ (Ideal.ofList (x :: ss') • (⊤ : Submodule R M))) ≠ ⊥ :=
      (supportDim_ne_bot_iff_nontrivial R _).mpr hQ_nt
    have hEqQ :
        supportDim R (M ⧸ (Ideal.ofList (x :: ss') • (⊤ : Submodule R M))) =
          supportDim R (QuotSMulTop x M ⧸ (Ideal.ofList ss' • (⊤ : Submodule R (QuotSMulTop x M)))) :=
      supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x ss')
    cases n with
    | zero =>
      exfalso
      cases hval : supportDim R (M ⧸ (Ideal.ofList (x :: ss') • (⊤ : Submodule R M))) with
      | bot => exact hne_bot hval
      | coe a =>
        rw [hval] at hquot
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hquot
        have h' : a + (ss'.length + 1 : ℕ∞) ≤ 0 := WithBot.coe_le_coe.mp hquot
        have : (ss'.length + 1 : ℕ∞) ≤ 0 := le_trans le_add_self h'
        have : ss'.length + 1 ≤ 0 := by exact_mod_cast this
        omega
    | succ m =>
      have hquot' :
          supportDim R (QuotSMulTop x M ⧸ (Ideal.ofList ss' • (⊤ : Submodule R (QuotSMulTop x M)))) +
            ss'.length ≤ m := by
        cases hval : supportDim R (M ⧸ (Ideal.ofList (x :: ss') • (⊤ : Submodule R M))) with
        | bot => exact False.elim (hne_bot hval)
        | coe a =>
          rw [← hEqQ, hval]
          rw [hval] at hquot
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hquot ⊢
          have hq1 : ((a + (ss'.length : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤
              ((m + 1 : ℕ∞) : WithBot ℕ∞) := by
            simpa only [WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_one, add_assoc] using hquot
          rw [WithBot.coe_le_coe] at hq1
          have hq2 := (ENat.add_le_add_iff_right (by decide : (1 : ℕ∞) ≠ ⊤)).mp hq1
          simpa only [WithBot.coe_add, WithBot.coe_natCast] using WithBot.coe_le_coe.mpr hq2
      have hdim' : supportDim R (QuotSMulTop x M) ≤ m :=
        (supportDim_le_supportDim_quot_ofList_add_length (M := QuotSMulTop x M) ss' hss').trans hquot'
      have hxreg : IsSMulRegular M x := by
        by_contra hnot
        have hxmem_union : x ∈ ⋃ p ∈ associatedPrimes R M, p := by
          rw [biUnion_associatedPrimes_eq_compl_regular R M]
          exact hnot
        rw [Set.mem_iUnion₂] at hxmem_union
        obtain ⟨p, hp, hxp⟩ := hxmem_union
        obtain ⟨rs, hrs_len, hrs_mem, hrs_reg⟩ := hdep
        have hlen_le : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
          rw [← hrs_len]
          exact length_le_ringKrullDim_quotient_of_isAssociatedPrime rs hrs_reg hrs_mem hp
        have hsub : PrimeSpectrum.zeroLocus (R := R) p ⊆ support R (QuotSMulTop x M) := by
          intro q hq
          rw [support_quotSMulTop, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
            Set.singleton_subset_iff]
          have hle : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ≤ q := hq
          refine ⟨mem_support_mono hle ?_, hq hxp⟩
          exact mem_support_iff_of_finite.mpr
            ((Submodule.annihilator_top (R := R) (M := M)) ▸ hp.annihilator_le)
        have hkrull_le : ringKrullDim (R ⧸ p) ≤ supportDim R (QuotSMulTop x M) := by
          rw [ringKrullDim_quotient, supportDim]
          exact Order.krullDim_le_of_strictMono (fun a => ⟨a.1, hsub a.2⟩) (fun _ _ h => h)
        have hbad : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) :=
          hlen_le.trans (hkrull_le.trans hdim')
        have hbad' : m + 1 ≤ m := by exact_mod_cast hbad
        omega
      have hdep' := exists_isRegular_quotSMulTop hx hxreg hdep
      exact IsRegular.cons hxreg (ih hss' m hdep' hquot')

lemma supportDim_quot_ofList_le_zero_of_isSystemOfParameters
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {ss : List R} (hss : IsSystemOfParameters R ss) :
    supportDim R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M))) ≤ 0 := by
  have hsub : Subsingleton (support R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M)))) := by
    refine ⟨fun p q => ?_⟩
    have hp_ann : annihilator R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M))) ≤ p.1.asIdeal :=
      mem_support_iff_of_finite.mp p.2
    have hq_ann : annihilator R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M))) ≤ q.1.asIdeal :=
      mem_support_iff_of_finite.mp q.2
    have hof_le : Ideal.ofList ss ≤ annihilator R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M))) := by
      intro r hr
      rw [mem_annihilator]
      intro u
      induction u using Submodule.Quotient.induction_on with | _ y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have : r • (⊤ : Submodule R M) ≤ Ideal.ofList ss • (⊤ : Submodule R M) := by
        rw [← Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mono_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr))
      exact this (Submodule.smul_mem_pointwise_smul y r ⊤ trivial)
    have hp_rad : maximalIdeal R ≤ p.1.asIdeal := by
      rw [← hss.radical_eq]
      exact p.1.isPrime.isRadical.radical_le_iff.mpr (hof_le.trans hp_ann)
    have hq_rad : maximalIdeal R ≤ q.1.asIdeal := by
      rw [← hss.radical_eq]
      exact q.1.isPrime.isRadical.radical_le_iff.mpr (hof_le.trans hq_ann)
    have hp_eq : p.1.asIdeal = maximalIdeal R :=
      le_antisymm (le_maximalIdeal p.1.isPrime.ne_top) hp_rad
    have hq_eq : q.1.asIdeal = maximalIdeal R :=
      le_antisymm (le_maximalIdeal q.1.isPrime.ne_top) hq_rad
    exact Subtype.ext (PrimeSpectrum.ext (hp_eq.trans hq_eq.symm))
  rw [supportDim]
  cases isEmpty_or_nonempty (support R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M)))) with
  | inl h =>
    rw [Order.krullDim_eq_bot_iff.mpr h]
    exact bot_le
  | inr h =>
    rw [@Order.krullDim_eq_iSup_length _ _ h, ← WithBot.coe_zero, WithBot.coe_le_coe]
    refine iSup_le fun l => ?_
    have h0 : l.length = 0 := by
      by_contra hne
      have hpos : 0 < l.length := Nat.pos_of_ne_zero hne
      let i0 : Fin (l.length + 1) := ⟨0, Nat.zero_lt_succ l.length⟩
      let i1 : Fin (l.length + 1) := ⟨1, Nat.succ_lt_succ hpos⟩
      have hlt : l i0 < l i1 := l.strictMono (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
      rw [Subsingleton.elim (l i0) (l i1)] at hlt
      exact lt_irrefl _ hlt
    simp [h0]

end OMA.SmallCM

theorem OMA.solution :
    type_of% @SmallCohenMacaulayModules.isBalancedBigCohenMacaulay_iff_isSmallCohenMacaulay := by
  intro R _ _ _ M _ _ _
  constructor
  · intro hM
    obtain ⟨rs, hrs⟩ := OMA.SmallCM.exists_isSystemOfParameters R
    exact ⟨inferInstance, rs, hrs, hM.isRegular rs hrs⟩
  · intro hM
    obtain ⟨rs₀, hrs₀, hreg₀⟩ := hM.exists_isRegular
    refine ⟨Module.smul_top_ne_top_of_isRegular hrs₀ hreg₀, fun ss hss => ?_⟩
    have hlen : ss.length = rs₀.length := by
      have h := hss.length_eq.trans hrs₀.length_eq.symm
      exact_mod_cast h
    have hq0 := OMA.SmallCM.supportDim_quot_ofList_le_zero_of_isSystemOfParameters (M := M) hss
    refine OMA.SmallCM.isRegular_of_supportDim_quot_add_length_le ss
      (fun _ hr => hss.mem_maximalIdeal hr) rs₀.length
      ⟨rs₀, rfl, fun _ hr => hrs₀.mem_maximalIdeal hr, hreg₀⟩ ?_
    calc Module.supportDim R (M ⧸ (Ideal.ofList ss • (⊤ : Submodule R M))) + (ss.length : WithBot ℕ∞)
        ≤ 0 + (rs₀.length : WithBot ℕ∞) := by
          rw [hlen]
          exact add_le_add hq0 le_rfl
      _ = (rs₀.length : WithBot ℕ∞) := zero_add _
