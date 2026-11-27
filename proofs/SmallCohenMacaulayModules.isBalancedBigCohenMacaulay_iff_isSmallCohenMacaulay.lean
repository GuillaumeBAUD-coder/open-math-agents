import FormalConjectures.Wikipedia.SmallCohenMacaulayModules
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! The equivalence of small and balanced big Cohen–Macaulay modules. -/

open IsLocalRing RingTheory.Sequence

namespace CohenMacaulayEquivalence

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

omit [IsNoetherianRing R] in
theorem radical_eq_of_maximalIdeal_mem_minimalPrimes
    {I : Ideal R} (h : maximalIdeal R ∈ I.minimalPrimes) :
    I.radical = maximalIdeal R := by
  rw [← Ideal.sInf_minimalPrimes]
  have heq : I.minimalPrimes = {maximalIdeal R} := by
    ext p
    constructor
    · intro hp
      have : p.IsPrime := hp.1.1
      exact Set.mem_singleton_iff.mpr
        (le_antisymm (le_maximalIdeal_of_isPrime p)
          (h.2 hp.1 (le_maximalIdeal_of_isPrime p)))
    · intro hp
      rwa [Set.mem_singleton_iff.mp hp]
  simp [heq]

theorem exists_systemOfParameters : ∃ xs : List R, IsSystemOfParameters R xs := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  refine ⟨s.toList, ⟨?_, ?_⟩⟩
  · rw [Finset.length_toList, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hcard
  · apply radical_eq_of_maximalIdeal_mem_minimalPrimes
    have hset : {r : R | r ∈ s.toList} = (s : Set R) := by
      ext r
      exact Finset.mem_toList
    unfold Ideal.ofList
    rwa [hset]

theorem balanced_to_small [Module.Finite R M]
    (h : Module.IsBalancedBigCohenMacaulay R M) : Module.IsSmallCohenMacaulay R M := by
  obtain ⟨xs, hxs⟩ := exists_systemOfParameters (R := R)
  exact ⟨inferInstance, xs, hxs, h.isRegular xs hxs⟩

omit [IsNoetherianRing R] in
theorem support_quotient_systemOfParameters [Module.Finite R M] [Nontrivial M]
    {xs : List R} (hxs : IsSystemOfParameters R xs) :
    Module.support R (M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M))) =
      PrimeSpectrum.zeroLocus (↑(maximalIdeal R) : Set R) := by
  rw [Module.support_quotient]
  have heq : PrimeSpectrum.zeroLocus (↑(Ideal.ofList xs) : Set R) =
      PrimeSpectrum.zeroLocus (↑(maximalIdeal R) : Set R) := by
    rw [PrimeSpectrum.zeroLocus_eq_iff, hxs.radical_eq, Ideal.IsPrime.radical inferInstance]
  rw [heq, Set.inter_eq_right]
  rw [PrimeSpectrum.zeroLocus_eq_singleton]
  exact Set.singleton_subset_iff.mpr (IsLocalRing.closedPoint_mem_support R M)

theorem supportDim_eq_ringKrullDim [Module.Finite R M] {xs : List R}
    (hxs : IsSystemOfParameters R xs) (hreg : IsRegular M xs) :
    Module.supportDim R M = ringKrullDim R := by
  have : Nontrivial M := hreg.nontrivial
  have hz : Module.supportDim R (M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M))) = 0 := by
    rw [Module.supportDim, support_quotient_systemOfParameters hxs,
      PrimeSpectrum.zeroLocus_eq_singleton]
    exact Order.krullDim_eq_zero
  have hdim := Module.supportDim_add_length_eq_supportDim_of_isRegular xs hreg
  rw [hz, zero_add] at hdim
  exact hdim.symm.trans hxs.length_eq

theorem regular_cons_of_regular_mod_prefix [Module.Finite R M] [Nontrivial M]
    {xs : List R} {x : R} (hxs : IsWeaklyRegular M xs)
    (hmem : ∀ r ∈ xs, r ∈ maximalIdeal R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular (M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M))) x) :
    IsRegular M (x :: xs) := by
  have hweak : IsWeaklyRegular M (xs ++ [x]) :=
    (isWeaklyRegular_append_iff M xs [x]).mpr ⟨hxs, (isWeaklyRegular_singleton_iff _ x).mpr hreg⟩
  have happ : IsRegular M (xs ++ [x]) := by
    apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M _ hweak
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact hmem r h
    · simpa using (List.mem_singleton.mp h).symm ▸ hx
  exact IsLocalRing.isRegular_of_perm happ (List.perm_append_singleton _ _)

theorem exists_regular_avoiding_primes [Module.Finite R M]
    {S : Set (Ideal R)} (hS : S.Finite) (hprime : ∀ p ∈ S, p.IsPrime)
    (hproper : ∀ p ∈ S, p ≠ maximalIdeal R)
    {a : R} (ha : a ∈ maximalIdeal R) (hareg : IsSMulRegular M a) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x ∧ ∀ p ∈ S, x ∉ p := by
  let T := associatedPrimes R M ∪ S
  have hT : T.Finite := (associatedPrimes.finite R M).union hS
  have hav : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ hT.toFinset, (p : Set R) := by
    refine (Ideal.subset_union_prime ⊥ ⊥ ?_).not.mpr ?_
    · intro p hp _ _
      rw [Set.Finite.mem_toFinset] at hp
      rcases hp with hp | hp
      · exact hp.isPrime
      · exact hprime p hp
    · push Not
      intro p hp hle
      rw [Set.Finite.mem_toFinset] at hp
      rcases hp with hp | hp
      · have hmem : a ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
          Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hle ha⟩⟩
        rw [biUnion_associatedPrimes_eq_compl_regular] at hmem
        exact hmem hareg
      · have : p.IsPrime := hprime p hp
        exact hproper p hp (le_antisymm (le_maximalIdeal_of_isPrime p) hle)
  simp_rw [Set.not_subset, Set.mem_iUnion, not_exists, Set.Finite.mem_toFinset] at hav
  obtain ⟨x, hx, havoid⟩ := hav
  refine ⟨x, hx, ?_, fun p hp => havoid p (Or.inr hp)⟩
  by_contra hreg
  have hm : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hreg
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hm
  obtain ⟨hpa, hxp⟩ := Set.mem_iUnion.mp hp
  exact havoid p (Or.inl hpa) hxp

omit [IsNoetherianRing R] in
theorem maximalIdeal_notMem_minimalPrimes_annihilator_of_supportDim_pos
    [Module.Finite R M] (hd : 0 < Module.supportDim R M) :
    maximalIdeal R ∉ (Module.annihilator R M).minimalPrimes := by
  intro h
  have hrad := radical_eq_of_maximalIdeal_mem_minimalPrimes h
  have heq : PrimeSpectrum.zeroLocus (↑(Module.annihilator R M) : Set R) =
      PrimeSpectrum.zeroLocus (↑(maximalIdeal R) : Set R) := by
    rw [PrimeSpectrum.zeroLocus_eq_iff, hrad, Ideal.IsPrime.radical inferInstance]
  rw [Module.supportDim, Module.support_eq_zeroLocus, heq,
    PrimeSpectrum.zeroLocus_eq_singleton] at hd
  rw [Order.krullDim_eq_zero] at hd
  exact (lt_irrefl (0 : WithBot ℕ∞)) hd

theorem exists_regular_dropping_supportDim [Module.Finite R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hd : 0 < Module.supportDim R N)
    {a : R} (ha : a ∈ maximalIdeal R) (hareg : IsSMulRegular M a) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x ∧
      Module.supportDim R (QuotSMulTop x N) + 1 = Module.supportDim R N := by
  have hn := maximalIdeal_notMem_minimalPrimes_annihilator_of_supportDim_pos hd
  obtain ⟨x, hx, hxreg, havoid⟩ :=
    exists_regular_avoiding_primes (Module.annihilator R N).finite_minimalPrimes_of_isNoetherianRing
      (fun p hp => hp.1.1) (fun p hp heq => hn (heq ▸ hp)) ha hareg
  exact ⟨x, hx, hxreg,
    Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal havoid hx⟩

theorem isSMulRegular_of_quot_supportDim_eq_zero [Module.Finite R M]
    {a g : R} (ha : a ∈ maximalIdeal R) (hareg : IsSMulRegular M a)
    (hd : Module.supportDim R (QuotSMulTop g M) = 0) :
    IsSMulRegular M g := by
  by_contra hgreg
  have hg : g ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hgreg
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hg
  obtain ⟨hpa, hgp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨hpprime, m, hpm⟩ := isAssociatedPrime_iff.mp hpa
  let P : PrimeSpectrum R := ⟨p, hpprime⟩
  have hP : P ∈ Module.support R M := by
    apply Module.mem_support_iff_of_finite.mpr
    change Module.annihilator R M ≤ p
    rw [hpm]
    intro r hr
    simpa using Module.mem_annihilator.mp hr m
  have hPQ : P ∈ Module.support R (QuotSMulTop g M) := by
    rw [Module.support_quotSMulTop]
    exact ⟨hP, Set.singleton_subset_iff.mpr hgp⟩
  rw [support_of_supportDim_eq_zero R _ hd, PrimeSpectrum.zeroLocus_eq_singleton] at hPQ
  have hpeq : p = maximalIdeal R :=
    congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hPQ)
  have hm : a ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
    Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpa, hpeq ▸ ha⟩⟩
  rw [biUnion_associatedPrimes_eq_compl_regular] at hm
  exact hm hareg

omit [IsNoetherianRing R] [IsLocalRing R] in
def quotSingletonEquiv (a : R) :
    (M ⧸ (Ideal.ofList [a] • (⊤ : Submodule R M))) ≃ₗ[R] QuotSMulTop a M :=
  Submodule.quotEquivOfEq _ _ (by rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul])

omit [IsNoetherianRing R] [IsLocalRing R] in
def quotPairEquiv (a b : R) :
    QuotSMulTop b (QuotSMulTop a M) ≃ₗ[R] QuotSMulTop a (QuotSMulTop b M) :=
  ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a [b]).trans
    (quotSingletonEquiv b)).symm.trans
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter M a [b] |>.trans
        (QuotSMulTop.congr a (quotSingletonEquiv b)))

theorem regular_and_exists_regular_on_quot [Module.Finite R M]
    {n : ℕ} {xs : List R} {g : R}
    (hlen : xs.length = n + 1) (hmem : ∀ a ∈ xs, a ∈ maximalIdeal R)
    (hxs : IsRegular M xs) (hg : g ∈ maximalIdeal R)
    (hd : Module.supportDim R (QuotSMulTop g M) = n) :
    IsSMulRegular M g ∧ ∃ ys : List R, ys.length = n ∧
      (∀ a ∈ ys, a ∈ maximalIdeal R) ∧ IsRegular (QuotSMulTop g M) ys := by
  induction n generalizing M xs with
  | zero =>
    have hne : xs ≠ [] := by intro e; simp [e] at hlen
    have ha : IsSMulRegular M (xs.head hne) := by
      cases xs with
      | nil => contradiction
      | cons a as => exact (isRegular_cons_iff M a as).mp hxs |>.1
    have hgreg := isSMulRegular_of_quot_supportDim_eq_zero
      (hmem _ (List.head_mem hne)) ha (by simpa using hd)
    have : Nontrivial M := hxs.nontrivial
    have : Nontrivial (QuotSMulTop g M) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal M hg
    exact ⟨hgreg, [], rfl, by simp, IsRegular.nil R _⟩
  | succ n ih =>
    have hne : xs ≠ [] := by intro e; simp [e] at hlen
    let fs := xs.dropLast
    let a := xs.getLast hne
    have hsplit : fs ++ [a] = xs := List.dropLast_append_getLast hne
    have hfslen : fs.length = n + 1 := by
      have e := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons, List.length_nil] at e
      omega
    have hfs : ∀ r ∈ fs, r ∈ maximalIdeal R := fun r hr =>
      hmem r (hsplit ▸ List.mem_append_left _ hr)
    have ha : a ∈ maximalIdeal R := hmem a (hsplit ▸ List.mem_append_right _ (by simp))
    have hparts := (isWeaklyRegular_append_iff M fs [a]).mp
      (hsplit.symm ▸ hxs.toIsWeaklyRegular)
    have haQ := (isWeaklyRegular_singleton_iff _ a).mp hparts.2
    have hpos : 0 < Module.supportDim R (QuotSMulTop g M) := by
      rw [hd]
      exact_mod_cast (Nat.zero_lt_succ n)
    obtain ⟨h, hh, hhreg, hdrop⟩ := exists_regular_dropping_supportDim hpos ha haQ
    have : Nontrivial M := hxs.nontrivial
    have hreg := regular_cons_of_regular_mod_prefix hparts.1 hfs hh hhreg
    obtain ⟨hhM, hfsQ⟩ := (isRegular_cons_iff M h fs).mp hreg
    have hd' : Module.supportDim R (QuotSMulTop g (QuotSMulTop h M)) = n := by
      rw [Module.supportDim_eq_of_equiv (quotPairEquiv h g)]
      apply ENat.WithBot.add_one_cancel.mp
      rw [hdrop, hd]
      push_cast
      rfl
    obtain ⟨hgQ, ys, hyslen, hysmem, hysreg⟩ := ih hfslen hfs hfsQ hd'
    have : Nontrivial (QuotSMulTop h M) := hfsQ.nontrivial
    have hpair : IsRegular M [h, g] := IsRegular.cons hhM
      (IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ (by simpa using hg)
        ((isWeaklyRegular_singleton_iff _ g).mpr hgQ))
    have hswap := IsLocalRing.isRegular_of_perm hpair (List.Perm.swap g h [])
    obtain ⟨hgM, hhQ⟩ := (isRegular_cons_iff M g [h]).mp hswap
    have hySwap := ((quotPairEquiv h g).isRegular_congr ys).mp hysreg
    exact ⟨hgM, h :: ys, by simp [hyslen], by simpa using And.intro hh hysmem,
      IsRegular.cons ((isRegular_cons_iff _ h []).mp hhQ).1 hySwap⟩

theorem supportDim_le_supportDim_quotient_add_length [Module.Finite R M]
    (ys : List R) (hmem : ∀ a ∈ ys, a ∈ maximalIdeal R) :
    Module.supportDim R M ≤
      Module.supportDim R (M ⧸ (Ideal.ofList ys • (⊤ : Submodule R M))) + ys.length := by
  induction ys generalizing M with
  | nil =>
    rw [Ideal.ofList_nil, Submodule.bot_smul]
    rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)]
    simp
  | cons g ys ih =>
    have h1 := Module.supportDim_le_supportDim_quotSMulTop_succ (M := M)
      (hmem g (by simp))
    have h2 := ih (M := QuotSMulTop g M) (fun a ha => hmem a (by simp [ha]))
    rw [Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M g ys)]
    have h3 := add_le_add_left h2 (1 : WithBot ℕ∞)
    exact h1.trans (by simpa [List.length_cons, Nat.cast_add, add_assoc] using h3)

theorem regular_of_full_length_and_quot_supportDim_zero [Module.Finite R M]
    {ys xs : List R} (hmem : ∀ a ∈ ys, a ∈ maximalIdeal R)
    (hxmem : ∀ a ∈ xs, a ∈ maximalIdeal R) (hx : IsRegular M xs)
    (hlen : xs.length = ys.length) (hd : Module.supportDim R M = ys.length)
    (hz : Module.supportDim R (M ⧸ (Ideal.ofList ys • (⊤ : Submodule R M))) = 0) :
    IsRegular M ys := by
  induction ys generalizing M xs with
  | nil =>
    have : Nontrivial M := hx.nontrivial
    exact IsRegular.nil R M
  | cons g ys ih =>
    have hg : g ∈ maximalIdeal R := hmem g (by simp)
    have hysmem : ∀ a ∈ ys, a ∈ maximalIdeal R := fun a ha => hmem a (by simp [ha])
    rw [Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M g ys)] at hz
    have hle := supportDim_le_supportDim_quotient_add_length (M := QuotSMulTop g M) ys hysmem
    rw [hz, zero_add] at hle
    have hge := Module.supportDim_le_supportDim_quotSMulTop_succ (M := M) hg
    rw [hd, List.length_cons, Nat.cast_add, Nat.cast_one] at hge
    have hd' := le_antisymm hle (ENat.WithBot.add_le_add_one_right_iff.mp hge)
    obtain ⟨hgreg, fs, hfslen, hfsMem, hfsReg⟩ :=
      regular_and_exists_regular_on_quot hlen hxmem hx hg hd'
    exact IsRegular.cons hgreg (ih hysmem hfsMem hfsReg hfslen hd' hz)

end CohenMacaulayEquivalence

-- Credit: @kenharimadesu
theorem OMA.solution : type_of% @SmallCohenMacaulayModules.isBalancedBigCohenMacaulay_iff_isSmallCohenMacaulay := by
  intro R _ _ _ M _ _ _
  refine ⟨CohenMacaulayEquivalence.balanced_to_small, ?_⟩
  intro h
  obtain ⟨xs, hxs, hxreg⟩ := h.exists_isRegular
  refine ⟨Module.smul_top_ne_top_of_isRegular hxs hxreg, ?_⟩
  intro ys hys
  have hlen : xs.length = ys.length := by
    exact_mod_cast hxs.length_eq.trans hys.length_eq.symm
  have hd := (CohenMacaulayEquivalence.supportDim_eq_ringKrullDim hxs hxreg).trans
    hys.length_eq.symm
  have : Nontrivial M := hxreg.nontrivial
  have hz : Module.supportDim R (M ⧸ (Ideal.ofList ys • (⊤ : Submodule R M))) = 0 := by
    rw [Module.supportDim, CohenMacaulayEquivalence.support_quotient_systemOfParameters hys,
      PrimeSpectrum.zeroLocus_eq_singleton]
    exact Order.krullDim_eq_zero
  exact CohenMacaulayEquivalence.regular_of_full_length_and_quot_supportDim_zero
    (fun _ ha => hys.mem_maximalIdeal ha) (fun _ ha => hxs.mem_maximalIdeal ha) hxreg hlen hd hz
