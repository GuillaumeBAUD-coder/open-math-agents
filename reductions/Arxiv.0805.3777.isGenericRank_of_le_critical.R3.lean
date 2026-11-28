import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Credit: @mattdorman
/-! # Endpoint ranks for Friedland’s critical-format conjecture

For each pair of leading dimensions and each predicted rank, the third
dimensions with that prediction form an integer interval. Projecting a
dense open set of complex tensors down from the largest admissible dimension
preserves the upper rank bound; the parameter count recovers equality.

The first step isolates the three-slice family with third side b+2. For
the remaining three-slice endpoints, write the rank as 2b−h. Every fixed
h≥3 leaves only finitely many middle widths: b<3h(h−1)−h+1. At b≥h²
only two possible endpoints extend past the constructed tangent. Fourier
commutators and perturbations treat every residue in this construction.
Translated Cauchy measurements cover all multiples of h and further widths. In every first
dimension, a decomposition into two-slice blocks rules out three arithmetic
classes from the residual cases. The top two ranks in the critical range
are already attained. The equivalence below preserves the odd-square
exception and asks for actual dense-open generic ranks in all three steps.

[Friedland, *On the generic and typical ranks of 3-tensors*, Conjecture 5.1](https://arxiv.org/abs/0805.3777)
provides the problem. [Abo, Ottaviani and Peterson, §3](https://arxiv.org/abs/math/0607191)
provide related subspace specializations. The generic-rank bounds and
boundary constructions reuse the formal proofs in Open Math Agents
[PR 3300](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3300),
[PR 6443](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6443)
and [PR 12200](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12200).
The pencil criterion and the initial cyclic constructions are shared with
[PR 17918](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17918).
-/

namespace CriticalReduction

open Arxiv.«0805.3777» Set Filter
open scoped Topology

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

lemma vanishing_on_polynomial_image {I J : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (F : J → MvPolynomial I ℂ) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : I → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P = 0 := by
  classical
  have hn : ¬ AlgebraicIndependent ℂ F := by
    intro h
    have hc := h.cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain] at hc
    have : Fintype.card J ≤ Fintype.card I := by simpa [Cardinal.mk_fintype] using hc
    omega
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  obtain ⟨P, ha, hP⟩ := hn
  refine ⟨P, hP, ?_⟩
  intro x
  rw [← eval_substitution F x P, ha, map_zero]

/-- Agreement with a lower-dimensional chart on a product of infinite subsets
extends to a polynomial identity on the entire parameter space. -/
lemma generic_chart_relation {I J K : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (chart : J → MvPolynomial I ℂ)
    (full : J → MvPolynomial K ℂ)
    (hnormal : ∀ x : K → ℂ, (∀ i, x i ≠ 0) →
      ∃ y : I → ℂ, ∀ j, MvPolynomial.eval x (full j) = MvPolynomial.eval y (chart j)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : K → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (full j)) P = 0 := by
  classical
  obtain ⟨P, hP, hvanish⟩ := vanishing_on_polynomial_image hd chart
  have hpoly : MvPolynomial.aeval full P = 0 := by
    apply MvPolynomial.funext_set (fun _ : K => ({0}ᶜ : Set ℂ))
      (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro x hx
    have hx0 (i : K) : x i ≠ 0 := hx i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := hnormal x hx0
    rw [eval_substitution full x P, funext hy, map_zero]
    exact hvanish y
  refine ⟨P, hP, fun x => ?_⟩
  rw [← eval_substitution full x P, hpoly, map_zero]

lemma zero_is_simple (ds : List ℕ) : Holor.CPRankMax1 (0 : Holor ℂ ds) := by
  induction ds with
  | nil => exact .nil _
  | cons n ds ih =>
    have h := Holor.CPRankMax1.cons (0 : Holor ℂ [n]) (0 : Holor ℂ ds) ih
    have he : Holor.mul (0 : Holor ℂ [n]) (0 : Holor ℂ ds) = (0 : Holor ℂ (n :: ds)) := by
      funext i
      change (0 : ℂ) * 0 = 0
      simp
    rwa [he] at h

lemma decomposition_of_rank_bound {ds : List ℕ} (T : Holor ℂ ds) (r : ℕ) (hr : T.cprank ≤ r) :
    Holor.CPRankMax r T := by
  classical
  have hmin : Holor.CPRankMax T.cprank T :=
    Nat.find_spec (p := fun k => Holor.CPRankMax k T) ⟨ds.prod, Holor.cprankMax_upper_bound T⟩
  induction r, hr using Nat.le_induction with
  | base => exact hmin
  | succ k _ ih => simpa using Holor.CPRankMax.succ k 0 T (zero_is_simple ds) ih

lemma finite_sum_of_simple {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : Holor.CPRankMax r T) :
    ∃ u : Fin r → Holor ℂ ds, (∀ i, Holor.CPRankMax1 (u i)) ∧ ∑ i, u i = T := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ k x y hx hy ih =>
    obtain ⟨u, hu, hs⟩ := ih
    refine ⟨Fin.cons x u, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hu j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hs]

/-- The explicit triple of natural-number indices in a rectangular holor. -/
lemma rectangular_indices (d e f : ℕ) :
    ∃ E : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f, ∀ (i : Fin d) (j : Fin e) (k : Fin f),
      E.symm (i,j,k) = ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ := by
  let mk (z : Fin d × Fin e × Fin f) : HolorIndex [d,e,f] :=
    ⟨[z.1.val,z.2.1.val,z.2.2.val],.cons z.1.isLt (.cons z.2.1.isLt (.cons z.2.2.isLt .nil))⟩
  have hb : Function.Bijective mk := by
    constructor
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
      have he := congrArg Subtype.val h
      simp [mk] at he
      exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))
    · rintro ⟨is,h⟩
      cases h with | cons hi h =>
        cases h with | cons hj h =>
          cases h with | cons hk h =>
            cases h
            exact ⟨(⟨_,hi⟩,⟨_,hj⟩,⟨_,hk⟩),rfl⟩
  exact ⟨(Equiv.ofBijective mk hb).symm, fun _ _ _ => rfl⟩

/-- Absorb the trailing scalar of a simple holor into its last vector. -/
lemma simple_coordinates {d e f : ℕ} {T : Holor ℂ [d,e,f]} (h : Holor.CPRankMax1 T) :
    ∃ (a : Fin d → ℂ) (b : Fin e → ℂ) (c : Fin f → ℂ), ∀ i j k,
      T ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ = a i * b j * c k := by
  cases h with
  | cons a yz hyz =>
    cases hyz with
    | cons b zs hzs =>
      cases hzs with
      | cons c z hz =>
        refine ⟨fun i => a ⟨[i.val],.cons i.isLt .nil⟩,
          fun j => b ⟨[j.val],.cons j.isLt .nil⟩,
          fun k => c ⟨[k.val],.cons k.isLt .nil⟩ * z ⟨[],.nil⟩, ?_⟩
        intro i j k
        change a _ * (b _ * (c _ * z _)) = a _ * b _ * (c _ * z _)
        rw [mul_assoc]
        rfl

/-- A low-rank holor is a coordinatewise sum of products of vector entries. -/
lemma sum_coordinates {d e f : ℕ} (E : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f)
    (hE : ∀ (i : Fin d) (j : Fin e) (k : Fin f),
      E.symm (i,j,k) = ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩)
    (T : Holor ℂ [d,e,f]) (r : ℕ) (hr : T.cprank ≤ r) :
    ∃ (a : Fin r → Fin d → ℂ) (b : Fin r → Fin e → ℂ) (c : Fin r → Fin f → ℂ),
      ∀ q, (∑ t, a t (E q).1 * b t (E q).2.1 * c t (E q).2.2) = T q := by
  classical
  obtain ⟨u,hu,hT⟩ := finite_sum_of_simple (decomposition_of_rank_bound T r hr)
  choose a b c habc using fun t => simple_coordinates (hu t)
  refine ⟨a,b,c,fun q => ?_⟩
  have term (t : Fin r) := habc t (E q).1 (E q).2.1 (E q).2.2
  have at_q := Finset.sum_apply (M := fun _ : HolorIndex [d,e,f] => ℂ) q
    (Finset.univ : Finset (Fin r)) (fun t => fun v => u t v)
  refine (Finset.sum_congr rfl (fun t _ => ?_)).trans (at_q.symm.trans (congrFun hT q))
  simpa only [← hE,Prod.mk.eta,Equiv.symm_apply_apply] using (term t).symm

/-- Scaling the first two factors to first coordinate one removes two
parameters per summand. Their product is absorbed into the third factor. -/
lemma rectangular_polynomial {J : Type} [Fintype J] (d e f r : ℕ)
    (E : J ≃ Fin (d+1) × Fin (e+1) × Fin f) (hd : r*(d+(e+f)) < Fintype.card J) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ (a : Fin r → Fin (d+1) → ℂ) (b : Fin r → Fin (e+1) → ℂ) (c : Fin r → Fin f → ℂ),
        MvPolynomial.eval (fun q => ∑ t, a t (E q).1 * b t (E q).2.1 * c t (E q).2.2) P = 0 := by
  classical
  let Raw := Fin r × (Fin (d+1) ⊕ (Fin (e+1) ⊕ Fin f))
  let Chart := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))
  let raw (q : J) : MvPolynomial Raw ℂ :=
    ∑ t : Fin r, MvPolynomial.X (t,Sum.inl (E q).1) * MvPolynomial.X (t,Sum.inr (Sum.inl (E q).2.1)) *
      MvPolynomial.X (t,Sum.inr (Sum.inr (E q).2.2))
  let chart (q : J) : MvPolynomial Chart ℂ :=
    ∑ t : Fin r, Fin.cases 1 (fun i => MvPolynomial.X (t,Sum.inl i)) (E q).1 *
      Fin.cases 1 (fun j => MvPolynomial.X (t,Sum.inr (Sum.inl j))) (E q).2.1 *
      MvPolynomial.X (t,Sum.inr (Sum.inr (E q).2.2))
  have hnorm (x : Raw → ℂ) (hx : ∀ j, x j ≠ 0) :
      ∃ y : Chart → ℂ, ∀ q, MvPolynomial.eval x (raw q) = MvPolynomial.eval y (chart q) := by
    let y : Chart → ℂ := fun (t,s) => match s with
      | .inl i => x (t,.inl i.succ) / x (t,.inl 0)
      | .inr (.inl j) => x (t,.inr (.inl j.succ)) / x (t,.inr (.inl 0))
      | .inr (.inr k) => x (t,.inr (.inr k)) * x (t,.inl 0) * x (t,.inr (.inl 0))
    refine ⟨y,fun q => ?_⟩
    simp only [raw,chart,map_sum,map_mul,MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro t _
    have ha (i : Fin (d+1)) :
        MvPolynomial.eval y (Fin.cases 1 (fun i : Fin d => MvPolynomial.X (t,Sum.inl i)) i) =
          x (t,.inl i) / x (t,.inl 0) := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hx]
      · simp [y]
    have hb (j : Fin (e+1)) :
        MvPolynomial.eval y (Fin.cases 1 (fun j : Fin e => MvPolynomial.X (t,Sum.inr (Sum.inl j))) j) =
          x (t,.inr (.inl j)) / x (t,.inr (.inl 0)) := by
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [hx]
      · simp [y]
    rw [ha,hb]
    dsimp only [y]
    field_simp [hx]
  have hcard : Fintype.card Chart < Fintype.card J := by
    simpa only [Chart,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin] using hd
  obtain ⟨P,hP,hzero⟩ := generic_chart_relation hcard chart raw hnorm
  refine ⟨P,hP,fun a b c => ?_⟩
  let x : Raw → ℂ := fun (t,s) => match s with
    | .inl i => a t i
    | .inr (.inl j) => b t j
    | .inr (.inr k) => c t k
  simpa only [raw,x,map_sum,map_mul,MvPolynomial.eval_X] using hzero x

/-- For any rectangular format, ranks whose normalized parameter count falls
below the number of tensor entries have nowhere dense closure. -/
theorem lower_of_count (a b c r : ℕ) (hdim : (a+b+c-2)*r < a*b*c) :
    interior (closure {T : Holor ℂ [a,b,c] | T.cprank ≤ r}) = ∅ := by
  classical
  obtain _|d := a
  · simp at hdim
  obtain _|e := b
  · simp at hdim
  obtain ⟨E,hE⟩ := rectangular_indices (d+1) (e+1) c
  let _ : Fintype (HolorIndex [d+1,e+1,c]) := Fintype.ofEquiv _ E.symm
  have hd : r*(d+(e+c)) < Fintype.card (HolorIndex [d+1,e+1,c]) := by
    rw [Fintype.card_congr E]
    have h : d.succ+e.succ+c-2 = d+(e+c) := by omega
    simpa only [Fintype.card_prod,Fintype.card_fin,h,Nat.mul_comm (d+(e+c)) r,Nat.mul_assoc,
      Nat.succ_eq_add_one] using hdim
  obtain ⟨P,hP,hzero⟩ := rectangular_polynomial d e c r E hd
  let Z := {T : Holor ℂ [d+1,e+1,c] | MvPolynomial.eval T P = 0}
  have hclosed : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
  have hsub : {T : Holor ℂ [d+1,e+1,c] | T.cprank ≤ r} ⊆ Z := by
    intro T hT
    obtain ⟨x,y,z,h⟩ := sum_coordinates E hE T r hT
    change MvPolynomial.eval T P = 0
    simpa only [funext h] using hzero x y z
  have hempty : interior Z = ∅ := interior_polynomial_zero_locus P hP
  apply Set.subset_empty_iff.mp
  simpa only [hempty] using interior_mono (closure_minimal hsub hclosed)

end CriticalReduction

namespace CriticalReduction.Dominance

open Set Filter
open scoped Topology Classical

lemma vector_is_simple {n : ℕ} (v : Holor ℂ [n]) : Holor.CPRankMax1 v := by
  let oneScalar : Holor ℂ [] := fun _ => 1
  have he : Holor.mul v oneScalar = v := by
    funext t
    change v t.take * (1 : ℂ) = v t
    rw [mul_one]
    congr 1
    apply Subtype.ext
    exact List.take_of_length_le t.property.length_eq.le
  rw [← he]
  exact Holor.CPRankMax1.cons _ _ (.nil _)

lemma tensor_sum_rank {d e f r : ℕ} (a : Fin r → Holor ℂ [d])
    (b : Fin r → Holor ℂ [e]) (c : Fin r → Holor ℂ [f]) :
    Holor.CPRankMax r (∑ i, Holor.mul (a i) (Holor.mul (b i) (c i))) := by
  have hs (i : Fin r) : Holor.CPRankMax1 (Holor.mul (a i) (Holor.mul (b i) (c i))) :=
    .cons _ _ (.cons _ _ (vector_is_simple (c i)))
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i => Holor.mul (a i) (Holor.mul (b i) (c i))) (fun i _ => Holor.cprankMax_1 (hs i))

/-- A constructible spectral image containing the generic point contains a
principal open neighborhood of it. -/
lemma open_in_spectral_image {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ f : A, f ≠ 0 ∧ ∀ q : PrimeSpectrum A, f ∉ q.asIdeal →
      q ∈ Set.range (PrimeSpectrum.comap φ) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hg : PrimeSpectrum.comap φ w = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hz : z ∈ T.toSet := by rw [hT]; exact ⟨w, hg⟩
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  change z ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    z ∉ PrimeSpectrum.zeroLocus {C.f} at hzC
  have hg0 (i : Fin C.n) : C.g i = 0 := by
    have h := (PrimeSpectrum.mem_zeroLocus z _).mp hzC.1 (Set.mem_range_self i)
    exact (Ideal.mem_bot : C.g i ∈ (⊥ : Ideal A) ↔ _).mp h
  have hf0 : C.f ≠ 0 := by
    intro e
    apply hzC.2
    exact (PrimeSpectrum.mem_zeroLocus z _).mpr (Set.singleton_subset_iff.mpr (e ▸ z.asIdeal.zero_mem))
  refine ⟨C.f, hf0, ?_⟩
  intro q hq
  rw [← hT]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    rintro _ ⟨i, rfl⟩
    rw [hg0 i]
    exact q.asIdeal.zero_mem
  · intro e
    exact hq ((PrimeSpectrum.mem_zeroLocus q _).mp e (Set.mem_singleton _))

/-- Hilbert's Nullstellensatz converts the principal open in the spectral image
to actual complex points in the image of the polynomial map. -/
lemma principal_open_in_image {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧ ∀ y : J → ℂ, MvPolynomial.eval y P ≠ 0 →
      ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (F j) = y j := by
  classical
  let φ : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ := MvPolynomial.aeval F
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial J ℂ))
    have he : φ.toRingHom.comp (algebraMap ℂ (MvPolynomial J ℂ)) =
        algebraMap ℂ (MvPolynomial I ℂ) :=
      RingHom.ext (fun a => φ.commutes a)
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨P, hP, hU⟩ := open_in_spectral_image φ.toRingHom hinj hfp
  refine ⟨P, hP, ?_⟩
  intro y hy
  let m := MvPolynomial.pointToPoint (k := ℂ) y
  have hy' : P ∉ m.asIdeal := fun h => hy ((MvPolynomial.mem_vanishingIdeal_singleton_iff y P).mp h)
  obtain ⟨q, hq⟩ := hU m hy'
  obtain ⟨M, hM, hle⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  intro j
  let v : MvPolynomial J ℂ := MvPolynomial.X j - MvPolynomial.C (y j)
  have hv : v ∈ m.asIdeal := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr
    simp [v]
  have hvq : φ v ∈ q.asIdeal := by
    change v ∈ (PrimeSpectrum.comap φ.toRingHom q).asIdeal
    rwa [hq]
  have hMx := hle hvq
  rw [hx] at hMx
  have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hMx
  simpa [φ, v, MvPolynomial.aeval_eq_eval, sub_eq_zero] using he

lemma dense_image_interior_of_nonempty {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))).Nonempty) :
    Dense (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))) := by
  classical
  let image := Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j))
  have hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ) := by
    apply algebraicIndependent_iff_injective_aeval.mp
    apply algebraicIndependent_iff.mpr
    intro Q hQ
    by_contra hne
    have hs : image ⊆ {y : J → ℂ | MvPolynomial.eval y Q = 0} := by
      rintro _ ⟨x, rfl⟩
      change MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) Q = 0
      rw [← eval_substitution F x Q, hQ, map_zero]
    obtain ⟨y, hy⟩ := h
    have bad := interior_mono hs hy
    rw [interior_polynomial_zero_locus Q hne] at bad
    exact bad
  obtain ⟨P, hP, hsurj⟩ := principal_open_in_image F hinj
  let Z := {y : J → ℂ | MvPolynomial.eval y P = 0}
  have ho : IsOpen Zᶜ := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hd : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (interior_polynomial_zero_locus P hP)
  apply hd.mono
  apply interior_maximal _ ho
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y hy
  exact ⟨x, funext hx⟩

/-- The derivative of each coordinate is the sum of its three factor variations. -/
lemma trilinear_image_has_interior {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (a b c : S → J → I) (base : I → ℂ)
    (hspan : ∀ y : J → ℂ, ∃ z : I → ℂ, ∀ j,
      y j = ∑ t : S, (z (a t j) * (base (b t j) * base (c t j)) +
        base (a t j) * (z (b t j) * base (c t j)) +
        base (a t j) * (base (b t j) * z (c t j)))) :
    (interior (Set.range (fun x : I → ℂ => fun j : J =>
      ∑ t : S, x (a t j) * (x (b t j) * x (c t j))))).Nonempty := by
  classical
  let φ (x : I → ℂ) (j : J) := ∑ t : S, x (a t j) * (x (b t j) * x (c t j))
  let pr (i : I) : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let D : (I → ℂ) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi fun j =>
    ∑ t : S, (base (a t j) • (base (b t j) • pr (c t j) + base (c t j) • pr (b t j)) +
      (base (b t j) * base (c t j)) • pr (a t j))
  have hder : HasStrictFDerivAt φ D base := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    apply HasStrictFDerivAt.fun_sum
    intro t _
    exact (pr (a t j)).hasStrictFDerivAt.fun_mul
      ((pr (b t j)).hasStrictFDerivAt.fun_mul (pr (c t j)).hasStrictFDerivAt)
  have hsurj : Function.Surjective D := by
    intro y
    obtain ⟨z, hz⟩ := hspan y
    refine ⟨z, funext fun j => ?_⟩
    rw [hz j]
    simp only [D, ContinuousLinearMap.pi_apply, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, pr,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hN : Set.range φ ∈ 𝓝 (φ base) := by
    rw [← hder.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)]
    exact Filter.range_mem_map
  exact ⟨φ base, mem_interior_iff_mem_nhds.mpr hN⟩

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

end CriticalReduction.Dominance

namespace CriticalReduction

open Dominance
open Arxiv.«0805.3777»

/-- If the derivative of the sum of simple tensors is surjective at one
configuration, a dense open set has CP rank at most the number of summands. -/
theorem upper_of_witness {a b c r : ℕ} (h :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k = ∑ t, (u t i*(y t j*z t k) +
          x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ U : Set (Holor ℂ [a,b,c]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  classical
  obtain ⟨x,y,z,hspan⟩ := h
  let consIdx (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds := {
    toFun := fun
      | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
      | ⟨[], h⟩ => nomatch h
    invFun := fun q => ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
    left_inv := by
      rintro ⟨l, hl⟩
      cases l with
      | nil => cases hl
      | cons i is => rfl
    right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl }
  let nilIdx : HolorIndex [] ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨[], .nil⟩
    left_inv := by rintro ⟨l, hl⟩; cases hl; rfl
    right_inv := by intro q; cases q; rfl }
  let point (i : Fin a) (j : Fin b) (k : Fin c) : HolorIndex [a,b,c] :=
    ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩
  have triple (q : HolorIndex [a,b,c]) : ∃ i j k, q = point i j k := by
    obtain ⟨⟨i,q⟩,rfl⟩ := (consIdx a [b,c]).symm.surjective q
    obtain ⟨⟨j,q⟩,rfl⟩ := (consIdx b [c]).symm.surjective q
    obtain ⟨⟨k,q⟩,rfl⟩ := (consIdx c []).symm.surjective q
    obtain ⟨⟨⟩,rfl⟩ := nilIdx.symm.surjective q
    exact ⟨i,j,k,rfl⟩
  let _ : Finite (HolorIndex [a,b,c]) := Finite.of_surjective
    (fun q : Fin a × Fin b × Fin c => point q.1 q.2.1 q.2.2) (by
      intro q
      obtain ⟨i,j,k,rfl⟩ := triple q
      exact ⟨(i,j,k),rfl⟩)
  let _ : Fintype (HolorIndex [a,b,c]) := Fintype.ofFinite _
  let P := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let entry {n : ℕ} (q : HolorIndex [n]) : Fin n := (consIdx n [] q).1
  let first (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inl (entry (HolorIndex.take (ds₁ := [a]) (ds₂ := [b,c]) q)))
  let second (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inr (.inl (entry (HolorIndex.take (ds₁ := [b]) (ds₂ := [c])
      (HolorIndex.drop (ds₁ := [a]) (ds₂ := [b,c]) q)))))
  let third (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inr (.inr (entry (HolorIndex.drop (ds₁ := [b]) (ds₂ := [c])
      (HolorIndex.drop (ds₁ := [a]) (ds₂ := [b,c]) q)))))
  let pack (A : Fin r → Fin a → ℂ) (B : Fin r → Fin b → ℂ) (C : Fin r → Fin c → ℂ) (q : P) : ℂ :=
    q.2.elim (A q.1) (Sum.elim (B q.1) (C q.1))
  let φ (v : P → ℂ) (q : HolorIndex [a,b,c]) :=
    ∑ t : Fin r, v (first t q) * (v (second t q) * v (third t q))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply trilinear_image_has_interior first second third (pack x y z)
    intro Y
    obtain ⟨u,v,w,hw⟩ := hspan fun i j k => Y (point i j k)
    refine ⟨pack u v w, ?_⟩
    intro q
    obtain ⟨i,j,k,rfl⟩ := triple q
    exact hw i j k
  let F (q : HolorIndex [a,b,c]) : MvPolynomial P ℂ :=
    ∑ t : Fin r, MvPolynomial.X (first t q) *
      (MvPolynomial.X (second t q) * MvPolynomial.X (third t q))
  have he : (fun v : P → ℂ => fun q => MvPolynomial.eval v (F q)) = φ := by
    funext v q
    simp [F, φ]
  have hd := dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ),isOpen_interior,hd,?_⟩
  intro T hT
  obtain ⟨v,rfl⟩ := interior_subset hT
  let fa (t : Fin r) (i : HolorIndex [a]) := v (t, Sum.inl (entry i))
  let fb (t : Fin r) (j : HolorIndex [b]) := v (t, Sum.inr (.inl (entry j)))
  let fc (t : Fin r) (k : HolorIndex [c]) := v (t, Sum.inr (.inr (entry k)))
  have hv : (φ v : Holor ℂ [a,b,c]) = ∑ t, Holor.mul (fa t) (Holor.mul (fb t) (fc t)) := by
    funext q
    rw [eval_holor_sum]
    rfl
  rw [hv]
  exact Nat.find_min' _ (tensor_sum_rank fa fb fc)

end CriticalReduction

namespace CriticalReduction.Grid

open MvPolynomial

/-- A nonzero polynomial of total degree at most `D` has a nonzero value on
`{0, …, D}` in each coordinate, even if the ambient variable type is infinite. -/
lemma nonvanishing {V : Type*} (P : MvPolynomial V ℂ) (D : ℕ)
    (hP : P ≠ 0) (hd : P.totalDegree ≤ D) :
    ∃ v : V → Fin (D+1), eval (fun i => ((v i).val : ℂ)) P ≠ 0 := by
  classical
  by_contra! hall
  obtain ⟨n,f,hf,Q,rfl⟩ := exists_fin_rename P
  apply hP
  suffices hQ : Q=0 by rw [hQ,map_zero]
  let castGrid : Fin (D+1) ↪ ℂ := ⟨fun j => (j.val : ℂ),fun _ _ h => Fin.ext (Nat.cast_injective h)⟩
  let S : Finset ℂ := Finset.univ.map castGrid
  apply eq_zero_of_eval_zero_at_prod_finset Q (fun _ => S)
  · intro i
    have hq := (degreeOf_le_totalDegree (rename f Q) (f i)).trans hd
    rw [degreeOf_rename_of_injective hf] at hq
    simpa [S] using Nat.lt_succ_of_le hq
  · intro x hx
    have hhit (i : Fin n) : ∃ j : Fin (D+1), castGrid j=x i := by
      obtain ⟨j,_,hj⟩ := Finset.mem_map.mp (hx i)
      exact ⟨j,hj⟩
    choose u hu using hhit
    let v := Function.extend f u (fun _ => (0 : Fin (D+1)))
    have he : (fun i => ((v i).val : ℂ)) ∘ f=x := by
      funext i
      change ((Function.extend f u (fun _ => (0 : Fin (D+1))) (f i)).val : ℂ) = x i
      rw [hf.extend_apply]
      exact hu i
    simpa only [eval_rename,he] using hall v

/-- A degree bound on each entry bounds the determinant through the Leibniz formula. -/
lemma degree_det {I V : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I (MvPolynomial V ℂ))
    (d : ℕ) (hd : ∀ i j, (M i j).totalDegree ≤ d) : M.det.totalDegree ≤ d*Fintype.card I := by
  classical
  have ci (z : ℤ) : ((z : MvPolynomial V ℂ)).totalDegree=0 := by
    rw [← map_intCast (C : ℂ →+* MvPolynomial V ℂ) z,totalDegree_C]
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_mul _ _).trans
  rw [ci,zero_add]
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum (fun i _ => hd (σ i) i)).trans_eq (by simp [Nat.mul_comm])

/-- A surjective specialization of an entrywise quadratic matrix can be chosen with
all parameter coordinates integers between zero and twice the number of rows. -/
lemma quadratic_matrix {I J V : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (hm : ∀ i j, (M i j).totalDegree ≤ 2)
    (x₀ : V → ℂ) (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ v : V → Fin (2*Fintype.card I+1),
      Function.Surjective (M.map (eval (fun i => ((v i).val : ℂ)))).mulVec := by
  classical
  obtain ⟨B,hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let L := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have hs (x : V → ℂ) : eval x L.det = (M.map (eval x)*B).det := by
    have hb : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x)=B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det,RingHom.mapMatrix_apply,show L = _ from rfl,Matrix.map_mul,hb]
  have h₁ : eval x₀ L.det=1 := by rw [hs,hB,Matrix.det_one]
  have hn : L.det≠0 := by intro h; rw [h,map_zero] at h₁; exact zero_ne_one h₁
  have hd : L.det.totalDegree ≤ 2*Fintype.card I := by
    apply degree_det
    intro i j
    change (∑ k, M i k * C (B k j)).totalDegree ≤ 2
    apply totalDegree_finsetSum_le
    intro k _
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,add_zero] using hm i k)
  obtain ⟨v,hv⟩ := nonvanishing L.det _ hn hd
  refine ⟨v,?_⟩
  let x : V → ℂ := fun i => ((v i).val : ℂ)
  have hdet : (M.map (eval x)*B).det≠0 := hs x ▸ hv
  have hsur : Function.Surjective (M.map (eval x)*B).mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro y
  obtain ⟨u,hu⟩ := hsur y
  exact ⟨B.mulVec u,(Matrix.mulVec_mulVec _ _ _).trans hu⟩

end CriticalReduction.Grid

namespace CriticalReduction

/-- One complex spanning tangent configuration gives a configuration whose
factor coordinates are integers between zero and twice the tensor dimension. -/
theorem bounded_of_witness {a b c r : ℕ} (h :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k = ∑ t, (u t i*(y t j*z t k) +
          x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ x : Fin r → Fin a → Fin (2*(a*b*c)+1), ∃ y : Fin r → Fin b → Fin (2*(a*b*c)+1),
      ∃ z : Fin r → Fin c → Fin (2*(a*b*c)+1), ∀ T : Fin a → Fin b → Fin c → ℂ,
        ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ,
          ∀ i j k, T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k)) := by
  classical
  let I := Fin a × Fin b × Fin c
  let J := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let M : Matrix I J (MvPolynomial J ℂ) := fun (i,j,k) (t,s) =>
    match s with
    | .inl v => if v=i then MvPolynomial.X (t,.inr (.inl j)) * MvPolynomial.X (t,.inr (.inr k)) else 0
    | .inr (.inl v) => if v=j then MvPolynomial.X (t,.inl i) * MvPolynomial.X (t,.inr (.inr k)) else 0
    | .inr (.inr v) => if v=k then MvPolynomial.X (t,.inl i) * MvPolynomial.X (t,.inr (.inl j)) else 0
  have degree (s t : J) : ((MvPolynomial.X s : MvPolynomial J ℂ)*MvPolynomial.X t).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have hm : ∀ i j, (M i j).totalDegree ≤ 2 := by
    rintro ⟨i,j,k⟩ ⟨t,v|v|v⟩ <;> simp only [M] <;> split <;> first | apply degree | simp
  have action (p q : J → ℂ) (i : Fin a) (j : Fin b) (k : Fin c) :
      (M.map (MvPolynomial.eval p)).mulVec q (i,j,k) = ∑ t : Fin r,
        (q (t,.inl i)*(p (t,.inr (.inl j))*p (t,.inr (.inr k))) +
         p (t,.inl i)*(q (t,.inr (.inl j))*p (t,.inr (.inr k))) +
         p (t,.inl i)*(p (t,.inr (.inl j))*q (t,.inr (.inr k)))) := by
    change (∑ s : J, MvPolynomial.eval p (M (i,j,k) s)*q s) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [M,apply_ite,ite_mul,Finset.sum_ite_eq']
    ring
  let pack (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ) (z : Fin r → Fin c → ℂ) : J → ℂ :=
    fun (t,s) => s.elim (x t) (Sum.elim (y t) (z t))
  obtain ⟨x,y,z,hspan⟩ := h
  have hs : Function.Surjective (M.map (MvPolynomial.eval (pack x y z))).mulVec := by
    intro T
    obtain ⟨u,v,w,hu⟩ := hspan fun i j k => T (i,j,k)
    refine ⟨pack u v w,?_⟩
    funext ⟨i,j,k⟩
    rw [action]
    exact (hu i j k).symm
  have hcard : Fintype.card I = a*b*c := by simp [I,Nat.mul_assoc]
  obtain ⟨g₀,hg₀⟩ := Grid.quadratic_matrix M hm (pack x y z) hs
  let g (s : J) : Fin (2*(a*b*c)+1) := Fin.cast (congrArg (fun n => 2*n+1) hcard) (g₀ s)
  have hg : Function.Surjective (M.map (MvPolynomial.eval (fun s => ((g s).val : ℂ)))).mulVec := hg₀
  refine ⟨fun t i => g (t,.inl i), fun t j => g (t,.inr (.inl j)), fun t k => g (t,.inr (.inr k)), ?_⟩
  intro T
  obtain ⟨q,hq⟩ := hg (fun s => T s.1 s.2.1 s.2.2)
  refine ⟨fun t i => q (t,.inl i), fun t j => q (t,.inr (.inl j)), fun t k => q (t,.inr (.inr k)), ?_⟩
  intro i j k
  exact (congrFun hq (i,j,k)).symm.trans (action _ q i j k)

end CriticalReduction

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1
open Arxiv.«0805.3777» Set
open scoped Topology

/-- A spanning configuration at the dimension-count ceiling proves generic
rank equality by intersecting the open upper- and lower-bound loci. -/
lemma generic_of_bounded (a b c : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (finite_witness :
      let r := a*b*c ⌈/⌉ (a+b+c-2)
      let D := 2*(a*b*c)+1
      ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
        ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
          ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
            T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
              ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
              ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))) :
    IsGenericRank [a,b,c] (a*b*c ⌈/⌉ (a+b+c-2)) := by
  classical
  let d := a+b+c-2
  let r := a*b*c ⌈/⌉ d
  have hd : 0<d := by dsimp only [d]; omega
  have habc : 0<a*b*c := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hrpos : 0<r := by
    by_contra! hz
    have he : a*b*c≤d*0 := (ceilDiv_le_iff_le_mul hd).mp hz
    rw [Nat.mul_zero] at he
    omega
  have hcost : d*(r-1)<a*b*c := by
    by_contra! he
    have hsmall : r≤r-1 := (ceilDiv_le_iff_le_mul hd).mpr he
    omega
  obtain ⟨x,y,z,h⟩ := finite_witness
  have upper := @CriticalReduction.upper_of_witness a b c r
    ⟨fun t i => ((x t i).val : ℂ),fun t j => ((y t j).val : ℂ),fun t k => ((z t k).val : ℂ),h⟩
  obtain ⟨U,hu,hU,hi⟩ := upper
  let K := closure {T : Holor ℂ [a,b,c] | T.cprank ≤ r-1}
  have hl : Dense Kᶜ := interior_eq_empty_iff_dense_compl.mp (CriticalReduction.lower_of_count a b c (r-1) hcost)
  refine ⟨U ∩ Kᶜ,hu.inter isClosed_closure.isOpen_compl,hU.inter_of_isOpen_left hl hu,?_⟩
  intro T ht
  have hup := hi T ht.1
  have hlo : ¬ T.cprank≤r-1 := fun he => ht.2 (subset_closure he)
  change T.cprank=r
  omega

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1

namespace LastSliceDual

/-- A left-kernel vector is an array of matrix slices. Varying the third factors
makes every slice orthogonal to each rank-one matrix. Varying the first two
factors tests the row and column contractions of one weighted matrix per point. -/
theorem transpose_kernel_iff {K : Type*} [Field K] {a b c r : ℕ}
    (x : Fin r → Fin a → K) (y : Fin r → Fin b → K) (z : Fin r → Fin c → K)
    (G : Matrix ((Fin a × Fin b) × Fin c) (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) K)
    (entry : ∀ i j k t v, G ((i,j),k) (t,v) =
      v.elim (fun i' => if i'=i then y t j*z t k else 0)
        (Sum.elim (fun j' => if j'=j then x t i*z t k else 0)
          (fun k' => if k'=k then x t i*y t j else 0)))
    (T : ((Fin a × Fin b) × Fin c) → K) :
    G.transpose.mulVec T = 0 ↔
      let D (t : Fin r) (ij : Fin a × Fin b) := ∑ k, z t k*T (ij,k)
      (∀ k s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k) = 0) ∧
      (∀ t i, ∑ j, y t j*D t (i,j) = 0) ∧
      (∀ t j, ∑ i, x t i*D t (i,j) = 0) := by
  classical
  let D (t : Fin r) (ij : Fin a × Fin b) := ∑ k, z t k*T (ij,k)
  have first (t : Fin r) (i : Fin a) : G.transpose.mulVec T (t,.inl i) = ∑ j, y t j*D t (i,j) := by
    change (∑ q : (Fin a × Fin b) × Fin c, G q (t,.inl i)*T q) = _
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ l : Fin a, if i=l then ∑ j, y t j*D t (l,j) else 0 := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : i=l
        · simp [entry,h,D,Finset.mul_sum,mul_assoc]
        · simp [entry,h]
      _ = _ := by simp
  have second (t : Fin r) (j : Fin b) : G.transpose.mulVec T (t,.inr (.inl j)) = ∑ i, x t i*D t (i,j) := by
    change (∑ q : (Fin a × Fin b) × Fin c, G q (t,.inr (.inl j))*T q) = _
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ∑ l : Fin b, if j=l then x t i*D t (i,l) else 0 := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : j=l
        · simp [entry,h,D,Finset.mul_sum,mul_assoc]
        · simp [entry,h]
      _ = _ := by simp
  have third (s : Fin r) (k : Fin c) : G.transpose.mulVec T (s,.inr (.inr k)) =
      ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k) := by
    change (∑ q : (Fin a × Fin b) × Fin c, G q (s,.inr (.inr k))*T q) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    rintro ⟨i,j⟩ _
    simp [entry,ite_mul]
  constructor
  · intro h
    exact ⟨fun k s => (third s k).symm.trans (congrFun h _),
      fun t i => (first t i).symm.trans (congrFun h _),
      fun t j => (second t j).symm.trans (congrFun h _)⟩
  · rintro ⟨outer,row,col⟩
    funext ⟨t,v⟩
    rcases v with v | v | v
    · exact (first t v).trans (row t v)
    · exact (second t v).trans (col t v)
    · exact (third t v).trans (outer v t)

end LastSliceDual

namespace CriticalHigher

/-- A spanning witness on the seed slice space restricts to every smaller
third dimension, preserving the number of points. -/
theorem project {a b k e w : ℕ} (hk : k≤e)
    (seed : ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin e → ℂ,
      ∀ T : Fin a → Fin b → Fin e → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin e → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin k → ℂ,
      ∀ T : Fin a → Fin b → Fin k → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin k → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)) := by
  obtain ⟨x,y,z,span⟩ := seed
  refine ⟨x,y,fun t l => z t (Fin.castLE hk l),?_⟩
  intro T
  let extT (i : Fin a) (j : Fin b) (l : Fin e) := if hl : l.val<k then T i j ⟨l.val,hl⟩ else 0
  obtain ⟨u,v,s,hs⟩ := span extT
  refine ⟨u,v,fun t l => s t (Fin.castLE hk l),?_⟩
  intro i j l
  simpa [extT,l.isLt] using hs i j (Fin.castLE hk l)

end CriticalHigher

namespace CriticalLastSlice.TwoPlanes

open Arxiv.«0805.3777»

/-- A spanning witness at the parameter-count ceiling gives the original
complex generic-rank conclusion in balanced dimensions. -/
theorem generic_rank_of_witness {a b n r : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hbn : b ≤ n)
    (count : r = a*b*n ⌈/⌉ (a+b+n-2))
    (witness : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    IsGenericRank [a,b,n] r := by
  subst r
  exact OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b n ha hab hbn
    (CriticalReduction.bounded_of_witness witness)

end CriticalLastSlice.TwoPlanes

namespace CriticalHigher

theorem count_le_iff {A d n r : ℕ} (hd : 0<d) (hr : r<A) :
    A*n ⌈/⌉ (d+n) ≤ r ↔ n ≤ r*d/(A-r) := by
  rw [ceilDiv_le_iff_le_mul (by omega : 0<d+n), Nat.le_div_iff_mul_le (by omega : 0<A-r)]
  have split := congrArg (fun z : ℕ => z*n) (Nat.sub_add_cancel hr.le)
  constructor <;> intro h <;> nlinarith only [split,h]

/-- Both endpoints are exact, including ranks for which the integer interval
is empty. -/
theorem count_interval {A d n r : ℕ} (hd : 0<d) (hr : 0<r) (proper : r<A) :
    A*n ⌈/⌉ (d+n) = r ↔ (r-1)*d/(A-(r-1)) < n ∧ n ≤ r*d/(A-r) := by
  have hi := count_le_iff (n:=n) hd proper
  have lo := count_le_iff (n:=n) hd (by omega : r-1<A)
  omega

theorem endpoint_count {A d n r : ℕ} (hd : 0<d) (hr : 0<r) (proper : r<A)
    (count : A*n ⌈/⌉ (d+n)=r) :
    let N := r*d/(A-r)
    n≤N ∧ A*N ⌈/⌉ (d+N)=r := by
  obtain ⟨lo,hi⟩ := (count_interval hd hr proper).mp count
  exact ⟨hi,(count_interval hd hr proper).mpr ⟨lo.trans_le hi,le_rfl⟩⟩

end CriticalHigher

namespace CriticalThreeQuotient

/-- The two point equations determine a three-slice normal at each ordered
pair of distinct samples. Its remaining freedom is one scalar per pair. -/
theorem normal_entries {K I : Type*} [Field K] (l m : I → K)
    (distinct : Function.Injective l) (A B C : I → I → K)
    (diag : ∀ s, A s s = 0 ∧ B s s = 0 ∧ C s s = 0)
    (row : ∀ s t, A s t + l s*B s t + m s*C s t = 0)
    (col : ∀ s t, A s t + l t*B s t + m t*C s t = 0) :
    ∃ E : I → I → K, ∀ s t,
      A s t = (l t*m s - l s*m t)*E s t ∧
      B s t = (m t - m s)*E s t ∧ C s t = (l s - l t)*E s t := by
  let E (s t : I) := C s t / (l s - l t)
  refine ⟨E, fun s t => ?_⟩
  by_cases eq : s=t
  · subst t
    simp [diag s]
  have gap : l s - l t ≠ 0 := sub_ne_zero.mpr (distinct.ne eq)
  have hC : C s t = (l s-l t)*E s t := by dsimp [E]; field_simp
  have hB : B s t = (m t-m s)*E s t := by
    apply (mul_left_cancel₀ gap)
    linear_combination (row s t) - (col s t) - (m s-m t)*hC
  exact ⟨by linear_combination (row s t) - l s*hB - m s*hC,hB,hC⟩

/-- Injectivity modulo diagonal matrices of the two compressed diagonal
commutators kills the full normal. The third slice is then forced entrywise. -/
theorem normal_zero_of_commutators {K I U V : Type*} [Field K] [Fintype I]
    (l m : I → K) (distinct : Function.Injective l) (P : U → I → K) (Q : V → I → K)
    (exactPair : ∀ E : I → I → K,
      (∀ u t, ∑ s, P u s*((l s-l t)*E s t) = 0) →
      (∀ u t, ∑ s, P u s*((m s-m t)*E s t) = 0) →
      (∀ v s, ∑ t, ((l s-l t)*E s t)*Q v t = 0) →
      (∀ v s, ∑ t, ((m s-m t)*E s t)*Q v t = 0) →
      ∀ s t, s≠t → E s t=0)
    (A B C : I → I → K)
    (diag : ∀ s, A s s = 0 ∧ B s s = 0 ∧ C s s = 0)
    (row : ∀ s t, A s t + l s*B s t + m s*C s t = 0)
    (col : ∀ s t, A s t + l t*B s t + m t*C s t = 0)
    (leftB : ∀ u t, ∑ s, P u s*B s t = 0)
    (leftC : ∀ u t, ∑ s, P u s*C s t = 0)
    (rightB : ∀ v s, ∑ t, B s t*Q v t = 0)
    (rightC : ∀ v s, ∑ t, C s t*Q v t = 0) :
    ∀ s t, A s t=0 ∧ B s t=0 ∧ C s t=0 := by
  obtain ⟨E,entries⟩ := normal_entries l m distinct A B C diag row col
  have eC (s t) := (entries s t).2.2
  have eB (s t) : (m s-m t)*E s t = -B s t := by
    rw [(entries s t).2.1]
    ring
  have zero := exactPair E
    (fun u t => by simpa only [← eC] using leftC u t)
    (fun u t => by simp only [eB,mul_neg,Finset.sum_neg_distrib,leftB,neg_zero])
    (fun v s => by simpa only [← eC] using rightC v s)
    (fun v s => by simp only [eB,neg_mul,Finset.sum_neg_distrib,rightB,neg_zero])
  intro s t
  by_cases eq : s=t
  · subst t
    exact diag s
  · simpa only [zero s t eq,mul_zero] using entries s t

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- A three-slice CP tangent spans if the two diagonal commutators have no
off-diagonal common kernel after compression by relations of the two frames. -/
theorem tangent_of_commutators {K U V : Type*} [Field K] {b n r : ℕ}
    (l m : Fin r → K) (distinct : Function.Injective l)
    (Y : Matrix (Fin r) (Fin b) K) (Z : Matrix (Fin r) (Fin n) K)
    (P : Matrix U (Fin r) K) (Q : Matrix V (Fin r) K)
    (pY : P * Y = 0) (qZ : Q * Z = 0)
    (embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) K => Y * N * Z.transpose))
    (exactPair : ∀ E : Fin r → Fin r → K,
      (∀ u t, ∑ s, P u s*((l s-l t)*E s t) = 0) →
      (∀ u t, ∑ s, P u s*((m s-m t)*E s t) = 0) →
      (∀ v s, ∑ t, ((l s-l t)*E s t)*Q v t = 0) →
      (∀ v s, ∑ t, ((m s-m t)*E s t)*Q v t = 0) →
      ∀ s t, s≠t → E s t=0) :
    let x (s : Fin r) : Fin 3 → K := ![1,l s,m s]
    ∀ T : Fin 3 → Fin b → Fin n → K, ∃ u : Fin r → Fin 3 → K,
      ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin n → K, ∀ i j k,
        T i j k=∑ t, (u t i*(Y t j*Z t k) + x t i*(v t j*Z t k) + x t i*(Y t j*w t k)) := by
  classical
  dsimp only
  let x (s : Fin r) : Fin 3 → K := ![1,l s,m s]
  let I := Fin r × (Fin 3 ⊕ (Fin b ⊕ Fin n))
  let M : Matrix ((Fin 3 × Fin b) × Fin n) I K := fun t s =>
    s.2.elim (fun i => if i=t.1.1 then Y s.1 t.1.2 * Z s.1 t.2 else 0)
      (Sum.elim (fun j => if j=t.1.2 then x s.1 t.1.1 * Z s.1 t.2 else 0)
        (fun k => if k=t.2 then x s.1 t.1.1 * Y s.1 t.1.2 else 0))
  have noRelation (H : (Fin 3 × Fin b) × Fin n → K) (relation : M.transpose.mulVec H=0) : H=0 := by
    obtain ⟨outer,diag,col⟩ := (LastSliceDual.transpose_kernel_iff x Y Z M (by intros; rfl) H).mp relation
    let N (i : Fin 3) : Matrix (Fin b) (Fin n) K := fun j k => H ((i,j),k)
    let S (i : Fin 3) := Y * N i * Z.transpose
    have value (i : Fin 3) (s t : Fin r) : S i s t = ∑ j, Y s j*(∑ k, Z t k*H ((i,j),k)) := by
      change (∑ k, (∑ j, Y s j * H ((i,j),k)) * Z t k) = _
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have rowEq (s t : Fin r) : ∑ i, x s i * S i s t = 0 := by
      calc
        _ = ∑ k, Z t k * (∑ ij : Fin 3 × Fin b, (x s ij.1*Y s ij.2)*H (ij,k)) := by
          simp only [value,Fintype.sum_prod_type,Finset.mul_sum]
          calc
            _ = ∑ i, ∑ k, ∑ j, x s i*(Y s j*(Z t k*H ((i,j),k))) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
            _ = _ := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k _
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = 0 := by simp [outer]
    have colEq (s t : Fin r) : ∑ i, x t i * S i s t = 0 := by
      calc
        _ = ∑ j, Y s j * (∑ i, x t i*(∑ k, Z t k*H ((i,j),k))) := by
          simp only [value,Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 0 := by simp [col]
    have leftZero (i : Fin 3) (u : U) (t : Fin r) : ∑ s, P u s*S i s t=0 := by
      have e : P * S i=0 := by simp [S,← Matrix.mul_assoc,pY]
      exact congrFun (congrFun e u) t
    have rightZero (i : Fin 3) (v : V) (s : Fin r) : ∑ t, S i s t*Q v t=0 := by
      have e : S i * Q.transpose=0 := by simp [S,Matrix.mul_assoc,← Matrix.transpose_mul,qZ]
      exact congrFun (congrFun e s) v
    have vanish := normal_zero_of_commutators l m distinct P Q exactPair (S 0) (S 1) (S 2)
      (fun s => ⟨(value 0 s s).trans (diag s 0),(value 1 s s).trans (diag s 1),
        (value 2 s s).trans (diag s 2)⟩)
      (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using rowEq s t)
      (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using colEq s t)
      (leftZero 1) (leftZero 2) (rightZero 1) (rightZero 2)
    have allZero (i : Fin 3) : N i=0 := by
      apply embed
      simp only [Matrix.mul_zero,Matrix.zero_mul]
      ext s t
      fin_cases i
      · exact (vanish s t).1
      · exact (vanish s t).2.1
      · exact (vanish s t).2.2
    funext ⟨⟨i,j⟩,k⟩
    exact congrFun (congrFun (allZero i) j) k
  have surj : Function.Surjective M.mulVec := by
    have hk : LinearMap.ker M.transpose.mulVecLin=⊥ := by
      apply bot_unique
      exact fun t h => (Submodule.mem_bot K).mpr (noRelation t h)
    have hr := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk)
    change M.transpose.rank=Module.finrank K (((Fin 3 × Fin b) × Fin n) → K) at hr
    rw [Matrix.rank_transpose] at hr
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hr)
  intro T
  obtain ⟨p,hp⟩ := surj fun q => T q.1.1 q.1.2 q.2
  refine ⟨fun t i => p (t,.inl i),fun t j => p (t,.inr (.inl j)),fun t k => p (t,.inr (.inr k)),?_⟩
  intro i j k
  refine (congrFun hp ((i,j),k)).symm.trans ?_
  change (∑ v : I, M ((i,j),k) v*p v)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [M,ite_mul,Finset.sum_ite_eq']
  ring

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- When all three factors use characters, the two compressed commutators
are injective modulo the diagonal as soon as every frequency graph is connected.
The hypotheses state connectivity as propagation of values along its edges. -/
theorem commutators_of_frequency_graphs {G K I U V : Type*} [AddCommGroup G] [Field K] [Fintype I]
    (χ : G → I → K) (law : ∀ a b t, χ (a+b) t=χ a t*χ b t)
    (fourier : Function.Injective (fun N : I → I → K => fun i j : G =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)))
    (one d : G) (distinct : Function.Injective (χ one)) (P : U → G) (Q : V → G)
    (connected : ∀ k : G, ∀ f : G → K,
      (∀ u, f (P u+one)=f (P u) ∧ f (P u+d)=f (P u)) →
      (∀ v, f (k-Q v-one)=f (k-Q v) ∧ f (k-Q v-d)=f (k-Q v)) →
      ∀ i j, f i=f j)
    (E : I → I → K)
    (leftOne : ∀ u t, ∑ s, χ (P u) s*((χ one s-χ one t)*E s t) = 0)
    (leftD : ∀ u t, ∑ s, χ (P u) s*((χ d s-χ d t)*E s t) = 0)
    (rightOne : ∀ v s, ∑ t, ((χ one s-χ one t)*E s t)*χ (Q v) t = 0)
    (rightD : ∀ v s, ∑ t, ((χ d s-χ d t)*E s t)*χ (Q v) t = 0) :
    ∀ s t, s≠t → E s t=0 := by
  let M (i j : G) := ∑ s, ∑ t, χ i s*(E s t*χ j t)
  let C (c i j : G) := ∑ s, ∑ t, χ i s*(((χ c s-χ c t)*E s t)*χ j t)
  have shift (c i j : G) : M (i+c) j-M i (j+c)=C c i j := by
    simp only [M,C,law,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have leftEdge (c : G) (left : ∀ u t, ∑ s, χ (P u) s*((χ c s-χ c t)*E s t)=0)
      (u : U) (j : G) : M (P u+c) j=M (P u) (j+c) := by
    apply sub_eq_zero.mp
    rw [shift]
    change (∑ s, ∑ t, χ (P u) s*(((χ c s-χ c t)*E s t)*χ j t))=0
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, (∑ s, χ (P u) s*((χ c s-χ c t)*E s t)) * χ j t := by
        simp only [Finset.sum_mul,mul_assoc]
      _ = 0 := by simp [left]
  have rightEdge (c : G) (right : ∀ v s, ∑ t, ((χ c s-χ c t)*E s t)*χ (Q v) t=0)
      (v : V) (i : G) : M (i+c) (Q v)=M i (Q v+c) := by
    apply sub_eq_zero.mp
    rw [shift]
    change (∑ s, ∑ t, χ i s*(((χ c s-χ c t)*E s t)*χ (Q v) t))=0
    simp only [← Finset.mul_sum,right,mul_zero,Finset.sum_const_zero]
  have same (k i j : G) : M i (k-i)=M j (k-j) := by
    apply connected k (fun u => M u (k-u))
    · intro u
      have edge (c : G) (hyp : ∀ z, M (P u+c) z=M (P u) (z+c)) :
          M (P u+c) (k-(P u+c))=M (P u) (k-P u) := by
        rw [hyp,show k-(P u+c)+c=k-P u by abel]
      exact ⟨edge one (leftEdge one leftOne u),edge d (leftEdge d leftD u)⟩
    · intro v
      have edge (c : G) (hyp : ∀ z, M (z+c) (Q v)=M z (Q v+c)) :
          M (k-Q v-c) (k-(k-Q v-c))=M (k-Q v) (k-(k-Q v)) := by
        rw [show k-(k-Q v-c)=Q v+c by abel,show k-(k-Q v)=Q v by abel,← hyp,
          show k-Q v-c+c=k-Q v by abel]
      exact ⟨edge one (rightEdge one rightOne v),edge d (rightEdge d rightD v)⟩
  have zero (i j : G) : C one i j=0 := by
    rw [← shift,sub_eq_zero]
    have h := same (i+j+one) (i+one) i
    rwa [show i+j+one-(i+one)=j by abel,show i+j+one-i=j+one by abel] at h
  have annihilated : (fun s t => (χ one s-χ one t)*E s t) = (0 : I → I → K) := by
    apply fourier
    funext i j
    simpa only [Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero] using zero i j
  intro s t ne
  have h := congrFun (congrFun annihilated s) t
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- Connected frequency graphs give a complex CP tangent at the literal
character factors, with the omitted Fourier modes as frame relations. -/
theorem tangent_of_cyclic_graphs {r b n : ℕ} [NeZero r] (d : ZMod r)
    (P Q : Finset (ZMod r)) (Y : Fin b ↪ ZMod r) (Z : Fin n ↪ ZMod r)
    (avoidY : ∀ j, Y j ∉ P) (avoidZ : ∀ k, Z k ∉ Q)
    (connected : ∀ k : ZMod r, ∀ f : ZMod r → ℂ,
      (∀ u ∈ P, f (u+1)=f u ∧ f (u+d)=f u) →
      (∀ v ∈ Q, f (k-v-1)=f (k-v) ∧ f (k-v-d)=f (k-v)) →
      ∀ i j, f i=f j) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let e := (ZMod.finEquiv r).toEquiv
  let χ (i : ZMod r) (s : Fin r) : ℂ := ZMod.stdAddChar (e s*i)
  have law (a b : ZMod r) (t : Fin r) : χ (a+b) t=χ a t*χ b t := by
    simp only [χ,mul_add,AddChar.map_add_eq_mul]
  have injective : Function.Injective (χ 1) := by
    simpa only [χ,mul_one,Function.comp_def] using ZMod.injective_stdAddChar.comp e.injective
  have orth (i j : ZMod r) : ∑ s, χ i s*χ (-j) s = if i=j then (r:ℂ) else 0 := by
    calc
      _ = ∑ s : Fin r, ZMod.stdAddChar (e s*(i-j)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← law,← sub_eq_add_neg]
      _ = ∑ t : ZMod r, ZMod.stdAddChar (t*(i-j)) := e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (t*(i-j)))
      _ = _ := by
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _),ZMod.card]
        by_cases h : i=j <;> simp [h,sub_eq_zero]
  have separates (a b : Fin r → ℂ) (test : ∀ i : ZMod r, ∑ s, χ i s*a s=∑ s, χ i s*b s) : a=b := by
    have eq : (fun j => a (e.symm j))=(fun j => b (e.symm j)) := by
      apply ZMod.dft.injective
      funext i
      rw [ZMod.dft_apply,ZMod.dft_apply]
      simp only [smul_eq_mul]
      rw [← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*a (e.symm t)),
        ← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*b (e.symm t))]
      simpa only [e.symm_apply_apply,χ,mul_neg] using test (-i)
    funext s
    simpa only [e.symm_apply_apply] using congrFun eq (e s)
  have fourier : Function.Injective (fun N : Fin r → Fin r → ℂ => fun i j : ZMod r =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)) := by
    intro A B he
    have each (j : ZMod r) : (fun s => ∑ t, A s t*χ j t)=(fun s => ∑ t, B s t*χ j t) := by
      apply separates
      intro i
      simpa only [Finset.mul_sum] using congrFun (congrFun he i) j
    funext s
    apply separates
    intro j
    simpa only [mul_comm (χ j _)] using congrFun (each j) s
  let frame {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin r) (Fin m) ℂ := fun s j => χ (-(H j)) s
  let dual {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin m) (Fin r) ℂ := fun j s => χ (H j) s / r
  have frameId {m : ℕ} (H : Fin m ↪ ZMod r) : dual H * frame H=1 := by
    ext i j
    change (∑ s, (χ (H i) s/r)*χ (-(H j)) s)=_
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,orth]
    by_cases h : i=j
    · subst j
      simp [NeZero.ne r]
    · simp [h,H.injective.ne h]
  have embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) ℂ => frame Y*N*(frame Z).transpose) := by
    intro A B eq
    have extract (N : Matrix (Fin b) (Fin n) ℂ) :
        (dual Y)*(frame Y*N*(frame Z).transpose)*(dual Z).transpose=N := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,frameId,Matrix.one_mul,Matrix.mul_assoc,
        ← Matrix.transpose_mul,frameId,Matrix.transpose_one,Matrix.mul_one]
    exact (extract A).symm.trans ((congrArg (fun N => (dual Y)*N*(dual Z).transpose) eq).trans (extract B))
  have annihilate {m : ℕ} (A : Finset (ZMod r)) (H : Fin m ↪ ZMod r) (avoid : ∀ j, H j∉A) :
      (Matrix.of (fun (i : A) (t : Fin r) => χ i.val t))*frame H=0 := by
    ext i j
    change (∑ s, χ i.val s*χ (-(H j)) s)=0
    have ne : i.val≠H j := fun h => avoid j (h ▸ i.property)
    rw [orth,if_neg ne]
  refine ⟨fun s => ![1,χ 1 s,χ d s],frame Y,frame Z,?_⟩
  apply tangent_of_commutators (χ 1) (χ d) injective (frame Y) (frame Z) _ _
    (annihilate P Y avoidY) (annihilate Q Z avoidZ) embed
  exact commutators_of_frequency_graphs χ law fourier 1 d injective Subtype.val Subtype.val
    (fun k f left right => connected k f (fun i hi => left ⟨i,hi⟩) (fun i hi => right ⟨i,hi⟩))

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- The dimensions complementary to the two relation sets determine frames
from the unused frequencies. -/
theorem tangent_of_graph_cards {r b n : ℕ} [NeZero r] (d : ZMod r)
    (P Q : Finset (ZMod r)) (pCard : P.card+b=r) (qCard : Q.card+n=r)
    (connected : ∀ k : ZMod r, ∀ f : ZMod r → ℂ,
      (∀ u ∈ P, f (u+1)=f u ∧ f (u+d)=f u) →
      (∀ v ∈ Q, f (k-v-1)=f (k-v) ∧ f (k-v-d)=f (k-v)) →
      ∀ i j, f i=f j) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  have choose {m : ℕ} (F : Finset (ZMod r)) (count : F.card+m=r) :
      ∃ J : Fin m ↪ ZMod r, ∀ i, J i∉F := by
    have size : Fintype.card (Fin m)=Fintype.card (↥(Fᶜ) : Type) := by
      rw [Fintype.card_fin,Fintype.card_coe,Finset.card_compl,ZMod.card]
      omega
    let e := Fintype.equivOfCardEq size
    exact ⟨e.toEmbedding.trans (Function.Embedding.subtype _),
      fun i => Finset.mem_compl.mp (e i).property⟩
  obtain ⟨Y,hy⟩ := choose P pCard
  obtain ⟨Z,hz⟩ := choose Q qCard
  exact tangent_of_cyclic_graphs d P Q Y Z hy hz connected

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- The gaps between d-spaced samples, including the closing gap, are at
most W. Every residue u is thus t*d plus an offset in [0,W), for t≤q. -/
theorem chain_hits {r W d q u : ℕ} (hd : 0<d) (step : d≤W) (closing : r≤q*d+W)
    (hr : u<r) : ∃ t≤q, ∃ o<W,t*d+o=u := by
  by_cases h : u<q*d
  · refine ⟨u/d,((Nat.div_lt_iff_lt_mul hd).mpr h).le,u%d,(Nat.mod_lt u hd).trans_le step,?_⟩
    rw [Nat.mul_comm,Nat.div_add_mod]
  · exact ⟨q,le_rfl,u-q*d,by omega,by omega⟩

/-- Within a block of width 2L+1 the L centers have steps +1 and +(L+1).
These edges force the value on every position to equal the block's first value. -/
theorem block_constant {r L : ℕ} {C : Type*} (f : ZMod r → C) (z : ZMod r)
    (edge : ∀ i : Fin L, f (z+(i.val:ZMod r)+1)=f (z+i.val) ∧
      f (z+(i.val:ZMod r)+((L+1:ℕ):ZMod r))=f (z+i.val)) :
    ∀ o : ℕ,o<2*L+1 → f (z+(o:ZMod r))=f z := by
  have first (t : ℕ) (ht : t≤L) : f (z+(t:ZMod r))=f z := by
    induction t with
    | zero => simp
    | succ t ih =>
      simpa only [Nat.cast_succ,← add_assoc] using
        ((edge ⟨t,by omega⟩).1.trans (ih (by omega)))
  intro o ho
  by_cases h : o≤L
  · exact first o h
  · let i : Fin L := ⟨o-(L+1),by omega⟩
    have eq : i.val+(L+1)=o := by dsimp [i]; omega
    have same : z+(i.val:ZMod r)+((L+1:ℕ):ZMod r)=z+(o:ZMod r) := by
      rw [add_assoc,← Nat.cast_add,eq]
    rw [← same]
    exact (edge i).2.trans (first i.val i.isLt.le)

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- ceil((r−W)/d) is the least number of right centers making the
closing gap at most W. All its sampled centers are distinct modulo r. -/
theorem least_chain {r W d : ℕ} (width : W≤r) (hd : 0<d) (step : d≤W) :
    let q := (r-W) ⌈/⌉ d
    q*d<r ∧ r≤q*d+W ∧ ∀ t : ℕ,r≤t*d+W ↔ q≤t := by
  intro q
  have least (t : ℕ) : r≤t*d+W ↔ q≤t := by
    change r≤t*d+W ↔ (r-W) ⌈/⌉ d≤t
    rw [ceilDiv_le_iff_le_mul hd,Nat.mul_comm d t]
    omega
  have upper : q*d≤(r-W+d-1) := by
    change ((r-W) ⌈/⌉ d)*d≤r-W+d-1
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_mul_le_self _ _
  exact ⟨by omega,(least q).mpr le_rfl,least⟩

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- The longer block has centers 0 and 2 through L+1. Its 0 to L+1
edge joins the two unit chains; its long edges cover the remaining positions. -/
theorem long_block_constant {L : ℕ} (hL : 2≤L) {C : Type*} (f : ℕ → C)
    (first : f 1=f 0 ∧ f (L+1)=f 0)
    (edges : ∀ t : ℕ,2≤t → t≤L+1 → f (t+1)=f t ∧ f (t+(L+1))=f t) :
    ∀ o : ℕ,o<2*L+3 → f o=f 0 := by
  have run (t : ℕ) (lo : 2≤t) (hi : t≤L+2) : f t=f 2 := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases eq : t+1=2
      · rw [eq]
      · exact ((edges t (by omega) (by omega)).1).trans (ih (by omega) (by omega))
  have two : f 2=f 0 := (run (L+1) (by omega) (by omega)).symm.trans first.2
  intro o ho
  by_cases small : o<2
  · rcases (by omega : o=0 ∨ o=1) with rfl|rfl
    · rfl
    · exact first.1
  · by_cases mid : o≤L+2
    · exact (run o (by omega) mid).trans two
    · let t := o-(L+1)
      have eq : t+(L+1)=o := by dsimp [t]; omega
      have lo : 2≤t := by dsimp [t]; omega
      have hi : t≤L+1 := by dsimp [t]; omega
      rw [← eq]
      exact ((edges t lo hi).2).trans ((run t lo (by omega)).trans two)

/-- Exactly L+1 distinct left Fourier modes are used in a long block. -/
theorem long_centers (L : ℕ) :
    ∃ centers : Fin (L+1) ↪ Fin (2*L+3),
      ∀ t : ℕ,(∃ i, (centers i).val=t) ↔ t=0 ∨ 2≤t ∧ t≤L+1 := by
  let centers (i : Fin (L+1)) : Fin (2*L+3) :=
    ⟨if i.val=0 then 0 else i.val+1,by split <;> have := i.isLt <;> omega⟩
  have inj : Function.Injective centers := by
    intro i j eq
    apply Fin.ext
    have raw := congrArg Fin.val eq
    change (if i.val=0 then 0 else i.val+1)=(if j.val=0 then 0 else j.val+1) at raw
    split_ifs at raw <;> omega
  refine ⟨⟨centers,inj⟩,?_⟩
  intro t
  constructor
  · rintro ⟨i,rfl⟩
    change (if i.val=0 then 0 else i.val+1)=0 ∨
      2≤(if i.val=0 then 0 else i.val+1) ∧ (if i.val=0 then 0 else i.val+1)≤L+1
    split_ifs <;> have := i.isLt <;> omega
  · rintro (rfl|⟨lo,hi⟩)
    · exact ⟨0,by simp [centers]⟩
    · let t' : Fin (L+1) := ⟨t-1,by omega⟩
      refine ⟨t',?_⟩
      change (if t-1=0 then 0 else t-1+1)=t
      split <;> omega

/-- A chain intersects every constant patch that contains at least W
consecutive residues from its start. Patch lengths may vary. -/
theorem patches_of_chain {r W d q : ℕ} [NeZero r] {C : Type*} (f : ZMod r → C) (k : ZMod r)
    (hd : 0<d) (step : d≤W) (closing : r≤q*d+W)
    (patch : ∀ x,∃ B : ZMod r, f x=f B ∧ ∀ o : ℕ,o<W → f (B+(o:ZMod r))=f B)
    (edge : ∀ t : Fin q,f (k-((t.val*d:ℕ):ZMod r)-(d:ZMod r))=f (k-((t.val*d:ℕ):ZMod r))) :
    ∀ i j,f i=f j := by
  have chain (t : ℕ) (ht : t≤q) : f (k-((t*d:ℕ):ZMod r))=f k := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul,Nat.cast_add,← sub_sub]
      exact (edge ⟨t,by omega⟩).trans (ih (by omega))
  have all (x : ZMod r) : f x=f k := by
    obtain ⟨B,hx,flat⟩ := patch x
    obtain ⟨t,ht,o,ho,dist⟩ := chain_hits hd step closing (k-B).val_lt
    have eq : ((t*d:ℕ):ZMod r)+(o:ZMod r)=k-B := by
      rw [← Nat.cast_add,dist,ZMod.natCast_zmod_val]
    have hit : B+(o:ZMod r)=k-((t*d:ℕ):ZMod r) := by linear_combination eq
    exact hx.trans ((flat _ ho).symm.trans ((congrArg f hit).trans (chain _ ht)))
  exact fun i j => (all i).trans (all j).symm

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- Use s initial blocks of width 2L+3 and h−s final blocks of width 2L+1.
Their Fourier centers and one chain of q right modes connect every frequency
graph whenever the chain and its closing gap fit the shorter block width. -/
theorem mixed_graphs_of_q (h L s q : ℕ) (hh : 0<h) (hL : 2≤L) (hs : s≤h)
    (short : q*(L+1)≤h*(2*L+1)+2*s)
    (cover : h*(2*L+1)+2*s≤q*(L+1)+(2*L+1)) :
    let r := h*(2*L+1)+2*s
    ∃ P Q : Finset (ZMod r), P.card=h*L+s ∧ Q.card=q ∧
      ∀ k : ZMod r,∀ f : ZMod r → ℂ,
        (∀ u∈P,f (u+1)=f u ∧ f (u+((L+1:ℕ):ZMod r))=f u) →
        (∀ v∈Q,f (k-v-1)=f (k-v) ∧ f (k-v-((L+1:ℕ):ZMod r))=f (k-v)) →
        ∀ i j,f i=f j := by
  classical
  intro r
  let W := 2*L+1
  let U := 2*L+3
  let d := L+1
  have hw : 0<W := by dsimp [W]; omega
  have hd : 0<d := by dsimp [d]; omega
  have hr : 0<r := Nat.add_pos_left (Nat.mul_pos hh hw) _
  let : NeZero r := ⟨hr.ne'⟩
  have widths : s*U+(h-s)*W=r := by
    have split := congrArg (·*W) (Nat.sub_add_cancel hs)
    change (h-s+s)*W=h*W at split
    change s*U+(h-s)*W=h*W+2*s
    rw [show U=W+2 by rfl]
    nlinarith only [split]
  let G := (Fin s × Fin U) ⊕ (Fin (h-s) × Fin W)
  let M := (Fin s × Fin (L+1)) ⊕ (Fin (h-s) × Fin L)
  let slot : G ≃ Fin r :=
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr widths)
  let residue : Fin r ↪ ZMod r :=
    { toFun := fun i => (i.val:ZMod r)
      inj' := by
        intro i j eq
        apply Fin.ext
        have raw := congrArg ZMod.val eq
        simpa only [ZMod.val_natCast_of_lt i.isLt,ZMod.val_natCast_of_lt j.isLt] using raw }
  let enc : G ↪ ZMod r := slot.toEmbedding.trans residue
  have onto : Function.Surjective enc := by
    intro x
    obtain ⟨p,hp⟩ := slot.surjective ⟨x.val,x.val_lt⟩
    refine ⟨p,?_⟩
    change ((slot p).val : ZMod r)=x
    rw [hp,ZMod.natCast_zmod_val]
  let lb (j : Fin s) : ZMod r := ((j.val*U:ℕ):ZMod r)
  let sb (j : Fin (h-s)) : ZMod r := ((s*U+j.val*W:ℕ):ZMod r)
  have leval (j : Fin s) (i : Fin U) : enc (.inl (j,i))=lb j+(i.val:ZMod r) := by
    change ((i.val+U*j.val:ℕ):ZMod r)=((j.val*U:ℕ):ZMod r)+i.val
    push_cast
    ring
  have seval (j : Fin (h-s)) (i : Fin W) : enc (.inr (j,i))=sb j+(i.val:ZMod r) := by
    change ((s*U+(i.val+W*j.val):ℕ):ZMod r)=((s*U+j.val*W:ℕ):ZMod r)+i.val
    push_cast
    ring
  obtain ⟨lc,lcRange⟩ := long_centers L
  let sc : Fin L ↪ Fin W := Fin.castLEEmb (by dsimp [W]; omega)
  let pick : M ↪ G := ((Function.Embedding.refl (Fin s)).prodMap lc).sumMap
    ((Function.Embedding.refl (Fin (h-s))).prodMap sc)
  let pe := pick.trans enc
  let P := Finset.univ.map pe
  have lmem (j : Fin s) (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤L+1) : lb j+(i:ZMod r)∈P := by
    obtain ⟨t,ht⟩ := (lcRange i).mpr hi
    have hm : pe (.inl (j,t))∈P := Finset.mem_map.mpr ⟨.inl (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inl (j,lc t))∈P at hm
    simpa only [leval,ht] using hm
  have smem (j : Fin (h-s)) (i : Fin L) : sb j+(i.val:ZMod r)∈P := by
    have hm : pe (.inr (j,i))∈P := Finset.mem_map.mpr ⟨.inr (j,i),Finset.mem_univ _,rfl⟩
    change enc (.inr (j,sc i))∈P at hm
    simpa only [seval,show (sc i).val=i.val from rfl] using hm
  have qlimit (t : Fin q) : t.val*d<r := (Nat.mul_lt_mul_of_pos_right t.isLt hd).trans_le short
  let qe : Fin q ↪ ZMod r :=
    { toFun := fun t => ((t.val*d:ℕ):ZMod r)
      inj' := by
        intro t u eq
        have raw := congrArg ZMod.val eq
        change (((t.val*d:ℕ):ZMod r)).val=(((u.val*d:ℕ):ZMod r)).val at raw
        rw [ZMod.val_natCast_of_lt (qlimit t),ZMod.val_natCast_of_lt (qlimit u)] at raw
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd raw) }
  let Q := Finset.univ.map qe
  have countP : P.card=h*L+s := by
    simp only [P,Finset.card_map,Finset.card_univ,M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    have split := congrArg (·*L) (Nat.sub_add_cancel hs)
    change (h-s+s)*L=h*L at split
    nlinarith only [split]
  refine ⟨P,Q,countP,by simp [Q],?_⟩
  intro k f left right
  have lf (j : Fin s) (o : ℕ) (ho : o<U) : f (lb j+(o:ZMod r))=f (lb j) := by
    let g (t : ℕ) := f (lb j+(t:ZMod r))
    have eq (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤L+1) :
        g (i+1)=g i ∧ g (i+(L+1))=g i := by
      have a := left (lb j+(i:ZMod r)) (lmem j i hi)
      simpa only [g,Nat.cast_add,Nat.cast_one,← add_assoc] using a
    have a := eq 0 (Or.inl rfl)
    have all := long_block_constant hL g (by simpa only [zero_add] using a)
      (fun t hlo hhi => eq t (.inr ⟨hlo,hhi⟩)) o ho
    simpa only [g,Nat.cast_zero,add_zero] using all
  have sf (j : Fin (h-s)) := block_constant f (sb j) (L:=L) (fun i => left _ (smem j i))
  apply patches_of_chain f k hd (by dsimp [d,W]; omega : d≤W) cover
  · intro x
    obtain ⟨⟨j,i⟩|⟨j,i⟩,rfl⟩ := onto x
    · exact ⟨lb j,(congrArg f (leval j i)).trans (lf j _ i.isLt),
        fun o ho => lf j o (by dsimp [W] at ho; dsimp [U]; omega)⟩
    · exact ⟨sb j,(congrArg f (seval j i)).trans (sf j _ i.isLt),sf j⟩
  · intro t
    exact (right (qe t) (Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩)).2

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- The short-chain test after splitting the middle dimension into long and
short blocks. The remainder s can be any integer between 0 and h. -/
theorem mixed_tangent_of_capacity (h L s N : ℕ) (hh : 0<h) (hL : 2≤L) (hs : s≤h) :
    let W := 2*L+1
    let r := h*W+2*s
    let b := h*(L+1)+s
    N≤r → r≤(r-N)*(L+1)+W →
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  intro W r b enough cap
  have hw : 0<W := by dsimp [W]; omega
  have hr : 0<r := by have := Nat.mul_pos hh hw; dsimp [r]; omega
  have : NeZero r := ⟨hr.ne'⟩
  have wle : W≤r := by
    have le : W≤h*W := by simpa only [one_mul] using Nat.mul_le_mul_right W (show 1≤h from hh)
    dsimp [r]
    omega
  let q := (r-W) ⌈/⌉ (L+1)
  have vals := least_chain wle (by omega : 0<L+1) (by dsimp [W]; omega : L+1≤W)
  have qle : q≤r-N := (vals.2.2 _).mp cap
  obtain ⟨P,Q,cardP,cardQ,connected⟩ :=
    mixed_graphs_of_q h L s q hh hL hs vals.1.le vals.2.1
  have psize : P.card+b=r := by rw [cardP]; dsimp [b,r,W]; ring
  have qsize : Q.card+(r-q)=r := by rw [cardQ]; omega
  exact CriticalHigher.project (show N≤r-q by omega)
    (tangent_of_graph_cards _ P Q psize qsize connected)

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- The mixed-width integer screen in the registered witness coordinates.
It supplies all generic weighted normal equations after the existing transfer. -/
theorem tangent_of_remainder_capacity (b N r h : ℕ) (hh : 0<h) (width : 3*h≤b)
    (enough : N≤r) (level : r+h=2*b) (cap : r+1≤(r-N+2)*(b/h)) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  let L := b/h-1
  let s := b%h
  have u : 3≤b/h := (Nat.le_div_iff_mul_le hh).mpr width
  have hL : 2≤L := by dsimp [L]; omega
  have hs : s<h := Nat.mod_lt _ hh
  have quotient : L+1=b/h := by dsimp [L]; omega
  have bsize : h*(L+1)+s=b := by rw [quotient]; exact Nat.div_add_mod b h
  have rsize : h*(2*L+1)+2*s=r := by nlinarith only [level,bsize]
  have capacity : r≤(r-N)*(L+1)+(2*L+1) := by
    rw [← quotient] at cap
    nlinarith only [cap]
  have witness := mixed_tangent_of_capacity h L s N hh hL hs.le
    (by rw [rsize]; exact enough) (by rw [rsize]; exact capacity)
  rwa [bsize,rsize] at witness

end CriticalThreeQuotient

namespace CriticalThreeQuotient

private theorem count_of_small_slack {p D r s : ℕ} (hd : 0<D)
    (slack : r*D=p+s) (small : s<D) : p ⌈/⌉ D=r := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr (by nlinarith only [slack])) _
  by_contra! below
  have cover := (ceilDiv_le_iff_le_mul (a:=D) (b:=p) hd).mp le_rfl
  have grow := Nat.mul_le_mul_left D (show (p ⌈/⌉ D)+1≤r by omega)
  rw [Nat.mul_add,Nat.mul_one] at grow
  nlinarith only [grow,cover,slack,small]

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- At the natural endpoint, b≥h² gives the exact expected count. One size
below, the stated linear inequality in b is necessary and sufficient. -/
theorem precise_mixed_counts (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    let r := 2*b-h
    let N := 2*b-3*h+1
    3≤b ∧ 3*h≤b ∧ b≤N ∧ N+1≤r ∧
    (3*b*N ⌈/⌉ (b+N+1)=r ↔ 3*h^2+h≤2*b+1) ∧
    3*b*(N+1) ⌈/⌉ (b+(N+1)+1)=r := by
  intro r N
  have width : 3*h≤b := by
    have prod := Nat.mul_le_mul_right h hh
    nlinarith only [prod,lower]
  have hb : 3≤b := by omega
  have idn : N+3*h=2*b+1 := by dsimp [N]; omega
  have idr : r+h=2*b := Nat.sub_add_cancel (by omega)
  have hp := congrArg (fun t : ℕ => t*h) (Nat.sub_add_cancel (by omega : 1≤h))
  have s₁ : r*(b+N+1)=3*b*N+(3*h*(h-1)+b+h) := by
    have e := congrArg (fun t : ℕ => t*(b+N+1)) idr
    have f := congrArg (fun t : ℕ => t*b) idn
    have g := congrArg (fun t : ℕ => t*h) idn
    nlinarith only [e,f,g,hp]
  have s₂ : r*(b+(N+1)+1)=3*b*(N+1)+3*h*(h-1) := by nlinarith only [s₁,idr]
  have small : 3*h*(h-1)<b+(N+1)+1 := by nlinarith only [lower,idn,hp]
  refine ⟨hb,width,by omega,by omega,⟨?_,?_⟩,count_of_small_slack (by omega) s₂ small⟩
  · intro count
    by_contra! fail
    have pred := Nat.sub_add_cancel (by omega : 1≤r)
    have next := congrArg (fun t : ℕ => t*(b+N+1)) pred
    have smaller : 3*b*N ⌈/⌉ (b+N+1)≤r-1 := (ceilDiv_le_iff_le_mul (by omega)).mpr
      (by nlinarith only [s₁,fail,next,hp,idn])
    omega
  · intro admissible
    apply count_of_small_slack (by omega) s₁
    nlinarith only [admissible,idn,hp]

/-- At the two adjacent sizes, the mixed interval test reduces respectively
to an automatic inequality and a condition on b modulo h. -/
theorem precise_mixed_capacity (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    let r := 2*b-h
    let N := 2*b-3*h+1
    r+1≤(r-N+2)*(b/h) ∧ (r+1≤(r-(N+1)+2)*(b/h) ↔ 2*(b%h)<h) := by
  intro r N
  have width := (precise_mixed_counts h b hh lower).2.1
  have d : h≤b/h := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [sq] using lower)
  have s := Nat.mod_lt b (by omega : 0<h)
  have euclid := Nat.div_add_mod b h
  have idn : N+3*h=2*b+1 := by dsimp [N]; omega
  have idr : r+h=2*b := Nat.sub_add_cancel (by omega)
  have enough : N+1≤r := by omega
  have q₁ : r-N+2=2*h+1 := by have := Nat.sub_add_cancel (by omega : N≤r); omega
  have q₂ : r-(N+1)+2=2*h := by have := Nat.sub_add_cancel enough; omega
  rw [q₁,q₂]
  have lim : b%h+1≤h := by omega
  constructor
  · nlinarith only [euclid,idr,d,lim]
  · constructor <;> intro edge <;> nlinarith only [euclid,idr,edge]

end CriticalThreeQuotient

namespace CriticalThreePerturbation

theorem nonzero_parameter {I J : Type*} [Fintype I] [Fintype J]
    (A B : (I → ℂ) →ₗ[ℂ] (J → ℂ)) (good : Function.Injective A) :
    ∃ z : ℂ, z≠0 ∧ Function.Injective (A+z • B) := by
  let a : (I → ℂ) →L[ℂ] (J → ℂ) := LinearMap.toContinuousLinearMap A
  let b : (I → ℂ) →L[ℂ] (J → ℂ) := LinearMap.toContinuousLinearMap B
  let O := {z : ℂ | Function.Injective (a+z • b)}
  have op : IsOpen O := ContinuousLinearMap.isOpen_injective.preimage
    (continuous_const.add (continuous_id.smul continuous_const))
  have zero : (0:ℂ)∈O := by
    change Function.Injective (a+(0:ℂ) • b)
    have eq : a+(0:ℂ) • b=a := by
      ext x j
      change a x j + 0*b x j=a x j
      ring
    rw [eq]
    exact good
  obtain ⟨z,hz,hne⟩ := (dense_compl_singleton (0:ℂ)).exists_mem_open op ⟨0,zero⟩
  exact ⟨z,hz,hne⟩

end CriticalThreePerturbation

namespace CriticalThreePerturbation

/-- Injectivity of the first-order obstruction from the kernel of A to its
cokernel guarantees an injective pencil at a nonzero complex parameter. -/
theorem first_order_injective {I J : Type*} [Fintype I] [Fintype J]
    (A B : (I → ℂ) →ₗ[ℂ] (J → ℂ))
    (test : ∀ x, A x=0 → B x∈LinearMap.range A → x=0) :
    ∃ z : ℂ, z≠0 ∧ Function.Injective (A+z • B) := by
  classical
  let Q := (J→ℂ) ⧸ LinearMap.range A
  let dim := Module.finrank ℂ Q
  let coord := (Module.finBasis ℂ Q).equivFun
  let π : (J→ℂ) →ₗ[ℂ] (Fin dim→ℂ) := coord.toLinearMap.comp (LinearMap.range A).mkQ
  let aug : (I→ℂ) →ₗ[ℂ] (J ⊕ Fin dim→ℂ) := LinearMap.pi (fun j => j.elim
    (fun i => (LinearMap.proj i).comp A) (fun i => (LinearMap.proj i).comp (π.comp B)))
  let side : (I→ℂ) →ₗ[ℂ] (J ⊕ Fin dim→ℂ) := LinearMap.pi (fun j => j.elim
    (fun i => (LinearMap.proj i).comp B) (fun _ => 0))
  have vanish (v : J→ℂ) : π v=0 ↔ v∈LinearMap.range A := by
    change coord ((LinearMap.range A).mkQ v)=0 ↔ _
    rw [← coord.map_zero,coord.injective.eq_iff]
    exact Submodule.Quotient.mk_eq_zero _
  have inj : Function.Injective aug := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    have hx' : aug x=0 := hx
    exact (Submodule.mem_bot ℂ).mpr (test x (funext fun j => congrFun hx' (.inl j))
      ((vanish _).mp (funext fun j => congrFun hx' (.inr j))))
  obtain ⟨z,nz,good⟩ := nonzero_parameter aug side inj
  refine ⟨z,nz,LinearMap.ker_eq_bot.mp (bot_unique ?_)⟩
  intro x hx
  have hx' : A x+z • B x=0 := hx
  have bz : z • B x∈LinearMap.range A := by
    rw [show z • B x=-(A x) from eq_neg_of_add_eq_zero_right hx']
    exact (LinearMap.range A).neg_mem ⟨x,rfl⟩
  have hb : B x∈LinearMap.range A := by
    have h := (LinearMap.range A).smul_mem z⁻¹ bz
    simpa only [inv_smul_smul₀ nz] using h
  have zero : (aug+z • side) x=0 := by
    funext j
    rcases j with i|i
    · exact congrFun hx' i
    · change π (B x) i+z*0=0
      rw [(vanish _).mpr hb]
      simp
  exact (Submodule.mem_bot ℂ).mpr (good (zero.trans (map_zero _).symm))

end CriticalThreePerturbation

namespace CriticalThreePerturbation

/-- A finite Fourier perturbation may couple many modes in each cycle.
The zeroth-order nullspace is tested by the weighted sums on the marked
cycles. The first-order kernel-to-cokernel criterion then gives injectivity. -/
theorem multipulse_frequency_kernel {G U V M H : Type*} [AddCommGroup G] [Fintype G]
    [Fintype U] [Fintype V] [Fintype M] [Fintype H] (one d : G) (pulse : H → G) (weight : H → ℂ)
    (unit : G → U → G) (base : G → V → G) (target pivot : M → G)
    (edge : ∀ a, ∃ v, base (target a) v=pivot a)
    (paths : ∀ a, ∀ f : G → ℂ, (∀ u, f (unit (target a) u+one)=f (unit (target a) u)) →
      f (pivot a+d)=f (pivot a))
    (baseKernel : ∀ F : G → G → ℂ,
      (∀ k u, F k (unit k u+one)=F k (unit k u)) → (∀ k v, F k (base k v+d)=F k (base k v)) →
      (∀ a, ∑ l, weight l*(F (target a+pulse l-d) (pivot a+pulse l)-
        F (target a+pulse l-d) (pivot a))=0) → ∀ k i j, F k i=F k j) :
    ∃ z : ℂ, z≠0 ∧ ∀ F : G → G → ℂ,
      (∀ k u, F k (unit k u+one)=F k (unit k u)) →
      (∀ k v, F k (base k v+d)-F k (base k v)+ z*
        (∑ l, weight l*(F (k+pulse l-d) (base k v+pulse l)-F (k+pulse l-d) (base k v)))=0) →
      ∀ k i j, F k i=F k j := by
  classical
  let Row := G ⊕ ((G×U) ⊕ (G×V))
  let Col := G×G
  let at' (k i : G) : (Col → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (k,i)
  let diff (k i c : G) := at' k (i+c)-at' k i
  let mix (k i : G) := ∑ l, weight l • diff (k+pulse l-d) i (pulse l)
  have readMix (k i : G) (x : Col → ℂ) : mix k i x=
      ∑ l, weight l*(x (k+pulse l-d,i+pulse l)-x (k+pulse l-d,i)) := by
    simp [mix,diff,at',LinearMap.sum_apply]
  let A : (Col → ℂ) →ₗ[ℂ] (Row → ℂ) := LinearMap.pi fun row => row.elim
    (fun k => at' k 0) (Sum.elim (fun u => diff u.1 (unit u.1 u.2) one)
      (fun v => diff v.1 (base v.1 v.2) d))
  let B : (Col → ℂ) →ₗ[ℂ] (Row → ℂ) := LinearMap.pi fun row => row.elim (fun _ => 0)
    (Sum.elim (fun _ => 0) (fun v => mix v.1 (base v.1 v.2)))
  have schur (x : Col → ℂ) (ax : A x=0) (bx : B x∈LinearMap.range A) : x=0 := by
    obtain ⟨y,hy⟩ := bx
    have yUnit (k : G) (u : U) : y (k,unit k u+one)=y (k,unit k u) :=
      sub_eq_zero.mp (congrFun hy (.inr (.inl (k,u))))
    have added (a : M) : ∑ l, weight l*(x (target a+pulse l-d,pivot a+pulse l)-
        x (target a+pulse l-d,pivot a))=0 := by
      obtain ⟨v,hv⟩ := edge a
      have h := congrFun hy (.inr (.inr (target a,v)))
      change y (target a,base (target a) v+d)-y (target a,base (target a) v)=mix _ _ x at h
      rw [hv,paths a (fun i => y (target a,i)) (yUnit _),sub_self,readMix] at h
      exact h.symm
    have flat := baseKernel (fun k i => x (k,i))
      (fun k u => sub_eq_zero.mp (congrFun ax (.inr (.inl (k,u)))))
      (fun k v => sub_eq_zero.mp (congrFun ax (.inr (.inr (k,v))))) added
    funext ⟨k,i⟩
    exact (flat k i 0).trans (congrFun ax (.inl k))
  obtain ⟨z,nz,inj⟩ := first_order_injective A B schur
  refine ⟨z,nz,?_⟩
  intro F units slopes
  let x (v : Col) := F v.1 v.2-F v.1 0
  have kernel : (A+z • B) x=0 := by
    funext row
    rcases row with k | unitRow | slopeRow
    · change x (k,0)+z*0=0
      simp [x]
    · obtain ⟨k,u⟩ := unitRow
      change (x (k,unit k u+one)-x (k,unit k u))+z*0=0
      simp [x,units]
    · obtain ⟨k,v⟩ := slopeRow
      change (x (k,base k v+d)-x (k,base k v))+z * mix k (base k v) x=0
      rw [readMix]
      simpa only [x,sub_sub_sub_cancel_right] using slopes k v
  have zx : x=0 := inj (kernel.trans (map_zero _).symm)
  intro k i j
  exact (sub_eq_zero.mp (congrFun zx (k,i))).trans (sub_eq_zero.mp (congrFun zx (k,j))).symm

end CriticalThreePerturbation

namespace CriticalThreePerturbation

/-- A finite sum of Fourier characters in the first-factor deformation
induces the corresponding weighted obstruction across different modes. -/
theorem multipulse_commutators {G I U V M H : Type*} [AddCommGroup G] [Fintype G] [Fintype I]
    [Fintype U] [Fintype V] [Fintype M] [Fintype H] (χ : G → I → ℂ)
    (law : ∀ a b t, χ (a+b) t=χ a t*χ b t)
    (fourier : Function.Injective (fun N : I → I → ℂ => fun i j : G =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)))
    (one d : G) (pulse : H→G) (weight : H→ℂ) (distinct : Function.Injective (χ one))
    (P : U → G) (Q : V → G) (target pivot : M → G) (inP : ∀ a, ∃ u, P u=pivot a)
    (paths : ∀ a, ∀ f : G → ℂ, (∀ u, f (P u+one)=f (P u)) →
      (∀ v, f (target a-Q v-one)=f (target a-Q v)) → f (pivot a+d)=f (pivot a))
    (baseKernel : ∀ F : G → G → ℂ,
      (∀ k u, F k (P u+one)=F k (P u) ∧ F k (P u+d)=F k (P u)) →
      (∀ k v, F k (k-Q v-one)=F k (k-Q v) ∧ F k (k-Q v-d)=F k (k-Q v)) →
      (∀ a, ∑ l, weight l*(F (target a+pulse l-d) (pivot a+pulse l)-
        F (target a+pulse l-d) (pivot a))=0) → ∀ k i j, F k i=F k j) :
    ∃ z : ℂ, z≠0 ∧
    let μ (s : I) := χ d s+z*(∑ l, weight l*χ (pulse l) s)
    ∀ E : I → I → ℂ,
      (∀ u t, ∑ s, χ (P u) s*((χ one s-χ one t)*E s t)=0) →
      (∀ u t, ∑ s, χ (P u) s*((μ s-μ t)*E s t)=0) →
      (∀ v s, ∑ t, ((χ one s-χ one t)*E s t)*χ (Q v) t=0) →
      (∀ v s, ∑ t, ((μ s-μ t)*E s t)*χ (Q v) t=0) →
      ∀ s t, s≠t → E s t=0 := by
  classical
  let start (c k : G) : U ⊕ V → G := Sum.elim P (fun v => k-Q v-c)
  have path' (a : M) (f : G → ℂ)
      (hyp : ∀ u, f (start one (target a) u+one)=f (start one (target a) u)) :
      f (pivot a+d)=f (pivot a) := by
    apply paths a f (fun u => hyp (.inl u))
    intro v
    simpa only [start,Sum.elim_inr,sub_add_cancel] using (hyp (.inr v)).symm
  have global (F : G→G→ℂ) (hu : ∀ k u, F k (start one k u+one)=F k (start one k u))
      (hd : ∀ k u, F k (start d k u+d)=F k (start d k u)) :=
    baseKernel F (fun k u => ⟨hu k (.inl u),hd k (.inl u)⟩)
      (fun k v => ⟨by simpa only [start,Sum.elim_inr,sub_add_cancel] using (hu k (.inr v)).symm,
        by simpa only [start,Sum.elim_inr,sub_add_cancel] using (hd k (.inr v)).symm⟩)
  obtain ⟨z,nz,works⟩ := multipulse_frequency_kernel one d pulse weight (start one) (start d)
    target pivot (fun a => by obtain ⟨u,hu⟩ := inP a; exact ⟨.inl u,hu⟩) path' global
  refine ⟨z,nz,?_⟩
  intro μ E leftOne leftMu rightOne rightMu
  let M₀ (i j : G) := ∑ s, ∑ t, χ i s*(E s t*χ j t)
  let F (k i : G) := M₀ i (k-i)
  let C (g : I → ℂ) (i j : G) := ∑ s, ∑ t, χ i s*(((g s-g t)*E s t)*χ j t)
  have shift (c i j : G) : M₀ (i+c) j-M₀ i (j+c)=C (χ c) i j := by
    simp only [M₀,C,law,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have delta (k i c : G) : F k (i+c)-F k i=C (χ c) i (k-i-c) := by
    rw [← shift]
    congr 1 <;> dsimp [F] <;> congr 1 <;> abel
  let D (i j : G) : (I→ℂ) →ₗ[ℂ] ℂ := ∑ s, ∑ t,
    (χ i s*(E s t*χ j t)) • ((LinearMap.proj s : (I→ℂ) →ₗ[ℂ] ℂ)-(LinearMap.proj t))
  have eval (i j : G) (g : I→ℂ) : D i j g=C g i j := by
    simp only [D,C,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.sub_apply,LinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have form : μ=χ d+z • (∑ l, weight l • χ (pulse l)) := by
    funext s
    simp [μ,Finset.sum_apply]
  have linear (i j : G) : C μ i j=C (χ d) i j+z*(∑ l, weight l*C (χ (pulse l)) i j) := by
    simp only [← eval,form,map_add,map_smul,map_sum,smul_eq_mul]
  have leftZero (g : I → ℂ) (rel : ∀ u t, ∑ s, χ (P u) s*((g s-g t)*E s t)=0)
      (u : U) (j : G) : C g (P u) j=0 := by
    unfold C
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, (∑ s, χ (P u) s*((g s-g t)*E s t))*χ j t := by simp only [Finset.sum_mul,mul_assoc]
      _ = 0 := by simp [rel]
  have rightZero (g : I → ℂ) (rel : ∀ v s, ∑ t, ((g s-g t)*E s t)*χ (Q v) t=0)
      (v : V) (i : G) : C g i (Q v)=0 := by simp only [C,← Finset.mul_sum,rel,mul_zero,Finset.sum_const_zero]
  have edges (c : G) (g : I → ℂ) (lrel : ∀ u t, ∑ s,χ (P u) s*((g s-g t)*E s t)=0)
      (rrel : ∀ v s, ∑ t, ((g s-g t)*E s t)*χ (Q v) t=0)
      (k : G) (u : U ⊕ V) : C g (start c k u) (k-start c k u-c)=0 := by
    rcases u with u | v
    · exact leftZero g lrel u _
    · change C g (k-Q v-c) (k-(k-Q v-c)-c)=0
      rw [show k-(k-Q v-c)-c=Q v by abel]
      exact rightZero g rrel v _
  have flat := works F
    (fun k u => sub_eq_zero.mp ((delta k _ one).trans (edges one _ leftOne rightOne k u)))
    (fun k u => by
      simp only [delta]
      have arg (l : H) : k+pulse l-d-start d k u-pulse l=k-start d k u-d := by abel
      simp only [arg,← linear]
      exact edges d _ leftMu rightMu k u)
  have zero (i j : G) : C (χ one) i j=0 := by
    rw [← shift,sub_eq_zero]
    have hh := flat (i+j+one) (i+one) i
    dsimp only [F] at hh
    rwa [show i+j+one-(i+one)=j by abel,show i+j+one-i=j+one by abel] at hh
  have annihilated : (fun s t => (χ one s-χ one t)*E s t)=(0 : I → I → ℂ) := by
    apply fourier
    funext i j
    simpa only [Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero] using zero i j
  intro s t ne
  have h := congrFun (congrFun annihilated s) t
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

end CriticalThreePerturbation

namespace CriticalThreePerturbation

/-- A finite collection of character shifts repairs a cyclic CP tangent
whenever the corresponding first-order cycle tests distinguish the entire
zeroth-order nullspace. Both the number of shifts and the marks are arbitrary. -/
theorem multipulse_tangent_of_graph_cards {r b n : ℕ} [NeZero r]
    {H A : Type*} [Fintype H] [Fintype A] (d : ZMod r) (pulse : H→ZMod r) (weight : H→ℂ)
    (P Q : Finset (ZMod r)) (pCard : P.card+b=r) (qCard : Q.card+n=r)
    (target pivot : A → ZMod r) (inP : ∀ a, pivot a∈P)
    (paths : ∀ a, ∀ f : ZMod r → ℂ, (∀ u∈P, f (u+1)=f u) →
      (∀ v∈Q, f (target a-v-1)=f (target a-v)) → f (pivot a+d)=f (pivot a))
    (baseKernel : ∀ F : ZMod r → ZMod r → ℂ,
      (∀ k, ∀ u∈P, F k (u+1)=F k u ∧ F k (u+d)=F k u) →
      (∀ k, ∀ v∈Q, F k (k-v-1)=F k (k-v) ∧ F k (k-v-d)=F k (k-v)) →
      (∀ a, ∑ l, weight l*(F (target a+pulse l-d) (pivot a+pulse l)-
        F (target a+pulse l-d) (pivot a))=0) → ∀ k i j, F k i=F k j) :
    let χ (i : ZMod r) (s : Fin r) : ℂ := ZMod.stdAddChar ((ZMod.finEquiv r s)*i)
    ∃ z : ℂ, z≠0 ∧ ∃ y : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ,
    let x (s : Fin r) : Fin 3→ℂ := ![1,χ 1 s,χ d s+z*(∑ l,weight l*χ (pulse l) s)]
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ a : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ c : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (a t i*(y t j*w t k) + x t i*(v t j*w t k) + x t i*(y t j*c t k)) := by
  classical
  dsimp only
  have choose {m : ℕ} (F : Finset (ZMod r)) (count : F.card+m=r) :
      ∃ J : Fin m ↪ ZMod r, ∀ i, J i∉F := by
    have size : Fintype.card (Fin m)=Fintype.card (↥(Fᶜ) : Type) := by
      rw [Fintype.card_fin,Fintype.card_coe,Finset.card_compl,ZMod.card]
      omega
    let e := Fintype.equivOfCardEq size
    exact ⟨e.toEmbedding.trans (Function.Embedding.subtype _),
      fun i => Finset.mem_compl.mp (e i).property⟩
  obtain ⟨Y,hy⟩ := choose P pCard
  obtain ⟨Z,hz⟩ := choose Q qCard
  let e := (ZMod.finEquiv r).toEquiv
  let χ (i : ZMod r) (s : Fin r) : ℂ := ZMod.stdAddChar (e s*i)
  have law (a b : ZMod r) (t : Fin r) : χ (a+b) t=χ a t*χ b t := by
    simp only [χ,mul_add,AddChar.map_add_eq_mul]
  have injective : Function.Injective (χ 1) := by
    simpa only [χ,mul_one,Function.comp_def] using ZMod.injective_stdAddChar.comp e.injective
  have orth (i j : ZMod r) : ∑ s, χ i s*χ (-j) s = if i=j then (r:ℂ) else 0 := by
    calc
      _ = ∑ s : Fin r, ZMod.stdAddChar (e s*(i-j)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← law,← sub_eq_add_neg]
      _ = ∑ t : ZMod r, ZMod.stdAddChar (t*(i-j)) := e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (t*(i-j)))
      _ = _ := by
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _),ZMod.card]
        by_cases h : i=j <;> simp [h,sub_eq_zero]
  have separates (a b : Fin r → ℂ) (test : ∀ i : ZMod r, ∑ s, χ i s*a s=∑ s, χ i s*b s) : a=b := by
    have eq : (fun j => a (e.symm j))=(fun j => b (e.symm j)) := by
      apply ZMod.dft.injective
      funext i
      rw [ZMod.dft_apply,ZMod.dft_apply]
      simp only [smul_eq_mul]
      rw [← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*a (e.symm t)),
        ← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*b (e.symm t))]
      simpa only [e.symm_apply_apply,χ,mul_neg] using test (-i)
    funext s
    simpa only [e.symm_apply_apply] using congrFun eq (e s)
  have fourier : Function.Injective (fun N : Fin r → Fin r → ℂ => fun i j : ZMod r =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)) := by
    intro A B he
    have each (j : ZMod r) : (fun s => ∑ t, A s t*χ j t)=(fun s => ∑ t, B s t*χ j t) := by
      apply separates
      intro i
      simpa only [Finset.mul_sum] using congrFun (congrFun he i) j
    funext s
    apply separates
    intro j
    simpa only [mul_comm (χ j _)] using congrFun (each j) s
  let frame {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin r) (Fin m) ℂ := fun s j => χ (-(H j)) s
  let dual {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin m) (Fin r) ℂ := fun j s => χ (H j) s / r
  have frameId {m : ℕ} (H : Fin m ↪ ZMod r) : dual H * frame H=1 := by
    ext i j
    change (∑ s, (χ (H i) s/r)*χ (-(H j)) s)=_
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,orth]
    by_cases h : i=j
    · subst j
      simp [NeZero.ne r]
    · simp [h,H.injective.ne h]
  have embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) ℂ => frame Y*N*(frame Z).transpose) := by
    intro A B eq
    have extract (N : Matrix (Fin b) (Fin n) ℂ) :
        (dual Y)*(frame Y*N*(frame Z).transpose)*(dual Z).transpose=N := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,frameId,Matrix.one_mul,Matrix.mul_assoc,
        ← Matrix.transpose_mul,frameId,Matrix.transpose_one,Matrix.mul_one]
    exact (extract A).symm.trans ((congrArg (fun N => (dual Y)*N*(dual Z).transpose) eq).trans (extract B))
  have annihilate {m : ℕ} (A : Finset (ZMod r)) (H : Fin m ↪ ZMod r) (avoid : ∀ j, H j∉A) :
      (Matrix.of (fun (i : A) (t : Fin r) => χ i.val t))*frame H=0 := by
    ext i j
    change (∑ s, χ i.val s*χ (-(H j)) s)=0
    have ne : i.val≠H j := fun h => avoid j (h ▸ i.property)
    rw [orth,if_neg ne]
  obtain ⟨z,nz,exactPair⟩ := multipulse_commutators χ law fourier 1 d pulse weight injective
    (fun p : P => p.val) (fun q : Q => q.val) target pivot
    (fun a => ⟨⟨pivot a,inP a⟩,rfl⟩)
    (fun a f h₁ h₂ => paths a f (fun u hu => h₁ ⟨u,hu⟩) (fun v hv => h₂ ⟨v,hv⟩))
    (fun F h₁ h₂ h₃ => baseKernel F (fun k u hu => h₁ k ⟨u,hu⟩) (fun k v hv => h₂ k ⟨v,hv⟩) h₃)
  refine ⟨z,nz,frame Y,frame Z,?_⟩
  exact CriticalThreeQuotient.tangent_of_commutators (χ 1)
    (fun s => χ d s+z*(∑ l,weight l*χ (pulse l) s)) injective
    (frame Y) (frame Z) _ _ (annihilate P Y hy) (annihilate Q Z hz) embed exactPair

end CriticalThreePerturbation

namespace CriticalThreePerturbation

/-- Only two kinds of information are needed to repair a frequency graph:
a unit-edge path at the shifted target and the resulting fixed comparison
at the original frequency. The same nonzero parameter works on every mode. -/
theorem perturbed_frequency_kernel {G U V M : Type*} [AddCommGroup G] [Fintype G]
    [Fintype U] [Fintype V] [Fintype M] (one d e : G)
    (unit : G → U → G) (base : G → V → G) (src pivot : M → G)
    (edge : ∀ a, ∃ v, base (src a-e+d) v=pivot a)
    (paths : ∀ a, ∀ f : G → ℂ, (∀ u, f (unit (src a-e+d) u+one)=f (unit (src a-e+d) u)) →
      f (pivot a+d)=f (pivot a))
    (connected : ∀ k, ∀ f : G → ℂ,
      (∀ u, f (unit k u+one)=f (unit k u)) → (∀ v, f (base k v+d)=f (base k v)) →
      (∀ a, k=src a → f (pivot a+e)=f (pivot a)) → ∀ i j, f i=f j) :
    ∃ z : ℂ, z≠0 ∧ ∀ F : G → G → ℂ,
      (∀ k u, F k (unit k u+one)=F k (unit k u)) →
      (∀ k v, F k (base k v+d)-F k (base k v) +
        z*(F (k+e-d) (base k v+e)-F (k+e-d) (base k v))=0) →
      ∀ k i j, F k i=F k j := by
  classical
  let Row := G ⊕ ((G×U) ⊕ ((G×V) ⊕ M))
  let Col := G × G
  let at' (k i : G) : (Col → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (k,i)
  let diff (k i c : G) := at' k (i+c)-at' k i
  let A : (Col → ℂ) →ₗ[ℂ] (Row → ℂ) := LinearMap.pi fun row => row.elim
    (fun k => at' k 0) (Sum.elim (fun u => diff u.1 (unit u.1 u.2) one)
      (Sum.elim (fun v => diff v.1 (base v.1 v.2) d) (fun a => diff (src a) (pivot a) e)))
  let B : (Col → ℂ) →ₗ[ℂ] (Row → ℂ) := LinearMap.pi fun row => row.elim (fun _ => 0)
    (Sum.elim (fun _ => 0) (Sum.elim (fun v => diff (v.1+e-d) (base v.1 v.2) e) (fun _ => 0)))
  have good : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    have zero : A x=0 := hx
    apply (Submodule.mem_bot ℂ).mpr
    funext ⟨k,i⟩
    have all := connected k (fun j => x (k,j))
      (fun u => sub_eq_zero.mp (congrFun zero (.inr (.inl (k,u)))))
      (fun v => sub_eq_zero.mp (congrFun zero (.inr (.inr (.inl (k,v))))))
      (fun a eq => by subst k; exact sub_eq_zero.mp (congrFun zero (.inr (.inr (.inr a)))))
    exact (all i 0).trans (congrFun zero (.inl k))
  obtain ⟨z,nz,inj⟩ := nonzero_parameter A B good
  refine ⟨z,nz,?_⟩
  intro F units slopes
  have fixed (a : M) : F (src a) (pivot a+e)=F (src a) (pivot a) := by
    obtain ⟨v,location⟩ := edge a
    have h := slopes (src a-e+d) v
    rw [location,paths a _ (units _),sub_self,zero_add,
      show src a-e+d+e-d=src a by abel] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left nz)
  let x (v : Col) := F v.1 v.2-F v.1 0
  have kernel : (A+z • B) x=0 := by
    funext row
    rcases row with k | unitRow | slopeRow | mark
    · change x (k,0)+z*0=0
      simp [x]
    · obtain ⟨k,u⟩ := unitRow
      change (x (k,unit k u+one)-x (k,unit k u))+z*0=0
      simp [x,units]
    · obtain ⟨k,v⟩ := slopeRow
      change (x (k,base k v+d)-x (k,base k v))+
        z*(x (k+e-d,base k v+e)-x (k+e-d,base k v))=0
      simpa only [x,sub_sub_sub_cancel_right] using slopes k v
    · change (x (src mark,pivot mark+e)-x (src mark,pivot mark))+z*0=0
      simp [x,fixed]
  have zx : x=0 := inj (kernel.trans (map_zero _).symm)
  intro k i j
  exact (sub_eq_zero.mp (congrFun zx (k,i))).trans (sub_eq_zero.mp (congrFun zx (k,j))).symm

end CriticalThreePerturbation

namespace CriticalThreePerturbation

/-- Tensor normal equations for the perturbed first factor
(1,χ₁,χ_d+zχ_e) split into shifted frequency equations.
A comparison recovered along each specified unit path repairs the base graph. -/
theorem perturbed_commutators {G I U V M : Type*} [AddCommGroup G] [Fintype G] [Fintype I]
    [Fintype U] [Fintype V] [Fintype M] (χ : G → I → ℂ)
    (law : ∀ a b t, χ (a+b) t=χ a t*χ b t)
    (fourier : Function.Injective (fun N : I → I → ℂ => fun i j : G =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)))
    (one d e : G) (distinct : Function.Injective (χ one)) (P : U → G) (Q : V → G)
    (src pivot : M → G) (inP : ∀ a, ∃ u, P u=pivot a)
    (paths : ∀ a, ∀ f : G → ℂ, (∀ u, f (P u+one)=f (P u)) →
      (∀ v, f (src a-e+d-Q v-one)=f (src a-e+d-Q v)) → f (pivot a+d)=f (pivot a))
    (graphs : ∀ k, ∀ f : G → ℂ,
      (∀ u, f (P u+one)=f (P u) ∧ f (P u+d)=f (P u)) →
      (∀ v, f (k-Q v-one)=f (k-Q v) ∧ f (k-Q v-d)=f (k-Q v)) →
      (∀ a, k=src a → f (pivot a+e)=f (pivot a)) → ∀ i j, f i=f j) :
    ∃ z : ℂ, z≠0 ∧
    let μ (s : I) := χ d s+z*χ e s
    ∀ E : I → I → ℂ,
      (∀ u t, ∑ s, χ (P u) s*((χ one s-χ one t)*E s t)=0) →
      (∀ u t, ∑ s, χ (P u) s*((μ s-μ t)*E s t)=0) →
      (∀ v s, ∑ t, ((χ one s-χ one t)*E s t)*χ (Q v) t=0) →
      (∀ v s, ∑ t, ((μ s-μ t)*E s t)*χ (Q v) t=0) →
      ∀ s t, s≠t → E s t=0 := by
  let start (c k : G) : U ⊕ V → G := Sum.elim P (fun v => k-Q v-c)
  have path' (a : M) (f : G → ℂ)
      (hyp : ∀ u, f (start one (src a-e+d) u+one)=f (start one (src a-e+d) u)) :
      f (pivot a+d)=f (pivot a) := by
    apply paths a f (fun u => hyp (.inl u))
    intro v
    simpa only [start,Sum.elim_inr,sub_add_cancel] using (hyp (.inr v)).symm
  have graph' (k : G) (f : G → ℂ) (hu : ∀ u, f (start one k u+one)=f (start one k u))
      (hd : ∀ u, f (start d k u+d)=f (start d k u)) :=
    graphs k f (fun u => ⟨hu (.inl u),hd (.inl u)⟩)
      (fun v => ⟨by simpa only [start,Sum.elim_inr,sub_add_cancel] using (hu (.inr v)).symm,
        by simpa only [start,Sum.elim_inr,sub_add_cancel] using (hd (.inr v)).symm⟩)
  obtain ⟨z,nz,works⟩ := perturbed_frequency_kernel one d e (start one) (start d) src pivot
    (fun a => by obtain ⟨u,hu⟩ := inP a; exact ⟨.inl u,hu⟩) path' graph'
  refine ⟨z,nz,?_⟩
  intro μ E leftOne leftMu rightOne rightMu
  let M₀ (i j : G) := ∑ s, ∑ t, χ i s*(E s t*χ j t)
  let F (k i : G) := M₀ i (k-i)
  let C (g : I → ℂ) (i j : G) := ∑ s, ∑ t, χ i s*(((g s-g t)*E s t)*χ j t)
  have shift (c i j : G) : M₀ (i+c) j-M₀ i (j+c)=C (χ c) i j := by
    simp only [M₀,C,law,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have delta (k i c : G) : F k (i+c)-F k i=C (χ c) i (k-i-c) := by
    rw [← shift]
    congr 1 <;> dsimp [F] <;> congr 1 <;> abel
  have linear (i j : G) : C μ i j=C (χ d) i j+z*C (χ e) i j := by
    simp only [C,μ,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have leftZero (g : I → ℂ) (rel : ∀ u t, ∑ s, χ (P u) s*((g s-g t)*E s t)=0)
      (u : U) (j : G) : C g (P u) j=0 := by
    unfold C
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, (∑ s, χ (P u) s*((g s-g t)*E s t))*χ j t := by simp only [Finset.sum_mul,mul_assoc]
      _ = 0 := by simp [rel]
  have rightZero (g : I → ℂ) (rel : ∀ v s, ∑ t, ((g s-g t)*E s t)*χ (Q v) t=0)
      (v : V) (i : G) : C g i (Q v)=0 := by simp only [C,← Finset.mul_sum,rel,mul_zero,Finset.sum_const_zero]
  have edges (c : G) (g : I → ℂ) (lrel : ∀ u t, ∑ s,χ (P u) s*((g s-g t)*E s t)=0)
      (rrel : ∀ v s, ∑ t, ((g s-g t)*E s t)*χ (Q v) t=0)
      (k : G) (u : U ⊕ V) : C g (start c k u) (k-start c k u-c)=0 := by
    rcases u with u | v
    · exact leftZero g lrel u _
    · change C g (k-Q v-c) (k-(k-Q v-c)-c)=0
      rw [show k-(k-Q v-c)-c=Q v by abel]
      exact rightZero g rrel v _
  have flat := works F
    (fun k u => sub_eq_zero.mp ((delta k _ one).trans (edges one _ leftOne rightOne k u)))
    (fun k u => by
      rw [delta,delta,show k+e-d-start d k u-e=k-start d k u-d by abel,← linear]
      exact edges d _ leftMu rightMu k u)
  have zero (i j : G) : C (χ one) i j=0 := by
    rw [← shift,sub_eq_zero]
    have hh := flat (i+j+one) (i+one) i
    dsimp only [F] at hh
    rwa [show i+j+one-(i+one)=j by abel,show i+j+one-i=j+one by abel] at hh
  have annihilated : (fun s t => (χ one s-χ one t)*E s t)=(0 : I → I → ℂ) := by
    apply fourier
    funext i j
    simpa only [Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero] using zero i j
  intro s t ne
  have h := congrFun (congrFun annihilated s) t
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

end CriticalThreePerturbation

namespace CriticalThreePerturbation

/-- Pure point comparisons obtained from unit-edge paths yield an actual
nonzero complex deformation of the cyclic first factors. The mark index
is arbitrary and finite, allowing repairs at many frequencies. -/
theorem perturbed_tangent_of_graph_cards {r b n : ℕ} [NeZero r] {A : Type*} [Fintype A]
    (d pulse : ZMod r) (P Q : Finset (ZMod r)) (pCard : P.card+b=r) (qCard : Q.card+n=r)
    (src pivot : A → ZMod r) (inP : ∀ a, pivot a∈P)
    (paths : ∀ a, ∀ f : ZMod r → ℂ, (∀ u∈P, f (u+1)=f u) →
      (∀ v∈Q, f (src a-pulse+d-v-1)=f (src a-pulse+d-v)) → f (pivot a+d)=f (pivot a))
    (graphs : ∀ k, ∀ f : ZMod r → ℂ,
      (∀ u∈P, f (u+1)=f u ∧ f (u+d)=f u) →
      (∀ v∈Q, f (k-v-1)=f (k-v) ∧ f (k-v-d)=f (k-v)) →
      (∀ a, k=src a → f (pivot a+pulse)=f (pivot a)) → ∀ i j, f i=f j) :
    let χ (i : ZMod r) (s : Fin r) : ℂ := ZMod.stdAddChar ((ZMod.finEquiv r s)*i)
    ∃ z : ℂ, z≠0 ∧ ∃ y : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ,
    let x (s : Fin r) : Fin 3→ℂ := ![1,χ 1 s,χ d s+z*χ pulse s]
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ a : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ c : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (a t i*(y t j*w t k) + x t i*(v t j*w t k) + x t i*(y t j*c t k)) := by
  classical
  dsimp only
  have choose {m : ℕ} (F : Finset (ZMod r)) (count : F.card+m=r) :
      ∃ J : Fin m ↪ ZMod r, ∀ i, J i∉F := by
    have size : Fintype.card (Fin m)=Fintype.card (↥(Fᶜ) : Type) := by
      rw [Fintype.card_fin,Fintype.card_coe,Finset.card_compl,ZMod.card]
      omega
    let e := Fintype.equivOfCardEq size
    exact ⟨e.toEmbedding.trans (Function.Embedding.subtype _),
      fun i => Finset.mem_compl.mp (e i).property⟩
  obtain ⟨Y,hy⟩ := choose P pCard
  obtain ⟨Z,hz⟩ := choose Q qCard
  let e := (ZMod.finEquiv r).toEquiv
  let χ (i : ZMod r) (s : Fin r) : ℂ := ZMod.stdAddChar (e s*i)
  have law (a b : ZMod r) (t : Fin r) : χ (a+b) t=χ a t*χ b t := by
    simp only [χ,mul_add,AddChar.map_add_eq_mul]
  have injective : Function.Injective (χ 1) := by
    simpa only [χ,mul_one,Function.comp_def] using ZMod.injective_stdAddChar.comp e.injective
  have orth (i j : ZMod r) : ∑ s, χ i s*χ (-j) s = if i=j then (r:ℂ) else 0 := by
    calc
      _ = ∑ s : Fin r, ZMod.stdAddChar (e s*(i-j)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← law,← sub_eq_add_neg]
      _ = ∑ t : ZMod r, ZMod.stdAddChar (t*(i-j)) := e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (t*(i-j)))
      _ = _ := by
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _),ZMod.card]
        by_cases h : i=j <;> simp [h,sub_eq_zero]
  have separates (a b : Fin r → ℂ) (test : ∀ i : ZMod r, ∑ s, χ i s*a s=∑ s, χ i s*b s) : a=b := by
    have eq : (fun j => a (e.symm j))=(fun j => b (e.symm j)) := by
      apply ZMod.dft.injective
      funext i
      rw [ZMod.dft_apply,ZMod.dft_apply]
      simp only [smul_eq_mul]
      rw [← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*a (e.symm t)),
        ← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*b (e.symm t))]
      simpa only [e.symm_apply_apply,χ,mul_neg] using test (-i)
    funext s
    simpa only [e.symm_apply_apply] using congrFun eq (e s)
  have fourier : Function.Injective (fun N : Fin r → Fin r → ℂ => fun i j : ZMod r =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)) := by
    intro A B he
    have each (j : ZMod r) : (fun s => ∑ t, A s t*χ j t)=(fun s => ∑ t, B s t*χ j t) := by
      apply separates
      intro i
      simpa only [Finset.mul_sum] using congrFun (congrFun he i) j
    funext s
    apply separates
    intro j
    simpa only [mul_comm (χ j _)] using congrFun (each j) s
  let frame {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin r) (Fin m) ℂ := fun s j => χ (-(H j)) s
  let dual {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin m) (Fin r) ℂ := fun j s => χ (H j) s / r
  have frameId {m : ℕ} (H : Fin m ↪ ZMod r) : dual H * frame H=1 := by
    ext i j
    change (∑ s, (χ (H i) s/r)*χ (-(H j)) s)=_
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,orth]
    by_cases h : i=j
    · subst j
      simp [NeZero.ne r]
    · simp [h,H.injective.ne h]
  have embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) ℂ => frame Y*N*(frame Z).transpose) := by
    intro A B eq
    have extract (N : Matrix (Fin b) (Fin n) ℂ) :
        (dual Y)*(frame Y*N*(frame Z).transpose)*(dual Z).transpose=N := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,frameId,Matrix.one_mul,Matrix.mul_assoc,
        ← Matrix.transpose_mul,frameId,Matrix.transpose_one,Matrix.mul_one]
    exact (extract A).symm.trans ((congrArg (fun N => (dual Y)*N*(dual Z).transpose) eq).trans (extract B))
  have annihilate {m : ℕ} (A : Finset (ZMod r)) (H : Fin m ↪ ZMod r) (avoid : ∀ j, H j∉A) :
      (Matrix.of (fun (i : A) (t : Fin r) => χ i.val t))*frame H=0 := by
    ext i j
    change (∑ s, χ i.val s*χ (-(H j)) s)=0
    have ne : i.val≠H j := fun h => avoid j (h ▸ i.property)
    rw [orth,if_neg ne]
  obtain ⟨z,nz,exactPair⟩ := perturbed_commutators χ law fourier 1 d pulse injective
    (fun p : P => p.val) (fun q : Q => q.val) src pivot
    (fun a => ⟨⟨pivot a,inP a⟩,rfl⟩)
    (fun a f h₁ h₂ => paths a f (fun u hu => h₁ ⟨u,hu⟩) (fun v hv => h₂ ⟨v,hv⟩))
    (fun k f h₁ h₂ h₃ => graphs k f (fun u hu => h₁ ⟨u,hu⟩) (fun v hv => h₂ ⟨v,hv⟩) h₃)
  refine ⟨z,nz,frame Y,frame Z,?_⟩
  exact CriticalThreeQuotient.tangent_of_commutators (χ 1) (fun s => χ d s+z*χ pulse s) injective
    (frame Y) (frame Z) _ _ (annihilate P Y hy) (annihilate Q Z hz) embed exactPair

end CriticalThreePerturbation

namespace CriticalThreeQuotient

/-- An equal number of short and long blocks partitions the cyclic group.
The short blocks come first. Their successors' first positions are left centers. -/
theorem half_modes (u d : ℕ) (hu : 0<u) (hd : 3≤d) :
    let r := 4*u*d
    let W := 2*d-1
    let V := 2*d+1
    let sB (j : Fin u) : ZMod r := ((j.val*W:ℕ):ZMod r)
    let lB (j : Fin u) : ZMod r := ((u*W+j.val*V:ℕ):ZMod r)
    ∃ P : Finset (ZMod r), P.card+(2*u*d+u)=r ∧
      (∀ j,∀ i : ℕ,i<d-1 → sB j+(i:ZMod r)∈P) ∧
      (∀ j,∀ i : ℕ,i=0 ∨ 2≤ i ∧ i≤d → lB j+(i:ZMod r)∈P) ∧
      (∀ j,sB j+(W:ZMod r)∈P) ∧
      ∀ x : ZMod r,(∃ j,∃ i : Fin W,x=sB j+(i.val:ZMod r)) ∨
        ∃ j,∃ i : Fin V,x=lB j+(i.val:ZMod r) := by
  classical
  intro r W V sB lB
  let L := d-1
  have predEq : L+1=d := by dsimp [L]; omega
  have hw : W+1=2*d := by dsimp [W]; omega
  have widths : u*W+u*V=r := by
    have z := congrArg (u*·) hw
    change u*(W+1)=u*(2*d) at z
    dsimp [r,V]
    nlinarith only [z]
  have : NeZero r := ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide) hu) (by omega))⟩
  let G := (Fin u × Fin W) ⊕ (Fin u × Fin V)
  let M := (Fin u × Fin L) ⊕ (Fin u × Fin (L+1))
  let slot : G ≃ Fin r :=
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr widths)
  let residue : Fin r ↪ ZMod r :=
    { toFun := fun i => (i.val:ZMod r)
      inj' := by
        intro i j eq
        apply Fin.ext
        have raw := congrArg ZMod.val eq
        simpa only [ZMod.val_natCast_of_lt i.isLt,ZMod.val_natCast_of_lt j.isLt] using raw }
  let enc : G ↪ ZMod r := slot.toEmbedding.trans residue
  have all (x : ZMod r) : ∃ p,enc p=x := by
    obtain ⟨p,hp⟩ := slot.surjective ⟨x.val,x.val_lt⟩
    refine ⟨p,?_⟩
    change ((slot p).val:ZMod r)=x
    rw [hp,ZMod.natCast_zmod_val]
  have seval (j : Fin u) (i : Fin W) : enc (.inl (j,i))=sB j+(i.val:ZMod r) := by
    change ((i.val+W*j.val:ℕ):ZMod r)=((j.val*W:ℕ):ZMod r)+i.val
    push_cast
    ring
  have leval (j : Fin u) (i : Fin V) : enc (.inr (j,i))=lB j+(i.val:ZMod r) := by
    change ((u*W+(i.val+V*j.val):ℕ):ZMod r)=((u*W+j.val*V:ℕ):ZMod r)+i.val
    push_cast
    ring
  obtain ⟨lc,lcrange⟩ := long_centers L
  let lcv : Fin (L+1) ↪ Fin V := lc.trans (finCongr (by dsimp [V]; omega : 2*L+3=V)).toEmbedding
  let sc : Fin L ↪ Fin W := Fin.castLEEmb (by dsimp [W,L]; omega)
  let pick : M ↪ G := ((Function.Embedding.refl (Fin u)).prodMap sc).sumMap
    ((Function.Embedding.refl (Fin u)).prodMap lcv)
  let pe := pick.trans enc
  let P := Finset.univ.map pe
  have smem (j : Fin u) (i : ℕ) (hi : i<d-1) : sB j+(i:ZMod r)∈P := by
    let t : Fin L := ⟨i,hi⟩
    have hm : pe (.inl (j,t))∈P := Finset.mem_map.mpr ⟨.inl (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inl (j,sc t))∈P at hm
    simpa only [seval,show (sc t).val=i from rfl] using hm
  have lmem (j : Fin u) (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤d) : lB j+(i:ZMod r)∈P := by
    obtain ⟨t,ht⟩ := (lcrange i).mpr (predEq ▸ hi)
    have hm : pe (.inr (j,t))∈P := Finset.mem_map.mpr ⟨.inr (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inr (j,lcv t))∈P at hm
    simpa only [leval,show (lcv t).val=(lc t).val from rfl,ht] using hm
  have card : P.card+(2*u*d+u)=r := by
    simp only [P,Finset.card_map,Finset.card_univ,M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    have z := congrArg (u*·) predEq
    change u*(L+1)=u*d at z
    dsimp [r]
    nlinarith only [z]
  refine ⟨P,card,smem,lmem,?_,?_⟩
  · intro j
    by_cases next : j.val+1<u
    · let k : Fin u := ⟨j.val+1,next⟩
      have eq : sB j+(W:ZMod r)=sB k := by
        change ((j.val*W:ℕ):ZMod r)+W=(((j.val+1)*W:ℕ):ZMod r)
        rw [Nat.add_mul,Nat.one_mul,Nat.cast_add]
      rw [eq]
      simpa only [Nat.cast_zero,add_zero] using smem k 0 (by omega)
    · let k : Fin u := ⟨0,hu⟩
      have jk : j.val+1=u := by have := j.isLt; omega
      have eq : sB j+(W:ZMod r)=lB k := by
        change ((j.val*W:ℕ):ZMod r)+W=((u*W+0*V:ℕ):ZMod r)
        rw [Nat.zero_mul,Nat.add_zero,← Nat.cast_add,← Nat.succ_mul,Nat.succ_eq_add_one,jk]
      rw [eq]
      simpa only [Nat.cast_zero,add_zero] using lmem k 0 (.inl rfl)
  · intro x
    obtain ⟨⟨j,i⟩|⟨j,i⟩,rfl⟩ := all x
    · exact Or.inl ⟨j,i,seval j i⟩
    · exact Or.inr ⟨j,i,leval j i⟩

end CriticalThreeQuotient

namespace CriticalThreeQuotient

private theorem half_set_of_nats {r : ℕ} {M : Type*} [Fintype M]
    (g : M → ℕ) (bound : ∀ i,g i<r) (inj : Function.Injective g) :
    ∃ P : Finset (ZMod r), P.card=Fintype.card M ∧ ∀ i,(g i : ZMod r)∈P := by
  classical
  let emb : M ↪ ZMod r :=
    { toFun := fun i => (g i:ZMod r)
      inj' := by
        intro i j e
        apply inj
        have eq := congrArg ZMod.val e
        simpa only [ZMod.val_natCast_of_lt (bound i),ZMod.val_natCast_of_lt (bound j)] using eq }
  exact ⟨Finset.univ.map emb,by simp,fun i => Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

private theorem half_unit_path {r : ℕ} {C : Type*} (f : ZMod r → C) (B : ZMod r)
    (d : ℕ) (step : ∀ i : ℕ,i<d → f (B+(i:ZMod r)+1)=f (B+i)) : f (B+(d:ZMod r))=f B := by
  have walk (t : ℕ) (ht : t≤d) : f (B+(t:ZMod r))=f B := by
    induction t with
    | zero => simp
    | succ t ih =>
      simpa only [Nat.cast_succ,← add_assoc] using (step t (by omega)).trans (ih (by omega))
  exact walk d le_rfl

/-- Repair the middle residue for every even block count. A shift can miss
a short block only one step before its start. The additional edge reaches
the next block; at the target frequency a path of unit edges forces it. -/
theorem half_repair_graphs (u d : ℕ) (hu : 1≤u) (hd : 3≤d) :
    let r := 4*u*d
    let D : ZMod r := (d:ℕ)
    let e : ZMod r := (3*d-1:ℕ)
    ∃ P Q : Finset (ZMod r), P.card+(2*u*d+u)=r ∧ Q.card+(r-4*u+2)=r ∧
      ∃ src pivot : Fin u → ZMod r, (∀ a,pivot a∈P) ∧
        (∀ a,∀ f : ZMod r → ℂ, (∀ v∈P,f (v+1)=f v) →
          (∀ v∈Q,f (src a-e+D-v-1)=f (src a-e+D-v)) → f (pivot a+D)=f (pivot a)) ∧
        (∀ k : ZMod r,∀ f : ZMod r → ℂ,
          (∀ v∈P,f (v+1)=f v ∧ f (v+D)=f v) →
          (∀ v∈Q,f (k-v-1)=f (k-v) ∧ f (k-v-D)=f (k-v)) →
          (∀ a,k=src a → f (pivot a+e)=f (pivot a)) → ∀ i j,f i=f j) := by
  classical
  intro r D e
  let W := 2*d-1
  let V := 2*d+1
  let q := 4*u-2
  let sB (j : Fin u) : ZMod r := ((j.val*W:ℕ):ZMod r)
  let lB (j : Fin u) : ZMod r := ((u*W+j.val*V:ℕ):ZMod r)
  let src (j : Fin u) := sB j-1
  have hq : 0<q := by dsimp [q]; omega
  have hr : 0<r := Nat.mul_pos (Nat.mul_pos (by decide) hu) (by omega)
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨P,hp,small,big,nextP,partition⟩ := half_modes u d hu hd
  have qsum : q*d+2*d=r := by
    have eq : q+2=4*u := by dsimp [q]; omega
    have z := congrArg (·*d) eq
    change (q+2)*d=r at z
    nlinarith only [z]
  let qn (t : Fin q) := t.val*d
  have qbound (t : Fin q) : qn t<r := by
    have ht := Nat.mul_lt_mul_of_pos_right t.isLt (by omega : 0<d)
    change t.val*d<r
    omega
  have qinj : Function.Injective qn := fun _ _ eq => Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0<d) eq)
  obtain ⟨Q,cardQ,modes⟩ := half_set_of_nats qn qbound qinj
  have wplus : (W:ZMod r)+1=2*D := by
    rw [← Nat.cast_add_one,show W+1=2*d by dsimp [W]; omega,Nat.cast_mul]
    norm_num [D]
  have eplus : e+1=3*D := by
    change ((3*d-1:ℕ):ZMod r)+1=3*(d:ZMod r)
    rw [← Nat.cast_add_one,show (3*d-1)+1=3*d by omega,Nat.cast_mul]
    norm_num
  have cycle : ((q*d:ℕ):ZMod r)+2*D=0 := by
    change ((q*d:ℕ):ZMod r)+2*(d:ZMod r)=0
    rw [show (2:ZMod r)*(d:ZMod r)=((2*d:ℕ):ZMod r) by push_cast; rfl,← Nat.cast_add,qsum,ZMod.natCast_self]
  let last : Fin q := ⟨q-1,by omega⟩
  have lastStep : (qn last:ZMod r)+D=((q*d:ℕ):ZMod r) := by
    change ((last.val*d:ℕ):ZMod r)+(d:ZMod r)=_
    rw [← Nat.cast_add,← Nat.succ_mul,Nat.succ_eq_add_one,show last.val+1=q by dsimp [last]; omega]
  have want (j : Fin u) : src j-e+D-(qn last:ZMod r)=sB j+D := by
    dsimp only [src]
    linear_combination -eplus-lastStep-cycle
  refine ⟨P,Q,hp,?_,src,sB,?_,?_,?_⟩
  · simp only [Fintype.card_fin] at cardQ
    have low : 4*u≤r := by
      dsimp [r]
      nlinarith only [Nat.mul_le_mul_left (4*u) (by omega : 1≤d)]
    dsimp [q] at cardQ
    omega
  · intro j
    simpa only [Nat.cast_zero,add_zero] using small j 0 (by omega)
  · intro j f left right
    apply half_unit_path f (sB j) d
    intro i hi
    by_cases h : i<d-1
    · exact left _ (small j i h)
    · have hqv := right (qn last:ZMod r) (modes last)
      rw [want] at hqv
      have endstep : (i:ZMod r)+1=D := by
        change (i:ZMod r)+1=(d:ZMod r)
        rw [← Nat.cast_add_one,show i+1=d by omega]
      rw [add_assoc,endstep,← hqv,← endstep]
      congr 1
      abel
  · intro k f left right extra
    have predEq : d-1+1=d := by omega
    have allShort (j : Fin u) (o : ℕ) (ho : o<W) : f (sB j+(o:ZMod r))=f (sB j) := by
      apply block_constant (L:=d-1) f (sB j) _ o (by dsimp [W] at ho; omega)
      intro i
      simpa only [predEq,D] using left _ (small j i.val i.isLt)
    have allLong (j : Fin u) (o : ℕ) (ho : o<V) : f (lB j+(o:ZMod r))=f (lB j) := by
      let g (t : ℕ) := f (lB j+(t:ZMod r))
      have step (i : ℕ) (h : i=0 ∨ 2≤ i ∧ i≤d-1+1) :
          g (i+1)=g i ∧ g (i+(d-1+1))=g i := by
        have he := left _ (big j i (predEq ▸ h))
        change f (lB j+(i:ZMod r)+1)=f (lB j+i) ∧ f (lB j+(i:ZMod r)+D)=f (lB j+i) at he
        simpa only [g,predEq,D,Nat.cast_add,Nat.cast_one,← add_assoc] using he
      have begin := step 0 (.inl rfl)
      have far := long_block_constant (L:=d-1) (by omega) g (by simpa only [zero_add] using begin)
        (fun i lo hi => step i (.inr ⟨lo,hi⟩)) o (by dsimp [V] at ho; omega)
      simpa only [g,Nat.cast_zero,add_zero] using far
    have chain (t : ℕ) (ht : t≤q) : f (k-((t*d:ℕ):ZMod r))=f k := by
      induction t with
      | zero => simp
      | succ t ih =>
        rw [Nat.succ_mul,Nat.cast_add,← sub_sub]
        exact ((right _ (modes ⟨t,by omega⟩)).2).trans (ih (by omega))
    have hit (z : ZMod r) (w : ℕ) (hw : d≤w) (near : (k-z).val<q*d+w)
        (flat : ∀ o : ℕ,o<w → f (z+(o:ZMod r))=f z) : f z=f k := by
      obtain ⟨t,ht,o,ho,dist⟩ := chain_hits (by omega : 0<d) hw (le_refl (q*d+w)) near
      have drift : ((t*d:ℕ):ZMod r)+(o:ZMod r)=k-z := by
        rw [← Nat.cast_add,dist,ZMod.natCast_zmod_val]
      have meet : z+(o:ZMod r)=k-((t*d:ℕ):ZMod r) := by linear_combination drift
      exact (flat _ ho).symm.trans ((congrArg f meet).trans (chain _ ht))
    have longs (j : Fin u) : f (lB j)=f k :=
      hit _ V (by dsimp [V]; omega) (by have := (k-lB j).val_lt; dsimp [V]; omega) (allLong j)
    have shorts (j : Fin u) : f (sB j)=f k := by
      by_cases near : (k-sB j).val<q*d+W
      · exact hit _ W (by dsimp [W]; omega) near (allShort j)
      · have hv := (k-sB j).val_lt
        have gap : (k-sB j).val+1=r := by dsimp [W] at near; omega
        have km : k-sB j+1=0 := by
          rw [← ZMod.natCast_zmod_val (k-sB j),← Nat.cast_add_one,gap,ZMod.natCast_self]
        have source : k=src j := by dsimp [src]; linear_combination km
        have endpoint : k-((q*d:ℕ):ZMod r)=sB j+(W:ZMod r) := by
          rw [source]
          dsimp only [src]
          linear_combination -cycle-wplus
        have longEdge : e=(W:ZMod r)+D := by linear_combination eplus-wplus
        calc
          f (sB j) = f (sB j+e) := (extra j source).symm
          _ = f (sB j+(W:ZMod r)+D) := by rw [longEdge,add_assoc]
          _ = f (sB j+(W:ZMod r)) := (left _ (nextP j)).2
          _ = f (k-((q*d:ℕ):ZMod r)) := congrArg f endpoint.symm
          _ = f k := chain q le_rfl
    have all (x : ZMod r) : f x=f k := by
      rcases partition x with ⟨j,i,eq⟩|⟨j,i,eq⟩
      · exact (congrArg f eq).trans ((allShort j _ i.isLt).trans (shorts j))
      · exact (congrArg f eq).trans ((allLong j _ i.isLt).trans (longs j))
    exact fun i j => (all i).trans (all j).symm

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- Short and long blocks partition the top-residue frequency group. The
left modes are the regular centers in each short block and the shifted centers in each long block. -/
theorem top_modes (h d s : ℕ) (hh : 3≤h) (hd : h≤d) (hs : s<h) (high : h<2*s) :
    let r := 2*h*d+(2*s-h)
    let W := 2*d-1
    let V := 2*d+1
    let sB (j : Fin (h-s)) : ZMod r := ((j.val*W:ℕ):ZMod r)
    let lB (j : Fin s) : ZMod r := (((h-s)*W+j.val*V:ℕ):ZMod r)
    ∃ P : Finset (ZMod r), P.card+(h*d+s)=r ∧
      (∀ j,∀ i : ℕ,i<d-1 → sB j+(i:ZMod r)∈P) ∧
      (∀ j,∀ i : ℕ,i=0 ∨ 2≤ i ∧ i≤d → lB j+(i:ZMod r)∈P) ∧
      ∀ x : ZMod r,(∃ j,∃ i : Fin W,x=sB j+(i.val:ZMod r)) ∨
        ∃ j,∃ i : Fin V,x=lB j+(i.val:ZMod r) := by
  classical
  intro r W V sB lB
  let L := d-1
  have predEq : L+1=d := by dsimp [L]; omega
  have hw : W+1=2*d := by dsimp [W]; omega
  have ks : 2*s-h+h=2*s := Nat.sub_add_cancel high.le
  have widths : (h-s)*W+s*V=r := by
    have split := congrArg (·*W) (Nat.sub_add_cancel hs.le)
    have mult := congrArg (h*·) hw
    change (h-s+s)*W=h*W at split
    change h*(W+1)=h*(2*d) at mult
    rw [show V=W+2 by dsimp [V,W]; omega]
    dsimp [r]
    nlinarith only [ks,split,mult]
  have : NeZero r := ⟨by have := Nat.mul_pos (show 0<2*h by omega) (show 0<d by omega); dsimp [r]; omega⟩
  let G := (Fin (h-s) × Fin W) ⊕ (Fin s × Fin V)
  let M := (Fin (h-s) × Fin L) ⊕ (Fin s × Fin (L+1))
  let slot : G ≃ Fin r :=
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr widths)
  let residue : Fin r ↪ ZMod r :=
    { toFun := fun i => (i.val:ZMod r)
      inj' := by
        intro i j eq
        apply Fin.ext
        have raw := congrArg ZMod.val eq
        simpa only [ZMod.val_natCast_of_lt i.isLt,ZMod.val_natCast_of_lt j.isLt] using raw }
  let enc : G ↪ ZMod r := slot.toEmbedding.trans residue
  have all (x : ZMod r) : ∃ p,enc p=x := by
    obtain ⟨p,hp⟩ := slot.surjective ⟨x.val,x.val_lt⟩
    refine ⟨p,?_⟩
    change ((slot p).val:ZMod r)=x
    rw [hp,ZMod.natCast_zmod_val]
  have seval (j : Fin (h-s)) (i : Fin W) : enc (.inl (j,i))=sB j+(i.val:ZMod r) := by
    change ((i.val+W*j.val:ℕ):ZMod r)=((j.val*W:ℕ):ZMod r)+i.val
    push_cast
    ring
  have leval (j : Fin s) (i : Fin V) : enc (.inr (j,i))=lB j+(i.val:ZMod r) := by
    change (((h-s)*W+(i.val+V*j.val):ℕ):ZMod r)=(((h-s)*W+j.val*V:ℕ):ZMod r)+i.val
    push_cast
    ring
  obtain ⟨lc,lcrange⟩ := long_centers L
  let lcv : Fin (L+1) ↪ Fin V := lc.trans (finCongr (by dsimp [V]; omega : 2*L+3=V)).toEmbedding
  let sc : Fin L ↪ Fin W := Fin.castLEEmb (by dsimp [W,L]; omega)
  let pick : M ↪ G := ((Function.Embedding.refl (Fin (h-s))).prodMap sc).sumMap
    ((Function.Embedding.refl (Fin s)).prodMap lcv)
  let pe := pick.trans enc
  let P := Finset.univ.map pe
  have smem (j : Fin (h-s)) (i : ℕ) (hi : i<d-1) : sB j+(i:ZMod r)∈P := by
    let t : Fin L := ⟨i,hi⟩
    have hm : pe (.inl (j,t))∈P := Finset.mem_map.mpr ⟨.inl (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inl (j,sc t))∈P at hm
    simpa only [seval,show (sc t).val=i from rfl] using hm
  have lmem (j : Fin s) (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤d) : lB j+(i:ZMod r)∈P := by
    obtain ⟨t,ht⟩ := (lcrange i).mpr (predEq ▸ hi)
    have hm : pe (.inr (j,t))∈P := Finset.mem_map.mpr ⟨.inr (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inr (j,lcv t))∈P at hm
    simpa only [leval,show (lcv t).val=(lc t).val from rfl,ht] using hm
  have card : P.card+(h*d+s)=r := by
    simp only [P,Finset.card_map,Finset.card_univ,M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    have z := congrArg (h*·) predEq
    have split := congrArg (·*L) (Nat.sub_add_cancel hs.le)
    change (h-s+s)*L=h*L at split
    change h*(L+1)=h*d at z
    dsimp [r]
    nlinarith only [z,split,ks]
  refine ⟨P,card,smem,lmem,?_⟩
  intro x
  obtain ⟨⟨j,i⟩|⟨j,i⟩,rfl⟩ := all x
  · exact Or.inl ⟨j,i,seval j i⟩
  · exact Or.inr ⟨j,i,leval j i⟩

end CriticalThreeQuotient

namespace CriticalThreeQuotient

private theorem top_set_of_nats {r : ℕ} {M : Type*} [Fintype M]
    (g : M → ℕ) (bound : ∀ i,g i<r) (inj : Function.Injective g) :
    ∃ P : Finset (ZMod r), P.card=Fintype.card M ∧ ∀ i,(g i : ZMod r)∈P := by
  classical
  let emb : M ↪ ZMod r :=
    { toFun := fun i => (g i:ZMod r)
      inj' := by
        intro i j e
        apply inj
        have eq := congrArg ZMod.val e
        simpa only [ZMod.val_natCast_of_lt (bound i),ZMod.val_natCast_of_lt (bound j)] using eq }
  exact ⟨Finset.univ.map emb,by simp,fun i => Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

private theorem top_unit_path {r : ℕ} {C : Type*} (f : ZMod r → C) (B : ZMod r)
    (d : ℕ) (step : ∀ i : ℕ,i<d → f (B+(i:ZMod r)+1)=f (B+i)) : f (B+(d:ZMod r))=f B := by
  have walk (t : ℕ) (ht : t≤d) : f (B+(t:ZMod r))=f B := by
    induction t with
    | zero => simp
    | succ t ih =>
      simpa only [Nat.cast_succ,← add_assoc] using (step t (by omega)).trans (ih (by omega))
  exact walk d le_rfl

/-- Unit paths for every pulse, and the classification of the ordinary
frequency graph. In each exceptional phase only a block with the displayed
nearby start may fail to equal the common right-chain value. -/
theorem top_residue_graphs (h d s : ℕ) (hh : 3≤h) (hd : h≤d) (hs : s<h) (high : h<2*s) :
    let K := 2*s-h
    let r := 2*h*d+K
    let W := 2*d-1
    let V := 2*d+1
    let q := 2*h-2
    let D := (d:ZMod r)
    let tS (i : Fin (h-s)) := ((i.val*W:ℕ):ZMod r)
    let tL (i : Fin s) := (((h-s)*W+i.val*V:ℕ):ZMod r)
    ∃ P Q : Finset (ZMod r), P.card+(h*d+s)=r ∧ Q.card=q ∧
      (∀ i,tS i∈P) ∧ (∀ i,tL i∈P) ∧
      (∀ x : ZMod r,(∃ i,∃ o : Fin W,x=tS i+(o.val:ZMod r)) ∨
        ∃ i,∃ o : Fin V,x=tL i+(o.val:ZMod r)) ∧
      (∀ i,∀ j : ℕ,1≤j → j≤K+1 → ∀ f : ZMod r → ℂ,
        (∀ v∈P,f (v+1)=f v) →
        (∀ v∈Q,f (tS i+((j*d:ℕ):ZMod r)-v-1)=f (tS i+((j*d:ℕ):ZMod r)-v)) →
        f (tS i+D)=f (tS i)) ∧
      (∀ i,∀ j : ℕ,j≤K+1 → ∀ f : ZMod r → ℂ,
        (∀ v∈P,f (v+1)=f v) →
        (∀ v∈Q,f (tL i+2+((j*d:ℕ):ZMod r)-v-1)=f (tL i+2+((j*d:ℕ):ZMod r)-v)) →
        f (tL i+D)=f (tL i)) ∧
      ∀ k : ZMod r,∀ f : ZMod r → ℂ,
        (∀ v∈P,f (v+1)=f v ∧ f (v+D)=f v) →
        (∀ v∈Q,f (k-v-1)=f (k-v) ∧ f (k-v-D)=f (k-v)) →
        (∀ i,∀ o : ℕ,o<W → f (tS i+(o:ZMod r))=f (tS i)) ∧
        (∀ i,∀ o : ℕ,o<V → f (tL i+(o:ZMod r))=f (tL i)) ∧
        (∀ a : ℕ,a≤q*d → f (k-(a:ZMod r))=f k) ∧
        (∀ i,f (tS i)≠f k → ∃ l : ℕ,l≤K ∧ k=tS i-1-(l:ZMod r)) ∧
        (∀ i,f (tL i)≠f k → ∃ l : ℕ,l+2≤K ∧ k=tL i-1-(l:ZMod r)) := by
  classical
  intro K r W V q D tS tL
  have hq : 0<q := by dsimp [q]; omega
  have hK : K+1<q := by dsimp [q,K]; omega
  have hr : 0<r := Nat.add_pos_left (Nat.mul_pos (by omega : 0<2*h) (by omega)) _
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨P,cardP,small,big,partition⟩ := top_modes h d s hh hd hs high
  have qsum : q*d+2*d+K=r := by
    have e : q+2=2*h := by dsimp [q]; omega
    have z := congrArg (·*d) e
    change (q+2)*d=(2*h)*d at z
    dsimp [r]
    nlinarith only [z]
  let qn (i : Fin q) := i.val*d
  have qbound (i : Fin q) : qn i<r := by
    have e := Nat.mul_lt_mul_of_pos_right i.isLt (by omega : 0<d)
    change i.val*d<r
    omega
  have qinj : Function.Injective qn := fun _ _ eq => Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0<d) eq)
  obtain ⟨Q,cardQ,modes⟩ := top_set_of_nats qn qbound qinj
  refine ⟨P,Q,cardP,by simpa only [Fintype.card_fin] using cardQ,?_,?_,partition,?_,?_,?_⟩
  · intro i
    simpa only [Nat.cast_zero,add_zero] using small i 0 (by omega)
  · intro i
    simpa only [Nat.cast_zero,add_zero] using big i 0 (.inl rfl)
  · intro i j low upper f left right
    apply top_unit_path f (tS i) d
    intro o ho
    by_cases old : o<d-1
    · exact left _ (small i o old)
    · let v : Fin q := ⟨j-1,by omega⟩
      have div : (qn v:ZMod r)+D=((j*d:ℕ):ZMod r) := by
        change ((v.val*d:ℕ):ZMod r)+(d:ZMod r)=_
        rw [← Nat.cast_add,← Nat.succ_mul,Nat.succ_eq_add_one,show v.val+1=j by dsimp [v]; omega]
      have last := right (qn v:ZMod r) (modes v)
      rw [show tS i+((j*d:ℕ):ZMod r)-(qn v:ZMod r)=tS i+D by rw [← div]; abel] at last
      have endpoint : (o:ZMod r)+1=D := by
        change (o:ZMod r)+1=(d:ZMod r)
        rw [← Nat.cast_add_one,show o+1=d by omega]
      rw [add_assoc,endpoint,← last,← endpoint]
      congr 1
      abel
  · intro i j upper f left right
    apply top_unit_path f (tL i) d
    intro o ho
    by_cases seam : o=1
    · subst o
      let v : Fin q := ⟨j,by omega⟩
      have last := right (qn v:ZMod r) (modes v)
      change f (tL i+2+((j*d:ℕ):ZMod r)-((j*d:ℕ):ZMod r)-1)=
        f (tL i+2+((j*d:ℕ):ZMod r)-((j*d:ℕ):ZMod r)) at last
      rw [add_sub_cancel_right] at last
      simpa only [Nat.cast_one,show tL i+2-1=tL i+1 by ring,show tL i+1+1=tL i+2 by ring] using last.symm
    · exact left _ (big i o (by omega))
  · intro k f left right
    have predEq : d-1+1=d := by omega
    have sflat (i : Fin (h-s)) (o : ℕ) (ho : o<W) : f (tS i+(o:ZMod r))=f (tS i) := by
      apply block_constant (L:=d-1) f (tS i) _ o (by dsimp [W] at ho; omega)
      intro w
      simpa only [predEq,D] using left _ (small i w.val w.isLt)
    have lflat (i : Fin s) (o : ℕ) (ho : o<V) : f (tL i+(o:ZMod r))=f (tL i) := by
      let g (a : ℕ) := f (tL i+(a:ZMod r))
      have step (a : ℕ) (ok : a=0 ∨ 2≤a ∧ a≤d-1+1) : g (a+1)=g a ∧ g (a+(d-1+1))=g a := by
        have e := left _ (big i a (predEq ▸ ok))
        change f (tL i+(a:ZMod r)+1)=f (tL i+a) ∧ f (tL i+(a:ZMod r)+D)=f (tL i+a) at e
        simpa only [g,predEq,D,Nat.cast_add,Nat.cast_one,← add_assoc] using e
      have first := step 0 (.inl rfl)
      have last := long_block_constant (L:=d-1) (by omega) g (by simpa only [zero_add] using first)
        (fun a lo hi => step a (.inr ⟨lo,hi⟩)) o (by dsimp [V] at ho; omega)
      simpa only [g,Nat.cast_zero,add_zero] using last
    have chain (a : ℕ) (ha : a≤q) : f (k-((a*d:ℕ):ZMod r))=f k := by
      induction a with
      | zero => simp
      | succ t ih =>
        rw [Nat.succ_mul,Nat.cast_add,← sub_sub]
        exact ((right _ (modes ⟨t,by omega⟩)).2).trans (ih (by omega))
    have hit (z : ZMod r) (w : ℕ) (dw : d≤w) (close : (k-z).val<q*d+w)
        (flat : ∀ o : ℕ,o<w → f (z+(o:ZMod r))=f z) : f z=f k := by
      obtain ⟨a,ha,o,ho,eq⟩ := chain_hits (by omega : 0<d) dw (le_refl (q*d+w)) close
      have d0 : ((a*d:ℕ):ZMod r)+(o:ZMod r)=k-z := by
        rw [← Nat.cast_add,eq,ZMod.natCast_zmod_val]
      have join : z+(o:ZMod r)=k-((a*d:ℕ):ZMod r) := by linear_combination d0
      exact (flat _ ho).symm.trans ((congrArg f join).trans (chain _ ha))
    have corridor (a : ℕ) (ha : a≤q*d) : f (k-(a:ZMod r))=f k := by
      have pin (z : ZMod r) (w o : ℕ) (dw : d≤w) (ho : o<w) (eq : k-(a:ZMod r)=z+(o:ZMod r))
          (flat : ∀ y : ℕ,y<w → f (z+(y:ZMod r))=f z) : f (k-(a:ZMod r))=f k := by
        have diff : k-z=((a+o:ℕ):ZMod r) := by rw [Nat.cast_add]; linear_combination eq
        have near : (k-z).val<q*d+w := by
          rw [diff,ZMod.val_natCast]
          have lim := Nat.mod_le (a+o) r
          omega
        exact (congrArg f eq).trans ((flat _ ho).trans (hit z w dw near flat))
      rcases partition (k-(a:ZMod r)) with ⟨i,o,eq⟩|⟨i,o,eq⟩
      · exact pin (tS i) W o.val (by dsimp [W]; omega) o.isLt eq (sflat i)
      · exact pin (tL i) V o.val (by dsimp [V]; omega) o.isLt eq (lflat i)
    have exceptional (z : ZMod r) (w : ℕ) (dw : d≤w) (flat : ∀ o : ℕ,o<w → f (z+(o:ZMod r))=f z)
        (bad : f z≠f k) : ∃ l : ℕ,q*d+w+l+1≤r ∧ k=z-1-(l:ZMod r) := by
      have away : q*d+w≤(k-z).val := by
        by_contra! near
        exact bad (hit z w dw near flat)
      let t := (k-z).val
      let l := r-(t+1)
      have ht : t<r := (k-z).val_lt
      have eq : t+(1+l)=r := by dsimp [l]; omega
      have phase : k-z+(1+(l:ZMod r))=0 := by
        rw [← ZMod.natCast_zmod_val (k-z)]
        change (t:ZMod r)+(1+(l:ZMod r))=0
        rw [← Nat.cast_one (R:=ZMod r),← Nat.cast_add,← Nat.cast_add,eq,ZMod.natCast_self]
      refine ⟨l,?_,?_⟩
      · change q*d+w≤t at away
        omega
      · linear_combination phase
    refine ⟨sflat,lflat,corridor,?_,?_⟩
    · intro i bad
      obtain ⟨l,limit,phase⟩ := exceptional _ W (by dsimp [W]; omega) (sflat i) bad
      dsimp [W] at limit
      exact ⟨l,by omega,phase⟩
    · intro i bad
      obtain ⟨l,limit,phase⟩ := exceptional _ V (by dsimp [V]; omega) (lflat i) bad
      dsimp [V] at limit
      exact ⟨l,by omega,phase⟩

end CriticalThreeQuotient

namespace CriticalThreeTop

/-- Equality of two base-d expansions with bounded low and high digits can
be read before reducing modulo r when the whole digit rectangle fits. -/
theorem two_digits {r d K u v l : ℕ} [NeZero r] (small : K<d) (room : K*d+K<r)
    (hu : u≤K) (hv : v≤K) (hl : l≤K)
    (same : ((v*d+l : ℕ) : ZMod r) = ((u*d+u : ℕ) : ZMod r)) :
    u=v ∧ u=l := by
  have a : v*d+l<r := (Nat.add_le_add (Nat.mul_le_mul_right d hv) hl).trans_lt room
  have b : u*d+u<r := (Nat.add_le_add (Nat.mul_le_mul_right d hu) hu).trans_lt room
  have sizes := congrArg ZMod.val same
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b] at sizes
  have high : u=v := by
    rcases lt_trichotomy u v with h | eq | h
    · have separated := Nat.mul_le_mul_right d (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at separated
      omega
    · exact eq
    · have separated := Nat.mul_le_mul_right d (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at separated
      omega
  exact ⟨high,by simpa only [high,Nat.add_right_inj] using sizes.symm⟩

/-- Each bad frequency can lose at most one left block. A row per phase
forces its value at the start of that block to equal its value on the
right-hand chain. The phase digits in the pulse separate the other rows. -/
theorem isolate_starts {r d K q : ℕ} [NeZero r] {B : Type*}
    (start : B → ZMod r) (offset : B → ℕ)
    (small : K<d) (room : K*d+K<r) (cover : K*d+2≤q*d) (hoff : ∀ i,offset i≤2)
    (F : ZMod r → ZMod r → ℂ)
    (corridor : ∀ k a, a≤q*d → F k (k-(a : ZMod r))=F k k)
    (missing : ∀ k i, F k (start i)≠F k k →
      ∃ l : ℕ, l+offset i≤K ∧ k=start i-1-(l : ZMod r)) :
    let pulse (u : Fin (K+1)) : ZMod r := -((u.val : ZMod r)*d+1+u.val)
    let target (i : B) (v : Fin (K+1)) := start i+((v.val : ZMod r)+1)*d+offset i
    (∀ i v, ∑ u, (F (target i v+pulse u-d) (start i+pulse u) -
      F (target i v+pulse u-d) (start i))=0) →
    ∀ k i, F k (start i)=F k k := by
  intro pulse target equations k i
  by_contra different
  obtain ⟨l,bound,source⟩ := missing k i different
  let v : Fin (K+1) := ⟨l+offset i,by omega⟩
  let mode (u : Fin (K+1)) := target i v+pulse u-d
  have at_v : mode v=k := by
    rw [source]
    dsimp [mode,target,pulse,v]
    push_cast
    ring
  have inCorridor : v.val*d+offset i ≤ q*d :=
    (Nat.add_le_add (Nat.mul_le_mul_right d (by omega : v.val≤K)) (hoff i)).trans cover
  have shifted (u : Fin (K+1)) : F (mode u) (start i+pulse u)=F (mode u) (mode u) := by
    have pos : start i+pulse u=mode u-((v.val*d+offset i : ℕ) : ZMod r) := by
      dsimp only [mode,target]
      push_cast
      ring
    rw [pos]
    exact corridor (mode u) _ inCorridor
  have other (u : Fin (K+1)) (ne : u≠v) : F (mode u) (start i)=F (mode u) (mode u) := by
    by_contra bad
    obtain ⟨l',bound',source'⟩ := missing (mode u) i bad
    have digits : ((v.val*d+(l'+offset i) : ℕ) : ZMod r) =
        ((u.val*d+u.val : ℕ) : ZMod r) := by
      push_cast
      dsimp only [mode,target,pulse] at source'
      linear_combination source'
    exact ne (Fin.ext (two_digits small room (by omega) (by omega) bound' digits).1)
  have zero := equations i v
  change (∑ u, (F (mode u) (start i+pulse u)-F (mode u) (start i)))=0 at zero
  rw [Finset.sum_eq_single v] at zero
  · rw [shifted v,at_v] at zero
    exact different (sub_eq_zero.mp zero).symm
  · intro u _ ne
    rw [shifted u,other u ne,sub_self]
  · simp

end CriticalThreeTop

namespace CriticalThreeTop

/-- A multi-frequency perturbation repairs the upper half of the width
residues. Its additional equations separate each possibly missed block
one phase at a time. -/
theorem high_tangent (h d s : ℕ) (hh : 3≤h) (hd : h≤d) (hs : s<h) (high : h<2*s) :
    let r := 2*h*d+(2*s-h)
    let b := h*d+s
    let n := r-(2*h-2)
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ a : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(a t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  classical
  intro r b n
  let K := 2*s-h
  let q := 2*h-2
  let W := 2*d-1
  let V := 2*d+1
  have hr : 0<r := Nat.add_pos_left (Nat.mul_pos (by omega : 0<2*h) (by omega)) _
  let : NeZero r := ⟨hr.ne'⟩
  have small : K<d := by dsimp [K]; omega
  have kh : K<h := by dsimp [K]; omega
  have prod := Nat.mul_le_mul_right d kh.le
  have room : K*d+K<r := by dsimp [r]; nlinarith only [prod,small,Nat.mul_le_mul_right d (by omega : 1≤h)]
  have cover : K*d+2≤q*d := by
    have step := Nat.mul_le_mul_right d (by dsimp [q]; omega : K+1≤q)
    rw [Nat.succ_mul] at step
    omega
  have counts : q+n=r := by
    have lower := Nat.mul_le_mul_left (2*h) (by omega : 1≤d)
    dsimp [q,n,r]
    omega
  obtain ⟨P,Q,pCard,qCard,shortP,longP,partition,shortPaths,longPaths,base⟩ :=
    CriticalThreeQuotient.top_residue_graphs h d s hh hd hs high
  let B := Fin (h-s) ⊕ Fin s
  let short (i : Fin (h-s)) : ZMod r := ((i.val*W : ℕ) : ZMod r)
  let long (i : Fin s) : ZMod r := (((h-s)*W+i.val*V : ℕ) : ZMod r)
  let start : B → ZMod r := Sum.elim short long
  let shift : B → ℕ := Sum.elim (fun _ => 0) (fun _ => 2)
  let tag := B × Fin (K+1)
  let pivot (a : tag) := start a.1
  let target (a : tag) := pivot a+((a.2.val : ZMod r)+1)*d+shift a.1
  let pulse (u : Fin (K+1)) : ZMod r := -((u.val : ZMod r)*d+1+u.val)
  obtain ⟨z,_,Y,Z,span⟩ := CriticalThreePerturbation.multipulse_tangent_of_graph_cards
    (d : ZMod r) pulse (fun _ => 1) P Q (b:=b) (n:=n) pCard (qCard ▸ counts)
    target pivot (by
      rintro ⟨i|i,v⟩
      · exact shortP i
      · exact longP i) (by
      rintro ⟨i|i,v⟩ f left right
      · apply shortPaths i (v.val+1) (by omega) (by omega) f left
        intro u hu
        have eq : target (.inl i,v)=short i+(((v.val+1)*d : ℕ) : ZMod r) := by
          dsimp [target,pivot,start,shift]
          push_cast
          ring
        simpa only [eq] using right u hu
      · apply longPaths i (v.val+1) (by omega) f left
        intro u hu
        have eq : target (.inr i,v)=long i+2+(((v.val+1)*d : ℕ) : ZMod r) := by
          dsimp [target,pivot,start,shift]
          push_cast
          ring
        simpa only [eq] using right u hu) (by
      intro F left right extra
      have localData (k : ZMod r) := base k (F k) (left k) (right k)
      have allStarts : ∀ k i,F k (start i)=F k k := by
        apply isolate_starts start shift small room cover (by rintro (i|i) <;> simp [shift]) F
          (fun k => (localData k).2.2.1)
        · rintro k (i|i) bad
          · simpa [K,shift,start,short,W] using (localData k).2.2.2.1 i bad
          · exact (localData k).2.2.2.2 i bad
        · intro i v
          simpa only [one_mul] using extra (i,v)
      have every (k j : ZMod r) : F k j=F k k := by
        rcases partition j with ⟨i,o,eq⟩ | ⟨i,o,eq⟩
        · rw [eq]
          exact ((localData k).1 i o.val o.isLt).trans (allStarts k (.inl i))
        · rw [eq]
          exact ((localData k).2.1 i o.val o.isLt).trans (allStarts k (.inr i))
      exact fun k i j => (every k i).trans (every k j).symm)
  exact ⟨_,Y,Z,span⟩

end CriticalThreeTop

namespace CriticalThreeTop

/-- Polynomial division of the upper endpoint remains valid when the
unshifted affine part would be negative. -/
theorem shifted_floor {h b : ℕ} (hh : 1≤h) (hb : 0<b) (bound : h≤2*b) :
    (2*b-h)*(b+1)/(b+h)+3*h = 2*b+2+3*h*(h-1)/(b+h) := by
  have pos : 0<b+h := by omega
  have right := Nat.sub_add_cancel bound
  have m := congrArg (fun u : ℕ => u*(b+1)) right
  have n := congrArg (fun u : ℕ => u*h) (Nat.sub_add_cancel hh)
  have identity : (2*b-h)*(b+1)+(b+h)*(3*h)=3*h*(h-1)+(b+h)*(2*b+2) := by
    nlinarith only [m,n]
  have divided := congrArg (fun v : ℕ => v/(b+h)) identity
  simp only [Nat.add_mul_div_left _ _ pos] at divided
  omega

/-- Exact lower and upper third dimensions for each positive trial rank
2b−h. This expression uses natural numbers even below b=h². -/
theorem level_interval {b h N : ℕ} (hb : 0<b) (hh : 1≤h) (rankpos : h<2*b) :
    3*b*N ⌈/⌉ (b+N+1)=2*b-h ↔
      2*b+3*h*(h+1)/(b+h+1) ≤ N+3*h ∧
      N+3*h ≤ 2*b+2+3*h*(h-1)/(b+h) := by
  have hi := shifted_floor hh hb rankpos.le
  have lo := shifted_floor (h:=h+1) (by omega) hb (by omega)
  rw [Nat.add_sub_cancel,show 3*(h+1)*h=3*h*(h+1) by ring,
    show b+(h+1)=b+h+1 by omega] at lo
  have exactRange := CriticalHigher.count_interval (A:=3*b) (d:=b+1) (r:=2*b-h) (n:=N)
    (by omega) (by omega) (by omega)
  rw [show b+1+N=b+N+1 by omega,show 3*b-(2*b-h)=b+h by omega,
    show 2*b-h-1=2*b-(h+1) by omega,show 3*b-(2*b-(h+1))=b+h+1 by omega] at exactRange
  omega

/-- The natural endpoint differs from the actual upper end of the level by
the explicitly displayed floor. -/
theorem true_upper_endpoint {h b : ℕ} (hh : 3≤h) (lower : h^2≤b) :
    (2*b-h)*(b+1)/(b+h)=(2*b-3*h+2)+3*h*(h-1)/(b+h) := by
  have width : 3*h≤b := by have z := Nat.mul_le_mul_right h hh; nlinarith only [z,lower]
  have upper := shifted_floor (by omega : 1≤h) (by omega : 0<b) (by omega : h≤2*b)
  omega

/-- The computed endpoint reaches every third size on this fixed-rank level
exactly beyond the stated threshold; at smaller widths at most two extra
third sizes remain if b≥h². -/
theorem endpoint_threshold {h b : ℕ} (hh : 3≤h) (lower : h^2≤b) :
    ((2*b-h)*(b+1)/(b+h)=2*b-3*h+2 ↔ 3*h*(h-1)-h+1≤b) ∧
    (2*b-h)*(b+1)/(b+h)≤2*b-3*h+4 := by
  have width : 3*h≤b := by have z := Nat.mul_le_mul_right h hh; nlinarith only [z,lower]
  have pos : 0<b+h := by omega
  have t : h≤3*h*(h-1) := by
    have z := Nat.mul_le_mul_left (3*h) (show 1≤h-1 by omega)
    nlinarith only [z,hh]
  have pred := Nat.sub_add_cancel t
  have tiny : 3*h*(h-1)/(b+h)≤2 := by
    have e := congrArg (fun u : ℕ => u*h) (Nat.sub_add_cancel (by omega : 1≤h))
    have z := (Nat.div_lt_iff_lt_mul pos).mpr
      (show 3*h*(h-1)<3*(b+h) by nlinarith only [lower,e,hh])
    omega
  have zero : 3*h*(h-1)/(b+h)=0 ↔ 3*h*(h-1)-h+1≤b := by
    constructor
    · intro h0
      by_contra! small
      have one : 1≤3*h*(h-1)/(b+h) := (Nat.le_div_iff_mul_le pos).mpr (by simp; omega)
      omega
    · intro wide
      exact Nat.div_eq_of_lt (by omega)
  rw [true_upper_endpoint hh lower]
  omega

/-- At each fixed h, only finitely many middle widths can lie outside the
uniform full-plateau range. The threshold itself already implies b≥h². -/
theorem lower_of_threshold {h b : ℕ} (hh : 3≤h) (wide : 3*h*(h-1)-h+1≤b) : h^2≤b := by
  have prod := Nat.mul_le_mul_left (3*h) (show 1≤h-1 by omega)
  have pred := Nat.sub_add_cancel (show h≤3*h*(h-1) by nlinarith only [prod,hh])
  have e := congrArg (fun t : ℕ => t*h) (Nat.sub_add_cancel (by omega : 1≤h))
  have z := Nat.mul_le_mul_right h hh
  nlinarith only [wide,pred,e,z,hh]

end CriticalThreeTop

namespace CriticalThreeTop

/-- At the middle residue the single-frequency deformation supplies the
tangent for every even number 2u of blocks. -/
theorem middle_tangent (u d : ℕ) (hu : 1≤u) (hd : 3≤d) :
    let r := 4*u*d
    let b := 2*u*d+u
    let n := r-4*u+2
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ a : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(a t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  intro r b n
  have : NeZero r := ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide) hu) (by omega))⟩
  obtain ⟨P,Q,pCard,qCard,src,pivot,inP,paths,graphs⟩ :=
    CriticalThreeQuotient.half_repair_graphs u d hu hd
  obtain ⟨z,_,Y,Z,spans⟩ := CriticalThreePerturbation.perturbed_tangent_of_graph_cards
    (d : ZMod r) ((3*d-1:ℕ):ZMod r) P Q pCard qCard src pivot inP paths graphs
  exact ⟨_,Y,Z,spans⟩

/-- At the natural endpoint, the low, middle and high residues together
give a spanning complex tangent for every middle dimension b≥h². -/
theorem uniform_tangent (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    let r := 2*b-h
    let n := 2*b-3*h+2
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ a : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(a t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  intro r n
  let d := b/h
  let s := b%h
  have hd : h≤d := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [sq] using lower)
  have hs : s<h := Nat.mod_lt _ (by omega)
  have dims : h*d+s=b := Nat.div_add_mod b h
  obtain ⟨hb,width,_,enough,_,_⟩ := CriticalThreeQuotient.precise_mixed_counts h b hh lower
  have level : r+h=2*b := Nat.sub_add_cancel (by omega)
  rcases lt_trichotomy (2*s) h with low | eq | high
  · exact CriticalThreeQuotient.tangent_of_remainder_capacity b n r h (by omega) width enough level
      ((CriticalThreeQuotient.precise_mixed_capacity h b hh lower).2.mpr low)
  · have b' : 2*s*d+s=b := by rw [eq]; exact dims
    have r' : 4*s*d=r := by nlinarith only [b',level,eq]
    have n' : 4*s*d-4*s+2=n := by dsimp [n]; omega
    have w := middle_tangent s d (by omega) (by omega)
    dsimp only at w
    rw [n',r',b'] at w
    exact w
  · have rem := Nat.sub_add_cancel high.le
    have r' : 2*h*d+(2*s-h)=r := by nlinarith only [dims,level,rem]
    have n' : (2*h*d+(2*s-h))-(2*h-2)=n := by dsimp [n]; omega
    have w := high_tangent h d s hh hd hs high
    dsimp only at w
    rw [n',r',dims] at w
    exact w

/-- All widths b≥h² realize rank 2b−h at the explicit third dimension. -/
theorem uniform_generic_rank (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    Arxiv.«0805.3777».IsGenericRank [3,b,2*b-3*h+2] (2*b-h) := by
  obtain ⟨hb,_,order,_,_,count⟩ := CriticalThreeQuotient.precise_mixed_counts h b hh lower
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb (by omega) _
    (uniform_tangent h b hh lower)
  rw [show 3+b+(2*b-3*h+2)-2=b+((2*b-3*h+1)+1)+1 by omega]
  exact count.symm

/-- Any ordered third dimension on this level below the explicit witness
inherits its full tangent by projection. -/
theorem rank_below_endpoint (h b N : ℕ) (hh : 3≤h) (lower : h^2≤b)
    (order : b≤N) (below : N≤2*b-3*h+2)
    (count : 3*b*N ⌈/⌉ (b+N+1)=2*b-h) :
    Arxiv.«0805.3777».IsGenericRank [3,b,N] (2*b-h) := by
  have hb := (CriticalThreeQuotient.precise_mixed_counts h b hh lower).1
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb order _
    (CriticalHigher.project below (uniform_tangent h b hh lower))
  rw [show 3+b+N-2=b+N+1 by omega]
  exact count.symm

/-- Every ordered third dimension whose predicted rank is 2b−h has that
actual rank past the exact upper-endpoint threshold. -/
theorem fixed_level_tail_rank (h b N : ℕ) (hh : 3≤h) (wide : 3*h*(h-1)-h+1≤b)
    (order : b≤N) (count : 3*b*N ⌈/⌉ (b+N+1)=2*b-h) :
    Arxiv.«0805.3777».IsGenericRank [3,b,N] (2*b-h) := by
  have lower := lower_of_threshold hh wide
  obtain ⟨hb,width,_,_,_,_⟩ := CriticalThreeQuotient.precise_mixed_counts h b hh lower
  have hi := ((level_interval (by omega) (by omega) (by omega)).mp count).2
  have upper := ((endpoint_threshold hh lower).1.mpr wide)
  rw [true_upper_endpoint hh lower] at upper
  exact rank_below_endpoint h b N hh lower order (by omega) count

/-- Above the witnessed third size there are at most two candidate slices,
and their middle widths lie in an explicit finite interval for each h. -/
theorem residual_sizes {h b N : ℕ} (hh : 3≤h) (lower : h^2≤b)
    (above : 2*b-3*h+2<N) (count : 3*b*N ⌈/⌉ (b+N+1)=2*b-h) :
    b≤3*h*(h-1)-h ∧ (N=2*b-3*h+3 ∨ N=2*b-3*h+4) := by
  obtain ⟨hb,width,_,_,_,_⟩ := CriticalThreeQuotient.precise_mixed_counts h b hh lower
  have hi := ((level_interval (by omega) (by omega) (by omega)).mp count).2
  obtain ⟨exactEnd,two⟩ := endpoint_threshold hh lower
  rw [true_upper_endpoint hh lower] at two exactEnd
  omega

end CriticalThreeTop

namespace CriticalThreeTop

/-- Once both rational corrections vanish, exactly three consecutive
third dimensions have the chosen dimension-count rank. -/
theorem three_row_interval {h b N : ℕ} (hh : 3≤h) (wide : 3*h^2+2*h≤b) :
    3*b*N ⌈/⌉ (b+N+1)=2*b-h ↔ 2*b-3*h≤N ∧ N≤2*b-3*h+2 := by
  have lower : h^2≤b := by omega
  have width : 3*h≤b := by have z := Nat.mul_le_mul_right h hh; nlinarith only [z,lower]
  have lo : 3*h*(h+1)/(b+h+1)=0 := Nat.div_eq_of_lt (by nlinarith only [wide])
  have u := congrArg (fun t : ℕ => t*h) (Nat.sub_add_cancel (by omega : 1≤h))
  have hi : 3*h*(h-1)/(b+h)=0 := Nat.div_eq_of_lt (by nlinarith only [wide,u,hh])
  rw [level_interval (by omega : 0<b) (by omega : 1≤h) (by omega : h<2*b),lo,hi]
  omega

/-- All three third dimensions 2b−3h, 2b−3h+1 and 2b−3h+2 have the
same complex generic CP rank once b≥3h²+2h. -/
theorem three_rows_generic_rank (h b j : ℕ) (hh : 3≤h) (wide : 3*h^2+2*h≤b) (hj : j≤2) :
    Arxiv.«0805.3777».IsGenericRank [3,b,2*b-3*h+j] (2*b-h) := by
  have lower : h^2≤b := by omega
  have width : 3*h≤b := by have z := Nat.mul_le_mul_right h hh; nlinarith only [z,lower]
  apply rank_below_endpoint h b _ hh lower (by omega) (by omega)
  exact (three_row_interval hh wide).mpr ⟨by omega,by omega⟩

/-- At the first third size of the three-row range, the width threshold
3h²+2h is necessary for the displayed rank even to be the parameter count. -/
theorem first_row_count_iff {h b : ℕ} (hh : 3≤h) (lower : h^2≤b) :
    3*b*(2*b-3*h) ⌈/⌉ (b+(2*b-3*h)+1)=2*b-h ↔ 3*h^2+2*h≤b := by
  have width : 3*h≤b := by have z := Nat.mul_le_mul_right h hh; nlinarith only [z,lower]
  constructor
  · intro count
    have lo := ((level_interval (by omega) (by omega) (by omega)).mp count).1
    by_contra! fail
    have frac : 1≤3*h*(h+1)/(b+h+1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith only [fail])
    omega
  · intro wide
    exact (three_row_interval hh wide).mpr ⟨le_rfl,by omega⟩

end CriticalThreeTop

namespace CriticalThreeTop

/-- On each of the three natural rows, a single strict inequality gives
the exact arithmetic range of the predicted rank. The middle width may
be smaller than h². -/
theorem natural_count_iff {h b j : ℕ} (hh : 3≤h) (defined : 3*h≤2*b) (row : j≤2) :
    3*b*(2*b-3*h+j) ⌈/⌉ (b+(2*b-3*h+j)+1)=2*b-h ↔
      3*h*(h+1)<(j+1)*(b+h+1) := by
  have pos : 0<b+h+1 := by omega
  have fix := Nat.sub_add_cancel defined
  rw [level_interval (by omega : 0<b) (by omega : 1≤h) (by omega : h<2*b)]
  have lower : 3*h*(h+1)/(b+h+1)<j+1 ↔ 3*h*(h+1)<(j+1)*(b+h+1) := Nat.div_lt_iff_lt_mul pos
  have upper := Nat.le_add_right (2*b+2) (3*h*(h-1)/(b+h))
  omega

/-- Whenever the dimension prediction on any of the three natural rows
is 2b−h, the complex generic rank realizes it. -/
theorem sharp_three_row_rank (h b j : ℕ) (hh : 3≤h) (row : j≤2)
    (fit : 3*h*(h+1)<(j+1)*(b+h+1)) :
    Arxiv.«0805.3777».IsGenericRank [3,b,2*b-3*h+j] (2*b-h) := by
  have limit := Nat.mul_le_mul_right (b+h+1) (show j+1≤3 by omega)
  have lower : h^2≤b := by nlinarith only [fit,limit]
  have width : 3*h≤b := by
    have z := Nat.mul_le_mul_right h hh
    nlinarith only [z,lower]
  apply rank_below_endpoint h b _ hh lower (by omega) (by omega)
  exact (natural_count_iff hh (by omega) row).mpr fit

/-- At fixed h the full strict-rectangle problem is equivalent to a finite
set of middle widths. For b≥h², only the two specified third sizes can remain. -/
theorem fixed_level_finite_iff (h : ℕ) (hh : 3≤h) :
    (∀ b N : ℕ, 3≤b → b<N → N≤2*(b-1) →
      3*b*N ⌈/⌉ (b+N+1)=2*b-h →
      Arxiv.«0805.3777».IsGenericRank [3,b,N] (2*b-h)) ↔
    (∀ b N : ℕ, 3≤b → b<N → N≤2*(b-1) →
      b<3*h*(h-1)-h+1 → (b<h^2 ∨ N=2*b-3*h+3 ∨ N=2*b-3*h+4) →
      3*b*N ⌈/⌉ (b+N+1)=2*b-h →
      Arxiv.«0805.3777».IsGenericRank [3,b,N] (2*b-h)) := by
  constructor
  · exact fun all b N hb ord bound _ _ count => all b N hb ord bound count
  · intro finite b N hb ord bound count
    by_cases past : 3*h*(h-1)-h+1≤b
    · exact fixed_level_tail_rank h b N hh past ord.le count
    by_cases low : h^2≤b
    · by_cases below : N≤2*b-3*h+2
      · exact rank_below_endpoint h b N hh low ord.le below count
      · have residual := residual_sizes hh low (by omega) count
        exact finite b N hb ord bound (by omega) (Or.inr residual.2) count
    · exact finite b N hb ord bound (by omega) (Or.inl (by omega)) count

/-- The full fixed-rank tail also yields literal tangent witnesses,
which specialize to the registered weighted normal equations. -/
theorem fixed_level_tail_tangent (h b N : ℕ) (hh : 3≤h) (wide : 3*h*(h-1)-h+1≤b)
    (count : 3*b*N ⌈/⌉ (b+N+1)=2*b-h) :
    let r := 2*b-h
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ a : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
          T i j k=∑ t,(a t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  have lower := lower_of_threshold hh wide
  obtain ⟨hb,width,_,_,_,_⟩ := CriticalThreeQuotient.precise_mixed_counts h b hh lower
  have hi := ((level_interval (by omega) (by omega) (by omega)).mp count).2
  have upper := (endpoint_threshold hh lower).1.mpr wide
  rw [true_upper_endpoint hh lower] at upper
  exact CriticalHigher.project (show N≤2*b-3*h+2 by omega) (uniform_tangent h b hh lower)

end CriticalThreeTop

namespace CriticalThreeTop

/-- For b≥h² the two candidates above the witness are exactly characterized:
the t-th higher slice has this rank prediction iff t(b+h)≤3h(h−1). -/
theorem extra_slice_count_iff {h b t : ℕ} (hh : 3≤h) (lower : h^2≤b) :
    3*b*(2*b-3*h+2+t) ⌈/⌉ (b+(2*b-3*h+2+t)+1)=2*b-h ↔
      t*(b+h)≤3*h*(h-1) := by
  have width : 3*h≤b := by have e := Nat.mul_le_mul_right h hh; nlinarith only [e,lower]
  have lo : 3*h*(h+1)/(b+h+1)<3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr
    (by nlinarith only [lower])
  have fit : t≤3*h*(h-1)/(b+h) ↔ t*(b+h)≤3*h*(h-1) := Nat.le_div_iff_mul_le (by omega)
  rw [level_interval (by omega : 0<b) (by omega : 1≤h) (by omega : h<2*b)]
  omega

/-- A strict rectangle with dimension-count rank 2b−h must already have
middle width at least 2h. -/
theorem strict_width_at_least_twice {h b N : ℕ} (hb : 0<b) (ordered : b<N)
    (count : 3*b*N ⌈/⌉ (b+N+1)=2*b-h) : 2*h≤b := by
  let r := 2*b-h
  have bound := (ceilDiv_le_iff_le_mul (by omega : 0<b+N+1)).mp count.le
  change 3*b*N≤(b+N+1)*r at bound
  have hr : 0<r := by
    by_contra! zero
    have e : r=0 := by omega
    rw [e,Nat.mul_zero] at bound
    have pos := Nat.mul_pos (Nat.mul_pos (by decide : 0<3) hb) (by omega : 0<N)
    omega
  have level : r+h=2*b := Nat.sub_add_cancel (Nat.sub_pos_iff_lt.mp hr).le
  have eq := congrArg (fun t : ℕ => t*N) level
  have delta : N*(b+h)≤r*(b+1) := by nlinarith only [eq,bound]
  have mul := (Nat.mul_le_mul_right (b+h) (show b+1≤N by omega)).trans delta
  rw [Nat.mul_comm r (b+1)] at mul
  have := Nat.le_of_mul_le_mul_left mul (by omega)
  omega

end CriticalThreeTop

namespace CriticalHigher

/-- The dimension budget for normal planes of arbitrary dimension.
The common annihilator has dimension A−r. Each point contributes A−r−d
scalar unknowns, and the third vectors supply r−n relations. -/
theorem normal_budget {A d n r : ℕ} (hd : 0<d) (proper : r<A) (small : d≤A-r)
    (count : A*n ⌈/⌉ (d+n)=r) :
    n≤r ∧ (A-r-d)*r ≤ (r-n)*(A-r) := by
  have upper := (count_le_iff hd proper).mp count.le
  have product := (Nat.le_div_iff_mul_le (by omega : 0<A-r)).mp upper
  have size : n≤r :=
    Nat.le_of_mul_le_mul_right (product.trans (Nat.mul_le_mul_left r small)) (by omega)
  have lhs := congrArg (fun z : ℕ => r*z) (Nat.sub_add_cancel small)
  have rhs := congrArg (fun z : ℕ => z*(A-r)) (Nat.sub_add_cancel size)
  exact ⟨size,by nlinarith only [lhs,rhs,product]⟩

end CriticalHigher

namespace CriticalThreeQuotient

/-- For uniform blocks the undivided parameter-count inequality is precisely
the number of right equations required by the Cauchy interpolation geometry. -/
theorem uniform_count_iff (h d n : ℕ) (hh : 1≤h) (hd : 2≤d)
    (hn : n≤h*(2*d-1)) :
    let b := h*d
    let W := 2*d-1
    let r := h*W
    let q := r-n
    3*b*n ⌈/⌉ (b+n+1) ≤ r ↔ (h-1)*W≤q*(d+1) := by
  intro b W r q
  rw [ceilDiv_le_iff_le_mul (by omega : 0<b+n+1)]
  have balance : (b+n+1)*r+h*((h-1)*W)=3*b*n+h*(q*(d+1)) := by
    dsimp [b,W,r,q]
    zify [hn,hh,show 1≤2*d by omega]
    ring
  have cancel : h*((h-1)*W)≤h*(q*(d+1)) ↔ (h-1)*W≤q*(d+1) :=
    Nat.mul_le_mul_left_iff hh
  omega

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- A repeated progression can be padded to exactly q modes. Every one of
its original indexed centers remains available to the unit paths. -/
private theorem cauchy_right_modes {r q : ℕ} [NeZero r] (bound : q≤r) (g : Fin q → ZMod r) :
    ∃ Q : Finset (ZMod r),Q.card=q ∧ ∀ i,g i∈Q := by
  classical
  let T := Finset.univ.image g
  have size : T.card≤q := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.card_image_le (s:=Finset.univ) (f:=g))
  obtain ⟨Q,sub,card⟩ := Finset.exists_superset_card_eq size
    (show q≤Fintype.card (ZMod r) by simpa only [ZMod.card] using bound)
  exact ⟨Q,card,fun i => sub (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩

end CriticalThreeQuotient

namespace CriticalThreeQuotient

private theorem cauchy_wide_left_set {r : ℕ} {M : Type*} [Fintype M]
    (g : M → ℕ) (bound : ∀ i,g i<r) (inj : Function.Injective g) :
    ∃ P : Finset (ZMod r), P.card=Fintype.card M ∧ ∀ i,(g i : ZMod r)∈P := by
  classical
  let emb : M ↪ ZMod r :=
    { toFun := fun i => (g i:ZMod r)
      inj' := by
        intro i j e
        apply inj
        have eq := congrArg ZMod.val e
        simpa only [ZMod.val_natCast_of_lt (bound i),ZMod.val_natCast_of_lt (bound j)] using eq }
  exact ⟨Finset.univ.map emb,by simp,fun i => Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

private theorem cauchy_wide_unit_path {r : ℕ} {C : Type*} (f : ZMod r → C) (B : ZMod r)
    (d : ℕ) (step : ∀ i : ℕ,i<d → f (B+(i:ZMod r)+1)=f (B+i)) : f (B+(d:ZMod r))=f B := by
  have walk (t : ℕ) (ht : t≤d) : f (B+(t:ZMod r))=f B := by
    induction t with
    | zero => simp
    | succ t ih =>
      simpa only [Nat.cast_succ,← add_assoc] using (step t (by omega)).trans (ih (by omega))
  exact walk d le_rfl

/-- Uniform first-frequency blocks. The right chain fixes the entire
closed corridor at every frequency. A value at a given block start can
differ from this baseline only at its L preceding source shifts, and
the count assumption ensures L≤q. Different blocks may have the same
exceptional frequency. -/
theorem uniform_cauchy_graphs_all (h d q : ℕ) (hh : 1≤h) (hd : 2≤d)
    (rightSize : q≤h*(2*d-1)) (count : (h-1)*(2*d-1)≤q*(d+1)) :
    let W := 2*d-1
    let r := h*W
    let L := r-q*d-W
    let D := (d:ZMod r)
    let t (i : Fin h) := ((i.val*W:ℕ):ZMod r)
    ∃ P Q : Finset (ZMod r), P.card+h*d=r ∧ Q.card=q ∧ L≤q ∧
      (∀ i,t i∈P) ∧ (∀ x : ZMod r,∃ i,∃ o : Fin W,x=t i+(o.val:ZMod r)) ∧
      (∀ i,∀ j : Fin q,∀ f : ZMod r → ℂ, (∀ v∈P,f (v+1)=f v) →
        (∀ v∈Q,f (t i+(((j.val+1)*d:ℕ):ZMod r)-v-1)=f (t i+(((j.val+1)*d:ℕ):ZMod r)-v)) →
        f (t i+D)=f (t i)) ∧
      ∀ k : ZMod r,∀ f : ZMod r → ℂ,
        (∀ v∈P,f (v+1)=f v ∧ f (v+D)=f v) →
        (∀ v∈Q,f (k-v-1)=f (k-v) ∧ f (k-v-D)=f (k-v)) →
        (∀ i,∀ o : ℕ,o<W → f (t i+(o:ZMod r))=f (t i)) ∧
        (∀ a : ℕ,a≤q*d → f (k-(a:ZMod r))=f k) ∧
        ∀ i,f (t i)≠f k → ∃ l : ℕ,l<L ∧ k=t i-1-(l:ZMod r) := by
  classical
  intro W r L D t
  have hw : 0<W := by dsimp [W]; omega
  have : NeZero r := ⟨Nat.ne_of_gt (Nat.mul_pos hh hw)⟩
  have predEq : d-1+1=d := by omega
  have widthEq : (d-1)+d=W := by dsimp [W]; omega
  have size : (h-1)*W+W=r := by
    change (h-1)*W+W=h*W
    rw [← Nat.succ_mul,Nat.succ_eq_add_one,show h-1+1=h by omega]
  have kfit : L≤q := by
    change (h-1)*W≤q*(d+1) at count
    rw [Nat.mul_add,Nat.mul_one] at count
    dsimp [L]
    omega
  let pi (x : Fin h × Fin (d-1)) := x.2.val+W*x.1.val
  have small (o : Fin (d-1)) : o.val<W := by have := o.isLt; dsimp [W]; omega
  have limit (x : Fin h × Fin (d-1)) : pi x<r := by
    calc
      _ < W+W*x.1.val := Nat.add_lt_add_right (small x.2) _
      _ = W*(x.1.val+1) := by ring
      _ ≤ W*h := Nat.mul_le_mul_left _ x.1.isLt
      _ = r := Nat.mul_comm _ _
  have indexInj : Function.Injective pi := by
    intro x y eq
    have quo := congrArg (fun n : ℕ => n/W) eq
    have rem := congrArg (fun n : ℕ => n%W) eq
    simp only [pi,Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt (small _),zero_add] at quo
    simp only [pi,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (small _)] at rem
    exact Prod.ext (Fin.ext quo) (Fin.ext rem)
  obtain ⟨P,pc,centers⟩ := cauchy_wide_left_set pi limit indexInj
  have leftMem (i : Fin h) (o : ℕ) (ho : o<d-1) : t i+(o:ZMod r)∈P := by
    have mem := centers (i,⟨o,ho⟩)
    have eq : ((o+W*i.val:ℕ):ZMod r)=t i+(o:ZMod r) := by
      change ((o+W*i.val:ℕ):ZMod r)=((i.val*W:ℕ):ZMod r)+o
      push_cast
      ring
    exact eq ▸ mem
  let qn (j : Fin q) := j.val*d
  obtain ⟨Q,qc,rightMem⟩ := cauchy_right_modes rightSize (fun j => (qn j:ZMod r))
  have cover (x : ZMod r) : ∃ i,∃ o : Fin W,x=t i+(o.val:ZMod r) := by
    let i : Fin h := ⟨x.val/W,(Nat.div_lt_iff_lt_mul hw).mpr x.val_lt⟩
    let o : Fin W := ⟨x.val%W,Nat.mod_lt _ hw⟩
    have eq : i.val*W+o.val=x.val := by
      change x.val/W*W+x.val%W=x.val
      rw [Nat.mul_comm,Nat.div_add_mod]
    refine ⟨i,o,?_⟩
    change x=((i.val*W:ℕ):ZMod r)+(o.val:ZMod r)
    rw [← Nat.cast_add,eq,ZMod.natCast_zmod_val]
  refine ⟨P,Q,?_,qc,kfit,?_,cover,?_,?_⟩
  · simp only [Fintype.card_prod,Fintype.card_fin] at pc
    rw [pc,← Nat.mul_add,widthEq]
  · intro i
    simpa only [Nat.cast_zero,add_zero] using leftMem i 0 (by omega)
  · intro i j f left right
    apply cauchy_wide_unit_path f (t i) d
    intro o ho
    by_cases prev : o<d-1
    · exact left _ (leftMem i o prev)
    · have point := right (qn j:ZMod r) (rightMem j)
      have sum : (((j.val+1)*d:ℕ):ZMod r)=(qn j:ZMod r)+D := by
        rw [Nat.add_mul,Nat.one_mul,Nat.cast_add]
      rw [sum,show t i+((qn j:ZMod r)+D)-(qn j:ZMod r)=t i+D by abel] at point
      have last : (o:ZMod r)+1=D := by
        change (o:ZMod r)+1=(d:ZMod r)
        rw [← Nat.cast_add_one,show o+1=d by omega]
      rw [add_assoc,last,← point,← last]
      congr 1
      abel
  · intro k f left right
    have flat (i : Fin h) (o : ℕ) (ho : o<W) : f (t i+(o:ZMod r))=f (t i) := by
      apply block_constant (L:=d-1) f (t i) _ o (by dsimp [W] at ho; omega)
      intro j
      simpa only [predEq,D] using left _ (leftMem i j.val j.isLt)
    have chain (i : ℕ) (hi : i≤q) : f (k-((i*d:ℕ):ZMod r))=f k := by
      induction i with
      | zero => simp
      | succ i prev =>
        rw [Nat.succ_mul,Nat.cast_add,← sub_sub]
        exact ((right _ (rightMem ⟨i,by omega⟩)).2).trans (prev (by omega))
    have hit (i : Fin h) (near : (k-t i).val<q*d+W) : f (t i)=f k := by
      obtain ⟨j,hj,o,ho,dist⟩ := chain_hits (by omega : 0<d) (by dsimp [W]; omega : d≤W) (le_refl (q*d+W)) near
      have diff : ((j*d:ℕ):ZMod r)+(o:ZMod r)=k-t i := by rw [← Nat.cast_add,dist,ZMod.natCast_zmod_val]
      have eq : t i+(o:ZMod r)=k-((j*d:ℕ):ZMod r) := by linear_combination diff
      exact (flat i _ ho).symm.trans ((congrArg f eq).trans (chain _ hj))
    refine ⟨flat,?_,?_⟩
    · intro a ha
      obtain ⟨i,o,eq⟩ := cover (k-(a:ZMod r))
      have diff : k-t i=((a+o.val:ℕ):ZMod r) := by rw [Nat.cast_add]; linear_combination eq
      have near : (k-t i).val<q*d+W := by
        rw [diff,ZMod.val_natCast]
        have m := Nat.mod_le (a+o.val) r
        have n := o.isLt
        omega
      exact (congrArg f eq).trans ((flat _ _ o.isLt).trans (hit _ near))
    · intro i bad
      have away : q*d+W≤(k-t i).val := by
        by_contra! near
        exact bad (hit i near)
      let n := (k-t i).val
      let l := r-(n+1)
      have hn : n<r := (k-t i).val_lt
      have sum : n+(1+l)=r := by dsimp [l]; omega
      have phase : k-t i+(1+(l:ZMod r))=0 := by
        rw [← ZMod.natCast_zmod_val (k-t i)]
        change (n:ZMod r)+(1+(l:ZMod r))=0
        rw [← Nat.cast_one (R:=ZMod r),← Nat.cast_add,← Nat.cast_add,sum,ZMod.natCast_self]
      refine ⟨l,?_,?_⟩
      · change q*d+W≤n at away
        dsimp [L,l]
        omega
      · linear_combination phase

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- Short and long blocks partition the top-residue frequency group. The
left modes are the regular centers in each short block and the shifted centers in each long block. -/
theorem mixed_cauchy_modes (h d s : ℕ) (hh : 1≤h) (hd : 2≤d) (hs : s≤h) :
    let r := h*(2*d-1)+2*s
    let W := 2*d-1
    let V := 2*d+1
    let sB (j : Fin (h-s)) : ZMod r := ((j.val*W:ℕ):ZMod r)
    let lB (j : Fin s) : ZMod r := (((h-s)*W+j.val*V:ℕ):ZMod r)
    ∃ P : Finset (ZMod r), P.card+(h*d+s)=r ∧
      (∀ j,∀ i : ℕ,i<d-1 → sB j+(i:ZMod r)∈P) ∧
      (∀ j,∀ i : ℕ,i=0 ∨ 2≤ i ∧ i≤d → lB j+(i:ZMod r)∈P) ∧
      ∀ x : ZMod r,(∃ j,∃ i : Fin W,x=sB j+(i.val:ZMod r)) ∨
        ∃ j,∃ i : Fin V,x=lB j+(i.val:ZMod r) := by
  classical
  intro r W V sB lB
  let L := d-1
  have predEq : L+1=d := by dsimp [L]; omega
  have hw : W+1=2*d := by dsimp [W]; omega
  have widths : (h-s)*W+s*V=r := by
    have split := congrArg (·*W) (Nat.sub_add_cancel hs)
    change (h-s+s)*W=h*W at split
    rw [show V=W+2 by dsimp [V,W]; omega]
    change (h-s)*W+s*(W+2)=h*W+2*s
    nlinarith only [split]
  have : NeZero r := ⟨Nat.ne_of_gt (Nat.add_pos_left (Nat.mul_pos hh (by dsimp [W]; omega : 0<W)) _)⟩
  let G := (Fin (h-s) × Fin W) ⊕ (Fin s × Fin V)
  let M := (Fin (h-s) × Fin L) ⊕ (Fin s × Fin (L+1))
  let slot : G ≃ Fin r :=
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr widths)
  let residue : Fin r ↪ ZMod r :=
    { toFun := fun i => (i.val:ZMod r)
      inj' := by
        intro i j eq
        apply Fin.ext
        have raw := congrArg ZMod.val eq
        simpa only [ZMod.val_natCast_of_lt i.isLt,ZMod.val_natCast_of_lt j.isLt] using raw }
  let enc : G ↪ ZMod r := slot.toEmbedding.trans residue
  have all (x : ZMod r) : ∃ p,enc p=x := by
    obtain ⟨p,hp⟩ := slot.surjective ⟨x.val,x.val_lt⟩
    refine ⟨p,?_⟩
    change ((slot p).val:ZMod r)=x
    rw [hp,ZMod.natCast_zmod_val]
  have seval (j : Fin (h-s)) (i : Fin W) : enc (.inl (j,i))=sB j+(i.val:ZMod r) := by
    change ((i.val+W*j.val:ℕ):ZMod r)=((j.val*W:ℕ):ZMod r)+i.val
    push_cast
    ring
  have leval (j : Fin s) (i : Fin V) : enc (.inr (j,i))=lB j+(i.val:ZMod r) := by
    change (((h-s)*W+(i.val+V*j.val):ℕ):ZMod r)=(((h-s)*W+j.val*V:ℕ):ZMod r)+i.val
    push_cast
    ring
  obtain ⟨lc,lcrange⟩ := long_centers L
  let lcv : Fin (L+1) ↪ Fin V := lc.trans (finCongr (by dsimp [V]; omega : 2*L+3=V)).toEmbedding
  let sc : Fin L ↪ Fin W := Fin.castLEEmb (by dsimp [W,L]; omega)
  let pick : M ↪ G := ((Function.Embedding.refl (Fin (h-s))).prodMap sc).sumMap
    ((Function.Embedding.refl (Fin s)).prodMap lcv)
  let pe := pick.trans enc
  let P := Finset.univ.map pe
  have smem (j : Fin (h-s)) (i : ℕ) (hi : i<d-1) : sB j+(i:ZMod r)∈P := by
    let t : Fin L := ⟨i,hi⟩
    have hm : pe (.inl (j,t))∈P := Finset.mem_map.mpr ⟨.inl (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inl (j,sc t))∈P at hm
    simpa only [seval,show (sc t).val=i from rfl] using hm
  have lmem (j : Fin s) (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤d) : lB j+(i:ZMod r)∈P := by
    obtain ⟨t,ht⟩ := (lcrange i).mpr (predEq ▸ hi)
    have hm : pe (.inr (j,t))∈P := Finset.mem_map.mpr ⟨.inr (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inr (j,lcv t))∈P at hm
    simpa only [leval,show (lcv t).val=(lc t).val from rfl,ht] using hm
  have card : P.card+(h*d+s)=r := by
    simp only [P,Finset.card_map,Finset.card_univ,M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    have z := congrArg (h*·) (show L+d=W by dsimp [L,W]; omega)
    have split := congrArg (·*L) (Nat.sub_add_cancel hs)
    change (h-s+s)*L=h*L at split
    change h*(L+d)=h*W at z
    change (h-s)*L+s*(L+1)+(h*d+s)=h*W+2*s
    nlinarith only [z,split]
  refine ⟨P,card,smem,lmem,?_⟩
  intro x
  obtain ⟨⟨j,i⟩|⟨j,i⟩,rfl⟩ := all x
  · exact Or.inl ⟨j,i,seval j i⟩
  · exact Or.inr ⟨j,i,leval j i⟩

end CriticalThreeQuotient

namespace CriticalThreeQuotient

private theorem wide_cauchy_long_block {L : ℕ} (hL : 1≤L) {C : Type*} (f : ℕ → C)
    (first : f 1=f 0 ∧ f (L+1)=f 0)
    (edges : ∀ t : ℕ,2≤t → t≤L+1 → f (t+1)=f t ∧ f (t+(L+1))=f t) :
    ∀ o : ℕ,o<2*L+3 → f o=f 0 := by
  have run (t : ℕ) (lo : 2≤t) (hi : t≤L+2) : f t=f 2 := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases eq : t+1=2
      · rw [eq]
      · exact ((edges t (by omega) (by omega)).1).trans (ih (by omega) (by omega))
  have two : f 2=f 0 := (run (L+1) (by omega) (by omega)).symm.trans first.2
  intro o ho
  by_cases small : o<2
  · rcases (by omega : o=0 ∨ o=1) with rfl|rfl
    · rfl
    · exact first.1
  · by_cases mid : o≤L+2
    · exact (run o (by omega) mid).trans two
    · let t := o-(L+1)
      have eq : t+(L+1)=o := by dsimp [t]; omega
      have lo : 2≤t := by dsimp [t]; omega
      have hi : t≤L+1 := by dsimp [t]; omega
      rw [← eq]
      exact ((edges t lo hi).2).trans ((run t lo (by omega)).trans two)

/-- Unit paths for every pulse, and the classification of the ordinary
frequency graph. In each exceptional phase only a block with the displayed
nearby start may fail to equal the common right-chain value. -/
theorem mixed_cauchy_graphs_all (h d s q : ℕ) (hh : 1≤h) (hd : 2≤d) (hs : s≤h)
    (rightSize : q≤h*(2*d-1)+2*s) (count : h*(2*d-1)+2*s≤q*(d+1)+(2*d-1)) :
    let W := 2*d-1
    let V := 2*d+1
    let r := h*W+2*s
    let L := r-q*d-W
    let D := (d:ZMod r)
    let tS (i : Fin (h-s)) := ((i.val*W:ℕ):ZMod r)
    let tL (i : Fin s) := (((h-s)*W+i.val*V:ℕ):ZMod r)
    ∃ P Q : Finset (ZMod r), P.card+(h*d+s)=r ∧ Q.card=q ∧ L≤q ∧
      (∀ i,tS i∈P) ∧ (∀ i,tL i∈P) ∧
      (∀ x : ZMod r,(∃ i,∃ o : Fin W,x=tS i+(o.val:ZMod r)) ∨
        ∃ i,∃ o : Fin V,x=tL i+(o.val:ZMod r)) ∧
      (∀ i,∀ j : Fin q,∀ f : ZMod r → ℂ,
        (∀ v∈P,f (v+1)=f v) →
        (∀ v∈Q,f (tS i+(((j.val+1)*d:ℕ):ZMod r)-v-1)=f (tS i+(((j.val+1)*d:ℕ):ZMod r)-v)) →
        f (tS i+D)=f (tS i)) ∧
      (∀ i,∀ j : Fin q,∀ f : ZMod r → ℂ,
        (∀ v∈P,f (v+1)=f v) →
        (∀ v∈Q,f (tL i+2+((j.val*d:ℕ):ZMod r)-v-1)=f (tL i+2+((j.val*d:ℕ):ZMod r)-v)) →
        f (tL i+D)=f (tL i)) ∧
      ∀ k : ZMod r,∀ f : ZMod r → ℂ,
        (∀ v∈P,f (v+1)=f v ∧ f (v+D)=f v) →
        (∀ v∈Q,f (k-v-1)=f (k-v) ∧ f (k-v-D)=f (k-v)) →
        (∀ i,∀ o : ℕ,o<W → f (tS i+(o:ZMod r))=f (tS i)) ∧
        (∀ i,∀ o : ℕ,o<V → f (tL i+(o:ZMod r))=f (tL i)) ∧
        (∀ a : ℕ,a≤q*d → f (k-(a:ZMod r))=f k) ∧
        (∀ i,f (tS i)≠f k → ∃ l : ℕ,l<L ∧ k=tS i-1-(l:ZMod r)) ∧
        (∀ i,f (tL i)≠f k → ∃ l : ℕ,l+2<L ∧ k=tL i-1-(l:ZMod r)) := by
  classical
  intro W V r L D tS tL
  have hr : 0<r := Nat.add_pos_left (Nat.mul_pos hh (by dsimp [W]; omega : 0<W)) _
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨P,cardP,small,big,partition⟩ := mixed_cauchy_modes h d s hh hd hs
  have cap : L≤q := by
    change r≤q*(d+1)+W at count
    rw [Nat.mul_add,Nat.mul_one] at count
    dsimp [L]
    omega
  let qn (i : Fin q) := i.val*d
  obtain ⟨Q,cardQ,modes⟩ := cauchy_right_modes rightSize (fun i => (qn i:ZMod r))
  refine ⟨P,Q,cardP,cardQ,cap,?_,?_,partition,?_,?_,?_⟩
  · intro i
    simpa only [Nat.cast_zero,add_zero] using small i 0 (by omega)
  · intro i
    simpa only [Nat.cast_zero,add_zero] using big i 0 (.inl rfl)
  · intro i j f left right
    apply cauchy_wide_unit_path f (tS i) d
    intro o ho
    by_cases old : o<d-1
    · exact left _ (small i o old)
    · have div : (qn j:ZMod r)+D=(((j.val+1)*d:ℕ):ZMod r) := by
        rw [Nat.add_mul,Nat.one_mul,Nat.cast_add]
      have last := right (qn j:ZMod r) (modes j)
      rw [show tS i+(((j.val+1)*d:ℕ):ZMod r)-(qn j:ZMod r)=tS i+D by rw [← div]; abel] at last
      have endpoint : (o:ZMod r)+1=D := by
        change (o:ZMod r)+1=(d:ZMod r)
        rw [← Nat.cast_add_one,show o+1=d by omega]
      rw [add_assoc,endpoint,← last,← endpoint]
      congr 1
      abel
  · intro i j f left right
    apply cauchy_wide_unit_path f (tL i) d
    intro o ho
    by_cases seam : o=1
    · subst o
      have last := right (qn j:ZMod r) (modes j)
      change f (tL i+2+((j.val*d:ℕ):ZMod r)-((j.val*d:ℕ):ZMod r)-1)=
        f (tL i+2+((j.val*d:ℕ):ZMod r)-((j.val*d:ℕ):ZMod r)) at last
      rw [add_sub_cancel_right] at last
      simpa only [Nat.cast_one,show tL i+2-1=tL i+1 by ring,show tL i+1+1=tL i+2 by ring] using last.symm
    · exact left _ (big i o (by omega))
  · intro k f left right
    have predEq : d-1+1=d := by omega
    have sflat (i : Fin (h-s)) (o : ℕ) (ho : o<W) : f (tS i+(o:ZMod r))=f (tS i) := by
      apply block_constant (L:=d-1) f (tS i) _ o (by dsimp [W] at ho; omega)
      intro w
      simpa only [predEq,D] using left _ (small i w.val w.isLt)
    have lflat (i : Fin s) (o : ℕ) (ho : o<V) : f (tL i+(o:ZMod r))=f (tL i) := by
      let g (a : ℕ) := f (tL i+(a:ZMod r))
      have step (a : ℕ) (ok : a=0 ∨ 2≤a ∧ a≤d-1+1) : g (a+1)=g a ∧ g (a+(d-1+1))=g a := by
        have e := left _ (big i a (predEq ▸ ok))
        change f (tL i+(a:ZMod r)+1)=f (tL i+a) ∧ f (tL i+(a:ZMod r)+D)=f (tL i+a) at e
        simpa only [g,predEq,D,Nat.cast_add,Nat.cast_one,← add_assoc] using e
      have first := step 0 (.inl rfl)
      have last := wide_cauchy_long_block (L:=d-1) (by omega) g (by simpa only [zero_add] using first)
        (fun a lo hi => step a (.inr ⟨lo,hi⟩)) o (by dsimp [V] at ho; omega)
      simpa only [g,Nat.cast_zero,add_zero] using last
    have chain (a : ℕ) (ha : a≤q) : f (k-((a*d:ℕ):ZMod r))=f k := by
      induction a with
      | zero => simp
      | succ t ih =>
        rw [Nat.succ_mul,Nat.cast_add,← sub_sub]
        exact ((right _ (modes ⟨t,by omega⟩)).2).trans (ih (by omega))
    have hit (z : ZMod r) (w : ℕ) (dw : d≤w) (close : (k-z).val<q*d+w)
        (flat : ∀ o : ℕ,o<w → f (z+(o:ZMod r))=f z) : f z=f k := by
      obtain ⟨a,ha,o,ho,eq⟩ := chain_hits (by omega : 0<d) dw (le_refl (q*d+w)) close
      have d0 : ((a*d:ℕ):ZMod r)+(o:ZMod r)=k-z := by
        rw [← Nat.cast_add,eq,ZMod.natCast_zmod_val]
      have join : z+(o:ZMod r)=k-((a*d:ℕ):ZMod r) := by linear_combination d0
      exact (flat _ ho).symm.trans ((congrArg f join).trans (chain _ ha))
    have corridor (a : ℕ) (ha : a≤q*d) : f (k-(a:ZMod r))=f k := by
      have pin (z : ZMod r) (w o : ℕ) (dw : d≤w) (ho : o<w) (eq : k-(a:ZMod r)=z+(o:ZMod r))
          (flat : ∀ y : ℕ,y<w → f (z+(y:ZMod r))=f z) : f (k-(a:ZMod r))=f k := by
        have diff : k-z=((a+o:ℕ):ZMod r) := by rw [Nat.cast_add]; linear_combination eq
        have near : (k-z).val<q*d+w := by
          rw [diff,ZMod.val_natCast]
          have lim := Nat.mod_le (a+o) r
          omega
        exact (congrArg f eq).trans ((flat _ ho).trans (hit z w dw near flat))
      rcases partition (k-(a:ZMod r)) with ⟨i,o,eq⟩|⟨i,o,eq⟩
      · exact pin (tS i) W o.val (by dsimp [W]; omega) o.isLt eq (sflat i)
      · exact pin (tL i) V o.val (by dsimp [V]; omega) o.isLt eq (lflat i)
    have exceptional (z : ZMod r) (w : ℕ) (dw : d≤w) (flat : ∀ o : ℕ,o<w → f (z+(o:ZMod r))=f z)
        (bad : f z≠f k) : ∃ l : ℕ,q*d+w+l+1≤r ∧ k=z-1-(l:ZMod r) := by
      have away : q*d+w≤(k-z).val := by
        by_contra! near
        exact bad (hit z w dw near flat)
      let t := (k-z).val
      let l := r-(t+1)
      have ht : t<r := (k-z).val_lt
      have eq : t+(1+l)=r := by dsimp [l]; omega
      have phase : k-z+(1+(l:ZMod r))=0 := by
        rw [← ZMod.natCast_zmod_val (k-z)]
        change (t:ZMod r)+(1+(l:ZMod r))=0
        rw [← Nat.cast_one (R:=ZMod r),← Nat.cast_add,← Nat.cast_add,eq,ZMod.natCast_self]
      refine ⟨l,?_,?_⟩
      · change q*d+w≤t at away
        omega
      · linear_combination phase
    refine ⟨sflat,lflat,corridor,?_,?_⟩
    · intro i bad
      obtain ⟨l,limit,phase⟩ := exceptional _ W (by dsimp [W]; omega) (sflat i) bad
      exact ⟨l,by dsimp [L]; omega,phase⟩
    · intro i bad
      obtain ⟨l,limit,phase⟩ := exceptional _ V (by dsimp [V]; omega) (lflat i) bad
      have wide : V=W+2 := by dsimp [V,W]; omega
      rw [wide] at limit
      exact ⟨l,by dsimp [L]; omega,phase⟩

end CriticalThreeQuotient

namespace CriticalHigher.CauchyPulses

open Polynomial

/-- A Cauchy matrix with distinct row nodes, distinct column poles and at
least as many rows as columns has trivial kernel. -/
theorem cauchy_separates {K J L : Type*} [Field K] [Fintype J] [Fintype L]
    (row : J → K) (col : L → K) (row_inj : Function.Injective row) (col_inj : Function.Injective col)
    (disjoint : ∀ j l, row j ≠ col l) (room : Fintype.card L ≤ Fintype.card J)
    (f : L → K) (zero : ∀ j, (∑ l, f l/(row j-col l))=0) : f=0 := by
  classical
  funext p
  have positive : 0 < Fintype.card L := Fintype.card_pos_iff.mpr ⟨p⟩
  let Q (l : L) : K[X] := ∏ k ∈ Finset.univ.erase l, (X-C (col k))
  let N : K[X] := ∑ l, C (f l)*Q l
  have degree : N.natDegree ≤ Fintype.card L-1 := by
    apply natDegree_sum_le_of_forall_le
    intro l _
    apply (natDegree_C_mul_le _ _).trans
    change (∏ k ∈ Finset.univ.erase l, (X-C (col k))).natDegree ≤ _
    rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ l),Finset.card_univ]
  have evaluate (t : K) : N.eval t = ∑ l, f l*∏ k ∈ Finset.univ.erase l, (t-col k) := by
    simp only [N,Q,eval_finsetSum,eval_mul,eval_C,eval_prod,eval_sub,eval_X]
  have roots (j : J) : N.eval (row j)=0 := by
    rw [evaluate]
    calc
      _ = (∑ l, f l/(row j-col l))*(∏ k, (row j-col k)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        let P := ∏ k ∈ Finset.univ.erase l, (row j-col k)
        have factor : P*(row j-col l) = ∏ k, (row j-col k) :=
          Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ l)
        rw [← factor]
        change f l*P=(f l/(row j-col l))*(P*(row j-col l))
        calc
          _ = (f l/(row j-col l)*(row j-col l))*P := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (disjoint j l))]
          _ = _ := by ring
      _ = 0 := by rw [zero,zero_mul]
  have ident := eq_zero_of_natDegree_lt_card_of_eval_eq_zero N row_inj roots (by omega)
  have pole := congrArg (Polynomial.eval (col p)) ident
  rw [evaluate,eval_zero,Finset.sum_eq_single p] at pole
  · have product : (∏ k ∈ Finset.univ.erase p, (col p-col k)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact sub_ne_zero.mpr (fun eq => Finset.ne_of_mem_erase hk (col_inj eq).symm)
    exact (mul_eq_zero.mp pole).resolve_right product
  · intro l _ hl
    have mem : p ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨Ne.symm hl,Finset.mem_univ p⟩
    rw [Finset.prod_eq_zero mem (sub_self (col p)),mul_zero]
  · simp

end CriticalHigher.CauchyPulses

namespace CriticalHigher.CauchyPulses

private lemma separated {r : ℕ} [NeZero r] (α : ℂ) (large : 1 < ‖α‖) (a b : ZMod r) :
    α*ZMod.stdAddChar a ≠ ZMod.stdAddChar b := by
  intro eq
  have h := congrArg (fun t : ℂ => ‖t‖) eq
  change ‖α*ZMod.stdAddChar a‖ = ‖ZMod.stdAddChar b‖ at h
  rw [norm_mul,ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,Circle.norm_coe,Circle.norm_coe,mul_one] at h
  exact large.ne' h

/-- The fixed cyclic pulse is everywhere nonzero. -/
theorem pulse_nonzero {r : ℕ} [NeZero r] (e : ZMod r) :
    (1/(1-2*ZMod.stdAddChar e) : ℂ) ≠ 0 := by
  apply one_div_ne_zero
  apply sub_ne_zero.mpr
  intro eq
  apply separated 2 (by norm_num) e 0
  rw [AddChar.map_zero_eq_one]
  exact eq.symm

private lemma pulse_fraction (α a b t : ℂ) (bne : b≠0) (apart : α*a≠b) :
    (1/(1-α*(a/b)))*t = (-b*t)/(α*a-b) := by
  have den : 1-α*(a/b) = (b-α*a)/b := by field_simp [bne]
  rw [den]
  field_simp [bne,sub_ne_zero.mpr apart,sub_ne_zero.mpr (Ne.symm apart)]
  ring

/-- Multiplicative separation of the two character circles realizes every
such cyclic restriction as a Cauchy matrix with nonzero column weights. -/
theorem scaled_cyclic_kernel {r : ℕ} [NeZero r] {J L : Type*} [Fintype J] [Fintype L]
    (α : ℂ) (large : 1 < ‖α‖) (row : J → ZMod r) (col : L → ZMod r)
    (row_inj : Function.Injective row) (col_inj : Function.Injective col)
    (room : Fintype.card L ≤ Fintype.card J) (f : L → ℂ)
    (zero : ∀ j, (∑ l, (1/(1-α*ZMod.stdAddChar (row j-col l)))*f l)=0) : f=0 := by
  let χ : AddChar (ZMod r) ℂ := ZMod.stdAddChar
  have nz (e : ZMod r) : χ e ≠ 0 := (AddChar.val_isUnit _ _).ne_zero
  have αne : α≠0 := by intro eq; norm_num [eq] at large
  have rows : Function.Injective (fun j => α*χ (row j)) := fun _ _ eq =>
    row_inj (ZMod.injective_stdAddChar (mul_left_cancel₀ αne eq))
  have cols : Function.Injective (fun l => χ (col l)) := ZMod.injective_stdAddChar.comp col_inj
  let w (l : L) := -χ (col l)*f l
  have vanishes : w=0 := by
    apply cauchy_separates (fun j => α*χ (row j)) (fun l => χ (col l)) rows cols
      (fun j l => separated α large (row j) (col l)) room w
    intro j
    rw [← zero j]
    apply Finset.sum_congr rfl
    intro l _
    change (-χ (col l)*f l)/(α*χ (row j)-χ (col l)) = (1/(1-α*χ (row j-col l)))*f l
    rw [AddChar.map_sub_eq_div]
    exact (pulse_fraction α _ _ _ (nz _) (separated α large _ _)).symm
  funext l
  exact (mul_eq_zero.mp (congrFun vanishes l : -χ (col l)*f l=0)).resolve_left (neg_ne_zero.mpr (nz _))

/-- One explicit pulse works for every choice of distinct rows and columns,
including empty index sets. -/
theorem cyclic_kernel {r q m : ℕ} [NeZero r] (row : Fin q → ZMod r) (col : Fin m → ZMod r)
    (row_inj : Function.Injective row) (col_inj : Function.Injective col) (room : m ≤ q)
    (f : Fin m → ℂ) (zero : ∀ j, (∑ l, (1/(1-2*ZMod.stdAddChar (row j-col l)))*f l)=0) : f=0 :=
  scaled_cyclic_kernel 2 (by norm_num) row col row_inj col_inj (by simpa only [Fintype.card_fin] using room) f zero

theorem cyclic_mulVec_injective {r q m : ℕ} [NeZero r] (row : Fin q → ZMod r) (col : Fin m → ZMod r)
    (row_inj : Function.Injective row) (col_inj : Function.Injective col) (room : m ≤ q) :
    Function.Injective (Matrix.of (fun j l => (1/(1-2*ZMod.stdAddChar (row j-col l)) : ℂ))).mulVec := by
  let M := Matrix.of (fun j l => (1/(1-2*ZMod.stdAddChar (row j-col l)) : ℂ))
  change Function.Injective M.mulVec
  intro f g eq
  have hz : M.mulVec (f-g)=0 := by rw [Matrix.mulVec_sub,eq,sub_self]
  exact sub_eq_zero.mp (cyclic_kernel row col row_inj col_inj room (f-g) (fun j => congrFun hz j))

/-- The quantification over all rectangular restrictions occurs after
choosing the nowhere-zero function on the group. -/
theorem exists_cyclic_pulse (r : ℕ) [NeZero r] :
    ∃ pulse : ZMod r → ℂ, (∀ e, pulse e≠0) ∧
      ∀ (q m : ℕ) (row : Fin q → ZMod r) (col : Fin m → ZMod r),
        Function.Injective row → Function.Injective col → m≤q → ∀ f : Fin m → ℂ,
        (∀ j, (∑ l, pulse (row j-col l)*f l)=0) → f=0 :=
  ⟨fun e => 1/(1-2*ZMod.stdAddChar e),pulse_nonzero,fun _ _ row col hr hc room => cyclic_kernel row col hr hc room⟩

end CriticalHigher.CauchyPulses

namespace CriticalHigher.CauchyPulses

private lemma phase_cast_injective {r L : ℕ} [NeZero r] (hL : L ≤ r) :
    Function.Injective (fun l : Fin L => (l.val : ZMod r)) := by
  intro i j he
  apply Fin.ext
  have h := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt (lt_of_lt_of_le i.isLt hL),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le j.isLt hL)] using h

/-- A sum whose Fourier mode is supported on the L consecutive phases
before t can be reindexed by these phases, for every pulse function. -/
theorem block_sum_reindex {r L : ℕ} [NeZero r] (t shift : ZMod r) (hL : L ≤ r)
    (c x : ZMod r → ℂ)
    (support : ∀ k, (∀ l : Fin L, k ≠ t-1-(l.val : ZMod r)) → x k = 0) :
    (∑ e : ZMod r, c e * x (t+shift+e)) =
      ∑ l : Fin L, c (-shift-1-(l.val : ZMod r)) * x (t-1-(l.val : ZMod r)) := by
  classical
  let E : Fin L ↪ ZMod r :=
    { toFun := fun l => -shift-1-(l.val : ZMod r)
      inj' := by
        intro i j he
        apply phase_cast_injective hL
        change -shift-1-(i.val : ZMod r) = -shift-1-(j.val : ZMod r) at he
        linear_combination -he }
  let F (e : ZMod r) := c e * x (t+shift+e)
  have phase (l : Fin L) : t+shift+E l = t-1-(l.val : ZMod r) := by
    change t+shift+(-shift-1-(l.val : ZMod r)) = _
    abel
  have restrict : (∑ e ∈ Finset.univ.map E, F e) = ∑ e : ZMod r, F e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have vanished : x (t+shift+e) = 0 := by
      apply support
      intro l hl
      apply he
      refine Finset.mem_map.mpr ⟨l,Finset.mem_univ _,?_⟩
      change -shift-1-(l.val : ZMod r) = e
      linear_combination -hl
    simp [F,vanished]
  change (∑ e : ZMod r, F e) = _
  rw [←restrict,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro l _
  simp only [F,phase]
  rfl

/-- The step-d row centers remain distinct before a whole period. -/
private lemma cauchy_row_injective {r q d : ℕ} [NeZero r] (τ : ZMod r)
    (hd : 0 < d) (cap : q*d ≤ r) :
    Function.Injective (fun j : Fin q => -τ-((j.val*d : ℕ) : ZMod r)-1) := by
  intro i j eq
  have he : ((i.val*d : ℕ) : ZMod r) = ((j.val*d : ℕ) : ZMod r) := by
    change -τ-((i.val*d : ℕ) : ZMod r)-1 = -τ-((j.val*d : ℕ) : ZMod r)-1 at eq
    linear_combination -eq
  have hi := (Nat.mul_lt_mul_of_pos_right i.isLt hd).trans_le cap
  have hj := (Nat.mul_lt_mul_of_pos_right j.isLt hd).trans_le cap
  have equality := congrArg ZMod.val he
  simp only [ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt hj] at equality
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd equality)

/-- Impose translated rows on the whole cyclic group, restrict to the block's
support, and apply any nonsingular rectangular translate kernel. -/
private lemma block_kernel_with {r q d L : ℕ} [NeZero r] (c : ZMod r → ℂ)
    (kernel : ∀ (row : Fin q → ZMod r) (col : Fin L → ZMod r),
      Function.Injective row → Function.Injective col → L ≤ q →
      ∀ f : Fin L → ℂ, (∀ j, (∑ l, c (row j-col l)*f l) = 0) → f = 0)
    (t τ : ZMod r) (hd : 0 < d) (cap : q*d ≤ r) (room : L ≤ q) (x : ZMod r → ℂ)
    (support : ∀ k, (∀ l : Fin L, k ≠ t-1-(l.val : ZMod r)) → x k = 0)
    (rows : ∀ j : Fin q, (∑ e : ZMod r, c e * x (t+τ+((j.val*d : ℕ) : ZMod r)+e)) = 0) :
    x = 0 := by
  let row (j : Fin q) := -τ-((j.val*d : ℕ) : ZMod r)-1
  let col (l : Fin L) := (l.val : ZMod r)
  let f (l : Fin L) := x (t-1-(l.val : ZMod r))
  have hL : L ≤ r := room.trans ((Nat.le_mul_of_pos_right q hd).trans cap)
  have vanishes (j : Fin q) : (∑ l, c (row j-col l)*f l) = 0 := by
    let step : ZMod r := ((j.val*d : ℕ) : ZMod r)
    have reindex := block_sum_reindex t (τ+step) hL c x support
    have z : (∑ e : ZMod r, c e*x (t+(τ+step)+e)) = 0 := by
      simpa only [add_assoc] using rows j
    rw [reindex] at z
    convert z using 1
    apply Finset.sum_congr rfl
    intro l _
    have phase : row j-col l = -(τ+step)-1-(l.val : ZMod r) := by dsimp [row,col,step]; abel
    rw [phase]
  have cut := kernel row col (cauchy_row_injective τ hd cap) (phase_cast_injective hL) room f vanishes
  funext k
  by_cases hit : ∃ l : Fin L, k = t-1-(l.val : ZMod r)
  · obtain ⟨l,rfl⟩ := hit
    exact congrFun cut l
  · exact support k (fun l h => hit ⟨l,h⟩)

end CriticalHigher.CauchyPulses

namespace CriticalHigher.CauchyPulses

/-- From all translated Cauchy-pulse equations, a consecutive block of at
most q exceptional phases vanishes. The offset can be any cyclic residue. -/
theorem block_kernel {r q d L : ℕ} [NeZero r] (t τ : ZMod r)
    (hd : 0 < d) (cap : q*d < r) (room : L ≤ q) (x : ZMod r → ℂ)
    (support : ∀ k, (∀ l : Fin L, k ≠ t-1-(l.val : ZMod r)) → x k = 0)
    (rows : ∀ j : Fin q, (∑ e : ZMod r, (1/(1-2*ZMod.stdAddChar e)) *
      x (t+τ+((j.val*d : ℕ) : ZMod r)+e)) = 0) : x = 0 := by
  apply block_kernel_with (fun e => 1/(1-2*ZMod.stdAddChar e)) _ t τ hd cap.le room x support rows
  intro row col hr hc hl f zero
  exact cyclic_kernel row col hr hc hl f zero

end CriticalHigher.CauchyPulses

namespace CriticalThreeTop

/-- Each pulse equation on a restored unit path is a translated Cauchy
measurement of the possible exceptional values at one block start. -/
theorem clear_cauchy_rows {r d q q' L : ℕ} [NeZero r] (t : ZMod r) (shift : ℕ)
    (hd : 0<d) (noWrap : q'*d<r) (room : L≤q') (inside : ∀ j : Fin q', j.val*d+shift≤q*d)
    (F : ZMod r → ZMod r → ℂ)
    (corridor : ∀ k a, a≤q*d → F k (k-(a:ZMod r))=F k k)
    (exceptional : ∀ k, F k t≠F k k → ∃ l : ℕ, l<L ∧ k=t-1-(l:ZMod r))
    (cuts : ∀ j : Fin q', ∑ e : ZMod r, (1/(1-2*ZMod.stdAddChar e)) *
      (F (t+shift+(((j.val+1)*d:ℕ):ZMod r)+e-d) (t+e) -
       F (t+shift+(((j.val+1)*d:ℕ):ZMod r)+e-d) t)=0) :
    ∀ k,F k t=F k k := by
  let x (k : ZMod r) := F k k-F k t
  have zero : x=0 := by
    apply CriticalHigher.CauchyPulses.block_kernel t (shift:ZMod r) hd noWrap room
    · intro k away
      have equal : F k t=F k k := by
        by_contra bad
        obtain ⟨l,hl,at_l⟩ := exceptional k bad
        exact away ⟨l,hl⟩ at_l
      exact sub_eq_zero.mpr equal.symm
    · intro j
      apply Eq.trans _ (cuts j)
      apply Finset.sum_congr rfl
      intro e _
      let k := t+shift+((j.val*d:ℕ):ZMod r)+e
      have mode : t+shift+(((j.val+1)*d:ℕ):ZMod r)+e-d=k := by dsimp [k]; push_cast; ring
      have pos : t+e=k-((j.val*d+shift:ℕ):ZMod r) := by dsimp [k]; push_cast; ring
      rw [mode,pos,corridor k _ (inside j)]
  intro k
  exact (sub_eq_zero.mp (congrFun zero k)).symm

/-- With q right relations, the full complex tangent is obtained whenever
the right unit paths can separate the left blocks by Cauchy interpolation.
The gap can contain several entire marked blocks at a given frequency. -/
theorem mixed_cauchy_tangent (h d s q : ℕ) (hh : 1≤h) (hd : 2≤d) (hs : s≤h)
    (rightSize : q≤h*(2*d-1)+2*s)
    (capacity : h*(2*d-1)+2*s≤q*(d+1)+(2*d-1)) :
    let r := h*(2*d-1)+2*s
    let b := h*d+s
    let n := r-q
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  classical
  intro r b n
  let W := 2*d-1
  let V := 2*d+1
  let L := r-q*d-W
  have hr : 0<r := Nat.add_pos_left (Nat.mul_pos hh (by omega : 0<2*d-1)) _
  let : NeZero r := ⟨hr.ne'⟩
  let short (i : Fin (h-s)) : ZMod r := ((i.val*W:ℕ):ZMod r)
  let long (i : Fin s) : ZMod r := (((h-s)*W+i.val*V:ℕ):ZMod r)
  obtain ⟨P,Q,pCard,qCard,len,shortP,longP,partition,shortPaths,longPaths,base⟩ :=
    CriticalThreeQuotient.mixed_cauchy_graphs_all h d s q hh hd hs rightSize capacity
  let Tag := (Fin (h-s) × Fin q) ⊕ (Fin s × Fin (q-1))
  let pivot : Tag → ZMod r := Sum.elim (fun p => short p.1) (fun p => long p.1)
  let target : Tag → ZMod r := Sum.elim (fun p => short p.1+(((p.2.val+1)*d:ℕ):ZMod r))
    (fun p => long p.1+2+(((p.2.val+1)*d:ℕ):ZMod r))
  have counts : Q.card+n=r := by rw [qCard]; exact Nat.add_sub_of_le rightSize
  obtain ⟨_,_,Y,Z,span⟩ := CriticalThreePerturbation.multipulse_tangent_of_graph_cards
    (d:ZMod r) (id : ZMod r → ZMod r) (fun e => 1/(1-2*ZMod.stdAddChar e)) P Q
    (b:=b) (n:=n) pCard counts target pivot (by
      rintro (⟨i,j⟩|⟨i,j⟩)
      · exact shortP i
      · exact longP i) (by
      rintro (⟨i,j⟩|⟨i,j⟩)
      · exact shortPaths i j
      · exact longPaths i ⟨j.val+1,by omega⟩) (by
      intro F left right extra
      have localData k := base k (F k) (left k) (right k)
      have smallLen : L≤q := len
      have shortGood (i : Fin (h-s)) (k : ZMod r) : F k (short i)=F k k := by
        by_cases wrap : r≤q*d
        · by_contra bad
          obtain ⟨l,hl,_⟩ := (localData k).2.2.2.1 i bad
          change l<L at hl
          dsimp [L] at hl
          omega
        apply clear_cauchy_rows (q:=q) (q':=q) (L:=L) (short i) 0 (by omega) (by omega) smallLen
          (fun j => by simpa using Nat.mul_le_mul_right d j.isLt.le) F
          (fun k => (localData k).2.2.1) (fun k => (localData k).2.2.2.1 i) _ k
        intro j
        simpa only [target,pivot,Sum.elim_inl,id_eq,Nat.cast_zero,add_zero] using extra (.inl (i,j))
      have longGood (i : Fin s) (k : ZMod r) : F k (long i)=F k k := by
        by_cases wrap : r≤q*d
        · by_contra bad
          obtain ⟨l,hl,_⟩ := (localData k).2.2.2.2 i bad
          change l+2<L at hl
          dsimp [L] at hl
          omega
        have noWrap : (q-1)*d<r := (Nat.mul_le_mul_right d (Nat.sub_le q 1)).trans_lt (by omega)
        apply clear_cauchy_rows (q:=q) (q':=q-1) (L:=L-2) (long i) 2 (by omega) noWrap
          (by omega) _ F (fun k => (localData k).2.2.1) _ _ k
        · intro j
          have one := Nat.mul_le_mul_right d (show j.val+1≤q by omega)
          rw [Nat.succ_mul] at one
          omega
        · intro k bad
          obtain ⟨l,hl,eq⟩ := (localData k).2.2.2.2 i bad
          change l+2<L at hl
          exact ⟨l,by omega,eq⟩
        · intro j
          simpa only [target,pivot,Sum.elim_inr,id_eq,Nat.cast_ofNat] using extra (.inr (i,j))
      have every (k j : ZMod r) : F k j=F k k := by
        rcases partition j with ⟨i,o,eq⟩|⟨i,o,eq⟩
        · rw [eq]
          exact ((localData k).1 i o.val o.isLt).trans (shortGood i k)
        · rw [eq]
          exact ((localData k).2.1 i o.val o.isLt).trans (longGood i k)
      exact fun k i j => (every k i).trans (every k j).symm)
  exact ⟨_,Y,Z,span⟩

end CriticalThreeTop

namespace CriticalThreeTop

/-- A criterion at arbitrary aspect ratio. The q=r−n translated right
measurements each contribute a row of a nonsingular Cauchy restriction. -/
theorem tangent_of_cauchy_capacity (b n r h : ℕ) (hh : 0<h) (width : 2*h≤b)
    (enough : n≤r) (level : r+h=2*b) (capacity : r+1≤(r-n+2)*(b/h)+(r-n)) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  let d := b/h
  let s := b%h
  let q := r-n
  have hd : 2≤d := (Nat.le_div_iff_mul_le hh).mpr width
  have hs : s<h := Nat.mod_lt _ hh
  have bsize : h*d+s=b := Nat.div_add_mod b h
  have twice : 2*d-1+1=2*d := by omega
  have prod := congrArg (fun t : ℕ => h*t) twice
  have rsize : h*(2*d-1)+2*s=r := by nlinarith only [prod,bsize,level]
  have cap : h*(2*d-1)+2*s≤q*(d+1)+(2*d-1) := by
    rw [rsize]
    change r+1≤(q+2)*d+q at capacity
    nlinarith only [capacity,twice]
  have rightSize : q≤h*(2*d-1)+2*s := rsize ▸ Nat.sub_le r n
  have witness := mixed_cauchy_tangent h d s q hh hd hs.le rightSize cap
  dsimp only at witness
  rwa [rsize,bsize,show r-q=n by dsimp [q]; omega] at witness

end CriticalThreeTop

namespace RemainingBoundary

/-- The pivot is supported at the first coordinate of both factors. Each other
point supplies one entry outside the first row and column. -/
private lemma slice_witness (p q : ℕ) (t : Fin (p*q+1)) :
    ∃ x : Fin (p*q+1) → Fin (p+1) → ℂ, ∃ y : Fin (p*q+1) → Fin (q+1) → ℂ,
      ∀ M : Fin (p+1) → Fin (q+1) → ℂ, ∃ u : Fin (p+1) → ℂ, ∃ v : Fin (q+1) → ℂ,
        ∃ w : Fin (p*q+1) → ℂ, ∀ i j,
          M i j = u i * y t j + x t i * v j + ∑ s, w s * (x s i * y s j) := by
  let e : Fin (p*q+1) ≃ Option (Fin p × Fin q) :=
    (finSuccEquiv' t).trans (Equiv.optionCongr finProdFinEquiv.symm)
  have ht : e t = none := by simp [e]
  let X : Option (Fin p × Fin q) → Fin (p+1) → ℂ
    | none, i => if i = 0 then 1 else 0
    | some z, i => if z.1.succ = i then 1 else 0
  let Y : Option (Fin p × Fin q) → Fin (q+1) → ℂ
    | none, j => if j = 0 then 1 else 0
    | some z, j => if z.2.succ = j then 1 else 0
  refine ⟨fun s => X (e s), fun s => Y (e s), ?_⟩
  intro M
  let W : Option (Fin p × Fin q) → ℂ
    | none => 0
    | some z => M z.1.succ z.2.succ
  refine ⟨fun i => M i 0, fun j => if j = 0 then 0 else M 0 j, fun s => W (e s), ?_⟩
  intro i j
  dsimp only
  rw [ht, e.sum_comp (fun z => W z * (X z i * Y z j))]
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [X, Y, W, Fintype.sum_option, Fintype.sum_prod_type, mul_ite, Finset.sum_ite_eq']

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
private lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

/-- A common choice of factors spans every marked matrix slice. -/
private lemma shared_slices (p q : ℕ) :
    ∃ x : Fin (p*q+1) → Fin (p+1) → ℂ, ∃ y : Fin (p*q+1) → Fin (q+1) → ℂ,
      ∀ t : Fin (p*q+1), ∀ M : Fin (p+1) → Fin (q+1) → ℂ,
        ∃ u : Fin (p+1) → ℂ, ∃ v : Fin (q+1) → ℂ, ∃ w : Fin (p*q+1) → ℂ,
          ∀ i j, M i j = u i * y t j + x t i * v j + ∑ s, w s * (x s i * y s j) := by
  classical
  let a := p+1
  let b := q+1
  let r := p*q+1
  let V := Fin r × (Fin a ⊕ Fin b)
  let I := Fin a × Fin b
  let J := Fin a ⊕ (Fin b ⊕ Fin r)
  let A (t : Fin r) : Matrix I J (MvPolynomial V ℂ) := fun (i,j) k =>
    match k with
    | .inl v => if v=i then X (t,.inr j) else 0
    | .inr (.inl v) => if v=j then X (t,.inl i) else 0
    | .inr (.inr s) => X (s,.inl i) * X (s,.inr j)
  have action (t : Fin r) (p : V → ℂ) (q : J → ℂ) (i : Fin a) (j : Fin b) :
      ((A t).map (eval p)).mulVec q (i,j) =
        q (.inl i) * p (t,.inr j) + p (t,.inl i) * q (.inr (.inl j)) +
          ∑ s, q (.inr (.inr s)) * (p (s,.inl i) * p (s,.inr j)) := by
    change (∑ k : J, eval p (A t (i,j) k) * q k) = _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [A,apply_ite,ite_mul,Finset.sum_ite_eq',mul_comm,mul_assoc,add_assoc]
  have span_iff (t : Fin r) (p : V → ℂ) :
      (∀ M : Fin a → Fin b → ℂ, ∃ u : Fin a → ℂ, ∃ v : Fin b → ℂ, ∃ w : Fin r → ℂ,
        ∀ i j, M i j = u i * p (t,.inr j) + p (t,.inl i) * v j +
          ∑ s, w s * (p (s,.inl i) * p (s,.inr j))) ↔
        Function.Surjective ((A t).map (eval p)).mulVec := by
    constructor
    · intro hs T
      obtain ⟨u,v,w,hw⟩ := hs fun i j => T (i,j)
      refine ⟨Sum.elim u (Sum.elim v w),?_⟩
      funext ⟨i,j⟩
      rw [action]
      exact (hw i j).symm
    · intro hA T
      obtain ⟨q,hq⟩ := hA fun ij => T ij.1 ij.2
      refine ⟨fun i => q (.inl i),fun j => q (.inr (.inl j)),fun s => q (.inr (.inr s)),?_⟩
      intro i j
      exact (congrFun hq (i,j)).symm.trans (action t p q i j)
  have each (t : Fin r) : ∃ p : V → ℂ, Function.Surjective ((A t).map (eval p)).mulVec := by
    obtain ⟨x,y,ht⟩ := slice_witness p q t
    let p (z : V) := z.2.elim (x z.1) (y z.1)
    exact ⟨p,(span_iff t p).mp ht⟩
  choose u hu using each
  choose Q hQ hgood using fun t => surjectivity_polynomial (A t) (u t) (hu t)
  have hprod : (∏ t, Q t) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hQ t
  obtain ⟨s,hs⟩ := CriticalReduction.Grid.nonvanishing (∏ t, Q t) _ hprod le_rfl
  let v (k : V) : ℂ := ((s k).val : ℂ)
  have hvals : (∏ t, eval v (Q t)) ≠ 0 := by simpa only [v,map_prod] using hs
  exact ⟨fun t i => v (t,.inl i),fun t j => v (t,.inr j),
    fun t => (span_iff t v).mpr (hgood t v (Finset.prod_ne_zero_iff.mp hvals t (Finset.mem_univ t)))⟩

/-- At the critical boundary there is an integer-grid tangent witness at the
dimension-count ceiling, with the same factor bound as the remaining formats. -/
lemma boundary_witness {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : c = (a-1)*(b-1)) :
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    let D := 2*(a*b*c)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k)) := by
  classical
  subst c
  dsimp only
  rw [Arxiv.«0805.3777».critical_ceilDiv ha hb]
  obtain _ | p := a
  · omega
  obtain _ | q := b
  · omega
  let c := p*q
  obtain ⟨x,y,hxy⟩ := shared_slices p q
  apply CriticalReduction.bounded_of_witness (a:=p+1) (b:=q+1) (c:=c) (r:=c+1)
  let z : Fin (c+1) → Fin c → ℂ := fun t k => if t = k.succ then 1 else 0
  refine ⟨x,y,z,?_⟩
  intro T
  choose u v w hw using fun k : Fin c => hxy k.succ (fun i j => T i j k)
  let U : Fin (c+1) → Fin (p+1) → ℂ := Fin.cases 0 u
  let V : Fin (c+1) → Fin (q+1) → ℂ := Fin.cases 0 v
  refine ⟨U,V,fun t k => w k t,?_⟩
  intro i j k
  have hU : (∑ t, U t i * (y t j * z t k)) = u k i * y k.succ j := by
    simp [z, U, mul_ite, Finset.sum_ite_eq']
  have hV : (∑ t, x t i * (V t j * z t k)) = x k.succ i * v k j := by
    simp [z, V, mul_ite, Finset.sum_ite_eq']
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hU, hV, hw k i j]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

end RemainingBoundary

namespace LastSliceBatch

/-- The stacked linear equations consist of all sampled-product conditions,
the two contractions at each marked point, and the unweighted sum of the tuple. -/
theorem stack_injective_iff {K A B S G : Type*} [Field K] [Fintype A] [Fintype B] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq G]
    (label : G → S) (x : S → A → K) (y : S → B → K)
    (M : Matrix ((G × (S ⊕ (A ⊕ B))) ⊕ (A × B)) (G × (A × B)) K)
    (entry : ∀ row col, M row col = row.elim
      (fun ge => if col.1=ge.1 then ge.2.elim
        (fun s => x s col.2.1*y s col.2.2)
        (Sum.elim (fun i => if col.2.1=i then y (label ge.1) col.2.2 else 0)
          (fun j => if col.2.2=j then x (label ge.1) col.2.1 else 0)) else 0)
      (fun ij => if col.2=ij then 1 else 0)) :
    Function.Injective M.mulVec ↔
      ∀ H : G → A × B → K, (∀ g s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H g ij=0) →
        (∀ g i, ∑ j, y (label g) j*H g (i,j)=0) →
        (∀ g j, ∑ i, x (label g) i*H g (i,j)=0) → (∑ g, H g)=0 → H=0 := by
  classical
  have outer (H : G → A × B → K) (g : G) (s : S) :
      M.mulVec (Function.uncurry H) (.inl (g,.inl s)) = ∑ ij, (x s ij.1*y s ij.2)*H g ij := by
    change (∑ z : G × (A × B), M (.inl (g,.inl s)) z*H z.1 z.2) = _
    rw [Fintype.sum_prod_type]
    simp [entry,ite_mul,Finset.sum_ite_eq']
  have row₁ (H : G → A × B → K) (g : G) (i : A) :
      M.mulVec (Function.uncurry H) (.inl (g,.inr (.inl i))) = ∑ j, y (label g) j*H g (i,j) := by
    change (∑ z : G × (A × B), M (.inl (g,.inr (.inl i))) z*H z.1 z.2) = _
    simp [Fintype.sum_prod_type,entry,ite_mul,Finset.sum_ite_eq']
  have col₁ (H : G → A × B → K) (g : G) (j : B) :
      M.mulVec (Function.uncurry H) (.inl (g,.inr (.inr j))) = ∑ i, x (label g) i*H g (i,j) := by
    change (∑ z : G × (A × B), M (.inl (g,.inr (.inr j))) z*H z.1 z.2) = _
    simp [Fintype.sum_prod_type,entry,ite_mul,Finset.sum_ite_eq']
  have total (H : G → A × B → K) (ij : A × B) :
      M.mulVec (Function.uncurry H) (.inr ij) = (∑ g, H g) ij := by
    change (∑ z : G × (A × B), M (.inr ij) z*H z.1 z.2) = _
    rw [Fintype.sum_prod_type]
    simp [entry,ite_mul,Finset.sum_apply,Finset.sum_ite_eq']
  constructor
  · intro inject H hp hx hy hz
    have ker : M.mulVec (Function.uncurry H)=0 := by
      funext z
      rcases z with ⟨g,s|i|j⟩|ij
      · exact (outer H g s).trans (hp g s)
      · exact (row₁ H g i).trans (hx g i)
      · exact (col₁ H g j).trans (hy g j)
      · exact (total H ij).trans (congrFun hz ij)
    have he := inject (ker.trans (Matrix.mulVec_zero M).symm)
    exact funext fun g => funext fun ij => congrFun he (g,ij)
  · intro hs
    change Function.Injective M.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro f hf
    let H : G → A × B → K := Function.curry f
    have eq : M.mulVec (Function.uncurry H) = 0 := hf
    have van := hs H (fun g s => (outer H g s).symm.trans (congrFun eq _))
      (fun g i => (row₁ H g i).symm.trans (congrFun eq _))
      (fun g j => (col₁ H g j).symm.trans (congrFun eq _))
      (funext fun ij => (total H ij).symm.trans (congrFun eq _))
    exact funext fun z => congrFun (congrFun van z.1) z.2

end LastSliceBatch


namespace LastSliceBatch

/-- Any two ordered partial markings of the same finite set extend to a
permutation of the whole point set. -/
theorem permutation_of_markings {G S : Type*} [Fintype G] [Fintype S]
    (first second : G ↪ S) : ∃ e : S ≃ S, ∀ g, e (first g)=second g := by
  classical
  let F := Set.range first
  let T := Set.range second
  let inner : F ≃ T := first.toEquivRange.symm.trans second.toEquivRange
  let outer : (Fᶜ : Set S) ≃ (Tᶜ : Set S) := Fintype.equivOfCardEq (by
    rw [Fintype.card_compl_set,Fintype.card_compl_set,Fintype.card_congr inner])
  let e := (Equiv.Set.sumCompl F).symm.trans ((Equiv.sumCongr inner outer).trans (Equiv.Set.sumCompl T))
  refine ⟨e,fun g => ?_⟩
  have mem : first g ∈ F := ⟨g,rfl⟩
  dsimp only [e,Equiv.trans_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_mem mem]
  change ((second.toEquivRange (first.toEquivRange.symm (first.toEquivRange g)) : T) : S) = second g
  rw [Equiv.symm_apply_apply]
  rfl

end LastSliceBatch


namespace LastSliceBatch

open MvPolynomial

/-- A left inverse at one point gives a polynomial sufficient for injectivity at other points. -/
private lemma injectivity_polynomial {I J V : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (p : V → ℂ) (hi : Function.Injective (M.map (eval p)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q≠0 ∧ ∀ u : V → ℂ, eval u Q≠0 → Function.Injective (M.map (eval u)).mulVec := by
  classical
  let A := M.map (eval p)
  obtain ⟨L,hL⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let B := LinearMap.toMatrix' L
  have left : B*A=1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' L)).comp A.mulVecLin=LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact hL
  let P := B.map (MvPolynomial.C : ℂ →+* MvPolynomial V ℂ)
  have spec (u : V → ℂ) : eval u (P*M).det = (B*M.map (eval u)).det := by
    have hP : P.map (eval u)=B := by ext; simp [P,Matrix.map_apply]
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,hP]
  have one : eval p (P*M).det=1 := (spec p).trans ((congrArg Matrix.det left).trans Matrix.det_one)
  refine ⟨(P*M).det,fun h => zero_ne_one (by simpa only [h,map_zero] using one),?_⟩
  intro u hu
  have nz : (B*M.map (eval u)).det≠0 := (spec u) ▸ hu
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nz))
  intro x y he
  apply hinj
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,he]

/-- A finite family of injectivity conditions on a common parameter space holds simultaneously
when each is realized separately. Both matrix index types may depend on the family member. -/
lemma common_injective {G V : Type*} [Fintype G] {U W : G → Type*}
    [∀ g,Fintype (U g)] [∀ g,Fintype (W g)]
    (M : ∀ g,Matrix (U g) (W g) (MvPolynomial V ℂ))
    (h : ∀ g, ∃ u : V → ℂ, Function.Injective ((M g).map (eval u)).mulVec) :
    ∃ u : V → ℂ, ∀ g,Function.Injective ((M g).map (eval u)).mulVec := by
  classical
  choose u hu using h
  choose Q hn hgood using fun g => injectivity_polynomial (M g) (u g) (hu g)
  have hprod : (∏ g,Q g)≠0 := Finset.prod_ne_zero_iff.mpr fun g _ => hn g
  obtain ⟨z,hz⟩ : ∃ z : V → ℂ,eval z (∏ g,Q g)≠0 := by
    by_contra! he
    exact hprod (MvPolynomial.funext fun z => by rw [he z,map_zero])
  have hval : (∏ g, eval z (Q g))≠0 := by simpa only [map_prod] using hz
  exact ⟨z,fun g => hgood g z (Finset.prod_ne_zero_iff.mp hval g (Finset.mem_univ g))⟩

end LastSliceBatch


namespace LastSliceBatch

open MvPolynomial

/-- One independent ordered marking gives common complex factors that work for
every ordered marking of the same size. All use the same sampled outer products. -/
theorem common_markings {A B P Q : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    (first : Q ↪ P) (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ e : Q ↪ P, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  let V := P × (A ⊕ B)
  let Row := (Q × (P ⊕ (A ⊕ B))) ⊕ (A × B)
  let Col := Q × (A × B)
  let M (e : Q ↪ P) : Matrix Row Col (MvPolynomial V ℂ) := fun row col => row.elim
    (fun te => if col.1=te.1 then te.2.elim
      (fun s => X (s,.inl col.2.1)*X (s,.inr col.2.2))
      (Sum.elim (fun i => if col.2.1=i then X (e te.1,.inr col.2.2) else 0)
        (fun j => if col.2.2=j then X (e te.1,.inl col.2.1) else 0)) else 0)
    (fun ij => if col.2=ij then 1 else 0)
  let D (x : P → A → ℂ) (y : P → B → ℂ) (e : Q ↪ P) : Prop := ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0
  have action (e : Q ↪ P) (p : V → ℂ) : Function.Injective ((M e).map (eval p)).mulVec ↔
      D (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j)) e := by
    apply stack_injective_iff e (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j))
    intro row col
    change eval p (M e row col) = _
    rcases row with ⟨t,s|i|j⟩|ij <;> rcases col with ⟨l,u,v⟩
    · by_cases ht : l=t <;> simp [M,ht]
    · by_cases ht : l=t <;> by_cases hi : u=i <;> simp [M,ht,hi]
    · by_cases ht : l=t <;> by_cases hj : v=j <;> simp [M,ht,hj]
    · by_cases he : (u,v)=ij <;> simp [M,he]
  obtain ⟨x₀,y₀,h₀⟩ := one
  have each (e : Q ↪ P) : ∃ p : V → ℂ, Function.Injective ((M e).map (eval p)).mulVec := by
    obtain ⟨σ,hσ⟩ := permutation_of_markings e first
    let p (z : V) := z.2.elim (x₀ (σ z.1)) (y₀ (σ z.1))
    refine ⟨p,(action e p).mpr ?_⟩
    intro H outer row col
    apply h₀ H
    · intro t s
      obtain ⟨s,rfl⟩ := σ.surjective s
      exact outer t s
    · simpa only [p,Sum.elim_inr,hσ] using row
    · simpa only [p,Sum.elim_inl,hσ] using col
  obtain ⟨p,hp⟩ := common_injective (U:=fun _ : Q ↪ P => Row) (W:=fun _ => Col) M each
  exact ⟨fun s i => p (s,.inl i),fun s j => p (s,.inr j),fun e => (action e p).mp (hp e)⟩

/-- Restrict a direct family along an embedding by extending the smaller
tuple by zero on the complement. -/
private lemma restrict_marking {A B P Q T : Type*} [Fintype A] [Fintype B] [Fintype Q] [Fintype T]
    (x : P → A → ℂ) (y : P → B → ℂ) (e : Q ↪ P) (f : T ↪ Q)
    (direct : ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) : ∀ H : T → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e (f t)) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e (f t)) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  let C := (Set.range f)ᶜ
  let q : T ⊕ C ≃ Q := (Equiv.sumCongr f.toEquivRange (Equiv.refl C)).trans (Equiv.Set.sumCompl _)
  have ql (t : T) : q (.inl t)=f t := rfl
  intro H outer row col total
  let F (s : Q) : A × B → ℂ := (q.symm s).elim H (fun _ => 0)
  have fl (t : T) : F (q (.inl t))=H t := by simp only [F,Equiv.symm_apply_apply,Sum.elim_inl]
  have fr (t : C) : F (q (.inr t))=0 := by simp only [F,Equiv.symm_apply_apply,Sum.elim_inr]
  have outer' (t : Q) (s : P) : ∑ ij : A×B, (x s ij.1*y s ij.2)*F t ij=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl]
      exact outer t s
    · simp [fr]
  have row' (t : Q) (i : A) : (∑ j, y (e t) j*F t (i,j))=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl,ql]
      exact row t i
    · simp [fr]
  have col' (t : Q) (j : B) : (∑ i, x (e t) i*F t (i,j))=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl,ql]
      exact col t j
    · simp [fr]
  have all_sum : ∑ t,F t=0 := by
    rw [←q.sum_comp F,Fintype.sum_sum_type]
    simpa only [fl,fr,Finset.sum_const_zero,add_zero] using total
  have zero := direct F outer' row' col' all_sum
  funext t ij
  exact congrFun ((fl t).symm.trans (congrFun zero (q (.inl t)))) ij

/-- Once every maximal marking works at the same factors, so does every
smaller injection. A permutation extends each such injection to a maximal one. -/
private lemma smaller_marking {A B P Q T : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    [Fintype T] (x : P → A → ℂ) (y : P → B → ℂ) (first : Q ↪ P) (label : T ↪ P)
    (size : Fintype.card T ≤ Fintype.card Q) (good : ∀ e : Q ↪ P, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) : ∀ H : T → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (label t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (label t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le size
  obtain ⟨σ,hσ⟩ := permutation_of_markings (f.trans first) label
  let e := first.trans σ.toEmbedding
  have agree (t : T) : e (f t)=label t := hσ t
  intro H outer row col total
  apply restrict_marking x y e f (good e) H outer
  · simpa only [agree] using row
  · simpa only [agree] using col
  · exact total

/-- Ragged color classes may have different cardinalities, including zero.
The same factors give independent normal spaces in every color class. -/
theorem common_small_fibers {A B P Q D : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    [DecidableEq D] (first : Q ↪ P) (label : P → D)
    (cap : ∀ g, Fintype.card {t : P // label t=g} ≤ Fintype.card Q) (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ g : D, ∀ H : {t : P // label t=g} → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (t.val) j*H t (i,j))=0) → (∀ t j, (∑ i, x (t.val) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  obtain ⟨x,y,good⟩ := common_markings first one
  exact ⟨x,y,fun g => smaller_marking x y first (Function.Embedding.subtype (fun t => label t=g)) (cap g) good⟩

end LastSliceBatch

namespace LastSliceBatch

/-- Annihilators of the image of a matrix are its row relations. -/
private lemma ragged_surj_of_no_relation {K R C : Type*} [Field K] [Fintype R] [Fintype C]
    (M : Matrix R C K) (h : ∀ u : R → K, M.transpose.mulVec u=0 → u=0) :
    Function.Surjective M.mulVec := by
  classical
  have hk : LinearMap.ker M.transpose.mulVecLin = ⊥ := by
    apply bot_unique
    intro u hu
    exact (Submodule.mem_bot K).mpr (h u hu)
  have he := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk)
  change M.transpose.rank = Module.finrank K (R → K) at he
  rw [Matrix.rank_transpose] at he
  change Function.Surjective M.mulVecLin
  apply LinearMap.range_eq_top.mp
  exact Submodule.eq_top_of_finrank_eq he

private lemma indicator_sum {K P G : Type*} [Field K] [Fintype P] [DecidableEq G] [DecidableEq P]
    (label : P → G) (g : G) (p : P) :
    (∑ t : {t : P // label t=g}, if t.val=p then (1 : K) else 0) =
      if label p=g then 1 else 0 := by
  by_cases h : label p=g
  · let v : {t : P // label t=g} := ⟨p,h⟩
    have e (t : {t : P // label t=g}) : t.val=p ↔ t=v :=
      ⟨fun ht => Subtype.ext ht,fun ht => congrArg Subtype.val ht⟩
    simp [h,e]
  · have e (t : {t : P // label t=g}) : t.val≠p := fun ht => h (ht ▸ t.property)
    simp [h,e]

/-- Independent normal tuples on the fibers give a tangent witness. One point
in each fiber is the negative sum of that fiber's other coordinate vectors. -/
theorem spans_of_ragged_independence {K P G : Type*} [Field K] [Fintype P] [Fintype G]
    [DecidableEq G] {a b : ℕ} (label : P → G) (onto : Function.Surjective label)
    (x : P → Fin a → K) (y : P → Fin b → K)
    (independent : ∀ g : G, ∀ H : {t : P // label t=g} → (Fin a × Fin b) → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij = 0) →
      (∀ t i, ∑ j,y t.val j*H t (i,j)=0) →
      (∀ t j, ∑ i,x t.val i*H t (i,j)=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ X : Fin (Fintype.card P) → Fin a → K, ∃ Y : Fin (Fintype.card P) → Fin b → K,
    ∃ Z : Fin (Fintype.card P) → Fin (Fintype.card P-Fintype.card G) → K,
      ∀ T : Fin a → Fin b → Fin (Fintype.card P-Fintype.card G) → K,
      ∃ u : Fin (Fintype.card P) → Fin a → K, ∃ v : Fin (Fintype.card P) → Fin b → K,
      ∃ w : Fin (Fintype.card P) → Fin (Fintype.card P-Fintype.card G) → K, ∀ i j k, T i j k =
        ∑ t, (u t i*(Y t j*Z t k) + X t i*(v t j*Z t k) + X t i*(Y t j*w t k)) := by
  classical
  choose pivot right using onto
  let Free := {p : P // p ≠ pivot (label p)}
  let split : G ⊕ Free ≃ P :=
    { toFun := Sum.elim pivot Subtype.val
      invFun := fun p => if h : p=pivot (label p) then .inl (label p) else .inr ⟨p,h⟩
      left_inv := by
        rintro (g|⟨p,h⟩)
        · simp [right]
        · simp [h]
      right_inv := by
        intro p
        by_cases hp : p=pivot (label p)
        · simpa only [dif_pos hp,Sum.elim_inl] using hp.symm
        · simp only [dif_neg hp,Sum.elim_inr] }
  have count : Fintype.card Free=Fintype.card P-Fintype.card G := by
    have size := Fintype.card_congr split
    rw [Fintype.card_sum] at size
    omega
  let E : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let F : Free ≃ Fin (Fintype.card P-Fintype.card G) := (Fintype.equivFin Free).trans (finCongr count)
  let X (s : Fin (Fintype.card P)) := x (E.symm s)
  let Y (s : Fin (Fintype.card P)) := y (E.symm s)
  let Z (s : Fin (Fintype.card P)) (k : Fin (Fintype.card P-Fintype.card G)) : K :=
    (if E.symm s=(F.symm k).val then 1 else 0) -
      (if E.symm s=pivot (label (F.symm k).val) then 1 else 0)
  have away (p : Free) (g : G) : p.val≠pivot g := by
    intro eq
    apply p.property
    have h : label p.val=g := eq ▸ right g
    rwa [h]
  have basisValue (p : Free) (k : Fin (Fintype.card P-Fintype.card G)) :
      Z (E p.val) k = if F p=k then 1 else 0 := by
    obtain ⟨q,rfl⟩ := F.surjective k
    have eq : p.val=q.val ↔ p=q := ⟨Subtype.ext,congrArg Subtype.val⟩
    simp only [Z,Equiv.symm_apply_apply,if_neg (away p _),sub_zero,Equiv.apply_eq_iff_eq,eq]
  have batchSum (g : G) (k : Fin (Fintype.card P-Fintype.card G)) :
      (∑ t : {p : P // label p=g}, Z (E t.val) k)=0 := by
    simp only [Z,Equiv.symm_apply_apply,Finset.sum_sub_distrib,indicator_sum,right,sub_self]
  let V := Fin (Fintype.card P) × (Fin a ⊕ (Fin b ⊕ Fin (Fintype.card P-Fintype.card G)))
  let M : Matrix ((Fin a × Fin b) × Fin (Fintype.card P-Fintype.card G)) V K := fun row col =>
    col.2.elim (fun i' => if i'=row.1.1 then Y col.1 row.1.2*Z col.1 row.2 else 0)
      (Sum.elim (fun j' => if j'=row.1.2 then X col.1 row.1.1*Z col.1 row.2 else 0)
        (fun k' => if k'=row.2 then X col.1 row.1.1*Y col.1 row.1.2 else 0))
  have full : Function.Surjective M.mulVec := by
    apply ragged_surj_of_no_relation
    intro T ht
    let D (s : P) (ij : Fin a × Fin b) := ∑ k,Z (E s) k*T (ij,k)
    obtain ⟨hout,hrow,hcol⟩ := (LastSliceDual.transpose_kernel_iff X Y Z M (fun _ _ _ _ _ => rfl) T).mp ht
    have outer (k : Fin (Fintype.card P-Fintype.card G)) (s : P) :
        (∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k))=0 := by
      simpa only [X,Y,Equiv.symm_apply_apply] using hout k (E s)
    have zero (g : G) : (fun t : {p : P // label p=g} => D t.val)=0 := by
      apply independent g
      · intro t s
        calc
          _ = ∑ k, Z (E t.val) k * (∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k)) := by
            simp only [D,Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro ij _
            ring
          _ = 0 := by simp [outer]
      · intro t i
        simpa only [D,Y,Equiv.symm_apply_apply] using hrow (E t.val) i
      · intro t j
        simpa only [D,X,Equiv.symm_apply_apply] using hcol (E t.val) j
      · funext ij
        simp only [Finset.sum_apply,D,Pi.zero_apply]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul,batchSum,zero_mul,Finset.sum_const_zero]
    funext ⟨ij,k⟩
    obtain ⟨p,rfl⟩ := F.surjective k
    have hh := congrFun (congrFun (zero (label p.val)) ⟨p.val,rfl⟩) ij
    simpa [D,basisValue,ite_mul,Finset.sum_ite_eq] using hh
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨z,hz⟩ := full fun q => T q.1.1 q.1.2 q.2
  refine ⟨fun t i => z (t,.inl i),fun t j => z (t,.inr (.inl j)),fun t k => z (t,.inr (.inr k)),?_⟩
  intro i j k
  refine (congrFun hz ((i,j),k)).symm.trans ?_
  change (∑ v : V, M ((i,j),k) v*z v)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [M,ite_mul,Finset.sum_ite_eq']
  ring

/-- Reduction modulo s distributes r points into s nonempty fibers of size
at most m whenever the available capacity s*m is at least r. -/
theorem balanced_partition {r s m : ℕ} (hs : s ≤ r) (hcap : r ≤ s*m) :
    ∃ label : Fin r → Fin s, Function.Surjective label ∧
      ∀ g, Fintype.card {p : Fin r // label p=g} ≤ m := by
  by_cases h0 : s=0
  · subst s
    obtain rfl : r=0 := by simpa using hcap
    exact ⟨id,Function.surjective_id,fun g => g.elim0⟩
  · have spos : 0 < s := Nat.pos_of_ne_zero h0
    let label (p : Fin r) : Fin s := ⟨p.val%s,Nat.mod_lt _ spos⟩
    refine ⟨label,?_,?_⟩
    · intro g
      refine ⟨⟨g.val,g.isLt.trans_le hs⟩,Fin.ext (Nat.mod_eq_of_lt g.isLt)⟩
    · intro g
      let encode (v : {p : Fin r // label p=g}) : Fin m :=
        ⟨v.val.val/s,(Nat.div_lt_iff_lt_mul spos).mpr (by simpa only [Nat.mul_comm m s] using v.val.isLt.trans_le hcap)⟩
      have inj : Function.Injective encode := by
        intro u v he
        have hq : u.val.val/s=v.val.val/s := congrArg Fin.val he
        have hr : u.val.val%s=v.val.val%s := (congrArg Fin.val u.property).trans (congrArg Fin.val v.property).symm
        apply Subtype.ext
        apply Fin.ext
        calc
          _ = s*(u.val.val/s)+u.val.val%s := (Nat.div_add_mod u.val.val s).symm
          _ = s*(v.val.val/s)+v.val.val%s := by rw [hq,hr]
          _ = _ := Nat.div_add_mod v.val.val s
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective encode inj

end LastSliceBatch

namespace LastSlicePositive

/-- Transport a marked collection of independent normal spaces through
bijections on the total points and both matrix axes. -/
private lemma move_mark {A B P Q A' B' P' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype Q]
    (ea : A ≃ A') (eb : B ≃ B') (ep : P ≃ P') (first : Q ↪ P)
    (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A × B → ℂ,
      (∀ t s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0) :
    ∃ X : P' → A' → ℂ, ∃ Y : P' → B' → ℂ, ∀ H : Q → A' × B' → ℂ,
      (∀ t s, ∑ ij : A' × B', (X s ij.1*Y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, Y (ep (first t)) j*H t (i,j)=0) →
      (∀ t j, ∑ i, X (ep (first t)) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0 := by
  classical
  obtain ⟨x,y,ind⟩ := one
  let X (s : P') (i : A') := x (ep.symm s) (ea.symm i)
  let Y (s : P') (j : B') := y (ep.symm s) (eb.symm j)
  refine ⟨X,Y,?_⟩
  intro H outer row col total
  let pull (t : Q) (ij : A × B) := H t (ea ij.1,eb ij.2)
  have out (t : Q) (s : P) : ∑ ij : A × B, (x s ij.1*y s ij.2)*pull t ij=0 := by
    have h := outer t (ep s)
    rw [← (ea.prodCongr eb).sum_comp] at h
    simpa only [pull,X,Y,Equiv.prodCongr_apply,Prod.map,Equiv.symm_apply_apply] using h
  have rows (t : Q) (i : A) : ∑ j, y (first t) j*pull t (i,j)=0 := by
    have h := row t (ea i)
    rw [← eb.sum_comp] at h
    simpa only [pull,Y,Equiv.symm_apply_apply] using h
  have cols (t : Q) (j : B) : ∑ i, x (first t) i*pull t (i,j)=0 := by
    have h := col t (eb j)
    rw [← ea.sum_comp] at h
    simpa only [pull,X,Equiv.symm_apply_apply] using h
  have trace : ∑ t, pull t=0 := by
    funext ij
    simpa only [Finset.sum_apply,pull,Pi.zero_apply] using congrFun total (ea ij.1,eb ij.2)
  have zero := ind pull out rows cols trace
  funext t ij
  simpa only [pull,Equiv.apply_symm_apply,Prod.mk.eta,Pi.zero_apply] using
    congrFun (congrFun zero t) (ea.symm ij.1,eb.symm ij.2)

end LastSlicePositive

namespace LastSlicePositive

/-- A marked independent family of size m permits w points to span whenever
the w−c batches can be chosen with at most m points apiece. -/
private lemma from_capacity {a b w c m : ℕ} {Q : Type*} [Fintype Q]
    (hq : Fintype.card Q=m) (first : Q ↪ Fin w) (hc : c≤w) (fit : w≤(w-c)*m)
    (one : ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∀ H : Q → Fin a × Fin b → ℂ,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0) :
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ v' : Fin w → Fin c → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*v' t k)) := by
  classical
  obtain ⟨label,onto,bound⟩ := LastSliceBatch.balanced_partition (Nat.sub_le w c) fit
  have cap (g : Fin (w-c)) : Fintype.card {t : Fin w // label t=g} ≤ Fintype.card Q := hq ▸ bound g
  obtain ⟨x,y,direct⟩ := LastSliceBatch.common_small_fibers first label cap one
  have result := LastSliceBatch.spans_of_ragged_independence label onto x y direct
  rw [Fintype.card_fin w,Fintype.card_fin (w-c),show w-(w-c)=c by omega] at result
  exact result

end LastSlicePositive

namespace LastSliceTwo

/-- Two marked labels per group have the same moment-curve vector in the last column.
Their coordinates in the old columns distinguish the two types. For both types the
third entry in the last column determines the full normal. -/
lemma exists_two_formulas (A B : ℕ) :
    ∃ x : (Fin B × (Fin 2 ⊕ Fin A)) → (Fin 3 ⊕ Fin A) → ℂ,
    ∃ y : (Fin B × (Fin 2 ⊕ Fin A)) → Option (Fin B) → ℂ,
    ∀ (i : Fin B) (v : Fin 2) (H : (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ),
      (∀ t, ∑ ij, (x t ij.1*y t ij.2)*H ij=0) →
      (∀ u, ∑ k, y (i,.inl v) k*H (u,k)=0) →
      (∀ k, ∑ u, x (i,.inl v) u*H (u,k)=0) →
      let s := H (.inl 2,none)
      (∀ u : Fin 3 ⊕ Fin A, H (u,none) = s * u.elim ![(i.val:ℂ)^2,-2*(i.val:ℂ),1]
        (fun l => (i.val:ℂ)^(l.val+3))) ∧
      (∀ j, H (.inl 2,some j) = if v=0 then (if i=j then -s else s) else 0) ∧ (s=0 → H=0) := by
  let lam : Fin 2 ⊕ Fin A → ℂ := Sum.elim (fun v => if v=0 then 1 else 0) (fun _ => 2)
  let x (p : Fin B × (Fin 2 ⊕ Fin A)) : (Fin 3 ⊕ Fin A) → ℂ :=
    match p.2 with
    | .inl v => Sum.elim (if v=0 then ![1,(p.1.val:ℂ),(p.1.val:ℂ)^2] else ![0,1,2*(p.1.val:ℂ)]) 0
    | .inr l => Sum.elim ![0,0,-(p.1.val:ℂ)^(l.val+3)] (fun u => if u=l then 1 else 0)
  let y (p : Fin B × (Fin 2 ⊕ Fin A)) : Option (Fin B) → ℂ := fun
    | none => lam p.2
    | some j => if j=p.1 then 1 else 0
  have second_action (p : Fin B × (Fin 2 ⊕ Fin A)) (w : Option (Fin B) → ℂ) :
      (∑ k, y p k*w k) = lam p.2*w none + w (some p.1) := by
    rw [Fintype.sum_option]
    simp [y,ite_mul,Finset.sum_ite_eq']
  have product_action (p : Fin B × (Fin 2 ⊕ Fin A)) (H : (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ) :
      (∑ ij, (x p ij.1*y p ij.2)*H ij) = ∑ u, x p u*(lam p.2*H (u,none)+H (u,some p.1)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    rw [← second_action p (fun k => H (u,k)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have first_action (j : Fin B) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inl 0) u*w u) =
      w (.inl 0)+(j.val:ℂ)*w (.inl 1)+(j.val:ℂ)^2*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two]
  have slope_action (j : Fin B) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inl 1) u*w u) =
      w (.inl 1)+2*(j.val:ℂ)*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two]
  have extra_action (j : Fin B) (l : Fin A) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inr l) u*w u) =
      w (.inr l)-(j.val:ℂ)^(l.val+3)*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two,ite_mul,Finset.sum_ite_eq']
    ring
  refine ⟨x,y,?_⟩
  intro i v H prod row col s
  let I : ℂ := i.val
  have selected (u : Fin 3 ⊕ Fin A) : (if v=0 then (1:ℂ) else 0)*H (u,none)+H (u,some i)=0 :=
    (second_action (i,.inl v) (fun k => H (u,k))).symm.trans (row u)
  have Xarm (hv : v=0) (k : Option (Fin B)) : H (.inl 0,k)+I*H (.inl 1,k)+I^2*H (.inl 2,k)=0 := by
    subst v
    exact (first_action i (fun u => H (u,k))).symm.trans (col k)
  have Darm (hv : v≠0) (k : Option (Fin B)) : H (.inl 1,k)+2*I*H (.inl 2,k)=0 := by
    have hv' : v=1 := by fin_cases v <;> simp_all
    subst v
    exact (slope_action i (fun u => H (u,k))).symm.trans (col k)
  have anchor (j : Fin B) : (H (.inl 0,none)+H (.inl 0,some j)) +
      (j.val:ℂ)*(H (.inl 1,none)+H (.inl 1,some j)) +
      (j.val:ℂ)^2*(H (.inl 2,none)+H (.inl 2,some j))=0 := by
    apply (first_action j (fun u => H (u,none)+H (u,some j))).symm.trans
    simpa only [lam,Sum.elim_inl,if_true,one_mul] using (product_action (j,.inl 0) H).symm.trans (prod (j,.inl 0))
  have slope (j : Fin B) : H (.inl 1,some j)+2*(j.val:ℂ)*H (.inl 2,some j)=0 := by
    apply (slope_action j (fun u => H (u,some j))).symm.trans
    simpa [lam] using (product_action (j,.inl 1) H).symm.trans (prod (j,.inl 1))
  have extra (j : Fin B) (l : Fin A) : (2*H (.inr l,none)+H (.inr l,some j)) -
      (j.val:ℂ)^(l.val+3)*(2*H (.inl 2,none)+H (.inl 2,some j))=0 := by
    apply (extra_action j l (fun u => 2*H (u,none)+H (u,some j))).symm.trans
    simpa only [lam,Sum.elim_inr] using (product_action (j,.inr l) H).symm.trans (prod (j,.inr l))
  have lastSlope : H (.inl 1,none)+2*I*s=0 := by
    by_cases hv : v=0
    · have u := selected (.inl 1)
      have w := selected (.inl 2)
      simp only [if_pos hv,one_mul] at u w
      dsimp only [I,s]
      linear_combination u + 2*(i.val:ℂ)*w - slope i
    · exact Darm hv none
  have lastPoint : H (.inl 0,none)+I*H (.inl 1,none)+I^2*s=0 := by
    by_cases hv : v=0
    · exact Xarm hv none
    · have zero (u : Fin 3 ⊕ Fin A) : H (u,some i)=0 := by simpa only [if_neg hv,zero_mul,zero_add] using selected u
      simpa only [zero,add_zero] using anchor i
  have last₁ : H (.inl 1,none) = -2*I*s := by linear_combination lastSlope
  have last₀ : H (.inl 0,none) = I^2*s := by linear_combination lastPoint - I*lastSlope
  have lastExtra (l : Fin A) : H (.inr l,none) = I^(l.val+3)*s := by
    have a := selected (.inr l)
    have b := selected (.inl 2)
    dsimp only [I,s]
    by_cases hv : v=0
    · simp only [if_pos hv,one_mul] at a b
      linear_combination extra i l - a + (i.val:ℂ)^(l.val+3)*b
    · simp only [if_neg hv,zero_mul,zero_add] at a b
      linear_combination (extra i l - a + (i.val:ℂ)^(l.val+3)*b)/2
  have atLast (u : Fin 3 ⊕ Fin A) : H (u,none) = s*u.elim ![(i.val:ℂ)^2,-2*(i.val:ℂ),1]
      (fun l => (i.val:ℂ)^(l.val+3)) := by
    rcases u with k|l
    · fin_cases k
      · change H (.inl (0:Fin 3),none)=s*I^2
        rw [last₀,mul_comm]
      · change H (.inl (1:Fin 3),none)=s*(-2*I)
        rw [last₁,mul_comm]
      · change s=s*1
        rw [mul_one]
    · change H (.inr l,none)=s*I^(l.val+3)
      rw [lastExtra,mul_comm]
  have old₁ (j : Fin B) : H (.inl 1,some j) = -2*(j.val:ℂ)*H (.inl 2,some j) := by
    linear_combination slope j
  have old₀ (j : Fin B) : H (.inl 0,some j) = (j.val:ℂ)^2*H (.inl 2,some j) -
      (H (.inl 0,none)+(j.val:ℂ)*H (.inl 1,none)+(j.val:ℂ)^2*s) := by
    dsimp only [s]
    linear_combination anchor j - (j.val:ℂ)*slope j
  have signs (j : Fin B) : H (.inl 2,some j) = if v=0 then (if i=j then -s else s) else 0 := by
    have diff (h : i≠j) : (j.val:ℂ) ≠ I := by
      intro eq
      apply h
      apply Fin.ext
      dsimp only [I] at eq
      exact_mod_cast eq.symm
    by_cases hv : v=0
    · rw [if_pos hv]
      by_cases h : i=j
      · subst j
        rw [if_pos rfl]
        have u := selected (.inl 2)
        simp only [if_pos hv,one_mul] at u
        dsimp only [s]
        linear_combination u
      · rw [if_neg h]
        have fact : ((j.val:ℂ)-I)^2*(s-H (.inl 2,some j))=0 := by
          have hy := Xarm hv (some j)
          rw [old₀,old₁,last₀,last₁] at hy
          linear_combination -hy
        exact (sub_eq_zero.mp ((mul_eq_zero.mp fact).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr (diff h))))).symm
    · rw [if_neg hv]
      by_cases h : i=j
      · subst j
        simpa only [if_neg hv,zero_mul,zero_add] using selected (.inl 2)
      · have fact : (2*(I-(j.val:ℂ)))*H (.inl 2,some j)=0 := by
          linear_combination Darm hv (some j) - slope j
        exact (mul_eq_zero.mp fact).resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm (diff h))))
  refine ⟨atLast,signs,?_⟩
  intro hs
  have lastZ (u : Fin 3 ⊕ Fin A) : H (u,none)=0 := by simpa only [hs,zero_mul] using atLast u
  have oldZ (j : Fin B) (u : Fin 3 ⊕ Fin A) : H (u,some j)=0 := by
    have z₂ : H (.inl 2,some j)=0 := by simpa only [hs,neg_zero,ite_self] using signs j
    rcases u with k|l
    · fin_cases k
      · change H (.inl (0 : Fin 3),some j)=0
        simpa only [z₂,lastZ,hs,mul_zero,add_zero,sub_zero] using old₀ j
      · change H (.inl (1 : Fin 3),some j)=0
        simpa only [z₂,mul_zero] using old₁ j
      · exact z₂
    · simpa only [lastZ,z₂,mul_zero,zero_add,add_zero,sub_zero] using extra j l
  funext ⟨u,k⟩
  cases k with
  | none => exact lastZ u
  | some j => exact oldZ j u

end LastSliceTwo

namespace LastSliceTwo

/-- Each signed row sum is the same total minus twice the coefficient at that row. -/
theorem signed_coefficients {B : ℕ} (hB : B ≠ 2) (s : Fin B → ℂ)
    (h : ∀ i, (∑ j, if j=i then -s j else s j)=0) : s=0 := by
  classical
  let T := ∑ j,s j
  have he (i : Fin B) : T = 2*s i := by
    have hrow : (∑ j, if j=i then -s j else s j)=T-2*s i := by
      calc
        _ = ∑ j, (s j-(if j=i then 2*s j else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j=i <;> simp [hji]
          ring
        _ = T-2*s i := by rw [Finset.sum_sub_distrib]; simp [T,Finset.sum_ite_eq']
    exact sub_eq_zero.mp (hrow.symm.trans (h i))
  have hall : (B : ℂ)*T=2*T := by
    calc
      _ = ∑ _ : Fin B,T := by simp
      _ = ∑ j,2*s j := Finset.sum_congr rfl fun j _ => he j
      _ = _ := (Finset.mul_sum ..).symm
  have hne : (B : ℂ)-2≠0 := sub_ne_zero.mpr (by exact_mod_cast hB)
  have hz : T=0 := (mul_eq_zero.mp (show ((B : ℂ)-2)*T=0 by linear_combination hall)).resolve_left hne
  funext i
  have hi := he i
  rw [hz] at hi
  change s i=0
  linear_combination -hi/2

/-- The initial three coordinates encode the quadratic, linear and constant moments;
the remaining coordinates supply the powers of degree three and above. -/
theorem moment_coefficients {A m : ℕ} (hm : m≤A+3) (t : Fin m → ℂ) (hit : Function.Injective t)
    (q : Fin m → ℂ) (h : ∀ u : Fin 3 ⊕ Fin A, (∑ j, q j*u.elim ![(t j)^2,-2*(t j),1]
      (fun l => (t j)^(l.val+3)))=0) : q=0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hit
  intro k
  by_cases h₀ : k.val=0
  · simpa [h₀,Matrix.cons_val_two] using h (.inl 2)
  by_cases h₁ : k.val=1
  · simp only [h₁,pow_one]
    have he : (∑ j,q j*t j)*(-2)=0 := by
      calc
        _ = ∑ j,q j*(-2*(t j)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by simpa using h (.inl 1)
    exact (mul_eq_zero.mp he).resolve_right (by norm_num)
  by_cases h₂ : k.val=2
  · simpa only [h₂,Sum.elim_inl,Matrix.cons_val_zero] using h (.inl 0)
  let l : Fin A := ⟨k.val-3,by omega⟩
  have hl : l.val+3=k.val := by dsimp only [l]; omega
  simpa only [Sum.elim_inr,hl] using h (.inr l)

theorem tagged_coefficients {A B : ℕ} (hB : B ≠ 2) (s : Fin B → ℂ) (q : Fin (min (A+3) B) → ℂ) :
    let h (j : Fin B) (u : Fin 3 ⊕ Fin A) : ℂ := u.elim ![(j.val : ℂ)^2,-2*(j.val : ℂ),1] (fun l => (j.val : ℂ)^(l.val+3))
    (∀ i, (∑ j, if j=i then -s j else s j)=0) →
    (∀ u, (∑ j, s j*h j u) + (∑ k, q k*h (k.castLE (Nat.min_le_right _ _)) u)=0) → s=0 ∧ q=0 := by
  intro h hs hq
  have hzero := signed_coefficients hB s hs
  refine ⟨hzero,?_⟩
  exact moment_coefficients (A:=A) (Nat.min_le_left (A+3) B) (fun j => (j.val : ℂ))
    (fun _ _ e => Fin.ext (Nat.cast_injective e)) q (fun u => by
      simpa only [h,hzero,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add,Fin.val_castLE] using hq u)

end LastSliceTwo

namespace LastSliceTwo

/-- Mark all `B` first-tag samples and the initial `min (A+3) B` second-tag samples.
Their normal spaces form an internal direct sum. -/
lemma exists_large_batch (A B : ℕ) (hB : 3 ≤ B) :
    ∃ label : (Fin B ⊕ Fin (min (A+3) B)) ↪ (Fin B × (Fin 2 ⊕ Fin A)),
    ∃ x : (Fin B × (Fin 2 ⊕ Fin A)) → (Fin 3 ⊕ Fin A) → ℂ,
    ∃ y : (Fin B × (Fin 2 ⊕ Fin A)) → Option (Fin B) → ℂ,
    ∀ H : (Fin B ⊕ Fin (min (A+3) B)) → (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ,
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (label t) j*H t (i,j))=0) →
      (∀ t j, (∑ i, x (label t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0 := by
  classical
  let k := min (A+3) B
  let inc (t : Fin k) := t.castLE (Nat.min_le_right (A+3) B)
  let label : (Fin B ⊕ Fin k) ↪ (Fin B × (Fin 2 ⊕ Fin A)) := {
    toFun := Sum.elim (fun i => (i,.inl 0)) (fun t => (inc t,.inl 1))
    inj' := by
      rintro (i|i) (j|j) he
      · exact congrArg Sum.inl (congrArg Prod.fst he)
      · have ht : (0 : Fin 2)=1 := Sum.inl.inj (congrArg Prod.snd he)
        exact (zero_ne_one ht).elim
      · have ht : (1 : Fin 2)=0 := Sum.inl.inj (congrArg Prod.snd he)
        exact (one_ne_zero ht).elim
      · have hv : inc i=inc j := congrArg Prod.fst he
        exact congrArg Sum.inr (Fin.ext (congrArg (fun v : Fin B => v.val) hv)) }
  obtain ⟨x,y,formula⟩ := exists_two_formulas A B
  refine ⟨label,x,y,?_⟩
  intro H outer rows cols total
  let s (i : Fin B) := H (.inl i) (.inl 2,none)
  let q (i : Fin k) := H (.inr i) (.inl 2,none)
  let v (i : Fin B) (u : Fin 3 ⊕ Fin A) := u.elim ![(i.val : ℂ)^2,-2*(i.val : ℂ),1] (fun l => (i.val : ℂ)^(l.val+3))
  have first (i : Fin B) := formula i 0 (H (.inl i)) (outer (.inl i)) (rows (.inl i)) (cols (.inl i))
  have extra (i : Fin k) := formula (inc i) 1 (H (.inr i)) (outer (.inr i)) (rows (.inr i)) (cols (.inr i))
  have f₁ (i : Fin B) (u : Fin 3 ⊕ Fin A) : H (.inl i) (u,none) = s i*v i u := (first i).1 u
  have f₂ (i j : Fin B) : H (.inl i) (.inl 2,some j) = if i=j then -s i else s i := (first i).2.1 j
  have e₁ (i : Fin k) (u : Fin 3 ⊕ Fin A) : H (.inr i) (u,none) = q i * v (inc i) u := (extra i).1 u
  have e₂ (i : Fin k) (j : Fin B) : H (.inr i) (.inl 2,some j) = 0 := (extra i).2.1 j
  have signed (j : Fin B) : (∑ i, if i=j then -s i else s i)=0 := by
    have he := congrFun total (.inl 2,some j)
    simpa only [Fintype.sum_sum_type,Pi.add_apply,Finset.sum_apply,f₂,e₂,Finset.sum_const_zero,add_zero,Pi.zero_apply] using he
  have last (u : Fin 3 ⊕ Fin A) : (∑ i, s i*v i u) + (∑ j, q j*v (inc j) u)=0 := by
    have he := congrFun total (u,none)
    simpa only [Fintype.sum_sum_type,Pi.add_apply,Finset.sum_apply,f₁,e₁,Pi.zero_apply] using he
  obtain ⟨hs,hq⟩ := tagged_coefficients (A:=A) (by omega : B≠2) s q signed last
  funext t
  cases t with
  | inl i => exact (first i).2.2 (congrFun hs i)
  | inr i => exact (extra i).2.2 (congrFun hq i)

end LastSliceTwo

namespace LastSlicePositive

/-- For every ordered pair of long sides in this range, the unrestricted
tangent spaces span at w=(a−1)(b−1) points throughout the batch-capacity range. -/
theorem second_full (a b c : ℕ) (ha : 3≤a) (hb : 4≤b) (_hab : a≤b)
    (hc : c≤(a-1)*(b-1))
    (fit : (a-1)*(b-1) ≤ ((a-1)*(b-1)-c)*((b-1)+min a (b-1))) :
    let w := (a-1)*(b-1)
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ v' : Fin w → Fin c → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*v' t k)) := by
  classical
  obtain ⟨A,rfl⟩ : ∃ A, a=A+3 := ⟨a-3,by omega⟩
  obtain ⟨B,rfl⟩ : ∃ B, b=B+1 := ⟨b-1,by omega⟩
  let P := Fin B × (Fin 2 ⊕ Fin A)
  let Q := Fin B ⊕ Fin (min (A+3) B)
  let w := (A+2)*B
  have size : Fintype.card P=w := by simp [P,w,Fintype.card_prod,Nat.mul_comm,Nat.add_comm]
  let ep : P ≃ Fin w := (Fintype.equivFin P).trans (finCongr size)
  let ea : (Fin 3 ⊕ Fin A) ≃ Fin (A+3) := finSumFinEquiv.trans (finCongr (Nat.add_comm 3 A))
  let eb : Option (Fin B) ≃ Fin (B+1) := (finSuccEquiv B).symm
  obtain ⟨mark,x,y,direct⟩ := LastSliceTwo.exists_large_batch A B (by omega)
  let first : Q ↪ Fin w := mark.trans ep.toEmbedding
  have count : Fintype.card Q = B+min (A+3) B := by simp [Q]
  exact from_capacity count first hc fit (move_mark ea eb ep mark ⟨x,y,direct⟩)

end LastSlicePositive

namespace CriticalPlateau

open Arxiv.«0805.3777»

private lemma boundary_product {a b w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) :
    a*b = w+(a+b-2)+1 := by
  have h₁ : a-1+1=a := by omega
  have h₂ : b-1+1=b := by omega
  have h : (a-1+1)*(b-1+1)=a*b := by rw [h₁,h₂]
  have h₃ : a*b+1=w+a+b := by nlinarith only [h,h₁,h₂,hw]
  omega

/-- Exactly the top values of the third dimension have dimension-count
ceiling one above the critical boundary dimension. -/
theorem rank_eq_iff {a b k w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) (hk : k≤w) :
    (a*b*k ⌈/⌉ (a+b+k-2) = w+1) ↔ w*(a+b-2)<(a+b-1)*k := by
  let D := a+b-2
  have hp : 0<D+k := by dsimp [D]; omega
  have hd : a+b+k-2=D+k := by dsimp [D]; omega
  have hs : a+b-1=D+1 := by dsimp [D]; omega
  rw [hd,hs,boundary_product ha hb hw]
  change ((w+D+1)*k ⌈/⌉ (D+k) = w+1) ↔ w*D<(D+1)*k
  let R := (w+D+1)*k ⌈/⌉ (D+k)
  have hihi : R≤w+1 := by
    apply (ceilDiv_le_iff_le_mul hp).mpr
    nlinarith only [Nat.mul_le_mul_left D (show k≤w+1 by omega)]
  have hcomp : R≤w ↔ (w+D+1)*k ≤ (D+k)*w := ceilDiv_le_iff_le_mul hp
  change R=w+1 ↔ w*D<(D+1)*k
  constructor
  · intro he
    have hgt : (D+k)*w < (w+D+1)*k := lt_of_not_ge (fun h => by have := hcomp.mpr h; omega)
    nlinarith only [hgt]
  · intro h
    have hgt : (D+k)*w < (w+D+1)*k := by nlinarith only [h]
    have hn : ¬R≤w := fun hs => (not_le_of_gt hgt) (hcomp.mp hs)
    omega

theorem rank_eq {a b k w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) (hk : k≤w)
    (ht : w*(a+b-2)<(a+b-1)*k) : a*b*k ⌈/⌉ (a+b+k-2) = w+1 :=
  (rank_eq_iff ha hb hw hk).mpr ht

/-- Express the strict threshold in terms of distance below the boundary. -/
theorem offset_mul_iff {a b k w : ℕ} (ha : 3≤a) (hk : k≤w) :
    w*(a+b-2)<(a+b-1)*k ↔ (a+b-1)*(w-k)<w := by
  rw [show a+b-1=(a+b-2)+1 by omega]
  have hd := congrArg (fun u : ℕ => ((a+b-2)+1)*u) (Nat.sub_add_cancel hk)
  constructor <;> intro h <;> nlinarith only [hd,h]

/-- The boundary offset must be strictly smaller than the ceiling of w/(a+b-1). -/
theorem offset_iff {a b k w : ℕ} (ha : 3≤a) (hk : k≤w) :
    w*(a+b-2)<(a+b-1)*k ↔ w-k < w ⌈/⌉ (a+b-1) := by
  rw [offset_mul_iff ha hk]
  have h := (ceilDiv_le_iff_le_mul (by omega : 0<a+b-1) (b:=w) (c:=w-k))
  omega

/-- Restrict the third factors of a boundary witness. Every prescribed
tensor on the retained coordinates extends by zero to the original tensor space. -/
theorem projected_witness {a b k w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) (hk : k≤w) :
    ∃ x : Fin (w+1) → Fin a → ℂ, ∃ y : Fin (w+1) → Fin b → ℂ, ∃ z : Fin (w+1) → Fin k → ℂ,
      ∀ T : Fin a → Fin b → Fin k → ℂ, ∃ u : Fin (w+1) → Fin a → ℂ,
        ∃ v : Fin (w+1) → Fin b → ℂ, ∃ s : Fin (w+1) → Fin k → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)) := by
  have hwit := RemainingBoundary.boundary_witness (a:=a) (b:=b) (c:=w) ha hb hw
  dsimp only at hwit
  have hr : a*b*w ⌈/⌉ (a+b+w-2)=w+1 := by
    subst w
    exact critical_ceilDiv ha hb
  rw [hr] at hwit
  obtain ⟨x,y,z,span⟩ := hwit
  refine ⟨fun t i => ((x t i).val : ℂ), fun t j => ((y t j).val : ℂ),
    fun t l => ((z t (Fin.castLE hk l)).val : ℂ), ?_⟩
  intro T
  let extend (i : Fin a) (j : Fin b) (l : Fin w) := if hl : l.val<k then T i j ⟨l.val,hl⟩ else 0
  obtain ⟨u,v,s,hs⟩ := span extend
  refine ⟨u,v,fun t l => s t (Fin.castLE hk l),?_⟩
  intro i j l
  simpa [extend,l.isLt] using hs i j (Fin.castLE hk l)

open Arxiv.«0805.3777» in
/-- Throughout the complete top plateau the complex generic rank is w+1. -/
theorem generic_rank {a b k w : ℕ} (ha : 3≤a) (hab : a≤b) (hbk : b≤k)
    (hw : w=(a-1)*(b-1)) (hk : k≤w) (ht : w*(a+b-2)<(a+b-1)*k) :
    IsGenericRank [a,b,k] (w+1) := by
  have hr := rank_eq ha (ha.trans hab) hw hk ht
  rw [←hr]
  apply OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b k ha hab hbk
  rw [hr]
  exact CriticalReduction.bounded_of_witness (projected_witness ha (ha.trans hab) hw hk)

/-- When the first two sides are equal, the plateau contains one more
boundary offset exactly when n reaches the next even integer. -/
theorem square_offset_iff (n d : ℕ) (hn : 3≤n) :
    (n+n-1)*d < (n-1)^2 ↔ 2*d+2 ≤ n := by
  let h := n-1
  have hpos : 0<h := by dsimp [h]; omega
  rw [show n+n-1=2*h+1 by dsimp [h]; omega]
  change (2*h+1)*d<h^2 ↔ _
  constructor
  · intro ht
    by_contra! hbad
    have hs : h≤2*d := by dsimp [h]; omega
    nlinarith only [Nat.mul_le_mul_left (2*h+1) hs, ht, hpos]
  · intro ht
    have hs : 2*d+1≤h := by dsimp [h]; omega
    nlinarith only [Nat.mul_le_mul_left (2*h+1) hs, hpos]

/-- For n by n matrices the width of the top ceiling plateau is floor(n/2). -/
theorem square_width (n : ℕ) (hn : 3≤n) : (n-1)^2 ⌈/⌉ (n+n-1) = n/2 := by
  have characterize (d : ℕ) : d < (n-1)^2 ⌈/⌉ (n+n-1) ↔ d < n/2 := by
    have hp := (ceilDiv_le_iff_le_mul (by omega : 0<n+n-1) (b:=(n-1)^2) (c:=d))
    have hs := square_offset_iff n d hn
    omega
  apply le_antisymm
  · by_contra! bad
    exact (not_lt_of_ge le_rfl) ((characterize _).mp bad)
  · by_contra! bad
    exact (not_lt_of_ge le_rfl) ((characterize _).mpr bad)

end CriticalPlateau

namespace CriticalPlateau.Full

private lemma budget_id {a b w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1)) :
    0<w ∧ a*b = w+(a+b-1) ∧ a*b=(w-1)+(a+b) := by
  subst w
  have ha₁ : 1≤a := by omega
  have hb₁ : 1≤b := by omega
  have hs : 1≤a+b := by omega
  have hw₀ : 0<(a-1)*(b-1) := Nat.mul_pos (by omega) (by omega)
  refine ⟨hw₀,?_,?_⟩ <;> zify [ha₁,hb₁,hs,Nat.succ_le_iff.mpr hw₀] <;> ring

theorem ceil_le_iff_offset {a b c w : ℕ} (ha : 3≤a) (hab : a≤b)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) :
    a*b*c ⌈/⌉ (a+b+c-2) ≤ w ↔ w ⌈/⌉ (a+b-1) ≤ w-c := by
  obtain ⟨_,hp,_⟩ := budget_id ha hab hw
  rw [ceilDiv_le_iff_le_mul (by omega : 0<a+b+c-2)]
  rw [hp, show a+b+c-2=(a+b-2)+c by omega]
  have h := CriticalPlateau.offset_iff (a:=a) (b:=b) ha hc
  constructor
  · intro he
    have : (a+b-1)*c ≤ w*(a+b-2) := by nlinarith only [he]
    omega
  · intro he
    have : (a+b-1)*c ≤ w*(a+b-2) := by omega
    nlinarith only [this]

private lemma square_capacity (n d : ℕ) (hn : 3≤n) :
    (n-1)^2 ≤ d*(2*(n-1)) ↔ n/2≤d := by
  rw [pow_two, show d*(2*(n-1))=(n-1)*(2*d) by ring]
  constructor
  · intro h
    have := Nat.le_of_mul_le_mul_left h (show 0<n-1 by omega)
    omega
  · intro h
    exact Nat.mul_le_mul_left _ (by omega)

/-- The ragged family has enough directions precisely when the predicted
rank is no greater than w. The formula includes equality of the first two
dimensions, where the normal count is 2(a-1). -/
theorem capacity_iff {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1)) (hc : c≤w) :
    a*b*c ⌈/⌉ (a+b+c-2) ≤ w ↔ w ≤ (w-c)*((b-1)+min a (b-1)) := by
  rw [ceil_le_iff_offset ha hab hw hc]
  by_cases he : a=b
  · subst b
    have width : w ⌈/⌉ (a+a-1) = a/2 := by
      simpa only [hw, pow_two] using CriticalPlateau.square_width a ha
    rw [width, min_eq_right (Nat.sub_le a 1), show a-1+(a-1)=2*(a-1) by omega]
    simpa only [hw,pow_two] using (square_capacity a (w-c) ha).symm
  · rw [min_eq_left (show a≤b-1 by omega), show b-1+a=a+b-1 by omega,
      ceilDiv_le_iff_le_mul (by omega : 0<a+b-1), Nat.mul_comm (w-c) (a+b-1)]

theorem capacity_of_second {a b c w : ℕ} (ha : 3≤a) (hab : a≤b)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (hr : a*b*c ⌈/⌉ (a+b+c-2) = w) :
    w≤(w-c)*((b-1)+min a (b-1)) :=
  (capacity_iff ha hab hw hc).mp hr.le

/-- Exact lower endpoint for belonging to either of the two highest ceiling values. -/
theorem at_least_second_iff {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1)) :
    w ≤ a*b*c ⌈/⌉ (a+b+c-2) ↔ (w-1)*(a+b-2)<(a+b)*c := by
  obtain ⟨hw₀,_,hp⟩ := budget_id ha hab hw
  have h := ceilDiv_le_iff_le_mul (by omega : 0<a+b+c-2) (b:=a*b*c) (c:=w-1)
  have comp : a*b*c ≤ (a+b+c-2)*(w-1) ↔ (a+b)*c ≤ (w-1)*(a+b-2) := by
    rw [hp, show a+b+c-2=(a+b-2)+c by omega]
    constructor <;> intro hx <;> nlinarith only [hx]
  omega

theorem top_two_ceil {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1))
    (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c) :
    a*b*c ⌈/⌉ (a+b+c-2) = if w*(a+b-2)<(a+b-1)*c then w+1 else w := by
  by_cases top : w*(a+b-2)<(a+b-1)*c
  · rw [if_pos top]
    exact CriticalPlateau.rank_eq ha (ha.trans hab) hw hc top
  · rw [if_neg top]
    apply le_antisymm _ ((at_least_second_iff ha hab hw).mpr ht)
    apply (ceil_le_iff_offset ha hab hw hc).mpr
    have h := CriticalPlateau.offset_iff (a:=a) (b:=b) ha hc
    omega

/-- At square first dimensions the top two bands together occupy exactly
n-1 successive third dimensions, indexed by offsets 0 through n-2. -/
theorem square_top_two_iff {n d : ℕ} (hn : 3≤n) (hd : d≤(n-1)^2) :
    ((n-1)^2-1)*(n+n-2)<(n+n)*((n-1)^2-d) ↔ d<n-1 := by
  let w := (n-1)^2
  have hw : 0<(n-1)^2 := pow_pos (by omega) _
  have h₁ : (n+n)*w = (w-1)*(n+n-2)+(n+n)*(n-1) := by
    dsimp only [w]
    zify [show 1≤n by omega, Nat.succ_le_iff.mpr hw, show 2≤n+n by omega]
    ring
  have h₂ := congrArg (fun x : ℕ => (n+n)*x) (Nat.sub_add_cancel hd)
  change (w-1)*(n+n-2)<(n+n)*(w-d) ↔ _
  change (n+n)*(w-d+d)=(n+n)*w at h₂
  have hmid : (w-1)*(n+n-2)<(n+n)*(w-d) ↔ (n+n)*d < (n+n)*(n-1) := by
    constructor <;> intro hx <;> nlinarith only [h₁,h₂,hx]
  rw [hmid]
  exact ⟨Nat.lt_of_mul_lt_mul_left, fun h => Nat.mul_lt_mul_of_pos_left h (by omega)⟩

end CriticalPlateau.Full

namespace CriticalPlateau.Full

open Arxiv.«0805.3777»

/-- Under the ragged capacity implication, the numerical ceiling is actually
attained by a spanning tangent in both of the two highest bands. -/
theorem expected_witness {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c)
    (seed : w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ s : Fin r → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)) := by
  dsimp only
  rw [top_two_ceil ha hab hw hc ht]
  by_cases top : w*(a+b-2)<(a+b-1)*c
  · rw [if_pos top]
    exact CriticalPlateau.projected_witness ha (by omega) hw hc
  · rw [if_neg top]
    apply seed
    apply capacity_of_second ha hab hw hc
    simpa only [if_neg top] using top_two_ceil ha hab hw hc ht

/-- The actual complex generic rank in the full two-band interval, conditional
only on the ragged seed for this format when its capacity is sufficient. -/
theorem generic_rank {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b) (hbc : b≤c)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c)
    (seed : w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) := by
  rw [← top_two_ceil ha hab hw hc ht]
  apply OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b c ha hab hbc
  exact CriticalReduction.bounded_of_witness (expected_witness ha hab hb hw hc ht seed)

/-- A uniform ragged witness with the stated normal count suffices for every
admissible format in the whole top-two rank interval. -/
theorem of_universal_witness
    (seed : ∀ a b c : ℕ, 3≤a → a≤b → 4≤b → b≤c →
      let w := (a-1)*(b-1)
      c≤w → w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)))
    {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b) (hbc : b≤c)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) := by
  apply generic_rank ha hab hb hbc hw hc ht
  subst w
  exact seed a b c ha hab hb hbc hc

/-- The same uniform construction covers every top-two format in the critical
range away from the exceptional 3-by-3-by-3 cube. At b=3 the remaining
format is the already proved critical boundary 3-by-3-by-4. -/
theorem of_universal_witness_away_cube
    (seed : ∀ a b c : ℕ, 3≤a → a≤b → 4≤b → b≤c →
      let w := (a-1)*(b-1)
      c≤w → w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)))
    {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hbc : b≤c) (hx : (a,b,c) ≠ (3,3,3))
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) := by
  by_cases hb : 4≤b
  · exact of_universal_witness seed ha hab hb hbc hw hc ht
  · obtain rfl : a=3 := by omega
    obtain rfl : b=3 := by omega
    obtain rfl : w=4 := hw
    have h₃ : c≠3 := by rintro rfl; exact hx rfl
    obtain rfl : c=4 := by omega
    exact CriticalPlateau.generic_rank (by decide : 3≤3) le_rfl (by decide : 3≤4)
      (by decide : 4=(3-1)*(3-1)) le_rfl (by decide)

/-- For n at least four the top n-1 square offsets give the two ranks shown:
the first floor(n/2) offsets have rank w+1, and the rest have rank w. -/
theorem square_generic_rank (n d : ℕ) (hn : 4≤n) (hd : d<n-1)
    (seed : let w := (n-1)^2
      w ≤ d*(2*(n-1)) →
      ∃ x : Fin w → Fin n → ℂ, ∃ y : Fin w → Fin n → ℂ, ∃ z : Fin w → Fin (w-d) → ℂ,
      ∀ T : Fin n → Fin n → Fin (w-d) → ℂ, ∃ u : Fin w → Fin n → ℂ,
        ∃ v : Fin w → Fin n → ℂ, ∃ s : Fin w → Fin (w-d) → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    IsGenericRank [n,n,(n-1)^2-d] (if d<n/2 then (n-1)^2+1 else (n-1)^2) := by
  let w := (n-1)^2
  have hs : 2*(n-1) ≤ w := by
    simpa only [w, pow_two] using Nat.mul_le_mul_right (n-1) (show 2≤n-1 by omega)
  have hdn : d≤w := by omega
  have hk : w-d≤w := Nat.sub_le _ _
  have hw : w=(n-1)*(n-1) := by dsimp [w]; ring
  have ht := (square_top_two_iff (by omega : 3≤n) (show d≤(n-1)^2 from hdn)).mpr hd
  have top : w*(n+n-2)<(n+n-1)*(w-d) ↔ d<n/2 := by
    rw [CriticalPlateau.offset_mul_iff (by omega : 3≤n) hk, show w-(w-d)=d by omega]
    exact (CriticalPlateau.square_offset_iff n d (by omega)).trans (by omega)
  have h := generic_rank (by omega : 3≤n) le_rfl hn (show n≤w-d by omega) hw hk ht (by
    intro hcap
    apply seed
    rw [show w-(w-d)=d by omega, min_eq_right (Nat.sub_le n 1),
      show n-1+(n-1)=2*(n-1) by omega] at hcap
    exact hcap)
  change IsGenericRank [n,n,w-d] (if d<n/2 then w+1 else w)
  by_cases b : d<n/2
  · simpa only [if_pos b, if_pos (top.mpr b)] using h
  · simpa only [if_neg b, if_neg (fun v => b (top.mp v))] using h

end CriticalPlateau.Full

namespace CriticalPlateau.Proved

open Arxiv.«0805.3777»

/-- In the two highest predicted-rank bands, the generic complex tensor has
the indicated rank. The only excluded cube in this band statement is 3 by 3 by 3. -/
theorem generic_rank {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hbc : b≤c)
    (hx : (a,b,c) ≠ (3,3,3)) (hw : w=(a-1)*(b-1)) (hc : c≤w)
    (ht : (w-1)*(a+b-2)<(a+b)*c) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) :=
  CriticalPlateau.Full.of_universal_witness_away_cube
    (fun a b c ha hab hb _ => LastSlicePositive.second_full a b c ha hb hab) ha hab hbc hx hw hc ht

/-- The catalogue dimension-count value is attained throughout both bands. -/
theorem generic_rank_at_ceiling {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hbc : b≤c)
    (hx : (a,b,c) ≠ (3,3,3)) (hw : w=(a-1)*(b-1)) (hc : c≤w)
    (high : w ≤ a*b*c ⌈/⌉ (a+b+c-2)) :
    IsGenericRank [a,b,c] (a*b*c ⌈/⌉ (a+b+c-2)) := by
  have ht := (CriticalPlateau.Full.at_least_second_iff ha hab hw).mp high
  rw [CriticalPlateau.Full.top_two_ceil ha hab hw hc ht]
  exact generic_rank ha hab hbc hx hw hc ht

end CriticalPlateau.Proved

namespace CriticalHigher.Blocks

open MvPolynomial

/-- A full-row-rank specialization gives a nonzero determinant polynomial.
Taking the product gives one specialization for a finite family of matrices. -/
theorem common_surjective {G V : Type*} [Fintype G] {I J : G → Type*}
    [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (M : ∀ g, Matrix (I g) (J g) (MvPolynomial V ℂ))
    (each : ∀ g, ∃ v : V → ℂ, Function.Surjective ((M g).map (eval v)).mulVec) :
    ∃ p : V → ℂ, ∀ g, Function.Surjective ((M g).map (eval p)).mulVec := by
  classical
  choose v good using each
  choose B inverse using fun g => Matrix.mulVec_surjective_iff_exists_right_inverse.mp (good g)
  let P (g : G) := (B g).map (C : ℂ →+* MvPolynomial V ℂ)
  let Q (g : G) := (M g*P g).det
  have spec (g : G) (u : V → ℂ) :
      eval u (Q g) = ((M g).map (eval u)*B g).det := by
    have constant : (P g).map (eval u)=B g := by ext; simp [P,Matrix.map_apply]
    change eval u (M g*P g).det = _
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,constant]
  have nz (g : G) : Q g≠0 := by
    intro zero
    have atPoint := spec g (v g)
    rw [zero,map_zero,inverse g,Matrix.det_one] at atPoint
    exact zero_ne_one atPoint
  have allnz : (∏ g,Q g)≠0 := Finset.prod_ne_zero_iff.mpr fun g _ => nz g
  obtain ⟨p,hp⟩ : ∃ p : V → ℂ, eval p (∏ g,Q g)≠0 := by
    by_contra! vanish
    exact allnz (MvPolynomial.funext fun q => by rw [vanish q,map_zero])
  have eachnz : (∏ g,eval p (Q g))≠0 := by simpa only [map_prod] using hp
  refine ⟨p,fun g => ?_⟩
  have hdet := Finset.prod_ne_zero_iff.mp eachnz g (Finset.mem_univ g)
  rw [spec] at hdet
  have onto := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro t
  obtain ⟨s,hs⟩ := onto t
  exact ⟨(B g).mulVec s,(Matrix.mulVec_mulVec _ _ _).trans hs⟩

/-- In one block all sampled products have free variations in the last
factor. Only the samples assigned to the block have their first two
variations present. Each separately verified block can use different
factors before common specialization. -/
theorem common_tangents {A B C P G : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype P] [Fintype G] [DecidableEq G] (label : P → G) :
    let D (g : G) (x : P → A → ℂ) (y : P → B → ℂ) (z : P → C → ℂ) :=
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, ((if label t=g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))
    (∀ g, ∃ x y z, D g x y z) → ∃ x y z, ∀ g, D g x y z := by
  classical
  intro D each
  let V := P × (A ⊕ (B ⊕ C))
  let M (g : G) : Matrix ((A × B) × C) V (MvPolynomial V ℂ) := fun row col => col.2.elim
    (fun i => if label col.1=g ∧ i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
    (Sum.elim
      (fun j => if label col.1=g ∧ j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
      (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  let pack (x : P → A → ℂ) (y : P → B → ℂ) (z : P → C → ℂ) : V → ℂ :=
    fun (t,q) => q.elim (x t) (Sum.elim (y t) (z t))
  have action (g : G) (p q : V → ℂ) (i : A) (j : B) (k : C) :
      ((M g).map (eval p)).mulVec q ((i,j),k) = ∑ t,
        ((if label t=g then q (t,.inl i)*(p (t,.inr (.inl j))*p (t,.inr (.inr k))) +
           p (t,.inl i)*(q (t,.inr (.inl j))*p (t,.inr (.inr k))) else 0) +
           p (t,.inl i)*(p (t,.inr (.inl j))*q (t,.inr (.inr k)))) := by
    change (∑ s : V, eval p (M g ((i,j),k) s)*q s) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    by_cases hit : label t=g <;> simp [M,hit,apply_ite,ite_mul,Finset.sum_ite_eq'] <;> ring
  have localFull (g : G) : ∃ p : V → ℂ, Function.Surjective ((M g).map (eval p)).mulVec := by
    obtain ⟨x,y,z,h⟩ := each g
    refine ⟨pack x y z,?_⟩
    intro T
    obtain ⟨u,v,w,cover⟩ := h fun i j k => T ((i,j),k)
    refine ⟨pack u v w,?_⟩
    funext ⟨⟨i,j⟩,k⟩
    exact (action g (pack x y z) (pack u v w) i j k).trans (cover i j k).symm
  obtain ⟨p,good⟩ := common_surjective M localFull
  refine ⟨fun t i => p (t,.inl i),fun t j => p (t,.inr (.inl j)),fun t k => p (t,.inr (.inr k)),?_⟩
  intro g T
  obtain ⟨q,hq⟩ := good g fun s => T s.1.1 s.1.2 s.2
  exact ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),fun t k => q (t,.inr (.inr k)),
    fun i j k => (congrFun hq ((i,j),k)).symm.trans (action g p q i j k)⟩

/-- Put each point's third vector in its assigned coordinate block. Third
variations can act on all blocks independently, so the local witnesses
produce a spanning tangent for the whole tensor. -/
theorem spans_of_blocks {A B C P G : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype P] [Fintype G] [DecidableEq G] (label : P → G)
    (one : ∀ g, ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∃ z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, ((if label t=g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∃ Z : P → G × C → ℂ,
      ∀ T : A → B → G × C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → G × C → ℂ,
        ∀ i j k, T i j k=∑ t,(u t i*(y t j*Z t k)+x t i*(v t j*Z t k)+x t i*(y t j*w t k)) := by
  classical
  obtain ⟨x,y,z,good⟩ := common_tangents label one
  let Z (t : P) (p : G × C) := if label t=p.1 then z t p.2 else 0
  refine ⟨x,y,Z,?_⟩
  intro T
  choose U V W repr using fun g => good g (fun i j k => T i j (g,k))
  refine ⟨fun t => U (label t) t, fun t => V (label t) t, fun t k => W k.1 t k.2,?_⟩
  rintro i j ⟨g,k⟩
  apply (repr g i j k).trans
  apply Finset.sum_congr rfl
  intro t _
  by_cases hit : label t=g <;> simp [Z,hit]

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

/-- Reindex a full tangent plus an external-product supplement onto any
finite point set, allowing the first two variations only on its marked set. -/
private theorem restricted_tangent_of_split {A B C P M N : Type*}
    [Fintype P] [Fintype M] [Fintype N] (active : P → Prop) [DecidablePred active]
    (e : (M ⊕ N) ≃ P) (marked : ∀ t : M, active (e (.inl t)))
    (one : ∃ x : M → A → ℂ, ∃ y : M → B → ℂ, ∃ z : M → C → ℂ,
      ∃ x' : N → A → ℂ, ∃ y' : N → B → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : M → A → ℂ, ∃ v : M → B → ℂ, ∃ w : M → C → ℂ,
      ∃ w' : N → C → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
      T i j k = ∑ t, ((if active t then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
        X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,x',y',hit⟩ := one
  let X (p : P) := (e.symm p).elim x x'
  let Y (p : P) := (e.symm p).elim y y'
  let Z (p : P) := (e.symm p).elim z 0
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨u,v,w,w',cover⟩ := hit T
  refine ⟨fun p => (e.symm p).elim u 0,fun p => (e.symm p).elim v 0,fun p => (e.symm p).elim w w',?_⟩
  intro i j k
  rw [cover i j k,← e.sum_comp,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    simp only [X,Y,Z,Equiv.symm_apply_apply,Sum.elim_inl,if_pos (marked t)]
  · apply Finset.sum_congr rfl
    intro t _
    simp [X,Y,Z]

/-- Choose a complementary enumeration for one group among the r points.
The designated group is the left summand and every other point is external. -/
private theorem pencil_group_complement {h m r : ℕ} (slots : h*m ≤ r) (g : Fin h) :
    ∃ e : (Fin m ⊕ Fin (r-m)) ≃ ((Fin h × Fin m) ⊕ Fin (r-h*m)),
      ∀ j : Fin m, e (.inl j) = .inl (g,j) := by
  classical
  let P := (Fin h × Fin m) ⊕ Fin (r-h*m)
  let f : Fin m → P := fun j => .inl (g,j)
  have finj : Function.Injective f := fun u v ev => congrArg Prod.snd (Sum.inl.inj ev)
  let front := Equiv.ofInjective f finj
  have size : Fintype.card P = r := by
    simp only [P,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have frontSize : Fintype.card {p : P // p ∈ Set.range f} = m := by
    rw [← Fintype.card_congr front,Fintype.card_fin]
  let rest : {p : P // p ∉ Set.range f} ≃ Fin (r-m) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl,frontSize,size])
  let e := (Equiv.sumCongr front rest.symm).trans (Equiv.sumCompl (fun p => p ∈ Set.range f))
  exact ⟨e,fun _ => rfl⟩

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

theorem tangent_cycle {A B C P : Type*} [Fintype P]
    (one : ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ,
      ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k))) :
    ∃ X : P → C → ℂ, ∃ Y : P → A → ℂ, ∃ Z : P → B → ℂ,
    ∀ T : C → A → B → ℂ, ∃ u : P → C → ℂ, ∃ v : P → A → ℂ,
    ∃ w : P → B → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,cover⟩ := one
  refine ⟨z,x,y,?_⟩
  intro T
  obtain ⟨u,v,w,rep⟩ := cover (fun i j k => T k i j)
  refine ⟨w,u,v,?_⟩
  intro k i j
  rw [rep i j k]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem tangent_swap_last {A B C P : Type*} [Fintype P]
    (one : ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ,
      ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k))) :
    ∃ X : P → A → ℂ, ∃ Y : P → C → ℂ, ∃ Z : P → B → ℂ,
    ∀ T : A → C → B → ℂ, ∃ u : P → A → ℂ, ∃ v : P → C → ℂ,
    ∃ w : P → B → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,cover⟩ := one
  refine ⟨x,z,y,?_⟩
  intro T
  obtain ⟨u,v,w,rep⟩ := cover (fun i j k => T i k j)
  refine ⟨u,w,v,?_⟩
  intro i k j
  rw [rep i j k]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem many_pencil_third (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin (2*h) → ℂ,
    ∀ T : Fin a → Fin b → Fin (2*h) → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
    ∃ w : Fin r → Fin (2*h) → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  by_cases empty : h=0
  · subst h
    exact ⟨0,0,0,fun _ => ⟨0,0,0,fun _ _ k => Fin.elim0 k⟩⟩
  let P := (Fin h × Fin m) ⊕ Fin (r-h*m)
  let label : P → Fin h := Sum.elim Prod.fst (fun _ => ⟨0,Nat.pos_of_ne_zero empty⟩)
  have each (g : Fin h) : ∃ X : P → Fin a → ℂ, ∃ Y : P → Fin b → ℂ, ∃ Z : P → Fin 2 → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : P → Fin a → ℂ, ∃ v : P → Fin b → ℂ, ∃ w : P → Fin 2 → ℂ,
      ∀ i j k, T i j k = ∑ t, ((if label t=g then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
        X t i*(Y t j*w t k)) := by
    obtain ⟨e,he⟩ := pencil_group_complement slots g
    apply restricted_tangent_of_split (fun t => label t=g) e _ one
    intro s
    rw [he s]
    rfl
  obtain ⟨x,y,z,span⟩ := spans_of_blocks label each
  let points : P ≃ Fin r := Fintype.equivFinOfCardEq (by
    simp only [P,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega)
  let coords : (Fin h × Fin 2) ≃ Fin (2*h) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨fun t => x (points.symm t),fun t => y (points.symm t),fun t k => z (points.symm t) (coords.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,hcover⟩ := span fun i j k => T i j (coords k)
  refine ⟨fun t => u (points.symm t),fun t => v (points.symm t),fun t k => w (points.symm t) (coords.symm k),?_⟩
  intro i j k
  have atRow := hcover i j (coords.symm k)
  simp only [Equiv.apply_symm_apply] at atRow
  rw [atRow,← points.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem many_pencil_first (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin (2*h) → ℂ, ∃ Y : Fin r → Fin a → ℂ, ∃ Z : Fin r → Fin b → ℂ,
    ∀ T : Fin (2*h) → Fin a → Fin b → ℂ, ∃ u : Fin r → Fin (2*h) → ℂ, ∃ v : Fin r → Fin a → ℂ,
    ∃ w : Fin r → Fin b → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  exact tangent_cycle (many_pencil_third a b h m r slots one)

theorem many_pencil_second (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin (2*h) → ℂ, ∃ Z : Fin r → Fin b → ℂ,
    ∀ T : Fin a → Fin (2*h) → Fin b → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin (2*h) → ℂ,
    ∃ w : Fin r → Fin b → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  exact tangent_swap_last (many_pencil_third a b h m r slots one)

end CriticalHigher.Blocks

namespace CriticalLastSlice.HigherPencil

/-- Pair consecutive positions in the listing by layer and then label. When
the last position is alone, pair it with the first. Every pair uses two
different labels, and each label's layers occur at distinct primary samples. -/
theorem cyclic_schedule (m n : ℕ) (hm : 2≤ m) :
    let S := Fin ((n*m+1)/2)
    ∃ L R : S → Fin n × Fin m, ∃ sample : Fin m → Fin n → S,
      (∀ s,(L s).2 ≠ (R s).2) ∧ (∀ i,Function.Injective (sample i)) ∧
      ∀ i j,L (sample i j)=(j,i) ∨ R (sample i j)=(j,i) := by
  intro S
  let even (s : S) : Fin (n*m) := ⟨2*s.val,by have := s.isLt; omega⟩
  let next (s : S) : Fin (n*m) := if h : 2*s.val+1<n*m then ⟨2*s.val+1,h⟩
    else ⟨0,by have := s.isLt; omega⟩
  let sample (i : Fin m) (j : Fin n) : S :=
    ⟨(finProdFinEquiv (j,i)).val/2,by have := (finProdFinEquiv (j,i)).isLt; omega⟩
  have next_ne (q : ℕ) : q%m ≠ (q+1)%m := by
    rw [Nat.add_mod,Nat.mod_eq_of_lt (by omega : 1< m)]
    have bound := Nat.mod_lt q (by omega : 0< m)
    by_cases hs : q%m+1< m
    · rw [Nat.mod_eq_of_lt hs]; omega
    · rw [show q%m+1=m by omega,Nat.mod_self]; omega
  refine ⟨fun s => finProdFinEquiv.symm (even s),fun s => finProdFinEquiv.symm (next s),
    sample,?_,?_,?_⟩
  · intro s hg
    apply next_ne (2*s.val)
    have eq := congrArg Fin.val hg
    change (2*s.val)%m=(next s).val%m at eq
    by_cases h : 2*s.val+1<n*m
    · simpa only [next,dif_pos h] using eq
    · have last : 2*s.val+1=n*m := by have := (even s).isLt; change 2*s.val<n*m at this; omega
      simpa [next,h,last] using eq
  · intro i j k eq
    have strict : StrictMono (fun t : ℕ => (i.val+m*t)/2) := by
      apply strictMono_nat_of_lt_succ
      intro t
      have bound : i.val+m*t+2 ≤ i.val+m*(t+1) := by rw [Nat.mul_add]; omega
      omega
    exact Fin.ext (strict.injective (congrArg Fin.val eq))
  · intro i j
    let q := finProdFinEquiv (j,i)
    have hit : (sample i j).val=q.val/2 := rfl
    by_cases h : q.val%2=0
    · left
      have he : even (sample i j)=q := Fin.ext (by change 2*(sample i j).val=q.val; omega)
      exact (congrArg finProdFinEquiv.symm he).trans (finProdFinEquiv.symm_apply_apply _)
    · right
      have he : 2*(sample i j).val+1=q.val := by omega
      have bound : 2*(sample i j).val+1<n*m := he ▸ q.isLt
      have hn : next (sample i j)=q := Fin.ext (by simp only [next,dif_pos bound,he])
      exact (congrArg finProdFinEquiv.symm hn).trans (finProdFinEquiv.symm_apply_apply _)

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- Two pencil coefficients separate the evaluations at different labels.
Vandermonde interpolation at each label's distinct samples recovers both
the complete marked row tail and the complete marked column tail. -/
theorem interpolate_slots {m d e : ℕ} {S : Type*}
    (node : S → ℂ) (hn : Function.Injective node) (μ : Fin m → ℂ) (hμ : Function.Injective μ)
    (L R : S → (Fin e ⊕ Fin d) × Fin m) (sample : Fin m → (Fin e ⊕ Fin d) → S)
    (separate : ∀ s,(L s).2 ≠ (R s).2) (distinct : ∀ i,Function.Injective (sample i))
    (cover : ∀ i j,L (sample i j)=(j,i) ∨ R (sample i j)=(j,i))
    (Y : Fin m → Fin e → ℂ) (X : Fin m → Fin d → ℂ) :
    let value (s : S) (q : (Fin e ⊕ Fin d) × Fin m) := q.1.elim
      (fun _ => ∑ j : Fin e,node s^j.val*Y q.2 j) (fun _ => ∑ i : Fin d,node s^i.val*X q.2 i)
    (∀ s,value s (L s)+value s (R s)=0) →
    (∀ s,μ (L s).2*value s (L s)+μ (R s).2*value s (R s)=0) → Y=0 ∧ X=0 := by
  intro value h₀ h₁
  have zero (s : S) : value s (L s)=0 ∧ value s (R s)=0 := by
    have diff : (μ (L s).2-μ (R s).2)*value s (L s)=0 := by
      linear_combination h₁ s - μ (R s).2 * h₀ s
    have nz : μ (L s).2-μ (R s).2≠0 := sub_ne_zero.mpr (fun eq => separate s (hμ eq))
    have left := (mul_eq_zero.mp diff).resolve_left nz
    exact ⟨left,by simpa only [left,zero_add] using h₀ s⟩
  have sampled (i : Fin m) (j : Fin e ⊕ Fin d) : value (sample i j) (j,i)=0 := by
    rcases cover i j with hl|hr
    · simpa only [hl] using (zero (sample i j)).1
    · simpa only [hr] using (zero (sample i j)).2
  constructor
  · funext i
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (f:=fun j : Fin e => node (sample i (.inl j)))
    · intro j k eq
      exact Sum.inl.inj (distinct i (hn eq))
    · exact fun j => sampled i (.inl j)
  · funext i
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (f:=fun j : Fin d => node (sample i (.inr j)))
    · intro j k eq
      exact Sum.inr.inj (distinct i (hn eq))
    · exact fun j => sampled i (.inr j)

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- A pure bilinear sample on the two off-diagonal blocks splits into its
upper row contributions and its upper column contributions. -/
theorem sample_off_diagonal {m d e : ℕ} (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
    (core : ∀ i j,M (.inl i) (.inl j)=0) (bottom : ∀ i j,M (.inr i) (.inr j)=0)
    (x y : Fin m → ℂ) (x' : Fin d → ℂ) (y' : Fin e → ℂ) :
    (∑ i,∑ j,(Sum.elim x x' i)*(Sum.elim y y' j)*M i j) =
      (∑ i,x i*(∑ j,y' j*M (.inl i) (.inr j))) +
      (∑ j,y j*(∑ i,x' i*M (.inr i) (.inl j))) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,core,bottom,mul_zero,
    Finset.sum_const_zero,zero_add,add_zero]
  congr 1
  · simp only [Finset.mul_sum,mul_assoc]
  · rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- One product reads two evaluation slots at the same Vandermonde node
regardless of whether the slots concern rows, columns, or one of each. -/
theorem two_slot_sample {m d e : ℕ} (z : ℂ) (L R : (Fin e ⊕ Fin d) × Fin m) :
    ∃ x : (Fin m ⊕ Fin d) → ℂ, ∃ y : (Fin m ⊕ Fin e) → ℂ,
      ∀ M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ,
        (∀ i j,M (.inl i) (.inl j)=0) → (∀ i j,M (.inr i) (.inr j)=0) →
        let value (q : (Fin e ⊕ Fin d) × Fin m) := q.1.elim
          (fun _ => ∑ j : Fin e,z^j.val*M (.inl q.2) (.inr j))
          (fun _ => ∑ i : Fin d,z^i.val*M (.inr i) (.inl q.2))
        (∑ i,∑ j,x i*y j*M i j)=value L+value R := by
  classical
  let xw (q : (Fin e ⊕ Fin d) × Fin m) (i : Fin m) : ℂ :=
    q.1.elim (fun _ => if i=q.2 then 1 else 0) (fun _ => 0)
  let yw (q : (Fin e ⊕ Fin d) × Fin m) (i : Fin m) : ℂ :=
    q.1.elim (fun _ => 0) (fun _ => if i=q.2 then 1 else 0)
  let x (i : Fin m) := xw L i+xw R i
  let y (i : Fin m) := yw L i+yw R i
  refine ⟨Sum.elim x (fun i => z^i.val),Sum.elim y (fun j => z^j.val),?_⟩
  intro M core bottom value
  rw [sample_off_diagonal M core bottom]
  rcases L with ⟨i|i,u⟩ <;> rcases R with ⟨j|j,v⟩ <;>
    simp [x,y,xw,yw,value,add_mul,Finset.sum_add_distrib,ite_mul,Finset.sum_ite_eq',add_comm]

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- Place m full points on the diagonal with third vectors (1,λᵢ). A further
d*e + ceil(m*(d+e)/2) pure products force the whole dual pencil to vanish.
Here the two matrix dimensions are m+d and m+e. -/
theorem product_samples {m d e : ℕ} (hm : 2 ≤ m)
    (lam : Fin m → ℂ) (hlam : Function.Injective lam) :
    let S := Fin (((e+d)*m+1)/2)
    let P := (Fin d × Fin e) ⊕ S
    ∃ x : P → (Fin m ⊕ Fin d) → ℂ, ∃ y : P → (Fin m ⊕ Fin e) → ℂ,
      ∀ U V : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ,
        (∀ i,U (.inl i) (.inl i)=0 ∧ V (.inl i) (.inl i)=0) →
        (∀ i j,U (.inl i) j+lam i*V (.inl i) j=0) →
        (∀ i j,U j (.inl i)+lam i*V j (.inl i)=0) →
        (∀ p,∑ i,∑ j,x p i*y p j*U i j=0) →
        (∀ p,∑ i,∑ j,x p i*y p j*V i j=0) → U=0 ∧ V=0 := by
  classical
  intro S P
  obtain ⟨L₀,R₀,pick,ne,dist,cover₀⟩ := cyclic_schedule m (e+d) hm
  let decode (q : Fin (e+d) × Fin m) : (Fin e ⊕ Fin d) × Fin m := (finSumFinEquiv.symm q.1,q.2)
  let L (s : S) := decode (L₀ s)
  let R (s : S) := decode (R₀ s)
  let sample (i : Fin m) (q : Fin e ⊕ Fin d) := pick i (finSumFinEquiv q)
  have cover (i : Fin m) (q : Fin e ⊕ Fin d) :
      L (sample i q)=(q,i) ∨ R (sample i q)=(q,i) := by
    have back : decode (finSumFinEquiv q,i)=(q,i) := by simp [decode]
    rcases cover₀ i (finSumFinEquiv q) with hl|hr
    · exact Or.inl ((congrArg decode hl).trans back)
    · exact Or.inr ((congrArg decode hr).trans back)
  let node (s : S) : ℂ := s.val
  choose xs ys reading using fun s : S => two_slot_sample (node s) (L s) (R s)
  let x : P → (Fin m ⊕ Fin d) → ℂ := Sum.elim (fun q i => if i=.inr q.1 then 1 else 0) xs
  let y : P → (Fin m ⊕ Fin e) → ℂ := Sum.elim (fun q j => if j=.inr q.2 then 1 else 0) ys
  let eval (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ) (s : S) (q : (Fin e ⊕ Fin d) × Fin m) :=
    q.1.elim (fun _ => ∑ j : Fin e,node s^j.val*M (.inl q.2) (.inr j))
      (fun _ => ∑ i : Fin d,node s^i.val*M (.inr i) (.inl q.2))
  have lower (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
      (sampled : ∀ p,∑ i,∑ j,x p i*y p j*M i j=0) (i : Fin d) (j : Fin e) :
      M (.inr i) (.inr j)=0 := by
    have h := sampled (.inl (i,j))
    simpa [x,y,ite_mul,Finset.sum_ite_eq',Finset.sum_ite_irrel] using h
  have evals (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
      (core : ∀ i j,M (.inl i) (.inl j)=0) (sampled : ∀ p,∑ i,∑ j,x p i*y p j*M i j=0)
      (s : S) : eval M s (L s)+eval M s (R s)=0 :=
    (reading s M core (lower M sampled)).symm.trans (sampled (.inr s))
  refine ⟨x,y,?_⟩
  intro U V diag row col testU testV
  have core (i j : Fin m) : U (.inl i) (.inl j)=0 ∧ V (.inl i) (.inl j)=0 := by
    by_cases eq : i=j
    · subst j
      exact diag i
    · have weighted : (lam i-lam j)*V (.inl i) (.inl j)=0 := by
        linear_combination row i (.inl j)-col j (.inl i)
      have vzero := (mul_eq_zero.mp weighted).resolve_left (sub_ne_zero.mpr (fun h => eq (hlam h)))
      exact ⟨by simpa only [vzero,mul_zero,add_zero] using row i (.inl j),vzero⟩
  have rowU (i : Fin m) (j : Fin e) :
      U (.inl i) (.inr j)=(-lam i)*V (.inl i) (.inr j) := by
    linear_combination row i (.inr j)
  have colU (i : Fin m) (j : Fin d) :
      U (.inr j) (.inl i)=(-lam i)*V (.inr j) (.inl i) := by
    linear_combination col i (.inr j)
  have relate (s : S) (q : (Fin e ⊕ Fin d) × Fin m) :
      eval U s q=(-lam q.2)*eval V s q := by
    rcases q with ⟨j|i,k⟩
    · simp only [eval,Sum.elim_inl,Finset.mul_sum,rowU]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [eval,Sum.elim_inr,Finset.mul_sum,colU]
      apply Finset.sum_congr rfl
      intro j _
      ring
  have plain := evals V (fun i j => (core i j).2) testV
  have weighted (s : S) : (-lam (L s).2)*eval V s (L s)+(-lam (R s).2)*eval V s (R s)=0 := by
    rw [← relate,← relate]
    exact evals U (fun i j => (core i j).1) testU s
  obtain ⟨Yzero,Xzero⟩ := interpolate_slots node (fun i j h => Fin.ext (Nat.cast_injective h))
    (fun i => -lam i) (fun i j h => hlam (neg_inj.mp h)) L R sample ne
    (fun i => (dist i).comp finSumFinEquiv.injective) cover
    (fun i j => V (.inl i) (.inr j)) (fun i j => V (.inr j) (.inl i)) plain weighted
  have zero : V=0 := by
    funext i j
    rcases i with i|i <;> rcases j with j|j
    · exact (core i j).2
    · exact congrFun (congrFun Yzero i) j
    · exact congrFun (congrFun Xzero j) i
    · exact lower V testV i j
  refine ⟨?_,zero⟩
  funext i j
  rcases i with i|i <;> rcases j with j|j
  · exact (core i j).1
  · simpa only [zero,Matrix.zero_apply,mul_zero] using rowU i j
  · simpa only [zero,Matrix.zero_apply,mul_zero] using colU j i
  · exact lower U testU i j

end CriticalLastSlice.HigherPencil

namespace HigherPencil

/-- A tensor annihilating the three tangent variations at each marked point
and the third variation at each exterior point detects surjectivity of their sum. -/
theorem augmented_span_of_annihilator {𝕜 I J K P Q : Type*} [Field 𝕜]
    [Fintype I] [Fintype J] [Fintype K] [Fintype P] [Fintype Q]
    (x : P → I → 𝕜) (y : P → J → 𝕜) (z : P → K → 𝕜) (x' : Q → I → 𝕜) (y' : Q → J → 𝕜)
    (detect : ∀ H : I → J → K → 𝕜,
      (∀ t i, ∑ j, ∑ k, (y t j*z t k)*H i j k=0) →
      (∀ t j, ∑ i, ∑ k, (x t i*z t k)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x t i*y t j)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x' t i*y' t j)*H i j k=0) → H=0) :
    ∀ T : I → J → K → 𝕜,
      ∃ u : P → I → 𝕜, ∃ v : P → J → 𝕜, ∃ w : P → K → 𝕜, ∃ w' : Q → K → 𝕜, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  classical
  let C := (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K)))
  let M : Matrix (I × J × K) C 𝕜
    | (i,j,k),.inl (t,h) => if h=i then y t j*z t k else 0
    | (i,j,k),.inr (.inl (t,h)) => if h=j then x t i*z t k else 0
    | (i,j,k),.inr (.inr (.inl (t,h))) => if h=k then x t i*y t j else 0
    | (i,j,k),.inr (.inr (.inr (t,h))) => if h=k then x' t i*y' t j else 0
  have no_rel (v : I × J × K → 𝕜) (hv : M.transpose.mulVec v=0) : v=0 := by
    let H (i : I) (j : J) (k : K) := v (i,j,k)
    have read (c : C) : (∑ q : I × J × K, M q c * v q)=0 := congrFun hv c
    have zero := detect H
      (fun t i => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inl (t,i)))
      (fun t j => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inr (.inl (t,j))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inl (t,k)))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inr (t,k)))))
    funext ⟨i,j,k⟩
    exact congrFun (congrFun (congrFun zero i) j) k
  have ker : LinearMap.ker M.transpose.mulVecLin=⊥ := by
    apply bot_unique
    intro u hu
    exact (Submodule.mem_bot 𝕜).mpr (no_rel u hu)
  have size := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp ker)
  change M.transpose.rank=Module.finrank 𝕜 (I × J × K → 𝕜) at size
  rw [Matrix.rank_transpose] at size
  have onto : Function.Surjective M.mulVec := LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq size)
  intro T
  obtain ⟨p,hp⟩ := onto (fun q => T q.1 q.2.1 q.2.2)
  refine ⟨fun t i => p (.inl (t,i)),fun t j => p (.inr (.inl (t,j))),
    fun t k => p (.inr (.inr (.inl (t,k)))),fun t k => p (.inr (.inr (.inr (t,k)))),?_⟩
  intro i j k
  refine (congrFun hp (i,j,k)).symm.trans ?_
  change (∑ q : (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K))), M (i,j,k) q*p q)=_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,M,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,Finset.sum_add_distrib]
  simp only [mul_assoc,mul_comm,add_assoc]

end HigherPencil

namespace HigherPencil

/-- The pencil dimension budget is equivalent to having enough exterior
labels for the lower rectangle and the paired off-diagonal slots. -/
theorem local_pencil_budget_iff {a b m r : ℕ} (hm : 2 ≤ m) (ha : m ≤ a) (hb : m ≤ b)
    (hr : m ≤ r) :
    2*(a*b-r) ≤ m*(a+b-2) ↔
      (a-m)*(b-m)+(((b-m)+(a-m))*m+1)/2 ≤ r-m := by
  let d := a-m
  let e := b-m
  change 2*(a*b-r) ≤ m*(a+b-2) ↔ d*e+((e+d)*m+1)/2 ≤ r-m
  have sa : a=m+d := by dsimp only [d]; omega
  have sb : b=m+e := by dsimp only [e]; omega
  have arms : m*(a+b-2)+2*m=m*(a+b) := calc
    _ = m*((a+b-2)+2) := by ring
    _ = m*(a+b) := by rw [show a+b-2+2=a+b by omega]
  have count : 2*(a*b)=2*(d*e)+(e+d)*m+2*m+m*(a+b-2) := calc
    _ = 2*(d*e)+(e+d)*m+m*(a+b) := by rw [sa,sb]; ring
    _ = _ := by omega
  constructor
  · intro h
    have above : a*b ≤ r+(a*b-r) := by omega
    omega
  · intro h
    by_cases le : r ≤ a*b
    · have hsub := Nat.sub_add_cancel le
      omega
    · have hsub : a*b-r=0 := by omega
      rw [hsub]
      omega

end HigherPencil

namespace HigherPencil

/-- The marked diagonal pencil and its exterior products span the primal
tangent. The exterior labels beyond the interpolation schedule carry zero factors. -/
theorem local_pencil_blocks {m d e q : ℕ} (hm : 2 ≤ m) (room : d*e+((e+d)*m+1)/2 ≤ q) :
    let A := Fin m ⊕ Fin d
    let B := Fin m ⊕ Fin e
    ∃ x : Fin m → A → ℂ, ∃ y : Fin m → B → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
    ∃ x' : Fin q → A → ℂ, ∃ y' : Fin q → B → ℂ,
    ∀ T : A → B → Fin 2 → ℂ,
      ∃ u : Fin m → A → ℂ, ∃ v : Fin m → B → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin q → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  classical
  intro A B
  let lam (t : Fin m) : ℂ := t.val
  have inject : Function.Injective lam := fun i j h => Fin.ext (Nat.cast_injective h)
  obtain ⟨X,Y,read⟩ := CriticalLastSlice.HigherPencil.product_samples (d:=d) (e:=e) hm lam inject
  let P := (Fin d × Fin e) ⊕ Fin (((e+d)*m+1)/2)
  have enough : Fintype.card P ≤ q := by simpa [P] using room
  let put : P ⊕ Fin (q-Fintype.card P) ≃ Fin q := Fintype.equivOfCardEq (by simp; omega)
  let xp (t : Fin q) : A → ℂ := (put.symm t).elim X 0
  let yp (t : Fin q) : B → ℂ := (put.symm t).elim Y 0
  let x (t : Fin m) (i : A) : ℂ := if Sum.inl t=i then 1 else 0
  let y (t : Fin m) (j : B) : ℂ := if Sum.inl t=j then 1 else 0
  let z (t : Fin m) : Fin 2 → ℂ := ![1,lam t]
  refine ⟨x,y,z,xp,yp,augmented_span_of_annihilator x y z xp yp ?_⟩
  intro H xvar yvar zvar exterior
  let U : Matrix A B ℂ := fun i j => H i j 0
  let V : Matrix A B ℂ := fun i j => H i j 1
  have diagonal (t : Fin m) (k : Fin 2) : H (.inl t) (.inl t) k = 0 := by
    simpa [A,B,x,y,mul_ite,ite_mul] using zvar t k
  have row (t : Fin m) (j : B) : U (.inl t) j+lam t*V (.inl t) j=0 := by
    simpa [A,x,z,U,V,Fin.sum_univ_two,ite_mul,Finset.sum_add_distrib] using yvar t j
  have col (t : Fin m) (i : A) : U i (.inl t)+lam t*V i (.inl t)=0 := by
    simpa [B,y,z,U,V,Fin.sum_univ_two,ite_mul,Finset.sum_add_distrib] using xvar t i
  have sampled (p : P) (k : Fin 2) : (∑ i,∑ j, X p i*Y p j*H i j k)=0 := by
    simpa only [xp,yp,Equiv.symm_apply_apply,Sum.elim_inl] using exterior (put (.inl p)) k
  obtain ⟨hu,hv⟩ := read U V (fun t => ⟨diagonal t 0,diagonal t 1⟩) row col
    (fun p => sampled p 0) (fun p => sampled p 1)
  funext i j k
  refine Fin.cases (congrFun (congrFun hu i) j) (fun h => ?_) k
  fin_cases h
  exact congrFun (congrFun hv i) j

end HigherPencil

namespace HigherPencil

/-- In actual finite coordinates a two-slice local tensor is spanned with
m full marked variations and r−m exterior third-factor variations whenever
the pencil dimension budget holds. -/
theorem local_pencil_fin {a b m r : ℕ} (hm : 2 ≤ m) (ha : m ≤ a) (hb : m ≤ b) (hr : m ≤ r)
    (budget : 2*(a*b-r) ≤ m*(a+b-2)) :
    ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
    ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
    ∀ T : Fin a → Fin b → Fin 2 → ℂ,
      ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  let ea : Fin m ⊕ Fin (a-m) ≃ Fin a := finSumFinEquiv.trans (finCongr (by omega))
  let eb : Fin m ⊕ Fin (b-m) ≃ Fin b := finSumFinEquiv.trans (finCongr (by omega))
  have room := (local_pencil_budget_iff hm ha hb hr).mp budget
  obtain ⟨x,y,z,x',y',span⟩ := local_pencil_blocks (d:=a-m) (e:=b-m) hm room
  refine ⟨fun t i => x t (ea.symm i),fun t j => y t (eb.symm j),z,
    fun t i => x' t (ea.symm i),fun t j => y' t (eb.symm j),?_⟩
  intro T
  obtain ⟨u,v,w,w',hit⟩ := span (fun i j k => T (ea i) (eb j) k)
  refine ⟨fun t i => u t (ea.symm i),fun t j => v t (eb.symm j),w,w',?_⟩
  intro i j k
  simpa only [Equiv.apply_symm_apply] using hit (ea.symm i) (eb.symm j) k

end HigherPencil

namespace CriticalHigher

/-- A two-dimensional block on any axis suffices whenever the marked points
fit and their pencil variations provide the local parameter count. The
criterion is arithmetic in the four dimensions. -/
theorem tangent_of_pencil_screen {a b n r : ℕ}
    (screen :
      let ok (u v w : ℕ) := ∃ h m, w = 2*h ∧ h*m ≤ r ∧ 2 ≤ m ∧ m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
      ok a b n ∨ ok b n a ∨ ok a n b) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  rcases screen with ⟨h,m,rfl,slots,hm,ha,hb,hr,budget⟩ |
    ⟨h,m,rfl,slots,hm,hb,hn,hr,budget⟩ | ⟨h,m,rfl,slots,hm,ha,hn,hr,budget⟩
  · exact Blocks.many_pencil_third a b h m r slots (HigherPencil.local_pencil_fin hm ha hb hr budget)
  · exact Blocks.many_pencil_first b n h m r slots (HigherPencil.local_pencil_fin hm hb hn hr budget)
  · exact Blocks.many_pencil_second a n h m r slots (HigherPencil.local_pencil_fin hm ha hn hr budget)

/-- An integer t with 2≤t≤min(a,b) gives a perfect format whenever
ab=t(h+(a+b−2)/2) in the denominator-free form below. This includes
formats for which the block axis is the only even dimension. -/
theorem perfect_pencil_format {a b h t : ℕ} (ha : 3≤a) (hab : a≤b) (order : b≤2*h)
    (ht : 2 ≤ t) (htA : t≤a) (balance : 2*(a*b)=t*(a+b+2*h-2)) :
    Arxiv.«0805.3777».IsGenericRank [a,b,2*h] (h*t) := by
  have hp : 0<h := by omega
  have den : 0<a+b+2*h-2 := by omega
  have num : a*b*(2*h)=(a+b+2*h-2)*(h*t) := by nlinarith only [congrArg (·*h) balance]
  have count : h*t=a*b*(2*h) ⌈/⌉ (a+b+2*h-2) := by
    rw [num]
    apply le_antisymm
    · exact Nat.le_of_mul_le_mul_left ((ceilDiv_le_iff_le_mul den).mp le_rfl) den
    · exact (ceilDiv_le_iff_le_mul den).mpr le_rfl
  have hr : t ≤ h*t := by
    simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ h from hp)
  have identity : 2*(a*b)=t*(a+b-2)+2*(h*t) := by
    rw [balance,show a+b+2*h-2=(a+b-2)+2*h by omega]
    ring
  have small : h*t≤a*b := by omega
  have budget : 2*(a*b-h*t)≤t*(a+b-2) := by omega
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha hab order count
  apply tangent_of_pencil_screen
  exact Or.inl ⟨h,t,rfl,le_rfl,ht,htA,htA.trans hab,hr,budget⟩

/-- Even the two unsplit axes may both be odd. Taking three marks per
pencil gives unbounded first dimensions in this rectangular family. -/
theorem odd_sides_three_marks (s t : ℕ) (ordered : 2*s+5 ≤ 6*t+3) :
    let h := (4*s+7)*t+s+2
    Arxiv.«0805.3777».IsGenericRank [2*s+5,6*t+3,2*h] (3*h) := by
  intro h
  have positive : 6*t+3 ≤ 2*h := by dsimp [h]; nlinarith
  have den : (2*s+5)+(6*t+3)+2*h-2=(2*s+5)+(6*t+3)+2*((4*s+7)*t+s+1) := by dsimp [h]; omega
  have balance : 2*((2*s+5)*(6*t+3))=3*((2*s+5)+(6*t+3)+2*h-2) := by rw [den]; ring
  simpa only [Nat.mul_comm h 3] using
    (perfect_pencil_format (a:=2*s+5) (b:=6*t+3) (h:=h) (t:=3) (by omega) ordered positive
      (by decide) (by omega) balance)

/-- For equal sides a=3(s+2), three marks in each pencil give rank 3h
at third dimension 2h, where h=a(s+1)+1. On this family the normal-space
dimension (a−1)²+1−3h is a−1, and tends to infinity. -/
theorem square_three_marks (s : ℕ) :
    let a := 3*(s+2)
    let h := a*(s+1)+1
    Arxiv.«0805.3777».IsGenericRank [a,a,2*h] (3*h) ∧ (a-1)*(a-1)+1-3*h=a-1 := by
  intro a h
  have positive : a ≤ 2*h := by dsimp [a,h]; nlinarith
  have den : a+a+2*h-2=a+a+2*(a*(s+1)) := by dsimp [h]; omega
  have balance : 2*(a*a)=3*(a+a+2*h-2) := by rw [den]; dsimp [a]; ring
  have pred : a-1=3*s+5 := by dsimp [a]; omega
  have dimension : (3*s+5)*(3*s+5)+1=3*h+(3*s+5) := by dsimp [h,a]; ring
  refine ⟨?_,by rw [pred]; omega⟩
  simpa only [Nat.mul_comm h 3] using
    (perfect_pencil_format (a:=a) (b:=a) (h:=h) (t:=3) (by dsimp [a]; omega) le_rfl
      positive (by decide) (by dsimp [a]; omega) balance)

end CriticalHigher

namespace CriticalHigher

open Set Arxiv.«0805.3777»
open scoped Topology

/-- Restricting coordinates along any injection is continuous, open and
surjective in the product topology. A local continuous section through
a chosen point keeps all its coordinates outside the image unchanged. -/
theorem coordinate_restriction_open {I J : Type*} (e : I → J) (inj : Function.Injective e) :
    let P : (J → ℂ) → I → ℂ := fun t i => t (e i)
    Continuous P ∧ IsOpenMap P ∧ Function.Surjective P := by
  classical
  intro P
  let lift (t : J → ℂ) (v : I → ℂ) (j : J) :=
    if h : ∃ i, e i=j then v (Classical.choose h) else t j
  have right (t : J → ℂ) (v : I → ℂ) : P (lift t v)=v := by
    funext i
    have hit : ∃ w, e w=e i := ⟨i,rfl⟩
    change lift t v (e i)=_
    simp only [lift,dif_pos hit,inj (Classical.choose_spec hit)]
  have through (t : J → ℂ) : lift t (P t)=t := by
    funext j
    by_cases hit : ∃ i, e i=j
    · simp only [lift,dif_pos hit,P,Classical.choose_spec hit]
    · simp only [lift,dif_neg hit]
  have cont (t : J → ℂ) : Continuous (lift t) := by
    apply continuous_pi
    intro j
    by_cases hit : ∃ i, e i=j
    · simpa only [lift,dif_pos hit] using (continuous_apply (Classical.choose hit) : Continuous (fun v : I → ℂ => v (Classical.choose hit)))
    · simpa only [lift,dif_neg hit] using (continuous_const : Continuous (fun _ : I → ℂ => t j))
  refine ⟨continuous_pi fun i => continuous_apply (e i),?_,fun v => ⟨lift 0 v,right 0 v⟩⟩
  intro U openU
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨t,ht,rfl⟩
  have inside : P t ∈ (lift t) ⁻¹' U := by
    change lift t (P t) ∈ U
    rwa [through]
  refine Filter.mem_of_superset ((openU.preimage (cont t)).mem_nhds inside) ?_
  intro v hv
  exact ⟨lift t v,hv,right t v⟩

/-- Project a rectangular complex holor onto its first n third coordinates.
The map is continuous, open and onto, and never increases ordinary CP rank. -/
theorem rank_projection_third (a b n N : ℕ) (hn : n ≤ N) :
    ∃ P : Holor ℂ [a,b,N] → Holor ℂ [a,b,n],
      Continuous P ∧ IsOpenMap P ∧ Function.Surjective P ∧ (∀ T, (P T).cprank ≤ T.cprank) ∧
      ∀ (T : Holor ℂ [a,b,N]) (i : Fin a) (j : Fin b) (k : Fin n),
        P T ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ =
        T ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons (lt_of_lt_of_le k.isLt hn) .nil))⟩ := by
  classical
  obtain ⟨small,hsmall⟩ := CriticalReduction.rectangular_indices a b n
  obtain ⟨big,hbig⟩ := CriticalReduction.rectangular_indices a b N
  let embed (q : HolorIndex [a,b,n]) := big.symm ((small q).1,(small q).2.1,Fin.castLE hn (small q).2.2)
  let P (t : Holor ℂ [a,b,N]) : Holor ℂ [a,b,n] := fun q => t (embed q)
  have at_index (i : Fin a) (j : Fin b) (k : Fin n) :
      embed (small.symm (i,j,k)) = big.symm (i,j,Fin.castLE hn k) := by simp [embed]
  have injection : Function.Injective embed := by
    intro q v he
    have equal := big.symm.injective he
    apply small.injective
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact congrArg (fun t : Fin a × Fin b × Fin N => t.1) equal
    · exact congrArg (fun t : Fin a × Fin b × Fin N => t.2.1) equal
    · exact Fin.ext (congrArg (fun t : Fin a × Fin b × Fin N => (t.2.2 : ℕ)) equal)
  obtain ⟨continuous,op,onto⟩ := coordinate_restriction_open embed injection
  refine ⟨P,continuous,op,onto,?_,?_⟩
  · intro t
    obtain ⟨x,y,z,h⟩ := CriticalReduction.sum_coordinates big hbig t t.cprank le_rfl
    let head {d : ℕ} (q : HolorIndex [d]) : Fin d := ⟨q.val.headI,by
      obtain ⟨is,hi⟩ := q
      cases hi with | cons h _ => exact h⟩
    let X (s : Fin t.cprank) : Holor ℂ [a] := fun q => x s (head q)
    let Y (s : Fin t.cprank) : Holor ℂ [b] := fun q => y s (head q)
    let Z (s : Fin t.cprank) : Holor ℂ [n] := fun q => z s (Fin.castLE hn (head q))
    let H (s : Fin t.cprank) := Holor.mul (X s) (Holor.mul (Y s) (Z s))
    have equal : P t = ∑ s, H s := by
      funext q
      obtain ⟨⟨i,j,k⟩,rfl⟩ := small.symm.surjective q
      have rep := h (big.symm (i,j,Fin.castLE hn k))
      simp only [Equiv.apply_symm_apply] at rep
      change t (embed (small.symm (i,j,k))) = _
      rw [at_index]
      refine rep.symm.trans ?_
      have value := Finset.sum_apply (M := fun _ : HolorIndex [a,b,n] => ℂ)
        (small.symm (i,j,k)) (Finset.univ : Finset (Fin t.cprank)) (fun s q => H s q)
      refine (Finset.sum_congr rfl ?_).trans value.symm
      intro s _
      rw [hsmall]
      change x s i * y s j * z s (Fin.castLE hn k) = x s i * (y s j * z s (Fin.castLE hn k))
      exact mul_assoc _ _ _
    rw [equal]
    exact Nat.find_min' _ (CriticalReduction.Dominance.tensor_sum_rank X Y Z)
  · intro t i j k
    calc
      _ = t (embed (small.symm (i,j,k))) := by rw [hsmall]
      _ = t (big.symm (i,j,Fin.castLE hn k)) := congrArg t (at_index i j k)
      _ = _ := congrArg t ((hbig i j (Fin.castLE hn k)).trans (Subtype.ext rfl))

/-- A generic upper bound descends under projection of slices, with
openness of the image providing an actual dense open set of tensors. -/
theorem project_generic_upper {a b n N r : ℕ} (hn : n ≤ N) (large : IsGenericRank [a,b,N] r) :
    ∃ U : Set (Holor ℂ [a,b,n]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  obtain ⟨P,cont,op,onto,rank,_⟩ := rank_projection_third a b n N hn
  obtain ⟨U,hU,dU,regular⟩ := large
  refine ⟨P '' U,op U hU,onto.denseRange.dense_image cont dU,?_⟩
  rintro T ⟨t,ht,rfl⟩
  exact (rank t).trans (regular t ht).le

/-- If the smaller format has the same dimension-count rank, that rank
remains generic after projection. This uses the generic rank at N alone. -/
theorem generic_rank_project {a b n N r : ℕ} (hn : n ≤ N) (den : 0 < a+b+n-2)
    (count : a*b*n ⌈/⌉ (a+b+n-2) = r) (large : IsGenericRank [a,b,N] r) :
    IsGenericRank [a,b,n] r := by
  obtain ⟨U,hU,dU,upper⟩ := project_generic_upper hn large
  by_cases zero : r=0
  · refine ⟨U,hU,dU,?_⟩
    intro T hT
    have le := upper T hT
    omega
  have cost : (a+b+n-2)*(r-1) < a*b*n := by
    by_contra! low
    have small := (ceilDiv_le_iff_le_mul den).mpr low
    rw [count] at small
    omega
  let K := closure {T : Holor ℂ [a,b,n] | T.cprank ≤ r-1}
  have lower : Dense Kᶜ := interior_eq_empty_iff_dense_compl.mp (CriticalReduction.lower_of_count a b n (r-1) cost)
  refine ⟨U ∩ Kᶜ,hU.inter isClosed_closure.isOpen_compl,dU.inter_of_isOpen_left lower hU,?_⟩
  intro T hT
  have hi := upper T hT.1
  have lo : ¬ T.cprank ≤ r-1 := fun h => hT.2 (subset_closure h)
  omega

/-- Endpoint generic rank and the ranks on the full dimension-count plateau
are equivalent whenever the endpoint belongs to the plateau. -/
theorem generic_rank_endpoint_iff {a b N r : ℕ} (den : 0 < a+b+N-2)
    (endCount : a*b*N ⌈/⌉ (a+b+N-2) = r) :
    IsGenericRank [a,b,N] r ↔ ∀ n : ℕ, n ≤ N → 0 < a+b+n-2 →
      a*b*n ⌈/⌉ (a+b+n-2) = r → IsGenericRank [a,b,n] r :=
  ⟨fun big _ hn hd count => generic_rank_project hn hd count big,
    fun all => all N le_rfl den endCount⟩

end CriticalHigher

namespace CriticalThreeTop

/-- At every width which is a multiple of h, the Cauchy condition is the
dimension count itself. This works for every d≥2, with no relative size
condition between d and h. -/
theorem divisible_level_rank (h d n : ℕ) (hh : 1≤h) (hd : 2≤d) :
    let b := h*d
    let r := h*(2*d-1)
    3≤b → b≤n → 3*b*n ⌈/⌉ (b+n+1)=r → Arxiv.«0805.3777».IsGenericRank [3,b,n] r := by
  intro b r hb order count
  have twice : 2*d-1+1=2*d := by omega
  have prod := congrArg (fun t : ℕ => h*t) twice
  have level : r+h=2*b := by dsimp [r,b]; nlinarith only [prod]
  have proper : r<3*b := by omega
  have small : b+1≤3*b-r := by omega
  have enough := (CriticalHigher.normal_budget (by omega : 0<b+1) proper small
    (show 3*b*n ⌈/⌉ (b+1+n)=r by simpa only [show b+1+n=b+n+1 by omega] using count)).1
  have cost := ((CriticalThreeQuotient.uniform_count_iff h d n hh hd enough).mp count.le)
  change (h-1)*(2*d-1) ≤ (r-n)*(d+1) at cost
  have prev := congrArg (fun t : ℕ => t*(2*d-1)) (Nat.sub_add_cancel hh)
  have cap : h*(2*d-1)+0 ≤ (r-n)*(d+1)+(2*d-1) := by nlinarith only [cost,prev]
  have wit := mixed_cauchy_tangent h d 0 (r-n) hh hd (Nat.zero_le _)
    (by simpa only [Nat.mul_zero,Nat.add_zero] using (Nat.sub_le r n)) (by
      simpa only [Nat.mul_zero,Nat.add_zero] using cap)
  dsimp only at wit
  simp only [Nat.mul_zero,Nat.add_zero] at wit
  have dimension : h*(2*d-1)-(r-n)=n := (show r-(r-n)=n by omega)
  rw [dimension] at wit
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb order _ wit
  rw [show 3+b+n-2=b+n+1 by omega]
  exact count.symm

/-- A two-parameter family has integral dimension count. If d is odd and
k is even, all three axes are odd. For instance d=3 and k=10 gives a
3 × 123 × 155 tensor of generic complex CP rank 205. -/
theorem perfect_cauchy_family (d k : ℕ) (hd : 3≤d) :
    let h := (d+1)*k+1
    let b := h*d
    let n := (2*d-1)*(d*k+1)
    Arxiv.«0805.3777».IsGenericRank [3,b,n] (h*(2*d-1)) := by
  intro h b n
  have hh : 1≤h := by dsimp [h]; omega
  have first : d≤b := by
    simpa only [one_mul] using Nat.mul_le_mul_right d hh
  have width : b+1=(d+1)*(d*k+1) := by dsimp [b,h]; ring
  have next : d+1≤2*d-1 := by omega
  have ordered : b+1≤n := by
    rw [width]
    exact Nat.mul_le_mul_right _ next
  have denom : b+n+1=3*d*(d*k+1) := by
    rw [show b+n+1=(b+1)+n by omega,width]
    change (d+1)*(d*k+1)+(2*d-1)*(d*k+1)=_
    rw [←Nat.add_mul,show (d+1)+(2*d-1)=3*d by omega]
  have positive : 0<b+n+1 := by omega
  have numerator : 3*b*n=(b+n+1)*(h*(2*d-1)) := by rw [denom]; dsimp [b,n]; ring
  apply divisible_level_rank h d n hh (by omega) (hd.trans first) (by omega)
  change 3*b*n ⌈/⌉ (b+n+1)=h*(2*d-1)
  rw [numerator]
  apply le_antisymm
  · exact (ceilDiv_le_iff_le_mul positive).mpr le_rfl
  · exact Nat.le_of_mul_le_mul_left ((ceilDiv_le_iff_le_mul positive).mp le_rfl) positive

end CriticalThreeTop

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R3

open Arxiv.«0805.3777»

/-- The three-slice family whose third dimension exceeds its middle dimension by two. -/
def H1 : Prop :=
  ∀ b : ℕ, 4 ≤ b →
    IsGenericRank [3,b,b+2] (3*b*(b+2) ⌈/⌉ (3+b+(b+2)-2))

/-- On each three-slice rank level there are finitely many residual middle
widths, and at most one third dimension for each such width. -/
def H2 : Prop :=
  ∀ b h : ℕ, 3 ≤ b → 3 ≤ h → 2*h ≤ b → ¬h∣b → b < 3*h*(h-1)-h+1 →
    let r := 2*b-h
    let N := min (2*(b-1)) (r*(b+1)/(b+h))
    b < N → N ≠ b+2 →
    3*b*N ⌈/⌉ (b+N+1) = r →
    (b < h^2 ∨ N=2*b-3*h+3 ∨ N=2*b-3*h+4) →
    let pencil (u v w : ℕ) := ∃ k m : ℕ, w=2*k ∧ k*m ≤ r ∧ 2 ≤ m ∧
      m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
    ¬(pencil 3 b N ∨ pencil b N 3 ∨ pencil 3 N b) →
    ¬(N ≤ r ∧ r+1 ≤ (r-N+2)*(b/h)+(r-N)) →
    IsGenericRank [3,b,N] r

/-- For larger first dimensions, only the maximum admissible third dimension
on each unfilled rank level outside the three pencil tests remains. -/
def H3 : Prop :=
  ∀ a b r : ℕ, 4 ≤ a → a ≤ b → 0 < r → r < (a-1)*(b-1) →
    let N := min ((a-1)*(b-1)) (r*(a+b-2)/(a*b-r))
    b ≤ N → a*b*N ⌈/⌉ (a+b+N-2)=r →
    let pencil (u v w : ℕ) := ∃ k m : ℕ, w=2*k ∧ k*m ≤ r ∧ 2 ≤ m ∧
      m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
    ¬(pencil a b N ∨ pencil b N a ∨ pencil a N b) →
    IsGenericRank [a,b,N] r

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R3

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R3

open Arxiv.«0805.3777»

/-- Clipping an attained rank interval to the critical upper bound preserves
its rank and gives its largest admissible third dimension. -/
theorem clipped_endpoint {A d w n r : ℕ} (hd : 0 < d) (hr : 0 < r) (proper : r < A)
    (inside : n ≤ w) (count : A*n ⌈/⌉ (d+n)=r) :
    let N := min w (r*d/(A-r))
    n ≤ N ∧ N ≤ w ∧ A*N ⌈/⌉ (d+N)=r := by
  intro N
  have interval := (CriticalHigher.count_interval hd hr proper).mp count
  have reach : n ≤ N := le_min inside interval.2
  exact ⟨reach,min_le_left _ _,(CriticalHigher.count_interval hd hr proper).mpr
    ⟨interval.1.trans_le reach,min_le_right _ _⟩⟩

private theorem even_square_count (k : ℕ) :
    3*(2*k)*(2*k) ⌈/⌉ (2*k+2*k+1)=3*k := by
  let q := 3*(2*k)*(2*k) ⌈/⌉ (2*k+2*k+1)
  have pos : 0 < 2*k+2*k+1 := by omega
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul pos).mpr
    nlinarith
  · by_contra! h
    have cap : 3*(2*k)*(2*k) ≤ (2*k+2*k+1)*q := (ceilDiv_le_iff_le_mul pos).mp le_rfl
    have ahead := Nat.mul_le_mul_left (2*k+2*k+1) (show q+1 ≤ 3*k by dsimp only [q]; omega)
    nlinarith only [cap,ahead]

private theorem three_endpoint (gap : H1) (residual : H2) {b h r N : ℕ}
    (hb : 3 ≤ b) (hh : 3 ≤ h) (hr : 0 < r) (rank : r+h=2*b)
    (endpt : N=min (2*(b-1)) (r*(b+1)/(b+h))) (ord : b ≤ N)
    (admissible : ∀ p : ℕ, (3,b,N) ≠ (3,2*p+1,2*p+1))
    (count : 3*b*N ⌈/⌉ (b+N+1)=r)
    (outside : let pencil (u v w : ℕ) := ∃ k m : ℕ, w=2*k ∧ k*m ≤ r ∧ 2 ≤ m ∧
      m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
      ¬(pencil 3 b N ∨ pencil b N 3 ∨ pencil 3 N b)) :
    IsGenericRank [3,b,N] r := by
  have value : r=2*b-h := by omega
  rw [value] at hr rank endpt count outside ⊢
  have upper : N ≤ 2*(b-1) := endpt ▸ min_le_left _ _
  by_cases gap2 : N=b+2
  · have four : 4 ≤ b := by omega
    have hit := gap b four
    rw [← gap2] at hit
    simpa only [show 3+b+N-2=b+N+1 by omega,count] using hit
  by_cases large : 3*h*(h-1)-h+1 ≤ b
  · exact CriticalThreeTop.fixed_level_tail_rank h b N hh large ord count
  by_cases covered : h^2 ≤ b ∧ N ≤ 2*b-3*h+2
  · exact CriticalThreeTop.rank_below_endpoint h b N hh covered.1 ord covered.2 count
  have strict : b < N := by
    by_contra! stop
    have same : N=b := by omega
    rcases Nat.even_or_odd b with even | ⟨p,odd⟩
    · obtain ⟨k,hk⟩ := even
      have double : b=2*k := by omega
      have cc := even_square_count k
      rw [← double] at cc
      have target : 2*b-h=3*k := count.symm.trans (by simpa only [same] using cc)
      exact outside (Or.inl ⟨k,3,same.trans double,by omega,by decide,le_rfl,hb,by omega,by omega⟩)
    · exact admissible p (by rw [same,odd])
  have width := CriticalThreeTop.strict_width_at_least_twice (by omega) strict count
  by_cases divisor : h ∣ b
  · obtain ⟨d,product⟩ := divisor
    have dh : 2 ≤ d := by
      have twice : h*2 ≤ h*d := by simpa only [Nat.mul_comm h 2,←product] using width
      exact Nat.le_of_mul_le_mul_left twice (by omega)
    have fix : 2*d-1+1=2*d := by omega
    have identity := congrArg (fun z : ℕ => h*z) fix
    have equal_rank : h*(2*d-1)=2*b-h := by nlinarith only [product,rank,identity]
    have hit := CriticalThreeTop.divisible_level_rank h d N (by omega) dh
    dsimp only at hit
    rw [← product,equal_rank] at hit
    exact hit hb ord count
  by_cases cauchy : N ≤ 2*b-h ∧ 2*b-h+1 ≤ (2*b-h-N+2)*(b/h)+(2*b-h-N)
  · apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb ord _
      (CriticalThreeTop.tangent_of_cauchy_capacity b N (2*b-h) h (by omega)
        width cauchy.1 (by omega) cauchy.2)
    simpa only [show 3+b+N-2=b+N+1 by omega] using count.symm
  have small : b < h^2 ∨ N=2*b-3*h+3 ∨ N=2*b-3*h+4 := by
    by_cases full : h^2 ≤ b
    · exact Or.inr (CriticalThreeTop.residual_sizes hh full (by omega) count).2
    · exact Or.inl (by omega)
  have rem := residual b h hb hh width divisor (by omega)
  dsimp only at rem
  rw [← endpt] at rem
  exact rem strict gap2 count small outside cauchy

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«0805.3777».isGenericRank_of_le_critical := by
  classical
  intro gap three larger a b n ha hab ordered critical exception
  let r := a*b*n ⌈/⌉ (a+b+n-2)
  change IsGenericRank [a,b,n] r
  by_cases gap2 : a=3 ∧ n=b+2
  · obtain ⟨rfl,rfl⟩ := gap2
    exact gap b (by change b+2 ≤ 2*(b-1) at critical; omega)
  let w := (a-1)*(b-1)
  by_cases high : w ≤ r
  · exact CriticalPlateau.Proved.generic_rank_at_ceiling ha hab ordered (exception 1) rfl critical high
  have proper : r < a*b := by
    have smaller : (a-1)*(b-1) < a*b :=
      (Nat.mul_le_mul_left (a-1) (Nat.sub_le b 1)).trans_lt
        (Nat.mul_lt_mul_of_pos_right (by omega : a-1<a) (by omega : 0<b))
    change ¬ (a-1)*(b-1) ≤ r at high
    omega
  have den : 0 < a+b+n-2 := by omega
  have positive : 0 < r := by
    by_contra! bad
    have h := (ceilDiv_le_iff_le_mul den).mp (show r ≤ 0 by omega)
    have nonzero : 0 < a*b*n := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    change a*b*n ≤ (a+b+n-2)*0 at h
    omega
  let N := min w (r*(a+b-2)/(a*b-r))
  obtain ⟨reach,inside,atN⟩ := clipped_endpoint (A:=a*b) (d:=a+b-2) (w:=w) (n:=n) (r:=r)
    (by omega) positive proper critical (by rw [show a+b-2+n=a+b+n-2 by omega])
  change n ≤ N at reach
  change N ≤ w at inside
  change a*b*N ⌈/⌉ (a+b-2+N)=r at atN
  rw [show a+b-2+N=a+b+N-2 by omega] at atN
  have orderN : b ≤ N := ordered.trans reach
  apply CriticalHigher.generic_rank_project reach den rfl
  let pencil (u v t : ℕ) := ∃ k m : ℕ, t=2*k ∧ k*m ≤ r ∧ 2 ≤ m ∧
    m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
  by_cases usePencil : pencil a b N ∨ pencil b N a ∨ pencil a N b
  · exact CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha hab orderN atN.symm
      (CriticalHigher.tangent_of_pencil_screen usePencil)
  by_cases first : a=3
  · subst a
    let h := 2*b-r
    have small : r < 2*(b-1) := by
      change ¬ 2*(b-1) ≤ r at high
      omega
    have level : r+h=2*b := by dsimp only [h]; omega
    have hh : 3 ≤ h := by omega
    have clipped : N=min (2*(b-1)) (r*(b+1)/(b+h)) := by
      dsimp only [N,w]
      rw [show 3+b-2=b+1 by omega,show 3*b-r=b+h by omega]
    have regular (p : ℕ) : (3,b,N) ≠ (3,2*p+1,2*p+1) := by
      intro eq
      have bval := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) eq
      have nval := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) eq
      change b=2*p+1 at bval
      change N=2*p+1 at nval
      exact exception p (by rw [bval,show n=2*p+1 by omega])
    apply three_endpoint gap three hab hh positive level clipped orderN regular _ usePencil
    simpa only [show 3+b+N-2=b+N+1 by omega] using atN
  · exact larger a b r (by omega) hab positive (by change r < w; omega) orderN atN usePencil

theorem gap_two_of_original (original : type_of% @Arxiv.«0805.3777».isGenericRank_of_le_critical) : H1 := by
  intro b hb
  apply original (by decide) (by omega) (by omega) (by change b+2 ≤ 2*(b-1); omega)
  intro p eq
  have one := congrArg (fun s : ℕ × ℕ × ℕ => s.2.1) eq
  have two := congrArg (fun s : ℕ × ℕ × ℕ => s.2.2) eq
  change b=2*p+1 at one
  change b+2=2*p+1 at two
  omega

theorem three_of_original (original : type_of% @Arxiv.«0805.3777».isGenericRank_of_le_critical) : H2 := by
  intro b h hb _ _ _ _ r N ord _ count _ pencil _ _
  rw [← count,← show 3+b+N-2=b+N+1 by omega]
  apply original (by decide) hb ord.le (min_le_left _ _)
  intro p eq
  have one : b=2*p+1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) eq
  have two : N=2*p+1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) eq
  omega

theorem larger_of_original (original : type_of% @Arxiv.«0805.3777».isGenericRank_of_le_critical) : H3 := by
  intro a b r ha hab _ _ N ord count pencil _
  rw [← count]
  apply original (by omega) hab ord (min_le_left _ _)
  intro p eq
  have first : a=3 := congrArg Prod.fst eq
  omega

/-- The three residual endpoint families are jointly equivalent to Friedland's original conjecture. -/
theorem equivalent : H1 ∧ H2 ∧ H3 ↔ type_of% @Arxiv.«0805.3777».isGenericRank_of_le_critical :=
  ⟨fun h => main h.1 h.2.1 h.2.2,
   fun original => ⟨gap_two_of_original original,three_of_original original,larger_of_original original⟩⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R3
