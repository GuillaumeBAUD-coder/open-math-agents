import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! A bounded integer tangent test for Friedland's critical-format conjecture.

In format (a,b,c), a single full-row-rank tangent matrix suffices at the
rank predicted by dimension count. Each entry is quadratic in the factor
coordinates. A full-row-rank specialization gives a determinant polynomial
of total degree at most 2abc. Its nonvanishing can be witnessed on the
integer grid from zero through 2abc in each coordinate. The reduction
proves these bounds, the generic upper bound from tangent spanning, and
the matching dimension lower bound.

The first geometric target is the entire five-slice family (5,m,m). The
second covers the remaining critical formats with the stated exceptions.
See [Friedland, Conjecture 5.1](https://arxiv.org/abs/0805.3777).
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

section FiveSquare

/-- The square-ended, five-slice family: bounded integer factor vectors
at the predicted rank whose tangent spaces span all tensor coordinates. -/
def H1 : Prop :=
  ∀ m : ℕ, 5 ≤ m →
    let r := 5*m*m ⌈/⌉ (5+m+m-2)
    let D := 2*(5*m*m)+1
    ∃ x : Fin r → Fin 5 → Fin D, ∃ y z : Fin r → Fin m → Fin D,
      ∀ T : Fin 5 → Fin m → Fin m → ℂ, ∃ u : Fin r → Fin 5 → ℂ, ∃ v w : Fin r → Fin m → ℂ,
        ∀ i j k, T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

end FiveSquare

section OtherCriticalFormats

/-- The corresponding bounded tangent test on every other admissible format. -/
def H2 : Prop :=
  ∀ a b c : ℕ, 3 ≤ a → a ≤ b → b ≤ c → c ≤ (a-1)*(b-1) →
    (∀ p : ℕ, (a,b,c) ≠ (3,2*p+1,2*p+1)) → (a ≠ 5 ∨ b ≠ c) →
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    let D := 2*(a*b*c)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

end OtherCriticalFormats

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

theorem main : H1 → H2 → type_of% @Arxiv.«0805.3777».isGenericRank_of_le_critical := by
  intro h₁ h₂ a b c ha hab hbc hcrit hexc
  apply generic_of_bounded a b c ha hab hbc
  by_cases h5 : a=5 ∧ b=c
  · obtain ⟨ha5,hbc'⟩ := h5
    subst a
    subst c
    exact h₁ b hab
  · exact h₂ a b c ha hab hbc hcrit hexc (by
      by_cases h : a=5
      · exact Or.inr (fun he => h5 ⟨h,he⟩)
      · exact Or.inl h)

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1
