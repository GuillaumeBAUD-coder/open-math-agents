import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Problem: Generic and maximal rank of 3-tensors — isGenericRank of eq critical
-- Upstream: formal-conjectures FormalConjectures/Arxiv/0805.3777/TensorRank.lean:263 (declaration Arxiv.«0805.3777».isGenericRank_of_eq_critical)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Reused: the namespaces CritRank.Dimension and CritRank.Dominance are copied, with the
-- namespace renamed, from the merged proof proofs/Arxiv.0805.3777.isGenericRank_four.lean by
-- mattdorman (PR #2988): the dimension count `lower_of_count` and the tangent-map upper bound
-- `upper_of_spans`.

/-! Generic rank at the critical boundary.

Write the format as `(p+1, q+1, p*q)`. The dimension count `lower_of_count` shows that the tensors
of rank at most `p*q` form a nowhere dense set, because `p + q + p*q` parameters per term is less
than `(p+1)*(q+1)`.

For the upper bound take the `p*q + 1` points `a_t = (t^i)`, `b_t = (t^(p*j))` with third factors
the basis vectors, and zero for the last point. The tangent map is onto slice by slice. For slice
`k`, a form `F(x, y) = ∑ P i j x^i y^j` orthogonal to the tangent space vanishes on the lines
`x = k` and `y = k^p`, so it factors as `(x - k)(y - k^p) G(x, y)`, with `G` of bidegree
`(p-1, q-1)`. It also vanishes at every point `(t, t^p)`. Then `G(s, s^p)` is a polynomial of
degree below `p*q` with `p*q` roots, and its coefficients are those of `G`, so `G = 0`. This is
Terracini's lemma for the configuration. See [Friedland, Corollary 6.4](https://arxiv.org/abs/0805.3777).
-/

namespace CritRank

open Arxiv.«0805.3777» Set Filter
open scoped Topology

namespace Dimension

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

def index_cons_equiv (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds where
  toFun
    | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
    | ⟨[], h⟩ => nomatch h
  invFun q := ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => cases h
    | cons i is => rfl
  right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl

def vector_index_equiv (n : ℕ) : HolorIndex [n] ≃ Fin n where
  toFun i := ((index_cons_equiv n []) i).1
  invFun i := ⟨[i.val], .cons i.isLt .nil⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases h with
    | cons _ h => cases h; rfl
  right_inv := by intro i; rfl

def indexEquiv (d e f : ℕ) : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f :=
  (index_cons_equiv d [e,f]).trans (Equiv.prodCongr (Equiv.refl _)
    ((index_cons_equiv e [f]).trans (Equiv.prodCongr (Equiv.refl _) (vector_index_equiv f))))

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

/-- Absorb the trailing scalar of a simple tensor into the last vector. -/
lemma simple_coordinates {d e f : ℕ} {T : Holor ℂ [d,e,f]} (h : Holor.CPRankMax1 T) :
    ∃ (a : Fin d → ℂ) (b : Fin e → ℂ) (c : Fin f → ℂ),
      ∀ i j k, T ((indexEquiv d e f).symm (i,j,k)) = a i * b j * c k := by
  cases h with
  | cons a yz hyz =>
    cases hyz with
    | cons b zs hzs =>
      cases hzs with
      | cons c z hz =>
        refine ⟨fun i => a ((vector_index_equiv d).symm i),
          fun j => b ((vector_index_equiv e).symm j),
          fun k => c ((vector_index_equiv f).symm k) * z ⟨[], .nil⟩, ?_⟩
        intro i j k
        change a _ * (b _ * (c _ * z _)) = a _ * b _ * (c _ * z _)
        rw [mul_assoc]
        rfl

abbrev Raw (d e f r : ℕ) := Fin r × (Fin (d+1) ⊕ (Fin (e+1) ⊕ Fin f))
abbrev Chart (d e f r : ℕ) := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))

noncomputable def rawCoordinate (d e f r : ℕ) (q : HolorIndex [d+1,e+1,f]) :
    MvPolynomial (Raw d e f r) ℂ :=
  let v := indexEquiv (d+1) (e+1) f q
  ∑ t : Fin r, MvPolynomial.X (t, Sum.inl v.1) * MvPolynomial.X (t, Sum.inr (Sum.inl v.2.1)) *
    MvPolynomial.X (t, Sum.inr (Sum.inr v.2.2))

noncomputable def chartCoordinate (d e f r : ℕ) (q : HolorIndex [d+1,e+1,f]) :
    MvPolynomial (Chart d e f r) ℂ :=
  let v := indexEquiv (d+1) (e+1) f q
  ∑ t : Fin r, Fin.cases 1 (fun i => MvPolynomial.X (t, Sum.inl i)) v.1 *
    Fin.cases 1 (fun j => MvPolynomial.X (t, Sum.inr (Sum.inl j))) v.2.1 *
    MvPolynomial.X (t, Sum.inr (Sum.inr v.2.2))

/-- Normalize the first coordinates of the first two vectors of each term. -/
lemma normalize (d e f r : ℕ) (x : Raw d e f r → ℂ) (hx : ∀ i, x i ≠ 0) :
    ∃ y : Chart d e f r → ℂ, ∀ q,
      MvPolynomial.eval x (rawCoordinate d e f r q) = MvPolynomial.eval y (chartCoordinate d e f r q) := by
  classical
  let y : Chart d e f r → ℂ := fun (t,s) => match s with
    | .inl i => x (t,.inl i.succ) / x (t,.inl 0)
    | .inr (.inl j) => x (t,.inr (.inl j.succ)) / x (t,.inr (.inl 0))
    | .inr (.inr k) => x (t,.inr (.inr k)) * x (t,.inl 0) * x (t,.inr (.inl 0))
  refine ⟨y,?_⟩
  intro q
  simp only [rawCoordinate,chartCoordinate,map_sum,map_mul,MvPolynomial.eval_X]
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

lemma representation (d e f r : ℕ) (T : Holor ℂ [d+1,e+1,f]) (hr : T.cprank ≤ r) :
    ∃ x : Raw d e f r → ℂ, ∀ q, MvPolynomial.eval x (rawCoordinate d e f r q) = T q := by
  classical
  obtain ⟨u,hu,hT⟩ := finite_sum_of_simple (decomposition_of_rank_bound T r hr)
  choose a b c habc using fun t => simple_coordinates (hu t)
  let x : Raw d e f r → ℂ := fun (t,s) => match s with
    | .inl i => a t i
    | .inr (.inl j) => b t j
    | .inr (.inr k) => c t k
  refine ⟨x,?_⟩
  intro q
  let v := indexEquiv (d+1) (e+1) f q
  have term (t : Fin r) : u t q = a t v.1 * b t v.2.1 * c t v.2.2 := by
    have ht := habc t v.1 v.2.1 v.2.2
    change u t ((indexEquiv (d+1) (e+1) f).symm v) = _ at ht
    simpa only [v,Equiv.symm_apply_apply] using ht
  have hcoord : (∑ t : Fin r, u t q) = T q := by
    have eqAt := Finset.sum_apply (M := fun _ : HolorIndex [d+1,e+1,f] => ℂ) q
      (Finset.univ : Finset (Fin r)) (fun t => fun v => u t v)
    exact eqAt.symm.trans (congrFun hT q)
  calc
    _ = ∑ t : Fin r, a t v.1 * b t v.2.1 * c t v.2.2 := by simp [rawCoordinate,v,x]
    _ = ∑ t : Fin r, u t q := Finset.sum_congr rfl fun t _ => (term t).symm
    _ = T q := hcoord

/-- Counting the free coordinates of the normalized chart bounds the rank for
every rectangular format. -/
theorem lower_of_count (a b c r : ℕ) (hcount : (a+b+c-2)*r < a*b*c) :
    interior (closure {T : Holor ℂ [a,b,c] | T.cprank ≤ r}) = ∅ := by
  classical
  obtain _|d := a
  · simp at hcount
  obtain _|e := b
  · simp at hcount
  let _ : Fintype (HolorIndex [d+1,e+1,c]) :=
    Fintype.ofEquiv _ (indexEquiv (d+1) (e+1) c).symm
  have hd : Fintype.card (Chart d e c r) < Fintype.card (HolorIndex [d+1,e+1,c]) := by
    rw [Fintype.card_congr (indexEquiv (d+1) (e+1) c)]
    simp only [Chart,Fintype.card_prod,Fintype.card_fin,Fintype.card_sum]
    have h : d.succ+e.succ+c-2 = d+(e+c) := by omega
    simpa only [h,Nat.mul_comm (d+(e+c)) r,Nat.mul_assoc,Nat.succ_eq_add_one] using hcount
  obtain ⟨P,hP,hzero⟩ := generic_chart_relation hd (chartCoordinate d e c r)
    (rawCoordinate d e c r) (normalize d e c r)
  let Z := {T : Holor ℂ [d+1,e+1,c] | MvPolynomial.eval T P = 0}
  have hclosed : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
  have hsub : {T : Holor ℂ [d+1,e+1,c] | T.cprank ≤ r} ⊆ Z := by
    intro T hT
    obtain ⟨x,hx⟩ := representation d e c r T hT
    have he : (fun j => MvPolynomial.eval x (rawCoordinate d e c r j)) = T := funext hx
    change MvPolynomial.eval T P = 0
    simpa only [he] using hzero x
  have hempty : interior Z = ∅ := interior_polynomial_zero_locus P hP
  apply Set.subset_empty_iff.mp
  simpa only [hempty] using interior_mono (closure_minimal hsub hclosed)

end Dimension

end CritRank

namespace CritRank.Dominance

open Set Filter
open CritRank.Dimension (interior_polynomial_zero_locus eval_substitution index_cons_equiv)
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

def index_nil_equiv : HolorIndex [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], .nil⟩
  left_inv := by rintro ⟨l, h⟩; cases h; rfl
  right_inv := by intro x; cases x; rfl

lemma finite_index (ds : List ℕ) : Finite (HolorIndex ds) := by
  induction ds with
  | nil => exact Finite.of_equiv Unit index_nil_equiv.symm
  | cons n ds ih =>
    let _ : Finite (HolorIndex ds) := ih
    exact Finite.of_equiv (Fin n × HolorIndex ds) (index_cons_equiv n ds).symm

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

def point {d e f : ℕ} (i : Fin d) (j : Fin e) (k : Fin f) : HolorIndex [d,e,f] :=
  ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩

lemma point_surjective {d e f : ℕ} (z : HolorIndex [d,e,f]) :
    ∃ i j k, z = point i j k := by
  obtain ⟨⟨i,z⟩,rfl⟩ := (index_cons_equiv d [e,f]).symm.surjective z
  obtain ⟨⟨j,z⟩,rfl⟩ := (index_cons_equiv e [f]).symm.surjective z
  obtain ⟨⟨k,z⟩,rfl⟩ := (index_cons_equiv f []).symm.surjective z
  obtain ⟨⟨⟩,rfl⟩ := index_nil_equiv.symm.surjective z
  exact ⟨i,j,k,rfl⟩

abbrev Coordinate (d e f : ℕ) := HolorIndex [d,e,f]
abbrev Parameter (d e f r : ℕ) := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))

def entry {n : ℕ} (i : HolorIndex [n]) : Fin n := (index_cons_equiv n [] i).1

def first {d e f r : ℕ} (t : Fin r) (z : Coordinate d e f) : Parameter d e f r :=
  (t, Sum.inl (entry (HolorIndex.take (ds₁ := [d]) (ds₂ := [e,f]) z)))

def second {d e f r : ℕ} (t : Fin r) (z : Coordinate d e f) : Parameter d e f r :=
  (t, Sum.inr (.inl (entry (HolorIndex.take (ds₁ := [e]) (ds₂ := [f])
    (HolorIndex.drop (ds₁ := [d]) (ds₂ := [e,f]) z)))))

def third {d e f r : ℕ} (t : Fin r) (z : Coordinate d e f) : Parameter d e f r :=
  (t, Sum.inr (.inr (entry (HolorIndex.drop (ds₁ := [e]) (ds₂ := [f])
    (HolorIndex.drop (ds₁ := [d]) (ds₂ := [e,f]) z)))))

def pack {d e f r : ℕ} (a : Fin r → Fin d → ℂ) (b : Fin r → Fin e → ℂ)
    (c : Fin r → Fin f → ℂ) (q : Parameter d e f r) : ℂ :=
  q.2.elim (a q.1) (Sum.elim (b q.1) (c q.1))

/-- The tangent map of the sum of r simple tensors is onto at one choice
of the factors. The three factor dimensions are independent. -/
def TangentSpans (d e f r : ℕ) : Prop :=
  ∃ a : Fin r → Fin d → ℂ, ∃ b : Fin r → Fin e → ℂ, ∃ c : Fin r → Fin f → ℂ,
    ∀ T : Fin d → Fin e → Fin f → ℂ, ∃ u : Fin r → Fin d → ℂ, ∃ v : Fin r → Fin e → ℂ,
      ∃ w : Fin r → Fin f → ℂ, ∀ i j k, T i j k = ∑ t, (u t i * (b t j * c t k) +
        a t i * (v t j * c t k) + a t i * (b t j * w t k))

open Arxiv.«0805.3777» in
/-- A spanning tangent configuration gives a dense open set of tensors
of CP rank at most r in a rectangular complex tensor space. -/
theorem upper_of_spans {d e f r : ℕ} (hs : TangentSpans d e f r) :
    ∃ U : Set (Holor ℂ [d,e,f]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  classical
  obtain ⟨a,b,c,hspan⟩ := hs
  let _ : Finite (Coordinate d e f) := finite_index _
  let _ : Fintype (Coordinate d e f) := Fintype.ofFinite _
  let φ (x : Parameter d e f r → ℂ) (j : Coordinate d e f) :=
    ∑ t : Fin r, x (first t j) * (x (second t j) * x (third t j))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply trilinear_image_has_interior first second third (pack a b c)
    intro y
    obtain ⟨u,v,w,h⟩ := hspan fun i j k => y (point i j k)
    refine ⟨pack u v w, ?_⟩
    intro z
    obtain ⟨i,j,k,rfl⟩ := point_surjective z
    exact h i j k
  let F (j : Coordinate d e f) : MvPolynomial (Parameter d e f r) ℂ :=
    ∑ t : Fin r, MvPolynomial.X (first t j) *
      (MvPolynomial.X (second t j) * MvPolynomial.X (third t j))
  have he : (fun x : Parameter d e f r → ℂ => fun j => MvPolynomial.eval x (F j)) = φ := by
    funext x j
    simp [F, φ]
  have hd := dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ), isOpen_interior, hd, ?_⟩
  intro T hT
  obtain ⟨x,rfl⟩ := interior_subset hT
  let xa (t : Fin r) (i : HolorIndex [d]) := x (t, Sum.inl (entry i))
  let xb (t : Fin r) (j : HolorIndex [e]) := x (t, Sum.inr (.inl (entry j)))
  let xc (t : Fin r) (k : HolorIndex [f]) := x (t, Sum.inr (.inr (entry k)))
  have hx : (φ x : Holor ℂ [d,e,f]) = ∑ t, Holor.mul (xa t) (Holor.mul (xb t) (xc t)) := by
    funext j
    rw [eval_holor_sum]
    rfl
  rw [hx]
  exact Nat.find_min' _ (tensor_sum_rank xa xb xc)

end CritRank.Dominance

namespace CritRank.Terracini

open Finset

/-- Coefficients are recovered from the values of `∑ c i j * s ^ (i + p * j)`. -/
lemma coeff_vanish (p q : ℕ) (c : ℕ → ℕ → ℂ) (S : Finset ℂ) (hS : p * q ≤ S.card)
    (h : ∀ s ∈ S, ∑ i ∈ range p, ∑ j ∈ range q, c i j * s ^ (i + p * j) = 0) :
    ∀ i < p, ∀ j < q, c i j = 0 := by
  intro i hi j hj
  classical
  let g : Polynomial ℂ := ∑ a ∈ range p, ∑ b ∈ range q,
    Polynomial.C (c a b) * Polynomial.X ^ (a + p * b)
  have hdeg : g.natDegree < S.card := by
    have hle : g.natDegree ≤ p * q - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro a ha
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro b hb
      refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      rw [mem_range] at ha hb
      have : p * (b + 1) ≤ p * q := Nat.mul_le_mul_left p hb
      rw [Nat.mul_succ] at this
      omega
    have hpq : 0 < p * q := Nat.mul_pos (by omega) (by omega)
    omega
  have hg : g = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g S _ hdeg
    intro s hs
    simpa [g, Polynomial.eval_finsetSum] using h s hs
  have hcoeff : g.coeff (i + p * j) = c i j := by
    simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single_of_mem i (mem_range.mpr hi)]
    · rw [Finset.sum_eq_single_of_mem j (mem_range.mpr hj)]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro he
        apply hb
        have hp : 0 < p := by omega
        have := Nat.eq_of_mul_eq_mul_left hp (by omega : p * b = p * j)
        exact this
    · intro a ha hai
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro he
      apply hai
      have h1 := congrArg (· % p) he
      simp only [Nat.add_mul_mod_self_left] at h1
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (mem_range.mp ha)] at h1
      exact h1.symm
  rw [← hcoeff, hg, Polynomial.coeff_zero]

/-- The coefficients of the quotient by `(x - x0) * (y - y0)`. -/
def tau (m n : ℕ) (P : ℕ → ℕ → ℂ) (x0 y0 : ℂ) (i j : ℕ) : ℂ :=
  ∑ a ∈ range m, ∑ b ∈ range n,
    if i < a ∧ j < b then P a b * x0 ^ (a - 1 - i) * y0 ^ (b - 1 - j) else 0

lemma geom_range (m a : ℕ) (ha : a < m) (x x0 : ℂ) :
    ∑ i ∈ range (m - 1), (if i < a then x ^ i * x0 ^ (a - 1 - i) else 0) =
      ∑ i ∈ range a, x ^ i * x0 ^ (a - 1 - i) := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

lemma tau_expand (m n : ℕ) (P : ℕ → ℕ → ℂ) (x0 y0 x y : ℂ) :
    ∑ i ∈ range (m - 1), ∑ j ∈ range (n - 1), tau m n P x0 y0 i j * x ^ i * y ^ j =
      ∑ a ∈ range m, ∑ b ∈ range n, P a b * (∑ i ∈ range a, x ^ i * x0 ^ (a - 1 - i)) *
        (∑ j ∈ range b, y ^ j * y0 ^ (b - 1 - j)) := by
  have hterm : ∀ a ∈ range m, ∀ b ∈ range n,
      P a b * (∑ i ∈ range a, x ^ i * x0 ^ (a - 1 - i)) *
        (∑ j ∈ range b, y ^ j * y0 ^ (b - 1 - j)) =
      ∑ i ∈ range (m - 1), ∑ j ∈ range (n - 1),
        (if i < a ∧ j < b then P a b * x0 ^ (a - 1 - i) * y0 ^ (b - 1 - j) else 0) *
          x ^ i * y ^ j := by
    intro a ha b hb
    rw [← geom_range m a (mem_range.mp ha), ← geom_range n b (mem_range.mp hb),
      mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : i < a <;> by_cases hj : j < b <;> simp [hi, hj]; ring
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hterm a ha b hb))]
  simp only [tau, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

lemma factor (m n : ℕ) (P : ℕ → ℕ → ℂ) (x0 y0 : ℂ)
    (hR : ∀ b < n, ∑ a ∈ range m, P a b * x0 ^ a = 0)
    (hC : ∀ a < m, ∑ b ∈ range n, P a b * y0 ^ b = 0) (x y : ℂ) :
    ∑ a ∈ range m, ∑ b ∈ range n, P a b * x ^ a * y ^ b =
      (x - x0) * (y - y0) *
        ∑ i ∈ range (m - 1), ∑ j ∈ range (n - 1), tau m n P x0 y0 i j * x ^ i * y ^ j := by
  rw [tau_expand]
  have key : ∀ a b, (x - x0) * (y - y0) * (P a b * (∑ i ∈ range a, x ^ i * x0 ^ (a - 1 - i)) *
        (∑ j ∈ range b, y ^ j * y0 ^ (b - 1 - j))) =
      P a b * x ^ a * y ^ b - x ^ a * (P a b * y0 ^ b) - y ^ b * (P a b * x0 ^ a) +
        x0 ^ a * (P a b * y0 ^ b) := by
    intro a b
    have h1 := geom_sum₂_mul x x0 a
    have h2 := geom_sum₂_mul y y0 b
    linear_combination (P a b * (∑ j ∈ range b, y ^ j * y0 ^ (b - 1 - j)) * (y - y0)) * h1 +
      (P a b * (x ^ a - x0 ^ a)) * h2
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).trans
    (Finset.sum_congr rfl fun b _ => key a b)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e2 : ∑ a ∈ range m, ∑ b ∈ range n, x ^ a * (P a b * y0 ^ b) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [← Finset.mul_sum, hC a (mem_range.mp ha), mul_zero]
  have e4 : ∑ a ∈ range m, ∑ b ∈ range n, x0 ^ a * (P a b * y0 ^ b) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [← Finset.mul_sum, hC a (mem_range.mp ha), mul_zero]
  have e3 : ∑ a ∈ range m, ∑ b ∈ range n, y ^ b * (P a b * x0 ^ a) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b hb
    rw [← Finset.mul_sum, hR b (mem_range.mp hb), mul_zero]
  rw [e2, e3, e4]
  ring

end CritRank.Terracini

namespace CritRank.Terracini

open Finset

/-- Point `k` of the configuration imposes the two divisibility conditions, and the remaining
`p * q` points of the curve `y = x ^ p` force the quotient to vanish. -/
lemma dual_zero (p q : ℕ) (hp : 1 ≤ p) (P : ℕ → ℕ → ℂ) (k : ℕ) (hk : k ≤ p * q)
    (hR : ∀ b < q + 1, ∑ a ∈ range (p + 1), P a b * (k : ℂ) ^ a = 0)
    (hC : ∀ a < p + 1, ∑ b ∈ range (q + 1), P a b * ((k : ℂ) ^ p) ^ b = 0)
    (hT : ∀ t ≤ p * q, ∑ a ∈ range (p + 1), ∑ b ∈ range (q + 1),
      P a b * (t : ℂ) ^ a * ((t : ℂ) ^ p) ^ b = 0) :
    ∀ a < p + 1, ∀ b < q + 1, P a b = 0 := by
  have hF := factor (p + 1) (q + 1) P (k : ℂ) ((k : ℂ) ^ p) hR hC
  simp only [Nat.add_sub_cancel] at hF
  have hτ : ∀ i < p, ∀ j < q, tau (p + 1) (q + 1) P k ((k : ℂ) ^ p) i j = 0 := by
    apply coeff_vanish p q _ (((range (p * q + 1)).erase k).image (fun t : ℕ => (t : ℂ)))
    · rw [card_image_of_injective _ Nat.cast_injective,
        card_erase_of_mem (mem_range.mpr (by omega)), card_range]
      omega
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      obtain ⟨htk, htr⟩ := mem_erase.mp ht
      have ht' : t ≤ p * q := by rw [mem_range] at htr; omega
      have h0 := hT t ht'
      rw [hF] at h0
      have hx : (t : ℂ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast htk)
      have hy : (t : ℂ) ^ p - (k : ℂ) ^ p ≠ 0 := by
        apply sub_ne_zero.mpr
        intro he
        apply htk
        have h2 : t ^ p = k ^ p := by exact_mod_cast he
        exact Nat.pow_left_injective (by omega) h2
      have h1 := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hx hy)
      rw [← h1]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add, pow_mul]
      ring
  have hFz : ∀ x y : ℂ, ∑ a ∈ range (p + 1), ∑ b ∈ range (q + 1), P a b * x ^ a * y ^ b = 0 := by
    intro x y
    rw [hF x y, Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => by
      rw [hτ i (mem_range.mp hi) j (mem_range.mp hj)]; ring)), mul_zero]
  apply coeff_vanish (p + 1) (q + 1) P ((range ((p + 1) * (q + 1))).image (fun t : ℕ => (t : ℂ)))
  · rw [card_image_of_injective _ Nat.cast_injective, card_range]
  · intro s _
    rw [← hFz s (s ^ (p + 1))]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add, pow_mul]
    ring

/-- The first factor of point `t`: the moment curve in `t`. -/
def ptA (p N : ℕ) (t : Fin (N + 1)) (i : Fin (p + 1)) : ℂ := ((t : ℕ) : ℂ) ^ (i : ℕ)

/-- The second factor of point `t`: the moment curve in `t ^ p`. -/
def ptB (p q N : ℕ) (t : Fin (N + 1)) (j : Fin (q + 1)) : ℂ := (((t : ℕ) : ℂ) ^ p) ^ (j : ℕ)

/-- Generators of the tangent space at point `k` plus the span of all the points. -/
def gen (p q N : ℕ) (k : Fin (N + 1)) :
    (Fin (p + 1) ⊕ Fin (q + 1)) ⊕ Fin (N + 1) → Fin (p + 1) → Fin (q + 1) → ℂ
  | .inl (.inl i0) => fun i j => if i = i0 then ptB p q N k j else 0
  | .inl (.inr j0) => fun i j => if j = j0 then ptA p N k i else 0
  | .inr t => fun i j => ptA p N t i * ptB p q N t j

/-- The matrix units. -/
def unit (m n : ℕ) (i : Fin m) (j : Fin n) : Fin m → Fin n → ℂ :=
  fun i' j' => if i' = i ∧ j' = j then 1 else 0

lemma eval_dual {m n : ℕ} (f : Module.Dual ℂ (Fin m → Fin n → ℂ)) (X : Fin m → Fin n → ℂ) :
    f X = ∑ i, ∑ j, X i j * f (unit m n i j) := by
  have hX : X = ∑ i, ∑ j, X i j • unit m n i j := by
    funext i' j'
    simp [Finset.sum_apply, unit, ite_and]
  conv_lhs => rw [hX]
  simp [map_sum, map_smul]

lemma span_top (p q : ℕ) (hp : 1 ≤ p) (k : Fin (p * q + 1)) :
    Submodule.span ℂ (Set.range (gen p q (p * q) k)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hg : ∀ α, f (gen p q (p * q) k α) = 0 := by
    intro α
    have h := Submodule.mem_map_of_mem (f := f)
      (Submodule.subset_span (R := ℂ) (Set.mem_range_self (f := gen p q (p * q) k) α))
    rw [hmap] at h
    simpa using h
  let P : ℕ → ℕ → ℂ := fun a b =>
    if h : a < p + 1 ∧ b < q + 1 then f (unit (p + 1) (q + 1) ⟨a, h.1⟩ ⟨b, h.2⟩) else 0
  have hP : ∀ (i : Fin (p + 1)) (j : Fin (q + 1)), f (unit (p + 1) (q + 1) i j) = P i j := by
    intro i j
    simp only [P]
    rw [dif_pos ⟨i.isLt, j.isLt⟩]
  have hzero := dual_zero p q hp P k (by omega)
    (by
      intro b hb
      have h := hg (.inl (.inr ⟨b, hb⟩))
      rw [eval_dual] at h
      simp only [gen, ite_mul, zero_mul, hP] at h
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      rw [← h, ← Fin.sum_univ_eq_sum_range (fun a => P a b * (k : ℂ) ^ a)]
      apply Finset.sum_congr rfl
      intro a _
      simp [ptA, mul_comm])
    (by
      intro a ha
      have h := hg (.inl (.inl ⟨a, ha⟩))
      rw [eval_dual] at h
      simp only [gen, ite_mul, zero_mul, hP] at h
      rw [Finset.sum_comm] at h
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      rw [← h, ← Fin.sum_univ_eq_sum_range (fun b => P a b * ((k : ℂ) ^ p) ^ b)]
      apply Finset.sum_congr rfl
      intro b _
      simp [ptB, mul_comm])
    (by
      intro t ht
      have h := hg (.inr ⟨t, by omega⟩)
      rw [eval_dual] at h
      simp only [gen, hP] at h
      rw [← h, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro b _
      simp only [ptA, ptB]
      ring)
  apply hf0
  apply LinearMap.ext
  intro X
  rw [eval_dual f X]
  simp only [hP, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [hzero i i.isLt j j.isLt, mul_zero]

lemma slice_spans (p q : ℕ) (hp : 1 ≤ p) (k : Fin (p * q + 1))
    (M : Fin (p + 1) → Fin (q + 1) → ℂ) :
    ∃ u : Fin (p + 1) → ℂ, ∃ v : Fin (q + 1) → ℂ, ∃ w : Fin (p * q + 1) → ℂ, ∀ i j,
      M i j = u i * ptB p q (p * q) k j + ptA p (p * q) k i * v j +
        ∑ t, ptA p (p * q) t i * (ptB p q (p * q) t j * w t) := by
  classical
  have hM : M ∈ Submodule.span ℂ (Set.range (gen p q (p * q) k)) := by
    rw [span_top p q hp k]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM
  refine ⟨fun i => c (.inl (.inl i)), fun j => c (.inl (.inr j)), fun t => c (.inr t), ?_⟩
  intro i j
  rw [← hc]
  simp only [Finset.sum_apply, Fintype.sum_sum_type, Pi.smul_apply, smul_eq_mul, gen]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro t _
    ring

end CritRank.Terracini

namespace CritRank

open Arxiv.«0805.3777» Terracini

/-- Taking the third factor of point `k` to be the `k`-th basis vector, and that of the last
point to be zero, the tangent map at the moment-curve configuration is onto. -/
lemma spans (p q : ℕ) (hp : 1 ≤ p) :
    Dominance.TangentSpans (p + 1) (q + 1) (p * q) (p * q + 1) := by
  classical
  refine ⟨ptA p (p * q), ptB p q (p * q), fun t k => if t = Fin.castSucc k then 1 else 0, ?_⟩
  intro T
  choose u v w h using fun k : Fin (p * q) =>
    slice_spans p q hp (Fin.castSucc k) (fun i j => T i j k)
  refine ⟨fun t i => if ht : t = Fin.last _ then 0 else u (t.castPred ht) i,
    fun t j => if ht : t = Fin.last _ then 0 else v (t.castPred ht) j, fun t k => w k t, ?_⟩
  intro i j k
  rw [h k i j]
  simp only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Fin.castSucc_ne_last, dite_false, Fin.castPred_castSucc]

lemma count (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (p + 1 + (q + 1) + p * q - 2) * (p * q) < (p + 1) * (q + 1) * (p * q) := by
  have hpq : 0 < p * q := Nat.mul_pos (by omega) (by omega)
  rw [show p + 1 + (q + 1) + p * q - 2 = p + q + p * q by omega]
  calc (p + q + p * q) * (p * q) < (p + q + p * q + 1) * (p * q) :=
        Nat.mul_lt_mul_of_pos_right (by omega) hpq
    _ = (p + 1) * (q + 1) * (p * q) := by ring

end CritRank

open Arxiv.«0805.3777» CritRank Set in
theorem OMA.solution : type_of% @Arxiv.«0805.3777».isGenericRank_of_eq_critical := by
  intro m₁ m₂ h₁ h₁₂
  obtain ⟨p, rfl⟩ : ∃ p, m₁ = p + 1 := ⟨m₁ - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, m₂ = q + 1 := ⟨m₂ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨U, hu, hd, hup⟩ := Dominance.upper_of_spans (spans p q (by omega))
  let K := closure {T : Holor ℂ [p + 1, q + 1, p * q] | T.cprank ≤ p * q}
  have hlow := Dimension.lower_of_count (p + 1) (q + 1) (p * q) (p * q)
    (count p q (by omega) (by omega))
  have hd' : Dense Kᶜ := interior_eq_empty_iff_dense_compl.mp hlow
  refine ⟨U ∩ Kᶜ, hu.inter isClosed_closure.isOpen_compl, hd.inter_of_isOpen_left hd' hu, ?_⟩
  intro T ht
  have hi := hup T ht.1
  have lo : ¬ T.cprank ≤ p * q := fun hle => ht.2 (subset_closure hle)
  omega
