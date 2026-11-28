import OMAReductions.R_Arxiv_0805_3777_isGenericRank_three_odd_R1

/-!
# Generic upper bound for `3 x (2p + 1) x (2p + 1)` complex tensors

Step `Arxiv.0805.3777.isGenericRank_three_odd.R1.H2`: for every `p ≥ 1`, there is a dense open
subset of `Holor ℂ [3, 2 * p + 1, 2 * p + 1]` on which `cprank ≤ 3 * p + 2`.

Proof strategy (Terracini + Chevalley + Nullstellensatz):
1. Construct an explicit cubic-block parameter tuple `basePoint p` of `3 * p + 2` rank-1 summands
   using `a(r) = (1, r, r^3)` on `p` blocks of size `2 x 2` plus one block of size `1 x 1`.
2. Prove the differential `DΦ(basePoint p)` is surjective block-by-block using the exact
   factorization of the cubic 4-cycle determinant.
3. By the inverse function theorem (`HasStrictFDerivAt.map_nhds_eq_of_equiv`), the range of `Φ`
   contains a nonempty open set, so the pullback algebra homomorphism `Φ*` is injective.
4. By Chevalley's theorem (`PrimeSpectrum.isConstructible_range_comap`) and Hilbert's
   Nullstellensatz (`MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`), the image of `Φ`
   contains a nonempty Zariski-open (hence Euclidean open and dense) set.
-/

-- Credit: @ovolee37

namespace OMA.ThreeOddUpper

open scoped BigOperators Topology Arxiv.«0805.3777»
open MvPolynomial

/- ### Part 1: Multivariate polynomials vanishing on nonempty open sets -/

private lemma mvPoly_eval_continuous {σ : Type*} (P : MvPolynomial σ ℂ) :
    Continuous (fun x : σ → ℂ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C] using continuous_const
  | add p q hp hq =>
    have h : (fun x : σ → ℂ => MvPolynomial.eval x (p + q)) =
        fun x => MvPolynomial.eval x p + MvPolynomial.eval x q := by
      funext x; exact map_add (MvPolynomial.eval x) p q
    rw [h]
    exact hp.add hq
  | mul_X p i hp =>
    have h : (fun x : σ → ℂ => MvPolynomial.eval x (p * MvPolynomial.X i)) =
        fun x => MvPolynomial.eval x p * x i := by
      funext x; simp
    rw [h]
    exact hp.mul (continuous_apply i)

private lemma poly_eq_zero_of_ball {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (P : Polynomial ℂ) (hP : ∀ z ∈ Metric.ball z₀ ε, P.eval z = 0) : P = 0 := by
  by_contra hne
  let f : ℕ → ℂ := fun n => z₀ + ((ε / (n + 2 : ℝ) : ℝ) : ℂ)
  have hf_inj : Function.Injective f := by
    intro m n hmn
    have h1 : ((ε / (m + 2 : ℝ) : ℝ) : ℂ) = ((ε / (n + 2 : ℝ) : ℝ) : ℂ) :=
      add_left_cancel hmn
    have h2 : ε / (m + 2 : ℝ) = ε / (n + 2 : ℝ) := Complex.ofReal_injective h1
    have h3 : (m + 2 : ℝ) = (n + 2 : ℝ) := by
      have hm : (m + 2 : ℝ) ≠ 0 := by positivity
      have hn : (n + 2 : ℝ) ≠ 0 := by positivity
      have hε' : ε ≠ 0 := hε.ne'
      field_simp at h2
      linarith
    have h4 : (m : ℝ) = (n : ℝ) := by linarith
    exact Nat.cast_injective h4
  have hmem : ∀ n : ℕ, f n ∈ Metric.ball z₀ ε := by
    intro n
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : f n - z₀ = ((ε / (n + 2 : ℝ) : ℝ) : ℂ) := by simp [f]
    rw [hsub, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlt : (1 : ℝ) < (n + 2 : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact div_lt_self hε hlt
  have hsub : Set.range f ⊆ {z : ℂ | P.IsRoot z} := by
    rintro _ ⟨n, rfl⟩
    exact hP (f n) (hmem n)
  have hinf : ({z : ℂ | P.IsRoot z}).Infinite :=
    (Set.infinite_range_of_injective hf_inj).mono hsub
  have hfin : ({z : ℂ | P.IsRoot z}).Finite := by
    have hsub' : {z : ℂ | P.IsRoot z} ⊆ (P.roots.toFinset : Set ℂ) := by
      intro z hz
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hz
    exact (P.roots.toFinset.finite_toSet).subset hsub'
  exact hinf hfin

private lemma mvPoly_fin_eq_zero_of_open : ∀ {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    {U : Set (Fin n → ℂ)}, IsOpen U → U.Nonempty →
    (∀ x ∈ U, MvPolynomial.eval x P = 0) → P = 0
  | 0, P, U, _, ⟨x₀, hx₀⟩, hP => by
    rw [MvPolynomial.eq_C_of_isEmpty P]
    have h0 := hP x₀ hx₀
    rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eval_C] at h0
    rw [h0, map_zero]
  | n + 1, P, U, hUopen, ⟨x₀, hx₀⟩, hP => by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen x₀ hx₀
    let Q : Polynomial (MvPolynomial (Fin n) ℂ) := MvPolynomial.finSuccEquiv ℂ n P
    have hcoeff : ∀ k : ℕ, Q.coeff k = 0 := by
      intro k
      refine mvPoly_fin_eq_zero_of_open (Q.coeff k) (Metric.isOpen_ball)
        ⟨Fin.tail x₀, Metric.mem_ball_self hε⟩ ?_
      intro y hy
      let R : Polynomial ℂ := Q.map (MvPolynomial.eval y)
      have hR : R = 0 := by
        refine poly_eq_zero_of_ball (z₀ := x₀ 0) hε R ?_
        intro t ht
        have hcons : Fin.cons t y ∈ Metric.ball x₀ ε := by
          rw [Metric.mem_ball, dist_pi_lt_iff hε]
          intro i
          refine Fin.cases ?_ ?_ i
          · simpa [Fin.cons_zero] using Metric.mem_ball.mp ht
          · intro j
            have hyj := (dist_pi_lt_iff hε).mp (Metric.mem_ball.mp hy) j
            simpa [Fin.cons_succ, Fin.tail] using hyj
        have hev := hP (Fin.cons t y) (hball hcons)
        have hrel : R.eval t = MvPolynomial.eval (Fin.cons t y) P := by
          simpa [R, Q, Polynomial.eval_map] using
            (MvPolynomial.eval_eq_eval_mv_eval' (R := ℂ) (n := n) y t P).symm
        rw [hrel, hev]
      have hc := congrArg (fun p : Polynomial ℂ => p.coeff k) hR
      simpa [R, Polynomial.coeff_map] using hc
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro k
      simpa using hcoeff k
    exact (MvPolynomial.finSuccEquiv ℂ n).injective (by simpa [Q] using hQ0)

private def piHomeo {α β : Type*} (e : α ≃ β) : (α → ℂ) ≃ₜ (β → ℂ) where
  toFun f b := f (e.symm b)
  invFun g a := g (e a)
  left_inv f := by funext a; simp
  right_inv g := by funext b; simp
  continuous_toFun := continuous_pi fun b => continuous_apply (e.symm b)
  continuous_invFun := continuous_pi fun a => continuous_apply (e a)

private lemma mvPoly_eq_zero_of_open {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) {U : Set (σ → ℂ)} (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hP : ∀ x ∈ U, MvPolynomial.eval x P = 0) : P = 0 := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let P' : MvPolynomial (Fin (Fintype.card σ)) ℂ := MvPolynomial.rename e P
  let hHomeo : (Fin (Fintype.card σ) → ℂ) ≃ₜ (σ → ℂ) := piHomeo e.symm
  have hOpen' : IsOpen (hHomeo ⁻¹' U) := hUopen.preimage hHomeo.continuous
  have hNe' : (hHomeo ⁻¹' U).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    exact ⟨hHomeo.symm x, by simpa using hx⟩
  have hP' : ∀ y ∈ hHomeo ⁻¹' U, MvPolynomial.eval y P' = 0 := by
    intro y hy
    have heq : MvPolynomial.eval y P' = MvPolynomial.eval (y ∘ e) P :=
      MvPolynomial.eval_rename e y P
    have hye : y ∘ e = hHomeo y := by
      funext i
      simp [hHomeo, piHomeo]
    rw [heq, hye]
    exact hP (hHomeo y) hy
  have h0 : P' = 0 := mvPoly_fin_eq_zero_of_open P' hOpen' hNe' hP'
  exact MvPolynomial.rename_injective e e.injective (by simpa [P'] using h0)

private lemma mvPoly_nonvanishing_open_dense {σ : Type*} [Fintype σ]
    {g : MvPolynomial σ ℂ} (hg : g ≠ 0) :
    IsOpen {x : σ → ℂ | MvPolynomial.eval x g ≠ 0} ∧
    Dense {x : σ → ℂ | MvPolynomial.eval x g ≠ 0} := by
  constructor
  · exact isClosed_singleton.isOpen_compl.preimage (mvPoly_eval_continuous g)
  · rw [dense_iff_inter_open]
    intro U hUopen hUne
    by_contra hdisj
    rw [Set.not_nonempty_iff_eq_empty] at hdisj
    have hzero : ∀ x ∈ U, MvPolynomial.eval x g = 0 := by
      intro x hx
      by_contra hne
      have : x ∈ U ∩ {x : σ → ℂ | MvPolynomial.eval x g ≠ 0} := ⟨hx, hne⟩
      rw [hdisj] at this
      exact this
    exact hg (mvPoly_eq_zero_of_open g hUopen hUne hzero)

/- ### Part 2: Dominant polynomial map via Chevalley's theorem and Nullstellensatz -/

private lemma exists_dense_open_subset_range_of_open_in_range
    {τ σ : Type*} [Fintype τ] [DecidableEq τ] [Fintype σ] [DecidableEq σ]
    (Φpoly : σ → MvPolynomial τ ℂ)
    (hopen : ∃ U : Set (σ → ℂ), IsOpen U ∧ U.Nonempty ∧
      U ⊆ Set.range (fun x : τ → ℂ => fun j : σ => MvPolynomial.eval x (Φpoly j))) :
    ∃ V : Set (σ → ℂ), IsOpen V ∧ Dense V ∧
      V ⊆ Set.range (fun x : τ → ℂ => fun j : σ => MvPolynomial.eval x (Φpoly j)) := by
  let Φ : (τ → ℂ) → (σ → ℂ) := fun x j => MvPolynomial.eval x (Φpoly j)
  let f : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ := MvPolynomial.aeval Φpoly
  have heval_f : ∀ (P : MvPolynomial σ ℂ) (x : τ → ℂ),
      MvPolynomial.eval x (f P) = MvPolynomial.eval (Φ x) P := by
    intro P x
    induction P using MvPolynomial.induction_on with
    | C c => simp [f]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p j hp =>
      rw [map_mul, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp]
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    obtain ⟨U, hUopen, hUne, hUsub⟩ := hopen
    refine mvPoly_eq_zero_of_open P hUopen hUne ?_
    intro y hy
    obtain ⟨x, hx⟩ := hUsub hy
    rw [← hx, ← heval_f P x, hP, map_zero]
  have hf_fp : f.toRingHom.FinitePresentation := by
    have hcomp : (f.toRingHom.comp (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).FinitePresentation := by
      have heq : f.toRingHom.comp (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) =
          algebraMap ℂ (MvPolynomial τ ℂ) := by
        ext c
        simp [f]
      rw [heq, RingHom.finitePresentation_algebraMap]
      infer_instance
    have hft : (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ).FiniteType := by
      change (algebraMap ℂ (MvPolynomial σ ℂ)).FiniteType
      rw [RingHom.finiteType_algebraMap]
      infer_instance
    exact RingHom.FinitePresentation.of_comp_finiteType _ hcomp hft
  have hcons : Topology.IsConstructible (Set.range (PrimeSpectrum.comap f.toRingHom)) :=
    PrimeSpectrum.isConstructible_range_comap hf_fp
  obtain ⟨S, hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hcons
  let botP : PrimeSpectrum (MvPolynomial σ ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  let botQ : PrimeSpectrum (MvPolynomial τ ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  have hbot_mem : botP ∈ S.toSet := by
    rw [hS]
    refine ⟨botQ, ?_⟩
    apply PrimeSpectrum.ext
    ext p
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, botP, botQ, Ideal.mem_bot,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact ⟨fun h => hf_inj (by simpa using h), fun h => by simp [h]⟩
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion, exists_prop] at hbot_mem
  obtain ⟨C, hCS, hbotC⟩ := hbot_mem
  rw [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff] at hbotC
  have hCg_zero : ∀ i, C.g i = 0 := by
    intro i
    have h1 := hbotC.1 (Set.mem_range_self i)
    exact Ideal.mem_bot.mp h1
  have hCf_ne : C.f ≠ 0 := by
    intro h0
    apply hbotC.2
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    rw [h0]
    exact Ideal.zero_mem _
  have hbasic_sub : ∀ P : PrimeSpectrum (MvPolynomial σ ℂ),
      C.f ∉ P.asIdeal → P ∈ Set.range (PrimeSpectrum.comap f.toRingHom) := by
    intro P hP
    rw [← hS]
    simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion, exists_prop]
    refine ⟨C, hCS, ?_⟩
    rw [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff]
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨i, rfl⟩ := hp
      rw [hCg_zero i]
      exact Ideal.zero_mem _
    · intro hmem
      exact hP (hmem (Set.mem_singleton C.f))
  refine ⟨{y : σ → ℂ | MvPolynomial.eval y C.f ≠ 0},
    (mvPoly_nonvanishing_open_dense hCf_ne).1,
    (mvPoly_nonvanishing_open_dense hCf_ne).2, ?_⟩
  intro y hy
  let my : PrimeSpectrum (MvPolynomial σ ℂ) := MvPolynomial.pointToPoint (k := ℂ) y
  have hCf_not_my : C.f ∉ my.asIdeal := by
    intro hmem
    have : MvPolynomial.eval y C.f = 0 := by
      have h1 := (MvPolynomial.mem_vanishingIdeal_singleton_iff (k := ℂ) y C.f).mp hmem
      simpa [MvPolynomial.aeval_eq_eval] using h1
    exact hy this
  obtain ⟨q, hq⟩ := hbasic_sub my hCf_not_my
  obtain ⟨n, hn_max, hqn⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  obtain ⟨x, rfl⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hn_max
  have hmy_max : my.asIdeal.IsMaximal :=
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨y, rfl⟩
  have hle : my.asIdeal ≤ (MvPolynomial.vanishingIdeal ℂ {x}).comap f.toRingHom := by
    rw [← hq]
    exact Ideal.comap_mono hqn
  have hne_top : (MvPolynomial.vanishingIdeal ℂ {x}).comap f.toRingHom ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial σ ℂ) ∈ (MvPolynomial.vanishingIdeal ℂ {x}).comap f.toRingHom := by
      rw [htop]; trivial
    rw [Ideal.mem_comap, map_one] at h1
    have h10 := (MvPolynomial.mem_vanishingIdeal_singleton_iff (k := ℂ) x 1).mp h1
    simp at h10
  have heq_id : my.asIdeal = (MvPolynomial.vanishingIdeal ℂ {x}).comap f.toRingHom :=
    hmy_max.eq_of_le hne_top hle
  refine ⟨x, ?_⟩
  funext j
  have hmem_my : MvPolynomial.X j - MvPolynomial.C (y j) ∈ my.asIdeal := by
    rw [show my.asIdeal = MvPolynomial.vanishingIdeal ℂ {y} from rfl,
      MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [heq_id, Ideal.mem_comap] at hmem_my
  have h0 := (MvPolynomial.mem_vanishingIdeal_singleton_iff (k := ℂ) x _).mp hmem_my
  have h1 : MvPolynomial.eval x (f (MvPolynomial.X j - MvPolynomial.C (y j))) = 0 := by
    simpa [MvPolynomial.aeval_eq_eval] using h0
  simp only [map_sub, f, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.eval_C] at h1
  exact sub_eq_zero.mp h1

/- ### Part 3: Submersion implies open neighborhood in range -/

private lemma open_subset_range_of_surjective_fderiv
    {τ σ : Type*} [Fintype τ] [Fintype σ]
    {Φ : (τ → ℂ) → (σ → ℂ)} {x₀ : τ → ℂ} {L : (τ → ℂ) →L[ℂ] (σ → ℂ)}
    (hderiv : HasStrictFDerivAt Φ L x₀) (hsurj : Function.Surjective L) :
    ∃ U : Set (σ → ℂ), IsOpen U ∧ U.Nonempty ∧ U ⊆ Set.range Φ := by
  have hrg : LinearMap.range L.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
  obtain ⟨R, hLR⟩ := LinearMap.exists_rightInverse_of_surjective L.toLinearMap hrg
  let Rc : (σ → ℂ) →L[ℂ] (τ → ℂ) := LinearMap.toContinuousLinearMap R
  let g : (σ → ℂ) → (τ → ℂ) := fun w => x₀ + Rc w
  have hg : HasStrictFDerivAt g Rc 0 := by
    simpa [g] using (hasStrictFDerivAt_const x₀ (0 : σ → ℂ)).add Rc.hasStrictFDerivAt
  have hcomp : HasStrictFDerivAt (Φ ∘ g) (L.comp Rc) 0 := by
    have hx : g 0 = x₀ := by simp [g]
    exact (hx ▸ hderiv).comp 0 hg
  have hLRc : L.comp Rc = (ContinuousLinearEquiv.refl ℂ (σ → ℂ) : (σ → ℂ) →L[ℂ] (σ → ℂ)) := by
    ext w j
    have := LinearMap.congr_fun hLR w
    exact congrFun this j
  rw [hLRc] at hcomp
  have hmap := hcomp.map_nhds_eq_of_equiv
  have hmem_nhds : Set.range (Φ ∘ g) ∈ 𝓝 ((Φ ∘ g) 0) := by
    rw [← hmap, Filter.mem_map]
    refine Filter.mem_of_superset Filter.univ_mem ?_
    intro w _
    exact Set.mem_range_self w
  have hmem_range : Set.range Φ ∈ 𝓝 (Φ x₀) := by
    have hsub : Set.range (Φ ∘ g) ⊆ Set.range Φ := Set.range_comp_subset_range g Φ
    have hg0 : (Φ ∘ g) 0 = Φ x₀ := by simp [g]
    rw [hg0] at hmem_nhds
    exact Filter.mem_of_superset hmem_nhds hsub
  obtain ⟨U, hUsub, hUopen, hUx₀⟩ := mem_nhds_iff.mp hmem_range
  exact ⟨U, hUopen, ⟨Φ x₀, hUx₀⟩, hUsub⟩

/- ### Part 4: Cubic-block Terracini point and surjectivity of DΦ(x₀) -/

private lemma cubic_two_roots {f₀ f₁ f₂ u v : ℂ} (huv : u ≠ v)
    (hu : f₀ + f₁ * u + f₂ * u ^ 3 = 0)
    (hv : f₀ + f₁ * v + f₂ * v ^ 3 = 0) (x : ℂ) :
    f₀ + f₁ * x + f₂ * x ^ 3 = f₂ * (x - u) * (x - v) * (x + u + v) := by
  have hdiff : (u - v) * (f₁ + f₂ * (u ^ 2 + u * v + v ^ 2)) = 0 := by
    linear_combination hu - hv
  have hf1 : f₁ = -f₂ * (u ^ 2 + u * v + v ^ 2) := by
    have h1 := (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr huv)
    linear_combination h1
  have hf0 : f₀ = f₂ * u * v * (u + v) := by
    linear_combination hu - u * hf1
  rw [hf0, hf1]
  ring

private lemma cubic_three_roots {f₀ f₁ f₂ u v w : ℂ}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hsum : u + v + w ≠ 0)
    (hu : f₀ + f₁ * u + f₂ * u ^ 3 = 0)
    (hv : f₀ + f₁ * v + f₂ * v ^ 3 = 0)
    (hw : f₀ + f₁ * w + f₂ * w ^ 3 = 0) :
    f₀ = 0 ∧ f₁ = 0 ∧ f₂ = 0 := by
  have h1 := cubic_two_roots huv hu hv w
  rw [hw] at h1
  have hf2 : f₂ = 0 := by
    have hprod : (w - u) * (w - v) * (w + u + v) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr huw.symm) (sub_ne_zero.mpr hvw.symm)) ?_
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have h2 : f₂ * ((w - u) * (w - v) * (w + u + v)) = 0 := by
      linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_right hprod
  have h1' := cubic_two_roots huv hu hv 0
  rw [hf2] at h1' hu
  have hf0 : f₀ = 0 := by simpa using h1'
  have hf1 : f₁ = 0 := by
    by_cases hu0 : u = 0
    · rw [hu0] at huv
      rw [hf0, hf2] at hv
      have hfv : f₁ * v = 0 := by linear_combination hv
      exact (mul_eq_zero.mp hfv).resolve_right huv.symm
    · rw [hf0] at hu
      have hfu : f₁ * u = 0 := by linear_combination hu
      exact (mul_eq_zero.mp hfu).resolve_right hu0
  exact ⟨hf0, hf1, hf2⟩

private lemma four_cycle_kill {α β γ α' β' γ' cP cQ cR cS : ℂ}
    (hαβ : α ≠ β) (hα'β' : α' ≠ β') (hγγ' : γ ≠ γ')
    (hγα : γ ≠ α) (hγβ : γ ≠ β) (hγα' : γ ≠ α') (hγβ' : γ ≠ β')
    (hγ'α : γ' ≠ α) (hγ'β : γ' ≠ β) (hγ'α' : γ' ≠ α') (hγ'β' : γ' ≠ β')
    (hsum_all : α + β + γ + α' + β' + γ' ≠ 0)
    (hs2 : β + α' + γ ≠ 0) (hs4 : β + β' + γ ≠ 0) (hs7 : α + β' + γ' ≠ 0)
    (heq1 : cP * (γ - α) * (γ - α') * (γ + α + α') +
            cR * (γ - β) * (γ - α') * (γ + β + α') = 0)
    (heq2 : cQ * (γ - α) * (γ - β') * (γ + α + β') +
            cS * (γ - β) * (γ - β') * (γ + β + β') = 0)
    (heq3 : cP * (γ' - α) * (γ' - α') * (γ' + α + α') +
            cQ * (γ' - α) * (γ' - β') * (γ' + α + β') = 0)
    (heq4 : cR * (γ' - β) * (γ' - α') * (γ' + β + α') +
            cS * (γ' - β) * (γ' - β') * (γ' + β + β') = 0) :
    cP = 0 ∧ cQ = 0 ∧ cR = 0 ∧ cS = 0 := by
  have e1 : cP * (γ - α) * (α + α' + γ) + cR * (γ - β) * (β + α' + γ) = 0 := by
    have h : (γ - α') * (cP * (γ - α) * (α + α' + γ) + cR * (γ - β) * (β + α' + γ)) = 0 := by
      linear_combination heq1
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hγα')
  have e2 : cQ * (γ - α) * (α + β' + γ) + cS * (γ - β) * (β + β' + γ) = 0 := by
    have h : (γ - β') * (cQ * (γ - α) * (α + β' + γ) + cS * (γ - β) * (β + β' + γ)) = 0 := by
      linear_combination heq2
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hγβ')
  have e3 : cP * (γ' - α') * (α + α' + γ') + cQ * (γ' - β') * (α + β' + γ') = 0 := by
    have h : (γ' - α) * (cP * (γ' - α') * (α + α' + γ') + cQ * (γ' - β') * (α + β' + γ')) = 0 := by
      linear_combination heq3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hγ'α)
  have e4 : cR * (γ' - α') * (β + α' + γ') + cS * (γ' - β') * (β + β' + γ') = 0 := by
    have h : (γ' - β) * (cR * (γ' - α') * (β + α' + γ') + cS * (γ' - β') * (β + β' + γ')) = 0 := by
      linear_combination heq4
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hγ'β)
  set A1 := (γ - α) * (α + α' + γ)
  set B1 := (γ - β) * (β + α' + γ)
  set A2 := (γ - α) * (α + β' + γ)
  set B2 := (γ - β) * (β + β' + γ)
  set A3 := (γ' - α') * (α + α' + γ')
  set B3 := (γ' - β') * (α + β' + γ')
  set A4 := (γ' - α') * (β + α' + γ')
  set B4 := (γ' - β') * (β + β' + γ')
  have h1 : cP * A1 + cR * B1 = 0 := by linear_combination e1
  have h2 : cQ * A2 + cS * B2 = 0 := by linear_combination e2
  have h3 : cP * A3 + cQ * B3 = 0 := by linear_combination e3
  have h4 : cR * A4 + cS * B4 = 0 := by linear_combination e4
  have hPS1 : cP * (A1 * A4) - cS * (B1 * B4) = 0 := by
    linear_combination A4 * h1 - B1 * h4
  have hPS2 : cP * (A3 * A2) - cS * (B3 * B2) = 0 := by
    linear_combination A2 * h3 - B3 * h2
  have hdet' : cP * (A1 * A4 * B2 * B3 - B1 * B4 * A2 * A3) = 0 := by
    linear_combination (B2 * B3) * hPS1 - (B1 * B4) * hPS2
  have hfac : A1 * A4 * B2 * B3 - B1 * B4 * A2 * A3 =
      (γ - α) * (γ - β) * (γ' - α') * (γ' - β') *
        ((α - β) * (α' - β') * (γ - γ') * (α + β + γ + α' + β' + γ')) := by
    dsimp [A1, B1, A2, B2, A3, B3, A4, B4]
    ring
  rw [hfac] at hdet'
  have hnz : (γ - α) * (γ - β) * (γ' - α') * (γ' - β') *
      ((α - β) * (α' - β') * (γ - γ') * (α + β + γ + α' + β' + γ')) ≠ 0 := by
    refine mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hγα) (sub_ne_zero.mpr hγβ))
        (sub_ne_zero.mpr hγ'α')) (sub_ne_zero.mpr hγ'β'))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hαβ) (sub_ne_zero.mpr hα'β'))
        (sub_ne_zero.mpr hγγ')) hsum_all)
  have hcP : cP = 0 := (mul_eq_zero.mp hdet').resolve_right hnz
  rw [hcP, zero_mul, zero_add] at h1 h3
  have hcR : cR = 0 := (mul_eq_zero.mp h1).resolve_right
    (mul_ne_zero (sub_ne_zero.mpr hγβ) hs2)
  have hcQ : cQ = 0 := (mul_eq_zero.mp h3).resolve_right
    (mul_ne_zero (sub_ne_zero.mpr hγ'β') hs7)
  rw [hcQ, zero_mul, zero_add] at h2
  have hcS : cS = 0 := (mul_eq_zero.mp h2).resolve_right
    (mul_ne_zero (sub_ne_zero.mpr hγβ) hs4)
  exact ⟨hcP, hcQ, hcR, hcS⟩

/- ### Explicit cubic-block configuration for 3 x (2p+1) x (2p+1) with k = 3p+2 -/

private abbrev ParamIdx (p : ℕ) : Type :=
  Fin (3 * p + 2) × (Fin 3 ⊕ Fin (2 * p + 1) ⊕ Fin (2 * p + 1))

private abbrev TensorIdx (p : ℕ) : Type :=
  Fin 3 × Fin (2 * p + 1) × Fin (2 * p + 1)

private def cubicA (r : ℕ) : Fin 3 → ℂ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => (r : ℂ)
  | ⟨2, _⟩ => (r : ℂ) ^ 3

private def baseB (p : ℕ) (r : Fin (3 * p + 2)) (i : Fin (2 * p + 1)) : ℂ :=
  if r.1 < 3 * p then
    let t := r.1 / 3
    let rem := r.1 % 3
    if rem = 0 then (if i.1 = 2 * t then 1 else 0)
    else if rem = 1 then (if i.1 = 2 * t + 1 then 1 else 0)
    else (if i.1 = 2 * t ∨ i.1 = 2 * t + 1 then 1 else 0)
  else
    if i.1 = 2 * p then 1 else 0

private def basePoint (p : ℕ) : ParamIdx p → ℂ
  | (r, Sum.inl s) => cubicA r.1 s
  | (r, Sum.inr (Sum.inl i)) => baseB p r i
  | (r, Sum.inr (Sum.inr j)) => baseB p r j

private noncomputable def tensorMapPoly (p : ℕ) :
    TensorIdx p → MvPolynomial (ParamIdx p) ℂ :=
  fun idx =>
    ∑ r : Fin (3 * p + 2),
      MvPolynomial.X (r, Sum.inl idx.1) *
      MvPolynomial.X (r, Sum.inr (Sum.inl idx.2.1)) *
      MvPolynomial.X (r, Sum.inr (Sum.inr idx.2.2))

private def tensorMap (p : ℕ) (x : ParamIdx p → ℂ) : TensorIdx p → ℂ :=
  fun idx =>
    ∑ r : Fin (3 * p + 2),
      x (r, Sum.inl idx.1) * x (r, Sum.inr (Sum.inl idx.2.1)) * x (r, Sum.inr (Sum.inr idx.2.2))

private lemma tensorMap_eq_eval (p : ℕ) (x : ParamIdx p → ℂ) (idx : TensorIdx p) :
    MvPolynomial.eval x (tensorMapPoly p idx) = tensorMap p x idx := by
  simp [tensorMapPoly, tensorMap, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X]

private noncomputable def tensorDeriv (p : ℕ) (x₀ : ParamIdx p → ℂ) :
    (ParamIdx p → ℂ) →L[ℂ] (TensorIdx p → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun δ idx =>
        ∑ r : Fin (3 * p + 2),
          (δ (r, Sum.inl idx.1) * x₀ (r, Sum.inr (Sum.inl idx.2.1)) * x₀ (r, Sum.inr (Sum.inr idx.2.2)) +
           x₀ (r, Sum.inl idx.1) * δ (r, Sum.inr (Sum.inl idx.2.1)) * x₀ (r, Sum.inr (Sum.inr idx.2.2)) +
           x₀ (r, Sum.inl idx.1) * x₀ (r, Sum.inr (Sum.inl idx.2.1)) * δ (r, Sum.inr (Sum.inr idx.2.2)))
      map_add' := fun u v => by
        funext idx
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => by ring
      map_smul' := fun c u => by
        funext idx
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring }

private lemma tensorMap_hasStrictFDerivAt (p : ℕ) (x₀ : ParamIdx p → ℂ) :
    HasStrictFDerivAt (tensorMap p) (tensorDeriv p x₀) x₀ := by
  have hpi : tensorDeriv p x₀ = ContinuousLinearMap.pi
      (fun idx : TensorIdx p =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : TensorIdx p => ℂ) idx).comp
          (tensorDeriv p x₀)) := by
    ext δ idx
    rfl
  rw [hpi]
  refine hasStrictFDerivAt_pi.mpr fun idx => ?_
  let pr (k : ParamIdx p) : (ParamIdx p → ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ParamIdx p => ℂ) k
  let Lr : Fin (3 * p + 2) → (ParamIdx p → ℂ) →L[ℂ] ℂ := fun r =>
    ((pr (r, Sum.inl idx.1)).smulRight (x₀ (r, Sum.inr (Sum.inl idx.2.1))) +
      x₀ (r, Sum.inl idx.1) • pr (r, Sum.inr (Sum.inl idx.2.1))).smulRight
        (x₀ (r, Sum.inr (Sum.inr idx.2.2))) +
      (x₀ (r, Sum.inl idx.1) * x₀ (r, Sum.inr (Sum.inl idx.2.1))) •
        pr (r, Sum.inr (Sum.inr idx.2.2))
  have hsum : HasStrictFDerivAt
      (fun x : ParamIdx p → ℂ =>
        ∑ r : Fin (3 * p + 2),
          x (r, Sum.inl idx.1) * x (r, Sum.inr (Sum.inl idx.2.1)) * x (r, Sum.inr (Sum.inr idx.2.2)))
      (∑ r : Fin (3 * p + 2), Lr r) x₀ := by
    refine HasStrictFDerivAt.fun_sum fun r _ => ?_
    have ha : HasStrictFDerivAt (fun x : ParamIdx p → ℂ => x (r, Sum.inl idx.1))
        (pr (r, Sum.inl idx.1)) x₀ := (pr (r, Sum.inl idx.1)).hasStrictFDerivAt
    have hb : HasStrictFDerivAt (fun x : ParamIdx p → ℂ => x (r, Sum.inr (Sum.inl idx.2.1)))
        (pr (r, Sum.inr (Sum.inl idx.2.1))) x₀ := (pr (r, Sum.inr (Sum.inl idx.2.1))).hasStrictFDerivAt
    have hc : HasStrictFDerivAt (fun x : ParamIdx p → ℂ => x (r, Sum.inr (Sum.inr idx.2.2)))
        (pr (r, Sum.inr (Sum.inr idx.2.2))) x₀ := (pr (r, Sum.inr (Sum.inr idx.2.2))).hasStrictFDerivAt
    refine ((ha.mul hb).mul hc).congr_fderiv ?_
    ext δ
    dsimp [Lr, pr]
    simp only [ContinuousLinearMap.smulRight_apply, smul_eq_mul, add_apply, smul_apply,
      ContinuousLinearMap.proj_apply]
    ring
  have hLeq : ∑ r : Fin (3 * p + 2), Lr r =
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : TensorIdx p => ℂ) idx).comp
        (tensorDeriv p x₀) := by
    ext δ
    simp only [sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, tensorDeriv, LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp [Lr, pr]
    simp only [ContinuousLinearMap.smulRight_apply, smul_eq_mul, add_apply, smul_apply,
      ContinuousLinearMap.proj_apply]
    ring
  rw [← hLeq]
  exact hsum

private lemma natCast_ne_of_ne {a b : ℕ} (h : a ≠ b) : (a : ℂ) ≠ (b : ℂ) :=
  fun heq => h (Nat.cast_injective heq)

private lemma natCast_sum_ne_zero {a b c : ℕ} (h : 0 < a + b + c) :
    (a : ℂ) + (b : ℂ) + (c : ℂ) ≠ 0 := by
  have h1 : (a : ℂ) + (b : ℂ) + (c : ℂ) = ((a + b + c : ℕ) : ℂ) := by push_cast; rfl
  rw [h1]
  exact Nat.cast_ne_zero.mpr (by omega)

private lemma natCast_sum6_ne_zero {a b c d e f : ℕ} (h : 0 < a + b + c + d + e + f) :
    (a : ℂ) + (b : ℂ) + (c : ℂ) + (d : ℂ) + (e : ℂ) + (f : ℂ) ≠ 0 := by
  have h1 : (a : ℂ) + (b : ℂ) + (c : ℂ) + (d : ℂ) + (e : ℂ) + (f : ℂ) =
      ((a + b + c + d + e + f : ℕ) : ℂ) := by push_cast; rfl
  rw [h1]
  exact Nat.cast_ne_zero.mpr (by omega)

private lemma baseB_r0 {p : ℕ} {t : ℕ} (ht : t < p) (i : Fin (2 * p + 1)) :
    baseB p ⟨3 * t, by omega⟩ i = if i.1 = 2 * t then 1 else 0 := by
  unfold baseB
  have hlt : 3 * t < 3 * p := by omega
  have hdiv : (3 * t) / 3 = t := by omega
  have hmod : (3 * t) % 3 = 0 := by omega
  simp [hlt, hdiv, hmod]

private lemma baseB_r1 {p : ℕ} {t : ℕ} (ht : t < p) (i : Fin (2 * p + 1)) :
    baseB p ⟨3 * t + 1, by omega⟩ i = if i.1 = 2 * t + 1 then 1 else 0 := by
  unfold baseB
  have hlt : 3 * t + 1 < 3 * p := by omega
  have hdiv : (3 * t + 1) / 3 = t := by omega
  have hmod : (3 * t + 1) % 3 = 1 := by omega
  simp [hlt, hdiv, hmod]

private lemma baseB_r2 {p : ℕ} {t : ℕ} (ht : t < p) (i : Fin (2 * p + 1)) :
    baseB p ⟨3 * t + 2, by omega⟩ i = if i.1 = 2 * t ∨ i.1 = 2 * t + 1 then 1 else 0 := by
  unfold baseB
  have hlt : 3 * t + 2 < 3 * p := by omega
  have hdiv : (3 * t + 2) / 3 = t := by omega
  have hmod : (3 * t + 2) % 3 = 2 := by omega
  simp [hlt, hdiv, hmod]

private lemma baseB_rp0 {p : ℕ} (i : Fin (2 * p + 1)) :
    baseB p ⟨3 * p, by omega⟩ i = if i.1 = 2 * p then 1 else 0 := by
  unfold baseB
  simp

private lemma baseB_rp1 {p : ℕ} (i : Fin (2 * p + 1)) :
    baseB p ⟨3 * p + 1, by omega⟩ i = if i.1 = 2 * p then 1 else 0 := by
  unfold baseB
  have hlt : ¬ (3 * p + 1 < 3 * p) := by omega
  simp [hlt]

private lemma exists_dual_ne_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    {x : E} (hx : x ≠ 0) : ∃ ψ : E →ₗ[ℂ] ℂ, ψ x ≠ 0 := by
  let S : Submodule ℂ E := Submodule.span ℂ {x}
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let f : S →ₗ[ℂ] ℂ :=
    (LinearEquiv.toSpanNonzeroSingleton ℂ E x hx).symm.toLinearMap
  let proj : E →ₗ[ℂ] S := S.projectionOnto T hT
  refine ⟨f.comp proj, ?_⟩
  have hmem : x ∈ S := Submodule.subset_span (Set.mem_singleton x)
  have hproj : proj x = ⟨x, hmem⟩ := Submodule.projectionOnto_apply_left hT ⟨x, hmem⟩
  change f (proj x) ≠ 0
  rw [hproj]
  have hf : f ⟨x, hmem⟩ = 1 := by
    apply (LinearEquiv.toSpanNonzeroSingleton ℂ E x hx).injective
    simp [f]
  rw [hf]
  exact one_ne_zero

private lemma tensorDeriv_basePoint_surjective (p : ℕ) (hp : 1 ≤ p) :
    Function.Surjective (tensorDeriv p (basePoint p)) := by
  set L := (tensorDeriv p (basePoint p)).toLinearMap
  change Function.Surjective L
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y : TensorIdx p → ℂ, y ∉ LinearMap.range L := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.mpr fun y _ => hall y)
  let q : (TensorIdx p → ℂ) →ₗ[ℂ] (TensorIdx p → ℂ) ⧸ LinearMap.range L :=
    Submodule.mkQ (LinearMap.range L)
  have hqy : q y ≠ 0 := by
    intro h0
    exact hy ((Submodule.Quotient.mk_eq_zero _).mp h0)
  obtain ⟨ψ, hψ⟩ := exists_dual_ne_zero hqy
  let φ : (TensorIdx p → ℂ) →ₗ[ℂ] ℂ := ψ.comp q
  have hφ_range : ∀ δ : ParamIdx p → ℂ, φ (L δ) = 0 := by
    intro δ
    change ψ (q (L δ)) = 0
    have : q (L δ) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨δ, rfl⟩
    rw [this, map_zero]
  have hφy : φ y ≠ 0 := hψ
  let M : Fin (2 * p + 1) → Fin (2 * p + 1) → Fin 3 → ℂ :=
    fun i j s => φ (Pi.single (s, i, j) 1)
  have hφ_eval : ∀ T : TensorIdx p → ℂ,
      φ T = ∑ s : Fin 3, ∑ i : Fin (2 * p + 1), ∑ j : Fin (2 * p + 1), M i j s * T (s, i, j) := by
    intro T
    have hT : T = ∑ idx : TensorIdx p, T idx • Pi.single idx (1 : ℂ) := by
      ext idx
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hT]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by
          dsimp [M]; ring
  let ev (i j : Fin (2 * p + 1)) (r : ℕ) : ℂ :=
    M i j 0 + M i j 1 * (r : ℂ) + M i j 2 * (r : ℂ) ^ 3
  have hvarA : ∀ (r : Fin (3 * p + 2)) (s : Fin 3),
      ∑ i : Fin (2 * p + 1), ∑ j : Fin (2 * p + 1),
        M i j s * baseB p r i * baseB p r j = 0 := by
    intro r s
    have h0 := hφ_range (Pi.single (r, Sum.inl s) 1)
    rw [hφ_eval] at h0
    have hL : ∀ (s' : Fin 3) (i j : Fin (2 * p + 1)),
        L (Pi.single (r, Sum.inl s) 1) (s', i, j) =
          if s' = s then baseB p r i * baseB p r j else 0 := by
      intro s' i j
      simp only [L, tensorDeriv, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
        AddHom.coe_mk, ContinuousLinearMap.coe_coe]
      rw [Finset.sum_eq_single r]
      · by_cases hs : s' = s
        · subst hs
          simp [Pi.single_apply, basePoint]
        · simp [Pi.single_apply, hs, basePoint]
      · intro r' _ hr'
        simp [Pi.single_apply, hr', basePoint]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    simp_rw [hL] at h0
    rw [Finset.sum_eq_single s] at h0
    · simpa [mul_assoc] using h0
    · intro s' _ hs'
      simp [hs']
    · intro hs; exact absurd (Finset.mem_univ s) hs
  have hvarB : ∀ (r : Fin (3 * p + 2)) (i : Fin (2 * p + 1)),
      ∑ j : Fin (2 * p + 1), ev i j r.1 * baseB p r j = 0 := by
    intro r i
    have h0 := hφ_range (Pi.single (r, Sum.inr (Sum.inl i)) 1)
    rw [hφ_eval] at h0
    have hL : ∀ (s' : Fin 3) (i' j : Fin (2 * p + 1)),
        L (Pi.single (r, Sum.inr (Sum.inl i)) 1) (s', i', j) =
          if i' = i then cubicA r.1 s' * baseB p r j else 0 := by
      intro s' i' j
      simp only [L, tensorDeriv, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
        AddHom.coe_mk, ContinuousLinearMap.coe_coe]
      rw [Finset.sum_eq_single r]
      · by_cases hi : i' = i
        · subst hi
          simp [Pi.single_apply, basePoint]
        · simp [Pi.single_apply, hi, basePoint]
      · intro r' _ hr'
        simp [Pi.single_apply, hr', basePoint]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    simp_rw [hL] at h0
    have h1 : ∀ s' : Fin 3,
        (∑ i' : Fin (2 * p + 1), ∑ j : Fin (2 * p + 1),
          M i' j s' * (if i' = i then cubicA r.1 s' * baseB p r j else 0)) =
        ∑ j : Fin (2 * p + 1), M i j s' * cubicA r.1 s' * baseB p r j := by
      intro s'
      rw [Finset.sum_eq_single i]
      · refine Finset.sum_congr rfl fun j _ => by simp [mul_assoc]
      · intro i' _ hi'
        simp [hi']
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [h1] at h0
    rw [Fin.sum_univ_three] at h0
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib] at h0
    have h2 : ∀ j : Fin (2 * p + 1),
        M i j 0 * cubicA r.1 0 * baseB p r j + M i j 1 * cubicA r.1 1 * baseB p r j +
          M i j 2 * cubicA r.1 2 * baseB p r j = ev i j r.1 * baseB p r j := by
      intro j
      simp only [ev, cubicA]
      ring
    simpa [h2] using h0
  have hvarC : ∀ (r : Fin (3 * p + 2)) (j : Fin (2 * p + 1)),
      ∑ i : Fin (2 * p + 1), ev i j r.1 * baseB p r i = 0 := by
    intro r j
    have h0 := hφ_range (Pi.single (r, Sum.inr (Sum.inr j)) 1)
    rw [hφ_eval] at h0
    have hL : ∀ (s' : Fin 3) (i j' : Fin (2 * p + 1)),
        L (Pi.single (r, Sum.inr (Sum.inr j)) 1) (s', i, j') =
          if j' = j then cubicA r.1 s' * baseB p r i else 0 := by
      intro s' i j'
      simp only [L, tensorDeriv, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
        AddHom.coe_mk, ContinuousLinearMap.coe_coe]
      rw [Finset.sum_eq_single r]
      · by_cases hj : j' = j
        · subst hj
          simp [Pi.single_apply, basePoint]
        · simp [Pi.single_apply, hj, basePoint]
      · intro r' _ hr'
        simp [Pi.single_apply, hr', basePoint]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    simp_rw [hL] at h0
    have h1 : ∀ s' : Fin 3,
        (∑ i : Fin (2 * p + 1), ∑ j' : Fin (2 * p + 1),
          M i j' s' * (if j' = j then cubicA r.1 s' * baseB p r i else 0)) =
        ∑ i : Fin (2 * p + 1), M i j s' * cubicA r.1 s' * baseB p r i := by
      intro s'
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single j]
      · simp [mul_assoc]
      · intro j' _ hj'
        simp [hj']
      · intro hj; exact absurd (Finset.mem_univ j) hj
    simp_rw [h1] at h0
    rw [Fin.sum_univ_three] at h0
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib] at h0
    have h2 : ∀ i : Fin (2 * p + 1),
        M i j 0 * cubicA r.1 0 * baseB p r i + M i j 1 * cubicA r.1 1 * baseB p r i +
          M i j 2 * cubicA r.1 2 * baseB p r i = ev i j r.1 * baseB p r i := by
      intro i
      simp only [ev, cubicA]
      ring
    simpa [h2] using h0
  have hA_single : ∀ (r : Fin (3 * p + 2)) (k : Fin (2 * p + 1)) (s : Fin 3),
      (∀ i, baseB p r i = if i = k then 1 else 0) → M k k s = 0 := by
    intro r k s hB
    have h := hvarA r s
    simp_rw [hB] at h
    rw [Finset.sum_eq_single k] at h
    · rw [Finset.sum_eq_single k] at h
      · simpa using h
      · intro j _ hj; simp [hj]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    · intro i _ hi; simp [hi]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hB_single : ∀ (r : Fin (3 * p + 2)) (k i : Fin (2 * p + 1)),
      (∀ j, baseB p r j = if j = k then 1 else 0) → ev i k r.1 = 0 := by
    intro r k i hB
    have h := hvarB r i
    simp_rw [hB] at h
    rw [Finset.sum_eq_single k] at h
    · simpa using h
    · intro j _ hj; simp [hj]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hC_single : ∀ (r : Fin (3 * p + 2)) (k j : Fin (2 * p + 1)),
      (∀ i, baseB p r i = if i = k then 1 else 0) → ev k j r.1 = 0 := by
    intro r k j hB
    have h := hvarC r j
    simp_rw [hB] at h
    rw [Finset.sum_eq_single k] at h
    · simpa using h
    · intro i _ hi; simp [hi]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hB_pair : ∀ (t : ℕ) (ht : t < p) (i : Fin (2 * p + 1)),
      ev i ⟨2 * t, by omega⟩ (3 * t + 2) + ev i ⟨2 * t + 1, by omega⟩ (3 * t + 2) = 0 := by
    intro t ht i
    have h := hvarB ⟨3 * t + 2, by omega⟩ i
    simp_rw [baseB_r2 ht] at h
    let u : Fin (2 * p + 1) := ⟨2 * t, by omega⟩
    let v : Fin (2 * p + 1) := ⟨2 * t + 1, by omega⟩
    have huv : u ≠ v := by intro heq; have := congrArg Fin.val heq; dsimp [u, v] at this; omega
    have hsum : (∑ j : Fin (2 * p + 1),
        ev i j (3 * t + 2) * (if j.1 = 2 * t ∨ j.1 = 2 * t + 1 then 1 else 0)) =
        ev i u (3 * t + 2) + ev i v (3 * t + 2) := by
      rw [← Finset.sum_subset (Finset.subset_univ ({u, v} : Finset (Fin (2 * p + 1))))]
      · rw [Finset.sum_pair huv]
        simp [u, v]
      · intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        have hj1 : j.1 ≠ 2 * t := fun heq => hj.1 (Fin.ext heq)
        have hj2 : j.1 ≠ 2 * t + 1 := fun heq => hj.2 (Fin.ext heq)
        simp [hj1, hj2]
    exact hsum.symm.trans h
  have hC_pair : ∀ (t : ℕ) (ht : t < p) (j : Fin (2 * p + 1)),
      ev ⟨2 * t, by omega⟩ j (3 * t + 2) + ev ⟨2 * t + 1, by omega⟩ j (3 * t + 2) = 0 := by
    intro t ht j
    have h := hvarC ⟨3 * t + 2, by omega⟩ j
    simp_rw [baseB_r2 ht] at h
    let u : Fin (2 * p + 1) := ⟨2 * t, by omega⟩
    let v : Fin (2 * p + 1) := ⟨2 * t + 1, by omega⟩
    have huv : u ≠ v := by intro heq; have := congrArg Fin.val heq; dsimp [u, v] at this; omega
    have hsum : (∑ i : Fin (2 * p + 1),
        ev i j (3 * t + 2) * (if i.1 = 2 * t ∨ i.1 = 2 * t + 1 then 1 else 0)) =
        ev u j (3 * t + 2) + ev v j (3 * t + 2) := by
      rw [← Finset.sum_subset (Finset.subset_univ ({u, v} : Finset (Fin (2 * p + 1))))]
      · rw [Finset.sum_pair huv]
        simp [u, v]
      · intro i _ hi
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        have hi1 : i.1 ≠ 2 * t := fun heq => hi.1 (Fin.ext heq)
        have hi2 : i.1 ≠ 2 * t + 1 := fun heq => hi.2 (Fin.ext heq)
        simp [hi1, hi2]
    exact hsum.symm.trans h
  have hM_zero : ∀ (i j : Fin (2 * p + 1)) (s : Fin 3), M i j s = 0 := by
    have hM_of_ev0 : ∀ (i j : Fin (2 * p + 1)),
        M i j 0 = 0 ∧ M i j 1 = 0 ∧ M i j 2 = 0 → ∀ s : Fin 3, M i j s = 0 := by
      intro i j ⟨h0, h1, h2⟩ s
      fin_cases s <;> assumption
    let w : Fin (2 * p + 1) := ⟨2 * p, by omega⟩
    have hB_rp0' : ∀ k : Fin (2 * p + 1), baseB p ⟨3 * p, by omega⟩ k = if k = w then 1 else 0 := by
      intro k; rw [baseB_rp0]; by_cases h : k = w
      · subst h; simp [w]
      · have h' : k.1 ≠ 2 * p := fun heq => h (Fin.ext heq)
        simp [h, h']
    have hB_rp1' : ∀ k : Fin (2 * p + 1), baseB p ⟨3 * p + 1, by omega⟩ k = if k = w then 1 else 0 := by
      intro k; rw [baseB_rp1]; by_cases h : k = w
      · subst h; simp [w]
      · have h' : k.1 ≠ 2 * p := fun heq => h (Fin.ext heq)
        simp [h, h']
    have hB_r0' : ∀ (t : ℕ) (ht : t < p) (k : Fin (2 * p + 1)),
        baseB p ⟨3 * t, by omega⟩ k = if k = ⟨2 * t, by omega⟩ then 1 else 0 := by
      intro t ht k; rw [baseB_r0 ht]; by_cases h : k = ⟨2 * t, by omega⟩
      · subst h; simp
      · have h' : k.1 ≠ 2 * t := fun heq => h (Fin.ext heq)
        simp [h, h']
    have hB_r1' : ∀ (t : ℕ) (ht : t < p) (k : Fin (2 * p + 1)),
        baseB p ⟨3 * t + 1, by omega⟩ k = if k = ⟨2 * t + 1, by omega⟩ then 1 else 0 := by
      intro t ht k; rw [baseB_r1 ht]; by_cases h : k = ⟨2 * t + 1, by omega⟩
      · subst h; simp
      · have h' : k.1 ≠ 2 * t + 1 := fun heq => h (Fin.ext heq)
        simp [h, h']
    have hww : ∀ s : Fin 3, M w w s = 0 := fun s => hA_single ⟨3 * p, by omega⟩ w s hB_rp0'
    have hiw : ∀ (i : Fin (2 * p + 1)), i.1 < 2 * p → ∀ s : Fin 3, M i w s = 0 := by
      intro i hi
      set t := i.1 / 2
      have ht : t < p := by omega
      have h1 : ev i w (3 * p) = 0 := hB_single ⟨3 * p, by omega⟩ w i hB_rp0'
      have h2 : ev i w (3 * p + 1) = 0 := hB_single ⟨3 * p + 1, by omega⟩ w i hB_rp1'
      have h3 : ∃ r0 : ℕ, r0 < 3 * p ∧ ev i w r0 = 0 := by
        by_cases hev : i.1 % 2 = 0
        · refine ⟨3 * t, by omega, ?_⟩
          have hieq : i = ⟨2 * t, by omega⟩ := Fin.ext (by change i.1 = 2 * t; omega)
          rw [hieq]
          exact hC_single ⟨3 * t, by omega⟩ ⟨2 * t, by omega⟩ w (hB_r0' t ht)
        · refine ⟨3 * t + 1, by omega, ?_⟩
          have hieq : i = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change i.1 = 2 * t + 1; omega)
          rw [hieq]
          exact hC_single ⟨3 * t + 1, by omega⟩ ⟨2 * t + 1, by omega⟩ w (hB_r1' t ht)
      obtain ⟨r0, hr0, h3'⟩ := h3
      exact hM_of_ev0 i w (cubic_three_roots
        (natCast_ne_of_ne (by omega : r0 ≠ 3 * p))
        (natCast_ne_of_ne (by omega : r0 ≠ 3 * p + 1))
        (natCast_ne_of_ne (by omega : 3 * p ≠ 3 * p + 1))
        (natCast_sum_ne_zero (by omega : 0 < r0 + 3 * p + (3 * p + 1)))
        h3' h1 h2)
    have hwj : ∀ (j : Fin (2 * p + 1)), j.1 < 2 * p → ∀ s : Fin 3, M w j s = 0 := by
      intro j hj
      set t := j.1 / 2
      have ht : t < p := by omega
      have h1 : ev w j (3 * p) = 0 := hC_single ⟨3 * p, by omega⟩ w j hB_rp0'
      have h2 : ev w j (3 * p + 1) = 0 := hC_single ⟨3 * p + 1, by omega⟩ w j hB_rp1'
      have h3 : ∃ r0 : ℕ, r0 < 3 * p ∧ ev w j r0 = 0 := by
        by_cases hev : j.1 % 2 = 0
        · refine ⟨3 * t, by omega, ?_⟩
          have hjeq : j = ⟨2 * t, by omega⟩ := Fin.ext (by change j.1 = 2 * t; omega)
          rw [hjeq]
          exact hB_single ⟨3 * t, by omega⟩ ⟨2 * t, by omega⟩ w (hB_r0' t ht)
        · refine ⟨3 * t + 1, by omega, ?_⟩
          have hjeq : j = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change j.1 = 2 * t + 1; omega)
          rw [hjeq]
          exact hB_single ⟨3 * t + 1, by omega⟩ ⟨2 * t + 1, by omega⟩ w (hB_r1' t ht)
      obtain ⟨r0, hr0, h3'⟩ := h3
      exact hM_of_ev0 w j (cubic_three_roots
        (natCast_ne_of_ne (by omega : r0 ≠ 3 * p))
        (natCast_ne_of_ne (by omega : r0 ≠ 3 * p + 1))
        (natCast_ne_of_ne (by omega : 3 * p ≠ 3 * p + 1))
        (natCast_sum_ne_zero (by omega : 0 < r0 + 3 * p + (3 * p + 1)))
        h3' h1 h2)
    have hdiag2 : ∀ (t : ℕ) (ht : t < p),
        (∀ s, M ⟨2 * t, by omega⟩ ⟨2 * t, by omega⟩ s = 0) ∧
        (∀ s, M ⟨2 * t + 1, by omega⟩ ⟨2 * t + 1, by omega⟩ s = 0) ∧
        (∀ s, M ⟨2 * t, by omega⟩ ⟨2 * t + 1, by omega⟩ s = 0) ∧
        (∀ s, M ⟨2 * t + 1, by omega⟩ ⟨2 * t, by omega⟩ s = 0) := by
      intro t ht
      let u : Fin (2 * p + 1) := ⟨2 * t, by omega⟩
      let v : Fin (2 * p + 1) := ⟨2 * t + 1, by omega⟩
      have huu : ∀ s, M u u s = 0 := fun s => hA_single ⟨3 * t, by omega⟩ u s (hB_r0' t ht)
      have hvv : ∀ s, M v v s = 0 := fun s => hA_single ⟨3 * t + 1, by omega⟩ v s (hB_r1' t ht)
      have huv0 : ev u v (3 * t) = 0 := hC_single ⟨3 * t, by omega⟩ u v (hB_r0' t ht)
      have huv1 : ev u v (3 * t + 1) = 0 := hB_single ⟨3 * t + 1, by omega⟩ v u (hB_r1' t ht)
      have huv2 : ev u v (3 * t + 2) = 0 := by
        have h := hC_pair t ht v
        have hv0 : ev v v (3 * t + 2) = 0 := by simp [ev, hvv]
        rw [hv0, add_zero] at h
        exact h
      have huv : ∀ s, M u v s = 0 := hM_of_ev0 u v (cubic_three_roots
        (natCast_ne_of_ne (by omega : 3 * t ≠ 3 * t + 1))
        (natCast_ne_of_ne (by omega : 3 * t ≠ 3 * t + 2))
        (natCast_ne_of_ne (by omega : 3 * t + 1 ≠ 3 * t + 2))
        (natCast_sum_ne_zero (by omega : 0 < 3 * t + (3 * t + 1) + (3 * t + 2)))
        huv0 huv1 huv2)
      have hvu0 : ev v u (3 * t) = 0 := hB_single ⟨3 * t, by omega⟩ u v (hB_r0' t ht)
      have hvu1 : ev v u (3 * t + 1) = 0 := hC_single ⟨3 * t + 1, by omega⟩ v u (hB_r1' t ht)
      have hvu2 : ev v u (3 * t + 2) = 0 := by
        have h := hC_pair t ht u
        have hu0 : ev u u (3 * t + 2) = 0 := by simp [ev, huu]
        rw [hu0, zero_add] at h
        exact h
      have hvu : ∀ s, M v u s = 0 := hM_of_ev0 v u (cubic_three_roots
        (natCast_ne_of_ne (by omega : 3 * t ≠ 3 * t + 1))
        (natCast_ne_of_ne (by omega : 3 * t ≠ 3 * t + 2))
        (natCast_ne_of_ne (by omega : 3 * t + 1 ≠ 3 * t + 2))
        (natCast_sum_ne_zero (by omega : 0 < 3 * t + (3 * t + 1) + (3 * t + 2)))
        hvu0 hvu1 hvu2)
      exact ⟨huu, hvv, huv, hvu⟩
    have hoff2 : ∀ (t s : ℕ) (ht : t < p) (hs : s < p), t ≠ s →
        (∀ k, M ⟨2 * t, by omega⟩ ⟨2 * s, by omega⟩ k = 0) ∧
        (∀ k, M ⟨2 * t, by omega⟩ ⟨2 * s + 1, by omega⟩ k = 0) ∧
        (∀ k, M ⟨2 * t + 1, by omega⟩ ⟨2 * s, by omega⟩ k = 0) ∧
        (∀ k, M ⟨2 * t + 1, by omega⟩ ⟨2 * s + 1, by omega⟩ k = 0) := by
      intro t s ht hs hts
      let u : Fin (2 * p + 1) := ⟨2 * t, by omega⟩
      let v : Fin (2 * p + 1) := ⟨2 * t + 1, by omega⟩
      let u' : Fin (2 * p + 1) := ⟨2 * s, by omega⟩
      let v' : Fin (2 * p + 1) := ⟨2 * s + 1, by omega⟩
      have hP1 : ev u u' (3 * t) = 0 := hC_single ⟨3 * t, by omega⟩ u u' (hB_r0' t ht)
      have hP2 : ev u u' (3 * s) = 0 := hB_single ⟨3 * s, by omega⟩ u' u (hB_r0' s hs)
      have hQ1 : ev u v' (3 * t) = 0 := hC_single ⟨3 * t, by omega⟩ u v' (hB_r0' t ht)
      have hQ2 : ev u v' (3 * s + 1) = 0 := hB_single ⟨3 * s + 1, by omega⟩ v' u (hB_r1' s hs)
      have hR1 : ev v u' (3 * t + 1) = 0 := hC_single ⟨3 * t + 1, by omega⟩ v u' (hB_r1' t ht)
      have hR2 : ev v u' (3 * s) = 0 := hB_single ⟨3 * s, by omega⟩ u' v (hB_r0' s hs)
      have hS1 : ev v v' (3 * t + 1) = 0 := hC_single ⟨3 * t + 1, by omega⟩ v v' (hB_r1' t ht)
      have hS2 : ev v v' (3 * s + 1) = 0 := hB_single ⟨3 * s + 1, by omega⟩ v' v (hB_r1' s hs)
      have fP := cubic_two_roots (natCast_ne_of_ne (by omega : 3 * t ≠ 3 * s)) hP1 hP2
      have fQ := cubic_two_roots (natCast_ne_of_ne (by omega : 3 * t ≠ 3 * s + 1)) hQ1 hQ2
      have fR := cubic_two_roots (natCast_ne_of_ne (by omega : 3 * t + 1 ≠ 3 * s)) hR1 hR2
      have fS := cubic_two_roots (natCast_ne_of_ne (by omega : 3 * t + 1 ≠ 3 * s + 1)) hS1 hS2
      have heq1 := hC_pair t ht u'
      have heq2 := hC_pair t ht v'
      have heq3 := hB_pair s hs u
      have heq4 := hB_pair s hs v
      dsimp only [ev] at heq1 heq2 heq3 heq4
      rw [fP, fR] at heq1
      rw [fQ, fS] at heq2
      rw [fP, fQ] at heq3
      rw [fR, fS] at heq4
      obtain ⟨hcP, hcQ, hcR, hcS⟩ := four_cycle_kill
        (natCast_ne_of_ne (by omega : 3 * t ≠ 3 * t + 1))
        (natCast_ne_of_ne (by omega : 3 * s ≠ 3 * s + 1))
        (natCast_ne_of_ne (by omega : 3 * t + 2 ≠ 3 * s + 2))
        (natCast_ne_of_ne (by omega : 3 * t + 2 ≠ 3 * t))
        (natCast_ne_of_ne (by omega : 3 * t + 2 ≠ 3 * t + 1))
        (natCast_ne_of_ne (by omega : 3 * t + 2 ≠ 3 * s))
        (natCast_ne_of_ne (by omega : 3 * t + 2 ≠ 3 * s + 1))
        (natCast_ne_of_ne (by omega : 3 * s + 2 ≠ 3 * t))
        (natCast_ne_of_ne (by omega : 3 * s + 2 ≠ 3 * t + 1))
        (natCast_ne_of_ne (by omega : 3 * s + 2 ≠ 3 * s))
        (natCast_ne_of_ne (by omega : 3 * s + 2 ≠ 3 * s + 1))
        (natCast_sum6_ne_zero (by omega : 0 < 3*t + (3*t+1) + (3*t+2) + 3*s + (3*s+1) + (3*s+2)))
        (natCast_sum_ne_zero (by omega : 0 < (3*t+1) + 3*s + (3*t+2)))
        (natCast_sum_ne_zero (by omega : 0 < (3*t+1) + (3*s+1) + (3*t+2)))
        (natCast_sum_ne_zero (by omega : 0 < 3*t + (3*s+1) + (3*s+2)))
        heq1 heq2 heq3 heq4
      have kill2 : ∀ (a b : Fin (2 * p + 1)) (r1 r2 : ℕ), r1 ≠ r2 →
          ev a b r1 = 0 → ev a b r2 = 0 → M a b 2 = 0 → ∀ k : Fin 3, M a b k = 0 := by
        intro a b r1 r2 hr12 h1 h2 hm2
        have h0 := cubic_two_roots (natCast_ne_of_ne hr12) h1 h2 0
        rw [hm2] at h0
        have hm0 : M a b 0 = 0 := by simpa using h0
        have h1' := cubic_two_roots (natCast_ne_of_ne hr12) h1 h2 1
        rw [hm0, hm2] at h1'
        have hm1 : M a b 1 = 0 := by simpa using h1'
        exact hM_of_ev0 a b ⟨hm0, hm1, hm2⟩
      exact ⟨kill2 u u' (3 * t) (3 * s) (by omega) hP1 hP2 hcP,
             kill2 u v' (3 * t) (3 * s + 1) (by omega) hQ1 hQ2 hcQ,
             kill2 v u' (3 * t + 1) (3 * s) (by omega) hR1 hR2 hcR,
             kill2 v v' (3 * t + 1) (3 * s + 1) (by omega) hS1 hS2 hcS⟩
    intro i j s
    by_cases hi : i.1 < 2 * p
    · by_cases hj : j.1 < 2 * p
      · set t := i.1 / 2 with ht_eq
        set u := j.1 / 2 with hu_eq
        have ht : t < p := by omega
        have hu : u < p := by omega
        by_cases htu : t = u
        · obtain ⟨h00, h11, h01, h10⟩ := hdiag2 t ht
          by_cases him : i.1 % 2 = 0 <;> by_cases hjm : j.1 % 2 = 0
          · have hi' : i = ⟨2 * t, by omega⟩ := Fin.ext (by change i.1 = 2 * t; omega)
            have hj' : j = ⟨2 * t, by omega⟩ := Fin.ext (by change j.1 = 2 * t; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h00 s)
          · have hi' : i = ⟨2 * t, by omega⟩ := Fin.ext (by change i.1 = 2 * t; omega)
            have hj' : j = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change j.1 = 2 * t + 1; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h01 s)
          · have hi' : i = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change i.1 = 2 * t + 1; omega)
            have hj' : j = ⟨2 * t, by omega⟩ := Fin.ext (by change j.1 = 2 * t; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h10 s)
          · have hi' : i = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change i.1 = 2 * t + 1; omega)
            have hj' : j = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change j.1 = 2 * t + 1; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h11 s)
        · obtain ⟨h00, h01, h10, h11⟩ := hoff2 t u ht hu htu
          by_cases him : i.1 % 2 = 0 <;> by_cases hjm : j.1 % 2 = 0
          · have hi' : i = ⟨2 * t, by omega⟩ := Fin.ext (by change i.1 = 2 * t; omega)
            have hj' : j = ⟨2 * u, by omega⟩ := Fin.ext (by change j.1 = 2 * u; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h00 s)
          · have hi' : i = ⟨2 * t, by omega⟩ := Fin.ext (by change i.1 = 2 * t; omega)
            have hj' : j = ⟨2 * u + 1, by omega⟩ := Fin.ext (by change j.1 = 2 * u + 1; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h01 s)
          · have hi' : i = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change i.1 = 2 * t + 1; omega)
            have hj' : j = ⟨2 * u, by omega⟩ := Fin.ext (by change j.1 = 2 * u; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h10 s)
          · have hi' : i = ⟨2 * t + 1, by omega⟩ := Fin.ext (by change i.1 = 2 * t + 1; omega)
            have hj' : j = ⟨2 * u + 1, by omega⟩ := Fin.ext (by change j.1 = 2 * u + 1; omega)
            exact (congrFun (congrArg₂ M hi' hj') s).trans (h11 s)
      · have hjw : j = w := Fin.ext (by dsimp [w]; omega)
        rw [hjw]; exact hiw i hi s
    · have hiw' : i = w := Fin.ext (by dsimp [w]; omega)
      rw [hiw']
      by_cases hj : j.1 < 2 * p
      · exact hwj j hj s
      · have hjw : j = w := Fin.ext (by dsimp [w]; omega)
        rw [hjw]; exact hww s
  apply hφy
  rw [hφ_eval]
  simp [hM_zero]

/- ### Part 5: Bridge between Holor ℂ [3, 2p+1, 2p+1] and TensorIdx p → ℂ -/

private def holorIdxEquiv (p : ℕ) : HolorIndex [3, 2 * p + 1, 2 * p + 1] ≃ TensorIdx p where
  toFun t := match t with
    | ⟨[s, i, j], h⟩ =>
      (⟨s, (List.forall₂_cons.mp h).1⟩,
       ⟨i, (List.forall₂_cons.mp (List.forall₂_cons.mp h).2).1⟩,
       ⟨j, (List.forall₂_cons.mp (List.forall₂_cons.mp (List.forall₂_cons.mp h).2).2).1⟩)
  invFun := fun ⟨s, i, j⟩ =>
    ⟨[s.1, i.1, j.1], List.Forall₂.cons s.2 (List.Forall₂.cons i.2 (List.Forall₂.cons j.2 List.Forall₂.nil))⟩
  left_inv t := by
    rcases t with ⟨is, his⟩
    cases his with
    | cons hs his1 =>
      cases his1 with
      | cons hi his2 =>
        cases his2 with
        | cons hj his3 =>
          cases his3
          rfl
  right_inv := fun ⟨s, i, j⟩ => by
    rfl

private noncomputable def holorHomeo (p : ℕ) :
    Holor ℂ [3, 2 * p + 1, 2 * p + 1] ≃ₜ (TensorIdx p → ℂ) :=
  piHomeo (holorIdxEquiv p)

private def vecToHolor {d : ℕ} (v : Fin d → ℂ) : Holor ℂ [d] :=
  fun t => match t with
    | ⟨[i], h⟩ => v ⟨i, (List.forall₂_cons.mp h).1⟩

private def oneHolor : Holor ℂ [] := fun _ => 1

private def rank1Holor (p : ℕ) (a : Fin 3 → ℂ) (b c : Fin (2 * p + 1) → ℂ) :
    Holor ℂ [3, 2 * p + 1, 2 * p + 1] :=
  Holor.mul (vecToHolor a) (Holor.mul (vecToHolor b) (Holor.mul (vecToHolor c) oneHolor))

private lemma rank1Holor_cprankMax1 (p : ℕ) (a : Fin 3 → ℂ) (b c : Fin (2 * p + 1) → ℂ) :
    Holor.CPRankMax1 (rank1Holor p a b c) :=
  Holor.CPRankMax1.cons _ _ (Holor.CPRankMax1.cons _ _
    (Holor.CPRankMax1.cons _ _ (Holor.CPRankMax1.nil _)))

private lemma rank1Holor_apply (p : ℕ) (a : Fin 3 → ℂ) (b c : Fin (2 * p + 1) → ℂ)
    (s : Fin 3) (i j : Fin (2 * p + 1)) :
    rank1Holor p a b c ((holorIdxEquiv p).symm (s, i, j)) = a s * b i * c j := by
  change a s * (b i * (c j * 1)) = a s * b i * c j
  ring

private lemma holor_sum_apply {β : Type*} {ds : List ℕ} [DecidableEq β]
    (s : Finset β) (f : β → Holor ℂ ds) (t : HolorIndex ds) :
    (∑ r ∈ s, f r) t = ∑ r ∈ s, f r t := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact congrArg (f a t + ·) ih

private lemma cprank_le_of_mem_range (p : ℕ) (T : Holor ℂ [3, 2 * p + 1, 2 * p + 1])
    (hmem : holorHomeo p T ∈ Set.range (tensorMap p)) :
    T.cprank ≤ 3 * p + 2 := by
  classical
  obtain ⟨x, hx⟩ := hmem
  let f : Fin (3 * p + 2) → Holor ℂ [3, 2 * p + 1, 2 * p + 1] :=
    fun r => rank1Holor p
      (fun s => x (r, Sum.inl s))
      (fun i => x (r, Sum.inr (Sum.inl i)))
      (fun j => x (r, Sum.inr (Sum.inr j)))
  have hT_eq : T = ∑ r : Fin (3 * p + 2), f r := by
    funext t
    have ht : t = (holorIdxEquiv p).symm (holorIdxEquiv p t) :=
      ((holorIdxEquiv p).symm_apply_apply t).symm
    rw [ht]
    set idx := holorIdxEquiv p t
    rcases idx with ⟨s, i, j⟩
    have hxij := congrFun hx (s, i, j)
    have hhomeo : holorHomeo p T (s, i, j) = T ((holorIdxEquiv p).symm (s, i, j)) := rfl
    rw [hhomeo] at hxij
    rw [← hxij, holor_sum_apply]
    change (∑ r : Fin (3 * p + 2),
      x (r, Sum.inl s) * x (r, Sum.inr (Sum.inl i)) * x (r, Sum.inr (Sum.inr j))) =
      ∑ r : Fin (3 * p + 2), f r ((holorIdxEquiv p).symm (s, i, j))
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp only [f]
    exact (rank1Holor_apply p (fun s => x (r, Sum.inl s))
      (fun i => x (r, Sum.inr (Sum.inl i))) (fun j => x (r, Sum.inr (Sum.inr j))) s i j).symm
  have hcprank : Holor.CPRankMax (3 * p + 2) T := by
    rw [hT_eq]
    have h := Holor.cprankMax_sum (Finset.univ : Finset (Fin (3 * p + 2))) f
      (fun r _ => Holor.cprankMax_1 (rank1Holor_cprankMax1 p _ _ _))
    simpa using h
  unfold Holor.cprank
  exact Nat.find_min' _ hcprank

theorem h2_proof : OMA.R_Arxiv_0805_3777_isGenericRank_three_odd_R1.H2 := by
  intro p hp
  have hopen := open_subset_range_of_surjective_fderiv
    (tensorMap_hasStrictFDerivAt p (basePoint p))
    (tensorDeriv_basePoint_surjective p hp)
  have hopen_eval : ∃ U : Set (TensorIdx p → ℂ), IsOpen U ∧ U.Nonempty ∧
      U ⊆ Set.range (fun x : ParamIdx p → ℂ => fun j : TensorIdx p =>
        MvPolynomial.eval x (tensorMapPoly p j)) := by
    obtain ⟨U, hUo, hUne, hUsub⟩ := hopen
    refine ⟨U, hUo, hUne, ?_⟩
    intro y hy
    obtain ⟨x, rfl⟩ := hUsub hy
    refine ⟨x, ?_⟩
    funext idx
    exact tensorMap_eq_eval p x idx
  obtain ⟨V₀, hV₀open, hV₀dense, hV₀sub⟩ :=
    exists_dense_open_subset_range_of_open_in_range (tensorMapPoly p) hopen_eval
  refine ⟨holorHomeo p ⁻¹' V₀, hV₀open.preimage (holorHomeo p).continuous,
    hV₀dense.preimage (holorHomeo p).isOpenMap, ?_⟩
  intro T hT
  refine cprank_le_of_mem_range p T ?_
  obtain ⟨x, hx⟩ := hV₀sub hT
  refine ⟨x, ?_⟩
  funext idx
  rw [← tensorMap_eq_eval p x idx]
  exact congrFun hx idx

end OMA.ThreeOddUpper

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_three_odd_R1.H2 :=
  OMA.ThreeOddUpper.h2_proof
