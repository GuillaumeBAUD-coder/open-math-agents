import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1
import Mathlib

/-!
# Simple connectivity of the 3-sphere `S^3`

Proves `OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1.H1`:
`SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)`.

Every punctured sphere `S^3 \ {p}` is contractible via normalized straight-line deformation to `-p`.
Any loop `γ` on `S^3` is uniformly continuous, hence homotopic rel `{0, 1}` to a piecewise
normalized-chordal loop `γ̃` whose image lies in a finite union of 2-dimensional linear subspaces
of `ℝ^4`. Using the moment curve `r ↦ (1, r, r^2, r^3)`, we find `p ∈ S^3` avoiding all of these
subspaces, so `γ̃` factors through the contractible (hence simply connected) space `S^3 \ {p}` and
is null-homotopic.
-/

namespace Sphere3SimplyConnected

open Metric Set Topology
open scoped unitInterval RealInnerProductSpace

abbrev E := EuclideanSpace ℝ (Fin 4)
abbrev S := Metric.sphere (0 : E) 1

private lemma norm_eq_one (x : S) : ‖x.1‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using x.2

private noncomputable def toSphere (v : E) (hv : v ≠ 0) : S :=
  ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

private lemma toSphere_self (x : S) (hx : x.1 ≠ 0) : toSphere x.1 hx = x := by
  ext1
  simp [toSphere, norm_eq_one x]

private lemma chord_ne_zero {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hne : a ≠ -b) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) • a + s • b ≠ 0 := by
  intro h
  have heq : (1 - s) • a = s • (-b) := by
    rw [smul_neg, eq_neg_iff_add_eq_zero]
    exact h
  have hnorm : ‖(1 - s) • a‖ = ‖s • (-b)‖ := congrArg norm heq
  rw [norm_smul, norm_smul, norm_neg, ha, hb, mul_one, mul_one,
    Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0] at hnorm
  have hs : s = 1 / 2 := by linarith
  rw [hs] at heq
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h12] at heq
  exact hne (smul_right_injective E (by norm_num : (1 / 2 : ℝ) ≠ 0) heq)

private lemma chord_ne_point {x p : S} (hxp : x ≠ p) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let v := (1 - s) • x.1 + s • (-p.1)
    ∀ hv : v ≠ 0, toSphere v hv ≠ p := by
  intro v hv hEq
  have hval : ‖v‖⁻¹ • v = p.1 := congrArg Subtype.val hEq
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hveq : (1 - s) • x.1 + s • (-p.1) = ‖v‖ • p.1 := by
    have := congrArg (‖v‖ • ·) hval
    rwa [smul_inv_smul₀ hvpos.ne'] at this
  have h1 : (1 - s) • x.1 = (‖v‖ + s) • p.1 := by
    rw [add_smul, ← hveq, smul_neg]
    abel
  have hnorm : ‖(1 - s) • x.1‖ = ‖(‖v‖ + s) • p.1‖ := congrArg norm h1
  rw [norm_smul, norm_smul, norm_eq_one x, norm_eq_one p, mul_one, mul_one,
    Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)] at hnorm
  have h1s_pos : 0 < 1 - s := by linarith
  rw [← hnorm] at h1
  exact hxp (Subtype.ext (smul_right_injective E h1s_pos.ne' h1))

private lemma neg_mem_sphere (p : S) : -p.1 ∈ S := by
  rw [Metric.mem_sphere, dist_zero_right, norm_neg, norm_eq_one p]

private lemma neg_ne_self (p : S) : (⟨-p.1, neg_mem_sphere p⟩ : S) ≠ p := by
  intro h
  have hval : -p.1 = p.1 := congrArg Subtype.val h
  have h0 : (2 : ℝ) • p.1 = 0 := by
    rw [two_smul]
    calc p.1 + p.1 = p.1 + (-p.1) := by rw [hval]
      _ = 0 := add_neg_cancel _
  have hp0 : p.1 = 0 := (smul_eq_zero.mp h0).resolve_left (by norm_num)
  have h1 := norm_eq_one p
  rw [hp0, norm_zero] at h1
  norm_num at h1

private lemma punctured_contractible (p : S) : ContractibleSpace {x : S // x ≠ p} := by
  rw [contractible_iff_id_nullhomotopic]
  let y₀ : {x : S // x ≠ p} := ⟨⟨-p.1, neg_mem_sphere p⟩, neg_ne_self p⟩
  refine ⟨y₀, ⟨{
    toFun := fun q =>
      let s : ℝ := q.1.1
      let x : {x : S // x ≠ p} := q.2
      have hv : (1 - s) • x.1.1 + s • (-p.1) ≠ 0 := by
        apply chord_ne_zero (norm_eq_one x.1) (by rw [norm_neg, norm_eq_one p])
        · rw [neg_neg]; exact fun h => x.2 (Subtype.ext h)
        · exact q.1.2.1
        · exact q.1.2.2
      ⟨toSphere _ hv, chord_ne_point x.2 q.1.2.1 q.1.2.2 hv⟩
    continuous_toFun := by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      have hcont_v : Continuous (fun q : I × {x : S // x ≠ p} =>
          (1 - (q.1 : ℝ)) • q.2.1.1 + (q.1 : ℝ) • (-p.1)) := by
        fun_prop
      have hne_v : ∀ q : I × {x : S // x ≠ p},
          (1 - (q.1 : ℝ)) • q.2.1.1 + (q.1 : ℝ) • (-p.1) ≠ 0 := fun q => by
        apply chord_ne_zero (norm_eq_one q.2.1) (by rw [norm_neg, norm_eq_one p])
        · rw [neg_neg]; exact fun h => q.2.2 (Subtype.ext h)
        · exact q.1.2.1
        · exact q.1.2.2
      exact (hcont_v.norm.inv₀ fun q => norm_ne_zero_iff.mpr (hne_v q)).smul hcont_v
    map_zero_left := fun x => by
      apply Subtype.ext; apply Subtype.ext
      simp [toSphere, norm_eq_one x.1]
    map_one_left := fun x => by
      apply Subtype.ext; apply Subtype.ext
      simp [toSphere, y₀, norm_eq_one p]
  }⟩⟩

private noncomputable def basisPt (i : Fin 4) : S :=
  ⟨EuclideanSpace.single i (1 : ℝ), by
    rw [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

private lemma basisPt_inj : Function.Injective basisPt := by
  intro i j h
  have hv : EuclideanSpace.single i (1 : ℝ) = EuclideanSpace.single j (1 : ℝ) :=
    congrArg Subtype.val h
  by_contra hij
  have := congrArg (fun v : E => v.ofLp i) hv
  simp [EuclideanSpace.single_apply, hij] at this

private lemma pathConnected_S : PathConnectedSpace S := by
  refine ⟨⟨basisPt 0⟩, fun x y => ?_⟩
  have hex : ∃ i : Fin 4, basisPt i ≠ x ∧ basisPt i ≠ y := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin 4)).image basisPt ⊆ ({x, y} : Finset S) := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      by_cases hx : basisPt i = x
      · simp [hx]
      · simp [h i hx]
    have hc1 : ((Finset.univ : Finset (Fin 4)).image basisPt).card = 4 := by
      rw [Finset.card_image_of_injective _ basisPt_inj, Finset.card_univ, Fintype.card_fin]
    have hc2 : ({x, y} : Finset S).card ≤ 2 := Finset.card_le_two
    have := Finset.card_le_card hsub
    omega
  obtain ⟨i, hix, hiy⟩ := hex
  haveI : ContractibleSpace {z : S // z ≠ basisPt i} := punctured_contractible (basisPt i)
  haveI : SimplyConnectedSpace {z : S // z ≠ basisPt i} :=
    SimplyConnectedSpace.ofContractible _
  have hjoin : Joined (⟨x, hix.symm⟩ : {z : S // z ≠ basisPt i}) ⟨y, hiy.symm⟩ :=
    PathConnectedSpace.joined _ _
  obtain ⟨γ⟩ := hjoin
  exact ⟨γ.map continuous_subtype_val⟩

private lemma exists_avoiding_point {N : ℕ} (a b : Fin N → E) :
    ∃ p : S, ∀ k : Fin N, ∀ c d : ℝ, p.1 ≠ c • a k + d • b k := by
  have horth : ∀ k : Fin N, ∃ w : E, w ≠ 0 ∧ inner ℝ w (a k) = 0 ∧ inner ℝ w (b k) = 0 := by
    intro k
    let W : Submodule ℝ E := Submodule.span ℝ ({a k, b k} : Set E)
    have hdimW : Module.finrank ℝ W ≤ 2 := by
      calc Module.finrank ℝ W
          ≤ ({a k, b k} : Finset E).card := by
            have := finrank_span_le_card (R := ℝ) ({a k, b k} : Set E)
            simpa [W, Set.toFinset_insert, Set.toFinset_singleton] using this
        _ ≤ 2 := Finset.card_le_two
    have hdimE : Module.finrank ℝ E = 4 := by
      simp [E]
    have hsum := Submodule.finrank_add_finrank_orthogonal W
    have hpos : 0 < Module.finrank ℝ Wᗮ := by omega
    have hnt : Nontrivial Wᗮ := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : Wᗮ)
    refine ⟨w, fun h => hw0 (Subtype.ext h), ?_, ?_⟩
    · rw [real_inner_comm]
      exact hw (a k) (Submodule.subset_span (by simp))
    · rw [real_inner_comm]
      exact hw (b k) (Submodule.subset_span (by simp))
  choose w hw0 hwa hwb using horth
  -- Moment curve `v r = (1, r, r^2, r^3)`
  let v : ℝ → E := fun r => WithLp.toLp 2 ![1, r, r ^ 2, r ^ 3]
  let P : Fin N → Polynomial ℝ := fun k =>
    Polynomial.C ((w k).ofLp 0) + Polynomial.C ((w k).ofLp 1) * Polynomial.X +
    Polynomial.C ((w k).ofLp 2) * Polynomial.X ^ 2 + Polynomial.C ((w k).ofLp 3) * Polynomial.X ^ 3
  have hPeval : ∀ k r, (P k).eval r = inner ℝ (w k) (v r) := by
    intro k r
    simp only [P, v, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_four, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    ring
  have hPne : ∀ k, P k ≠ 0 := by
    intro k h0
    apply hw0 k
    ext i
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff i.1) h0
    fin_cases i <;>
      simp [P, Polynomial.coeff_X, Polynomial.coeff_X_pow] at hc <;>
      exact hc
  let bad : Finset ℝ := Finset.univ.biUnion fun k : Fin N => (P k).roots.toFinset
  have hinf : (Set.univ : Set ℝ).Infinite := Set.infinite_univ
  obtain ⟨r, -, hr⟩ := (hinf.diff bad.finite_toSet).nonempty
  have hv0 : v r ≠ 0 := by
    intro h
    have := congrArg (fun u : E => u.ofLp 0) h
    simp [v] at this
  refine ⟨toSphere (v r) hv0, fun k c d hEq => ?_⟩
  have hinner0 : inner ℝ (w k) (toSphere (v r) hv0).1 = 0 := by
    rw [hEq, inner_add_right, inner_smul_right, inner_smul_right, hwa k, hwb k]
    ring
  have hvr0 : inner ℝ (w k) (v r) = 0 := by
    simp only [toSphere, inner_smul_right] at hinner0
    exact (mul_eq_zero.mp hinner0).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hv0))
  have hroot : r ∈ (P k).roots := by
    rw [Polynomial.mem_roots (hPne k), Polynomial.IsRoot, hPeval k r]
    exact hvr0
  exact hr (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, Multiset.mem_toFinset.mpr hroot⟩))

private lemma loop_nullhomotopic (x₀ : S) (γ : Path x₀ x₀) :
    Path.Homotopic γ (Path.refl x₀) := by
  have huc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp huc (1 / 2) (by norm_num)
  let N : ℕ := ⌈1 / δ⌉₊ + 1
  have hNpos : 0 < N := Nat.succ_pos _
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNδ : 1 / (N : ℝ) < δ := by
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil (1 / δ)
    have h2 : (⌈1 / δ⌉₊ : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self _
    have h3 : 1 / δ < (N : ℝ) := lt_of_le_of_lt h1 h2
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hδpos] at h3
    linarith
  let pt : ℕ → I := fun j =>
    ⟨min ((j : ℝ) / (N : ℝ)) 1,
      le_min (div_nonneg (Nat.cast_nonneg j) hNR.le) zero_le_one,
      min_le_right _ _⟩
  have hpt_val : ∀ j ≤ N, (pt j : ℝ) = (j : ℝ) / (N : ℝ) := by
    intro j hj
    exact min_eq_left ((div_le_one hNR).mpr (by exact_mod_cast hj))
  have hpt0 : pt 0 = 0 := by ext; simp [pt]
  have hptN : pt N = 1 := by ext; simp [pt, div_self hNR.ne']
  -- Piecewise linear chord function `L : I → E`
  let L : I → E := fun t =>
    let k := min ⌊(N : ℝ) * (t : ℝ)⌋₊ (N - 1)
    let u := (N : ℝ) * (t : ℝ) - (k : ℝ)
    (1 - u) • (γ (pt k)).1 + u • (γ (pt (k + 1))).1
  have hL_on_seg : ∀ (k : Fin N) (t : I),
      (k : ℝ) / (N : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ ((k : ℝ) + 1) / (N : ℝ) →
      L t = (1 - ((N : ℝ) * (t : ℝ) - (k : ℝ))) • (γ (pt k)).1 +
            ((N : ℝ) * (t : ℝ) - (k : ℝ)) • (γ (pt (k + 1))).1 := by
    intro k t hlo hhi
    have hlo' : (k : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
      rwa [div_le_iff₀ hNR, mul_comm] at hlo
    have hhi' : (N : ℝ) * (t : ℝ) ≤ (k : ℝ) + 1 := by
      rwa [le_div_iff₀ hNR, mul_comm] at hhi
    by_cases hlt : (N : ℝ) * (t : ℝ) < (k : ℝ) + 1
    · have hfl : ⌊(N : ℝ) * (t : ℝ)⌋₊ = k.1 :=
        (Nat.floor_eq_iff (mul_nonneg hNR.le t.2.1)).mpr ⟨hlo', hlt⟩
      have hmin : min ⌊(N : ℝ) * (t : ℝ)⌋₊ (N - 1) = k.1 := by
        rw [hfl]; exact min_eq_left (Nat.le_sub_one_of_lt k.2)
      simp only [L, hmin]
    · have heq : (N : ℝ) * (t : ℝ) = (k : ℝ) + 1 := le_antisymm hhi' (le_of_not_gt hlt)
      have hfl : ⌊(N : ℝ) * (t : ℝ)⌋₊ = k.1 + 1 := by
        rw [heq]; exact_mod_cast Nat.floor_natCast (k.1 + 1)
      by_cases hlast : k.1 + 1 = N
      · have hmin : min ⌊(N : ℝ) * (t : ℝ)⌋₊ (N - 1) = k.1 := by
          rw [hfl]; omega
        simp only [L, hmin]
      · have hmin : min ⌊(N : ℝ) * (t : ℝ)⌋₊ (N - 1) = k.1 + 1 := by
          rw [hfl]; omega
        dsimp only [L]
        rw [hmin, heq]
        push_cast
        simp
  have hL_cont : Continuous L := by
    rw [continuous_iff_isClosed]
    intro s hs
    let seg : Fin N → Set I := fun k =>
      {t : I | (k : ℝ) / (N : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ ((k : ℝ) + 1) / (N : ℝ)}
    have hcov : ∀ t : I, ∃ k : Fin N, t ∈ seg k := by
      intro t
      let k := min ⌊(N : ℝ) * (t : ℝ)⌋₊ (N - 1)
      refine ⟨⟨k, by omega⟩, ?_, ?_⟩
      · change (k : ℝ) / (N : ℝ) ≤ (t : ℝ)
        rw [div_le_iff₀ hNR, mul_comm]
        exact le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le (mul_nonneg hNR.le t.2.1))
      · change (t : ℝ) ≤ ((k : ℝ) + 1) / (N : ℝ)
        rw [le_div_iff₀ hNR, mul_comm]
        by_cases h : ⌊(N : ℝ) * (t : ℝ)⌋₊ ≤ N - 1
        · have hk : k = ⌊(N : ℝ) * (t : ℝ)⌋₊ := min_eq_left h
          rw [hk]; exact (Nat.lt_floor_add_one _).le
        · have hk : k = N - 1 := min_eq_right (le_of_not_ge h)
          have h1 : (k : ℝ) + 1 = (N : ℝ) := by exact_mod_cast (show k + 1 = N by omega)
          rw [h1]; nlinarith [t.2.2]
    have hpre : L ⁻¹' s = ⋃ k : Fin N, (seg k ∩
        (fun t : I => (1 - ((N : ℝ) * (t : ℝ) - (k : ℝ))) • (γ (pt k)).1 +
          ((N : ℝ) * (t : ℝ) - (k : ℝ)) • (γ (pt (k + 1))).1) ⁻¹' s) := by
      ext t
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      constructor
      · intro ht
        obtain ⟨k, hk⟩ := hcov t
        exact ⟨k, hk, by rwa [← hL_on_seg k t hk.1 hk.2]⟩
      · rintro ⟨k, hk, ht⟩
        rwa [hL_on_seg k t hk.1 hk.2]
    rw [hpre]
    refine isClosed_iUnion_of_finite fun k => ?_
    have hseg_closed : IsClosed (seg k) :=
      (isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)
    have hcont_k : Continuous (fun t : I =>
        (1 - ((N : ℝ) * (t : ℝ) - (k : ℝ))) • (γ (pt k)).1 +
        ((N : ℝ) * (t : ℝ) - (k : ℝ)) • (γ (pt (k + 1))).1) := by fun_prop
    exact hseg_closed.inter (hs.preimage hcont_k)
  -- Distance bounds on each segment
  have hL_bounds : ∀ t : I, ∃ k : Fin N,
      L t = (1 - ((N : ℝ) * (t : ℝ) - (k : ℝ))) • (γ (pt k)).1 +
            ((N : ℝ) * (t : ℝ) - (k : ℝ)) • (γ (pt (k + 1))).1 ∧
      0 ≤ (N : ℝ) * (t : ℝ) - (k : ℝ) ∧ (N : ℝ) * (t : ℝ) - (k : ℝ) ≤ 1 ∧
      dist (γ t) (γ (pt k)) < 1 / 2 ∧ dist (γ (pt (k + 1))) (γ (pt k)) < 1 / 2 := by
    intro t
    let k_nat := min ⌊(N : ℝ) * (t : ℝ)⌋₊ (N - 1)
    let k : Fin N := ⟨k_nat, by omega⟩
    have hlo : (k : ℝ) / (N : ℝ) ≤ (t : ℝ) := by
      rw [div_le_iff₀ hNR, mul_comm]
      exact le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le (mul_nonneg hNR.le t.2.1))
    have hhi : (t : ℝ) ≤ ((k : ℝ) + 1) / (N : ℝ) := by
      rw [le_div_iff₀ hNR, mul_comm]
      by_cases h : ⌊(N : ℝ) * (t : ℝ)⌋₊ ≤ N - 1
      · have hk : k_nat = ⌊(N : ℝ) * (t : ℝ)⌋₊ := min_eq_left h
        change (N : ℝ) * (t : ℝ) ≤ (k_nat : ℝ) + 1
        rw [hk]; exact (Nat.lt_floor_add_one _).le
      · have hk : k_nat = N - 1 := min_eq_right (le_of_not_ge h)
        have h1 : (k_nat : ℝ) + 1 = (N : ℝ) := by exact_mod_cast (show k_nat + 1 = N by omega)
        change (N : ℝ) * (t : ℝ) ≤ (k_nat : ℝ) + 1
        rw [h1]; nlinarith [t.2.2]
    have hu0 : 0 ≤ (N : ℝ) * (t : ℝ) - (k : ℝ) := by
      rw [div_le_iff₀ hNR, mul_comm] at hlo; linarith
    have hu1 : (N : ℝ) * (t : ℝ) - (k : ℝ) ≤ 1 := by
      rw [le_div_iff₀ hNR, mul_comm] at hhi; linarith
    have hd1 : dist t (pt k) < δ := by
      rw [Subtype.dist_eq, Real.dist_eq, hpt_val k (le_of_lt k.2),
        abs_of_nonneg (by linarith)]
      have : (t : ℝ) - (k : ℝ) / (N : ℝ) ≤ 1 / (N : ℝ) := by
        have hdiv : ((k : ℝ) + 1) / (N : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by ring
        linarith
      exact lt_of_le_of_lt this hNδ
    have hd2 : dist (pt (k + 1)) (pt k) < δ := by
      rw [Subtype.dist_eq, Real.dist_eq, hpt_val (k + 1) k.2, hpt_val k (le_of_lt k.2)]
      push_cast
      have hsub : ((k : ℝ) + 1) / (N : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by ring
      rw [hsub, abs_of_pos (div_pos one_pos hNR)]
      exact hNδ
    exact ⟨k, hL_on_seg k t hlo hhi, hu0, hu1, hδ hd1, hδ hd2⟩
  have hL_norm : ∀ t : I, 1 / 2 < ‖L t‖ ∧ ‖L t‖ ≤ 1 := by
    intro t
    obtain ⟨k, hL, hu0, hu1, _, hd2⟩ := hL_bounds t
    set u := (N : ℝ) * (t : ℝ) - (k : ℝ)
    have hdiff : L t - (γ (pt k)).1 = u • ((γ (pt (k + 1))).1 - (γ (pt k)).1) := by
      rw [hL, smul_sub, sub_smul, one_smul]; abel
    have hndiff : ‖L t - (γ (pt k)).1‖ < 1 / 2 := by
      rw [hdiff, norm_smul, Real.norm_of_nonneg hu0]
      have hd2' : ‖(γ (pt (k + 1))).1 - (γ (pt k)).1‖ < 1 / 2 := by
        simpa [Subtype.dist_eq, dist_eq_norm] using hd2
      nlinarith [norm_nonneg ((γ (pt (k + 1))).1 - (γ (pt k)).1)]
    constructor
    · have htri := norm_sub_norm_le (γ (pt k)).1 (L t)
      rw [norm_eq_one, norm_sub_rev] at htri
      linarith
    · rw [hL]
      calc ‖(1 - u) • (γ (pt k)).1 + u • (γ (pt (k + 1))).1‖
          ≤ ‖(1 - u) • (γ (pt k)).1‖ + ‖u • (γ (pt (k + 1))).1‖ := norm_add_le _ _
        _ = (1 - u) * 1 + u * 1 := by
            rw [norm_smul, norm_smul, norm_eq_one, norm_eq_one,
              Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hu0]
        _ = 1 := by ring
  have hL_ne : ∀ t : I, L t ≠ 0 := fun t =>
    norm_pos_iff.mp (lt_trans (by norm_num) (hL_norm t).1)
  have hL0 : L 0 = x₀.1 := by
    have h := hL_on_seg ⟨0, hNpos⟩ 0 (by simp) (by positivity)
    simp only [Fin.val_zero, Nat.cast_zero, Set.Icc.coe_zero, mul_zero, sub_zero, one_smul,
      zero_smul, add_zero, hpt0, γ.source] at h
    exact h
  have hL1 : L 1 = x₀.1 := by
    have h := hL_on_seg ⟨N - 1, Nat.sub_lt hNpos one_pos⟩ 1
      ((div_le_one hNR).mpr (by exact_mod_cast Nat.sub_le N 1))
      (by
        have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hNpos
        simp [hN1, div_self hNR.ne'])
    have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hNpos
    have hu : (N : ℝ) * (1 : ℝ) - ((N - 1 : ℕ) : ℝ) = 1 := by linarith
    have hk1 : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
    simp only [Set.Icc.coe_one, hu, sub_self, zero_smul, one_smul, zero_add, hk1, hptN, γ.target] at h
    exact h
  let γtilde : Path x₀ x₀ := {
    toFun := fun t => toSphere (L t) (hL_ne t)
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact (hL_cont.norm.inv₀ fun t => norm_ne_zero_iff.mpr (hL_ne t)).smul hL_cont
    source' := by
      ext1; simp [toSphere, hL0, norm_eq_one x₀]
    target' := by
      ext1; simp [toSphere, hL1, norm_eq_one x₀]
  }
  -- Straight-line homotopy `γ ~ γtilde`
  have hne_hom : ∀ t : I, (γ t).1 ≠ -(γtilde t).1 := by
    intro t heq
    obtain ⟨k, hL, hu0, hu1, hd1, hd2⟩ := hL_bounds t
    set u := (N : ℝ) * (t : ℝ) - (k : ℝ)
    have hdiff1 : ‖L t - (γ (pt k)).1‖ < 1 / 2 := by
      have hdiff : L t - (γ (pt k)).1 = u • ((γ (pt (k + 1))).1 - (γ (pt k)).1) := by
        rw [hL, smul_sub, sub_smul, one_smul]; abel
      rw [hdiff, norm_smul, Real.norm_of_nonneg hu0]
      have hd2' : ‖(γ (pt (k + 1))).1 - (γ (pt k)).1‖ < 1 / 2 := by
        simpa [Subtype.dist_eq, dist_eq_norm] using hd2
      nlinarith [norm_nonneg ((γ (pt (k + 1))).1 - (γ (pt k)).1)]
    have hdiff2 : ‖(γ t).1 - (γ (pt k)).1‖ < 1 / 2 := by
      simpa [Subtype.dist_eq, dist_eq_norm] using hd1
    have hdiff3 : ‖(γtilde t).1 - L t‖ < 1 / 2 := by
      have hnormL := hL_norm t
      have hne0 : ‖L t‖ ≠ 0 := (lt_trans (by norm_num) hnormL.1).ne'
      have h1 : (γtilde t).1 - L t = (‖L t‖⁻¹ - 1) • L t := by
        change ‖L t‖⁻¹ • L t - L t = _
        rw [sub_smul, one_smul]
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by
        have : 1 ≤ ‖L t‖⁻¹ := (one_le_inv₀ (lt_trans (by norm_num) hnormL.1)).mpr hnormL.2
        linarith)]
      rw [sub_mul, inv_mul_cancel₀ hne0, one_mul]
      linarith
    have h2 : ‖(γ t).1 - (γtilde t).1‖ = 2 := by
      have hneg : -(γtilde t).1 - (γtilde t).1 = (-(2 : ℝ)) • (γtilde t).1 := by
        rw [neg_smul, two_smul, neg_add]
        abel
      rw [heq, hneg, norm_smul, norm_neg, Real.norm_ofNat, norm_eq_one]
      norm_num
    have htri : ‖(γ t).1 - (γtilde t).1‖ ≤
        ‖(γ t).1 - (γ (pt k)).1‖ + ‖(γ (pt k)).1 - L t‖ + ‖L t - (γtilde t).1‖ := by
      have h1 : ‖(γ t).1 - (γtilde t).1‖ ≤
          ‖((γ t).1 - (γ (pt k)).1) + ((γ (pt k)).1 - L t)‖ + ‖L t - (γtilde t).1‖ := by
        have heq3 : (γ t).1 - (γtilde t).1 =
            ((γ t).1 - (γ (pt k)).1) + ((γ (pt k)).1 - L t) + (L t - (γtilde t).1) := by abel
        rw [heq3]
        exact norm_add_le _ _
      have h2' := norm_add_le ((γ t).1 - (γ (pt k)).1) ((γ (pt k)).1 - L t)
      linarith
    rw [norm_sub_rev (γ (pt k)).1 (L t), norm_sub_rev (L t) (γtilde t).1] at htri
    linarith
  have hhom1 : Path.Homotopic γ γtilde := ⟨{
    toFun := fun q =>
      have hv : (1 - (q.1 : ℝ)) • (γ q.2).1 + (q.1 : ℝ) • (γtilde q.2).1 ≠ 0 :=
        chord_ne_zero (norm_eq_one _) (norm_eq_one _) (hne_hom q.2) q.1.2.1 q.1.2.2
      toSphere _ hv
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      have hcv : Continuous (fun q : I × I =>
          (1 - (q.1 : ℝ)) • (γ q.2).1 + (q.1 : ℝ) • (γtilde q.2).1) := by fun_prop
      have hnev : ∀ q : I × I,
          (1 - (q.1 : ℝ)) • (γ q.2).1 + (q.1 : ℝ) • (γtilde q.2).1 ≠ 0 := fun q =>
        chord_ne_zero (norm_eq_one _) (norm_eq_one _) (hne_hom q.2) q.1.2.1 q.1.2.2
      exact (hcv.norm.inv₀ fun q => norm_ne_zero_iff.mpr (hnev q)).smul hcv
    map_zero_left := fun t => by
      ext1; simp [toSphere, norm_eq_one]
    map_one_left := fun t => by
      ext1; simp [toSphere, norm_eq_one]
    prop' := fun s t ht => by
      rcases ht with rfl | rfl
      · ext1
        simp only [γ.source, γtilde.source, toSphere]
        have h1 : (1 - (s : ℝ)) • x₀.1 + (s : ℝ) • x₀.1 = x₀.1 := by
          rw [← add_smul, sub_add_cancel, one_smul]
        simp [h1, norm_eq_one x₀]
      · ext1
        simp only [γ.target, γtilde.target, toSphere]
        have h1 : (1 - (s : ℝ)) • x₀.1 + (s : ℝ) • x₀.1 = x₀.1 := by
          rw [← add_smul, sub_add_cancel, one_smul]
        simp [h1, norm_eq_one x₀]
  }⟩
  -- Find `p ∈ S` missed by `γtilde`
  obtain ⟨p, hp⟩ := exists_avoiding_point (fun k : Fin N => (γ (pt k)).1) (fun k : Fin N => (γ (pt (k + 1))).1)
  have hmiss : ∀ t : I, γtilde t ≠ p := by
    intro t heq
    obtain ⟨k, hL, -, -, -, -⟩ := hL_bounds t
    have hval : ‖L t‖⁻¹ • L t = p.1 := congrArg Subtype.val heq
    rw [hL, smul_add, smul_smul, smul_smul] at hval
    exact hp k _ _ hval.symm
  -- Lift `γtilde` to the contractible (hence simply connected) punctured sphere `S \ {p}`
  have hx₀p : x₀ ≠ p := by simpa [γtilde.source] using hmiss 0
  let U := {z : S // z ≠ p}
  haveI : ContractibleSpace U := punctured_contractible p
  haveI : SimplyConnectedSpace U := SimplyConnectedSpace.ofContractible U
  let γU : Path (⟨x₀, hx₀p⟩ : U) ⟨x₀, hx₀p⟩ := {
    toFun := fun t => ⟨γtilde t, hmiss t⟩
    continuous_toFun := γtilde.continuous.subtype_mk _
    source' := Subtype.ext γtilde.source
    target' := Subtype.ext γtilde.target
  }
  have hhomU : Path.Homotopic γU (Path.refl (⟨x₀, hx₀p⟩ : U)) :=
    (simply_connected_iff_loops_nullhomotopic.mp inferInstance).2 (⟨x₀, hx₀p⟩ : U) γU
  have hhom2 : Path.Homotopic γtilde (Path.refl x₀) := by
    have hmap := hhomU.map ⟨Subtype.val, continuous_subtype_val⟩
    have heq1 : γU.map continuous_subtype_val = γtilde := by ext t; rfl
    have heq2 : (Path.refl (⟨x₀, hx₀p⟩ : U)).map continuous_subtype_val = Path.refl x₀ := by ext t; rfl
    rwa [heq1, heq2] at hmap
  exact hhom1.trans hhom2

theorem main_proof : SimplyConnectedSpace S :=
  simply_connected_iff_loops_nullhomotopic.mpr ⟨pathConnected_S, loop_nullhomotopic⟩

end Sphere3SimplyConnected

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1.H1 :=
  Sphere3SimplyConnected.main_proof
