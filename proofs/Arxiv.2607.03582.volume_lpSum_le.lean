import FormalConjectures.Arxiv.«2607.03582».LpRogersShephard

-- Problem: Arxiv.2607.03582.volume_lpSum_le (planar L_p Rogers-Shephard, Corollary 29)
-- Reuse: Lean proofs by Kenta Kitamura, repo KitaKen1/lp-rogers-shephard-conjectures-lean,
-- commit c646c668c0568b8533bf5534abcf02aab4d2df72, licence Apache-2.0 (Copyright the repo author).
-- Files lean4web/LpRogersShephardLean4Web.lean and lean4web/LpRogersShephardProof.lean are
-- adapted (n = 2 case of Conjecture 4); the Conjecture 5 equality part is not used.

open MeasureTheory Real Set
open scoped Pointwise ENNReal

namespace LpRogersShephardLean4Web

noncomputable section

/-! ## The centered-slice algebra used by both proofs -/

/-- Translation written as an image, to keep all subsequent set identities explicit. -/
def translate {E : Type*} [Add E] (c : E) (C : Set E) : Set E :=
  (fun x ↦ x + c) '' C

/-- The one-parameter Minkowski slice from Lemma 5.3 of arXiv:2607.20387. -/
noncomputable def slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q t : ℝ) (K : Set E) : Set E :=
  (1 - t) ^ (1 / q) • K + t ^ (1 / q) • (-K)

/-- The two-body weighted slice. -/
noncomputable def weightedSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q t : ℝ) (K L : Set E) : Set E :=
  (1 - t) ^ (1 / q) • K + t ^ (1 / q) • L

/-- The parameter-body presentation of the Firey sum. -/
noncomputable def parameterBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (K L : Set E) : Set E :=
  {z | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ x ∈ K, ∃ y ∈ L,
    z = (1 - t) ^ (1 / q) • x + t ^ (1 / q) • y}

lemma mem_parameterBody_iff_mem_weightedSlice {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℝ} {K L : Set E} {z : E} :
    z ∈ parameterBody q K L ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, z ∈ weightedSlice q t K L := by
  simp only [parameterBody, weightedSlice, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, x, hx, y, hy, rfl⟩
    exact ⟨t, ht, _, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨t, ht, ax, ⟨x, hx, rfl⟩, bz, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨t, ht, x, hx, y, hy, rfl⟩

lemma parameterBody_neg (q : ℝ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) :
    parameterBody q K (-K) = ⋃ t ∈ Set.Icc (0 : ℝ) 1, slice q t K := by
  ext z
  simp only [mem_parameterBody_iff_mem_weightedSlice, Set.mem_iUnion, slice, weightedSlice]
  aesop

/-- Generic support function.  The specialized definitions below unfold to this expression. -/
noncomputable def supportFunctionE {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (u : E) : ℝ :=
  ⨆ x : K, inner ℝ (x : E) u

/-- Generic half-space definition of the Firey `L_p` sum. -/
noncomputable def lpSumE {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ℝ) (K L : Set E) : Set E :=
  {x | ∀ u : E,
    inner ℝ x u ≤ (supportFunctionE K u ^ p + supportFunctionE L u ^ p) ^ (1 / p)}

lemma bddAbove_inner_range {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E} (hK : IsCompact K) (u : E) :
    BddAbove (Set.range (fun x : K ↦ inner ℝ (x : E) u)) := by
  have hcont : ContinuousOn (fun x : E ↦ inner ℝ x u) K := by fun_prop
  have hbdd := hK.bddAbove_image hcont
  rw [show Set.range (fun x : K ↦ inner ℝ (x : E) u) =
      (fun x : E ↦ inner ℝ x u) '' K by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩]
  exact hbdd

lemma inner_le_supportFunctionE {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E} (hK : IsCompact K) {x : E} (hx : x ∈ K) (u : E) :
    inner ℝ x u ≤ supportFunctionE K u := by
  exact le_ciSup (bddAbove_inner_range hK u) ⟨x, hx⟩

lemma supportFunctionE_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E} (hK : IsCompact K) (h0 : 0 ∈ K) (u : E) :
    0 ≤ supportFunctionE K u := by
  simpa using inner_le_supportFunctionE hK h0 u

lemma exists_inner_eq_supportFunctionE {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E} (hK : IsCompact K) (hKn : K.Nonempty) (u : E) :
    ∃ x ∈ K, inner ℝ x u = supportFunctionE K u := by
  letI : Nonempty K := hKn.to_subtype
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKn (by fun_prop : ContinuousOn (fun z : E ↦ inner ℝ z u) K)
  refine ⟨x, hx, le_antisymm (inner_le_supportFunctionE hK hx u) ?_⟩
  exact ciSup_le fun y ↦ hmax y.property

set_option maxHeartbeats 800000 in
/-- The two-coordinate Hölder inequality in exactly the normalization used by the slices. -/
lemma holder_slice_bound (p q t A B : ℝ) (hpq : p.HolderConjugate q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) ^ (1 / q) * A + t ^ (1 / q) * B ≤ (A ^ p + B ^ p) ^ (1 / p) := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  let f : Fin 2 → NNReal := ![(⟨A, hA⟩ : NNReal), (⟨B, hB⟩ : NNReal)]
  let g : Fin 2 → NNReal :=
    ![(⟨(1 - t) ^ (1 / q), Real.rpow_nonneg hsub _⟩ : NNReal),
      (⟨t ^ (1 / q), Real.rpow_nonneg ht0 _⟩ : NNReal)]
  have f0coe : (f 0 : ℝ) = A := rfl
  have f1coe : (f 1 : ℝ) = B := rfl
  have g0coe : (g 0 : ℝ) = (1 - t) ^ (1 / q) := rfl
  have g1coe : (g 1 : ℝ) = t ^ (1 / q) := rfl
  have h := NNReal.inner_le_Lp_mul_Lq (Finset.univ : Finset (Fin 2)) f g hpq
  have hg : ∑ i, g i ^ q = 1 := by
    apply NNReal.eq
    rw [NNReal.coe_one, NNReal.coe_sum, Fin.sum_univ_two,
      NNReal.coe_rpow, NNReal.coe_rpow, g0coe, g1coe]
    rw [← Real.rpow_mul hsub, ← Real.rpow_mul ht0]
    rw [one_div]
    rw [inv_mul_cancel₀ hpq.symm.ne_zero]
    simp
  rw [hg] at h
  have hR := (NNReal.coe_le_coe).2 h
  simp only [Fin.sum_univ_two, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_rpow,
    NNReal.coe_one, one_div] at hR
  rw [f0coe, f1coe, g0coe, g1coe] at hR
  simpa [mul_comm] using hR

lemma parameterBody_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ} (hq : 0 < q) {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (parameterBody q K L) := by
  let domain : Set (ℝ × (E × E)) := Set.Icc (0 : ℝ) 1 ×ˢ (K ×ˢ L)
  let F : ℝ × (E × E) → E := fun w ↦
    (1 - w.1) ^ (1 / q) • w.2.1 + w.1 ^ (1 / q) • w.2.2
  have hexp : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
  have hpow : Continuous (fun t : ℝ ↦ t ^ (1 / q)) := Real.continuous_rpow_const hexp
  have hF : Continuous F := by
    dsimp [F]
    exact ((hpow.comp (continuous_const.sub continuous_fst)).smul
      (continuous_fst.comp continuous_snd)).add
      ((hpow.comp continuous_fst).smul (continuous_snd.comp continuous_snd))
  have hdom : IsCompact domain := isCompact_Icc.prod (hK.prod hL)
  have himage : F '' domain = parameterBody q K L := by
    ext z
    simp only [domain, F, parameterBody, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨t, x, y⟩, ⟨ht, hx, hy⟩, rfl⟩
      exact ⟨t, ht, x, hx, y, hy, rfl⟩
    · rintro ⟨t, ht, x, hx, y, hy, rfl⟩
      exact ⟨(t, x, y), ⟨ht, hx, hy⟩, rfl⟩
  rw [← himage]
  exact hdom.image hF

lemma exists_scaled_combination_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : Convex ℝ K) (h0 : 0 ∈ K) {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R) (habR : a + b ≤ R) :
    ∃ z ∈ K, R • z = a • x + b • y := by
  by_cases hR0 : R = 0
  · have hab0 : a + b = 0 := le_antisymm (hR0 ▸ habR) (add_nonneg ha hb)
    have ha0 : a = 0 := (add_eq_zero_iff_of_nonneg ha hb).mp hab0 |>.1
    have hb0 : b = 0 := (add_eq_zero_iff_of_nonneg ha hb).mp hab0 |>.2
    exact ⟨0, h0, by simp [hR0, ha0, hb0]⟩
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    obtain ⟨w, hw, hweq⟩ := hK.exists_mem_add_smul_eq hx hy ha hb
    let c : ℝ := (a + b) / R
    have hc : c ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (add_nonneg ha hb) hRpos.le, (div_le_one hRpos).mpr habR⟩
    refine ⟨c • w, hK.smul_mem_of_zero_mem h0 hw hc, ?_⟩
    rw [smul_smul]
    have hRc : R * c = a + b := by
      dsimp [c]
      rw [mul_comm, div_mul_cancel₀ _ hR0]
    rw [hRc, hweq]

lemma parameterBody_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ} (hq : 1 ≤ q) {K L : Set E}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (h0K : 0 ∈ K) (h0L : 0 ∈ L) :
    Convex ℝ (parameterBody q K L) := by
  rintro z₁ ⟨t₁, ht₁, x₁, hx₁, y₁, hy₁, rfl⟩ z₂ ⟨t₂, ht₂, x₂, hx₂, y₂, hy₂, rfl⟩ a b ha hb hab
  let t : ℝ := a * t₁ + b * t₂
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg ha ht₁.1) (mul_nonneg hb ht₂.1)
    · calc
        t ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left ht₁.2 ha)
          (mul_le_mul_of_nonneg_left ht₂.2 hb)
        _ = 1 := by rw [mul_one, mul_one, hab]
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hr0 : 0 ≤ 1 / q := one_div_nonneg.mpr hqpos.le
  have hr1 : 1 / q ≤ 1 := (div_le_one hqpos).mpr hq
  have hconc := Real.concaveOn_rpow hr0 hr1
  have hleft :
      a * (1 - t₁) ^ (1 / q) + b * (1 - t₂) ^ (1 / q) ≤
        (1 - t) ^ (1 / q) := by
    have hc := hconc.2 (sub_nonneg.mpr ht₁.2) (sub_nonneg.mpr ht₂.2) ha hb hab
    have hbase : a * (1 - t₁) + b * (1 - t₂) = 1 - t := by
      dsimp [t]
      calc
        a * (1 - t₁) + b * (1 - t₂) = (a + b) - (a * t₁ + b * t₂) := by ring
        _ = 1 - (a * t₁ + b * t₂) := by rw [hab]
    simpa only [smul_eq_mul, hbase] using hc
  have hright : a * t₁ ^ (1 / q) + b * t₂ ^ (1 / q) ≤ t ^ (1 / q) := by
    exact hconc.2 ht₁.1 ht₂.1 ha hb hab
  obtain ⟨x, hx, hxeq⟩ := exists_scaled_combination_mem hK h0K hx₁ hx₂
    (mul_nonneg ha (Real.rpow_nonneg (sub_nonneg.mpr ht₁.2) _))
    (mul_nonneg hb (Real.rpow_nonneg (sub_nonneg.mpr ht₂.2) _))
    (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _) hleft
  obtain ⟨y, hy, hyeq⟩ := exists_scaled_combination_mem hL h0L hy₁ hy₂
    (mul_nonneg ha (Real.rpow_nonneg ht₁.1 _))
    (mul_nonneg hb (Real.rpow_nonneg ht₂.1 _))
    (Real.rpow_nonneg ht.1 _) hright
  refine ⟨t, ht, x, hx, y, hy, ?_⟩
  rw [hxeq, hyeq]
  module

lemma exists_slice_weights {q : ℝ} (hq : 0 < q) (a b : NNReal)
    (hab : a ^ q + b ^ q ≤ 1) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      (a : ℝ) ≤ (1 - t) ^ (1 / q) ∧ (b : ℝ) ≤ t ^ (1 / q) := by
  let t : ℝ := (b ^ q : NNReal)
  have habR : (a : ℝ) ^ q + (b : ℝ) ^ q ≤ 1 := by exact_mod_cast hab
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact le_trans (le_add_of_nonneg_left (Real.rpow_nonneg a.coe_nonneg _)) habR
  refine ⟨t, ⟨ht0, ht1⟩, ?_, ?_⟩
  · rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos a.coe_nonneg (sub_nonneg.mpr ht1) hq).2
    dsimp [t]
    linarith
  · have hb : ((b : ℝ) ^ q) ^ q⁻¹ = (b : ℝ) :=
      Real.rpow_rpow_inv b.coe_nonneg hq.ne'
    simpa [t, one_div, NNReal.coe_rpow] using hb.ge

/-- Every directional support value of the parameter body is attained by an actual slice point. -/
lemma parameterBody_has_support_point {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p q : ℝ} (hpq : p.HolderConjugate q) {K L : Set E}
    (hKc : IsCompact K) (hLc : IsCompact L) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (h0K : 0 ∈ K) (h0L : 0 ∈ L) (u : E) :
    ∃ z ∈ parameterBody q K L,
      inner ℝ z u =
        (supportFunctionE K u ^ p + supportFunctionE L u ^ p) ^ (1 / p) := by
  let A : NNReal := ⟨supportFunctionE K u, supportFunctionE_nonneg hKc h0K u⟩
  let B : NNReal := ⟨supportFunctionE L u, supportFunctionE_nonneg hLc h0L u⟩
  let f : Fin 2 → NNReal := ![A, B]
  have f0coe : (f 0 : ℝ) = supportFunctionE K u := rfl
  have f1coe : (f 1 : ℝ) = supportFunctionE L u := rfl
  obtain ⟨x, hx, hxA⟩ := exists_inner_eq_supportFunctionE hKc ⟨0, h0K⟩ u
  obtain ⟨y, hy, hyB⟩ := exists_inner_eq_supportFunctionE hLc ⟨0, h0L⟩ u
  obtain ⟨g, hg, hdot⟩ :=
    (NNReal.isGreatest_Lp (Finset.univ : Finset (Fin 2)) f hpq).1
  have hgq : g 0 ^ q + g 1 ^ q ≤ 1 := by simpa using hg
  obtain ⟨t, ht, hga, hgb⟩ := exists_slice_weights hpq.symm.pos (g 0) (g 1) hgq
  obtain ⟨x', hx', hxeq⟩ := exists_scaled_combination_mem hK h0K hx h0K
    (show 0 ≤ (g 0 : ℝ) from (g 0).coe_nonneg) (le_refl 0)
    (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _) (by simpa using hga)
  obtain ⟨y', hy', hyeq⟩ := exists_scaled_combination_mem hL h0L hy h0L
    (show 0 ≤ (g 1 : ℝ) from (g 1).coe_nonneg) (le_refl 0)
    (Real.rpow_nonneg ht.1 _) (by simpa using hgb)
  let z := (1 - t) ^ (1 / q) • x' + t ^ (1 / q) • y'
  refine ⟨z, ⟨t, ht, x', hx', y', hy', rfl⟩, ?_⟩
  have hdotR :
      (g 0 : ℝ) * supportFunctionE K u + (g 1 : ℝ) * supportFunctionE L u =
        (supportFunctionE K u ^ p + supportFunctionE L u ^ p) ^ (1 / p) := by
    have hdot' := congrArg ((↑) : NNReal → ℝ) hdot
    simp only [Fin.sum_univ_two, NNReal.coe_add, NNReal.coe_mul,
      NNReal.coe_rpow] at hdot'
    rw [f0coe, f1coe] at hdot'
    simpa [mul_comm] using hdot'
  have hxi :
      (1 - t) ^ (1 / q) * inner ℝ x' u = (g 0 : ℝ) * supportFunctionE K u := by
    have hh := congrArg (fun v : E ↦ inner ℝ v u) hxeq
    simpa [inner_add_left, inner_smul_left, hxA] using hh
  have hyi : t ^ (1 / q) * inner ℝ y' u = (g 1 : ℝ) * supportFunctionE L u := by
    have hh := congrArg (fun v : E ↦ inner ℝ v u) hyeq
    simpa [inner_add_left, inner_smul_left, hyB] using hh
  dsimp [z]
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  change (1 - t) ^ (1 / q) * inner ℝ x' u + t ^ (1 / q) * inner ℝ y' u = _
  rw [hxi, hyi]
  exact hdotR

lemma parameterBody_subset_lpSumE {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p q : ℝ} (hpq : p.HolderConjugate q) {K L : Set E}
    (hKc : IsCompact K) (hLc : IsCompact L) (h0K : 0 ∈ K) (h0L : 0 ∈ L) :
    parameterBody q K L ⊆ lpSumE p K L := by
  rintro z ⟨t, ht, x, hx, y, hy, rfl⟩ u
  have hsK := inner_le_supportFunctionE hKc hx u
  have hsL := inner_le_supportFunctionE hLc hy u
  have hA := supportFunctionE_nonneg hKc h0K u
  have hB := supportFunctionE_nonneg hLc h0L u
  calc
    inner ℝ ((1 - t) ^ (1 / q) • x + t ^ (1 / q) • y) u =
        (1 - t) ^ (1 / q) * inner ℝ x u + t ^ (1 / q) * inner ℝ y u := by
          simp [inner_add_left, inner_smul_left]
    _ ≤ (1 - t) ^ (1 / q) * supportFunctionE K u +
        t ^ (1 / q) * supportFunctionE L u := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hsK (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _))
            (mul_le_mul_of_nonneg_left hsL (Real.rpow_nonneg ht.1 _))
    _ ≤ _ := holder_slice_bound p q t _ _ hpq hA hB ht

/-- Equation (8) of arXiv:2607.20387, proved from the half-space definition used by Formal
Conjectures.  The reverse inclusion uses strong separation and an attained Hölder maximizer. -/
lemma lpSumE_eq_parameterBody {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {p q : ℝ} (hpq : p.HolderConjugate q) {K L : Set E}
    (hKc : IsCompact K) (hLc : IsCompact L) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (h0K : 0 ∈ K) (h0L : 0 ∈ L) :
    lpSumE p K L = parameterBody q K L := by
  apply Set.Subset.antisymm ?_ (parameterBody_subset_lpSumE hpq hKc hLc h0K h0L)
  intro x hx
  by_contra hxp
  have hq1 : 1 ≤ q := hpq.symm.lt.le
  obtain ⟨f, c, hfc, hcfx⟩ := geometric_hahn_banach_closed_point
    (parameterBody_convex hq1 hK hL h0K h0L)
    (parameterBody_isCompact hpq.symm.pos hKc hLc).isClosed hxp
  let u : E := (InnerProductSpace.toDual ℝ E).symm f
  obtain ⟨z, hz, hzu⟩ :=
    parameterBody_has_support_point hpq hKc hLc hK hL h0K h0L u
  have hfxu : f x = inner ℝ x u := by
    dsimp [u]
    rw [← InnerProductSpace.toDual_symm_apply]
    exact real_inner_comm _ _
  have hfzu : f z = inner ℝ z u := by
    dsimp [u]
    rw [← InnerProductSpace.toDual_symm_apply]
    exact real_inner_comm _ _
  have hzx : inner ℝ z u < inner ℝ x u := by
    rw [← hfzu, ← hfxu]
    exact (hfc z hz).trans hcfx
  have hxu := hx u
  rw [← hzu] at hxu
  exact (not_lt_of_ge hxu) hzx

lemma mem_translate {E : Type*} [AddCommGroup E] {c : E} {C : Set E} {z : E} :
    z ∈ translate c C ↔ z - c ∈ C := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hz
    exact ⟨z - c, hz, by abel⟩

lemma neg_translate {E : Type*} [AddCommGroup E] (c : E) (C : Set E) :
    -(translate c C) = translate (-c) (-C) := by
  ext z
  simp only [mem_neg, mem_translate]
  constructor <;> intro h
  · simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using h
  · simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using h

lemma translate_neg_cancel {E : Type*} [AddCommGroup E] (c : E) (K : Set E) :
    translate c (translate (-c) K) = K := by
  ext z
  simp only [mem_translate]
  constructor <;> intro h
  · simpa only [sub_neg_eq_add, sub_add_cancel] using h
  · simpa only [sub_neg_eq_add, sub_add_cancel] using h

lemma centered_neg_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {c : E} (hsym : ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K) :
    -(translate (-c) K) = translate (-c) K := by
  ext z
  simp only [mem_neg, mem_translate, sub_neg_eq_add]
  have h := hsym (z + c)
  constructor
  · intro hz
    apply h.mpr
    convert hz using 1 <;> module
  · intro hz
    have hz' := h.mp hz
    convert hz' using 1 <;> module

lemma convex_translate_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) (C : Set E) : Convex ℝ (translate c C) ↔ Convex ℝ C := by
  change Convex ℝ ((fun x : E ↦ x + c) '' C) ↔ Convex ℝ C
  rw [show (fun x : E ↦ x + c) = (fun x : E ↦ c + x) by
    funext x
    exact add_comm x c]
  exact convex_vadd (𝕜 := ℝ) (s := C) c

lemma volume_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] (c : E) (C : Set E) :
    volume (translate c C) = volume C := by
  have hset : translate c C = (fun z : E ↦ z + (-c)) ⁻¹' C := by
    ext z
    simp only [mem_translate, mem_preimage]
    constructor <;> intro h
    · simpa [sub_eq_add_neg] using h
    · simpa [sub_eq_add_neg] using h
  rw [hset, measure_preimage_add_right]

/-- For a centrally symmetric body `C`, every parameter slice is a translate of one homothet
of `C`.  This is the algebraic specialization behind Conjecture 4. -/
lemma slice_translate_of_neg_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q t : ℝ) (c : E) (C : Set E) (hC : -C = C)
    (hconv : Convex ℝ C) (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    slice q t (translate c C) =
      translate ((((1 - t) ^ (1 / q)) - t ^ (1 / q)) • c)
        ((((1 - t) ^ (1 / q)) + t ^ (1 / q)) • C) := by
  let a : ℝ := (1 - t) ^ (1 / q)
  let b : ℝ := t ^ (1 / q)
  have ha : 0 ≤ a := Real.rpow_nonneg (sub_nonneg.mpr ht.2) _
  have hb : 0 ≤ b := Real.rpow_nonneg ht.1 _
  have hab : 0 < a + b := by
    by_cases htz : t = 0
    · have hqi : q⁻¹ ≠ 0 := inv_ne_zero hq.ne'
      simp [a, b, htz, hqi]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htz)
      exact add_pos_of_nonneg_of_pos ha (Real.rpow_pos_of_pos htpos _)
  ext z
  constructor
  · rintro ⟨ax, hax, bz, hbz, rfl⟩
    rcases hax with ⟨kx, hkx, rfl⟩
    rcases hkx with ⟨x, hx, rfl⟩
    have hneg : -(translate c C) = translate (-c) C := by rw [neg_translate, hC]
    rw [hneg] at hbz
    rcases hbz with ⟨ky, hky, rfl⟩
    rcases hky with ⟨y, hy, rfl⟩
    rw [mem_translate]
    change a • (x + c) + b • (y + -c) - (a - b) • c ∈ (a + b) • C
    refine ⟨(a / (a + b)) • x + (b / (a + b)) • y, ?_, ?_⟩
    · exact hconv hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le) (by field_simp)
    · have hax : (a + b) * (a / (a + b)) = a := by field_simp
      have hby : (a + b) * (b / (a + b)) = b := by field_simp
      symm
      calc
        a • (x + c) + b • (y + -c) - (a - b) • c = a • x + b • y := by module
        _ = (a + b) • ((a / (a + b)) • x + (b / (a + b)) • y) := by
          rw [smul_add, smul_smul, smul_smul, hax, hby]
  · rw [mem_translate]
    rintro ⟨w, hw, hwz⟩
    change (a + b) • w = z - (a - b) • c at hwz
    have hneg : -(translate c C) = translate (-c) C := by rw [neg_translate, hC]
    refine ⟨a • (w + c), ?_, b • (w + -c), ?_, ?_⟩
    · exact ⟨w + c, ⟨w, hw, rfl⟩, rfl⟩
    · rw [hneg]
      exact ⟨w + -c, ⟨w, hw, rfl⟩, rfl⟩
    · change a • (w + c) + b • (w + -c) = z
      have hz : (a + b) • w + (a - b) • c = z := (eq_sub_iff_add_eq).mp hwz
      rw [← hz]
      module

lemma volume_slice_translate_of_neg_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    (q t : ℝ) (c : E) (C : Set E) (hC : -C = C)
    (hconv : Convex ℝ C) (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    volume (slice q t (translate c C)) =
      ENNReal.ofReal
        ((((1 - t) ^ (1 / q)) + t ^ (1 / q)) ^ Module.finrank ℝ E) * volume C := by
  rw [slice_translate_of_neg_eq q t c C hC hconv hq ht, volume_translate,
    MeasureTheory.Measure.addHaar_smul]
  have hs : 0 ≤ ((1 - t) ^ (1 / q)) + t ^ (1 / q) :=
    add_nonneg (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)
      (Real.rpow_nonneg ht.1 _)
  rw [abs_of_nonneg (pow_nonneg hs _)]

/-! ## Definitions matching the current planar Formal Conjectures file -/

noncomputable def supportFunction (K : Set (EuclideanSpace ℝ (Fin 2))) (u : (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  supportFunctionE K u

noncomputable def lpSum (p : ℝ) (K L : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  lpSumE p K L

def HasCentreOfSymmetry (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ c : (EuclideanSpace ℝ (Fin 2)), ∀ x, x ∈ K ↔ (2 • c - x) ∈ K

noncomputable def rsConstant (q : ℝ) : ℝ :=
  2 * Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q) + 2

def IsParallelogramAtOrigin (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ a b : (EuclideanSpace ℝ (Fin 2)), LinearIndependent ℝ ![a, b] ∧
    K = convexHull ℝ {0, a, b, a + b}

/-! ## A dimension-generic Formal Conjectures target for Conjecture 4 -/

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def supportFunctionN {n : ℕ} (K : Set (Ambient n)) (u : Ambient n) : ℝ :=
  supportFunctionE K u

noncomputable def lpSumN {n : ℕ} (p : ℝ) (K L : Set (Ambient n)) : Set (Ambient n) :=
  lpSumE p K L

def HasCentreOfSymmetryN {n : ℕ} (K : Set (Ambient n)) : Prop :=
  ∃ c : Ambient n, ∀ x, x ∈ K ↔ (2 • c - x) ∈ K

/-- The Gamma-function extension of `choose x y` used in the source paper. -/
noncomputable def generalizedBinomial (x y : ℝ) : ℝ :=
  Real.Gamma (x + 1) / (Real.Gamma (y + 1) * Real.Gamma (x - y + 1))

/-- The conjectured sharp symmetric-body coefficient in dimension `n`. -/
noncomputable def symmetricRSConstant (n : ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (Nat.choose n i : ℝ) / generalizedBinomial ((n : ℝ) / q) ((i : ℝ) / q)

/-- The unit cube `[0,1]^n`, transported to the Euclidean-space model used by the theorem. -/
noncomputable def unitCube (n : ℕ) : Set (Ambient n) :=
  WithLp.ofLp ⁻¹' Set.Icc (0 : Fin n → ℝ) 1

/--
The universal-inequality clause of Conjecture 4.

Keeping the proposition as a named definition makes the theorem statement reusable by both the
mathlib-only package and the Formal Conjectures bridge.  Its proof is `conjecture4_proved`;
the full paper statement is `Conjecture4FullTarget` below.
-/
def Conjecture4Target : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Set (Ambient n)),
    Convex ℝ K → IsCompact K → (interior K).Nonempty →
    HasCentreOfSymmetryN K → (0 : Ambient n) ∈ K →
    ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
      volume (lpSumN p K (-K)) ≤
        ENNReal.ofReal (symmetricRSConstant n q) * volume K

/-- The sharpness clause in Conjecture 4: the unit cube attains the bound. -/
def Conjecture4SharpnessTarget : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
    volume (lpSumN p (unitCube n) (-(unitCube n))) =
      ENNReal.ofReal (symmetricRSConstant n q) * volume (unitCube n)

/-- Conjecture 4 exactly as stated in the paper: the bound together with cube equality. -/
def Conjecture4FullTarget : Prop :=
  Conjecture4Target ∧ Conjecture4SharpnessTarget

/-! ## Conjecture 5 -/

def Conjecture5Target : Prop :=
  ∀ (K : Set (EuclideanSpace ℝ (Fin 2))), Convex ℝ K → IsCompact K → (interior K).Nonempty →
    HasCentreOfSymmetry K → (0 : (EuclideanSpace ℝ (Fin 2))) ∈ K →
    ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
      volume (lpSum p K (-K)) = ENNReal.ofReal (rsConstant q) * volume K →
        IsParallelogramAtOrigin K

/-- A definitional audit that the copied target has exactly the intended statement. -/
theorem conjecture5_target_unfolds :
    Conjecture5Target ↔
      ∀ (K : Set (EuclideanSpace ℝ (Fin 2))), Convex ℝ K → IsCompact K → (interior K).Nonempty →
        HasCentreOfSymmetry K → (0 : (EuclideanSpace ℝ (Fin 2))) ∈ K →
        ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
          volume (lpSum p K (-K)) = ENNReal.ofReal (rsConstant q) * volume K →
            IsParallelogramAtOrigin K := by
  rfl


noncomputable def parameterGraph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (K L : Set E) : Set (E × ℝ) :=
  {w | w.2 ∈ Set.Icc (0 : ℝ) 1 ∧ w.1 ∈ weightedSlice q w.2 K L}

noncomputable def parameterFiber {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (K L : Set E) (z : E) : Set ℝ :=
  (fun t ↦ (z, t)) ⁻¹' parameterGraph q K L

lemma parameterGraph_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ} (hq : 0 < q) {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (parameterGraph q K L) := by
  let domain : Set (ℝ × (E × E)) := Set.Icc (0 : ℝ) 1 ×ˢ (K ×ˢ L)
  let F : ℝ × (E × E) → E × ℝ := fun w ↦
    ((1 - w.1) ^ (1 / q) • w.2.1 + w.1 ^ (1 / q) • w.2.2, w.1)
  have hexp : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
  have hpow : Continuous (fun t : ℝ ↦ t ^ (1 / q)) := Real.continuous_rpow_const hexp
  have hfirst : Continuous (fun w : ℝ × (E × E) ↦
      (1 - w.1) ^ (1 / q) • w.2.1 + w.1 ^ (1 / q) • w.2.2) :=
    ((hpow.comp (continuous_const.sub continuous_fst)).smul
      (continuous_fst.comp continuous_snd)).add
      ((hpow.comp continuous_fst).smul (continuous_snd.comp continuous_snd))
  have hF : Continuous F := hfirst.prodMk continuous_fst
  have hdom : IsCompact domain := isCompact_Icc.prod (hK.prod hL)
  have himage : F '' domain = parameterGraph q K L := by
    ext w
    rcases w with ⟨z, t⟩
    change (z, t) ∈ F '' domain ↔
      t ∈ Set.Icc (0 : ℝ) 1 ∧ z ∈ weightedSlice q t K L
    constructor
    · rintro ⟨⟨s, ⟨x, y⟩⟩, ⟨hs, hx, hy⟩, heq⟩
      have hst : s = t := congrArg Prod.snd heq
      have hsz : (1 - s) ^ (1 / q) • x + s ^ (1 / q) • y = z := congrArg Prod.fst heq
      subst t
      refine ⟨hs, ?_⟩
      rw [← hsz]
      exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨ht, hz⟩
      rcases hz with ⟨ax, ⟨x, hx, rfl⟩, byv, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨⟨t, ⟨x, y⟩⟩, ⟨ht, hx, hy⟩, rfl⟩
  rw [← himage]
  exact hdom.image hF

lemma radial_interval_subset_fiber {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ} (hq : 0 < q) {K L : Set E}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (h0K : 0 ∈ K) (h0L : 0 ∈ L)
    {t₀ τ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    {x y : E} (hx : x ∈ K) (hy : y ∈ L) :
    Set.Icc (τ ^ q * t₀) (1 - τ ^ q * (1 - t₀)) ⊆
      parameterFiber q K L
        (τ • ((1 - t₀) ^ (1 / q) • x + t₀ ^ (1 / q) • y)) := by
  intro t ht
  change t ∈ Set.Icc (0 : ℝ) 1 ∧
    τ • ((1 - t₀) ^ (1 / q) • x + t₀ ^ (1 / q) • y) ∈ weightedSlice q t K L
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_trans (mul_nonneg (Real.rpow_nonneg hτ.1 _) ht₀.1) ht.1
    · exact ht.2.trans (sub_le_self _ (mul_nonneg (Real.rpow_nonneg hτ.1 _)
        (sub_nonneg.mpr ht₀.2)))
  have hr0 : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
  have hleftBase : τ ^ q * (1 - t₀) ≤ 1 - t := by linarith [ht.2]
  have hrightBase : τ ^ q * t₀ ≤ t := ht.1
  have hleftCoeff :
      τ * (1 - t₀) ^ (1 / q) ≤ (1 - t) ^ (1 / q) := by
    calc
      τ * (1 - t₀) ^ (1 / q) = (τ ^ q * (1 - t₀)) ^ (1 / q) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hτ.1 _) (sub_nonneg.mpr ht₀.2),
          one_div, Real.rpow_rpow_inv hτ.1 hq.ne']
      _ ≤ _ := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hτ.1 _)
        (sub_nonneg.mpr ht₀.2)) hleftBase hr0
  have hrightCoeff : τ * t₀ ^ (1 / q) ≤ t ^ (1 / q) := by
    calc
      τ * t₀ ^ (1 / q) = (τ ^ q * t₀) ^ (1 / q) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hτ.1 _) ht₀.1,
          one_div, Real.rpow_rpow_inv hτ.1 hq.ne']
      _ ≤ _ := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hτ.1 _) ht₀.1)
        hrightBase hr0
  obtain ⟨x', hx', hxeq⟩ := exists_scaled_combination_mem hK h0K hx h0K
    (mul_nonneg hτ.1 (Real.rpow_nonneg (sub_nonneg.mpr ht₀.2) _)) (le_refl 0)
    (Real.rpow_nonneg (sub_nonneg.mpr htI.2) _) (by simpa using hleftCoeff)
  obtain ⟨y', hy', hyeq⟩ := exists_scaled_combination_mem hL h0L hy h0L
    (mul_nonneg hτ.1 (Real.rpow_nonneg ht₀.1 _)) (le_refl 0)
    (Real.rpow_nonneg htI.1 _) (by simpa using hrightCoeff)
  refine ⟨htI, _, ⟨x', hx', rfl⟩, _, ⟨y', hy', rfl⟩, ?_⟩
  change (1 - t) ^ (1 / q) • x' + t ^ (1 / q) • y' =
    τ • ((1 - t₀) ^ (1 / q) • x + t₀ ^ (1 / q) • y)
  have hxeq' : (1 - t) ^ (1 / q) • x' =
      (τ * (1 - t₀) ^ (1 / q)) • x + 0 • 0 := by simpa [one_div] using hxeq
  have hyeq' : t ^ (1 / q) • y' =
      (τ * t₀ ^ (1 / q)) • y + 0 • 0 := by simpa [one_div] using hyeq
  rw [hxeq', hyeq']
  simp only [zero_smul, add_zero]
  module

lemma ofReal_one_sub_rpow_le_fiber_volume {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ} (hq : 0 < q) {K L : Set E}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (h0K : 0 ∈ K) (h0L : 0 ∈ L)
    {w : E} (hw : w ∈ parameterBody q K L) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (1 - τ ^ q) ≤ volume (parameterFiber q K L (τ • w)) := by
  rcases hw with ⟨t₀, ht₀, x, hx, y, hy, rfl⟩
  have hsub := radial_interval_subset_fiber hq hK hL h0K h0L ht₀ hτ hx hy
  calc
    ENNReal.ofReal (1 - τ ^ q) =
        volume (Set.Icc (τ ^ q * t₀) (1 - τ ^ q * (1 - t₀))) := by
          rw [Real.volume_Icc]
          congr 1
          ring
    _ ≤ _ := measure_mono hsub

noncomputable def fiberLength {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (K L : Set E) (z : E) : ℝ :=
  (volume (parameterFiber q K L z)).toReal

lemma parameterFiber_subset_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (K L : Set E) (z : E) :
    parameterFiber q K L z ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  exact ht.1

lemma parameterFiber_volume_lt_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (K L : Set E) (z : E) :
    volume (parameterFiber q K L z) < ∞ := by
  calc
    volume (parameterFiber q K L z) ≤ volume (Set.Icc (0 : ℝ) 1) :=
      measure_mono (parameterFiber_subset_Icc q K L z)
    _ < ∞ := by rw [Real.volume_Icc]; simp

lemma measurable_fiberLength {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {q : ℝ} (hq : 0 < q) {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    Measurable (fiberLength q K L) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_measure_prodMk_left (parameterGraph_isCompact hq hK hL).measurableSet)

lemma parameterGraph_volume_eq_lintegral_fibers {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    {q : ℝ} (hq : 0 < q) {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    (volume.prod volume) (parameterGraph q K L) =
      ∫⁻ z, volume (parameterFiber q K L z) ∂volume := by
  rw [Measure.prod_apply (parameterGraph_isCompact hq hK hL).measurableSet]
  rfl

lemma parameterGraph_volume_eq_lintegral_slices {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [SFinite (volume : Measure E)]
    {q : ℝ} (hq : 0 < q) {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    (volume.prod volume) (parameterGraph q K L) =
      ∫⁻ t in Set.Icc (0 : ℝ) 1, volume (weightedSlice q t K L) ∂volume := by
  rw [Measure.prod_apply_symm (parameterGraph_isCompact hq hK hL).measurableSet]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · have hsec : (fun x : E ↦ (x, t)) ⁻¹' parameterGraph q K L =
        weightedSlice q t K L := by
      ext z
      change (t ∈ Set.Icc (0 : ℝ) 1 ∧ z ∈ weightedSlice q t K L) ↔
        z ∈ weightedSlice q t K L
      exact and_iff_right ht
    rw [hsec, Set.indicator_of_mem ht]
  · have hsec : (fun x : E ↦ (x, t)) ⁻¹' parameterGraph q K L = ∅ := by
      ext z
      change (t ∈ Set.Icc (0 : ℝ) 1 ∧ z ∈ weightedSlice q t K L) ↔ False
      simp only [ht, false_and, iff_self]
    rw [hsec, measure_empty, Set.indicator_of_notMem ht]

lemma smul_parameterBody_subset_fiberLength_level {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ} (hq : 0 < q) {K L : Set E}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (h0K : 0 ∈ K) (h0L : 0 ∈ L)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - s) ^ (1 / q)) • parameterBody q K L ⊆
      {z | s ≤ fiberLength q K L z} := by
  rintro z ⟨w, hw, rfl⟩
  let τ : ℝ := (1 - s) ^ (1 / q)
  have hr0 : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨Real.rpow_nonneg (sub_nonneg.mpr hs.2) _,
      Real.rpow_le_one (sub_nonneg.mpr hs.2) (by linarith [hs.1]) hr0⟩
  have hτq : 1 - τ ^ q = s := by
    dsimp [τ]
    rw [one_div, Real.rpow_inv_rpow (sub_nonneg.mpr hs.2) hq.ne']
    ring
  have hvol := ofReal_one_sub_rpow_le_fiber_volume hq hK hL h0K h0L hw hτ
  rw [hτq] at hvol
  have hreal := (ENNReal.toReal_le_toReal (by simp)
    (parameterFiber_volume_lt_top q K L (τ • w)).ne).2 hvol
  change s ≤ fiberLength q K L (τ • w)
  simpa [fiberLength, ENNReal.toReal_ofReal hs.1] using hreal

lemma lintegral_Ioc_one_sub_rpow {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - s) ^ r) ∂volume =
      ENNReal.ofReal (1 / (r + 1)) := by
  let f : ℝ → ℝ := fun s ↦ (1 - s) ^ r
  have hfcont : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    exact (Real.continuous_rpow_const hr).comp (continuous_const.sub continuous_id)
  have hfint : IntervalIntegrable f volume (0 : ℝ) 1 := hfcont.intervalIntegrable
  have hfIoc : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hfint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Real.rpow_nonneg (by linarith [hs.2]) _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfIoc hnonneg]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ s in (0 : ℝ)..1, (1 - s) ^ r) = 1 / (r + 1)
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ r) 1]
  norm_num
  rw [integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  simp

lemma lintegral_volume_rpow_smul {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {q : ℝ} (hq : 0 < q) {D : Set E} (hD : IsCompact D) :
    ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        volume (((1 - s) ^ (1 / q)) • D) ∂volume =
      ENNReal.ofReal (q / ((Module.finrank ℝ E : ℝ) + q)) * volume D := by
  have hDtop : volume D ≠ ∞ := hD.measure_lt_top.ne
  calc
    (∫⁻ s in Set.Ioc (0 : ℝ) 1,
        volume (((1 - s) ^ (1 / q)) • D) ∂volume) =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((1 - s) ^ ((Module.finrank ℝ E : ℝ) / q)) * volume D ∂volume := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
            rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume
              (Real.rpow_nonneg (by linarith [hs.2]) _)]
            congr 2
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [hs.2] : 0 ≤ 1 - s)]
            congr 1
            ring
    _ = (∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((1 - s) ^ ((Module.finrank ℝ E : ℝ) / q)) ∂volume) * volume D := by
            exact lintegral_mul_const' (volume D) _ hDtop
    _ = ENNReal.ofReal (1 / ((Module.finrank ℝ E : ℝ) / q + 1)) * volume D := by
          rw [lintegral_Ioc_one_sub_rpow (div_nonneg (Nat.cast_nonneg _) hq.le)]
    _ = ENNReal.ofReal (q / ((Module.finrank ℝ E : ℝ) + q)) * volume D := by
          rw [show 1 / ((Module.finrank ℝ E : ℝ) / q + 1) =
              q / ((Module.finrank ℝ E : ℝ) + q) by
            field_simp [hq.ne']]

lemma ofReal_fiberLength {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (K L : Set E) (z : E) :
    ENNReal.ofReal (fiberLength q K L z) = volume (parameterFiber q K L z) := by
  exact ENNReal.ofReal_toReal (parameterFiber_volume_lt_top q K L z).ne

lemma lintegral_fiber_volume_eq_lintegral_levels {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    {q : ℝ} (hq : 0 < q) {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    (∫⁻ z, volume (parameterFiber q K L z) ∂volume) =
      ∫⁻ s in Set.Ioi (0 : ℝ), volume {z | s ≤ fiberLength q K L z} ∂volume := by
  calc
    (∫⁻ z, volume (parameterFiber q K L z) ∂volume) =
        ∫⁻ z, ENNReal.ofReal (fiberLength q K L z) ∂volume := by
          apply lintegral_congr
          intro z
          exact (ofReal_fiberLength q K L z).symm
    _ = _ := MeasureTheory.lintegral_eq_lintegral_meas_le volume
      (Filter.Eventually.of_forall fun z ↦ ENNReal.toReal_nonneg)
      (measurable_fiberLength hq hK hL).aemeasurable

lemma lintegral_scaled_parameterBody_le_fibers {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    {q : ℝ} (hq : 0 < q) {K L : Set E}
    (hKc : IsCompact K) (hLc : IsCompact L)
    (hK : Convex ℝ K) (hL : Convex ℝ L) (h0K : 0 ∈ K) (h0L : 0 ∈ L) :
    (∫⁻ s in Set.Ioc (0 : ℝ) 1,
        volume (((1 - s) ^ (1 / q)) • parameterBody q K L) ∂volume) ≤
      ∫⁻ z, volume (parameterFiber q K L z) ∂volume := by
  rw [lintegral_fiber_volume_eq_lintegral_levels hq hKc hLc]
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_mono
  intro s
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1
  · have hsIoi : s ∈ Set.Ioi (0 : ℝ) := hs.1
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem hsIoi]
    exact measure_mono (smul_parameterBody_subset_fiberLength_level hq hK hL h0K h0L
      ⟨hs.1.le, hs.2⟩)
  · rw [Set.indicator_of_notMem hs]
    exact bot_le

/-- Lemma 5.3 in the multiplicative form best suited to the layer-cake proof. -/
theorem lemma53_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {q : ℝ} (hq : 0 < q) {K L : Set E}
    (hKc : IsCompact K) (hLc : IsCompact L)
    (hK : Convex ℝ K) (hL : Convex ℝ L) (h0K : 0 ∈ K) (h0L : 0 ∈ L) :
    ENNReal.ofReal (q / ((Module.finrank ℝ E : ℝ) + q)) *
        volume (parameterBody q K L) ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1, volume (weightedSlice q t K L) ∂volume := by
  calc
    ENNReal.ofReal (q / ((Module.finrank ℝ E : ℝ) + q)) *
        volume (parameterBody q K L) =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          volume (((1 - s) ^ (1 / q)) • parameterBody q K L) ∂volume := by
            symm
            exact lintegral_volume_rpow_smul hq (parameterBody_isCompact hq hKc hLc)
    _ ≤ ∫⁻ z, volume (parameterFiber q K L z) ∂volume :=
      lintegral_scaled_parameterBody_le_fibers hq hKc hLc hK hL h0K h0L
    _ = (volume.prod volume) (parameterGraph q K L) :=
      (parameterGraph_volume_eq_lintegral_fibers hq hKc hLc).symm
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, volume (weightedSlice q t K L) ∂volume :=
      parameterGraph_volume_eq_lintegral_slices hq hKc hLc

lemma lintegral_Ioo_beta_rpow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫⁻ x in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume) =
      ENNReal.ofReal (ProbabilityTheory.beta α β) := by
  have hbeta : 0 < ProbabilityTheory.beta α β := ProbabilityTheory.beta_pos hα hβ
  have hnorm :
      (∫⁻ x in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((1 / ProbabilityTheory.beta α β) *
          x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume) = 1 := by
    rw [← ProbabilityTheory.lintegral_betaPDF]
    exact ProbabilityTheory.lintegral_betaPDF_eq_one hα hβ
  have hfactor :
      (∫⁻ x in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((1 / ProbabilityTheory.beta α β) *
          x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume) =
      ENNReal.ofReal (1 / ProbabilityTheory.beta α β) *
        ∫⁻ x in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (1 / ProbabilityTheory.beta α β)) _
      ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hbeta.le)]
    congr 1
    ring
  rw [hfactor, one_div, ENNReal.ofReal_inv_of_pos hbeta] at hnorm
  let B : ℝ≥0∞ := ENNReal.ofReal (ProbabilityTheory.beta α β)
  have hB0 : B ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hbeta
  have hBtop : B ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (∫⁻ x in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume) =
        1 * (∫⁻ x in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume) := by simp
    _ = (B * B⁻¹) * (∫⁻ x in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume) := by
          rw [ENNReal.mul_inv_cancel hB0 hBtop]
    _ = B * (B⁻¹ * (∫⁻ x in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (x ^ (α - 1) * (1 - x) ^ (β - 1)) ∂volume)) := by
          rw [mul_assoc]
    _ = B * 1 := by rw [hnorm]
    _ = ENNReal.ofReal (ProbabilityTheory.beta α β) := by simp [B]

lemma lintegral_Ioo_slice_monomial (n i : ℕ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal
          ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i))) ∂volume) =
      ENNReal.ofReal
        (ProbabilityTheory.beta (((n - i : ℕ) : ℝ) / q + 1) ((i : ℝ) / q + 1)) := by
  have hα : 0 < ((n - i : ℕ) : ℝ) / q + 1 := by positivity
  have hβ : 0 < (i : ℝ) / q + 1 := by positivity
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal
          ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i))) ∂volume) =
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal
            (t ^ ((((n - i : ℕ) : ℝ) / q + 1) - 1) *
              (1 - t) ^ (((i : ℝ) / q + 1) - 1)) ∂volume := by
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro t ht
            change ENNReal.ofReal
                ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i))) =
              ENNReal.ofReal
                (t ^ ((((n - i : ℕ) : ℝ) / q + 1) - 1) *
                  (1 - t) ^ (((i : ℝ) / q + 1) - 1))
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [ht.2] : 0 ≤ 1 - t),
              ← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
            ring_nf
    _ = _ := lintegral_Ioo_beta_rpow hα hβ

lemma lintegral_Icc_slice_power_eq_sum_beta (n : ℕ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (((1 - t) ^ (1 / q) + t ^ (1 / q)) ^ n) ∂volume) =
      ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ≥0∞) *
        ENNReal.ofReal
          (ProbabilityTheory.beta (((n - i : ℕ) : ℝ) / q + 1) ((i : ℝ) / q + 1)) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (((1 - t) ^ (1 / q) + t ^ (1 / q)) ^ n) ∂volume) =
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          ∑ i ∈ Finset.range (n + 1),
            ENNReal.ofReal
              ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i)) *
                (Nat.choose n i : ℝ)) ∂volume := by
          apply setLIntegral_congr_fun measurableSet_Ioo
          intro t ht
          change ENNReal.ofReal (((1 - t) ^ (1 / q) + t ^ (1 / q)) ^ n) =
            ∑ i ∈ Finset.range (n + 1),
              ENNReal.ofReal
                ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i)) *
                  (Nat.choose n i : ℝ))
          rw [add_pow, ENNReal.ofReal_sum_of_nonneg]
          intro i hi
          exact mul_nonneg
            (mul_nonneg (pow_nonneg (Real.rpow_nonneg (by linarith [ht.2]) _) _)
              (pow_nonneg (Real.rpow_nonneg ht.1.le _) _))
            (Nat.cast_nonneg _)
    _ = ∑ i ∈ Finset.range (n + 1),
          ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            ENNReal.ofReal
              ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i)) *
                (Nat.choose n i : ℝ)) ∂volume := by
          rw [MeasureTheory.lintegral_finset_sum]
          intro i hi
          fun_prop
    _ = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ≥0∞) *
          ENNReal.ofReal
            (ProbabilityTheory.beta (((n - i : ℕ) : ℝ) / q + 1) ((i : ℝ) / q + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∫⁻ t in Set.Ioo (0 : ℝ) 1,
                ENNReal.ofReal
                  ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i)) *
                    (Nat.choose n i : ℝ)) ∂volume) =
                ∫⁻ t in Set.Ioo (0 : ℝ) 1,
                  ENNReal.ofReal
                    ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i))) *
                    (Nat.choose n i : ℝ≥0∞) ∂volume := by
                      apply lintegral_congr_ae
                      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
                      rw [← ENNReal.ofReal_natCast]
                      exact ENNReal.ofReal_mul
                        (mul_nonneg
                          (pow_nonneg (Real.rpow_nonneg (by linarith [ht.2]) _) _)
                          (pow_nonneg (Real.rpow_nonneg ht.1.le _) _))
            _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1,
                  ENNReal.ofReal
                    ((((1 - t) ^ (1 / q)) ^ i) * ((t ^ (1 / q)) ^ (n - i))) ∂volume) *
                  (Nat.choose n i : ℝ≥0∞) := by
                    exact lintegral_mul_const' _ _ (by simp)
            _ = (Nat.choose n i : ℝ≥0∞) *
                ENNReal.ofReal
                  (ProbabilityTheory.beta (((n - i : ℕ) : ℝ) / q + 1)
                    ((i : ℝ) / q + 1)) := by
                    rw [lintegral_Ioo_slice_monomial n i hq]
                    exact mul_comm _ _

lemma beta_slice_eq_div_generalizedBinomial (n i : ℕ) {q : ℝ} (hq : 0 < q)
    (hi : i ∈ Finset.range (n + 1)) :
    ProbabilityTheory.beta (((n - i : ℕ) : ℝ) / q + 1) ((i : ℝ) / q + 1) =
      (q / ((n : ℝ) + q)) /
        generalizedBinomial ((n : ℝ) / q) ((i : ℝ) / q) := by
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hsub : (((n - i : ℕ) : ℝ)) = (n : ℝ) - (i : ℝ) := by
    exact Nat.cast_sub hin
  have hApos : 0 < ((n : ℝ) / q - (i : ℝ) / q + 1) := by
    rw [← sub_div, ← hsub]
    positivity
  have hBpos : 0 < (i : ℝ) / q + 1 := by positivity
  have hNpos : 0 < (n : ℝ) / q + 1 := by positivity
  have hsum :
      ((n - i : ℕ) : ℝ) / q + 1 + ((i : ℝ) / q + 1) =
        ((n : ℝ) / q + 1) + 1 := by
    rw [hsub]
    field_simp [hq.ne']
    ring
  rw [ProbabilityTheory.beta, generalizedBinomial, hsum,
    Real.Gamma_add_one hNpos.ne']
  rw [hsub]
  have hAeq : ((n : ℝ) - (i : ℝ)) / q + 1 =
      (n : ℝ) / q - (i : ℝ) / q + 1 := by ring
  rw [hAeq]
  field_simp [hq.ne', (Real.Gamma_pos_of_pos hApos).ne',
    (Real.Gamma_pos_of_pos hBpos).ne', (Real.Gamma_pos_of_pos hNpos).ne']

lemma generalizedBinomial_slice_pos (n i : ℕ) {q : ℝ} (hq : 0 < q)
    (hi : i ∈ Finset.range (n + 1)) :
    0 < generalizedBinomial ((n : ℝ) / q) ((i : ℝ) / q) := by
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hcastle : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin
  have hsub : (0 : ℝ) ≤ (n : ℝ) - (i : ℝ) := sub_nonneg.mpr hcastle
  rw [generalizedBinomial]
  exact div_pos (Real.Gamma_pos_of_pos (by positivity))
    (mul_pos (Real.Gamma_pos_of_pos (by positivity))
      (Real.Gamma_pos_of_pos (by
        have : 0 ≤ (n : ℝ) / q - (i : ℝ) / q := by
          rw [← sub_div]
          exact div_nonneg hsub hq.le
        linarith)))

lemma lintegral_Icc_slice_power_eq_constant (n : ℕ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (((1 - t) ^ (1 / q) + t ^ (1 / q)) ^ n) ∂volume) =
      ENNReal.ofReal (q / ((n : ℝ) + q)) *
        ENNReal.ofReal (symmetricRSConstant n q) := by
  rw [lintegral_Icc_slice_power_eq_sum_beta n hq, symmetricRSConstant,
    ENNReal.ofReal_sum_of_nonneg]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [beta_slice_eq_div_generalizedBinomial n i hq hi]
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg (Nat.choose n i)),
      ← ENNReal.ofReal_mul (div_nonneg hq.le (add_nonneg (Nat.cast_nonneg n) hq.le))]
    congr 1
    ring
  · intro i hi
    exact div_nonneg (Nat.cast_nonneg _) (generalizedBinomial_slice_pos n i hq hi).le

lemma volume_weightedSlice_neg_of_central_symmetry {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {q t : ℝ} (hq : 0 < q) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {K : Set E} (hK : Convex ℝ K) {c : E}
    (hsym : ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K) :
    volume (weightedSlice q t K (-K)) =
      ENNReal.ofReal
        ((((1 - t) ^ (1 / q)) + t ^ (1 / q)) ^ Module.finrank ℝ E) * volume K := by
  let C : Set E := translate (-c) K
  have hCneg : -C = C := centered_neg_eq hsym
  have hCconv : Convex ℝ C := (convex_translate_iff (-c) K).2 hK
  have hKrepr : translate c C = K := by
    dsimp [C]
    exact translate_neg_cancel c K
  have hCvol : volume C = volume K := by
    dsimp [C]
    exact volume_translate (-c) K
  change volume (slice q t K) = _
  have hvol := volume_slice_translate_of_neg_eq q t c C hCneg hCconv hq ht
  rw [hKrepr, hCvol] at hvol
  exact hvol

lemma lintegral_weightedSlice_neg_of_central_symmetry {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {q : ℝ} (hq : 0 < q) {K : Set E} (hKc : IsCompact K) (hK : Convex ℝ K)
    {c : E} (hsym : ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1, volume (weightedSlice q t K (-K)) ∂volume) =
      (ENNReal.ofReal (q / ((Module.finrank ℝ E : ℝ) + q)) *
        ENNReal.ofReal (symmetricRSConstant (Module.finrank ℝ E) q)) * volume K := by
  calc
    (∫⁻ t in Set.Icc (0 : ℝ) 1, volume (weightedSlice q t K (-K)) ∂volume) =
        ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal
            ((((1 - t) ^ (1 / q)) + t ^ (1 / q)) ^ Module.finrank ℝ E) *
            volume K ∂volume := by
              apply setLIntegral_congr_fun measurableSet_Icc
              intro t ht
              exact volume_weightedSlice_neg_of_central_symmetry hq ht hK hsym
    _ = (∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal
            ((((1 - t) ^ (1 / q)) + t ^ (1 / q)) ^ Module.finrank ℝ E) ∂volume) *
          volume K := by
            exact lintegral_mul_const' _ _ hKc.measure_lt_top.ne
    _ = _ := by rw [lintegral_Icc_slice_power_eq_constant (Module.finrank ℝ E) hq]

theorem central_symmetric_lpSum_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {p q : ℝ} (hpq : p.HolderConjugate q) {K : Set E}
    (hKc : IsCompact K) (hK : Convex ℝ K) (h0K : 0 ∈ K)
    {c : E} (hsym : ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K) :
    volume (lpSumE p K (-K)) ≤
      ENNReal.ofReal (symmetricRSConstant (Module.finrank ℝ E) q) * volume K := by
  have h0neg : (0 : E) ∈ -K := by simpa using h0K
  have hq : 0 < q := hpq.symm.pos
  let a : ℝ := q / ((Module.finrank ℝ E : ℝ) + q)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hq (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hq)
  have hlower := lemma53_lower hq hKc hKc.neg hK hK.neg h0K h0neg
  rw [lintegral_weightedSlice_neg_of_central_symmetry hq hKc hK hsym] at hlower
  change ENNReal.ofReal a * volume (parameterBody q K (-K)) ≤
    (ENNReal.ofReal a *
      ENNReal.ofReal (symmetricRSConstant (Module.finrank ℝ E) q)) * volume K at hlower
  rw [mul_assoc] at hlower
  have hbody : volume (parameterBody q K (-K)) ≤
      ENNReal.ofReal (symmetricRSConstant (Module.finrank ℝ E) q) * volume K :=
    (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr ha)
      ENNReal.ofReal_ne_top).mp hlower
  rw [lpSumE_eq_parameterBody hpq hKc hKc.neg hK hK.neg h0K h0neg]
  exact hbody

theorem conjecture4_proved : Conjecture4Target := by
  intro n hn K hK hKc hinter hsym h0K p q hp hrecip
  obtain ⟨c, hcenter⟩ := hsym
  have hpq : p.HolderConjugate q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa [one_div] using hrecip⟩
  have hcenterR : ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K := by
    intro x
    simpa [two_smul ℝ, two_nsmul] using hcenter x
  have hbound := central_symmetric_lpSum_bound hpq hKc hK h0K hcenterR
  simpa [lpSumN] using hbound

lemma symmetricRSConstant_two_eq_rsConstant {q : ℝ} (hq : 0 < q) :
    symmetricRSConstant 2 q = rsConstant q := by
  norm_num [symmetricRSConstant, rsConstant, generalizedBinomial, Finset.sum_range_succ]
  have h1 : Real.Gamma (1 / q + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h2 : Real.Gamma (2 / q + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp [hq.ne', h1, h2]
  ring

end
end LpRogersShephardLean4Web


theorem OMA.solution : type_of% @Arxiv.«2607.03582».volume_lpSum_le := by
  intro K hK hKc hKi hsym h0 p q hp hq
  have h := LpRogersShephardLean4Web.conjecture4_proved 2 (by norm_num) K hK hKc hKi hsym h0 p q hp hq
  have hq0 : 0 < q := by
    have : 0 < 1 / q := by
      have : 1 / q = 1 - 1 / p := by linarith
      rw [this]; have : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
      linarith
    exact one_div_pos.mp this
  rw [LpRogersShephardLean4Web.symmetricRSConstant_two_eq_rsConstant hq0] at h
  exact h
