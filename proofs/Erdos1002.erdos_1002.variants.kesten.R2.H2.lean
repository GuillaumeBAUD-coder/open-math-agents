import OMAReductions.R_Erdos1002_erdos_1002_variants_kesten_R2

/-!
Discretization estimate for Erdős Problem 1002 (Kesten variant, reduction R2, hypothesis H2):
shows that the continuous 2D Lebesgue distribution `source n c` and its `n^3 × n^3` modular grid
discretization `grid n c` satisfy `source n c - grid n c → 0` as `n → ∞`.
-/

namespace Erdos1002KestenR2H2

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Classical

private noncomputable def F (n : ℕ) (α β : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) n, (1 / 2 - Int.fract (β + α * (k : ℝ)))

private noncomputable def G (n a b : ℕ) : ℝ :=
  (n : ℝ) / 2 -
    (∑ k ∈ Finset.Icc 1 n, (((b + k * a) % (n ^ 3) : ℕ) : ℝ)) / ((n ^ 3 : ℕ) : ℝ)

private def cell (q a b : ℕ) : Set (ℝ × ℝ) :=
  Ico ((a : ℝ) / (q : ℝ)) (((a : ℝ) + 1) / (q : ℝ)) ×ˢ
    Ico ((b : ℝ) / (q : ℝ)) (((b : ℝ) + 1) / (q : ℝ))

private def badPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n ^ 3)).product (Finset.range (n ^ 3))).filter fun ab =>
    ∃ k ∈ Finset.Icc 1 n, n ^ 3 - (n + 1) ≤ (ab.2 + k * ab.1) % (n ^ 3)

private noncomputable def C_fn (n : ℕ) (α : ℝ) : ℝ :=
  (n : ℝ) / 2 - ∑ k ∈ Finset.Icc (1 : ℕ) n, Int.fract (α * (k : ℝ))

private def strip (n : ℕ) (T B : ℝ) (m : ℕ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ico (0 : ℝ) 1 ∧
    (C_fn n p.1 + (m : ℝ) - T) / (n : ℝ) ≤ p.2 ∧
    p.2 < (C_fn n p.1 + (m : ℝ) - T + B) / (n : ℝ)}

private def band (n : ℕ) (T B : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ico (0 : ℝ) 1 ∧ p.2 ∈ Ico (0 : ℝ) 1 ∧
    T - B < F n p.1 p.2 ∧ F n p.1 p.2 ≤ T}

private lemma measurableSet_cell (q a b : ℕ) : MeasurableSet (cell q a b) :=
  measurableSet_Ico.prod measurableSet_Ico

private lemma volume_cell {q : ℕ} (hq : 0 < q) (a b : ℕ) :
    volume (cell q a b) = ENNReal.ofReal (1 / (q : ℝ) ^ 2) := by
  have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  rw [cell, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  have hsub (x : ℕ) : ((x : ℝ) + 1) / (q : ℝ) - (x : ℝ) / (q : ℝ) = 1 / (q : ℝ) := by
    field_simp
    ring
  rw [hsub a, hsub b, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private lemma pairwiseDisjoint_cell {q : ℕ} (hq : 0 < q) :
    Set.PairwiseDisjoint
      (↑((Finset.range q).product (Finset.range q)) : Set (ℕ × ℕ))
      (fun ab => cell q ab.1 ab.2) := by
  have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  intro ab₁ _ ab₂ _ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro ⟨α, β⟩ h1 h2
  simp only [cell, mem_prod, mem_Ico] at h1 h2
  have hcoord : ab₁.1 ≠ ab₂.1 ∨ ab₁.2 ≠ ab₂.2 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext h.1 h.2)
  have hcontra {x y : ℕ} {t : ℝ} (hxy : x ≠ y)
      (hx1 : (x : ℝ) / q ≤ t) (hx2 : t < ((x : ℝ) + 1) / q)
      (hy1 : (y : ℝ) / q ≤ t) (hy2 : t < ((y : ℝ) + 1) / q) : False := by
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hle : (x : ℝ) + 1 ≤ (y : ℝ) := by exact_mod_cast hlt
      have : ((x : ℝ) + 1) / q ≤ (y : ℝ) / q := div_le_div_of_nonneg_right hle hq'.le
      linarith
    · have hle : (y : ℝ) + 1 ≤ (x : ℝ) := by exact_mod_cast hgt
      have : ((y : ℝ) + 1) / q ≤ (x : ℝ) / q := div_le_div_of_nonneg_right hle hq'.le
      linarith
  rcases hcoord with h1ne | h2ne
  · exact hcontra h1ne h1.1.1 h1.1.2 h2.1.1 h2.1.2
  · exact hcontra h2ne h1.2.1 h1.2.2 h2.2.1 h2.2.2

private lemma volume_biUnion_cell {q : ℕ} (hq : 0 < q) (A : Finset (ℕ × ℕ))
    (hA : A ⊆ (Finset.range q).product (Finset.range q)) :
    volume (⋃ ab ∈ A, cell q ab.1 ab.2) = ENNReal.ofReal ((A.card : ℝ) / (q : ℝ) ^ 2) := by
  have hdisj : Set.PairwiseDisjoint (↑A : Set (ℕ × ℕ)) (fun ab => cell q ab.1 ab.2) :=
    (pairwiseDisjoint_cell hq).subset (by exact_mod_cast hA)
  rw [measure_biUnion_finset hdisj (fun ab _ => measurableSet_cell q ab.1 ab.2)]
  simp_rw [volume_cell hq]
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

private lemma mem_cell_of_mem_Ico {q : ℕ} (hq : 0 < q) {α β : ℝ}
    (hα : α ∈ Ico (0 : ℝ) 1) (hβ : β ∈ Ico (0 : ℝ) 1) :
    ∃ ab ∈ (Finset.range q).product (Finset.range q), (α, β) ∈ cell q ab.1 ab.2 := by
  have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  let a := ⌊(q : ℝ) * α⌋₊
  let b := ⌊(q : ℝ) * β⌋₊
  have ha_lt : a < q := by
    refine (Nat.floor_lt (mul_nonneg hq'.le hα.1)).mpr ?_
    calc (q : ℝ) * α < (q : ℝ) * 1 := mul_lt_mul_of_pos_left hα.2 hq'
      _ = (q : ℝ) := mul_one _
  have hb_lt : b < q := by
    refine (Nat.floor_lt (mul_nonneg hq'.le hβ.1)).mpr ?_
    calc (q : ℝ) * β < (q : ℝ) * 1 := mul_lt_mul_of_pos_left hβ.2 hq'
      _ = (q : ℝ) := mul_one _
  refine ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha_lt, Finset.mem_range.mpr hb_lt⟩, ?_⟩
  simp only [cell, mem_prod, mem_Ico]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [div_le_iff₀ hq', mul_comm]
    exact Nat.floor_le (mul_nonneg hq'.le hα.1)
  · rw [lt_div_iff₀ hq', mul_comm]
    exact Nat.lt_floor_add_one _
  · rw [div_le_iff₀ hq', mul_comm]
    exact Nat.floor_le (mul_nonneg hq'.le hβ.1)
  · rw [lt_div_iff₀ hq', mul_comm]
    exact Nat.lt_floor_add_one _

private lemma volume_Icc_prod_diff_Ico_prod :
    volume ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)) = 0 := by
  have hsub :
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) ⊆
      ({(1 : ℝ)} ×ˢ Icc (0 : ℝ) 1) ∪ (Icc (0 : ℝ) 1 ×ˢ {(1 : ℝ)}) := by
    rintro ⟨α, β⟩ ⟨⟨⟨hα0, hα1⟩, ⟨hβ0, hβ1⟩⟩, hnot⟩
    by_cases hα : α < 1
    · right
      refine ⟨⟨hα0, hα1⟩, ?_⟩
      simp only [mem_singleton_iff]
      by_contra hβne
      exact hnot ⟨⟨hα0, hα⟩, ⟨hβ0, lt_of_le_of_ne hβ1 hβne⟩⟩
    · left
      exact ⟨by simp only [mem_singleton_iff]; linarith, ⟨hβ0, hβ1⟩⟩
  have h1 : volume ({(1 : ℝ)} ×ˢ Icc (0 : ℝ) 1) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have h2 : volume (Icc (0 : ℝ) 1 ×ˢ {(1 : ℝ)}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  exact measure_mono_null hsub (measure_union_null h1 h2)

private lemma volume_Icc_eq_volume_Ico (P : ℝ × ℝ → Prop) :
    volume {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ P p} =
      volume {p : ℝ × ℝ | p.1 ∈ Ico (0 : ℝ) 1 ∧ p.2 ∈ Ico (0 : ℝ) 1 ∧ P p} := by
  apply le_antisymm
  · have hsub :
        {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ P p} ⊆
        {p : ℝ × ℝ | p.1 ∈ Ico (0 : ℝ) 1 ∧ p.2 ∈ Ico (0 : ℝ) 1 ∧ P p} ∪
          ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)) := by
      rintro ⟨α, β⟩ ⟨hα, hβ, hP⟩
      by_cases h : α ∈ Ico (0 : ℝ) 1 ∧ β ∈ Ico (0 : ℝ) 1
      · exact Or.inl ⟨h.1, h.2, hP⟩
      · exact Or.inr ⟨⟨hα, hβ⟩, fun h' => h h'⟩
    calc volume {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ P p}
        ≤ volume ({p : ℝ × ℝ | p.1 ∈ Ico (0 : ℝ) 1 ∧ p.2 ∈ Ico (0 : ℝ) 1 ∧ P p} ∪
            ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))) :=
          measure_mono hsub
      _ ≤ volume {p : ℝ × ℝ | p.1 ∈ Ico (0 : ℝ) 1 ∧ p.2 ∈ Ico (0 : ℝ) 1 ∧ P p} +
            volume ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)) :=
          measure_union_le _ _
      _ = volume {p : ℝ × ℝ | p.1 ∈ Ico (0 : ℝ) 1 ∧ p.2 ∈ Ico (0 : ℝ) 1 ∧ P p} := by
          rw [volume_Icc_prod_diff_Ico_prod, add_zero]
  · exact measure_mono (fun p ⟨h1, h2, hP⟩ => ⟨Ico_subset_Icc_self h1, Ico_subset_Icc_self h2, hP⟩)

private lemma F_bounds_on_good_cell {n a b : ℕ} (hn : 2 ≤ n)
    (hab : (a, b) ∈ (Finset.range (n ^ 3)).product (Finset.range (n ^ 3)))
    (hnotbad : (a, b) ∉ badPairs n)
    {α β : ℝ} (hcell : (α, β) ∈ cell (n ^ 3) a b) :
    G n a b - ((n : ℝ) + 1) / (n : ℝ) ^ 2 ≤ F n α β ∧ F n α β ≤ G n a b := by
  set q := n ^ 3 with hq_def
  have hq_pos : 0 < q := by positivity
  have hq_rpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
  have hn_rpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hq_cast : (q : ℝ) = (n : ℝ) ^ 3 := by simp [hq_def]
  simp only [cell, mem_prod, mem_Ico] at hcell
  let u := (q : ℝ) * α - (a : ℝ)
  let v := (q : ℝ) * β - (b : ℝ)
  have hu0 : 0 ≤ u := by
    have : (a : ℝ) ≤ (q : ℝ) * α := by
      rw [mul_comm]; exact (div_le_iff₀ hq_rpos).mp hcell.1.1
    linarith
  have hu1 : u < 1 := by
    have : (q : ℝ) * α < (a : ℝ) + 1 := by
      rw [mul_comm]; exact (lt_div_iff₀ hq_rpos).mp hcell.1.2
    linarith
  have hv0 : 0 ≤ v := by
    have : (b : ℝ) ≤ (q : ℝ) * β := by
      rw [mul_comm]; exact (div_le_iff₀ hq_rpos).mp hcell.2.1
    linarith
  have hv1 : v < 1 := by
    have : (q : ℝ) * β < (b : ℝ) + 1 := by
      rw [mul_comm]; exact (lt_div_iff₀ hq_rpos).mp hcell.2.2
    linarith
  have hα_eq : α = ((a : ℝ) + u) / (q : ℝ) := by
    dsimp [u]; field_simp; ring
  have hβ_eq : β = ((b : ℝ) + v) / (q : ℝ) := by
    dsimp [v]; field_simp; ring
  have hno_wrap : ∀ k ∈ Finset.Icc 1 n, (b + k * a) % q + (n + 1) ≤ q := by
    intro k hk
    have : ¬ (q - (n + 1) ≤ (b + k * a) % q) := by
      intro hle
      exact hnotbad (Finset.mem_filter.mpr ⟨hab, ⟨k, hk, hle⟩⟩)
    omega
  have hfract_eq : ∀ k ∈ Finset.Icc 1 n,
      Int.fract (β + α * (k : ℝ)) =
        (((b + k * a) % q : ℕ) : ℝ) / (q : ℝ) + (v + (k : ℝ) * u) / (q : ℝ) := by
    intro k hk
    have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hdiv : b + k * a = q * ((b + k * a) / q) + (b + k * a) % q :=
      (Nat.div_add_mod (b + k * a) q).symm
    have hdiv_r : ((b : ℝ) + (k : ℝ) * (a : ℝ)) =
        (q : ℝ) * (((b + k * a) / q : ℕ) : ℝ) + (((b + k * a) % q : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    set x : ℝ := (((b + k * a) % q : ℕ) : ℝ) / (q : ℝ) + (v + (k : ℝ) * u) / (q : ℝ)
    have hdecomp : β + α * (k : ℝ) = ((((b + k * a) / q : ℕ) : ℤ) : ℝ) + x := by
      rw [hα_eq, hβ_eq, Int.cast_natCast]
      dsimp [x]
      have hne : (q : ℝ) ≠ 0 := hq_rpos.ne'
      field_simp [hne]
      linarith [hdiv_r]
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    have hx1 : x < 1 := by
      dsimp [x]
      rw [← add_div, div_lt_one hq_rpos]
      have hbound : (((b + k * a) % q : ℕ) : ℝ) + ((n : ℝ) + 1) ≤ (q : ℝ) := by
        exact_mod_cast hno_wrap k hk
      have hk_r : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk_le
      have hku : (k : ℝ) * u ≤ (n : ℝ) * 1 := by nlinarith
      linarith
    rw [hdecomp, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hx0, hx1⟩]
  have hF_eq : F n α β =
      G n a b - (∑ k ∈ Finset.Icc 1 n, (v + (k : ℝ) * u)) / (q : ℝ) := by
    dsimp only [F, G]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
      show n + 1 - 1 = n by omega, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hfract_eq, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div]
    ring
  rw [hF_eq]
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 n, (v + (k : ℝ) * u) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hsum_le : ∑ k ∈ Finset.Icc 1 n, (v + (k : ℝ) * u) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
    calc ∑ k ∈ Finset.Icc 1 n, (v + (k : ℝ) * u)
        ≤ ∑ _k ∈ Finset.Icc 1 n, ((n : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk_r : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
          nlinarith
      _ = (n : ℝ) * ((n : ℝ) + 1) := by
          rw [Finset.sum_const, Nat.card_Icc, show n + 1 - 1 = n by omega, nsmul_eq_mul]
  have hdiv_le :
      (∑ k ∈ Finset.Icc 1 n, (v + (k : ℝ) * u)) / (q : ℝ) ≤ ((n : ℝ) + 1) / (n : ℝ) ^ 2 := by
    calc (∑ k ∈ Finset.Icc 1 n, (v + (k : ℝ) * u)) / (q : ℝ)
        ≤ ((n : ℝ) * ((n : ℝ) + 1)) / (q : ℝ) := div_le_div_of_nonneg_right hsum_le hq_rpos.le
      _ = ((n : ℝ) + 1) / (n : ℝ) ^ 2 := by
          rw [hq_cast]; field_simp
  constructor
  · linarith
  · have : 0 ≤ (∑ k ∈ Finset.Icc 1 n, (v + (k : ℝ) * u)) / (q : ℝ) :=
      div_nonneg hsum_nonneg hq_rpos.le
    linarith

private lemma card_badPairs_le {n : ℕ} (hn : 2 ≤ n) :
    (badPairs n).card ≤ n ^ 3 * n * (n + 1) := by
  set q := n ^ 3 with hq_def
  have hnq : n + 1 ≤ q := by
    have h4 : 4 ≤ n ^ 2 := by nlinarith
    have h8 : 4 * n ≤ n ^ 3 := by nlinarith
    omega
  have hsub : badPairs n ⊆
      (Finset.Icc 1 n).biUnion fun k =>
        (Finset.range q).biUnion fun a =>
          ((Finset.range q).filter fun b => q - (n + 1) ≤ (b + k * a) % q).map
            ⟨fun b => (a, b), fun _ _ h => (Prod.mk.inj h).2⟩ := by
    intro ab hab
    simp only [badPairs, ← hq_def, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_range] at hab
    rcases hab with ⟨⟨ha, hb⟩, ⟨k, hk, hle⟩⟩
    refine Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_biUnion.mpr ⟨ab.1, Finset.mem_range.mpr ha, ?_⟩⟩
    exact Finset.mem_map.mpr ⟨ab.2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hle⟩, rfl⟩
  have hinner : ∀ k a,
      ((Finset.range q).filter fun b => q - (n + 1) ≤ (b + k * a) % q).card ≤ n + 1 := by
    intro k a
    calc ((Finset.range q).filter fun b => q - (n + 1) ≤ (b + k * a) % q).card
        ≤ (Finset.Ico (q - (n + 1)) q).card := by
          apply Finset.card_le_card_of_injOn (fun b => (b + k * a) % q)
          · intro b hb
            rw [Finset.mem_coe, Finset.mem_filter] at hb
            rw [Finset.mem_coe, Finset.mem_Ico]
            exact ⟨hb.2, Nat.mod_lt _ (by omega)⟩
          · intro b₁ hb₁ b₂ hb₂ heq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb₁ hb₂
            have hmod : b₁ + k * a ≡ b₂ + k * a [MOD q] := heq
            have hmod' : b₁ ≡ b₂ [MOD q] := Nat.ModEq.add_right_cancel' (k * a) hmod
            simpa [Nat.ModEq, Nat.mod_eq_of_lt hb₁.1, Nat.mod_eq_of_lt hb₂.1] using hmod'
      _ = n + 1 := by rw [Nat.card_Ico]; omega
  calc (badPairs n).card
      ≤ ((Finset.Icc 1 n).biUnion fun k =>
          (Finset.range q).biUnion fun a =>
            ((Finset.range q).filter fun b => q - (n + 1) ≤ (b + k * a) % q).map
              ⟨fun b => (a, b), fun _ _ h => (Prod.mk.inj h).2⟩).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc 1 n,
          ((Finset.range q).biUnion fun a =>
            ((Finset.range q).filter fun b => q - (n + 1) ≤ (b + k * a) % q).map
              ⟨fun b => (a, b), fun _ _ h => (Prod.mk.inj h).2⟩).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.Icc 1 n, ∑ a ∈ Finset.range q,
          (((Finset.range q).filter fun b => q - (n + 1) ≤ (b + k * a) % q).map
            ⟨fun b => (a, b), fun _ _ h => (Prod.mk.inj h).2⟩).card := by
        apply Finset.sum_le_sum; intro k _; exact Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, ∑ _a ∈ Finset.range q, (n + 1) := by
        apply Finset.sum_le_sum; intro k _
        apply Finset.sum_le_sum; intro a _
        rw [Finset.card_map]
        exact hinner k a
    _ = q * n * (n + 1) := by
        simp [Finset.sum_const, Nat.card_Icc]
        ring

private lemma measurable_fract_real : Measurable (Int.fract : ℝ → ℝ) := by
  have hfloor : Measurable (fun x : ℝ => (⌊x⌋ : ℝ)) :=
    Monotone.measurable fun _ _ h => Int.cast_le.mpr (Int.floor_mono h)
  exact measurable_id.sub hfloor

private lemma measurable_C_fn (n : ℕ) : Measurable (C_fn n) := by
  unfold C_fn
  refine measurable_const.sub ?_
  refine Finset.measurable_sum (Finset.Icc (1 : ℕ) n) fun k _ => ?_
  exact measurable_fract_real.comp (measurable_id.mul measurable_const)

private lemma volume_strip {n : ℕ} (hn : 1 ≤ n) (T B : ℝ) (m : ℕ) :
    volume (strip n T B m) = ENNReal.ofReal (B / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hg1 : Measurable (fun p : ℝ × ℝ => (C_fn n p.1 + (m : ℝ) - T) / (n : ℝ)) :=
    ((((measurable_C_fn n).comp measurable_fst).add measurable_const).sub measurable_const).div_const _
  have hg2 : Measurable (fun p : ℝ × ℝ => (C_fn n p.1 + (m : ℝ) - T + B) / (n : ℝ)) :=
    (((((measurable_C_fn n).comp measurable_fst).add measurable_const).sub
      measurable_const).add measurable_const).div_const _
  have hmeas : MeasurableSet (strip n T B m) := by
    have hset : strip n T B m =
        (Prod.fst ⁻¹' Ico (0 : ℝ) 1) ∩
        ({p : ℝ × ℝ | (C_fn n p.1 + (m : ℝ) - T) / (n : ℝ) ≤ p.2} ∩
         {p : ℝ × ℝ | p.2 < (C_fn n p.1 + (m : ℝ) - T + B) / (n : ℝ)}) := by
      ext ⟨α, β⟩; simp [strip]
    rw [hset]
    exact (measurableSet_Ico.preimage measurable_fst).inter
      ((measurableSet_le hg1 measurable_snd).inter (measurableSet_lt measurable_snd hg2))
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have hslice : ∀ α : ℝ,
      volume (Prod.mk α ⁻¹' strip n T B m) =
        (Ico (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (B / (n : ℝ))) α := by
    intro α
    by_cases hα : α ∈ Ico (0 : ℝ) 1
    · rw [Set.indicator_of_mem hα]
      have hpre : Prod.mk α ⁻¹' strip n T B m =
          Ico ((C_fn n α + (m : ℝ) - T) / (n : ℝ)) ((C_fn n α + (m : ℝ) - T + B) / (n : ℝ)) := by
        ext β
        simp only [Set.mem_preimage, strip, Set.mem_ofPred_eq, mem_Ico]
        exact ⟨fun h => h.2, fun h => ⟨hα, h⟩⟩
      rw [hpre, Real.volume_Ico]
      congr 1
      ring
    · rw [Set.indicator_of_notMem hα]
      have hpre : Prod.mk α ⁻¹' strip n T B m = ∅ := by
        ext β
        simp only [Set.mem_preimage, strip, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hα h.1
      rw [hpre, measure_empty]
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, Real.volume_Ico]
  simp

private lemma band_subset_biUnion_strip {n : ℕ} (hn : 1 ≤ n) (T B : ℝ) :
    band n T B ⊆ ⋃ m ∈ Finset.range (n + 1), strip n T B m := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  rintro ⟨α, β⟩ ⟨hα, hβ, hlt, hle⟩
  let S_jump : Finset ℕ :=
    (Finset.Icc (1 : ℕ) n).filter fun (k : ℕ) => 1 ≤ Int.fract (α * (k : ℝ)) + β
  let m := S_jump.card
  have hm_mem : m ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    have hcard : S_jump.card ≤ (Finset.Icc (1 : ℕ) n).card := Finset.card_filter_le _ _
    rw [Nat.card_Icc] at hcard
    omega
  refine Set.mem_iUnion₂.mpr ⟨m, hm_mem, ?_⟩
  have hterm : ∀ k ∈ Finset.Icc (1 : ℕ) n,
      Int.fract (β + α * (k : ℝ)) =
        Int.fract (α * (k : ℝ)) + β - if 1 ≤ Int.fract (α * (k : ℝ)) + β then (1 : ℝ) else 0 := by
    intro k _
    set x := α * (k : ℝ)
    have hx_decomp : β + x = (⌊x⌋ : ℝ) + (Int.fract x + β) := by
      linarith [Int.floor_add_fract x]
    by_cases h1 : 1 ≤ Int.fract x + β
    · rw [if_pos h1]
      have hshift : β + x = ((⌊x⌋ + 1 : ℤ) : ℝ) + (Int.fract x + β - 1) := by
        push_cast; linarith [hx_decomp]
      have hlt1 : Int.fract x + β - 1 < 1 := by
        linarith [Int.fract_lt_one x, hβ.2]
      rw [hshift, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by linarith, hlt1⟩]
    · rw [if_neg h1, sub_zero]
      have hnonneg : 0 ≤ Int.fract x + β := add_nonneg (Int.fract_nonneg x) hβ.1
      rw [hx_decomp, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hnonneg, not_le.mp h1⟩]
  have hsum_fract : ∑ k ∈ Finset.Icc (1 : ℕ) n, Int.fract (β + α * (k : ℝ)) =
      (∑ k ∈ Finset.Icc (1 : ℕ) n, Int.fract (α * (k : ℝ))) + (n : ℝ) * β - (m : ℝ) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, show n + 1 - 1 = n by omega, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_boole]
  have hF_eq : F n α β = C_fn n α - (n : ℝ) * β + (m : ℝ) := by
    dsimp only [F, C_fn]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
      show n + 1 - 1 = n by omega, nsmul_eq_mul, hsum_fract]
    ring
  refine ⟨hα, ?_, ?_⟩
  · rw [div_le_iff₀ hn_pos]
    linarith [hF_eq, hle]
  · rw [lt_div_iff₀ hn_pos]
    linarith [hF_eq, hlt]

private lemma volume_band_le {n : ℕ} (hn : 1 ≤ n) (T B : ℝ) :
    volume (band n T B) ≤ ENNReal.ofReal (((n : ℝ) + 1) * (B / (n : ℝ))) := by
  calc volume (band n T B)
      ≤ volume (⋃ m ∈ Finset.range (n + 1), strip n T B m) :=
        measure_mono (band_subset_biUnion_strip hn T B)
    _ ≤ ∑ m ∈ Finset.range (n + 1), volume (strip n T B m) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _m ∈ Finset.range (n + 1), ENNReal.ofReal (B / (n : ℝ)) := by
        refine Finset.sum_congr rfl fun m _ => volume_strip hn T B m
    _ = ENNReal.ofReal (((n : ℝ) + 1) * (B / (n : ℝ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        push_cast
        rfl

end Erdos1002KestenR2H2

open Filter MeasureTheory Real Set Topology Erdos1002KestenR2H2
open scoped BigOperators Classical

theorem OMA.solution : OMA.R_Erdos1002_erdos_1002_variants_kesten_R2.H2 := by
  intro c
  have hbound : ∀ n : ℕ, 2 ≤ n →
      ‖(volume {p : ℝ × ℝ |
          let ⟨α, β⟩ := p
          α ∈ Icc (0 : ℝ) 1 ∧ β ∈ Icc (0 : ℝ) 1 ∧
            (1 / Real.log (n : ℝ)) * ∑ k ∈ Finset.Icc (1 : ℕ) n,
              (1 / 2 - Int.fract (β + α * k)) ≤ c}).toReal -
        ((((Finset.range (n ^ 3)).product (Finset.range (n ^ 3))).filter fun ab =>
            (1 / Real.log (n : ℝ)) *
              ((n : ℝ) / 2 - (∑ k ∈ Finset.Icc 1 n,
                (((ab.2 + k * ab.1) % (n ^ 3) : ℕ) : ℝ)) / ((n ^ 3 : ℕ) : ℝ)) ≤ c).card : ℝ) /
          ((n ^ 3 : ℕ) : ℝ) ^ 2‖ ≤ 6 / (n : ℝ) := by
    intro n hn
    set q := n ^ 3 with hq_def
    have hq_pos : 0 < q := by positivity
    have hq_rpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
    have hn_rpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hq_cast : (q : ℝ) = (n : ℝ) ^ 3 := by simp [hq_def]
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    set T := c * Real.log (n : ℝ)
    set B := ((n : ℝ) + 1) / (n : ℝ) ^ 2
    have hB_nonneg : 0 ≤ B := by positivity
    have hiff : ∀ x : ℝ, (1 / Real.log (n : ℝ)) * x ≤ c ↔ x ≤ T := by
      intro x
      rw [one_div, inv_mul_le_iff₀ hL_pos, mul_comm]
    set pairs := (Finset.range q).product (Finset.range q)
    set good := pairs.filter fun ab => (1 / Real.log (n : ℝ)) * G n ab.1 ab.2 ≤ c
    set S_src : Set (ℝ × ℝ) :=
      {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ (1 / Real.log (n : ℝ)) * F n p.1 p.2 ≤ c}
    set S_ico : Set (ℝ × ℝ) :=
      {p | p.1 ∈ Ico (0 : ℝ) 1 ∧ p.2 ∈ Ico (0 : ℝ) 1 ∧ F n p.1 p.2 ≤ T}
    set S_grid : Set (ℝ × ℝ) := ⋃ ab ∈ good, cell q ab.1 ab.2
    set S_bad : Set (ℝ × ℝ) := ⋃ ab ∈ badPairs n, cell q ab.1 ab.2
    have hvol_src : volume S_src = volume S_ico := by
      have h1 : S_src = {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ F n p.1 p.2 ≤ T} := by
        ext ⟨α, β⟩; simp only [S_src, Set.mem_ofPred_eq, hiff]
      rw [h1]
      exact volume_Icc_eq_volume_Ico (fun p => F n p.1 p.2 ≤ T)
    have hvol_src_ne_top : volume S_src ≠ ⊤ := by
      have hsub : S_src ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun p hp => ⟨hp.1, hp.2.1⟩
      have hfin : volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) < ⊤ := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
        simp
      exact (lt_of_le_of_lt (measure_mono hsub) hfin).ne
    have hvol_grid : volume S_grid = ENNReal.ofReal ((good.card : ℝ) / (q : ℝ) ^ 2) :=
      volume_biUnion_cell hq_pos good (Finset.filter_subset _ _)
    have hvol_bad : volume S_bad ≤ ENNReal.ofReal B := by
      rw [volume_biUnion_cell hq_pos (badPairs n) (Finset.filter_subset _ _)]
      apply ENNReal.ofReal_le_ofReal
      have hcard : ((badPairs n).card : ℝ) ≤ (q : ℝ) * (n : ℝ) * ((n : ℝ) + 1) := by
        exact_mod_cast card_badPairs_le hn
      calc ((badPairs n).card : ℝ) / (q : ℝ) ^ 2
          ≤ ((q : ℝ) * (n : ℝ) * ((n : ℝ) + 1)) / (q : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hcard (by positivity)
        _ = B := by dsimp [B]; rw [hq_cast]; field_simp
    have hgrid_diff : S_grid \ S_ico ⊆ S_bad := by
      rintro ⟨α, β⟩ ⟨hgrid, hnot⟩
      rcases Set.mem_iUnion₂.mp hgrid with ⟨⟨a, b⟩, hab_good, hcell⟩
      have hab_pairs : (a, b) ∈ pairs := Finset.mem_of_mem_filter _ hab_good
      have hG_le : G n a b ≤ T := (hiff _).mp (Finset.mem_filter.mp hab_good).2
      by_contra hnot_bad_union
      have hnot_bad : (a, b) ∉ badPairs n := fun hb =>
        hnot_bad_union (Set.mem_iUnion₂.mpr ⟨(a, b), hb, hcell⟩)
      have hF_le : F n α β ≤ G n a b := (F_bounds_on_good_cell hn hab_pairs hnot_bad hcell).2
      have hα_ico : α ∈ Ico (0 : ℝ) 1 := by
        have ha : a < q := (Finset.mem_range.mp (Finset.mem_product.mp hab_pairs).1)
        simp only [cell, mem_prod, mem_Ico] at hcell
        refine ⟨le_trans (by positivity) hcell.1.1, lt_of_lt_of_le hcell.1.2 ?_⟩
        rw [div_le_one hq_rpos]
        exact_mod_cast ha
      have hβ_ico : β ∈ Ico (0 : ℝ) 1 := by
        have hb : b < q := (Finset.mem_range.mp (Finset.mem_product.mp hab_pairs).2)
        simp only [cell, mem_prod, mem_Ico] at hcell
        refine ⟨le_trans (by positivity) hcell.2.1, lt_of_lt_of_le hcell.2.2 ?_⟩
        rw [div_le_one hq_rpos]
        exact_mod_cast hb
      exact hnot ⟨hα_ico, hβ_ico, le_trans hF_le hG_le⟩
    have hico_diff : S_ico \ S_grid ⊆ S_bad ∪ band n T B := by
      rintro ⟨α, β⟩ ⟨⟨hα, hβ, hF_le⟩, hnot_grid⟩
      rcases mem_cell_of_mem_Ico hq_pos hα hβ with ⟨⟨a, b⟩, hab_pairs, hcell⟩
      by_cases hbad : (a, b) ∈ badPairs n
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨(a, b), hbad, hcell⟩)
      · right
        have hG_gt : T < G n a b := by
          by_contra hle
          push Not at hle
          have hab_good : (a, b) ∈ good :=
            Finset.mem_filter.mpr ⟨hab_pairs, (hiff _).mpr hle⟩
          exact hnot_grid (Set.mem_iUnion₂.mpr ⟨(a, b), hab_good, hcell⟩)
        have hF_ge : G n a b - B ≤ F n α β :=
          (F_bounds_on_good_cell hn hab_pairs hbad hcell).1
        exact ⟨hα, hβ, by linarith, hF_le⟩
    have hvol_upper : (volume S_src).toReal ≤
        (good.card : ℝ) / (q : ℝ) ^ 2 + (B + ((n : ℝ) + 1) * (B / (n : ℝ))) := by
      have hle_vol : volume S_src ≤
          ENNReal.ofReal ((good.card : ℝ) / (q : ℝ) ^ 2 + (B + ((n : ℝ) + 1) * (B / (n : ℝ)))) := by
        calc volume S_src = volume S_ico := hvol_src
          _ ≤ volume (S_grid ∪ (S_ico \ S_grid)) := measure_mono (fun x hx => by
              by_cases h : x ∈ S_grid; exact Or.inl h; exact Or.inr ⟨hx, h⟩)
          _ ≤ volume S_grid + volume (S_ico \ S_grid) := measure_union_le _ _
          _ ≤ volume S_grid + volume (S_bad ∪ band n T B) :=
              add_le_add le_rfl (measure_mono hico_diff)
          _ ≤ volume S_grid + (volume S_bad + volume (band n T B)) :=
              add_le_add le_rfl (measure_union_le _ _)
          _ ≤ ENNReal.ofReal ((good.card : ℝ) / (q : ℝ) ^ 2) +
                (ENNReal.ofReal B + ENNReal.ofReal (((n : ℝ) + 1) * (B / (n : ℝ)))) := by
              rw [hvol_grid]
              exact add_le_add le_rfl (add_le_add hvol_bad (volume_band_le (by omega) T B))
          _ = ENNReal.ofReal ((good.card : ℝ) / (q : ℝ) ^ 2 + (B + ((n : ℝ) + 1) * (B / (n : ℝ)))) := by
              rw [← ENNReal.ofReal_add hB_nonneg (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_vol
      rwa [ENNReal.toReal_ofReal (by positivity)] at hto
    have hvol_lower : (good.card : ℝ) / (q : ℝ) ^ 2 ≤ (volume S_src).toReal + B := by
      have hle_vol : ENNReal.ofReal ((good.card : ℝ) / (q : ℝ) ^ 2) ≤
          volume S_src + ENNReal.ofReal B := by
        calc ENNReal.ofReal ((good.card : ℝ) / (q : ℝ) ^ 2) = volume S_grid := hvol_grid.symm
          _ ≤ volume (S_ico ∪ (S_grid \ S_ico)) := measure_mono (fun x hx => by
              by_cases h : x ∈ S_ico; exact Or.inl h; exact Or.inr ⟨hx, h⟩)
          _ ≤ volume S_ico + volume (S_grid \ S_ico) := measure_union_le _ _
          _ ≤ volume S_src + volume S_bad := by
              rw [hvol_src]; exact add_le_add le_rfl (measure_mono hgrid_diff)
          _ ≤ volume S_src + ENNReal.ofReal B := add_le_add le_rfl hvol_bad
      have hto := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hvol_src_ne_top, ENNReal.ofReal_ne_top⟩) hle_vol
      rw [ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_add hvol_src_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hB_nonneg] at hto
      exact hto
    have herr_le : B + ((n : ℝ) + 1) * (B / (n : ℝ)) ≤ 6 / (n : ℝ) := by
      dsimp [B]
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h1 : ((n : ℝ) + 1) / (n : ℝ) ^ 2 ≤ 2 / (n : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hn_rpos]
        nlinarith
      have h2 : ((n : ℝ) + 1) * (((n : ℝ) + 1) / (n : ℝ) ^ 2 / (n : ℝ)) ≤ 4 / (n : ℝ) := by
        have : ((n : ℝ) + 1) * (((n : ℝ) + 1) / (n : ℝ) ^ 2 / (n : ℝ)) =
            ((n : ℝ) + 1) ^ 2 / (n : ℝ) ^ 3 := by ring
        rw [this, div_le_div_iff₀ (by positivity) hn_rpos]
        nlinarith
      calc ((n : ℝ) + 1) / (n : ℝ) ^ 2 + ((n : ℝ) + 1) * (((n : ℝ) + 1) / (n : ℝ) ^ 2 / (n : ℝ))
          ≤ 2 / (n : ℝ) + 4 / (n : ℝ) := add_le_add h1 h2
        _ = 6 / (n : ℝ) := by ring
    change ‖(volume S_src).toReal - (good.card : ℝ) / (q : ℝ) ^ 2‖ ≤ 6 / (n : ℝ)
    rw [Real.norm_eq_abs, abs_le]
    have hnonneg2 : 0 ≤ ((n : ℝ) + 1) * (B / (n : ℝ)) := by positivity
    constructor <;> linarith
  refine squeeze_zero_norm' (a := fun n : ℕ => (6 : ℝ) / (n : ℝ)) ?_ ?_
  · exact eventually_atTop.mpr ⟨2, hbound⟩
  · exact tendsto_const_div_atTop_nhds_zero_nat 6
