import FormalConjectures.ErdosProblems.«1038»

/-!
Finite-product duality for the upper bound in Erdős problem 1038, following the
two-point and tail cases in Section 2 of Terence Tao, *Sublevel sets of logarithmic
potentials* (2025). Points of a finite certificate may repeat, giving rational
weights after normalization. The polynomial factorization follows the argument
in the project's proof of Erdos1038.erdos_1038.variants.inf_lowerBound.

https://terrytao.wordpress.com/wp-content/uploads/2025/12/erdos-1038-1.pdf
-/

open scoped BigOperators Real ENNReal
open MeasureTheory Set Polynomial

namespace OMA.R_Erdos1038_erdos_1038_parts_ii_R1

/-- The two-point certificate for a pair with central endpoints. Positive
integer multiplicities avoid logarithms at zero in the duality argument. -/
def H1 : Prop :=
  ∀ x y : ℝ, -(1.7624 : ℝ) ≤ x → y ≤ 1.7624 → 2 * Real.sqrt 2 < y - x →
    ∃ p q : ℕ, ∀ t ∈ Icc (-1 : ℝ) 1, 1 ≤ |x - t| ^ (p + 1) * |y - t| ^ (q + 1)

/-- A finite dual certificate on a large open set reaching past the central
range. Only finitely many test points are specified, so the certificate need
only bound the potential there. -/
def H2 : Prop :=
  ∀ E : Set ℝ, IsOpen E → E ⊆ Ioo (-2) 2 →
    ENNReal.ofReal (2 * Real.sqrt 2) < volume E →
    (∃ x ∈ E, (1.7624 : ℝ) < |x|) →
    ∀ (n : ℕ) (r : Fin n → ℝ), (∀ i, r i ∈ Icc (-1 : ℝ) 1) →
    ∃ (k : ℕ) (w : Fin (k + 1) → ℝ), (∀ j, w j ∈ E) ∧
      ∀ i, 1 ≤ ∏ j, |w j - r i|

theorem exists_gap {E : Set ℝ} {d : ℝ} (hE : E ⊆ Ioo (-2) 2)
    (hvol : ENNReal.ofReal d < volume E) : ∃ x ∈ E, ∃ y ∈ E, d < y - x := by
  have hn : E.Nonempty := by
    by_contra! h
    simp [h] at hvol
  have hb : BddBelow E := ⟨-2, fun x hx => (hE hx).1.le⟩
  have ha : BddAbove E := ⟨2, fun x hx => (hE hx).2.le⟩
  by_contra! h
  have hwidth : sSup E ≤ d + sInf E := by
    apply csSup_le hn
    intro y hy
    have hy' : y - d ≤ sInf E :=
      le_csInf hn fun x hx => by linarith [h x hx y hy]
    linarith
  have hbox : E ⊆ Icc (sInf E) (sSup E) :=
    fun x hx => ⟨csInf_le hb hx, le_csSup ha hx⟩
  apply hvol.not_ge
  calc
    volume E ≤ volume (Icc (sInf E) (sSup E)) := measure_mono hbox
    _ = ENNReal.ofReal (sSup E - sInf E) := Real.volume_Icc
    _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal (by linarith)

theorem prod_bound (hc : H1) (ht : H2) {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) :
    volume {x : ℝ | (∏ i, |x - r i|) < 1} ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  classical
  let E := {x : ℝ | (∏ i, |x - r i|) < 1}
  have hnonneg (x : ℝ) : 0 ≤ ∏ i, |x - r i| :=
    Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hbox : E ⊆ Ioo (-2) 2 := by
    intro x hx
    change (∏ i, |x - r i|) < 1 at hx
    constructor
    · by_contra! h
      apply hx.not_ge
      apply Finset.one_le_prod
      intro i _
      have t := (hr i).1
      calc
        1 ≤ -(x - r i) := by linarith
        _ ≤ |x - r i| := neg_le_abs _
    · by_contra! h
      apply hx.not_ge
      apply Finset.one_le_prod
      intro i _
      exact le_trans (by linarith [(hr i).2] : 1 ≤ x - r i) (le_abs_self _)
  by_contra! hvol
  change ENNReal.ofReal (2 * Real.sqrt 2) < volume E at hvol
  by_cases hfar : ∃ x ∈ E, (1.7624 : ℝ) < |x|
  · have hopen : IsOpen E :=
      isOpen_lt (continuous_finsetProd _ fun i _ => (continuous_id.sub continuous_const).abs)
        continuous_const
    obtain ⟨k, w, hw, hdual⟩ := ht E hopen hbox hvol hfar n r hr
    have hrows : (∏ j, ∏ i, |w j - r i|) < 1 := by
      rw [Fin.prod_univ_succ]
      have hrest : (∏ j : Fin k, ∏ i, |w j.succ - r i|) ≤ 1 :=
        Finset.prod_le_one (fun j _ => hnonneg _) (fun j _ => le_of_lt (hw j.succ))
      exact (mul_le_of_le_one_right (hnonneg _) hrest).trans_lt (hw 0)
    rw [Finset.prod_comm] at hrows
    exact hrows.not_ge (Finset.one_le_prod fun i _ => hdual i)
  · obtain ⟨x, hx, y, hy, hxy⟩ := exists_gap hbox hvol
    push Not at hfar
    obtain ⟨p, q, hdual⟩ :=
      hc x y (abs_le.mp (hfar x hx)).1 (abs_le.mp (hfar y hy)).2 hxy
    have hcols := Finset.one_le_prod (s := Finset.univ) (fun i _ => hdual (r i) (hr i))
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow] at hcols
    have hxp : (∏ i, |x - r i|) ^ (p + 1) < 1 :=
      pow_lt_one₀ (hnonneg x) hx (by omega)
    have hyq : (∏ i, |y - r i|) ^ (q + 1) ≤ 1 :=
      pow_le_one₀ (hnonneg y) (le_of_lt hy)
    exact hxp.not_ge (hcols.trans (mul_le_of_le_one_right (by positivity) hyq))

theorem main : H1 → H2 → type_of% @Erdos1038.erdos_1038.parts.ii := by
  classical
  intro hc ht
  refine le_antisymm Erdos1038.erdos_1038.variants.sup_lowerBound (iSup_le ?_)
  rintro ⟨f, hmonic, hf⟩
  have hle := f.card_roots'
  have hge := Multiset.card_le_card (Multiset.filter_le (fun x => x ∈ Icc (-1 : ℝ) 1) f.roots)
  have hcard : f.roots.card = f.natDegree := by omega
  have hfilter : f.roots.filter (fun x => x ∈ Icc (-1 : ℝ) 1) = f.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (by omega)
  let L := f.roots.toList
  let r : Fin L.length → ℝ := L.get
  have hr (i : Fin L.length) : r i ∈ Icc (-1 : ℝ) 1 := by
    have hmem : r i ∈ f.roots := Multiset.mem_toList.mp (List.get_mem L i)
    exact (Multiset.mem_filter.mp (hfilter.symm ▸ hmem)).2
  have he (x : ℝ) : |f.eval x| = ∏ i, |x - r i| := by
    rw [(Polynomial.splits_iff_card_roots.mpr hcard).eval_eq_prod_roots_of_monic hmonic]
    change |(f.roots.map fun t => x - t).prod| = _
    rw [← f.roots.coe_toList]
    simp only [Multiset.map_coe, Multiset.prod_coe]
    change |(L.map fun t => x - t).prod| = _
    calc
      _ = |((List.ofFn r).map fun t => x - t).prod| := by
        rw [show List.ofFn r = L from List.ofFn_get L]
      _ = _ := by
        rw [List.map_ofFn, List.prod_ofFn, Finset.abs_prod]
        rfl
  change volume {x : ℝ | |f.eval x| < 1} ≤ _
  simp_rw [he]
  calc
    _ ≤ ENNReal.ofReal (2 * Real.sqrt 2) := prod_bound hc ht r hr
    _ = 2 * 2 ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_mul zero_le_two, Real.sqrt_eq_rpow,
        ← ENNReal.ofReal_rpow_of_nonneg zero_le_two (by norm_num)]
      norm_num

end OMA.R_Erdos1038_erdos_1038_parts_ii_R1
