import OMAReductions.R_Erdos210_erdos_210_variants_csima_sawyer_R1

/-! In homogeneous coordinates normalized off an ordinary line, an
attachment is minimal or maximal in each of two independent coordinates. -/

open EuclideanGeometry Finset
open scoped EuclideanGeometry Classical

namespace OMA.Attachment

abbrev HSpace := Fin 3 → ℝ

noncomputable def hom (p : ℝ²) : HSpace := ![p 0, p 1, 1]

noncomputable def minor (u v : HSpace) : HSpace →ₗ[ℝ] ℝ where
  toFun x := x 0 * (u 1 * v 2 - u 2 * v 1) +
    x 1 * (u 2 * v 0 - u 0 * v 2) + x 2 * (u 0 * v 1 - u 1 * v 0)
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' r x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] lemma minor_left (u v : HSpace) : minor u v u = 0 := by
  dsimp [minor]
  ring

@[simp] lemma minor_right (u v : HSpace) : minor u v v = 0 := by
  dsimp [minor]
  ring

lemma pl_ext {x y : ℝ²} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

lemma minor_off_line {p q z : ℝ²} (hpq : p ≠ q)
    (hz : z ∉ line[ℝ, p, q]) : minor (hom p) (hom q) (hom z) ≠ 0 := by
  intro h
  have hcross : (q 0 - p 0) * (z 1 - p 1) = (q 1 - p 1) * (z 0 - p 0) := by
    simp [minor, hom] at h
    nlinarith only [h]
  apply hz
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  by_cases hx : q 0 = p 0
  · have hy : q 1 - p 1 ≠ 0 := by
      intro he
      exact hpq (pl_ext hx.symm (sub_eq_zero.mp he).symm)
    refine ⟨(z 1 - p 1) / (q 1 - p 1), ?_⟩
    rw [AffineMap.lineMap_apply_module']
    apply pl_ext
    · change (z 1 - p 1) / (q 1 - p 1) * (q 0 - p 0) + p 0 = z 0
      rw [hx, sub_self, mul_zero, zero_add]
      rw [hx, sub_self, zero_mul, eq_comm, mul_eq_zero] at hcross
      exact (sub_eq_zero.mp (hcross.resolve_left hy)).symm
    · change (z 1 - p 1) / (q 1 - p 1) * (q 1 - p 1) + p 1 = z 1
      rw [div_mul_cancel₀ _ hy, sub_add_cancel]
  · have hnx : q 0 - p 0 ≠ 0 := sub_ne_zero.mpr hx
    refine ⟨(z 0 - p 0) / (q 0 - p 0), ?_⟩
    rw [AffineMap.lineMap_apply_module']
    apply pl_ext
    · change (z 0 - p 0) / (q 0 - p 0) * (q 0 - p 0) + p 0 = z 0
      rw [div_mul_cancel₀ _ hnx, sub_add_cancel]
    · change (z 0 - p 0) / (q 0 - p 0) * (q 1 - p 1) + p 1 = z 1
      apply (eq_sub_iff_add_eq).mp
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff hnx).mpr
      simpa [mul_comm] using hcross.symm

def extreme (s : Finset ℝ²) (f : ℝ² → ℝ) (w : ℝ²) : Prop :=
  (∀ z ∈ s, f w ≤ f z) ∨ (∀ z ∈ s, f z ≤ f w)

def given (s : Finset ℝ²) (u v w : HSpace) : Prop :=
  ∀ z ∈ s, ∃ a b c : ℝ, hom z = a • u + b • v + c • w ∧
    ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))

lemma given_swap {s : Finset ℝ²} {u v w : HSpace} (h : given s u v w) :
    given s v u w := by
  intro z hz
  obtain ⟨a, b, c, he, hs⟩ := h z hz
  refine ⟨b, a, c, ?_, ?_⟩
  · rw [he, add_comm (a • u)]
  · rcases hs with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
    · exact Or.inl ⟨hb,ha,hc⟩
    · exact Or.inr ⟨hb,ha,hc⟩

lemma coordinate_extreme {s : Finset ℝ²} {u v : HSpace} {w : ℝ²} {δ : ℝ}
    (C X : HSpace →ₗ[ℝ] ℝ) (hCu : C u = 0) (hCv : C v = 0)
    (hXv : X v = 0) (hw : C (hom w) ≠ 0) (hδ : δ ≠ 0)
    (hs : ∀ z ∈ s, C (hom z) ≠ 0) (h : given s u v (δ • hom w)) :
    extreme s (fun z => X (hom z) / C (hom z)) w := by
  have hd (z : ℝ²) (hz : z ∈ s) :
      ∃ t : ℝ, 0 ≤ t ∧ X (hom z) / C (hom z) - X (hom w) / C (hom w) =
        t * (X u / (δ * C (hom w))) := by
    obtain ⟨a, b, c, he, hsgn⟩ := h z hz
    have hc : C (hom z) = c * (δ * C (hom w)) := by
      rw [he]
      simp [hCu, hCv]
    have hx : X (hom z) = a * X u + c * (δ * X (hom w)) := by
      rw [he]
      simp [hXv]
    have hcn : c ≠ 0 := by
      intro hn
      exact hs z hz (by simp [hc, hn])
    refine ⟨a / c, ?_, ?_⟩
    · rcases hsgn with ⟨ha, _, hca⟩ | ⟨ha, _, hca⟩
      · exact div_nonneg ha hca
      · exact div_nonneg_of_nonpos ha hca
    · rw [hx, hc]
      field_simp [hcn, hδ, hw]
      ring
  by_cases hcoeff : 0 ≤ X u / (δ * C (hom w))
  · left
    intro z hz
    obtain ⟨t, ht, he⟩ := hd z hz
    exact sub_nonneg.mp (he.symm ▸ mul_nonneg ht hcoeff)
  · right
    intro z hz
    obtain ⟨t, ht, he⟩ := hd z hz
    exact sub_nonpos.mp (he.symm ▸ mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_ge hcoeff))

lemma coordinate_inj {p q u z w : ℝ²}
    (hD : minor (hom p) (hom q) (hom u) ≠ 0)
    (hz : minor (hom p) (hom q) (hom z) ≠ 0)
    (hw : minor (hom p) (hom q) (hom w) ≠ 0)
    (ha : minor (hom q) (hom u) (hom z) / minor (hom p) (hom q) (hom z) =
      minor (hom q) (hom u) (hom w) / minor (hom p) (hom q) (hom w))
    (hb : minor (hom u) (hom p) (hom z) / minor (hom p) (hom q) (hom z) =
      minor (hom u) (hom p) (hom w) / minor (hom p) (hom q) (hom w)) : z = w := by
  let A := minor (hom q) (hom u)
  let B := minor (hom u) (hom p)
  let C := minor (hom p) (hom q)
  have hcz : C (hom z) ≠ 0 := hz
  have hcw : C (hom w) ≠ 0 := hw
  have repr (x : HSpace) (i : Fin 3) :
      A x * hom p i + B x * hom q i + C x * hom u i = C (hom u) * x i := by
    fin_cases i <;> simp [A, B, C, minor, hom] <;> ring
  have eq (i : Fin 3) :
      C (hom u) / C (hom z) * hom z i = C (hom u) / C (hom w) * hom w i := by
    calc
      _ = A (hom z) / C (hom z) * hom p i +
          B (hom z) / C (hom z) * hom q i + hom u i := by
        field_simp [hcz]
        linarith only [repr (hom z) i]
      _ = A (hom w) / C (hom w) * hom p i +
          B (hom w) / C (hom w) * hom q i + hom u i := by
        change A (hom z) / C (hom z) = A (hom w) / C (hom w) at ha
        change B (hom z) / C (hom z) = B (hom w) / C (hom w) at hb
        rw [ha, hb]
      _ = _ := by
        field_simp [hcw]
        linarith only [repr (hom w) i]
  have he : C (hom u) / C (hom z) = C (hom u) / C (hom w) := by
    simpa [hom] using eq 2
  have hident (i : Fin 3) : hom z i = hom w i := by
    have h := eq i
    rw [← he] at h
    exact mul_left_cancel₀ (div_ne_zero hD hz) h
  apply pl_ext
  · simpa [hom] using hident 0
  · simpa [hom] using hident 1

noncomputable def minTag (s : Finset ℝ²) (f : ℝ² → ℝ) (w : ℝ²) : Bool :=
  @decide (∀ z ∈ s, f w ≤ f z) (Classical.propDecidable _)

lemma minTag_eq {s : Finset ℝ²} {f : ℝ² → ℝ} {z w : ℝ²}
    (hz : z ∈ s) (hw : w ∈ s) (he1 : extreme s f z) (he2 : extreme s f w)
    (h : minTag s f z = minTag s f w) : f z = f w := by
  classical
  have he : (∀ y ∈ s, f z ≤ f y) ↔ (∀ y ∈ s, f w ≤ f y) := by
    constructor
    · intro hp
      have ht : minTag s f z = true := @decide_eq_true _ (Classical.propDecidable _) hp
      exact @of_decide_eq_true _ (Classical.propDecidable _) (h.symm.trans ht)
    · intro hp
      have ht : minTag s f w = true := @decide_eq_true _ (Classical.propDecidable _) hp
      exact @of_decide_eq_true _ (Classical.propDecidable _) (h.trans ht)
  by_cases hm : ∀ y ∈ s, f z ≤ f y
  · exact le_antisymm (hm w hw) ((he.mp hm) z hz)
  · exact le_antisymm ((he2.resolve_left (mt he.mpr hm)) z hz)
      ((he1.resolve_left hm) w hw)

def attached (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) (w : ℝ²) : Prop :=
  ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
    ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧ given s (hom p) (ε • hom q) (δ • hom w)

lemma four (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) (hL : L ∈ ordinaryLines s) :
    (s.filter (attached s L)).card ≤ 4 := by
  classical
  obtain ⟨⟨p, hp, q, hq, hpq, rfl⟩, hcard⟩ := mem_ordinaryLines.mp hL
  let L := line[ℝ, p, q]
  let T := s.filter (attached s L)
  change T.card ≤ 4
  by_cases hn : T.Nonempty
  swap
  · exact (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)).le.trans (by decide)
  obtain ⟨u, hu⟩ := hn
  have outside {w : ℝ²} (hw : w ∈ T) : w ∉ L := by
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := (mem_filter.mp hw).2
    exact h
  let U := s.filter (fun w => w ∉ L)
  have sub : T ⊆ U := fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1, outside h⟩
  let C := minor (hom p) (hom q)
  let A := minor (hom q) (hom u)
  let B := minor (hom u) (hom p)
  let f (w : ℝ²) := A (hom w) / C (hom w)
  let g (w : ℝ²) := B (hom w) / C (hom w)
  have hc (w : ℝ²) (hw : w ∈ U) : C (hom w) ≠ 0 :=
    minor_off_line hpq (mem_filter.mp hw).2
  have hend : s.filter (· ∈ L) = {p, q} := by
    symm
    refine eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact mem_filter.mpr ⟨hp, left_mem_affineSpan_pair ℝ p q⟩
      · rw [hx]
        exact mem_filter.mpr ⟨hq, right_mem_affineSpan_pair ℝ p q⟩
    · simpa [L, hpq] using hcard.le
  have hex (w : ℝ²) (hw : w ∈ T) : extreme U f w ∧ extreme U g w := by
    obtain ⟨p', hp', q', hq', hne, hpL, hqL, _, ε, δ, _, hδ, h⟩ := (mem_filter.mp hw).2
    have hpq' (x : ℝ²) (hx : x ∈ s) (hxL : x ∈ L) : x = p ∨ x = q := by
      have hm : x ∈ s.filter (· ∈ L) := mem_filter.mpr ⟨hx,hxL⟩
      simpa [hend] using hm
    have hδ0 : δ ≠ 0 := by
      intro hz
      simp [hz] at hδ
    have restrict {a b : HSpace} (h : given s a b (δ • hom w)) :
        given U a b (δ • hom w) := fun x hx => h x (mem_filter.mp hx).1
    have first {a b : ℝ} (h : given U (a • hom p) (b • hom q) (δ • hom w)) :
        extreme U f w ∧ extreme U g w :=
      ⟨coordinate_extreme C A (by simp [C]) (by simp [C]) (by simp [A]) (hc w (sub hw)) hδ0 hc h,
       coordinate_extreme C B (by simp [C]) (by simp [C]) (by simp [B]) (hc w (sub hw)) hδ0 hc
         (given_swap h)⟩
    rcases hpq' p' hp' hpL with rfl | rfl <;> rcases hpq' q' hq' hqL with rfl | rfl
    · exact (hne rfl).elim
    · exact first (a := 1) (b := ε) (by simpa using restrict h)
    · exact first (a := ε) (b := 1) (by simpa using given_swap (restrict h))
    · exact (hne rfl).elim
  let tag (w : ↥T) : Bool × Bool := (minTag U f w, minTag U g w)
  have ht : Function.Injective tag := by
    intro z w h
    apply Subtype.ext
    exact coordinate_inj (hc u (sub hu)) (hc z (sub z.property)) (hc w (sub w.property))
      (minTag_eq (sub z.property) (sub w.property) (hex z z.property).1 (hex w w.property).1
        (congrArg Prod.fst h))
      (minTag_eq (sub z.property) (sub w.property) (hex z z.property).2 (hex w w.property).2
        (congrArg Prod.snd h))
  have h := Fintype.card_le_of_injective tag ht
  simpa using h

end OMA.Attachment

theorem OMA.solution : OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1.H2 := by
  classical
  intro s _ _
  dsimp only
  intro L hL
  refine (Finset.card_le_card ?_).trans (OMA.Attachment.four s L hL)
  intro w hw
  simpa only [Finset.mem_filter, OMA.Attachment.attached, OMA.Attachment.given,
    OMA.Attachment.hom] using hw
