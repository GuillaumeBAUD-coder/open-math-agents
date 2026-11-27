import OMAReductions.R_Erdos652_erdos_652_variants_order_sqrt_R1

/-! A rectangular version of Elekes's construction. The grid has `m` columns and
`k*m` radial levels. Adapted from the square-grid proof by @Deldor14. -/
open scoped EuclideanGeometry
open Finset Filter
namespace OMA.E652Rectangle
noncomputable section

private def anchor (h : ℕ) : ℝ² := WithLp.toLp 2 ![(h : ℝ), 0]
private def grid (m r : ℕ) (p : Fin m × Fin r) : ℝ² :=
  WithLp.toLp 2 ![-(p.1.val : ℝ), Real.sqrt ((m : ℝ)^2 + p.2.val - (p.1.val : ℝ)^2)]

private theorem height_nonneg (m r : ℕ) (p : Fin m × Fin r) :
    0 ≤ (m : ℝ)^2 + p.2.val - (p.1.val : ℝ)^2 := by
  have hx : (p.1.val : ℝ) ≤ m := by exact_mod_cast p.1.isLt.le
  have hs := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) p.1.val) hx
  nlinarith [Nat.cast_nonneg (α := ℝ) p.2.val]

private theorem grid_inj (m r : ℕ) : Function.Injective (grid m r) := by
  intro p q hpq
  have h₁ := congrArg (fun z : ℝ² => z 0) hpq
  change -(p.1.val : ℝ) = -(q.1.val : ℝ) at h₁
  have hx : p.1 = q.1 := Fin.ext (by exact_mod_cast neg_inj.mp h₁)
  have h₂ := congrArg (fun z : ℝ² => (z 1)^2) hpq
  change (Real.sqrt _)^2 = (Real.sqrt _)^2 at h₂
  rw [Real.sq_sqrt (height_nonneg m r p), Real.sq_sqrt (height_nonneg m r q), hx] at h₂
  exact Prod.ext hx (Fin.ext (by exact_mod_cast (show (p.2.val : ℝ) = q.2.val by linarith)))

private theorem grid_dist (m r h : ℕ) (p : Fin m × Fin r) :
    dist (grid m r p) (anchor h) =
      Real.sqrt ((m : ℝ)^2 + (h : ℝ)^2 + (p.2.val + 2*h*p.1.val : ℕ)) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  congr 1
  simp only [Real.dist_eq, sq_abs]
  change (-(p.1.val : ℝ) - h)^2 + (Real.sqrt _ - 0)^2 = _
  rw [sub_zero, Real.sq_sqrt (height_nonneg m r p)]
  push_cast
  ring

theorem construction (k n m : ℕ) (hk : k ≤ n) (hn : n ≤ m * (k * m)) :
    ∃ pts : Finset ℝ², pts.card = n ∧
      k ≤ (pts.filter fun v => distinctDistancesFrom pts v ≤ k + 3*k*m).card := by
  classical
  let A := (range k).image anchor
  let B := univ.image (grid m (k*m))
  have hai : Function.Injective anchor := by
    intro a b hab
    have he := congrArg (fun z : ℝ² => z 0) hab
    change (a : ℝ) = (b : ℝ) at he
    exact_mod_cast he
  have ha : A.card = k := by simp [A, card_image_of_injective _ hai]
  have hb : B.card = m * (k*m) := by simp [B, card_image_of_injective _ (grid_inj m (k*m))]
  obtain ⟨pts, hA, hpts, hcard⟩ := exists_subsuperset_card_eq
    (subset_union_left : A ⊆ A ∪ B) (ha ▸ hk)
    (hn.trans (hb ▸ card_le_card (subset_union_right : B ⊆ A ∪ B)))
  refine ⟨pts, hcard, ha.ge.trans (card_le_card (s := A) ?_)⟩
  intro x hx
  obtain ⟨h, hh, rfl⟩ := mem_image.mp hx
  have hhk := mem_range.mp hh
  refine mem_filter.mpr ⟨hA (mem_image.mpr ⟨h,hh,rfl⟩), ?_⟩
  let D := (range (3*k*m)).image (fun j : ℕ => Real.sqrt ((m:ℝ)^2 + (h:ℝ)^2 + j))
  have sub : ((pts.erase (anchor h)).image fun y => dist y (anchor h)) ⊆
      (A.image fun y => dist y (anchor h)) ∪ D := by
    rintro _ hy
    obtain ⟨y, hypts, rfl⟩ := mem_image.mp hy
    rcases mem_union.mp (hpts (mem_of_mem_erase hypts)) with ha' | hb'
    · exact mem_union_left _ (mem_image_of_mem _ ha')
    · obtain ⟨p, _, rfl⟩ := mem_image.mp hb'
      apply mem_union_right
      refine mem_image.mpr ⟨p.2.val+2*h*p.1.val, mem_range.mpr ?_, (grid_dist m (k*m) h p).symm⟩
      have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hhk.le) p.1.isLt.le
      nlinarith [p.2.isLt]
  have deq : distinctDistancesFrom pts (anchor h) =
      ((pts.erase (anchor h)).image fun y => dist y (anchor h)).card := by
    unfold distinctDistancesFrom
    apply congrArg Finset.card
    ext d
    simp only [mem_image, mem_erase]
  rw [deq]
  exact (card_le_card sub).trans ((card_union_le ..).trans <| Nat.add_le_add
    (card_image_le.trans ha.le) (card_image_le.trans (card_range _).le))
end
end OMA.E652Rectangle

theorem OMA.solution : OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1.H2 :=
  OMA.E652Rectangle.construction
