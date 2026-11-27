import OMAReductions.R_Erdos507_erdos_507_variants_lower_kps82_R1
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


/-! Slice counting for small triangles on an integer grid. The estimate is
valid before normalization to the unit disk. -/

namespace OMA.HeilbronnGrid

open Finset
open scoped BigOperators

private theorem fiber_bound {m : ℕ} (a b t : ℝ) (ha : a ≠ 0) (ht : 0 ≤ t) :
    (((univ : Finset (Fin m)).filter fun x => |a*(x.val : ℝ)+b| ≤ t).card : ℝ)
      ≤ 1 + 2*t/|a| := by
  let S := (univ : Finset (Fin m)).filter fun x => |a*(x.val : ℝ)+b| ≤ t
  change (S.card : ℝ) ≤ _
  by_cases hS : S.Nonempty
  · let P := S.image Fin.val
    have hP : P.Nonempty := hS.image Fin.val
    let lo := P.min' hP
    let hi := P.max' hP
    have hLo : lo ∈ P := P.min'_mem hP
    have hHi : hi ∈ P := P.max'_mem hP
    have hOrder : lo ≤ hi := P.min'_le hi hHi
    have hsub : P ⊆ Icc lo hi :=
      fun j hj => mem_Icc.mpr ⟨P.min'_le j hj, P.le_max' j hj⟩
    have hcard : S.card ≤ hi + 1 - lo := by
      have hinj : Function.Injective (Fin.val : Fin m → ℕ) := Fin.val_injective
      rw [← card_image_of_injective S hinj]
      change P.card ≤ _
      simpa [Nat.card_Icc] using card_le_card hsub
    have hlo : |a*(lo : ℝ)+b| ≤ t := by
      obtain ⟨x, hx, hval⟩ := mem_image.mp hLo
      rw [← hval]
      exact (mem_filter.mp hx).2
    have hhi : |a*(hi : ℝ)+b| ≤ t := by
      obtain ⟨x, hx, hval⟩ := mem_image.mp hHi
      rw [← hval]
      exact (mem_filter.mp hx).2
    have hOrderR : (lo : ℝ) ≤ hi := by exact_mod_cast hOrder
    have hw : |a| * ((hi : ℝ)-lo) ≤ 2*t := by
      rw [← abs_of_nonneg (sub_nonneg.mpr hOrderR), ← abs_mul]
      rw [show a*((hi : ℝ)-lo) = (a*hi+b)-(a*lo+b) by ring]
      exact (abs_sub _ _).trans (by linarith)
    have hAbs : 0 < |a| := abs_pos.mpr ha
    have hw' : (hi : ℝ)-lo ≤ 2*t/|a| := (le_div_iff₀ hAbs).mpr (by simpa only [mul_comm] using hw)
    have hc : (S.card : ℝ) ≤ ((hi + 1 - lo : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_sub (by omega : lo ≤ hi+1), Nat.cast_add, Nat.cast_one] at hc
    linarith
  · have hzero : S.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hS)
    rw [hzero, Nat.cast_zero]
    positivity

theorem strip_bound {m : ℕ} (a b c t : ℝ) (hb : b ≠ 0) (ht : 0 ≤ t) :
    (((univ : Finset (Fin m × Fin m)).filter
      fun p => |a*(p.1.val : ℝ)+b*(p.2.val : ℝ)+c| ≤ t).card : ℝ)
      ≤ (m : ℝ) * (1 + 2*t/|b|) := by
  let strip := ((univ : Finset (Fin m × Fin m)).filter
      fun p => |a*(p.1.val : ℝ)+b*(p.2.val : ℝ)+c| ≤ t)
  let ys (x : Fin m) := (univ : Finset (Fin m)).filter
      fun y => |a*(x.val : ℝ)+b*(y.val : ℝ)+c| ≤ t
  have hcount : strip.card = ∑ x : Fin m, (ys x).card := by
    rw [card_filter, Fintype.sum_prod_type]
    simp only [ys, card_filter]
  have hslice (x : Fin m) : ((ys x).card : ℝ) ≤ 1 + 2*t/|b| := by
    simpa only [ys, add_comm (a*(x.val : ℝ)), add_assoc] using fiber_bound b (a*x.val+c) t hb ht
  change (strip.card : ℝ) ≤ _
  rw [hcount, Nat.cast_sum]
  calc
    _ ≤ ∑ _x : Fin m, (1 + 2*t/|b|) := sum_le_sum (fun x _ => hslice x)
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]


abbrev Grid (m : ℕ) := Fin m × Fin m

/-- Distance in the original integer coordinates, before scaling. -/
def gridDistance {m : ℕ} (a b : Grid m) : ℕ :=
  max (Nat.dist a.1.val b.1.val) (Nat.dist a.2.val b.2.val)

private theorem coordinate_band {m : ℕ} (a : Fin m) (j : ℕ) :
    ((univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val ≤ j).card ≤ 2*j+1 := by
  let B := (univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val ≤ j
  change B.card ≤ _
  rw [← card_image_of_injective B Fin.val_injective]
  have hsub : B.image Fin.val ⊆ Icc (a.val-j) (a.val+j) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    have hd := (mem_filter.mp hb).2
    unfold Nat.dist at hd
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  omega

private theorem coordinate_shell {m : ℕ} (a : Fin m) (j : ℕ) :
    ((univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val = j).card ≤ 2 := by
  let B := (univ : Finset (Fin m)).filter fun b => Nat.dist a.val b.val = j
  change B.card ≤ _
  rw [← card_image_of_injective B Fin.val_injective]
  have hsub : B.image Fin.val ⊆ {a.val-j,a.val+j} := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    have hd := (mem_filter.mp hb).2
    simp only [mem_insert, mem_singleton]
    unfold Nat.dist at hd
    omega
  exact (card_le_card hsub).trans (by
    exact (card_insert_le _ _).trans (by simp))

/-- At most twelve times the radius many grid points have a given positive distance. -/
theorem shell_bound {m : ℕ} (a : Grid m) (j : ℕ) (hj : 0 < j) :
    ((univ : Finset (Grid m)).filter fun b => gridDistance a b = j).card ≤ 12*j := by
  let U₁ := (univ : Finset (Fin m)).filter fun x => Nat.dist a.1.val x.val ≤ j
  let U₂ := (univ : Finset (Fin m)).filter fun y => Nat.dist a.2.val y.val ≤ j
  let D₁ := (univ : Finset (Fin m)).filter fun x => Nat.dist a.1.val x.val = j
  let D₂ := (univ : Finset (Fin m)).filter fun y => Nat.dist a.2.val y.val = j
  have hsub : ((univ : Finset (Grid m)).filter fun b => gridDistance a b = j) ⊆
      D₁ ×ˢ U₂ ∪ U₁ ×ˢ D₂ := by
    rintro ⟨x,y⟩ h
    have hd := (mem_filter.mp h).2
    change max (Nat.dist a.1.val x.val) (Nat.dist a.2.val y.val) = j at hd
    have hx : Nat.dist a.1.val x.val ≤ j := hd ▸ le_max_left _ _
    have hy : Nat.dist a.2.val y.val ≤ j := hd ▸ le_max_right _ _
    rcases le_total (Nat.dist a.1.val x.val) (Nat.dist a.2.val y.val) with hxy | hyx
    · rw [max_eq_right hxy] at hd
      exact mem_union_right _ (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,
        mem_filter.mpr ⟨mem_univ _,hd⟩⟩)
    · rw [max_eq_left hyx] at hd
      exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hd⟩,
        mem_filter.mpr ⟨mem_univ _,hy⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [card_product, card_product]
  have h1 := Nat.mul_le_mul (coordinate_shell a.1 j) (coordinate_band a.2 j)
  have h2 := Nat.mul_le_mul (coordinate_band a.1 j) (coordinate_shell a.2 j)
  change D₁.card*U₂.card ≤ _ at h1
  change U₁.card*D₂.card ≤ _ at h2
  omega

theorem gridDistance_pos {m : ℕ} {a b : Grid m} (h : a ≠ b) : 0 < gridDistance a b := by
  by_contra! h'
  have hx : Nat.dist a.1.val b.1.val = 0 := by
    change max (Nat.dist a.1.val b.1.val) (Nat.dist a.2.val b.2.val) ≤ 0 at h'
    exact Nat.le_zero.mp ((le_max_left _ _).trans h')
  have hy : Nat.dist a.2.val b.2.val = 0 := by
    exact Nat.le_zero.mp ((le_max_right _ _).trans h')
  apply h
  apply Prod.ext
  · apply Fin.ext
    unfold Nat.dist at hx
    omega
  · apply Fin.ext
    unfold Nat.dist at hy
    omega

theorem gridDistance_lt {m : ℕ} (a b : Grid m) : gridDistance a b < m := by
  unfold gridDistance Nat.dist
  have h1 := a.1.isLt
  have h2 := a.2.isLt
  have h3 := b.1.isLt
  have h4 := b.2.isLt
  omega


/-- Twice the signed area in the unscaled grid, up to orientation. -/
def determinant {m : ℕ} (a b c : Grid m) : ℝ :=
  ((b.1.val : ℝ) - a.1.val)*((c.2.val : ℝ) - a.2.val) -
    ((b.2.val : ℝ) - a.2.val)*((c.1.val : ℝ) - a.1.val)

private theorem abs_coordinate_dist (x y : ℕ) :
    |(x : ℝ) - y| = (Nat.dist x y : ℝ) := by
  rcases le_total x y with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)

theorem triangle_slice_bound {m : ℕ} {a b : Grid m} (hab : a ≠ b) (t : ℝ) (ht : 0 ≤ t) :
    (((univ : Finset (Grid m)).filter fun c => |determinant a b c| ≤ t).card : ℝ)
      ≤ (m : ℝ) * (1 + 2*t/(gridDistance a b : ℝ)) := by
  let x := (b.1.val : ℝ) - a.1.val
  let y := (b.2.val : ℝ) - a.2.val
  let z := y*a.1.val - x*a.2.val
  have hf (c : Grid m) : determinant a b c = (-y)*c.1.val + x*c.2.val + z := by
    unfold determinant
    dsimp [x,y,z]
    ring
  have hd : (gridDistance a b : ℝ) = max |x| |y| := by
    simp [gridDistance, x,y, Nat.cast_max, abs_coordinate_dist, Nat.dist_comm]
  have hpos : 0 < (gridDistance a b : ℝ) := by exact_mod_cast gridDistance_pos hab
  simp_rw [hf]
  rcases le_total |y| |x| with h | h
  · rw [hd, max_eq_left h]
    have hxb : x ≠ 0 := by
      rw [hd, max_eq_left h] at hpos
      exact (abs_pos.mp hpos)
    exact strip_bound (-y) x z t hxb ht
  · rw [hd, max_eq_right h]
    have hyb : -y ≠ 0 := by
      rw [hd, max_eq_right h] at hpos
      exact neg_ne_zero.mpr (abs_pos.mp hpos)
    let U := (univ : Finset (Grid m)).filter fun c => |(-y)*c.1.val+x*c.2.val+z| ≤ t
    let V := (univ : Finset (Grid m)).filter fun c => |x*c.1.val+(-y)*c.2.val+z| ≤ t
    have hUV : U.card = V.card := by
      apply card_equiv (Equiv.prodComm (Fin m) (Fin m))
      intro c
      simp [U,V,add_comm (x*(c.2.val : ℝ))]
    change (U.card : ℝ) ≤ _
    rw [hUV]
    simpa [V, abs_neg] using strip_bound (m := m) x (-y) z t hyb ht

private theorem group_radii {m : ℕ} (a : Grid m) (f : ℕ → ℝ) :
    (∑ b ∈ (univ.filter fun b : Grid m => b ≠ a), f (gridDistance a b)) =
      ∑ r ∈ Icc 1 m, ((univ.filter fun b : Grid m => gridDistance a b = r).card : ℝ)*f r := by
  let S := (univ : Finset (Grid m)).filter fun b => b ≠ a
  have hm : ∀ b ∈ S, gridDistance a b ∈ Icc 1 m := by
    intro b hb
    have hne : a ≠ b := fun h => (mem_filter.mp hb).2 h.symm
    exact mem_Icc.mpr ⟨gridDistance_pos hne, (gridDistance_lt a b).le⟩
  rw [← sum_fiberwise_of_maps_to hm]
  apply sum_congr rfl
  intro r hr
  have hrPos : 0 < r := (mem_Icc.mp hr).1
  have hFiber : (S.filter fun b => gridDistance a b = r) =
      (univ.filter fun b : Grid m => gridDistance a b = r) := by
    ext b
    by_cases hb : b = a
    · subst b
      have hz : gridDistance a a = 0 := by simp [gridDistance]
      simp [S,hz,show (0 : ℕ) ≠ r by omega]
    · simp [S,hb]
  rw [hFiber]
  rw [show (∑ b ∈ (univ.filter fun b : Grid m => gridDistance a b = r),
        f (gridDistance a b)) = ∑ _ ∈ (univ.filter fun b : Grid m => gridDistance a b = r), f r by
    apply sum_congr rfl
    intro b hb
    rw [(mem_filter.mp hb).2]]
  simp

theorem first_inverse_moment {m : ℕ} (a : Grid m) :
    (∑ b ∈ (univ.filter fun b : Grid m => b ≠ a), (1 : ℝ) / gridDistance a b) ≤ 12*(m : ℝ) := by
  rw [group_radii a (fun j => (1 : ℝ)/j)]
  calc
    _ ≤ ∑ r ∈ Icc 1 m, (12 : ℝ) := by
      apply sum_le_sum
      intro r hr
      have hrNat : 0 < r := (mem_Icc.mp hr).1
      have hrPos : 0 < (r : ℝ) := by exact_mod_cast hrNat
      have hcard : ((univ.filter fun b : Grid m => gridDistance a b = r).card : ℝ) ≤ 12*r := by
        exact_mod_cast shell_bound a r hrNat
      calc _ ≤ (12*(r : ℝ))*(1/r) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by field_simp
    _ = _ := by simp [Nat.card_Icc, mul_comm]

theorem second_inverse_moment {m : ℕ} (a : Grid m) :
    (∑ b ∈ (univ.filter fun b : Grid m => b ≠ a), ((1 : ℝ) / gridDistance a b)^2)
      ≤ 12*(1 + Real.log m) := by
  rw [group_radii a (fun j => ((1 : ℝ)/j)^2)]
  calc
    _ ≤ ∑ r ∈ Icc 1 m, (12 : ℝ) * (r : ℝ)⁻¹ := by
      apply sum_le_sum
      intro r hr
      have hrNat : 0 < r := (mem_Icc.mp hr).1
      have hrPos : 0 < (r : ℝ) := by exact_mod_cast hrNat
      have hcard : ((univ.filter fun b : Grid m => gridDistance a b = r).card : ℝ) ≤ 12*r := by
        exact_mod_cast shell_bound a r hrNat
      calc _ ≤ (12*(r : ℝ))*(1/r)^2 := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by field_simp
    _ = 12*(harmonic m : ℝ) := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      push_cast <;> rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log m) (by norm_num)


abbrev Triple (m : ℕ) := Grid m × Grid m × Grid m
abbrev Quadruple (m : ℕ) := Grid m × Grid m × Grid m × Grid m

noncomputable def triangleLabels {m : ℕ} (t : ℝ) : Finset (Triple m) :=
  univ.filter fun q => q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2 ∧
    |determinant q.1 q.2.1 q.2.2| ≤ t

noncomputable def conflictLabels {m : ℕ} (t : ℝ) : Finset (Quadruple m) :=
  univ.filter fun q => q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧
    q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2 ∧
      |determinant q.1 q.2.1 q.2.2.1| ≤ t ∧ |determinant q.1 q.2.1 q.2.2.2| ≤ t

private noncomputable def slice {m : ℕ} (a b : Grid m) (t : ℝ) : Finset (Grid m) :=
  univ.filter fun c => |determinant a b c| ≤ t

private theorem count_by_fibers {A B : Type*} [Fintype A] [Fintype B]
    (P : A × B → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ a : A, (@Finset.filter B (fun b => P (a,b))
      (fun b => inferInstance) univ).card := by
  rw [card_filter, Fintype.sum_prod_type]
  simp only [card_filter]

private theorem weaken_triangles {m : ℕ} (t : ℝ) :
    (triangleLabels (m:=m) t).card ≤
      ∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card := by
  let L : Finset (Triple m) := univ.filter fun q => q.2.1 ≠ q.1 ∧
    |determinant q.1 q.2.1 q.2.2| ≤ t
  have hsub : triangleLabels t ⊆ L := by
    intro q hq
    have h := (mem_filter.mp hq).2
    exact mem_filter.mpr ⟨mem_univ _, h.1.symm, h.2.2.2⟩
  refine (card_le_card hsub).trans_eq ?_
  dsimp only [L]
  rw [count_by_fibers]
  apply sum_congr rfl
  intro a ha
  rw [count_by_fibers, sum_filter]
  apply sum_congr rfl
  intro b hb
  by_cases h : b ≠ a <;> simp [h, slice]

private theorem weaken_conflicts {m : ℕ} (t : ℝ) :
    (conflictLabels (m:=m) t).card ≤
      ∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card^2 := by
  let L : Finset (Quadruple m) := univ.filter fun q => q.2.1 ≠ q.1 ∧
    |determinant q.1 q.2.1 q.2.2.1| ≤ t ∧ |determinant q.1 q.2.1 q.2.2.2| ≤ t
  have hsub : conflictLabels t ⊆ L := by
    intro q hq
    have h := (mem_filter.mp hq).2
    exact mem_filter.mpr ⟨mem_univ _, h.1.symm, h.2.2.2.2.2.2⟩
  refine (card_le_card hsub).trans_eq ?_
  dsimp only [L]
  rw [count_by_fibers]
  apply sum_congr rfl
  intro a ha
  rw [count_by_fibers, sum_filter]
  apply sum_congr rfl
  intro b hb
  by_cases h : b ≠ a
  · rw [if_pos h, pow_two, ← card_product]
    congr 1
    ext q
    simp [h, slice]
  · simp [h]

theorem triangles_total {m : ℕ} (t : ℝ) (ht : 0 ≤ t) :
    ((triangleLabels (m:=m) t).card : ℝ) ≤ (m : ℝ)^5 + 24*t*(m : ℝ)^4 := by
  have hcast := (show ((triangleLabels (m:=m) t).card : ℝ) ≤
      ((∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card : ℕ) : ℝ) by
    exact_mod_cast weaken_triangles t)
  simp only [Nat.cast_sum] at hcast
  refine hcast.trans ?_
  have fibers (a : Grid m) : (∑ b ∈ univ.filter (· ≠ a), ((slice a b t).card : ℝ)) ≤
      (m : ℝ)^3 + 24*t*(m : ℝ)^2 := by
    calc
      _ ≤ ∑ b ∈ univ.filter (· ≠ a), (m : ℝ)*(1+2*t/(gridDistance a b : ℝ)) := by
        apply sum_le_sum
        intro b hb
        have hn : a ≠ b := fun h => (mem_filter.mp hb).2 h.symm
        exact triangle_slice_bound hn t ht
      _ = (m : ℝ)*((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) +
          (2*t*(m : ℝ))*(∑ b ∈ univ.filter (· ≠ a), (1 : ℝ)/gridDistance a b) := by
        have hs : (∑ _b ∈ univ.filter (· ≠ a), (m : ℝ)) =
            (m : ℝ)*((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
        rw [Finset.mul_sum, ← hs, ← sum_add_distrib]
        apply sum_congr rfl
        intro b hb
        ring
      _ ≤ _ := by
        have hcardNat := card_filter_le (s := (univ : Finset (Grid m))) (· ≠ a)
        have hcard : ((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) ≤ (m : ℝ)^2 := by
          simp only [card_univ,Fintype.card_prod,Fintype.card_fin] at hcardNat
          exact_mod_cast (by simpa [pow_two] using hcardNat : _ ≤ m^2)
        have h1 := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m)
        have h2 := mul_le_mul_of_nonneg_left (first_inverse_moment a)
          (show 0 ≤ 2*t*(m : ℝ) by positivity)
        nlinarith only [h1,h2]
  calc
    _ ≤ ∑ _a : Grid m, ((m : ℝ)^3 + 24*t*(m : ℝ)^2) := sum_le_sum (fun a _ => fibers a)
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod,Fintype.card_fin]; push_cast; ring

theorem conflicts_total {m : ℕ} (t : ℝ) (ht : 0 ≤ t) :
    ((conflictLabels (m:=m) t).card : ℝ) ≤
      2*(m : ℝ)^6 + 96*t^2*(m : ℝ)^4*(1+Real.log m) := by
  have hcast := (show ((conflictLabels (m:=m) t).card : ℝ) ≤
      ((∑ a : Grid m, ∑ b ∈ univ.filter (· ≠ a), (slice a b t).card^2 : ℕ) : ℝ) by
    exact_mod_cast weaken_conflicts t)
  simp only [Nat.cast_sum,Nat.cast_pow] at hcast
  refine hcast.trans ?_
  have fibers (a : Grid m) : (∑ b ∈ univ.filter (· ≠ a), ((slice a b t).card : ℝ)^2) ≤
      2*(m : ℝ)^4 + 96*t^2*(m : ℝ)^2*(1+Real.log m) := by
    calc
      _ ≤ ∑ b ∈ univ.filter (· ≠ a), (2*(m : ℝ)^2 + 8*t^2*(m : ℝ)^2*((1 : ℝ)/gridDistance a b)^2) := by
        apply sum_le_sum
        intro b hb
        have hn : a ≠ b := fun h => (mem_filter.mp hb).2 h.symm
        have hu := triangle_slice_bound hn t ht
        have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ((slice a b t).card : ℝ)) hu 2
        apply hs.trans
        have he : 2*(m : ℝ)^2 + 8*t^2*(m : ℝ)^2*((1 : ℝ)/gridDistance a b)^2 -
            ((m : ℝ)*(1+2*t/(gridDistance a b : ℝ)))^2 =
            (m : ℝ)^2*(1-2*t/(gridDistance a b : ℝ))^2 := by ring
        rw [← sub_nonneg, he]
        positivity
      _ = 2*(m : ℝ)^2*((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) +
          (8*t^2*(m : ℝ)^2)*(∑ b ∈ univ.filter (· ≠ a), ((1 : ℝ)/gridDistance a b)^2) := by
        rw [Finset.mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm ((univ.filter (· ≠ a)).card : ℝ)]
      _ ≤ _ := by
        have hcardNat := card_filter_le (s := (univ : Finset (Grid m))) (· ≠ a)
        have hcard : ((univ.filter (fun b : Grid m => b ≠ a)).card : ℝ) ≤ (m : ℝ)^2 := by
          simp only [card_univ,Fintype.card_prod,Fintype.card_fin] at hcardNat
          exact_mod_cast (by simpa [pow_two] using hcardNat : _ ≤ m^2)
        have h1 := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 2*(m : ℝ)^2 by positivity)
        have h2 := mul_le_mul_of_nonneg_left (second_inverse_moment a)
          (show 0 ≤ 8*t^2*(m : ℝ)^2 by positivity)
        nlinarith only [h1,h2]
  calc
    _ ≤ ∑ _a : Grid m, (2*(m : ℝ)^4 + 96*t^2*(m : ℝ)^2*(1+Real.log m)) :=
      sum_le_sum (fun a _ => fibers a)
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod,Fintype.card_fin]; push_cast; ring


open scoped EuclideanGeometry
open Finset

def tripleVerts {m : ℕ} (q : Triple m) : Finset (Grid m) :=
  {q.1,q.2.1,q.2.2}

def conflictVerts {m : ℕ} (q : Quadruple m) : Finset (Grid m) :=
  {q.1,q.2.1,q.2.2.1,q.2.2.2}

theorem triple_card {m : ℕ} {q : Triple m} {t : ℝ} (h : q ∈ triangleLabels t) :
    (tripleVerts q).card = 3 := by
  have hq := (mem_filter.mp h).2
  simp [tripleVerts, hq.1, hq.2.1, hq.2.2.1, card_insert_of_notMem]

theorem conflict_card {m : ℕ} {q : Quadruple m} {t : ℝ} (h : q ∈ conflictLabels t) :
    (conflictVerts q).card = 4 := by
  have hq := (mem_filter.mp h).2
  simp [conflictVerts, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1,
    hq.2.2.2.2.2.1, card_insert_of_notMem]

private theorem determinant_same_vertices {m : ℕ} (a b c x y z : Grid m)
    (he : ({a,b,c} : Finset (Grid m)) = {x,y,z}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    |determinant a b c| = |determinant x y z| := by
  have hx : x = a ∨ x = b ∨ x = c := by
    have : x ∈ ({a,b,c} : Finset (Grid m)) := by rw [he]; simp
    simpa only [mem_insert, mem_singleton] using this
  have hy : y = a ∨ y = b ∨ y = c := by
    have : y ∈ ({a,b,c} : Finset (Grid m)) := by rw [he]; simp
    simpa only [mem_insert, mem_singleton] using this
  have hz : z = a ∨ z = b ∨ z = c := by
    have : z ∈ ({a,b,c} : Finset (Grid m)) := by rw [he]; simp
    simpa only [mem_insert, mem_singleton] using this
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
    rcases hz with hz | hz | hz <;> subst x <;> subst y <;> subst z <;> try contradiction
  · rfl
  · rw [show determinant a c b = -determinant a b c by unfold determinant; ring, abs_neg]
  · rw [show determinant b a c = -determinant a b c by unfold determinant; ring, abs_neg]
  · exact congrArg abs (by unfold determinant; ring)
  · exact congrArg abs (by unfold determinant; ring)
  · rw [show determinant c b a = -determinant a b c by unfold determinant; ring, abs_neg]

private theorem set_eq_triangle {m : ℕ} {e : Finset (Grid m)} (he : e.card = 3)
    {a b c : Grid m} (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : e = {a,b,c} := by
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simp [he, hab, hac, hbc, card_insert_of_notMem]

private noncomputable def point {m : ℕ} (q : Grid m) : ℝ² :=
  WithLp.toLp 2 ![(q.1.val : ℝ)/(2*m), (q.2.val : ℝ)/(2*m)]

private theorem point_injective {m : ℕ} (hm : 0 < m) : Function.Injective (point (m:=m)) := by
  intro a b h
  have hm' : (0 : ℝ) < 2*m := by exact_mod_cast (show 0 < 2*m by omega)
  apply Prod.ext <;> apply Fin.ext
  · have h₀ := congrArg (fun x : ℝ² => x 0) h
    change (a.1.val : ℝ)/(2*m) = (b.1.val : ℝ)/(2*m) at h₀
    exact_mod_cast (div_left_inj' hm'.ne').mp h₀
  · have h₁ := congrArg (fun x : ℝ² => x 1) h
    change (a.2.val : ℝ)/(2*m) = (b.2.val : ℝ)/(2*m) at h₁
    exact_mod_cast (div_left_inj' hm'.ne').mp h₁

private theorem point_in_disk {m : ℕ} (hm : 0 < m) (q : Grid m) :
    point q ∈ Metric.closedBall (0 : ℝ²) 1 := by
  have hm' : (0 : ℝ) < 2*m := by exact_mod_cast (show 0 < 2*m by omega)
  have hx : (q.1.val : ℝ)/(2*m) ≤ 1/2 := by
    apply (div_le_iff₀ hm').mpr
    have := (show (q.1.val : ℝ) ≤ m by exact_mod_cast q.1.isLt.le)
    linarith
  have hy : (q.2.val : ℝ)/(2*m) ≤ 1/2 := by
    apply (div_le_iff₀ hm').mpr
    have := (show (q.2.val : ℝ) ≤ m by exact_mod_cast q.2.isLt.le)
    linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change ((q.1.val : ℝ)/(2*m))^2 + ((q.2.val : ℝ)/(2*m))^2 ≤ 1^2
  have hx2 := pow_le_pow_left₀ (by positivity) hx 2
  have hy2 := pow_le_pow_left₀ (by positivity) hy 2
  norm_num at hx2 hy2 ⊢
  linarith

private theorem point_area {m : ℕ} (hm : 0 < m) (a b c : Grid m) :
    |EuclideanGeometry.triangle_area (point a) (point b) (point c)| =
      |determinant a b c| / (8 * (m : ℝ)^2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : EuclideanGeometry.triangle_area (point a) (point b) (point c) =
      determinant a b c / (8 * (m : ℝ)^2) := by
    rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
    simp [point, determinant]
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * m^2)]

theorem grid_to_disk {m : ℕ} (hm : 0 < m) (r : ℝ) (U : Finset (Grid m)) :
    let t := 8 * (m : ℝ)^2 * r
    let T := (triangleLabels t).filter (fun q => tripleVerts q ⊆ U)
    let X := (conflictLabels t).filter (fun q => conflictVerts q ⊆ U)
    ∃ (S : Finset ℝ²) (E : Finset (Finset ℝ²)),
      S.card = U.card ∧ E.card ≤ T.card ∧
      (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤ X.card ∧
      (S : Set ℝ²) ⊆ Metric.closedBall 0 1 ∧
      (∀ e ∈ E, e ⊆ S ∧ e.card = 3) ∧
      (∀ p : Fin 3 → ℝ², Function.Injective p → (∀ i, p i ∈ S) →
        |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| ≤ r →
        univ.image p ∈ E) := by
  classical
  dsimp only
  let t := 8 * (m : ℝ)^2 * r
  let T := (triangleLabels t).filter (fun q => tripleVerts q ⊆ U)
  let X := (conflictLabels t).filter (fun q => conflictVerts q ⊆ U)
  let p : Grid m ↪ ℝ² := ⟨point, point_injective hm⟩
  let F := T.image tripleVerts
  let f : Finset (Grid m) ↪ Finset ℝ² := ⟨Finset.map p, Finset.map_injective p⟩
  let S := U.map p
  let E := F.map f
  have hF (e : Finset (Grid m)) (he : e ∈ F) : e ⊆ U ∧ e.card = 3 := by
    obtain ⟨q,hq,rfl⟩ := mem_image.mp he
    exact ⟨(mem_filter.mp hq).2,triple_card (mem_filter.mp hq).1⟩
  have hTri (e : Finset (Grid m)) (he : e ∈ F) {a b c : Grid m}
      (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      |determinant a b c| ≤ t := by
    have hEq := set_eq_triangle (hF e he).2 ha hb hc hab hac hbc
    obtain ⟨q,hq,hEq'⟩ := mem_image.mp he
    rw [← determinant_same_vertices q.1 q.2.1 q.2.2 a b c (hEq'.trans hEq) hab hac hbc]
    exact (mem_filter.mp (mem_filter.mp hq).1).2.2.2.2
  refine ⟨S,E,card_map _,(card_map _).le.trans card_image_le,?_,?_,?_,?_⟩
  · let Y := (E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card
    change Y.card ≤ X.card
    let form (q : Quadruple m) : Finset ℝ² × Finset ℝ² :=
      (f (tripleVerts (q.1,q.2.1,q.2.2.1)), f (tripleVerts (q.1,q.2.1,q.2.2.2)))
    apply card_le_card_of_surjOn form
    rintro ⟨e₀,g₀⟩ hY
    have hpair := mem_filter.mp hY
    obtain ⟨he₀,hg₀⟩ := mem_product.mp hpair.1
    obtain ⟨e,he,rfl⟩ := mem_map.mp he₀
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hg₀
    have hne : e ≠ g := fun h => hpair.2.1 (congrArg f h)
    have hcard : 2 ≤ (e ∩ g).card := by
      have h := hpair.2.2
      change 2 ≤ (e.map p ∩ g.map p).card at h
      rw [← map_inter e g, card_map] at h
      exact h
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < (e ∩ g).card)
    have hae := (mem_inter.mp ha).1
    have hag := (mem_inter.mp ha).2
    have hbe := (mem_inter.mp hb).1
    have hbg := (mem_inter.mp hb).2
    have heCard := (hF e he).2
    have hgCard := (hF g hg).2
    have hesub : ¬ e ⊆ g := fun h => hne (eq_of_subset_of_card_le h (by omega))
    have hgsub : ¬ g ⊆ e := fun h => hne (eq_of_subset_of_card_le h (by omega)).symm
    obtain ⟨c,hce,hcg⟩ := not_subset.mp hesub
    obtain ⟨d,hdg,hde⟩ := not_subset.mp hgsub
    have hac : a ≠ c := fun h => hcg (h ▸ hag)
    have had : a ≠ d := fun h => hde (h ▸ hae)
    have hbc : b ≠ c := fun h => hcg (h ▸ hbg)
    have hbd : b ≠ d := fun h => hde (h ▸ hbe)
    have hcd : c ≠ d := fun h => hcg (h.symm ▸ hdg)
    have hq1 := hTri e he hae hbe hce hab hac hbc
    have hq2 := hTri g hg hag hbg hdg hab had hbd
    let q : Quadruple m := (a,b,c,d)
    have hX : q ∈ X := by
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hab,hac,had,hbc,hbd,hcd,hq1,hq2⟩,?_⟩
      intro x hx
      simp only [conflictVerts, q, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (hF e he).1 hae
      · exact (hF e he).1 hbe
      · exact (hF e he).1 hce
      · exact (hF g hg).1 hdg
    refine ⟨q,hX,?_⟩
    change (f ({a,b,c} : Finset (Grid m)), f ({a,b,d} : Finset (Grid m))) = (f e, f g)
    rw [← set_eq_triangle heCard hae hbe hce hab hac hbc, ← set_eq_triangle hgCard hag hbg hdg hab had hbd]
  · intro x hx
    obtain ⟨q,_,rfl⟩ := mem_map.mp hx
    exact point_in_disk hm q
  · intro e he
    obtain ⟨g,hg,rfl⟩ := mem_map.mp he
    exact ⟨map_subset_map.mpr (hF g hg).1, (card_map _).trans (hF g hg).2⟩
  · intro w hw hmem hArea
    have hpre (i : Fin 3) : ∃ q ∈ U, p q = w i := mem_map.mp (hmem i)
    choose q hqU hqEq using hpre
    have hqInj : Function.Injective q := fun i j h => hw (by rw [← hqEq i, ← hqEq j,h])
    have h01 : q 0 ≠ q 1 := hqInj.ne (by decide)
    have h02 : q 0 ≠ q 2 := hqInj.ne (by decide)
    have h12 : q 1 ≠ q 2 := hqInj.ne (by decide)
    let z : Triple m := (q 0,q 1,q 2)
    have hmt : 0 < (8 : ℝ) * m^2 := by
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    rw [← hqEq 0, ← hqEq 1, ← hqEq 2] at hArea
    change |EuclideanGeometry.triangle_area (point (q 0)) (point (q 1)) (point (q 2))| ≤ r at hArea
    rw [point_area hm] at hArea
    have hzt : |determinant (q 0) (q 1) (q 2)| ≤ t := by
      simpa only [t, mul_comm r] using (div_le_iff₀ hmt).mp hArea
    have hZ : z ∈ T := by
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h01,h02,h12,hzt⟩,?_⟩
      intro x hx
      simp only [tripleVerts, z, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> apply hqU
    refine mem_map.mpr ⟨tripleVerts z,mem_image.mpr ⟨z,hZ,rfl⟩,?_⟩
    change (tripleVerts z).map p = univ.image w
    ext x
    simp [tripleVerts, z, hqEq, Fin.exists_fin_succ, eq_comm]


end OMA.HeilbronnGrid


/- Bernoulli sampling of vertex sets with bounded induced configurations. -/

open Finset
open scoped BigOperators

namespace OMA.SampleFinset

private theorem weight_supersets {V : Type*} [DecidableEq V] {Q T : Finset V}
    (hT : T ⊆ Q) (p : ℝ) :
    (∑ S ∈ Q.powerset, if T ⊆ S then p ^ S.card * (1 - p) ^ (Q \ S).card else 0)
      = p ^ T.card := by
  let g := fun v => if v ∈ T then (0 : ℝ) else 1 - p
  have hprod := Finset.prod_add (fun _ : V => p) g Q
  have hleft : (∏ v ∈ Q, (p + g v)) = p ^ T.card := by
    rw [← prod_sdiff hT]
    have hs : (∏ v ∈ Q \ T, (p + g v)) = 1 := by
      apply prod_eq_one
      intro v hv
      simp [g, (mem_sdiff.1 hv).2]
    have ht : (∏ v ∈ T, (p + g v)) = p ^ T.card := by
      rw [← prod_const]
      exact prod_congr rfl fun v hv => by simp [g, hv]
    rw [hs, ht, one_mul]
  rw [hleft] at hprod
  rw [hprod]
  apply sum_congr rfl
  intro S hS
  by_cases hsub : T ⊆ S
  · rw [if_pos hsub, prod_const]
    congr 1
    rw [← prod_const]
    apply prod_congr rfl
    intro v hv
    have hnv : v ∉ T := fun hm => (mem_sdiff.1 hv).2 (hsub hm)
    simp [g, hnv]
  · rw [if_neg hsub]
    obtain ⟨v, hvT, hvS⟩ := not_subset.1 hsub
    have hv : v ∈ Q \ S := mem_sdiff.2 ⟨hT hvT, hvS⟩
    have hz : g v = 0 := if_pos hvT
    rw [Finset.prod_eq_zero hv hz, mul_zero]

private theorem expectation {V I : Type*} [DecidableEq V] (Q : Finset V) (A : Finset I)
    (t : I → Finset V) (d : ℕ)
    (h : ∀ i ∈ A, t i ⊆ Q ∧ (t i).card = d) (p : ℝ) :
    (∑ S ∈ Q.powerset, (p ^ S.card * (1 - p) ^ (Q \ S).card) *
      ((A.filter fun i => t i ⊆ S).card : ℝ)) = (A.card : ℝ) * p ^ d := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ _i ∈ A, p ^ d := by
      apply sum_congr rfl
      intro i hi
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [weight_supersets (h i hi).1, (h i hi).2]
    _ = _ := by rw [sum_const, nsmul_eq_mul]


/-- Choose a Bernoulli subset that is large and has few induced triples and
four-vertex conflicts. The labels of the triples and conflicts may repeat a vertex set. -/
theorem exists_sparse_sample {V E X : Type*} [DecidableEq V]
    (Q : Finset V) (edges : Finset E) (conflicts : Finset X)
    (edgeVerts : E → Finset V) (conflictVerts : X → Finset V)
    (hE : ∀ e ∈ edges, edgeVerts e ⊆ Q ∧ (edgeVerts e).card = 3)
    (hX : ∀ x ∈ conflicts, conflictVerts x ⊆ Q ∧ (conflictVerts x).card = 4)
    (p d : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hd : 0 < d)
    (avgE : 24 * (edges.card : ℝ) * p^3 ≤ d * ((Q.card : ℝ) * p))
    (avgX : 8 * (conflicts.card : ℝ) * p^4 ≤ (Q.card : ℝ) * p) :
    ∃ S ⊆ Q, (Q.card : ℝ) * p / 2 ≤ (S.card : ℝ) ∧
      6 * ((edges.filter fun e => edgeVerts e ⊆ S).card : ℝ) ≤ d * S.card ∧
      2 * (conflicts.filter fun x => conflictVerts x ⊆ S).card ≤ S.card := by
  let w (S : Finset V) : ℝ := p ^ S.card * (1-p) ^ (Q \ S).card
  let e (S : Finset V) : ℝ := (edges.filter fun v => edgeVerts v ⊆ S).card
  let x (S : Finset V) : ℝ := (conflicts.filter fun v => conflictVerts v ⊆ S).card
  let score (S : Finset V) : ℝ := S.card - (6/d)*e S - 2*x S
  have hw (S : Finset V) : 0 ≤ w S :=
    mul_nonneg (pow_nonneg hp₀ _) (pow_nonneg (sub_nonneg.mpr hp₁) _)
  have hMass : ∑ S ∈ Q.powerset, w S = 1 := by
    simpa only [empty_subset, if_true, card_empty, pow_zero] using
      weight_supersets (Q := Q) (T := ∅) (empty_subset Q) p
  have hEdge : (∑ S ∈ Q.powerset, w S * e S) = (edges.card : ℝ)*p^3 :=
    expectation Q edges edgeVerts 3 hE p
  have hConflict : (∑ S ∈ Q.powerset, w S * x S) = (conflicts.card : ℝ)*p^4 :=
    expectation Q conflicts conflictVerts 4 hX p
  have hVertices : (∑ S ∈ Q.powerset, w S * (S.card : ℝ)) = (Q.card : ℝ)*p := by
    have h := expectation Q Q (fun a : V => {a}) 1 (fun a ha => by simpa using ha) p
    rw [pow_one] at h
    rw [← h]
    apply sum_congr rfl
    intro S hS
    have hf : (Q.filter fun a => ({a} : Finset V) ⊆ S) = S := by
      ext a
      simp only [mem_filter, singleton_subset_iff]
      exact ⟨And.right, fun ha => ⟨mem_powerset.mp hS ha, ha⟩⟩
    rw [hf]
  have hScore : (∑ S ∈ Q.powerset, w S * score S) =
      (Q.card : ℝ) * p - (6/d)*((edges.card : ℝ)*p^3) - 2*((conflicts.card : ℝ)*p^4) := by
    rw [← hVertices, ← hEdge, ← hConflict, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro S hS
    dsimp only [score]
    ring
  have hpE : (6/d)*((edges.card : ℝ)*p^3) ≤ (Q.card : ℝ)*p/4 := by
    calc
      _ = (24*(edges.card : ℝ)*p^3) / (4*d) := by field_simp; ring
      _ ≤ (d*((Q.card : ℝ)*p))/(4*d) := div_le_div_of_nonneg_right avgE (by positivity)
      _ = _ := by field_simp
  have hExpected : (Q.card : ℝ)*p/2 ≤ ∑ S ∈ Q.powerset, w S * score S := by
    rw [hScore]
    linarith
  obtain ⟨S,hS,hBest⟩ := exists_max_image Q.powerset score
    ⟨∅, mem_powerset.mpr (empty_subset Q)⟩
  have hMax : (∑ T ∈ Q.powerset, w T * score T) ≤ score S := by
    calc
      _ ≤ ∑ T ∈ Q.powerset, w T * score S :=
        sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left (hBest T hT) (hw T))
      _ = _ := by rw [← sum_mul, hMass, one_mul]
  have hChoice := hExpected.trans hMax
  have hNonneg : 0 ≤ (Q.card : ℝ)*p/2 := by positivity
  have hEdge₀ : 0 ≤ (6/d)*e S := by dsimp [e]; positivity
  have hConflict₀ : 0 ≤ 2*x S := by dsimp [x]; positivity
  change (Q.card : ℝ)*p/2 ≤ S.card - (6/d)*e S - 2*x S at hChoice
  refine ⟨S,mem_powerset.mp hS,by linarith,?_ ,?_⟩
  · change 6*e S ≤ d*S.card
    rw [mul_comm d]
    apply (div_le_iff₀ hd).mp
    rw [mul_div_right_comm]
    linarith
  · have hc : 2*x S ≤ S.card := by linarith
    dsimp only [x] at hc
    exact_mod_cast hc

end OMA.SampleFinset


namespace OMA.HeilbronnParameters

open Filter Asymptotics

/-- Parameters for the Bernoulli sample. Its expected size is x^(9/8),
and the area threshold is r per triangle. -/
theorem eventual_parameters (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      let N := x ^ (9/8 : ℝ)
      let r := ε * (Real.log x / x^2)
      let d := 5000*r*N^2
      1 < x ∧ 1 ≤ Real.log x ∧ 1/x^4 ≤ r ∧
        0 < N ∧ N ≤ x^8 ∧
        2 ≤ d ∧ Real.log x / 4 ≤ Real.log d ∧ 320000*r^2*Real.log x*N^3 ≤ 1 := by
  let K := (320000 : ℝ) * ε^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (s:=5/8) (3:ℝ)
    (by norm_num)).bound (inv_pos.mpr hK)
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 ε⁻¹), hlog] with x hx hlogB hlogRate
  dsimp only
  let N := x ^ (9/8 : ℝ)
  let r := ε * (Real.log x / x^2)
  let d := 5000*r*N^2
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl1 : 1 ≤ Real.log x := (le_max_left _ _).trans hlogB
  have hl0 : 0 < Real.log x := by linarith
  have hεlog : 1 ≤ ε * Real.log x := by
    have h := mul_le_mul_of_nonneg_left ((le_max_right 1 ε⁻¹).trans hlogB) hε.le
    rwa [mul_inv_cancel₀ hε.ne'] at h
  have hN0 : 0 < N := Real.rpow_pos_of_pos hx0 _
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hN2 : N^2 = x ^ (9/4 : ℝ) := by
    dsimp only [N]
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num
  have hN3 : N^3 = x ^ (27/8 : ℝ) := by
    dsimp only [N]
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num
  have hApow : (x ^ (5/8 : ℝ)) * x ^ (27/8 : ℝ) = x^4 := by
    rw [← Real.rpow_add hx0]
    norm_num [Real.rpow_natCast]
  have hDpower : x ^ (9/4 : ℝ) = x^2 * x ^ (1/4 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hx0]
    norm_num
  have hD : d = 5000*ε*Real.log x * x ^ (1/4 : ℝ) := by
    dsimp only [d,r]
    rw [hN2,hDpower]
    field_simp
  have hp1 : 1 ≤ x ^ (1/4 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
  have hDlower : 2 ≤ d := by
    rw [hD]
    have h := mul_le_mul hεlog hp1 (by positivity) (by positivity : 0 ≤ ε * Real.log x)
    nlinarith only [h]
  have hloglower : Real.log x / 4 ≤ Real.log d := by
    have hbase : x ^ (1/4 : ℝ) ≤ d := by
      rw [hD]
      have h := mul_le_mul_of_nonneg_right hεlog
        (Real.rpow_nonneg hx0.le (1/4 : ℝ))
      nlinarith only [h,hp1]
    have hmono := Real.log_le_log (Real.rpow_pos_of_pos hx0 (1/4:ℝ)) hbase
    rw [Real.log_rpow hx0] at hmono
    linarith
  have hround : 1 / x^4 ≤ r := by
    have h : 1 / x^2 ≤ r := by
      dsimp only [r]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hεlog (by positivity)
    apply (one_div_le_one_div_of_le (by positivity) _).trans h
    have hs := one_le_pow₀ (a:=x) hx.le (n:=2)
    nlinarith [sq_nonneg (x^2-1)]
  have hNle : N ≤ x^8 := by
    dsimp only [N]
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hlogBound : (Real.log x)^3 ≤ K⁻¹ * x ^ (5/8 : ℝ) := by
    have hh := hlogRate
    change ‖(Real.log x)^(3:ℝ)‖ ≤ K⁻¹ * ‖x ^ (5/8:ℝ)‖ at hh
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hh
    exact (Real.rpow_natCast (Real.log x) 3 ▸ hh)
  have hlogPower : (Real.log x)^3 * x^(27/8 : ℝ) ≤ K⁻¹ * x^4 := by
    calc
      _ ≤ (K⁻¹ * x ^ (5/8 : ℝ)) * x^(27/8 : ℝ) :=
        mul_le_mul_of_nonneg_right hlogBound (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [mul_assoc,hApow]
  have hlogPower' : K * ((Real.log x)^3 * x^(27/8 : ℝ)) ≤ x^4 := by
    calc _ ≤ K * (K⁻¹ * x^4) := mul_le_mul_of_nonneg_left hlogPower hK.le
      _ = _ := by rw [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]
  have hConf : 320000*r^2*Real.log x*N^3 ≤ 1 := by
    rw [hN3]
    calc
      _ = (K * ((Real.log x)^3 * x^(27/8 : ℝ))) / x^4 := by
        dsimp only [r,K]
        field_simp
      _ ≤ _ := (div_le_one (by positivity)).mpr hlogPower'
  exact ⟨hx,hl1,hround,hN0,hNle,hDlower,hloglower,hConf⟩

end OMA.HeilbronnParameters


namespace OMA.HeilbronnSampleApplication

open OMA.HeilbronnGrid OMA.HeilbronnParameters
open Finset Filter Erdos507
open scoped BigOperators EuclideanGeometry

private theorem normalized_triangle_bound {m : ℕ} (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r)
    (hRound : 1/(m : ℝ) ≤ r) :
    ((triangleLabels (m:=m) (8*(m : ℝ)^2*r)).card : ℝ) ≤ (m : ℝ)^6*(193*r) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    _ ≤ (m : ℝ)^5 + 24*(8*(m : ℝ)^2*r)*(m : ℝ)^4 :=
      triangles_total _ (by positivity)
    _ = (m : ℝ)^6*(1/(m : ℝ)+192*r) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem normalized_conflict_bound {m : ℕ} (hm : 0 < m) (r L : ℝ) (hr : 0 ≤ r)
    (hRound : 1/(m : ℝ) ≤ r) (hL : 1 ≤ L) (hLog : Real.log (m : ℝ) = 4*L) :
    ((conflictLabels (m:=m) (8*(m : ℝ)^2*r)).card : ℝ) ≤ (m : ℝ)^8*(40000*r^2*L) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1/(m : ℝ)) hRound 2
  calc
    _ ≤ 2*(m : ℝ)^6 + 96*(8*(m : ℝ)^2*r)^2*(m : ℝ)^4*(1+Real.log m) :=
      conflicts_total _ (by positivity)
    _ = (m : ℝ)^8*(2*(1/(m : ℝ))^2 + 6144*r^2*(1+4*L)) := by
      rw [hLog]
      field_simp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 2 by norm_num)
      have h2 := mul_le_mul_of_nonneg_right (show 2 + 6144 * (1+4*L) ≤ 40000*L by linarith)
        (sq_nonneg r)
      nlinarith only [h1,h2]

theorem successful_sampling : OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1.H1 := by
  classical
  refine ⟨80000, by norm_num, ?_⟩
  intro ε hε
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (eventual_parameters ε hε)] with n hParams
  let m := n^4
  let N := (n : ℝ) ^ (9/8 : ℝ)
  let r := ε * lowerBest n
  let d := 5000*r*N^2
  have hP : (1 : ℝ) < n ∧ 1 ≤ Real.log n ∧ 1/(n : ℝ)^4 ≤ r ∧
      0 < N ∧ N ≤ (n : ℝ)^8 ∧
      2 ≤ d ∧ Real.log n/4 ≤ Real.log d ∧ 320000*r^2*Real.log n*N^3 ≤ 1 := hParams
  rcases hP with ⟨hn,hL,hRound,hN,hNle,hd,hLogD,hTiny⟩
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn
  have hm : 0 < m := by
    have hn' : 0 < n := by exact_mod_cast hn0
    exact pow_pos hn' _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : 0 < r := by dsimp [r,lowerBest]; positivity
  have hd0 : 0 < d := by linarith
  have hL0 : 0 < Real.log (n : ℝ) := by linarith
  have hRound' : 1/(m : ℝ) ≤ r := by simpa only [m,Nat.cast_pow] using hRound
  have hLogM : Real.log (m : ℝ) = 4 * Real.log n := by
    rw [show (m : ℝ) = (n : ℝ)^4 by simp [m], Real.log_pow]
    norm_num
  let p := N/(m : ℝ)^2
  have hp0 : 0 < p := div_pos hN (by positivity)
  have hp1 : p ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    simpa only [m,Nat.cast_pow,← pow_mul, show 4*2=8 by decide] using hNle
  let Q : Finset (Grid m) := univ
  let t := 8*(m : ℝ)^2*r
  let T := triangleLabels (m:=m) t
  let X := conflictLabels (m:=m) t
  have hT : (T.card : ℝ) ≤ (m : ℝ)^6*(193*r) :=
    normalized_triangle_bound hm r hr.le hRound'
  have hX : (X.card : ℝ) ≤ (m : ℝ)^8*(40000*r^2*Real.log n) :=
    normalized_conflict_bound hm r _ hr.le hRound' hL hLogM
  have hMp : (m : ℝ)^2*p = N := by dsimp [p]; field_simp
  have hQ : (Q.card : ℝ)*p = N := by
    rw [show (Q.card : ℝ) = (m : ℝ)^2 by simp [Q,Grid,pow_two]]
    exact hMp
  have hCube : (m : ℝ)^6 * p^3 = N^3 := by
    rw [← hMp]
    ring
  have hFourth : (m : ℝ)^8 * p^4 = N^4 := by
    rw [← hMp]
    ring
  have hMeanT : 24*(T.card : ℝ)*p^3 ≤ d*((Q.card : ℝ)*p) := by
    calc
      _ ≤ 24*((m : ℝ)^6*(193*r))*p^3 := by gcongr
      _ = (24*193)*r*N^3 := by
        rw [show (24:ℝ)*((m : ℝ)^6*(193*r))*p^3 = (24*193)*r*((m : ℝ)^6*p^3) by ring, hCube]
      _ ≤ d*((Q.card : ℝ)*p) := by
        rw [hQ]
        dsimp only [d]
        nlinarith only [mul_nonneg hr.le (pow_nonneg hN.le 3)]
  have hMeanX : 8*(X.card : ℝ)*p^4 ≤ (Q.card : ℝ)*p := by
    calc
      _ ≤ 8*((m : ℝ)^8*(40000*r^2*Real.log n))*p^4 := by gcongr
      _ = (320000*r^2*Real.log n*N^3)*N := by
        rw [show (8:ℝ)*((m : ℝ)^8*(40000*r^2*Real.log n))*p^4 =
              (320000*r^2*Real.log n)*((m : ℝ)^8*p^4) by ring, hFourth]
        ring
      _ ≤ _ := by simpa only [hQ,one_mul] using mul_le_mul_of_nonneg_right hTiny hN.le
  have hTL (q : Triple m) (hq : q ∈ T) : tripleVerts q ⊆ Q ∧ (tripleVerts q).card = 3 :=
    ⟨subset_univ _,triple_card hq⟩
  have hXL (q : Quadruple m) (hq : q ∈ X) : conflictVerts q ⊆ Q ∧ (conflictVerts q).card = 4 :=
    ⟨subset_univ _,conflict_card hq⟩
  obtain ⟨U,-,hUSize,hUCount,hUConf⟩ :=
    OMA.SampleFinset.exists_sparse_sample Q T X tripleVerts conflictVerts hTL hXL
      p d hp0.le hp1 hd0 hMeanT hMeanX
  rw [hQ] at hUSize
  obtain ⟨S,E,hSCard,hEBound,hXBound,hDisk,hEdges,hCover⟩ := grid_to_disk hm r U
  refine ⟨S,E,d,hDisk,hEdges,hCover,?_,hd,?_,?_⟩
  · change (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤
      (X.filter fun q => conflictVerts q ⊆ U).card at hXBound
    omega
  · have hEcast : (E.card : ℝ) ≤ ((T.filter fun q => tripleVerts q ⊆ U).card : ℝ) := by
      exact Nat.cast_le.mpr hEBound
    rw [← hSCard] at hUCount
    linarith
  · have hSSize : N ≤ 2*(S.card : ℝ) := by rw [hSCard]; linarith
    have hdiv := div_le_div_of_nonneg_right hSSize hn0.le
    calc
      d / Real.log d ≤ d / (Real.log n / 4) :=
        div_le_div_of_nonneg_left hd0.le (by positivity) hLogD
      _ = 20000*ε*(N/(n : ℝ))^2 := by
        dsimp only [d,r,lowerBest]
        field_simp
        ring
      _ ≤ 20000*ε*((2*(S.card : ℝ))/(n : ℝ))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdiv 2) (by positivity)
      _ = _ := by ring

end OMA.HeilbronnSampleApplication


theorem OMA.solution : OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1.H1 :=
  OMA.HeilbronnSampleApplication.successful_sampling
