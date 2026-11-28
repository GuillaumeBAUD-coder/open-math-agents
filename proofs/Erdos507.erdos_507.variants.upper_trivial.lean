import FormalConjectures.ErdosProblems.«507»

/-! An adaptation of the existing strip proof. Use at most (n - 1) / 2
strips, counting the right endpoint as its own bin, and bound the two
products in the area determinant by the same estimate. -/

open Asymptotics Filter
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos507.erdos_507.variants.upper_trivial := by
  classical
  apply Asymptotics.IsBigO.of_bound 16
  filter_upwards [eventually_ge_atTop (7 : ℕ)] with n hn
  have hnonneg : 0 ≤ Erdos507.α n :=
    Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ Real.sInf_nonneg fun _ ⟨_, _, _, h'⟩ => h' ▸ abs_nonneg _
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (by positivity)]
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨S, ⟨hS, hball, _⟩, rfl⟩
  have hcoord {x : ℝ²} (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) : |x i| ≤ 1 :=
    (Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
  let k := (n - 3) / 2
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let sc (p : ℝ²) : ℝ := (p 0 + 1) * k / 2
  have hsc {p} (hp : p ∈ S) : 0 ≤ sc p ∧ sc p ≤ k := by
    have := abs_le.mp (hcoord (hball hp) 0)
    dsimp [sc]; constructor <;> nlinarith
  have hmaps (p) (hp : p ∈ S) : ⌊sc p⌋₊ ∈ Finset.range (k + 1) :=
    Finset.mem_range.2 ((Nat.floor_lt (hsc hp).1).2 (by push_cast; linarith [(hsc hp).2]))
  obtain ⟨j, _, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := 2) hmaps
    (by rw [Finset.card_range, hS]; omega)
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := S.filter (⌊sc ·⌋₊ = j)) (by simpa using Nat.succ_le_of_lt hj)
  have hpF (i : Fin 3) := Finset.mem_filter.mp (hp (Set.mem_range_self i))
  have hst (i : Fin 3) := (Nat.floor_eq_iff (hsc (hpF i).1).1).mp (hpF i).2
  have hx (i : Fin 3) : |p i 0 - p 2 0| ≤ 2 / k := by
    have h1 := hst i; have h2 := hst 2; dsimp [sc] at h1 h2
    rw [abs_le, ← neg_div, div_le_iff₀ hk, le_div_iff₀ hk]; constructor <;> nlinarith
  have hy (i : Fin 3) : |p i 1 - p 2 1| ≤ 2 := by
    exact (abs_sub _ _).trans (by
      linarith [hcoord (hball (hpF i).1) 1, hcoord (hball (hpF 2).1) 1])
  have hmin : Erdos507.minTriangleArea S ≤ |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| :=
    csInf_le ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact abs_nonneg _⟩ ⟨p, p.injective, fun i => (hpF i).1, rfl⟩
  have hdet : EuclideanGeometry.triangle_area (p 0) (p 1) (p 2) =
      ((p 0 0 - p 2 0) * (p 1 1 - p 2 1) - (p 1 0 - p 2 0) * (p 0 1 - p 2 1)) / 2 := by
    rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]; simp; ring
  have harea : |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| ≤ 4 / k := by
    rw [hdet, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    have bound (i j : Fin 3) : |(p i 0 - p 2 0) * (p j 1 - p 2 1)| ≤ (2 / k) * 2 := by
      rw [abs_mul]
      exact mul_le_mul (hx i) (hy j) (abs_nonneg _) (by positivity)
    calc
      _ ≤ _ := (abs_sub _ _).trans (add_le_add (bound 0 1) (bound 1 0))
      _ = _ := by ring
  refine hmin.trans (harea.trans ?_)
  rw [mul_one_div, div_le_div_iff₀ hk (by exact_mod_cast (show 0 < n by omega))]
  exact_mod_cast (show 4 * n ≤ 16 * k by omega)
