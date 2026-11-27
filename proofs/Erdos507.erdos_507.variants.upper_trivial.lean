import FormalConjectures.ErdosProblems.«507»

/-! Vertical strips of width proportional to 1/n give the trivial Heilbronn upper bound. -/

open Asymptotics Filter
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos507.erdos_507.variants.upper_trivial := by
  classical
  apply Asymptotics.IsBigO.of_bound 36
  filter_upwards [eventually_ge_atTop (6 : ℕ)] with n hn
  have hnonneg : 0 ≤ Erdos507.α n :=
    Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ Real.sInf_nonneg fun _ ⟨_, _, _, h'⟩ => h' ▸ abs_nonneg _
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (by positivity)]
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨S, ⟨hS, hball, _⟩, rfl⟩
  have hcoord {x : ℝ²} (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) : |x i| ≤ 1 :=
    (Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
  let k : ℕ := n / 3
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let sc (p : ℝ²) : ℝ := (p 0 + 1) * k / 3
  have hsc {p} (hp : p ∈ S) : 0 ≤ sc p ∧ sc p < k := by
    have := abs_le.mp (hcoord (hball hp) 0)
    dsimp [sc]; constructor <;> nlinarith
  have hmaps : ∀ p ∈ S, ⌊sc p⌋₊ ∈ Finset.range k := fun p hp =>
    Finset.mem_range.2 ((Nat.floor_lt (hsc hp).1).2 (hsc hp).2)
  obtain ⟨j, _, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := 2) hmaps
    (by rw [Finset.card_range, hS]; omega)
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := S.filter (⌊sc ·⌋₊ = j)) (by simpa using Nat.succ_le_of_lt hj)
  have hpF (i : Fin 3) := Finset.mem_filter.mp (hp (Set.mem_range_self i))
  have hst (i : Fin 3) := (Nat.floor_eq_iff (hsc (hpF i).1).1).mp (hpF i).2
  have hx (i : Fin 3) : |p i 0 - p 2 0| ≤ 3 / k := by
    have h1 := hst i; have h2 := hst 2; dsimp [sc] at h1 h2
    rw [abs_le, ← neg_div, div_le_iff₀ hk, le_div_iff₀ hk]; constructor <;> nlinarith
  have hy (i : Fin 3) : |p i 1 - p 2 1| ≤ 2 := by
    have h1 := abs_le.mp (hcoord (hball (hpF i).1) 1)
    have h2 := abs_le.mp (hcoord (hball (hpF 2).1) 1)
    rw [abs_le]; constructor <;> linarith
  have hmin : Erdos507.minTriangleArea S ≤ |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| :=
    csInf_le ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact abs_nonneg _⟩ ⟨p, p.injective, fun i => (hpF i).1, rfl⟩
  have hdet : EuclideanGeometry.triangle_area (p 0) (p 1) (p 2) =
      ((p 0 0 - p 2 0) * (p 1 1 - p 2 1) - (p 1 0 - p 2 0) * (p 0 1 - p 2 1)) / 2 := by
    rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]; simp; ring
  have harea : |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| ≤ 6 / k := by
    rw [hdet, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 : |(p 0 0 - p 2 0) * (p 1 1 - p 2 1)| ≤ 3 / k * 2 := by
      rw [abs_mul]; exact mul_le_mul (hx 0) (hy 1) (abs_nonneg _) (by positivity)
    have h2 : |(p 1 0 - p 2 0) * (p 0 1 - p 2 1)| ≤ 3 / k * 2 := by
      rw [abs_mul]; exact mul_le_mul (hx 1) (hy 0) (abs_nonneg _) (by positivity)
    have h3 := abs_sub ((p 0 0 - p 2 0) * (p 1 1 - p 2 1)) ((p 1 0 - p 2 0) * (p 0 1 - p 2 1))
    have : (3 : ℝ) / k * 2 = 6 / k := by ring
    linarith
  have hkn : (6 : ℝ) / k ≤ 36 * (1 / n) := by
    have : (n : ℝ) ≤ 6 * k := by exact_mod_cast (show n ≤ 6 * k by omega)
    rw [mul_one_div, div_le_div_iff₀ hk hnR]; linarith
  linarith
