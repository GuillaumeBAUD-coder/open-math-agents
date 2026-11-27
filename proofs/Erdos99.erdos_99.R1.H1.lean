import OMAReductions.R_Erdos99_erdos_99_R1
import Mathlib

-- Step Erdos99.erdos_99.R1.H1: hypothesis H1 of reduction Erdos99.erdos_99.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! A square grid. With `s = ⌊√n⌋`, the `(s + 1)^2 > n` integer points `(i, j)`, `i, j ≤ s`,
contain `n` points including `(0, 0)` and `(1, 0)`. Distinct integer points are at distance at
least `1`, and any two grid points are at distance at most `√(2 s^2) ≤ √(4 n) = 2 √n`. -/

open Set Metric EuclideanGeometry Filter
open scoped InnerProductSpace Topology

namespace P4E99

noncomputable def pt (i j : ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[(i : ℝ), (j : ℝ)]

theorem dist_pt (i j i' j' : ℕ) :
    dist (pt i j) (pt i' j') = Real.sqrt (((i : ℝ) - i') ^ 2 + ((j : ℝ) - j') ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [pt, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem pt_inj {i j i' j' : ℕ} (h : pt i j = pt i' j') : i = i' ∧ j = j' := by
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h
  simp [pt] at h0 h1
  exact ⟨h0, h1⟩

theorem one_le_sq_sub {i i' : ℕ} (h : i ≠ i') : 1 ≤ ((i : ℝ) - i') ^ 2 := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast h
    nlinarith
  · have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast h
    nlinarith

theorem sq_sub_le {i i' s : ℕ} (hi : i ≤ s) (hi' : i' ≤ s) : ((i : ℝ) - i') ^ 2 ≤ (s : ℝ) ^ 2 := by
  have h1 : (i : ℝ) ≤ s := by exact_mod_cast hi
  have h2 : (i' : ℝ) ≤ s := by exact_mod_cast hi'
  have h3 : (0 : ℝ) ≤ i := by positivity
  have h4 : (0 : ℝ) ≤ i' := by positivity
  nlinarith

end P4E99

open P4E99 in
theorem OMA.solution : OMA.R_Erdos99_erdos_99_R1.H1 := by
  intro n hn
  classical
  set s := Nat.sqrt n with hs
  have hs1 : 1 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hss : s * s ≤ n := Nat.sqrt_le n
  have hlt : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  let G : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.range (s + 1) ×ˢ Finset.range (s + 1)).image (fun ij => pt ij.1 ij.2)
  have hG : ∀ p ∈ G, ∃ i j, i ≤ s ∧ j ≤ s ∧ p = pt i j := by
    intro p hp
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    exact ⟨i, j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi),
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), rfl⟩
  have hGcard : G.card = (s + 1) * (s + 1) := by
    rw [Finset.card_image_of_injective _ (fun a b h => Prod.ext (pt_inj h).1 (pt_inj h).2),
      Finset.card_product, Finset.card_range]
  have hmem : ∀ i j, i ≤ s → j ≤ s → pt i j ∈ G := by
    intro i j hi hj
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, rfl⟩
  have hne01 : pt 0 0 ≠ pt 1 0 := fun h => by have := (pt_inj h).1; omega
  have hsub : ({pt 0 0, pt 1 0} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆ G := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hmem 0 0 (by omega) (by omega)
    · rw [Finset.mem_singleton.mp hp]; exact hmem 1 0 hs1 (by omega)
  obtain ⟨B, hB1, hB2, hBc⟩ := Finset.exists_subsuperset_card_eq (n := n) hsub
    (by rw [Finset.card_pair hne01]; exact hn) (by rw [hGcard]; omega)
  refine ⟨B, hBc, ?_, ⟨pt 0 0, hB1 (by simp), pt 1 0, hB1 (by simp), ?_⟩, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨i, j, -, -, rfl⟩ := hG p (hB2 hp)
    obtain ⟨i', j', -, -, rfl⟩ := hG q (hB2 hq)
    rw [dist_pt, Real.le_sqrt (by norm_num) (by positivity), one_pow]
    by_cases hii : i = i'
    · have hjj : j ≠ j' := fun h => hpq (by rw [hii, h])
      have := one_le_sq_sub hjj
      nlinarith [sq_nonneg ((i : ℝ) - i')]
    · have := one_le_sq_sub hii
      nlinarith [sq_nonneg ((j : ℝ) - j')]
  · rw [dist_pt]; norm_num
  · apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro p hp q hq
    obtain ⟨i, j, hi, hj, rfl⟩ := hG p (hB2 hp)
    obtain ⟨i', j', hi', hj', rfl⟩ := hG q (hB2 hq)
    rw [dist_pt]
    have h1 := sq_sub_le hi hi'
    have h2 := sq_sub_le hj hj'
    have h3 : ((s : ℝ)) ^ 2 ≤ n := by
      have : ((s * s : ℕ) : ℝ) ≤ n := by exact_mod_cast hss
      push_cast at this; nlinarith
    have e : (2 : ℝ) * Real.sqrt n = Real.sqrt (4 * n) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [e]
    exact Real.sqrt_le_sqrt (by linarith)
