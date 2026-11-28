import OMAStatements.S_mo_487180
import Mathlib

/-!
A disproof of the claim of MathOverflow question 487180 (see statements/mo-487180.lean).

Consider the four functions
  f1 y = 2 * floor (3 y) + 2 * floor y
  f2 y = floor (3 y) + floor (2 y) + 3 * floor y
  f3 y = 4 * floor (2 y)
  f4 y = 3 * floor (2 y) + 2 * floor y,
which are the floor sums with coefficient lists [3,3,1,1], [3,2,1,1,1], [2,2,2,2], [2,2,2,1,1].
All four increase by 8 when y increases by 1, so it suffices to look at y modulo 1.  Writing
y = n + t with n = floor y and t in [0,1), the four values are 8 n plus

  t < 1/3:         0, 0, 0, 0
  1/3 <= t < 1/2:  2, 1, 0, 0
  1/2 <= t < 2/3:  2, 2, 4, 3
  2/3 <= t < 1:    4, 3, 4, 3,

so at every positive `y` the minimum of the four values is attained at least twice and no one of
the four is ever strictly below all the others.
-/

open OMA.S_mo_487180

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_487180.main) := by
  classical
  intro hmain
  let f1 : ℝ → ℤ := floorSum [3, 3, 1, 1]
  let f2 : ℝ → ℤ := floorSum [3, 2, 1, 1, 1]
  let f3 : ℝ → ℤ := floorSum [2, 2, 2, 2]
  let f4 : ℝ → ℤ := floorSum [2, 2, 2, 1, 1]
  let S : Finset (ℝ → ℤ) := {f1, f2, f3, f4}
  have hS : S.Nonempty := ⟨f1, by simp [S]⟩
  have hfs : ∀ f ∈ S, isFloorSum f := by
    intro f hf
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact ⟨[3, 3, 1, 1], by decide, rfl⟩
    · exact ⟨[3, 2, 1, 1, 1], by decide, rfl⟩
    · exact ⟨[2, 2, 2, 2], by decide, rfl⟩
    · exact ⟨[2, 2, 2, 1, 1], by decide, rfl⟩
  obtain ⟨x, hx, f, hf, hlt⟩ := hmain S hS hfs
  have hv1 : ∀ y : ℝ, f1 y = 2 * ⌊3 * y⌋ + 2 * ⌊y⌋ := by
    intro y
    simp only [f1, floorSum]
    norm_num
    ring
  have hv2 : ∀ y : ℝ, f2 y = ⌊3 * y⌋ + ⌊2 * y⌋ + 3 * ⌊y⌋ := by
    intro y
    simp only [f2, floorSum]
    norm_num
    ring
  have hv3 : ∀ y : ℝ, f3 y = 4 * ⌊2 * y⌋ := by
    intro y
    simp only [f3, floorSum]
    norm_num
    ring
  have hv4 : ∀ y : ℝ, f4 y = 3 * ⌊2 * y⌋ + 2 * ⌊y⌋ := by
    intro y
    simp only [f4, floorSum]
    norm_num
    ring
  have h12 : f1 ≠ f2 := by
    intro heq
    have h := congrFun heq (2 / 5)
    rw [hv1, hv2] at h
    norm_num at h
  have h34 : f3 ≠ f4 := by
    intro heq
    have h := congrFun heq (1 / 2)
    rw [hv3, hv4] at h
    norm_num at h
  have h24 : f2 ≠ f4 := by
    intro heq
    have h := congrFun heq (2 / 5)
    rw [hv2, hv4] at h
    norm_num at h
  set n : ℤ := ⌊x⌋ with hn
  set t : ℝ := x - (n : ℝ) with ht
  have hxt : x = t + (n : ℝ) := by rw [ht]; ring
  have ht0 : 0 ≤ t := by rw [ht]; linarith [Int.floor_le x]
  have ht1 : t < 1 := by rw [ht]; linarith [Int.lt_floor_add_one x]
  have hfloor : ∀ (a : ℝ) (k : ℤ), (k : ℝ) ≤ a → a < (k : ℝ) + 1 → ⌊a⌋ = k :=
    fun a k h1 h2 => Int.floor_eq_iff.mpr ⟨h1, h2⟩
  have hs1 : ⌊x⌋ = n + ⌊t⌋ := by
    calc ⌊x⌋ = ⌊t + (n : ℝ)⌋ := by rw [hxt]
      _ = ⌊t⌋ + n := Int.floor_add_intCast t n
      _ = n + ⌊t⌋ := by ring
  have hs2 : ⌊(2 : ℝ) * x⌋ = 2 * n + ⌊(2 : ℝ) * t⌋ := by
    have hx' : (2 : ℝ) * x = (2 : ℝ) * t + ((2 : ℤ) * n : ℤ) := by
      calc (2 : ℝ) * x = (2 : ℝ) * (t + (n : ℝ)) := by rw [hxt]
        _ = (2 : ℝ) * t + ((2 : ℤ) * n : ℤ) := by push_cast; ring
    rw [hx', Int.floor_add_intCast]
    ring
  have hs3 : ⌊(3 : ℝ) * x⌋ = 3 * n + ⌊(3 : ℝ) * t⌋ := by
    have hx' : (3 : ℝ) * x = (3 : ℝ) * t + ((3 : ℤ) * n : ℤ) := by
      calc (3 : ℝ) * x = (3 : ℝ) * (t + (n : ℝ)) := by rw [hxt]
        _ = (3 : ℝ) * t + ((3 : ℤ) * n : ℤ) := by push_cast; ring
    rw [hx', Int.floor_add_intCast]
    ring
  have hf1 : f1 x = 8 * n + 2 * ⌊3 * t⌋ + 2 * ⌊t⌋ := by
    rw [hv1, hs3, hs1]
    ring
  have hf2 : f2 x = 8 * n + ⌊3 * t⌋ + ⌊2 * t⌋ + 3 * ⌊t⌋ := by
    rw [hv2, hs3, hs2, hs1]
    ring
  have hf3 : f3 x = 8 * n + 4 * ⌊2 * t⌋ := by
    rw [hv3, hs2]
    ring
  have hf4 : f4 x = 8 * n + 3 * ⌊2 * t⌋ + 2 * ⌊t⌋ := by
    rw [hv4, hs2, hs1]
    ring
  have key : ∀ g1 g2 : ℝ → ℤ, g1 ∈ S → g2 ∈ S → g1 ≠ g2 → g1 x = g2 x →
      (∀ g ∈ S, g1 x ≤ g x) → False := by
    intro g1 g2 hg1 hg2 hne heq hle
    rcases eq_or_ne f g1 with hfg | hfg
    · have h2 : g2 ≠ f := by rw [hfg]; exact hne.symm
      have hlt' := hlt g2 hg2 h2
      rw [hfg, heq] at hlt'
      exact lt_irrefl _ hlt'
    · have h1 : g1 ≠ f := fun h => hfg h.symm
      have hA := hlt g1 hg1 h1
      have hB := hle f hf
      omega
  have ht3 : ⌊t⌋ = 0 := hfloor t 0 (by push_cast; linarith) (by push_cast; linarith)
  rcases lt_or_ge t (1 / 3) with hA | hA
  · -- t < 1/3 : all four values are equal to 8 n
    have h3 : ⌊3 * t⌋ = 0 := hfloor (3 * t) 0 (by push_cast; linarith) (by push_cast; linarith)
    have h2 : ⌊2 * t⌋ = 0 := hfloor (2 * t) 0 (by push_cast; linarith) (by push_cast; linarith)
    have h1x : f1 x = 8 * n := by rw [hf1, h3, ht3]; ring
    have h2x : f2 x = 8 * n := by rw [hf2, h3, h2, ht3]; ring
    have h3x : f3 x = 8 * n := by rw [hf3, h2]; ring
    have h4x : f4 x = 8 * n := by rw [hf4, h2, ht3]; ring
    refine key f1 f2 (by simp [S]) (by simp [S]) h12 (by rw [h1x, h2x]) ?_
    intro g hg
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hg
    rw [h1x]
    rcases hg with rfl | rfl | rfl | rfl
    · rw [h1x]
    · rw [h2x]
    · rw [h3x]
    · rw [h4x]
  rcases lt_or_ge t (1 / 2) with hB | hB
  · -- 1/3 <= t < 1/2
    have h3 : ⌊3 * t⌋ = 1 := hfloor (3 * t) 1 (by push_cast; linarith) (by push_cast; linarith)
    have h2 : ⌊2 * t⌋ = 0 := hfloor (2 * t) 0 (by push_cast; linarith) (by push_cast; linarith)
    have h1x : f1 x = 8 * n + 2 := by rw [hf1, h3, ht3]; ring
    have h2x : f2 x = 8 * n + 1 := by rw [hf2, h3, h2, ht3]; ring
    have h3x : f3 x = 8 * n := by rw [hf3, h2]; ring
    have h4x : f4 x = 8 * n := by rw [hf4, h2, ht3]; ring
    refine key f3 f4 (by simp [S]) (by simp [S]) h34 (by rw [h3x, h4x]) ?_
    intro g hg
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hg
    rw [h3x]
    rcases hg with rfl | rfl | rfl | rfl
    · rw [h1x]; omega
    · rw [h2x]; omega
    · rw [h3x]
    · rw [h4x]
  rcases lt_or_ge t (2 / 3) with hC | hC
  · -- 1/2 <= t < 2/3
    have h3 : ⌊3 * t⌋ = 1 := hfloor (3 * t) 1 (by push_cast; linarith) (by push_cast; linarith)
    have h2 : ⌊2 * t⌋ = 1 := hfloor (2 * t) 1 (by push_cast; linarith) (by push_cast; linarith)
    have h1x : f1 x = 8 * n + 2 := by rw [hf1, h3, ht3]; ring
    have h2x : f2 x = 8 * n + 2 := by rw [hf2, h3, h2, ht3]; ring
    have h3x : f3 x = 8 * n + 4 := by rw [hf3, h2]; ring
    have h4x : f4 x = 8 * n + 3 := by rw [hf4, h2, ht3]; ring
    refine key f1 f2 (by simp [S]) (by simp [S]) h12 (by rw [h1x, h2x]) ?_
    intro g hg
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hg
    rw [h1x]
    rcases hg with rfl | rfl | rfl | rfl
    · rw [h1x]
    · rw [h2x]
    · rw [h3x]; omega
    · rw [h4x]; omega
  · -- 2/3 <= t < 1
    have h3 : ⌊3 * t⌋ = 2 := hfloor (3 * t) 2 (by push_cast; linarith) (by push_cast; linarith)
    have h2 : ⌊2 * t⌋ = 1 := hfloor (2 * t) 1 (by push_cast; linarith) (by push_cast; linarith)
    have h1x : f1 x = 8 * n + 4 := by rw [hf1, h3, ht3]; ring
    have h2x : f2 x = 8 * n + 3 := by rw [hf2, h3, h2, ht3]; ring
    have h3x : f3 x = 8 * n + 4 := by rw [hf3, h2]; ring
    have h4x : f4 x = 8 * n + 3 := by rw [hf4, h2, ht3]; ring
    refine key f2 f4 (by simp [S]) (by simp [S]) h24 (by rw [h2x, h4x]) ?_
    intro g hg
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hg
    rw [h2x]
    rcases hg with rfl | rfl | rfl | rfl
    · rw [h1x]; omega
    · rw [h2x]
    · rw [h3x]; omega
    · rw [h4x]
