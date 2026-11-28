import OMAStatements.S_oeis_a326247
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a326247 Finset

/-- Number of good pairs of edges whose right ends are `b` and `d`. -/
def edgeCnt326 (b d : ℕ) : ℕ :=
  ∑ x ∈ range b, ∑ y ∈ range d,
    if ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0

/-- Closed form of `edgeCnt326`. -/
def edgeCF326 (b d : ℕ) : ℕ :=
  if b < d then b * (d + 1 - b) else if d < b then d * (b + 1 - d) else b * b

theorem a326_as_sum (n : ℕ) :
    a n = ∑ b ∈ range n, ∑ d ∈ range n, edgeCnt326 b d := by
  unfold a
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hb' : b ≤ n := (Finset.mem_range.mp hb).le
  have hd' : d ≤ n := (Finset.mem_range.mp hd).le
  unfold edgeCnt326
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hb')]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxb : x < b := Finset.mem_range.mp hx
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hd')]
    · refine Finset.sum_congr rfl (fun y hy => ?_)
      have hyd : y < d := Finset.mem_range.mp hy
      simp only [hxb, hyd, true_and]
    · intro y _ hy
      have hyd : ¬ y < d := fun h => hy (Finset.mem_range.mpr h)
      simp only [hyd, false_and, and_false, if_false]
  · intro x _ hx
    have hxb : ¬ x < b := fun h => hx (Finset.mem_range.mpr h)
    simp only [hxb, false_and, if_false, Finset.sum_const_zero]

theorem cnt326_ind (x b : ℕ) (hxb : x < b) :
    ∀ m : ℕ, (∑ y ∈ range m, if y = x ∨ b ≤ y then 1 else 0) = (if x < m then 1 else 0) + (m - b) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

theorem edgeCnt326_lt (b d : ℕ) (h : b < d) : edgeCnt326 b d = b * (d + 1 - b) := by
  unfold edgeCnt326
  have key : ∀ x ∈ range b, (∑ y ∈ range d,
      if ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0) = d + 1 - b := by
    intro x hx
    have hxb : x < b := Finset.mem_range.mp hx
    rw [Finset.sum_congr rfl (g := fun y => if y = x ∨ b ≤ y then 1 else 0)]
    · rw [cnt326_ind x b hxb d]
      rw [if_pos (by omega)]
      omega
    · intro y hy
      have hyd : y < d := Finset.mem_range.mp hy
      by_cases hc : y = x ∨ b ≤ y
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem edgeCnt326_symm (b d : ℕ) : edgeCnt326 b d = edgeCnt326 d b := by
  unfold edgeCnt326
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  by_cases hc : ¬ Crossing x b y d ∧ ¬ Nesting x b y d
  · rw [if_pos hc, if_pos (by omega)]
  · rw [if_neg hc, if_neg (by omega)]

theorem edgeCnt326_eq (b : ℕ) : edgeCnt326 b b = b * b := by
  unfold edgeCnt326
  have key : ∀ x ∈ range b, (∑ y ∈ range b,
      if ¬ Crossing x b y b ∧ ¬ Nesting x b y b then 1 else 0) = b := by
    intro x hx
    have hxb : x < b := Finset.mem_range.mp hx
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro y hy
      have hyd : y < b := Finset.mem_range.mp hy
      rw [if_pos (by omega)]
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem edgeCnt326_cf (b d : ℕ) : edgeCnt326 b d = edgeCF326 b d := by
  unfold edgeCF326
  rcases Nat.lt_trichotomy b d with h | h | h
  · rw [if_pos h, edgeCnt326_lt b d h]
  · subst h
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), edgeCnt326_eq]
  · rw [if_neg (by omega), if_pos h, edgeCnt326_symm, edgeCnt326_lt d b h]

theorem gauss326 (n : ℕ) : 2 * (∑ b ∈ range n, (b : ℤ)) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem side326 (n : ℕ) : 6 * (∑ b ∈ range n, ((b * (n + 1 - b) : ℕ) : ℤ)) = n * (n - 1) * (n + 4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have e : ∀ b ∈ range n, ((b * (n + 1 + 1 - b) : ℕ) : ℤ) = ((b * (n + 1 - b) : ℕ) : ℤ) + b := by
      intro b hb
      have hbn : b < n := Finset.mem_range.mp hb
      rw [show n + 1 + 1 - b = (n + 1 - b) + 1 by omega]
      push_cast
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, mul_add, mul_add, ih]
    have g := gauss326 n
    rw [show n + 1 + 1 - n = 2 by omega]
    push_cast
    linear_combination 3 * g

theorem closed326 (n : ℕ) : 12 * (a n : ℤ) = n * (12 - 19 * n + 6 * n ^ 2 + n ^ 3) := by
  rw [a326_as_sum]
  simp_rw [edgeCnt326_cf]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    push_cast
    have h1 : ∀ b ∈ range n, ((edgeCF326 b n : ℕ) : ℤ) = ((b * (n + 1 - b) : ℕ) : ℤ) := by
      intro b hb
      have hbn : b < n := Finset.mem_range.mp hb
      unfold edgeCF326
      rw [if_pos hbn]
    have h2 : ∀ d ∈ range n, ((edgeCF326 n d : ℕ) : ℤ) = ((d * (n + 1 - d) : ℕ) : ℤ) := by
      intro d hd
      have hdn : d < n := Finset.mem_range.mp hd
      unfold edgeCF326
      rw [if_neg (by omega), if_pos hdn]
    have h3 : ((edgeCF326 n n : ℕ) : ℤ) = (n : ℤ) * n := by
      unfold edgeCF326
      rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
      push_cast
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, h3]
    have s := side326 n
    push_cast at ih s ⊢
    linear_combination ih + 4 * s

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a326247.main := by
  refine ⟨closed326, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e0 := closed326 (m + 5)
  have e1 := closed326 (m + 4)
  have e2 := closed326 (m + 3)
  have e3 := closed326 (m + 2)
  have e4 := closed326 (m + 1)
  have e5 := closed326 m
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  push_cast at e0 e1 e2 e3 e4 e5
  linarith
