import OMAStatements.S_oeis_a000392
import Mathlib.Tactic.Tauto

/-! OEIS A000392：从 {1} 开始，反复取原集合与其两倍、三倍的并集，证明其元素和公式。 -/

namespace A000392Proof

open OMA.S_oeis_a000392

abbrev rounds (n : ℕ) : Finset ℕ := S (n + 1)

def scale (k : ℕ) (s : Finset ℕ) : Finset ℕ := s.image (k * ·)

-- row n 枚举 1, 2, 4, …, 2^n。
def row : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 => insert 1 (scale 2 (row n))

theorem row_grow (n : ℕ) : row (n + 1) = row n ∪ scale 2 (row n) := by
  induction n with
  | zero => simp [row, scale]
  | succ n ih =>
    have hone : 1 ∈ row (n + 1) := by simp [row]
    have hsub : row n ⊆ row (n + 1) := by
      rw [ih]
      exact Finset.subset_union_left
    ext x
    change x ∈ insert 1 (scale 2 (row (n + 1))) ↔ x ∈ row (n + 1) ∪ scale 2 (row (n + 1))
    simp only [Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro (rfl | h)
      · exact Or.inl hone
      · exact Or.inr h
    · rintro (h | h)
      · change x ∈ insert 1 (scale 2 (row n)) at h
        rcases Finset.mem_insert.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.image_subset_image hsub h)
      · exact Or.inr h

theorem row_mod_three (n x : ℕ) (hx : x ∈ row n) : x % 3 ≠ 0 := by
  induction n generalizing x with
  | zero => simp [row] at hx; omega
  | succ n ih =>
    simp only [row, Finset.mem_insert, scale, Finset.mem_image] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · decide
    · have := ih y hy
      omega

theorem row_disjoint (n : ℕ) (s : Finset ℕ) : Disjoint (row n) (scale 3 s) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hs
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hs
  have := row_mod_three n _ hx
  omega

theorem sum_scale (k : ℕ) (hk : 0 < k) (s : Finset ℕ) :
    (∑ x ∈ scale k s, x) = k * ∑ x ∈ s, x := by
  unfold scale
  rw [Finset.sum_image, Finset.mul_sum]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hk h

theorem row_sum (n : ℕ) : (∑ x ∈ row n, x) = Nat.stirlingSecond (n + 2) 2 := by
  induction n with
  | zero => simp [row, Nat.stirlingSecond]
  | succ n ih =>
    have hn : 1 ∉ scale 2 (row n) := by
      intro hm
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hm
      change 2 * y = 1 at hy
      omega
    rw [row, Finset.sum_insert hn, sum_scale 2 (by decide), ih]
    rw [Nat.stirlingSecond_succ_succ (n + 2) 1, Nat.stirlingSecond_one_right]
    change 1 + 2 * Nat.stirlingSecond (n + 2) 2 = 2 * Nat.stirlingSecond (n + 2) 2 + 1
    omega

def grow (s : Finset ℕ) : Finset ℕ := s ∪ scale 2 s ∪ scale 3 s

private theorem scale_union (k : ℕ) (s t : Finset ℕ) :
    scale k (s ∪ t) = scale k s ∪ scale k t := Finset.image_union ..

private theorem scale_commute (k l : ℕ) (s : Finset ℕ) :
    scale k (scale l s) = scale l (scale k s) := by
  simp only [scale, Finset.image_image]
  congr 1
  funext x
  exact Nat.mul_left_comm k l x

private theorem grow_union (s t : Finset ℕ) :
    grow (s ∪ t) = grow s ∪ grow t := by
  simp only [grow, scale_union]
  ext x
  simp only [Finset.mem_union]
  tauto

private theorem grow_scale (k : ℕ) (s : Finset ℕ) :
    grow (scale k s) = scale k (grow s) := by
  unfold grow
  rw [scale_union, scale_union, scale_commute 2 k, scale_commute 3 k]

-- 在下一轮中，带因子 3 的部分恰好来自上一轮整体乘 3。
private theorem split_round (n : ℕ) :
    rounds (n + 1) = row (n + 1) ∪ scale 3 (rounds n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change grow (rounds (n + 1)) = row (n + 2) ∪ scale 3 (rounds (n + 1))
    calc
      grow (rounds (n + 1)) =
          grow (row (n + 1)) ∪ grow (scale 3 (rounds n)) := by rw [ih, grow_union]
      _ = (row (n + 2) ∪ scale 3 (row (n + 1))) ∪ scale 3 (rounds (n + 1)) := by
          rw [grow_scale, row_grow (n + 1)]
          rfl
      _ = row (n + 2) ∪ scale 3 (rounds (n + 1)) := by
          have h : scale 3 (row (n + 1)) ⊆ scale 3 (rounds (n + 1)) := by
            rw [ih, scale_union]
            exact Finset.subset_union_left
          rw [Finset.union_assoc, Finset.union_eq_right.mpr h]

theorem rounds_sum (n : ℕ) :
    (∑ x ∈ rounds n, x) = Nat.stirlingSecond (n + 3) 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [split_round, Finset.sum_union (row_disjoint _ _), sum_scale 3 (by decide),
      row_sum, ih]
    exact (Nat.add_comm _ _).trans (Nat.stirlingSecond_succ_succ (n + 3) 2).symm

end A000392Proof

/-- OEIS A000392：集合 S(n) 的元素和等于第二类斯特林数 {n + 2,3}。 -/
theorem OMA.solution : type_of% @OMA.S_oeis_a000392.main := by
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact (A000392Proof.rounds_sum n).symm
