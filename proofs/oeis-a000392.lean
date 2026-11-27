import OMAStatements.S_oeis_a000392
import Mathlib.Tactic

/-!
# Layman's sum of distinct products of twos and threes

In the next set, every multiple of three is three times an element of the
current set. The other elements are exactly the powers of two. These two
parts give the two terms of the Stirling recurrence. The statement and an
earlier standalone proof were contributed by @Heart-galaxy in PR #6907.
-/

open Finset OMA.S_oeis_a000392

private theorem mem_products (n x : ℕ) :
    x ∈ S (n+1) ↔ ∃ i j : ℕ, i+j ≤ n ∧ x = 2^i * 3^j := by
  induction n generalizing x with
  | zero =>
    constructor
    · intro hx
      refine ⟨0,0,by decide,?_⟩
      simpa [S] using hx
    · rintro ⟨i,j,h,rfl⟩
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      simp [hi,hj,S]
  | succ n ih =>
    change x ∈ (S (n+1) ∪ (S (n+1)).image (fun y => 2*y)) ∪
        (S (n+1)).image (fun y => 3*y) ↔ _
    simp only [mem_union,mem_image]
    constructor
    · rintro ((h | ⟨y,hy,rfl⟩) | ⟨y,hy,rfl⟩)
      · obtain ⟨i,j,hij,rfl⟩ := (ih _).mp h
        exact ⟨i,j,by omega,rfl⟩
      · obtain ⟨i,j,hij,rfl⟩ := (ih _).mp hy
        exact ⟨i+1,j,by omega,by rw [pow_succ]; ring⟩
      · obtain ⟨i,j,hij,rfl⟩ := (ih _).mp hy
        exact ⟨i,j+1,by omega,by rw [pow_succ]; ring⟩
    · rintro ⟨i,j,h,rfl⟩
      cases i with
      | succ i =>
        exact Or.inl (Or.inr ⟨_, (ih _).mpr ⟨i,j,by omega,rfl⟩, by rw [pow_succ]; ring⟩)
      | zero =>
        cases j with
        | zero => exact Or.inl (Or.inl ((ih _).mpr ⟨0,0,by omega,rfl⟩))
        | succ j =>
          exact Or.inr ⟨_, (ih _).mpr ⟨0,j,by omega,rfl⟩, by rw [pow_succ]; ring⟩

private theorem next_set (n : ℕ) :
    S (n+2) = (S (n+1)).image (fun y => 3*y) ∪ (range (n+2)).image (fun j => 2^j) := by
  ext x
  rw [mem_products]
  simp only [mem_union,mem_image,mem_range]
  constructor
  · rintro ⟨i,j,h,rfl⟩
    cases j with
    | zero => exact Or.inr ⟨i,by omega,by simp⟩
    | succ j =>
      exact Or.inl ⟨_, (mem_products _ _).mpr ⟨i,j,by omega,rfl⟩, by rw [pow_succ]; ring⟩
  · rintro (⟨y,hy,rfl⟩ | ⟨i,hi,rfl⟩)
    · obtain ⟨i,j,h,rfl⟩ := (mem_products _ _).mp hy
      exact ⟨i,j+1,by omega,by rw [pow_succ]; ring⟩
    · exact ⟨i,0,by omega,by simp⟩

private theorem two_blocks (n : ℕ) :
    Nat.stirlingSecond (n+1) 2 = ∑ i ∈ range n, 2^i := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.stirlingSecond_succ_succ (n+1) 1, Nat.stirlingSecond_one_right, ih,
      Finset.sum_range_succ']
    simp [pow_succ', Finset.mul_sum]

theorem OMA.solution : type_of% @OMA.S_oeis_a000392.main := by
  intro n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  induction m with
  | zero => decide
  | succ m ih =>
    have hd : Disjoint ((S (m+1)).image (fun y => 3*y))
        ((range (m+2)).image (fun j => 2^j)) := by
      rw [Finset.disjoint_left]
      rintro _ hx hy
      obtain ⟨x,_,rfl⟩ := mem_image.mp hx
      obtain ⟨j,_,he⟩ := mem_image.mp hy
      have h : 3 ∣ 2^j := he ▸ dvd_mul_right 3 x
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
    have recSum := Nat.stirlingSecond_succ_succ (m+3) 2
    change Nat.stirlingSecond (m+4) 3 = ∑ x ∈ S (m+2), x
    change Nat.stirlingSecond (m+3) 3 = ∑ x ∈ S (m+1), x at ih
    rw [recSum, ih, two_blocks (m+2), next_set, sum_union hd]
    rw [sum_image (fun _ _ _ _ h => by omega),
      sum_image (fun _ _ _ _ h => (Nat.pow_right_inj (by decide : 1 < 2)).mp h),
      Finset.mul_sum]

