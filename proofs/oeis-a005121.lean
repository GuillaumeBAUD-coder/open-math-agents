import OMAStatements.S_oeis_a005121
import Mathlib

/-!
Mohapatra's triangle reproduces Lengyel's recurrence. Let `hs r lo hi = h_r(lo, …, hi)` be the
complete homogeneous symmetric polynomial (recursion on the smallest variable). The split on
the largest variable together with the Stirling recurrence gives `h_r(1, …, m) = S(m + r, m)`.
By induction on `N`, the suffix sums of row `N` are
`∑_{j=k}^{N} R(N, j) = ∑_{m=1}^{N} a(m) h_{N-m}(k, …, m)` and `R(N, N) = a(N)`: the next row's
entries are `k` times these sums, summing them again raises the degree of `h` by one, and at
`k = 1` the diagonal becomes `∑_m S(N+1, m) a(m) = a(N+1)` (Lengyel).
-/

namespace A005121Proof

open OMA.S_oeis_a005121

open Finset

/-- complete homogeneous symmetric polynomial `h_r(lo, ..., hi)` -/
def hs : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | r + 1, lo, hi => ∑ i ∈ Icc lo hi, i * hs r i hi

lemma hs_zero_of_lt (r lo hi : ℕ) (h : hi < lo) : hs (r + 1) lo hi = 0 := by
  simp [hs, Finset.Icc_eq_empty_of_lt h]

lemma hs_top (r lo hi : ℕ) (hlo : lo ≤ hi + 1) :
    hs (r + 1) lo (hi + 1) = hs (r + 1) lo hi + (hi + 1) * hs r lo (hi + 1) := by
  induction r generalizing lo with
  | zero =>
    simp only [hs, mul_one]
    rw [Finset.sum_Icc_succ_top hlo]
  | succ r ih =>
    rw [hs, Finset.sum_Icc_succ_top hlo]
    have hdiag : hs (r + 1) (hi + 1) (hi + 1) = (hi + 1) * hs r (hi + 1) (hi + 1) := by
      simp [hs]
    have hsplit : ∑ i ∈ Icc lo hi, i * hs (r + 1) i (hi + 1) =
        ∑ i ∈ Icc lo hi, i * hs (r + 1) i hi + (hi + 1) * ∑ i ∈ Icc lo hi, i * hs r i (hi + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi'
      rw [mem_Icc] at hi'
      rw [ih i (by omega)]; ring
    have hr1 : hs (r + 1) lo (hi + 1) =
        ∑ i ∈ Icc lo hi, i * hs r i (hi + 1) + (hi + 1) * hs r (hi + 1) (hi + 1) := by
      rw [hs, Finset.sum_Icc_succ_top hlo]
    rw [hsplit, hdiag, hr1, show hs (r + 1 + 1) lo hi = ∑ i ∈ Icc lo hi, i * hs (r + 1) i hi from rfl]
    ring

lemma hs_stirling (r m : ℕ) : hs r 1 m = Nat.stirlingSecond (m + r) m := by
  induction r generalizing m with
  | zero => simp [hs, Nat.stirlingSecond_self]
  | succ r ih =>
    induction m with
    | zero => simp [hs]
    | succ m ihm =>
      rw [hs_top r 1 m (by omega), ihm, ih (m + 1),
        show m + 1 + (r + 1) = (m + 1 + r) + 1 by ring, Nat.stirlingSecond_succ_succ,
        show m + (r + 1) = m + 1 + r by ring]
      ring

lemma a_lengyel (N : ℕ) (hN : 1 ≤ N) :
    a (N + 1) = ∑ m ∈ Icc 1 N, Nat.stirlingSecond (N + 1) m * a m := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [a, Fin.sum_univ_eq_sum_range (fun k => if k = 0 then 0 else
    Nat.stirlingSecond (n + 2) k * a k), Finset.sum_range_succ']
  simp only [Nat.succ_ne_zero, if_false, if_true, add_zero]
  rw [show Icc 1 (n + 1) = Ico 1 (n + 2) from rfl, Finset.sum_Ico_eq_sum_range,
    show n + 2 - 1 = n + 1 by omega]
  apply Finset.sum_congr rfl; intro i _; rw [add_comm 1 i]

lemma R_succ (N k : ℕ) (hN : 1 ≤ N) (hk1 : 1 ≤ k) (hk : k ≤ N) :
    R (N + 1) k = k * ∑ j ∈ Icc k N, R N j := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [R, if_pos ⟨hk1, by omega⟩]

lemma R_diag (N : ℕ) (hN : 1 ≤ N) :
    R (N + 1) (N + 1) = ∑ i ∈ Icc 1 N, R (N + 1) i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [R, if_neg (by omega), if_pos rfl]
  apply Finset.sum_congr rfl
  intro i hi; rw [mem_Icc] at hi
  rw [R_succ (n + 1) i (by omega) hi.1 hi.2]

lemma key (N : ℕ) (hN : 1 ≤ N) : R N N = a N ∧ ∀ k, 1 ≤ k → k ≤ N →
    ∑ j ∈ Icc k N, R N j = ∑ m ∈ Icc 1 N, a m * hs (N - m) k m := by
  induction N, hN using Nat.le_induction with
  | base =>
    refine ⟨by simp [R, a], ?_⟩
    intro k hk1 hk
    obtain rfl : k = 1 := by omega
    simp [R, a, hs]
  | succ N hN ih =>
    obtain ⟨hdiag, hU⟩ := ih
    -- the entries of row N+1 below the diagonal
    have hrow : ∀ i, 1 ≤ i → i ≤ N → R (N + 1) i = ∑ m ∈ Icc 1 N, a m * (i * hs (N - m) i m) := by
      intro i hi1 hi
      rw [R_succ N i hN hi1 hi, hU i hi1 hi, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro m _; ring
    have hW : ∀ k, 1 ≤ k → ∑ i ∈ Icc k N, R (N + 1) i = ∑ m ∈ Icc 1 N, a m * hs (N + 1 - m) k m := by
      intro k hk1
      rw [Finset.sum_congr rfl (fun i hi => hrow i (by rw [mem_Icc] at hi; omega)
        (by rw [mem_Icc] at hi; omega)), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm; rw [mem_Icc] at hm
      rw [← Finset.mul_sum, show N + 1 - m = (N - m) + 1 by omega]
      congr 1
      rw [hs]
      by_cases hkm : k ≤ m
      · symm
        apply Finset.sum_subset
        · intro x hx; rw [mem_Icc] at hx ⊢; omega
        · intro x hx hx'
          rw [mem_Icc] at hx hx'
          have hxm : m < x := by omega
          obtain ⟨r, hr⟩ : ∃ r, N - m = r + 1 := ⟨N - m - 1, by omega⟩
          rw [hr, hs_zero_of_lt r x m hxm, mul_zero]
      · rw [Finset.Icc_eq_empty_of_lt (a := k) (b := m) (by omega), Finset.sum_empty]
        apply Finset.sum_eq_zero
        intro x hx; rw [mem_Icc] at hx
        by_cases hmN : m = N
        · omega
        · obtain ⟨r, hr⟩ : ∃ r, N - m = r + 1 := ⟨N - m - 1, by omega⟩
          rw [hr, hs_zero_of_lt r x m (by omega), mul_zero]
    have hdiag' : R (N + 1) (N + 1) = a (N + 1) := by
      rw [R_diag N hN, hW 1 le_rfl, a_lengyel N hN]
      apply Finset.sum_congr rfl
      intro m hm; rw [mem_Icc] at hm
      rw [hs_stirling, show m + (N + 1 - m) = N + 1 by omega]; ring
    refine ⟨hdiag', ?_⟩
    intro k hk1 hk
    rw [Finset.sum_Icc_succ_top (by omega), hW k hk1, hdiag',
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), Nat.sub_self]
    simp [hs]

theorem solved : ∀ n : ℕ, 1 ≤ n → a n = R n n := fun n hn => (key n hn).1.symm
end A005121Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a005121.main := A005121Proof.solved
