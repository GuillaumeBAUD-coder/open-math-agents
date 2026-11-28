import OMAStatements.S_oeis_a286014
import Mathlib

/-!
The parts m+1, ..., m+k sum to k*m + k(k+1)/2. For fixed k >= 1 at most one m gives the sum n,
namely m = (n - k(k+1)/2)/k, and it exists exactly when k divides n - k(k+1)/2; its smallest
part (n - k(k+1)/2)/k + 1 is the entry A211343(n,k). Summing over k gives the row sum.
-/

namespace R286014
open OMA.S_oeis_a286014

theorem sum2 (m k : ℕ) : (consecParts m k).sum * 2 = k * (2 * m + k + 1) := by
  induction k with
  | zero => simp [consecParts]
  | succ k ih =>
    unfold consecParts at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [add_mul, ih]
    ring

theorem sum_eq (m k : ℕ) : (consecParts m k).sum = k * m + k * (k + 1) / 2 := by
  have h := sum2 m k
  have ht : k * (k + 1) / 2 * 2 = k * (k + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
  have e : k * (2 * m + k + 1) = 2 * (k * m) + k * (k + 1) := by ring
  rw [e] at h
  generalize (consecParts m k).sum = S at h ⊢
  generalize k * (k + 1) = Y at h ht ⊢
  generalize k * m = X at h ⊢
  omega

theorem sum_single (n k t : ℕ) (hk : 1 ≤ k) (f : ℕ → ℕ) :
    ∑ m ∈ Finset.range (n + 1), (if k * m + t = n then f m else 0) =
      if t ≤ n ∧ (n - t) % k = 0 then f ((n - t) / k) else 0 := by
  split_ifs with hc
  · obtain ⟨ht, hd⟩ := hc
    have hm0 : k * ((n - t) / k) = n - t := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)
    have hiff : ∀ m, k * m + t = n ↔ m = (n - t) / k := by
      intro m
      constructor
      · intro h
        apply Nat.eq_of_mul_eq_mul_left hk
        omega
      · rintro rfl
        omega
    simp only [hiff]
    rw [Finset.sum_ite_eq', if_pos]
    rw [Finset.mem_range]
    have : (n - t) / k ≤ n - t := Nat.div_le_self _ _
    omega
  · apply Finset.sum_eq_zero
    intro m _
    rw [if_neg]
    intro h
    apply hc
    refine ⟨by omega, ?_⟩
    have : n - t = k * m := by omega
    rw [this, Nat.mul_mod_right]

theorem col (n k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.range (n + 1),
      (if (consecParts m k).sum = n then m + 1 else 0) =
      if k * (k + 1) / 2 ≤ n then A211343 n k else 0 := by
  simp only [sum_eq]
  rw [sum_single n k (k * (k + 1) / 2) hk (fun m => m + 1)]
  unfold A211343
  by_cases h : k * (k + 1) / 2 ≤ n
  · rw [if_pos h]
  · rw [if_neg h, if_neg (fun h' => h h'.1)]

theorem main' (n : ℕ) : a n = rowSum n := by
  unfold a rowSum
  simp only [Finset.sum_filter]
  rw [Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  exact col n k hk.1

end R286014

theorem OMA.solution : type_of% @OMA.S_oeis_a286014.main := by
  intro n _
  exact R286014.main' n
