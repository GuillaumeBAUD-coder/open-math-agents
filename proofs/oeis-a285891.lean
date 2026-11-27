import OMAStatements.S_oeis_a285891
import Mathlib

/-!
The parts m+1, ..., m+k sum to k*m + k(k+1)/2, so for k >= 1 the sum equals n for at most one m,
namely m = (n - k(k+1)/2)/k, and it exists exactly when k divides n - k(k+1)/2.
-/

namespace R285891
open OMA.S_oeis_a285891

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

theorem main' (n k : ℕ) (hk : 1 ≤ k) (ht : k * (k + 1) / 2 ≤ n) :
    T n k = ∑ m ∈ Finset.range (n + 1),
      (if (consecParts m k).sum = n then (consecParts m k).sum else 0) := by
  simp only [sum_eq]
  rw [sum_single n k (k * (k + 1) / 2) hk (fun m => k * m + k * (k + 1) / 2)]
  unfold T A237048
  by_cases hd : (n - k * (k + 1) / 2) % k = 0
  · rw [if_pos ⟨ht, hd⟩, if_pos ⟨ht, hd⟩, mul_one]
    have hm0 : k * ((n - k * (k + 1) / 2) / k) = n - k * (k + 1) / 2 :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)
    omega
  · rw [if_neg (fun h => hd h.2), if_neg (fun h => hd h.2), mul_zero]

end R285891

theorem OMA.solution : type_of% @OMA.S_oeis_a285891.main := by
  intro n k _ hk ht
  exact R285891.main' n k hk ht
