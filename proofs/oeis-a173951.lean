import OMAStatements.S_oeis_a173951
import Mathlib

/-!
# A173951: every term of A173952 is a term of A173951

By induction, b(n) + 4 = 4 * 9^n. Write n = k + 1. The list L = [2, 1] ++ (2k copies of 2) ++ [0, 1]
has base-3 value 4 * 9^(k+1) - 4 = b(k+1), its entries are below 3 and its last entry is 1, so it
is exactly the list of base-3 digits of b(k+1). Its reverse [1, 0] ++ (2k copies of 2) ++ [1, 2]
has base-3 value 8 * 9^(k+1) - 8 = 2 * b(k+1), which is the defining property of A173951.
-/

namespace OMA.P173951

open OMA.S_oeis_a173951

lemma b_add (n : ℕ) : b n + 4 = 4 * 9 ^ n := by
  induction n with
  | zero => simp [b]
  | succ n ih => simp only [b, pow_succ]; omega

lemma rep (m : ℕ) : Nat.ofDigits 3 (List.replicate m 2) + 1 = 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]; omega

def L (k : ℕ) : List ℕ := [2, 1] ++ List.replicate (2 * k) 2 ++ [0, 1]

lemma L_val (k : ℕ) : Nat.ofDigits 3 (L k) = b (k + 1) := by
  have h1 := rep (2 * k)
  have h2 := b_add (k + 1)
  have h3 : (3 : ℕ) ^ (2 * k) = 9 ^ k := by rw [pow_mul]; norm_num
  simp only [L, Nat.ofDigits_append, List.length_append, List.length_replicate,
    Nat.ofDigits_cons, Nat.ofDigits_nil, List.length_cons, List.length_nil] at *
  rw [pow_succ] at h2
  have h4 : (3 : ℕ) ^ (0 + 1 + 1 + 2 * k) = 9 * 9 ^ k := by
    rw [show 0 + 1 + 1 + 2 * k = 2 + 2 * k by omega, pow_add, h3]; norm_num
  rw [h4]
  rw [h3] at h1
  generalize Nat.ofDigits 3 (List.replicate (2 * k) 2) = R at *
  generalize 9 ^ k = T at *
  norm_num
  omega

lemma L_rev_val (k : ℕ) : Nat.ofDigits 3 (L k).reverse = 2 * b (k + 1) := by
  have h1 := rep (2 * k)
  have h2 := b_add (k + 1)
  have h3 : (3 : ℕ) ^ (2 * k) = 9 ^ k := by rw [pow_mul]; norm_num
  have hr : (L k).reverse = [1, 0] ++ List.replicate (2 * k) 2 ++ [1, 2] := by
    simp [L, List.reverse_append, List.reverse_replicate]
  rw [hr]
  simp only [Nat.ofDigits_append, List.length_append, List.length_replicate,
    Nat.ofDigits_cons, Nat.ofDigits_nil, List.length_cons, List.length_nil] at *
  rw [pow_succ] at h2
  have h4 : (3 : ℕ) ^ (0 + 1 + 1 + 2 * k) = 9 * 9 ^ k := by
    rw [show 0 + 1 + 1 + 2 * k = 2 + 2 * k by omega, pow_add, h3]; norm_num
  rw [h4]
  rw [h3] at h1
  generalize Nat.ofDigits 3 (List.replicate (2 * k) 2) = R at *
  generalize 9 ^ k = T at *
  norm_num
  omega

lemma L_digits (k : ℕ) : Nat.digits 3 (b (k + 1)) = L k := by
  rw [← L_val]
  apply Nat.digits_ofDigits _ (by norm_num)
  · intro l hl
    simp [L] at hl
    omega
  · intro h
    simp [L]

end OMA.P173951

open OMA.P173951 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173951.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · have := b_add (k + 1)
    have : 1 ≤ 9 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  · rw [L_digits, L_rev_val]
