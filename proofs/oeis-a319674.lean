import OMAStatements.S_oeis_a319674
import Mathlib

/-!
Each block 6j+1..6j+6 adds 3 terms and subtracts 3 terms, so a(6j) = -9j, and then
a(6j+1) = 1-3j, a(6j+2) = 3j+3, a(6j+3) = 9j+6, a(6j+4) = 3j+2, a(6j+5) = -3j-3.
The index m with A047235(m) = n (resp. A007310(m) = n) is count(n) + 1, and the counting function
of the residues {2,4} (resp. {1,5}) mod 6 is explicit, which gives the parity of m.
-/

namespace R319674
open OMA.S_oeis_a319674

theorem a_step (n m : ℕ) (h : m = n + 1) : a m = a n + ((n : ℤ) + 1) * (-1) ^ (n / 3) := by
  subst h
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
  push_cast <;> ring

theorem s (j c : ℕ) : (-1 : ℤ) ^ (2 * j + c) = (-1) ^ c := by
  rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

theorem chain (j : ℕ) :
    a (6 * j + 1) = a (6 * j) + (6 * (j : ℤ) + 1) ∧
    a (6 * j + 2) = a (6 * j + 1) + (6 * (j : ℤ) + 2) ∧
    a (6 * j + 3) = a (6 * j + 2) + (6 * (j : ℤ) + 3) ∧
    a (6 * j + 4) = a (6 * j + 3) - (6 * (j : ℤ) + 4) ∧
    a (6 * j + 5) = a (6 * j + 4) - (6 * (j : ℤ) + 5) ∧
    a (6 * (j + 1)) = a (6 * j + 5) - (6 * (j : ℤ) + 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_step (6 * j) (6 * j + 1) rfl, show 6 * j / 3 = 2 * j + 0 by omega, s]
    push_cast <;> ring
  · rw [a_step (6 * j + 1) (6 * j + 2) rfl, show (6 * j + 1) / 3 = 2 * j + 0 by omega, s]
    push_cast <;> ring
  · rw [a_step (6 * j + 2) (6 * j + 3) rfl, show (6 * j + 2) / 3 = 2 * j + 0 by omega, s]
    push_cast <;> ring
  · rw [a_step (6 * j + 3) (6 * j + 4) rfl, show (6 * j + 3) / 3 = 2 * j + 1 by omega, s]
    push_cast <;> ring
  · rw [a_step (6 * j + 4) (6 * j + 5) rfl, show (6 * j + 4) / 3 = 2 * j + 1 by omega, s]
    push_cast <;> ring
  · rw [a_step (6 * j + 5) (6 * (j + 1)) (by ring), show (6 * j + 5) / 3 = 2 * j + 1 by omega, s]
    push_cast <;> ring

theorem a6 (j : ℕ) : a (6 * j) = -9 * (j : ℤ) := by
  induction j with
  | zero => simp [a]
  | succ j ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := chain j
    push_cast
    linarith

theorem aval (n : ℕ) :
    (n % 6 = 0 → (a n : ℚ) = -3 * n / 2) ∧ (n % 6 = 1 → (a n : ℚ) = (3 - n) / 2) ∧
    (n % 6 = 2 → (a n : ℚ) = (n + 4) / 2) ∧ (n % 6 = 3 → (a n : ℚ) = (3 * n + 3) / 2) ∧
    (n % 6 = 4 → (a n : ℚ) = n / 2) ∧ (n % 6 = 5 → (a n : ℚ) = (-n - 1) / 2) := by
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 6 ∧ n = 6 * j + r := ⟨n / 6, n % 6, by omega, by omega⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := chain j
  have h0 := a6 j
  have v1 : a (6 * j + 1) = -3 * (j : ℤ) + 1 := by linarith
  have v2 : a (6 * j + 2) = 3 * (j : ℤ) + 3 := by linarith
  have v3 : a (6 * j + 3) = 9 * (j : ℤ) + 6 := by linarith
  have v4 : a (6 * j + 4) = 3 * (j : ℤ) + 2 := by linarith
  have v5 : a (6 * j + 5) = -3 * (j : ℤ) - 3 := by linarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain rfl : r = 0 := by omega
    rw [add_zero, h0]
    push_cast <;> ring
  · obtain rfl : r = 1 := by omega
    rw [v1]
    push_cast <;> ring
  · obtain rfl : r = 2 := by omega
    rw [v2]
    push_cast <;> ring
  · obtain rfl : r = 3 := by omega
    rw [v3]
    push_cast <;> ring
  · obtain rfl : r = 4 := by omega
    rw [v4]
    push_cast <;> ring
  · obtain rfl : r = 5 := by omega
    rw [v5]
    push_cast <;> ring

theorem cntp (n : ℕ) : Nat.count (fun k => k % 6 = 2 ∨ k % 6 = 4) n =
    2 * (n / 6) + (if n % 6 ≤ 2 then 0 else if n % 6 ≤ 4 then 1 else 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.count_succ, ih]
    split_ifs <;> omega

theorem cntq (n : ℕ) : Nat.count (fun k => k % 6 = 1 ∨ k % 6 = 5) n =
    2 * (n / 6) + (if n % 6 ≤ 1 then 0 else 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.count_succ, ih]
    split_ifs <;> omega

theorem infp : {k : ℕ | k % 6 = 2 ∨ k % 6 = 4}.Infinite :=
  Set.infinite_of_forall_exists_gt
    (fun x => ⟨6 * x + 2, show (6 * x + 2) % 6 = 2 ∨ (6 * x + 2) % 6 = 4 by omega, by omega⟩)

theorem infq : {k : ℕ | k % 6 = 1 ∨ k % 6 = 5}.Infinite :=
  Set.infinite_of_forall_exists_gt
    (fun x => ⟨6 * x + 1, show (6 * x + 1) % 6 = 1 ∨ (6 * x + 1) % 6 = 5 by omega, by omega⟩)

theorem charp (m n : ℕ) (hm : 1 ≤ m) (h : A047235 m = n) :
    (n % 6 = 2 ∧ m % 2 = 1) ∨ (n % 6 = 4 ∧ m % 2 = 0) := by
  unfold A047235 at h
  have hpn : n % 6 = 2 ∨ n % 6 = 4 := by
    have := Nat.nth_mem_of_infinite infp (m - 1)
    rw [h] at this
    exact this
  have hc := Nat.count_nth_of_infinite infp (m - 1)
  rw [h, cntp] at hc
  split_ifs at hc <;> omega

theorem charq (m n : ℕ) (hm : 1 ≤ m) (h : A007310 m = n) :
    (n % 6 = 1 ∧ m % 2 = 1) ∨ (n % 6 = 5 ∧ m % 2 = 0) := by
  unfold A007310 at h
  have hpn : n % 6 = 1 ∨ n % 6 = 5 := by
    have := Nat.nth_mem_of_infinite infq (m - 1)
    rw [h] at this
    exact this
  have hc := Nat.count_nth_of_infinite infq (m - 1)
  rw [h, cntq] at hc
  split_ifs at hc <;> omega

theorem memp (n : ℕ) (hn : n % 6 = 2 ∨ n % 6 = 4) :
    A047235 (Nat.count (fun k => k % 6 = 2 ∨ k % 6 = 4) n + 1) = n := by
  unfold A047235
  rw [Nat.add_sub_cancel]
  exact Nat.nth_count hn

theorem memq (n : ℕ) (hn : n % 6 = 1 ∨ n % 6 = 5) :
    A007310 (Nat.count (fun k => k % 6 = 1 ∨ k % 6 = 5) n + 1) = n := by
  unfold A007310
  rw [Nat.add_sub_cancel]
  exact Nat.nth_count hn

theorem main' :
    ∀ n : ℕ, 2 ≤ n →
      (0 < a n →
        (∀ m : ℕ, 1 ≤ m → A047235 m = n →
            (a n : ℚ) = (n : ℚ) / 2 + 2 * ((m % 2 : ℕ) : ℚ)) ∧
        ((∀ m : ℕ, 1 ≤ m → A047235 m ≠ n) → (a n : ℚ) = 3 * ((n : ℚ) + 1) / 2)) ∧
      (a n < 0 →
        (∀ m : ℕ, 1 ≤ m → A007310 m = n →
            (a n : ℚ) = 1 + (1 - (n : ℚ)) / 2 + 2 * (((m % 2 : ℕ) : ℚ) - 1)) ∧
        ((∀ m : ℕ, 1 ≤ m → A007310 m ≠ n) → (a n : ℚ) = -3 * (n : ℚ) / 2)) := by
  intro n hn
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := aval n
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  refine ⟨fun hpos => ⟨?_, ?_⟩, fun hneg => ⟨?_, ?_⟩⟩
  · intro m hm hA
    rcases charp m n hm hA with ⟨h2, hm2⟩ | ⟨h4, hm2⟩
    · rw [v2 h2, hm2]
      push_cast <;> ring
    · rw [v4 h4, hm2]
      push_cast <;> ring
  · intro hno
    have hq : (0 : ℚ) < a n := by exact_mod_cast hpos
    have h3 : n % 6 = 3 := by
      by_contra hne
      have : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
      rcases this with h | h | h | h | h
      · rw [v0 h] at hq
        linarith
      · have h7 : (7 : ℚ) ≤ n := by exact_mod_cast (show 7 ≤ n by omega)
        rw [v1 h] at hq
        linarith
      · exact hno _ (by omega) (memp n (by omega))
      · exact hno _ (by omega) (memp n (by omega))
      · rw [v5 h] at hq
        linarith
    rw [v3 h3]
    ring
  · intro m hm hA
    rcases charq m n hm hA with ⟨h1, hm2⟩ | ⟨h5, hm2⟩
    · rw [v1 h1, hm2]
      push_cast <;> ring
    · rw [v5 h5, hm2]
      push_cast <;> ring
  · intro hno
    have hq : (a n : ℚ) < 0 := by exact_mod_cast hneg
    have h0 : n % 6 = 0 := by
      by_contra hne
      have : n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
      rcases this with h | h | h | h | h
      · exact hno _ (by omega) (memq n (by omega))
      · rw [v2 h] at hq
        linarith
      · rw [v3 h] at hq
        linarith
      · rw [v4 h] at hq
        linarith
      · exact hno _ (by omega) (memq n (by omega))
    rw [v0 h0]

end R319674

theorem OMA.solution : type_of% @OMA.S_oeis_a319674.main := by
  exact R319674.main'
