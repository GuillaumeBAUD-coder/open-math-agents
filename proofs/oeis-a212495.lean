import OMAStatements.S_oeis_a212495
import Mathlib

-- Problem: A212495: Numbers all of whose base 11 digits are even.
-- Upstream: formal-conjectures statements/oeis-a212495.lean:0 (declaration OMA.S_oeis_a212495.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Idea.  Below 11^L there are exactly 6^L numbers with only even base-11 digits (zero included),
-- and at most (5^(L+1) - 5)/4 positive numbers with only odd base-11 digits.  Since
-- 5^(L+2) <= 4 * 6^L for L >= 11, the odd-digit numbers below 11^(L+1) are fewer than the
-- even-digit numbers below 11^L.  So if the i-th odd-digit number is smaller than the i-th
-- even-digit number e, then e < 11^11, and i <= e.

namespace OMA.A212495

open OMA.S_oeis_a212495
open Classical

/-- The digit recursion for `evenDigits`. -/
lemma even_iff (m : ℕ) : evenDigits m ↔ Even (m % 11) ∧ evenDigits (m / 11) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [evenDigits]
  · unfold evenDigits
    rw [Nat.digits_def' (by norm_num) hm]
    simp

/-- The digit recursion for `oddDigits`. -/
lemma odd_iff (m : ℕ) : oddDigits m ↔ Odd (m % 11) ∧ (m / 11 = 0 ∨ oddDigits (m / 11)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [oddDigits]
  · unfold oddDigits
    rw [Nat.digits_def' (by norm_num) hm]
    constructor
    · rintro ⟨_, h⟩
      refine ⟨h (m % 11) (by simp), ?_⟩
      rcases Nat.eq_zero_or_pos (m / 11) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0, fun d hd => h d (by simp [hd])⟩
    · rintro ⟨h1, h2⟩
      refine ⟨hm, fun d hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · exact h1
      · rcases h2 with h0 | h0
        · rw [h0] at hd
          simp at hd
        · exact h0.2 d hd

/-- Among the eleven numbers `11 n, ..., 11 n + 10`, six have only even digits if `n` does,
and none otherwise. -/
lemma blockE (n : ℕ) :
    Nat.count (fun k => evenDigits (11 * n + k)) 11 = if evenDigits n then 6 else 0 := by
  have key : ∀ k, k < 11 → (evenDigits (11 * n + k) ↔ (Even k ∧ evenDigits n)) := by
    intro k hk
    rw [even_iff]
    have h1 : (11 * n + k) % 11 = k := by omega
    have h2 : (11 * n + k) / 11 = n := by omega
    rw [h1, h2]
  rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.count_succ, Nat.count_zero]
  rw [key 0 (by norm_num), key (0 + 1) (by norm_num), key (0 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1) (by norm_num), key (0 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1) (by norm_num), key (0 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num)]
  by_cases h : evenDigits n
  · norm_num [h, Nat.even_iff]
  · simp [h]

/-- Among the eleven numbers `11 n, ..., 11 n + 10`, five have only odd digits if `n = 0` or `n`
has only odd digits, and none otherwise. -/
lemma blockO (n : ℕ) :
    Nat.count (fun k => oddDigits (11 * n + k)) 11 = if (n = 0 ∨ oddDigits n) then 5 else 0 := by
  have key : ∀ k, k < 11 → (oddDigits (11 * n + k) ↔ (Odd k ∧ (n = 0 ∨ oddDigits n))) := by
    intro k hk
    rw [odd_iff]
    have h1 : (11 * n + k) % 11 = k := by omega
    have h2 : (11 * n + k) / 11 = n := by omega
    rw [h1, h2]
  rw [show (11 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.count_succ, Nat.count_zero]
  rw [key 0 (by norm_num), key (0 + 1) (by norm_num), key (0 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1) (by norm_num), key (0 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1) (by norm_num), key (0 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num),
    key (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by norm_num)]
  by_cases h : (n = 0 ∨ oddDigits n)
  · norm_num [h, Nat.odd_iff]
  · simp [h]

/-- Counting even-digit numbers below a multiple of 11. -/
lemma countE_mul (n : ℕ) : Nat.count evenDigits (11 * n) = 6 * Nat.count evenDigits n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Nat.count_add, ih, blockE, Nat.count_succ]
    split_ifs <;> ring

/-- Counting odd-digit numbers below a multiple of 11. -/
lemma countO_mul (n : ℕ) : Nat.count oddDigits (11 * n) ≤ 5 * Nat.count oddDigits n + 5 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Nat.count_add, blockO, Nat.count_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : n ≠ 0 := by omega
      by_cases h : oddDigits n
      · simp only [h, or_true, if_true]
        omega
      · simp only [h, hn0, or_self, if_false]
        omega

/-- There are exactly `6 ^ L` even-digit numbers below `11 ^ L`. -/
lemma countE_pow (L : ℕ) : Nat.count evenDigits (11 ^ L) = 6 ^ L := by
  induction L with
  | zero =>
    have h0 : evenDigits 0 := by simp [evenDigits]
    have h1 : Nat.count evenDigits (0 + 1) = 1 := by
      rw [Nat.count_succ, Nat.count_zero, if_pos h0]
    simpa using h1
  | succ L ih =>
    rw [pow_succ, mul_comm, countE_mul, ih]
    ring

/-- There are at most `(5 ^ (L + 1) - 5) / 4` odd-digit numbers below `11 ^ L`. -/
lemma countO_pow (L : ℕ) : 4 * Nat.count oddDigits (11 ^ L) + 5 ≤ 5 ^ (L + 1) := by
  induction L with
  | zero =>
    have h0 : ¬ oddDigits 0 := by simp [oddDigits]
    have h1 : Nat.count oddDigits (0 + 1) = 0 := by
      rw [Nat.count_succ, Nat.count_zero, if_neg h0]
    have h2 : Nat.count oddDigits (11 ^ 0) = 0 := by simpa using h1
    rw [h2]
    norm_num
  | succ L ih =>
    have h := countO_mul (11 ^ L)
    have h3 : (11 : ℕ) ^ (L + 1) = 11 * 11 ^ L := by ring
    have h4 : (5 : ℕ) ^ (L + 1 + 1) = 5 * 5 ^ (L + 1) := by ring
    rw [h3, h4]
    omega

/-- The numerical inequality behind the comparison. -/
lemma pow_ineq (L : ℕ) (hL : 11 ≤ L) : 5 ^ (L + 2) ≤ 4 * 6 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h1 : (5 : ℕ) ^ (L + 1 + 2) = 5 * 5 ^ (L + 2) := by ring
    have h2 : (6 : ℕ) ^ (L + 1) = 6 * 6 ^ L := by ring
    rw [h1, h2]
    omega

/-- Infinitely many numbers have only even digits. -/
lemma infE : (Set.ofPred evenDigits).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  induction a with
  | zero =>
    refine ⟨2, ?_, by norm_num⟩
    show evenDigits 2
    rw [even_iff]
    refine ⟨by norm_num, ?_⟩
    norm_num [evenDigits]
  | succ a ih =>
    obtain ⟨b, hb, hab⟩ := ih
    refine ⟨11 * b, ?_, by omega⟩
    show evenDigits (11 * b)
    rw [even_iff]
    have h1 : (11 * b) % 11 = 0 := by omega
    have h2 : (11 * b) / 11 = b := by omega
    rw [h1, h2]
    exact ⟨by norm_num, hb⟩

/-- Infinitely many numbers have only odd digits. -/
lemma infO : (Set.ofPred oddDigits).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  induction a with
  | zero =>
    refine ⟨1, ?_, by norm_num⟩
    show oddDigits 1
    rw [odd_iff]
    exact ⟨by norm_num, Or.inl (by norm_num)⟩
  | succ a ih =>
    obtain ⟨b, hb, hab⟩ := ih
    refine ⟨11 * b + 1, ?_, by omega⟩
    show oddDigits (11 * b + 1)
    rw [odd_iff]
    have h1 : (11 * b + 1) % 11 = 1 := by omega
    have h2 : (11 * b + 1) / 11 = b := by omega
    rw [h1, h2]
    exact ⟨by norm_num, Or.inr hb⟩

/-- Every index at which the odd-digit number is the smaller one is below `11 ^ 11`. -/
lemma index_lt (i : ℕ) (hi : Nat.nth oddDigits i < Nat.nth evenDigits i) : i < 11 ^ 11 := by
  by_contra hcon
  have hi11 : 11 ^ 11 ≤ i := not_lt.1 hcon
  have hce : Nat.count evenDigits (Nat.nth evenDigits i) = i := Nat.count_nth_of_infinite infE i
  have hco : Nat.count oddDigits (Nat.nth oddDigits i) = i := Nat.count_nth_of_infinite infO i
  have hOo : oddDigits (Nat.nth oddDigits i) := Nat.nth_mem_of_infinite infO i
  have hie : i ≤ Nat.nth evenDigits i := by
    have h := Nat.count_le (p := evenDigits) (n := Nat.nth evenDigits i)
    rw [hce] at h
    exact h
  have hpos : 0 < 11 ^ 11 := by norm_num
  have he0 : Nat.nth evenDigits i ≠ 0 := by omega
  have hL1 : 11 ^ Nat.log 11 (Nat.nth evenDigits i) ≤ Nat.nth evenDigits i :=
    Nat.pow_log_le_self 11 he0
  have hL2 : Nat.nth evenDigits i < 11 ^ (Nat.log 11 (Nat.nth evenDigits i) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hL : 11 ≤ Nat.log 11 (Nat.nth evenDigits i) :=
    Nat.le_log_of_pow_le (by norm_num) (le_trans hi11 hie)
  have h1 : Nat.count evenDigits (11 ^ Nat.log 11 (Nat.nth evenDigits i)) ≤ i := by
    have h := Nat.count_monotone evenDigits hL1
    rw [hce] at h
    exact h
  have h2 : i + 1 ≤ Nat.count oddDigits (11 ^ (Nat.log 11 (Nat.nth evenDigits i) + 1)) := by
    have h3 : Nat.count oddDigits (Nat.nth oddDigits i + 1) = i + 1 := by
      rw [Nat.count_succ, if_pos hOo, hco]
    rw [← h3]
    exact Nat.count_monotone oddDigits (by omega)
  have h4 : 4 * Nat.count oddDigits (11 ^ (Nat.log 11 (Nat.nth evenDigits i) + 1)) + 5
      ≤ 5 ^ (Nat.log 11 (Nat.nth evenDigits i) + 2) :=
    countO_pow (Nat.log 11 (Nat.nth evenDigits i) + 1)
  have h5 := pow_ineq (Nat.log 11 (Nat.nth evenDigits i)) hL
  rw [countE_pow] at h1
  omega

end OMA.A212495

theorem OMA.solution : type_of% @OMA.S_oeis_a212495.main :=
  (Set.finite_lt_nat (11 ^ 11)).subset fun i hi => OMA.A212495.index_lt i hi
