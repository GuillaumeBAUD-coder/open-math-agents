import OMAStatements.S_oeis_a386658
import Mathlib

/-!
# Proof of OEIS A386658 Conjecture

1. Modulo `2` (for `n >= 2`):
   `5 ≡ 1 (mod 2)`, so `a(n) ≡ 1 + n + ∑_{m = 2..n, m even} C(n, m) (mod 2)`.
   Since `∑_{m = 0..n, m even} C(n, m) ≡ 0 (mod 2)` for all `n >= 2`, we get
   `a(n) ≡ n (mod 2)`, matching `targetMod6 n` mod `2`.
2. Modulo `3`:
   `5 ≡ 2 (mod 3)`, so `(a n : ZMod 3)` satisfies the same `binomMod6` period-6 reduction as
   for base `2`, hence `(a (n + 6) : ZMod 3) = (a n : ZMod 3)` for all `n >= 6`.
   Checking `n = 6..11` matches `targetMod6 n` mod `3`.
3. Combining mod `2` and mod `3` by CRT gives `a(n) ≡ targetMod6 n [ZMOD 6]` for all `n >= 6`.
-/

namespace OeisA386658Proof

open Finset OMA.S_oeis_a386658

private lemma even_odd_binom_zmod2 (n : ℕ) (hn : 2 ≤ n) :
    (∑ m ∈ Finset.range (n + 1), if m % 2 = 0 then (Nat.choose n m : ZMod 2) else 0) = 0 ∧
    (∑ m ∈ Finset.range (n + 1), if m % 2 = 1 then (Nat.choose n m : ZMod 2) else 0) = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn1 : n = 1
    · subst hn1; decide
    · obtain ⟨ihE, ihO⟩ := ih (by omega)
      have hstep : ∀ b : ℕ, b < 2 →
          (∑ m ∈ Finset.range (n + 2), if m % 2 = b then (Nat.choose (n + 1) m : ZMod 2) else 0) =
          (∑ m ∈ Finset.range (n + 1), if m % 2 = b then (Nat.choose n m : ZMod 2) else 0) +
          (∑ m ∈ Finset.range (n + 1), if m % 2 = 1 - b then (Nat.choose n m : ZMod 2) else 0) := by
        intro b hb
        rw [Finset.sum_range_succ']
        have hsplit :
            ∑ m ∈ Finset.range (n + 1),
              (if (m + 1) % 2 = b then (Nat.choose (n + 1) (m + 1) : ZMod 2) else 0) =
            (∑ m ∈ Finset.range (n + 1),
              if (m + 1) % 2 = b then (Nat.choose n (m + 1) : ZMod 2) else 0) +
            (∑ m ∈ Finset.range (n + 1),
              if (m + 1) % 2 = b then (Nat.choose n m : ZMod 2) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro m _
          split_ifs
          · rw [Nat.choose_succ_succ, Nat.cast_add]; ring
          · simp
        rw [hsplit]
        have h1 :
            (∑ m ∈ Finset.range (n + 1),
              if (m + 1) % 2 = b then (Nat.choose n (m + 1) : ZMod 2) else 0) +
            (if 0 % 2 = b then (Nat.choose (n + 1) 0 : ZMod 2) else 0) =
            ∑ m ∈ Finset.range (n + 1), if m % 2 = b then (Nat.choose n m : ZMod 2) else 0 := by
          rw [Finset.sum_range_succ (f := fun m => if (m + 1) % 2 = b then (Nat.choose n (m + 1) : ZMod 2) else 0)]
          have hzero : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp only [hzero, Nat.cast_zero, ite_self, add_zero]
          rw [Finset.sum_range_succ' (f := fun m => if m % 2 = b then (Nat.choose n m : ZMod 2) else 0)]
          simp
        have h2 :
            (∑ m ∈ Finset.range (n + 1),
              if (m + 1) % 2 = b then (Nat.choose n m : ZMod 2) else 0) =
            ∑ m ∈ Finset.range (n + 1), if m % 2 = 1 - b then (Nat.choose n m : ZMod 2) else 0 := by
          apply Finset.sum_congr rfl
          intro m _
          have hiff : (m + 1) % 2 = b ↔ m % 2 = 1 - b := by omega
          simp only [hiff]
        rw [add_right_comm, h1, h2]
      constructor
      · rw [hstep 0 (by omega), ihE, ihO, add_zero]
      · rw [hstep 1 (by omega), ihO, ihE, add_zero]

private lemma a_zmod_two (n : ℕ) (hn : 2 ≤ n) :
    (a n : ZMod 2) = (n : ZMod 2) := by
  unfold a
  push_cast
  have h51 : (5 : ZMod 2) = 1 := by decide
  rw [h51, one_pow]
  have hbij :
      ∑ k ∈ Finset.range n,
        (Nat.choose n k : ZMod 2) * (1 : ZMod 2) ^ (k * (k + 1)) *
          ((1 : ZMod 2) ^ k - ((n - k : ℕ) : ZMod 2)) ^ (n - k - 1) =
      ∑ m ∈ Finset.Icc 1 n,
        (Nat.choose n m : ZMod 2) * ((1 : ZMod 2) - (m : ZMod 2)) ^ (m - 1) := by
    apply Finset.sum_bij (fun k _ => n - k)
    · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
    · intro a ha b hb hab; rw [Finset.mem_range] at ha hb; omega
    · intro m hm; rw [Finset.mem_Icc] at hm
      exact ⟨n - m, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk
      rw [Finset.mem_range] at hk
      simp only [one_pow, mul_one]
      rw [Nat.choose_symm (by omega : k ≤ n)]
  rw [hbij]
  have hIcc : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc, Finset.sum_insert (by simp)]
  simp only [Nat.choose_one_right, Nat.sub_self, pow_zero, mul_one]
  have htail :
      ∑ m ∈ Finset.Icc 2 n, (Nat.choose n m : ZMod 2) * ((1 : ZMod 2) - (m : ZMod 2)) ^ (m - 1) =
      ∑ m ∈ Finset.Icc 2 n, if m % 2 = 0 then (Nat.choose n m : ZMod 2) else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmcast : (m : ZMod 2) = ((m % 2 : ℕ) : ZMod 2) := by
      rw [ZMod.natCast_eq_natCast_iff]; exact (Nat.mod_modEq m 2).symm
    rw [hmcast]
    by_cases hev : m % 2 = 0
    · simp [hev]
    · have hodd : m % 2 = 1 := by omega
      simp [hodd, zero_pow (by omega : m - 1 ≠ 0)]
  rw [htail]
  have hE := (even_odd_binom_zmod2 n hn).1
  have hr_split : Finset.range (n + 1) = insert 0 (insert 1 (Finset.Icc 2 n)) := by
    ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hr_split, Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at hE
  simp only [Nat.zero_mod, ↓reduceIte, Nat.choose_zero_right, Nat.cast_one,
    show 1 % 2 ≠ 0 by decide, zero_add] at hE
  have hsum1 : (∑ m ∈ Finset.Icc 2 n, if m % 2 = 0 then (Nat.choose n m : ZMod 2) else 0) = 1 := by
    have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    calc (∑ m ∈ Finset.Icc 2 n, if m % 2 = 0 then (Nat.choose n m : ZMod 2) else 0)
        = (1 + 1) + ∑ m ∈ Finset.Icc 2 n, if m % 2 = 0 then (Nat.choose n m : ZMod 2) else 0 := by
          rw [h2, zero_add]
      _ = 1 + (1 + ∑ m ∈ Finset.Icc 2 n, if m % 2 = 0 then (Nat.choose n m : ZMod 2) else 0) := by
          rw [add_assoc]
      _ = 1 + 0 := by rw [hE]
      _ = 1 := add_zero 1
  rw [hsum1]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  calc (1 : ZMod 2) + ((n : ZMod 2) + 1) = ((1 : ZMod 2) + 1) + (n : ZMod 2) := by ring
    _ = (n : ZMod 2) := by rw [h2, zero_add]

private lemma targetMod6_zmod_two (n : ℕ) :
    (targetMod6 n : ZMod 2) = (n : ZMod 2) := by
  have hcast : (n : ZMod 2) = (((n % 6) : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact (Nat.mod_modEq n 6).symm.of_dvd (by decide : 2 ∣ 6)
  rw [hcast]
  unfold targetMod6
  have hlt : n % 6 < 6 := Nat.mod_lt n (by omega)
  interval_cases (n % 6) <;> decide

private def binomMod6 (n : ℕ) (r : ZMod 6) : ZMod 3 :=
  ∑ m ∈ Finset.range (n + 1), if (m : ZMod 6) = r then (Nat.choose n m : ZMod 3) else 0

private lemma binomMod6_succ (n : ℕ) (r : ZMod 6) :
    binomMod6 (n + 1) r = binomMod6 n r + binomMod6 n (r - 1) := by
  unfold binomMod6
  rw [Finset.sum_range_succ']
  have hsplit :
      ∑ m ∈ Finset.range (n + 1),
        (if ((m + 1 : ℕ) : ZMod 6) = r then (Nat.choose (n + 1) (m + 1) : ZMod 3) else 0) =
      (∑ m ∈ Finset.range (n + 1),
        if ((m + 1 : ℕ) : ZMod 6) = r then (Nat.choose n (m + 1) : ZMod 3) else 0) +
      (∑ m ∈ Finset.range (n + 1),
        if ((m + 1 : ℕ) : ZMod 6) = r then (Nat.choose n m : ZMod 3) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs
    · rw [Nat.choose_succ_succ, Nat.cast_add]; ring
    · simp
  rw [hsplit]
  have h1 :
      (∑ m ∈ Finset.range (n + 1),
        if ((m + 1 : ℕ) : ZMod 6) = r then (Nat.choose n (m + 1) : ZMod 3) else 0) +
      (if ((0 : ℕ) : ZMod 6) = r then (Nat.choose (n + 1) 0 : ZMod 3) else 0) =
      ∑ m ∈ Finset.range (n + 1), if (m : ZMod 6) = r then (Nat.choose n m : ZMod 3) else 0 := by
    rw [Finset.sum_range_succ (f := fun m => if ((m + 1 : ℕ) : ZMod 6) = r then (Nat.choose n (m + 1) : ZMod 3) else 0)]
    have hzero : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hzero, Nat.cast_zero, ite_self, add_zero]
    rw [Finset.sum_range_succ' (f := fun m => if (m : ZMod 6) = r then (Nat.choose n m : ZMod 3) else 0)]
    simp
  have h2 :
      (∑ m ∈ Finset.range (n + 1),
        if ((m + 1 : ℕ) : ZMod 6) = r then (Nat.choose n m : ZMod 3) else 0) =
      ∑ m ∈ Finset.range (n + 1), if (m : ZMod 6) = r - 1 then (Nat.choose n m : ZMod 3) else 0 := by
    apply Finset.sum_congr rfl
    intro m _
    have hiff : ((m + 1 : ℕ) : ZMod 6) = r ↔ (m : ZMod 6) = r - 1 := by
      push_cast; constructor <;> intro h
      · rw [← h]; ring
      · rw [h]; ring
    simp only [hiff]
  rw [add_right_comm, h1, h2]

private lemma binomMod6_add_six (n : ℕ) (r : ZMod 6) :
    binomMod6 (n + 6) r = 2 * binomMod6 n r + 2 * binomMod6 n (r - 3) := by
  have h1 := binomMod6_succ (n + 5) r
  have h2 := binomMod6_succ (n + 4) r
  have h3 := binomMod6_succ (n + 4) (r - 1)
  have h4 := binomMod6_succ (n + 3) r
  have h5 := binomMod6_succ (n + 3) (r - 1)
  have h6 := binomMod6_succ (n + 3) (r - 2)
  have h7 := binomMod6_succ (n + 2) r
  have h8 := binomMod6_succ (n + 2) (r - 1)
  have h9 := binomMod6_succ (n + 2) (r - 2)
  have h10 := binomMod6_succ (n + 2) (r - 3)
  have h11 := binomMod6_succ (n + 1) r
  have h12 := binomMod6_succ (n + 1) (r - 1)
  have h13 := binomMod6_succ (n + 1) (r - 2)
  have h14 := binomMod6_succ (n + 1) (r - 3)
  have h15 := binomMod6_succ (n + 1) (r - 4)
  have h16 := binomMod6_succ n r
  have h17 := binomMod6_succ n (r - 1)
  have h18 := binomMod6_succ n (r - 2)
  have h19 := binomMod6_succ n (r - 3)
  have h20 := binomMod6_succ n (r - 4)
  have h21 := binomMod6_succ n (r - 5)
  have hr6 : r - 6 = r := by
    have : (6 : ZMod 6) = 0 := by decide
    rw [this, sub_zero]
  have hs1 : r - 1 - 1 = r - 2 := by ring
  have hs2 : r - 2 - 1 = r - 3 := by ring
  have hs3 : r - 3 - 1 = r - 4 := by ring
  have hs4 : r - 4 - 1 = r - 5 := by ring
  have hs5 : r - 5 - 1 = r - 6 := by ring
  rw [hs1] at h3 h5 h8 h12 h17
  rw [hs2] at h6 h9 h13 h18
  rw [hs3] at h10 h14 h19
  rw [hs4] at h15 h20
  rw [hs5, hr6] at h21
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
  have hc6 : (6 : ZMod 3) = 0 := by decide
  have hc15 : (15 : ZMod 3) = 0 := by decide
  have hc20 : (20 : ZMod 3) = 2 := by decide
  calc
    (binomMod6 n r + binomMod6 n (r - 1) + (binomMod6 n (r - 1) + binomMod6 n (r - 2)) +
      (binomMod6 n (r - 1) + binomMod6 n (r - 2) + (binomMod6 n (r - 2) + binomMod6 n (r - 3))) +
      (binomMod6 n (r - 1) + binomMod6 n (r - 2) + (binomMod6 n (r - 2) + binomMod6 n (r - 3)) +
        (binomMod6 n (r - 2) + binomMod6 n (r - 3) + (binomMod6 n (r - 3) + binomMod6 n (r - 4)))) +
      (binomMod6 n (r - 1) + binomMod6 n (r - 2) + (binomMod6 n (r - 2) + binomMod6 n (r - 3)) +
        (binomMod6 n (r - 2) + binomMod6 n (r - 3) + (binomMod6 n (r - 3) + binomMod6 n (r - 4))) +
        (binomMod6 n (r - 2) + binomMod6 n (r - 3) + (binomMod6 n (r - 3) + binomMod6 n (r - 4)) +
          (binomMod6 n (r - 3) + binomMod6 n (r - 4) + (binomMod6 n (r - 4) + binomMod6 n (r - 5)))))) +
      (binomMod6 n (r - 1) + binomMod6 n (r - 2) + (binomMod6 n (r - 2) + binomMod6 n (r - 3)) +
        (binomMod6 n (r - 2) + binomMod6 n (r - 3) + (binomMod6 n (r - 3) + binomMod6 n (r - 4))) +
        (binomMod6 n (r - 2) + binomMod6 n (r - 3) + (binomMod6 n (r - 3) + binomMod6 n (r - 4)) +
          (binomMod6 n (r - 3) + binomMod6 n (r - 4) + (binomMod6 n (r - 4) + binomMod6 n (r - 5)))) +
        (binomMod6 n (r - 2) + binomMod6 n (r - 3) + (binomMod6 n (r - 3) + binomMod6 n (r - 4)) +
          (binomMod6 n (r - 3) + binomMod6 n (r - 4) + (binomMod6 n (r - 4) + binomMod6 n (r - 5))) +
          (binomMod6 n (r - 3) + binomMod6 n (r - 4) + (binomMod6 n (r - 4) + binomMod6 n (r - 5)) +
            (binomMod6 n (r - 4) + binomMod6 n (r - 5) + (binomMod6 n (r - 5) + binomMod6 n r)))))
        = 2 * binomMod6 n r + 6 * binomMod6 n (r - 1) + 15 * binomMod6 n (r - 2) +
          20 * binomMod6 n (r - 3) + 15 * binomMod6 n (r - 4) + 6 * binomMod6 n (r - 5) := by ring
    _ = 2 * binomMod6 n r + 2 * binomMod6 n (r - 3) := by rw [hc6, hc15, hc20]; ring

private lemma binomMod6_period (n : ℕ) (hn : 6 ≤ n) (r : ZMod 6) :
    binomMod6 (n + 6) r = binomMod6 n r := by
  have hn' : n = (n - 6) + 6 := by omega
  conv_lhs => rw [hn', show (n - 6) + 6 + 6 = ((n - 6) + 6) + 6 by omega]
  rw [binomMod6_add_six ((n - 6) + 6) r, binomMod6_add_six (n - 6) r, binomMod6_add_six (n - 6) (r - 3)]
  have hr6 : r - 3 - 3 = r := by
    have : (6 : ZMod 6) = 0 := by decide
    calc r - 3 - 3 = r - 6 := by ring
      _ = r := by rw [this, sub_zero]
  rw [hr6]
  conv_rhs => rw [hn', binomMod6_add_six (n - 6) r]
  have h8 : (8 : ZMod 3) = 2 := by decide
  calc 2 * (2 * binomMod6 (n - 6) r + 2 * binomMod6 (n - 6) (r - 3)) +
        2 * (2 * binomMod6 (n - 6) (r - 3) + 2 * binomMod6 (n - 6) r)
      = 8 * binomMod6 (n - 6) r + 8 * binomMod6 (n - 6) (r - 3) := by ring
    _ = 2 * binomMod6 (n - 6) r + 2 * binomMod6 (n - 6) (r - 3) := by rw [h8]

private def termF (p2 : ℕ) (r : ZMod 6) : ZMod 3 :=
  ((2 : ZMod 3) ^ ((p2 + 6 - r.val) % 2) - (r.val : ZMod 3)) ^ (1 + r.val % 2)

private lemma zmod3_pow_eq (x : ZMod 3) (m : ℕ) (hm : 1 ≤ m) :
    x ^ m = x ^ (1 + (m - 1) % 2) := by
  have h3 : ∀ y : ZMod 3, y ^ 3 = y := by decide
  have hstep : ∀ q r : ℕ, 1 ≤ r → x ^ (r + 2 * q) = x ^ r := by
    intro q
    induction q with
    | zero => intro r _; simp
    | succ q ih =>
      intro r hr
      have heq : r + 2 * (q + 1) = (r - 1) + 3 + 2 * q := by omega
      have heq2 : r = (r - 1) + 1 := by omega
      calc x ^ (r + 2 * (q + 1)) = x ^ ((r - 1) + 3 + 2 * q) := by rw [heq]
        _ = x ^ (r - 1) * x ^ 3 * x ^ (2 * q) := by rw [pow_add, pow_add]
        _ = x ^ (r - 1) * x * x ^ (2 * q) := by rw [h3 x]
        _ = x ^ ((r - 1) + 1 + 2 * q) := by rw [pow_add, pow_add, pow_one]
        _ = x ^ (r + 2 * q) := by rw [← heq2]
        _ = x ^ r := ih r hr
  have hdecomp : m = (1 + (m - 1) % 2) + 2 * ((m - 1) / 2) := by omega
  conv_lhs => rw [hdecomp]
  exact hstep ((m - 1) / 2) (1 + (m - 1) % 2) (by omega)

private lemma two_pow_zmod3 (m : ℕ) : (2 : ZMod 3) ^ m = (2 : ZMod 3) ^ (m % 2) := by
  have hsq : (2 : ZMod 3) ^ 2 = 1 := by decide
  have hdecomp : m = 2 * (m / 2) + m % 2 := by omega
  conv_lhs => rw [hdecomp, pow_add, pow_mul, hsq, one_pow, one_mul]

private lemma a_zmod_three_eq (n : ℕ) (hn : 2 ≤ n) :
    (a n : ZMod 3) =
      (2 : ZMod 3) ^ (n % 2) + (n : ZMod 3) +
      ∑ r : ZMod 6, termF (n % 2) r *
        (binomMod6 n r - (if r = 0 then 1 else 0) - (if r = 1 then (n : ZMod 3) else 0)) := by
  unfold a
  push_cast
  have h52 : (5 : ZMod 3) = 2 := by decide
  rw [h52]
  have hsq : (2 : ZMod 3) ^ (n ^ 2) = (2 : ZMod 3) ^ (n % 2) := by
    rw [two_pow_zmod3]
    have hp : n ^ 2 % 2 = n % 2 := by
      rw [sq, Nat.mul_mod]
      have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
      interval_cases (n % 2) <;> rfl
    rw [hp]
  rw [hsq]
  have hreidx :
      ∑ k ∈ Finset.range n,
        (Nat.choose n k : ZMod 3) * (2 : ZMod 3) ^ (k * (k + 1)) *
          ((2 : ZMod 3) ^ k - ((n - k : ℕ) : ZMod 3)) ^ (n - k - 1) =
      (n : ZMod 3) +
      ∑ m ∈ Finset.Icc 2 n,
        (Nat.choose n m : ZMod 3) * termF (n % 2) (m : ZMod 6) := by
    have hbij :
        ∑ k ∈ Finset.range n,
          (Nat.choose n k : ZMod 3) * (2 : ZMod 3) ^ (k * (k + 1)) *
            ((2 : ZMod 3) ^ k - ((n - k : ℕ) : ZMod 3)) ^ (n - k - 1) =
        ∑ m ∈ Finset.Icc 1 n,
          (Nat.choose n m : ZMod 3) * ((2 : ZMod 3) ^ (n - m) - (m : ZMod 3)) ^ (m - 1) := by
      apply Finset.sum_bij (fun k _ => n - k)
      · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
      · intro a ha b hb hab; rw [Finset.mem_range] at ha hb; omega
      · intro m hm; rw [Finset.mem_Icc] at hm
        exact ⟨n - m, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k hk
        rw [Finset.mem_range] at hk
        have hev : (k * (k + 1)) % 2 = 0 := by
          have := Nat.even_mul_succ_self k
          rcases this with ⟨t, ht⟩; omega
        rw [two_pow_zmod3 (k * (k + 1)), hev, pow_zero, mul_one, Nat.choose_symm (by omega : k ≤ n)]
        have hsub : n - (n - k) = k := by omega
        rw [hsub]
    rw [hbij]
    have hIcc : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    simp only [Nat.choose_one_right, Nat.sub_self, pow_zero, mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    congr 1
    rw [zmod3_pow_eq _ (m - 1) (by omega), two_pow_zmod3 (n - m)]
    unfold termF
    have hmval : (m : ZMod 6).val = m % 6 := @ZMod.val_natCast 6 m
    rw [hmval]
    have hcast_m : (m : ZMod 3) = ((m % 6 : ℕ) : ZMod 3) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact (Nat.mod_modEq m 6).symm.of_dvd (by decide : 3 ∣ 6)
    have hp1 : (n - m) % 2 = (n % 2 + 6 - m % 6) % 2 := by omega
    have hp2 : (m - 1 - 1) % 2 = m % 6 % 2 := by omega
    rw [hcast_m, hp1, hp2]
  rw [hreidx, ← add_assoc]
  congr 1
  have hgroup :
      ∑ m ∈ Finset.Icc 2 n, (Nat.choose n m : ZMod 3) * termF (n % 2) (m : ZMod 6) =
      ∑ r : ZMod 6, termF (n % 2) r *
        ∑ m ∈ Finset.Icc 2 n, if (m : ZMod 6) = r then (Nat.choose n m : ZMod 3) else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_eq_single (m : ZMod 6)]
    · simp [mul_comm]
    · intro r _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hgroup]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  unfold binomMod6
  have hr_split : Finset.range (n + 1) = insert 0 (insert 1 (Finset.Icc 2 n)) := by
    ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hr_split, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, Nat.choose_zero_right, Nat.cast_one, Nat.choose_one_right]
  have hiff0 : (0 : ZMod 6) = r ↔ r = 0 := eq_comm
  have hiff1 : (1 : ZMod 6) = r ↔ r = 1 := eq_comm
  simp only [hiff0, hiff1]
  ring

private lemma a_zmod_three_period (n : ℕ) (hn : 6 ≤ n) :
    (a (n + 6) : ZMod 3) = (a n : ZMod 3) := by
  rw [a_zmod_three_eq (n + 6) (by omega), a_zmod_three_eq n (by omega)]
  have hm2 : (n + 6) % 2 = n % 2 := by omega
  have hcast3 : ((n + 6 : ℕ) : ZMod 3) = (n : ZMod 3) := by
    rw [Nat.cast_add]; have h6 : ((6 : ℕ) : ZMod 3) = 0 := by decide
    rw [h6, add_zero]
  rw [hm2, hcast3]
  have hsum : ∀ r : ZMod 6, binomMod6 (n + 6) r = binomMod6 n r := fun r => binomMod6_period n hn r
  simp_rw [hsum]

private lemma binomMod6_val (t : Fin 6) (r : Fin 6) :
    binomMod6 t.1 (r.1 : ZMod 6) = if r.1 ≤ t.1 then (Nat.choose t.1 r.1 : ZMod 3) else 0 := by
  unfold binomMod6
  split_ifs with h
  · rw [Finset.sum_eq_single r.1]
    · simp
    · intro m hm hne
      simp only [Finset.mem_range] at hm
      have hne6 : (m : ZMod 6) ≠ (r.1 : ZMod 6) := by
        intro heq
        have := (ZMod.natCast_eq_natCast_iff' m r.1 6).mp heq
        have ht := t.2; have hr := r.2; omega
      simp [hne6]
    · intro hmem; simp only [Finset.mem_range] at hmem; omega
  · apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_range] at hm
    have hne6 : (m : ZMod 6) ≠ (r.1 : ZMod 6) := by
      intro heq
      have := (ZMod.natCast_eq_natCast_iff' m r.1 6).mp heq
      have ht := t.2; have hr := r.2; omega
    simp [hne6]

private lemma a_zmod_three_base : ∀ t : Fin 6, (a (6 + t.1) : ZMod 3) = (targetMod6 (6 + t.1) : ZMod 3) := by
  have hsum6 : ∀ f : ZMod 6 → ZMod 3, (∑ r : ZMod 6, f r) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
    intro f
    have hu : (Finset.univ : Finset (ZMod 6)) = {0, 1, 2, 3, 4, 5} := by decide
    rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  intro t
  rw [a_zmod_three_eq (6 + t.1) (by omega), hsum6]
  have hadd : ∀ r : ZMod 6, binomMod6 (6 + t.1) r = 2 * binomMod6 t.1 r + 2 * binomMod6 t.1 (r - 3) := by
    intro r; rw [Nat.add_comm 6 t.1, binomMod6_add_six]
  simp only [hadd]
  have hb0 : binomMod6 t.1 0 = if 0 ≤ t.1 then (Nat.choose t.1 0 : ZMod 3) else 0 := binomMod6_val t 0
  have hb1 : binomMod6 t.1 1 = if 1 ≤ t.1 then (Nat.choose t.1 1 : ZMod 3) else 0 := binomMod6_val t 1
  have hb2 : binomMod6 t.1 2 = if 2 ≤ t.1 then (Nat.choose t.1 2 : ZMod 3) else 0 := binomMod6_val t 2
  have hb3 : binomMod6 t.1 3 = if 3 ≤ t.1 then (Nat.choose t.1 3 : ZMod 3) else 0 := binomMod6_val t 3
  have hb4 : binomMod6 t.1 4 = if 4 ≤ t.1 then (Nat.choose t.1 4 : ZMod 3) else 0 := binomMod6_val t 4
  have hb5 : binomMod6 t.1 5 = if 5 ≤ t.1 then (Nat.choose t.1 5 : ZMod 3) else 0 := binomMod6_val t 5
  have hs0 : (0 : ZMod 6) - 3 = 3 := by decide
  have hs1 : (1 : ZMod 6) - 3 = 4 := by decide
  have hs2 : (2 : ZMod 6) - 3 = 5 := by decide
  have hs3 : (3 : ZMod 6) - 3 = 0 := by decide
  have hs4 : (4 : ZMod 6) - 3 = 1 := by decide
  have hs5 : (5 : ZMod 6) - 3 = 2 := by decide
  rw [hs0, hs1, hs2, hs3, hs4, hs5, hb0, hb1, hb2, hb3, hb4, hb5]
  fin_cases t <;> decide

private lemma a_zmod_three_target (n : ℕ) (hn : 6 ≤ n) :
    (a n : ZMod 3) = (targetMod6 n : ZMod 3) := by
  have hmod : ∀ q : ℕ, ∀ t : Fin 6, (a (6 + t.1 + 6 * q) : ZMod 3) = (targetMod6 (6 + t.1) : ZMod 3) := by
    intro q
    induction q with
    | zero => intro t; simpa using a_zmod_three_base t
    | succ q ih =>
      intro t
      have heq : 6 + t.1 + 6 * (q + 1) = (6 + t.1 + 6 * q) + 6 := by ring
      rw [heq, a_zmod_three_period _ (by omega)]
      exact ih t
  have hdecomp : n = 6 + (n - 6) % 6 + 6 * ((n - 6) / 6) := by omega
  have htg : targetMod6 n = targetMod6 (6 + (n - 6) % 6) := by
    unfold targetMod6
    have : n % 6 = (6 + (n - 6) % 6) % 6 := by omega
    rw [this]
  rw [htg]
  conv_lhs => rw [hdecomp]
  exact hmod ((n - 6) / 6) ⟨(n - 6) % 6, Nat.mod_lt _ (by omega)⟩

end OeisA386658Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a386658.main := by
  intro n hn
  have h2 : OMA.S_oeis_a386658.a n ≡ OMA.S_oeis_a386658.targetMod6 n [ZMOD ((2 : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    rw [OeisA386658Proof.a_zmod_two n (by omega), OeisA386658Proof.targetMod6_zmod_two n]
  have h3 : OMA.S_oeis_a386658.a n ≡ OMA.S_oeis_a386658.targetMod6 n [ZMOD ((3 : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    exact OeisA386658Proof.a_zmod_three_target n hn
  rw [Int.modEq_iff_dvd] at h2 h3 ⊢
  have hcop : IsCoprime (2 : ℤ) (3 : ℤ) := ⟨-1, 1, by norm_num⟩
  have h6 := hcop.mul_dvd h2 h3
  simpa using h6
