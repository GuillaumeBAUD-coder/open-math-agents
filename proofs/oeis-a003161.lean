import OMAStatements.S_oeis_a003161

-- Credit: Daniel Whorlow (@draonbioetl)
-- Proof of Peter Bala's 2023 supercongruence conjecture (OEIS A003161):
--   For prime p >= 5 and positive integers n, k,
--   b(n * p^k) ≡ b(n * p^(k-1)) (mod p^(3*k)),
-- where a(m) = sum_{j=0}^{m/2} (C(m, j) - C(m, j-1))^3 and b(n) = a(2*n - 1).
--
-- Proof outline:
-- 1. WZ telescoping establishes the exact identity
--      2 * b(n) = C(2n - 1, n - 1) * (3 * A(n) - C(2n - 1, n - 1)^2),
--    where A(n) = sum_{k=0}^{n-1} C(n + k - 1, k)^2.
-- 2. A short elementary pairing argument proves the general Jacobsthal/Kazandzidis
--    congruence: for prime p >= 5, if p^t | p*b and p^e | (p*(a-b))*(p*a) with 1 <= t <= e,
--    then C(p*a, p*b) ≡ C(a, b) (mod p^(e+t)). This yields both
--      C(2*n*p^k - 1, n*p^k - 1) ≡ C(2*n*p^(k-1) - 1, n*p^(k-1) - 1) (mod p^(3*k))
--    and the termwise congruence for multiples of p in A(n*p^k) - A(n*p^(k-1)).
-- 3. For indices not divisible by p in A(n*p^k), each p^k-block is divisible by p^(3*k)
--    via an elementary downward induction on k using the vanishing of sum u^(-2) over units.

open OMA.S_oeis_a003161

namespace OMA_A003161

open Finset

/-! ### Part 1: Exact combinatorial identity via WZ telescoping -/

private def A_nat (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (Nat.choose (n - 1 + k) k) ^ 2

private lemma succ_mul_choose_eq (n k : ℕ) :
    (n + 1) * Nat.choose n k = (k + 1) * Nat.choose (n + 1) (k + 1) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Nat.choose_eq_zero_of_lt (show 1 < k + 2 by omega)]
  | succ n ih =>
    cases k with
    | zero => simp [Nat.choose_one_right]
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      have hpas1 : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
        Nat.choose_succ_succ n k
      have hpas2 : Nat.choose (n + 1 + 1) (k + 1 + 1) =
          Nat.choose (n + 1) (k + 1) + Nat.choose (n + 1) (k + 1 + 1) :=
        Nat.choose_succ_succ (n + 1) (k + 1)
      calc (n + 1 + 1) * Nat.choose (n + 1) (k + 1)
          = (n + 1) * Nat.choose n k + (n + 1) * Nat.choose n (k + 1) +
            Nat.choose (n + 1) (k + 1) := by rw [hpas1]; ring
        _ = (k + 1) * Nat.choose (n + 1) (k + 1) +
            (k + 1 + 1) * Nat.choose (n + 1) (k + 1 + 1) +
            Nat.choose (n + 1) (k + 1) := by rw [h1, h2]
        _ = (k + 1 + 1) * Nat.choose (n + 1 + 1) (k + 1 + 1) := by rw [hpas2]; ring

private lemma mul_add_div_right {a b c : ℕ} (hc : 0 < c) : (a * c + b) / c = a + b / c := by
  rw [mul_comm, Nat.mul_add_div hc]

private lemma isUnit_prod_of_mem {R : Type*} [CommMonoid R] {α : Type*}
    (s : Finset α) (f : α → R) (h : ∀ x ∈ s, IsUnit (f x)) :
    IsUnit (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private lemma choose_mul_upper (m k : ℕ) (hm : 1 ≤ m) :
    (m : ℚ) * (Nat.choose (m + k) k : ℚ) = ((m + k : ℚ)) * (Nat.choose (m - 1 + k) k : ℚ) := by
  have h1 : m * Nat.choose (m + k) k = (m + k) * Nat.choose (m - 1 + k) k := by
    have hs : m + k = (m - 1 + k) + 1 := by omega
    have hle1 : k ≤ m + k := Nat.le_add_left k m
    have hle2 : k ≤ m - 1 + k := Nat.le_add_left k (m - 1)
    have hsym1 : Nat.choose (m + k) k = Nat.choose (m + k) m := by
      rw [← Nat.choose_symm hle1, Nat.add_sub_cancel]
    have hsym2 : Nat.choose (m - 1 + k) k = Nat.choose (m - 1 + k) (m - 1) := by
      rw [← Nat.choose_symm hle2, Nat.add_sub_cancel]
    rw [hsym1, hsym2, hs]
    have h2 := succ_mul_choose_eq (m - 1 + k) (m - 1)
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1] at h2
    linarith
  exact_mod_cast h1

private lemma choose_mul_lower (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    (m : ℚ) * (Nat.choose (m - 1 + k) (k - 1) : ℚ) = (k : ℚ) * (Nat.choose (m - 1 + k) k : ℚ) := by
  have h1 : m * Nat.choose (m - 1 + k) (k - 1) = k * Nat.choose (m - 1 + k) k := by
    have h2 := Nat.choose_succ_right_eq (m - 1 + k) (k - 1)
    have hk1 : k - 1 + 1 = k := by omega
    have hsub : m - 1 + k - (k - 1) = m := by omega
    rw [hk1, hsub] at h2
    linarith
  exact_mod_cast h1

private lemma choose_two_mul_succ (n : ℕ) :
    ((n + 1 : ℚ)) * (Nat.choose (2 * n + 1) n : ℚ) =
      (2 * (n : ℚ) + 1) * (Nat.choose (2 * n) n : ℚ) := by
  have h1 : (n + 1) * Nat.choose (2 * n + 1) n = (2 * n + 1) * Nat.choose (2 * n) n := by
    have h2 := succ_mul_choose_eq (2 * n) n
    have hsym : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
      rw [← Nat.choose_symm (show n ≤ 2 * n + 1 by omega)]
      congr 1; omega
    rw [hsym] at h2
    linarith
  exact_mod_cast h1

private lemma choose_two_mul_pred (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
  have h1 : 2 * Nat.choose (2 * n - 1) (n - 1) = Nat.choose (2 * n) n := by
    have h2 := succ_mul_choose_eq (2 * n - 1) (n - 1)
    have h2n : 2 * n - 1 + 1 = 2 * n := by omega
    have hn1 : n - 1 + 1 = n := by omega
    rw [h2n, hn1] at h2
    have h3 : n * (2 * Nat.choose (2 * n - 1) (n - 1)) = n * Nat.choose (2 * n) n := by linarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  exact_mod_cast h1

private def GA (n k : ℕ) : ℚ :=
  if k = 0 then 0
  else (3 * (n : ℚ) + 2 * (k : ℚ)) * (Nat.choose (n - 1 + k) (k - 1) : ℚ) ^ 2

private lemma A_wz_step (n k : ℕ) (hn : 1 ≤ n) :
    2 * (2 * (n : ℚ) + 1) * (Nat.choose (n + k) k : ℚ) ^ 2 -
      (n : ℚ) * (Nat.choose (n - 1 + k) k : ℚ) ^ 2 =
      GA n (k + 1) - GA n k := by
  by_cases hk : k = 0
  · subst hk
    simp only [GA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_zero,
      Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one, sub_zero]
    have h1 : Nat.choose (n - 1 + 1) 0 = 1 := Nat.choose_zero_right _
    rw [h1]
    push_cast; ring
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    have hn0 : (n : ℚ) ≠ 0 := by positivity
    simp only [GA, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, hk,
      Nat.add_sub_cancel]
    have hnm : n - 1 + (k + 1) = n + k := by omega
    rw [hnm]
    have hu := choose_mul_upper n k hn
    have hl := choose_mul_lower n k hn hk1
    have hu' : (Nat.choose (n + k) k : ℚ) = ((n : ℚ) + k) / n * (Nat.choose (n - 1 + k) k : ℚ) := by
      field_simp; linarith
    have hl' : (Nat.choose (n - 1 + k) (k - 1) : ℚ) = (k : ℚ) / n * (Nat.choose (n - 1 + k) k : ℚ) := by
      field_simp; linarith
    rw [hu', hl']
    push_cast
    field_simp
    ring

private lemma A_rec (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * (n : ℚ) + 1) * (A_nat (n + 1) : ℚ) - (n : ℚ) * (A_nat n : ℚ) =
      (21 * (n : ℚ) + 8) / 4 * (Nat.choose (2 * n) n : ℚ) ^ 2 := by
  have hA1 : (A_nat (n + 1) : ℚ) =
      (∑ k ∈ Finset.range n, (Nat.choose (n + k) k : ℚ) ^ 2) + (Nat.choose (2 * n) n : ℚ) ^ 2 := by
    simp only [A_nat, Nat.add_sub_cancel, Finset.sum_range_succ, Nat.cast_add, Nat.cast_sum,
      Nat.cast_pow]
    rw [show n + n = 2 * n by omega]
  have hA0 : (A_nat n : ℚ) = ∑ k ∈ Finset.range n, (Nat.choose (n - 1 + k) k : ℚ) ^ 2 := by
    simp only [A_nat, Nat.cast_sum, Nat.cast_pow]
  rw [hA1, hA0]
  have hsum : ∑ k ∈ Finset.range n,
      (2 * (2 * (n : ℚ) + 1) * (Nat.choose (n + k) k : ℚ) ^ 2 -
        (n : ℚ) * (Nat.choose (n - 1 + k) k : ℚ) ^ 2) =
      GA n n - GA n 0 := by
    calc ∑ k ∈ Finset.range n,
          (2 * (2 * (n : ℚ) + 1) * (Nat.choose (n + k) k : ℚ) ^ 2 -
            (n : ℚ) * (Nat.choose (n - 1 + k) k : ℚ) ^ 2)
        = ∑ k ∈ Finset.range n, (GA n (k + 1) - GA n k) :=
          Finset.sum_congr rfl fun k _ => A_wz_step n k hn
      _ = GA n n - GA n 0 := Finset.sum_range_sub (GA n) n
  have hsplit :
      2 * (2 * (n : ℚ) + 1) * ((∑ k ∈ Finset.range n, (Nat.choose (n + k) k : ℚ) ^ 2) +
          (Nat.choose (2 * n) n : ℚ) ^ 2) -
        (n : ℚ) * (∑ k ∈ Finset.range n, (Nat.choose (n - 1 + k) k : ℚ) ^ 2) =
      (∑ k ∈ Finset.range n,
        (2 * (2 * (n : ℚ) + 1) * (Nat.choose (n + k) k : ℚ) ^ 2 -
          (n : ℚ) * (Nat.choose (n - 1 + k) k : ℚ) ^ 2)) +
      2 * (2 * (n : ℚ) + 1) * (Nat.choose (2 * n) n : ℚ) ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  rw [hsplit, hsum]
  have hGA0 : GA n 0 = 0 := by simp [GA]
  have hGAn : GA n n = 5 * (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ) ^ 2 := by
    have hn0 : n ≠ 0 := by omega
    simp only [GA, hn0, ↓reduceIte]
    have h2n : n - 1 + n = 2 * n - 1 := by omega
    rw [h2n]; ring
  rw [hGA0, hGAn, sub_zero]
  have hp := choose_two_mul_pred n hn
  have hp' : (Nat.choose (2 * n - 1) (n - 1) : ℚ) = (Nat.choose (2 * n) n : ℚ) / 2 := by linarith
  rw [hp']
  ring

private def R_rat (n : ℕ) : ℚ :=
  (Nat.choose (2 * n - 1) (n - 1) : ℚ) *
    (3 * (A_nat n : ℚ) - (Nat.choose (2 * n - 1) (n - 1) : ℚ) ^ 2) / 2

private lemma R_rat_rec (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ)) * R_rat (n + 1) - (n : ℚ) * R_rat n =
      (7 * (n : ℚ) ^ 2 + 8 * n + 2) / (2 * (n + 1 : ℚ) ^ 2) * (Nat.choose (2 * n) n : ℚ) ^ 3 := by
  simp only [R_rat, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.add_sub_cancel]
  have h1 := choose_two_mul_succ n
  have h2 := choose_two_mul_pred n hn
  have hA := A_rec n hn
  have hn1 : (n + 1 : ℚ) ≠ 0 := by positivity
  have hc1 : (Nat.choose (2 * n + 1) n : ℚ) = (2 * n + 1) / (n + 1) * (Nat.choose (2 * n) n : ℚ) := by
    field_simp; linarith
  have hc0 : (Nat.choose (2 * n - 1) (n - 1) : ℚ) = (Nat.choose (2 * n) n : ℚ) / 2 := by linarith
  rw [hc1, hc0]
  have hA' : 2 * (2 * (n : ℚ) + 1) * (A_nat (n + 1) : ℚ) =
      (n : ℚ) * (A_nat n : ℚ) + (21 * (n : ℚ) + 8) / 4 * (Nat.choose (2 * n) n : ℚ) ^ 2 := by
    linarith
  have hcalc :
      (n + 1 : ℚ) * ((2 * n + 1) / (n + 1) * (Nat.choose (2 * n) n : ℚ) *
        (3 * (A_nat (n + 1) : ℚ) - ((2 * n + 1) / (n + 1) * (Nat.choose (2 * n) n : ℚ)) ^ 2) / 2) -
      (n : ℚ) * ((Nat.choose (2 * n) n : ℚ) / 2 *
        (3 * (A_nat n : ℚ) - ((Nat.choose (2 * n) n : ℚ) / 2) ^ 2) / 2) =
      (3 / 4) * (Nat.choose (2 * n) n : ℚ) *
        (2 * (2 * (n : ℚ) + 1) * (A_nat (n + 1) : ℚ) - (n : ℚ) * (A_nat n : ℚ)) -
      ((2 * (n : ℚ) + 1) ^ 3 / (2 * (n + 1) ^ 2) - (n : ℚ) / 16) * (Nat.choose (2 * n) n : ℚ) ^ 3 := by
    field_simp; ring
  rw [hcalc, hA]
  field_simp; ring

private lemma diff_choose_eq (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) :
    ((Nat.choose (2 * n - 1) k : ℚ) -
        (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℚ))) =
      ((n : ℚ) - k) / n * (Nat.choose (2 * n) k : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  by_cases hk0 : k = 0
  · subst hk0; simp [hn0]
  · simp only [hk0, ↓reduceIte]
    have hpas : Nat.choose (2 * n) k = Nat.choose (2 * n - 1) (k - 1) + Nat.choose (2 * n - 1) k := by
      have h2n : 2 * n = (2 * n - 1) + 1 := by omega
      have hk1 : k = (k - 1) + 1 := by omega
      conv_lhs => rw [h2n, hk1, Nat.choose_succ_succ]
      rw [Nat.succ_eq_add_one, ← hk1]
    have habs : k * Nat.choose (2 * n) k = 2 * n * Nat.choose (2 * n - 1) (k - 1) := by
      have h2 := succ_mul_choose_eq (2 * n - 1) (k - 1)
      have h2n : 2 * n - 1 + 1 = 2 * n := by omega
      have hk1 : k - 1 + 1 = k := by omega
      rw [h2n, hk1] at h2
      linarith
    have hpasQ : (Nat.choose (2 * n) k : ℚ) =
        (Nat.choose (2 * n - 1) (k - 1) : ℚ) + (Nat.choose (2 * n - 1) k : ℚ) := by exact_mod_cast hpas
    have habsQ : (k : ℚ) * (Nat.choose (2 * n) k : ℚ) =
        2 * (n : ℚ) * (Nat.choose (2 * n - 1) (k - 1) : ℚ) := by exact_mod_cast habs
    field_simp
    linear_combination -(n : ℚ) * hpasQ + habsQ

private def Fc (n j : ℕ) : ℚ :=
  ((j : ℚ) ^ 3 / (n : ℚ) ^ 2) * (Nat.choose (2 * n) (n - j) : ℚ) ^ 3

private lemma mul_b_eq_sum_Fc (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) * (b n : ℚ) = ∑ j ∈ Finset.Icc 1 n, Fc n j := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hdiv : (2 * n - 1) / 2 + 1 = n := by omega
  have hb : (b n : ℚ) = ∑ k ∈ Finset.range n,
      (((n : ℚ) - k) / n * (Nat.choose (2 * n) k : ℚ)) ^ 3 := by
    simp only [b, a, hdiv, Int.cast_sum, Int.cast_pow, Int.cast_sub]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have h1 := diff_choose_eq n k hn hk
    by_cases hk0 : k = 0
    · simp only [hk0, ↓reduceIte, Int.cast_zero, Int.cast_natCast] at h1 ⊢
      rw [h1]
    · simp only [hk0, ↓reduceIte, Int.cast_natCast] at h1 ⊢
      rw [h1]
  rw [hb, Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc]; omega
  · intro k1 hk1 k2 hk2 heq
    rw [Finset.mem_range] at hk1 hk2; omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact ⟨n - j, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rw [Finset.mem_range] at hk
    simp only [Fc, show n - (n - k) = k by omega]
    have hcast : ((n - k : ℕ) : ℚ) = (n : ℚ) - (k : ℚ) := by
      rw [Nat.cast_sub (by omega)]
    rw [hcast]
    field_simp

private def Q_WZ (n j : ℚ) : ℚ :=
  (-7 * n ^ 5 - 15 * n ^ 4 - 10 * n ^ 3 - 2 * n ^ 2) +
    (21 * n ^ 4 + 24 * n ^ 3 + 6 * n ^ 2) * j +
    (-21 * n ^ 4 - 24 * n ^ 3 + 3 * n) * j ^ 2 +
    (-12 * n ^ 2 - 6 * n + 1) * j ^ 3 +
    (6 * n ^ 2 + 3 * n - 3) * j ^ 4 +
    3 * j ^ 5 - j ^ 6

private def Gb (n j : ℕ) : ℚ :=
  Q_WZ (n : ℚ) (j : ℚ) / (2 * (n : ℚ) ^ 2 * ((n + 1 - j : ℚ) ^ 3)) *
    (Nat.choose (2 * n) (n - j) : ℚ) ^ 3

private lemma choose_2n_step_n (n j : ℕ) (hj : j ≤ n) :
    ((n + 1 - j : ℚ) * (n + 1 + j : ℚ)) * (Nat.choose (2 * (n + 1)) (n + 1 - j) : ℚ) =
      (2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1) * (Nat.choose (2 * n) (n - j) : ℚ) := by
  have h1 : (n + 1 - j) * (n + 1 + j) * Nat.choose (2 * n + 2) (n + 1 - j) =
      (2 * n + 2) * (2 * n + 1) * Nat.choose (2 * n) (n - j) := by
    have ha := succ_mul_choose_eq (2 * n + 1) (n - j)
    have hnj : n - j + 1 = n + 1 - j := by omega
    rw [hnj] at ha
    have hb := succ_mul_choose_eq (2 * n) (n + j)
    have hsym1 : Nat.choose (2 * n + 1) (n + j + 1) = Nat.choose (2 * n + 1) (n - j) := by
      rw [← Nat.choose_symm (show n - j ≤ 2 * n + 1 by omega)]
      congr 1; omega
    have hsym2 : Nat.choose (2 * n) (n + j) = Nat.choose (2 * n) (n - j) := by
      rw [← Nat.choose_symm (show n - j ≤ 2 * n by omega)]
      congr 1; omega
    rw [hsym1, hsym2] at hb
    calc (n + 1 - j) * (n + 1 + j) * Nat.choose (2 * n + 2) (n + 1 - j)
        = (n + 1 + j) * ((n + 1 - j) * Nat.choose (2 * n + 2) (n + 1 - j)) := by ring
      _ = (n + 1 + j) * ((2 * n + 2) * Nat.choose (2 * n + 1) (n - j)) := by rw [← ha]
      _ = (2 * n + 2) * ((n + j + 1) * Nat.choose (2 * n + 1) (n - j)) := by ring
      _ = (2 * n + 2) * ((2 * n + 1) * Nat.choose (2 * n) (n - j)) := by rw [← hb]
      _ = (2 * n + 2) * (2 * n + 1) * Nat.choose (2 * n) (n - j) := by ring
  have hcast : ((n + 1 - j : ℕ) : ℚ) = (n : ℚ) + 1 - (j : ℚ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((n + 1 - j : ℕ) : ℚ) * ((n + 1 + j : ℕ) : ℚ) *
      (Nat.choose (2 * (n + 1)) (n + 1 - j) : ℚ) =
      ((2 * n + 2 : ℕ) : ℚ) * ((2 * n + 1 : ℕ) : ℚ) * (Nat.choose (2 * n) (n - j) : ℚ) := by
    exact_mod_cast h1
  rw [hcast] at h2
  push_cast at h2
  linarith

private lemma choose_2n_step_j (n j : ℕ) (hj : j < n) :
    ((n + 1 + j : ℚ)) * (Nat.choose (2 * n) (n - (j + 1)) : ℚ) =
      ((n : ℚ) - j) * (Nat.choose (2 * n) (n - j) : ℚ) := by
  have h1 : (n + 1 + j) * Nat.choose (2 * n) (n - (j + 1)) =
      (n - j) * Nat.choose (2 * n) (n - j) := by
    have h2 := Nat.choose_succ_right_eq (2 * n) (n - (j + 1))
    have hsub1 : n - (j + 1) + 1 = n - j := by omega
    have hsub2 : 2 * n - (n - (j + 1)) = n + 1 + j := by omega
    rw [hsub1, hsub2] at h2
    linarith
  have hcast : ((n - j : ℕ) : ℚ) = (n : ℚ) - (j : ℚ) := by rw [Nat.cast_sub (by omega)]
  have h2 : ((n + 1 + j : ℕ) : ℚ) * (Nat.choose (2 * n) (n - (j + 1)) : ℚ) =
      ((n - j : ℕ) : ℚ) * (Nat.choose (2 * n) (n - j) : ℚ) := by exact_mod_cast h1
  rw [hcast] at h2
  push_cast at h2
  linarith

private lemma b_wz_step (n j : ℕ) (hn : 1 ≤ n) (hj : j < n) :
    Gb n (j + 1) - Gb n j = Fc (n + 1) j - Fc n j := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hnj : (n : ℚ) - j ≠ 0 := by
    have : (j : ℚ) < (n : ℚ) := by exact_mod_cast hj
    linarith
  have hn1j : (n : ℚ) + 1 - j ≠ 0 := by
    have : (j : ℚ) < (n : ℚ) := by exact_mod_cast hj
    linarith
  have hnp1j : (n : ℚ) + 1 + j ≠ 0 := by positivity
  have hs1 := choose_2n_step_n n j (by omega)
  have hs2 := choose_2n_step_j n j hj
  have hc_n : (Nat.choose (2 * (n + 1)) (n + 1 - j) : ℚ) =
      (2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1) / (((n : ℚ) + 1 - j) * ((n : ℚ) + 1 + j)) *
        (Nat.choose (2 * n) (n - j) : ℚ) := by
    field_simp; linarith
  have hc_j : (Nat.choose (2 * n) (n - (j + 1)) : ℚ) =
      ((n : ℚ) - j) / ((n : ℚ) + 1 + j) * (Nat.choose (2 * n) (n - j) : ℚ) := by
    field_simp; linarith
  simp only [Gb, Fc]
  rw [hc_n, hc_j]
  simp only [Q_WZ]
  push_cast
  have hsub : (n : ℚ) + 1 - ((j : ℚ) + 1) = (n : ℚ) - j := by ring
  rw [hsub]
  field_simp
  ring

private lemma b_rec (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ)) * (b (n + 1) : ℚ) - (n : ℚ) * (b n : ℚ) =
      (7 * (n : ℚ) ^ 2 + 8 * n + 2) / (2 * (n + 1 : ℚ) ^ 2) * (Nat.choose (2 * n) n : ℚ) ^ 3 := by
  have hb1 := mul_b_eq_sum_Fc (n + 1) (by omega)
  push_cast at hb1
  rw [hb1, mul_b_eq_sum_Fc n hn]
  have hIcc_np1 : Finset.Icc 1 (n + 1) = insert (n + 1) (insert n (Finset.Ico 1 n)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  have hIcc_n : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hIcc_np1, hIcc_n]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp)]
  have hsub_sum :
      (∑ j ∈ Finset.Ico 1 n, Fc (n + 1) j) - (∑ j ∈ Finset.Ico 1 n, Fc n j) =
      Gb n n - Gb n 1 := by
    rw [← Finset.sum_sub_distrib]
    have hcongr : ∑ j ∈ Finset.Ico 1 n, (Fc (n + 1) j - Fc n j) =
        ∑ j ∈ Finset.Ico 1 n, (Gb n (j + 1) - Gb n j) :=
      Finset.sum_congr rfl fun j hj => (b_wz_step n j hn (Finset.mem_Ico.mp hj).2).symm
    rw [hcongr]
    exact Finset.sum_Ico_sub (Gb n) hn
  have hcomb :
      (Fc (n + 1) (n + 1) + (Fc (n + 1) n + ∑ j ∈ Finset.Ico 1 n, Fc (n + 1) j)) -
        (Fc n n + ∑ j ∈ Finset.Ico 1 n, Fc n j) =
      (Gb n n + Fc (n + 1) n - Fc n n + Fc (n + 1) (n + 1)) - Gb n 1 := by
    linarith
  rw [hcomb]
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h_end : Gb n n + Fc (n + 1) n - Fc n n + Fc (n + 1) (n + 1) = 0 := by
    simp only [Gb, Fc, Q_WZ, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one,
      show n + 1 - n = 1 by omega, Nat.choose_one_right]
    push_cast
    field_simp
    ring
  have h_start : -Gb n 1 =
      (7 * (n : ℚ) ^ 2 + 8 * n + 2) / (2 * (n + 1 : ℚ) ^ 2) * (Nat.choose (2 * n) n : ℚ) ^ 3 := by
    simp only [Gb, Q_WZ]
    have hc : (n + 1 : ℚ) * (Nat.choose (2 * n) (n - 1) : ℚ) =
        (n : ℚ) * (Nat.choose (2 * n) n : ℚ) := by
      have h := choose_2n_step_j n 0 (by omega)
      simpa using h
    have hc' : (Nat.choose (2 * n) (n - 1) : ℚ) =
        (n : ℚ) / (n + 1 : ℚ) * (Nat.choose (2 * n) n : ℚ) := by
      field_simp; linarith
    rw [hc']
    push_cast
    rw [show (n : ℚ) + 1 - 1 = (n : ℚ) by ring]
    field_simp
    ring
  rw [h_end, zero_sub]
  exact h_start

private lemma b_eq_R_rat (n : ℕ) (hn : 1 ≤ n) : (b n : ℚ) = R_rat n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hb1 : b 1 = 1 := by decide
    have hA1 : A_nat 1 = 1 := by decide
    simp only [R_rat, hb1, hA1]
    norm_num
  | succ n hn ih =>
    have hr1 := b_rec n hn
    have hr2 := R_rat_rec n hn
    have hn1 : (n + 1 : ℚ) ≠ 0 := by positivity
    rw [ih] at hr1
    have hmul : (n + 1 : ℚ) * (b (n + 1) : ℚ) = (n + 1 : ℚ) * R_rat (n + 1) := by linarith
    exact mul_left_cancel₀ hn1 hmul

private lemma two_mul_b_eq (n : ℕ) (hn : 1 ≤ n) :
    2 * b n = (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
      (3 * (A_nat n : ℤ) - (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2) := by
  have hq := b_eq_R_rat n hn
  simp only [R_rat] at hq
  have hq2 : (2 : ℚ) * (b n : ℚ) =
      (Nat.choose (2 * n - 1) (n - 1) : ℚ) *
        (3 * (A_nat n : ℚ) - (Nat.choose (2 * n - 1) (n - 1) : ℚ) ^ 2) := by linarith
  exact_mod_cast hq2

/-! ### Part 2: Elementary unit-sum and general Jacobsthal/Kazandzidis lemmas -/

private lemma coprime_of_not_dvd_prime {p u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    Nat.Coprime u p :=
  (hp.coprime_iff_not_dvd.mpr hu).symm

private lemma isUnit_zmod_pow {p s u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    IsUnit (u : ZMod (p ^ s)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (coprime_of_not_dvd_prime hp hu).pow_right s

private lemma zmod_pow_mul_inv {p s u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    (u : ZMod (p ^ s)) * (u : ZMod (p ^ s))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_zmod_pow hp hu)

private lemma sum_inv_sq_units {p s : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  set N := p ^ s
  set S := (Finset.range N).filter (fun u => ¬ p ∣ u)
  have hNpos : 0 < N := pow_pos hp.pos s
  have h2nd : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
  have h3nd : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
  have h2u : IsUnit (2 : ZMod N) := by
    change IsUnit ((2 : ℕ) : ZMod N); exact isUnit_zmod_pow hp h2nd
  have h3u : IsUnit (3 : ZMod N) := by
    change IsUnit ((3 : ℕ) : ZMod N); exact isUnit_zmod_pow hp h3nd
  have hbij : ∑ u ∈ S, (((2 * u % N : ℕ) : ZMod N)⁻¹) ^ 2 = ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    refine Finset.sum_bij (fun u _ => 2 * u % N) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu ⊢
      refine ⟨Nat.mod_lt _ hNpos, ?_⟩
      intro hd
      have hpN : p ∣ N := dvd_pow_self p (by omega)
      have h2u_dvd : p ∣ 2 * u := by
        have hmod := Nat.div_add_mod (2 * u) N
        have : p ∣ N * (2 * u / N) + 2 * u % N := dvd_add (dvd_mul_of_dvd_left hpN _) hd
        rwa [hmod] at this
      rcases hp.dvd_mul.mp h2u_dvd with h2 | hu'
      · exact h2nd h2
      · exact hu.2 hu'
    · intro u1 hu1 u2 hu2 heq
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu1 hu2
      have hcast : ((2 * u1 % N : ℕ) : ZMod N) = ((2 * u2 % N : ℕ) : ZMod N) := by rw [heq]
      simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat] at hcast
      have hcancel := h2u.mul_left_cancel hcast
      have hval := congrArg ZMod.val hcancel
      rwa [ZMod.val_natCast_of_lt hu1.1, ZMod.val_natCast_of_lt hu2.1] at hval
    · intro v hv
      simp only [S, Finset.mem_filter, Finset.mem_range] at hv
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      set u := ((2 : ZMod N)⁻¹ * (v : ZMod N)).val
      have hu_lt : u < N := ZMod.val_lt _
      have hu_cast : (u : ZMod N) = (2 : ZMod N)⁻¹ * (v : ZMod N) := ZMod.natCast_zmod_val _
      have h2u_eq : ((2 * u % N : ℕ) : ZMod N) = (v : ZMod N) := by
        rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, hu_cast, ← mul_assoc,
          ZMod.mul_inv_of_unit _ h2u, one_mul]
      have h2u_nat : 2 * u % N = v := by
        have hval := congrArg ZMod.val h2u_eq
        rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ hNpos), ZMod.val_natCast_of_lt hv.1] at hval
      refine ⟨u, ?_, h2u_nat⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨hu_lt, fun hdu => hv.2 ?_⟩
      have hpN : p ∣ N := dvd_pow_self p (by omega)
      have hmod := Nat.div_add_mod (2 * u) N
      have h1 : p ∣ 2 * u := dvd_mul_of_dvd_right hdu 2
      rw [← h2u_nat]
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hpN _)).mp (hmod.symm ▸ h1)
    · intro _ _; rfl
  have h4 : ∑ u ∈ S, (((2 * u % N : ℕ) : ZMod N)⁻¹) ^ 2 =
      ((2 : ZMod N)⁻¹ ^ 2) * ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
    have hu_u : IsUnit (u : ZMod N) := isUnit_zmod_pow hp (Finset.mem_filter.mp hu).2
    have hmul_inv : ((2 : ZMod N) * (u : ZMod N))⁻¹ = (2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹ := by
      have h1 : ((2 : ZMod N) * (u : ZMod N)) * ((2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹) = 1 := by
        calc ((2 : ZMod N) * (u : ZMod N)) * ((2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹)
            = ((2 : ZMod N) * (2 : ZMod N)⁻¹) * ((u : ZMod N) * (u : ZMod N)⁻¹) := by ring
          _ = 1 := by rw [ZMod.mul_inv_of_unit _ h2u, ZMod.mul_inv_of_unit _ hu_u, mul_one]
      exact (h2u.mul hu_u).mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ (h2u.mul hu_u), h1])
    rw [hmul_inv, mul_pow]
  rw [h4] at hbij
  have h4_eq : (4 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) =
      ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    have h2sq : (4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2) = 1 := by
      calc (4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2)
          = ((2 : ZMod N) * (2 : ZMod N)⁻¹) ^ 2 := by ring
        _ = 1 := by rw [ZMod.mul_inv_of_unit _ h2u, one_pow]
    calc (4 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2)
        = (4 : ZMod N) * (((2 : ZMod N)⁻¹ ^ 2) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2)) := by rw [hbij]
      _ = ((4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2)) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) := by ring
      _ = ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by rw [h2sq, one_mul]
  have h3_eq : (3 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) = 0 := by
    linear_combination h4_eq
  exact h3u.mul_left_cancel (by rw [h3_eq, mul_zero])

private lemma sum_inv_sq_mul_block {p s c : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ u ∈ (Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hsplit : (Finset.range ((c + 1) * p ^ s)).filter (fun u => ¬ p ∣ u) =
        (Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u) ∪
        ((Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u)).image (fun u => c * p ^ s + u) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx, hnd⟩
        by_cases hlt : x < c * p ^ s
        · exact Or.inl ⟨hlt, hnd⟩
        · right
          have hlt2 : x - c * p ^ s < p ^ s := by rw [add_mul, one_mul] at hx; omega
          refine ⟨x - c * p ^ s, ⟨hlt2, ?_⟩, by omega⟩
          intro hd
          apply hnd
          have hpN : p ∣ c * p ^ s := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
          have := dvd_add hpN hd
          rwa [show c * p ^ s + (x - c * p ^ s) = x by omega] at this
      · rintro (⟨hlt, hnd⟩ | ⟨u, ⟨hu, hnd⟩, rfl⟩)
        · exact ⟨by nlinarith, hnd⟩
        · refine ⟨by nlinarith, fun hd => hnd ?_⟩
          have hpN : p ∣ c * p ^ s := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
          exact (Nat.dvd_add_right hpN).mp hd
    have hdisj : Disjoint
        ((Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u))
        (((Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u)).image (fun u => c * p ^ s + u)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx1 hx2
      rcases hx2 with ⟨u, _, rfl⟩; omega
    rw [hsplit, Finset.sum_union hdisj, ih, zero_add,
      Finset.sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)]
    have hcongr : ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u),
        (((c * p ^ s + u : ℕ) : ZMod (p ^ s))⁻¹) ^ 2 =
        ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u), ((u : ZMod (p ^ s))⁻¹) ^ 2 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [hcongr]
    exact sum_inv_sq_units hp h5 hs

private lemma sum_inv_pair_block {p t B : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (ht : 1 ≤ t)
    (hB : p ^ t ∣ B) :
    ∑ u ∈ (Finset.range B).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t)))⁻¹ = 0 := by
  rcases hB with ⟨c, rfl⟩
  rw [mul_comm]
  have hcongr : ∑ u ∈ (Finset.range (c * p ^ t)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ t)) * ((c * p ^ t - u : ℕ) : ZMod (p ^ t)))⁻¹ =
      - ∑ u ∈ (Finset.range (c * p ^ t)).filter (fun u => ¬ p ∣ u),
        ((u : ZMod (p ^ t))⁻¹) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    have hcast : ((c * p ^ t - u : ℕ) : ZMod (p ^ t)) = -(u : ZMod (p ^ t)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_sub]
    rw [hcast, mul_neg, ← sq]
    have huu : IsUnit ((u : ZMod (p ^ t)) ^ 2) := (isUnit_zmod_pow hp hu.2).pow 2
    have hneg_inv : (-((u : ZMod (p ^ t)) ^ 2))⁻¹ = -((u : ZMod (p ^ t))⁻¹ ^ 2) := by
      have h1 : (-((u : ZMod (p ^ t)) ^ 2)) * (-((u : ZMod (p ^ t))⁻¹ ^ 2)) = 1 := by
        calc (-((u : ZMod (p ^ t)) ^ 2)) * (-((u : ZMod (p ^ t))⁻¹ ^ 2))
            = ((u : ZMod (p ^ t)) * (u : ZMod (p ^ t))⁻¹) ^ 2 := by ring
          _ = 1 := by rw [zmod_pow_mul_inv hp hu.2, one_pow]
      exact huu.neg.mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ huu.neg, h1])
    exact hneg_inv
  rw [hcongr, sum_inv_sq_mul_block hp h5 ht, neg_zero]

private lemma prod_Icc_split_dvd (p m : ℕ) (hp : 1 ≤ p) (f : ℕ → ℕ) :
    ∏ u ∈ Finset.Icc 1 (p * m), f u =
      (∏ j ∈ Finset.Icc 1 m, f (p * j)) *
        (∏ u ∈ (Finset.range (p * m)).filter (fun u => ¬ p ∣ u), f u) := by
  have hpart : Finset.Icc 1 (p * m) =
      (Finset.Icc 1 m).image (fun j => p * j) ∪
      (Finset.range (p * m)).filter (fun u => ¬ p ∣ u) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨hu1, hum⟩
      by_cases hd : p ∣ u
      · left
        rcases hd with ⟨j, rfl⟩
        exact ⟨j, ⟨by nlinarith, by nlinarith⟩, rfl⟩
      · right
        refine ⟨?_, hd⟩
        have hne : u ≠ p * m := fun h => hd (h ▸ dvd_mul_right p m)
        omega
    · rintro (⟨j, ⟨hj1, hjm⟩, rfl⟩ | ⟨hult, hnd⟩)
      · exact ⟨by nlinarith, by nlinarith⟩
      · refine ⟨?_, by omega⟩
        by_contra h0
        have hu0 : u = 0 := by omega
        exact hnd (hu0 ▸ dvd_zero p)
  have hdisj : Disjoint ((Finset.Icc 1 m).image (fun j => p * j))
      ((Finset.range (p * m)).filter (fun u => ¬ p ∣ u)) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_image, Finset.mem_filter] at hu1 hu2
    rcases hu1 with ⟨j, _, rfl⟩
    exact hu2.2 (dvd_mul_right p j)
  rw [hpart, Finset.prod_union hdisj,
    Finset.prod_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]

private lemma choose_mul_prod_Icc (d b : ℕ) :
    Nat.choose (d + b) b * (∏ j ∈ Finset.Icc 1 b, j) =
      ∏ j ∈ Finset.Icc 1 b, (d + j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hIcc : Finset.Icc 1 (b + 1) = insert (b + 1) (Finset.Icc 1 b) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
    have hstep : (b + 1) * Nat.choose (d + (b + 1)) (b + 1) =
        (d + (b + 1)) * Nat.choose (d + b) b := by
      have h := succ_mul_choose_eq (d + b) b
      rw [show d + (b + 1) = d + b + 1 by omega]
      linarith
    calc Nat.choose (d + (b + 1)) (b + 1) * ((b + 1) * ∏ j ∈ Finset.Icc 1 b, j)
        = ((b + 1) * Nat.choose (d + (b + 1)) (b + 1)) * ∏ j ∈ Finset.Icc 1 b, j := by ring
      _ = (d + (b + 1)) * (Nat.choose (d + b) b * ∏ j ∈ Finset.Icc 1 b, j) := by rw [hstep]; ring
      _ = (d + (b + 1)) * ∏ j ∈ Finset.Icc 1 b, (d + j) := by rw [ih]

private lemma choose_mul_prod_nonmul (p a b : ℕ) (hp : 1 ≤ p) (hab : b ≤ a) :
    Nat.choose (p * a) (p * b) *
        (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), u) =
      Nat.choose a b *
        (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), (p * (a - b) + u)) := by
  set d := a - b
  have ha : d + b = a := Nat.sub_add_cancel hab
  have hpa : p * d + p * b = p * a := by rw [← mul_add, ha]
  have h1 := choose_mul_prod_Icc (p * d) (p * b)
  rw [hpa] at h1
  rw [prod_Icc_split_dvd p b hp (fun u => u),
      prod_Icc_split_dvd p b hp (fun u => p * d + u)] at h1
  have h2 := choose_mul_prod_Icc d b
  rw [ha] at h2
  have hpmul1 : ∏ j ∈ Finset.Icc 1 b, (p * j) = p ^ b * ∏ j ∈ Finset.Icc 1 b, j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  have hpmul2 : ∏ j ∈ Finset.Icc 1 b, (p * d + p * j) =
      p ^ b * ∏ j ∈ Finset.Icc 1 b, (d + j) := by
    have : ∀ j, p * d + p * j = p * (d + j) := fun j => by ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  rw [hpmul1, hpmul2, ← h2] at h1
  have hpos : 0 < p ^ b * ∏ j ∈ Finset.Icc 1 b, j := by
    apply mul_pos (pow_pos (by omega) b)
    exact Finset.prod_pos fun j hj => (Finset.mem_Icc.mp hj).1
  apply Nat.eq_of_mul_eq_mul_left hpos
  linarith

private lemma prod_one_add_of_sq_zero {R : Type*} [CommRing R] {α : Type*}
    (s : Finset α) (c : R) (hc : c ^ 2 = 0) (f : α → R) :
    ∏ x ∈ s, (1 + c * f x) = 1 + c * ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    linear_combination (f a * ∑ x ∈ s, f x) * hc

private lemma jacobsthal_gen {p a b t e : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hab : b ≤ a)
    (ht : 1 ≤ t) (hte : t ≤ e) (hB : p ^ t ∣ p * b) (hDA : p ^ e ∣ (p * (a - b)) * (p * a)) :
    (Nat.choose (p * a) (p * b) : ZMod (p ^ (e + t))) =
      (Nat.choose a b : ZMod (p ^ (e + t))) := by
  set N := p ^ (e + t)
  set B := p * b
  set D := p * (a - b)
  set S := (Finset.range B).filter (fun u => ¬ p ∣ u)
  have hNpos : 0 < N := pow_pos hp.pos _
  have hprod_nat := choose_mul_prod_nonmul p a b hp.one_le hab
  have hprod_z : (Nat.choose (p * a) (p * b) : ZMod N) * (∏ u ∈ S, (u : ZMod N)) =
      (Nat.choose a b : ZMod N) * (∏ u ∈ S, ((D + u : ℕ) : ZMod N)) := by
    have hc := congrArg (fun n : ℕ => (n : ZMod N)) hprod_nat
    simpa only [Nat.cast_mul, Nat.cast_prod] using hc
  have hU : IsUnit (∏ u ∈ S, (u : ZMod N)) :=
    isUnit_prod_of_mem _ _ fun u hu => isUnit_zmod_pow hp (Finset.mem_filter.mp hu).2
  set P : ZMod N := ∏ u ∈ S, (1 + (D : ZMod N) * (u : ZMod N)⁻¹)
  have hprod_P : (∏ u ∈ S, ((D + u : ℕ) : ZMod N)) = (∏ u ∈ S, (u : ZMod N)) * P := by
    simp only [P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    have hinv := zmod_pow_mul_inv (s := e + t) hp (Finset.mem_filter.mp hu).2
    push_cast
    calc (D : ZMod N) + (u : ZMod N)
        = (u : ZMod N) + (D : ZMod N) * ((u : ZMod N) * (u : ZMod N)⁻¹) := by rw [hinv, mul_one]; ring
      _ = (u : ZMod N) * (1 + (D : ZMod N) * (u : ZMod N)⁻¹) := by ring
  have hP_eq_one : P = 1 := by
    -- Show P^2 = 1 via the involution u ↦ B - u on S!
    have hP_rev : P = ∏ u ∈ S, (1 + (D : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) := by
      refine Finset.prod_bij (fun u _ => B - u) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [S, Finset.mem_filter, Finset.mem_range] at hu ⊢
        have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu.2 (h ▸ dvd_zero p))
        refine ⟨by omega, fun hd => hu.2 ?_⟩
        have hpB : p ∣ B := dvd_mul_right p b
        have := (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
        exact this
      · intro u1 hu1 u2 hu2 heq
        simp only [S, Finset.mem_filter, Finset.mem_range] at hu1 hu2; omega
      · intro v hv
        simp only [S, Finset.mem_filter, Finset.mem_range] at hv
        have hv1 : 1 ≤ v := Nat.pos_of_ne_zero (fun h => hv.2 (h ▸ dvd_zero p))
        refine ⟨B - v, ?_, by omega⟩
        simp only [S, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, fun hd => hv.2 ?_⟩
        have hpB : p ∣ B := dvd_mul_right p b
        exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
      · intro u hu
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
        rw [Nat.sub_sub_self (by omega)]
    have hDA_eq : (D : ZMod N) * ((D + B : ℕ) : ZMod N) = ((D * (p * a) : ℕ) : ZMod N) := by
      have : D + B = p * a := by
        simp only [D, B]; rw [← mul_add, Nat.sub_add_cancel hab]
      rw [this, ← Nat.cast_mul]
    have hP2 : P ^ 2 = ∏ u ∈ S, (1 + ((D * (p * a) : ℕ) : ZMod N) *
        ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹) := by
      rw [sq]
      conv_lhs => rhs; rw [hP_rev]
      simp only [P, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun u hu => ?_
      have hnd1 : ¬ p ∣ u := (Finset.mem_filter.mp hu).2
      have hult : u < B := (Finset.mem_filter.mp hu).1 |> Finset.mem_range.mp
      have hnd2 : ¬ p ∣ (B - u) := fun hd => hnd1 <| by
        have hpB : p ∣ B := dvd_mul_right p b
        exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
      have hu1 := isUnit_zmod_pow (s := e + t) hp hnd1
      have hu2 := isUnit_zmod_pow (s := e + t) hp hnd2
      have hmul_inv : ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹ =
          (u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹ := by
        have h1 : ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) *
            ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) = 1 := by
          calc ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) *
                ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹)
              = ((u : ZMod N) * (u : ZMod N)⁻¹) *
                (((B - u : ℕ) : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
            _ = 1 := by rw [ZMod.mul_inv_of_unit _ hu1, ZMod.mul_inv_of_unit _ hu2, mul_one]
        exact (hu1.mul hu2).mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ (hu1.mul hu2), h1])
      rw [hmul_inv, ← hDA_eq]
      have hBu : (B : ZMod N) = (u : ZMod N) + ((B - u : ℕ) : ZMod N) := by
        rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
      have hinv1 := ZMod.mul_inv_of_unit _ hu1
      have hinv2 := ZMod.mul_inv_of_unit _ hu2
      have hsum_inv : (u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹ =
          (B : ZMod N) * ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by
        rw [hBu]
        calc (u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹
            = (u : ZMod N)⁻¹ * (((B - u : ℕ) : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) +
              ((u : ZMod N) * (u : ZMod N)⁻¹) * ((B - u : ℕ) : ZMod N)⁻¹ := by rw [hinv1, hinv2]; ring
          _ = ((u : ZMod N) + ((B - u : ℕ) : ZMod N)) *
              ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
      push_cast
      calc (1 + (D : ZMod N) * (u : ZMod N)⁻¹) * (1 + (D : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹)
          = 1 + (D : ZMod N) * ((u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹) +
            (D : ZMod N) ^ 2 * ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
        _ = 1 + (D : ZMod N) * ((D : ZMod N) + (B : ZMod N)) *
            ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by rw [hsum_inv]; ring
    have hc_sq : (((D * (p * a) : ℕ) : ZMod N)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      have h1 : (p ^ e) ^ 2 ∣ (D * (p * a)) ^ 2 := pow_dvd_pow_of_dvd hDA 2
      have h2 : p ^ (e + t) ∣ (p ^ e) ^ 2 := by
        rw [← pow_mul]
        exact pow_dvd_pow p (by omega)
      exact dvd_trans h2 h1
    rw [prod_one_add_of_sq_zero S _ hc_sq] at hP2
    -- Show ((D * (p*a)) : ZMod N) * sum = 0 because p^e | D*(p*a) and sum = 0 mod p^t!
    set sum_inv : ZMod N := ∑ u ∈ S, ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹
    have hproj_sum : ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t)) sum_inv = 0 := by
      set φ := ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t))
      have hmap : φ sum_inv = ∑ u ∈ S, ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t)))⁻¹ := by
        simp only [sum_inv, map_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hnd1 : ¬ p ∣ u := (Finset.mem_filter.mp hu).2
        have hult : u < B := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
        have hnd2 : ¬ p ∣ (B - u) := fun hd => hnd1 <| by
          have hpB : p ∣ B := dvd_mul_right p b
          exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
        have huN : IsUnit ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) :=
          (isUnit_zmod_pow hp hnd1).mul (isUnit_zmod_pow hp hnd2)
        have hut : IsUnit ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t))) :=
          (isUnit_zmod_pow hp hnd1).mul (isUnit_zmod_pow hp hnd2)
        have h1 := congrArg φ (ZMod.mul_inv_of_unit _ huN)
        simp only [map_mul, map_natCast, map_one] at h1
        exact hut.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ hut])
      rw [hmap]
      exact sum_inv_pair_block hp h5 ht hB
    have hmul_zero : ((D * (p * a) : ℕ) : ZMod N) * sum_inv = 0 := by
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      have hdvd_sum : p ^ t ∣ sum_inv.val := by
        rw [← ZMod.natCast_eq_zero_iff]
        have h1 : ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t))
            (sum_inv.val : ZMod N) = (sum_inv.val : ZMod (p ^ t)) := map_natCast _ _
        rw [← h1, ZMod.natCast_zmod_val, hproj_sum]
      rcases hDA with ⟨q1, hq1⟩
      rcases hdvd_sum with ⟨q2, hq2⟩
      rw [← ZMod.natCast_zmod_val sum_inv, hq1, hq2, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      dsimp only [N]
      rw [pow_add]
      exact ⟨q1 * q2, by ring⟩
    rw [hmul_zero, add_zero] at hP2
    -- P^2 = 1 and P ≡ 1 (mod p), so P + 1 is a unit in ZMod N, hence P = 1!
    have hP_mod_p : ZMod.castHom (dvd_pow_self p (by omega : e + t ≠ 0)) (ZMod p) P = 1 := by
      set ψ := ZMod.castHom (dvd_pow_self p (by omega : e + t ≠ 0)) (ZMod p)
      simp only [P, map_prod, map_add, map_one, map_mul, map_natCast]
      have hD0 : (D : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact dvd_mul_right p (a - b)
      simp [hD0]
    have hP1_unit : IsUnit (P + 1) := by
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      rw [← ZMod.natCast_zmod_val (P + 1), ZMod.isUnit_iff_coprime]
      refine (coprime_of_not_dvd_prime hp ?_).pow_right (e + t)
      intro hd
      have h0 : ((P + 1).val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
      have h1 : ZMod.castHom (dvd_pow_self p (by omega : e + t ≠ 0)) (ZMod p) (P + 1) = 0 := by
        rw [← ZMod.natCast_zmod_val (P + 1), map_natCast, h0]
      rw [map_add, map_one, hP_mod_p] at h1
      have h20 : ((2 : ℕ) : ZMod p) = 0 := by simpa only [Nat.cast_ofNat, one_add_one_eq_two] using h1
      have hd2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
      have := Nat.le_of_dvd (by decide) hd2; omega
    have hdiff : (P + 1) * (P - 1) = 0 := by linear_combination hP2
    have hPsub : P - 1 = 0 := hP1_unit.mul_left_cancel (by rw [hdiff, mul_zero])
    exact sub_eq_zero.mp hPsub
  rw [hprod_P, hP_eq_one, mul_one] at hprod_z
  exact hU.mul_right_cancel hprod_z

private lemma choose_central_pred_cong {p n r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hn : 0 < n) (hr : 0 < r) :
    (Nat.choose (2 * (n * p ^ r) - 1) (n * p ^ r - 1) : ZMod (p ^ (3 * r))) =
      (Nat.choose (2 * (n * p ^ (r - 1)) - 1) (n * p ^ (r - 1) - 1) : ZMod (p ^ (3 * r))) := by
  set M := n * p ^ r
  set N := n * p ^ (r - 1)
  have hMp : M = p * N := by
    simp only [M, N]
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    ring
  have h2M : 2 * M = p * (2 * N) := by rw [hMp]; ring
  have hMpos : 1 ≤ M := Nat.mul_pos hn (pow_pos hp.pos r)
  have hNpos : 1 ≤ N := Nat.mul_pos hn (pow_pos hp.pos (r - 1))
  have hjac := jacobsthal_gen (p := p) (a := 2 * N) (b := N) (t := r) (e := 2 * r)
    hp h5 (by omega) hr (by omega)
    (by rw [← hMp]; exact dvd_mul_left (p ^ r) n)
    (by
      have hsub : 2 * N - N = N := by omega
      rw [hsub, ← hMp, ← h2M, show 2 * r = r + r by omega, pow_add]
      exact mul_dvd_mul (dvd_mul_left (p ^ r) n)
        (dvd_mul_of_dvd_right (dvd_mul_left (p ^ r) n) 2))
  rw [show 2 * r + r = 3 * r by omega, ← h2M, ← hMp] at hjac
  have h2u : IsUnit (2 : ZMod (p ^ (3 * r))) := by
    change IsUnit ((2 : ℕ) : ZMod (p ^ (3 * r)))
    exact isUnit_zmod_pow hp (fun h => by have := Nat.le_of_dvd (by decide) h; omega)
  have hrel1 : 2 * Nat.choose (2 * M - 1) (M - 1) = Nat.choose (2 * M) M := by
    have hq := choose_two_mul_pred M hMpos; exact_mod_cast hq
  have hrel2 : 2 * Nat.choose (2 * N - 1) (N - 1) = Nat.choose (2 * N) N := by
    have hq := choose_two_mul_pred N hNpos; exact_mod_cast hq
  apply h2u.mul_left_cancel
  have hc1 : (2 : ZMod (p ^ (3 * r))) * (Nat.choose (2 * M - 1) (M - 1) : ZMod (p ^ (3 * r))) =
      (Nat.choose (2 * M) M : ZMod (p ^ (3 * r))) := by
    have := congrArg (fun x : ℕ => (x : ZMod (p ^ (3 * r)))) hrel1
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using this
  have hc2 : (2 : ZMod (p ^ (3 * r))) * (Nat.choose (2 * N - 1) (N - 1) : ZMod (p ^ (3 * r))) =
      (Nat.choose (2 * N) N : ZMod (p ^ (3 * r))) := by
    have := congrArg (fun x : ℕ => (x : ZMod (p ^ (3 * r)))) hrel2
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using this
  rw [hc1, hc2, hjac]

/-! ### Part 3: Supercongruence for A_nat(n * p^r) ≡ A_nat(n * p^(r-1)) (mod p^(3*r)) -/

private lemma choose_pred_mul_eq (N j : ℕ) (hN : 1 ≤ N) :
    (N + j) * Nat.choose (N - 1 + j) j = N * Nat.choose (N + j) j := by
  have hq := choose_mul_upper N j hN
  exact_mod_cast hq.symm

private lemma A_div_term_cong {p n r j : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hn : 0 < n) (hr : 0 < r) (hj : j < n * p ^ (r - 1)) :
    (Nat.choose (n * p ^ r - 1 + p * j) (p * j) : ZMod (p ^ (3 * r))) ^ 2 =
      (Nat.choose (n * p ^ (r - 1) - 1 + j) j : ZMod (p ^ (3 * r))) ^ 2 := by
  set M := n * p ^ r
  set N := n * p ^ (r - 1)
  have hMp : M = p * N := by
    simp only [M, N]
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    ring
  have hNpos : 1 ≤ N := Nat.mul_pos hn (pow_pos hp.pos (r - 1))
  have hMpos : 1 ≤ M := Nat.mul_pos hn (pow_pos hp.pos r)
  by_cases hj0 : j = 0
  · subst hj0; simp
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have : Fact p.Prime := ⟨hp⟩
    set v := padicValNat p j
    set w := padicValNat p (N + j)
    set m := padicValNat p N
    have hm_ge : r - 1 ≤ m := by
      have hd : p ^ (r - 1) ∣ N := dvd_mul_left (p ^ (r - 1)) n
      exact (padicValNat_dvd_iff_le (by omega)).mp hd
    set t := min (m + 1) (v + 1)
    set e := (m + 1) + (w + 1)
    have ht1 : 1 ≤ t := by omega
    have hte : t ≤ e := by omega
    have hB : p ^ t ∣ p * j := by
      have hv : p ^ v ∣ j := pow_padicValNat_dvd
      have hv1 : p ^ (v + 1) ∣ p * j := by
        rw [pow_succ']; exact mul_dvd_mul_left p hv
      exact dvd_trans (pow_dvd_pow p (min_le_right _ _)) hv1
    have hDA : p ^ e ∣ (p * ((N + j) - j)) * (p * (N + j)) := by
      rw [Nat.add_sub_cancel]
      have hm1 : p ^ (m + 1) ∣ p * N := by
        rw [pow_succ']; exact mul_dvd_mul_left p pow_padicValNat_dvd
      have hw1 : p ^ (w + 1) ∣ p * (N + j) := by
        rw [pow_succ']; exact mul_dvd_mul_left p pow_padicValNat_dvd
      rw [show e = (m + 1) + (w + 1) from rfl, pow_add]
      exact mul_dvd_mul hm1 hw1
    have hjac := jacobsthal_gen (p := p) (a := N + j) (b := j) (t := t) (e := e)
      hp h5 (Nat.le_add_left j N) ht1 hte hB hDA
    have hdvd_C : ((p ^ (e + t) : ℕ) : ℤ) ∣
        ((Nat.choose (p * (N + j)) (p * j) : ℤ) - (Nat.choose (N + j) j : ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        sub_eq_zero]
      exact hjac
    -- Relate C(M-1+pj, pj) - C(N-1+j, j) via (N+j) * Δ = N * (C(p(N+j), pj) - C(N+j, j))
    set cM : ℤ := (Nat.choose (M - 1 + p * j) (p * j) : ℤ)
    set cN : ℤ := (Nat.choose (N - 1 + j) j : ℤ)
    have hrelM : ((N + j : ℕ) : ℤ) * cM = (N : ℤ) * (Nat.choose (p * (N + j)) (p * j) : ℤ) := by
      have h1 := choose_pred_mul_eq M (p * j) hMpos
      have h2 : M + p * j = p * (N + j) := by rw [hMp]; ring
      conv_lhs at h1 => rw [h2]
      conv_rhs at h1 => rw [h2, hMp]
      have h3 : (N + j) * Nat.choose (M - 1 + p * j) (p * j) =
          N * Nat.choose (p * (N + j)) (p * j) := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        linarith
      dsimp only [cM]
      exact_mod_cast h3
    have hrelN : ((N + j : ℕ) : ℤ) * cN = (N : ℤ) * (Nat.choose (N + j) j : ℤ) := by
      dsimp only [cN]
      exact_mod_cast choose_pred_mul_eq N j hNpos
    have hrelΔ : ((N + j : ℕ) : ℤ) * (cM - cN) =
        (N : ℤ) * ((Nat.choose (p * (N + j)) (p * j) : ℤ) - (Nat.choose (N + j) j : ℤ)) := by
      linear_combination hrelM - hrelN
    -- Extract p^w from N + j: write N + j = p^w * u with ¬ p | u!
    have hw_dvd : p ^ w ∣ N + j := pow_padicValNat_dvd
    rcases hw_dvd with ⟨u, hu⟩
    have hund : ¬ p ∣ u := by
      intro hpu
      have hd1 : p ^ (w + 1) ∣ N + j := by
        rw [hu, pow_succ]
        rcases hpu with ⟨u', rfl⟩
        exact ⟨u', by ring⟩
      have hle := (padicValNat_dvd_iff_le (by omega : N + j ≠ 0)).mp hd1
      omega
    have hcop_u : ∀ k : ℕ, IsCoprime ((p ^ k : ℕ) : ℤ) (u : ℤ) := fun k => by
      have hc : Nat.Coprime (p ^ k) u := (hp.coprime_iff_not_dvd.mpr hund).pow_left k
      exact_mod_cast hc.isCoprime
    -- Therefore p^(2m + t + 2) | (cM - cN)!
    have hdvd_Δ : ((p ^ (2 * m + t + 2) : ℕ) : ℤ) ∣ (cM - cN) := by
      have hm_dvd : ((p ^ m : ℕ) : ℤ) ∣ (N : ℤ) := by
        exact_mod_cast (pow_padicValNat_dvd (p := p) (n := N))
      have hrhs : ((p ^ (m + (e + t)) : ℕ) : ℤ) ∣ ((N + j : ℕ) : ℤ) * (cM - cN) := by
        rw [hrelΔ, pow_add, Nat.cast_mul]
        exact mul_dvd_mul hm_dvd hdvd_C
      have hsplit : m + (e + t) = w + (2 * m + t + 2) := by omega
      rw [hsplit, hu, pow_add, Nat.cast_mul, Nat.cast_mul] at hrhs
      have hpw_ne : ((p ^ w : ℕ) : ℤ) ≠ 0 := by positivity
      have hcancel : ((p ^ (2 * m + t + 2) : ℕ) : ℤ) ∣ (u : ℤ) * (cM - cN) := by
        rcases hrhs with ⟨q, hq⟩
        exact ⟨q, mul_left_cancel₀ hpw_ne (by linarith)⟩
      exact (hcop_u (2 * m + t + 2)).dvd_of_dvd_mul_left hcancel
    -- Now prove p^(3*r) | (cM^2 - cN^2) = (cM - cN) * (cM + cN)!
    have hdvd_sq : ((p ^ (3 * r) : ℕ) : ℤ) ∣ (cM ^ 2 - cN ^ 2) := by
      have h3r_le : 3 * r ≤ 3 * m + 3 := by omega
      by_cases hvm : v < m
      · -- Case 1: v < m => w = v, t = v + 1, and p^(m - v) | cN and p^(m - v) | cM!
        have hwv : w = v := by
          have hv_dvd : p ^ v ∣ N + j :=
            dvd_add (dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd) pow_padicValNat_dvd
          have hv_le : v ≤ w := (padicValNat_dvd_iff_le (by omega : N + j ≠ 0)).mp hv_dvd
          have hw_le : w ≤ v := by
            by_contra hlt
            have h1 : p ^ (v + 1) ∣ N + j :=
              dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd
            have h2 : p ^ (v + 1) ∣ N :=
              dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd
            have h3 : p ^ (v + 1) ∣ j := (Nat.dvd_add_right h2).mp h1
            have := (padicValNat_dvd_iff_le (by omega : j ≠ 0)).mp h3
            omega
          omega
        have ht_eq : t = v + 1 := by omega
        have hdvd_cN : ((p ^ (m - v) : ℕ) : ℤ) ∣ cN := by
          have hm_dvd : ((p ^ m : ℕ) : ℤ) ∣ (N : ℤ) := by
            exact_mod_cast (pow_padicValNat_dvd (p := p) (n := N))
          have hrhs : ((p ^ m : ℕ) : ℤ) ∣ ((N + j : ℕ) : ℤ) * cN := by
            rw [hrelN]; exact dvd_mul_of_dvd_left hm_dvd _
          rw [hu, hwv, show m = v + (m - v) by omega, pow_add, Nat.cast_mul, Nat.cast_mul] at hrhs
          have hpw_ne : ((p ^ v : ℕ) : ℤ) ≠ 0 := by positivity
          have hcancel : ((p ^ (m - v) : ℕ) : ℤ) ∣ (u : ℤ) * cN := by
            rcases hrhs with ⟨q, hq⟩
            exact ⟨q, mul_left_cancel₀ hpw_ne (by linarith)⟩
          exact (hcop_u (m - v)).dvd_of_dvd_mul_left hcancel
        have hdvd_Δ_mv : ((p ^ (m - v) : ℕ) : ℤ) ∣ (cM - cN) :=
          dvd_trans (by exact_mod_cast pow_dvd_pow p (show m - v ≤ 2 * m + t + 2 by omega)) hdvd_Δ
        have hdvd_sum : ((p ^ (m - v) : ℕ) : ℤ) ∣ (cM + cN) := by
          have : cM + cN = (cM - cN) + 2 * cN := by ring
          rw [this]
          exact dvd_add hdvd_Δ_mv (dvd_mul_of_dvd_right hdvd_cN 2)
        have hmul : ((p ^ ((2 * m + t + 2) + (m - v)) : ℕ) : ℤ) ∣ (cM - cN) * (cM + cN) := by
          rw [pow_add, Nat.cast_mul]
          exact mul_dvd_mul hdvd_Δ hdvd_sum
        rw [show (cM - cN) * (cM + cN) = cM ^ 2 - cN ^ 2 by ring] at hmul
        have hexp : 3 * r ≤ (2 * m + t + 2) + (m - v) := by omega
        exact dvd_trans (by exact_mod_cast pow_dvd_pow p hexp) hmul
      · -- Case 2: m <= v => t = m + 1 => 2m + t + 2 = 3m + 3 >= 3r already!
        have ht_eq : t = m + 1 := by omega
        have hexp : 3 * r ≤ 2 * m + t + 2 := by omega
        have hd1 : ((p ^ (3 * r) : ℕ) : ℤ) ∣ (cM - cN) :=
          dvd_trans (by exact_mod_cast pow_dvd_pow p hexp) hdvd_Δ
        rw [show cM ^ 2 - cN ^ 2 = (cM - cN) * (cM + cN) by ring]
        exact dvd_mul_of_dvd_left hd1 _
    have h0 : ((cM ^ 2 - cN ^ 2 : ℤ) : ZMod (p ^ (3 * r))) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd_sq
    simp only [cM, cN, Int.cast_sub, Int.cast_pow, Int.cast_natCast, sub_eq_zero] at h0
    exact h0

private lemma choose_shift_mod {p s n a v i : ℕ} (hp : p.Prime) (hs : 1 ≤ s) (hi : i < p) :
    (Nat.choose ((n + a) * p ^ s + p * v + i) (a * p ^ s + p * v + i) : ZMod (p ^ s)) =
      (Nat.choose ((n + a) * p ^ (s - 1) + v) (a * p ^ (s - 1) + v) : ZMod (p ^ s)) := by
  -- Step 1: reduce i down to 0 by induction on i!
  have hstep1 : ∀ i, i < p →
      (Nat.choose ((n + a) * p ^ s + p * v + i) (a * p ^ s + p * v + i) : ZMod (p ^ s)) =
        (Nat.choose ((n + a) * p ^ s + p * v) (a * p ^ s + p * v) : ZMod (p ^ s)) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hrel : (a * p ^ s + p * v + (i + 1)) *
            Nat.choose ((n + a) * p ^ s + p * v + (i + 1)) (a * p ^ s + p * v + (i + 1)) =
          ((n + a) * p ^ s + p * v + (i + 1)) *
            Nat.choose ((n + a) * p ^ s + p * v + i) (a * p ^ s + p * v + i) := by
        have h := succ_mul_choose_eq ((n + a) * p ^ s + p * v + i) (a * p ^ s + p * v + i)
        simpa only [add_assoc] using h.symm
      have hnd : ¬ p ∣ (a * p ^ s + p * v + (i + 1)) := by
        intro hd
        have h1 : p ∣ a * p ^ s + p * v :=
          dvd_add (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) a) (dvd_mul_right p v)
        have h2 : p ∣ i + 1 := (Nat.dvd_add_right h1).mp hd
        have := Nat.le_of_dvd (by omega) h2; omega
      have hu : IsUnit ((a * p ^ s + p * v + (i + 1) : ℕ) : ZMod (p ^ s)) :=
        isUnit_zmod_pow hp hnd
      have hcast := congrArg (fun x : ℕ => (x : ZMod (p ^ s))) hrel
      simp only [Nat.cast_mul] at hcast
      have hcoef : (((n + a) * p ^ s + p * v + (i + 1) : ℕ) : ZMod (p ^ s)) =
          ((a * p ^ s + p * v + (i + 1) : ℕ) : ZMod (p ^ s)) := by
        simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
      rw [hcoef] at hcast
      rw [hu.mul_left_cancel hcast]
      exact ih (by omega)
  rw [hstep1 i hi]
  -- Step 2: use choose_mul_prod_nonmul in ZMod (p^s)!
  set A := (n + a) * p ^ (s - 1) + v
  set B := a * p ^ (s - 1) + v
  have hAB : B ≤ A := by simp only [A, B]; rw [add_mul]; omega
  have hpA : p * A = (n + a) * p ^ s + p * v := by
    simp only [A]
    conv_rhs => rw [show s = (s - 1) + 1 by omega, pow_succ]
    ring
  have hpB : p * B = a * p ^ s + p * v := by
    simp only [B]
    conv_rhs => rw [show s = (s - 1) + 1 by omega, pow_succ]
    ring
  have hpD : p * (A - B) = n * p ^ s := by
    have : A - B = n * p ^ (s - 1) := by
      simp only [A, B]; rw [add_mul]; omega
    rw [this]
    conv_rhs => rw [show s = (s - 1) + 1 by omega, pow_succ]
    ring
  rw [← hpA, ← hpB]
  have hprod := choose_mul_prod_nonmul p A B hp.one_le hAB
  rw [hpD] at hprod
  have hc := congrArg (fun x : ℕ => (x : ZMod (p ^ s))) hprod
  simp only [Nat.cast_mul, Nat.cast_prod] at hc
  have hprod_eq : ∏ u ∈ (Finset.range (p * B)).filter (fun u => ¬ p ∣ u),
      ((n * p ^ s + u : ℕ) : ZMod (p ^ s)) =
      ∏ u ∈ (Finset.range (p * B)).filter (fun u => ¬ p ∣ u), (u : ZMod (p ^ s)) := by
    refine Finset.prod_congr rfl fun u _ => ?_
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  rw [hprod_eq] at hc
  have hU : IsUnit (∏ u ∈ (Finset.range (p * B)).filter (fun u => ¬ p ∣ u), (u : ZMod (p ^ s))) :=
    isUnit_prod_of_mem _ _ fun u hu => isUnit_zmod_pow hp (Finset.mem_filter.mp hu).2
  exact hU.mul_right_cancel hc

private def I_k (p r k v : ℕ) : ZMod (p ^ r) :=
  ∑ w ∈ (Finset.range (p ^ k)).filter (fun w => ¬ p ∣ w),
    (((v * p ^ k + w : ℕ) : ZMod (p ^ r))⁻¹) ^ 2

private lemma proj_I_k_eq_zero {p r k v : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hk : 1 ≤ k) (hkr : k ≤ r) :
    ZMod.castHom (pow_dvd_pow p hkr) (ZMod (p ^ k)) (I_k p r k v) = 0 := by
  set φ := ZMod.castHom (pow_dvd_pow p hkr) (ZMod (p ^ k))
  have hmap : φ (I_k p r k v) =
      ∑ w ∈ (Finset.range (p ^ k)).filter (fun w => ¬ p ∣ w), ((w : ZMod (p ^ k))⁻¹) ^ 2 := by
    simp only [I_k, map_sum, map_pow]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hnd : ¬ p ∣ w := (Finset.mem_filter.mp hw).2
    have hnd2 : ¬ p ∣ (v * p ^ k + w) := fun hd => hnd <| by
      have hp1 : p ∣ v * p ^ k := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) v
      exact (Nat.dvd_add_right hp1).mp hd
    have huR : IsUnit ((v * p ^ k + w : ℕ) : ZMod (p ^ r)) := isUnit_zmod_pow hp hnd2
    have huK : IsUnit (w : ZMod (p ^ k)) := isUnit_zmod_pow hp hnd
    have h1 := congrArg φ (ZMod.mul_inv_of_unit _ huR)
    rw [map_mul, map_natCast, map_one] at h1
    have hcast : ((v * p ^ k + w : ℕ) : ZMod (p ^ k)) = (w : ZMod (p ^ k)) := by
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [hcast] at h1
    congr 1
    exact huK.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ huK])
  rw [hmap]
  exact sum_inv_sq_units hp h5 hk

private lemma mul_zero_of_proj_eq_zero {p r s k : ℕ} (hp : p.Prime) (hsk : s + k = r)
    (x y : ZMod (p ^ r))
    (hx : ZMod.castHom (pow_dvd_pow p (by omega : s ≤ r)) (ZMod (p ^ s)) x = 0)
    (hy : ZMod.castHom (pow_dvd_pow p (by omega : k ≤ r)) (ZMod (p ^ k)) y = 0) :
    x * y = 0 := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hdx : p ^ s ∣ x.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h1 : ZMod.castHom (pow_dvd_pow p (by omega : s ≤ r)) (ZMod (p ^ s))
        (x.val : ZMod (p ^ r)) = (x.val : ZMod (p ^ s)) := map_natCast _ _
    rw [← h1, ZMod.natCast_zmod_val, hx]
  have hdy : p ^ k ∣ y.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h1 : ZMod.castHom (pow_dvd_pow p (by omega : k ≤ r)) (ZMod (p ^ k))
        (y.val : ZMod (p ^ r)) = (y.val : ZMod (p ^ k)) := map_natCast _ _
    rw [← h1, ZMod.natCast_zmod_val, hy]
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff]
  have hmul : p ^ s * p ^ k ∣ x.val * y.val := mul_dvd_mul hdx hdy
  rwa [← pow_add, hsk] at hmul

private def T_sum (p r n a k : ℕ) : ZMod (p ^ r) :=
  ∑ v ∈ Finset.range (p ^ (r - k)),
    ((Nat.choose ((n + a) * p ^ (r - k) + v) (a * p ^ (r - k) + v) : ZMod (p ^ r)) ^ 2) *
      I_k p r k v

private lemma sum_I_k_step {p r k v : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range p, I_k p r k (p * v + i) = I_k p r (k + 1) v := by
  simp only [I_k]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => x.1 * p ^ k + x.2) ?_ ?_ ?_ ?_
  · rintro ⟨i, w⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [pow_succ']
      have h1 : i * p ^ k + w < (i + 1) * p ^ k := by
        rw [add_mul, one_mul]; omega
      have h2 : (i + 1) * p ^ k ≤ p * p ^ k := Nat.mul_le_mul_right _ hx.1
      omega
    · intro hd
      have hp1 : p ∣ i * p ^ k := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) i
      exact hx.2.2 ((Nat.dvd_add_right hp1).mp hd)
  · rintro ⟨i1, w1⟩ hx1 ⟨i2, w2⟩ hx2 heq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx1 hx2
    have hq : i1 = i2 := by
      have h1 := congrArg (fun z => z / p ^ k) heq
      simp only [mul_add_div_right (pow_pos hp.pos k), Nat.div_eq_of_lt hx1.2.1,
        Nat.div_eq_of_lt hx2.2.1, add_zero] at h1
      exact h1
    subst hq
    have hw : w1 = w2 := Nat.add_left_cancel heq
    subst hw; rfl
  · intro w' hw'
    simp only [Finset.mem_filter, Finset.mem_range] at hw'
    refine ⟨⟨w' / p ^ k, w' % p ^ k⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      refine ⟨?_, Nat.mod_lt _ (pow_pos hp.pos k), ?_⟩
      · rw [pow_succ'] at hw'
        exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hw'.1)
      · intro hd
        apply hw'.2
        have hmod := Nat.div_add_mod w' (p ^ k)
        have hp1 : p ∣ p ^ k * (w' / p ^ k) := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
        exact hmod ▸ dvd_add hp1 hd
    · have := Nat.div_add_mod w' (p ^ k); linarith
  · rintro ⟨i, w⟩ _
    congr 3
    rw [pow_succ']; ring

private lemma T_sum_step {p r n a k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hk : 1 ≤ k) (hkr : k < r) :
    T_sum p r n a k = T_sum p r n a (k + 1) := by
  set s := r - k
  have hs : 1 ≤ s := by omega
  have hsk : s + k = r := by omega
  have hrk1 : r - (k + 1) = s - 1 := by omega
  simp only [T_sum]
  have hsplit : Finset.range (p ^ s) =
      (Finset.range (p ^ (s - 1)) ×ˢ Finset.range p).image (fun x => p * x.1 + x.2) := by
    ext v
    simp only [Finset.mem_range, Finset.mem_image, Finset.mem_product]
    constructor
    · intro hv
      refine ⟨(v / p, v % p), ⟨?_, Nat.mod_lt _ hp.pos⟩, Nat.div_add_mod v p⟩
      have : p ^ s = p * p ^ (s - 1) := by
        conv_lhs => rw [show s = (s - 1) + 1 by omega, pow_succ']
      rw [this] at hv
      exact Nat.div_lt_of_lt_mul hv
    · rintro ⟨⟨q, i⟩, ⟨hq, hi⟩, rfl⟩
      dsimp only
      have : p ^ s = p * p ^ (s - 1) := by
        conv_lhs => rw [show s = (s - 1) + 1 by omega, pow_succ']
      rw [this]
      have h1 : p * q + i < p * (q + 1) := by rw [mul_add, mul_one]; omega
      have h2 : p * (q + 1) ≤ p * p ^ (s - 1) := Nat.mul_le_mul_left p hq
      omega
  have hinj : Set.InjOn (fun x : ℕ × ℕ => p * x.1 + x.2)
      ((Finset.range (p ^ (s - 1)) ×ˢ Finset.range p : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro ⟨q1, i1⟩ h1 ⟨q2, i2⟩ h2 heq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at h1 h2
    dsimp only at heq
    have hq : q1 = q2 := by
      have hdiv := congrArg (fun z => z / p) heq
      simp only [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt h1.2, Nat.div_eq_of_lt h2.2,
        add_zero] at hdiv
      exact hdiv
    subst hq
    have hi : i1 = i2 := Nat.add_left_cancel heq
    subst hi; rfl
  change ∑ v ∈ Finset.range (p ^ s), _ = ∑ v ∈ Finset.range (p ^ (r - (k + 1))), _
  rw [hsplit, Finset.sum_image hinj, Finset.sum_product, hrk1]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hcongr : ∑ i ∈ Finset.range p,
      ((Nat.choose ((n + a) * p ^ s + (p * v + i)) (a * p ^ s + (p * v + i)) : ZMod (p ^ r)) ^ 2) *
        I_k p r k (p * v + i) =
      ∑ i ∈ Finset.range p,
      ((Nat.choose ((n + a) * p ^ (s - 1) + v) (a * p ^ (s - 1) + v) : ZMod (p ^ r)) ^ 2) *
        I_k p r k (p * v + i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [← sub_eq_zero, ← sub_mul]
    apply mul_zero_of_proj_eq_zero hp hsk
    · simp only [map_sub, map_pow, map_natCast, sub_eq_zero]
      rw [← add_assoc, ← add_assoc, choose_shift_mod hp hs hi]
    · exact proj_I_k_eq_zero hp h5 hk (by omega)
  rw [hcongr, ← Finset.mul_sum, sum_I_k_step hp hk]

private lemma T_sum_eq_zero {p r n a : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 1 ≤ r) :
    T_sum p r n a 1 = 0 := by
  have hwalk : ∀ d, d ≤ r - 1 → T_sum p r n a (1 + d) = T_sum p r n a 1 := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
      rw [show 1 + (d + 1) = (1 + d) + 1 by omega]
      rw [← ih (by omega)]
      exact (T_sum_step hp h5 (by omega) (by omega)).symm
  have htop := hwalk (r - 1) (le_refl _)
  rw [show 1 + (r - 1) = r by omega] at htop
  rw [← htop]
  simp only [T_sum, Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton, I_k,
    zero_mul, zero_add]
  rw [sum_inv_sq_units hp h5 hr, mul_zero]

private lemma A_ndiv_block_zero {p r n a : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hn : 0 < n) (hr : 1 ≤ r) :
    ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
      (Nat.choose (n * p ^ r - 1 + (a * p ^ r + u)) (a * p ^ r + u) : ZMod (p ^ (3 * r))) ^ 2 = 0 := by
  set M := n * p ^ r
  set A := a * p ^ r
  have hMpos : 1 ≤ M := Nat.mul_pos hn (pow_pos hp.pos r)
  -- For each u with ¬ p | u, p^r divides C(M - 1 + A + u, A + u)!
  -- Write C(M - 1 + A + u, A + u) = p^r * c(u), where (M + A + u) * c(u) = n * C(M + A + u, A + u).
  have hdiv : ∀ u, ¬ p ∣ u → p ^ r ∣ Nat.choose (M - 1 + (A + u)) (A + u) := by
    intro u hnd
    have hrel := choose_pred_mul_eq M (A + u) hMpos
    have hd1 : p ^ r ∣ (M + (A + u)) * Nat.choose (M - 1 + (A + u)) (A + u) := by
      rw [hrel]
      exact dvd_mul_of_dvd_left (dvd_mul_left (p ^ r) n) _
    have hnd2 : ¬ p ∣ (M + (A + u)) := fun hd => hnd <| by
      have hpMA : p ∣ M + A := dvd_add
        (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) n)
        (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) a)
      exact (Nat.dvd_add_right hpMA).mp (by rwa [← add_assoc] at hd)
    have hcop : Nat.Coprime (p ^ r) (M + (A + u)) :=
      (hp.coprime_iff_not_dvd.mpr hnd2).pow_left r
    exact hcop.dvd_of_dvd_mul_left hd1
  -- Define c(u) = C(M - 1 + A + u, A + u) / p^r.
  set c : ℕ → ℕ := fun u => Nat.choose (M - 1 + (A + u)) (A + u) / p ^ r
  have hc_mul : ∀ u, ¬ p ∣ u → Nat.choose (M - 1 + (A + u)) (A + u) = p ^ r * c u := fun u hu =>
    (Nat.mul_div_cancel' (hdiv u hu)).symm
  have hsum_c : ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
      ((c u : ZMod (p ^ r)) ^ 2) = 0 := by
    have hc_val : ∀ u, ¬ p ∣ u →
        (c u : ZMod (p ^ r)) =
          (n : ZMod (p ^ r)) *
            (Nat.choose ((n + a) * p ^ (r - 1) + u / p) (a * p ^ (r - 1) + u / p) : ZMod (p ^ r)) *
            (u : ZMod (p ^ r))⁻¹ := by
      intro u hnd
      have hrel := choose_pred_mul_eq M (A + u) hMpos
      rw [hc_mul u hnd] at hrel
      have hrel2 : (M + (A + u)) * c u = n * Nat.choose (M + (A + u)) (A + u) := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos r)
        calc p ^ r * ((M + (A + u)) * c u)
            = (M + (A + u)) * (p ^ r * c u) := by ring
          _ = M * Nat.choose (M + (A + u)) (A + u) := hrel
          _ = p ^ r * (n * Nat.choose (M + (A + u)) (A + u)) := by simp only [M]; ring
      have hcast := congrArg (fun x : ℕ => (x : ZMod (p ^ r))) hrel2
      simp only [Nat.cast_mul] at hcast
      have hMAu : ((M + (A + u) : ℕ) : ZMod (p ^ r)) = (u : ZMod (p ^ r)) := by
        simp only [M, A, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
      rw [hMAu] at hcast
      have hC_eq : (Nat.choose (M + (A + u)) (A + u) : ZMod (p ^ r)) =
          (Nat.choose ((n + a) * p ^ (r - 1) + u / p) (a * p ^ (r - 1) + u / p) : ZMod (p ^ r)) := by
        have h1 : M + (A + u) = (n + a) * p ^ r + p * (u / p) + u % p := by
          have := Nat.div_add_mod u p
          simp only [M, A]; linarith
        have h2 : A + u = a * p ^ r + p * (u / p) + u % p := by
          have := Nat.div_add_mod u p
          simp only [A]; linarith
        rw [h1, h2]
        exact choose_shift_mod hp hr (Nat.mod_lt u hp.pos)
      rw [hC_eq] at hcast
      have hu := isUnit_zmod_pow (s := r) hp hnd
      apply hu.mul_left_cancel
      rw [hcast]
      have hinv := ZMod.mul_inv_of_unit _ hu
      calc (n : ZMod (p ^ r)) *
              (Nat.choose ((n + a) * p ^ (r - 1) + u / p) (a * p ^ (r - 1) + u / p) : ZMod (p ^ r))
          = (n : ZMod (p ^ r)) *
              (Nat.choose ((n + a) * p ^ (r - 1) + u / p) (a * p ^ (r - 1) + u / p) : ZMod (p ^ r)) *
              ((u : ZMod (p ^ r)) * (u : ZMod (p ^ r))⁻¹) := by rw [hinv, mul_one]
        _ = (u : ZMod (p ^ r)) * ((n : ZMod (p ^ r)) *
              (Nat.choose ((n + a) * p ^ (r - 1) + u / p) (a * p ^ (r - 1) + u / p) : ZMod (p ^ r)) *
              (u : ZMod (p ^ r))⁻¹) := by ring
    have hrew : ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u), ((c u : ZMod (p ^ r)) ^ 2) =
        (n : ZMod (p ^ r)) ^ 2 * T_sum p r n a 1 := by
      have h1 : ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u), ((c u : ZMod (p ^ r)) ^ 2) =
          (n : ZMod (p ^ r)) ^ 2 *
            ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
              ((Nat.choose ((n + a) * p ^ (r - 1) + u / p) (a * p ^ (r - 1) + u / p) : ZMod (p ^ r)) ^ 2) *
                ((u : ZMod (p ^ r))⁻¹ ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [hc_val u (Finset.mem_filter.mp hu).2]; ring
      rw [h1]
      congr 1
      -- Reindex u = v * p + w into T_sum p r n a 1!
      simp only [T_sum, I_k, pow_one, Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine (Finset.sum_bij (fun x _ => x.1 * p + x.2) ?_ ?_ ?_ ?_).symm
      · rintro ⟨v, w⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx ⊢
        refine ⟨?_, fun hd => hx.2.2 ((Nat.dvd_add_right (dvd_mul_left p v)).mp hd)⟩
        have hpr : p ^ r = p ^ (r - 1) * p := by
          conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
        rw [hpr]
        have h2 : v * p + w < (v + 1) * p := by rw [add_mul, one_mul]; omega
        have h3 : (v + 1) * p ≤ p ^ (r - 1) * p := Nat.mul_le_mul_right p hx.1
        omega
      · rintro ⟨v1, w1⟩ h1 ⟨v2, w2⟩ h2 heq
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at h1 h2
        have hv : v1 = v2 := by
          have hd := congrArg (fun z => z / p) heq
          simp only [mul_add_div_right hp.pos, Nat.div_eq_of_lt h1.2.1, Nat.div_eq_of_lt h2.2.1,
            add_zero] at hd
          exact hd
        subst hv
        have hw : w1 = w2 := Nat.add_left_cancel heq
        subst hw; rfl
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_range] at hu
        refine ⟨⟨u / p, u % p⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
          refine ⟨?_, Nat.mod_lt _ hp.pos, ?_⟩
          · have hpr : p ^ r = p * p ^ (r - 1) := by
              conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
            rw [hpr] at hu
            exact Nat.div_lt_of_lt_mul hu.1
          · intro hd
            apply hu.2
            have hmod := Nat.div_add_mod u p
            exact hmod ▸ dvd_add (dvd_mul_right p _) hd
        · have := Nat.div_add_mod u p; linarith
      · rintro ⟨v, w⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx
        have hdiv_eq : (v * p + w) / p = v := by
          rw [mul_add_div_right hp.pos, Nat.div_eq_of_lt hx.2.1, add_zero]
        rw [hdiv_eq]
    rw [hrew, T_sum_eq_zero hp h5 hr, mul_zero]
  -- Lift sum c(u)^2 = 0 in ZMod (p^r) to sum (p^r * c(u))^2 = 0 in ZMod (p^(3*r))!
  have hdvd_nat : p ^ r ∣ ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u), (c u) ^ 2 := by
    rw [← ZMod.natCast_eq_zero_iff]
    simpa only [Nat.cast_sum, Nat.cast_pow] using hsum_c
  have hsum_nat :
      ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
        (Nat.choose (M - 1 + (A + u)) (A + u)) ^ 2 =
      p ^ (2 * r) *
        ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u), (c u) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hc_mul u (Finset.mem_filter.mp hu).2, mul_pow, ← pow_mul]
    congr 1; ring
  have hcast :
      (∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
        (Nat.choose (M - 1 + (A + u)) (A + u) : ZMod (p ^ (3 * r))) ^ 2) =
      ((∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
        (Nat.choose (M - 1 + (A + u)) (A + u)) ^ 2 : ℕ) : ZMod (p ^ (3 * r))) := by
    simp only [Nat.cast_sum, Nat.cast_pow]
  rw [hcast, hsum_nat, ZMod.natCast_eq_zero_iff, show 3 * r = 2 * r + r by omega, pow_add]
  exact mul_dvd_mul_left (p ^ (2 * r)) hdvd_nat

private lemma A_nat_cong {p n r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hn : 0 < n) (hr : 1 ≤ r) :
    (A_nat (n * p ^ r) : ZMod (p ^ (3 * r))) =
      (A_nat (n * p ^ (r - 1)) : ZMod (p ^ (3 * r))) := by
  set M := n * p ^ r
  set N := n * p ^ (r - 1)
  have hMp : M = p * N := by
    simp only [M, N]
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    ring
  simp only [A_nat, Nat.cast_sum, Nat.cast_pow]
  -- Split range M into multiples of p and non-multiples of p!
  have hsplit : Finset.range M =
      (Finset.range N).image (fun j => p * j) ∪
      (Finset.range M).filter (fun k => ¬ p ∣ k) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hk
      by_cases hd : p ∣ k
      · left
        rcases hd with ⟨j, rfl⟩
        exact ⟨j, by nlinarith, rfl⟩
      · exact Or.inr ⟨hk, hd⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨hk, _⟩)
      · nlinarith
      · exact hk
  have hdisj : Disjoint ((Finset.range N).image (fun j => p * j))
      ((Finset.range M).filter (fun k => ¬ p ∣ k)) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Finset.mem_image, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨j, _, rfl⟩
    exact h2.2 (dvd_mul_right p j)
  rw [hsplit, Finset.sum_union hdisj,
    Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
  have hdiv_part : ∑ j ∈ Finset.range N,
      (Nat.choose (M - 1 + p * j) (p * j) : ZMod (p ^ (3 * r))) ^ 2 =
      ∑ j ∈ Finset.range N, (Nat.choose (N - 1 + j) j : ZMod (p ^ (3 * r))) ^ 2 :=
    Finset.sum_congr rfl fun j hj => A_div_term_cong hp h5 hn hr (Finset.mem_range.mp hj)
  have hndiv_part : ∑ k ∈ (Finset.range M).filter (fun k => ¬ p ∣ k),
      (Nat.choose (M - 1 + k) k : ZMod (p ^ (3 * r))) ^ 2 = 0 := by
    -- Split into n blocks of size p^r!
    have hblocks : (Finset.range M).filter (fun k => ¬ p ∣ k) =
        (Finset.range n ×ˢ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u)).image
          (fun x => x.1 * p ^ r + x.2) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product]
      constructor
      · rintro ⟨hk, hnd⟩
        refine ⟨(k / p ^ r, k % p ^ r), ⟨?_, Nat.mod_lt _ (pow_pos hp.pos r), ?_⟩, ?_⟩
        · dsimp only [M] at hk
          exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hk)
        · intro hd
          apply hnd
          have hmod := Nat.div_add_mod k (p ^ r)
          have hp1 : p ∣ p ^ r * (k / p ^ r) := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
          exact hmod ▸ dvd_add hp1 hd
        · have := Nat.div_add_mod k (p ^ r); linarith
      · rintro ⟨⟨a, u⟩, ⟨ha, hu, hnd⟩, rfl⟩
        dsimp only
        refine ⟨?_, fun hd => hnd ?_⟩
        · have h1 : a * p ^ r + u < (a + 1) * p ^ r := by rw [add_mul, one_mul]; omega
          have h2 : (a + 1) * p ^ r ≤ n * p ^ r := Nat.mul_le_mul_right _ ha
          dsimp only [M]; omega
        · exact (Nat.dvd_add_right (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) a)).mp hd
    have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * p ^ r + x.2)
        ((Finset.range n ×ˢ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u) : Finset (ℕ × ℕ)) :
          Set (ℕ × ℕ)) := by
      rintro ⟨a1, u1⟩ h1 ⟨a2, u2⟩ h2 heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at h1 h2
      dsimp only at heq
      have ha : a1 = a2 := by
        have hd := congrArg (fun z => z / p ^ r) heq
        simp only [mul_add_div_right (pow_pos hp.pos r), Nat.div_eq_of_lt h1.2.1,
          Nat.div_eq_of_lt h2.2.1, add_zero] at hd
        exact hd
      subst ha
      have hu : u1 = u2 := Nat.add_left_cancel heq
      subst hu; rfl
    rw [hblocks, Finset.sum_image hinj, Finset.sum_product]
    refine Finset.sum_eq_zero fun a _ => ?_
    exact A_ndiv_block_zero hp h5 hn hr
  rw [hdiv_part, hndiv_part, add_zero]

end OMA_A003161

theorem OMA.solution : type_of% @OMA.S_oeis_a003161.main := by
  intro p n k hp h5 hn hk
  have hMpos : 1 ≤ n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos k)
  have hNpos : 1 ≤ n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hp.pos (k - 1))
  have h2M := OMA_A003161.two_mul_b_eq (n * p ^ k) hMpos
  have h2N := OMA_A003161.two_mul_b_eq (n * p ^ (k - 1)) hNpos
  have hC := OMA_A003161.choose_central_pred_cong hp h5 hn hk
  have hA := OMA_A003161.A_nat_cong hp h5 hn hk
  have h2_eq : ((2 * b (n * p ^ k) : ℤ) : ZMod (p ^ (3 * k))) =
      ((2 * b (n * p ^ (k - 1)) : ℤ) : ZMod (p ^ (3 * k))) := by
    rw [h2M, h2N]
    push_cast
    rw [hC, hA]
  have h2u : IsUnit (2 : ZMod (p ^ (3 * k))) := by
    change IsUnit ((2 : ℕ) : ZMod (p ^ (3 * k)))
    exact OMA_A003161.isUnit_zmod_pow hp (fun h => by have := Nat.le_of_dvd (by decide) h; omega)
  have hb_eq : ((b (n * p ^ k) : ℤ) : ZMod (p ^ (3 * k))) =
      ((b (n * p ^ (k - 1)) : ℤ) : ZMod (p ^ (3 * k))) := by
    apply h2u.mul_left_cancel
    simpa only [Int.cast_mul, Int.cast_ofNat] using h2_eq
  have hsub : ((b (n * p ^ (k - 1)) - b (n * p ^ k) : ℤ) : ZMod (p ^ (3 * k))) = 0 := by
    rw [Int.cast_sub, sub_eq_zero]; exact hb_eq.symm
  have hdvd : ((p ^ (3 * k) : ℕ) : ℤ) ∣ (b (n * p ^ (k - 1)) - b (n * p ^ k)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hsub
  have hdvd' : (p : ℤ) ^ (3 * k) ∣ (b (n * p ^ (k - 1)) - b (n * p ^ k)) := by
    simpa only [Nat.cast_pow] using hdvd
  exact Int.modEq_iff_dvd.mpr hdvd'
