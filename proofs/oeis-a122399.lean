import OMAStatements.S_oeis_a122399
import Mathlib

/-!
# OEIS A122399: `a(n + p - 1) ≡ a(n) (mod p)` for `n ≥ 1`

Here `a(n) = ∑_{j ≤ n} j^n · j! · S(n, j)`. Write `F(n, j) = S(n, j) · j!` (the number of
surjections from an `n`-set onto a `j`-set), so `a(n) = ∑_j j^n F(n, j)`.

**Step 1.** `i^n = ∑_{j ≤ i} C(i, j) F(n, j)` for all `n, i` (induction on `n`, using
`F(n+1, j+1) = (j+1) (F(n, j+1) + F(n, j))` and `(j+1) C(i, j+1) = (i-j) C(i, j)`).

**Step 2.** Solving Step 1 for `F(n, j)` by induction on `j`: if `k ∣ i^n' - i^n` for every `i`,
then `k ∣ F(n', j) - F(n, j)` for every `j`.

**Step 3.** By Fermat's little theorem `i^(n + p - 1) ≡ i^n (mod p)` for every `i` when `n ≥ 1`.
So `F(n + p - 1, j) ≡ F(n, j)` and `j^(n + p - 1) ≡ j^n` modulo `p`, and the two sums agree
term by term (the terms of `a(n)` with `j > n` vanish since `S(n, j) = 0`).
-/

namespace OMA.A122399

/-- The four defining rules of the Stirling numbers of the second kind. -/
structure IsStirling (S : ℕ → ℕ → ℕ) : Prop where
  zero_zero : S 0 0 = 1
  succ_zero : ∀ n, S (n + 1) 0 = 0
  zero_succ : ∀ j, S 0 (j + 1) = 0
  succ_succ : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j

/-- `F(n, j) = S(n, j) · j!`, the number of surjections from `n` points onto `j` points. -/
def F (S : ℕ → ℕ → ℕ) (n j : ℕ) : ℤ := (S n j : ℤ) * (j.factorial : ℤ)

variable {S : ℕ → ℕ → ℕ}

lemma F_succ (hS : IsStirling S) (n j : ℕ) :
    F S (n + 1) (j + 1) = ((j : ℤ) + 1) * (F S n (j + 1) + F S n j) := by
  unfold F
  rw [hS.succ_succ, Nat.factorial_succ]
  push_cast
  ring

/-- `S(n, j) = 0` when `j > n`. -/
lemma S_eq_zero (hS : IsStirling S) : ∀ n j : ℕ, n < j → S n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact hS.zero_succ j'
  | succ n ih =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hS.succ_succ, ih (j' + 1) (by omega), ih j' (by omega), Nat.mul_zero]

lemma F_eq_zero (hS : IsStirling S) {n j : ℕ} (h : n < j) : F S n j = 0 := by
  unfold F
  rw [S_eq_zero hS n j h]
  simp

/-- Step 1: `i^n = ∑_{j ≤ i} C(i, j) F(n, j)`. -/
lemma pow_eq_sum (hS : IsStirling S) (n i : ℕ) :
    (i : ℤ) ^ n = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℤ) * F S n j := by
  induction n with
  | zero =>
    rw [Finset.sum_range_succ']
    simp [F, hS.zero_zero, hS.zero_succ]
  | succ n ih =>
    rw [pow_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    have h0 : F S (n + 1) 0 = 0 := by simp [F, hS.succ_zero]
    rw [h0, mul_zero, add_zero]
    -- expand `F(n+1, j+1)`
    have hA : ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * F S (n + 1) (j + 1)
        = ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n (j + 1)
          + ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [F_succ hS]; ring
    -- first part: shift the index
    have hB : ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n (j + 1)
        = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℤ) * (j : ℤ) * F S n j := by
      rw [Finset.sum_range_succ' _ i]
      simp
    -- second part: `(j+1) C(i, j+1) = (i-j) C(i, j)`
    have hC : ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) * F S n j
        = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℤ) * ((i : ℤ) - j) * F S n j := by
      rw [Finset.sum_range_succ _ i]
      simp only [sub_self, mul_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≤ i := (Finset.mem_range.mp hj).le
      have hc : (i.choose (j + 1) : ℤ) * ((j : ℤ) + 1) = (i.choose j : ℤ) * ((i : ℤ) - j) := by
        have h := congrArg (Nat.cast : ℕ → ℤ) (Nat.choose_succ_right_eq i j)
        push_cast [Nat.cast_sub hji] at h
        linarith
      rw [hc]
    rw [hA, hB, hC, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Step 2: a congruence between all `n`-th and `n'`-th powers passes to `F(n, ·)`, `F(n', ·)`. -/
lemma F_dvd_sub (hS : IsStirling S) (k : ℤ) (n n' : ℕ)
    (h : ∀ i : ℕ, k ∣ (i : ℤ) ^ n' - (i : ℤ) ^ n) : ∀ j : ℕ, k ∣ F S n' j - F S n j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have e1 := pow_eq_sum hS n j
    have e2 := pow_eq_sum hS n' j
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at e1 e2
    have key : F S n' j - F S n j = ((j : ℤ) ^ n' - (j : ℤ) ^ n)
        - ∑ l ∈ Finset.range j, (j.choose l : ℤ) * (F S n' l - F S n l) := by
      rw [e1, e2]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
    exact dvd_sub (h j)
      (Finset.dvd_sum fun l hl => Dvd.dvd.mul_left (ih l (Finset.mem_range.mp hl)) _)

open OMA.S_oeis_a122399 in
/-- The statement's `stirling2` obeys the four rules. -/
lemma isStirling : IsStirling stirling2 where
  zero_zero := by simp [stirling2]
  succ_zero := fun n => by simp [stirling2]
  zero_succ := fun j => by simp [stirling2]
  succ_succ := fun n j => by simp [stirling2]

end OMA.A122399

open OMA.A122399 OMA.S_oeis_a122399 in
theorem OMA.solution : type_of% @OMA.S_oeis_a122399.main := by
  intro p n hp hn
  have : Fact p.Prime := ⟨hp⟩
  -- Fermat: all `(n+p-1)`-th and `n`-th powers agree modulo `p`
  have hpow : ∀ i : ℕ, (p : ℤ) ∣ (i : ℤ) ^ (n + (p - 1)) - (i : ℤ) ^ n := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hp1 : n' + 1 + (p - 1) = n' + p := by have := hp.pos; omega
    push_cast
    rw [hp1, pow_add, ZMod.pow_card, pow_succ]
    ring
  have hF := F_dvd_sub isStirling (p : ℤ) n (n + (p - 1)) hpow
  -- `a m = ∑_j j^m F(m, j)`
  have e : ∀ m : ℕ, (a m : ℤ)
      = ∑ j ∈ Finset.range (m + 1), (j : ℤ) ^ m * F stirling2 m j := by
    intro m
    unfold a F
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- extend the sum for `a n`: the extra terms vanish
  have hext : ∑ j ∈ Finset.range (n + 1), (j : ℤ) ^ n * F stirling2 n j
      = ∑ j ∈ Finset.range (n + (p - 1) + 1), (j : ℤ) ^ n * F stirling2 n j := by
    refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
    · rw [Finset.mem_range] at hj ⊢; omega
    · rw [Finset.mem_range] at hj
      rw [F_eq_zero isStirling (by omega), mul_zero]
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, e, e, hext, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j _ => ?_
  have key : (j : ℤ) ^ n * F stirling2 n j
        - (j : ℤ) ^ (n + (p - 1)) * F stirling2 (n + (p - 1)) j
      = -(((j : ℤ) ^ (n + (p - 1)) - (j : ℤ) ^ n) * F stirling2 (n + (p - 1)) j
          + (j : ℤ) ^ n * (F stirling2 (n + (p - 1)) j - F stirling2 n j)) := by ring
  rw [key]
  exact (dvd_neg (a := (p : ℤ))).mpr
    (dvd_add (Dvd.dvd.mul_right (hpow j) _) (Dvd.dvd.mul_left (hF j) _))
