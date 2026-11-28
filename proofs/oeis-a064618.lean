import OMAStatements.S_oeis_a064618
import Mathlib

/-!
# OEIS A064618: eventual periodicity modulo `k` with period `φ(k)`

Here `a(n) = ∑_{j ≤ n} S(n, j) · (j!)^2`.

Write `F(n, j) = S(n, j) · j!` (the number of surjections from an `n`-set onto a `j`-set).

**Step 1.** `i^n = ∑_{j ≤ i} C(i, j) F(n, j)` for all `n, i` (induction on `n`, using
`F(n+1, j+1) = (j+1) (F(n, j+1) + F(n, j))` and `(j+1) C(i, j+1) = (i-j) C(i, j)`).

**Step 2.** Solving Step 1 for `F(n, j)` by induction on `j`: if `k ∣ i^n' - i^n` for every `i`,
then `k ∣ F(n', j) - F(n, j)` for every `j`.

**Step 3.** For `n ≥ k ≥ 1` we have `k ∣ i^(n + φ(k)) - i^n` for every `i`: check each prime
power `p^e ∣ k`. If `p ∣ i` then `p^e ∣ i^n` because `e < k ≤ n`; otherwise Euler's theorem
gives `p^e ∣ i^φ(k) - 1`.

So for `n ≥ k` every `F(n + φ(k), j) - F(n, j)` is divisible by `k`, and so is the difference
of `∑_j F(·, j) g(j)` for any weights `g` (the terms with `j > n` vanish since `S(n, j) = 0`).

The sequence is the case `g(j) = j!`; the period starts at `N = k`.
-/

namespace OMA.A064618

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

/-- Step 3: `i^(n + φ(k)) ≡ i^n (mod k)` once `n ≥ k`. -/
lemma pow_period {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) (i : ℕ) :
    (k : ℤ) ∣ (i : ℤ) ^ (n + k.totient) - (i : ℤ) ^ n := by
  have hnat : k ∣ i ^ n * (i ^ k.totient - 1) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p e hp hpe
    by_cases hpi : p ∣ i
    · -- `p ∣ i`: then `p^e ∣ i^n` since `e < k ≤ n`
      have he : e ≤ n := by
        have h1 : p ^ e ≤ k := Nat.le_of_dvd (by omega) hpe
        have h2 : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        have h3 : e < 2 ^ e := Nat.lt_two_pow_self
        omega
      exact Dvd.dvd.mul_right ((pow_dvd_pow_of_dvd hpi e).trans (pow_dvd_pow i he)) _
    · -- `p ∤ i`: Euler's theorem modulo `p^e`
      have hcop : Nat.Coprime i (p ^ e) :=
        Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
      obtain ⟨m, hm⟩ := Nat.totient_dvd_of_dvd hpe
      have h1 : i ^ k.totient ≡ 1 [MOD p ^ e] := by
        rw [hm, pow_mul]
        simpa using (Nat.ModEq.pow_totient hcop).pow m
      have hipos : 1 ≤ i ^ k.totient :=
        Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => hpi (h0 ▸ dvd_zero p))
      exact Dvd.dvd.mul_left ((Nat.modEq_iff_dvd' hipos).mp h1.symm) _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h1 : n ≠ 0 := by omega
    simp [h1]
  · have hipos : 1 ≤ i ^ k.totient := Nat.one_le_pow _ _ hi
    have hcast : ((i ^ n * (i ^ k.totient - 1) : ℕ) : ℤ)
        = (i : ℤ) ^ (n + k.totient) - (i : ℤ) ^ n := by
      push_cast [Nat.cast_sub hipos]
      ring
    rw [← hcast]
    exact Int.natCast_dvd_natCast.mpr hnat

/-- For `n ≥ k ≥ 1`: `F(n + φ(k), j) ≡ F(n, j) (mod k)` for every `j`. -/
lemma F_period (hS : IsStirling S) {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) (j : ℕ) :
    (k : ℤ) ∣ F S (n + k.totient) j - F S n j :=
  F_dvd_sub hS k n (n + k.totient) (pow_period hk hn) j

/-- The general conclusion: `∑_{j ≤ n} F(n, j) g(j)` is periodic modulo `k` from `n = k` on. -/
lemma sum_period (hS : IsStirling S) (g : ℕ → ℤ) {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) :
    (k : ℤ) ∣ ∑ j ∈ Finset.range (n + k.totient + 1), F S (n + k.totient) j * g j
      - ∑ j ∈ Finset.range (n + 1), F S n j * g j := by
  -- extend the second sum: its extra terms vanish
  have hext : ∑ j ∈ Finset.range (n + 1), F S n j * g j
      = ∑ j ∈ Finset.range (n + k.totient + 1), F S n j * g j := by
    refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
    · rw [Finset.mem_range] at hj ⊢; omega
    · rw [Finset.mem_range] at hj
      rw [F_eq_zero hS (by omega), zero_mul]
  rw [hext, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j _ => ?_
  rw [← sub_mul]
  exact Dvd.dvd.mul_right (F_period hS hk hn j) _

open OMA.S_oeis_a064618 in
/-- The statement's `stirling2` obeys the four rules. -/
lemma isStirling : IsStirling stirling2 where
  zero_zero := by simp [stirling2]
  succ_zero := fun n => by simp [stirling2]
  zero_succ := fun j => by simp [stirling2]
  succ_succ := fun n j => by simp [stirling2]

end OMA.A064618

open OMA.A064618 OMA.S_oeis_a064618 in
theorem OMA.solution : type_of% @OMA.S_oeis_a064618.main := by
  intro k hk
  refine ⟨k, fun n hn => ?_⟩
  have h := sum_period isStirling (fun j => ((j.factorial : ℕ) : ℤ)) hk hn
  -- `a m` is the weighted sum with these weights
  have e : ∀ m : ℕ, (a m : ℤ)
      = ∑ j ∈ Finset.range (m + 1), F stirling2 m j * ((j.factorial : ℕ) : ℤ) := by
    intro m
    unfold a F
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, e, e]
  have hneg := (dvd_neg (a := (k : ℤ))).mpr h
  rwa [neg_sub] at hneg
