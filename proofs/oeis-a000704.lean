import OMAStatements.S_oeis_a000704
import Mathlib

namespace A000704

open Finset OMA.S_oeis_a000704

lemma matchings_zero (n : ℕ) : matchings n 0 = 1 := by
  simp [matchings]

lemma matchings_eq_zero {n k : ℕ} (h : n < 2 * k) : matchings n k = 0 := by
  unfold matchings
  rw [Nat.choose_eq_zero_of_lt h, zero_mul]

/-- Termwise recurrence: the last label is fixed or matched with one of the others. -/
lemma matchings_step (n k : ℕ) :
    matchings (n + 2) (k + 1) = matchings (n + 1) (k + 1) + (n + 1) * matchings n k := by
  unfold matchings
  have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
  have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have hd : (2 * k + 1).doubleFactorial = (2 * k + 1) * (2 * k - 1).doubleFactorial := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h3 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
      have h4 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [h3, h4, Nat.doubleFactorial_add_two]
  have hp : (n + 2).choose (2 * k + 1 + 1) =
      (n + 1).choose (2 * k + 1) + (n + 1).choose (2 * k + 1 + 1) :=
    Nat.choose_succ_succ' (n + 1) (2 * k + 1)
  have hc : (n + 1) * n.choose (2 * k) = (n + 1).choose (2 * k + 1) * (2 * k + 1) :=
    Nat.add_one_mul_choose_eq n (2 * k)
  rw [h2, h1, hp, hd]
  have hc' : (n + 1) * (n.choose (2 * k) * (2 * k - 1).doubleFactorial) =
      (n + 1).choose (2 * k + 1) * (2 * k + 1) * (2 * k - 1).doubleFactorial := by
    rw [← mul_assoc, hc]
  rw [hc']
  ring

/-- Sum over even numbers of transpositions, with a free upper bound. -/
def Ae (n N : ℕ) : ℕ := ∑ j ∈ range N, matchings n (2 * j)

/-- Sum over odd numbers of transpositions, with a free upper bound. -/
def De (n N : ℕ) : ℕ := ∑ j ∈ range N, matchings n (2 * j + 1)

lemma Ae_step (n N : ℕ) :
    Ae (n + 2) (N + 1) = Ae (n + 1) (N + 1) + (n + 1) * De n N := by
  unfold Ae De
  rw [sum_range_succ', sum_range_succ', mul_sum]
  have h : ∀ j, matchings (n + 2) (2 * (j + 1)) =
      matchings (n + 1) (2 * (j + 1)) + (n + 1) * matchings n (2 * j + 1) := by
    intro j
    have h0 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [h0]
    exact matchings_step n (2 * j + 1)
  simp only [h, sum_add_distrib, Nat.mul_zero, matchings_zero]
  ring

lemma De_step (n N : ℕ) : De (n + 2) N = De (n + 1) N + (n + 1) * Ae n N := by
  unfold Ae De
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun j _ => matchings_step n (2 * j))

lemma Ae_eq (n N : ℕ) (h : n + 1 ≤ N) : Ae n N = a n := by
  unfold Ae a
  symm
  apply sum_subset
  · intro x hx
    rw [mem_range] at hx ⊢
    omega
  · intro x _ hx
    rw [mem_range] at hx
    apply matchings_eq_zero
    omega

/-- The companion sequence: involutions with an odd number of transpositions. -/
def d (n : ℕ) : ℕ := De n (n + 1)

lemma De_eq (n N : ℕ) (h : n + 1 ≤ N) : De n N = d n := by
  unfold d De
  symm
  apply sum_subset
  · intro x hx
    rw [mem_range] at hx ⊢
    omega
  · intro x _ hx
    rw [mem_range] at hx
    apply matchings_eq_zero
    omega

lemma a_rec (n : ℕ) : a (n + 2) = a (n + 1) + (n + 1) * d n := by
  have h := Ae_step n (n + 3)
  rw [Ae_eq (n + 2) (n + 3 + 1) (by omega), Ae_eq (n + 1) (n + 3 + 1) (by omega),
    De_eq n (n + 3) (by omega)] at h
  exact h

lemma d_rec (n : ℕ) : d (n + 2) = d (n + 1) + (n + 1) * a n := by
  have h := De_step n (n + 3)
  rw [De_eq (n + 2) (n + 3) (by omega), De_eq (n + 1) (n + 3) (by omega),
    Ae_eq n (n + 3) (by omega)] at h
  exact h

end A000704

theorem OMA.solution : type_of% @OMA.S_oeis_a000704.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : m + 5 - 1 = m + 4 := by omega
  have e2 : m + 5 - 2 = m + 3 := by omega
  have e3 : m + 5 - 3 = m + 2 := by omega
  have e4 : m + 5 - 4 = m + 1 := by omega
  have e5 : m + 5 - 5 = m := by omega
  rw [e1, e2, e3, e4, e5]
  have h5 : (OMA.S_oeis_a000704.a (m + 5) : ℤ) =
      OMA.S_oeis_a000704.a (m + 4) + ((m : ℤ) + 4) * A000704.d (m + 3) := by
    have := A000704.a_rec (m + 3)
    exact_mod_cast this
  have h4 : (OMA.S_oeis_a000704.a (m + 4) : ℤ) =
      OMA.S_oeis_a000704.a (m + 3) + ((m : ℤ) + 3) * A000704.d (m + 2) := by
    have := A000704.a_rec (m + 2)
    exact_mod_cast this
  have h3 : (OMA.S_oeis_a000704.a (m + 3) : ℤ) =
      OMA.S_oeis_a000704.a (m + 2) + ((m : ℤ) + 2) * A000704.d (m + 1) := by
    have := A000704.a_rec (m + 1)
    exact_mod_cast this
  have g3 : (A000704.d (m + 3) : ℤ) =
      A000704.d (m + 2) + ((m : ℤ) + 2) * OMA.S_oeis_a000704.a (m + 1) := by
    have := A000704.d_rec (m + 1)
    exact_mod_cast this
  have g2 : (A000704.d (m + 2) : ℤ) =
      A000704.d (m + 1) + ((m : ℤ) + 1) * OMA.S_oeis_a000704.a m := by
    have := A000704.d_rec m
    exact_mod_cast this
  push_cast
  linear_combination h5 - 2 * h4 + h3 + ((m : ℤ) + 4) * g3 - ((m : ℤ) + 2) * g2
