import OMAStatements.S_oeis_a330715
import Mathlib

namespace A330715

open OMA.S_oeis_a330715 in
lemma step (n : ℕ) : a (n + 4) = a (n + 3) % a (n + 1) + a (n + 2) + 1 := by
  rw [a]

open OMA.S_oeis_a330715 in
lemma key (j : ℕ) :
    a (2 * j + 6) = j ^ 2 + 3 ∧ a (2 * j + 7) = j ^ 2 + j + 4 ∧
      a (2 * j + 8) = j ^ 2 + 2 * j + 4 := by
  induction j with
  | zero => refine ⟨by decide, by decide, by decide⟩
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have h4 : a (2 * j + 9) = j ^ 2 + 3 * j + 6 := by
      have e : a (2 * j + 9) = a (2 * j + 8) % a (2 * j + 6) + a (2 * j + 7) + 1 :=
        step (2 * j + 5)
      have hm : (j ^ 2 + 2 * j + 4) % (j ^ 2 + 3) = 2 * j + 1 := by
        have e2 : j ^ 2 + 2 * j + 4 = (2 * j + 1) + 1 * (j ^ 2 + 3) := by ring
        rw [e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
        nlinarith [sq_nonneg (j - 1 : ℤ), sq_nonneg j]
      rw [e, h1, h2, h3, hm]; ring
    have h5 : a (2 * j + 10) = j ^ 2 + 4 * j + 7 := by
      have e : a (2 * j + 10) = a (2 * j + 9) % a (2 * j + 7) + a (2 * j + 8) + 1 :=
        step (2 * j + 6)
      have hm : (j ^ 2 + 3 * j + 6) % (j ^ 2 + j + 4) = 2 * j + 2 := by
        have e2 : j ^ 2 + 3 * j + 6 = (2 * j + 2) + 1 * (j ^ 2 + j + 4) := by ring
        rw [e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
        nlinarith [sq_nonneg j]
      rw [e, h4, h2, h3, hm]; ring
    refine ⟨?_, ?_, ?_⟩
    · have e : 2 * (j + 1) + 6 = 2 * j + 8 := by ring
      rw [e, h3]; ring
    · have e : 2 * (j + 1) + 7 = 2 * j + 9 := by ring
      rw [e, h4]; ring
    · have e : 2 * (j + 1) + 8 = 2 * j + 10 := by ring
      rw [e, h5]; ring

end A330715

open OMA.S_oeis_a330715 in
theorem OMA.solution : type_of% @OMA.S_oeis_a330715.main := by
  have closed : ∀ n : ℕ, 5 < n →
      8 * (a n : ℤ) = 99 - 3 * (-1 : ℤ) ^ n - 24 * (n : ℤ) + 2 * (n : ℤ) ^ 2 := by
    intro n hn
    rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have e : n = 2 * j + 6 := by omega
      subst e
      have h := (A330715.key j).1
      have hp : (-1 : ℤ) ^ (2 * j + 6) = 1 := by
        have : 2 * j + 6 = 2 * (j + 3) := by ring
        rw [this, pow_mul]; norm_num
      rw [h, hp]; push_cast; ring
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have e : n = 2 * j + 7 := by omega
      subst e
      have h := (A330715.key j).2.1
      have hp : (-1 : ℤ) ^ (2 * j + 7) = -1 := by
        have : 2 * j + 7 = 2 * (j + 3) + 1 := by ring
        rw [this, pow_succ, pow_mul]; norm_num
      rw [h, hp]; push_cast; ring
  refine ⟨?_, closed⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have e1 : m + 10 - 1 = m + 9 := by omega
  have e3 : m + 10 - 3 = m + 7 := by omega
  have e4 : m + 10 - 4 = m + 6 := by omega
  rw [e1, e3, e4]
  have c0 := closed (m + 10) (by omega)
  have c1 := closed (m + 9) (by omega)
  have c3 := closed (m + 7) (by omega)
  have c4 := closed (m + 6) (by omega)
  have p10 : (-1 : ℤ) ^ (m + 10) = (-1) ^ m := by
    rw [pow_add]; norm_num
  have p9 : (-1 : ℤ) ^ (m + 9) = -(-1) ^ m := by
    rw [pow_add]; norm_num
  have p7 : (-1 : ℤ) ^ (m + 7) = -(-1) ^ m := by
    rw [pow_add]; norm_num
  have p6 : (-1 : ℤ) ^ (m + 6) = (-1) ^ m := by
    rw [pow_add]; norm_num
  rw [p10] at c0
  rw [p9] at c1
  rw [p7] at c3
  rw [p6] at c4
  push_cast at c0 c1 c3 c4
  linarith
