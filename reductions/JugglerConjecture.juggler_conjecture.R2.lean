import FormalConjectures.Wikipedia.JugglerConjecture
import Mathlib.Order.Filter.Cofinite

/-!
# Juggler: no escape to infinity and no nontrivial odd periodic point

`H1` says that no positive orbit tends to infinity. It does not ask for a
numerical bound on the orbit. An injective sequence of natural numbers tends
to infinity, so `H1` forces a repeated value and hence a periodic point.

`H2` excludes positive-period returns only for odd integers greater than one.
The minimum of a positive periodic orbit cannot be even and greater than one,
because an even Juggler step strictly decreases. Thus its minimum must be one.

The general recurrence/cycle decomposition is related to the Collatz reduction
CollatzConjecture.collatz_conjecture.R1 by @Dugongue. The minimum-orbit argument
here restricts the cycle hypothesis to odd integers at least three.
-/

namespace OMA.R_JugglerConjecture_juggler_conjecture_R2

open JugglerConjecture

/-- No positive Juggler orbit tends to infinity. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n →
    ¬ Filter.Tendsto (fun k : ℕ => jugglerStep^[k] n) Filter.atTop Filter.atTop

/-- No odd integer greater than one returns to itself after a positive number of steps. -/
def H2 : Prop :=
  ∀ n k : ℕ, 1 < n → Odd n → 0 < k → jugglerStep^[k] n ≠ n

lemma step_pos {n : ℕ} (hn : 0 < n) : 0 < jugglerStep n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  unfold jugglerStep
  split
  all_goals
    apply Nat.lt_of_lt_of_le Nat.zero_lt_one
    apply (Nat.one_le_floor_iff _).mpr
    exact Real.one_le_rpow hn1 (by norm_num)

lemma iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < jugglerStep^[k] n := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (step_pos hn)

lemma step_lt_of_even {n : ℕ} (hn : 1 < n) (he : Even n) : jugglerStep n < n := by
  unfold jugglerStep
  rw [if_pos he, ← Real.sqrt_eq_rpow]
  apply (Nat.floor_lt' (by omega : n ≠ 0)).mpr
  apply Real.sqrt_lt_self_iff.mpr
  exact_mod_cast hn

lemma exists_repeat {n : ℕ}
    (hn : ¬ Filter.Tendsto (fun k : ℕ => jugglerStep^[k] n)
      Filter.atTop Filter.atTop) :
    ∃ i j : ℕ, i < j ∧ jugglerStep^[i] n = jugglerStep^[j] n := by
  classical
  by_contra hrepeat
  apply hn
  apply Function.Injective.nat_tendsto_atTop
  intro i j heq
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hrepeat ⟨i, j, hlt, heq⟩
  · exact hrepeat ⟨j, i, hgt, heq.symm⟩

theorem main : H1 → H2 → type_of% @JugglerConjecture.juggler_conjecture := by
  classical
  intro h1 h2 n hn
  obtain ⟨i, j, hij, heq⟩ := exists_repeat (h1 n hn)
  set x := jugglerStep^[i] n with hx
  have hxpos : 0 < x := iterate_pos hn i
  have hperiod : jugglerStep^[j - i] x = x := by
    rw [hx, ← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
    exact heq.symm
  have hex : ∃ y : ℕ, ∃ t : ℕ, jugglerStep^[t] x = y := ⟨x, 0, rfl⟩
  let y := Nat.find hex
  obtain ⟨t, ht⟩ : ∃ t : ℕ, jugglerStep^[t] x = y := Nat.find_spec hex
  have hypos : 0 < y := ht ▸ iterate_pos hxpos t
  have hymin : y ≤ jugglerStep y := by
    apply Nat.find_le
    refine ⟨t + 1, ?_⟩
    rw [Function.iterate_succ_apply', ht]
  have hyperiod : jugglerStep^[j - i] y = y := by
    rw [← ht, ← Function.iterate_add_apply, Nat.add_comm (j - i) t,
      Function.iterate_add_apply, hperiod]
  have hyone : y = 1 := by
    by_contra hy
    have hygt : 1 < y := by omega
    rcases Nat.even_or_odd y with heven | hodd
    · exact (step_lt_of_even hygt heven).not_ge hymin
    · exact h2 y (j - i) hygt hodd (by omega) hyperiod
  refine ⟨t + i, ?_⟩
  rw [Function.iterate_add_apply, ← hx, ht, hyone]

end OMA.R_JugglerConjecture_juggler_conjecture_R2
