import OMAStatements.S_oeis_a299154
import Mathlib

namespace OMA.A299154Proof

open OMA.S_oeis_a299154

theorem step_le (x : ℕ) : (Nat.digits 10 x).sum ≤ x := Nat.digit_sum_le 10 x

theorem step_lt (x : ℕ) (hx : 10 ≤ x) : (Nat.digits 10 x).sum < x := by
  have h1 : 0 < x := by omega
  rw [Nat.digits_def' (by norm_num) h1, List.sum_cons]
  have h2 := Nat.digit_sum_le 10 (x / 10)
  have h3 : 0 < x / 10 := by omega
  omega

theorem step_mod (x : ℕ) : (Nat.digits 10 x).sum % 9 = x % 9 :=
  (Nat.modEq_nine_digits_sum x).symm

theorem iter_mod (m : ℕ) : ∀ k : ℕ,
    ((fun y => (Nat.digits 10 y).sum)^[k] m) % 9 = m % 9 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', step_mod, ih]

theorem iter_le (m : ℕ) : ∀ k : ℕ,
    (fun y => (Nat.digits 10 y).sum)^[k] m ≤ max 9 (m - k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set x := (fun y => (Nat.digits 10 y).sum)^[k] m
    by_cases hx : 10 ≤ x
    · have := step_lt x hx
      omega
    · have := step_le x
      omega

theorem dr_eq (p d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 8) (hp : p % 9 = d) :
    digitalRoot p = d := by
  unfold digitalRoot
  have h1 := iter_mod p p
  have h2 := iter_le p p
  rw [Nat.sub_self] at h2
  set x := (fun y => (Nat.digits 10 y).sum)^[p] p
  omega

theorem inf (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 8) (hc : Nat.Coprime d 9) :
    {p : ℕ | Nat.Prime p ∧ digitalRoot p = d}.Infinite := by
  have hu : IsUnit (d : ZMod 9) := (ZMod.isUnit_iff_coprime d 9).mpr hc
  apply (Nat.infinite_setOfPred_prime_and_eq_mod hu).mono
  intro p hp
  refine ⟨hp.1, ?_⟩
  apply dr_eq p d hd1 hd2
  have := (ZMod.natCast_eq_natCast_iff' p d 9).mp hp.2
  omega

end OMA.A299154Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a299154.main := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact OMA.A299154Proof.inf _ (by norm_num) (by norm_num) (by norm_num)
