import OMAStatements.S_oeis_a246048
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Finset OMA.S_oeis_a246048

private lemma val_pow (p : ℕ) [Fact p.Prime] (m : ℕ) :
    padicValNat p (p ^ m).factorial = ∑ i ∈ range m, p ^ i := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', padicValNat_factorial_mul, ih, sum_range_succ]

theorem OMA.solution : type_of% @OMA.S_oeis_a246048.main := by
  intro p k hp h
  have : Fact p.Prime := ⟨hp⟩
  unfold isTerm at h
  set m := k + 1 with hm
  set n := p ^ m with hn
  set S := ∑ i ∈ range m, p ^ i with hS
  have hSpos : 0 < S := by
    rw [hS, hm, sum_range_succ']
    simp
  have hfn : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  have h2 : n.factorial ^ n * (n.factorial * n.factorial) ∣ (n ^ 2).factorial := by
    refine dvd_trans (mul_dvd_mul_left _ ?_) h
    have := Nat.factorial_mul_factorial_dvd_factorial_add n n
    rwa [← two_mul] at this
  have hv : padicValNat p n.factorial = S := val_pow p m
  have hsq : padicValNat p (n ^ 2).factorial = S + n * S := by
    rw [hn, ← pow_mul, val_pow, mul_two, sum_range_add, ← hS]
    congr 1
    rw [hS, mul_sum]
    exact sum_congr rfl fun i _ => pow_add _ _ _
  have hle := (padicValNat_dvd_iff_le (p := p) (Nat.factorial_ne_zero (n^2))).1
    (dvd_trans pow_padicValNat_dvd h2)
  rw [padicValNat.mul (pow_ne_zero _ hfn) (mul_ne_zero hfn hfn), padicValNat.pow,
    padicValNat.mul hfn hfn, hv, hsq] at hle
  omega
