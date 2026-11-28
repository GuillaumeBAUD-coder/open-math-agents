import OMAStatements.S_oeis_a087445
import Mathlib

/-!
Proof for A087445. Halving leads from any positive n to an odd x; then 3x+1 and further halving
lead to an odd y not divisible by 3. If y is 1 mod 4 it is 1 or 5 mod 12. Otherwise the second
iterate (3y+1)/2 is odd, not divisible by 3, and (3y+1)/2 + 1 = 3(y+1)/2 is divisible by a
smaller power of 2 than y + 1; induct on that power.
-/

namespace OMA.P_oeis_a087445

open OMA.S_oeis_a087445

/-- From a positive m not divisible by 3, halving reaches an odd number not divisible by 3. -/
theorem reach_odd : ∀ N m : ℕ, m ≤ N → 1 ≤ m → m % 3 ≠ 0 →
    ∃ k : ℕ, collatz^[k] m % 2 = 1 ∧ collatz^[k] m % 3 ≠ 0 := by
  intro N
  induction N with
  | zero => intro m h1 h2; omega
  | succ N ih =>
    intro m hm h1 h3
    by_cases hp : m % 2 = 1
    · exact ⟨0, by simpa using hp, by simpa using h3⟩
    · obtain ⟨k, hk1, hk2⟩ := ih (m / 2) (by omega) (by omega) (by omega)
      refine ⟨k + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply]
        have : collatz m = m / 2 := by unfold collatz; rw [if_pos (by omega)]
        rw [this]; exact hk1
      · rw [Function.iterate_succ_apply]
        have : collatz m = m / 2 := by unfold collatz; rw [if_pos (by omega)]
        rw [this]; exact hk2

/-- Induction on the power of 2 not dividing y + 1. -/
theorem from_odd : ∀ e y : ℕ, y % 2 = 1 → y % 3 ≠ 0 → ¬ (2 ^ e ∣ y + 1) →
    ∃ k : ℕ, collatz^[k] y % 12 = 1 ∨ collatz^[k] y % 12 = 5 := by
  intro e
  induction e with
  | zero => intro y _ _ h; exact absurd (by simp) h
  | succ e ih =>
    intro y h2 h3 hd
    by_cases h4 : y % 4 = 1
    · exact ⟨0, by simp only [Function.iterate_zero, id_eq]; omega⟩
    · have hc1 : collatz y = 3 * y + 1 := by unfold collatz; rw [if_neg (by omega)]
      have hc2 : collatz (3 * y + 1) = (3 * y + 1) / 2 := by
        unfold collatz; rw [if_pos (by omega)]
      have hd' : ¬ (2 ^ e ∣ (3 * y + 1) / 2 + 1) := by
        intro hdvd
        apply hd
        have e1 : (3 * y + 1) / 2 + 1 = 3 * ((y + 1) / 2) := by omega
        rw [e1] at hdvd
        have hco : Nat.Coprime (2 ^ e) 3 := Nat.Coprime.pow_left e (by decide)
        have h5 : 2 ^ e ∣ (y + 1) / 2 := hco.dvd_of_dvd_mul_left hdvd
        have e2 : y + 1 = 2 * ((y + 1) / 2) := by omega
        rw [e2, pow_succ, mul_comm]
        exact Nat.mul_dvd_mul_left 2 h5
      obtain ⟨k, hk⟩ := ih ((3 * y + 1) / 2) (by omega) (by omega) hd'
      refine ⟨k + 2, ?_⟩
      rw [Function.iterate_add_apply]
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      rw [hc1, hc2]
      exact hk

/-- Every trajectory of a positive integer hits a number that is 1 or 5 mod 12. -/
theorem hits : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, collatz^[k] n % 12 = 1 ∨ collatz^[k] n % 12 = 5 := by
  intro n hn
  by_cases h3 : n % 3 = 0
  · -- first reach an odd x, possibly divisible by 3
    have step : ∀ N m : ℕ, m ≤ N → 1 ≤ m → ∃ k : ℕ, collatz^[k] m % 2 = 1 := by
      intro N
      induction N with
      | zero => intro m h1 h2; omega
      | succ N ih =>
        intro m hm h1
        by_cases hp : m % 2 = 1
        · exact ⟨0, by simpa using hp⟩
        · obtain ⟨k, hk1⟩ := ih (m / 2) (by omega) (by omega)
          refine ⟨k + 1, ?_⟩
          rw [Function.iterate_succ_apply]
          have : collatz m = m / 2 := by unfold collatz; rw [if_pos (by omega)]
          rw [this]; exact hk1
    obtain ⟨k1, hk1⟩ := step n n le_rfl hn
    set x := collatz^[k1] n with hx
    have hcx : collatz x = 3 * x + 1 := by unfold collatz; rw [if_neg (by omega)]
    obtain ⟨k2, hk2, hk2'⟩ := reach_odd (3 * x + 1) (3 * x + 1) le_rfl (by omega) (by omega)
    obtain ⟨k3, hk3⟩ := from_odd (collatz^[k2] (3 * x + 1) + 1) (collatz^[k2] (3 * x + 1)) hk2 hk2'
      (Nat.not_dvd_of_pos_of_lt (by omega) (Nat.lt_two_pow_self))
    refine ⟨k3 + (k2 + (1 + k1)), ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      ← hx, Function.iterate_one, hcx]
    exact hk3
  · obtain ⟨k2, hk2, hk2'⟩ := reach_odd n n le_rfl hn h3
    obtain ⟨k3, hk3⟩ := from_odd (collatz^[k2] n + 1) (collatz^[k2] n) hk2 hk2'
      (Nat.not_dvd_of_pos_of_lt (by omega) (Nat.lt_two_pow_self))
    refine ⟨k3 + k2, ?_⟩
    rw [Function.iterate_add_apply]
    exact hk3

end OMA.P_oeis_a087445

theorem OMA.solution : type_of% @OMA.S_oeis_a087445.main := by
  intro n hn
  obtain ⟨k, hk⟩ := OMA.P_oeis_a087445.hits n hn
  refine ⟨k, ?_⟩
  rcases hk with hk | hk
  · refine ⟨2 * (OMA.S_oeis_a087445.collatz^[k] n / 12) + 1, by omega, ?_⟩
    unfold OMA.S_oeis_a087445.a
    rw [if_pos (by omega)]
    omega
  · refine ⟨2 * (OMA.S_oeis_a087445.collatz^[k] n / 12) + 2, by omega, ?_⟩
    unfold OMA.S_oeis_a087445.a
    rw [if_neg (by omega)]
    omega
