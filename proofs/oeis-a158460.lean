import OMAStatements.S_oeis_a158460
import Mathlib

-- Problem: A158460, k with prime(k-1) + 5 a square equal to prime(k+1) - 1.
-- Upstream: formal-conjectures statements/oeis-a158460.lean (declaration OMA.S_oeis_a158460.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: with q = prime(k-1), the hypotheses give prime(k+1) = q + 6 and q + 5 = s^2. Squares
-- modulo 10 force q to end in 1, 5 or 9; 5 and 9 are impossible (q = 5, or 5 | q + 6), so q ends
-- in 1 and the only candidate prime strictly between q and q + 6 is q + 2, which ends in 3.

namespace OMA.P_oeis_a158460

open OMA.S_oeis_a158460

theorem prime_mono {i j : ℕ} (h : i < j) : Nat.nth Nat.Prime i < Nat.nth Nat.Prime j :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime h

theorem eq_of_mod_eq_zero {p d : ℕ} (hp : p.Prime) (hd : 1 < d) (h : p % d = 0) : p = d := by
  rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h) with h1 | h1 <;> omega

theorem main' : ∀ k : ℕ, 2 ≤ k →
    (∃ s : ℕ, prime (k - 1) + 5 = s ^ 2) → prime (k - 1) + 5 = prime (k + 1) - 1 →
    prime k = prime (k - 1) + 2 ∧ prime (k - 1) % 10 = 1 ∧ prime k % 10 = 3 := by
  intro k hk ⟨s, hs⟩ ht
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have e1 : prime (j + 2 - 1) = Nat.nth Nat.Prime j := by
    unfold prime; rw [show j + 2 - 1 - 1 = j by omega]
  have e2 : prime (j + 2) = Nat.nth Nat.Prime (j + 1) := by
    unfold prime; rw [show j + 2 - 1 = j + 1 by omega]
  have e3 : prime (j + 2 + 1) = Nat.nth Nat.Prime (j + 2) := by
    unfold prime; rw [show j + 2 + 1 - 1 = j + 2 by omega]
  rw [e1, e3] at ht
  rw [e1] at hs
  rw [e1, e2]
  have pq : (Nat.nth Nat.Prime j).Prime := Nat.prime_nth_prime j
  have pr : (Nat.nth Nat.Prime (j + 1)).Prime := Nat.prime_nth_prime (j + 1)
  have pt : (Nat.nth Nat.Prime (j + 2)).Prime := Nat.prime_nth_prime (j + 2)
  have qr : Nat.nth Nat.Prime j < Nat.nth Nat.Prime (j + 1) := prime_mono (by omega)
  have rt : Nat.nth Nat.Prime (j + 1) < Nat.nth Nat.Prime (j + 2) := prime_mono (by omega)
  generalize Nat.nth Nat.Prime j = q at *
  generalize Nat.nth Nat.Prime (j + 1) = r at *
  generalize Nat.nth Nat.Prime (j + 2) = t at *
  have q2 := pq.two_le
  have ht6 : t = q + 6 := by omega
  have hq7 : q ≠ 2 := by
    rintro rfl
    have h7 : s ^ 2 = 7 := by omega
    have hs3 : s ≤ 2 := by nlinarith
    interval_cases s <;> omega
  have hqodd : q % 2 = 1 := by
    by_contra hc
    exact hq7 (eq_of_mod_eq_zero pq (by norm_num) (by omega))
  have hs10 : (q + 5) % 10 = (s % 10) ^ 2 % 10 := by rw [hs, Nat.pow_mod]
  have hq10 : q % 10 = 1 ∨ q % 10 = 5 ∨ q % 10 = 9 := by
    have hu : s % 10 < 10 := Nat.mod_lt _ (by norm_num)
    generalize s % 10 = u at hs10 hu
    interval_cases u <;> omega
  have hq1 : q % 10 = 1 := by
    rcases hq10 with h | h | h
    · exact h
    · have h5 : q = 5 := eq_of_mod_eq_zero pq (by norm_num) (by omega)
      subst h5
      have h10 : s ^ 2 = 10 := by omega
      have hs3 : s ≤ 3 := by nlinarith
      interval_cases s <;> omega
    · have h5 : t = 5 := eq_of_mod_eq_zero pt (by norm_num) (by omega)
      omega
  have hq11 : 11 ≤ q := by
    rcases (show q = 1 ∨ 11 ≤ q by omega) with h | h
    · omega
    · exact h
  have hr2 : r % 2 = 1 := by
    by_contra hc
    have := eq_of_mod_eq_zero pr (by norm_num) (show r % 2 = 0 by omega)
    omega
  have hr5 : r % 5 ≠ 0 := by
    intro hc
    have := eq_of_mod_eq_zero pr (by norm_num) hc
    omega
  have hr6 : r = q + 1 ∨ r = q + 2 ∨ r = q + 3 ∨ r = q + 4 ∨ r = q + 5 := by omega
  rcases hr6 with h | h | h | h | h <;> subst h <;> omega

end OMA.P_oeis_a158460

theorem OMA.solution : type_of% @OMA.S_oeis_a158460.main := OMA.P_oeis_a158460.main'
