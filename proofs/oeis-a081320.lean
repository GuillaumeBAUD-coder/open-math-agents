import OMAStatements.S_oeis_a081320
import Mathlib

open OMA.S_oeis_a081320

theorem P081320.veq (p B x y : ℕ) (hp : p.Prime) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ k ≤ B, p ^ k ∣ x ↔ p ^ k ∣ y) (hB : ¬ p ^ B ∣ y) :
    x.factorization p = y.factorization p := by
  have hyl : y.factorization p < B := by
    by_contra hc
    push_neg at hc
    exact hB ((Nat.pow_dvd_pow p hc).trans (Nat.ordProj_dvd y p))
  have h1 : p ^ y.factorization p ∣ x := (h _ hyl.le).2 (Nat.ordProj_dvd y p)
  have h2 : ¬ p ^ (y.factorization p + 1) ∣ x := fun hd =>
    Nat.pow_succ_factorization_not_dvd hy hp ((h _ hyl).1 hd)
  rw [hp.pow_dvd_iff_le_factorization hx] at h1 h2
  omega

theorem P081320.per (m : ℕ) : Nat.fib m % 144 = Nat.fib (m % 24) % 144 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 24 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have e := Nat.fib_add (m - 24) 23
      rw [show m - 24 + 23 + 1 = m by omega, show (23 : ℕ) + 1 = 24 by rfl] at e
      have f23 : Nat.fib 23 = 28657 := by decide
      have f24 : Nat.fib 24 = 46368 := by decide
      rw [f23, f24] at e
      have := ih (m - 24) (by omega)
      rw [show (m - 24) % 24 = m % 24 by omega] at this
      omega

theorem P081320.res : ∀ r < 24, r % 12 ≠ 0 → Nat.fib r % 16 ≠ 0 ∧ Nat.fib r % 9 ≠ 0 := by
  decide

theorem OMA.solution : type_of% @OMA.S_oeis_a081320.main := by
  intro n hn h12
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  rw [show m + 12 - 12 = m by omega]
  have e := Nat.fib_add m 11
  rw [show m + 11 + 1 = m + 12 by omega, show (11 : ℕ) + 1 = 12 by rfl] at e
  have f11 : Nat.fib 11 = 89 := by decide
  have f12 : Nat.fib 12 = 144 := by decide
  rw [f11, f12] at e
  have hm : m % 12 ≠ 0 := by omega
  have hr := P081320.res (m % 24) (Nat.mod_lt _ (by norm_num)) (by omega)
  have hp := P081320.per m
  have hy16 : Nat.fib m % 16 ≠ 0 := by omega
  have hy9 : Nat.fib m % 9 ≠ 0 := by omega
  have hy : Nat.fib m ≠ 0 := by intro h0; rw [h0] at hy16; simp at hy16
  have hx : Nat.fib (m + 12) ≠ 0 := by omega
  have e2 : (Nat.fib (m + 12)).factorization 2 = (Nat.fib m).factorization 2 := by
    apply P081320.veq 2 4 _ _ Nat.prime_two hx hy
    · intro k hk
      interval_cases k <;> norm_num <;> omega
    · norm_num; omega
  have e3 : (Nat.fib (m + 12)).factorization 3 = (Nat.fib m).factorization 3 := by
    apply P081320.veq 3 2 _ _ Nat.prime_three hx hy
    · intro k hk
      interval_cases k <;> norm_num <;> omega
    · norm_num; omega
  simp only [a, smooth3Part, e2, e3]
