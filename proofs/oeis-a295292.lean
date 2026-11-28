import OMAStatements.S_oeis_a295292

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: with B(n) = sum of i over 1 ≤ i ≤ n/2 with n - i odd, for n ≥ 1
-- a(n+4) = a(n) + 4 B(n) + T(n), where T(n) collects the two new top summands.
-- B(n+4) - B(n) = 2(n/4) + (1, 2, 3, 2 for n mod 4 = 0, 1, 2, 3), so B has constant second difference 2 (step 4), and
-- T(4q+r) is an explicit quadratic in q, with constant second difference 8. Hence
-- a(n) - 3a(n-4) + 3a(n-8) - a(n-12) = 16 for n ≥ 13, which gives the recurrence.

namespace OMA.Sol_oeis_a295292
open OMA.S_oeis_a295292

def B (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 (n / 2), i * ((n - i) % 2)

def T (n : ℕ) : ℕ :=
  (n / 2 + 1) * (n + 4 - (n / 2 + 1)) * ((n + 4 - (n / 2 + 1)) % 2)
    + (n / 2 + 2) * (n + 4 - (n / 2 + 2)) * ((n + 4 - (n / 2 + 2)) % 2)

lemma stepA (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = a n + 4 * B n + T n := by
  unfold a B T
  have hk : (n + 4) / 2 = n / 2 + 2 := by omega
  rw [hk, show n / 2 + 2 = (n / 2 + 1) + 1 by ring,
    Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  have hc : ∑ i ∈ Finset.Icc 1 (n / 2), i * (n + 4 - i) * ((n + 4 - i) % 2)
      = ∑ i ∈ Finset.Icc 1 (n / 2), (i * (n - i) * ((n - i) % 2) + 4 * (i * ((n - i) % 2))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    have e1 : n + 4 - i = (n - i) + 4 := by omega
    have e2 : (n - i + 4) % 2 = (n - i) % 2 := by omega
    rw [e1, e2]; ring
  rw [hc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

lemma stepB (n : ℕ) (hn : 1 ≤ n) : B (n + 4) = B n + (2 * (n / 4) + 1 + n % 4 - 2 * (n % 4 / 3)) := by
  have h : B (n + 4) = B n + (n / 2 + 1) * ((n + 4 - (n / 2 + 1)) % 2)
      + (n / 2 + 2) * ((n + 4 - (n / 2 + 2)) % 2) := by
    unfold B
    have hk : (n + 4) / 2 = n / 2 + 2 := by omega
    rw [hk, show n / 2 + 2 = (n / 2 + 1) + 1 by ring,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have hc : ∑ i ∈ Finset.Icc 1 (n / 2), i * ((n + 4 - i) % 2)
        = ∑ i ∈ Finset.Icc 1 (n / 2), i * ((n - i) % 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      congr 1
      omega
    rw [hc]
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one (n + 4 - (n / 2 + 1)) with e1 | e1 <;>
  rcases Nat.mod_two_eq_zero_or_one (n + 4 - (n / 2 + 2)) with e2 | e2 <;>
  · rw [e1, e2]; omega

lemma T0 (q : ℕ) : T (4 * q) = (2 * q + 1) * (2 * q + 3) := by
  unfold T
  rw [show 4 * q / 2 = 2 * q by omega, show 4 * q + 4 - (2 * q + 1) = 2 * q + 3 by omega,
    show 4 * q + 4 - (2 * q + 2) = 2 * q + 2 by omega, show (2 * q + 3) % 2 = 1 by omega,
    show (2 * q + 2) % 2 = 0 by omega]
  ring

lemma T1 (q : ℕ) : T (4 * q + 1) = (2 * q + 2) * (2 * q + 3) := by
  unfold T
  rw [show (4 * q + 1) / 2 = 2 * q by omega, show 4 * q + 1 + 4 - (2 * q + 1) = 2 * q + 4 by omega,
    show 4 * q + 1 + 4 - (2 * q + 2) = 2 * q + 3 by omega, show (2 * q + 4) % 2 = 0 by omega,
    show (2 * q + 3) % 2 = 1 by omega]
  ring

lemma T2 (q : ℕ) : T (4 * q + 2) = (2 * q + 3) * (2 * q + 3) := by
  unfold T
  rw [show (4 * q + 2) / 2 = 2 * q + 1 by omega,
    show 4 * q + 2 + 4 - (2 * q + 1 + 1) = 2 * q + 4 by omega,
    show 4 * q + 2 + 4 - (2 * q + 1 + 2) = 2 * q + 3 by omega, show (2 * q + 4) % 2 = 0 by omega,
    show (2 * q + 3) % 2 = 1 by omega]
  ring

lemma T3 (q : ℕ) : T (4 * q + 3) = (2 * q + 2) * (2 * q + 5) := by
  unfold T
  rw [show (4 * q + 3) / 2 = 2 * q + 1 by omega,
    show 4 * q + 3 + 4 - (2 * q + 1 + 1) = 2 * q + 5 by omega,
    show 4 * q + 3 + 4 - (2 * q + 1 + 2) = 2 * q + 4 by omega, show (2 * q + 4) % 2 = 0 by omega,
    show (2 * q + 5) % 2 = 1 by omega]
  ring

lemma Tdiff (n : ℕ) (hn : 1 ≤ n) : T (n + 8) + T n = 2 * T (n + 4) + 8 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r := ⟨n / 4, n % 4, by omega, by omega⟩
  interval_cases r
  · rw [show 4 * q + 0 + 8 = 4 * (q + 2) by ring, show 4 * q + 0 + 4 = 4 * (q + 1) by ring,
      show 4 * q + 0 = 4 * q by ring, T0, T0, T0]
    ring
  · rw [show 4 * q + 1 + 8 = 4 * (q + 2) + 1 by ring, show 4 * q + 1 + 4 = 4 * (q + 1) + 1 by ring,
      T1, T1, T1]
    ring
  · rw [show 4 * q + 2 + 8 = 4 * (q + 2) + 2 by ring, show 4 * q + 2 + 4 = 4 * (q + 1) + 2 by ring,
      T2, T2, T2]
    ring
  · rw [show 4 * q + 3 + 8 = 4 * (q + 2) + 3 by ring, show 4 * q + 3 + 4 = 4 * (q + 1) + 3 by ring,
      T3, T3, T3]
    ring

lemma third (x : ℕ) (hx : 1 ≤ x) :
    a (x + 12) + 3 * a (x + 4) = 3 * a (x + 8) + a x + 16 := by
  have a1 := stepA (x + 8) (by omega)
  have a2 := stepA (x + 4) (by omega)
  have a3 := stepA x hx
  have b1 := stepB (x + 4) (by omega)
  have b2 := stepB x hx
  have t1 := Tdiff x hx
  rw [show x + 8 + 4 = x + 12 by ring] at a1
  rw [show x + 4 + 4 = x + 8 by ring] at a2 b1
  have hb : B (x + 8) + B x = 2 * B (x + 4) + 2 := by omega
  omega

end OMA.Sol_oeis_a295292

theorem OMA.solution : type_of% @OMA.S_oeis_a295292.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
  have h1 := OMA.Sol_oeis_a295292.third (m + 2) (by omega)
  have h2 := OMA.Sol_oeis_a295292.third (m + 1) (by omega)
  simp only [show m + 14 - 1 = m + 1 + 12 by omega, show m + 14 - 4 = m + 2 + 8 by omega,
    show m + 14 - 5 = m + 1 + 8 by omega, show m + 14 - 8 = m + 2 + 4 by omega,
    show m + 14 - 9 = m + 1 + 4 by omega, show m + 14 - 12 = m + 2 by omega,
    show m + 14 - 13 = m + 1 by omega, show m + 14 = m + 2 + 12 by omega]
  omega
