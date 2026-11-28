import OMAStatements.S_oeis_a195549
import Mathlib

namespace OMA.S_oeis_a195549

lemma conv_eq (n : ℕ) : convergent n = (Nat.fib (n + 1), Nat.fib n) := by
  induction n with
  | zero => simp [convergent]
  | succ n ih =>
    simp only [convergent, ih]
    rw [Nat.fib_add_two (n := n)]
    simp [add_comm]

lemma fib_parity (k : ℕ) : Nat.fib k % 2 = if k % 3 = 0 then 0 else 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp
    · simp
    · have h1 := ih k (by omega)
      have h2 := ih (k + 1) (by omega)
      rw [Nat.fib_add_two]
      split_ifs at h1 h2 ⊢ <;> omega

lemma hyp_gen (u v : ℕ) (hcop : Nat.Coprime u v) (hle : v ≤ u) :
    hyp u v = (u ^ 2 + v ^ 2) / Nat.gcd 2 (u ^ 2 + v ^ 2) := by
  unfold hyp
  congr 1
  apply Nat.dvd_antisymm
  · -- g ∣ 2 and g ∣ u^2+v^2
    have h1 : Nat.gcd (Nat.gcd (2 * (u * v)) (u ^ 2 + v ^ 2)) (u ^ 2 - v ^ 2) ∣ u ^ 2 + v ^ 2 :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have h2 : Nat.gcd (Nat.gcd (2 * (u * v)) (u ^ 2 + v ^ 2)) (u ^ 2 - v ^ 2) ∣ u ^ 2 - v ^ 2 :=
      Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd (Nat.gcd (2 * (u * v)) (u ^ 2 + v ^ 2)) (u ^ 2 - v ^ 2) ∣ 2 * u ^ 2 := by
      have := Nat.dvd_add h1 h2
      have e : u ^ 2 + v ^ 2 + (u ^ 2 - v ^ 2) = 2 * u ^ 2 := by
        have : v ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hle 2
        omega
      rwa [e] at this
    have h4 : Nat.gcd (Nat.gcd (2 * (u * v)) (u ^ 2 + v ^ 2)) (u ^ 2 - v ^ 2) ∣ 2 * v ^ 2 := by
      have := Nat.dvd_sub h1 h2
      have e : u ^ 2 + v ^ 2 - (u ^ 2 - v ^ 2) = 2 * v ^ 2 := by
        have : v ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hle 2
        omega
      rwa [e] at this
    have hcop2 : Nat.Coprime (u ^ 2) (v ^ 2) := hcop.pow 2 2
    have h5 : Nat.gcd (Nat.gcd (2 * (u * v)) (u ^ 2 + v ^ 2)) (u ^ 2 - v ^ 2) ∣ 2 := by
      have := Nat.dvd_gcd h3 h4
      rwa [Nat.gcd_mul_left, hcop2, mul_one] at this
    exact Nat.dvd_gcd h5 h1
  · apply Nat.dvd_gcd
    · apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left _ _).trans (dvd_mul_right _ _)
      · exact Nat.gcd_dvd_right _ _
    · have hd : Nat.gcd 2 (u ^ 2 + v ^ 2) ∣ u ^ 2 + v ^ 2 := Nat.gcd_dvd_right _ _
      have hd2 : Nat.gcd 2 (u ^ 2 + v ^ 2) ∣ 2 := Nat.gcd_dvd_left _ _
      have hle2 : v ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hle 2
      have : u ^ 2 - v ^ 2 = (u ^ 2 + v ^ 2) - 2 * v ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub hd (hd2.trans (dvd_mul_right _ _))

lemma hyp_eq (n : ℕ) : hyp (Nat.fib (n + 1)) (Nat.fib n) =
    Nat.fib (2 * n + 1) / Nat.gcd 2 (Nat.fib (2 * n + 1)) := by
  have hsq : Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 = Nat.fib (2 * n + 1) := by
    rw [Nat.fib_two_mul_add_one]
  rw [hyp_gen _ _ (Nat.fib_coprime_fib_succ n).symm (Nat.fib_mono (by omega)), hsq]

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = Nat.fib (2 * n + 1) / Nat.gcd 2 (Nat.fib (2 * n + 1)) := by
  unfold a
  rw [if_neg (by omega), conv_eq]
  exact hyp_eq n

lemma a_val (n : ℕ) (hn : 1 ≤ n) :
    (n % 3 = 1 → a n * 2 = Nat.fib (2 * n + 1)) ∧ (n % 3 ≠ 1 → a n = Nat.fib (2 * n + 1)) := by
  rw [a_eq n hn]
  have hp := fib_parity (2 * n + 1)
  constructor
  · intro h
    have h0 : (2 * n + 1) % 3 = 0 := by omega
    rw [if_pos h0] at hp
    have : Nat.gcd 2 (Nat.fib (2 * n + 1)) = 2 := by
      apply Nat.gcd_eq_left; omega
    rw [this]; apply Nat.div_mul_cancel; omega
  · intro h
    have h0 : ¬ (2 * n + 1) % 3 = 0 := by omega
    rw [if_neg h0] at hp
    have : Nat.gcd 2 (Nat.fib (2 * n + 1)) = 1 := by
      rw [Nat.gcd_rec, hp]; rfl
    rw [this]; simp

lemma fib_id (m : ℕ) : Nat.fib (m + 12) + Nat.fib m = 18 * Nat.fib (m + 6) := by
  have e2 := Nat.fib_add_two (n := m)
  have e3 := Nat.fib_add_two (n := m + 1)
  have e4 := Nat.fib_add_two (n := m + 2)
  have e5 := Nat.fib_add_two (n := m + 3)
  have e6 := Nat.fib_add_two (n := m + 4)
  have e7 := Nat.fib_add_two (n := m + 5)
  have e8 := Nat.fib_add_two (n := m + 6)
  have e9 := Nat.fib_add_two (n := m + 7)
  have e10 := Nat.fib_add_two (n := m + 8)
  have e11 := Nat.fib_add_two (n := m + 9)
  have e12 := Nat.fib_add_two (n := m + 10)
  simp only [show m + 1 + 2 = m + 3 from rfl, show m + 2 + 2 = m + 4 from rfl,
    show m + 3 + 2 = m + 5 from rfl, show m + 4 + 2 = m + 6 from rfl, show m + 5 + 2 = m + 7 from rfl,
    show m + 6 + 2 = m + 8 from rfl, show m + 7 + 2 = m + 9 from rfl, show m + 8 + 2 = m + 10 from rfl,
    show m + 9 + 2 = m + 11 from rfl, show m + 10 + 2 = m + 12 from rfl,
    show m + 1 + 1 = m + 2 from rfl, show m + 2 + 1 = m + 3 from rfl, show m + 3 + 1 = m + 4 from rfl,
    show m + 4 + 1 = m + 5 from rfl, show m + 5 + 1 = m + 6 from rfl, show m + 6 + 1 = m + 7 from rfl,
    show m + 7 + 1 = m + 8 from rfl, show m + 8 + 1 = m + 9 from rfl, show m + 9 + 1 = m + 10 from rfl,
    show m + 10 + 1 = m + 11 from rfl] at *
  omega

lemma rec_ok : recurrence := by
  intro n hn
  have h1 := a_val n hn
  have h2 := a_val (n + 3) (by omega)
  have h3 := a_val (n + 6) (by omega)
  have fi := fib_id (2 * n + 1)
  have e1 : 2 * (n + 3) + 1 = 2 * n + 1 + 6 := by ring
  have e2 : 2 * (n + 6) + 1 = 2 * n + 1 + 12 := by ring
  rw [e1] at h2
  rw [e2] at h3
  by_cases h : n % 3 = 1
  · have := h1.1 h
    have := h2.1 (by omega)
    have := h3.1 (by omega)
    omega
  · have := h1.2 h
    have := h2.2 (by omega)
    have := h3.2 (by omega)
    omega

lemma a_small : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 13 ∧ a 4 = 17 ∧ a 5 = 89 ∧ a 6 = 233 := by
  refine ⟨by simp [a], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

open PowerSeries in
lemma gf_ok : generatingFunction := by
  unfold generatingFunction
  have h1 : ((1-3*X+X^2)*(1+3*X+8*X^2+3*X^3+X^4) : PowerSeries ℤ) = 1 - 18 * X^3 + X^6 := by ring
  rw [h1]
  have h2 : (1 - 18 * X^3 + X^6 : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ))
      = PowerSeries.mk (fun n => (a n : ℤ)) - PowerSeries.C (18:ℤ) * (X^3 * PowerSeries.mk (fun n => (a n : ℤ)))
        + X^6 * PowerSeries.mk (fun n => (a n : ℤ)) := by
    rw [map_ofNat PowerSeries.C 18]; ring
  have h3 : (X * (1+5*X+13*X^2-X^3-X^4-X^5) : PowerSeries ℤ)
      = X + PowerSeries.C (5:ℤ) * X^2 + PowerSeries.C (13:ℤ) * X^3 - X^4 - X^5 - X^6 := by
    rw [map_ofNat PowerSeries.C 5, map_ofNat PowerSeries.C 13]; ring
  rw [h2, h3]
  ext n
  have hr := rec_ok
  have hs := a_small
  simp only [map_add, map_sub, map_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := hs
  by_cases hn : n ≤ 6
  · interval_cases n <;> simp [s0, s1, s2, s3, s4, s5, s6]
  · have h := hr (n - 6) (by omega)
    rw [show n - 6 + 6 = n by omega, show n - 6 + 3 = n - 3 by omega] at h
    have h' : (a n : ℤ) + a (n - 6) = 18 * a (n - 3) := by exact_mod_cast h
    split_ifs <;> omega

lemma red_ok : reducedDenominator := by
  intro n hn
  have hF : 2 ≤ Nat.fib (2 * n + 1) := by
    have : Nat.fib 3 ≤ Nat.fib (2 * n + 1) := Nat.fib_mono (by omega)
    have h3 : Nat.fib 3 = 2 := by decide
    omega
  rw [a_eq n hn, Rat.den_mkRat]
  generalize Nat.fib (2 * n + 1) = F at hF ⊢
  have e : ((F : ℤ) - 2).natAbs = F - 2 := by omega
  rw [e, if_neg (by omega)]
  congr 1
  rw [Nat.gcd_comm 2 F]
  have : Nat.gcd (F - 2) F = Nat.gcd 2 F := by
    obtain ⟨k, rfl⟩ : ∃ k, F = k + 2 := ⟨F - 2, by omega⟩
    simp [Nat.gcd_comm]
  rw [Nat.gcd_comm F (F - 2), this, Nat.gcd_comm]

end OMA.S_oeis_a195549

theorem OMA.solution : type_of% @OMA.S_oeis_a195549.main := by
  exact ⟨OMA.S_oeis_a195549.rec_ok, OMA.S_oeis_a195549.gf_ok, OMA.S_oeis_a195549.red_ok⟩
