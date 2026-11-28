import OMAStatements.S_oeis_a111093
import Mathlib

namespace OMA.S_oeis_a111093

def D (n : ℕ) : ℤ := ((position n % 10 : ℕ) : ℤ)

lemma pos_shift (n : ℕ) : position (n + 20) = position n + (20 * n ^ 2 + 420 * n + 2870) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : position (n + 1 + 20) = position (n + 20) + (n + 21) ^ 2 := by
      show position (n + 20 + 1) = _
      rfl
    have h2 : position (n + 1) = position n + (n + 1) ^ 2 := rfl
    rw [h1, h2, ih]; ring

lemma D_per (n : ℕ) : D (n + 20) = D n := by
  unfold D
  rw [pos_shift]
  congr 1
  omega

lemma D_per' (n : ℕ) : ∀ q, D (n + 20 * q) = D n := by
  intro q
  induction q with
  | zero => rfl
  | succ q ih => rw [show n + 20 * (q + 1) = (n + 20 * q) + 20 by ring, D_per, ih]

lemma H_id (n : ℕ) (hn : 15 ≤ n) : D n - D (n - 5) + D (n - 10) - D (n - 15) = 0 := by
  have key : ∀ m < 20, D (m + 15) - D (m + 10) + D (m + 5) - D m = 0 := by decide
  obtain ⟨m, hm⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
  subst hm
  have e1 : m + 15 - 5 = m + 10 := by omega
  have e2 : m + 15 - 10 = m + 5 := by omega
  have e3 : m + 15 - 15 = m := by omega
  rw [e1, e2, e3]
  have hm20 : m = m % 20 + 20 * (m / 20) := by omega
  have := key (m % 20) (Nat.mod_lt _ (by norm_num))
  have a1 := D_per' (m % 20 + 15) (m / 20)
  have a2 := D_per' (m % 20 + 10) (m / 20)
  have a3 := D_per' (m % 20 + 5) (m / 20)
  have a4 := D_per' (m % 20) (m / 20)
  have b1 : m % 20 + 15 + 20 * (m / 20) = m + 15 := by omega
  have b2 : m % 20 + 10 + 20 * (m / 20) = m + 10 := by omega
  have b3 : m % 20 + 5 + 20 * (m / 20) = m + 5 := by omega
  have b4 : m % 20 + 20 * (m / 20) = m := by omega
  rw [b1] at a1; rw [b2] at a2; rw [b3] at a3; rw [b4] at a4
  rw [a1, a2, a3, a4]; exact this

lemma a_step (n : ℕ) (hn : 1 ≤ n) : a n - a (n - 1) = D n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  show a m + _ - a m = _
  unfold D; ring

lemma rec_ok (n : ℕ) (hn : 15 < n) :
    a n = a (n-1)+a (n-5)-a (n-6)-a (n-10)+a (n-11)+a (n-15)-a (n-16) := by
  have h0 := a_step n (by omega)
  have h1 := a_step (n - 5) (by omega)
  have h2 := a_step (n - 10) (by omega)
  have h3 := a_step (n - 15) (by omega)
  have h := H_id n (by omega)
  have e1 : n - 5 - 1 = n - 6 := by omega
  have e2 : n - 10 - 1 = n - 11 := by omega
  have e3 : n - 15 - 1 = n - 16 := by omega
  have e4 : n - 5 - 5 = n - 10 := by omega
  have e5 : n - 5 - 10 = n - 15 := by omega
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  rw [e4] at *; rw [e5] at *
  omega

end OMA.S_oeis_a111093

theorem OMA.solution : type_of% @OMA.S_oeis_a111093.main := by
  refine ⟨fun n hn => OMA.S_oeis_a111093.rec_ok n hn, ?_⟩
  intro X
  ext n
  have hc : ∀ k : ℕ, PowerSeries.coeff n (X ^ k * PowerSeries.mk OMA.S_oeis_a111093.a) =
      if k ≤ n then OMA.S_oeis_a111093.a (n - k) else 0 := by
    intro k
    rw [PowerSeries.coeff_X_pow_mul']
    simp
  have hL : PowerSeries.coeff n ((X^16 - X^15 - X^11 + X^10 + X^6 - X^5 - X + 1) *
      PowerSeries.mk OMA.S_oeis_a111093.a) =
      (if 16 ≤ n then OMA.S_oeis_a111093.a (n - 16) else 0) - (if 15 ≤ n then OMA.S_oeis_a111093.a (n - 15) else 0)
      - (if 11 ≤ n then OMA.S_oeis_a111093.a (n - 11) else 0) + (if 10 ≤ n then OMA.S_oeis_a111093.a (n - 10) else 0)
      + (if 6 ≤ n then OMA.S_oeis_a111093.a (n - 6) else 0) - (if 5 ≤ n then OMA.S_oeis_a111093.a (n - 5) else 0)
      - (if 1 ≤ n then OMA.S_oeis_a111093.a (n - 1) else 0) + OMA.S_oeis_a111093.a n := by
    have e : (X^16 - X^15 - X^11 + X^10 + X^6 - X^5 - X + 1) * PowerSeries.mk OMA.S_oeis_a111093.a =
        X^16 * PowerSeries.mk OMA.S_oeis_a111093.a - X^15 * PowerSeries.mk OMA.S_oeis_a111093.a
        - X^11 * PowerSeries.mk OMA.S_oeis_a111093.a + X^10 * PowerSeries.mk OMA.S_oeis_a111093.a
        + X^6 * PowerSeries.mk OMA.S_oeis_a111093.a - X^5 * PowerSeries.mk OMA.S_oeis_a111093.a
        - X^1 * PowerSeries.mk OMA.S_oeis_a111093.a + X^0 * PowerSeries.mk OMA.S_oeis_a111093.a := by
      simp only [pow_one, pow_zero, one_mul]; ring
    rw [e]
    simp only [map_sub, map_add, hc]
    simp
  have hR : PowerSeries.coeff n (X * (9*X^12+5*X^11+6*X^10+5*X^8-5*X^6+5*X^4+4*X^2+5*X+1)) =
      (if n = 13 then 9 else 0) + (if n = 12 then 5 else 0) + (if n = 11 then 6 else 0)
      + (if n = 9 then 5 else 0) - (if n = 7 then 5 else 0) + (if n = 5 then 5 else 0)
      + (if n = 3 then 4 else 0) + (if n = 2 then 5 else 0) + (if n = 1 then 1 else 0) := by
    have e : X * (9*X^12+5*X^11+6*X^10+5*X^8-5*X^6+5*X^4+4*X^2+5*X+1) =
        9*X^13+5*X^12+6*X^11+5*X^9-5*X^7+5*X^5+4*X^3+5*X^2+X^1 := by ring
    rw [e]
    have hn : ∀ (c : ℕ) (k : ℕ), PowerSeries.coeff n ((c : PowerSeries ℤ) * X ^ k) =
        if n = k then (c : ℤ) else 0 := by
      intro c k
      rw [← map_natCast (PowerSeries.C) c, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      split_ifs <;> simp
    have h1 := hn 9 13
    have h2 := hn 5 12
    have h3 := hn 6 11
    have h4 := hn 5 9
    have h5 := hn 5 7
    have h6 := hn 5 5
    have h7 := hn 4 3
    have h8 := hn 5 2
    simp only [Nat.cast_ofNat] at h1 h2 h3 h4 h5 h6 h7 h8
    simp only [map_add, map_sub, h1, h2, h3, h4, h5, h6, h7, h8, PowerSeries.coeff_X_pow]
    simp
    exact PowerSeries.coeff_X n
  rw [hL, hR]
  by_cases h : 15 < n
  · have := OMA.S_oeis_a111093.rec_ok n h
    have c1 : ¬ n = 13 := by omega
    have c2 : ¬ n = 12 := by omega
    have c3 : ¬ n = 11 := by omega
    have c4 : ¬ n = 9 := by omega
    have c5 : ¬ n = 7 := by omega
    have c6 : ¬ n = 5 := by omega
    have c7 : ¬ n = 3 := by omega
    have c8 : ¬ n = 2 := by omega
    have c9 : ¬ n = 1 := by omega
    simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, if_false, if_true, show 16 ≤ n by omega,
      show 15 ≤ n by omega, show 11 ≤ n by omega, show 10 ≤ n by omega, show 6 ≤ n by omega,
      show 5 ≤ n by omega, show 1 ≤ n by omega]
    omega
  · have : n ≤ 15 := by omega
    interval_cases n <;> simp [OMA.S_oeis_a111093.a, OMA.S_oeis_a111093.position, PowerSeries.coeff_mk]