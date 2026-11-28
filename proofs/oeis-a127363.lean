import OMAStatements.S_oeis_a127363
import Mathlib

namespace OMA.S_oeis_a127363

noncomputable def R (n m : ℕ) : ℚ := ∑ i ∈ Finset.range m, (Nat.choose n i : ℚ) * (1 / 16 : ℚ) ^ i

lemma R_succ (n m : ℕ) : R n (m + 1) = R n m + (Nat.choose n m : ℚ) * (1 / 16 : ℚ) ^ m := by
  unfold R; rw [Finset.sum_range_succ]

lemma R_pas (n m : ℕ) : R (n + 1) (m + 1) = (17 / 16 : ℚ) * R n m + (Nat.choose n m : ℚ) * (1 / 16 : ℚ) ^ m := by
  induction m with
  | zero => simp [R]
  | succ m ih =>
    rw [R_succ (n + 1) (m + 1), ih, R_succ n m, Nat.choose_succ_succ' n m]
    push_cast
    ring

lemma ch_up_aux (N k : ℕ) :
    ((Nat.choose (N + 1) (k + 1) : ℚ)) * ((k : ℚ) + 1) = ((N : ℚ) + 1) * Nat.choose N k := by
  have h := Nat.add_one_mul_choose_eq N k
  have h' : (((N + 1) * Nat.choose N k : ℕ) : ℚ) = ((Nat.choose (N + 1) (k + 1) * (k + 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linarith

noncomputable def ρ (m : ℕ) : ℚ := 16 ^ m * R (2 * m) m
noncomputable def τ (m : ℕ) : ℚ := (Nat.choose (2 * m) m : ℚ)

lemma uw (m : ℕ) : (16 : ℚ) ^ m * (1 / 16 : ℚ) ^ m = 1 := by
  rw [← mul_pow]; norm_num

lemma rho_succ (m : ℕ) : ((m : ℚ) + 1) * ρ (m + 1) = ((m : ℚ) + 1) * (289 / 16) * ρ m + (15 * (m : ℚ) + 16) * τ m := by
  have hX := R_pas (2 * m) m
  have hY := R_pas (2 * m + 1) m
  have hS := R_succ (2 * m + 1) m
  have hc : (Nat.choose (2 * m + 1) m : ℚ) * ((m : ℚ) + 1) = (2 * (m : ℚ) + 1) * τ m := by
    have h1 := Nat.choose_symm_half m
    have h2 := ch_up_aux (2 * m) m
    unfold τ
    rw [← h1]; push_cast at h2; linarith
  have h2m : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  unfold ρ
  rw [h2m, hY]
  have hu := uw m
  unfold τ at *
  rw [pow_succ]
  have hY2 : R (2 * m + 1) m = R (2 * m + 1) (m + 1) - (Nat.choose (2 * m + 1) m : ℚ) * (1 / 16 : ℚ) ^ m := by linarith
  rw [hY2, hX]
  linear_combination (((m : ℚ) + 1) * (17 * (Nat.choose (2 * m) m : ℚ) - (Nat.choose (2 * m + 1) m : ℚ))) * hu - hc

lemma tau_succ (m : ℕ) : ((m : ℚ) + 1) * τ (m + 1) = 2 * (2 * (m : ℚ) + 1) * τ m := by
  have := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at this
  have h' : (((m + 1) * Nat.choose (2 * (m + 1)) (m + 1) : ℕ) : ℚ) = ((2 * (2 * m + 1) * Nat.choose (2 * m) m : ℕ) : ℚ) := by
    rw [this]
  push_cast at h'
  unfold τ; linarith

lemma sum_even_odd (f : ℕ → ℚ) (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M), f k = ∑ i ∈ Finset.range M, (f (2 * i) + f (2 * i + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

lemma pw_even (j : ℕ) : ((-4 : ℚ)) ^ (2 * j) = 16 ^ j := by
  rw [pow_mul]; norm_num

lemma pw_odd (j : ℕ) : ((-4 : ℚ)) ^ (2 * j + 1) = -4 * 16 ^ j := by
  rw [pow_succ, pow_mul]; norm_num; ring

lemma pw16 (m i : ℕ) (h : i ≤ m) : (16 : ℚ) ^ (m - i) = 16 ^ m * (1 / 16 : ℚ) ^ i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, one_div, inv_pow]
  field_simp

lemma aq (n : ℕ) : (a n : ℚ) = ∑ k ∈ Finset.range (n + 1), (Nat.choose n (k / 2) : ℚ) * (-4 : ℚ) ^ (n - k) := by
  unfold a; push_cast; rfl

lemma aO (m : ℕ) : (a (2 * m + 1) : ℚ) = -3 * (17 / 16 * ρ m + τ m) := by
  rw [aq, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, sum_even_odd]
  have hX := R_pas (2 * m) m
  have : ∀ i ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m + 1) (2 * i / 2) : ℚ) * (-4 : ℚ) ^ (2 * m + 1 - 2 * i)
        + (Nat.choose (2 * m + 1) ((2 * i + 1) / 2) : ℚ) * (-4 : ℚ) ^ (2 * m + 1 - (2 * i + 1)))
      = -3 * 16 ^ m * ((Nat.choose (2 * m + 1) i : ℚ) * (1 / 16 : ℚ) ^ i) := by
    intro i hi
    have hi := Finset.mem_range.mp hi
    rw [show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega,
      show 2 * m + 1 - 2 * i = 2 * (m - i) + 1 by omega, show 2 * m + 1 - (2 * i + 1) = 2 * (m - i) by omega,
      pw_odd, pw_even, pw16 m i (by omega)]
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  have h1 : R (2 * m + 1) (m + 1) = ∑ i ∈ Finset.range (m + 1), (Nat.choose (2 * m + 1) i : ℚ) * (1 / 16 : ℚ) ^ i := rfl
  rw [← h1, show R (2 * m + 1) (m + 1) = _ from hX]
  unfold ρ τ
  have hu := uw m
  linear_combination (-3 * (Nat.choose (2 * m) m : ℚ)) * hu

lemma aE (m : ℕ) : (a (2 * m) : ℚ) = 3 / 4 * ρ m + τ m := by
  rw [aq, Finset.sum_range_succ, show 2 * m = 2 * m by rfl]
  have e1 : ∑ k ∈ Finset.range (2 * m), (Nat.choose (2 * m) (k / 2) : ℚ) * (-4 : ℚ) ^ (2 * m - k)
      = ∑ i ∈ Finset.range m, ((Nat.choose (2 * m) (2 * i / 2) : ℚ) * (-4 : ℚ) ^ (2 * m - 2 * i)
        + (Nat.choose (2 * m) ((2 * i + 1) / 2) : ℚ) * (-4 : ℚ) ^ (2 * m - (2 * i + 1))) :=
    sum_even_odd (fun k => (Nat.choose (2 * m) (k / 2) : ℚ) * (-4 : ℚ) ^ (2 * m - k)) m
  rw [e1]
  have : ∀ i ∈ Finset.range m,
      ((Nat.choose (2 * m) (2 * i / 2) : ℚ) * (-4 : ℚ) ^ (2 * m - 2 * i)
        + (Nat.choose (2 * m) ((2 * i + 1) / 2) : ℚ) * (-4 : ℚ) ^ (2 * m - (2 * i + 1)))
      = 3 / 4 * 16 ^ m * ((Nat.choose (2 * m) i : ℚ) * (1 / 16 : ℚ) ^ i) := by
    intro i hi
    have hi := Finset.mem_range.mp hi
    obtain ⟨e, he⟩ : ∃ e, m - i = e + 1 := ⟨m - i - 1, by omega⟩
    rw [show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega,
      show 2 * m - 2 * i = 2 * (e + 1) by omega, show 2 * m - (2 * i + 1) = 2 * e + 1 by omega,
      pw_odd, pw_even]
    have := pw16 m i (by omega)
    rw [he] at this
    linear_combination (3 / 4 * (Nat.choose (2 * m) i : ℚ)) * this
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  have h1 : R (2 * m) m = ∑ i ∈ Finset.range m, (Nat.choose (2 * m) i : ℚ) * (1 / 16 : ℚ) ^ i := rfl
  rw [← h1]
  unfold ρ τ
  simp
  ring

lemma rho_eq (m : ℕ) : ρ (m + 1) = (((m : ℚ) + 1) * (289 / 16) * ρ m + (15 * (m : ℚ) + 16) * τ m) / ((m : ℚ) + 1) := by
  have hp : (m : ℚ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff hp]; linear_combination rho_succ m

lemma tau_eq (m : ℕ) : τ (m + 1) = 2 * (2 * (m : ℚ) + 1) * τ m / ((m : ℚ) + 1) := by
  have hp : (m : ℚ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff hp]; linear_combination tau_succ m

end OMA.S_oeis_a127363

theorem OMA.solution : type_of% @OMA.S_oeis_a127363.main := by
  intro n hn
  open OMA.S_oeis_a127363 in
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
    have r0 := aE (p + 2)
    have r1 : (a (2 * (p + 2) - 1) : ℚ) = -3 * (17 / 16 * ρ (p + 1) + τ (p + 1)) := by
      rw [show 2 * (p + 2) - 1 = 2 * (p + 1) + 1 by omega]; exact aO (p + 1)
    have r2 : (a (2 * (p + 2) - 2) : ℚ) = 3 / 4 * ρ (p + 1) + τ (p + 1) := by
      rw [show 2 * (p + 2) - 2 = 2 * (p + 1) by omega]; exact aE (p + 1)
    have r3 : (a (2 * (p + 2) - 3) : ℚ) = -3 * (17 / 16 * ρ p + τ p) := by
      rw [show 2 * (p + 2) - 3 = 2 * p + 1 by omega]; exact aO p
    have k2 : ρ (p + 2) = ((((p + 1 : ℕ) : ℚ) + 1) * (289 / 16) * ρ (p + 1) + (15 * ((p + 1 : ℕ) : ℚ) + 16) * τ (p + 1)) / (((p + 1 : ℕ) : ℚ) + 1) := rho_eq (p + 1)
    have t2 : τ (p + 2) = 2 * (2 * ((p + 1 : ℕ) : ℚ) + 1) * τ (p + 1) / (((p + 1 : ℕ) : ℚ) + 1) := tau_eq (p + 1)
    have k1 := rho_eq p
    have t1 := tau_eq p
    have hq : (((4 * ((2 * (p + 2) : ℕ) : ℤ) * a (2 * (p + 2)) + (17 * ((2 * (p + 2) : ℕ) : ℤ) - 8) * a (2 * (p + 2) - 1)
        + 2 * (-8 * ((2 * (p + 2) : ℕ) : ℤ) - 1) * a (2 * (p + 2) - 2) + 68 * (-((2 * (p + 2) : ℕ) : ℤ) + 2) * a (2 * (p + 2) - 3) : ℤ)) : ℚ) = 0 := by
      push_cast
      rw [r0, r1, r2, r3, k2, t2, k1, t1]
      push_cast
      have hp : (p : ℚ) + 1 ≠ 0 := by positivity
      have hp2 : (p : ℚ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring
    exact_mod_cast hq
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have r0 := aO (p + 1)
    have r1 : (a (2 * (p + 1)) : ℚ) = 3 / 4 * ρ (p + 1) + τ (p + 1) := aE (p + 1)
    have r2 : (a (2 * (p + 1) - 1) : ℚ) = -3 * (17 / 16 * ρ p + τ p) := by
      rw [show 2 * (p + 1) - 1 = 2 * p + 1 by omega]; exact aO p
    have r3 : (a (2 * (p + 1) - 2) : ℚ) = 3 / 4 * ρ p + τ p := by
      rw [show 2 * (p + 1) - 2 = 2 * p by omega]; exact aE p
    have k1 := rho_eq p
    have t1 := tau_eq p
    have hq : (((4 * ((2 * (p + 1) + 1 : ℕ) : ℤ) * a (2 * (p + 1) + 1) + (17 * ((2 * (p + 1) + 1 : ℕ) : ℤ) - 8) * a (2 * (p + 1) + 1 - 1)
        + 2 * (-8 * ((2 * (p + 1) + 1 : ℕ) : ℤ) - 1) * a (2 * (p + 1) + 1 - 2) + 68 * (-((2 * (p + 1) + 1 : ℕ) : ℤ) + 2) * a (2 * (p + 1) + 1 - 3) : ℤ)) : ℚ) = 0 := by
      push_cast
      rw [r0, r1, r2, r3, k1, t1]
      have hp : (p : ℚ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    exact_mod_cast hq
