import OMAStatements.S_oeis_a027171
import Mathlib

namespace OMA.S_oeis_a027171

lemma cb_succ (n : ℕ) : ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * (n : ℚ) + 1) * Nat.centralBinom n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have h' : (((n + 1) * Nat.centralBinom (n + 1) : ℕ) : ℚ) = ((2 * (2 * n + 1) * Nat.centralBinom n : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  exact h'

lemma ha (n : ℕ) : (a n : ℚ) * ((n : ℚ) + 1) = (Nat.centralBinom n : ℚ) * (9 * (n : ℚ) + 5) - 4 * ((n : ℚ) + 1) := by
  have h1 := cb_succ n
  have h2 := Nat.add_one_mul_choose_eq (2 * n) n
  have h3 : Nat.choose (2 * n + 1) n = Nat.choose (2 * n + 1) (n + 1) := by
    have := Nat.choose_symm_add (a := n) (b := n + 1)
    rw [show n + (n + 1) = 2 * n + 1 by ring] at this
    exact this
  have h2' : ((2 * (n : ℚ) + 1)) * (Nat.choose (2 * n) n : ℚ) = (Nat.choose (2 * n + 1) (n + 1) : ℚ) * ((n : ℚ) + 1) := by
    have : (((2 * n + 1) * Nat.choose (2 * n) n : ℕ) : ℚ) = ((Nat.choose (2 * n + 1) (n + 1) * (n + 1) : ℕ) : ℚ) := by rw [h2]
    push_cast at this
    exact this
  have h4 : Nat.choose (2 * n + 2) (n + 1) = Nat.centralBinom (n + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    ring_nf
  have h5 : Nat.choose (2 * n) n = Nat.centralBinom n := (Nat.centralBinom_eq_two_mul_choose n).symm
  have e : (a n : ℚ) = (Nat.choose (2 * n + 2) (n + 1) : ℚ) + (Nat.choose (2 * n + 1) n : ℚ) + (Nat.choose (2 * n + 1) (n + 1) : ℚ) + (Nat.choose (2 * n) n : ℚ) - 4 := by
    have h0 : a n = ((Nat.choose (2 * n + 2) (n + 1) : ℕ) : ℤ) + (Nat.choose (2 * n + 1) n : ℕ) + (Nat.choose (2 * n + 1) (n + 1) : ℕ) + (Nat.choose (2 * n) n : ℕ) - 4 := by
      simp [a, T, t]
      ring
    rw [h0]; push_cast; ring
  rw [e, h3, h4, h5]
  push_cast
  rw [h5] at h2'
  linear_combination h1 - 2 * h2'

theorem OMA.solution : type_of% @OMA.S_oeis_a027171.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e0 := ha m
  have e1 := ha (m + 1)
  have e2 := ha (m + 2)
  have c1 := cb_succ m
  have c2 := cb_succ (m + 1)
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  push_cast at e1 e2 c2
  have hm : (0:ℚ) < (m:ℚ) + 1 := by positivity
  have hm2 : (0:ℚ) < (m:ℚ) + 2 := by positivity
  have hm3 : (0:ℚ) < (m:ℚ) + 3 := by positivity
  have x1 : (Nat.centralBinom (m + 1) : ℚ) = 2 * (2 * (m:ℚ) + 1) * Nat.centralBinom m / ((m:ℚ) + 1) := by
    rw [eq_div_iff hm.ne']; linarith
  have x2 : (Nat.centralBinom (m + 2) : ℚ) = 2 * (2 * ((m:ℚ) + 1) + 1) * Nat.centralBinom (m + 1) / ((m:ℚ) + 1 + 1) := by
    rw [eq_div_iff (by positivity)]; linarith
  have y0 : (a m : ℚ) = ((Nat.centralBinom m : ℚ) * (9 * (m : ℚ) + 5) - 4 * ((m : ℚ) + 1)) / ((m:ℚ) + 1) := by
    rw [eq_div_iff hm.ne']; exact e0
  have y1 : (a (m + 1) : ℚ) = ((Nat.centralBinom (m + 1) : ℚ) * (9 * ((m : ℚ) + 1) + 5) - 4 * ((m : ℚ) + 1 + 1)) / ((m:ℚ) + 1 + 1) := by
    rw [eq_div_iff (by positivity)]; exact e1
  have y2 : (a (m + 2) : ℚ) = ((Nat.centralBinom (m + 2) : ℚ) * (9 * ((m : ℚ) + 2) + 5) - 4 * ((m : ℚ) + 2 + 1)) / ((m:ℚ) + 2 + 1) := by
    rw [eq_div_iff (by positivity)]; push_cast at e2; linarith
  have key : (2 * ((((m + 2 : ℕ)) : ℚ) + 1) * (a (m + 2) : ℚ) + (-7 * (((m + 2 : ℕ)) : ℚ) - 5) * (a (m + 1) : ℚ) + 2 * (-2 * (((m + 2 : ℕ)) : ℚ) + 3) * (a m : ℚ) + 12 * (-3 * (((m + 2 : ℕ)) : ℚ) + 1)) = 0 := by
    rw [y2, y1, y0, x2, x1]
    push_cast
    field_simp
    ring
  exact_mod_cast key
