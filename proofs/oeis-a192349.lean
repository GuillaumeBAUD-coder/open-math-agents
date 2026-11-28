import OMAStatements.S_oeis_a192349
import Mathlib

namespace A192349
open Polynomial

/-- Reductions of P_n and Q_n modulo X^2 - X - 1: P_n = u + v X, Q_n = s + t X. -/
def st : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 =>
    ((st n).2.1 + (st n).2.2.2 + 3 * (st n).2.2.1,
     (st n).1 + (st n).2.1 + (st n).2.2.1 + 4 * (st n).2.2.2,
     (st n).1 + (st n).2.2.2,
     (st n).2.1 + (st n).2.2.1 + (st n).2.2.2)

lemma pq_eq (n : ℕ) : ∃ q1 q2 : ℤ[X],
    (OMA.S_oeis_a192349.pq n).1 = (X ^ 2 - X - 1) * q1 + (C (st n).1 + C (st n).2.1 * X) ∧
    (OMA.S_oeis_a192349.pq n).2 = (X ^ 2 - X - 1) * q2 + (C (st n).2.2.1 + C (st n).2.2.2 * X) := by
  induction n with
  | zero => exact ⟨0, 0, by simp [OMA.S_oeis_a192349.pq, st], by simp [OMA.S_oeis_a192349.pq, st]⟩
  | succ n ih =>
    obtain ⟨q1, q2, h1, h2⟩ := ih
    refine ⟨X * q1 + (X + 3) * q2 + C (st n).2.1 + C (st n).2.2.2, q1 + X * q2 + C (st n).2.2.2,
      ?_, ?_⟩
    · rw [OMA.S_oeis_a192349.pq, st]
      simp only [h1, h2, map_add, map_mul, map_ofNat]
      ring
    · rw [OMA.S_oeis_a192349.pq, st]
      simp only [h1, h2, map_add]
      ring

lemma monicQ : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have h : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp only [map_one]; ring
  rw [h]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  decide

lemma mod_coeff (f q : ℤ[X]) (u v : ℤ) (h : f = (X ^ 2 - X - 1) * q + (C u + C v * X)) :
    (f %ₘ (X ^ 2 - X - 1)).coeff 1 = v := by
  have hdeg : (C u + C v * X : ℤ[X]).degree < (X ^ 2 - X - 1 : ℤ[X]).degree := by
    have h1 : (C u + C v * X : ℤ[X]).degree ≤ 1 := by compute_degree
    have h2 : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
    rw [h2]
    exact lt_of_le_of_lt h1 (by decide)
  have := (div_modByMonic_unique (f := f) q (C u + C v * X) monicQ ⟨by rw [h]; ring, hdeg⟩).2
  rw [this, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  simp

lemma a_eq (n : ℕ) : OMA.S_oeis_a192349.a (n + 1) = (st n).2.1 := by
  obtain ⟨q1, q2, h1, h2⟩ := pq_eq n
  unfold OMA.S_oeis_a192349.a OMA.S_oeis_a192349.p
  rw [Nat.add_sub_cancel]
  exact mod_coeff _ q1 _ _ h1

end A192349

theorem OMA.solution : type_of% @OMA.S_oeis_a192349.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : m + 5 - 1 = m + 3 + 1 := by omega
  have e2 : m + 5 - 2 = m + 2 + 1 := by omega
  have e3 : m + 5 - 3 = m + 1 + 1 := by omega
  have e4 : m + 5 - 4 = m + 1 := by omega
  have e0 : m + 5 = m + 4 + 1 := by omega
  rw [e1, e2, e3, e4, e0, A192349.a_eq, A192349.a_eq, A192349.a_eq, A192349.a_eq, A192349.a_eq]
  simp only [A192349.st]
  ring
