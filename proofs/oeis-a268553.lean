import OMAStatements.S_oeis_a268553
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: The constraints force a=b=c=n, so diagFactor n = (3n)!/(n!)^3; cancelling factorials gives
-- n^2 D(n) = 3(3n-1)(3n-2) D(n-1), and squaring yields the recurrence.

namespace OMA.A268553Proof
open OMA.S_oeis_a268553
lemma diag_eq (n : ℕ) :
    diagFactor n = (3 * n).factorial / (n.factorial * n.factorial * n.factorial) := by
  unfold diagFactor
  have hn : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single n, Finset.sum_eq_single n, Finset.sum_eq_single n]
  · rw [if_pos (by omega)]
    congr 2
    ring
  · intro c _ hc; rw [if_neg (by omega)]
  · intro h; exact absurd hn h
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _; rw [if_neg (by omega)]
  · intro h; exact absurd hn h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _; rw [if_neg (by omega)]
  · intro h; exact absurd hn h

lemma dvd3 (n : ℕ) : n.factorial * n.factorial * n.factorial ∣ (3 * n).factorial := by
  have h1 : n.factorial * n.factorial ∣ (n + n).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add n n
  have h2 : (n + n).factorial * n.factorial ∣ (n + n + n).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add (n + n) n
  have h3 : 3 * n = n + n + n := by ring
  rw [h3]
  exact (Nat.mul_dvd_mul_right h1 _).trans h2

lemma key (n : ℕ) : n.factorial * n.factorial * n.factorial *
    ((3 * n).factorial / (n.factorial * n.factorial * n.factorial)) = (3 * n).factorial :=
  Nat.mul_div_cancel' (dvd3 n)

lemma fac3 (m : ℕ) : (3 * (m + 1)).factorial
    = (3 * m + 3) * ((3 * m + 2) * ((3 * m + 1) * (3 * m).factorial)) := by
  have e : 3 * (m + 1) = 3 * m + 2 + 1 := by ring
  rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]

lemma rec (m : ℕ) :
    (m + 1) ^ 2 * diagFactor (m + 1) = 3 * (3 * m + 2) * (3 * m + 1) * diagFactor m := by
  rw [diag_eq, diag_eq]
  have hA := key (m + 1)
  have hB := key m
  set A := (3 * (m + 1)).factorial / ((m + 1).factorial * (m + 1).factorial * (m + 1).factorial)
  set B := (3 * m).factorial / (m.factorial * m.factorial * m.factorial)
  clear_value A B
  rw [fac3, Nat.factorial_succ] at hA
  have hpos : 0 < (m + 1) * (m.factorial * m.factorial * m.factorial) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (m + 1) * (m.factorial * m.factorial * m.factorial) * ((m + 1) ^ 2 * A)
      = (m + 1) * m.factorial * ((m + 1) * m.factorial) * ((m + 1) * m.factorial) * A := by ring
    _ = (3 * m + 3) * ((3 * m + 2) * ((3 * m + 1) * (3 * m).factorial)) := hA
    _ = _ := by rw [← hB]; ring
end OMA.A268553Proof

open OMA.S_oeis_a268553 in
theorem OMA.solution : type_of% @OMA.S_oeis_a268553.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := OMA.A268553Proof.rec m
  have e1 : m + 1 - 1 = m := by omega
  have e2 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
  have e3 : 3 * (m + 1) - 2 = 3 * m + 1 := by omega
  rw [e1, e2, e3]
  unfold a268553
  calc (m + 1) ^ 4 * (diagFactor (m + 1) * diagFactor (m + 1))
      = ((m + 1) ^ 2 * diagFactor (m + 1)) * ((m + 1) ^ 2 * diagFactor (m + 1)) := by ring
    _ = _ := by rw [h]; ring
