import OMAStatements.S_oeis_a112849

-- Problem: A112849: Number of congruence classes (epimorphisms/vertex partitionings induced by graph endomorphisms) of undirected cycles of even length: |C(C_{2*n})|.
-- Upstream: formal-conjectures statements/oeis-a112849.lean:0 (declaration OMA.S_oeis_a112849.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n ≥ 2 the two binomial coefficients are equal and add up to the central binomial coefficient
binomial(2n, n), so a(n) = 1 + binomial(2n, n)/2. The recurrence then follows from
(n + 1) * binomial(2n + 2, n + 1) = 2 * (2n + 1) * binomial(2n, n), applied twice. -/

namespace A112849Aux

theorem half (j : ℕ) : ((2 * j + 1).choose j : ℚ) = (Nat.centralBinom (j + 1) : ℚ) / 2 ∧
    ((2 * j + 1).choose (j + 1) : ℚ) = (Nat.centralBinom (j + 1) : ℚ) / 2 := by
  have h1 : (2 * j + 1).choose (j + 1) = (2 * j + 1).choose j := Nat.choose_symm_half j
  have h2 : Nat.centralBinom (j + 1) = (2 * j + 1).choose j + (2 * j + 1).choose (j + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [e, Nat.choose_succ_succ]
  have h1' : ((2 * j + 1).choose (j + 1) : ℚ) = ((2 * j + 1).choose j : ℚ) := by exact_mod_cast h1
  have h2' : (Nat.centralBinom (j + 1) : ℚ) =
      ((2 * j + 1).choose j : ℚ) + ((2 * j + 1).choose (j + 1) : ℚ) := by exact_mod_cast h2
  constructor <;> linarith

theorem step (k : ℕ) : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
    2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : (((k + 1) * Nat.centralBinom (k + 1) : ℕ) : ℚ) =
      ((2 * (2 * k + 1) * Nat.centralBinom k : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at h'
  linear_combination h'

end A112849Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a112849.main := by
  intro a _ ha n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := rfl
  have e2 : m + 4 - 2 = m + 2 := rfl
  rw [e1, e2]
  have f (j : ℕ) : a (j + 2) = 1 + (Nat.centralBinom (j + 2) : ℚ) / 2 := by
    have h := ha (j + 2) (by omega)
    have i1 : 2 * (j + 2) - 1 = 2 * (j + 1) + 1 := by omega
    have i2 : j + 2 - 1 = j + 1 := rfl
    rw [i1, i2] at h
    obtain ⟨p, q⟩ := A112849Aux.half (j + 1)
    rw [h, p, q]
    ring
  have r1 := A112849Aux.step (m + 2)
  have r2 := A112849Aux.step (m + 3)
  rw [f (m + 2), f (m + 1), f m]
  push_cast at r1 r2 ⊢
  linear_combination (3 * ((m : ℚ) + 4) - 5) / 2 * r2 - (3 * ((m : ℚ) + 4) - 2) / 2 * r1
