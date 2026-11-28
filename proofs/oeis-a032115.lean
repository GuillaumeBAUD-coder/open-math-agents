import OMAStatements.S_oeis_a032115
import Mathlib

namespace A032115Proof

open PowerSeries

lemma two_eq : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm

lemma d_two_X : derivative ℚ ((2 : PowerSeries ℚ) * X) = 2 := by
  rw [two_eq, Derivation.leibniz, derivative_X, derivative_C]
  simp

lemma d_u : derivative ℚ ((1 : PowerSeries ℚ) - 2 * X) = -2 := by
  rw [map_sub, d_two_X, Derivation.map_one_eq_zero, zero_sub]

lemma coeff_theta (F : PowerSeries ℚ) (k : ℕ) :
    coeff k (X * derivative ℚ F) = (k : ℚ) * coeff k F := by
  cases k with
  | zero => simp
  | succ j =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma coeff_E (t : ℕ) : coeff t (exp ℚ) = 1 / (t.factorial : ℚ) := by
  rw [coeff_exp]
  simp

lemma wfac (t : ℕ) :
    ((t + 1).factorial : ℚ) * coeff (t + 1) ((1 - 2 * X) * exp ℚ) = 1 - 2 * ((t : ℚ) + 1) := by
  have h : coeff (t + 1) ((1 - 2 * X) * exp ℚ)
      = coeff (t + 1) (exp ℚ) - 2 * coeff t (exp ℚ) := by
    rw [two_eq, sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul]
  have hn : (t + 1).factorial = (t + 1) * t.factorial := Nat.factorial_succ t
  have ht : (t.factorial : ℚ) ≠ 0 := by positivity
  have ht1 : ((t : ℚ) + 1) ≠ 0 := by positivity
  rw [h, coeff_E, coeff_E, hn]
  push_cast
  field_simp

lemma main_proof : type_of% @OMA.S_oeis_a032115.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℚ,
      V = C (2 : ℚ) * G - C (2 : ℚ) + (1 - 2 * X) * exp ℚ := ⟨_, rfl⟩
  have hVW : V * ((1 - 2 * X) * exp ℚ) = 1 := by
    rw [hV, ← two_eq]
    linear_combination hG
  have dW : derivative ℚ ((1 - 2 * X) * exp ℚ) = (-1 - 2 * X) * exp ℚ := by
    rw [Derivation.leibniz, derivative_exp, d_u]
    simp only [smul_eq_mul]
    ring
  have h0 : V * ((-1 - 2 * X) * exp ℚ) + (1 - 2 * X) * exp ℚ * derivative ℚ V = 0 := by
    have h : derivative ℚ (V * ((1 - 2 * X) * exp ℚ)) = derivative ℚ 1 := by rw [hVW]
    rw [Derivation.leibniz, dW, Derivation.map_one_eq_zero] at h
    simp only [smul_eq_mul] at h
    exact h
  have ode : (1 - 2 * X) * derivative ℚ V = (1 + 2 * X) * V := by
    linear_combination (V * (1 - 2 * X)) * h0
      - ((1 - 2 * X) * derivative ℚ V - (1 + 2 * X) * V) * hVW
  obtain ⟨θ, hθ⟩ : ∃ θ : PowerSeries ℚ, θ = X * derivative ℚ V := ⟨_, rfl⟩
  have hθc : ∀ k : ℕ, coeff k θ = (k : ℚ) * coeff k V := by
    intro k
    rw [hθ]
    exact coeff_theta V k
  have odeX : θ - C (2 : ℚ) * (X * θ) = X * V + C (2 : ℚ) * (X * (X * V)) := by
    rw [hθ, ← two_eq]
    linear_combination X * ode
  have K : ∀ k : ℕ, ((k + 2 : ℕ) : ℚ) * coeff (k + 2) V
      - 2 * (((k + 1 : ℕ) : ℚ) * coeff (k + 1) V) = coeff (k + 1) V + 2 * coeff k V := by
    intro k
    have h := congrArg (fun s => coeff (k + 2) s) odeX
    simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, hθc] at h
    exact h
  have hc : ∀ t : ℕ, ((t + 1).factorial : ℚ) * coeff (t + 1) V
      = 2 * (((t + 1).factorial : ℚ) * coeff (t + 1) G) + 1 - 2 * ((t : ℚ) + 1) := by
    intro t
    have hw := wfac t
    have h : coeff (t + 1) V
        = 2 * coeff (t + 1) G + coeff (t + 1) ((1 - 2 * X) * exp ℚ) := by
      rw [hV, map_add, map_sub, coeff_C_mul, coeff_C, if_neg (by omega : ¬ (t + 1 = 0)), sub_zero]
    rw [h]
    linear_combination hw
  have rel : ∀ j : ℕ, OMA.S_oeis_a032115.a G (j + 3)
      - (2 * (j : ℚ) + 5) * OMA.S_oeis_a032115.a G (j + 2)
      - 2 * ((j : ℚ) + 2) * OMA.S_oeis_a032115.a G (j + 1)
      + (4 * (j : ℚ) ^ 2 + 12 * (j : ℚ) + 7) = 0 := by
    intro j
    have k := K (j + 1)
    have v1 := hc j
    have v2 := hc (j + 1)
    have v3 := hc (j + 2)
    have F2n : (j + 2).factorial = (j + 2) * (j + 1).factorial := Nat.factorial_succ (j + 1)
    have F3n : (j + 3).factorial = (j + 3) * (j + 2).factorial := Nat.factorial_succ (j + 2)
    have F2 : ((j + 2).factorial : ℚ) = ((j : ℚ) + 2) * ((j + 1).factorial : ℚ) := by
      rw [F2n]; push_cast; ring
    have F3 : ((j + 3).factorial : ℚ)
        = ((j : ℚ) + 3) * (((j : ℚ) + 2) * ((j + 1).factorial : ℚ)) := by
      rw [F3n, F2n]; push_cast; ring
    simp only [Nat.add_assoc, Nat.reduceAdd] at k v2 v3
    unfold OMA.S_oeis_a032115.a
    rw [F3] at v3 ⊢
    rw [F2] at v2 ⊢
    push_cast at k v1 v2 v3 ⊢
    linear_combination (((j : ℚ) + 2) * ((j + 1).factorial : ℚ) / 2) * k - (1 / 2) * v3
      + ((2 * (j : ℚ) + 5) / 2) * v2 + ((j : ℚ) + 2) * v1
  have r3 := rel (m + 3)
  have r2 := rel (m + 2)
  have r1 := rel (m + 1)
  have r0 := rel m
  simp only [Nat.add_assoc, Nat.reduceAdd] at r3 r2 r1
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  push_cast at r3 r2 r1 ⊢
  linear_combination r3 - 3 * r2 + 3 * r1 - r0

end A032115Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a032115.main :=
  A032115Proof.main_proof
