import OMAStatements.S_oeis_a181142

-- Problem: A181142: Number of permutations of {1,2,...,2n} , say x(1),x(2), ... , x(2n) , such that x(i) + x(i+1) is not equal to 2n-1 for all i, 1<=i<=2n-1.
-- Upstream: formal-conjectures statements/oeis-a181142.lean:0 (declaration OMA.S_oeis_a181142.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Put J(p,q) = Sum_{k<=q} C(q,k) (-2)^k (p+q-k)!, so that a(n) = J(n+1,n-1). Pascal's rule gives
J(p,q+1) = J(p+1,q) - 2 J(p,q), and splitting (p+q+2-k) = (p+1) + (q+1-k) gives
J(p+1,q+1) = (p+1) J(p,q+1) + (q+1) J(p+1,q). Together they give the three-term recurrence
J(p+2,q+1) = (p+q+5) J(p+1,q+1) - 2 (p+1) J(p,q+1) in p, and the recurrence of the statement is a
combination of instances of these relations. -/

namespace A181142Aux

open OMA.S_oeis_a181142

def J (p q : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (q + 1), (q.choose k : ℤ) * (-2) ^ k * ((p + q - k).factorial : ℤ)

theorem a_eq (m : ℕ) : a (m + 1) = J (m + 2) m := by
  unfold a J
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [show m + 1 - 1 = m from rfl, show 2 * (m + 1) - k = m + 2 + m - k by omega]

theorem R1 (p q : ℕ) : J p (q + 1) = J (p + 1) q - 2 * J p q := by
  unfold J
  have hL := Finset.sum_range_succ'
    (fun k => ((q + 1).choose k : ℤ) * (-2) ^ k * ((p + (q + 1) - k).factorial : ℤ)) (q + 1)
  have hM := Finset.sum_range_succ'
    (fun k => (q.choose k : ℤ) * (-2) ^ k * ((p + 1 + q - k).factorial : ℤ)) (q + 1)
  have hterm : ∀ k ∈ Finset.range (q + 1),
      ((q + 1).choose (k + 1) : ℤ) * (-2) ^ (k + 1) * ((p + (q + 1) - (k + 1)).factorial : ℤ) =
        (q.choose (k + 1) : ℤ) * (-2) ^ (k + 1) * ((p + 1 + q - (k + 1)).factorial : ℤ) -
          2 * ((q.choose k : ℤ) * (-2) ^ k * ((p + q - k).factorial : ℤ)) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [show p + (q + 1) - (k + 1) = p + q - k by omega, show p + 1 + q - (k + 1) = p + q - k by omega,
      Nat.choose_succ_succ' q k]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum] at hL
  rw [Finset.sum_range_succ
    (fun k => (q.choose k : ℤ) * (-2) ^ k * ((p + 1 + q - k).factorial : ℤ)) (q + 1)] at hM
  simp only [Nat.choose_succ_self, Nat.choose_zero_right, Nat.cast_zero, Nat.cast_one, zero_mul, pow_zero,
    one_mul, mul_one, add_zero, Nat.sub_zero] at hL hM
  have hfac : ((p + (q + 1)).factorial : ℤ) = ((p + 1 + q).factorial : ℤ) := by
    rw [show p + (q + 1) = p + 1 + q by ring]
  linear_combination hL - hM + hfac

theorem R2 (p q : ℕ) :
    J (p + 1) (q + 1) = ((p : ℤ) + 1) * J p (q + 1) + ((q : ℤ) + 1) * J (p + 1) q := by
  unfold J
  have hterm : ∀ k ∈ Finset.range (q + 1 + 1),
      ((q + 1).choose k : ℤ) * (-2) ^ k * ((p + 1 + (q + 1) - k).factorial : ℤ) =
        ((p : ℤ) + 1) * (((q + 1).choose k : ℤ) * (-2) ^ k * ((p + (q + 1) - k).factorial : ℤ)) +
          ((q : ℤ) + 1) * ((q.choose k : ℤ) * (-2) ^ k * ((p + 1 + q - k).factorial : ℤ)) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hc := Nat.choose_mul_succ_eq q k
    zify [show k ≤ q + 1 by omega] at hc
    have hD : ((p + 1 + (q + 1) - k).factorial : ℤ) =
        ((p : ℤ) + (q : ℤ) + 2 - (k : ℤ)) * ((p + (q + 1) - k).factorial : ℤ) := by
      rw [show p + 1 + (q + 1) - k = (p + (q + 1) - k) + 1 by omega, Nat.factorial_succ]
      push_cast [Nat.cast_sub (show k ≤ p + (q + 1) by omega)]
      ring
    rw [hD, show p + 1 + q - k = p + (q + 1) - k by omega]
    linear_combination (-((-2 : ℤ) ^ k * ((p + (q + 1) - k).factorial : ℤ))) * hc
  have hpeel : (∑ k ∈ Finset.range (q + 1 + 1),
      (q.choose k : ℤ) * (-2) ^ k * ((p + 1 + q - k).factorial : ℤ)) =
      ∑ k ∈ Finset.range (q + 1), (q.choose k : ℤ) * (-2) ^ k * ((p + 1 + q - k).factorial : ℤ) :=
    (Finset.sum_range_succ _ _).trans (by simp)
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hpeel]

theorem R3 (p q : ℕ) :
    J (p + 1 + 1) (q + 1) =
      ((p : ℤ) + (q : ℤ) + 5) * J (p + 1) (q + 1) - 2 * ((p : ℤ) + 1) * J p (q + 1) := by
  have Ea := R2 (p + 1) q
  have Eb := R1 (p + 1) q
  have Ec := R2 p q
  push_cast at Ea
  linear_combination Ea - ((q : ℤ) + 1) * Eb - 2 * Ec

end A181142Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a181142.main := by
  intro n hn
  obtain ⟨Q, rfl⟩ : ∃ Q, n = Q + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  rw [show Q + 1 + 1 + 1 - 1 = Q + 1 + 1 from rfl, show Q + 1 + 1 + 1 - 2 = Q + 1 from rfl,
    A181142Aux.a_eq (Q + 1 + 1), A181142Aux.a_eq (Q + 1), A181142Aux.a_eq Q]
  have E1 := A181142Aux.R1 (Q + 4) (Q + 1)
  have E2 := A181142Aux.R2 (Q + 1) Q
  have F1 := A181142Aux.R3 (Q + 1) Q
  have F2 := A181142Aux.R3 (Q + 2) Q
  have F3 := A181142Aux.R3 (Q + 3) Q
  simp only [Nat.add_assoc, Nat.reduceAdd] at E1 E2 F1 F2 F3 ⊢
  push_cast at E1 E2 F1 F2 F3 ⊢
  linear_combination (-((Q : ℤ) + 2)) * E1 + (-4 * ((Q : ℤ) + 3) ^ 2) * E2 + (-2 * ((Q : ℤ) + 3) ^ 2) * F1 +
    (-((Q : ℤ) + 2) * (2 * (Q : ℤ) + 6)) * F2 + (-((Q : ℤ) + 2)) * F3
