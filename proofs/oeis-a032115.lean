import OMAStatements.S_oeis_a032115

-- Problem: A032115: 'BIJ' (reversible, indistinct, labeled) transform of 1,3,5,7...
-- Upstream: formal-conjectures statements/oeis-a032115.lean:0 (declaration OMA.S_oeis_a032115.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A032115Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G P E : ℚ⟦X⟧)
    (hE : derivative ℚ E = E)
    (hPE : P * ((1 - 2 * X) * E) = 1)
    (hG : (2) * G = (2) + (1) * P + (-1 + 2 * X) * E) :
    (X ^ 5 - 2 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (-12 * X ^ 5 + 4 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (16 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2 * X ^ 5 - 4 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-9 * X ^ 5 + 2 * X ^ 6) * derivative ℚ G + (2 * X ^ 5) * G =
      2 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have dd2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have hLP : derivative ℚ (P * ((1 - 2 * X) * E)) =
      derivative ℚ P * ((1 - 2 * X) * E) + P * (-2 * E + (1 - 2 * X) * derivative ℚ E) := by
    simp [Derivation.leibniz, dd2]
    ring
  have hdP : derivative ℚ P * ((1 - 2 * X) * E) + P * (-2 * E + (1 - 2 * X) * derivative ℚ E) = 0 := by
    rw [← hLP, hPE]
    simp
  have hEne : E ≠ 0 := by
    intro h
    rw [h] at hPE
    simp at hPE
  have r0_1 : (1 - 2 * X : ℚ⟦X⟧) * derivative ℚ P =
      (1 + 2 * X : ℚ⟦X⟧) * P := by
    have hEr : E * ((1 - 2 * X) * derivative ℚ P - (1 + 2 * X) * P) = 0 := by
      linear_combination hdP - P * (1 - 2 * X) * hE
    have h := (mul_eq_zero.mp hEr).resolve_left hEne
    linear_combination h
  have hLr0_2 : derivative ℚ ((1 - 2 * X : ℚ⟦X⟧) * derivative ℚ P) =
      (-2) * derivative ℚ P + (1 - 2 * X) * derivative ℚ (derivative ℚ P) := by
    simp [Derivation.leibniz, d2]
    ring
  have hRr0_2 : derivative ℚ ((1 + 2 * X : ℚ⟦X⟧) * P) =
      (2) * P + (1 + 2 * X) * derivative ℚ P := by
    simp [Derivation.leibniz, d2]
    ring
  have r0_2 : (-2) * derivative ℚ P + (1 - 2 * X) * derivative ℚ (derivative ℚ P) =
      (2) * P + (1 + 2 * X) * derivative ℚ P := by
    rw [← hLr0_2, ← hRr0_2, r0_1]
  have r0_2p : (-2 : ℚ⟦X⟧) * derivative ℚ P + (1 - 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P) =
      (2 : ℚ⟦X⟧) * P + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ P := by linear_combination r0_2
  have hLr0_3 : derivative ℚ ((-2 : ℚ⟦X⟧) * derivative ℚ P + (1 - 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) =
      (0) * derivative ℚ P + 2 * (-2) * derivative ℚ (derivative ℚ P) + (1 - 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ P)) := by
    simp [Derivation.leibniz, d2]
    ring
  have hRr0_3 : derivative ℚ ((2 : ℚ⟦X⟧) * P + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ P) =
      (0) * P + 2 * (2) * derivative ℚ P + (1 + 2 * X) * derivative ℚ (derivative ℚ P) := by
    simp [Derivation.leibniz, d2]
    ring
  have r0_3 : (0) * derivative ℚ P + 2 * (-2) * derivative ℚ (derivative ℚ P) + (1 - 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ P)) =
      (0) * P + 2 * (2) * derivative ℚ P + (1 + 2 * X) * derivative ℚ (derivative ℚ P) := by
    rw [← hLr0_3, ← hRr0_3, r0_2p]
  have r0_3p : (0 : ℚ⟦X⟧) * derivative ℚ P + 2 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + (1 - 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P)) =
      (0 : ℚ⟦X⟧) * P + 2 * ((2 : ℚ⟦X⟧) * derivative ℚ P) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P) := by linear_combination r0_3
  have hLr0_4 : derivative ℚ ((0 : ℚ⟦X⟧) * derivative ℚ P + 2 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + (1 - 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P))) =
      (0) * derivative ℚ P + 3 * (0) * derivative ℚ (derivative ℚ P) + 3 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (1 - 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) := by
    simp [Derivation.leibniz, d2]
    ring
  have hRr0_4 : derivative ℚ ((0 : ℚ⟦X⟧) * P + 2 * ((2 : ℚ⟦X⟧) * derivative ℚ P) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) =
      (0) * P + 3 * (0) * derivative ℚ P + 3 * (2) * derivative ℚ (derivative ℚ P) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ P)) := by
    simp [Derivation.leibniz, d2]
    ring
  have r0_4 : (0) * derivative ℚ P + 3 * (0) * derivative ℚ (derivative ℚ P) + 3 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (1 - 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) =
      (0) * P + 3 * (0) * derivative ℚ P + 3 * (2) * derivative ℚ (derivative ℚ P) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ P)) := by
    rw [← hLr0_4, ← hRr0_4, r0_3p]
  have r0_4p : (0 : ℚ⟦X⟧) * derivative ℚ P + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P))) + (1 - 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) =
      (0 : ℚ⟦X⟧) * P + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + 3 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P)) := by linear_combination r0_4
  have hLr0_5 : derivative ℚ ((0 : ℚ⟦X⟧) * derivative ℚ P + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P))) + (1 - 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P)))) =
      (0) * derivative ℚ P + 4 * (0) * derivative ℚ (derivative ℚ P) + 6 * (0) * derivative ℚ (derivative ℚ (derivative ℚ P)) + 4 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (1 - 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P)))) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hRr0_5 : derivative ℚ ((0 : ℚ⟦X⟧) * P + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + 3 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P))) =
      (0) * P + 4 * (0) * derivative ℚ P + 6 * (0) * derivative ℚ (derivative ℚ P) + 4 * (2) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have r0_5 : (0) * derivative ℚ P + 4 * (0) * derivative ℚ (derivative ℚ P) + 6 * (0) * derivative ℚ (derivative ℚ (derivative ℚ P)) + 4 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (1 - 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P)))) =
      (0) * P + 4 * (0) * derivative ℚ P + 6 * (0) * derivative ℚ (derivative ℚ P) + 4 * (2) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) := by
    rw [← hLr0_5, ← hRr0_5, r0_4p]
  have r1_1 : (1 : ℚ⟦X⟧) * derivative ℚ E =
      (1 : ℚ⟦X⟧) * E := by
    linear_combination hE
  have hLr1_2 : derivative ℚ ((1 : ℚ⟦X⟧) * derivative ℚ E) =
      (0) * derivative ℚ E + (1) * derivative ℚ (derivative ℚ E) := by
    simp
  have hRr1_2 : derivative ℚ ((1 : ℚ⟦X⟧) * E) =
      (0) * E + (1) * derivative ℚ E := by
    simp
  have r1_2 : (0) * derivative ℚ E + (1) * derivative ℚ (derivative ℚ E) =
      (0) * E + (1) * derivative ℚ E := by
    rw [← hLr1_2, ← hRr1_2, r1_1]
  have r1_2p : (0 : ℚ⟦X⟧) * derivative ℚ E + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E) =
      (0 : ℚ⟦X⟧) * E + (1 : ℚ⟦X⟧) * derivative ℚ E := by linear_combination r1_2
  have hLr1_3 : derivative ℚ ((0 : ℚ⟦X⟧) * derivative ℚ E + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) =
      (0) * derivative ℚ E + 2 * (0) * derivative ℚ (derivative ℚ E) + (1) * derivative ℚ (derivative ℚ (derivative ℚ E)) := by
    simp
  have hRr1_3 : derivative ℚ ((0 : ℚ⟦X⟧) * E + (1 : ℚ⟦X⟧) * derivative ℚ E) =
      (0) * E + 2 * (0) * derivative ℚ E + (1) * derivative ℚ (derivative ℚ E) := by
    simp
  have r1_3 : (0) * derivative ℚ E + 2 * (0) * derivative ℚ (derivative ℚ E) + (1) * derivative ℚ (derivative ℚ (derivative ℚ E)) =
      (0) * E + 2 * (0) * derivative ℚ E + (1) * derivative ℚ (derivative ℚ E) := by
    rw [← hLr1_3, ← hRr1_3, r1_2p]
  have r1_3p : (0 : ℚ⟦X⟧) * derivative ℚ E + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E)) =
      (0 : ℚ⟦X⟧) * E + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E) := by linear_combination r1_3
  have hLr1_4 : derivative ℚ ((0 : ℚ⟦X⟧) * derivative ℚ E + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E))) =
      (0) * derivative ℚ E + 3 * (0) * derivative ℚ (derivative ℚ E) + 3 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) := by
    simp
  have hRr1_4 : derivative ℚ ((0 : ℚ⟦X⟧) * E + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) =
      (0) * E + 3 * (0) * derivative ℚ E + 3 * (0) * derivative ℚ (derivative ℚ E) + (1) * derivative ℚ (derivative ℚ (derivative ℚ E)) := by
    simp
  have r1_4 : (0) * derivative ℚ E + 3 * (0) * derivative ℚ (derivative ℚ E) + 3 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) =
      (0) * E + 3 * (0) * derivative ℚ E + 3 * (0) * derivative ℚ (derivative ℚ E) + (1) * derivative ℚ (derivative ℚ (derivative ℚ E)) := by
    rw [← hLr1_4, ← hRr1_4, r1_3p]
  have r1_4p : (0 : ℚ⟦X⟧) * derivative ℚ E + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E))) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) =
      (0 : ℚ⟦X⟧) * E + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E)) := by linear_combination r1_4
  have hLr1_5 : derivative ℚ ((0 : ℚ⟦X⟧) * derivative ℚ E + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E))) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E)))) =
      (0) * derivative ℚ E + 4 * (0) * derivative ℚ (derivative ℚ E) + 6 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E)))) := by
    simp
  have hRr1_5 : derivative ℚ ((0 : ℚ⟦X⟧) * E + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E))) =
      (0) * E + 4 * (0) * derivative ℚ E + 6 * (0) * derivative ℚ (derivative ℚ E) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) := by
    simp
  have r1_5 : (0) * derivative ℚ E + 4 * (0) * derivative ℚ (derivative ℚ E) + 6 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E)))) =
      (0) * E + 4 * (0) * derivative ℚ E + 6 * (0) * derivative ℚ (derivative ℚ E) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) := by
    rw [← hLr1_5, ← hRr1_5, r1_4p]
  have e0 : (2 : ℚ⟦X⟧) * G =
      (2 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * P + (-1 + 2 * X : ℚ⟦X⟧) * E := by linear_combination hG
  have hLe1 : derivative ℚ ((2 : ℚ⟦X⟧) * G) =
      (0) * G + (2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
  have hRe1 : derivative ℚ ((2 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * P + (-1 + 2 * X : ℚ⟦X⟧) * E) =
      (0) + (0) * P + (1) * derivative ℚ P + (2) * E + (-1 + 2 * X) * derivative ℚ E := by
    simp [Derivation.leibniz, d2]
    ring
  have e1 : (0) * G + (2) * derivative ℚ G =
      (0) + (0) * P + (1) * derivative ℚ P + (2) * E + (-1 + 2 * X) * derivative ℚ E := by
    rw [← hLe1, ← hRe1, e0]
  have e1p : (0 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * derivative ℚ G =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + (1 : ℚ⟦X⟧) * derivative ℚ P + (2 : ℚ⟦X⟧) * E + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ E := by linear_combination e1
  have hLe2 : derivative ℚ ((0 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * derivative ℚ G) =
      (0) * G + 2 * (0) * derivative ℚ G + (2) * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, d2]
  have hRe2 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + (1 : ℚ⟦X⟧) * derivative ℚ P + (2 : ℚ⟦X⟧) * E + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ E) =
      (0) + (0) * P + 2 * (0) * derivative ℚ P + (1) * derivative ℚ (derivative ℚ P) + (0) * E + 2 * (2) * derivative ℚ E + (-1 + 2 * X) * derivative ℚ (derivative ℚ E) := by
    simp [Derivation.leibniz, d2]
    ring
  have e2 : (0) * G + 2 * (0) * derivative ℚ G + (2) * derivative ℚ (derivative ℚ G) =
      (0) + (0) * P + 2 * (0) * derivative ℚ P + (1) * derivative ℚ (derivative ℚ P) + (0) * E + 2 * (2) * derivative ℚ E + (-1 + 2 * X) * derivative ℚ (derivative ℚ E) := by
    rw [← hLe2, ← hRe2, e1p]
  have e2p : (0 : ℚ⟦X⟧) * G + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P) + (0 : ℚ⟦X⟧) * E + 2 * ((2 : ℚ⟦X⟧) * derivative ℚ E) + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E) := by linear_combination e2
  have hLe3 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) =
      (0) * G + 3 * (0) * derivative ℚ G + 3 * (0) * derivative ℚ (derivative ℚ G) + (2) * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2]
  have hRe3 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P) + (0 : ℚ⟦X⟧) * E + 2 * ((2 : ℚ⟦X⟧) * derivative ℚ E) + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) =
      (0) + (0) * P + 3 * (0) * derivative ℚ P + 3 * (0) * derivative ℚ (derivative ℚ P) + (1) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (0) * E + 3 * (0) * derivative ℚ E + 3 * (2) * derivative ℚ (derivative ℚ E) + (-1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ E)) := by
    simp [Derivation.leibniz, d2]
    ring
  have e3 : (0) * G + 3 * (0) * derivative ℚ G + 3 * (0) * derivative ℚ (derivative ℚ G) + (2) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0) + (0) * P + 3 * (0) * derivative ℚ P + 3 * (0) * derivative ℚ (derivative ℚ P) + (1) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (0) * E + 3 * (0) * derivative ℚ E + 3 * (2) * derivative ℚ (derivative ℚ E) + (-1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ E)) := by
    rw [← hLe3, ← hRe3, e2p]
  have e3p : (0 : ℚ⟦X⟧) * G + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (0 : ℚ⟦X⟧) * E + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + 3 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E)) := by linear_combination e3
  have hLe4 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0) * G + 4 * (0) * derivative ℚ G + 6 * (0) * derivative ℚ (derivative ℚ G) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2]
  have hRe4 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (0 : ℚ⟦X⟧) * E + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + 3 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E))) =
      (0) + (0) * P + 4 * (0) * derivative ℚ P + 6 * (0) * derivative ℚ (derivative ℚ P) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (0) * E + 4 * (0) * derivative ℚ E + 6 * (0) * derivative ℚ (derivative ℚ E) + 4 * (2) * derivative ℚ (derivative ℚ (derivative ℚ E)) + (-1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have e4 : (0) * G + 4 * (0) * derivative ℚ G + 6 * (0) * derivative ℚ (derivative ℚ G) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0) + (0) * P + 4 * (0) * derivative ℚ P + 6 * (0) * derivative ℚ (derivative ℚ P) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ P)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (0) * E + 4 * (0) * derivative ℚ E + 6 * (0) * derivative ℚ (derivative ℚ E) + 4 * (2) * derivative ℚ (derivative ℚ (derivative ℚ E)) + (-1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) := by
    rw [← hLe4, ← hRe4, e3p]
  have e4p : (0 : ℚ⟦X⟧) * G + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P))) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (0 : ℚ⟦X⟧) * E + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + 4 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E))) + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) := by linear_combination e4
  have hLe5 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (0) * G + 5 * (0) * derivative ℚ G + 10 * (0) * derivative ℚ (derivative ℚ G) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) := by
    simp [Derivation.leibniz, d2]
  have hRe5 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * P + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ P) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ P)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ P))) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (0 : ℚ⟦X⟧) * E + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ E) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ E)) + 4 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ E))) + (-1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E)))) =
      (0) + (0) * P + 5 * (0) * derivative ℚ P + 10 * (0) * derivative ℚ (derivative ℚ P) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ P)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P)))) + (0) * E + 5 * (0) * derivative ℚ E + 10 * (0) * derivative ℚ (derivative ℚ E) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + 5 * (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) + (-1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E)))) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have e5 : (0) * G + 5 * (0) * derivative ℚ G + 10 * (0) * derivative ℚ (derivative ℚ G) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (0) + (0) * P + 5 * (0) * derivative ℚ P + 10 * (0) * derivative ℚ (derivative ℚ P) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ P)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P))) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ P)))) + (0) * E + 5 * (0) * derivative ℚ E + 10 * (0) * derivative ℚ (derivative ℚ E) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ E)) + 5 * (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E))) + (-1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ E)))) := by
    rw [← hLe5, ← hRe5, e4p]
  have hfull : (2 : ℚ⟦X⟧) * ((X ^ 5 - 2 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (-12 * X ^ 5 + 4 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (16 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2 * X ^ 5 - 4 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-9 * X ^ 5 + 2 * X ^ 6) * derivative ℚ G + (2 * X ^ 5) * G - (2 * X ^ 5)) = 0 := by
    linear_combination (X ^ 5 - 2 * X ^ 6) * e5 +
      (-12 * X ^ 5 + 4 * X ^ 6) * e4 +
      (16 * X ^ 5) * e3 +
      (2 * X ^ 5 - 4 * X ^ 6) * e2 +
      (-9 * X ^ 5 + 2 * X ^ 6) * e1 +
      (2 * X ^ 5) * e0 +
      (X ^ 5) * r0_5 +
      (-X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7) * r1_5 +
      (-3 * X ^ 5) * r0_4 +
      (21 * X ^ 5 - 44 * X ^ 6 + 4 * X ^ 7) * r1_4 +
      (3 * X ^ 5) * r0_3 +
      (-91 * X ^ 5 + 20 * X ^ 6 + 4 * X ^ 7) * r1_3 +
      (-X ^ 5) * r0_2 +
      (3 * X ^ 5 + 28 * X ^ 6 - 4 * X ^ 7) * r1_2 +
      (20 * X ^ 5 - 8 * X ^ 6) * r1_1
  have hM0 : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp [kc] at h'
  have h := (mul_eq_zero.mp hfull).resolve_left hM0
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G P E : ℚ⟦X⟧)
    (hE : derivative ℚ E = E)
    (hPE : P * ((1 - 2 * X) * E) = 1)
    (hG : (2) * G = (2) + (1) * P + (-1 + 2 * X) * E) :
    derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * X * C (-2) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * C (-12) + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * C 4 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 16 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 2 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-4) + derivative ℚ G * X * X * X * X * X * C (-9) +
      derivative ℚ G * X * X * X * X * X * X * C 2 + G * X * X * X * X * X * C 2 =
      C 2 * X * X * X * X * X := by
  have h := key G P E hE hPE hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G P E : ℚ⟦X⟧)
    (hE : derivative ℚ E = E)
    (hPE : P * ((1 - 2 * X) * E) = 1)
    (hG : (2) * G = (2) + (1) * P + (-1 + 2 * X) * E) (m : ℕ) :
    1 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 4 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1) G +
      16 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G + 2 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-4) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-9) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      2 * ((m : ℚ) + 1) * coeff (m + 1) G + 2 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G P E hE hPE hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A032115Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a032115.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5]
  have hE : PowerSeries.derivative ℚ (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
    rw [PowerSeries.derivative_exp]
  have hc : PowerSeries.constantCoeff ((1 - 2 * PowerSeries.X) * PowerSeries.exp ℚ : PowerSeries ℚ) ≠ 0 := by
    simp
  have hPE : ((1 - 2 * PowerSeries.X) * PowerSeries.exp ℚ)⁻¹ * ((1 - 2 * PowerSeries.X) * PowerSeries.exp ℚ) = 1 := PowerSeries.inv_mul_cancel _ hc
  have hGl : (2) * G = (2) + (1) * ((1 - 2 * PowerSeries.X) * PowerSeries.exp ℚ)⁻¹ + (-1 + 2 * PowerSeries.X) * PowerSeries.exp ℚ := by
    linear_combination ((1 - 2 * PowerSeries.X) * PowerSeries.exp ℚ)⁻¹ * hG - (2 * G - 2 + (1 - 2 * PowerSeries.X) * PowerSeries.exp ℚ) * hPE
  unfold OMA.S_oeis_a032115.a
  have r := A032115Aux.rel G (((1 - 2 * PowerSeries.X) * PowerSeries.exp ℚ)⁻¹) (PowerSeries.exp ℚ) hE hPE hGl m
  simp only [Nat.factorial_succ]
  push_cast
  linear_combination (((m : ℚ) + 1) * (m.factorial : ℚ)) * r
