import FormalConjectures.GreensOpenProblems.«22»

-- Problem: Green's Open Problem 22 — lower nine
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/22.lean:115 (declaration Green22.green_22.variants.lower_nine)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Green22.green_22.variants.lower_nine := by
  intro r hr N hN
  obtain ⟨x, y, hx, hy, _, hprod, _⟩ :=
    hN (fun _ => ⟨0, Nat.pos_of_ne_zero hr⟩)
  have h := (Finset.mem_Icc.mp hprod).2
  have h9 : 9 ≤ x * y := by
    calc 9 = 3 * 3 := rfl
      _ ≤ x * y := Nat.mul_le_mul hx hy
  omega

