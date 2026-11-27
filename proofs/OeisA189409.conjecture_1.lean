import FormalConjectures.OEIS.«189409»

-- Problem: Primorial squared plus one — conjecture 1
-- Upstream: formal-conjectures FormalConjectures/OEIS/189409.lean:58 (declaration OeisA189409.conjecture_1)
-- Credit: @sebastianbachmaier (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.disproof : ¬ (type_of% @OeisA189409.conjecture_1) := by
  intro h
  have h9 : OeisA189409.a 9 = 223092870 ^ 2 + 1 := by
    simp [OeisA189409.a, Nat.kthPrimorial_succ]
  have hs := h 9
  rw [h9] at hs
  have hd : (29 * 29 : ℕ) ∣ 223092870 ^ 2 + 1 := ⟨59180057841661, by norm_num⟩
  have := hs 29 hd
  norm_num at this
