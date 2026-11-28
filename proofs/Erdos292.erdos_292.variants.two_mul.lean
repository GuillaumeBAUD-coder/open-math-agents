import FormalConjectures.ErdosProblems.«292»

-- Problem: Erdős Problem 292 — two mul
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/292.lean:83 (declaration Erdos292.erdos_292.variants.two_mul)
-- Credit: @GuillaumeBAUD-coder (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Double the denominators and insert the new term 1/2. -/

theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.two_mul := by
  rintro n ⟨S, hS, hn, hs⟩ h
  have h1 : 1 ∉ S := by
    intro h1
    have := Finset.single_lt_sum (f := fun m : ℕ => (1 : ℚ) / m) (by omega : n ≠ 1) h1 hn
      (by positivity : (0 : ℚ) < 1 / n) (by intros; positivity)
    simp only [Nat.cast_one, div_one, hs, lt_self_iff_false] at this
  refine ⟨insert 2 (S.image (2 * ·)), fun m hm => ?_, by simp [hn], ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_image] at hm
    obtain rfl | ⟨k, hk, rfl⟩ := hm
    · simp; omega
    · have := Finset.mem_Icc.1 (hS hk)
      simp; omega
  · rw [Finset.sum_insert (by simpa using h1), Finset.sum_image (by simp)]
    simp at hs ⊢
    rw [← Finset.sum_mul, hs]
    norm_num
