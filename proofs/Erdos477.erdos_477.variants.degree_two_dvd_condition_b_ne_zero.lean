import FormalConjectures.ErdosProblems.«477»

-- Problem: Erdős Problem 477 — degree two dvd condition b ne zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/477.lean:73 (declaration Erdos477.erdos_477.variants.degree_two_dvd_condition_b_ne_zero)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

theorem OMA.solution : type_of% @Erdos477.erdos_477.variants.degree_two_dvd_condition_b_ne_zero := by
  intro a b c ha hb hab f A
  by_contra h
  push_neg at h
  have hf : ∀ x : ℤ, f.eval x = a * x ^ 2 + b * x + c := by
    intro x; simp [f]
  obtain ⟨k, hk⟩ := hab
  have key : ∀ j : ℤ, f.eval j - f.eval (j - k) = 2 * b * j := by
    intro j; rw [hf, hf, hk]; ring
  -- uniqueness of representations
  have huniq : ∀ (z : ℤ) (p q : ℤ × ℤ), p ∈ A ×ˢ Set.range f.eval → z = p.1 + p.2 →
      q ∈ A ×ˢ Set.range f.eval → z = q.1 + q.2 → p = q := by
    intro z p q hp hpz hq hqz
    obtain ⟨r, _, hr⟩ := h z
    have e1 := hr p ⟨hp, hpz⟩
    have e2 := hr q ⟨hq, hqz⟩
    rw [e1, e2]
  -- A is finite: injective modulo 2b
  have hinj : Set.InjOn (fun x : ℤ => x % (2 * b)) A := by
    intro x1 hx1 x2 hx2 hmod
    simp only at hmod
    have hd : (2 * b) ∣ x2 - x1 := Int.ModEq.dvd hmod
    obtain ⟨j, hj⟩ := hd
    have e := huniq (x1 + f.eval j) (x1, f.eval j) (x2, f.eval (j - k))
      ⟨hx1, ⟨j, rfl⟩⟩ rfl ⟨hx2, ⟨j - k, rfl⟩⟩ (by
        have := key j
        simp only
        linarith)
    exact (Prod.mk.inj e).1
  have hfin : A.Finite := by
    apply Set.Finite.of_finite_image _ hinj
    apply (Set.finite_Ico (0 : ℤ) ((2 * b).natAbs : ℤ)).subset
    rintro _ ⟨x, _, rfl⟩
    have h2b : (2 * b) ≠ 0 := by positivity
    exact ⟨Int.emod_nonneg _ h2b, Int.emod_lt _ h2b⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · obtain ⟨U, hU⟩ := hfin.bddAbove
    obtain ⟨p, ⟨⟨hp1, ⟨m, hm⟩⟩, hpz⟩, _⟩ := h (U + c + b ^ 2 + 1)
    have h1 := hU hp1
    simp only at hm; rw [hf] at hm
    have : a * m ^ 2 + b * m + c ≤ c + b ^ 2 := by
      nlinarith [sq_nonneg m, sq_nonneg (2 * m - b), mul_nonneg (by linarith : (0:ℤ) ≤ -a - 1) (sq_nonneg m)]
    linarith
  · obtain ⟨L, hL⟩ := hfin.bddBelow
    obtain ⟨p, ⟨⟨hp1, ⟨m, hm⟩⟩, hpz⟩, _⟩ := h (L + c - b ^ 2 - 1)
    have h1 := hL hp1
    simp only at hm; rw [hf] at hm
    have : c - b ^ 2 ≤ a * m ^ 2 + b * m + c := by
      nlinarith [sq_nonneg m, sq_nonneg (2 * m + b), mul_nonneg (by linarith : (0:ℤ) ≤ a - 1) (sq_nonneg m)]
    linarith
