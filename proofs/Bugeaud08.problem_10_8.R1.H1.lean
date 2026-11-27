import OMAReductions.R_Bugeaud08_problem_10_8_R1

-- If q * dist(q xi, Z) takes arbitrarily small values over q >= 1, then the p-adic Littlewood infimum is 0.
-- Original Lean proof of the classical remark that the p-adic Littlewood conjecture is only open for badly
-- approximable numbers: the p-adic absolute value of an integer is at most 1, so each term is at most
-- q * dist(q xi, Z); the terms are nonnegative and the set is nonempty.
-- An elementary case, not progress on the conjecture.

namespace OMA.Padic1

theorem well_approximable (ξ : ℝ) (p : ℕ) (hp : p.Prime)
    (h : ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) * distToNearestInt (q * ξ) < ε) :
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hd0 : ∀ x : ℝ, 0 ≤ distToNearestInt x := fun x => abs_nonneg _
  have hn0 : ∀ q : ℕ, (0 : ℝ) ≤ ((padicNorm p (q : ℚ) : ℚ) : ℝ) := fun q => by
    exact_mod_cast padicNorm.nonneg (q : ℚ)
  have hn1 : ∀ q : ℕ, ((padicNorm p (q : ℚ) : ℚ) : ℝ) ≤ 1 := fun q => by
    exact_mod_cast padicNorm.of_nat (p := p) q
  have hS0 : ∀ x ∈ {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)}, 0 ≤ x := by
    rintro x ⟨q, -, rfl⟩
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (hn0 q)) (hd0 _)
  have hne : {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)}.Nonempty := ⟨_, 1, le_refl 1, rfl⟩
  have hbdd : BddBelow {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} := ⟨0, fun x hx => hS0 x hx⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨q, hq1, hq⟩ := h ε hε
    rw [zero_add]
    have hmem : (q : ℝ) * padicNorm p q * distToNearestInt (q * ξ) ∈ {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
        x = q * padicNorm p q * distToNearestInt (q * ξ)} := ⟨q, hq1, rfl⟩
    refine le_trans (csInf_le hbdd hmem) ?_
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have h1 := hn1 q
    have h0 := hn0 q
    have hd := hd0 ((q : ℝ) * ξ)
    have hprod : (0 : ℝ) ≤ (q : ℝ) * distToNearestInt (q * ξ) := mul_nonneg hq0 hd
    have hle : (q : ℝ) * padicNorm p q * distToNearestInt (q * ξ) ≤
        (q : ℝ) * distToNearestInt (q * ξ) := by
      have e : (q : ℝ) * padicNorm p q * distToNearestInt (q * ξ) =
          ((q : ℝ) * distToNearestInt (q * ξ)) * padicNorm p q := by ring
      rw [e]
      exact mul_le_of_le_one_right hprod h1
    linarith
  · exact le_csInf hne (fun x hx => hS0 x hx)

end OMA.Padic1

theorem OMA.solution : OMA.R_Bugeaud08_problem_10_8_R1.H1 := by
  intro ξ p hp h
  exact OMA.Padic1.well_approximable ξ p hp h
