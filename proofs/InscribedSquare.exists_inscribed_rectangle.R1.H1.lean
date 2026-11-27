import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1
import Mathlib

/-!
The chord endpoints have arguments π(s+t) and π(s-t) for (s,t) in the unit
square. Periodicity identifies the vertical edges with reversed parameters.
The integer equations for two unordered pairs show that there are no other
identifications.
-/

open scoped unitInterval
open Real

namespace CircleChords

lemma phase_eq (a b : ℝ) : Circle.exp (π*a) = Circle.exp (π*b) ↔
    ∃ k : ℤ, a = b + 2*(k:ℝ) := by
  rw [Circle.exp_eq_exp]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,mul_left_cancel₀ Real.pi_ne_zero ?_⟩
    linear_combination hk
  · rintro ⟨k,rfl⟩
    exact ⟨k,by ring⟩

end CircleChords

theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_R1.H1 := by
  let u (p : I × I) := Circle.exp (π * ((p.1 : ℝ) + p.2))
  let v (p : I × I) := Circle.exp (π * ((p.1 : ℝ) - p.2))
  refine ⟨u,v,?_,?_,?_,?_,?_⟩
  · exact Circle.exp.continuous.comp (by fun_prop)
  · exact Circle.exp.continuous.comp (by fun_prop)
  · intro t
    constructor
    · apply (CircleChords.phase_eq _ _).2
      exact ⟨0,by simp [unitInterval.coe_symm_eq]⟩
    · apply (CircleChords.phase_eq _ _).2
      refine ⟨-1,?_⟩
      simp [unitInterval.coe_symm_eq]
      <;> ring
  · intro p
    change Circle.exp _ = Circle.exp _ ↔ _
    rw [CircleChords.phase_eq]
    constructor
    · rintro ⟨k,hk⟩
      have lo := p.2.property.1
      have hi := p.2.property.2
      have k0 : 0 ≤ k := by exact_mod_cast (show 0 ≤ (k:ℝ) by linarith)
      have k1 : k ≤ 1 := by exact_mod_cast (show (k:ℝ) ≤ 1 by linarith)
      interval_cases k
      · left; apply Subtype.ext; change (p.2:ℝ) = 0; norm_num at hk; linarith
      · right; apply Subtype.ext; change (p.2:ℝ) = 1; norm_num at hk; linarith
    · rintro (hz|ho)
      · exact ⟨0,by simp [hz]⟩
      · refine ⟨1,?_⟩
        simp [ho]; ring
  · intro p q pairs
    have p₁ := p.1.property
    have p₂ := p.2.property
    have q₁ := q.1.property
    have q₂ := q.2.property
    obtain ⟨p1l,p1u⟩ := p₁
    obtain ⟨p2l,p2u⟩ := p₂
    obtain ⟨q1l,q1u⟩ := q₁
    obtain ⟨q2l,q2u⟩ := q₂
    change p = q ∨ (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
      (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
    simp only [Prod.ext_iff,Subtype.ext_iff,unitInterval.coe_symm_eq]
    change ((p.1:ℝ) = q.1 ∧ (p.2:ℝ) = q.2) ∨
      ((p.1:ℝ) = 0 ∧ (q.1:ℝ) = 1 ∧ (q.2:ℝ) = 1-(p.2:ℝ)) ∨
      ((p.1:ℝ) = 1 ∧ (q.1:ℝ) = 0 ∧ (p.2:ℝ) = 1-(q.2:ℝ))
    rcases pairs with ⟨hp,hq⟩ | ⟨hp,hq⟩
    all_goals
      dsimp only [u,v] at hp hq
      obtain ⟨m,hm⟩ := (CircleChords.phase_eq _ _).1 hp
      obtain ⟨n,hn⟩ := (CircleChords.phase_eq _ _).1 hq
      have hm0 : -2 < m := by exact_mod_cast (show (-2:ℝ) < m by linarith)
      have hm1 : m < 2 := by exact_mod_cast (show (m:ℝ) < 2 by linarith)
      have hn0 : -2 < n := by exact_mod_cast (show (-2:ℝ) < n by linarith)
      have hn1 : n < 2 := by exact_mod_cast (show (n:ℝ) < 2 by linarith)
      interval_cases m <;> interval_cases n <;> norm_num at hm hn <;>
        first
        | left; constructor <;> linarith
        | right; left; refine ⟨?_,?_,?_⟩ <;> linarith
        | right; right; refine ⟨?_,?_,?_⟩ <;> linarith
