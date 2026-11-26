import FormalConjectures.Wikipedia.SquarePacking

-- Problem: Packing — twenty one circle packing in square bound
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SquarePacking.lean:188 (declaration SquarePacking.twenty_one_circle_packing_in_square_bound)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAPack21Aux

open SquarePacking

def cx : Fin 21 → ℤ := ![100009, 300028, 662222, 481125, 835881, 117015, 317034, 663100, 489857,
  835881, 100009, 316241, 662638, 835881, 467945, 207563, 662638, 828522, 100009, 315116, 515135]
def cy : Fin 21 → ℤ := ![100009, 100009, 100009, 184930, 199258, 299304, 299304, 300026, 399999,
  400795, 498599, 499321, 500768, 600814, 637195, 667240, 700787, 828522, 835881, 835881, 835881]

lemma hsep : ∀ i j : Fin 21, i ≠ j →
    40000000000 ≤ (cx i - cx j) ^ 2 + (cy i - cy j) ^ 2 := by
  decide

lemma hbd : ∀ i : Fin 21,
    100000 ≤ cx i ∧ cx i ≤ 835900 ∧ 100000 ≤ cy i ∧ cy i ≤ 835900 := by
  decide

noncomputable def c (i : Fin 21) : EuclideanSpace ℝ (Fin 2) := !₂[(cx i : ℝ) / 100000, (cy i : ℝ) / 100000]

lemma c0 (i : Fin 21) : c i 0 = (cx i : ℝ) / 100000 := by simp [c]
lemma c1 (i : Fin 21) : c i 1 = (cy i : ℝ) / 100000 := by simp [c]

lemma mem_unit {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ UnitCircle) : p 0 ^ 2 + p 1 ^ 2 < 1 := by
  simpa [UnitCircle, SquarePacking.Circle] using hp

noncomputable def P : Packing 21 UnitCircle (Square 9.359) where
  embeddings i := IsometryEquiv.addRight (c i)
  disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro y ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hp' := mem_unit hp
    have hq' := mem_unit hq
    have e0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hpq
    have e1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hpq
    simp only [IsometryEquiv.addRight_apply, PiLp.add_apply, c0, c1] at e0 e1
    have h := hsep i j hij
    have hr : (40000000000 : ℝ) ≤ ((cx i : ℝ) - cx j) ^ 2 + ((cy i : ℝ) - cy j) ^ 2 := by
      exact_mod_cast h
    have d0 : (cx i : ℝ) - cx j = 100000 * (q 0 - p 0) := by linarith
    have d1 : (cy i : ℝ) - cy j = 100000 * (q 1 - p 1) := by linarith
    rw [d0, d1] at hr
    have k : (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 < 4 := by
      nlinarith [sq_nonneg (p 0 + q 0), sq_nonneg (p 1 + q 1)]
    nlinarith
  inside := by
    intro i
    rintro y ⟨p, hp, rfl⟩
    have hp' := mem_unit hp
    obtain ⟨h1, h2, h3, h4⟩ := hbd i
    have r1 : (100000 : ℝ) ≤ cx i := by exact_mod_cast h1
    have r2 : (cx i : ℝ) ≤ 835900 := by exact_mod_cast h2
    have r3 : (100000 : ℝ) ≤ cy i := by exact_mod_cast h3
    have r4 : (cy i : ℝ) ≤ 835900 := by exact_mod_cast h4
    have a0 : p 0 ^ 2 < 1 := by nlinarith [sq_nonneg (p 1)]
    have a1 : p 1 ^ 2 < 1 := by nlinarith [sq_nonneg (p 0)]
    have b0 : -1 < p 0 ∧ p 0 < 1 := ⟨by nlinarith, by nlinarith⟩
    have b1 : -1 < p 1 ∧ p 1 < 1 := ⟨by nlinarith, by nlinarith⟩
    simp only [Square, Set.mem_ofPred_eq, IsometryEquiv.addRight_apply, PiLp.add_apply, c0, c1]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith [b0.1, b0.2, b1.1, b1.2]

end OMAPack21Aux

theorem OMA.solution : type_of% @SquarePacking.twenty_one_circle_packing_in_square_bound :=
  ⟨OMAPack21Aux.P⟩
