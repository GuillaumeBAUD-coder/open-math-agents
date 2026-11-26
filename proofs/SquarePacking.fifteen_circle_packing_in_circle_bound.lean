import FormalConjectures.Wikipedia.SquarePacking

/-!
An explicit fifteen-disk packing, using a central regular pentagon of side two
and ten outer centers in five pairs. Put t = sqrt(5) and a = sqrt(1 + 2/t).
The central pentagon has vertices (1,a), (-1,a), (-(t+1)/2,a*(t-3)/2),
(0,a*(1-t)), and ((t+1)/2,a*(t-3)/2). Each outer pair is obtained by moving
both endpoints of an edge outward by two units along its unit normal.

All coordinates are polynomial in t and a with rational coefficients.
The identities t^2 = 5 and a^2 = 1 + 2*t/5 reduce the distance checks to
polynomial inequalities. The resulting centers have norm at most
sqrt(6 + 2/t + 4*a), so translating the open unit disk gives the target.

Construction: Graham, Lubachevsky, Nurmela, and Ostergard,
Dense packings of congruent circles in a circle (1998), Figure 2.
Credit: @rleshner.
-/

namespace OMA.Packing15

noncomputable def cx (t a : ℝ) : Fin 15 → ℝ :=
  ![1, -1, -(t+1)/2, 0, (t+1)/2,
    1, a*(t-5)/2-1, a*(5-3*t)/2-(t+1)/2,
    a*(3*t-5)/2, a*(5-t)/2+(t+1)/2,
    -1, a*(t-5)/2-(t+1)/2, a*(5-3*t)/2,
    a*(3*t-5)/2+(t+1)/2, a*(5-t)/2+1]

noncomputable def cy (t a : ℝ) : Fin 15 → ℝ :=
  ![a, a, a*(t-3)/2, a*(1-t), a*(t-3)/2,
    a+2, a+(t-1)/2, a*(t-3)/2-(t+1)/2,
    a*(1-t)-(t+1)/2, a*(t-3)/2+(t-1)/2,
    a+2, a*(t-3)/2+(t-1)/2, a*(1-t)-(t+1)/2,
    a*(t-3)/2-(t+1)/2, a+(t-1)/2]

set_option maxHeartbeats 8000000 in
lemma separated (t a : ℝ) (ht : t^2 = 5) (ha : a^2 = 1+2*t/5)
    (ht0 : 0 ≤ t) (ht3 : t ≤ 3) (ha0 : 0 ≤ a) :
    ∀ i j : Fin 15, i ≠ j → 4 ≤ (cx t a i-cx t a j)^2+(cy t a i-cy t a j)^2 := by
  have hat : a*t ≤ 3*a := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ht3)]
  intro i j hij
  fin_cases i <;> fin_cases j <;> try { norm_num at hij }
  all_goals norm_num [cx, cy]
  all_goals ring_nf
  all_goals try simp only [ht, ha]
  all_goals ring_nf
  all_goals try simp only [ht]
  all_goals nlinarith only [ht0, ht3, ha0, hat]

set_option maxHeartbeats 2000000 in
lemma bounded (t a : ℝ) (ht : t^2 = 5) (ha : a^2 = 1+2*t/5)
    (ha0 : 0 ≤ a) (i : Fin 15) :
    (cx t a i)^2+(cy t a i)^2 ≤ 6+2*t/5+4*a := by
  fin_cases i <;> norm_num [cx, cy] <;>
    ring_nf <;> (try simp only [ht, ha]) <;> ring_nf <;> (try simp only [ht]) <;>
    nlinarith only [ha0]

end OMA.Packing15

namespace OMA.Packing15
open SquarePacking
open scoped NNReal

lemma norm_sq (p : EuclideanSpace ℝ (Fin 2)) :
    ‖p‖^2 = p 0 ^ 2 + p 1 ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p

lemma mem_circle (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ≥0) :
    p ∈ SquarePacking.Circle r ↔ ‖p‖ < (r : ℝ) := by
  change p 0 ^ 2 + p 1 ^ 2 < (r : ℝ)^2 ↔ _
  rw [← norm_sq]
  exact sq_lt_sq₀ (norm_nonneg _) r.coe_nonneg

noncomputable def packingOfCenters {n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin 2))
    (r : ℝ≥0)
    (hsep : ∀ i j, i ≠ j → 4 ≤ (c i 0-c j 0)^2+(c i 1-c j 1)^2)
    (hbound : ∀ i, (c i 0)^2+(c i 1)^2 ≤ (r : ℝ)^2) :
    Packing n UnitCircle (SquarePacking.Circle (1+r)) where
  embeddings i := IsometryEquiv.addRight (c i)
  disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro y ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hp' : p 0 ^ 2+p 1 ^ 2 < 1 := by simpa [UnitCircle, SquarePacking.Circle] using hp
    have hq' : q 0 ^ 2+q 1 ^ 2 < 1 := by simpa [UnitCircle, SquarePacking.Circle] using hq
    have e0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hpq
    have e1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hpq
    simp only [IsometryEquiv.addRight_apply, PiLp.add_apply] at e0 e1
    have d0 : c i 0-c j 0 = q 0-p 0 := by linarith
    have d1 : c i 1-c j 1 = q 1-p 1 := by linarith
    have hs := hsep i j hij
    rw [d0, d1] at hs
    nlinarith [sq_nonneg (p 0+q 0), sq_nonneg (p 1+q 1)]
  inside := by
    intro i
    rintro y ⟨p, hp, rfl⟩
    have hp' : ‖p‖ < 1 := by simpa [UnitCircle, mem_circle] using hp
    have hc : ‖c i‖ ≤ (r : ℝ) := by
      have hb := hbound i
      rw [← norm_sq] at hb
      exact (sq_le_sq₀ (norm_nonneg _) r.coe_nonneg).mp hb
    rw [mem_circle]
    change ‖p+c i‖ < (1 : ℝ)+r
    exact lt_of_le_of_lt (norm_add_le _ _) (add_lt_add_of_lt_of_le hp' hc)

end OMA.Packing15

namespace OMA.Packing15
open scoped NNReal

noncomputable def result : SquarePacking.Packing 15 SquarePacking.UnitCircle
    (SquarePacking.Circle (1 + NNReal.sqrt (6 + 2 / NNReal.sqrt 5 +
      4 * NNReal.sqrt (1 + 2 / NNReal.sqrt 5)))) := by
  let t : ℝ := NNReal.sqrt 5
  let a : ℝ := NNReal.sqrt (1 + 2 / NNReal.sqrt 5)
  let r : ℝ≥0 := NNReal.sqrt (6 + 2 / NNReal.sqrt 5 +
    4 * NNReal.sqrt (1 + 2 / NNReal.sqrt 5))
  have ht : t^2 = 5 := by
    dsimp [t]
    exact_mod_cast NNReal.sq_sqrt 5
  have ht0 : 0 ≤ t := NNReal.coe_nonneg _
  have htpos : 0 < t := by nlinarith
  have ht3 : t ≤ 3 := by nlinarith
  have hdiv : 2/t = 2*t/5 := by
    apply (div_eq_iff (ne_of_gt htpos)).2
    nlinarith
  have ha0 : 0 ≤ a := NNReal.coe_nonneg _
  have ha : a^2 = 1+2*t/5 := by
    rw [← hdiv]
    dsimp [a, t]
    exact_mod_cast NNReal.sq_sqrt (1+2/NNReal.sqrt 5)
  have hr : (r : ℝ)^2 = 6+2/t+4*a := by
    dsimp [r, t, a]
    exact_mod_cast NNReal.sq_sqrt (6+2/NNReal.sqrt 5+
      4*NNReal.sqrt (1+2/NNReal.sqrt 5))
  refine packingOfCenters (fun i => !₂[cx t a i, cy t a i]) r ?_ ?_
  · intro i j hij
    change 4 ≤ (cx t a i-cx t a j)^2+(cy t a i-cy t a j)^2
    exact separated t a ht ha ht0 ht3 ha0 i j hij
  · intro i
    change (cx t a i)^2+(cy t a i)^2 ≤ (r : ℝ)^2
    rw [hr, hdiv]
    exact bounded t a ht ha ha0 i

end OMA.Packing15

theorem OMA.solution : type_of% @SquarePacking.fifteen_circle_packing_in_circle_bound :=
  ⟨OMA.Packing15.result⟩
