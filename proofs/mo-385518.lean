import OMAStatements.S_mo_385518
import Mathlib

namespace OMA.S_mo_385518_Proof

open Matrix Finset

private lemma mem_convexHull_range_iff {n m : ℕ} (P : Fin m → OMA.S_mo_385518.Mat n)
    (M : OMA.S_mo_385518.Mat n) :
    M ∈ convexHull ℝ (Set.range P) ↔
      ∃ p : OMA.S_mo_385518.Row m, OMA.S_mo_385518.Distribution p ∧
        M = ∑ a : Fin m, p a • P a := by
  constructor
  · intro hM
    let S : Set (OMA.S_mo_385518.Mat n) :=
      {N | ∃ p : OMA.S_mo_385518.Row m, OMA.S_mo_385518.Distribution p ∧
        N = ∑ a : Fin m, p a • P a}
    have hsub : Set.range P ⊆ S := by
      rintro N ⟨a, rfl⟩
      refine ⟨Pi.single a (1 : ℝ), ⟨?_, ?_⟩, ?_⟩
      · intro b
        by_cases hba : b = a
        · subst hba; simp
        · simp [Pi.single_eq_of_ne hba]
      · simp
      · symm
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hba
          simp [Pi.single_eq_of_ne hba]
        · intro ha
          exact absurd (Finset.mem_univ a) ha
    have hconv : Convex ℝ S := by
      rintro N₁ ⟨p₁, ⟨hp₁0, hp₁1⟩, rfl⟩ N₂ ⟨p₂, ⟨hp₂0, hp₂1⟩, rfl⟩ c₁ c₂ hc₁ hc₂ hc12
      refine ⟨fun a => c₁ * p₁ a + c₂ * p₂ a, ⟨?_, ?_⟩, ?_⟩
      · intro a
        exact add_nonneg (mul_nonneg hc₁ (hp₁0 a)) (mul_nonneg hc₂ (hp₂0 a))
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp₁1, hp₂1]
        linarith
      · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    exact convexHull_min hsub hconv hM
  · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
    have hcm : (Finset.univ : Finset (Fin m)).centerMass p P = ∑ a : Fin m, p a • P a := by
      rw [Finset.centerMass, hp1, inv_one, one_smul]
    rw [← hcm]
    exact Finset.centerMass_mem_convexHull Finset.univ (fun a _ => hp0 a)
      (by rw [hp1]; norm_num) (fun a _ => Set.mem_range_self a)

private def piFinSuccEquiv (m z : ℕ) : (Fin m × (Fin z → Fin m)) ≃ (Fin (z + 1) → Fin m) where
  toFun := fun x => Fin.cons x.1 x.2
  invFun := fun w => (w 0, fun t => w t.succ)
  left_inv := fun ⟨a, w'⟩ => by
    ext
    · simp
    · simp
  right_inv := fun w => by
    ext t
    refine Fin.cases ?_ ?_ t <;> simp

private lemma prod_ofFn_sum {n m : ℕ} :
    ∀ (z : ℕ) (p : Fin z → OMA.S_mo_385518.Row m) (P : Fin m → OMA.S_mo_385518.Mat n),
      (List.ofFn (fun t : Fin z => ∑ a : Fin m, p t a • P a)).prod =
        ∑ w : Fin z → Fin m, (∏ t : Fin z, p t (w t)) • (List.ofFn (P ∘ w)).prod
  | 0, p, P => by
    have huniq : ∀ w : Fin 0 → Fin m, w = Fin.elim0 := fun w => funext fun i => i.elim0
    rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → Fin m)]
    · simp
    · intro w _ hw
      exact absurd (huniq w) hw
    · intro h
      exact absurd (Finset.mem_univ _) h
  | z + 1, p, P => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_sum z (fun t => p t.succ) P]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (piFinSuccEquiv m z) _ _ ?_
    rintro ⟨a, w'⟩
    simp only [piFinSuccEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [List.ofFn_succ, List.prod_cons]
    simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
    rw [smul_mul_smul_comm]
    rfl

private lemma vecMul_sum {n ι : Type*} [Fintype n] (s : Finset ι)
    (x : n → ℝ) (f : ι → Matrix n n ℝ) :
    x ᵥ* (∑ i ∈ s, f i) = ∑ i ∈ s, (x ᵥ* f i) := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

private lemma vecMul_smul_mat {n : Type*} [Fintype n]
    (x : n → ℝ) (c : ℝ) (M : Matrix n n ℝ) :
    x ᵥ* (c • M) = c • (x ᵥ* M) := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma part1_char {n m z : ℕ} (x : OMA.S_mo_385518.Row n)
    (P : Fin m → OMA.S_mo_385518.Mat n) (y : OMA.S_mo_385518.Row n) :
    y ∈ OMA.S_mo_385518.reachable z x P ↔
      ∃ p : Fin z → OMA.S_mo_385518.Row m, (∀ t, OMA.S_mo_385518.Distribution (p t)) ∧
        y = ∑ w : Fin z → Fin m, (∏ t, p t (w t)) • OMA.S_mo_385518.wordEnd x P w := by
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    have hex : ∀ t : Fin z, ∃ p : OMA.S_mo_385518.Row m,
        OMA.S_mo_385518.Distribution p ∧ Q t = ∑ a : Fin m, p a • P a :=
      fun t => (mem_convexHull_range_iff P (Q t)).mp (hQ t)
    choose p hpD hpQ using hex
    refine ⟨p, hpD, ?_⟩
    have hQfun : Q = fun t => ∑ a : Fin m, p t a • P a := funext hpQ
    unfold OMA.S_mo_385518.endpoint OMA.S_mo_385518.wordEnd
    rw [hQfun, prod_ofFn_sum, vecMul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [vecMul_smul_mat]
    rfl
  · rintro ⟨p, hpD, rfl⟩
    refine ⟨fun t => ∑ a : Fin m, p t a • P a, ?_, ?_⟩
    · intro t
      exact (mem_convexHull_range_iff P _).mpr ⟨p t, hpD t, rfl⟩
    · unfold OMA.S_mo_385518.endpoint OMA.S_mo_385518.wordEnd
      rw [prod_ofFn_sum, vecMul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [vecMul_smul_mat]
      rfl

private lemma part1_hull {n m z : ℕ} (x : OMA.S_mo_385518.Row n)
    (P : Fin m → OMA.S_mo_385518.Mat n) :
    convexHull ℝ (OMA.S_mo_385518.reachable z x P) =
      convexHull ℝ (Set.range (OMA.S_mo_385518.wordEnd (z := z) x P)) := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro y hy
    rcases (part1_char x P y).mp hy with ⟨p, hpD, rfl⟩
    let μ : (Fin z → Fin m) → ℝ := fun w => ∏ t : Fin z, p t (w t)
    have hμ0 : ∀ w ∈ (Finset.univ : Finset (Fin z → Fin m)), 0 ≤ μ w :=
      fun w _ => Finset.prod_nonneg fun t _ => (hpD t).1 (w t)
    have hμ1 : ∑ w : Fin z → Fin m, μ w = 1 := by
      dsimp only [μ]
      rw [← Fintype.prod_sum]
      exact Finset.prod_eq_one fun t _ => (hpD t).2
    have hcm : (Finset.univ : Finset (Fin z → Fin m)).centerMass μ
        (OMA.S_mo_385518.wordEnd x P) =
        ∑ w : Fin z → Fin m, μ w • OMA.S_mo_385518.wordEnd x P w := by
      rw [Finset.centerMass, hμ1, inv_one, one_smul]
    rw [← hcm]
    exact Finset.centerMass_mem_convexHull Finset.univ hμ0
      (by rw [hμ1]; norm_num) (fun w _ => Set.mem_range_self w)
  · refine convexHull_mono ?_
    rintro y ⟨w, rfl⟩
    refine ⟨P ∘ w, ?_, rfl⟩
    intro t
    exact subset_convexHull ℝ (Set.range P) (Set.mem_range_self (w t))

private lemma part2 :
    ∃ (x : OMA.S_mo_385518.Row 3) (P : Fin 2 → OMA.S_mo_385518.Mat 3),
      OMA.S_mo_385518.Distribution x ∧ (∀ a, OMA.S_mo_385518.Stochastic (P a)) ∧
      ¬ Convex ℝ (OMA.S_mo_385518.reachable 2 x P) := by
  let x : OMA.S_mo_385518.Row 3 := ![1, 0, 0]
  let P0 : OMA.S_mo_385518.Mat 3 := !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  let P1 : OMA.S_mo_385518.Mat 3 := !![0, 1, 0; 0, 0, 1; 0, 0, 1]
  let P : Fin 2 → OMA.S_mo_385518.Mat 3 := ![P0, P1]
  have hx : OMA.S_mo_385518.Distribution x := by
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [x]
    · simp [x, Fin.sum_univ_three]
  have hP : ∀ a, OMA.S_mo_385518.Stochastic (P a) := by
    intro a i
    fin_cases a <;> fin_cases i
    all_goals
      refine ⟨?_, ?_⟩
      · intro j; fin_cases j <;> norm_num [P, P0, P1]
      · simp [P, P0, P1, Fin.sum_univ_three]
  refine ⟨x, P, hx, hP, ?_⟩
  intro hconv
  have hword : ∀ a b : Fin 2,
      OMA.S_mo_385518.wordEnd x P ![a, b] =
        if a = 0 ∧ b = 0 then ![1, 0, 0]
        else if a = 1 ∧ b = 1 then ![0, 0, 1]
        else ![0, 1, 0] := by
    intro a b
    fin_cases a <;> fin_cases b
    all_goals
      ext j
      fin_cases j
      all_goals
        simp [OMA.S_mo_385518.wordEnd, OMA.S_mo_385518.endpoint, List.ofFn_succ,
          Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_three, x, P, P0, P1]
  let w00 : Fin 2 → Fin 2 := ![0, 0]
  let w11 : Fin 2 → Fin 2 := ![1, 1]
  have hy0 : OMA.S_mo_385518.wordEnd x P w00 ∈ OMA.S_mo_385518.reachable 2 x P := by
    refine ⟨P ∘ w00, fun t => subset_convexHull ℝ (Set.range P) (Set.mem_range_self _), rfl⟩
  have hy1 : OMA.S_mo_385518.wordEnd x P w11 ∈ OMA.S_mo_385518.reachable 2 x P := by
    refine ⟨P ∘ w11, fun t => subset_convexHull ℝ (Set.range P) (Set.mem_range_self _), rfl⟩
  have hmid : (1 / 2 : ℝ) • OMA.S_mo_385518.wordEnd x P w00 +
      (1 / 2 : ℝ) • OMA.S_mo_385518.wordEnd x P w11 ∈ OMA.S_mo_385518.reachable 2 x P :=
    hconv hy0 hy1 (by norm_num) (by norm_num) (by norm_num)
  rcases (part1_char x P _).mp hmid with ⟨p, hpD, heq⟩
  let e : (Fin 2 × Fin 2) ≃ (Fin 2 → Fin 2) :=
    { toFun := fun ab => ![ab.1, ab.2]
      invFun := fun w => (w 0, w 1)
      left_inv := fun ⟨a, b⟩ => by simp
      right_inv := fun w => by ext i; fin_cases i <;> simp }
  have hsum :
      ∑ w : Fin 2 → Fin 2, (∏ t : Fin 2, p t (w t)) • OMA.S_mo_385518.wordEnd x P w =
        (p 0 0 * p 1 0) • (![1, 0, 0] : OMA.S_mo_385518.Row 3) +
        (p 0 0 * p 1 1 + p 0 1 * p 1 0) • (![0, 1, 0] : OMA.S_mo_385518.Row 3) +
        (p 0 1 * p 1 1) • (![0, 0, 1] : OMA.S_mo_385518.Row 3) := by
    rw [← Equiv.sum_comp e]
    rw [Fintype.sum_prod_type]
    simp only [e, Equiv.coe_fn_mk, Fin.sum_univ_two, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, hword]
    ext j
    fin_cases j <;> simp <;> ring
  rw [hsum] at heq
  have h00 : OMA.S_mo_385518.wordEnd x P w00 = ![1, 0, 0] := by simpa [w00] using hword 0 0
  have h11 : OMA.S_mo_385518.wordEnd x P w11 = ![0, 0, 1] := by simpa [w11] using hword 1 1
  rw [h00, h11] at heq
  have hc0 : (1 / 2 : ℝ) = p 0 0 * p 1 0 := by
    have := congrFun heq 0
    simp at this
    linarith
  have hc1 : (0 : ℝ) = p 0 0 * p 1 1 + p 0 1 * p 1 0 := by
    have := congrFun heq 1
    simp at this
    linarith
  have hc2 : (1 / 2 : ℝ) = p 0 1 * p 1 1 := by
    have := congrFun heq 2
    simp at this
    linarith
  have ha0 : 0 ≤ p 0 0 := (hpD 0).1 0
  have ha1 : 0 ≤ p 0 1 := (hpD 0).1 1
  have hb0 : 0 ≤ p 1 0 := (hpD 1).1 0
  have hb1 : 0 ≤ p 1 1 := (hpD 1).1 1
  have hprod0 : p 0 0 * p 1 1 = 0 := by nlinarith
  have hprod1 : p 0 1 * p 1 0 = 0 := by nlinarith
  have hcontr : (p 0 0 * p 1 0) * (p 0 1 * p 1 1) = (p 0 0 * p 1 1) * (p 0 1 * p 1 0) := by ring
  nlinarith

end OMA.S_mo_385518_Proof

theorem OMA.solution : type_of% @OMA.S_mo_385518.main := by
  refine ⟨?_, OMA.S_mo_385518_Proof.part2⟩
  intro n m z _ x P _ _
  exact ⟨OMA.S_mo_385518_Proof.part1_char x P, OMA.S_mo_385518_Proof.part1_hull x P⟩
