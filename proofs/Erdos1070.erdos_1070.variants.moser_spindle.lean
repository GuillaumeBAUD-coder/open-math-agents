import FormalConjectures.ErdosProblems.«1070»

-- Problem: Erdős Problem 1070 — moser spindle
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1070.lean:100 (declaration Erdos1070.erdos_1070.variants.moser_spindle)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.O2

open SimpleGraph Finset

/-- The Moser spindle: vertices 0 = O, 1 = P, 2, 3 = middle points of the first rhombus,
4 = P', 5, 6 = middle points of the rotated rhombus (rotation with cos = 5/6). -/
noncomputable def sx : Fin 7 → ℝ :=
  ![0, √3, √3 / 2, √3 / 2, 5 * √3 / 6, (5 * √3 - √11) / 12, (5 * √3 + √11) / 12]

noncomputable def sy : Fin 7 → ℝ :=
  ![0, 0, 1 / 2, -1 / 2, √3 * √11 / 6, (√3 * √11 + 5) / 12, (√3 * √11 - 5) / 12]

def edges : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (2, 3), (1, 2), (1, 3), (0, 5), (0, 6), (5, 6), (4, 5), (4, 6), (1, 4)]

def E (a b : Fin 7) : Bool :=
  edges.contains (a.val, b.val) || edges.contains (b.val, a.val)

theorem indep_le : ∀ S : Finset (Fin 7), (∀ a ∈ S, ∀ b ∈ S, E a b = false) → S.card ≤ 2 := by
  decide +kernel

theorem E_irrefl : ∀ a : Fin 7, E a a = false := by decide

noncomputable def pt (i : ℕ) (j : Fin 7) : EuclideanSpace ℝ (Fin 2) :=
  !₂[sx j + 10 * (i : ℝ), sy j]

theorem pt0 (i : ℕ) (j : Fin 7) : pt i j 0 = sx j + 10 * (i : ℝ) := by simp [pt]

theorem pt1 (i : ℕ) (j : Fin 7) : pt i j 1 = sy j := by simp [pt]

theorem dist_pt (i : ℕ) (a b : Fin 7) :
    dist (pt i a) (pt i b) = √((sx a - sx b) ^ 2 + (sy a - sy b) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, pt0, pt0, pt1, pt1, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs]
  congr 1
  ring

theorem edge_sq (a b : Fin 7) (h : E a b = true) :
    (sx a - sx b) ^ 2 + (sy a - sy b) ^ 2 = 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h33 : √3 ^ 2 * √11 ^ 2 = 33 := by rw [h3, h11]; norm_num
  fin_cases a <;> fin_cases b <;>
    first
    | (exfalso; revert h; decide)
    | (norm_num [sx, sy]; done)
    | (simp [sx, sy] <;> ring_nf <;> nlinarith [h3, h11, h33])

theorem sx_bounds (j : Fin 7) : 0 ≤ sx j ∧ sx j ≤ 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have p3 := Real.sqrt_nonneg 3
  have p11 := Real.sqrt_nonneg 11
  have a1 : √3 < 1.74 := by nlinarith
  have a2 : 1.73 < √3 := by nlinarith
  have b1 : √11 < 3.32 := by nlinarith
  have b2 : 3.31 < √11 := by nlinarith
  fin_cases j <;> constructor <;> simp [sx] <;> linarith

theorem sxy_inj (a b : Fin 7) (hx : sx a = sx b) (hy : sy a = sy b) : a = b := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have p3 := Real.sqrt_nonneg 3
  have p11 := Real.sqrt_nonneg 11
  have a1 : √3 < 1.74 := by nlinarith
  have a2 : 1.73 < √3 := by nlinarith
  have b1 : √11 < 3.32 := by nlinarith
  have b2 : 3.31 < √11 := by nlinarith
  fin_cases a <;> fin_cases b <;> simp [sx, sy] at hx hy ⊢ <;> linarith

theorem pt_inj {i i' : ℕ} {a b : Fin 7} (h : pt i a = pt i' b) : i = i' ∧ a = b := by
  have h0 : sx a + 10 * (i : ℝ) = sx b + 10 * (i' : ℝ) := by
    rw [← pt0, ← pt0, h]
  have h1 : sy a = sy b := by
    rw [← pt1 i a, ← pt1 i' b, h]
  have ba := sx_bounds a
  have bb := sx_bounds b
  have hii : i = i' := by
    rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
    · have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hlt
      linarith
    · exact heq
    · have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hgt
      linarith
  subst hii
  refine ⟨rfl, sxy_inj a b (by linarith) h1⟩

theorem main (m : ℕ) : Erdos1070.f (7 * m) ≤ 2 * m := by
  classical
  let φ : Fin m × Fin 7 → EuclideanSpace ℝ (Fin 2) := fun ij => pt ij.1 ij.2
  have hφ : Function.Injective φ := by
    rintro ⟨i, a⟩ ⟨i', b⟩ h
    obtain ⟨h1, h2⟩ := pt_inj h
    simp only [Prod.mk.injEq]
    exact ⟨Fin.ext h1, h2⟩
  set X : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.univ.image φ with hX
  have hcard : X.card = 7 * m := by
    rw [hX, Finset.card_image_of_injective _ hφ, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, mul_comm]
  have hf := Erdos1070.f_le X
  rw [hcard] at hf
  refine hf.trans ?_
  obtain ⟨s, hs⟩ :=
    (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  let sv : Finset (EuclideanSpace ℝ (Fin 2)) := s.image Subtype.val
  let T : Finset (Fin m × Fin 7) := Finset.univ.filter (fun ij => φ ij ∈ sv)
  have h1 : s.card ≤ T.card := by
    have hsub : sv ⊆ T.image φ := by
      intro x hx
      have hxX : x ∈ X := by
        obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hx
        rw [← hv]
        exact Finset.mem_coe.mp v.property
      obtain ⟨ij, -, rfl⟩ := Finset.mem_image.mp hxX
      exact Finset.mem_image.mpr ⟨ij, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    calc s.card = sv.card := (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (T.image φ).card := Finset.card_le_card hsub
      _ ≤ T.card := Finset.card_image_le
  have hfib : ∀ i : Fin m, (T.filter (fun ij => ij.1 = i)).card ≤ 2 := by
    intro i
    let S : Finset (Fin 7) := Finset.univ.filter (fun j => (i, j) ∈ T)
    have hS : (T.filter (fun ij => ij.1 = i)).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro ij hij
        have hij' := Finset.mem_filter.mp (Finset.mem_coe.mp hij)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        have : ij = (i, ij.2) := Prod.ext hij'.2 rfl
        rw [← this]
        exact hij'.1
      · intro x hx y hy hxy
        have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
        exact Prod.ext (hx'.trans hy'.symm) hxy
    refine hS.trans (indep_le S ?_)
    intro a ha b hb
    by_contra hE
    have hE' : E a b = true := by simpa using hE
    have hab : a ≠ b := by
      rintro rfl
      rw [E_irrefl] at hE'
      exact Bool.false_ne_true hE'
    have ha' : φ (i, a) ∈ sv := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).2).2
    have hb' : φ (i, b) ∈ sv := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).2).2
    obtain ⟨va, hva, hva'⟩ := Finset.mem_image.mp ha'
    obtain ⟨vb, hvb, hvb'⟩ := Finset.mem_image.mp hb'
    have hne : va ≠ vb := by
      intro h
      apply hab
      have : φ (i, a) = φ (i, b) := by rw [← hva', ← hvb', h]
      have := hφ this
      simp only [Prod.mk.injEq] at this
      exact this.2
    apply hs.isIndepSet (Finset.mem_coe.mpr hva) (Finset.mem_coe.mpr hvb) hne
    show dist (va : EuclideanSpace ℝ (Fin 2)) (vb : EuclideanSpace ℝ (Fin 2)) = 1
    rw [hva', hvb']
    show dist (pt (i : ℕ) a) (pt (i : ℕ) b) = 1
    rw [dist_pt, edge_sq a b hE', Real.sqrt_one]
  calc s.card ≤ T.card := h1
    _ = ∑ i : Fin m, (T.filter (fun ij => ij.1 = i)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ x.1))
    _ ≤ ∑ _i : Fin m, 2 := Finset.sum_le_sum (fun i _ => hfib i)
    _ = 2 * m := by simp [mul_comm]

end OMA.O2

theorem OMA.solution : type_of% @Erdos1070.erdos_1070.variants.moser_spindle := by
  intro m
  exact OMA.O2.main m
