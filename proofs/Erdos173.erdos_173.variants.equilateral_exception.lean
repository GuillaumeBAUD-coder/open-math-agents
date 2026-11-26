import FormalConjectures.ErdosProblems.«173»

-- Problem: Erdős Problem 173 — equilateral exception
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Colour the plane in horizontal half-open strips of height √3/2, alternately. A unit
-- equilateral triangle has no monochromatic copy.

open Affine
open scoped Congruent EuclideanGeometry

namespace OMA

/-- The strip height. -/
noncomputable def hh : ℝ := Real.sqrt 3 / 2

theorem hh_pos : 0 < hh := by unfold hh; positivity

theorem hh_sq : hh ^ 2 = 3 / 4 := by
  unfold hh
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem same_floor (a b : ℝ) (h : ⌊a / hh⌋ = ⌊b / hh⌋) : (a - b) ^ 2 < 3 / 4 := by
  have ha1 := Int.floor_le (a / hh)
  have ha2 := Int.lt_floor_add_one (a / hh)
  have hb1 := Int.floor_le (b / hh)
  have hb2 := Int.lt_floor_add_one (b / hh)
  rw [h] at ha1 ha2
  have hab : a - b = hh * (a / hh - b / hh) := by
    field_simp [hh_pos.ne']
  rw [hab, mul_pow, hh_sq]
  have h1 : a / hh - b / hh < 1 := by linarith
  have h2 : -1 < a / hh - b / hh := by linarith
  nlinarith

theorem diff_floor (a b : ℝ) (hpar : Even ⌊a / hh⌋ ↔ Even ⌊b / hh⌋)
    (hne : ⌊a / hh⌋ ≠ ⌊b / hh⌋) : 3 / 4 < (a - b) ^ 2 := by
  have ha1 := Int.floor_le (a / hh)
  have ha2 := Int.lt_floor_add_one (a / hh)
  have hb1 := Int.floor_le (b / hh)
  have hb2 := Int.lt_floor_add_one (b / hh)
  have hab : a - b = hh * (a / hh - b / hh) := by
    field_simp [hh_pos.ne']
  rw [hab, mul_pow, hh_sq]
  rw [Int.even_iff, Int.even_iff] at hpar
  have hcases : ⌊a / hh⌋ + 2 ≤ ⌊b / hh⌋ ∨ ⌊b / hh⌋ + 2 ≤ ⌊a / hh⌋ := by omega
  rcases hcases with hc | hc
  · have hcR : ((⌊a / hh⌋ : ℤ) : ℝ) + 2 ≤ ((⌊b / hh⌋ : ℤ) : ℝ) := by exact_mod_cast hc
    have h1 : a / hh - b / hh < -1 := by linarith
    nlinarith
  · have hcR : ((⌊b / hh⌋ : ℤ) : ℝ) + 2 ≤ ((⌊a / hh⌋ : ℤ) : ℝ) := by exact_mod_cast hc
    have h1 : 1 < a / hh - b / hh := by linarith
    nlinarith

/-- `b` lies between `a` and `c`. -/
theorem mid (a b c : ℝ) (hab : Even ⌊a / hh⌋ ↔ Even ⌊b / hh⌋)
    (hbc : Even ⌊b / hh⌋ ↔ Even ⌊c / hh⌋)
    (hS : (a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2 = 3 / 2)
    (hmid : 0 ≤ (a - b) * (b - c)) : False := by
  have hac3 : (a - c) ^ 2 = (a - b) ^ 2 + (b - c) ^ 2 + 2 * ((a - b) * (b - c)) := by ring
  have h1 := sq_nonneg (a - b)
  have h2 := sq_nonneg (b - c)
  by_cases hfac : ⌊a / hh⌋ = ⌊c / hh⌋
  · have := same_floor a c hfac
    nlinarith
  · by_cases hfab : ⌊a / hh⌋ = ⌊b / hh⌋
    · have hfbc : ⌊b / hh⌋ ≠ ⌊c / hh⌋ := fun h => hfac (hfab.trans h)
      have := diff_floor b c hbc hfbc
      nlinarith
    · have := diff_floor a b hab hfab
      nlinarith

theorem no_three (a b c : ℝ) (hab : Even ⌊a / hh⌋ ↔ Even ⌊b / hh⌋)
    (hbc : Even ⌊b / hh⌋ ↔ Even ⌊c / hh⌋)
    (hS : (a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2 = 3 / 2) : False := by
  have hac : Even ⌊a / hh⌋ ↔ Even ⌊c / hh⌋ := hab.trans hbc
  rcases le_total a b with h1 | h1 <;> rcases le_total b c with h2 | h2 <;>
    rcases le_total a c with h3 | h3
  all_goals first
    | exact mid a b c hab hbc hS (by nlinarith)
    | exact mid b a c hab.symm hac (by nlinarith) (by nlinarith)
    | exact mid a c b hac hbc.symm (by nlinarith) (by nlinarith)

theorem sq_of_dist (p q : ℝ²) (h : dist p q = 1) : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 1 := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_eq_one, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs] at h
  exact h

theorem dist_of_sq (p q : ℝ²) (h : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 1) : dist p q = 1 := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_eq_one, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs]
  exact h

/-- Three points at pairwise distance one: the vertical differences have squares summing to 3/2. -/
theorem vertical (p q r : ℝ²) (h1 : dist p q = 1) (h2 : dist q r = 1) (h3 : dist p r = 1) :
    (p 1 - q 1) ^ 2 + (q 1 - r 1) ^ 2 + (p 1 - r 1) ^ 2 = 3 / 2 := by
  have e1 := sq_of_dist p q h1
  have e2 := sq_of_dist q r h2
  have e3 := sq_of_dist p r h3
  set ax := p 0 - q 0 with hax
  set bx := q 0 - r 0 with hbx
  set a := p 1 - q 1 with ha
  set b := q 1 - r 1 with hb
  have hx : p 0 - r 0 = ax + bx := by rw [hax, hbx]; ring
  have hy : p 1 - r 1 = a + b := by rw [ha, hb]; ring
  rw [hx, hy] at e3
  rw [hy]
  have h4 : ax * bx = -1 / 2 - a * b := by nlinarith
  have h5 : (ax * bx) ^ 2 = (1 - a ^ 2) * (1 - b ^ 2) := by
    rw [mul_pow]
    have : ax ^ 2 = 1 - a ^ 2 := by linarith
    have : bx ^ 2 = 1 - b ^ 2 := by linarith
    nlinarith
  rw [h4] at h5
  linear_combination 2 * h5

/-- The colouring. -/
noncomputable def col (p : ℝ²) : Fin 2 := if Even ⌊p 1 / hh⌋ then 0 else 1

theorem col_eq (p q : ℝ²) (h : col p = col q) : Even ⌊p 1 / hh⌋ ↔ Even ⌊q 1 / hh⌋ := by
  unfold col at h
  split_ifs at h with h1 h2 h2
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩

/-- The vertices of the triangle. -/
noncomputable def pts : Fin 3 → ℝ² := ![!₂[0, 0], !₂[1, 0], !₂[1 / 2, hh]]

theorem d01 : dist (pts 0) (pts 1) = 1 := by
  apply dist_of_sq
  simp [pts]

theorem d12 : dist (pts 1) (pts 2) = 1 := by
  apply dist_of_sq
  simp [pts]
  have := hh_sq
  nlinarith

theorem d02 : dist (pts 0) (pts 2) = 1 := by
  apply dist_of_sq
  simp [pts]
  have := hh_sq
  nlinarith

theorem indep : AffineIndependent ℝ pts := by
  unfold pts
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  rw [collinear_iff_of_mem (p₀ := (!₂[0, 0] : ℝ²)) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨r1, hr1⟩ := hv (!₂[1, 0]) (by simp)
  obtain ⟨r2, hr2⟩ := hv (!₂[1 / 2, hh]) (by simp)
  have a0 := congrFun (congrArg (fun p : ℝ² => (p : Fin 2 → ℝ)) hr1) 0
  have a1 := congrFun (congrArg (fun p : ℝ² => (p : Fin 2 → ℝ)) hr1) 1
  have b1 := congrFun (congrArg (fun p : ℝ² => (p : Fin 2 → ℝ)) hr2) 1
  simp at a0 a1 b1
  have hr1ne : r1 ≠ 0 := by
    intro h0
    rw [h0] at a0
    simp at a0
  have hv1 : v 1 = 0 := by
    rcases a1 with h | h
    · exact absurd h hr1ne
    · exact h
  rw [hv1] at b1
  have := hh_pos
  simp at b1
  linarith

end OMA

theorem OMA.solution : type_of% @Erdos173.erdos_173.variants.equilateral_exception := by
  refine ⟨OMA.col, ⟨OMA.pts, OMA.indep⟩, ?_, ?_, ?_⟩
  · show dist (OMA.pts 0) (OMA.pts 1) = dist (OMA.pts 1) (OMA.pts 2)
    rw [OMA.d01, OMA.d12]
  · show dist (OMA.pts 1) (OMA.pts 2) = dist (OMA.pts 2) (OMA.pts 0)
    rw [OMA.d12, dist_comm, OMA.d02]
  · rintro ⟨T', hcong, i, hi⟩
    have hd : ∀ a b, dist (T'.points a) (T'.points b) = dist (OMA.pts a) (OMA.pts b) :=
      fun a b => hcong.dist_eq a b
    have h01 : dist (T'.points 0) (T'.points 1) = 1 := (hd 0 1).trans OMA.d01
    have h12 : dist (T'.points 1) (T'.points 2) = 1 := (hd 1 2).trans OMA.d12
    have h02 : dist (T'.points 0) (T'.points 2) = 1 := (hd 0 2).trans OMA.d02
    have hS := OMA.vertical _ _ _ h01 h12 h02
    exact OMA.no_three _ _ _
      (OMA.col_eq _ _ ((hi 0).trans (hi 1).symm))
      (OMA.col_eq _ _ ((hi 1).trans (hi 2).symm)) hS
