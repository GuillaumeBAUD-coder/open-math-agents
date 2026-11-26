import FormalConjectures.ErdosProblems.«91»

-- Problem: Erdős Problem 91 — unitSquare optimal
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/91.lean:120 (declaration Erdos91.erdos_91.test.unitSquare_optimal)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# The unit square is an optimal four-point configuration

The unit square has four points and its distances are `1` and `√2`, so it determines at most two
distinct distances. Conversely, four points of the plane never determine a single distance: if all
six distances were equal, the three difference vectors from one of the points would have a
nonsingular Gram matrix, which is impossible for three vectors in dimension two. Hence the minimum
number of distinct distances over four-point sets is two, and the unit square attains it.
-/

open EuclideanGeometry

namespace OMA.UnitSquare

/-- Three vectors `u`, `v`, `w` of the plane have a singular Gram matrix. So they cannot all have
squared norm `D` and pairwise inner products `D / 2` unless `D = 0`. -/
lemma gram_aux (u1 u2 v1 v2 w1 w2 D : ℝ)
    (huu : u1 ^ 2 + u2 ^ 2 = D) (hvv : v1 ^ 2 + v2 ^ 2 = D) (hww : w1 ^ 2 + w2 ^ 2 = D)
    (huv : u1 * v1 + u2 * v2 = D / 2) (huw : u1 * w1 + u2 * w2 = D / 2)
    (hvw : v1 * w1 + v2 * w2 = D / 2) : D = 0 := by
  -- The determinant of the Gram matrix of `u`, `v`, `w` vanishes identically.
  have key : (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) * (w1 ^ 2 + w2 ^ 2)
      + 2 * (u1 * v1 + u2 * v2) * (u1 * w1 + u2 * w2) * (v1 * w1 + v2 * w2)
      - (u1 ^ 2 + u2 ^ 2) * (v1 * w1 + v2 * w2) ^ 2
      - (v1 ^ 2 + v2 ^ 2) * (u1 * w1 + u2 * w2) ^ 2
      - (w1 ^ 2 + w2 ^ 2) * (u1 * v1 + u2 * v2) ^ 2 = 0 := by ring
  -- With the prescribed entries that determinant is `D ^ 3 / 2`.
  rw [huu, hvv, hww, huv, huw, hvw] at key
  have h3 : D ^ 3 = 0 := by linear_combination 2 * key
  exact (pow_eq_zero_iff (by norm_num)).mp h3

/-- The squared distance between two points of the plane, in coordinates. -/
lemma dist_sq (p q : ℝ²) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Four points of the plane determine at least two distinct distances. -/
lemma two_le_distinctDistances (S : Finset ℝ²) (hS : S.card = 4) :
    2 ≤ distinctDistances S := by
  by_contra hlt
  have hcard : (distanceSet S).card ≤ 1 := by
    unfold distinctDistances at hlt
    omega
  -- Name the four points `a`, `b`, `c`, `d`.
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp hS
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp ht
  have hab : a ≠ b := by
    rintro rfl
    exact hat (by simp)
  have hac : a ≠ c := by
    rintro rfl
    exact hat (by simp)
  have had : a ≠ d := by
    rintro rfl
    exact hat (by simp)
  -- With at most one distance, every pair of distinct points is as far apart as `a` and `b`.
  have key : ∀ p q : ℝ², p ∈ insert a ({b, c, d} : Finset ℝ²) →
      q ∈ insert a ({b, c, d} : Finset ℝ²) → p ≠ q → dist p q ^ 2 = dist a b ^ 2 := by
    intro p q hp hq hpq
    congr 1
    apply Finset.card_le_one.mp hcard
    · exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨by simp, by simp, hab⟩, rfl⟩
  have eab := dist_sq a b
  have eac := (key a c (by simp) (by simp) hac).symm.trans (dist_sq a c)
  have ead := (key a d (by simp) (by simp) had).symm.trans (dist_sq a d)
  have ebc := (key b c (by simp) (by simp) hbc).symm.trans (dist_sq b c)
  have ebd := (key b d (by simp) (by simp) hbd).symm.trans (dist_sq b d)
  have ecd := (key c d (by simp) (by simp) hcd).symm.trans (dist_sq c d)
  -- Apply the Gram argument to the vectors `b - a`, `c - a`, `d - a`.
  have hD : dist a b ^ 2 = 0 :=
    gram_aux (b 0 - a 0) (b 1 - a 1) (c 0 - a 0) (c 1 - a 1) (d 0 - a 0) (d 1 - a 1) (dist a b ^ 2)
      (by linear_combination -eab) (by linear_combination -eac) (by linear_combination -ead)
      (by linear_combination (-1 / 2 : ℝ) * eab - (1 / 2 : ℝ) * eac + (1 / 2 : ℝ) * ebc)
      (by linear_combination (-1 / 2 : ℝ) * eab - (1 / 2 : ℝ) * ead + (1 / 2 : ℝ) * ebd)
      (by linear_combination (-1 / 2 : ℝ) * eac - (1 / 2 : ℝ) * ead + (1 / 2 : ℝ) * ecd)
  have hpos : 0 < dist a b := dist_pos.mpr hab
  exact absurd hD (pow_pos hpos 2).ne'

/-- A nonnegative real whose square is `1` or `2` is `1` or `√2`. -/
lemma mem_of_sq (r : ℝ) (hr : 0 ≤ r) (h : r ^ 2 = 1 ∨ r ^ 2 = 2) :
    r ∈ ({1, Real.sqrt 2} : Finset ℝ) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases h with h | h
  · left
    rw [← Real.sqrt_sq hr, h, Real.sqrt_one]
  · right
    rw [← Real.sqrt_sq hr, h]

/-- The unit square has four points. -/
lemma card_unitSquare : Erdos91.unitSquare.card = 4 := by
  simp [Erdos91.unitSquare]

/-- Every distance determined by the unit square is `1` or `√2`. -/
lemma distanceSet_unitSquare_subset :
    distanceSet Erdos91.unitSquare ⊆ ({1, Real.sqrt 2} : Finset ℝ) := by
  intro r hr
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hr
  simp only [Erdos91.unitSquare, Finset.mem_offDiag, Finset.mem_insert,
    Finset.mem_singleton] at hpq
  obtain ⟨hp, hq, hne⟩ := hpq
  apply mem_of_sq _ dist_nonneg
  rw [dist_sq]
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | norm_num

end OMA.UnitSquare

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.unitSquare_optimal := by
  have hc : Erdos91.unitSquare.card = 4 := OMA.UnitSquare.card_unitSquare
  have hle : distinctDistances Erdos91.unitSquare ≤ 2 :=
    (Finset.card_le_card OMA.UnitSquare.distanceSet_unitSquare_subset).trans Finset.card_le_two
  have h2 : distinctDistances Erdos91.unitSquare = 2 :=
    le_antisymm hle (OMA.UnitSquare.two_le_distinctDistances _ hc)
  refine ⟨hc, ?_⟩
  rw [h2]
  unfold minimalDistinctDistances
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, Erdos91.unitSquare, hc, rfl⟩
    · rintro m ⟨S, hS, rfl⟩
      exact OMA.UnitSquare.two_le_distinctDistances S hS
  · exact Nat.sInf_le ⟨Erdos91.unitSquare, hc, h2⟩
