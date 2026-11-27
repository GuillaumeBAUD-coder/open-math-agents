import FormalConjectures.ErdosProblems.«1084»

-- Reduction Erdos1084.erdos_1084.variants.triangular_optimal_d2.R1 of Erdős Problem 1084 — triangular optimal d2
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

open scoped EuclideanGeometry
open Finset

-- Count integer coordinates in the three strips defining the regular hexagon.
def H1 : Prop :=
  ∀ n : ℕ, let interval := Finset.Icc (-(n : ℤ)) (n : ℤ)
    let patch := (interval ×ˢ interval).filter fun p => p.1 + p.2 ∈ interval
    patch.card = 3*n^2 + 3*n + 1

-- Count the nearest-neighbour contacts in the same patch.
def H2 : Prop :=
  ∀ n : ℕ, let interval := Finset.Icc (-(n : ℤ)) (n : ℤ)
    let patch := (interval ×ˢ interval).filter fun p => p.1 + p.2 ∈ interval
    let point (p : ℤ × ℤ) : ℝ² :=
      !₂[(p.1 : ℝ) + (p.2 : ℝ)/2, Real.sqrt 3 * (p.2 : ℝ)/2]
    9*n^2 + 3*n ≤ unitDistNum (patch.image point)

-- Harborth's squared deficit inequality for planar contact graphs.
def H3 : Prop :=
  ∀ S : Finset ℝ², Metric.IsSeparated' 1 (S : Set ℝ²) →
    12*S.card ≤ (3*S.card - unitDistNum S)^2 + 3

-- The lattice norm estimate follows the hexagonal lattice argument in
-- the repository's proof of the hexagonal lower bound for Erdős 232.
lemma int_key (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) : (4 : ℤ) ≤ (2 * x + y) ^ 2 + 3 * y ^ 2 := by
  have hsq : ∀ n : ℤ, n ≠ 0 → (1 : ℤ) ≤ n ^ 2 := by
    intro n hn
    by_cases h1 : (1 : ℤ) ≤ n
    · nlinarith
    · have h2 : n ≤ -1 := by omega
      nlinarith
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    simp only [add_zero]
    rcases h with hx | hx
    · have := hsq x hx
      nlinarith
    · exact absurd rfl hx
  · have hy1 := hsq y hy
    rcases eq_or_ne (2 * x + y) 0 with hm | hm
    · have hx0 : x ≠ 0 := by rintro rfl; omega
      have hx1 := hsq x hx0
      have hyy : y = -2 * x := by omega
      rw [hyy]
      nlinarith
    · have hm1 := hsq (2 * x + y) hm
      nlinarith

lemma real_key (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    (4 : ℝ) ≤ (2 * (x : ℝ) + (y : ℝ)) ^ 2 + 3 * (y : ℝ) ^ 2 := by
  have h' := int_key x y h
  have h'' : ((4 : ℤ) : ℝ) ≤ (((2 * x + y) ^ 2 + 3 * y ^ 2 : ℤ) : ℝ) := by exact_mod_cast h'
  push_cast at h''
  linarith


lemma lattice_sep (p q : ℤ × ℤ) (hne : p ≠ q) :
    let point (r : ℤ × ℤ) : ℝ² :=
      !₂[(r.1 : ℝ) + (r.2 : ℝ)/2, Real.sqrt 3 * (r.2 : ℝ)/2]
    1 ≤ dist (point p) (point q) := by
  intro point
  have hd : p.1-q.1 ≠ 0 ∨ p.2-q.2 ≠ 0 := by
    by_contra! h
    exact hne (Prod.ext (sub_eq_zero.mp h.1) (sub_eq_zero.mp h.2))
  have h := real_key _ _ hd
  push_cast at h
  have hid : 4 * ‖point p - point q‖^2 =
      (2*((p.1 : ℝ)-q.1) + ((p.2 : ℝ)-q.2))^2 + 3*((p.2 : ℝ)-q.2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change 4 * (((p.1 : ℝ) + p.2/2 - (q.1 + q.2/2))^2 +
      (Real.sqrt 3*p.2/2 - Real.sqrt 3*q.2/2)^2) = _
    ring_nf
    norm_num [Real.sq_sqrt] <;> ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (point p - point q)]

theorem main : H1 → H2 → H3 → type_of% @Erdos1084.erdos_1084.variants.triangular_optimal_d2 := by
  classical
  intro count contacts bound n
  let N := 3*n^2 + 3*n + 1
  let target := 9*n^2 + 3*n
  have upper (S : Finset ℝ²) (hs : S.card = N)
      (hsep : Metric.IsSeparated' 1 (S : Set ℝ²)) : unitDistNum S ≤ target := by
    have h := bound S hsep
    rw [hs] at h
    have hdef : 6*n + 3 ≤ 3*N - unitDistNum S := by
      by_contra! hsmall
      have hle : 3*N - unitDistNum S ≤ 6*n+2 := by omega
      have hh := Nat.pow_le_pow_left hle 2
      dsimp [N] at h
      nlinarith
    dsimp [N,target] at *
    omega
  apply le_antisymm
  · exact ciSup_le' fun S => ciSup_le' fun hs => ciSup_le' fun hsep => upper S hs hsep
  let interval := Finset.Icc (-(n : ℤ)) (n : ℤ)
  let patch := (interval ×ˢ interval).filter fun p => p.1 + p.2 ∈ interval
  let point (p : ℤ × ℤ) : ℝ² :=
    !₂[(p.1 : ℝ) + (p.2 : ℝ)/2, Real.sqrt 3 * (p.2 : ℝ)/2]
  let S := patch.image point
  have inj : Function.Injective point := by
    intro p q he
    by_contra h
    have hh := lattice_sep p q h
    change 1 ≤ dist (point p) (point q) at hh
    rw [he, dist_self] at hh
    norm_num at hh
  have hs : S.card = N := (Finset.card_image_of_injective _ inj).trans (count n)
  have hsep : Metric.IsSeparated' 1 (S : Set ℝ²) := by
    intro x hx y hy hne
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    have hd : 1 ≤ dist (point p) (point q) := lattice_sep p q (fun he => hne (congrArg point he))
    simpa only [ENNReal.ofReal_one, ← edist_dist] using ENNReal.ofReal_le_ofReal hd
  change target ≤ ⨆ (T : Finset ℝ²) (_ : T.card = N) (_ : Metric.IsSeparated' 1 (T : Set ℝ²)), unitDistNum T
  refine le_ciSup_of_le ?_ S ?_
  · refine ⟨target, ?_⟩
    rintro _ ⟨T,rfl⟩
    exact ciSup_le' fun h => ciSup_le' fun h' => upper T h h'
  apply le_ciSup_of_le (Set.finite_range _).bddAbove hs
  apply le_ciSup_of_le (Set.finite_range _).bddAbove hsep
  exact contacts n

end OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1
