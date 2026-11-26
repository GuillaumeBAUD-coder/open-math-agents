import FormalConjectures.WrittenOnTheWallII.Test
import Mathlib.Tactic

-- Problem: Testing Graph Invariants — petersen cvetkovic
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/Test.lean:392 (declaration WrittenOnTheWallII.Test.petersen_cvetkovic)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.PetersenCvetkovic

open SimpleGraph WrittenOnTheWallII.Test Matrix

theorem cubicZ : ∀ p : PetersenVertex × PetersenVertex,
    (PetersenGraph.adjMatrix ℤ * PetersenGraph.adjMatrix ℤ * PetersenGraph.adjMatrix ℤ
      - 2 • (PetersenGraph.adjMatrix ℤ * PetersenGraph.adjMatrix ℤ) - 5 • PetersenGraph.adjMatrix ℤ
      + 6 • (1 : Matrix PetersenVertex PetersenVertex ℤ)) p.1 p.2 = 0 := by
  decide +kernel

theorem cubicR :
    (PetersenGraph.adjMatrix ℝ * PetersenGraph.adjMatrix ℝ * PetersenGraph.adjMatrix ℝ
      - 2 • (PetersenGraph.adjMatrix ℝ * PetersenGraph.adjMatrix ℝ) - 5 • PetersenGraph.adjMatrix ℝ
      + 6 • (1 : Matrix PetersenVertex PetersenVertex ℝ)) = 0 := by
  have hZ : (PetersenGraph.adjMatrix ℤ * PetersenGraph.adjMatrix ℤ * PetersenGraph.adjMatrix ℤ
      - 2 • (PetersenGraph.adjMatrix ℤ * PetersenGraph.adjMatrix ℤ) - 5 • PetersenGraph.adjMatrix ℤ
      + 6 • (1 : Matrix PetersenVertex PetersenVertex ℤ)) = 0 := Matrix.ext fun i j => cubicZ (i, j)
  have hmap : (Int.castRingHom ℝ).mapMatrix (PetersenGraph.adjMatrix ℤ) = PetersenGraph.adjMatrix ℝ := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adjMatrix_apply]
    split_ifs <;> simp
  have hR := congrArg (Int.castRingHom ℝ).mapMatrix hZ
  simpa only [map_add, map_sub, map_mul, map_nsmul, map_one, map_zero, hmap] using hR

theorem eig (hA : (PetersenGraph.adjMatrix ℝ).IsHermitian) (i : PetersenVertex) :
    hA.eigenvalues i = 3 ∨ hA.eigenvalues i = 1 ∨ hA.eigenvalues i = -2 := by
  set A := PetersenGraph.adjMatrix ℝ with hAdef
  set v := ⇑(hA.eigenvectorBasis i) with hvdef
  set t := hA.eigenvalues i
  have hv : A *ᵥ v = t • v := hA.mulVec_eigenvectorBasis i
  have hv0 : v ≠ 0 := by
    intro h
    apply (hA.eigenvectorBasis.orthonormal.ne_zero i)
    ext k
    simpa using congrFun h k
  have h0 : (A * A * A - 2 • (A * A) - 5 • A + 6 • (1 : Matrix PetersenVertex PetersenVertex ℝ)) *ᵥ v = 0 := by
    rw [hAdef, cubicR]; simp
  have h1 : (A * A * A - 2 • (A * A) - 5 • A + 6 • (1 : Matrix PetersenVertex PetersenVertex ℝ)) *ᵥ v
      = (t^3 - 2*t^2 - 5*t + 6) • v := by
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hv, Matrix.mulVec_smul, smul_smul]
    rw [← sub_eq_zero]
    ext k
    simp [nsmul_eq_mul]
    ring
  rw [h1] at h0
  rcases smul_eq_zero.mp h0 with h | h
  · have : (t - 3) * (t - 1) * (t + 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · left; linarith
      · right; left; linarith
    · right; right; linarith
  · exact absurd h hv0

theorem key (S : Multiset ℝ) (h : ∀ x ∈ S, x = 3 ∨ x = 1 ∨ x = -2) :
    S.countP (fun x => 0 = x) = 0 ∧
    S.countP (fun x => 0 < x) = S.countP (· = 3) + S.countP (· = 1) ∧
    S.countP (fun x => 0 > x) = S.countP (· = -2) ∧
    Multiset.card S = S.countP (· = 3) + S.countP (· = 1) + S.countP (· = -2) ∧
    S.sum = 3 * (S.countP (· = 3) : ℝ) + S.countP (· = 1) - 2 * S.countP (· = -2) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    rcases h a (Multiset.mem_cons_self a S) with rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Multiset.countP_cons, h1, h2, h3, h4, h5] <;> norm_num <;> ring

theorem main : cvetkovic PetersenGraph = 4 := by
  have hA : (PetersenGraph.adjMatrix ℝ).IsHermitian := isHermitian_adjMatrix (G := PetersenGraph) (R := ℝ)
  have hr : (PetersenGraph.adjMatrix ℝ).charpoly.roots = Finset.univ.val.map hA.eigenvalues := by
    rw [hA.roots_charpoly_eq_eigenvalues]; simp
  have hmem : ∀ x ∈ Finset.univ.val.map hA.eigenvalues, x = 3 ∨ x = 1 ∨ x = -2 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact eig hA i
  obtain ⟨h1, h2, h3, h4, h5⟩ := key _ hmem
  have hcard : Multiset.card (Finset.univ.val.map hA.eigenvalues) = 10 := by
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, card_petersenVertex]
  have hsum : (Finset.univ.val.map hA.eigenvalues).sum = 0 := by
    rw [← Finset.sum_eq_multiset_sum]
    have ht := hA.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at ht
    rw [← ht, trace_adjMatrix]
  unfold cvetkovic
  rw [hr, h1, h2, h3]
  rw [hsum] at h5
  have h6 : 3 * (Multiset.countP (· = (3:ℝ)) (Finset.univ.val.map hA.eigenvalues)) + Multiset.countP (· = (1:ℝ)) (Finset.univ.val.map hA.eigenvalues) = 2 * Multiset.countP (· = (-2:ℝ)) (Finset.univ.val.map hA.eigenvalues) := by
    exact_mod_cast (by linarith : (3 * (Multiset.countP (· = (3:ℝ)) (Finset.univ.val.map hA.eigenvalues) : ℝ) + Multiset.countP (· = (1:ℝ)) (Finset.univ.val.map hA.eigenvalues) = 2 * Multiset.countP (· = (-2:ℝ)) (Finset.univ.val.map hA.eigenvalues)))
  omega

end OMA.PetersenCvetkovic

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.petersen_cvetkovic :=
  OMA.PetersenCvetkovic.main
