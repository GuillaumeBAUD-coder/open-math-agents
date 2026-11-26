import OMAReductions.R_Erdos91_erdos_91_test_wheelSeven_optimal_R1

/-! A planar set with at most two pairwise distances has at most six points. -/

open EuclideanGeometry

namespace WheelBound

-- The six monomials of degree at most two in the planar coordinates.
private noncomputable def feature (p : ℝ²) : Fin 6 → ℝ :=
  ![1, p 0, p 1, p 0 ^ 2, p 0 * p 1, p 1 ^ 2]

private noncomputable def coeff (a b : ℝ) (q : ℝ²) : Fin 6 → ℝ :=
  let x := q 0
  let y := q 1
  let r := x ^ 2 + y ^ 2
  ![r ^ 2 - (a + b) * r + a * b / 2,
    (a + b - 4 * r) * x, (a + b - 4 * r) * y,
    r + 2 * x ^ 2, 4 * x * y, r + 2 * y ^ 2]

private noncomputable def halfKernel (a b : ℝ) (p q : ℝ²) : ℝ :=
  ∑ k, feature p k * coeff a b q k

-- Each term in the quartic has degree at most two in at least one of p and q.
private lemma expand_kernel (a b : ℝ) (p q : ℝ²) :
    (dist p q ^ 2 - a) * (dist p q ^ 2 - b) =
    halfKernel a b p q + halfKernel a b q p := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [halfKernel, feature, coeff, Fin.sum_univ_succ, Real.dist_eq, sq_abs]
  ring

private lemma two_radii (S : Finset ℝ²) (h : distinctDistances S < 3) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ d ∈ distanceSet S, d = a ∨ d = b := by
  classical
  have pos : ∀ d ∈ distanceSet S, 0 < d := by
    intro d hd
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hd
    exact dist_pos.mpr (Finset.mem_offDiag.mp hpq).2.2
  change (distanceSet S).card < 3 at h
  have cases' : (distanceSet S).card = 0 ∨ (distanceSet S).card = 1 ∨
      (distanceSet S).card = 2 := by omega
  rcases cases' with h0 | h1 | h2
  · exact ⟨1, 1, by norm_num, by norm_num, by simp [Finset.card_eq_zero.mp h0]⟩
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have hp := pos a (by simp [ha])
    exact ⟨a, a, hp, hp, by simp [ha]⟩
  · obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp h2
    exact ⟨a, b, pos a (by simp [hab]), pos b (by simp [hab]), by simp [hab]⟩

-- A weighted relation among the six monomials annihilates each half of the
-- quartic after summing over both points. On the diagonal the quartic is positive.
private lemma bound (S : Finset ℝ²) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (roots : ∀ i j : S, i ≠ j →
      (dist i.val j.val ^ 2 - a) * (dist i.val j.val ^ 2 - b) = 0) :
    S.card ≤ 6 := by
  classical
  have independent : LinearIndependent ℝ (fun i : S => feature i.val) := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro c hc t
    have moment (k : Fin 6) : ∑ i, c i * feature i.val k = 0 := by
      simpa [Finset.sum_apply] using congrFun hc k
    have vanish (j : S) : ∑ i : S, c i * halfKernel a b i.val j.val = 0 := by
      simp only [halfKernel, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k _
      simp_rw [← mul_assoc, ← Finset.sum_mul, moment, zero_mul]
    let term := fun i j : S => c j * (c i * halfKernel a b i.val j.val)
    have half_zero : ∑ j : S, ∑ i : S, term i j = 0 := by
      simp only [term, ← Finset.mul_sum, vanish, mul_zero, Finset.sum_const_zero]
    have other_zero : ∑ j : S, ∑ i : S, term j i = 0 := by
      rw [Finset.sum_comm]
      exact half_zero
    have entry (i j : S) : term i j + term j i =
        if i = j then c j ^ 2 * (a * b) else 0 := by
      calc
        _ = c i * c j * ((dist i.val j.val ^ 2 - a) * (dist i.val j.val ^ 2 - b)) := by
          rw [expand_kernel]
          dsimp [term]
          ring
        _ = _ := by
          split_ifs with e
          · subst i
            simp only [dist_self, zero_pow (by decide : 2 ≠ 0), zero_sub, neg_mul_neg, pow_two]
          · rw [roots i j e, mul_zero]
    have total : ∑ j : S, c j ^ 2 * (a * b) = 0 := by
      have hz : ∑ j : S, ∑ i : S, (term i j + term j i) = 0 := by
        simp_rw [Finset.sum_add_distrib]
        rw [half_zero, other_zero, add_zero]
      simpa only [entry, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hz
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (sq_nonneg (c j)) (mul_pos ha hb).le)).mp total t (Finset.mem_univ _)
    rcases mul_eq_zero.mp ht with ht | ht
    · exact eq_zero_of_pow_eq_zero ht
    · exact ((mul_pos ha hb).ne' ht).elim
  simpa [Module.finrank_fintype_fun_eq_card] using independent.fintype_card_le_finrank

end WheelBound

open WheelBound

theorem OMA.solution : OMA.R_Erdos91_erdos_91_test_wheelSeven_optimal_R1.H2 := by
  intro S h
  obtain ⟨a, b, ha, hb, hr⟩ := two_radii S h
  apply bound S (a ^ 2) (b ^ 2) (by positivity) (by positivity)
  intro i j hij
  have hm : dist i.val j.val ∈ distanceSet S := Finset.mem_image.mpr
    ⟨(i.val, j.val), Finset.mem_offDiag.mpr ⟨i.property, j.property, fun e => hij (Subtype.ext e)⟩,
     rfl⟩
  rcases hr _ hm with he | he <;> simp [he]
