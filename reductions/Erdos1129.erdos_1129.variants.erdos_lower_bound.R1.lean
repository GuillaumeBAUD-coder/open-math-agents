import FormalConjectures.ErdosProblems.«1129»

-- Reduction Erdos1129.erdos_1129.variants.erdos_lower_bound.R1 of Erdős Problem 1129 — erdos lower bound
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Route (Brutman 1978, via de Boor and Pinkus 1978): every node set has Lebesgue constant at least
-- the smallest interior local maximum of any canonical node set (H1, the conjecture of Erdős proved
-- by de Boor and Pinkus). For the expanded Chebyshev nodes every interior local maximum is at least
-- (2/pi) log n - C (H2, an explicit computation at the extrema cos(j pi / n) of T_n). The case n = 1
-- is the trivial bound 1 <= Lambda.

namespace OMA.R_Erdos1129_erdos_1129_variants_erdos_lower_bound_R1

open Erdos1129 Finset Real

-- H1 (conjecture of Erdős, proved by de Boor and Pinkus, J. Approx. Theory 24 (1978) 289-303, and
-- Kilgore, ibid. 273-288; see Brutman, Ann. Numer. Math. 4 (1997), and Ibrahimoglu, J. Inequal.
-- Appl. 2016:93, Section 3.7). For a canonical node set y (x_1 = -1, x_n = 1) the smallest of the
-- local maxima lambda_1(y), ..., lambda_(n-1)(y) between consecutive nodes is at most the optimal
-- Lebesgue constant, hence at most the Lebesgue constant of every node set x in [-1, 1].
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ y x : Fin n → ℝ, IsCanonical y → IsNodeSet x →
    ∃ j ∈ Finset.Icc 1 (n - 1), gapMax y j ≤ lebesgueConstant x

-- H2 (expanded Chebyshev nodes; Brutman, SIAM J. Numer. Anal. 15 (1978) 694-704, and Rivlin, The
-- Chebyshev Polynomials, Section 1.3). The nodes -cos((2k+1) pi/(2n)) / cos(pi/(2n)), k < n, form a
-- canonical node set, and each of its interior local maxima exceeds (2/pi) log n - C. By affine
-- invariance the j-th one equals the maximum of the Lebesgue function of the zeros of T_n between
-- two consecutive zeros, and at the extremum cos(j pi/n) of T_n that function equals
-- (1/n) sum_k sin t_k / |cos(j pi/n) - cos t_k|, which is (2/pi) log n + O(1).
def H2 : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    IsCanonical (fun k : Fin n => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) ∧
    ∀ j ∈ Finset.Icc 1 (n - 1), 2 / π * Real.log n - C <
      gapMax (fun k : Fin n => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) j

lemma bdd_L {n : ℕ} (x : Fin n → ℝ) : BddAbove (lebesgueFunction x '' Set.Icc (-1 : ℝ) 1) := by
  refine (isCompact_Icc.image ?_).bddAbove
  unfold lebesgueFunction
  exact continuous_finsetSum _ fun k _ => (Polynomial.continuous _).abs

lemma one_le_Lam {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) :
    1 ≤ lebesgueConstant x := by
  set j : Fin n := ⟨0, by omega⟩
  have e : ∀ k, (Lagrange.basis univ x k).eval (x j) = if k = j then 1 else 0 := by
    intro k
    split_ifs with h
    · subst h; exact Lagrange.eval_basis_self hx.1.injective.injOn (mem_univ _)
    · exact Lagrange.eval_basis_of_ne h (mem_univ _)
  have hL : lebesgueFunction x (x j) = 1 := by
    simp only [lebesgueFunction, e]
    rw [sum_eq_single j (fun b _ hb => by rw [if_neg hb]; norm_num) (by simp)]
    simp
  have := le_csSup (bdd_L x) (Set.mem_image_of_mem _ (hx.2 j))
  rw [hL] at this
  exact this

theorem main : H1 → H2 → type_of% @Erdos1129.erdos_1129.variants.erdos_lower_bound := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2
  refine ⟨max C 0, fun n x hn hx => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have h1n : n = 1 := by omega
    subst h1n
    have := one_le_Lam le_rfl x hx
    simp only [Nat.cast_one, Real.log_one, mul_zero, zero_sub]
    have : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    linarith
  · obtain ⟨hcan, hgap⟩ := hC n hn2
    obtain ⟨j, hj, hle⟩ := h1 n hn2 _ x hcan hx
    have h3 := hgap j hj
    have : C ≤ max C 0 := le_max_left _ _
    linarith

end OMA.R_Erdos1129_erdos_1129_variants_erdos_lower_bound_R1
