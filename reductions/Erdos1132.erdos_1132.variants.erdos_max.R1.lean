import FormalConjectures.ErdosProblems.«1132»

-- Reduction Erdos1132.erdos_1132.variants.erdos_max.R1 of Erdős Problem 1132 — erdos max
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Route (Brutman 1978, via de Boor and Pinkus 1978): the Lebesgue function of any n distinct nodes
-- in [-1, 1] somewhere reaches the smallest interior local maximum of any canonical node set (H1,
-- the conjecture of Erdős proved by de Boor and Pinkus). For the expanded Chebyshev nodes every
-- interior local maximum exceeds (2/pi) log n - C (H2, an explicit computation at the extrema
-- cos(j pi / n) of T_n). The case n = 1 is l_0(x_0) = 1.

namespace OMA.R_Erdos1132_erdos_1132_variants_erdos_max_R1

open Erdos1132 Finset Real

-- H1 (conjecture of Erdős, proved by de Boor and Pinkus, J. Approx. Theory 24 (1978) 289-303, and
-- Kilgore, ibid. 273-288; see Brutman, Ann. Numer. Math. 4 (1997), and Ibrahimoglu, J. Inequal.
-- Appl. 2016:93, Section 3.7). Let y 0 < ... < y (n-1) be canonical (y 0 = -1, y (n-1) = 1). Then
-- for some gap [y j, y (j+1)] the maximum of the Lebesgue function of y on that gap is at most the
-- optimal Lebesgue constant, hence at most the maximum on [-1, 1] of the Lebesgue function of any
-- n distinct nodes x 0, ..., x (n-1) in [-1, 1] (in any order).
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ y x : ℕ → ℝ, (∀ i j, i < j → j < n → y i < y j) → y 0 = -1 →
    y (n - 1) = 1 → (∀ k < n, x k ∈ Set.Icc (-1 : ℝ) 1) → Set.InjOn x (Set.Iio n) →
      ∃ j, j + 1 < n ∧ ∀ s ∈ Set.Icc (y j) (y (j + 1)),
        ∃ t ∈ Set.Icc (-1 : ℝ) 1, lebesgueFunction n y s ≤ lebesgueFunction n x t

-- H2 (expanded Chebyshev nodes; Brutman, SIAM J. Numer. Anal. 15 (1978) 694-704, and Rivlin, The
-- Chebyshev Polynomials, Section 1.3). The nodes -cos((2k+1) pi/(2n)) / cos(pi/(2n)), k < n, are
-- increasing from -1 to 1, and on each gap between consecutive ones the Lebesgue function exceeds
-- (2/pi) log n - C somewhere. By affine invariance this is the Lebesgue function of the zeros of
-- T_n between two consecutive zeros; at the extremum cos(j pi/n) of T_n it equals
-- (1/n) sum_k sin t_k / |cos(j pi/n) - cos t_k|, which is (2/pi) log n + O(1).
def H2 : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (∀ i j, i < j → j < n →
      -Real.cos ((2 * i + 1) * π / (2 * n)) / Real.cos (π / (2 * n)) <
        -Real.cos ((2 * j + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) ∧
    -Real.cos ((2 * (0 : ℕ) + 1) * π / (2 * n)) / Real.cos (π / (2 * n)) = -1 ∧
    -Real.cos ((2 * ((n - 1 : ℕ) : ℝ) + 1) * π / (2 * n)) / Real.cos (π / (2 * n)) = 1 ∧
    ∀ j, j + 1 < n → ∃ s ∈ Set.Icc
        (-Real.cos ((2 * j + 1) * π / (2 * n)) / Real.cos (π / (2 * n)))
        (-Real.cos ((2 * ((j + 1 : ℕ) : ℝ) + 1) * π / (2 * n)) / Real.cos (π / (2 * n))),
      2 / π * Real.log n - C <
        lebesgueFunction n (fun k : ℕ => -Real.cos ((2 * k + 1) * π / (2 * n)) /
          Real.cos (π / (2 * n))) s

lemma lebesgueFunction_one (x : ℕ → ℝ) : lebesgueFunction 1 x (x 0) = 1 := by
  have h := lagrangeBasis_self (n := 1) (x := x) (k := 0)
    (fun a ha b hb _ => by simp only [Set.mem_Iio] at ha hb; omega) (by norm_num)
  simp [lebesgueFunction, h]

theorem main : H1 → H2 → type_of% @Erdos1132.erdos_1132.variants.erdos_max := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2
  refine ⟨max C 0, fun n hn x hx hinj => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have h1n : n = 1 := by omega
    subst h1n
    refine ⟨x 0, hx 0 (by norm_num), ?_⟩
    rw [lebesgueFunction_one]
    simp only [Nat.cast_one, Real.log_one, mul_zero, zero_sub]
    have : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    linarith
  · obtain ⟨hmono, h0, hlast, hgap⟩ := hC n hn2
    obtain ⟨j, hj, hj'⟩ := h1 n hn2
      (fun k : ℕ => -Real.cos ((2 * k + 1) * π / (2 * n)) / Real.cos (π / (2 * n))) x
      hmono h0 hlast hx hinj
    obtain ⟨s, hs, hbound⟩ := hgap j hj
    obtain ⟨t, ht, hle⟩ := hj' s hs
    refine ⟨t, ht, ?_⟩
    have : C ≤ max C 0 := le_max_left _ _
    linarith

end OMA.R_Erdos1132_erdos_1132_variants_erdos_max_R1
