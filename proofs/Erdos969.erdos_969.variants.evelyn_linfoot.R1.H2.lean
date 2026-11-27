import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! The product of the squarefree counting function's increment series and zeta at twice
the argument recovers the Riemann zeta function in the half-plane of absolute convergence.
The parity argument follows the project's PowerfulNumbersDensity proof.
The square-supported series reindexing follows its one-point ChowlaLiouvilleConjecture proof. -/

namespace SquarefreeSeries

noncomputable def freeCoeff (n : ℕ) : ℂ := if Squarefree n then 1 else 0

noncomputable def squareCoeff (n : ℕ) : ℂ := if IsSquare n then 1 else 0

lemma count_diff (n : ℕ) :
    (Erdos969.squarefreeCounting n : ℂ) - Erdos969.squarefreeCounting (n - 1) =
      freeCoeff n := by
  classical
  cases n with
  | zero => simp [freeCoeff]
  | succ n =>
    rw [Nat.succ_sub_one]
    unfold Erdos969.squarefreeCounting
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n + 1), Finset.filter_insert]
    have hnot : n + 1 ∉ (Finset.Icc 1 n).filter Squarefree := by simp
    by_cases hf : Squarefree (n + 1) <;> simp [freeCoeff, hf, hnot]

lemma squarefree_part_unique {a b c d : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hb : Squarefree b) (hd : Squarefree d)
    (h : a ^ 2 * b = c ^ 2 * d) : b = d := by
  have parity (x y : ℕ) (hx : 0 < x) (hy : Squarefree y) (p : ℕ) :
      y.factorization p = (x ^ 2 * y).factorization p % 2 := by
    rw [Nat.factorization_mul (pow_ne_zero 2 hx.ne') hy.ne_zero, Nat.factorization_pow]
    have := hy.natFactorization_le_one p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    omega
  apply Nat.eq_of_factorization_eq hb.ne_zero hd.ne_zero
  intro p
  rw [parity a b ha hb p, parity c d hc hd p, h]

lemma conv_eq_one {n : ℕ} (hn : n ≠ 0) :
    LSeries.convolution freeCoeff squareCoeff n = 1 := by
  classical
  obtain ⟨a, b, ha, hb, hprod, hfree⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  have hmem : (a, b ^ 2) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨by simpa only [mul_comm] using hprod, hn⟩
  rw [LSeries.convolution_def]
  change ∑ p ∈ n.divisorsAntidiagonal, freeCoeff p.1 * squareCoeff p.2 = 1
  rw [Finset.sum_eq_single_of_mem (a, b ^ 2) hmem]
  · simp [freeCoeff, squareCoeff, hfree, show IsSquare (b ^ 2) from ⟨b, sq b⟩]
  · rintro ⟨u, v⟩ hp hne
    by_cases hu : Squarefree u
    · by_cases hv : IsSquare v
      · obtain ⟨k, rfl⟩ := hv
        have hp' : u * (k * k) = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hk : k ≠ 0 := by rintro rfl; simp_all
        have hprod' : k ^ 2 * u = b ^ 2 * a := by
          calc k ^ 2 * u = u * (k * k) := by ring
               _ = n := hp'
               _ = b ^ 2 * a := hprod.symm
        have hua := squarefree_part_unique (Nat.pos_of_ne_zero hk) hb hu hfree hprod'
        subst u
        have hk2 : k ^ 2 = b ^ 2 := Nat.eq_of_mul_eq_mul_right ha hprod'
        exact (hne (Prod.ext rfl (by simpa only [pow_two] using hk2))).elim
      · simp [squareCoeff, hv]
    · simp [freeCoeff, hu]

-- Reindex the series on perfect squares by their nonnegative square roots.
lemma square_series {s : ℂ} (hs : 1 < s.re) :
    LSeries squareCoeff s = riemannZeta (2 * s) := by
  have h2s : 1 < (2 * s).re := by simp; linarith
  rw [← LSeries_one_eq_riemannZeta h2s]
  unfold LSeries
  have hterm (m : ℕ) : LSeries.term squareCoeff s (m ^ 2) = LSeries.term 1 (2 * s) m := by
    have hpower : ((m ^ 2 : ℕ) : ℂ) ^ s = (m : ℂ) ^ (2 * s) := by
      simpa using (Complex.natCast_cpow_natCast_mul m 2 s).symm
    by_cases hm : m = 0
    · simp [hm, LSeries.term]
    · have hsquare : IsSquare (m ^ 2) := ⟨m, sq m⟩
      simp only [LSeries.term_of_ne_zero (pow_ne_zero 2 hm), LSeries.term_of_ne_zero hm,
        squareCoeff, if_pos hsquare, Pi.one_apply, hpower]
  have htsum : (∑' m : ℕ, LSeries.term squareCoeff s (m ^ 2)) =
      ∑' n : ℕ, LSeries.term squareCoeff s n := by
    refine Function.Injective.tsum_eq (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) fun n hn => ?_
    by_cases hsquare : IsSquare n
    · obtain ⟨k, rfl⟩ := hsquare
      exact ⟨k, sq k⟩
    · exact (hn (by simp [LSeries.term, squareCoeff, hsquare])).elim
  rw [← htsum]
  exact tsum_congr hterm

theorem squarefree_lseries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (Erdos969.squarefreeCounting n : ℂ) -
      (Erdos969.squarefreeCounting (n - 1) : ℂ)) s * riemannZeta (2 * s) = riemannZeta s := by
  have hf : LSeriesSummable freeCoeff s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
      by_cases h : Squarefree n <;> simp [freeCoeff, h]) hs
  have hg : LSeriesSummable squareCoeff s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
      by_cases h : IsSquare n <;> simp [squareCoeff, h]) hs
  simp_rw [count_diff]
  rw [← square_series hs, ← LSeries_convolution' hf hg, ← LSeries_one_eq_riemannZeta hs]
  exact LSeries_congr (fun hn => conv_eq_one hn) s

end SquarefreeSeries

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1.H2 := SquarefreeSeries.squarefree_lseries
