import OMAStatements.S_oeis_a325695

namespace OMA.S_oeis_a325695_proof

open OMA.S_oeis_a325695

private def p3 (n : ℕ) : ℕ :=
  ∑ u ∈ Finset.range (n + 1),
    ((Finset.range (n + 1)).filter (fun v => decide (3 * u + 2 * v + 6 ≤ n))).card

private def bad (n : ℕ) : ℕ :=
  ∑ u ∈ Finset.range (n + 1),
    ((Finset.range (n + 1)).filter
      (fun v => decide (3 * u + 2 * v + 6 ≤ n ∧ 2 * (2 * u + v + 3) = n))).card

private lemma allowed_iff (n u v : ℕ) :
    allowed n u v = true ↔ 3 * u + 2 * v + 6 ≤ n ∧ 2 * (2 * u + v + 3) ≠ n := by
  dsimp [allowed]
  simp only [decide_eq_true_eq]
  omega

private lemma term_add_bad (n : ℕ) : term n + bad n = p3 n := by
  dsimp [term, bad, p3]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hdisj : Disjoint
      ((Finset.range (n + 1)).filter (fun v => allowed n u v))
      ((Finset.range (n + 1)).filter
        (fun v => decide (3 * u + 2 * v + 6 ≤ n ∧ 2 * (2 * u + v + 3) = n))) := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h2
    rw [allowed_iff] at h1
    simp only [decide_eq_true_eq] at h2
    exact h1.2 h2.2
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext v
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, allowed_iff,
    decide_eq_true_eq]
  tauto

private lemma bad_eq (n : ℕ) : bad n = if n % 2 = 0 then (n / 2 - 1) / 2 else 0 := by
  dsimp [bad]
  by_cases hn : n % 2 = 0
  · rw [if_pos hn]
    have hcard : ∀ u ∈ Finset.range (n + 1),
        ((Finset.range (n + 1)).filter
          (fun v => decide (3 * u + 2 * v + 6 ≤ n ∧ 2 * (2 * u + v + 3) = n))).card =
        if u < (n / 2 - 1) / 2 then 1 else 0 := by
      intro u _
      by_cases hu : u < (n / 2 - 1) / 2
      · rw [if_pos hu, Finset.card_eq_one]
        refine ⟨n / 2 - 2 * u - 3, ?_⟩
        ext v
        simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq, Finset.mem_singleton]
        omega
      · rw [if_neg hu, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro v _
        simp only [decide_eq_true_eq]
        omega
    rw [Finset.sum_congr rfl hcard, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, smul_eq_mul, mul_one]
    have hsub : (Finset.range (n + 1)).filter (fun u => u < (n / 2 - 1) / 2) =
        Finset.range ((n / 2 - 1) / 2) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hsub, Finset.card_range]
  · rw [if_neg hn]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    simp only [decide_eq_true_eq]
    omega

private lemma p3_filter_extend (m N u : ℕ) (hN : m ≤ N) :
    ((Finset.range (N + 1)).filter (fun v => decide (3 * u + 2 * v + 6 ≤ m))).card =
    ((Finset.range (m + 1)).filter (fun v => decide (3 * u + 2 * v + 6 ≤ m))).card := by
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
  omega

private lemma p3_add_six (n : ℕ) (hn : 1 ≤ n) : p3 (n + 6) = p3 n + n := by
  dsimp [p3]
  have h1 : ∀ u,
      ((Finset.range (n + 6 + 1)).filter
        (fun v => decide (3 * (u + 2) + 2 * v + 6 ≤ n + 6))).card =
      ((Finset.range (n + 1)).filter
        (fun v => decide (3 * u + 2 * v + 6 ≤ n))).card := by
    intro u
    rw [← p3_filter_extend n (n + 6) u (by omega)]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
    omega
  have hzero : ∀ u, n + 1 ≤ u →
      ((Finset.range (n + 1)).filter (fun v => decide (3 * u + 2 * v + 6 ≤ n))).card = 0 := by
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    simp only [decide_eq_true_eq]
    omega
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp_rw [h1]
  have htail : ∑ u ∈ Finset.range (n + 5),
      ((Finset.range (n + 1)).filter (fun v => decide (3 * u + 2 * v + 6 ≤ n))).card =
      ∑ u ∈ Finset.range (n + 1),
        ((Finset.range (n + 1)).filter (fun v => decide (3 * u + 2 * v + 6 ≤ n))).card := by
    rw [show n + 5 = (n + 1) + 4 by omega]
    simp only [Finset.sum_range_succ]
    rw [hzero (n + 1) (by omega), hzero (n + 2) (by omega),
      hzero (n + 3) (by omega), hzero (n + 4) (by omega)]
    omega
  rw [htail]
  have hf0 : ((Finset.range (n + 6 + 1)).filter
      (fun v => decide (3 * 0 + 2 * v + 6 ≤ n + 6))).card = n / 2 + 1 := by
    have heq : (Finset.range (n + 6 + 1)).filter
        (fun v => decide (3 * 0 + 2 * v + 6 ≤ n + 6)) = Finset.range (n / 2 + 1) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
      omega
    rw [heq, Finset.card_range]
  have hf1 : ((Finset.range (n + 6 + 1)).filter
      (fun v => decide (3 * 1 + 2 * v + 6 ≤ n + 6))).card = (n - 1) / 2 := by
    have heq : (Finset.range (n + 6 + 1)).filter
        (fun v => decide (3 * 1 + 2 * v + 6 ≤ n + 6)) = Finset.range ((n - 1) / 2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
      omega
    rw [heq, Finset.card_range]
  rw [hf0, hf1]
  omega

private lemma p3_rec (k : ℕ) :
    p3 (k + 10) + p3 (k + 5) + p3 (k + 4) + p3 (k + 3) =
    p3 (k + 8) + p3 (k + 7) + p3 (k + 6) + p3 (k + 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 6
    · interval_cases k <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
      have hm := ih m (by omega)
      have hsub : ∀ j : ℕ, 1 ≤ j → p3 (m + 6 + j) = p3 (m + j) + (m + j) := fun j hj => by
        rw [show m + 6 + j = m + j + 6 by omega]
        exact p3_add_six (m + j) (by omega)
      have a10 := hsub 10 (by omega)
      have a5 := hsub 5 (by omega)
      have a4 := hsub 4 (by omega)
      have a3 := hsub 3 (by omega)
      have a8 := hsub 8 (by omega)
      have a7 := hsub 7 (by omega)
      have a6 := hsub 6 (by omega)
      have a1 := hsub 1 (by omega)
      omega

private lemma bad_mod4 (q : ℕ) :
    bad (4 * q) = q - 1 ∧ bad (4 * q + 1) = 0 ∧
    bad (4 * q + 2) = q ∧ bad (4 * q + 3) = 0 := by
  simp only [bad_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [if_pos (by omega), show 4 * q / 2 = 2 * q by omega]; omega
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega), show (4 * q + 2) / 2 = 2 * q + 1 by omega]; omega
  · rw [if_neg (by omega)]

private lemma bad_rec (k : ℕ) :
    bad (k + 10) + bad (k + 5) + bad (k + 4) + bad (k + 3) =
    bad (k + 8) + bad (k + 7) + bad (k + 6) + bad (k + 1) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ k = 4 * q + r :=
    ⟨k / 4, k % 4, Nat.mod_lt _ (by omega), (Nat.div_add_mod k 4).symm⟩
  have hb0 := fun x => (bad_mod4 x).1
  have hb1 := fun x => (bad_mod4 x).2.1
  have hb2 := fun x => (bad_mod4 x).2.2.1
  have hb3 := fun x => (bad_mod4 x).2.2.2
  interval_cases r
  · rw [show 4 * q + 0 + 10 = 4 * (q + 2) + 2 by omega,
        show 4 * q + 0 + 5 = 4 * (q + 1) + 1 by omega,
        show 4 * q + 0 + 4 = 4 * (q + 1) by omega,
        show 4 * q + 0 + 3 = 4 * q + 3 by omega,
        show 4 * q + 0 + 8 = 4 * (q + 2) by omega,
        show 4 * q + 0 + 7 = 4 * (q + 1) + 3 by omega,
        show 4 * q + 0 + 6 = 4 * (q + 1) + 2 by omega,
        show 4 * q + 0 + 1 = 4 * q + 1 by omega]
    simp only [hb0, hb1, hb2, hb3]
    omega
  · rw [show 4 * q + 1 + 10 = 4 * (q + 2) + 3 by omega,
        show 4 * q + 1 + 5 = 4 * (q + 1) + 2 by omega,
        show 4 * q + 1 + 4 = 4 * (q + 1) + 1 by omega,
        show 4 * q + 1 + 3 = 4 * (q + 1) by omega,
        show 4 * q + 1 + 8 = 4 * (q + 2) + 1 by omega,
        show 4 * q + 1 + 7 = 4 * (q + 2) by omega,
        show 4 * q + 1 + 6 = 4 * (q + 1) + 3 by omega,
        show 4 * q + 1 + 1 = 4 * q + 2 by omega]
    simp only [hb0, hb1, hb2, hb3]
    omega
  · rw [show 4 * q + 2 + 10 = 4 * (q + 3) by omega,
        show 4 * q + 2 + 5 = 4 * (q + 1) + 3 by omega,
        show 4 * q + 2 + 4 = 4 * (q + 1) + 2 by omega,
        show 4 * q + 2 + 3 = 4 * (q + 1) + 1 by omega,
        show 4 * q + 2 + 8 = 4 * (q + 2) + 2 by omega,
        show 4 * q + 2 + 7 = 4 * (q + 2) + 1 by omega,
        show 4 * q + 2 + 6 = 4 * (q + 2) by omega,
        show 4 * q + 2 + 1 = 4 * q + 3 by omega]
    simp only [hb0, hb1, hb2, hb3]
    omega
  · rw [show 4 * q + 3 + 10 = 4 * (q + 3) + 1 by omega,
        show 4 * q + 3 + 5 = 4 * (q + 2) by omega,
        show 4 * q + 3 + 4 = 4 * (q + 1) + 3 by omega,
        show 4 * q + 3 + 3 = 4 * (q + 1) + 2 by omega,
        show 4 * q + 3 + 8 = 4 * (q + 2) + 3 by omega,
        show 4 * q + 3 + 7 = 4 * (q + 2) + 2 by omega,
        show 4 * q + 3 + 6 = 4 * (q + 2) + 1 by omega,
        show 4 * q + 3 + 1 = 4 * (q + 1) by omega]
    simp only [hb0, hb1, hb2, hb3]
    omega

private lemma term_rec (k : ℕ) :
    term (k + 10) + term (k + 5) + term (k + 4) + term (k + 3) =
    term (k + 8) + term (k + 7) + term (k + 6) + term (k + 1) := by
  have h10 := term_add_bad (k + 10)
  have h5 := term_add_bad (k + 5)
  have h4 := term_add_bad (k + 4)
  have h3 := term_add_bad (k + 3)
  have h8 := term_add_bad (k + 8)
  have h7 := term_add_bad (k + 7)
  have h6 := term_add_bad (k + 6)
  have h1 := term_add_bad (k + 1)
  have hp := p3_rec k
  have hb := bad_rec k
  omega

private lemma series_eq :
    ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 *
      (1 + PowerSeries.X ^ 2) * (1 + PowerSeries.X + PowerSeries.X ^ 2)) * series =
    PowerSeries.X ^ 7 * (1 + PowerSeries.X + 2 * PowerSeries.X ^ 2) := by
  have hL : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 3 * (1 + PowerSeries.X) ^ 2 *
      (1 + PowerSeries.X ^ 2) * (1 + PowerSeries.X + PowerSeries.X ^ 2) =
      1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 +
        PowerSeries.X ^ 5 + PowerSeries.X ^ 6 + PowerSeries.X ^ 7 - PowerSeries.X ^ 9 := by
    ring
  have hR : (PowerSeries.X : PowerSeries ℚ) ^ 7 * (1 + PowerSeries.X + 2 * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 7 + PowerSeries.X ^ 8 + PowerSeries.X ^ 9 + PowerSeries.X ^ 9 := by
    ring
  rw [hL, hR]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  dsimp [series]
  simp only [PowerSeries.coeff_mk]
  by_cases hn : n < 10
  · have h0 : term 0 = 0 := by decide
    have h1 : term 1 = 0 := by decide
    have h2 : term 2 = 0 := by decide
    have h3 : term 3 = 0 := by decide
    have h4 : term 4 = 0 := by decide
    have h5 : term 5 = 0 := by decide
    have h6 : term 6 = 0 := by decide
    have h7 : term 7 = 1 := by decide
    have h8 : term 8 = 1 := by decide
    have h9 : term 9 = 3 := by decide
    interval_cases n <;> (simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]; try norm_num)
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have hr := term_rec k
    have hq : (term (k + 10) : ℚ) + term (k + 5) + term (k + 4) + term (k + 3) =
        term (k + 8) + term (k + 7) + term (k + 6) + term (k + 1) := by
      exact_mod_cast hr
    simp only [show 2 ≤ k + 10 by omega, show 3 ≤ k + 10 by omega,
      show 4 ≤ k + 10 by omega, show 5 ≤ k + 10 by omega,
      show 6 ≤ k + 10 by omega, show 7 ≤ k + 10 by omega,
      show 9 ≤ k + 10 by omega, ite_true,
      show ¬ (k + 10 = 7) by omega, show ¬ (k + 10 = 8) by omega,
      show ¬ (k + 10 = 9) by omega, ite_false]
    have e2 : k + 10 - 2 = k + 8 := by omega
    have e3 : k + 10 - 3 = k + 7 := by omega
    have e4 : k + 10 - 4 = k + 6 := by omega
    have e5 : k + 10 - 5 = k + 5 := by omega
    have e6 : k + 10 - 6 = k + 4 := by omega
    have e7 : k + 10 - 7 = k + 3 := by omega
    have e9 : k + 10 - 9 = k + 1 := by omega
    rw [e2, e3, e4, e5, e6, e7, e9]
    linarith

end OMA.S_oeis_a325695_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a325695.main :=
  ⟨OMA.S_oeis_a325695_proof.term_rec, OMA.S_oeis_a325695_proof.series_eq⟩
