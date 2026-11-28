import OMAStatements.S_oeis_a224832
import Mathlib

open OMA.S_oeis_a224832 ArithmeticFunction

theorem P224832.recip (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (1 / (d : ℚ)) = (sigma 1 n : ℚ) / n := by
  rw [sigma_one_apply, Nat.cast_sum, Finset.sum_div]
  rw [← Nat.sum_div_divisors n (fun d => (d : ℚ) / n)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [Nat.cast_div hdn hd0]
  field_simp

theorem P224832.oddf (M e : ℕ) (hM : Odd M) :
    (2 ^ e * M).divisors.filter (fun d => ¬ Even d) = M.divisors := by
  have hM0 : M ≠ 0 := by rintro rfl; simp at hM
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, hodd⟩
    rw [Nat.not_even_iff_odd] at hodd
    exact ⟨(Nat.Coprime.pow_right e hodd.coprime_two_right).dvd_of_dvd_mul_left hd, hM0⟩
  · rintro ⟨hd, _⟩
    refine ⟨⟨dvd_mul_of_dvd_right hd _, by positivity⟩, ?_⟩
    rw [Nat.not_even_iff_odd]
    exact hM.of_dvd_nat hd

theorem P224832.sm (p e r : ℕ) (hp : p.Prime) (hc : Nat.Coprime (p ^ e) r) :
    sigma 1 (p ^ e * r) = (∑ k ∈ Finset.range (e + 1), p ^ k) * sigma 1 r := by
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, sigma_one_apply_prime_pow hp]

theorem P224832.sM : sigma 1 (3 ^ 5 * (5 ^ 2 * (7 ^ 2 * (11 ^ 1 * (13 ^ 1 * (17 ^ 1 * (19 ^ 1 *
    (31 ^ 1 * (43 ^ 1 * 257 ^ 1))))))))) = 364 * 31 * 57 * 12 * 14 * 18 * 20 * 32 * 44 * 258 := by
  rw [P224832.sm 3 5, P224832.sm 5 2, P224832.sm 7 2, P224832.sm 11 1, P224832.sm 13 1, P224832.sm 17 1,
    P224832.sm 19 1, P224832.sm 31 1, P224832.sm 43 1, sigma_one_apply_prime_pow]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  all_goals norm_num

theorem OMA.solution : type_of% @OMA.S_oeis_a224832.main := by
  intro hc
  set M : ℕ := 3 ^ 5 * (5 ^ 2 * (7 ^ 2 * (11 ^ 1 * (13 ^ 1 * (17 ^ 1 * (19 ^ 1 *
    (31 ^ 1 * (43 ^ 1 * 257 ^ 1)))))))) with hMdef
  have hMo : Odd M := by rw [hMdef]; decide
  have hM0 : M ≠ 0 := by rw [hMdef]; norm_num
  have hsM : sigma 1 M = 364 * 31 * 57 * 12 * 14 * 18 * 20 * 32 * 44 * 258 := P224832.sM
  have hs16 : sigma 1 (2 ^ 16 * M) = (∑ k ∈ Finset.range (16 + 1), 2 ^ k) * sigma 1 M :=
    P224832.sm 2 16 M Nat.prime_two (Nat.Coprime.pow_left 16 (Nat.coprime_two_left.2 hMo))
  have hs15 : sigma 1 (2 ^ 15 * M) = (∑ k ∈ Finset.range (15 + 1), 2 ^ k) * sigma 1 M :=
    P224832.sm 2 15 M Nat.prime_two (Nat.Coprime.pow_left 15 (Nat.coprime_two_left.2 hMo))
  have key : recipEven (2 ^ 16 * M) = 3 := by
    have htot := Finset.sum_filter_add_sum_filter_not (s := (2 ^ 16 * M).divisors)
      (p := fun d : ℕ => Even d) (f := fun d : ℕ => (1 : ℚ) / d)
    rw [P224832.oddf M 16 hMo, P224832.recip M hM0, P224832.recip _ (by positivity), hs16, hsM] at htot
    unfold recipEven
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at htot
    rw [hMdef] at htot
    norm_num at htot
    rw [hMdef]
    norm_num
    linarith
  have hnot : ¬ TwiceEvenPerfect (2 ^ 16 * M) := by
    rintro ⟨P, _, hP, hk⟩
    have hPM : P = 2 ^ 15 * M := by omega
    rw [hPM, Nat.perfect_iff_sum_divisors_eq_two_mul (by positivity), ← sigma_one_apply, hs15,
      hsM] at hP
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hP
    rw [hMdef] at hP
    norm_num at hP
  have hk := hc (2 ^ 16 * M) ⟨by positivity, ⟨2 ^ 15 * M, by ring⟩, ⟨3, by rw [key]; norm_num⟩⟩ hnot
  rw [key] at hk
  norm_num at hk
