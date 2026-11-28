import OMAReductions.R_opg_strange_series_R1

/-!
# Proof of `opg-strange-series.R1.H1`

Proves finite Collatz stopping time (`∃ k, f^[k] n < n`) for every `n > 1` whose residue modulo
`32` is not in `{7, 15, 27, 31}`:
- Even `n`: `f n = n / 2 < n` (`k = 1`).
- `n % 4 = 1`: `f^[3] (4a + 1) = 3a + 1 < 4a + 1` (`k = 3`).
- `n % 16 = 3`: `f^[6] (16a + 3) = 9a + 2 < 16a + 3` (`k = 6`).
- `n % 32 = 11`: `f^[8] (32b + 11) = 27b + 10 < 32b + 11` (`k = 8`).
- `n % 32 = 23`: `f^[8] (32b + 23) = 27b + 20 < 32b + 23` (`k = 8`).
-/

namespace OpgStrangeSeriesR1H1Proof

open OMA.S_opg_strange_series

private lemma f_even {m : ℕ} (hm : 0 < m) : f (2 * m) = m := by
  unfold f
  rw [if_neg (by omega), if_neg (by omega)]
  omega

private lemma f_odd {m : ℕ} (hm : 0 < m) : f (2 * m + 1) = 6 * m + 4 := by
  unfold f
  rw [if_neg (by omega), if_pos (by omega)]
  omega

end OpgStrangeSeriesR1H1Proof

theorem OMA.solution : OMA.R_opg_strange_series_R1.H1 := by
  intro n hn h7 h15 h27 h31
  open OMA.S_opg_strange_series in
  by_cases h2 : n % 2 = 0
  · refine ⟨1, ?_⟩
    simp only [Function.iterate_one]
    have hm : n = 2 * (n / 2) := by omega
    rw [hm, OpgStrangeSeriesR1H1Proof.f_even (by omega)]
    omega
  · by_cases h4 : n % 4 = 1
    · refine ⟨3, ?_⟩
      obtain ⟨a, ha⟩ : ∃ a, n = 4 * a + 1 := ⟨n / 4, by omega⟩
      have ha1 : 1 ≤ a := by omega
      rw [ha]
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      have s1 : f (4 * a + 1) = 12 * a + 4 := by
        simpa [show 2 * (2 * a) + 1 = 4 * a + 1 by omega, show 6 * (2 * a) + 4 = 12 * a + 4 by omega] using
          OpgStrangeSeriesR1H1Proof.f_odd (m := 2 * a) (by omega)
      have s2 : f (12 * a + 4) = 6 * a + 2 := by
        simpa [show 2 * (6 * a + 2) = 12 * a + 4 by omega] using
          OpgStrangeSeriesR1H1Proof.f_even (m := 6 * a + 2) (by omega)
      have s3 : f (6 * a + 2) = 3 * a + 1 := by
        simpa [show 2 * (3 * a + 1) = 6 * a + 2 by omega] using
          OpgStrangeSeriesR1H1Proof.f_even (m := 3 * a + 1) (by omega)
      rw [s1, s2, s3]
      omega
    · by_cases h16 : n % 16 = 3
      · refine ⟨6, ?_⟩
        obtain ⟨a, ha⟩ : ∃ a, n = 16 * a + 3 := ⟨n / 16, by omega⟩
        rw [ha]
        simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
        have s1 : f (16 * a + 3) = 48 * a + 10 := by
          simpa [show 2 * (8 * a + 1) + 1 = 16 * a + 3 by omega, show 6 * (8 * a + 1) + 4 = 48 * a + 10 by omega] using
            OpgStrangeSeriesR1H1Proof.f_odd (m := 8 * a + 1) (by omega)
        have s2 : f (48 * a + 10) = 24 * a + 5 := by
          simpa [show 2 * (24 * a + 5) = 48 * a + 10 by omega] using
            OpgStrangeSeriesR1H1Proof.f_even (m := 24 * a + 5) (by omega)
        have s3 : f (24 * a + 5) = 72 * a + 16 := by
          simpa [show 2 * (12 * a + 2) + 1 = 24 * a + 5 by omega, show 6 * (12 * a + 2) + 4 = 72 * a + 16 by omega] using
            OpgStrangeSeriesR1H1Proof.f_odd (m := 12 * a + 2) (by omega)
        have s4 : f (72 * a + 16) = 36 * a + 8 := by
          simpa [show 2 * (36 * a + 8) = 72 * a + 16 by omega] using
            OpgStrangeSeriesR1H1Proof.f_even (m := 36 * a + 8) (by omega)
        have s5 : f (36 * a + 8) = 18 * a + 4 := by
          simpa [show 2 * (18 * a + 4) = 36 * a + 8 by omega] using
            OpgStrangeSeriesR1H1Proof.f_even (m := 18 * a + 4) (by omega)
        have s6 : f (18 * a + 4) = 9 * a + 2 := by
          simpa [show 2 * (9 * a + 2) = 18 * a + 4 by omega] using
            OpgStrangeSeriesR1H1Proof.f_even (m := 9 * a + 2) (by omega)
        rw [s1, s2, s3, s4, s5, s6]
        omega
      · by_cases h11 : n % 32 = 11
        · refine ⟨8, ?_⟩
          obtain ⟨b, hb⟩ : ∃ b, n = 32 * b + 11 := ⟨n / 32, by omega⟩
          rw [hb]
          simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
          have s1 : f (32 * b + 11) = 96 * b + 34 := by
            simpa [show 2 * (16 * b + 5) + 1 = 32 * b + 11 by omega, show 6 * (16 * b + 5) + 4 = 96 * b + 34 by omega] using
              OpgStrangeSeriesR1H1Proof.f_odd (m := 16 * b + 5) (by omega)
          have s2 : f (96 * b + 34) = 48 * b + 17 := by
            simpa [show 2 * (48 * b + 17) = 96 * b + 34 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 48 * b + 17) (by omega)
          have s3 : f (48 * b + 17) = 144 * b + 52 := by
            simpa [show 2 * (24 * b + 8) + 1 = 48 * b + 17 by omega, show 6 * (24 * b + 8) + 4 = 144 * b + 52 by omega] using
              OpgStrangeSeriesR1H1Proof.f_odd (m := 24 * b + 8) (by omega)
          have s4 : f (144 * b + 52) = 72 * b + 26 := by
            simpa [show 2 * (72 * b + 26) = 144 * b + 52 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 72 * b + 26) (by omega)
          have s5 : f (72 * b + 26) = 36 * b + 13 := by
            simpa [show 2 * (36 * b + 13) = 72 * b + 26 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 36 * b + 13) (by omega)
          have s6 : f (36 * b + 13) = 108 * b + 40 := by
            simpa [show 2 * (18 * b + 6) + 1 = 36 * b + 13 by omega, show 6 * (18 * b + 6) + 4 = 108 * b + 40 by omega] using
              OpgStrangeSeriesR1H1Proof.f_odd (m := 18 * b + 6) (by omega)
          have s7 : f (108 * b + 40) = 54 * b + 20 := by
            simpa [show 2 * (54 * b + 20) = 108 * b + 40 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 54 * b + 20) (by omega)
          have s8 : f (54 * b + 20) = 27 * b + 10 := by
            simpa [show 2 * (27 * b + 10) = 54 * b + 20 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 27 * b + 10) (by omega)
          rw [s1, s2, s3, s4, s5, s6, s7, s8]
          omega
        · have h23 : n % 32 = 23 := by omega
          refine ⟨8, ?_⟩
          obtain ⟨b, hb⟩ : ∃ b, n = 32 * b + 23 := ⟨n / 32, by omega⟩
          rw [hb]
          simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
          have s1 : f (32 * b + 23) = 96 * b + 70 := by
            simpa [show 2 * (16 * b + 11) + 1 = 32 * b + 23 by omega, show 6 * (16 * b + 11) + 4 = 96 * b + 70 by omega] using
              OpgStrangeSeriesR1H1Proof.f_odd (m := 16 * b + 11) (by omega)
          have s2 : f (96 * b + 70) = 48 * b + 35 := by
            simpa [show 2 * (48 * b + 35) = 96 * b + 70 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 48 * b + 35) (by omega)
          have s3 : f (48 * b + 35) = 144 * b + 106 := by
            simpa [show 2 * (24 * b + 17) + 1 = 48 * b + 35 by omega, show 6 * (24 * b + 17) + 4 = 144 * b + 106 by omega] using
              OpgStrangeSeriesR1H1Proof.f_odd (m := 24 * b + 17) (by omega)
          have s4 : f (144 * b + 106) = 72 * b + 53 := by
            simpa [show 2 * (72 * b + 53) = 144 * b + 106 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 72 * b + 53) (by omega)
          have s5 : f (72 * b + 53) = 216 * b + 160 := by
            simpa [show 2 * (36 * b + 26) + 1 = 72 * b + 53 by omega, show 6 * (36 * b + 26) + 4 = 216 * b + 160 by omega] using
              OpgStrangeSeriesR1H1Proof.f_odd (m := 36 * b + 26) (by omega)
          have s6 : f (216 * b + 160) = 108 * b + 80 := by
            simpa [show 2 * (108 * b + 80) = 216 * b + 160 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 108 * b + 80) (by omega)
          have s7 : f (108 * b + 80) = 54 * b + 40 := by
            simpa [show 2 * (54 * b + 40) = 108 * b + 80 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 54 * b + 40) (by omega)
          have s8 : f (54 * b + 40) = 27 * b + 20 := by
            simpa [show 2 * (27 * b + 20) = 54 * b + 40 by omega] using
              OpgStrangeSeriesR1H1Proof.f_even (m := 27 * b + 20) (by omega)
          rw [s1, s2, s3, s4, s5, s6, s7, s8]
          omega
