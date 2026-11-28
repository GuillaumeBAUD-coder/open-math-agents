import OMAStatements.S_oeis_a387426

-- Problem: A387426: Numbers k such that all nonzero fractions (2*k mod m)/m (for 1 <= m <= k) are distinct.
-- Upstream: formal-conjectures statements/oeis-a387426.lean:0 (declaration OMA.S_oeis_a387426.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for a prime p and 3 <= a < b < p with equal fractions, a*b*(q1-q2) = 2p(b-a), so p divides
-- q1-q2 and a*b*t = 2(b-a), impossible. For a composite k > 24 two m give equal nonzero fractions:
-- (2A, 2Ax) when 2k = A*x*y with x, y odd, x >= 3, y >= 4 (both fractions 1/2); (3B, 12B) when k = B*t,
-- t even, t >= 12, 3 not dividing t (both fractions (2t mod 3)/3); (5, 30) for k = 36 and k = 72.

open OMA.S_oeis_a387426 in
theorem OMA.solution : type_of% @OMA.S_oeis_a387426.main := by
  have refute : ∀ k m m' : ℕ, 1 ≤ m → m ≤ k → 1 ≤ m' → m' ≤ k → m ≠ m' → 2 * k % m ≠ 0 →
      2 * k % m' ≠ 0 →
      ((2 * k % m : ℕ) : ℚ) / (m : ℚ) = ((2 * k % m' : ℕ) : ℚ) / (m' : ℚ) → ¬ InSeq k := by
    intro k m m' h1 h2 h3 h4 hne hr hr' heq hin
    have hm : m ∈ {m : ℕ | 1 ≤ m ∧ m ≤ k ∧ 2 * k % m ≠ 0} :=
      show 1 ≤ m ∧ m ≤ k ∧ 2 * k % m ≠ 0 from ⟨h1, h2, hr⟩
    have hm' : m' ∈ {m : ℕ | 1 ≤ m ∧ m ≤ k ∧ 2 * k % m ≠ 0} :=
      show 1 ≤ m' ∧ m' ≤ k ∧ 2 * k % m' ≠ 0 from ⟨h3, h4, hr'⟩
    exact hne (hin hm hm' heq)
  have H : ∀ k A x y : ℕ, 2 * k = A * (x * y) → 0 < A → x % 2 = 1 → y % 2 = 1 → 3 ≤ x → 4 ≤ y →
      ¬ InSeq k := by
    intro k A x y hk hA hx hy hx3 hy4
    have hxy : x * y % 2 = 1 := by rw [Nat.mul_mod, hx, hy]
    have e1 : 2 * k % (A * 2) = A := by
      rw [hk, Nat.mul_mod_mul_left, hxy, mul_one]
    have e2 : 2 * k % (A * x * 2) = A * x := by
      rw [hk, ← mul_assoc, Nat.mul_mod_mul_left, hy, mul_one]
    have hAx : 0 < A * x := Nat.mul_pos hA (by omega)
    have hc1 : A * (3 * 4) ≤ A * (x * y) := Nat.mul_le_mul_left A (Nat.mul_le_mul hx3 hy4)
    have hc2 : A * x * 4 ≤ 2 * k := by
      rw [hk, ← mul_assoc]
      exact Nat.mul_le_mul_left (A * x) hy4
    have hc3 : A * 3 ≤ A * x := Nat.mul_le_mul_left A hx3
    refine refute k (A * 2) (A * x * 2) (by omega) (by omega) (by omega) (by omega) (by omega)
      ?_ ?_ ?_
    · rw [e1]
      omega
    · rw [e2]
      omega
    · rw [e1, e2]
      have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
      have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
      have hd1 : (A : ℚ) * 2 ≠ 0 := mul_ne_zero hAq two_ne_zero
      have hd2 : (A : ℚ) * x * 2 ≠ 0 := mul_ne_zero (mul_ne_zero hAq hxq) two_ne_zero
      push_cast
      rw [div_eq_div_iff hd1 hd2]
      ring
  have T : ∀ k B t : ℕ, k = B * t → 0 < B → ¬ 3 ∣ t → t % 2 = 0 → 12 ≤ t → ¬ InSeq k := by
    intro k B t hk hB ht3 ht2 ht12
    have e0 : 2 * k = B * (2 * t) := by
      rw [hk]
      ring
    have e1 : 2 * k % (B * 3) = B * (2 * t % 3) := by
      rw [e0, Nat.mul_mod_mul_left]
    have e2 : 2 * k % (B * 12) = B * (4 * (2 * t % 3)) := by
      rw [e0, Nat.mul_mod_mul_left]
      congr 1
      omega
    have hr : 2 * t % 3 ≠ 0 := by omega
    have hb1 : B * 3 ≤ k := by
      rw [hk]
      exact Nat.mul_le_mul_left B (by omega)
    have hb2 : B * 12 ≤ k := by
      rw [hk]
      exact Nat.mul_le_mul_left B ht12
    refine refute k (B * 3) (B * 12) (by omega) hb1 (by omega) hb2 (by omega) ?_ ?_ ?_
    · rw [e1]
      exact mul_ne_zero hB.ne' hr
    · rw [e2]
      exact mul_ne_zero hB.ne' (by omega)
    · rw [e1, e2]
      have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
      have hd1 : (B : ℚ) * 3 ≠ 0 := mul_ne_zero hBq (by norm_num)
      have hd2 : (B : ℚ) * 12 ≠ 0 := mul_ne_zero hBq (by norm_num)
      push_cast
      rw [div_eq_div_iff hd1 hd2]
      ring
  have aux : ∀ p a b q1 q2 r1 r2 : ℕ, p.Prime → 3 ≤ a → a < b → b < p →
      a * q1 + r1 = 2 * p → b * q2 + r2 = 2 * p → r1 * b = r2 * a → False := by
    intro p a b q1 q2 r1 r2 hp ha hab hbp E1 E2 E3
    have Z1 : (a : ℤ) * q1 + r1 = 2 * p := by exact_mod_cast E1
    have Z2 : (b : ℤ) * q2 + r2 = 2 * p := by exact_mod_cast E2
    have Z3 : (r1 : ℤ) * b = r2 * a := by exact_mod_cast E3
    have hZ : (a : ℤ) * b * ((q1 : ℤ) - q2) = (p : ℤ) * (2 * ((b : ℤ) - a)) := by
      linear_combination (b : ℤ) * Z1 - (a : ℤ) * Z2 - Z3
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpa : ¬ (p : ℤ) ∣ (a : ℤ) := by
      intro h
      have h' : p ∣ a := Int.natCast_dvd_natCast.mp h
      have := Nat.le_of_dvd (by omega) h'
      omega
    have hpb : ¬ (p : ℤ) ∣ (b : ℤ) := by
      intro h
      have h' : p ∣ b := Int.natCast_dvd_natCast.mp h
      have := Nat.le_of_dvd (by omega) h'
      omega
    have hdvd : (p : ℤ) ∣ (a : ℤ) * b * ((q1 : ℤ) - q2) := Dvd.intro _ hZ.symm
    obtain ⟨t, ht⟩ : (p : ℤ) ∣ ((q1 : ℤ) - q2) := by
      rcases hpZ.dvd_or_dvd hdvd with h | h
      · rcases hpZ.dvd_or_dvd h with h' | h'
        · exact absurd h' hpa
        · exact absurd h' hpb
      · exact h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hk : (a : ℤ) * b * t = 2 * ((b : ℤ) - a) := by
      apply mul_left_cancel₀ hp0
      rw [ht] at hZ
      linear_combination hZ
    have ha3 : (3 : ℤ) ≤ a := by exact_mod_cast ha
    have hab' : (a : ℤ) < b := by exact_mod_cast hab
    have hab0 : (0 : ℤ) ≤ (a : ℤ) * b := by positivity
    rcases le_or_gt t 0 with ht0 | ht0
    · have h1 : 0 ≤ (a : ℤ) * b * (-t) := mul_nonneg hab0 (by linarith)
      linarith
    · have h1 : (a : ℤ) * b * 1 ≤ (a : ℤ) * b * t := mul_le_mul_of_nonneg_left (by omega) hab0
      have h2 : (3 : ℤ) * b ≤ (a : ℤ) * b := mul_le_mul_of_nonneg_right ha3 (by positivity)
      linarith
  refine ⟨?_, ?_⟩
  · intro p hp
    have keyp : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ p → 2 * p % a ≠ 0 → 2 * p % b ≠ 0 →
        2 * p % a * b = 2 * p % b * a → False := by
      intro a b ha hab hbp hra hrb hc
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hra (Nat.mod_one _)
      have ha2 : a ≠ 2 := by
        rintro rfl
        omega
      have hbp' : b ≠ p := by
        rintro rfl
        exact hrb (by simp)
      exact aux p a b (2 * p / a) (2 * p / b) (2 * p % a) (2 * p % b) hp (by omega) hab (by omega)
        (Nat.div_add_mod (2 * p) a) (Nat.div_add_mod (2 * p) b) hc
    unfold InSeq
    intro m₁ hm₁ m₂ hm₂ heq
    have hm₁' : 1 ≤ m₁ ∧ m₁ ≤ p ∧ 2 * p % m₁ ≠ 0 := hm₁
    have hm₂' : 1 ≤ m₂ ∧ m₂ ≤ p ∧ 2 * p % m₂ ≠ 0 := hm₂
    have heq' : ((2 * p % m₁ : ℕ) : ℚ) / (m₁ : ℚ) = ((2 * p % m₂ : ℕ) : ℚ) / (m₂ : ℚ) := heq
    have hq1 : (m₁ : ℚ) ≠ 0 := by exact_mod_cast (show m₁ ≠ 0 by omega)
    have hq2 : (m₂ : ℚ) ≠ 0 := by exact_mod_cast (show m₂ ≠ 0 by omega)
    rw [div_eq_div_iff hq1 hq2] at heq'
    have hc : 2 * p % m₁ * m₂ = 2 * p % m₂ * m₁ := by exact_mod_cast heq'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact keyp m₁ m₂ hm₁'.1 hlt hm₂'.2.1 hm₁'.2.2 hm₂'.2.2 hc
    · exact keyp m₂ m₁ hm₂'.1 hlt hm₁'.2.1 hm₂'.2.2 hm₁'.2.2 hc.symm
  · intro k hk hnp
    have hk0 : k ≠ 0 := by omega
    obtain ⟨w, t, ht3, hkt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 3 (by norm_num)
    have hB : 0 < 3 ^ w := by positivity
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hkt
      omega
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | hodd
    · by_cases h12 : 12 ≤ t
      · exact T k (3 ^ w) t hkt hB ht3 (by omega) h12
      · have hcases : t = 2 ∨ t = 4 ∨ t = 8 ∨ t = 10 := by omega
        rcases hcases with rfl | rfl | rfl | rfl
        · have hw : 3 ≤ w := by
            by_contra hw
            have h9 : 3 ^ w ≤ 9 := by
              calc 3 ^ w ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 9 := by norm_num
            omega
          obtain ⟨u, rfl⟩ : ∃ u, w = u + 3 := ⟨w - 3, by omega⟩
          have hU := Nat.one_le_pow u 3 (by norm_num)
          exact H k 4 3 (9 * 3 ^ u) (by subst hkt; ring) (by norm_num) (by norm_num)
            (Nat.odd_iff.mp (Odd.mul ⟨4, rfl⟩ (Odd.pow ⟨1, rfl⟩))) le_rfl (by omega)
        · have hw : 2 ≤ w := by
            by_contra hw
            have h3 : 3 ^ w ≤ 3 := by
              calc 3 ^ w ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 3 := by norm_num
            omega
          rcases Nat.lt_or_ge w 3 with hw3 | hw3
          · have hw2 : w = 2 := by omega
            subst hw2
            have hk36 : k = 36 := by norm_num [hkt]
            subst hk36
            exact refute 36 5 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          · obtain ⟨u, rfl⟩ : ∃ u, w = u + 3 := ⟨w - 3, by omega⟩
            have hU := Nat.one_le_pow u 3 (by norm_num)
            exact H k 8 3 (9 * 3 ^ u) (by subst hkt; ring) (by norm_num) (by norm_num)
              (Nat.odd_iff.mp (Odd.mul ⟨4, rfl⟩ (Odd.pow ⟨1, rfl⟩))) le_rfl (by omega)
        · have hw : 2 ≤ w := by
            by_contra hw
            have h3 : 3 ^ w ≤ 3 := by
              calc 3 ^ w ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 3 := by norm_num
            omega
          rcases Nat.lt_or_ge w 3 with hw3 | hw3
          · have hw2 : w = 2 := by omega
            subst hw2
            have hk72 : k = 72 := by norm_num [hkt]
            subst hk72
            exact refute 72 5 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          · obtain ⟨u, rfl⟩ : ∃ u, w = u + 3 := ⟨w - 3, by omega⟩
            have hU := Nat.one_le_pow u 3 (by norm_num)
            exact H k 16 3 (9 * 3 ^ u) (by subst hkt; ring) (by norm_num) (by norm_num)
              (Nat.odd_iff.mp (Odd.mul ⟨4, rfl⟩ (Odd.pow ⟨1, rfl⟩))) le_rfl (by omega)
        · have hw : 1 ≤ w := by
            by_contra hw
            have hw0 : w = 0 := by omega
            subst hw0
            rw [pow_zero, one_mul] at hkt
            omega
          obtain ⟨u, rfl⟩ : ∃ u, w = u + 1 := ⟨w - 1, by omega⟩
          have hU := Nat.one_le_pow u 3 (by norm_num)
          exact H k 4 3 (5 * 3 ^ u) (by subst hkt; ring) (by norm_num) (by norm_num)
            (Nat.odd_iff.mp (Odd.mul ⟨2, rfl⟩ (Odd.pow ⟨1, rfl⟩))) le_rfl (by omega)
    · have hko : k % 2 = 1 := by
        rw [hkt]
        exact Nat.odd_iff.mp (Odd.mul (Odd.pow ⟨1, rfl⟩) hodd)
      obtain ⟨d, ⟨e, hde⟩, hd2, hdk⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 2 ≤ k) hnp
      have hdo : d % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one d with h | h
        · rw [hde, Nat.mul_mod, h, zero_mul, Nat.zero_mod] at hko
          omega
        · exact h
      have heo : e % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one e with h | h
        · rw [hde, Nat.mul_mod, h, mul_zero, Nat.zero_mod] at hko
          omega
        · exact h
      have he2 : 2 ≤ e := by
        rcases Nat.lt_or_ge e 2 with h | h
        · interval_cases e <;> omega
        · exact h
      rcases Nat.lt_or_ge e 4 with he4 | he4
      · have he3 : e = 3 := by omega
        subst he3
        exact H k 2 3 d (by omega) (by norm_num) (by norm_num) hdo le_rfl (by omega)
      · exact H k 2 d e (by rw [hde]) (by norm_num) hdo heo (by omega) he4