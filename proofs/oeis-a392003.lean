import OMAStatements.S_oeis_a392003

-- Problem: A392003: a(n) = (7*2^n - 9 + 5*(-1)^n) / 6.
-- Upstream: formal-conjectures statements/oeis-a392003.lean:0 (declaration OMA.S_oeis_a392003.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: Prove by induction on n >= 1 the exact tape configuration of Rule 163 at generation n.
-- Deduce A266753 (n + 1) = 4 * A266753 n + 2 for n >= 1, hence 6 * A266753 n = 7 * 4^n - 4 = 6 * a (2*n).

open OMA.S_oeis_a392003 in
theorem OMA.solution : type_of% @OMA.S_oeis_a392003.main := by
  let tape : ℕ → ℤ → Bool := fun n i =>
    if i ≤ -(n : ℤ) then true
    else if i = -(n : ℤ) + 1 ∨ i = -(n : ℤ) + 2 then false
    else if i ≤ (n : ℤ) then decide ((i + (n : ℤ)) % 2 = 1)
    else true
  have htape_le : ∀ (m : ℕ) (i : ℤ), i ≤ -(m : ℤ) → tape m i = true := by
    intro m i h
    dsimp only [tape]
    exact if_pos h
  have htape_f : ∀ (m : ℕ) (i : ℤ), i = -(m : ℤ) + 1 ∨ i = -(m : ℤ) + 2 → tape m i = false := by
    intro m i h
    dsimp only [tape]
    rw [if_neg (by omega), if_pos h]
  have htape_mid : ∀ (m : ℕ) (i : ℤ), -(m : ℤ) + 3 ≤ i → i ≤ (m : ℤ) →
      tape m i = decide ((i + (m : ℤ)) % 2 = 1) := by
    intro m i h1 h2
    dsimp only [tape]
    rw [if_neg (by omega), if_neg (by omega), if_pos h2]
  have htape_gt : ∀ (m : ℕ) (i : ℤ), 1 ≤ m → (m : ℤ) < i → tape m i = true := by
    intro m i hm h
    dsimp only [tape]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hca : ∀ n : ℕ, 1 ≤ n → ∀ i : ℤ, ca163 n i = tape n i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro i
      change rule163 (i - 1 == 0) (i == 0) (i + 1 == 0) = tape 1 i
      by_cases h1 : i ≤ -1
      · rw [htape_le 1 i (by omega)]
        by_cases h2 : i = -1
        · subst h2
          decide
        · have hl : (i - 1 == 0) = false := beq_false_of_ne (by omega)
          have hc : (i == 0) = false := beq_false_of_ne (by omega)
          have hr : (i + 1 == 0) = false := beq_false_of_ne (by omega)
          rw [hl, hc, hr]
          rfl
      · by_cases h2 : i = 0
        · subst h2
          rw [htape_f 1 0 (Or.inl (by omega))]
          decide
        · by_cases h3 : i = 1
          · subst h3
            rw [htape_f 1 1 (Or.inr (by omega))]
            decide
          · rw [htape_gt 1 i le_rfl (by omega)]
            have hl : (i - 1 == 0) = false := beq_false_of_ne (by omega)
            have hc : (i == 0) = false := beq_false_of_ne (by omega)
            have hr : (i + 1 == 0) = false := beq_false_of_ne (by omega)
            rw [hl, hc, hr]
            rfl
    | succ m hm ih =>
      intro i
      change rule163 (ca163 m (i - 1)) (ca163 m i) (ca163 m (i + 1)) = tape (m + 1) i
      rw [ih (i - 1), ih i, ih (i + 1)]
      by_cases c1 : i ≤ -((m + 1 : ℕ) : ℤ)
      · rw [htape_le (m + 1) i c1, htape_le m (i - 1) (by omega),
          htape_le m i (by omega), htape_le m (i + 1) (by omega)]
        rfl
      · by_cases c2 : i = -((m + 1 : ℕ) : ℤ) + 1
        · rw [htape_f (m + 1) i (Or.inl c2), htape_le m (i - 1) (by omega),
            htape_le m i (by omega), htape_f m (i + 1) (Or.inl (by omega))]
          rfl
        · by_cases c3 : i = -((m + 1 : ℕ) : ℤ) + 2
          · rw [htape_f (m + 1) i (Or.inr c3), htape_le m (i - 1) (by omega),
              htape_f m i (Or.inl (by omega)), htape_f m (i + 1) (Or.inr (by omega))]
            rfl
          · by_cases c4 : i = -((m + 1 : ℕ) : ℤ) + 3
            · rw [htape_mid (m + 1) i (by omega) (by omega)]
              rw [htape_f m (i - 1) (Or.inl (by omega)), htape_f m i (Or.inr (by omega))]
              have hr : tape m (i + 1) = true := by
                by_cases hm1 : m = 1
                · exact htape_gt m (i + 1) hm (by omega)
                · rw [htape_mid m (i + 1) (by omega) (by omega)]
                  exact decide_eq_true (by omega)
              rw [hr, decide_eq_true (show (i + ((m + 1 : ℕ) : ℤ)) % 2 = 1 by omega)]
              rfl
            · by_cases c5 : i ≤ (m : ℤ) - 1
              · rw [htape_mid (m + 1) i (by omega) (by omega)]
                rw [htape_mid m i (by omega) (by omega), htape_mid m (i + 1) (by omega) (by omega)]
                by_cases c5a : i = -(m : ℤ) + 3
                · rw [htape_f m (i - 1) (Or.inr (by omega)),
                    decide_eq_true (show (i + (m : ℤ)) % 2 = 1 by omega),
                    decide_eq_false (show ¬((i + 1 + (m : ℤ)) % 2 = 1) by omega),
                    decide_eq_false (show ¬((i + ((m + 1 : ℕ) : ℤ)) % 2 = 1) by omega)]
                  rfl
                · rw [htape_mid m (i - 1) (by omega) (by omega)]
                  by_cases hpar : (i + (m : ℤ)) % 2 = 0
                  · rw [decide_eq_true (show (i - 1 + (m : ℤ)) % 2 = 1 by omega),
                      decide_eq_false (show ¬((i + (m : ℤ)) % 2 = 1) by omega),
                      decide_eq_true (show (i + 1 + (m : ℤ)) % 2 = 1 by omega),
                      decide_eq_true (show (i + ((m + 1 : ℕ) : ℤ)) % 2 = 1 by omega)]
                    rfl
                  · rw [decide_eq_false (show ¬((i - 1 + (m : ℤ)) % 2 = 1) by omega),
                      decide_eq_true (show (i + (m : ℤ)) % 2 = 1 by omega),
                      decide_eq_false (show ¬((i + 1 + (m : ℤ)) % 2 = 1) by omega),
                      decide_eq_false (show ¬((i + ((m + 1 : ℕ) : ℤ)) % 2 = 1) by omega)]
                    rfl
              · by_cases c6 : i = (m : ℤ)
                · rw [htape_mid (m + 1) i (by omega) (by omega),
                    htape_mid m (i - 1) (by omega) (by omega),
                    htape_mid m i (by omega) (by omega),
                    htape_gt m (i + 1) hm (by omega)]
                  rw [decide_eq_true (show (i - 1 + (m : ℤ)) % 2 = 1 by omega),
                    decide_eq_false (show ¬((i + (m : ℤ)) % 2 = 1) by omega),
                    decide_eq_true (show (i + ((m + 1 : ℕ) : ℤ)) % 2 = 1 by omega)]
                  rfl
                · by_cases c7 : i = ((m + 1 : ℕ) : ℤ)
                  · rw [htape_mid (m + 1) i (by omega) (by omega),
                      htape_gt m i hm (by omega), htape_gt m (i + 1) hm (by omega)]
                    have hl : tape m (i - 1) = false := by
                      by_cases hm1 : m = 1
                      · exact htape_f m (i - 1) (Or.inr (by omega))
                      · rw [htape_mid m (i - 1) (by omega) (by omega)]
                        exact decide_eq_false (by omega)
                    rw [hl, decide_eq_false (show ¬((i + ((m + 1 : ℕ) : ℤ)) % 2 = 1) by omega)]
                    rfl
                  · rw [htape_gt (m + 1) i (by omega) (by omega),
                      htape_gt m (i - 1) hm (by omega),
                      htape_gt m i hm (by omega),
                      htape_gt m (i + 1) hm (by omega)]
                    rfl
  have hbit : ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, k ≤ 2 * n →
      ca163 n ((k : ℤ) - (n : ℤ)) =
        (if k = 0 then true else if k = 1 ∨ k = 2 then false else decide (k % 2 = 1)) := by
    intro n hn k hk
    rw [hca n hn]
    by_cases h0 : k = 0
    · subst h0
      rw [if_pos rfl]
      exact htape_le n ((0 : ℕ) - (n : ℤ)) (by omega)
    · rw [if_neg h0]
      by_cases h12 : k = 1 ∨ k = 2
      · rw [if_pos h12]
        exact htape_f n ((k : ℤ) - (n : ℤ)) (by omega)
      · rw [if_neg h12, htape_mid n ((k : ℤ) - (n : ℤ)) (by omega) (by omega)]
        have hmod : (((k : ℤ) - (n : ℤ) + (n : ℤ)) % 2 = 1) ↔ (k % 2 = 1) := by omega
        exact decide_eq_decide.mpr hmod
  have hrec : ∀ n : ℕ, 1 ≤ n → A266753 (n + 1) = 4 * A266753 n + 2 := by
    intro n hn
    unfold A266753
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hb1 : ca163 (n + 1) (((2 * n + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) = true := by
      rw [hbit (n + 1) (by omega) (2 * n + 1) (by omega)]
      rw [if_neg (by omega), if_neg (by omega)]
      exact decide_eq_true (by omega)
    have hb2 : ca163 (n + 1) ((((2 * n + 1) + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) = false := by
      rw [hbit (n + 1) (by omega) ((2 * n + 1) + 1) (by omega)]
      rw [if_neg (by omega), if_neg (by omega)]
      exact decide_eq_false (by omega)
    rw [hb1, hb2]
    have hsum : ∑ k ∈ Finset.range (2 * n + 1),
        (if ca163 (n + 1) ((k : ℤ) - ((n + 1 : ℕ) : ℤ)) then 1 else 0) * 2 ^ (2 * (n + 1) - k) =
        4 * ∑ k ∈ Finset.range (2 * n + 1),
        (if ca163 n ((k : ℤ) - (n : ℤ)) then 1 else 0) * 2 ^ (2 * n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ 2 * n := by
        have := Finset.mem_range.mp hk
        omega
      rw [hbit (n + 1) (by omega) k (by omega), hbit n hn k hk']
      have hexp : 2 ^ (2 * (n + 1) - k) = 4 * 2 ^ (2 * n - k) := by
        rw [show 2 * (n + 1) - k = (2 * n - k) + 2 by omega, pow_add]
        ring
      rw [hexp]
      ring
    rw [hsum]
    have e1 : 2 * (n + 1) - (2 * n + 1) = 1 := by omega
    have e2 : 2 * (n + 1) - ((2 * n + 1) + 1) = 0 := by omega
    rw [e1, e2]
    simp
  have hclosed : ∀ n : ℕ, 1 ≤ n → 6 * (A266753 n : ℤ) = 7 * (4 : ℤ) ^ n - 4 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have h1 : A266753 1 = 4 := by decide
      rw [h1]
      norm_num
    | succ m hm ih =>
      have hr : (A266753 (m + 1) : ℤ) = 4 * (A266753 m : ℤ) + 2 := by
        exact_mod_cast hrec m hm
      rw [hr, pow_succ]
      linarith
  intro n hn
  unfold a
  have hpow1 : (2 : ℤ) ^ (2 * n) = (4 : ℤ) ^ n := by
    rw [pow_mul]
    norm_num
  have hpow2 : (-1 : ℤ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [hpow1, hpow2]
  have hc := hclosed n hn
  have hnum : 7 * (4 : ℤ) ^ n - 9 + 5 * 1 = (A266753 n : ℤ) * 6 := by linarith
  rw [hnum]
  exact Int.mul_ediv_cancel (A266753 n : ℤ) (by norm_num)
