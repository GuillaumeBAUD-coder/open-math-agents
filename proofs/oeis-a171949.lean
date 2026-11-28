import OMAStatements.S_oeis_a171949

open OMA.S_oeis_a171949

namespace OMA.P_oeis_a171949

lemma not_trailing_of_not_dvd {n : ℕ} (h : ¬ 4 ∣ n) : ¬ trailing n := by
  rintro ⟨hn, hv⟩
  apply h
  have h2 : 2 ≤ n.factorization 2 := by omega
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega : n ≠ 0)).2 h2
  simpa using h4

lemma v_four_mul {q : ℕ} (hq : q ≠ 0) : (4 * q).factorization 2 = q.factorization 2 + 2 := by
  rw [Nat.factorization_mul (by norm_num) hq, Finsupp.add_apply]
  have h4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  rw [h4]
  omega

lemma losing_iff (n : ℕ) : losing n ↔ (n = 0 ∨ trailing n) := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rw [losing]
  constructor
  · intro hL
    by_contra hP
    have hn0 : n ≠ 0 := fun h => hP (Or.inl h)
    have hnt : ¬ trailing n := fun h => hP (Or.inr h)
    obtain ⟨m, hmn, hmove, hPm⟩ : ∃ m, m < n ∧ (n ≤ m + 3 ∨ m = n / 4) ∧ (m = 0 ∨ trailing m) := by
      by_cases h3 : n ≤ 3
      · exact ⟨0, by omega, Or.inl (by omega), Or.inl rfl⟩
      · by_cases h4 : 4 ∣ n
        · obtain ⟨q, hq⟩ := h4
          have hq0 : q ≠ 0 := by omega
          have hv := v_four_mul hq0
          refine ⟨q, by omega, Or.inr (by omega), Or.inr ⟨by omega, ?_⟩⟩
          have hnt' : ¬ (0 < 4 * q ∧ 2 ≤ (4 * q).factorization 2 % 4) := by
            rw [← hq]; exact hnt
          omega
        · have hm0 : 4 ∣ n - n % 4 := by omega
          by_cases ht : trailing (n - n % 4)
          · exact ⟨n - n % 4, by omega, Or.inl (by omega), Or.inr ht⟩
          · obtain ⟨q, hq⟩ := hm0
            have hq0 : q ≠ 0 := by omega
            have hv := v_four_mul hq0
            refine ⟨q, by omega, Or.inr (by omega), Or.inr ⟨by omega, ?_⟩⟩
            have ht' : ¬ (0 < 4 * q ∧ 2 ≤ (4 * q).factorization 2 % 4) := by
              rw [← hq]; exact ht
            omega
    exact hL m hmn hmove ((ih m hmn).2 hPm)
  · intro hP m hmn hmove hLm
    have hPm := (ih m hmn).1 hLm
    rcases hP with h0 | ⟨hn, hvn⟩
    · omega
    · have h4 : 4 ∣ n := by
        by_contra h
        exact not_trailing_of_not_dvd h ⟨hn, hvn⟩
      obtain ⟨q, hq⟩ := h4
      have hq0 : q ≠ 0 := by omega
      have hv := v_four_mul hq0
      rw [hq] at hvn
      rcases hmove with hle | heq
      · rcases hPm with h0 | hmt
        · omega
        · exact not_trailing_of_not_dvd (by omega) hmt
      · have hmq : m = q := by omega
        rw [hmq] at hPm
        rcases hPm with h0 | ⟨_, hvm⟩
        · omega
        · omega

lemma count_shift [DecidablePred losing] [DecidablePred trailing] (x : ℕ) :
    Nat.count losing (x + 1) = Nat.count trailing (x + 1) + 1 := by
  induction x with
  | zero =>
    have h0 : losing 0 := (losing_iff 0).2 (Or.inl rfl)
    have h1 : ¬ trailing 0 := fun h => by have := h.1; omega
    rw [Nat.count_succ (p := losing) (n := 0), Nat.count_succ (p := trailing) (n := 0),
      Nat.count_zero, Nat.count_zero, if_pos h0, if_neg h1]
    all_goals simp
  | succ x ih =>
    rw [Nat.count_succ (p := losing) (n := x + 1), ih, Nat.count_succ (p := trailing) (n := x + 1)]
    have hiff : losing (x + 1) ↔ trailing (x + 1) := by
      rw [losing_iff]
      constructor
      · intro hl
        rcases hl with h0 | ht
        · omega
        · exact ht
      · exact Or.inr
    by_cases h : trailing (x + 1)
    · simp [h, hiff.2 h]
    · simp [h, mt hiff.1 h]

lemma trailing_four (j : ℕ) : trailing (4 * (2 * j + 1)) := by
  refine ⟨by omega, ?_⟩
  have h2 := v_four_mul (q := 2 * j + 1) (by omega)
  have h0 : (2 * j + 1).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    omega
  omega

lemma trailing_infinite : (setOf trailing).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hle : 4 * (2 * B + 1) ≤ B := hB (trailing_four B)
  omega

end OMA.P_oeis_a171949

open OMA.P_oeis_a171949 in
theorem OMA.solution : type_of% @OMA.S_oeis_a171949.main := by
  classical
  intro k
  have ht := Nat.nth_mem_of_infinite (p := trailing) trailing_infinite k
  have hc := Nat.count_nth_of_infinite (p := trailing) trailing_infinite k
  have ht0 : 0 < Nat.nth trailing k := ht.1
  have hlt : losing (Nat.nth trailing k) := (losing_iff _).2 (Or.inr ht)
  have hcl : Nat.count losing (Nat.nth trailing k) = k + 1 := by
    obtain ⟨s, hs⟩ : ∃ s, Nat.nth trailing k = s + 1 := ⟨Nat.nth trailing k - 1, by omega⟩
    rw [hs, count_shift, ← hs, hc]
  calc Nat.nth losing (k + 1)
      = Nat.nth losing (Nat.count losing (Nat.nth trailing k)) := by rw [hcl]
    _ = Nat.nth trailing k := Nat.nth_count (p := losing) hlt
