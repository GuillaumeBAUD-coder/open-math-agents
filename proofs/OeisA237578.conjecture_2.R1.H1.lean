import OMAReductions.R_OeisA237578_conjecture_2_R1

-- Step OeisA237578.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA237578.conjecture_2.R1
-- Credit: @green-notes
-- H1 := ∀ n : ℕ, (n = 5 ∨ n = 8 ∨ n = 13) → OeisA237578.a n = 1

def primeLe168 (n : ℕ) : Bool :=
  n == 2 || n == 3 || n == 5 || n == 7 || n == 11 ||
    (1 < n && n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0 && n % 11 != 0)

def piFast (m : ℕ) : ℕ :=
  (List.range (m + 1)).countP primeLe168

lemma prime_iff_primeLe168 {n : ℕ} (hn : n ≤ 168) :
    n.Prime ↔ primeLe168 n = true := by
  constructor
  · intro hp
    by_cases h : n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11
    · rcases h with rfl | rfl | rfl | rfl | rfl <;> decide
    · have h1 : 1 < n := hp.one_lt
      have hdvd : ∀ p : ℕ, p.Prime → p ≠ n → n % p ≠ 0 := by
        intro p hp' hne hmod
        have : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
        rcases hp.eq_one_or_self_of_dvd p this with rfl | rfl
        · exact hp'.ne_one rfl
        · exact hne rfl
      have h2 := hdvd 2 (by decide) (by omega)
      have h3 := hdvd 3 (by decide) (by omega)
      have h5 := hdvd 5 (by decide) (by omega)
      have h7 := hdvd 7 (by decide) (by omega)
      have h11 := hdvd 11 (by decide) (by omega)
      simp only [primeLe168, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
        decide_eq_true_eq]
      omega
  · intro hb
    simp only [primeLe168, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      decide_eq_true_eq] at hb
    rcases hb with ((((rfl | rfl) | rfl) | rfl) | rfl) | ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h7⟩, h11⟩
    · decide
    · decide
    · decide
    · decide
    · decide
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨h1, fun m hm2 hms hdvd => ?_⟩
      have hm2sq : m * m ≤ 168 := (Nat.le_sqrt.mp hms).trans hn
      have hm12 : m ≤ 12 := by nlinarith
      obtain ⟨k, rfl⟩ := hdvd
      interval_cases m <;> omega

lemma primeCounting_eq_piFast {m : ℕ} (hm : m ≤ 167) :
    Nat.primeCounting m = piFast m := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count, piFast]
  refine List.countP_congr fun x hx => ?_
  rw [List.mem_range] at hx
  have hxn : x ≤ 168 := by omega
  simp [prime_iff_primeLe168 hxn]

lemma a_eq_fast {n : ℕ} (hn : n ≤ 13) :
    OeisA237578.a n = ∑ k ∈ Finset.Ico 1 n, if primeLe168 (piFast (k * n)) = true then 1 else 0 := by
  rw [OeisA237578.a]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_lt : k < n := (Finset.mem_Ico.mp hk).2
  have hk_le : k ≤ 12 := by omega
  have hm : k * n ≤ 167 := by nlinarith
  have hpi_le : piFast (k * n) ≤ 168 := by
    have : piFast (k * n) ≤ (List.range (k * n + 1)).length := List.countP_le_length
    rw [List.length_range] at this
    omega
  rw [primeCounting_eq_piFast hm]
  simp only [prime_iff_primeLe168 hpi_le]

lemma a_8 : OeisA237578.a 8 = 1 := by
  rw [a_eq_fast (by decide)]
  decide

lemma a_13 : OeisA237578.a 13 = 1 := by
  rw [a_eq_fast (by decide)]
  decide

theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  rintro n (rfl | rfl | rfl)
  · exact OeisA237578.a_5
  · exact a_8
  · exact a_13
