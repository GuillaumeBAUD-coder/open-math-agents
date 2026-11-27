import OMAReductions.R_Erdos408_erdos_408_parts_ii_R1

-- Step Erdos408.erdos_408.parts.ii.R1.H1: |f n - F n| <= 1 for the additive companion F.
-- Credit: @senamakel
-- The corrected-height recursion follows the idea of Erdos, Granville, Pomerance and Spiro (1990); the Lean proof is original here.

open Erdos408

lemma OMA.totient_hit (m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.totient^[k] m = 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h : m = 1
    · subst m
      exact ⟨1, le_rfl, by simp⟩
    have hgt : 1 < m := by omega
    obtain ⟨k, hk, hiter⟩ := ih m.totient (Nat.totient_lt m hgt) (Nat.totient_pos.mpr hm)
    exact ⟨k + 1, by omega, by rw [Function.iterate_succ_apply, hiter]⟩

lemma OMA.totient_height_spec (m : ℕ) (hm : 0 < m) :
    1 ≤ f m ∧ Nat.totient^[f m] m = 1 :=
  Nat.sInf_mem (OMA.totient_hit m hm)

lemma OMA.totient_step (m : ℕ) (hm : 2 < m) : f m = f m.totient + 1 := by
  have hm0 : 0 < m := by omega
  have hp0 : 0 < m.totient := Nat.totient_pos.mpr hm0
  have hp1 : m.totient ≠ 1 := by
    intro h
    rcases Nat.totient_eq_one_iff.mp h with h | h <;> omega
  obtain ⟨hpos, hφ⟩ := OMA.totient_height_spec m.totient hp0
  apply le_antisymm
  · exact Nat.sInf_le (show 1 ≤ f m.totient + 1 ∧
      Nat.totient^[f m.totient + 1] m = 1 from
        ⟨by omega, by rw [Function.iterate_succ_apply, hφ]⟩)
  · refine le_csInf (OMA.totient_hit m hm0) ?_
    rintro (k | k) ⟨hk, hiter⟩
    · omega
    · have htail : Nat.totient^[k] m.totient = 1 := by
        simpa only [Function.iterate_succ_apply] using hiter
      have hk' : 1 ≤ k := by
        by_contra! h
        have hk0 : k = 0 := by omega
        subst k
        exact hp1 (by simpa using htail)
      exact Nat.succ_le_succ (Nat.sInf_le (show 1 ≤ k ∧
        Nat.totient^[k] m.totient = 1 from ⟨hk', htail⟩))

/-- the additive companion, as a Finsupp sum -/
noncomputable def OMA.G (n : ℕ) : ℕ :=
  n.factorization.sum fun p e => e * (if p = 2 then 1 else f p - 1)

lemma OMA.G_eq (n : ℕ) :
    OMA.G n = ∑ p ∈ n.primeFactors, n.factorization p * (if p = 2 then 1 else f p - 1) := rfl

lemma OMA.G_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : OMA.G (a * b) = OMA.G a + OMA.G b := by
  unfold OMA.G
  rw [Nat.factorization_mul ha hb]
  exact Finsupp.sum_add_index' (fun p => by simp) (fun p x y => by ring)

lemma OMA.G_one : OMA.G 1 = 0 := by simp [OMA.G]

lemma OMA.G_pow_prime (p k : ℕ) (hp : p.Prime) :
    OMA.G (p ^ k) = k * (if p = 2 then 1 else f p - 1) := by
  unfold OMA.G
  rw [hp.factorization_pow]
  rw [Finsupp.sum_single_index (by simp)]

lemma OMA.G_prod {ι : Type*} (s : Finset ι) (h : ι → ℕ) (hh : ∀ i ∈ s, h i ≠ 0) :
    OMA.G (∏ i ∈ s, h i) = ∑ i ∈ s, OMA.G (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [OMA.G_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : h a ≠ 0 := hh a (Finset.mem_insert_self _ _)
    have h2 : ∏ i ∈ s, h i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hh i (Finset.mem_insert_of_mem hi)
    rw [OMA.G_mul _ _ h1 h2, ih fun i hi => hh i (Finset.mem_insert_of_mem hi)]

lemma OMA.main_claim : ∀ n : ℕ, 2 ≤ n → f n = OMA.G n + (if n % 2 = 0 then 0 else 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h2 : n = 2
    · subst h2
      have : OMA.G 2 = 1 := by
        have := OMA.G_pow_prime 2 1 Nat.prime_two
        simpa using this
      simp [this, f_two]
    have hn3 : 2 < n := by omega
    have hφ2 : 2 ≤ n.totient := by
      have := Nat.totient_even hn3
      have hp := Nat.totient_pos.mpr (by omega : 0 < n)
      obtain ⟨k, hk⟩ := this
      omega
    have hφlt : n.totient < n := Nat.totient_lt n (by omega)
    have hφeven : n.totient % 2 = 0 := by
      obtain ⟨k, hk⟩ := Nat.totient_even hn3
      omega
    have ihφ := ih _ hφlt hφ2
    simp only [hφeven, if_true] at ihφ
    rw [OMA.totient_step n hn3, ihφ]
    -- key: G (φ n) + [n even] = G n
    have key : OMA.G n.totient + (if n % 2 = 0 then 1 else 0) = OMA.G n := by
      have hne : n ≠ 0 := by omega
      rw [Nat.totient_eq_prod_factorization hne]
      unfold Finsupp.prod
      rw [OMA.G_prod _ _ (fun p hp => by
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact mul_ne_zero (pow_ne_zero _ hpp.ne_zero) (by have := hpp.two_le; omega))]
      rw [OMA.G_eq]
      -- termwise
      have hterm : ∀ p ∈ n.factorization.support,
          OMA.G (p ^ (n.factorization p - 1) * (p - 1)) + (if p = 2 then 1 else 0) =
            n.factorization p * (if p = 2 then 1 else f p - 1) := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have ha : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
        have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
        rw [OMA.G_mul _ _ (pow_ne_zero _ hpp.ne_zero) hp1, OMA.G_pow_prime _ _ hpp]
        by_cases hp2 : p = 2
        · subst hp2
          have : OMA.G (2 - 1) = 0 := by simp [OMA.G_one]
          rw [this]
          simp only [if_true]
          obtain ⟨a, ha'⟩ : ∃ a, n.factorization 2 = a + 1 := ⟨_, (Nat.succ_pred_eq_of_pos ha).symm⟩
          rw [ha']; simp
        · simp only [if_neg hp2]
          have hodd : 2 < p := lt_of_le_of_ne hpp.two_le (Ne.symm hp2)
          have hp1lt : p - 1 < n := lt_of_lt_of_le (by omega) (Nat.le_of_mem_primeFactors hp)
          have h1 := ih (p - 1) hp1lt (by omega)
          have hodd' : (p - 1) % 2 = 0 := by
            have := hpp.eq_one_or_self_of_dvd 2
            rcases hpp.eq_two_or_odd with h | h
            · exact absurd h hp2
            · omega
          rw [hodd'] at h1
          have hfp : f p = f (p - 1) + 1 := by
            rw [OMA.totient_step p hodd, Nat.totient_prime hpp]
          have : f p - 1 = f (p - 1) := by omega
          rw [this, h1]
          simp
          obtain ⟨a, ha'⟩ : ∃ a, n.factorization p = a + 1 := ⟨_, (Nat.succ_pred_eq_of_pos ha).symm⟩
          rw [ha']; simp; ring
      have := Finset.sum_congr rfl hterm
      rw [Finset.sum_add_distrib] at this
      have h2sum : ∑ p ∈ n.factorization.support, (if p = 2 then 1 else 0) =
          if n % 2 = 0 then 1 else 0 := by
        rw [Finset.sum_ite_eq' ]
        have : (2 ∈ n.factorization.support) ↔ n % 2 = 0 := by
          rw [Nat.support_factorization, Nat.mem_primeFactors]
          constructor
          · rintro ⟨-, h, -⟩; omega
          · intro h; exact ⟨Nat.prime_two, by omega, hne⟩
        simp only [this]
      rw [h2sum] at this
      exact this
    rw [← key]
    split_ifs <;> omega

theorem OMA.solution : OMA.R_Erdos408_erdos_408_parts_ii_R1.H1 := by
  unfold OMA.R_Erdos408_erdos_408_parts_ii_R1.H1
  intro F n hn
  show |(f n : ℝ) - ((OMA.G n : ℕ) : ℝ)| ≤ 1
  by_cases h1 : n = 1
  · subst h1
    simp [OMA.G_one, f_one]
  · have := OMA.main_claim n (by omega)
    rw [this]
    split_ifs <;> simp
