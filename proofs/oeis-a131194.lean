import OMAStatements.S_oeis_a131194

theorem j18_suffix_length :
    (Nat.digits 10 1234567890123456789012345678901).length = 31 := by
  decide

theorem j18_suffix_count (d : ℕ) (hd : d < 10) :
    3 ≤ (Nat.digits 10 1234567890123456789012345678901).count d := by
  interval_cases d <;> decide

theorem j18_universal_prime (N : ℕ) :
    ∃ q : ℕ, N < q ∧ q.Prime ∧
      ∀ d : ℕ, d < 10 → 3 ≤ (Nat.digits 10 q).count d := by
  obtain ⟨q, hN, hq, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N
      (q := 10 ^ 31) (a := 1234567890123456789012345678901)
      (by decide) (by decide)
  refine ⟨q, hN, hq, ?_⟩
  have hrem : q % 10 ^ 31 = 1234567890123456789012345678901 := by
    change q % 10 ^ 31 = 1234567890123456789012345678901 % 10 ^ 31 at hmod
    exact hmod.trans (by decide)
  have heq : 1234567890123456789012345678901 + 10 ^ 31 * (q / 10 ^ 31) = q := by
    rw [← hrem]
    exact Nat.mod_add_div q (10 ^ 31)
  have hds : Nat.digits 10 q =
      Nat.digits 10 1234567890123456789012345678901 ++ Nat.digits 10 (q / 10 ^ 31) := by
    rw [Nat.digits_append_digits (by decide), j18_suffix_length, heq]
  intro d hd
  rw [hds, List.count_append]
  exact le_trans (j18_suffix_count d hd) (Nat.le_add_right _ _)

lemma j18_digits_count_sum (p : ℕ) :
    (∑ d ∈ Finset.range 10, (Nat.digits 10 p).count d) = (Nat.digits 10 p).length := by
  simpa only [Multiset.coe_count, Multiset.coe_card] using
    (Multiset.sum_count_eq_card (s := Finset.range 10)
      (m := (Nat.digits 10 p : Multiset ℕ)) (by
        intro d hd
        apply Finset.mem_range.mpr
        exact Nat.digits_lt_base (by decide) (by simpa using hd)))

lemma j18_common (p q : ℕ) (hp : 100 ≤ p)
    (hq : ∀ d : ℕ, d < 10 → 3 ≤ (Nat.digits 10 q).count d) :
    3 ≤ OMA.S_oeis_a131194.commonDigitCount p q := by
  have hlen : 3 ≤ (Nat.digits 10 p).length := by
    have h := (Nat.lt_digits_length_iff (b := 10) (k := 2) (by decide) p).2
      (by simpa using hp)
    omega
  unfold OMA.S_oeis_a131194.commonDigitCount
  by_cases h : ∃ d ∈ Finset.range 10, 3 ≤ (Nat.digits 10 p).count d
  · obtain ⟨d, hd, hpd⟩ := h
    have hqd := hq d (Finset.mem_range.mp hd)
    exact (le_min hpd hqd).trans
      (Finset.single_le_sum
        (f := fun d => min ((Nat.digits 10 p).count d) ((Nat.digits 10 q).count d))
        (fun _ _ => Nat.zero_le _) hd)
  · push Not at h
    calc
      3 ≤ (Nat.digits 10 p).length := hlen
      _ = ∑ d ∈ Finset.range 10, (Nat.digits 10 p).count d := (j18_digits_count_sum p).symm
      _ = ∑ d ∈ Finset.range 10,
          min ((Nat.digits 10 p).count d) ((Nat.digits 10 q).count d) := by
        apply Finset.sum_congr rfl
        intro d hd
        apply (min_eq_left _).symm
        exact (Nat.le_of_lt (h d hd)).trans (hq d (Finset.mem_range.mp hd))

lemma j18_term_next (seed i : ℕ) :
    OMA.S_oeis_a131194.term (OMA.S_oeis_a131194.nextPrime seed) i =
      OMA.S_oeis_a131194.term seed (i + 1) := by
  induction i with
  | zero => rfl
  | succ i hi =>
    simp only [OMA.S_oeis_a131194.term, hi]

lemma j18_reaches (q seed : ℕ) (hq : q.Prime) (hs : 100 ≤ seed) (hsq : seed ≤ q)
    (hcommon : ∀ p : ℕ, 100 ≤ p → 3 ≤ OMA.S_oeis_a131194.commonDigitCount p q) :
    ∃ i, OMA.S_oeis_a131194.term seed i = q := by
  have hall : ∀ d seed : ℕ, q - seed = d → 100 ≤ seed → seed ≤ q →
      ∃ i, OMA.S_oeis_a131194.term seed i = q := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro seed hd hs hsq
      by_cases heq : seed = q
      · exact ⟨0, heq⟩
      let S : Set ℕ := {r | seed < r ∧ r.Prime ∧
        3 ≤ OMA.S_oeis_a131194.commonDigitCount seed r}
      have hmemq : q ∈ S := ⟨by omega, hq, hcommon seed hs⟩
      have hmem : OMA.S_oeis_a131194.nextPrime seed ∈ S :=
        Nat.sInf_mem ⟨q, hmemq⟩
      have hnext : OMA.S_oeis_a131194.nextPrime seed ≤ q := csInf_le' hmemq
      have hlt : seed < OMA.S_oeis_a131194.nextPrime seed := hmem.1
      obtain ⟨i, hi⟩ := ih (q - OMA.S_oeis_a131194.nextPrime seed) (by omega)
        (OMA.S_oeis_a131194.nextPrime seed) rfl (by omega) hnext
      exact ⟨i + 1, (j18_term_next seed i).symm.trans hi⟩
  exact hall (q - seed) seed rfl hs hsq

theorem OMA.solution : type_of% @OMA.S_oeis_a131194.main := by
  intro seed _ hseed
  obtain ⟨q, hbound, hprime, hcounts⟩ := j18_universal_prime (max seed 101)
  have hcommon : ∀ p : ℕ, 100 ≤ p →
      3 ≤ OMA.S_oeis_a131194.commonDigitCount p q :=
    fun p hp => j18_common p q hp hcounts
  obtain ⟨i, hi⟩ := j18_reaches q seed hprime hseed
    ((le_max_left seed 101).trans hbound.le) hcommon
  obtain ⟨j, hj⟩ := j18_reaches q 101 hprime (by decide)
    ((le_max_right seed 101).trans hbound.le) hcommon
  refine ⟨i, j, ?_, hi.trans hj.symm⟩
  simpa only [hi] using hprime
