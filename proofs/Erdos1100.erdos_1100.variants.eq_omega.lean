import FormalConjectures.ErdosProblems.«1100»

-- Problem: Erdős Problem 1100 — eq omega
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1100.lean:177 (declaration Erdos1100.erdos_1100.variants.eq_omega)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.O3

/-- Construction: `n = p_1 ⋯ p_k` with each prime larger than the product of the previous ones.
The last component records the key property: two coprime divisors `d < d'` with `d'` not prime
always have a divisor strictly between them. -/
theorem exists_n (k : ℕ) : ∃ n : ℕ, 0 < n ∧ Squarefree n ∧ n.primeFactors.card = k ∧
    ∀ d d' : ℕ, d ∣ n → d' ∣ n → d < d' → Nat.Coprime d d' → ¬ d'.Prime →
      ∃ e, e ∣ n ∧ d < e ∧ e < d' := by
  induction k with
  | zero =>
    refine ⟨1, one_pos, squarefree_one, by simp, ?_⟩
    intro d d' hd hd' hlt _ _
    have h1 : d' = 1 := Nat.dvd_one.mp hd'
    have h2 : d = 1 := Nat.dvd_one.mp hd
    omega
  | succ k ih =>
    obtain ⟨n, hn, hsq, hc, hQ⟩ := ih
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
    have hndvd : ¬ p ∣ n := fun h => by
      have := Nat.le_of_dvd hn h
      omega
    have hcop : Nat.Coprime n p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)
    refine ⟨n * p, Nat.mul_pos hn hp.pos,
      Nat.squarefree_mul_iff.mpr ⟨hcop, hsq, hp.prime.squarefree⟩, ?_, ?_⟩
    · rw [Nat.primeFactors_mul hn.ne' hp.ne_zero, hp.primeFactors,
        Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr fun h => hndvd (Nat.dvd_of_mem_primeFactors h)),
        hc, Finset.card_singleton]
    · intro d d' hd hd' hlt hdd' hnp
      have hd'pos : 0 < d' := by omega
      by_cases hpd' : p ∣ d'
      · have hpd : ¬ p ∣ d := fun h => by
          have h3 := Nat.dvd_gcd h hpd'
          rw [Nat.Coprime.gcd_eq_one hdd'] at h3
          exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
        have hdn : d ∣ n :=
          Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm hd
        have hdle : d ≤ n := Nat.le_of_dvd hn hdn
        have hple : p ≤ d' := Nat.le_of_dvd hd'pos hpd'
        have hne : p ≠ d' := fun h => hnp (h ▸ hp)
        exact ⟨p, dvd_mul_left p n, by omega, by omega⟩
      · have hd'n : d' ∣ n :=
          Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd').symm hd'
        have hd'le : d' ≤ n := Nat.le_of_dvd hn hd'n
        have hdpos : 0 < d := by
          rcases Nat.eq_zero_or_pos d with h | h
          · subst h
            rw [zero_dvd_iff] at hd
            have := Nat.mul_pos hn hp.pos
            omega
          · exact h
        have hpd : ¬ p ∣ d := fun h => by
          have := Nat.le_of_dvd hdpos h
          omega
        have hdn : d ∣ n :=
          Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm hd
        obtain ⟨e, he, h1, h2⟩ := hQ d d' hdn hd'n hlt hdd' hnp
        exact ⟨e, Dvd.dvd.mul_right he p, h1, h2⟩

/-- Under the key property, every coprime consecutive pair of divisors ends in a prime, so
`tauPerp n` is at most the number of prime factors. -/
theorem tau_le (n : ℕ) (hn : 0 < n)
    (hQ : ∀ d d' : ℕ, d ∣ n → d' ∣ n → d < d' → Nat.Coprime d d' → ¬ d'.Prime →
      ∃ e, e ∣ n ∧ d < e ∧ e < d') :
    Erdos1100.tauPerp n ≤ n.primeFactors.card := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  unfold Erdos1100.tauPerp
  refine Finset.card_le_card_of_injOn (fun i => Nat.nth (· ∣ n) ((i : ℕ) + 1)) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hi0 := i.isLt
    have hi1 : (i : ℕ) + 1 < hf.toFinset.card := by rw [hcard]; omega
    have hb : Nat.nth (· ∣ n) ((i : ℕ) + 1) ∣ n := Nat.nth_mem_of_lt_card hf hi1
    have ha : Nat.nth (· ∣ n) (i : ℕ) ∣ n := Nat.nth_mem_of_lt_card hf (by omega)
    have hlt : Nat.nth (· ∣ n) (i : ℕ) < Nat.nth (· ∣ n) ((i : ℕ) + 1) :=
      Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) hi1
    have hprime : (Nat.nth (· ∣ n) ((i : ℕ) + 1)).Prime := by
      by_contra hnp
      obtain ⟨e, he, h1, h2⟩ := hQ _ _ ha hb hlt hi hnp
      have := Nat.le_nth_of_lt_nth_succ (p := (· ∣ n)) h2 he
      omega
    show Nat.nth (· ∣ n) ((i : ℕ) + 1) ∈ n.primeFactors
    exact Nat.mem_primeFactors.mpr ⟨hprime, hb, hn.ne'⟩
  · intro i _ j _ hij
    have hi0 := i.isLt
    have hj0 := j.isLt
    have h := Nat.nth_injOn hf
      (show (i : ℕ) + 1 ∈ Set.Iio hf.toFinset.card by rw [Set.mem_Iio, hcard]; omega)
      (show (j : ℕ) + 1 ∈ Set.Iio hf.toFinset.card by rw [Set.mem_Iio, hcard]; omega) hij
    exact Fin.ext (by omega)

end OMA.O3

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.eq_omega := by
  intro k
  obtain ⟨n, hn, hsq, hc, hQ⟩ := OMA.O3.exists_n k
  have hω : ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
    rfl
  have h1 := Erdos1100.erdos_1100.variants.omega_le n hn
  have h2 := OMA.O3.tau_le n hn hQ
  refine ⟨n, hsq, ?_, ?_⟩
  · rw [hω, hc]
  · rw [hω, hc] at h1
    rw [hc] at h2
    omega
