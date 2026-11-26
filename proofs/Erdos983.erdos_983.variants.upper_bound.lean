import FormalConjectures.ErdosProblems.«983»

/-! Erdős and Straus's bound, reported in Erdős, Some applications of graph theory
to number theory (1970), p. 139: https://www.renyi.hu/~p_erdos/1970-20.pdf.
Keep all small primes and select the large primes by the sizes of their fibers. -/

open scoped BigOperators

private theorem OMA.selectLargePrimes {B : Finset ℕ} (weight : ℕ → ℕ) (a s : ℕ)
    (hsize : s + 1 ≤ B.card) (htotal : s + B.card < a + ∑ p ∈ B, weight p) :
    ∃ T ⊆ B, T.card = s + 1 ∧ 2 * (s + 1) ≤ a + ∑ p ∈ T, weight p := by
  classical
  induction B using Finset.strongInductionOn with
  | _ B ih =>
    by_cases heq : B.card = s + 1
    · exact ⟨B, Finset.Subset.rfl, heq, by omega⟩
    by_cases hlight : ∃ p ∈ B, weight p ≤ 1
    · obtain ⟨p, hp, hw⟩ := hlight
      have hc : (B.erase p).card + 1 = B.card := Finset.card_erase_add_one hp
      have hsum : (∑ q ∈ B.erase p, weight q) + weight p = ∑ q ∈ B, weight q :=
        Finset.sum_erase_add _ _ hp
      obtain ⟨T, hTB, hT, hcount⟩ :=
        ih (B.erase p) (Finset.erase_ssubset hp) (by omega) (by omega)
      exact ⟨T, hTB.trans (Finset.erase_subset _ _), hT, hcount⟩
    · obtain ⟨T, hTB, hT⟩ := Finset.exists_subset_card_eq hsize
      have hweights : (∑ _ ∈ T, 2) ≤ ∑ p ∈ T, weight p := by
        apply Finset.sum_le_sum
        intro p hp
        have hw : ¬ weight p ≤ 1 := fun h => hlight ⟨p, hTB hp, h⟩
        omega
      simp [hT] at hweights
      exact ⟨T, hTB, hT, by omega⟩

private theorem OMA.uniqueLargePrime {n m p q : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hp : p ∈ m.primeFactors) (hq : q ∈ m.primeFactors)
    (hpl : n.sqrt < p) (hql : n.sqrt < q) : p = q := by
  by_contra hne
  have hp' := Nat.mem_primeFactors.mp hp
  have hq' := Nat.mem_primeFactors.mp hq
  have hdvd : p * q ∣ m :=
    ((Nat.coprime_primes hp'.1 hq'.1).2 hne).mul_dvd_of_dvd_of_dvd hp'.2.1 hq'.2.1
  have hpq : p * q ≤ n := (Nat.le_of_dvd hm hdvd).trans hmn
  rcases le_total p q with h | h
  · exact (not_lt_of_ge ((Nat.mul_le_mul_left p h).trans hpq)) (Nat.sqrt_lt.mp hpl)
  · exact (not_lt_of_ge ((Nat.mul_le_mul_right q h).trans hpq)) (Nat.sqrt_lt.mp hql)

theorem OMA.solution : type_of% @Erdos983.erdos_983.variants.upper_bound := by
  classical
  intro n
  by_cases hn : Nat.primeCounting n ≤ 2 * Nat.primeCounting n.sqrt + 1
  · exact (Erdos983.erdos_983.variants.le_primeCounting (Nat.lt_succ_self _)).trans hn
  apply Erdos983.f_le
  intro A hA hcard
  let primes (k : ℕ) : Finset ℕ := (Finset.range (k + 1)).filter Nat.Prime
  let P := primes n.sqrt
  let B := primes n \ P
  have hprimeCard (k : ℕ) : (primes k).card = Nat.primeCounting k := by
    simp [primes, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hPB : P ⊆ primes n := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hm.1).trans_le
        (Nat.succ_le_succ (Nat.sqrt_le_self n))), hm.2⟩
  have hBCard : B.card + P.card = Nat.primeCounting n := by
    rw [← hprimeCard]
    exact Finset.card_sdiff_add_card_eq_card hPB
  have hp0 : 0 ∉ B := by
    intro h
    exact Nat.not_prime_zero (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
  let g (m : ℕ) : ℕ :=
    if h : ∃ p ∈ m.primeFactors, n.sqrt < p then h.choose else 0
  have hfactor {m p : ℕ} (hm : m ∈ A) (hp : p ∈ m.primeFactors) (h : n.sqrt < p) :
      g m = p := by
    let hh : ∃ q ∈ m.primeFactors, n.sqrt < q := ⟨p, hp, h⟩
    have hm' := Finset.mem_Icc.mp (hA hm)
    dsimp only [g]
    rw [dif_pos hh]
    exact OMA.uniqueLargePrime (by omega) hm'.2 hh.choose_spec.1 hp hh.choose_spec.2 h
  have hmaps : (A : Set ℕ).MapsTo g (insert 0 B : Finset ℕ) := by
    intro m hm
    change g m ∈ insert 0 B
    by_cases h : ∃ p ∈ m.primeFactors, n.sqrt < p
    · have hm' := Finset.mem_Icc.mp (hA hm)
      have hprime := Nat.mem_primeFactors.mp h.choose_spec.1
      have hle := (Nat.le_of_dvd (by omega) hprime.2.1).trans hm'.2
      dsimp only [g]
      rw [dif_pos h]
      refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime.1⟩
      · intro hmem
        have := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
        have := h.choose_spec.2
        omega
    · dsimp only [g]
      rw [dif_neg h]
      exact Finset.mem_insert_self _ _
  let weight (p : ℕ) := (A.filter fun m => g m = p).card
  have htotal : A.card = weight 0 + ∑ p ∈ B, weight p := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_insert hp0
  have hPCard : P.card = Nat.primeCounting n.sqrt := hprimeCard _
  obtain ⟨T, hTB, hTCard, hcount⟩ := OMA.selectLargePrimes weight (weight 0) P.card
    (B := B) (by omega) (by omega)
  have hdisj : Disjoint P T := by
    refine Finset.disjoint_left.mpr fun p hp ht => ?_
    exact (Finset.mem_sdiff.mp (hTB ht)).2 hp
  refine ⟨P ∪ T, by rw [Finset.card_union_of_disjoint hdisj, hTCard, hPCard]; omega, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).2
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hTB hp)).1).2
  · have hsubset : A.filter (fun m => g m ∈ insert 0 T) ⊆
        A.filter (fun m => ∀ p ∈ m.primeFactors, p ∈ P ∪ T) := by
      intro m hm
      obtain ⟨ha, hg⟩ := Finset.mem_filter.mp hm
      refine Finset.mem_filter.mpr ⟨ha, fun p hp => ?_⟩
      by_cases h : p ≤ n.sqrt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), (Nat.mem_primeFactors.mp hp).1⟩)
      · rw [hfactor ha hp (by omega)] at hg
        rcases Finset.mem_insert.mp hg with he | ht
        · omega
        · exact Finset.mem_union_right _ ht
    have hcardF : (A.filter fun m => g m ∈ insert 0 T).card =
        weight 0 + ∑ p ∈ T, weight p := by
      rw [← Finset.sum_card_fiberwise_eq_card_filter A (insert 0 T) g]
      exact Finset.sum_insert (fun h => hp0 (hTB h))
    have hle := Finset.card_le_card hsubset
    rw [hcardF] at hle
    exact (show 2 * Nat.primeCounting n.sqrt + 1 < 2 * (P.card + 1) by omega).trans_le
      (hcount.trans hle)