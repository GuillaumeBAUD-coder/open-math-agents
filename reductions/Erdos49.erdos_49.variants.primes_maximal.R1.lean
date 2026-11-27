import FormalConjectures.ErdosProblems.«49»

namespace OMA.R_Erdos49_erdos_49_variants_primes_maximal_R1

-- The initial segment of the chain may use 1 and 2, but no odd prime.
def H1 : Prop :=
  ∀ N ≥ 2, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
    (∀ n ∈ A, n.Prime → n ≤ 2) → StrictMonoOn Nat.totient (A : Set ℕ) →
    A.card ≤ Nat.primeCounting N

-- After the last selected odd prime p, replace the remaining composite terms
-- by primes in (p,N]. All their totients are at least p.
def H2 : Prop :=
  ∀ p N : ℕ, 2 < p → p.Prime → p ≤ N → ∀ A : Finset ℕ,
    A ⊆ Finset.Ioc p N → (∀ n ∈ A, ¬ n.Prime ∧ p ≤ n.totient) →
    StrictMonoOn Nat.totient (A : Set ℕ) → Nat.primeCounting p + A.card ≤ Nat.primeCounting N

lemma chain_bound (h₁ : H1) (h₂ : H2) (N : ℕ) (hN : 2 ≤ N)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hm : StrictMonoOn Nat.totient (A : Set ℕ)) : A.card ≤ Nat.primeCounting N := by
  classical
  induction N using Nat.strong_induction_on generalizing A with
  | h N ih =>
    let P := A.filter fun n => 2 < n ∧ n.Prime
    by_cases hP : P.Nonempty
    · let p := P.max' hP
      obtain ⟨hpA, hp3, hprime⟩ := Finset.mem_filter.mp (P.max'_mem hP)
      change p ∈ A at hpA
      change 2 < p at hp3
      change p.Prime at hprime
      have hpN := (Finset.mem_Icc.mp (hA hpA)).2
      let L := A.filter fun n => n < p
      let R := A.filter fun n => p < n
      have hL : L.card ≤ Nat.primeCounting (p - 1) := by
        apply ih (p - 1) (by omega) (by omega) L _ (hm.mono (Finset.filter_subset _ _))
        intro n hn
        obtain ⟨ha, hlt⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hA ha)).1, by omega⟩
      have hR : Nat.primeCounting p + R.card ≤ Nat.primeCounting N := by
        apply h₂ p N hp3 hprime hpN R _ _ (hm.mono (Finset.filter_subset _ _))
        · intro n hn
          obtain ⟨ha, hlt⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_Ioc.mpr ⟨hlt, (Finset.mem_Icc.mp (hA ha)).2⟩
        · intro n hn
          obtain ⟨ha, hlt⟩ := Finset.mem_filter.mp hn
          refine ⟨fun hnprime => ?_, ?_⟩
          · have hle : n ≤ p := Finset.le_max' P n (Finset.mem_filter.mpr ⟨ha, by omega, hnprime⟩)
            omega
          · have ht := hm hpA ha hlt
            rw [Nat.totient_prime hprime] at ht
            omega
      have hjump : Nat.primeCounting p = Nat.primeCounting (p - 1) + 1 := by
        unfold Nat.primeCounting Nat.primeCounting'
        rw [Nat.count_succ, if_pos hprime, show p - 1 + 1 = p by omega]
      have partition : A = insert p (L ∪ R) := by
        ext n
        simp [L, R]
        grind
      have hdisj : Disjoint L R := by
        simp [L, R, Finset.disjoint_left]
        omega
      have hnot : p ∉ L ∪ R := by simp [L, R]
      have hcard := congrArg Finset.card partition
      rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj] at hcard
      omega
    · apply h₁ N hN A hA _ hm
      intro n hn hprime
      by_contra! h
      exact hP ⟨n, Finset.mem_filter.mpr ⟨hn, h, hprime⟩⟩

theorem main : H1 → H2 → type_of% @Erdos49.erdos_49.variants.primes_maximal := by
  intro h₁ h₂ N hN
  unfold Erdos49.f
  apply le_antisymm
  · apply csSup_le' 
    rintro k ⟨A, hA, hm, rfl⟩
    exact chain_bound h₁ h₂ N hN A hA hm
  · apply le_csSup
    · refine ⟨(Finset.Icc 1 N).card, ?_⟩
      rintro k ⟨A, ha, _, rfl⟩
      exact Finset.card_le_card ha
    · refine ⟨N.primesLE, ?_, ?_, Nat.primesLE_card_eq_primeCounting N⟩
      · intro p hp
        exact Finset.mem_Icc.mpr ⟨(Nat.one_lt_of_mem_primesLE hp).le, Nat.le_of_mem_primesLE hp⟩
      · intro p hp q hq hpq
        rw [Nat.totient_prime (Nat.prime_of_mem_primesLE hp), Nat.totient_prime (Nat.prime_of_mem_primesLE hq)]
        have := Nat.two_le_of_mem_primesLE hp
        omega

end OMA.R_Erdos49_erdos_49_variants_primes_maximal_R1
