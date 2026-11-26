import FormalConjectures.ErdosProblems.«1100»

-- Problem: Erdős Problem 1100 — eq omega
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1100.lean:177 (declaration Erdos1100.erdos_1100.variants.eq_omega)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped ArithmeticFunction.omega

namespace OMA

def Good (n : ℕ) : Prop :=
  ∀ q, q.Prime → q ∣ n → ∀ e, e ∣ n → (∀ r, r.Prime → r ∣ e → r < q) → e < q

lemma key {n d d' : ℕ} (hn : 0 < n) (hG : Good n) (hd : d ∣ n) (hd' : d' ∣ n) (hlt : d < d')
    (hbetw : ∀ c, c ∣ n → c < d' → c ≤ d) (hcop : Nat.Coprime d d') : d'.Prime := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hd'1 : 1 < d' := by omega
  obtain ⟨p, hp, hmax⟩ : ∃ p ∈ d'.primeFactors, ∀ r ∈ d'.primeFactors, id r ≤ id p :=
    Finset.exists_max_image _ id (Nat.nonempty_primeFactors.mpr hd'1)
  obtain ⟨hpp, hpd', -⟩ := Nat.mem_primeFactors.mp hp
  by_contra hnp
  have hpne : p ≠ d' := fun h => hnp (h ▸ hpp)
  have hple : p ≤ d' := Nat.le_of_dvd (by omega) hpd'
  have hpd : p ≤ d := hbetw p (hpd'.trans hd') (lt_of_le_of_ne hple hpne)
  have hpnd : ¬ p ∣ d := by
    intro h
    have := Nat.dvd_gcd h hpd'
    rw [hcop.gcd_eq_one] at this
    exact hpp.not_dvd_one this
  by_cases hq : ∃ q, q.Prime ∧ q ∣ d ∧ p < q
  · obtain ⟨q, hq, hqd, hpq⟩ := hq
    have h1 : d' < q := hG q hq (hqd.trans hd) d' hd' (fun r hr hrd' =>
      lt_of_le_of_lt (hmax r (Nat.mem_primeFactors.mpr ⟨hr, hrd', by omega⟩)) hpq)
    have h2 : q ≤ d := Nat.le_of_dvd hdpos hqd
    omega
  · push Not at hq
    have : d < p := hG p hpp (hpd'.trans hd') d hd (fun r hr hrd =>
      lt_of_le_of_ne (hq r hr hrd) (fun h => hpnd (h ▸ hrd)))
    omega

lemma exists_good (k : ℕ) : ∃ n, 0 < n ∧ Squarefree n ∧ ω n = k ∧ Good n := by
  induction k with
  | zero =>
    refine ⟨1, one_pos, squarefree_one, ArithmeticFunction.cardDistinctFactors_one, ?_⟩
    intro q hq hq1
    exact absurd hq1 hq.not_dvd_one
  | succ k ih =>
    obtain ⟨n, hn, hsq, hω, hG⟩ := ih
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (n + 1)
    have hpn : n < p := by omega
    have hpnd : ¬ p ∣ n := Nat.not_dvd_of_pos_of_lt hn hpn
    have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpnd).symm
    refine ⟨n * p, Nat.mul_pos hn hp.pos, Nat.squarefree_mul_iff.mpr
      ⟨hcop, hsq, hp.prime.squarefree⟩, ?_, ?_⟩
    · rw [ArithmeticFunction.cardDistinctFactors_mul hcop, hω,
        ArithmeticFunction.cardDistinctFactors_apply_prime hp]
    · intro q hq hqd e he hr
      by_cases hpe : p ∣ e
      · have hpq : p < q := hr p hp hpe
        rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
        · have := Nat.le_of_dvd hn h
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
          omega
      · have hcop' : Nat.Coprime e p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpe).symm
        have hen : e ∣ n := hcop'.dvd_of_dvd_mul_right he
        rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
        · exact hG q hq h e hen hr
        · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
          have := Nat.le_of_dvd hn hen
          omega

lemma tau_le {n : ℕ} (hn : 0 < n) (hG : Good n) : Erdos1100.tauPerp n ≤ ω n := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  have hω : ω n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
    rfl
  rw [hω]
  unfold Erdos1100.tauPerp
  apply Finset.card_le_card_of_injOn (fun i : Fin (n.divisors.card - 1) =>
    Nat.nth (· ∣ n) ((i : ℕ) + 1))
  · intro i hi
    have hcop := (Finset.mem_filter.mp hi).2
    have hi1 : (i : ℕ) + 1 < hf.toFinset.card := by
      have := i.isLt
      omega
    have hd : Nat.nth (· ∣ n) (i : ℕ) ∣ n := Nat.nth_mem_of_lt_card hf (by omega)
    have hd' : Nat.nth (· ∣ n) ((i : ℕ) + 1) ∣ n := Nat.nth_mem_of_lt_card hf hi1
    have hlt := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self (i : ℕ)) hi1
    have hbetw : ∀ c, c ∣ n → c < Nat.nth (· ∣ n) ((i : ℕ) + 1) →
        c ≤ Nat.nth (· ∣ n) (i : ℕ) := by
      intro c hc hclt
      have hj : Nat.nth (· ∣ n) (Nat.count (· ∣ n) c) = c := Nat.nth_count (p := (· ∣ n)) hc
      have hjlt : Nat.count (· ∣ n) c < hf.toFinset.card := Nat.count_lt_card hf hc
      by_cases hji : Nat.count (· ∣ n) c ≤ (i : ℕ)
      · have := Nat.nth_le_nth_of_lt_card hf hji (by omega)
        omega
      · have := Nat.nth_le_nth_of_lt_card hf (show (i : ℕ) + 1 ≤ Nat.count (· ∣ n) c by omega)
          hjlt
        omega
    have hprime := key hn hG hd hd' hlt hbetw hcop
    exact Finset.mem_coe.mpr (Nat.mem_primeFactors.mpr ⟨hprime, hd', hn.ne'⟩)
  · intro i _ j _ hij
    have hi1 : (i : ℕ) + 1 < hf.toFinset.card := by
      have := i.isLt
      omega
    have hj1 : (j : ℕ) + 1 < hf.toFinset.card := by
      have := j.isLt
      omega
    have := Nat.nth_injOn hf hi1 hj1 hij
    exact Fin.ext (by omega)

end OMA

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.eq_omega := by
  intro k
  obtain ⟨n, hn, hsq, hω, hG⟩ := OMA.exists_good k
  refine ⟨n, hsq, hω, ?_⟩
  have h1 := Erdos1100.erdos_1100.variants.omega_le n hn
  have h2 := OMA.tau_le hn hG
  omega
