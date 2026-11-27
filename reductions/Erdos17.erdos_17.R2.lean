import FormalConjectures.ErdosProblems.«17»

/-! A packing criterion for primes satisfying the bounded difference condition. -/

namespace OMA.R_Erdos17_erdos_17_R2

/-- A coarse, uniform upper bound for the smaller prime in a representation
of each even difference up to twice the block scale. -/
def H1 : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, ∀ i ≤ k ^ 4,
    ∃ r : ℕ, r.Prime ∧ (2 * i + r).Prime ∧ r ≤ k ^ 2

/-- The smaller prime can be taken polylogarithmic for all relevant differences,
except possibly in k intervals of length k squared. -/
def H2 : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, ∃ E : Finset ℕ, E.card ≤ k ∧
    ∀ i ≤ k ^ 4, k ^ 4 ≤ 2 * i + k ^ 2 → (2 * i) / k ^ 2 ∉ E →
      ∃ r : ℕ, r.Prime ∧ (2 * i + r).Prime ∧ r ≤ (Nat.log2 (k ^ 4) + 1) ^ 3

/-- Arbitrarily large blocks contain more than k separated primes passing
only the terminal tests for odd composite deficits up to a cubic logarithm. -/
def H3 : Prop :=
  ∀ N : ℕ, ∃ k ≥ N, ∃ S : Finset ℕ, k < S.card ∧
    (∀ p ∈ S, k ^ 4 ≤ p ∧ p ≤ 2 * k ^ 4 ∧ p.Prime ∧
      ∀ t : ℕ, 3 ≤ t → t ≤ (Nat.log2 (k ^ 4) + 1) ^ 3 → t ≤ p →
        Odd t → ¬ t.Prime → ∃ r : ℕ, r.Prime ∧ (p - t + r).Prime ∧ r ≤ t) ∧
    ∀ p ∈ S, ∀ q ∈ S, p < q → p + 2 * k ^ 2 ≤ q

/-- A prime failing the cluster tests has an even difference for which
every pair of witnesses overshoots the endpoint. -/
lemma obstruction {p : ℕ} (hp : p.Prime) (h : ¬ Erdos17.IsClusterPrime p) :
    ∃ i : ℕ, 2 * i + 3 ≤ p ∧
      ∀ r : ℕ, r.Prime → (2 * i + r).Prime → p < 2 * i + r := by
  by_contra! hall
  apply h
  refine ⟨hp, ?_⟩
  rintro n ⟨i, hi⟩ hn
  obtain ⟨r, hr, hs, hle⟩ := hall i (by omega)
  exact ⟨2 * i + r, r, hs, hr, hle, by omega, by omega⟩

/-- A failing endpoint belongs to the interval of length 2B starting at
the left edge of an exceptional cell of differences. -/
lemma exceptional_cell {X B W p : ℕ} {E : Finset ℕ} (hB : 0 < B)
    (hlo : X ≤ p) (hhi : p ≤ 2 * X) (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : ∀ i ≤ X, ∃ r : ℕ, r.Prime ∧ (2 * i + r).Prime ∧ r ≤ B)
    (hf : ∀ i ≤ X, X ≤ 2 * i + B → (2 * i) / B ∉ E →
      ∃ r : ℕ, r.Prime ∧ (2 * i + r).Prime ∧ r ≤ W)
    (hloc : ∀ t : ℕ, 3 ≤ t → t ≤ W → t ≤ p → Odd t → ¬ t.Prime →
      ∃ r : ℕ, r.Prime ∧ (p - t + r).Prime ∧ r ≤ t)
    (hbad : ¬ Erdos17.IsClusterPrime p) :
    ∃ j ∈ E, j * B ≤ p ∧ p < j * B + 2 * B := by
  obtain ⟨i, hi, hmiss⟩ := obstruction hp hbad
  obtain ⟨r, hr, hs, hrB⟩ := hc i (by omega)
  have hlarge := hmiss r hr hs
  have hrem := Nat.mod_lt (2 * i) hB
  have hdiv := Nat.mod_add_div (2 * i) B
  rw [Nat.mul_comm B ((2 * i) / B)] at hdiv
  refine ⟨(2 * i) / B, ?_, by omega, by omega⟩
  by_contra hnot
  obtain ⟨s, hsp, hpair, hW⟩ := hf i (by omega) (by omega) hnot
  have hovershoot := hmiss s hsp hpair
  let t := p - 2 * i
  have hsum : 2 * i + t = p := by dsimp [t]; omega
  have hodd : Odd t := by
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    exact ⟨j - i, by omega⟩
  by_cases ht : t.Prime
  · have := hmiss t ht (hsum ▸ hp)
    omega
  · obtain ⟨a, ha, hap, hat⟩ := hloc t (by omega) (by omega) (by omega) hodd ht
    have heq : p - t = 2 * i := by omega
    rw [heq] at hap
    have := hmiss a ha hap
    omega

/-- Separated points cannot be assigned to fewer left endpoints of intervals
of length B. The intervals need not themselves be disjoint. -/
lemma separated_card_le {S E : Finset ℕ} {B : ℕ} {start : ℕ → ℕ}
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p < q → p + B ≤ q)
    (h : ∀ p ∈ S, ∃ i ∈ E, start i ≤ p ∧ p < start i + B) :
    S.card ≤ E.card := by
  classical
  let f (p : ℕ) := if hp : p ∈ S then (h p hp).choose else 0
  have hf {p : ℕ} (hp : p ∈ S) :
      f p ∈ E ∧ start (f p) ≤ p ∧ p < start (f p) + B := by
    simpa [f, hp] using (h p hp).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    exact (hf hp).1
  · intro p hp q hq heq
    have hstart := congrArg start heq
    have h₁ := (hf hp).2
    have h₂ := (hf hq).2
    rcases lt_trichotomy p q with hl | he | hg
    · have := hsep p hp q hq hl
      omega
    · exact he
    · have := hsep q hq p hp hg
      omega

/-- The number of local candidates lost is at most the exceptional-set size. -/
lemma cluster_count_bound [DecidablePred Erdos17.IsClusterPrime]
    {S E : Finset ℕ} {B : ℕ} {start : ℕ → ℕ}
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p < q → p + B ≤ q)
    (h : ∀ p ∈ S, ¬ Erdos17.IsClusterPrime p →
      ∃ i ∈ E, start i ≤ p ∧ p < start i + B) :
    S.card ≤ E.card + (S.filter Erdos17.IsClusterPrime).card := by
  let T := S.filter (fun p ↦ ¬ Erdos17.IsClusterPrime p)
  have hloss : T.card ≤ E.card := by
    apply separated_card_le (B := B) (start := start)
    · intro p hp q hq
      exact hsep p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    · intro p hp
      exact h p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hpartition := S.card_filter_add_card_filter_not Erdos17.IsClusterPrime
  change (S.filter Erdos17.IsClusterPrime).card + T.card = S.card at hpartition
  omega

theorem main : H1 → H2 → H3 → type_of% @Erdos17.erdos_17 := by
  classical
  rintro ⟨K, hc⟩ ⟨L, hf⟩ hlocal
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hk, S, hcard, hS, hsep⟩ := hlocal (max (max K L) (N + 3))
  obtain ⟨E, hE, hsmall⟩ := hf k (by omega)
  have hpow : k ≤ k ^ 4 := Nat.le_self_pow (by decide) k
  have hB : 0 < k ^ 2 := pow_pos (by omega) 2
  have hcount := cluster_count_bound (E := E) (start := fun j ↦ j * k ^ 2) hsep (by
    intro p hp hbad
    obtain ⟨hlo, hhi, hprime, hnear⟩ := hS p hp
    exact exceptional_cell hB hlo hhi hprime (by omega)
      (hc k (by omega)) hsmall hnear hbad)
  have hpos : 0 < (S.filter Erdos17.IsClusterPrime).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  obtain ⟨hpS, hcluster⟩ := Finset.mem_filter.mp hp
  have hlo := (hS p hpS).1
  exact ⟨p, hcluster, by omega⟩

end OMA.R_Erdos17_erdos_17_R2
