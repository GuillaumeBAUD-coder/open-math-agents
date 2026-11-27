import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1

-- Reduction Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2.R1 of step Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2
-- Credit: @graydeveloper01

/-!
Split of the orders n < 2^m by the deficit of their 2-part.

The target only needs: the orders below 2^m that are not powers of two carry at most
half as many groups as the 2-power orders. Write d = 2^(m-r) for a fixed r.

* H1 (large deficit): the orders n < 2^m that are not multiples of 2^(m-r), all together,
  carry at most a quarter of g(2^(m-1)).
* H2 (bounded deficit): for a fixed q < 2^r that is not a power of two, the single order
  2^k * q carries at most a 2^(-(r+2)) fraction of g(2^(k+r-1)); the threshold on k may
  depend on r and q.

main is elementary: every n < 2^m is a power of two, or not a multiple of 2^(m-r), or
of the form 2^(m-r) * q with q < 2^r not a power of two (fewer than 2^r such orders).
The abelian classes are not needed: 2 * (S - A) ≤ 2 * S.

Both hypotheses are consequences of the 2-group domination theorem announced by
Yinan Li and Youming Qiao, arXiv:2610.14509 (together with the growth of g(2^k));
neither is known to follow from the classical Higman, Sims and Pyber estimates.
-/

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1_H2_R1

/-- Large deficit: for some fixed r, the orders below 2^m that are not multiples of
2^(m-r) carry in total at most a quarter of the number of groups of order 2^(m-1). -/
def H1 : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∀ᶠ m : ℕ in atTop,
    4 * (∑ n ∈ (Finset.Ico 1 (2 ^ m)).filter (fun n => ¬ 2 ^ (m - r) ∣ n), g n)
      ≤ g (2 ^ (m - 1))

/-- Bounded deficit: for fixed r and fixed q < 2^r not a power of two, the order 2^k * q
eventually carries at most a 2^(-(r+2)) fraction of the groups of order 2^(k+r-1). -/
def H2 : Prop :=
  ∀ r q : ℕ, 0 < r → q < 2 ^ r → (∀ j : ℕ, q ≠ 2 ^ j) → ∀ᶠ k : ℕ in atTop,
    2 ^ (r + 2) * g (2 ^ k * q) ≤ g (2 ^ (k + r - 1))

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) :=
  Nat.pow_right_injective (le_refl 2)

lemma sum_union_le' (s t : Finset ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ s ∪ t, f n ≤ ∑ n ∈ s, f n + ∑ n ∈ t, f n := by
  rw [← Finset.sum_union_inter]
  exact Nat.le_add_right _ _

/-- Every order below 2^m lies in one of the three populations. -/
lemma cover (m r : ℕ) (hrm : r ≤ m) :
    Finset.Ico 1 (2 ^ m) ⊆
      ((Finset.range m).image (fun k => 2 ^ k) ∪
        (Finset.Ico 1 (2 ^ m)).filter (fun n => ¬ 2 ^ (m - r) ∣ n)) ∪
        ((Finset.range (2 ^ r)).filter (fun q => ∀ j ∈ Finset.range r, q ≠ 2 ^ j)).image
          (fun q => 2 ^ (m - r) * q) := by
  intro n hn
  have hn' := Finset.mem_Ico.mp hn
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  by_cases hp : ∃ k, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hp
    exact Or.inl (Or.inl ⟨k, (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hn'.2, rfl⟩)
  · by_cases hd : 2 ^ (m - r) ∣ n
    · obtain ⟨q, rfl⟩ := hd
      refine Or.inr ⟨q, ⟨?_, ?_⟩, rfl⟩
      · have h2 : 2 ^ m = 2 ^ (m - r) * 2 ^ r := by
          rw [← pow_add]; congr 1; omega
        have h3 := hn'.2
        rw [h2] at h3
        exact lt_of_mul_lt_mul_left h3 (Nat.zero_le _)
      · intro j _ hq
        apply hp
        exact ⟨m - r + j, by rw [hq, pow_add]⟩
    · exact Or.inl (Or.inr ⟨hn, hd⟩)

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1.H2 := by
  intro h1 h2
  obtain ⟨r, hr, hA⟩ := h1
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1.H2
  have hB : ∀ᶠ k : ℕ in atTop, ∀ q ∈ Finset.range (2 ^ r), (∀ j : ℕ, q ≠ 2 ^ j) →
      2 ^ (r + 2) * g (2 ^ k * q) ≤ g (2 ^ (k + r - 1)) := by
    rw [Finset.eventually_all]
    intro q hq
    by_cases hp : ∀ j : ℕ, q ≠ 2 ^ j
    · filter_upwards [h2 r q hr (Finset.mem_range.mp hq) hp] with k hk _ using hk
    · exact Filter.Eventually.of_forall (fun k h => absurd h hp)
  have hB' := (Filter.tendsto_sub_atTop_nat r).eventually hB
  filter_upwards [hA, hB', eventually_ge_atTop (r + 1)] with m hAm hBm hm
  set d := 2 ^ (m - r) with hd
  set P := ∑ k ∈ Finset.range m, g (2 ^ k) with hP
  set T1 := ∑ n ∈ (Finset.Ico 1 (2 ^ m)).filter (fun n => ¬ d ∣ n), g n with hT1
  set Q := (Finset.range (2 ^ r)).filter (fun q => ∀ j ∈ Finset.range r, q ≠ 2 ^ j) with hQ
  have hGP : g (2 ^ (m - 1)) ≤ P :=
    Finset.single_le_sum (f := fun k => g (2 ^ k)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : m - 1 < m))
  have hdpos : 0 < d := by positivity
  -- the bounded-deficit orders
  have hT2 : 2 ^ (r + 2) * (∑ q ∈ Q, g (d * q)) ≤ 2 ^ r * g (2 ^ (m - 1)) := by
    rw [Finset.mul_sum]
    calc ∑ q ∈ Q, 2 ^ (r + 2) * g (d * q)
        ≤ ∑ q ∈ Q, g (2 ^ (m - 1)) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [hQ, Finset.mem_filter] at hq
          have hne : ∀ j : ℕ, q ≠ 2 ^ j := by
            intro j hj
            by_cases hjr : j < r
            · exact hq.2 j (Finset.mem_range.mpr hjr) hj
            · have h1 := Finset.mem_range.mp hq.1
              rw [hj] at h1
              have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h1
              omega
          have h := hBm q hq.1 hne
          have he : m - r + r - 1 = m - 1 := by omega
          rw [he] at h
          exact h
      _ = Q.card * g (2 ^ (m - 1)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ r * g (2 ^ (m - 1)) := by
          apply Nat.mul_le_mul_right
          calc Q.card ≤ (Finset.range (2 ^ r)).card := Finset.card_filter_le _ _
            _ = 2 ^ r := Finset.card_range _
  have hT2' : 4 * (∑ q ∈ Q, g (d * q)) ≤ g (2 ^ (m - 1)) := by
    have h : 2 ^ r * (4 * (∑ q ∈ Q, g (d * q))) ≤ 2 ^ r * g (2 ^ (m - 1)) := by
      calc 2 ^ r * (4 * (∑ q ∈ Q, g (d * q))) = 2 ^ (r + 2) * (∑ q ∈ Q, g (d * q)) := by ring
        _ ≤ _ := hT2
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  -- the total
  have hS : ∑ n ∈ Finset.Ico 1 (2 ^ m), g n ≤ P + T1 + ∑ q ∈ Q, g (d * q) := by
    calc ∑ n ∈ Finset.Ico 1 (2 ^ m), g n
        ≤ ∑ n ∈ ((Finset.range m).image (fun k => 2 ^ k) ∪
            (Finset.Ico 1 (2 ^ m)).filter (fun n => ¬ d ∣ n)) ∪ Q.image (fun q => d * q), g n :=
          Finset.sum_le_sum_of_subset (cover m r (by omega))
      _ ≤ ∑ n ∈ ((Finset.range m).image (fun k => 2 ^ k) ∪
            (Finset.Ico 1 (2 ^ m)).filter (fun n => ¬ d ∣ n)), g n +
            ∑ n ∈ Q.image (fun q => d * q), g n := sum_union_le' _ _ _
      _ ≤ (∑ n ∈ (Finset.range m).image (fun k => 2 ^ k), g n + T1) +
            ∑ n ∈ Q.image (fun q => d * q), g n :=
          Nat.add_le_add_right (sum_union_le' _ _ _) _
      _ = P + T1 + ∑ q ∈ Q, g (d * q) := by
          rw [Finset.sum_image (fun a _ b _ hab => pow_two_injective hab),
            Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hdpos hab)]
  have hsub : ∀ a s : ℕ, 2 * (s - a) ≤ 2 * s := fun a s => by omega
  refine le_trans (hsub _ _) ?_
  omega

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1_H2_R1
