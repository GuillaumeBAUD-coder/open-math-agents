import FormalConjectures.ErdosProblems.«882»

-- Problem: Erdős Problem 882 — greedy
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/882.lean:152 (declaration Erdos882.erdos_882.variants.greedy)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA882

/-- popcount -/
def pc (n : ℕ) : ℕ := n.bitIndices.length

lemma pc_two_mul (n : ℕ) : pc (2 * n) = pc n := by simp [pc]

lemma pc_two_mul_add_one (n : ℕ) : pc (2 * n + 1) = pc n + 1 := by simp [pc]

lemma pc_succ_le : ∀ x : ℕ, pc (x + 1) ≤ pc x + 1 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    obtain ⟨y, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [pc_two_mul_add_one, pc_two_mul]
    · have h : 2 * y + 1 + 1 = 2 * (y + 1) := by ring
      rw [h, pc_two_mul, pc_two_mul_add_one]
      rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp [pc]
      · have := ih y (by omega)
        omega

lemma pc_add_two_pow (t : ℕ) : ∀ x : ℕ, pc (x + 2 ^ t) ≤ pc x + 1 := by
  induction t with
  | zero => intro x; simpa using pc_succ_le x
  | succ s ih =>
    intro x
    obtain ⟨y, rfl | rfl⟩ := Nat.even_or_odd' x
    · have h : 2 * y + 2 ^ (s + 1) = 2 * (y + 2 ^ s) := by ring
      rw [h, pc_two_mul, pc_two_mul]; exact ih y
    · have h : 2 * y + 1 + 2 ^ (s + 1) = 2 * (y + 2 ^ s) + 1 := by ring
      rw [h, pc_two_mul_add_one, pc_two_mul_add_one]; have := ih y; omega

lemma pc_add_list (x : ℕ) (L : List ℕ) : pc (x + (L.map (fun t => 2 ^ t)).sum) ≤ pc x + L.length := by
  induction L generalizing x with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := ih (x + 2 ^ a)
    have h2 := pc_add_two_pow a x
    rw [← add_assoc]; omega

lemma pc_add (x y : ℕ) : pc (x + y) ≤ pc x + pc y := by
  have h := pc_add_list x y.bitIndices
  rwa [Nat.sum_map_two_pow_bitIndices] at h

lemma pc_sum_finset (s : Finset ℕ) : pc (∑ i ∈ s, 2 ^ i) = s.card := by
  have h := Finset.toFinset_bitIndices_sum_two_pow s
  unfold pc
  conv_rhs => rw [← h]
  rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup]

lemma pc_lt (q : ℕ) (hq : 2 ≤ q) : pc q < q := by
  have hs := Finset.sum_toFinset_bitIndices_two_pow q
  set s := q.bitIndices.toFinset
  have hc : pc q = s.card := by
    unfold pc; rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  rw [hc]
  by_cases h1 : s.card ≤ 1
  · omega
  · have : ∃ i ∈ s, i ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      have : s ⊆ {0} := fun i hi => by simp [hne i hi]
      have := Finset.card_le_card this
      simp at this; omega
    obtain ⟨i, hi, hi0⟩ := this
    have hle : ∀ j ∈ s, 1 ≤ 2 ^ j := fun j _ => Nat.one_le_two_pow
    have hsum : ∑ j ∈ s, 1 < ∑ j ∈ s, 2 ^ j := by
      apply Finset.sum_lt_sum hle ⟨i, hi, ?_⟩
      exact Nat.one_lt_two_pow hi0
    simp at hsum; omega

lemma pc_mul_two_pow (q i : ℕ) : pc (q * 2 ^ i) = pc q := by
  unfold pc; rw [mul_comm, Nat.bitIndices_two_pow_mul, List.length_map]

lemma pc_mul_sum (q : ℕ) (s : Finset ℕ) : pc (q * ∑ i ∈ s, 2 ^ i) ≤ pc q * s.card := by
  induction s using Finset.induction_on with
  | empty => simp [pc]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, mul_add, Finset.card_insert_of_notMem ha]
    have := pc_add (q * 2 ^ a) (q * ∑ i ∈ s, 2 ^ i)
    rw [pc_mul_two_pow] at this
    nlinarith

lemma geom_lt (k : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range k) : ∑ i ∈ I, 2 ^ i < 2 ^ k := by
  calc ∑ i ∈ I, 2 ^ i ≤ ∑ i ∈ Finset.range k, 2 ^ i := Finset.sum_le_sum_of_subset hI
    _ < 2 ^ k := by
      have := Nat.geomSum_eq (le_refl 2) k
      rw [this]; have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega

lemma core (k : ℕ) (I1 I2 : Finset ℕ) (h1 : I1 ⊆ Finset.range k) (h2 : I2 ⊆ Finset.range k)
    (hn1 : I1.Nonempty) (hn2 : I2.Nonempty) (hne : I1 ≠ I2) :
    ¬ (∑ i ∈ I1, 2 ^ i + I1.card * (k * 2 ^ k)) ∣ (∑ i ∈ I2, 2 ^ i + I2.card * (k * 2 ^ k)) := by
  rintro ⟨q, hq⟩
  set E1 := ∑ i ∈ I1, 2 ^ i with hE1
  set E2 := ∑ i ∈ I2, 2 ^ i with hE2
  set j1 := I1.card with hj1
  set j2 := I2.card with hj2
  set T := k * 2 ^ k with hT
  have hE1lt : E1 < 2 ^ k := geom_lt k I1 h1
  have hE2lt : E2 < 2 ^ k := geom_lt k I2 h2
  have hj1pos : 1 ≤ j1 := Finset.card_pos.mpr hn1
  have hj2pos : 1 ≤ j2 := Finset.card_pos.mpr hn2
  have hj1k : j1 ≤ k := by simpa using Finset.card_le_card h1
  have hj2k : j2 ≤ k := by simpa using Finset.card_le_card h2
  have hk : 1 ≤ k := le_trans hj1pos hj1k
  have hTge : 2 ^ k ≤ T := by rw [hT]; nlinarith [Nat.one_le_two_pow (n := k)]
  have heq : E2 + j2 * T = q * E1 + q * j1 * T := by rw [hq]; ring
  rcases lt_trichotomy (q * j1) j2 with hlt | hqe | hgt
  · -- q * j1 < j2
    have hqk : q ≤ k := by
      have : q ≤ q * j1 := Nat.le_mul_of_pos_right q hj1pos
      omega
    have h3 : q * E1 ≤ k * E1 := Nat.mul_le_mul_right E1 hqk
    have h4 : k * E1 < T := by rw [hT]; exact Nat.mul_lt_mul_of_pos_left hE1lt (by omega)
    have h5 : (q * j1 + 1) * T ≤ j2 * T := Nat.mul_le_mul_right T hlt
    nlinarith
  · -- q * j1 = j2
    have hE : E2 = q * E1 := by
      have : q * j1 * T = j2 * T := by rw [hqe]
      omega
    rcases Nat.lt_or_ge q 2 with hq2 | hq2
    · interval_cases q
      · simp at hqe; omega
      · apply hne
        have : E1 = E2 := by rw [hE]; ring
        rw [← Finset.toFinset_bitIndices_sum_two_pow I1, ← Finset.toFinset_bitIndices_sum_two_pow I2]
        rw [← hE1, ← hE2, this]
    · have a1 := pc_sum_finset I2
      have a2 := pc_mul_sum q I1
      have a3 := pc_lt q hq2
      rw [← hE2, hE] at a1
      rw [← hE1] at a2
      have b1 : pc (q * E1) = j2 := a1
      have b2 : pc (q * E1) ≤ pc q * j1 := a2
      have : pc q * j1 < q * j1 := Nat.mul_lt_mul_of_pos_right a3 hj1pos
      omega
  · -- q * j1 > j2
    have h5 : (j2 + 1) * T ≤ q * j1 * T := Nat.mul_le_mul_right T hgt
    nlinarith

lemma pow_bound (k : ℕ) (hk : 4 ≤ k) : (k + 1) * 2 ^ k ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.one_le_two_pow (n := k)]

lemma antichain (k : ℕ) :
    Erdos882.IsSubsetSumAntichain
      ((Finset.range k).image (fun i => 2 ^ i + k * 2 ^ k)) := by
  have hinj : Function.Injective (fun i : ℕ => 2 ^ i + k * 2 ^ k) := by
    intro a b h
    simp only [add_left_inj] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have hsum : ∀ I : Finset ℕ, ∑ x ∈ I.image (fun i => 2 ^ i + k * 2 ^ k), x =
      ∑ i ∈ I, 2 ^ i + I.card * (k * 2 ^ k) := by
    intro I
    rw [Finset.sum_image (fun a _ b _ h => hinj h), Finset.sum_add_distrib]
    simp
  intro S1 hS1 S2 hS2 hn1 hn2 hne
  obtain ⟨I1, hI1, rfl⟩ := Finset.subset_image_iff.mp hS1
  obtain ⟨I2, hI2, rfl⟩ := Finset.subset_image_iff.mp hS2
  rw [hsum, hsum]
  refine core k I1 I2 hI1 hI2 (by simpa using hn1) (by simpa using hn2) ?_
  rintro rfl; exact hne rfl

end OMA882

theorem OMA.solution : type_of% @Erdos882.erdos_882.variants.greedy := by
  rw [Filter.eventually_atTop]
  refine ⟨81, fun n hn => ?_⟩
  set k := Nat.log 3 n with hk
  have hk4 : 4 ≤ k := by
    rw [hk]; exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hkn : 3 ^ k ≤ n := Nat.pow_log_le_self 3 (by omega)
  have hnk : n < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  set A := (Finset.range k).image (fun i => 2 ^ i + k * 2 ^ k) with hA
  have hcard : A.card = k := by
    rw [hA, Finset.card_image_of_injective]
    · simp
    · intro a b h
      simp only [add_left_inj] at h
      exact Nat.pow_right_injective (le_refl 2) h
  have hsub : A ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [hA, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    have h1 : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hi.le
    have h2 := OMA882.pow_bound k hk4
    rw [Finset.mem_Icc]
    constructor
    · have := Nat.one_le_two_pow (n := i); omega
    · nlinarith
  have hle : k ≤ Erdos882.maxAntichainCard n := by
    apply le_csSup
    · refine ⟨n, ?_⟩
      rintro m ⟨B, hB, -, rfl⟩
      simpa using Finset.card_le_card hB
    · exact ⟨A, hsub, OMA882.antichain k, hcard⟩
  have hlog : Real.logb 3 n < k + 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast (show 0 < n by omega))]
    have : ((3 : ℝ) ^ ((k : ℝ) + 1)) = ((3 ^ (k + 1) : ℕ) : ℝ) := by
      rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      push_cast; ring
    rw [this]; exact_mod_cast hnk
  have : (k : ℝ) ≤ (Erdos882.maxAntichainCard n : ℝ) := by exact_mod_cast hle
  linarith
