import FormalConjectures.ErdosProblems.«350»

-- Problem: Erdős Problem 350 — strengthening
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/350.lean:88 (declaration Erdos350.erdos_350.variants.strengthening)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA

open Finset

lemma tangent_aux {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : 1 - s * (t - 1) ≤ t ^ (-s) := by
  rcases le_or_gt 1 s with h1 | h1
  · have hx : (-1 : ℝ) ≤ 1 / t - 1 := by
      have : 0 < 1 / t := by positivity
      linarith
    have key := one_add_mul_self_le_rpow_one_add hx h1
    have e : (1 + (1 / t - 1)) ^ s = t ^ (-s) := by
      rw [show 1 + (1 / t - 1) = t⁻¹ by ring, Real.inv_rpow ht.le, Real.rpow_neg ht.le]
    rw [e] at key
    have h2 : 1 - t ≤ 1 / t - 1 := by
      rw [div_sub_one ht.ne', le_div_iff₀ ht]
      nlinarith [sq_nonneg (t - 1)]
    nlinarith
  · have hx : (-1 : ℝ) ≤ t - 1 := by linarith
    have key := rpow_one_add_le_one_add_mul_self hx hs.le h1.le
    rw [show 1 + (t - 1) = t by ring] at key
    have hy : 0 < 1 + s * (t - 1) := by nlinarith
    have hts : 0 < t ^ s := Real.rpow_pos_of_pos ht s
    rw [Real.rpow_neg ht.le]
    have : (1 + s * (t - 1))⁻¹ ≤ (t ^ s)⁻¹ := inv_anti₀ hts key
    have h3 : 1 - s * (t - 1) ≤ (1 + s * (t - 1))⁻¹ := by
      rw [← one_div, le_div_iff₀ hy]
      nlinarith [sq_nonneg (s * (t - 1))]
    linarith

lemma tangent {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) :
    a ^ (-s) ≤ b ^ (-s) + s * a ^ (-s - 1) * (b - a) := by
  have ht : 0 < b / a := div_pos hb ha
  have key := tangent_aux hs ht
  have hb' : b = a * (b / a) := by field_simp
  have e1 : b ^ (-s) = a ^ (-s) * (b / a) ^ (-s) := by
    conv_lhs => rw [hb']
    rw [Real.mul_rpow ha.le ht.le]
  have e2 : a ^ (-s - 1) = a ^ (-s) / a := Real.rpow_sub_one ha.ne' _
  have e3 : s * a ^ (-s - 1) * (b - a) = a ^ (-s) * (s * (b / a - 1)) := by
    rw [e2]; field_simp
  rw [e1, e3]
  have hpos : 0 < a ^ (-s) := Real.rpow_pos_of_pos ha _
  nlinarith

lemma abel_nonneg : ∀ (n : ℕ) (c d : ℕ → ℝ), (∀ i j, i ≤ j → j < n → c j ≤ c i) →
    (∀ i < n, 0 ≤ c i) → (∀ j ≤ n, 0 ≤ ∑ i ∈ range j, d i) →
    0 ≤ ∑ i ∈ range n, c i * d i := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro c d hc hc0 hd
    have e : ∑ i ∈ range (n + 1), c i * d i =
        ∑ i ∈ range n, (c i - c n) * d i + c n * ∑ i ∈ range (n + 1), d i := by
      simp only [sum_range_succ, sub_mul, sum_sub_distrib, mul_add, ← mul_sum]
      ring
    rw [e]
    have h1 : 0 ≤ ∑ i ∈ range n, (c i - c n) * d i := by
      apply ih (fun i => c i - c n) d
      · intro i j hij hj
        have := hc i j hij (by omega)
        linarith
      · intro i hi
        have := hc i n hi.le (by omega)
        show 0 ≤ c i - c n; linarith
      · intro j hj; exact hd j (by omega)
    have h2 : 0 ≤ c n * ∑ i ∈ range (n + 1), d i :=
      mul_nonneg (hc0 n (by omega)) (hd (n + 1) le_rfl)
    linarith

lemma two_pow_sum (j : ℕ) : ∑ i ∈ range j, (2 : ℝ) ^ i = 2 ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [sum_range_succ, ih, pow_succ]; ring

lemma subset_sum_ge (A : Finset ℕ) (hA : Finset.DecidableDistinctSubsetSums A)
    (T : Finset ℕ) (hT : T ⊆ A) : 2 ^ T.card ≤ T.sum id + 1 := by
  have := card_le_card_of_injOn (fun X : Finset ℕ => X.sum id) (s := T.powerset)
    (t := range (T.sum id + 1)) ?_ ?_
  · simpa using this
  · intro X hX
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hX
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (sum_le_sum_of_subset hX)
  · intro X hX Y hY hXY
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hX hY
    by_contra hne
    exact hA X (hX.trans hT) Y (hY.trans hT) hne hXY

lemma geom_lt {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∑ i ∈ range k, ((2 : ℝ) ^ i) ^ (-s) < 1 / (1 - 2 ^ (-s)) := by
  have hr0 : 0 < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have e : ∀ i : ℕ, ((2 : ℝ) ^ i) ^ (-s) = ((2 : ℝ) ^ (-s)) ^ i := by
    intro i
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  simp_rw [e]
  rw [geom_sum_eq hr1.ne]
  have hk : 0 < ((2 : ℝ) ^ (-s)) ^ k := pow_pos hr0 k
  have hd : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
  rw [show (((2 : ℝ) ^ (-s)) ^ k - 1) / ((2 : ℝ) ^ (-s) - 1) = (1 - ((2 : ℝ) ^ (-s)) ^ k) / (1 - (2 : ℝ) ^ (-s)) by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]]
  exact (div_lt_div_iff_of_pos_right hd).mpr (by linarith)

end OMA

open OMA Finset in
theorem OMA.solution : type_of% @Erdos350.erdos_350.variants.strengthening := by
  intro A hA s hs
  set k := A.card with hk
  set e := A.orderEmbOfFin rfl with he
  set a : ℕ → ℕ := fun i => if h : i < k then e ⟨i, h⟩ else 0 with ha
  have ha_mem : ∀ i < k, a i ∈ A := by
    intro i hi; simp only [ha, dif_pos hi]; exact orderEmbOfFin_mem A rfl _
  have ha_mono : ∀ i j, i < j → j < k → a i < a j := by
    intro i j hij hj
    simp only [ha, dif_pos hj, dif_pos (hij.trans hj)]
    exact e.strictMono (Fin.mk_lt_mk.mpr hij)
  have h0 : 0 ∉ A := by
    intro h
    exact hA ∅ (empty_subset _) {0} (singleton_subset_iff.mpr h) (by simp) (by simp)
  have ha_pos : ∀ i < k, (0 : ℝ) < a i := by
    intro i hi
    have := ha_mem i hi
    have : a i ≠ 0 := fun h' => h0 (h' ▸ this)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hsum : ∑ n ∈ A, (1 / (n : ℝ)) ^ s = ∑ i ∈ range k, ((a i : ℝ)) ^ (-s) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ((a i : ℝ)) ^ (-s))]
    conv_lhs => rw [← map_orderEmbOfFin_univ A rfl, sum_map]
    refine sum_congr rfl fun i _ => ?_
    have hai : a i = e i := by simp only [ha]; exact dif_pos i.isLt
    show (1 / ((e i : ℕ) : ℝ)) ^ s = ((a i : ℝ)) ^ (-s)
    rw [hai, one_div, Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
  have hpart : ∀ j ≤ k, (2 : ℝ) ^ j - 1 ≤ ∑ i ∈ range j, (a i : ℝ) := by
    intro j hj
    have hinj : Set.InjOn a (range j : Set ℕ) := by
      intro x hx y hy hxy
      simp only [coe_range, Set.mem_Iio] at hx hy
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd hxy (ha_mono x y h (by omega)).ne
      · exact absurd hxy (ha_mono y x h (by omega)).ne'
    have hT : (range j).image a ⊆ A := by
      intro x hx
      simp only [mem_image, mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact ha_mem i (by omega)
    have := subset_sum_ge A hA _ hT
    rw [card_image_of_injOn hinj, card_range, sum_image hinj] at this
    have : ((2 ^ j : ℕ) : ℝ) ≤ ((∑ x ∈ range j, id (a x) + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    simp only [id] at this
    linarith
  rw [hsum]
  refine lt_of_le_of_lt ?_ (geom_lt hs k)
  set c : ℕ → ℝ := fun i => s * (a i : ℝ) ^ (-s - 1) with hc
  set d : ℕ → ℝ := fun i => (a i : ℝ) - 2 ^ i with hd
  have habel := abel_nonneg k c d ?_ ?_ ?_
  · have h1 : ∑ i ∈ range k, ((a i : ℝ)) ^ (-s) ≤
        ∑ i ∈ range k, (((2 : ℝ) ^ i) ^ (-s) + s * (a i : ℝ) ^ (-s - 1) * (2 ^ i - a i)) := by
      apply sum_le_sum
      intro i hi
      exact tangent hs (ha_pos i (mem_range.mp hi)) (by positivity)
    have h2 : ∑ i ∈ range k, (((2 : ℝ) ^ i) ^ (-s) + s * (a i : ℝ) ^ (-s - 1) * (2 ^ i - a i)) =
        ∑ i ∈ range k, ((2 : ℝ) ^ i) ^ (-s) - ∑ i ∈ range k, c i * d i := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hc, hd]; ring
    linarith
  · intro i j hij hj
    simp only [hc]
    apply mul_le_mul_of_nonneg_left _ hs.le
    apply Real.rpow_le_rpow_of_nonpos (ha_pos i (by omega))
    · rcases hij.lt_or_eq with h | h
      · exact_mod_cast (ha_mono i j h hj).le
      · rw [h]
    · linarith
  · intro i hi
    simp only [hc]
    exact mul_nonneg hs.le (Real.rpow_pos_of_pos (ha_pos i hi) _).le
  · intro j hj
    simp only [hd]
    rw [sum_sub_distrib, two_pow_sum]
    linarith [hpart j hj]
