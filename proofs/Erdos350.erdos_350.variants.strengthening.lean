import FormalConjectures.ErdosProblems.«350»

-- Problem: Erdős Problem 350 — strengthening
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/350.lean:88 (declaration Erdos350.erdos_350.variants.strengthening)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA350

/-- Abel summation: nonnegative antitone weights preserve nonnegative prefix sums. -/
lemma abel (x : ℕ → ℝ) : ∀ (n : ℕ) (c : ℕ → ℝ),
    (∀ i j, i ≤ j → j < n → c j ≤ c i) → (∀ i, i < n → 0 ≤ c i) →
    (∀ j, j ≤ n → 0 ≤ ∑ i ∈ Finset.range j, x i) →
    0 ≤ ∑ i ∈ Finset.range n, c i * x i := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro c hc hc0 hx
    have key : ∑ i ∈ Finset.range (n+1), c i * x i =
        ∑ i ∈ Finset.range n, (c i - c n) * x i +
          c n * ∑ i ∈ Finset.range (n+1), x i := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, Finset.mul_sum]
      simp only [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    rw [key]
    apply add_nonneg
    · apply ih (fun i => c i - c n)
      · intro i j hij hjn
        have := hc i j hij (by omega)
        show c j - c n ≤ c i - c n
        linarith
      · intro i hi
        have := hc i n (by omega) (by omega)
        show 0 ≤ c i - c n
        linarith
      · intro j hj
        exact hx j (by omega)
    · exact mul_nonneg (hc0 n (by omega)) (hx (n+1) le_rfl)

/-- Tangent line inequality for the convex function `x ↦ (1/x)^s`. -/
lemma tangent {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    (1 / a) ^ s ≤ (1 / b) ^ s + s * ((1 / a) ^ s / a) * (b - a) := by
  have hu : 0 < a / b := div_pos ha hb
  have h1 : (1 / b) ^ s = (1 / a) ^ s * (a / b) ^ s := by
    rw [← Real.mul_rpow (by positivity) hu.le]
    congr 1
    field_simp
  have h2 : 1 + s * Real.log (a / b) ≤ (a / b) ^ s := by
    rw [Real.rpow_def_of_pos hu]
    have := Real.add_one_le_exp (Real.log (a / b) * s)
    linarith [mul_comm s (Real.log (a / b))]
  have h3 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have h4 : Real.log (a / b) = - Real.log (b / a) := by
    rw [← Real.log_inv, inv_div]
  have hA : 0 < (1 / a) ^ s := by positivity
  have h5 : 1 - s * (b / a - 1) ≤ (a / b) ^ s := by
    rw [h4] at h2
    nlinarith
  rw [h1]
  have h6 : s * ((1 / a) ^ s / a) * (b - a) = (1 / a) ^ s * (s * (b / a - 1)) := by
    rw [div_sub_one ha.ne']
    ring
  rw [h6]
  have := mul_le_mul_of_nonneg_left h5 hA.le
  nlinarith

lemma geom2 (j : ℕ) : ∑ i ∈ Finset.range j, (2 : ℝ) ^ i + 1 = 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

end OMA350

theorem OMA.solution : type_of% @Erdos350.erdos_350.variants.strengthening := by
  intro A hA s hs
  classical
  have hA' : ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → X.sum id ≠ Y.sum id := hA
  let f : ℕ → ℕ := fun i => if h : i < A.card then A.orderEmbOfFin rfl ⟨i, h⟩ else 0
  have hf_mem : ∀ i, i < A.card → f i ∈ A := by
    intro i h
    simp only [f, dif_pos h]
    exact Finset.orderEmbOfFin_mem A rfl _
  have hf_mono : ∀ i j, i < j → j < A.card → f i < f j := by
    intro i j hij hj
    simp only [f, dif_pos hj, dif_pos (hij.trans hj)]
    exact (A.orderEmbOfFin rfl).strictMono (by simpa [Fin.lt_def] using hij)
  have hsum : ∀ g : ℕ → ℝ, ∑ a ∈ A, g a = ∑ i ∈ Finset.range A.card, g (f i) := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun i => g (f i))]
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ A rfl]
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    simp [f, i.isLt]
  have h0 : (0 : ℕ) ∉ A := by
    intro h0
    exact hA' {0} (by simpa using h0) ∅ (Finset.empty_subset _) (by simp) (by simp)
  have hfpos : ∀ i, i < A.card → (0 : ℝ) < f i := by
    intro i h
    have hm := hf_mem i h
    have : f i ≠ 0 := fun h' => h0 (h' ▸ hm)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hinj : ∀ j, j ≤ A.card → Set.InjOn f (Finset.range j : Set ℕ) := by
    intro j hj i hi k hk hik
    simp only [Finset.coe_range, Set.mem_Iio] at hi hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hf_mono i k h (by omega)
      omega
    · have := hf_mono k i h (by omega)
      omega
  have hprefix : ∀ j, j ≤ A.card →
      (2 : ℝ) ^ j ≤ ∑ i ∈ Finset.range j, (f i : ℝ) + 1 := by
    intro j hj
    set B := (Finset.range j).image f with hB
    have hBA : B ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hf_mem i (by simp at hi; omega)
    have hBcard : B.card = j := by
      rw [hB, Finset.card_image_of_injOn (hinj j hj), Finset.card_range]
    have hBsum : B.sum id = ∑ i ∈ Finset.range j, f i := by
      rw [hB, Finset.sum_image (fun x hx y hy h => hinj j hj hx hy h)]
      rfl
    have hmap : B.powerset.image (fun X => X.sum id) ⊆ Finset.range (B.sum id + 1) := by
      intro t ht
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.mem_range]
      have := Finset.sum_le_sum_of_subset (f := id) (Finset.mem_powerset.mp hX)
      exact Nat.lt_succ_of_le this
    have hcard : (B.powerset.image (fun X => X.sum id)).card = 2 ^ j := by
      rw [Finset.card_image_of_injOn, Finset.card_powerset, hBcard]
      intro X hX Y hY hXY
      by_contra hne
      exact hA' X ((Finset.mem_powerset.mp (Finset.mem_coe.mp hX)).trans hBA)
        Y ((Finset.mem_powerset.mp (Finset.mem_coe.mp hY)).trans hBA) hne hXY
    have := Finset.card_le_card hmap
    rw [hcard, Finset.card_range, hBsum] at this
    exact_mod_cast this
  -- the weights
  let c : ℕ → ℝ := fun i => s * ((1 / (f i : ℝ)) ^ s / f i)
  let x : ℕ → ℝ := fun i => (f i : ℝ) - 2 ^ i
  have habel : 0 ≤ ∑ i ∈ Finset.range A.card, c i * x i := by
    apply OMA350.abel x A.card c
    · intro i j hij hjn
      have hfi := hfpos i (by omega)
      have hfij : (f i : ℝ) ≤ f j := by
        rcases eq_or_lt_of_le hij with h | h
        · rw [h]
        · exact_mod_cast (hf_mono i j h hjn).le
      simp only [c]
      have h1 : 1 / (f j : ℝ) ≤ 1 / f i := one_div_le_one_div_of_le hfi hfij
      have h2 : (1 / (f j : ℝ)) ^ s ≤ (1 / (f i : ℝ)) ^ s :=
        Real.rpow_le_rpow (by positivity) h1 hs.le
      have h3 : (1 / (f j : ℝ)) ^ s / f j ≤ (1 / (f i : ℝ)) ^ s / f i := by
        calc (1 / (f j : ℝ)) ^ s / f j ≤ (1 / (f j : ℝ)) ^ s / f i :=
              div_le_div_of_nonneg_left (by positivity) hfi hfij
          _ ≤ (1 / (f i : ℝ)) ^ s / f i := div_le_div_of_nonneg_right h2 hfi.le
      exact mul_le_mul_of_nonneg_left h3 hs.le
    · intro i hi
      simp only [c]
      positivity
    · intro j hj
      simp only [x]
      rw [Finset.sum_sub_distrib]
      have := hprefix j hj
      have := OMA350.geom2 j
      linarith
  have hstep : ∑ i ∈ Finset.range A.card, (1 / (f i : ℝ)) ^ s ≤
      ∑ i ∈ Finset.range A.card, ((1 / (2 : ℝ) ^ i) ^ s + c i * ((2 : ℝ) ^ i - f i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact OMA350.tangent (hfpos i (Finset.mem_range.mp hi)) (by positivity) hs
  have hsplit : ∑ i ∈ Finset.range A.card, ((1 / (2 : ℝ) ^ i) ^ s + c i * ((2 : ℝ) ^ i - f i))
      = ∑ i ∈ Finset.range A.card, (1 / (2 : ℝ) ^ i) ^ s -
        ∑ i ∈ Finset.range A.card, c i * x i := by
    rw [Finset.sum_add_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [x]
    ring
  set r : ℝ := (2 : ℝ) ^ (-s) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ i : ℕ, (1 / (2 : ℝ) ^ i) ^ s = r ^ i := by
    intro i
    rw [hr, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.inv_rpow (by norm_num),
      Real.rpow_pow_comm (by norm_num), one_div, inv_pow]
  have hgeom : ∑ i ∈ Finset.range A.card, (1 / (2 : ℝ) ^ i) ^ s < 1 / (1 - r) := by
    simp only [hpow]
    rw [lt_div_iff₀ (by linarith)]
    have := geom_sum_mul r A.card
    have := pow_pos hr0 A.card
    nlinarith
  rw [hsum (fun n => (1 / (n : ℝ)) ^ s)]
  linarith
