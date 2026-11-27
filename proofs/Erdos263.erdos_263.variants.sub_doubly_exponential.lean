import FormalConjectures.ErdosProblems.«263»

-- Problem: Erdős Problem 263 — sub doubly exponential
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/263.lean:104 (declaration Erdos263.erdos_263.variants.sub_doubly_exponential)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology

namespace OMA263

/-- Tail sums of a summable sequence of reals. -/
lemma tail_step (f : ℕ → ℝ) (hf : Summable f) (n : ℕ) :
    ∑' k, f (k + n) = f n + ∑' k, f (k + (n + 1)) := by
  have hs : Summable (fun k => f (k + n)) := (summable_nat_add_iff n).2 hf
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  refine tsum_congr (fun k => ?_)
  congr 1
  omega

lemma ceil_bounds {D : ℝ} (hD : 0 < D) :
    0 ≤ D - 1 / (⌈1 / D⌉₊ : ℝ) ∧ D - 1 / (⌈1 / D⌉₊ : ℝ) ≤ D ^ 2 := by
  have h1 : 1 / D ≤ (⌈1 / D⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈1 / D⌉₊ : ℝ) < 1 / D + 1 := Nat.ceil_lt_add_one (by positivity)
  have hpos : 0 < (⌈1 / D⌉₊ : ℝ) := lt_of_lt_of_le (by positivity) h1
  constructor
  · have : 1 / (⌈1 / D⌉₊ : ℝ) ≤ D := by
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hD] at h1
      linarith
    linarith
  · have h3 : D / (1 + D) ≤ 1 / (⌈1 / D⌉₊ : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hpos]
      have : (⌈1 / D⌉₊ : ℝ) * D < 1 + D := by
        have h5 := mul_lt_mul_of_pos_right h2 hD
        have e5 : (1 / D + 1) * D = 1 + D := by field_simp
        linarith
      nlinarith
    have h4 : D - D / (1 + D) ≤ D ^ 2 := by
      have e : D - D / (1 + D) = D ^ 2 / (1 + D) := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg D]
    linarith

end OMA263

open OMA263 in
theorem OMA.solution : type_of% @Erdos263.erdos_263.variants.sub_doubly_exponential := by
  intro a ha' ha'' ha'''
  rintro ⟨hpos, -, hirr⟩
  set A : ℕ → ℝ := fun n => (a n : ℝ) with hAdef
  have hA1 : ∀ n, 1 ≤ A n := fun n => by
    show (1 : ℝ) ≤ (a n : ℝ); exact_mod_cast hpos n
  have hA0 : ∀ n, 0 < A n := fun n => lt_of_lt_of_le one_pos (hA1 n)
  -- tails
  set t : ℕ → ℝ := fun n => ∑' k, 1 / A (k + n) with htdef
  have ht_step : ∀ n, t n = 1 / A n + t (n + 1) := fun n =>
    tail_step (fun k => 1 / A k) ha'' n
  have ht_lim : Tendsto t atTop (𝓝 0) := tendsto_sum_nat_add (fun k => 1 / A k)
  -- the growth condition
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (ha'''.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)))
  have hgrow : ∀ n ≥ N, 4 * A (n + 1) ≤ A n ^ 2 := by
    intro n hn
    have h : (a (n + 1) : ℝ) / (a n : ℝ) ^ 2 ≤ 1 / 4 := hN n hn
    have hp : (0 : ℝ) < (a n : ℝ) ^ 2 := pow_pos (hA0 n) 2
    rw [div_le_iff₀ hp] at h
    show 4 * (a (n + 1) : ℝ) ≤ (a n : ℝ) ^ 2
    linarith
  -- the target rational
  set S : ℝ := ∑ k ∈ Finset.range N, 1 / A k with hS
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show S + t N < S + t N + 1 / A N by have := hA0 N; linarith [one_div_pos.2 this])
  set r : ℝ := (q : ℝ) with hr
  -- the recursion
  let bf : ℕ → ℝ → ℕ := fun n x => if n < N then a n else ⌈1 / (x - t (n + 1))⌉₊
  let R : ℕ → ℝ := fun n => Nat.rec r (fun k x => x - 1 / (bf k x : ℝ)) n
  have hR0 : R 0 = r := rfl
  have hRs : ∀ n, R (n + 1) = R n - 1 / (bf n (R n) : ℝ) := fun n => rfl
  set b : ℕ → ℕ := fun n => bf n (R n) with hbdef
  -- partial sums
  have hpartial : ∀ n, ∑ k ∈ Finset.range n, 1 / (b k : ℝ) = r - R n := by
    intro n
    induction n with
    | zero => simp [hR0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hRs]
      ring
  -- before N
  have hbefore : ∀ n ≤ N, R n = r - ∑ k ∈ Finset.range n, 1 / A k := by
    intro n hn
    induction n with
    | zero => simp [hR0]
    | succ n ih =>
      have hbn : bf n (R n) = a n := by simp [bf, show n < N by omega]
      rw [hRs, hbn, ih (by omega), Finset.sum_range_succ]
      ring
  -- main invariant: for n ≥ N, with e n = R n - t n
  have hinv : ∀ m, 0 ≤ R (N + m) - t (N + m) ∧
      (R (N + m) - t (N + m)) + 1 / A (N + m) ≤ 2 / A (N + m) ∧
      (1 ≤ m → R (N + m) - t (N + m) ≤ 4 / A (N + m - 1) ^ 2) := by
    intro m
    induction m with
    | zero =>
      have hRN := hbefore N le_rfl
      rw [← hS] at hRN
      simp only [add_zero]
      refine ⟨by rw [hRN]; linarith, ?_, fun h => absurd h (by norm_num)⟩
      rw [hRN]
      have : 2 / A N = 1 / A N + 1 / A N := by ring
      linarith
    | succ m ih =>
      obtain ⟨he, hD, -⟩ := ih
      set n := N + m with hn
      have hDpos : 0 < R n - t (n + 1) := by
        rw [ht_step n] at he
        have := one_div_pos.2 (hA0 n)
        linarith
      have hb : bf n (R n) = ⌈1 / (R n - t (n + 1))⌉₊ := by
        simp [bf, show ¬ n < N by omega]
      obtain ⟨c1, c2⟩ := ceil_bounds hDpos
      have hstep : R (n + 1) - t (n + 1) = (R n - t (n + 1)) - 1 / (bf n (R n) : ℝ) := by
        rw [hRs]; ring
      rw [← hb] at c1 c2
      have hDle : R n - t (n + 1) ≤ 2 / A n := by
        rw [ht_step n] at hD
        linarith
      have hsq : (R n - t (n + 1)) ^ 2 ≤ 4 / A n ^ 2 := by
        have : (R n - t (n + 1)) ^ 2 ≤ (2 / A n) ^ 2 := pow_le_pow_left₀ hDpos.le hDle 2
        rw [div_pow] at this
        linarith
      have hg := hgrow n (by omega)
      have hkey : 4 / A n ^ 2 ≤ 1 / A (n + 1) := by
        rw [div_le_div_iff₀ (pow_pos (hA0 n) 2) (hA0 _)]
        linarith
      have hn1 : N + (m + 1) = n + 1 := by omega
      rw [hn1]
      refine ⟨by rw [hstep]; exact c1, ?_, fun _ => ?_⟩
      · rw [hstep]
        have : 2 / A (n + 1) = 1 / A (n + 1) + 1 / A (n + 1) := by ring
        linarith
      · rw [hstep, show n + 1 - 1 = n by omega]
        linarith
  -- positivity of b
  have hbpos : ∀ n, b n > 0 := by
    intro n
    by_cases hn : n < N
    · simp only [hbdef, bf, if_pos hn]; exact hpos n
    · simp only [hbdef, bf, if_neg hn]
      obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
      obtain ⟨he, -, -⟩ := hinv m
      rw [ht_step] at he
      have := one_div_pos.2 (hA0 (N + m))
      exact Nat.ceil_pos.2 (one_div_pos.2 (by linarith))
  -- e n → 0 along the shift
  have hA_top : Tendsto A atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    simp only [hAdef]; exact_mod_cast ha'.le_apply
  have hratio0 : Tendsto (fun n => A (n + 1) / A n ^ 2) atTop (𝓝 0) := ha'''
  have hAe : Tendsto (fun m => A (N + m + 1) * (R (N + m + 1) - t (N + m + 1))) atTop (𝓝 0) := by
    have hup : Tendsto (fun m => 4 * (A (N + m + 1) / A (N + m) ^ 2)) atTop (𝓝 0) := by
      have := (hratio0.comp (tendsto_add_atTop_nat N)).const_mul 4
      simpa [Function.comp, add_comm] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_)
      (fun m => ?_)
    · obtain ⟨he, -, -⟩ := hinv (m + 1)
      rw [← add_assoc] at he
      exact mul_nonneg (hA0 _).le he
    · obtain ⟨-, -, h3⟩ := hinv (m + 1)
      have h3 := h3 (by omega)
      rw [← add_assoc, show N + m + 1 - 1 = N + m by omega] at h3
      have := mul_le_mul_of_nonneg_left h3 (hA0 (N + m + 1)).le
      calc A (N + m + 1) * (R (N + m + 1) - t (N + m + 1))
          ≤ A (N + m + 1) * (4 / A (N + m) ^ 2) := this
        _ = 4 * (A (N + m + 1) / A (N + m) ^ 2) := by ring
  -- ratio a / b → 1
  have hratio : Tendsto (fun n => (a n : ℝ) / (b n : ℝ)) atTop (𝓝 1) := by
    rw [← tendsto_add_atTop_iff_nat (N + 1)]
    have hlow : Tendsto (fun m => A (m + (N + 1)) / (A (m + (N + 1)) + 1)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun m => A (m + (N + 1))) atTop atTop :=
        hA_top.comp (tendsto_add_atTop_nat (N + 1))
      have h2 : Tendsto (fun m => 1 - 1 / (A (m + (N + 1)) + 1)) atTop (𝓝 (1 - 0)) := by
        refine tendsto_const_nhds.sub ?_
        exact (tendsto_atTop_add_const_right _ 1 h1).inv_tendsto_atTop.congr
          (fun m => by simp [one_div])
      rw [sub_zero] at h2
      refine h2.congr (fun m => ?_)
      have := hA0 (m + (N + 1))
      field_simp
      ring
    have hupp : Tendsto (fun m => 1 + A (N + m + 1) * (R (N + m + 1) - t (N + m + 1)))
        atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hAe
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow (hupp.congr (fun m => by
      rw [show N + m + 1 = m + (N + 1) by omega])) (fun m => ?_) (fun m => ?_)
    · -- lower bound
      set n := m + (N + 1) with hn
      obtain ⟨he, hD, -⟩ := hinv (m + 1)
      rw [show N + (m + 1) = n by omega] at he hD
      have hDpos : 0 < R n - t (n + 1) := by
        rw [ht_step n] at he; have := one_div_pos.2 (hA0 n); linarith
      have hb : (b n : ℝ) = ⌈1 / (R n - t (n + 1))⌉₊ := by
        simp [hbdef, bf, show ¬ n < N by omega]
      have hle : 1 / A n ≤ R n - t (n + 1) := by rw [ht_step n] at he; linarith
      have hc : (b n : ℝ) < A n + 1 := by
        rw [hb]
        have := Nat.ceil_lt_add_one (show 0 ≤ 1 / (R n - t (n + 1)) by positivity)
        have h2 : 1 / (R n - t (n + 1)) ≤ A n := by
          rw [div_le_iff₀ hDpos]
          rw [div_le_iff₀ (hA0 n)] at hle
          linarith
        linarith
      have hbp : (0 : ℝ) < b n := by exact_mod_cast hbpos n
      show A n / (A n + 1) ≤ (a n : ℝ) / (b n : ℝ)
      rw [div_le_div_iff₀ (by linarith [hA0 n]) hbp]
      simp only [hAdef]
      have := hA0 n
      nlinarith
    · -- upper bound
      set n := m + (N + 1) with hn
      obtain ⟨he, -, -⟩ := hinv (m + 1)
      rw [show N + (m + 1) = n by omega] at he
      have hDpos : 0 < R n - t (n + 1) := by
        rw [ht_step n] at he; have := one_div_pos.2 (hA0 n); linarith
      have hb : (b n : ℝ) = ⌈1 / (R n - t (n + 1))⌉₊ := by
        simp [hbdef, bf, show ¬ n < N by omega]
      have hbge : 1 / (R n - t (n + 1)) ≤ (b n : ℝ) := by rw [hb]; exact Nat.le_ceil _
      have hbp : (0 : ℝ) < b n := by exact_mod_cast hbpos n
      show (a n : ℝ) / (b n : ℝ) ≤ 1 + A n * (R n - t n)
      rw [div_le_iff₀ hbp]
      have e1 : R n - t (n + 1) = (R n - t n) + 1 / A n := by rw [ht_step n]; ring
      rw [div_le_iff₀ hDpos] at hbge
      have hAn := hA0 n
      have h4 : A n * (R n - t (n + 1)) = 1 + A n * (R n - t n) := by
        rw [e1]; field_simp; ring
      have h2 : A n ≤ (1 + A n * (R n - t n)) * b n := by
        have h3 : 1 ≤ (R n - t (n + 1)) * b n := by linarith
        calc A n = A n * 1 := by ring
          _ ≤ A n * ((R n - t (n + 1)) * b n) := mul_le_mul_of_nonneg_left h3 hAn.le
          _ = (A n * (R n - t (n + 1))) * b n := by ring
          _ = (1 + A n * (R n - t n)) * b n := by rw [h4]
      simpa [hAdef] using h2
  -- the sum is r
  have hR_lim : Tendsto R atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat (N + 1)]
    have he : Tendsto (fun m => R (m + (N + 1)) - t (m + (N + 1))) atTop (𝓝 0) := by
      have hupp : Tendsto (fun m => 4 * (A (N + m + 1) / A (N + m) ^ 2)) atTop (𝓝 0) := by
        have := (hratio0.comp (tendsto_add_atTop_nat N)).const_mul 4
        simpa [Function.comp, add_comm] using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp (fun m => ?_)
        (fun m => ?_)
      · obtain ⟨he, -, -⟩ := hinv (m + 1)
        rw [show N + (m + 1) = m + (N + 1) by omega] at he
        exact he
      · obtain ⟨-, -, h3⟩ := hinv (m + 1)
        have h3 := h3 (by omega)
        rw [show N + (m + 1) = m + (N + 1) by omega,
          show m + (N + 1) - 1 = N + m by omega] at h3
        refine h3.trans ?_
        have hA := hA1 (N + m + 1)
        rw [show N + m + 1 = m + (N + 1) by omega] at hA ⊢
        have hp : 0 < A (N + m) ^ 2 := by have := hA0 (N + m); positivity
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hp]
        linarith
    have htt : Tendsto (fun m => t (m + (N + 1))) atTop (𝓝 0) :=
      ht_lim.comp (tendsto_add_atTop_nat (N + 1))
    simpa using he.add htt
  have hsum : HasSum (fun n => 1 / (b n : ℝ)) r := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
    have := (tendsto_const_nhds (x := r)).sub hR_lim
    rw [sub_zero] at this
    exact this.congr (fun n => (hpartial n).symm)
  have := hirr b ⟨hbpos, hratio⟩
  rw [hsum.tsum_eq, hr] at this
  exact q.not_irrational this
