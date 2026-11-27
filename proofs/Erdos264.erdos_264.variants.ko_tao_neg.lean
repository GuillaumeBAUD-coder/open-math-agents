import FormalConjectures.ErdosProblems.«264»

/-! # Kovač–Tao: a summable, slowly thinning sequence is not an irrationality sequence

We follow the informal argument of Kovač and Tao (arXiv:2406.17593). Perturb each `a n` by an
integer `b n ∈ [1, 1 + D]`. When `a n ^ 2 * ∑_{k > n} 1 / a k ^ 2 ≥ C`, a large enough `D` makes
the set of reachable tail sums an interval that a greedy choice can keep hitting, so the tail can
be steered onto any rational target in its range. The prefix is rational as well, so the full sum
is rational. -/

open Filter

namespace OMA.KovacTao

/-- Some point of the grid `1/(A+c)`, `1 ≤ c ≤ 1+D`, lies in a long enough interval that meets
the range of the grid. -/
lemma grid (A : ℝ) (hA : 1 ≤ A) (D : ℕ) (x y : ℝ) (hxy : 1 / A ^ 2 ≤ y - x)
    (hx : x ≤ 1 / (A + 1)) (hy : 1 / (A + ((1 + D : ℕ) : ℝ)) ≤ y) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ 1 + D ∧ x ≤ 1 / (A + c) ∧ 1 / (A + c) ≤ y := by
  classical
  have hex : ∃ c : ℕ, 1 ≤ c ∧ 1 / (A + c) ≤ y := ⟨1 + D, by omega, hy⟩
  have hc : 1 ≤ Nat.find hex ∧ 1 / (A + (Nat.find hex : ℕ)) ≤ y := Nat.find_spec hex
  have hcle : Nat.find hex ≤ 1 + D := Nat.find_min' hex ⟨by omega, hy⟩
  refine ⟨Nat.find hex, hc.1, hcle, ?_, hc.2⟩
  rcases Nat.lt_or_ge 1 (Nat.find hex) with h1 | h1
  · have hprev : ¬ (1 ≤ Nat.find hex - 1 ∧ 1 / (A + ((Nat.find hex - 1 : ℕ) : ℝ)) ≤ y) :=
      Nat.find_min hex (by omega)
    have hprev' : y < 1 / (A + ((Nat.find hex - 1 : ℕ) : ℝ)) := by
      by_contra h
      exact hprev ⟨by omega, not_lt.mp h⟩
    have hcast : ((Nat.find hex - 1 : ℕ) : ℝ) = (Nat.find hex : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hcast] at hprev'
    have hc1 : (1 : ℝ) ≤ (Nat.find hex : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (Nat.find hex : ℝ) := by exact_mod_cast h1
      linarith
    have hp1 : 0 < A + ((Nat.find hex : ℝ) - 1) := by linarith
    have hp2 : 0 < A + (Nat.find hex : ℝ) := by linarith
    have hgap : 1 / (A + ((Nat.find hex : ℝ) - 1)) - 1 / (A + (Nat.find hex : ℝ)) ≤ 1 / A ^ 2 := by
      rw [div_sub_div _ _ hp1.ne' hp2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · have h : Nat.find hex = 1 := by omega
    rw [h]
    simpa using hx

theorem main {a : ℕ → ℕ} (h₁ : StrictMono a) (h₂ : 0 ∉ Set.range a)
    (h₃ : Summable ((1 : ℝ) / a ·))
    (h₄ : ∃ C > 0, ∀ᶠ n in atTop, C ≤ a n ^ 2 * ∑' k : Set.Ioi n, (1 : ℝ) / a k ^ 2) :
    ¬ (∀ b : ℕ → ℤ, BddAbove (Set.range b) → BddBelow (Set.range b) →
      0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) → 0 ∉ Set.range b →
      Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n))) := by
  intro hirr
  obtain ⟨C, hC, hev⟩ := h₄
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  have hapos : ∀ n, (1 : ℝ) ≤ a n := by
    intro n
    have : a n ≠ 0 := fun h => h₂ ⟨n, h⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  obtain ⟨D, hD⟩ := exists_nat_gt (6 / C)
  have hDpos : (0 : ℝ) < D := lt_trans (by positivity) hD
  have hDC : 6 < (D : ℝ) * C := by
    have := (div_lt_iff₀ hC).mp hD
    linarith
  obtain ⟨N, hN⟩ : ∃ N, N = max N0 (D + 1) := ⟨_, rfl⟩
  have hge : ∀ k, k ≤ a k := h₁.id_le
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℕ → ℝ, ∀ n c, t n c = 1 / ((a n : ℝ) + c) := ⟨_, fun _ _ => rfl⟩
  have ht_nonneg : ∀ n c, 0 ≤ t n c := fun n c => by rw [ht]; positivity
  have ht_le : ∀ n c, t n c ≤ 1 / (a n : ℝ) := by
    intro n c
    rw [ht]
    apply one_div_le_one_div_of_le (by linarith [hapos n])
    linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  have hsum : ∀ c, Summable (fun n => t n c) := fun c =>
    Summable.of_nonneg_of_le (ht_nonneg · c) (ht_le · c) h₃
  have hsumS : ∀ c m, Summable (fun j => t (j + m) c) := fun c m =>
    (summable_nat_add_iff m).mpr (hsum c)
  obtain ⟨tl, htl⟩ : ∃ tl : ℕ → ℕ → ℝ, ∀ c n, tl c n = ∑' j, t (j + n) c := ⟨_, fun _ _ => rfl⟩
  have hsplit : ∀ c n, tl c n = t n c + tl c (n + 1) := by
    intro c n
    rw [htl, htl, (hsumS c n).tsum_eq_zero_add]
    have : ∀ j, j + 1 + n = j + (n + 1) := by intro j; omega
    simp only [zero_add, this]
  have htl_nonneg : ∀ c n, 0 ≤ tl c n := fun c n => by
    rw [htl]; exact tsum_nonneg fun j => ht_nonneg _ _
  -- the tail of `1/a²` in the hypothesis, as a shifted sum
  have hsq_sum : Summable (fun k => (1 : ℝ) / (a k : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h₃
    apply one_div_le_one_div_of_le (by linarith [hapos k])
    nlinarith [hapos k]
  have hT : ∀ n, ∑' k : Set.Ioi n, (1 : ℝ) / (a k : ℝ) ^ 2 =
      ∑' j, (1 : ℝ) / (a (j + (n + 1)) : ℝ) ^ 2 := by
    intro n
    rw [tsum_subtype (Set.Ioi n) (fun k => (1 : ℝ) / (a k : ℝ) ^ 2)]
    have hs := (hsq_sum.indicator (Set.Ioi n)).sum_add_tsum_nat_add (n + 1)
    rw [← hs, Finset.sum_eq_zero, zero_add]
    · congr 1
      ext j
      rw [Set.indicator_of_mem]
      simp only [Set.mem_Ioi]
      omega
    · intro i hi
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ioi, not_lt]
      simp only [Finset.mem_range] at hi
      omega
  -- the key gap estimate
  have hgap : ∀ n, N ≤ n → 1 / (a n : ℝ) ^ 2 ≤ tl 1 (n + 1) - tl (1 + D) (n + 1) := by
    intro n hn
    have hpt : ∀ j, (D : ℝ) / 6 * ((1 : ℝ) / (a (j + (n + 1)) : ℝ) ^ 2) ≤
        t (j + (n + 1)) 1 - t (j + (n + 1)) (1 + D) := by
      intro j
      have hk : D + 1 ≤ a (j + (n + 1)) := by
        have := hge (j + (n + 1)); omega
      have hk' : (D : ℝ) + 1 ≤ a (j + (n + 1)) := by exact_mod_cast hk
      set A : ℝ := (a (j + (n + 1)) : ℝ)
      rw [ht, ht]
      push_cast
      have hA1 : 1 ≤ A := hapos _
      rw [div_sub_div _ _ (by positivity) (by positivity)]
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have hDn : (0 : ℝ) ≤ D := le_of_lt hDpos
      nlinarith [mul_nonneg hDn (mul_nonneg (by linarith : (0:ℝ) ≤ A - 1) (by linarith : (0:ℝ) ≤ A - D - 1)),
        mul_nonneg hDn (sq_nonneg A), mul_nonneg hDn (mul_nonneg (by linarith : (0:ℝ) ≤ A) (by linarith : (0:ℝ) ≤ A - D - 1))]
    have hle : (D : ℝ) / 6 * ∑' j, (1 : ℝ) / (a (j + (n + 1)) : ℝ) ^ 2 ≤
        tl 1 (n + 1) - tl (1 + D) (n + 1) := by
      rw [htl, htl, ← (hsumS 1 (n + 1)).tsum_sub (hsumS (1 + D) (n + 1)),
        ← ((summable_nat_add_iff (n + 1)).mpr hsq_sum).tsum_mul_left]
      exact Summable.tsum_le_tsum hpt
        (((summable_nat_add_iff (n + 1)).mpr hsq_sum).mul_left _)
        ((hsumS 1 (n + 1)).sub (hsumS (1 + D) (n + 1)))
    have hC' := hN0 n (le_trans (le_max_left _ _) (hN ▸ hn))
    rw [hT n] at hC'
    set T := ∑' j, (1 : ℝ) / (a (j + (n + 1)) : ℝ) ^ 2
    have hA2 : 0 < (a n : ℝ) ^ 2 := by have := hapos n; positivity
    refine le_trans ?_ hle
    rw [div_le_iff₀ hA2]
    have : (D : ℝ) / 6 * C ≤ (D : ℝ) / 6 * ((a n : ℝ) ^ 2 * T) :=
      mul_le_mul_of_nonneg_left hC' (by positivity)
    nlinarith
  -- one greedy step
  have step : ∀ n, N ≤ n → ∀ r : ℝ, tl (1 + D) n ≤ r → r ≤ tl 1 n →
      ∃ c : ℕ, (1 ≤ c ∧ c ≤ 1 + D) ∧ tl (1 + D) (n + 1) ≤ r - t n c ∧
        r - t n c ≤ tl 1 (n + 1) := by
    intro n hn r hlo hhi
    have e1 := hsplit 1 n
    have e2 := hsplit (1 + D) n
    rw [ht] at e1 e2
    obtain ⟨c, hc1, hc2, hx, hy⟩ := grid (a n) (hapos n) D (r - tl 1 (n + 1))
      (r - tl (1 + D) (n + 1)) (by linarith [hgap n hn]) (by push_cast at e1; linarith)
      (by linarith)
    exact ⟨c, ⟨hc1, hc2⟩, by rw [ht]; linarith, by rw [ht]; linarith⟩
  choose! cf hcf using step
  have hlohi : tl (1 + D) N < tl 1 N := by
    have e1 := hsplit 1 N
    have e2 := hsplit (1 + D) N
    have := hgap N le_rfl
    have : 0 < 1 / (a N : ℝ) ^ 2 := by have := hapos N; positivity
    have hmono : t N (1 + D) ≤ t N 1 := by
      rw [ht, ht]
      apply one_div_le_one_div_of_le (by linarith [hapos N])
      push_cast
      linarith [hDpos]
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlohi
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → ℝ, r 0 = q ∧
      ∀ m, r (m + 1) = r m - t (m + N) (cf (m + N) (r m)) :=
    ⟨fun m => Nat.rec (motive := fun _ => ℝ) (q : ℝ)
      (fun m rm => rm - t (m + N) (cf (m + N) rm)) m, rfl, fun _ => rfl⟩
  have hinv : ∀ m, tl (1 + D) (m + N) ≤ r m ∧ r m ≤ tl 1 (m + N) := by
    intro m
    induction m with
    | zero => rw [hr0, zero_add]; exact ⟨hq1.le, hq2.le⟩
    | succ m ih =>
      obtain ⟨-, h1, h2⟩ := hcf (m + N) (by omega) (r m) ih.1 ih.2
      rw [hrs, show m + 1 + N = m + N + 1 by omega]
      exact ⟨h1, h2⟩
  have hcb : ∀ m, 1 ≤ cf (m + N) (r m) ∧ cf (m + N) (r m) ≤ 1 + D := fun m =>
    (hcf (m + N) (by omega) (r m) (hinv m).1 (hinv m).2).1
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℤ, ∀ n, b n = if n < N then 1 else (cf n (r (n - N)) : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have hb1 : ∀ n, 1 ≤ b n ∧ b n ≤ 1 + D := by
    intro n
    rw [hb]
    split_ifs with h
    · constructor <;> omega
    · have := hcb (n - N)
      rw [show n - N + N = n by omega] at this
      constructor <;> omega
  have hf_lt : ∀ i, i < N → (1 : ℝ) / (((a i : ℤ) + b i : ℤ) : ℝ) = 1 / ((a i : ℝ) + 1) := by
    intro i hi
    rw [hb, if_pos hi]
    push_cast
    rfl
  have hf_ge : ∀ m, (1 : ℝ) / (((a (m + N) : ℤ) + b (m + N) : ℤ) : ℝ) =
      t (m + N) (cf (m + N) (r m)) := by
    intro m
    rw [hb, if_neg (by omega), ht, Nat.add_sub_cancel]
    push_cast
    rfl
  -- partial sums of the tail
  have hpart : ∀ M, ∑ i ∈ Finset.range M, t (i + N) (cf (i + N) (r i)) = q - r M := by
    intro M
    induction M with
    | zero => simp [hr0]
    | succ M ih => rw [Finset.sum_range_succ, ih, hrs]; ring
  have hr_lim : Tendsto r atTop (nhds 0) := by
    have hhi : Tendsto (fun m => tl 1 (m + N)) atTop (nhds 0) := by
      have := (tendsto_sum_nat_add (fun k => t k 1)).comp (tendsto_add_atTop_nat N)
      refine this.congr fun m => ?_
      simp [htl]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi
      (fun m => le_trans (htl_nonneg _ _) (hinv m).1) (fun m => (hinv m).2)
  have hhas_tail : HasSum (fun i => t (i + N) (cf (i + N) (r i))) (q : ℝ) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => ht_nonneg _ _)]
    have := (tendsto_const_nhds (x := (q : ℝ))).sub hr_lim
    rw [sub_zero] at this
    exact this.congr fun M => (hpart M).symm
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (((a n : ℤ) + b n : ℤ) : ℝ) with hfdef
  have hhas : HasSum f ((q : ℝ) + ∑ i ∈ Finset.range N, f i) := by
    rw [← hasSum_nat_add_iff' N, add_sub_cancel_right]
    refine hhas_tail.congr_fun fun m => ?_
    simp only [hfdef]
    exact hf_ge m
  have hirr' := hirr b ⟨1 + D, by rintro _ ⟨n, rfl⟩; exact (hb1 n).2⟩
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hb1 n).1⟩
    (by rintro ⟨n, hn⟩; have := (hb1 n).1; simp only at hn; omega)
    (by rintro ⟨n, hn⟩; have := (hb1 n).1; omega)
  have heq : ∑' n, (1 : ℝ) / (((a n : ℤ) + b n : ℤ) : ℝ) =
      ((q + ∑ i ∈ Finset.range N, (1 : ℚ) / ((a i : ℚ) + 1) : ℚ) : ℝ) := by
    rw [show (fun n => (1 : ℝ) / (((a n : ℤ) + b n : ℤ) : ℝ)) = f from rfl, hhas.tsum_eq]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun i hi => hf_lt i (Finset.mem_range.mp hi)
  refine hirr' ⟨q + ∑ i ∈ Finset.range N, (1 : ℚ) / ((a i : ℚ) + 1), ?_⟩
  rw [← heq]
  congr 1
  funext n
  push_cast
  rfl

end OMA.KovacTao

theorem OMA.solution : type_of% @Erdos264.erdos_264.variants.ko_tao_neg := by
  intro a h₁ h₂ h₃ h₄
  exact OMA.KovacTao.main h₁ h₂ h₃ h₄
