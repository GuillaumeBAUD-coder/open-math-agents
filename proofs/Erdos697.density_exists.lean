import FormalConjectures.ErdosProblems.«697»

open Filter
open scoped Topology

theorem OMA.solution : type_of% @Erdos697.density_exists := by
  classical
  intro m α
  let B := Real.exp ((m : ℝ) ^ α)
  let T := (⌈B⌉₊).factorial
  have hT : 0 < T := Nat.factorial_pos _
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let p (n : ℕ) := ∃ d : ℕ, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 B ∧ d ∣ n
  have hp (n : ℕ) : p (n + T) = p n := propext <| exists_congr fun d =>
    and_congr_right fun _ => and_congr_right fun hd => by
      have hdvd : d ∣ T :=
        Nat.dvd_factorial (by exact_mod_cast zero_lt_one.trans hd.1) (Nat.lt_ceil.mpr hd.2).le
      exact ⟨(Nat.dvd_add_iff_left hdvd).mpr, fun h => Nat.dvd_add h hdvd⟩
  let c := Nat.count p
  let δ : ℝ := c T / T
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := (div_le_one hTr).mpr (by exact_mod_cast Nat.count_le (p := p))
  have hsh (n : ℕ) : Nat.count (fun i => p (i + T)) n = c n := by
    simp only [c, Nat.count_eq_card_filter_range]; congr 1; ext i; simp [hp]
  have hblk (q r : ℕ) : c (q * T + r) = q * c T + c r := by
    induction q with
    | zero => simp
    | succ q ih =>
      show Nat.count p ((q + 1) * T + r) = _
      rw [Nat.succ_mul, add_right_comm, Nat.count_add', hsh]; change c _ + c T = _
      rw [ih, Nat.succ_mul, add_right_comm]
  have hnc (n : ℕ) : ({k | p k} ∩ Set.Iio n).ncard = c n := by
    rw [show {k | p k} ∩ Set.Iio n = ↑((Finset.range n).filter p) by ext k; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
  have herr : ∀ᶠ n : ℕ in atTop, |(c n : ℝ) / n - δ| ≤ (T : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let q := n / T; let r := n % T
    have hsplit : q * T + r = n := by simpa [q, r, mul_comm] using Nat.div_add_mod n T
    have hsp : (q : ℝ) * T + r = n := by exact_mod_cast hsplit
    have hcnt : (q : ℝ) * c T + c r = c n := by
      exact_mod_cast (hblk q r).symm.trans (congrArg c hsplit)
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hr : (r : ℝ) ≤ T := by exact_mod_cast (Nat.mod_lt n hT).le
    have hcr : (c r : ℝ) ≤ r := by exact_mod_cast Nat.count_le (p := p)
    have heq : (c n : ℝ) / n - δ = (c r - r * δ) / n := by
      have : (T : ℝ) * δ = c T := mul_div_cancel₀ _ hTr.ne'
      rw [eq_div_iff hn'.ne', sub_mul, div_mul_cancel₀ _ hn'.ne', ← hcnt, ← hsp, mul_add,
        mul_comm δ, mul_assoc, this]; ring
    rw [heq, abs_div, abs_of_pos hn']
    refine div_le_div_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) hn'.le
    · nlinarith [Nat.cast_nonneg (α := ℝ) (c r), Nat.cast_nonneg (α := ℝ) r]
    · nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hu := tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
  have ht : Tendsto (fun n : ℕ => (c n : ℝ) / n - δ) atTop (𝓝 0) :=
    (show Tendsto (fun n : ℕ => -((T : ℝ) / n)) atTop (𝓝 0) by simpa using hu.neg).squeeze' hu
      (herr.mono fun _ h => (abs_le.mp h).1) (herr.mono fun _ h => (abs_le.mp h).2)
  refine ⟨δ, ?_⟩
  change ({n | p n}).HasDensity δ
  simpa [Set.HasDensity, Set.partialDensity, hnc] using ht.add_const δ
