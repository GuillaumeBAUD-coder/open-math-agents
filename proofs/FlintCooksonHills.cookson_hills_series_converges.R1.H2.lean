import OMAReductions.R_FlintCooksonHills_cookson_hills_series_converges_R1

-- Step FlintCooksonHills.cookson_hills_series_converges.R1.H2: hypothesis H2 of reduction FlintCooksonHills.cookson_hills_series_converges.R1
-- Credit: @OrangeHeadz
-- H2 := ∀ α c ν : ℝ, 0 < c → 1 < ν → ν < 5 / 2 →     (∀ q : ℕ, 0 < q →       c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) →     Summable (fun q : ℕ =>       1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2))

/-! # Summability of `1 / (q ^ 3 * ‖q α‖ ^ 2)` from an irrationality-measure bound

Write `‖q α‖` for the distance from `q * α` to the nearest integer and suppose
`‖q α‖ ≥ c * q ^ (1 - ν)` with `1 < ν < 5 / 2`.

On a dyadic block `2 ^ k ≤ q < 2 ^ (k + 1)` put `d = c * (2 ^ (k + 1)) ^ (1 - ν)`. Every `‖q α‖`
in the block is at least `d`, and for `q ≠ q'` in the block the signed remainders
`q α - round (q α)` differ by at least `‖(q - q') α‖ ≥ d`. So among the `q` with a remainder of a
given sign, the values `‖q α‖` are at least `d` and pairwise `d`-separated: their integer levels
`⌊‖q α‖ / d⌋` are distinct and at least `1`, which bounds the sum of `1 / ‖q α‖ ^ 2` by
`(∑ 1 / m ^ 2) / d ^ 2 ≤ 2 / d ^ 2` for each sign, hence by `4 / d ^ 2` on the block.

Dividing by `q ^ 3 ≥ 8 ^ k`, the block contributes at most a constant times
`(2 ^ (2 ν - 5)) ^ k`, a convergent geometric series since `ν < 5 / 2`. The partial sums are
therefore bounded, and the terms are nonnegative. -/

open Finset

/-- Positive reals that are at least `d` and pairwise `d`-separated have inverse squares
summing to at most `2 / d ^ 2`. -/
lemma OMA.sep_sum (S : Finset ℕ) (x : ℕ → ℝ) (d : ℝ) (hd : 0 < d)
    (hx : ∀ q ∈ S, d ≤ x q)
    (hsep : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → d ≤ |x q - x q'|) :
    ∑ q ∈ S, 1 / (x q) ^ 2 ≤ 2 / d ^ 2 := by
  have hq0 : ∀ q ∈ S, 0 ≤ x q / d := fun q hq => div_nonneg (hd.le.trans (hx q hq)) hd.le
  have hm1 : ∀ q ∈ S, 1 ≤ ⌊x q / d⌋₊ := fun q hq =>
    Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hd, one_mul]; exact hx q hq)
  have hmle : ∀ q ∈ S, (⌊x q / d⌋₊ : ℝ) * d ≤ x q := fun q hq =>
    (le_div_iff₀ hd).1 (Nat.floor_le (hq0 q hq))
  have hinj : Set.InjOn (fun q => ⌊x q / d⌋₊) (S : Set ℕ) := by
    intro q hq q' hq' hmm
    by_contra hne
    have h1 := hsep q hq q' hq' hne
    have e : (⌊x q / d⌋₊ : ℝ) = (⌊x q' / d⌋₊ : ℝ) := by exact_mod_cast hmm
    have a1 := Nat.floor_le (hq0 q hq)
    have a2 := Nat.lt_floor_add_one (x q / d)
    have b1 := Nat.floor_le (hq0 q' hq')
    have b2 := Nat.lt_floor_add_one (x q' / d)
    have h2 : |x q / d - x q' / d| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have h3 : x q - x q' = (x q / d - x q' / d) * d := by field_simp
    rw [h3, abs_mul, abs_of_pos hd] at h1
    have h4 := mul_lt_mul_of_pos_right h2 hd
    linarith
  have hterm : ∀ q ∈ S, 1 / (x q) ^ 2 ≤ ((⌊x q / d⌋₊ : ℝ) ^ 2)⁻¹ / d ^ 2 := by
    intro q hq
    have hmpos : (0 : ℝ) < ⌊x q / d⌋₊ := by exact_mod_cast hm1 q hq
    have h4 : ((⌊x q / d⌋₊ : ℝ) * d) ^ 2 ≤ (x q) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hmle q hq) 2
    have h5 : ((⌊x q / d⌋₊ : ℝ) ^ 2)⁻¹ / d ^ 2 = 1 / ((⌊x q / d⌋₊ : ℝ) * d) ^ 2 := by
      rw [mul_pow]; field_simp
    rw [h5]
    exact one_div_le_one_div_of_le (by positivity) h4
  calc ∑ q ∈ S, 1 / (x q) ^ 2
      ≤ ∑ q ∈ S, ((⌊x q / d⌋₊ : ℝ) ^ 2)⁻¹ / d ^ 2 := Finset.sum_le_sum hterm
    _ = (∑ i ∈ S.image (fun q => ⌊x q / d⌋₊), ((i : ℝ) ^ 2)⁻¹) / d ^ 2 := by
        rw [Finset.sum_image hinj, Finset.sum_div]
    _ ≤ (∑ i ∈ Finset.Ioo (0 : ℕ) (S.sup (fun q => ⌊x q / d⌋₊) + 1), ((i : ℝ) ^ 2)⁻¹) / d ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
          rw [Finset.mem_Ioo]
          exact ⟨hm1 q hq, Nat.lt_succ_of_le (Finset.le_sup (f := fun q => ⌊x q / d⌋₊) hq)⟩
        · intro i _ _; positivity
    _ ≤ 2 / d ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (S.sup (fun q => ⌊x q / d⌋₊) + 1)
        simpa using h

/-- On a dyadic block, the distances to the nearest integer of `q * α` are separated, so
their inverse squares have a controlled sum. -/
lemma OMA.block (α d : ℝ) (k : ℕ) (hd : 0 < d)
    (hlow : ∀ n : ℕ, 0 < n → n ≤ 2 ^ (k + 1) →
      d ≤ |(n : ℝ) * α - (round ((n : ℝ) * α) : ℝ)|) :
    ∑ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)),
      1 / |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2 ≤ 4 / d ^ 2 := by
  set s : ℕ → ℝ := fun q => (q : ℝ) * α - (round ((q : ℝ) * α) : ℝ) with hs
  have hsub : ∀ q q' : ℕ, q' < q → q ≤ 2 ^ (k + 1) → d ≤ |s q - s q'| := by
    intro q q' hlt hq
    have hn : 0 < q - q' := Nat.sub_pos_of_lt hlt
    have h1 := hlow (q - q') hn (by omega)
    have h2 := round_le (((q - q' : ℕ) : ℝ) * α)
      (round ((q : ℝ) * α) - round ((q' : ℝ) * α))
    have e : s q - s q' = ((q - q' : ℕ) : ℝ) * α -
        ((round ((q : ℝ) * α) - round ((q' : ℝ) * α) : ℤ) : ℝ) := by
      simp only [hs]
      push_cast [Nat.cast_sub hlt.le]
      ring
    rw [e]
    exact h1.trans h2
  have hsep : ∀ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)), ∀ q' ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)),
      q ≠ q' → d ≤ |s q - s q'| := by
    intro q hq q' hq' hne
    rw [Finset.mem_Ico] at hq hq'
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm]; exact hsub q' q h hq'.2.le
    · exact hsub q q' h hq.2.le
  have hx : ∀ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)), d ≤ |s q| := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    have hpos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
    exact hlow q (by omega) hq.2.le
  have hP := OMA.sep_sum ((Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1))).filter (fun q => 0 ≤ s q))
    (fun q => |s q|) d hd
    (fun q hq => hx q (Finset.mem_filter.1 hq).1)
    (fun q hq q' hq' hne => by
      have h1 := (Finset.mem_filter.1 hq)
      have h2 := (Finset.mem_filter.1 hq')
      simp only [abs_of_nonneg h1.2, abs_of_nonneg h2.2]
      exact hsep q h1.1 q' h2.1 hne)
  have hN := OMA.sep_sum ((Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1))).filter (fun q => ¬ 0 ≤ s q))
    (fun q => |s q|) d hd
    (fun q hq => hx q (Finset.mem_filter.1 hq).1)
    (fun q hq q' hq' hne => by
      have h1 := (Finset.mem_filter.1 hq)
      have h2 := (Finset.mem_filter.1 hq')
      have e1 : |s q| = -s q := abs_of_neg (not_le.1 h1.2)
      have e2 : |s q'| = -s q' := abs_of_neg (not_le.1 h2.2)
      rw [e1, e2, show -s q - -s q' = -(s q - s q') by ring, abs_neg]
      exact hsep q h1.1 q' h2.1 hne)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)))
    (fun q => 0 ≤ s q) (fun q => 1 / |s q| ^ 2)
  show ∑ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)), 1 / |s q| ^ 2 ≤ 4 / d ^ 2
  rw [← hsplit]
  have e4 : (4 : ℝ) / d ^ 2 = 2 / d ^ 2 + 2 / d ^ 2 := by ring
  rw [e4]
  exact add_le_add hP hN

theorem OMA.solution : OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1.H2 := by
  intro α c ν hc hν1 hν2 h
  set ρ : ℝ := (2 : ℝ) ^ (1 - ν) with hρdef
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  -- `8 * ρ ^ 2 > 1`
  have hτ : (2 : ℝ) ^ (-(3 / 2) : ℝ) < ρ :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hτpos : (0 : ℝ) < (2 : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hτsq : ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ 2 = 1 / 8 := by
    rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (-(3 / 2) : ℝ) + -(3 / 2) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hρsq : 1 / 8 < ρ ^ 2 := by
    rw [← hτsq]; exact pow_lt_pow_left₀ hτ hτpos.le (by norm_num)
  set r : ℝ := ((2 : ℝ) ^ 3 * ρ ^ 2)⁻¹ with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [hrdef]
    apply inv_lt_one_of_one_lt₀
    nlinarith
  set A : ℝ := 4 / (c ^ 2 * ρ ^ 2) with hAdef
  have hA : 0 ≤ A := by positivity
  set f : ℕ → ℝ := fun q =>
    1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2) with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => by simp only [hf]; positivity
  -- the dyadic block bound
  have hblock : ∀ k : ℕ, ∑ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)), f q ≤ A * r ^ k := by
    intro k
    have hdk : 0 < c * ρ ^ (k + 1) := by positivity
    have hlow : ∀ n : ℕ, 0 < n → n ≤ 2 ^ (k + 1) →
        c * ρ ^ (k + 1) ≤ |(n : ℝ) * α - (round ((n : ℝ) * α) : ℝ)| := by
      intro n hn hle
      refine le_trans ?_ (h n hn)
      apply mul_le_mul_of_nonneg_left _ hc.le
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hle' : (n : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hle
      have h1 : ((2 : ℝ) ^ (k + 1)) ^ (1 - ν) ≤ (n : ℝ) ^ (1 - ν) :=
        Real.rpow_le_rpow_of_nonpos hn' hle' (by linarith)
      have h2 : ((2 : ℝ) ^ (k + 1)) ^ (1 - ν) = ρ ^ (k + 1) := by
        rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [← h2]; exact h1
    have hb := OMA.block α (c * ρ ^ (k + 1)) k hdk hlow
    calc ∑ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)), f q
        ≤ ∑ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)),
            (1 / ((2 : ℝ) ^ k) ^ 3) *
              (1 / |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_Ico] at hq
          have hq1 : ((2 : ℝ) ^ k) ≤ (q : ℝ) := by exact_mod_cast hq.1
          have hq3 : ((2 : ℝ) ^ k) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hq1 3
          simp only [hf]
          rw [one_div_mul_one_div]
          apply one_div_le_one_div_of_le
          · have hpos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
            have habs : 0 < |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| :=
              lt_of_lt_of_le hdk (hlow q (by omega) hq.2.le)
            positivity
          · exact mul_le_mul_of_nonneg_right hq3 (by positivity)
      _ = (1 / ((2 : ℝ) ^ k) ^ 3) * ∑ q ∈ Finset.Ico ((2 : ℕ) ^ k) (2 ^ (k + 1)),
            (1 / |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / ((2 : ℝ) ^ k) ^ 3) * (4 / (c * ρ ^ (k + 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = A * r ^ k := by
          rw [hAdef, hrdef, inv_pow]
          field_simp
          simp only [mul_pow, ← pow_mul]
          ring
  -- partial sums over `range (2 ^ n)`
  have hpow : ∀ n : ℕ, ∑ q ∈ Finset.range (2 ^ n), f q ≤ ∑ k ∈ Finset.range n, A * r ^ k := by
    intro n
    induction n with
    | zero => simp [hf]
    | succ n ih =>
      rw [← Finset.sum_range_add_sum_Ico f (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)),
        Finset.sum_range_succ]
      exact add_le_add ih (hblock n)
  have hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range n, A * r ^ k ≤ A * (1 - r)⁻¹ := by
    intro n
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [← tsum_geometric_of_lt_one hr0.le hr1]
    exact (summable_geometric_of_lt_one hr0.le hr1).sum_le_tsum _ (fun i _ => by positivity)
  refine summable_of_sum_range_le (c := A * (1 - r)⁻¹) hf0 (fun n => ?_)
  calc ∑ q ∈ Finset.range n, f q ≤ ∑ q ∈ Finset.range (2 ^ n), f q :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (Nat.lt_two_pow_self).le) (fun q _ _ => hf0 q)
    _ ≤ ∑ k ∈ Finset.range n, A * r ^ k := hpow n
    _ ≤ A * (1 - r)⁻¹ := hgeom n
