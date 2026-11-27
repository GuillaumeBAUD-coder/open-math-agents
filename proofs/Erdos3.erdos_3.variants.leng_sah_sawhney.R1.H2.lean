import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1

-- Step Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H2: hypothesis H2 of reduction Erdos3.erdos_3.variants.leng_sah_sawhney.R1

/-!
Iterating the dichotomy at most `gap s / η + 1` times (the gap drops by `η` each time and stays
nonnegative) gives `level s ≤ (n + 1) C (1 + gap s)^D` whenever `gap s ≤ n η`, hence
`max (level s) 0 ≤ B (1 + gap s)^(D+1)` with `B = C (1/η + 2)`. With `c = 1 / (2 (D + 1))` this
yields `(max (level s) 0)^c ≤ B^c √(1 + gap s) ≤ 1 + gap s + (B^c)^2 / 4`, which is the claim
with `K = exp (1 + (B^c)^2 / 4)`.
-/

theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1.H2 := by
  unfold OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1.H2
  intro State gap level η C D hη hC hgap hstep
  have hiter : ∀ n : ℕ, ∀ s, gap s ≤ (n : ℝ) * η →
      level s ≤ ((n : ℝ) + 1) * (C * (1 + gap s) ^ D) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      rcases hstep s with h | ⟨t, ht, _⟩
      · simpa using h
      · exfalso
        have h1 := hgap t
        simp at hs
        linarith
    | succ n ih =>
      intro s hs
      have hX : 0 ≤ C * (1 + gap s) ^ D :=
        mul_nonneg hC.le (pow_nonneg (by linarith [hgap s]) D)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have e : (((n + 1 : ℕ) : ℝ) + 1) * (C * (1 + gap s) ^ D) =
          ((n : ℝ) + 1) * (C * (1 + gap s) ^ D) + C * (1 + gap s) ^ D := by
        push_cast
        ring
      rw [e]
      have hnX : 0 ≤ ((n : ℝ) + 1) * (C * (1 + gap s) ^ D) := mul_nonneg (by linarith) hX
      rcases hstep s with h | ⟨t, ht, hlev⟩
      · linarith
      · have ht2 : gap t ≤ (n : ℝ) * η := by
          push_cast at hs
          linarith
        have h1 := ih t ht2
        have hmono : (1 + gap t) ^ D ≤ (1 + gap s) ^ D :=
          pow_le_pow_left₀ (by linarith [hgap t]) (by linarith) D
        have h2 : ((n : ℝ) + 1) * (C * (1 + gap t) ^ D) ≤
            ((n : ℝ) + 1) * (C * (1 + gap s) ^ D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hC.le) (by linarith)
        linarith
  have hηinv : 0 < 1 / η := one_div_pos.2 hη
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C * (1 / η + 2) := ⟨_, rfl⟩
  have hBpos : 0 < B := by
    rw [hBdef]
    exact mul_pos hC (by linarith)
  have hB : ∀ s, max (level s) 0 ≤ B * (1 + gap s) ^ (D + 1) := by
    intro s
    have hg := hgap s
    have hX : 0 ≤ C * (1 + gap s) ^ D := mul_nonneg hC.le (pow_nonneg (by linarith) D)
    have hdiv : 0 ≤ gap s / η := div_nonneg hg hη.le
    have hn1 : gap s ≤ (⌈gap s / η⌉₊ : ℝ) * η := by
      have h := Nat.le_ceil (gap s / η)
      calc gap s = gap s / η * η := by field_simp
        _ ≤ (⌈gap s / η⌉₊ : ℝ) * η := mul_le_mul_of_nonneg_right h hη.le
    have hn2 : (⌈gap s / η⌉₊ : ℝ) ≤ gap s / η + 1 := (Nat.ceil_lt_add_one hdiv).le
    have h1 := hiter _ s hn1
    have h2 : level s ≤ (gap s / η + 2) * (C * (1 + gap s) ^ D) :=
      h1.trans (mul_le_mul_of_nonneg_right (by linarith) hX)
    have h4 : gap s / η + 2 ≤ (1 / η + 2) * (1 + gap s) := by
      have e : (1 / η + 2) * (1 + gap s) = 1 / η + 2 + gap s / η + 2 * gap s := by ring
      rw [e]
      linarith
    have h3 : (gap s / η + 2) * (C * (1 + gap s) ^ D) ≤ B * (1 + gap s) ^ (D + 1) := by
      calc (gap s / η + 2) * (C * (1 + gap s) ^ D)
          ≤ ((1 / η + 2) * (1 + gap s)) * (C * (1 + gap s) ^ D) :=
            mul_le_mul_of_nonneg_right h4 hX
        _ = B * (1 + gap s) ^ (D + 1) := by
            rw [hBdef]
            ring
    have h5 : 0 ≤ B * (1 + gap s) ^ (D + 1) :=
      mul_nonneg hBpos.le (pow_nonneg (by linarith) _)
    exact max_le (h2.trans h3) h5
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (2 * ((D : ℝ) + 1)) := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have he : ((D + 1 : ℕ) : ℝ) * c = 1 / 2 := by
    rw [hc]
    push_cast
    field_simp
  refine ⟨c, Real.exp (1 + (B ^ c) ^ 2 / 4), hcpos, Real.exp_pos _, ?_⟩
  intro s
  have hg := hgap s
  have hL0 : 0 ≤ max (level s) 0 := le_max_right _ _
  have hx0 : 0 < 1 + gap s := by linarith
  have h1 : (max (level s) 0) ^ c ≤ (B * (1 + gap s) ^ (D + 1)) ^ c :=
    Real.rpow_le_rpow hL0 (hB s) hcpos.le
  have h2 : (B * (1 + gap s) ^ (D + 1)) ^ c = B ^ c * Real.sqrt (1 + gap s) := by
    rw [Real.mul_rpow hBpos.le (pow_nonneg hx0.le _), ← Real.rpow_natCast (1 + gap s) (D + 1),
      ← Real.rpow_mul hx0.le, he, Real.sqrt_eq_rpow]
  have h3 : B ^ c * Real.sqrt (1 + gap s) ≤ (1 + gap s) + (B ^ c) ^ 2 / 4 := by
    have hs := Real.sq_sqrt hx0.le
    nlinarith [sq_nonneg (Real.sqrt (1 + gap s) - B ^ c / 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  linarith
