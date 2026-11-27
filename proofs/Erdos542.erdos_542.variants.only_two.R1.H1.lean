import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1
import Mathlib

-- Step Erdos542.erdos_542.variants.only_two.R1.H1: hypothesis H1 of reduction Erdos542.erdos_542.variants.only_two.R1
-- Credit: @ivillar

/-!
# The numerical inequality behind the case `3 ∈ A` of Erdős Problem 542

For `n ≥ 12`,
`∑_{n/2 < m ≤ n, 3 ∤ m} 1/m + ∑_{n/3 < b ≤ n/2, 3 ∤ b} 1/(2 b) ≤ 2/3`.

Write `alt k = 1 - 1/2 + 1/3 - … ± 1/k`. Since `alt k = H_k - H_⌊k/2⌋`, the first sum is exactly
`alt n - alt ⌊n/3⌋ / 3` (all integers in `(n / 2, n]` minus the multiples of `3`). Odd-indexed
partial sums of the alternating series decrease and even-indexed ones increase, so for
`n ≥ 200` the first sum is at most `alt 199 - alt 66 / 3`. The second sum has at most
`(n + 34) / 9` terms, each at most `3 / (2 n)`, so it is at most `1/6 + 3/100` for `n ≥ 200`.
The constants add up to less than `2/3` (kernel computation with rationals), and the cases
`12 ≤ n ≤ 199` are checked directly by the kernel.
-/

namespace OMA.Erdos542H1

/-- Harmonic numbers. -/
def hs (n : ℕ) : ℚ := ∑ m ∈ Finset.Icc 1 n, (1 : ℚ) / m

/-- Partial sums of the alternating harmonic series. -/
def alt (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (-1 : ℚ) ^ i / ((i : ℚ) + 1)

lemma hs_succ (n : ℕ) : hs (n + 1) = hs n + 1 / ((n : ℚ) + 1) := by
  unfold hs
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  rfl

lemma alt_succ (n : ℕ) : alt (n + 1) = alt n + (-1 : ℚ) ^ n / ((n : ℚ) + 1) := by
  unfold alt
  rw [Finset.sum_range_succ]

/-- `1 - 1/2 + 1/3 - … ± 1/n = H_n - H_⌊n/2⌋`. -/
lemma alt_eq (n : ℕ) : alt n = hs n - hs (n / 2) := by
  induction n with
  | zero => simp [alt, hs]
  | succ n ih =>
    rw [alt_succ, ih, hs_succ]
    rcases Nat.even_or_odd n with he | ho
    · have h2 : (n + 1) / 2 = n / 2 := by
        obtain ⟨k, hk⟩ := he
        omega
      rw [h2, he.neg_one_pow]
      ring
    · obtain ⟨k, hk⟩ := ho
      have h2 : (n + 1) / 2 = n / 2 + 1 := by omega
      have h3 : ((n / 2 : ℕ) : ℚ) + 1 = ((n : ℚ) + 1) / 2 := by
        have hk2 : n / 2 = k := by omega
        rw [hk2, hk]
        push_cast
        ring
      have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
      rw [h2, hs_succ, Odd.neg_one_pow ⟨k, hk⟩, h3]
      field_simp
      ring

lemma neg_one_div (x : ℚ) : (-1 : ℚ) / x = -(1 / x) := by
  ring

lemma alt_even_le_odd (l : ℕ) : alt (2 * l) ≤ alt (2 * l + 1) := by
  have s1 := alt_succ (2 * l)
  have hp : (-1 : ℚ) ^ (2 * l) = 1 := Even.neg_one_pow ⟨l, two_mul l⟩
  rw [hp] at s1
  have hnn : (0 : ℚ) ≤ 1 / (((2 * l : ℕ) : ℚ) + 1) := by positivity
  linarith

lemma alt_even_succ_le_odd (l : ℕ) : alt (2 * l + 2) ≤ alt (2 * l + 1) := by
  have s1 : alt (2 * l + 2) = alt (2 * l + 1) + (-1 : ℚ) ^ (2 * l + 1) / (((2 * l + 1 : ℕ) : ℚ) + 1) :=
    alt_succ (2 * l + 1)
  have hp : (-1 : ℚ) ^ (2 * l + 1) = -1 := Odd.neg_one_pow ⟨l, rfl⟩
  rw [hp, neg_one_div] at s1
  have hnn : (0 : ℚ) ≤ 1 / (((2 * l + 1 : ℕ) : ℚ) + 1) := by positivity
  linarith

lemma alt_odd_anti (l : ℕ) : alt (2 * l + 3) ≤ alt (2 * l + 1) := by
  have s1 : alt (2 * l + 2) = alt (2 * l + 1) + (-1 : ℚ) ^ (2 * l + 1) / (((2 * l + 1 : ℕ) : ℚ) + 1) :=
    alt_succ (2 * l + 1)
  have s2 : alt (2 * l + 3) = alt (2 * l + 2) + (-1 : ℚ) ^ (2 * l + 2) / (((2 * l + 2 : ℕ) : ℚ) + 1) :=
    alt_succ (2 * l + 2)
  have hp1 : (-1 : ℚ) ^ (2 * l + 1) = -1 := Odd.neg_one_pow ⟨l, rfl⟩
  have hp2 : (-1 : ℚ) ^ (2 * l + 2) = 1 := Even.neg_one_pow ⟨l + 1, by ring⟩
  rw [hp1, neg_one_div] at s1
  rw [hp2] at s2
  have h1 : (0 : ℚ) < ((2 * l + 1 : ℕ) : ℚ) + 1 := by positivity
  have hle : (1 : ℚ) / (((2 * l + 2 : ℕ) : ℚ) + 1) ≤ 1 / (((2 * l + 1 : ℕ) : ℚ) + 1) := by
    apply one_div_le_one_div_of_le h1
    push_cast
    linarith
  linarith

lemma alt_even_mono (l : ℕ) : alt (2 * l) ≤ alt (2 * l + 2) := by
  have s1 : alt (2 * l + 1) = alt (2 * l) + (-1 : ℚ) ^ (2 * l) / (((2 * l : ℕ) : ℚ) + 1) :=
    alt_succ (2 * l)
  have s2 : alt (2 * l + 2) = alt (2 * l + 1) + (-1 : ℚ) ^ (2 * l + 1) / (((2 * l + 1 : ℕ) : ℚ) + 1) :=
    alt_succ (2 * l + 1)
  have hp1 : (-1 : ℚ) ^ (2 * l) = 1 := Even.neg_one_pow ⟨l, two_mul l⟩
  have hp2 : (-1 : ℚ) ^ (2 * l + 1) = -1 := Odd.neg_one_pow ⟨l, rfl⟩
  rw [hp1] at s1
  rw [hp2, neg_one_div] at s2
  have h1 : (0 : ℚ) < ((2 * l : ℕ) : ℚ) + 1 := by positivity
  have hle : (1 : ℚ) / (((2 * l + 1 : ℕ) : ℚ) + 1) ≤ 1 / (((2 * l : ℕ) : ℚ) + 1) := by
    apply one_div_le_one_div_of_le h1
    push_cast
    linarith
  linarith

/-- Every later partial sum is at most an odd-indexed one. -/
lemma alt_le_odd (j : ℕ) : ∀ k, 2 * j + 1 ≤ k → alt k ≤ alt (2 * j + 1) := by
  have hodd : ∀ d, alt (2 * (j + d) + 1) ≤ alt (2 * j + 1) := by
    intro d
    induction d with
    | zero => exact le_refl _
    | succ d ih =>
      have h := alt_odd_anti (j + d)
      rw [show 2 * (j + (d + 1)) + 1 = 2 * (j + d) + 3 by ring]
      exact h.trans ih
  intro k hk
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨l, hl⟩ := he
    obtain ⟨d, hd⟩ : ∃ d, l = j + d + 1 := ⟨l - j - 1, by omega⟩
    have h1 := alt_even_succ_le_odd (j + d)
    rw [show k = 2 * (j + d) + 2 by omega]
    exact h1.trans (hodd d)
  · obtain ⟨l, hl⟩ := ho
    obtain ⟨d, hd⟩ : ∃ d, l = j + d := ⟨l - j, by omega⟩
    rw [hl, hd]
    exact hodd d

/-- Every later partial sum is at least an even-indexed one. -/
lemma alt_ge_even (i : ℕ) : ∀ k, 2 * i ≤ k → alt (2 * i) ≤ alt k := by
  have heven : ∀ d, alt (2 * i) ≤ alt (2 * (i + d)) := by
    intro d
    induction d with
    | zero => exact le_refl _
    | succ d ih =>
      have h := alt_even_mono (i + d)
      rw [show 2 * (i + (d + 1)) = 2 * (i + d) + 2 by ring]
      exact ih.trans h
  intro k hk
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨l, hl⟩ := he
    obtain ⟨d, hd⟩ : ∃ d, l = i + d := ⟨l - i, by omega⟩
    rw [show k = 2 * (i + d) by omega]
    exact heven d
  · obtain ⟨l, hl⟩ := ho
    obtain ⟨d, hd⟩ : ∃ d, l = i + d := ⟨l - i, by omega⟩
    rw [hl, hd]
    exact (heven d).trans (alt_even_le_odd (i + d))

/-- The reciprocals of the integers in `(n / 2, n]` sum to `H_n - H_⌊n/2⌋`. -/
lemma upper_half (n : ℕ) :
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m), (1 : ℚ) / m = hs n - hs (n / 2) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun m => n < 2 * m)
    (fun m => (1 : ℚ) / m)
  have hlow : (Finset.Icc 1 n).filter (fun m => ¬ n < 2 * m) = Finset.Icc 1 (n / 2) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hlow] at hsplit
  unfold hs
  linarith

/-- The non-multiples of `3` in `(n / 2, n]`: all integers there minus the multiples `3 k`,
`n / 6 < k ≤ n / 3`. -/
lemma S1_eq (n : ℕ) :
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / m =
      alt n - alt (n / 3) / 3 := by
  have hmul : ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ ¬ m % 3 ≠ 0), (1 : ℚ) / m =
      (hs (n / 3) - hs (n / 3 / 2)) / 3 := by
    have himg : (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ ¬ m % 3 ≠ 0) =
        ((Finset.Icc 1 (n / 3)).filter (fun k => n / 3 < 2 * k)).image (fun k : ℕ => 3 * k) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨m / 3, ⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
      · rintro ⟨k, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    rw [himg, Finset.sum_image (fun x _ y _ (h : 3 * x = 3 * y) => by omega), ← upper_half,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    push_cast
    field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 n).filter (fun m => n < 2 * m)) (fun m => m % 3 ≠ 0) (fun m => (1 : ℚ) / m)
  rw [Finset.filter_filter, Finset.filter_filter, upper_half, hmul] at hsplit
  rw [alt_eq n, alt_eq (n / 3)]
  linarith

/-- A crude bound for the second sum when `n ≥ 200`. -/
lemma S2_le {n : ℕ} (hn : 200 ≤ n) :
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
      (1 : ℚ) / (2 * b) ≤ 1 / 6 + 3 / 100 := by
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ,
      F = (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0) := ⟨_, rfl⟩
  rw [← hF]
  have hmem : ∀ b ∈ F, 1 ≤ b ∧ n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0 := by
    intro b hb
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hb
    exact ⟨hb.1.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hterm : ∑ b ∈ F, (1 : ℚ) / (2 * b) ≤ (F.card : ℚ) * (3 / (2 * n)) := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro b hb
    have hb' := hmem b hb
    have hbQ : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hle : (n : ℚ) ≤ 3 * b := by exact_mod_cast (by omega : n ≤ 3 * b)
    linarith
  have hinj : ∀ p : ℕ → Prop, [DecidablePred p] → (∀ b c, p b → p c → b % 3 = c % 3) →
      (F.filter p).card ≤ (Finset.Icc (n / 9) (n / 6)).card := by
    intro p _ hp
    apply Finset.card_le_card_of_injOn (fun b => b / 3)
    · intro b hb
      have hb1 := hmem b (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
      have hI : b / 3 ∈ Finset.Icc (n / 9) (n / 6) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact Finset.mem_coe.mpr hI
    · intro b hb c hc hbc
      have hb1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hc1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
      have hmod := hp b c hb1 hc1
      have hbc' : b / 3 = c / 3 := hbc
      omega
  have hc1 := hinj (fun b => b % 3 = 1) (fun b c hb hc => by omega)
  have hc2 : (F.filter (fun b => ¬ b % 3 = 1)).card ≤ (Finset.Icc (n / 9) (n / 6)).card := by
    have h := hinj (fun b => b % 3 = 2) (fun b c hb hc => by omega)
    have heq : F.filter (fun b => ¬ b % 3 = 1) = F.filter (fun b => b % 3 = 2) := by
      apply Finset.filter_congr
      intro b hb
      have := (hmem b hb).2.2.2
      omega
    rw [heq]
    exact h
  have hsum := Finset.card_filter_add_card_filter_not (s := F) (fun b => b % 3 = 1)
  rw [Nat.card_Icc] at hc1 hc2
  have hcard : 9 * F.card ≤ n + 34 := by omega
  have hcardQ : (9 : ℚ) * (F.card : ℚ) ≤ n + 34 := by exact_mod_cast hcard
  have hn200 : (200 : ℚ) ≤ n := by exact_mod_cast hn
  have hfin : (F.card : ℚ) * (3 / (2 * n)) ≤ 1 / 6 + 3 / 100 := by
    have key : (F.card : ℚ) * (3 / (2 * n)) = (3 * (F.card : ℚ)) / (2 * n) := by ring
    rw [key, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma num_large : alt 199 - alt 66 / 3 + (1 / 6 + 3 / 100) ≤ 2 / 3 := by
  decide +kernel

lemma num_small : ∀ n ∈ Finset.Icc (12 : ℕ) 199,
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / (m : ℚ) +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℚ) / (2 * (b : ℚ)) ≤ 2 / 3 := by
  decide +kernel

/-- The inequality over `ℚ`. -/
lemma main_rat (n : ℕ) (hn : 12 ≤ n) :
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / (m : ℚ) +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℚ) / (2 * (b : ℚ)) ≤ 2 / 3 := by
  by_cases h : n ≤ 199
  · exact num_small n (Finset.mem_Icc.mpr ⟨hn, h⟩)
  · have h200 : 200 ≤ n := by omega
    have h1 := S1_eq n
    have h2 := S2_le h200
    have ha := alt_le_odd 99 n (by omega)
    have hb := alt_ge_even 33 (n / 3) (by omega)
    have hnum := num_large
    rw [h1]
    linarith

end OMA.Erdos542H1

theorem OMA.solution : OMA.R_Erdos542_erdos_542_variants_only_two_R1.H1 := by
  intro n hn
  have h := OMA.Erdos542H1.main_rat n hn
  have hr : ((∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / (m : ℚ) +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℚ) / (2 * (b : ℚ)) : ℚ) : ℝ) ≤ ((2 / 3 : ℚ) : ℝ) := Rat.cast_le.mpr h
  push_cast at hr
  exact hr
