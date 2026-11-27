import OMAStatements.S_oeis_a193358

-- Problem: A193358, every positive integer occurs and odd values occur once.
-- Credit: @ShoQo
-- Proof: Chai Wah Wu's block description. Write n = m(m+1) + r with r ≤ 2m+1 (unique); then
-- g(n) = 2m+1 if r = 2m and 2m+2 otherwise. g satisfies the recurrence (three cases on r),
-- any solution equals g by strong induction (g ≥ 1, so n - g(n-2) < n), and both properties
-- are read off the block description.

open OMA.S_oeis_a193358

namespace OMA_A193358_Proof

lemma decomp (n : ℕ) : ∃ m r, n = m * (m + 1) + r ∧ r ≤ 2 * m + 1 := by
  induction n with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨m, r, h, hr⟩ := ih
    rcases Nat.lt_or_ge r (2 * m + 1) with h' | h'
    · exact ⟨m, r + 1, by rw [h]; ring, by omega⟩
    · refine ⟨m + 1, 0, ?_, by omega⟩
      obtain rfl : r = 2 * m + 1 := by omega
      rw [h]; ring

lemma decomp_unique {m r m' r' : ℕ} (h : m * (m + 1) + r = m' * (m' + 1) + r')
    (hr : r ≤ 2 * m + 1) (hr' : r' ≤ 2 * m' + 1) : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exfalso
    have : (m + 1) * (m + 2) ≤ m' * (m' + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  · exact heq
  · exfalso
    have : (m' + 1) * (m' + 2) ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

noncomputable def blk (n : ℕ) : ℕ := Classical.choose (decomp n)

lemma blk_spec (n : ℕ) : ∃ r, n = blk n * (blk n + 1) + r ∧ r ≤ 2 * blk n + 1 :=
  Classical.choose_spec (decomp n)

lemma blk_eq {n m r : ℕ} (h : n = m * (m + 1) + r) (hr : r ≤ 2 * m + 1) : blk n = m := by
  obtain ⟨r', h', hr'⟩ := blk_spec n
  exact decomp_unique (h'.symm.trans h) hr' hr

/-- The block description of A193358. -/
noncomputable def g (n : ℕ) : ℕ :=
  if n - blk n * (blk n + 1) = 2 * blk n then 2 * blk n + 1 else 2 * blk n + 2

lemma g_spec {n m r : ℕ} (h : n = m * (m + 1) + r) (hr : r ≤ 2 * m + 1) :
    g n = if r = 2 * m then 2 * m + 1 else 2 * m + 2 := by
  unfold g
  rw [blk_eq h hr]
  have : n - m * (m + 1) = r := by rw [h]; exact Nat.add_sub_cancel_left _ _
  rw [this]

lemma g_pos (n : ℕ) : 1 ≤ g n := by
  unfold g; split_ifs <;> omega

lemma g_rec (n : ℕ) (hn2 : 2 ≤ n) : g n = g (n - g (n - 2)) + 2 := by
  obtain ⟨r, hn, hr⟩ := blk_spec n
  set m := blk n
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hn hr; (simp at hn) <;> omega
    · exact ⟨m - 1, by omega⟩
  rw [hk] at hn hr
  have hQ : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * k + 2 := by ring
  rw [hQ] at hn
  have hgn := g_spec (n := n) (m := k + 1) (r := r) (by rw [hQ]; exact hn) hr
  generalize hP : k * (k + 1) = P at hn
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · interval_cases r
    · have h1 : g (n - 2) = 2 * k + 1 := by
        rw [g_spec (m := k) (r := 2 * k) (by rw [hP]; omega) (by omega)]; simp
      have h2 : g (n - (2 * k + 1)) = 2 * k + 2 := by
        rw [g_spec (m := k) (r := 1) (by rw [hP]; omega) (by omega)]; split_ifs <;> omega
      rw [hgn, h1, h2, if_neg (by omega)]; omega
    · have h1 : g (n - 2) = 2 * k + 2 := by
        rw [g_spec (m := k) (r := 2 * k + 1) (by rw [hP]; omega) (by omega)]; split_ifs <;> omega
      have h2 : g (n - (2 * k + 2)) = 2 * k + 2 := by
        rw [g_spec (m := k) (r := 1) (by rw [hP]; omega) (by omega)]; split_ifs <;> omega
      rw [hgn, h1, h2, if_neg (by omega)]; omega
  · have h1 : g (n - 2) = 2 * k + 4 := by
      rw [g_spec (m := k + 1) (r := r - 2) (by rw [hQ, hP]; omega) (by omega)]
      split_ifs <;> omega
    have h2 : g (n - (2 * k + 4)) = if r - 2 = 2 * k then 2 * k + 1 else 2 * k + 2 :=
      g_spec (m := k) (r := r - 2) (by rw [hP]; omega) (by omega)
    rw [hgn, h1, h2]; split_ifs <;> omega

lemma g_zero : g 0 = 1 := by rw [g_spec (m := 0) (r := 0) (by simp) (by simp)]; simp

lemma g_one : g 1 = 2 := by rw [g_spec (m := 0) (r := 1) (by simp) (by simp)]; simp

lemma isA_g : IsA193358 g := ⟨g_zero, g_one, g_rec⟩

lemma eq_g {f : ℕ → ℕ} (hf : IsA193358 f) (n : ℕ) : f n = g n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | h2
    · rw [hf.1, g_zero]
    · rw [hf.2.1, g_one]
    · rw [hf.2.2 n h2, g_rec n h2, ih (n - 2) (by omega)]
      have := g_pos (n - 2)
      rw [ih _ (by omega)]

lemma g_surj (k : ℕ) (hk : 1 ≤ k) : ∃ n, g n = k := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine ⟨i * (i + 1) + (2 * i + 1), ?_⟩
    rw [g_spec rfl (by omega)]; split_ifs <;> omega
  · refine ⟨j * (j + 1) + 2 * j, ?_⟩
    rw [g_spec rfl (by omega)]; split_ifs <;> omega

lemma g_odd_inj (a b : ℕ) (h : g a = g b) (hodd : g a % 2 = 1) : a = b := by
  obtain ⟨ra, ha, hra⟩ := blk_spec a
  obtain ⟨rb, hb, hrb⟩ := blk_spec b
  have ga := g_spec ha hra
  have gb := g_spec hb hrb
  rw [ga] at hodd h
  rw [gb] at h
  have hra' : ra = 2 * blk a := by by_contra hc; rw [if_neg hc] at hodd; omega
  rw [if_pos hra'] at h
  have hrb' : rb = 2 * blk b := by by_contra hc; rw [if_neg hc] at h; omega
  rw [if_pos hrb'] at h
  have hab : blk a = blk b := by omega
  rw [ha, hb, hra', hrb', hab]

end OMA_A193358_Proof

open OMA_A193358_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a193358.main := by
  refine ⟨⟨g, isA_g⟩, fun f hf => ?_⟩
  have hfg : f = g := funext (eq_g hf)
  subst hfg
  exact ⟨g_surj, g_odd_inj⟩
