import OMAReductions.R_Erdos186_erdos_186_R1

-- Step H1 of reduction Erdos186.erdos_186.R1: an explicit parabola gives F(N) ≥ 2k+1.
-- Credit: @GiridhariPradeep (agent: Claude Code, model claude-opus-5-5)
-- Checked against the merged reduction reductions/Erdos186.erdos_186.R1.lean (PR #9824).

open Finset

namespace OMA.E186

/-- The parabola point `i + 1 + L (i - k)^2`, as an integer. -/
def g (k i : ℕ) : ℤ := (i : ℤ) + 1 + ((k * (2 * k + 1) + 1 : ℕ) : ℤ) * ((i : ℤ) - k) ^ 2

def f (k i : ℕ) : ℕ := (g k i).toNat

lemma g_nonneg (k i : ℕ) : 0 ≤ g k i := by unfold g; positivity

lemma f_cast (k i : ℕ) : (f k i : ℤ) = g k i := Int.toNat_of_nonneg (g_nonneg k i)

lemma gauss (k : ℕ) : ∑ i ∈ range (2 * k + 1), (i : ℤ) = k * (2 * k + 1) := by
  have h := Finset.sum_range_id_mul_two (2 * k + 1)
  have h' : ((∑ i ∈ range (2 * k + 1), i : ℕ) : ℤ) * 2 = ((2 * k + 1) * (2 * k + 1 - 1) : ℕ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

lemma g_sub (k i a : ℕ) : g k i - g k a =
    ((i : ℤ) - a) * (1 + ((k * (2 * k + 1) + 1 : ℕ) : ℤ) * ((i : ℤ) - a)) +
    ((k * (2 * k + 1) + 1 : ℕ) : ℤ) * (2 * ((a : ℤ) - k)) * ((i : ℤ) - a) := by
  unfold g; ring

lemma g_inj (k : ℕ) {i j : ℕ} (h : g k i = g k j) : i = j := by
  set L : ℤ := ((k * (2 * k + 1) + 1 : ℕ) : ℤ) with hL
  have e : ((i : ℤ) - j) * (1 + L * ((i : ℤ) + j - 2 * k)) = 0 := by
    have := h; unfold g at this; rw [← hL] at this; linear_combination this
  rcases mul_eq_zero.mp e with h1 | h1
  · omega
  · have hd : L ∣ 1 := ⟨-((i : ℤ) + j - 2 * k), by linear_combination h1⟩
    have hL1 : L = 1 := by
      have hpos : 0 < L := by rw [hL]; positivity
      have := Int.eq_one_of_dvd_one hpos.le hd
      exact this
    have hk : k = 0 := by
      rw [hL] at hL1
      have : k * (2 * k + 1) = 0 := by omega
      rcases Nat.mul_eq_zero.mp this with h | h <;> omega
    subst hk
    have : ((i : ℤ) + j) * 1 = -1 := by
      have := h1; simp [hL1] at this; linear_combination this
    omega

theorem h1 : ∀ k : ℕ, 2 * k + 1 ≤
    Erdos186.F ((k * (2 * k + 1) + 1) * k ^ 2 + 2 * k + 1) := by
  intro k
  set L : ℕ := k * (2 * k + 1) + 1 with hL
  have hinj : Set.InjOn (f k) (range (2 * k + 1) : Set ℕ) := by
    intro i _ j _ hij
    apply g_inj k
    rw [← f_cast, ← f_cast, hij]
  have hcard : ((range (2 * k + 1)).image (f k)).card = 2 * k + 1 := by
    rw [card_image_of_injOn hinj, card_range]
  rw [← hcard]
  apply Erdos186.card_le_F
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [mem_range] at hi
    rw [mem_Icc]
    have hg : g k i ≤ ((L * k ^ 2 + 2 * k + 1 : ℕ) : ℤ) := by
      unfold g
      rw [← hL]
      have hsq : ((i : ℤ) - k) ^ 2 ≤ (k : ℤ) ^ 2 := by
        have h1 : -(k : ℤ) ≤ (i : ℤ) - k := by omega
        have h2 : (i : ℤ) - k ≤ k := by omega
        nlinarith
      have hL0 : (0 : ℤ) ≤ (L : ℤ) := by positivity
      push_cast
      nlinarith
    constructor
    · have : (1 : ℤ) ≤ (f k i : ℤ) := by
        rw [f_cast]; unfold g
        have : (0:ℤ) ≤ ((k * (2 * k + 1) + 1 : ℕ) : ℤ) * ((i : ℤ) - k) ^ 2 := by positivity
        linarith
      exact_mod_cast this
    · have : (f k i : ℤ) ≤ ((L * k ^ 2 + 2 * k + 1 : ℕ) : ℤ) := by rw [f_cast]; exact hg
      exact_mod_cast this
  · intro x hx S hS hS2 hsum
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    -- pull S back to indices
    set T := (range (2 * k + 1)).filter (fun i => f k i ∈ S) with hT
    have hST : T.image (f k) = S := by
      ext y; constructor
      · intro hy
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
        exact (mem_filter.mp hi).2
      · intro hy
        have hy' := hS hy
        obtain ⟨_, hyA⟩ := mem_erase.mp hy'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hyA
        exact mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, hy⟩, rfl⟩
    have hTsub : T ⊆ range (2 * k + 1) := filter_subset _ _
    have hinjT : Set.InjOn (f k) (T : Set ℕ) := hinj.mono (by exact_mod_cast hTsub)
    have hTa : a ∉ T := by
      intro haT
      have : f k a ∈ S := (mem_filter.mp haT).2
      exact (mem_erase.mp (hS this)).1 rfl
    have hcT : T.card = S.card := by rw [← hST, card_image_of_injOn hinjT]
    rw [← hST, sum_image hinjT, card_image_of_injOn hinjT] at hsum
    have hsumZ : ∑ i ∈ T, (g k i - g k a) = 0 := by
      have : ((∑ i ∈ T, f k i : ℕ) : ℤ) = ((T.card * f k a : ℕ) : ℤ) := by rw [hsum]
      push_cast at this
      simp only [f_cast] at this
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, this]; ring
    set Lz : ℤ := (L : ℤ) with hLz
    set U : ℤ := ∑ i ∈ T, ((i : ℤ) - a) with hU
    set Q : ℤ := ∑ i ∈ T, ((i : ℤ) - a) ^ 2 with hQ
    have key : U * (1 + Lz * (2 * ((a : ℤ) - k))) = -(Lz * Q) := by
      have : ∑ i ∈ T, (g k i - g k a) = U + Lz * Q + Lz * (2 * ((a : ℤ) - k)) * U := by
        simp only [g_sub, ← hL, ← hLz, hU, hQ, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl; intro i _; ring
      rw [hsumZ] at this; linear_combination -this
    have hdvd : Lz ∣ U := by
      have h1 : Lz ∣ U * (1 + Lz * (2 * ((a : ℤ) - k))) := ⟨-Q, by rw [key]; ring⟩
      have hcop : IsCoprime Lz (1 + Lz * (2 * ((a : ℤ) - k))) :=
        ⟨-(2 * ((a : ℤ) - k)), 1, by ring⟩
      exact hcop.dvd_of_dvd_mul_right h1
    have ha' : a < 2 * k + 1 := mem_range.mp ha
    have hUle : U ≤ k * (2 * k + 1) := by
      calc U ≤ ∑ i ∈ T, (i : ℤ) := sum_le_sum fun i _ => by omega
        _ ≤ ∑ i ∈ range (2 * k + 1), (i : ℤ) :=
            sum_le_sum_of_subset_of_nonneg hTsub fun i _ _ => by positivity
        _ = k * (2 * k + 1) := gauss k
    have hUge : -(k * (2 * k + 1) : ℤ) ≤ U := by
      have hrefl : ∑ i ∈ range (2 * k + 1), ((2 * k : ℤ) - i) = k * (2 * k + 1) := by
        rw [sum_sub_distrib, gauss, sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      have : ∑ i ∈ T, ((2 * k : ℤ) - i) ≤ k * (2 * k + 1) := by
        rw [← hrefl]
        apply sum_le_sum_of_subset_of_nonneg hTsub
        intro i hi _; have := mem_range.mp hi; omega
      have h2 : -∑ i ∈ T, ((2 * k : ℤ) - i) ≤ U := by
        rw [hU, ← sum_neg_distrib]; apply sum_le_sum; intro i _; omega
      linarith
    have hU0 : U = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have hLpos : (k * (2 * k + 1) : ℤ) + 1 = Lz := by rw [hLz, hL]; push_cast; ring
      have hc1 : c = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have : Lz * c ≤ -Lz := by nlinarith
          nlinarith
        · have : Lz ≤ Lz * c := by nlinarith
          nlinarith
      rw [hc, hc1, mul_zero]
    have hQ0 : Q = 0 := by
      have hLpos : 0 < Lz := by rw [hLz]; positivity
      rw [hU0, zero_mul] at key
      have : Lz * Q = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · omega
      · exact h
    have hTne : T.Nonempty := by
      rw [← card_pos, hcT]; omega
    obtain ⟨i, hi⟩ := hTne
    have hia : i ≠ a := fun h => hTa (h ▸ hi)
    have hpos : 0 < Q := by
      rw [hQ]
      apply sum_pos' (fun j _ => by positivity)
      have hne : (i : ℤ) - a ≠ 0 := by omega
      exact ⟨i, hi, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))⟩
    omega

end OMA.E186

theorem OMA.solution : OMA.R_Erdos186_erdos_186_R1.H1 := OMA.E186.h1
