import OMAReductions.R_Erdos158_erdos_158_R1

-- Step Erdos158.erdos_158.R1.H1: every infinite Sidon set A has liminf |A ∩ [0, N)| / √N = 0 (Erdős).
-- Credit: @marcusbuffett. Original proof. The positive differences of a Sidon set are distinct, so
-- at most 2D ordered pairs lie at distance below D. Cut [0, D K^J) into blocks of length D; if
-- |A ∩ [0, N)| ≥ c √N eventually, Cauchy-Schwarz on each range of blocks [K^j, K^(j+1)) gives a
-- sum of squared block counts of at least D / K per range, J D / K in all, against 4 D from the
-- pair bound: impossible once J > 4 K.

/-! Erdős's theorem on the lower density of infinite Sidon sets, by the block-counting argument. -/

open Filter Real Finset

open scoped Classical

namespace OMA.R_Erdos158_erdos_158_R1.Sidon


/-- `|A ∩ [0, n)|` as a finset count. -/
noncomputable def cnt (A : Set ℕ) (n : ℕ) : ℕ := ((range n).filter (· ∈ A)).card

/-- The elements of `A` in the block `[iD, iD + D)`. -/
noncomputable def blk (A : Set ℕ) (D i : ℕ) : Finset ℕ :=
  (Ico (i * D) (i * D + D)).filter (· ∈ A)

lemma cnt_eq (A : Set ℕ) (n : ℕ) : (A ∩ Set.Iio n).ncard = cnt A n := by
  unfold cnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [and_comm]

/-- In a Sidon set, at most `2D` ordered pairs of distinct elements lie at distance below `D`:
the map `(x, y) ↦ y - x` is injective on such pairs. -/
lemma pairs_le {A : Set ℕ} (hA : IsSidon A) (D : ℕ) (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧ p.1 < p.2 + D ∧ p.2 < p.1 + D) :
    P.card ≤ 2 * D := by
  have h : P.card ≤ (Finset.Ioo (-(D : ℤ)) D).card := by
    apply Finset.card_le_card_of_injOn (fun p => (p.2 : ℤ) - p.1)
    · intro p hp
      obtain ⟨-, -, -, h1, h2⟩ := hP p hp
      simp only [Finset.coe_Ioo, Set.mem_Ioo]
      omega
    · intro p hp q hq hpq
      obtain ⟨hp1, hp2, hp3, -, -⟩ := hP p hp
      obtain ⟨hq1, hq2, hq3, -, -⟩ := hP q hq
      simp only at hpq
      have hs : p.2 + q.1 = q.2 + p.1 := by omega
      rcases hA p.2 hp2 q.2 hq2 q.1 hq1 p.1 hp1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h2.symm h1
      · exact absurd h1.symm hp3
  simp only [Int.card_Ioo] at h
  omega

lemma cnt_sq_le {A : Set ℕ} (hA : IsSidon A) (X : ℕ) :
    cnt A X * cnt A X ≤ 2 * X + cnt A X := by
  have h := pairs_le hA X ((range X).filter (· ∈ A)).offDiag (by
    intro p hp
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.1.2, hp.2.1.2, hp.2.2, by omega, by omega⟩)
  rw [Finset.offDiag_card] at h
  exact Nat.sub_le_iff_le_add.1 h

lemma cnt_sq_le_four {A : Set ℕ} (hA : IsSidon A) (X : ℕ) (hX : 1 ≤ X) :
    (cnt A X : ℝ) ^ 2 ≤ 4 * X := by
  have h' : (cnt A X : ℝ) * cnt A X ≤ 2 * X + cnt A X := by exact_mod_cast cnt_sq_le hA X
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have h0 : (0 : ℝ) ≤ cnt A X := by positivity
  rcases Nat.lt_or_ge (cnt A X) 2 with h2 | h2
  · have : (cnt A X : ℝ) ≤ 1 := by exact_mod_cast (by omega : cnt A X ≤ 1)
    nlinarith
  · have : (2 : ℝ) ≤ cnt A X := by exact_mod_cast h2
    nlinarith

lemma cnt_add (A : Set ℕ) {m n : ℕ} (h : m ≤ n) :
    cnt A m + ((Ico m n).filter (· ∈ A)).card = cnt A n := by
  unfold cnt
  rw [card_filter, card_filter, card_filter]
  exact sum_range_add_sum_Ico _ h

lemma cnt_add_sum_blk (A : Set ℕ) (D lo : ℕ) :
    ∀ hi, lo ≤ hi → cnt A (lo * D) + ∑ i ∈ Ico lo hi, (blk A D i).card = cnt A (hi * D) := by
  intro hi hhi
  induction hi, hhi using Nat.le_induction with
  | base => simp
  | succ hi hle ih =>
    rw [sum_Ico_succ_top hle, ← add_assoc, ih, blk, cnt_add A (by omega : hi * D ≤ hi * D + D)]
    congr 1
    ring

/-- Ordered pairs inside the same block: at most `2D` in all. -/
lemma blocks_le {A : Set ℕ} (hA : IsSidon A) (D M : ℕ) :
    ∑ i ∈ range M, ((blk A D i).card * (blk A D i).card - (blk A D i).card) ≤ 2 * D := by
  simp only [← Finset.offDiag_card]
  rw [← Finset.card_sigma]
  have hinj : Set.InjOn (fun x : (Σ _ : ℕ, ℕ × ℕ) => x.2)
      ((range M).sigma (fun i => (blk A D i).offDiag) : Set (Σ _ : ℕ, ℕ × ℕ)) := by
    rintro ⟨i, p⟩ hx ⟨j, q⟩ hy hpq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_offDiag, blk,
      Finset.mem_filter, Finset.mem_Ico] at hx hy
    simp only at hpq
    subst hpq
    have hij : i = j := by
      rcases lt_trichotomy i j with h | h | h
      · have : (i + 1) * D ≤ j * D := Nat.mul_le_mul_right _ h
        rw [add_mul, one_mul] at this
        omega
      · exact h
      · have : (j + 1) * D ≤ i * D := Nat.mul_le_mul_right _ h
        rw [add_mul, one_mul] at this
        omega
    subst hij
    rfl
  rw [← Finset.card_image_of_injOn hinj]
  apply pairs_le hA D
  intro p hp
  simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_offDiag, blk, Finset.mem_filter,
    Finset.mem_Ico, Finset.mem_range] at hp
  obtain ⟨⟨i, q⟩, ⟨-, ⟨⟨h1, h1A⟩, ⟨h2, h2A⟩, hne⟩⟩, rfl⟩ := hp
  exact ⟨h1A, h2A, hne, by omega, by omega⟩

lemma sq_gap (x z y : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) (hy : 0 ≤ y) (h1 : 9 * y ≤ x ^ 2)
    (h2 : z ^ 2 ≤ 4 * y) : y ≤ (x - z) ^ 2 := by
  have hr : √y ^ 2 = y := Real.sq_sqrt hy
  have hr0 : 0 ≤ √y := Real.sqrt_nonneg y
  have h3 : 3 * √y ≤ x := by
    rw [← pow_le_pow_iff_left₀ (by positivity) hx two_ne_zero]
    nlinarith
  have h4 : z ≤ 2 * √y := by
    rw [← pow_le_pow_iff_left₀ hz (by positivity) two_ne_zero]
    nlinarith
  calc y = √y ^ 2 := hr.symm
    _ ≤ (x - z) ^ 2 := pow_le_pow_left₀ hr0 (by linarith) 2

lemma sum_ranges (g : ℕ → ℝ) (K : ℕ) (hK : 0 < K) (J : ℕ) :
    ∑ j ∈ range J, ∑ i ∈ Ico (K ^ j) (K ^ (j + 1)), g i = ∑ i ∈ Ico 1 (K ^ J), g i := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih, sum_Ico_consecutive _ (Nat.one_le_pow _ _ hK)
      (Nat.pow_le_pow_right hK (Nat.le_succ J))]

theorem sidon_liminf (A : Set ℕ) (hA : IsSidon A) :
    liminf (fun N : ℕ => (A ∩ .Iio N).ncard * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 := by
  have key : ∀ c : ℝ, 0 < c →
      ¬ ∀ᶠ N : ℕ in atTop, c ≤ (A ∩ .Iio N).ncard * (N : ℝ) ^ (- 1 / 2 : ℝ) := by
    intro c hc hev
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    have hlow : ∀ N, N0 ≤ N → 1 ≤ N → c ^ 2 * N ≤ (cnt A N : ℝ) ^ 2 := by
      intro N hN h1
      have h := hN0 N hN
      rw [cnt_eq] at h
      have hNpos : (0 : ℝ) < N := by exact_mod_cast h1
      have hr : (N : ℝ) ^ (-1 / 2 : ℝ) = (√(N : ℝ))⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hNpos.le]
        norm_num
      rw [hr, ← div_eq_mul_inv] at h
      have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNpos
      have h' : c * √N ≤ cnt A N := (le_div_iff₀ hs).1 h
      have hsq : (√(N : ℝ)) ^ 2 = N := Real.sq_sqrt hNpos.le
      calc c ^ 2 * (N : ℝ) = (c * √(N : ℝ)) ^ 2 := by rw [mul_pow, hsq]
        _ ≤ ((cnt A N : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
    obtain ⟨K0, hK0⟩ := exists_nat_gt (9 / c ^ 2)
    obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = K0 + 2 := ⟨_, rfl⟩
    have hK : 0 < K := by omega
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hcK : 9 ≤ c ^ 2 * K := by
      have h9 : 9 < c ^ 2 * K0 := by
        rw [div_lt_iff₀ (by positivity)] at hK0
        linarith
      have : (K0 : ℝ) ≤ K := by exact_mod_cast (by omega : K0 ≤ K)
      nlinarith [sq_nonneg c]
    obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = 4 * K + 1 := ⟨_, rfl⟩
    obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = K ^ J := ⟨_, rfl⟩
    obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = N0 + M + 1 := ⟨_, rfl⟩
    have hD1 : 0 < D := by omega
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD1
    obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℝ, b = fun i => ((blk A D i).card : ℝ) := ⟨_, rfl⟩
    -- each range of blocks `[K^j, K^(j+1))` carries at least `D / K`
    have hrange : ∀ j, (D : ℝ) / K ≤ ∑ i ∈ Ico (K ^ j) (K ^ (j + 1)), b i ^ 2 := by
      intro j
      have hlo1 : 0 < K ^ j := pow_pos hK _
      have hhi1 : 0 < K ^ (j + 1) := pow_pos hK _
      have hle : K ^ j ≤ K ^ (j + 1) := Nat.pow_le_pow_right hK (Nat.le_succ j)
      have hsum := cnt_add_sum_blk A D (K ^ j) (K ^ (j + 1)) hle
      have hsr : ∑ i ∈ Ico (K ^ j) (K ^ (j + 1)), b i =
          ((cnt A (K ^ (j + 1) * D) : ℕ) : ℝ) - ((cnt A (K ^ j * D) : ℕ) : ℝ) := by
        have : ((cnt A (K ^ j * D) : ℕ) : ℝ) + ∑ i ∈ Ico (K ^ j) (K ^ (j + 1)), b i =
            ((cnt A (K ^ (j + 1) * D) : ℕ) : ℝ) := by
          simp only [hbdef]
          exact_mod_cast hsum
        linarith
      have hN1 : N0 ≤ K ^ (j + 1) * D := by
        have : N0 ≤ D := by omega
        nlinarith
      have h1 := hlow _ hN1 (Nat.mul_pos hhi1 hD1)
      have hlo := cnt_sq_le_four hA (K ^ j * D) (Nat.mul_pos hlo1 hD1)
      push_cast at h1 hlo
      have hy0 : (0 : ℝ) ≤ (K : ℝ) ^ j * D := by positivity
      have h9 : 9 * ((K : ℝ) ^ j * D) ≤ ((cnt A (K ^ (j + 1) * D) : ℕ) : ℝ) ^ 2 := by
        have e : c ^ 2 * ((K : ℝ) ^ (j + 1) * D) = (c ^ 2 * K) * ((K : ℝ) ^ j * D) := by ring
        rw [e] at h1
        nlinarith
      have hgap := sq_gap _ _ _ (by positivity) (by positivity) hy0 h9 hlo
      have hcs := sq_sum_le_card_mul_sum_sq (s := Ico (K ^ j) (K ^ (j + 1))) (f := b)
      rw [hsr, Nat.card_Ico] at hcs
      have hcard : ((K ^ (j + 1) - K ^ j : ℕ) : ℝ) ≤ (K : ℝ) * (K : ℝ) ^ j := by
        have : K ^ (j + 1) - K ^ j ≤ K * K ^ j := (Nat.sub_le _ _).trans (le_of_eq (by ring))
        exact_mod_cast this
      have hS : 0 ≤ ∑ i ∈ Ico (K ^ j) (K ^ (j + 1)), b i ^ 2 :=
        sum_nonneg fun i _ => sq_nonneg _
      have hkj : (0 : ℝ) < (K : ℝ) ^ j := by positivity
      have hprod := mul_le_mul_of_nonneg_right hcard hS
      have h2 : (K : ℝ) ^ j * D ≤
          (K : ℝ) ^ j * (K * ∑ i ∈ Ico (K ^ j) (K ^ (j + 1)), b i ^ 2) := by
        nlinarith
      have h3 := le_of_mul_le_mul_left h2 hkj
      rw [div_le_iff₀ hKr]
      linarith
    -- the pair bound caps the sum of squared block counts by `4 D`
    have htot : ∑ i ∈ range M, b i ^ 2 ≤ 4 * D := by
      have hnat := blocks_le hA D M
      have hsplit : ∑ i ∈ range M, (blk A D i).card * (blk A D i).card =
          ∑ i ∈ range M, ((blk A D i).card * (blk A D i).card - (blk A D i).card) +
            ∑ i ∈ range M, (blk A D i).card := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun i _ => (Nat.sub_add_cancel (Nat.le_mul_self _)).symm
      have hcnt := cnt_add_sum_blk A D 0 M (Nat.zero_le _)
      simp only [zero_mul, ← range_eq_Ico] at hcnt
      have h0 : cnt A 0 = 0 := by simp [cnt]
      rw [h0, zero_add] at hcnt
      have hle : ∑ i ∈ range M, (blk A D i).card * (blk A D i).card ≤
          2 * D + cnt A (M * D) := by
        rw [hsplit, hcnt]; omega
      have hMD : M ≤ D := by omega
      have hc4 := cnt_sq_le_four hA (M * D) (Nat.mul_pos (by rw [hMdef]; exact pow_pos hK _) hD1)
      have hcD : ((cnt A (M * D) : ℕ) : ℝ) ≤ 2 * D := by
        have hMDr : ((M * D : ℕ) : ℝ) ≤ (D : ℝ) * D := by
          have : M * D ≤ D * D := Nat.mul_le_mul_right _ hMD
          exact_mod_cast this
        have h0' : (0 : ℝ) ≤ ((cnt A (M * D) : ℕ) : ℝ) := by positivity
        nlinarith
      have hler : ∑ i ∈ range M, b i ^ 2 ≤ 2 * D + ((cnt A (M * D) : ℕ) : ℝ) := by
        rw [hbdef]
        simp only [sq]
        exact_mod_cast hle
      linarith
    have hsub : ∑ i ∈ Ico 1 M, b i ^ 2 ≤ ∑ i ∈ range M, b i ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [mem_Ico, mem_range] at hi ⊢
        omega
      · intro i _ _
        exact sq_nonneg _
    have hJsum : (J : ℝ) * (D / K) ≤ ∑ i ∈ Ico 1 M, b i ^ 2 := by
      rw [hMdef, ← sum_ranges (fun i => b i ^ 2) K hK J]
      have := sum_le_sum (s := range J) (fun j _ => hrange j)
      simpa [sum_const, card_range, nsmul_eq_mul] using this
    have hJr : (J : ℝ) = 4 * K + 1 := by rw [hJdef]; push_cast; ring
    have hKD : (K : ℝ) * (D / K) = D := by field_simp
    have hfin : (J : ℝ) * (D / K) = 4 * D + D / K := by
      rw [hJr]
      linear_combination 4 * hKD
    have : (0 : ℝ) < D / K := div_pos hDr hKr
    linarith
  have h0mem : (0 : ℝ) ∈ {a : ℝ | ∀ᶠ n : ℕ in atTop,
      a ≤ ((A ∩ Set.Iio n).ncard : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ)} :=
    Filter.Eventually.of_forall fun N => by positivity
  have hbdd : ∀ a ∈ {a : ℝ | ∀ᶠ n : ℕ in atTop,
      a ≤ ((A ∩ Set.Iio n).ncard : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ)}, a ≤ 0 := by
    intro a ha
    by_contra h
    push_neg at h
    exact key a h ha
  rw [liminf_eq]
  exact le_antisymm (csSup_le ⟨0, h0mem⟩ hbdd) (le_csSup ⟨0, fun a ha => hbdd a ha⟩ h0mem)

end OMA.R_Erdos158_erdos_158_R1.Sidon

theorem OMA.solution : OMA.R_Erdos158_erdos_158_R1.H1 := fun A _ hA =>
  OMA.R_Erdos158_erdos_158_R1.Sidon.sidon_liminf A hA
