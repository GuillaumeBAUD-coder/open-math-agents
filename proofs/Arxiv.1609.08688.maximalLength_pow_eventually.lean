import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples
import Mathlib.Tactic

/-!
# Proof of maximalLength_pow_eventually
-/

section OMAHelpers

open Arxiv.«1609.08688»

lemma oma_bddAbove_lengths (n : ℕ) :
    BddAbove { List.length s | (s : List (Fin 3 → ℕ))
      (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) } := by
  refine ⟨max 1 (n ^ 2), ?_⟩
  rintro k ⟨s, hs_range, hs_inc, rfl⟩
  by_cases hn : 2 ≤ n
  · refine le_trans ?_ (le_max_right 1 (n ^ 2))
    by_contra hle
    have hs_len : n ^ 2 < s.length := Nat.lt_of_not_ge hle
    obtain ⟨i, j, hij, h0, h1⟩ := exists_pair_of_mem_Icc hn hs_range hs_len
    have hp : s.Pairwise lt₂ := hs_inc
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge)
        (List.pairwise_iff_get.1 hp i j hij')
    · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le)
        (List.pairwise_iff_get.1 hp j i hji')
  · refine le_trans ?_ (le_max_left 1 (n ^ 2))
    interval_cases n
    · cases s with
      | nil => simp
      | cons a tl =>
        have h0 := hs_range a List.mem_cons_self ⟨0, rfl⟩
        simp at h0
    · have h_const : ∀ a ∈ s, ∀ j, a j = 1 := by
        intro a ha j
        have hj := hs_range a ha ⟨j, rfl⟩
        rw [Set.mem_Icc] at hj
        omega
      have hlt := isIncreasing₂_const_length hs_inc h_const
      omega

lemma oma_exists_attaining (n : ℕ) :
    ∃ s : List (Fin 3 → ℕ), (∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) ∧
      IsIncreasing₂ s ∧ s.length = maximalLength n := by
  have hne : { List.length s | (s : List (Fin 3 → ℕ))
      (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }.Nonempty :=
    ⟨0, [], by simp, isIncreasing₂_nil, rfl⟩
  obtain ⟨s, hs_range, hs_inc, hlen⟩ := Nat.sSup_mem hne (oma_bddAbove_lengths n)
  exact ⟨s, hs_range, hs_inc, hlen⟩

lemma oma_le_maximalLength {n : ℕ} {s : List (Fin 3 → ℕ)}
    (hs_range : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs_inc : IsIncreasing₂ s) :
    s.length ≤ maximalLength n :=
  le_csSup (oma_bddAbove_lengths n) ⟨s, hs_range, hs_inc, rfl⟩

lemma oma_maximalLength_mono {m n : ℕ} (hmn : m ≤ n) :
    maximalLength m ≤ maximalLength n := by
  obtain ⟨s, hs_range, hs_inc, hlen⟩ := oma_exists_attaining m
  rw [← hlen]
  refine oma_le_maximalLength (fun a ha => ?_) hs_inc
  exact Set.Subset.trans (hs_range a ha) (Set.Icc_subset_Icc_right hmn)

def oma_comb (n : ℕ) (a b : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun i => (a i - 1) * n + b i

lemma oma_comb_lt₂_left {m n : ℕ} {a₁ a₂ b₁ b₂ : Fin 3 → ℕ}
    (ha₁ : Set.range a₁ ⊆ Set.Icc 1 m)
    (hb₁ : Set.range b₁ ⊆ Set.Icc 1 n)
    (hb₂ : Set.range b₂ ⊆ Set.Icc 1 n)
    (h : lt₂ a₁ a₂) : lt₂ (oma_comb n a₁ b₁) (oma_comb n a₂ b₂) := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  refine ⟨i, j, hij, ?_, ?_⟩
  · have ha₁i := (Set.mem_Icc.1 (ha₁ ⟨i, rfl⟩)).1
    have hb₁i := (Set.mem_Icc.1 (hb₁ ⟨i, rfl⟩)).2
    have hb₂i := (Set.mem_Icc.1 (hb₂ ⟨i, rfl⟩)).1
    have hsub : (a₁ i - 1) + 1 ≤ a₂ i - 1 := by omega
    have hmul : ((a₁ i - 1) + 1) * n ≤ (a₂ i - 1) * n := Nat.mul_le_mul_right n hsub
    dsimp [oma_comb]
    linarith [Nat.succ_mul (a₁ i - 1) n]
  · have ha₁j := (Set.mem_Icc.1 (ha₁ ⟨j, rfl⟩)).1
    have hb₁j := (Set.mem_Icc.1 (hb₁ ⟨j, rfl⟩)).2
    have hb₂j := (Set.mem_Icc.1 (hb₂ ⟨j, rfl⟩)).1
    have hsub : (a₁ j - 1) + 1 ≤ a₂ j - 1 := by omega
    have hmul : ((a₁ j - 1) + 1) * n ≤ (a₂ j - 1) * n := Nat.mul_le_mul_right n hsub
    dsimp [oma_comb]
    linarith [Nat.succ_mul (a₁ j - 1) n]

lemma oma_comb_lt₂_right {n : ℕ} (a : Fin 3 → ℕ) {b₁ b₂ : Fin 3 → ℕ}
    (h : lt₂ b₁ b₂) : lt₂ (oma_comb n a b₁) (oma_comb n a b₂) := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  exact ⟨i, j, hij, by dsimp [oma_comb]; omega, by dsimp [oma_comb]; omega⟩

lemma oma_comb_range {m n : ℕ} {a b : Fin 3 → ℕ}
    (ha : Set.range a ⊆ Set.Icc 1 m) (hb : Set.range b ⊆ Set.Icc 1 n) :
    Set.range (oma_comb n a b) ⊆ Set.Icc 1 (m * n) := by
  rintro x ⟨i, rfl⟩
  have hai := Set.mem_Icc.1 (ha ⟨i, rfl⟩)
  have hbi := Set.mem_Icc.1 (hb ⟨i, rfl⟩)
  rw [Set.mem_Icc]
  dsimp [oma_comb]
  refine ⟨by omega, ?_⟩
  have hsub : (a i - 1) + 1 ≤ m := by omega
  have hmul : ((a i - 1) + 1) * n ≤ m * n := Nat.mul_le_mul_right n hsub
  linarith [Nat.succ_mul (a i - 1) n]

lemma oma_flatMap_isIncreasing₂ {m n : ℕ} :
    ∀ {s : List (Fin 3 → ℕ)},
      (∀ a ∈ s, Set.range a ⊆ Set.Icc 1 m) →
      IsIncreasing₂ s →
      ∀ {t : List (Fin 3 → ℕ)},
        (∀ b ∈ t, Set.range b ⊆ Set.Icc 1 n) →
        IsIncreasing₂ t →
        IsIncreasing₂ (s.flatMap (fun a => t.map (oma_comb n a)))
  | [], _, _, _, _, _ => by simp [IsIncreasing₂]
  | a :: s, hs_range, hs_inc, t, ht_range, ht_inc => by
    rw [IsIncreasing₂, List.flatMap_cons, List.pairwise_append]
    have hcons := List.pairwise_cons.1 hs_inc
    refine ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map (oma_comb n a) (fun b₁ b₂ hb => oma_comb_lt₂_right a hb) ht_inc
    · exact oma_flatMap_isIncreasing₂ (fun x hx => hs_range x (List.mem_cons_of_mem a hx))
        hcons.2 ht_range ht_inc
    · intro x hx y hy
      rw [List.mem_map] at hx
      rcases hx with ⟨b₁, hb₁, rfl⟩
      rw [List.mem_flatMap] at hy
      rcases hy with ⟨a₂, ha₂, hy'⟩
      rw [List.mem_map] at hy'
      rcases hy' with ⟨b₂, hb₂, rfl⟩
      exact oma_comb_lt₂_left (hs_range a List.mem_cons_self)
        (ht_range b₁ hb₁) (ht_range b₂ hb₂) (hcons.1 a₂ ha₂)

lemma oma_flatMap_length {α β γ : Type*} (f : α → β → γ) :
    ∀ (s : List α) (t : List β),
      (s.flatMap (fun a => t.map (f a))).length = s.length * t.length
  | [], t => by simp
  | a :: s, t => by
    simp [List.flatMap_cons, oma_flatMap_length f s t, Nat.add_mul, Nat.add_comm]

lemma oma_maximalLength_mul (m n : ℕ) :
    maximalLength m * maximalLength n ≤ maximalLength (m * n) := by
  obtain ⟨s, hs_range, hs_inc, hslen⟩ := oma_exists_attaining m
  obtain ⟨t, ht_range, ht_inc, htlen⟩ := oma_exists_attaining n
  rw [← hslen, ← htlen, ← oma_flatMap_length (oma_comb n) s t]
  refine oma_le_maximalLength ?_ (oma_flatMap_isIncreasing₂ hs_range hs_inc ht_range ht_inc)
  intro x hx
  rw [List.mem_flatMap] at hx
  rcases hx with ⟨a, ha, hx'⟩
  rw [List.mem_map] at hx'
  rcases hx' with ⟨b, hb, rfl⟩
  exact oma_comb_range (hs_range a ha) (ht_range b hb)

lemma oma_maximalLength_pow_nat (n k : ℕ) :
    maximalLength n ^ k ≤ maximalLength (n ^ k) := by
  induction k with
  | zero => simp [maximalLength_one]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (Nat.mul_le_mul_right (maximalLength n) ih) (oma_maximalLength_mul (n ^ k) n)

end OMAHelpers

theorem OMA.solution : type_of% @Arxiv.«1609.08688».maximalLength_pow_eventually := by
  intro n e hn h b hb
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hFn_ge_one : 1 ≤ Arxiv.«1609.08688».maximalLength n := by
    have h1 := oma_maximalLength_mono (Nat.le_of_lt hn)
    simpa [Arxiv.«1609.08688».maximalLength_one] using h1
  have hne_ge_one : (1 : ℝ) ≤ (n : ℝ) ^ e := by
    rw [← h]
    exact_mod_cast hFn_ge_one
  have he_nonneg : 0 ≤ e := by
    by_contra he_not_nonneg
    have he_neg : e < 0 := lt_of_not_ge he_not_nonneg
    have hlt : (n : ℝ) ^ e < (n : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hn1 he_neg
    rw [Real.rpow_zero] at hlt
    linarith
  have hne_pos : 0 < (n : ℝ) ^ e := Real.rpow_pos_of_pos hn0 e
  have hdiff_pos : 0 < e - b := sub_pos.2 hb
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (((n : ℝ) ^ e) ^ (1 / (e - b))))
  rw [Filter.eventually_atTop]
  refine ⟨M, fun m hm => ?_⟩
  have hM_lt_m : max 1 (((n : ℝ) ^ e) ^ (1 / (e - b))) < (m : ℝ) :=
    lt_of_lt_of_le hM (by exact_mod_cast hm)
  have hm_gt_one : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM_lt_m
  have hm_pos_real : (0 : ℝ) < (m : ℝ) := by linarith
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    rw [hm0] at hm_gt_one
    norm_num at hm_gt_one
  set k := Nat.log n m
  have hk_low : n ^ k ≤ m := Nat.pow_log_le_self n hm_ne_zero
  have hk_high : m < n ^ (k + 1) := Nat.lt_pow_succ_log_self hn m
  have hFm_nat : Arxiv.«1609.08688».maximalLength n ^ k ≤ Arxiv.«1609.08688».maximalLength m :=
    le_trans (oma_maximalLength_pow_nat n k) (oma_maximalLength_mono hk_low)
  have hFm_real : ((n : ℝ) ^ e) ^ k ≤ (Arxiv.«1609.08688».maximalLength m : ℝ) := by
    rw [← h]
    exact_mod_cast hFm_nat
  have hm_le_pow : (m : ℝ) ≤ ((n ^ (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast le_of_lt hk_high
  have hm_rpow_le : (m : ℝ) ^ e ≤ (((n ^ (k + 1) : ℕ) : ℝ)) ^ e :=
    Real.rpow_le_rpow (le_of_lt hm_pos_real) hm_le_pow he_nonneg
  have hpow_Id : (((n ^ (k + 1) : ℕ) : ℝ)) ^ e = ((n : ℝ) ^ e) ^ k * (n : ℝ) ^ e := by
    push_cast
    rw [← Real.rpow_natCast (n : ℝ) (k + 1), ← Real.rpow_mul (le_of_lt hn0)]
    push_cast
    rw [add_mul, one_mul, Real.rpow_add hn0, ← Real.rpow_natCast ((n : ℝ) ^ e) k,
      ← Real.rpow_mul (le_of_lt hn0), mul_comm e (k : ℝ)]
  have h_upper : (m : ℝ) ^ e ≤ (Arxiv.«1609.08688».maximalLength m : ℝ) * (n : ℝ) ^ e := by
    calc (m : ℝ) ^ e
      _ ≤ (((n ^ (k + 1) : ℕ) : ℝ)) ^ e := hm_rpow_le
      _ = ((n : ℝ) ^ e) ^ k * (n : ℝ) ^ e := hpow_Id
      _ ≤ (Arxiv.«1609.08688».maximalLength m : ℝ) * (n : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right hFm_real (le_of_lt hne_pos)
  have h_thresh_base : ((n : ℝ) ^ e) ^ (1 / (e - b)) ≤ (m : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hM_lt_m)
  have h_thresh : (n : ℝ) ^ e ≤ (m : ℝ) ^ (e - b) := by
    have h0_base : 0 ≤ ((n : ℝ) ^ e) ^ (1 / (e - b)) :=
      Real.rpow_nonneg (le_of_lt hne_pos) _
    have h1 := Real.rpow_le_rpow h0_base h_thresh_base (le_of_lt hdiff_pos)
    rw [← Real.rpow_mul (le_of_lt hne_pos), one_div_mul_cancel (ne_of_gt hdiff_pos),
      Real.rpow_one] at h1
    exact h1
  have h_prod : (m : ℝ) ^ b * (n : ℝ) ^ e ≤ (m : ℝ) ^ e := by
    have hmb_pos : 0 ≤ (m : ℝ) ^ b := Real.rpow_nonneg (le_of_lt hm_pos_real) b
    calc (m : ℝ) ^ b * (n : ℝ) ^ e
      _ ≤ (m : ℝ) ^ b * (m : ℝ) ^ (e - b) := mul_le_mul_of_nonneg_left h_thresh hmb_pos
      _ = (m : ℝ) ^ (b + (e - b)) := (Real.rpow_add hm_pos_real b (e - b)).symm
      _ = (m : ℝ) ^ e := by ring_nf
  have h_final : (m : ℝ) ^ b * (n : ℝ) ^ e ≤ (Arxiv.«1609.08688».maximalLength m : ℝ) * (n : ℝ) ^ e :=
    le_trans h_prod h_upper
  exact le_of_mul_le_mul_right h_final hne_pos
