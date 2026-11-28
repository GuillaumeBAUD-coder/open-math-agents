import OMAStatements.S_oeis_a004129
import Mathlib.Tactic

namespace OMA.P_oeis_a004129

open OMA.S_oeis_a004129

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℤ) (m n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) ^ m * f) =
      if m ≤ n then PowerSeries.coeff (n - m) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single (m, n - m)]
    · simp [PowerSeries.coeff_X_pow]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.mem_antidiagonal] at hab
      have ham : a ≠ m := fun ha => hne (Prod.ext ha (by omega))
      dsimp only
      rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hnot
  · refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    have ham : a ≠ m := by omega
    dsimp only
    rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]

private lemma covers_upper_bound (n m : ℕ) (h : CoversDistinctTwoSum n m) :
    2 * m ≤ n * (n - 1) := by
  rcases h with ⟨S, hScard, hcov⟩
  let P_lt := (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2)
  let P_gt := (S ×ˢ S).filter (fun p : ℕ × ℕ => p.2 < p.1)
  have hsub_img : Finset.Icc 1 m ⊆ P_lt.image (fun p : ℕ × ℕ => p.1 + p.2) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨a, ha, b, hb, hne, hab⟩ := hcov k hk.1 hk.2
    rw [Finset.mem_image]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hlt⟩, hab⟩
    · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hgt⟩, by omega⟩
  have hm_le : m ≤ P_lt.card := by
    have h1 := Finset.card_le_card hsub_img
    have h2 := Finset.card_image_le (s := P_lt) (f := fun p : ℕ × ℕ => p.1 + p.2)
    rw [Nat.card_Icc] at h1
    omega
  have hswap_card : P_lt.card = P_gt.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [P_lt, P_gt, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      simp only [P_lt, P_gt, Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
  have hdisj : Disjoint P_lt P_gt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [P_lt, P_gt, Finset.mem_filter] at hp1 hp2
    omega
  have hdiag_disj : Disjoint (P_lt ∪ P_gt) (S.image (fun a => (a, a))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_union, P_lt, P_gt, Finset.mem_filter, Finset.mem_image] at hp1 hp2
    rcases hp2 with ⟨a, _, rfl⟩
    rcases hp1 with h1 | h2 <;> omega
  have hunion_sub : (P_lt ∪ P_gt) ∪ (S.image (fun a => (a, a))) ⊆ S ×ˢ S := by
    intro p hp
    simp only [Finset.mem_union, P_lt, P_gt, Finset.mem_filter, Finset.mem_image,
      Finset.mem_product] at hp ⊢
    rcases hp with (h1 | h2) | ⟨a, ha, rfl⟩
    · exact h1.1
    · exact h2.1
    · exact ⟨ha, ha⟩
  have hcard_le := Finset.card_le_card hunion_sub
  rw [Finset.card_union_of_disjoint hdiag_disj, Finset.card_union_of_disjoint hdisj,
    Finset.card_product, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
    hScard, ← hswap_card] at hcard_le
  have hnn : n + n * (n - 1) = n * n := by
    cases n with
    | zero => simp
    | succ r => simp [Nat.mul_succ]; ring
  omega

private lemma A004129_26_le : A004129 26 ≤ 325 := by
  unfold A004129
  have hne : { m : ℕ | CoversDistinctTwoSum 26 m }.Nonempty :=
    ⟨0, ⟨Finset.range 26, Finset.card_range 26, fun k hk1 hk0 => by omega⟩⟩
  refine csSup_le hne fun m hm => ?_
  have h := covers_upper_bound 26 m hm
  omega

private theorem prove_disproof : ¬ type_of% @OMA.S_oeis_a004129.main := by
  intro hEq
  set A : PowerSeries ℤ := PowerSeries.mk fun k => (A004129 (k + 2) : ℤ)
  have hId : (1 - (PowerSeries.X : PowerSeries ℤ) ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 6) * A =
      1 + PowerSeries.C (3 : ℤ) * PowerSeries.X + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 2 +
        PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 3 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 4 +
        PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
    have hL : ((PowerSeries.X : PowerSeries ℤ) - 1) *
        (PowerSeries.X ^ 5 + PowerSeries.X ^ 4 + PowerSeries.X ^ 3 - PowerSeries.X - 1) =
        1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 6 := by ring
    have hR : ((PowerSeries.X : PowerSeries ℤ) ^ 4 + PowerSeries.X ^ 3 +
          PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 + PowerSeries.C (2 : ℤ) * PowerSeries.X + 1) *
        (PowerSeries.X ^ 2 + PowerSeries.X + 1) =
        1 + PowerSeries.C (3 : ℤ) * PowerSeries.X + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 2 +
          PowerSeries.C (5 : ℤ) * PowerSeries.X ^ 3 + PowerSeries.C (4 : ℤ) * PowerSeries.X ^ 4 +
          PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
      have h2 : (PowerSeries.C (2 : ℤ) : PowerSeries ℤ) = 2 := by simp
      have h3 : (PowerSeries.C (3 : ℤ) : PowerSeries ℤ) = 3 := by simp
      have h4 : (PowerSeries.C (4 : ℤ) : PowerSeries ℤ) = 4 := by simp
      have h5 : (PowerSeries.C (5 : ℤ) : PowerSeries ℤ) = 5 := by simp
      rw [h2, h3, h4, h5]; ring
    rw [← hL, ← hR]
    exact hEq
  have hstep : ∀ n : ℕ,
      (A004129 (n + 2) : ℤ) -
        (if 2 ≤ n then (A004129 n : ℤ) else 0) -
        (if 3 ≤ n then (A004129 (n - 1) : ℤ) else 0) +
        (if 6 ≤ n then (A004129 (n - 4) : ℤ) else 0) =
      (if n = 0 then 1 else 0) + 3 * (if n = 1 then 1 else 0) + 5 * (if n = 2 then 1 else 0) +
        5 * (if n = 3 then 1 else 0) + 4 * (if n = 4 then 1 else 0) +
        2 * (if n = 5 then 1 else 0) + (if n = 6 then 1 else 0) := by
    intro n
    have hc := congrArg (PowerSeries.coeff n) hId
    rw [add_mul, sub_mul, sub_mul, one_mul,
      map_add, map_sub, map_sub,
      map_add, map_add, map_add, map_add, map_add, map_add,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hc
    rw [coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq,
      PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X_pow] at hc
    simp only [A, PowerSeries.coeff_mk] at hc
    have h2 : (if 2 ≤ n then (A004129 (n - 2 + 2) : ℤ) else 0) =
        (if 2 ≤ n then (A004129 n : ℤ) else 0) := by
      split_ifs with h
      · rw [Nat.sub_add_cancel h]
      · rfl
    have h3 : (if 3 ≤ n then (A004129 (n - 3 + 2) : ℤ) else 0) =
        (if 3 ≤ n then (A004129 (n - 1) : ℤ) else 0) := by
      split_ifs with h
      · rw [show n - 3 + 2 = n - 1 by omega]
      · rfl
    have h6 : (if 6 ≤ n then (A004129 (n - 6 + 2) : ℤ) else 0) =
        (if 6 ≤ n then (A004129 (n - 4) : ℤ) else 0) := by
      split_ifs with h
      · rw [show n - 6 + 2 = n - 4 by omega]
      · rfl
    rw [h2, h3, h6] at hc
    exact hc
  have hrec : ∀ n : ℕ, 7 ≤ n →
      (A004129 (n + 2) : ℤ) =
        (A004129 n : ℤ) + (A004129 (n - 1) : ℤ) - (A004129 (n - 4) : ℤ) := by
    intro n hn
    have h := hstep n
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
    linarith
  have h2 : (A004129 2 : ℤ) = 1 := by
    have h := hstep 0
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num at h; linarith
  have h3 : (A004129 3 : ℤ) = 3 := by
    have h := hstep 1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num at h; linarith
  have h4 : (A004129 4 : ℤ) = 6 := by
    have h := hstep 2
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h2] at h; linarith
  have h5 : (A004129 5 : ℤ) = 9 := by
    have h := hstep 3
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h
    norm_num [h2, h3] at h; linarith
  have h6 : (A004129 6 : ℤ) = 13 := by
    have h := hstep 4
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h
    norm_num [h3, h4] at h; linarith
  have h7 : (A004129 7 : ℤ) = 17 := by
    have h := hstep 5
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h
    norm_num [h4, h5] at h; linarith
  have h8 : (A004129 8 : ℤ) = 22 := by
    have h := hstep 6
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)] at h
    norm_num [h2, h5, h6] at h; linarith
  have h9 : (A004129 9 : ℤ) = 27 := by have h := hrec 7 (by omega); norm_num [h3, h6, h7] at h; linarith
  have h10 : (A004129 10 : ℤ) = 33 := by have h := hrec 8 (by omega); norm_num [h4, h7, h8] at h; linarith
  have h11 : (A004129 11 : ℤ) = 40 := by have h := hrec 9 (by omega); norm_num [h5, h8, h9] at h; linarith
  have h12 : (A004129 12 : ℤ) = 47 := by have h := hrec 10 (by omega); norm_num [h6, h9, h10] at h; linarith
  have h13 : (A004129 13 : ℤ) = 56 := by have h := hrec 11 (by omega); norm_num [h7, h10, h11] at h; linarith
  have h14 : (A004129 14 : ℤ) = 65 := by have h := hrec 12 (by omega); norm_num [h8, h11, h12] at h; linarith
  have h15 : (A004129 15 : ℤ) = 76 := by have h := hrec 13 (by omega); norm_num [h9, h12, h13] at h; linarith
  have h16 : (A004129 16 : ℤ) = 88 := by have h := hrec 14 (by omega); norm_num [h10, h13, h14] at h; linarith
  have h17 : (A004129 17 : ℤ) = 101 := by have h := hrec 15 (by omega); norm_num [h11, h14, h15] at h; linarith
  have h18 : (A004129 18 : ℤ) = 117 := by have h := hrec 16 (by omega); norm_num [h12, h15, h16] at h; linarith
  have h19 : (A004129 19 : ℤ) = 133 := by have h := hrec 17 (by omega); norm_num [h13, h16, h17] at h; linarith
  have h20 : (A004129 20 : ℤ) = 153 := by have h := hrec 18 (by omega); norm_num [h14, h17, h18] at h; linarith
  have h21 : (A004129 21 : ℤ) = 174 := by have h := hrec 19 (by omega); norm_num [h15, h18, h19] at h; linarith
  have h22 : (A004129 22 : ℤ) = 198 := by have h := hrec 20 (by omega); norm_num [h16, h19, h20] at h; linarith
  have h23 : (A004129 23 : ℤ) = 226 := by have h := hrec 21 (by omega); norm_num [h17, h20, h21] at h; linarith
  have h24 : (A004129 24 : ℤ) = 255 := by have h := hrec 22 (by omega); norm_num [h18, h21, h22] at h; linarith
  have h25 : (A004129 25 : ℤ) = 291 := by have h := hrec 23 (by omega); norm_num [h19, h22, h23] at h; linarith
  have h26 : (A004129 26 : ℤ) = 328 := by have h := hrec 24 (by omega); norm_num [h20, h23, h24] at h; linarith
  have hle : (A004129 26 : ℤ) ≤ 325 := by exact_mod_cast A004129_26_le
  linarith

end OMA.P_oeis_a004129

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a004129.main) :=
  OMA.P_oeis_a004129.prove_disproof
