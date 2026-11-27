import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_bounds_R1

-- Step Erdos1186.erdos_1186.variants.prs_bounds.R1.H3: hypothesis H3 of reduction Erdos1186.erdos_1186.variants.prs_bounds.R1
-- Credit: @ptc-prover-bot
-- H3 := ∀ (n : ℕ) (c : ℕ → Bool),     let X := ((Icc 1 n ×ˢ Icc 1 n).filter       (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n)).card     (n : ℝ) ^ 2 / 2 ≤       2 * (monoCount 3 n c : ℝ) + n + X + ((n : ℝ) + 1) ^ 2 / 8  private theorem mono_le_sq (n k : ℕ) (c : ℕ → Bool) : monoCount k n c ≤ n ^ 2 := by   unfold monoCount   have h := card_filter_le (s := Icc 1 n ×ˢ Icc 1 n)     (fun p : ℕ × ℕ => p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1)   simpa only [card_product, Nat.card_Icc, Nat.add_sub_cancel, pow_two] using h  set_option maxHeartbeats 600000 in

/-! Erdos1186 prs_bounds R1.H3 .
S = ordered pairs (a, b) in [1,n]² of equal parity, m = (a+b)/2.
(A) for 2 colours: 2 = 2·[mono] + [a≠m] + [b≠m] + [a≠b];
(B) #{a≠m} ≤ X and #{b≠m} ≤ X (injections p ↦ (a, m), (b, m));
(C) #mono ≤ n + 2·monoCount (diagonal, a < b, a > b, each injected);
(D) 2·#{a≠b} ≤ |S| (per parity class: 2|R||B| ≤ |P|²/2);
(E) n² ≤ 2|S| (|S| = |P0|² + |P1|², |P0| + |P1| = n).
Then 4n² ≤ 16M + 8n + 8X + (n+1)². -/

open Finset Erdos1186

namespace OMA.H3proof

lemma diff_pairs (P : Finset ℕ) (c : ℕ → Bool) :
    2 * ((P ×ˢ P).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2)).card ≤ P.card * P.card := by
  classical
  set R := P.filter (fun a => c a = true) with hR
  set B := P.filter (fun a => ¬ c a = true) with hB
  have hRB : R.card + B.card = P.card := card_filter_add_card_filter_not _
  have hsub : (P ×ˢ P).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2) ⊆ R ×ˢ B ∪ B ×ˢ R := by
    rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_product] at h
    simp only [hR, hB, mem_union, mem_product, mem_filter]
    obtain ⟨⟨ha, hb⟩, hne⟩ := h
    cases hca : c a <;> cases hcb : c b <;> simp_all
  have h1 := card_le_card hsub
  have h2 := card_union_le (R ×ˢ B) (B ×ˢ R)
  rw [card_product, card_product] at h2
  have h3 : (4 * R.card * B.card : ℤ) ≤ ((R.card : ℤ) + B.card) ^ 2 := by
    nlinarith [sq_nonneg ((R.card : ℤ) - B.card)]
  have h4 : 4 * R.card * B.card ≤ (R.card + B.card) ^ 2 := by exact_mod_cast h3
  rw [hRB] at h4
  nlinarith

theorem main_ineq (n : ℕ) (c : ℕ → Bool) :
    let X := ((Icc 1 n ×ˢ Icc 1 n).filter
      (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n)).card
    (n : ℝ) ^ 2 / 2 ≤ 2 * (monoCount 3 n c : ℝ) + n + X + ((n : ℝ) + 1) ^ 2 / 8 := by
  classical
  intro X
  set P0 := (Icc 1 n).filter (fun a => a % 2 = 0) with hP0
  set P1 := (Icc 1 n).filter (fun a => ¬ a % 2 = 0) with hP1
  set S := P0 ×ˢ P0 ∪ P1 ×ˢ P1 with hS
  have memS : ∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ n ∧ p.1 % 2 = p.2 % 2 := by
    intro p hp
    simp only [hS, hP0, hP1, mem_union, mem_product, mem_filter, mem_Icc] at hp
    omega
  -- (A) pointwise identity, summed
  have hpt : ∀ p ∈ S, 2 = 2 * (if c p.1 = c ((p.1 + p.2) / 2) ∧ c p.2 = c ((p.1 + p.2) / 2)
      then 1 else 0) + (if c p.1 ≠ c ((p.1 + p.2) / 2) then 1 else 0)
      + (if c p.2 ≠ c ((p.1 + p.2) / 2) then 1 else 0) + (if c p.1 ≠ c p.2 then 1 else 0) := by
    intro p _
    generalize c p.1 = x
    generalize c p.2 = y
    generalize c ((p.1 + p.2) / 2) = z
    cases x <;> cases y <;> cases z <;> decide
  have hsum := Finset.sum_congr rfl hpt
  simp only [sum_add_distrib, ← mul_sum, sum_boole, sum_const, smul_eq_mul, Nat.cast_id] at hsum
  set T := S.filter (fun p => c p.1 = c ((p.1 + p.2) / 2) ∧ c p.2 = c ((p.1 + p.2) / 2)) with hT
  set E1 := S.filter (fun p => c p.1 ≠ c ((p.1 + p.2) / 2)) with hE1
  set E2 := S.filter (fun p => c p.2 ≠ c ((p.1 + p.2) / 2)) with hE2
  set D := S.filter (fun p => c p.1 ≠ c p.2) with hD
  set Xs := (Icc 1 n ×ˢ Icc 1 n).filter
      (fun p : ℕ × ℕ => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n) with hXs
  -- (B)
  have hB1 : E1.card ≤ X := by
    apply card_le_card_of_injOn (fun p => (p.1, (p.1 + p.2) / 2))
    · intro p hp
      rw [coe_filter, Set.mem_ofPred_eq] at hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hp.1
      simp only [mem_coe, hXs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h1, h2⟩, by omega, by omega⟩, hp.2, by omega, by omega⟩
    · intro p hp q hq hpq
      rw [coe_filter, Set.mem_ofPred_eq] at hp hq
      have := memS p hp.1
      have := memS q hq.1
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (by omega)
  have hB2 : E2.card ≤ X := by
    apply card_le_card_of_injOn (fun p => (p.2, (p.1 + p.2) / 2))
    · intro p hp
      rw [coe_filter, Set.mem_ofPred_eq] at hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hp.1
      simp only [mem_coe, hXs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h3, h4⟩, by omega, by omega⟩, hp.2, by omega, by omega⟩
    · intro p hp q hq hpq
      rw [coe_filter, Set.mem_ofPred_eq] at hp hq
      have := memS p hp.1
      have := memS q hq.1
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (by omega) hpq.1
  -- (C)
  set Ms := (Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ =>
      p.1 + (3 - 1) * p.2 ≤ n ∧ ∀ i < 3, c (p.1 + i * p.2) = c p.1) with hMs
  have hM : monoCount 3 n c = Ms.card := by rw [hMs]; unfold monoCount; convert rfl
  have hlt : (T.filter (fun p => p.1 < p.2)).card ≤ Ms.card := by
    apply card_le_card_of_injOn (fun p => (p.1, (p.2 - p.1) / 2))
    · intro p hp
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp
      obtain ⟨⟨hpS, hc1, hc2⟩, hlt⟩ := hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hpS
      simp only [mem_coe, hMs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h1, h2⟩, by omega, by omega⟩, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simp
      · rw [show p.1 + 1 * ((p.2 - p.1) / 2) = (p.1 + p.2) / 2 by omega]; exact hc1.symm
      · rw [show p.1 + 2 * ((p.2 - p.1) / 2) = p.2 by omega, hc2, hc1]
    · intro p hp q hq hpq
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp hq
      have := memS p hp.1.1
      have := memS q hq.1.1
      have := hp.2
      have := hq.2
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (by omega)
  have hgt : (T.filter (fun p => p.2 < p.1)).card ≤ Ms.card := by
    apply card_le_card_of_injOn (fun p => (p.2, (p.1 - p.2) / 2))
    · intro p hp
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp
      obtain ⟨⟨hpS, hc1, hc2⟩, hgt⟩ := hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := memS p hpS
      simp only [mem_coe, hMs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨h3, h4⟩, by omega, by omega⟩, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simp
      · rw [show p.2 + 1 * ((p.1 - p.2) / 2) = (p.1 + p.2) / 2 by omega]; exact hc2.symm
      · rw [show p.2 + 2 * ((p.1 - p.2) / 2) = p.1 by omega, hc1, hc2]
    · intro p hp q hq hpq
      simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp hq
      have := memS p hp.1.1
      have := memS q hq.1.1
      have := hp.2
      have := hq.2
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (by omega) hpq.1
  have hdiag : (T.filter (fun p => p.1 = p.2)).card ≤ n := by
    calc (T.filter (fun p => p.1 = p.2)).card ≤ (Icc 1 n).card := by
          apply card_le_card_of_injOn (fun p => p.1)
          · intro p hp
            simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp
            obtain ⟨h1, h2, -⟩ := memS p hp.1.1
            simp only [mem_coe, mem_Icc]
            exact ⟨h1, h2⟩
          · intro p hp q hq hpq
            simp only [coe_filter, Set.mem_ofPred_eq, hT, mem_filter] at hp hq
            exact Prod.ext hpq (by rw [← hp.2, ← hq.2]; exact hpq)
      _ = n := by simp
  have hTsplit : T.card ≤ (T.filter (fun p => p.1 = p.2)).card +
      (T.filter (fun p => p.1 < p.2)).card + (T.filter (fun p => p.2 < p.1)).card := by
    calc T.card ≤ ((T.filter (fun p => p.1 = p.2)) ∪ (T.filter (fun p => p.1 < p.2)) ∪
          (T.filter (fun p => p.2 < p.1))).card := by
          apply card_le_card
          intro p hp
          simp only [mem_union, mem_filter]
          rcases lt_trichotomy p.1 p.2 with h | h | h
          · exact Or.inl (Or.inr ⟨hp, h⟩)
          · exact Or.inl (Or.inl ⟨hp, h⟩)
          · exact Or.inr ⟨hp, h⟩
      _ ≤ _ := by
          refine (card_union_le _ _).trans ?_
          exact Nat.add_le_add_right (card_union_le _ _) _
  have hTle : T.card ≤ n + 2 * monoCount 3 n c := by rw [hM]; omega
  -- (D), (E)
  have hdisj : Disjoint (P0 ×ˢ P0) (P1 ×ˢ P1) := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [hP0, hP1, mem_product, mem_filter] at h1 h2
    omega
  have hScard : S.card = P0.card * P0.card + P1.card * P1.card := by
    rw [hS, card_union_of_disjoint hdisj, card_product, card_product]
  have hP : P0.card + P1.card = n := by
    rw [hP0, hP1, card_filter_add_card_filter_not]
    simp
  have hDle : 2 * D.card ≤ S.card := by
    have hDsub : D ⊆ ((P0 ×ˢ P0).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2)) ∪
        ((P1 ×ˢ P1).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2)) := by
      intro p hp
      simp only [hD, hS, mem_filter, mem_union] at hp ⊢
      rcases hp.1 with h | h
      · exact Or.inl ⟨h, hp.2⟩
      · exact Or.inr ⟨h, hp.2⟩
    have := card_le_card hDsub
    have := card_union_le ((P0 ×ˢ P0).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2))
      ((P1 ×ˢ P1).filter (fun p : ℕ × ℕ => c p.1 ≠ c p.2))
    have := diff_pairs P0 c
    have := diff_pairs P1 c
    omega
  have hSge : n ^ 2 ≤ 2 * S.card := by
    rw [hScard, ← hP]
    nlinarith [sq_nonneg ((P0.card : ℤ) - P1.card)]
  -- combine
  have key : 4 * n ^ 2 ≤ 16 * monoCount 3 n c + 8 * n + 8 * X + (n + 1) ^ 2 := by
    nlinarith
  have keyR : (4 : ℝ) * (n : ℝ) ^ 2 ≤
      16 * (monoCount 3 n c : ℝ) + 8 * n + 8 * X + ((n : ℝ) + 1) ^ 2 := by
    exact_mod_cast key
  linarith

end OMA.H3proof

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_bounds_R1.H3 := by
  intro n c
  exact OMA.H3proof.main_ineq n c

