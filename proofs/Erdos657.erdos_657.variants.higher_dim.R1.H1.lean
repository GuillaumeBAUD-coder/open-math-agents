import OMAReductions.R_Erdos657_erdos_657_variants_higher_dim_R1
import Mathlib

/-!
Proof of Erdos657.erdos_657.variants.higher_dim.R1.H1 via Balog-Szemeredi-Gowers,
Pluennecke-Ruzsa, Freiman-2 embedding into Z, Ruzsa modeling into ZMod p, and Roth's 3AP theorem.
-/

open Finset
open scoped Pointwise Combinatorics.Additive EuclideanGeometry Classical

namespace Erdos657H1Aux

/- ### Part 1: Balog-Szemeredi-Gowers theorem -/

private lemma rep_le_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (s : G) :
    ((A ×ˢ A).filter (fun p => p.1 + p.2 = s)).card ≤ A.card := by
  refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p₁ hp₁ p₂ hp₂ h => ?_)
  · simp only [mem_coe, mem_filter, mem_product] at hp
    exact hp.1.1
  · simp only [mem_coe, mem_filter, mem_product] at hp₁ hp₂
    ext
    · exact h
    · have h1 : p₁.1 + p₁.2 = p₂.1 + p₂.2 := hp₁.2.trans hp₂.2.symm
      rw [h] at h1
      exact add_left_cancel h1

private lemma sum_rep_eq_sq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) :
    ∑ s ∈ A + A, ((A ×ˢ A).filter (fun p => p.1 + p.2 = s)).card = A.card ^ 2 := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilt : (A ×ˢ A).filter (fun p => p.1 + p.2 ∈ A + A) = A ×ˢ A := by
    rw [filter_eq_self]
    intro p hp
    rw [mem_product] at hp
    exact add_mem_add hp.1 hp.2
  rw [hfilt, card_product, sq]

theorem balog_szemeredi_gowers {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (M : ℕ) (hM : 1 ≤ M) (hA : A.Nonempty)
    (hE : A.card ^ 3 ≤ M * Finset.addEnergy A A) :
    ∃ A' ⊆ A, A'.Nonempty ∧ A.card ≤ 8 * M * A'.card ∧
      (A' - A').card ≤ (2 ^ 27 * M ^ 10) * A'.card := by
  set n := A.card with hn_def
  have hn_pos : 0 < n := hA.card_pos
  have hM_pos : 0 < M := by omega
  let r : G → ℕ := fun s => ((A ×ˢ A).filter (fun p => p.1 + p.2 = s)).card
  have hE_sum : Finset.addEnergy A A = ∑ s ∈ A + A, r s ^ 2 :=
    Finset.addEnergy_eq_sum_sq' A A
  have hr_sum : ∑ s ∈ A + A, r s = n ^ 2 := sum_rep_eq_sq A
  have hr_le : ∀ s, r s ≤ n := fun s => rep_le_card A s
  let P : Finset G := (A + A).filter (fun s => n ≤ 2 * M * r s)
  have hP_card : P.card ≤ 2 * M * n := by
    have h1 : P.card * n ≤ 2 * M * n ^ 2 := calc
      P.card * n = ∑ _s ∈ P, n := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ s ∈ P, 2 * M * r s := sum_le_sum (fun s hs => (mem_filter.mp hs).2)
      _ = 2 * M * ∑ s ∈ P, r s := by rw [mul_sum]
      _ ≤ 2 * M * ∑ s ∈ A + A, r s := by
        gcongr
        exact filter_subset _ _
      _ = 2 * M * n ^ 2 := by rw [hr_sum]
    have h2 : P.card * n ≤ (2 * M * n) * n := by linarith [sq n]
    exact Nat.le_of_mul_le_mul_right h2 hn_pos
  have hsum_P_sq : n ^ 3 ≤ 2 * M * ∑ s ∈ P, r s ^ 2 := by
    have hnotP : 2 * M * ∑ s ∈ (A + A).filter (fun s => ¬ (n ≤ 2 * M * r s)), r s ^ 2 ≤ n ^ 3 := by
      calc
        2 * M * ∑ s ∈ (A + A).filter (fun s => ¬ (n ≤ 2 * M * r s)), r s ^ 2
            = ∑ s ∈ (A + A).filter (fun s => ¬ (n ≤ 2 * M * r s)), (2 * M * r s) * r s := by
              rw [mul_sum]
              refine sum_congr rfl fun s _ => ?_
              ring
        _ ≤ ∑ s ∈ (A + A).filter (fun s => ¬ (n ≤ 2 * M * r s)), n * r s := by
              refine sum_le_sum fun s hs => ?_
              have hlt : 2 * M * r s < n := not_le.mp (mem_filter.mp hs).2
              exact Nat.mul_le_mul_right (r s) hlt.le
        _ = n * ∑ s ∈ (A + A).filter (fun s => ¬ (n ≤ 2 * M * r s)), r s := by rw [mul_sum]
        _ ≤ n * ∑ s ∈ A + A, r s := by
              gcongr
              exact filter_subset _ _
        _ = n ^ 3 := by rw [hr_sum]; ring
    have hsplit : ∑ s ∈ P, r s ^ 2 +
        ∑ s ∈ (A + A).filter (fun s => ¬ (n ≤ 2 * M * r s)), r s ^ 2 =
        Finset.addEnergy A A := by
      rw [hE_sum, sum_filter_add_sum_filter_not]
    have h2E : 2 * n ^ 3 ≤ 2 * M * Finset.addEnergy A A := by nlinarith
    linarith [h2E, hnotP, show 2 * M * Finset.addEnergy A A =
      2 * M * ∑ s ∈ P, r s ^ 2 +
      2 * M * ∑ s ∈ (A + A).filter (fun s => ¬ (n ≤ 2 * M * r s)), r s ^ 2 by
      rw [← mul_add, hsplit]]
  have hsum_P : n ^ 2 ≤ 2 * M * ∑ s ∈ P, r s := by
    have h1 : n ^ 3 ≤ (2 * M * ∑ s ∈ P, r s) * n := calc
      n ^ 3 ≤ 2 * M * ∑ s ∈ P, r s ^ 2 := hsum_P_sq
      _ ≤ 2 * M * ∑ s ∈ P, r s * n := by
            gcongr with s
            rw [sq]
            exact Nat.mul_le_mul_left (r s) (hr_le s)
      _ = (2 * M * ∑ s ∈ P, r s) * n := by rw [← sum_mul]; ring
    have h2 : n ^ 2 * n ≤ (2 * M * ∑ s ∈ P, r s) * n := by linarith [pow_succ n 2]
    exact Nat.le_of_mul_le_mul_right h2 hn_pos
  let N : G → Finset G := fun a => A.filter (fun b => a + b ∈ P)
  have hN_symm : ∀ a b, a ∈ A → b ∈ A → (b ∈ N a ↔ a ∈ N b) := by
    intro a b ha hb
    simp only [N, mem_filter, ha, hb, true_and, add_comm]
  have hsum_N : ∑ b ∈ A, (N b).card = ∑ s ∈ P, r s := by
    have h1 : ∑ b ∈ A, (N b).card = ((A ×ˢ A).filter (fun p => p.1 + p.2 ∈ P)).card := by
      have hcard_eq : ∀ b ∈ A, (N b).card =
          ∑ a ∈ A, if b + a ∈ P then 1 else 0 := by
        intro b _
        dsimp only [N]
        rw [Finset.card_filter]
      rw [sum_congr rfl hcard_eq, ← sum_product', Finset.card_filter]
    rw [h1, Finset.sum_card_fiberwise_eq_card_filter]
  have hCS : n ^ 3 ≤ 4 * M ^ 2 * ∑ b ∈ A, (N b).card ^ 2 := by
    have hsq := sq_sum_le_card_mul_sum_sq (s := A) (f := fun b => (N b).card)
    have h4 : n ^ 4 ≤ (2 * M * ∑ b ∈ A, (N b).card) ^ 2 := by
      rw [hsum_N]
      have : (n ^ 2) ^ 2 ≤ (2 * M * ∑ s ∈ P, r s) ^ 2 := Nat.pow_le_pow_left hsum_P 2
      linarith
    have h5 : n ^ 3 * n ≤ (4 * M ^ 2 * ∑ b ∈ A, (N b).card ^ 2) * n := calc
      n ^ 3 * n = n ^ 4 := by ring
      _ ≤ (2 * M * ∑ b ∈ A, (N b).card) ^ 2 := h4
      _ = 4 * M ^ 2 * (∑ b ∈ A, (N b).card) ^ 2 := by ring
      _ ≤ 4 * M ^ 2 * (n * ∑ b ∈ A, (N b).card ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = (4 * M ^ 2 * ∑ b ∈ A, (N b).card ^ 2) * n := by ring
    exact Nat.le_of_mul_le_mul_right h5 hn_pos
  let K : ℕ := 256 * M ^ 2
  let isBad : G × G → Prop := fun p => K * (N p.1 ∩ N p.2).card < n
  let Bad : Finset (G × G) := (A ×ˢ A).filter isBad
  let badPairs : G → Finset (G × G) := fun b => (N b ×ˢ N b).filter isBad
  have hsum_bad : ∑ b ∈ A, (badPairs b).card = ∑ p ∈ Bad, (N p.1 ∩ N p.2).card := by
    have h1 : ∀ b ∈ A, (badPairs b).card =
        ∑ p ∈ Bad, if b ∈ N p.1 ∩ N p.2 then 1 else 0 := by
      intro b hb
      have hsub : (N b ×ˢ N b).filter isBad = Bad.filter (fun p => b ∈ N p.1 ∩ N p.2) := by
        ext ⟨a₁, a₂⟩
        simp only [Bad, mem_filter, mem_product, mem_inter]
        constructor
        · rintro ⟨⟨ha₁, ha₂⟩, hbad⟩
          have ha₁A : a₁ ∈ A := (mem_filter.mp ha₁).1
          have ha₂A : a₂ ∈ A := (mem_filter.mp ha₂).1
          refine ⟨⟨⟨ha₁A, ha₂A⟩, hbad⟩, ?_, ?_⟩
          · exact (hN_symm a₁ b ha₁A hb).mpr ha₁
          · exact (hN_symm a₂ b ha₂A hb).mpr ha₂
        · rintro ⟨⟨⟨ha₁A, ha₂A⟩, hbad⟩, hb₁, hb₂⟩
          refine ⟨⟨?_, ?_⟩, hbad⟩
          · exact (hN_symm a₁ b ha₁A hb).mp hb₁
          · exact (hN_symm a₂ b ha₂A hb).mp hb₂
      dsimp only [badPairs]
      rw [hsub, Finset.card_filter]
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun p _ => ?_
    have hsub : N p.1 ∩ N p.2 ⊆ A := (inter_subset_left).trans (filter_subset _ _)
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, inter_eq_right.mpr hsub]
  have hK_bad : K * ∑ b ∈ A, (badPairs b).card ≤ n ^ 3 := by
    rw [hsum_bad, mul_sum]
    calc
      ∑ p ∈ Bad, K * (N p.1 ∩ N p.2).card ≤ ∑ _p ∈ Bad, n := by
        refine sum_le_sum fun p hp => ?_
        exact (mem_filter.mp hp).2.le
      _ = Bad.card * n := by rw [sum_const, smul_eq_mul]
      _ ≤ (A ×ˢ A).card * n := Nat.mul_le_mul_right n (card_le_card (filter_subset _ _))
      _ = n ^ 3 := by rw [card_product]; ring
  have hsum_lt : ∑ b ∈ A, (K * (badPairs b).card + n ^ 2) <
      ∑ b ∈ A, (16 * M ^ 2 * (N b).card ^ 2) := by
    rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, ← mul_sum, ← hn_def]
    have h1 : K * ∑ b ∈ A, (badPairs b).card + n * n ^ 2 ≤ 2 * n ^ 3 := by
      have : n * n ^ 2 = n ^ 3 := by ring
      omega
    have h2 : 4 * n ^ 3 ≤ 16 * M ^ 2 * ∑ b ∈ A, (N b).card ^ 2 := by nlinarith [hCS]
    have h3 : 0 < n ^ 3 := by positivity
    omega
  obtain ⟨b₀, _, hb₀⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  set X := N b₀ with hX_def
  set m := X.card with hm_def
  have hX_sub : X ⊆ A := filter_subset _ _
  have hm_big : n < 4 * M * m := by
    have hsq : n ^ 2 < (4 * M * m) ^ 2 := by
      have : 16 * M ^ 2 * m ^ 2 = (4 * M * m) ^ 2 := by ring
      omega
    by_contra hle
    push Not at hle
    have := Nat.pow_le_pow_left hle 2
    omega
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, mul_zero] at hm_big
    omega
  have hbad_small : 16 * (badPairs b₀).card < m ^ 2 := by
    have h1 : (16 * M ^ 2) * (16 * (badPairs b₀).card) < (16 * M ^ 2) * m ^ 2 := by
      have hK_eq : K * (badPairs b₀).card = (16 * M ^ 2) * (16 * (badPairs b₀).card) := by
        dsimp only [K]; ring
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  let badDeg : G → ℕ := fun x => (X.filter (fun y => isBad (x, y))).card
  have hsum_badDeg : ∑ x ∈ X, badDeg x = (badPairs b₀).card := by
    have h1 : ∀ x ∈ X, badDeg x = ∑ y ∈ X, if isBad (x, y) then 1 else 0 := by
      intro x _
      dsimp only [badDeg]
      rw [Finset.card_filter]
    rw [sum_congr rfl h1, ← sum_product', ← Finset.card_filter]
  let A' : Finset G := X.filter (fun x => 8 * badDeg x < m)
  have hA'_sub_X : A' ⊆ X := filter_subset _ _
  have hA'_sub : A' ⊆ A := hA'_sub_X.trans hX_sub
  have hA'_large : m < 2 * A'.card := by
    let Y := X.filter (fun x => ¬ (8 * badDeg x < m))
    have hY_mul : 2 * Y.card * m < m * m := by
      have h1 : Y.card * m ≤ 8 * (badPairs b₀).card := calc
        Y.card * m = ∑ _x ∈ Y, m := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ Y, 8 * badDeg x := sum_le_sum (fun x hx => not_lt.mp (mem_filter.mp hx).2)
        _ = 8 * ∑ x ∈ Y, badDeg x := by rw [mul_sum]
        _ ≤ 8 * ∑ x ∈ X, badDeg x := Nat.mul_le_mul_left 8 (sum_le_sum_of_subset (filter_subset _ _))
        _ = 8 * (badPairs b₀).card := by rw [hsum_badDeg]
      have h2 : 2 * Y.card * m ≤ 16 * (badPairs b₀).card := by linarith
      linarith [sq m, hbad_small]
    have hY_lt : 2 * Y.card < m := Nat.lt_of_mul_lt_mul_right hY_mul
    have hcard_split : A'.card + Y.card = m := card_filter_add_card_filter_not _
    omega
  have hA'_nonempty : A'.Nonempty := Finset.card_pos.mp (by omega)
  have hA'_bound : n ≤ 8 * M * A'.card := by
    have : 4 * M * m ≤ 4 * M * (2 * A'.card) := Nat.mul_le_mul_left _ hA'_large.le
    linarith
  let Good : G → G → Finset G := fun a₁ a₂ =>
    A'.filter (fun a₃ => ¬ isBad (a₁, a₃) ∧ ¬ isBad (a₂, a₃))
  have hGood_card : ∀ a₁ ∈ A', ∀ a₂ ∈ A', A'.card ≤ 2 * (Good a₁ a₂).card := by
    intro a₁ ha₁ a₂ ha₂
    have hd1 : 8 * badDeg a₁ < m := (mem_filter.mp ha₁).2
    have hd2 : 8 * badDeg a₂ < m := (mem_filter.mp ha₂).2
    let B1 := A'.filter (fun a₃ => isBad (a₁, a₃))
    let B2 := A'.filter (fun a₃ => isBad (a₂, a₃))
    have hB1 : B1.card ≤ badDeg a₁ :=
      card_le_card (fun x hx => mem_filter.mpr ⟨hA'_sub_X (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
    have hB2 : B2.card ≤ badDeg a₂ :=
      card_le_card (fun x hx => mem_filter.mpr ⟨hA'_sub_X (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
    have hcov : A' ⊆ Good a₁ a₂ ∪ (B1 ∪ B2) := by
      intro x hx
      by_cases h1 : isBad (a₁, x)
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hx, h1⟩))
      · by_cases h2 : isBad (a₂, x)
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hx, h2⟩))
        · exact mem_union_left _ (mem_filter.mpr ⟨hx, h1, h2⟩)
    have hcard_le : A'.card ≤ (Good a₁ a₂).card + B1.card + B2.card := by
      have := (card_le_card hcov).trans (card_union_le _ _)
      have := this.trans (Nat.add_le_add_left (card_union_le _ _) _)
      omega
    omega
  have hmem_sub : ∀ d ∈ A' - A', ∃ p : G × G, p.1 ∈ A' ∧ p.2 ∈ A' ∧ p.1 - p.2 = d := by
    intro d hd
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Finset.mem_sub.mp hd
    exact ⟨(a₁, a₂), ha₁, ha₂, rfl⟩
  let wit : G → G × G := fun d =>
    if hd : d ∈ A' - A' then Classical.choose (hmem_sub d hd) else (b₀, b₀)
  have hwit_spec : ∀ d ∈ A' - A', (wit d).1 ∈ A' ∧ (wit d).2 ∈ A' ∧ (wit d).1 - (wit d).2 = d := by
    intro d hd
    simp only [wit, dif_pos hd]
    exact Classical.choose_spec (hmem_sub d hd)
  let Paths : G → Finset (Σ _ : G, G × G) := fun d =>
    (Good (wit d).1 (wit d).2).sigma (fun a₃ => (N (wit d).1 ∩ N a₃) ×ˢ (N a₃ ∩ N (wit d).2))
  have hPaths_card : ∀ d ∈ A' - A', A'.card * n ^ 2 ≤ 2 * K ^ 2 * (Paths d).card := by
    intro d hd
    obtain ⟨ha₁, ha₂, _⟩ := hwit_spec d hd
    have hgood := hGood_card (wit d).1 ha₁ (wit d).2 ha₂
    have hsum : (Good (wit d).1 (wit d).2).card * n ^ 2 ≤ K ^ 2 * (Paths d).card := by
      rw [card_sigma, mul_sum, ← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun a₃ ha₃ => ?_
      have ⟨h1, h2⟩ := (mem_filter.mp ha₃).2
      have hle1 : n ≤ K * (N (wit d).1 ∩ N a₃).card := not_lt.mp h1
      have hle2 : n ≤ K * (N a₃ ∩ N (wit d).2).card := by
        rw [inter_comm]
        exact not_lt.mp h2
      rw [card_product]
      have hmul := Nat.mul_le_mul hle1 hle2
      linarith [sq n, sq K]
    have hmul2 := Nat.mul_le_mul_left 2 hsum
    have hmul3 := Nat.mul_le_mul_right (n ^ 2) hgood
    linarith
  let allPaths := (A' - A').sigma Paths
  let f : (Σ _ : G, Σ _ : G, G × G) → (G × G) × (G × G) := fun x =>
    let d := x.1
    let a₃ := x.2.1
    let b₁ := x.2.2.1
    let b₂ := x.2.2.2
    (((wit d).1 + b₁, a₃ + b₁), (a₃ + b₂, (wit d).2 + b₂))
  have hall_le : allPaths.card ≤ P.card ^ 4 := by
    have hP4 : ((P ×ˢ P) ×ˢ (P ×ˢ P)).card = P.card ^ 4 := by
      simp only [card_product]; ring
    rw [← hP4]
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro x hx
      simp only [mem_coe, allPaths, Paths, mem_sigma, mem_product, mem_inter] at hx
      obtain ⟨hd, ha₃, ⟨hb₁1, hb₁3⟩, ⟨hb₂3, hb₂2⟩⟩ := hx
      simp only [mem_coe, f, mem_product]
      exact ⟨⟨(mem_filter.mp hb₁1).2, (mem_filter.mp hb₁3).2⟩,
        ⟨(mem_filter.mp hb₂3).2, (mem_filter.mp hb₂2).2⟩⟩
    · intro x hx y hy hxy
      simp only [mem_coe, allPaths, Paths, mem_sigma] at hx hy
      obtain ⟨hdx, _⟩ := hx
      obtain ⟨hdy, _⟩ := hy
      simp only [f, Prod.mk.injEq] at hxy
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hxy
      have hd_eq : x.1 = y.1 := by
        have hwx := (hwit_spec x.1 hdx).2.2
        have hwy := (hwit_spec y.1 hdy).2.2
        calc
          x.1 = (wit x.1).1 - (wit x.1).2 := hwx.symm
          _ = ((wit x.1).1 + x.2.2.1) - (x.2.1 + x.2.2.1) +
              (x.2.1 + x.2.2.2) - ((wit x.1).2 + x.2.2.2) := by abel
          _ = ((wit y.1).1 + y.2.2.1) - (y.2.1 + y.2.2.1) +
              (y.2.1 + y.2.2.2) - ((wit y.1).2 + y.2.2.2) := by rw [h1, h2, h3, h4]
          _ = (wit y.1).1 - (wit y.1).2 := by abel
          _ = y.1 := hwy
      cases x with | mk dx px =>
      cases y with | mk dy py =>
      dsimp only at hd_eq h1 h2 h3 h4
      subst hd_eq
      have hb₁ : px.2.1 = py.2.1 := add_left_cancel h1
      rw [hb₁] at h2
      have ha₃ : px.1 = py.1 := add_right_cancel h2
      rw [ha₃] at h3
      have hb₂ : px.2.2 = py.2.2 := add_left_cancel h3
      cases px with | mk a3x bx =>
      cases py with | mk a3y by_ =>
      cases bx; cases by_
      dsimp only at ha₃ hb₁ hb₂
      subst ha₃; subst hb₁; subst hb₂
      rfl
  have hfinal : (A' - A').card * A'.card * n ^ 2 ≤ 2 * K ^ 2 * P.card ^ 4 := calc
    (A' - A').card * A'.card * n ^ 2
        = ∑ _d ∈ A' - A', A'.card * n ^ 2 := by rw [sum_const, smul_eq_mul, mul_assoc]
    _ ≤ ∑ d ∈ A' - A', 2 * K ^ 2 * (Paths d).card := sum_le_sum hPaths_card
    _ = 2 * K ^ 2 * allPaths.card := by rw [← mul_sum, card_sigma]
    _ ≤ 2 * K ^ 2 * P.card ^ 4 := Nat.mul_le_mul_left _ hall_le
  have hP4_le : P.card ^ 4 ≤ (2 * M * n) ^ 4 := Nat.pow_le_pow_left hP_card 4
  have hstep1 : (A' - A').card * A'.card * n ^ 2 ≤
      (32 * K ^ 2 * M ^ 4 * n ^ 2) * n ^ 2 := by
    calc
      (A' - A').card * A'.card * n ^ 2 ≤ 2 * K ^ 2 * (2 * M * n) ^ 4 :=
        hfinal.trans (Nat.mul_le_mul_left _ hP4_le)
      _ = (32 * K ^ 2 * M ^ 4 * n ^ 2) * n ^ 2 := by ring
  have hstep2 : (A' - A').card * A'.card ≤ 32 * K ^ 2 * M ^ 4 * n ^ 2 :=
    Nat.le_of_mul_le_mul_right hstep1 (by positivity)
  have hn2_le : n ^ 2 ≤ (8 * M * A'.card) ^ 2 := Nat.pow_le_pow_left hA'_bound 2
  have hstep3 : (A' - A').card * A'.card ≤ ((2 ^ 27 * M ^ 10) * A'.card) * A'.card := by
    calc
      (A' - A').card * A'.card ≤ 32 * K ^ 2 * M ^ 4 * (8 * M * A'.card) ^ 2 :=
        hstep2.trans (Nat.mul_le_mul_left _ hn2_le)
      _ = ((2 ^ 27 * M ^ 10) * A'.card) * A'.card := by dsimp only [K]; ring
  have hdiff : (A' - A').card ≤ (2 ^ 27 * M ^ 10) * A'.card :=
    Nat.le_of_mul_le_mul_right hstep3 hA'_nonempty.card_pos
  exact ⟨A', hA'_sub, hA'_nonempty, hA'_bound, hdiff⟩

/- ### Part 2: Pluennecke-Ruzsa corollary -/

theorem card_two_add_sub_two_add_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A' : Finset G) (C : ℕ) (hA' : A'.Nonempty) (hdiff : (A' - A').card ≤ C * A'.card) :
    ((A' + A') - (A' + A')).card ≤ C ^ 4 * A'.card := by
  have h2 : (2 : ℕ) • A' = A' + A' := by
    rw [two_nsmul]
  have hpr := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hA' A' 2 2
  rw [h2] at hpr
  have hpos : (0 : ℚ≥0) < (A'.card : ℚ≥0) := Nat.cast_pos.mpr hA'.card_pos
  have hratio : ((A' - A').card : ℚ≥0) / (A'.card : ℚ≥0) ≤ (C : ℚ≥0) := by
    rw [div_le_iff₀ hpos]
    exact_mod_cast hdiff
  have hle : (((A' + A') - (A' + A')).card : ℚ≥0) ≤ ((C ^ 4 * A'.card : ℕ) : ℚ≥0) := by
    calc
      (((A' + A') - (A' + A')).card : ℚ≥0)
          ≤ (((A' - A').card : ℚ≥0) / (A'.card : ℚ≥0)) ^ (2 + 2) * (A'.card : ℚ≥0) := hpr
      _ ≤ (C : ℚ≥0) ^ 4 * (A'.card : ℚ≥0) := by gcongr
      _ = ((C ^ 4 * A'.card : ℕ) : ℚ≥0) := by push_cast; ring
  exact_mod_cast hle

/- ### Part 3: Freiman-2-isomorphism into Z -/

private lemma base_repr_eq_zero : ∀ (r : ℕ) (B : ℤ) (_ : 0 < B) (f : Fin r → ℤ),
    (∀ i, |f i| < B) → (∑ i : Fin r, f i * B ^ (i : ℕ)) = 0 → ∀ i, f i = 0
  | 0, _, _, _, _, _, i => Fin.elim0 i
  | r + 1, B, hB, f, hbound, hsum, i => by
    rw [Fin.sum_univ_succ] at hsum
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ'] at hsum
    have htail : ∑ j : Fin r, f j.succ * (B * B ^ (j : ℕ)) =
        B * ∑ j : Fin r, f j.succ * B ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [htail] at hsum
    have hdvd : B ∣ f 0 := ⟨-(∑ j : Fin r, f j.succ * B ^ (j : ℕ)), by linarith⟩
    have hf0 : f 0 = 0 := by
      obtain ⟨k, hk⟩ := hdvd
      by_contra hne
      have hk_ne : k ≠ 0 := by intro hk0; rw [hk0, mul_zero] at hk; exact hne hk
      have hk_abs : 1 ≤ |k| := Int.one_le_abs hk_ne
      have h1 : B ≤ |f 0| := by
        rw [hk, abs_mul, abs_of_pos hB]
        nlinarith
      linarith [hbound 0]
    rw [hf0, zero_add] at hsum
    have hrest : ∑ j : Fin r, f j.succ * B ^ (j : ℕ) = 0 :=
      (mul_eq_zero.mp hsum).resolve_left (ne_of_gt hB)
    have hih := base_repr_eq_zero r B hB (fun j => f j.succ) (fun j => hbound j.succ) hrest
    refine Fin.cases hf0 hih i

theorem freiman_embed_int {E : Type*} [AddCommGroup E] [Module ℚ E] [DecidableEq E]
    (A' : Finset E) (h3ap : ThreeAPFree (A' : Set E)) :
    ∃ B' : Finset ℤ, B'.card = A'.card ∧ ThreeAPFree (B' : Set ℤ) ∧
      ((B' + B') - (B' + B')).card ≤ ((A' + A') - (A' + A')).card := by
  let V : Submodule ℚ E := Submodule.span ℚ (A' : Set E)
  have : Module.Finite ℚ V := Module.Finite.span_of_finite ℚ A'.finite_toSet
  let b := Module.finBasis ℚ V
  let r := Module.finrank ℚ V
  let v : ∀ a ∈ A', V := fun a ha => ⟨a, Submodule.subset_span ha⟩
  let D : ℕ := ∏ a ∈ A'.attach, ∏ i : Fin r, (b.repr (v a.1 a.2) i).den
  have hD_pos : 0 < D := Finset.prod_pos fun a _ => Finset.prod_pos fun i _ => Rat.den_pos _
  have hD_dvd : ∀ (a : {x // x ∈ A'}) (i : Fin r), (b.repr (v a.1 a.2) i).den ∣ D := by
    intro a i
    have h1 : (b.repr (v a.1 a.2) i).den ∣ ∏ j : Fin r, (b.repr (v a.1 a.2) j).den :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have h2 : (∏ j : Fin r, (b.repr (v a.1 a.2) j).den) ∣ D :=
      Finset.dvd_prod_of_mem _ (Finset.mem_attach A' a)
    exact dvd_trans h1 h2
  let z : {x // x ∈ A'} → Fin r → ℤ := fun a i =>
    (b.repr (v a.1 a.2) i).num * ((D / (b.repr (v a.1 a.2) i).den : ℕ) : ℤ)
  have hz_cast : ∀ (a : {x // x ∈ A'}) (i : Fin r),
      (z a i : ℚ) = (D : ℚ) * b.repr (v a.1 a.2) i := by
    intro a i
    dsimp only [z]
    set q := b.repr (v a.1 a.2) i
    have hden_pos : (0 : ℚ) < (q.den : ℚ) := Nat.cast_pos.mpr q.den_pos
    have hdiv : ((D / q.den : ℕ) : ℚ) = (D : ℚ) / (q.den : ℚ) :=
      Nat.cast_div (hD_dvd a i) (ne_of_gt hden_pos)
    rw [Int.cast_mul, Int.cast_natCast, hdiv]
    have hq : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
    calc
      (q.num : ℚ) * ((D : ℚ) / (q.den : ℚ))
          = (D : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by ring
      _ = (D : ℚ) * q := by rw [hq]
  let Mz : ℕ := A'.attach.sup (fun a => Finset.univ.sup (fun i : Fin r => (z a i).natAbs))
  let B : ℤ := 4 * (Mz : ℤ) + 1
  have hB_pos : 0 < B := by dsimp only [B]; omega
  have hz_le : ∀ a i, |z a i| ≤ (Mz : ℤ) := by
    intro a i
    have h1 : (z a i).natAbs ≤ Finset.univ.sup (fun j : Fin r => (z a j).natAbs) :=
      Finset.le_sup (f := fun j : Fin r => (z a j).natAbs) (Finset.mem_univ i)
    have h2 : Finset.univ.sup (fun j : Fin r => (z a j).natAbs) ≤ Mz :=
      Finset.le_sup (f := fun a => Finset.univ.sup (fun j : Fin r => (z a j).natAbs))
        (Finset.mem_attach A' a)
    have h3 : (z a i).natAbs ≤ Mz := h1.trans h2
    rw [← Int.natCast_natAbs]
    exact_mod_cast h3
  let Φ : {x // x ∈ A'} → ℤ := fun a => ∑ i : Fin r, z a i * B ^ (i : ℕ)
  let L : V →ₗ[ℚ] ℚ :=
    ∑ i : Fin r, ((D : ℚ) * (B : ℚ) ^ (i : ℕ)) • (Finsupp.lapply i).comp b.repr.toLinearMap
  have hL_eq : ∀ a : {x // x ∈ A'}, L (v a.1 a.2) = (Φ a : ℚ) := by
    intro a
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      Finsupp.lapply_apply, LinearEquiv.coe_coe, smul_eq_mul, Φ]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz_cast a i]
    ring
  have hFreiman : ∀ a₁ a₂ a₃ a₄ : {x // x ∈ A'},
      Φ a₁ + Φ a₂ = Φ a₃ + Φ a₄ → a₁.1 + a₂.1 = a₃.1 + a₄.1 := by
    intro a₁ a₂ a₃ a₄ h
    have hsum0 : ∑ i : Fin r, (z a₁ i + z a₂ i - z a₃ i - z a₄ i) * B ^ (i : ℕ) = 0 := by
      have : ∑ i : Fin r, (z a₁ i + z a₂ i - z a₃ i - z a₄ i) * B ^ (i : ℕ) =
          Φ a₁ + Φ a₂ - Φ a₃ - Φ a₄ := by
        simp only [Φ, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [this]; omega
    have hbd : ∀ i : Fin r, |z a₁ i + z a₂ i - z a₃ i - z a₄ i| < B := by
      intro i
      have h1 := hz_le a₁ i
      have h2 := hz_le a₂ i
      have h3 := hz_le a₃ i
      have h4 := hz_le a₄ i
      have htri : |z a₁ i + z a₂ i - z a₃ i - z a₄ i| ≤
          |z a₁ i| + |z a₂ i| + |z a₃ i| + |z a₄ i| := by
        calc
          |z a₁ i + z a₂ i - z a₃ i - z a₄ i|
              = |(z a₁ i + z a₂ i - z a₃ i) + (-z a₄ i)| := by ring_nf
          _ ≤ |z a₁ i + z a₂ i - z a₃ i| + |-z a₄ i| := abs_add_le _ _
          _ = |(z a₁ i + z a₂ i) + (-z a₃ i)| + |z a₄ i| := by rw [abs_neg]; ring_nf
          _ ≤ (|z a₁ i + z a₂ i| + |-z a₃ i|) + |z a₄ i| := by gcongr; exact abs_add_le _ _
          _ ≤ (|z a₁ i| + |z a₂ i| + |z a₃ i|) + |z a₄ i| := by
            rw [abs_neg]; gcongr; exact abs_add_le _ _
          _ = |z a₁ i| + |z a₂ i| + |z a₃ i| + |z a₄ i| := by ring
      dsimp only [B]
      linarith
    have hzero := base_repr_eq_zero r B hB_pos _ hbd hsum0
    have hrepr : b.repr (v a₁.1 a₁.2 + v a₂.1 a₂.2) = b.repr (v a₃.1 a₃.2 + v a₄.1 a₄.2) := by
      ext i
      simp only [map_add, Finsupp.add_apply]
      have hzi : (z a₁ i + z a₂ i : ℚ) = (z a₃ i + z a₄ i : ℚ) := by
        have := hzero i
        exact_mod_cast (show z a₁ i + z a₂ i = z a₃ i + z a₄ i by omega)
      rw [hz_cast, hz_cast, hz_cast, hz_cast] at hzi
      have hDne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
      exact mul_left_cancel₀ hDne (by linarith)
    have hv : v a₁.1 a₁.2 + v a₂.1 a₂.2 = v a₃.1 a₃.2 + v a₄.1 a₄.2 := b.repr.injective hrepr
    exact congrArg Subtype.val hv
  have hΦ_inj : Function.Injective Φ := by
    intro a₁ a₂ h
    have hadd := hFreiman a₁ a₁ a₂ a₂ (by omega)
    have h2 : (2 : ℚ) • a₁.1 = (2 : ℚ) • a₂.1 := by
      rw [two_smul, two_smul]
      exact hadd
    exact Subtype.ext (smul_right_injective E (two_ne_zero : (2 : ℚ) ≠ 0) h2)
  let B' : Finset ℤ := A'.attach.image Φ
  have hB'_card : B'.card = A'.card := by
    rw [Finset.card_image_of_injective _ hΦ_inj, Finset.card_attach]
  have hB'_3ap : ThreeAPFree (B' : Set ℤ) := by
    intro x hx y hy z_ hz hxyz
    simp only [mem_coe, B', mem_image, mem_attach, true_and] at hx hy hz
    obtain ⟨a₁, rfl⟩ := hx
    obtain ⟨a₂, rfl⟩ := hy
    obtain ⟨a₃, rfl⟩ := hz
    have h1 := hFreiman a₁ a₃ a₂ a₂ hxyz
    have h2 := h3ap a₁.2 a₂.2 a₃.2 h1
    have h3 : a₁ = a₂ := Subtype.ext h2
    rw [h3]
  have hS_mem_V : ∀ x ∈ (A' + A') - (A' + A'), x ∈ V := by
    intro x hx
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Finset.mem_add.mp hs₁
    obtain ⟨a₃, ha₃, a₄, ha₄, rfl⟩ := Finset.mem_add.mp hs₂
    exact V.sub_mem (V.add_mem (Submodule.subset_span ha₁) (Submodule.subset_span ha₂))
      (V.add_mem (Submodule.subset_span ha₃) (Submodule.subset_span ha₄))
  have hB'_4card : ((B' + B') - (B' + B')).card ≤ ((A' + A') - (A' + A')).card := by
    have hinj : Function.Injective (Int.cast : ℤ → ℚ) := Int.cast_injective
    rw [← Finset.card_image_of_injective ((B' + B') - (B' + B')) hinj]
    let T := ((A' + A') - (A' + A')).attach.image (fun x => L ⟨x.1, hS_mem_V x.1 x.2⟩)
    have hsub : ((B' + B') - (B' + B')).image (Int.cast : ℤ → ℚ) ⊆ T := by
      intro q hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Finset.mem_sub.mp hy
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Finset.mem_add.mp hs₁
      obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := Finset.mem_add.mp hs₂
      obtain ⟨a₁, _, rfl⟩ := Finset.mem_image.mp hb₁
      obtain ⟨a₂, _, rfl⟩ := Finset.mem_image.mp hb₂
      obtain ⟨a₃, _, rfl⟩ := Finset.mem_image.mp hb₃
      obtain ⟨a₄, _, rfl⟩ := Finset.mem_image.mp hb₄
      have hx_mem : (a₁.1 + a₂.1) - (a₃.1 + a₄.1) ∈ (A' + A') - (A' + A') :=
        Finset.sub_mem_sub (Finset.add_mem_add a₁.2 a₂.2) (Finset.add_mem_add a₃.2 a₄.2)
      refine Finset.mem_image.mpr ⟨⟨_, hx_mem⟩, Finset.mem_attach _ _, ?_⟩
      have hv_eq : (⟨(a₁.1 + a₂.1) - (a₃.1 + a₄.1), hS_mem_V _ hx_mem⟩ : V) =
          (v a₁.1 a₁.2 + v a₂.1 a₂.2) - (v a₃.1 a₃.2 + v a₄.1 a₄.2) := rfl
      rw [hv_eq, map_sub, map_add, map_add, hL_eq, hL_eq, hL_eq, hL_eq]
      push_cast
      rfl
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by rw [card_attach]))
  exact ⟨B', hB'_card, hB'_3ap, hB'_4card⟩

/- ### Part 4: Ruzsa modeling lemma into ZMod p -/

private def cen (Q : ℕ) (x : ZMod Q) : ℤ :=
  if 2 * x.val < Q then (x.val : ℤ) else (x.val : ℤ) - (Q : ℤ)

private lemma cen_cast {Q : ℕ} [NeZero Q] (x : ZMod Q) : ((cen Q x : ℤ) : ZMod Q) = x := by
  dsimp only [cen]
  split_ifs <;> simp

private lemma two_mul_abs_cen_lt {Q : ℕ} (hQ_odd : Odd Q) [NeZero Q] (x : ZMod Q) :
    2 * |cen Q x| < (Q : ℤ) := by
  have hxlt : x.val < Q := ZMod.val_lt x
  dsimp only [cen]
  split_ifs with h
  · rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast h
  · have hgt : Q < 2 * x.val := by
      have hge : Q ≤ 2 * x.val := not_lt.mp h
      obtain ⟨k, hk⟩ := hQ_odd
      omega
    have hneg : (x.val : ℤ) - (Q : ℤ) < 0 := by omega
    rw [abs_of_neg hneg]
    omega

private lemma eq_cen_of_cast_eq {Q : ℕ} (hQ_odd : Odd Q) [NeZero Q] {z : ℤ} {x : ZMod Q}
    (hcast : (z : ZMod Q) = x) (hsmall : 2 * |z| < (Q : ℤ)) :
    z = cen Q x := by
  have hc := two_mul_abs_cen_lt hQ_odd x
  have hcast0 : ((z - cen Q x : ℤ) : ZMod Q) = 0 := by
    push_cast
    rw [hcast, cen_cast, sub_self]
  have hdvd : (Q : ℤ) ∣ (z - cen Q x) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast0
  have hlt : |z - cen Q x| < (Q : ℤ) := by
    have htri : |z - cen Q x| ≤ |z| + |cen Q x| := abs_sub z (cen Q x)
    linarith
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k = 0 := by
    by_contra hne
    have h1 : 1 ≤ |k| := Int.one_le_abs hne
    have hQpos : (0 : ℤ) < (Q : ℤ) := by
      obtain ⟨t, ht⟩ := hQ_odd
      omega
    have h2 : (Q : ℤ) ≤ |z - cen Q x| := by
      rw [hk, abs_mul, abs_of_pos hQpos]
      nlinarith
    linarith
  rw [hk0, mul_zero] at hk
  omega

theorem ruzsa_modeling (B' : Finset ℤ) (C₂ : ℕ)
    (hB' : B'.Nonempty) (h3ap : ThreeAPFree (B' : Set ℤ))
    (h4 : ((B' + B') - (B' + B')).card ≤ C₂ * B'.card) :
    ∃ p : ℕ, Nat.Prime p ∧ B'.card < p ∧ p ≤ (4 * C₂ + 6) * B'.card ∧
      ∃ C : Finset (ZMod p), B'.card ≤ 5 * C.card ∧ ThreeAPFree (C : Set (ZMod p)) := by
  let Dset : Finset ℤ := ((B' + B') - (B' + B')).erase 0
  have hD_card : Dset.card ≤ C₂ * B'.card := (Finset.card_erase_le).trans h4
  have h0_not_mem : (0 : ℤ) ∉ Dset := Finset.notMem_erase 0 _
  let m : ℕ := 2 * Dset.card + B'.card + 2
  obtain ⟨p, hp_prime, hm_lt_p, hp_le_2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have hD_lt_p : Dset.card < p := by omega
  have hB'_lt_p : B'.card < p := by omega
  have hp_ub : p ≤ (4 * C₂ + 6) * B'.card := by
    have h1 : 1 ≤ B'.card := hB'.card_pos
    dsimp only [m] at hp_le_2m
    nlinarith
  have hp_pos : 0 < p := hp_prime.pos
  let Dmax : ℕ := Dset.sup Int.natAbs
  obtain ⟨Q, hQ_ge, hQ_prime⟩ := Nat.exists_infinite_primes (max (4 * Dmax + 25) (2 * p + 25))
  have hQ_gt_Dmax : Dmax < Q := by omega
  have hQ_gt_2p : 2 * p < Q := by omega
  have hQ_gt_2 : 2 < Q := by omega
  have hQ_odd : Odd Q := hQ_prime.odd_of_ne_two (by omega)
  have : Fact (Nat.Prime Q) := ⟨hQ_prime⟩
  have : NeZero Q := ⟨hQ_prime.ne_zero⟩
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have hd_ne_zero : ∀ d ∈ Dset, (d : ZMod Q) ≠ 0 := by
    intro d hd h0
    have hdvd : (Q : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd d Q).mp h0
    have hdvd_nat : Q ∣ d.natAbs := Int.natCast_dvd.mp hdvd
    have hd_ne : d ≠ 0 := fun h => h0_not_mem (h ▸ hd)
    have hnat_pos : 0 < d.natAbs := Int.natAbs_pos.mpr hd_ne
    have hQ_le : Q ≤ d.natAbs := Nat.le_of_dvd hnat_pos hdvd_nat
    have hle_max : d.natAbs ≤ Dmax := Finset.le_sup (f := Int.natAbs) hd
    omega
  let U : Finset (ZMod Q) := (Finset.univ : Finset (ZMod Q)).erase 0
  have hU_card : U.card = Q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card Q]
  let BadZ : Finset (ZMod Q) := U.filter (fun x => (p : ℤ) ∣ cen Q x)
  have hBadZ_card : p * BadZ.card ≤ Q - 1 := by
    let L : ℕ := (Q - 1) / (2 * p)
    let Kset : Finset ℤ := (Finset.Icc (-(L : ℤ)) (L : ℤ)).erase 0
    have hsub : BadZ ⊆ Kset.image (fun k => ((p * k : ℤ) : ZMod Q)) := by
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hxU, k, hk⟩ := hx
      have hx_ne : x ≠ 0 := (mem_erase.mp hxU).1
      have hk_ne : k ≠ 0 := by
        intro hk0
        rw [hk0, mul_zero] at hk
        have hxc := cen_cast x
        rw [hk, Int.cast_zero] at hxc
        exact hx_ne hxc.symm
      have hsmall := two_mul_abs_cen_lt hQ_odd x
      rw [hk, abs_mul, abs_of_pos (Nat.cast_pos.mpr hp_pos : (0 : ℤ) < (p : ℤ))] at hsmall
      have hnat : 2 * p * k.natAbs < Q := by
        have hint : ((2 * p * k.natAbs : ℕ) : ℤ) < (Q : ℤ) := by
          push_cast
          linarith
        exact_mod_cast hint
      have hnat_le : k.natAbs ≤ L := by
        refine (Nat.le_div_iff_mul_le (by omega : 0 < 2 * p)).mpr ?_
        rw [mul_comm]
        omega
      have hk_mem : k ∈ Kset := by
        rw [mem_erase, mem_Icc]
        have hka : (k.natAbs : ℤ) = |k| := Int.natCast_natAbs k
        have hle : |k| ≤ (L : ℤ) := by omega
        exact ⟨hk_ne, neg_le_of_abs_le hle, le_of_abs_le hle⟩
      refine mem_image.mpr ⟨k, hk_mem, ?_⟩
      rw [← hk, cen_cast]
    have hKcard : Kset.card = 2 * L := by
      have h0mem : (0 : ℤ) ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) := by
        rw [mem_Icc]
        exact ⟨neg_nonpos.mpr (Nat.cast_nonneg L), Nat.cast_nonneg L⟩
      rw [Finset.card_erase_of_mem h0mem, Int.card_Icc]
      have hdiff : (L : ℤ) + 1 - -(L : ℤ) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hdiff, Int.toNat_natCast]
      omega
    have hle : BadZ.card ≤ 2 * L := (card_le_card hsub).trans (card_image_le.trans hKcard.le)
    calc
      p * BadZ.card ≤ p * (2 * L) := Nat.mul_le_mul_left p hle
      _ = (2 * p) * ((Q - 1) / (2 * p)) := by ring
      _ ≤ Q - 1 := Nat.mul_div_le (Q - 1) (2 * p)
  let BadLam : Finset (ZMod Q) :=
    U.filter (fun l => ∃ d ∈ Dset, (p : ℤ) ∣ cen Q (l * (d : ZMod Q)))
  have hBadLam_card : BadLam.card < U.card := by
    have hsub : BadLam ⊆ Dset.biUnion (fun d => U.filter (fun l => (p : ℤ) ∣ cen Q (l * (d : ZMod Q)))) := by
      intro l hl
      obtain ⟨hlU, d, hd, hdvd⟩ := mem_filter.mp hl
      exact mem_biUnion.mpr ⟨d, hd, mem_filter.mpr ⟨hlU, hdvd⟩⟩
    have hfib : ∀ d ∈ Dset,
        (U.filter (fun l => (p : ℤ) ∣ cen Q (l * (d : ZMod Q)))).card ≤ BadZ.card := by
      intro d hd
      have hne : (d : ZMod Q) ≠ 0 := hd_ne_zero d hd
      refine Finset.card_le_card_of_injOn (fun l => l * (d : ZMod Q)) ?_ ?_
      · intro l hl
        simp only [mem_coe, BadZ, mem_filter, U, mem_erase, mem_univ, and_true] at hl ⊢
        exact ⟨mul_ne_zero hl.1 hne, hl.2⟩
      · intro l₁ _ l₂ _ h
        exact mul_right_cancel₀ hne h
    have hle1 : BadLam.card ≤ Dset.card * BadZ.card := calc
      BadLam.card ≤ (Dset.biUnion (fun d => U.filter (fun l => (p : ℤ) ∣ cen Q (l * (d : ZMod Q))))).card :=
        card_le_card hsub
      _ ≤ ∑ d ∈ Dset, (U.filter (fun l => (p : ℤ) ∣ cen Q (l * (d : ZMod Q)))).card :=
        card_biUnion_le
      _ ≤ ∑ _d ∈ Dset, BadZ.card := sum_le_sum hfib
      _ = Dset.card * BadZ.card := by rw [sum_const, smul_eq_mul]
    have hle2 : p * BadLam.card < p * (Q - 1) := calc
      p * BadLam.card ≤ p * (Dset.card * BadZ.card) := Nat.mul_le_mul_left p hle1
      _ = Dset.card * (p * BadZ.card) := by ring
      _ ≤ Dset.card * (Q - 1) := Nat.mul_le_mul_left _ hBadZ_card
      _ < p * (Q - 1) := Nat.mul_lt_mul_of_pos_right hD_lt_p (by omega)
    rw [hU_card]
    exact Nat.lt_of_mul_lt_mul_left hle2
  have hex_good : ∃ l ∈ U, l ∉ BadLam := by
    have hsub : BadLam ⊆ U := filter_subset _ _
    have hpos : 0 < (U \ BadLam).card := by
      rw [Finset.card_sdiff_of_subset hsub]
      omega
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
    exact ⟨l, (mem_sdiff.mp hl).1, (mem_sdiff.mp hl).2⟩
  obtain ⟨l, hlU, hlGood⟩ := hex_good
  have hl_good : ∀ d ∈ Dset, ¬ ((p : ℤ) ∣ cen Q (l * (d : ZMod Q))) := by
    intro d hd hdvd
    exact hlGood (mem_filter.mpr ⟨hlU, d, hd, hdvd⟩)
  let v : ℤ → ℕ := fun b => (l * (b : ZMod Q)).val
  have hv_lt : ∀ b, v b < Q := fun b => ZMod.val_lt _
  let bucket : ℤ → Fin 5 := fun b =>
    ⟨(5 * v b) / Q, (Nat.div_lt_iff_lt_mul (by omega : 0 < Q)).mpr (by have := hv_lt b; omega)⟩
  have hex_bucket : ∃ j : Fin 5, B'.card ≤ 5 * (B'.filter (fun b => bucket b = j)).card := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 5)))
      Finset.univ_nonempty (fun j _ => h j)
    rw [← mul_sum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hpart : ∑ j : Fin 5, (B'.filter (fun b => bucket b = j)).card = B'.card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp
    rw [hpart] at hsum
    omega
  obtain ⟨j₀, hj₀⟩ := hex_bucket
  let B'' : Finset ℤ := B'.filter (fun b => bucket b = j₀)
  have hB''_sub : B'' ⊆ B' := filter_subset _ _
  have hdiff_small : ∀ b₁ ∈ B'', ∀ b₂ ∈ B'', 5 * |(v b₁ : ℤ) - (v b₂ : ℤ)| < (Q : ℤ) := by
    intro b₁ hb₁ b₂ hb₂
    have h1 : (5 * v b₁) / Q = j₀.val := congrArg Fin.val (mem_filter.mp hb₁).2
    have h2 : (5 * v b₂) / Q = j₀.val := congrArg Fin.val (mem_filter.mp hb₂).2
    have hQpos : 0 < Q := by omega
    have hlo1 : j₀.val * Q ≤ 5 * v b₁ := by
      have := Nat.div_mul_le_self (5 * v b₁) Q
      rw [h1] at this; exact this
    have hhi1 : 5 * v b₁ < (j₀.val + 1) * Q := by
      have := Nat.lt_mul_div_succ (5 * v b₁) hQpos
      rw [h1] at this; linarith
    have hlo2 : j₀.val * Q ≤ 5 * v b₂ := by
      have := Nat.div_mul_le_self (5 * v b₂) Q
      rw [h2] at this; exact this
    have hhi2 : 5 * v b₂ < (j₀.val + 1) * Q := by
      have := Nat.lt_mul_div_succ (5 * v b₂) hQpos
      rw [h2] at this; linarith
    have hlo1' : (j₀.val : ℤ) * (Q : ℤ) ≤ 5 * (v b₁ : ℤ) := by exact_mod_cast hlo1
    have hhi1' : 5 * (v b₁ : ℤ) < ((j₀.val : ℤ) + 1) * (Q : ℤ) := by exact_mod_cast hhi1
    have hlo2' : (j₀.val : ℤ) * (Q : ℤ) ≤ 5 * (v b₂ : ℤ) := by exact_mod_cast hlo2
    have hhi2' : 5 * (v b₂ : ℤ) < ((j₀.val : ℤ) + 1) * (Q : ℤ) := by exact_mod_cast hhi2
    have h5 : |5 * ((v b₁ : ℤ) - (v b₂ : ℤ))| < (Q : ℤ) := by
      rw [abs_lt]
      constructor <;> linarith
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 5)] at h5
    exact h5
  let ψ : ℤ → ZMod p := fun b => (v b : ZMod p)
  have hψ_inj : Set.InjOn ψ (B'' : Set ℤ) := by
    intro b₁ hb₁ b₂ hb₂ hψ
    by_contra hne
    have hb₁' : b₁ ∈ B' := hB''_sub hb₁
    have hb₂' : b₂ ∈ B' := hB''_sub hb₂
    have hd_mem : b₁ - b₂ ∈ Dset := by
      rw [mem_erase]
      refine ⟨sub_ne_zero.mpr hne, ?_⟩
      have h1 : b₁ + b₁ ∈ B' + B' := add_mem_add hb₁' hb₁'
      have h2 : b₂ + b₁ ∈ B' + B' := add_mem_add hb₂' hb₁'
      have heq : (b₁ + b₁) - (b₂ + b₁) = b₁ - b₂ := by ring
      rw [← heq]
      exact sub_mem_sub h1 h2
    have hcast_p : (((v b₁ : ℤ) - (v b₂ : ℤ) : ℤ) : ZMod p) = 0 := by
      push_cast
      exact sub_eq_zero.mpr hψ
    have hdvd_p : (p : ℤ) ∣ ((v b₁ : ℤ) - (v b₂ : ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast_p
    have hcast_Q : (((v b₁ : ℤ) - (v b₂ : ℤ) : ℤ) : ZMod Q) = l * ((b₁ - b₂ : ℤ) : ZMod Q) := by
      push_cast
      simp only [v, ZMod.natCast_zmod_val]
      ring
    have hsm : 2 * |(v b₁ : ℤ) - (v b₂ : ℤ)| < (Q : ℤ) := by
      have := hdiff_small b₁ hb₁ b₂ hb₂
      omega
    have hcen := eq_cen_of_cast_eq hQ_odd hcast_Q hsm
    rw [hcen] at hdvd_p
    exact hl_good (b₁ - b₂) hd_mem hdvd_p
  let C : Finset (ZMod p) := B''.image ψ
  have hC_card : C.card = B''.card := Finset.card_image_of_injOn hψ_inj
  have hC_3ap : ThreeAPFree (C : Set (ZMod p)) := by
    intro x hx y hy z_ hz hxyz
    simp only [mem_coe, C, mem_image] at hx hy hz
    obtain ⟨b₁, hb₁, rfl⟩ := hx
    obtain ⟨b₂, hb₂, rfl⟩ := hy
    obtain ⟨b₃, hb₃, rfl⟩ := hz
    have hcast_p : (((v b₁ : ℤ) + (v b₃ : ℤ) - 2 * (v b₂ : ℤ) : ℤ) : ZMod p) = 0 := by
      push_cast
      dsimp only [ψ] at hxyz
      linear_combination hxyz
    have hdvd_p : (p : ℤ) ∣ ((v b₁ : ℤ) + (v b₃ : ℤ) - 2 * (v b₂ : ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast_p
    let d : ℤ := (b₁ + b₃) - (b₂ + b₂)
    have hcast_Q : (((v b₁ : ℤ) + (v b₃ : ℤ) - 2 * (v b₂ : ℤ) : ℤ) : ZMod Q) =
        l * (d : ZMod Q) := by
      dsimp only [d]
      push_cast
      simp only [v, ZMod.natCast_zmod_val]
      ring
    have hsm : 2 * |(v b₁ : ℤ) + (v b₃ : ℤ) - 2 * (v b₂ : ℤ)| < (Q : ℤ) := by
      have h1 := hdiff_small b₁ hb₁ b₂ hb₂
      have h2 := hdiff_small b₃ hb₃ b₂ hb₂
      have htri : |(v b₁ : ℤ) + (v b₃ : ℤ) - 2 * (v b₂ : ℤ)| ≤
          |(v b₁ : ℤ) - (v b₂ : ℤ)| + |(v b₃ : ℤ) - (v b₂ : ℤ)| := by
        calc
          |(v b₁ : ℤ) + (v b₃ : ℤ) - 2 * (v b₂ : ℤ)|
              = |((v b₁ : ℤ) - (v b₂ : ℤ)) + ((v b₃ : ℤ) - (v b₂ : ℤ))| := by ring_nf
          _ ≤ |(v b₁ : ℤ) - (v b₂ : ℤ)| + |(v b₃ : ℤ) - (v b₂ : ℤ)| := abs_add_le _ _
      omega
    have hcen := eq_cen_of_cast_eq hQ_odd hcast_Q hsm
    rw [hcen] at hdvd_p
    have hd_not : d ∉ Dset := fun hd => hl_good d hd hdvd_p
    have hd_in : d ∈ (B' + B') - (B' + B') :=
      sub_mem_sub (add_mem_add (hB''_sub hb₁) (hB''_sub hb₃))
        (add_mem_add (hB''_sub hb₂) (hB''_sub hb₂))
    have hd0 : d = 0 := by
      by_contra hne
      exact hd_not (mem_erase.mpr ⟨hne, hd_in⟩)
    have h3 : b₁ + b₃ = b₂ + b₂ := by dsimp only [d] at hd0; omega
    have heq : b₁ = b₂ := h3ap (hB''_sub hb₁) (hB''_sub hb₂) (hB''_sub hb₃) h3
    rw [heq]
  exact ⟨p, hp_prime, hB'_lt_p, hp_ub, C, by rw [hC_card]; exact hj₀, hC_3ap⟩

/- ### Part 5: Energy bound for 3AP-free sets in any Q-vector space -/

theorem energy_subcubic_of_threeAPFree {E : Type*} [AddCommGroup E] [Module ℚ E] [DecidableEq E]
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ N : ℕ, ∀ A : Finset E, N ≤ A.card → ThreeAPFree (A : Set E) →
      M * Finset.addEnergy A A ≤ A.card ^ 3 := by
  let C₁ : ℕ := 2 ^ 27 * M ^ 10
  let C₂ : ℕ := C₁ ^ 4
  let ε : ℝ := 1 / ((5 * (4 * C₂ + 6) : ℕ) : ℝ)
  have hε : 0 < ε := by positivity
  refine ⟨max 1 (8 * M * cornersTheoremBound ε), fun A hN h3ap => ?_⟩
  by_contra hgt
  push Not at hgt
  have hA : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hN))
  obtain ⟨A', hA'_sub, hA'_ne, hA'_card, hA'_diff⟩ :=
    balog_szemeredi_gowers A M hM hA hgt.le
  have hA'_4 := card_two_add_sub_two_add_le A' C₁ hA'_ne hA'_diff
  have hA'_3ap : ThreeAPFree (A' : Set E) := h3ap.mono (Finset.coe_subset.mpr hA'_sub)
  obtain ⟨B', hB'_card, hB'_3ap, hB'_4⟩ := freiman_embed_int A' hA'_3ap
  have hB'_ne : B'.Nonempty := Finset.card_pos.mp (hB'_card ▸ hA'_ne.card_pos)
  have hB'_4' : ((B' + B') - (B' + B')).card ≤ C₂ * B'.card := by
    rw [hB'_card]
    exact hB'_4.trans hA'_4
  obtain ⟨p, hp_prime, hB'_lt_p, hp_ub, C, hC_card, hC_3ap⟩ :=
    ruzsa_modeling B' C₂ hB'_ne hB'_3ap hB'_4'
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have hp_ge : cornersTheoremBound ε ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card p]
    have h1 : 8 * M * cornersTheoremBound ε ≤ A.card := (le_max_right _ _).trans hN
    have h2 : A.card ≤ 8 * M * B'.card := hB'_card ▸ hA'_card
    have h3 : 8 * M * cornersTheoremBound ε ≤ 8 * M * p := h1.trans (h2.trans (Nat.mul_le_mul_left _ hB'_lt_p.le))
    exact Nat.le_of_mul_le_mul_left h3 (by omega)
  have hC_dens : ε * (Fintype.card (ZMod p) : ℝ) ≤ (C.card : ℝ) := by
    rw [ZMod.card p]
    dsimp only [ε]
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    have hnat : p ≤ C.card * (5 * (4 * C₂ + 6)) := by nlinarith [hp_ub, hC_card]
    exact_mod_cast hnat
  exact roth_3ap_theorem ε hε hp_ge C hC_dens hC_3ap

end Erdos657H1Aux

/- ### Part 6: Solution to H1 -/

theorem OMA.solution : OMA.R_Erdos657_erdos_657_variants_higher_dim_R1.H1 := by
  intro k _ t
  by_cases ht : t = 0
  · subst ht
    exact ⟨0, fun A _ _ => by simp⟩
  · have hM : 1 ≤ 2 * t := by omega
    obtain ⟨N, hN⟩ :=
      Erdos657H1Aux.energy_subcubic_of_threeAPFree (E := ℝ^k) (2 * t) hM
    refine ⟨N, fun A hcard hfree => ?_⟩
    have h3ap : ThreeAPFree (A : Set (ℝ^k)) := by
      intro a ha b hb c hc habc
      by_contra hab
      have hbc : b ≠ c := by
        intro h
        subst h
        exact hab (add_right_cancel habc)
      have hac : a ≠ c := by
        intro h
        subst h
        have h2 : (2 : ℝ) • a = (2 : ℝ) • b := by
          rw [two_smul, two_smul]
          exact habc
        exact hab (smul_right_injective (ℝ^k) (two_ne_zero : (2 : ℝ) ≠ 0) h2)
      have hdist : dist a b = dist b c := by
        rw [dist_eq_norm, dist_eq_norm]
        have hsub : a - b = b - c := by
          have : a + c - b - c = b + b - b - c := by rw [habc]
          abel_nf at this ⊢
          exact this
        rw [hsub]
      exact hfree ha hb hc hab hbc hac (Or.inl hdist)
    have hE := hN A hcard h3ap
    dsimp only
    refine le_trans (Nat.mul_le_mul_left t ?_) (by linarith : t * (2 * Finset.addEnergy A A) ≤ A.card ^ 3)
    have hdisj : (distanceSet A : Set ℝ).PairwiseDisjoint
        (fun d => (((A.offDiag.filter fun e => dist e.1 e.2 = d) ×ˢ
          (A.offDiag.filter fun e => dist e.1 e.2 = d)).filter fun p =>
          p.1.1 - p.1.2 = p.2.1 - p.2.2 ∨ p.1.1 - p.1.2 = p.2.2 - p.2.1)) := by
      intro d₁ _ d₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      have hd₁ : dist p.1.1 p.1.2 = d₁ := (mem_filter.mp (mem_product.mp (mem_filter.mp hp₁).1).1).2
      have hd₂ : dist p.1.1 p.1.2 = d₂ := (mem_filter.mp (mem_product.mp (mem_filter.mp hp₂).1).1).2
      exact hne (hd₁.symm.trans hd₂)
    rw [← Finset.card_biUnion hdisj]
    let T₁ := ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun p => p.1.1 - p.1.2 = p.2.1 - p.2.2
    let T₂ := ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun p => p.1.1 - p.1.2 = p.2.2 - p.2.1
    have hsub : (distanceSet A).biUnion
        (fun d => (((A.offDiag.filter fun e => dist e.1 e.2 = d) ×ˢ
          (A.offDiag.filter fun e => dist e.1 e.2 = d)).filter fun p =>
          p.1.1 - p.1.2 = p.2.1 - p.2.2 ∨ p.1.1 - p.1.2 = p.2.2 - p.2.1)) ⊆ T₁ ∪ T₂ := by
      intro p hp
      obtain ⟨d, _, hpd⟩ := mem_biUnion.mp hp
      obtain ⟨hprod, hor⟩ := mem_filter.mp hpd
      obtain ⟨hp1, hp2⟩ := mem_product.mp hprod
      have hp1o := mem_offDiag.mp (mem_filter.mp hp1).1
      have hp2o := mem_offDiag.mp (mem_filter.mp hp2).1
      have hpA : p ∈ (A ×ˢ A) ×ˢ (A ×ˢ A) :=
        mem_product.mpr ⟨mem_product.mpr ⟨hp1o.1, hp1o.2.1⟩, mem_product.mpr ⟨hp2o.1, hp2o.2.1⟩⟩
      rcases hor with h1 | h2
      · exact mem_union_left _ (mem_filter.mpr ⟨hpA, h1⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hpA, h2⟩)
    have hT₁ : T₁.card ≤ Finset.addEnergy A A := by
      unfold Finset.addEnergy
      refine Finset.card_le_card_of_injOn
        (fun p => ((p.1.1, p.2.1), (p.2.2, p.1.2))) ?_ ?_
      · intro p hp
        simp only [mem_coe, T₁, mem_filter, mem_product] at hp ⊢
        refine ⟨⟨⟨hp.1.1.1, hp.1.2.1⟩, ⟨hp.1.2.2, hp.1.1.2⟩⟩, ?_⟩
        have := hp.2
        have h : p.1.1 - p.1.2 + p.1.2 + p.2.2 = p.2.1 - p.2.2 + p.1.2 + p.2.2 := by rw [this]
        abel_nf at h ⊢
        exact h
      · intro p₁ _ p₂ _ h
        simp only [Prod.mk.injEq] at h
        ext <;> simp [h]
    have hT₂ : T₂.card ≤ Finset.addEnergy A A := by
      unfold Finset.addEnergy
      refine Finset.card_le_card_of_injOn
        (fun p => ((p.1.1, p.2.2), (p.2.1, p.1.2))) ?_ ?_
      · intro p hp
        simp only [mem_coe, T₂, mem_filter, mem_product] at hp ⊢
        refine ⟨⟨⟨hp.1.1.1, hp.1.2.2⟩, ⟨hp.1.2.1, hp.1.1.2⟩⟩, ?_⟩
        have := hp.2
        have h : p.1.1 - p.1.2 + p.1.2 + p.2.1 = p.2.2 - p.2.1 + p.1.2 + p.2.1 := by rw [this]
        abel_nf at h ⊢
        exact h
      · intro p₁ _ p₂ _ h
        simp only [Prod.mk.injEq] at h
        ext <;> simp [h]
    have h1 := (card_le_card hsub).trans (card_union_le T₁ T₂)
    omega
