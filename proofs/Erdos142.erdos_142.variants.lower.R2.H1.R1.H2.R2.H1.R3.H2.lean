import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Take m maximal with 2^m r_3(N) <= N and n the first j with 2^m r_3(j) <= j; since r_3 is
-- monotone with increments at most one, the crossing is exact. Block subadditivity
-- r_k(N) <= (N/n + 1) r_k(n) gives n r_k(N) <= 2N r_k(n).

namespace OMA.SolFC

theorem fc_image_ap (c : ℕ) {t : Set ℕ} {l : ℕ∞} (h : t.IsAPOfLength l) :
    ((· + c) '' t).IsAPOfLength l := by
  obtain ⟨a, d, hc, he⟩ := h
  refine ⟨a + c, d, ?_, ?_⟩
  · have : ENat.card ((· + c) '' t) = ENat.card t :=
      (add_left_injective c).encard_image t
    rw [this, hc]
  · rw [he]
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨n, hn, by ring⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨a + n • d, ⟨n, hn, rfl⟩, by ring⟩

theorem fc_free_of_image (c : ℕ) {S T : Set ℕ} {l : ℕ∞} (hS : S.IsAPOfLengthFree l)
    (hT : (· + c) '' T ⊆ S) : T.IsAPOfLengthFree l := by
  intro t ht hap
  exact hS _ ((Set.image_mono ht).trans hT) (fc_image_ap c hap)

theorem fc_bdd (k N : ℕ) : BddAbove {x | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = x} := by
  refine ⟨N, ?_⟩
  rintro _ ⟨S, hS, -, rfl⟩
  simpa using Finset.card_le_card hS

theorem fc_block (k N j : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ).IsAPOfLengthFree k) :
    (S.filter (fun x => j * N < x ∧ x ≤ j * N + N)).card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  set Sj := S.filter (fun x => j * N < x ∧ x ≤ j * N + N) with hSj
  have hinj : Set.InjOn (fun x => x - j * N) (Sj : Set ℕ) := by
    intro x hx y hy hxy
    simp only [hSj, Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    omega
  rw [← Finset.card_image_of_injOn hinj]
  apply le_csSup (fc_bdd k N)
  refine ⟨Sj.image (fun x => x - j * N), ?_, ?_, rfl⟩
  · intro y hy
    simp only [Finset.mem_image, hSj, Finset.mem_filter] at hy
    obtain ⟨x, ⟨-, h1, h2⟩, rfl⟩ := hy
    simp only [Finset.mem_Icc]
    omega
  · apply fc_free_of_image (j * N) hS
    rintro _ ⟨y, hy, rfl⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, hSj, Finset.mem_filter] at hy
    obtain ⟨x, ⟨hx, h1, h2⟩, rfl⟩ := hy
    have : x - j * N + j * N = x := by omega
    simp only [Finset.mem_coe, this]
    exact hx



theorem fc_mem (k N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ Set.IsAPOfLengthFree.maxCard k N :=
  le_csSup (fc_bdd k N) ⟨S, hS, hf, rfl⟩

theorem fc_le (k N : ℕ) : Set.IsAPOfLengthFree.maxCard k N ≤ N := by
  apply csSup_le'
  rintro _ ⟨S, hS, -, rfl⟩
  simpa using Finset.card_le_card hS

theorem fc_mono (k N : ℕ) : Set.IsAPOfLengthFree.maxCard k N ≤ Set.IsAPOfLengthFree.maxCard k (N + 1) := by
  apply csSup_le'
  rintro _ ⟨S, hS, hf, rfl⟩
  apply fc_mem k (N + 1) S _ hf
  intro x hx
  have := hS hx
  simp only [Finset.mem_Icc] at this ⊢
  omega

theorem fc_succ (k N : ℕ) : Set.IsAPOfLengthFree.maxCard k (N + 1) ≤ Set.IsAPOfLengthFree.maxCard k N + 1 := by
  apply csSup_le'
  rintro _ ⟨S, hS, hf, rfl⟩
  have h1 : (S.erase (N + 1)).card ≤ Set.IsAPOfLengthFree.maxCard k N := by
    apply fc_mem
    · intro x hx
      have hx' := Finset.mem_erase.1 hx
      have := hS hx'.2
      simp only [Finset.mem_Icc] at this ⊢
      omega
    · intro t ht hap
      exact hf t (ht.trans (by simp)) hap
  have h2 := Finset.pred_card_le_card_erase (s := S) (a := N + 1)
  omega

theorem fc_one : 1 ≤ Set.IsAPOfLengthFree.maxCard 3 1 := by
  have := fc_mem 3 1 {1} (by simp) (by
    intro t ht hap
    exfalso
    have hc : t.encard = 3 := hap.card
    have : t.encard ≤ ({1} : Set ℕ).encard := Set.encard_le_encard (by simpa using ht)
    rw [hc, Set.encard_singleton] at this
    exact absurd this (by decide))
  simpa using this

theorem fc_pos (N : ℕ) (hN : 0 < N) : 1 ≤ Set.IsAPOfLengthFree.maxCard 3 N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact fc_one
    · exact (ih h).trans (fc_mono 3 N)

theorem fc_blocks (k n : ℕ) (S : Finset ℕ) (hf : (S : Set ℕ).IsAPOfLengthFree k)
    (hp : ∀ x ∈ S, 0 < x) :
    ∀ q : ℕ, (S.filter (fun x => x ≤ q * n)).card ≤ q * Set.IsAPOfLengthFree.maxCard k n := by
  intro q
  induction q with
  | zero =>
    rw [Finset.filter_false_of_mem (fun x hx => by have := hp x hx; simp only [zero_mul]; omega)]
    simp
  | succ q ih =>
    have hsub : S.filter (fun x => x ≤ (q + 1) * n) ⊆ S.filter (fun x => x ≤ q * n) ∪
        S.filter (fun x => q * n < x ∧ x ≤ q * n + n) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_union] at hx ⊢
      rw [add_mul, one_mul] at hx
      obtain ⟨h1, h2⟩ := hx
      by_cases h3 : x ≤ q * n
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr ⟨h1, by omega, h2⟩
    have hb := fc_block k n q S hf
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ q * Set.IsAPOfLengthFree.maxCard k n + Set.IsAPOfLengthFree.maxCard k n := Nat.add_le_add ih hb
      _ = (q + 1) * Set.IsAPOfLengthFree.maxCard k n := by ring

theorem fc_sub (k n N : ℕ) (hn : 0 < n) : Set.IsAPOfLengthFree.maxCard k N ≤ (N / n + 1) * Set.IsAPOfLengthFree.maxCard k n := by
  apply csSup_le'
  rintro _ ⟨S, hS, hf, rfl⟩
  have hp : ∀ x ∈ S, 0 < x := fun x hx => by
    have := hS hx; simp only [Finset.mem_Icc] at this; omega
  have h := fc_blocks k n S hf hp (N / n + 1)
  have hle : N ≤ (N / n + 1) * n := by
    have := Nat.lt_div_mul_add (a := N) hn
    rw [add_mul, one_mul]; omega
  rwa [Finset.filter_true_of_mem (fun x hx => by
    have := hS hx; simp only [Finset.mem_Icc] at this; omega)] at h

theorem fc_sub2 (k n N : ℕ) (hn : 0 < n) (hnN : n ≤ N) : n * Set.IsAPOfLengthFree.maxCard k N ≤ 2 * N * Set.IsAPOfLengthFree.maxCard k n := by
  have h := fc_sub k n N hn
  have h2 : n * (N / n) ≤ N := Nat.mul_div_le N n
  calc n * Set.IsAPOfLengthFree.maxCard k N ≤ n * ((N / n + 1) * Set.IsAPOfLengthFree.maxCard k n) := Nat.mul_le_mul_left _ h
    _ = (n * (N / n) + n) * Set.IsAPOfLengthFree.maxCard k n := by ring
    _ ≤ 2 * N * Set.IsAPOfLengthFree.maxCard k n := Nat.mul_le_mul_right _ (by omega)

end OMA.SolFC

open OMA.SolFC in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3.H2

  classical
  intro k N hN
  have hpos := fc_pos N hN
  have hex : ∃ m, N < 2 ^ (m + 1) * Set.IsAPOfLengthFree.maxCard 3 N := by
    refine ⟨N, ?_⟩
    have : N < 2 ^ (N + 1) := Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
    calc N < 2 ^ (N + 1) := this
      _ = 2 ^ (N + 1) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpos
  set m := Nat.find hex with hm
  have hm1 : N < 2 ^ (m + 1) * Set.IsAPOfLengthFree.maxCard 3 N := Nat.find_spec hex
  have hm2 : 2 ^ m * Set.IsAPOfLengthFree.maxCard 3 N ≤ N := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero, one_mul]; exact fc_le 3 N
    · have := Nat.find_min hex (show m - 1 < m by omega)
      rw [show m - 1 + 1 = m by omega] at this
      omega
  have hex2 : ∃ j, 0 < j ∧ 2 ^ m * Set.IsAPOfLengthFree.maxCard 3 j ≤ j := ⟨N, hN, hm2⟩
  set n := Nat.find hex2 with hn
  have hn1 : 0 < n ∧ 2 ^ m * Set.IsAPOfLengthFree.maxCard 3 n ≤ n := Nat.find_spec hex2
  have hnN : n ≤ N := Nat.find_min' hex2 ⟨hN, hm2⟩
  have hmin : ∀ j, 0 < j → j < n → j < 2 ^ m * Set.IsAPOfLengthFree.maxCard 3 j := by
    intro j hj hjn
    have := Nat.find_min hex2 hjn
    simp only [not_and, not_le] at this
    exact this hj
  refine ⟨m, n, hn1.1, hnN, ?_, hmin, hm1, fc_sub2 k n N hn1.1 hnN⟩
  show 2 ^ m * Set.IsAPOfLengthFree.maxCard 3 n = n
  have hP : 0 < 2 ^ m := by positivity
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    have := fc_one
    rw [h1] at hn1 ⊢
    have : 2 ^ m * 1 ≤ 2 ^ m * Set.IsAPOfLengthFree.maxCard 3 1 := Nat.mul_le_mul_left _ this
    omega
  · have hprev := hmin (n - 1) (by omega) (by omega)
    have hmo := fc_mono 3 (n - 1)
    have hsu := fc_succ 3 (n - 1)
    rw [show n - 1 + 1 = n by omega] at hmo hsu
    rcases Nat.lt_or_ge (Set.IsAPOfLengthFree.maxCard 3 (n - 1)) (Set.IsAPOfLengthFree.maxCard 3 n) with h2 | h2
    · have he : Set.IsAPOfLengthFree.maxCard 3 n = Set.IsAPOfLengthFree.maxCard 3 (n - 1) + 1 := by omega
      rw [he, mul_add, mul_one] at hn1
      omega
    · have he : Set.IsAPOfLengthFree.maxCard 3 n = Set.IsAPOfLengthFree.maxCard 3 (n - 1) := by omega
      rw [← he] at hprev
      omega

