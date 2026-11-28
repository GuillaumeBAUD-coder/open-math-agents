import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Split an AP-free S in [1, 4N] into the four blocks (jN, (j+1)N]; shifting a block down by jN
-- keeps it AP-free (a progression shifts back up into S) and lands in [1, N].

namespace OMA.SolSA

theorem sa_image_ap (c : ℕ) {t : Set ℕ} {l : ℕ∞} (h : t.IsAPOfLength l) :
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

theorem sa_free_of_image (c : ℕ) {S T : Set ℕ} {l : ℕ∞} (hS : S.IsAPOfLengthFree l)
    (hT : (· + c) '' T ⊆ S) : T.IsAPOfLengthFree l := by
  intro t ht hap
  exact hS _ ((Set.image_mono ht).trans hT) (sa_image_ap c hap)

theorem sa_bdd (k N : ℕ) : BddAbove {x | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = x} := by
  refine ⟨N, ?_⟩
  rintro _ ⟨S, hS, -, rfl⟩
  simpa using Finset.card_le_card hS

theorem sa_block (k N j : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ).IsAPOfLengthFree k) :
    (S.filter (fun x => j * N < x ∧ x ≤ j * N + N)).card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  set Sj := S.filter (fun x => j * N < x ∧ x ≤ j * N + N) with hSj
  have hinj : Set.InjOn (fun x => x - j * N) (Sj : Set ℕ) := by
    intro x hx y hy hxy
    simp only [hSj, Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    omega
  rw [← Finset.card_image_of_injOn hinj]
  apply le_csSup (sa_bdd k N)
  refine ⟨Sj.image (fun x => x - j * N), ?_, ?_, rfl⟩
  · intro y hy
    simp only [Finset.mem_image, hSj, Finset.mem_filter] at hy
    obtain ⟨x, ⟨-, h1, h2⟩, rfl⟩ := hy
    simp only [Finset.mem_Icc]
    omega
  · apply sa_free_of_image (j * N) hS
    rintro _ ⟨y, hy, rfl⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, hSj, Finset.mem_filter] at hy
    obtain ⟨x, ⟨hx, h1, h2⟩, rfl⟩ := hy
    have : x - j * N + j * N = x := by omega
    simp only [Finset.mem_coe, this]
    exact hx

end OMA.SolSA

open OMA.SolSA in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H1 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H1
  intro k hk N
  show Set.IsAPOfLengthFree.maxCard k (4 * N) ≤ 4 * Set.IsAPOfLengthFree.maxCard k N
  revert k hk N

  intro k _ N
  apply csSup_le'
  rintro _ ⟨S, hS, hfree, rfl⟩
  have hsub : S ⊆ S.filter (fun x => 0 * N < x ∧ x ≤ 0 * N + N) ∪
      S.filter (fun x => 1 * N < x ∧ x ≤ 1 * N + N) ∪
      S.filter (fun x => 2 * N < x ∧ x ≤ 2 * N + N) ∪
      S.filter (fun x => 3 * N < x ∧ x ≤ 3 * N + N) := by
    intro x hx
    have := hS hx
    simp only [Finset.mem_Icc] at this
    simp only [Finset.mem_union, Finset.mem_filter, hx, true_and]
    omega
  have h0 := sa_block k N 0 S hfree
  have h1 := sa_block k N 1 S hfree
  have h2 := sa_block k N 2 S hfree
  have h3 := sa_block k N 3 S hfree
  calc S.card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ _ := by omega
