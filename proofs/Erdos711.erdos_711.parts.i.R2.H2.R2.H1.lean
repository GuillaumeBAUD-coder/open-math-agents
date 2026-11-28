import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R2
import Mathlib

theorem OMA.solution : OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R2.H1 := by
  intro U Y q D hU hY
  have h1 : ∀ d ∈ U, q * (q - 1) ≤
      ((Y.offDiag).filter (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2)).card := by
    intro d hd
    have e : (Y.offDiag).filter (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2) =
        (Y.filter (d ∣ ·)).offDiag := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      tauto
    rw [e, Finset.offDiag_card]
    have hm := hU d hd
    calc q * (q - 1) ≤ (Y.filter (d ∣ ·)).card * ((Y.filter (d ∣ ·)).card - 1) :=
          Nat.mul_le_mul hm (Nat.sub_le_sub_right hm 1)
      _ = _ := by rw [Nat.mul_sub_one]
  have h2 : ∀ p ∈ Y.offDiag, (U.filter (fun d => d ∣ p.1 ∧ d ∣ p.2)).card ≤ D := by
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_offDiag] at hp
    obtain ⟨hx, hy, hne⟩ := hp
    rcases lt_or_gt_of_ne hne with h | h
    · refine le_trans (Finset.card_le_card ?_) (hY x hx y hy h)
      intro d hd
      simp only [Finset.mem_filter] at hd
      refine Nat.mem_divisors.2 ⟨?_, by omega⟩
      first | exact Nat.dvd_sub' hd.2.2 hd.2.1 | exact Nat.dvd_sub hd.2.2 hd.2.1
    · refine le_trans (Finset.card_le_card ?_) (hY y hy x hx h)
      intro d hd
      simp only [Finset.mem_filter] at hd
      refine Nat.mem_divisors.2 ⟨?_, by omega⟩
      first | exact Nat.dvd_sub' hd.2.1 hd.2.2 | exact Nat.dvd_sub hd.2.1 hd.2.2
  calc U.card * (q * (q - 1)) = ∑ _d ∈ U, q * (q - 1) := by simp
    _ ≤ ∑ d ∈ U, ((Y.offDiag).filter (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2)).card :=
        Finset.sum_le_sum h1
    _ = ∑ p ∈ Y.offDiag, (U.filter (fun d => d ∣ p.1 ∧ d ∣ p.2)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _p ∈ Y.offDiag, D := Finset.sum_le_sum h2
    _ = Y.card * (Y.card - 1) * D := by
        rw [Finset.sum_const, smul_eq_mul, Finset.offDiag_card, Nat.mul_sub_one]
