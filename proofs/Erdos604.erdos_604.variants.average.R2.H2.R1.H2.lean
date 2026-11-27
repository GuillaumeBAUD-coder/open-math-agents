import OMAReductions.R_Erdos604_erdos_604_variants_average_R2_H2_R1

open Finset
open scoped EuclideanGeometry Classical

private lemma dist_sq_coords (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

private lemma eq_of_coords_eq {p q : ℝ²} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

private lemma fiber_card_le_two (u v : ℝ²) (huv : u ≠ v) (F : Finset ℝ²) (d : ℝ × ℝ)
    (hF : ∀ p ∈ F, dist p u = d.1 ∧ dist p v = d.2) :
    F.card ≤ 2 := by
  set a : ℝ := v 0 - u 0
  set b : ℝ := v 1 - u 1
  have hab : 0 < a ^ 2 + b ^ 2 := by
    by_contra hle
    have h0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have h1 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact huv (eq_of_coords_eq (by linarith) (by linarith))
  let s : ℝ² → ℝ := fun p => a * (p 1 - u 1) - b * (p 0 - u 0)
  have hdot : ∀ p ∈ F, 2 * (a * (p 0 - u 0) + b * (p 1 - u 1)) =
      d.1 ^ 2 - d.2 ^ 2 + a ^ 2 + b ^ 2 := by
    intro p hp
    obtain ⟨hpu, hpv⟩ := hF p hp
    have hu : (p 0 - u 0) ^ 2 + (p 1 - u 1) ^ 2 = d.1 ^ 2 := by
      rw [← dist_sq_coords, hpu]
    have hv : (p 0 - v 0) ^ 2 + (p 1 - v 1) ^ 2 = d.2 ^ 2 := by
      rw [← dist_sq_coords, hpv]
    have h0 : p 0 - v 0 = (p 0 - u 0) - a := by dsimp [a]; ring
    have h1 : p 1 - v 1 = (p 1 - u 1) - b := by dsimp [b]; ring
    rw [h0, h1] at hv
    linarith [hu, hv]
  have hsq : ∀ p ∈ F, ∀ q ∈ F, s p ^ 2 = s q ^ 2 := by
    intro p hp q hq
    have hpu : (p 0 - u 0) ^ 2 + (p 1 - u 1) ^ 2 = d.1 ^ 2 := by
      rw [← dist_sq_coords, (hF p hp).1]
    have hqu : (q 0 - u 0) ^ 2 + (q 1 - u 1) ^ 2 = d.1 ^ 2 := by
      rw [← dist_sq_coords, (hF q hq).1]
    have hdp := hdot p hp
    have hdq := hdot q hq
    have hdot_eq : a * (p 0 - u 0) + b * (p 1 - u 1) = a * (q 0 - u 0) + b * (q 1 - u 1) := by
      linarith
    have hlagP : (a ^ 2 + b ^ 2) * ((p 0 - u 0) ^ 2 + (p 1 - u 1) ^ 2) =
        (a * (p 0 - u 0) + b * (p 1 - u 1)) ^ 2 + s p ^ 2 := by
      dsimp [s]; ring
    have hlagQ : (a ^ 2 + b ^ 2) * ((q 0 - u 0) ^ 2 + (q 1 - u 1) ^ 2) =
        (a * (q 0 - u 0) + b * (q 1 - u 1)) ^ 2 + s q ^ 2 := by
      dsimp [s]; ring
    rw [hpu] at hlagP
    rw [hqu, ← hdot_eq] at hlagQ
    linarith
  have hinj : ∀ p ∈ F, ∀ q ∈ F, s p = s q → p = q := by
    intro p hp q hq hspq
    have hdp := hdot p hp
    have hdq := hdot q hq
    have h1 : a * (p 0 - q 0) + b * (p 1 - q 1) = 0 := by linarith
    have h2 : a * (p 1 - q 1) - b * (p 0 - q 0) = 0 := by
      dsimp [s] at hspq
      linarith
    have hx : (a ^ 2 + b ^ 2) * (p 0 - q 0) = 0 := by
      calc (a ^ 2 + b ^ 2) * (p 0 - q 0)
          = a * (a * (p 0 - q 0) + b * (p 1 - q 1)) - b * (a * (p 1 - q 1) - b * (p 0 - q 0)) := by
            ring
        _ = 0 := by rw [h1, h2]; ring
    have hy : (a ^ 2 + b ^ 2) * (p 1 - q 1) = 0 := by
      calc (a ^ 2 + b ^ 2) * (p 1 - q 1)
          = b * (a * (p 0 - q 0) + b * (p 1 - q 1)) + a * (a * (p 1 - q 1) - b * (p 0 - q 0)) := by
            ring
        _ = 0 := by rw [h1, h2]; ring
    have hx0 : p 0 = q 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · linarith
      · linarith
    have hy0 : p 1 = q 1 := by
      rcases mul_eq_zero.mp hy with h | h
      · linarith
      · linarith
    exact eq_of_coords_eq hx0 hy0
  by_contra hgt
  have h3 : 3 ≤ F.card := by omega
  obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  have hcard1 : 2 ≤ (F.erase p1).card := by
    rw [Finset.card_erase_of_mem hp1]; omega
  obtain ⟨p2, hp2'⟩ := Finset.card_pos.mp (by omega : 0 < (F.erase p1).card)
  have hp2 : p2 ∈ F := Finset.mem_of_mem_erase hp2'
  have h12 : p2 ≠ p1 := Finset.ne_of_mem_erase hp2'
  have hcard2 : 1 ≤ ((F.erase p1).erase p2).card := by
    rw [Finset.card_erase_of_mem hp2']; omega
  obtain ⟨p3, hp3''⟩ := Finset.card_pos.mp (by omega : 0 < ((F.erase p1).erase p2).card)
  have hp3' : p3 ∈ F.erase p1 := Finset.mem_of_mem_erase hp3''
  have hp3 : p3 ∈ F := Finset.mem_of_mem_erase hp3'
  have h32 : p3 ≠ p2 := Finset.ne_of_mem_erase hp3''
  have h31 : p3 ≠ p1 := Finset.ne_of_mem_erase hp3'
  have h12_sq : s p1 ^ 2 = s p2 ^ 2 := hsq p1 hp1 p2 hp2
  have h13_sq : s p1 ^ 2 = s p3 ^ 2 := hsq p1 hp1 p3 hp3
  have hcase12 : s p1 = s p2 ∨ s p1 = -s p2 := sq_eq_sq_iff_eq_or_eq_neg.mp h12_sq
  have hcase13 : s p1 = s p3 ∨ s p1 = -s p3 := sq_eq_sq_iff_eq_or_eq_neg.mp h13_sq
  rcases hcase12 with h | h
  · exact h12 (hinj p1 hp1 p2 hp2 h).symm
  · rcases hcase13 with h' | h'
    · exact h31 (hinj p1 hp1 p3 hp3 h').symm
    · exact h32 (hinj p2 hp2 p3 hp3 (by linarith)).symm

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1.H2 := by
  intro A u v huv
  let f : ℝ² → ℝ × ℝ := fun p => (dist p u, dist p v)
  calc
    A.card = ∑ d ∈ A.image f, (A.filter (fun p => f p = d)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem f hp)
    _ ≤ ∑ _d ∈ A.image f, 2 := by
      refine Finset.sum_le_sum fun d _ => fiber_card_le_two u v huv _ d ?_
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    _ = 2 * (A.image f).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
