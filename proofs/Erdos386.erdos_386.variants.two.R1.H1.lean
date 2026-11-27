import OMAReductions.R_Erdos386_erdos_386_variants_two_R1

-- Step Erdos386.erdos_386.variants.two.R1.H1: hypothesis H1 of reduction Erdos386.erdos_386.variants.two.R1
-- Credit: @ptc-prover-bot

/-! If `8P + 1 = s²` then `s = 2t + 1` is odd and `2P = t(t + 1)`, so `P = C(t + 1, 2)`;
`P ≥ 6` forces `t ≥ 3`, and `P ≤ (t + 1)²`. -/

namespace OMA.Erdos386TwoH1

theorem H1_proof : OMA.R_Erdos386_erdos_386_variants_two_R1.H1 := by
  intro P hP hsq
  obtain ⟨s, hs⟩ := hsq
  have hodd : Odd (s * s) := by rw [← hs]; exact ⟨4 * P, by ring⟩
  obtain ⟨t, rfl⟩ := (Nat.odd_mul.mp hodd).1
  have h2 : 2 * P = t * (t + 1) := by nlinarith
  refine ⟨t + 1, ?_, ?_, ?_⟩
  · by_contra h
    have ht : t ≤ 2 := by omega
    interval_cases t <;> omega
  · rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have : (t + 1) * t = 2 * P := by rw [h2]; ring
    rw [this]; omega
  · nlinarith

end OMA.Erdos386TwoH1

theorem OMA.solution : OMA.R_Erdos386_erdos_386_variants_two_R1.H1 := OMA.Erdos386TwoH1.H1_proof
