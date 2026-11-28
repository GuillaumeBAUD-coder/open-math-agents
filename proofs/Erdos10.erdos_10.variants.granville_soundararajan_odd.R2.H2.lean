import OMAReductions.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R2
import Mathlib
-- Credit: @LordMike

theorem OMA.solution : OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R2.H2 := by
  intro m k hm
  obtain ⟨p, pows, hp, hcard, hsum⟩ := hm
  refine ⟨p, 0 ::ₘ pows, hp, ?_, ?_⟩
  · simp only [Multiset.card_cons]
    omega
  · simp only [Multiset.map_cons, Multiset.sum_cons, pow_zero]
    omega
