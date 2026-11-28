import OMAStatements.S_oeis_a004767

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: write m = 2t+1, so (3m+1)/2 = 3t+2, which is always > m and is odd iff t is odd,
-- i.e. iff m = 4s+3.

open OMA.S_oeis_a004767

theorem OMA.solution : type_of% @OMA.S_oeis_a004767.main := by
  intro m hm
  obtain ⟨t, rfl⟩ := hm
  have e : (3 * (2 * t + 1) + 1) / 2 = 3 * t + 2 := by omega
  rw [e]
  constructor
  · rintro ⟨⟨r, hr⟩, -⟩
    refine ⟨(t - 1) / 2, ?_⟩
    unfold a; omega
  · rintro ⟨s, hs⟩
    unfold a at hs
    refine ⟨⟨3 * s + 2, by omega⟩, by omega⟩
