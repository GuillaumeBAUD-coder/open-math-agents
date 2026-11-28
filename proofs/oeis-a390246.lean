import OMAStatements.S_oeis_a390246

-- Problem: A390246: a(n) is the least integer k such that there exist n distinct integers b1, ..., bn with n < bi < n+k and bi is divisible by i for 1
-- Upstream: formal-conjectures statements/oeis-a390246.lean:0 (declaration OMA.S_oeis_a390246.main)
-- Credit: @yuka30240 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a390246

theorem OMA.solution : type_of% @OMA.S_oeis_a390246.main := by
  rintro (_ | m) hn
  · omega
  change sInf (widths (m + 1)) = sInf (endpoints (m + 1)) - m
  -- With lower endpoint m + 1, an open interval of width k ends at k + m inclusively.
  have shift : widths (m + 1) = {k | k + m ∈ endpoints (m + 1)} := by
    ext k
    simp only [widths, endpoints, Set.mem_ofPred_eq,
      show m + 1 + k = k + m + 1 by omega, Nat.lt_succ_iff, Nat.succ_le_iff]
  rw [shift]
  obtain empty | inhabited := (endpoints (m + 1)).eq_empty_or_nonempty
  · simp [empty]
  have lower : m ≤ sInf (endpoints (m + 1)) := by
    obtain ⟨b, _, hb⟩ := Nat.sInf_mem inhabited
    have bounds := (hb 0).2
    omega
  exact Nat.eq_sub_of_add_eq (Nat.sInf_add (p := fun u ↦ u ∈ endpoints (m + 1)) lower)

