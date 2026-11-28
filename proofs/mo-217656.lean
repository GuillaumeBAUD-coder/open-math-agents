import OMAStatements.S_mo_217656

-- Problem: exchange mappings between equal-sized subsets
-- Upstream: formal-conjectures statements/mo-217656.lean:0 (declaration OMA.S_mo_217656.main)
-- Credit: @yhay81 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_mo_217656

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_217656.main) := by
  intro h
  obtain ⟨maps, _, hfix, hcoc⟩ := h 3 2 (by decide)
  let A : Selection 3 2 := ⟨{0, 1}, by decide⟩
  let B : Selection 3 2 := ⟨{1, 2}, by decide⟩
  let C : Selection 3 2 := ⟨{0, 2}, by decide⟩
  have hCA : maps C A ⟨0, by decide⟩ = ⟨0, by decide⟩ := hfix C A 0 (by decide) (by decide)
  have hAB1 : maps A B ⟨1, by decide⟩ = ⟨1, by decide⟩ := hfix A B 1 (by decide) (by decide)
  have hCB2 : maps C B ⟨2, by decide⟩ = ⟨2, by decide⟩ := hfix C B 2 (by decide) (by decide)
  have heq : maps A B ⟨0, by decide⟩ = maps C B ⟨0, by decide⟩ := by
    have hc := hcoc A B C ⟨0, by decide⟩
    rwa [hCA] at hc
  have hmem := (maps A B ⟨0, by decide⟩).property
  simp only [B, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2
  · have : (⟨0, by decide⟩ : Element A) = ⟨1, by decide⟩ :=
      (maps A B).injective ((Subtype.ext h1).trans hAB1.symm)
    exact (by decide : (0 : Fin 3) ≠ 1) (congrArg Subtype.val this)
  · have : (⟨0, by decide⟩ : Element C) = ⟨2, by decide⟩ :=
      (maps C B).injective (heq.symm.trans ((Subtype.ext h2).trans hCB2.symm))
    exact (by decide : (0 : Fin 3) ≠ 2) (congrArg Subtype.val this)
