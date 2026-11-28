import OMAStatements.S_mo_217656

open OMA.S_mo_217656

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_217656.main) := by
  intro h
  obtain ⟨maps, _, fixes, comp⟩ := h 3 2 (by decide)
  let A : Selection 3 2 := ⟨{0, 1}, by decide⟩
  let B : Selection 3 2 := ⟨{0, 2}, by decide⟩
  let C : Selection 3 2 := ⟨{1, 2}, by decide⟩
  let a0 : Element A := ⟨0, by decide⟩
  let a1 : Element A := ⟨1, by decide⟩
  let b0 : Element B := ⟨0, by decide⟩
  let b2 : Element B := ⟨2, by decide⟩
  let c1 : Element C := ⟨1, by decide⟩
  let c2 : Element C := ⟨2, by decide⟩
  have fix0 : maps B A b0 = a0 := fixes B A 0 b0.property a0.property
  have fix1 : maps C A c1 = a1 := fixes C A 1 c1.property a1.property
  have fix2 : maps C B c2 = b2 := fixes C B 2 c2.property b2.property
  -- Sending 2 to A must give the same answer when starting from B or C.
  -- The first map is forced to avoid 0, and the second is forced to avoid 1.
  have same := comp B A C c2
  rw [fix2] at same
  have mem := (maps B A b2).property
  change (maps B A b2).val ∈ ({0, 1} : Finset (Fin 3)) at mem
  rcases Finset.mem_insert.mp mem with zero | one
  · have eq0 : maps B A b2 = a0 := Subtype.ext zero
    have clash : b2 = b0 := (maps B A).injective (eq0.trans fix0.symm)
    exact (by decide : (2 : Fin 3) ≠ 0) (congrArg Subtype.val clash)
  · have eq1 : maps B A b2 = a1 := Subtype.ext (Finset.mem_singleton.mp one)
    have clash : c2 = c1 := (maps C A).injective (same.symm.trans (eq1.trans fix1.symm))
    exact (by decide : (2 : Fin 3) ≠ 1) (congrArg Subtype.val clash)
