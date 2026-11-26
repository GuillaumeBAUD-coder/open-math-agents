import OMAReductions.R_BusyBeaver_BB_3_R1

/-! # A three-state machine that stops after exactly 21 transitions -/
-- Credit: @steveDOTdigital

open Turing Turing.BusyBeaver BusyBeaver
namespace OMA.BB3Witness
private def champion : Machine (Fin 2) (Fin 3) := fun q s =>
  match q.val,s.val with
  | 0,0 => some (some 1, ⟨1,.right⟩)
  | 0,_ => some (none,   ⟨1,.right⟩)
  | 1,0 => some (some 1, ⟨1,.left⟩)
  | 1,_ => some (some 2, ⟨0,.right⟩)
  | _,0 => some (some 2, ⟨1,.left⟩)
  | _,_ => some (some 0, ⟨1,.left⟩)
private theorem stop : champion.multiStep (Machine.init []) 22 = none := by rfl
private theorem live : (champion.multiStep (Machine.init []) 21).isSome := by rfl
theorem witness : OMA.R_BusyBeaver_BB_3_R1.H1 := by
  let C : Candidate 3 :=
    { Γ := Fin 2
      Λ := Fin 3
      Γ_fintype := inferInstance
      Γ_card := Fintype.card_fin _
      Γ_inhabited := inferInstance
      Λ_fintype := inferInstance
      Λ_card := Fintype.card_fin _
      Λ_inhabited := inferInstance
      M := champion
      M_isHalting := (Machine.isHalting_iff_exists_haltsAt champion).mpr ⟨21,stop⟩ }
  refine ⟨C,?_⟩
  exact Machine.haltingNumber_def champion 21 (Option.isSome_iff_exists.mp live) stop
end OMA.BB3Witness

theorem OMA.solution : OMA.R_BusyBeaver_BB_3_R1.H1 := OMA.BB3Witness.witness
