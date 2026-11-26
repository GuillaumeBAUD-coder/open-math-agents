import FormalConjectures.Wikipedia.BusyBeaver

/-! # A witness and a universal stopping-time bound for three-state machines -/
-- Credit: @steveDOTdigital
namespace OMA.R_BusyBeaver_BB_3_R1

open Turing Turing.BusyBeaver BusyBeaver

def H1 : Prop := ∃ C : Candidate 3, C.M.haltingNumber = (21 : ℕ)

def H2 : Prop := ∀ (C : Candidate 3) (n : ℕ), C.M.haltingNumber = n → n ≤ 21

theorem main : H1 → H2 → type_of% @BusyBeaver.BB_3 := by
  intro witness bound
  let S := {n : ℕ | ∃ C : Candidate 3, C.M.haltingNumber = n}
  have hm : 21 ∈ S := witness
  have hub : ∀ n ∈ S, n ≤ 21 := fun n ⟨C,hC⟩ => bound C n hC
  change sSup S = 21
  exact le_antisymm (csSup_le ⟨21,hm⟩ hub) (le_csSup ⟨21,hub⟩ hm)

end OMA.R_BusyBeaver_BB_3_R1
