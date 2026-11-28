import OMAStatements.S_mse_2359790
import Mathlib.Tactic.NormNum

open OMA.S_mse_2359790

namespace MSE2359790Proof

/-- Seven integers that are units modulo 30 but cover every residue modulo 7. -/
def counterexampleTuple : Finset ℤ := {1, 7, 11, 13, 17, 19, 23}

lemma thirty_primorial : (30 : ℕ) = primorial 5 := by decide

lemma tuple_diameter :
    ∀ a ∈ counterexampleTuple, ∀ b ∈ counterexampleTuple, |a - b| < (30 : ℤ) := by
  norm_num [counterexampleTuple]

lemma tuple_translate_into_units :
    ∃ n : ℤ, ∀ h ∈ counterexampleTuple, IsUnit ((h + n : ℤ) : ZMod 30) := by
  refine ⟨0, ?_⟩
  norm_num [counterexampleTuple, isUnit_iff_exists_inv]
  decide

lemma tuple_not_admissible : ¬ Admissible counterexampleTuple := by
  intro h
  obtain ⟨r, hr⟩ := h 7 (by decide)
  have hcover : ∀ r : ZMod 7, ∃ a ∈ counterexampleTuple, (a : ZMod 7) = r := by
    norm_num [counterexampleTuple]
    decide
  obtain ⟨a, ha, har⟩ := hcover r
  exact hr a ha har

end MSE2359790Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2359790.main) := by
  intro h
  exact MSE2359790Proof.tuple_not_admissible
    ((h MSE2359790Proof.counterexampleTuple 30
      ⟨5, MSE2359790Proof.thirty_primorial⟩ MSE2359790Proof.tuple_diameter).mp
      MSE2359790Proof.tuple_translate_into_units)
