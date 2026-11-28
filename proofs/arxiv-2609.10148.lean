import OMAStatements.S_arxiv_2609_10148
import Mathlib

namespace OMA.P_arxiv_2609_10148

open OMA.S_arxiv_2609_10148

def A11 : Finset (ZMod 11) := {0, 1, 2, 3, 4, 5, 7}
def B11 : Finset (ZMod 11) := {0, 1, 2, 5}

lemma card_A11 : A11.card = 7 := by decide
lemma card_B11 : B11.card = 4 := by decide
lemma card_rsum : (restrictedSumset A11 B11).card = 9 := by decide

lemma not_ap_B11 : ¬ IsArithProg B11 := by
  unfold IsArithProg
  rw [card_B11]
  decide

end OMA.P_arxiv_2609_10148

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2609_10148.main) := by
  intro h
  have ⟨_, hB⟩ :=
    h 11 (by decide) OMA.P_arxiv_2609_10148.A11 OMA.P_arxiv_2609_10148.B11
      (by decide) (by decide) (by decide) (by decide) (by decide)
  exact OMA.P_arxiv_2609_10148.not_ap_B11 hB
