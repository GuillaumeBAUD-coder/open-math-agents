import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1
import Mathlib

namespace OMA.MahlerAffine

theorem finite_consecutive (W : Submodule ℚ (ℚ × ℚ)) (proper : W ≠ ⊤) :
    {n : ℕ | ((n : ℚ), (n : ℚ) + 1) ∈ W}.Finite := by
  apply Set.Subsingleton.finite
  intro n hn m hm
  by_contra hnm
  have hd : (m : ℚ) - (n : ℚ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast Ne.symm hnm
  have diagonal : ((1 : ℚ), (1 : ℚ)) ∈ W := by
    convert W.smul_mem (1 / ((m : ℚ) - (n : ℚ))) (W.sub_mem hm hn) using 1
    ext <;> dsimp <;> field_simp [hd] <;> ring
  have vertical : ((0 : ℚ), (1 : ℚ)) ∈ W := by
    convert W.sub_mem hn (W.smul_mem (n : ℚ) diagonal) using 1
    ext <;> dsimp <;> ring
  have horizontal : ((1 : ℚ), (0 : ℚ)) ∈ W := by
    simpa using W.sub_mem diagonal vertical
  apply proper
  apply eq_top_iff.mpr
  rintro ⟨a,b⟩ _
  simpa using W.add_mem (W.smul_mem a horizontal) (W.smul_mem b vertical)

end OMA.MahlerAffine

theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1.H2 := by
  intro W proper
  exact OMA.MahlerAffine.finite_consecutive W proper
