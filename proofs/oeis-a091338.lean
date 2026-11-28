import OMAStatements.S_oeis_a091338

namespace OMA.P_oeis_a091338

open OMA.S_oeis_a091338

lemma k1 : kronecker 3 1 = 1 := by
  rw [kronecker, if_neg (by norm_num)]
  exact jacobiSym.one_right 3

lemma k2 : kronecker 3 2 = -1 := by
  rw [kronecker, if_pos (by norm_num)]
  rw [show (1 + 1) / 2 = 1 by norm_num, k1]
  norm_num [kron2]

lemma k4 : kronecker 3 4 = 1 := by
  rw [kronecker, if_pos (by norm_num)]
  rw [show (3 + 1) / 2 = 2 by norm_num, k2]
  norm_num [kron2]

lemma k8 : kronecker 3 8 = -1 := by
  rw [kronecker, if_pos (by norm_num)]
  rw [show (7 + 1) / 2 = 4 by norm_num, k4]
  norm_num [kron2]

lemma k16 : kronecker 3 16 = 1 := by
  rw [kronecker, if_pos (by norm_num)]
  rw [show (15 + 1) / 2 = 8 by norm_num, k8]
  norm_num [kron2]

end OMA.P_oeis_a091338

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a091338.main) := by
  intro h
  have h0 := h.2.2.2.2.2.2.2 0
  simp only [OMA.S_oeis_a091338.a] at h0
  norm_num [OMA.P_oeis_a091338.k16, OMA.P_oeis_a091338.k4] at h0
