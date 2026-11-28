import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3

namespace CollatzH2

def E (o : ℕ) : ℕ := o * 1584962500721156 / 1000000000000000 + 1

theorem table : ∀ o < 971, 2 ^ (E o - 1) ≤ 3 ^ o ∧ 300001 ^ o < 2 ^ (E o) * 100000 ^ o := by
  decide +kernel

end CollatzH2

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3.H2 := by
  intro o e _ ho h
  obtain ⟨h1, h2⟩ := CollatzH2.table o ho
  have hlt : 2 ^ (CollatzH2.E o - 1) < 2 ^ e := lt_of_le_of_lt h1 h
  have he : CollatzH2.E o - 1 < e := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hle : 2 ^ CollatzH2.E o ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 300001 ^ o < 2 ^ CollatzH2.E o * 100000 ^ o := h2
    _ ≤ 2 ^ e * 100000 ^ o := Nat.mul_le_mul_right _ hle
