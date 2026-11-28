import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1_H2_R1
import Mathlib

open CollatzConjecture

private def residues : List ℕ := [191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem certificate : residues.Forall (fun r => ∃ t : Fin 22,
    ((Finset.range t.val).filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ 13 ∧
    3 ^ ((Finset.range t.val).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
    2 ^ ((Finset.range t.val).filter (fun i => collatzStep^[i] r % 2 = 0)).card) := by
  decide +kernel

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro r hr
  change r ∈ residues at hr
  obtain ⟨t, ht⟩ := (List.forall_iff_forall_mem.mp certificate) r hr
  exact ⟨t.val, by have := t.isLt; omega, ht⟩