import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1_H2_R1
import Mathlib

namespace CollatzSieve8192
open CollatzConjecture

private def advance : ℕ → ℕ × ℕ → Option (ℕ × ℕ)
  | 0, ab => some ab
  | i + 1, (a, b) =>
    if a % 2 = 0 then
      if b % 2 = 0 then advance i (a / 2, b / 2)
      else advance i (3 * a, 3 * b + 1)
    else none

private theorem step (a b q : ℕ) (ha : a % 2 = 0) :
    collatzStep (a * q + b) =
      if b % 2 = 0 then a / 2 * q + b / 2 else 3 * a * q + (3 * b + 1) := by
  have hsplit : a = 2 * (a / 2) := by omega
  conv in a * q + b =>
    rw [hsplit, Nat.mul_assoc]
  have hparity : Even (2 * (a / 2 * q) + b) ↔ b % 2 = 0 := by
    rw [Nat.even_iff]
    omega
  simp only [collatzStep, hparity]
  split
  · omega
  · rw [← Nat.mul_assoc 2, ← hsplit]
    ring

private theorem advance_correct (i a b q c d : ℕ)
    (h : advance i (a, b) = some (c, d)) :
    collatzStep^[i] (a * q + b) = c * q + d := by
  induction i generalizing a b with
  | zero =>
    simp [advance] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ i ih =>
    by_cases ha : a % 2 = 0
    · rw [Function.iterate_succ_apply, step a b q ha]
      by_cases hb : b % 2 = 0
      · simp only [advance, if_pos ha, if_pos hb] at h
        simpa only [if_pos hb] using ih (a / 2) (b / 2) h
      · simp only [advance, if_pos ha, if_neg hb] at h
        simpa only [if_neg hb] using ih (3 * a) (3 * b + 1) h
    · simp [advance, ha] at h

private def residues : List ℕ := [191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159]

private def descends (r i : ℕ) : Bool :=
  match advance i (8192, r) with
  | some (a, b) => decide (a ≤ 8192 ∧ b < r)
  | none => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem certificate : residues.Forall (fun r => ∃ i : Fin 22, descends r i.val = true) := by
  decide +kernel

end CollatzSieve8192

open CollatzSieve8192 CollatzConjecture

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro n hn hr
  change n % 8192 ∈ residues at hr
  obtain ⟨i, hi⟩ := (List.forall_iff_forall_mem.mp certificate) (n % 8192) hr
  unfold descends at hi
  cases h : advance i.val (8192, n % 8192) with
  | none => simp [h] at hi
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hlt : a ≤ 8192 ∧ b < n % 8192 := by simpa [h] using hi
    refine ⟨i.val, by have := i.isLt; omega, ?_⟩
    have hiter := advance_correct i.val 8192 (n % 8192) (n / 8192) a b h
    rw [Nat.div_add_mod] at hiter
    calc
      _ = a * (n / 8192) + b := hiter
      _ < 8192 * (n / 8192) + n % 8192 :=
        Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right _ hlt.1) hlt.2
      _ = n := Nat.div_add_mod _ _