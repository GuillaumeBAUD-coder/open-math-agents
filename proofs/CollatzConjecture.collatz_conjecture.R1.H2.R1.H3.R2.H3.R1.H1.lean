import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1

namespace CollatzResidueDescent

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

private def surviving : List ℕ :=
  [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
    239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
    511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
    767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023]

private def descends (r i : ℕ) : Bool :=
  match advance i (1024, r) with
  | some (a, b) => decide (a ≤ 1024 ∧ b < r)
  | none => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem residue_certificate : ∀ r : Fin 1024,
    r.val % 128 ∈ ([27, 31, 39, 47, 63, 71, 79, 91, 95, 103, 111, 123, 127] : List ℕ) →
    r.val ∉ surviving → ∃ i : Fin 17, descends r.val i.val = true := by
  decide +kernel

theorem descent (n : ℕ)
    (hold : n % 128 ∈ ([27, 31, 39, 47, 63, 71, 79, 91, 95, 103, 111, 123, 127] : List ℕ))
    (hnew : n % 1024 ∉ surviving) : ∃ i : ℕ, collatzStep^[i] n < n := by
  let r : Fin 1024 := ⟨n % 1024, Nat.mod_lt _ (by decide)⟩
  have hsplit : 1024 * (n / 1024) + r.val = n := Nat.div_add_mod _ _
  have hr : r.val % 128 = n % 128 := by
    change n % 1024 % 128 = n % 128
    omega
  obtain ⟨i, hi⟩ := residue_certificate r (hr ▸ hold) hnew
  unfold descends at hi
  cases h : advance i.val (1024, r.val) with
  | none => simp [h] at hi
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hlt : a ≤ 1024 ∧ b < r.val := by simpa [h] using hi
    refine ⟨i.val, ?_⟩
    have hiter := advance_correct i.val 1024 r.val (n / 1024) a b h
    rw [hsplit] at hiter
    calc
      _ = a * (n / 1024) + b := hiter
      _ < 1024 * (n / 1024) + r.val :=
        Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right _ hlt.1) hlt.2
      _ = n := hsplit

end CollatzResidueDescent

theorem OMA.solution :
    OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1.H1 := by
  intro n _ hold hnew
  apply CollatzResidueDescent.descent n _ hnew
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hold