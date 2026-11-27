import OMAStatements.S_oeis_a346310
import Mathlib

/-!
Every word of length `L` has `#0 + #1 = L`, so `#0 - #1` is even iff `L` is even. The words of
length `L` occupy the (0-based) indices `i` with `2^L <= i + 2 < 2^(L+1)`, so the word at
position `n >= 1` has length `log2(n+1)`. Hence position `n` is counted iff `n >= 1` and `n + 1`
has an odd number of binary digits (`log2(n+1)` even). The set of numbers with an odd number of
binary digits misses `0` and contains `1`; shifting it down by one and removing `0` is exactly
the set of counted positions, which a count argument turns into `a(n) = A053738(n+1) - 1`.
-/

namespace R346310
open OMA.S_oeis_a346310

/-- Numbers with an odd number of binary digits. -/
def OD (k : ℕ) : Prop := Odd (Nat.digits 2 k).length

theorem vectors_length (L : ℕ) : (vectors L).length = 2 ^ L := by
  simp [vectors]

theorem mem_vectors_length {L : ℕ} {v : List Bool} (h : v ∈ vectors L) : v.length = L := by
  unfold vectors at h
  rw [List.mem_map] at h
  obtain ⟨j, _, rfl⟩ := h
  simp

theorem wordsUpTo_succ (N : ℕ) : wordsUpTo (N + 1) = wordsUpTo N ++ vectors (N + 1) := by
  unfold wordsUpTo
  rw [List.range'_concat, List.flatMap_append, List.flatMap_singleton,
    show 1 + 1 * N = N + 1 by ring]

theorem wordsUpTo_length (N : ℕ) : (wordsUpTo N).length + 2 = 2 ^ (N + 1) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [wordsUpTo_succ, List.length_append, vectors_length,
      show 2 ^ (N + 1 + 1) = 2 * 2 ^ (N + 1) by ring]
    omega

theorem length_word (N : ℕ) : ∀ i, i + 2 < 2 ^ (N + 1) →
    ((wordsUpTo N).getD i []).length = Nat.log 2 (i + 2) := by
  induction N with
  | zero =>
    intro i hi
    simp at hi
  | succ N ih =>
    intro i hi
    have hlen := wordsUpTo_length N
    rw [wordsUpTo_succ]
    by_cases h : i + 2 < 2 ^ (N + 1)
    · rw [List.getD_append (wordsUpTo N) (vectors (N + 1)) [] i (by omega)]
      exact ih i h
    · rw [List.getD_append_right (wordsUpTo N) (vectors (N + 1)) [] i (by omega)]
      have hi' : i + 2 < 2 * 2 ^ (N + 1) := by
        rw [show 2 ^ (N + 1 + 1) = 2 * 2 ^ (N + 1) by ring] at hi
        exact hi
      have hj : i - (wordsUpTo N).length < (vectors (N + 1)).length := by
        rw [vectors_length]
        omega
      rw [List.getD_eq_getElem _ _ hj, mem_vectors_length (List.getElem_mem hj)]
      symm
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · omega
      · exact hi

theorem OD_iff (k : ℕ) : OD k ↔ k ≠ 0 ∧ Even (Nat.log 2 k) := by
  unfold OD
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Nat.odd_iff]
  · rw [Nat.length_digits 2 k (by norm_num) (by omega), Nat.odd_iff, Nat.even_iff]
    omega

theorem OD_zero : ¬ OD 0 := fun h => ((OD_iff 0).mp h).1 rfl

theorem OD_one : OD 1 := (OD_iff 1).mpr ⟨one_ne_zero, by rw [Nat.log_one_right]; exact ⟨0, rfl⟩⟩

theorem OD_infinite : (Set.ofPred OD).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨2 ^ (2 * a), ?_, ?_⟩
  · show OD (2 ^ (2 * a))
    exact (OD_iff _).mpr ⟨pow_ne_zero _ two_ne_zero, by
      rw [Nat.log_pow (by norm_num)]
      exact even_two_mul a⟩
  · calc a < 2 ^ a := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem EvenPos_iff (n : ℕ) : EvenPos n ↔ 1 ≤ n ∧ OD (n + 1) := by
  unfold EvenPos
  refine and_congr_right fun hn => ?_
  have hb : n - 1 + 2 < 2 ^ (n + 1) := by
    have := (Nat.lt_two_pow_self : n < 2 ^ n)
    rw [pow_succ]
    omega
  have hl : (w n).length = Nat.log 2 (n + 1) := by
    unfold w
    have := length_word n (n - 1) hb
    rwa [show n - 1 + 2 = n + 1 by omega] at this
  have hc := List.count_false_add_count_true (w n)
  rw [OD_iff, Int.even_iff, Nat.even_iff, ← hl]
  omega

theorem EvenPos_eq : EvenPos = fun i => 1 ≤ i ∧ OD (i + 1) :=
  funext fun i => propext (EvenPos_iff i)

theorem count_shift (P : ℕ → Prop) [DecidablePred P] (hP0 : ¬ P 0) (hP1 : P 1) (j : ℕ) :
    Nat.count (fun i => 1 ≤ i ∧ P (i + 1)) (j + 1) + 1 = Nat.count P (j + 1 + 1) := by
  rw [Nat.count_succ', Nat.count_succ', Nat.count_succ']
  simp [hP0, hP1]

end R346310

open OMA.S_oeis_a346310 R346310 in
theorem OMA.solution : type_of% @OMA.S_oeis_a346310.main := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold a A053738
  rw [EvenPos_eq, Nat.add_sub_cancel, show k + 1 + 1 - 1 = k + 1 by omega]
  show Nat.nth (fun i => 1 ≤ i ∧ OD (i + 1)) k = Nat.nth OD (k + 1) - 1
  have hmem : OD (Nat.nth OD (k + 1)) := Nat.nth_mem_of_infinite OD_infinite (k + 1)
  have hcnt : Nat.count OD (Nat.nth OD (k + 1)) = k + 1 :=
    Nat.count_nth_of_infinite OD_infinite (k + 1)
  have h0 : 1 ≤ Nat.nth OD 0 := by
    have h := Nat.nth_mem_of_infinite OD_infinite 0
    rcases Nat.eq_zero_or_pos (Nat.nth OD 0) with h' | h'
    · rw [h'] at h
      exact absurd h OD_zero
    · exact h'
  have hlt : Nat.nth OD 0 < Nat.nth OD (k + 1) := (Nat.nth_lt_nth OD_infinite).mpr (by omega)
  obtain ⟨j, hj⟩ : ∃ j, Nat.nth OD (k + 1) = j + 1 + 1 := ⟨Nat.nth OD (k + 1) - 2, by omega⟩
  rw [hj] at hmem hcnt
  rw [hj, show j + 1 + 1 - 1 = j + 1 by omega]
  have hQ : (fun i => 1 ≤ i ∧ OD (i + 1)) (j + 1) := ⟨by omega, hmem⟩
  have hc := count_shift OD OD_zero OD_one j
  rw [hcnt] at hc
  have hc' : Nat.count (fun i => 1 ≤ i ∧ OD (i + 1)) (j + 1) = k := by omega
  rw [← hc']
  exact Nat.nth_count hQ
