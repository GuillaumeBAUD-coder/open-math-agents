import OMAStatements.S_arxiv_2611_14718

/-!
# A subcubic tree disproves stochastic dominance in graph parking

Credit: @rleshner. Among its 55 maximal independent sets, one has size six,
50 have size seven, and four have size eight. The sequential process stops by
six placements with probability 64/3375, which exceeds the static probability
1/55. This reverses the required lower-tail inequality.
-/

namespace ParkingWitness
open OMA.S_arxiv_2611_14718

private def N : Fin 15 → ℕ := ![1025, 134, 294, 2072, 1112, 36, 336, 130,
  324, 16896, 1041, 10248, 12288, 30720, 25088]

private def near (i j : Fin 15) : Prop := i ≠ j ∧ (N i).testBit j.val = true

private instance (i j : Fin 15) : Decidable (near i j) := by unfold near; infer_instance

private def tree : SimpleGraph (Fin 15) where
  Adj := near
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

private instance : DecidableRel tree.Adj := fun i j => inferInstanceAs (Decidable (near i j))

private theorem degree_bound : ∀ v, tree.degree v ≤ 3 := by decide +kernel

private theorem masks : closedMask tree = N := by
  funext i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
private theorem static : staticCDF N 6 = 1 / 55 := by decide +kernel

/-- Keep only branches whose chosen vertices all belong to the unique six-set. -/
private def allowed : ℕ := 8853

private def restricted : ℕ → ℕ → ℚ
  | 0, s => if s = 0 then 1 else 0
  | k + 1, s =>
    if s = 0 then 1 else
      let xs := seats 15 s
      (xs.map (fun i => if allowed.testBit i.val then restricted k (s ^^^ (s &&& N i)) else 0)).sum / xs.length

private theorem seq_nonneg (k s : ℕ) : 0 ≤ seqCDF N k s := by
  induction k generalizing s with
  | zero => simp only [seqCDF]; split <;> norm_num
  | succ k ih =>
    simp only [seqCDF]
    split
    · norm_num
    · apply div_nonneg _ (by positivity)
      apply List.sum_nonneg
      simpa using fun (i : Fin 15) (_ : i ∈ seats 15 s) => ih (s ^^^ (s &&& N i))

private theorem lower (k s : ℕ) : restricted k s ≤ seqCDF N k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [restricted, seqCDF]
    split
    · rfl
    · apply div_le_div_of_nonneg_right _ (by positivity)
      apply List.sum_le_sum
      intro i hi
      split
      · apply ih
      · apply seq_nonneg

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem selected : restricted 6 32767 = 64 / 3375 := by decide +kernel
end ParkingWitness

open OMA.S_arxiv_2611_14718 ParkingWitness in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2611_14718.main) := by
  intro claim
  have h := claim tree degree_bound 6
  rw [masks] at h
  change seqCDF N 6 32767 ≤ staticCDF N 6 at h
  have q := (lower 6 32767).trans h
  rw [static, selected] at q
  norm_num at q
