import OMAStatements.S_oeis_a073783

/-! Proof of R. J. Mathar's A073783 conjecture. Credit: @cjchaffin.
For a positive index j, j − π(j) counts 1 and the composites through j.
Its level sets are half-open intervals between consecutive composites. -/

namespace OeisA073783Proof
open OMA.S_oeis_a073783

private abbrev C (m : ℕ) := 1 < m ∧ ¬ m.Prime

private theorem infiniteC : (Set.ofPred C).Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  exact ⟨2*(n+2), ⟨by omega, Nat.not_prime_mul (by decide) (by omega)⟩, by omega⟩

private theorem balance (k : ℕ) :
    Nat.count C (k+2) + Nat.count Nat.Prime (k+2) = k := by
  induction k with
  | zero => decide
  | succ k ih =>
    change Nat.count C ((k+2)+1) + Nat.count Nat.Prime ((k+2)+1) = k+1
    rw [Nat.count_succ, Nat.count_succ (p := Nat.Prime)]
    have h : 1 < k+2 := by omega
    by_cases hp : (k+2).Prime <;> simp [C, h, hp] <;> omega

private theorem fiber (k : ℕ) :
    {j : ℕ | 1 ≤ j ∧ A065308 j = prime (k+2)} =
      Set.Ico (Nat.nth C k) (Nat.nth C (k+1)) := by
  ext j
  have hj0 := (Nat.nth_mem_of_infinite infiniteC k).1
  change (1 ≤ j ∧ Nat.nth Nat.Prime (j-j.primeCounting-1) =
      Nat.nth Nat.Prime (k+1)) ↔ Nat.nth C k ≤ j ∧ j < Nat.nth C (k+1)
  rw [(Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.eq_iff]
  cases j with
  | zero => omega
  | succ j =>
    have hb := balance j
    change (1 ≤ j+1 ∧ j+1-Nat.count Nat.Prime (j+2)-1=k+1) ↔ _
    have hL := Nat.lt_nth_iff_count_lt infiniteC (a := k) (b := j+2)
    have hR := Nat.count_le_iff_le_nth infiniteC (a := j+2) (b := k+1)
    omega

theorem result : type_of% @OMA.S_oeis_a073783.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1, by omega⟩
  unfold a A065310
  rw [fiber k, Set.ncard_Ico_nat]
  rfl

end OeisA073783Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a073783.main := OeisA073783Proof.result
