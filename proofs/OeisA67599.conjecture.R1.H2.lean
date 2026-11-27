import OMAReductions.R_OeisA67599_conjecture_R1

-- Step OeisA67599.conjecture.R1.H2: hypothesis H2 of reduction OeisA67599.conjecture.R1
-- Credit: @DeepDuke
-- H2 := ∀ q : ℕ, 7 < q → q.Prime →     OeisA67599.a (2401 * q) = 740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hp
  have hf : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
    have hperm := Nat.primeFactorsList_unique
      (show [7, 7, 7, 7, q].prod = 2401 * q by simp; ring)
      (show ∀ p ∈ [7, 7, 7, 7, q], p.Prime by
        intro p h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> first | decide | exact hp)
    exact hperm.symm.eq_of_pairwise' (r := (· ≤ ·))
      (Nat.primeFactorsList_sorted _).pairwise (by simp [List.pairwise_cons]; omega)
  have hne : q ≠ 7 := by omega
  have hne' : 7 ≠ q := hne.symm
  unfold OeisA67599.a
  rw [if_neg (by omega), hf]
  have hd1 : Nat.digits 10 1 = [1] := by decide
  have hd4 : Nat.digits 10 4 = [4] := by decide
  simp [hne, hne', OeisA67599.concatenateNats, hd1, hd4]
  ring

