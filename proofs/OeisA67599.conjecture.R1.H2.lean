import OMAReductions.R_OeisA67599_conjecture_R1

-- Step OeisA67599.conjecture.R1.H2: hypothesis H2 of reduction OeisA67599.conjecture.R1
-- Credit: @marcusbuffett
-- H2 := ∀ q : ℕ, 7 < q → q.Prime →     OeisA67599.a (2401 * q) = 740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hp
  have hf : (2401*q).primeFactorsList = [7,7,7,7,q] := by
    have hprod : ([7,7,7,7,q] : List ℕ).prod = 2401*q := by simp; ring
    have hprime : ∀ p ∈ ([7,7,7,7,q] : List ℕ), p.Prime := by
      simpa [show Nat.Prime 7 by decide] using hp
    have hsort : ([7,7,7,7,q] : List ℕ).Pairwise (· ≤ ·) := by simp [hq.le]
    exact ((Nat.primeFactorsList_unique hprod hprime).eq_of_pairwise' hsort
      (Nat.primeFactorsList_sorted _).pairwise).symm
  have hne := hq.ne
  simp [OeisA67599.a,show ¬2401*q < 2 by omega,hf,List.dedup_cons,List.count_cons,
    hne,hne.symm,OeisA67599.concatenateNats]
  ring
