import FormalConjectures.ErdosProblems.«723»

-- Reduction Erdos723.erdos_723.variants.leq_11.R1 of Erdős Problem 723: The prime power conjecture. — leq 11
-- Credit: @avivorly
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1

open Configuration

-- A plane of order six would give this Boolean incidence matrix.
def H1 : Prop :=
  ∀ incidence : Fin 43 → Fin 43 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 7) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 7) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    False

-- A plane of order ten would give this Boolean incidence matrix.
def H2 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    False

lemma incidence_of_order {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    [ProjectivePlane P L] {n v : ℕ} (order_eq : ProjectivePlane.order P L = n)
    (size_eq : n ^ 2 + n + 1 = v) :
    ∃ incidence : Fin v → Fin v → Bool,
      (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = n + 1) ∧
      (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = n + 1) ∧
      (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) ∧
      (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) := by
  classical
  have point_count : Fintype.card P = v := by
    rw [ProjectivePlane.card_points (P := P) L, order_eq, size_eq]
  have line_count : Fintype.card L = v := by
    rw [ProjectivePlane.card_lines P (L := L), order_eq, size_eq]
  let pointIndex : P ≃ Fin v := Fintype.equivFinOfCardEq point_count
  let lineIndex : L ≃ Fin v := Fintype.equivFinOfCardEq line_count
  let incidence (l p : Fin v) : Bool := decide (pointIndex.symm p ∈ lineIndex.symm l)
  have incidence_iff (l p : Fin v) : incidence l p = true ↔ pointIndex.symm p ∈ lineIndex.symm l := by
    simp [incidence]
  refine ⟨incidence, ?_, ?_, ?_, ?_⟩
  · intro l
    let onLine := Finset.univ.filter fun p => incidence l p = true
    have equiv : (↑onLine : Type) ≃ {p : P // p ∈ lineIndex.symm l} :=
      pointIndex.symm.subtypeEquiv (fun p => by simp [onLine, incidence_iff])
    calc
      onLine.card = Fintype.card onLine := (Fintype.card_coe onLine).symm
      _ = Nat.card {p : P // p ∈ lineIndex.symm l} :=
        (Fintype.card_congr equiv).trans Nat.card_eq_fintype_card.symm
      _ = n + 1 := (ProjectivePlane.pointCount_eq P (lineIndex.symm l)).trans (by rw [order_eq])
  · intro p
    let throughPoint := Finset.univ.filter fun l => incidence l p = true
    have equiv : (↑throughPoint : Type) ≃ {l : L // pointIndex.symm p ∈ l} :=
      lineIndex.symm.subtypeEquiv (fun l => by simp [throughPoint, incidence_iff])
    calc
      throughPoint.card = Fintype.card throughPoint := (Fintype.card_coe throughPoint).symm
      _ = Nat.card {l : L // pointIndex.symm p ∈ l} :=
        (Fintype.card_congr equiv).trans Nat.card_eq_fintype_card.symm
      _ = n + 1 := (ProjectivePlane.lineCount_eq L (pointIndex.symm p)).trans (by rw [order_eq])
  · intro l m distinct
    obtain ⟨p, onBoth, unique⟩ := HasPoints.existsUnique_point P L (lineIndex.symm l)
      (lineIndex.symm m) (fun equal => distinct (lineIndex.symm.injective equal))
    refine ⟨pointIndex p, ?_, ?_⟩
    · simpa only [incidence_iff, Equiv.symm_apply_apply] using onBoth
    · intro q onBoth'
      apply pointIndex.symm.injective
      rw [Equiv.symm_apply_apply]
      exact unique _ ⟨(incidence_iff _ _).mp onBoth'.1, (incidence_iff _ _).mp onBoth'.2⟩
  · intro p q distinct
    obtain ⟨l, onBoth, unique⟩ := HasLines.existsUnique_line P L (pointIndex.symm p)
      (pointIndex.symm q) (fun equal => distinct (pointIndex.symm.injective equal))
    refine ⟨lineIndex l, ?_, ?_⟩
    · simpa only [incidence_iff, Equiv.symm_apply_apply] using onBoth
    · intro m onBoth'
      apply lineIndex.symm.injective
      rw [Equiv.symm_apply_apply]
      exact unique _ ⟨(incidence_iff _ _).mp onBoth'.1, (incidence_iff _ _).mp onBoth'.2⟩

lemma prime_power_or_exception (n : ℕ) (lower : 1 < n) (upper : n ≤ 11) :
    IsPrimePow n ∨ n = 6 ∨ n = 10 := by
  interval_cases n
  · exact Or.inl Nat.prime_two.isPrimePow
  · exact Or.inl Nat.prime_three.isPrimePow
  · exact Or.inl ((isPrimePow_nat_iff 4).mpr ⟨2, 2, Nat.prime_two, by decide, by decide⟩)
  · exact Or.inl Nat.prime_five.isPrimePow
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl Nat.prime_seven.isPrimePow
  · exact Or.inl ((isPrimePow_nat_iff 8).mpr ⟨2, 3, Nat.prime_two, by decide, by decide⟩)
  · exact Or.inl ((isPrimePow_nat_iff 9).mpr ⟨3, 2, Nat.prime_three, by decide, by decide⟩)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl Nat.prime_eleven.isPrimePow

theorem main : H1 → H2 → type_of% @Erdos723.erdos_723.variants.leq_11 := by
  intro noSix noTen P L membership points lines plane upper
  let : ProjectivePlane P L := plane
  rcases prime_power_or_exception _ (ProjectivePlane.one_lt_order P L) upper with
    primePower | orderSix | orderTen
  · exact primePower
  · obtain ⟨incidence, lineSizes, pointDegrees, linePairs, pointPairs⟩ :=
      incidence_of_order orderSix (v := 43) (by decide)
    exact (noSix incidence lineSizes pointDegrees linePairs pointPairs).elim
  · obtain ⟨incidence, lineSizes, pointDegrees, linePairs, pointPairs⟩ :=
      incidence_of_order orderTen (v := 111) (by decide)
    exact (noTen incidence lineSizes pointDegrees linePairs pointPairs).elim

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1
