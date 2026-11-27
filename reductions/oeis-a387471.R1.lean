import OMAStatements.S_oeis_a387471

-- Reduction oeis-a387471.R1 of A387471: a(n) = number of interior triple intersections for the equal-angle model with parameter m = 2*n-1.
-- Credit: @begcdn
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a387471_R1

open OMA.S_oeis_a387471

-- Every nonmedian solution has its three angles on the 3-degree grid.
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → ∀ t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1),
  ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 →
  ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) → (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))

-- Count all solutions with at least one median.
def H2 : Prop := ∀ n : ℕ, 1 ≤ n →
  Set.ncard {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) |
    ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)} = 6*n-5

-- Count the exceptional solutions on the fixed grid.
def H3 : Prop := ∀ n : ℕ, 1 ≤ n →
  Set.ncard {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) |
    ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) ∧
    (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))} = if 5 ∣ n then 12 else 0

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a387471.main := by
  intro hgrid hmed hex n hn
  let A : Set (Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)) :=
    {t | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)}
  let B : Set (Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)) :=
    {t | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) ∧ (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))}
  have hab : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro t ht hs
    exact hs.2.1 ht.2
  have heq : {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1} = A ∪ B := by
    ext t
    constructor
    · intro ht
      by_cases hm : (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)
      · exact Or.inl ⟨ht, hm⟩
      · exact Or.inr ⟨ht, hm, hgrid n hn t ht hm⟩
    · rintro (ht | ht)
      · exact ht.1
      · exact ht.1
  unfold d
  rw [heq, Set.ncard_union_eq hab]
  have ha : A.ncard = 6*n-5 := hmed n hn
  have hb : B.ncard = if 5 ∣ n then 12 else 0 := hex n hn
  rw [ha, hb]
  split <;> omega

end OMA.R_oeis_a387471_R1
