import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H2: hypothesis H2 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @marcusbuffett
-- H2 := ∀ (n : ℕ) (P : Finset ℝ²), P.card = n →     (∀ u ∈ distanceSet P, distanceMultiplicity P u ≤ n) →     ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤       (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2         else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4)  -- The open core: convex n-gons in which some distance occurs more than n times.

open Finset

private def gap (n x : ℕ) : ℝ := (x % n : ℕ) * ((n : ℝ) - (x % n : ℕ))

/-- The deficit x(n-x) is subadditive when the multiplicities are added modulo n. -/
private lemma gap_add (n x y : ℕ) (hn : 0 < n) : gap n (x+y) ≤ gap n x + gap n y := by
  let a := x % n
  let b := y % n
  have ha : a < n := Nat.mod_lt _ hn
  have hb : b < n := Nat.mod_lt _ hn
  have hab : (x+y)%n = (a+b)%n := Nat.add_mod _ _ _
  unfold gap
  rw [hab]
  change _ ≤ (a:ℝ)*(n-a) + (b:ℝ)*(n-b)
  by_cases h : a+b < n
  · rw [Nat.mod_eq_of_lt h, Nat.cast_add]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (Nat.cast_nonneg (α := ℝ) b)]
  · have H : (a+b)%n = a+b-n := by
      rw [Nat.mod_eq_sub_mod (by omega : n ≤ a+b), Nat.mod_eq_of_lt (by omega)]
    rw [H, Nat.cast_sub (by omega : n ≤ a+b), Nat.cast_add]
    have ha' : (a:ℝ) ≤ n := by exact_mod_cast ha.le
    have hb' : (b:ℝ) ≤ n := by exact_mod_cast hb.le
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')]

private lemma gap_sum {α : Type*} (s : Finset α) (f : α → ℕ) (n : ℕ) (hn : 0 < n) :
    gap n (∑ i ∈ s, f i) ≤ ∑ i ∈ s, gap n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gap]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (gap_add n _ _ hn).trans (add_le_add_right ih _)

private lemma capped_squares {α : Type*} (s : Finset α) (f : α → ℕ) (n : ℕ)
    (ht : ∑ i ∈ s, f i = n.choose 2) (hc : ∀ i ∈ s, f i ≤ n) :
    ∑ i ∈ s, (f i : ℝ)^2 ≤ if n%2 = 1 then (n:ℝ)^2*(n-1)/2 else (n:ℝ)^3/2-3*(n:ℝ)^2/4 := by
  classical
  by_cases hz : n = 0
  · subst n
    have hzero : ∀ i ∈ s, f i = 0 := fun i hi => Nat.eq_zero_of_le_zero (hc i hi)
    have hzsum : ∑ i ∈ s, (f i : ℝ)^2 = 0 := Finset.sum_eq_zero (fun i hi => by simp [hzero i hi])
    simp [hzsum]
  have H := gap_sum s f n (Nat.pos_of_ne_zero hz)
  rw [ht] at H
  have term (i : α) (hi : i ∈ s) :
      gap n (f i) = (n:ℝ)*f i - (f i:ℝ)^2 := by
    rcases (hc i hi).lt_or_eq with lt | eq
    · rw [gap, Nat.mod_eq_of_lt lt]; ring
    · rw [eq, gap]; simp; ring
  rw [Finset.sum_congr rfl term, sum_sub_distrib, ← Finset.mul_sum] at H
  have hsum : ∑ i ∈ s, (f i : ℝ) = (n:ℝ)*(n-1)/2 := by
    rw [← Nat.cast_sum, ht, Nat.cast_choose_two]
  rw [hsum] at H
  split_ifs with odd
  · have nonneg : 0 ≤ gap n (n.choose 2) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (Nat.mod_lt (n.choose 2) (Nat.pos_of_ne_zero hz)).le))
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2*(k+1) := ⟨n/2-1, by omega⟩
    let n := 2*(k+1)
    have hchoose : n.choose 2 = k*n+(k+1) := by
      apply Nat.cast_injective (R := ℝ)
      rw [Nat.cast_choose_two]
      dsimp [n]; push_cast; ring
    have rem : n.choose 2 % n = k+1 := by
      rw [hchoose, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by dsimp [n]; omega)]
    change gap n (n.choose 2) ≤ _ at H
    rw [gap, rem] at H
    dsimp [n] at H ⊢
    push_cast at H ⊢
    linarith

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  intro n P hcard hcap
  apply capped_squares _ _ _ _ hcap
  rw [sum_distanceMultiplicity, hcard]
