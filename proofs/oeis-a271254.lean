import OMAStatements.S_oeis_a271254

-- Problem: A271254: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 323, based on the 5-celled von Neumann neighborhood.
-- Upstream: formal-conjectures statements/oeis-a271254.lean:0 (declaration OMA.S_oeis_a271254.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OEISA271254Proof

open OMA.S_oeis_a271254 PowerSeries

private def step323 (f : ℤ → ℤ → Bool) (i j : ℤ) : Bool :=
  (323 : ℕ).testBit ((f i j).toNat + 2 * ((f (i + 1) j).toNat +
    (f (i - 1) j).toNat + (f i (j + 1)).toNat + (f i (j - 1)).toNat))

private def evenModel (m : ℕ) (i j : ℤ) : Bool :=
  let a := i.natAbs
  let b := j.natAbs
  decide ((a = 0 ∧ b ≤ m) ∨ (b = 0 ∧ a ≤ m) ∨ (a = 1 ∧ b = 1))

private def offPred (m : ℕ) (i j : ℤ) : Prop :=
  (i.natAbs = 0 ∧ j.natAbs ≤ m + 1) ∨
  (j.natAbs = 0 ∧ i.natAbs ≤ m + 1) ∨
  (i.natAbs = 1 ∧ j.natAbs ≤ m) ∨
  (j.natAbs = 1 ∧ i.natAbs ≤ m)

private instance (m : ℕ) (i j : ℤ) : Decidable (offPred m i j) := by
  unfold offPred
  infer_instance

private def oddModel (m : ℕ) (i j : ℤ) : Bool :=
  !decide (offPred m i j)

private lemma step323_neg_left (f : ℤ → ℤ → Bool) (hf : ∀ x y, f (-x) y = f x y) (i j : ℤ) :
    step323 f (-i) j = step323 f i j := by
  unfold step323
  have h1 : -i + 1 = -(i - 1) := by ring
  have h2 : -i - 1 = -(i + 1) := by ring
  rw [h1, h2, hf, hf, hf, hf, hf]
  congr 1
  omega

private lemma step323_neg_right (f : ℤ → ℤ → Bool) (hf : ∀ x y, f x (-y) = f x y) (i j : ℤ) :
    step323 f i (-j) = step323 f i j := by
  unfold step323
  have h1 : -j + 1 = -(j - 1) := by ring
  have h2 : -j - 1 = -(j + 1) := by ring
  rw [h1, h2, hf, hf, hf, hf, hf]
  congr 1
  omega

private lemma step323_swap (f : ℤ → ℤ → Bool) (hf : ∀ x y, f y x = f x y) (i j : ℤ) :
    step323 f j i = step323 f i j := by
  unfold step323
  rw [hf j i, hf (j + 1) i, hf (j - 1) i, hf j (i + 1), hf j (i - 1)]
  congr 1
  omega

private lemma evenModel_neg_left (m : ℕ) (i j : ℤ) : evenModel m (-i) j = evenModel m i j := by
  simp [evenModel]

private lemma evenModel_neg_right (m : ℕ) (i j : ℤ) : evenModel m i (-j) = evenModel m i j := by
  simp [evenModel]

private lemma evenModel_swap (m : ℕ) (i j : ℤ) : evenModel m j i = evenModel m i j := by
  unfold evenModel
  simp only [decide_eq_decide]
  tauto

private lemma oddModel_neg_left (m : ℕ) (i j : ℤ) : oddModel m (-i) j = oddModel m i j := by
  simp [oddModel, offPred]

private lemma oddModel_neg_right (m : ℕ) (i j : ℤ) : oddModel m i (-j) = oddModel m i j := by
  simp [oddModel, offPred]

private lemma oddModel_swap (m : ℕ) (i j : ℤ) : oddModel m j i = oddModel m i j := by
  unfold oddModel
  rw [Bool.not_inj_iff, decide_eq_decide]
  unfold offPred
  tauto

private lemma step_odd_to_even_nat (m : ℕ) (hm : 2 ≤ m) (a b : ℕ) (hab : a ≤ b) :
    step323 (oddModel m) (a : ℤ) (b : ℤ) = evenModel (m + 1) (a : ℤ) (b : ℤ) := by
  unfold step323 oddModel evenModel offPred
  have hnat : ∀ n : ℕ, ((n : ℤ)).natAbs = n := fun n => Int.natAbs_natCast n
  have hadd1 : ∀ n : ℕ, ((n : ℤ) + 1).natAbs = n + 1 := fun n => by
    exact_mod_cast Int.natAbs_natCast (n + 1)
  have hsub1 : ∀ n : ℕ, ((n : ℤ) - 1).natAbs = if n = 0 then 1 else n - 1 := fun n => by
    cases n with
    | zero => decide
    | succ k =>
      have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [this]
      simp
  simp only [hnat, hadd1, hsub1]
  have hm0 : m ≠ 0 := by omega
  have hm1 : 1 ≤ m := by omega
  rcases eq_or_ne a 0 with rfl | ha0
  · simp only [↓reduceIte]
    by_cases hb0 : b = 0
    · subst hb0; simp only [↓reduceIte]; have h1 : 0 ≤ m := by omega
      have h2 : 1 ≤ m := by omega
      have h3 : 0 ≤ m + 1 := by omega
      have h4 : 1 ≤ m + 1 := by omega
      simp [h1, h2, h3, h4]
    · simp only [hb0, ↓reduceIte]
      by_cases hb1 : b = 1
      · subst hb1; simp only [Nat.sub_self]
        have h1 : 1 ≤ m := by omega
        have h2 : 2 ≤ m + 1 := by omega
        have h3 : 1 ≤ m + 1 := by omega
        have h4 : 0 ≤ m + 1 := by omega
        simp [h1, h2, h3, h4]
      · by_cases hbm : b ≤ m
        · have h1 : b - 1 ≤ m + 1 := by omega
          have h2 : b ≤ m + 1 := by omega
          have h3 : b + 1 ≤ m + 1 := by omega
          have h4 : ¬ (b = 1) := hb1
          simp [hbm, h1, h2, h3, h4]
        · by_cases hbm1 : b = m + 1
          · subst hbm1
            have h1 : ¬ (m + 1 ≤ m) := by omega
            have h2 : ¬ (m + 1 + 1 ≤ m + 1) := by omega
            have h3 : m + 1 - 1 ≤ m + 1 := by omega
            have h4 : ¬ (m + 1 = 1) := by omega
            simp [hm0, hm1, hm, h1, h2, h3, h4]; decide
          · by_cases hbm2 : b = m + 2
            · subst hbm2
              have h1 : ¬ (m + 2 ≤ m) := by omega
              have h2 : ¬ (m + 2 ≤ m + 1) := by omega
              have h3 : ¬ (m + 2 + 1 ≤ m + 1) := by omega
              have h4 : m + 2 - 1 ≤ m + 1 := by omega
              have h5 : ¬ (m + 2 = 1) := by omega
              simp [hm0, hm1, hm, h1, h2, h3, h4, h5]; decide
            · have h1 : ¬ (b ≤ m) := by omega
              have h2 : ¬ (b ≤ m + 1) := by omega
              have h3 : ¬ (b + 1 ≤ m + 1) := by omega
              have h4 : ¬ (b - 1 ≤ m + 1) := by omega
              have h5 : ¬ (b = 1) := by omega
              have h6 : b ≠ 0 := by omega
              have h7 : b - 1 ≠ 0 := by omega
              have h8 : b ≠ 2 := by omega
              simp [hm0, hm1, hm, h1, h2, h3, h4, h5, h6, h7, h8]; decide
  · simp only [ha0, ↓reduceIte]
    have hb0 : b ≠ 0 := by omega
    simp only [hb0, ↓reduceIte]
    rcases eq_or_ne a 1 with rfl | ha1
    · by_cases hb1 : b = 1
      · subst hb1
        have h1 : 1 ≤ m := by omega
        have h2 : 2 ≤ m := by omega
        have h3 : 1 ≤ m + 1 := by omega
        have h4 : 0 ≤ m + 1 := by omega
        simp [h1, h2, h3, h4]
      · by_cases hbm1 : b ≤ m - 1
        · have h1 : b ≤ m := by omega
          have h2 : b + 1 ≤ m := by omega
          have h3 : b - 1 ≤ m := by omega
          have h4 : b ≤ m + 1 := by omega
          have h5 : ¬ (b = 1) := hb1
          have h6 : 2 ≤ b := by omega
          simp [hm0, hm1, hm, h1, h2, h3, h4, h5, h6]; decide
        · by_cases hbm : b = m
          · subst hbm
            have h1 : ¬ (b + 1 ≤ b) := by omega
            have h2 : b - 1 ≤ b := by omega
            have h3 : b ≤ b + 1 := by omega
            have h4 : ¬ (b = 1) := by omega
            have h5 : 1 ≤ b := by omega
            have h6 : 2 ≤ b := hm
            simp [hm0, h1, h2, h3, h4, h5, h6]; decide
          · by_cases hbm1' : b = m + 1
            · subst hbm1'
              have h1 : ¬ (m + 1 ≤ m) := by omega
              have h2 : ¬ (m + 1 + 1 ≤ m) := by omega
              have h3 : m + 1 - 1 ≤ m := by omega
              have h4 : ¬ (m + 1 = 1) := by omega
              simp [hm0, hm1, hm, h1, h2, h3, h4]; decide
            · have h1 : ¬ (b ≤ m) := by omega
              have h2 : ¬ (b + 1 ≤ m) := by omega
              have h3 : ¬ (b - 1 ≤ m) := by omega
              have h4 : ¬ (b ≤ m + 1) := by omega
              have h5 : ¬ (b = 1) := by omega
              have h6 : 1 ≤ b := by omega
              have h7 : 2 ≤ b := by omega
              have h8 : b - 1 ≠ 0 := by omega
              have h9 : b ≠ 2 := by omega
              simp [hm0, hm1, hm, hb0, h1, h2, h3, h4, h5, h6, h7, h8, h9]; decide
    · rcases eq_or_ne a 2 with rfl | ha2
      · have hb1 : b ≠ 1 := by omega
        have hb1ge : 1 ≤ b := by omega
        have hb2ge : 2 ≤ b := by omega
        have hbm10 : b - 1 ≠ 0 := by omega
        by_cases hb2 : b = 2
        · subst hb2
          simp [hm0, hm1, hm]; decide
        · have hbm11 : b - 1 ≠ 1 := by omega
          by_cases hbm : b ≤ m
          · simp [hm0, hm1, hm, hb0, hb1, hb1ge, hb2ge, hbm10, hb2, hbm11, hbm]; decide
          · simp [hm0, hm1, hm, hb0, hb1, hb1ge, hb2ge, hbm10, hb2, hbm11, hbm]; decide
      · have ha3 : 3 ≤ a := by omega
        have hb3 : 3 ≤ b := by omega
        have h1 : a - 1 ≠ 0 := by omega
        have h2 : a - 1 ≠ 1 := by omega
        have h3 : a + 1 ≠ 0 := by omega
        have h4 : a + 1 ≠ 1 := by omega
        have h5 : b - 1 ≠ 0 := by omega
        have h6 : b - 1 ≠ 1 := by omega
        have h7 : b + 1 ≠ 0 := by omega
        have h8 : b + 1 ≠ 1 := by omega
        have h9 : b ≠ 1 := by omega
        simp [ha0, ha1, hb0, h1, h2, h3, h4, h5, h6, h7, h8, h9]; decide

private lemma step_even_to_odd_nat (m : ℕ) (hm : 3 ≤ m) (a b : ℕ) (hab : a ≤ b) :
    step323 (evenModel m) (a : ℤ) (b : ℤ) = oddModel m (a : ℤ) (b : ℤ) := by
  unfold step323 oddModel evenModel offPred
  have hnat : ∀ n : ℕ, ((n : ℤ)).natAbs = n := fun n => Int.natAbs_natCast n
  have hadd1 : ∀ n : ℕ, ((n : ℤ) + 1).natAbs = n + 1 := fun n => by
    exact_mod_cast Int.natAbs_natCast (n + 1)
  have hsub1 : ∀ n : ℕ, ((n : ℤ) - 1).natAbs = if n = 0 then 1 else n - 1 := fun n => by
    cases n with
    | zero => decide
    | succ k =>
      have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [this]
      simp
  simp only [hnat, hadd1, hsub1]
  have hm0 : m ≠ 0 := by omega
  have hm1 : 1 ≤ m := by omega
  rcases eq_or_ne a 0 with rfl | ha0
  · simp only [↓reduceIte]
    by_cases hb0 : b = 0
    · subst hb0
      have h1 : 1 ≤ m := by omega
      simp [h1]; decide
    · simp only [hb0, ↓reduceIte]
      by_cases hb1 : b = 1
      · subst hb1
        have h1 : 1 ≤ m := by omega
        have h2 : 2 ≤ m := by omega
        have h3 : 1 ≤ m + 1 := by omega
        simp [h1, h2, h3]; decide
      · by_cases hbm1 : b ≤ m - 1
        · have h1 : b ≤ m := by omega
          have h2 : b + 1 ≤ m := by omega
          have h3 : b - 1 ≤ m := by omega
          have h4 : b ≤ m + 1 := by omega
          simp [hb1, h1, h2, h3, h4]; decide
        · by_cases hbm : b = m
          · subst hbm
            have h1 : ¬ (b + 1 ≤ b) := by omega
            have h2 : b - 1 ≤ b := by omega
            have h3 : b ≤ b + 1 := by omega
            have h4 : ¬ (b = 1) := by omega
            simp [h1, h2, h3, h4]; decide
          · by_cases hbm1' : b = m + 1
            · subst hbm1'
              have h1 : ¬ (m + 1 ≤ m) := by omega
              have h2 : ¬ (m + 1 + 1 ≤ m) := by omega
              have h3 : m + 1 - 1 ≤ m := by omega
              have h4 : ¬ (m + 1 = 1) := by omega
              have h5 : m ≠ 0 := by omega
              simp [h1, h2, h3, h4, h5]; decide
            · have h1 : ¬ (b ≤ m) := by omega
              have h2 : ¬ (b + 1 ≤ m) := by omega
              have h3 : ¬ (b - 1 ≤ m) := by omega
              have h4 : ¬ (b ≤ m + 1) := by omega
              have h5 : b - 1 ≠ 0 := by omega
              simp [hb1, h1, h2, h3, h4, h5]
  · simp only [ha0, ↓reduceIte]
    have hb0 : b ≠ 0 := by omega
    simp only [hb0, ↓reduceIte]
    rcases eq_or_ne a 1 with rfl | ha1
    · by_cases hb1 : b = 1
      · subst hb1
        have h1 : 1 ≤ m := by omega
        simp [h1]; decide
      · by_cases hb2 : b = 2
        · subst hb2
          have h1 : 2 ≤ m := by omega
          simp [h1]; decide
        · by_cases hbm : b ≤ m
          · have h1 : b - 1 ≠ 1 := by omega
            have h2 : b + 1 ≠ 1 := by omega
            have h3 : b - 1 ≠ 0 := by omega
            simp [hb0, hb1, hbm, h1, h2, h3]; decide
          · have h1 : b - 1 ≠ 1 := by omega
            have h2 : b + 1 ≠ 1 := by omega
            have h3 : b - 1 ≠ 0 := by omega
            simp [hb0, hb1, hbm, h1, h2, h3]
    · have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := by omega
      have h1 : a - 1 ≠ 0 := by omega
      have h2 : a + 1 ≠ 0 := by omega
      have h3 : a + 1 ≠ 1 := by omega
      have h4 : b - 1 ≠ 0 := by omega
      have h5 : b + 1 ≠ 0 := by omega
      have h6 : b + 1 ≠ 1 := by omega
      have h7 : b ≠ 1 := by omega
      simp [ha0, ha1, hb0, h1, h2, h3, h4, h5, h6, h7]

private lemma step_odd_to_even (m : ℕ) (hm : 2 ≤ m) (i j : ℤ) :
    step323 (oddModel m) i j = evenModel (m + 1) i j := by
  have hi : step323 (oddModel m) i j = step323 (oddModel m) (i.natAbs : ℤ) (j.natAbs : ℤ) := by
    rcases Int.natAbs_eq i with h1 | h1 <;> rcases Int.natAbs_eq j with h2 | h2
    · conv_lhs => rw [h1, h2]
    · conv_lhs => rw [h1, h2]
      exact step323_neg_right _ (oddModel_neg_right m) _ _
    · conv_lhs => rw [h1, h2]
      exact step323_neg_left _ (oddModel_neg_left m) _ _
    · conv_lhs => rw [h1, h2]
      rw [step323_neg_left _ (oddModel_neg_left m), step323_neg_right _ (oddModel_neg_right m)]
  have hj : evenModel (m + 1) i j = evenModel (m + 1) (i.natAbs : ℤ) (j.natAbs : ℤ) := by
    simp only [evenModel, Int.natAbs_natCast]
  rw [hi, hj]
  rcases le_total i.natAbs j.natAbs with hab | hba
  · exact step_odd_to_even_nat m hm i.natAbs j.natAbs hab
  · rw [← step323_swap _ (oddModel_swap m), ← evenModel_swap]
    exact step_odd_to_even_nat m hm j.natAbs i.natAbs hba

private lemma step_even_to_odd (m : ℕ) (hm : 3 ≤ m) (i j : ℤ) :
    step323 (evenModel m) i j = oddModel m i j := by
  have hi : step323 (evenModel m) i j = step323 (evenModel m) (i.natAbs : ℤ) (j.natAbs : ℤ) := by
    rcases Int.natAbs_eq i with h1 | h1 <;> rcases Int.natAbs_eq j with h2 | h2
    · conv_lhs => rw [h1, h2]
    · conv_lhs => rw [h1, h2]
      exact step323_neg_right _ (evenModel_neg_right m) _ _
    · conv_lhs => rw [h1, h2]
      exact step323_neg_left _ (evenModel_neg_left m) _ _
    · conv_lhs => rw [h1, h2]
      rw [step323_neg_left _ (evenModel_neg_left m), step323_neg_right _ (evenModel_neg_right m)]
  have hj : oddModel m i j = oddModel m (i.natAbs : ℤ) (j.natAbs : ℤ) := by
    simp only [oddModel, offPred, Int.natAbs_natCast]
  rw [hi, hj]
  rcases le_total i.natAbs j.natAbs with hab | hba
  · exact step_even_to_odd_nat m hm i.natAbs j.natAbs hab
  · rw [← step323_swap _ (evenModel_swap m), ← oddModel_swap]
    exact step_even_to_odd_nat m hm j.natAbs i.natAbs hba

private lemma cell_lightcone (t : ℕ) (i j : ℤ) (h : t < i.natAbs + j.natAbs) :
    cell 323 t i j = decide (t % 2 = 1) := by
  induction t generalizing i j with
  | zero =>
    have : ¬ (i = 0 ∧ j = 0) := by omega
    simp [cell, this]
  | succ t ih =>
    simp only [cell]
    rw [ih i j (by omega), ih (i + 1) j (by omega), ih (i - 1) j (by omega),
      ih i (j + 1) (by omega), ih i (j - 1) (by omega)]
    have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hmod with ht | ht
    · have ht1 : (t + 1) % 2 = 1 := by omega
      simp [ht, ht1]
    · have ht1 : (t + 1) % 2 = 0 := by omega
      simp [ht, ht1]
      decide

private def model1 (i j : ℤ) : Bool :=
  !decide (i.natAbs + j.natAbs = 1)

private def model2 (i j : ℤ) : Bool :=
  decide (i.natAbs + j.natAbs ≤ 1)

private def model4 (i j : ℤ) : Bool :=
  decide ((i.natAbs = 0 ∧ j.natAbs ≤ 2) ∨ (j.natAbs = 0 ∧ i.natAbs ≤ 2))

private lemma cell_one_small :
    ∀ x ∈ Finset.Icc (-1 : ℤ) 1, ∀ y ∈ Finset.Icc (-1 : ℤ) 1,
      cell 323 1 x y = model1 x y := by
  decide

private lemma cell_one (i j : ℤ) : cell 323 1 i j = model1 i j := by
  by_cases h : 1 < i.natAbs + j.natAbs
  · rw [cell_lightcone 1 i j h]
    have hno : decide (i.natAbs + j.natAbs = 1) = false := decide_eq_false (by omega)
    simp [model1, hno]
  · exact cell_one_small i (Finset.mem_Icc.mpr (by omega)) j (Finset.mem_Icc.mpr (by omega))

private lemma step_one_to_two_small :
    ∀ x ∈ Finset.Icc (-2 : ℤ) 2, ∀ y ∈ Finset.Icc (-2 : ℤ) 2,
      step323 model1 x y = model2 x y := by
  decide

private lemma cell_two (i j : ℤ) : cell 323 2 i j = model2 i j := by
  by_cases h : 2 < i.natAbs + j.natAbs
  · rw [cell_lightcone 2 i j h]
    have hno : decide (i.natAbs + j.natAbs ≤ 1) = false := decide_eq_false (by omega)
    simp [model2, hno]
  · change step323 (cell 323 1) i j = model2 i j
    have h1 : cell 323 1 = model1 := funext fun x => funext fun y => cell_one x y
    rw [h1]
    exact step_one_to_two_small i (Finset.mem_Icc.mpr (by omega)) j (Finset.mem_Icc.mpr (by omega))

private lemma step_two_to_three_small :
    ∀ x ∈ Finset.Icc (-3 : ℤ) 3, ∀ y ∈ Finset.Icc (-3 : ℤ) 3,
      step323 model2 x y = oddModel 1 x y := by
  decide

private lemma cell_three (i j : ℤ) : cell 323 3 i j = oddModel 1 i j := by
  by_cases h : 3 < i.natAbs + j.natAbs
  · rw [cell_lightcone 3 i j h]
    have hno : decide (offPred 1 i j) = false := decide_eq_false (by unfold offPred; omega)
    simp [oddModel, hno]
  · change step323 (cell 323 2) i j = oddModel 1 i j
    have h2 : cell 323 2 = model2 := funext fun x => funext fun y => cell_two x y
    rw [h2]
    exact step_two_to_three_small i (Finset.mem_Icc.mpr (by omega)) j (Finset.mem_Icc.mpr (by omega))

private lemma step_three_to_four_small :
    ∀ x ∈ Finset.Icc (-4 : ℤ) 4, ∀ y ∈ Finset.Icc (-4 : ℤ) 4,
      step323 (oddModel 1) x y = model4 x y := by
  decide

private lemma cell_four (i j : ℤ) : cell 323 4 i j = model4 i j := by
  by_cases h : 4 < i.natAbs + j.natAbs
  · rw [cell_lightcone 4 i j h]
    have hno : ¬ ((i.natAbs = 0 ∧ j.natAbs ≤ 2) ∨ (j.natAbs = 0 ∧ i.natAbs ≤ 2)) := by omega
    rw [model4, decide_eq_false hno]
    decide
  · change step323 (cell 323 3) i j = model4 i j
    have h3 : cell 323 3 = oddModel 1 := funext fun x => funext fun y => cell_three x y
    rw [h3]
    exact step_three_to_four_small i (Finset.mem_Icc.mpr (by omega)) j (Finset.mem_Icc.mpr (by omega))

private lemma step_four_to_five_small :
    ∀ x ∈ Finset.Icc (-5 : ℤ) 5, ∀ y ∈ Finset.Icc (-5 : ℤ) 5,
      step323 model4 x y = oddModel 2 x y := by
  decide

private lemma cell_five (i j : ℤ) : cell 323 5 i j = oddModel 2 i j := by
  by_cases h : 5 < i.natAbs + j.natAbs
  · rw [cell_lightcone 5 i j h]
    have hno : decide (offPred 2 i j) = false := decide_eq_false (by unfold offPred; omega)
    simp [oddModel, hno]
  · change step323 (cell 323 4) i j = oddModel 2 i j
    have h4 : cell 323 4 = model4 := funext fun x => funext fun y => cell_four x y
    rw [h4]
    exact step_four_to_five_small i (Finset.mem_Icc.mpr (by omega)) j (Finset.mem_Icc.mpr (by omega))

private lemma cell_odd_even (m : ℕ) (hm : 2 ≤ m) :
    (∀ i j, cell 323 (2 * m + 1) i j = oddModel m i j) ∧
    (∀ i j, cell 323 (2 * m + 2) i j = evenModel (m + 1) i j) := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨cell_five, fun i j => ?_⟩
    change step323 (cell 323 5) i j = evenModel 3 i j
    have h5 : cell 323 5 = oddModel 2 := funext fun x => funext fun y => cell_five x y
    rw [h5]
    exact step_odd_to_even 2 (by omega) i j
  | succ m hm ih =>
    have hodd : ∀ i j, cell 323 (2 * (m + 1) + 1) i j = oddModel (m + 1) i j := by
      intro i j
      have heq : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
      rw [heq]
      change step323 (cell 323 (2 * m + 2)) i j = oddModel (m + 1) i j
      have hprev : cell 323 (2 * m + 2) = evenModel (m + 1) :=
        funext fun x => funext fun y => ih.2 x y
      rw [hprev]
      exact step_even_to_odd (m + 1) (by omega) i j
    refine ⟨hodd, fun i j => ?_⟩
    have heq : 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 := by omega
    rw [heq]
    change step323 (cell 323 (2 * (m + 1) + 1)) i j = evenModel (m + 1 + 1) i j
    have hprev : cell 323 (2 * (m + 1) + 1) = oddModel (m + 1) :=
      funext fun x => funext fun y => hodd x y
    rw [hprev]
    exact step_odd_to_even (m + 1) (by omega) i j

private lemma sum_indicator_Icc (N lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi < N) :
    (∑ j ∈ Finset.range N, if lo ≤ j ∧ j ≤ hi then (1 : ℕ) else 0) = hi - lo + 1 := by
  rw [Finset.sum_boole]
  have hfilt : (Finset.range N).filter (fun j => lo ≤ j ∧ j ≤ hi) = Finset.Icc lo hi := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  simp only [Nat.cast_id, hfilt, Nat.card_Icc]
  omega

private lemma offRow_sum (m t : ℕ) (hm : 2 ≤ m) (ht : t = 2 * m + 1) (i : ℕ) (hi : i < 2 * t + 1) :
    (∑ j ∈ Finset.range (2 * t + 1), if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) =
      if i = t then 2 * m + 3
      else if i = t - 1 ∨ i = t + 1 then 2 * m + 1
      else if (t - m ≤ i ∧ i ≤ t - 2) ∨ (t + 2 ≤ i ∧ i ≤ t + m) then 3
      else if i = t - (m + 1) ∨ i = t + (m + 1) then 1
      else 0 := by
  have hle1 : m + 1 ≤ t := by omega
  have hle2 : m ≤ t := by omega
  have hle3 : 1 ≤ t := by omega
  by_cases h0 : i = t
  · simp only [h0, ↓reduceIte]
    have hcongr : ∀ j ∈ Finset.range (2 * t + 1),
        (if offPred m ((t : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) =
        if t - (m + 1) ≤ j ∧ j ≤ t + (m + 1) then 1 else 0 := by
      intro j _; congr 1; simp only [offPred, sub_self, Int.natAbs_zero, true_and, eq_iff_iff]; omega
    rw [Finset.sum_congr rfl hcongr, sum_indicator_Icc _ (t - (m + 1)) (t + (m + 1)) (by omega) (by omega)]
    omega
  · simp only [h0, ↓reduceIte]
    by_cases h1 : i = t - 1 ∨ i = t + 1
    · simp only [h1, ↓reduceIte]
      have hcongr : ∀ j ∈ Finset.range (2 * t + 1),
          (if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) =
          if t - m ≤ j ∧ j ≤ t + m then 1 else 0 := by
        intro j _
        have ha : ((i : ℤ) - t).natAbs = 1 := by omega
        have hiff : offPred m ((i : ℤ) - t) ((j : ℤ) - t) ↔ t - m ≤ j ∧ j ≤ t + m := by
          unfold offPred
          have hsub : t - m = m + 1 := by omega
          rw [ha, hsub]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> omega
          · intro h
            right; right; left
            exact ⟨rfl, by omega⟩
        simp only [hiff]
      rw [Finset.sum_congr rfl hcongr, sum_indicator_Icc _ (t - m) (t + m) (by omega) (by omega)]
      omega
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (t - m ≤ i ∧ i ≤ t - 2) ∨ (t + 2 ≤ i ∧ i ≤ t + m)
      · simp only [h2, ↓reduceIte]
        have hcongr : ∀ j ∈ Finset.range (2 * t + 1),
            (if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) =
            if t - 1 ≤ j ∧ j ≤ t + 1 then 1 else 0 := by
          intro j _
          have ha2 : 2 ≤ ((i : ℤ) - t).natAbs ∧ ((i : ℤ) - t).natAbs ≤ m := by omega
          congr 1; simp only [offPred, eq_iff_iff]; omega
        rw [Finset.sum_congr rfl hcongr, sum_indicator_Icc _ (t - 1) (t + 1) (by omega) (by omega)]
        omega
      · simp only [h2, ↓reduceIte]
        by_cases h3 : i = t - (m + 1) ∨ i = t + (m + 1)
        · simp only [h3, ↓reduceIte]
          have hcongr : ∀ j ∈ Finset.range (2 * t + 1),
              (if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) =
              if t ≤ j ∧ j ≤ t then 1 else 0 := by
            intro j _
            have ha3 : ((i : ℤ) - t).natAbs = m + 1 := by omega
            congr 1; simp only [offPred, ha3, eq_iff_iff]; omega
          rw [Finset.sum_congr rfl hcongr, sum_indicator_Icc _ t t (by omega) (by omega)]
          omega
        · simp only [h3, ↓reduceIte]
          refine Finset.sum_eq_zero fun j _ => ?_
          have ha4 : m + 2 ≤ ((i : ℤ) - t).natAbs := by omega
          have hno : ¬ offPred m ((i : ℤ) - t) ((j : ℤ) - t) := by
            unfold offPred; omega
          simp [hno]

private lemma onCount_odd (m : ℕ) (hm : 2 ≤ m) :
    onCount 323 (2 * m + 1) = 16 * m ^ 2 + 12 * m + 8 := by
  set t := 2 * m + 1 with ht_def
  have hcell : ∀ i j, cell 323 t i j = oddModel m i j := (cell_odd_even m hm).1
  have hsum_add :
      onCount 323 t +
        ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
          (if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) =
      (2 * t + 1) * (2 * t + 1) := by
    unfold onCount
    rw [← Finset.sum_add_distrib]
    have hinner : ∀ i ∈ Finset.range (2 * t + 1),
        (∑ j ∈ Finset.range (2 * t + 1), if cell 323 t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) +
        (∑ j ∈ Finset.range (2 * t + 1), if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) =
        2 * t + 1 := by
      intro i _
      rw [← Finset.sum_add_distrib]
      have h1 : ∀ j ∈ Finset.range (2 * t + 1),
          (if cell 323 t ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) +
          (if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) = 1 := by
        intro j _
        rw [hcell]
        unfold oddModel
        by_cases hp : offPred m ((i : ℤ) - t) ((j : ℤ) - t) <;> simp [hp]
      rw [Finset.sum_congr rfl h1]
      simp
    rw [Finset.sum_congr rfl hinner]
    simp
  have hoff :
      (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
          if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) =
      12 * m + 1 := by
    have hrow : ∀ i ∈ Finset.range (2 * t + 1),
        (∑ j ∈ Finset.range (2 * t + 1), if offPred m ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℕ) else 0) =
        (if t ≤ i ∧ i ≤ t then 2 * m + 3 else 0) +
        (if t - 1 ≤ i ∧ i ≤ t - 1 then 2 * m + 1 else 0) +
        (if t + 1 ≤ i ∧ i ≤ t + 1 then 2 * m + 1 else 0) +
        (if t - m ≤ i ∧ i ≤ t - 2 then 3 else 0) +
        (if t + 2 ≤ i ∧ i ≤ t + m then 3 else 0) +
        (if t - (m + 1) ≤ i ∧ i ≤ t - (m + 1) then 1 else 0) +
        (if t + (m + 1) ≤ i ∧ i ≤ t + (m + 1) then 1 else 0) := by
      intro i hi
      rw [offRow_sum m t hm ht_def i (Finset.mem_range.mp hi)]
      by_cases c0 : i = t
      · subst c0
        have f1 : ¬ (t - 1 ≤ t ∧ t ≤ t - 1) := by omega
        have f2 : ¬ (t + 1 ≤ t ∧ t ≤ t + 1) := by omega
        have f3 : ¬ (t - m ≤ t ∧ t ≤ t - 2) := by omega
        have f4 : ¬ (t + 2 ≤ t ∧ t ≤ t + m) := by omega
        have f5 : ¬ (t - (m + 1) ≤ t ∧ t ≤ t - (m + 1)) := by omega
        have f6 : ¬ (t + (m + 1) ≤ t ∧ t ≤ t + (m + 1)) := by omega
        rw [if_pos rfl, if_pos ⟨le_refl t, le_refl t⟩,
          if_neg f1, if_neg f2, if_neg f3, if_neg f4, if_neg f5, if_neg f6]
      · by_cases c1a : i = t - 1
        · subst c1a
          have f0 : ¬ (t ≤ t - 1 ∧ t - 1 ≤ t) := by omega
          have f2 : ¬ (t + 1 ≤ t - 1 ∧ t - 1 ≤ t + 1) := by omega
          have f3 : ¬ (t - m ≤ t - 1 ∧ t - 1 ≤ t - 2) := by omega
          have f4 : ¬ (t + 2 ≤ t - 1 ∧ t - 1 ≤ t + m) := by omega
          have f5 : ¬ (t - (m + 1) ≤ t - 1 ∧ t - 1 ≤ t - (m + 1)) := by omega
          have f6 : ¬ (t + (m + 1) ≤ t - 1 ∧ t - 1 ≤ t + (m + 1)) := by omega
          have hl : t - 1 = t - 1 ∨ t - 1 = t + 1 := Or.inl rfl
          rw [if_neg c0, if_pos hl, if_neg f0, if_pos ⟨le_refl _, le_refl _⟩,
            if_neg f2, if_neg f3, if_neg f4, if_neg f5, if_neg f6]
          omega
        · by_cases c1b : i = t + 1
          · subst c1b
            have f0 : ¬ (t ≤ t + 1 ∧ t + 1 ≤ t) := by omega
            have f1 : ¬ (t - 1 ≤ t + 1 ∧ t + 1 ≤ t - 1) := by omega
            have f3 : ¬ (t - m ≤ t + 1 ∧ t + 1 ≤ t - 2) := by omega
            have f4 : ¬ (t + 2 ≤ t + 1 ∧ t + 1 ≤ t + m) := by omega
            have f5 : ¬ (t - (m + 1) ≤ t + 1 ∧ t + 1 ≤ t - (m + 1)) := by omega
            have f6 : ¬ (t + (m + 1) ≤ t + 1 ∧ t + 1 ≤ t + (m + 1)) := by omega
            have hl : t + 1 = t - 1 ∨ t + 1 = t + 1 := Or.inr rfl
            rw [if_neg c0, if_pos hl, if_neg f0, if_neg f1, if_pos ⟨le_refl _, le_refl _⟩,
              if_neg f3, if_neg f4, if_neg f5, if_neg f6]
            omega
          · have nc1 : ¬ (i = t - 1 ∨ i = t + 1) := by omega
            by_cases c2a : t - m ≤ i ∧ i ≤ t - 2
            · have f0 : ¬ (t ≤ i ∧ i ≤ t) := by omega
              have f1 : ¬ (t - 1 ≤ i ∧ i ≤ t - 1) := by omega
              have f2 : ¬ (t + 1 ≤ i ∧ i ≤ t + 1) := by omega
              have f4 : ¬ (t + 2 ≤ i ∧ i ≤ t + m) := by omega
              have f5 : ¬ (t - (m + 1) ≤ i ∧ i ≤ t - (m + 1)) := by omega
              have f6 : ¬ (t + (m + 1) ≤ i ∧ i ≤ t + (m + 1)) := by omega
              have hl : (t - m ≤ i ∧ i ≤ t - 2) ∨ (t + 2 ≤ i ∧ i ≤ t + m) := Or.inl c2a
              rw [if_neg c0, if_neg nc1, if_pos hl, if_neg f0, if_neg f1, if_neg f2,
                if_pos c2a, if_neg f4, if_neg f5, if_neg f6]
            · by_cases c2b : t + 2 ≤ i ∧ i ≤ t + m
              · have f0 : ¬ (t ≤ i ∧ i ≤ t) := by omega
                have f1 : ¬ (t - 1 ≤ i ∧ i ≤ t - 1) := by omega
                have f2 : ¬ (t + 1 ≤ i ∧ i ≤ t + 1) := by omega
                have f5 : ¬ (t - (m + 1) ≤ i ∧ i ≤ t - (m + 1)) := by omega
                have f6 : ¬ (t + (m + 1) ≤ i ∧ i ≤ t + (m + 1)) := by omega
                have hl : (t - m ≤ i ∧ i ≤ t - 2) ∨ (t + 2 ≤ i ∧ i ≤ t + m) := Or.inr c2b
                rw [if_neg c0, if_neg nc1, if_pos hl, if_neg f0, if_neg f1, if_neg f2,
                  if_neg c2a, if_pos c2b, if_neg f5, if_neg f6]
              · have nc2 : ¬ ((t - m ≤ i ∧ i ≤ t - 2) ∨ (t + 2 ≤ i ∧ i ≤ t + m)) := by tauto
                by_cases c3a : i = t - (m + 1)
                · subst c3a
                  have f0 : ¬ (t ≤ t - (m + 1) ∧ t - (m + 1) ≤ t) := by omega
                  have f1 : ¬ (t - 1 ≤ t - (m + 1) ∧ t - (m + 1) ≤ t - 1) := by omega
                  have f2 : ¬ (t + 1 ≤ t - (m + 1) ∧ t - (m + 1) ≤ t + 1) := by omega
                  have f6 : ¬ (t + (m + 1) ≤ t - (m + 1) ∧ t - (m + 1) ≤ t + (m + 1)) := by omega
                  have hl : t - (m + 1) = t - (m + 1) ∨ t - (m + 1) = t + (m + 1) := Or.inl rfl
                  rw [if_neg c0, if_neg nc1, if_neg nc2, if_pos hl, if_neg f0, if_neg f1, if_neg f2,
                    if_neg c2a, if_neg c2b, if_pos ⟨le_refl _, le_refl _⟩, if_neg f6]
                · by_cases c3b : i = t + (m + 1)
                  · subst c3b
                    have f0 : ¬ (t ≤ t + (m + 1) ∧ t + (m + 1) ≤ t) := by omega
                    have f1 : ¬ (t - 1 ≤ t + (m + 1) ∧ t + (m + 1) ≤ t - 1) := by omega
                    have f2 : ¬ (t + 1 ≤ t + (m + 1) ∧ t + (m + 1) ≤ t + 1) := by omega
                    have f5 : ¬ (t - (m + 1) ≤ t + (m + 1) ∧ t + (m + 1) ≤ t - (m + 1)) := by omega
                    have hl : t + (m + 1) = t - (m + 1) ∨ t + (m + 1) = t + (m + 1) := Or.inr rfl
                    rw [if_neg c0, if_neg nc1, if_neg nc2, if_pos hl, if_neg f0, if_neg f1, if_neg f2,
                      if_neg c2a, if_neg c2b, if_neg f5, if_pos ⟨le_refl _, le_refl _⟩]
                  · have nc3 : ¬ (i = t - (m + 1) ∨ i = t + (m + 1)) := by omega
                    have f0 : ¬ (t ≤ i ∧ i ≤ t) := by omega
                    have f1 : ¬ (t - 1 ≤ i ∧ i ≤ t - 1) := by omega
                    have f2 : ¬ (t + 1 ≤ i ∧ i ≤ t + 1) := by omega
                    have f5 : ¬ (t - (m + 1) ≤ i ∧ i ≤ t - (m + 1)) := by omega
                    have f6 : ¬ (t + (m + 1) ≤ i ∧ i ≤ t + (m + 1)) := by omega
                    rw [if_neg c0, if_neg nc1, if_neg nc2, if_neg nc3, if_neg f0, if_neg f1, if_neg f2,
                      if_neg c2a, if_neg c2b, if_neg f5, if_neg f6]
    rw [Finset.sum_congr rfl hrow]
    simp only [Finset.sum_add_distrib]
    have hscale : ∀ (lo hi c : ℕ), lo ≤ hi → hi < 2 * t + 1 →
        (∑ i ∈ Finset.range (2 * t + 1), if lo ≤ i ∧ i ≤ hi then c else 0) = (hi - lo + 1) * c := by
      intro lo hi c hlo hhi
      have h1 : ∀ i ∈ Finset.range (2 * t + 1),
          (if lo ≤ i ∧ i ≤ hi then c else 0) = (if lo ≤ i ∧ i ≤ hi then 1 else 0) * c := by
        intro i _; split_ifs <;> simp
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, sum_indicator_Icc _ lo hi hlo hhi]
    rw [hscale t t (2 * m + 3) (by omega) (by omega),
      hscale (t - 1) (t - 1) (2 * m + 1) (by omega) (by omega),
      hscale (t + 1) (t + 1) (2 * m + 1) (by omega) (by omega),
      hscale (t - m) (t - 2) 3 (by omega) (by omega),
      hscale (t + 2) (t + m) 3 (by omega) (by omega),
      hscale (t - (m + 1)) (t - (m + 1)) 1 (by omega) (by omega),
      hscale (t + (m + 1)) (t + (m + 1)) 1 (by omega) (by omega)]
    have hs1 : t - 2 - (t - m) + 1 = m - 1 := by omega
    have hs2 : t + m - (t + 2) + 1 = m - 1 := by omega
    simp only [Nat.sub_self, zero_add, one_mul, hs1, hs2]
    omega
  rw [hoff] at hsum_add
  have hsq : (2 * t + 1) * (2 * t + 1) = (16 * m ^ 2 + 12 * m + 8) + (12 * m + 1) := by
    rw [ht_def]; ring
  omega

private lemma a_init :
    a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 36 ∧ a 3 = 188 ∧ a 4 = 876 := by
  have h0 : a 0 = 1 := by decide
  have h1 : a 1 = 5 := by
    unfold a onCount
    have hpow : 2 ^ 1 - 1 = 1 := by norm_num
    rw [hpow]
    simp_rw [cell_one]
    decide
  have h2 : a 2 = 36 := by
    unfold a onCount
    have hpow : 2 ^ 2 - 1 = 3 := by norm_num
    rw [hpow]
    simp_rw [cell_three]
    decide
  have h3 : a 3 = 188 := by
    unfold a
    have : 2 ^ 3 - 1 = 2 * 3 + 1 := by norm_num
    rw [this, onCount_odd 3 (by omega)]
    norm_num
  have h4 : a 4 = 876 := by
    unfold a
    have : 2 ^ 4 - 1 = 2 * 7 + 1 := by norm_num
    rw [this, onCount_odd 7 (by omega)]
    norm_num
  exact ⟨h0, h1, h2, h3, h4⟩

private lemma a_closed (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = 4 * (4 : ℚ) ^ n - 10 * (2 : ℚ) ^ n + 12 := by
  by_cases hn2 : n = 2
  · subst hn2
    have h2 : a 2 = 36 := a_init.2.2.1
    rw [h2]; norm_num
  · have hn3 : 3 ≤ n := by omega
    set m := 2 ^ (n - 1) - 1 with hm_def
    have hpow : 4 ≤ 2 ^ (n - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm2 : 2 ≤ m := by omega
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      have : n = (n - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have ht : 2 ^ n - 1 = 2 * m + 1 := by omega
    unfold a
    rw [ht, onCount_odd m hm2]
    push_cast
    have hmQ : (m : ℚ) = (2 : ℚ) ^ (n - 1) - 1 := by
      have h1 : 1 ≤ 2 ^ (n - 1) := by omega
      rw [hm_def, Nat.cast_sub h1]
      push_cast
      rfl
    have h2Q : (2 : ℚ) ^ n = 2 * (2 : ℚ) ^ (n - 1) := by
      have : n = (n - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have h4Q : (4 : ℚ) ^ n = 4 * ((2 : ℚ) ^ (n - 1)) ^ 2 := by
      have h42 : (4 : ℚ) ^ n = ((2 : ℚ) ^ n) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h42, h2Q]; ring
    rw [hmQ, h2Q, h4Q]
    ring

end OEISA271254Proof

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a271254.main := by
  have hclosed := OEISA271254Proof.a_closed
  have hrec : ∀ n : ℕ, 5 ≤ n →
      (OMA.S_oeis_a271254.a n : ℚ) =
        7 * OMA.S_oeis_a271254.a (n - 1) - 14 * OMA.S_oeis_a271254.a (n - 2) +
        8 * OMA.S_oeis_a271254.a (n - 3) := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h0 : 5 + k - 1 = 4 + k := by omega
    have h1 : 5 + k - 2 = 3 + k := by omega
    have h2 : 5 + k - 3 = 2 + k := by omega
    rw [h0, h1, h2, hclosed (5 + k) (by omega), hclosed (4 + k) (by omega),
      hclosed (3 + k) (by omega), hclosed (2 + k) (by omega)]
    have hp4 : ∀ j, (4 : ℚ) ^ (j + k) = (4 : ℚ) ^ j * (4 : ℚ) ^ k := fun j => pow_add 4 j k
    have hp2 : ∀ j, (2 : ℚ) ^ (j + k) = (2 : ℚ) ^ j * (2 : ℚ) ^ k := fun j => pow_add 2 j k
    rw [hp4 5, hp4 4, hp4 3, hp4 2, hp2 5, hp2 4, hp2 3, hp2 2]
    ring
  refine ⟨hclosed, hrec, ?_⟩
  have hfac : ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) =
      1 - C 7 * X ^ 1 + C 14 * X ^ 2 - C 8 * X ^ 3 := by
    simp only [map_ofNat, pow_one]
    ring
  have hrhs : (1 - 2 * X + 15 * X ^ 2 - 2 * X ^ 3 + 24 * X ^ 4 : PowerSeries ℚ) =
      C 1 * X ^ 0 - C 2 * X ^ 1 + C 15 * X ^ 2 - C 2 * X ^ 3 + C 24 * X ^ 4 := by
    simp only [map_ofNat, map_one, pow_zero, pow_one, mul_one, one_mul]
  rw [hfac, hrhs]
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (OMA.S_oeis_a271254.a n : ℚ))
  have hmul : A * (1 - C 7 * X ^ 1 + C 14 * X ^ 2 - C 8 * X ^ 3) =
      A - C 7 * (A * X ^ 1) + C 14 * (A * X ^ 2) - C 8 * (A * X ^ 3) := by
    ring
  rw [hmul]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_mk, A]
  by_cases hn5 : 5 ≤ n
  · have h0 : 0 ≤ n := by omega
    have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have hne0 : n - 0 ≠ 0 := by omega
    have hne1 : n - 1 ≠ 0 := by omega
    have hne2 : n - 2 ≠ 0 := by omega
    have hne3 : n - 3 ≠ 0 := by omega
    have hne4 : n - 4 ≠ 0 := by omega
    simp only [h0, h1, h2, h3, h4, hne0, hne1, hne2, hne3, hne4, ↓reduceIte]
    linarith [hrec n hn5]
  · obtain ⟨h0, h1, h2, h3, h4⟩ := OEISA271254Proof.a_init
    have hlt : n < 5 := by omega
    interval_cases n <;> simp [h0, h1, h2, h3, h4] <;> norm_num
