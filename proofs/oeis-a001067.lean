import OMAStatements.S_oeis_a001067
import Mathlib

open OMA.S_oeis_a001067

/- Values of the Bernoulli numbers needed to reach `B 20`. -/

@[simp] lemma bn0 : bernoulli' 0 = (1 : ℚ) := by
  rw [bernoulli'_def]; simp

@[simp] lemma bn1 : bernoulli' 1 = (1 / 2 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn2 : bernoulli' 2 = (1 / 6 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn3 : bernoulli' 3 = (0 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn4 : bernoulli' 4 = (-1 / 30 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn5 : bernoulli' 5 = (0 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn6 : bernoulli' 6 = (1 / 42 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn7 : bernoulli' 7 = (0 : ℚ) :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[simp] lemma bn8 : bernoulli' 8 = (-1 / 30 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn9 : bernoulli' 9 = (0 : ℚ) :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[simp] lemma bn10 : bernoulli' 10 = (5 / 66 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn11 : bernoulli' 11 = (0 : ℚ) :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[simp] lemma bn12 : bernoulli' 12 = (-691 / 2730 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn13 : bernoulli' 13 = (0 : ℚ) :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[simp] lemma bn14 : bernoulli' 14 = (7 / 6 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn15 : bernoulli' 15 = (0 : ℚ) :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[simp] lemma bn16 : bernoulli' 16 = (-3617 / 510 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn17 : bernoulli' 17 = (0 : ℚ) :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[simp] lemma bn18 : bernoulli' 18 = (43867 / 798 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

@[simp] lemma bn19 : bernoulli' 19 = (0 : ℚ) :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

lemma bn20 : bernoulli' 20 = (-174611 / 330 : ℚ) := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

lemma bernoulli_twenty : bernoulli 20 = (-174611 / 330 : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bn20

lemma absNumerator_ten : absNumerator 10 = 174611 := by
  rw [absNumerator, bernoulli_twenty]
  norm_num

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001067.main) := by
  intro h
  have hcase := h 10 (by decide)
  rw [absNumerator_ten] at hcase
  rcases hcase with h1 | hp
  · norm_num at h1
  · norm_num at hp
