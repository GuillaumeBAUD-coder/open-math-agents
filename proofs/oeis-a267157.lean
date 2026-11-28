import OMAStatements.S_oeis_a267157
import Mathlib

namespace A267157Aux

def p0 (i : ℤ) : Bool :=
  decide (i = 0)

lemma far0 (i : ℤ) (h : i < -0 ∨ 0 < i) : p0 i = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega
def p1 (i : ℤ) : Bool :=
  decide (¬((0 ≤ i ∧ i ≤ 1)))

lemma far1 (i : ℤ) (h : i < -1 ∨ 1 < i) : p1 i = true := by
  simp only [p1, decide_eq_true_eq]
  omega
def p2 (i : ℤ) : Bool :=
  decide (i = -1 ∨ (1 ≤ i ∧ i ≤ 2))

lemma far2 (i : ℤ) (h : i < -2 ∨ 2 < i) : p2 i = false := by
  simp only [p2, decide_eq_false_iff_not]
  omega
def p3 (i : ℤ) : Bool :=
  decide (¬(i = -1 ∨ i = 3))

lemma far3 (i : ℤ) (h : i < -3 ∨ 3 < i) : p3 i = true := by
  simp only [p3, decide_eq_true_eq]
  omega
def p4 (i : ℤ) : Bool :=
  decide ((-2 ≤ i ∧ i ≤ 0) ∨ (2 ≤ i ∧ i ≤ 4))

lemma far4 (i : ℤ) (h : i < -4 ∨ 4 < i) : p4 i = false := by
  simp only [p4, decide_eq_false_iff_not]
  omega
def p5 (i : ℤ) : Bool :=
  decide (¬(i = -1 ∨ i = 3 ∨ i = 5))

lemma far5 (i : ℤ) (h : i < -5 ∨ 5 < i) : p5 i = true := by
  simp only [p5, decide_eq_true_eq]
  omega
def p6 (i : ℤ) : Bool :=
  decide ((-2 ≤ i ∧ i ≤ 0) ∨ (2 ≤ i ∧ i ≤ 3) ∨ (5 ≤ i ∧ i ≤ 6))

lemma far6 (i : ℤ) (h : i < -6 ∨ 6 < i) : p6 i = false := by
  simp only [p6, decide_eq_false_iff_not]
  omega
def p7 (i : ℤ) : Bool :=
  decide (¬(i = -1 ∨ i = 7))

lemma far7 (i : ℤ) (h : i < -7 ∨ 7 < i) : p7 i = true := by
  simp only [p7, decide_eq_true_eq]
  omega
def p8 (i : ℤ) : Bool :=
  decide ((-2 ≤ i ∧ i ≤ 0) ∨ (6 ≤ i ∧ i ≤ 8))

lemma far8 (i : ℤ) (h : i < -8 ∨ 8 < i) : p8 i = false := by
  simp only [p8, decide_eq_false_iff_not]
  omega
def p9 (i : ℤ) : Bool :=
  decide (¬(i = -1 ∨ i = 1 ∨ i = 7 ∨ i = 9))

lemma far9 (i : ℤ) (h : i < -9 ∨ 9 < i) : p9 i = true := by
  simp only [p9, decide_eq_true_eq]
  omega
def p10 (i : ℤ) : Bool :=
  decide ((-2 ≤ i ∧ i ≤ -1) ∨ (1 ≤ i ∧ i ≤ 2) ∨ (6 ≤ i ∧ i ≤ 7) ∨ (9 ≤ i ∧ i ≤ 10))

lemma far10 (i : ℤ) (h : i < -10 ∨ 10 < i) : p10 i = false := by
  simp only [p10, decide_eq_false_iff_not]
  omega

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox0 : ∀ i ∈ box1, p1 i = Nat.testBit 107 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  decide

lemma tr0 (i : ℤ) : p1 i = Nat.testBit 107 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  by_cases h : -1 ≤ i ∧ i ≤ 1
  · exact trbox0 i (mem_box1 i h.1 h.2)
  · rw [far1 i (by omega), far0 (i - 1) (by omega), far0 i (by omega), far0 (i + 1) (by omega)]
    decide

def box2 : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_box2 (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ box2 := by
  unfold box2
  simp
  omega

lemma trbox1 : ∀ i ∈ box2, p2 i = Nat.testBit 107 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  decide

lemma tr1 (i : ℤ) : p2 i = Nat.testBit 107 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  by_cases h : -2 ≤ i ∧ i ≤ 2
  · exact trbox1 i (mem_box2 i h.1 h.2)
  · rw [far2 i (by omega), far1 (i - 1) (by omega), far1 i (by omega), far1 (i + 1) (by omega)]
    decide

def box3 : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_box3 (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ box3 := by
  unfold box3
  simp
  omega

lemma trbox2 : ∀ i ∈ box3, p3 i = Nat.testBit 107 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  decide

lemma tr2 (i : ℤ) : p3 i = Nat.testBit 107 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  by_cases h : -3 ≤ i ∧ i ≤ 3
  · exact trbox2 i (mem_box3 i h.1 h.2)
  · rw [far3 i (by omega), far2 (i - 1) (by omega), far2 i (by omega), far2 (i + 1) (by omega)]
    decide

def box4 : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

lemma mem_box4 (x : ℤ) (h1 : -4 ≤ x) (h2 : x ≤ 4) : x ∈ box4 := by
  unfold box4
  simp
  omega

lemma trbox3 : ∀ i ∈ box4, p4 i = Nat.testBit 107 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  decide

lemma tr3 (i : ℤ) : p4 i = Nat.testBit 107 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  by_cases h : -4 ≤ i ∧ i ≤ 4
  · exact trbox3 i (mem_box4 i h.1 h.2)
  · rw [far4 i (by omega), far3 (i - 1) (by omega), far3 i (by omega), far3 (i + 1) (by omega)]
    decide

def box5 : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

lemma mem_box5 (x : ℤ) (h1 : -5 ≤ x) (h2 : x ≤ 5) : x ∈ box5 := by
  unfold box5
  simp
  omega

lemma trbox4 : ∀ i ∈ box5, p5 i = Nat.testBit 107 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  decide

lemma tr4 (i : ℤ) : p5 i = Nat.testBit 107 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  by_cases h : -5 ≤ i ∧ i ≤ 5
  · exact trbox4 i (mem_box5 i h.1 h.2)
  · rw [far5 i (by omega), far4 (i - 1) (by omega), far4 i (by omega), far4 (i + 1) (by omega)]
    decide

def box6 : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6]

lemma mem_box6 (x : ℤ) (h1 : -6 ≤ x) (h2 : x ≤ 6) : x ∈ box6 := by
  unfold box6
  simp
  omega

lemma trbox5 : ∀ i ∈ box6, p6 i = Nat.testBit 107 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  decide

lemma tr5 (i : ℤ) : p6 i = Nat.testBit 107 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  by_cases h : -6 ≤ i ∧ i ≤ 6
  · exact trbox5 i (mem_box6 i h.1 h.2)
  · rw [far6 i (by omega), far5 (i - 1) (by omega), far5 i (by omega), far5 (i + 1) (by omega)]
    decide

def box7 : List ℤ := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7]

lemma mem_box7 (x : ℤ) (h1 : -7 ≤ x) (h2 : x ≤ 7) : x ∈ box7 := by
  unfold box7
  simp
  omega

lemma trbox6 : ∀ i ∈ box7, p7 i = Nat.testBit 107 (4 * (p6 (i - 1)).toNat + 2 * (p6 i).toNat + (p6 (i + 1)).toNat) := by
  decide

lemma tr6 (i : ℤ) : p7 i = Nat.testBit 107 (4 * (p6 (i - 1)).toNat + 2 * (p6 i).toNat + (p6 (i + 1)).toNat) := by
  by_cases h : -7 ≤ i ∧ i ≤ 7
  · exact trbox6 i (mem_box7 i h.1 h.2)
  · rw [far7 i (by omega), far6 (i - 1) (by omega), far6 i (by omega), far6 (i + 1) (by omega)]
    decide

def box8 : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]

lemma mem_box8 (x : ℤ) (h1 : -8 ≤ x) (h2 : x ≤ 8) : x ∈ box8 := by
  unfold box8
  simp
  omega

lemma trbox7 : ∀ i ∈ box8, p8 i = Nat.testBit 107 (4 * (p7 (i - 1)).toNat + 2 * (p7 i).toNat + (p7 (i + 1)).toNat) := by
  decide

lemma tr7 (i : ℤ) : p8 i = Nat.testBit 107 (4 * (p7 (i - 1)).toNat + 2 * (p7 i).toNat + (p7 (i + 1)).toNat) := by
  by_cases h : -8 ≤ i ∧ i ≤ 8
  · exact trbox7 i (mem_box8 i h.1 h.2)
  · rw [far8 i (by omega), far7 (i - 1) (by omega), far7 i (by omega), far7 (i + 1) (by omega)]
    decide

def box9 : List ℤ := [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

lemma mem_box9 (x : ℤ) (h1 : -9 ≤ x) (h2 : x ≤ 9) : x ∈ box9 := by
  unfold box9
  simp
  omega

lemma trbox8 : ∀ i ∈ box9, p9 i = Nat.testBit 107 (4 * (p8 (i - 1)).toNat + 2 * (p8 i).toNat + (p8 (i + 1)).toNat) := by
  decide

lemma tr8 (i : ℤ) : p9 i = Nat.testBit 107 (4 * (p8 (i - 1)).toNat + 2 * (p8 i).toNat + (p8 (i + 1)).toNat) := by
  by_cases h : -9 ≤ i ∧ i ≤ 9
  · exact trbox8 i (mem_box9 i h.1 h.2)
  · rw [far9 i (by omega), far8 (i - 1) (by omega), far8 i (by omega), far8 (i + 1) (by omega)]
    decide

def box10 : List ℤ := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

lemma mem_box10 (x : ℤ) (h1 : -10 ≤ x) (h2 : x ≤ 10) : x ∈ box10 := by
  unfold box10
  simp
  omega

lemma trbox9 : ∀ i ∈ box10, p10 i = Nat.testBit 107 (4 * (p9 (i - 1)).toNat + 2 * (p9 i).toNat + (p9 (i + 1)).toNat) := by
  decide

lemma tr9 (i : ℤ) : p10 i = Nat.testBit 107 (4 * (p9 (i - 1)).toNat + 2 * (p9 i).toNat + (p9 (i + 1)).toNat) := by
  by_cases h : -10 ≤ i ∧ i ≤ 10
  · exact trbox9 i (mem_box10 i h.1 h.2)
  · rw [far10 i (by omega), far9 (i - 1) (by omega), far9 i (by omega), far9 (i + 1) (by omega)]
    decide

open OMA.S_oeis_a267157 in
lemma c0 : ∀ i, row 0 i = p0 i := by
  intro i
  rfl

open OMA.S_oeis_a267157 in
lemma c1 : ∀ i, row 1 i = p1 i := by
  intro i
  show rule (row 0 (i - 1)) (row 0 i) (row 0 (i + 1)) = p1 i
  rw [c0, c0, c0]
  exact (tr0 i).symm

open OMA.S_oeis_a267157 in
lemma c2 : ∀ i, row 2 i = p2 i := by
  intro i
  show rule (row 1 (i - 1)) (row 1 i) (row 1 (i + 1)) = p2 i
  rw [c1, c1, c1]
  exact (tr1 i).symm

open OMA.S_oeis_a267157 in
lemma c3 : ∀ i, row 3 i = p3 i := by
  intro i
  show rule (row 2 (i - 1)) (row 2 i) (row 2 (i + 1)) = p3 i
  rw [c2, c2, c2]
  exact (tr2 i).symm

open OMA.S_oeis_a267157 in
lemma c4 : ∀ i, row 4 i = p4 i := by
  intro i
  show rule (row 3 (i - 1)) (row 3 i) (row 3 (i + 1)) = p4 i
  rw [c3, c3, c3]
  exact (tr3 i).symm

open OMA.S_oeis_a267157 in
lemma c5 : ∀ i, row 5 i = p5 i := by
  intro i
  show rule (row 4 (i - 1)) (row 4 i) (row 4 (i + 1)) = p5 i
  rw [c4, c4, c4]
  exact (tr4 i).symm

open OMA.S_oeis_a267157 in
lemma c6 : ∀ i, row 6 i = p6 i := by
  intro i
  show rule (row 5 (i - 1)) (row 5 i) (row 5 (i + 1)) = p6 i
  rw [c5, c5, c5]
  exact (tr5 i).symm

open OMA.S_oeis_a267157 in
lemma c7 : ∀ i, row 7 i = p7 i := by
  intro i
  show rule (row 6 (i - 1)) (row 6 i) (row 6 (i + 1)) = p7 i
  rw [c6, c6, c6]
  exact (tr6 i).symm

open OMA.S_oeis_a267157 in
lemma c8 : ∀ i, row 8 i = p8 i := by
  intro i
  show rule (row 7 (i - 1)) (row 7 i) (row 7 (i + 1)) = p8 i
  rw [c7, c7, c7]
  exact (tr7 i).symm

open OMA.S_oeis_a267157 in
lemma c9 : ∀ i, row 9 i = p9 i := by
  intro i
  show rule (row 8 (i - 1)) (row 8 i) (row 8 (i + 1)) = p9 i
  rw [c8, c8, c8]
  exact (tr8 i).symm

open OMA.S_oeis_a267157 in
lemma c10 : ∀ i, row 10 i = p10 i := by
  intro i
  show rule (row 9 (i - 1)) (row 9 i) (row 9 (i + 1)) = p10 i
  rw [c9, c9, c9]
  exact (tr9 i).symm

open OMA.S_oeis_a267157 in
lemma r0 : row 0 0 = true := by
  rw [c0]
  decide

open OMA.S_oeis_a267157 in
lemma r1 : row 1 0 = false := by
  rw [c1]
  decide

open OMA.S_oeis_a267157 in
lemma r2 : row 2 0 = false := by
  rw [c2]
  decide

open OMA.S_oeis_a267157 in
lemma r3 : row 3 0 = true := by
  rw [c3]
  decide

open OMA.S_oeis_a267157 in
lemma r4 : row 4 0 = true := by
  rw [c4]
  decide

open OMA.S_oeis_a267157 in
lemma r5 : row 5 0 = true := by
  rw [c5]
  decide

open OMA.S_oeis_a267157 in
lemma r6 : row 6 0 = true := by
  rw [c6]
  decide

open OMA.S_oeis_a267157 in
lemma r7 : row 7 0 = true := by
  rw [c7]
  decide

open OMA.S_oeis_a267157 in
lemma r8 : row 8 0 = true := by
  rw [c8]
  decide

open OMA.S_oeis_a267157 in
lemma r9 : row 9 0 = true := by
  rw [c9]
  decide

open OMA.S_oeis_a267157 in
lemma r10 : row 10 0 = false := by
  rw [c10]
  decide

open OMA.S_oeis_a267157 in
lemma a7 : a 7 = 159 := by
  unfold a
  simp [Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7]

open OMA.S_oeis_a267157 in
lemma a8 : a 8 = 319 := by
  unfold a
  simp [Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7, r8]

open OMA.S_oeis_a267157 in
lemma a9 : a 9 = 639 := by
  unfold a
  simp [Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9]

open OMA.S_oeis_a267157 in
lemma a10 : a 10 = 1278 := by
  unfold a
  simp [Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]

end A267157Aux

open OMA.S_oeis_a267157 A267157Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267157.main) := by
  intro h
  have h10 := h.2.1 10 (by norm_num)
  norm_num [a7, a8, a9, a10] at h10
