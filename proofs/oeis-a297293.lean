import OMAStatements.S_oeis_a297293
import Mathlib

-- Problem: OEIS A297293, conjectures of Kimberling for the system a(n) = least new,
-- b(n) = least new >= a(n) + 2, c(n) = a(n) + b(n) - 2: for all n >= 0,
-- 0 <= 5n + 4 - 2a(n) <= 5, 0 <= 5n + 8 - 2b(n) <= 4, 0 <= c(n) - 5n <= 4.
-- Statement: statements/oeis-a297293.lean (declaration OMA.S_oeis_a297293.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Block j is the set of the numbers 5j, ..., 5j + 4. Invariant before block j (j >= 2):
-- all numbers below 5j are placed, exactly one more number b(2j-1) = 5j + o with o in {0, 1}
-- (the carry) is placed, and each c(i), i <= 2j - 1, is in block i. So in 5j, ..., 5j + 9 the
-- placed numbers are the carry, c(j) = 5j + e(j) and c(j+1) = 5j + 5 + e(j+1). The steps 2j and
-- 2j + 1 are then determined by the configuration (o, e(j), e(j+1)): a table with 16 rows gives
-- the offsets of a(2j), b(2j), a(2j+1), b(2j+1) (lemma blk checks one row, lemma block16 all).
-- The new values e(2j), e(2j+1) and the next carry are functions of the configuration.
-- To see that only the 16 configurations occur, the invariant also has two finite relations:
-- H (a configuration and the next value e) and V (the configuration of block i and the carry
-- of block 2i). The configurations of the blocks 2i, 2i + 1, 2i + 2 are functions of the
-- configurations of the blocks i, i + 1 and the carry of block 2i, and a finite check (lemma
-- closureF, by decide) shows that S, H and V are preserved. The base is the first four steps.
-- The bounds follow from the table (lemma tabfactsF).

namespace OMA.A297293

open OMA.S_oeis_a297293

lemma lnf_eq (s : Finset ℕ) (t m : ℕ) (hm : t ≤ m) (hns : m ∉ s)
    (hall : ∀ k, t ≤ k → k < m → k ∈ s) : leastNewFrom s t = m := by
  unfold leastNewFrom
  apply le_antisymm
  · exact Nat.sInf_le ⟨hm, hns⟩
  · refine le_csInf ⟨m, hm, hns⟩ ?_
    rintro k ⟨hk, hks⟩
    by_contra hlt
    exact hks (hall k hk (by omega))

lemma step_eq (U : Finset ℕ) (x y : ℕ) (h1 : leastNewFrom U 1 = x)
    (h2 : leastNewFrom (insert x U) (x + 2) = y) :
    step U = (x, y, x + y - 2, insert (x + y - 2) (insert y (insert x U))) := by
  unfold step
  simp only [h1, h2]

/-- The two steps of a block. The numbers 5j + t (t <= 9) that are placed before the block are
t = o (carry), t = ej (the number c(j)) and t = 5 + ej1 (the number c(j+1)). -/
lemma blk (j o ej ej1 α0 β0 α1 β1 : ℕ) (U : Finset ℕ) (hj : 2 ≤ j)
    (low : ∀ k, 0 < k → k < 5 * j → k ∈ U)
    (win : ∀ k, 5 * j ≤ k → k ≤ 5 * j + 9 →
      (k ∈ U ↔ k = 5 * j + o ∨ k = 5 * j + ej ∨ k = 5 * j + 5 + ej1))
    (s1 : ∀ t, t < α0 → t = o ∨ t = ej ∨ t = 5 + ej1)
    (s2 : ¬ (α0 = o ∨ α0 = ej ∨ α0 = 5 + ej1))
    (s3 : α0 + 2 ≤ β0)
    (s4 : ¬ (β0 = o ∨ β0 = ej ∨ β0 = 5 + ej1))
    (s5 : ∀ t, α0 + 2 ≤ t → t < β0 → t = o ∨ t = ej ∨ t = 5 + ej1)
    (s6 : ∀ t, t < α1 → (t = o ∨ t = ej ∨ t = 5 + ej1) ∨ t = α0 ∨ t = β0)
    (s7 : ¬ (α1 = o ∨ α1 = ej ∨ α1 = 5 + ej1) ∧ α1 ≠ α0 ∧ α1 ≠ β0)
    (s8 : α1 + 2 ≤ β1)
    (s9 : ¬ (β1 = o ∨ β1 = ej ∨ β1 = 5 + ej1) ∧ β1 ≠ α0 ∧ β1 ≠ β0)
    (s10 : ∀ t, α1 + 2 ≤ t → t < β1 → (t = o ∨ t = ej ∨ t = 5 + ej1) ∨ t = α0 ∨ t = β0)
    (sb : β0 ≤ 9 ∧ β1 ≤ 9) :
    step U = (5 * j + α0, 5 * j + β0, 5 * j + α0 + (5 * j + β0) - 2,
      insert (5 * j + α0 + (5 * j + β0) - 2) (insert (5 * j + β0) (insert (5 * j + α0) U))) ∧
    step (insert (5 * j + α0 + (5 * j + β0) - 2) (insert (5 * j + β0) (insert (5 * j + α0) U)))
      = (5 * j + α1, 5 * j + β1, 5 * j + α1 + (5 * j + β1) - 2,
        insert (5 * j + α1 + (5 * j + β1) - 2) (insert (5 * j + β1) (insert (5 * j + α1)
          (insert (5 * j + α0 + (5 * j + β0) - 2) (insert (5 * j + β0)
            (insert (5 * j + α0) U)))))) := by
  have inU : ∀ t, t ≤ 9 → (5 * j + t ∈ U ↔ t = o ∨ t = ej ∨ t = 5 + ej1) := by
    intro t ht
    rw [win _ (by omega) (by omega)]
    omega
  have h1 : leastNewFrom U 1 = 5 * j + α0 := by
    apply lnf_eq U 1 _ (by omega)
    · rw [inU α0 (by omega)]; exact s2
    · intro k hk hlt
      rcases Nat.lt_or_ge k (5 * j) with h | h
      · exact low k (by omega) h
      · have := s1 (k - 5 * j) (by omega)
        rw [show k = 5 * j + (k - 5 * j) by omega, inU _ (by omega)]
        exact this
  have h2 : leastNewFrom (insert (5 * j + α0) U) (5 * j + α0 + 2) = 5 * j + β0 := by
    apply lnf_eq _ _ _ (by omega)
    · rw [Finset.mem_insert, inU β0 sb.1]
      rintro (h | h)
      · omega
      · exact s4 h
    · intro k hk hlt
      rw [Finset.mem_insert]; right
      have := s5 (k - 5 * j) (by omega) (by omega)
      rw [show k = 5 * j + (k - 5 * j) by omega, inU _ (by omega)]
      exact this
  have first := step_eq U _ _ h1 h2
  refine ⟨first, ?_⟩
  have hc0 : 5 * j + 10 ≤ 5 * j + α0 + (5 * j + β0) - 2 := by omega
  have inU1 : ∀ t, t ≤ 9 → (5 * j + t ∈ insert (5 * j + α0 + (5 * j + β0) - 2)
      (insert (5 * j + β0) (insert (5 * j + α0) U)) ↔
      (t = o ∨ t = ej ∨ t = 5 + ej1) ∨ t = α0 ∨ t = β0) := by
    intro t ht
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, inU t ht]
    omega
  have lowU1 : ∀ k, 0 < k → k < 5 * j → k ∈ insert (5 * j + α0 + (5 * j + β0) - 2)
      (insert (5 * j + β0) (insert (5 * j + α0) U)) := fun k hk hlt =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (low k hk hlt)))
  have h3 : leastNewFrom (insert (5 * j + α0 + (5 * j + β0) - 2)
      (insert (5 * j + β0) (insert (5 * j + α0) U))) 1 = 5 * j + α1 := by
    apply lnf_eq _ 1 _ (by omega)
    · rw [inU1 α1 (by omega)]
      rintro (h | h | h)
      · exact s7.1 h
      · exact s7.2.1 h
      · exact s7.2.2 h
    · intro k hk hlt
      rcases Nat.lt_or_ge k (5 * j) with h | h
      · exact lowU1 k (by omega) h
      · have := s6 (k - 5 * j) (by omega)
        rw [show k = 5 * j + (k - 5 * j) by omega, inU1 _ (by omega)]
        exact this
  have h4 : leastNewFrom (insert (5 * j + α1) (insert (5 * j + α0 + (5 * j + β0) - 2)
      (insert (5 * j + β0) (insert (5 * j + α0) U)))) (5 * j + α1 + 2) = 5 * j + β1 := by
    apply lnf_eq _ _ _ (by omega)
    · rw [Finset.mem_insert, inU1 β1 sb.2]
      rintro (h | h | h | h)
      · omega
      · exact s9.1 h
      · exact s9.2.1 h
      · exact s9.2.2 h
    · intro k hk hlt
      rw [Finset.mem_insert]; right
      have := s10 (k - 5 * j) (by omega) (by omega)
      rw [show k = 5 * j + (k - 5 * j) by omega, inU1 _ (by omega)]
      exact this
  exact step_eq _ _ _ h3 h4

/-- The transition table: (carry o, c(j) - 5j, c(j+1) - 5(j+1)) gives the offsets of
a(2j), b(2j), a(2j+1), b(2j+1) from 5j. -/
def tab : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ
  | 0, 1, 2 => (2, 4, 3, 5)
  | 0, 1, 3 => (2, 4, 3, 5)
  | 0, 1, 4 => (2, 4, 3, 5)
  | 0, 2, 0 => (1, 3, 4, 6)
  | 0, 2, 3 => (1, 3, 4, 6)
  | 0, 3, 0 => (1, 4, 2, 6)
  | 0, 3, 1 => (1, 4, 2, 5)
  | 0, 3, 4 => (1, 4, 2, 5)
  | 0, 4, 1 => (1, 3, 2, 5)
  | 1, 0, 1 => (2, 4, 3, 5)
  | 1, 0, 2 => (2, 4, 3, 5)
  | 1, 0, 3 => (2, 4, 3, 5)
  | 1, 0, 4 => (2, 4, 3, 5)
  | 1, 3, 0 => (0, 2, 4, 6)
  | 1, 3, 4 => (0, 2, 4, 6)
  | 1, 4, 1 => (0, 2, 3, 5)
  | _, _, _ => (0, 0, 0, 0)

def out0 (o ej ej1 : ℕ) : ℕ := (tab o ej ej1).1 + (tab o ej ej1).2.1 - 2
def out1 (o ej ej1 : ℕ) : ℕ := (tab o ej ej1).2.2.1 + (tab o ej ej1).2.2.2 - 7
def onx (o ej ej1 : ℕ) : ℕ := (tab o ej ej1).2.2.2 - 5

/-- The 16 configurations that occur. -/
def inS (o ej ej1 : ℕ) : Bool := [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 0), (0, 2, 3), (0, 3, 0), (0, 3, 1), (0, 3, 4), (0, 4, 1), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 4), (1, 3, 0), (1, 3, 4), (1, 4, 1)].contains (o, ej, ej1)

/-- The allowed successions: a configuration and the next value e. -/
def inH (o ej ej1 ej2 : ℕ) : Bool := [(0, 1, 2, 0), (0, 1, 2, 3), (0, 1, 3, 0), (0, 1, 3, 1), (0, 1, 4, 1), (0, 2, 0, 4), (0, 2, 3, 0), (0, 2, 3, 4), (0, 3, 0, 1), (0, 3, 0, 2), (0, 3, 0, 4), (0, 3, 1, 4), (0, 3, 4, 1), (0, 4, 1, 2), (0, 4, 1, 3), (0, 4, 1, 4), (1, 0, 1, 4), (1, 0, 2, 0), (1, 0, 3, 0), (1, 0, 3, 4), (1, 0, 4, 1), (1, 3, 0, 3), (1, 3, 4, 1), (1, 4, 1, 2)].contains (o, ej, ej1, ej2)

/-- The allowed pairs: the configuration of block i and the carry of block 2i. -/
def inV (o ej ej1 o2 : ℕ) : Bool := [(0, 1, 2, 0), (0, 1, 3, 0), (0, 1, 4, 0), (0, 2, 0, 0), (0, 2, 3, 0), (0, 3, 0, 0), (0, 3, 1, 0), (0, 3, 4, 0), (0, 4, 1, 0), (1, 0, 1, 0), (1, 0, 2, 0), (1, 0, 3, 0), (1, 0, 4, 0), (1, 0, 4, 1), (1, 3, 0, 1), (1, 3, 4, 1), (1, 4, 1, 1)].contains (o, ej, ej1, o2)

set_option maxRecDepth 100000 in
lemma tabfactsF : ∀ o : Fin 2, ∀ ej ej1 : Fin 5, inS o ej ej1 = true →
    (tab o ej ej1).1 ≤ 2 ∧ 2 ≤ (tab o ej ej1).2.1 ∧ (tab o ej ej1).2.1 ≤ 4 ∧
    (tab o ej ej1).1 + 2 ≤ (tab o ej ej1).2.1 ∧
    2 ≤ (tab o ej ej1).2.2.1 ∧ (tab o ej ej1).2.2.1 ≤ 4 ∧
    5 ≤ (tab o ej ej1).2.2.2 ∧ (tab o ej ej1).2.2.2 ≤ 6 ∧
    (tab o ej ej1).1 + (tab o ej ej1).2.1 ≤ 6 ∧
    7 ≤ (tab o ej ej1).2.2.1 + (tab o ej ej1).2.2.2 ∧
    (tab o ej ej1).2.2.1 + (tab o ej ej1).2.2.2 ≤ 11 ∧
    (∀ t : Fin 5, (t : ℕ) = o ∨ (t : ℕ) = ej ∨ (t : ℕ) = (tab o ej ej1).1 ∨
      (t : ℕ) = (tab o ej ej1).2.1 ∨ (t : ℕ) = (tab o ej ej1).2.2.1) := by decide

lemma tabfacts (o ej ej1 : ℕ) (ho : o < 2) (hej : ej < 5) (hej1 : ej1 < 5)
    (hS : inS o ej ej1 = true) :
    (tab o ej ej1).1 ≤ 2 ∧ 2 ≤ (tab o ej ej1).2.1 ∧ (tab o ej ej1).2.1 ≤ 4 ∧
    (tab o ej ej1).1 + 2 ≤ (tab o ej ej1).2.1 ∧
    2 ≤ (tab o ej ej1).2.2.1 ∧ (tab o ej ej1).2.2.1 ≤ 4 ∧
    5 ≤ (tab o ej ej1).2.2.2 ∧ (tab o ej ej1).2.2.2 ≤ 6 ∧
    (tab o ej ej1).1 + (tab o ej ej1).2.1 ≤ 6 ∧
    7 ≤ (tab o ej ej1).2.2.1 + (tab o ej ej1).2.2.2 ∧
    (tab o ej ej1).2.2.1 + (tab o ej ej1).2.2.2 ≤ 11 ∧
    (∀ t, t < 5 → t = o ∨ t = ej ∨ t = (tab o ej ej1).1 ∨
      t = (tab o ej ej1).2.1 ∨ t = (tab o ej ej1).2.2.1) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    tabfactsF ⟨o, ho⟩ ⟨ej, hej⟩ ⟨ej1, hej1⟩ hS
  exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, fun t ht => f12 ⟨t, ht⟩⟩

set_option maxRecDepth 100000 in
lemma closureF : ∀ o : Fin 2, ∀ ej ej1 ej2 : Fin 5, ∀ o2 : Fin 2,
    inV o ej ej1 o2 = true → inH o ej ej1 ej2 = true →
    (inS o2 (out0 o ej ej1) (out1 o ej ej1) = true ∧
     inS (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2) = true ∧
     inH o2 (out0 o ej ej1) (out1 o ej ej1) (out0 (onx o ej ej1) ej1 ej2) = true ∧
     inV (onx o ej ej1) ej1 ej2 (onx (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2)) = true ∧
     inH (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2) (out1 (onx o ej ej1) ej1 ej2) = true ∧
     inS (onx (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2)) (out0 (onx o ej ej1) ej1 ej2)
       (out1 (onx o ej ej1) ej1 ej2) = true) := by decide

lemma closure (o ej ej1 ej2 o2 : ℕ) (ho : o < 2) (hej : ej < 5) (hej1 : ej1 < 5)
    (hej2 : ej2 < 5) (ho2 : o2 < 2)
    (hV : inV o ej ej1 o2 = true) (hH : inH o ej ej1 ej2 = true) :
    (inS o2 (out0 o ej ej1) (out1 o ej ej1) = true ∧
     inS (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2) = true ∧
     inH o2 (out0 o ej ej1) (out1 o ej ej1) (out0 (onx o ej ej1) ej1 ej2) = true ∧
     inV (onx o ej ej1) ej1 ej2 (onx (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2)) = true ∧
     inH (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2) (out1 (onx o ej ej1) ej1 ej2) = true ∧
     inS (onx (onx o2 (out0 o ej ej1) (out1 o ej ej1)) (out1 o ej ej1)
       (out0 (onx o ej ej1) ej1 ej2)) (out0 (onx o ej ej1) ej1 ej2)
       (out1 (onx o ej ej1) ej1 ej2) = true) :=
  closureF ⟨o, ho⟩ ⟨ej, hej⟩ ⟨ej1, hej1⟩ ⟨ej2, hej2⟩ ⟨o2, ho2⟩ hV hH

/-- The two steps of a block, for each of the 16 configurations. -/
lemma block16 (j o ej ej1 : ℕ) (U : Finset ℕ) (hj : 2 ≤ j)
    (low : ∀ k, 0 < k → k < 5 * j → k ∈ U)
    (win : ∀ k, 5 * j ≤ k → k ≤ 5 * j + 9 →
      (k ∈ U ↔ k = 5 * j + o ∨ k = 5 * j + ej ∨ k = 5 * j + 5 + ej1))
    (hS : inS o ej ej1 = true) :
    step U = (5 * j + (tab o ej ej1).1, 5 * j + (tab o ej ej1).2.1,
      5 * j + (tab o ej ej1).1 + (5 * j + (tab o ej ej1).2.1) - 2,
      insert (5 * j + (tab o ej ej1).1 + (5 * j + (tab o ej ej1).2.1) - 2)
        (insert (5 * j + (tab o ej ej1).2.1) (insert (5 * j + (tab o ej ej1).1) U))) ∧
    step (insert (5 * j + (tab o ej ej1).1 + (5 * j + (tab o ej ej1).2.1) - 2)
        (insert (5 * j + (tab o ej ej1).2.1) (insert (5 * j + (tab o ej ej1).1) U)))
      = (5 * j + (tab o ej ej1).2.2.1, 5 * j + (tab o ej ej1).2.2.2,
        5 * j + (tab o ej ej1).2.2.1 + (5 * j + (tab o ej ej1).2.2.2) - 2,
        insert (5 * j + (tab o ej ej1).2.2.1 + (5 * j + (tab o ej ej1).2.2.2) - 2)
          (insert (5 * j + (tab o ej ej1).2.2.2) (insert (5 * j + (tab o ej ej1).2.2.1)
            (insert (5 * j + (tab o ej ej1).1 + (5 * j + (tab o ej ej1).2.1) - 2)
              (insert (5 * j + (tab o ej ej1).2.1) (insert (5 * j + (tab o ej ej1).1) U)))))) := by
  have hmem : (o, ej, ej1) ∈ [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 0), (0, 2, 3), (0, 3, 0), (0, 3, 1), (0, 3, 4), (0, 4, 1), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 4), (1, 3, 0), (1, 3, 4), (1, 4, 1)] := by
    unfold inS at hS
    exact List.contains_iff_mem.mp hS
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact blk j 0 1 2 2 4 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 1 3 2 4 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 1 4 2 4 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 2 0 1 3 4 6 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 2 3 1 3 4 6 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 3 0 1 4 2 6 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 3 1 1 4 2 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 3 4 1 4 2 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 0 4 1 1 3 2 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 1 0 1 2 4 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 1 0 2 2 4 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 1 0 3 2 4 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 1 0 4 2 4 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 1 3 0 0 2 4 6 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 1 3 4 0 2 4 6 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)
  · exact blk j 1 4 1 0 2 3 5 U hj low win
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega)
      (by intro t h; omega) (by omega) (by omega) (by omega) (by intro t h1 h2; omega) (by omega)

/-- c(n) - 5n, for a function cf. -/
def E (cf : ℕ → ℕ) (n : ℕ) : ℕ := cf n - 5 * n

/-- The carry b(2j-1) - 5j, for a function bf. -/
def O (bf : ℕ → ℕ) (j : ℕ) : ℕ := bf (2 * j - 1) - 5 * j

/-- The two steps of block i follow the table. -/
def Row (i : ℕ) : Prop :=
  a (2 * i) = 5 * i + (tab (O b i) (E c i) (E c (i + 1))).1 ∧
  b (2 * i) = 5 * i + (tab (O b i) (E c i) (E c (i + 1))).2.1 ∧
  c (2 * i) = a (2 * i) + b (2 * i) - 2 ∧
  a (2 * i + 1) = 5 * i + (tab (O b i) (E c i) (E c (i + 1))).2.2.1 ∧
  b (2 * i + 1) = 5 * i + (tab (O b i) (E c i) (E c (i + 1))).2.2.2 ∧
  c (2 * i + 1) = a (2 * i + 1) + b (2 * i + 1) - 2

/-- The invariant before block j (after step 2j - 1). -/
def Inv (j : ℕ) : Prop :=
  (∀ k, k ∈ (state (2 * j - 1)).2.2.2 ↔
    (1 ≤ k ∧ k < 5 * j) ∨ k = b (2 * j - 1) ∨ ∃ i, i ≤ 2 * j - 1 ∧ k = c i) ∧
  (∀ i, i ≤ 2 * j - 1 → 5 * i ≤ c i ∧ c i ≤ 5 * i + 4) ∧
  (∀ i, 1 ≤ i → i ≤ j → 5 * i ≤ b (2 * i - 1) ∧ b (2 * i - 1) ≤ 5 * i + 1) ∧
  (∀ i, 1 ≤ i → i ≤ j → inS (O b i) (E c i) (E c (i + 1)) = true) ∧
  (∀ i, 1 ≤ i → i < j → Row i) ∧
  (∀ i, 1 ≤ i → i < j → inH (O b i) (E c i) (E c (i + 1)) (E c (i + 2)) = true) ∧
  (∀ i, 1 ≤ i → 2 * i ≤ j → inV (O b i) (E c i) (E c (i + 1)) (O b (2 * i)) = true)

lemma derive (i : ℕ) (hR : Row i)
    (hb : 5 * i ≤ b (2 * i - 1) ∧ b (2 * i - 1) ≤ 5 * i + 1)
    (hc : 5 * i ≤ c i ∧ c i ≤ 5 * i + 4)
    (hc1 : 5 * (i + 1) ≤ c (i + 1) ∧ c (i + 1) ≤ 5 * (i + 1) + 4)
    (hS : inS (O b i) (E c i) (E c (i + 1)) = true) :
    (∀ m, m = 2 * i → E c m = out0 (O b i) (E c i) (E c (i + 1)) ∧ 5 * m ≤ c m ∧ c m ≤ 5 * m + 4) ∧
    (∀ m, m = 2 * i + 1 →
      E c m = out1 (O b i) (E c i) (E c (i + 1)) ∧ 5 * m ≤ c m ∧ c m ≤ 5 * m + 4) ∧
    (∀ m, m = i + 1 → O b m = onx (O b i) (E c i) (E c (i + 1)) ∧
      5 * m ≤ b (2 * m - 1) ∧ b (2 * m - 1) ≤ 5 * m + 1) ∧
    (5 * i ≤ a (2 * i) ∧ a (2 * i) ≤ 5 * i + 2 ∧ 5 * i + 2 ≤ b (2 * i) ∧ b (2 * i) ≤ 5 * i + 4 ∧
      5 * i + 2 ≤ a (2 * i + 1) ∧ a (2 * i + 1) ≤ 5 * i + 4 ∧ 5 * i + 5 ≤ b (2 * i + 1) ∧
      b (2 * i + 1) ≤ 5 * i + 6) := by
  have hO : O b i < 2 := by unfold O; omega
  have hE : E c i < 5 := by unfold E; omega
  have hE1 : E c (i + 1) < 5 := by unfold E; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, -⟩ := tabfacts _ _ _ hO hE hE1 hS
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    subst hm
    show c (2 * i) - 5 * (2 * i) = (tab (O b i) (E c i) (E c (i + 1))).1 + (tab (O b i) (E c i) (E c (i + 1))).2.1 - 2 ∧ _
    omega
  · intro m hm
    subst hm
    show c (2 * i + 1) - 5 * (2 * i + 1) = (tab (O b i) (E c i) (E c (i + 1))).2.2.1 + (tab (O b i) (E c i) (E c (i + 1))).2.2.2 - 7 ∧ _
    omega
  · intro m hm
    subst hm
    have h21 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
    show b (2 * (i + 1) - 1) - 5 * (i + 1) = (tab (O b i) (E c i) (E c (i + 1))).2.2.2 - 5 ∧ _
    rw [h21]
    omega
  · omega

lemma state_succ (n : ℕ) : state (n + 1) = step (state n).2.2.2 := by
  rw [state]

/-- The induction step: block j. -/
lemma inv_step (j : ℕ) (hj : 2 ≤ j) (h : Inv j) : Inv (j + 1) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h
  have hb := i3 j (by omega) le_rfl
  have hcj := i2 j (by omega)
  have hcj1 := i2 (j + 1) (by omega)
  have hSj := i4 j (by omega) le_rfl
  have hOj : O b j < 2 := by unfold O; omega
  have hEj : E c j < 5 := by unfold E; omega
  have hEj1 : E c (j + 1) < 5 := by unfold E; omega
  have low : ∀ k, 0 < k → k < 5 * j → k ∈ (state (2 * j - 1)).2.2.2 :=
    fun k hk hlt => (i1 k).mpr (Or.inl ⟨hk, hlt⟩)
  have win : ∀ k, 5 * j ≤ k → k ≤ 5 * j + 9 → (k ∈ (state (2 * j - 1)).2.2.2 ↔
      k = 5 * j + O b j ∨ k = 5 * j + E c j ∨ k = 5 * j + 5 + E c (j + 1)) := by
    intro k hk1 hk2
    rw [i1 k]
    unfold O E
    constructor
    · rintro (h | h | ⟨i, hi, hk⟩)
      · omega
      · left; omega
      · have hci := i2 i hi
        have hij : i = j ∨ i = j + 1 := by omega
        rcases hij with rfl | rfl
        · right; left; omega
        · right; right; omega
    · rintro (h | h | h)
      · right; left; omega
      · right; right; exact ⟨j, by omega, by omega⟩
      · right; right; exact ⟨j + 1, by omega, by omega⟩
  obtain ⟨st1, st2⟩ := block16 j (O b j) (E c j) (E c (j + 1)) _ hj low win hSj
  have hs1 : state (2 * j) = step (state (2 * j - 1)).2.2.2 := by
    have := state_succ (2 * j - 1)
    rwa [show 2 * j - 1 + 1 = 2 * j by omega] at this
  rw [← hs1] at st1
  have hs2 : state (2 * j + 1) = step (state (2 * j)).2.2.2 := state_succ (2 * j)
  have hU1 : (state (2 * j)).2.2.2 = insert (5 * j + (tab (O b j) (E c j) (E c (j + 1))).1
      + (5 * j + (tab (O b j) (E c j) (E c (j + 1))).2.1) - 2)
      (insert (5 * j + (tab (O b j) (E c j) (E c (j + 1))).2.1)
        (insert (5 * j + (tab (O b j) (E c j) (E c (j + 1))).1) (state (2 * j - 1)).2.2.2)) := by
    rw [st1]
  rw [← hU1, ← hs2] at st2
  -- the values of a, b, c at 2j and 2j + 1
  have ha0 : a (2 * j) = 5 * j + (tab (O b j) (E c j) (E c (j + 1))).1 := by
    show (state (2 * j)).1 = _; rw [st1]
  have hb0 : b (2 * j) = 5 * j + (tab (O b j) (E c j) (E c (j + 1))).2.1 := by
    show (state (2 * j)).2.1 = _; rw [st1]
  have hc0 : c (2 * j) = a (2 * j) + b (2 * j) - 2 := by
    rw [ha0, hb0]; show (state (2 * j)).2.2.1 = _; rw [st1]
  have ha1 : a (2 * j + 1) = 5 * j + (tab (O b j) (E c j) (E c (j + 1))).2.2.1 := by
    show (state (2 * j + 1)).1 = _; rw [st2]
  have hb1 : b (2 * j + 1) = 5 * j + (tab (O b j) (E c j) (E c (j + 1))).2.2.2 := by
    show (state (2 * j + 1)).2.1 = _; rw [st2]
  have hc1 : c (2 * j + 1) = a (2 * j + 1) + b (2 * j + 1) - 2 := by
    rw [ha1, hb1]; show (state (2 * j + 1)).2.2.1 = _; rw [st2]
  have hRow : Row j := ⟨ha0, hb0, hc0, ha1, hb1, hc1⟩
  obtain ⟨d0, d1, d2, d3⟩ := derive j hRow hb hcj hcj1 hSj
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, fcov⟩ := tabfacts _ _ _ hOj hEj hEj1 hSj
  -- membership in the new set
  have hmem : ∀ k, k ∈ (state (2 * j + 1)).2.2.2 ↔
      k = c (2 * j + 1) ∨ k = b (2 * j + 1) ∨ k = a (2 * j + 1) ∨ k = c (2 * j) ∨ k = b (2 * j)
        ∨ k = a (2 * j) ∨ k ∈ (state (2 * j - 1)).2.2.2 := by
    intro k
    rw [hc1, hc0, ha0, hb0, ha1, hb1, st2, hU1]
    simp only [Finset.mem_insert]
  have allRow : ∀ i, 1 ≤ i → i ≤ j → Row i := by
    intro i hi1 hi2
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact i5 i hi1 hlt
    · rw [show i = j by omega]; exact hRow
  have n2 : ∀ i, i ≤ 2 * (j + 1) - 1 → 5 * i ≤ c i ∧ c i ≤ 5 * i + 4 := by
    intro i hi
    rcases Nat.lt_or_ge i (2 * j) with hlt | hge
    · exact i2 i (by omega)
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · exact (d0 i heq.symm).2
      · exact (d1 i (by omega)).2
  have n3 : ∀ i, 1 ≤ i → i ≤ j + 1 → 5 * i ≤ b (2 * i - 1) ∧ b (2 * i - 1) ≤ 5 * i + 1 := by
    intro i hi1 hi2
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact i3 i hi1 (by omega)
    · exact (d2 i (by omega)).2
  have bnd : ∀ i, i ≤ 2 * j + 1 → E c i < 5 := by
    intro i hi
    have := n2 i (by omega)
    unfold E; omega
  have bndO : ∀ i, 1 ≤ i → i ≤ j + 1 → O b i < 2 := by
    intro i hi1 hi2
    have := n3 i hi1 hi2
    unfold O; omega
  -- derived facts for a block i <= j
  have dv : ∀ i, 1 ≤ i → i ≤ j →
      (∀ m, m = 2 * i → E c m = out0 (O b i) (E c i) (E c (i + 1))) ∧
      (∀ m, m = 2 * i + 1 → E c m = out1 (O b i) (E c i) (E c (i + 1))) ∧
      (∀ m, m = i + 1 → O b m = onx (O b i) (E c i) (E c (i + 1))) := by
    intro i hi1 hi2
    obtain ⟨x0, x1, x2, -⟩ := derive i (allRow i hi1 hi2) (n3 i hi1 (by omega))
      (n2 i (by omega)) (n2 (i + 1) (by omega))
      (by
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · exact i4 i hi1 (by omega)
        · omega)
    exact ⟨fun m hm => (x0 m hm).1, fun m hm => (x1 m hm).1, fun m hm => (x2 m hm).1⟩
  -- the closure facts
  have key : inS (O b (j + 1)) (E c (j + 1)) (E c (j + 1 + 1)) = true ∧
      inH (O b j) (E c j) (E c (j + 1)) (E c (j + 2)) = true ∧
      (∀ i, 1 ≤ i → 2 * i = j + 1 → inV (O b i) (E c i) (E c (i + 1)) (O b (2 * i)) = true) := by
    rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
    · -- j = 2 i
      have hi : 1 ≤ i := by omega
      have cl := closure (O b i) (E c i) (E c (i + 1)) (E c (i + 2)) (O b (2 * i))
        (bndO i hi (by omega)) (bnd i (by omega)) (bnd (i + 1) (by omega)) (bnd (i + 2) (by omega))
        (bndO (2 * i) (by omega) (by omega)) (i7 i hi le_rfl) (i6 i hi (by omega))
      obtain ⟨di0, di1, di2⟩ := dv i hi (by omega)
      obtain ⟨dn0, dn1, dn2⟩ := dv (i + 1) (by omega) (by omega)
      obtain ⟨dj0, dj1, dj2⟩ := dv (2 * i) (by omega) le_rfl
      have e1 : E c (2 * i) = out0 (O b i) (E c i) (E c (i + 1)) := di0 _ rfl
      have e2 : E c (2 * i + 1) = out1 (O b i) (E c i) (E c (i + 1)) := di1 _ rfl
      have e3 : O b (i + 1) = onx (O b i) (E c i) (E c (i + 1)) := di2 _ rfl
      have e4 : E c (2 * i + 1 + 1) = out0 (O b (i + 1)) (E c (i + 1)) (E c (i + 2)) :=
        dn0 _ (by omega)
      have e5 : O b (2 * i + 1) = onx (O b (2 * i)) (E c (2 * i)) (E c (2 * i + 1)) := dj2 _ rfl
      have e6 : E c (2 * i + 2) = E c (2 * i + 1 + 1) := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [e5, e4, e1, e2, e3]; exact cl.2.1
      · rw [e6, e4, e1, e2, e3]; exact cl.2.2.1
      · intro i' h1 h2; omega
    · -- j = 2 i + 1
      have hi : 1 ≤ i := by omega
      have cl := closure (O b i) (E c i) (E c (i + 1)) (E c (i + 2)) (O b (2 * i))
        (bndO i hi (by omega)) (bnd i (by omega)) (bnd (i + 1) (by omega)) (bnd (i + 2) (by omega))
        (bndO (2 * i) (by omega) (by omega)) (i7 i hi (by omega)) (i6 i hi (by omega))
      obtain ⟨di0, di1, di2⟩ := dv i hi (by omega)
      obtain ⟨dn0, dn1, dn2⟩ := dv (i + 1) (by omega) (by omega)
      obtain ⟨dk0, dk1, dk2⟩ := dv (2 * i) (by omega) (by omega)
      obtain ⟨dj0, dj1, dj2⟩ := dv (2 * i + 1) (by omega) le_rfl
      have e1 : E c (2 * i) = out0 (O b i) (E c i) (E c (i + 1)) := di0 _ rfl
      have e2 : E c (2 * i + 1) = out1 (O b i) (E c i) (E c (i + 1)) := di1 _ rfl
      have e3 : O b (i + 1) = onx (O b i) (E c i) (E c (i + 1)) := di2 _ rfl
      have e4 : E c (2 * i + 1 + 1) = out0 (O b (i + 1)) (E c (i + 1)) (E c (i + 2)) :=
        dn0 _ (by omega)
      have e5 : E c (2 * i + 1 + 1 + 1) = out1 (O b (i + 1)) (E c (i + 1)) (E c (i + 2)) :=
        dn1 _ (by omega)
      have e6 : O b (2 * i + 1) = onx (O b (2 * i)) (E c (2 * i)) (E c (2 * i + 1)) := dk2 _ rfl
      have e7 : O b (2 * i + 1 + 1) = onx (O b (2 * i + 1)) (E c (2 * i + 1)) (E c (2 * i + 1 + 1)) :=
        dj2 _ rfl
      have e8 : E c (2 * i + 1 + 2) = E c (2 * i + 1 + 1 + 1) := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [e7, e5, e6, e4, e1, e2, e3]; exact cl.2.2.2.2.2
      · rw [e8, e5, e6, e4, e1, e2, e3]; exact cl.2.2.2.2.1
      · intro i' h1 h2
        have hi' : i' = i + 1 := by omega
        subst hi'
        have e9 : O b (2 * (i + 1)) = O b (2 * i + 1 + 1) := by
          rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
        have e10 : E c (i + 1 + 1) = E c (i + 2) := rfl
        rw [e9, e7, e6, e4, e1, e2, e3, e10]
        exact cl.2.2.2.1
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨?_, n2, n3, ?_, ?_, ?_, ?_⟩
  · -- the placed set after step 2j + 1
    intro k
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, hmem k, i1 k]
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d3
    constructor
    · rintro (h | h | h | h | h | h | h | h | ⟨i, hi, hk⟩)
      · right; right; exact ⟨2 * j + 1, le_rfl, h⟩
      · right; left; exact h
      · left; omega
      · right; right; exact ⟨2 * j, by omega, h⟩
      · left; omega
      · left; omega
      · left; omega
      · left; omega
      · right; right; exact ⟨i, by omega, hk⟩
    · rintro (⟨h1, h2⟩ | h | ⟨i, hi, hk⟩)
      · rcases Nat.lt_or_ge k (5 * j) with hlt | hge
        · right; right; right; right; right; right; left; exact ⟨h1, hlt⟩
        · have hcov := fcov (k - 5 * j) (by omega)
          have hOb : b (2 * j - 1) = 5 * j + O b j := by unfold O; omega
          have hEc : c j = 5 * j + E c j := by unfold E; omega
          rcases hcov with hh | hh | hh | hh | hh
          · right; right; right; right; right; right; right; left; omega
          · right; right; right; right; right; right; right; right
            exact ⟨j, by omega, by omega⟩
          · right; right; right; right; right; left; omega
          · right; right; right; right; left; omega
          · right; right; left; omega
      · right; left; exact h
      · rcases Nat.lt_or_ge i (2 * j) with hlt | hge
        · right; right; right; right; right; right; right; right; exact ⟨i, by omega, hk⟩
        · rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · right; right; right; left; rw [hk, ← heq]
          · left; rw [hk, show i = 2 * j + 1 by omega]
  · intro i hi1 hi2
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact i4 i hi1 (by omega)
    · rw [show i = j + 1 by omega]; exact k1
  · intro i hi1 hi2
    exact allRow i hi1 (by omega)
  · intro i hi1 hi2
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact i6 i hi1 hlt
    · rw [show i = j by omega]; exact k2
  · intro i hi1 hi2
    rcases Nat.lt_or_ge (2 * i) (j + 1) with hlt | hge
    · exact i7 i hi1 (by omega)
    · exact k3 i hi1 (by omega)

lemma step_eq' (U : Finset ℕ) (x y z : ℕ) (h1 : leastNewFrom U 1 = x)
    (h2 : leastNewFrom (insert x U) (x + 2) = y) (hz : x + y - 2 = z) :
    step U = (x, y, z, insert z (insert y (insert x U))) := by
  rw [step_eq U x y h1 h2, hz]

lemma st0 : state 0 = (1, 3, 2, insert 2 (insert 3 (insert 1 ∅))) := by
  rw [state]
  apply step_eq' ∅ 1 3 2
  · exact lnf_eq _ 1 1 le_rfl (by simp) (by intro k h1 h2; omega)
  · exact lnf_eq _ 3 3 le_rfl (by simp) (by intro k h1 h2; omega)
  · rfl

lemma st1 : state 1 = (4, 6, 8, insert 8 (insert 6 (insert 4
    (insert 2 (insert 3 (insert 1 ∅)))))) := by
  rw [state_succ 0, st0]
  apply step_eq' _ 4 6 8
  · exact lnf_eq _ 1 4 (by norm_num) (by simp)
      (by intro k h1 h2; interval_cases k <;> simp)
  · exact lnf_eq _ 6 6 le_rfl (by simp) (by intro k h1 h2; omega)
  · rfl

lemma st2 : state 2 = (5, 7, 10, insert 10 (insert 7 (insert 5 (insert 8 (insert 6 (insert 4
    (insert 2 (insert 3 (insert 1 ∅))))))))) := by
  rw [state_succ 1, st1]
  apply step_eq' _ 5 7 10
  · exact lnf_eq _ 1 5 (by norm_num) (by simp)
      (by intro k h1 h2; interval_cases k <;> simp)
  · exact lnf_eq _ 7 7 le_rfl (by simp) (by intro k h1 h2; omega)
  · rfl

lemma st3 : state 3 = (9, 11, 18, insert 18 (insert 11 (insert 9 (insert 10 (insert 7 (insert 5
    (insert 8 (insert 6 (insert 4 (insert 2 (insert 3 (insert 1 ∅)))))))))))) := by
  rw [state_succ 2, st2]
  apply step_eq' _ 9 11 18
  · exact lnf_eq _ 1 9 (by norm_num) (by simp)
      (by intro k h1 h2; interval_cases k <;> simp)
  · exact lnf_eq _ 11 11 le_rfl (by simp) (by intro k h1 h2; omega)
  · rfl

lemma a0 : a 0 = 1 := by show (state 0).1 = _; rw [st0]
lemma b0 : b 0 = 3 := by show (state 0).2.1 = _; rw [st0]
lemma c0 : c 0 = 2 := by show (state 0).2.2.1 = _; rw [st0]
lemma a1 : a 1 = 4 := by show (state 1).1 = _; rw [st1]
lemma b1 : b 1 = 6 := by show (state 1).2.1 = _; rw [st1]
lemma c1 : c 1 = 8 := by show (state 1).2.2.1 = _; rw [st1]
lemma a2 : a 2 = 5 := by show (state 2).1 = _; rw [st2]
lemma b2 : b 2 = 7 := by show (state 2).2.1 = _; rw [st2]
lemma c2 : c 2 = 10 := by show (state 2).2.2.1 = _; rw [st2]
lemma a3 : a 3 = 9 := by show (state 3).1 = _; rw [st3]
lemma b3 : b 3 = 11 := by show (state 3).2.1 = _; rw [st3]
lemma c3 : c 3 = 18 := by show (state 3).2.2.1 = _; rw [st3]

lemma inv_base : Inv 2 := by
  have hO1 : O b 1 = 1 := by unfold O; rw [show 2 * 1 - 1 = 1 by norm_num, b1]
  have hO2 : O b 2 = 1 := by unfold O; rw [show 2 * 2 - 1 = 3 by norm_num, b3]
  have hE1 : E c 1 = 3 := by unfold E; rw [c1]
  have hE2 : E c 2 = 0 := by unfold E; rw [c2]
  have hE3 : E c 3 = 3 := by unfold E; rw [c3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [show 2 * 2 - 1 = 3 by norm_num, st3, b3]
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false]
    constructor
    · intro h
      have hk : (1 ≤ k ∧ k ≤ 11) ∨ k = 18 := by omega
      rcases hk with ⟨h1, h2⟩ | h18
      · rcases Nat.lt_or_ge k 10 with hlt | hge
        · left; omega
        · rcases Nat.eq_or_lt_of_le hge with h10 | h11
          · right; right; exact ⟨2, by norm_num, by rw [c2]; omega⟩
          · right; left; omega
      · right; right; exact ⟨3, le_rfl, by rw [c3]; exact h18⟩
    · rintro (⟨h1, h2⟩ | h | ⟨i, hi, hk⟩)
      · omega
      · omega
      · interval_cases i
        · rw [c0] at hk; omega
        · rw [c1] at hk; omega
        · rw [c2] at hk; omega
        · rw [c3] at hk; omega
  · intro i hi
    have hi3 : i ≤ 3 := by omega
    interval_cases i
    · rw [c0]; omega
    · rw [c1]; omega
    · rw [c2]; omega
    · rw [c3]; omega
  · intro i h1 h2
    interval_cases i
    · rw [show 2 * 1 - 1 = 1 by norm_num, b1]; omega
    · rw [show 2 * 2 - 1 = 3 by norm_num, b3]; omega
  · intro i h1 h2
    interval_cases i
    · rw [hO1, hE1, hE2]; decide
    · rw [hO2, hE2, hE3]; decide
  · intro i h1 h2
    have hi : i = 1 := by omega
    subst hi
    unfold Row
    rw [hO1, hE1, hE2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * 1 = 2 by norm_num, a2]; rfl
    · rw [show 2 * 1 = 2 by norm_num, b2]; rfl
    · rw [show 2 * 1 = 2 by norm_num, a2, b2, c2]
    · rw [show 2 * 1 + 1 = 3 by norm_num, a3]; rfl
    · rw [show 2 * 1 + 1 = 3 by norm_num, b3]; rfl
    · rw [show 2 * 1 + 1 = 3 by norm_num, a3, b3, c3]
  · intro i h1 h2
    have hi : i = 1 := by omega
    subst hi
    rw [hO1, hE1, hE2, hE3]; decide
  · intro i h1 h2
    have hi : i = 1 := by omega
    subst hi
    rw [hO1, hE1, hE2, show 2 * 1 = 2 by norm_num, hO2]; decide

lemma inv_all : ∀ j, 2 ≤ j → Inv j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact inv_base
  | succ j hj ih => exact inv_step j hj ih

theorem main' : ∀ n : ℕ,
    (0 ≤ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ∧ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ≤ 5) ∧
    (0 ≤ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ∧ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ≤ 4) ∧
    (0 ≤ (c n : ℤ) - 5 * (n : ℤ) ∧ (c n : ℤ) - 5 * (n : ℤ) ≤ 4) := by
  intro n
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · interval_cases n
    · rw [a0, b0, c0]; norm_num
    · rw [a1, b1, c1]; norm_num
    · rw [a2, b2, c2]; norm_num
    · rw [a3, b3, c3]; norm_num
  · obtain ⟨j, hj⟩ : ∃ j, n = 2 * j ∨ n = 2 * j + 1 := ⟨n / 2, by omega⟩
    have hj2 : 2 ≤ j := by omega
    obtain ⟨-, i2, i3, i4, i5, -, -⟩ := inv_all (j + 1) (by omega)
    obtain ⟨-, -, -, g1, g2, g3, g4, g5, g6, g7, g8⟩ := derive j (i5 j (by omega) (by omega))
      (i3 j (by omega) (by omega)) (i2 j (by omega)) (i2 (j + 1) (by omega))
      (i4 j (by omega) (by omega))
    rcases hj with rfl | rfl
    · have hc := i2 (2 * j) (by omega)
      push_cast
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
    · have hc := i2 (2 * j + 1) (by omega)
      push_cast
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

end OMA.A297293

theorem OMA.solution : type_of% @OMA.S_oeis_a297293.main :=
  OMA.A297293.main'
