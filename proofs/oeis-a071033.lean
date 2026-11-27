import OMAStatements.S_oeis_a071033
import Mathlib

namespace A071033

open OMA.S_oeis_a071033

/-- `alt j t` is the block `1 0` repeated `j` times, followed by `t`. -/
def alt : ℕ → List Bool → List Bool
  | 0, t => t
  | k + 1, t => true :: false :: alt k t

lemma alt_tail (j : ℕ) (t : List Bool) : alt j (true :: false :: t) = alt (j + 1) t := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show true :: false :: alt j (true :: false :: t) = true :: false :: alt (j + 1) t
    rw [ih]

lemma c001 : cell false false true = true := by decide
lemma c011 : cell false true true = true := by decide
lemma c110 : cell true true false = true := by decide
lemma c111 : cell true true true = false := by decide
lemma c101 : cell true false true = false := by decide
lemma c010 : cell false true false = true := by decide

lemma scan_alt (j : ℕ) (t : List Bool) :
    true :: scan true false (alt j t) = alt j (true :: scan true false t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show true :: cell true false true :: cell false true false :: scan true false (alt j t)
      = true :: false :: alt j (true :: scan true false t)
    rw [c101, c010, ih]

lemma tail2 : scan true false [true, true] = [false, true, true, true] := by decide
lemma tail3 : scan true false [true, true, true] = [false, true, false, true, true] := by decide

lemma step_even (j : ℕ) :
    scan false false (true :: alt (j + 1) [true, true])
      = true :: true :: alt (j + 1) [true, true, true] := by
  show cell false false true :: cell false true true :: cell true true false ::
      scan true false (alt j [true, true]) = _
  rw [c001, c011, c110, scan_alt, tail2, alt_tail]

lemma step_odd (j : ℕ) :
    scan false false (true :: true :: alt (j + 1) [true, true, true])
      = true :: alt (j + 3) [true, true] := by
  show cell false false true :: cell false true true :: cell true true true ::
      cell true true false :: scan true false (alt j [true, true, true]) = _
  rw [c001, c011, c111, c110, scan_alt, tail3, alt_tail, alt_tail]
  rfl

lemma rows (m : ℕ) :
    row (2 * m + 2) = true :: alt (2 * m + 1) [true, true] ∧
      row (2 * m + 3) = true :: true :: alt (2 * m + 1) [true, true, true] := by
  induction m with
  | zero => exact ⟨by decide, by decide⟩
  | succ m ih =>
    obtain ⟨_, h2⟩ := ih
    have h3 : row (2 * m + 4) = true :: alt (2 * m + 3) [true, true] := by
      show scan false false (row (2 * m + 3)) = _
      rw [h2, step_odd]
    have h4 : row (2 * m + 5) = true :: true :: alt (2 * m + 3) [true, true, true] := by
      show scan false false (row (2 * m + 4)) = _
      rw [h3, step_even]
    exact ⟨h3, h4⟩

/-- the accumulator after reading `j` blocks `1 0`. -/
def g : ℕ → ℕ → ℕ
  | 0, a => a
  | j + 1, a => g j (100 * a + 10)

lemma read_alt (j acc : ℕ) (t : List Bool) :
    readWord acc (alt j t) = readWord (g j acc) t := by
  induction j generalizing acc with
  | zero => rfl
  | succ j ih =>
    show readWord ((acc * 10 + true.toNat) * 10 + false.toNat) (alt j t)
      = readWord (g j (100 * acc + 10)) t
    rw [ih]
    have e : (acc * 10 + true.toNat) * 10 + false.toNat = 100 * acc + 10 := by
      simp only [Bool.toNat_true, Bool.toNat_false]; ring
    rw [e]

lemma g_eq (j a : ℕ) : 99 * g j a + 10 = 100 ^ j * (99 * a + 10) := by
  induction j generalizing a with
  | zero => simp [g]
  | succ j ih =>
    show 99 * g j (100 * a + 10) + 10 = _
    rw [ih]; ring

lemma read_even (m : ℕ) :
    readWord 0 (true :: alt (2 * m + 1) [true, true]) = 100 * g (2 * m + 1) 1 + 11 := by
  show readWord (0 * 10 + true.toNat) (alt (2 * m + 1) [true, true]) = _
  rw [read_alt]
  show ((g (2 * m + 1) (0 * 10 + true.toNat)) * 10 + true.toNat) * 10 + true.toNat = _
  simp only [Bool.toNat_true]
  ring

lemma read_odd (m : ℕ) :
    readWord 0 (true :: true :: alt (2 * m + 1) [true, true, true])
      = 1000 * g (2 * m + 1) 11 + 111 := by
  show readWord ((0 * 10 + true.toNat) * 10 + true.toNat) (alt (2 * m + 1) [true, true, true]) = _
  rw [read_alt]
  show (((g (2 * m + 1) ((0 * 10 + true.toNat) * 10 + true.toNat)) * 10 + true.toNat) * 10
    + true.toNat) * 10 + true.toNat = _
  simp only [Bool.toNat_true]
  ring

end A071033

open OMA.S_oeis_a071033 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071033.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e : n = 2 * m + 2 := by omega
    subst e
    rw [if_neg (by omega), (A071033.rows m).1, A071033.read_even]
    have hg := A071033.g_eq (2 * m + 1) 1
    have hp : (100 : ℕ) ^ (2 * m + 2) = 100 * 100 ^ (2 * m + 1) := by ring
    rw [hp]
    generalize (100 : ℕ) ^ (2 * m + 1) = T at *
    generalize A071033.g (2 * m + 1) 1 = G at *
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e : n = 2 * m + 3 := by omega
    subst e
    rw [if_pos (by omega), (A071033.rows m).2, A071033.read_odd]
    have hg := A071033.g_eq (2 * m + 1) 11
    have hp : (100 : ℕ) ^ (2 * m + 3) = 10000 * 100 ^ (2 * m + 1) := by ring
    rw [hp]
    generalize (100 : ℕ) ^ (2 * m + 1) = T at *
    generalize A071033.g (2 * m + 1) 11 = G at *
    omega
