import OMAStatements.S_oeis_a133552
import Mathlib

namespace A133552
open OMA.S_oeis_a133552 in
def L0 : List Int := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]
open OMA.S_oeis_a133552 in
def L1 : List Int := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 0]
open OMA.S_oeis_a133552 in
def L2 : List Int := [4, 4, 4, 4, 4, 4, 4, 3, 4, 4, 4, 3, 4, 3, 3, 1, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 2, 4, 2, 2, 0]
open OMA.S_oeis_a133552 in
def L3 : List Int := [8, 8, 8, 7, 8, 7, 7, 4, 8, 8, 8, 6, 8, 6, 6, 2, 8, 8, 8, 7, 8, 7, 7, 3, 8, 8, 8, 4, 8, 4, 4, 0]
open OMA.S_oeis_a133552 in
def L4 : List Int := [16, 15, 15, 11, 16, 14, 14, 8, 16, 15, 15, 10, 16, 12, 12, 4, 16, 15, 15, 11, 16, 14, 14, 6, 16, 15, 15, 7, 16, 8, 8, 0]
open OMA.S_oeis_a133552 in
def L5 : List Int := [31, 26, 30, 22, 31, 25, 28, 16, 31, 26, 30, 20, 31, 22, 24, 8, 31, 26, 30, 22, 31, 25, 28, 12, 31, 26, 30, 14, 31, 15, 16, 0]
open OMA.S_oeis_a133552 in
def L6 : List Int := [57, 52, 56, 44, 57, 50, 53, 32, 57, 52, 56, 40, 57, 44, 46, 16, 57, 52, 56, 44, 57, 50, 53, 24, 57, 52, 56, 28, 57, 30, 31, 0]
open OMA.S_oeis_a133552 in
def L7 : List Int := [109, 100, 107, 85, 109, 96, 101, 62, 109, 100, 107, 77, 109, 84, 87, 31, 109, 100, 107, 85, 109, 96, 101, 46, 109, 100, 107, 53, 109, 56, 57, 0]
open OMA.S_oeis_a133552 in
def L8 : List Int := [209, 192, 205, 163, 209, 184, 193, 118, 209, 192, 205, 147, 209, 160, 165, 57, 209, 192, 205, 163, 209, 184, 193, 87, 209, 192, 205, 101, 209, 107, 109, 0]
open OMA.S_oeis_a133552 in
def L9 : List Int := [401, 368, 393, 311, 401, 352, 369, 222, 401, 368, 393, 280, 401, 306, 316, 109, 401, 368, 393, 311, 401, 352, 369, 165, 401, 368, 393, 193, 401, 205, 209, 0]
open OMA.S_oeis_a133552 in
def L10 : List Int := [769, 704, 753, 591, 769, 673, 707, 425, 769, 704, 753, 534, 769, 586, 606, 209, 769, 704, 753, 591, 769, 673, 707, 316, 769, 704, 753, 369, 769, 393, 401, 0]
open OMA.S_oeis_a133552 in
def L11 : List Int := [1473, 1344, 1442, 1132, 1473, 1287, 1355, 815, 1473, 1344, 1442, 1023, 1473, 1122, 1162, 401, 1473, 1344, 1442, 1132, 1473, 1287, 1355, 606, 1473, 1344, 1442, 707, 1473, 753, 769, 0]
open OMA.S_oeis_a133552 in
def L12 : List Int := [2817, 2574, 2760, 2170, 2817, 2465, 2595, 1563, 2817, 2574, 2760, 1961, 2817, 2149, 2226, 769, 2817, 2574, 2760, 2170, 2817, 2465, 2595, 1162, 2817, 2574, 2760, 1355, 2817, 1442, 1473, 0]
open OMA.S_oeis_a133552 in
def L13 : List Int := [5391, 4930, 5282, 4158, 5391, 4721, 4966, 2995, 5391, 4930, 5282, 3757, 5391, 4115, 4259, 1473, 5391, 4930, 5282, 4158, 5391, 4721, 4966, 2226, 5391, 4930, 5282, 2595, 5391, 2760, 2817, 0]
open OMA.S_oeis_a133552 in
def L14 : List Int := [10321, 9440, 10112, 7961, 10321, 9039, 9506, 5732, 10321, 9440, 10112, 7192, 10321, 7877, 8151, 2817, 10321, 9440, 10112, 7961, 10321, 9039, 9506, 4259, 10321, 9440, 10112, 4966, 10321, 5282, 5391, 0]
open OMA.S_oeis_a133552 in
def L15 : List Int := [19761, 18073, 19360, 15238, 19761, 17304, 18198, 10968, 19761, 18073, 19360, 13765, 19761, 15078, 15603, 5391, 19761, 18073, 19360, 15238, 19761, 17304, 18198, 8151, 19761, 18073, 19360, 9506, 19761, 10112, 10321, 0]

open OMA.S_oeis_a133552 in
def T (l : List Int) (s : Fin 32) : Int := l.getD s.val 0

open OMA.S_oeis_a133552 in
lemma c0 : ∀ s : Fin 32, count 0 s = T L0 s := by decide

open OMA.S_oeis_a133552 in
lemma key1 : ∀ s : Fin 32, step (T L0) s = T L1 s := by decide

open OMA.S_oeis_a133552 in
lemma c1 : ∀ s : Fin 32, count 1 s = T L1 s := by
  intro s
  have h : count 0 = T L0 := funext c0
  show step (count 0) s = _
  rw [h]
  exact key1 s

open OMA.S_oeis_a133552 in
lemma key2 : ∀ s : Fin 32, step (T L1) s = T L2 s := by decide

open OMA.S_oeis_a133552 in
lemma c2 : ∀ s : Fin 32, count 2 s = T L2 s := by
  intro s
  have h : count 1 = T L1 := funext c1
  show step (count 1) s = _
  rw [h]
  exact key2 s

open OMA.S_oeis_a133552 in
lemma key3 : ∀ s : Fin 32, step (T L2) s = T L3 s := by decide

open OMA.S_oeis_a133552 in
lemma c3 : ∀ s : Fin 32, count 3 s = T L3 s := by
  intro s
  have h : count 2 = T L2 := funext c2
  show step (count 2) s = _
  rw [h]
  exact key3 s

open OMA.S_oeis_a133552 in
lemma key4 : ∀ s : Fin 32, step (T L3) s = T L4 s := by decide

open OMA.S_oeis_a133552 in
lemma c4 : ∀ s : Fin 32, count 4 s = T L4 s := by
  intro s
  have h : count 3 = T L3 := funext c3
  show step (count 3) s = _
  rw [h]
  exact key4 s

open OMA.S_oeis_a133552 in
lemma key5 : ∀ s : Fin 32, step (T L4) s = T L5 s := by decide

open OMA.S_oeis_a133552 in
lemma c5 : ∀ s : Fin 32, count 5 s = T L5 s := by
  intro s
  have h : count 4 = T L4 := funext c4
  show step (count 4) s = _
  rw [h]
  exact key5 s

open OMA.S_oeis_a133552 in
lemma key6 : ∀ s : Fin 32, step (T L5) s = T L6 s := by decide

open OMA.S_oeis_a133552 in
lemma c6 : ∀ s : Fin 32, count 6 s = T L6 s := by
  intro s
  have h : count 5 = T L5 := funext c5
  show step (count 5) s = _
  rw [h]
  exact key6 s

open OMA.S_oeis_a133552 in
lemma key7 : ∀ s : Fin 32, step (T L6) s = T L7 s := by decide

open OMA.S_oeis_a133552 in
lemma c7 : ∀ s : Fin 32, count 7 s = T L7 s := by
  intro s
  have h : count 6 = T L6 := funext c6
  show step (count 6) s = _
  rw [h]
  exact key7 s

open OMA.S_oeis_a133552 in
lemma key8 : ∀ s : Fin 32, step (T L7) s = T L8 s := by decide

open OMA.S_oeis_a133552 in
lemma c8 : ∀ s : Fin 32, count 8 s = T L8 s := by
  intro s
  have h : count 7 = T L7 := funext c7
  show step (count 7) s = _
  rw [h]
  exact key8 s

open OMA.S_oeis_a133552 in
lemma key9 : ∀ s : Fin 32, step (T L8) s = T L9 s := by decide

open OMA.S_oeis_a133552 in
lemma c9 : ∀ s : Fin 32, count 9 s = T L9 s := by
  intro s
  have h : count 8 = T L8 := funext c8
  show step (count 8) s = _
  rw [h]
  exact key9 s

open OMA.S_oeis_a133552 in
lemma key10 : ∀ s : Fin 32, step (T L9) s = T L10 s := by decide

open OMA.S_oeis_a133552 in
lemma c10 : ∀ s : Fin 32, count 10 s = T L10 s := by
  intro s
  have h : count 9 = T L9 := funext c9
  show step (count 9) s = _
  rw [h]
  exact key10 s

open OMA.S_oeis_a133552 in
lemma key11 : ∀ s : Fin 32, step (T L10) s = T L11 s := by decide

open OMA.S_oeis_a133552 in
lemma c11 : ∀ s : Fin 32, count 11 s = T L11 s := by
  intro s
  have h : count 10 = T L10 := funext c10
  show step (count 10) s = _
  rw [h]
  exact key11 s

open OMA.S_oeis_a133552 in
lemma key12 : ∀ s : Fin 32, step (T L11) s = T L12 s := by decide

open OMA.S_oeis_a133552 in
lemma c12 : ∀ s : Fin 32, count 12 s = T L12 s := by
  intro s
  have h : count 11 = T L11 := funext c11
  show step (count 11) s = _
  rw [h]
  exact key12 s

open OMA.S_oeis_a133552 in
lemma key13 : ∀ s : Fin 32, step (T L12) s = T L13 s := by decide

open OMA.S_oeis_a133552 in
lemma c13 : ∀ s : Fin 32, count 13 s = T L13 s := by
  intro s
  have h : count 12 = T L12 := funext c12
  show step (count 12) s = _
  rw [h]
  exact key13 s

open OMA.S_oeis_a133552 in
lemma key14 : ∀ s : Fin 32, step (T L13) s = T L14 s := by decide

open OMA.S_oeis_a133552 in
lemma c14 : ∀ s : Fin 32, count 14 s = T L14 s := by
  intro s
  have h : count 13 = T L13 := funext c13
  show step (count 13) s = _
  rw [h]
  exact key14 s

open OMA.S_oeis_a133552 in
lemma key15 : ∀ s : Fin 32, step (T L14) s = T L15 s := by decide

open OMA.S_oeis_a133552 in
lemma c15 : ∀ s : Fin 32, count 15 s = T L15 s := by
  intro s
  have h : count 14 = T L14 := funext c14
  show step (count 14) s = _
  rw [h]
  exact key15 s

open OMA.S_oeis_a133552 in
lemma dev_tab : ∀ s : Fin 32, T L15 s - T L14 s - T L13 s - T L12 s - T L10 s - 2 * T L9 s
    + 2 * T L7 s + 2 * T L6 s + T L3 s - T L0 s = 0 := by decide

open OMA.S_oeis_a133552 in
lemma dev_zero : ∀ s : Fin 32, deviation (fun j => count (0 + j) s) = 0 := by
  intro s
  unfold deviation
  simp only [Nat.zero_add]
  rw [c15 s, c14 s, c13 s, c12 s, c10 s, c9 s, c7 s, c6 s, c3 s, c0 s]
  exact dev_tab s

open OMA.S_oeis_a133552 in
lemma step_dev (f : Nat → Fin 32 → Int) (s : Fin 32) :
    deviation (fun j => step (f j) s) = step (fun t => deviation (fun j => f j t)) s := by
  unfold deviation step
  split_ifs <;> ring

open OMA.S_oeis_a133552 in
lemma dev_all (n : ℕ) : ∀ s : Fin 32, deviation (fun j => count (n + j) s) = 0 := by
  induction n with
  | zero => exact dev_zero
  | succ n ih =>
    intro s
    have e : (fun j => count (n + 1 + j) s) = (fun j => step (count (n + j)) s) := by
      funext j
      have e' : n + 1 + j = (n + j) + 1 := by omega
      rw [e']
      rfl
    rw [e, step_dev (fun j => count (n + j)) s]
    have z : (fun t => deviation (fun j => count (n + j) t)) = fun _ => 0 := funext ih
    rw [z]
    unfold step
    split_ifs <;> simp

open OMA.S_oeis_a133552 in
lemma pc_single (f : Nat → Int) (c : Int) (m : Nat) : productCoeff f [c] m = c * f m := by
  cases m with
  | zero => rfl
  | succ k =>
    show c * f (k + 1) + productCoeff f [] k = c * f (k + 1)
    have h : productCoeff f [] k = 0 := by
      cases k <;> rfl
    rw [h, add_zero]

open OMA.S_oeis_a133552 in
lemma pc_congr (f g : Nat → Int) (l : List Int) :
    ∀ n : Nat, (∀ j ≤ n, f j = g j) → productCoeff f l n = productCoeff g l n := by
  induction l with
  | nil =>
    intro n _
    cases n <;> rfl
  | cons c cs ih =>
    intro n h
    cases n with
    | zero =>
      show c * f 0 = c * g 0
      rw [h 0 (le_refl 0)]
    | succ k =>
      show c * f (k + 1) + productCoeff f cs k = c * g (k + 1) + productCoeff g cs k
      rw [h (k + 1) (le_refl _), ih k (fun j hj => h j (by omega))]

open OMA.S_oeis_a133552 in
def tabA (j : Nat) : Int := [1, 2, 4, 8, 16, 31, 57, 109, 209, 401, 769, 1473, 2817, 5391, 10321].getD j 0

open OMA.S_oeis_a133552 in
lemma a_tab : ∀ j : Nat, j ≤ 14 → a j = tabA j := by
  intro j hj
  interval_cases j
  · show count 0 0 = _
    rw [c0 0]
    rfl
  · show count 1 0 = _
    rw [c1 0]
    rfl
  · show count 2 0 = _
    rw [c2 0]
    rfl
  · show count 3 0 = _
    rw [c3 0]
    rfl
  · show count 4 0 = _
    rw [c4 0]
    rfl
  · show count 5 0 = _
    rw [c5 0]
    rfl
  · show count 6 0 = _
    rw [c6 0]
    rfl
  · show count 7 0 = _
    rw [c7 0]
    rfl
  · show count 8 0 = _
    rw [c8 0]
    rfl
  · show count 9 0 = _
    rw [c9 0]
    rfl
  · show count 10 0 = _
    rw [c10 0]
    rfl
  · show count 11 0 = _
    rw [c11 0]
    rfl
  · show count 12 0 = _
    rw [c12 0]
    rfl
  · show count 13 0 = _
    rw [c13 0]
    rfl
  · show count 14 0 = _
    rw [c14 0]
    rfl

open OMA.S_oeis_a133552 in
lemma small_tab : ∀ n : Fin 15, productCoeff tabA denominator n.val = numeratorCoeff n.val := by
  decide

open OMA.S_oeis_a133552 in
lemma small (n : Nat) (hn : n < 15) : productCoeff a denominator n = numeratorCoeff n := by
  rw [pc_congr a tabA denominator n (fun j hj => a_tab j (by omega))]
  exact small_tab ⟨n, hn⟩

open OMA.S_oeis_a133552 in
lemma large (m : Nat) : productCoeff a denominator (m + 15) = numeratorCoeff (m + 15) := by
  have h : productCoeff a denominator (m + 15)
      = 1 * a (m + 15) + (-1 * a (m + 14) + (-1 * a (m + 13) + (-1 * a (m + 12) + (0 * a (m + 11)
        + (-1 * a (m + 10) + (-2 * a (m + 9) + (0 * a (m + 8) + (2 * a (m + 7) + (2 * a (m + 6)
        + (0 * a (m + 5) + (0 * a (m + 4) + (1 * a (m + 3) + (0 * a (m + 2) + (0 * a (m + 1)
        + productCoeff a [-1] m)))))))))))))) := rfl
  have hz : numeratorCoeff (m + 15) = 0 := rfl
  have hd := dev_all m 0
  unfold deviation at hd
  rw [h, hz, pc_single]
  have e : ∀ j, count (m + j) 0 = a (m + j) := fun j => rfl
  simp only [e] at hd
  simp only [Nat.add_zero] at hd
  linarith

end A133552

theorem OMA.solution : type_of% @OMA.S_oeis_a133552.main := by
  constructor
  · intro n
    exact A133552.dev_all n 0
  · intro n
    rcases lt_or_ge n 15 with h | h
    · exact A133552.small n h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
      exact A133552.large m
