import OMAStatements.S_oeis_a200786
import Mathlib

/-! Proof for OEIS A200786: build the array from the front. `E_m(s, t)` counts the ways to append `m` entries after a last entry `t` reached in step-state `s` (fresh, after an increase); summing over the next entry, split at `t`, gives a recursion in which every `E_m(s, t)` is an explicit polynomial in `n` and `t` (for `t ≤ n`), proved by induction using closed forms for the partial sums. Summing over the first entry gives an explicit polynomial of degree 4 for `a(n)`, and the g.f. follows coefficientwise.
Credit: Sudharsan Rajendiran -/

namespace OMA.Old200786

/-- `ok l`: no three consecutive entries of `l` are strictly increasing. -/
def ok : List ℕ → Bool
  | a :: b :: c :: t => !(decide (a < b) && decide (b < c)) && ok (b :: c :: t)
  | _ => true

/-- A200786(n): the number of 0..n arrays `x(0..3)` of 4 elements without any two consecutive increases, i.e. no three consecutive entries are strictly increasing. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

end OMA.Old200786

namespace OMA.P200786
open OMA.Old200786 Finset

def nxt (t x : ℕ) : ℕ := if t < x then 1 else 0
def bad (s t x : ℕ) : Bool := decide (s = 1) && decide (t < x)

/-- `goodS s t l`: the list `t :: l`, entered into `t` with step-state `s`, has no bad triple. -/
def goodS : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | s, t, x :: l => !bad s t x && goodS (nxt t x) x l

lemma ok3 (a b : ℕ) (l : List ℕ) : ok (a :: b :: l) = goodS (nxt a b) b l := by
  induction l generalizing a b with
  | nil => simp [ok, goodS]
  | cons c l ih =>
    rw [ok, ih b c, goodS]
    congr 1
    simp only [nxt, bad]
    by_cases h1 : a < b <;> by_cases h2 : b < a <;> by_cases h3 : b < c <;> by_cases h4 : c < b <;>
      simp [h1, h2, h3, h4] <;> omega

lemma ok1 (t : ℕ) (l : List ℕ) : ok (t :: l) = goodS 0 t l := by
  cases l with
  | nil => simp [ok, goodS]
  | cons x l => rw [ok3, goodS]; simp [bad]

abbrev arr (n L : ℕ) : Finset (Fin L → ℕ) := Fintype.piFinset fun _ : Fin L => range (n + 1)

lemma card_cons (n L : ℕ) (Q : ℕ → (Fin L → ℕ) → Bool) :
    ((arr n (L + 1)).filter (fun v => Q (v 0) (Fin.tail v))).card =
      ∑ w ∈ arr n L, ((range (n + 1)).filter (fun x => Q x w)).card := by
  rw [← card_sigma]
  apply card_nbij' (fun v => (⟨Fin.tail v, v 0⟩ : (_ : Fin L → ℕ) × ℕ)) (fun p => Fin.cons p.2 p.1)
  · intro v hv
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hv
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, Fintype.mem_piFinset, mem_range, mem_filter]
    exact ⟨fun i => hv.1 _, hv.1 0, hv.2⟩
  · intro p hp
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, Fintype.mem_piFinset, mem_range, mem_filter] at hp
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq]
    refine ⟨fun i => ?_, by simpa using hp.2.2⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hp.2.1
    · simpa using hp.1 j
  · intro v _; simp
  · intro p _; simp

lemma card_cons' (n L : ℕ) (Q : ℕ → (Fin L → ℕ) → Bool) :
    ((arr n (L + 1)).filter (fun v => Q (v 0) (Fin.tail v))).card =
      ∑ x ∈ range (n + 1), ((arr n L).filter (fun w => Q x w)).card := by
  rw [card_cons]; simp only [card_filter]; exact sum_comm

lemma ofFn_eq {L : ℕ} (v : Fin (L + 1) → ℕ) : List.ofFn v = v 0 :: List.ofFn (Fin.tail v) := by
  rw [List.ofFn_succ]; rfl

/-- ways to continue `t`, entered with state `s`, by `m` more entries. -/
def E (n m s t : ℕ) : ℕ := ((arr n m).filter (fun w => goodS s t (List.ofFn w))).card

lemma E_zero (n s t : ℕ) : E n 0 s t = 1 := by
  unfold E
  rw [filter_true_of_mem (fun w _ => by simp [goodS])]
  simp

lemma E_succ (n m s t : ℕ) : E n (m + 1) s t =
    ∑ x ∈ range (n + 1), (if bad s t x then 0 else E n m (nxt t x) x) := by
  have e1 : E n (m + 1) s t = ((arr n (m + 1)).filter
      (fun v => (fun x w => goodS s t (x :: List.ofFn w)) (v 0) (Fin.tail v))).card := by
    unfold E; congr 1; apply filter_congr; intro v _; rw [ofFn_eq]
  rw [e1]; refine (card_cons' n m (fun x w => goodS s t (x :: List.ofFn w))).trans ?_
  apply sum_congr rfl; intro x _
  have e2 : (arr n m).filter (fun w => goodS s t (x :: List.ofFn w)) =
      (arr n m).filter (fun w => (!bad s t x && goodS (nxt t x) x (List.ofFn w)) = true) :=
    filter_congr (fun w _ => by rw [goodS])
  rw [e2]
  cases hb : bad s t x
  · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]; rfl
  · simp

/-- split a sum over `0..n` at `t`. -/
lemma split3 (n t : ℕ) (ht : t ≤ n) (g : ℕ → ℚ) :
    ∑ x ∈ range (n + 1), g x = ∑ x ∈ range t, g x + g t + ∑ x ∈ Ico (t + 1) (n + 1), g x := by
  rw [← sum_range_add_sum_Ico g (show t + 1 ≤ n + 1 by omega), sum_range_succ]

lemma Ico_sum (a b : ℕ) (hab : a ≤ b) (g : ℕ → ℚ) :
    ∑ x ∈ Ico a b, g x = ∑ x ∈ range b, g x - ∑ x ∈ range a, g x := by
  rw [← sum_range_add_sum_Ico g hab]; ring

def Q0_0 (n t : ℚ) : ℚ := (1 : ℚ)

lemma S0_0 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q0_0 n (x : ℚ) = (1 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q0_0]; push_cast; ring

def Q0_1 (n t : ℚ) : ℚ := (1 : ℚ)

lemma S0_1 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q0_1 n (x : ℚ) = (1 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q0_1]; push_cast; ring

def Q1_0 (n t : ℚ) : ℚ := (1 : ℚ) * n ^ 1 + (1 : ℚ)

lemma S1_0 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q1_0 n (x : ℚ) = (1 : ℚ) * n ^ 1 * (M : ℚ) ^ 1 + (1 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q1_0]; push_cast; ring

def Q1_1 (n t : ℚ) : ℚ := (1 : ℚ) * t ^ 1 + (1 : ℚ)

lemma S1_1 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q1_1 n (x : ℚ) = (1 / 2 : ℚ) * (M : ℚ) ^ 2 + (1 / 2 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q1_1]; push_cast; ring

def Q2_0 (n t : ℚ) : ℚ := (1 / 2 : ℚ) * n ^ 2 + (1 : ℚ) * n ^ 1 * t ^ 1 + (5 / 2 : ℚ) * n ^ 1 + (-1 / 2 : ℚ) * t ^ 2 + (-1 / 2 : ℚ) * t ^ 1 + (1 : ℚ)

lemma S2_0 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q2_0 n (x : ℚ) = (1 / 2 : ℚ) * n ^ 2 * (M : ℚ) ^ 1 + (1 / 2 : ℚ) * n ^ 1 * (M : ℚ) ^ 2 + (2 : ℚ) * n ^ 1 * (M : ℚ) ^ 1 + (-1 / 6 : ℚ) * (M : ℚ) ^ 3 + (7 / 6 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q2_0]; push_cast; ring

def Q2_1 (n t : ℚ) : ℚ := (1 : ℚ) * n ^ 1 * t ^ 1 + (1 : ℚ) * n ^ 1 + (1 : ℚ) * t ^ 1 + (1 : ℚ)

lemma S2_1 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q2_1 n (x : ℚ) = (1 / 2 : ℚ) * n ^ 1 * (M : ℚ) ^ 2 + (1 / 2 : ℚ) * n ^ 1 * (M : ℚ) ^ 1 + (1 / 2 : ℚ) * (M : ℚ) ^ 2 + (1 / 2 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q2_1]; push_cast; ring

def Q3_0 (n t : ℚ) : ℚ := (1 / 2 : ℚ) * n ^ 3 + (1 / 2 : ℚ) * n ^ 2 * t ^ 1 + (5 / 2 : ℚ) * n ^ 2 + (3 / 2 : ℚ) * n ^ 1 * t ^ 1 + (4 : ℚ) * n ^ 1 + (-1 / 6 : ℚ) * t ^ 3 + (-1 : ℚ) * t ^ 2 + (-5 / 6 : ℚ) * t ^ 1 + (1 : ℚ)

lemma S3_0 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q3_0 n (x : ℚ) = (1 / 2 : ℚ) * n ^ 3 * (M : ℚ) ^ 1 + (1 / 4 : ℚ) * n ^ 2 * (M : ℚ) ^ 2 + (9 / 4 : ℚ) * n ^ 2 * (M : ℚ) ^ 1 + (3 / 4 : ℚ) * n ^ 1 * (M : ℚ) ^ 2 + (13 / 4 : ℚ) * n ^ 1 * (M : ℚ) ^ 1 + (-1 / 24 : ℚ) * (M : ℚ) ^ 4 + (-1 / 4 : ℚ) * (M : ℚ) ^ 3 + (1 / 24 : ℚ) * (M : ℚ) ^ 2 + (5 / 4 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q3_0]; push_cast; ring

def Q3_1 (n t : ℚ) : ℚ := (1 / 2 : ℚ) * n ^ 2 * t ^ 1 + (1 / 2 : ℚ) * n ^ 2 + (1 / 2 : ℚ) * n ^ 1 * t ^ 2 + (3 : ℚ) * n ^ 1 * t ^ 1 + (5 / 2 : ℚ) * n ^ 1 + (-1 / 6 : ℚ) * t ^ 3 + (-1 / 2 : ℚ) * t ^ 2 + (2 / 3 : ℚ) * t ^ 1 + (1 : ℚ)

lemma S3_1 (n : ℚ) (M : ℕ) : ∑ x ∈ range M, Q3_1 n (x : ℚ) = (1 / 4 : ℚ) * n ^ 2 * (M : ℚ) ^ 2 + (1 / 4 : ℚ) * n ^ 2 * (M : ℚ) ^ 1 + (1 / 6 : ℚ) * n ^ 1 * (M : ℚ) ^ 3 + (5 / 4 : ℚ) * n ^ 1 * (M : ℚ) ^ 2 + (13 / 12 : ℚ) * n ^ 1 * (M : ℚ) ^ 1 + (-1 / 24 : ℚ) * (M : ℚ) ^ 4 + (-1 / 12 : ℚ) * (M : ℚ) ^ 3 + (13 / 24 : ℚ) * (M : ℚ) ^ 2 + (7 / 12 : ℚ) * (M : ℚ) ^ 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; simp only [Q3_1]; push_cast; ring

lemma EC0 (n s t : ℕ) : (E n 0 s t : ℚ) = Q0_0 n t := by
  rw [E_zero]; simp [Q0_0]

lemma EC1_0 (n t : ℕ) (ht : t ≤ n) : (E n 1 0 t : ℚ) = Q1_0 n t := by
  rw [show 1 = 0 + 1 from rfl, E_succ]; push_cast
  rw [split3 n t ht]
  rw [sum_congr rfl (fun x hx => (show (if bad 0 t x = true then (0 : ℚ) else (E n 0 (nxt t x) x : ℚ)) = Q0_1 n (x : ℚ) from by
    simp only [mem_Ico] at hx
    rw [show bad 0 t x = false by simp [bad] <;> omega, show nxt t x = 1 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC0]; try simp [Q0_1, Q0_0]) : ∀ x ∈ Ico (t + 1) (n + 1), _ = _)]
  rw [Ico_sum (t + 1) (n + 1) (by omega), S0_1, S0_1]
  rw [sum_congr rfl (fun x hx => (show (if bad 0 t x = true then (0 : ℚ) else (E n 0 (nxt t x) x : ℚ)) = Q0_0 n (x : ℚ) from by
    simp only [mem_range] at hx
    rw [show bad 0 t x = false by simp [bad] <;> omega, show nxt t x = 0 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC0]; try simp [Q0_0]) : ∀ x ∈ range t, _ = _), S0_0]
  rw [show bad 0 t t = false by simp [bad], show nxt t t = 0 by simp [nxt]]
  simp only [Bool.false_eq_true, if_false]
  rw [EC0]
  simp only [Q0_0, Q0_1, Q1_0, sum_const_zero]
  push_cast; ring

lemma EC1_1 (n t : ℕ) (ht : t ≤ n) : (E n 1 1 t : ℚ) = Q1_1 n t := by
  rw [show 1 = 0 + 1 from rfl, E_succ]; push_cast
  rw [split3 n t ht]
  rw [sum_congr rfl (fun x hx => (show (if bad 1 t x = true then (0 : ℚ) else (E n 0 (nxt t x) x : ℚ)) = 0 from by
    simp only [mem_Ico] at hx
    rw [show bad 1 t x = true by simp [bad] <;> omega]; simp) : ∀ x ∈ Ico (t + 1) (n + 1), _ = _)]
  rw [sum_congr rfl (fun x hx => (show (if bad 1 t x = true then (0 : ℚ) else (E n 0 (nxt t x) x : ℚ)) = Q0_0 n (x : ℚ) from by
    simp only [mem_range] at hx
    rw [show bad 1 t x = false by simp [bad] <;> omega, show nxt t x = 0 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC0]; try simp [Q0_0]) : ∀ x ∈ range t, _ = _), S0_0]
  rw [show bad 1 t t = false by simp [bad], show nxt t t = 0 by simp [nxt]]
  simp only [Bool.false_eq_true, if_false]
  rw [EC0]
  simp only [Q0_0, Q0_1, Q1_1, sum_const_zero]
  push_cast; ring

lemma EC2_0 (n t : ℕ) (ht : t ≤ n) : (E n 2 0 t : ℚ) = Q2_0 n t := by
  rw [show 2 = 1 + 1 from rfl, E_succ]; push_cast
  rw [split3 n t ht]
  rw [sum_congr rfl (fun x hx => (show (if bad 0 t x = true then (0 : ℚ) else (E n 1 (nxt t x) x : ℚ)) = Q1_1 n (x : ℚ) from by
    simp only [mem_Ico] at hx
    rw [show bad 0 t x = false by simp [bad] <;> omega, show nxt t x = 1 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC1_1 n x (by omega)]) : ∀ x ∈ Ico (t + 1) (n + 1), _ = _)]
  rw [Ico_sum (t + 1) (n + 1) (by omega), S1_1, S1_1]
  rw [sum_congr rfl (fun x hx => (show (if bad 0 t x = true then (0 : ℚ) else (E n 1 (nxt t x) x : ℚ)) = Q1_0 n (x : ℚ) from by
    simp only [mem_range] at hx
    rw [show bad 0 t x = false by simp [bad] <;> omega, show nxt t x = 0 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC1_0 n x (by omega)]) : ∀ x ∈ range t, _ = _), S1_0]
  rw [show bad 0 t t = false by simp [bad], show nxt t t = 0 by simp [nxt]]
  simp only [Bool.false_eq_true, if_false]
  rw [EC1_0 n t ht]
  simp only [Q1_0, Q1_1, Q2_0, sum_const_zero]
  push_cast; ring

lemma EC2_1 (n t : ℕ) (ht : t ≤ n) : (E n 2 1 t : ℚ) = Q2_1 n t := by
  rw [show 2 = 1 + 1 from rfl, E_succ]; push_cast
  rw [split3 n t ht]
  rw [sum_congr rfl (fun x hx => (show (if bad 1 t x = true then (0 : ℚ) else (E n 1 (nxt t x) x : ℚ)) = 0 from by
    simp only [mem_Ico] at hx
    rw [show bad 1 t x = true by simp [bad] <;> omega]; simp) : ∀ x ∈ Ico (t + 1) (n + 1), _ = _)]
  rw [sum_congr rfl (fun x hx => (show (if bad 1 t x = true then (0 : ℚ) else (E n 1 (nxt t x) x : ℚ)) = Q1_0 n (x : ℚ) from by
    simp only [mem_range] at hx
    rw [show bad 1 t x = false by simp [bad] <;> omega, show nxt t x = 0 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC1_0 n x (by omega)]) : ∀ x ∈ range t, _ = _), S1_0]
  rw [show bad 1 t t = false by simp [bad], show nxt t t = 0 by simp [nxt]]
  simp only [Bool.false_eq_true, if_false]
  rw [EC1_0 n t ht]
  simp only [Q1_0, Q1_1, Q2_1, sum_const_zero]
  push_cast; ring

lemma EC3_0 (n t : ℕ) (ht : t ≤ n) : (E n 3 0 t : ℚ) = Q3_0 n t := by
  rw [show 3 = 2 + 1 from rfl, E_succ]; push_cast
  rw [split3 n t ht]
  rw [sum_congr rfl (fun x hx => (show (if bad 0 t x = true then (0 : ℚ) else (E n 2 (nxt t x) x : ℚ)) = Q2_1 n (x : ℚ) from by
    simp only [mem_Ico] at hx
    rw [show bad 0 t x = false by simp [bad] <;> omega, show nxt t x = 1 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC2_1 n x (by omega)]) : ∀ x ∈ Ico (t + 1) (n + 1), _ = _)]
  rw [Ico_sum (t + 1) (n + 1) (by omega), S2_1, S2_1]
  rw [sum_congr rfl (fun x hx => (show (if bad 0 t x = true then (0 : ℚ) else (E n 2 (nxt t x) x : ℚ)) = Q2_0 n (x : ℚ) from by
    simp only [mem_range] at hx
    rw [show bad 0 t x = false by simp [bad] <;> omega, show nxt t x = 0 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC2_0 n x (by omega)]) : ∀ x ∈ range t, _ = _), S2_0]
  rw [show bad 0 t t = false by simp [bad], show nxt t t = 0 by simp [nxt]]
  simp only [Bool.false_eq_true, if_false]
  rw [EC2_0 n t ht]
  simp only [Q2_0, Q2_1, Q3_0, sum_const_zero]
  push_cast; ring

lemma EC3_1 (n t : ℕ) (ht : t ≤ n) : (E n 3 1 t : ℚ) = Q3_1 n t := by
  rw [show 3 = 2 + 1 from rfl, E_succ]; push_cast
  rw [split3 n t ht]
  rw [sum_congr rfl (fun x hx => (show (if bad 1 t x = true then (0 : ℚ) else (E n 2 (nxt t x) x : ℚ)) = 0 from by
    simp only [mem_Ico] at hx
    rw [show bad 1 t x = true by simp [bad] <;> omega]; simp) : ∀ x ∈ Ico (t + 1) (n + 1), _ = _)]
  rw [sum_congr rfl (fun x hx => (show (if bad 1 t x = true then (0 : ℚ) else (E n 2 (nxt t x) x : ℚ)) = Q2_0 n (x : ℚ) from by
    simp only [mem_range] at hx
    rw [show bad 1 t x = false by simp [bad] <;> omega, show nxt t x = 0 by simp [nxt] <;> omega]
    simp only [Bool.false_eq_true, if_false]
    rw [EC2_0 n x (by omega)]) : ∀ x ∈ range t, _ = _), S2_0]
  rw [show bad 1 t t = false by simp [bad], show nxt t t = 0 by simp [nxt]]
  simp only [Bool.false_eq_true, if_false]
  rw [EC2_0 n t ht]
  simp only [Q2_0, Q2_1, Q3_1, sum_const_zero]
  push_cast; ring

lemma a_eq (n : ℕ) : a n = ∑ t ∈ range (n + 1), E n 3 0 t := by
  have e1 : a n = ((arr n 4).filter
      (fun v => (fun x w => goodS 0 x (List.ofFn w)) (v 0) (Fin.tail v))).card := by
    unfold a; congr 1; apply filter_congr; intro v _; rw [ofFn_eq, ok1]
  rw [e1]; exact card_cons' n 3 (fun x w => goodS 0 x (List.ofFn w))

lemma closed (n : ℕ) : (a n : ℚ) = (17 / 24 : ℚ) * (n : ℚ) ^ 4 + (43 / 12 : ℚ) * (n : ℚ) ^ 3 + (151 / 24 : ℚ) * (n : ℚ) ^ 2 + (53 / 12 : ℚ) * (n : ℚ) ^ 1 + (1 : ℚ) := by
  rw [a_eq]; push_cast
  rw [sum_congr rfl (fun t ht => (show (E n 3 0 t : ℚ) = Q3_0 n t from by
    simp only [mem_range] at ht
    exact EC3_0 n t (by omega)))]
  rw [S3_0]; push_cast; ring

open PowerSeries in
lemma gf_old :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (16 - 5 * X + 10 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  ext m
  have hX : ((1 - X) ^ 5 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-5 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 + C (-10 : ℚ) * X ^ 3 + C (5 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 := by
    simp only [map_neg, map_one, map_ofNat, map_natCast]; ring
  rw [hX]
  have hN : (X * (16 - 5 * X + 10 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : PowerSeries ℚ) = X ^ 1 * C (16 : ℚ) + X ^ 2 * C (-5 : ℚ) + X ^ 3 * C (10 : ℚ) + X ^ 4 * C (-5 : ℚ) + X ^ 5 * C (1 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hN]
  simp only [mul_add, map_add, coeff_mk, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_mul_C, coeff_X,
    Nat.zero_le, if_true, Nat.sub_zero]
  have t1 : (OMA.Old200786.a 1 : ℚ) = 16 := by rw [OMA.P200786.closed]; norm_num
  have t2 : (OMA.Old200786.a 2 : ℚ) = 75 := by rw [OMA.P200786.closed]; norm_num
  have t3 : (OMA.Old200786.a 3 : ℚ) = 225 := by rw [OMA.P200786.closed]; norm_num
  have t4 : (OMA.Old200786.a 4 : ℚ) = 530 := by rw [OMA.P200786.closed]; norm_num
  have t5 : (OMA.Old200786.a 5 : ℚ) = 1071 := by rw [OMA.P200786.closed]; norm_num
  have t6 : (OMA.Old200786.a 6 : ℚ) = 1946 := by rw [OMA.P200786.closed]; norm_num
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m <;> norm_num [t1, t2, t3, t4, t5, t6, ]
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 6 := ⟨m - 6, by omega⟩
    simp only [if_pos (show 1 ≤ p + 6 by omega), if_pos (show 2 ≤ p + 6 by omega), if_pos (show 3 ≤ p + 6 by omega), if_pos (show 4 ≤ p + 6 by omega), if_pos (show 5 ≤ p + 6 by omega)]
    try simp only [if_neg (show ¬ (p + 6 = 0) by omega), if_neg (show ¬ (p + 6 = 1) by omega), if_neg (show ¬ (p + 6 = 2) by omega), if_neg (show ¬ (p + 6 = 3) by omega), if_neg (show ¬ (p + 6 = 4) by omega), if_neg (show ¬ (p + 6 = 5) by omega)]
    try simp only [if_neg (show ¬ (p + 6 - 0 = 0) by omega), if_neg (show ¬ (p + 6 - 1 = 0) by omega), if_neg (show ¬ (p + 6 - 2 = 0) by omega), if_neg (show ¬ (p + 6 - 3 = 0) by omega), if_neg (show ¬ (p + 6 - 4 = 0) by omega), if_neg (show ¬ (p + 6 - 5 = 0) by omega)]
    rw [show p + 6 - 1 = p + 5 by omega, show p + 6 - 2 = p + 4 by omega, show p + 6 - 3 = p + 3 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 5 = p + 1 by omega]
    try simp only [if_neg (show ¬ (p + 6 = 0) by omega), if_neg (show ¬ (p + 5 = 0) by omega), if_neg (show ¬ (p + 4 = 0) by omega), if_neg (show ¬ (p + 3 = 0) by omega), if_neg (show ¬ (p + 2 = 0) by omega), if_neg (show ¬ (p + 1 = 0) by omega)]
    rw [OMA.P200786.closed (p + 6), OMA.P200786.closed (p + 5), OMA.P200786.closed (p + 4), OMA.P200786.closed (p + 3), OMA.P200786.closed (p + 2), OMA.P200786.closed (p + 1)]
    push_cast
    ring

lemma ofFn4 (v : Fin 4 → ℕ) : List.ofFn v = [v 0, v 1, v 2, v 3] := by
  simp [List.ofFn_succ]
lemma ok4 (p q r s : ℕ) : OMA.Old200786.ok [p, q, r, s] = true ↔ ¬(p < q ∧ q < r) ∧ ¬(q < r ∧ r < s) := by
  simp only [OMA.Old200786.ok]
  by_cases h1 : p < q <;> by_cases h2 : q < r <;> by_cases h3 : r < s <;> simp [h1, h2, h3]
lemma bridge (n : ℕ) : OMA.S_oeis_a200786.a n = OMA.Old200786.a n := by
  unfold OMA.S_oeis_a200786.a OMA.Old200786.a
  apply Finset.card_nbij' (fun p : ℕ × ℕ × ℕ × ℕ => ![p.1, p.2.1, p.2.2.1, p.2.2.2])
    (fun v => (v 0, v 1, v 2, v 3))
  · rintro ⟨x0, x1, x2, x3⟩ hx
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq,
      Fintype.mem_piFinset] at hx ⊢
    refine ⟨fun i => by fin_cases i <;> simp <;> omega, ?_⟩
    rw [ofFn4, ok4]
    show ¬(x0 < x1 ∧ x1 < x2) ∧ ¬(x1 < x2 ∧ x2 < x3); omega
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq,
      Fintype.mem_piFinset] at hv ⊢
    obtain ⟨hr, hv⟩ := hv
    have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; have h3 := hr 3
    rw [ofFn4, ok4] at hv
    omega
  · rintro ⟨x0, x1, x2, x3⟩ _; rfl
  · intro v _; funext i; fin_cases i <;> rfl

lemma rec_new (n : ℕ) (hn : 5 < n) : (OMA.S_oeis_a200786.a n : ℤ) = 5 * OMA.S_oeis_a200786.a (n - 1) - 10 * OMA.S_oeis_a200786.a (n - 2) + 10 * OMA.S_oeis_a200786.a (n - 3) - 5 * OMA.S_oeis_a200786.a (n - 4) + OMA.S_oeis_a200786.a (n - 5) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  simp only [show p + 6 - 1 = p + 5 by omega, show p + 6 - 2 = p + 4 by omega, show p + 6 - 3 = p + 3 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 5 = p + 1 by omega]
  simp only [bridge]
  rw [← @Int.cast_inj ℚ]
  push_cast
  simp only [closed]
  push_cast
  ring

end OMA.P200786

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a200786.main := by
  refine ⟨?_, ?_, OMA.P200786.rec_new⟩
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    simp only [OMA.P200786.bridge]; exact OMA.P200786.gf_old
  · intro n _; rw [OMA.P200786.bridge, OMA.P200786.closed]; ring
