import OMAStatements.S_oeis_a288309

namespace OMA.S_oeis_a288309




/-! ## Tokens and the reading machine -/

/-- The tokens B = 0010, C = 110, D = 0. -/
inductive U where
  | B | C | D
  deriving DecidableEq

def img : U → List ℕ
  | .B => [0, 0, 1, 0]
  | .C => [1, 1, 0]
  | .D => [0]

def flat (us : List U) : List ℕ := us.flatMap img

/-- The reading machine with a pending zero `c`. -/
def mach : Bool → List U → List U
  | c, [] => if c then [.D] else []
  | false, .B :: t => [.B, .C] ++ mach true t
  | true, .B :: t => [.B, .D, .C] ++ mach true t
  | false, .C :: t => [.C, .C] ++ mach true t
  | true, .C :: t => [.D, .C, .C] ++ mach true t
  | false, .D :: t => mach true t
  | true, .D :: t => [.B] ++ mach false t

def pend (c : Bool) : List ℕ := if c then [0] else []

lemma flat_append (xs ys : List U) : flat (xs ++ ys) = flat xs ++ flat ys := by
  simp [flat]

lemma step_mach : ∀ (us : List U) (c : Bool), step (pend c ++ flat us) = flat (mach c us)
  | [], false => rfl
  | [], true => rfl
  | .B :: t, false => by
    show step (0 :: 0 :: 1 :: 0 :: flat t) = flat ([.B, .C] ++ mach true t)
    rw [flat_append, ← step_mach t true]
    rfl
  | .B :: t, true => by
    show step (0 :: 0 :: 0 :: 1 :: 0 :: flat t) = flat ([.B, .D, .C] ++ mach true t)
    rw [flat_append, ← step_mach t true]
    rfl
  | .C :: t, false => by
    show step (1 :: 1 :: 0 :: flat t) = flat ([.C, .C] ++ mach true t)
    rw [flat_append, ← step_mach t true]
    rfl
  | .C :: t, true => by
    show step (0 :: 1 :: 1 :: 0 :: flat t) = flat ([.D, .C, .C] ++ mach true t)
    rw [flat_append, ← step_mach t true]
    rfl
  | .D :: t, false => by
    show step (0 :: flat t) = flat (mach true t)
    rw [← step_mach t true]
    rfl
  | .D :: t, true => by
    show step (0 :: 0 :: flat t) = flat ([.B] ++ mach false t)
    rw [flat_append, ← step_mach t false]
    rfl

/-! ## Typed tokens -/

/-- Tokens typed by the carry in front of them. -/
inductive Tok where
  | B0 | B1 | C0 | C1 | D0 | D1
  deriving DecidableEq

def typedOf : Bool → List U → List Tok
  | _, [] => []
  | c, .B :: t => (if c then .B1 else .B0) :: typedOf true t
  | c, .C :: t => (if c then .C1 else .C0) :: typedOf true t
  | c, .D :: t => (if c then .D1 else .D0) :: typedOf (!c) t

def carryOut : Bool → List U → Bool
  | c, [] => c
  | _, .B :: t => carryOut true t
  | _, .C :: t => carryOut true t
  | c, .D :: t => carryOut (!c) t

lemma typedOf_append : ∀ (xs ys : List U) (c : Bool),
    typedOf c (xs ++ ys) = typedOf c xs ++ typedOf (carryOut c xs) ys
  | [], _, _ => rfl
  | .B :: t, ys, c => by simp [typedOf, carryOut, typedOf_append t ys true]
  | .C :: t, ys, c => by simp [typedOf, carryOut, typedOf_append t ys true]
  | .D :: t, ys, c => by simp [typedOf, carryOut, typedOf_append t ys (!c)]

lemma carryOut_append : ∀ (xs ys : List U) (c : Bool),
    carryOut c (xs ++ ys) = carryOut (carryOut c xs) ys
  | [], _, _ => rfl
  | .B :: t, ys, _ => by simp [carryOut, carryOut_append t ys true]
  | .C :: t, ys, _ => by simp [carryOut, carryOut_append t ys true]
  | .D :: t, ys, c => by simp [carryOut, carryOut_append t ys (!c)]

/-- The typed image of a typed token when the carry in front of its image is set. -/
def tau : Tok → List Tok
  | .B0 => [.B1, .C1]
  | .B1 => [.B1, .D1, .C0]
  | .C0 => [.C1, .C1]
  | .C1 => [.D1, .C0, .C1]
  | .D0 => []
  | .D1 => [.B1]

lemma typed_mach : ∀ (us : List U) (c : Bool),
    typedOf true (mach c us) = (typedOf c us).flatMap tau ++ (if carryOut c us then [.D1] else []) ∧
    carryOut true (mach c us) = !(carryOut c us)
  | [], false => by simp [mach, typedOf, carryOut]
  | [], true => by simp [mach, typedOf, carryOut]
  | .B :: t, false => by
    obtain ⟨h1, h2⟩ := typed_mach t true
    simp only [mach, typedOf_append, carryOut_append]
    simp [typedOf, carryOut, h1, h2, tau] <;> rfl
  | .B :: t, true => by
    obtain ⟨h1, h2⟩ := typed_mach t true
    simp only [mach, typedOf_append, carryOut_append]
    simp [typedOf, carryOut, h1, h2, tau] <;> rfl
  | .C :: t, false => by
    obtain ⟨h1, h2⟩ := typed_mach t true
    simp only [mach, typedOf_append, carryOut_append]
    simp [typedOf, carryOut, h1, h2, tau] <;> rfl
  | .C :: t, true => by
    obtain ⟨h1, h2⟩ := typed_mach t true
    simp only [mach, typedOf_append, carryOut_append]
    simp [typedOf, carryOut, h1, h2, tau] <;> rfl
  | .D :: t, false => by
    obtain ⟨h1, h2⟩ := typed_mach t true
    simp only [mach]
    simp [typedOf, carryOut, h1, h2, tau]
  | .D :: t, true => by
    obtain ⟨h1, h2⟩ := typed_mach t false
    simp only [mach, typedOf_append, carryOut_append]
    simp [typedOf, carryOut, h1, h2, tau]

/-! ## The iterates -/

/-- The token word after `B`: `iter (n + 1) = flat (.B :: rest n)`. -/
def rest : ℕ → List U
  | 0 => []
  | n + 1 => .C :: mach true (rest n)

lemma iter_succ (n : ℕ) : iter (n + 1) = flat (.B :: rest n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter, Function.iterate_succ_apply', ← iter, ih]
    have := step_mach (.B :: rest n) false
    simp only [pend, Bool.false_eq_true, if_false, List.nil_append] at this
    rw [this]
    rfl

/-- The typed rest. -/
def R (n : ℕ) : List Tok := typedOf true (rest n)

/-- The final carry. -/
def f (n : ℕ) : Bool := carryOut true (rest n)

lemma R_succ (n : ℕ) : R (n + 1) = .C1 :: ((R n).flatMap tau ++ (if f n then [.D1] else [])) := by
  simp only [R, rest, typedOf, if_true]
  rw [(typed_mach (rest n) true).1]
  rfl

lemma f_succ (n : ℕ) : f (n + 1) = !(f n) := by
  simp only [f, rest, carryOut]
  exact (typed_mach (rest n) true).2

/-! ## Counting -/

lemma sum_map_tok (g : Tok → ℕ) : ∀ L : List Tok, (L.map g).sum =
    g .B0 * L.count .B0 + g .B1 * L.count .B1 + g .C0 * L.count .C0 + g .C1 * L.count .C1 +
    g .D0 * L.count .D0 + g .D1 * L.count .D1
  | [] => by simp
  | x :: L => by
    rw [List.map_cons, List.sum_cons, sum_map_tok g L]
    cases x <;> simp [List.count_cons] <;> ring

lemma count_flatMap_tau (L : List Tok) (x : Tok) :
    (L.flatMap tau).count x = (tau .B0).count x * L.count .B0 + (tau .B1).count x * L.count .B1 +
      (tau .C0).count x * L.count .C0 + (tau .C1).count x * L.count .C1 +
      (tau .D0).count x * L.count .D0 + (tau .D1).count x * L.count .D1 := by
  rw [List.count_flatMap]
  exact sum_map_tok (fun t => (tau t).count x) L

/-- Length of a token word from the counts of its typed version. -/
def wt : Tok → ℕ
  | .B0 => 4 | .B1 => 4 | .C0 => 3 | .C1 => 3 | .D0 => 1 | .D1 => 1

lemma length_flat : ∀ (us : List U) (c : Bool), (flat us).length = ((typedOf c us).map wt).sum
  | [], _ => rfl
  | .B :: t, c => by
    have := length_flat t true
    cases c <;> simp [flat, img, typedOf, wt] at this ⊢ <;> omega
  | .C :: t, c => by
    have := length_flat t true
    cases c <;> simp [flat, img, typedOf, wt] at this ⊢ <;> omega
  | .D :: t, c => by
    have := length_flat t (!c)
    cases c <;> simp [flat, img, typedOf, wt] at this ⊢ <;> omega

/-- The counts of the typed rest. -/
def b1 (n : ℕ) : ℕ := (R n).count .B1
def c0 (n : ℕ) : ℕ := (R n).count .C0
def c1 (n : ℕ) : ℕ := (R n).count .C1
def d1 (n : ℕ) : ℕ := (R n).count .D1
def fv (n : ℕ) : ℕ := if f n then 1 else 0

lemma fv_succ (n : ℕ) : fv (n + 1) + fv n = 1 := by
  unfold fv
  rw [f_succ]
  cases f n <;> rfl

lemma fv_le (n : ℕ) : fv n ≤ 1 := by
  unfold fv
  split <;> omega

lemma tr (n : ℕ) : (R (n + 1)).count .B0 = 0 ∧ (R (n + 1)).count .D0 = 0 ∧
    b1 (n + 1) = (R n).count .B0 + b1 n + d1 n ∧ c0 (n + 1) = b1 n + c1 n ∧
    c1 (n + 1) = 1 + (R n).count .B0 + 2 * c0 n + c1 n ∧ d1 (n + 1) = b1 n + c1 n + fv n := by
  simp only [b1, c0, c1, d1, fv]
  rw [R_succ]
  simp only [List.count_cons, List.count_append, count_flatMap_tau]
  cases f n <;> simp [tau] <;> omega

lemma inv (n : ℕ) : (R n).count .B0 = 0 ∧ (R n).count .D0 = 0 ∧
    2 * b1 n + d1 n = c0 n + c1 n ∧ c1 n + fv n = 2 * b1 n + 1 := by
  induction n with
  | zero => simp [R, rest, typedOf, b1, c0, c1, d1, fv, f, carryOut]
  | succ n ih =>
    obtain ⟨h0, h0', h1, h2⟩ := ih
    obtain ⟨t0, t0', tb, tc0, tc1, td⟩ := tr n
    have hf := fv_succ n
    refine ⟨t0, t0', ?_, ?_⟩ <;> omega

lemma trans (n : ℕ) : b1 (n + 1) + fv n = b1 n + c0 n + 1 ∧ c0 (n + 1) + fv n = 3 * b1 n + 1 ∧
    fv (n + 1) + fv n = 1 := by
  obtain ⟨h0, h0', h1, h2⟩ := inv n
  obtain ⟨t0, t0', tb, tc0, tc1, td⟩ := tr n
  refine ⟨by omega, by omega, fv_succ n⟩

lemma len_iter (n : ℕ) : ((iter (n + 1)).length : ℤ) =
    8 + 10 * b1 n + 4 * c0 n - 4 * fv n := by
  have hlen : (iter (n + 1)).length = 4 + ((R n).map wt).sum := by
    rw [iter_succ]
    show (img .B ++ flat (rest n)).length = _
    rw [List.length_append, length_flat (rest n) true]
    rfl
  rw [hlen, sum_map_tok]
  obtain ⟨h0, h0', h1, h2⟩ := inv n
  simp only [b1, c0, c1, d1, wt] at h1 h2 ⊢
  rw [h0, h0']
  push_cast
  omega

lemma len_rec (n : ℕ) : ((iter (n + 4)).length : ℤ) = 2 * (iter (n + 3)).length +
    2 * (iter (n + 2)).length - 3 * (iter (n + 1)).length := by
  rw [len_iter (n + 3), len_iter (n + 2), len_iter (n + 1), len_iter n]
  obtain ⟨t1, t2, t3⟩ := trans n
  obtain ⟨u1, u2, u3⟩ := trans (n + 1)
  obtain ⟨v1, v2, v3⟩ := trans (n + 2)
  have e1 : ((b1 (n + 1) : ℕ) : ℤ) + fv n = b1 n + c0 n + 1 := by exact_mod_cast t1
  have e2 : ((c0 (n + 1) : ℕ) : ℤ) + fv n = 3 * b1 n + 1 := by exact_mod_cast t2
  have e3 : ((fv (n + 1) : ℕ) : ℤ) + fv n = 1 := by exact_mod_cast t3
  have e4 : ((b1 (n + 2) : ℕ) : ℤ) + fv (n + 1) = b1 (n + 1) + c0 (n + 1) + 1 := by exact_mod_cast u1
  have e5 : ((c0 (n + 2) : ℕ) : ℤ) + fv (n + 1) = 3 * b1 (n + 1) + 1 := by exact_mod_cast u2
  have e6 : ((fv (n + 2) : ℕ) : ℤ) + fv (n + 1) = 1 := by exact_mod_cast u3
  have e7 : ((b1 (n + 3) : ℕ) : ℤ) + fv (n + 2) = b1 (n + 2) + c0 (n + 2) + 1 := by exact_mod_cast v1
  have e8 : ((c0 (n + 3) : ℕ) : ℤ) + fv (n + 2) = 3 * b1 (n + 2) + 1 := by exact_mod_cast v2
  have e9 : ((fv (n + 3) : ℕ) : ℤ) + fv (n + 2) = 1 := by exact_mod_cast v3
  linarith

/-- Kimberling's conjecture: the n-th iterate has a(n) letters. -/
theorem conjecture : ∀ n : ℕ, ((iter n).length : ℤ) = A n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | k + 4 =>
      rw [len_rec k, A, ih (k + 3) (by omega), ih (k + 2) (by omega), ih (k + 1) (by omega)]

/-- Controls: the iterates 00, 0010, 00101100 and a(0..6) = 2, 4, 8, 18, 40, 92, 210. -/
example : iter 1 = [0, 0, 1, 0] ∧ iter 2 = [0, 0, 1, 0, 1, 1, 0, 0] ∧
    (List.range 7).map (fun n => (iter n).length) = [2, 4, 8, 18, 40, 92, 210] := by
  decide +kernel

end OMA.S_oeis_a288309

theorem OMA.solution : type_of% @OMA.S_oeis_a288309.main :=
  OMA.S_oeis_a288309.conjecture
