import OMAStatements.S_oeis_a288260
import Mathlib

-- Problem: A288260: a(n) = 2*a(n-1) + 2*a(n-3) - 3*a(n-4), where a(0) = 2, a(1) = 4, a(2) = 8, a(3) = 16.
-- Upstream: formal-conjectures statements/oeis-a288260.lean:0 (declaration OMA.S_oeis_a288260.main)
-- Credit: @jmtdev0 (the owner of the agent is credited as the solver)
--
-- Proof idea, the same for both rules.
-- Cut a word into blocks 0^k 1, followed by a few final zeros. A pass acts on each block on its own
-- (`Jg`), and the image of every block ends with the same zeros (two for Rule A, one for Rule B),
-- which belong to the next block. Moving those zeros across (`Js`) turns the pass into a
-- substitution `s` on blocks. So `word (n + 1)` is exactly a first block, a list of blocks and some
-- final zeros (`we`), the final zeros going through a cycle of three. The number of blocks of each
-- size then follows a linear map (`cs`), and four steps of it give the recurrence of `reference`
-- (`fo`, used through `R`).
--
-- Names, kept short on purpose. In each rule: `T` blocks (`a`, `b`, `c`, `d` are 0^k 1 for
-- k = 1, 2, 3, 4), `P` the three states of the final zeros, `r` the pass, `f` the bits of a block,
-- `g` its image under a pass, `s` the substitution, `t` the final zeros, `e` the blocks they turn
-- into, `v` the next state, `N` one pass on a described word, `q n` the description of
-- `word (n + 1)`, `L` its length.

open OMA.S_oeis_a288260

namespace K

abbrev O := false
abbrev I := true

/-- `J f X`: the concatenation of `f b` over the blocks `b` of `X`. -/
def J {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | b :: X => f b ++ J f X

theorem Ja {α β : Type} (f : α → List β) (X Y : List α) : J f (X ++ Y) = J f X ++ J f Y := by
  induction X with
  | nil => rfl
  | cons b X ih => simp [J, ih]

/-- A pass that acts block by block acts on a list of blocks. -/
theorem Jg {α : Type} {r : List Bool → List Bool} {f g : α → List Bool}
    (k : ∀ b w, r (f b ++ w) = g b ++ r w) (X : List α) (w : List Bool) :
    r (J f X ++ w) = J g X ++ r w := by
  induction X with
  | nil => rfl
  | cons b X ih =>
    show r ((f b ++ J f X) ++ w) = (g b ++ J g X) ++ r w
    rw [List.append_assoc, k, ih, List.append_assoc]

/-- Moving the zeros `z` that end every image across a list of blocks. -/
theorem Js {α : Type} {z : List Bool} {f g : α → List Bool} {s : α → List α}
    (h : ∀ b, z ++ g b = J f (s b) ++ z) (X : List α) : z ++ J g X = J f (J s X) ++ z := by
  induction X with
  | nil => simp [J]
  | cons b X ih =>
    show z ++ (g b ++ J g X) = J f (s b ++ J s X) ++ z
    rw [← List.append_assoc, h, List.append_assoc, ih, Ja, List.append_assoc]

/-- A sequence with the first values and the four-step identity is `reference`, shifted by one. -/
theorem R (l : ℕ → ℕ) (h0 : l 0 = 4) (h1 : l 1 = 8) (h2 : l 2 = 16) (h3 : l 3 = 34)
    (h : ∀ n, l (n + 4) + 3 * l n = 2 * l (n + 3) + 2 * l (n + 1)) (n : ℕ) :
    reference (n + 1) = l n ∧ reference (n + 2) = l (n + 1) ∧ reference (n + 3) = l (n + 2) ∧
      reference (n + 4) = l (n + 3) := by
  induction n with
  | zero => simp [reference, h0, h1, h2, h3]
  | succ n ih =>
    obtain ⟨a, b, c, d⟩ := ih
    have e : reference (n + 5) =
        2 * reference (n + 4) + 2 * reference (n + 2) - 3 * reference (n + 1) := rfl
    have := h n
    exact ⟨b, c, d, by show reference (n + 5) = (l (n + 4) : ℤ); omega⟩

/-! ### Rule A: 1 becomes 100, 00 becomes 0010, any other 0 is kept -/

namespace A

inductive T
  | a | b | c | d
  deriving DecidableEq

inductive P
  | x | y | z

abbrev r := RuleA.rewrite

def f : T → List Bool
  | .a => [O, I]
  | .b => [O, O, I]
  | .c => [O, O, O, I]
  | .d => [O, O, O, O, I]

def g : T → List Bool
  | .a => [O, I, O, O]
  | .b => [O, O, I, O, I, O, O]
  | .c => [O, O, I, O, O, I, O, O]
  | .d => [O, O, I, O, O, O, I, O, I, O, O]

def s : T → List T
  | .a => [.c]
  | .b => [.d, .a]
  | .c => [.d, .b]
  | .d => [.d, .c, .a]

def t : P → List Bool
  | .x => [O]
  | .y => [O, O, O]
  | .z => [O, O]

def e : P → List T
  | .x => []
  | _ => [.d]

def v : P → P
  | .x => .y
  | .y => .z
  | .z => .x

theorem k (b : T) (w : List Bool) : r (f b ++ w) = g b ++ r w := by cases b <;> rfl

theorem h (b : T) : [O, O] ++ g b = J f (s b) ++ [O, O] := by cases b <;> rfl

theorem tq (p : P) : [O, O] ++ r (t p) = J f (e p) ++ t (v p) := by cases p <;> rfl

/-- One pass, on the word with first block `b`, blocks `X` and final zeros `t p`. -/
theorem sp (X : List T) (p : P) :
    r (J f (.b :: X) ++ t p) = J f (.b :: .a :: (J s X ++ e p)) ++ t (v p) := by
  rw [Jg k]
  simp only [J, Ja, List.append_assoc]
  rw [← tq, ← List.append_assoc (J f (J s X)), ← Js h]
  simp [g, f]

def N (w : List T × P) : List T × P := (.a :: (J s w.1 ++ e w.2), v w.2)

def q : ℕ → List T × P
  | 0 => ([], .x)
  | n + 1 => N (q n)

theorem we (n : ℕ) : RuleA.word (n + 1) = J f (.b :: (q n).1) ++ t (q n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show r (RuleA.word (n + 1)) = J f (.b :: .a :: (J s (q n).1 ++ e (q n).2)) ++ t (v (q n).2)
    rw [ih, sp]

theorem lf (X : List T) :
    (J f X).length = 2 * X.count .a + 3 * X.count .b + 4 * X.count .c + 5 * X.count .d := by
  induction X with
  | nil => rfl
  | cons b X ih => cases b <;> simp [J, f, List.count_cons, ih] <;> omega

theorem cs (X : List T) :
    (J s X).count .a = X.count .b + X.count .d ∧ (J s X).count .b = X.count .c ∧
    (J s X).count .c = X.count .a + X.count .d ∧
    (J s X).count .d = X.count .b + X.count .c + X.count .d := by
  induction X with
  | nil => simp [J]
  | cons b X ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    cases b <;> simp [J, s, List.count_cons, List.count_append, h1, h2, h3, h4] <;> omega

def L (w : List T × P) : ℕ :=
  3 + (2 * w.1.count .a + 3 * w.1.count .b + 4 * w.1.count .c + 5 * w.1.count .d) + (t w.2).length

theorem lw (n : ℕ) : (RuleA.word (n + 1)).length = L (q n) := by
  rw [we, List.length_append, lf]
  simp [L, List.count_cons]
  omega

/-- Four passes: the recurrence, as an identity in the numbers of blocks. -/
theorem fo (w : List T × P) : L (N (N (N (N w)))) + 3 * L w = 2 * L (N (N (N w))) + 2 * L (N w) := by
  obtain ⟨X, p⟩ := w
  cases p <;> simp [L, N, v, e, t, List.count_cons, List.count_append, cs] <;> omega

theorem le (n : ℕ) : ((RuleA.word n).length : ℤ) = reference n := by
  cases n with
  | zero => rfl
  | succ n => rw [lw, (R (fun n => L (q n)) rfl rfl rfl rfl (fun n => fo (q n)) n).1]

end A

/-! ### Rule B: 1 becomes 010, 00 becomes 0101, any other 0 is kept -/

namespace B

inductive T
  | a | b | c
  deriving DecidableEq

inductive P
  | x | y | z

abbrev r := RuleB.rewrite

def f : T → List Bool
  | .a => [O, I]
  | .b => [O, O, I]
  | .c => [O, O, O, I]

def g : T → List Bool
  | .a => [O, O, I, O]
  | .b => [O, I, O, I, O, I, O]
  | .c => [O, I, O, I, O, O, I, O]

def s : T → List T
  | .a => [.c]
  | .b => [.b, .a, .a]
  | .c => [.b, .a, .b]

def t : P → List Bool
  | .x => []
  | .y => [O]
  | .z => [O, O]

def e : P → List T
  | .z => [.b, .a]
  | _ => []

def v : P → P
  | .x => .y
  | .y => .z
  | .z => .x

/-- The first block: `a` and `b` in turn. -/
def H : Bool → T
  | false => .a
  | true => .b

/-- The blocks that the first block gives, after the new first block. -/
def pr : Bool → List T
  | false => []
  | true => [.a, .a]

theorem k (b : T) (w : List Bool) : r (f b ++ w) = g b ++ r w := by cases b <;> rfl

theorem h (b : T) : [O] ++ g b = J f (s b) ++ [O] := by cases b <;> rfl

theorem tq (p : P) : [O] ++ r (t p) = J f (e p) ++ t (v p) := by cases p <;> rfl

theorem hd (c : Bool) : g (H c) = f (H (!c)) ++ (J f (pr c) ++ [O]) := by cases c <;> rfl

/-- One pass, on the word with first block `H c`, blocks `X` and final zeros `t p`. -/
theorem sp (c : Bool) (X : List T) (p : P) :
    r (J f (H c :: X) ++ t p) = J f (H (!c) :: (pr c ++ (J s X ++ e p))) ++ t (v p) := by
  rw [Jg k]
  simp only [J, Ja, List.append_assoc]
  rw [hd, ← tq, ← List.append_assoc (J f (J s X)), ← Js h]
  simp

def N (w : Bool × List T × P) : Bool × List T × P :=
  (!w.1, pr w.1 ++ (J s w.2.1 ++ e w.2.2), v w.2.2)

def q : ℕ → Bool × List T × P
  | 0 => (false, [.a], .x)
  | n + 1 => N (q n)

theorem we (n : ℕ) : RuleB.word (n + 1) = J f (H (q n).1 :: (q n).2.1) ++ t (q n).2.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show r (RuleB.word (n + 1)) =
      J f (H (!(q n).1) :: (pr (q n).1 ++ (J s (q n).2.1 ++ e (q n).2.2))) ++ t (v (q n).2.2)
    rw [ih, sp]

theorem lf (X : List T) : (J f X).length = 2 * X.count .a + 3 * X.count .b + 4 * X.count .c := by
  induction X with
  | nil => rfl
  | cons b X ih => cases b <;> simp [J, f, List.count_cons, ih] <;> omega

theorem cs (X : List T) :
    (J s X).count .a = 2 * X.count .b + X.count .c ∧
    (J s X).count .b = X.count .b + 2 * X.count .c ∧ (J s X).count .c = X.count .a := by
  induction X with
  | nil => simp [J]
  | cons b X ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    cases b <;> simp [J, s, List.count_cons, List.count_append, h1, h2, h3] <;> omega

def L (w : Bool × List T × P) : ℕ :=
  (f (H w.1)).length + (2 * w.2.1.count .a + 3 * w.2.1.count .b + 4 * w.2.1.count .c) +
    (t w.2.2).length

theorem lw (n : ℕ) : (RuleB.word (n + 1)).length = L (q n) := by
  rw [we]
  simp [L, J, lf]
  omega

/-- Four passes: the recurrence, as an identity in the numbers of blocks. -/
theorem fo (w : Bool × List T × P) :
    L (N (N (N (N w)))) + 3 * L w = 2 * L (N (N (N w))) + 2 * L (N w) := by
  obtain ⟨c, X, p⟩ := w
  cases c <;> cases p <;>
    simp [L, N, v, e, t, pr, H, f, List.count_cons, List.count_append, cs] <;> omega

theorem le (n : ℕ) : ((RuleB.word n).length : ℤ) = reference n := by
  cases n with
  | zero => rfl
  | succ n => rw [lw, (R (fun n => L (q n)) rfl rfl rfl rfl (fun n => fo (q n)) n).1]

end B

end K

theorem OMA.solution : type_of% @OMA.S_oeis_a288260.main :=
  fun n => ⟨K.A.le n, K.B.le n⟩
