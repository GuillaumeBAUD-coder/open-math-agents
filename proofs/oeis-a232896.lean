import OMAStatements.S_oeis_a232896
import Mathlib.Tactic

/-! At depth d the only new odd number is 2d+1, and it appears first.
After division by two, the even numbers are generated from 1 by increment
and doubling. Appending a binary 0 costs one step and appending a binary 1
costs two. Counting this set by its last bit gives Fibonacci numbers. -/

namespace KimberlingPositions
open OMA.S_oeis_a232896

def binaryBall : ℕ → Finset ℕ
  | 0 => {1}
  | 1 => {1, 2}
  | d+2 => insert 1
      (((binaryBall (d+1)).image (fun y => 2*y)) ∪
       ((binaryBall d).image (fun y => 2*y+1)))

lemma decompose (d x : ℕ) : x ∈ binaryBall (d+2) ↔
    x = 1 ∨ (∃ y ∈ binaryBall (d+1), 2*y = x) ∨ ∃ y ∈ binaryBall d, 2*y+1 = x := by
  simp [binaryBall]

lemma monotoneStep : ∀ d, binaryBall d ⊆ binaryBall (d+1)
  | 0 => by decide
  | 1 => by decide
  | d+2 => by
    intro x hx
    rcases (decompose d x).mp hx with h | ⟨y, hy, he⟩ | ⟨y, hy, he⟩
    · exact (decompose (d+1) x).mpr (Or.inl h)
    · exact (decompose (d+1) x).mpr (Or.inr (Or.inl ⟨y, monotoneStep (d+1) hy, he⟩))
    · exact (decompose (d+1) x).mpr (Or.inr (Or.inr ⟨y, monotoneStep d hy, he⟩))

lemma monotoneBall : Monotone binaryBall :=
  monotone_nat_of_le_succ monotoneStep

lemma oneIn (d : ℕ) : 1 ∈ binaryBall d :=
  monotoneBall (Nat.zero_le d) (by decide : 1 ∈ binaryBall 0)

lemma doubleIn : ∀ d y, y ∈ binaryBall d → 2*y ∈ binaryBall (d+1)
  | 0, y, hy => by
    have : y = 1 := by simpa [binaryBall] using hy
    subst y
    decide
  | d+1, y, hy => (decompose d _).mpr (Or.inr (Or.inl ⟨y, hy, rfl⟩))

lemma oddIn (d y : ℕ) (hy : y ∈ binaryBall d) : 2*y+1 ∈ binaryBall (d+2) :=
  (decompose d _).mpr (Or.inr (Or.inr ⟨y, hy, rfl⟩))

lemma incrementIn : ∀ d y, y ∈ binaryBall d → y+1 ∈ binaryBall (d+1)
  | 0, y, hy => by
    have : y = 1 := by simpa [binaryBall] using hy
    subst y
    decide
  | 1, y, hy => by
    have : y = 1 ∨ y = 2 := by simpa [binaryBall] using hy
    rcases this with rfl | rfl <;> decide
  | d+2, y, hy => by
    rcases (decompose d y).mp hy with rfl | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact doubleIn (d+2) 1 (oneIn _)
    · exact oddIn (d+1) z hz
    · have h := doubleIn (d+2) (z+1) (monotoneStep (d+1) (incrementIn d z hz))
      convert h using 1
      omega

lemma grow (d x : ℕ) : x ∈ binaryBall (d+1) ↔
    x = 1 ∨ (∃ y ∈ binaryBall d, 2*y = x) ∨ ∃ y ∈ binaryBall d, y+1 = x := by
  constructor
  · intro hx
    cases d with
    | zero =>
      have : x = 1 ∨ x = 2 := by simpa [binaryBall] using hx
      rcases this with h | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨1, oneIn _, rfl⟩)
    | succ d =>
      rcases (decompose d x).mp hx with h | h | ⟨y, hy, he⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨2*y, doubleIn d y hy, he⟩)
  · rintro (rfl | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact oneIn _
    · exact doubleIn d y hy
    · exact incrementIn d y hy

lemma positive : ∀ d x, x ∈ binaryBall d → 0 < x
  | 0, x, hx => by
    have : x = 1 := by simpa [binaryBall] using hx
    omega
  | d+1, x, hx => by
    rcases (grow d x).mp hx with rfl | ⟨y, hy, rfl⟩ | ⟨y, _, rfl⟩
    · decide
    · have := positive d y hy
      omega
    · omega

lemma small (d : ℕ) : d+1 ∈ binaryBall d := by
  induction d with
  | zero => decide
  | succ d ih => exact incrementIn d (d+1) ih

lemma oddShortcut (d k : ℕ) (h : k ≤ d) : 2*k+1 ∈ binaryBall (d+1) := by
  cases k with
  | zero => exact oneIn _
  | succ k => exact monotoneBall (show k+2 ≤ d+1 by omega) (oddIn k (k+1) (small k))

lemma throughStep (d x : ℕ) : x ∈ through (d+1) ↔
    x = 1 ∨ x = 2 ∨ ∃ y ∈ through d, x = y+2 ∨ x = 2*y := by
  simp [through, children, List.mem_flatMap]

lemma reached : ∀ d x, x ∈ through d ↔
    (∃ k ≤ d, x = 2*k+1) ∨ ∃ y ∈ binaryBall d, x = 2*y
  | 0, x => by simp [through, binaryBall]
  | d+1, x => by
    rw [throughStep]
    constructor
    · rintro (rfl | rfl | ⟨y, hy, h⟩)
      · exact Or.inl ⟨0, Nat.zero_le _, rfl⟩
      · exact Or.inr ⟨1, oneIn _, rfl⟩
      · rcases (reached d y).mp hy with ⟨k, hk, he⟩ | ⟨k, hk, he⟩
        · rcases h with h | h
          · exact Or.inl ⟨k+1, by omega, by omega⟩
          · exact Or.inr ⟨2*k+1, oddShortcut d k hk, by omega⟩
        · rcases h with h | h
          · exact Or.inr ⟨k+1, incrementIn d k hk, by omega⟩
          · exact Or.inr ⟨2*k, doubleIn d k hk, by omega⟩
    · rintro (⟨k, hk, he⟩ | ⟨k, hk, he⟩)
      · cases k with
        | zero => exact Or.inl (by omega)
        | succ k =>
          exact Or.inr (Or.inr ⟨2*k+1, (reached d _).mpr (Or.inl ⟨k, by omega, rfl⟩),
            Or.inl (by omega)⟩)
      · rcases (grow d k).mp hk with h | ⟨y, hy, h⟩ | ⟨y, hy, h⟩
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr ⟨2*y, (reached d _).mpr (Or.inr ⟨y, hy, rfl⟩),
            Or.inr (by omega)⟩)
        · exact Or.inr (Or.inr ⟨2*y, (reached d _).mpr (Or.inr ⟨y, hy, rfl⟩),
            Or.inl (by omega)⟩)

lemma disjointImages (s t : Finset ℕ) :
    Disjoint (s.image (fun y => 2*y)) (t.image (fun y => 2*y+1)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hy
  omega

lemma doubleInjective : Function.Injective (fun y : ℕ => 2*y) := by
  intro a b h
  change 2*a = 2*b at h
  omega

lemma oddInjective : Function.Injective (fun y : ℕ => 2*y+1) := by
  intro a b h
  change 2*a+1 = 2*b+1 at h
  omega

lemma cardStep (d : ℕ) :
    (binaryBall (d+2)).card = (binaryBall (d+1)).card + (binaryBall d).card + 1 := by
  have h : 1 ∉ ((binaryBall (d+1)).image (fun y => 2*y) ∪
      (binaryBall d).image (fun y => 2*y+1)) := by
    intro h
    rcases Finset.mem_union.mp h with he | ho
    · obtain ⟨y, _, eq⟩ := Finset.mem_image.mp he
      omega
    · obtain ⟨y, hy, eq⟩ := Finset.mem_image.mp ho
      have := positive d y hy
      omega
  rw [binaryBall, Finset.card_insert_of_notMem h, Finset.card_union_of_disjoint (disjointImages _ _),
    Finset.card_image_of_injective _ doubleInjective, Finset.card_image_of_injective _ oddInjective]

lemma cardBall : ∀ d, (binaryBall d).card + 1 = Nat.fib (d+3)
  | 0 => by decide
  | 1 => by decide
  | d+2 => by
    have first := cardBall d
    have second := cardBall (d+1)
    have fib := Nat.fib_add_two (n := d+3)
    rw [cardStep]
    simp only [Nat.add_assoc, Nat.reduceAdd] at second fib ⊢
    omega

lemma throughCard (d : ℕ) : (through d).toFinset.card = d+1+(binaryBall d).card := by
  have setEq : (through d).toFinset =
      (Finset.range (d+1)).image (fun y => 2*y+1) ∪ (binaryBall d).image (fun y => 2*y) := by
    ext x
    rw [List.mem_toFinset, reached, Finset.mem_union]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro (⟨k, hk, e⟩ | ⟨k, hk, e⟩)
      · exact Or.inl ⟨k, by omega, e.symm⟩
      · exact Or.inr ⟨k, hk, e.symm⟩
    · rintro (⟨k, hk, e⟩ | ⟨k, hk, e⟩)
      · exact Or.inl ⟨k, by omega, e.symm⟩
      · exact Or.inr ⟨k, hk, e.symm⟩
  rw [setEq, Finset.card_union_of_disjoint (disjointImages _ _).symm,
    Finset.card_image_of_injective _ oddInjective, Finset.card_image_of_injective _ doubleInjective,
    Finset.card_range]

lemma nextLayer : ∀ d, ∃ tail : List ℕ,
    through (d+1) = through d ++ (2*(d+1)+1)::tail
  | 0 => ⟨[2, 4, 4], rfl⟩
  | d+1 => by
    obtain ⟨tail, h⟩ := nextLayer d
    refine ⟨2*(2*(d+1)+1) :: tail.flatMap children, ?_⟩
    have parentStep := congrArg (fun xs : List ℕ => [1,2] ++ xs.flatMap children) h
    have arithmetic : (2*(d+1)+1)+2 = 2*(d+2)+1 := by omega
    calc
      through (d+2) = [1,2] ++ (through d ++ (2*(d+1)+1)::tail).flatMap children := parentStep
      _ = through (d+1) ++ (2*(d+2)+1)::(2*(2*(d+1)+1))::tail.flatMap children := by
        simp [through, List.flatMap_append, children, arithmetic]

lemma prefixBefore (xs ys : List ℕ) (t : ℕ) (h : t ∉ xs) :
    (xs ++ t::ys).takeWhile (fun y => decide (y ≠ t)) = xs := by
  have all : ∀ v ∈ xs, decide (v ≠ t) = true := by
    intro v hv
    apply decide_eq_true
    rintro rfl
    exact h hv
  rw [List.takeWhile_append_of_pos all]
  simp

lemma explicitTerm : ∀ d : ℕ, term d = (d : ℤ) + (Nat.fib (d+2) : ℤ)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | d+4 => by
    rw [term, explicitTerm (d+3), explicitTerm (d+2), explicitTerm (d+1), explicitTerm d]
    have f0 := Nat.fib_add_two (n := d+2)
    have f1 := Nat.fib_add_two (n := d+3)
    have f2 := Nat.fib_add_two (n := d+4)
    simp only [Nat.add_assoc, Nat.reduceAdd] at f0 f1 f2 ⊢
    omega

lemma oddPosition : ∀ d : ℕ,
    2*d+1 ∈ through d ∧ (position (through d) (2*d+1) : ℤ) = term d
  | 0 => by decide
  | d+1 => by
    obtain ⟨tail, shape⟩ := nextLayer d
    have fresh : 2*(d+1)+1 ∉ through d := by
      intro h
      rcases (reached d _).mp h with ⟨k, hk, eq⟩ | ⟨k, _, eq⟩ <;> omega
    constructor
    · rw [shape]
      simp
    · rw [position, shape, prefixBefore _ _ _ fresh, throughCard, explicitTerm]
      have := cardBall d
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega

end KimberlingPositions

theorem OMA.solution : type_of% @OMA.S_oeis_a232896.main :=
  KimberlingPositions.oddPosition
