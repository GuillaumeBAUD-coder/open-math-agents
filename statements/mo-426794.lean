import Mathlib

namespace OMA.S_mo_426794

open scoped BigOperators Topology
open Filter

/-- The harmonic mass of the block from `a+1` through `b`. -/
noncomputable def blockMass (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico a b, ((i : ℝ) + 1)⁻¹

/-- A position records the previous and current cut, the number of
played blocks, and the signed sum at the current cut. -/
structure Position where
  before : ℕ
  cut : ℕ
  blocks : ℕ
  value : ℝ

noncomputable def opening (k : ℕ) : Position := ⟨0, k, 1, blockMass 0 k⟩

def Allowed (p : Position) (k : ℕ) : Prop :=
  p.cut < k ∧ blockMass p.cut k < blockMass p.before p.cut

noncomputable def advance (p : Position) (k : ℕ) : Position :=
  ⟨p.cut, k, p.blocks + 1, p.value + (-1 : ℝ) ^ p.blocks * blockMass p.cut k⟩

/-- The limit if every future block is a singleton, starting with the current position. -/
noncomputable def stopValue (p : Position) : ℝ :=
  limUnder atTop fun n : ℕ =>
    p.value + (-1 : ℝ) ^ p.blocks *
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((p.cut : ℝ) + i + 1)⁻¹

/-- A finite backward-induction test. At an even block count player 1 moves.
A successful stop uses the singleton move and its forced continuation. -/
def WinsWithin (A : Set ℝ) : ℕ → Position → Prop
  | 0, p => Even p.blocks ∧ stopValue p ∈ A
  | n + 1, p => WinsWithin A n p ∨
      if Even p.blocks then
        ∃ k, Allowed p k ∧ WinsWithin A n (advance p k)
      else
        ∀ k, Allowed p k → WinsWithin A n (advance p k)

def IsPlay (start : Position) (play : ℕ → Position) : Prop :=
  play 0 = start ∧ ∀ n, Allowed (play n) (play (n + 1)).cut ∧
    play (n + 1) = advance (play n) (play (n + 1)).cut

/-- The positions before move `n`, in reverse order. -/
def past (play : ℕ → Position) : ℕ → List Position
  | 0 => []
  | n + 1 => play n :: past play n

/-- The policy may depend on the whole history and chooses a legal cut. -/
def IsLegalPolicy (policy : List Position → ℕ) : Prop :=
  ∀ (p : Position) (earlier : List Position),
    p.before < p.cut → Even p.blocks → Allowed p (policy (p :: earlier))

def Follows (policy : List Position → ℕ) (play : ℕ → Position) : Prop :=
  ∀ n, Even (play n).blocks →
    (play (n + 1)).cut = policy (play n :: past play n)

def PlayerOneWins (A : Set ℝ) : Prop :=
  ∃ k, 0 < k ∧ ∃ policy, IsLegalPolicy policy ∧
    ∀ play, IsPlay (opening k) play → Follows policy play →
      ∃ x ∈ A, Tendsto (fun n => (play n).value) atTop (𝓝 x)

/-- For an open payoff set, player 1 wins exactly when a bounded finite
backward-induction test succeeds after some opening move. Convergence
is tested at block endpoints, as in the author's follow-up. -/
theorem main :
    ∀ A : Set ℝ, A ⊆ Set.Ioi 0 → IsOpen A →
      (PlayerOneWins A ↔ ∃ k, 0 < k ∧ ∃ n, WinsWithin A n (opening k)) := by
  sorry

end OMA.S_mo_426794
