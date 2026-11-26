import FormalConjectures.Wikipedia.BusyBeaver

-- Problem: Busy Beaver — BB 1
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/BusyBeaver.lean:74 (declaration BusyBeaver.BB_1)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Turing BusyBeaver

namespace OMA

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

lemma init_eq : (Machine.init [] : Cfg Γ Λ) =
    ⟨some default, ⟨default, ListBlank.mk [], ListBlank.mk []⟩⟩ := rfl

/-- A one-state machine that keeps moving right never leaves the blank part of the tape. -/
lemma loop_right (M : Machine Γ Λ) [Subsingleton Λ] (q' : Λ) (a : Γ)
    (h : M default default = some (some q', Stmt.write a Dir.right)) (k : ℕ) :
    ∃ L, M.multiStep (Machine.init []) k =
      some ⟨some default, ⟨default, L, ListBlank.mk []⟩⟩ := by
  induction k with
  | zero => exact ⟨ListBlank.mk [], rfl⟩
  | succ k ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨ListBlank.cons a L, ?_⟩
    rw [Machine.multiStep_succ, hL, Option.bind_some]
    simp only [Machine.step, h, Option.map_some, Subsingleton.elim q' default, Tape.write,
      Tape.move, ListBlank.head_mk, ListBlank.tail_mk, List.headI_nil, List.tail_nil]

/-- A one-state machine that keeps moving left never leaves the blank part of the tape. -/
lemma loop_left (M : Machine Γ Λ) [Subsingleton Λ] (q' : Λ) (a : Γ)
    (h : M default default = some (some q', Stmt.write a Dir.left)) (k : ℕ) :
    ∃ R, M.multiStep (Machine.init []) k =
      some ⟨some default, ⟨default, ListBlank.mk [], R⟩⟩ := by
  induction k with
  | zero => exact ⟨ListBlank.mk [], rfl⟩
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨ListBlank.cons a R, ?_⟩
    rw [Machine.multiStep_succ, hR, Option.bind_some]
    simp only [Machine.step, h, Option.map_some, Subsingleton.elim q' default, Tape.write,
      Tape.move, ListBlank.head_mk, ListBlank.tail_mk, List.headI_nil, List.tail_nil]

lemma haltingNumber_top (M : Machine Γ Λ)
    (h : ∀ k, M.multiStep (Machine.init []) k ≠ none) : M.haltingNumber = ⊤ := by
  unfold Machine.haltingNumber
  rw [sInf_eq_top]
  rintro _ ⟨n, hn, rfl⟩
  exact absurd hn (h (n + 1))

/-- Every one-state machine halts after 0 or 1 steps, or never. -/
lemma haltingNumber_le_one (M : Machine Γ Λ) [Subsingleton Λ] (N : ℕ)
    (hN : M.haltingNumber = N) : N ≤ 1 := by
  rcases hM : M default default with _ | ⟨_ | q', ⟨a, d⟩⟩
  · have : M.haltingNumber = (0 : ℕ) := by
      apply Machine.haltingNumber_def
      · exact ⟨_, rfl⟩
      · simp [Machine.multiStep_succ, init_eq, Machine.step, hM]
    rw [this] at hN
    have := (Nat.cast_inj (R := ℕ∞)).1 hN
    omega
  · have : M.haltingNumber = (1 : ℕ) := by
      apply Machine.haltingNumber_def
      · simp [Machine.multiStep_succ, init_eq, Machine.step, hM]
      · simp [Machine.multiStep_succ, init_eq, Machine.step, hM]
    rw [this] at hN
    have := (Nat.cast_inj (R := ℕ∞)).1 hN
    omega
  · have : M.haltingNumber = ⊤ := by
      apply haltingNumber_top
      intro k
      cases d with
      | left => obtain ⟨R, hR⟩ := loop_left M q' a hM k; simp [hR]
      | right => obtain ⟨L, hL⟩ := loop_right M q' a hM k; simp [hL]
    rw [this] at hN; exact absurd hN.symm (ENat.natCast_ne_top N)

/-- The machine that halts after one step. -/
def oneStep : Machine Bool Unit := fun _ _ => some (none, Stmt.write default Dir.right)

instance oneStep_isHalting : oneStep.IsHalting := by
  constructor
  unfold Machine.IsHaltingInput Machine.eval
  rw [Part.map_Dom, Part.dom_iff_mem]
  refine ⟨⟨none, (Tape.mk₁ []).move Dir.right⟩, StateTransition.mem_eval.2 ⟨?_, rfl⟩⟩
  exact Relation.ReflTransGen.single rfl

lemma oneStep_haltingNumber : oneStep.haltingNumber = (1 : ℕ) := by
  apply Machine.haltingNumber_def
  · simp [Machine.multiStep_succ, init_eq, Machine.step, oneStep]
  · simp [Machine.multiStep_succ, init_eq, Machine.step, oneStep]

def oneStepCandidate : Candidate 1 where
  Γ := Bool
  Λ := Unit
  Γ_fintype := inferInstance
  Γ_card := rfl
  Γ_inhabited := inferInstance
  Λ_fintype := inferInstance
  Λ_card := rfl
  Λ_inhabited := inferInstance
  M := oneStep
  M_isHalting := oneStep_isHalting

end OMA

theorem OMA.solution : type_of% @BusyBeaver.BB_1 := by
  unfold BusyBeaver.BB
  have bound : ∀ N ∈ {N : ℕ | ∃ C : Candidate 1, C.M.haltingNumber = N}, N ≤ 1 := by
    rintro N ⟨C, hC⟩
    have : Subsingleton C.Λ := Fintype.card_le_one_iff_subsingleton.1 C.Λ_card.le
    exact OMA.haltingNumber_le_one C.M N hC
  have mem : 1 ∈ {N : ℕ | ∃ C : Candidate 1, C.M.haltingNumber = N} :=
    ⟨OMA.oneStepCandidate, OMA.oneStep_haltingNumber⟩
  exact le_antisymm (csSup_le ⟨1, mem⟩ bound) (le_csSup ⟨1, bound⟩ mem)
