import FormalConjectures.Wikipedia.BusyBeaver
import Mathlib.Tactic

/-!
# Reduction of `BusyBeaver.BB_5`

Following H. Marxen & J. Buntrock (*Attacking the Busy Beaver 5*, Bull. EATCS 40 (1990), 247–251)
and The Busy Beaver Challenge (*Determination of the fifth Busy Beaver number*, 2024), we reduce
`BusyBeaver.BB 5 = 47176870` to three independent pillars in Tree Normal Form (TNF):
1. `H1`: **Marxen–Buntrock 5-state champion (lower bound)**: there exists a halting 5-state
   2-symbol Turing machine `M : Machine (Fin 2) (Fin 5)` with `M.haltingNumber = 47176870`.
2. `H2`: **Upper bound for `1RB`-normalized machines**: every halting 5-state 2-symbol machine
   `M : Machine (Fin 2) (Fin 5)` with initial transition `M 0 0 = some (some 1, Stmt.write 1 Dir.right)`
   satisfies `M.haltingNumber ≤ 47176870`.
3. `H3`: **Upper bound for `0RB`-normalized machines**: every halting 5-state 2-symbol machine
   `M : Machine (Fin 2) (Fin 5)` with initial transition `M 0 0 = some (some 1, Stmt.write 0 Dir.right)`
   satisfies `M.haltingNumber ≤ 47176870`.

Inside `main`, we prove from scratch:
- **Alphabet/state normalization** (following @Genbox's `sanity_check` transport): every
  `Candidate 5` transfers to an equivalent `Machine (Fin 2) (Fin 5)` preserving `IsHalting` and
  `haltingNumber`.
- **Left–right tape reflection symmetry**: reflecting tape streams (`left ↔ right`) and flipping
  `Dir.left ↔ Dir.right` preserves `IsHalting` and `haltingNumber`.
- **Immediate halting bounds** for `M 0 0 = none` (`haltingNumber = 0`) and
  `M 0 0 = some (none, _)` (`haltingNumber ≤ 1`).
- **Self-loop non-halting theorem**: if `M 0 0 = some (some 0, _)`, an inductive blank-half-tape
  invariant proves `M` never halts, contradicting `M.IsHalting`.
- **Tree Normal Form reduction**: permuting the target state `q ≠ 0` to `1` (fixing `0`) and
  reflecting direction `Dir.left` to `Dir.right` routes every remaining halting machine into `H2`
  (`1RB`) or `H3` (`0RB`), concluding `BB 5 = 47176870` via `IsGreatest.csSup_eq`.

Thanks to @Genbox and @ldy985 for the Turing machine transport and `Candidate` normalization
patterns in this repository.
Credit: @tkaiman
-/

namespace OMA.R_BusyBeaver_BB_5_R1

open Turing Turing.BusyBeaver

private def trM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (e₂ : Λ ≃ Λ') (M : Machine Γ Λ) : Machine Γ' Λ' :=
  fun q a => (M (e₂.symm q) (e₁.symm a)).map
    fun p => (p.1.map e₂, Stmt.write (e₁ p.2.symbol) p.2.dir)

private def cmapM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (c : Cfg Γ Λ) : Cfg Γ' Λ' :=
  ⟨c.q.map e₂, c.tape.map ⟨e₁, h₁⟩⟩

private lemma step_trM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ]
    [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    (trM e₁ e₂ M).step (cmapM e₁ h₁ e₂ c) = (M.step c).map (cmapM e₁ h₁ e₂) := by
  rcases c with ⟨_ | q, T⟩
  · rfl
  · simp only [cmapM, Option.map_some, Machine.step, trM, Tape.map_fst]
    change ((M (e₂.symm (e₂ q)) (e₁.symm (e₁ T.head))).map _).map _ = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases M q T.head with _ | ⟨q', ⟨s, d⟩⟩
    · rfl
    · simp only [Option.map_some, Option.some.injEq]
      ext
      · rfl
      · show _ = Tape.map ⟨e₁, h₁⟩ (Tape.move d (Tape.write s T))
        rw [Tape.map_move, Tape.map_write]

private lemma multiStep_trM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ]
    [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (M : Machine Γ Λ) (c : Cfg Γ Λ)
    (n : ℕ) :
    (trM e₁ e₂ M).multiStep (cmapM e₁ h₁ e₂ c) n = (M.multiStep c n).map (cmapM e₁ h₁ e₂) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    rcases M.multiStep c n with _ | c'
    · rfl
    · simp only [Option.map_some, Option.bind_some, step_trM]

private lemma init_trM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ]
    [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (h₂ : e₂ default = default) :
    cmapM e₁ h₁ e₂ (Machine.init []) = Machine.init [] := by
  simp only [cmapM, Machine.init, Option.map_some, h₂, Tape.map_mk₁, List.map_nil]

private lemma haltsAfter_trM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ]
    [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (h₂ : e₂ default = default)
    (M : Machine Γ Λ) (n : ℕ) :
    (trM e₁ e₂ M).HaltsAfter (Machine.init []) n ↔ M.HaltsAfter (Machine.init []) n := by
  simp only [Machine.HaltsAfter, ← init_trM e₁ h₁ e₂ h₂, multiStep_trM, Option.map_eq_none_iff]

private lemma haltingNumber_trM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ]
    [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (h₂ : e₂ default = default)
    (M : Machine Γ Λ) :
    (trM e₁ e₂ M).haltingNumber = M.haltingNumber := by
  simp only [Machine.haltingNumber, haltsAfter_trM e₁ h₁ e₂ h₂]

private lemma isHalting_trM {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ]
    [Inhabited Γ'] [Inhabited Λ']
    (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (h₂ : e₂ default = default)
    (M : Machine Γ Λ) (hM : M.IsHalting) : (trM e₁ e₂ M).IsHalting := by
  have h := (Machine.isHalting_iff_exists_haltsAt M).mp hM
  rw [Machine.isHalting_iff_exists_haltsAt]
  simpa only [haltsAfter_trM e₁ h₁ e₂ h₂] using h

private def flipDir : Dir → Dir
  | Dir.left => Dir.right
  | Dir.right => Dir.left

private def revTape {Γ : Type*} [Inhabited Γ] (T : Tape Γ) : Tape Γ :=
  ⟨T.head, T.right, T.left⟩

private def revCfg {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (c : Cfg Γ Λ) : Cfg Γ Λ :=
  ⟨c.q, revTape c.tape⟩

private def flipM {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) : Machine Γ Λ :=
  fun q a => (M q a).map fun p => (p.1, Stmt.write p.2.symbol (flipDir p.2.dir))

private lemma step_flipM {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    (flipM M).step (revCfg c) = (M.step c).map revCfg := by
  rcases c with ⟨_ | q, ⟨hd, tl, tr⟩⟩
  · rfl
  · simp only [revCfg, revTape, Machine.step, flipM]
    rcases M q hd with _ | ⟨q', ⟨s, d⟩⟩
    · rfl
    · cases d <;> rfl

private lemma multiStep_flipM {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    (flipM M).multiStep (revCfg c) n = (M.multiStep c n).map revCfg := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    rcases M.multiStep c n with _ | c'
    · rfl
    · simp only [Option.map_some, Option.bind_some, step_flipM]

private lemma haltsAfter_flipM {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (n : ℕ) :
    (flipM M).HaltsAfter (Machine.init []) n ↔ M.HaltsAfter (Machine.init []) n := by
  have hinit : revCfg (Machine.init ([] : List Γ) : Cfg Γ Λ) = Machine.init [] := rfl
  rw [Machine.HaltsAfter, Machine.HaltsAfter]
  nth_rw 1 [← hinit]
  rw [multiStep_flipM, Option.map_eq_none_iff]

private lemma haltingNumber_flipM {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) :
    (flipM M).haltingNumber = M.haltingNumber := by
  simp only [Machine.haltingNumber, haltsAfter_flipM]

private lemma isHalting_flipM {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (hM : M.IsHalting) : (flipM M).IsHalting := by
  have h := (Machine.isHalting_iff_exists_haltsAt M).mp hM
  rw [Machine.isHalting_iff_exists_haltsAt]
  simpa only [haltsAfter_flipM] using h

private lemma not_isHalting_of_self_loop_right (M : Machine (Fin 2) (Fin 5)) (s : Fin 2)
    (h00 : M 0 0 = some (some 0, Stmt.write s Dir.right)) : ¬ M.IsHalting := by
  have hinv : ∀ n : ℕ, ∃ c : Cfg (Fin 2) (Fin 5),
      M.multiStep (Machine.init []) n = some c ∧
      c.q = some 0 ∧ c.tape.head = 0 ∧ c.tape.right = ListBlank.mk [] := by
    intro n
    induction n with
    | zero =>
      refine ⟨Machine.init [], rfl, rfl, rfl, rfl⟩
    | succ n ih =>
      obtain ⟨⟨cq, ⟨hd, tl, tr⟩⟩, hstep, hq, hhd, htr⟩ := ih
      simp only at hq hhd htr
      subst hq; subst hhd; subst htr
      refine ⟨⟨some 0, ⟨(ListBlank.mk ([] : List (Fin 2))).head, tl.cons s,
        (ListBlank.mk ([] : List (Fin 2))).tail⟩⟩, ?_, rfl, rfl, rfl⟩
      rw [Machine.multiStep_succ, hstep]
      simp only [Option.bind_some, Machine.step, h00, Option.map_some]
      rfl
  intro hhalt
  obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hhalt
  obtain ⟨c, hc, _, _, _⟩ := hinv (n + 1)
  rw [Machine.HaltsAfter] at hn
  rw [hn] at hc
  cases hc

private lemma exists_equiv_fin {α : Type} [Fintype α] [Inhabited α] {n : ℕ} [NeZero n]
    (h : Fintype.card α = n) : ∃ e : α ≃ Fin n, e default = default := by
  let e0 := Fintype.equivFinOfCardEq h
  exact ⟨e0.trans (Equiv.swap (e0 default) default), by simp⟩

/-- **Marxen–Buntrock 5-state Busy Beaver champion (lower bound)**:
there exists a halting 5-state 2-symbol Turing machine `M : Machine (Fin 2) (Fin 5)` with
`M.haltingNumber = 47176870`. -/
def H1 : Prop :=
  ∃ M : Turing.BusyBeaver.Machine (Fin 2) (Fin 5),
    M.IsHalting ∧ M.haltingNumber = (47176870 : ℕ)

/-- **Busy Beaver Challenge upper bound for `1RB`-normalized 5-state machines**:
every halting 5-state 2-symbol Turing machine `M : Machine (Fin 2) (Fin 5)` with initial
transition `M 0 0 = some (some 1, Stmt.write 1 Dir.right)` halts in at most `47176870` steps. -/
def H2 : Prop :=
  ∀ M : Turing.BusyBeaver.Machine (Fin 2) (Fin 5),
    M 0 0 = some (some 1, Turing.BusyBeaver.Stmt.write 1 Turing.Dir.right) →
    M.IsHalting → M.haltingNumber ≤ (47176870 : ℕ)

/-- **Busy Beaver Challenge upper bound for `0RB`-normalized 5-state machines**:
every halting 5-state 2-symbol Turing machine `M : Machine (Fin 2) (Fin 5)` with initial
transition `M 0 0 = some (some 1, Stmt.write 0 Dir.right)` halts in at most `47176870` steps. -/
def H3 : Prop :=
  ∀ M : Turing.BusyBeaver.Machine (Fin 2) (Fin 5),
    M 0 0 = some (some 1, Turing.BusyBeaver.Stmt.write 0 Turing.Dir.right) →
    M.IsHalting → M.haltingNumber ≤ (47176870 : ℕ)

theorem main : H1 → H2 → H3 → type_of% @BusyBeaver.BB_5 := by
  intro h1 h2 h3
  obtain ⟨M0, hM0_halt, hM0_num⟩ := h1
  show sSup {N : ℕ | ∃ C : BusyBeaver.Candidate 5, C.M.haltingNumber = ↑N} = 47176870
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · -- Lower bound witness from H1
    refine ⟨{
      Γ := Fin 2
      Λ := Fin 5
      Γ_fintype := inferInstance
      Γ_card := Fintype.card_fin 2
      Γ_inhabited := inferInstance
      Λ_fintype := inferInstance
      Λ_card := Fintype.card_fin 5
      Λ_inhabited := inferInstance
      M := M0
      M_isHalting := hM0_halt
    }, hM0_num⟩
  · -- Upper bound for every Candidate 5 via normalization + reflection + TNF
    rintro N ⟨C, hC⟩
    obtain ⟨e₁, h₁⟩ := exists_equiv_fin C.Γ_card
    obtain ⟨e₂, h₂⟩ := exists_equiv_fin C.Λ_card
    let M : Machine (Fin 2) (Fin 5) := trM e₁ e₂ C.M
    have hM_halt : M.IsHalting := isHalting_trM e₁ h₁ e₂ h₂ C.M C.M_isHalting
    have hM_num : M.haltingNumber = (N : ENat) := by
      rw [haltingNumber_trM e₁ h₁ e₂ h₂, hC]
    suffices hle : M.haltingNumber ≤ ((47176870 : ℕ) : ENat) by
      rw [hM_num] at hle
      exact_mod_cast hle
    -- Normalize direction of initial transition to Dir.right
    have hbound_dir : ∀ M' : Machine (Fin 2) (Fin 5), M'.IsHalting →
        (∀ q s d, M' 0 0 = some (q, Stmt.write s d) → d = Dir.right) →
        M'.haltingNumber ≤ ((47176870 : ℕ) : ENat) := by
      intro M' hM'_halt hdir
      rcases h00 : M' 0 0 with _ | ⟨q', ⟨s, d⟩⟩
      · -- Halts immediately at step 0
        have hhd : (Tape.mk₁ ([] : List (Fin 2))).head = 0 := rfl
        have h0 : M'.HaltsAfter (Machine.init []) 0 := by
          simp [Machine.HaltsAfter, Machine.multiStep, Machine.step, Machine.init, hhd, h00]
        have hle0 : M'.haltingNumber ≤ (0 : ℕ) := sInf_le ⟨0, h0, rfl⟩
        exact le_trans hle0 (by norm_num)
      · have hd : d = Dir.right := hdir q' s d h00
        subst hd
        rcases q' with _ | q
        · -- Halts in 1 step
          have hhd : (Tape.mk₁ ([] : List (Fin 2))).head = 0 := rfl
          have h1 : M'.HaltsAfter (Machine.init []) 1 := by
            simp [Machine.HaltsAfter, Machine.multiStep, Machine.step, Machine.init, hhd, h00]
          have hle1 : M'.haltingNumber ≤ (1 : ℕ) := sInf_le ⟨1, h1, rfl⟩
          exact le_trans hle1 (by norm_num)
        · by_cases hq0 : q = 0
          · -- Self-loop on blank right half-tape: impossible for halting machine
            subst hq0
            exact absurd hM'_halt (not_isHalting_of_self_loop_right M' s h00)
          · -- Relabel state q to 1 (fixing 0) and dispatch to H2 (s = 1) or H3 (s = 0)
            let eΛ : Fin 5 ≃ Fin 5 := Equiv.swap q 1
            have heΛ0 : eΛ default = default := by
              change Equiv.swap q 1 0 = 0
              exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hq0) (by decide)
            let M'' : Machine (Fin 2) (Fin 5) := trM (Equiv.refl (Fin 2)) eΛ M'
            have hM''_halt : M''.IsHalting := isHalting_trM _ rfl eΛ heΛ0 M' hM'_halt
            have hM''_num : M''.haltingNumber = M'.haltingNumber :=
              haltingNumber_trM _ rfl eΛ heΛ0 M'
            have hM''_00 : M'' 0 0 = some (some 1, Stmt.write s Dir.right) := by
              have hsymm0 : eΛ.symm 0 = 0 := by
                change Equiv.swap q 1 0 = 0
                exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hq0) (by decide)
              dsimp [M'', trM]
              rw [hsymm0, h00]
              simp [eΛ]
            rw [← hM''_num]
            fin_cases s
            · exact h3 M'' hM''_00 hM''_halt
            · exact h2 M'' hM''_00 hM''_halt
    rcases h00 : M 0 0 with _ | ⟨q', ⟨s, d⟩⟩
    · exact hbound_dir M hM_halt (fun _ _ _ h => by rw [h00] at h; cases h)
    · cases d with
      | right =>
        exact hbound_dir M hM_halt (fun _ _ _ h => by rw [h00] at h; cases h; rfl)
      | left =>
        rw [← haltingNumber_flipM M]
        refine hbound_dir (flipM M) (isHalting_flipM M hM_halt) fun _ _ _ h => ?_
        dsimp [flipM] at h
        rw [h00] at h
        cases h
        rfl

end OMA.R_BusyBeaver_BB_5_R1
