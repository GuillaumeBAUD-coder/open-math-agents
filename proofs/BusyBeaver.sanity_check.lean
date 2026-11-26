import FormalConjectures.Wikipedia.BusyBeaver

-- Problem: Busy Beaver — sanity check
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/BusyBeaver.lean:67 (declaration BusyBeaver.sanity_check)
-- Credit: @Genbox (the owner of the agent is credited as the solver)

namespace OMABB
open Turing Turing.BusyBeaver

section
variable {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ']

def tr (e₁ : Γ ≃ Γ') (e₂ : Λ ≃ Λ') (M : Machine Γ Λ) : Machine Γ' Λ' :=
  fun q a => (M (e₂.symm q) (e₁.symm a)).map
    (fun p => (p.1.map e₂, Stmt.write (e₁ p.2.symbol) p.2.dir))

def pm (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) : PointedMap Γ Γ' := ⟨e₁, h₁⟩

def cmap (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (c : Cfg Γ Λ) : Cfg Γ' Λ' :=
  ⟨c.q.map e₂, c.tape.map (pm e₁ h₁)⟩

theorem step_tr (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ') (M : Machine Γ Λ)
    (c : Cfg Γ Λ) : (tr e₁ e₂ M).step (cmap e₁ h₁ e₂ c) = (M.step c).map (cmap e₁ h₁ e₂) := by
  rcases c with ⟨_ | q, T⟩
  · rfl
  · simp only [cmap, Option.map_some, Machine.step, tr, Tape.map_fst]
    have : (pm e₁ h₁) T.head = e₁ T.head := rfl
    rw [this, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases M q T.head with _ | ⟨q', ⟨s, d⟩⟩
    · rfl
    · simp only [Option.map_some, Option.some.injEq]
      ext
      · rfl
      · show _ = Tape.map (pm e₁ h₁) (Tape.move d (Tape.write s T))
        rw [Tape.map_move, Tape.map_write]; rfl

theorem multiStep_tr (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ')
    (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    (tr e₁ e₂ M).multiStep (cmap e₁ h₁ e₂ c) n = (M.multiStep c n).map (cmap e₁ h₁ e₂) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    rcases M.multiStep c n with _ | c'
    · rfl
    · simp only [Option.map_some, Option.bind_some, step_tr]

theorem init_tr (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ')
    (h₂ : e₂ default = default) : cmap e₁ h₁ e₂ (Machine.init []) = Machine.init [] := by
  simp only [cmap, Machine.init, Option.map_some, h₂, Tape.map_mk₁, List.map_nil]

theorem haltsAfter_tr (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ')
    (h₂ : e₂ default = default) (M : Machine Γ Λ) (n : ℕ) :
    (tr e₁ e₂ M).HaltsAfter (Machine.init []) n ↔ M.HaltsAfter (Machine.init []) n := by
  simp only [Machine.HaltsAfter, ← init_tr e₁ h₁ e₂ h₂, multiStep_tr, Option.map_eq_none_iff]

theorem haltingNumber_tr (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ')
    (h₂ : e₂ default = default) (M : Machine Γ Λ) :
    (tr e₁ e₂ M).haltingNumber = M.haltingNumber := by
  simp only [Machine.haltingNumber, haltsAfter_tr e₁ h₁ e₂ h₂]

theorem isHalting_tr (e₁ : Γ ≃ Γ') (h₁ : e₁ default = default) (e₂ : Λ ≃ Λ')
    (h₂ : e₂ default = default) (M : Machine Γ Λ) [M.IsHalting] : (tr e₁ e₂ M).IsHalting := by
  have h := (Machine.isHalting_iff_exists_haltsAt M).mp ‹_›
  rw [Machine.isHalting_iff_exists_haltsAt]
  simpa only [haltsAfter_tr e₁ h₁ e₂ h₂] using h

end

theorem exists_equiv {α : Type} [Fintype α] [Inhabited α] {n : ℕ} [NeZero n]
    (h : Fintype.card α = n) : ∃ e : α ≃ Fin n, e default = default := by
  let e0 := Fintype.equivFinOfCardEq h
  refine ⟨e0.trans (Equiv.swap (e0 default) default), ?_⟩
  simp

theorem hn_ne_top {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ) [M.IsHalting] :
    M.haltingNumber ≠ ⊤ := by
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp ‹_›
  have : M.haltingNumber ≤ k := sInf_le ⟨k, hk, rfl⟩
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top k) this

instance finStmt : Finite (Stmt (Fin 2)) :=
  Finite.of_surjective (fun p : Fin 2 × Bool => Stmt.write p.1 (if p.2 then Dir.left else Dir.right))
    (by
      rintro ⟨a, d⟩
      cases d
      · exact ⟨(a, true), rfl⟩
      · exact ⟨(a, false), rfl⟩)

theorem main (n : ℕ) [NeZero n] :
    BusyBeaver.BB n = sSup {N | ∃ (M : Machine (Fin 2) (Fin n)) (_ : M.IsHalting),
      M.haltingNumber = N} := by
  unfold BusyBeaver.BB
  set S := {N : ℕ | ∃ C : BusyBeaver.Candidate n, C.M.haltingNumber = ↑N} with hS
  have hset : {N | ∃ (M : Machine (Fin 2) (Fin n)) (_ : M.IsHalting), M.haltingNumber = N}
      = (fun k : ℕ => (k : ℕ∞)) '' S := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_image, hS]
    constructor
    · rintro ⟨M, hM, hN⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hn_ne_top M)
      refine ⟨k, ⟨⟨Fin 2, Fin n, inferInstance, by simp, inferInstance, inferInstance, by simp,
        inferInstance, M, hM⟩, hk.symm⟩, ?_⟩
      rw [hk, hN]
    · rintro ⟨k, ⟨C, hC⟩, rfl⟩
      obtain ⟨e₁, h₁⟩ := exists_equiv C.Γ_card
      obtain ⟨e₂, h₂⟩ := exists_equiv C.Λ_card
      have := C.M_isHalting
      exact ⟨tr e₁ e₂ C.M, isHalting_tr e₁ h₁ e₂ h₂ C.M, by rw [haltingNumber_tr e₁ h₁ e₂ h₂]; exact hC⟩
  have hfin : Finite (Machine (Fin 2) (Fin n)) := by
    unfold Machine; infer_instance
  have hbdd : BddAbove S := by
    have hsub : (fun k : ℕ => (k : ℕ∞)) '' S ⊆
        Set.range (fun M : Machine (Fin 2) (Fin n) => M.haltingNumber) := by
      rw [← hset]
      rintro _ ⟨M, _, rfl⟩
      exact ⟨M, rfl⟩
    have hf : ((fun k : ℕ => (k : ℕ∞)) '' S).Finite := (Set.finite_range _).subset hsub
    exact (Set.Finite.of_finite_image hf (fun a _ b _ h => by exact_mod_cast h)).bddAbove
  rw [hset, ENat.natCast_sSup hbdd, sSup_image]

end OMABB

theorem OMA.solution : type_of% @BusyBeaver.sanity_check := fun n _ => OMABB.main n
