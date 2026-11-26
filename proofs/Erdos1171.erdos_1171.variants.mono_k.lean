import FormalConjectures.ErdosProblems.«1171»

-- Problem: Erdős Problem 1171 — mono k
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1171.lean:62 (declaration Erdos1171.erdos_1171.variants.mono_k)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Note: upstream states mono_k with two universe parameters (hypothesis in u_1, conclusion in u_2),
-- so the proof first transfers the partition relation across universes along an order isomorphism
-- of the two copies of ω₁², then drops colours with Fin.castLE.

open Cardinal Ordinal

universe u v

namespace OMA

def imageRelIso {X : Type u} {Y : Type v} [LinearOrder X] [LinearOrder Y]
    (e : X ≃o Y) (A : Set X) :
    ((· < ·) : A → A → Prop) ≃r ((· < ·) : (e '' A) → (e '' A) → Prop) where
  toEquiv := e.toEquiv.image A
  map_rel_iff' := by
    intro a b
    show e a.1 < e b.1 ↔ a < b
    exact e.lt_iff_lt

lemma transfer {α : Ordinal.{u}} {α' : Ordinal.{v}} {β : Ordinal.{u}} {β' : Ordinal.{v}}
    {γ : Cardinal.{u}} {γ' : Cardinal.{v}} {k : ℕ}
    (e : α.ToType ≃o α'.ToType)
    (hβ : Ordinal.lift.{v} β = Ordinal.lift.{u} β')
    (hγ : Cardinal.lift.{v} γ = Cardinal.lift.{u} γ')
    (h : OrdinalMultiColorRamsey α β γ k) : OrdinalMultiColorRamsey α' β' γ' k := by
  intro col
  rcases h (fun s => col (s.map e)) with ⟨A, hA, hAβ⟩ | ⟨i, A, hA, hAγ⟩
  · left
    refine ⟨e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have := hA x hx y hy (fun h => hxy (by rw [h]))
      simpa using this
    · apply Ordinal.lift_inj.{u, v}.1
      rw [← hβ, ← hAβ]
      exact (Ordinal.lift_type_eq.{v, u, 0}).2 ⟨(imageRelIso e A).symm⟩
  · right
    refine ⟨i, e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have := hA x hx y hy (fun h => hxy (by rw [h]))
      simpa using this
    · apply Cardinal.lift_inj.{v, u}.1
      rw [← hγ, ← hAγ]
      exact (Cardinal.lift_mk_eq'.2 ⟨e.toEquiv.image A⟩).symm

lemma liftX : Ordinal.lift.{v} (ω_ 1 ^ 2 : Ordinal.{u}) = ω_ 1 ^ 2 := by
  simp [pow_two, Ordinal.lift_omega]

lemma liftB : Ordinal.lift.{v} (ω_ 1 * ω : Ordinal.{u}) = ω_ 1 * ω := by
  simp [Ordinal.lift_omega]

noncomputable def isoX : (ω_ 1 ^ 2 : Ordinal.{u}).ToType ≃o (ω_ 1 ^ 2 : Ordinal.{v}).ToType := by
  have h : Ordinal.lift.{v} (Ordinal.type ((· < ·) : (ω_ 1 ^ 2 : Ordinal.{u}).ToType → _ → Prop)) =
      Ordinal.lift.{u} (Ordinal.type ((· < ·) : (ω_ 1 ^ 2 : Ordinal.{v}).ToType → _ → Prop)) := by
    rw [Ordinal.type_toType, Ordinal.type_toType, liftX, liftX]
  exact OrderIso.ofRelIsoLT (Classical.choice ((Ordinal.lift_type_eq.{u, v, 0}).1 h))

lemma monoK {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2 : Ordinal.{v}) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2 : Ordinal.{v}) (ω_ 1 * ω) 3 j := by
  intro col
  have hle : j + 1 ≤ k + 1 := Nat.succ_le_succ hjk
  rcases hk (fun e => Fin.castLE hle (col e)) with ⟨A, hA, hβ⟩ | ⟨i, A, hA, hγ⟩
  · left
    refine ⟨A, fun x hx y hy hxy => ?_, hβ⟩
    apply Fin.ext
    have h := congrArg Fin.val (hA x hx y hy hxy)
    simpa using h
  · right
    have h1 : (1 : Cardinal) < #A := by
      rw [hγ]
      exact_mod_cast (by norm_num : (1 : ℕ) < 3)
    rw [Cardinal.one_lt_iff_nontrivial] at h1
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h1.exists_pair_ne
    have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
    have hi : i.val < j := by
      have h := congrArg Fin.val (hA x hx y hy hxy')
      simp at h
      have := (col s(x, y)).isLt
      omega
    refine ⟨⟨i.val, hi⟩, A, fun a ha b hb hab => ?_, hγ⟩
    apply Fin.ext
    have h := congrArg Fin.val (hA a ha b hb hab)
    simpa using h

end OMA

theorem OMA.solution : type_of% @Erdos1171.erdos_1171.variants.mono_k := by
  intro j k hjk hk
  apply OMA.monoK hjk
  refine OMA.transfer OMA.isoX ?_ ?_ hk
  · rw [OMA.liftB, OMA.liftB]
  · simp

