import OMAStatements.S_mo_143188
import Mathlib

open Set Topology

open OMA.S_mo_143188



theorem OMA.solution : type_of% @OMA.S_mo_143188.main := by
  intro E _ _ _ _ _ _ _ _ _ _ hDimension h
  obtain ⟨U, hOpen, ⟨e⟩⟩ := h
  have hU : U.Nonempty := ⟨(e fun _ => 1).val,(e fun _ => 1).property⟩
  have hRange : range (fun x : ℕ → Circle => (e x).val) = U := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact (e x).property
    · intro hy
      obtain ⟨x, hx⟩ := e.surjective ⟨y,hy⟩
      exact ⟨x,congrArg Subtype.val hx⟩
  have hCompact : IsCompact U := by
    rw [←hRange]
    exact isCompact_range (continuous_subtype_val.comp e.continuous)
  have hPath : IsPathConnected (univ : Set E) :=
    (convex_univ : Convex ℝ (univ : Set E)).isPathConnected univ_nonempty
  let _ : PreconnectedSpace E := ⟨hPath.isConnected.isPreconnected⟩
  have hFull : U = univ :=
    (show IsClopen U from ⟨hCompact.isClosed,hOpen⟩).eq_univ hU
  have hAll : IsCompact (univ : Set E) := hFull ▸ hCompact
  have ha : ∃ a : E, a ≠ 0 := by
    by_contra! hAllZero
    let _ : Subsingleton E := ⟨fun a b => (hAllZero a).trans (hAllZero b).symm⟩
    exact hDimension inferInstance
  obtain ⟨a,ha⟩ := ha
  let line : ℝ →ₗ[ℝ] E := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight a
  have hInjective : Function.Injective line := by
    intro s t he
    change s • a = t • a at he
    have hz : (s-t) • a = 0 := by rw [sub_smul,he,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right ha)
  have hClosed := line.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hInjective)
  have hReal : IsCompact (univ : Set ℝ) := by
    simpa only [preimage_univ] using hClosed.isCompact_preimage hAll
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) ⟨hReal⟩
