import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1
import Mathlib.GroupTheory.GroupExtension.Basic

/-!
Fixed outer action, following Lemma 8.8 of Su and Xia, arXiv:2610.11092v1.
Choose compatible lifts in every extension. The factors of two sections with
these lifts have the same inner action, so their differences lie in the center.
Equal factor sets give equivalent extensions via the normal forms n s(h).
-/

namespace Erdos1160.FixedCofactor

section Extensions

variable {N H E : Type*} [Group N] [Group H] [Group E]

private theorem conjugation_on_kernel (S : GroupExtension N E H) (n : N) :
    S.conjAct (S.inl n) = MulAut.conj n := by
  ext t
  apply S.inl_injective
  simp [GroupExtension.inl_conjAct_comm, MulAut.conj_apply]

private noncomputable def factor (S : GroupExtension N E H) (s : S.Section) (h k : H) : N :=
  (s.mul_mul_mul_inv_mem_range_inl h k).choose

private theorem factor_spec (S : GroupExtension N E H) (s : S.Section) (h k : H) :
    S.inl (factor S s h k) = s h * s k * (s (h * k))⁻¹ :=
  (s.mul_mul_mul_inv_mem_range_inl h k).choose_spec

private theorem factor_action (S : GroupExtension N E H) (s : S.Section) (h k : H) :
    MulAut.conj (factor S s h k) =
      S.conjAct (s h) * S.conjAct (s k) * (S.conjAct (s (h * k)))⁻¹ := by
  rw [← conjugation_on_kernel S, factor_spec, map_mul, map_mul, map_inv]

private noncomputable def coordinates (S : GroupExtension N E H) (s : S.Section) : N × H ≃ E :=
  Equiv.ofBijective (fun p => S.inl p.1 * s p.2) (by
    constructor
    · rintro ⟨n, h⟩ ⟨t, k⟩ he
      change S.inl n * s h = S.inl t * s k at he
      have hk := congrArg S.rightHom he
      simp only [map_mul, S.rightHom_inl, one_mul, s.rightHom_section] at hk
      subst k
      exact Prod.ext (S.inl_injective (mul_right_cancel he)) rfl
    · intro e
      have hm : e * (s (S.rightHom e))⁻¹ ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
        simp [s.rightHom_section]
      obtain ⟨n, hn⟩ := hm
      exact ⟨(n, S.rightHom e), by
        change S.inl n * s (S.rightHom e) = e
        rw [hn, inv_mul_cancel_right]⟩)

private theorem coordinates_mul (S : GroupExtension N E H) (s : S.Section) (n t : N) (h k : H) :
    coordinates S s (n, h) * coordinates S s (t, k) =
      coordinates S s (n * S.conjAct (s h) t * factor S s h k, h * k) := by
  change (S.inl n * s h) * (S.inl t * s k) = S.inl _ * s (h * k)
  rw [map_mul, map_mul, S.inl_conjAct_comm, factor_spec]
  simp [mul_assoc]

private noncomputable def equiv_of_same_data {D : Type*} [Group D]
    (S : GroupExtension N E H) (T : GroupExtension N D H) (s : S.Section) (t : T.Section)
    (ha : ∀ h, S.conjAct (s h) = T.conjAct (t h))
    (hf : ∀ h k, factor S s h k = factor T t h k) : S.Equiv T := by
  let e := (coordinates S s).symm.trans (coordinates T t)
  have he (p : N × H) : e (coordinates S s p) = coordinates T t p := by simp [e]
  let f : E ≃* D := { e with
    map_mul' := by
      intro x y
      obtain ⟨⟨n,h⟩, rfl⟩ := (coordinates S s).surjective x
      obtain ⟨⟨v,k⟩, rfl⟩ := (coordinates S s).surjective y
      change e _ = e _ * e _
      rw [coordinates_mul, he, he, he, coordinates_mul, ha, hf] }
  have hcoord (n : N) (h : H) : f (S.inl n * s h) = T.inl n * t h := he (n,h)
  have hsection (h : H) : f (s h) = t h := by simpa using hcoord 1 h
  refine { toMulEquiv := f, inl_comm := ?_, rightHom_comm := ?_ }
  · funext n
    apply mul_right_cancel (b := t 1)
    simpa only [Function.comp_apply, map_mul, hsection] using hcoord n 1
  · funext x
    obtain ⟨⟨n,h⟩, rfl⟩ := (coordinates S s).surjective x
    change T.rightHom (f (S.inl n * s h)) = S.rightHom (S.inl n * s h)
    simp [hcoord, s.rightHom_section, t.rightHom_section]

/-- Inequivalent extensions inducing a common outer action inject into central factor sets. -/
theorem extension_family_encoding {I : Type*}
    {D : I → Type*} [∀ i, Group (D i)] (S : ∀ i, GroupExtension N (D i) H)
    (action : H → MulAut N)
    (outer : ∀ i h, ∃ e : D i, ∃ n : N, (S i).rightHom e = h ∧
      MulAut.conj n * (S i).conjAct e = action h)
    (distinct : ∀ i j, Nonempty ((S i).Equiv (S j)) → i = j) :
    Nonempty (I ↪ (H × H → Subgroup.center N)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hempty =>
    let _ := hempty
    exact ⟨⟨isEmptyElim, fun i => isEmptyElim i⟩⟩
  | inr hnonempty =>
    obtain ⟨i₀⟩ := hnonempty
    have lifts (i : I) (h : H) : ∃ e : D i, (S i).rightHom e = h ∧
        (S i).conjAct e = action h := by
      obtain ⟨e,n,hπ,ha⟩ := outer i h
      exact ⟨(S i).inl n * e, by simp [hπ],
        by rw [map_mul, conjugation_on_kernel, ha]⟩
    let s (i : I) : (S i).Section :=
      ⟨fun h => (lifts i h).choose, fun h => (lifts i h).choose_spec.1⟩
    have act (i : I) (h : H) : (S i).conjAct (s i h) = action h := (lifts i h).choose_spec.2
    let u (i : I) (p : H × H) := factor (S i) (s i) p.1 p.2
    have common (i : I) (p : H × H) : MulAut.conj (u i p) = MulAut.conj (u i₀ p) := by
      simp only [u, factor_action, act]
    have central (i : I) (p : H × H) : (u i₀ p)⁻¹ * u i p ∈ Subgroup.center N := by
      have hone : MulAut.conj ((u i₀ p)⁻¹ * u i p) = 1 := by
        rw [map_mul, map_inv, common i p, inv_mul_cancel]
      apply Subgroup.mem_center_iff.mpr
      intro x
      have hx := congrArg (fun v : MulAut N => v x) hone
      change _ * x * _⁻¹ = x at hx
      exact ((mul_inv_eq_iff_eq_mul).mp hx).symm
    let code (i : I) (p : H × H) : Subgroup.center N := ⟨_, central i p⟩
    have hinj : Function.Injective code := by
      intro i j hij
      apply distinct i j
      apply Nonempty.intro
      apply equiv_of_same_data (S i) (S j) (s i) (s j) (fun h => (act i h).trans (act j h).symm)
      intro h k
      have hh := congrArg (fun z => (z : Subgroup.center N).val) (congrFun hij (h,k))
      exact mul_left_cancel hh
    exact ⟨⟨code, hinj⟩⟩

end Extensions

end Erdos1160.FixedCofactor

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1.H1 := by
  intro N H I D S action outer distinct
  exact Erdos1160.FixedCofactor.extension_family_encoding S action outer distinct
