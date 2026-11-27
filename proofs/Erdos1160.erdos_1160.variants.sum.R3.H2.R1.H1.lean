import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1
import Mathlib

/-! Choose sections with the prescribed action on the kernel. Their
multiplication factors differ from a fixed reference by central elements.
Equal central differences identify the coordinate multiplication laws and
give an equivalence of the extensions. -/

namespace OMA.ExtensionCount

open GroupExtension

private theorem conj_inl {N E G : Type*} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G) (n : N) :
    S.conjAct (S.inl n) = MulAut.conj n := by
  ext x
  apply S.inl_injective
  simp [S.inl_conjAct_comm,MulAut.conj_apply]

private theorem normal_product {N X G : Type*} [Group N] [Group X] [Group G]
    (U : GroupExtension N X G) (u : U.Section) (A : G → MulAut N) (c : G → G → N)
    (hAct : ∀ g, U.conjAct (u g) = A g)
    (hCoc : ∀ g h, U.inl (c g h) = u g * u h * (u (g*h))⁻¹)
    (a b : N) (g h : G) :
    (U.inl a * u g) * (U.inl b * u h) =
      U.inl (a * A g b * c g h) * u (g*h) := by
  rw [map_mul,map_mul,← hAct g,U.inl_conjAct_comm,hCoc]
  group

private theorem extension_equiv_of_coordinates {N E F G : Type*}
    [Group N] [Group E] [Group F] [Group G]
    (S : GroupExtension N E G) (T : GroupExtension N F G)
    (s : S.Section) (t : T.Section) (hs : s 1 = 1) (ht : t 1 = 1)
    (A : G → MulAut N) (c : G → G → N)
    (hSA : ∀ g, S.conjAct (s g) = A g) (hTA : ∀ g, T.conjAct (t g) = A g)
    (hSc : ∀ g h, S.inl (c g h) = s g * s h * (s (g*h))⁻¹)
    (hTc : ∀ g h, T.inl (c g h) = t g * t h * (t (g*h))⁻¹) :
    Nonempty (S.Equiv T) := by
  classical
  let getN (x : E) : N := Function.invFun S.inl (x * (s (S.rightHom x))⁻¹)
  have hgN (x : E) : S.inl (getN x) = x * (s (S.rightHom x))⁻¹ := by
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range,S.range_inl_eq_ker_rightHom,MonoidHom.mem_ker]
    simp
  have hNormal (x : E) : S.inl (getN x) * s (S.rightHom x) = x := by
    rw [hgN,inv_mul_cancel_right]
  have hProj (a : N) (g : G) : S.rightHom (S.inl a * s g) = g := by simp
  let phi (x : E) : F := T.inl (getN x) * t (S.rightHom x)
  have hGet (a : N) (g : G) : getN (S.inl a * s g) = a := by
    apply S.inl_injective
    rw [hgN,hProj]
    group
  have hphi (a : N) (g : G) : phi (S.inl a * s g) = T.inl a * t g := by
    simp only [phi,hProj,hGet]
  have hLeft (a : N) : phi (S.inl a) = T.inl a := by simpa [hs,ht] using hphi a 1
  let f : E →* F := {
    toFun := phi
    map_one' := by simpa using hLeft 1
    map_mul' := by
      intro x y
      have hx : ∃ a g, S.inl a * s g = x := ⟨getN x,S.rightHom x,hNormal x⟩
      have hy : ∃ a g, S.inl a * s g = y := ⟨getN y,S.rightHom y,hNormal y⟩
      obtain ⟨a,g,rfl⟩ := hx
      obtain ⟨b,h,rfl⟩ := hy
      calc
        phi ((S.inl a * s g) * (S.inl b * s h)) =
            phi (S.inl (a * A g b * c g h) * s (g*h)) :=
          congrArg phi (normal_product S s A c hSA hSc a b g h)
        _ = T.inl (a * A g b * c g h) * t (g*h) := hphi _ _
        _ = (T.inl a * t g) * (T.inl b * t h) := (normal_product T t A c hTA hTc a b g h).symm
        _ = _ := by rw [hphi,hphi] }
  refine ⟨GroupExtension.Equiv.ofMonoidHom f ?_ ?_⟩
  · ext a
    exact hLeft a
  · ext x
    change T.rightHom (phi x) = S.rightHom x
    simp [phi]

theorem inject_factor_systems (N G : Type*) [Group N] [Group G]
    (I : Type*) (E : I → Type*) [∀ i, Group (E i)]
    (S : ∀ i, GroupExtension N (E i) G) (action : G → MulAut N)
    (hAct : ∀ i g, ∃ e : E i, ∃ n : N, (S i).rightHom e = g ∧
      MulAut.conj n * (S i).conjAct e = action g)
    (hEq : ∀ i j, Nonempty ((S i).Equiv (S j)) → i = j) :
    Nonempty (I ↪ (G × G → Subgroup.center N)) := by
  classical
  by_cases hI : Nonempty I
  swap
  · exact ⟨⟨fun i => (hI ⟨i⟩).elim,fun i _ _ => (hI ⟨i⟩).elim⟩⟩
  obtain ⟨i₀⟩ := hI
  choose e n he hn using hAct
  let A (g : G) : MulAut N := if g=1 then 1 else action g
  let s (i : I) : (S i).Section := {
    toFun := fun g => if g=1 then 1 else (S i).inl (n i g) * e i g
    rightInverse_rightHom := by
      intro g
      by_cases hg : g=1 <;> simp [hg,he] }
  have hs (i : I) : s i 1 = 1 := by simp [s]
  have hSA (i : I) (g : G) : (S i).conjAct (s i g) = A g := by
    by_cases hg : g=1
    · simp [A,hg,hs]
    · simpa [A,s,hg,conj_inl] using hn i g
  have hExists (i : I) (g h : G) : ∃ v : N,
      (S i).inl v = s i g * s i h * (s i (g*h))⁻¹ :=
    (s i).mul_mul_mul_inv_mem_range_inl g h
  choose c hc using hExists
  have hConj (i : I) (g h : G) :
      MulAut.conj (c i g h) = A g * A h * (A (g*h))⁻¹ := by
    rw [← conj_inl (S i),hc,map_mul,map_mul,map_inv,hSA,hSA,hSA]
  let classify (i : I) (p : G × G) : Subgroup.center N := ⟨c i p.1 p.2 * (c i₀ p.1 p.2)⁻¹,by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hC : MulAut.conj (c i p.1 p.2 * (c i₀ p.1 p.2)⁻¹) = 1 := by
      rw [map_mul,map_inv,hConj,hConj,mul_inv_cancel]
    have hEval := congrArg (fun a : MulAut N => a g) hC
    rw [MulAut.conj_apply,MulAut.one_apply] at hEval
    exact (mul_inv_eq_iff_eq_mul.mp hEval).symm⟩
  refine ⟨⟨classify,?_⟩⟩
  intro i j h
  apply hEq i j
  have hC (g h' : G) : c i g h' = c j g h' := by
    have hSame := congrArg (fun f : G × G → Subgroup.center N => (f (g,h')).val) h
    change c i g h' * (c i₀ g h')⁻¹ = c j g h' * (c i₀ g h')⁻¹ at hSame
    exact mul_right_cancel hSame
  apply extension_equiv_of_coordinates (S i) (S j) (s i) (s j) (hs i) (hs j)
    A (c i) (hSA i) (hSA j) (hc i)
  intro g h'
  rw [hC,hc]

end OMA.ExtensionCount


theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1.H1 := by
  intro N H I D S action hAct hEq
  exact OMA.ExtensionCount.inject_factor_systems N H I (fun i => D i) S action hAct hEq
