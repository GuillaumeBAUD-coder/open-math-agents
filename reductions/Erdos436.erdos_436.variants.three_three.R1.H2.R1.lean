import OMAReductions.R_Erdos436_erdos_436_variants_three_three_R1
import Mathlib

/-! Split cubic character prescription into its Kummer and Chebotarev ingredients.
The Frobenius congruence forces the fixed cube root of unity into the prime field.
For each radical it then gives the desired character by dividing out its
nonzero residue and taking its cube. -/
namespace OMA.R_Erdos436_erdos_436_variants_three_three_R1_H2_R1
open NumberField

def H1 : Prop := ∀ (v : ℕ → ℕ) (M : ℕ),
  ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : NumberField L) (_ : IsGalois ℚ L)
    (σ : (𝓞 L) ≃+* (𝓞 L)) (u : 𝓞 L), u^2+u+1=0 ∧ σ u = u ∧
      ∀ q : ℕ, q.Prime → q ≤ M → ∃ r : 𝓞 L, r^3 = q ∧ σ r = r * u^(v q)

def H2 : Prop := ∀ (L : Type) [Field L] [CharZero L] [NumberField L] [IsGalois ℚ L]
  (σ : (𝓞 L) ≃+* (𝓞 L)) (B : ℕ), ∃ p > B, p.Prime ∧
    ∃ (F : Type) (_ : Field F) (_ : CharP F p) (φ : 𝓞 L →+* F),
      ∀ x : 𝓞 L, φ (σ x) = (φ x)^p

lemma descend {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (y : F) (hy : y^p=y) : ∃ z : ZMod p, ZMod.castHom (m := p) dvd_rfl F z = y := by
  have h := (Subfield.mem_bot_iff_pow_eq_self F p).mpr hy
  rw [← ZMod.fieldRange_castHom_eq_bot p] at h
  exact h

theorem main : H1 → H2 → OMA.R_Erdos436_erdos_436_variants_three_three_R1.H2 := by
  intro kum frob v M B
  obtain ⟨L,_,_,_,_,σ,u,hu,hs,hr⟩ := kum v M
  obtain ⟨p,hp,hprime,F,_,_,φ,hφ⟩ := frob L σ (max (max B M) 3)
  letI : Fact p.Prime := ⟨hprime⟩
  have hB : B < p := by omega
  have hM : M < p := by omega
  have hp3 : 3 < p := by omega
  let j := ZMod.castHom (m := p) dvd_rfl F
  obtain ⟨z,hz⟩ := descend (φ u) (by rw [← hφ,hs])
  change j z = φ u at hz
  have cz : z^2+z+1 = 0 := j.injective (by
    simpa only [map_add,map_pow,map_one,map_zero,hz] using congrArg φ hu)
  have cube : z^3 = 1 := by linear_combination (z-1)*cz
  have zn : z ≠ 1 := by
    intro ez
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by rw [ez] at cz; linear_combination cz
    have := Nat.le_of_dvd (by decide : 0 < 3) ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
    omega
  have prim : IsPrimitiveRoot z 3 := isPrimitiveRoot_of_mem_nthRootsFinset (by decide)
    ((Polynomial.mem_nthRootsFinset (by decide : 0<3) 1).mpr cube) zn
  have zne : z ≠ 0 := by rintro rfl; simp at cube
  have pd := prim.dvd_of_pow_eq_one (p-1) (ZMod.pow_card_sub_one_eq_one zne)
  refine ⟨p,hB,hprime,pd,z,prim,?_⟩
  intro q hq hqm
  obtain ⟨r,rc,rs⟩ := hr q hq hqm
  have ec : (φ r)^3 = (q : F) := by simpa only [map_pow,map_natCast] using congrArg φ rc
  have en : (q : ZMod p) ≠ 0 := by
    intro he
    exact (not_le_of_gt (hqm.trans_lt hM)) (Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff _ _).mp he))
  have rn : φ r ≠ 0 := by
    intro er
    apply en
    apply j.injective
    simpa [er] using ec.symm
  have ep : (φ r)^(p-1) = (φ u)^(v q) := by
    apply mul_left_cancel₀ rn
    calc
      φ r * (φ r)^(p-1) = (φ r)^p := by rw [← pow_succ',Nat.sub_add_cancel hprime.pos]
      _ = φ (σ r) := (hφ r).symm
      _ = _ := by rw [rs,map_mul,map_pow]
  apply j.injective
  simp only [map_pow,map_natCast,hz,← ec,← pow_mul,Nat.mul_div_cancel' pd,ep]

end OMA.R_Erdos436_erdos_436_variants_three_three_R1_H2_R1
