import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-! The integer-unit norm of an unramified local extension is surjective. The supporting local-field declarations are adapted from ClassFieldTheory, revision 2e6280f9d2579705a0cc6c76ec68c2b60f9c601a, https://github.com/n-yamaguchi-0729/ClassFieldTheory. Selected declarations are combined and imports replaced by their dependency declarations below. -/
/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/- ValuedFieldTheory.LocalField.NormUnits -/
section
namespace LocalFieldTheory
noncomputable section
universe u v w
variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]
 
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)
 
@[simp]
theorem normUnits_apply_coe (x : Lˣ) :
    ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension -/
section
namespace Valuation
end Valuation
namespace LocalFieldTheory
noncomputable section
universe u v
open scoped ValuativeRel
 


class ValuativeExtension (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] : Prop where
   

  integer_isIntegral : ∀ x : 𝒪[L], IsIntegral 𝒪[K] (x : L)
 

instance valuativeExtensionOfIsIntegralClosure
    (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    ValuativeExtension K L where
  integer_isIntegral x :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2 ⟨x, rfl⟩
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic -/
section
namespace LocalFieldTheory
noncomputable section
universe u
namespace IsNonarchimedeanLocalField
open scoped ValuativeRel WithZero
 



noncomputable def v (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ → Int :=
  fun x =>
    Multiplicative.toAdd
      (WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
        (by simp))
 

@[simp]
theorem v_apply (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    v K x =
      Multiplicative.toAdd
        (WithZero.unzero
          (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
            (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
          (by simp)) :=
  rfl
 
@[simp]
theorem v_one (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    v K (Additive.ofMul (1 : Kˣ)) = 0 := by
  dsimp [v]
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (((1 : Kˣ) : K))))
        (by simp) = (1 : Multiplicative Int) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    simp
  rw [hunzero]
  exact toAdd_one
 
def integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] : 𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K).toMonoidHom
 

@[simp]
theorem integerUnitsToFieldUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    ((integerUnitsToFieldUnits K x : Kˣ) : K) = (((x : 𝒪[K]ˣ) : 𝒪[K]) : K) :=
  rfl
 
@[simp]
theorem v_integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]ˣ) :
    v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0 := by
  have hxv :
      ValuativeRel.valuation K ((integerUnitsToFieldUnits K x : Kˣ) : K) = 1 := by
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) x)
  rw [v_apply]
  apply (WithZero.toAdd_unzero_eq_iff _ 0).2
  change
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
        (ValuativeRel.valuation K
          ((integerUnitsToFieldUnits K x : Kˣ) : K)) =
      ((Multiplicative.ofAdd (0 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int))
  rw [hxv, map_one]
  rfl
end IsNonarchimedeanLocalField
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm -/
section
namespace LocalFieldTheory
noncomputable section
universe u v
namespace IsNonarchimedeanLocalField
open scoped BigOperators ValuativeRel
variable {K : Type u} {L : Type v}
section AlgebraNorm
variable [Field K] [Field L] [Algebra K L] [Module.Free K L] [Module.Finite K L]
end AlgebraNorm
section UnitNorm
variable [Field K] [Field L] [Algebra K L]
 
def mapBaseUnitsToExtensionUnits
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom
 

@[simp]
lemma mapBaseUnitsToExtensionUnits_apply_coe (x : Kˣ) :
    ((mapBaseUnitsToExtensionUnits K L x : Lˣ) : L) = algebraMap K L (x : K) :=
  rfl
 
lemma algebraNorm_mem_integers_of_mem_integers [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]) :
    Algebra.norm K (x : L) ∈ 𝒪[K] := by
  exact Valuation.Integers.mem_of_integral
    (Valuation.integer.integers (ValuativeRel.valuation K))
    (Algebra.isIntegral_norm K (LocalFieldTheory.ValuativeExtension.integer_isIntegral x))
 
def normIntegerUnitsValue [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) : 𝒪[K] :=
  ⟨Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L),
    algebraNorm_mem_integers_of_mem_integers ((x : 𝒪[L]ˣ) : 𝒪[L])⟩
 
lemma normIntegerUnitsValue_mul_inv [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x *
      normIntegerUnitsValue (K := K) (L := L) x⁻¹ = 1 := by
  ext
  change Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x * x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]
 
lemma normIntegerUnitsValue_inv_mul [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x⁻¹ *
      normIntegerUnitsValue (K := K) (L := L) x = 1 := by
  ext
  change Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x⁻¹ * x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]
 
def normIntegerUnits
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [LocalFieldTheory.ValuativeExtension K L] : 𝒪[L]ˣ →* 𝒪[K]ˣ where
  toFun := fun x => {
    val := normIntegerUnitsValue (K := K) (L := L) x
    inv := normIntegerUnitsValue (K := K) (L := L) x⁻¹
    val_inv := normIntegerUnitsValue_mul_inv (K := K) (L := L) x
    inv_val := normIntegerUnitsValue_inv_mul (K := K) (L := L) x
  }
  map_one' := by
    ext
    simp [normIntegerUnitsValue]
  map_mul' := by
    intro x y
    ext
    simp [normIntegerUnitsValue]
 
lemma normIntegerUnits_apply_coe [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    (((normIntegerUnits K L x : 𝒪[K]ˣ) : 𝒪[K]) : K) =
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) :=
  rfl
end UnitNorm
section Valuation
variable [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable [Algebra K L]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
 

lemma mapBaseUnits_normUnits_eq_prod_gal [FiniteDimensional K L] [IsGalois K L]
    (x : Lˣ) :
    mapBaseUnitsToExtensionUnits K L (normUnits K L x) =
      ∏ σ : L ≃ₐ[K] L, Units.mapEquiv σ.toMulEquiv x := by
  ext
  simp [mapBaseUnitsToExtensionUnits, normUnits, Algebra.norm_eq_prod_automorphisms]
end Valuation
end IsNonarchimedeanLocalField
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
 
def principalUnits (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Subgroup 𝒪[K]ˣ where
  carrier := {u | ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])}
  one_mem' := by
    simp
  mul_mem' := by
    intro a b ha hb
    change ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) =
        ((a : 𝒪[K]) - 1) * (b : 𝒪[K]) + ((b : 𝒪[K]) - 1) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb
  inv_mem' := by
    intro a ha
    change (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
        -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) by
      calc
        (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1)
            = ((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K])
              - (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (a : 𝒪[K])) := by
                simp
        _ = -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) := by
          ring]
    exact (𝓂[K] ^ n : Ideal 𝒪[K]).neg_mem (Ideal.mul_mem_left _ _ ha)
 

theorem mem_principalUnits_iff (K : Type u) [Field K] [ValuativeRel K]
    (u : 𝒪[K]ˣ) (n : Nat) :
    u ∈ principalUnits K n ↔ ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
  Iff.rfl
 

theorem principalUnits_integerRingEquiv_mem (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (σ𝒪 : 𝒪[K] ≃+* 𝒪[K])
    (hpow : ∀ x : 𝒪[K],
      x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) → σ𝒪 x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]))
    (u : 𝒪[K]ˣ) (hu : u ∈ principalUnits K n) :
    Units.mapEquiv σ𝒪.toMulEquiv u ∈ principalUnits K n := by
  rw [mem_principalUnits_iff] at hu ⊢
  have hmem : σ𝒪 ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
    hpow ((u : 𝒪[K]) - 1) hu
  simpa using hmem
 
@[simp] theorem principalUnits_zero (K : Type u) [Field K] [ValuativeRel K] :
    principalUnits K 0 = ⊤ := by
  ext u
  simp [principalUnits]
 
theorem principalUnits_antitone (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) :
    principalUnits K n ≤ principalUnits K m := by
  intro u hu
  exact Ideal.pow_le_pow_right h hu
 
theorem principalUnits_succ_le (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnits K (n + 1) ≤ principalUnits K n :=
  principalUnits_antitone K (Nat.le_succ n)
 
def IntegerUnitsPrincipalQuot (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K n
 

instance integerUnitsPrincipalQuotCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (IntegerUnitsPrincipalQuot K n) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)
  infer_instance
 


def integerUnitsPrincipalQuotConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsPrincipalQuot K n ≃* (𝒪[K]ˣ ⧸ principalUnits K n) := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) ≃* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact MulEquiv.refl _
 
def integerUnitsPrincipalQuotMk (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) : 𝒪[K]ˣ →* IntegerUnitsPrincipalQuot K n := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact QuotientGroup.mk' (principalUnits K n)
 

@[simp]
theorem integerUnitsPrincipalQuotConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (u : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotConcreteEquiv K n
        (integerUnitsPrincipalQuotMk K n u) =
      QuotientGroup.mk u :=
  rfl
 

@[simp]
theorem integerUnitsPrincipalQuotMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (u : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotMk K n u = 1 ↔ u ∈ principalUnits K n := by
  change QuotientGroup.mk' (principalUnits K n) u = 1 ↔ _
  exact QuotientGroup.eq_one_iff (N := principalUnits K n) u
 

@[simp]
theorem integerUnitsPrincipalQuotMk_eq_iff_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (u v : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotMk K n u =
        integerUnitsPrincipalQuotMk K n v ↔
      u / v ∈ principalUnits K n := by
  change (QuotientGroup.mk u : 𝒪[K]ˣ ⧸ principalUnits K n) =
      QuotientGroup.mk v ↔ _
  exact QuotientGroup.eq_iff_div_mem (N := principalUnits K n)
 
def integerUnitsPrincipalQuotLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker) :
    IntegerUnitsPrincipalQuot K n →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) →* M
  exact QuotientGroup.lift (principalUnits K n) f h
 

@[simp]
theorem integerUnitsPrincipalQuotLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (u : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotLift n f h
        (integerUnitsPrincipalQuotMk K n u) = f u :=
  rfl
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
open Filter
 
def PrincipalUnitsSuccQuot (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Type u :=
  principalUnits K n ⧸ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)
 

instance principalUnitsSuccQuotCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (PrincipalUnitsSuccQuot K n) := by
  change CommGroup
    (principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n))
  infer_instance
 
def principalUnitsSuccQuotConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    PrincipalUnitsSuccQuot K n ≃*
      (principalUnits K n ⧸
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) := by
  change
    (principalUnits K n ⧸
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) ≃*
      (principalUnits K n ⧸
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n))
  exact MulEquiv.refl _
 
def principalUnitsSuccQuotMk (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnits K n →* PrincipalUnitsSuccQuot K n := by
  change principalUnits K n →*
    (principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n))
  exact QuotientGroup.mk'
    ((principalUnits K (n + 1)).subgroupOf (principalUnits K n))
 
def principalUnitsSuccQuotLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : principalUnits K n →* M)
    (h : (principalUnits K (n + 1)).subgroupOf
      (principalUnits K n) ≤ f.ker) :
    PrincipalUnitsSuccQuot K n →* M := by
  change
    (principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) →* M
  exact QuotientGroup.lift
    ((principalUnits K (n + 1)).subgroupOf (principalUnits K n)) f h
 

@[simp]
theorem principalUnitsSuccQuotLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : principalUnits K n →* M)
    (h : (principalUnits K (n + 1)).subgroupOf
      (principalUnits K n) ≤ f.ker) (x : principalUnits K n) :
    principalUnitsSuccQuotLift n f h
        (principalUnitsSuccQuotMk K n x) = f x :=
  rfl
 
protected theorem PrincipalUnitsSuccQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : PrincipalUnitsSuccQuot K n → Prop}
    (q : PrincipalUnitsSuccQuot K n)
    (h : ∀ x : principalUnits K n,
      motive (principalUnitsSuccQuotMk K n x)) :
    motive q := by
  change motive
    (show principalUnits K n ⧸
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n) from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x
 

theorem maximalIdeal_iInf_pow_eq_bot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (⨅ n : Nat, (𝓂[K] ^ n : Ideal 𝒪[K])) = ⊥ := by
  exact Ideal.iInf_pow_eq_bot_of_isLocalRing
    (I := (𝓂[K] : Ideal 𝒪[K])) Ideal.IsPrime.ne_top'
 

theorem eq_zero_of_mem_all_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝒪[K])
    (hx : ∀ n : Nat, x ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    x = 0 := by
  have hxInf : x ∈ (⨅ n : Nat, (𝓂[K] ^ n : Ideal 𝒪[K])) := by
    rw [Ideal.mem_iInf]
    exact hx
  rw [maximalIdeal_iInf_pow_eq_bot K] at hxInf
  exact (Ideal.mem_bot.mp hxInf)
 

theorem principalUnits_eq_one_of_mem_all
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : 𝒪[K]ˣ)
    (hu : ∀ n : Nat, u ∈ principalUnits K n) :
    u = 1 := by
  apply Units.ext
  have hsub :
      ((u : 𝒪[K]) - 1) = 0 :=
    eq_zero_of_mem_all_maximalIdeal_pow K ((u : 𝒪[K]) - 1) (by
      intro n
      exact (mem_principalUnits_iff K u n).1 (hu n))
  exact sub_eq_zero.mp hsub
 

theorem principalUnits_eq_one_of_mem_add_all
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (u : 𝒪[K]ˣ)
    (hu : ∀ d : Nat, u ∈ principalUnits K (n + d)) :
    u = 1 := by
  refine principalUnits_eq_one_of_mem_all K u ?_
  intro m
  by_cases hm : m ≤ n
  · exact principalUnits_antitone K hm (hu 0)
  · have hnm : n ≤ m := Nat.le_of_not_ge hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact hu d
 

theorem exists_maximalIdeal_pow_subset_nhds_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) :
    ∃ N : Nat, ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s := by
  rcases (mem_nhds_subtype ((ValuativeRel.valuation K).integer : Set K)
      (0 : 𝒪[K]) s).1 hs with
    ⟨t, ht, hts⟩
  rcases (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp ht with
    ⟨γ, -, hγt⟩
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  rcases exists_pow_lt₀
      (Valuation.integer.v_irreducible_lt_one (v := ValuativeRel.valuation K) hϖ)
      γ with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro x hx
  apply hts
  apply hγt
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation K) hϖ N
  have hxset : x ∈ ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) := hx
  rw [hset] at hxset
  exact hxset.trans_lt hN
 

theorem eventually_maximalIdeal_pow_subset_nhds_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m →
      ((𝓂[K] ^ m : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s := by
  rcases exists_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  refine ⟨N, fun m hm x hx => hN ?_⟩
  exact Ideal.pow_le_pow_right hm hx
 
theorem isClosed_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    IsClosed (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation K) hϖ n
  rw [hset]
  have hclosed :
      IsClosed {x : 𝒪[K] |
        (ValuativeRel.valuation K).restrict (x : K) ≤
          (ValuativeRel.valuation K).restrict ((ϖ : K) ^ n)} :=
    ((ValuativeRel.valuation K).isClosed_closedBall
      ((ValuativeRel.valuation K).restrict ((ϖ : K) ^ n))).preimage
        (continuous_subtype_val : Continuous (fun x : 𝒪[K] => (x : K)))
  convert hclosed using 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [← map_pow, Valuation.restrict_le_iff, map_pow]
 

theorem maximalIdeal_pow_mem_nhds_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) ∈ nhds (0 : 𝒪[K]) := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  let γ : (ValuativeRel.ValueGroupWithZero K)ˣ :=
    Units.mk0 (ValuativeRel.valuation K ((ϖ : 𝒪[K]) : K) ^ n)
      (pow_ne_zero n (ne_of_gt (Valuation.integer.v_irreducible_pos
        (v := ValuativeRel.valuation K) hϖ)))
  refine (mem_nhds_subtype ((ValuativeRel.valuation K).integer : Set K)
      (0 : 𝒪[K]) (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]))).2 ?_
  refine ⟨{x : K | ValuativeRel.valuation K x <
      (γ : ValuativeRel.ValueGroupWithZero K)}, ?_, ?_⟩
  · exact (IsValuativeTopology.hasBasis_nhds_zero K).mem_of_mem (i := γ) trivial
  · intro x hx
    change x ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
      (v := ValuativeRel.valuation K) hϖ n
    rw [hset]
    have hxv : ValuativeRel.valuation K ((x : 𝒪[K]) : K) <
        (γ : ValuativeRel.ValueGroupWithZero K) := hx
    exact le_of_lt hxv
 

theorem eventually_sub_mem_maximalIdeal_pow_of_tendsto
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] {f : Nat → 𝒪[K]} {x : 𝒪[K]} (n : Nat)
    (hf : Tendsto f atTop (nhds x)) :
    ∀ᶠ d in atTop, f d - x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  have hdiff : Tendsto (fun d : Nat => f d - x) atTop (nhds (0 : 𝒪[K])) := by
    simpa using hf.sub (tendsto_const_nhds (x := x))
  exact hdiff.eventually (maximalIdeal_pow_mem_nhds_zero K n)
 

theorem eventually_div_mem_principalUnits_of_tendsto_units
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] {f : Nat → 𝒪[K]ˣ} {x : 𝒪[K]ˣ} (n : Nat)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[K]ˣ) : 𝒪[K])) atTop
      (nhds ((x : 𝒪[K]ˣ) : 𝒪[K]))) :
    ∀ᶠ d in atTop, f d / x ∈ principalUnits K n := by
  have hsub := eventually_sub_mem_maximalIdeal_pow_of_tendsto K n hf
  filter_upwards [hsub] with d hd
  rw [mem_principalUnits_iff]
  change (((f d / x : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
  rw [show (((f d / x : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      (((f d : 𝒪[K]ˣ) : 𝒪[K]) - ((x : 𝒪[K]ˣ) : 𝒪[K])) * ↑(x⁻¹) by
    simp only [div_eq_mul_inv, Units.val_mul]
    calc
      ((f d : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) - 1 =
          ((f d : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) -
            ((x : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) := by
            simp
      _ = (((f d : 𝒪[K]ˣ) : 𝒪[K]) - ((x : 𝒪[K]ˣ) : 𝒪[K])) * ↑(x⁻¹) := by
            ring]
  exact (𝓂[K] ^ n : Ideal 𝒪[K]).mul_mem_right _ hd
 


def principalUnitsCorrectionProduct (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (z : ∀ d : Nat, principalUnits K (n + d)) :
    Nat → 𝒪[K]ˣ
  | 0 => 1
  | d + 1 => principalUnitsCorrectionProduct K n z d * (z d : 𝒪[K]ˣ)
 
@[simp]
theorem principalUnitsCorrectionProduct_zero
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    principalUnitsCorrectionProduct K n z 0 = 1 :=
  rfl
 
@[simp]
theorem principalUnitsCorrectionProduct_succ
    (K : Type u) [Field K] [ValuativeRel K] (n d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    principalUnitsCorrectionProduct K n z (d + 1) =
      principalUnitsCorrectionProduct K n z d * (z d : 𝒪[K]ˣ) :=
  rfl
 

theorem principalUnitsCorrectionProduct_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) (d : Nat) :
    principalUnitsCorrectionProduct K n z d ∈ principalUnits K n := by
  induction d with
  | zero =>
      simp [principalUnitsCorrectionProduct]
  | succ d ih =>
      rw [principalUnitsCorrectionProduct_succ]
      exact (principalUnits K n).mul_mem ih
        (principalUnits_antitone K (Nat.le_add_right n d) (z d).2)
 


theorem principalUnitsCorrectionProduct_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    principalUnitsCorrectionProduct K n z (m + d) /
        principalUnitsCorrectionProduct K n z m ∈
      principalUnits K (n + m) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hprod :
          principalUnitsCorrectionProduct K n z (m + (d + 1)) =
            principalUnitsCorrectionProduct K n z (m + d) *
              (z (m + d) : 𝒪[K]ˣ) := by
        rw [Nat.add_succ]
        rfl
      rw [hprod]
      have hz :
          (z (m + d) : 𝒪[K]ˣ) ∈ principalUnits K (n + m) := by
        exact principalUnits_antitone K
          (Nat.add_le_add_left (Nat.le_add_right m d) n) (z (m + d)).2
      have hEq :
          principalUnitsCorrectionProduct K n z (m + d) *
              (z (m + d) : 𝒪[K]ˣ) /
              principalUnitsCorrectionProduct K n z m =
            (principalUnitsCorrectionProduct K n z (m + d) /
              principalUnitsCorrectionProduct K n z m) *
              (z (m + d) : 𝒪[K]ˣ) := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm]
      rw [hEq]
      exact (principalUnits K (n + m)).mul_mem ih hz
 

theorem principalUnitsCorrectionProduct_div_sub_one_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ((principalUnitsCorrectionProduct K n z (m + d) /
          principalUnitsCorrectionProduct K n z m : 𝒪[K]ˣ) : 𝒪[K]) - 1 ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
  exact (mem_principalUnits_iff K
    (principalUnitsCorrectionProduct K n z (m + d) /
      principalUnitsCorrectionProduct K n z m) (n + m)).1
    (principalUnitsCorrectionProduct_div_mem K n m d z)
 


lemma unit_sub_eq_mul_div_sub_one
    (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    (a : 𝒪[K]) - (b : 𝒪[K]) =
      (b : 𝒪[K]) * (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
  have hmul : (b : 𝒪[K]) * ((a / b : 𝒪[K]ˣ) : 𝒪[K]) = (a : 𝒪[K]) := by
    simp [div_eq_mul_inv, mul_left_comm]
  calc
    (a : 𝒪[K]) - (b : 𝒪[K]) =
        (b : 𝒪[K]) * ((a / b : 𝒪[K]ˣ) : 𝒪[K]) - (b : 𝒪[K]) := by
      rw [hmul]
    _ = (b : 𝒪[K]) * (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
      ring
 

theorem principalUnitsCorrectionProduct_sub_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ((principalUnitsCorrectionProduct K n z (m + d) : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z m : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
  let a : 𝒪[K]ˣ := principalUnitsCorrectionProduct K n z (m + d)
  let b : 𝒪[K]ˣ := principalUnitsCorrectionProduct K n z m
  have htail : (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
    simpa [a, b] using principalUnitsCorrectionProduct_div_sub_one_mem K n m d z
  rw [unit_sub_eq_mul_div_sub_one K a b]
  exact Ideal.mul_mem_left _ _ htail
 

theorem principalUnitsCorrectionProduct_sub_mem_of_le
    (K : Type u) [Field K] [ValuativeRel K] (n N i j : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d))
    (hi : N ≤ i) (hj : N ≤ j) :
    ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z j : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + N) : Ideal 𝒪[K]) := by
  by_cases hji : j ≤ i
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
    exact Ideal.pow_le_pow_right (Nat.add_le_add_left hj n)
      (principalUnitsCorrectionProduct_sub_mem K n j d z)
  · have hij : i ≤ j := Nat.le_of_not_ge hji
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hdiff :
        ((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) ∈
          (𝓂[K] ^ (n + N) : Ideal 𝒪[K]) := by
      exact Ideal.pow_le_pow_right (Nat.add_le_add_left hi n)
        (principalUnitsCorrectionProduct_sub_mem K n i d z)
    have hEq :
        ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) =
          -(((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K])) := by
      ring
    rw [hEq]
    exact (𝓂[K] ^ (n + N) : Ideal 𝒪[K]).neg_mem hdiff
 

theorem principalUnitsCorrectionProduct_cauchySeq
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    CauchySeq fun d : Nat =>
      ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]) := by
  rw [cauchySeq_iff]
  intro V hV
  rw [uniformity_eq_comap_nhds_zero 𝒪[K]] at hV
  rw [mem_comap] at hV
  rcases hV with ⟨s, hs, hsub⟩
  rcases eventually_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi j hj
  apply hsub
  exact hN (n + N) (Nat.le_add_left N n)
    (principalUnitsCorrectionProduct_sub_mem_of_le K n N j i z hj hi)
 



theorem exists_tendsto_principalUnitsCorrectionProduct
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ∃ x : 𝒪[K], Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds x) :=
  cauchySeq_tendsto_of_complete
    (principalUnitsCorrectionProduct_cauchySeq K n z)
 

theorem principalUnitsCorrectionProduct_limit_sub_one_mem
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) (x : 𝒪[K])
    (hx : Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds x)) :
    x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  have hclosed := isClosed_maximalIdeal_pow K n
  refine hclosed.mem_of_tendsto
    (f := fun d : Nat =>
      ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]) - 1)
    (b := (atTop : Filter Nat)) (x := x - 1) ?_ ?_
  · exact hx.sub tendsto_const_nhds
  · exact Eventually.of_forall fun d =>
      (mem_principalUnits_iff K (principalUnitsCorrectionProduct K n z d) n).1
        (principalUnitsCorrectionProduct_mem K n z d)
 


theorem exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ∃ x : 𝒪[K], Tendsto
        (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
        atTop (nhds x) ∧
      x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  rcases exists_tendsto_principalUnitsCorrectionProduct K n z with ⟨x, hx⟩
  exact ⟨x, hx, principalUnitsCorrectionProduct_limit_sub_one_mem K n z x hx⟩
 

@[simp]
theorem principalUnitsSuccQuotConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (u : principalUnits K n) :
    principalUnitsSuccQuotConcreteEquiv K n
        (principalUnitsSuccQuotMk K n u) =
      QuotientGroup.mk u :=
  rfl
 
def principalUnitsSuccIncl (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnits K (n + 1) →* principalUnits K n where
  toFun u := ⟨u.1, principalUnits_succ_le K n u.2⟩
  map_one' := rfl
  map_mul' := by
    intro a b
    rfl
 

theorem principalUnitsSuccIncl_range
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    MonoidHom.range (principalUnitsSuccIncl K n) =
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨v, hv⟩
    rw [← hv]
    exact v.2
  · intro hu
    exact ⟨⟨u.1, hu⟩, by ext; rfl⟩
 
theorem principalUnitsSuccQuotMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Function.Surjective (principalUnitsSuccQuotMk K n) :=
  QuotientGroup.mk'_surjective ((principalUnits K (n + 1)).subgroupOf (principalUnits K n))
 
theorem principalUnitsSuccQuotMk_ker (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    MonoidHom.ker (principalUnitsSuccQuotMk K n) =
      (principalUnits K (n + 1)).subgroupOf (principalUnits K n) :=
  QuotientGroup.ker_mk'
    (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n))
 
theorem principalUnitsSuccQuotMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    principalUnitsSuccQuotMk K n u = 1 ↔
      u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) u).mp
    have h' := congrArg (principalUnitsSuccQuotConcreteEquiv K n) h
    simpa using h'
  · intro h
    apply (principalUnitsSuccQuotConcreteEquiv K n).injective
    simpa using
      (QuotientGroup.eq_one_iff
        (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n)) u).mpr h
 

theorem principalUnitsSuccQuotMk_eq_iff_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u v : principalUnits K n) :
    principalUnitsSuccQuotMk K n u = principalUnitsSuccQuotMk K n v ↔
      u / v ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  constructor
  · intro h
    have h' := congrArg (principalUnitsSuccQuotConcreteEquiv K n) h
    exact (QuotientGroup.eq_iff_div_mem
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n))).mp h'
  · intro h
    apply (principalUnitsSuccQuotConcreteEquiv K n).injective
    exact (QuotientGroup.eq_iff_div_mem
      (N := (principalUnits K (n + 1)).subgroupOf (principalUnits K n))).mpr h
 
theorem principalUnitsSuccIncl_exact
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    MonoidHom.range (principalUnitsSuccIncl K n) =
      MonoidHom.ker (principalUnitsSuccQuotMk K n) := by
  rw [principalUnitsSuccIncl_range, principalUnitsSuccQuotMk_ker]
 
theorem principalUnitsSuccIncl_mem_ker
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K (n + 1)) :
    principalUnitsSuccIncl K n u ∈ MonoidHom.ker (principalUnitsSuccQuotMk K n) := by
  rw [← principalUnitsSuccIncl_exact K n]
  exact ⟨u, rfl⟩
 
@[simp]
theorem principalUnitsSuccQuotMk_comp_incl_apply
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K (n + 1)) :
    principalUnitsSuccQuotMk K n (principalUnitsSuccIncl K n u) = 1 := by
  exact principalUnitsSuccIncl_mem_ker K n u
 

theorem mem_principalUnits_succ_subgroupOf_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) ↔
      (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
        (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  rw [Subgroup.mem_subgroupOf, mem_principalUnits_iff]
 
abbrev maximalIdealPowSuccSubmodule
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Submodule (𝒪[K]) ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) :=
  Submodule.comap (Submodule.subtype (p := (𝓂[K] ^ n : Ideal 𝒪[K])))
    ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Submodule (𝒪[K]) (𝒪[K]))
 
def MaximalIdealPowSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Type u :=
  ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸ maximalIdealPowSuccSubmodule K n
 
instance maximalIdealPowSuccQuotAddCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    AddCommGroup (MaximalIdealPowSuccQuot K n) := by
  change AddCommGroup
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  infer_instance
 
instance maximalIdealPowSuccQuotModule
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Module 𝒪[K] (MaximalIdealPowSuccQuot K n) := by
  change Module 𝒪[K]
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  infer_instance
 
def maximalIdealPowSuccQuotConcreteLinearEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    MaximalIdealPowSuccQuot K n ≃ₗ[𝒪[K]]
      (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
        maximalIdealPowSuccSubmodule K n) := by
  change
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
        maximalIdealPowSuccSubmodule K n) ≃ₗ[𝒪[K]]
      (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
        maximalIdealPowSuccSubmodule K n)
  exact LinearEquiv.refl 𝒪[K] _
 
def maximalIdealPowSuccQuotMk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]]
      MaximalIdealPowSuccQuot K n := by
  change ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]]
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n)
  exact Submodule.mkQ (maximalIdealPowSuccSubmodule K n)
 

@[simp]
theorem maximalIdealPowSuccQuotConcreteLinearEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotConcreteLinearEquiv K n
        (maximalIdealPowSuccQuotMk K n a) =
      Submodule.Quotient.mk a :=
  rfl
 
protected theorem MaximalIdealPowSuccQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n → Prop}
    (q : MaximalIdealPowSuccQuot K n)
    (h : ∀ a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)) :
    motive q := by
  change motive
    (show ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n from q)
  refine Quotient.inductionOn q ?_
  intro a
  exact h a
 
protected theorem MaximalIdealPowSuccQuot.inductionOn₂
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) :
    motive q r := by
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun q' => motive q' r) q ?_
  intro a
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun r' => motive (maximalIdealPowSuccQuotMk K n a) r') r ?_
  intro b
  exact h a b
 

def maximalIdealPowSuccQuotLift
    {K : Type u} {P : Sort*} [Field K] [ValuativeRel K] (n : Nat)
    (f : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) → P)
    (h : ∀ a b, a - b ∈ maximalIdealPowSuccSubmodule K n →
      f a = f b) :
    MaximalIdealPowSuccQuot K n → P := by
  change
    ((((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) → P)
  refine Quotient.lift f ?_
  intro a b hab
  have hq :
      (Submodule.Quotient.mk a :
        ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
          maximalIdealPowSuccSubmodule K n) =
        Submodule.Quotient.mk b :=
    Quotient.sound hab
  exact h a b
    ((Submodule.Quotient.eq (maximalIdealPowSuccSubmodule K n)).1 hq)
 
@[simp]
theorem maximalIdealPowSuccQuotLift_mk
    {K : Type u} {P : Sort*} [Field K] [ValuativeRel K] (n : Nat)
    (f : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) → P)
    (h : ∀ a b, a - b ∈ maximalIdealPowSuccSubmodule K n →
      f a = f b)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotLift n f h
        (maximalIdealPowSuccQuotMk K n a) = f a :=
  rfl
 
def maximalIdealPowSuccQuotLinearLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K]
    [AddCommGroup M] [Module 𝒪[K] M] (n : Nat)
    (f : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]] M)
    (h : maximalIdealPowSuccSubmodule K n ≤ f.ker) :
    MaximalIdealPowSuccQuot K n →ₗ[𝒪[K]] M := by
  change
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) →ₗ[𝒪[K]] M
  exact (maximalIdealPowSuccSubmodule K n).liftQ f h
 

@[simp]
theorem maximalIdealPowSuccQuotLinearLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K]
    [AddCommGroup M] [Module 𝒪[K] M] (n : Nat)
    (f : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →ₗ[𝒪[K]] M)
    (h : maximalIdealPowSuccSubmodule K n ≤ f.ker)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotLinearLift n f h
        (maximalIdealPowSuccQuotMk K n a) = f a :=
  rfl
 

theorem mem_maximalIdealPowSuccSubmodule_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    a ∈ maximalIdealPowSuccSubmodule K n ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
  Iff.rfl
 
theorem maximalIdealPowSuccQuotMk_eq_zero_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMk K n a = 0 ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  change (Submodule.Quotient.mk a :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl
 

@[simp]
theorem maximalIdealPowSuccQuotMk_eq_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMk K n a =
        maximalIdealPowSuccQuotMk K n b ↔
      a - b ∈ maximalIdealPowSuccSubmodule K n := by
  change (Submodule.Quotient.mk a :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) =
    Submodule.Quotient.mk b ↔ _
  exact Submodule.Quotient.eq (maximalIdealPowSuccSubmodule K n)
 
theorem isUnit_one_add_of_mem_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : IsUnit (1 + a) := by
  have ha1 : a ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    have hle : (𝓂[K] ^ n : Ideal 𝒪[K]) ≤ (𝓂[K] ^ 1 : Ideal 𝒪[K]) :=
      Ideal.pow_le_pow_right hn
    simpa using hle ha
  have hnon : (-a) ∈ nonunits 𝒪[K] := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact (𝓂[K] : Ideal 𝒪[K]).neg_mem ha1
  have hunit : IsUnit (1 - (-a)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-a) hnon
  simpa [sub_neg_eq_add] using hunit
 
noncomputable def principalUnitOneAddOfMemPow
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]ˣ :=
  (isUnit_one_add_of_mem_maximalIdeal_pow K hn a ha).unit
 
@[simp]
theorem principalUnitOneAddOfMemPow_val
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    ((principalUnitOneAddOfMemPow K hn a ha : 𝒪[K]ˣ) : 𝒪[K]) = 1 + a :=
  IsUnit.unit_spec (isUnit_one_add_of_mem_maximalIdeal_pow K hn a ha)
 
noncomputable def principalUnitOneAddOfMemPowSubgroup
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : principalUnits K n :=
  ⟨principalUnitOneAddOfMemPow K hn a ha, by
    rw [mem_principalUnits_iff]
    simp [principalUnitOneAddOfMemPow_val, ha]
  ⟩
 
@[simp]
theorem principalUnitOneAddOfMemPowSubgroup_val
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    ((principalUnitOneAddOfMemPowSubgroup K hn a ha : principalUnits K n) : 𝒪[K]ˣ) =
      principalUnitOneAddOfMemPow K hn a ha :=
  rfl
 

theorem exists_tendsto_principalUnitsCorrectionProduct_principalUnit
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ∃ x : principalUnits K n, Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds (((x : principalUnits K n) : 𝒪[K]ˣ) : 𝒪[K])) := by
  rcases exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem K n z with
    ⟨x, hx, hmem⟩
  let u : principalUnits K n :=
    principalUnitOneAddOfMemPowSubgroup K hn (x - 1) hmem
  refine ⟨u, ?_⟩
  have huval : (((u : principalUnits K n) : 𝒪[K]ˣ) : 𝒪[K]) = x := by
    change ((principalUnitOneAddOfMemPow K hn (x - 1) hmem : 𝒪[K]ˣ) : 𝒪[K]) = x
    rw [principalUnitOneAddOfMemPow_val]
    ring
  simpa [huval] using hx
 
noncomputable def principalUnitsSuccQuotOfIdealPow
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    (𝓂[K] ^ n : Ideal 𝒪[K]) → PrincipalUnitsSuccQuot K n :=
  fun a =>
    principalUnitsSuccQuotMk K n
      (principalUnitOneAddOfMemPowSubgroup K hn a.1 a.2)
 
@[simp]
theorem principalUnitsSuccQuotOfIdealPow_apply
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a =
      principalUnitsSuccQuotMk K n
        (principalUnitOneAddOfMemPowSubgroup K hn a.1 a.2) :=
  rfl
 

theorem principalUnitsSuccQuotMk_eq_oneAdd_of_sub_one_sub_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (u : principalUnits K n) (a : (𝓂[K] ^ n : Ideal 𝒪[K]))
    (h : (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) ∈
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])) :
    principalUnitsSuccQuotMk K n u =
      principalUnitsSuccQuotOfIdealPow K n hn a := by
  rw [principalUnitsSuccQuotOfIdealPow_apply]
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n _ _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  change ((((u : 𝒪[K]ˣ) /
        principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [show ((((u : 𝒪[K]ˣ) /
        principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) *
        ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    have hunit :
        ((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) *
          ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ = 1 := by
      simp
    calc
      ((u : 𝒪[K]ˣ) : 𝒪[K]) *
            ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ - 1 =
          ((u : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ -
            ((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ := by
        rw [hunit]
      _ = (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) *
          ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ := by
        rw [principalUnitOneAddOfMemPow_val K hn (a : 𝒪[K]) a.2]
        ring]
  exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).mul_mem_right _ h
 
theorem principalUnitsSuccQuotOfIdealPow_eq_one_of_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (a : (𝓂[K] ^ n : Ideal 𝒪[K]))
    (ha : (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a = 1 := by
  apply (principalUnitsSuccQuotMk_eq_one_iff K n _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  simp [principalUnitOneAddOfMemPowSubgroup, principalUnitOneAddOfMemPow_val, ha]
 
theorem principalUnitsSuccQuotOfIdealPow_eq_of_sub_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K]))
    (hab : ((a : 𝒪[K]) - (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a =
      principalUnitsSuccQuotOfIdealPow K n hn b := by
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n _ _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  change (((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 /
            principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [show (((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 /
            principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      ((a : 𝒪[K]) - (b : 𝒪[K])) *
        ↑(principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [principalUnitOneAddOfMemPow_val K hn (a : 𝒪[K]) a.2]
    have hbval :
        ((principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) =
          1 + (b : 𝒪[K]) :=
      principalUnitOneAddOfMemPow_val K hn (b : 𝒪[K]) b.2
    have hbinv :
        ((principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) : 𝒪[K]) *
          ↑(principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2)⁻¹ = 1 := by
      simp
    calc
      (1 + (a : 𝒪[K])) * ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ - 1 =
          (1 + (a : 𝒪[K])) * ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ -
            ((principalUnitOneAddOfMemPow K hn ↑b b.2 : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ := by
        rw [hbinv]
      _ = (↑a - ↑b) * ↑(principalUnitOneAddOfMemPow K hn ↑b b.2)⁻¹ := by
        rw [hbval]
        ring]
  exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).mul_mem_right _ hab
 
noncomputable def principalUnitsSuccQuotOfMaximalIdealPowSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot K n → PrincipalUnitsSuccQuot K n :=
  maximalIdealPowSuccQuotLift n
    (principalUnitsSuccQuotOfIdealPow K n hn)
    (fun a b hab =>
      principalUnitsSuccQuotOfIdealPow_eq_of_sub_mem_succ K n hn a b (by
        simpa using
          (mem_maximalIdealPowSuccSubmodule_iff K n (a - b)).1 hab))
 

@[simp]
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n a) =
      principalUnitsSuccQuotOfIdealPow K n hn a :=
  rfl
 
theorem maximalIdealPow_mul_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    ((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  have hmul : ((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + n) : Ideal 𝒪[K]) := by
    simpa [pow_add] using (Ideal.mul_mem_mul a.2 b.2)
  have hle : (𝓂[K] ^ (n + n) : Ideal 𝒪[K]) ≤
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_left hn n)
  exact hle hmul
 

theorem finset_prod_one_add_sub_one_mem_maximalIdeal_of_mem_pow
    (K : Type u) [Field K] [ValuativeRel K] {ι : Type*}
    (s : Finset ι) (n : Nat) (hn : 1 ≤ n) (a : ι → 𝒪[K])
    (ha : ∀ i ∈ s, a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    (s.prod fun i => 1 + a i) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  classical
  revert a
  refine Finset.induction_on s ?base ?step
  · intro a ha
    simp
  · intro i s hi ih a ha
    have hai_pow : a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := ha i (by simp [hi])
    have hai : a i ∈ (𝓂[K] : Ideal 𝒪[K]) := by
      have hle : (𝓂[K] ^ n : Ideal 𝒪[K]) ≤ (𝓂[K] ^ 1 : Ideal 𝒪[K]) :=
        Ideal.pow_le_pow_right hn
      simpa using hle hai_pow
    have hs : ∀ j ∈ s, a j ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
      intro j hj
      exact ha j (by simp [hj])
    have hprod : (s.prod fun j => 1 + a j) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      ih a hs
    have hterm : a i * (s.prod fun j => 1 + a j) ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      (𝓂[K] : Ideal 𝒪[K]).mul_mem_right _ hai
    rw [Finset.prod_insert hi]
    rw [show (1 + a i) * (s.prod fun j => 1 + a j) - 1 =
        ((s.prod fun j => 1 + a j) - 1) +
          a i * (s.prod fun j => 1 + a j) by
      ring]
    exact (𝓂[K] : Ideal 𝒪[K]).add_mem hprod hterm
 


theorem finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ
    (K : Type u) [Field K] [ValuativeRel K] {ι : Type*}
    (s : Finset ι) (n : Nat) (hn : 1 ≤ n) (a : ι → 𝒪[K])
    (ha : ∀ i ∈ s, a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    (s.prod fun i => 1 + a i) - 1 - (s.sum fun i => a i) ∈
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  classical
  revert a
  refine Finset.induction_on s ?base ?step
  · intro a ha
    simp
  · intro i s hi ih a ha
    have hai : a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := ha i (by simp [hi])
    have hs : ∀ j ∈ s, a j ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
      intro j hj
      exact ha j (by simp [hj])
    have hind :
        (s.prod fun j => 1 + a j) - 1 - (s.sum fun j => a j) ∈
          (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
      ih a hs
    have hprod :
        (s.prod fun j => 1 + a j) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      finset_prod_one_add_sub_one_mem_maximalIdeal_of_mem_pow K s n hn a hs
    have hmul_raw :
        a i * ((s.prod fun j => 1 + a j) - 1) ∈
          (𝓂[K] ^ n : Ideal 𝒪[K]) * (𝓂[K] : Ideal 𝒪[K]) :=
      Ideal.mul_mem_mul hai hprod
    have hmul :
        a i * ((s.prod fun j => 1 + a j) - 1) ∈
          (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
      simpa [pow_add] using hmul_raw
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [show (1 + a i) * (s.prod fun j => 1 + a j) - 1 -
          (a i + (s.sum fun j => a j)) =
        ((s.prod fun j => 1 + a j) - 1 - (s.sum fun j => a j)) +
          a i * ((s.prod fun j => 1 + a j) - 1) by
      ring]
    exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).add_mem hind hmul
 
@[simp]
theorem principalUnitsSuccQuotOfIdealPow_zero
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    principalUnitsSuccQuotOfIdealPow K n hn (0 : (𝓂[K] ^ n : Ideal 𝒪[K])) = 1 := by
  apply principalUnitsSuccQuotOfIdealPow_eq_one_of_mem_succ
  simp
 

theorem principalUnitsSuccQuotOfIdealPow_add
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn (a + b) =
      principalUnitsSuccQuotOfIdealPow K n hn a *
        principalUnitsSuccQuotOfIdealPow K n hn b := by
  rw [principalUnitsSuccQuotOfIdealPow_apply,
    principalUnitsSuccQuotOfIdealPow_apply,
    principalUnitsSuccQuotOfIdealPow_apply,
    ← (principalUnitsSuccQuotMk K n).map_mul]
  symm
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n _ _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  change ((((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 *
              principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) /
            principalUnitOneAddOfMemPow K hn
              ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 :
              𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [show ((((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 *
              principalUnitOneAddOfMemPow K hn (b : 𝒪[K]) b.2 : 𝒪[K]ˣ) /
            principalUnitOneAddOfMemPow K hn
              ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 :
              𝒪[K]ˣ) : 𝒪[K]) - 1) =
      ((a : 𝒪[K]) * (b : 𝒪[K])) *
        ↑(principalUnitOneAddOfMemPow K hn
          ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [principalUnitOneAddOfMemPow_val K hn (a : 𝒪[K]) a.2,
      principalUnitOneAddOfMemPow_val K hn (b : 𝒪[K]) b.2]
    have habval :
        ((principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 : 𝒪[K]ˣ) :
            𝒪[K]) =
          1 + (a : 𝒪[K]) + (b : 𝒪[K]) := by
      rw [principalUnitOneAddOfMemPow_val K hn
        ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2]
      change 1 + ((a : 𝒪[K]) + (b : 𝒪[K])) = 1 + (a : 𝒪[K]) + (b : 𝒪[K])
      ring
    have habinv :
        ((principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 : 𝒪[K]ˣ) :
            𝒪[K]) *
          ↑(principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ = 1 := by
      simp
    calc
      ((1 + (a : 𝒪[K])) * (1 + (b : 𝒪[K]))) *
            ↑(principalUnitOneAddOfMemPow K hn
              ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ - 1 =
          ((1 + (a : 𝒪[K])) * (1 + (b : 𝒪[K]))) *
              ↑(principalUnitOneAddOfMemPow K hn
                ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ -
            ((principalUnitOneAddOfMemPow K hn
                ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2 :
                𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn
                ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ := by
        rw [habinv]
      _ = ((a : 𝒪[K]) * (b : 𝒪[K])) *
          ↑(principalUnitOneAddOfMemPow K hn
            ((a + b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]) (a + b).2)⁻¹ := by
        rw [habval]
        ring]
  exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).mul_mem_right _
    (maximalIdealPow_mul_mem_succ K hn a b)
 
@[simp]
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_zero
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn 0 = 1 := by
  rw [← map_zero (maximalIdealPowSuccQuotMk K n)]
  change principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
      (maximalIdealPowSuccQuotMk K n (0 : (𝓂[K] ^ n : Ideal 𝒪[K]))) = 1
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
  exact principalUnitsSuccQuotOfIdealPow_zero K n hn
 
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_add
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (x y : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x + y) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x *
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn y := by
  refine MaximalIdealPowSuccQuot.inductionOn₂ n
    (motive := fun x' y' =>
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x' + y') =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x' *
          principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn y') x y ?_
  intro a b
  let qa : MaximalIdealPowSuccQuot K n := maximalIdealPowSuccQuotMk K n a
  let qb : MaximalIdealPowSuccQuot K n := maximalIdealPowSuccQuotMk K n b
  have hleft :
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (qa + qb) =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
          (maximalIdealPowSuccQuotMk K n (a + b)) := by
    have hadd : qa + qb = maximalIdealPowSuccQuotMk K n (a + b) := by
      exact (map_add (maximalIdealPowSuccQuotMk K n) a b).symm
    exact congrArg (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn) hadd
  have hrep :
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
          (maximalIdealPowSuccQuotMk K n (a + b)) =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn qa *
          principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn qb := by
    dsimp [qa, qb]
    change principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n (a + b)) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n a) *
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
        (maximalIdealPowSuccQuotMk K n b)
    rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
    exact principalUnitsSuccQuotOfIdealPow_add K n hn a b
  exact hleft.trans hrep
 
noncomputable def principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot K n →+ Additive (PrincipalUnitsSuccQuot K n) where
  toFun x := Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x)
  map_zero' := by
    change Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn 0) = 0
    simp [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_zero]
  map_add' x y := by
    change Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x + y)) =
      Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x *
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn y)
    rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map_add]
 

@[simp]
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_apply
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (x : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn x =
      Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) :=
  rfl
 
theorem principalUnitsSuccQuotOfIdealPow_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsSuccQuotOfIdealPow K n hn a = 1 ↔
      (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  constructor
  · intro h
    have hmem := (principalUnitsSuccQuotMk_eq_one_iff K n _).1 h
    rw [mem_principalUnits_succ_subgroupOf_iff] at hmem
    simpa [principalUnitsSuccQuotOfIdealPow, principalUnitOneAddOfMemPowSubgroup,
      principalUnitOneAddOfMemPow_val] using hmem
  · intro ha
    exact principalUnitsSuccQuotOfIdealPow_eq_one_of_mem_succ K n hn a ha
 

theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (x : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x = 1 ↔ x = 0 := by
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x' =>
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x' = 1 ↔ x' = 0)
    x ?_
  intro a
  rw [← map_zero (maximalIdealPowSuccQuotMk K n)]
  change principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn
      (maximalIdealPowSuccQuotMk K n a) = 1 ↔
    (maximalIdealPowSuccQuotMk K n a : MaximalIdealPowSuccQuot K n) = 0
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
    maximalIdealPowSuccQuotMk_eq_zero_iff]
  exact principalUnitsSuccQuotOfIdealPow_eq_one_iff K n hn a
 
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn) := by
  intro x
  rcases principalUnitsSuccQuotMk_surjective K n x with ⟨u, rfl⟩
  let a0 : 𝒪[K] := ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1
  have ha0 : a0 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
    dsimp [a0]
    exact (mem_principalUnits_iff K (u : 𝒪[K]ˣ) n).1 u.2
  let a : (𝓂[K] ^ n : Ideal 𝒪[K]) := ⟨a0, ha0⟩
  refine ⟨maximalIdealPowSuccQuotMk K n a, ?_⟩
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
    principalUnitsSuccQuotOfIdealPow_apply]
  congr 1
  dsimp [a]
  apply Subtype.ext
  rw [principalUnitOneAddOfMemPowSubgroup_val]
  apply Units.ext
  rw [principalUnitOneAddOfMemPow_val]
  dsimp [a0]
  ring
 

theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn) := by
  intro y
  rcases principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_surjective K n hn
      (Additive.toMul y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) = y
  rw [hx]
  rfl
 
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    Function.Injective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn) := by
  intro x y hxy
  have hzero : principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmul : principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x - y) = 1 := by
    change Additive.ofMul (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn (x - y)) =
      Additive.ofMul (1 : PrincipalUnitsSuccQuot K n) at hzero
    exact Additive.ofMul.injective hzero
  have hxmy : x - y = 0 :=
    (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff K n hn (x - y)).1 hmul
  exact sub_eq_zero.mp hxmy
 
noncomputable def maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot K n ≃+ Additive (PrincipalUnitsSuccQuot K n) :=
  AddEquiv.ofBijective (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn)
    ⟨principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_injective K n hn,
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective K n hn⟩
 

@[simp]
theorem maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot_apply
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (x : MaximalIdealPowSuccQuot K n) :
    maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn x =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn x :=
  rfl
 


noncomputable def maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n) :
    Multiplicative (MaximalIdealPowSuccQuot K n) ≃*
      PrincipalUnitsSuccQuot K n where
  toFun x :=
    Additive.toMul
      (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
        (Multiplicative.toAdd x))
  invFun x :=
    Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm
        (Additive.ofMul x))
  left_inv := by
    intro x
    change Multiplicative.ofAdd
        ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm
          (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).left_inv
        (Multiplicative.toAdd x))
  right_inv := by
    intro x
    change Additive.toMul
        (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm
            (Additive.ofMul x))) =
      Additive.toMul (Additive.ofMul x)
    exact congrArg Additive.toMul
      ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).right_inv
        (Additive.ofMul x))
  map_mul' := by
    intro x y
    rw [show Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x + Multiplicative.toAdd y from rfl]
    change Additive.toMul
        (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
      Additive.toMul
        (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          (Multiplicative.toAdd x) +
        maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn
          (Multiplicative.toAdd y))
    exact congrArg Additive.toMul
      ((maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).map_add
        (Multiplicative.toAdd x) (Multiplicative.toAdd y))
 

@[simp]
theorem maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot_apply
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (x : MaximalIdealPowSuccQuot K n) :
    maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot K n hn
        (Multiplicative.ofAdd x) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x :=
  rfl
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
 
theorem integerRingEquiv_mem_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (x : 𝒪[K]) :
    e x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
    ← IsLocalRing.mem_maximalIdeal]
 
theorem integerRingEquiv_map_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) :
    Ideal.map e.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K]) := by
  ext y
  constructor
  · intro hy
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hy with
      ⟨x, hx, rfl⟩
    exact (integerRingEquiv_mem_maximalIdeal K e x).2 hx
  · intro hy
    refine (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).2 ?_
    refine ⟨e.symm y, ?_, by simp⟩
    have hy' : e (e.symm y) ∈ (𝓂[K] : Ideal 𝒪[K]) := by
      simpa using hy
    exact (integerRingEquiv_mem_maximalIdeal K e (e.symm y)).1 hy'
 
theorem integerRingEquiv_map_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat) :
    Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) =
      (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  rw [Ideal.map_pow, integerRingEquiv_map_maximalIdeal]
 
theorem integerRingEquiv_mem_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat) (x : 𝒪[K]) :
    e x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  constructor
  · intro hx
    have hxmap :
        e.symm (e x) ∈ Ideal.map e.symm.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.symm.toRingHom hx
    rw [integerRingEquiv_map_maximalIdeal_pow K e.symm n] at hxmap
    simpa using hxmap
  · intro hx
    have hxmap : e x ∈ Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.toRingHom hx
    rw [integerRingEquiv_map_maximalIdeal_pow K e n] at hxmap
    exact hxmap
 
def maximalIdealPowMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ≃+
      ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun a := ⟨e (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e n a).2 a.2⟩
  invFun a :=
    ⟨e.symm (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e.symm n a).2 a.2⟩
  left_inv := by
    intro a
    ext
    simp
  right_inv := by
    intro a
    ext
    simp
  map_add' := by
    intro a b
    ext
    simp
private theorem maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K])
    (a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u))
    (hab : a - b ∈ maximalIdealPowSuccSubmodule K n) :
    maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a) =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e b) := by
  apply (maximalIdealPowSuccQuotMk_eq_iff K n _ _).2
  rw [mem_maximalIdealPowSuccSubmodule_iff]
  change e (a : 𝒪[K]) - e (b : 𝒪[K]) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [← map_sub]
  exact (integerRingEquiv_mem_maximalIdeal_pow K e (n + 1)
    ((a - b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K])).2
      ((mem_maximalIdealPowSuccSubmodule_iff K n (a - b)).1 hab)
 
def maximalIdealPowSuccQuotMapOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    MaximalIdealPowSuccQuot K n →+ MaximalIdealPowSuccQuot K n := by
  let f : MaximalIdealPowSuccQuot K n → MaximalIdealPowSuccQuot K n :=
    maximalIdealPowSuccQuotLift n
      (fun a => maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a))
      (maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects K n e)
  refine
    { toFun := f
      map_zero' := ?_
      map_add' := ?_ }
  · change f 0 = 0
    rw [← map_zero (maximalIdealPowSuccQuotMk K n)]
    dsimp only [f]
    rw [maximalIdealPowSuccQuotLift_mk, map_zero, map_zero]
  · intro x y
    change f (x + y) = f x + f y
    refine MaximalIdealPowSuccQuot.inductionOn₂ n
      (motive := fun x' y' => f (x' + y') = f x' + f y') x y ?_
    intro a b
    rw [← map_add (maximalIdealPowSuccQuotMk K n)]
    dsimp only [f]
    rw [maximalIdealPowSuccQuotLift_mk,
      maximalIdealPowSuccQuotLift_mk,
      maximalIdealPowSuccQuotLift_mk, map_add, map_add]
 

theorem maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K])
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
        (maximalIdealPowSuccQuotMk K n a) =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a) := by
  change maximalIdealPowSuccQuotLift n
      (fun b => maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e b))
      (maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects K n e)
      (maximalIdealPowSuccQuotMk K n a) =
    maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a)
  exact maximalIdealPowSuccQuotLift_mk n _ _ a
 
def maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    MaximalIdealPowSuccQuot K n ≃+ MaximalIdealPowSuccQuot K n where
  toFun := maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
  invFun := maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x' =>
        maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm
            (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e x') = x')
      x ?_
    intro a
    rw [maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk,
      maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk]
    have h := (maximalIdealPowMapEquivOfIntegerRingEquiv K n e).left_inv a
    exact congrArg (maximalIdealPowSuccQuotMk K n) h
  right_inv := by
    intro x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x' =>
        maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
            (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm x') = x')
      x ?_
    intro a
    rw [maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk,
      maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk]
    have h := (maximalIdealPowMapEquivOfIntegerRingEquiv K n e).right_inv a
    exact congrArg (maximalIdealPowSuccQuotMk K n) h
  map_add' := by
    intro x y
    exact map_add (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e) x y
 
theorem principalUnits_integerRingEquiv_mem_self
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (u : 𝒪[K]ˣ)
    (hu : u ∈ principalUnits K n) :
    Units.mapEquiv e.toMulEquiv u ∈ principalUnits K n :=
  principalUnits_integerRingEquiv_mem K n e
    (fun x hx => (integerRingEquiv_mem_maximalIdeal_pow K e n x).2 hx) u hu
 
def principalUnitsMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    principalUnits K n ≃* principalUnits K n where
  toFun u :=
    ⟨Units.mapEquiv e.toMulEquiv u.1,
      principalUnits_integerRingEquiv_mem_self K n e u.1 u.2⟩
  invFun u :=
    ⟨Units.mapEquiv e.symm.toMulEquiv u.1,
      principalUnits_integerRingEquiv_mem_self K n e.symm u.1 u.2⟩
  left_inv := by
    intro u
    ext
    simp
  right_inv := by
    intro u
    ext
    simp
  map_mul' := by
    intro a b
    ext
    simp
 
def principalUnitsSuccQuotMapOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    PrincipalUnitsSuccQuot K n →* PrincipalUnitsSuccQuot K n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk K n).comp
      (principalUnitsMapEquivOfIntegerRingEquiv K n e).toMonoidHom)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      exact principalUnits_integerRingEquiv_mem_self K (n + 1) e u.1 hu)
 

theorem principalUnitsSuccQuotMapOfIntegerRingEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (u : principalUnits K n) :
    principalUnitsSuccQuotMapOfIntegerRingEquiv K n e
        (principalUnitsSuccQuotMk K n u) =
      principalUnitsSuccQuotMk K n
        (principalUnitsMapEquivOfIntegerRingEquiv K n e u) :=
  rfl
 
def principalUnitsSuccQuotMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    PrincipalUnitsSuccQuot K n ≃* PrincipalUnitsSuccQuot K n where
  toFun := principalUnitsSuccQuotMapOfIntegerRingEquiv K n e
  invFun := principalUnitsSuccQuotMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine PrincipalUnitsSuccQuot.inductionOn n
      (motive := fun x' =>
        principalUnitsSuccQuotMapOfIntegerRingEquiv K n e.symm
            (principalUnitsSuccQuotMapOfIntegerRingEquiv K n e x') = x')
      x ?_
    intro u
    rw [principalUnitsSuccQuotMapOfIntegerRingEquiv_apply,
      principalUnitsSuccQuotMapOfIntegerRingEquiv_apply]
    have h := (principalUnitsMapEquivOfIntegerRingEquiv K n e).left_inv u
    exact congrArg
      (fun z : principalUnits K n =>
        principalUnitsSuccQuotMk K n z) h
  right_inv := by
    intro x
    refine PrincipalUnitsSuccQuot.inductionOn n
      (motive := fun x' =>
        principalUnitsSuccQuotMapOfIntegerRingEquiv K n e
            (principalUnitsSuccQuotMapOfIntegerRingEquiv K n e.symm x') = x')
      x ?_
    intro u
    rw [principalUnitsSuccQuotMapOfIntegerRingEquiv_apply,
      principalUnitsSuccQuotMapOfIntegerRingEquiv_apply]
    have h := (principalUnitsMapEquivOfIntegerRingEquiv K n e).right_inv u
    exact congrArg
      (fun z : principalUnits K n =>
        principalUnitsSuccQuotMk K n z) h
  map_mul' := by
    intro x y
    exact map_mul (principalUnitsSuccQuotMapOfIntegerRingEquiv K n e) x y
 

def principalUnitsSuccQuotAddEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    Additive (PrincipalUnitsSuccQuot K n) ≃+
      Additive (PrincipalUnitsSuccQuot K n) where
  toFun x :=
    Additive.ofMul
      (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e (Additive.toMul x))
  invFun x :=
    Additive.ofMul
      (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e.symm (Additive.toMul x))
  left_inv := by
    intro x
    change Additive.ofMul
        (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
          (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e (Additive.toMul x))) =
      Additive.ofMul (Additive.toMul x)
    exact congrArg Additive.ofMul
      ((principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e).left_inv
        (Additive.toMul x))
  right_inv := by
    intro x
    change Additive.ofMul
        (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e
          (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
            (Additive.toMul x))) =
      Additive.ofMul (Additive.toMul x)
    exact congrArg Additive.ofMul
      ((principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e).right_inv
        (Additive.toMul x))
  map_add' := by
    intro x y
    change Additive.ofMul
        (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Additive.toMul (x + y))) =
      Additive.ofMul
        (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e (Additive.toMul x) *
          principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e (Additive.toMul y))
    rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl]
    rw [map_mul]
 

@[simp]
theorem principalUnitsSuccQuotAddEquivOfIntegerRingEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (x : PrincipalUnitsSuccQuot K n) :
    principalUnitsSuccQuotAddEquivOfIntegerRingEquiv K n e (Additive.ofMul x) =
      Additive.ofMul (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e x) :=
  rfl
 

def maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    Multiplicative (MaximalIdealPowSuccQuot K n) ≃*
      Multiplicative (MaximalIdealPowSuccQuot K n) where
  toFun x :=
    Multiplicative.ofAdd
      (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
        (Multiplicative.toAdd x))
  invFun x :=
    Multiplicative.ofAdd
      (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
        (Multiplicative.toAdd x))
  left_inv := by
    intro x
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
          (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e).left_inv
        (Multiplicative.toAdd x))
  right_inv := by
    intro x
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e).right_inv
        (Multiplicative.toAdd x))
  map_mul' := by
    intro x y
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd (x * y))) =
      Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd x) +
        maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd y))
    rw [show Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x + Multiplicative.toAdd y from rfl]
    rw [map_add]
 

@[simp]
theorem maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (x : MaximalIdealPowSuccQuot K n) :
    maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv K n e
        (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e x) :=
  rfl
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.AdditiveEquiv -/
section
namespace LocalFieldTheory
noncomputable section
universe u
 
def additiveEquivOfMulEquiv {A B : Type u} [Group A] [Group B] (e : A ≃* B) :
    Additive A ≃+ Additive B where
  toFun := fun a => Additive.ofMul (e (Additive.toMul a))
  invFun := fun b => Additive.ofMul (e.symm (Additive.toMul b))
  left_inv := by
    intro a
    simp
  right_inv := by
    intro b
    simp
  map_add' := by
    intro a b
    ext
    exact e.map_mul _ _
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
 
def ResidueUnits (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝓀[K]ˣ
 
instance residueUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (ResidueUnits K) := by
  change CommGroup 𝓀[K]ˣ
  infer_instance
 
def residueUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    ResidueUnits K ≃* 𝓀[K]ˣ := by
  change 𝓀[K]ˣ ≃* 𝓀[K]ˣ
  exact MulEquiv.refl _
 

@[simp]
theorem residueUnitsConcreteEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K] (u : ResidueUnits K) :
    residueUnitsConcreteEquiv K u = u :=
  rfl
 
abbrev IntegerUnitsModPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K 1
 
instance integerUnitsModPrincipalUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (IntegerUnitsModPrincipalUnits K) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K 1)
  infer_instance
 
def integerUnitsModPrincipalUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    IntegerUnitsModPrincipalUnits K ≃*
      (𝒪[K]ˣ ⧸ principalUnits K 1) := by
  change (𝒪[K]ˣ ⧸ principalUnits K 1) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact MulEquiv.refl _
 
abbrev integerUnitsModPrincipalUnitsMk
    (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnits K := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact QuotientGroup.mk' (principalUnits K 1)
 

@[simp]
theorem integerUnitsModPrincipalUnitsConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsConcreteEquiv K
        (integerUnitsModPrincipalUnitsMk K x) =
      QuotientGroup.mk x :=
  rfl
 
protected theorem IntegerUnitsModPrincipalUnits.inductionOn
    {K : Type u} [Field K] [ValuativeRel K]
    {motive : IntegerUnitsModPrincipalUnits K → Prop}
    (q : IntegerUnitsModPrincipalUnits K)
    (h : ∀ x : 𝒪[K]ˣ, motive (integerUnitsModPrincipalUnitsMk K x)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K 1 from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x
 
def integerUnitsModPrincipalUnitsLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (f : 𝒪[K]ˣ →* M) (h : principalUnits K 1 ≤ f.ker) :
    IntegerUnitsModPrincipalUnits K →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K 1) →* M
  exact QuotientGroup.lift (principalUnits K 1) f h
 

@[simp]
theorem integerUnitsModPrincipalUnitsLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (f : 𝒪[K]ˣ →* M) (h : principalUnits K 1 ≤ f.ker) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsLift f h
        (integerUnitsModPrincipalUnitsMk K x) = f x :=
  rfl
 
def integerUnitsToResidueUnits (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* ResidueUnits K :=
  Units.map (IsLocalRing.residue 𝒪[K]).toMonoidHom
 

theorem integerUnitsToResidueUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    ((residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K x) : 𝓀[K]ˣ) :
        𝓀[K]) =
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) :=
  rfl
 
theorem mem_ker_integerUnitsToResidueUnits_iff (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    x ∈ (integerUnitsToResidueUnits K).ker ↔
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg (residueUnitsConcreteEquiv K) h
    have h'' := congrArg Units.val h'
    simpa only [integerUnitsToResidueUnits_apply, map_one, Units.val_one] using h''
  · intro h
    apply (residueUnitsConcreteEquiv K).injective
    apply Units.ext
    simpa only [integerUnitsToResidueUnits_apply, map_one, Units.val_one] using h
 
theorem principalUnits_one_eq_ker_integerUnitsToResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    principalUnits K 1 = (integerUnitsToResidueUnits K).ker := by
  ext x
  rw [mem_principalUnits_iff, mem_ker_integerUnitsToResidueUnits_iff]
  rw [pow_one]
  rw [← sub_eq_zero]
  rw [← map_one (IsLocalRing.residue 𝒪[K]), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.symm
 
theorem integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsToResidueUnits K x = 1 ↔ x ∈ principalUnits K 1 := by
  rw [principalUnits_one_eq_ker_integerUnitsToResidueUnits K, MonoidHom.mem_ker]
 
theorem integerUnitsToResidueUnits_surjective (K : Type u) [Field K] [ValuativeRel K] :
    Function.Surjective (integerUnitsToResidueUnits K) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (inferInstanceAs (IsLocalHom (IsLocalRing.residue 𝒪[K])))
 
def integerUnitsModPrincipalUnitsEquivResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    IntegerUnitsModPrincipalUnits K ≃* ResidueUnits K :=
  (integerUnitsModPrincipalUnitsConcreteEquiv K).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (principalUnits_one_eq_ker_integerUnitsToResidueUnits K)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (integerUnitsToResidueUnits K)
        (integerUnitsToResidueUnits_surjective K)))
 

@[simp]
theorem integerUnitsModPrincipalUnitsEquivResidueUnits_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsMk K x) =
      integerUnitsToResidueUnits K x := by
  simp only [integerUnitsModPrincipalUnitsEquivResidueUnits, MulEquiv.trans_apply,
    integerUnitsModPrincipalUnitsConcreteEquiv_mk,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rw [QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply,
    QuotientGroup.kerLift_mk]
 
def integerUnitsModPrincipalUnitsAddEquivResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    Additive (IntegerUnitsModPrincipalUnits K) ≃+ Additive (ResidueUnits K) :=
  additiveEquivOfMulEquiv (integerUnitsModPrincipalUnitsEquivResidueUnits K)
 
theorem IntegerUnitsModPrincipalUnits_mk_eq_mk_iff
    (K : Type u) [Field K] [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x =
        integerUnitsModPrincipalUnitsMk K y ↔
      x / y ∈ principalUnits K 1 :=
  by
    change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K 1) =
      QuotientGroup.mk y ↔ _
    exact QuotientGroup.eq_iff_div_mem (N := principalUnits K 1)
 
theorem IntegerUnitsModPrincipalUnits_mk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x = 1 ↔
      x ∈ principalUnits K 1 :=
  by
    change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K 1) = 1 ↔ _
    exact QuotientGroup.eq_one_iff (N := principalUnits K 1) x
 
@[simp]
theorem integerUnitsModPrincipalUnitsAddEquivResidueUnits_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAddEquivResidueUnits K
        (Additive.ofMul (integerUnitsModPrincipalUnitsMk K x)) =
      Additive.ofMul (integerUnitsToResidueUnits K x) := by
  exact congrArg Additive.ofMul
    (integerUnitsModPrincipalUnitsEquivResidueUnits_mk K x)
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
 

def integerRingMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝒪[K] →+* 𝒪[L] :=
  algebraMap 𝒪[K] 𝒪[L]
 
instance integerRingMapOfValuationExtension_isLocalHom (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IsLocalHom (integerRingMapOfValuationExtension K L) := by
  change IsLocalHom (algebraMap 𝒪[K] 𝒪[L])
  infer_instance
 
@[simp]
theorem integerRingMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    integerRingMapOfValuationExtension K L x = algebraMap 𝒪[K] 𝒪[L] x :=
  rfl
 


def residueFieldMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[K] →+* 𝓀[L] :=
  IsLocalRing.ResidueField.map (integerRingMapOfValuationExtension K L)
 

theorem residueFieldMapOfValuationExtension_eq_algebraMap (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    residueFieldMapOfValuationExtension K L = algebraMap 𝓀[K] 𝓀[L] :=
  rfl
 

@[simp]
theorem residueFieldMapOfValuationExtension_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    residueFieldMapOfValuationExtension K L (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (integerRingMapOfValuationExtension K L x) :=
  rfl
 
@[simp]
theorem residueField_algebraMap_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) :=
  rfl
 
def residueUnitsMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[K]ˣ →* 𝓀[L]ˣ :=
  Units.map (residueFieldMapOfValuationExtension K L)
 

@[simp]
theorem residueUnitsMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝓀[K]ˣ) :
    ((residueUnitsMapOfValuationExtension K L u : 𝓀[L]ˣ) : 𝓀[L]) =
      algebraMap 𝓀[K] 𝓀[L] (u : 𝓀[K]) :=
  rfl
 
theorem residueUnitsMapOfValuationExtension_injective (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Injective (residueUnitsMapOfValuationExtension K L) :=
  Units.map_injective (RingHom.injective (residueFieldMapOfValuationExtension K L))
 
def integerUnitsMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝒪[K]ˣ →* 𝒪[L]ˣ :=
  Units.map (integerRingMapOfValuationExtension K L).toMonoidHom
 

@[simp]
theorem integerUnitsMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    ((integerUnitsMapOfValuationExtension K L u : 𝒪[L]ˣ) : 𝒪[L]) =
      integerRingMapOfValuationExtension K L (u : 𝒪[K]) :=
  rfl
 

@[simp]
theorem residueUnitsMap_integerUnitsToResidueUnits (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    residueUnitsMapOfValuationExtension K L (integerUnitsToResidueUnits K u) =
      integerUnitsToResidueUnits L (integerUnitsMapOfValuationExtension K L u) := by
  ext
  rfl
 
theorem integerUnitsMapOfValuationExtension_mem_principalUnits_one (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) (hu : u ∈ principalUnits K 1) :
    integerUnitsMapOfValuationExtension K L u ∈ principalUnits L 1 := by
  rw [← integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one L]
  rw [← residueUnitsMap_integerUnitsToResidueUnits K L u]
  rw [(integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K u).2 hu]
  exact map_one (residueUnitsMapOfValuationExtension K L)
 
def integerUnitsModPrincipalUnitsMapOfValuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IntegerUnitsModPrincipalUnits K →* IntegerUnitsModPrincipalUnits L :=
  integerUnitsModPrincipalUnitsLift
    ((integerUnitsModPrincipalUnitsMk L).comp
      (integerUnitsMapOfValuationExtension K L))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        IntegerUnitsModPrincipalUnits_mk_eq_one_iff]
      exact integerUnitsMapOfValuationExtension_mem_principalUnits_one K L u hu)
 
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfValuationExtension_mk (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsMk K u) =
      integerUnitsModPrincipalUnitsMk L
        (integerUnitsMapOfValuationExtension K L u) :=
  rfl
 




def integerUnitsModPrincipalUnitsResidueNormOfValuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IntegerUnitsModPrincipalUnits L →* IntegerUnitsModPrincipalUnits K :=
  (integerUnitsModPrincipalUnitsEquivResidueUnits K).symm.toMonoidHom.comp
    ((Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))).comp
      (integerUnitsModPrincipalUnitsEquivResidueUnits L).toMonoidHom)
 

theorem integerUnitsModPrincipalUnitsResidueNorm_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : IntegerUnitsModPrincipalUnits L) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x) := by
  change
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        ((integerUnitsModPrincipalUnitsEquivResidueUnits K).symm
          (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
            (integerUnitsModPrincipalUnitsEquivResidueUnits L x))) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x)
  exact (integerUnitsModPrincipalUnitsEquivResidueUnits K).apply_symm_apply _
 

theorem residueUnitsMap_residueField_norm_eq_prod_algEquiv (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝓀[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])) u) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv u) := by
  ext
  change algebraMap 𝓀[K] 𝓀[L] (Algebra.norm 𝓀[K] (u : 𝓀[L])) =
    ↑(Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      Units.mapEquiv τ.toMulEquiv u))
  rw [Algebra.norm_eq_prod_automorphisms]
  simp
 

theorem integerUnitsModPrincipalUnitsResidueNorm_base_extend_eq_prod_algEquiv
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x)) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv (integerUnitsModPrincipalUnitsEquivResidueUnits L x)) := by
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  exact residueUnitsMap_residueField_norm_eq_prod_algEquiv K L
    (integerUnitsModPrincipalUnitsEquivResidueUnits L x)
 

theorem residueAlgEquiv_card_eq_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Module.finrank 𝓀[K] 𝓀[L] :=
  IsGalois.card_aut_eq_finrank (F := 𝓀[K]) (E := 𝓀[L])
 


theorem maximalIdeal_inertiaDeg_eq_residue_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Ideal.inertiaDeg' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) =
      Module.finrank 𝓀[K] 𝓀[L] := by
  rw [Ideal.inertiaDeg'_algebraMap]
  rfl
 


theorem integerRing_moduleFinite_of_isIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Module.Finite 𝒪[K] 𝒪[L] :=
  IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]
 

theorem maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Ideal.inertiaDeg' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) =
        Module.finrank K L := by
  classical
  have := FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L
  have hp := IsDiscreteValuationRing.not_a_field 𝒪[K]
  have hprimes := IsLocalRing.primesOver_eq (A := 𝒪[L]) hp
  have hq (q : (𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :
      (q : Ideal 𝒪[L]) = 𝓂[L] :=
    Set.mem_singleton_iff.mp (hprimes ▸ q.property)
  let : Unique ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :=
    { default := ⟨𝓂[L], hprimes ▸ Set.mem_singleton _⟩
      uniq := fun q => Subtype.ext (Set.mem_singleton_iff.mp (hprimes ▸ q.property)) }
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    Ideal.inertiaDeg'_eq_inertiaDeg,
    IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L]
  simpa only [Fintype.sum_unique, hq] using
    (Ideal.sum_ramification_inertia_eq_finrank (𝓂[K] : Ideal 𝒪[K]) 𝒪[L])
 

theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] =
        Module.finrank K L := by
  rw [← maximalIdeal_inertiaDeg_eq_residue_finrank K L]
  exact maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank K L
 
theorem residueFieldAlgebra_isSeparable_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Algebra.IsSeparable 𝓀[K] 𝓀[L] := by
  infer_instance
 

theorem residueField_trace_surjective_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Algebra.trace 𝓀[K] 𝓀[L]) := by
  let : Algebra.IsSeparable 𝓀[K] 𝓀[L] :=
    residueFieldAlgebra_isSeparable_of_valuationExtension K L
  exact Algebra.trace_surjective 𝓀[K] 𝓀[L]
 

theorem residueField_units_norm_surjective_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))) := by
  let := Fintype.ofFinite 𝓀[K]
  exact FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L]
 
theorem integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective
      (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L) := by
  intro y
  obtain ⟨v, hv⟩ := residueField_units_norm_surjective_of_valuationExtension K L
    (integerUnitsModPrincipalUnitsEquivResidueUnits K y)
  refine ⟨(integerUnitsModPrincipalUnitsEquivResidueUnits L).symm v, ?_⟩
  apply (integerUnitsModPrincipalUnitsEquivResidueUnits K).injective
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  exact (congrArg (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])))
    ((integerUnitsModPrincipalUnitsEquivResidueUnits L).apply_symm_apply v)).trans hv
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
 






theorem galoisGroup_mem_integerRing_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    σ (x : L) ∈ 𝒪[L] := by
  have hx : IsIntegral 𝒪[K] ((x : 𝒪[L]) : L) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2
      ⟨x, rfl⟩
  have hσ : IsIntegral 𝒪[K] (σ ((x : 𝒪[L]) : L)) :=
    IsIntegral.map σ.toAlgHom hx
  rcases (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hσ
    with ⟨y, hy⟩
  exact hy ▸ y.2
 

def galoisGroupIntegerRingEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    𝒪[L] ≃+* 𝒪[L] where
  toFun x :=
    ⟨σ (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ x⟩
  invFun x :=
    ⟨σ.symm (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ.symm x⟩
  left_inv := by
    intro x
    ext
    simp
  right_inv := by
    intro x
    ext
    simp
  map_mul' := by
    intro x y
    ext
    simp
  map_add' := by
    intro x y
    ext
    simp
 

@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x : 𝒪[L]) : L) =
      σ (x : L) :=
  rfl
 
@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    (((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).symm x : 𝒪[L]) : L) =
      σ.symm (x : L) :=
  rfl
 

def galoisGroupIntegerRingEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝒪[L] ≃+* 𝒪[L]) where
  toFun := galoisGroupIntegerRingEquivOfIsIntegralClosure K L
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    rfl
 

abbrev galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulSemiringAction (Gal(L / K)) 𝒪[L] :=
  MulSemiringAction.compHom 𝒪[L] (galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L)
 

theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[K]) :
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerRingMapOfValuationExtension K L x) =
      integerRingMapOfValuationExtension K L x := by
  ext
  change σ (algebraMap K L (x : K)) = algebraMap K L (x : K)
  exact σ.commutes (x : K)
 

theorem galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulCommClass (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ x y
  rw [Algebra.smul_def, Algebra.smul_def]
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x * y) =
    algebraMap 𝒪[K] 𝒪[L] x *
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ y
  rw [map_mul]
  have hx : galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x) = algebraMap 𝒪[K] 𝒪[L] x := by
    simpa [integerRingMapOfValuationExtension] using
      galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap K L σ x
  rw [hx]
 

theorem galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulDistribClass (Gal(L / K)) 𝒪[L] L := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ r s
  change σ (((r : 𝒪[L]) : L) * s) =
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r : 𝒪[L]) : L) * σ s
  rw [map_mul]
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
 


theorem galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    IsGaloisGroup (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    IsIntegralClosure.isIntegral_algebra 𝒪[K] L
  exact IsGaloisGroup.of_isFractionRing (Gal(L / K)) 𝒪[K] 𝒪[L] K L
 
abbrev galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    DistribMulAction (Gal(L / K)) (Ideal 𝒪[L]) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact Ideal.pointwiseDistribMulAction
 

abbrev galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulAction (Gal(L / K)) (Ideal 𝒪[L]) := by
  exact (galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L).toMulAction
 
theorem galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) :
    Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
        (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
      (𝓂[L] : Ideal 𝒪[L]) =
      (𝓂[L] : Ideal 𝒪[L]) := by
  change Ideal.map
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toRingHom
      (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L] : Ideal 𝒪[L])
  exact integerRingEquiv_map_maximalIdeal L
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)
 

theorem galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) :
    σ ∈ @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) := by
  rw [@MulAction.mem_stabilizer_iff (Gal(L / K)) (Ideal 𝒪[L]) _
    (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)]
  change Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
      (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
        (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L] : Ideal 𝒪[L])
  exact galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure K L σ
 

def galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) where
  toFun σ :=
    ⟨σ, galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure K L σ⟩
  map_one' := by
    ext
    rfl
  map_mul' σ τ := by
    ext
    rfl
 

def galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L / K)) :
    principalUnits L n ≃* principalUnits L n :=
  principalUnitsMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)
 

theorem galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L / K)) (u : principalUnits L n) :
    ((galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u :
        principalUnits L n) : 𝒪[L]ˣ) =
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u.1 :=
  rfl
 

theorem galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (Finset.univ.prod fun σ : Gal(L / K) =>
        1 + galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  classical
  refine finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ L
    (Finset.univ : Finset (Gal(L / K))) n hn
    (fun σ => galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ?_
  intro σ _
  exact (integerRingEquiv_mem_maximalIdeal_pow L
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n (a : 𝒪[L])).2 a.2
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
 





def galoisGroupResidueFieldEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    𝓀[L] ≃+* 𝓀[L] :=
  IsLocalRing.ResidueField.mapEquiv
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)
 

@[simp]
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) (x : 𝒪[L]) :
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
        (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) := by
  rfl
 
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) (u : 𝒪[L]ˣ) :
    Units.mapEquiv (galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ).toMulEquiv
        (integerUnitsToResidueUnits L u) =
      integerUnitsToResidueUnits L
        (Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) := by
  ext
  rfl
 
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) (x : 𝓀[K]) :
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ (algebraMap 𝓀[K] 𝓀[L] x) =
      algebraMap 𝓀[K] 𝓀[L] x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
      (algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] a)) =
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] a)
  rw [residueField_algebraMap_residue K L a]
  rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue]
  exact congrArg (fun z : 𝒪[L] => IsLocalRing.residue 𝒪[L] z)
    (galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap K L σ a)
 
abbrev galoisGroupResidueAlgEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] where
  __ := galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
  commutes' := galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap K L σ
 
def galoisGroupResidueAlgEquivHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun := galoisGroupResidueAlgEquivOfIsIntegralClosure K L
  map_one' := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_mul' := by
    intro σ τ
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
 

@[simp]
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L σ =
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ :=
  rfl
 

theorem galoisGroup_sum_residue_eq_residueAlgEquiv_sum_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (a : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a) =
      Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ
          (IsLocalRing.residue 𝒪[L] a) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  simp [galoisGroupResidueAlgEquivOfIsIntegralClosure]
 

def galoisGroupResidueStabilizerHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    @MulAction.stabilizer Gal(L / K) (Ideal 𝒪[L]) _
        (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
        (𝓂[L] : Ideal 𝒪[L]) →*
      (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  letI := galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure K L
  letI := galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L
  exact Ideal.Quotient.stabilizerHom (𝓂[L] : Ideal 𝒪[L])
    (𝓂[K] : Ideal 𝒪[K]) Gal(L / K)
 
def galoisGroupMaximalIdealInertiaOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Subgroup Gal(L / K) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact (𝓂[L] : Ideal 𝒪[L]).toAddSubgroup.inertia Gal(L / K)
 
def galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).comp
    (galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure K L)
 

theorem galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure_eq
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure K L =
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L := by
  ext σ x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_stabilizerHom
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure K L σ ∈
        (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).ker := by
  rw [← galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure_eq K L]
  rfl
 
theorem galoisGroupResidueStabilizerHomOfIsIntegralClosure_ker_eq_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).ker =
      (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L).subgroupOf
        (@MulAction.stabilizer Gal(L / K) (Ideal 𝒪[L]) _
          (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
          (𝓂[L] : Ideal 𝒪[L])) := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure K L
  let := galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L
  exact Ideal.Quotient.ker_stabilizerHom (𝓂[L] : Ideal 𝒪[L])
    (𝓂[K] : Ideal 𝒪[K]) Gal(L / K)
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_mem_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      σ ∈ galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_stabilizerHom]
  rw [galoisGroupResidueStabilizerHomOfIsIntegralClosure_ker_eq_maximalIdealInertia K L]
  rfl
 
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker =
      galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L := by
  ext σ
  exact galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_mem_maximalIdealInertia
    K L σ
 

theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdxIn
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) =
      (𝓂[K] : Ideal 𝒪[K]).ramificationIdxIn 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    integerRing_moduleFinite_of_isIntegralClosure K L
  let : Algebra.IsSeparable (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))
      (𝒪[L] ⧸ (𝓂[L] : Ideal 𝒪[L])) :=
    residueFieldAlgebra_isSeparable_of_valuationExtension K L
  let : Finite (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) := by
    change Finite 𝓀[K]
    infer_instance
  simpa [galoisGroupMaximalIdealInertiaOfIsIntegralClosure] using
    (Ideal.card_inertia_eq_ramificationIdxIn
      (R := 𝒪[K]) (S := 𝒪[L]) (G := Gal(L / K))
      (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]))
 

theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure K L
  rw [galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdxIn K L]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx
    (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) Gal(L / K)
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia K L]
  exact galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx K L
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_ramificationIdx_eq_one
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (h :
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1) :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker = 1 := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx K L, h]
end
end LocalFieldTheory
end

/- ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.NormSide -/
section
noncomputable section
universe u
namespace LocalClassFieldTheory
open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
 





theorem integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (u : 𝒪[L]ˣ) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) := by
  ext
  have hfield := mapBaseUnits_normUnits_eq_prod_gal (K := K) (L := L)
    (integerUnitsToFieldUnits L u)
  have hfield' := congrArg (fun z : Lˣ => (z : L)) hfield
  simp only [mapBaseUnitsToExtensionUnits_apply_coe, normUnits_apply_coe,
    integerUnitsToFieldUnits_apply] at hfield'
  change (algebraMap K L (((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) : K)) =
      (((Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) : 𝒪[L]ˣ) :
          𝒪[L]) : L)
  rw [normIntegerUnits_apply_coe]
  simpa [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply] using hfield'
 

theorem galoisGroup_prod_mem_principalUnits_of_isIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    Finset.univ.prod (fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) ∈
        principalUnits L n := by
  simpa using (Subgroup.prod_mem (principalUnits L n) (t := Finset.univ)
    (f := fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u)
    (fun σ _ =>
      principalUnits_integerRingEquiv_mem_self L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) u hu))
 

theorem integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u) ∈
      principalUnits L n := by
  rw [integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u]
  exact galoisGroup_prod_mem_principalUnits_of_isIntegralClosure K L n u hu
 



noncomputable def principalUnitsNormExtensionSideOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L] (n : Nat) :
    principalUnits L n →* principalUnits L n where
  toFun u :=
    ⟨integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1),
      integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
        K L n u.1 u.2⟩
  map_one' := by
    ext
    simp [integerUnitsMapOfValuationExtension]
  map_mul' := by
    intro u v
    ext
    simp [integerUnitsMapOfValuationExtension]
 
@[simp]
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    ((principalUnitsNormExtensionSideOfIsIntegralClosure K L n u :
        principalUnits L n) : 𝒪[L]ˣ) =
      integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1) :=
  rfl
 

theorem principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsNormExtensionSideOfIsIntegralClosure K L n u =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) := by
  apply Subtype.ext
  simpa [principalUnitsNormExtensionSideOfIsIntegralClosure_apply,
    galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply] using
    integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u.1
 

theorem principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (((principalUnitsNormExtensionSideOfIsIntegralClosure K L n
          (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2) :
        principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  classical
  rw [principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod K L n
    (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)]
  simpa [galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure,
    principalUnitsMapEquivOfIntegerRingEquiv,
    principalUnitOneAddOfMemPowSubgroup, principalUnitOneAddOfMemPow_val]
    using
      galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
        K L n hn a
end LocalClassFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients -/
section
namespace LocalFieldTheory
noncomputable section
universe u
open scoped ValuativeRel
 




def integerRingModMaximalIdealAddEquivResidue
    (K : Type u) [Field K] [ValuativeRel K] :
    (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) ≃+ 𝓀[K] :=
  AddEquiv.refl _
 

@[simp]
theorem integerRingModMaximalIdealAddEquivResidue_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]) :
    integerRingModMaximalIdealAddEquivResidue K
        (Ideal.Quotient.mk (𝓂[K] : Ideal 𝒪[K]) x) =
      IsLocalRing.residue 𝒪[K] x :=
  rfl
 

def chosenIntegerRingUniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 𝒪[K] :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[K])
 
theorem chosenIntegerRingUniformizer_irreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Irreducible (chosenIntegerRingUniformizer K) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[K])
 
theorem chosenIntegerRingUniformizer_maximalIdeal_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (𝓂[K] : Ideal 𝒪[K]) = Ideal.span ({chosenIntegerRingUniformizer K} : Set 𝒪[K]) :=
  (chosenIntegerRingUniformizer_irreducible K).maximalIdeal_eq
 




def integerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  Units.mk0 (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) (by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible K).ne_zero (Subtype.ext h))
 

@[simp]
theorem integerRingUniformizerFieldUnit_coe
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ((integerRingUniformizerFieldUnit K : Kˣ) : K) =
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) :=
  rfl
 




def inverseIntegerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  (integerRingUniformizerFieldUnit K)⁻¹
 
@[simp]
theorem inverseIntegerRingUniformizerFieldUnit_coe
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ((inverseIntegerRingUniformizerFieldUnit K : Kˣ) : K) =
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K))⁻¹ :=
  rfl
 

theorem maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) (n : Nat) :
    (𝓂[K] ^ n : Ideal 𝒪[K]) = Ideal.span ({ϖ ^ n} : Set 𝒪[K]) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
 
theorem maximalIdeal_pow_eq_span_uniformizer_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    (𝓂[K] ^ n : Ideal 𝒪[K]) =
      Ideal.span ({chosenIntegerRingUniformizer K ^ n} : Set 𝒪[K]) :=
  maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible K
    (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n
 

theorem mul_uniformizer_pow_mem_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    r * ϖ ^ n ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  rw [maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible K ϖ hϖ n]
  rw [Ideal.mem_span_singleton]
  exact ⟨r, by rw [mul_comm]⟩
 

theorem mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    r * ϖ ^ n ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) ↔
      r ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hne : ϖ ^ n ≠ 0 := pow_ne_zero n hϖ.ne_zero
    have hcancel : r * ϖ ^ n = (ϖ * c) * ϖ ^ n := by
      calc
        r * ϖ ^ n = ϖ ^ (n + 1) * c := hc
        _ = (ϖ * c) * ϖ ^ n := by
          rw [pow_succ']
          ring
    exact mul_right_cancel₀ hne hcancel
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc]
    rw [pow_succ']
    ring
 
def maximalIdealPowMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun r := ⟨r * ϖ ^ n, mul_uniformizer_pow_mem_maximalIdeal_pow K ϖ hϖ n r⟩
  map_add' r s := by
    ext
    simp [add_mul]
  map_smul' a r := by
    ext
    simp [mul_assoc]
 

@[simp]
theorem maximalIdealPowMulUniformizerPowMap_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r : 𝒪[K]) =
      r * ϖ ^ n :=
  rfl
 
def maximalIdealPowSuccQuotMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] MaximalIdealPowSuccQuot K n :=
  (maximalIdealPowSuccQuotMk K n).comp
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n)
 

@[simp]
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n r =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) :=
  rfl
 
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_ker
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    LinearMap.ker (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n) =
      (𝓂[K] : Ideal 𝒪[K]) := by
  ext r
  rw [LinearMap.mem_ker]
  change maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) = 0 ↔
    r ∈ (𝓂[K] : Ideal 𝒪[K])
  rw [maximalIdealPowSuccQuotMk_eq_zero_iff]
  change r * ϖ ^ n ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) ↔
    r ∈ (𝓂[K] : Ideal 𝒪[K])
  exact mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff K ϖ hϖ n r
 

theorem maximalIdealPowSuccQuotMulUniformizerPowMap_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    Function.Surjective (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n) := by
  intro x
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x' =>
      ∃ r, maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n r = x')
    x ?_
  intro a
  have ha_span : (a : 𝒪[K]) ∈ Ideal.span ({ϖ ^ n} : Set 𝒪[K]) := by
    simpa [maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible K ϖ hϖ n] using a.2
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  change maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) =
    maximalIdealPowSuccQuotMk K n a
  have hrep : maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r = a := by
    ext
    simp [maximalIdealPowMulUniformizerPowMap, hr, mul_comm]
  rw [hrep]
 

def residueLinearEquivMaximalIdealPowSuccQuotOfIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝓀[K] ≃ₗ[𝒪[K]] MaximalIdealPowSuccQuot K n :=
  (Submodule.quotEquivOfEq (𝓂[K] : Submodule 𝒪[K] 𝒪[K])
      (LinearMap.ker (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n))
      (maximalIdealPowSuccQuotMulUniformizerPowMap_ker K ϖ hϖ n).symm).trans
    ((maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n).quotKerEquivOfSurjective
      (maximalIdealPowSuccQuotMulUniformizerPowMap_surjective K ϖ hϖ n))
 
def residueAddEquivMaximalIdealPowSuccQuotOfIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝓀[K] ≃+ MaximalIdealPowSuccQuot K n :=
  (residueLinearEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n).toAddEquiv
 

@[simp]
theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n
        (IsLocalRing.residue 𝒪[K] r) =
    maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n r := by
  let f := maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n
  let hker : (𝓂[K] : Submodule 𝒪[K] 𝒪[K]) = LinearMap.ker f :=
    (maximalIdealPowSuccQuotMulUniformizerPowMap_ker K ϖ hϖ n).symm
  change (Submodule.quotEquivOfEq (𝓂[K] : Submodule 𝒪[K] 𝒪[K])
        (LinearMap.ker f) hker).trans
      (f.quotKerEquivOfSurjective
        (maximalIdealPowSuccQuotMulUniformizerPowMap_surjective K ϖ hϖ n))
      (Submodule.Quotient.mk r) = f r
  rw [LinearEquiv.trans_apply]
  have hquot :
      Submodule.quotEquivOfEq (𝓂[K] : Submodule 𝒪[K] 𝒪[K])
          (LinearMap.ker f) hker (Submodule.Quotient.mk r) =
        (Submodule.Quotient.mk r : 𝒪[K] ⧸ LinearMap.ker f) := by
    exact Submodule.quotEquivOfEq_mk
      (p := (𝓂[K] : Submodule 𝒪[K] 𝒪[K])) (p' := LinearMap.ker f) hker r
  rw [hquot]
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
 



def principalUnitsSuccQuotAddEquivResidueOfIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) :
    Additive (PrincipalUnitsSuccQuot K n) ≃+ 𝓀[K] :=
  (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm.trans
    (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n).symm
 

@[simp]
theorem principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[K]) :
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible K ϖ hϖ n hn).symm x =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n x) :=
  rfl
 

@[simp]
theorem principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[K]) :
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible K ϖ hϖ n hn).symm
        (IsLocalRing.residue 𝒪[K] r) =
      Additive.ofMul
        (principalUnitsSuccQuotMk K n
          (principalUnitOneAddOfMemPowSubgroup K hn
            ((maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r :
              (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K])
            (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r).2)) := by
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue]
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_apply]
  rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
  rfl
 



noncomputable def principalUnitsSuccQuotUniformizerCoord
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[K]) :
    PrincipalUnitsSuccQuot K n :=
  principalUnitsSuccQuotMk K n
    (principalUnitOneAddOfMemPowSubgroup K hn
      ((maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r :
        (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K])
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r).2)
 
@[simp]
theorem principalUnitsSuccQuotUniformizerCoord_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) :
    principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn 0 = 1 := by
  change principalUnitsSuccQuotOfIdealPow K n hn
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n 0) = 1
  rw [map_zero]
  exact principalUnitsSuccQuotOfIdealPow_zero K n hn
 


theorem principalUnitsSuccQuotUniformizerCoord_add
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r s : 𝒪[K]) :
    principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn (r + s) =
      principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r *
        principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn s := by
  change principalUnitsSuccQuotOfIdealPow K n hn
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n (r + s)) =
    principalUnitsSuccQuotOfIdealPow K n hn
        (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) *
      principalUnitsSuccQuotOfIdealPow K n hn
        (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n s)
  rw [map_add]
  exact principalUnitsSuccQuotOfIdealPow_add K n hn
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r)
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n s)
 

noncomputable def principalUnitsSuccQuotUniformizerCoordAddHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) :
    𝒪[K] →+ Additive (PrincipalUnitsSuccQuot K n) where
  toFun r := Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r)
  map_zero' := by
    change Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn 0) = 0
    rw [principalUnitsSuccQuotUniformizerCoord_zero]
    rfl
  map_add' r s := by
    change Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn (r + s)) =
      Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r) +
        Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn s)
    rw [principalUnitsSuccQuotUniformizerCoord_add]
    rfl
 

@[simp]
theorem principalUnitsSuccQuotUniformizerCoordAddHom_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[K]) :
    principalUnitsSuccQuotUniformizerCoordAddHom K ϖ hϖ n hn r =
      Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r) :=
  rfl
end
end LocalFieldTheory
end

/- ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified -/
section
namespace LocalFieldTheory
noncomputable section
universe u
namespace IsNonarchimedeanLocalField
open scoped ValuativeRel
 



class IsUnramifiedValuedExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop where
   
  maximalIdeal_ramificationIdx_eq_one :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1
 
theorem unramifiedValuation_ramificationIdx_eq_one
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L] :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1 :=
  IsUnramifiedValuedExtension.maximalIdeal_ramificationIdx_eq_one
    (K := K) (L := L)
 

theorem unramifiedValuation_residue_finrank_eq_finrank
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  have h :=
    LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K L
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    unramifiedValuation_ramificationIdx_eq_one K L, one_mul] at h
  exact h
end IsNonarchimedeanLocalField
open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open Filter
 

theorem maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (𝓂[K] : Ideal 𝒪[K]) =
      (𝓂[L] : Ideal 𝒪[L]) := by
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ := by
    exact Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  have hfact := Ideal.map_algebraMap_eq_finsetProd_pow
    (R := 𝒪[L]) (S := 𝒪[K]) (p := (𝓂[K] : Ideal 𝒪[K])) hp
  have hfin : ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]).toFinset =
      ({(𝓂[L] : Ideal 𝒪[L])} : Finset (Ideal 𝒪[L])) := by
    ext P
    simp [IsLocalRing.primesOver_eq 𝒪[L] hp]
  rw [hfin] at hfact
  simpa [LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one K L]
    using hfact
 

theorem integerRingMap_uniformizer_irreducible_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Irreducible (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  calc
    (𝓂[L] : Ideal 𝒪[L]) =
        Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (𝓂[K] : Ideal 𝒪[K]) :=
      (maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation K L).symm
    _ = Ideal.map (algebraMap 𝒪[K] 𝒪[L])
        (Ideal.span ({chosenIntegerRingUniformizer K} : Set 𝒪[K])) := by
          rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    _ = Ideal.span
        ({integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)} :
          Set 𝒪[L]) := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl
 



theorem integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {a : 𝒪[K]} (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    integerRingMapOfValuationExtension K L a ∈ (𝓂[L] ^ n : Ideal 𝒪[L]) := by
  let πK : 𝒪[K] := chosenIntegerRingUniformizer K
  have hπL : Irreducible (integerRingMapOfValuationExtension K L πK) := by
    simpa [πK] using integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  have ha_span : a ∈ Ideal.span ({πK ^ n} : Set 𝒪[K]) := by
    simpa [πK, maximalIdeal_pow_eq_span_uniformizer_pow K n] using ha
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  rw [maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible L
    (integerRingMapOfValuationExtension K L πK) hπL n]
  rw [Ideal.mem_span_singleton]
  refine ⟨integerRingMapOfValuationExtension K L r, ?_⟩
  simp [integerRingMapOfValuationExtension, hr, map_pow]
 

def maximalIdealPowMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →+ ((𝓂[L] ^ n : Ideal 𝒪[L]) : Type u) where
  toFun a :=
    ⟨integerRingMapOfValuationExtension K L (a : 𝒪[K]),
      integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n a.2⟩
  map_zero' := by
    ext
    simp [integerRingMapOfValuationExtension]
  map_add' a b := by
    ext
    simp [integerRingMapOfValuationExtension]
 

@[simp]
theorem maximalIdealPowMapOfUnramifiedValuation_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    (maximalIdealPowMapOfUnramifiedValuation K L n a : 𝒪[L]) =
      integerRingMapOfValuationExtension K L (a : 𝒪[K]) :=
  rfl
 

def maximalIdealPowSuccQuotMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    MaximalIdealPowSuccQuot K n →+ MaximalIdealPowSuccQuot L n :=
  QuotientAddGroup.map
    (maximalIdealPowSuccSubmodule K n).toAddSubgroup
    (maximalIdealPowSuccSubmodule L n).toAddSubgroup
    (maximalIdealPowMapOfUnramifiedValuation K L n)
    (by
      intro a ha
      exact (mem_maximalIdealPowSuccSubmodule_iff L n
        (maximalIdealPowMapOfUnramifiedValuation K L n a)).2
        (integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L (n + 1)
          ((mem_maximalIdealPowSuccSubmodule_iff K n a).1 ha)))
 

theorem maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (maximalIdealPowSuccQuotMk K n a) =
      maximalIdealPowSuccQuotMk L n
        (maximalIdealPowMapOfUnramifiedValuation K L n a) :=
  QuotientAddGroup.map_mk _ _ _ _ a
 

theorem maximalIdealPowMapOfUnramifiedValuation_mul_uniformizer_pow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowMapOfUnramifiedValuation K L n
        (maximalIdealPowMulUniformizerPowMap K (chosenIntegerRingUniformizer K)
          (chosenIntegerRingUniformizer_irreducible K) n r) =
      maximalIdealPowMulUniformizerPowMap L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (integerRingMapOfValuationExtension K L r) := by
  ext
  simp [maximalIdealPowMulUniformizerPowMap, integerRingMapOfValuationExtension, map_pow]
 

theorem maximalIdealPowSuccQuotMapOfUnramifiedValuation_mul_uniformizer_pow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (maximalIdealPowSuccQuotMulUniformizerPowMap K (chosenIntegerRingUniformizer K)
          (chosenIntegerRingUniformizer_irreducible K) n r) =
      maximalIdealPowSuccQuotMulUniformizerPowMap L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (integerRingMapOfValuationExtension K L r) := by
  rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply,
    maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk,
    maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
  exact congrArg (maximalIdealPowSuccQuotMk L n)
    (maximalIdealPowMapOfUnramifiedValuation_mul_uniformizer_pow K L n r)
 


theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map_residue
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n
          (IsLocalRing.residue 𝒪[K] r)) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (residueFieldMapOfValuationExtension K L (IsLocalRing.residue 𝒪[K] r)) := by
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue,
    maximalIdealPowSuccQuotMapOfUnramifiedValuation_mul_uniformizer_pow]
  rw [residueFieldMapOfValuationExtension_residue]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue]
 





theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (x : 𝓀[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n x) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (residueFieldMapOfValuationExtension K L x) := by
  refine Quotient.inductionOn' x ?_
  intro r
  exact residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map_residue K L n r
 

theorem integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {u : 𝒪[K]ˣ} (hu : u ∈ principalUnits K n) :
    integerUnitsMapOfValuationExtension K L u ∈ principalUnits L n := by
  rw [mem_principalUnits_iff] at hu ⊢
  have hmap :=
    integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n hu
  simpa [integerUnitsMapOfValuationExtension_apply, integerRingMapOfValuationExtension,
    sub_eq_add_neg] using hmap
 

def principalUnitsMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    principalUnits K n →* principalUnits L n where
  toFun u :=
    ⟨integerUnitsMapOfValuationExtension K L u.1,
      integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
        K L n u.2⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp
 

@[simp]
theorem principalUnitsMapOfUnramifiedValuation_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits K n) :
    ((principalUnitsMapOfUnramifiedValuation K L n u : principalUnits L n) :
        𝒪[L]ˣ) =
      integerUnitsMapOfValuationExtension K L u.1 :=
  rfl
 

theorem principalUnitsMapOfUnramifiedValuation_oneAdd (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsMapOfUnramifiedValuation K L n
        (principalUnitOneAddOfMemPowSubgroup K hn (a : 𝒪[K]) a.2) =
      principalUnitOneAddOfMemPowSubgroup L hn
        (integerRingMapOfValuationExtension K L (a : 𝒪[K]))
        (integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n a.2) := by
  ext
  simp [principalUnitsMapOfUnramifiedValuation, principalUnitOneAddOfMemPowSubgroup,
    principalUnitOneAddOfMemPow_val, integerRingMapOfValuationExtension]
 

def principalUnitsSuccQuotMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    PrincipalUnitsSuccQuot K n →* PrincipalUnitsSuccQuot L n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk L n).comp
      (principalUnitsMapOfUnramifiedValuation K L n))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      change ((principalUnitsMapOfUnramifiedValuation K L n u :
        principalUnits L n) : 𝒪[L]ˣ) ∈ principalUnits L (n + 1)
      simpa [principalUnitsMapOfUnramifiedValuation_apply]
        using integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
          K L (n + 1) (u := u.1) hu)
 

@[simp]
theorem principalUnitsSuccQuotMapOfUnramifiedValuation_mk (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits K n) :
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotMk K n u) =
      principalUnitsSuccQuotMk L n
        (principalUnitsMapOfUnramifiedValuation K L n u) :=
  rfl
 

theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x) := by
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x =>
      principalUnitsSuccQuotMapOfUnramifiedValuation K L n
          (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
          (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x))
    x ?_
  intro a
  rw [maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk,
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
  rw [principalUnitsSuccQuotOfIdealPow_apply, principalUnitsSuccQuotOfIdealPow_apply,
    principalUnitsSuccQuotMapOfUnramifiedValuation_mk]
  congr 1
  exact principalUnitsMapOfUnramifiedValuation_oneAdd K L n hn a
 

theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot K n) :
    MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn x) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x) := by
  change Additive.ofMul
      (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x)) =
    Additive.ofMul
      (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x))
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map]
 


theorem principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[K]) :
    MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        ((principalUnitsSuccQuotAddEquivResidueOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K)
          n hn).symm x) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L)
        n hn).symm (residueFieldMapOfValuationExtension K L x) := by
  change MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
      (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n x)) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L)
        n (residueFieldMapOfValuationExtension K L x))
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_map]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map]
 

theorem principalUnitsSuccQuotMapOfUnramifiedValuation_injective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Injective (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) := by
  intro x y hxy
  let eK :=
    principalUnitsSuccQuotAddEquivResidueOfIrreducible K
      (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n hn
  let eL :=
    principalUnitsSuccQuotAddEquivResidueOfIrreducible L
      (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
      (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n hn
  let xκ : 𝓀[K] := eK (Additive.ofMul x)
  let yκ : 𝓀[K] := eK (Additive.ofMul y)
  have hxmap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        eL.symm (residueFieldMapOfValuationExtension K L xκ) := by
    simpa [eK, eL, xκ] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn xκ
  have hymap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul y) =
        eL.symm (residueFieldMapOfValuationExtension K L yκ) := by
    simpa [eK, eL, yκ] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn yκ
  have hxyAdd :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul y) := by
    change Additive.ofMul
        (principalUnitsSuccQuotMapOfUnramifiedValuation K L n x) =
      Additive.ofMul (principalUnitsSuccQuotMapOfUnramifiedValuation K L n y)
    exact congrArg Additive.ofMul hxy
  have hres :
      residueFieldMapOfValuationExtension K L xκ =
        residueFieldMapOfValuationExtension K L yκ :=
    eL.symm.injective (hxmap.symm.trans (hxyAdd.trans hymap))
  have hκ : xκ = yκ :=
    (RingHom.injective (residueFieldMapOfValuationExtension K L)) hres
  have hadd : Additive.ofMul x = Additive.ofMul y :=
    eK.injective (by simpa [xκ, yκ] using hκ)
  exact Additive.ofMul.injective hadd
 



theorem principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {a : 𝒪[K]ˣ}
    (haL : integerUnitsMapOfValuationExtension K L a ∈ principalUnits L n) :
    a ∈ principalUnits K n := by
  let xK : 𝒪[K] := (a : 𝒪[K]) - 1
  let πK : 𝒪[K] := chosenIntegerRingUniformizer K
  have hxLpow : integerRingMapOfValuationExtension K L xK ∈ (𝓂[L] ^ n : Ideal 𝒪[L]) := by
    have haLpow :=
      (mem_principalUnits_iff L (integerUnitsMapOfValuationExtension K L a) n).1 haL
    simpa [xK, integerRingMapOfValuationExtension, sub_eq_add_neg] using haLpow
  have hπL : Irreducible (integerRingMapOfValuationExtension K L πK) := by
    simpa [πK] using integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  have hvalL :
      ValuativeRel.valuation L
          ((integerRingMapOfValuationExtension K L xK : 𝒪[L]) : L) ≤
        ValuativeRel.valuation L
          ((integerRingMapOfValuationExtension K L πK : 𝒪[L]) : L) ^ n := by
    have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
      (ValuativeRel.valuation L) hπL n
    exact (show integerRingMapOfValuationExtension K L xK ∈
        ({y : 𝒪[L] | ValuativeRel.valuation L (y : L) ≤
          ValuativeRel.valuation L
            ((integerRingMapOfValuationExtension K L πK : 𝒪[L]) : L) ^ n}) from by
      rw [← hset]
      exact hxLpow)
  have hvalL' :
      ValuativeRel.valuation L (algebraMap K L (xK : K)) ≤
        ValuativeRel.valuation L (algebraMap K L (((πK ^ n : 𝒪[K]) : K))) := by
    simpa [integerRingMapOfValuationExtension, map_pow] using hvalL
  have hvalKpow :
      ValuativeRel.valuation K (xK : K) ≤
        ValuativeRel.valuation K (((πK ^ n : 𝒪[K]) : K)) :=
    (Valuation.HasExtension.val_map_le_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
      (xK : K) (((πK ^ n : 𝒪[K]) : K))).1 hvalL'
  rw [mem_principalUnits_iff]
  change xK ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
  have hsetK := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (ValuativeRel.valuation K) (chosenIntegerRingUniformizer_irreducible K) n
  have hvalK : xK ∈
      ({y : 𝒪[K] | ValuativeRel.valuation K (y : K) ≤
        ValuativeRel.valuation K ((πK : 𝒪[K]) : K) ^ n}) := by
    simpa [πK, map_pow] using hvalKpow
  change xK ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
  rw [hsetK]
  exact hvalK
 

theorem galoisGroup_card_eq_finrank (K L : Type u)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Nat.card Gal(L / K) = Module.finrank K L :=
  IsGalois.card_aut_eq_finrank (F := K) (E := L)
 

theorem residueAlgEquiv_card_eq_finrank_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Module.finrank K L := by
  rw [residueAlgEquiv_card_eq_finrank K L,
    LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrank K L]
 

theorem residueAlgEquiv_card_eq_galoisGroup_card_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Nat.card Gal(L / K) := by
  rw [residueAlgEquiv_card_eq_finrank_of_unramifiedValuation K L,
    galoisGroup_card_eq_finrank K L]
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker = 1 :=
  galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_ramificationIdx_eq_one K L
    (LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one K L)
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Injective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  exact ((galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker).eq_bot_of_card_eq
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_unramifiedValuation
      K L)
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_surjective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) := by
  exact ((Nat.bijective_iff_injective_and_card
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)).2
      ⟨galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
          K L,
        (residueAlgEquiv_card_eq_galoisGroup_card_of_unramifiedValuation K L).symm⟩).2
 

theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Bijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) :=
  ⟨galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L,
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_surjective_of_unramifiedValuation K L⟩
 

noncomputable def galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation K L)
 

@[simp]
theorem galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (σ : Gal(L / K)) :
    galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L σ =
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ :=
  rfl
 


theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_prod_eq_prod_algEquiv_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (u : 𝓀[L]ˣ) :
    Finset.univ.prod (fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv u) =
    Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      Units.mapEquiv τ.toMulEquiv u) :=
  Fintype.prod_equiv
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).toEquiv
    (fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv u)
    (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => Units.mapEquiv τ.toMulEquiv u)
    (by intro σ; rfl)
 


theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_sum_eq_sum_algEquiv_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : 𝓀[L]) :
    Finset.univ.sum (fun σ : Gal(L / K) =>
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ x) =
    Finset.univ.sum (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => τ x) :=
  Fintype.sum_equiv
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).toEquiv
    (fun σ : Gal(L / K) => galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ x)
    (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => τ x)
    (by intro σ; rfl)
 

theorem galoisGroup_sum_residue_eq_algebraMap_trace_of_unramifiedValuation_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (a : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a) =
      algebraMap 𝓀[K] 𝓀[L]
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] a)) := by
  rw [galoisGroup_sum_residue_eq_residueAlgEquiv_sum_of_isIntegralClosure K L a]
  rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_sum_eq_sum_algEquiv_of_unramifiedValuation
    K L]
  exact (trace_eq_sum_automorphisms
    (K := 𝓀[K]) (L := 𝓀[L]) (IsLocalRing.residue 𝒪[L] a)).symm
 

theorem galoisGroup_sum_mul_base_uniformizer_pow_eq_coeff_sum_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    Finset.univ.sum (fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (r * πL ^ n)) =
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := by
  intro πL
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [map_mul, map_pow]
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r *
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))) ^ n =
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r * πL ^ n
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap]
 

theorem galoisSum_uniformizerGraded_eq_residueTrace
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    maximalIdealPowSuccQuotMulUniformizerPowMap L πL hπL n
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
  intro πL hπL
  rw [← residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue L πL hπL n
    (Finset.univ.sum fun σ : Gal(L / K) =>
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r)]
  rw [galoisGroup_sum_residue_eq_algebraMap_trace_of_unramifiedValuation_of_isIntegralClosure
    K L r]
end
end LocalFieldTheory
end

/- ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Basic -/
section
noncomputable section
universe u
namespace LocalClassFieldTheory
open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter
 

theorem normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    normIntegerUnits K L u ∈ principalUnits K n := by
  apply principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation K L n
  exact integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure K L n u hu
 

noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat) :
    principalUnits L n →* principalUnits K n where
  toFun u :=
    ⟨normIntegerUnits K L u.1,
      normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
        K L n u.1 u.2⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intro u v
    ext
    simp
 
@[simp]
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat)
    (u : principalUnits L n) :
    ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u :
        principalUnits K n) : 𝒪[K]ˣ) =
      normIntegerUnits K L u.1 :=
  rfl
 


theorem principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsMapOfUnramifiedValuation K L n
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u) =
      principalUnitsNormExtensionSideOfIsIntegralClosure K L n u := by
  ext
  rfl
namespace UnramifiedPrincipalUnits
 

theorem norm_oneAdd_sub_galoisSum_mem_next
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (((principalUnitsMapOfUnramifiedValuation K L n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)) :
        principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  rw [principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
    K L n (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)]
  exact
      principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ
      K L n hn a
end UnramifiedPrincipalUnits
 


noncomputable def principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat) :
    PrincipalUnitsSuccQuot L n →* PrincipalUnitsSuccQuot K n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk K n).comp
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      change ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u :
          principalUnits K n) : 𝒪[K]ˣ) ∈ principalUnits K (n + 1)
      simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply]
        using
          normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
            K L (n + 1) u.1 hu)
 
@[simp]
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat)
    (u : principalUnits L n) :
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
        (principalUnitsSuccQuotMk L n u) =
      principalUnitsSuccQuotMk K n
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u) :=
  rfl
 

theorem principalUnitsSuccQuotMap_normOfUnramifiedValuationOfIsIntegralClosure_oneAdd_base_eq_sum
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    let b : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      ⟨Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L]),
        by
          classical
          exact Ideal.sum_mem _ fun σ _ =>
            (integerRingEquiv_mem_maximalIdeal_pow L
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n
              (a : 𝒪[L])).2 a.2⟩
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))) =
      principalUnitsSuccQuotOfIdealPow L n hn b := by
  classical
  intro b
  rw [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk,
    principalUnitsSuccQuotMapOfUnramifiedValuation_mk]
  exact principalUnitsSuccQuotMk_eq_oneAdd_of_sub_one_sub_mem_succ L n hn
    (principalUnitsMapOfUnramifiedValuation K L n
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n
        (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))
    b
    (by
      simpa [b] using
    UnramifiedPrincipalUnits.norm_oneAdd_sub_galoisSum_mem_next
          K L n hn a)
end LocalClassFieldTheory
end

/- ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Trace -/
section
noncomputable section
universe u
namespace LocalClassFieldTheory
open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter
namespace UnramifiedPrincipalUnits
 


theorem quotientNorm_oneAdd_uniformizerPow_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let a : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      maximalIdealPowMulUniformizerPowMap L πL hπL n r
    Additive.ofMul
        (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
          (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
            (principalUnitsSuccQuotMk L n
              (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
  classical
  intro πL hπL a
  let b : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
    ⟨Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L]),
      by
        exact Ideal.sum_mem _ fun σ _ =>
          (integerRingEquiv_mem_maximalIdeal_pow L
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n
            (a : 𝒪[L])).2 a.2⟩
  have hnorm :=
    principalUnitsSuccQuotMap_normOfUnramifiedValuationOfIsIntegralClosure_oneAdd_base_eq_sum
      K L n hn a
  change Additive.ofMul
      (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))) =
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
      (algebraMap 𝓀[K] 𝓀[L]
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r)))
  rw [hnorm]
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply]
  change Additive.ofMul (principalUnitsSuccQuotOfIdealPow L n hn b) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))))
  rw [← principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk L n hn b]
  change principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (maximalIdealPowSuccQuotMk L n b) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))))
  congr 1
  have hb_eq :
      (b : 𝒪[L]) =
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := by
    simpa [b, a, πL] using
      galoisGroup_sum_mul_base_uniformizer_pow_eq_coeff_sum_of_isIntegralClosure K L n r
  rw [show maximalIdealPowSuccQuotMk L n b =
      maximalIdealPowSuccQuotMulUniformizerPowMap L πL hπL n
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) by
    rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
    apply congrArg (maximalIdealPowSuccQuotMk L n)
    apply Subtype.ext
    calc
      (b : 𝒪[L]) = (Finset.univ.sum fun σ : Gal(L / K) =>
            galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := hb_eq
      _ =
          ((maximalIdealPowMulUniformizerPowMap L πL hπL n
            (Finset.univ.sum fun σ : Gal(L / K) =>
              galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) :
            (𝓂[L] ^ n : Ideal 𝒪[L])) : 𝒪[L]) := by
        rw [maximalIdealPowMulUniformizerPowMap_apply]]
  exact
    galoisSum_uniformizerGraded_eq_residueTrace
      K L n r
end UnramifiedPrincipalUnits
 


theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_oneAdd_uniformizer_pow_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[L]) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let a : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      maximalIdealPowMulUniformizerPowMap L πL hπL n r
    Additive.ofMul
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
        (chosenIntegerRingUniformizer_irreducible K) n hn).symm
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r)) := by
  classical
  intro πK πL hπL a
  let x :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
      (principalUnitsSuccQuotMk L n
        (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))
  let y :=
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
      (chosenIntegerRingUniformizer_irreducible K) n hn).symm
      (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))
  have hxmap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
          (algebraMap 𝓀[K] 𝓀[L]
            (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
    simpa [x, πK, πL, hπL, a] using
    UnramifiedPrincipalUnits.quotientNorm_oneAdd_uniformizerPow_eq_trace
        K L n hn r
  have hymap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) y =
        (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
          (algebraMap 𝓀[K] 𝓀[L]
            (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
    simpa [y, πK, πL, hπL, residueFieldMapOfValuationExtension_eq_algebraMap] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))
  have hmul : x = Additive.toMul y := by
    apply principalUnitsSuccQuotMapOfUnramifiedValuation_injective K L n hn
    apply Additive.ofMul.injective
    change MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        (Additive.ofMul x) =
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) y
    exact hxmap.trans hymap.symm
  change Additive.ofMul x = y
  simpa using congrArg Additive.ofMul hmul
 

theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_trace_coord
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[L]) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let eK := principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
      (chosenIntegerRingUniformizer_irreducible K) n hn
    let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
    MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)
        (eL.symm x) =
      eK.symm (Algebra.trace 𝓀[K] 𝓀[L] x) := by
  classical
  intro πK πL hπL eK eL
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  have hrep :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_oneAdd_uniformizer_pow_eq_trace
      K L n hn r
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue]
  change Additive.ofMul _ = _
  simpa only [eK, eL, πK, πL, hπL, toMul_ofMul] using hrep
 

noncomputable def principalUnitsSuccQuotTraceOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Additive (PrincipalUnitsSuccQuot L n) →+ Additive (PrincipalUnitsSuccQuot K n) :=
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  ((principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
    (chosenIntegerRingUniformizer_irreducible K) n hn).symm.toAddMonoidHom).comp
    ((Algebra.trace 𝓀[K] 𝓀[L]).toAddMonoidHom.comp
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).toAddMonoidHom)
 

theorem principalUnitsSuccQuotTraceOfUnramifiedValuation_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn) := by
  classical
  intro y
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  let eK := principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
    (chosenIntegerRingUniformizer_irreducible K) n hn
  let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
  obtain ⟨x, hx⟩ :=
    residueField_trace_surjective_of_valuationExtension K L (eK y)
  refine ⟨eL.symm x, ?_⟩
  change
    (((eK.symm.toAddMonoidHom).comp
      ((Algebra.trace 𝓀[K] 𝓀[L]).toAddMonoidHom.comp eL.toAddMonoidHom))
      (eL.symm x)) = y
  simp [hx]
 


theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n) =
      principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn := by
  apply AddMonoidHom.ext
  intro x
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
  have hcoord :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_trace_coord
      K L n hn (eL x)
  simpa [principalUnitsSuccQuotTraceOfUnramifiedValuation, πK, πL, hπL, eL]
    using hcoord
 


theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_toAdditive_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective
      (MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)) := by
  rw [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_eq_trace
    K L n hn]
  exact principalUnitsSuccQuotTraceOfUnramifiedValuation_surjective K L n hn
 

theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective
      (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n) := by
  intro y
  obtain ⟨x, hx⟩ :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_toAdditive_surjective
      K L n hn (Additive.ofMul y)
  refine ⟨Additive.toMul x, ?_⟩
  apply Additive.ofMul.injective
  change MonoidHom.toAdditive
      (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)
      (Additive.ofMul (Additive.toMul x)) = Additive.ofMul y
  simpa using hx
end LocalClassFieldTheory
end

/- ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Lift -/
section
noncomputable section
universe u
namespace LocalClassFieldTheory
open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter
 
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n,
      principalUnitsSuccQuotMk K n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x) =
        principalUnitsSuccQuotMk K n y := by
  obtain ⟨q, hq⟩ :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_surjective
      K L n hn (principalUnitsSuccQuotMk K n y)
  obtain ⟨x, rfl⟩ := principalUnitsSuccQuotMk_surjective L n q
  refine ⟨x, ?_⟩
  simpa [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk]
    using hq
 


theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n,
      y / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x ∈
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  obtain ⟨x, hx⟩ :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ K L n hn y
  refine ⟨x, ?_⟩
  exact (principalUnitsSuccQuotMk_eq_iff_div_mem K n y
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x)).1 hx.symm
 

noncomputable def chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    principalUnits L (n + d) :=
  let r : principalUnits K (n + d) :=
    ⟨(y : 𝒪[K]ˣ) / normIntegerUnits K L (s.1 : 𝒪[L]ˣ), s.2⟩
  have hnd : 1 ≤ n + d := le_trans hn (Nat.le_add_right n d)
  Classical.choose
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
      K L (n + d) hnd r)
 

noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    {x : principalUnits L n //
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + (d + 1))} := by
  let r : principalUnits K (n + d) :=
    ⟨(y : 𝒪[K]ˣ) / normIntegerUnits K L (s.1 : 𝒪[L]ˣ), s.2⟩
  let z : principalUnits L (n + d) :=
    chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
      K L n hn y d s
  let x' : principalUnits L n :=
    ⟨(s.1 : 𝒪[L]ˣ) * (z : 𝒪[L]ˣ),
      (principalUnits L n).mul_mem s.1.2
        (principalUnits_antitone L (Nat.le_add_right n d) z.2)⟩
  have hz :
      (((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
          (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) ∈
        principalUnits K ((n + d) + 1)) :=
    by
      have hnd : 1 ≤ n + d := le_trans hn (Nat.le_add_right n d)
      dsimp [z, chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection]
      exact Classical.choose_spec
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
          K L (n + d) hnd r)
  refine ⟨x', ?_⟩
  have hresEq :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x' : 𝒪[L]ˣ) =
        ((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
            (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) := by
    change
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x' : 𝒪[L]ˣ) =
        (r : 𝒪[K]ˣ) /
          ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
              (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ)
    simp only [x', r, principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply,
      (normIntegerUnits K L).map_mul]
    exact div_mul_eq_div_div _ _ _
  rw [hresEq]
  simpa [Nat.add_assoc] using hz
 

theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep_div_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep
          K L n hn y d s).1 : 𝒪[L]ˣ) /
        (s.1 : 𝒪[L]ˣ)) ∈ principalUnits L (n + d) := by
  let z : principalUnits L (n + d) :=
    chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
      K L n hn y d s
  change (((s.1 : 𝒪[L]ˣ) * (z : 𝒪[L]ˣ)) / (s.1 : 𝒪[L]ˣ)) ∈
    principalUnits L (n + d)
  rw [mul_div_cancel_left]
  exact z.2
 

noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    (d : Nat) →
      {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}
  | 0 => by
      refine ⟨1, ?_⟩
      change (y : 𝒪[K]ˣ) / normIntegerUnits K L (1 : 𝒪[L]ˣ) ∈
        principalUnits K (n + 0)
      rw [(normIntegerUnits K L).map_one, div_one, Nat.add_zero]
      exact y.2
  | d + 1 =>
      principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep K L n hn y d
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d)
 

theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_succ_div_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ)) ∈
      principalUnits L (n + d) := by
  change
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep K L n hn y d
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d)).1 : 𝒪[L]ˣ) /
        ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : 𝒪[L]ˣ)) ∈ principalUnits L (n + d)
  exact principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep_div_mem
    K L n hn y d
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y d)
 

noncomputable def chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∀ d : Nat, principalUnits L (n + d) :=
  fun d =>
    ⟨(((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ),
      principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_succ_div_mem
        K L n hn y d⟩
 

theorem principalUnitsCorrectionProduct_approxCorrectionSeqOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    principalUnitsCorrectionProduct L n
        (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
          K L n hn y) d =
      (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) := by
  induction d with
  | zero =>
      simp [principalUnitsCorrectionProduct_zero,
        principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState]
  | succ d ih =>
      rw [principalUnitsCorrectionProduct_succ, ih]
      change
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) *
            ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
              (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
                K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ)) =
          (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ)
      rw [mul_comm, div_mul_cancel]
 


theorem exists_tendsto_principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n, Filter.Tendsto
      (fun d : Nat =>
        ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))
      Filter.atTop (nhds (((x : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L])) := by
  obtain ⟨x, hx⟩ :=
    exists_tendsto_principalUnitsCorrectionProduct_principalUnit L n hn
      (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
        K L n hn y)
  refine ⟨x, ?_⟩
  have hseq :
      (fun d : Nat =>
        ((principalUnitsCorrectionProduct L n
            (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
              K L n hn y) d : 𝒪[L]ˣ) : 𝒪[L])) =
        (fun d : Nat =>
          ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L])) := by
    funext d
    rw [principalUnitsCorrectionProduct_approxCorrectionSeqOfIsIntegralClosure
      K L n hn y d]
  simpa [hseq] using hx
 

theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_error_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    ((y : 𝒪[K]ˣ) /
        normIntegerUnits K L
          ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : 𝒪[L]ˣ)) ∈
      principalUnits K (n + d) :=
  (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    K L n hn y d).2
 


theorem eventually_normIntegerUnits_div_mem_principalUnits_of_tendsto_units_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    {f : Nat → 𝒪[L]ˣ} {x : 𝒪[L]ˣ} (n : Nat)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    ∀ᶠ d in atTop,
      normIntegerUnits K L (f d) / normIntegerUnits K L x ∈ principalUnits K n := by
  have hdiv := eventually_div_mem_principalUnits_of_tendsto_units L n hf
  filter_upwards [hdiv] with d hd
  have hnorm : normIntegerUnits K L (f d / x) ∈ principalUnits K n :=
    normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
      K L n (f d / x) hd
  simpa [(normIntegerUnits K L).map_div] using hnorm
 

theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_limit_error_mem_add_all
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n)
    (x : principalUnits L n)
    (hx : Tendsto
      (fun d : Nat =>
        ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))
      atTop (nhds (((x : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))) :
    ∀ d : Nat,
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d) := by
  intro d
  let f : Nat → 𝒪[L]ˣ := fun i =>
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y i).1 : principalUnits L n) : 𝒪[L]ˣ)
  have hnormEv : ∀ᶠ i in atTop,
      normIntegerUnits K L (f i) / normIntegerUnits K L (x : 𝒪[L]ˣ) ∈
        principalUnits K (n + d) := by
    exact
      eventually_normIntegerUnits_div_mem_principalUnits_of_tendsto_units_of_isIntegralClosure
        K L (n + d) hx
  have hge : ∀ᶠ i : Nat in atTop, d ≤ i := eventually_ge_atTop d
  rcases (hnormEv.and hge).exists with ⟨i, hboth⟩
  rcases hboth with ⟨hnorm, hdi⟩
  have herrDeep :
      ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) ∈
        principalUnits K (n + i) :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_error_mem
      K L n hn y i
  have herr :
      ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d) :=
    principalUnits_antitone K (Nat.add_le_add_left hdi n) herrDeep
  have heq :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ) =
        ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) *
        (normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ) /
          normIntegerUnits K L (x : 𝒪[L]ˣ)) := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [heq]
  exact (principalUnits K (n + d)).mul_mem herr (by simpa [f] using hnorm)
 


theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_eq_of_error_mem_add_all
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (y : principalUnits K n) (x : principalUnits L n)
    (h : ∀ d : Nat,
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d)) :
    (y : 𝒪[K]ˣ) = normIntegerUnits K L (x : 𝒪[L]ˣ) := by
  have hOne :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ) = 1 :=
    principalUnits_eq_one_of_mem_add_all K n
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) h
  exact div_eq_one.mp hOne
 


theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n) := by
  intro y
  obtain ⟨x, hx⟩ :=
    exists_tendsto_principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y
  refine ⟨x, ?_⟩
  have hmem :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_limit_error_mem_add_all
      K L n hn y x hx
  have hEq :
      (y : 𝒪[K]ˣ) = normIntegerUnits K L (x : 𝒪[L]ˣ) :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_eq_of_error_mem_add_all
      K L n y x hmem
  apply Subtype.ext
  simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply] using hEq.symm
end LocalClassFieldTheory
end

/- ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.ResidueNorm -/
section
noncomputable section
universe u
namespace LocalClassFieldTheory
open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
 


noncomputable def integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    IntegerUnitsModPrincipalUnits L →* IntegerUnitsModPrincipalUnits K :=
  integerUnitsModPrincipalUnitsLift
    ((integerUnitsModPrincipalUnitsMk K).comp (normIntegerUnits K L))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        IntegerUnitsModPrincipalUnits_mk_eq_one_iff]
      exact normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
        K L 1 u hu)
 
@[simp]
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (u : 𝒪[L]ˣ) :
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L
        (integerUnitsModPrincipalUnitsMk L u) =
      integerUnitsModPrincipalUnitsMk K (normIntegerUnits K L u) :=
  integerUnitsModPrincipalUnitsLift_mk
    ((integerUnitsModPrincipalUnitsMk K).comp (normIntegerUnits K L)) _ u
 

theorem residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (u : 𝒪[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K (normIntegerUnits K L u)) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsToResidueUnits L u)) := by
  rw [residueUnitsMap_integerUnitsToResidueUnits K L (normIntegerUnits K L u)]
  rw [integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  exact
    (galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits
      K L σ u).symm
 

theorem residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_algEquiv_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (u : 𝒪[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K (normIntegerUnits K L u)) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsToResidueUnits L u)) := by
  rw [residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure
    K L u]
 

theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_algEquiv_base_extend
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsModPrincipalUnitsEquivResidueUnits L x)) := by
  refine IntegerUnitsModPrincipalUnits.inductionOn
    (motive := fun x =>
      residueUnitsMapOfValuationExtension K L
          (integerUnitsModPrincipalUnitsEquivResidueUnits K
            (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
        Finset.univ.prod (fun σ : Gal(L / K) =>
          Units.mapEquiv
            (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
            (integerUnitsModPrincipalUnitsEquivResidueUnits L x)))
    x ?_
  intro u
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk]
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  exact
    residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_algEquiv_prod_of_isIntegralClosure
      K L u
 

theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_base_extend_eq_residueNorm
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
      residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x)) := by
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_algEquiv_base_extend]
  rw [integerUnitsModPrincipalUnitsResidueNorm_base_extend_eq_prod_algEquiv]
  exact
    galoisGroupResidueAlgEquivOfIsIntegralClosure_prod_eq_prod_algEquiv_of_unramifiedValuation
      K L (integerUnitsModPrincipalUnitsEquivResidueUnits L x)
 

theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_eq_residueNorm_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L =
      integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L := by
  apply MonoidHom.ext
  intro x
  apply (integerUnitsModPrincipalUnitsEquivResidueUnits K).injective
  apply residueUnitsMapOfValuationExtension_injective K L
  exact
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_base_extend_eq_residueNorm
      K L x
 

theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_surjective_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective
      (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L) := by
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_eq_residueNorm_of_unramifiedValuation
    K L]
  exact integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension K L
end LocalClassFieldTheory
end

/- ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Norm -/
section
noncomputable section
universe u
namespace LocalClassFieldTheory
open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
 


theorem normIntegerUnits_surjective_unramified_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective (normIntegerUnits K L) := by
  intro y
  obtain ⟨q, hq⟩ :=
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_surjective_of_unramifiedValuation
      K L (QuotientGroup.mk y : IntegerUnitsModPrincipalUnits K)
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q
  have hclass :
      (QuotientGroup.mk (normIntegerUnits K L u) : IntegerUnitsModPrincipalUnits K) =
        QuotientGroup.mk y := by
    change integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L
        (integerUnitsModPrincipalUnitsMk L u) =
      integerUnitsModPrincipalUnitsMk K y at hq
    rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk] at hq
    exact hq
  have hresInv : normIntegerUnits K L u / y ∈ principalUnits K 1 :=
    (IntegerUnitsModPrincipalUnits_mk_eq_mk_iff K (normIntegerUnits K L u) y).1 hclass
  have hres : y / normIntegerUnits K L u ∈ principalUnits K 1 := by
    have hinv : (normIntegerUnits K L u / y)⁻¹ ∈ principalUnits K 1 :=
      (principalUnits K 1).inv_mem hresInv
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hinv
  let r : principalUnits K 1 := ⟨y / normIntegerUnits K L u, hres⟩
  obtain ⟨z, hz⟩ :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
      K L 1 (Nat.le_refl 1) r
  refine ⟨u * (z : 𝒪[L]ˣ), ?_⟩
  have hzUnits : normIntegerUnits K L (z : 𝒪[L]ˣ) = y / normIntegerUnits K L u := by
    have hzUnitsSub := congrArg (fun w : principalUnits K 1 => (w : 𝒪[K]ˣ)) hz
    simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply, r]
      using hzUnitsSub
  calc
    normIntegerUnits K L (u * (z : 𝒪[L]ˣ))
        = normIntegerUnits K L u * normIntegerUnits K L (z : 𝒪[L]ˣ) := by
          rw [(normIntegerUnits K L).map_mul]
    _ = normIntegerUnits K L u * (y / normIntegerUnits K L u) := by
          rw [hzUnits]
    _ = y := by
          simp [div_eq_mul_inv, mul_left_comm]
end LocalClassFieldTheory
end
namespace TunnellCFTPublicLocal
open LocalFieldTheory LocalClassFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel
theorem result : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e u
  letI : IsUnramifiedValuedExtension K L := ⟨e⟩
  obtain ⟨y,hy⟩ := normIntegerUnits_surjective_unramified_of_isIntegralClosure K L u
  refine ⟨integerUnitsToFieldUnits L y, ?_⟩
  exact congrArg (fun a : 𝒪[K]ˣ => (a.val : K)) hy

end TunnellCFTPublicLocal

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := TunnellCFTPublicLocal.result
