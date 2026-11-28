import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1
import Mathlib
/-! Finite Szemerédi theorem by Gabriel Dahia, © 2026, Apache-2.0. Adapted for Erdős 142 by Thomas Fredrickson with Codex. Source revision fc13f6ed360bbe2300f844f34fc5d06eca9c216c.
https://github.com/gdahia/DensityHalesJewett/tree/fc13f6ed360bbe2300f844f34fc5d06eca9c216c
Modified by consolidating modules, adapting declarations to the registry pin, and translating to one-based intervals.

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
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

Modified and golfed by @pmcao (2026).
-/
open scoped NNReal
abbrev Α:=DecidableEq
abbrev Β:=Fintype
section
open Finset
open scoped BigOperators
namespace Δ
def fiber {α ι κ : Type*} [Β (κ → α)] [Α (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) (x : ι → α) : Finset (κ → α) :=
  Finset.univ.filter λ y ↦ Sum.elim x y ∈ A
@[simp]
lemma τ {α ι κ : Type*} [Β (κ → α)] [Α (ι ⊕ κ → α)]
    {A : Finset (ι ⊕ κ → α)} {x : ι → α} {y : κ → α} :
    y ∈ fiber A x ↔ Sum.elim x y ∈ A := by
  simp [fiber]
lemma σ {α ι κ : Type*} [Β (ι → α)] [Β (κ → α)]
    [Β (ι ⊕ κ → α)] [Α (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) :
    (𝔼 x : ι → α, ((fiber A x).dens : ℝ)) = (A.dens : ℝ) := by
  classical
  simp_rw [← Finset.expect_indicator_one]
  rw [← Finset.expect_product']
  apply Finset.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ α).symm
  · simp
  · intro x _
    rcases x with ⟨x, y⟩
    have hy : y ∈ fiber A x ↔ (Equiv.sumArrowEquivProdArrow ι κ α).symm (x, y) ∈ A :=
      τ
    by_cases h : (Equiv.sumArrowEquivProdArrow ι κ α).symm (x, y) ∈ A
    · rw [Set.indicator_of_mem (by simpa [hy] using h), Set.indicator_of_mem h]
      simp only [Pi.one_apply]
    · rw [Set.indicator_of_notMem (by simpa [hy] using h), Set.indicator_of_notMem h]
lemma ß {X : Type*} [Β X] [Nonempty X]
    (f : X → ℝ) (a b : ℝ) (hf₁ : ∀ x, f x ≤ 1)
    (hba : b < a) (havg : a ≤ 𝔼 x : X, f x) :
    (a - b) / (1 - b) ≤
      ((Finset.univ.filter λ x ↦ b ≤ f x).dens : ℝ) := by
  classical
  let H := Finset.univ.filter λ x ↦ b ≤ f x
  change (a - b) / (1 - b) ≤ (H.dens : ℝ)
  have h1b : 0 < 1 - b := by
    rw [sub_pos]
    exact hba.trans_le <| havg.trans <|
      Finset.expect_le Finset.univ_nonempty λ x _ ↦ hf₁ x
  rw [div_le_iff₀ h1b, sub_le_iff_le_add]
  apply havg.trans
  convert Finset.expect_le_expect (s := Finset.univ) (f := f)
    (g := λ x ↦ b + (1 - b) * Set.indicator (H : Set X) 1 x) ?_ using 1
  · symm
    rw [Finset.expect_add_distrib]
    simp only [Fintype.expect_const, ← Finset.mul_expect, Finset.expect_indicator_one]
    ring
  · intro x _
    by_cases hx : x ∈ H
    · rw [Set.indicator_of_mem (by simpa using hx)]
      simp only [Pi.one_apply]
      linarith [hf₁ x]
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      simp only [mul_zero, add_zero]
      exact le_of_lt <| lt_of_not_ge <| by simpa [H] using hx
end Δ
end
section
open Finset Function
open Combinatorics
namespace Δ
namespace Subspace
variable {η α ι : Type*}
lemma injective (V : Combinatorics.Subspace η α ι) :
    Function.Injective V := by
  intro x y ô
  funext e
  obtain ⟨i, hi⟩ := V.proper e
  simpa only [V.apply_inr hi] using congrFun ô i
def range [Β (η → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) : Finset (ι → α) :=
  Finset.univ.image V
@[simp]
lemma mem_range [Β (η → α)] [Α (ι → α)]
    {V : Combinatorics.Subspace η α ι} {w : ι → α} :
    w ∈ range V ↔ ∃ x, V x = w := by
  simp [range]
def Ι (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : Prop :=
  ∀ x, V x ∈ A
def compose (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η) :
    Combinatorics.Subspace θ α ι where
  idxFun i := (V.idxFun i).elim Sum.inl W.idxFun
  proper e := by
    obtain ⟨j, hj⟩ := W.proper e
    obtain ⟨i, hi⟩ := V.proper j
    refine ⟨i, ?_⟩
    simp only [hi, Sum.elim_inr, hj]
@[simp]
lemma Ψ (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η)
    (x : θ → α) : compose V W x = V (W x) := by
  funext i
  cases hi : V.idxFun i
  · simp [compose, Combinatorics.Subspace.coe_apply, hi]
  · simp [compose, Combinatorics.Subspace.coe_apply, hi]
def repeatInitial {m M : ℕ} (α : Type*) (hm : 1 ≤ m) (Ὴ : m ≤ M) :
    Combinatorics.Subspace (Fin m) α (Fin M) where
  idxFun i := Sum.inr <|
    if hi : i.val < m then ⟨i.val, hi⟩ else ⟨0, Nat.zero_lt_of_lt hm⟩
  proper e := by
    refine ⟨Fin.castLE Ὴ e, ?_⟩
    simp only [Fin.castLE, e.isLt, ↓reduceDIte]
@[simp]
lemma repeatInitial_map {β : Type*} {m M : ℕ} (α : Type*) (hm : 1 ≤ m) (Ὴ : m ≤ M)
    (f : β → α) (x : Fin m → β) :
    repeatInitial α hm Ὴ (f ∘ x) = f ∘ repeatInitial β hm Ὴ x := by
  funext i
  simp only [Function.comp_apply]
  rw [(repeatInitial α hm Ὴ).apply_inr rfl, (repeatInitial β hm Ὴ).apply_inr rfl]
  rfl
def concat (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α κ) :
    Combinatorics.Subspace (η ⊕ θ) α (ι ⊕ κ) where
  idxFun := Sum.elim
    (λ i ↦ (V.idxFun i).elim Sum.inl (λ e ↦ Sum.inr <| Sum.inl e))
    (λ i ↦ (W.idxFun i).elim Sum.inl (λ e ↦ Sum.inr <| Sum.inr e))
  proper e := by
    cases e with
    | inl e =>
      obtain ⟨i, hi⟩ := V.proper e
      refine ⟨Sum.inl i, ?_⟩
      simp only [hi, Sum.elim_inl, Sum.elim_inr]
    | inr e =>
      obtain ⟨i, hi⟩ := W.proper e
      refine ⟨Sum.inr i, ?_⟩
      simp only [hi, Sum.elim_inr]
@[simp]
lemma concat_apply (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α κ)
    (x : η → α) (y : θ → α) : concat V W (Sum.elim x y) =
      Sum.elim (V x) (W y) := by
  funext i
  cases i with
  | inl i =>
    cases hi : V.idxFun i <;>
      simp [concat, Combinatorics.Subspace.coe_apply, hi]
  | inr i =>
    cases hi : W.idxFun i <;>
      simp [concat, Combinatorics.Subspace.coe_apply, hi]
def Ô (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι :=
  l.toSubspaceUnit.reindex finOneEquiv.symm (Equiv.refl _) (Equiv.refl _)
@[simp]
lemma ÿ (l : Combinatorics.Line α ι) (x : Fin 1 → α) :
    Ô l x = l (x 0) := by
  funext i
  simp only [Ô, Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
    Equiv.refl_symm, Function.comp_apply, Combinatorics.Line.toSubspaceUnit_apply]
  exact congrArg (λ a ↦ l a i) (congrArg x (Fin.eq_zero _))
def Θ [Β (η → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℚ≥0 :=
  (Finset.univ.filter λ x ↦ V x ∈ A).dens
def ῒ [Β (η → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) :=
  {l : Combinatorics.Line α ι // ∀ a, l a ∈ range V}
def φ (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := V.proper e
    refine ⟨i, ?_⟩
    simp only [hi, Sum.elim_inr, he]
@[simp]
lemma composeLine_apply (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η)
    (a : α) : φ V l a = V (l a) := by
  funext i
  cases hi : V.idxFun i
  · simp [φ, Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply, hi]
  · simp [φ, Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply, hi]
def ᾫ [Β (η → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) : ῒ V :=
  ⟨φ V l, λ a ↦ mem_range.mpr ⟨l a, (composeLine_apply V l a).symm⟩⟩
noncomputable def Ί [Β (η → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : ῒ V) (a : α) : η → α :=
  Classical.choose <| mem_range.mp (q.2 a)
lemma å [Β (η → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : ῒ V) (a : α) :
    V (Ί V q a) = q.1 a :=
  Classical.choose_spec <| mem_range.mp (q.2 a)
noncomputable def ä (V : Combinatorics.Subspace η α ι) (e : η) : ι :=
  Classical.choose <| V.proper e
lemma ἦ (V : Combinatorics.Subspace η α ι) (e : η) :
    V.idxFun (ä V e) = Sum.inr e :=
  Classical.choose_spec <| V.proper e
noncomputable def ὤ [Β (η → α)] [Α (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : ῒ V) : Combinatorics.Line α η where
  idxFun e := q.1.idxFun (ä V e)
  proper := by
    obtain ⟨j, hj⟩ := q.1.proper
    cases hVj : V.idxFun j with
    | inl b =>
      obtain ⟨a, hab⟩ := exists_ne b
      exfalso
      apply hab
      rw [← q.1.apply_none a j hj, ← å V q a]
      exact V.apply_inl hVj
    | inr e =>
      cases hq : q.1.idxFun (ä V e) with
      | none => exact ⟨e, hq⟩
      | some c =>
        obtain ⟨a, hac⟩ := exists_ne c
        exfalso
        apply hac
        rw [← q.1.apply_none a j hj, ← q.1.apply_some hq]
        rw [← å V q a]
        rw [V.apply_inr (ἦ V e), V.apply_inr hVj]
lemma ὁ [Β (η → α)] [Α (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : ῒ V) (a : α) :
    V (ὤ V q a) = q.1 a := by
  funext i
  cases hi : V.idxFun i with
  | inl b =>
    rw [V.apply_inl hi]
    rw [← å V q a]
    rw [V.apply_inl hi]
  | inr e =>
    rw [V.apply_inr hi]
    change (q.1.idxFun (ä V e)).getD a = q.1 a i
    change q.1 a (ä V e) = q.1 a i
    rw [← å V q a]
    rw [V.apply_inr (ἦ V e), V.apply_inr hi]
noncomputable def linesEquiv [Β (η → α)] [Α (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) :
    Combinatorics.Line α η ≃ ῒ V := by
  refine
    { toFun := ᾫ V
      invFun := ὤ V
      left_inv := ?_
      right_inv := ?_ }
  · intro l
    apply Combinatorics.Line.coe_injective
    funext a
    apply injective V
    rw [ὁ]
    exact composeLine_apply V l a
  · intro q
    apply Subtype.ext
    change φ V (ὤ V q) = q.1
    apply Combinatorics.Line.coe_injective
    funext a
    rw [composeLine_apply]
    exact ὁ V q a
noncomputable def mapLine [Β (η → α)] [Α (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι :=
  (linesEquiv V l).1
lemma mapLine_eq_composeLine [Β (η → α)] [Α (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    mapLine V l = φ V l :=
  rfl
@[simp]
lemma mapLine_apply [Β (η → α)] [Α (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η)
    (a : α) : mapLine V l a = V (l a) := by
  exact composeLine_apply V l a
def Ï {β : Type*} [Β (η → β)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) (e : β ↪ α) : Finset (ι → α) :=
  Finset.univ.image λ x ↦ V (e ∘ x)
end Subspace
end Δ
end
section
open Finset
open Combinatorics
namespace Δ
def ὢ {α ι : Type*} (x y : ι → Option α) : Prop := ∀ i, x i = none ↔ y i = none
namespace Line
variable {α ι : Type*}
def fillOption (l : Combinatorics.Line α ι) (v : Option α) : ι → Option α :=
  λ i ↦ (l.idxFun i).elim v some
@[simp]
lemma fillOption_some (l : Combinatorics.Line α ι) (a : α) :
    fillOption l (some a) = some ∘ l a := by
  funext i
  cases h : l.idxFun i <;> simp [fillOption, Combinatorics.Line.coe_apply, h]
end Line
namespace Subspace
variable {α η θ ι : Type*}
def Ä (V : Combinatorics.Subspace η α ι) (x : η → Option α) : ι → Option α :=
  λ i ↦ Sum.elim some x (V.idxFun i)
lemma Ἰ (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η)
    (x : θ → Option α) : Ä (compose V W) x = Ä V (Ä W x) := by
  funext i
  cases h : V.idxFun i <;> simp [Ä, compose, h]
lemma ᾪ (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    (φ V l).idxFun = Ä V l.idxFun :=
  rfl
def ᾩ {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') : Combinatorics.Subspace (Fin (ℓ + 1)) α (B ⊕ B') where
  idxFun := Sum.elim (λ b ↦ (V.idxFun b).map id Fin.succ)
    λ i ↦ (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    induction e using Fin.cases with
    | zero =>
      obtain ⟨i, hi⟩ := l.proper
      exact ⟨Sum.inr i, by simp [hi]⟩
    | succ j =>
      obtain ⟨b, hb⟩ := V.proper j
      exact ⟨Sum.inl b, by simp [hb]⟩
lemma ὴ {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') (x : Fin (ℓ + 1) → Option α) :
    Ä (ᾩ V l) x
      = Sum.elim (Ä V λ i ↦ x i.succ) (Line.fillOption l (x 0)) := by
  funext i
  cases i with
  | inl b => cases h : V.idxFun b <;> simp [Ä, ᾩ, h]
  | inr i => cases h : l.idxFun i <;> simp [Ä, ᾩ, Line.fillOption, h]
noncomputable def ΐ (α : Type*) [Nonempty α] {N n : ℕ} (h : N ≤ n) :
    Combinatorics.Subspace (Fin N) α (Fin n) where
  idxFun i := if hi : i.val < N then Sum.inr ⟨i.val, hi⟩ else Sum.inl (Classical.arbitrary α)
  proper e := ⟨Fin.castLE h e, by simp [Fin.castLE, e.isLt]⟩
end Subspace
namespace ᾮ
variable {α : Type*}
open _root_.Δ.Subspace _root_.Combinatorics.Subspace
private lemma ᾔ (α : Type*) [Finite α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∀ (P S : Type) [Finite P] [Finite S], ∃ (B : Type) (_ : Finite B),
      ∀ χ : (P → Option α) → (B → Option α) → (S → Option α) → C,
        ∃ V : Combinatorics.Subspace (Fin ℓ) α B,
          ∀ (p : P → Option α) (s : S → Option α) (x y : Fin ℓ → Option α),
            ὢ x y → χ p (Ä V x) s = χ p (Ä V y) s := by
  induction ℓ with
  | zero =>
    intro P S _ _
    refine ⟨PEmpty, inferInstance, ?_⟩
    intro χ
    refine ⟨⟨PEmpty.elim, ?_⟩, ?_⟩
    · intro e
      exact e.elim0
    · intro p s _ _ _
      exact congrArg (λ w ↦ χ p w s) (funext λ i ↦ i.elim)
  | succ ℓ ih =>
    intro P S _ _
    obtain ⟨B, _, hB⟩ := ih P (Unit ⊕ S)
    obtain ⟨B', _, hB'⟩ := Combinatorics.Line.exists_mono_in_high_dimension α
      ((P → Option α) → (B → Option α) → (S → Option α) → C)
    refine ⟨B ⊕ B', inferInstance, ?_⟩
    intro χ
    obtain ⟨l, prof, hprof⟩ := hB' λ u p b s ↦ χ p (Sum.elim b (some ∘ u)) s
    have hprof' : ∀ (a : α) (p : P → Option α) (b : B → Option α) (s : S → Option α),
        χ p (Sum.elim b (some ∘ l a)) s = prof p b s :=
      λ a p b s ↦ congrFun (congrFun (congrFun (hprof a) p) b) s
    obtain ⟨V, hV⟩ := hB λ p b q ↦
      χ p (Sum.elim b (Line.fillOption l (q (Sum.inl ())))) λ s ↦ q (Sum.inr s)
    refine ⟨ᾩ V l, ?_⟩
    intro p s x y ô
    rw [ὴ, ὴ]
    apply Eq.trans (hV p (Sum.elim (λ _ ↦ x 0) s) (λ i ↦ x i.succ) (λ i ↦ y i.succ)
      λ i ↦ ô i.succ)
    simp only [Sum.elim_inl, Sum.elim_inr]
    cases hx : x 0 with
    | none => rw [(ô 0).1 hx]
    | some a =>
      cases hy : y 0 with
      | none => simp [(ô 0).2 hy] at hx
      | some b =>
        rw [Line.fillOption_some, Line.fillOption_some, hprof' a, hprof' b]
lemma ᾼ (α : Type*) [Finite α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∃ N : ℕ, ∀ χ : (Fin N → Option α) → C,
      ∃ V : Combinatorics.Subspace (Fin ℓ) α (Fin N),
        ∀ x y : Fin ℓ → Option α, ὢ x y → χ (Ä V x) = χ (Ä V y) := by
  obtain ⟨B, _, hB⟩ := ᾔ α C ℓ PEmpty PEmpty
  have := Fintype.ofFinite B
  refine ⟨Fintype.card B, ?_⟩
  intro χ
  obtain ⟨V, hV⟩ := hB λ _ w _ ↦ χ (w ∘ (Fintype.equivFin B).symm)
  have hw : ∀ z : Fin ℓ → Option α,
      Ä (V.reindex (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin B)) z
        = Ä V z ∘ (Fintype.equivFin B).symm := by
    intro z
    funext i
    cases h : V.idxFun ((Fintype.equivFin B).symm i) <;>
      simp [Ä, Combinatorics.Subspace.reindex, h]
  refine ⟨V.reindex (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin B), ?_⟩
  intro x y ô
  rw [hw x, hw y]
  exact hV PEmpty.elim PEmpty.elim x y ô
lemma exists_canonical_of_le (α : Type*) [Finite α] [Nonempty α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ χ : (Fin n → Option α) → C,
      ∃ V : Combinatorics.Subspace (Fin ℓ) α (Fin n),
        ∀ x y : Fin ℓ → Option α, ὢ x y → χ (Ä V x) = χ (Ä V y) := by
  obtain ⟨N, hN⟩ := ᾼ α C ℓ
  refine ⟨N, ?_⟩
  intro n hn χ
  obtain ⟨V, hV⟩ := hN λ w ↦ χ (Ä (ΐ α hn) w)
  refine ⟨compose (ΐ α hn) V, ?_⟩
  intro x y ô
  rw [Ἰ, Ἰ]
  exact hV x y ô
end ᾮ
end Δ
end
section
open Finset
open Combinatorics
namespace Δ
namespace ᾭ
lemma ᾋ (C : Type*) [Finite C] (n : ℕ) :
    ∃ M : ℕ, ∀ d : Finset (Fin M) → C,
      ∃ (E : Finset (Fin M)) (G : Fin n → Finset (Fin M)),
        E.Nonempty ∧ (∀ i, (G i).Nonempty) ∧ (∀ i, Disjoint E (G i)) ∧
          (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧
          ∃ c, ∀ I : Finset (Fin n), d (E ∪ I.biUnion G) = c := by
  classical
  obtain ⟨M, hM⟩ := Combinatorics.Subspace.exists_mono_in_high_dimension_fin Bool C (Fin (n + 1))
  refine ⟨M, ?_⟩
  intro d
  obtain ⟨W, c, hc⟩ := hM λ x ↦ d {i | x i}
  set S : Finset (Fin M) := {i | W.idxFun i = Sum.inl true} with hS
  set X : Fin (n + 1) → Finset (Fin M) := λ j ↦ {i | W.idxFun i = Sum.inr j} with hX
  have hXne : ∀ j, (X j).Nonempty := by
    intro j
    obtain ⟨i, hi⟩ := W.proper j
    exact ⟨i, by simp [hX, hi]⟩
  have hXX : ∀ j j', j ≠ j' → Disjoint (X j) (X j') := by
    intro j j' hjj'
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact hjj' (Sum.inr_injective (hi.symm.trans hi'))
  have hSX : ∀ j, Disjoint S (X j) := by
    intro j
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hS, hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact absurd (hi.symm.trans hi') (by simp)
  have key : ∀ J : Finset (Fin (n + 1)), d (S ∪ J.biUnion X) = c := by
    intro J
    rw [← hc λ j ↦ decide (j ∈ J)]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_biUnion]
    simp only [hS, hX]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Combinatorics.Subspace.coe_apply]
    cases h : W.idxFun i with
    | inl b => cases b <;> simp
    | inr j => simp
  refine ⟨S ∪ X 0, λ i ↦ X i.succ, (hXne 0).mono Finset.subset_union_right,
    λ i ↦ hXne _, ?_, λ i j Ἂ ↦ hXX _ _ λ h ↦ Ἂ (Fin.succ_injective _ h),
    c, ?_⟩
  · intro i
    exact Finset.disjoint_union_left.2 ⟨hSX _, hXX _ _ (Fin.succ_ne_zero i).symm⟩
  · intro I
    convert key (insert 0 (I.image Fin.succ)) using 2
    ext i
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image, or_assoc]
    constructor
    · rintro (hi | hi | ⟨j, hj, Ἂ⟩)
      · exact Or.inl hi
      · exact Or.inr ⟨0, Or.inl rfl, hi⟩
      · exact Or.inr ⟨j.succ, Or.inr ⟨j, hj, rfl⟩, Ἂ⟩
    · rintro (hi | ⟨j, rfl | ⟨j', hj', rfl⟩, Ἂ⟩)
      · exact Or.inl hi
      · exact Or.inr (Or.inl Ἂ)
      · exact Or.inr (Or.inr ⟨j', hj', Ἂ⟩)
lemma ᾡ (C : Type*) [Finite C] (t : ℕ) :
    ∃ D : ℕ, ∀ d : Finset (Fin D) → C, ∃ E : Fin t → Finset (Fin D),
      (∀ i, (E i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        ∃ f : Fin t → C, ∀ (J : Finset (Fin t)) (hJ : J.Nonempty),
          d (J.biUnion E) = f (J.min' hJ) := by
  classical
  induction t with
  | zero =>
    refine ⟨0, ?_⟩
    intro d
    refine ⟨Fin.elim0, λ i ↦ i.elim0, λ i ↦ i.elim0, Fin.elim0, ?_⟩
    intro J hJ
    simp [Finset.eq_empty_of_isEmpty J] at hJ
  | succ t ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨M, hM⟩ := ᾋ C D
    refine ⟨M, ?_⟩
    intro d
    obtain ⟨E₀, G, hE₀, hG, hE₀G, hGG, c, hc⟩ := hM d
    obtain ⟨I, hI, hII, f, hf⟩ := hD λ K ↦ d (K.biUnion G)
    refine ⟨Fin.cons E₀ λ j ↦ (I j).biUnion G, ?_, ?_, Fin.cons c f, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hE₀
      | succ j => simpa using (hI j).biUnion λ g _ ↦ hG g
    · intro i j Ἂ
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl Ἂ
        | succ j =>
          simpa using (Finset.disjoint_biUnion_right _ _ _).2 λ g _ ↦ hE₀G g
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simpa using
            (Finset.disjoint_biUnion_left _ _ _).2 λ g _ ↦ (hE₀G g).symm
        | succ j =>
          simp only [Fin.cons_succ]
          apply (Finset.disjoint_biUnion_left _ _ _).2
          intro g hg
          apply (Finset.disjoint_biUnion_right _ _ _).2
          intro g' hg'
          apply hGG g g'
          intro hgg'
          exact (hII i j λ h ↦ Ἂ (congrArg Fin.succ h)).notMem_of_mem_left_finset hg
            (hgg' ▸ hg')
    · intro J hJ
      set K : Finset (Fin t) := {j | j.succ ∈ J} with hK
      have himage : J.erase 0 = K.image Fin.succ := by
        ext i
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp [hK, Fin.succ_ne_zero]
      have Ὸ : (J.erase 0).biUnion (Fin.cons E₀ λ j ↦ (I j).biUnion G)
          = (K.biUnion I).biUnion G := by
        rw [himage, Finset.image_biUnion, Finset.biUnion_biUnion]
        simp
      by_cases h0 : (0 : Fin (t + 1)) ∈ J
      · have hmin : J.min' hJ = 0 := le_antisymm (Finset.min'_le _ _ h0) (Fin.zero_le _)
        rw [hmin]
        simp only [Fin.cons_zero]
        rw [← Finset.insert_erase h0, Finset.biUnion_insert]
        simp only [Fin.cons_zero]
        rw [Ὸ]
        exact hc _
      · have hKne : K.Nonempty := by
          obtain ⟨i, hi⟩ := hJ
          induction i using Fin.cases with
          | zero => exact absurd hi h0
          | succ j => exact ⟨j, by simpa [hK] using hi⟩
        have hJK : J = K.image Fin.succ := by rw [← himage, Finset.erase_eq_of_notMem h0]
        have hmin : J.min' hJ = (K.min' hKne).succ := by
          apply le_antisymm
          · apply Finset.min'_le
            rw [hJK]
            exact Finset.mem_image_of_mem _ (K.min'_mem _)
          · apply Finset.le_min'
            intro y hy
            rw [hJK, Finset.mem_image] at hy
            obtain ⟨j, hj, rfl⟩ := hy
            exact Fin.succ_le_succ_iff.2 (Finset.min'_le _ _ hj)
        rw [hmin]
        simp only [Fin.cons_succ]
        rw [← Finset.erase_eq_of_notMem h0, Ὸ]
        exact hf K hKne
lemma exists_monochromaticUnions (C : Type*) [Finite C] (m : ℕ) :
    ∃ D : ℕ, ∀ d : Finset (Fin D) → C, ∃ E : Fin m → Finset (Fin D),
      (∀ i, (E i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        ∃ c, ∀ J : Finset (Fin m), J.Nonempty → d (J.biUnion E) = c := by
  classical
  let _ := Fintype.ofFinite C
  obtain ⟨D, hD⟩ := ᾡ C ((m - 1) * Fintype.card C + 1)
  refine ⟨D, ?_⟩
  intro d
  obtain ⟨E, hE, Ῠ, f, hf⟩ := hD d
  obtain ⟨c, -, þ⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := Finset.univ)
      (t := (Finset.univ : Finset C)) (f := f) (n := m - 1) (λ a _ ↦ Finset.mem_univ _) (by
        simp only [Finset.card_univ, Fintype.card_fin]
        rw [Nat.mul_comm]
        omega)
  obtain ⟨T, hTsub, Ὶ⟩ :=
    Finset.exists_subset_card_eq (s := {i | f i = c}) (n := m) (by omega)
  refine ⟨λ j ↦ E (T.orderEmbOfFin Ὶ j), λ j ↦ hE _,
    λ i j Ἂ ↦ Ῠ _ _ λ h ↦ Ἂ ((T.orderEmbOfFin Ὶ).injective h), c, ?_⟩
  intro J hJ
  rw [← Finset.image_biUnion, hf _ (hJ.image _)]
  obtain ⟨j, -, hj⟩ :=
    Finset.mem_image.1 (Finset.min'_mem _ (hJ.image (T.orderEmbOfFin Ὶ)))
  rw [← hj]
  simpa using hTsub (T.orderEmbOfFin_mem Ὶ j)
end ᾭ
end Δ
end
section
open Finset
open Combinatorics
namespace Δ
namespace Ñ
open _root_.Δ.Subspace _root_.Combinatorics.Subspace
variable {α ι C : Type*} [Α ι] {m n : ℕ}
noncomputable def ὣ (a₀ : α) (E : Fin m → Finset ι) (hE : ∀ j, (E j).Nonempty)
    (Ῠ : ∀ i j, i ≠ j → Disjoint (E i) (E j)) : Combinatorics.Subspace (Fin m) α ι where
  idxFun i := if h : ∃ j, i ∈ E j then Sum.inr h.choose else Sum.inl a₀
  proper e := by
    obtain ⟨i, hi⟩ := hE e
    refine ⟨i, ?_⟩
    rw [dif_pos ⟨e, hi⟩]
    apply congrArg Sum.inr
    by_contra hne
    exact Finset.disjoint_left.1 (Ῠ _ _ hne) (Exists.choose_spec (⟨e, hi⟩ : ∃ j, i ∈ E j)) hi
variable {a₀ : α} {E : Fin m → Finset ι} {hE : ∀ j, (E j).Nonempty}
  {Ῠ : ∀ i j, i ≠ j → Disjoint (E i) (E j)}
lemma ᾁ {i : ι} {j : Fin m} (Ἂ : i ∈ E j) :
    (ὣ a₀ E hE Ῠ).idxFun i = Sum.inr j := by
  simp only [ὣ]
  rw [dif_pos ⟨j, Ἂ⟩]
  apply congrArg Sum.inr
  by_contra hne
  exact Finset.disjoint_left.1 (Ῠ _ _ hne) (Exists.choose_spec (⟨j, Ἂ⟩ : ∃ j, i ∈ E j)) Ἂ
lemma ὥ {i : ι} (hi : ∀ j, i ∉ E j) :
    (ὣ a₀ E hE Ῠ).idxFun i = Sum.inl a₀ := by
  simp only [ὣ]
  rw [dif_neg (by simpa using hi)]
lemma ὂ (x : Fin m → Option α) (J : Finset (Fin m))
    (hJ : ∀ j, j ∈ J ↔ x j = none) :
    ὢ (Ä (ὣ a₀ E hE Ῠ) x)
      λ i ↦ if i ∈ J.biUnion E then none else some a₀ := by
  have hite : ∀ i : ι, ((if i ∈ J.biUnion E then none else some a₀ : Option α) = none)
      ↔ i ∈ J.biUnion E := by
    intro i
    split <;> simp [*]
  intro i
  rw [Ä]
  by_cases h : ∃ j, i ∈ E j
  · obtain ⟨j, hj⟩ := h
    rw [ᾁ hj, Sum.elim_inr, ← hJ j, hite i, Finset.mem_biUnion]
    constructor
    · intro hjJ
      exact ⟨j, hjJ, hj⟩
    · rintro ⟨j', hj'J, hij'⟩
      by_contra hne
      refine Finset.disjoint_left.1 (Ῠ j j' ?_) hj hij'
      intro hjj'
      apply hne
      rw [hjj']
      exact hj'J
  · rw [not_exists] at h
    rw [ὥ h, Sum.elim_inl, hite i]
    simp only [reduceCtorEq, false_iff]
    intro hi
    obtain ⟨j, -, Ἂ⟩ := Finset.mem_biUnion.1 hi
    exact h j Ἂ
private noncomputable def extend [Nonempty C] (χ : Combinatorics.Line α (Fin n) → C)
    (w : Fin n → Option α) : C :=
  if h : ∃ i, w i = none then χ ⟨w, h⟩ else Classical.arbitrary C
private lemma Ῡ [Nonempty C] (χ : Combinatorics.Line α (Fin n) → C)
    (l : Combinatorics.Line α (Fin n)) : extend χ l.idxFun = χ l :=
  dif_pos l.proper
lemma ῳ (α : Type*) [Finite α] [Nonempty α] (C : Type*) [Finite C] [Nonempty C]
    (m : ℕ) : ∃ N : ℕ, ∀ n, N ≤ n → ∀ χ : Combinatorics.Line α (Fin n) → C,
      ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
        ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (φ V l) = c := by
  classical
  obtain ⟨L, hL⟩ := ᾭ.exists_monochromaticUnions C m
  obtain ⟨N, hN⟩ := ᾮ.exists_canonical_of_le α C L
  refine ⟨N, ?_⟩
  intro n hn χ
  obtain ⟨V, hV⟩ := hN n hn (extend χ)
  obtain ⟨E, hE, Ῠ, c, hc⟩ := hL λ I ↦
    extend χ (Ä V λ i ↦ if i ∈ I then none else some (Classical.arbitrary α))
  refine ⟨compose V (ὣ (Classical.arbitrary α) E hE Ῠ), c, ?_⟩
  intro l
  rw [← Ῡ χ, ᾪ, Ἰ,
    hV _ _ (ὂ l.idxFun {j | l.idxFun j = none} λ j ↦ by simp)]
  apply hc
  obtain ⟨j, hj⟩ := l.proper
  exact ⟨j, by simpa using hj⟩
def ῂ (k r m N : ℕ) : Prop :=
  ∀ χ : Combinatorics.Line (Fin k) (Fin N) → Fin r,
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin N),
      ∃ c, ∀ l : Combinatorics.Line (Fin k) (Fin m), χ (φ V l) = c
noncomputable def bound (alphabet colors dimension : ℕ) : ℕ :=
  sInf {N | ∀ n, N ≤ n → ῂ alphabet colors dimension n}
private lemma ὶ {k r m : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r) (n : ℕ)
    (hn : bound k r m ≤ n) : ῂ k r m n := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact Nat.sInf_mem (ῳ (Fin k) (Fin r) m) n hn
private lemma ᾥ {β : Type*} (e : α ≃ β)
    (V : Combinatorics.Subspace (Fin m) β (Fin n)) (l : Combinatorics.Line α (Fin m)) :
    φ (V.reindex (Equiv.refl _) e.symm (Equiv.refl _)) l
      = Combinatorics.Line.map e.symm (φ V (l.map e)) := by
  apply Combinatorics.Line.ext
  funext i
  cases h : V.idxFun i with
  | inl b => simp [φ, Combinatorics.Subspace.reindex, Combinatorics.Line.map, h]
  | inr j => simp [φ, Combinatorics.Subspace.reindex, Combinatorics.Line.map, h]
lemma lines (α C : Type*) [Β α] [Nontrivial α] [Β C] [Nonempty C]
    [Α α] (m n : ℕ)
    (hn : bound (Fintype.card α) (Fintype.card C) m ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (Subspace.mapLine V l) = c := by
  obtain ⟨V, c, hc⟩ :=
    ὶ (k := Fintype.card α) (r := Fintype.card C) (m := m)
      (le_trans one_le_two Fintype.one_lt_card) Fintype.card_pos n hn
      λ l ↦ Fintype.equivFin C (χ (l.map (Fintype.equivFin α).symm))
  refine ⟨V.reindex (Equiv.refl _) (Fintype.equivFin α).symm (Equiv.refl _),
    (Fintype.equivFin C).symm c, ?_⟩
  intro l
  rw [Subspace.mapLine_eq_composeLine, ᾥ, ← hc (l.map (Fintype.equivFin α)),
    Equiv.symm_apply_apply]
lemma lines_twoColor (α : Type*) [Β α] [Nontrivial α] [Α α]
    (m n : ℕ)
    (hn : bound (Fintype.card α) 2 m ≤ n)
    (L : Finset (Combinatorics.Line α (Fin n))) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∈ L) ∨
        (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∉ L) := by
  classical
  obtain ⟨V, c, hc⟩ :=
    lines α (Fin 2) m n hn λ l ↦ if l ∈ L then 0 else 1
  obtain rfl | ⟨c, rfl⟩ := c.eq_zero_or_eq_succ
  · refine ⟨V, Or.inl ?_⟩
    intro l
    by_contra h
    simpa [h] using hc l
  · refine ⟨V, Or.inr ?_⟩
    rw [Fin.eq_zero c] at hc
    intro l h
    simpa [h] using hc l
end Ñ
end Δ
end
section
open Finset
open Combinatorics
open scoped BigOperators
namespace Δ
def Ζ (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ #A → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A
namespace Subspace
noncomputable def ο (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ Ζ k then
    Nat.find (h.2 δ h.1)
  else 0
lemma densityOneBound_spec {k : ℕ} (Μ : Ζ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : ο k δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A := by
  classical
  rw [ο, dif_pos ⟨hδ, Μ⟩] at hn
  exact Nat.find_spec (Μ δ hδ) n hn A hA
lemma ᾌ {k : ℕ} (Μ : Ζ k)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : ο k δ ≤ n)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin 1) (Fin k) (Fin n), Ι V A := by
  obtain ⟨l, hl⟩ := densityOneBound_spec Μ δ hδ n hn A hA
  refine ⟨Ô l, ?_⟩
  intro x
  rw [ÿ]
  exact hl _
private noncomputable def ῗ (α ι : Type*) :
    Combinatorics.Line α ι ≃
      {f : ι → Option α // ¬ ∀ i, f i ≠ none} := by
  classical
  refine {
    toFun := λ l ↦ ⟨l.idxFun, by
      intro h
      obtain ⟨i, hi⟩ := l.proper
      exact h i hi⟩
    invFun := λ f ↦ {
      idxFun := f
      proper := by
        have hf := f.property
        push Not at hf
        exact hf
    }
    left_inv := ?_
    right_inv := ?_
  }
  · intro l
    cases l
    rfl
  · intro f
    apply Subtype.ext
    rfl
private noncomputable def ᾠ (α ι : Type*) [Nonempty α] :
    {f : ι → Option α // ∀ i, f i ≠ none} ≃ (ι → α) := by
  classical
  let a : α := Classical.choice inferInstance
  refine {
    toFun := λ f i ↦ (f.1 i).getD a
    invFun := λ x ↦ ⟨some ∘ x, by
      intro i
      change some (x i) ≠ none
      exact Option.some_ne_none (x i)⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro f
    apply Subtype.ext
    funext i
    cases hi : f.1 i with
    | none => exact (f.2 i hi).elim
    | some b =>
        simp only [Function.comp_apply]
        rw [hi]
        rfl
  · intro x
    funext i
    simp only [Function.comp_apply, Option.getD_some]
lemma card_line (k m : ℕ) (hk : 0 < k)
    [Β (Combinatorics.Line (Fin k) (Fin m))] :
    Fintype.card (Combinatorics.Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [Fintype.card_congr (ῗ (Fin k) (Fin m)),
    Fintype.card_subtype_compl (λ f : Fin m → Option (Fin k) ↦ ∀ i, f i ≠ none),
    Fintype.card_pi_const, Fintype.card_option, Fintype.card_fin,
    Fintype.card_congr (ᾠ (Fin k) (Fin m)),
    Fintype.card_pi_const, Fintype.card_fin]
noncomputable abbrev lineFintype (k m : ℕ) : Β (Combinatorics.Line (Fin k) (Fin m)) :=
  Fintype.ofInjective (λ l ↦ l.idxFun) λ l₁ l₂ h ↦ by
    cases l₁
    cases l₂
    cases h
    rfl
def ò {m n : ℕ} (hm : 1 ≤ m) (ἁ : m ≤ n) :
    Combinatorics.Subspace (Fin m) (Fin 0) (Fin n) where
  idxFun i := Sum.inr ⟨i.val % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm)⟩
  proper e := by
    refine ⟨Fin.castLE ἁ e, ?_⟩
    simp only [Sum.inr.injEq]
    apply Fin.ext
    exact Nat.mod_eq_of_lt e.isLt
lemma Ἓ {m n : ℕ} (hm : 1 ≤ m) (ἁ : m ≤ n)
    (A : Finset (Fin n → Fin 0)) : Ι (ò hm ἁ) A := by
  intro x
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)
lemma density_le_of_card_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    δ ≤ (A.dens : ℝ) := by
  rw [Finset.nnratCast_dens]
  refine (le_div_iff₀ ?_).mpr ?_
  · simp only [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  · simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using hA
lemma card_le_of_density_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ * (k : ℝ) ^ n ≤ #A := by
  rw [Finset.nnratCast_dens] at hA
  have hpos : 0 < (Fintype.card (Fin n → Fin k) : ℝ) := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  have þ := (le_div_iff₀ hpos).mp hA
  simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using þ
lemma exists_fiber_density {X Y : Type*} [Β X] [Β Y] [Nonempty Y] [Α Y]
    (s : Finset X) (f : X → Y) :
    ∃ y, (s.filter λ x ↦ f x = y).dens ≥ (s.dens : ℝ) / Fintype.card Y := by
  classical
  let b : ℝ := #s / Fintype.card Y
  have hb : (#(Finset.univ : Finset Y) : ℕ) • b ≤ ∑ _x ∈ s, (1 : ℝ) := by
    simp only [Finset.card_univ, nsmul_eq_mul, b]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, mul_div_cancel₀]
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨y, _, hy⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (s := s) (t := Finset.univ)
      (f := f) (w := λ _ ↦ (1 : ℝ)) (λ _ _ ↦ Finset.mem_univ _)
      Finset.univ_nonempty hb
  refine ⟨y, ?_⟩
  rw [Finset.nnratCast_dens, Finset.nnratCast_dens]
  change (#s : ℝ) / Fintype.card Y ≤ ∑ x ∈ s with f x = y, (1 : ℝ) at hy
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hy
  rw [ge_iff_le]
  simpa only [div_div, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_one] using
    div_le_div_of_nonneg_right hy (by positivity : 0 ≤ (Fintype.card X : ℝ))
lemma ᾊ {k p q : ℕ} (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ / 2 ≤
      ((Finset.univ.filter λ x : Fin p → Fin k ↦ δ / 2 ≤ ((fiber A x).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let : Nonempty (Fin p → Fin k) := Pi.instNonempty
  have hδ₁ : δ ≤ 1 := hA.trans (by exact_mod_cast Finset.dens_le_one (s := A))
  have ᾚ := ß (λ x : Fin p → Fin k ↦ ((fiber A x).dens : ℝ))
    δ (δ / 2)
    (λ x ↦ by exact_mod_cast Finset.dens_le_one (s := fiber A x))
    (by linarith) (by simpa only [σ] using hA)
  refine le_trans ?_ ᾚ
  refine (le_div_iff₀ ?_).mpr ?_
  · linarith
  · nlinarith
lemma Ὀ {k p q : ℕ} (hk : 0 < k) (Μ : Ζ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : ο k δ ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (x : Fin p → Fin k)
    (hx : δ ≤ ((fiber A x).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin q), ∀ a, Sum.elim x (l a) ∈ A := by
  obtain ⟨l, hl⟩ :=
    densityOneBound_spec Μ δ hδ q hq (fiber A x)
      (card_le_of_density_le hk δ (fiber A x) hx)
  refine ⟨l, ?_⟩
  intro a
  exact τ.mp (hl a)
lemma ά {k p q : ℕ} (hk : 0 < k) (Μ : Ζ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : ο k (δ / 2) ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    letI := lineFintype k q
    ∃ l : Combinatorics.Line (Fin k) (Fin q),
      δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q))) ≤
        ((Finset.univ.filter λ x : Fin p → Fin k ↦
          ∀ a, Sum.elim x (l a) ∈ A).dens : ℝ) := by
  classical
  let := lineFintype k q
  let B := Finset.univ.filter λ x : Fin p → Fin k ↦
    δ / 2 ≤ ((fiber A x).dens : ℝ)
  have hB : δ / 2 ≤ (B.dens : ℝ) := ᾊ hk δ hδ A hA
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.dens_empty] at hB
    norm_num at hB
    linarith
  have existsLine (x : {x // x ∈ B}) : ∃ l : Combinatorics.Line (Fin k) (Fin q),
      ∀ a, Sum.elim x (l a) ∈ A :=
    Ὀ hk Μ (δ / 2) (by linarith) hq A x
      (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using x.2)
  choose lineAt ῥ using existsLine
  let l₀ := lineAt ⟨hBne.choose, hBne.choose_spec⟩
  let : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let f : (Fin p → Fin k) → Combinatorics.Line (Fin k) (Fin q) := λ x ↦
    if hx : x ∈ B then lineAt ⟨x, hx⟩ else l₀
  obtain ⟨l, hl⟩ := exists_fiber_density B f
  refine ⟨l, le_trans ?_ (le_trans hl ?_)⟩
  · simpa only [div_div] using
      div_le_div_of_nonneg_right hB
        (by positivity : 0 ≤ (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ))
  · exact_mod_cast Finset.dens_le_dens <| by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hfl : lineAt ⟨x, hx.1⟩ = l := by
        simpa only [f, dif_pos hx.1] using hx.2
      intro a
      rw [← hfl]
      exact ῥ ⟨x, hx.1⟩ a
lemma î {k : ℕ} (Μ : Ζ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), Ι V A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n ἁ A _
    exact ⟨ò hm ἁ, Ἓ hm ἁ A⟩
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  induction m, hm using Nat.le_induction generalizing δ with
  | base =>
      exact ⟨ο k δ, λ n hn A hA ↦
        ᾌ Μ δ hδ n hn A hA⟩
  | succ m hm ih =>
      let q := max 1 (ο k (δ / 2))
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      have hq : ο k (δ / 2) ≤ q := le_max_right _ _
      let : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
      let := lineFintype k q
      let ε := δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q)))
      have hε : 0 < ε := by
        have ᾰ : 0 < Fintype.card (Combinatorics.Line (Fin k) (Fin q)) :=
          Fintype.card_pos
        dsimp only [ε]
        exact div_pos hδ (by exact_mod_cast mul_pos (by norm_num : 0 < (2 : ℕ)) ᾰ)
      obtain ⟨P, hP⟩ := ih ε hε
      refine ⟨P + q, ?_⟩
      intro n hn A hA
      let p := n - q
      have hqn : q ≤ n := by omega
      have hpq : p + q = n := Nat.sub_add_cancel hqn
      have hPp : P ≤ p := by omega
      let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hpq)
      let wordEquiv : (Fin p ⊕ Fin q → Fin k) ≃ (Fin n → Fin k) :=
        e.arrowCongr (Equiv.refl _)
      let A' := A.map wordEquiv.symm.toEmbedding
      have hA' : δ ≤ (A'.dens : ℝ) := by
        simpa only [A', Finset.dens_map_equiv] using density_le_of_card_le hk δ A hA
      obtain ⟨l, hl⟩ := ά hk Μ δ hδ hq A' hA'
      let C := Finset.univ.filter λ x : Fin p → Fin k ↦
        ∀ a, Sum.elim x (l a) ∈ A'
      have hC : ε ≤ (C.dens : ℝ) := by
        simpa only [ε, C] using hl
      obtain ⟨V, hV⟩ := hP p hPp C (card_le_of_density_le hk ε C hC)
      let W₀ : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin p ⊕ Fin q) :=
        (Subspace.concat V (Ô l)).reindex finSumFinEquiv
          (Equiv.refl _) (Equiv.refl _)
      let W : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin n) :=
        W₀.reindex (Equiv.refl _) (Equiv.refl _) e
      refine ⟨W, ?_⟩
      intro z
      let x : Fin m → Fin k := λ i ↦ z (finSumFinEquiv (Sum.inl i))
      let a : Fin k := z (finSumFinEquiv (Sum.inr 0))
      have hx : Sum.elim (V x) (l a) ∈ A' := by
        have hxC : ∀ b, Sum.elim (V x) (l b) ∈ A' := by
          simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hV x
        exact hxC a
      rw [Finset.mem_map_equiv] at hx
      simp only [Equiv.symm_symm] at hx
      convert hx using 1
      funext i
      simp only [W, W₀, Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
        Equiv.refl_symm]
      change (Subspace.concat V (Ô l)) (z ∘ finSumFinEquiv) (e.symm i) =
        wordEquiv (Sum.elim (V x) (l a)) i
      have hz : z ∘ finSumFinEquiv =
          Sum.elim x (λ _ : Fin 1 ↦ a) := by
        funext j
        cases j with
        | inl j => rfl
        | inr j => exact congrArg z (congrArg finSumFinEquiv (congrArg Sum.inr (Fin.eq_zero j)))
      rw [hz, Subspace.concat_apply, ÿ]
      rfl
noncomputable def ὀ (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ Ζ k then
    Nat.find (î h.2.2 m h.1 δ h.2.1)
  else 0
lemma ᾴ {k : ℕ} (Μ : Ζ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : ὀ k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), Ι V A := by
  classical
  rw [ὀ, dif_pos ⟨hm, hδ, Μ⟩] at hn
  exact Nat.find_spec (î Μ m hm δ hδ) n hn A hA
lemma exists_of_density {k : ℕ} (Μ : Ζ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : ὀ k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), Ι V A := by
  exact ᾴ Μ m hm δ hδ n hn A hA
def Ω {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : Finset (Fin p ⊕ Fin q → Fin alphabet) :=
  A.map (e.arrowCongr (Equiv.refl (Fin alphabet))).symm.toEmbedding
@[simp]
lemma ᾏ {alphabet p q n : ℕ} {e : Fin p ⊕ Fin q ≃ Fin n}
    {A : Finset (Fin n → Fin alphabet)} {w : Fin p ⊕ Fin q → Fin alphabet} :
    w ∈ Ω e A ↔ w ∘ e.symm ∈ A := by
  rw [Ω, Finset.mem_map_equiv, Equiv.symm_symm]
  rfl
@[simp]
lemma dens_splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : (Ω e A).dens = A.dens := by
  rw [Ω, Finset.dens_map_equiv]
def ý {p q n : ℕ} (h : p + q = n) : Fin p ⊕ Fin q ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)
def Ὣ (α : Type*) (m : ℕ) : Combinatorics.Subspace (Fin m) α (Fin m) where
  idxFun i := Sum.inr i
  proper e := ⟨e, rfl⟩
@[simp]
lemma ᾦ {α : Type*} {m : ℕ} (x : Fin m → α) : Ὣ α m x = x := by
  funext i
  exact (Ὣ α m).apply_inr rfl
def û {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) : Combinatorics.Subspace η α (Fin (m + p)) where
  idxFun i :=
    match finSumFinEquiv.symm i with
    | Sum.inl j => Sum.inl (u j)
    | Sum.inr j => V.idxFun j
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨finSumFinEquiv (Sum.inr i), by simp only [Equiv.symm_apply_apply, hi]⟩
@[simp]
lemma prependFixed_apply {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) (x : η → α) :
    û u V x = Sum.elim u (V x) ∘ finSumFinEquiv.symm := by
  funext i
  simp only [Function.comp_apply, Combinatorics.Subspace.coe_apply, û]
  cases hi : finSumFinEquiv.symm i with
  | inl j => simp only [Sum.elim_inl, Sum.elim_inl, id_eq]
  | inr j =>
      rw [Sum.elim_inr, Combinatorics.Subspace.coe_apply]
def ἂ {m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin m ⊕ Fin r :=
  ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin q))).trans
      (Equiv.sumAssoc (Fin m) (Fin p) (Fin q))).trans ((Equiv.refl (Fin m)).sumCongr e)
def ᾘ {m p q r n : ℕ} (h : m + r = n) (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin n :=
  (ἂ e).trans (ý h)
lemma ᾣ {alphabet η m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r)
    (u : Fin m → Fin alphabet) (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (û u V x) y ∘ (ἂ e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) := by
  funext s
  cases s with
  | inl a => simp [ἂ]
  | inr b =>
      cases hb : e.symm b with
      | inl c => simp [ἂ, hb]
      | inr d => simp [ἂ, hb]
lemma ύ {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (û u V x) y ∘ (ᾘ h e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) ∘
        (ý h).symm := by
  rw [← ᾣ e u V x y]
  rfl
lemma ὑ {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (A : Finset (Fin n → Fin alphabet)) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p)) (x : Fin η → Fin alphabet) :
    fiber (Ω (ᾘ h e) A) (û u V x) =
      fiber (Ω e (fiber (Ω (ý h) A) u)) (V x) := by
  ext y
  simp only [τ, ᾏ]
  rw [ύ]
lemma ᾢ {alphabet m q : ℕ} (ñ : 0 < alphabet) {ε : ℝ} (hε : 0 < ε)
    (A : Finset (Fin m ⊕ Fin q → Fin alphabet)) (u₀ : Fin m → Fin alphabet)
    (hu₀ : ((fiber A u₀).dens : ℝ) < (A.dens : ℝ) - ε) :
    ∃ u, (A.dens : ℝ) + ε / (alphabet : ℝ) ^ m ≤ ((fiber A u).dens : ℝ) := by
  classical
  by_contra! hcon
  have halphabetR : (0 : ℝ) < (alphabet : ℝ) := by exact_mod_cast ñ
  have hpow : (0 : ℝ) < (alphabet : ℝ) ^ m := pow_pos halphabetR m
  have þ : (Fintype.card (Fin m → Fin alphabet) : ℝ) = (alphabet : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have hsum : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) =
      (alphabet : ℝ) ^ m * (A.dens : ℝ) := by
    rw [← σ A, ← þ, ← Finset.card_univ, Finset.card_mul_expect]
  have hle : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) ≤
      ∑ u : Fin m → Fin alphabet, (((A.dens : ℝ) + ε / (alphabet : ℝ) ^ m) +
        if u = u₀ then -(ε + ε / (alphabet : ℝ) ^ m) else 0) := by
    apply Finset.sum_le_sum
    intro u _
    by_cases hu : u = u₀
    · rw [hu, if_pos rfl]
      linarith
    · rw [if_neg hu, add_zero]
      linarith [hcon u]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq' Finset.univ u₀,
    if_pos (Finset.mem_univ u₀), Finset.card_univ, nsmul_eq_mul, þ, hsum, mul_add,
    mul_div_cancel₀ ε hpow.ne'] at hle
  linarith [div_pos hε hpow]
def ú (alphabet dimension : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n → Fin alphabet),
    ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
      ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
        ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (Ω e A) (V x)).dens : ℝ)
private lemma Ὓ (alphabet dimension : ℕ) (ñ : 0 < alphabet)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t n : ℕ, dimension * (t + 1) < n → ∀ A : Finset (Fin n → Fin alphabet),
      1 ≤ (A.dens : ℝ) + t * (ε / (alphabet : ℝ) ^ dimension) →
      ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
        ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
          ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (Ω e A) (V x)).dens : ℝ) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      intro n hn A hfuel
      have hblock : dimension ≤ dimension * (t + 1) :=
        Nat.le_mul_of_pos_right dimension (Nat.succ_pos t)
      have hd : dimension + (n - dimension) = n := by omega
      have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension :=
        div_pos hε (pow_pos (by exact_mod_cast ñ) dimension)
      by_cases hsucc :
          ∀ u, (A.dens : ℝ) - ε ≤ ((fiber (Ω (ý hd) A) u).dens : ℝ)
      · exact ⟨dimension, n - dimension, ý hd, by omega,
          Ὣ (Fin alphabet) dimension, by simpa only [ᾦ] using hsucc⟩
      push Not at hsucc
      obtain ⟨u₀, hu₀⟩ := hsucc
      obtain ⟨u, hu⟩ := ᾢ ñ hε (Ω (ý hd) A) u₀
        (by rwa [dens_splitWords])
      rw [dens_splitWords] at hu
      have hu₁ : ((fiber (Ω (ý hd) A) u).dens : ℝ) ≤ 1 := by
        exact_mod_cast Finset.dens_le_one (s := fiber (Ω (ý hd) A) u)
      have htR : (1 : ℝ) ≤ (t : ℝ) := by
        nlinarith [mul_pos hεpos hεpos]
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by
        have : 1 ≤ t := by exact_mod_cast htR
        omega⟩
      have ᾜ : dimension * (s + 1 + 1) = dimension * (s + 1) + dimension := by ring
      obtain ⟨p, q, e, hq, V, hV⟩ := ih s (by omega) (n - dimension) (by omega)
        (fiber (Ω (ý hd) A) u)
        (by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hfuel; linarith)
      refine ⟨dimension + p, q, ᾘ hd e, hq, û u V, ?_⟩
      intro x
      rw [ὑ]
      linarith [hV x]
lemma Ë (alphabet dimension : ℕ)
    (ὄ : 1 ≤ dimension) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ú alphabet dimension ε n := by
  classical
  by_cases ñ : alphabet = 0
  · subst alphabet
    refine ⟨dimension + 1, ?_⟩
    intro n hn A
    refine ⟨dimension, n - dimension, ý (by omega), by omega,
      ò ὄ le_rfl, ?_⟩
    intro x
    exact Fin.elim0 (x ⟨0, ὄ⟩)
  have ñ₀ : 0 < alphabet := Nat.pos_of_ne_zero ñ
  have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension :=
    div_pos hε (pow_pos (by exact_mod_cast ñ₀) dimension)
  obtain ⟨t, ht⟩ := exists_nat_gt (1 / (ε / (alphabet : ℝ) ^ dimension))
  refine ⟨dimension * (t + 1) + 1, ?_⟩
  intro n hn A
  apply Ὓ alphabet dimension ñ₀ hε t n (by omega) A
  rw [div_lt_iff₀ hεpos] at ht
  linarith [NNRat.cast_nonneg (α := ℝ) A.dens]
noncomputable def variableCutFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ dimension ∧ 0 < ε then
    Nat.find (Ë alphabet dimension h.1 h.2)
  else 0
lemma variableCutFibersBound_spec (alphabet dimension n : ℕ) (ὄ : 1 ≤ dimension)
    {ε : ℝ} (hε : 0 < ε) (hn : variableCutFibersBound alphabet dimension ε ≤ n) :
    ú alphabet dimension ε n := by
  classical
  rw [variableCutFibersBound, dif_pos ⟨ὄ, hε⟩] at hn
  exact Nat.find_spec
    (Ë alphabet dimension ὄ hε) n hn
lemma average_restrictedParameterSlice {k M : ℕ}
    {ι κ : Type*} [Β (κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) :
    Finset.expect Finset.univ (λ y : κ → Fin (k + 1) ↦
      ((Finset.univ.filter λ x : Fin M → Fin k ↦
        Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) =
      Finset.expect Finset.univ (λ x : Fin M → Fin k ↦
        ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) := by
  simp_rw [← Finset.expect_indicator_one]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro y _
  by_cases h : Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A
  · have hx : x ∈ Finset.univ.filter λ z : Fin M → Fin k ↦
        Sum.elim (W (Fin.castSucc ∘ z)) y ∈ A :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hy : y ∈ fiber A (W (Fin.castSucc ∘ x)) := τ.mpr h
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    simp only [Pi.one_apply]
  · have hx : x ∉ Finset.univ.filter λ z : Fin M → Fin k ↦
        Sum.elim (W (Fin.castSucc ∘ z)) y ∈ A :=
      λ hx ↦ h (Finset.mem_filter.mp hx).2
    have hy : y ∉ fiber A (W (Fin.castSucc ∘ x)) := λ hy ↦ h (τ.mp hy)
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
lemma ø {k M : ℕ} (hk : 0 < k) (δ : ℝ)
    {ι κ : Type*} [Β (κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hW : ∀ x : Fin M → Fin k,
      δ / 2 ≤ ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) :
    ∃ y : κ → Fin (k + 1),
      δ / 2 ≤
        ((Finset.univ.filter λ x : Fin M → Fin k ↦
          Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have havg : δ / 2 ≤
      Finset.expect Finset.univ (λ y : κ → Fin (k + 1) ↦
        ((Finset.univ.filter λ x : Fin M → Fin k ↦
          Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) := by
    rw [average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty λ x _ ↦ hW x
  by_contra! h
  apply (not_lt_of_ge havg)
  apply Finset.expect_lt
  · intro y _
    exact (h y).le
  · exact ⟨λ _ ↦ 0, Finset.mem_univ _, h (λ _ ↦ 0)⟩
lemma ὗ {k m M : ℕ} {ι κ ζ : Type*}
    [Α (ζ → Fin (k + 1))] (e : ι ⊕ κ ≃ ζ)
    (A : Finset (ζ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) (y : κ → Fin (k + 1))
    (S : Combinatorics.Subspace (Fin m) (Fin k) (Fin M))
    (hS : ∀ x, (Sum.elim (W (Fin.castSucc ∘ S x)) y) ∘ e.symm ∈ A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ,
      Ï V Fin.castSuccEmb ⊆ A := by
  let lift_S : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M) :=
    { idxFun := λ i ↦ (S.idxFun i).map (Fin.castSuccEmb : Fin k → Fin (k + 1)) id
      proper := λ e ↦ by
        obtain ⟨i, hi⟩ := S.proper e
        refine ⟨i, ?_⟩
        simp [hi] }
  have h_lift_eval (x : Fin m → Fin k) : lift_S (Fin.castSuccEmb ∘ x) = Fin.castSucc ∘ S x := by
    ext i
    simp [lift_S, Combinatorics.Subspace.coe_apply]
    cases S.idxFun i <;> simp
  let concat_suffix : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ζ :=
    { idxFun := λ c ↦
        match e.symm c with
        | Sum.inl i => W.idxFun i
        | Sum.inr j => Sum.inl (y j)
      proper := λ e' ↦ by
        obtain ⟨i, hi⟩ := W.proper e'
        refine ⟨e (Sum.inl i), ?_⟩
        simp [hi] }
  have ᾓ (z : Fin M → Fin (k + 1)) :
      concat_suffix z = (Sum.elim (W z) y) ∘ e.symm := by
    ext c
    simp only [Subspace.coe_apply, Function.comp_apply, concat_suffix]
    cases e.symm c with
    | inl i => simp [Combinatorics.Subspace.coe_apply]
    | inr j => simp
  let V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ :=
    compose concat_suffix lift_S
  refine ⟨V, ?_⟩
  intro w hw
  rw [Ï, Finset.mem_image] at hw
  rcases hw with ⟨x, _, rfl⟩
  rw [Ψ, h_lift_eval x, ᾓ (Fin.castSucc ∘ S x)]
  exact hS x
lemma Ἃ {m n : ℕ} (hm : 1 ≤ m) (ἁ : m ≤ n)
    (A : Finset (Fin n → Fin 1)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n),
      Ï V Fin.castSuccEmb ⊆ A := by
  let V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n) :=
    { idxFun := λ i ↦ if hi : i.val < m then Sum.inr ⟨i.val, hi⟩ else Sum.inl 0
      proper := λ e ↦ by
        refine ⟨Fin.castLE ἁ e, ?_⟩
        simp only [Fin.castLE, e.isLt, ↓reduceDIte] }
  refine ⟨V, ?_⟩
  intro w hw
  rw [Ï] at hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨x, _⟩ := hw
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)
lemma Ð {k : ℕ} (Μ : Ζ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
      δ * (k + 1 : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          Ï V Fin.castSuccEmb ⊆ A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n ἁ A _
    exact Ἃ hm ἁ A
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  let M := max 1 (ὀ k m (δ / 2))
  refine ⟨variableCutFibersBound (k + 1) M (δ / 2), ?_⟩
  intro n hn A hA
  have hM : 1 ≤ M := le_max_left _ _
  have hA' : δ ≤ (A.dens : ℝ) := by
    apply density_le_of_card_le (Nat.zero_lt_succ k) δ A
    convert hA using 1
    norm_num
  obtain ⟨p, q, e, _hq, W, hW⟩ :=
    variableCutFibersBound_spec (k + 1) M n hM (by linarith) hn A
  obtain ⟨y, hy⟩ :=
    ø hk δ (Ω e A) W λ x ↦ by
      linarith [hW (Fin.castSucc ∘ x)]
  let B := Finset.univ.filter λ x : Fin M → Fin k ↦
    Sum.elim (W (Fin.castSucc ∘ x)) y ∈ Ω e A
  obtain ⟨S, hS⟩ :=
    exists_of_density Μ m hm (δ / 2) (by linarith) M (le_max_right _ _) B
      (card_le_of_density_le hk (δ / 2) B (by simpa only [B] using hy))
  apply ὗ e A W y S
  intro x
  rw [← ᾏ]
  simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hS x
noncomputable def Ã (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ Ζ k then
    Nat.find (Ð h.2.2 m h.1 δ h.2.1)
  else 0
lemma ὓ {k : ℕ} (Μ : Ζ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : Ã k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      Ï V Fin.castSuccEmb ⊆ A := by
  classical
  rw [Ã, dif_pos ⟨hm, hδ, Μ⟩] at hn
  exact Nat.find_spec (Ð Μ m hm δ hδ) n hn A hA
lemma exists_restrictAlphabet_subset {k : ℕ} (Μ : Ζ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : Ã k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1)))
    (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      Ï V Fin.castSuccEmb ⊆ A := by
  exact ὓ Μ m hm δ hδ n hn A hA
end Subspace
end Δ
end
section
open Finset
open Combinatorics
open scoped BigOperators
namespace Δ
namespace Parameters
noncomputable def m₀ (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ Ζ k then
    Nat.succ <| Nat.find <| h.2 (δ / 4) (by linarith)
  else 1
lemma m₀_pos (k : ℕ) (δ : ℝ) : 0 < m₀ k δ := by
  classical
  unfold m₀
  split <;> simp
lemma m₀_antitone {k : ℕ} (Μ : Ζ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : m₀ k ρ ≤ m₀ k δ := by
  classical
  rw [m₀, dif_pos ⟨hδ.trans_le hδρ, Μ⟩, m₀, dif_pos ⟨hδ, Μ⟩]
  apply Nat.succ_le_succ
  apply Nat.find_min'
  intro n hn A hA
  exact Nat.find_spec (Μ (δ / 4) (by linarith)) n hn A (le_trans (by gcongr) hA)
lemma ἧ (k : ℕ) {m n : ℕ} (ἁ : m ≤ n) :
    ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m ≤
      ((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n := by
  induction n, ἁ using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    apply ih.trans
    rw [Nat.cast_add, Nat.cast_one]
    suffices 0 ≤ (k : ℝ) * (((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n) by
      rw [Nat.cast_add, Nat.cast_one] at this
      nlinarith [pow_nonneg (by positivity : 0 ≤ (k : ℝ)) n]
    apply mul_nonneg
    · positivity
    · apply sub_nonneg.mpr
      apply pow_le_pow_left₀
      · positivity
      · exact_mod_cast Nat.le_succ k
lemma θ_denominator_pos {k : ℕ} (hk : 2 ≤ k) (δ : ℝ) :
    0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
  apply sub_pos.mpr
  apply pow_lt_pow_left₀
  · exact_mod_cast Nat.lt_succ_self k
  · positivity
  · exact Nat.ne_of_gt <| m₀_pos k δ
noncomputable def θ (k : ℕ) (δ : ℝ) : ℝ :=
  (δ / 4) /
    (((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ)
lemma θ_mono_of_dhj {k : ℕ} (hk : 2 ≤ k) (Μ : Ζ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  unfold θ
  refine div_le_div₀ ?_ (by linarith) (θ_denominator_pos hk ρ) ?_
  · exact div_nonneg (hδ.trans_le hδρ).le (by norm_num)
  · exact ἧ k <| m₀_antitone Μ hδ hδρ
lemma θ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  classical
  by_cases Μ : Ζ k
  · exact θ_mono_of_dhj hk Μ hδ hδρ
  · unfold θ
    rw [m₀, dif_neg (λ h ↦ Μ h.2), m₀, dif_neg (λ h ↦ Μ h.2)]
    apply div_le_div_of_nonneg_right
    · linarith
    · rw [pow_one, pow_one, Nat.cast_add, Nat.cast_one]
      linarith
lemma θ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < θ k δ := by
  unfold θ
  exact div_pos (by positivity) (θ_denominator_pos hk δ)
noncomputable def η (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))
lemma η_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : η k δ ≤ η k ρ := by
  unfold η
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hδρ (θ_mono hk hδ hδρ) (θ_pos hk hδ).le
        (hδ.trans_le hδρ).le
    · norm_num
  · exact div_le_div_of_nonneg_right (θ_mono hk hδ hδρ) (by norm_num)
  · exact div_le_div_of_nonneg_right hδρ (by norm_num)
lemma η_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < η k δ := by
  unfold η
  apply lt_min
  · positivity [θ_pos hk hδ]
  · apply lt_min
    · positivity [θ_pos hk hδ]
    · positivity
noncomputable def γ (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * η k δ ^ 2 / k) (min (η k δ ^ 2 / 2) (3 * η k δ))
lemma γ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : γ k δ ≤ γ k ρ := by
  unfold γ
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · apply mul_le_mul hδρ
      · exact (sq_le_sq₀ (η_pos hk hδ).le
          (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
      · positivity
      · exact (hδ.trans_le hδρ).le
    · positivity
  · apply div_le_div_of_nonneg_right
    · exact (sq_le_sq₀ (η_pos hk hδ).le
        (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
    · norm_num
  · exact mul_le_mul_of_nonneg_left (η_mono hk hδ hδρ) (by norm_num)
lemma γ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < γ k δ := by
  unfold γ
  positivity [η_pos hk hδ]
lemma η_lt_θ_div_two {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    η k δ < θ k δ / 2 := by
  unfold η
  apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
  linarith [θ_pos hk hδ]
lemma η_le_δ_div_six (k : ℕ) (δ : ℝ) : η k δ ≤ δ / 6 := by
  unfold η
  exact (min_le_right _ _).trans (min_le_right _ _)
lemma γ_le_η_sq_div_two (k : ℕ) (δ : ℝ) : γ k δ ≤ η k δ ^ 2 / 2 := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_left _ _)
lemma γ_le_three_mul_η (k : ℕ) (δ : ℝ) : γ k δ ≤ 3 * η k δ := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_right _ _)
lemma γ_mono_lowerBound {k : ℕ} (hk : 2 ≤ k) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    0 < γ k δ₀ ∧ ∀ ρ, δ₀ ≤ ρ → γ k δ₀ ≤ γ k ρ := by
  constructor
  · exact γ_pos hk hδ₀
  · intro ρ hδρ
    exact γ_mono hk hδ₀ hδρ
lemma θ_le_one {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ₁ : δ ≤ 1) :
    θ k δ ≤ 1 := by
  unfold θ
  have hden_pos : 0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ :=
    θ_denominator_pos hk δ
  have ῧ : 1 ≤ ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
    have h1 : ((k + 1 : ℕ) : ℝ) ^ 1 - (k : ℝ) ^ 1 = (1 : ℝ) := by norm_num
    simpa [h1] using ἧ k (Nat.succ_le_of_lt (m₀_pos k δ))
  apply (div_le_one hden_pos).mpr
  linarith [hδ₁, ῧ]
lemma large_intersection_complement_gain {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    (δ + 6 * η k δ) * (1 - θ k δ / 4) ≤ δ - 3 * η k δ := by
  have hη : η k δ ≤ δ * θ k δ / 48 :=
    min_le_left (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))
  nlinarith [hη, θ_pos hk hδ₀, η_pos hk hδ₀,
    mul_nonneg hδ₀.le (θ_pos hk hδ₀).le,
    mul_nonneg (η_pos hk hδ₀).le (θ_pos hk hδ₀).le]
end Parameters
end Δ
end
section
open Finset
open Combinatorics
open scoped BigOperators
namespace Δ
def ἰ {α ι : Type*} (i j : α) (x y : ι → α) : Prop :=
  ∀ a, a ≠ i → a ≠ j → ∀ c, (x c = a ↔ y c = a)
def Γ {α ι : Type*} (i j : α) (D : Finset (ι → α)) : Prop :=
  ∀ ⦃x y⦄, ἰ i j x y → (x ∈ D ↔ y ∈ D)
def Κ {α ι ι' : Type*}
    (e : ι ≃ ι') (D : Finset (ι → α)) : Finset (ι' → α) :=
  D.map ((e.arrowCongr (Equiv.refl α)).toEmbedding)
@[simp]
lemma υ {α ι ι' : Type*}
    {e : ι ≃ ι'} {D : Finset (ι → α)} {w : ι' → α} :
    w ∈ Κ e D ↔ w ∘ e ∈ D := by
  rw [Κ, Finset.mem_map_equiv]
  rfl
@[simp]
lemma Ὃ {α ι ι' : Type*} [Β (ι → α)] [Β (ι' → α)]
    (e : ι ≃ ι') (D : Finset (ι → α)) : (Κ e D).dens = D.dens := by
  rw [Κ, Finset.dens_map_equiv]
def ï {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) : Combinatorics.Subspace η α ι where
  idxFun c := Sum.elim (λ a ↦ Sum.inl (z a)) V.idxFun (e c)
  proper x := by
    obtain ⟨c, hc⟩ := V.proper x
    exact ⟨e.symm (Sum.inr c), by simp only [Equiv.apply_symm_apply, Sum.elim_inr, hc]⟩
@[simp]
lemma Á {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) (x : η → α) :
    ï e z V x = Sum.elim z (V x) ∘ e := by
  funext c
  simp only [Combinatorics.Subspace.coe_apply, ï, Function.comp_apply]
  cases e c with
  | inl a => simp only [Sum.elim_inl, id_eq]
  | inr c =>
      simp only [Sum.elim_inr, Combinatorics.Subspace.coe_apply]
namespace Γ
lemma reindex {α ι ι' : Type*}
    {i j : α} {D : Finset (ι → α)} (e : ι ≃ ι') (hD : Γ i j D) :
    Γ i j (Δ.Κ e D) := by
  intro x y ô
  simp only [υ]
  apply hD
  intro a ῐ haj c
  exact ô a ῐ haj (e c)
lemma ᾬ {α ι κ : Type*} [Β (κ → α)] [Α (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : Γ i j D) (v : ι → α) :
    Γ i j (Δ.fiber D v) := by
  intro x y ô
  simp only [τ]
  apply hD
  intro a ῐ haj c
  cases c with
  | inl c => simp only [Sum.elim_inl]
  | inr c => exact ô a ῐ haj c
lemma compl {α ι : Type*} [Β (ι → α)] [Α (ι → α)]
    {i j : α} {D : Finset (ι → α)} (hD : Γ i j D) :
    Γ i j Dᶜ := by
  intro x y ô
  simp only [mem_compl]
  exact not_congr (hD ô)
noncomputable def Η {η α ι : Type*} [Β (η → α)]
    [Α (ι → α)] (D : Finset (ι → α))
    (𝒱 : Set (Combinatorics.Subspace η α ι)) : Finset (ι → α) := by
  classical
  exact D.filter λ w ↦ ∀ V ∈ 𝒱, w ∉ Subspace.range V
noncomputable def intersection {r : ℕ} {X : Type*} [Β X]
    (D : Fin r → Finset X) : Finset X := by
  classical
  exact Finset.univ.inf D
@[simp]
lemma Φ {r : ℕ} {X : Type*} [Β X]
    {D : Fin r → Finset X} {x : X} :
    x ∈ intersection D ↔ ∀ i, x ∈ D i := by
  classical
  rw [intersection, ← Finset.singleton_subset_iff, Finset.le_inf_iff]
  simp only [Finset.mem_univ, forall_const, Finset.singleton_subset_iff]
def Ç (k m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ i : Fin k, ∀ D : Finset (Fin n → Fin (k + 1)),
    Γ i.castSucc (Fin.last k) D →
    2 * β ≤ (D.dens : ℝ) →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.Ι V D) ∧
      (𝒱.PairwiseDisjoint λ V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((Η D 𝒱).dens : ℝ) < 2 * β
lemma sdiff {α ι : Type*} [Α (ι → α)]
    {i j : α} {D E : Finset (ι → α)} (hD : Γ i j D)
    (hE : Γ i j E) : Γ i j (D \ E) := by
  intro x y ô
  simp only [Finset.mem_sdiff]
  rw [hD ô, hE ô]
lemma fiber_congr {α ι κ : Type*} [Β (κ → α)] [Α (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : Γ i j D) {v w : ι → α}
    (hvw : ἰ i j v w) :
    Δ.fiber D v = Δ.fiber D w := by
  ext y
  simp only [τ]
  apply hD
  intro a ῐ haj c
  cases c with
  | inl c => exact hvw a ῐ haj c
  | inr c => simp only [Sum.elim_inr]
end Γ
private lemma ᾤ {α ω ν ν₁ ν₂ : Type*} (s : ν ≃ ν₁ ⊕ ν₂)
    (u : ω → α) (r : ν₁ → α) (x : ν₂ → α) :
    Sum.elim (Sum.elim u r) x ∘
        (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm) =
      Sum.elim u (Sum.elim r x ∘ s) := by
  funext c
  cases c with
  | inl a => simp [Equiv.sumAssoc]
  | inr n => cases hn : s n <;> simp [Equiv.sumAssoc, hn]
private lemma Þ {α ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν)
    (s : ν ≃ ν₁ ⊕ ν₂) (u : ω → α) (r : ν₁ → α) (x : ν₂ → α) :
    Sum.elim (Sum.elim u r) x ∘
        (e.trans (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm)) =
      Sum.elim u (Sum.elim r x ∘ s) ∘ e := by
  rw [← ᾤ s u r x]
  rfl
private lemma í {α ι ω ν ν₁ ν₂ : Type*}
    [Β α] [Α α] [Β ω]
    [Β ν] [Α ν] [Β ν₁] [Β ν₂] [Α ν₂]
    (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂) (U : Finset (ι → α)) (u : ω → α) (r : ν₁ → α) :
    Δ.fiber
        (Κ (e.trans (((Equiv.refl ω).sumCongr s).trans
          (Equiv.sumAssoc ω ν₁ ν₂).symm)) U) (Sum.elim u r) =
      Δ.fiber
        (Κ s (Δ.fiber (Κ e U) u)) r := by
  ext x
  simp only [τ, υ, Þ]
private lemma ῑ {α ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (w : ι → α) :
    Sum.elim (λ a ↦ w (e.symm (Sum.inl a)))
        (λ n ↦ w (e.symm (Sum.inr n))) ∘ e = w := by
  simpa [Function.comp_def] using congrArg (· ∘ e) (Sum.elim_comp_inl_inr (w ∘ e.symm))
private lemma ὖ {α ι ω ν : Type*}
    [Β α] [Α α] [Β ι] [Β ω]
    [Β ν] [Α ν]
    (e : ι ≃ ω ⊕ ν) (A B : Finset (ι → α)) (v : ω → α) :
    Δ.fiber (Κ e (A \ B)) v =
      Δ.fiber (Κ e A) v \
        Δ.fiber (Κ e B) v := by
  ext y
  simp only [Finset.mem_sdiff, τ, υ]
private lemma ᾖ {X : Type*} [Β X] [Α X] {A B : Finset X}
    (h : B ⊆ A) : (((A \ B).dens : ℝ)) = (A.dens : ℝ) - (B.dens : ℝ) := by
  push_cast [← Finset.dens_sdiff_add_dens_eq_dens h]
  ring
private lemma ᾐ {X : Type*} [Β X] {A : Finset X} (h : A.Nonempty) :
    1 / (Fintype.card X : ℝ) ≤ (A.dens : ℝ) := by
  rw [Finset.nnratCast_dens]
  gcongr
  exact_mod_cast h.card_pos
lemma ἕ {k m b : ℕ} (Μ : Ζ k) (hm : 1 ≤ m)
    (i : Fin k) {β : ℝ} (hβ : 0 < β) (hb : Subspace.Ã k m β ≤ b)
    (E : Finset (Fin b → Fin (k + 1)))
    (hE : Γ i.castSucc (Fin.last k) E) (hdens : β ≤ (E.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b), Subspace.Ι V E := by
  obtain ⟨V, hV⟩ :=
    Subspace.exists_restrictAlphabet_subset Μ m hm β hβ b hb E
      (by
        have þ := Subspace.card_le_of_density_le (k := k + 1) (Nat.succ_pos k) β E hdens
        push_cast at þ ⊢
        exact þ)
  refine ⟨V, ?_⟩
  intro x
  refine (hE ?_).mpr
    (hV (Finset.mem_image.mpr ⟨λ e ↦ if h : x e = Fin.last k then i else (x e).castPred h,
      Finset.mem_univ _, rfl⟩))
  intro a ῐ hal c
  cases hc : V.idxFun c with
  | inl t => simp only [V.apply_inl hc]
  | inr e =>
      simp only [V.apply_inr hc, Function.comp_apply]
      by_cases hx : x e = Fin.last k
      · rw [dif_pos hx, hx, Fin.castSuccEmb_apply]
        apply iff_of_false
        · intro h
          exact hal h.symm
        · intro h
          exact ῐ h.symm
      · rw [dif_neg hx, Fin.castSuccEmb_apply, Fin.castSucc_castPred]
private lemma ι {α ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂)
    (u : ω → α) (y : ν₁ → α) (x : ν₂ → α) :
    Sum.elim (Sum.elim u y) x ∘
        (e.trans (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm)) =
      Sum.elim (Sum.elim u x) y ∘
        (e.trans (((Equiv.refl ω).sumCongr (s.trans (Equiv.sumComm ν₁ ν₂))).trans
          (Equiv.sumAssoc ω ν₂ ν₁).symm)) := by
  rw [Þ, Þ]
  refine congrArg (· ∘ e) (congrArg (Sum.elim u) ?_)
  funext n
  cases hn : s n <;> simp [hn]
noncomputable def É {k m b : ℕ} (hm : 1 ≤ m) (ᾒ : m ≤ b)
    (E : Finset (Fin b → Fin (k + 1))) :
    Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b) := by
  classical
  exact if h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.Ι V E then Classical.choose h
    else Subspace.repeatInitial (Fin (k + 1)) hm ᾒ
lemma Ὥ {k m b : ℕ} (hm : 1 ≤ m) (ᾒ : m ≤ b)
    {E : Finset (Fin b → Fin (k + 1))}
    (h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.Ι V E) :
    Subspace.Ι (É hm ᾒ E) E := by
  classical
  rw [É, dif_pos h]
  exact Classical.choose_spec h
namespace Γ
@[simp]
private lemma ῃ {η α ι : Type*} [Β (η → α)] [Α (ι → α)]
    (D : Finset (ι → α)) :
    Η D (∅ : Set (Combinatorics.Subspace η α ι)) = D := by
  simp only [Η, Set.mem_empty_iff_false, false_implies, implies_true,
    Finset.filter_true_of_mem]
private def À {α η : Type*} {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin N)) :
    Combinatorics.Subspace η α (Fin n) where
  idxFun i :=
    match e.symm i with
    | Sum.inl j => Sum.inl (z j)
    | Sum.inr j => V.idxFun j
  proper a := by
    obtain ⟨i, hi⟩ := V.proper a
    refine ⟨e (Sum.inr i), ?_⟩
    simp only [Equiv.symm_apply_apply, hi]
@[simp]
private lemma Ù {α η : Type*} {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin N)) (x : η → α) :
    À e z V x =
      Sum.elim z (V x) ∘ e.symm := by
  funext i
  cases hi : e.symm i with
  | inl j =>
      simp [À, Combinatorics.Subspace.coe_apply, hi,
        Sum.elim, Function.comp_apply]
  | inr j =>
      simp [À, Combinatorics.Subspace.coe_apply, hi,
        Sum.elim, Function.comp_apply]
private lemma ὒ {α η : Type*} [Β α] [Β (η → α)]
    [Α α] {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (D : Finset (Fin n → α))
    (tiles : (Fin r → α) → Set (Combinatorics.Subspace η α (Fin N)))
    (hfinite : ∀ z, (tiles z).Finite)
    (ς : ∀ z V, V ∈ tiles z →
      Subspace.Ι V (fiber (D.map
        (e.arrowCongr (Equiv.refl α)).symm.toEmbedding) z))
    (Χ : ∀ z, (tiles z).PairwiseDisjoint λ V ↦
      (Subspace.range V : Set (Fin N → α))) :
    let global : Set (Combinatorics.Subspace η α (Fin n)) :=
      ⋃ z, À e z '' tiles z
    global.Finite ∧
      (∀ V ∈ global, Subspace.Ι V D) ∧
      (global.PairwiseDisjoint λ V ↦ (Subspace.range V : Set (Fin n → α))) := by
  classical
  dsimp only
  refine ⟨Set.finite_iUnion λ z ↦ (hfinite z).image (À e z), ?_, ?_⟩
  · intro U hU x
    simp only [Set.mem_iUnion, Set.mem_image] at hU
    obtain ⟨z, V, hV, rfl⟩ := hU
    have hx := ς z V hV x
    simp only [τ, Finset.mem_map_equiv, Equiv.symm_symm] at hx
    simpa [Ù, Equiv.arrowCongr] using hx
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' ῲ ὅ
    simp only [Set.mem_iUnion, Set.mem_image] at hU ῲ
    obtain ⟨z, V, hV, rfl⟩ := hU
    obtain ⟨z', V', hV', rfl⟩ := ῲ
    obtain ⟨w, hw, ῢ⟩ := ὅ
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.mp ῢ
    have hzx : Sum.elim z (V x) = Sum.elim z' (V' x') := by
      funext c
      have hc := congrFun (hx.trans hx'.symm) (e c)
      simpa only [Ù, Function.comp_apply,
        Equiv.symm_apply_apply] using hc
    have hzz : z = z' := by
      funext j
      exact congrFun hzx (Sum.inl j)
    subst z'
    apply congrArg (À e z)
    apply Set.pairwiseDisjoint_iff.mp (Χ z) hV hV'
    refine ⟨V x, Subspace.mem_range.mpr ⟨x, rfl⟩,
      Subspace.mem_range.mpr ⟨x', ?_⟩⟩
    exact funext λ j ↦ (congrFun hzx (Sum.inr j)).symm
private lemma Ἔ {α η : Type*} [Β α] [Β (η → α)]
    [Α α] {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (D : Finset (Fin n → α))
    (tiles : (Fin r → α) → Set (Combinatorics.Subspace η α (Fin N)))
    (z : Fin r → α) :
    let wordEquiv := e.arrowCongr (Equiv.refl α)
    let global : Set (Combinatorics.Subspace η α (Fin n)) :=
      ⋃ z, À e z '' tiles z
    fiber ((Η D global).map wordEquiv.symm.toEmbedding) z =
      Η (fiber (D.map wordEquiv.symm.toEmbedding) z) (tiles z) := by
  classical
  dsimp only
  ext y
  simp only [τ, Finset.mem_map_equiv, Η, Finset.mem_filter]
  constructor
  · rintro ⟨hyD, Ό⟩
    refine ⟨hyD, ?_⟩
    intro V hV hyV
    apply Ό (À e z V)
    · exact Set.mem_iUnion_of_mem z <| Set.mem_image_of_mem _ hV
    · obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyV
      exact Subspace.mem_range.mpr ⟨x, by
        simp [Ù, Equiv.arrowCongr, hx]⟩
  · rintro ⟨hyD, Ό⟩
    refine ⟨hyD, ?_⟩
    intro U hU hyU
    simp only [Set.mem_iUnion, Set.mem_image] at hU
    obtain ⟨z', V, hV, rfl⟩ := hU
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyU
    have hconcat : Sum.elim z y = Sum.elim z' (V x) := by
      apply (e.arrowCongr (Equiv.refl α)).injective
      simpa [Ù, Equiv.arrowCongr] using hx.symm
    have hzz : z = z' := by
      funext j
      exact congrFun hconcat (Sum.inl j)
    subst z'
    apply Ό V hV
    exact Subspace.mem_range.mpr ⟨x,
      funext λ j ↦ (congrFun hconcat (Sum.inr j)).symm⟩
private lemma ᾗ {ι : Type*} [Β ι] [Α ι]
    {k m S : ℕ} {β c : ℝ}
    (U R : Finset (ι → Fin (k + 1)))
    (newTiles oldTiles : Set
      (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι))
    (hnewfinite : newTiles.Finite) (holdfinite : oldTiles.Finite)
    (hRU : R ⊆ U)
    (ὧ : ∀ V ∈ newTiles, Subspace.Ι V R)
    (hRcovered : ∀ w ∈ R, ∃ V ∈ newTiles, w ∈ Subspace.range V)
    (ί : newTiles.PairwiseDisjoint λ V ↦
      (Subspace.range V : Set (ι → Fin (k + 1))))
    (ᾟ : ∀ V ∈ oldTiles, Subspace.Ι V (U \ R))
    (Ύ : oldTiles.PairwiseDisjoint λ V ↦
      (Subspace.range V : Set (ι → Fin (k + 1))))
    (hRdens : c ≤ (R.dens : ℝ))
    (Ῑ : ((Η (U \ R) oldTiles).dens : ℝ) < 2 * β ∨
      ((Η (U \ R) oldTiles).dens : ℝ) + S * c ≤ ((U \ R).dens : ℝ)) :
    let allTiles := newTiles ∪ oldTiles
    allTiles.Finite ∧
      (∀ V ∈ allTiles, Subspace.Ι V U) ∧
      (allTiles.PairwiseDisjoint λ V ↦
        (Subspace.range V : Set (ι → Fin (k + 1)))) ∧
      (((Η U allTiles).dens : ℝ) < 2 * β ∨
        ((Η U allTiles).dens : ℝ) + (S + 1) * c ≤ (U.dens : ℝ)) := by
  classical
  dsimp only
  refine ⟨hnewfinite.union holdfinite, ?_, ?_, ?_⟩
  · intro V hV
    rcases hV with hV | hV
    · exact λ x ↦ hRU (ὧ V hV x)
    · exact λ x ↦ (Finset.mem_sdiff.mp (ᾟ V hV x)).1
  · apply Set.PairwiseDisjoint.union ί Ύ
    intro V hV V' hV' _
    rw [Set.disjoint_left]
    intro w hw ῢ
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.mp ῢ
    exact (Finset.mem_sdiff.mp (hx' ▸ ᾟ V' hV' x')).2
      (hx ▸ ὧ V hV x)
  · have μ : Η U (newTiles ∪ oldTiles) =
        Η (U \ R) oldTiles := by
      ext w
      simp only [Η, Finset.mem_filter, Finset.mem_sdiff, Set.mem_union]
      constructor
      · rintro ⟨hwU, ð⟩
        refine ⟨⟨hwU, ?_⟩, ?_⟩
        · intro hwR
          obtain ⟨V, hV, hmem⟩ := hRcovered w hwR
          exact ð V (Or.inl hV) hmem
        · intro V hV
          exact ð V (Or.inr hV)
      · rintro ⟨⟨hwU, hwR⟩, ð⟩
        refine ⟨hwU, ?_⟩
        rintro V (hV | hV)
        · intro hmem
          obtain ⟨x, hx⟩ := Subspace.mem_range.mp hmem
          exact hwR (hx ▸ ὧ V hV x)
        · exact ð V hV
    rw [μ]
    rcases Ῑ with hlt | hle
    · exact Or.inl hlt
    · apply Or.inr
      rw [ᾖ hRU] at hle
      nlinarith
private lemma ᾎ {k m b : ℕ} {ι ζ : Type*}
    [Β ι] [Β ζ]
    [Α (ζ → Fin (k + 1))]
    (hm : 1 ≤ m) (ᾒ : m ≤ b) (e : ι ≃ ζ ⊕ Fin b)
    (U : Finset (ι → Fin (k + 1)))
    (B : (ζ → Fin (k + 1)) → Finset (Fin b → Fin (k + 1)))
    (hB : B = λ z ↦ fiber (Κ e U) z)
    (good : Finset (ζ → Fin (k + 1)))
    (tile : (ζ → Fin (k + 1)) →
      Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (Ώ : tile = λ z ↦ ï e z (É hm ᾒ (B z)))
    (hpick : ∀ z ∈ good, Subspace.Ι (É hm ᾒ (B z)) (B z))
    (R : Finset (ι → Fin (k + 1)))
    (hR : R = U.filter λ w ↦
      (λ a ↦ w (e.symm (Sum.inl a))) ∈ good ∧
        (λ j ↦ w (e.symm (Sum.inr j))) ∈
          Subspace.range (É hm ᾒ (B (λ a ↦ w (e.symm (Sum.inl a)))))) :
    (∀ z ∈ good, Subspace.Ι (tile z) R) ∧
      (∀ w ∈ R, ∃ z ∈ good, w ∈ Subspace.range (tile z)) := by
  classical
  subst B
  constructor
  · intro z hz x
    have hmemU : tile z x ∈ U := by
      have hx := hpick z hz x
      rw [τ, υ] at hx
      simpa only [Ώ, Á] using hx
    have hparts : (λ a ↦ tile z x (e.symm (Sum.inl a))) = z := by
      funext a
      simp only [Ώ, Á, Function.comp_apply,
        Equiv.apply_symm_apply, Sum.elim_inl]
    rw [hR, Finset.mem_filter]
    refine ⟨hmemU, by rw [hparts]; exact hz, ?_⟩
    rw [hparts]
    refine Subspace.mem_range.mpr ⟨x, ?_⟩
    funext j
    simp only [Ώ, Á, Function.comp_apply,
      Equiv.apply_symm_apply, Sum.elim_inr]
  · intro w hw
    rw [hR, Finset.mem_filter] at hw
    obtain ⟨_, hz, hrange⟩ := hw
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hrange
    refine ⟨_, hz, Subspace.mem_range.mpr ⟨x, ?_⟩⟩
    rw [Ώ, Á, hx]
    exact ῑ e w
private lemma Ὗ {k b : ℕ} {ι ζ : Type*}
    [Β ι] [Α ι] [Β ζ]
    [Β (ζ → Fin (k + 1))]
    (e : ι ≃ ζ ⊕ Fin b) (R : Finset (ι → Fin (k + 1)))
    (good : Finset (ζ → Fin (k + 1))) {β : ℝ}
    (ἅ : β ≤ (good.dens : ℝ))
    (hnonempty : ∀ z ∈ good, (fiber (Κ e R) z).Nonempty) :
    β / ((k : ℝ) + 1) ^ b ≤ (R.dens : ℝ) := by
  classical
  have þ : (Fintype.card (Fin b → Fin (k + 1)) : ℝ) = ((k : ℝ) + 1) ^ b := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one]
  have Ἤ (z : ζ → Fin (k + 1)) (hz : z ∈ good) :
      1 / ((k : ℝ) + 1) ^ b ≤ ((fiber (Κ e R) z).dens : ℝ) := by
    rw [← þ]
    exact ᾐ (hnonempty z hz)
  have haverage : (R.dens : ℝ) =
      𝔼 z : (ζ → Fin (k + 1)), ((fiber (Κ e R) z).dens : ℝ) := by
    rw [σ, Ὃ]
  rw [haverage, div_eq_mul_inv, mul_comm β (((k : ℝ) + 1) ^ b)⁻¹, ← one_div]
  apply le_trans (mul_le_mul_of_nonneg_left ἅ (by positivity))
  rw [← Finset.expect_indicator_one (s := good), Finset.mul_expect]
  apply Finset.expect_le_expect
  intro z _
  by_cases hz : z ∈ good
  · rw [Set.indicator_of_mem (by simpa using hz)]
    simpa only [Pi.one_apply, mul_one] using Ἤ z hz
  · rw [Set.indicator_of_notMem (by simpa using hz)]
    simp only [mul_zero]
    positivity
private lemma ù {k m S b : ℕ} (i : Fin k)
    {ι ω : Type*} [Β ι] [Β ω]
    (hm : 1 ≤ m) (ᾒ : m ≤ b)
    (e₁ : ι ≃ (ω ⊕ Fin (S * b)) ⊕ Fin b)
    (e₂ : ι ≃ (ω ⊕ Fin b) ⊕ Fin (S * b))
    (U : Finset (ι → Fin (k + 1)))
    (B : (ω ⊕ Fin (S * b) → Fin (k + 1)) → Finset (Fin b → Fin (k + 1)))
    (good : Finset (ω ⊕ Fin (S * b) → Fin (k + 1)))
    (R : Finset (ι → Fin (k + 1)))
    (hR : R = U.filter λ w ↦
      (λ a ↦ w (e₁.symm (Sum.inl a))) ∈ good ∧
        (λ j ↦ w (e₁.symm (Sum.inr j))) ∈
          Subspace.range (É hm ᾒ (B (λ a ↦ w (e₁.symm (Sum.inl a))))))
    (hU : ∀ v, Γ i.castSucc (Fin.last k) (fiber (Κ e₂ U) v))
    (hBcongr : ∀ u y y', ἰ i.castSucc (Fin.last k) y y' →
      B (Sum.elim u y) = B (Sum.elim u y'))
    (ἅ : ∀ u y y', B (Sum.elim u y) = B (Sum.elim u y') →
      (Sum.elim u y ∈ good ↔ Sum.elim u y' ∈ good))
    (hswap : ∀ (v : ω ⊕ Fin b → Fin (k + 1)) y,
      Sum.elim v y ∘ e₂ =
        Sum.elim (Sum.elim (λ a ↦ v (Sum.inl a)) y)
          (λ j ↦ v (Sum.inr j)) ∘ e₁) :
    ∀ v, Γ i.castSucc (Fin.last k) (fiber (Κ e₂ (U \ R)) v) := by
  classical
  intro v
  rw [ὖ]
  let u : ω → Fin (k + 1) := λ a ↦ v (Sum.inl a)
  let x : Fin b → Fin (k + 1) := λ j ↦ v (Sum.inr j)
  have hv : v = Sum.elim u x := (Sum.elim_comp_inl_inr v).symm
  have Ὼ (y : Fin (S * b) → Fin (k + 1)) :
      Sum.elim v y ∘ e₂ = Sum.elim (Sum.elim u y) x ∘ e₁ := by
    simpa only [u, x] using hswap v y
  have hUpart := hU v
  apply sdiff hUpart
  intro y y' hyy'
  have ᾧ : B (Sum.elim u y) = B (Sum.elim u y') := hBcongr u y y' hyy'
  have hmemU : Sum.elim v y ∘ e₂ ∈ U ↔ Sum.elim v y' ∘ e₂ ∈ U := by
    have := hUpart (x := y) (y := y') hyy'
    rwa [τ, υ, τ, υ] at this
  have hout (z : Fin (S * b) → Fin (k + 1)) :
      (λ a ↦ (Sum.elim v z ∘ e₂) (e₁.symm (Sum.inl a))) = Sum.elim u z := by
    rw [Ὼ z]
    funext a
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inl]
  have hblock (z : Fin (S * b) → Fin (k + 1)) :
      (λ j ↦ (Sum.elim v z ∘ e₂) (e₁.symm (Sum.inr j))) = x := by
    rw [Ὼ z]
    funext j
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inr]
  have hmemR (z : Fin (S * b) → Fin (k + 1)) :
      z ∈ fiber (Κ e₂ R) v ↔
        Sum.elim v z ∘ e₂ ∈ U ∧ Sum.elim u z ∈ good ∧
          x ∈ Subspace.range (É hm ᾒ (B (Sum.elim u z))) := by
    rw [τ, υ, hR, Finset.mem_filter, hout z, hblock z]
  rw [hmemR y, hmemR y', ᾧ, hmemU]
  rw [ἅ u y y' ᾧ]
private lemma ἇ {k : ℕ} (i : Fin k) (Μ : Ζ k)
    {m b : ℕ} (hm : 1 ≤ m) (ᾒ : m ≤ b) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hb : Subspace.Ã k m β ≤ b) :
    ∀ T : ℕ, ∀ ι ω : Type, ∀ [Β ι] [Α ι] [Β ω],
      ∀ e : ι ≃ ω ⊕ Fin (T * b), ∀ U : Finset (ι → Fin (k + 1)),
        (∀ v : ω → Fin (k + 1),
          Γ i.castSucc (Fin.last k) (fiber (Κ e U) v)) →
        ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι),
          𝒱.Finite ∧ (∀ V ∈ 𝒱, Subspace.Ι V U) ∧
          (𝒱.PairwiseDisjoint λ V ↦ (Subspace.range V : Set (ι → Fin (k + 1)))) ∧
          (((Η U 𝒱).dens : ℝ) < 2 * β ∨
            ((Η U 𝒱).dens : ℝ) + T * (β / ((k : ℝ) + 1) ^ b) ≤ (U.dens : ℝ)) := by
  classical
  intro T
  induction T with
  | zero =>
      intro ι ω _ _ _ e U _
      refine ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty, Or.inr ?_⟩
      simp only [ῃ, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ S ih =>
      intro ι ω _ _ _ e U hins
      by_cases hU : (U.dens : ℝ) < 2 * β
      · exact ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty, Or.inl (by simpa using hU)⟩
      push Not at hU
      have hsplit : S * b + b = (S + 1) * b := by ring
      set s : Fin ((S + 1) * b) ≃ Fin (S * b) ⊕ Fin b :=
        (finSumFinEquiv.trans (finCongr hsplit)).symm with hs
      set e₁ : ι ≃ (ω ⊕ Fin (S * b)) ⊕ Fin b :=
        e.trans (((Equiv.refl ω).sumCongr s).trans
          (Equiv.sumAssoc ω (Fin (S * b)) (Fin b)).symm) with he₁
      set e₂ : ι ≃ (ω ⊕ Fin b) ⊕ Fin (S * b) :=
        e.trans (((Equiv.refl ω).sumCongr (s.trans (Equiv.sumComm (Fin (S * b)) (Fin b)))).trans
          (Equiv.sumAssoc ω (Fin b) (Fin (S * b))).symm) with he₂
      set B : (ω ⊕ Fin (S * b) → Fin (k + 1)) → Finset (Fin b → Fin (k + 1)) :=
        λ z ↦ fiber (Κ e₁ U) z with hBdef
      have hB (u : ω → Fin (k + 1)) (r : Fin (S * b) → Fin (k + 1)) :
          B (Sum.elim u r) = fiber (Κ s (fiber (Κ e U) u)) r :=
        í e s U u r
      have hBins (z : ω ⊕ Fin (S * b) → Fin (k + 1)) :
          Γ i.castSucc (Fin.last k) (B z) := by
        rw [← Sum.elim_comp_inl_inr z, hB]
        exact ᾬ (reindex s (hins _)) _
      have havg : (𝔼 z : (ω ⊕ Fin (S * b) → Fin (k + 1)), ((B z).dens : ℝ)) = (U.dens : ℝ) := by
        simp only [hBdef]
        rw [σ, Ὃ]
      have ἅ :
          β ≤ ((Finset.univ.filter λ z : ω ⊕ Fin (S * b) → Fin (k + 1) ↦
            β ≤ ((B z).dens : ℝ)).dens : ℝ) := by
        refine le_trans ?_ (ß (λ z ↦ ((B z).dens : ℝ)) (2 * β) β
          (λ z ↦ by exact_mod_cast Finset.dens_le_one (s := B z))
          (by linarith) (by rw [havg]; exact hU))
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      set good : Finset (ω ⊕ Fin (S * b) → Fin (k + 1)) :=
        Finset.univ.filter λ z ↦ β ≤ ((B z).dens : ℝ) with Ή
      set tile : (ω ⊕ Fin (S * b) → Fin (k + 1)) →
          Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι :=
        λ z ↦ ï e₁ z (É hm ᾒ (B z)) with ῆ
      have hpick (z : ω ⊕ Fin (S * b) → Fin (k + 1)) (hz : z ∈ good) :
          Subspace.Ι (É hm ᾒ (B z)) (B z) :=
        Ὥ hm ᾒ
          (ἕ Μ hm i hβ₀ hb (B z) (hBins z)
            (by simpa only [Ή, Finset.mem_filter, Finset.mem_univ, true_and] using hz))
      set R : Finset (ι → Fin (k + 1)) := U.filter (λ w ↦
        (λ a ↦ w (e₁.symm (Sum.inl a))) ∈ good ∧
          (λ j ↦ w (e₁.symm (Sum.inr j))) ∈
            Subspace.range (É hm ᾒ (B (λ a ↦ w (e₁.symm (Sum.inl a))))))
        with hRdef
      have hRU : R ⊆ U := Finset.filter_subset _ _
      obtain ⟨htileR, hRtile⟩ :=
        ᾎ hm ᾒ e₁ U B hBdef good tile ῆ hpick R hRdef
      have hdensR : β / ((k : ℝ) + 1) ^ b ≤ (R.dens : ℝ) := by
        apply Ὗ e₁ R good
          (by simpa only [Ή] using ἅ)
        intro z hz
        refine ⟨É hm ᾒ (B z) (λ _ ↦ 0), ?_⟩
        rw [τ, υ]
        simpa only [ῆ, Á] using htileR z hz (λ _ ↦ 0)
      have hins' : ∀ v : ω ⊕ Fin b → Fin (k + 1),
          Γ i.castSucc (Fin.last k) (fiber (Κ e₂ (U \ R)) v) := by
        apply ù i hm ᾒ e₁ e₂ U B good R hRdef
        · intro v
          let u : ω → Fin (k + 1) := λ a ↦ v (Sum.inl a)
          let x : Fin b → Fin (k + 1) := λ j ↦ v (Sum.inr j)
          have hv : v = Sum.elim u x := (Sum.elim_comp_inl_inr v).symm
          rw [hv, he₂,
            í e
              (s.trans (Equiv.sumComm (Fin (S * b)) (Fin b))) U u x]
          exact ᾬ (reindex _ (hins _)) _
        · intro u y y' hyy'
          rw [hB, hB]
          exact fiber_congr (reindex s (hins u)) hyy'
        · intro u y y' ᾧ
          simp only [Ή, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [ᾧ]
        · intro v y
          let u : ω → Fin (k + 1) := λ a ↦ v (Sum.inl a)
          let x : Fin b → Fin (k + 1) := λ j ↦ v (Sum.inr j)
          have hv : v = Sum.elim u x := (Sum.elim_comp_inl_inr v).symm
          rw [hv, he₁, he₂]
          exact (ι e s u y x).symm
      obtain ⟨𝒲, hfin', hcont', hdisj', hdens'⟩ := ih ι (ω ⊕ Fin b) e₂ (U \ R) hins'
      let newTiles := tile '' (good : Set (ω ⊕ Fin (S * b) → Fin (k + 1)))
      have ί : newTiles.PairwiseDisjoint λ V ↦
          (Subspace.range V : Set (ι → Fin (k + 1))) := by
        rw [Set.pairwiseDisjoint_iff]
        intro V hV V' hV' hmeet
        obtain ⟨z, hz, rfl⟩ := hV
        obtain ⟨z', hz', rfl⟩ := hV'
        obtain ⟨w, hw, ῢ⟩ := hmeet
        obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
        obtain ⟨x', hx'⟩ := Subspace.mem_range.mp ῢ
        have hzz : z = z' := by
          funext a
          have h := congrFun (hx.trans hx'.symm) (e₁.symm (Sum.inl a))
          simpa only [ῆ, Á, Function.comp_apply,
            Equiv.apply_symm_apply, Sum.elim_inl] using h
        rw [hzz]
      obtain ⟨hfinite, ς, hdisjoint, hdensity⟩ :=
        ᾗ U R newTiles 𝒲
          (good.finite_toSet.image tile) hfin' hRU
          (λ _ hV ↦ by obtain ⟨z, hz, rfl⟩ := hV; exact htileR z hz)
          (λ w hw ↦ by
            obtain ⟨z, hz, hmem⟩ := hRtile w hw
            exact ⟨tile z, ⟨z, hz, rfl⟩, hmem⟩)
          ί hcont' hdisj' hdensR hdens'
      refine ⟨newTiles ∪ 𝒲, hfinite, ς, hdisjoint, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hdensity
lemma Ý (k m : ℕ) (Μ : Ζ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, Ç k m β N := by
  by_cases hβ : β < 1
  · set b := max m (Subspace.Ã k m β) with hbdef
    have hc : 0 < β / ((k : ℝ) + 1) ^ b := by positivity
    obtain ⟨T, hT⟩ := exists_nat_gt (1 / (β / ((k : ℝ) + 1) ^ b))
    rw [div_lt_iff₀ hc] at hT
    refine ⟨T * b, ?_⟩
    intro i D hD hDβ
    have hsections : ∀ v : Fin 0 → Fin (k + 1),
        Γ i.castSucc (Fin.last k)
          (fiber (Κ (Equiv.emptySum (Fin 0) (Fin (T * b))).symm D) v) := by
      intro v x y ô
      simp only [τ, υ]
      apply hD
      intro a ῐ hal c
      simpa only [Function.comp_apply, Equiv.emptySum_symm_apply, Sum.elim_inr] using
        ô a ῐ hal c
    obtain ⟨𝒱, hfinite, ς, Χ, hconclusion⟩ :=
      ἇ i Μ hm (le_max_left _ _) hβ₀ hβ
        (le_max_right _ _) T (Fin (T * b)) (Fin 0)
        (Equiv.emptySum (Fin 0) (Fin (T * b))).symm D hsections
    refine ⟨𝒱, hfinite, ς, Χ, ?_⟩
    rcases hconclusion with hlt | hle
    · exact hlt
    · exfalso
      have hD₁ : (D.dens : ℝ) ≤ 1 := by exact_mod_cast Finset.dens_le_one (s := D)
      have hnonneg : (0 : ℝ) ≤ ((Η D 𝒱).dens : ℝ) := by positivity
      linarith
  · refine ⟨m, ?_⟩
    intro _i D _hD hDβ
    have hD₁ : (D.dens : ℝ) ≤ 1 := by
      exact_mod_cast Finset.dens_le_one (s := D)
    linarith
private lemma ᾆ {k m N n : ℕ} {β : ℝ}
    (hN : Ç k m β N) (hNn : N ≤ n) :
    Ç k m β n := by
  classical
  intro i D hD hDβ
  let r := n - N
  have hNr : N + r = n := Nat.add_sub_of_le hNn
  let e : Fin r ⊕ Fin N ≃ Fin n :=
    (Equiv.sumComm (Fin r) (Fin N)).trans <| finSumFinEquiv.trans (finCongr hNr)
  let wordEquiv :=
    e.arrowCongr (Equiv.refl (Fin (k + 1)))
  let D' := D.map wordEquiv.symm.toEmbedding
  let slice := λ z : Fin r → Fin (k + 1) ↦ fiber D' z
  have ῼ (z : Fin r → Fin (k + 1)) :
      Γ i.castSucc (Fin.last k) (slice z) := by
    intro x y ô
    simp only [slice, τ, D', Finset.mem_map_equiv]
    apply hD
    intro a ῐ hal c
    cases hc : e.symm c with
    | inl j =>
        simp [wordEquiv, Equiv.arrowCongr, hc]
    | inr j =>
        simpa [wordEquiv, Equiv.arrowCongr, hc] using
          ô a ῐ hal j
  have existsLocal (z : Fin r → Fin (k + 1)) :
      ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N)),
        𝒱.Finite ∧
        (∀ V ∈ 𝒱, Subspace.Ι V (slice z)) ∧
        (𝒱.PairwiseDisjoint λ V ↦
          (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
        ((Η (slice z) 𝒱).dens : ℝ) < 2 * β := by
    by_cases hz : 2 * β ≤ ((slice z).dens : ℝ)
    · exact hN i (slice z) (ῼ z) hz
    · refine ⟨∅, Set.finite_empty, ?_, Set.pairwiseDisjoint_empty, ?_⟩
      · simp
      · have μ : Η (slice z)
            (∅ : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N))) =
              slice z := by
          simp [Η]
        rw [μ]
        exact lt_of_not_ge hz
  choose tiles ὸ Ἲ ὐ ἄ using existsLocal
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ z, À e z '' tiles z
  obtain ⟨ἆ, æ, ë⟩ := ὒ e D tiles
    ὸ
    (λ z V hV ↦ by simpa only [slice, D'] using Ἲ z V hV)
    ὐ
  refine ⟨global, ἆ, æ, ë, ?_⟩
  · let E := (Η D global).map wordEquiv.symm.toEmbedding
    have Ἤ (z : Fin r → Fin (k + 1)) :
        fiber E z = Η (slice z) (tiles z) := by
      simpa only [E, global, slice, D', wordEquiv] using
        Ἔ e D tiles z
    have hEdens :
        (E.dens : ℝ) = ((Η D global).dens : ℝ) := by
      simp only [E, Finset.dens_map_equiv]
    rw [← hEdens, ← σ]
    apply Finset.expect_lt
    · intro z _
      rw [Ἤ]
      exact (ἄ z).le
    · let z : Fin r → Fin (k + 1) := λ _ ↦ 0
      refine ⟨z, Finset.mem_univ z, ?_⟩
      rw [Ἤ]
      exact ἄ z
lemma Û (k m : ℕ) (Μ : Ζ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, ∀ n ≥ N, Ç k m β n := by
  obtain ⟨N, hN⟩ := Ý k m Μ hm hβ₀
  refine ⟨N, ?_⟩
  intro _n hn
  exact ᾆ hN hn
noncomputable def ᾇ (k m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : Ζ k ∧ 1 ≤ m ∧ 0 < β then
    Nat.find (Û k m h.1 h.2.1 h.2.2)
  else 0
lemma ᾶ (k m n : ℕ) (Μ : Ζ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β)
    (hn : ᾇ k m β ≤ n) : Ç k m β n := by
  classical
  rw [ᾇ, dif_pos ⟨Μ, hm, hβ₀⟩] at hn
  exact Nat.find_spec (Û k m Μ hm hβ₀) n hn
noncomputable def Í {η α ι : Type*} [Β (η → α)]
    (V : Combinatorics.Subspace η α ι) (D : Finset (ι → α)) : Finset (η → α) := by
  classical
  apply Finset.univ.filter
  intro x
  exact V x ∈ D
lemma Ἠ {α η ι : Type*}
    [Β (η → α)] {a b : α} (V : Combinatorics.Subspace η α ι) (D : Finset (ι → α))
    (hD : Γ a b D) : Γ a b (Í V D) := by
  classical
  intro x y ô
  simp only [Í, Finset.mem_filter, Finset.mem_univ, true_and]
  apply hD
  intro c hca hcb i
  cases hi : V.idxFun i with
  | inl d =>
      rw [V.apply_inl hi, V.apply_inl hi]
  | inr e =>
      rw [V.apply_inr hi, V.apply_inr hi]
      exact ô c hca hcb e
lemma ὡ {k d M n : ℕ}
    (D : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n))
    (𝒲 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M)))
    (h𝒲 : 𝒲.Finite)
    (ς : ∀ W ∈ 𝒲, Subspace.Ι W (Í V D))
    (Χ : 𝒲.PairwiseDisjoint λ W ↦
      (Subspace.range W : Set (Fin M → Fin (k + 1)))) :
    let 𝒰 := Subspace.compose V '' 𝒲
    𝒰.Finite ∧
      (∀ U ∈ 𝒰, Subspace.Ι U D) ∧
      (𝒰.PairwiseDisjoint λ U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) := by
  classical
  refine ⟨h𝒲.image (Subspace.compose V), ?_, ?_⟩
  · intro U hU x
    obtain ⟨W, hW, rfl⟩ := hU
    simp only [Subspace.Ψ]
    simpa only [Í, Finset.mem_filter, Finset.mem_univ, true_and] using
      ς W hW x
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' ῲ ὅ
    obtain ⟨W, hW, rfl⟩ := hU
    obtain ⟨W', hW', rfl⟩ := ῲ
    apply congrArg (Subspace.compose V)
    apply Set.pairwiseDisjoint_iff.mp Χ hW hW'
    obtain ⟨z, hz, hz'⟩ := ὅ
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hz
    obtain ⟨y, hy⟩ := Subspace.mem_range.mp hz'
    refine ⟨W x, Subspace.mem_range.mpr ⟨x, rfl⟩,
      Subspace.mem_range.mpr ⟨y, ?_⟩⟩
    apply Subspace.injective V
    simpa only [Subspace.Ψ] using hy.trans hx.symm
private lemma ἶ {α η ι : Type*}
    [Β (η → α)] [Β (ι → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (η → α)) :
    ((A.map ⟨V, Subspace.injective V⟩).dens : ℝ) =
      (A.dens : ℝ) * ((Subspace.range V).dens : ℝ) := by
  simp only [Finset.nnratCast_dens, Subspace.range, Finset.card_map]
  rw [Finset.card_image_iff.mpr (Subspace.injective V).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · let : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hA : A = ∅ := Subsingleton.elim _ _
    rw [hA]
    simp
  · field_simp
    simp only [Finset.card_univ]
def Ν (k r m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ (_ : 1 ≤ r), ∀ ᾑ : r ≤ k,
    ∀ D : Fin r → Finset (Fin n → Fin (k + 1)),
    (∀ i, Γ (Fin.castLE ᾑ i).castSucc (Fin.last k) (D i)) →
    2 * r * β ≤ ((intersection D).dens : ℝ) →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.Ι V (intersection D)) ∧
      (𝒱.PairwiseDisjoint λ V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((Η (intersection D) 𝒱).dens : ℝ) < 2 * r * β
private lemma ἡ {k m n : ℕ} {β : ℝ}
    (h : Ç k m β n) :
    Ν k 1 m β n := by
  intro _ ᾑ D hD hDβ
  have ê : intersection D = D 0 := by
    ext x
    simp only [Φ]
    constructor
    · intro hx
      exact hx 0
    · intro hx i
      simpa only [Fin.eq_zero i] using hx
  have hsensitive :
      Γ (Fin.castLE ᾑ 0).castSucc (Fin.last k) (D 0) :=
    hD 0
  obtain ⟨𝒱, hfinite, ς, Χ, μ⟩ :=
    h (Fin.castLE ᾑ 0) (D 0) hsensitive (by
      rw [ê] at hDβ
      norm_num at hDβ ⊢
      exact hDβ)
  refine ⟨𝒱, hfinite, ?_, Χ, ?_⟩
  · simpa only [ê] using ς
  · rw [ê]
    norm_num
    exact μ
private lemma ἲ {k M n : ℕ} {β : ℝ} (hβ₀ : 0 < β)
    (𝒱 : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)))
    (hfinite : 𝒱.Finite)
    (Χ : 𝒱.PairwiseDisjoint λ V ↦
      (Subspace.range V : Set (Fin n → Fin (k + 1))))
    (localError : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) →
      Finset (Fin M → Fin (k + 1)))
    (hlocal : ∀ V, ((localError V).dens : ℝ) ≤ 2 * β) :
    let outer := hfinite.toFinset
    let errors := outer.biUnion λ V ↦
      (localError V).map ⟨V, Subspace.injective V⟩
    (errors.dens : ℝ) ≤ 2 * β := by
  classical
  dsimp only
  let outer := hfinite.toFinset
  let innerError := λ V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    (localError V).map ⟨V, Subspace.injective V⟩
  have ῌ : (outer : Set _).PairwiseDisjoint innerError := by
    intro V hV V' hV' hVV
    change Disjoint (innerError V) (innerError V')
    rw [Finset.disjoint_left]
    intro w hw ῢ
    apply Set.disjoint_left.mp (Χ
      (by simpa [outer] using hV) (by simpa [outer] using hV') hVV)
    · obtain ⟨x, _hx, hxw⟩ := Finset.mem_map.mp hw
      exact Subspace.mem_range.mpr ⟨x, hxw⟩
    · obtain ⟨x', _hx', hx'w⟩ := Finset.mem_map.mp ῢ
      exact Subspace.mem_range.mpr ⟨x', hx'w⟩
  rw [Finset.dens_biUnion ῌ]
  change (NNRat.castHom ℝ) (∑ V ∈ outer, (innerError V).dens) ≤ 2 * β
  rw [map_sum (NNRat.castHom ℝ)]
  have hsummand (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      ((innerError V).dens : ℝ) ≤ 2 * β * ((Subspace.range V).dens : ℝ) := by
    dsimp only [innerError]
    rw [ἶ]
    exact mul_le_mul_of_nonneg_right (hlocal V) (by positivity)
  apply (Finset.sum_le_sum λ V _ ↦ hsummand V).trans
  rw [← Finset.mul_sum]
  have Ὰ : (outer : Set _).PairwiseDisjoint
      (λ V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
        Subspace.range V) := by
    intro V hV V' hV' hVV
    change Disjoint (Subspace.range V) (Subspace.range V')
    rw [Finset.disjoint_left]
    intro w hw ῢ
    exact Set.disjoint_left.mp (Χ
      (by simpa [outer] using hV) (by simpa [outer] using hV') hVV) hw ῢ
  have hsum : (∑ V ∈ outer, ((Subspace.range V).dens : ℝ)) ≤ 1 := by
    have Ῥ : (((outer.biUnion Subspace.range).dens : ℚ≥0) : ℝ) =
        ∑ V ∈ outer, ((Subspace.range V).dens : ℝ) := by
      rw [Finset.dens_biUnion Ὰ]
      change (NNRat.castHom ℝ) (∑ V ∈ outer, (Subspace.range V).dens) = _
      rw [map_sum (NNRat.castHom ℝ)]
      rfl
    rw [← Ῥ]
    exact_mod_cast Finset.dens_le_one (s := outer.biUnion Subspace.range)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hβ₀.le)
private lemma ἥ {k r m M n : ℕ}
    (D : Fin r.succ → Finset (Fin n → Fin (k + 1)))
    (D₀ : Fin r → Finset (Fin n → Fin (k + 1)))
    (ᾄ : intersection D ⊆ intersection D₀)
    (𝒱 : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)))
    (hfinite : 𝒱.Finite)
    (tiles : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) →
      Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M))) :
    let pullback := λ V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
      Í V (D (Fin.last r))
    let global := ⋃ V : 𝒱, Subspace.compose V.val '' tiles V
    let errors := hfinite.toFinset.biUnion λ V ↦
      (Η (pullback V) (tiles V)).map ⟨V, Subspace.injective V⟩
    Η (intersection D) global ⊆ Η (intersection D₀) 𝒱 ∪ errors := by
  classical
  dsimp only
  intro w hw
  simp only [Η, Finset.mem_filter] at hw
  simp only [Η, Finset.mem_filter, Finset.mem_union]
  by_cases hparent : ∃ V ∈ 𝒱, w ∈ Subspace.range V
  · right
    obtain ⟨V, hV, hwV⟩ := hparent
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hwV
    refine Finset.mem_biUnion.mpr ⟨V, by simpa using hV, ?_⟩
    apply Finset.mem_map.mpr
    refine ⟨x, ?_, hx⟩
    simp only [Finset.mem_filter]
    constructor
    · simp only [Í, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx ▸ (Φ.mp hw.1 (Fin.last r))
    · intro W hW hxW
      apply hw.2 (Subspace.compose V W)
      · exact Set.mem_iUnion_of_mem ⟨V, hV⟩ <|
          Set.mem_image_of_mem (Subspace.compose V) hW
      · obtain ⟨y, hy⟩ := Subspace.mem_range.mp hxW
        exact Subspace.mem_range.mpr ⟨y, by rw [Subspace.Ψ, hy, hx]⟩
  · left
    refine ⟨ᾄ hw.1, ?_⟩
    intro V hV hwV
    exact hparent ⟨V, hV, hwV⟩
private lemma ὠ {k r m M n : ℕ}
    (D : Fin (r + 1) → Finset (Fin n → Fin (k + 1)))
    (D₀ : Fin r → Finset (Fin n → Fin (k + 1)))
    (hD₀ : ∀ i, D₀ i = D (Fin.castSucc i))
    (𝒱 : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)))
    (hfinite : 𝒱.Finite)
    (ς : ∀ V ∈ 𝒱, Subspace.Ι V (intersection D₀))
    (Χ : 𝒱.PairwiseDisjoint λ V ↦
      (Subspace.range V : Set (Fin n → Fin (k + 1))))
    (tiles : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) →
      Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M)))
    (ᾉ : ∀ V,
      (Subspace.compose V '' tiles V).Finite ∧
      (∀ U ∈ Subspace.compose V '' tiles V,
        Subspace.Ι U (D (Fin.last r))) ∧
      ((Subspace.compose V '' tiles V).PairwiseDisjoint λ U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1))))) :
    let global := ⋃ V : 𝒱, Subspace.compose V.val '' tiles V
    global.Finite ∧
      (∀ U ∈ global, Subspace.Ι U (intersection D)) ∧
      (global.PairwiseDisjoint λ U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) := by
  classical
  let : Finite 𝒱 := hfinite
  dsimp only
  refine ⟨Set.finite_iUnion λ V ↦ (ᾉ V).1, ?_, ?_⟩
  · intro U hU x
    simp only [Set.mem_iUnion] at hU
    obtain ⟨V, W, hW, rfl⟩ := hU
    rw [Φ]
    intro i
    refine Fin.lastCases ?_ ?_ i
    · exact (ᾉ V).2.1 (Subspace.compose V W)
        (Set.mem_image_of_mem (Subspace.compose V.val) hW) x
    · intro j
      have hx := ς V V.prop (W x)
      rw [Φ] at hx
      simpa only [Subspace.Ψ, hD₀ j] using hx j
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' ῲ ὅ
    simp only [Set.mem_iUnion] at hU ῲ
    obtain ⟨V, hU⟩ := hU
    obtain ⟨V', ῲ⟩ := ῲ
    have hVV : V = V' := by
      apply Subtype.ext
      apply Set.pairwiseDisjoint_iff.mp Χ V.prop V'.prop
      obtain ⟨w, hw, ῢ⟩ := ὅ
      obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
      obtain ⟨x', hx'⟩ := Subspace.mem_range.mp ῢ
      obtain ⟨W, hW, rfl⟩ := hU
      obtain ⟨W', hW', rfl⟩ := ῲ
      refine ⟨V.val (W x), Subspace.mem_range.mpr ⟨W x, rfl⟩,
        Subspace.mem_range.mpr ⟨W' x', ?_⟩⟩
      simpa only [Subspace.Ψ] using hx'.trans hx.symm
    subst V'
    exact Set.pairwiseDisjoint_iff.mp (ᾉ V).2.2 hU ῲ ὅ
private lemma Ὑ {k r m M n : ℕ}
    (hr₀ : 1 ≤ r) (ᾑ : r + 1 ≤ k) {β : ℝ} (hβ₀ : 0 < β)
    (houter : Ν k r M β n)
    (ᾉ : Ç k m β M) :
    Ν k (r + 1) m β n := by
  intro _ hrk' D hD hDβ
  let D₀ : Fin r → Finset (Fin n → Fin (k + 1)) := λ i ↦
    D (Fin.castSucc i)
  have ᾄ : intersection D ⊆ intersection D₀ := by
    intro x hx
    rw [Φ] at hx ⊢
    intro i
    simpa only [D₀] using hx (Fin.castSucc i)
  have hD₀ (i : Fin r) :
      Γ (Fin.castLE (by omega) i).castSucc (Fin.last k) (D₀ i) := by
    have hindex : Fin.castLE hrk' (Fin.castSucc i) = Fin.castLE (by omega) i := by
      apply Fin.ext
      rfl
    rw [← hindex]
    simpa only [D₀] using hD (Fin.castSucc i)
  obtain ⟨𝒱, hfinite, ς, Χ, μ⟩ :=
    houter hr₀ (by omega) D₀ hD₀ (by
        apply le_trans (b := 2 * ((r : ℝ) + 1) * β)
        · nlinarith
        · have hdens : ((intersection D).dens : ℝ) ≤ ((intersection D₀).dens : ℝ) := by
            exact_mod_cast Finset.dens_mono ᾄ
          convert hDβ.trans hdens using 1
          norm_num)
  let iLast : Fin k := ⟨r, by omega⟩
  let DLast := D (Fin.last r)
  have hLast : Γ iLast.castSucc (Fin.last k) DLast := by
    convert hD (Fin.last r) using 1
    simp only [iLast, Fin.castLE, Fin.last, Fin.castSucc]
  let pullback := λ V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    Í V DLast
  have hPullback (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      Γ iLast.castSucc (Fin.last k) (pullback V) :=
    Ἠ V DLast hLast
  have existsInner (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      ∃ 𝒲 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M)),
        𝒲.Finite ∧
        (∀ W ∈ 𝒲, Subspace.Ι W (pullback V)) ∧
        (𝒲.PairwiseDisjoint λ W ↦
          (Subspace.range W : Set (Fin M → Fin (k + 1)))) ∧
        ((Η (pullback V) 𝒲).dens : ℝ) < 2 * β := by
    by_cases hV : 2 * β ≤ ((pullback V).dens : ℝ)
    · exact ᾉ iLast (pullback V) (hPullback V) hV
    · refine ⟨∅, Set.finite_empty, ?_, Set.pairwiseDisjoint_empty, ?_⟩
      · simp
      · have μ : Η (pullback V)
            (∅ : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M))) = pullback V := by
          simp [Η]
        rw [μ]
        exact lt_of_not_ge hV
  choose tiles Ὺ ῄ Ῐ ῤ using existsInner
  let composed := λ V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    Subspace.compose V '' tiles V
  have hcomposed (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      (composed V).Finite ∧
      (∀ U ∈ composed V, Subspace.Ι U DLast) ∧
      ((composed V).PairwiseDisjoint λ U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) := by
    exact ὡ DLast V (tiles V)
      (Ὺ V) (ῄ V) (Ῐ V)
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ V : 𝒱, composed V
  obtain ⟨ἆ, æ, ë⟩ :=
    ὠ D D₀ (λ _ ↦ rfl) 𝒱 hfinite
      ς Χ tiles (λ V ↦ by simpa only [composed] using hcomposed V)
  refine ⟨global, ?_, ?_, ?_, ?_⟩
  · simpa only [global, composed] using ἆ
  · simpa only [global, composed] using æ
  · simpa only [global, composed] using ë
  · let outer := hfinite.toFinset
    let innerError := λ V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
      (Η (pullback V) (tiles V)).map ⟨V, Subspace.injective V⟩
    let errors := outer.biUnion innerError
    have herrors : (errors.dens : ℝ) ≤ 2 * β := by
      simpa only [errors, outer, innerError] using
        ἲ hβ₀ 𝒱 hfinite Χ
          (λ V ↦ Η (pullback V) (tiles V))
          (λ V ↦ (ῤ V).le)
    have ᾯ :
        Η (intersection D) global ⊆
          Η (intersection D₀) 𝒱 ∪ errors := by
      simpa only [global, composed, errors, outer, innerError, pullback, DLast] using
        ἥ D D₀ ᾄ 𝒱 hfinite tiles
    have hdens :
        ((Η (intersection D) global).dens : ℝ) ≤
          ((Η (intersection D₀) 𝒱 ∪ errors).dens : ℝ) := by
      exact_mod_cast Finset.dens_mono ᾯ
    have hdens_union :
        ((Η (intersection D₀) 𝒱 ∪ errors).dens : ℝ) ≤
          ((Η (intersection D₀) 𝒱).dens : ℝ) + (errors.dens : ℝ) := by
      exact_mod_cast Finset.dens_union_le (Η (intersection D₀) 𝒱) errors
    apply hdens.trans_lt
    apply lt_of_le_of_lt hdens_union
    convert add_lt_add_of_lt_of_le μ herrors using 1
    push_cast
    ring
lemma é (k r m : ℕ) (Μ : Ζ k)
    (hr₀ : 1 ≤ r) (ᾑ : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, Ν k r m β N := by
  induction r using Nat.strong_induction_on generalizing m with
  | h r ih =>
      obtain rfl | hr := r
      · omega
      obtain rfl | s := hr
      · obtain ⟨N, hN⟩ := Ý k m Μ hm hβ₀
        exact ⟨N, ἡ hN⟩
      · let M := max 1 (ᾇ k m β)
        have hM : 1 ≤ M := le_max_left _ _
        obtain ⟨N, houter⟩ :=
          ih (s + 1) (by omega) M (by omega) (by omega) hM
        have ᾉ : Ç k m β M :=
          ᾶ k m M Μ hm hβ₀ (le_max_right _ _)
        exact ⟨N, Ὑ (by omega) (by omega) hβ₀ houter ᾉ⟩
private lemma ἑ {k r m N n : ℕ} {β : ℝ}
    (hN : Ν k r m β N) (hNn : N ≤ n) :
    Ν k r m β n := by
  classical
  intro hr₀ ᾑ D hD hDβ
  let q := n - N
  have hNq : N + q = n := Nat.add_sub_of_le hNn
  let e : Fin q ⊕ Fin N ≃ Fin n :=
    (Equiv.sumComm (Fin q) (Fin N)).trans <| finSumFinEquiv.trans (finCongr hNq)
  let wordEquiv := e.arrowCongr (Equiv.refl (Fin (k + 1)))
  let D' := λ i ↦ (D i).map wordEquiv.symm.toEmbedding
  let slice := λ z : Fin q → Fin (k + 1) ↦ λ i ↦ fiber (D' i) z
  have ῼ (z : Fin q → Fin (k + 1)) (i : Fin r) :
      Γ (Fin.castLE ᾑ i).castSucc (Fin.last k) (slice z i) := by
    intro x y ô
    simp only [slice, τ, D', Finset.mem_map_equiv]
    apply hD i
    intro a ῐ hal c
    cases hc : e.symm c with
    | inl j =>
        simp [wordEquiv, Equiv.arrowCongr, hc]
    | inr j =>
        simpa [wordEquiv, Equiv.arrowCongr, hc] using
          ô a ῐ hal j
  let I := intersection D
  let I' := I.map wordEquiv.symm.toEmbedding
  have hIdens : (I'.dens : ℝ) = (I.dens : ℝ) := by
    simp only [I', Finset.dens_map_equiv]
  have hfiberI (z : Fin q → Fin (k + 1)) :
      fiber I' z = intersection (slice z) := by
    ext y
    simp only [τ, Finset.mem_map_equiv, I', I, Φ, slice, D',
      Equiv.symm_symm]
  have existsLocal (z : Fin q → Fin (k + 1)) :
      ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N)),
        𝒱.Finite ∧
        (∀ V ∈ 𝒱, Subspace.Ι V (intersection (slice z))) ∧
        (𝒱.PairwiseDisjoint λ V ↦
          (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
        ((Η (intersection (slice z)) 𝒱).dens : ℝ) < 2 * r * β := by
    by_cases hz : 2 * r * β ≤ ((intersection (slice z)).dens : ℝ)
    · exact hN hr₀ ᾑ (slice z) (ῼ z) hz
    · refine ⟨∅, Set.finite_empty, ?_, Set.pairwiseDisjoint_empty, ?_⟩
      · simp
      · have μ : Η (intersection (slice z))
            (∅ : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N))) =
              intersection (slice z) := by
          simp [Η]
        rw [μ]
        exact lt_of_not_ge hz
  choose tiles ὸ Ἲ ὐ ἄ using existsLocal
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ z, À e z '' tiles z
  obtain ⟨ἆ, æ, ë⟩ := ὒ e I tiles
    ὸ
    (λ z V hV ↦ by
      have h := Ἲ z V hV
      rw [← hfiberI z] at h
      simpa only [I'] using h)
    ὐ
  refine ⟨global, ἆ, ?_, ë, ?_⟩
  · simpa only [I, Φ] using æ
  · let E := (Η I global).map wordEquiv.symm.toEmbedding
    have Ἤ (z : Fin q → Fin (k + 1)) :
        fiber E z = Η (intersection (slice z)) (tiles z) := by
      rw [← hfiberI z]
      simpa only [E, global, I', wordEquiv] using Ἔ e I tiles z
    have hEdens :
        (E.dens : ℝ) = ((Η I global).dens : ℝ) := by
      simp only [E, Finset.dens_map_equiv]
    rw [← hEdens, ← σ]
    apply Finset.expect_lt
    · intro z _
      rw [Ἤ]
      exact (ἄ z).le
    · let z : Fin q → Fin (k + 1) := λ _ ↦ 0
      refine ⟨z, Finset.mem_univ z, ?_⟩
      rw [Ἤ]
      exact ἄ z
lemma Æ (k r m : ℕ) (Μ : Ζ k)
    (hr₀ : 1 ≤ r) (ᾑ : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, ∀ n ≥ N, Ν k r m β n := by
  obtain ⟨N, hN⟩ :=
    é k r m Μ hr₀ ᾑ hm hβ₀
  exact ⟨N, λ _n hn ↦ ἑ hN hn⟩
noncomputable def Τ (k r m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : Ζ k ∧ 1 ≤ r ∧ r ≤ k ∧ 1 ≤ m ∧ 0 < β then
    Nat.find (Æ
      k r m h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 0
lemma ὃ (k r m n : ℕ) (Μ : Ζ k)
    (hr₀ : 1 ≤ r) (ᾑ : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β)
    (hn : Τ k r m β ≤ n) :
    Ν k r m β n := by
  classical
  rw [Τ,
    dif_pos ⟨Μ, hr₀, ᾑ, hm, hβ₀⟩] at hn
  exact Nat.find_spec
    (Æ k r m Μ hr₀ ᾑ hm hβ₀) n hn
lemma exists_disjoint_subspaces_iInter {k : ℕ} (r m n : ℕ) (Μ : Ζ k)
    (hr₀ : 1 ≤ r) (ᾑ : r ≤ k) (hm : 1 ≤ m)
    (β : ℝ) (hβ₀ : 0 < β)
    (hn : Τ k r m β ≤ n)
    (D : Fin r → Finset (Fin n → Fin (k + 1)))
    (hD : ∀ i, Γ (Fin.castLE ᾑ i).castSucc (Fin.last k) (D i))
    (hDβ : 2 * r * β ≤ ((intersection D).dens : ℝ)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.Ι V (intersection D)) ∧
      (𝒱.PairwiseDisjoint λ V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((Η (intersection D) 𝒱).dens : ℝ) < 2 * r * β := by
  exact ὃ k r m n Μ hr₀ ᾑ hm hβ₀ hn
    hr₀ ᾑ D hD hDβ
end Γ
end Δ
end
section
open Finset
open Combinatorics
open scoped BigOperators
namespace Δ
def Ἕ {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ∃ a, l a ∉ A
def pullback {η α ι : Type*} [Β (η → α)] [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι → α)) : Finset (η → α) :=
  Finset.univ.filter λ x ↦ V x ∈ A
noncomputable def ἀ (k m : ℕ) (δ : ℝ) : ℕ :=
  max m (Parameters.m₀ k δ)
noncomputable def ó (k m : ℕ) (δ : ℝ) : ℕ :=
  max 1 (Ñ.bound (k + 1) 2 (ἀ k m δ))
noncomputable def Ἧ (k m : ℕ) (δ : ℝ) : ℕ :=
  Subspace.variableCutFibersBound (k + 1) (ó k m δ)
    (Parameters.η k δ ^ 2 / 2)
lemma ì {k M L : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ)
    {ι κ : Type*} [Finite ι] [Β (κ → Fin (k + 1))]
    [Β (ι ⊕ κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (hGR : Ñ.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (ᾃ : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
      ((∀ l : Combinatorics.Line (Fin k) (Fin M),
          Parameters.θ k δ ≤
            ((Finset.univ.filter λ y ↦
              ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
        (∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter λ y ↦
            ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ)) := by
  let : Nontrivial (Fin (k + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  let ε := Parameters.η k δ ^ 2 / 2
  have hε₀ : 0 < ε := by
    dsimp only [ε]
    positivity [Parameters.η_pos hk hδ₀]
  by_cases hM : 1 ≤ M
  · have hL : 1 ≤ L := by
      by_contra hL
      obtain rfl : L = 0 := by omega
      obtain ⟨R, _⟩ :=
        Ñ.lines_twoColor (Fin (k + 1)) M 0
          (by simpa only [Fintype.card_fin] using hGR) ∅
      obtain ⟨i, _⟩ := R.proper ⟨0, hM⟩
      exact Fin.elim0 i
    obtain ⟨U, hU⟩ := ᾃ hL
    let : Β (Combinatorics.Line (Fin (k + 1)) (Fin L)) :=
      Subspace.lineFintype (k + 1) L
    let goodLines :=
      Finset.univ.filter λ q : Combinatorics.Line (Fin (k + 1)) (Fin L) ↦
        Parameters.θ k δ ≤
          ((Finset.univ.filter λ y ↦
            ∀ a : Fin k, Sum.elim (U (q a.castSucc)) y ∈ A).dens : ℝ)
    obtain ⟨R, ἅ | hbad⟩ :=
      Ñ.lines_twoColor (Fin (k + 1)) M L
        (by simpa only [Fintype.card_fin] using hGR) goodLines
    · refine ⟨Subspace.compose U R, ?_, Or.inl ?_⟩
      · intro x
        rw [Subspace.Ψ]
        have hx := hU (R x)
        linarith
      · intro l
        have hl := ἅ (l.map Fin.castSucc)
        simpa only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply,
          Subspace.Ψ] using hl
    · refine ⟨Subspace.compose U R, ?_, Or.inr ?_⟩
      · intro x
        rw [Subspace.Ψ]
        have hx := hU (R x)
        linarith
      · intro l
        have hl := hbad (l.map Fin.castSucc)
        simp only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply] at hl
        simpa only [Subspace.Ψ] using lt_of_not_ge hl
  · have hM₀ : M = 0 := by omega
    subst M
    let : Β (ι → Fin (k + 1)) := Fintype.ofFinite _
    have havg :
        δ ≤ 𝔼 x : ι → Fin (k + 1), ((fiber A x).dens : ℝ) := by
      simpa only [σ] using hA
    obtain ⟨x, _, hx⟩ :=
      Finset.exists_le_of_le_expect Finset.univ_nonempty havg
    let W : Combinatorics.Subspace (Fin 0) (Fin (k + 1)) ι := {
      idxFun := λ i ↦ Sum.inl (x i)
      proper := λ e ↦ Fin.elim0 e
    }
    refine ⟨W, ?_, Or.inl ?_⟩
    · intro z
      have hW : W z = x := by
        funext i
        simp only [W, Combinatorics.Subspace.coe_apply, Sum.elim_inl, id_eq]
      rw [hW]
      dsimp only [ε] at hε₀
      linarith
    · intro l
      exact Fin.elim0 l.proper.choose
lemma Ἅ {k m M : ℕ} (hm : 1 ≤ m) (Ὴ : m ≤ M)
    {δ : ℝ} {ι κ : Type*} [Β (κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (Ἆ : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ))
    (ὕ : ∀ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter λ y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter λ y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  let R := Subspace.repeatInitial (Fin (k + 1)) hm Ὴ
  let V := Subspace.compose W R
  refine ⟨V, ?_, ?_⟩
  · intro x
    dsimp only [V]
    rw [Subspace.Ψ]
    exact Ἆ (R x)
  · intro l
    let Rk := Subspace.repeatInitial (Fin k) hm Ὴ
    simpa only [V, R, Rk, Subspace.Ψ, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using
        ὕ (Subspace.φ Rk l)
lemma è {k M L : ℕ} (hk : 2 ≤ k)
    (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ)
    {ι κ : Type*} [Finite ι] [Β (κ → Fin (k + 1))]
    [Β (ι ⊕ κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (Ὴ : m ≤ M) (hm₀M : Parameters.m₀ k δ ≤ M)
    (hGR : Ñ.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ))
    (ᾃ : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter λ y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
      ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
        ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
          (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin M),
            ((Finset.univ.filter λ y ↦
              ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
                Parameters.θ k δ := by
  obtain ⟨W, Ἆ, ἅ | ᾝ⟩ :=
    ì hk hδ₀ hGR A hA ᾃ
  · exact Or.inl <|
      Ἅ hm Ὴ A W Ἆ ἅ
  · exact Or.inr ⟨M, hm₀M, W, Ἆ, ᾝ⟩
lemma ἤ {k M : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Β (κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (Ἆ : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    δ / 4 ≤
      ((Finset.univ.filter λ y : κ → Fin (k + 1) ↦
        δ / 4 ≤
          ((Finset.univ.filter λ x : Fin M → Fin k ↦
            Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let f := λ y : κ → Fin (k + 1) ↦
    ((Finset.univ.filter λ x : Fin M → Fin k ↦
      Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hη₀ := Parameters.η_pos hk hδ₀
  have hηδ := Parameters.η_le_δ_div_six k δ
  have havg : δ - Parameters.η k δ ^ 2 / 2 ≤
      Finset.expect Finset.univ f := by
    rw [Subspace.average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty λ x _ ↦
      Ἆ (Fin.castSucc ∘ x)
  have ᾚ := ß f
    (δ - Parameters.η k δ ^ 2 / 2) (δ / 4)
    (λ y ↦ by
      dsimp only [f]
      exact_mod_cast Finset.dens_le_one)
    (by nlinarith [sq_nonneg δ]) havg
  refine (le_div_iff₀ (by linarith : 0 < 1 - δ / 4)).mpr ?_ |>.trans ᾚ
  nlinarith [sq_nonneg δ]
lemma Ἀ {k M : ℕ} (hk : 2 ≤ k)
    (Μ : Ζ k) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hM : Parameters.m₀ k δ ≤ M)
    {ι κ : Type*} [Β (κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (Ἆ : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter λ y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  classical
  let q := Parameters.m₀ k δ
  have hq₀ : 0 < q := Parameters.m₀_pos k δ
  let R := Subspace.repeatInitial (Fin (k + 1)) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  let W₀ := Subspace.compose W R
  have hW₀ : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W₀ x)).dens : ℝ) := by
    intro x
    simpa only [W₀, Subspace.Ψ] using Ἆ (R x)
  have hdense := ἤ hk hδ₀ hδ₁ A W₀ hW₀
  let := Subspace.lineFintype k q
  let B := Finset.univ.filter λ y : κ → Fin (k + 1) ↦
    δ / 4 ≤
      ((Finset.univ.filter λ x : Fin q → Fin k ↦
        Sum.elim (W₀ (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hB : δ / 4 ≤ (B.dens : ℝ) := by
    simpa only [B] using hdense
  have hBne : B.Nonempty := by
    apply Finset.dens_pos.mp
    exact_mod_cast lt_of_lt_of_le (by linarith : 0 < δ / 4) hB
  have hbound : Subspace.ο k (δ / 4) ≤ q := by
    dsimp only [q]
    rw [Subspace.ο, dif_pos ⟨by linarith, Μ⟩,
      Parameters.m₀, dif_pos ⟨hδ₀, Μ⟩]
    omega
  have existsLine (y : κ → Fin (k + 1)) (hy : y ∈ B) :
      ∃ l : Combinatorics.Line (Fin k) (Fin q),
        ∀ a, Sum.elim (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    let S := Finset.univ.filter λ x : Fin q → Fin k ↦
      Sum.elim (W₀ (Fin.castSucc ∘ x)) y ∈ A
    obtain ⟨l, hl⟩ :=
      Subspace.densityOneBound_spec Μ (δ / 4) (by linarith) q hbound S <|
        Subspace.card_le_of_density_le (by omega) (δ / 4) S
          (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, S] using hy)
    exact ⟨l, λ a ↦ by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hl a⟩
  choose lineAt ῥ using λ y : {y // y ∈ B} ↦ existsLine y y.2
  let l₀ := lineAt ⟨hBne.choose, hBne.choose_spec⟩
  let : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let f : (κ → Fin (k + 1)) → Combinatorics.Line (Fin k) (Fin q) := λ y ↦
    if hy : y ∈ B then lineAt ⟨y, hy⟩ else l₀
  obtain ⟨l, hl⟩ := Subspace.exists_fiber_density B f
  have ὅ :
      (B.filter λ y ↦ f y = l) ⊆
        Finset.univ.filter λ y ↦
          ∀ a, Sum.elim (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have ᾱ : lineAt ⟨y, hy.1⟩ = l := by
      simpa only [f, dif_pos hy.1] using hy.2
    intro a
    rw [← ᾱ]
    exact ῥ ⟨y, hy.1⟩ a
  have þ :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ q - (k : ℝ) ^ q := by
    rw [Subspace.card_line k q (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) q
  have hθ :
      Parameters.θ k δ ≤
        (B.dens : ℝ) / Fintype.card (Combinatorics.Line (Fin k) (Fin q)) := by
    unfold Parameters.θ
    rw [← þ]
    exact div_le_div_of_nonneg_right hB (by positivity)
  let Rk := Subspace.repeatInitial (Fin k) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  refine ⟨Subspace.φ Rk l, hθ.trans (hl.trans ?_)⟩
  exact_mod_cast Finset.dens_le_dens <| by
    simpa only [W₀, R, Rk, Subspace.Ψ, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using ὅ
lemma â {k : ℕ} (hk : 2 ≤ k)
    (Μ : Ζ k) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Β (κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    ¬ ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
      ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
        (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
        ∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter λ y ↦
            ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ := by
  rintro ⟨M, hM, W, Ἆ, ᾝ⟩
  obtain ⟨l, hl⟩ :=
    Ἀ hk Μ hδ₀ hδ₁ hM A W Ἆ
  exact (not_lt_of_ge hl) (ᾝ l)
lemma ἓ {k M L : ℕ} (hk : 2 ≤ k)
    (Μ : Ζ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Finite ι] [Β (κ → Fin (k + 1))]
    [Β (ι ⊕ κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (Ὴ : m ≤ M) (hm₀M : Parameters.m₀ k δ ≤ M)
    (hGR : Ñ.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ))
    (ᾃ : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter λ y ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  obtain hV | ᾝ :=
    è hk m hm δ hδ₀ Ὴ hm₀M hGR A hA ᾃ
  · exact hV
  · exact (â hk Μ δ hδ₀ hδ₁ A
      ᾝ).elim
def ξ {α η ι κ : Type*} [Β (η → α)]
    [Α (ι ⊕ κ → α)] (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι ⊕ κ → α)) (y : κ → α) : Finset (η → α) :=
  Finset.univ.filter λ x ↦ Sum.elim (V x) y ∈ A
def Õ {k m : ℕ} {ι κ : Type*}
    [Β (Combinatorics.Line (Fin k) (Fin m))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (y : κ → Fin (k + 1)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  Finset.univ.filter λ l ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A
def Subspace.fixSuffix {α η ι κ : Type*} (V : Combinatorics.Subspace η α ι)
    (y : κ → α) : Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun := Sum.elim V.idxFun (Sum.inl ∘ y)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩
def Subspace.fixSuffixReindex {α η ι κ ζ : Type*} (e : ι ⊕ κ ≃ ζ)
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α ζ :=
  (Subspace.fixSuffix V y).reindex (Equiv.refl _) (Equiv.refl _) e
lemma Ὅ {α η ι κ : Type*} [Nonempty α] [Β (η → α)]
    [Β (κ → α)] [Α (ι ⊕ κ → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) (r : ℝ)
    (hV : ∀ x, r ≤ ((fiber A (V x)).dens : ℝ)) :
    r ≤ 𝔼 y : κ → α, ((ξ V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) =
      𝔼 y : κ → α, ((ξ V A y).dens : ℝ) := by
    calc
      𝔼 x : η → α, ((fiber A (V x)).dens : ℝ)
          = 𝔼 x : η → α, 𝔼 y : κ → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        simp
      _ = 𝔼 y : κ → α, 𝔼 x : η → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (η → α)) (Finset.univ : Finset (κ → α))]
      _ = 𝔼 y : κ → α, 𝔼 x : η → α,
          (Set.indicator (ξ V A y) (1 : (η → α) → ℝ) x : ℝ) := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro x _
        by_cases h : Sum.elim (V x) y ∈ A
        · have hy : y ∈ fiber A (V x) := by simpa [fiber] using h
          have hx : x ∈ ξ V A y := by
            dsimp [ξ]
            simp [h]
          simp [hy, hx]
        · have hy : y ∉ fiber A (V x) := by simpa [fiber] using h
          have hx : x ∉ ξ V A y := by
            dsimp [ξ]
            simp [h]
          simp [hy, hx]
      _ = 𝔼 y : κ → α, ((ξ V A y).dens : ℝ) := by
        simp
  have h_r_le_expect : r ≤ 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := η → α)) λ x _ => hV x
  exact h_r_le_expect.trans h_expect_eq.le
lemma ᾕ {X : Type*} [Β X] [Nonempty X]
    (f : X → ℝ) (δ η : ℝ) (hη₀ : 0 < η)
    (havg : δ - η ^ 2 / 2 ≤ 𝔼 x : X, f x)
    (ᾷ : ∀ x, f x < δ + η ^ 2 / 2) :
    1 - η ≤ ((Finset.univ.filter λ x ↦ δ - 2 * η ≤ f x).dens : ℝ) := by
  set H := Finset.univ.filter λ x ↦ δ - 2 * η ≤ f x
  by_cases hH : 1 - η ≤ (H.dens : ℝ)
  · exact hH
  · exfalso
    have hfg : ∀ x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η)
        * (Set.indicator H (1 : X → ℝ) x : ℝ) := by
      intro x
      by_cases hxH : x ∈ H
      · rw [Set.indicator_of_mem (by simpa using hxH), Pi.one_apply, mul_one]
        linarith [ᾷ x]
      · rw [Set.indicator_of_notMem (by simpa using hxH), mul_zero, add_zero]
        have : ¬(δ - 2 * η ≤ f x) := by simpa [H] using hxH
        linarith
    have hexpect : 𝔼 x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) := by
      apply (Finset.expect_le_expect λ x _ ↦ hfg x).trans_eq
      rw [Finset.expect_add_distrib, Finset.expect_const univ_nonempty, ← Finset.mul_expect]
      simp
    linarith [havg, hexpect,
      mul_le_mul_of_nonneg_left (not_le.mp hH).le (by positivity : (0 : ℝ) ≤ η ^ 2 / 2 + 2 * η),
      mul_pos hη₀ hη₀, pow_pos hη₀ 3]
lemma Ὤ {k m : ℕ} {ι κ : Type*}
    [Β (κ → Fin (k + 1))]
    [Β (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (θ : ℝ)
    (hV : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      θ ≤ ((Finset.univ.filter λ y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    θ ≤ 𝔼 y : κ → Fin (k + 1), ((Õ V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter λ y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) =
      𝔼 y : κ → Fin (k + 1), ((Õ V A y).dens : ℝ) := by
    calc
      𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          ((Finset.univ.filter λ y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)
          = 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
            𝔼 y : κ → Fin (k + 1),
            (Set.indicator (Finset.univ.filter λ y ↦
              ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A)
              (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        apply Finset.expect_congr rfl
        intro l _
        rw [← Finset.expect_indicator_one]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (Finset.univ.filter λ y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A)
            (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (Combinatorics.Line (Fin k) (Fin m)))
          (Finset.univ : Finset (κ → Fin (k + 1)))]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (Õ V A y)
            (1 : Combinatorics.Line (Fin k) (Fin m) → ℝ) l : ℝ) := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro l _
        dsimp [Õ]
        by_cases h : ∀ a : Fin k, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A
        · simp [h]
        · simp [h]
      _ = 𝔼 y : κ → Fin (k + 1), ((Õ V A y).dens : ℝ) := by
        simp
  have h_θ_le_expect : θ ≤ 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter λ y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := Combinatorics.Line (Fin k) (Fin m)))
      λ l _ => hV l
  exact h_θ_le_expect.trans h_expect_eq.le
lemma ᾅ {X : Type*} [Β X] [Nonempty X]
    (f : X → ℝ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hf₁ : ∀ x, f x ≤ 1) (havg : θ ≤ 𝔼 x : X, f x) :
    θ / 2 ≤ ((Finset.univ.filter λ x ↦ θ / 2 ≤ f x).dens : ℝ) := by
  refine le_trans ?_
    (ß f θ (θ / 2) hf₁ (by linarith) havg)
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - θ / 2)]
  nlinarith [sq_nonneg (θ / 2)]
lemma ἔ {X : Type*} [Β X]
    (S T : Finset X) (η θ : ℝ)
    (hS : 1 - η ≤ (S.dens : ℝ)) (hT : θ / 2 ≤ (T.dens : ℝ))
    (hηθ : η < θ / 2) : ∃ x, x ∈ S ∧ x ∈ T := by
  classical
  by_contra h
  have hunion : ((S ∪ T).dens : ℝ) = (S.dens : ℝ) + (T.dens : ℝ) := by
    exact_mod_cast Finset.dens_union_of_disjoint
      (Finset.disjoint_left.mpr λ x hxS hxT ↦ h ⟨x, hxS, hxT⟩)
  have hle : ((S ∪ T).dens : ℝ) ≤ 1 := by
    exact_mod_cast Finset.dens_le_one (s := S ∪ T)
  linarith [hunion, hle]
lemma Ὧ {k m : ℕ} (hk : 2 ≤ k)
    [Β (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Β (Fin m → Fin (k + 1))]
    [Β (κ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (Ἤ : ∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ))
    (ὕ : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      Parameters.θ k δ ≤
        ((Finset.univ.filter λ y ↦
          ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    (∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤
      ((ξ V A y).dens : ℝ)) ∨
    ∃ y, δ - 2 * Parameters.η k δ ≤ ((ξ V A y).dens : ℝ) ∧
      Parameters.θ k δ / 2 ≤ ((Õ V A y).dens : ℝ) := by
  classical
  let f := λ y : κ → Fin (k + 1) ↦ ((ξ V A y).dens : ℝ)
  let g := λ y : κ → Fin (k + 1) ↦ ((Õ V A y).dens : ℝ)
  by_cases hinc : ∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤ f y
  · exact Or.inl hinc
  apply Or.inr
  have hη₀ : 0 < Parameters.η k δ := Parameters.η_pos hk hδ₀
  have hη₁ : Parameters.η k δ ≤ 1 :=
    (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  have havgf : δ - Parameters.η k δ ^ 2 / 2 ≤ 𝔼 y, f y := by
    exact Ὅ V A _ Ἤ
  have ᾷ : ∀ y, f y < δ + Parameters.η k δ ^ 2 / 2 := by
    intro y
    exact lt_of_not_ge λ hy ↦ hinc ⟨y, hy⟩
  have hmostly : 1 - Parameters.η k δ ≤
      ((Finset.univ.filter λ y ↦ δ - 2 * Parameters.η k δ ≤ f y).dens : ℝ) := by
    exact ᾕ f δ (Parameters.η k δ) hη₀ havgf ᾷ
  have havgg : Parameters.θ k δ ≤ 𝔼 y, g y := by
    exact Ὤ V A (Parameters.θ k δ) ὕ
  have hmany : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter λ y ↦ Parameters.θ k δ / 2 ≤ g y).dens : ℝ) := by
    refine ᾅ g (Parameters.θ k δ) (Parameters.θ_pos hk hδ₀)
      (Parameters.θ_le_one hk hδ₁) ?_ havgg
    intro y
    dsimp only [g]
    exact_mod_cast Finset.dens_le_one (s := Õ V A y)
  obtain ⟨y, hy₁, hy₂⟩ := ἔ
    (Finset.univ.filter λ y ↦ δ - 2 * Parameters.η k δ ≤ f y)
    (Finset.univ.filter λ y ↦ Parameters.θ k δ / 2 ≤ g y)
    (Parameters.η k δ) (Parameters.θ k δ) hmostly hmany
    (Parameters.η_lt_θ_div_two hk hδ₀)
  refine ⟨y, ?_, ?_⟩
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f] using hy₁
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g] using hy₂
lemma Subspace.fixSuffixReindex_statistics {k m : ℕ} {ι κ ζ : Type*}
    [Β (Fin m → Fin (k + 1))]
    [Β (Combinatorics.Line (Fin k) (Fin m))]
    [Α (ζ → Fin (k + 1))]
    [Α (ι ⊕ κ → Fin (k + 1))]
    (e : ι ⊕ κ ≃ ζ) (A : Finset (ζ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (y : κ → Fin (k + 1)) :
    let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
    (Subspace.Θ (Subspace.fixSuffixReindex e V y) A : ℝ) =
        ((ξ V A' y).dens : ℝ) ∧
      ((Finset.univ.filter λ l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, Subspace.fixSuffixReindex e V y (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) =
        ((Õ V A' y).dens : ℝ) := by
  intro A'
  have Ά (x : Fin m → Fin (k + 1)) :
      (Subspace.fixSuffix V y : (Fin m → Fin (k + 1)) → (ι ⊕ κ → Fin (k + 1))) x
        = Sum.elim (V x) y := by
    ext j
    cases j with
    | inl i =>
      simp [Subspace.fixSuffix, Combinatorics.Subspace.coe_apply]
    | inr k =>
      simp [Subspace.fixSuffix, Combinatorics.Subspace.coe_apply]
  have h_eval (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x = Sum.elim (V x) y ∘ e.symm := by
    calc
      Subspace.fixSuffixReindex e V y x
          = (Subspace.fixSuffix V y) x ∘ e.symm := by
        ext i
        simp [Subspace.fixSuffixReindex, Combinatorics.Subspace.reindex_apply]
      _ = Sum.elim (V x) y ∘ e.symm := by rw [Ά x]
  have ᾲ (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x ∈ A ↔ Sum.elim (V x) y ∈ A' := by
    rw [h_eval x]
    dsimp [A']
    simp [Finset.mem_map_equiv, Equiv.arrowCongr]
  constructor
  · dsimp [Subspace.Θ, ξ]
    congr
    ext x
    simp [ᾲ x]
  · dsimp [Õ]
    congr
    ext l
    constructor
    · intro h a
      rw [← ᾲ (Fin.castSucc ∘ l a)]
      exact h a
    · intro h a
      rw [ᾲ (Fin.castSucc ∘ l a)]
      exact h a
noncomputable def Ú (k m : ℕ) (δ : ℝ) : ℕ :=
  Ἧ k m δ
lemma Ὕ {k : ℕ} (hk : 2 ≤ k) (Μ : Ζ k)
    (m : ℕ) [Β (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (hm : 1 ≤ m) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : Ú k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.Θ V A : ℝ)) ∨
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ - 2 * Parameters.η k δ ≤ (Subspace.Θ V A : ℝ) ∧
      Parameters.θ k δ / 2 ≤
        ((Finset.univ.filter λ l : Combinatorics.Line (Fin k) (Fin m) ↦
          ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) := by
  classical
  have hε₀ : 0 < Parameters.η k δ ^ 2 / 2 := by
    positivity [Parameters.η_pos hk hδ₀]
  obtain ⟨p, q, e, _hq, U, hU⟩ :=
    Subspace.variableCutFibersBound_spec (k + 1) (ó k m δ) n
      (le_max_left _ _) hε₀ (by simpa only [Ú, Ἧ] using hn) A
  let A' := Subspace.Ω e A
  have hA' : δ ≤ (A'.dens : ℝ) := by
    simpa only [A', Subspace.dens_splitWords] using hA
  obtain ⟨W, hWfiber, hWlines⟩ :=
    ἓ hk Μ m hm δ hδ₀ hδ₁
      (ι := Fin p) (κ := Fin q) (M := ἀ k m δ)
      (L := ó k m δ) (le_max_left _ _) (le_max_right _ _)
      (le_max_right _ _) A' hA' (λ _ ↦ ⟨U, λ x ↦ by
        simpa only [A', Subspace.dens_splitWords] using hU x⟩)
  obtain ⟨y, hy⟩ | ⟨y, hy, hylines⟩ :=
    Ὧ hk δ hδ₀ hδ₁ A' W hWfiber hWlines
  · left
    use Subspace.fixSuffixReindex e W y
    rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
    simpa only [A', Subspace.Ω] using hy
  · right
    refine ⟨Subspace.fixSuffixReindex e W y, ?_, ?_⟩
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
      simpa only [A', Subspace.Ω] using hy
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).2]
      simpa only [A', Subspace.Ω] using hylines
end Δ
end
section
open Finset
open Combinatorics
open scoped BigOperators
namespace Δ
lemma Ø {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    ∃ m : ℕ, ((k : ℝ) / (k + 1)) ^ m < Parameters.η k δ := by
  apply exists_pow_lt_of_lt_one (Parameters.η_pos hk hδ₀)
  apply (div_lt_one (by positivity : 0 < (k + 1 : ℝ))).mpr
  norm_num
noncomputable def Λ (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 2 ≤ k ∧ 0 < δ then
    Nat.find (Ø h.1 h.2)
  else 0
lemma ἃ {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hm : Λ k δ ≤ m) :
    ((k : ℝ) / (k + 1)) ^ m ≤ Parameters.η k δ := by
  classical
  rw [Λ, dif_pos ⟨hk, hδ₀⟩] at hm
  refine (pow_le_pow_of_le_one (by positivity) ?_ hm).trans ?_
  · exact (div_le_one (by positivity : 0 < (k + 1 : ℝ))).mpr (by norm_num)
  · exact (Nat.find_spec (Ø hk hδ₀)).le
def Ξ {k m : ℕ} (i : Fin k) (x : Fin m → Fin (k + 1)) :
    Fin m → Fin (k + 1) :=
  λ c ↦ if x c = Fin.last k then i.castSucc else x c
def Ì {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (i : Fin k) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter λ x ↦ V (Ξ i x) ∈ A
def Ρ (k m : ℕ) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter λ x ↦ ∀ c, x c ≠ Fin.last k
lemma ã (k m : ℕ) :
    Ρ k m =
      Finset.univ.map (Function.Embedding.piCongrRight λ _ : Fin m ↦
        (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) := by
  classical
  ext x
  simp only [Ρ, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · intro hx
    let y : Fin m → Fin k := λ c ↦ (x c).castPred (hx c)
    refine ⟨y, ?_⟩
    funext c
    exact Fin.castSucc_castPred (x c) (hx c)
  · rintro ⟨y, rfl⟩ c
    exact Fin.castSucc_ne_last (y c)
lemma ἠ (k m : ℕ) :
    ((Ρ k m).dens : ℝ) = ((k : ℝ) / (k + 1)) ^ m := by
  rw [ã, Finset.nnratCast_dens, Finset.card_map,
    Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
    Fintype.card_pi_const, Fintype.card_fin]
  rw [div_pow]
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
lemma Ὁ {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k) :
    Γ i.castSucc (Fin.last k) (Ì A V i) := by
  intro x y ô
  have hreplace : Ξ i x = Ξ i y := by
    funext c
    by_cases hx : x c = i.castSucc ∨ x c = Fin.last k
    · by_cases hy : y c = i.castSucc ∨ y c = Fin.last k
      · rcases hx with hxi | ὔ
        · rcases hy with ῠ | Ἶ
          · simp [Ξ, hxi, ῠ]
          · simp [Ξ, hxi, Ἶ]
        · rcases hy with ῠ | Ἶ
          · simp [Ξ, ὔ, ῠ]
          · simp [Ξ, ὔ, Ἶ]
      · have ῠ : y c ≠ i.castSucc := λ h ↦ hy (Or.inl h)
        have Ἶ : y c ≠ Fin.last k := λ h ↦ hy (Or.inr h)
        have hxyc : x c = y c := (ô (y c) ῠ Ἶ c).mpr rfl
        rcases hx with hxi | ὔ
        · exact (ῠ (hxyc.symm.trans hxi)).elim
        · exact (Ἶ (hxyc.symm.trans ὔ)).elim
    · have hxi : x c ≠ i.castSucc := λ h ↦ hx (Or.inl h)
      have ὔ : x c ≠ Fin.last k := λ h ↦ hx (Or.inr h)
      by_cases hy : y c = i.castSucc ∨ y c = Fin.last k
      · have hxyc : y c = x c := (ô (x c) hxi ὔ c).mp rfl
        rcases hy with ῠ | Ἶ
        · exact (hxi (hxyc.symm.trans ῠ)).elim
        · exact (ὔ (hxyc.symm.trans Ἶ)).elim
      · have ῠ : y c ≠ i.castSucc := λ h ↦ hy (Or.inl h)
        have Ἶ : y c ≠ Fin.last k := λ h ↦ hy (Or.inr h)
        have hxyc : y c = x c := (ô (x c) hxi ὔ c).mp rfl
        simpa only [Ξ, if_neg ὔ, if_neg Ἶ] using hxyc.symm
  simp only [Ì, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hreplace]
private def Ö {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Fin m → Fin (k + 1) :=
  λ c ↦
    match l.idxFun c with
    | none => Fin.last k
    | some a => a.castSucc
private lemma ᾂ {k m : ℕ} :
    Function.Injective (Ö : Combinatorics.Line (Fin k) (Fin m) →
      (Fin m → Fin (k + 1))) := by
  intro l l' hll
  cases l with
  | mk f hf =>
    cases l' with
    | mk g hg =>
      congr
      funext c
      cases hfc : f c with
      | none =>
        cases hgc : g c with
        | none => rfl
        | some a =>
          have hc := congrFun hll c
          simp only [Ö, hfc, hgc] at hc
          exact (Fin.castSucc_ne_last a hc.symm).elim
      | some a =>
        cases hgc : g c with
        | none =>
          have hc := congrFun hll c
          simp only [Ö, hfc, hgc] at hc
          exact (Fin.castSucc_ne_last a hc).elim
        | some b =>
          have hc := congrFun hll c
          simp only [Ö, hfc, hgc] at hc
          exact congrArg some (Fin.castSucc_injective k hc)
lemma Ἒ {k m n : ℕ} (hk : 2 ≤ k)
    [Β (Combinatorics.Line (Fin k) (Fin m))]
    {δ : ℝ} (hδ₀ : 0 < δ)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (ᾈ : ((Ρ k m).dens : ℝ) ≤ 1 / 2)
    (ὕ : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter λ l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    Parameters.θ k δ / 4 ≤
      ((Γ.intersection (Ì A V)).dens : ℝ) := by
  classical
  let good := Finset.univ.filter λ l : Combinatorics.Line (Fin k) (Fin m) ↦
    ∀ a, V (Fin.castSucc ∘ l a) ∈ A
  let endpointEmbedding :
      Combinatorics.Line (Fin k) (Fin m) ↪ (Fin m → Fin (k + 1)) :=
    ⟨Ö, ᾂ⟩
  have ᾄ :
      good.map endpointEmbedding ⊆ Γ.intersection (Ì A V) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hx
    apply Γ.Φ.mpr
    intro i
    simp only [Ì, Finset.mem_filter, Finset.mem_univ, true_and]
    have ἅ :
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A := by
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    have heval :
        Ξ i (Ö l) = Fin.castSucc ∘ l i := by
      funext c
      cases hc : l.idxFun c with
      | none =>
          simp [Ö, Ξ, Combinatorics.Line.coe_apply, hc]
      | some a =>
          simp [Ö, Ξ, Combinatorics.Line.coe_apply, hc,
            Fin.castSucc_ne_last]
    change V (Ξ i (Ö l)) ∈ A
    rw [heval]
    exact ἅ i
  have hmono :
      ((good.map endpointEmbedding).dens : ℝ) ≤
        ((Γ.intersection (Ì A V)).dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens ᾄ
  refine (le_trans ?_ hmono)
  have ἅ :
      Parameters.θ k δ / 2 ≤ (good.dens : ℝ) := by
    simpa only [good] using ὕ
  have ῷ :
      0 < (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) := by
    have hgoodpos : 0 < (good.dens : ℝ) :=
      (div_pos (Parameters.θ_pos hk hδ₀) (by norm_num)).trans_le ἅ
    have hgne : good.Nonempty := by
      apply Finset.dens_pos.mp
      exact_mod_cast hgoodpos
    let : Nonempty (Combinatorics.Line (Fin k) (Fin m)) := ⟨hgne.choose⟩
    exact_mod_cast Fintype.card_pos
  rw [Finset.nnratCast_dens, Finset.card_map]
  rw [Finset.nnratCast_dens] at ἅ ᾈ
  have ᾰ :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    rw [Subspace.card_line k m (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) m
  have ῡ :
      (Fintype.card (Fin m → Fin (k + 1)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have ῇ :
      (Ρ k m).card = k ^ m := by
    rw [ã, Finset.card_map, Finset.card_univ,
      Fintype.card_pi_const, Fintype.card_fin]
  rw [ᾰ] at ἅ ῷ
  rw [ῡ] at ⊢
  rw [ῇ, Nat.cast_pow, ῡ] at ᾈ
  have ῶ : 0 < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hhalf :
      ((k + 1 : ℕ) : ℝ) ^ m / 2 ≤
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    apply (div_le_iff₀ ῶ).mp at ᾈ
    nlinarith
  rw [le_div_iff₀ ῷ] at ἅ
  rw [le_div_iff₀ ῶ]
  nlinarith [hhalf, ἅ, Parameters.θ_pos hk hδ₀]
lemma á {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (ð : Ἕ A) :
    pullback V A ∩ Γ.intersection (Ì A V) ⊆
      Ρ k m := by
  intro x hx
  obtain ⟨hxpull, hxinter⟩ := Finset.mem_inter.mp hx
  simp only [Ρ, Finset.mem_filter, Finset.mem_univ, true_and]
  intro c hc
  let p : Combinatorics.Line (Fin (k + 1)) (Fin m) := {
    idxFun := λ i ↦ if x i = Fin.last k then none else some (x i)
    proper := ⟨c, if_pos hc⟩
  }
  have hp_last : p (Fin.last k) = x := by
    funext i
    by_cases hi : x i = Fin.last k <;>
      simp only [p, Combinatorics.Line.coe_apply, hi, ↓reduceIte, Option.getD_none,
        Option.getD_some]
  have hp_cast (i : Fin k) : p i.castSucc = Ξ i x := by
    funext j
    by_cases hj : x j = Fin.last k <;>
      simp only [p, Ξ, Combinatorics.Line.coe_apply, hj, ↓reduceIte,
        Option.getD_none, Option.getD_some]
  obtain ⟨a, ha⟩ := ð (Subspace.φ V p)
  apply ha
  rw [Subspace.composeLine_apply]
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
  · rw [hp_cast]
    have hi := Γ.Φ.mp hxinter i
    simpa only [Ì, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · rw [hp_last]
    simpa only [pullback, Finset.mem_filter, Finset.mem_univ, true_and] using hxpull
lemma Ó {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (ü : Λ k δ ≤ m) :
    ((Ρ k m).dens : ℝ) ≤ Parameters.η k δ := by
  rw [ἠ]
  exact ἃ hk hδ₀ ü
lemma õ {k m n : ℕ} (hk : 2 ≤ k)
    [Β (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ü : Λ k δ ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (ð : Ἕ A)
    (ὕ : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter λ l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, Γ i.castSucc (Fin.last k) (C i)) ∧
      Parameters.θ k δ / 4 ≤ ((Γ.intersection C).dens : ℝ) ∧
      ((pullback V A ∩ Γ.intersection C).dens : ℝ) ≤
        Parameters.η k δ := by
  refine ⟨Ì A V, Ὁ A V, ?_, ?_⟩
  · refine Ἒ hk hδ₀ A V ?_ ὕ
    apply (Ó hk hδ₀ ü).trans
    exact (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  · refine le_trans ?_ <|
      Ó hk hδ₀ ü
    exact_mod_cast Finset.dens_mono <|
      á A V ð
lemma Ὢ {X : Type*} [Β X] [Nonempty X]
    [Α X] (A C : Finset X) (δ η θ : ℝ)
    (hδ₀ : 0 ≤ δ) (hη₀ : 0 ≤ η) (hA : δ - 2 * η ≤ (A.dens : ℝ))
    (hC : θ / 4 ≤ (C.dens : ℝ))
    (hAC : ((A ∩ C).dens : ℝ) ≤ η)
    (hgain : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η) :
    (δ + 6 * η) * ((Cᶜ).dens : ℝ) ≤ ((A ∩ Cᶜ).dens : ℝ) ∧
      δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
  have hsplitA : ((A ∩ C).dens : ℝ) + ((A ∩ Cᶜ).dens : ℝ) = (A.dens : ℝ) := by
    norm_cast
    simpa only [sdiff_eq_inter_compl] using Finset.dens_inter_add_dens_sdiff A C
  have hsplitC : ((Cᶜ).dens : ℝ) + (C.dens : ℝ) = 1 := by
    norm_cast
    simpa only [← compl_eq_univ_sdiff, Finset.dens_univ] using
      Finset.dens_sdiff_add_dens_eq_dens C.subset_univ
  have ᾨ : δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
    linarith [hsplitA, hA, hAC]
  constructor
  · refine (mul_le_mul_of_nonneg_left ?_ ?_).trans (hgain.trans ᾨ)
    · linarith [hsplitC, hC]
    · linarith [hδ₀, hη₀]
  · exact ᾨ
lemma Ἁ {k : ℕ} (hk : 2 ≤ k)
    (Μ : Ζ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ü : Λ k δ ≤ m)
    (hn : Ú k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (ð : Ἕ A)
    (Ᾱ : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (Subspace.Θ V A : ℝ) < δ + Parameters.η k δ ^ 2 / 2) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, Γ i.castSucc (Fin.last k) (C i)) ∧
        (δ + 6 * Parameters.η k δ) *
            ((Γ.intersection C)ᶜ.dens : ℝ) ≤
          ((pullback V A ∩ (Γ.intersection C)ᶜ).dens : ℝ) ∧
        δ - 3 * Parameters.η k δ ≤
          ((pullback V A ∩ (Γ.intersection C)ᶜ).dens : ℝ) := by
  classical
  let : Β (Combinatorics.Line (Fin k) (Fin m)) :=
    Fintype.ofInjective (λ l ↦ l.idxFun) λ _ _ h ↦ Combinatorics.Line.ext h
  obtain ⟨V, hV⟩ | ⟨V, hV, ὕ⟩ :=
    Ὕ hk Μ m hm δ hδ₀ hδ₁ n hn A hA
  · exact ((not_lt_of_ge hV) (Ᾱ V)).elim
  obtain ⟨C, hC, hCdense, hAC⟩ :=
    õ hk δ hδ₀ hδ₁ ü A V ð ὕ
  refine ⟨V, C, hC, ?_⟩
  apply Ὢ
  · exact hδ₀.le
  · exact (Parameters.η_pos hk hδ₀).le
  · simpa only [Subspace.Θ, pullback] using hV
  · exact hCdense
  · exact hAC
  · exact Parameters.large_intersection_complement_gain hk hδ₀
def Ε {k : ℕ} {X : Type*} [Β X] [Α X]
    (C : Fin k → Finset X) (i : Fin k) : Finset X :=
  (C i)ᶜ ∩ Finset.univ.filter λ x ↦ ∀ j, j < i → x ∈ C j
def Å {k : ℕ} {X : Type*} [Β X] [Α X]
    (C : Fin k → Finset X) (i : Fin k) : Fin k → Finset X :=
  λ j ↦ if j < i then C j else if j = i then (C j)ᶜ else Finset.univ
lemma ἢ {k : ℕ} {ι : Type*}
    [Β (ι → Fin (k + 1))] [Α (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, Γ i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    ∀ j, Γ j.castSucc (Fin.last k) (Å C i j) := by
  intro j
  dsimp [Å]
  by_cases Ἂ : j < i
  · simp [Ἂ, hC j]
  · by_cases hej : j = i
    · rw [hej]
      simpa using (hC i).compl
    · simp [Ἂ, hej, Γ]
lemma Ἥ {k : ℕ} {X : Type*} [Β X] [Α X]
    (C : Fin k → Finset X) (i : Fin k) :
    Γ.intersection (Å C i) = Ε C i := by
  ext x
  simp only [Γ.Φ, Å, Ε,
    Finset.mem_inter, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    constructor
    · have hxi := hx i
      simp only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] at hxi
      exact hxi
    · intro j Ἂ
      simpa only [if_pos Ἂ] using hx j
  · rintro ⟨hnot, hbefore⟩ j
    by_cases Ἂ : j < i
    · simpa only [if_pos Ἂ] using hbefore j Ἂ
    · by_cases hji : j = i
      · subst j
        simpa only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] using hnot
      · simp only [if_neg Ἂ, if_neg hji, Finset.mem_univ]
lemma Ü {k : ℕ} {X : Type*} [Β X] [Α X]
    (C : Fin k → Finset X) :
    Finset.univ.biUnion (Ε C) = (Γ.intersection C)ᶜ := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    rw [Ε, Finset.mem_inter, Finset.mem_compl] at hi
    rw [Finset.mem_compl]
    intro hinter
    exact hi.1 (Γ.Φ.mp hinter i)
  · rw [Finset.mem_compl]
    intro hx
    have hfailed : ∃ i, x ∉ C i := by
      by_contra! h
      exact hx <| Γ.Φ.mpr h
    let I := Finset.univ.filter λ i : Fin k ↦ x ∉ C i
    have hI : I.Nonempty := by
      obtain ⟨i, hi⟩ := hfailed
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i := I.min' hI
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [Ε, Finset.mem_inter, Finset.mem_compl]
    constructor
    · exact (Finset.mem_filter.mp (I.min'_mem hI)).2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j Ἂ
      by_contra hj
      have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      exact (not_lt_of_ge (I.min'_le j hjI)) Ἂ
lemma à {k : ℕ} {X : Type*} [Β X] [Α X]
    (C : Fin k → Finset X) {i j : Fin k} (Ἂ : i < j) :
    Disjoint (Ε C i : Set X) (Ε C j : Set X) := by
  dsimp only [Disjoint]
  intro x hxi hxj
  simp only [Ε, coe_inter, coe_compl, coe_filter, mem_univ, true_and,
    Set.subset_inter_iff] at *
  simp only [Set.bot_eq_empty, Set.subset_empty_iff]
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  exact (hxi.1 hy) (hxj.2 hy i Ἂ)
lemma Ê {k : ℕ} {X : Type*} [Β X] [Α X]
    (C : Fin k → Finset X) :
    (Set.univ : Set (Fin k)).PairwiseDisjoint λ i ↦ (Ε C i : Set X) := by
  intro i _ j _ Ἂ
  obtain Ἂ | hji := lt_or_gt_of_ne Ἂ
  · exact à C Ἂ
  · exact (à C hji).symm
lemma ἳ {k : ℕ}
    {X : Type*} [Β X] [Α X]
    (A : Finset X) (C : Fin k → Finset X) :
    (∑ i, ((Ε C i).dens : ℝ)) =
        (((Γ.intersection C)ᶜ).dens : ℝ) ∧
      (∑ i, ((A ∩ Ε C i).dens : ℝ)) =
        ((A ∩ (Γ.intersection C)ᶜ).dens : ℝ) := by
  constructor
  · have h := Finset.dens_biUnion (s := Finset.univ) (t := Ε C) <|
      Finset.pairwiseDisjoint_coe.mp <| by
        simpa only [Finset.coe_univ] using Ê C
    rw [Ü] at h
    rw [← NNRat.cast_sum]
    exact congrArg (λ q : ℚ≥0 ↦ (q : ℝ)) h.symm
  · have Χ :
        (Set.univ : Set (Fin k)).PairwiseDisjoint λ i ↦
          (A ∩ Ε C i : Set X) :=
      (Ê C).mono_on λ _ _ ↦
        Set.inter_subset_right
    have h := Finset.dens_biUnion (s := Finset.univ)
      (t := λ i ↦ A ∩ Ε C i) <|
        Finset.pairwiseDisjoint_coe.mp <| by
          simpa only [Finset.coe_univ, Finset.coe_inter] using Χ
    rw [← Finset.inter_biUnion, Ü] at h
    rw [← NNRat.cast_sum]
    exact congrArg (λ q : ℚ≥0 ↦ (q : ℝ)) h.symm
lemma ç {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Β X] [Α X]
    (A : Finset X) (C : Fin k → Finset X)
    (ὦ : (δ + 6 * Parameters.η k δ) *
        ((Γ.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (Γ.intersection C)ᶜ).dens : ℝ))
    (ή : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (Γ.intersection C)ᶜ).dens : ℝ))
    (ᾛ : (∑ i, ((Ε C i).dens : ℝ)) =
      (((Γ.intersection C)ᶜ).dens : ℝ))
    (ἒ : (∑ i, ((A ∩ Ε C i).dens : ℝ)) =
      ((A ∩ (Γ.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((Ε C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((Ε C i).dens : ℝ) ≤
        ((A ∩ Ε C i).dens : ℝ) := by
  by_contra! h
  let g := Parameters.γ k δ
  let e := Parameters.η k δ
  let c := (((Γ.intersection C)ᶜ).dens : ℝ)
  let a := ((A ∩ (Γ.intersection C)ᶜ).dens : ℝ)
  let : Nonempty (Fin k) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hk⟩⟩
  have hg₀ : 0 < g := Parameters.γ_pos hk hδ₀
  have he₀ : 0 < e := Parameters.η_pos hk hδ₀
  have Ᾰ :
      ∑ i, ((A ∩ Ε C i).dens : ℝ) <
        ∑ i, ((δ + g) * ((Ε C i).dens : ℝ) + g) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    by_cases hi : g ≤ ((Ε C i).dens : ℝ)
    · linarith [h i (by simpa only [g] using hi)]
    · have hinter :
          ((A ∩ Ε C i).dens : ℝ) ≤
            ((Ε C i).dens : ℝ) := by
        exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
      have ό : 0 ≤ δ + g := by
        linarith
      nlinarith [mul_nonneg ό
        (by positivity : 0 ≤ ((Ε C i).dens : ℝ))]
  have ᾷ : a < (δ + g) * c + (k : ℝ) * g := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at Ᾰ
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at Ᾰ
    rw [ᾛ, ἒ] at Ᾰ
    exact Ᾰ
  have hac : a ≤ c := by
    dsimp only [a, c]
    exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
  have hc : δ / 2 ≤ c := by
    dsimp only [a, c] at ή hac
    linarith [Parameters.η_le_δ_div_six k δ]
  have hcoef : 3 * e ≤ 6 * e - g := by
    dsimp only [e, g]
    linarith [Parameters.γ_le_three_mul_η k δ]
  have hleft :
      3 * e * (δ / 2) ≤ (6 * e - g) * c := by
    exact mul_le_mul hcoef hc (by positivity) (by linarith)
  have hk_real : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk)
  have hright : (k : ℝ) * g ≤ δ * e ^ 2 := by
    have hdiv : g ≤ δ * e ^ 2 / (k : ℝ) := by
      dsimp only [g, e]
      unfold Parameters.γ
      exact min_le_left _ _
    simpa only [mul_comm] using (le_div_iff₀ hk_real).mp hdiv
  have hstrict : δ * e ^ 2 < 3 * e * (δ / 2) := by
    dsimp only [e]
    nlinarith [Parameters.η_le_δ_div_six k δ]
  have hgap : (6 * e - g) * c < (k : ℝ) * g := by
    dsimp only [a, c, e, g] at ὦ ᾷ
    nlinarith
  exact (not_lt_of_ge hleft) (hgap.trans_le hright |>.trans hstrict)
lemma ἵ {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Β X] [Α X]
    (A : Finset X) (C : Fin k → Finset X)
    (ὦ : (δ + 6 * Parameters.η k δ) *
        ((Γ.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (Γ.intersection C)ᶜ).dens : ℝ))
    (ή : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (Γ.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((Ε C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((Ε C i).dens : ℝ) ≤
        ((A ∩ Ε C i).dens : ℝ) := by
  obtain ⟨ᾛ, ἒ⟩ :=
    ἳ A C
  exact ç hk hδ₀ hδ₁ A C ὦ
    ή ᾛ ἒ
lemma Ὦ {k : ℕ} {ι : Type*}
    [Β (ι → Fin (k + 1))] [Α (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, Γ i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    (∀ j, Γ j.castSucc (Fin.last k) (Å C i j)) ∧
      Γ.intersection (Å C i) = Ε C i ∧
      Finset.univ.biUnion (Ε C) = (Γ.intersection C)ᶜ ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint λ j ↦
        (Ε C j : Set (ι → Fin (k + 1))) := by
  exact ⟨ἢ C hC i,
    Ἥ C i, Ü C,
    Ê C⟩
lemma Ἳ {k : ℕ} (hk : 2 ≤ k)
    (Μ : Ζ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ü : Λ k δ ≤ m)
    (hn : Ú k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (ð : Ἕ A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, Γ i.castSucc (Fin.last k) (D i)) ∧
        Parameters.γ k δ ≤ ((Γ.intersection D).dens : ℝ) ∧
        (δ + Parameters.γ k δ) * ((Γ.intersection D).dens : ℝ) ≤
          ((pullback V A ∩ Γ.intersection D).dens : ℝ) := by
  classical
  by_cases ή : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.Θ V A : ℝ)
  · obtain ⟨V, hV⟩ := ή
    let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    let : Α (Fin m → Fin (k + 1)) := Classical.decEq _
    let D := λ _ : Fin k ↦ (Finset.univ : Finset (Fin m → Fin (k + 1)))
    have hD : Γ.intersection D = Finset.univ := by
      simpa only [Γ.intersection, D] using
        (Finset.inf_const (s := (Finset.univ : Finset (Fin k))) Finset.univ_nonempty
          (Finset.univ : Finset (Fin m → Fin (k + 1))))
    refine ⟨V, D, ?_, ?_, ?_⟩
    · intro i x y _
      simp only [D, Finset.mem_univ]
    · rw [hD]
      norm_num
      nlinarith [Parameters.η_le_δ_div_six k δ,
        Parameters.γ_le_η_sq_div_two k δ, Parameters.η_pos hk hδ₀,
        sq_nonneg (1 - Parameters.η k δ)]
    · rw [hD]
      norm_num
      change δ + Parameters.γ k δ ≤ (Subspace.Θ V A : ℝ)
      linarith [Parameters.γ_le_η_sq_div_two k δ]
  · have Ᾱ : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        (Subspace.Θ V A : ℝ) <
          δ + Parameters.η k δ ^ 2 / 2 := by
      intro V
      exact lt_of_not_ge λ hV ↦ ή ⟨V, hV⟩
    obtain ⟨V, C, hC, ὦ, ᾨ⟩ :=
      Ἁ hk Μ m n hm δ hδ₀ hδ₁ ü hn A hA
        ð Ᾱ
    obtain ⟨i, hidense, ῦ⟩ :=
      ἵ hk hδ₀ hδ₁ (pullback V A) C ὦ
        ᾨ
    obtain ⟨hD, ê, _, _⟩ := Ὦ C hC i
    refine ⟨V, Å C i, hD, ?_, ?_⟩
    · rw [ê]
      exact hidense
    · rw [ê]
      exact ῦ
end Δ
end
section
open Finset
open Combinatorics
open scoped BigOperators
namespace Δ
def έ (k d : ℕ) (δ : ℝ) (n : ℕ) : Prop :=
  ∀ (_ : 2 ≤ k), Ζ k → 1 ≤ d → 0 < δ → δ ≤ 1 →
    ∃ m, 1 ≤ m ∧
      Λ k δ ≤ m ∧
      Ú k m δ ≤ n ∧
      Γ.Τ k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m
lemma Î (k d : ℕ) (δ : ℝ) :
    ∃ N, ∀ n ≥ N, έ k d δ n := by
  let m := max (max 1 (Λ k δ))
    (Γ.Τ k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))))
  refine ⟨Ú k m δ, ?_⟩
  intro n hn _ _ _ _ _
  refine ⟨m, ?_, ?_, hn, ?_⟩ <;>
    dsimp only [m] <;> omega
noncomputable def Â (k d : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact Nat.find (Î k d δ)
lemma ᾙ {k d : ℕ} (hk : 2 ≤ k) (Μ : Ζ k) (hd : 1 ≤ d)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {n : ℕ} (hn : Â k d δ ≤ n) :
    ∃ m, 1 ≤ m ∧
      Λ k δ ≤ m ∧
      Ú k m δ ≤ n ∧
      Γ.Τ k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m := by
  classical
  unfold Â at hn
  exact Nat.find_spec (Î k d δ) n hn
    hk Μ hd hδ₀ hδ₁
lemma Ἦ {k d m : ℕ}
    (hk : 2 ≤ k) (Μ : Ζ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (Ὠ : Γ.Τ k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, Γ i.castSucc (Fin.last k) (D i))
    (Ὡ : Parameters.γ k δ ≤ ((Γ.intersection D).dens : ℝ)) :
    ∃ 𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)),
      𝒱.Nonempty ∧
      (∀ W ∈ 𝒱, Subspace.Ι W (Γ.intersection D)) ∧
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint λ W ↦
        (Subspace.range W : Set (Fin m → Fin (k + 1)))) ∧
      ((Γ.Η (η := Fin d)
        (Γ.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2 := by
  classical
  let β := Parameters.γ k δ ^ 2 / (4 * (k : ℝ))
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have hγ₁ : Parameters.γ k δ ≤ 1 := by
    linarith [Parameters.γ_le_three_mul_η k δ, Parameters.η_le_δ_div_six k δ]
  have hβ₀ : 0 < β := by
    dsimp only [β]
    positivity
  have hβ_simplify :
      2 * (k : ℝ) * β = Parameters.γ k δ ^ 2 / 2 := by
    dsimp only [β]
    field_simp
    ring
  have hDβ :
      2 * (k : ℝ) * β ≤ ((Γ.intersection D).dens : ℝ) := by
    rw [hβ_simplify]
    nlinarith
  obtain ⟨𝒱, h𝒱finite, ς, Χ, μ⟩ :=
    Γ.exists_disjoint_subspaces_iInter (k := k) k d m Μ (by omega) le_rfl hd
      β hβ₀ Ὠ D (by
        simpa only [Fin.castLE_rfl, id_eq] using hD) hDβ
  have h𝒱nonempty : 𝒱.Nonempty := by
    by_contra h𝒱
    rw [Set.not_nonempty_iff_eq_empty.mp h𝒱] at μ
    have hempty :
        Γ.Η (η := Fin d)
          (Γ.intersection D) (∅ : Set _) =
            Γ.intersection D := by
      ext x
      simp [Γ.Η]
    rw [hempty, hβ_simplify] at μ
    nlinarith
  refine ⟨h𝒱finite.toFinset, h𝒱finite.toFinset_nonempty.mpr h𝒱nonempty, ?_, ?_, ?_⟩
  · intro W hW
    exact ς W (h𝒱finite.mem_toFinset.mp hW)
  · simpa only [h𝒱finite.coe_toFinset] using Χ
  · simpa only [h𝒱finite.coe_toFinset, hβ_simplify] using μ
lemma Ἱ {k d m n : ℕ}
    (hk : 2 ≤ k) {δ : ℝ} (hδ₀ : 0 < δ)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (Ὡ : Parameters.γ k δ ≤ ((Γ.intersection D).dens : ℝ))
    (Ἇ : (δ + Parameters.γ k δ) *
        ((Γ.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ Γ.intersection D).dens : ℝ))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (ς : ∀ W ∈ 𝒱, Subspace.Ι W (Γ.intersection D))
    (Χ :
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint λ W ↦
      (Subspace.range W : Set (Fin m → Fin (k + 1)))))
    (μ :
      ((Γ.Η (η := Fin d)
        (Γ.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2) :
    (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ) := by
  classical
  let C := Γ.intersection D
  let P := pullback V A
  let T := 𝒱.biUnion Subspace.range
  have hTsub : T ⊆ C := by
    intro x hx
    simp only [T, Finset.mem_biUnion] at hx
    obtain ⟨W, hW, hxW⟩ := hx
    obtain ⟨z, rfl⟩ := Subspace.mem_range.mp hxW
    exact ς W hW z
  have ᾞ :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        Subspace.range := by
    intro W hW W' hW' hne
    apply Finset.disjoint_left.mpr
    intro x hxW hxW'
    exact Set.disjoint_left.mp (Χ hW hW' hne) hxW hxW'
  have hsumT :
      ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) = (T.dens : ℝ) := by
    exact_mod_cast (Finset.dens_biUnion ᾞ).symm
  have Έ :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        (λ W ↦ P ∩ Subspace.range W) := by
    intro W hW W' hW' hne
    exact (ᾞ hW hW' hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hinterT :
      𝒱.biUnion (λ W ↦ P ∩ Subspace.range W) = P ∩ T := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, T]
    aesop
  have hsumPT :
      ∑ W ∈ 𝒱, ((P ∩ Subspace.range W).dens : ℝ) = ((P ∩ T).dens : ℝ) := by
    rw [← hinterT]
    exact_mod_cast (Finset.dens_biUnion Έ).symm
  have ΰ : Γ.Η (η := Fin d) C (𝒱 : Set _) = C \ T := by
    ext x
    simp [Γ.Η, T]
  have hPT_eq : (P ∩ C) ∩ T = P ∩ T := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hxP, _⟩, hxT⟩
      exact ⟨hxP, hxT⟩
    · rintro ⟨hxP, hxT⟩
      exact ⟨⟨hxP, hTsub hxT⟩, hxT⟩
  have hremainder :
      ((P ∩ C) \ T).dens ≤ (C \ T).dens := by
    apply Finset.dens_le_dens
    intro x hx
    obtain ⟨hxPC, hxT⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hxPC).2, hxT⟩
  have Ὲ :
      (((P ∩ C) \ T).dens : ℝ) ≤ ((C \ T).dens : ℝ) := by
    exact_mod_cast hremainder
  have hdecomp :
      ((P ∩ T).dens : ℝ) + (((P ∩ C) \ T).dens : ℝ) =
        ((P ∩ C).dens : ℝ) := by
    norm_cast
    simpa only [hPT_eq] using Finset.dens_inter_add_dens_sdiff (P ∩ C) T
  have hTdens : (T.dens : ℝ) ≤ (C.dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens hTsub
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have ό : 0 ≤ δ + Parameters.γ k δ / 2 := by
    linarith
  rw [hsumT, hsumPT]
  apply (mul_le_mul_of_nonneg_left hTdens ό).trans
  rw [ΰ] at μ
  dsimp only [C, P] at Ὡ Ἇ μ hdecomp Ὲ hTdens ⊢
  nlinarith
lemma Subspace.dens_inter_range_eq_relativeDensity_mul_range
    {η α ι : Type*} [Β (η → α)] [Β (ι → α)]
    [Α (ι → α)]
    (W : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    ((A ∩ range W).dens : ℝ) =
      (Θ W A : ℝ) * ((range W).dens : ℝ) := by
  classical
  let B := Finset.univ.filter λ x : η → α ↦ W x ∈ A
  have hAB : A ∩ range W = B.image W := by
    ext w
    simp only [B, range, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, x, hx⟩
      exact ⟨x, hx.symm ▸ hw, hx⟩
    · rintro ⟨x, hx, ô⟩
      exact ⟨ô ▸ hx, x, ô⟩
  rw [hAB]
  simp only [Finset.nnratCast_dens, Θ, range, B]
  rw [Finset.card_image_iff.mpr (Subspace.injective W).injOn,
    Finset.card_image_iff.mpr (Subspace.injective W).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · let : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hB : (Finset.univ.filter λ x : η → α ↦ W x ∈ A) = ∅ :=
      Subsingleton.elim _ _
    rw [hB]
    simp
  · field_simp
    simp only [Finset.card_univ]
lemma ἣ {k d m n : ℕ}
    {δ : ℝ} (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (h𝒱 : 𝒱.Nonempty)
    (hsum : (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) :
    ∃ W ∈ 𝒱,
      δ + Parameters.γ k δ / 2 ≤
        (Subspace.Θ W (pullback V A) : ℝ) := by
  by_contra! h
  apply (not_lt_of_ge hsum)
  calc
    (∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) <
        ∑ W ∈ 𝒱, (δ + Parameters.γ k δ / 2) *
          ((Subspace.range W).dens : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty h𝒱
      intro W hW
      rw [Subspace.dens_inter_range_eq_relativeDensity_mul_range]
      apply mul_lt_mul_of_pos_right (h W hW)
      exact_mod_cast Finset.dens_pos.mpr
        ⟨W (λ _ ↦ 0), Subspace.mem_range.mpr ⟨λ _ ↦ 0, rfl⟩⟩
    _ = (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) := by
      rw [Finset.mul_sum]
lemma Subspace.relativeDensity_compose {α η ζ ι : Type*}
    [Β (η → α)] [Β (ζ → α)] [Α (η → α)]
    [Α (ι → α)]
    (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    (Θ (compose V W) A : ℝ) =
      (Θ W (pullback V A) : ℝ) := by
  simp only [Θ, pullback, Finset.mem_filter, Finset.mem_univ, true_and,
    Ψ]
lemma Ò {k d m n : ℕ}
    (hk : 2 ≤ k) (Μ : Ζ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (Ὠ : Γ.Τ k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, Γ i.castSucc (Fin.last k) (D i))
    (Ὡ : Parameters.γ k δ ≤ ((Γ.intersection D).dens : ℝ))
    (Ἇ : (δ + Parameters.γ k δ) *
        ((Γ.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ Γ.intersection D).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
      δ + Parameters.γ k δ / 2 ≤ (Subspace.Θ W A : ℝ) := by
  obtain ⟨𝒱, h𝒱, ς, Χ, μ⟩ :=
    Ἦ hk Μ hd hδ₀ hδ₁ Ὠ D hD Ὡ
  obtain ⟨W, _, hW⟩ :=
    ἣ A V 𝒱 h𝒱 <|
      Ἱ hk hδ₀ A V D Ὡ Ἇ 𝒱
        ς Χ μ
  refine ⟨Subspace.compose V W, ?_⟩
  rw [Subspace.relativeDensity_compose]
  exact hW
lemma ᾳ {k : ℕ} (hk : 2 ≤ k) (Μ : Ζ k)
    (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : Â k d δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        δ + Parameters.γ k δ / 2 ≤ (Subspace.Θ V A : ℝ) := by
  classical
  by_cases ð : Ἕ A
  · obtain ⟨m, hm, ü, ἁ, Ὠ⟩ :=
      ᾙ hk Μ hd hδ₀ hδ₁ hn
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let : Nonempty (Combinatorics.Line (Fin k) (Fin m)) :=
      ⟨Combinatorics.Line.diagonal (Fin k) (Fin m)⟩
    obtain ⟨V, D, hD, Ὡ, Ἇ⟩ :=
      Ἳ hk Μ m n hm δ hδ₀ hδ₁ ü ἁ A hA ð
    exact Or.inr <|
      Ò hk Μ hd hδ₀ hδ₁ Ὠ
        A V D hD Ὡ Ἇ
  · rw [Ἕ] at ð
    push Not at ð
    exact Or.inl ð
end Δ
end
section
open Finset
open Combinatorics
namespace Δ
def ψ {ι : Type*} [Β ι] (w : ι → Fin 2) : Finset ι :=
  Finset.univ.filter λ i ↦ w i = 1
lemma ὼ {ι : Type*} [Β ι] (x y : ι → Fin 2) :
    (∃ l : Combinatorics.Line (Fin 2) ι, l 0 = x ∧ l 1 = y) ↔
      ψ x ⊂ ψ y := by
  constructor
  · rintro ⟨l, hlx, hly⟩
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ?_
    · intro i hix
      rw [← hlx] at hix
      rw [← hly]
      simp only [ψ, mem_filter, mem_univ, true_and] at hix ⊢
      change (l.idxFun i).getD 0 = 1 at hix
      change (l.idxFun i).getD 1 = 1
      cases hi : l.idxFun i
      · exfalso
        rw [hi] at hix
        exact Fin.zero_ne_one hix
      · rw [hi] at hix
        exact hix
    · obtain ⟨i, hi⟩ := l.proper
      refine ⟨i, ?_, ?_⟩
      · rw [← hly]
        simp only [ψ, mem_filter, mem_univ, true_and]
        change (l.idxFun i).getD 1 = 1
        rw [hi]
        simp
      · rw [← hlx]
        simp only [ψ, mem_filter, mem_univ, true_and]
        change ¬ (l.idxFun i).getD 0 = 1
        rw [hi]
        simp
  · classical
    intro h
    obtain ⟨i, hiy, hix⟩ := (Finset.ssubset_iff_of_subset h.1).1 h
    have ῠ : y i = 1 := by
      simpa [ψ] using hiy
    have hxi₀ : x i = 0 := by
      obtain hxi₀ | ⟨j, hxi₀⟩ := (x i).eq_zero_or_eq_succ
      · exact hxi₀
      · rw [Fin.eq_zero j] at hxi₀
        exfalso
        apply hix
        simp only [ψ, mem_filter, mem_univ, true_and]
        exact hxi₀
    let l : Combinatorics.Line (Fin 2) ι :=
      ⟨λ j ↦ if x j = 0 ∧ y j = 1 then none else some (x j), ⟨i, by simp [hxi₀, ῠ]⟩⟩
    refine ⟨l, ?_, ?_⟩
    · funext j
      simp only [l, Combinatorics.Line.coe_apply]
      split
      · rename_i hj
        simp [hj.1]
      · simp
    · funext j
      simp only [l, Combinatorics.Line.coe_apply]
      split
      · rename_i hj
        simp [hj.2]
      · rename_i hj
        simp only [Option.getD_some]
        obtain hxj | ⟨a, hxj⟩ := (x j).eq_zero_or_eq_succ
        · obtain hyj | ⟨b, hyj⟩ := (y j).eq_zero_or_eq_succ
          · rw [hxj, hyj]
          · rw [Fin.eq_zero b] at hyj
            exact (hj ⟨hxj, hyj⟩).elim
        · rw [Fin.eq_zero a] at hxj
          rw [hxj]
          symm
          change y j = 1
          suffices j ∈ ψ y by
            simpa only [ψ, mem_filter, mem_univ, true_and] using this
          apply h.1
          simp only [ψ, mem_filter, mem_univ, true_and]
          exact hxj
lemma ώ {ι : Type*} [Β ι] :
    Function.Injective (ψ : (ι → Fin 2) → Finset ι) := by
  intro x y ô
  funext i
  apply Fin.ext
  have hi : x i = 1 ↔ y i = 1 := by
    simpa only [ψ, mem_filter, mem_univ, true_and] using Finset.ext_iff.mp ô i
  grind
lemma Ὄ (m : ℕ) :
    ((Nat.centralBinom m : ℝ) / 4 ^ m) ^ 2 * (3 * m + 1) ≤ 1 := by
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec : ((m + 1 : ℕ) : ℝ) * Nat.centralBinom (m + 1) =
          2 * (2 * m + 1) * Nat.centralBinom m := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ m
      have hratio : (Nat.centralBinom (m + 1) : ℝ) / 4 ^ (m + 1) =
          ((Nat.centralBinom m : ℝ) / 4 ^ m) *
            ((2 * m + 1 : ℝ) / (2 * (m + 1))) := by
        rw [pow_succ]
        field_simp
        push_cast at hrec ⊢
        linear_combination 2 * hrec
      rw [hratio, mul_pow, mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) ih
      rw [div_pow, div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity))).mpr
      push_cast
      ring_nf
      nlinarith
lemma ἷ (m : ℕ) :
    (Nat.centralBinom m : ℝ) / 4 ^ m ≤ (√(3 * m + 1))⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (Real.sqrt_pos.2 (by positivity))]
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [one_pow] using Ὄ m
private lemma ᾀ (m : ℕ) : (2 : ℝ) ^ (2 * m) = 4 ^ m := by
  rw [pow_mul]
  norm_num
lemma Ἡ (n : ℕ) :
    (n.choose (n / 2) : ℝ) / 2 ^ n ≤
      (Nat.centralBinom (n / 2) : ℝ) / 4 ^ (n / 2) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    have hdiv : 2 * m / 2 = m := by grind
    rw [hdiv, Nat.centralBinom]
    rw [ᾀ]
  · subst n
    have hdiv : (2 * m + 1) / 2 = m := by grind
    rw [hdiv, Nat.centralBinom]
    cases m with
    | zero => norm_num
    | succ m =>
      have hchoose : (2 * (m + 1) + 1).choose (m + 1) ≤
          2 * Nat.centralBinom (m + 1) := by
        rw [Nat.choose_succ_left (2 * (m + 1)) (m + 1) (by grind)]
        simpa only [Nat.add_sub_cancel, two_mul] using
          add_le_add (Nat.choose_le_centralBinom m (m + 1))
            (Nat.choose_le_centralBinom (m + 1) (m + 1))
      rw [pow_succ, ᾀ]
      rw [mul_comm (4 ^ (m + 1) : ℝ) 2]
      apply le_trans (b := (2 * Nat.centralBinom (m + 1) : ℝ) /
        (2 * 4 ^ (m + 1)))
      · exact (div_le_div_iff_of_pos_right
          (by positivity : (0 : ℝ) < 2 * 4 ^ (m + 1))).mpr <| by
            exact_mod_cast hchoose
      · field_simp
        rfl
lemma ὰ (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → (n.choose (n / 2) : ℝ) < δ * 2 ^ n := by
  have ht : Filter.Tendsto (λ m : ℕ ↦ (√(3 * (m : ℝ) + 1))⁻¹)
      Filter.atTop (nhds 0) := by
    apply tendsto_inv_atTop_zero.comp
    apply Real.tendsto_sqrt_atTop.comp
    simpa only [add_comm] using
      tendsto_const_nhds.add_atTop
        ((tendsto_natCast_atTop_atTop : Filter.Tendsto (λ m : ℕ ↦ (m : ℝ))
          Filter.atTop Filter.atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hδ)
  refine ⟨2 * M, ?_⟩
  intro n hn
  have hMn : M ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by grind)
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp
  apply (Ἡ n).trans_lt
  apply (ἷ (n / 2)).trans_lt
  exact hM (n / 2) hMn
lemma dhj_two : Ζ 2 := by
  intro δ hδ
  obtain ⟨N, hN⟩ := ὰ δ hδ
  refine ⟨N, ?_⟩
  intro n hn A hA
  by_contra ᾱ
  let B := A.image ψ
  have hB : IsAntichain (· ⊆ ·) (B : Set (Finset (Fin n))) := by
    intro s hs t ht hst hsub
    change s ∈ B at hs
    change t ∈ B at ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    apply ᾱ
    obtain ⟨l, hlx, hly⟩ := (ὼ x y).2 <|
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, hst⟩
    refine ⟨l, ?_⟩
    intro a
    obtain rfl | ⟨i, rfl⟩ := a.eq_zero_or_eq_succ
    · rw [hlx]
      exact hx
    · simp only [Fin.eq_zero i]
      change l 1 ∈ A
      rw [hly]
      exact hy
  have þ : #A ≤ n.choose (n / 2) := by
    rw [← Finset.card_image_of_injective A ώ]
    simpa only [B, Fintype.card_fin] using hB.sperner
  exact (not_lt_of_ge (hA.trans <| by exact_mod_cast þ)) (hN n hn)
lemma ἴ {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 1 < δ + (R : ℝ) * (Parameters.γ k δ / 2) := by
  refine ⟨⌈2 / (Parameters.γ k δ)⌉₊ + 1, ?_⟩
  refine lt_trans (?_) (lt_add_of_pos_left _ hδ)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ zero_lt_two).2
  simp only [one_mul]
  apply (div_lt_iff₀ (Parameters.γ_pos hk hδ)).1
  apply lt_of_le_of_lt (Nat.ceil_le.mp le_rfl) (by grind)
lemma Ἐ (k R : ℕ) (δ : ℝ) :
    ∃ d : ℕ → ℕ,
      d R = 1 ∧
      (∀ j, j ≤ R → 1 ≤ d j) ∧
      ∀ j, j < R →
        Â k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j := by
  let γ := Parameters.γ k δ
  let d_aux : ℕ → ℕ :=
    Nat.rec 1 (λ t d_t => max 1 (Â k d_t (δ + ((R - (t + 1) : ℕ) : ℝ) * (γ / 2))))
  let d : ℕ → ℕ := λ j => d_aux (R - j)
  have ῖ (t : ℕ) : d_aux (t + 1) =
      max 1 (Â k (d_aux t) (δ + ((R - (t + 1) : ℕ) : ℝ) * (γ / 2))) := rfl
  have h_aux_one (t : ℕ) : 1 ≤ d_aux t := by
    induction t with
    | zero => simp [d_aux]
    | succ t ih => rw [ῖ t]; exact le_max_left _ _
  have h_d_R : d R = 1 := by
    dsimp [d, d_aux]
    simp
  have h_d_one (j : ℕ) (hj : j ≤ R) : 1 ≤ d j := by
    dsimp [d]
    exact h_aux_one (R - j)
  have h_d_step (j : ℕ) (hj : j < R) :
      Â k (d (j + 1)) (δ + (j : ℝ) * (γ / 2)) ≤ d j := by
    have h_sub : R - j = (R - (j + 1)) + 1 := by omega
    have h_index : (R - ((R - (j + 1) : ℕ) + 1) : ℕ) = j := by omega
    dsimp [d]
    rw [h_sub, ῖ (R - (j + 1))]
    rw [h_index]
    exact le_max_right _ _
  exact ⟨d, h_d_R, h_d_one, h_d_step⟩
def π {m n : ℕ} (ἁ : m ≤ n) : Fin m ⊕ Fin (n - m) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le ἁ))
def È {α : Type*} {m n : ℕ} (ἁ : m ≤ n)
    (x : Fin m → α) (y : Fin (n - m) → α) : Fin n → α :=
  Sum.elim x y ∘ (π ἁ).symm
def Ἄ {α : Type*} {m n : ℕ} (ἁ : m ≤ n)
    (y : Fin (n - m) → α) : Combinatorics.Subspace (Fin m) α (Fin n) where
  idxFun i := ((π ἁ).symm i).elim Sum.inr (Sum.inl ∘ y)
  proper e := by
    refine ⟨π ἁ (Sum.inl e), ?_⟩
    simp only [Equiv.symm_apply_apply, Sum.elim_inl]
@[simp]
lemma ἱ {α : Type*} {m n : ℕ} (ἁ : m ≤ n)
    (y : Fin (n - m) → α) (x : Fin m → α) :
    Ἄ ἁ y x = È ἁ x y := by
  funext i
  change (((π ἁ).symm i).elim Sum.inr (Sum.inl ∘ y)).elim id x =
    Sum.elim x y ((π ἁ).symm i)
  cases (π ἁ).symm i <;> rfl
lemma Ἑ {k m n : ℕ} (ἁ : m ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) :
    ∃ y : Fin (n - m) → Fin (k + 1),
      (A.dens : ℝ) ≤
        ((Finset.univ.filter λ x : Fin m → Fin (k + 1) ↦
          È ἁ x y ∈ A).dens : ℝ) := by
  let eCoord := (Equiv.sumComm (Fin (n - m)) (Fin m)).trans (π ἁ)
  let eWord := eCoord.arrowCongr (Equiv.refl (Fin (k + 1)))
  let A' := A.map eWord.symm.toEmbedding
  have hA' : (A'.dens : ℝ) = (A.dens : ℝ) := by
    simp only [A', Finset.dens_map_equiv]
  have havg :
      (A.dens : ℝ) ≤ Finset.expect Finset.univ (λ y : Fin (n - m) → Fin (k + 1) ↦
        ((fiber A' y).dens : ℝ)) := by
    rw [σ, hA']
  obtain ⟨y, _, hy⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty havg
  refine ⟨y, ?_⟩
  have Ὼ (x : Fin m → Fin (k + 1)) :
      eWord (Sum.elim y x) = È ἁ x y := by
    funext i
    cases h : (π ἁ).symm i with
    | inl j =>
        simp [eWord, eCoord, È, Equiv.arrowCongr,
          Sum.elim, h, Function.comp_apply]
    | inr j =>
        simp [eWord, eCoord, È, Equiv.arrowCongr,
          Sum.elim, h, Function.comp_apply]
  have Ἤ : fiber A' y = Finset.univ.filter λ x : Fin m → Fin (k + 1) ↦
      È ἁ x y ∈ A := by
    ext x
    simp only [τ, Finset.mem_filter, Finset.mem_univ, true_and, A',
      Finset.mem_map_equiv]
    simp only [Equiv.symm_symm]
    rw [Ὼ]
  rw [← Ἤ]
  exact hy
lemma ö {k m n : ℕ} (ἁ : m ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (A.dens : ℝ) ≤ (Subspace.Θ V A : ℝ) := by
  obtain ⟨y, hy⟩ := Ἑ ἁ A
  refine ⟨Ἄ ἁ y, ?_⟩
  simpa only [Subspace.Θ, ἱ] using hy
lemma Ὂ {k R n j : ℕ} (hk : 2 ≤ k)
    (Μ : Ζ k) {δ : ℝ} (hδ : 0 < δ)
    (d : ℕ → ℕ) (hd : ∀ t, t ≤ R → 1 ≤ d t)
    (ᾜ : ∀ t, t < R →
      Â k (d (t + 1))
        (δ + (t : ℝ) * (Parameters.γ k δ / 2)) ≤ d t)
    (hj : j < R) (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n))
    (hV : δ + (j : ℝ) * (Parameters.γ k δ / 2) ≤
      (Subspace.Θ V A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ W : Combinatorics.Subspace (Fin (d (j + 1))) (Fin (k + 1)) (Fin n),
        δ + ((j + 1 : ℕ) : ℝ) * (Parameters.γ k δ / 2) ≤
          (Subspace.Θ W A : ℝ) := by
  let : Nontrivial (Fin (k + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  let ρ := δ + (j : ℝ) * (Parameters.γ k δ / 2)
  have hγ := Parameters.γ_mono_lowerBound hk hδ
  have hρ₀ : 0 < ρ := by
    dsimp only [ρ]
    nlinarith [hγ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have hρ₁ : ρ ≤ 1 := by
    exact hV.trans <| by
      exact_mod_cast Finset.dens_le_one (s := pullback V A)
  have hinc := ᾳ hk Μ (d (j + 1))
    (hd (j + 1) (Nat.succ_le_of_lt hj)) ρ hρ₀ hρ₁ (d j) (ᾜ j hj)
      (pullback V A) (by
        simpa only [ρ, Subspace.Θ, pullback] using hV)
  obtain ⟨l, hl⟩ | ⟨U, hU⟩ := hinc
  · left
    use Subspace.mapLine V l
    intro a
    simpa only [Subspace.mapLine_apply, pullback, Finset.mem_filter, Finset.mem_univ,
      true_and] using hl a
  · right
    use Subspace.compose V U
    rw [Subspace.relativeDensity_compose]
    dsimp only [ρ] at hU
    have hδρ : δ ≤ δ + (j : ℝ) * (Parameters.γ k δ / 2) := by
      nlinarith [hγ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith [hγ.2 _ hδρ]
lemma Ἣ {k R n : ℕ} (hk : 2 ≤ k)
    (Μ : Ζ k) {δ : ℝ} (hδ : 0 < δ)
    (d : ℕ → ℕ) (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (ᾜ : ∀ j, j < R →
      Â k (d (j + 1))
        (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j)
    (A : Finset (Fin n → Fin (k + 1)))
    (V₀ : Combinatorics.Subspace (Fin (d 0)) (Fin (k + 1)) (Fin n))
    (hV₀ : δ ≤ (Subspace.Θ V₀ A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin (d R)) (Fin (k + 1)) (Fin n),
        δ + (R : ℝ) * (Parameters.γ k δ / 2) ≤
          (Subspace.Θ V A : ℝ) := by
  suffices ∀ j, j ≤ R →
      (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
        ∃ V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n),
          δ + (j : ℝ) * (Parameters.γ k δ / 2) ≤
            (Subspace.Θ V A : ℝ) by
    exact this R le_rfl
  intro j hj
  induction j with
  | zero =>
      exact Or.inr ⟨V₀, by
        simpa only [Nat.cast_zero, zero_mul, add_zero] using hV₀⟩
  | succ j ih =>
      obtain ᾱ | ⟨V, hV⟩ := ih (Nat.le_of_succ_le hj)
      · exact Or.inl ᾱ
      · exact Ὂ hk Μ hδ d hd ᾜ
          (Nat.lt_of_succ_le hj) A V hV
lemma Ἢ {k R n : ℕ} (hk : 2 ≤ k) (Μ : Ζ k)
    {δ : ℝ} (hδ : 0 < δ) (d : ℕ → ℕ)
    (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (ᾜ : ∀ j, j < R →
      Â k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j)
    (hn : d 0 ≤ n) (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      δ + (R : ℝ) * (Parameters.γ k δ / 2) ≤ 1 := by
  obtain ⟨V₀, hV₀⟩ :=
    ö hn A
  obtain ᾱ | ⟨V, hV⟩ :=
    Ἣ hk Μ hδ d hd ᾜ A V₀ (hA.trans hV₀)
  · exact Or.inl ᾱ
  · apply Or.inr
    apply hV.trans
    exact_mod_cast Finset.dens_le_one (s := pullback V A)
lemma density_hales_jewett_fin (k : ℕ) (hk : 2 ≤ k) : Ζ k := by
  induction k, hk using Nat.le_induction with
  | base => exact dhj_two
  | succ k hk Μ =>
      intro δ hδ
      obtain ⟨R, hR⟩ := ἴ hk hδ
      obtain ⟨d, _, hd, ᾜ⟩ := Ἐ k R δ
      refine ⟨d 0, ?_⟩
      intro n hn A hA
      refine (Ἢ hk Μ hδ d hd ᾜ hn A ?_).resolve_right ?_
      · exact Subspace.density_le_of_card_le (Nat.zero_lt_succ k) δ A hA
      · exact not_le_of_gt hR
end Δ
namespace Combinatorics.Line
noncomputable def Υ (k : ℕ) (δ : ℝ) : ℕ :=
  if 2 ≤ k then Δ.Subspace.ο k δ else 1
lemma Ἴ (α : Type*) [Β α]
    (hα : Fintype.card α ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin n → α))
    (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hα
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨Line.diagonal α (Fin n), ?_⟩
  intro x
  have þ : Fintype.card α = 1 :=
    Fintype.card_eq_one_of_forall_eq λ y ↦ Subsingleton.elim y x
  rw [þ] at hAδ
  norm_num at hAδ
  obtain ⟨w, hw⟩ : A.Nonempty := Finset.card_pos.mp <| by
    exact_mod_cast hδ.trans_le hAδ
  simpa only [Subsingleton.elim (Line.diagonal α (Fin n) x) w] using hw
lemma Ἵ (α : Type*) [Β α]
    (hα : 2 ≤ Fintype.card α) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : Δ.Subspace.ο (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let e := Fintype.equivFin α
  let wordEquiv : (Fin n → α) ≃ (Fin n → Fin (Fintype.card α)) :=
    (Equiv.refl (Fin n)).arrowCongr e
  let B := A.map wordEquiv.toEmbedding
  have hB : δ * (Fintype.card α : ℝ) ^ n ≤ #B := by
    simpa only [B, Finset.card_map] using hAδ
  obtain ⟨l, hl⟩ := Δ.Subspace.densityOneBound_spec
    (Δ.density_hales_jewett_fin (Fintype.card α) hα)
    δ hδ n hn B hB
  refine ⟨l.map e.symm, ?_⟩
  intro x
  specialize hl (e x)
  rw [Finset.mem_map_equiv] at hl
  change (e.symm ∘ l (e x)) ∈ A at hl
  rw [← e.symm_apply_apply x, Combinatorics.Line.map_apply]
  exact hl
lemma ὲ (α : Type*) [Β α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : Υ (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  by_cases hα : 2 ≤ Fintype.card α
  · refine Ἵ α hα δ hδ n ?_ A hAδ
    simpa only [Υ, if_pos hα] using hn
  · refine Ἴ α (by grind) δ hδ n ?_ A hAδ
    simpa only [Υ, if_neg hα] using hn
theorem exists_of_density (α : Type*) [Β α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : Υ (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  exact ὲ α δ hδ n hn A hAδ
end Combinatorics.Line
end
section
open Finset
open Combinatorics
namespace Combinatorics
structure Ο (α : Type*) [AddMonoid α] (k : ℕ) where
  start : α
  diff : α
  Ἷ : diff ≠ 0
namespace Ο
def term {α : Type*} [AddMonoid α] {k : ℕ} (P : Ο α k)
    (i : Fin k) : α :=
  P.start + (i : ℕ) • P.diff
def IsSubset {α : Type*} [AddMonoid α] {k : ℕ} (P : Ο α k)
    (s : Set α) : Prop :=
  ∀ i, P.term i ∈ s
end Ο
end Combinatorics
namespace Δ
namespace Line
lemma ἐ {k m : ℕ} (hk : 1 ≤ k)
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ∃ P : Combinatorics.Ο ℕ k,
      ∀ a, P.term a = (finFunctionFinEquiv (l a) : ℕ) := by
  let d := ∑ i : Fin m, if l.idxFun i = none then k ^ (i : ℕ) else 0
  refine ⟨
    { start := (finFunctionFinEquiv (l ⟨0, hk⟩) : ℕ)
      diff := d
      Ἷ := ?_ }, ?_⟩
  · apply Nat.ne_of_gt
    apply Finset.sum_pos'
    · intro i _
      exact Nat.zero_le _
    · obtain ⟨i, hi⟩ := l.proper
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simp [hi, Nat.zero_lt_of_lt hk]
  · intro a
    change (finFunctionFinEquiv (l ⟨0, hk⟩) : ℕ) + (a : ℕ) • d
      = (finFunctionFinEquiv (l a) : ℕ)
    simp only [finFunctionFinEquiv_apply]
    rw [nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : l.idxFun i = none
    · simp [Combinatorics.Line.coe_apply, hi]
    · cases hli : l.idxFun i with
      | none => exact (hi hli).elim
      | some b => simp [Combinatorics.Line.coe_apply, hli]
end Line
lemma ὺ {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 2 * K / δ ≤ N) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : δ * N ≤ #A) :
    ∃ q : ℕ, (q + 1) * K ≤ N ∧
      δ / 2 * K ≤ #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
  let Q := N / K
  let S := A ∩ Finset.range (Q * K)
  have htail : (#(A \ Finset.range (Q * K)) : ℝ) < K := by
    norm_cast
    refine (Finset.card_le_card (t := Finset.Ico (Q * K) N) ?_).trans_lt ?_
    · intro x hx
      rw [Finset.mem_Ico]
      rw [Finset.mem_sdiff, Finset.mem_range] at hx
      exact ⟨Nat.le_of_not_gt hx.2, Finset.mem_range.mp (hAN hx.1)⟩
    · rw [Nat.card_Ico]
      simpa only [Q, Nat.mod_eq_sub_mul_div, Nat.mul_comm] using
        Nat.mod_lt N (Nat.zero_lt_of_lt hK)
  have hS : δ / 2 * N ≤ (#S : ℝ) := by
    rw [← Finset.card_inter_add_card_sdiff A (Finset.range (Q * K))] at hA
    push_cast at hA
    dsimp only [S]
    nlinarith [htail, (div_le_iff₀ hδ).mp hN]
  have hmap : ∀ x ∈ S, x / K ∈ Finset.range Q := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_range] at hx
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).2 hx.2)
  obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ Finset.range Q,
      δ / 2 * K ≤ ∑ x ∈ S with x / K = q, (1 : ℝ) := by
    apply Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (M := ℝ) (s := S) (t := Finset.range Q) (f := λ x ↦ x / K)
      (w := λ _ ↦ 1) (b := δ / 2 * K) hmap
    · obtain ⟨x, hx⟩ : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hSempty
        rw [hSempty, Finset.card_empty, Nat.cast_zero] at hS
        apply (not_lt_of_ge hS)
        apply mul_pos
        · positivity
        · apply lt_of_lt_of_le _ hN
          positivity
      exact ⟨x / K, hmap x hx⟩
    · simp only [Finset.card_range, nsmul_eq_mul, Finset.sum_const, mul_one]
      apply le_trans _ hS
      rw [← mul_assoc, mul_comm (Q : ℝ) (δ / 2), mul_assoc]
      apply mul_le_mul_of_nonneg_left
      · norm_cast
        exact Nat.div_mul_le_self N K
      · positivity
  refine ⟨q, ?_, ?_⟩
  · exact (Nat.mul_le_mul_right K (Nat.succ_le_iff.mp (Finset.mem_range.mp hqQ))).trans
      (Nat.div_mul_le_self N K)
  · convert hq using 1
    norm_cast
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    ext x
    dsimp only [S]
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hxA, hxlo, hxhi⟩
      refine ⟨⟨hxA, hxhi.trans_le ?_⟩, ?_⟩
      · exact Nat.mul_le_mul_right K
          (Nat.succ_le_iff.mp (Finset.mem_range.mp hqQ))
      · apply Nat.le_antisymm
        · exact Nat.lt_succ_iff.mp
            ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).2 hxhi)
        · exact (Nat.le_div_iff_mul_le (Nat.zero_lt_of_lt hK)).2 hxlo
    · rintro ⟨⟨hxA, _⟩, hxq⟩
      refine ⟨hxA, ?_, ?_⟩
      · rw [← hxq]
        simpa [Nat.mul_comm] using Nat.mul_div_le x K
      · rw [← hxq]
        exact (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).mp (Nat.lt_succ_self _)
end Δ
namespace Combinatorics.Ο
noncomputable def Υ (k : ℕ) (δ : ℝ) : ℕ :=
  ⌈2 * (k ^ Combinatorics.Line.Υ k (δ / 2) : ℕ) / δ⌉₊
theorem ᾍ (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : Υ k δ ≤ n) (A : Finset ℕ)
    (hAn : A ⊆ range n) (hAδ : δ * n ≤ #A) :
    ∃ P : Ο ℕ k, P.IsSubset (A : Set ℕ) := by
  classical
  have hk_one : 1 ≤ k := by grind
  let m := Combinatorics.Line.Υ k (δ / 2)
  let K := k ^ m
  obtain ⟨q, _, hqA⟩ : ∃ q : ℕ, (q + 1) * K ≤ n ∧
      δ / 2 * K ≤ #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
    refine Δ.ὺ (one_le_pow₀ hk_one) hδ ?_ A hAn hAδ
    · apply Nat.le_of_ceil_le
      simpa only [Υ, m, K] using hn
  let encode (x : Fin m → Fin k) := q * K + (finFunctionFinEquiv x : ℕ)
  let B := Finset.univ.filter λ x : Fin m → Fin k ↦ encode x ∈ A
  let encodeOnB (x : Fin m → Fin k) (_ : x ∈ B) := encode x
  have hBcard : #B = #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
    apply Finset.card_bij encodeOnB
    · intro x hx
      dsimp only [encodeOnB, encode]
      rw [Finset.mem_filter] at hx
      refine Finset.mem_inter.mpr ⟨hx.2, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, ?_⟩⟩
      rw [add_mul, one_mul]
      apply Nat.add_lt_add_left
      exact (finFunctionFinEquiv x).isLt
    · intro x _ y _ ô
      dsimp only [encodeOnB, encode] at ô
      exact finFunctionFinEquiv.injective (Fin.ext (Nat.add_left_cancel ô))
    · intro y hy
      rw [Finset.mem_inter, Finset.mem_Ico] at hy
      have hz : y - q * K < K := by
        rw [Nat.sub_lt_iff_lt_add hy.2.1]
        simpa only [add_mul, one_mul, Nat.add_comm] using hy.2.2
      let z : Fin K := ⟨y - q * K, hz⟩
      let x := finFunctionFinEquiv.symm z
      have ῴ : (finFunctionFinEquiv x : ℕ) = y - q * K :=
        congrArg Fin.val (Equiv.apply_symm_apply finFunctionFinEquiv z)
      dsimp only [encodeOnB, encode]
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · dsimp only [encode]
        rw [ῴ, Nat.add_sub_of_le hy.2.1]
        exact hy.1
      · rw [ῴ, Nat.add_sub_of_le hy.2.1]
  obtain ⟨l, hl⟩ : ∃ l : Combinatorics.Line (Fin k) (Fin m), ∀ x : Fin k, l x ∈ B := by
    apply Combinatorics.Line.exists_of_density (Fin k) (δ / 2)
    · positivity
    · simp [m]
    · rw [Fintype.card_fin, hBcard]
      simpa only [K, Nat.cast_pow] using hqA
  obtain ⟨P, hP⟩ := Δ.Line.ἐ hk_one l
  refine ⟨
    { start := q * K + P.start
      diff := P.diff
      Ἷ := P.Ἷ }, ?_⟩
  intro a
  change (q * K + P.start) + (a : ℕ) • P.diff ∈ A
  rw [add_assoc]
  change q * K + P.term a ∈ A
  rw [hP]
  exact (Finset.mem_filter.mp (hl a)).2
end Combinatorics.Ο
end
open Filter
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.H2 := by
  intro k hk T
  let δ := Real.exp (-T)
  let M := Combinatorics.Ο.Υ k δ
  refine ⟨(M : ℝ)+1,fun N S hN hsub þ ð hparam => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (0 : ℝ) < S.card := by exact_mod_cast þ
  have hδ : 0 < δ := Real.exp_pos _
  have hlog : Real.log (2*(N:ℝ)/S.card) ≤ T := (le_max_right _ _).trans hparam
  have he := (div_le_iff₀ hc).mp ((Real.log_le_iff_le_exp (by positivity)).mp hlog)
  have hd : 2*(N:ℝ)*δ ≤ S.card := by
    rw [show δ = (Real.exp T)⁻¹ by simp [δ,Real.exp_neg], ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos T)).mpr (by simpa only [mul_comm] using he)
  have Ᾱ : N < M := by
    by_contra! ή
    have hsize : δ * ((N+1:ℕ):ℝ) ≤ S.card := by
      push_cast
      have h1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      nlinarith only [hd,mul_le_mul_of_nonneg_left h1 hδ.le]
    obtain ⟨P,hP⟩ := Combinatorics.Ο.ᾍ k (by omega)
      δ hδ (N+1) (ή.trans (Nat.le_succ _)) S
      (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp (hsub hx)).2)) hsize
    exact ð ⟨P.start,P.diff,Nat.pos_of_ne_zero P.Ἷ,fun i hi => hP ⟨i,hi⟩⟩
  have hlogpos : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hnm : (N:ℝ) < M := by exact_mod_cast Ᾱ
  linarith [Real.log_le_sub_one_of_pos hNpos,Real.log_le_sub_one_of_pos hlogpos]
