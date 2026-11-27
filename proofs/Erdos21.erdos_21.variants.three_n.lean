import FormalConjectures.ErdosProblems.«21»
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A disproof of the bounded additive error in Erdős Problem 21

The residual cover bound, peeling lemmas, and linearization below are adapted
from Varun Sivashankar's An Improved Lower Bound for the Erdős–Lovász Cover
Number Problem, arXiv:2606.24878v2. The ancillary Lean source is distributed
with the paper under CC BY 4.0. These excerpts have been selected and adapted
to the pinned Mathlib version.
https://arxiv.org/src/2606.24878v2/anc/lean-proof/RequestProject/Theorem1.lean
https://creativecommons.org/licenses/by/4.0/

We apply the finite almost-perfect matching theorem of Sergey Norin and
Raphael Steiner to the dense linear four-uniform residual hypergraph.
The Apache-2.0 notice for their Lean source follows.
-/
/-
Matching proof adapted from LinearHadwiger, commit 9ef0db5fbaba0c4bc15248b9ea83933c262559c1.
Copyright 2026 Sergey Norin and Raphael Steiner.
Source: https://github.com/snorin239/LinearHadwiger/tree/9ef0db5fbaba0c4bc15248b9ea83933c262559c1
Changes: modules combined for a standalone Lean submission and adapted to Lean 4.33.1.

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
-/


section
/- Adapted module: HadwigerLean/Hypergraph/Indexed.lean. -/
/-
Finite multihypergraphs with indexed edge copies.

The edge labels distinguish repeated edges. A residual hypergraph retains the
same ambient vertex and edge label types while changing its active finite sets.
-/

namespace HadwigerLean

/-- A finite hypergraph whose edge copies are indexed by `E`. -/
structure IndexedHypergraph (V E : Type*) where
  vertices : Finset V
  edges : Finset E
  edge : E → Finset V
  edge_subset : ∀ e ∈ edges, edge e ⊆ vertices

namespace IndexedHypergraph

variable {V E : Type*} [DecidableEq V]
variable (H : IndexedHypergraph V E)

/-- Number of active copies incident with `v`. -/
def degree (v : V) : ℕ := (H.edges.filter fun e => v ∈ H.edge e).card

/-- Number of active copies incident with both `u` and `v`. -/
def codegree (u v : V) : ℕ :=
  (H.edges.filter fun e => u ∈ H.edge e ∧ v ∈ H.edge e).card

/-- Maximum active degree, zero for an empty vertex set. -/
def maxDegree : ℕ := H.vertices.sup H.degree

/-- Maximum codegree over distinct active vertices. -/
def maxCodegree : ℕ :=
  H.vertices.sup (fun u => (H.vertices.erase u).sup (H.codegree u))

/-- Every active edge copy has cardinality r. -/
def IsUniform (r : ℕ) : Prop := ∀ e ∈ H.edges, (H.edge e).card = r

/-- The active copies in `M` have disjoint vertex sets. -/
def IsMatching (M : Finset E) : Prop :=
  M ⊆ H.edges ∧ Set.Pairwise (M : Set E) (fun e f => Disjoint (H.edge e) (H.edge f))

/-- Vertices covered by a collection of edge copies. -/
def covered (M : Finset E) : Finset V := M.biUnion H.edge

/-- The total shortfall from a proposed degree cap. -/
def degreeDeficit (D : ℕ) : ℕ :=
  H.vertices.sum (fun v => D - H.degree v)

/-- The total excess above a proposed degree cap. -/
def degreeExcess (D : ℕ) : ℕ :=
  H.vertices.sum (fun v => H.degree v - D)

/-- Discard active edge copies, preserving the ambient label types. -/
def restrictEdges (F : Finset E) (hF : F ⊆ H.edges) : IndexedHypergraph V E where
  vertices := H.vertices
  edges := F
  edge := H.edge
  edge_subset := by
    intro e he
    exact H.edge_subset e (hF he)

/-- Induce on a finite vertex set, retaining exactly the edge copies inside it. -/
def induce (U : Finset V) : IndexedHypergraph V E where
  vertices := H.vertices ∩ U
  edges := H.edges.filter (fun e => H.edge e ⊆ U)
  edge := H.edge
  edge_subset := by
    intro e he
    rcases Finset.mem_filter.mp he with ⟨heH, heU⟩
    exact Finset.subset_inter (H.edge_subset e heH) heU

omit [DecidableEq V] in
@[simp] theorem restrictEdges_vertices (F : Finset E) (hF : F ⊆ H.edges) :
    (H.restrictEdges F hF).vertices = H.vertices := rfl

omit [DecidableEq V] in
omit [DecidableEq V] in
@[simp] theorem restrictEdges_edges (F : Finset E) (hF : F ⊆ H.edges) :
    (H.restrictEdges F hF).edges = F := rfl

omit [DecidableEq V] in
@[simp] theorem restrictEdges_edge (F : Finset E) (hF : F ⊆ H.edges) (e : E) :
    (H.restrictEdges F hF).edge e = H.edge e := rfl

theorem restrictEdges_degree_le (F : Finset E) (hF : F ⊆ H.edges) (v : V) :
    (H.restrictEdges F hF).degree v ≤ H.degree v := by
  unfold degree
  simp only [restrictEdges_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hF)

theorem restrictEdges_codegree_le (F : Finset E) (hF : F ⊆ H.edges) (u v : V) :
    (H.restrictEdges F hF).codegree u v ≤ H.codegree u v := by
  unfold codegree
  simp only [restrictEdges_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hF)

theorem degree_eq_zero_of_not_mem {v : V} (hv : v ∉ H.vertices) : H.degree v = 0 := by
  classical
  unfold degree
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro e heH hve
  exact hv (H.edge_subset e heH hve)

theorem degree_le_maxDegree {v : V} (hv : v ∈ H.vertices) :
    H.degree v ≤ H.maxDegree := Finset.le_sup hv

theorem codegree_le_maxCodegree {u v : V}
    (hu : u ∈ H.vertices) (hv : v ∈ H.vertices) (hne : u ≠ v) :
    H.codegree u v ≤ H.maxCodegree := by
  unfold maxCodegree
  have hinner : H.codegree u v ≤
      (H.vertices.erase u).sup (H.codegree u) :=
    Finset.le_sup (Finset.mem_erase.mpr ⟨hne.symm, hv⟩)
  exact hinner.trans (Finset.le_sup (f := fun w => (H.vertices.erase w).sup (H.codegree w)) hu)

/-- An active edge of uniform rank at least two gives a positive codegree. -/
theorem maxCodegree_pos_of_maxDegree_pos (H : IndexedHypergraph V E)
    {r : ℕ} (hr : 2 ≤ r) (hunif : H.IsUniform r)
    (hdegree : 0 < H.maxDegree) : 0 < H.maxCodegree := by
  classical
  have hE : H.edges.Nonempty := by
    by_contra h
    have he : H.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [IndexedHypergraph.maxDegree, IndexedHypergraph.degree, he] at hdegree
  obtain ⟨e, he⟩ := hE
  have hcard : 1 < (H.edge e).card := by rw [hunif e he]; omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  have hsub := H.edge_subset e he
  have hcodeg : 0 < H.codegree u v := by
    unfold IndexedHypergraph.codegree
    apply Finset.card_pos.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hu, hv⟩⟩
  exact lt_of_lt_of_le hcodeg
    (H.codegree_le_maxCodegree (hsub hu) (hsub hv) huv)
theorem codegree_le_degree_left (u v : V) : H.codegree u v ≤ H.degree u := by
  unfold codegree degree
  exact Finset.card_le_card (by
    intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2.1⟩)

theorem codegree_le_degree_right (u v : V) : H.codegree u v ≤ H.degree v := by
  unfold codegree degree
  exact Finset.card_le_card (by
    intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2.2⟩)

/-- Counting incidences first by vertex and then by edge copy. -/
theorem sum_degrees_eq_sum_edge_card :
    H.vertices.sum H.degree = H.edges.sum (fun e => (H.edge e).card) := by
  classical
  calc
    H.vertices.sum H.degree =
        H.vertices.sum (fun v => H.edges.sum (fun e => if v ∈ H.edge e then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa only [degree] using
        (Finset.card_filter (fun e => v ∈ H.edge e) H.edges)
    _ = H.edges.sum (fun e => H.vertices.sum
        (fun v => if v ∈ H.edge e then 1 else 0)) := Finset.sum_comm
    _ = H.edges.sum (fun e => (H.edge e).card) := by
      apply Finset.sum_congr rfl
      intro e he
      have hfilter : H.vertices.filter (fun v => v ∈ H.edge e) = H.edge e := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · exact And.right
        · intro hv
          exact ⟨H.edge_subset e he hv, hv⟩
      calc
        H.vertices.sum (fun v => if v ∈ H.edge e then 1 else 0) =
            (H.vertices.filter (fun v => v ∈ H.edge e)).card :=
          (Finset.card_filter (fun v => v ∈ H.edge e) H.vertices).symm
        _ = (H.edge e).card := congrArg Finset.card hfilter

/-- The incidence count is r times the number of active copies. -/
theorem sum_degrees_uniform {r : ℕ} (hunif : H.IsUniform r) :
    H.vertices.sum H.degree = r * H.edges.card := by
  rw [H.sum_degrees_eq_sum_edge_card]
  calc
    H.edges.sum (fun e => (H.edge e).card) =
        H.edges.sum (fun _ => r) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hunif e he
    _ = r * H.edges.card := by simp [mul_comm]

/-- Count pairs consisting of an edge copy through v and a vertex on it. -/
theorem sum_codegrees_eq_sum_incident_edge_card (v : V) :
    H.vertices.sum (H.codegree v) =
      (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e => (H.edge e).card) := by
  classical
  calc
    H.vertices.sum (H.codegree v) =
        H.vertices.sum (fun u => H.edges.sum
          (fun e => if v ∈ H.edge e ∧ u ∈ H.edge e then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro u hu
      simpa only [codegree] using
        (Finset.card_filter (fun e => v ∈ H.edge e ∧ u ∈ H.edge e) H.edges)
    _ = H.edges.sum (fun e => H.vertices.sum
        (fun u => if v ∈ H.edge e ∧ u ∈ H.edge e then 1 else 0)) :=
      Finset.sum_comm
    _ = H.edges.sum (fun e => if v ∈ H.edge e then (H.edge e).card else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hve : v ∈ H.edge e
      · simp only [hve, true_and, ite_true]
        have hfilter : H.vertices.filter (fun u => u ∈ H.edge e) = H.edge e := by
          ext u
          simp only [Finset.mem_filter]
          constructor
          · exact And.right
          · intro hu
            exact ⟨H.edge_subset e he hu, hu⟩
        calc
          H.vertices.sum (fun u => if u ∈ H.edge e then 1 else 0) =
              (H.vertices.filter (fun u => u ∈ H.edge e)).card :=
            (Finset.card_filter (fun u => u ∈ H.edge e) H.vertices).symm
          _ = (H.edge e).card := congrArg Finset.card hfilter
      · simp [hve]
    _ = (H.edges.filter (fun e => v ∈ H.edge e)).sum
        (fun e => (H.edge e).card) := by
      rw [Finset.sum_ite]
      simp

/-- Total codegree at v, including the diagonal, is r times its degree. -/
theorem sum_codegrees_uniform {r : ℕ} (hunif : H.IsUniform r) (v : V) :
    H.vertices.sum (H.codegree v) = r * H.degree v := by
  rw [H.sum_codegrees_eq_sum_incident_edge_card]
  calc
    (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e => (H.edge e).card) =
        (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun _ => r) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hunif e (Finset.mem_filter.mp he).1
    _ = r * H.degree v := by simp [degree, mul_comm]

/-- Off-diagonal codegrees account for the other vertices on incident edges. -/
theorem sum_codegrees_offdiag_add_degree {r : ℕ}
    (hunif : H.IsUniform r) {v : V} (hv : v ∈ H.vertices) :
    (H.vertices.erase v).sum (H.codegree v) + H.degree v =
      r * H.degree v := by
  have hdiag : H.codegree v v = H.degree v := by
    simp [codegree, degree]
  calc
    (H.vertices.erase v).sum (H.codegree v) + H.degree v =
        H.vertices.sum (H.codegree v) := by
      rw [← hdiag]
      exact Finset.sum_erase_add H.vertices (H.codegree v) hv
    _ = r * H.degree v := H.sum_codegrees_uniform hunif v
/-- The overlapping-edge contribution to the variance is controlled by
maximum codegree and degree. -/
theorem sum_codegree_sq_le {r B D : ℕ} (hunif : H.IsUniform r)
    {v : V} (hv : v ∈ H.vertices)
    (hB : H.maxCodegree ≤ B) (hD : H.degree v ≤ D) :
    (H.vertices.erase v).sum (fun u => H.codegree v u * H.codegree v u) ≤
      B * (r * D) := by
  have hpoint : ∀ u ∈ H.vertices.erase v,
      H.codegree v u * H.codegree v u ≤ B * H.codegree v u := by
    intro u hu
    have hcodeg : H.codegree v u ≤ B :=
      (H.codegree_le_maxCodegree hv (Finset.mem_erase.mp hu).2
        (Finset.mem_erase.mp hu).1.symm).trans hB
    exact Nat.mul_le_mul_right (H.codegree v u) hcodeg
  have hoff : (H.vertices.erase v).sum (H.codegree v) ≤ r * H.degree v := by
    have h := H.sum_codegrees_offdiag_add_degree hunif hv
    omega
  calc
    (H.vertices.erase v).sum (fun u => H.codegree v u * H.codegree v u) ≤
        (H.vertices.erase v).sum (fun u => B * H.codegree v u) :=
      Finset.sum_le_sum hpoint
    _ = B * (H.vertices.erase v).sum (H.codegree v) := by
      rw [Finset.mul_sum]
    _ ≤ B * (r * H.degree v) := Nat.mul_le_mul_left B hoff
    _ ≤ B * (r * D) :=
      Nat.mul_le_mul_left B (Nat.mul_le_mul_left r hD)
/-- The paper's total degree deficit, expressed without truncated subtraction. -/
theorem degreeDeficit_add_edges {r D : ℕ} (hunif : H.IsUniform r)
    (hD : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    H.degreeDeficit D + r * H.edges.card = H.vertices.card * D := by
  have hsum : H.degreeDeficit D + H.vertices.sum H.degree =
      H.vertices.card * D := by
    unfold degreeDeficit
    rw [← Finset.sum_add_distrib]
    calc
      H.vertices.sum (fun v => D - H.degree v + H.degree v) =
          H.vertices.sum (fun _ => D) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact Nat.sub_add_cancel (hD v hv)
      _ = H.vertices.card * D := by simp
  rwa [H.sum_degrees_uniform hunif] at hsum

/-- A uniform matching covers exactly r vertices per selected copy. -/
theorem covered_card_of_matching {r : ℕ} (hunif : H.IsUniform r)
    {M : Finset E} (hM : H.IsMatching M) :
    (H.covered M).card = r * M.card := by
  classical
  have hdisj : (M : Set E).PairwiseDisjoint H.edge := by
    intro e he f hf hne
    exact hM.2 he hf hne
  rw [covered, Finset.card_biUnion hdisj]
  calc
    M.sum (fun e => (H.edge e).card) = M.sum (fun _ => r) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hunif e (hM.1 he)
    _ = r * M.card := by simp [mul_comm]
section Trimming
variable [DecidableEq E]

/-- Removing an incident copy lowers a vertex degree by exactly one. -/
theorem degree_restrict_erase_add_one {e : E} (he : e ∈ H.edges)
    {v : V} (hve : v ∈ H.edge e) :
    (H.restrictEdges (H.edges.erase e) (Finset.erase_subset e H.edges)).degree v + 1 =
      H.degree v := by
  classical
  unfold degree
  simp only [restrictEdges_edges, Finset.filter_erase]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨he, hve⟩)

/-- Removing an edge incident to an overfull vertex strictly lowers total excess. -/
theorem degreeExcess_restrict_erase_lt {D : ℕ} {e : E} (he : e ∈ H.edges)
    {v : V} (hv : v ∈ H.vertices) (hve : v ∈ H.edge e)
    (hover : D < H.degree v) :
    (H.restrictEdges (H.edges.erase e) (Finset.erase_subset e H.edges)).degreeExcess D <
      H.degreeExcess D := by
  classical
  let H' := H.restrictEdges (H.edges.erase e) (Finset.erase_subset e H.edges)
  have hle : ∀ u ∈ H.vertices, H'.degree u - D ≤ H.degree u - D := by
    intro u hu
    exact Nat.sub_le_sub_right (H.restrictEdges_degree_le _ _ u) D
  have hdeg : H'.degree v + 1 = H.degree v :=
    H.degree_restrict_erase_add_one he hve
  have hvlt : H'.degree v - D < H.degree v - D := by omega
  exact Finset.sum_lt_sum hle ⟨v, hv, hvlt⟩
/-- Delete at most the initial total degree excess to obtain a degree cap. -/
theorem exists_degree_trim (D : ℕ) :
    ∃ F : Finset E, ∃ hF : F ⊆ H.edges,
      (∀ v ∈ H.vertices, (H.restrictEdges F hF).degree v ≤ D) ∧
      H.edges.card ≤ F.card + H.degreeExcess D := by
  classical
  have aux : ∀ n, ∀ K : IndexedHypergraph V E,
      K.degreeExcess D = n →
      ∃ F : Finset E, ∃ hF : F ⊆ K.edges,
        (∀ v ∈ K.vertices, (K.restrictEdges F hF).degree v ≤ D) ∧
        K.edges.card ≤ F.card + K.degreeExcess D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hKn
      by_cases hcap : ∀ v ∈ K.vertices, K.degree v ≤ D
      · refine ⟨K.edges, Finset.Subset.rfl, ?_, ?_⟩
        · intro v hv
          exact le_trans (K.restrictEdges_degree_le _ _ v) (hcap v hv)
        · simp
      · push Not at hcap
        obtain ⟨v, hv, hover⟩ := hcap
        have hpos : 0 < K.degree v := by omega
        have hne : (K.edges.filter (fun e => v ∈ K.edge e)).Nonempty :=
          Finset.card_pos.mp hpos
        obtain ⟨e, heinc⟩ := hne
        obtain ⟨he, hve⟩ := Finset.mem_filter.mp heinc
        let K' := K.restrictEdges (K.edges.erase e) (Finset.erase_subset e K.edges)
        have hstrict : K'.degreeExcess D < K.degreeExcess D :=
          K.degreeExcess_restrict_erase_lt he hv hve hover
        have hsmall : K'.degreeExcess D < n := by omega
        obtain ⟨F, hF, hcapF, hboundF⟩ := ih _ hsmall K' rfl
        have hF' : F ⊆ K.edges := hF.trans (Finset.erase_subset e K.edges)
        refine ⟨F, hF', ?_, ?_⟩
        · intro u hu
          have hu' : u ∈ K'.vertices := hu
          have h := hcapF u hu'
          change (F.filter (fun f => u ∈ K.edge f)).card ≤ D at h ⊢
          exact h
        · have hcard : K'.edges.card + 1 = K.edges.card :=
            Finset.card_erase_add_one he
          omega
  exact aux (H.degreeExcess D) H rfl
end Trimming

@[simp] theorem induce_vertices (U : Finset V) :
    (H.induce U).vertices = H.vertices ∩ U := rfl

@[simp] theorem induce_edges (U : Finset V) :
    (H.induce U).edges = H.edges.filter (fun e => H.edge e ⊆ U) := rfl

@[simp] theorem induce_edge (U : Finset V) (e : E) :
    (H.induce U).edge e = H.edge e := rfl

theorem induce_edges_subset (U : Finset V) :
    (H.induce U).edges ⊆ H.edges := Finset.filter_subset _ _

theorem induce_uniform {r : ℕ} (hunif : H.IsUniform r) (U : Finset V) :
    (H.induce U).IsUniform r := by
  intro e he
  exact hunif e (H.induce_edges_subset U he)

theorem induce_degree_le (U : Finset V) (v : V) :
    (H.induce U).degree v ≤ H.degree v := by
  unfold degree
  simp only [induce_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (H.induce_edges_subset U))

theorem induce_codegree_le (U : Finset V) (u v : V) :
    (H.induce U).codegree u v ≤ H.codegree u v := by
  unfold codegree
  simp only [induce_edges]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (H.induce_edges_subset U))

theorem covered_subset_vertices {M : Finset E} (hM : M ⊆ H.edges) :
    H.covered M ⊆ H.vertices := by
  intro v hv
  obtain ⟨e, heM, hve⟩ := Finset.mem_biUnion.mp hv
  exact H.edge_subset e (hM heM) hve
end IndexedHypergraph

end HadwigerLean

/- Adapted module: HadwigerLean/Probability/FiniteBernoulli.lean. -/
/-
# Finite independent Bernoulli marking

An elementary finite probability space for independent marks indexed by an arbitrary finite type.
The index can be the edge-copy type of an indexed multihypergraph, so repeated edges remain
independent. Probabilities and expectations are finite real sums.
-/

namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Probability weight of one configuration of independent Bernoulli marks. -/
noncomputable def weight (p : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then p i else 1 - p i

/-- Probability of an event in the finite Bernoulli product space. -/
noncomputable def prob (p : ι → ℝ) (A : Set (ι → Bool)) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ A then weight p ω else 0

/-- Expectation in the finite Bernoulli product space. -/
noncomputable def expect (p : ι → ℝ) (X : (ι → Bool) → ℝ) : ℝ := by
  classical
  exact ∑ ω, weight p ω * X ω

theorem sum_weight (p : ι → ℝ) : (∑ ω : ι → Bool, weight p ω) = 1 := by
  classical
  calc
    (∑ ω : ι → Bool, weight p ω) =
        ∏ i, ∑ b : Bool, if b then p i else 1 - p i := by
      simpa only [weight] using
        (Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1 - p i)).symm
    _ = 1 := by simp

omit [DecidableEq ι] in
theorem weight_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (ω : ι → Bool) : 0 ≤ weight p ω := by
  classical
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (hp i).1
  · linarith [(hp i).2]

theorem prob_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A : Set (ι → Bool)) : 0 ≤ prob p A := by
  classical
  unfold prob
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs with h
  · exact weight_nonneg p hp ω
  · exact le_rfl

/-- Exact factorization of an expectation of coordinate-wise factors. -/
theorem expect_prod (p : ι → ℝ) (f : ι → Bool → ℝ) :
    expect p (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (p i * f i true + (1 - p i) * f i false) := by
  classical
  calc
    expect p (fun ω => ∏ i, f i (ω i)) =
        ∑ ω : ι → Bool, ∏ i, (if ω i then p i else 1 - p i) * f i (ω i) := by
      simp only [expect, weight, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, (if b then p i else 1 - p i) * f i b := by
      simpa only using
        (Fintype.prod_sum
          (fun i (b : Bool) => (if b then p i else 1 - p i) * f i b)).symm
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) := by
      simp

/-- Probability that all marks in a specified finite set are absent. -/
theorem prob_all_false (p : ι → ℝ) (S : Finset ι) :
    prob p {ω | ∀ i ∈ S, ω i = false} = ∏ i ∈ S, (1 - p i) := by
  classical
  let f : ι → Bool → ℝ := fun i b => if i ∈ S then (if b then 0 else 1) else 1
  have hind (ω : ι → Bool) :
      (if (∀ i ∈ S, ω i = false) then (1 : ℝ) else 0) = ∏ i, f i (ω i) := by
    by_cases h : ∀ i ∈ S, ω i = false
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS, h i hS]
      · simp [f, hS]
    · obtain ⟨i, hi, hω⟩ : ∃ i ∈ S, ω i = true := by
        by_contra hx
        apply h
        intro j hj
        cases hjω : ω j
        · simp
        · exact False.elim (hx ⟨j, hj, hjω⟩)
      have hz : f i (ω i) = 0 := by simp [f, hi, hω]
      rw [if_neg h]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) hz).symm
  calc
    prob p {ω | ∀ i ∈ S, ω i = false} =
        expect p (fun ω => ∏ i, f i (ω i)) := by
      unfold prob expect
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∀ i ∈ S, ω i = false
      · have hf : (∏ i, f i (ω i)) = 1 := by rw [← hind ω, if_pos h]
        have hmem : ω ∈ {ω | ∀ i ∈ S, ω i = false} := h
        simp only [if_pos hmem, hf, mul_one]
      · have hf : (∏ i, f i (ω i)) = 0 := by rw [← hind ω, if_neg h]
        have hmem : ω ∉ {ω | ∀ i ∈ S, ω i = false} := h
        simp only [if_neg hmem, hf, mul_zero]
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) :=
      expect_prod p f
    _ = ∏ i, (if i ∈ S then 1 - p i else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS]
      · simp only [f, if_neg hS, mul_one]
        ring
    _ = ∏ i ∈ S, (1 - p i) := by simp [Finset.prod_ite_mem]

/-- Bernoulli mark probability with Poisson zero probability exp(-rate). -/
noncomputable def expMarkProbability (rate : ι → ℝ) (i : ι) : ℝ :=
  1 - Real.exp (-rate i)

omit [Fintype ι] [DecidableEq ι] in
theorem expMarkProbability_bounds (rate : ι → ℝ) (hrate : ∀ i, 0 ≤ rate i)
    (i : ι) : 0 ≤ expMarkProbability rate i ∧ expMarkProbability rate i ≤ 1 := by
  have h₁ : Real.exp (-rate i) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hrate i))
  have h₂ : 0 < Real.exp (-rate i) := Real.exp_pos _
  unfold expMarkProbability
  constructor <;> linarith

/-- Exact joint survival probability under Poisson-zero Bernoulli marks. -/
theorem prob_all_false_exp (rate : ι → ℝ) (S : Finset ι) :
    prob (expMarkProbability rate) {ω | ∀ i ∈ S, ω i = false} =
      Real.exp (-(∑ i ∈ S, rate i)) := by
  rw [prob_all_false]
  calc
    (∏ i ∈ S, (1 - expMarkProbability rate i)) =
        ∏ i ∈ S, Real.exp (-rate i) := by
      apply Finset.prod_congr rfl
      intro i hi
      unfold expMarkProbability
      ring
    _ = Real.exp (∑ i ∈ S, -rate i) := (Real.exp_sum S (fun i => -rate i)).symm
    _ = Real.exp (-(∑ i ∈ S, rate i)) := by rw [Finset.sum_neg_distrib]

/-- Number of present marks in a finite set, as a real number. -/
noncomputable def count (S : Finset ι) (ω : ι → Bool) : ℝ :=
  ∑ i ∈ S, if ω i then 1 else 0

/-- Mean number of present marks in a finite set. -/
noncomputable def mean (p : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, p i

/-- Expected value of a single Bernoulli mark. -/
theorem expect_mark (p : ι → ℝ) (i : ι) :
    expect p (fun ω => if ω i then 1 else 0) = p i := by
  classical
  let f : ι → Bool → ℝ := fun j b => if j = i then (if b then 1 else 0) else 1
  have hrepr (ω : ι → Bool) :
      (if ω i then (1 : ℝ) else 0) = ∏ j, f j (ω j) := by
    simp [f]
  calc
    expect p (fun ω => if ω i then 1 else 0) =
        expect p (fun ω => ∏ j, f j (ω j)) := by
      congr 1
      funext ω
      exact hrepr ω
    _ = ∏ j, (p j * f j true + (1 - p j) * f j false) := expect_prod p f
    _ = p i := by
      have hfactor (j : ι) :
          p j * f j true + (1 - p j) * f j false =
            if j = i then p i else 1 := by
        by_cases h : j = i
        · subst j
          simp [f]
        · simp only [f, if_neg h, mul_one]
          ring
      simp_rw [hfactor]
      simp [Finset.prod_ite_eq']

theorem expect_count (p : ι → ℝ) (S : Finset ι) :
    expect p (count S) = mean p S := by
  classical
  unfold expect count mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [expect] using expect_mark p i

omit [Fintype ι] [DecidableEq ι] in
/-- Exponential of a sampled count is a product of coordinate factors. -/
theorem exp_mul_count (S : Finset ι) (t : ℝ) (ω : ι → Bool) :
    Real.exp (t * count S ω) =
      ∏ i ∈ S, (if ω i then Real.exp t else 1) := by
  calc
    Real.exp (t * count S ω) =
        Real.exp (∑ i ∈ S, t * (if ω i then (1 : ℝ) else 0)) := by
      simp only [count, Finset.mul_sum]
    _ = ∏ i ∈ S, Real.exp (t * (if ω i then (1 : ℝ) else 0)) :=
      Real.exp_sum S _
    _ = ∏ i ∈ S, (if ω i then Real.exp t else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      cases h : ω i <;> simp

/-- Exact moment-generating function of the sampled count. -/
theorem expect_exp_count (p : ι → ℝ) (S : Finset ι) (t : ℝ) :
    expect p (fun ω => Real.exp (t * count S ω)) =
      ∏ i ∈ S, (1 - p i + p i * Real.exp t) := by
  classical
  let f : ι → Bool → ℝ :=
    fun i b => if i ∈ S then (if b then Real.exp t else 1) else 1
  have hrepr (ω : ι → Bool) :
      Real.exp (t * count S ω) = ∏ i, f i (ω i) := by
    rw [exp_mul_count]
    simp [f, Finset.prod_ite_mem]
  calc
    expect p (fun ω => Real.exp (t * count S ω)) =
        expect p (fun ω => ∏ i, f i (ω i)) := by
      congr 1
      funext ω
      exact hrepr ω
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) := expect_prod p f
    _ = ∏ i, (if i ∈ S then 1 - p i + p i * Real.exp t else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · simp only [f, if_pos hS, Bool.false_eq_true, ↓reduceIte, mul_one]
        ring
      · simp only [f, if_neg hS, mul_one]
        ring
    _ = ∏ i ∈ S, (1 - p i + p i * Real.exp t) := by
      simp [Finset.prod_ite_mem]

/-- A mean-sensitive MGF bound for a finite Bernoulli sum. -/
theorem expect_exp_count_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t : ℝ) :
    expect p (fun ω => Real.exp (t * count S ω)) ≤
      Real.exp (mean p S * (Real.exp t - 1)) := by
  rw [expect_exp_count]
  calc
    (∏ i ∈ S, (1 - p i + p i * Real.exp t)) =
        ∏ i ∈ S, (1 + p i * (Real.exp t - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ ≤ ∏ i ∈ S, Real.exp (p i * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i hi
        have h₁ : 0 ≤ 1 - p i := by linarith [(hp i).2]
        have h₂ : 0 ≤ p i * Real.exp t :=
          mul_nonneg (hp i).1 (Real.exp_pos t).le
        convert add_nonneg h₁ h₂ using 1; ring
      · intro i hi
        simpa [add_comm] using Real.add_one_le_exp (p i * (Real.exp t - 1))
    _ = Real.exp (∑ i ∈ S, p i * (Real.exp t - 1)) :=
      (Real.exp_sum S (fun i => p i * (Real.exp t - 1))).symm
    _ = Real.exp (mean p S * (Real.exp t - 1)) := by
      congr 1
      simp [mean, Finset.sum_mul]

/-- Finite weighted Markov inequality for an event and a nonnegative witness. -/
theorem prob_le_expect (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A : Set (ι → Bool)) (X : (ι → Bool) → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hA : ∀ ω ∈ A, 1 ≤ X ω) :
    prob p A ≤ expect p X := by
  classical
  unfold prob expect
  apply Finset.sum_le_sum
  intro ω hω
  by_cases h : ω ∈ A
  · simp only [if_pos h]
    have hw := weight_nonneg p hp ω
    have hx := hA ω h
    nlinarith
  · simp only [if_neg h]
    exact mul_nonneg (weight_nonneg p hp ω) (hX ω)

/-- Mean-sensitive Chernoff bound, with either tail selected by the sign of `t`. -/
theorem prob_count_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t threshold : ℝ) :
    prob p {ω | t * threshold ≤ t * count S ω} ≤
      Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
  let X : (ι → Bool) → ℝ :=
    fun ω => Real.exp (-t * threshold) * Real.exp (t * count S ω)
  have hX (ω : ι → Bool) : 0 ≤ X ω :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hA (ω : ι → Bool)
      (hω : ω ∈ {ω | t * threshold ≤ t * count S ω}) : 1 ≤ X ω := by
    have harg : 0 ≤ -t * threshold + t * count S ω := by
      dsimp at hω
      linarith
    calc
      (1 : ℝ) ≤ Real.exp (-t * threshold + t * count S ω) :=
        Real.one_le_exp harg
      _ = X ω := by rw [Real.exp_add]
  calc
    prob p {ω | t * threshold ≤ t * count S ω} ≤ expect p X :=
      prob_le_expect p hp _ X hX hA
    _ = Real.exp (-t * threshold) *
        expect p (fun ω => Real.exp (t * count S ω)) := by
      unfold expect X
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ ≤ Real.exp (-t * threshold) *
        Real.exp (mean p S * (Real.exp t - 1)) :=
      mul_le_mul_of_nonneg_left (expect_exp_count_le p hp S t) (Real.exp_pos _).le
    _ = Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
      rw [Real.exp_add]

theorem prob_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {A B : Set (ι → Bool)} (hAB : A ⊆ B) : prob p A ≤ prob p B := by
  classical
  unfold prob
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : ω ∈ A
  · have hB : ω ∈ B := hAB hA
    simp [hA, hB]
  · by_cases hB : ω ∈ B
    · simp only [if_neg hA, if_pos hB]
      exact weight_nonneg p hp ω
    · simp [hA, hB]

/-- Upper-tail Chernoff bound with a positive exponential parameter. -/
theorem prob_count_ge_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t threshold : ℝ) (ht : 0 ≤ t) :
    prob p {ω | threshold ≤ count S ω} ≤
      Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
  apply (prob_mono p hp ?_).trans (prob_count_chernoff p hp S t threshold)
  intro ω hω
  exact mul_le_mul_of_nonneg_left hω ht

/-- Lower-tail Chernoff bound with a negative exponential parameter. -/
theorem prob_count_le_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (t threshold : ℝ) (ht : t ≤ 0) :
    prob p {ω | count S ω ≤ threshold} ≤
      Real.exp (-t * threshold + mean p S * (Real.exp t - 1)) := by
  apply (prob_mono p hp ?_).trans (prob_count_chernoff p hp S t threshold)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω ht

omit [Fintype ι] [DecidableEq ι] in
theorem mean_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) : 0 ≤ mean p S := by
  unfold mean
  exact Finset.sum_nonneg (fun i hi => (hp i).1)

/-- Quadratic Chernoff form for |t| ≤ 1. The exponent scales with the mean,
not the number of possible marks. -/
theorem prob_count_chernoff_quadratic (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (t threshold : ℝ) (ht : |t| ≤ 1) :
    prob p {ω | t * threshold ≤ t * count S ω} ≤
      Real.exp (-t * threshold + mean p S * (t + t ^ 2)) := by
  have hTaylor := Real.abs_exp_sub_one_sub_id_le ht
  have hExp : Real.exp t - 1 ≤ t + t ^ 2 := by
    have h := (abs_le.mp hTaylor).2
    linarith
  have harg :
      -t * threshold + mean p S * (Real.exp t - 1) ≤
        -t * threshold + mean p S * (t + t ^ 2) := by
    linarith [mul_le_mul_of_nonneg_left hExp (mean_nonneg p hp S)]
  exact (prob_count_chernoff p hp S t threshold).trans
    (Real.exp_le_exp.mpr harg)

theorem prob_univ (p : ι → ℝ) : prob p Set.univ = 1 := by
  classical
  simpa [prob] using sum_weight p

theorem prob_union_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A B : Set (ι → Bool)) :
    prob p (A ∪ B) ≤ prob p A + prob p B := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [hA, hB]; nlinarith [weight_nonneg p hp ω]

/-- Union bound over a finite family of bad events. -/
theorem prob_biUnion_le {κ : Type*} (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset κ) (A : κ → Set (ι → Bool)) :
    prob p (⋃ j ∈ s, A j) ≤ ∑ j ∈ s, prob p (A j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [prob]
  | @insert j s hjs ih =>
      have hset : (⋃ k ∈ insert j s, A k) = A j ∪ ⋃ k ∈ s, A k := by
        ext ω
        simp
      rw [hset, Finset.sum_insert hjs]
      have hUnion := prob_union_le p hp (A j) (⋃ k ∈ s, A k)
      linarith

/-- If a bad event has probability less than one, some configuration avoids it. -/
theorem exists_not_mem_of_prob_lt_one (p : ι → ℝ)
    (A : Set (ι → Bool)) (hA : prob p A < 1) :
    ∃ ω, ω ∉ A := by
  by_contra h
  have hfull : A = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    by_contra hω
    exact h ⟨ω, hω⟩
  rw [hfull, prob_univ] at hA
  exact (lt_irrefl (1 : ℝ)) hA

/-- Real indicator of an event in the finite sample space. -/
noncomputable def eventIndicator (A : Set (ι → Bool)) (ω : ι → Bool) : ℝ := by
  classical
  exact if ω ∈ A then 1 else 0

theorem expect_eventIndicator (p : ι → ℝ) (A : Set (ι → Bool)) :
    expect p (eventIndicator A) = prob p A := by
  classical
  unfold expect prob eventIndicator
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : ω ∈ A <;> simp [h]

/-- Finite linearity of expectation. -/
theorem expect_sum {κ : Type*} (p : ι → ℝ) (s : Finset κ)
    (X : κ → (ι → Bool) → ℝ) :
    expect p (fun ω => ∑ j ∈ s, X j ω) =
      ∑ j ∈ s, expect p (X j) := by
  classical
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Probability that every mark in a finite set is present. -/
theorem prob_all_true (p : ι → ℝ) (S : Finset ι) :
    prob p {ω | ∀ i ∈ S, ω i = true} = ∏ i ∈ S, p i := by
  classical
  let f : ι → Bool → ℝ := fun i b => if i ∈ S then (if b then 1 else 0) else 1
  have hind (ω : ι → Bool) :
      (if (∀ i ∈ S, ω i = true) then (1 : ℝ) else 0) = ∏ i, f i (ω i) := by
    by_cases h : ∀ i ∈ S, ω i = true
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS, h i hS]
      · simp [f, hS]
    · obtain ⟨i, hi, hω⟩ : ∃ i ∈ S, ω i = false := by
        by_contra hx
        apply h
        intro j hj
        cases hjω : ω j
        · exact False.elim (hx ⟨j, hj, hjω⟩)
        · simp
      have hz : f i (ω i) = 0 := by simp [f, hi, hω]
      rw [if_neg h]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) hz).symm
  calc
    prob p {ω | ∀ i ∈ S, ω i = true} =
        expect p (fun ω => ∏ i, f i (ω i)) := by
      unfold prob expect
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∀ i ∈ S, ω i = true
      · have hf : (∏ i, f i (ω i)) = 1 := by rw [← hind ω, if_pos h]
        have hmem : ω ∈ {ω | ∀ i ∈ S, ω i = true} := h
        simp only [if_pos hmem, hf, mul_one]
      · have hf : (∏ i, f i (ω i)) = 0 := by rw [← hind ω, if_neg h]
        have hmem : ω ∉ {ω | ∀ i ∈ S, ω i = true} := h
        simp only [if_neg hmem, hf, mul_zero]
    _ = ∏ i, (p i * f i true + (1 - p i) * f i false) :=
      expect_prod p f
    _ = ∏ i, (if i ∈ S then p i else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · simp [f, hS]
      · simp only [f, if_neg hS, mul_one]
        ring
    _ = ∏ i ∈ S, p i := by simp [Finset.prod_ite_mem]

/-- Two distinct marks occur jointly with the product of their probabilities. -/
theorem prob_two_true (p : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    prob p {ω | ω i = true ∧ ω j = true} = p i * p j := by
  classical
  have hset :
      {ω : ι → Bool | ω i = true ∧ ω j = true} =
        {ω | ∀ k ∈ ({i, j} : Finset ι), ω k = true} := by
    ext ω
    simp
  rw [hset, prob_all_true]
  simp [hij]

end HadwigerLean.FiniteBernoulli
























namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite weighted Cauchy–Schwarz: the mean absolute value is bounded by
the square root of the second moment. -/
theorem expect_abs_le_sqrt_expect_sq (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (X : (ι → Bool) → ℝ) :
    expect p (fun ω => |X ω|) ≤
      Real.sqrt (expect p (fun ω => (X ω)^2)) := by
  classical
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset (ι → Bool)))
    (r := fun ω => weight p ω * |X ω|)
    (f := fun ω => weight p ω)
    (g := fun ω => weight p ω * (X ω)^2)
    (fun ω hω => weight_nonneg p hp ω)
    (fun ω hω => mul_nonneg (weight_nonneg p hp ω) (sq_nonneg _))
    (fun ω hω => by rw [mul_pow, sq_abs]; nlinarith)
  have hsq : (expect p (fun ω => |X ω|))^2 ≤
      expect p (fun ω => (X ω)^2) := by
    change (∑ ω : ι → Bool, weight p ω * |X ω|)^2 ≤
      ∑ ω : ι → Bool, weight p ω * (X ω)^2
    simpa only [sum_weight p, one_mul] using hcs
  have hnonneg : 0 ≤ expect p (fun ω => |X ω|) := by
    unfold expect
    exact Finset.sum_nonneg (fun ω hω =>
      mul_nonneg (weight_nonneg p hp ω) (abs_nonneg _))
  have hsqrt := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hsqrt

end HadwigerLean.FiniteBernoulli




namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A centered upper-tail bound using a cap on the mean. -/
theorem prob_count_ge_mean_add (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (D s : ℝ) (hD : 0 < D) (hs : 0 ≤ s) (hsD : s ≤ 2 * D)
    (hmean : mean p S ≤ D) :
    prob p {ω | mean p S + s ≤ count S ω} ≤
      Real.exp (-(s ^ 2) / (4 * D)) := by
  let t := s / (2 * D)
  have ht : 0 ≤ t := div_nonneg hs (by positivity)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
    linarith
  have htAbs : |t| ≤ 1 := by simpa [abs_of_nonneg ht] using ht1
  have hbase := prob_count_chernoff_quadratic p hp S t (mean p S + s) htAbs
  have hsubset :
      {ω | mean p S + s ≤ count S ω} ⊆
        {ω | t * (mean p S + s) ≤ t * count S ω} := by
    intro ω hω
    exact mul_le_mul_of_nonneg_left hω ht
  have hfirst := (prob_mono p hp hsubset).trans hbase
  have harg :
      -t * (mean p S + s) + mean p S * (t + t ^ 2) ≤
        -(s ^ 2) / (4 * D) := by
    have hsq := mul_le_mul_of_nonneg_right hmean (sq_nonneg t)
    have hid :
        -t * (mean p S + s) + mean p S * (t + t ^ 2) =
          -t * s + mean p S * t ^ 2 := by ring
    have hcalc : -t * s + D * t ^ 2 = -(s ^ 2) / (4 * D) := by
      dsimp [t]
      field_simp
      ring
    rw [hid]
    rw [← hcalc]
    linarith
  exact hfirst.trans (Real.exp_le_exp.mpr harg)

end HadwigerLean.FiniteBernoulli
namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A centered lower-tail bound using a cap on the mean. -/
theorem prob_count_le_mean_sub (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (D s : ℝ) (hD : 0 < D) (hs : 0 ≤ s) (hsD : s ≤ 2 * D)
    (hmean : mean p S ≤ D) :
    prob p {ω | count S ω ≤ mean p S - s} ≤
      Real.exp (-(s ^ 2) / (4 * D)) := by
  let t := -(s / (2 * D))
  have ht : t ≤ 0 := by
    dsimp [t]
    exact neg_nonpos.mpr (div_nonneg hs (by positivity))
  have htAbs : |t| ≤ 1 := by
    have hbound : s / (2 * D) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
      linarith
    change |-(s / (2 * D))| ≤ 1
    rw [abs_neg, abs_of_nonneg (div_nonneg hs (by positivity))]
    exact hbound
  have hbase := prob_count_chernoff_quadratic p hp S t (mean p S - s) htAbs
  have hsubset :
      {ω | count S ω ≤ mean p S - s} ⊆
        {ω | t * (mean p S - s) ≤ t * count S ω} := by
    intro ω hω
    exact mul_le_mul_of_nonpos_left hω ht
  have hfirst := (prob_mono p hp hsubset).trans hbase
  have harg :
      -t * (mean p S - s) + mean p S * (t + t ^ 2) ≤
        -(s ^ 2) / (4 * D) := by
    have hsq := mul_le_mul_of_nonneg_right hmean (sq_nonneg t)
    have hid :
        -t * (mean p S - s) + mean p S * (t + t ^ 2) =
          t * s + mean p S * t ^ 2 := by ring
    have hcalc : t * s + D * t ^ 2 = -(s ^ 2) / (4 * D) := by
      dsimp [t]
      field_simp
      ring
    rw [hid]
    rw [← hcalc]
    linarith
  exact hfirst.trans (Real.exp_le_exp.mpr harg)

end HadwigerLean.FiniteBernoulli

namespace HadwigerLean.FiniteBernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the mean is at most half the threshold, a fixed exponential tilt
gives an exponentially small upper tail. -/
theorem prob_count_ge_of_mean_le_half (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι)
    (C : ℝ) (hmean : mean p S ≤ C / 2) :
    prob p {ω | C ≤ count S ω} ≤ Real.exp (-C / 8) := by
  have hbase := prob_count_chernoff_quadratic p hp S (1 / 2) C (by norm_num)
  have hsubset :
      {ω | C ≤ count S ω} ⊆
        {ω | (1 / 2 : ℝ) * C ≤ (1 / 2 : ℝ) * count S ω} := by
    intro ω hω
    change C ≤ count S ω at hω
    exact mul_le_mul_of_nonneg_left hω (by norm_num)
  have hfirst := (prob_mono p hp hsubset).trans hbase
  have harg :
      -(1 / 2 : ℝ) * C + mean p S * ((1 / 2 : ℝ) + (1 / 2 : ℝ) ^ 2) ≤
        -C / 8 := by
    linarith
  exact hfirst.trans (Real.exp_le_exp.mpr harg)

end HadwigerLean.FiniteBernoulli

/- Adapted module: HadwigerLean/Quantitative/BackwardPotential.lean. -/
/-
# Backward potential coefficients for matching rounds

The potential weights are defined by elapsed rounds, then read backward
along a fixed finite horizon. This makes the one-round conditional
expectation estimate telescope without constructing a global sample space.
-/

namespace HadwigerLean.Theorem2

/-- Coefficient of the surviving-vertex count after `k` remaining rounds. -/
def potentialCoeff (q c β : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => q * potentialCoeff q c β k + c * (k : ℝ) + β


theorem potentialCoeff_nonneg (q c β : ℝ)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (k : ℕ) : 0 ≤ potentialCoeff q c β k := by
  induction k with
  | zero => norm_num [potentialCoeff]
  | succ k ih =>
      simp only [potentialCoeff]
      positivity
theorem potentialCoeff_le (q c β : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (k : ℕ) :
    potentialCoeff q c β k ≤
      q ^ k + c * (k : ℝ) ^ 2 + β * (k : ℝ) := by
  induction k with
  | zero => simp [potentialCoeff]
  | succ k ih =>
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hpoly : 0 ≤ c * (k : ℝ) ^ 2 + β * (k : ℝ) := by positivity
      have hqpoly :
          q * (c * (k : ℝ) ^ 2 + β * (k : ℝ)) ≤
            c * (k : ℝ) ^ 2 + β * (k : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hpoly]
      have hmul := mul_le_mul_of_nonneg_left ih hq0
      have hslack : 0 ≤ c * ((k : ℝ) + 1) := by positivity
      change q * potentialCoeff q c β k + c * (k : ℝ) + β ≤
        q ^ (k + 1) + c * ((k + 1 : ℕ) : ℝ) ^ 2 +
          β * ((k + 1 : ℕ) : ℝ)
      rw [pow_succ]
      push_cast
      nlinarith [hmul, hqpoly, hslack]

/-- Coefficient of the degree-deficit state at round `i` in a horizon `T`. -/
def lossPotentialB (a : ℝ) (T i : ℕ) : ℝ :=
  a * (T - i : ℕ)

/-- Coefficient of the survivor-count state at round `i`. -/
def lossPotentialA (q δ a β : ℝ) (T i : ℕ) : ℝ :=
  potentialCoeff q (δ * a) β (T - i)


theorem lossPotentialA_nonneg (q δ a β : ℝ)
    (hq : 0 ≤ q) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (T i : ℕ) : 0 ≤ lossPotentialA q δ a β T i := by
  exact potentialCoeff_nonneg q (δ * a) β hq (mul_nonneg hδ ha) hβ _

theorem lossPotentialB_nonneg (a : ℝ) (ha : 0 ≤ a) (T i : ℕ) :
    0 ≤ lossPotentialB a T i := by
  unfold lossPotentialB
  positivity
theorem lossPotentialB_terminal (a : ℝ) (T : ℕ) :
    lossPotentialB a T T = 0 := by simp [lossPotentialB]

theorem lossPotentialA_terminal (q δ a β : ℝ) (T : ℕ) :
    lossPotentialA q δ a β T T = 1 := by
  simp [lossPotentialA, potentialCoeff]

theorem lossPotentialB_step (a : ℝ) {T i : ℕ} (hi : i < T) :
    lossPotentialB a T i = lossPotentialB a T (i + 1) + a := by
  have hsub : T - i = T - (i + 1) + 1 := by omega
  simp only [lossPotentialB, hsub, Nat.cast_add, Nat.cast_one]
  ring

theorem lossPotentialA_step (q δ a β : ℝ) {T i : ℕ} (hi : i < T) :
    lossPotentialA q δ a β T i =
      q * lossPotentialA q δ a β T (i + 1) +
        δ * lossPotentialB a T (i + 1) + β := by
  have hsub : T - i = T - (i + 1) + 1 := by omega
  simp only [lossPotentialA, lossPotentialB, hsub, potentialCoeff]
  ring

theorem lossPotentialA_zero_le (q δ a β : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (T : ℕ) :
    lossPotentialA q δ a β T 0 ≤
      q ^ T + δ * a * (T : ℝ) ^ 2 + β * (T : ℝ) := by
  simpa [lossPotentialA, mul_assoc] using
    potentialCoeff_le q (δ * a) β hq0 hq1 (mul_nonneg hδ ha) hβ T

theorem lossPotentialB_zero (a : ℝ) (T : ℕ) :
    lossPotentialB a T 0 = a * (T : ℝ) := by
  simp [lossPotentialB]

end HadwigerLean.Theorem2

/- Adapted module: HadwigerLean/Hypergraph/AlmostPerfectMatching.lean. -/
/-
Deterministic bookkeeping for the almost-perfect-matching iteration.

Probability will supply a favorable round. Here a round records its surviving
vertices and its accepted disjoint edge copies, and the lemmas track the
vertices that were deleted without being covered.
-/

namespace HadwigerLean

variable {V E : Type*} [DecidableEq V]

/-- The combinatorial data produced by a matching round. -/
structure MatchingRound (H : IndexedHypergraph V E) where
  survivors : Finset V
  survivors_subset : survivors ⊆ H.vertices
  accepted : Finset E
  accepted_matching : H.IsMatching accepted
  survivors_disjoint_accepted : Disjoint survivors (H.covered accepted)

namespace MatchingRound

variable {H : IndexedHypergraph V E} (R : MatchingRound H)

/-- Vertices lost in this round without an accepted matching edge. -/
def waste : Finset V :=
  H.vertices \ (R.survivors ∪ H.covered R.accepted)

/-- The untrimmed hypergraph on surviving vertices. -/
def nextBase : IndexedHypergraph V E := H.induce R.survivors

@[simp] theorem nextBase_vertices : R.nextBase.vertices = R.survivors := by
  simp [nextBase, Finset.inter_eq_right.mpr R.survivors_subset]

theorem accepted_covered_subset : H.covered R.accepted ⊆ H.vertices :=
  H.covered_subset_vertices R.accepted_matching.1

theorem waste_partition_card :
    R.survivors.card + (H.covered R.accepted).card + R.waste.card =
      H.vertices.card := by
  classical
  have hsub : R.survivors ∪ H.covered R.accepted ⊆ H.vertices :=
    Finset.union_subset R.survivors_subset R.accepted_covered_subset
  have hcount := Finset.card_sdiff_add_card_eq_card hsub
  have hdisj := Finset.card_union_of_disjoint R.survivors_disjoint_accepted
  change R.waste.card + (R.survivors ∪ H.covered R.accepted).card =
    H.vertices.card at hcount
  rw [hdisj] at hcount
  omega

section Union
variable [DecidableEq E]

/-- A matching found among survivors extends the accepted matching. -/
theorem matching_union_next {N : Finset E}
    (hN : R.nextBase.IsMatching N) :
    H.IsMatching (R.accepted ∪ N) := by
  classical
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact R.accepted_matching.1 he
    · exact (H.induce_edges_subset R.survivors) (hN.1 he)
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with heM | heN
    · rcases Finset.mem_union.mp hf with hfM | hfN
      · exact R.accepted_matching.2 heM hfM hne
      · apply Finset.disjoint_left.mpr
        intro v hve hvf
        have hvcovered : v ∈ H.covered R.accepted :=
          Finset.mem_biUnion.mpr ⟨e, heM, hve⟩
        have hfu : H.edge f ⊆ R.survivors :=
          (Finset.mem_filter.mp (hN.1 hfN)).2
        exact (Finset.disjoint_left.mp R.survivors_disjoint_accepted)
          (hfu hvf) hvcovered
    · rcases Finset.mem_union.mp hf with hfM | hfN
      · apply Finset.disjoint_right.mpr
        intro v hve hvf
        have hvcovered : v ∈ H.covered R.accepted :=
          Finset.mem_biUnion.mpr ⟨f, hfM, hve⟩
        have heu : H.edge e ⊆ R.survivors :=
          (Finset.mem_filter.mp (hN.1 heN)).2
        exact (Finset.disjoint_left.mp R.survivors_disjoint_accepted)
          (heu hvf) hvcovered
      · exact hN.2 heN hfN hne

/-- The vertices left uncovered after adding a later matching split into
survivors still uncovered and waste from this round. -/
theorem uncovered_partition_card {N : Finset E}
    (hN : N ⊆ R.nextBase.edges) :
    (H.covered (R.accepted ∪ N)).card +
      (R.survivors \ H.covered N).card + R.waste.card =
      H.vertices.card := by
  classical
  have hcoveredN : H.covered N ⊆ R.survivors := by
    intro v hv
    obtain ⟨e, heN, hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp (hN heN)).2 hve
  have hdisj : Disjoint (H.covered R.accepted) (H.covered N) :=
    Finset.disjoint_of_subset_right hcoveredN R.survivors_disjoint_accepted.symm
  have hcoveredUnion :
      H.covered (R.accepted ∪ N) =
        H.covered R.accepted ∪ H.covered N := by
    unfold IndexedHypergraph.covered
    exact Finset.union_biUnion
  have hcountN := Finset.card_sdiff_add_card_eq_card hcoveredN
  have hcountR := R.waste_partition_card
  rw [hcoveredUnion, Finset.card_union_of_disjoint hdisj]
  omega
/-- Trim the induced survivor hypergraph, preserving uniformity and codegree,
while charging every discarded edge to initial degree excess. -/
theorem exists_trimmed_next {r : ℕ} (hunif : H.IsUniform r)
    (D' : ℕ) :
    ∃ K : IndexedHypergraph V E,
      K.vertices = R.survivors ∧
      K.edges ⊆ R.nextBase.edges ∧
      K.IsUniform r ∧
      (∀ v ∈ K.vertices, K.degree v ≤ D') ∧
      (∀ u v, K.codegree u v ≤ H.codegree u v) ∧
      (K.degreeDeficit D' + r * R.nextBase.edges.card ≤
        R.survivors.card * D' +
          r * R.nextBase.degreeExcess D') ∧
      K.edge = H.edge := by
  classical
  obtain ⟨F, hF, hcap, hcount⟩ := R.nextBase.exists_degree_trim D'
  let K := R.nextBase.restrictEdges F hF
  have hKunif : K.IsUniform r := by
    intro e he
    exact (H.induce_uniform hunif R.survivors) e (hF he)
  have hdef := K.degreeDeficit_add_edges hKunif hcap
  have hmul : r * R.nextBase.edges.card ≤
      r * F.card + r * R.nextBase.degreeExcess D' := by
    simpa [Nat.mul_add] using Nat.mul_le_mul_left r hcount
  refine ⟨K, ?_, ?_, hKunif, hcap, ?_, ?_, ?_⟩
  · simp [K]
  · simpa [K] using hF
  · intro u v
    exact (R.nextBase.restrictEdges_codegree_le F hF u v).trans
      (H.induce_codegree_le R.survivors u v)
  · have hvertices : K.vertices = R.survivors := by simp [K]
    have hedges : K.edges = F := rfl
    rw [hvertices, hedges] at hdef
    omega
  · rfl
end Union

end MatchingRound

namespace MatchingRound

section Probability

variable [Fintype V] [Fintype E] [DecidableEq E]

/-- One-round mark rate; inactive ambient labels receive rate zero. -/
noncomputable def rate (H : IndexedHypergraph V E) (a : ℝ) (D : ℕ) :
    E ⊕ V → ℝ
  | Sum.inl e => if e ∈ H.edges then a / (D : ℝ) else 0
  | Sum.inr v =>
      if v ∈ H.vertices then a * (1 - (H.degree v : ℝ) / (D : ℝ)) else 0

omit [Fintype V] [Fintype E] in
theorem rate_nonneg (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (i : E ⊕ V) : 0 ≤ rate H a D i := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  cases i with
  | inl e =>
      by_cases he : e ∈ H.edges
      · simp only [rate, if_pos he]
        exact div_nonneg ha hDr.le
      · simp [rate, he]
  | inr v =>
      by_cases hv : v ∈ H.vertices
      · have hdeg : (H.degree v : ℝ) ≤ (D : ℝ) := by
          exact_mod_cast hcap v hv
        have hratio : (H.degree v : ℝ) / (D : ℝ) ≤ 1 :=
          (div_le_iff₀ hDr).mpr (by simpa using hdeg)
        simp only [rate, if_pos hv]
        exact mul_nonneg ha (sub_nonneg.mpr hratio)
      · simp [rate, hv]

omit [Fintype V] [Fintype E] in
theorem markProbability_bounds (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (i : E ⊕ V) :
    0 ≤ FiniteBernoulli.expMarkProbability (rate H a D) i ∧
      FiniteBernoulli.expMarkProbability (rate H a D) i ≤ 1 :=
  FiniteBernoulli.expMarkProbability_bounds _ (rate_nonneg H ha hD hcap) i
/-- Edge and private marks whose absence lets a vertex survive. -/
def vertexLabels (H : IndexedHypergraph V E) (v : V) : Finset (E ⊕ V) :=
  ((H.edges.filter (fun e => v ∈ H.edge e)).image Sum.inl) ∪ {Sum.inr v}

/-- Survival of a vertex in a single independent-mark round. -/
def vertexSurvives (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (v : V) : Prop :=
  ω (Sum.inr v) = false ∧
    ∀ e ∈ H.edges, v ∈ H.edge e → ω (Sum.inl e) = false

omit [Fintype V] [Fintype E] in
theorem vertexSurvives_iff_all_false (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (v : V) :
    vertexSurvives H ω v ↔ ∀ i ∈ vertexLabels H v, ω i = false := by
  classical
  constructor
  · intro h i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨e, heinc, rfl⟩ := Finset.mem_image.mp hi
      exact h.2 e (Finset.mem_filter.mp heinc).1 (Finset.mem_filter.mp heinc).2
    · have hi' : i = Sum.inr v := Finset.mem_singleton.mp hi
      simpa [hi'] using h.1
  · intro h
    constructor
    · exact h (Sum.inr v) (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _)))
    · intro e he hve
      apply h (Sum.inl e)
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩, rfl⟩

omit [Fintype V] [Fintype E] in
theorem sum_vertexLabels_rate (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    (vertexLabels H v).sum (rate H a D) = a := by
  classical
  have hdisj :
      Disjoint ((H.edges.filter (fun e => v ∈ H.edge e)).image Sum.inl)
        ({Sum.inr v} : Finset (E ⊕ V)) := by
    apply Finset.disjoint_singleton_right.mpr
    intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    cases heq
  unfold vertexLabels
  rw [Finset.sum_union hdisj,
    Finset.sum_image (by intro e he f hf h; exact Sum.inl_injective h),
    Finset.sum_singleton]
  have hedge :
      (H.edges.filter (fun e => v ∈ H.edge e)).sum
        (fun e => rate H a D (Sum.inl e)) =
      (H.degree v : ℝ) * (a / (D : ℝ)) := by
    calc
      (H.edges.filter (fun e => v ∈ H.edge e)).sum
          (fun e => rate H a D (Sum.inl e)) =
        (H.edges.filter (fun e => v ∈ H.edge e)).sum
          (fun _ => a / (D : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            simp [rate, (Finset.mem_filter.mp he).1]
      _ = (H.degree v : ℝ) * (a / (D : ℝ)) := by
            simp [IndexedHypergraph.degree, nsmul_eq_mul]
  rw [hedge]
  simp only [rate, if_pos hv]
  have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  field_simp
  ring
theorem prob_vertexSurvives (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | vertexSurvives H ω v} = Real.exp (-a) := by
  have hset :
      {ω | vertexSurvives H ω v} =
        {ω | ∀ i ∈ vertexLabels H v, ω i = false} := by
    ext ω
    exact vertexSurvives_iff_all_false H ω v
  rw [hset, FiniteBernoulli.prob_all_false_exp,
    sum_vertexLabels_rate H a hD hv]

/-- Real-valued count of surviving active vertices. -/
noncomputable def survivorCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  H.vertices.sum (fun v =>
    FiniteBernoulli.eventIndicator {ω | vertexSurvives H ω v} ω)

/-- The actual surviving active vertex set. -/
noncomputable def survivingVertices (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset V := by
  classical
  exact H.vertices.filter (vertexSurvives H ω)

/-- A marked copy accepted only when no other marked copy meets it. -/
def isolatedMarked (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (e : E) : Prop :=
  ω (Sum.inl e) = true ∧
    ∀ f ∈ H.edges, f ≠ e → ω (Sum.inl f) = true →
      Disjoint (H.edge e) (H.edge f)

noncomputable def acceptedEdges (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset E := by
  classical
  exact H.edges.filter (isolatedMarked H ω)

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem acceptedEdges_matching (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    H.IsMatching (acceptedEdges H ω) := by
  classical
  constructor
  · exact Finset.filter_subset _ _
  · intro e he f hf hne
    have he' : e ∈ H.edges.filter (isolatedMarked H ω) := by
      simpa [acceptedEdges] using he
    have hf' : f ∈ H.edges.filter (isolatedMarked H ω) := by
      simpa [acceptedEdges] using hf
    exact (Finset.mem_filter.mp he').2.2 f
      (Finset.mem_filter.mp hf').1 hne.symm
      (Finset.mem_filter.mp hf').2.1

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem surviving_disjoint_accepted (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    Disjoint (survivingVertices H ω) (H.covered (acceptedEdges H ω)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hvc
  have hv' : v ∈ H.vertices.filter (vertexSurvives H ω) := by
    simpa [survivingVertices] using hv
  have hsurvive := (Finset.mem_filter.mp hv').2
  obtain ⟨e, heacc, hve⟩ := Finset.mem_biUnion.mp hvc
  have he' : e ∈ H.edges.filter (isolatedMarked H ω) := by
    simpa [acceptedEdges] using heacc
  have heH := (Finset.mem_filter.mp he').1
  have hemark := (Finset.mem_filter.mp he').2.1
  have hfalse := hsurvive.2 e heH hve
  simp [hemark] at hfalse

/-- Every marking configuration supplies valid deterministic round data. -/
noncomputable def sampledRound (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : MatchingRound H where
  survivors := survivingVertices H ω
  survivors_subset := by
    classical
    exact Finset.filter_subset _ _
  accepted := acceptedEdges H ω
  accepted_matching := acceptedEdges_matching H ω
  survivors_disjoint_accepted := surviving_disjoint_accepted H ω
omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem survivorCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    survivorCount H ω = (survivingVertices H ω).card := by
  classical
  simp only [survivorCount, survivingVertices, FiniteBernoulli.eventIndicator]
  rw [Finset.card_filter]
  norm_cast
/-- Every active vertex survives with the same probability exp(-a). -/
theorem expect_survivorCount (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (survivorCount H) =
        (H.vertices.card : ℝ) * Real.exp (-a) := by
  classical
  unfold survivorCount
  rw [FiniteBernoulli.expect_sum]
  calc
    H.vertices.sum (fun v =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω)) =
      H.vertices.sum (fun _ => Real.exp (-a)) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [FiniteBernoulli.expect_eventIndicator]
        exact prob_vertexSurvives H a hD hv
    _ = (H.vertices.card : ℝ) * Real.exp (-a) := by simp
/-- Vertices with a positive private mark. -/
noncomputable def privateMarkedVertices (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset V := by
  classical
  exact H.vertices.filter (fun v => ω (Sum.inr v) = true)

/-- Marked copies that meet a second marked copy. -/
noncomputable def collidingFirstEdges (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset E := by
  classical
  exact H.edges.filter (fun e =>
    ω (Sum.inl e) = true ∧
      ∃ f ∈ H.edges, f ≠ e ∧ ω (Sum.inl f) = true ∧
        ¬Disjoint (H.edge e) (H.edge f))

/-- Active edge copies other than e meeting e. -/
noncomputable def intersectingNeighbors (H : IndexedHypergraph V E)
    (e : E) : Finset E := by
  classical
  exact H.edges.filter (fun f => f ≠ e ∧ ¬Disjoint (H.edge e) (H.edge f))

omit [Fintype V] [Fintype E] in
theorem card_intersectingNeighbors_le (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {e : E} (he : e ∈ H.edges) :
    (intersectingNeighbors H e).card ≤ r * D := by
  classical
  let U : Finset E :=
    (H.edge e).biUnion (fun v => H.edges.filter (fun f => v ∈ H.edge f))
  have hsub : intersectingNeighbors H e ⊆ U := by
    intro f hf
    have hf' : f ∈ H.edges.filter
        (fun f => f ≠ e ∧ ¬Disjoint (H.edge e) (H.edge f)) := by
      simpa [intersectingNeighbors] using hf
    obtain ⟨hfH, hfe, hinter⟩ := Finset.mem_filter.mp hf'
    obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp hinter
    exact Finset.mem_biUnion.mpr
      ⟨v, hve, Finset.mem_filter.mpr ⟨hfH, hvf⟩⟩
  calc
    (intersectingNeighbors H e).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ (H.edge e).sum H.degree := by
      change U.card ≤ ∑ v ∈ H.edge e, H.degree v
      simp only [U, IndexedHypergraph.degree]
      exact Finset.card_biUnion_le
    _ ≤ (H.edge e).sum (fun _ => D) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hcap v (H.edge_subset e he hv)
    _ = r * D := by simp [hunif e he]
/-- Ordered distinct pairs of active copies that intersect. -/
noncomputable def intersectingPairs (H : IndexedHypergraph V E) : Finset (E × E) := by
  classical
  exact (H.edges.product H.edges).filter (fun p =>
    p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2))

omit [Fintype V] [Fintype E] in
theorem card_intersectingPairs_le (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    (intersectingPairs H).card ≤ H.edges.card * (r * D) := by
  classical
  have hfirst : Set.MapsTo Prod.fst
      (intersectingPairs H : Set (E × E)) (H.edges : Set E) := by
    intro p hp
    have hp' : p ∈ (H.edges.product H.edges).filter
        (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
      simpa [intersectingPairs] using hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).1
  have hfiber (e : E) (he : e ∈ H.edges) :
      ((intersectingPairs H).filter (fun p => p.1 = e)).card ≤ r * D := by
    have hmap : Set.MapsTo Prod.snd
        (((intersectingPairs H).filter (fun p => p.1 = e)) : Set (E × E))
        (intersectingNeighbors H e : Set E) := by
      intro p hp
      obtain ⟨hpbase, hpeq⟩ := Finset.mem_filter.mp hp
      have hp' : p ∈ (H.edges.product H.edges).filter
          (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
        simpa [intersectingPairs] using hpbase
      obtain ⟨hprod, hne, hinter⟩ := Finset.mem_filter.mp hp'
      have hsecond := (Finset.mem_product.mp hprod).2
      have hmem : p.2 ∈ H.edges.filter
          (fun f => f ≠ e ∧ ¬Disjoint (H.edge e) (H.edge f)) := by
        apply Finset.mem_filter.mpr
        constructor
        · exact hsecond
        · constructor
          · intro h2
            exact hne (hpeq.trans h2.symm)
          · simpa [hpeq] using hinter
      simpa [intersectingNeighbors] using hmem
    have hinj : Set.InjOn Prod.snd
        (((intersectingPairs H).filter (fun p => p.1 = e)) : Set (E × E)) := by
      intro p hp q hq hsec
      have hpfirst := (Finset.mem_filter.mp hp).2
      have hqfirst := (Finset.mem_filter.mp hq).2
      exact Prod.ext (hpfirst.trans hqfirst.symm) hsec
    exact (Finset.card_le_card_of_injOn Prod.snd hmap hinj).trans
      (card_intersectingNeighbors_le H hunif hcap he)
  calc
    (intersectingPairs H).card =
        H.edges.sum (fun e =>
          ((intersectingPairs H).filter (fun p => p.1 = e)).card) :=
      Finset.card_eq_sum_card_fiberwise hfirst
    _ ≤ H.edges.sum (fun _ => r * D) :=
      Finset.sum_le_sum hfiber
    _ = H.edges.card * (r * D) := by simp
/-- Intersecting ordered pairs whose two copies are marked. -/
noncomputable def markedPairs (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : Finset (E × E) := by
  classical
  exact (intersectingPairs H).filter (fun p =>
    ω (Sum.inl p.1) = true ∧ ω (Sum.inl p.2) = true)

omit [Fintype V] [Fintype E] in
theorem collidingFirstEdges_eq_image_markedPairs
    (H : IndexedHypergraph V E) (ω : E ⊕ V → Bool) :
    collidingFirstEdges H ω = (markedPairs H ω).image Prod.fst := by
  classical
  ext e
  constructor
  · intro he
    have he' : e ∈ H.edges.filter (fun e =>
        ω (Sum.inl e) = true ∧
          ∃ f ∈ H.edges, f ≠ e ∧ ω (Sum.inl f) = true ∧
            ¬Disjoint (H.edge e) (H.edge f)) := by
      simpa [collidingFirstEdges] using he
    obtain ⟨heH, hemark, f, hfH, hfe, hfmark, hinter⟩ :=
      Finset.mem_filter.mp he'
    apply Finset.mem_image.mpr
    refine ⟨(e, f), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨heH, hfH⟩, hfe.symm, hinter⟩
    · exact ⟨hemark, hfmark⟩
  · intro he
    obtain ⟨p, hp, hpfirst⟩ := Finset.mem_image.mp he
    rcases p with ⟨e', f⟩
    change e' = e at hpfirst
    subst e'
    have hp' : (e, f) ∈ (intersectingPairs H).filter
        (fun p => ω (Sum.inl p.1) = true ∧ ω (Sum.inl p.2) = true) := by
      simpa [markedPairs] using hp
    obtain ⟨hpbase, hemark, hfmark⟩ := Finset.mem_filter.mp hp'
    have hpbase' : (e, f) ∈
        (H.edges.product H.edges).filter
          (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
      simpa [intersectingPairs] using hpbase
    obtain ⟨hprod, hne, hinter⟩ := Finset.mem_filter.mp hpbase'
    obtain ⟨heH, hfH⟩ := Finset.mem_product.mp hprod
    have he' : e ∈ H.edges.filter (fun e =>
        ω (Sum.inl e) = true ∧
          ∃ f ∈ H.edges, f ≠ e ∧ ω (Sum.inl f) = true ∧
            ¬Disjoint (H.edge e) (H.edge f)) :=
      Finset.mem_filter.mpr ⟨heH, hemark, f, hfH, hne.symm, hfmark, hinter⟩
    simpa [collidingFirstEdges] using he'

omit [Fintype V] [Fintype E] in
theorem card_collidingFirstEdges_le_markedPairs
    (H : IndexedHypergraph V E) (ω : E ⊕ V → Bool) :
    (collidingFirstEdges H ω).card ≤ (markedPairs H ω).card := by
  rw [collidingFirstEdges_eq_image_markedPairs]
  exact Finset.card_image_le
/-- Real indicator sum for marked intersecting ordered pairs. -/
noncomputable def markedPairCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  (intersectingPairs H).sum (fun p =>
    FiniteBernoulli.eventIndicator
      {ω | ω (Sum.inl p.1) = true ∧ ω (Sum.inl p.2) = true} ω)

omit [Fintype V] [Fintype E] in
theorem markedPairCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    markedPairCount H ω = ((markedPairs H ω).card : ℝ) := by
  classical
  simp only [markedPairCount, markedPairs, FiniteBernoulli.eventIndicator]
  rw [Finset.card_filter]
  norm_cast

theorem expect_markedPairCount (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (markedPairCount H) =
    (intersectingPairs H).sum (fun p =>
      FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) *
      FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2)) := by
  classical
  unfold markedPairCount
  rw [FiniteBernoulli.expect_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [FiniteBernoulli.expect_eventIndicator]
  have hp' : p ∈ (H.edges.product H.edges).filter
      (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
    simpa [intersectingPairs] using hp
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp').2.1
  exact FiniteBernoulli.prob_two_true _
    (by intro h; exact hne (Sum.inl_injective h))
omit [Fintype V] [Fintype E] in
theorem markProbability_le_rate (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) (i : E ⊕ V) :
    FiniteBernoulli.expMarkProbability (rate H a D) i ≤
      rate H a D i := by
  unfold FiniteBernoulli.expMarkProbability
  have h := Real.add_one_le_exp (-(rate H a D i))
  linarith

theorem expect_markedPairCount_le (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (markedPairCount H) ≤
        (intersectingPairs H).card * (a / (D : ℝ)) ^ 2 := by
  classical
  rw [expect_markedPairCount]
  have hDr : 0 ≤ (D : ℝ) := by exact_mod_cast (Nat.zero_le D)
  have hdiv : 0 ≤ a / (D : ℝ) := div_nonneg ha hDr
  calc
    (intersectingPairs H).sum (fun p =>
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) *
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2)) ≤
      (intersectingPairs H).sum (fun _ => (a / (D : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p ∈ (H.edges.product H.edges).filter
            (fun p => p.1 ≠ p.2 ∧ ¬Disjoint (H.edge p.1) (H.edge p.2)) := by
          simpa [intersectingPairs] using hp
        obtain ⟨he, hf⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp').1
        have hpe : 0 ≤
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) :=
          (markProbability_bounds H ha hD hcap (Sum.inl p.1)).1
        have hpf : 0 ≤
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) :=
          (markProbability_bounds H ha hD hcap (Sum.inl p.2)).1
        have hbe :
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) ≤
              a / (D : ℝ) := by
          simpa [rate, he] using markProbability_le_rate H a D (Sum.inl p.1)
        have hbf :
            FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) ≤
              a / (D : ℝ) := by
          simpa [rate, hf] using markProbability_le_rate H a D (Sum.inl p.2)
        calc
          FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.1) *
              FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) ≤
            (a / (D : ℝ)) *
              FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inl p.2) :=
            mul_le_mul_of_nonneg_right hbe hpf
          _ ≤ (a / (D : ℝ)) * (a / (D : ℝ)) :=
            mul_le_mul_of_nonneg_left hbf hdiv
          _ = (a / (D : ℝ)) ^ 2 := by ring
    _ = (intersectingPairs H).card * (a / (D : ℝ)) ^ 2 := by
      simp [nsmul_eq_mul]
theorem expect_markedPairCount_le_global (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (markedPairCount H) ≤
        ((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
          (a / (D : ℝ)) ^ 2 := by
  have hpair :
      ((intersectingPairs H).card : ℝ) ≤
        (H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ)) := by
    exact_mod_cast card_intersectingPairs_le H hunif hcap
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (markedPairCount H) ≤
      ((intersectingPairs H).card : ℝ) * (a / (D : ℝ)) ^ 2 :=
      expect_markedPairCount_le H ha hD hcap
    _ ≤ ((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
        (a / (D : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hpair (sq_nonneg _)
omit [Fintype V] [Fintype E] in
/-- A wasted vertex has a private mark or lies on a colliding marked edge. -/
theorem waste_subset_private_union_colliding (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    (sampledRound H ω).waste ⊆
      privateMarkedVertices H ω ∪ H.covered (collidingFirstEdges H ω) := by
  classical
  intro v hvw
  have hvH : v ∈ H.vertices := (Finset.mem_sdiff.mp hvw).1
  have hvnot : v ∉ (sampledRound H ω).survivors ∪
      H.covered (sampledRound H ω).accepted :=
    (Finset.mem_sdiff.mp hvw).2
  have hvnotU : v ∉ survivingVertices H ω := by
    intro hv
    exact hvnot (Finset.mem_union.mpr (Or.inl hv))
  have hvnotC : v ∉ H.covered (acceptedEdges H ω) := by
    intro hv
    exact hvnot (Finset.mem_union.mpr (Or.inr hv))
  by_cases hp : ω (Sum.inr v) = true
  · apply Finset.mem_union.mpr
    left
    have hvpriv : v ∈ H.vertices.filter (fun x => ω (Sum.inr x) = true) :=
      Finset.mem_filter.mpr ⟨hvH, hp⟩
    simpa [privateMarkedVertices] using hvpriv
  · apply Finset.mem_union.mpr
    right
    have hprivate : ω (Sum.inr v) = false := by
      cases h : ω (Sum.inr v) <;> simp_all
    have hnotSurvive : ¬ vertexSurvives H ω v := by
      intro hs
      apply hvnotU
      exact Finset.mem_filter.mpr ⟨hvH, hs⟩
    have hmarked :
        ∃ e ∈ H.edges, v ∈ H.edge e ∧ ω (Sum.inl e) = true := by
      by_contra hn
      apply hnotSurvive
      constructor
      · exact hprivate
      · intro e he hve
        cases heω : ω (Sum.inl e)
        · rfl
        · exact False.elim (hn ⟨e, he, hve, heω⟩)
    obtain ⟨e, he, hve, hemark⟩ := hmarked
    have hnotAccepted : e ∉ acceptedEdges H ω := by
      intro heacc
      exact hvnotC (Finset.mem_biUnion.mpr ⟨e, heacc, hve⟩)
    have hnotIsolated :
        ¬ ∀ f ∈ H.edges, f ≠ e → ω (Sum.inl f) = true →
          Disjoint (H.edge e) (H.edge f) := by
      intro hiso
      apply hnotAccepted
      apply Finset.mem_filter.mpr
      exact ⟨he, hemark, hiso⟩
    push Not at hnotIsolated
    obtain ⟨f, hf, hfe, hfmark, hinter⟩ := hnotIsolated
    apply Finset.mem_biUnion.mpr
    refine ⟨e, ?_, hve⟩
    apply Finset.mem_filter.mpr
    exact ⟨he, hemark, f, hf, hfe, hfmark, hinter⟩
omit [Fintype V] [Fintype E] in
theorem waste_card_le_private_add_colliding (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r) (ω : E ⊕ V → Bool) :
    (sampledRound H ω).waste.card ≤
      (privateMarkedVertices H ω).card +
        r * (collidingFirstEdges H ω).card := by
  classical
  have hsub := waste_subset_private_union_colliding H ω
  have hfirst : collidingFirstEdges H ω ⊆ H.edges := by
    unfold collidingFirstEdges
    exact Finset.filter_subset _ _
  have hcover :
      (H.covered (collidingFirstEdges H ω)).card ≤
        r * (collidingFirstEdges H ω).card := by
    calc
      (H.covered (collidingFirstEdges H ω)).card ≤
          (collidingFirstEdges H ω).sum (fun e => (H.edge e).card) :=
        Finset.card_biUnion_le
      _ = (collidingFirstEdges H ω).sum (fun _ => r) := by
        apply Finset.sum_congr rfl
        intro e he
        exact hunif e (hfirst he)
      _ = r * (collidingFirstEdges H ω).card := by simp [mul_comm]
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (privateMarkedVertices H ω) (H.covered (collidingFirstEdges H ω))
  omega
omit [Fintype V] [Fintype E] in
theorem waste_card_le_private_add_pairs (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r) (ω : E ⊕ V → Bool) :
    (sampledRound H ω).waste.card ≤
      (privateMarkedVertices H ω).card + r * (markedPairs H ω).card := by
  have h₁ := waste_card_le_private_add_colliding H hunif ω
  have h₂ := card_collidingFirstEdges_le_markedPairs H ω
  have hmul := Nat.mul_le_mul_left r h₂
  omega
/-- Expected actual number of surviving vertices in one round. -/
theorem expect_survivingVertices_card (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => ((survivingVertices H ω).card : ℝ)) =
        (H.vertices.card : ℝ) * Real.exp (-a) := by
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω => ((survivingVertices H ω).card : ℝ)) =
      FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (survivorCount H) := by
          congr 1
          funext ω
          exact (survivorCount_eq_card H ω).symm
    _ = (H.vertices.card : ℝ) * Real.exp (-a) :=
      expect_survivorCount H a hD

/-- Count private positive marks on active vertices. -/
noncomputable def privateMarkCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  H.vertices.sum (fun v => if ω (Sum.inr v) then 1 else 0)

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem privateMarkCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    privateMarkCount H ω = ((privateMarkedVertices H ω).card : ℝ) := by
  classical
  simp only [privateMarkCount, privateMarkedVertices]
  rw [Finset.card_filter]
  norm_cast

theorem expect_privateMarkCount (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) :
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (privateMarkCount H) =
      H.vertices.sum (fun v =>
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inr v)) := by
  classical
  unfold privateMarkCount
  rw [FiniteBernoulli.expect_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact FiniteBernoulli.expect_mark _ (Sum.inr v)

omit [Fintype V] [Fintype E] in
theorem sum_privateRate_eq_deficit (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    H.vertices.sum (fun v => rate H a D (Sum.inr v)) =
      (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) := by
  classical
  have hDc : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  calc
    H.vertices.sum (fun v => rate H a D (Sum.inr v)) =
        H.vertices.sum (fun v =>
          (a / (D : ℝ)) * ((D - H.degree v : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [rate, if_pos hv, Nat.cast_sub (hcap v hv)]
      field_simp
    _ = (a / (D : ℝ)) *
        H.vertices.sum (fun v => ((D - H.degree v : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) := by
      simp [IndexedHypergraph.degreeDeficit]

theorem expect_privateMarkCount_le (H : IndexedHypergraph V E)
    (a : ℝ) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D) :
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (privateMarkCount H) ≤
      (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) := by
  rw [expect_privateMarkCount]
  calc
    H.vertices.sum (fun v =>
        FiniteBernoulli.expMarkProbability (rate H a D) (Sum.inr v)) ≤
      H.vertices.sum (fun v => rate H a D (Sum.inr v)) :=
      Finset.sum_le_sum (fun v hv => markProbability_le_rate H a D (Sum.inr v))
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) :=
      sum_privateRate_eq_deficit H a hD hcap
private theorem expect_mono (p : E ⊕ V → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (X Y : (E ⊕ V → Bool) → ℝ)
    (hXY : ∀ ω, X ω ≤ Y ω) :
    FiniteBernoulli.expect p X ≤ FiniteBernoulli.expect p Y := by
  classical
  unfold FiniteBernoulli.expect
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hXY ω)
    (FiniteBernoulli.weight_nonneg p hp ω)

private theorem expect_add (p : E ⊕ V → ℝ)
    (X Y : (E ⊕ V → Bool) → ℝ) :
    FiniteBernoulli.expect p (fun ω => X ω + Y ω) =
      FiniteBernoulli.expect p X + FiniteBernoulli.expect p Y := by
  classical
  unfold FiniteBernoulli.expect
  simp only [mul_add, Finset.sum_add_distrib]

private theorem expect_mul_const (p : E ⊕ V → ℝ) (c : ℝ)
    (X : (E ⊕ V → Bool) → ℝ) :
    FiniteBernoulli.expect p (fun ω => c * X ω) =
      c * FiniteBernoulli.expect p X := by
  classical
  unfold FiniteBernoulli.expect
  calc
    (∑ ω, FiniteBernoulli.weight p ω * (c * X ω)) =
      ∑ ω, c * (FiniteBernoulli.weight p ω * X ω) := by
        apply Finset.sum_congr rfl
        intro ω hω
        ring
    _ = c * ∑ ω, FiniteBernoulli.weight p ω * X ω := by
      rw [Finset.mul_sum]

private theorem expect_const (p : E ⊕ V → ℝ) (c : ℝ) :
    FiniteBernoulli.expect p (fun _ : E ⊕ V → Bool => c) = c := by
  classical
  unfold FiniteBernoulli.expect
  rw [← Finset.sum_mul]
  simp [FiniteBernoulli.sum_weight]

/-- A finite marking configuration has value no greater than its mean. -/
theorem exists_le_expect (p : E ⊕ V → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (X : (E ⊕ V → Bool) → ℝ) :
    ∃ ω, X ω ≤ FiniteBernoulli.expect p X := by
  classical
  obtain ⟨ω, _, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (E ⊕ V → Bool)) X
      Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have h := expect_mono p hp (fun _ => X ω) X
    (fun η => hmin η (Finset.mem_univ η))
  simpa only [expect_const] using h
/-- One-round expected waste, before simplifying the edge count by regularity. -/
theorem expect_waste_le (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
        (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) *
            (((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
              (a / (D : ℝ)) ^ 2) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  have hpoint (ω : E ⊕ V → Bool) :
      (((sampledRound H ω).waste.card : ℝ)) ≤
        privateMarkCount H ω + (r : ℝ) * markedPairCount H ω := by
    rw [privateMarkCount_eq_card, markedPairCount_eq_card]
    exact_mod_cast waste_card_le_private_add_pairs H hunif ω
  calc
    FiniteBernoulli.expect p
        (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
      FiniteBernoulli.expect p
        (fun ω => privateMarkCount H ω + (r : ℝ) * markedPairCount H ω) :=
      expect_mono p hp _ _ hpoint
    _ = FiniteBernoulli.expect p (privateMarkCount H) +
        (r : ℝ) * FiniteBernoulli.expect p (markedPairCount H) := by
      rw [expect_add, expect_mul_const]
    _ ≤ (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) *
            (((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
              (a / (D : ℝ)) ^ 2) := by
      apply add_le_add
      · exact expect_privateMarkCount_le H a hD hcap
      · exact mul_le_mul_of_nonneg_left
          (expect_markedPairCount_le_global H hunif hcap ha hD)
          (by positivity)
/-- The collision term depends only on the number of active vertices. -/
theorem expect_waste_le_simplified (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
        (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ) := by
  have hcountNat : r * H.edges.card ≤ H.vertices.card * D := by
    have h := H.degreeDeficit_add_edges hunif hcap
    omega
  have hcount :
      (r : ℝ) * (H.edges.card : ℝ) ≤
        (H.vertices.card : ℝ) * (D : ℝ) := by
    exact_mod_cast hcountNat
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hDr : 0 ≤ (D : ℝ) := by positivity
  have hmult : 0 ≤
      ((r : ℝ) * (D : ℝ)) * (a / (D : ℝ)) ^ 2 :=
    mul_nonneg (mul_nonneg hr hDr) (sq_nonneg _)
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω => (((sampledRound H ω).waste.card : ℝ))) ≤
      (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
        (r : ℝ) *
          (((H.edges.card : ℝ) * ((r : ℝ) * (D : ℝ))) *
            (a / (D : ℝ)) ^ 2) :=
      expect_waste_le H hunif hcap ha hD
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
        ((r : ℝ) * (H.edges.card : ℝ)) *
          (((r : ℝ) * (D : ℝ)) * (a / (D : ℝ)) ^ 2) := by ring
    _ ≤ (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
        ((H.vertices.card : ℝ) * (D : ℝ)) *
          (((r : ℝ) * (D : ℝ)) * (a / (D : ℝ)) ^ 2) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right hcount hmult) _
    _ = (a / (D : ℝ)) * (H.degreeDeficit D : ℝ) +
          (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ) := by
      field_simp
/-- Labels whose simultaneous absence makes a vertex set survive. -/
def setLabels (H : IndexedHypergraph V E) (U : Finset V) :
    Finset (E ⊕ V) :=
  U.biUnion (vertexLabels H)

def setSurvives (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U : Finset V) : Prop :=
  ∀ v ∈ U, vertexSurvives H ω v

omit [Fintype V] [Fintype E] in
theorem setSurvives_iff_all_false (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U : Finset V) :
    setSurvives H ω U ↔ ∀ i ∈ setLabels H U, ω i = false := by
  classical
  simp only [setSurvives, setLabels, Finset.mem_biUnion]
  constructor
  · intro hs i hi
    obtain ⟨v, hv, hiv⟩ := hi
    exact (vertexSurvives_iff_all_false H ω v).mp (hs v hv) i hiv
  · intro hs v hv
    apply (vertexSurvives_iff_all_false H ω v).mpr
    intro i hi
    exact hs i ⟨v, hv, hi⟩

theorem prob_setSurvives (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) (U : Finset V) :
    FiniteBernoulli.prob
      (FiniteBernoulli.expMarkProbability (rate H a D))
      {ω | setSurvives H ω U} =
        Real.exp (-(setLabels H U).sum (rate H a D)) := by
  have hset :
      {ω | setSurvives H ω U} =
        {ω | ∀ i ∈ setLabels H U, ω i = false} := by
    ext ω
    exact setSurvives_iff_all_false H ω U
  rw [hset, FiniteBernoulli.prob_all_false_exp]

private theorem sum_biUnion_le {κ ι : Type*} [DecidableEq ι]
    (s : Finset κ) (t : κ → Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (s.biUnion t).sum f ≤ s.sum (fun j => (t j).sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      have hinter : 0 ≤ ((t j) ∩ s.biUnion t).sum f :=
        Finset.sum_nonneg (fun i hi => hf i)
      have hunion := Finset.sum_union_inter
        (s₁ := t j) (s₂ := s.biUnion t) (f := f)
      simp only [Finset.biUnion_insert, Finset.sum_insert hj]
      calc
        (t j ∪ s.biUnion t).sum f ≤
            (t j).sum f + (s.biUnion t).sum f := by linarith
        _ ≤ (t j).sum f + s.sum (fun x => (t x).sum f) :=
          add_le_add_right ih _

omit [Fintype V] [Fintype E] in
theorem sum_setLabels_rate_le (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {U : Finset V} (hU : U ⊆ H.vertices) :
    (setLabels H U).sum (rate H a D) ≤ (U.card : ℝ) * a := by
  classical
  calc
    (setLabels H U).sum (rate H a D) ≤
      U.sum (fun v => (vertexLabels H v).sum (rate H a D)) :=
      sum_biUnion_le U (vertexLabels H) (rate H a D)
        (rate_nonneg H ha hD hcap)
    _ = U.sum (fun _ => a) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact sum_vertexLabels_rate H a hD (hU hv)
    _ = (U.card : ℝ) * a := by simp

/-- Positive association of no-mark events yields an edge-set survival lower bound. -/
theorem prob_setSurvives_ge (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {U : Finset V} (hU : U ⊆ H.vertices) :
    Real.exp (-((U.card : ℝ) * a)) ≤
      FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω U} := by
  rw [prob_setSurvives]
  exact Real.exp_le_exp.mpr
    (neg_le_neg (sum_setLabels_rate_le H ha hD hcap hU))
/-- Count the active edge copies whose vertices all survive. -/
noncomputable def inducedEdgeCount (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) : ℝ :=
  H.edges.sum (fun e =>
    FiniteBernoulli.eventIndicator
      {ω | setSurvives H ω (H.edge e)} ω)

omit [Fintype V] [Fintype E] in
omit [DecidableEq V] [DecidableEq E] in
theorem edge_subset_survivors_iff (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) {e : E} (he : e ∈ H.edges) :
    H.edge e ⊆ survivingVertices H ω ↔
      setSurvives H ω (H.edge e) := by
  classical
  constructor
  · intro hs v hv
    exact (Finset.mem_filter.mp (hs hv)).2
  · intro hs v hv
    exact Finset.mem_filter.mpr
      ⟨H.edge_subset e he hv, hs v hv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedEdgeCount_eq_card (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) :
    inducedEdgeCount H ω =
      (((H.induce (survivingVertices H ω)).edges.card : ℝ)) := by
  classical
  simp only [inducedEdgeCount, FiniteBernoulli.eventIndicator,
    IndexedHypergraph.induce_edges]
  rw [Finset.card_filter]
  norm_cast
  apply Finset.sum_congr rfl
  intro e he
  simp only [Set.mem_ofPred_eq, ← edge_subset_survivors_iff H ω he]

theorem expect_inducedEdgeCount_ge (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    (H.edges.card : ℝ) * Real.exp (-((r : ℝ) * a)) ≤
      FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedEdgeCount H) := by
  classical
  unfold inducedEdgeCount
  rw [FiniteBernoulli.expect_sum]
  calc
    (H.edges.card : ℝ) * Real.exp (-((r : ℝ) * a)) =
      H.edges.sum (fun _ => Real.exp (-((r : ℝ) * a))) := by simp
    _ ≤ H.edges.sum (fun e =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e)} ω)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [FiniteBernoulli.expect_eventIndicator]
      have hsub : H.edge e ⊆ H.vertices := H.edge_subset e he
      simpa [hunif e he] using
        (prob_setSurvives_ge H ha hD hcap hsub)
omit [Fintype V] [Fintype E] in
theorem vertexLabels_inter (H : IndexedHypergraph V E)
    {u v : V} (huv : u ≠ v) :
    vertexLabels H u ∩ vertexLabels H v =
      ((H.edges.filter (fun e => u ∈ H.edge e ∧ v ∈ H.edge e)).image
        Sum.inl) := by
  classical
  ext i
  cases i with
  | inl e =>
      simp only [vertexLabels, Finset.mem_inter, Finset.mem_union,
        Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨h₁, h₂⟩
        obtain ⟨e₁, he₁, heq₁⟩ := h₁.resolve_right (by simp)
        obtain ⟨e₂, he₂, heq₂⟩ := h₂.resolve_right (by simp)
        have h₁' : e₁ = e := Sum.inl_injective heq₁
        have h₂' : e₂ = e := Sum.inl_injective heq₂
        subst e₁
        subst e₂
        exact ⟨e, Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp he₁).1,
            (Finset.mem_filter.mp he₁).2, (Finset.mem_filter.mp he₂).2⟩, rfl⟩
      · rintro ⟨e', he', heq⟩
        have heq' : e' = e := Sum.inl_injective heq
        subst e'
        obtain ⟨he, hu, hv⟩ := Finset.mem_filter.mp he'
        constructor
        · left
          exact ⟨e, Finset.mem_filter.mpr ⟨he, hu⟩, rfl⟩
        · left
          exact ⟨e, Finset.mem_filter.mpr ⟨he, hv⟩, rfl⟩
  | inr w =>
      simp only [vertexLabels, Finset.mem_inter, Finset.mem_union,
        Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨h₁, h₂⟩
        have hwu : w = u := by
          rcases h₁ with h | h
          · obtain ⟨e, _, heq⟩ := h
            cases heq
          · exact Sum.inr_injective h
        have hwv : w = v := by
          rcases h₂ with h | h
          · obtain ⟨e, _, heq⟩ := h
            cases heq
          · exact Sum.inr_injective h
        exact False.elim (huv (hwu.symm.trans hwv))
      · rintro ⟨e, _, heq⟩
        cases heq

omit [Fintype V] [Fintype E] in
theorem sum_vertexLabels_inter_rate (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) {u v : V} (huv : u ≠ v) :
    (vertexLabels H u ∩ vertexLabels H v).sum (rate H a D) =
      (H.codegree u v : ℝ) * (a / (D : ℝ)) := by
  classical
  rw [vertexLabels_inter H huv]
  rw [Finset.sum_image (by
    intro e he f hf h
    exact Sum.inl_injective h)]
  calc
    (H.edges.filter (fun e => u ∈ H.edge e ∧ v ∈ H.edge e)).sum
        (fun e => rate H a D (Sum.inl e)) =
      (H.edges.filter (fun e => u ∈ H.edge e ∧ v ∈ H.edge e)).sum
        (fun _ => a / (D : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [rate, (Finset.mem_filter.mp he).1]
    _ = (H.codegree u v : ℝ) * (a / (D : ℝ)) := by
      simp [IndexedHypergraph.codegree, nsmul_eq_mul]
omit [Fintype V] [Fintype E] in
theorem vertexLabels_inter_setLabels (H : IndexedHypergraph V E)
    (v : V) (U : Finset V) :
    vertexLabels H v ∩ setLabels H U =
      U.biUnion (fun u => vertexLabels H v ∩ vertexLabels H u) := by
  classical
  ext i
  simp only [setLabels, Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hiv, u, hu, hiu⟩
    exact ⟨u, hu, hiv, hiu⟩
  · rintro ⟨u, hu, hiv, hiu⟩
    exact ⟨hiv, u, hu, hiu⟩

omit [Fintype V] [Fintype E] in
theorem sum_vertexLabels_inter_setLabels_le
    (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ u ∈ H.vertices, H.degree u ≤ D)
    {B : ℕ} (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {v : V} (hv : v ∈ H.vertices)
    {U : Finset V} (hU : U ⊆ H.vertices) (hvU : v ∉ U) :
    (vertexLabels H v ∩ setLabels H U).sum (rate H a D) ≤
      (U.card : ℝ) * ((B : ℝ) * (a / (D : ℝ))) := by
  classical
  rw [vertexLabels_inter_setLabels H v U]
  calc
    (U.biUnion (fun u => vertexLabels H v ∩ vertexLabels H u)).sum
        (rate H a D) ≤
      U.sum (fun u =>
        (vertexLabels H v ∩ vertexLabels H u).sum (rate H a D)) :=
      sum_biUnion_le U _ _ (rate_nonneg H ha hD hcap)
    _ ≤ U.sum (fun _ => (B : ℝ) * (a / (D : ℝ))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hne : v ≠ u := by
        intro h
        exact hvU (h ▸ hu)
      rw [sum_vertexLabels_inter_rate H a D hne]
      have hcodegR : (H.codegree v u : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast hcodeg v hv u (hU hu) hne
      exact mul_le_mul_of_nonneg_right hcodegR
        (div_nonneg ha (by positivity))
    _ = (U.card : ℝ) * ((B : ℝ) * (a / (D : ℝ))) := by simp
omit [Fintype V] [Fintype E] in
/-- A bounded codegree limits the repeated labels in a joint survival event. -/
theorem sum_setLabels_rate_lower (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {B : ℕ} (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    (U : Finset V) (hU : U ⊆ H.vertices) :
    (U.card : ℝ) * a ≤
      (setLabels H U).sum (rate H a D) +
        (U.card : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ))) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
      simp [setLabels]
  | @insert v U hvU ih =>
      have hv : v ∈ H.vertices := hU (Finset.mem_insert_self v U)
      have hU' : U ⊆ H.vertices := by
        intro u hu
        exact hU (Finset.mem_insert_of_mem hu)
      have hih := ih hU'
      have hinter :=
        sum_vertexLabels_inter_setLabels_le H ha hD hcap hcodeg hv hU' hvU
      have hunion := Finset.sum_union_inter
        (s₁ := vertexLabels H v) (s₂ := setLabels H U)
        (f := rate H a D)
      have hset :
          setLabels H (insert v U) =
            vertexLabels H v ∪ setLabels H U := by
        simp [setLabels]
      have hvsum := sum_vertexLabels_rate H a hD hv
      have hnonneg : 0 ≤ (U.card : ℝ) *
          ((B : ℝ) * (a / (D : ℝ))) := by
        positivity
      have hc : 0 ≤ (B : ℝ) * (a / (D : ℝ)) := by positivity
      rw [hset, Finset.card_insert_of_notMem hvU]
      push_cast
      nlinarith
theorem prob_setSurvives_le (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {B : ℕ} (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {U : Finset V} (hU : U ⊆ H.vertices) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω U} ≤
      Real.exp
        (-((U.card : ℝ) * a) +
          (U.card : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ)))) := by
  rw [prob_setSurvives]
  apply Real.exp_le_exp.mpr
  have h := sum_setLabels_rate_lower H ha hD hcap hcodeg U hU
  linarith
/-- Degree of a fixed vertex in the induced hypergraph, as an indicator sum. -/
noncomputable def inducedDegreeCount (H : IndexedHypergraph V E)
    (v : V) (ω : E ⊕ V → Bool) : ℝ :=
  (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e =>
    FiniteBernoulli.eventIndicator
      {ω | setSurvives H ω (H.edge e)} ω)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedDegreeCount_eq_degree (H : IndexedHypergraph V E)
    (v : V) (ω : E ⊕ V → Bool) :
    inducedDegreeCount H v ω =
      (((H.induce (survivingVertices H ω)).degree v : ℝ)) := by
  classical
  simp only [inducedDegreeCount, FiniteBernoulli.eventIndicator,
    IndexedHypergraph.degree, IndexedHypergraph.induce_edges]
  rw [Finset.filter_comm, Finset.card_filter]
  norm_cast
  apply Finset.sum_congr rfl
  intro e he
  have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
  simp only [Set.mem_ofPred_eq, ← edge_subset_survivors_iff H ω heH]

theorem expect_inducedDegreeCount_le (H : IndexedHypergraph V E)
    {r D B : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (v : V) :
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedDegreeCount H v) ≤
      (H.degree v : ℝ) *
        Real.exp (-(r : ℝ) * a +
          (r : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ)))) := by
  classical
  unfold inducedDegreeCount
  rw [FiniteBernoulli.expect_sum]
  calc
    (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e)} ω)) ≤
      (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun _ =>
        Real.exp (-(r : ℝ) * a +
          (r : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ))))) := by
        apply Finset.sum_le_sum
        intro e he
        rw [FiniteBernoulli.expect_eventIndicator]
        have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
        simpa [hunif e heH] using
          (prob_setSurvives_le H ha hD hcap hcodeg
            (H.edge_subset e heH))
    _ = (H.degree v : ℝ) *
        Real.exp (-(r : ℝ) * a +
          (r : ℝ) ^ 2 * ((B : ℝ) * (a / (D : ℝ)))) := by
        simp [IndexedHypergraph.degree]
omit [Fintype V] [Fintype E] in
omit [DecidableEq E] in
theorem setSurvives_union (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U W : Finset V) :
    setSurvives H ω (U ∪ W) ↔
      setSurvives H ω U ∧ setSurvives H ω W := by
  constructor
  · intro h
    constructor
    · intro v hv
      exact h v (Finset.mem_union_left W hv)
    · intro v hv
      exact h v (Finset.mem_union_right U hv)
  · rintro ⟨hU, hW⟩ v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hU v hv
    · exact hW v hv

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem indicator_setSurvives_mul (H : IndexedHypergraph V E)
    (ω : E ⊕ V → Bool) (U W : Finset V) :
    FiniteBernoulli.eventIndicator
        {ω | setSurvives H ω U} ω *
      FiniteBernoulli.eventIndicator
        {ω | setSurvives H ω W} ω =
      FiniteBernoulli.eventIndicator
        {ω | setSurvives H ω (U ∪ W)} ω := by
  classical
  by_cases hU : setSurvives H ω U
  · by_cases hW : setSurvives H ω W
    · have hUW := (setSurvives_union H ω U W).mpr ⟨hU, hW⟩
      simp [FiniteBernoulli.eventIndicator, hU, hW, hUW]
    · have hUW : ¬ setSurvives H ω (U ∪ W) := by
        intro h
        exact hW ((setSurvives_union H ω U W).mp h).2
      simp [FiniteBernoulli.eventIndicator, hU, hW, hUW]
  · have hUW : ¬ setSurvives H ω (U ∪ W) := by
      intro h
      exact hU ((setSurvives_union H ω U W).mp h).1
    simp [FiniteBernoulli.eventIndicator, hU, hUW]

theorem expect_inducedDegreeCount_sq (H : IndexedHypergraph V E)
    (a : ℝ) (D : ℕ) (v : V) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) =
        (H.edges.filter (fun e => v ∈ H.edge e)).sum (fun e =>
          (H.edges.filter (fun f => v ∈ H.edge f)).sum (fun f =>
            FiniteBernoulli.prob
              (FiniteBernoulli.expMarkProbability (rate H a D))
              {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) := by
  classical
  let I := H.edges.filter (fun e => v ∈ H.edge e)
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  have hpoint (ω : E ⊕ V → Bool) :
      (inducedDegreeCount H v ω) ^ 2 =
        I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ω)) := by
    simp only [inducedDegreeCount, I]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro f hf
    exact indicator_setSurvives_mul H ω (H.edge e) (H.edge f)
  calc
    FiniteBernoulli.expect p
        (fun ω => (inducedDegreeCount H v ω) ^ 2) =
      FiniteBernoulli.expect p
        (fun ω => I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ω))) := by
      congr 1
      funext ω
      exact hpoint ω
    _ = I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.expect p
            (FiniteBernoulli.eventIndicator
              {ω | setSurvives H ω (H.edge e ∪ H.edge f)}))) := by
      rw [FiniteBernoulli.expect_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [FiniteBernoulli.expect_sum]
    _ = I.sum (fun e => I.sum (fun f =>
          FiniteBernoulli.prob p
            {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      exact FiniteBernoulli.expect_eventIndicator p _
/-- Incident copies at a fixed vertex, retaining multiplicity through labels. -/
def incidentEdges (H : IndexedHypergraph V E) (v : V) : Finset E :=
  H.edges.filter (fun e => v ∈ H.edge e)

/-- Ordered incident-copy pairs sharing a second vertex. -/
noncomputable def doublyIntersectingPairs (H : IndexedHypergraph V E)
    (v : V) : Finset (E × E) := by
  classical
  exact ((incidentEdges H v).product (incidentEdges H v)).filter
    (fun p => ∃ u ∈ H.vertices.erase v,
      u ∈ H.edge p.1 ∧ u ∈ H.edge p.2)

omit [Fintype V] [Fintype E] in
theorem card_doublyIntersectingPairs_le (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    {v : V} (hv : v ∈ H.vertices)
    (hB : H.maxCodegree ≤ B) (hD : H.degree v ≤ D) :
    (doublyIntersectingPairs H v).card ≤ B * (r * D) := by
  classical
  let C : V → Finset E := fun u =>
    H.edges.filter (fun e => v ∈ H.edge e ∧ u ∈ H.edge e)
  have hsub :
      doublyIntersectingPairs H v ⊆
        (H.vertices.erase v).biUnion (fun u => (C u).product (C u)) := by
    intro p hp
    obtain ⟨hprod, u, hu, hu₁, hu₂⟩ :=
      Finset.mem_filter.mp (show p ∈
        ((incidentEdges H v).product (incidentEdges H v)).filter
          (fun p => ∃ u ∈ H.vertices.erase v,
            u ∈ H.edge p.1 ∧ u ∈ H.edge p.2) from hp)
    obtain ⟨he₁, hv₁⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hprod).1
    obtain ⟨he₂, hv₂⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hprod).2
    exact Finset.mem_biUnion.mpr
      ⟨u, hu, Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨he₁, hv₁, hu₁⟩,
          Finset.mem_filter.mpr ⟨he₂, hv₂, hu₂⟩⟩⟩
  calc
    (doublyIntersectingPairs H v).card ≤
      ((H.vertices.erase v).biUnion
        (fun u => (C u).product (C u))).card :=
      Finset.card_le_card hsub
    _ ≤ (H.vertices.erase v).sum
        (fun u => ((C u).product (C u)).card) :=
      Finset.card_biUnion_le
    _ = (H.vertices.erase v).sum
        (fun u => H.codegree v u * H.codegree v u) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [C, IndexedHypergraph.codegree, Finset.card_product]
    _ ≤ B * (r * D) :=
      H.sum_codegree_sq_le hunif hv hB hD
omit [Fintype V] [Fintype E] in
omit [DecidableEq E] in
theorem union_card_of_good_incident_pair (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    {v : V} {e f : E}
    (he : e ∈ incidentEdges H v) (hf : f ∈ incidentEdges H v)
    (hgood : (e, f) ∉ doublyIntersectingPairs H v) :
    (H.edge e ∪ H.edge f).card + 1 = 2 * r := by
  classical
  obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
  obtain ⟨hfH, hvf⟩ := Finset.mem_filter.mp hf
  have hnot :
      ¬ ∃ u ∈ H.vertices.erase v,
        u ∈ H.edge e ∧ u ∈ H.edge f := by
    intro h
    exact hgood (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨he, hf⟩, h⟩)
  have hinter : H.edge e ∩ H.edge f = {v} := by
    ext u
    constructor
    · intro hu
      have hue := (Finset.mem_inter.mp hu).1
      have huf := (Finset.mem_inter.mp hu).2
      have huv : u = v := by
        by_contra hne
        exact hnot ⟨u,
          Finset.mem_erase.mpr ⟨hne, H.edge_subset e heH hue⟩,
          hue, huf⟩
      simp [huv]
    · intro hu
      have huv : u = v := Finset.mem_singleton.mp hu
      subst u
      exact Finset.mem_inter.mpr ⟨hve, hvf⟩
  have hcount := Finset.card_union_add_card_inter (H.edge e) (H.edge f)
  rw [hinter, Finset.card_singleton, hunif e heH, hunif f hfH] at hcount
  omega
theorem prob_incident_pair_le_vertex (H : IndexedHypergraph V E)
    {a : ℝ} (ha : 0 ≤ a) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {v : V} {e f : E} (he : e ∈ incidentEdges H v) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ≤
      Real.exp (-a) := by
  have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
  have hve : v ∈ H.edge e := (Finset.mem_filter.mp he).2
  have hv : v ∈ H.vertices := H.edge_subset e heH hve
  have hp : ∀ i, 0 ≤
      FiniteBernoulli.expMarkProbability (rate H a D) i ∧
      FiniteBernoulli.expMarkProbability (rate H a D) i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  calc
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ≤
      FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | vertexSurvives H ω v} := by
          apply FiniteBernoulli.prob_mono _ hp
          intro ω hω
          exact hω v (Finset.mem_union_left _ hve)
    _ = Real.exp (-a) := prob_vertexSurvives H a hD hv

theorem prob_good_incident_pair_le (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} {e f : E}
    (he : e ∈ incidentEdges H v) (hf : f ∈ incidentEdges H v)
    (hgood : (e, f) ∉ doublyIntersectingPairs H v) :
    FiniteBernoulli.prob
        (FiniteBernoulli.expMarkProbability (rate H a D))
        {ω | setSurvives H ω (H.edge e ∪ H.edge f)} ≤
      Real.exp
        (-(((2 * r - 1 : ℕ) : ℝ) * a) +
          (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
            ((B : ℝ) * (a / (D : ℝ)))) := by
  have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
  have hfH : f ∈ H.edges := (Finset.mem_filter.mp hf).1
  have hcard : (H.edge e ∪ H.edge f).card = 2 * r - 1 := by
    have h := union_card_of_good_incident_pair H hunif he hf hgood
    omega
  have hsub : H.edge e ∪ H.edge f ⊆ H.vertices :=
    Finset.union_subset (H.edge_subset e heH) (H.edge_subset f hfH)
  simpa [hcard] using
    (prob_setSurvives_le H ha hD hcap hcodeg hsub)
theorem expect_inducedDegreeCount_sq_le_raw (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (v : V) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) ≤
        ((incidentEdges H v).card : ℝ) ^ 2 *
          Real.exp
            (-(((2 * r - 1 : ℕ) : ℝ) * a) +
              (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ)))) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
  classical
  let I := incidentEdges H v
  let C := Real.exp
    (-(((2 * r - 1 : ℕ) : ℝ) * a) +
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))))
  let q := Real.exp (-a)
  have hbadsub : doublyIntersectingPairs H v ⊆ I.product I := by
    dsimp only [doublyIntersectingPairs]
    exact Finset.filter_subset _ _
  have hsum :
      (I.product I).sum (fun p =>
        if p ∈ doublyIntersectingPairs H v then q else 0) =
          ((doublyIntersectingPairs H v).card : ℝ) * q := by
    rw [← Finset.sum_filter]
    have heq :
        (I.product I).filter
          (fun p => p ∈ doublyIntersectingPairs H v) =
            doublyIntersectingPairs H v := by
      ext p
      constructor
      · intro hp
        exact (Finset.mem_filter.mp hp).2
      · intro hp
        exact Finset.mem_filter.mpr ⟨hbadsub hp, hp⟩
    rw [heq]
    simp
  rw [expect_inducedDegreeCount_sq]
  change I.sum (fun e => I.sum (fun f =>
    FiniteBernoulli.prob
      (FiniteBernoulli.expMarkProbability (rate H a D))
      {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) ≤
        (I.card : ℝ) ^ 2 * C +
          ((doublyIntersectingPairs H v).card : ℝ) * q
  calc
    I.sum (fun e => I.sum (fun f =>
        FiniteBernoulli.prob
          (FiniteBernoulli.expMarkProbability (rate H a D))
          {ω | setSurvives H ω (H.edge e ∪ H.edge f)})) =
      (I.product I).sum (fun p =>
        FiniteBernoulli.prob
          (FiniteBernoulli.expMarkProbability (rate H a D))
          {ω | setSurvives H ω (H.edge p.1 ∪ H.edge p.2)}) := by
      exact (Finset.sum_product I I (fun p =>
        FiniteBernoulli.prob
          (FiniteBernoulli.expMarkProbability (rate H a D))
          {ω | setSurvives H ω (H.edge p.1 ∪ H.edge p.2)})).symm
    _ ≤ (I.product I).sum (fun p =>
        C + if p ∈ doublyIntersectingPairs H v then q else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨he, hf⟩ := Finset.mem_product.mp hp
      by_cases hbad : p ∈ doublyIntersectingPairs H v
      · have hprob := prob_incident_pair_le_vertex H ha hD hcap (f := p.2) he
        have hC : 0 ≤ C := Real.exp_nonneg _
        simp only [if_pos hbad]
        exact le_trans hprob (by dsimp [C, q] at *; linarith)
      · have hprob :=
          prob_good_incident_pair_le H hunif hcap hcodeg ha hD (e := p.1) (f := p.2) he hf hbad
        simpa only [if_neg hbad, add_zero, C] using hprob
    _ = (I.card : ℝ) ^ 2 * C +
          ((doublyIntersectingPairs H v).card : ℝ) * q := by
      rw [Finset.sum_add_distrib, hsum]
      simp [Finset.card_product, pow_two, C, q]
theorem expect_inducedDegreeCount_sq_le (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) ≤
        (D : ℝ) ^ 2 *
          Real.exp
            (-(((2 * r - 1 : ℕ) : ℝ) * a) +
              (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ)))) +
        ((B * (r * D) : ℕ) : ℝ) * Real.exp (-a) := by
  have hcodeg :
      ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, u ≠ v →
        H.codegree u v ≤ B := by
    intro u hu w hw hne
    exact (H.codegree_le_maxCodegree hu hw hne).trans hB
  have hdegreeNat : (incidentEdges H v).card ≤ D := hcap v hv
  have hdegree : ((incidentEdges H v).card : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hdegreeNat
  have hdegreeSq :
      ((incidentEdges H v).card : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
    have hnonneg : 0 ≤ ((incidentEdges H v).card : ℝ) := by positivity
    nlinarith
  have hbad :
      ((doublyIntersectingPairs H v).card : ℝ) ≤
        ((B * (r * D) : ℕ) : ℝ) := by
    exact_mod_cast card_doublyIntersectingPairs_le H hunif hv hB (hcap v hv)
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω => (inducedDegreeCount H v ω) ^ 2) ≤
      ((incidentEdges H v).card : ℝ) ^ 2 *
        Real.exp
          (-(((2 * r - 1 : ℕ) : ℝ) * a) +
            (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D : ℝ)))) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) :=
      expect_inducedDegreeCount_sq_le_raw H hunif hcap hcodeg ha hD v
    _ ≤ (D : ℝ) ^ 2 *
        Real.exp
          (-(((2 * r - 1 : ℕ) : ℝ) * a) +
            (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D : ℝ)))) +
      ((B * (r * D) : ℕ) : ℝ) * Real.exp (-a) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hdegreeSq (Real.exp_nonneg _)
      · exact mul_le_mul_of_nonneg_right hbad (Real.exp_nonneg _)
theorem expect_inducedDegreeCount_ge (H : IndexedHypergraph V E)
    {r D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (v : V) :
    (H.degree v : ℝ) * Real.exp (-((r : ℝ) * a)) ≤
      FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedDegreeCount H v) := by
  classical
  unfold inducedDegreeCount
  rw [FiniteBernoulli.expect_sum]
  calc
    (H.degree v : ℝ) * Real.exp (-((r : ℝ) * a)) =
      (incidentEdges H v).sum
        (fun _ => Real.exp (-((r : ℝ) * a))) := by
      simp [incidentEdges, IndexedHypergraph.degree]
    _ ≤ (incidentEdges H v).sum (fun e =>
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (fun ω => FiniteBernoulli.eventIndicator
            {ω | setSurvives H ω (H.edge e)} ω)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [FiniteBernoulli.expect_eventIndicator]
      have heH : e ∈ H.edges := (Finset.mem_filter.mp he).1
      simpa [hunif e heH] using
        (prob_setSurvives_ge H ha hD hcap
          (H.edge_subset e heH))
omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedDegreeCount_zero_of_not_vertexSurvives
    (H : IndexedHypergraph V E) (v : V) (ω : E ⊕ V → Bool)
    (hnot : ¬ vertexSurvives H ω v) :
    inducedDegreeCount H v ω = 0 := by
  classical
  unfold inducedDegreeCount
  apply Finset.sum_eq_zero
  intro e he
  have hve : v ∈ H.edge e := (Finset.mem_filter.mp he).2
  have hnotEdge : ¬ setSurvives H ω (H.edge e) := by
    intro hs
    exact hnot (hs v hve)
  simp [FiniteBernoulli.eventIndicator, hnotEdge]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem inducedDegreeCount_mul_vertexIndicator
    (H : IndexedHypergraph V E) (v : V) (ω : E ⊕ V → Bool) :
    inducedDegreeCount H v ω *
      FiniteBernoulli.eventIndicator
        {ω | vertexSurvives H ω v} ω =
      inducedDegreeCount H v ω := by
  classical
  by_cases hv : vertexSurvives H ω v
  · simp [FiniteBernoulli.eventIndicator, hv]
  · have hz := inducedDegreeCount_zero_of_not_vertexSurvives H v ω hv
    simp [FiniteBernoulli.eventIndicator, hv, hz]

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
theorem vertexIndicator_sq (H : IndexedHypergraph V E)
    (v : V) (ω : E ⊕ V → Bool) :
    (FiniteBernoulli.eventIndicator
      {ω | vertexSurvives H ω v} ω) ^ 2 =
      FiniteBernoulli.eventIndicator
        {ω | vertexSurvives H ω v} ω := by
  classical
  by_cases hv : vertexSurvives H ω v
  · simp [FiniteBernoulli.eventIndicator, hv]
  · simp [FiniteBernoulli.eventIndicator, hv]

theorem expect_centered_inducedDegreeCount_sq
    (H : IndexedHypergraph V E) (a c : ℝ)
    {D : ℕ} (hD : 0 < D) {v : V} (hv : v ∈ H.vertices) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) =
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω => (inducedDegreeCount H v ω) ^ 2) -
      2 * c * FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (inducedDegreeCount H v) +
      c ^ 2 * Real.exp (-a) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let I := fun ω => FiniteBernoulli.eventIndicator
    {ω | vertexSurvives H ω v} ω
  let Z := inducedDegreeCount H v
  have hpoint (ω : E ⊕ V → Bool) :
      (Z ω - c * I ω) ^ 2 =
        (Z ω) ^ 2 + (-2 * c) * Z ω + c ^ 2 * I ω := by
    have hZI : Z ω * I ω = Z ω :=
      inducedDegreeCount_mul_vertexIndicator H v ω
    have hI : (I ω) ^ 2 = I ω := vertexIndicator_sq H v ω
    calc
      (Z ω - c * I ω) ^ 2 =
        (Z ω) ^ 2 - 2 * c * (Z ω * I ω) +
          c ^ 2 * (I ω) ^ 2 := by ring
      _ = (Z ω) ^ 2 + (-2 * c) * Z ω + c ^ 2 * I ω := by
        rw [hZI, hI]
        ring
  calc
    FiniteBernoulli.expect p (fun ω => (Z ω - c * I ω) ^ 2) =
      FiniteBernoulli.expect p
        (fun ω => (Z ω) ^ 2 + (-2 * c) * Z ω + c ^ 2 * I ω) := by
      congr 1
      funext ω
      exact hpoint ω
    _ = FiniteBernoulli.expect p (fun ω => (Z ω) ^ 2) +
          (-2 * c) * FiniteBernoulli.expect p Z +
          c ^ 2 * FiniteBernoulli.expect p I := by
      rw [expect_add, expect_add, expect_mul_const, expect_mul_const]
    _ = FiniteBernoulli.expect p (fun ω => (Z ω) ^ 2) -
          2 * c * FiniteBernoulli.expect p Z +
          c ^ 2 * Real.exp (-a) := by
      have hI :
          FiniteBernoulli.expect p I = Real.exp (-a) := by
        exact (FiniteBernoulli.expect_eventIndicator p
          {ω | vertexSurvives H ω v}).trans
            (prob_vertexSurvives H a hD hv)
      rw [hI]
      ring
theorem expect_centered_inducedDegreeCount_sq_le_raw
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices)
    {c : ℝ} (hc : 0 ≤ c) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
        ((incidentEdges H v).card : ℝ) ^ 2 *
          Real.exp
            (-(((2 * r - 1 : ℕ) : ℝ) * a) +
              (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ)))) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) -
        2 * c * ((H.degree v : ℝ) * Real.exp (-((r : ℝ) * a))) +
        c ^ 2 * Real.exp (-a) := by
  have hcodeg :
      ∀ u ∈ H.vertices, ∀ w ∈ H.vertices, u ≠ w →
        H.codegree u w ≤ B := by
    intro u hu w hw hne
    exact (H.codegree_le_maxCodegree hu hw hne).trans hB
  have hsecond :=
    expect_inducedDegreeCount_sq_le_raw H hunif hcap hcodeg ha hD v
  have hfirst :=
    expect_inducedDegreeCount_ge H hunif hcap ha hD v
  have hnegative : -2 * c ≤ 0 := by linarith
  have hfirst' :
      (-2 * c) *
        FiniteBernoulli.expect
          (FiniteBernoulli.expMarkProbability (rate H a D))
          (inducedDegreeCount H v) ≤
      (-2 * c) * ((H.degree v : ℝ) *
        Real.exp (-((r : ℝ) * a))) :=
    mul_le_mul_of_nonpos_left hfirst hnegative
  rw [expect_centered_inducedDegreeCount_sq H a c hD hv]
  linarith
/-- Center at the degree predicted by independent vertex survival. -/
theorem expect_centered_inducedDegreeCount_sq_le
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices) :
    let c := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 *
        Real.exp (-(k * a)) * (Real.exp (k ^ 2 * b) - 1) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
  dsimp
  let d := (H.degree v : ℝ)
  let k := ((2 * r - 1 : ℕ) : ℝ)
  let b := (B : ℝ) * (a / (D : ℝ))
  let s := a - (r : ℝ) * a
  let c := d * Real.exp s
  let q := Real.exp (-a)
  let t := Real.exp (-(r : ℝ) * a)
  let base := Real.exp (-(k * a))
  have hk : k = 2 * (r : ℝ) - 1 := by
    dsimp [k]
    have hle : 1 ≤ 2 * r := by omega
    rw [Nat.cast_sub hle]
    norm_num
  have hexp1 : Real.exp (-a) * Real.exp s = t := by
    calc
      Real.exp (-a) * Real.exp s = Real.exp (-a + s) :=
        (Real.exp_add _ _).symm
      _ = t := by
        congr 1
        dsimp [s, t]
        ring
  have hqc : q * c = d * t := by
    calc
      q * c = d * (Real.exp (-a) * Real.exp s) := by
        dsimp [q, c]
        ring
      _ = d * t := by rw [hexp1]
  have hexp2 : Real.exp s * t = base := by
    calc
      Real.exp s * t =
          Real.exp (s + (-(r : ℝ) * a)) := by
        dsimp [t]
        rw [Real.exp_add]
      _ = base := by
        congr 1
        dsimp [s, base]
        rw [hk]
        ring
  have hqc2 : c ^ 2 * q = d ^ 2 * base := by
    calc
      c ^ 2 * q = c * (q * c) := by ring
      _ = (d * Real.exp s) * (d * t) := by rw [hqc]
      _ = d ^ 2 * (Real.exp s * t) := by ring
      _ = d ^ 2 * base := by rw [hexp2]
  have hexp3 :
      Real.exp (-(k * a) + k ^ 2 * b) =
        base * Real.exp (k ^ 2 * b) := by
    dsimp [base]
    rw [Real.exp_add]
  have hraw :=
    expect_centered_inducedDegreeCount_sq_le_raw H hunif hcap hB ha hD hv
      (c := c) (by positivity)
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω =>
          (inducedDegreeCount H v ω -
            c * FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      d ^ 2 * Real.exp (-(k * a) + k ^ 2 * b) +
        ((doublyIntersectingPairs H v).card : ℝ) * q -
        2 * c * (d * t) + c ^ 2 * q := by
      simpa only [d, k, b, q, t, c, incidentEdges, IndexedHypergraph.degree, neg_mul]
        using hraw
    _ = d ^ 2 * base * (Real.exp (k ^ 2 * b) - 1) +
          ((doublyIntersectingPairs H v).card : ℝ) * q := by
      rw [hexp3, ← hqc]
      nlinarith [hqc2]
theorem expect_centered_inducedDegreeCount_sq_le_linear
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1) :
    let c := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 *
        Real.exp (-(k * a)) * (2 * (k ^ 2 * b)) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
  dsimp
  let k := ((2 * r - 1 : ℕ) : ℝ)
  let b := (B : ℝ) * (a / (D : ℝ))
  let x := k ^ 2 * b
  have hx : 0 ≤ x := by
    dsimp [x, b]
    positivity
  have hAbs : |x| ≤ 1 := by
    simpa [abs_of_nonneg hx, x, k, b] using hsmall
  have hexpGap : Real.exp x - 1 ≤ 2 * x := by
    calc
      Real.exp x - 1 ≤ |Real.exp x - 1| := le_abs_self _
      _ ≤ 2 * |x| := Real.abs_exp_sub_one_le hAbs
      _ = 2 * x := by rw [abs_of_nonneg hx]
  have hcoeff : 0 ≤
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) := by
    positivity
  have hraw :=
    expect_centered_inducedDegreeCount_sq_le H hr hunif hcap hB ha hD hv
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω =>
          (inducedDegreeCount H v ω -
            (H.degree v : ℝ) *
              Real.exp (a - (r : ℝ) * a) *
              FiniteBernoulli.eventIndicator
                {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) *
        (Real.exp x - 1) +
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
      simpa only [k, b, x] using hraw
    _ ≤ (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) *
          (2 * x) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hexpGap hcoeff) _
theorem expect_centered_inducedDegreeCount_sq_le_global
    (H : IndexedHypergraph V E)
    {r B D : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    {v : V} (hv : v ∈ H.vertices)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1) :
    let c := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (inducedDegreeCount H v ω -
          c * FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
        ((B * (r * D) : ℕ) : ℝ) := by
  dsimp
  let k := ((2 * r - 1 : ℕ) : ℝ)
  let b := (B : ℝ) * (a / (D : ℝ))
  have hd : (H.degree v : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hcap v hv
  have hdSq : (H.degree v : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
    have hnonneg : 0 ≤ (H.degree v : ℝ) := by positivity
    nlinarith
  have hbase : Real.exp (-(k * a)) ≤ 1 := by
    have hk : 0 ≤ k := by positivity
    have hneg : -(k * a) ≤ 0 := neg_nonpos.mpr (mul_nonneg hk ha)
    simpa using (Real.exp_le_exp.mpr hneg :
      Real.exp (-(k * a)) ≤ Real.exp 0)
  have hcoeff :
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) ≤
        (D : ℝ) ^ 2 := by
    calc
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) ≤
        (H.degree v : ℝ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = (H.degree v : ℝ) ^ 2 := by ring
      _ ≤ (D : ℝ) ^ 2 := hdSq
  have hmult : 0 ≤ 2 * (k ^ 2 * b) := by
    dsimp [b]
    positivity
  have hbad : ((doublyIntersectingPairs H v).card : ℝ) ≤
      ((B * (r * D) : ℕ) : ℝ) := by
    exact_mod_cast card_doublyIntersectingPairs_le H hunif hv hB (hcap v hv)
  have hq : Real.exp (-a) ≤ 1 := by
    have hneg : -a ≤ 0 := by linarith
    simpa using (Real.exp_le_exp.mpr hneg :
      Real.exp (-a) ≤ Real.exp 0)
  have hbadTerm :
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) ≤
        ((B * (r * D) : ℕ) : ℝ) := by
    calc
      ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) ≤
        ((doublyIntersectingPairs H v).card : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = ((doublyIntersectingPairs H v).card : ℝ) := by ring
      _ ≤ ((B * (r * D) : ℕ) : ℝ) := hbad
  have hraw :=
    expect_centered_inducedDegreeCount_sq_le_linear H hr hunif hcap hB
      ha hD hv hsmall
  calc
    FiniteBernoulli.expect
        (FiniteBernoulli.expMarkProbability (rate H a D))
        (fun ω =>
          (inducedDegreeCount H v ω -
            (H.degree v : ℝ) *
              Real.exp (a - (r : ℝ) * a) *
              FiniteBernoulli.eventIndicator
                {ω | vertexSurvives H ω v} ω) ^ 2) ≤
      (H.degree v : ℝ) ^ 2 * Real.exp (-(k * a)) *
          (2 * (k ^ 2 * b)) +
        ((doublyIntersectingPairs H v).card : ℝ) * Real.exp (-a) := by
      simpa only [k, b] using hraw
    _ ≤ (D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
        ((B * (r * D) : ℕ) : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoeff hmult) hbadTerm
omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- A unit of integer rounding plus centered deviation pays for a vertex's
positive degree excess after the survivor step. -/
theorem vertex_degreeExcess_le_abs_centered
    (H : IndexedHypergraph V E) (Dnext : ℕ)
    (ω : E ⊕ V → Bool) (v : V) (c : ℝ)
    (hc : c ≤ (Dnext : ℝ) + 1) :
    (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
      FiniteBernoulli.eventIndicator
        {ω | vertexSurvives H ω v} ω ≤
      |inducedDegreeCount H v ω -
        c * FiniteBernoulli.eventIndicator
          {ω | vertexSurvives H ω v} ω| +
        FiniteBernoulli.eventIndicator
          {ω | vertexSurvives H ω v} ω := by
  classical
  let Z := inducedDegreeCount H v ω
  let I := FiniteBernoulli.eventIndicator
    {ω | vertexSurvives H ω v} ω
  have hZ :
      Z = (((H.induce (survivingVertices H ω)).degree v : ℝ)) :=
    inducedDegreeCount_eq_degree H v ω
  change
    (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) * I ≤
      |Z - c * I| + I
  by_cases hs : vertexSurvives H ω v
  · have hI : I = 1 := by simp [I, FiniteBernoulli.eventIndicator, hs]
    rw [hI]
    simp only [mul_one]
    by_cases hdeg :
        (H.induce (survivingVertices H ω)).degree v ≤ Dnext
    · have hzero :
          (H.induce (survivingVertices H ω)).degree v - Dnext = 0 :=
        Nat.sub_eq_zero_of_le hdeg
      rw [hzero]
      norm_num
      exact add_nonneg (abs_nonneg _) (by norm_num)
    · have hle :
          Dnext ≤ (H.induce (survivingVertices H ω)).degree v := by omega
      have hcast :
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) =
            Z - (Dnext : ℝ) := by
        rw [Nat.cast_sub hle, hZ]
      rw [hcast]
      have habs : Z - c ≤ |Z - c| := le_abs_self _
      linarith
  · have hI : I = 0 := by simp [I, FiniteBernoulli.eventIndicator, hs]
    rw [hI]
    simp
omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem induced_degreeExcess_eq_indicator_sum
    (H : IndexedHypergraph V E) (Dnext : ℕ)
    (ω : E ⊕ V → Bool) :
    (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ) =
      H.vertices.sum (fun v =>
        ((((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ)) *
          FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) := by
  classical
  let J := H.induce (survivingVertices H ω)
  have hJvertices :
      J.vertices = H.vertices.filter (vertexSurvives H ω) := by
    simp [J, survivingVertices,
      Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
  calc
    ((J.degreeExcess Dnext : ℕ) : ℝ) =
      J.vertices.sum (fun v => (((J.degree v - Dnext : ℕ) : ℝ))) := by
        simp [IndexedHypergraph.degreeExcess]
    _ = (H.vertices.filter (vertexSurvives H ω)).sum
          (fun v => (((J.degree v - Dnext : ℕ) : ℝ))) := by
      rw [hJvertices]
    _ = H.vertices.sum (fun v =>
          if vertexSurvives H ω v then
            (((J.degree v - Dnext : ℕ) : ℝ)) else 0) := by
      rw [Finset.sum_filter]
    _ = H.vertices.sum (fun v =>
          (((J.degree v - Dnext : ℕ) : ℝ)) *
            FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω) := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hs : vertexSurvives H ω v
      · simp [FiniteBernoulli.eventIndicator, hs]
      · simp [FiniteBernoulli.eventIndicator, hs]
theorem expect_vertex_degreeExcess_le (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    {v : V} (hv : v ∈ H.vertices) :
    let _ := (H.degree v : ℝ) *
      Real.exp (a - (r : ℝ) * a)
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
          FiniteBernoulli.eventIndicator
            {ω | vertexSurvives H ω v} ω) ≤
      Real.sqrt
        ((D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
          ((B * (r * D) : ℕ) : ℝ)) +
        Real.exp (-a) := by
  dsimp
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let c := (H.degree v : ℝ) * Real.exp (a - (r : ℝ) * a)
  let I := fun ω => FiniteBernoulli.eventIndicator
    {ω | vertexSurvives H ω v} ω
  let X := fun ω => inducedDegreeCount H v ω - c * I ω
  let M := (D : ℝ) ^ 2 *
      (2 * (((2 * r - 1 : ℕ) : ℝ) ^ 2 *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  have hcv : c ≤ (Dnext : ℝ) + 1 := by
    have hd : (H.degree v : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast hcap v hv
    have hfac : 0 ≤ Real.exp (a - (r : ℝ) * a) :=
      (Real.exp_pos _).le
    exact (mul_le_mul_of_nonneg_right hd hfac).trans hthreshold
  have hpoint (ω : E ⊕ V → Bool) :
      (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
        I ω ≤ |X ω| + I ω :=
    vertex_degreeExcess_le_abs_centered H Dnext ω v c hcv
  have hcs := FiniteBernoulli.expect_abs_le_sqrt_expect_sq p hp X
  have hmoment :
      FiniteBernoulli.expect p (fun ω => (X ω) ^ 2) ≤ M := by
    simpa only [p, X, I, c, M] using
      (expect_centered_inducedDegreeCount_sq_le_global H hr hunif
        hcap hB ha hD hv hsmall)
  have hsqrt :
      Real.sqrt (FiniteBernoulli.expect p (fun ω => (X ω) ^ 2)) ≤
        Real.sqrt M :=
    Real.sqrt_le_sqrt hmoment
  have hI : FiniteBernoulli.expect p I = Real.exp (-a) := by
    exact (FiniteBernoulli.expect_eventIndicator p
      {ω | vertexSurvives H ω v}).trans
        (prob_vertexSurvives H a hD hv)
  calc
    FiniteBernoulli.expect p
        (fun ω =>
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
            I ω) ≤
      FiniteBernoulli.expect p (fun ω => |X ω| + I ω) :=
      expect_mono p hp _ _ hpoint
    _ = FiniteBernoulli.expect p (fun ω => |X ω|) +
        FiniteBernoulli.expect p I := expect_add p _ _
    _ ≤ Real.sqrt M + Real.exp (-a) := by
      rw [hI]
      linarith
/-- Expected total degree excess in the induced survivor hypergraph. -/
theorem expect_induced_degreeExcess_le (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1) :
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ)) ≤
      (H.vertices.card : ℝ) *
        (Real.sqrt
          ((D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
            ((B * (r * D) : ℕ) : ℝ)) +
          Real.exp (-a)) := by
  dsimp
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let M := (D : ℝ) ^ 2 *
      (2 * (((2 * r - 1 : ℕ) : ℝ) ^ 2 *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)
  have hpoint (v : V) (hv : v ∈ H.vertices) :
      FiniteBernoulli.expect p
        (fun ω =>
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
            FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω) ≤
        Real.sqrt M + Real.exp (-a) := by
    simpa only [p, M] using
      (expect_vertex_degreeExcess_le H hr hunif hcap hB ha hD
        hsmall hthreshold hv)
  calc
    FiniteBernoulli.expect p
        (fun ω =>
          (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ)) =
      FiniteBernoulli.expect p
        (fun ω => H.vertices.sum (fun v =>
          (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
            FiniteBernoulli.eventIndicator
              {ω | vertexSurvives H ω v} ω)) := by
      congr 1
      funext ω
      exact induced_degreeExcess_eq_indicator_sum H Dnext ω
    _ = H.vertices.sum (fun v =>
        FiniteBernoulli.expect p
          (fun ω =>
            (((H.induce (survivingVertices H ω)).degree v - Dnext : ℕ) : ℝ) *
              FiniteBernoulli.eventIndicator
                {ω | vertexSurvives H ω v} ω)) :=
      FiniteBernoulli.expect_sum p H.vertices _
    _ ≤ H.vertices.sum (fun _ => Real.sqrt M + Real.exp (-a)) :=
      Finset.sum_le_sum hpoint
    _ = (H.vertices.card : ℝ) *
          (Real.sqrt M + Real.exp (-a)) := by
      simp
      ring
/-- Choose the deterministic trim after each realized marking configuration. -/
noncomputable def trimmedNext (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    (Dnext : ℕ) (ω : E ⊕ V → Bool) : IndexedHypergraph V E :=
  Classical.choose ((sampledRound H ω).exists_trimmed_next hunif Dnext)

omit [Fintype V] [Fintype E] in
theorem trimmedNext_spec (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    (Dnext : ℕ) (ω : E ⊕ V → Bool) :
    let K := trimmedNext H hunif Dnext ω
    K.vertices = survivingVertices H ω ∧
    K.edges ⊆ (sampledRound H ω).nextBase.edges ∧
    K.IsUniform r ∧
    (∀ v ∈ K.vertices, K.degree v ≤ Dnext) ∧
    (∀ u v, K.codegree u v ≤ H.codegree u v) ∧
    (K.degreeDeficit Dnext +
      r * (sampledRound H ω).nextBase.edges.card ≤
      (survivingVertices H ω).card * Dnext +
        r * (sampledRound H ω).nextBase.degreeExcess Dnext) ∧
      K.edge = H.edge := by
  dsimp [trimmedNext]
  exact Classical.choose_spec
    ((sampledRound H ω).exists_trimmed_next hunif Dnext)

omit [Fintype V] [Fintype E] in
theorem trimmedNext_deficit_le (H : IndexedHypergraph V E)
    {r : ℕ} (hunif : H.IsUniform r)
    (Dnext : ℕ) (ω : E ⊕ V → Bool) :
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) +
      (r : ℝ) * (inducedEdgeCount H ω) ≤
      ((survivingVertices H ω).card : ℝ) * (Dnext : ℝ) +
        (r : ℝ) *
          (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ) := by
  have hNat := (trimmedNext_spec H hunif Dnext ω).2.2.2.2.2.1
  have hNat' :
      (trimmedNext H hunif Dnext ω).degreeDeficit Dnext +
        r * (H.induce (survivingVertices H ω)).edges.card ≤
      (survivingVertices H ω).card * Dnext +
        r * (H.induce (survivingVertices H ω)).degreeExcess Dnext := by
    simpa [MatchingRound.nextBase, sampledRound] using hNat
  have hReal : (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) +
      (r : ℝ) *
        (((H.induce (survivingVertices H ω)).edges.card : ℕ) : ℝ) ≤
      ((survivingVertices H ω).card : ℝ) * (Dnext : ℝ) +
        (r : ℝ) *
          (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ) := by
    exact_mod_cast hNat'
  simpa only [inducedEdgeCount_eq_card H ω] using hReal
/-- One-round expected degree-deficit recurrence after choosing the trim. -/
theorem expect_trimmedNext_degreeDeficit_le
    (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    (hscale :
      (Dnext : ℝ) * Real.exp (-a) ≤
        (D : ℝ) * Real.exp (-((r : ℝ) * a))) :
    let k := ((2 * r - 1 : ℕ) : ℝ)
    let b := (B : ℝ) * (a / (D : ℝ))
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ)) ≤
      Real.exp (-((r : ℝ) * a)) * (H.degreeDeficit D : ℝ) +
        (r : ℝ) * (H.vertices.card : ℝ) *
          (Real.sqrt
            ((D : ℝ) ^ 2 * (2 * (k ^ 2 * b)) +
              ((B * (r * D) : ℕ) : ℝ)) +
            Real.exp (-a)) := by
  dsimp
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let S := (H.degreeDeficit D : ℝ)
  let n := (H.vertices.card : ℝ)
  let m := (H.edges.card : ℝ)
  let q := Real.exp (-a)
  let er := Real.exp (-((r : ℝ) * a))
  let K := Real.sqrt
    ((D : ℝ) ^ 2 *
      (2 * (((2 * r - 1 : ℕ) : ℝ) ^ 2 *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)) + q
  let X : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ)
  let M : (E ⊕ V → Bool) → ℝ := inducedEdgeCount H
  let N : (E ⊕ V → Bool) → ℝ := fun ω => ((survivingVertices H ω).card : ℝ)
  let F : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((H.induce (survivingVertices H ω)).degreeExcess Dnext : ℕ) : ℝ)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  have hpoint (ω : E ⊕ V → Bool) :
      X ω + (r : ℝ) * M ω ≤
        (Dnext : ℝ) * N ω + (r : ℝ) * F ω := by
    dsimp [X, M, N, F]
    simpa [mul_comm] using trimmedNext_deficit_le H hunif Dnext ω
  have hmono := expect_mono p hp
    (fun ω => X ω + (r : ℝ) * M ω)
    (fun ω => (Dnext : ℝ) * N ω + (r : ℝ) * F ω) hpoint
  have hlinear :
      FiniteBernoulli.expect p X +
        (r : ℝ) * FiniteBernoulli.expect p M ≤
      (Dnext : ℝ) * FiniteBernoulli.expect p N +
        (r : ℝ) * FiniteBernoulli.expect p F := by
    simpa only [expect_add, expect_mul_const] using hmono
  have hn : FiniteBernoulli.expect p N = n * q := by
    simpa only [p, N, n, q] using expect_survivingVertices_card H a hD
  have hm : m * er ≤ FiniteBernoulli.expect p M := by
    simpa only [p, M, m, er] using
      expect_inducedEdgeCount_ge H hunif hcap ha hD
  have hF : FiniteBernoulli.expect p F ≤ n * K := by
    simpa only [p, F, n, q, K] using
      expect_induced_degreeExcess_le H hr hunif hcap hB ha hD
        hsmall hthreshold
  have hscaleN :
      (Dnext : ℝ) * (n * q) ≤ (n * (D : ℝ)) * er := by
    calc
      (Dnext : ℝ) * (n * q) = n * ((Dnext : ℝ) * q) := by ring
      _ ≤ n * ((D : ℝ) * er) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (n * (D : ℝ)) * er := by ring
  have hrnonneg : 0 ≤ (r : ℝ) := by positivity
  have hm' : (r : ℝ) * (m * er) ≤
      (r : ℝ) * FiniteBernoulli.expect p M :=
    mul_le_mul_of_nonneg_left hm hrnonneg
  have hF' : (r : ℝ) * FiniteBernoulli.expect p F ≤
      (r : ℝ) * (n * K) :=
    mul_le_mul_of_nonneg_left hF hrnonneg
  have hcount : S + (r : ℝ) * m = n * (D : ℝ) := by
    dsimp [S, m, n]
    exact_mod_cast H.degreeDeficit_add_edges hunif hcap
  have hcountEr :
      (S + (r : ℝ) * m) * er = (n * (D : ℝ)) * er :=
    congrArg (fun x : ℝ => x * er) hcount
  dsimp [X, p, S, n, er, K] at *
  nlinarith [hlinear, hn, hm', hF', hscaleN, hcountEr]
/-- The trimmed deficit, normalized by the next degree cap, has a
one-round additive error. -/
theorem expect_trimmedNext_normalizedDeficit_le
    (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a δ : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (hDnext : 0 < Dnext)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    (hscale :
      (Dnext : ℝ) * Real.exp (-a) ≤
        (D : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hlower :
      (D : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ Dnext)
    (herror :
      (r : ℝ) *
        (Real.sqrt
          ((D : ℝ) ^ 2 *
              (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ))))) +
            ((B * (r * D) : ℕ) : ℝ)) +
          Real.exp (-a)) ≤ δ * (Dnext : ℝ)) :
    FiniteBernoulli.expect
      (FiniteBernoulli.expMarkProbability (rate H a D))
      (fun ω =>
        (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
          (Dnext : ℝ)) ≤
      (H.degreeDeficit D : ℝ) / (D : ℝ) +
        δ * (H.vertices.card : ℝ) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let S := (H.degreeDeficit D : ℝ)
  let n := (H.vertices.card : ℝ)
  let er := Real.exp (-((r : ℝ) * a))
  let K := Real.sqrt
    ((D : ℝ) ^ 2 *
      (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))))) +
      ((B * (r * D) : ℕ) : ℝ)) + Real.exp (-a)
  let X : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ)
  have hraw : FiniteBernoulli.expect p X ≤ er * S + (r : ℝ) * n * K := by
    simpa only [p, X, S, n, er, K] using
      (expect_trimmedNext_degreeDeficit_le H hr hunif hcap hB ha hD
        hsmall hthreshold hscale)
  have hlinear :
      FiniteBernoulli.expect p (fun ω => X ω / (Dnext : ℝ)) =
        FiniteBernoulli.expect p X / (Dnext : ℝ) := by
    calc
      FiniteBernoulli.expect p (fun ω => X ω / (Dnext : ℝ)) =
        FiniteBernoulli.expect p
          (fun ω => ((Dnext : ℝ)⁻¹) * X ω) := by
            congr 1
            funext ω
            ring
      _ = ((Dnext : ℝ)⁻¹) * FiniteBernoulli.expect p X :=
        expect_mul_const p _ X
      _ = FiniteBernoulli.expect p X / (Dnext : ℝ) := by ring
  have hDn : (0 : ℝ) < D := by exact_mod_cast hD
  have hDnextn : (0 : ℝ) < Dnext := by exact_mod_cast hDnext
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hscaleS : er * S ≤ (S / (D : ℝ)) * (Dnext : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hlower (div_nonneg hS hDn.le)
    have hident : (D : ℝ) * er * (S / (D : ℝ)) = er * S := by
      field_simp
    nlinarith
  have herrorN : (r : ℝ) * n * K ≤ δ * n * (Dnext : ℝ) := by
    have h := mul_le_mul_of_nonneg_left herror hn
    nlinarith
  have hbound :
      FiniteBernoulli.expect p X ≤
        ((S / (D : ℝ)) + δ * n) * (Dnext : ℝ) := by
    nlinarith [hraw, hscaleS, herrorN]
  have hdiv := (div_le_iff₀ hDnextn).mpr hbound
  simpa only [p, X, S, n, hlinear] using hdiv
/-- Select one marking configuration that controls the backward potential:
surviving vertices, normalized deficit, and unmatched waste together. -/
theorem exists_round_potential_le
    (H : IndexedHypergraph V E)
    {r B D Dnext : ℕ} (hr : 1 ≤ r) (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    (hB : H.maxCodegree ≤ B)
    {a δ A C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hD : 0 < D) (hDnext : 0 < Dnext)
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D : ℝ))) ≤ 1)
    (hthreshold :
      (D : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (Dnext : ℝ) + 1)
    (hscale :
      (Dnext : ℝ) * Real.exp (-a) ≤
        (D : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hlower :
      (D : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ Dnext)
    (herror :
      (r : ℝ) *
        (Real.sqrt
          ((D : ℝ) ^ 2 *
              (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D : ℝ))))) +
            ((B * (r * D) : ℕ) : ℝ)) +
          Real.exp (-a)) ≤ δ * (Dnext : ℝ)) :
    ∃ ω : E ⊕ V → Bool,
      A * ((survivingVertices H ω).card : ℝ) +
        C *
          ((((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
            (Dnext : ℝ)) +
        ((sampledRound H ω).waste.card : ℝ) ≤
      (A * Real.exp (-a) + C * δ + (r : ℝ) * a ^ 2) *
          (H.vertices.card : ℝ) +
        (C + a) * ((H.degreeDeficit D : ℕ) : ℝ) / (D : ℝ) := by
  let p := FiniteBernoulli.expMarkProbability (rate H a D)
  let N : (E ⊕ V → Bool) → ℝ := fun ω =>
    ((survivingVertices H ω).card : ℝ)
  let Z : (E ⊕ V → Bool) → ℝ := fun ω =>
    (((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
      (Dnext : ℝ)
  let W : (E ⊕ V → Bool) → ℝ := fun ω =>
    ((sampledRound H ω).waste.card : ℝ)
  let X : (E ⊕ V → Bool) → ℝ := fun ω =>
    A * N ω + C * Z ω + W ω
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    markProbability_bounds H ha hD hcap
  obtain ⟨ω, hω⟩ := exists_le_expect p hp X
  have hlin : FiniteBernoulli.expect p X =
      A * FiniteBernoulli.expect p N +
        C * FiniteBernoulli.expect p Z +
          FiniteBernoulli.expect p W := by
    dsimp [X]
    rw [expect_add, expect_add, expect_mul_const, expect_mul_const]
  have hN : FiniteBernoulli.expect p N =
      (H.vertices.card : ℝ) * Real.exp (-a) := by
    simpa only [p, N] using expect_survivingVertices_card H a hD
  have hZ : FiniteBernoulli.expect p Z ≤
      (H.degreeDeficit D : ℝ) / (D : ℝ) +
        δ * (H.vertices.card : ℝ) := by
    simpa only [p, Z] using
      (expect_trimmedNext_normalizedDeficit_le H hr hunif hcap hB
        ha hD hDnext hsmall hthreshold hscale hlower herror)
  have hW : FiniteBernoulli.expect p W ≤
      a * ((H.degreeDeficit D : ℕ) : ℝ) / (D : ℝ) +
        (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ) := by
    have h := expect_waste_le_simplified H hunif hcap ha hD
    convert h using 1; ring
  refine ⟨ω, ?_⟩
  have hCZ := mul_le_mul_of_nonneg_left hZ hC
  dsimp [X, N, Z, W] at hω
  calc
    A * ((survivingVertices H ω).card : ℝ) +
          C *
            ((((trimmedNext H hunif Dnext ω).degreeDeficit Dnext : ℕ) : ℝ) /
              (Dnext : ℝ)) +
          ((sampledRound H ω).waste.card : ℝ) ≤
        FiniteBernoulli.expect p X := hω
    _ = A * FiniteBernoulli.expect p N +
          C * FiniteBernoulli.expect p Z +
            FiniteBernoulli.expect p W := hlin
    _ ≤ (A * Real.exp (-a) + C * δ + (r : ℝ) * a ^ 2) *
          (H.vertices.card : ℝ) +
        (C + a) * ((H.degreeDeficit D : ℕ) : ℝ) / (D : ℝ) := by
      rw [hN]
      calc
        A * ((H.vertices.card : ℝ) * Real.exp (-a)) +
            C * FiniteBernoulli.expect p Z +
              FiniteBernoulli.expect p W ≤
          A * ((H.vertices.card : ℝ) * Real.exp (-a)) +
            C * ((H.degreeDeficit D : ℝ) / (D : ℝ) +
              δ * (H.vertices.card : ℝ)) +
            (a * (H.degreeDeficit D : ℝ) / (D : ℝ) +
              (r : ℝ) * a ^ 2 * (H.vertices.card : ℝ)) := by
                linarith [hCZ, hW]
        _ = _ := by ring
/-- A residual hypergraph together with all accepted edge copies and the
number of vertices deleted without coverage in earlier rounds. -/
structure MatchingState (H₀ : IndexedHypergraph V E)
    (r B : ℕ) (D : ℕ → ℕ) (i : ℕ) where
  residual : IndexedHypergraph V E
  accepted : Finset E
  wasted : ℕ
  vertices_subset : residual.vertices ⊆ H₀.vertices
  edges_subset : residual.edges ⊆ H₀.edges
  edge_eq : residual.edge = H₀.edge
  uniform : residual.IsUniform r
  degree_cap : ∀ v ∈ residual.vertices, residual.degree v ≤ D i
  codegree_cap : residual.maxCodegree ≤ B
  accepted_matching : H₀.IsMatching accepted
  residual_disjoint_accepted : Disjoint residual.vertices (H₀.covered accepted)
  partition_card :
    (H₀.covered accepted).card + residual.vertices.card + wasted = H₀.vertices.card

/-- The initial residual state before any marking. -/
def initialMatchingState (H₀ : IndexedHypergraph V E)
    {r B : ℕ} (D : ℕ → ℕ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B) :
    MatchingState H₀ r B D 0 where
  residual := H₀
  accepted := ∅
  wasted := 0
  vertices_subset := Finset.Subset.rfl
  edges_subset := Finset.Subset.rfl
  edge_eq := rfl
  uniform := hunif
  degree_cap := hcap
  codegree_cap := hB
  accepted_matching := by
    constructor
    · simp
    · simp
  residual_disjoint_accepted := by simp [IndexedHypergraph.covered]
  partition_card := by simp [IndexedHypergraph.covered]

/-- The quantity controlled by the backward potential at round `i`. -/
noncomputable def MatchingState.potential
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i)
    (q δ a β : ℝ) (T : ℕ) : ℝ :=
  Theorem2.lossPotentialA q δ a β T i * (s.residual.vertices.card : ℝ) +
    Theorem2.lossPotentialB a T i *
      ((s.residual.degreeDeficit (D i) : ℝ) / (D i : ℝ)) +
    (s.wasted : ℝ)
omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The residual and initial hypergraphs interpret every edge-copy label identically. -/
theorem MatchingState.covered_eq
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (F : Finset E) :
    s.residual.covered F = H₀.covered F := by
  simp only [IndexedHypergraph.covered, s.edge_eq]

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- A residual matching remains a matching in the original hypergraph. -/
theorem MatchingState.lift_matching
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) {F : Finset E}
    (hF : s.residual.IsMatching F) : H₀.IsMatching F := by
  constructor
  · exact hF.1.trans s.edges_subset
  · intro e he f hf hne
    simpa only [← s.edge_eq] using hF.2 he hf hne

omit [Fintype V] [Fintype E] in
private theorem matching_union_of_disjoint_covered
    (H : IndexedHypergraph V E) {M F : Finset E}
    (hM : H.IsMatching M) (hF : H.IsMatching F)
    (hdisj : Disjoint (H.covered M) (H.covered F)) :
    H.IsMatching (M ∪ F) := by
  classical
  constructor
  · exact Finset.union_subset hM.1 hF.1
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with heM | heF
    · rcases Finset.mem_union.mp hf with hfM | hfF
      · exact hM.2 heM hfM hne
      · apply Finset.disjoint_left.mpr
        intro v hve hvf
        exact (Finset.disjoint_left.mp hdisj)
          (Finset.mem_biUnion.mpr ⟨e, heM, hve⟩)
          (Finset.mem_biUnion.mpr ⟨f, hfF, hvf⟩)
    · rcases Finset.mem_union.mp hf with hfM | hfF
      · apply Finset.disjoint_left.mpr
        intro v hve hvf
        exact (Finset.disjoint_left.mp hdisj)
          (Finset.mem_biUnion.mpr ⟨f, hfM, hvf⟩)
          (Finset.mem_biUnion.mpr ⟨e, heF, hve⟩)
      · exact hF.2 heF hfF hne

omit [Fintype V] [Fintype E] in
/-- Extend the accumulated matching by a matching in the current residual. -/
theorem MatchingState.matching_union
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) {F : Finset E}
    (hF : s.residual.IsMatching F) :
    H₀.IsMatching (s.accepted ∪ F) := by
  have hcoveredF : H₀.covered F ⊆ s.residual.vertices := by
    rw [← s.covered_eq F]
    exact s.residual.covered_subset_vertices hF.1
  exact matching_union_of_disjoint_covered H₀ s.accepted_matching
    (s.lift_matching hF)
    (Finset.disjoint_of_subset_right hcoveredF
      s.residual_disjoint_accepted.symm)

omit [Fintype V] [Fintype E] in
private theorem covered_union (H : IndexedHypergraph V E) (M F : Finset E) :
    H.covered (M ∪ F) = H.covered M ∪ H.covered F := by
  exact Finset.union_biUnion
/-- Update the residual state after any marking and deterministic trim. The
combinatorial invariants hold for every outcome. -/
noncomputable def MatchingState.next
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    MatchingState H₀ r B D (i + 1) := by
  classical
  let H := s.residual
  let R := sampledRound H ω
  let K := trimmedNext H s.uniform (D (i + 1)) ω
  have hspec := trimmedNext_spec H s.uniform (D (i + 1)) ω
  have hverts : K.vertices ⊆ H.vertices := by
    rw [hspec.1]
    exact R.survivors_subset
  have hedges : K.edges ⊆ H.edges := by
    have hbase := H.induce_edges_subset (survivingVertices H ω)
    exact hspec.2.1.trans (by simp [MatchingRound.nextBase, sampledRound] at hbase ⊢)
  have hcoverA : H₀.covered R.accepted ⊆ H.vertices := by
    rw [← s.covered_eq R.accepted]
    exact R.accepted_covered_subset
  have hcoverDisj : Disjoint (H₀.covered s.accepted) (H₀.covered R.accepted) :=
    Finset.disjoint_of_subset_right hcoverA s.residual_disjoint_accepted.symm
  have hcoveredUnion : H₀.covered (s.accepted ∪ R.accepted) =
      H₀.covered s.accepted ∪ H₀.covered R.accepted :=
    covered_union H₀ s.accepted R.accepted
  refine {
    residual := K
    accepted := s.accepted ∪ R.accepted
    wasted := s.wasted + R.waste.card
    vertices_subset := hverts.trans s.vertices_subset
    edges_subset := hedges.trans s.edges_subset
    edge_eq := hspec.2.2.2.2.2.2.trans s.edge_eq
    uniform := hspec.2.2.1
    degree_cap := hspec.2.2.2.1
    codegree_cap := ?_
    accepted_matching := s.matching_union R.accepted_matching
    residual_disjoint_accepted := ?_
    partition_card := ?_
  }
  · unfold IndexedHypergraph.maxCodegree
    apply Finset.sup_le
    intro u hu
    apply Finset.sup_le
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    have hne : u ≠ v := hv'.1.symm
    have hcodeg := hspec.2.2.2.2.1 u v
    exact (hcodeg.trans
      (H.codegree_le_maxCodegree (hverts hu) (hverts hv'.2) hne)).trans
        s.codegree_cap
  · apply Finset.disjoint_left.mpr
    intro v hv hvcov
    have hvR : v ∈ R.survivors := by
      change v ∈ survivingVertices H ω
      rw [← hspec.1]
      exact hv
    rw [hcoveredUnion] at hvcov
    rcases Finset.mem_union.mp hvcov with hvM | hvA
    · exact (Finset.disjoint_left.mp s.residual_disjoint_accepted)
        (R.survivors_subset hvR) hvM
    · have hvA' : v ∈ H.covered R.accepted := by
        change v ∈ s.residual.covered R.accepted
        rw [s.covered_eq R.accepted]
        exact hvA
      exact (Finset.disjoint_left.mp R.survivors_disjoint_accepted)
        hvR hvA'
  · have hround := R.waste_partition_card
    have hcardUnion :
        (H₀.covered (s.accepted ∪ R.accepted)).card =
          (H₀.covered s.accepted).card + (H₀.covered R.accepted).card := by
      rw [hcoveredUnion, Finset.card_union_of_disjoint hcoverDisj]
    have hcardA : (H₀.covered R.accepted).card =
        (H.covered R.accepted).card := by
      simpa only [H] using congrArg Finset.card (s.covered_eq R.accepted).symm
    have hcardK : K.vertices.card = R.survivors.card := by
      rw [hspec.1]
      rfl
    have hstart : (H₀.covered s.accepted).card + H.vertices.card +
        s.wasted = H₀.vertices.card := s.partition_card
    have hround' : K.vertices.card + (H₀.covered R.accepted).card +
        R.waste.card = H.vertices.card := by
      rw [hcardK, hcardA]
      exact hround
    rw [hcardUnion]
    omega
omit [Fintype V] [Fintype E] in
@[simp] theorem MatchingState.next_residual
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    (s.next ω).residual =
      trimmedNext s.residual s.uniform (D (i + 1)) ω := rfl

omit [Fintype V] [Fintype E] in
@[simp] theorem MatchingState.next_accepted
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    (s.next ω).accepted = s.accepted ∪ (sampledRound s.residual ω).accepted := rfl

omit [Fintype V] [Fintype E] in
@[simp] theorem MatchingState.next_wasted
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i) (ω : E ⊕ V → Bool) :
    (s.next ω).wasted = s.wasted + (sampledRound s.residual ω).waste.card := rfl
/-- Choose one round so that the backward potential does not increase. -/
theorem MatchingState.exists_next_potential_le
    {H₀ : IndexedHypergraph V E} {r B : ℕ} {D : ℕ → ℕ} {i : ℕ}
    (s : MatchingState H₀ r B D i)
    (T : ℕ) (hi : i < T)
    {a δ : ℝ} (ha : 0 ≤ a) (_hδ : 0 ≤ δ)
    (hr : 1 ≤ r) (hD : 0 < D i) (hDnext : 0 < D (i + 1))
    (hsmall :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        ((B : ℝ) * (a / (D i : ℝ))) ≤ 1)
    (hthreshold :
      (D i : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (D (i + 1) : ℝ) + 1)
    (hscale :
      (D (i + 1) : ℝ) * Real.exp (-a) ≤
        (D i : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hlower :
      (D i : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ D (i + 1))
    (herror :
      (r : ℝ) *
        (Real.sqrt
          ((D i : ℝ) ^ 2 *
              (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
                ((B : ℝ) * (a / (D i : ℝ))))) +
            ((B * (r * D i) : ℕ) : ℝ)) +
          Real.exp (-a)) ≤ δ * (D (i + 1) : ℝ)) :
    ∃ ω : E ⊕ V → Bool,
      (s.next ω).potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T ≤
        s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T := by
  let q := Real.exp (-a)
  let β := (r : ℝ) * a ^ 2
  let A := Theorem2.lossPotentialA q δ a β T (i + 1)
  let C := Theorem2.lossPotentialB a T (i + 1)
  have hC : 0 ≤ C := Theorem2.lossPotentialB_nonneg a ha T (i + 1)
  obtain ⟨ω, hselect⟩ :=
    exists_round_potential_le s.residual hr s.uniform s.degree_cap
      s.codegree_cap ha hC hD hDnext hsmall hthreshold hscale
      hlower herror (A := A)
  have hnext :
      (s.next ω).potential q δ a β T =
        A * ((survivingVertices s.residual ω).card : ℝ) +
          C *
            ((((trimmedNext s.residual s.uniform (D (i + 1)) ω).degreeDeficit
                (D (i + 1)) : ℕ) : ℝ) / (D (i + 1) : ℝ)) +
          ((sampledRound s.residual ω).waste.card : ℝ) +
          (s.wasted : ℝ) := by
    simp only [MatchingState.potential, MatchingState.next_residual,
      MatchingState.next_wasted, Nat.cast_add]
    rw [(trimmedNext_spec s.residual s.uniform (D (i + 1)) ω).1]
    dsimp [A, C]
    ring
  have hcurrent :
      s.potential q δ a β T =
        (A * q + C * δ + β) * (s.residual.vertices.card : ℝ) +
          (C + a) * ((s.residual.degreeDeficit (D i) : ℕ) : ℝ) /
            (D i : ℝ) +
          (s.wasted : ℝ) := by
    unfold MatchingState.potential
    rw [Theorem2.lossPotentialA_step q δ a β hi,
      Theorem2.lossPotentialB_step a hi]
    dsimp [A, C]
    ring
  refine ⟨ω, ?_⟩
  rw [hnext, hcurrent]
  dsimp [q, β] at hselect ⊢
  linarith [hselect]
/-- A coarse bound for the square-root error under degree-ratio and
half-life estimates. -/
theorem one_round_error_le_eight
    {r B D Dnext : ℕ} (hr : 2 ≤ r) (hB : 1 ≤ B)
    (hD : 0 < D)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hratio : (B : ℝ) / (D : ℝ) ≤ b)
    (hhalf : (D : ℝ) ≤ 2 * (Dnext : ℝ)) :
    (r : ℝ) *
      (Real.sqrt
        ((D : ℝ) ^ 2 *
            (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D : ℝ))))) +
          ((B * (r * D) : ℕ) : ℝ)) +
        Real.exp (-a)) ≤
      8 * (r : ℝ) ^ 2 * Real.sqrt b * (Dnext : ℝ) := by
  let R : ℝ := r
  let d : ℝ := D
  let C : ℝ := B
  let k : ℝ := (2 * r - 1 : ℕ)
  let M : ℝ := d ^ 2 * (2 * (k ^ 2 * (C * (a / d)))) +
    ((B * (r * D) : ℕ) : ℝ)
  have hR : 1 ≤ R := by dsimp [R]; exact_mod_cast (by omega : 1 ≤ r)
  have hR0 : 0 ≤ R := by linarith
  have hd : 0 < d := by dsimp [d]; exact_mod_cast hD
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBd : C ≤ d * b := by
    dsimp [C, d]
    nlinarith [(div_le_iff₀ hd).mp hratio]
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk : k ≤ 2 * R := by
    dsimp [k, R]
    have hnat : 2 * r - 1 ≤ 2 * r := Nat.sub_le _ _
    exact_mod_cast hnat
  have hkSq : k ^ 2 ≤ 4 * R ^ 2 := by nlinarith
  have hka : k ^ 2 * a ≤ k ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr ha1)]
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hcoeff : 2 * k ^ 2 * a + R ≤ 9 * R ^ 2 := by
    nlinarith [hkSq, hka, hR2]
  have hMident : M = d * C * (2 * k ^ 2 * a + R) := by
    dsimp [M, d, C, R]
    have hne : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
    simp only [Nat.cast_mul]
    field_simp
  have hMbound : M ≤ (3 * R * d * Real.sqrt b) ^ 2 := by
    calc
      M = d * C * (2 * k ^ 2 * a + R) := hMident
      _ ≤ d * C * (9 * R ^ 2) :=
        mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hd.le hC)
      _ ≤ (d * (d * b)) * (9 * R ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBd hd.le) (by positivity)
      _ = (3 * R * d * Real.sqrt b) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hb]
        ring
  have hroot : Real.sqrt M ≤ 3 * R * d * Real.sqrt b :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hMbound⟩
  have hbSq : b ^ 2 ≤ b := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hb1)]
  have hbroot : b ≤ Real.sqrt b := (Real.le_sqrt hb hb).mpr hbSq
  have hdb : 1 ≤ d * b := by
    have hBC : (1 : ℝ) ≤ C := by dsimp [C]; exact_mod_cast hB
    linarith
  have hdroot : 1 ≤ d * Real.sqrt b := by
    nlinarith [mul_le_mul_of_nonneg_left hbroot hd.le]
  have hq : Real.exp (-a) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hrootR : R * Real.sqrt M ≤ 3 * R ^ 2 * d * Real.sqrt b := by
    nlinarith [mul_le_mul_of_nonneg_left hroot hR0]
  have hqR : R * Real.exp (-a) ≤ R * d * Real.sqrt b := by
    nlinarith [mul_le_mul_of_nonneg_left hq hR0,
      mul_le_mul_of_nonneg_left hdroot hR0]
  have hRroot : R * d * Real.sqrt b ≤ R ^ 2 * d * Real.sqrt b := by
    have hnonneg : 0 ≤ d * Real.sqrt b := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hR2 hnonneg]
  have hfirst : R * (Real.sqrt M + Real.exp (-a)) ≤
      4 * R ^ 2 * d * Real.sqrt b := by
    nlinarith [hrootR, hqR, hRroot]
  have hlast : 4 * R ^ 2 * d * Real.sqrt b ≤
      8 * R ^ 2 * Real.sqrt b * (Dnext : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (by positivity : 0 ≤ 4 * R ^ 2 * Real.sqrt b)
    nlinarith
  simpa only [R, d, C, k, M] using hfirst.trans hlast
/-- Integer floors retain at least half the current cap and at least the exact
exponential survival scale when `a r ≤ 1/100` and `a D ≥ 4`. -/


theorem floor_decay_bounds
    {r D Dnext : ℕ} {a : ℝ}
    (hr : 2 ≤ r) (ha : 0 ≤ a)
    (har : (r : ℝ) * a ≤ 1 / 100)
    (had : 4 ≤ a * (D : ℝ))
    (hfloor : Real.exp ((1 - (r : ℝ)) * a) * (D : ℝ) <
      (Dnext : ℝ) + 1) :
    (D : ℝ) ≤ 2 * (Dnext : ℝ) ∧
      (D : ℝ) * Real.exp (-(r : ℝ) * a) ≤ (Dnext : ℝ) := by
  let R : ℝ := r
  let d : ℝ := D
  let e : ℝ := Real.exp ((1 - R) * a)
  let q : ℝ := Real.exp (-a)
  have hR : 2 ≤ R := by dsimp [R]; exact_mod_cast hr
  have ha1 : a ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : (0:ℝ) ≤ R-1)) ha]
  have hdpos : 0 < d := by
    by_contra h
    have hdle : d ≤ 0 := le_of_not_gt h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hdle]
  have hd4 : 4 ≤ d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hdpos.le]
  have he : 3 / 4 ≤ e := by
    have h := Real.add_one_le_exp ((1 - R) * a)
    dsimp [e]
    nlinarith [h, har, ha]
  have hepos : 0 < e := by dsimp [e]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hExp := Real.add_one_le_exp a
  have hqmul : (1 + a) * q ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hExp hqpos.le
    have hcancel : Real.exp a * q = 1 := by
      dsimp [q]
      rw [← Real.exp_add]
      simp
    nlinarith
  have hbound : 1 ≤ (1 + a) * (1 - a / 2) := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
  have hqgap : q ≤ 1 - a / 2 := by
    have hpos : 0 < 1 + a := by linarith
    apply le_of_mul_le_mul_left _ hpos
    nlinarith [hqmul, hbound]
  have hed : (3 / 4) * d ≤ e * d :=
    mul_le_mul_of_nonneg_right he hdpos.le
  have hfloor' : e * d < (Dnext : ℝ) + 1 := hfloor
  have hhalf : d ≤ 2 * (Dnext : ℝ) := by nlinarith [hed, hd4, hfloor']
  have hgap : a / 2 ≤ 1 - q := by linarith [hqgap]
  have hgap0 : 0 ≤ 1 - q := by linarith
  have hprod : 3 * a / 8 ≤ e * (1 - q) := by
    have h := mul_nonneg (sub_nonneg.mpr he) hgap0
    have h' := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (sub_nonneg.mpr hgap)
    nlinarith
  have hprodD : 1 ≤ e * (1 - q) * d := by
    have h := mul_le_mul_of_nonneg_right hprod hdpos.le
    nlinarith [had, h]
  have hexp : e * q = Real.exp (-R * a) := by
    dsimp [e,q]
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · simpa only [d] using hhalf
  · rw [← hexp]
    nlinarith [hfloor', hprodD]


/-- Explicit numerical hypotheses needed by every round of the finite
matching iteration. These are discharged by the paper's parameter choices. -/
structure MatchingSchedule (r B T : ℕ) (D : ℕ → ℕ)
    (a δ : ℝ) : Prop where
  rank_pos : 1 ≤ r
  rate_nonneg : 0 ≤ a
  error_nonneg : 0 ≤ δ
  degree_pos : ∀ i ≤ T, 0 < D i
  small : ∀ i < T,
    (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
      ((B : ℝ) * (a / (D i : ℝ))) ≤ 1
  threshold : ∀ i < T,
    (D i : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
      (D (i + 1) : ℝ) + 1
  scale : ∀ i < T,
    (D (i + 1) : ℝ) * Real.exp (-a) ≤
      (D i : ℝ) * Real.exp (-((r : ℝ) * a))
  lower : ∀ i < T,
    (D i : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ D (i + 1)
  error : ∀ i < T,
    (r : ℝ) *
      (Real.sqrt
        ((D i : ℝ) ^ 2 *
            (2 * ((((2 * r - 1 : ℕ) : ℝ) ^ 2) *
              ((B : ℝ) * (a / (D i : ℝ))))) +
          ((B * (r * D i) : ℕ) : ℝ)) +
        Real.exp (-a)) ≤ δ * (D (i + 1) : ℝ)

/-- Build a matching schedule from simple cap decay and codegree-ratio
bounds. Only one scalar smallness check and one scalar error budget remain. -/
theorem matchingSchedule_of_degree_bounds
    {r B T : ℕ} {D : ℕ → ℕ} {a δ b : ℝ}
    (hr : 2 ≤ r) (hB : 1 ≤ B)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hsmallBase :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) * a * b ≤ 1)
    (hdelta : 8 * (r : ℝ) ^ 2 * Real.sqrt b ≤ δ)
    (hDpos : ∀ i ≤ T, 0 < D i)
    (hRatio : ∀ i < T, (B : ℝ) / (D i : ℝ) ≤ b)
    (hHalf : ∀ i < T, (D i : ℝ) ≤ 2 * (D (i + 1) : ℝ))
    (hThreshold : ∀ i < T,
      (D i : ℝ) * Real.exp (a - (r : ℝ) * a) ≤
        (D (i + 1) : ℝ) + 1)
    (hScale : ∀ i < T,
      (D (i + 1) : ℝ) * Real.exp (-a) ≤
        (D i : ℝ) * Real.exp (-((r : ℝ) * a)))
    (hLower : ∀ i < T,
      (D i : ℝ) * Real.exp (-((r : ℝ) * a)) ≤ D (i + 1)) :
    MatchingSchedule r B T D a δ := by
  have hδ : 0 ≤ δ := by
    have hnonneg : 0 ≤ 8 * (r : ℝ) ^ 2 * Real.sqrt b := by positivity
    linarith
  refine {
    rank_pos := by omega
    rate_nonneg := ha
    error_nonneg := hδ
    degree_pos := hDpos
    small := ?_
    threshold := hThreshold
    scale := hScale
    lower := hLower
    error := ?_
  }
  · intro i hi
    let k : ℝ := (2 * r - 1 : ℕ)
    have hka : 0 ≤ k ^ 2 * a := by positivity
    have hratio' := hRatio i hi
    have hmul := mul_le_mul_of_nonneg_left hratio' hka
    have hident : k ^ 2 * ((B : ℝ) * (a / (D i : ℝ))) =
        (k ^ 2 * a) * ((B : ℝ) / (D i : ℝ)) := by ring
    rw [hident]
    nlinarith [hmul, hsmallBase]
  · intro i hi
    have hround := one_round_error_le_eight hr hB
      (hDpos i hi.le) ha ha1 hb hb1 (hRatio i hi) (hHalf i hi)
    have hscale := mul_le_mul_of_nonneg_right hdelta
      (Nat.cast_nonneg (D (i + 1)) : (0 : ℝ) ≤ D (i + 1))
    exact hround.trans (by nlinarith [hscale])
/-- A floor recurrence supplies both half-degree preservation and the
exponential lower cap once `a D_i ≥ 4`. -/
theorem matchingSchedule_of_floor_bounds
    {r B T : ℕ} {D : ℕ → ℕ} {a δ b : ℝ}
    (hr : 2 ≤ r) (hB : 1 ≤ B)
    (ha : 0 ≤ a) (har : (r : ℝ) * a ≤ 1 / 100)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hsmallBase :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) * a * b ≤ 1)
    (hdelta : 8 * (r : ℝ) ^ 2 * Real.sqrt b ≤ δ)
    (hDpos : ∀ i ≤ T, 0 < D i)
    (hRatio : ∀ i < T, (B : ℝ) / (D i : ℝ) ≤ b)
    (haD : ∀ i < T, 4 ≤ a * (D i : ℝ))
    (hFloor : ∀ i < T,
      Real.exp ((1 - (r : ℝ)) * a) * (D i : ℝ) <
        (D (i + 1) : ℝ) + 1)
    (hScale : ∀ i < T,
      (D (i + 1) : ℝ) * Real.exp (-a) ≤
        (D i : ℝ) * Real.exp (-((r : ℝ) * a))) :
    MatchingSchedule r B T D a δ := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ha1 : a ≤ 1 := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1) ha
    nlinarith [har, h]
  apply matchingSchedule_of_degree_bounds hr hB ha ha1 hb hb1
    hsmallBase hdelta hDpos hRatio
  · intro i hi
    exact (floor_decay_bounds hr ha har (haD i hi) (hFloor i hi)).1
  · intro i hi
    have h := (hFloor i hi).le
    rw [sub_mul, one_mul] at h
    simpa only [mul_comm (Real.exp (a - (r : ℝ) * a)) (D i : ℝ)] using h
  · exact hScale
  · intro i hi
    simpa only [neg_mul] using
      (floor_decay_bounds hr ha har (haD i hi) (hFloor i hi)).2
/-- Iterate favorable marking choices through the full finite horizon. -/
theorem exists_terminal_state
    (H₀ : IndexedHypergraph V E)
    {r B T : ℕ} {D : ℕ → ℕ} {a δ : ℝ}
    (hsched : MatchingSchedule r B T D a δ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B) :
    ∃ s : MatchingState H₀ r B D T,
      s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T ≤
        (initialMatchingState H₀ D hunif hcap hB).potential
          (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T := by
  let s₀ := initialMatchingState H₀ D hunif hcap hB
  have hiterate : ∀ i ≤ T,
      ∃ s : MatchingState H₀ r B D i,
        s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T ≤
          s₀.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T := by
    intro i hi
    induction i with
    | zero =>
        exact ⟨s₀, le_refl _⟩
    | succ i ih =>
        have hiT : i < T := by omega
        obtain ⟨s, hs⟩ := ih (by omega)
        obtain ⟨ω, hstep⟩ :=
          s.exists_next_potential_le T hiT
            hsched.rate_nonneg hsched.error_nonneg hsched.rank_pos
            (hsched.degree_pos i hiT.le)
            (hsched.degree_pos (i + 1) (by omega))
            (hsched.small i hiT) (hsched.threshold i hiT)
            (hsched.scale i hiT) (hsched.lower i hiT)
            (hsched.error i hiT)
        exact ⟨s.next ω, hstep.trans hs⟩
  simpa only [s₀] using hiterate T le_rfl
/-- A valid finite schedule yields a matching whose uncovered vertices are
bounded by the initial backward potential. -/
theorem exists_matching_coverage_bound
    (H₀ : IndexedHypergraph V E)
    {r B T : ℕ} {D : ℕ → ℕ} {a δ : ℝ}
    (hsched : MatchingSchedule r B T D a δ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B) :
    ∃ M : Finset E, H₀.IsMatching M ∧
      (H₀.vertices.card : ℝ) - (H₀.covered M).card ≤
        Theorem2.lossPotentialA (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T 0 *
          (H₀.vertices.card : ℝ) +
        Theorem2.lossPotentialB a T 0 *
          ((H₀.degreeDeficit (D 0) : ℝ) / (D 0 : ℝ)) := by
  obtain ⟨s, hpot⟩ :=
    exists_terminal_state H₀ hsched hunif hcap hB
  have hterminal :
      s.potential (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T =
        (s.residual.vertices.card : ℝ) + (s.wasted : ℝ) := by
    simp [MatchingState.potential,
      Theorem2.lossPotentialA_terminal, Theorem2.lossPotentialB_terminal]
  have hinitial :
      (initialMatchingState H₀ D hunif hcap hB).potential
          (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T =
        Theorem2.lossPotentialA (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T 0 *
          (H₀.vertices.card : ℝ) +
        Theorem2.lossPotentialB a T 0 *
          ((H₀.degreeDeficit (D 0) : ℝ) / (D 0 : ℝ)) := by
    simp [MatchingState.potential, initialMatchingState]
  rw [hterminal, hinitial] at hpot
  have hpart :
      (H₀.covered s.accepted).card + s.residual.vertices.card + s.wasted =
        H₀.vertices.card := s.partition_card
  have hpartReal :
      ((H₀.covered s.accepted).card : ℝ) +
          (s.residual.vertices.card : ℝ) + (s.wasted : ℝ) =
        (H₀.vertices.card : ℝ) := by exact_mod_cast hpart
  exact ⟨s.accepted, s.accepted_matching, by linarith⟩

/-- The nearly-perfect matching conclusion once the explicit initial
potential is at most the requested uncovered-vertex budget. -/
theorem exists_almostPerfectMatching_of_schedule
    (H₀ : IndexedHypergraph V E)
    {r B T : ℕ} {D : ℕ → ℕ} {a δ ξ : ℝ}
    (hsched : MatchingSchedule r B T D a δ)
    (hunif : H₀.IsUniform r)
    (hcap : ∀ v ∈ H₀.vertices, H₀.degree v ≤ D 0)
    (hB : H₀.maxCodegree ≤ B)
    (hbudget :
      Theorem2.lossPotentialA (Real.exp (-a)) δ a ((r : ℝ) * a ^ 2) T 0 *
          (H₀.vertices.card : ℝ) +
        Theorem2.lossPotentialB a T 0 *
          ((H₀.degreeDeficit (D 0) : ℝ) / (D 0 : ℝ)) ≤
        ξ * (H₀.vertices.card : ℝ)) :
    ∃ M : Finset E, H₀.IsMatching M ∧
      (1 - ξ) * (H₀.vertices.card : ℝ) ≤ (H₀.covered M).card := by
  obtain ⟨M, hM, hcover⟩ :=
    exists_matching_coverage_bound H₀ hsched hunif hcap hB
  exact ⟨M, hM, by nlinarith⟩
omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Near-regular minimum degree bounds the initial deficit after
normalizing by the maximum degree. -/
theorem normalized_degreeDeficit_le
    (H : IndexedHypergraph V E) {D : ℕ} (hD : 0 < D)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D)
    {μ : ℝ}
    (hmin : ∀ v ∈ H.vertices,
      (1 - μ) * (D : ℝ) ≤ (H.degree v : ℝ)) :
    (H.degreeDeficit D : ℝ) / (D : ℝ) ≤
      μ * (H.vertices.card : ℝ) := by
  have hsum : (H.degreeDeficit D : ℝ) ≤
      H.vertices.sum (fun _ => μ * (D : ℝ)) := by
    unfold IndexedHypergraph.degreeDeficit
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro v hv
    rw [Nat.cast_sub (hcap v hv)]
    nlinarith [hmin v hv]
  have hsum' : (H.degreeDeficit D : ℝ) ≤
      μ * (H.vertices.card : ℝ) * (D : ℝ) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hsum
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  exact (div_le_iff₀ hDreal).mpr hsum'
/-- A coarse initial-potential budget, separating survivor decay, cumulative
waste/deficit error, and the initial degree shortfall. -/
theorem initial_potential_budget
    (T : ℕ) (N z₀ q δ a β L μ ξ : ℝ)
    (hN : 0 ≤ N) (hμ : 0 ≤ μ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (hqT : q ^ T ≤ ξ / 4)
    (hError : δ * a * (T : ℝ) ^ 2 + β * (T : ℝ) ≤ ξ / 2)
    (hDeficit : z₀ ≤ μ * N)
    (haT : a * (T : ℝ) ≤ 2 * L)
    (hInitial : 2 * L * μ ≤ ξ / 4) :
    Theorem2.lossPotentialA q δ a β T 0 * N +
      Theorem2.lossPotentialB a T 0 * z₀ ≤ ξ * N := by
  have hA := Theorem2.lossPotentialA_zero_le q δ a β
    hq0 hq1 hδ ha hβ T
  have hB := Theorem2.lossPotentialB_zero a T
  have hA' := mul_le_mul_of_nonneg_right hA hN
  have hqT' := mul_le_mul_of_nonneg_right hqT hN
  have hError' := mul_le_mul_of_nonneg_right hError hN
  have haT0 : 0 ≤ a * (T : ℝ) := by positivity
  have hDeficit' := mul_le_mul_of_nonneg_left hDeficit haT0
  have hμN : 0 ≤ μ * N := mul_nonneg hμ hN
  have haT' := mul_le_mul_of_nonneg_right haT hμN
  have hInitial' := mul_le_mul_of_nonneg_right hInitial hN
  rw [hB]
  nlinarith [hA', hqT', hError', hDeficit', haT', hInitial']
end Probability

end MatchingRound
end HadwigerLean

/- Adapted module: HadwigerLean/Quantitative/MatchingConstants.lean. -/
/-
# Numerical parameters for the almost-perfect matching iteration

The paper's logarithmic schedule is kept here, separate from the
combinatorial and probabilistic hypergraph lemmas. Intermediate bounds may
be weakened whenever the final covering error still fits.
-/

namespace HadwigerLean.Theorem2

noncomputable def matchingL (ξ : ℝ) : ℝ := Real.log (4 / ξ)
noncomputable def matchingA (r : ℕ) (ξ : ℝ) : ℝ :=
  ξ / (100 * (r : ℝ) * matchingL ξ)
noncomputable def matchingQ (r : ℕ) (ξ : ℝ) : ℝ :=
  Real.exp (-matchingA r ξ)
noncomputable def matchingT (r : ℕ) (ξ : ℝ) : ℕ :=
  ⌈matchingL ξ / matchingA r ξ⌉₊
noncomputable def matchingMu (r : ℕ) (ξ : ℝ) : ℝ :=
  (ξ / (100 * (r : ℝ))) ^ (20 * r)
noncomputable def matchingB (r : ℕ) (ξ : ℝ) : ℝ :=
  2 * matchingMu r ξ * (4 / ξ) ^ (2 * r)

theorem matchingL_ge_one {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    1 ≤ matchingL ξ := by
  have hfour : (4 : ℝ) ≤ 4 / ξ := by
    apply (le_div_iff₀ hξ).2
    nlinarith
  have harg : 0 < 4 / ξ := div_pos (by norm_num) hξ
  unfold matchingL
  apply (Real.le_log_iff_exp_le harg).2
  exact (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4)).trans hfour

theorem matchingL_le_four_div {ξ : ℝ} (hξ : 0 < ξ) :
    matchingL ξ ≤ 4 / ξ := by
  unfold matchingL
  exact Real.log_le_self (div_nonneg (by norm_num) hξ.le)

theorem matchingA_pos {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    0 < matchingA r ξ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hL : 0 < matchingL ξ := lt_of_lt_of_le zero_lt_one (matchingL_ge_one hξ hξ1)
  unfold matchingA
  positivity

theorem matchingA_mul_r_le {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingA r ξ * (r : ℝ) ≤ 1 / 100 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hL := matchingL_ge_one hξ hξ1
  have hLpos : 0 < matchingL ξ := lt_of_lt_of_le zero_lt_one hL
  have hξL : ξ ≤ matchingL ξ := hξ1.trans hL
  unfold matchingA
  have heq :
      ξ / (100 * (r : ℝ) * matchingL ξ) * (r : ℝ) =
        ξ / (100 * matchingL ξ) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 100 * matchingL ξ)).2
  nlinarith [hξL]

theorem matchingA_le_L {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingA r ξ ≤ matchingL ξ := by
  have ha := matchingA_mul_r_le hr hξ hξ1
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hsmall : matchingA r ξ ≤ matchingA r ξ * (r : ℝ) := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hr1)]
  have hL := matchingL_ge_one hξ hξ1
  linarith

theorem matchingQ_pos {r : ℕ} {ξ : ℝ} :
    0 < matchingQ r ξ := by unfold matchingQ; positivity

theorem matchingQ_le_one {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingQ r ξ ≤ 1 := by
  unfold matchingQ
  have ha := matchingA_pos hr hξ hξ1
  simpa using (Real.exp_le_exp.mpr (show -matchingA r ξ ≤ 0 by linarith))

theorem matchingA_mul_T_bounds {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingL ξ ≤ matchingA r ξ * (matchingT r ξ : ℝ) ∧
      matchingA r ξ * (matchingT r ξ : ℝ) ≤ 2 * matchingL ξ := by
  have ha := matchingA_pos hr hξ hξ1
  have hL := matchingL_ge_one hξ hξ1
  have hquot : 0 ≤ matchingL ξ / matchingA r ξ :=
    div_nonneg (by linarith) ha.le
  have hceil :
      matchingL ξ / matchingA r ξ ≤ (matchingT r ξ : ℝ) := by
    unfold matchingT
    exact Nat.le_ceil _
  have hceilUpper :
      (matchingT r ξ : ℝ) < matchingL ξ / matchingA r ξ + 1 := by
    unfold matchingT
    exact Nat.ceil_lt_add_one hquot
  have hlow := mul_le_mul_of_nonneg_left hceil ha.le
  have hupp := mul_lt_mul_of_pos_left hceilUpper ha
  have hident :
      matchingA r ξ * (matchingL ξ / matchingA r ξ) = matchingL ξ := by
    field_simp
  constructor
  · nlinarith [hlow]
  · have haL := matchingA_le_L hr hξ hξ1
    nlinarith [hupp]

theorem matchingQ_pow_T_le {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingQ r ξ ^ matchingT r ξ ≤ ξ / 4 := by
  have hLT := (matchingA_mul_T_bounds hr hξ hξ1).1
  have hξ4 : 0 < 4 / ξ := div_pos (by norm_num) hξ
  have hqpow :
      matchingQ r ξ ^ matchingT r ξ =
        Real.exp (-(matchingA r ξ * (matchingT r ξ : ℝ))) := by
    unfold matchingQ
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hqpow]
  calc
    Real.exp (-(matchingA r ξ * (matchingT r ξ : ℝ))) ≤
        Real.exp (-matchingL ξ) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = ξ / 4 := by
      unfold matchingL
      rw [Real.exp_neg, Real.exp_log hξ4]
      field_simp


/-- A direct small-base estimate for the paper's codegree error. -/
theorem matchingB_le_base_pow_ten {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ ≤ (ξ / (100 * (r : ℝ))) ^ 10 := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htHalf : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hpair : t * (4 / ξ) ≤ 1 := by
    have heq : t * (4 / ξ) = 4 / (100 * (r : ℝ)) := by
      dsimp [t]
      field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hpairpow : (t * (4 / ξ)) ^ (2 * r) ≤ 1 :=
    pow_le_one₀ (mul_nonneg ht0 (div_nonneg (by norm_num) hξ.le)) hpair
  have hfactor :
      matchingB r ξ = 2 * t ^ (18 * r) * (t * (4 / ξ)) ^ (2 * r) := by
    change 2 * t ^ (20 * r) * (4 / ξ) ^ (2 * r) =
      2 * t ^ (18 * r) * (t * (4 / ξ)) ^ (2 * r)
    have hexp : 20 * r = 18 * r + 2 * r := by omega
    rw [hexp, pow_add, mul_pow]
    ring
  have hpow : t ^ (18 * r) ≤ t ^ 11 :=
    pow_le_pow_of_le_one ht0 (by linarith : t ≤ 1) (by omega : 11 ≤ 18 * r)
  have htwo : 2 * t ≤ 1 := by linarith [htHalf]
  calc
    matchingB r ξ = 2 * t ^ (18 * r) * (t * (4 / ξ)) ^ (2 * r) := hfactor
    _ ≤ 2 * t ^ (18 * r) := by
      nlinarith [mul_le_mul_of_nonneg_left hpairpow (by positivity : 0 ≤ 2 * t ^ (18 * r))]
    _ ≤ 2 * t ^ 11 := by gcongr
    _ = t ^ 10 * (2 * t) := by ring
    _ ≤ t ^ 10 := by
      nlinarith [mul_le_mul_of_nonneg_left htwo (pow_nonneg ht0 10)]
    _ = (ξ / (100 * (r : ℝ))) ^ 10 := rfl

theorem matchingB_sqrt_le {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    Real.sqrt (matchingB r ξ) ≤ ξ ^ 5 / (100000000 * (r : ℝ) ^ 3) := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hB := matchingB_le_base_pow_ten hr hξ hξ1
  have hsqrt : Real.sqrt (matchingB r ξ) ≤ t ^ 5 := by
    have h := Real.sqrt_le_sqrt hB
    have heq : Real.sqrt (t ^ 10) = t ^ 5 := by
      calc
        Real.sqrt (t ^ 10) = Real.sqrt ((t ^ 5) ^ 2) := by congr 1; ring
        _ = |t ^ 5| := Real.sqrt_sq_eq_abs _
        _ = t ^ 5 := abs_of_nonneg (pow_nonneg ht0 _)
    rwa [heq] at h
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by linarith
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr1
  have hden :
      100000000 * (r : ℝ) ^ 3 ≤ (100 * (r : ℝ)) ^ 5 := by
    have hmul := mul_le_mul_of_nonneg_left hr2
      (by positivity : 0 ≤ 10000000000 * (r : ℝ) ^ 3)
    nlinarith [hmul]
  have hdenpos : 0 < 100000000 * (r : ℝ) ^ 3 := by positivity
  calc
    Real.sqrt (matchingB r ξ) ≤ t ^ 5 := hsqrt
    _ = ξ ^ 5 / (100 * (r : ℝ)) ^ 5 := by dsimp [t]; ring
    _ ≤ ξ ^ 5 / (100000000 * (r : ℝ) ^ 3) :=
      div_le_div_of_nonneg_left (pow_nonneg hξ.le _) hdenpos hden

theorem matchingA_ge_quadratic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ξ ^ 2 / (400 * (r : ℝ)) ≤ matchingA r ξ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hLpos : 0 < matchingL ξ :=
    lt_of_lt_of_le zero_lt_one (matchingL_ge_one hξ hξ1)
  have hLbound := matchingL_le_four_div hξ
  have hξL : ξ * matchingL ξ ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hLbound hξ.le
    have heq : ξ * (4 / ξ) = 4 := by field_simp
    rw [heq] at h
    exact h
  have hfactor : ξ / 4 ≤ 1 / matchingL ξ := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hLpos).2
    nlinarith [hξL]
  have hnum : 0 ≤ ξ / (100 * (r : ℝ)) := by positivity
  calc
    ξ ^ 2 / (400 * (r : ℝ)) =
        (ξ / (100 * (r : ℝ))) * (ξ / 4) := by ring
    _ ≤ (ξ / (100 * (r : ℝ))) * (1 / matchingL ξ) :=
      mul_le_mul_of_nonneg_left hfactor hnum
    _ = matchingA r ξ := by unfold matchingA; field_simp

theorem matchingMu_le_quadratic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingMu r ξ ≤ ξ ^ 2 / 800 := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hpow : matchingMu r ξ ≤ t ^ 2 := by
    unfold matchingMu
    exact pow_le_pow_of_le_one ht0 ht1 (by omega : 2 ≤ 20 * r)
  have hden : (800 : ℝ) ≤ (100 * (r : ℝ)) ^ 2 := by
    have hbase : (200 : ℝ) ≤ 100 * (r : ℝ) := by nlinarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 200) hbase 2
    nlinarith [hsq]
  calc
    matchingMu r ξ ≤ t ^ 2 := hpow
    _ = ξ ^ 2 / (100 * (r : ℝ)) ^ 2 := by dsimp [t]; ring
    _ ≤ ξ ^ 2 / 800 :=
      div_le_div_of_nonneg_left (sq_nonneg ξ) (by norm_num) hden

theorem matchingB_le_a_quarter {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ ≤ matchingA r ξ / 4 := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hden : (1600 * (r : ℝ)) ≤ (100 * (r : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (by norm_num : (0 : ℝ) ≤ 10000 * (r : ℝ))]
  have hsmall : t ^ 2 ≤ ξ ^ 2 / (1600 * (r : ℝ)) := by
    calc
      t ^ 2 = ξ ^ 2 / (100 * (r : ℝ)) ^ 2 := by dsimp [t]; ring
      _ ≤ ξ ^ 2 / (1600 * (r : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg ξ)
          (by positivity) hden
  calc
    matchingB r ξ ≤ t ^ 10 := matchingB_le_base_pow_ten hr hξ hξ1
    _ ≤ t ^ 2 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
    _ ≤ ξ ^ 2 / (1600 * (r : ℝ)) := hsmall
    _ = (ξ ^ 2 / (400 * (r : ℝ))) / 4 := by ring
    _ ≤ matchingA r ξ / 4 := by
      gcongr
      exact matchingA_ge_quadratic hr hξ hξ1

/-- Multiplicative degree decay before taking integer floors. -/
noncomputable def matchingLambda (r : ℕ) (ξ : ℝ) : ℝ :=
  matchingQ r ξ ^ (r - 1)

/-- Recursive integer degree caps, exactly as in the paper. -/
noncomputable def matchingD (D₀ r : ℕ) (ξ : ℝ) : ℕ → ℕ
  | 0 => D₀
  | i + 1 => ⌊matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ)⌋₊

theorem matchingLambda_pos (r : ℕ) (ξ : ℝ) :
    0 < matchingLambda r ξ := by
  unfold matchingLambda
  exact pow_pos matchingQ_pos _

theorem matchingLambda_le_one {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingLambda r ξ ≤ 1 := by
  unfold matchingLambda
  exact pow_le_one₀ (matchingQ_pos.le) (matchingQ_le_one hr hξ hξ1)

theorem matchingLambda_eq_exp {r : ℕ} {ξ : ℝ} (hr : 2 ≤ r) :
    matchingLambda r ξ =
      Real.exp ((1 - (r : ℝ)) * matchingA r ξ) := by
  unfold matchingLambda matchingQ
  rw [← Real.exp_nat_mul]
  congr 1
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  rw [hcast]
  ring

theorem matchingLambda_mul_q_eq_exp {r : ℕ} {ξ : ℝ} (hr : 2 ≤ r) :
    matchingLambda r ξ * matchingQ r ξ =
      Real.exp (-(r : ℝ) * matchingA r ξ) := by
  have hsub : r - 1 + 1 = r := Nat.sub_add_cancel (by omega : 1 ≤ r)
  unfold matchingLambda matchingQ
  rw [← pow_succ, hsub, ← Real.exp_nat_mul]
  congr 1
  ring

theorem matchingD_next_le {D₀ r i : ℕ} {ξ : ℝ} :
    (matchingD D₀ r ξ (i + 1) : ℝ) ≤
      matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ) := by
  simp only [matchingD]
  exact Nat.floor_le (mul_nonneg (matchingLambda_pos r ξ).le (Nat.cast_nonneg _))

theorem matchingD_next_lt_add_one {D₀ r i : ℕ} {ξ : ℝ} :
    matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ) <
      (matchingD D₀ r ξ (i + 1) : ℝ) + 1 := by
  simp only [matchingD]
  exact Nat.lt_floor_add_one _

theorem matchingD_next_le_exp {D₀ r i : ℕ} {ξ : ℝ} (hr : 2 ≤ r) :
    (matchingD D₀ r ξ (i + 1) : ℝ) * matchingQ r ξ ≤
      (matchingD D₀ r ξ i : ℝ) *
        Real.exp (-(r : ℝ) * matchingA r ξ) := by
  have hq : 0 < matchingQ r ξ := matchingQ_pos
  calc
    (matchingD D₀ r ξ (i + 1) : ℝ) * matchingQ r ξ ≤
        (matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ)) * matchingQ r ξ :=
      mul_le_mul_of_nonneg_right matchingD_next_le hq.le
    _ = (matchingD D₀ r ξ i : ℝ) *
          (matchingLambda r ξ * matchingQ r ξ) := by ring
    _ = (matchingD D₀ r ξ i : ℝ) *
          Real.exp (-(r : ℝ) * matchingA r ξ) := by
      rw [matchingLambda_mul_q_eq_exp hr]
theorem matchingD_rounding_loss {D₀ r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (i : ℕ) :
    matchingLambda r ξ ^ i * (D₀ : ℝ) ≤
      (matchingD D₀ r ξ i : ℝ) + (i : ℝ) := by
  induction i with
  | zero => simp [matchingD]
  | succ i ih =>
      have hLambda0 := (matchingLambda_pos r ξ).le
      have hLambda1 := matchingLambda_le_one hr hξ hξ1
      have hstep := matchingD_next_lt_add_one (D₀ := D₀) (r := r) (i := i) (ξ := ξ)
      calc
        matchingLambda r ξ ^ (i + 1) * (D₀ : ℝ) =
            matchingLambda r ξ * (matchingLambda r ξ ^ i * (D₀ : ℝ)) := by ring
        _ ≤ matchingLambda r ξ * ((matchingD D₀ r ξ i : ℝ) + (i : ℝ)) :=
          mul_le_mul_of_nonneg_left ih hLambda0
        _ ≤ matchingLambda r ξ * (matchingD D₀ r ξ i : ℝ) + (i : ℝ) := by
          have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right hLambda1 hi0]
        _ ≤ (matchingD D₀ r ξ (i + 1) : ℝ) + ((i + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
theorem matchingT_cubic_bound {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (matchingT r ξ : ℝ) * ξ ^ 3 ≤ 3200 * (r : ℝ) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hT0 : 0 ≤ (matchingT r ξ : ℝ) := Nat.cast_nonneg _
  have hLbound := matchingL_le_four_div hξ
  have hLxi : ξ * matchingL ξ ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hLbound hξ.le
    have heq : ξ * (4 / ξ) = 4 := by field_simp
    rw [heq] at h
    exact h
  have haT := (matchingA_mul_T_bounds hr hξ hξ1).2
  have hTxi : matchingA r ξ * (matchingT r ξ : ℝ) * ξ ≤ 8 := by
    have h := mul_le_mul_of_nonneg_right haT hξ.le
    nlinarith [hLxi]
  have ha2 : ξ ^ 2 ≤ 400 * (r : ℝ) * matchingA r ξ := by
    have h := matchingA_ge_quadratic hr hξ hξ1
    apply (div_le_iff₀ (by positivity : 0 < 400 * (r : ℝ))).1 at h
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right ha2 hT0
  have hmulxi := mul_le_mul_of_nonneg_right hmul hξ.le
  have hbound := mul_le_mul_of_nonneg_left hTxi
    (by positivity : 0 ≤ 400 * (r : ℝ))
  nlinarith [hmulxi, hbound]
theorem matchingB_le_cubic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ ≤ ξ ^ 3 / (10000 * (r : ℝ)) := by
  let t : ℝ := ξ / (100 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))).2
    nlinarith
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by linarith
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr1
  have hpow := mul_le_mul_of_nonneg_left hr2 hrpos.le
  have hden : 10000 * (r : ℝ) ≤ (100 * (r : ℝ)) ^ 3 := by
    nlinarith [hpow]
  calc
    matchingB r ξ ≤ t ^ 10 := matchingB_le_base_pow_ten hr hξ hξ1
    _ ≤ t ^ 3 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
    _ = ξ ^ 3 / (100 * (r : ℝ)) ^ 3 := by dsimp [t]; ring
    _ ≤ ξ ^ 3 / (10000 * (r : ℝ)) :=
      div_le_div_of_nonneg_left (pow_nonneg hξ.le _) (by positivity) hden

theorem matchingB_mul_T_le_one {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingB r ξ * (matchingT r ξ : ℝ) ≤ 1 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hT0 : 0 ≤ (matchingT r ξ : ℝ) := Nat.cast_nonneg _
  have hb := matchingB_le_cubic hr hξ hξ1
  have hbT := mul_le_mul_of_nonneg_right hb hT0
  have hT := matchingT_cubic_bound hr hξ hξ1
  have hscaled := mul_le_mul_of_nonneg_right hbT
    (by positivity : 0 ≤ 10000 * (r : ℝ))
  have heq :
      ξ ^ 3 / (10000 * (r : ℝ)) *
        (matchingT r ξ : ℝ) * (10000 * (r : ℝ)) =
      (matchingT r ξ : ℝ) * ξ ^ 3 := by field_simp
  rw [heq] at hscaled
  by_contra hnot
  have hgt : 1 < matchingB r ξ * (matchingT r ξ : ℝ) := lt_of_not_ge hnot
  have hprod : 0 < (matchingB r ξ * (matchingT r ξ : ℝ) - 1) * (r : ℝ) :=
    mul_pos (by linarith) hrpos
  nlinarith [hscaled, hT, hprod]
theorem matchingLambda_pow_lower {r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hi : i ≤ matchingT r ξ) :
    (ξ / 4) ^ (2 * r) ≤ matchingLambda r ξ ^ i := by
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hL0 : 0 ≤ matchingL ξ :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (matchingL_ge_one hξ hξ1)
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hiReal : (i : ℝ) ≤ (matchingT r ξ : ℝ) := by exact_mod_cast hi
  have hai : matchingA r ξ * (i : ℝ) ≤ 2 * matchingL ξ := by
    have h := mul_le_mul_of_nonneg_left hiReal ha0
    have hT := (matchingA_mul_T_bounds hr hξ hξ1).2
    linarith
  have hri : 0 ≤ (r : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hai hri
  have hexpArg :
      -(2 * (r : ℝ) * matchingL ξ) ≤
        ((1 - (r : ℝ)) * matchingA r ξ) * (i : ℝ) := by
    nlinarith [hmul]
  have hpow :
      matchingLambda r ξ ^ i =
        Real.exp (((1 - (r : ℝ)) * matchingA r ξ) * (i : ℝ)) := by
    rw [matchingLambda_eq_exp hr, ← Real.exp_nat_mul]
    congr 1
    ring
  have hleft :
      Real.exp (-(2 * (r : ℝ) * matchingL ξ)) =
        (ξ / 4) ^ (2 * r) := by
    have hξ4 : 0 < 4 / ξ := div_pos (by norm_num) hξ
    have hbase : Real.exp (-matchingL ξ) = ξ / 4 := by
      unfold matchingL
      rw [Real.exp_neg, Real.exp_log hξ4]
      field_simp
    calc
      Real.exp (-(2 * (r : ℝ) * matchingL ξ)) =
          Real.exp (-matchingL ξ) ^ (2 * r) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
      _ = (ξ / 4) ^ (2 * r) := by rw [hbase]
  rw [← hleft, hpow]
  exact Real.exp_le_exp.mpr hexpArg
theorem matchingB_mul_decay_base {r : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    matchingB r ξ * (ξ / 4) ^ (2 * r) =
      2 * matchingMu r ξ := by
  have hcancel : (4 / ξ) * (ξ / 4) = 1 := by field_simp
  calc
    matchingB r ξ * (ξ / 4) ^ (2 * r) =
        2 * matchingMu r ξ *
          ((4 / ξ) * (ξ / 4)) ^ (2 * r) := by
            unfold matchingB
            rw [mul_pow]
            ring
    _ = 2 * matchingMu r ξ := by rw [hcancel]; simp

theorem matchingB_pos {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) : 0 < matchingB r ξ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  unfold matchingB matchingMu
  positivity

/-- The initial codegree cap absorbs every floor loss in the schedule. -/
theorem matchingD_codegree_invariant {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    (B : ℝ) ≤ matchingB r ξ * (matchingD D₀ r ξ i : ℝ) := by
  have hb0 := (matchingB_pos (r := r) hr hξ).le
  have hiReal : (i : ℝ) ≤ (matchingT r ξ : ℝ) := by exact_mod_cast hi
  have hround := matchingD_rounding_loss (D₀ := D₀) hr hξ hξ1 i
  have hdecay := matchingLambda_pow_lower hr hξ hξ1 hi
  have hD0 : 0 ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hbulk :
      (ξ / 4) ^ (2 * r) * (D₀ : ℝ) ≤
        (matchingD D₀ r ξ i : ℝ) + (i : ℝ) :=
    (mul_le_mul_of_nonneg_right hdecay hD0).trans hround
  have hscaled := mul_le_mul_of_nonneg_left hbulk hb0
  have hscaleeq :
      matchingB r ξ * ((ξ / 4) ^ (2 * r) * (D₀ : ℝ)) =
        2 * matchingMu r ξ * (D₀ : ℝ) := by
    rw [← mul_assoc, matchingB_mul_decay_base hξ]
  rw [hscaleeq] at hscaled
  have hbi : matchingB r ξ * (i : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hiReal hb0).trans
      (matchingB_mul_T_le_one hr hξ hξ1)
  have hBminR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBmin
  nlinarith [hscaled, hbi]

theorem matchingD_positive {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    0 < matchingD D₀ r ξ i := by
  have h := matchingD_codegree_invariant hr hξ hξ1 hBmin hBmax hi
  by_contra hnot
  have hz : matchingD D₀ r ξ i = 0 := by omega
  simp [hz] at h
  have hBminR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBmin
  linarith
theorem matchingD_large {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    4 ≤ matchingA r ξ * (matchingD D₀ r ξ i : ℝ) := by
  have hinv := matchingD_codegree_invariant hr hξ hξ1 hBmin hBmax hi
  have hBminR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBmin
  have hb := matchingB_le_a_quarter hr hξ hξ1
  have hD0 : 0 ≤ (matchingD D₀ r ξ i : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right
    (show 4 * matchingB r ξ ≤ matchingA r ξ by linarith) hD0
  nlinarith [hinv, hmul]

theorem matchingD_codegree_ratio {D₀ B r i : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hi : i ≤ matchingT r ξ) :
    (B : ℝ) / (matchingD D₀ r ξ i : ℝ) ≤ matchingB r ξ := by
  have hinv := matchingD_codegree_invariant hr hξ hξ1 hBmin hBmax hi
  have hDpos : 0 < (matchingD D₀ r ξ i : ℝ) := by
    exact_mod_cast matchingD_positive hr hξ hξ1 hBmin hBmax hi
  exact (div_le_iff₀ hDpos).2 hinv

theorem matching_small {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
      (matchingA r ξ * matchingB r ξ) ≤ 1 := by
  have hNat : 2 * r - 1 ≤ 2 * r := by omega
  have hcast : (((2 * r - 1 : ℕ) : ℝ)) ≤ 2 * (r : ℝ) := by
    exact_mod_cast hNat
  have hsquare :
      (((2 * r - 1 : ℕ) : ℝ) ^ 2) ≤ (2 * (r : ℝ)) ^ 2 := by
    gcongr
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hb0 := (matchingB_pos hr hξ).le
  have hb := matchingB_le_a_quarter hr hξ hξ1
  have har := matchingA_mul_r_le hr hξ hξ1
  have hfirst := mul_le_mul_of_nonneg_right hsquare
    (mul_nonneg ha0 hb0)
  have hsecond := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (sq_nonneg (2 * (r : ℝ))) ha0)
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hsq := pow_le_pow_left₀ (mul_nonneg ha0 hr0) har 2
  calc
    (((2 * r - 1 : ℕ) : ℝ) ^ 2) *
        (matchingA r ξ * matchingB r ξ) ≤
      (2 * (r : ℝ)) ^ 2 * (matchingA r ξ * matchingB r ξ) := hfirst
    _ = ((2 * (r : ℝ)) ^ 2 * matchingA r ξ) * matchingB r ξ := by ring
    _ ≤ ((2 * (r : ℝ)) ^ 2 * matchingA r ξ) *
          (matchingA r ξ / 4) := hsecond
    _ = (matchingA r ξ * (r : ℝ)) ^ 2 := by ring
    _ ≤ (1 / 100 : ℝ) ^ 2 := hsq
    _ ≤ 1 := by norm_num
noncomputable def matchingDelta (r : ℕ) (ξ : ℝ) : ℝ :=
  8 * (r : ℝ) ^ 2 * Real.sqrt (matchingB r ξ)

theorem matchingDelta_nonneg (r : ℕ) (ξ : ℝ) :
    0 ≤ matchingDelta r ξ := by
  unfold matchingDelta
  positivity

theorem matchingDelta_le_quintic {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingDelta r ξ ≤
      ξ ^ 5 / (12500000 * (r : ℝ)) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hsqrt := matchingB_sqrt_le hr hξ hξ1
  have hmul := mul_le_mul_of_nonneg_left hsqrt
    (by positivity : 0 ≤ 8 * (r : ℝ) ^ 2)
  have heq :
      8 * (r : ℝ) ^ 2 *
        (ξ ^ 5 / (100000000 * (r : ℝ) ^ 3)) =
      ξ ^ 5 / (12500000 * (r : ℝ)) := by field_simp; ring
  unfold matchingDelta
  rw [heq] at hmul
  exact hmul
theorem matching_round_error_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingDelta r ξ * matchingA r ξ *
        (matchingT r ξ : ℝ) ^ 2 ≤ ξ / 100 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hδ := matchingDelta_le_quintic hr hξ hξ1
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hT0 : 0 ≤ (matchingT r ξ : ℝ) := Nat.cast_nonneg _
  have hAT : matchingA r ξ * (matchingT r ξ : ℝ) ≤ 8 / ξ := by
    calc
      matchingA r ξ * (matchingT r ξ : ℝ) ≤ 2 * matchingL ξ :=
        (matchingA_mul_T_bounds hr hξ hξ1).2
      _ ≤ 2 * (4 / ξ) := by gcongr; exact matchingL_le_four_div hξ
      _ = 8 / ξ := by ring
  have hT : (matchingT r ξ : ℝ) ≤
      3200 * (r : ℝ) / ξ ^ 3 := by
    exact (le_div_iff₀ (pow_pos hξ 3)).2 (matchingT_cubic_bound hr hξ hξ1)
  calc
    matchingDelta r ξ * matchingA r ξ *
        (matchingT r ξ : ℝ) ^ 2 =
      matchingDelta r ξ *
        (matchingA r ξ * (matchingT r ξ : ℝ)) *
        (matchingT r ξ : ℝ) := by ring
    _ ≤ (ξ ^ 5 / (12500000 * (r : ℝ))) *
        (matchingA r ξ * (matchingT r ξ : ℝ)) *
        (matchingT r ξ : ℝ) := by
          gcongr
    _ ≤ (ξ ^ 5 / (12500000 * (r : ℝ))) *
        (8 / ξ) * (matchingT r ξ : ℝ) := by
          gcongr
    _ ≤ (ξ ^ 5 / (12500000 * (r : ℝ))) *
        (8 / ξ) * (3200 * (r : ℝ) / ξ ^ 3) := by
          gcongr
    _ ≤ ξ / 100 := by
      field_simp
      nlinarith [hξ.le]
theorem matching_quadratic_rate_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (r : ℝ) * matchingA r ξ ^ 2 * (matchingT r ξ : ℝ) ≤
      ξ / 50 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hLpos : 0 < matchingL ξ :=
    lt_of_lt_of_le zero_lt_one (matchingL_ge_one hξ hξ1)
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have hmul := mul_le_mul_of_nonneg_left
    (matchingA_mul_T_bounds hr hξ hξ1).2
    (mul_nonneg hrpos.le ha0)
  have hcancel :
      (r : ℝ) * matchingA r ξ * matchingL ξ = ξ / 100 := by
    unfold matchingA
    field_simp
  nlinarith [hmul]

theorem matching_initial_mu_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    2 * matchingL ξ * matchingMu r ξ ≤ ξ / 4 := by
  have hmu0 : 0 ≤ matchingMu r ξ := by unfold matchingMu; positivity
  have hL0 : 0 ≤ matchingL ξ :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (matchingL_ge_one hξ hξ1)
  calc
    2 * matchingL ξ * matchingMu r ξ ≤
        2 * (4 / ξ) * matchingMu r ξ := by
          gcongr
          exact matchingL_le_four_div hξ
    _ ≤ 2 * (4 / ξ) * (ξ ^ 2 / 800) := by
      gcongr
      exact matchingMu_le_quadratic hr hξ hξ1
    _ = ξ / 100 := by field_simp; ring
    _ ≤ ξ / 4 := by nlinarith
theorem matching_total_error_budget {r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    matchingDelta r ξ * matchingA r ξ *
        (matchingT r ξ : ℝ) ^ 2 +
      ((r : ℝ) * matchingA r ξ ^ 2) *
        (matchingT r ξ : ℝ) ≤ ξ / 2 := by
  have hround := matching_round_error_budget hr hξ hξ1
  have hrate := matching_quadratic_rate_budget hr hξ hξ1
  linarith [hξ]
end HadwigerLean.Theorem2

/- Adapted module: HadwigerLean/Quantitative/MatchingApplication.lean. -/
/-
# The paper's finite matching schedule

The constant estimates are combined here with the checked finite
hypergraph iteration. The sampled hypergraph is supplied separately by
the rounding development.
-/

namespace HadwigerLean.Theorem2

open MatchingRound

/-- The paper's floor schedule satisfies every condition of the finite
matching iteration once the initial maximum codegree is small. -/
theorem matchingSchedule_paper
    {D₀ B r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ)) :
    MatchingRound.MatchingSchedule r B (matchingT r ξ)
      (matchingD D₀ r ξ) (matchingA r ξ) (matchingDelta r ξ) := by
  have ha0 := (matchingA_pos hr hξ hξ1).le
  have har : (r : ℝ) * matchingA r ξ ≤ 1 / 100 := by
    simpa only [mul_comm] using matchingA_mul_r_le hr hξ hξ1
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ha1 : matchingA r ξ ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1) ha0]
  have hb0 := (matchingB_pos hr hξ).le
  have hb1 : matchingB r ξ ≤ 1 := by
    have hb := matchingB_le_a_quarter hr hξ hξ1
    linarith
  apply MatchingRound.matchingSchedule_of_floor_bounds
    hr hBmin ha0 har hb0 hb1
  · simpa only [mul_assoc] using matching_small hr hξ hξ1
  · exact le_refl _
  · intro i hi
    exact matchingD_positive hr hξ hξ1 hBmin hBmax hi
  · intro i hi
    exact matchingD_codegree_ratio hr hξ hξ1 hBmin hBmax hi.le
  · intro i hi
    exact matchingD_large hr hξ hξ1 hBmin hBmax hi.le
  · intro i hi
    have h := matchingD_next_lt_add_one
      (D₀ := D₀) (r := r) (i := i) (ξ := ξ)
    rw [matchingLambda_eq_exp hr] at h
    simpa only [mul_comm] using h
  · intro i hi
    simpa only [matchingQ, neg_mul] using
      (matchingD_next_le_exp (D₀ := D₀) (r := r) (i := i) (ξ := ξ) hr)

/-- The numerical potential budget for the sampled hypergraph. -/
theorem matching_initial_potential_budget
    {V E : Type*} [DecidableEq V]
    (H : IndexedHypergraph V E)
    {D₀ r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hDeficit :
      (H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ) ≤
        matchingMu r ξ * (H.vertices.card : ℝ)) :
    lossPotentialA (Real.exp (-matchingA r ξ))
        (matchingDelta r ξ) (matchingA r ξ)
        ((r : ℝ) * matchingA r ξ ^ 2)
        (matchingT r ξ) 0 * (H.vertices.card : ℝ) +
      lossPotentialB (matchingA r ξ) (matchingT r ξ) 0 *
        ((H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ)) ≤
      ξ * (H.vertices.card : ℝ) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hmu : 0 ≤ matchingMu r ξ := by
    unfold matchingMu
    positivity
  have h := MatchingRound.initial_potential_budget
    (matchingT r ξ) (H.vertices.card : ℝ)
    ((H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ))
    (matchingQ r ξ) (matchingDelta r ξ)
    (matchingA r ξ)
    ((r : ℝ) * matchingA r ξ ^ 2)
    (matchingL ξ) (matchingMu r ξ) ξ
    (Nat.cast_nonneg _) hmu
    (matchingQ_pos.le) (matchingQ_le_one hr hξ hξ1)
    (matchingDelta_nonneg r ξ) (matchingA_pos hr hξ hξ1).le
    (by positivity)
    (matchingQ_pow_T_le hr hξ hξ1)
    (matching_total_error_budget hr hξ hξ1)
    hDeficit
    (matchingA_mul_T_bounds hr hξ hξ1).2
    (matching_initial_mu_budget hr hξ hξ1)
  simpa only [matchingQ] using h

/-- The paper's matching bound for a uniform indexed hypergraph with the
specified initial degree, codegree, and deficit caps. -/
theorem exists_almostPerfectMatching_paper
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (H : IndexedHypergraph V E)
    {D₀ B r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D₀)
    (hB : H.maxCodegree ≤ B)
    (hDeficit :
      (H.degreeDeficit D₀ : ℝ) / (D₀ : ℝ) ≤
        matchingMu r ξ * (H.vertices.card : ℝ)) :
    ∃ M : Finset E, H.IsMatching M ∧
      (1 - ξ) * (H.vertices.card : ℝ) ≤ (H.covered M).card := by
  have hsched :=
    matchingSchedule_paper hr hξ hξ1 hBmin hBmax
  have hpot :=
    matching_initial_potential_budget H hr hξ hξ1 hDeficit
  exact MatchingRound.exists_almostPerfectMatching_of_schedule H
    hsched hunif
    (by simpa only [matchingD] using hcap)
    hB
    (by simpa only [matchingD] using hpot)
/-- A minimum-degree hypothesis supplies the normalized initial deficit
used by the almost-perfect matching theorem. -/
theorem exists_almostPerfectMatching_of_degree_bounds
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (H : IndexedHypergraph V E)
    {D₀ B r : ℕ} {ξ : ℝ}
    (hr : 2 ≤ r) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hD₀ : 0 < D₀)
    (hBmin : 1 ≤ B)
    (hBmax : (B : ℝ) ≤ matchingMu r ξ * (D₀ : ℝ))
    (hunif : H.IsUniform r)
    (hcap : ∀ v ∈ H.vertices, H.degree v ≤ D₀)
    (hmin : ∀ v ∈ H.vertices,
      (1 - matchingMu r ξ) * (D₀ : ℝ) ≤ (H.degree v : ℝ))
    (hB : H.maxCodegree ≤ B) :
    ∃ M : Finset E, H.IsMatching M ∧
      (1 - ξ) * (H.vertices.card : ℝ) ≤ (H.covered M).card := by
  apply exists_almostPerfectMatching_paper H hr hξ hξ1
    hBmin hBmax hunif hcap hB
  exact MatchingRound.normalized_degreeDeficit_le H hD₀ hcap hmin
end HadwigerLean.Theorem2
end

section
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise




/-
# The Erdős–Lovász residual cover bound

Extracted and adapted for Lean 4.33.1 from Varun Sivashankar's ancillary Lean
formalization of *An Improved Lower Bound for the Erdős–Lovász Cover Number
Problem*, arXiv:2606.24878v2. The paper credits ChatGPT 5.5 Pro with helping
discover the proof and Harmonic's Aristotle with helping formalize it.

The original source is distributed under CC BY 4.0.
https://arxiv.org/src/2606.24878v2/anc/lean-proof/RequestProject/Theorem1.lean
https://creativecommons.org/licenses/by/4.0/

This extract proves `ErdosLovasz.keyLemma`. In every intersecting
`r`-uniform hypergraph with `q` edges, the cover number is at most
`(q + r + 4) / 4`.
-/

namespace ErdosLovasz

universe u

variable {V : Type*} [DecidableEq V]
def edgeDeg (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun E => v ∈ E)).card

/- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ E ∈ H, E.card = r

/- `H` is intersecting: every two edges meet. -/
def Intersecting (H : Finset (Finset V)) : Prop :=
  ∀ E ∈ H, ∀ F ∈ H, (E ∩ F).Nonempty

/- `C` is a cover (transversal) of `H`: it meets every edge. -/
def IsCover (H : Finset (Finset V)) (C : Finset V) : Prop :=
  ∀ E ∈ H, ∃ v ∈ C, v ∈ E

/- The set of cardinalities of covers of `H`. -/
def coverCards (H : Finset (Finset V)) : Set ℕ :=
  {n | ∃ C : Finset V, IsCover H C ∧ C.card = n}

/- The cover number `τ(H)`: the minimum size of a cover. -/
noncomputable def coverNum (H : Finset (Finset V)) : ℕ :=
  sInf (coverCards H)

/- Any cover gives an upper bound on the cover number. -/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
omit [DecidableEq V] in
lemma coverNum_le {H : Finset (Finset V)} {C : Finset V} (hC : IsCover H C) :
    coverNum H ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl⟩

/- If every edge of `H` is nonempty, then a cover exists. -/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma coverCards_nonempty {H : Finset (Finset V)} (hne : ∀ E ∈ H, E.Nonempty) :
    (coverCards H).Nonempty := by
  refine ⟨(H.biUnion id).card, H.biUnion id, ?_, rfl⟩
  intro E hE
  obtain ⟨v, hv⟩ := hne E hE
  exact ⟨v, Finset.mem_biUnion.2 ⟨E, hE, hv⟩, hv⟩

/- If every edge of `H` is nonempty, the cover number is attained by some cover. -/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma exists_opt_cover {H : Finset (Finset V)} (hne : ∀ E ∈ H, E.Nonempty) :
    ∃ C : Finset V, IsCover H C ∧ C.card = coverNum H := by
  obtain ⟨C, hC, hn⟩ := Nat.sInf_mem (coverCards_nonempty hne)
  exact ⟨C, hC, hn⟩

/- An intersecting hypergraph has nonempty edges. -/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma Intersecting.edge_nonempty {H : Finset (Finset V)} (hint : Intersecting H)
    {E : Finset V} (hE : E ∈ H) : E.Nonempty := by
  obtain ⟨v, hv⟩ := hint E hE E hE
  exact ⟨v, (Finset.mem_inter.1 hv).1⟩

/- ## Lemma 1 -/

/-
**Lemma 1.** An `r`-uniform intersecting hypergraph of maximum degree `≤ 3`
has at most `2r + 1` edges.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma lemma1 (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 3) :
    J.card ≤ 2 * r + 1 := by
  by_contra! h_contra;
  -- By double counting, we have $\sum_{F \in J} |E \cap F| = \sum_{v \in E} \deg_J(v)$.
  have h_double_count : ∀ E ∈ J, ∑ F ∈ J, (E ∩ F).card = ∑ v ∈ E, edgeDeg J v := by
    intro E hE
    have h_double_count : ∑ F ∈ J, (E ∩ F).card = ∑ v ∈ E, ∑ F ∈ J, if v ∈ F then 1 else 0 := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    simp_all +decide [ edgeDeg ];
  -- Since J is intersecting, for each F ∈ J, (E ∩ F).Nonempty, so 1 ≤ (E ∩ F).card. Therefore
  have h_card_inter : ∀ E ∈ J, ∑ F ∈ J, (E ∩ F).card ≥ (J.card - 1) + r := by
    intro E hE
    have h_card_inter : ∀ F ∈ J, F ≠ E → (E ∩ F).card ≥ 1 := by
      exact fun F hF hne => Finset.card_pos.mpr ( by have := ‹Intersecting J› E hE F hF; aesop );
    rw [ ← Finset.sum_erase_add _ _ hE ];
    exact add_le_add ( le_trans ( by simp +decide [ Finset.card_erase_of_mem hE ] ) ( Finset.sum_le_sum fun x hx => h_card_inter x ( Finset.mem_of_mem_erase hx ) ( Finset.ne_of_mem_erase hx ) ) ) ( by simp +decide [ huni E hE ] );
  rcases J.eq_empty_or_nonempty with ( rfl | ⟨ E, hE ⟩ ) <;> simp_all +decide;
  exact absurd ( h_card_inter E hE ) ( by have := huni E hE; have := Finset.sum_le_sum fun v ( hv : v ∈ E ) => hdeg v; norm_num at *; omega )

/- ## Lemma 2 (link-graph support bound) -/

/-
Geometric fact: a 2-edge `g` meeting two disjoint 2-edges `e`, `f` lies in `e ∪ f`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma edge_in_union {e f g : Finset V} (_he : e.card = 2) (_hf : f.card = 2)
    (hef : Disjoint e f) (hg : g.card = 2)
    (hge : (g ∩ e).Nonempty) (hgf : (g ∩ f).Nonempty) : g ⊆ e ∪ f := by
  obtain ⟨ x, hx ⟩ := hge; obtain ⟨ y, hy ⟩ := hgf; simp_all +decide [ Finset.disjoint_left ] ;
  intro z hz; have := Finset.card_eq_two.mp hg; obtain ⟨ u, v, huv ⟩ := this; aesop;

/-
The support of a graph whose edges are subsets of `U` is contained in `U`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma support_card_le {U : Finset V} {G : Finset (Finset V)}
    (hG : ∀ e ∈ G, e ⊆ U) : (G.biUnion id).card ≤ U.card := by
  exact Finset.card_le_card ( Finset.biUnion_subset.mpr hG )

/-
A pairwise-intersecting family of 2-element edges is a star or a triangle:
either its support has size at most `3`, or all edges share a common vertex.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma star_or_triangle {G : Finset (Finset V)} (hcard : ∀ e ∈ G, e.card = 2)
    (hpi : ∀ e ∈ G, ∀ f ∈ G, (e ∩ f).Nonempty) :
    (G.biUnion id).card ≤ 3 ∨ ∃ c, ∀ e ∈ G, c ∈ e := by
  by_cases h : ∃ c, ∀ e ∈ G, c ∈ e;
  · exact Or.inr h;
  · by_cases hG_empty : G = ∅;
    · aesop;
    · obtain ⟨e0, he0⟩ : ∃ e0 ∈ G, True := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty hG_empty ) fun e he => ⟨ e, he, trivial ⟩
      obtain ⟨a, b, hab⟩ : ∃ a b : V, a ≠ b ∧ e0 = {a, b} := by
        have := Finset.card_eq_two.mp ( hcard e0 he0.1 ) ; tauto;
      obtain ⟨e1, he1, ha⟩ : ∃ e1 ∈ G, a ∉ e1 := by
        exact by push Not at h; exact h a;
      obtain ⟨c, hc⟩ : ∃ c : V, c ≠ a ∧ c ≠ b ∧ e1 = {b, c} := by
        have := hpi e0 he0.1 e1 he1; simp_all +decide [ Finset.Nonempty ] ;
        have := Finset.card_eq_two.mp ( hcard e1 he1 ) ; obtain ⟨ c, d, hcd ⟩ := this; use if c = b then d else c; aesop;
      obtain ⟨e2, he2, hb⟩ : ∃ e2 ∈ G, b ∉ e2 := by
        exact not_forall_not.mp fun contra => h ⟨ b, fun e he => by aesop ⟩
      obtain ⟨ha2, hc2⟩ : a ∈ e2 ∧ c ∈ e2 := by
        obtain ⟨ x, hx ⟩ := hpi _ he0.1 _ he2; obtain ⟨ y, hy ⟩ := hpi _ he1 _ he2; simp_all +decide [ Finset.Nonempty ] ;
        grind
      have he2_eq : e2 = {a, c} := by
        rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ ha2, Finset.singleton_subset_iff.mpr hc2 ⟩ ) ] ; aesop
      have h_support : ∀ e ∈ G, e = {a, b} ∨ e = {b, c} ∨ e = {a, c} := by
        intro e he; specialize hpi e he; simp_all +decide [ Finset.Nonempty ] ;
        have := Finset.card_eq_two.mp ( hcard e he ) ; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
        grind
      have h_support_card : (G.biUnion id).card ≤ 3 := by
        refine' le_trans ( Finset.card_le_card _ ) _;
        exact { a, b, c };
        · intro x hx; obtain ⟨ e, he, hx ⟩ := Finset.mem_biUnion.mp hx; specialize h_support e he; aesop;
        · grind +qlia
      exact Or.inl h_support_card

/-
**Lemma 2, Case A.** The colour class `Ga` contains two vertex-disjoint edges.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma lemma2_caseA (U : Finset V) (Ga Gb Gc : Finset (Finset V))
    (ha : ∀ e ∈ Ga, e.card = 2 ∧ e ⊆ U) (hb : ∀ e ∈ Gb, e.card = 2 ∧ e ⊆ U)
    (hc : ∀ e ∈ Gc, e.card = 2 ∧ e ⊆ U)
    (hdab : Disjoint Ga Gb) (hdac : Disjoint Ga Gc) (hdbc : Disjoint Gb Gc)
    (hcab : ∀ e ∈ Ga, ∀ f ∈ Gb, (e ∩ f).Nonempty)
    (hcac : ∀ e ∈ Ga, ∀ f ∈ Gc, (e ∩ f).Nonempty)
    (hcbc : ∀ e ∈ Gb, ∀ f ∈ Gc, (e ∩ f).Nonempty)
    (e f : Finset V) (he : e ∈ Ga) (hf : f ∈ Ga) (hef : Disjoint e f) :
    (Ga.biUnion id).card + (Gb.biUnion id).card + (Gc.biUnion id).card
      ≤ max 12 (U.card + 4) := by
  -- Let W := e ∪ f; e ∩ f = ∅ and W.card = 4.
  set W := e ∪ f with hW_def
  have hW_card : W.card = 4 := by
    rw [ Finset.card_union_of_disjoint hef, ha e he |>.1, ha f hf |>.1 ];
  -- First establish hW : ∀ g ∈ Gb ∪ Gc, g ⊆ W.
  have hW : ∀ g ∈ Gb ∪ Gc, g ⊆ W := by
    intro g hg; by_cases hg' : g ∈ Gb <;> simp_all +decide [ Finset.disjoint_left ] ;
    · have hW : (g ∩ e).Nonempty ∧ (g ∩ f).Nonempty := by
        exact ⟨ by simpa only [ Finset.inter_comm ] using hcab e he g hg', by simpa only [ Finset.inter_comm ] using hcab f hf g hg' ⟩;
      have := edge_in_union ( ha e he |>.1 ) ( ha f hf |>.1 ) ( Finset.disjoint_left.mpr hef ) ( hb g hg' |>.1 ) hW.1 hW.2; aesop;
    · apply edge_in_union;
      any_goals rw [ Finset.inter_comm ] ; exact hcac _ ‹_› _ ‹_›;
      · exact ha e he |>.1;
      · exact ha f hf |>.1;
      · exact Finset.disjoint_left.mpr hef;
      · exact hc g hg |>.1;
  by_cases h_common : ∃ c, ∀ g ∈ Gb ∪ Gc, c ∈ g;
  · obtain ⟨ c, hc ⟩ := h_common
    have hGbGc_card : (Gb ∪ Gc).card ≤ 2 := by
      -- Choose f' ∈ {e,f} with c ∉ f'.
      obtain ⟨f', hf'⟩ : ∃ f' ∈ [e, f], c ∉ f' := by
        by_cases hc_e : c ∈ e <;> by_cases hc_f : c ∈ f <;> simp_all +decide [ Finset.disjoint_left ];
      -- Every g ∈ Gb ∪ Gc satisfies c ∈ g, g ⊆ W, and (g ∩ f').Nonempty (g meets the Ga-edge f' by the relevant cross hypothesis + inter_comm); with g.card = 2 and c ∉ f', g = {c, y}, y ∈ f'.
      have hGbGc_subset : ∀ g ∈ Gb ∪ Gc, ∃ y ∈ f', g = {c, y} := by
        intro g hg
        have hg_subset : g ⊆ W := hW g hg
        have hg_card : g.card = 2 := by
          grind
        have hg_inter : (g ∩ f').Nonempty := by
          by_cases hgGb : g ∈ Gb <;> by_cases hgGc : g ∈ Gc <;> simp_all +decide [ Finset.disjoint_left ];
          · exact hcab _ ( hf'.1.elim ( fun h => h.symm ▸ he ) fun h => h.symm ▸ hf ) _ hgGb |> fun ⟨ x, hx ⟩ => ⟨ x, by aesop ⟩;
          · exact hcac _ ( hf'.1.elim ( fun h => h.symm ▸ he ) fun h => h.symm ▸ hf ) _ hgGc |> fun ⟨ x, hx ⟩ => ⟨ x, by aesop ⟩
        have hg_form : ∃ y ∈ f', g = {c, y} := by
          obtain ⟨ y, hy ⟩ := hg_inter;
          use y;
          rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hc g hg, Finset.singleton_subset_iff.mpr ( Finset.mem_of_mem_inter_left hy ) ⟩ ) ] ; aesop;
          grind
        exact hg_form;
      have hGbGc_subset : Gb ∪ Gc ⊆ Finset.image (fun y => {c, y}) f' := by
        intro g hg; obtain ⟨ y, hy, rfl ⟩ := hGbGc_subset g hg; exact Finset.mem_image_of_mem _ hy;
      exact le_trans ( Finset.card_le_card hGbGc_subset ) ( Finset.card_image_le.trans ( by aesop ) );
    have hGbGc_card : (Gb.biUnion id).card ≤ 2 * Gb.card ∧ (Gc.biUnion id).card ≤ 2 * Gc.card := by
      exact ⟨ le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum fun x hx => hb x hx |>.1.le ), le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum fun x hx => ‹∀ e ∈ Gc, e.card = 2 ∧ e ⊆ U› x hx |>.1.le ) ⟩;
    have hGa_card : (Ga.biUnion id).card ≤ U.card := by
      exact Finset.card_le_card ( Finset.biUnion_subset.mpr fun x hx => ha x hx |>.2 );
    simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
    grind;
  · -- Prove ∀ h ∈ Ga, h ⊆ W.
    have hGa_subset_W : ∀ h ∈ Ga, h ⊆ W := by
      intro h hh
      have h_meet : ∀ g ∈ Gb ∪ Gc, (h ∩ g).Nonempty := by
        grind;
      -- If ∃ p q ∈ Gb ∪ Gc with Disjoint p q, then p,q ⊆ W (hW) disjoint card-2, h meets both, edge_in_union gives h ⊆ p ∪ q ⊆ W.
      by_cases h_disjoint : ∃ p q, p ∈ Gb ∪ Gc ∧ q ∈ Gb ∪ Gc ∧ Disjoint p q;
      · obtain ⟨ p, q, hp, hq, hpq ⟩ := h_disjoint;
        have h_subset : h ⊆ p ∪ q := by
          apply edge_in_union;
          any_goals solve_by_elim;
          · grind;
          · grind;
          · exact ha h hh |>.1;
        exact h_subset.trans ( Finset.union_subset ( hW p hp ) ( hW q hq ) );
      · -- Apply star_or_triangle to Gb ∪ Gc; the common-vertex disjunct is excluded by hypothesis, so its support T := (Gb∪Gc).biUnion id has T.card ≤ 3 and (by hW) T ⊆ W.
        obtain ⟨T, hT⟩ : ∃ T : Finset V, T = (Gb ∪ Gc).biUnion id ∧ T.card ≤ 3 ∧ T ⊆ W := by
          have := star_or_triangle ( show ∀ e ∈ Gb ∪ Gc, e.card = 2 from ?_ ) ( show ∀ e ∈ Gb ∪ Gc, ∀ f ∈ Gb ∪ Gc, ( e ∩ f ).Nonempty from ?_ );
          · exact ⟨ _, rfl, this.resolve_right h_common, Finset.biUnion_subset.mpr fun x hx => hW x hx ⟩;
          · grind;
          · simp_all +decide [ Finset.disjoint_left ];
            exact fun e he f hf => by obtain ⟨ x, hx₁, hx₂ ⟩ := h_disjoint e he f hf; exact ⟨ x, Finset.mem_inter_of_mem hx₁ hx₂ ⟩ ;
        -- If h had a vertex outside T, h's other vertex would lie in every edge of Gb∪Gc (to meet each), i.e. be a common vertex — contradiction; so both vertices of h are in T, giving h ⊆ T ⊆ W.
        by_contra h_contra
        obtain ⟨v, hv⟩ : ∃ v ∈ h, v ∉ T := by
          exact Finset.not_subset.mp fun h' => h_contra <| h'.trans hT.2.2;
        obtain ⟨w, hw⟩ : ∃ w ∈ h, w ≠ v := by
          exact Finset.exists_mem_ne ( by linarith [ ha h hh ] ) v;
        have h_w_in_T : ∀ g ∈ Gb ∪ Gc, w ∈ g := by
          intro g hg; specialize h_meet g hg; simp_all +decide [ Finset.Nonempty ] ;
          obtain ⟨ x, hx₁, hx₂ ⟩ := h_meet; have := Finset.card_eq_two.mp ( ha _ hh |>.1 ) ; obtain ⟨ y, z, hy, hz, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
          grind +revert;
        exact h_common ⟨ w, h_w_in_T ⟩;
    -- Then Va, Vb, Vc ⊆ W (Va by this, Vb,Vc by hW), each card ≤ 4, total ≤ 12 (le_max_left).
    have hVa_subset_W : (Ga.biUnion id) ⊆ W := by
      exact Finset.biUnion_subset.mpr hGa_subset_W
    have hVb_subset_W : (Gb.biUnion id) ⊆ W := by
      exact Finset.biUnion_subset.mpr fun g hg => hW g ( Finset.mem_union_left _ hg )
    have hVc_subset_W : (Gc.biUnion id) ⊆ W := by
      exact Finset.biUnion_subset.mpr fun g hg => hW g ( Finset.mem_union_right _ hg );
    exact le_trans ( add_le_add_three ( Finset.card_le_card hVa_subset_W ) ( Finset.card_le_card hVb_subset_W ) ( Finset.card_le_card hVc_subset_W ) ) ( by simp +decide [ hW_card ] )

/-
**Lemma 2, Case B.** Every colour class is pairwise intersecting.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma lemma2_caseB (U : Finset V) (G1 G2 G3 : Finset (Finset V))
    (h1 : ∀ e ∈ G1, e.card = 2 ∧ e ⊆ U) (h2 : ∀ e ∈ G2, e.card = 2 ∧ e ⊆ U)
    (h3 : ∀ e ∈ G3, e.card = 2 ∧ e ⊆ U)
    (hd12 : Disjoint G1 G2) (hd13 : Disjoint G1 G3) (hd23 : Disjoint G2 G3)
    (hc12 : ∀ e ∈ G1, ∀ f ∈ G2, (e ∩ f).Nonempty)
    (hc13 : ∀ e ∈ G1, ∀ f ∈ G3, (e ∩ f).Nonempty)
    (hc23 : ∀ e ∈ G2, ∀ f ∈ G3, (e ∩ f).Nonempty)
    (hpi1 : ∀ e ∈ G1, ∀ f ∈ G1, (e ∩ f).Nonempty)
    (hpi2 : ∀ e ∈ G2, ∀ f ∈ G2, (e ∩ f).Nonempty)
    (hpi3 : ∀ e ∈ G3, ∀ f ∈ G3, (e ∩ f).Nonempty) :
    (G1.biUnion id).card + (G2.biUnion id).card + (G3.biUnion id).card
      ≤ max 12 (U.card + 4) := by
  by_cases h : ( G1.biUnion id ).card ≤ 4 ∧ ( G2.biUnion id ).card ≤ 4 ∧ ( G3.biUnion id ).card ≤ 4 <;> simp_all +decide;
  · grind;
  · -- By the symmetry of the hypotheses you may treat the three possibilities the same way; describe it for the class whose support is ≥ 5, call it Ga (one of G1,G2,G3), with the other two Gb, Gc.
    suffices h_symm : ∀ (Ga Gb Gc : Finset (Finset V)),
      (∀ e ∈ Ga, e.card = 2 ∧ e ⊆ U) →
      (∀ e ∈ Gb, e.card = 2 ∧ e ⊆ U) →
      (∀ e ∈ Gc, e.card = 2 ∧ e ⊆ U) →
      Disjoint Ga Gb →
      Disjoint Ga Gc →
      Disjoint Gb Gc →
      (∀ e ∈ Ga, ∀ f ∈ Gb, (e ∩ f).Nonempty) →
      (∀ e ∈ Ga, ∀ f ∈ Gc, (e ∩ f).Nonempty) →
      (∀ e ∈ Gb, ∀ f ∈ Gc, (e ∩ f).Nonempty) →
      (∀ e ∈ Ga, ∀ f ∈ Ga, (e ∩ f).Nonempty) →
      (∀ e ∈ Gb, ∀ f ∈ Gb, (e ∩ f).Nonempty) →
      (∀ e ∈ Gc, ∀ f ∈ Gc, (e ∩ f).Nonempty) →
      (Ga.biUnion id).card ≥ 5 →
      (Ga.biUnion id).card + (Gb.biUnion id).card + (Gc.biUnion id).card ≤ U.card + 4 by
        by_cases h1 : (G1.biUnion id).card ≥ 5;
        · exact Or.inr ( h_symm G1 G2 G3 ‹_› ‹_› ‹_› hd12 hd13 hd23 hc12 hc13 hc23 hpi1 hpi2 hpi3 h1 );
        · by_cases h2 : (G2.biUnion id).card ≥ 5;
          · specialize h_symm G2 G1 G3 ; simp_all +decide [ add_comm, add_left_comm ];
            exact Or.inr ( h_symm ( Finset.disjoint_left.mpr fun x hx1 hx2 => Finset.disjoint_left.mp hd12 hx2 hx1 ) fun e he f hf => by simpa only [ Finset.inter_comm ] using hc12 f hf e he );
          · specialize h_symm G3 G1 G2 ; simp_all +decide [ add_comm, add_left_comm ];
            exact Or.inr ( h_symm ( Finset.disjoint_left.mpr fun x hx1 hx2 => Finset.disjoint_left.mp hd13 hx2 hx1 ) ( Finset.disjoint_left.mpr fun x hx1 hx2 => Finset.disjoint_left.mp hd23 hx2 hx1 ) ( fun e he f hf => by simpa only [ Finset.inter_comm ] using hc13 f hf e he ) ( fun e he f hf => by simpa only [ Finset.inter_comm ] using hc23 f hf e he ) ( by linarith [ h ( by linarith ) ( by linarith ) ] ) );
    intros Ga Gb Gc ha hb hc hdab hdac hdbc hcab hcac hcbc hpiGa hpiGb hpiGc hGa_card
    obtain ⟨c, hcGa⟩ : ∃ c, ∀ e ∈ Ga, c ∈ e := by
      have := star_or_triangle ( fun e he => ha e he |>.1 ) hpiGa;
      exact this.resolve_left ( by linarith )
    have hcU : c ∈ U := by
      exact ha _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) |>.2 ( hcGa _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) )
    have hcGb : ∀ g ∈ Gb, c ∈ g := by
      intro g hg
      by_contra hcGb_contra
      have h_leaves : (Ga.biUnion id \ {c}).card ≥ 4 := by
        grind;
      have h_leaves_subset : ∀ x ∈ Ga.biUnion id \ {c}, x ∈ g := by
        simp_all +decide [ Finset.Nonempty ];
        intro x e he hx hx'; specialize hcab e he g hg; obtain ⟨ y, hy, hy' ⟩ := hcab; have := ha e he; have := hb g hg; simp_all +decide [ Finset.card_eq_two ] ;
        grind;
      exact absurd ( Finset.card_le_card h_leaves_subset ) ( by linarith [ hb g hg ] )
    have hcGc : ∀ g ∈ Gc, c ∈ g := by
      intro g hg
      by_contra hgc
      have h_leaves : (Ga.biUnion id \ {c}).card ≥ 4 := by
        grind;
      have h_leaves_subset : (Ga.biUnion id \ {c}) ⊆ g := by
        intro x hx; simp_all +decide ;
        obtain ⟨ ⟨ e, he, hx ⟩, hx' ⟩ := hx;
        obtain ⟨ y, hy ⟩ := hcac e he g hg;
        have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hx ( Finset.singleton_subset_iff.mpr ( hcGa e he ) ) ) ; simp_all +decide ;
        grind;
      exact absurd ( Finset.card_le_card h_leaves_subset ) ( by linarith [ hc g hg ] );
    have h_inter : ∀ x ≠ c, (x ∈ (Ga.biUnion id) ∧ x ∈ (Gb.biUnion id)) ∨ (x ∈ (Ga.biUnion id) ∧ x ∈ (Gc.biUnion id)) ∨ (x ∈ (Gb.biUnion id) ∧ x ∈ (Gc.biUnion id)) → False := by
      simp_all +decide [ Finset.disjoint_left ];
      refine' fun x hx => ⟨ _, _, _ ⟩;
      · intro e he hx f hf; have := ha e he; have := hb f hf; simp_all +decide [ Finset.card_eq_two ] ;
        grind;
      · intro e he hx f hf hxf; have := ha e he; have := hc f hf; simp_all +decide [ Finset.card_eq_two ] ;
        grind;
      · intro e he hx f hf hx'; have := hb e he; have := hc f hf; simp_all +decide [ Finset.subset_iff ] ;
        have := Finset.eq_of_subset_of_card_le ( show { x, c } ⊆ e from Finset.insert_subset_iff.mpr ⟨ hx, Finset.singleton_subset_iff.mpr ( hcGb e he ) ⟩ ) ; have := Finset.eq_of_subset_of_card_le ( show { x, c } ⊆ f from Finset.insert_subset_iff.mpr ⟨ hx', Finset.singleton_subset_iff.mpr ( hcGc f hf ) ⟩ ) ; simp_all +decide ;
    have h_inter_card : (Ga.biUnion id ∩ Gb.biUnion id).card ≤ 1 ∧ (Ga.biUnion id ∩ Gc.biUnion id).card ≤ 1 ∧ (Gb.biUnion id ∩ Gc.biUnion id).card ≤ 1 := by
      refine' ⟨ Finset.card_le_one.mpr _, Finset.card_le_one.mpr _, Finset.card_le_one.mpr _ ⟩;
      · grind;
      · grind +splitIndPred;
      · grind;
    have h_union_card : (Ga.biUnion id ∪ Gb.biUnion id ∪ Gc.biUnion id).card ≤ U.card := by
      exact Finset.card_le_card ( Finset.union_subset ( Finset.union_subset ( Finset.biUnion_subset.mpr fun e he => ha e he |>.2 ) ( Finset.biUnion_subset.mpr fun e he => hb e he |>.2 ) ) ( Finset.biUnion_subset.mpr fun e he => hc e he |>.2 ) );
    have := Finset.card_union_add_card_inter ( Ga.biUnion id ) ( Gb.biUnion id ) ; simp_all +decide ;
    have := Finset.card_union_add_card_inter ( Ga.biUnion id ∪ Gb.biUnion id ) ( Gc.biUnion id ) ; simp_all +decide ;
    rw [ Finset.union_inter_distrib_right ] at this;
    linarith [ show Finset.card ( Ga.biUnion id ∩ Gc.biUnion id ∪ Gb.biUnion id ∩ Gc.biUnion id ) ≤ 2 by exact le_trans ( Finset.card_union_le _ _ ) ( by linarith ) ]

/-
**Lemma 2.** Let `G1, G2, G3` be the three colour classes of a simple graph on
the vertex set `U`, with edges being `2`-element subsets of `U`.  Assume the three
classes are pairwise edge-disjoint and that no two vertex-disjoint edges have
different colours (cross-intersecting condition).  Then the total size of the
three colour supports is at most `max 12 (|U| + 4)`.

The proof is split into helper lemmas `edge_in_union`, `support_card_le`,
`star_or_triangle`, and the two cases `lemma2_caseA` and `lemma2_caseB`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma lemma2 (U : Finset V) (G1 G2 G3 : Finset (Finset V))
    (h1 : ∀ e ∈ G1, e.card = 2 ∧ e ⊆ U) (h2 : ∀ e ∈ G2, e.card = 2 ∧ e ⊆ U)
    (h3 : ∀ e ∈ G3, e.card = 2 ∧ e ⊆ U)
    (hd12 : Disjoint G1 G2) (hd13 : Disjoint G1 G3) (hd23 : Disjoint G2 G3)
    (hc12 : ∀ e ∈ G1, ∀ f ∈ G2, (e ∩ f).Nonempty)
    (hc13 : ∀ e ∈ G1, ∀ f ∈ G3, (e ∩ f).Nonempty)
    (hc23 : ∀ e ∈ G2, ∀ f ∈ G3, (e ∩ f).Nonempty) :
    (G1.biUnion id).card + (G2.biUnion id).card + (G3.biUnion id).card
      ≤ max 12 (U.card + 4) := by
  by_cases h_caseA : ∃ e ∈ G1, ∃ f ∈ G1, Disjoint e f;
  · obtain ⟨ e, he, f, hf, hef ⟩ := h_caseA; exact lemma2_caseA U G1 G2 G3 h1 h2 h3 hd12 hd13 hd23 hc12 hc13 hc23 e f he hf hef;
  · by_cases h_caseB : ∃ e ∈ G2, ∃ f ∈ G2, Disjoint e f;
    · convert lemma2_caseA U G2 G1 G3 _ _ _ _ _ _ _ _ using 1;
      any_goals tauto;
      · grind;
      · exact fun e he f hf => by simpa only [ Finset.inter_comm ] using hc12 f hf e he;
    · by_cases h_caseC : ∃ e ∈ G3, ∃ f ∈ G3, Disjoint e f;
      · have := lemma2_caseA U G3 G1 G2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_;
        any_goals tauto;
        · grind;
        · exact fun e he f hf => by simpa only [ Finset.inter_comm ] using hc13 f hf e he;
        · exact fun e he f hf => by simpa only [ Finset.inter_comm ] using hc23 f hf e he;
      · apply lemma2_caseB U G1 G2 G3 h1 h2 h3 hd12 hd13 hd23 hc12 hc13 hc23;
        · exact fun e he f hf => Finset.not_disjoint_iff_nonempty_inter.mp fun h => h_caseA ⟨ e, he, f, hf, h ⟩;
        · exact fun e he f hf => Finset.not_disjoint_iff_nonempty_inter.mp fun h => h_caseB ⟨ e, he, f, hf, h ⟩;
        · exact fun e he f hf => Finset.not_disjoint_iff_nonempty_inter.mp fun h => h_caseC ⟨ e, he, f, hf, h ⟩

/- ## Lemma 3 (arithmetic) -/

/-
**Lemma 3.** A purely arithmetic inequality used to bound the cover number.
Here `K = max 12 (u + 4)` and `d` is allowed to be negative.  The hypothesis
`h2` is the integer form of `d ≤ 1 + (K - u) t / (2u)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma lemma3 (u : ℕ) (_hu : 1 ≤ u) (t : ℕ) (d : ℤ) (K : ℤ)
    (hK : K = max 12 ((u : ℤ) + 4))
    (h1 : (t : ℤ) ≤ (u : ℤ) - 2 * d + 1)
    (h2 : 2 * (u : ℤ) * (d - 1) ≤ (K - u) * t) :
    d + 4 * (((u + 1) / 2 : ℕ) : ℤ) - 2 * (u : ℤ) ≤ 4 := by
  norm_num [ Nat.cast_div ] at *;
  cases max_cases ( 12 : ℤ ) ( u + 4 ) <;> nlinarith [ Int.mul_ediv_add_emod ( u + 1 ) 2, Int.emod_nonneg ( u + 1 ) two_ne_zero, Int.emod_lt_of_pos ( u + 1 ) two_pos ]

/- ## Lemma 4 (residual cover bound)

We form the auxiliary `3`-uniform system `T` on the points `E(J)` whose edges are
the size-`3` blocks `B_v = {A ∈ E(J) : v ∈ A}`, take a maximum matching `M`, and
count around the unmatched points.  The deep counting step is `eq4_nat`. -/

/- The block of a vertex `v`: the edges of `J` (as points) that contain `v`. -/
def block (J : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  J.filter (fun A => v ∈ A)

/- A *good triple* is a `3`-element set of edges sharing a common vertex; i.e. a
size-`3` block. -/
def IsGoodTriple (J : Finset (Finset V)) (S : Finset (Finset V)) : Prop :=
  S.card = 3 ∧ ∃ v, S = block J v

/- A *matching* in the auxiliary triple system: pairwise-disjoint good triples. -/
def IsMatching (J : Finset (Finset V)) (M : Finset (Finset (Finset V))) : Prop :=
  (∀ S ∈ M, IsGoodTriple J S) ∧ ∀ S ∈ M, ∀ T ∈ M, S ≠ T → Disjoint S T

/-
A maximum matching exists.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma exists_max_matching (J : Finset (Finset V)) :
    ∃ M : Finset (Finset (Finset V)), IsMatching J M ∧
      ∀ M', IsMatching J M' → M'.card ≤ M.card := by
  apply Classical.byContradiction
  intro h_no_max;
  -- Let's denote the set of all matchings by `𝓜`.
  set M_set := {M : Finset (Finset (Finset V)) | IsMatching J M};
  -- Since $M_set$ is nonempty and finite, it must have a maximum element.
  have h_max : ∃ M ∈ M_set, ∀ M' ∈ M_set, M'.card ≤ M.card := by
    apply_rules [ Set.exists_max_image ];
    · exact Set.finite_iff_bddAbove.mpr ⟨ Finset.powerset J, fun M hM => fun S hS => Finset.mem_powerset.mpr <| hM.1 S hS |> fun h => h.2.choose_spec ▸ Finset.filter_subset _ _ ⟩;
    · exact ⟨ ∅, by unfold M_set IsMatching; simp +decide ⟩;
  exact h_no_max ⟨ h_max.choose, h_max.choose_spec.1, fun M' hM' => h_max.choose_spec.2 M' hM' ⟩

/-
Maximality forbids a good triple inside the unmatched set `U = E(J) \ ⋃ M`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma no_good_triple_in_U (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    {S : Finset (Finset V)} (hS : IsGoodTriple J S) (hSU : S ⊆ J \ M.biUnion id) :
    False := by
  contrapose! hMmax;
  refine' ⟨ Insert.insert S M, _, _ ⟩ <;> simp_all +decide [ IsMatching ];
  · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
    grind;
  · rw [ Finset.card_insert_of_notMem ];
    · exact Nat.lt_succ_self _;
    · intro hSM; have := hSU ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hS.1 ] ) ) ) ; simp_all +decide [ Finset.subset_iff ] ;
      exact this.2 _ hSM ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hS.1 ] ) ) )

/-
The number of edges splits as `q = 3t + u` (`t = |M|`, `u = |U|`).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma matching_q (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) :
    J.card = 3 * M.card + (J \ M.biUnion id).card := by
  rw [ show J.card = ( M.biUnion id ).card + ( J \ M.biUnion id ).card from ?_, show 3 * M.card = ( M.biUnion id ).card from ?_ ];
  · rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_const_nat ];
      rw [ mul_comm ];
      exact fun x hx => hM.1 x hx |>.1;
    · exact fun x hx y hy hxy => hM.2 x hx y hy hxy;
  · rw [ ← Finset.card_union_of_disjoint, Finset.union_sdiff_of_subset ];
    · intro x hx
      obtain ⟨S, hS⟩ := Finset.mem_biUnion.mp hx
      have hS_block : S = block J (Classical.choose (hM.1 S hS.1).2) := by
        exact Classical.choose_spec ( hM.1 S hS.1 |>.2 );
      exact Finset.mem_filter.mp ( hS_block ▸ hS.2 ) |>.1;
    · exact Finset.disjoint_sdiff

/-
An intersecting family can be covered by `⌈n/2⌉` vertices (pair up edges; each
pair shares a vertex).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma intersecting_cover_half (F : Finset (Finset V))
    (hF : ∀ x ∈ F, ∀ y ∈ F, (x ∩ y).Nonempty) :
    ∃ C : Finset V, (∀ E ∈ F, ∃ v ∈ C, v ∈ E) ∧ C.card ≤ (F.card + 1) / 2 := by
  induction' hn : F.card using Nat.strong_induction_on with n ih generalizing F;
  by_cases h_empty : F = ∅;
  · exact ⟨ ∅, by simp +decide [ h_empty ] ⟩;
  · by_cases h_card : F.card ≤ 1;
    · obtain ⟨ E, hE ⟩ := Finset.card_pos.mp ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h_empty ) );
      obtain ⟨ v, hv ⟩ := hF E hE E hE;
      use {v}; simp;
      rw [ Finset.card_le_one_iff_subset_singleton ] at h_card ; aesop;
    · obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : Finset V, x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ (x ∩ y).Nonempty := by
        obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ( lt_of_not_ge h_card ) ; exact ⟨ x, y, hx, hy, hxy, hF x hx y hy ⟩ ;
      obtain ⟨ v, hv ⟩ := hxy.2;
      obtain ⟨ C, hC₁, hC₂ ⟩ := ih ( F.card - 2 ) ( by omega ) ( F \ { x, y } ) ( fun E hE F hF => hF |> fun hF => by aesop ) ( by rw [ Finset.card_sdiff ] ; aesop );
      refine' ⟨ Insert.insert v C, _, _ ⟩ <;> simp_all +decide;
      · intro E hE; by_cases hE' : E = x <;> by_cases hE'' : E = y <;> simp_all +decide ;
      · exact le_trans ( Finset.card_insert_le _ _ ) ( by omega )

/-
Cover bound from a matching: `τ(J) ≤ t + ⌈u/2⌉`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma matching_cover (J : Finset (Finset V)) (hint : Intersecting J)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M) :
    coverNum J ≤ M.card + ((J \ M.biUnion id).card + 1) / 2 := by
  -- Construct a cover of $J$ of size at most $M.card + ((J \ M.biUnion id).card + 1) / 2$.
  obtain ⟨C, hC⟩ : ∃ C : Finset V, (∀ E ∈ J, ∃ v ∈ C, v ∈ E) ∧ C.card ≤ M.card + ((J \ M.biUnion id).card + 1) / 2 := by
    -- Let $C_c$ be the set of vertices in the matched part.
    obtain ⟨Cc, hCc⟩ : ∃Cc : Finset V, (∀ E ∈ M.biUnion id, ∃ v ∈ Cc, v ∈ E) ∧ Cc.card ≤ M.card := by
      have hCc : ∀ S ∈ M, ∃ v, v ∈ S.biUnion id ∧ S = block J v := by
        intro S hS
        obtain ⟨v, hv⟩ := hM.left S hS |>.2
        use v
        simp [hv];
        have := hM.1 S hS; simp_all +decide [ IsGoodTriple ] ;
        exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hx, by unfold block at hx; aesop ⟩;
      choose! v hv hv' using hCc;
      refine' ⟨ Finset.image ( fun S : M => v S S.2 ) Finset.univ, _, _ ⟩;
      · simp +decide [ Finset.mem_biUnion ];
        grind +locals;
      · exact Finset.card_image_le.trans ( by simp +decide );
    -- Let $C_u$ be the set of vertices in the unmatched part.
    obtain ⟨Cu, hCu⟩ : ∃ Cu : Finset V, (∀ E ∈ J \ M.biUnion id, ∃ v ∈ Cu, v ∈ E) ∧ Cu.card ≤ ((J \ M.biUnion id).card + 1) / 2 := by
      apply intersecting_cover_half;
      exact fun x hx y hy => ‹∀ E ∈ J, ∀ F ∈ J, ( E ∩ F ).Nonempty› x ( Finset.mem_sdiff.mp hx |>.1 ) y ( Finset.mem_sdiff.mp hy |>.1 );
    use Cc ∪ Cu;
    exact ⟨ fun E hE => if hE' : E ∈ M.biUnion id then by obtain ⟨ v, hv₁, hv₂ ⟩ := hCc.1 E hE'; exact ⟨ v, Finset.mem_union_left _ hv₁, hv₂ ⟩ else by obtain ⟨ v, hv₁, hv₂ ⟩ := hCu.1 E ( Finset.mem_sdiff.mpr ⟨ hE, hE' ⟩ ) ; exact ⟨ v, Finset.mem_union_right _ hv₁, hv₂ ⟩, le_trans ( Finset.card_union_le _ _ ) ( add_le_add hCc.2 hCu.2 ) ⟩;
  exact le_trans ( coverNum_le hC.1 ) hC.2

/- ### Machinery for equation (4)

We abbreviate `C = ⋃ M` (matched points), `U = E(J) \ C` (unmatched points),
`t = |M|`, `u = |U|`.  `selVerts` are the chosen witnesses for `2`-subsets of `U`,
`coveredUC` the set of `U`–`C` pairs covered by a selected witness, and
`linkGraph p` the colour class of `p` in a matched triple. -/

/- The witness vertices chosen for the `2`-element subsets of `U` (via `ω`). -/
def selVerts (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) : Finset V :=
  ((J \ M.biUnion id).powersetCard 2).image ω

/- `U`–`C` pairs covered by a selected witness. -/
def coveredUC (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) : Finset (Finset V × Finset V) :=
  ((J \ M.biUnion id) ×ˢ M.biUnion id).filter
    (fun pr => ∃ v ∈ selVerts J M ω, v ∈ pr.1 ∧ v ∈ pr.2)

/- For a point `p ∈ C`, the number of `U`-points `x` with `(x,p)` covered. -/
def gCount (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) (p : Finset V) : ℕ :=
  ((J \ M.biUnion id).filter
    (fun x => ∃ v ∈ selVerts J M ω, v ∈ x ∧ v ∈ p)).card

/- The colour class of `p`: `2`-subsets `s` of `U` whose witness block is `s ∪ {p}`. -/
def linkGraph (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) (p : Finset V) : Finset (Finset (Finset V)) :=
  ((J \ M.biUnion id).powersetCard 2).filter (fun s => block J (ω s) = insert p s)

/-
Double counting: total vertex–`U` incidences equal `u * r`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma incid_total (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (M : Finset (Finset (Finset V))) :
    ∑ v ∈ J.biUnion id, (block J v ∩ (J \ M.biUnion id)).card
      = (J \ M.biUnion id).card * r := by
  have h_double_counting : ∀ x ∈ J \ M.biUnion id, ∑ v ∈ J.biUnion id, (if v ∈ x then 1 else 0) = r := by
    intro x hx
    have hx_card : x.card = r := by
      exact huni x ( Finset.mem_sdiff.mp hx |>.1 ) ▸ rfl
    simp;
    convert hx_card using 2 ; ext v ; aesop;
  convert Finset.sum_congr rfl h_double_counting using 1;
  · rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    simp +contextual [ block ];
    exact fun x y hy hx => congr_arg Finset.card ( by ext; aesop );
  · rw [ Finset.sum_const, smul_eq_mul, mul_comm ]

/-
The matched points number `3t`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma card_matched (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) : (M.biUnion id).card = 3 * M.card := by
  rw [ Finset.card_biUnion ];
  · rw [ Finset.sum_const_nat ];
    rw [ mul_comm ];
    exact fun x hx => hM.1 x hx |>.1;
  · exact fun x hx y hy hxy => hM.2 x hx y hy hxy

/-
A witness function for `U`-pairs: injective, with `ω s` a common vertex of the
two edges of `s`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma exists_witness (J : Finset (Finset V)) (hint : Intersecting J)
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (hu : 0 < (J \ M.biUnion id).card) :
    ∃ ω : Finset (Finset V) → V,
      (∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x) ∧
      Set.InjOn ω ↑((J \ M.biUnion id).powersetCard 2) := by
  by_contra! h_contra;
  obtain ⟨ω, hω⟩ : ∃ ω : Finset (Finset V) → V, (∀ s ∈ Finset.powersetCard 2 (J \ M.biUnion id), ∀ x ∈ s, ω s ∈ x) := by
    have hω_exists : ∀ s ∈ Finset.powersetCard 2 (J \ M.biUnion id), ∃ v, ∀ x ∈ s, v ∈ x := by
      simp +decide [ Finset.mem_powersetCard ];
      intro s hs hs'; rw [ Finset.card_eq_two ] at hs'; obtain ⟨ x, y, hxy ⟩ := hs'; simp_all +decide [ Finset.subset_iff ] ;
      exact Exists.elim ( ‹Intersecting J› x hs.1.1 y hs.2.1 ) fun v hv => ⟨ v, by aesop ⟩;
    exact ⟨ fun s => if hs : s ∈ Finset.powersetCard 2 ( J \ M.biUnion id ) then Classical.choose ( hω_exists s hs ) else Classical.choice ( show Nonempty V from by
                                                                                                                                              obtain ⟨ x, hx ⟩ := Finset.card_pos.mp hu; exact ⟨ Classical.choose ( Finset.card_pos.mp ( show 0 < Finset.card x from Finset.card_pos.mpr ( Intersecting.edge_nonempty ‹_› ( Finset.mem_sdiff.mp hx |>.1 ) ) ) ) ⟩ ; ), fun s hs x hx => by simpa [ hs ] using Classical.choose_spec ( hω_exists s hs ) x hx ⟩;
  obtain ⟨s, s', hs, hs', h_eq⟩ : ∃ s s' : Finset (Finset V), s ∈ Finset.powersetCard 2 (J \ M.biUnion id) ∧ s' ∈ Finset.powersetCard 2 (J \ M.biUnion id) ∧ s ≠ s' ∧ ω s = ω s' := by
    specialize h_contra ω hω;
    simp_all +decide [ Set.InjOn ];
    exact ⟨ _, ⟨ h_contra.choose_spec.1, h_contra.choose_spec.2.1 ⟩, _, ⟨ h_contra.choose_spec.2.2.choose_spec.1, h_contra.choose_spec.2.2.choose_spec.2.1 ⟩, h_contra.choose_spec.2.2.choose_spec.2.2.2, h_contra.choose_spec.2.2.choose_spec.2.2.1 ⟩;
  have h_card : (s ∪ s').card ≤ 3 := by
    have h_card : (s ∪ s').card ≤ (J.filter (fun A => ω s ∈ A)).card := by
      refine Finset.card_le_card ?_;
      grind;
    exact h_card.trans ( hdeg _ );
  have h_card_eq : (s ∪ s').card = 3 := by
    have h_card_eq : (s ∩ s').card ≤ 1 := by
      have := Finset.mem_powersetCard.mp hs; have := Finset.mem_powersetCard.mp hs'; simp_all +decide ;
      exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( by linarith ) ) fun h => h_eq.1 <| Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith ) |> fun h' => Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by linarith ) |> fun h'' => by aesop );
    grind;
  have h_card_eq : s ∪ s' = block J (ω s) := by
    refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
    · grind +locals;
    · exact le_trans ( hdeg _ ) ( by linarith );
  have h_card_eq : IsGoodTriple J (block J (ω s)) := by
    exact ⟨ by aesop, ω s, rfl ⟩;
  apply no_good_triple_in_U J M hM hMmax h_card_eq;
  grind

/-
Lower bound from witnesses: `∑_{v ∈ Sel} a(v) ≥ u(u-1)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma witness_lower (J : Finset (Finset V))
    (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x)
    (hωinj : Set.InjOn ω ↑((J \ M.biUnion id).powersetCard 2)) :
    (J \ M.biUnion id).card * ((J \ M.biUnion id).card - 1)
      ≤ ∑ v ∈ selVerts J M ω, (block J v ∩ (J \ M.biUnion id)).card := by
  rw [ selVerts ];
  rw [ Finset.sum_image <| by tauto ];
  refine' le_trans _ ( Finset.sum_le_sum fun s hs => Finset.card_mono <| show s ⊆ block J ( ω s ) ∩ ( J \ M.biUnion id ) from _ );
  · rw [ Finset.sum_congr rfl fun x hx => Finset.mem_powersetCard.mp hx |>.2 ] ; simp +decide [ Nat.choose_two_right ];
    rw [ Nat.div_mul_cancel ( even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ) ];
  · simp_all +decide [ Finset.subset_iff, block ]

/- Matched points are edges of `J`. -/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma matched_subset (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) : M.biUnion id ⊆ J := by
  intro b hb
  obtain ⟨S, hSM, hbS⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨_, v, rfl⟩ := hM.1 S hSM
  exact Finset.filter_subset _ _ hbS

/-
Unselected lower bound: total `U`–`C` pairs `≤` covered-by-selected plus
`2 ∑_{w ∉ Sel} a(w)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma unsel_lower (J : Finset (Finset V)) (hint : Intersecting J)
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (ω : Finset (Finset V) → V) :
    ((J \ M.biUnion id) ×ˢ M.biUnion id).card
      ≤ (coveredUC J M ω).card
        + 2 * ∑ v ∈ J.biUnion id \ selVerts J M ω,
            (block J v ∩ (J \ M.biUnion id)).card := by
  have h_card_biUnion : ((J \ M.biUnion id) ×ˢ M.biUnion id \ coveredUC J M ω).card ≤ ∑ v ∈ (J.biUnion id) \ selVerts J M ω, ((J \ M.biUnion id).filter (fun x => v ∈ x)).card * ((M.biUnion id).filter (fun x => v ∈ x)).card := by
    have h_card_biUnion : ((J \ M.biUnion id) ×ˢ M.biUnion id \ coveredUC J M ω) ⊆ Finset.biUnion ((J.biUnion id) \ selVerts J M ω) (fun v => ((J \ M.biUnion id).filter (fun x => v ∈ x)) ×ˢ ((M.biUnion id).filter (fun x => v ∈ x))) := by
      intro x hx; simp_all +decide ;
      obtain ⟨ v, hv ⟩ := Finset.nonempty_iff_ne_empty.2 ( show x.1 ∩ x.2 ≠ ∅ from by
                                                            exact Finset.Nonempty.ne_empty ( by have := ‹Intersecting J› x.1 hx.1.1.1 x.2 ( by obtain ⟨ a, ha, ha' ⟩ := hx.1.2; exact Finset.mem_of_subset ( matched_subset J M hM ) ( Finset.mem_biUnion.2 ⟨ a, ha, ha' ⟩ ) ) ; aesop ) );
      refine' ⟨ v, ⟨ ⟨ x.1, hx.1.1.1, Finset.mem_of_mem_inter_left hv ⟩, _ ⟩, Finset.mem_of_mem_inter_left hv, Finset.mem_of_mem_inter_right hv ⟩;
      contrapose! hx; unfold coveredUC at *; aesop;
    exact le_trans ( Finset.card_le_card h_card_biUnion ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun _ _ => by rw [ Finset.card_product ] ) );
  -- For each $v \in J.biUnion id \ selVerts J M ω$, we have $(J \ M.biUnion id).filter (fun x => v ∈ x)).card * ((M.biUnion id).filter (fun x => v ∈ x)).card ≤ 2 * (block J v ∩ (J \ M.biUnion id)).card$.
  have h_card_filter : ∀ v ∈ (J.biUnion id) \ selVerts J M ω, ((J \ M.biUnion id).filter (fun x => v ∈ x)).card * ((M.biUnion id).filter (fun x => v ∈ x)).card ≤ 2 * (block J v ∩ (J \ M.biUnion id)).card := by
    intro v hv
    have h_card_filter : ((J \ M.biUnion id).filter (fun x => v ∈ x)).card + ((M.biUnion id).filter (fun x => v ∈ x)).card ≤ 3 := by
      rw [ ← Finset.card_union_of_disjoint ];
      · refine' le_trans ( Finset.card_le_card _ ) ( hdeg v );
        simp +contextual [ Finset.subset_iff ];
        rintro x ( hx | hx ) <;> simp_all +decide [ Finset.mem_biUnion ];
        exact matched_subset J M hM ( Finset.mem_biUnion.mpr ⟨ _, hx.1.choose_spec.1, hx.1.choose_spec.2 ⟩ );
      · simp +contextual [ Finset.disjoint_left ];
    have h_card_filter : (block J v ∩ (J \ M.biUnion id)).card = ((J \ M.biUnion id).filter (fun x => v ∈ x)).card := by
      congr 1 with x ; simp +decide [ block ];
      tauto;
    rcases n : Finset.card ( Finset.filter ( fun x => v ∈ x ) ( J \ M.biUnion id ) ) with ( _ | _ | _ | _ | n ) <;> rcases n' : Finset.card ( Finset.filter ( fun x => v ∈ x ) ( M.biUnion id ) ) with ( _ | _ | _ | _ | n' ) <;> simp_all +arith +decide only;
  rw [ ← Finset.card_sdiff_add_card_inter ];
  rw [ add_comm ];
  refine' add_le_add _ _;
  any_goals exact coveredUC J M ω;
  · exact Finset.card_le_card fun x hx => by aesop;
  · exact h_card_biUnion.trans ( by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum h_card_filter )

/-
Regrouping: `|coveredUC| = ∑_{p ∈ C} g(p)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma coveredUC_regroup (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) :
    (coveredUC J M ω).card = ∑ p ∈ M.biUnion id, gCount J M ω p := by
  simp +decide only [coveredUC, Finset.card_filter];
  rw [ Finset.sum_product ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop

/-
For each point `p ∈ C`, `g(p) ≤ |support(linkGraph p)|`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma gCount_le_support (J : Finset (Finset V)) (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x)
    {p : Finset V} (hp : p ∈ M.biUnion id) :
    gCount J M ω p ≤ ((linkGraph J M ω p).biUnion id).card := by
  refine Finset.card_mono ?_;
  intro x hx
  obtain ⟨v, hv_sel, hv_x, hv_p⟩ := Finset.mem_filter.mp hx |>.2
  have hv_block : block J v = insert p (Classical.choose (Finset.mem_image.mp hv_sel)) := by
    have hv_block : block J v ⊇ insert p (Classical.choose (Finset.mem_image.mp hv_sel)) := by
      grind +locals;
    have hv_block_card : (block J v).card ≤ 3 := by
      exact hdeg v;
    have hv_block_card_eq : (insert p (Classical.choose (Finset.mem_image.mp hv_sel))).card = 3 := by
      grind +suggestions;
    rw [ Finset.eq_of_subset_of_card_le hv_block ( by linarith ) ];
  refine' Finset.mem_biUnion.mpr ⟨ Classical.choose ( Finset.mem_image.mp hv_sel ), _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
  · simp_all +decide [ Finset.mem_powersetCard, linkGraph ];
    grind;
  · grind +locals

/-
Edges of a link graph are `2`-subsets of `U`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma linkGraph_edges (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) (p : Finset V) :
    ∀ e ∈ linkGraph J M ω p, e.card = 2 ∧ e ⊆ (J \ M.biUnion id) := by
  intro e he; rw [ linkGraph ] at he; rw [ Finset.mem_filter ] at he; rw [ Finset.mem_powersetCard ] at he; aesop;

/-
Distinct colours give edge-disjoint link graphs (for matched points `p, p'`).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma linkGraph_disjoint (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) {p p' : Finset V}
    (hpC : p ∈ M.biUnion id) (hp'C : p' ∈ M.biUnion id) (h : p ≠ p') :
    Disjoint (linkGraph J M ω p) (linkGraph J M ω p') := by
  refine Finset.disjoint_left.mpr ?_;
  intro e he he'; simp_all +decide ;
  have := Finset.mem_filter.mp he; have := Finset.mem_filter.mp he'; simp_all +decide [ Finset.subset_iff, Finset.ext_iff ] ;
  grind +splitImp

/-
**Cross-intersecting (maximality).** Two link edges of different colours within a
matched triple cannot be vertex-disjoint.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma linkGraph_cross (J : Finset (Finset V))
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (ω : Finset (Finset V) → V)
    {S : Finset (Finset V)} (hS : S ∈ M) {p p' : Finset V}
    (hp : p ∈ S) (hp' : p' ∈ S) (hpp' : p ≠ p')
    {e f : Finset (Finset V)}
    (he : e ∈ linkGraph J M ω p) (hf : f ∈ linkGraph J M ω p') :
    (e ∩ f).Nonempty := by
  contrapose! hMmax;
  refine' ⟨ Insert.insert ( { p } ∪ e ) ( Insert.insert ( { p' } ∪ f ) ( M.erase S ) ), _, _ ⟩ <;> simp_all +decide [ IsMatching ];
  · refine' ⟨ _, _, _, _ ⟩;
    · unfold linkGraph at he hf; simp_all +decide [ IsGoodTriple ] ;
      grind +suggestions;
    · refine' ⟨ _, _ ⟩;
      · simp_all +decide [ Finset.disjoint_left, Finset.ext_iff ];
        intro x hx; have := Finset.mem_powersetCard.mp ( Finset.mem_filter.mp he |>.1 ) ; have := Finset.mem_powersetCard.mp ( Finset.mem_filter.mp hf |>.1 ) ; simp_all +decide [ Finset.subset_iff ] ;
        grind;
      · intro a ha₁ ha₂ ha₃; have := hM.2 _ hS _ ha₂; simp_all +decide [ Finset.disjoint_left ] ;
        grind +locals;
    · refine' ⟨ _, _ ⟩;
      · intro h; simp_all +decide [ Finset.disjoint_left, Finset.ext_iff ] ;
        refine' ⟨ _, _, _ ⟩ <;> contrapose! hMmax <;> simp_all +decide [ linkGraph ];
        · grind;
        · grind;
        · exact ⟨ _, hMmax.choose_spec.2, hMmax.choose_spec.1 ⟩;
      · intro a ha₁ ha₂ ha₃; have := hM.2 _ hS _ ha₂; simp_all +decide [ Finset.disjoint_left ] ;
        refine' ⟨ this ( Ne.symm ha₁ ) hp', _ ⟩;
        intro x hx₁ hx₂; have := Finset.mem_sdiff.mp ( Finset.mem_powersetCard.mp ( Finset.mem_filter.mp hf |>.1 ) |>.1 hx₁ ) ; simp_all +decide ;
    · intro T hTS hTM; have := hM.2 _ hTM _ hS hTS; simp_all +decide [ Finset.disjoint_left ] ;
      simp_all +decide [ linkGraph ];
      grind;
  · simp_all +decide [ Finset.subset_iff, linkGraph ];
    grind

/-
Per matched triple, the colour-support sum is `≤ K` (link graphs + `lemma2`).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma per_triple_bound (J : Finset (Finset V))
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x)
    {S : Finset (Finset V)} (hS : S ∈ M) :
    ∑ p ∈ S, gCount J M ω p ≤ max 12 ((J \ M.biUnion id).card + 4) := by
  rcases hM.1 S hS with ⟨ hS₁, hS₂ ⟩;
  rcases Finset.card_eq_three.mp hS₁ with ⟨ a, b, c, hab, hbc, hac ⟩;
  have h_sum_le_K : (gCount J M ω a) + (gCount J M ω b) + (gCount J M ω c) ≤ max 12 ((J \ M.biUnion id).card + 4) := by
    refine' le_trans _ ( lemma2 ( J \ M.biUnion id ) ( linkGraph J M ω a ) ( linkGraph J M ω b ) ( linkGraph J M ω c ) _ _ _ _ _ _ _ _ _ );
    any_goals intro e he f hf; exact linkGraph_cross J M hM hMmax ω hS (by simp +decide [ hac ] ) (by simp +decide [ hac ] ) (by tauto) he hf;
    any_goals exact linkGraph_edges J M ω _;
    · gcongr;
      · apply gCount_le_support J hdeg M hM ω hωmem;
        exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · apply gCount_le_support J hdeg M hM ω hωmem;
        exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · apply gCount_le_support J hdeg M hM ω hωmem;
        exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
    · apply linkGraph_disjoint;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact hab;
    · apply linkGraph_disjoint;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact hbc;
    · apply linkGraph_disjoint;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · tauto;
  grind

/-
`S ≤ t K`: covered `U`–`C` pairs are at most `t · K`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma S_bound (J : Finset (Finset V))
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x) :
    (coveredUC J M ω).card ≤ M.card * max 12 ((J \ M.biUnion id).card + 4) := by
  rw [ coveredUC_regroup ];
  rw [ Finset.sum_biUnion ];
  · calc
      _ ≤ ∑ _T ∈ M, max 12 ((J \ M.biUnion id).card + 4) :=
        Finset.sum_le_sum fun T hT => per_triple_bound J hdeg M hM hMmax ω hωmem hT
      _ = _ := by simp
  · exact fun x hx y hy hxy => hM.2 x hx y hy hxy

/-
**Equation (4).** The core counting inequality obtained from a maximum matching
via the link graphs and `lemma2`.  Here `t = |M|`, `u = |U|`, and
`K = max 12 (u + 4)`; the inequality is the cleared-denominators form of
`u r ≥ u(u-1) + (3tu - tK)/2`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma eq4_nat (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (hu : 0 < (J \ M.biUnion id).card) :
    2 * (J \ M.biUnion id).card * ((J \ M.biUnion id).card - 1)
        + 3 * M.card * (J \ M.biUnion id).card
      ≤ 2 * (J \ M.biUnion id).card * r
        + M.card * max 12 ((J \ M.biUnion id).card + 4) := by
  obtain ⟨ω, hωmem, hωinj⟩ := exists_witness J ‹_› ‹_› M ‹_› ‹_› hu;
  have hsplit : ∑ v ∈ J.biUnion id, (block J v ∩ (J \ M.biUnion id)).card = ∑ v ∈ selVerts J M ω, (block J v ∩ (J \ M.biUnion id)).card + ∑ v ∈ J.biUnion id \ selVerts J M ω, (block J v ∩ (J \ M.biUnion id)).card := by
    rw [ add_comm, Finset.sum_sdiff <| show selVerts J M ω ⊆ J.biUnion id from ?_ ];
    intro v hv; obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hv; specialize hωmem s hs; simp_all +decide [ Finset.subset_iff ] ;
    exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hs.1 hx |>.1, hωmem x hx ⟩;
  have := unsel_lower J ‹_› ‹_› M ‹_› ω; simp_all +decide [ Finset.card_product ] ;
  have := S_bound J hdeg M hM hMmax ω; simp_all +decide ;
  have := card_matched J M hM; simp_all +decide [ mul_comm, mul_assoc ] ;
  linarith [ incid_total r J huni M, witness_lower J M ω ( fun s hs x hx => hωmem s ( Finset.mem_powersetCard.mp hs |>.1 ) ( Finset.mem_powersetCard.mp hs |>.2 ) x hx ) hωinj ]

/- **Lemma 4.** An `r`-uniform intersecting hypergraph `J` of maximum degree `≤ 3`
with `q` edges satisfies `4 τ(J) ≤ q + r + 4`. -/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma lemma4 (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 3) :
    4 * coverNum J ≤ J.card + r + 4 := by
  obtain ⟨M, hM, hMmax⟩ := exists_max_matching J
  have hq := matching_q J M hM
  have hcov := matching_cover J hint M hM
  have hl1 := lemma1 r J huni hint hdeg
  set t := M.card with ht
  set u := (J \ M.biUnion id).card with hudef
  -- hq : J.card = 3*t + u ; hcov : coverNum J ≤ t + (u+1)/2 ; hl1 : J.card ≤ 2r+1
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · omega
  · have heq4 := eq4_nat r J huni hint hdeg M hM hMmax hupos
    rw [← ht, ← hudef] at heq4
    have h5 := lemma3 u hupos t ((u : ℤ) + t - r) (max 12 ((u : ℤ) + 4)) rfl
      (by omega)
      (by
        have h : ((2 * u * (u - 1) + 3 * t * u : ℕ) : ℤ)
            ≤ ((2 * u * r + t * max 12 (u + 4) : ℕ) : ℤ) := by exact_mod_cast heq4
        push_cast [Nat.cast_sub (show 1 ≤ u by omega)] at h
        nlinarith [h])
    omega

/- ## The peeling reduction (Key Lemma) -/

/-
**Key Lemma.** For every `r`-uniform intersecting hypergraph `H`,
`4 τ(H) ≤ |E(H)| + r + 4`.

Proved by induction on the number of edges: if some vertex has degree `≥ 4`, peel
it off; otherwise the maximum degree is `≤ 3` and `lemma4` applies.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma keyLemma (r : ℕ) (H : Finset (Finset V)) (huni : IsUniform r H)
    (hint : Intersecting H) :
    4 * coverNum H ≤ H.card + r + 4 := by
  induction' n : H.card using Nat.strong_induction_on with n ih generalizing H;
  -- Assume there exists a vertex $v$ with degree $\geq 4$.
  by_cases h_deg : ∃ v, 4 ≤ edgeDeg H v;
  · -- Let $H'$ be the subhypergraph of $H$ obtained by removing all edges containing $v$.
    obtain ⟨v, hv⟩ := h_deg
    set H' := H.filter (fun E => v ∉ E) with hH';
    -- Then $H'$ is an $r$-uniform intersecting hypergraph with fewer edges than $H$.
    have hH'_uniform : IsUniform r H' := by
      exact fun E hE => huni E ( Finset.mem_filter.mp hE |>.1 )
    have hH'_intersecting : Intersecting H' := by
      exact fun E hE F hF => ‹Intersecting H› E ( Finset.filter_subset _ _ hE ) F ( Finset.filter_subset _ _ hF )
    have hH'_card : H'.card < H.card := by
      refine' Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.filter_subset _ _, _ ⟩ );
      simp_all +decide [ Finset.ext_iff, edgeDeg ];
      exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt hv ) ) fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
    -- By the induction hypothesis, we have $4 * coverNum H' ≤ H'.card + r + 4$.
    have h_ind : 4 * coverNum H' ≤ H'.card + r + 4 := by
      exact ih _ ( by linarith ) _ hH'_uniform hH'_intersecting rfl;
    -- Now bound coverNum H ≤ 1 + coverNum H'.
    have h_coverNum : coverNum H ≤ 1 + coverNum H' := by
      -- Since $H'$ is intersecting, its edges are nonempty (Intersecting.edge_nonempty), so `exists_opt_cover` gives a cover $C'$ of $H'$ with $C'.card = coverNum H'$.
      obtain ⟨C', hC'⟩ : ∃ C' : Finset V, IsCover H' C' ∧ C'.card = coverNum H' := by
        apply exists_opt_cover;
        exact fun E hE => Intersecting.edge_nonempty hH'_intersecting hE;
      -- Then $C' \cup \{v\}$ (or insert $v$ $C'$) is a cover of $H$: any edge $E \in H$ either contains $v$ (covered by $v$) or lies in $H'$ (covered by $C'$).
      have h_cover : IsCover H (insert v C') := by
        intro E hE; by_cases hvE : v ∈ E <;> simp_all +decide [ IsCover ] ;
      exact le_trans ( coverNum_le h_cover ) ( by rw [ add_comm ] ; exact Finset.card_insert_le _ _ |> le_trans <| by linarith );
    -- Since $H$ is the disjoint union of $H'$ and $H.filter (fun E => v ∈ E)$, we have $H.card = H'.card + edgeDeg H v$.
    have h_card : H.card = H'.card + edgeDeg H v := by
      rw [ show edgeDeg H v = Finset.card ( Finset.filter ( fun E => v ∈ E ) H ) from rfl, ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr fun _ _ _ => by tauto ) ] ; congr ; ext ; by_cases h : v ∈ ‹Finset V› <;> aesop;
    grind;
  · grind +suggestions

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma peel5 (r : ℕ) (H : Finset (Finset V)) (huni : IsUniform r H)
    (hint : Intersecting H) :
    ∃ (J : Finset (Finset V)) (k : ℕ),
      J ⊆ H ∧ (∀ v, edgeDeg J v ≤ 4) ∧
      J.card + 5 * k ≤ H.card ∧
      coverNum H ≤ k + coverNum J := by
  induction' h : Finset.card H using Nat.strong_induction_on with n ih generalizing H;
  by_cases h_deg : ∃ v, edgeDeg H v ≥ 5;
  · obtain ⟨ v, hv ⟩ := h_deg;
    obtain ⟨J, k, hJ_sub, hJ_deg, hJ_card, hJ_cover⟩ : ∃ J : Finset (Finset V), ∃ k : ℕ, J ⊆ H.filter (fun E => v ∉ E) ∧ (∀ w, edgeDeg J w ≤ 4) ∧ J.card + 5 * k ≤ (H.filter (fun E => v ∉ E)).card ∧ coverNum (H.filter (fun E => v ∉ E)) ≤ k + coverNum J := by
      apply ih ((H.filter (fun E => v ∉ E)).card);
      · refine' h ▸ Finset.card_lt_card _;
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt hv ) ) fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
      · exact fun E hE => huni E ( Finset.mem_filter.mp hE |>.1 );
      · intro E hE F hF; have := ‹Intersecting H› E ( Finset.mem_filter.mp hE |>.1 ) F ( Finset.mem_filter.mp hF |>.1 ) ; aesop;
      · rfl;
    refine' ⟨ J, k + 1, _, _, _, _ ⟩;
    · exact fun x hx => Finset.mem_filter.mp ( hJ_sub hx ) |>.1;
    · exact hJ_deg;
    · have h_card_split : H.card = (H.filter (fun E => v ∈ E)).card + (H.filter (fun E => v ∉ E)).card := by
        rw [ Finset.card_filter_add_card_filter_not ];
      linarith! [ show Finset.card ( Finset.filter ( fun E => v ∈ E ) H ) ≥ 5 by exact hv ];
    · have h_cover : ∃ C : Finset V, IsCover (H.filter (fun E => v ∉ E)) C ∧ C.card = coverNum (H.filter (fun E => v ∉ E)) := by
        apply exists_opt_cover;
        exact fun E hE => Intersecting.edge_nonempty ‹_› ( Finset.mem_filter.mp hE |>.1 );
      obtain ⟨ C, hC₁, hC₂ ⟩ := h_cover;
      have h_cover : IsCover H (insert v C) := by
        intro E hE; by_cases hvE : v ∈ E <;> simp_all +decide [ IsCover ] ;
      exact le_trans ( coverNum_le h_cover ) ( by linarith [ Finset.card_insert_le v C ] );
  · exact ⟨ H, 0, Finset.Subset.refl _, fun v => not_lt.1 fun contra => h_deg ⟨ v, contra ⟩, by simp +decide [ h ], by simp +decide ⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma lemma1_deg4 (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    J.card ≤ 3 * r + 1 := by
  by_cases hJ : J = ∅;
  · grind;
  · obtain ⟨E, hE⟩ : ∃ E ∈ J, True := by
      exact Exists.elim ( Finset.nonempty_of_ne_empty hJ ) fun E hE => ⟨ E, hE, trivial ⟩;
    have h_double_counting : (J.card - 1) ≤ ∑ v ∈ E, (edgeDeg J v - 1) := by
      have h_double_counting : (J.card - 1) ≤ ∑ F ∈ J.erase E, (E ∩ F).card := by
        exact le_trans ( by simp +decide [ Finset.card_erase_of_mem hE.1 ] ) ( Finset.sum_le_sum fun x hx => Finset.card_pos.mpr <| by have := ‹∀ E ∈ J, ∀ F ∈ J, ( E ∩ F ).Nonempty› E hE.1 x ( Finset.mem_of_mem_erase hx ) ; aesop );
      have h_double_counting : ∑ F ∈ J.erase E, (E ∩ F).card = ∑ v ∈ E, ∑ F ∈ J.erase E, (if v ∈ F then 1 else 0) := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
      simp_all +decide [ Finset.filter_erase, edgeDeg ];
    have h_double_counting : (J.card - 1) ≤ ∑ v ∈ E, 3 := by
      exact h_double_counting.trans ( Finset.sum_le_sum fun v hv => Nat.sub_le_of_le_add <| by linarith [ hdeg v ] );
    simp_all +decide [ mul_comm, huni E hE.1 ]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma matching_cover4 (J : Finset (Finset V)) (hint : Intersecting J)
    (M : Finset V)
    (hM4 : ∀ v ∈ M, (block J v).card = 4)
    (hMdisj : ∀ v ∈ M, ∀ w ∈ M, v ≠ w → Disjoint (block J v) (block J w)) :
    coverNum J ≤ M.card + (J.card - 4 * M.card + 1) / 2 := by
  obtain ⟨C, hC⟩ : ∃ C : Finset V, (∀ E ∈ J \ (M.biUnion (fun v => block J v)), ∃ v ∈ C, v ∈ E) ∧ C.card ≤ (J.card - 4 * M.card + 1) / 2 := by
    convert intersecting_cover_half ( J \ M.biUnion ( fun v => block J v ) ) _;
    · rw [ Finset.card_sdiff ];
      rw [ Finset.inter_eq_left.mpr ];
      · rw [ Finset.card_biUnion ];
        · rw [ Finset.sum_congr rfl hM4, Finset.sum_const, smul_eq_mul, mul_comm ];
        · exact fun v hv w hw hvw => hMdisj v hv w hw hvw;
      · exact Finset.biUnion_subset.mpr fun v hv => Finset.filter_subset _ _;
    · exact fun x hx y hy => ‹Intersecting J› x ( Finset.mem_sdiff.mp hx |>.1 ) y ( Finset.mem_sdiff.mp hy |>.1 );
  refine' le_trans ( coverNum_le _ ) _;
  exact M ∪ C;
  · intro E hE; by_cases hE' : E ∈ M.biUnion ( fun v => block J v ) <;> simp_all +decide ;
    · obtain ⟨ v, hv, hv' ⟩ := hE'; use v; simp_all +decide [ block ] ;
    · exact Exists.elim ( hC.1 E hE hE' ) fun v hv => ⟨ v, Or.inr hv.1, hv.2 ⟩;
  · grind

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma matched_blocks_card (J : Finset (Finset V)) (M : Finset V)
    (hM4 : ∀ v ∈ M, (block J v).card = 4) (hMsub : ∀ v ∈ M, block J v ⊆ J)
    (hMdisj : ∀ v ∈ M, ∀ w ∈ M, v ≠ w → Disjoint (block J v) (block J w)) :
    4 * M.card ≤ J.card := by
  have h_union : (M.biUnion (fun v => block J v)).card = 4 * M.card := by
    rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl hM4, Finset.sum_const, smul_eq_mul, mul_comm ];
    · exact fun v hv w hw hvw => hMdisj v hv w hw hvw;
  exact h_union ▸ Finset.card_le_card ( Finset.biUnion_subset.mpr hMsub )

def verts (J : Finset (Finset V)) : Finset V := J.biUnion id


def numDeg (J : Finset (Finset V)) (i : ℕ) : ℕ :=
  ((verts J).filter (fun v => edgeDeg J v = i)).card

def deg4Verts (J : Finset (Finset V)) : Finset V :=
  (verts J).filter (fun v => edgeDeg J v = 4)

def codeg (J : Finset (Finset V)) (W : Finset V) (s : Finset (Finset V)) : ℕ :=
  (W.filter (fun v => s ⊆ block J v)).card

def potential (J : Finset (Finset V)) (W : Finset V) : ℕ :=
  ∑ s ∈ J.powersetCard 2, (codeg J W s - 1)


def zCount (J : Finset (Finset V)) : ℕ :=
  ((J.powersetCard 2).filter (fun s => codeg J (deg4Verts J) s = 0)).card

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma edgeDeg_eq_block_card (J : Finset (Finset V)) (v : V) :
    edgeDeg J v = (block J v).card := rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma deg4Verts_card (J : Finset (Finset V)) :
    (deg4Verts J).card = numDeg J 4 := rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma exists_codeg_le_one (J : Finset (Finset V)) (W : Finset V) :
    ∃ W' ⊆ W, (∀ s ∈ J.powersetCard 2, codeg J W' s ≤ 1) ∧
      W.card ≤ W'.card + potential J W := by
  induction' n : potential J W using Nat.strong_induction_on with n ih generalizing W;
  by_cases h : ∃ s ∈ J.powersetCard 2, codeg J W s > 1;
  · obtain ⟨ s, hs₁, hs₂ ⟩ := h;
    obtain ⟨ v, hv₁, hv₂ ⟩ : ∃ v ∈ W, s ⊆ block J v := by
      contrapose! hs₂; simp_all +decide [ codeg ] ;
    have h_potential_lt : potential J (W.erase v) < potential J W := by
      refine' Finset.sum_lt_sum _ _;
      · intro i hi; exact Nat.sub_le_sub_right ( Finset.card_le_card ( Finset.filter_subset_filter _ ( Finset.erase_subset _ _ ) ) ) _;
      · refine' ⟨ s, hs₁, _ ⟩;
        unfold codeg at *;
        rw [ Finset.filter_erase ] ; aesop;
    grind;
  · exact ⟨ W, Finset.Subset.refl _, fun s hs => le_of_not_gt fun hs' => h ⟨ s, hs, hs' ⟩, by linarith ⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma codeg_sum (J : Finset (Finset V)) (huni : ∀ v ∈ deg4Verts J, (block J v).card = 4)
    (hsub : ∀ v ∈ deg4Verts J, block J v ⊆ J) :
    ∑ s ∈ J.powersetCard 2, codeg J (deg4Verts J) s = 6 * numDeg J 4 := by
  -- First, rewrite `codeg` using the alternative definition.
  -- `codeg J (deg4Verts J) s = (deg4Verts J).filter (fun v => s ⊆ block J v)).card`.
  -- This will allow us to switch the order of the sums in the double counting argument.
  unfold codeg;
  simp +decide only [Finset.card_filter];
  rw [ Finset.sum_comm, Finset.sum_eq_card_nsmul ] <;> norm_num;
  rw [ mul_comm, deg4Verts_card ];
  intro v hv; rw [ show { x ∈ Finset.powersetCard 2 J | x ⊆ block J v } = Finset.powersetCard 2 ( block J v ) from ?_ ] ; simp +decide [ huni v hv ] ;
  grind

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma potential_add_choose (J : Finset (Finset V))
    (huni : ∀ v ∈ deg4Verts J, (block J v).card = 4)
    (hsub : ∀ v ∈ deg4Verts J, block J v ⊆ J) :
    potential J (deg4Verts J) + (J.card).choose 2 = 6 * numDeg J 4 + zCount J := by
  have h_potential : potential J (deg4Verts J) + (Finset.powersetCard 2 J).card = ∑ s ∈ Finset.powersetCard 2 J, (codeg J (deg4Verts J) s + if codeg J (deg4Verts J) s = 0 then 1 else 0) := by
    unfold potential;
    rw [ Finset.card_eq_sum_ones, ← Finset.sum_add_distrib ];
    refine Finset.sum_congr rfl fun x hx => ?_
    rcases Nat.eq_zero_or_pos (codeg J (deg4Verts J) x) with h | h
    · simp +decide [h]
    · rw [if_neg (by omega)]; omega
  convert h_potential using 1;
  · rw [ Finset.card_powersetCard ];
  · rw [ Finset.sum_add_distrib, codeg_sum J huni hsub ];
    simp +decide [ zCount ]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma degree_sum (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    numDeg J 1 + 2 * numDeg J 2 + 3 * numDeg J 3 + 4 * numDeg J 4 = J.card * r := by
  have h_sum_deg : (J.biUnion id).sum (fun v => edgeDeg J v) = J.card * r := by
    calc
      _ = ∑ v ∈ J.biUnion id, ∑ E ∈ J, if v ∈ E then 1 else 0 := by
        simp only [edgeDeg, Finset.card_filter]
      _ = ∑ E ∈ J, ∑ v ∈ J.biUnion id, if v ∈ E then 1 else 0 := Finset.sum_comm
      _ = ∑ _E ∈ J, r := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [← Finset.card_filter]
        have heq : (J.biUnion id).filter (fun v => v ∈ E) = E := by
          ext v
          exact Finset.mem_filter.trans
            ⟨And.right, fun hv => ⟨Finset.mem_biUnion.mpr ⟨E,hE,hv⟩,hv⟩⟩
        rw [heq, huni E hE]
      _ = _ := by simp
  unfold numDeg verts;
  rw [ ← h_sum_deg, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
  rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ];
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by have := hdeg x; interval_cases edgeDeg J x <;> trivial;

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma z_le (J : Finset (Finset V)) (hint : Intersecting J)
    (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    zCount J ≤ numDeg J 2 + 3 * numDeg J 3 := by
  refine' le_trans _ ( _ : _ ≤ numDeg J 2 + 3 * numDeg J 3 );
  exact ∑ v ∈ ( verts J ).filter ( fun v => edgeDeg J v = 2 ∨ edgeDeg J v = 3 ), ( ( block J v ).powersetCard 2 ).card;
  · refine' le_trans ( Finset.card_le_card _ ) ( Finset.card_biUnion_le );
    intro s hs; simp_all +decide [ codeg ] ;
    obtain ⟨A, B, hAB⟩ : ∃ A B : Finset V, A ∈ J ∧ B ∈ J ∧ s = {A, B} ∧ A ≠ B := by
      rcases Finset.card_eq_two.mp hs.1.2 with ⟨ A, B, hAB ⟩ ; use A, B ; aesop;
    obtain ⟨v, hv⟩ : ∃ v ∈ A ∩ B, edgeDeg J v ≤ 3 := by
      obtain ⟨v, hv⟩ : ∃ v ∈ A ∩ B, edgeDeg J v ≠ 4 := by
        contrapose! hs; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ v, hv ⟩ := Finset.nonempty_iff_ne_empty.mpr ( show A ∩ B ≠ ∅ from Finset.Nonempty.ne_empty ( by simpa using ‹Intersecting J› A hAB.1 B hAB.2.1 ) ) ; use v; simp_all +decide [ deg4Verts, block ] ;
        exact Finset.mem_biUnion.mpr ⟨ A, hAB.1, hv.1 ⟩;
      exact ⟨ v, hv.1, Nat.le_of_lt_succ ( lt_of_le_of_ne ( hdeg v ) hv.2 ) ⟩;
    refine' ⟨ v, ⟨ _, _ ⟩, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact Finset.mem_biUnion.mpr ⟨ A, hAB.1, hv.1.1 ⟩;
    · have h_edgeDeg_ge_2 : 2 ≤ edgeDeg J v := by
        exact Finset.one_lt_card.2 ⟨ A, by aesop, B, by aesop ⟩;
      grind;
    · exact ⟨ Finset.mem_filter.mpr ⟨ hAB.1, hv.1.1 ⟩, Finset.mem_filter.mpr ⟨ hAB.2.1, hv.1.2 ⟩ ⟩;
  · unfold numDeg; simp +decide ;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ ← edgeDeg_eq_block_card ] ] ; simp +decide [ Finset.sum_filter ] ;
    rw [ Finset.card_filter, Finset.card_filter ] ; rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_le_sum fun x hx => by have := hdeg x; interval_cases edgeDeg J x <;> trivial;

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma Qlin_exists (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    ∃ W' ⊆ deg4Verts J,
      (∀ p ∈ J, ∀ q ∈ J, p ≠ q →
        (W'.filter (fun v => p ∈ block J v ∧ q ∈ block J v)).card ≤ 1) ∧
      4 * (J.card).choose 2 ≤ 4 * W'.card + 5 * (J.card * r) := by
  obtain ⟨ W', hW' ⟩ := exists_codeg_le_one J ( deg4Verts J );
  use W';
  refine' ⟨ hW'.1, _, _ ⟩;
  · intro p hp q hq hpq; specialize hW'; have := hW'.2.1 { p, q } ; simp_all +decide [ codeg ] ;
    convert hW'.2.1 { p, q } ( by aesop_cat ) ( by rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop_cat ) using 1 ; simp +decide [ Finset.subset_iff, block ];
  · have := potential_add_choose J ?_ ?_;
    · have := z_le J ‹_› ‹_›;
      have := degree_sum r J huni hdeg;
      linarith [ show ( deg4Verts J ).card = numDeg J 4 from deg4Verts_card J ];
    · exact fun v hv => edgeDeg_eq_block_card J v ▸ Finset.mem_filter.mp hv |>.2;
    · exact fun v hv => Finset.filter_subset _ _

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma tau_cast (c m q : ℕ) (h : c ≤ m + (q - 4 * m + 1) / 2) (h2 : 4 * m ≤ q) :
    (c : ℝ) ≤ (q : ℝ) / 2 - (m : ℝ) + 1 / 2 := by
  field_simp;
  norm_cast;
  rw [ Int.subNatNat_eq_coe ] ; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
lemma choose_cast (w q r : ℕ) (hq : 1 ≤ q)
    (h : 4 * (q.choose 2) ≤ 4 * w + 5 * (q * r)) :
    2 * (q : ℝ) * ((q : ℝ) - 1) ≤ 4 * (w : ℝ) + 5 * (q : ℝ) * (r : ℝ) := by
  norm_cast;
  rw [ Nat.choose_two_right ] at h;
  linarith [ Nat.div_mul_cancel ( show 2 ∣ q * ( q - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ) ]

end ErdosLovasz
end

section
/-
# Erdős–Lovász additive gap

Transfers a matching bound for dense linear four-element blocks to the
Erdős–Lovász cover number problem.
-/

open scoped Classical

namespace ErdosLovasz

universe u

/-- A matching bound for sufficiently dense linear systems of four-element blocks. -/
def DenseLinearFourMatching : Prop :=
  ∃ μ : ℝ, 0 < μ ∧
    ∀ {α ι : Type u} [DecidableEq α] [DecidableEq ι]
      (ground : Finset α) (W : Finset ι) (B : ι → Finset α) (D : ℕ),
      1 ≤ μ * (D : ℝ) →
      (∀ v ∈ W, B v ⊆ ground) →
      (∀ v ∈ W, (B v).card = 4) →
      (∀ x ∈ ground, ∀ y ∈ ground, x ≠ y →
        (W.filter fun v => x ∈ B v ∧ y ∈ B v).card ≤ 1) →
      (∀ x ∈ ground, (W.filter fun v => x ∈ B v).card ≤ D) →
      (ground.card : ℝ) * D ≤ 4 * (W.card : ℝ) + μ * (ground.card : ℝ) * D →
      ∃ M ⊆ W,
        (∀ v ∈ M, ∀ w ∈ M, v ≠ w → Disjoint (B v) (B w)) ∧
        (7 / 40 : ℝ) * (ground.card : ℝ) ≤ M.card

/-- Dense linear four-block matchings force an unbounded gap above three times the rank. -/
theorem additive_gap_of_denseLinearFourMatching
    (hmatch : DenseLinearFourMatching.{u}) (C : ℕ) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      ∀ {V : Type u} [DecidableEq V] (H : Finset (Finset V)),
        IsUniform r H → Intersecting H → coverNum H = r → 3 * r + C < H.card := by
  obtain ⟨μ, hμ, hmatching⟩ := hmatch
  obtain ⟨K, hK⟩ := exists_nat_gt (((8 : ℝ) * C + 42) / μ)
  refine ⟨K + 8 * C + 26, ?_⟩
  intro r hr V _ H huni hint hcov
  by_contra! hm
  obtain ⟨J, k, hJsub, hJdeg, hJcard, hJcov⟩ := peel5 r H huni hint
  have hJuni : IsUniform r J := fun E hE => huni E (hJsub hE)
  have hJint : Intersecting J := fun E hE F hF => hint E (hJsub hE) F (hJsub hF)
  have hkey := keyLemma r J hJuni hJint
  have hrcov : r ≤ k + coverNum J := hcov ▸ hJcov
  have hqLow : 3 * r ≤ J.card + 4 * C + 20 := by omega
  have hqr : r ≤ J.card := by omega
  have hqPos : 1 ≤ J.card := by omega
  have hqHigh : J.card ≤ 3 * r + 1 := lemma1_deg4 r J hJuni hJint hJdeg
  obtain ⟨W, hWsub, hWcodeg, hWcount⟩ := Qlin_exists r J hJuni hJint hJdeg
  have hBsub : ∀ v ∈ W, block J v ⊆ J := fun v _ => Finset.filter_subset _ _
  have hBcard : ∀ v ∈ W, (block J v).card = 4 := by
    intro v hv
    have hv4 := hWsub hv
    simp only [deg4Verts, Finset.mem_filter] at hv4
    rw [← edgeDeg_eq_block_card]
    exact hv4.2
  have hcap : ∀ x ∈ J, (W.filter fun v => x ∈ block J v).card ≤ r := by
    intro x hx
    rw [← hJuni x hx]
    apply Finset.card_le_card
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).2
  have hμK : (8 : ℝ) * C + 42 < (K : ℝ) * μ := (div_lt_iff₀ hμ).mp hK
  have hKr : (K : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show K ≤ r by omega)
  have hμr : (8 : ℝ) * C + 42 ≤ μ * (r : ℝ) := by
    linarith [mul_le_mul_of_nonneg_right hKr hμ.le]
  have hthreshold : 1 ≤ μ * (r : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) C]
  have hqLowReal : (3 : ℝ) * r ≤ (J.card : ℝ) + 4 * C + 20 := by exact_mod_cast hqLow
  have hqNonneg : (0 : ℝ) ≤ (J.card : ℝ) := by positivity
  have hDensity :
      (J.card : ℝ) * r ≤ 4 * (W.card : ℝ) + μ * (J.card : ℝ) * r := by
    have hcount := choose_cast W.card J.card r hqPos hWcount
    have hLow := mul_le_mul_of_nonneg_right hqLowReal hqNonneg
    have hμqr := mul_le_mul_of_nonneg_right hμr hqNonneg
    nlinarith only [hcount, hLow, hμqr]
  obtain ⟨M, hMsub, hMdisj, hMbound⟩ :=
    hmatching J W (block J) r hthreshold hBsub hBcard hWcodeg hcap hDensity
  have hM4 := fun v hv => hBcard v (hMsub hv)
  have hMground := fun v hv => hBsub v (hMsub hv)
  have hcover := matching_cover4 J hJint M hM4 hMdisj
  have hmatched := matched_blocks_card J M hM4 hMground hMdisj
  have htau := tau_cast _ _ _ hcover hmatched
  have hkreal : (r : ℝ) ≤ (k : ℝ) + (coverNum J : ℝ) := by exact_mod_cast hrcov
  have hcardreal : (J.card : ℝ) + 5 * (k : ℝ) ≤ (H.card : ℝ) := by exact_mod_cast hJcard
  have hqHighReal : (J.card : ℝ) ≤ 3 * (r : ℝ) + 1 := by exact_mod_cast hqHigh
  have hrBig : (8 : ℝ) * C + 26 ≤ r := by exact_mod_cast (show 8 * C + 26 ≤ r by omega)
  have hmReal : (H.card : ℝ) ≤ 3 * (r : ℝ) + C := by exact_mod_cast hm
  linarith only [hMbound, htau, hkreal, hcardreal, hqHighReal, hrBig, hmReal]

/-- The avoidance property gives the exact cover number at positive rank. -/
theorem coverNum_eq_of_isErdosLovaszFamily {r : ℕ} {H : Finset (Finset ℕ)}
    (hr : 0 < r) (h : Erdos21.IsErdosLovaszFamily r H) : coverNum H = r := by
  have hint : Intersecting H := h.2.1
  obtain ⟨E, hE, _⟩ := h.2.2 ∅ (by simp)
  have hEcover : IsCover H E := by
    intro F hF
    obtain ⟨v, hv⟩ := hint E hE F hF
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  have hUpper := coverNum_le hEcover
  rw [h.1 E hE] at hUpper
  refine le_antisymm hUpper ?_
  by_contra! hlt
  obtain ⟨S, hScover, hScard⟩ := exists_opt_cover (fun E hE => hint.edge_nonempty hE)
  obtain ⟨A, hA, hdisj⟩ := h.2.2 S (by omega)
  obtain ⟨v, hvS, hvA⟩ := hScover A hA
  exact Finset.disjoint_left.mp hdisj hvS hvA

theorem admissible_additive_gap (hmatch : DenseLinearFourMatching.{0}) (C : ℕ) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ H : Finset (Finset ℕ),
      Erdos21.IsErdosLovaszFamily r H → 3 * r + C < H.card := by
  obtain ⟨r₀, hgap⟩ := additive_gap_of_denseLinearFourMatching hmatch C
  refine ⟨max r₀ 1, ?_⟩
  intro r hr H hH
  have hr₀ : r₀ ≤ r := (le_max_left _ _).trans hr
  have hrPos : 0 < r := (le_max_right _ _).trans hr
  have huni : IsUniform r H := hH.1
  have hint : Intersecting H := hH.2.1
  exact hgap r hr₀ (V := ℕ) H huni hint (coverNum_eq_of_isErdosLovaszFamily hrPos hH)

end ErdosLovasz
end

section
open scoped Classical
open HadwigerLean HadwigerLean.Theorem2

namespace ErdosLovasz

universe u

private lemma filter_subtype_card {α : Type*} [DecidableEq α] (s : Finset α)
    (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset s).filter (fun x => P x.val)).card = (s.filter P).card := by
  classical
  let e : s ↪ α := Function.Embedding.subtype _
  have h : ((Finset.univ : Finset s).filter (fun x => P x.val)).map e = s.filter P := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.property, hi⟩
    · rintro ⟨hx, hp⟩
      exact ⟨⟨x, hx⟩, hp, rfl⟩
  rw [← h, Finset.card_map]

theorem denseLinearFourMatching : DenseLinearFourMatching.{u} := by
  classical
  let μ := matchingMu 4 (1 / 4)
  have hμ : 0 < μ := by unfold μ matchingMu; positivity
  refine ⟨μ, hμ, ?_⟩
  intro α ι _ _ ground W B D hD hsub hfour hlin hcap hdensity
  let H : IndexedHypergraph ground W :=
    { vertices := Finset.univ
      edges := Finset.univ
      edge := fun i => Finset.univ.filter (fun x => x.val ∈ B i.val)
      edge_subset := fun _ _ => Finset.subset_univ _ }
  have hunif : H.IsUniform 4 := by
    intro i _
    change ((Finset.univ : Finset ground).filter (fun x => x.val ∈ B i.val)).card = 4
    rw [filter_subtype_card ground (fun x => x ∈ B i.val)]
    have heq : ground.filter (fun x => x ∈ B i.val) = B i.val := by
      ext x
      exact Finset.mem_filter.trans ⟨And.right, fun hx => ⟨hsub i.val i.property hx, hx⟩⟩
    rw [heq]
    exact hfour i.val i.property
  have hcap' : ∀ x ∈ H.vertices, H.degree x ≤ D := by
    intro x _
    simpa only [H, IndexedHypergraph.degree, Finset.mem_filter, Finset.mem_univ,
      true_and, filter_subtype_card] using (show
      ((Finset.univ : Finset W).filter (fun i => x.val ∈ B i.val)).card ≤ D by
        rw [filter_subtype_card W (fun i => x.val ∈ B i)]
        exact hcap x.val x.property)
  have hlin' : H.maxCodegree ≤ 1 := by
    apply Finset.sup_le
    intro x _
    apply Finset.sup_le
    intro y hy
    have hxy : x.val ≠ y.val := fun heq => (Finset.mem_erase.mp hy).1 ((Subtype.ext heq).symm)
    simp only [H, IndexedHypergraph.codegree, Finset.mem_filter, Finset.mem_univ, true_and]
    change ((Finset.univ : Finset W).filter
      (fun i => (fun j => x.val ∈ B j ∧ y.val ∈ B j) i.val)).card ≤ 1
    rw [filter_subtype_card W (fun j => x.val ∈ B j ∧ y.val ∈ B j)]
    exact hlin _ x.property _ y.property hxy
  have hsize : H.vertices.card = ground.card := by simp [H]
  have hw : H.edges.card = W.card := by simp [H]
  have hpos : 0 < (D : ℝ) := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos hμ.le hn
    linarith
  have hbudget : (H.degreeDeficit D : ℝ) / D ≤ μ * (H.vertices.card : ℝ) := by
    apply (div_le_iff₀ hpos).2
    have hsum := H.degreeDeficit_add_edges hunif hcap'
    rw [hsize, hw] at hsum
    have hreal : (H.degreeDeficit D : ℝ) + 4 * (W.card : ℝ) = (ground.card : ℝ) * D := by
      exact_mod_cast hsum
    rw [hsize]
    linarith
  obtain ⟨M, hm, hcover⟩ := exists_almostPerfectMatching_paper H
    (r := 4) (ξ := 1/4) (D₀ := D) (B := 1)
    (by decide) (by norm_num) (by norm_num) (by decide) (by simpa [μ] using hD)
    hunif hcap' hlin' hbudget
  let emb : W ↪ ι := Function.Embedding.subtype _
  refine ⟨M.map emb, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  · intro i hi j hj hne
    obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
    have hd := hm.2 hi' hj' (fun h => hne (congrArg emb h))
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    let v : ground := ⟨x, hsub i'.val i'.property hxi⟩
    apply (Finset.disjoint_left.mp hd) (a := v)
    · simpa [H, v, emb] using hxi
    · simpa [H, v, emb] using hxj
  · rw [Finset.card_map]
    rw [H.covered_card_of_matching hunif hm, hsize] at hcover
    push_cast at hcover
    linarith [show 0 ≤ (ground.card : ℝ) by positivity]

end ErdosLovasz
end

section
/-
# Refuting the proposed asymptotic for Erdős Problem 21

This implication uses the exact statement of `erdos_21.variants.three_n` and
accepts an eventual lower bound on every admissible family as its hypothesis.
-/

open Filter

namespace Erdos21

/-- If every fixed additive upper bound is eventually exceeded by all admissible
families, then `f n = 3 * n + O(1)` is false. -/
theorem not_three_n_of_eventual_family_card_gt
    (h : ∀ C : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ F : Finset (Finset ℕ), IsErdosLovaszFamily n F → 3 * n + C < F.card) :
    ¬ (∃ C : ℕ, ∀ᶠ n : ℕ in atTop, f n ≤ 3 * n + C ∧ 3 * n ≤ f n + C) := by
  rintro ⟨C, hC⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hC.and (h C))
  let n := max M (C + 1)
  have hCn : C + 1 ≤ n := le_max_right _ _
  obtain ⟨⟨hupper, hclose⟩, hlower⟩ := hM n (le_max_left _ _)
  have hnonempty : {m : ℕ | ∃ F : Finset (Finset ℕ),
      IsErdosLovaszFamily n F ∧ F.card = m}.Nonempty := by
    by_contra hnone
    have h0 : f n = 0 := by
      rw [f, Set.not_nonempty_iff_eq_empty.mp hnone, Nat.sInf_empty]
    omega
  obtain ⟨F, hF, hcard⟩ := Nat.sInf_mem hnonempty
  change F.card = f n at hcard
  have hbound := hlower F hF
  omega


end Erdos21
end

theorem OMA.disproof : ¬ (type_of% @Erdos21.erdos_21.variants.three_n) := by
  apply Erdos21.not_three_n_of_eventual_family_card_gt
  intro C
  exact Filter.eventually_atTop.2
    (ErdosLovasz.admissible_additive_gap ErdosLovasz.denseLinearFourMatching C)
