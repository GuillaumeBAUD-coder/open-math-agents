import FormalConjectures.ErdosProblems.«808»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The positive-label variant of Erdős Problem 808 -/

/-
Copyright (c) 2026. Adapted from the Apache-2.0 Lean formalization by Codex and Boris Alexeev.
Pinned source:
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos808.lean
Mathematical proof: Alon, Ruzsa, and Solymosi, Sums, products and ratios along the edges of a graph.
This version uses Mathlib's Chebyshev bound and checks the positive-label variant.

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

noncomputable section
open Filter Erdos808
open scoped BigOperators Real

namespace OMA.Erdos808Port

/-- The `i`th prime in the block beginning at prime index `q²`. -/
def blockPrime (q : ℕ) (i : Fin q) : ℕ :=
  Nat.nth Nat.Prime (q ^ 2 + i)

lemma blockPrime_prime (q : ℕ) (i : Fin q) : (blockPrime q i).Prime := by
  exact Nat.prime_nth_prime _

lemma blockPrime_injective (q : ℕ) : Function.Injective (blockPrime q) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel
    (Nat.nth_injective Nat.infinite_setOfPred_prime hij)

lemma sq_le_blockPrime (q : ℕ) (i : Fin q) : q ^ 2 ≤ blockPrime q i := by
  exact (Nat.le_add_right (q ^ 2) (i : ℕ)).trans
    ((Nat.le_add_right _ 2).trans (Nat.add_two_le_nth_prime _))

/-- Chebyshev's elementary estimate supplies the primes without an asymptotic prime-counting theorem. -/
lemma blockPrime_le_seventh_eventually :
    ∀ᶠ q : ℕ in atTop, ∀ i : Fin q, blockPrime q i ≤ q ^ 7 := by
  filter_upwards [eventually_ge_atTop (40 : ℕ)] with q hq
  intro i
  let x : ℝ := q
  have hx : 40 ≤ x := by dsimp [x]; exact_mod_cast hq
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x := Real.log_le_self hx0.le
  have hl7 : Real.log (x ^ 7) ≤ 7 * x := by
    rw [Real.log_pow]
    push_cast
    linarith
  have hp7 : 1 ≤ x ^ 7 := one_le_pow₀ hx1
  have hl8 : Real.log (x ^ 7 + 1) ≤ 8 * x := by
    have hpow : x ^ 7 + 1 ≤ x ^ 8 := by
      calc
        x ^ 7 + 1 ≤ x ^ 7 + x ^ 7 * (x - 1) := by
          have hmul : 1 * 1 ≤ x ^ 7 * (x - 1) :=
            mul_le_mul hp7 (by linarith) (by norm_num) (by positivity)
          linarith
        _ = x ^ 8 := by ring
    calc
      Real.log (x ^ 7 + 1) ≤ Real.log (x ^ 8) := Real.log_le_log (by positivity) hpow
      _ = 8 * Real.log x := by rw [Real.log_pow]; norm_num
      _ ≤ 8 * x := by linarith
  have hlog7pos : 0 < Real.log (x ^ 7) := Real.log_pos (one_lt_pow₀ (by linarith) (by decide))
  have hpow : 40 * x ^ 3 ≤ x ^ 7 := by
    calc
      40 * x ^ 3 ≤ x * x ^ 3 := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = x ^ 4 := by ring
      _ ≤ x ^ 7 := pow_le_pow_right₀ hx1 (by decide)
  have hsmall : 8 * x < 6 * x ^ 3 := by
    have hxx : 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
    nlinarith [mul_le_mul_of_nonneg_right hxx hx0.le]
  have hqterm : (x ^ 2 + x) * Real.log (x ^ 7) ≤ 14 * x ^ 3 := by
    calc
      (x ^ 2 + x) * Real.log (x ^ 7) ≤ (2 * x ^ 2) * (7 * x) := by
        apply mul_le_mul (by nlinarith) hl7 hlog7pos.le (by positivity)
      _ = 14 * x ^ 3 := by ring
  have hbig : 14 * x ^ 3 < x ^ 7 * Real.log 2 - Real.log (x ^ 7 + 1) := by
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ x ^ 7 by positivity)]
  have hcount : (q ^ 2 + q : ℕ) < (q ^ 7).primeCounting := by
    rw [← Nat.cast_lt (α := ℝ)]
    push_cast
    change x ^ 2 + x < (Nat.primeCounting (q ^ 7) : ℝ)
    have bound := Chebyshev.pi_ge (q ^ 7)
    push_cast at bound
    exact ((lt_div_iff₀ hlog7pos).mpr (hqterm.trans_lt hbig)).trans_le bound
  have hi : q ^ 2 + (i : ℕ) < Nat.count Nat.Prime (q ^ 7 + 1) :=
    (Nat.add_lt_add_left i.isLt _).trans (by
      simpa only [Nat.primeCounting, Nat.primeCounting'] using hcount)
  exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hi)

/-- Positive integers at most `q¹⁵` which avoid every prime in the block. -/
def goodNumbers (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 15)).filter
    (fun u ↦ ∀ i : Fin q, ¬ blockPrime q i ∣ u)

@[simp] lemma mem_goodNumbers {q u : ℕ} :
    u ∈ goodNumbers q ↔
      1 ≤ u ∧ u ≤ q ^ 15 ∧ ∀ i : Fin q, ¬ blockPrime q i ∣ u := by
  simp [goodNumbers, and_assoc]

lemma goodNumbers_pos {q u : ℕ} (hu : u ∈ goodNumbers q) : 0 < u := by
  exact (mem_goodNumbers.mp hu).1

lemma goodNumbers_le {q u : ℕ} (hu : u ∈ goodNumbers q) : u ≤ q ^ 15 := by
  exact (mem_goodNumbers.mp hu).2.1

/-- Multiples of one selected prime in the ambient interval. -/
def blockMultiples (q : ℕ) (i : Fin q) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 15)).filter (fun u ↦ blockPrime q i ∣ u)

/-- The complement of `goodNumbers` inside the ambient interval. -/
def badNumbers (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 15)).filter
    (fun u ↦ ¬ ∀ i : Fin q, ¬ blockPrime q i ∣ u)

lemma blockMultiples_card_le (q : ℕ) (i : Fin q) :
    (blockMultiples q i).card ≤ q ^ 13 := by
  have heq : blockMultiples q i =
      (Finset.Ioc 0 (q ^ 15)).filter (fun u ↦ blockPrime q i ∣ u) := by
    ext u
    simp only [blockMultiples, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc]
    omega
  rw [heq, Nat.Ioc_filter_dvd_card_eq_div]
  apply Nat.div_le_of_le_mul
  calc
    q ^ 15 = q ^ 13 * q ^ 2 := by ring
    _ ≤ q ^ 13 * blockPrime q i :=
      Nat.mul_le_mul_left _ (sq_le_blockPrime q i)
    _ = blockPrime q i * q ^ 13 := by ac_rfl

lemma badNumbers_subset_biUnion (q : ℕ) :
    badNumbers q ⊆
      (Finset.univ : Finset (Fin q)).biUnion (blockMultiples q) := by
  intro u hu
  rw [Finset.mem_biUnion]
  rw [badNumbers, Finset.mem_filter] at hu
  push Not at hu
  obtain ⟨i, hi⟩ := hu.2
  exact ⟨i, Finset.mem_univ _, by
    exact Finset.mem_filter.mpr ⟨hu.1, hi⟩⟩

lemma badNumbers_card_le (q : ℕ) : (badNumbers q).card ≤ q ^ 14 := by
  calc
    (badNumbers q).card ≤
        ((Finset.univ : Finset (Fin q)).biUnion (blockMultiples q)).card :=
      Finset.card_le_card (badNumbers_subset_biUnion q)
    _ ≤ ∑ i : Fin q, (blockMultiples q i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, q ^ 13 :=
      Finset.sum_le_sum fun i _ ↦ blockMultiples_card_le q i
    _ = q ^ 14 := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      simpa using (pow_succ' q 13).symm

lemma goodNumbers_card_add_badNumbers_card (q : ℕ) :
    (goodNumbers q).card + (badNumbers q).card = q ^ 15 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 (q ^ 15))
    (p := fun u ↦ ∀ i : Fin q, ¬ blockPrime q i ∣ u)
  have hcard : (Finset.Icc 1 (q ^ 15)).card = q ^ 15 := by
    simp [Nat.card_Icc]
  simpa only [goodNumbers, badNumbers, hcard] using h

lemma goodNumbers_card_lower (q : ℕ) :
    q ^ 15 - q ^ 14 ≤ (goodNumbers q).card := by
  have hsum := goodNumbers_card_add_badNumbers_card q
  have hbad := badNumbers_card_le q
  omega

lemma goodNumbers_card_half {q : ℕ} (hq : 2 ≤ q) :
    q ^ 15 ≤ 2 * (goodNumbers q).card := by
  have hlower := goodNumbers_card_lower q
  have hpowers : 2 * q ^ 14 ≤ q ^ 15 := by
    calc
      2 * q ^ 14 ≤ q * q ^ 14 := Nat.mul_le_mul_right _ hq
      _ = q ^ 15 := by ring
  omega

lemma goodNumbers_card_upper (q : ℕ) :
    (goodNumbers q).card ≤ q ^ 15 := by
  exact (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc])

/- ## Vertices and their integer labels -/

/-- Sifted positive integers used as the first vertex coordinate. -/
abbrev Good (q : ℕ) := ↑(goodNumbers q)

/-- Ordered pairs of distinct block indices. -/
abbrev OrientedPair (q : ℕ) :=
  ↑((Finset.univ : Finset (Fin q)).offDiag)

/-- The vertices of the counterexample. -/
abbrev CounterVertex (q : ℕ) := Good q × OrientedPair q

/-- Product of all block primes except the one indexed by `i`. -/
def primeQuotient (q : ℕ) (i : Fin q) : ℕ :=
  ∏ k ∈ (Finset.univ : Finset (Fin q)).erase i, blockPrime q k

/-- Product of all block primes. -/
def primeProduct (q : ℕ) : ℕ :=
  ∏ k : Fin q, blockPrime q k

lemma blockPrime_mul_primeQuotient (q : ℕ) (i : Fin q) :
    blockPrime q i * primeQuotient q i = primeProduct q := by
  exact Finset.mul_prod_erase (Finset.univ : Finset (Fin q))
    (blockPrime q) (Finset.mem_univ i)

lemma primeQuotient_pos (q : ℕ) (i : Fin q) : 0 < primeQuotient q i := by
  exact Finset.prod_pos fun k _ ↦ (blockPrime_prime q k).pos

lemma blockPrime_dvd_primeQuotient {q : ℕ} {i k : Fin q} (hki : k ≠ i) :
    blockPrime q k ∣ primeQuotient q i := by
  exact Finset.dvd_prod_of_mem (blockPrime q) (by simp [hki])

lemma blockPrime_not_dvd_primeQuotient (q : ℕ) (i : Fin q) :
    ¬ blockPrime q i ∣ primeQuotient q i := by
  apply (blockPrime_prime q i).prime.not_dvd_finsetProd
  intro k hk hdvd
  have hik : i = k := (blockPrime_injective q)
    ((Nat.prime_dvd_prime_iff_eq (blockPrime_prime q i)
      (blockPrime_prime q k)).mp hdvd)
  exact (Finset.mem_erase.mp hk).1 hik.symm

/-- The label `u p_j (D / p_i)`, written without natural-number division. -/
def counterLabel (q : ℕ) (x : CounterVertex q) : ℕ :=
  x.1.1 * blockPrime q x.2.1.2 * primeQuotient q x.2.1.1

lemma oriented_ne (q : ℕ) (x : CounterVertex q) : x.2.1.1 ≠ x.2.1.2 := by
  exact (Finset.mem_offDiag.mp x.2.2).2.2

lemma counterLabel_pos (q : ℕ) (x : CounterVertex q) :
    0 < counterLabel q x := by
  exact mul_pos (mul_pos (goodNumbers_pos x.1.2)
    (blockPrime_prime q x.2.1.2).pos) (primeQuotient_pos q x.2.1.1)

lemma index_prime_not_dvd_counterLabel (q : ℕ) (x : CounterVertex q) :
    ¬ blockPrime q x.2.1.1 ∣ counterLabel q x := by
  intro hdvd
  rcases (blockPrime_prime q x.2.1.1).dvd_mul.mp hdvd with hdvd | hdvd
  · rcases (blockPrime_prime q x.2.1.1).dvd_mul.mp hdvd with hu | hp
    · exact (mem_goodNumbers.mp x.1.2).2.2 x.2.1.1 hu
    · exact (oriented_ne q x)
        ((blockPrime_injective q)
          ((Nat.prime_dvd_prime_iff_eq (blockPrime_prime q x.2.1.1)
            (blockPrime_prime q x.2.1.2)).mp hp))
  · exact blockPrime_not_dvd_primeQuotient q x.2.1.1 hdvd

lemma blockPrime_dvd_counterLabel_of_ne (q : ℕ) (x : CounterVertex q)
    (k : Fin q) (hki : k ≠ x.2.1.1) :
    blockPrime q k ∣ counterLabel q x := by
  exact dvd_mul_of_dvd_right (blockPrime_dvd_primeQuotient hki)
    (x.1.1 * blockPrime q x.2.1.2)

lemma counterLabel_injective (q : ℕ) : Function.Injective (counterLabel q) := by
  intro x y hxy
  have hi : x.2.1.1 = y.2.1.1 := by
    by_contra hne
    have hdvd := blockPrime_dvd_counterLabel_of_ne q y x.2.1.1 hne
    rw [← hxy] at hdvd
    exact index_prime_not_dvd_counterLabel q x hdvd
  have hcore :
      x.1.1 * blockPrime q x.2.1.2 =
        y.1.1 * blockPrime q y.2.1.2 := by
    apply Nat.mul_right_cancel (m := primeQuotient q x.2.1.1)
      (primeQuotient_pos q x.2.1.1)
    simpa only [counterLabel, hi] using hxy
  have hjdvd : blockPrime q x.2.1.2 ∣
      y.1.1 * blockPrime q y.2.1.2 := by
    rw [← hcore]
    exact ⟨x.1.1, by ac_rfl⟩
  have hj : x.2.1.2 = y.2.1.2 := by
    rcases (blockPrime_prime q x.2.1.2).dvd_mul.mp hjdvd with hu | hp
    · exact False.elim ((mem_goodNumbers.mp y.1.2).2.2 x.2.1.2 hu)
    · exact (blockPrime_injective q)
        ((Nat.prime_dvd_prime_iff_eq (blockPrime_prime q x.2.1.2)
          (blockPrime_prime q y.2.1.2)).mp hp)
  have hu : x.1.1 = y.1.1 := by
    apply Nat.mul_right_cancel (m := blockPrime q x.2.1.2)
      (blockPrime_prime q x.2.1.2).pos
    simpa only [hj] using hcore
  apply Prod.ext
  · exact Subtype.ext hu
  · apply Subtype.ext
    exact Prod.ext hi hj

/-- The label embedding used in the statement of Problem 808. -/
def counterEmbedding (q : ℕ) : CounterVertex q ↪ ℕ :=
  ⟨counterLabel q, counterLabel_injective q⟩

lemma counterVertex_card (q : ℕ) :
    Fintype.card (CounterVertex q) =
      (goodNumbers q).card * (q * q - q) := by
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.offDiag_card,
    Finset.card_univ, Fintype.card_fin]

lemma counterVertex_card_upper (q : ℕ) :
    Fintype.card (CounterVertex q) ≤ q ^ 17 := by
  rw [counterVertex_card]
  calc
    (goodNumbers q).card * (q * q - q) ≤ q ^ 15 * q ^ 2 := by
      apply Nat.mul_le_mul (goodNumbers_card_upper q)
      simp [pow_two]
    _ = q ^ 17 := by ring

lemma orderedPair_card_half {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 ≤ 2 * (q * q - q) := by
  have hlin : q ≤ 2 * (q - 1) := by omega
  have hfac : q * q - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib]
    simp
  calc
    q ^ 2 = q * q := by ring
    _ ≤ q * (2 * (q - 1)) := Nat.mul_le_mul_left q hlin
    _ = 2 * (q * q - q) := by rw [hfac]; ring

lemma counterVertex_card_quarter {q : ℕ} (hq : 2 ≤ q) :
    q ^ 17 ≤ 4 * Fintype.card (CounterVertex q) := by
  rw [counterVertex_card]
  calc
    q ^ 17 = q ^ 15 * q ^ 2 := by ring
    _ ≤ (2 * (goodNumbers q).card) * (2 * (q * q - q)) :=
      Nat.mul_le_mul (goodNumbers_card_half hq) (orderedPair_card_half hq)
    _ = 4 * ((goodNumbers q).card * (q * q - q)) := by ring

/- ## The swap graph -/

/-- Two vertices are adjacent when their ordered prime indices are reversed. -/
def counterGraph (q : ℕ) : SimpleGraph (CounterVertex q) where
  Adj x y := x.2.1.1 = y.2.1.2 ∧ x.2.1.2 = y.2.1.1
  symm := ⟨by
      intro x y h
      exact ⟨h.2.symm, h.1.symm⟩⟩
  loopless := ⟨by
      intro x h
      exact oriented_ne q x h.1⟩

open Classical in
instance counterGraph_decidableAdj (q : ℕ) :
    DecidableRel (counterGraph q).Adj := fun _ _ ↦ inferInstance

@[simp] lemma counterGraph_adj {q : ℕ} {x y : CounterVertex q} :
    (counterGraph q).Adj x y ↔
      x.2.1.1 = y.2.1.2 ∧ x.2.1.2 = y.2.1.1 := Iff.rfl

/-- The unique neighbor of `x` with prescribed sifted coordinate `u`. -/
def swapNeighbor (q : ℕ) (x : CounterVertex q) (u : Good q) :
    CounterVertex q :=
  ⟨u, ⟨(x.2.1.2, x.2.1.1), Finset.mem_offDiag.mpr
    ⟨Finset.mem_univ _, Finset.mem_univ _, (oriented_ne q x).symm⟩⟩⟩

lemma swapNeighbor_injective (q : ℕ) (x : CounterVertex q) :
    Function.Injective (swapNeighbor q x) := by
  intro u v huv
  exact congrArg Prod.fst huv

def swapNeighborEmbedding (q : ℕ) (x : CounterVertex q) :
    Good q ↪ CounterVertex q :=
  ⟨swapNeighbor q x, swapNeighbor_injective q x⟩

lemma neighborFinset_counterGraph (q : ℕ) (x : CounterVertex q) :
    (counterGraph q).neighborFinset x =
      (Finset.univ : Finset (Good q)).map (swapNeighborEmbedding q x) := by
  ext y
  constructor
  · intro hy
    have hadj : (counterGraph q).Adj x y := by simpa using hy
    apply Finset.mem_map.mpr
    refine ⟨y.1, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Prod.ext hadj.2 hadj.1
  · intro hy
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hy
    apply ((counterGraph q).mem_neighborFinset x _).mpr
    exact ⟨rfl, rfl⟩

lemma counterGraph_degree (q : ℕ) (x : CounterVertex q) :
    (counterGraph q).degree x = (goodNumbers q).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_counterGraph, Finset.card_map]
  simp

lemma counterGraph_twice_edges (q : ℕ) :
    2 * (counterGraph q).edgeFinset.card =
      Fintype.card (CounterVertex q) * (goodNumbers q).card := by
  rw [← (counterGraph q).sum_degrees_eq_twice_card_edges]
  simp only [counterGraph_degree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rfl

lemma counterGraph_many_edges {q : ℕ} (hq : 2 ≤ q) :
    q ^ 32 ≤ 16 * (counterGraph q).edgeFinset.card := by
  calc
    q ^ 32 = q ^ 17 * q ^ 15 := by ring
    _ ≤ (4 * Fintype.card (CounterVertex q)) *
        (2 * (goodNumbers q).card) :=
      Nat.mul_le_mul (counterVertex_card_quarter hq) (goodNumbers_card_half hq)
    _ = 8 * (Fintype.card (CounterVertex q) *
        (goodNumbers q).card) := by ring
    _ = 8 * (2 * (counterGraph q).edgeFinset.card) := by
      rw [counterGraph_twice_edges]
    _ = 16 * (counterGraph q).edgeFinset.card := by ring

/- ## The two restricted image bounds -/

/-- Product of all block primes except `p_i` and `p_j`. -/
def primeRest (q : ℕ) (i j : Fin q) : ℕ :=
  ∏ k ∈ ((Finset.univ : Finset (Fin q)).erase i).erase j,
    blockPrime q k

lemma primeRest_symm (q : ℕ) (i j : Fin q) :
    primeRest q i j = primeRest q j i := by
  unfold primeRest
  apply Finset.prod_congr
  · ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  · intro k _
    rfl

lemma primeQuotient_eq_mul_rest {q : ℕ} {i j : Fin q} (hij : i ≠ j) :
    primeQuotient q i = blockPrime q j * primeRest q i j := by
  symm
  exact Finset.mul_prod_erase
    ((Finset.univ : Finset (Fin q)).erase i) (blockPrime q)
    (by simp [hij.symm])

lemma counterLabel_mul_of_adj {q : ℕ} {x y : CounterVertex q}
    (hxy : (counterGraph q).Adj x y) :
    counterLabel q x * counterLabel q y =
      (x.1.1 * y.1.1) * primeProduct q ^ 2 := by
  have hxi := blockPrime_mul_primeQuotient q x.2.1.1
  have hxj := blockPrime_mul_primeQuotient q x.2.1.2
  rw [counterLabel, counterLabel, ← hxy.1, ← hxy.2]
  calc
    (x.1.1 * blockPrime q x.2.1.2 * primeQuotient q x.2.1.1) *
        (y.1.1 * blockPrime q x.2.1.1 * primeQuotient q x.2.1.2) =
      (x.1.1 * y.1.1) *
        (blockPrime q x.2.1.1 * primeQuotient q x.2.1.1) *
        (blockPrime q x.2.1.2 * primeQuotient q x.2.1.2) := by ring
    _ = (x.1.1 * y.1.1) * primeProduct q ^ 2 := by
      rw [hxi, hxj]
      ring

lemma counterLabel_add_of_adj {q : ℕ} {x y : CounterVertex q}
    (hxy : (counterGraph q).Adj x y) :
    counterLabel q x + counterLabel q y =
      primeRest q x.2.1.1 x.2.1.2 *
        (x.1.1 * blockPrime q x.2.1.2 ^ 2 +
          y.1.1 * blockPrime q x.2.1.1 ^ 2) := by
  have hne := oriented_ne q x
  have hQi := primeQuotient_eq_mul_rest (q := q) hne
  have hQj := primeQuotient_eq_mul_rest (q := q) hne.symm
  rw [counterLabel, counterLabel, ← hxy.1, ← hxy.2, hQi, hQj,
    ← primeRest_symm q x.2.1.1 x.2.1.2]
  ring

/-- A one-dimensional target containing every restricted product. -/
def productTargets (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 30)).image
    (fun t ↦ t * primeProduct q ^ 2)

lemma edgeProducts_subset_productTargets (q : ℕ) :
    edgeProducts (counterEmbedding q) (counterGraph q) ⊆ productTargets q := by
  intro r hr
  rw [edgeProducts, mem_edgeValues_iff] at hr
  obtain ⟨x, y, hxy, rfl⟩ := hr
  change counterLabel q x * counterLabel q y ∈ productTargets q
  rw [counterLabel_mul_of_adj hxy]
  apply Finset.mem_image.mpr
  refine ⟨x.1.1 * y.1.1, ?_, rfl⟩
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (goodNumbers_pos x.1.2)
    (goodNumbers_pos y.1.2), by
      calc
        x.1.1 * y.1.1 ≤ q ^ 15 * q ^ 15 :=
          Nat.mul_le_mul (goodNumbers_le x.1.2) (goodNumbers_le y.1.2)
        _ = q ^ 30 := by ring⟩

lemma productTargets_card_le (q : ℕ) :
    (productTargets q).card ≤ q ^ 30 := by
  calc
    (productTargets q).card ≤ (Finset.Icc 1 (q ^ 30)).card :=
      Finset.card_image_le
    _ ≤ q ^ 30 := by simp [Nat.card_Icc]

lemma counter_edgeProducts_card_le (q : ℕ) :
    (edgeProducts (counterEmbedding q) (counterGraph q)).card ≤ q ^ 30 :=
  (Finset.card_le_card (edgeProducts_subset_productTargets q)).trans
    (productTargets_card_le q)

/-- A target containing every restricted sum, indexed by its two omitted
primes and by its bounded numerator. -/
def sumTargets (q : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin q)).biUnion fun i ↦
    (Finset.univ : Finset (Fin q)).biUnion fun j ↦
      (Finset.Icc 1 (2 * q ^ 29)).image (fun t ↦ primeRest q i j * t)

lemma edgeSums_subset_sumTargets (q : ℕ)
    (hp : ∀ i : Fin q, blockPrime q i ≤ q ^ 7) :
    edgeSums (counterEmbedding q) (counterGraph q) ⊆ sumTargets q := by
  intro r hr
  rw [edgeSums, mem_edgeValues_iff] at hr
  obtain ⟨x, y, hxy, rfl⟩ := hr
  change counterLabel q x + counterLabel q y ∈ sumTargets q
  rw [counterLabel_add_of_adj hxy]
  rw [sumTargets, Finset.mem_biUnion]
  refine ⟨x.2.1.1, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨x.2.1.2, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  let t := x.1.1 * blockPrime q x.2.1.2 ^ 2 +
    y.1.1 * blockPrime q x.2.1.1 ^ 2
  refine ⟨t, ?_, rfl⟩
  apply Finset.mem_Icc.mpr
  constructor
  · dsimp [t]
    have hxpos : 0 < x.1.1 := goodNumbers_pos x.1.2
    have hppos : 0 < blockPrime q x.2.1.2 :=
      (blockPrime_prime q x.2.1.2).pos
    have hpos : 0 < x.1.1 * blockPrime q x.2.1.2 ^ 2 := by
      exact Nat.mul_pos hxpos (pow_pos hppos 2)
    omega
  · dsimp [t]
    calc
      x.1.1 * blockPrime q x.2.1.2 ^ 2 +
          y.1.1 * blockPrime q x.2.1.1 ^ 2 ≤
        q ^ 15 * (q ^ 7) ^ 2 + q ^ 15 * (q ^ 7) ^ 2 :=
          Nat.add_le_add
            (Nat.mul_le_mul (goodNumbers_le x.1.2)
              (pow_le_pow_left' (hp x.2.1.2) 2))
            (Nat.mul_le_mul (goodNumbers_le y.1.2)
              (pow_le_pow_left' (hp x.2.1.1) 2))
      _ = 2 * q ^ 29 := by ring

lemma sumTargets_card_le (q : ℕ) :
    (sumTargets q).card ≤ 2 * q ^ 31 := by
  calc
    (sumTargets q).card ≤
        ∑ _i : Fin q, ∑ _j : Fin q,
          ((Finset.Icc 1 (2 * q ^ 29)).image
            (fun t ↦ primeRest q _i _j * t)).card := by
      exact Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun i _ ↦ Finset.card_biUnion_le)
    _ ≤ ∑ _i : Fin q, ∑ _j : Fin q, 2 * q ^ 29 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le.trans (by simp [Nat.card_Icc])
    _ = 2 * q ^ 31 := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hpow : q ^ 2 * q ^ 29 = q ^ 31 := by
        rw [← pow_add]
      calc
        q * (q * (2 * q ^ 29)) = 2 * (q ^ 2 * q ^ 29) := by ring
        _ = 2 * q ^ 31 := by rw [hpow]

lemma counter_edgeSums_card_le (q : ℕ)
    (hp : ∀ i : Fin q, blockPrime q i ≤ q ^ 7) :
    (edgeSums (counterEmbedding q) (counterGraph q)).card ≤ 2 * q ^ 31 :=
  (Finset.card_le_card (edgeSums_subset_sumTargets q hp)).trans
    (sumTargets_card_le q)

/- ## Real-power comparisons and the disproof -/

/-- A fixed multiple of a smaller real power of a natural parameter is
eventually at most a larger power. -/
lemma eventually_const_mul_rpow_le_rpow_nat
    {C a b : ℝ} (_hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ a ≤ (q : ℝ) ^ b := by
  have htop : Tendsto (fun q : ℕ ↦ (q : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htop (eventually_ge_atTop C), eventually_ge_atTop (1 : ℕ)]
    with q hqC hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (zero_lt_one.trans_le hq)
  calc
    C * (q : ℝ) ^ a ≤ (q : ℝ) ^ (b - a) * (q : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hqC (Real.rpow_nonneg hqpos.le _)
    _ = (q : ℝ) ^ b := by
      rw [← Real.rpow_add hqpos]
      congr 1
      ring

lemma pow_rpow_eq_rpow_mul (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (a : ℝ) :
    (x ^ n) ^ a = x ^ ((n : ℝ) * a) := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_mul hx (n : ℝ) a).symm

lemma counterGraph_edge_threshold_eventually :
    ∀ᶠ q : ℕ in atTop,
      (Fintype.card (CounterVertex q) : ℝ) ^ ((63 : ℝ) / 34) ≤
        ((counterGraph q).edgeFinset.card : ℝ) := by
  have habsorb : ∀ᶠ q : ℕ in atTop,
      16 * (q : ℝ) ^ ((63 : ℝ) / 2) ≤ (q : ℝ) ^ (32 : ℝ) :=
    eventually_const_mul_rpow_le_rpow_nat (by norm_num)
      (by norm_num : (63 : ℝ) / 2 < 32)
  filter_upwards [habsorb, eventually_ge_atTop 2] with q hab hq
  let n := Fintype.card (CounterVertex q)
  let m := (counterGraph q).edgeFinset.card
  have hn : (n : ℝ) ≤ (q : ℝ) ^ 17 := by
    exact_mod_cast counterVertex_card_upper q
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hmono : (n : ℝ) ^ ((63 : ℝ) / 34) ≤
      ((q : ℝ) ^ 17) ^ ((63 : ℝ) / 34) :=
    Real.rpow_le_rpow hnnonneg hn (by norm_num)
  have hrexp : ((q : ℝ) ^ 17) ^ ((63 : ℝ) / 34) =
      (q : ℝ) ^ ((63 : ℝ) / 2) := by
    rw [pow_rpow_eq_rpow_mul _ hqnonneg]
    congr 1
    norm_num
  have hedgeNat := counterGraph_many_edges hq
  have hedge : ((q ^ 32 : ℕ) : ℝ) ≤ 16 * (m : ℝ) := by
    exact_mod_cast hedgeNat
  have hpowEq : (q : ℝ) ^ (32 : ℝ) = ((q ^ 32 : ℕ) : ℝ) := by
    norm_num [Real.rpow_natCast]
  have hqm : (q : ℝ) ^ ((63 : ℝ) / 2) ≤ (m : ℝ) := by
    linarith [hab, hedge]
  exact hmono.trans_eq hrexp |>.trans hqm

lemma counterGraph_output_small_eventually :
    ∀ᶠ q : ℕ in atTop,
      max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) <
        (Fintype.card (CounterVertex q) : ℝ) ^ ((125 : ℝ) / 68) := by
  let b : ℝ := 125 / 68
  let scale : ℝ := (4 : ℝ) ^ b
  have hscale : 0 < scale := Real.rpow_pos_of_pos (by norm_num) _
  have habsorb : ∀ᶠ q : ℕ in atTop,
      (3 * scale) * (q : ℝ) ^ (31 : ℝ) ≤
        (q : ℝ) ^ ((125 : ℝ) / 4) :=
    eventually_const_mul_rpow_le_rpow_nat
      (mul_nonneg (by norm_num) hscale.le)
      (by norm_num : (31 : ℝ) < 125 / 4)
  filter_upwards [habsorb, blockPrime_le_seventh_eventually,
    eventually_ge_atTop 2] with q hab hp hq
  let n := Fintype.card (CounterVertex q)
  have hsumNat := counter_edgeSums_card_le q hp
  have hprodNat := counter_edgeProducts_card_le q
  have hprodCoarse : (edgeProducts (counterEmbedding q)
      (counterGraph q)).card ≤ 2 * q ^ 31 := by
    calc
      (edgeProducts (counterEmbedding q) (counterGraph q)).card ≤ q ^ 30 :=
        hprodNat
      _ ≤ 2 * q ^ 31 := by
        have hpows : q ^ 30 ≤ q ^ 31 :=
          pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
        omega
  have hout : max ((edgeSums (counterEmbedding q)
      (counterGraph q)).card : ℝ)
      ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) ≤
      2 * (q : ℝ) ^ (31 : ℝ) := by
    have houtNat : max (edgeSums (counterEmbedding q)
        (counterGraph q)).card
        (edgeProducts (counterEmbedding q) (counterGraph q)).card ≤
        2 * q ^ 31 := max_le hsumNat hprodCoarse
    have houtCast :
        max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) ≤
          ((2 * q ^ 31 : ℕ) : ℝ) := by
      exact_mod_cast houtNat
    calc
      max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) ≤
          ((2 * q ^ 31 : ℕ) : ℝ) := houtCast
      _ = 2 * (q : ℝ) ^ (31 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hnNat := counterVertex_card_quarter hq
  have hn : (q : ℝ) ^ 17 ≤ 4 * (n : ℝ) := by
    exact_mod_cast hnNat
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hbase : (q : ℝ) ^ ((125 : ℝ) / 4) ≤
      scale * (n : ℝ) ^ b := by
    calc
      (q : ℝ) ^ ((125 : ℝ) / 4) =
          ((q : ℝ) ^ 17) ^ b := by
        rw [pow_rpow_eq_rpow_mul _ hqnonneg]
        dsimp [b]
        congr 1
        norm_num
      _ ≤ (4 * (n : ℝ)) ^ b :=
        Real.rpow_le_rpow (by positivity) hn (by dsimp [b]; norm_num)
      _ = scale * (n : ℝ) ^ b := by
        rw [Real.mul_rpow (by norm_num) hnnonneg]
  have hscaled : scale * (3 * (q : ℝ) ^ (31 : ℝ)) ≤
      scale * (n : ℝ) ^ b := by
    calc
      scale * (3 * (q : ℝ) ^ (31 : ℝ)) =
          (3 * scale) * (q : ℝ) ^ (31 : ℝ) := by ring
      _ ≤ (q : ℝ) ^ ((125 : ℝ) / 4) := hab
      _ ≤ scale * (n : ℝ) ^ b := hbase
  have hqpowpos : 0 < (q : ℝ) ^ (31 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < q by omega)) _
  have hstrictScaled :
      scale * (2 * (q : ℝ) ^ (31 : ℝ)) <
        scale * (3 * (q : ℝ) ^ (31 : ℝ)) := by
    exact mul_lt_mul_of_pos_left (by linarith) hscale
  have hstrict : 2 * (q : ℝ) ^ (31 : ℝ) < (n : ℝ) ^ b :=
    lt_of_mul_lt_mul_left (hstrictScaled.trans_le hscaled) hscale.le
  exact hout.trans_lt (by simpa only [b, n] using hstrict)

end OMA.Erdos808Port

open OMA.Erdos808Port Erdos808 Filter in
theorem OMA.solution : type_of% @Erdos808.erdos_808.variants.positive := by
  intro hstrong
  obtain ⟨n₀, hstrong⟩ := hstrong ((29 : ℝ) / 34) (by norm_num)
    ((1 : ℝ) / 68) (by norm_num)
  have hcounter : ∀ᶠ q : ℕ in atTop,
      (∀ i : Fin q, blockPrime q i ≤ q ^ 7) ∧
      (Fintype.card (CounterVertex q) : ℝ) ^ ((63 : ℝ) / 34) ≤
        ((counterGraph q).edgeFinset.card : ℝ) ∧
      max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) <
        (Fintype.card (CounterVertex q) : ℝ) ^ ((125 : ℝ) / 68) ∧
      max (4 * n₀) 2 ≤ q := by
    filter_upwards [blockPrime_le_seventh_eventually,
      counterGraph_edge_threshold_eventually,
      counterGraph_output_small_eventually,
      eventually_ge_atTop (max (4 * n₀) 2)] with q hp hedge hout hq
    exact ⟨hp, hedge, hout, hq⟩
  obtain ⟨q, hp, hedge, hout, hq⟩ := hcounter.exists
  have hq2 : 2 ≤ q := (le_max_right (4 * n₀) 2).trans hq
  have hqlarge : 4 * n₀ ≤ q := (le_max_left (4 * n₀) 2).trans hq
  have hqpow : q ≤ q ^ 17 := le_self_pow (by omega) (by norm_num)
  have hnlarge : n₀ ≤ Fintype.card (CounterVertex q) := by
    have hv := counterVertex_card_quarter hq2
    omega
  have hclaimed := hstrong (CounterVertex q) (counterEmbedding q)
    (counterLabel_pos q) (counterGraph q) hnlarge (by simpa only [show (1 : ℝ) + 29 / 34 = 63 / 34 by norm_num]
      using hedge)
  have hclaimed' :
      (Fintype.card (CounterVertex q) : ℝ) ^ ((125 : ℝ) / 68) ≤
        max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) := by
    simpa only [show (1 : ℝ) + 29 / 34 - 1 / 68 = 125 / 68 by norm_num]
      using hclaimed
  exact (not_lt_of_ge hclaimed') hout
