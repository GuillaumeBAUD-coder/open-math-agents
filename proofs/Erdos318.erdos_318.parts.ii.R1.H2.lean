import OMAReductions.R_Erdos318_erdos_318_parts_ii_R1

/-!
The reciprocal-tail estimates and factorization bookkeeping adapt Collin Yuanjie Ren's
Apache-2.0 Lean formalization of Daniel Larsen's proof, at commit
`8c4f1b2b4b9d1e7fb872340b7ae88dde5e862097` of `CollinYuanjieRen/awards`.
The square cover and uniform cutoff here follow this reduction's definitions.
-/

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

open Finset

namespace OMA.ReciprocalSquareTail

/-- A reciprocal square is bounded by the adjacent telescoping difference. -/
private theorem recip_sq_le_telescope (x : ℚ) (hx : 2 ≤ x) :
    1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hid : 1 / (x - 1) - 1 / x = 1 / ((x - 1) * x) := by
    field_simp
    ring
  rw [hid]
  apply one_div_le_one_div_of_le (mul_pos hx1 hx0)
  nlinarith

/-- A reciprocal fourth power is bounded by a cubic telescoping difference. -/
private theorem recip_fourth_le_telescope (x : ℚ) (hx : 2 ≤ x) :
    1 / x ^ 4 ≤ 1 / (x - 1) ^ 3 - 1 / x ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  rw [le_sub_iff_add_le]
  have hid : 1 / x ^ 4 + 1 / x ^ 3 = (1 + x) / x ^ 4 := by
    field_simp
  rw [hid]
  apply (div_le_div_iff₀ (pow_pos hx0 4) (pow_pos hx1 3)).2
  have hprod : 0 ≤ x * (x - 1) * (x + 1) := by positivity
  nlinarith

/-- A finite reciprocal-square tail is bounded by its first telescoping term. -/
theorem sum_recip_sq_tail (F : Finset ℕ) (K : ℕ)
    (hK : 2 ≤ K) (hF : ∀ n ∈ F, K ≤ n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 1 / ((K : ℚ) - 1) := by
  by_cases hFempty : F = ∅
  · simp [hFempty]
    omega
  have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
  let M := F.sup id
  have hKM : K ≤ M := by
    calc
      K ≤ hFne.choose := hF hFne.choose hFne.choose_spec
      _ ≤ F.sup id := Finset.le_sup (f := id) hFne.choose_spec
      _ = M := rfl
  have hsub : F ⊆ Finset.Icc K M := by
    intro n hn
    have hnM : n ≤ M := by
      simpa [M] using Finset.le_sup (f := id) hn
    exact Finset.mem_Icc.mpr ⟨hF n hn, hnM⟩
  have henlarge :
      (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ n ∈ Finset.Icc K M, (1 : ℚ) / (n : ℚ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    have hn0 : 0 < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) (Finset.mem_Icc.mp hn).1)
    positivity
  have hsquare :
      (∑ n ∈ Finset.Icc K M, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ n ∈ Finset.Icc K M,
          (1 / ((n : ℚ) - 1) - 1 / (n : ℚ)) := by
    apply Finset.sum_le_sum
    intro n hn
    apply recip_sq_le_telescope
    exact_mod_cast hK.trans (Finset.mem_Icc.mp hn).1
  have htel : ∀ L : ℕ, K ≤ L →
      (∑ n ∈ Finset.Icc K L,
        (1 / ((n : ℚ) - 1) - 1 / (n : ℚ))) =
        1 / ((K : ℚ) - 1) - 1 / (L : ℚ) := by
    intro L hKL
    induction L, hKL using Nat.le_induction with
    | base => simp
    | succ L hKL ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hKL), ih]
      push_cast
      ring
  have hM0 : 0 < (M : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) hKM)
  calc
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ n ∈ Finset.Icc K M, (1 : ℚ) / (n : ℚ) ^ 2 := henlarge
    _ ≤ ∑ n ∈ Finset.Icc K M,
        (1 / ((n : ℚ) - 1) - 1 / (n : ℚ)) := hsquare
    _ = 1 / ((K : ℚ) - 1) - 1 / (M : ℚ) := htel M hKM
    _ ≤ 1 / ((K : ℚ) - 1) := by
      linarith [one_div_pos.mpr hM0]

theorem sum_recip_sq_le_two (F : Finset ℕ)
    (hF : ∀ n ∈ F, 0 < n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 2 := by
  by_cases h1 : 1 ∈ F
  · have htail := sum_recip_sq_tail (F.erase 1) 2 (by omega) (by
      intro n hn
      have hnF := Finset.mem_of_mem_erase hn
      have hn1 := Finset.ne_of_mem_erase hn
      have hn0 := hF n hnF
      omega)
    have hdecomp := Finset.add_sum_erase F
      (fun n ↦ (1 : ℚ) / (n : ℚ) ^ 2) h1
    norm_num at hdecomp htail ⊢
    linarith
  · have htail := sum_recip_sq_tail F 2 (by omega) (by
      intro n hn
      have hn0 := hF n hn
      have hn1 : n ≠ 1 := by
        intro heq
        apply h1
        simpa [heq] using hn
      omega)
    norm_num at htail ⊢
    linarith

theorem sum_recip_fourth_tail (P : Finset ℕ) (N : ℕ)
    (hN : 1 ≤ N) (hP : ∀ p ∈ P, N < p) :
    (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4) ≤ 1 / (N : ℚ) ^ 3 := by
  by_cases hPempty : P = ∅
  · simp [hPempty]
  have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPempty
  let M := P.sup id
  have hNM : N + 1 ≤ M := by
    calc
      N + 1 ≤ hPne.choose := by
        exact Nat.succ_le_iff.mpr (hP hPne.choose hPne.choose_spec)
      _ ≤ P.sup id := Finset.le_sup (f := id) hPne.choose_spec
      _ = M := rfl
  have hsub : P ⊆ Finset.Icc (N + 1) M := by
    intro p hp
    have hpM : p ≤ M := by
      simpa [M] using Finset.le_sup (f := id) hp
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_iff.mpr (hP p hp), hpM⟩
  have henlarge :
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4) ≤
        ∑ p ∈ Finset.Icc (N + 1) M, (1 : ℚ) / (p : ℚ) ^ 4 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp0 : 0 < (p : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N + 1) (Finset.mem_Icc.mp hp).1)
    positivity
  have hfourth :
      (∑ p ∈ Finset.Icc (N + 1) M, (1 : ℚ) / (p : ℚ) ^ 4) ≤
        ∑ p ∈ Finset.Icc (N + 1) M,
          (1 / ((p : ℚ) - 1) ^ 3 - 1 / (p : ℚ) ^ 3) := by
    apply Finset.sum_le_sum
    intro p hp
    apply recip_fourth_le_telescope
    have hplow := (Finset.mem_Icc.mp hp).1
    have hp2 : 2 ≤ p := by
      omega
    exact_mod_cast hp2
  have htel : ∀ L : ℕ, N + 1 ≤ L →
      (∑ p ∈ Finset.Icc (N + 1) L,
        (1 / ((p : ℚ) - 1) ^ 3 - 1 / (p : ℚ) ^ 3)) =
        1 / (N : ℚ) ^ 3 - 1 / (L : ℚ) ^ 3 := by
    intro L hNL
    induction L, hNL using Nat.le_induction with
    | base =>
      push_cast
      simp
    | succ L hNL ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hNL), ih]
      push_cast
      ring
  have hM0 : 0 < (M : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N + 1) hNM)
  calc
    (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4) ≤
        ∑ p ∈ Finset.Icc (N + 1) M, (1 : ℚ) / (p : ℚ) ^ 4 := henlarge
    _ ≤ ∑ p ∈ Finset.Icc (N + 1) M,
        (1 / ((p : ℚ) - 1) ^ 3 - 1 / (p : ℚ) ^ 3) := hfourth
    _ = 1 / (N : ℚ) ^ 3 - 1 / (M : ℚ) ^ 3 := htel M hNM
    _ ≤ 1 / (N : ℚ) ^ 3 := by
      linarith [one_div_pos.mpr (pow_pos hM0 3)]

/-- The part of `n` supported on prime factors at most `N`. -/
def lowPart (N n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≤ N), p ^ n.factorization p

/-- The prime factors of `n` that are larger than `N`. -/
def highSupport (N n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => N < p)

/-- Splitting the factorization at `N` reconstructs `n` when high exponents are at most one. -/
theorem lowPart_mul_highSupport (N n : ℕ) (hn : 0 < n)
    (hlarge : ∀ p ∈ n.primeFactors, N < p → n.factorization p ≤ 1) :
    lowPart N n * (highSupport N n).prod id = n := by
  have hall :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
      Nat.prod_factorization_pow_eq_self hn.ne'
  have hhigh :
      (highSupport N n).prod id =
        ∏ p ∈ n.primeFactors.filter (fun p => N < p),
          p ^ n.factorization p := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpF : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
    have hpgt : N < p := (Finset.mem_filter.mp hp).2
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpF
    have hppos : 0 < n.factorization p :=
      hpprime.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hpF)
    have hpleone : n.factorization p ≤ 1 := hlarge p hpF hpgt
    have hpone : n.factorization p = 1 := by
      omega
    simp [hpone]
  rw [lowPart, hhigh]
  calc
    (∏ p ∈ n.primeFactors.filter (fun p => p ≤ N), p ^ n.factorization p) *
        ∏ p ∈ n.primeFactors.filter (fun p => N < p), p ^ n.factorization p =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      simpa only [not_le] using Finset.prod_filter_mul_prod_filter_not
        n.primeFactors (fun p => p ≤ N) (fun p => p ^ n.factorization p)
    _ = n := hall

/-- The low part divides the original number. -/
theorem lowPart_dvd (N n : ℕ) (hn : 0 < n) : lowPart N n ∣ n := by
  have hprod :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
      Nat.prod_factorization_pow_eq_self hn.ne'
  have hdvd :
      (∏ p ∈ n.primeFactors.filter (fun p => p ≤ N), p ^ n.factorization p) ∣
        ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  unfold lowPart
  rwa [hprod] at hdvd

theorem sum_recip_sq_multiples_sq (F : Finset ℕ) (p : ℕ)
    (hp : 0 < p) (hF : ∀ n ∈ F, 0 < n ∧ p ^ 2 ∣ n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 2 / (p : ℚ) ^ 4 := by
  have hp2 : 0 < p ^ 2 := pow_pos hp _
  have hrec : ∀ n ∈ F, n = p ^ 2 * (n / p ^ 2) := by
    intro n hn
    exact (Nat.mul_div_cancel' (hF n hn).2).symm
  have hquot : ∀ n ∈ F, 0 < n / p ^ 2 := by
    intro n hn
    have hnpos := (hF n hn).1
    have heq := hrec n hn
    nlinarith
  have hinj : ∀ n ∈ F, ∀ k ∈ F, n / p ^ 2 = k / p ^ 2 → n = k := by
    intro n hn k hk heq
    rw [hrec n hn, hrec k hk, heq]
  have hmass := sum_recip_sq_le_two (F.image (fun n => n / p ^ 2)) (by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact hquot n hn)
  rw [Finset.sum_image hinj] at hmass
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hsum : (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) =
      (1 / (p : ℚ) ^ 4) * ∑ n ∈ F, (1 : ℚ) / ((n / p ^ 2 : ℕ) : ℚ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : ((n : ℕ) : ℚ) = (p : ℚ) ^ 2 * ((n / p ^ 2 : ℕ) : ℚ) := by
      exact_mod_cast hrec n hn
    rw [hnQ]
    field_simp
  rw [hsum]
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (by positivity : (0 : ℚ) ≤ 1 / (p : ℚ) ^ 4)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hscaled

/-- A finite union bound for roots divisible by one of the selected prime
squares. No primality is needed for this estimate. -/
theorem sum_recip_sq_of_square_divisor_cover
    (F P : Finset ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hF : ∀ n ∈ F, 0 < n) (hP : ∀ p ∈ P, N < p)
    (hcover : ∀ n ∈ F, ∃ p ∈ P, p ^ 2 ∣ n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 2 / (N : ℚ) ^ 3 := by
  have hcover_sum : (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
      ∑ p ∈ P, ∑ n ∈ F.filter (fun n => p ^ 2 ∣ n), (1 : ℚ) / (n : ℚ) ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hcover n hn
    calc
      (1 : ℚ) / (n : ℚ) ^ 2 =
          if p ^ 2 ∣ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0 := by simp [hpn]
      _ ≤ ∑ q ∈ P, if q ^ 2 ∣ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0 := by
        apply Finset.single_le_sum
          (f := fun q : ℕ => if q ^ 2 ∣ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0)
        · intro q _
          split_ifs <;> positivity
        · exact hp
  calc
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ p ∈ P, ∑ n ∈ F.filter (fun n => p ^ 2 ∣ n), (1 : ℚ) / (n : ℚ) ^ 2 :=
      hcover_sum
    _ ≤ ∑ p ∈ P, (2 : ℚ) / (p : ℚ) ^ 4 := by
      apply Finset.sum_le_sum
      intro p hp
      apply sum_recip_sq_multiples_sq _ p (by have := hP p hp; omega)
      intro n hn
      obtain ⟨hnF, hdiv⟩ := Finset.mem_filter.mp hn
      exact ⟨hF n hnF, hdiv⟩
    _ = 2 * ∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ 2 / (N : ℚ) ^ 3 := by
      have hscaled := mul_le_mul_of_nonneg_left (sum_recip_fourth_tail P N hN hP)
        (by norm_num : (0 : ℚ) ≤ 2)
      simpa only [div_eq_mul_inv, one_mul] using hscaled

private def smoothSquares (N : ℕ) : Finset ℕ :=
  ((Finset.range (N * 2 ^ N)).filter
    (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)

private def largePrimeSquares (N : ℕ) : Finset ℕ :=
  ((Finset.range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)

private def squareCover (N : ℕ) : Finset ℕ :=
  (smoothSquares N ×ˢ (largePrimeSquares N).powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)

private theorem lowPart_le_bound {N n : ℕ} (hn : 0 < n) (hb : n < N * 2 ^ N) :
    lowPart N n ^ 2 ∈ smoothSquares N := by
  have hdvd := lowPart_dvd N n hn
  have hpos : 0 < lowPart N n := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz] at hdvd
    exact hn.ne' (zero_dvd_iff.mp hdvd)
  apply Finset.mem_image.mpr
  refine ⟨lowPart N n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    ((Nat.le_of_dvd hn hdvd).trans_lt hb), hpos, ?_⟩, rfl⟩
  intro q hq
  have hprime := Nat.prime_of_mem_primeFactors hq
  have h := Nat.dvd_of_mem_primeFactors hq
  unfold lowPart at h
  rw [Prime.dvd_finsetProd_iff hprime.prime] at h
  obtain ⟨p, hp, hpdvd⟩ := h
  obtain ⟨hpmem, hpN⟩ := Finset.mem_filter.mp hp
  have heq := (Nat.prime_dvd_prime_iff_eq hprime (Nat.prime_of_mem_primeFactors hpmem)).mp
    (hprime.dvd_of_dvd_pow hpdvd)
  exact heq.symm ▸ hpN

private theorem square_mem_cover {N n : ℕ} (hn : 0 < n) (hb : n < N * 2 ^ N)
    (hlarge : ∀ p ∈ n.primeFactors, N < p → n.factorization p ≤ 1) :
    n ^ 2 ∈ squareCover N := by
  let S := (highSupport N n).image (fun p => p ^ 2)
  have hS : S ⊆ largePrimeSquares N := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hpmem, hpN⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Nat.le_of_mem_primeFactors hpmem).trans_lt hb), Nat.prime_of_mem_primeFactors hpmem, hpN⟩, rfl⟩
  have hprod : ∏ q ∈ S, q = (∏ p ∈ highSupport N n, p) ^ 2 := by
    change (∏ q ∈ (highSupport N n).image (fun p => p ^ 2), q) = _
    rw [Finset.prod_image (fun a _ b _ h => Nat.pow_left_injective (by decide : 2 ≠ 0) h)]
    exact Finset.prod_pow _ _ _
  apply Finset.mem_image.mpr
  refine ⟨(lowPart N n ^ 2, S), Finset.mem_product.mpr
    ⟨lowPart_le_bound hn hb, Finset.mem_powerset.mpr hS⟩, ?_⟩
  change lowPart N n ^ 2 * (∏ q ∈ S, q) = n ^ 2
  rw [hprod, ← mul_pow]
  exact congrArg (· ^ 2) (lowPart_mul_highSupport N n hn hlarge)

private theorem omitted_has_large_prime_square {N n : ℕ}
    (hn : 0 < n) (hb : n < N * 2 ^ N) (hm : n ^ 2 ∉ squareCover N) :
    ∃ p, p.Prime ∧ N < p ∧ p ^ 2 ∣ n := by
  by_contra h
  push Not at h
  apply hm (square_mem_cover hn hb (fun p hp hNp => ?_))
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_contra! hlarge
  have hdiv := (hprime.pow_dvd_iff_le_factorization hn.ne').mpr (show 2 ≤ n.factorization p by omega)
  exact h p hprime hNp hdiv

private theorem sq_le_two_pow {N : ℕ} (hN : 4 ≤ N) : N ^ 2 ≤ 2 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ (2 : ℕ) n]
    have h := Nat.mul_le_mul_right 2 ih
    have hn' := Nat.mul_le_mul_right n hn
    nlinarith only [hn, hn', h]

private theorem omitted_mass_bound (N M : ℕ) (hN : 40 ≤ N) :
    ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ squareCover N), (1 : ℚ) / (n : ℚ)^2 ≤
      1 / (10 * (N : ℚ)^2) := by
  let F := (Ico 2 M).filter (fun n => n ^ 2 ∉ squareCover N)
  let A := F.filter (· < N ^ 3)
  let B := F.filter (N ^ 3 ≤ ·)
  have hsplit : (∑ n ∈ A, (1 : ℚ) / (n : ℚ)^2) + ∑ n ∈ B, (1 : ℚ) / (n : ℚ)^2 =
      ∑ n ∈ F, (1 : ℚ) / (n : ℚ)^2 := by
    simpa only [A, B, not_lt] using sum_filter_add_sum_filter_not F (· < N ^ 3)
      (fun n => (1 : ℚ) / (n : ℚ)^2)
  have hNcube : N ^ 3 ≤ N * 2 ^ N := by
    simpa only [pow_succ, mul_comm] using Nat.mul_le_mul_left N (sq_le_two_pow (by omega : 4 ≤ N))
  have hA : ∑ n ∈ A, (1 : ℚ) / (n : ℚ)^2 ≤ 2 / (N : ℚ)^3 := by
    apply sum_recip_sq_of_square_divisor_cover A (Ioo N M) N (by omega)
    · intro n hn
      have h := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
      omega
    · intro p hp
      exact (mem_Ioo.mp hp).1
    · intro n hn
      obtain ⟨hF, hlt⟩ := mem_filter.mp hn
      obtain ⟨hi, hm⟩ := mem_filter.mp hF
      obtain ⟨hlo, hhi⟩ := mem_Ico.mp hi
      have hpos : 0 < n := by omega
      obtain ⟨p, _, hp, hdiv⟩ := omitted_has_large_prime_square hpos (hlt.trans_le hNcube) hm
      have hle : p ≤ n := Nat.le_of_dvd hpos ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv)
      exact ⟨p, mem_Ioo.mpr ⟨hp, hle.trans_lt hhi⟩, hdiv⟩
  have htwo : 2 ≤ N ^ 3 := (show 2 ≤ N by omega).trans (Nat.le_self_pow (by decide) N)
  have htwo' : (2 : ℚ) ≤ (N : ℚ)^3 := by exact_mod_cast htwo
  have hB : ∑ n ∈ B, (1 : ℚ) / (n : ℚ)^2 ≤ 2 / (N : ℚ)^3 := by
    have ht := sum_recip_sq_tail B (N ^ 3) htwo (fun n hn => (mem_filter.mp hn).2)
    push_cast at ht
    refine ht.trans ((div_le_div_iff₀ (by linarith only [htwo']) (by linarith only [htwo'])).2 ?_)
    linarith only [htwo']
  have hN' : (40 : ℚ) ≤ N := by exact_mod_cast hN
  have hmass : (∑ n ∈ F, (1 : ℚ) / (n : ℚ)^2) ≤ 4 / (N : ℚ)^3 := by
    calc
      _ = (∑ n ∈ A, (1 : ℚ) / (n : ℚ)^2) + ∑ n ∈ B, (1 : ℚ) / (n : ℚ)^2 := hsplit.symm
      _ ≤ 2 / (N : ℚ)^3 + 2 / (N : ℚ)^3 := add_le_add hA hB
      _ = _ := by ring
  refine hmass.trans ((div_le_div_iff₀ (by positivity) (by positivity)).2 ?_)
  nlinarith only [mul_le_mul_of_nonneg_right hN' (sq_nonneg (N : ℚ))]

end OMA.ReciprocalSquareTail

open OMA.ReciprocalSquareTail in
theorem OMA.solution : OMA.R_Erdos318_erdos_318_parts_ii_R1.H2 := by
  refine ⟨40, fun N hN M => ?_⟩
  change ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ squareCover N), (1 : ℝ) / (n : ℝ)^2 ≤
    1 / (10 * (N : ℝ)^2)
  have h := (Rat.cast_le (K := ℝ)).2 (omitted_mass_bound N M hN)
  push_cast at h
  exact h
