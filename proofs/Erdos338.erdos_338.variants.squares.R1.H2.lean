import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1
import Mathlib

/-!
# Five distinct squares

Choose two large unequal squares so that the remainder is smaller than both,
congruent to 5 modulo 25, and a square multiple of a number congruent to 3 modulo 8.
Ankeny gives three squares for the remainder. A repeated square would give
2*x²+y² ≡ 5 modulo 25, which is impossible.

The Ankeny proof in namespace Three338 is adapted from pitmonticone/SumsThreeSquares,
commit b2e98cd1585300cafcc237ab5daacde565089fba, files MinkowskiConvex.lean and
SumThreeSquares.lean. The two files have been combined in a namespace.
https://github.com/pitmonticone/SumsThreeSquares
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
namespace Three338
open MeasureTheory Module Submodule

theorem classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : 2 ^ n < volume s) :
    ∃ x ≠ 0, (x ∈ s) ∧ (∀ i : Fin n, (∃ (m : ℤ), m = x i)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have : Countable (span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (span ℤ (Set.range b)))
  have fund : IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain' b volume
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [(ZSpan.fundamentalDomain_ae_parallelepiped b volume).measure_eq]
    exact (EuclideanSpace.basisFun _ _).volume_parallelepiped
  have hmeas : volume (ZSpan.fundamentalDomain b) *
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) < volume s := by
    simpa [hF, finrank_euclideanSpace_fin] using h
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv hmeas
  refine ⟨x, fun h0 => hx_ne (Subtype.ext h0), hx_mem, fun i => ?_⟩
  obtain ⟨m, hm⟩ := (b.mem_span_iff_repr_mem ℤ x.1).mp x.2 i
  exact ⟨m, by simpa [b, EuclideanSpace.basisFun_repr] using hm⟩

open scoped BigOperators Real Int Nat Classical Pointwise

noncomputable section

/-
A number is the sum of three squares if it can be written as a^2 + b^2 + c^2.
-/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

/-- If the `p`-adic valuation of `n` is odd, then `p ∣ n` (since `padicValInt p n = 0`
when `p ∤ n`, and `0` is not odd). -/
private lemma dvd_of_odd_padicValInt {p : ℕ} {n : ℤ}
    (h : Odd (padicValInt p n)) : (p : ℤ) ∣ n := by
  by_contra hpn
  rw [padicValInt.eq_zero_of_not_dvd hpn] at h
  exact absurd h (by decide)

/-- If `p` is prime and `p ∣ k`, then `jacobiSym k p ≠ 1` (it is in fact `0`). -/
private lemma not_jacobiSym_eq_one_of_dvd {p : ℕ} (hp : Nat.Prime p) {k : ℤ} (hpk : (p : ℤ) ∣ k) :
    jacobiSym k p ≠ 1 := by
  rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd hpk, jacobiSym.zero_left hp.one_lt]
  decide

/-
There exists a prime `q` with `q ≡ 1 (mod 4)` and `(-2q/p) = 1` for all prime factors `p` of `m`.
-/

/-- For any natural `a` and any odd natural `p`, some shift `a + k * p` is `≡ 1 (mod 4)`.
(Since `gcd(p, 4) = 1`, multiplication by `p` is a permutation on `ZMod 4`.) -/
private lemma exists_shift_mod4_eq_one (a : ℕ) {p : ℕ} (hp_odd : Odd p) :
    ∃ k : ℕ, (a + k * p) % 4 = 1 := by
  have hp2 : p ^ 2 % 4 = 1 := by
    have : (p : ℤ) ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd (by exact_mod_cast hp_odd)
    exact_mod_cast this
  have heq : a + (3 * a + 1) * p * p = a + (3 * a + 1) * p ^ 2 := by ring
  exact ⟨(3 * a + 1) * p, by grind [Nat.add_mod, Nat.mul_mod]⟩

/-- For an odd prime `p`, there is a natural `a ≡ 1 (mod 4)` coprime to `p` with `-2 * a`
a quadratic residue modulo `p`. Witness: `(p-1)/2` (giving `-2 * (p-1)/2 ≡ 1 (mod p)`),
shifted by a multiple of `p` to fix the residue modulo 4. -/
private lemma exists_residue_neg_two_qr_mod_odd_prime (p : ℕ) (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2) :
    ∃ a : ℕ, jacobiSym (-2 * a) p = 1 ∧ a % p ≠ 0 ∧ a % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hp.odd_of_ne_two hp_ne_two
  have hk_lt : k < 2 * k + 1 ∧ k ≠ 0 := by have := hp.two_le; omega
  obtain ⟨ks, hks⟩ := exists_shift_mod4_eq_one k ⟨k, rfl⟩
  refine ⟨k + ks * (2 * k + 1), ?_, ?_, hks⟩
  · have h1 : (-2 * ((k + ks * (2 * k + 1) : ℕ) : ℤ)) =
        1 + ↑(2 * k + 1) * (-1 - 2 * ks) := by push_cast; ring
    rw [jacobiSym.mod_left, h1, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
      jacobiSym.one_left]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk_lt.1]; exact hk_lt.2

/-- Chinese Remainder Theorem over the prime factors of an odd natural number `m`,
simultaneously achieving `≡ 1 (mod 4)`. Given per-prime residue data `a p`, we can find
a single `c` satisfying all the congruences `c ≡ a p (mod p)` for `p ∈ primeFactors m`
together with `c ≡ 1 (mod 4)`. -/
private lemma exists_crt_primeFactors_and_mod4 {m : ℕ} (hm_odd : Odd m) (a : ℕ → ℕ) :
    ∃ c : ℕ, (∀ p : ℕ, p ∣ m → Nat.Prime p → c ≡ a p [MOD p]) ∧ c ≡ 1 [MOD 4] := by
  have hodd : ∀ p ∈ m.primeFactors, Odd p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd'.resolve_left fun h2 => by
      subst h2
      have h2dvd := Nat.dvd_of_mem_primeFactors hp
      have := Nat.odd_iff.mp hm_odd
      omega
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset (fun p => if p = 4 then 1 else a p) id
    (insert 4 m.primeFactors)
    (fun p hp => by rcases Finset.mem_insert.mp hp with rfl | hp
                    · norm_num
                    · exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun p hp r hr hpr => by
      rcases Finset.mem_insert.mp hp with rfl | hp <;>
        rcases Finset.mem_insert.mp hr with rfl | hr
      · exact absurd rfl hpr
      · exact Nat.Coprime.pow_left 2 (hodd r hr).coprime_two_left
      · exact Nat.coprime_comm.mp (Nat.Coprime.pow_left 2 (hodd p hp).coprime_two_left)
      · exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hr)).mpr hpr)
  refine ⟨c, fun p hp_dvd hp_prime => ?_, by simpa using hc 4 (Finset.mem_insert_self _ _)⟩
  have hp_in : p ∈ insert 4 m.primeFactors := Finset.mem_insert_of_mem
    (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hm_odd.pos.ne'⟩)
  have hp_ne_4 : p ≠ 4 := fun h => absurd hp_prime (h ▸ by decide)
  simpa [if_neg hp_ne_4] using hc p hp_in

/-- Dirichlet's theorem, packaged as an existence statement: for `a : ℕ` coprime to `N > 0`,
there is a prime in the same residue class as `a` modulo `N`. -/
private lemma exists_prime_eq_mod {a N : ℕ} (hN : 0 < N) (hcop : Nat.Coprime a N) :
    ∃ q : ℕ, Nat.Prime q ∧ q % N = a % N := by
  have : NeZero N := ⟨hN.ne'⟩
  have h_dir : Set.Infinite {q : ℕ | Nat.Prime q ∧ q % N = a % N} := by
    convert Nat.infinite_setOf_prime_and_eq_mod (q := N) (a := (a : ZMod N))
      ((ZMod.isUnit_iff_coprime a N).mpr hcop) using 1
    norm_num [← ZMod.natCast_eq_natCast_iff']
  exact h_dir.nonempty

lemma exists_prime_aux (m : ℕ) (hm_mod : m % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  have ha_p : ∀ p : ℕ, p ∣ m → Nat.Prime p → ∃ a_p : ℕ,
      jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 ∧ a_p % 4 = 1 := fun p hp hp_prime =>
    exists_residue_neg_two_qr_mod_odd_prime p hp_prime fun h => by
      subst h; have : 2 ∣ m := hp; omega
  choose! a ha using ha_p
  obtain ⟨a_crt, ha_crt_p, ha_crt_4⟩ := exists_crt_primeFactors_and_mod4 hm_odd a
  have ha_crt_cop : Nat.Coprime a_crt (4 * m) := by
    refine Nat.Coprime.mul_right (ha_crt_4.gcd_eq.trans (by norm_num)) ?_
    refine Nat.coprime_of_dvd' fun k hk hk₁ hk₂ => ?_
    grind [Nat.ModEq, Nat.dvd_iff_mod_eq_zero]
  obtain ⟨q, hq_prime, hq_mod⟩ := exists_prime_eq_mod (by omega : 0 < 4 * m) ha_crt_cop
  refine ⟨q, hq_prime, ?_, fun p hp hp_prime => ?_⟩
  · rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 4 m), hq_mod,
        Nat.mod_mod_of_dvd _ (dvd_mul_right 4 m)]
    exact ha_crt_4
  · have h_qap : (q : ℤ) ≡ a p [ZMOD p] :=
      (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hp 4))
        (Int.natCast_modEq_iff.mpr hq_mod)).trans
        (Int.natCast_modEq_iff.mpr (ha_crt_p p hp hp_prime))
    rw [jacobiSym.mod_left (-2 * (q : ℤ)), (h_qap.mul_left (-2)), ← jacobiSym.mod_left]
    grind

/-
If `m ≡ 3 (mod 8)` is squarefree, `q ≡ 1 (mod 4)` is prime, and `(-2q/p) = 1` for all `p | m`,
then `(-m/q) = 1`.
-/
lemma exists_odd_sq_mod_prime_of_jacobi_eq_one (m q : ℕ) (hq_prime : Nat.Prime q)
    (hq_mod : q % 4 = 1) (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b : ℤ, b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b % 2 = 1 := by
  have := Fact.mk hq_prime
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one h_jacobi
  have hb₀ : (x.val : ℤ) ^ 2 ≡ -(m : ℤ) [ZMOD q] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  by_cases hb₀_odd : (x.val : ℤ) % 2 = 1
  · exact ⟨x.val, hb₀, hb₀_odd⟩
  · refine ⟨x.val + q, (Int.add_modEq_right.pow 2).trans hb₀, ?_⟩
    have hq_odd : (q : ℤ) % 2 = 1 := mod_cast hq_prime.eq_two_or_odd.resolve_left (by grind)
    grind

lemma jacobi_neg_m_q (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_mod : q % 4 = 1)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    jacobiSym (-m) q = 1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  have h_qm : jacobiSym (-2 * q) m = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_pmap.mp hx
    have hp_prime := Nat.prime_of_mem_primeFactorsList hp
    have := Fact.mk hp_prime
    simpa [jacobiSym, Nat.primeFactorsList_prime hp_prime] using
      h_jacobi p (Nat.dvd_of_mem_primeFactorsList hp) hp_prime
  have h_qm' : jacobiSym q m = jacobiSym (-2) m := by
    grind [jacobiSym.mul_left, Int.mul_eq_one_iff_eq_one_or_neg_one]
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hq_odd, ZMod.χ₄_nat_one_mod_four hq_mod, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' hm_odd hq_mod, h_qm',
      jacobiSym.mod_right _ hm_odd]
  norm_num [hm_mod]

/-
There exist integers $b$ and $h$ such that $b$ is odd and $b^2 - 4qh = -m$.
-/
lemma exists_b_h (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b h : ℤ, b^2 - 4 * q * h = -m := by
  obtain ⟨b, hb_mod_q, hb_odd⟩ :=
    exists_odd_sq_mod_prime_of_jacobi_eq_one m q hq_prime hq_mod h_jacobi
  have h_cop : ((4 : ℤ).natAbs).Coprime ((q : ℤ).natAbs) :=
    Nat.coprime_comm.mp (hq_prime.coprime_iff_not_dvd.mpr fun (h : q ∣ 4) => by
      have := Nat.le_of_dvd (by decide) h; have := hq_prime.two_le; omega)
  have hb_mod : b ^ 2 ≡ -↑m [ZMOD (4 * ↑q : ℤ)] :=
    (Int.modEq_and_modEq_iff_modEq_mul h_cop).mp
      ⟨by grind [Int.ModEq, Int.sq_mod_four_eq_one_of_odd], hb_mod_q⟩
  exact ⟨b, (b^2 + m) / (4 * q),
    by have := Int.ediv_mul_cancel hb_mod.symm.dvd; grind⟩

/-
There exists an integer $t$ such that $2q t^2 \equiv -1 \pmod m$.
-/
/-- Per-prime existence: for a prime `p` with `2q` coprime to `p` and `(-2q/p) = 1`, there is
an integer `t_p` with `2q·t_p² ≡ -1 (mod p)`. The witness is `s · (2q)⁻¹` where `s² ≡ -2q`. -/
private lemma exists_t_local_of_jacobi (p q : ℕ) (hp : Nat.Prime p)
    (hp_cop : Nat.Coprime (2 * q) p) (hjac : jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, 2 * q * t ^ 2 ≡ -1 [ZMOD p] := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one hjac
  have hs : (x.val : ℤ) ^ 2 ≡ -2 * q [ZMOD p] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  obtain ⟨inv_2q, hinv_2q⟩ : ∃ inv_2q : ℤ, (2 * q : ℤ) * inv_2q ≡ 1 [ZMOD p] :=
    Int.mod_coprime hp_cop
  refine ⟨x.val * inv_2q, ?_⟩
  convert hs.mul_left (2 * q * inv_2q ^ 2) |>.trans ?_ using 1 <;> ring_nf
  convert (hinv_2q.pow 2).neg using 1 <;> ring

lemma exists_t (m : ℕ) (q : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, (2 * q : ℤ) * t^2 ≡ -1 [ZMOD m] := by
  have h_tp : ∀ p ∈ Nat.primeFactors m, ∃ t_p : ℤ, 2 * q * t_p ^ 2 ≡ -1 [ZMOD (p : ℤ)] := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    refine exists_t_local_of_jacobi p q hp_prime (Nat.Coprime.mul_left
      (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2p => by
        have : 2 ∣ m := dvd_trans h2p hpm; omega)
      ((Nat.coprime_primes hq_prime hp_prime).mpr fun heq => by
        subst heq
        exact not_jacobiSym_eq_one_of_dvd hq_prime (by simp) (h_jacobi q hpm hq_prime)))
      (h_jacobi p hpm hp_prime)
  choose! t ht using h_tp
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset (fun p => ((t p).emod p).toNat) id
    m.primeFactors (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun _ hp _ hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  refine ⟨c, ?_⟩
  rw [Int.modEq_iff_dvd, ← Nat.prod_primeFactors_of_squarefree hm_sq, Nat.cast_prod]
  refine Finset.prod_dvd_of_coprime
    (fun _ hp _ hq hpq => ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq).cast)
    (fun p hp => Int.modEq_iff_dvd.mp ?_)
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have h1 : (c : ℤ) ≡ ((t p).emod p).toNat [ZMOD (p : ℤ)] := by exact_mod_cast hc p hp
  have hcp : (c : ℤ) ≡ t p [ZMOD (p : ℤ)] :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ hp_ne) ▸ h1).trans (Int.emod_emod_of_dvd _ dvd_rfl)
  exact ((hcp.pow 2).mul_left _).trans (ht p hp)

noncomputable def linear_map_M (m q : ℕ) (t b : ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (!![
    2 * t * q, t * b, m;
    Real.sqrt (2 * q), b / Real.sqrt (2 * q), 0;
    0, Real.sqrt m / Real.sqrt (2 * q), 0])

lemma det_linear_map_M (m q : ℕ) (t b : ℤ) (hq : 0 < q) :
    LinearMap.det (linear_map_M m q t b) = m * Real.sqrt m := by
  unfold linear_map_M
  simp [Matrix.det_fin_three]
  rw [mul_assoc, mul_div_cancel₀ _ (by positivity)]

noncomputable abbrev linear_map_M_euclidean (m q : ℕ) (t b : ℤ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap ∘ₗ
    (linear_map_M m q t b) ∘ₗ (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap

lemma det_linear_map_M_euclidean (m q : ℕ) (t b : ℤ) (hq : 0 < q) :
    LinearMap.det (linear_map_M_euclidean m q t b) = m * Real.sqrt m :=
  (LinearMap.det_conj (linear_map_M m q t b)
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv).trans (det_linear_map_M m q t b hq)

/-- Component formulas for the linear map `linear_map_M_euclidean`. -/
private lemma linear_map_M_euclidean_apply (m q : ℕ) (t b : ℤ) (x : EuclideanSpace ℝ (Fin 3)) :
    (linear_map_M_euclidean m q t b x) 0 = 2 * t * q * x 0 + t * b * x 1 + m * x 2 ∧
    (linear_map_M_euclidean m q t b x) 1 =
      Real.sqrt (2 * q) * x 0 + b / Real.sqrt (2 * q) * x 1 ∧
    (linear_map_M_euclidean m q t b x) 2 = Real.sqrt m / Real.sqrt (2 * q) * x 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp [linear_map_M_euclidean, linear_map_M, Matrix.toLin'_apply, Matrix.vecHead,
      Matrix.vecTail]; try ring)

lemma quad_form_decomposition (m q : ℕ) (b h x y : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
      (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 =
      2 * ((q : ℝ) * x ^ 2 + (b : ℝ) * x * y + (h : ℝ) * y ^ 2) := by
  have hb2 : (b : ℝ) ^ 2 = 4 * q * h - m :=
    by exact_mod_cast (by grind : (b : ℤ) ^ 2 = 4 * q * h - m)
  field_simp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * q),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  linear_combination (y : ℝ)^2 * hb2

/-- Minkowski volume certificate: the preimage under `linear_map_M_euclidean` of the ball
of radius `√(2m)` has volume strictly greater than `2^3 = 8`. -/
private lemma vol_preimage_ball_gt_eight (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    (2 : ENNReal) ^ 3 < MeasureTheory.volume
      ((linear_map_M_euclidean m q t b) ⁻¹'
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
  have hdet_ne : LinearMap.det (linear_map_M_euclidean m q t b) ≠ 0 := by
    rw [det_linear_map_M_euclidean m q t b hq]; positivity
  rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet_ne,
      det_linear_map_M_euclidean m q t b hq, EuclideanSpace.volume_ball_fin_three,
      abs_inv, abs_of_nonneg (by positivity),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      (by norm_num : ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8),
      ENNReal.ofReal_lt_ofReal_iff (by positivity),
      (by rw [pow_succ, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m),
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; ring :
        (Real.sqrt (2 * m)) ^ 3 = 2 * Real.sqrt 2 * ((m : ℝ) * Real.sqrt m))]
  field_simp
  nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
    (by positivity : 0 < (m : ℝ) * Real.sqrt m)]

private lemma exists_lattice_xyz_lt_two_m (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    ((2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z)^2 +
      (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y)^2 +
      (Real.sqrt m / Real.sqrt (2 * q) * y)^2 < 2 * m := by
  obtain ⟨x, hx0, hxs, h⟩ :=
    classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (fun _ hx => by simpa using hx)
      (Convex.linear_preimage (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) _)
      (vol_preimage_ball_gt_eight m q t b hm hq)
  choose R hR using h
  refine ⟨R 0, R 1, R 2, ?_, ?_⟩
  · contrapose! hx0
    ext i; rw [← hR i]; fin_cases i <;> aesop
  · obtain ⟨h0, h1, h2⟩ := linear_map_M_euclidean_apply m q t b x
    have h_norm_sq : (‖linear_map_M_euclidean m q t b x‖ ^ 2 : ℝ) < 2 * m := by
      have : ‖linear_map_M_euclidean m q t b x‖ < Real.sqrt (2 * m) := by simpa using hxs
      nlinarith [norm_nonneg (linear_map_M_euclidean m q t b x),
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m)]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2] at h_norm_sq
    convert h_norm_sq using 1
    push_cast [hR 0, hR 1, hR 2]
    ring

private lemma rst_modEq_zero (m q : ℕ) (t b h x y z : ℤ)
    (hqt : 2 * q * t^2 ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * q * h = -m) :
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) ≡ 0 [ZMOD m] := by
  obtain ⟨c, hc⟩ : (m : ℤ) ∣ 2 * q * t ^ 2 + 1 := by
    simpa [neg_sub] using (Int.modEq_iff_dvd.mp hqt).neg_right
  rw [Int.modEq_zero_iff_dvd]
  refine ⟨c * (2 * q * x ^ 2 + 2 * b * x * y + 2 * h * y ^ 2) +
    (4 * t * q * x * z + 2 * t * b * y * z + m * z ^ 2 - t ^ 2 * y ^ 2), ?_⟩
  linear_combination (2 * q * x ^ 2 + 2 * b * x * y + 2 * h * y ^ 2) * hc + t ^ 2 * y ^ 2 * hbqm

/-- The integer binary quadratic form `q·x² + b·x·y + h·y²` is nonnegative when its
discriminant is `-m < 0` (i.e. negative definite `-Δ`) and `q > 0`. -/
private lemma quadform_nonneg {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (x y : ℤ) :
    0 ≤ (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 := by
  nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y), sq_nonneg (y : ℤ), hbqm,
    Int.natCast_nonneg m]

/-- The binary form `q·x² + b·x·y + h·y²` with `q > 0` and discriminant `-m < 0` has only the
trivial zero: `qf = 0 ↔ x = y = 0`. (Reverse direction is trivial; stated as `x = 0 ∧ y = 0`.) -/
private lemma quadform_eq_zero_imp_xy_zero {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) {x y : ℤ}
    (h_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · exact ⟨by subst hy; nlinarith [sq_nonneg x, hq, h_zero], hy⟩
  · exact absurd h_zero <| by
      nlinarith [sq_nonneg (2 * (q:ℤ)*x + b*y), mul_self_pos.mpr hy, hbqm, Int.natCast_pos.mpr hm]

/-- A nonnegative integer `n ≡ 0 (mod m)` with `n < 2m` is either `0` or `m`. -/
private lemma eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul {m : ℤ} (hm : 0 < m)
    {n : ℤ} (h_nn : 0 ≤ n) (h_mod : n ≡ 0 [ZMOD m]) (h_lt : n < 2 * m) :
    n = 0 ∨ n = m := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h_mod
  have hk0 : 0 ≤ k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  interval_cases k <;> grind

/-- The discriminant `b² - 4qh` of an integer binary quadratic form cannot equal `-1`:
squares mod 4 are in `{0, 1}` but `-1 ≡ 3 (mod 4)`. -/
private lemma discriminant_ne_neg_one (q : ℕ) (b h : ℤ) : b ^ 2 - 4 * (q : ℤ) * h ≠ -1 := by
  intro hcon
  have hcon' : b ^ 2 = 4 * ((q : ℤ) * h) - 1 := by linarith [hcon]
  rcases Int.even_or_odd b with ⟨k, rfl⟩ | hodd
  · grind
  · grind [Int.sq_mod_four_eq_one_of_odd]

lemma exists_Rv_from_Minkowski (m q : ℕ) (t b h : ℤ) (hm : 0 < m) (hq : 0 < q)
    (hqt : 2 * q * t ^ 2 ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    ∃ (x y : ℤ) (R : ℤ) (v : ℕ),
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  obtain ⟨x, y, z, hne, hlt⟩ := exists_lattice_xyz_lt_two_m m q t b hm hq
  have hqf_nn : 0 ≤ (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 := quadform_nonneg hq hbqm x y
  -- `R² + 2·qf` is nonneg, `< 2m`, and `≡ 0 (mod m)`, hence `∈ {0, m}`.
  have h_lt : (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
      2 * ((q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2) < 2 * m := by
    have hqfd := quad_form_decomposition m q b h x y hq (by exact_mod_cast hbqm)
    have : ((2 * t * q * x + t * b * y + m * z : ℤ) : ℝ) ^ 2 +
        2 * (((q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 : ℤ) : ℝ) < 2 * m := by push_cast; linarith
    exact_mod_cast this
  have h_cases := eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul
    (by exact_mod_cast hm : (0 : ℤ) < m) (by positivity)
    (rst_modEq_zero m q t b h x y z hqt hbqm) h_lt
  rcases h_cases with h_case1 | h_case2
  · have h_qf0 : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * t * q * x + t * b * y + m * z : ℤ)]
    obtain ⟨rfl, rfl⟩ := quadform_eq_zero_imp_xy_zero hq hm hbqm h_qf0
    obtain rfl : z = 0 :=
      (mul_eq_zero.mp (by nlinarith : (m : ℤ) * z = 0)).resolve_left (by exact_mod_cast hm.ne')
    exact absurd rfl hne
  · refine ⟨x, y, 2 * t * q * x + t * b * y + m * z,
      Int.toNat (q * x ^ 2 + b * x * y + h * y ^ 2), ?_, ?_, ?_⟩ <;> norm_num
    · exact hqf_nn
    · grind
    · contrapose! hne
      have hqf_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
        nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y)]
      obtain ⟨rfl, rfl⟩ := quadform_eq_zero_imp_xy_zero hq hm hbqm hqf_zero
      simp_all
      rcases m with _ | _ | m <;> norm_num at *
      · exact absurd hbqm (discriminant_ne_neg_one q b h)
      · have hz : z ^ 2 * (m + 1 + 1) = 1 := by nlinarith
        nlinarith [hz]

lemma jacobi_neg_d_of_dvd_sq_add (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2) (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (hp_not_dvd_b : ¬ (p : ℤ) ∣ b') :
    jacobiSym (-d) p = 1 := by
  have := Fact.mk hp
  rw [jacobiSym]
  norm_num [Nat.primeFactorsList_prime hp]
  simp_all [← ZMod.intCast_zmod_eq_zero_iff_dvd, legendreSym.eq_one_iff]
  use a / b'
  grind

lemma jacobi_neg_d_of_odd_padicVal (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (h_odd_val : Odd (padicValInt p (a ^ 2 + d * b' ^ 2))) :
    jacobiSym (-d) p = 1 := by
  induction' n : Int.natAbs a + Int.natAbs b' using Nat.strong_induction_on with n ih
    generalizing a b'
  by_cases h_div_b' : (p : ℤ) ∣ b'
  · obtain ⟨k, hk⟩ := h_div_b'
    obtain ⟨a', ha'⟩ : ∃ a', a = p * a' :=
      Int.Prime.dvd_pow' hp <| by
        simpa [hk, ← ZMod.intCast_zmod_eq_zero_iff_dvd] using dvd_of_odd_padicValInt h_odd_val
    contrapose! ih
    refine ⟨a'.natAbs + k.natAbs, ?_, a', k, ?_, rfl, ih⟩
    · rcases eq_or_ne a' 0 with ha0 | ha0 <;> rcases eq_or_ne k 0 with hk0 | hk0 <;>
        simp_all [Int.natAbs_mul]
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hk0) hp.one_lt
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr ha0) hp.one_lt
      · nlinarith [hp.two_le, abs_pos.mpr ha0, abs_pos.mpr hk0]
    · simp_all [padicValInt, parity_simps]
      have hfactor : (p * a') ^ 2 + d * (p * k) ^ 2 = p ^ 2 * (a' ^ 2 + d * k ^ 2) := by ring
      rw [hfactor, Int.natAbs_mul, Int.natAbs_pow] at h_odd_val
      have := Fact.mk hp
      rw [padicValNat.mul] at h_odd_val <;> simp_all +decide [parity_simps]
      · exact hp.ne_zero
      · intro H; simp_all
  · exact jacobi_neg_d_of_dvd_sq_add p a d b' hp (dvd_of_odd_padicValInt h_odd_val)
      hp_not_dvd_d h_div_b'

/-- Completing-the-square for the binary form: `4·q·v = (2·q·x + b·y)² + m·y²` when
`v = q·x² + b·x·y + h·y²` and `b² - 4·q·h = -m`. -/
private lemma four_q_v_eq_sq_plus_m_y_sq {m : ℕ} {q : ℤ} {b h x y v : ℤ}
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -(m : ℤ)) :
    4 * q * v = (2 * q * x + b * y) ^ 2 + (m : ℤ) * y ^ 2 := by
  rw [hv]; linear_combination -hbqm * y ^ 2

/-- If `R² ≡ a (mod p)` with `p ∤ a` and `p` an odd prime, then `(a/p) = 1` (Jacobi/Legendre). -/
private lemma jacobiSym_eq_one_of_sq_modEq {p : ℕ} (hp : Nat.Prime p) {a R : ℤ}
    (hpa : ¬ (p : ℤ) ∣ a) (hRa : R ^ 2 ≡ a [ZMOD p]) :
    jacobiSym a p = 1 := by
  have := Fact.mk hp
  simp_all [← ZMod.intCast_eq_intCast_iff, jacobiSym,
    Nat.primeFactorsList_prime hp]
  rw [legendreSym.eq_one_iff]
  · exact ⟨R, by simpa [sq] using hRa.symm⟩
  · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpa

/-- For an odd prime `p` coprime to `q` and dividing a nonzero integer `v`,
`padicValInt p (4qv) = padicValInt p v`. -/
private lemma padicValInt_four_q_v {p : ℕ} {q v : ℤ}
    (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hpq : ¬ (p : ℤ) ∣ q) (hpv : Odd (padicValInt p v)) :
    padicValInt p (4 * q * v) = padicValInt p v := by
  have := Fact.mk hp
  rw [padicValInt.mul, padicValInt.mul] <;> norm_num
  · refine ⟨Or.inr <| mod_cast fun h => hp_odd ?_, Or.inr <| Or.inr hpq⟩
    have := Nat.le_of_dvd (by decide) h
    interval_cases p <;> trivial
  all_goals aesop

lemma p_mod4_eq1_of_dvd_v_not_dvd_m (p : ℕ) (q : ℤ) (b h x y v R m : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -m)
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : Odd (padicValInt p v))
    (hpm : ¬ (p : ℤ) ∣ m) :
    p % 4 = 1 := by
  have hpv_dvd : (p : ℤ) ∣ v := dvd_of_odd_padicValInt hpv
  have h_diff : (m - R ^ 2 : ℤ) = 2 * v := by grind
  have h_jacobi_m : jacobiSym m p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp hpm (R := R)
      (Int.modEq_iff_dvd.mpr (by rw [h_diff]; exact hpv_dvd.mul_left 2))
  have h_jacobi_neg_m : jacobiSym (-m) p = 1 := by
    by_cases hpq : (p : ℤ) ∣ q
    · -- `p | q`: then `b² - 4qh = -m` gives `b² ≡ -m (mod p)`, so `(-m/p) = 1`.
      refine jacobiSym_eq_one_of_sq_modEq hp (by simpa using hpm) (R := b) ?_
      exact Int.modEq_iff_dvd.mpr ⟨-4 * h * hpq.choose,
        by linear_combination -hbqm - 4 * h * hpq.choose_spec⟩
    · have h_padic := padicValInt_four_q_v hp hp_odd hpq hpv
      apply jacobi_neg_d_of_odd_padicVal p (2 * q * x + b * y) m y hp hpm
      grind
  rw [jacobiSym.neg _ (hp.odd_of_ne_two hp_odd), h_jacobi_m, mul_one,
    ZMod.χ₄_nat_mod_four] at h_jacobi_neg_m
  have := Nat.mod_lt p zero_lt_four
  interval_cases p % 4 <;> trivial

/-- If `R² + 2v = m`, `p` is a prime dividing both `v` and `m`, then `p ∣ R`. -/
private lemma dvd_R_of_dvd_v_dvd_m {p : ℕ} (hp : Nat.Prime p) {R v : ℤ} {m : ℕ}
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) : (p : ℤ) ∣ R :=
  Int.Prime.dvd_pow' hp <| by
    rw [← Int.dvd_add_left (dvd_mul_of_dvd_right hpv _)]
    exact hRv.symm ▸ Int.natCast_dvd_natCast.mpr hpm

/-- Given `v = qx² + bxy + hy²`, `b² - 4qh = -m`, a prime `p ∣ v` and `p ∣ m`, then
`p ∣ (2qx + by)`. Uses the identity `4qv = (2qx + by)² + m·y²`. -/
private lemma dvd_two_q_x_add_b_y_of_dvd_v_dvd_m {p q : ℕ} {b h x y v : ℤ} {m : ℕ}
    (hp : Nat.Prime p) (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) : (p : ℤ) ∣ (2 * q * x + b * y) := by
  have h_sum : (p : ℤ) ∣ ((2 * q * x + b * y) ^ 2 + m * y ^ 2) := by
    rw [← four_q_v_eq_sq_plus_m_y_sq hv hbqm]
    exact hpv.mul_left (4 * q)
  exact Int.Prime.dvd_pow' hp <|
    (Int.dvd_add_left ((Int.natCast_dvd_natCast.mpr hpm).mul_right _)).mp h_sum

/-- The quadratic residue extraction: given the problem hypotheses with `p` a prime
dividing both `v` and `m` (and `m` squarefree), we have `y² ≡ 2q (mod p)`. -/
private lemma y_sq_modEq_two_mul_q {p q : ℕ} {b h x y : ℤ} {R v : ℤ} {m : ℕ}
    (hp : Nat.Prime p) (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) :
    y ^ 2 ≡ 2 * q [ZMOD p] := by
  have hp_R := dvd_R_of_dvd_v_dvd_m hp hRv hpv hpm
  have hp_2qx_by := dvd_two_q_x_add_b_y_of_dvd_v_dvd_m hp hv hbqm hpv hpm
  have h_div_p : (m / p : ℤ) * y ^ 2 ≡ (m / p : ℤ) * (2 * q) [ZMOD p] := by
    have h_div_p : (4 * q * v : ℤ) ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
      obtain ⟨k, hk⟩ := hpv
      simp_all [Int.modEq_iff_dvd]
      obtain ⟨a, ha⟩ := hp_R
      obtain ⟨b', hb'⟩ := hp_2qx_by
      simp_all [← eq_sub_iff_add_eq', ← mul_assoc]
      exact ⟨a ^ 2 * 2 * q, by nlinarith⟩
    have h_div_p : (4 * q * v : ℤ) ≡ (2 * q * x + b * y) ^ 2 + m * y ^ 2 [ZMOD p ^ 2] :=
      (four_q_v_eq_sq_plus_m_y_sq hv hbqm) ▸ .refl _
    have h_div_p : (m : ℤ) * y ^ 2 ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
      simp_all [Int.ModEq]
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at *
      aesop
    rw [Int.modEq_iff_dvd] at *
    obtain ⟨k, hk⟩ := h_div_p
    use k
    have hpm' : (p : ℤ) ∣ m := mod_cast hpm
    nlinarith [hp.two_le, Int.ediv_mul_cancel hpm']
  have := Fact.mk hp
  simp_all [← ZMod.intCast_eq_intCast_iff]
  cases h_div_p <;> simp_all [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_cast at *
  simp_all [Nat.squarefree_iff_prime_squarefree]

lemma p_mod4_of_dvd_v_dvd_m (p : ℕ) (q : ℕ) (b h x y : ℤ) (R v : ℤ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m)
    (hjac : jacobiSym (-2 * q) p = 1) :
    False := by
  have h_jacobi_2q_p : jacobiSym (2 * q) p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp
      (fun h2q => not_jacobiSym_eq_one_of_dvd hp (by simpa [neg_mul] using h2q.neg_right) hjac)
      (y_sq_modEq_two_mul_q hp hm_sq hv hbqm hRv hpv hpm)
  simp only [neg_mul] at hjac
  rw [jacobiSym.neg _ (hp.odd_of_ne_two (by omega)), ZMod.χ₄_nat_mod_four, hp3,
      h_jacobi_2q_p, mul_one] at hjac
  exact absurd hjac (by decide)

lemma even_padicVal_of_mod4_eq3 (p : ℕ) (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hm_sq : Squarefree m) (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p', p' ∣ m → Nat.Prime p' → jacobiSym (-2 * ↑q) ↑p' = 1) :
    Even (padicValNat p (2 * v)) := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hEven : Even (padicValInt p v) := by
    by_contra h_even
    have h_odd : Odd (padicValInt p v) := Nat.not_even_iff_odd.mp h_even
    by_cases hpm : (p : ℕ) ∣ m
    · exact p_mod4_of_dvd_v_dvd_m p q b h x y R v m hp hp3 hm_sq hv_def hbqm hRv
        (dvd_of_odd_padicValInt h_odd) hpm (hjac p hpm hp)
    · have := p_mod4_eq1_of_dvd_v_not_dvd_m p q b h x y v R m hp hp2 hv_def hbqm hRv h_odd
        (by exact_mod_cast hpm)
      omega
  rw [padicValNat.mul (by omega) hv_pos.ne',
    padicValNat.eq_zero_of_not_dvd fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h), zero_add,
    ← padicValInt.of_nat]
  exact hEven

/-- The final theorem -/
theorem blueprint_case_mod8_eq3 (m : ℕ) (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hm_mod : m % 8 = 3) : IsSumOfThreeSquares m := by
  obtain ⟨q, hq_prime, hq_mod, hjac⟩ := exists_prime_aux m hm_mod
  obtain ⟨b, h, hbqm⟩ :=
    exists_b_h m q hm_mod hq_prime hq_mod (jacobi_neg_m_q m q hm_mod hq_mod hjac)
  obtain ⟨t, hqt⟩ := exists_t m q hm_sq hm_mod hq_prime hjac
  obtain ⟨x, y, R, v, hv_def, hRv, hv_pos⟩ :=
    exists_Rv_from_Minkowski m q t b h hm_pos hq_prime.pos hqt hbqm
  have h2v : ∃ a b : ℕ, 2 * v = a ^ 2 + b ^ 2 := Nat.eq_sq_add_sq_iff.mpr fun p hp hp3 =>
    even_padicVal_of_mod4_eq3 p q b h x y R v m
      (Nat.prime_of_mem_primeFactors hp) hp3 hm_sq hv_pos hv_def hbqm hRv hjac
  obtain ⟨a, b, c, habc⟩ : ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
    obtain ⟨s, t, hst⟩ := h2v
    exact ⟨R, s, t, by zify at hst; linarith [hRv, hst]⟩
  refine ⟨a.natAbs, b.natAbs, c.natAbs, ?_⟩
  zify [Int.natCast_natAbs, sq_abs, habc]

end

end Three338

open Finset Filter
namespace Distinct338
private def good (n : ℕ) : Prop := n%8=3 ∨ n%32=12 ∨ n%128=48
private instance (n : ℕ) : Decidable (good n) := by unfold good; infer_instance

private lemma three_base {n : ℕ} (hn : n%8=3) : Three338.IsSumOfThreeSquares n := by
  obtain ⟨x,y,hy,hx⟩ := Nat.sq_mul_squarefree n
  have hm : (y%8)^2*(x%8)%8=3 := by
    have he := ((Nat.mod_modEq y 8).pow 2).mul (Nat.mod_modEq x 8)
    change _ % 8 = _ % 8 at he
    exact he.trans (by simpa only [hy] using hn)
  have htable : ∀ a b : Fin 8, a.val^2*b.val%8=3 → b.val=3 := by decide
  have hx8 := htable ⟨y%8,Nat.mod_lt _ (by decide)⟩ ⟨x%8,Nat.mod_lt _ (by decide)⟩ hm
  obtain ⟨a,b,c,h⟩ := Three338.blueprint_case_mod8_eq3 x hx (by change x%8=3 at hx8; omega) hx8
  exact ⟨y*a,y*b,y*c,by rw [←hy,←h]; ring⟩

private lemma scale {n : ℕ} (k : ℕ) (h : Three338.IsSumOfThreeSquares n) :
    Three338.IsSumOfThreeSquares (k^2*n) := by
  obtain ⟨a,b,c,ha⟩ := h
  exact ⟨k*a,k*b,k*c,by rw [← ha]; ring⟩

private lemma three {n : ℕ} (hn : good n) : Three338.IsSumOfThreeSquares n := by
  rcases hn with h | h | h
  · exact three_base h
  · have ht := scale 2 (three_base (show (n/4)%8=3 by omega))
    convert ht using 1 <;> omega
  · have ht := scale 4 (three_base (show (n/16)%8=3 by omega))
    convert ht using 1 <;> omega

private lemma residues (n : ℕ) : ∃ a b r : ℕ, a<3200 ∧ b<3200 ∧ good r ∧
    n ≡ a^2+b^2+r [MOD 128] ∧ n ≡ a^2+b^2+5 [MOD 25] := by
  have tab : ∀ x : Fin 128, ∃ i j : Fin 16, good ((x.val+128-(i.val^2+j.val^2)%128)%128) := by decide +kernel
  have tab' : ∀ x : Fin 25, ∃ i j : Fin 25, x.val = (i.val^2+j.val^2+5)%25 := by decide +kernel
  obtain ⟨i,j,h⟩ := tab ⟨n%128,Nat.mod_lt _ (by decide)⟩
  obtain ⟨u,v,h'⟩ := tab' ⟨n%25,Nat.mod_lt _ (by decide)⟩
  let r := (n%128+128-(i.val^2+j.val^2)%128)%128
  have hr : n ≡ i.val^2+j.val^2+r [MOD 128] := by dsimp [r,Nat.ModEq]; omega
  have cp : Nat.Coprime 128 25 := by decide
  let a := Nat.chineseRemainder cp i.val u.val
  let b := Nat.chineseRemainder cp j.val v.val
  refine ⟨a.val,b.val,r,Nat.chineseRemainder_lt_mul cp _ _ (by decide) (by decide),
    Nat.chineseRemainder_lt_mul cp _ _ (by decide) (by decide),h,?_,?_⟩
  · exact hr.trans (((a.property.1.pow 2).add (b.property.1.pow 2)).add_right r).symm
  · exact (show n ≡ u.val^2+v.val^2+5 [MOD 25] from h').trans
      (((a.property.2.pow 2).add (b.property.2.pow 2)).add_right 5).symm

private lemma neq_repeat {x y n : ℕ} (hm : n ≡ 5 [MOD 25]) (he : 2*x^2+y^2=n) : False := by
  have hh : ∀ a b : Fin 25, (2*a.val^2+b.val^2)%25 ≠ 5 := by decide
  apply hh ⟨x%25,Nat.mod_lt _ (by decide)⟩ ⟨y%25,Nat.mod_lt _ (by decide)⟩
  change (2*(x%25)^2+(y%25)^2)%25 = 5
  change n%25=5 at hm
  rw [← he] at hm
  simpa only [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,Nat.mod_mod] using hm

private lemma big_squares (n : ℕ) (hn : 3200000^2 ≤ n) {i j : ℕ} (hi : i<3200) (hj : j<3200) :
    ∃ a b w : ℕ, n=a^2+b^2+w ∧ w<b^2 ∧ b<a ∧ a ≡ i [MOD 3200] ∧ b ≡ j [MOD 3200] := by
  let k := n.sqrt / 32000
  have hs := Nat.le_sqrt'.mpr hn
  have hk : 100 ≤ k := by dsimp [k]; omega
  let a := 25600*k+i
  let b := 16000*k+j
  have ha : a ≤ 25700*k := by dsimp [a]; omega
  have hb : b ≤ 16100*k := by dsimp [b]; omega
  have hal : 25600*k ≤ a := Nat.le_add_right _ _
  have hbl : 16000*k ≤ b := Nat.le_add_right _ _
  have hs1 : 32000*k ≤ n.sqrt := by dsimp [k]; omega
  have hs2 : n.sqrt+1 ≤ 32320*k := by dsimp [k] at *; omega
  have hle : a^2+b^2 ≤ n := calc
    _ ≤ (25700*k)^2+(16100*k)^2 := Nat.add_le_add (Nat.pow_le_pow_left ha _) (Nat.pow_le_pow_left hb _)
    _ ≤ (32000*k)^2 := by nlinarith only [Nat.zero_le (k*k)]
    _ ≤ _ := (Nat.pow_le_pow_left hs1 _).trans (Nat.sqrt_le' n)
  have hlt : n < a^2+b^2+b^2 := calc
    _ < (32320*k)^2 := (Nat.lt_succ_sqrt' n).trans_le (Nat.pow_le_pow_left hs2 _)
    _ ≤ (25600*k)^2+(16000*k)^2+(16000*k)^2 := by nlinarith only [Nat.zero_le (k*k)]
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.pow_le_pow_left hal _) (Nat.pow_le_pow_left hbl _)) (Nat.pow_le_pow_left hbl _)
  refine ⟨a,b,n-(a^2+b^2),by omega,by omega,by dsimp [a,b]; omega,?_,?_⟩
  · change (25600*k+i)%3200 = i%3200; omega
  · change (16000*k+j)%3200 = j%3200; omega

private lemma complete : Erdos338.HasRestrictedOrder (Set.range fun k : ℕ => k^2) 5 := by
  classical
  filter_upwards [eventually_ge_atTop (3200000^2 : ℕ)] with n hn
  obtain ⟨i,j,r,hi,hj,hr,h128,h25⟩ := residues n
  obtain ⟨a,b,w,he,hwb,hba,ha,hb⟩ := big_squares n hn hi hj
  have cong (q : ℕ) (hq : q ∣ 3200) : a^2+b^2 ≡ i^2+j^2 [MOD q] :=
    ((ha.of_dvd hq).pow 2).add ((hb.of_dvd hq).pow 2)
  have hw128 : w ≡ r [MOD 128] := by
    rw [he] at h128
    exact Nat.ModEq.add_left_cancel (cong 128 (by decide)) h128
  have hw25 : w ≡ 5 [MOD 25] := by
    rw [he] at h25
    exact Nat.ModEq.add_left_cancel (cong 25 (by decide)) h25
  have hsame : good w := by
    unfold good at *
    have h8 := hw128.of_dvd (by decide : 8 ∣ 128)
    have h32 := hw128.of_dvd (by decide : 32 ∣ 128)
    dsimp [Nat.ModEq] at hw128 h8 h32
    omega
  obtain ⟨x,y,z,hs⟩ := three hsame
  have hxy : x^2 ≠ y^2 := by intro h; exact neq_repeat (x:=x) (y:=z) hw25 (by omega)
  have hxz : x^2 ≠ z^2 := by intro h; exact neq_repeat (x:=x) (y:=y) hw25 (by omega)
  have hyz : y^2 ≠ z^2 := by intro h; exact neq_repeat (x:=y) (y:=x) hw25 (by omega)
  have hba' : b^2 < a^2 := by gcongr
  have hx : x^2 < b^2 := by omega
  have hy : y^2 < b^2 := by omega
  have hz : z^2 < b^2 := by omega
  refine ⟨{a^2,b^2,x^2,y^2,z^2},?_,?_,?_⟩
  · intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h|h|h|h|h <;> subst t <;> exact ⟨_,rfl⟩
  · exact card_le_five
  · simp [Ne.symm hba'.ne,hba'.ne',hxy,hxz,hyz,hx.ne',hy.ne',hz.ne',
      (hx.trans hba').ne',(hy.trans hba').ne',(hz.trans hba').ne']
    omega

end Distinct338

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H2 := Distinct338.complete
