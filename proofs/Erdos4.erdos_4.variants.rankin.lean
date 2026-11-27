import FormalConjectures.ErdosProblems.«4»

/-!
Rankin gaps in dyadic blocks of prime indices.

The sieve below is Marcus Buffett's completion of the OpenAI partial covering
argument (open-math-agents PR #2593). The excerpt is from
https://github.com/openai/LongGapsBetweenPrimes/tree/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b.
The original license follows. The
logarithm comparison and the conversion of a composite interval into a gap
are from senamakel's reduction in PR #2097. We translate the covering to
just after the Nth prime to put a large gap in each large block [N, 2N].
-/
/-
# Rankin's covering by small primes

Apply the partial covering lemma at x = y/(16 log y). Chebyshev's lower
bound supplies more unused primes up to y than there are surviving
offsets. Assign one prime to each survivor, then combine the residues
with the Chinese remainder theorem.

The partial covering estimates are excerpted from OpenAI's
LongGapsBetweenPrimes.lean, commit 03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b.
Their Apache 2.0 license is reproduced below.
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
namespace LongGapsBetweenPrimes
noncomputable section

/-- The initial zero-residue sieve leaves only primes and z-smooth integers. -/
theorem prime_or_smooth_of_survives {n H : ℕ} {x w z : ℝ}
    (hn : 1 ≤ n) (hnH : n ≤ H) (hx : 0 < x) (hsmall : 2 * (H : ℝ) < x * w)
    (hsurvives : ∀ p : ℕ, p.Prime → ((p : ℝ) ≤ w ∨ (z < p ∧ (p : ℝ) ≤ x / 2)) → ¬p ∣ n) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z := by
  by_cases hprime : n.Prime
  · exact Or.inl hprime
  right
  intro p hp hpn
  by_contra! hpz
  have hpbig : x / 2 < (p : ℝ) := by
    by_contra! hpx
    exact hsurvives p hp (Or.inr ⟨hpz, hpx⟩) hpn
  obtain ⟨k, rfl⟩ := hpn
  have hk1 : k ≠ 1 := by
    intro hk
    simp [hk, hp] at hprime
  obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
  have hqn : q ∣ p * k := dvd_mul_of_dvd_right hqk p
  have hqbig : w < (q : ℝ) := by
    by_contra! hqw
    exact hsurvives q hq (Or.inl hqw) hqn
  have hkn : q ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero (by rintro rfl; simp at hn)) hqk
  have hpkH : (p : ℝ) * k ≤ H := by exact_mod_cast hnH
  have hqk' : (q : ℝ) ≤ k := by exact_mod_cast hkn
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  nlinarith [mul_le_mul_of_nonneg_left hqk' hp0,
    mul_lt_mul_of_pos_right hpbig hq0,
    mul_lt_mul_of_pos_left hqbig hx]

/-- Elements of `S` avoiding the selected residue classes. -/
def survivors (S ps : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  S.filter fun n => ∀ p ∈ ps, n % p ≠ a p

/-- The greedy product bound in (2.1), before applying Mertens' estimate. -/
theorem greedy_residue_classes (S ps : Finset ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤ (S.card : ℝ) * ∏ p ∈ ps, (1 - 1 / (p : ℝ)) := by
  classical
  induction ps using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, by simp, by simp [survivors]⟩
  | @insert p ps hp ih =>
      have hp0 : 0 < p := hpos p (Finset.mem_insert_self p ps)
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
      obtain ⟨a, ha, hcard⟩ := ih (fun q hq => hpos q (Finset.mem_insert_of_mem hq))
      let T := survivors S ps a
      have hsum : (∑ r ∈ Finset.range p,
          ((T.filter fun n => n % p = r).card : ℝ)) = T.card := by
        exact_mod_cast (Finset.card_eq_sum_card_fiberwise
          (f := fun n => n % p) (s := T) (t := Finset.range p)
          (by intro n _; exact Finset.mem_range.mpr (Nat.mod_lt n hp0))).symm
      obtain ⟨r, hr, hlarge⟩ : ∃ r ∈ Finset.range p,
          (T.card : ℝ) / p ≤ ((T.filter fun n => n % p = r).card : ℝ) := by
        apply Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr hp0.ne')
        rw [hsum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact le_of_eq (by field_simp)
      have hsplit : ((T.filter fun n => n % p = r).card : ℝ) +
          ((T.filter fun n => n % p ≠ r).card : ℝ) = T.card := by
        exact_mod_cast T.card_filter_add_card_filter_not (fun n => n % p = r)
      have hstep : ((T.filter fun n => n % p ≠ r).card : ℝ) ≤
          (T.card : ℝ) * (1 - 1 / (p : ℝ)) := by
        rw [div_eq_mul_inv] at hlarge
        simp only [one_div]
        nlinarith
      refine ⟨Function.update a p r, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · simpa using Finset.mem_range.mp hr
        · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hq hp)] using ha q hq
      · have hsurvivors : survivors S (insert p ps) (Function.update a p r) =
            T.filter (fun n => n % p ≠ r) := by
          have hupdate : ∀ q ∈ ps, Function.update a p r q = a q := by
            intro q hq
            exact Function.update_of_ne (ne_of_mem_of_not_mem hq hp) r a
          ext n
          simp (config := { contextual := true }) only [survivors, Finset.mem_filter,
            Finset.mem_insert, forall_eq_or_imp, Function.update_self, T, hupdate]
          tauto
        rw [hsurvivors, Finset.prod_insert hp]
        calc
          _ ≤ (T.card : ℝ) * (1 - 1 / (p : ℝ)) := hstep
          _ ≤ ((S.card : ℝ) * ∏ q ∈ ps, (1 - 1 / (q : ℝ))) *
              (1 - 1 / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard (by
              have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
              exact sub_nonneg.mpr ((div_le_one hpR).mpr this))
          _ = _ := by ring

/-- The logarithms of distinct prime divisors sum to at most `log n`. -/
lemma sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by
  have hfilter : N.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1.2, h.2, hn.ne'⟩,
      fun h => ⟨⟨(Nat.le_of_dvd hn h.2.1).trans hnN, h.1⟩, h.2.1⟩⟩
  rw [← Finset.sum_filter, hfilter, ← Real.log_prod (fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp =>
      Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hp).1.pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- An elementary upper bound for the logarithmically weighted prime harmonic sum. -/
theorem sum_prime_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount (p : ℕ) (_hp : p ∈ N.primesLE) :
      (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
      (Nat.sub_one_lt_floor ((N : ℝ) / p)).le
  have hsum : (∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.range N,
          if p ∣ n + 1 then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Nat.card_multiples N p, ← Finset.sum_boole]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = ∑ n ∈ Finset.range N, ∑ p ∈ N.primesLE,
          if p ∣ n + 1 then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
        exact (sum_log_prime_divisors_le_log (by omega : 0 < n + 1) hnN).trans
          (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log N := by simp
  have hlower : (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / p) -
      Chebyshev.theta N ≤ (N : ℝ) * Real.log N := by
    apply le_trans _ hsum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_right (hcount p hp)
      (Nat.mem_primesLE.mp hp).2.log_pos.le
    calc
      (N : ℝ) * (Real.log p / p) - Real.log p =
        ((N : ℝ) / p - 1) * Real.log p := by ring
      _ ≤ _ := h
  have htheta := Chebyshev.theta_le_log4_mul_x hNr.le
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/-- The finite Euler product over primes at most N. -/
def eulerProduct (N : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹

/-- The multiplicative weight `n ↦ n ^ (-σ)`. -/
def natPowerHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The weighted sum over smooth numbers is bounded by the finite Euler product. -/
lemma sum_smooth_le_eulerProduct {N : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ eulerProduct N σ := by
  classical
  have hprime {p : ℕ} (hp : p.Prime) : ‖natPowerHom σ p‖ < 1 := by
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)
  have hsum :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := natPowerHom σ) hprime (N + 1)).2
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum

/-- The lower half of the weak Mertens product estimate. -/
theorem log_le_eulerProduct_one (N : ℕ) : Real.log N ≤ eulerProduct N 1 := by
  have h := sum_smooth_le_eulerProduct (N := N) (by norm_num : (0 : ℝ) < 1)
    (Finset.Icc 1 N) (fun n hn => Nat.mem_smoothNumbers_of_lt
      (by have := Finset.mem_Icc.mp hn; omega)
      (by have := Finset.mem_Icc.mp hn; omega))
  have hlog := log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg _)
  rw [Nat.floor_natCast, harmonic_eq_sum_Icc] at hlog
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlog
  simp only [Real.rpow_neg_one] at h
  exact hlog.trans h

/-- The elementary zeta-function bound obtained by integrating t^(-σ). -/
theorem tsum_succ_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hexp : -σ < -1 := neg_lt_neg hσ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num) hx)) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num), Nat.cast_one, Real.one_rpow,
    show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq] at htail
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hexp)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  apply add_le_add le_rfl
  simpa only [Nat.cast_add, Nat.cast_one] using htail

/-- For `σ > 1`, the finite Euler product is at most `1 + 1 / (σ - 1)`. -/
lemma eulerProduct_le_zeta_bound {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    eulerProduct N σ ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ))
    ((N + 1).smoothNumbers) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
  have hseries := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natPowerHom σ) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-σ)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
        (by linarith)) (N + 1)).2
  change HasSum (fun n : (N + 1).smoothNumbers => (n.val : ℝ) ^ (-σ))
    (eulerProduct N σ) at hseries
  rw [hseries.tsum_eq] at ht
  rw [hs.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add] at ht
  simp only [Nat.cast_add, Nat.cast_one] at ht
  exact ht.trans (tsum_succ_rpow_le hσ)

/-- Compare an Euler factor at exponent one with its shift by `r`. -/
lemma euler_factor_comparison {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    (1 - p ^ (-(1 : ℝ)))⁻¹ ≤
      (1 - p ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hden : 0 < 1 - p ^ (-(1 + r)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  have hlog : 0 ≤ r * Real.log p := mul_nonneg hr (Real.log_pos hp1).le
  have hpow : 1 - p ^ (-r) ≤ r * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * -r)
    nlinarith
  rw [Real.rpow_neg_one, ← div_eq_inv_mul]
  apply (le_div_iff₀ hden).mpr
  rw [← div_eq_inv_mul]
  calc
    (1 - p ^ (-(1 + r))) / (1 - p⁻¹) =
        1 + (1 - p ^ (-r)) / (p - 1) := by
      rw [neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
      field_simp
      ring
    _ ≤ 1 + (r * Real.log p) / (p - 1) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hpow hpm.le)
    _ ≤ 1 + 2 * r * Real.log p / p := by
      apply add_le_add le_rfl
      apply (div_le_div_iff₀ hpm hp0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hlog]
    _ ≤ Real.exp (2 * r * Real.log p / p) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * r * Real.log p / p)

/-- Moving the Euler product to the right of its pole has bounded cost. -/
theorem eulerProduct_comparison (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    eulerProduct N 1 ≤ eulerProduct N (1 + r) *
      Real.exp (2 * r * ∑ p ∈ N.primesLE, Real.log p / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE,
        (1 - (p : ℝ) ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt)
          (by norm_num : -(1 : ℝ) < 0)).le
      · intro p hp
        exact euler_factor_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) hr
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- An explicit weak Mertens upper bound, sufficient throughout the proof. -/
theorem eulerProduct_one_le {N : ℕ} (hN : 2 ≤ N) :
    eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ 2 * Real.log N := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log N := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hcost : 2 * (Real.log N)⁻¹ * (∑ p ∈ N.primesLE, Real.log p / p) ≤ 6 := by
    calc
      _ ≤ 2 * (Real.log N)⁻¹ * (3 * Real.log N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 6 := by field_simp; norm_num
  have hzeta : eulerProduct N (1 + (Real.log N)⁻¹) ≤ 1 + Real.log N := by
    simpa using eulerProduct_le_zeta_bound
      (lt_add_of_pos_right 1 (inv_pos.mpr hlog)) N
  calc
    _ ≤ eulerProduct N (1 + (Real.log N)⁻¹) *
        Real.exp (2 * (Real.log N)⁻¹ * ∑ p ∈ N.primesLE, Real.log p / p) :=
      eulerProduct_comparison N (inv_nonneg.mpr hlog.le)
    _ ≤ (1 + Real.log N) * Real.exp 6 :=
      mul_le_mul hzeta (Real.exp_le_exp.mpr hcost) (Real.exp_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

/-- The finite Euler product is positive at every positive exponent. -/
lemma eulerProduct_pos (N : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < eulerProduct N σ := by
  apply Finset.prod_pos
  intro p hp
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)))

/-- Primes in the interval `(Z, Y]`. -/
def auxiliaryPrimes (Z Y : ℕ) : Finset ℕ := Y.primesLE \ Z.primesLE

/-- Every auxiliary prime is prime. -/
lemma auxiliaryPrimes_prime {Z Y p : ℕ} (hp : p ∈ auxiliaryPrimes Z Y) : p.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2

/-- Membership in the auxiliary primes means primality and `Z < p ≤ Y`. -/
lemma mem_auxiliaryPrimes {Z Y p : ℕ} :
    p ∈ auxiliaryPrimes Z Y ↔ p.Prime ∧ Z < p ∧ p ≤ Y := by
  simp only [auxiliaryPrimes, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or, not_le]
  tauto

/-- Split the Euler product at the lower cutoff `Z`. -/
lemma auxiliary_euler_factorization {Z Y : ℕ} (hZY : Z ≤ Y) (σ : ℝ) :
    (∏ p ∈ auxiliaryPrimes Z Y, (1 - (p : ℝ) ^ (-σ))⁻¹) * eulerProduct Z σ =
      eulerProduct Y σ := Finset.prod_sdiff (Nat.primesLE_mono hZY)

/-- An explicit absolute moment bound from a lower bound on the normalizer. -/
def absoluteMomentBound (b : ℝ) : ℝ :=
  Real.exp 2 + 2 * Real.exp 6 * Real.exp (6 * Real.exp 2) / b

/-- The absolute moment bound divided by the normalizer lower bound. -/
def coefficientControl (b : ℝ) : ℝ := absoluteMomentBound b / b

/-- The absolute moment bound is positive for positive `b`. -/
lemma absoluteMomentBound_pos {b : ℝ} (hb : 0 < b) : 0 < absoluteMomentBound b := by
  unfold absoluteMomentBound
  positivity

/-- The coefficient control constant is positive for positive `b`. -/
lemma coefficientControl_pos {b : ℝ} (hb : 0 < b) : 0 < coefficientControl b :=
  div_pos (absoluteMomentBound_pos hb) hb

/-- A fixed positive lower bound used for the sieve normalizer. -/
def normalizerLower : ℝ := 1 / (100 * Real.exp 6)

/-- The fixed normalizer lower bound is positive. -/
lemma normalizerLower_pos : 0 < normalizerLower := by
  unfold normalizerLower
  positivity

/-- A common constant controlling the coefficient moments. -/
def weightConstant : ℝ :=
  1 + absoluteMomentBound normalizerLower + coefficientControl normalizerLower

/-- The common coefficient constant exceeds one. -/
lemma weightConstant_gt_one : 1 < weightConstant := by
  unfold weightConstant
  linarith [absoluteMomentBound_pos normalizerLower_pos,
    coefficientControl_pos normalizerLower_pos]

/-- The density threshold for simultaneously hitting all root families. -/
def sieveDelta : ℝ := 1 / (64 * weightConstant)

/-- The simultaneous-root density threshold is positive. -/
lemma sieveDelta_pos : 0 < sieveDelta := by
  exact one_div_pos.mpr (mul_pos (by norm_num) (zero_lt_one.trans weightConstant_gt_one))

/-- The simultaneous-root density threshold is less than one half. -/
lemma sieveDelta_lt_half : sieveDelta < 1 / 2 := by
  unfold sieveDelta
  apply one_div_lt_one_div_of_lt (by norm_num)
  linarith [weightConstant_gt_one]

/-- A uniform geometric factor for the smooth-number estimate. -/
def smoothEulerConstant : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

/-- The smooth Euler constant is positive. -/
lemma smoothEulerConstant_pos : 0 < smoothEulerConstant := by
  exact inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))

/-- The scale constant used to choose the smoothness cutoff and tilt. -/
def smoothScaleConstant : ℝ := 3 * smoothEulerConstant + 10

/-- The smoothness scale constant is positive. -/
lemma smoothScaleConstant_pos : 0 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- Bound the cost of shifting an Euler factor to exponent `1 - t`. -/
lemma euler_factor_left_comparison {p t : ℝ} (hp : 2 ≤ p) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 - p ^ (-(1 - t)))⁻¹ ≤ (1 - p ^ (-(1 : ℝ)))⁻¹ *
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hpow : p ^ (-(1 - t)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ p ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by norm_num)
  have hcden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hden : 0 < 1 - p ^ (-(1 - t)) := by linarith
  have hnum : 0 ≤ p ^ t - 1 := sub_nonneg.mpr (Real.one_le_rpow hp1 ht)
  have hsplit : p ^ (-(1 - t)) = p ^ t / p := by
    rw [show -(1 - t) = t + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one,
      div_eq_mul_inv]
  have he : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ =
      1 + ((p ^ t - 1) / p) / (1 - p ^ (-(1 - t))) := by
    have hpt : p ^ t < p := (div_lt_one hp0).mp (by rw [← hsplit]; linarith)
    rw [hsplit]
    field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hpt)]
    ring
  have hratio : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ ≤
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
    rw [he]
    calc
      _ ≤ 1 + ((p ^ t - 1) / p) / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
        exact add_le_add le_rfl
          (div_le_div_of_nonneg_left (div_nonneg hnum hp0.le) hcden (by linarith))
      _ = 1 + smoothEulerConstant * (p ^ t - 1) / p := by
        unfold smoothEulerConstant
        ring
      _ ≤ _ := by simpa only [add_comm] using
        Real.add_one_le_exp (smoothEulerConstant * (p ^ t - 1) / p)
  rw [Real.rpow_neg_one, inv_mul_eq_div]
  apply (le_div_iff₀ (show 0 < 1 - p⁻¹ by
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith)))).mpr
  simpa only [mul_comm] using hratio

/-- Bound the cost of shifting the Euler product to exponent `1 - t`. -/
lemma eulerProduct_left_comparison (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (smoothEulerConstant * ∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ *
        Real.exp (smoothEulerConstant * ((p : ℝ) ^ t - 1) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)).le)
      · intro p hp
        exact euler_factor_left_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) ht ht'
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- A secant bound controls `p ^ t - 1` using the ratio `log p / log z`. -/
lemma rpow_secant_log {p z t : ℝ} (hp : 1 ≤ p) (hpz : p ≤ z) (hz : 1 < z)
    (ht : 0 ≤ t) : p ^ t - 1 ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) := by
  rcases ht.eq_or_lt with rfl | _
  · simp
  have hlogz := Real.log_pos hz
  have hratio : Real.log p / Real.log z ≤ 1 :=
    (div_le_one hlogz).mpr (Real.log_le_log (zero_lt_one.trans_le hp) hpz)
  have h := convexOn_exp.2 (Set.mem_univ (t * Real.log z)) (Set.mem_univ 0)
    (div_nonneg (Real.log_nonneg hp) hlogz.le) (sub_nonneg.mpr hratio)
    (show Real.log p / Real.log z + (1 - Real.log p / Real.log z) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have harg : Real.log p / Real.log z * (t * Real.log z) = Real.log p * t := by
    field_simp
  rw [harg, ← Real.rpow_def_of_pos (zero_lt_one.trans_le hp)] at h
  linarith

/-- Bound the shifted Euler product using the tilt and the largest prime cutoff. -/
lemma eulerProduct_left_bound {N : ℕ} {z t : ℝ} (hN : 2 ≤ N) (hNz : (N : ℝ) ≤ z)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (3 * smoothEulerConstant * Real.exp (t * Real.log z)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 1 < z := by linarith
  have hlogz := Real.log_pos hz
  have hlogN : Real.log N ≤ Real.log z :=
    Real.log_le_log (by linarith) hNz
  have hlog4 : Real.log 4 ≤ 2 * Real.log z := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ z ^ 2 by nlinarith)
  have hlogs : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log z := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hsum : (∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) ≤
      3 * Real.exp (t * Real.log z) := by
    calc
      _ ≤ ∑ p ∈ N.primesLE,
          (Real.log p / p) * (Real.exp (t * Real.log z) / Real.log z) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
        calc
          _ ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) / p :=
            div_le_div_of_nonneg_right
              (rpow_secant_log (by exact_mod_cast hp.one_lt.le)
                ((by exact_mod_cast hpN : (p : ℝ) ≤ N).trans hNz) hz ht)
              (Nat.cast_nonneg p)
          _ ≤ (Real.log p / Real.log z) * Real.exp (t * Real.log z) / p := by
            gcongr
            exact sub_le_self _ zero_le_one
          _ = _ := by ring
      _ = (∑ p ∈ N.primesLE, Real.log p / p) *
          (Real.exp (t * Real.log z) / Real.log z) := (Finset.sum_mul ..).symm
      _ ≤ (3 * Real.log z) * (Real.exp (t * Real.log z) / Real.log z) :=
        mul_le_mul_of_nonneg_right hlogs (by positivity)
      _ = 3 * Real.exp (t * Real.log z) := by field_simp
  apply (eulerProduct_left_comparison N ht ht').trans
  apply mul_le_mul_of_nonneg_left _ (eulerProduct_pos N (by norm_num)).le
  apply Real.exp_le_exp.mpr
  simpa [mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hsum smoothEulerConstant_pos.le

/-- A finite Euler-product bound for the count of smooth integers up to `H`. -/
lemma smooth_count_rankin {N H : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 H)
    (hsmooth : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (S.card : ℝ) ≤ (H : ℝ) ^ σ * eulerProduct N σ := by
  have hsum := sum_smooth_le_eulerProduct hσ S hsmooth
  have hpoint (n : ℕ) (hn : n ∈ S) : (1 : ℝ) ≤ (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
    have hnI := Finset.mem_Icc.mp (hS hn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnH : (n : ℝ) ≤ H := by exact_mod_cast hnI.2
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hn0 σ)).mpr
      (by simpa only [one_mul] using Real.rpow_le_rpow hn0.le hnH hσ.le)
  calc
    (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := Finset.sum_le_sum hpoint
    _ = (H : ℝ) ^ σ * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg H) σ)

/-- The logarithmic smoothness cutoff in the covering construction. -/
def coverLogZ (x : ℝ) : ℝ :=
  Real.log x * Real.log (Real.log (Real.log x)) /
    (smoothScaleConstant * Real.log (Real.log x))

/-- The smoothness cutoff in the covering construction, rounded down to an integer. -/
def coverZ (x : ℝ) : ℕ := ⌊Real.exp (coverLogZ x)⌋₊

/-- The small-prime cutoff, given by the integer part of `(log x)^4`. -/
def coverW (x : ℝ) : ℕ := ⌊(Real.log x) ^ 4⌋₊

/-- The Rankin tilt used to count smooth integers. -/
def coverTilt (x : ℝ) : ℝ := smoothScaleConstant * Real.log (Real.log x) / Real.log x

/-- The integer interval length targeted by the covering argument. -/
def coverLength (η x : ℝ) : ℕ :=
  ⌊η * x * Real.log x ^ 2 * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ^ 2⌋₊

/-- The smoothness scale constant exceeds ten. -/
lemma smoothScaleConstant_gt_ten : 10 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- The covering tilt times the logarithmic cutoff equals the third iterated logarithm. -/
lemma coverTilt_mul_coverLogZ {x : ℝ} (hx : 1 < x) (hlog : 1 < Real.log x) :
    coverTilt x * coverLogZ x = Real.log (Real.log (Real.log x)) := by
  have hl1 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hl2 : Real.log (Real.log x) ≠ 0 := (Real.log_pos hlog).ne'
  unfold coverTilt coverLogZ
  field_simp [hl1, hl2, smoothScaleConstant_pos.ne']

/-- The size, ordering, and tilt bounds for the covering parameters hold eventually. -/
lemma eventually_cover_parameters : ∀ᶠ x : ℝ in Filter.atTop,
    2 ≤ x ∧ 2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) ∧ 1 ≤ Real.log (Real.log (Real.log x)) ∧
    4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x ∧
    0 ≤ coverTilt x ∧ coverTilt x ≤ 1 / 2 ∧
    4 * Real.log (Real.log x) ≤ coverLogZ x ∧ coverLogZ x ≤ Real.log x := by
  have hlog := Real.tendsto_log_atTop
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := hlog.comp hlog
  have hlogloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x)))
      Filter.atTop Filter.atTop := hlog.comp hloglog
  have hsmall : Filter.Tendsto
      (fun x : ℝ => 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [mul_div_assoc] using ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      hlog).const_mul (4 * smoothScaleConstant)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hlog.eventually_ge_atTop 2,
    hloglog.eventually_ge_atTop 1, hlogloglog.eventually_ge_atTop 1,
    hsmall.eventually_le_const zero_lt_one] with x hx hl hll hlll hsmall
  have hl0 : 0 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hquad : 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x :=
    (div_le_one hl0).mp hsmall
  have hlinear : 4 * smoothScaleConstant * Real.log (Real.log x) ≤ Real.log x := by
    calc
      _ ≤ 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith)
          (mul_nonneg (by norm_num) smoothScaleConstant_pos.le)
      _ ≤ _ := hquad
  refine ⟨hx, hl, hll, hlll, hquad, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg smoothScaleConstant_pos.le hll0.le) hl0.le
  · unfold coverTilt
    apply (div_le_iff₀ hl0).mpr
    nlinarith
  · unfold coverLogZ
    apply (le_div_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    calc
      _ = 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 := by ring
      _ ≤ Real.log x := hquad
      _ ≤ Real.log x * Real.log (Real.log (Real.log x)) :=
        le_mul_of_one_le_right hl0.le hlll
  · unfold coverLogZ
    apply (div_le_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    apply mul_le_mul_of_nonneg_left _ hl0.le
    calc
      _ ≤ Real.log (Real.log x) := by
        linarith [Real.log_le_sub_one_of_pos hll0]
      _ ≤ smoothScaleConstant * Real.log (Real.log x) :=
        le_mul_of_one_le_left hll0.le (by linarith [smoothScaleConstant_gt_ten])

/-- The small-prime cutoff does not exceed the smoothness cutoff. -/
lemma coverW_le_coverZ {x : ℝ} (hx : 1 < x)
    (hz : 4 * Real.log (Real.log x) ≤ coverLogZ x) : coverW x ≤ coverZ x := by
  apply Nat.floor_mono
  calc
    (Real.log x) ^ 4 = Real.exp ((4 : ℕ) * Real.log (Real.log x)) := by
      rw [Real.exp_nat_mul, Real.exp_log (Real.log_pos hx)]
    _ ≤ Real.exp (coverLogZ x) := Real.exp_le_exp.mpr hz

/-- The smoothness cutoff is at most the integer part of `x`. -/
lemma coverZ_le_floor {x : ℝ} (hx : 0 < x) (hz : coverLogZ x ≤ Real.log x) : coverZ x ≤ ⌊x⌋₊ := by
  exact Nat.floor_mono ((Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hx))

/-- The small-prime cutoff is at least two when `log x ≥ 2`. -/
lemma coverW_ge_two {x : ℝ} (hL : 2 ≤ Real.log x) : 2 ≤ coverW x := by
  apply Nat.le_floor
  exact (by norm_num : (2 : ℝ) ≤ 2 ^ 4).trans
    (pow_le_pow_left₀ (by norm_num) hL 4)

/-- Eventually, at most `H / (log x)^3` integers up to `H` are `coverZ x`-smooth. -/
lemma eventually_smooth_count : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H →
    (∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x) →
    (S.card : ℝ) ≤ (H : ℝ) / Real.log x ^ 3 := by
  filter_upwards [eventually_cover_parameters,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2]
    with x hparameters hlarge
  simp only [Function.comp_apply] at hlarge
  obtain ⟨hx, hl, hll, _, _, ht, ht', hZlow, hZhigh⟩ := hparameters
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hl1 : 1 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hZ : 2 ≤ coverZ x :=
    (coverW_ge_two hl).trans (coverW_le_coverZ hx1 hZlow)
  have hlogZ : Real.log (coverZ x) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < coverZ x))
      ((by exact_mod_cast coverZ_le_floor hx0 hZhigh : (coverZ x : ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le hx0.le))
  have hEulerOne : eulerProduct (coverZ x) 1 ≤
      Real.exp (7 * Real.log (Real.log x)) := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log (coverZ x)) := eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * Real.log x ^ 2 := by
        gcongr
        nlinarith
      _ = Real.exp (6 + 2 * Real.log (Real.log x)) := by
        rw [Real.exp_add, show Real.exp (2 * Real.log (Real.log x)) =
          Real.log x ^ 2 by
            simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 2]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hEuler : eulerProduct (coverZ x) (1 - coverTilt x) ≤
      Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) := by
    have hbound := eulerProduct_left_bound hZ
      (Nat.floor_le (Real.exp_pos (coverLogZ x)).le) ht ht'
    rw [Real.log_exp, coverTilt_mul_coverLogZ hx1 hl1, Real.exp_log hll0] at hbound
    calc
      _ ≤ eulerProduct (coverZ x) 1 *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := hbound
      _ ≤ Real.exp (7 * Real.log (Real.log x)) *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        unfold smoothScaleConstant
        ring
  intro H hxH S hS hsmooth
  have hH0 : 0 < (H : ℝ) := hx0.trans_le hxH
  have hpower : (H : ℝ) ^ (1 - coverTilt x) ≤
      H * Real.exp (-smoothScaleConstant * Real.log (Real.log x)) := by
    rw [sub_eq_add_neg, Real.rpow_add hH0, Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ hH0.le
    calc
      _ ≤ x ^ (-coverTilt x) := Real.rpow_le_rpow_of_nonpos hx0 hxH (neg_nonpos.mpr ht)
      _ = _ := by
        rw [Real.rpow_def_of_pos hx0]
        congr 1
        unfold coverTilt
        field_simp
  calc
    (S.card : ℝ) ≤ (H : ℝ) ^ (1 - coverTilt x) *
        eulerProduct (coverZ x) (1 - coverTilt x) := by
      apply smooth_count_rankin (by linarith) S hS
      intro n hn
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp (hS hn)).1; omega
      apply Nat.mem_smoothNumbers.mpr
      refine ⟨hn0, ?_⟩
      intro p hp
      obtain ⟨hp, hpn⟩ := (Nat.mem_primeFactorsList hn0).mp hp
      exact Nat.lt_succ_of_le (hsmooth n hn p hp hpn)
    _ ≤ (H * Real.exp (-smoothScaleConstant * Real.log (Real.log x))) *
        Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) :=
      mul_le_mul hpower hEuler (eulerProduct_pos _ (by linarith)).le (by positivity)
    _ = (H : ℝ) / Real.log x ^ 3 := by
      rw [mul_assoc, ← Real.exp_add,
        show -smoothScaleConstant * Real.log (Real.log x) +
          (smoothScaleConstant - 3) * Real.log (Real.log x) =
          -(3 * Real.log (Real.log x)) by ring,
        Real.exp_neg, show Real.exp (3 * Real.log (Real.log x)) = Real.log x ^ 3 by
          simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 3,
        div_eq_mul_inv]

/-- A logarithmic upper bound for the product of greedy survival factors. -/
lemma greedy_product_le {W Z : ℕ} (hW : 2 ≤ W) (hWZ : W ≤ Z) :
    (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) ≤
      Real.exp 6 * (1 + Real.log W) / Real.log Z := by
  have hprod : 0 < ∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    simpa only [one_div] using sub_pos.mpr
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt))
  have hfactor := auxiliary_euler_factorization hWZ 1
  simp only [Real.rpow_neg_one] at hfactor
  rw [Finset.prod_inv_distrib, inv_mul_eq_div] at hfactor
  simp only [← one_div] at hfactor
  have hcancel := (div_eq_iff hprod.ne').mp hfactor
  have hlog : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) * eulerProduct Z 1 :=
      mul_le_mul_of_nonneg_left (log_le_eulerProduct_one Z) hprod.le
    _ = eulerProduct W 1 := (mul_comm _ _).trans hcancel.symm
    _ ≤ Real.exp 6 * (1 + Real.log W) := eulerProduct_one_le hW

/-- The chosen cutoffs give an explicit bound for the greedy survival product. -/
lemma eventually_greedy_product_bound : ∀ᶠ x : ℝ in Filter.atTop,
    (∏ p ∈ auxiliaryPrimes (coverW x) (coverZ x), (1 - 1 / (p : ℝ))) ≤
      10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
        (Real.log x * Real.log (Real.log (Real.log x))) := by
  filter_upwards [eventually_cover_parameters] with x hparameters
  obtain ⟨hx, hl, hll, hlll, _, _, _, hZlow, _⟩ := hparameters
  have hx1 : 1 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hlll0 : 0 < Real.log (Real.log (Real.log x)) := by linarith
  have hW : 2 ≤ coverW x := coverW_ge_two hl
  have hWZ : coverW x ≤ coverZ x := coverW_le_coverZ hx1 hZlow
  have hW0 : 0 < (coverW x : ℝ) := by exact_mod_cast (by omega : 0 < coverW x)
  have hnum : 1 + Real.log (coverW x) ≤ 5 * Real.log (Real.log x) := by
    have hlogW : Real.log (coverW x) ≤ 4 * Real.log (Real.log x) := by
      calc
        _ ≤ Real.log (Real.log x ^ 4) :=
          Real.log_le_log hW0 (Nat.floor_le (by positivity))
        _ = _ := by rw [Real.log_pow]; norm_num
    linarith
  have hlogZ : coverLogZ x / 2 ≤ Real.log (coverZ x) := by
    have hexp : 2 ≤ Real.exp (coverLogZ x / 2) := by
      linarith [Real.add_one_le_exp (coverLogZ x / 2)]
    have hsquare : Real.exp (coverLogZ x) = Real.exp (coverLogZ x / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add, add_halves]
    have hfloor : Real.exp (coverLogZ x) < (coverZ x : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    calc
      _ = Real.log (Real.exp (coverLogZ x / 2)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by nlinarith)
  calc
    _ ≤ Real.exp 6 * (1 + Real.log (coverW x)) / Real.log (coverZ x) :=
      greedy_product_le hW hWZ
    _ ≤ Real.exp 6 * (5 * Real.log (Real.log x)) / (coverLogZ x / 2) := by
      gcongr
      linarith
    _ = _ := by
      unfold coverLogZ
      field_simp [smoothScaleConstant_pos.ne', hl0.ne', hll0.ne', hlll0.ne']
      ring

/-- Primes assigned residue zero before the greedy covering step. -/
def zeroCoverPrimes (x : ℝ) : Finset ℕ :=
  (coverW x).primesLE ∪ (⌊x / 2⌋₊.primesLE \ (coverZ x).primesLE)

/-- Integers in `[1, H]` surviving the initial zero-residue sieve. -/
def zeroSurvivors (x : ℝ) (H : ℕ) : Finset ℕ :=
  survivors (Finset.Icc 1 H) (zeroCoverPrimes x) (fun _ => 0)

/-- Combine a zero-residue sieve with greedy choices on a disjoint set of moduli. -/
lemma combine_greedy_residues (S ps₀ ps₁ ps : Finset ℕ)
    (h₀ : ps₀ ⊆ ps) (h₁ : ps₁ ⊆ ps) (hdisj : Disjoint ps₀ ps₁)
    (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤
        ((survivors S ps₀ (fun _ => 0)).card : ℝ) * ∏ p ∈ ps₁, (1 - 1 / (p : ℝ)) := by
  classical
  obtain ⟨b, hb, hcard⟩ := greedy_residue_classes
    (survivors S ps₀ (fun _ => 0)) ps₁ (fun p hp => hpos p (h₁ hp))
  let a : ℕ → ℕ := fun p => if p ∈ ps₁ then b p else 0
  refine ⟨a, ?_, ?_⟩
  · intro p hp
    by_cases hp₁ : p ∈ ps₁
    · simpa [a, hp₁] using hb p hp₁
    · simpa [a, hp₁] using hpos p hp
  · have hsubset : survivors S ps a ⊆
        survivors (survivors S ps₀ (fun _ => 0)) ps₁ b := by
      intro n hn
      obtain ⟨hnS, hn⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnS, ?_⟩, ?_⟩
      · intro p hp
        have hp₁ : p ∉ ps₁ := Finset.disjoint_left.mp hdisj hp
        simpa [a, hp₁] using hn p (h₀ hp)
      · intro p hp
        simpa [a, hp] using hn p (h₁ hp)
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans hcard

/-- A zero-sieve survivor is prime or has all prime factors at most the smoothness cutoff. -/
lemma zeroSurvivors_prime_or_smooth {x : ℝ} {H n : ℕ} (hx : 0 < x)
    (hsmall : 2 * (H : ℝ) < x * (coverW x : ℝ)) (hn : n ∈ zeroSurvivors x H) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x := by
  obtain ⟨hnI, hsurvives⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnH⟩ := Finset.mem_Icc.mp hnI
  have h := prime_or_smooth_of_survives hn1 hnH hx hsmall (z := (coverZ x : ℝ))
  apply Or.imp_right (fun hs p hp hpn => by exact_mod_cast hs p hp hpn) (h ?_)
  intro p hp hrange hpn
  apply hsurvives p ?_ (Nat.mod_eq_zero_of_dvd hpn)
  simp only [zeroCoverPrimes, Finset.mem_union, Finset.mem_sdiff, Nat.mem_primesLE]
  rcases hrange with hpW | ⟨hpZ, hpx⟩
  · exact Or.inl ⟨by exact_mod_cast hpW, hp⟩
  · refine Or.inr ⟨⟨Nat.le_floor hpx, hp⟩, ?_⟩
    rintro ⟨hpZ', _⟩
    exact (not_le_of_gt hpZ) (by exact_mod_cast hpZ')

/-- The small-prime cutoff exceeds `2 * (log x)^2`. -/
lemma coverW_large {x : ℝ} (hL : 2 ≤ Real.log x) :
    2 * Real.log x ^ 2 < (coverW x : ℝ) := by
  have hfloor : Real.log x ^ 4 < (coverW x : ℝ) + 1 := Nat.lt_floor_add_one _
  nlinarith [sq_nonneg (Real.log x ^ 2 - 2)]

/-- An explicit `H / log x` bound for the initial sieve's survivors. -/
lemma eventually_zeroSurvivors_bound : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → (H : ℝ) ≤ x * Real.log x ^ 2 →
      ((zeroSurvivors x H).card : ℝ) ≤ (Real.log 4 + 2) * H / Real.log x := by
  classical
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  filter_upwards [Filter.eventually_ge_atTop B, eventually_smooth_count,
    eventually_cover_parameters] with x hxB hsmooth hp
  obtain ⟨hx, hL, _, _, _, _, _, _, _⟩ := hp
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  intro H hxH hH
  have hprime := hB (H : ℝ) (hxB.trans hxH)
  rw [Nat.floor_natCast, ← Nat.primesLE_card_eq_primeCounting] at hprime
  have hlog : Real.log x ≤ Real.log (H : ℝ) := Real.log_le_log hx0 hxH
  have hC : 0 < Real.log 4 + 1 := by
    have h := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hprime := hprime.trans (div_le_div_of_nonneg_left (by positivity) hL0 hlog)
  have hsmall : 2 * (H : ℝ) < x * (coverW x : ℝ) := by
    have hw := mul_lt_mul_of_pos_left (coverW_large hL) hx0
    nlinarith
  let smooth : Finset ℕ := (Finset.Icc 1 H).filter
    (fun n => ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x)
  have hsub : zeroSurvivors x H ⊆ H.primesLE ∪ smooth := by
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    rcases zeroSurvivors_prime_or_smooth hx0 hsmall hn with hpn | hsn
    · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hnI).2, hpn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hsn⟩)
  have hcard : ((zeroSurvivors x H).card : ℝ) ≤ (H.primesLE.card : ℝ) + smooth.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le H.primesLE smooth)
  have hsm := hsmooth H hxH smooth (Finset.filter_subset _ _)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  have hpow : Real.log x ≤ Real.log x ^ 3 := by
    have hsq : (1 : ℝ) ≤ Real.log x ^ 2 := one_le_pow₀ (by linarith : 1 ≤ Real.log x)
    have hm := mul_le_mul_of_nonneg_left hsq hL0.le
    nlinarith
  have hdiv : (H : ℝ) / Real.log x ^ 3 ≤ (H : ℝ) / Real.log x :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hL0 hpow
  calc
    _ ≤ (H.primesLE.card : ℝ) + smooth.card := hcard
    _ ≤ (Real.log 4 + 1) * H / Real.log x + (H : ℝ) / Real.log x :=
      add_le_add hprime (hsm.trans hdiv)
    _ = _ := by ring

/-- The real scale of the interval covered by the sieve. -/
def coverScale (x : ℝ) : ℝ :=
  x * Real.log x ^ 2 * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ^ 2

/-- The covering length is the integer part of `η * coverScale x`. -/
lemma coverLength_eq (η x : ℝ) : coverLength η x = ⌊η * coverScale x⌋₊ := by
  simp only [coverLength, coverScale, mul_div_assoc, mul_assoc]

/-- The constant combining the initial sieve and greedy survival bounds. -/
def coveringConstant : ℝ :=
  10 * smoothScaleConstant * Real.exp 6 * (Real.log 4 + 2)

/-- The combined covering constant is positive. -/
lemma coveringConstant_pos : 0 < coveringConstant := by
  have := smoothScaleConstant_pos
  unfold coveringConstant
  positivity

/-- A covering scale small enough to meet the short-translate density threshold. -/
def coverEta : ℝ := sieveDelta / (2 * (1 + coveringConstant))

/-- The chosen covering scale is positive. -/
lemma coverEta_pos : 0 < coverEta := by
  exact div_pos sieveDelta_pos
    (mul_pos (by norm_num) (add_pos zero_lt_one coveringConstant_pos))

/-- The chosen covering scale is at most one. -/
lemma coverEta_le_one : coverEta ≤ 1 := by
  unfold coverEta
  apply (div_le_one (by linarith [coveringConstant_pos])).mpr
  linarith [sieveDelta_lt_half, coveringConstant_pos]

/-- The combined covering bound fits within the sieve density threshold. -/
lemma coveringConstant_mul_eta_le : coveringConstant * coverEta ≤ sieveDelta := by
  have hC := coveringConstant_pos
  have hδ := sieveDelta_pos
  unfold coverEta
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hC hδ]

/-- Eventually, the rounded covering length has the required size and retains half its scale. -/
lemma eventually_coverLength_bounds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ x : ℝ in Filter.atTop, x < (coverLength η x : ℝ) ∧
      (coverLength η x : ℝ) ≤ x * Real.log x ^ 2 ∧
      (η / 2) * coverScale x ≤ (coverLength η x : ℝ) := by
  filter_upwards [eventually_cover_parameters,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 / η)] with x hp hηL
  obtain ⟨hx, hL, hLL, hLLL, hquad, _, _, _, _⟩ := hp
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := by linarith
  have hden : Real.log (Real.log x) ^ 2 ≤ Real.log x := by
    nlinarith [smoothScaleConstant_gt_ten, sq_nonneg (Real.log (Real.log x))]
  have hlower : x * Real.log x ≤ coverScale x := by
    unfold coverScale
    apply (le_div_iff₀ (sq_pos_of_pos hLL0)).mpr
    calc
      _ ≤ x * Real.log x * Real.log x :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = x * Real.log x ^ 2 := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hLLL
  have hbig : 2 * x ≤ η * coverScale x := by
    calc
      _ ≤ (Real.log x * η) * x :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).mp hηL) hx0.le
      _ = η * (x * Real.log x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower hη.le
  have hscale0 : 0 ≤ coverScale x := (by positivity : 0 ≤ x * Real.log x).trans hlower
  have hupper : η * coverScale x ≤ x * Real.log x ^ 2 := by
    calc
      _ ≤ coverScale x := mul_le_of_le_one_left hscale0 hη1
      _ ≤ _ := by
        unfold coverScale
        apply (div_le_iff₀ (sq_pos_of_pos hLL0)).mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [Real.log_le_sub_one_of_pos hLL0]
  rw [coverLength_eq]
  have hfloor := Nat.lt_floor_add_one (η * coverScale x)
  exact ⟨by linarith, (Nat.floor_le (mul_nonneg hη.le hscale0)).trans hupper,
    by linarith⟩

/-- Every prime in the zero-residue sieve is at most `x`. -/
lemma zeroCoverPrimes_subset {x : ℝ} (hx : 0 ≤ x) (hW : coverW x ≤ ⌊x⌋₊) :
    zeroCoverPrimes x ⊆ ⌊x⌋₊.primesLE := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hW, (Nat.mem_primesLE.mp hp).2⟩
  · have hm := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
    exact Nat.mem_primesLE.mpr ⟨hm.1.trans (Nat.floor_mono (by linarith : x / 2 ≤ x)), hm.2⟩

/-- The zero-residue and greedy prime sets are disjoint. -/
lemma zeroCoverPrimes_disjoint (x : ℝ) :
    Disjoint (zeroCoverPrimes x) (auxiliaryPrimes (coverW x) (coverZ x)) := by
  simp only [zeroCoverPrimes, auxiliaryPrimes, Finset.disjoint_left, Finset.mem_union,
    Finset.mem_sdiff]
  tauto

/-- For large `x`, residue classes leave at most `sieveDelta * x` integers uncovered. -/
lemma eventually_covering_residues : ∀ᶠ x : ℝ in Filter.atTop,
    ∃ a : ℕ → ℕ, (∀ p ∈ ⌊x⌋₊.primesLE, a p < p) ∧
      ((survivors (Finset.Icc 1 (coverLength coverEta x)) ⌊x⌋₊.primesLE a).card : ℝ) ≤
        sieveDelta * x := by
  classical
  filter_upwards [eventually_cover_parameters,
    eventually_coverLength_bounds coverEta_pos coverEta_le_one,
    eventually_zeroSurvivors_bound, eventually_greedy_product_bound]
    with x hparameters hlength hzero hgreedy
  obtain ⟨hx, hL, hLL, hLLL, _, _, _, hZlow, hZhigh⟩ := hparameters
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := by linarith
  have hLLL0 : 0 < Real.log (Real.log (Real.log x)) := by linarith
  have hZ := coverZ_le_floor hx0 hZhigh
  have hW := (coverW_le_coverZ (by linarith) hZlow).trans hZ
  obtain ⟨a, ha, hcard⟩ := combine_greedy_residues
    (Finset.Icc 1 (coverLength coverEta x)) (zeroCoverPrimes x)
    (auxiliaryPrimes (coverW x) (coverZ x)) ⌊x⌋₊.primesLE
    (zeroCoverPrimes_subset hx0.le hW)
    (by
      intro p hp
      obtain ⟨hp, _, hpZ⟩ := mem_auxiliaryPrimes.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpZ.trans hZ, hp⟩)
    (zeroCoverPrimes_disjoint x) (fun p hp => (Nat.mem_primesLE.mp hp).2.pos)
  refine ⟨a, ha, ?_⟩
  have hfloor : (coverLength coverEta x : ℝ) ≤ coverEta * coverScale x := by
    rw [coverLength_eq]
    apply Nat.floor_le
    unfold coverScale
    exact mul_nonneg coverEta_pos.le (by positivity)
  have hzero' := hzero (coverLength coverEta x) hlength.1.le hlength.2.1
  have hC := smoothScaleConstant_pos
  calc
    _ ≤ ((zeroSurvivors x (coverLength coverEta x)).card : ℝ) *
        ∏ p ∈ auxiliaryPrimes (coverW x) (coverZ x), (1 - 1 / (p : ℝ)) := hcard
    _ ≤ ((zeroSurvivors x (coverLength coverEta x)).card : ℝ) *
        (10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
          (Real.log x * Real.log (Real.log (Real.log x)))) :=
      mul_le_mul_of_nonneg_left hgreedy (Nat.cast_nonneg _)
    _ ≤ ((Real.log 4 + 2) * (coverEta * coverScale x) / Real.log x) *
        (10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
          (Real.log x * Real.log (Real.log (Real.log x)))) := by
      gcongr
      exact hzero'.trans (by gcongr)
    _ = (coveringConstant * coverEta) * x := by
      unfold coveringConstant coverScale
      field_simp
    _ ≤ sieveDelta * x := mul_le_mul_of_nonneg_right coveringConstant_mul_eta_le hx0.le


end
end LongGapsBetweenPrimes
open Finset Filter Real LongGapsBetweenPrimes
namespace ERankin

private lemma complete_cover {H y z : ℕ} (hz : z ≤ y) (a : ℕ → ℕ)
    (ha : ∀ p ∈ z.primesLE, a p < p)
    (hc : (survivors (Icc 1 H) z.primesLE a).card ≤ (y.primesLE \ z.primesLE).card) :
    ∃ x : ℕ, ∀ i ∈ Icc 1 H, ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ p ∣ x+i := by
  classical
  let S := survivors (Icc 1 H) z.primesLE a
  obtain ⟨e,he⟩ := Function.Embedding.exists_of_card_le_finset (α := S)
    (s := y.primesLE \ z.primesLE) (by simpa [S] using hc)
  have hem (s : S) := mem_sdiff.mp (he ⟨s,rfl⟩)
  let r (p : ℕ) := if h : ∃ s : S, e s = p then (h.choose.val % p) else (a p % p)
  have hr p (hp : p ∈ y.primesLE) : r p < p := by
    dsimp [r]
    split <;> apply Nat.mod_lt _ (Nat.mem_primesLE.mp hp).2.pos
  have hex (i) (hi : i ∈ Icc 1 H) : ∃ p ∈ y.primesLE, i % p = r p := by
    by_cases hs : i ∈ S
    · let s : S := ⟨i,hs⟩
      have h : ∃ u : S, e u = e s := ⟨s,rfl⟩
      refine ⟨e s,(hem s).1,?_⟩
      simp only [r,dif_pos h,e.injective h.choose_spec]
      rfl
    · obtain ⟨p,hp,hmod⟩ : ∃ p ∈ z.primesLE, i % p = a p := by simpa [S,survivors,hi] using hs
      have hn : ¬∃ s : S, e s = p := by rintro ⟨s,rfl⟩; exact (hem s).2 hp
      obtain ⟨hpz,hprime⟩ := Nat.mem_primesLE.mp hp
      exact ⟨p,Nat.mem_primesLE.mpr ⟨hpz.trans hz,hprime⟩,by simpa only [r,dif_neg hn,Nat.mod_eq_of_lt (ha p hp)] using hmod⟩
  let b := Nat.chineseRemainderOfFinset (fun p => p-r p) id y.primesLE
    (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (Nat.mem_primesLE.mp hp).2 (Nat.mem_primesLE.mp hq).2).mpr hpq)
  refine ⟨b.val,?_⟩
  intro i hi
  obtain ⟨p,hp,hmod⟩ := hex i hi
  obtain ⟨hpy,hpp⟩ := Nat.mem_primesLE.mp hp
  refine ⟨p,hpp,hpy,Nat.dvd_of_mod_eq_zero ?_⟩
  have hb : b.val % p = (p-r p)%p := b.property p hp
  calc
    _ = ((p-r p)+r p)%p := by
      rw [Nat.add_mod, hb, hmod, Nat.add_mod (p-r p),Nat.mod_eq_of_lt (hr p hp)]
    _ = 0 := by rw [Nat.sub_add_cancel (hr p hp).le,Nat.mod_self]

private lemma half_log {u v : ℝ} (hv : 4 ≤ v) (hu : v/2 ≤ u) : log v/2 ≤ log u := by
  rw [← Real.log_sqrt (by linarith)]
  apply Real.log_le_log (Real.sqrt_pos.2 (by linarith))
  apply le_trans _ hu
  apply (Real.sqrt_le_iff).mpr
  constructor <;> nlinarith [mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ v-4 by linarith)]

private lemma primes_lower : ∀ᶠ y : ℕ in atTop, (y:ℝ)/4 ≤ (y.primeCounting:ℝ)*log y := by
  have hf : Tendsto (fun y : ℕ => (y:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  filter_upwards [hf.eventually (isLittleO_log_id_atTop.bound (show (0:ℝ)<1/8 by norm_num)),
    eventually_ge_atTop 2] with y hy hy2
  have hy2' : (2:ℝ) ≤ y := by exact_mod_cast hy2
  change ‖log ((y:ℝ)+1)‖ ≤ 1/8 * ‖(y:ℝ)+1‖ at hy
  rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),Real.norm_of_nonneg (by linarith)] at hy
  have hh := (div_le_iff₀ (log_pos (by linarith : 1 < (y:ℝ)))).mp (Chebyshev.pi_ge y)
  nlinarith [mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ log 2 by linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg (α:=ℝ) y)]

lemma rankin : ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∃ x : ℕ, ∀ i : ℕ, 1 ≤ i →
    (i:ℝ) ≤ c*y*log y*log (log (log y))/(log (log y))^2 →
    ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ p ∣ x+i := by
  let f (y : ℕ) := (y:ℝ)/(16*log y)
  have hl : Tendsto (fun y : ℕ => log y) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := tendsto_log_atTop.comp hl
  have hroot : ∀ᶠ y : ℕ in atTop, √(y:ℝ) ≤ f y := by
    have h0 := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).bound (show (0:ℝ)<1/16 by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h0,hl.eventually_ge_atTop 1] with y hy hly
    change ‖log (y:ℝ)‖ ≤ 1/16 * ‖(y:ℝ)^(1/2:ℝ)‖ at hy
    rw [← sqrt_eq_rpow, Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg (sqrt_nonneg _)] at hy
    apply (le_div_iff₀ (by positivity : 0 < 16*log y)).mpr
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) y),mul_le_mul_of_nonneg_left hy (sqrt_nonneg (y:ℝ))]
  have hf : Tendsto f atTop atTop := tendsto_atTop_mono' _ hroot (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨coverEta/256,div_pos coverEta_pos (by norm_num),?_⟩
  apply eventually_atTop.mp
  filter_upwards [hroot, hf.eventually eventually_covering_residues,
    hf.eventually (eventually_coverLength_bounds coverEta_pos coverEta_le_one),
    hf.eventually_ge_atTop 4,hl.eventually_ge_atTop 4,hll.eventually_ge_atTop 4,
    primes_lower] with y hrt hres hlen hx hy hyy hpr
  change 4 ≤ log (log y) at hyy
  let x := f y
  have hx4 : 4 ≤ x := hx
  have hylog : 0 < log y := by linarith
  have hy0 : 0 < (y:ℝ) := by
    by_contra! hh
    have : y=0 := by exact_mod_cast (le_antisymm hh (Nat.cast_nonneg _))
    norm_num [this] at hy
  have hxy : x ≤ y := div_le_self hy0.le (by linarith)
  have hxy' : ⌊x⌋₊ ≤ y := by exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ x)).trans hxy
  obtain ⟨a,ha,hS⟩ := hres
  let H := coverLength coverEta x
  let S := survivors (Icc 1 H) ⌊x⌋₊.primesLE a
  have hcard : S.card ≤ (y.primesLE \ ⌊x⌋₊.primesLE).card := by
    have hcount : ⌊x⌋₊.primesLE.card ≤ ⌊x⌋₊+1 := by
      calc
        _ ≤ (range (⌊x⌋₊+1)).card := card_le_card (fun p hp => mem_range.mpr
          (Nat.lt_succ_of_le (Nat.mem_primesLE.mp hp).1))
        _ = _ := card_range _
    have hh := Finset.card_le_card_sdiff_add_card (s := y.primesLE) (t := ⌊x⌋₊.primesLE)
    rw [Nat.primesLE_card_eq_primeCounting] at hh
    have hp : 4*x ≤ y.primeCounting := by
      dsimp only [x,f]
      have h := (div_le_iff₀ hylog).mpr hpr
      calc
        _ = (y:ℝ)/4/log y := by ring
        _ ≤ _ := h
    have hs : (S.card:ℝ) ≤ x := hS.trans (mul_le_of_le_one_left (by linarith) (by linarith [sieveDelta_lt_half]))
    have hc' : (⌊x⌋₊.primesLE.card:ℝ) ≤ (⌊x⌋₊:ℕ)+1 := by exact_mod_cast hcount
    have hh' : (y.primeCounting:ℝ) ≤ ((y.primesLE \ ⌊x⌋₊.primesLE).card:ℝ)+⌊x⌋₊.primesLE.card := by exact_mod_cast hh
    exact_mod_cast (show (S.card:ℝ) ≤ ((y.primesLE \ ⌊x⌋₊.primesLE).card:ℝ) by linarith [Nat.floor_le (by linarith : 0 ≤ x)])
  obtain ⟨u,hu⟩ := complete_cover hxy' a ha hcard
  have h1 : log (y:ℝ)/2 ≤ log x := by
    rw [← log_sqrt hy0.le]
    exact log_le_log (sqrt_pos.2 hy0) hrt
  have h2 := half_log hy h1
  have h3 := half_log hyy h2
  have h4 : log (log x) ≤ log (log y) :=
    log_le_log (by linarith) (log_le_log (by linarith) hxy)
  have hyy0 : 0 < log (log (log y)) := log_pos (by linarith)
  have he := coverEta_pos
  have hxpos : 0 < x := by linarith
  have hxll : 0 < log (log x) := by linarith
  have hxlll : 0 < log (log (log x)) := by linarith
  have hs : coverEta/256 * y * log y * log (log (log y)) / log (log y)^2 ≤
      (coverEta/2)*coverScale x := by
    unfold coverScale
    calc
      _ = (coverEta/2)*(x*(log y/2)^2*(log (log (log y))/2)/(log (log y))^2) := by
        dsimp [x,f]; field_simp; ring
      _ ≤ _ := by gcongr
  refine ⟨u, fun i hi hle => hu i (mem_Icc.mpr ⟨hi,?_⟩)⟩
  exact_mod_cast hle.trans (hs.trans hlen.2.2)

end ERankin

namespace RankinDyadic

open Real

lemma key (y A : ℝ) (hy : 16 ≤ Real.log y) (hy0 : 0 < y) (hA1 : y / 4 ≤ A)
    (hA2 : A ≤ 3 * y) :
    A * Real.log A * (Real.log (Real.log (Real.log A)) / (Real.log (Real.log A)) ^ 2) ≤
      48 * (y * Real.log y * (Real.log (Real.log (Real.log y)) /
        (Real.log (Real.log y)) ^ 2)) := by
  have hA0 : 0 < A := by linarith
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog3 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  set u := Real.log y with hu
  have hu0 : 0 < u := by linarith
  have hLA1 : u / 2 ≤ Real.log A := by
    have h1 : Real.log (y / 4) ≤ Real.log A := Real.log_le_log (by positivity) hA1
    rw [Real.log_div hy0.ne' (by norm_num)] at h1
    linarith
  have hLA2 : Real.log A ≤ 2 * u := by
    have h1 : Real.log A ≤ Real.log (3 * y) := Real.log_le_log hA0 hA2
    rw [Real.log_mul (by norm_num) hy0.ne'] at h1
    linarith
  set t := Real.log u with ht
  have ht2 : 2 ≤ t := by
    have h1 : Real.log 16 ≤ t := Real.log_le_log (by norm_num) hy
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  set s := Real.log (Real.log A) with hs
  have hs1 : t / 2 ≤ s := by
    have h1 : Real.log (u / 2) ≤ s := Real.log_le_log (by positivity) hLA1
    rw [Real.log_div hu0.ne' (by norm_num)] at h1
    linarith
  have hs2 : s ≤ 2 * t := by
    have h1 : s ≤ Real.log (2 * u) := Real.log_le_log (by linarith) hLA2
    rw [Real.log_mul (by norm_num) hu0.ne'] at h1
    linarith
  have hs0 : 1 ≤ s := by linarith
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg hs0
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
  have hlogs : Real.log s ≤ 2 * Real.log t := by
    have h1 : Real.log s ≤ Real.log (2 * t) := Real.log_le_log (by linarith) hs2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have ht0 : 0 < t := by linarith
  have hlt0 : 0 ≤ Real.log t := by linarith
  have hfrac : Real.log s / s ^ 2 ≤ 8 * (Real.log t / t ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : t ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    have h5 : 8 * (Real.log t / t ^ 2) * (t ^ 2 / 4) = 2 * Real.log t := by
      field_simp; ring
    have h6 : 0 ≤ 8 * (Real.log t / t ^ 2) := by positivity
    calc Real.log s ≤ 2 * Real.log t := hlogs
      _ = 8 * (Real.log t / t ^ 2) * (t ^ 2 / 4) := h5.symm
      _ ≤ 8 * (Real.log t / t ^ 2) * s ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ h6; linarith
  have hAl : A * Real.log A ≤ 6 * (y * u) := by
    have := mul_le_mul hA2 hLA2 (by linarith) (by linarith)
    linarith
  have hfr0 : 0 ≤ Real.log s / s ^ 2 := by positivity
  have hyu : 0 ≤ 6 * (y * u) := by positivity
  calc A * Real.log A * (Real.log s / s ^ 2)
        ≤ (6 * (y * u)) * (8 * (Real.log t / t ^ 2)) := mul_le_mul hAl hfrac hfr0 hyu
    _ = 48 * (y * u * (Real.log t / t ^ 2)) := by ring

lemma gap (x M : ℕ) (hx : 2 ≤ x) (hc : ∀ i, 1 ≤ i → i ≤ M → ¬ (x + i).Prime) :
    Nat.nth Nat.Prime (Nat.primeCounting x - 1) ≤ x ∧
    x + M + 1 ≤ Nat.nth Nat.Prime (Nat.primeCounting x - 1 + 1) := by
  have hk : 1 ≤ Nat.primeCounting x := by
    have h2 : Nat.primeCounting 2 ≤ Nat.primeCounting x := Nat.monotone_primeCounting hx
    have : Nat.primeCounting 2 = 1 := by decide
    omega
  have hkk : Nat.primeCounting x - 1 + 1 = Nat.primeCounting x := by omega
  constructor
  · have : Nat.nth Nat.Prime (Nat.primeCounting x - 1) < x + 1 :=
      Nat.nth_lt_of_lt_count (by
        show Nat.primeCounting x - 1 < Nat.count Nat.Prime (x + 1)
        have : Nat.primeCounting x = Nat.count Nat.Prime (x + 1) := rfl
        omega)
    omega
  · rw [hkk]
    have h1 : x + 1 ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (x + 1)) :=
      Nat.le_nth_count Nat.infinite_setOfPred_prime (x + 1)
    have hpr : (Nat.nth Nat.Prime (Nat.primeCounting x)).Prime := Nat.prime_nth_prime _
    by_contra hlt
    push Not at hlt
    have h1' : x + 1 ≤ Nat.nth Nat.Prime (Nat.primeCounting x) := h1
    obtain ⟨i, hi⟩ : ∃ i, Nat.nth Nat.Prime (Nat.primeCounting x) = x + i :=
      ⟨_, (Nat.add_sub_cancel' (by omega)).symm⟩
    exact hc i (by omega) (by omega) (hi ▸ hpr)

/-- Place a representative of a specified residue class just beyond the Nth
prime. A modulus at most N / 2 fits before the prime with index 2N. -/
lemma place_residue (N P r : ℕ) (hP : 0 < P) (hPN : 2 * P ≤ N) :
    ∃ x : ℕ, Nat.nth Nat.Prime N ≤ x ∧ x < Nat.nth Nat.Prime (2 * N) ∧
      x ≡ r [MOD P] := by
  let p := Nat.nth Nat.Prime N
  let x := r % P + P * (p / P + 1)
  have hsplit := Nat.div_add_mod p P
  have hrem := Nat.mod_lt p hP
  have hr := Nat.mod_lt r hP
  have hbase : P * (p / P + 1) = P * (p / P) + P := by ring
  have hspread := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).add_le_nat N N
  change N + p ≤ Nat.nth Nat.Prime (N + N) at hspread
  refine ⟨x, ?_, ?_, ?_⟩
  · dsimp only [x]
    omega
  · rw [show 2 * N = N + N by omega]
    dsimp only [x]
    omega
  · show (r % P + P * (p / P + 1)) % P = r % P
    simp

/-- The scale y is one below the base-four logarithm of N. Throughout
[N, 2N], log n is comparable to y with the constants used by the sieve. -/
lemma log_window {N n y : ℕ} (hy : 16 ≤ y) (hlo : 4 ^ (y + 1) ≤ N)
    (hhi : N < 4 ^ (y + 2)) (hn : N ≤ n) (hn' : n ≤ 2 * N) :
    (y : ℝ) / 4 ≤ log n ∧ log n ≤ 3 * y := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by decide : 0 < 4) _) (hlo.trans hn))
  have h1 : (4 : ℝ) ^ (y + 1) ≤ n := by exact_mod_cast hlo.trans hn
  have h2 : (n : ℝ) ≤ 2 * 4 ^ (y + 2) := by
    exact_mod_cast hn'.trans (Nat.mul_le_mul_left 2 hhi.le)
  have hl := Real.log_le_log (by positivity) h1
  have hu := Real.log_le_log hn0 h2
  have hfour : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_pow, hfour] at hl
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hfour] at hu
  push_cast at hl hu
  have hy' : (16 : ℝ) ≤ y := by exact_mod_cast hy
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) y) (sub_nonneg.mpr Real.log_two_gt_d9.le),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) y) (sub_nonneg.mpr Real.log_two_lt_d9.le)]

/-- Every sufficiently large dyadic block of prime indices contains
consecutive primes with a gap of Rankin's order. -/
theorem dyadic_gaps : ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧
      C * log (log n) * log (log (log (log n))) / (log (log (log n))) ^ 2 * log n <
        (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ) := by
  obtain ⟨c, hc, Y, hY⟩ := ERankin.rankin
  refine ⟨c / 48, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4 ^ (max Y (2 ^ 24) + 1))] with N hN
  have ht := Nat.le_log_of_pow_le (by decide : 1 < 4) hN
  let y := Nat.log 4 N - 1
  have hyY : Y ≤ y := by dsimp [y]; omega
  have hy24 : 2 ^ 24 ≤ y := by dsimp [y]; omega
  have hscale : Nat.log 4 N = y + 1 := by dsimp [y]; omega
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos (by decide : 0 < 4) _) hN
  have hlow := Nat.pow_log_le_self 4 hNpos.ne'
  have hhigh := Nat.lt_pow_succ_log_self (by decide : 1 < 4) N
  rw [hscale] at hlow hhigh
  obtain ⟨x0, hx0⟩ := hY y hyY
  set P := primorial y with hP
  have hP0 : 0 < P := primorial_pos y
  have hP4 : P ≤ 4 ^ y := primorial_le_four_pow y
  have hPN : 2 * P ≤ N := by rw [pow_succ] at hlow; omega
  obtain ⟨x, hxlo, hxhi, hxmod⟩ := place_residue N P x0 hP0 hPN
  have hNy : y ≤ N := le_trans (Nat.sub_le _ _) (Nat.log_le_self 4 N)
  have hxy := Nat.add_two_le_nth_prime N
  set L : ℝ := c * y * log y * log (log (log y)) / (log (log y)) ^ 2 with hL
  set M := ⌊L⌋₊ with hM
  have hcomp : ∀ i, 1 ≤ i → i ≤ M → ¬ (x + i).Prime := by
    intro i hi hiM hpr
    have hL0 : 0 ≤ L := by
      by_contra! hneg
      have : M = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    obtain ⟨p, hp, hpy, hpd⟩ := hx0 i hi ((Nat.cast_le.mpr hiM).trans (Nat.floor_le hL0))
    have hpP : p ∣ P := by
      rw [hP, primorial]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
    have hcong := (hxmod.of_dvd hpP).add_right i
    have hdiv : p ∣ x + i := (hcong.dvd_iff (dvd_refl p)).mpr hpd
    have he := (Nat.prime_dvd_prime_iff_eq hp hpr).mp hdiv
    omega
  obtain ⟨hlo, hhi⟩ := gap x M (by omega) hcomp
  set n := Nat.primeCounting x - 1 with hn
  have hcount (j : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime j) = j + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime j
  have hleft := Nat.monotone_primeCounting hxlo
  have hright := Nat.monotone_primeCounting hxhi.le
  rw [hcount] at hleft hright
  have hnlo : N ≤ n := by omega
  have hnhi : n ≤ 2 * N := by omega
  refine ⟨n, hnlo, hnhi, ?_⟩
  have hyR : (2 : ℝ) ^ 24 ≤ y := by exact_mod_cast hy24
  have hlogy : 16 ≤ log (y : ℝ) := by
    have hl := Real.log_le_log (by positivity) hyR
    rw [Real.log_pow] at hl
    push_cast at hl
    linarith [Real.log_two_gt_d9]
  set A := log (n : ℝ) with hA
  obtain ⟨hA1,hA2⟩ := log_window (by omega : 16 ≤ y) hlow hhigh hnlo hnhi
  have hk := key (y : ℝ) A hlogy (by linarith : (0 : ℝ) < y) hA1 hA2
  have hg : ((x + M + 1 : ℕ) : ℝ) - (x : ℝ) ≤
      (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ) := by
    have a1 : ((x + M + 1 : ℕ) : ℝ) ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) := by exact_mod_cast hhi
    have a2 : (Nat.nth Nat.Prime n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hlo
    linarith
  have hML : L < (M : ℝ) + 1 := Nat.lt_floor_add_one L
  push_cast at hg
  have hrw : c / 48 * Real.log (Real.log (n:ℝ)) * Real.log (Real.log (Real.log (Real.log (n:ℝ)))) /
      (Real.log (Real.log (Real.log (n:ℝ)))) ^ 2 * Real.log (n:ℝ) =
      c / 48 * (A * Real.log A * (Real.log (Real.log (Real.log A)) /
        (Real.log (Real.log A)) ^ 2)) := by
    rw [hA]; ring
  rw [hrw]
  have hLeq : L = c * (y * Real.log y * (Real.log (Real.log (Real.log y)) /
      (Real.log (Real.log y)) ^ 2)) := by rw [hL]; ring
  have : c / 48 * (A * Real.log A * (Real.log (Real.log (Real.log A)) /
        (Real.log (Real.log A)) ^ 2)) ≤ L := by
    rw [hLeq]
    have := mul_le_mul_of_nonneg_left hk (le_of_lt (show 0 < c / 48 by positivity))
    linarith
  linarith

end RankinDyadic

theorem OMA.solution : type_of% @Erdos4.erdos_4.variants.rankin := by
  obtain ⟨C, hC, h⟩ := RankinDyadic.dyadic_gaps
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  refine ⟨C, hC, Set.infinite_of_forall_exists_gt ?_⟩
  intro N
  obtain ⟨n, hn, _, hgap⟩ := hN₀ (max N₀ (N + 1)) (le_max_left _ _)
  exact ⟨n, hgap, lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _)) hn⟩
