import OMAReductions.R_Erdos1050_erdos_1050_variants_transcendental_R1
import Mathlib

/-!
# The irrationality step in Erdős Problem 1050

Peter B. Borwein, *On the irrationality of ∑ 1/(qⁿ+r)*,
Journal of Number Theory 37 (1991), 253–259, and
*On the irrationality of certain series*, Mathematical Proceedings of the
Cambridge Philosophical Society 112 (1992), 141–146.

The proof is adapted from Trevor Morris's LeanGallery formalization at
https://github.com/gotrevor/lean-gallery/tree/b4e3ce4d0a061e2ee2e4507f90661c3ea498b5a9/LeanGallery/NumberTheory/Erdos1050.
For this single-file submission, the dependencies of `GeneralAssembly` are
included in order below with their copyright notices and license. The final
theorem specializes Borwein's result to base 2 and translates the pole exclusion.
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

-- LeanGallery/NumberTheory/Erdos1050/Basic.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Erdős #1050 — irrationality of `∑ 1/(2ⁿ − 3)`

Erdős & Graham asked whether `∑_{n} 1/(2ⁿ − 3)` is irrational. The answer is **yes**, by
P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory **37** (1991) 253–259;
cleaner self-contained proof in P. B. Borwein, *On the irrationality of certain series*,
Math. Proc. Camb. Phil. Soc. **112** (1992) 141–146 (free: cecm.sfu.ca/~pborwein/PAPERS/P59.pdf).

Method (no transcendence theory): explicit Padé / rational approximants `pₙ/qₙ` to the series with
integer numerators/denominators and a super-exponential error bound `0 < |qₙ·S − pₙ| → 0`, feeding the
classical integer-approximation irrationality criterion (`Criterion.lean`). The contour integral in the
paper is **avoided** — the approximants are reconstructed as explicit finite sums (`Approximants.lean`).

Problem page: <https://www.erdosproblems.com/1050>.
-/

namespace LeanGallery.NumberTheory.Erdos1050
open scoped BigOperators

/-- The Erdős–Graham series `∑_{n≥0} 1/(2^(n+2) − 3)`.

Index base note: every denominator `2^(n+2) − 3 ≥ 1` is positive, so all terms are well-defined
positive reals. The problem is usually written `∑ 1/(2ⁿ − 3)`; the low terms (`n=0,1` give `−1/2, −1`)
are rational, and **adding/removing finitely many rationals does not change irrationality**, so the
index base is a free, faithfulness-irrelevant choice. We start at `n+2` to keep every term positive. -/
noncomputable def S : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)

/-- The tail series defining `S` is summable: every term `1/(2^(n+2)−3)` is dominated by `2^{-n}`.
(Auto-formalized by Harmonic's Aristotle, ported here and verified axiom-clean.) -/
lemma S_summable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)) := by
  ring_nf
  exact Summable.of_nonneg_of_le
    (fun n => inv_nonneg.mpr <| by
      nlinarith [show (2 : ℝ) ^ n ≥ 1 by exact one_le_pow₀ (by norm_num)])
    (fun n => by
      rw [inv_le_comm₀] <;> norm_num <;> induction n <;> norm_num [pow_succ'] at * <;> nlinarith)
    summable_geometric_two

/- The headline theorem `erdos_1050 : Irrational S` is proved in `Approximants.lean` (it needs the
proof engine); `Statement.lean` re-exports it as the audit surface. -/

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/Criterion.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The integer-approximation irrationality criterion

The single reusable lemma the whole proof feeds: a real `x` is irrational if there are integer
sequences `aₙ, bₙ` with `bₙ·x − aₙ ≠ 0` for all `n` and `bₙ·x − aₙ → 0`. (Hardy–Wright Thm 186 /
Van Assche Lemma 5.1.) The standard one-line argument: if `x = p/q` were rational, then
`bₙ·x − aₙ = (bₙ·p − aₙ·q)/q` is a nonzero rational of absolute value `≥ 1/q`, contradicting `→ 0`.

⚠️ Check whether mathlib already has this (it has `Liouville` machinery in
`Mathlib.NumberTheory.Liouville.*` and `Irrational` API). If a close form exists, delegate to it; this
file is a ~20-line standalone fallback otherwise.
-/

namespace LeanGallery.NumberTheory.Erdos1050
open Filter Topology

/-- Irrationality from integer approximations with nonzero, vanishing error.
If `b n * x - a n ≠ 0` for all `n` and `(fun n => b n * x - a n) → 0`, then `x` is irrational.

Proof: if `x = r` were rational with denominator `d = r.den`, then `d·(bₙ·x − aₙ) =
bₙ·r.num − d·aₙ` is a nonzero integer, hence has absolute value `≥ 1`, so `|bₙ·x − aₙ| ≥ 1/d > 0`
for all `n` — contradicting `bₙ·x − aₙ → 0`. -/
theorem irrational_of_intApprox (x : ℝ) (a b : ℕ → ℤ)
    (hne : ∀ n, (b n : ℝ) * x - a n ≠ 0)
    (hlim : Tendsto (fun n => (b n : ℝ) * x - a n) atTop (𝓝 0)) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast Rat.den_pos r
  have hdne : (r.den : ℝ) ≠ 0 := ne_of_gt hden
  have hrd : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by
    rw [Rat.cast_def]; field_simp
  -- Lower bound: `|bₙ·r − aₙ| ≥ 1/r.den` for every `n`.
  have hlb : ∀ n, 1 / (r.den : ℝ) ≤ |(b n : ℝ) * (r : ℝ) - (a n : ℝ)| := by
    intro n
    have hcast : ((b n * r.num - r.den * a n : ℤ) : ℝ)
        = (r.den : ℝ) * ((b n : ℝ) * (r : ℝ) - (a n : ℝ)) := by
      push_cast
      linear_combination (-(b n : ℝ)) * hrd
    have hcne : (b n * r.num - r.den * a n : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hcast
      rcases mul_eq_zero.mp hcast.symm with h | h
      · exact hdne h
      · exact hne n h
    have h1 : (1 : ℝ) ≤ |((b n * r.num - r.den * a n : ℤ) : ℝ)| := by
      have hz : (1 : ℤ) ≤ |b n * r.num - r.den * a n| := Int.one_le_abs hcne
      calc (1 : ℝ) ≤ ((|b n * r.num - r.den * a n| : ℤ) : ℝ) := by exact_mod_cast hz
        _ = |((b n * r.num - r.den * a n : ℤ) : ℝ)| := by rw [Int.cast_abs]
    rw [hcast, abs_mul, abs_of_pos hden] at h1
    rw [div_le_iff₀ hden]
    nlinarith [h1]
  -- The error tends to `0` in absolute value, contradicting the constant lower bound.
  have habs : Tendsto (fun n => |(b n : ℝ) * (r : ℝ) - (a n : ℝ)|) atTop (𝓝 0) := by
    simpa using hlim.abs
  have hle : 1 / (r.den : ℝ) ≤ 0 := ge_of_tendsto' habs hlb
  have hpos : (0 : ℝ) < 1 / (r.den : ℝ) := by positivity
  linarith

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/Approximants.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Explicit rational approximants to `S` (contour-free)

Borwein (1992) builds the approximants from a contour integral `Fₙ(q)`. The decisive observation
(buried in his Lemma 5 proof) is that `Fₙ` equals an **explicit convergent series** of finite
products — no contour integral is logically needed:

  `Fₙ = ∑_{m=n}^∞ Iₘ`,   `Iₘ = -(1 - c·q^{m+n})⁻¹ · ∏_{k=1}^{n-1} (1 - q^{k-m})·(1 - c·q^{k+m})⁻¹`.

We take this as the *definition* of the error term `Eₙ` and rebuild the irrationality argument on it.

## Reduction to the q-harmonic form
`S = ∑_{n≥0} 1/(2^{n+2}−3)` is, up to an affine map by nonzero rationals and a finite `q^{m}` shift,
the value `z = ∑_{j≥1} 1/(1 − (8/3)·2^j)` (Borwein's normalized form with `q = 2`, `c = 8/3`,
`|c| > 2`). Irrationality is invariant under both operations, so `Irrational S ⟺ Irrational z`.

See `PENDING_WORK.md` for the full reduction chain and the obligation breakdown (O1–O4).
-/

namespace LeanGallery.NumberTheory.Erdos1050
open scoped BigOperators
open Filter Topology Finset

/-- Borwein base `q = 2`. -/
def qB : ℝ := 2

/-- Reduced shift parameter `c = 8/3` (so `|c| > 2`), obtained from `c' = 1/3` shifted by `q^3`. -/
noncomputable def cB : ℝ := 8 / 3

/-- Denominator of the rational parameter `c = 8/3`. Used for the `β^{2n}` denominator clearing. -/
def βB : ℕ := 3

/-- The reduced q-harmonic target value `z = ∑_{j≥1} 1/(1 − c·q^j)` (with `q = 2`, `c = 8/3`).
`Irrational S ⟺ Irrational z`. -/
noncomputable def zB : ℝ := ∑' j : ℕ, (1 - cB * qB ^ (j + 1))⁻¹

/-- The `m`-th term of the explicit (contour-free) error series. For `m ≥ n` this is Borwein's
residue `Iₘ`. All factors use integer (`zpow`) exponents so that `q^{k-m}` makes sense. -/
noncomputable def Iterm (n m : ℕ) : ℝ :=
  -(1 - cB * qB ^ ((m : ℤ) + n))⁻¹ *
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹

/-- The error term `Eₙ = Fₙ = ∑_{m≥n} Iₘ`, reindexed as `∑_{j≥0} I_{n}(n+j)`. -/
noncomputable def Eterm (n : ℕ) : ℝ := ∑' j : ℕ, Iterm n (n + j)

/- ### Numeric facts about the base parameters `q = 2`, `c = 8/3`. -/

lemma qB_pos : (0 : ℝ) < qB := by norm_num [qB]
lemma one_lt_qB : (1 : ℝ) < qB := by norm_num [qB]
lemma qB_ne : qB ≠ 0 := ne_of_gt qB_pos
lemma cB_pos : (0 : ℝ) < cB := by norm_num [cB]
lemma two_lt_cB : (2 : ℝ) < cB := by norm_num [cB]

/-- `q^k ≥ 2` for `k ≥ 1` (natural power version). -/
lemma two_le_pow {k : ℕ} (hk : 1 ≤ k) : (2 : ℝ) ≤ qB ^ k := by
  calc (2 : ℝ) = qB ^ 1 := by norm_num [qB]
    _ ≤ qB ^ k := pow_le_pow_right₀ (le_of_lt one_lt_qB) hk

/-- `q^a ≥ q ≥ 2` for `a ≥ 1`. -/
lemma two_le_zpow {a : ℤ} (ha : 1 ≤ a) : (2 : ℝ) ≤ qB ^ a := by
  calc (2 : ℝ) = qB ^ (1 : ℤ) := by norm_num [qB]
    _ ≤ qB ^ a := zpow_le_zpow_right₀ (le_of_lt one_lt_qB) ha

/-- Each `c·q^a − 1` (for `a ≥ 1`) dominates `q^a`, so its inverse is at most `q^{-a}`. -/
lemma inv_cqpow_le {a : ℤ} (ha : 1 ≤ a) : |(1 - cB * qB ^ a)⁻¹| ≤ qB ^ (-a) := by
  have hqa : (2 : ℝ) ≤ qB ^ a := two_le_zpow ha
  have hqpos : (0 : ℝ) < qB ^ a := zpow_pos qB_pos a
  -- `c·q^a − 1 ≥ q^a > 0`
  have hge : qB ^ a ≤ cB * qB ^ a - 1 := by nlinarith [hqa, hqpos, two_lt_cB]
  have hpos : (0 : ℝ) < cB * qB ^ a - 1 := lt_of_lt_of_le hqpos hge
  have habs : |(1 - cB * qB ^ a)⁻¹| = (cB * qB ^ a - 1)⁻¹ := by
    rw [abs_inv]
    congr 1
    rw [abs_of_neg (by linarith)]
    ring
  rw [habs, zpow_neg]
  exact inv_anti₀ hqpos hge

/-- Each product factor `(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹` has absolute value at most `1/2`
(for `1 ≤ k < m`). -/
lemma factor_bound {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (1 : ℝ) / 2 := by
  rw [abs_mul]
  have h1 : |1 - qB ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : qB ^ ((k : ℤ) - m) ≤ 1 := by
      calc qB ^ ((k : ℤ) - m) ≤ qB ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) hexp
        _ = 1 := by norm_num
    have hpos : 0 < qB ^ ((k : ℤ) - m) := zpow_pos qB_pos _
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h2 : |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ qB ^ (-((k : ℤ) + m)) :=
    inv_cqpow_le (by omega)
  have h3 : qB ^ (-((k : ℤ) + m)) ≤ (1 : ℝ) / 2 := by
    calc qB ^ (-((k : ℤ) + m)) ≤ qB ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
      _ = 1 / 2 := by rw [zpow_neg, zpow_one]; norm_num [qB]
  calc |1 - qB ^ ((k : ℤ) - m)| * |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * (1 / 2) := mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := by ring

/-- **Crude per-term bound.** For `1 ≤ n ≤ m`, `|Iₘ| ≤ q^{-(m+n)}·(1/2)^{n-1}`. The leading
factor carries the geometric `m`-decay; the `(n−1)` product factors are each `≤ 1/2`. (Enough for
summability and non-vanishing; the sharp super-exponential bound is the separate error obligation.) -/
lemma Iterm_abs_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ qB ^ (-((m : ℤ) + n)) * (1 / 2) ^ (n - 1) := by
  rw [Iterm, abs_mul, abs_neg]
  have hlead : |(1 - cB * qB ^ ((m : ℤ) + n))⁻¹| ≤ qB ^ (-((m : ℤ) + n)) :=
    inv_cqpow_le (by omega)
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (1 / 2) ^ (n - 1) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 (n - 1), |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ _k ∈ Finset.Icc 1 (n - 1), (1 / 2 : ℝ) :=
          Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => by
            rw [Finset.mem_Icc] at hk
            exact factor_bound hk.1 (by omega))
      _ = (1 / 2 : ℝ) ^ (Finset.Icc 1 (n - 1)).card := by rw [Finset.prod_const]
      _ = (1 / 2 : ℝ) ^ (n - 1) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hbnn : (0 : ℝ) ≤ qB ^ (-((m : ℤ) + n)) := le_of_lt (zpow_pos qB_pos _)
  exact mul_le_mul hlead hprod (abs_nonneg _) hbnn

/-- `q^{-j} = (1/2)^j`. -/
lemma qB_neg_zpow (j : ℕ) : qB ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := by
  rw [zpow_neg, zpow_natCast, show qB = 2 from rfl,
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]

/-- The reindexed term `I_n(n+j)` is bounded by `(1/2)^j` — enough for absolute summability. -/
lemma Iterm_shift_le {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : |Iterm n (n + j)| ≤ (1 / 2 : ℝ) ^ j := by
  have h := Iterm_abs_le hn (Nat.le_add_right n j)
  have hexp : qB ^ (-(((n + j : ℕ) : ℤ) + n)) ≤ qB ^ (-(j : ℤ)) := by
    apply zpow_le_zpow_right₀ (le_of_lt one_lt_qB)
    push_cast; omega
  have hpow1 : (1 / 2 : ℝ) ^ (n - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc |Iterm n (n + j)| ≤ qB ^ (-(((n + j : ℕ) : ℤ) + n)) * (1 / 2) ^ (n - 1) := h
    _ ≤ qB ^ (-(j : ℤ)) * 1 :=
        mul_le_mul hexp hpow1 (by positivity) (le_of_lt (zpow_pos qB_pos _))
    _ = (1 / 2) ^ j := by rw [mul_one, qB_neg_zpow]

/-- The error series `Eₙ = ∑_{j} I_n(n+j)` is summable. -/
lemma Eterm_summable {n : ℕ} (hn : 1 ≤ n) : Summable (fun j => Iterm n (n + j)) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ j)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro j; rw [Real.norm_eq_abs]; exact Iterm_shift_le hn j

/- ### Non-vanishing of the error (Borwein's Lemma 5).

For `q = 2`, `c = 8/3 > 1`, every term `Iₘ` (`m ≥ n`) has the *same* nonzero sign `(-1)^{n-1}`:
the leading factor `(1 − c·q^{m+n})⁻¹` is negative, and each of the `n−1` product factors
`(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹` is negative. A sum of same-sign nonzero terms cannot vanish. -/

/-- The leading factor `(1 − c·q^a)⁻¹` is negative for `a ≥ 1`. -/
lemma leading_neg {a : ℤ} (ha : 1 ≤ a) : (1 - cB * qB ^ a)⁻¹ < 0 := by
  have h2 : (2 : ℝ) ≤ qB ^ a := two_le_zpow ha
  have hneg : (1 - cB * qB ^ a) < 0 := by nlinarith [h2, two_lt_cB, zpow_pos qB_pos a]
  exact inv_neg''.mpr hneg

/-- Each product factor is negative for `1 ≤ k < m`. -/
lemma factor_neg {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹ < 0 := by
  have hnum : 0 < 1 - qB ^ ((k : ℤ) - m) := by
    have hle : qB ^ ((k : ℤ) - m) ≤ qB ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
    have heq : qB ^ (-1 : ℤ) = 1 / 2 := by rw [zpow_neg, zpow_one]; norm_num [qB]
    rw [heq] at hle; linarith
  exact mul_neg_of_pos_of_neg hnum (leading_neg (by omega))

/-- `(-1)^{n-1}` times the product of the `n−1` (negative) factors is positive. -/
lemma prod_factor_sign {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < (-1 : ℝ) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1),
          (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹ := by
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h1 : (-1 : ℝ) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) := by
    rw [Finset.prod_const, hcard]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hf := factor_neg hk.1 (show k < m by omega)
  linarith

/-- The sign of `Iₘ` (for `m ≥ n ≥ 1`) is exactly `(-1)^{n-1}`, and it is nonzero. -/
lemma Iterm_sign {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : 0 < (-1 : ℝ) ^ (n - 1) * Iterm n m := by
  rw [Iterm]
  have hL : (1 - cB * qB ^ ((m : ℤ) + n))⁻¹ < 0 := leading_neg (by omega)
  have hP := prod_factor_sign hn hnm
  have hnegL : (0 : ℝ) < -(1 - cB * qB ^ ((m : ℤ) + n))⁻¹ := by linarith
  have := mul_pos hnegL hP
  -- v4.31: `convert … using 1` now also emits the `LT` instance-equality goal
  -- (`Real.instLT = Real.instPreorder.toLT`); close it by `rfl`, the algebra by `ring`.
  convert this using 1 <;> first | rfl | ring

/- ### Sharp super-exponential error bound (Borwein's Lemma 4).

The decisive estimate. Using `|1 − q^{k−m}| ≤ 1` and `(c·q^a − 1)⁻¹ ≤ q^{-a}`,

  `|Iₘ| ≤ q^{-(m+n)}·∏_{k=1}^{n-1} q^{-(k+m)} = q^{-(n + T + n·m)}`,  `T = ∑_{k=1}^{n-1} k`,

which factors as `Cₙ·rⁿ` with `r = q^{-n} ∈ (0,1)`. Summing the geometric tail gives
`|Eₙ| ≤ 2·Cₙ·q^{-n²}`, super-exponential decay — enough to beat the denominator growth `Wₙ`. -/

/-- Tight per-factor bound: `|(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹| ≤ (q^{k+m})⁻¹` for `1 ≤ k < m`. -/
lemma factor_abs_le {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (qB ^ (k + m))⁻¹ := by
  rw [abs_mul]
  have h1 : |1 - qB ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : qB ^ ((k : ℤ) - m) ≤ 1 := by
      calc qB ^ ((k : ℤ) - m) ≤ qB ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) hexp
        _ = 1 := by norm_num
    have hpos : 0 < qB ^ ((k : ℤ) - m) := zpow_pos qB_pos _
    rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ qB ^ (-((k : ℤ) + m)) := inv_cqpow_le (by omega)
  have h3 : qB ^ (-((k : ℤ) + m)) = (qB ^ (k + m))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast qB (k + m), Nat.cast_add]
  calc |1 - qB ^ ((k : ℤ) - m)| * |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * qB ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (qB ^ (k + m))⁻¹ := by rw [one_mul, h3]

/-- Sharp per-term bound in product form. -/
lemma Iterm_abs_le_sharp {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ (qB ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹ := by
  rw [Iterm, abs_mul, abs_neg]
  have hlead : |(1 - cB * qB ^ ((m : ℤ) + n))⁻¹| ≤ (qB ^ (m + n))⁻¹ := by
    have h := inv_cqpow_le (a := (m : ℤ) + n) (by omega)
    have he : qB ^ (-((m : ℤ) + n)) = (qB ^ (m + n))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast qB (m + n), Nat.cast_add]
    rwa [he] at h
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹ := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
    intro k hk; rw [Finset.mem_Icc] at hk
    exact factor_abs_le hk.1 (by omega)
  exact mul_le_mul hlead hprod (abs_nonneg _) (le_of_lt (inv_pos.mpr (pow_pos qB_pos _)))

/-- Exponent bookkeeping: `(m+n) + ∑_{k=1}^{n-1}(k+m) = (n + ∑_{k=1}^{n-1} k) + n·m` for `n ≥ 1`.
The `n·m` term is the source of the super-exponential (`q^{-n·m}`) decay. -/
lemma exp_identity {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    (m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)
      = (n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
  have hmul : (n - 1) * m + m = n * m := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left m hn)]
  omega

/-- **Closed-form sharp per-term bound** (Borwein Lemma 4 core): `|Iₘ| ≤ Cₙ·(q^{-n})^m` with
`Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. Geometric in `m` with ratio `q^{-n} ≤ 1/2`, so the tail sum is
super-exponentially small. -/
lemma Iterm_abs_le_geom {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ m := by
  refine (Iterm_abs_le_sharp hn hnm).trans (le_of_eq ?_)
  have hL : (qB ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹
      = (qB ^ ((m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹ := by
    rw [Finset.prod_inv_distrib, prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
  have hR : (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ m
      = (qB ^ ((n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add]
  rw [hL, hR, exp_identity hn m]

/-- **Lemma 4 (error bound), `Eₙ` half.** Summing the geometric per-term bound:
`|Eₙ| ≤ Cₙ·(q^{-n})ⁿ·(1 − q^{-n})⁻¹` with `Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. Since `(q^{-n})ⁿ = q^{-n²}`
and `Cₙ = q^{-(n + n(n-1)/2)}`, this is `≈ q^{-3n²/2}` — super-exponential, as in Borwein. -/
lemma Eterm_abs_le {n : ℕ} (hn : 1 ≤ n) :
    |Eterm n| ≤ (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n
        * (1 - (qB ^ n)⁻¹)⁻¹ := by
  set r : ℝ := (qB ^ n)⁻¹ with hr_def
  set Cn : ℝ := (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ with hCn_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact le_of_lt (inv_pos.mpr (pow_pos qB_pos n))
  have hqn1 : (1 : ℝ) < qB ^ n := by
    calc (1 : ℝ) < qB := one_lt_qB
      _ = qB ^ 1 := (pow_one qB).symm
      _ ≤ qB ^ n := pow_le_pow_right₀ (le_of_lt one_lt_qB) hn
  have hr1 : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ hqn1
  have hsummabs : Summable (fun j => |Iterm n (n + j)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => Iterm_shift_le hn j)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have h1 : |Eterm n| ≤ ∑' j, |Iterm n (n + j)| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun j => Iterm n (n + j))
      (by simpa [Real.norm_eq_abs] using hsummabs)
    simpa [Eterm, Real.norm_eq_abs] using hnorm
  have hge : ∀ j, |Iterm n (n + j)| ≤ Cn * r ^ (n + j) := fun j =>
    Iterm_abs_le_geom hn (Nat.le_add_right n j)
  have hsummaj : Summable (fun j => Cn * r ^ (n + j)) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).mul_left _
  have h2 : ∑' j, |Iterm n (n + j)| ≤ ∑' j, Cn * r ^ (n + j) :=
    hsummabs.tsum_le_tsum hge hsummaj
  have h3 : ∑' j, Cn * r ^ (n + j) = Cn * r ^ n * (1 - r)⁻¹ := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  calc |Eterm n| ≤ ∑' j, |Iterm n (n + j)| := h1
    _ ≤ ∑' j, Cn * r ^ (n + j) := h2
    _ = Cn * r ^ n * (1 - r)⁻¹ := h3

/-- Clean closed form of the error bound: `|Eₙ| ≤ 2·(q^{n + ∑_{k<n}k + n²})⁻¹`. The exponent
`n + (n−1)n/2 + n² = (3n² + n)/2` is Borwein's `3n²/2` decay (up to lower order). -/
lemma Eterm_abs_le' {n : ℕ} (hn : 1 ≤ n) :
    |Eterm n| ≤ 2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
  refine (Eterm_abs_le hn).trans ?_
  have hC : (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n
      = (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add, sq]
  have hqn2 : (2 : ℝ) ≤ qB ^ n := two_le_pow hn
  have h1 : (qB ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqn2
  have htail : (1 - (qB ^ n)⁻¹)⁻¹ ≤ 2 := by
    have hb : (0 : ℝ) < 1 / 2 := by norm_num
    calc (1 - (qB ^ n)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ hb (by linarith)
      _ = 2 := by norm_num
  have hCnn : (0 : ℝ) ≤ (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ :=
    le_of_lt (inv_pos.mpr (pow_pos qB_pos _))
  calc (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n * (1 - (qB ^ n)⁻¹)⁻¹
      = (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * (1 - (qB ^ n)⁻¹)⁻¹ := by rw [hC]
    _ ≤ (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htail hCnn
    _ = 2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by ring

/-- **Lemma 5 (non-vanishing).** `Eₙ ≠ 0` for `n ≥ 1`. -/
lemma Eterm_ne_zero {n : ℕ} (hn : 1 ≤ n) : Eterm n ≠ 0 := by
  have hsum : Summable (fun j => (-1 : ℝ) ^ (n - 1) * Iterm n (n + j)) :=
    (Eterm_summable hn).mul_left _
  have hpos : ∀ j, 0 < (-1 : ℝ) ^ (n - 1) * Iterm n (n + j) :=
    fun j => Iterm_sign hn (Nat.le_add_right n j)
  have hp : 0 < ∑' j, (-1 : ℝ) ^ (n - 1) * Iterm n (n + j) :=
    hsum.tsum_pos (fun j => le_of_lt (hpos j)) 0 (hpos 0)
  rw [tsum_mul_left] at hp
  intro h0
  rw [show (∑' j, Iterm n (n + j)) = Eterm n from rfl, h0, mul_zero] at hp
  exact lt_irrefl 0 hp

/- ### The denominator-clearing factor `Wₙ` and the assembly into irrationality. -/

lemma one_sub_cqpow_ne {k : ℕ} (hk : 1 ≤ k) : (1 - cB * qB ^ k) ≠ 0 :=
  ne_of_lt (by nlinarith [two_le_pow hk, two_lt_cB, pow_pos qB_pos k])

lemma one_sub_qpow_ne {k : ℕ} (hk : 1 ≤ k) : (1 - qB ^ k) ≠ 0 :=
  ne_of_lt (by nlinarith [two_le_pow hk])

/-- The clearing factor `Wₙ = (n−2)!·∏_{k=1}^n (1 − c·q^k)·∏_{k=⌈n/2⌉}^n (1 − q^k)` (Borwein's
`wₙ` without the `pₙ` factor; `Wₙ·Fₙ = wₙ·z + sₙ`). -/
noncomputable def Wterm (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ)
    * (∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k))
    * (∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k))

/-- `Wₙ ≠ 0` for `n ≥ 1`: a nonzero factorial times two products of nonzero factors. -/
lemma Wterm_ne_zero {n : ℕ} (hn : 1 ≤ n) : Wterm n ≠ 0 := by
  rw [Wterm]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast Nat.factorial_ne_zero _
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    exact one_sub_cqpow_ne hk.1
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    -- `k ≥ ⌈n/2⌉ ≥ 1` since `n ≥ 1`
    exact one_sub_qpow_ne (by omega)

/-- **Wₙ growth bound** (Borwein Lemma 3 estimate). `|Wₙ| ≤ (n−2)!·cⁿ·(q^{∑_{k≤n}k})²`. Each
`|1 − c·q^k| ≤ c·q^k` and `|1 − q^k| ≤ q^k`; the second product (over `⌈n/2⌉..n`) is bounded by the
full product over `1..n`. -/
lemma Wterm_abs_le {n : ℕ} (hn : 1 ≤ n) :
    |Wterm n| ≤ (Nat.factorial (n - 2) : ℝ) * cB ^ n
        * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
  have hfac : (0:ℝ) ≤ (Nat.factorial (n-2) : ℝ) := by positivity
  have hqS : (0:ℝ) ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) := pow_nonneg (le_of_lt qB_pos) _
  rw [Wterm, abs_mul, abs_mul, abs_of_nonneg hfac]
  have hP1 : |∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k)| ≤ cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 n, |1 - cB * qB ^ k|
        ≤ ∏ k ∈ Finset.Icc 1 n, cB * qB ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          rw [abs_of_neg (by nlinarith [two_le_pow hk.1, two_lt_cB, pow_pos qB_pos k] :
            (1 - cB * qB ^ k) < 0)]
          nlinarith [pow_pos qB_pos k, cB_pos]
      _ = cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, prod_pow_eq_pow_sum, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hP2 : |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k)| ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc ((n + 1) / 2) n, |1 - qB ^ k|
        ≤ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, qB ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          rw [abs_of_nonpos (by nlinarith [two_le_pow (show 1 ≤ k by omega)] : (1 - qB ^ k) ≤ 0)]
          linarith
      _ = qB ^ (∑ k ∈ Finset.Icc ((n + 1) / 2) n, k) := prod_pow_eq_pow_sum _ _ _
      _ ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) :=
          pow_le_pow_right₀ (le_of_lt one_lt_qB)
            (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) (le_refl n)))
  calc (Nat.factorial (n - 2) : ℝ) * |∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k)|
        * |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k)|
      ≤ (Nat.factorial (n - 2) : ℝ) * (cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k))
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
        apply mul_le_mul _ hP2 (abs_nonneg _)
          (mul_nonneg hfac (mul_nonneg (pow_nonneg (le_of_lt cB_pos) n) hqS))
        exact mul_le_mul_of_nonneg_left hP1 hfac
    _ = (Nat.factorial (n - 2) : ℝ) * cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k)
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by ring

/- **O1 — Borwein Lemmas 1+2+3.** Formerly a monolithic axiom `borwein_integrality` lived here; it is
now a fully machine-checked THEOREM (`Lemma3.lean`). Lemma 1 (residue identity) is proved elementarily
(`Residue.lean`, `RESIDUE-IDENTITY-ELEMENTARY-PROOF.md`); Lemma 2 (denominator integrality) is
`Bden_cast` (`Integrality.lean`, via `qBin_cauchy`); Lemma 3 (numerator integrality) is proved
elementarily (`Lemma3.lean`, via q-Lagrange + a 2-adic/odd-denominator clearing for `N_h`). The
headline `erdos_1050` is axiom-clean. -/

/-- Gauss' formula over `Icc 1 n`: `2·∑_{k=1}^n k = n(n+1)`. -/
lemma gauss_Icc (n : ℕ) : 2 * (∑ k ∈ Finset.Icc 1 n, k) = n * (n + 1) := by
  have hconv : (∑ k ∈ Finset.Icc 1 n, k) = ∑ k ∈ Finset.range (n + 1), k := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
    · intro x hx hx2; rw [Finset.mem_range] at hx; rw [Finset.mem_Icc] at hx2; omega
  rw [hconv, mul_comm, Finset.sum_range_id_mul_two, Nat.add_sub_cancel, Nat.mul_comm]

/-- **The combine majorant** (Borwein Lemma 4, all factors assembled). The cleared error is bounded
by `2·(n−2)!·(9c)ⁿ·(q^{∑_{k<n}k})⁻¹`: the `q^{2∑_{k≤n}k}` from `Wₙ` and `β^{2n}=9ⁿ` cancel against
`Eₙ`'s `q^{-(n + ∑_{k<n}k + n²)}` decay, leaving the super-exponential `(q^{∑_{k<n}k})⁻¹`. -/
lemma cleared_error_le {n : ℕ} (hn : 1 ≤ n) :
    |(βB : ℝ) ^ (2 * n) * Wterm n * Eterm n|
      ≤ 2 * (Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
          * (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
  have hβ : (βB : ℝ) ^ (2 * n) = (9 : ℝ) ^ n := by rw [pow_mul]; norm_num [βB]
  have h2 : n + n ^ 2 = (∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [← two_mul, gauss_Icc n]; ring
  have hexp : n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k))
        + (∑ k ∈ Finset.Icc 1 (n - 1), k) := by omega
  have hq : qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k)
        * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
      = (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
    rw [← pow_add, hexp]
    nth_rewrite 2 [pow_add]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos qB_pos _)), one_mul]
  have hWnn : (0:ℝ) ≤ (Nat.factorial (n - 2) : ℝ) * cB ^ n
      * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (le_of_lt cB_pos) n)) ?_) ?_ <;> exact pow_nonneg (le_of_lt qB_pos) _
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  calc (βB : ℝ) ^ (2 * n) * |Wterm n| * |Eterm n|
      ≤ (βB : ℝ) ^ (2 * n) * ((Nat.factorial (n - 2) : ℝ) * cB ^ n
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹) := by
        apply mul_le_mul _ (Eterm_abs_le' hn) (abs_nonneg _)
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hWnn)
        exact mul_le_mul_of_nonneg_left (Wterm_abs_le hn) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = 2 * (Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
          * (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
        rw [hβ, mul_pow, ← hq]; ring

/-- `∑_{k=1}^{n-1} k = n(n−1)/2` (Gauss, lower form). -/
lemma gauss_Icc' (n : ℕ) : ∑ k ∈ Finset.Icc 1 (n - 1), k = n * (n - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0; simp
  · have h := gauss_Icc (n - 1)
    rw [Nat.sub_add_cancel hn0, Nat.mul_comm (n - 1) n] at h
    omega

/- ### The asymptotic `(n-2)!·Cⁿ·(q^{n(n-1)/2})⁻¹ → 0` (auto-formalized by Aristotle, verified
axiom-clean in our kernel). Super-exponential `(q^{n(n-1)/2})⁻¹` decay beats `(n-2)!·Cⁿ`; proved
by the ratio test (consecutive ratio `(n−1)C/qⁿ → 0`). -/

/-- Triangle-number recurrence `T(n+1) = T(n) + n`. -/
private lemma tri_succ (n : ℕ) : (n + 1) * ((n + 1) - 1) / 2 = n * (n - 1) / 2 + n := by
  have e : ∀ k : ℕ, k * (k - 1) / 2 = k.choose 2 := fun k => (Nat.choose_two_right k).symm
  rw [e, e, Nat.choose_succ_succ n 1]
  simp [Nat.choose_one_right]
  omega

private lemma fact_step (n : ℕ) (hn : 2 ≤ n) :
    Nat.factorial (n - 1) = (n - 1) * Nat.factorial (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [Nat.factorial_succ]

/-- The Borwein cleared-error majorant `(n-2)!·Cⁿ·(q^{n(n-1)/2})⁻¹`. -/
private noncomputable def fseq (q C : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ) * C ^ n * (q ^ (n * (n - 1) / 2))⁻¹

private lemma fseq_pos (q C : ℝ) (hq : 1 < q) (hC : 0 < C) (n : ℕ) : 0 < fseq q C n := by
  have hq0 : 0 < q := by linarith
  unfold fseq; positivity

private lemma fseq_ratio (q C : ℝ) (hq : 1 < q) (hC : 0 < C) (n : ℕ) (hn : 2 ≤ n) :
    fseq q C (n + 1) / fseq q C n = (↑(n - 1)) * C * (q ^ n)⁻¹ := by
  have hq0 : 0 < q := by linarith
  unfold fseq
  have hfn : (n + 1) - 2 = n - 1 := by omega
  rw [hfn, fact_step n hn, tri_succ n, pow_add]
  have hpos1 : (0 : ℝ) < q ^ (n * (n - 1) / 2) := by positivity
  have hpos2 : (0 : ℝ) < q ^ n := by positivity
  have hC0 : C ≠ 0 := ne_of_gt hC
  push_cast; field_simp; ring

private lemma ratio_tendsto (q C : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹) atTop (𝓝 0) := by
  have hr : |q⁻¹| < 1 := by
    rw [abs_of_pos (by positivity), inv_lt_one_iff₀]; right; exact hq
  have hbase : Tendsto (fun n : ℕ => (↑n : ℝ) * (q⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one hr
  have hsq : Tendsto (fun n : ℕ => (↑(n - 1) : ℝ) * (q⁻¹) ^ n) atTop (𝓝 0) := by
    apply squeeze_zero (f := fun n : ℕ => (↑(n - 1) : ℝ) * (q⁻¹) ^ n)
      (g := fun n => (↑n : ℝ) * (q⁻¹) ^ n) (fun n => by positivity) ?_ hbase
    intro n
    have hb : (0 : ℝ) ≤ (q⁻¹) ^ n := by positivity
    have hle : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    nlinarith [hle, hb]
  have heq : (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹)
      = (fun n : ℕ => C * ((↑(n - 1) : ℝ) * (q⁻¹) ^ n)) := by
    funext n; rw [inv_pow]; ring
  rw [heq]; simpa using hsq.const_mul C

/-- **The combine asymptotic** (Aristotle, verified). -/
theorem combine_asymptotic (q C : ℝ) (hq : 1 < q) (hC : 0 < C) :
    Tendsto (fun n : ℕ => (Nat.factorial (n - 2) : ℝ) * C ^ n * (q ^ (n * (n - 1) / 2))⁻¹)
      atTop (nhds 0) := by
  have hsummable : Summable (fseq q C) := by
    apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
    · filter_upwards with n using ne_of_gt (fseq_pos q C hq hC n)
    · have hcongr : (fun n : ℕ => ‖fseq q C (n + 1)‖ / ‖fseq q C n‖)
          =ᶠ[atTop] (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹) := by
        filter_upwards [eventually_ge_atTop 2] with n hn
        rw [Real.norm_of_nonneg (le_of_lt (fseq_pos q C hq hC _)),
            Real.norm_of_nonneg (le_of_lt (fseq_pos q C hq hC _))]
        exact fseq_ratio q C hq hC n hn
      exact (ratio_tendsto q C hq).congr' hcongr.symm
  exact hsummable.tendsto_atTop_zero

/-- **O2 — error → 0 (Borwein Lemma 4, combine step), PROVED.** The cleared error `β^{2n}·Wₙ·Eₙ → 0`.
Squeeze: `cleared_error_le` bounds `|β^{2n}WₙEₙ|` by `2·(n-2)!·(9c)ⁿ·(q^{n(n-1)/2})⁻¹`, which
`combine_asymptotic` sends to `0`. -/
lemma cleared_error_tendsto :
    Filter.Tendsto (fun n => (βB : ℝ) ^ (2 * n) * Wterm n * Eterm n) Filter.atTop (nhds 0) := by
  have hg : Tendsto (fun n => 2 * ((Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
      * (qB ^ (n * (n - 1) / 2))⁻¹)) atTop (𝓝 0) := by
    simpa using (combine_asymptotic qB (9 * cB) one_lt_qB (by have := cB_pos; positivity)).const_mul 2
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have h := cleared_error_le hn
  rw [gauss_Icc' n] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **O4 — reduction `S ↔ z`, PROVED.** Per-term `(1 − c·q^{j+1})⁻¹ = −3/(2^{j+4}−3)`, so
`zB = −3·∑_{j} 1/(2^{(j+2)+2}−3) = −3·(S − 1 − 1/5) = −3·S + 18/5`. Irrationality is invariant
under the nonzero-rational affine map. -/
lemma irrational_S_iff_zB : Irrational S ↔ Irrational zB := by
  -- Summability (auto-formalized by Aristotle, verified axiom-clean; compare `∑ 2^{-n}`);
  -- lifted to `S_summable` in `Basic.lean`.
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)) := S_summable
  have hkey : zB = -3 * S + 18 / 5 := by
    have hterm : ∀ j : ℕ,
        (1 - cB * qB ^ (j + 1))⁻¹ = -3 * ((1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3)) := by
      intro j
      have hp2 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hexp : (2 : ℝ) ^ ((j + 2) + 2) = 8 * 2 ^ (j + 1) := by
        rw [show (j + 2) + 2 = (j + 1) + 3 from by ring, pow_add]; ring
      rw [hexp]; simp only [cB, qB]
      have hd2 : (1 : ℝ) - 8 / 3 * 2 ^ (j + 1) ≠ 0 := ne_of_lt (by nlinarith [hp2])
      have hd1 : (8 : ℝ) * 2 ^ (j + 1) - 3 ≠ 0 := ne_of_gt (by nlinarith [hp2])
      rw [inv_eq_one_div, mul_one_div, div_eq_div_iff hd2 hd1]
      ring
    rw [zB, tsum_congr hterm, tsum_mul_left]
    have hsum1 : Summable (fun i : ℕ => (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3)) :=
      hsummable.comp_injective (add_left_injective 1)
    have e1 : S = (1 : ℝ) / ((2 : ℝ) ^ (0 + 2) - 3)
        + ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3) := hsummable.tsum_eq_zero_add
    have e2 : (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3))
        = (1 : ℝ) / ((2 : ℝ) ^ ((0 + 1) + 2) - 3)
          + ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (((i + 1) + 1) + 2) - 3) := hsum1.tsum_eq_zero_add
    have htail : (∑' j : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3)) = S - 6 / 5 := by
      have hconv : (∑' j : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3))
          = ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (((i + 1) + 1) + 2) - 3) := rfl
      rw [hconv]
      have hSf0 : (1 : ℝ) / ((2 : ℝ) ^ (0 + 2) - 3) = 1 := by norm_num
      have hSf1 : (1 : ℝ) / ((2 : ℝ) ^ ((0 + 1) + 2) - 3) = 1 / 5 := by norm_num
      rw [hSf0] at e1
      rw [hSf1] at e2
      linarith [e1, e2]
    rw [htail]; ring
  rw [hkey, show (-3 : ℝ) * S + 18 / 5 = ((-3 : ℤ) : ℝ) * S + ((18 / 5 : ℚ) : ℝ) by push_cast; ring,
    irrational_add_ratCast_iff, irrational_intCast_mul_iff]
  exact ⟨fun h => ⟨by decide, h⟩, And.right⟩

/- `irrational_zB` and the headline `erdos_1050 : Irrational S` are assembled in `Integrality.lean`
(they need the `pVal`-based `borwein_integrality` theorem, which is downstream of `Pade.lean`). -/

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/QBinom.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Gaussian (q-)binomial coefficients — toward Borwein Lemma 2

The denominator polynomial `pₙ(c,q)` of Borwein's Padé approximants is built from Gaussian binomial
coefficients `[n choose k]_q`, and its **integrality** (Lemma 2) rests on the **Cauchy q-binomial
theorem**. mathlib has no q-binomial machinery, so we build the minimum here.

`qBin q n k` is defined by the q-Pascal recurrence, so it is *manifestly* an integer polynomial in
`q` (a `CommRing` element); no division. The Cauchy theorem is the engine that makes `pₙ ∈ ℤ[c,q]`.

This is a prerequisite for discharging the `borwein_integrality` axiom (O1); see `PENDING_WORK.md`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

/-- Gaussian binomial coefficient `[n choose k]_q`, via the q-Pascal recurrence
`[n+1, k+1]_q = q^{k+1}·[n, k+1]_q + [n, k]_q`. Integer-polynomial in `q` by construction. -/
def qBin {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => q ^ (k + 1) * qBin q n (k + 1) + qBin q n k

@[simp] lemma qBin_zero_right {R : Type*} [CommRing R] (q : R) (n : ℕ) : qBin q n 0 = 1 := by
  cases n <;> rfl

@[simp] lemma qBin_zero_succ {R : Type*} [CommRing R] (q : R) (k : ℕ) : qBin q 0 (k + 1) = 0 := rfl

lemma qBin_succ_succ {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    qBin q (n + 1) (k + 1) = q ^ (k + 1) * qBin q n (k + 1) + qBin q n k := rfl

/-- The Gaussian binomial vanishes above the diagonal: `[n,k]_q = 0` for `k > n`. -/
lemma qBin_eq_zero_of_lt {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∀ k, n < k → qBin q n k = 0 := by
  induction n with
  | zero => intro k hk; cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih => intro k hk; cases k with
    | zero => omega
    | succ k => rw [qBin_succ_succ, ih (k + 1) (by omega), ih k (by omega), mul_zero, add_zero]

/-- The Gaussian binomial on the diagonal is `1`: `[n,n]_q = 1`. -/
@[simp] lemma qBin_self {R : Type*} [CommRing R] (q : R) (n : ℕ) : qBin q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qBin_succ_succ, qBin_eq_zero_of_lt q n (n + 1) (by omega), mul_zero,
      zero_add, ih]

/-- The q-integer: `[n,1]_q = 1 + q + ⋯ + q^{n-1}`. -/
lemma qBin_one {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qBin q n 1 = ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp [qBin]
  | succ n ih =>
    rw [show (1 : ℕ) = 0 + 1 from rfl, qBin_succ_succ, qBin_zero_right, ih, pow_one,
      Finset.sum_range_succ', pow_zero, Finset.mul_sum]
    simp [pow_succ, mul_comm]

/-- `qBin` commutes with ring homomorphisms. In particular `qBin (2:ℝ) n k` is the integer
`qBin (2:ℤ) n k` cast to `ℝ` — the bridge that makes Borwein's `pₙ(c,q)` integer-valued at `q = 2`. -/
lemma qBin_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : R) :
    ∀ n k, qBin (f q) n k = f (qBin q n k)
  | _, 0 => by rw [qBin_zero_right, qBin_zero_right, map_one]
  | 0, _ + 1 => by rw [qBin_zero_succ, qBin_zero_succ, map_zero]
  | n + 1, k + 1 => by
      rw [qBin_succ_succ, qBin_succ_succ, qBin_map f q n (k + 1), qBin_map f q n k,
        map_add, map_mul, map_pow]

/-- Triangular-number identity in `ℕ`: `k*(k-1)/2 + k = (k+1)*((k+1)-1)/2`. -/
private lemma cauchy_tri_succ (k : ℕ) :
    k * (k - 1) / 2 + k = (k + 1) * ((k + 1) - 1) / 2 := by
  rcases k with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1 + 1) * (m + 1) = (c + (m + 1)) + (c + (m + 1)) := by
      have : (m + 1 + 1) * (m + 1) = m * (m + 1) + 2 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- Power-level triangular identity: `q^(k(k-1)/2) * q^k = q^((k+1)k/2)`. -/
private lemma cauchy_tri_pow {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    q ^ (k * (k - 1) / 2) * q ^ k = q ^ ((k + 1) * k / 2) := by
  rw [← pow_add]
  congr 1
  have h := cauchy_tri_succ k
  simpa [Nat.add_sub_cancel] using h

/-- **Cauchy q-binomial theorem** (the engine of Borwein Lemma 2):
`∏_{i<n} (1 + q^i·t) = ∑_{k≤n} q^{k(k-1)/2}·[n,k]_q·t^k`.

Borwein's form `∑_{m≤n} y^m q^{m(m+1)/2}[n,m]_q = ∏_{k=1}^n (1+y q^k)` is the `t = q·y` case.
Proved by induction on `n` via the q-Pascal recurrence (Aristotle-formalized, verified axiom-clean
in our kernel). -/
theorem qBin_cauchy {R : Type*} [CommRing R] (q t : R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + q ^ i * t)
      = ∑ k ∈ Finset.range (n + 1), q ^ (k * (k - 1) / 2) * qBin q n k * t ^ k := by
  induction n generalizing t with
  | zero => simp [qBin]
  | succ n ih =>
    set P : R := ∑ k ∈ Finset.range (n + 1),
        q ^ (k * (k - 1) / 2) * q ^ k * qBin q n k * t ^ k with hP
    set Q : R := ∑ k ∈ Finset.range (n + 1),
        q ^ ((k + 1) * k / 2) * qBin q n k * t ^ (k + 1) with hQ
    have hprod : ∏ i ∈ Finset.range (n + 1), (1 + q ^ i * t) = (1 + t) * P := by
      have ev : (∏ i ∈ Finset.range n, (1 + q ^ (i + 1) * t)) = P := by
        rw [show (∏ i ∈ Finset.range n, (1 + q ^ (i + 1) * t))
              = ∏ i ∈ Finset.range n, (1 + q ^ i * (q * t)) from
            Finset.prod_congr rfl (fun i _ => by rw [pow_succ]; ring), ih (q * t), hP]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_pow]; ring
      rw [Finset.prod_range_succ', ev, pow_zero, one_mul]
      ring
    set A : R := ∑ k ∈ Finset.range n,
        q ^ ((k + 1) * k / 2) * q ^ (k + 1) * qBin q n (k + 1) * t ^ (k + 1) with hA
    have hPA : P = 1 + A := by
      rw [hP, Finset.sum_range_succ', hA]
      simp only [Nat.add_sub_cancel, qBin, Nat.zero_sub, Nat.mul_zero, Nat.zero_div,
        pow_zero, mul_one]
      ring
    have hsplit : ∑ k ∈ Finset.range (n + 2),
        q ^ (k * (k - 1) / 2) * qBin q (n + 1) k * t ^ k = P + Q := by
      rw [Finset.sum_range_succ', hPA, hQ, hA]
      simp only [Nat.add_sub_cancel, qBin, Nat.zero_sub, Nat.mul_zero, Nat.zero_div,
        pow_zero, mul_one]
      rw [show (∑ k ∈ Finset.range (n + 1),
              q ^ ((k + 1) * k / 2) * (q ^ (k + 1) * qBin q n (k + 1) + qBin q n k)
                * t ^ (k + 1))
            = (∑ k ∈ Finset.range (n + 1),
                q ^ ((k + 1) * k / 2) * q ^ (k + 1) * qBin q n (k + 1) * t ^ (k + 1))
              + (∑ k ∈ Finset.range (n + 1),
                q ^ ((k + 1) * k / 2) * qBin q n k * t ^ (k + 1)) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)]
      rw [Finset.sum_range_succ, qBin_eq_zero_of_lt q n (n + 1) (Nat.lt_succ_self n)]
      ring
    have htP : t * P = Q := by
      rw [hP, hQ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show t * (q ^ (k * (k - 1) / 2) * q ^ k * qBin q n k * t ^ k)
            = (q ^ (k * (k - 1) / 2) * q ^ k) * qBin q n k * t ^ (k + 1) by ring, cauchy_tri_pow]
    rw [hprod, hsplit, add_mul, one_mul, htP]

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/Pade.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The q-Padé denominator `pₙ` and its integrality (toward Borwein Lemma 2)

`pVal n` is the real value of Borwein's denominator polynomial `pₙ(c,q)` at `c = 8/3`, `q = 2`
(second form, via Gaussian binomials). `pInt n` is the `3^{n-1}`-cleared integer version. The lemma
`pInt_cast` (Borwein Lemma 2, integrality half) says they agree after clearing — so `3^{n-1}·pₙ ∈ ℤ`.

This is a prerequisite for discharging `borwein_integrality` (O1); the remaining piece is the
residue identity (Lemma 1, see `ON-LINE-REQUEST.md`).
-/

namespace LeanGallery.NumberTheory.Erdos1050
open scoped BigOperators

/-- `pₙ(8/3, 2)` (Borwein Lemma 2, second form): the real-valued q-Padé denominator. -/
noncomputable def pVal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-cB) ^ k * qB ^ (k * (k + 3) / 2)
    * qBin qB (n - 1) k * qBin qB (n + k - 1) (n - 1)

/-- The `3^{n-1}`-cleared **integer** q-Padé denominator. -/
def pInt (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-8) ^ k * 3 ^ (n - 1 - k) * 2 ^ (k * (k + 3) / 2)
    * qBin (2 : ℤ) (n - 1) k * qBin (2 : ℤ) (n + k - 1) (n - 1)

/-- `qBin` at the real base `2` is the integer `qBin` cast to `ℝ`. -/
lemma qBin_two_cast (m j : ℕ) : qBin qB m j = ((qBin (2 : ℤ) m j : ℤ) : ℝ) := by
  simpa [qB] using qBin_map (Int.castRingHom ℝ) (2 : ℤ) m j

/-- **Borwein Lemma 2 (integrality of `pₙ`).** `(pInt n : ℝ) = 3^{n-1}·pₙ(8/3,2)`, so the cleared
q-Padé denominator is an integer. -/
lemma pInt_cast (n : ℕ) : (pInt n : ℝ) = 3 ^ (n - 1) * pVal n := by
  rw [pInt, pVal, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hclear : (3 : ℝ) ^ (n - 1) * (-cB) ^ k = (-8) ^ k * 3 ^ (n - 1 - k) := by
    have h3 : (3 : ℝ) ^ (n - 1) = 3 ^ k * 3 ^ (n - 1 - k) := by rw [← pow_add]; congr 1; omega
    have hcB : (-cB : ℝ) = -8 / 3 := by simp only [cB]; ring
    rw [h3, hcB, mul_assoc, mul_comm ((3 : ℝ) ^ (n - 1 - k)) ((-8 / 3 : ℝ) ^ k), ← mul_assoc,
      ← mul_pow, show (3 : ℝ) * (-8 / 3) = -8 by ring]
  rw [qBin_two_cast (n - 1) k, qBin_two_cast (n + k - 1) (n - 1), ← hclear,
    show qB = (2 : ℝ) from rfl]
  ring

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/Residue.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Elementary (contour-free) proof of Borwein's residue identity — Piece II: the geometric collapse

The previous laps reduced Erdős #1050 to the single axiom `borwein_integrality`, whose only deep
component is Borwein's Lemma 1 (the residue identity). This file begins a **fully elementary** proof
of that identity (no contour integral); see `RESIDUE-IDENTITY-ELEMENTARY-PROOF.md` for the full
strategy. The crux is the **collapse of the auxiliary series**

  `T_i := ∑_{h≥1} q^{-i·h} / (1 − c·q^h)  =  c^i · z  +  R_i`,    `R_i ∈ ℚ`,

which is what the contour integral was hiding. This is proved here by the per-term identity

  `q^{-i·h}/(1−c·q^h) = q^{-i·h} + c · q^{-(i-1)·h}/(1−c·q^h)`

(`key_term` below), a geometric series, and induction on `i`. Indexing matches `zB`: we sum over
`j : ℕ` with `h = j + 1`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Filter Topology

/-- The rational correction `R_i = ∑_{l=1}^{i} c^{i-l}/(q^l − 1)`, via the recurrence
`R_{i+1} = 1/(q^{i+1} − 1) + c·R_i`, `R_0 = 0`. -/
noncomputable def Rrat : ℕ → ℝ
  | 0 => 0
  | (i + 1) => 1 / (qB ^ (i + 1) - 1) + cB * Rrat i

/-- The auxiliary series `T_i = ∑_{h≥1} q^{-i·h}·(1 − c·q^h)⁻¹` (with `h = j + 1`).
All exponents are non-positive, so we use `(qB^…)⁻¹` (natural power) rather than `zpow`. -/
noncomputable def Tser (i : ℕ) : ℝ :=
  ∑' j : ℕ, (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹

/-- The per-term collapse identity. With `P = q^h` (`P ≠ 0`, `1 − c·P ≠ 0`):
`(P^{i+1})⁻¹·(1−cP)⁻¹ = (P^{i+1})⁻¹ + c·(P^i)⁻¹·(1−cP)⁻¹`. -/
lemma key_term (P : ℝ) (i : ℕ) (hP : P ≠ 0) (hcP : 1 - cB * P ≠ 0) :
    (P ^ (i + 1))⁻¹ * (1 - cB * P)⁻¹
      = (P ^ (i + 1))⁻¹ + cB * (P ^ i)⁻¹ * (1 - cB * P)⁻¹ := by
  have hPi : P ^ i ≠ 0 := pow_ne_zero i hP
  have hPi1 : P ^ (i + 1) ≠ 0 := pow_ne_zero (i + 1) hP
  field_simp
  ring

/-- `q^{j+1} ≠ 0`. -/
private lemma qpow_ne (j : ℕ) : qB ^ (j + 1) ≠ 0 := pow_ne_zero _ qB_ne

/-- Per-term absolute bound `|q^{-i(j+1)}·u_{j+1}| ≤ (1/2)^{j+1}`. -/
lemma Tterm_abs_le (i j : ℕ) :
    |(qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹| ≤ (1 / 2 : ℝ) ^ (j + 1) := by
  rw [abs_mul]
  have h1 : |(qB ^ (i * (j + 1)))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt one_lt_qB))
  have h2 : |(1 - cB * qB ^ (j + 1))⁻¹| ≤ qB ^ (-((j : ℤ) + 1)) := by
    have h := inv_cqpow_le (a := (j : ℤ) + 1) (by omega)
    have he : qB ^ ((j : ℤ) + 1) = qB ^ (j + 1) := by
      rw [← zpow_natCast qB (j + 1)]; norm_num
    rwa [he] at h
  have h3 : qB ^ (-((j : ℤ) + 1)) = (1 / 2 : ℝ) ^ (j + 1) := by
    rw [show (-((j : ℤ) + 1)) = -(((j + 1 : ℕ) : ℤ)) by push_cast; ring, qB_neg_zpow]
  calc |(qB ^ (i * (j + 1)))⁻¹| * |(1 - cB * qB ^ (j + 1))⁻¹|
      ≤ 1 * qB ^ (-((j : ℤ) + 1)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (1 / 2 : ℝ) ^ (j + 1) := by rw [one_mul, h3]

/-- `T_i` is summable (dominated by the geometric `(1/2)^{j+1}`). -/
lemma Tser_summable (i : ℕ) :
    Summable (fun j : ℕ => (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ (j + 1))
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  · intro j; rw [Real.norm_eq_abs]; exact Tterm_abs_le i j

/-- `T_0 = z`. -/
lemma Tser_zero : Tser 0 = zB := by
  unfold Tser zB
  apply tsum_congr
  intro j
  simp

/-- The geometric piece `∑_{j} q^{-(i+1)(j+1)} = 1/(q^{i+1} − 1)`. -/
lemma geom_piece (i : ℕ) :
    ∑' j : ℕ, (qB ^ ((i + 1) * (j + 1)))⁻¹ = 1 / (qB ^ (i + 1) - 1) := by
  set r : ℝ := (qB ^ (i + 1))⁻¹ with hr
  have hrpos : 0 < r := by rw [hr]; exact inv_pos.mpr (pow_pos qB_pos _)
  have hqgt : (1 : ℝ) < qB ^ (i + 1) := by
    calc (1 : ℝ) < qB := one_lt_qB
      _ = qB ^ 1 := (pow_one qB).symm
      _ ≤ qB ^ (i + 1) := pow_le_pow_right₀ (le_of_lt one_lt_qB) (by omega)
  have hr1 : r < 1 := by rw [hr]; exact inv_lt_one_of_one_lt₀ hqgt
  have hconv : ∀ j : ℕ, (qB ^ ((i + 1) * (j + 1)))⁻¹ = r * r ^ j := by
    intro j; rw [hr, ← pow_succ', inv_pow, ← pow_mul]
  rw [tsum_congr hconv, tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt hrpos) hr1, hr]
  have hx1 : (1 : ℝ) - (qB ^ (i + 1))⁻¹ ≠ 0 := by
    have : (qB ^ (i + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqgt
    linarith
  have hx0 : (qB : ℝ) ^ (i + 1) ≠ 0 := ne_of_gt (pow_pos qB_pos _)
  have hx2 : (qB : ℝ) ^ (i + 1) - 1 ≠ 0 := by linarith [hqgt]
  field_simp

/-- The geometric piece is summable. -/
lemma geom_summable (i : ℕ) : Summable (fun j : ℕ => (qB ^ ((i + 1) * (j + 1)))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ (j + 1))
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  · intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
    have h1 : (qB ^ ((i + 1) * (j + 1)))⁻¹ ≤ (qB ^ (j + 1))⁻¹ :=
      inv_anti₀ (pow_pos qB_pos _)
        (pow_le_pow_right₀ (le_of_lt one_lt_qB) (by rw [Nat.succ_mul]; omega))
    calc (qB ^ ((i + 1) * (j + 1)))⁻¹ ≤ (qB ^ (j + 1))⁻¹ := h1
      _ = (1 / 2 : ℝ) ^ (j + 1) := by
          rw [show (1 / 2 : ℝ) = qB⁻¹ by norm_num [qB], inv_pow]

/-- **The collapse recurrence**: `T_{i+1} = 1/(q^{i+1} − 1) + c·T_i`. -/
lemma Tser_succ (i : ℕ) : Tser (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Tser i := by
  unfold Tser
  have hterm : ∀ j : ℕ,
      (qB ^ ((i + 1) * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹
        = (qB ^ ((i + 1) * (j + 1)))⁻¹
          + cB * (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹ := by
    intro j
    have hk := key_term (qB ^ (j + 1)) i (qpow_ne j) (one_sub_cqpow_ne (k := j + 1) (by omega))
    have e1 : qB ^ ((i + 1) * (j + 1)) = (qB ^ (j + 1)) ^ (i + 1) := by
      rw [← pow_mul, Nat.mul_comm]
    have e2 : qB ^ (i * (j + 1)) = (qB ^ (j + 1)) ^ i := by
      rw [← pow_mul, Nat.mul_comm]
    rw [e1, e2]; exact hk
  rw [tsum_congr hterm]
  have hsum_rest : Summable
      (fun j : ℕ => cB * (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹) := by
    simp_rw [mul_assoc]
    exact (Tser_summable i).mul_left cB
  rw [Summable.tsum_add (geom_summable i) hsum_rest, geom_piece i]
  congr 1
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- **Piece II — the collapse**: `T_i = c^i · z + R_i`. Every auxiliary series is
`(rational) + (rational)·z`. Proved by induction on `i` from the recurrence. -/
theorem Tser_collapse (i : ℕ) : Tser i = cB ^ i * zB + Rrat i := by
  induction i with
  | zero => rw [Tser_zero, show Rrat 0 = 0 from rfl]; ring
  | succ i ih =>
      rw [Tser_succ, ih, show Rrat (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Rrat i from rfl]
      ring

/- ### Assembly building block: the product form of `Iₘ`

The lead factor `(1 − c·q^{m+n})⁻¹` is the `k = n` term of the `c`-product, so `Iₘ` separates into a
`q`-numerator times a clean `c`-product over `1..n`. This is the first algebraic step toward the
residue identity (then Piece I partial-fractions the `c`-product, Piece II collapses the result). -/

/-- `Iₘ = −(∏_{k=1}^{n-1}(1−q^{k−m}))·∏_{k=1}^{n}(1−c·q^{k+m})⁻¹` (for `n ≥ 1`). -/
lemma Iterm_prod_form (n m : ℕ) (hn : 1 ≤ n) :
    Iterm n m
      = -((∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)))
          * ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + m))⁻¹) := by
  rw [Iterm, Finset.prod_mul_distrib,
    show ((m : ℤ) + n) = ((n : ℤ) + m) from by ring,
    show Finset.Icc 1 n = Finset.Icc 1 ((n - 1) + 1) from by rw [Nat.sub_add_cancel hn],
    Finset.prod_Icc_succ_top (by omega : 1 ≤ (n - 1) + 1), Nat.sub_add_cancel hn]
  ring

/-- **`q`-numerator expansion** `D_m = ∏_{k=1}^{n-1}(1−q^{k−m})` as a sum of monomials in `q^{−m}`:
each subset `t` contributes weight `(q^{−m})^{|t|}`. This produces exactly the `q^{−i·m}` weights
that the collapse `Tser_collapse` consumes (with `i = |t|`). -/
lemma Dterm_expand (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * ((qB ^ m)⁻¹) ^ t.card := by
  have hfac : ∀ k : ℕ, (1 : ℝ) - qB ^ ((k : ℤ) - m) = 1 + (-(qB ^ k)) * (qB ^ m)⁻¹ := by
    intro k
    rw [zpow_sub₀ qB_ne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    ring
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- **Piece IIIa — Cauchy expansion of the `c`-product** `∏_{k=1}^{n-1}(1 − c·q^{k+j})`, a direct
application of the Cauchy q-binomial theorem `qBin_cauchy` (reindex `k = 1 + i`, `t = −c·q^{j+1}`).
This is the first half of the first-form = second-form identity (Borwein Lemma 2); the second half is
the q-Lagrange identity `∑_j μ_j q^{jk} = q^k[n+k−1,n−1]_q` (Piece IIIb). -/
lemma cprod_cauchy {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
      = ∑ i ∈ Finset.range n,
          qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i) := by
  have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.prod_Ico_eq_prod_range]
  have hterm : ∀ k, (1 - cB * qB ^ (1 + k + j)) = 1 + qB ^ k * (-cB * qB ^ (j + 1)) := by
    intro k
    rw [show 1 + k + j = k + (j + 1) from by ring, pow_add]; ring
  rw [Finset.prod_congr rfl (fun k _ => hterm k), qBin_cauchy qB (-cB * qB ^ (j + 1)) (n - 1),
    Nat.sub_add_cancel hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← pow_mul]
  ring

/-- Exponent bookkeeping `i(i−1)/2 + 2i = i(i+3)/2` (the `qBin_cauchy` exponent plus the two `q^i`
factors from the q-Lagrange step combine into the `pVal` exponent). -/
private lemma exp_iden (i : ℕ) : i * (i - 1) / 2 + 2 * i = i * (i + 3) / 2 := by
  rcases i with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1) * (m + 1 + 3) = (c + 2 * (m + 1)) + (c + 2 * (m + 1)) := by
      have : (m + 1) * (m + 1 + 3) = m * (m + 1) + 4 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- The q-Lagrange weight `μ_j = ∏_{l∈[1,n], l≠j}(1 − q^l/q^j)⁻¹` (independent of `c`, `m`). -/
noncomputable def muW (n j : ℕ) : ℝ :=
  ∏ l ∈ (Finset.Icc 1 n).erase j, (1 - qB ^ l / qB ^ j)⁻¹

/-- Borwein's q-Padé denominator in **first form** `pₙ = ∑_{j=1}^n μ_j·∏_{k=1}^{n-1}(1−c q^{k+j})`. -/
noncomputable def pFirst (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))

/-- **Piece III — first form = second form** (Borwein Lemma 2), conditional on the q-Lagrange
identity `qLag` (Piece IIIb, `aristotle/QLagrange.lean`). Assembled from the Cauchy expansion
`cprod_cauchy` + a finite sum swap + the exponent identity `exp_iden`. NO new axiom: `qLag` is a
hypothesis, to be discharged once IIIb is proved. -/
theorem pFirst_eq_pVal {n : ℕ} (hn : 1 ≤ n)
    (qLag : ∀ i, i < n →
      ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1)) :
    pFirst n = pVal n := by
  rw [pFirst, pVal]
  -- expand the c-product inside the j-sum via cprod_cauchy
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
        = ∑ i ∈ Finset.range n,
            muW n j * (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i)) := by
    intro j _
    rw [cprod_cauchy hn j, Finset.mul_sum]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  -- pull the i-dependent factors out of the j-sum, leaving ∑_j μ_j (qB^j)^i
  have hfac : ∀ j ∈ Finset.Icc 1 n,
      muW n j * (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i))
        = (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ i)
          * (muW n j * (qB ^ j) ^ i) := by
    intro j _
    rw [show (j + 1) * i = i + j * i from by ring, pow_add, pow_mul]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, qLag i hi]
  rw [show i * (i + 3) / 2 = i * (i - 1) / 2 + 2 * i from (exp_iden i).symm, pow_add]
  ring

/- ### Assembly building block: the inner tail-sum collapse

In `Eterm n = ∑'_m Iₘ`, after the partial fraction (Piece I) and the `q`-numerator expansion
(`Dterm_expand`), the inner sum over `m ≥ n` of `q^{−i·m}·u_{m+j}` appears. Reindexing onto the
`Tser` grid and applying `Tser_collapse` turns it into `(rational) + (rational)·z`. This is the step
that makes the whole series collapse to `−pVal·z + (rational)`. -/

/-- The inner tail series `∑_{m≥0} q^{−i(n+m)}·u_{(n+m)+j}` appearing in the assembly. -/
noncomputable def Stail (i j n : ℕ) : ℝ :=
  ∑' m : ℕ, (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹

/-- **Tail collapse**: the inner series equals `q^{ij}·(Tser i − head)`, a finite reindex onto the
`Tser` grid. Combined with `Tser_collapse`, this is `q^{ij}·(c^i·z + R_i − head)`. -/
lemma Stail_collapse (i j n : ℕ) (hnj : 1 ≤ n + j) :
    Stail i j n
      = qB ^ (i * j) * (Tser i
          - ∑ m' ∈ Finset.range (n + j - 1),
              (qB ^ (i * (m' + 1)))⁻¹ * (1 - cB * qB ^ (m' + 1))⁻¹) := by
  have hterm : ∀ m : ℕ,
      (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹
        = qB ^ (i * j) * ((qB ^ (i * ((m + (n + j - 1)) + 1)))⁻¹
            * (1 - cB * qB ^ ((m + (n + j - 1)) + 1))⁻¹) := by
    intro m
    have h1 : (m + (n + j - 1)) + 1 = (n + m) + j := by omega
    have hw : (qB ^ (i * (n + m)))⁻¹ = qB ^ (i * j) * (qB ^ (i * ((n + m) + j)))⁻¹ := by
      rw [show i * ((n + m) + j) = i * j + i * (n + m) from by ring, pow_add, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ qB_ne), one_mul]
    rw [h1, hw]; ring
  rw [Stail, tsum_congr hterm, tsum_mul_left]
  congr 1
  have hsum := Summable.sum_add_tsum_nat_add (n + j - 1) (Tser_summable i)
  rw [show Tser i = ∑' m : ℕ, (qB ^ (i * (m + 1)))⁻¹ * (1 - cB * qB ^ (m + 1))⁻¹ from rfl]
  linarith [hsum]

/-- **z-coefficient bridge**: `pFirst` re-expanded over the same subsets `t ⊆ [1,n−1]` that the
`q`-numerator `Dterm_expand` produces. This matches the assembly's z-coefficient
`−∑_t (∏_{k∈t}−q^k)·c^{|t|}·(∑_j μ_j (q^j)^{|t|})` exactly (since `∏_{k∈t}(−c·q^k) = (∏−q^k)·c^{|t|}`),
so the whole double series' z-part is `−pFirst·z = −pVal·z` — **without** needing the `e_i` or
q-Lagrange identities for the z-collection. -/
lemma pFirst_powerset (n : ℕ) :
    pFirst n = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-cB * qB ^ k)) * ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ t.card := by
  rw [pFirst]
  have hexp : ∀ j, ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-cB * qB ^ k)) * (qB ^ j) ^ t.card := by
    intro j
    have hf : ∀ k, (1 : ℝ) - cB * qB ^ (k + j) = 1 + (-cB * qB ^ k) * qB ^ j := by
      intro k; rw [pow_add]; ring
    rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hexp j])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/- ### Piece I — the partial-fraction decomposition (Aristotle-harvested, verified axiom-clean)

`1/∏_{k=1}^n(1 − x·q^k) = ∑_{j=1}^n μ_j/(1 − x·q^j)` over the `n` distinct simple poles `x = q^{−j}`,
with `μ_j = ∏_{k≠j}(1 − q^k/q^j)⁻¹`. Proved via mathlib's `Lagrange.sum_basis` (the Lagrange basis
polynomials sum to `1`). Aristotle run `70eb84a6`; it correctly flagged that `n = 0` is false and
added `1 ≤ n`. In the assembly, specialize `x = c·q^m` so `1 − x·q^k = 1 − c·q^{m+k}` and
`μ_j = muW n j`. -/

/-- The nodes `(q^k)⁻¹` are pairwise distinct on `Icc 1 n` (for `q > 1`). -/
lemma pf_injOn (q : ℝ) (hq : 1 < q) (n : ℕ) :
    Set.InjOn (fun k => (q ^ k)⁻¹) (↑(Finset.Icc 1 n)) := by
  exact fun x hx y hy hxy => by rw [inv_inj, pow_right_inj₀] at hxy <;> linarith

/-- Per-factor identity bridging the Lagrange-basis factor and the residue factor. -/
lemma pf_factor (q : ℝ) (hq : 1 < q) (x : ℝ) (j k : ℕ) :
    ((q ^ j)⁻¹ - (q ^ k)⁻¹)⁻¹ * (x - (q ^ k)⁻¹)
      = (1 - q ^ k / q ^ j)⁻¹ * (1 - x * q ^ k) := by
  field_simp
  rw [← neg_div_neg_eq, neg_sub, neg_sub]

/-- Cleared form `∑_{j=1}^n μ_j·∏_{k≠j}(1 − x·q^k) = 1` (Lagrange interpolation of the constant 1). -/
lemma pf_cleared (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹)
          * ∏ k ∈ (Finset.Icc 1 n).erase j, (1 - x * q ^ k) = 1 := by
  have h_sum_basis : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        (Polynomial.C ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹
          * (Polynomial.X - Polynomial.C ((q ^ k : ℝ)⁻¹)))) = 1 := by
    convert Lagrange.sum_basis (pf_injOn q hq n) (Finset.nonempty_Icc.mpr hn) using 1
    simp only [Lagrange.basis, Lagrange.basisDivisor]
  have h_eval : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹ * (x - (q ^ k : ℝ)⁻¹)) = 1 := by
    convert congr_arg (Polynomial.eval x) h_sum_basis using 1
    · simp +decide [Polynomial.eval_finsetSum, Polynomial.eval_prod]
    · norm_num
  convert h_eval using 2
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [pf_factor q hq x _ _]

/-- **Piece I — partial-fraction decomposition** `∏_{k=1}^n(1 − x·q^k)⁻¹ = ∑_j μ_j (1 − x·q^j)⁻¹`. -/
theorem partial_fraction (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : ∀ k, 1 ≤ k → k ≤ n → 1 - x * q ^ k ≠ 0) :
    (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹
      = ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹) * (1 - x * q ^ j)⁻¹ := by
  convert (Eq.symm ?_) using 1
  convert congr_arg (fun y => y * (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹)
    (pf_cleared q hq n hn x) using 1
  · rw [Finset.sum_mul _ _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul _ _ hj, mul_assoc, mul_comm]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    exact Or.inl (by rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.1)
        (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.2)), one_mul])
  · ring

/- ### Negative-base (`1 < |q|`) partial-fraction decomposition.

Parallel to `pf_injOn`/`pf_factor`/`pf_cleared`/`partial_fraction`, but with the hypothesis weakened
from `1 < q` to `1 < |q|` so it covers negative bases `q ≤ −2`. The only sign-dependent step is node
distinctness (`pf_injOn_abs`), proved via strict monotonicity of `k ↦ |q|^k`; everything else is the
same Lagrange-basis argument. These feed the negative-base residue identity (`ItermG_triple` for
`1 < |q|` in `GeneralResidue.lean`). Left untouched: the `1 < q` originals (the axiom-clean q=2
`erdos_1050` chain routes through those). -/

/-- The nodes `(q^k)⁻¹` are pairwise distinct on `Icc 1 n` for `1 < |q|` (any sign of `q`). -/
lemma pf_injOn_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) :
    Set.InjOn (fun k => (q ^ k)⁻¹) (↑(Finset.Icc 1 n)) := by
  intro x _ y _ hxy
  simp only [inv_inj] at hxy
  have habs : |q| ^ x = |q| ^ y := by rw [← abs_pow, ← abs_pow, hxy]
  exact (StrictMono.injective (fun a b h => pow_lt_pow_right₀ hq h)) habs

/-- Per-factor identity bridging the Lagrange-basis factor and the residue factor (`q ≠ 0`). -/
lemma pf_factor_abs (q : ℝ) (hq0 : q ≠ 0) (x : ℝ) (j k : ℕ) :
    ((q ^ j)⁻¹ - (q ^ k)⁻¹)⁻¹ * (x - (q ^ k)⁻¹)
      = (1 - q ^ k / q ^ j)⁻¹ * (1 - x * q ^ k) := by
  have hj : (q ^ j : ℝ) ≠ 0 := pow_ne_zero _ hq0
  have hk : (q ^ k : ℝ) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  rw [← neg_div_neg_eq, neg_sub, neg_sub]

/-- Cleared form `∑_{j} μ_j·∏_{k≠j}(1 − x·q^k) = 1` for `1 < |q|`. -/
lemma pf_cleared_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹)
          * ∏ k ∈ (Finset.Icc 1 n).erase j, (1 - x * q ^ k) = 1 := by
  have hq0 : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  have h_sum_basis : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        (Polynomial.C ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹
          * (Polynomial.X - Polynomial.C ((q ^ k : ℝ)⁻¹)))) = 1 := by
    convert Lagrange.sum_basis (pf_injOn_abs q hq n) (Finset.nonempty_Icc.mpr hn) using 1
    simp only [Lagrange.basis, Lagrange.basisDivisor]
  have h_eval : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹ * (x - (q ^ k : ℝ)⁻¹)) = 1 := by
    convert congr_arg (Polynomial.eval x) h_sum_basis using 1
    · simp +decide [Polynomial.eval_finsetSum, Polynomial.eval_prod]
    · norm_num
  convert h_eval using 2
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [pf_factor_abs q hq0 x _ _]

/-- **Piece I — partial-fraction decomposition for `1 < |q|`** (negative base allowed). -/
theorem partial_fraction_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : ∀ k, 1 ≤ k → k ≤ n → 1 - x * q ^ k ≠ 0) :
    (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹
      = ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹) * (1 - x * q ^ j)⁻¹ := by
  convert (Eq.symm ?_) using 1
  convert congr_arg (fun y => y * (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹)
    (pf_cleared_abs q hq n hn x) using 1
  · rw [Finset.sum_mul _ _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul _ _ hj, mul_assoc, mul_comm]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    exact Or.inl (by rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.1)
        (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.2)), one_mul])
  · ring

/- ### Final assembly: `Eterm n = −pVal n · zB + (rational)`

Combine all pieces. First `Iterm_triple` rewrites each `Iₘ` as a finite double sum (over subsets `t`
of the `q`-numerator and poles `j` of the partial fraction). Then `Eterm_eq_Stail` pulls the two
finite sums out of `∑'_m` (each inner series is `Stail`). Finally `Stail_collapse` + `Tser_collapse`
+ `pFirst_powerset` collect the z-coefficient as `−pFirst = −pVal`. -/

/-- Each `Iₘ` (here `M` general) as a finite double sum over subsets `t ⊆ [1,n−1]` and poles
`j ∈ [1,n]`, via `Iterm_prod_form` (split) + `partial_fraction` (Piece I) + `Dterm_expand`. -/
lemma Iterm_triple {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    Iterm n M
      = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ t, (-qB ^ k)) * muW n j
            * (((qB ^ M)⁻¹) ^ t.card * (1 - cB * qB ^ (M + j))⁻¹) := by
  have hpm : ∀ a : ℕ, cB * qB ^ M * qB ^ a = cB * qB ^ (M + a) := by
    intro a; rw [pow_add]; ring
  have hC : ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + M))⁻¹
      = ∑ j ∈ Finset.Icc 1 n, muW n j * (1 - cB * qB ^ (M + j))⁻¹ := by
    have hconv : ∀ k : ℕ, (1 : ℝ) - cB * qB ^ ((k : ℤ) + M) = 1 - cB * qB ^ M * qB ^ k := by
      intro k
      have he : ((k : ℤ) + M) = ((k + M : ℕ) : ℤ) := by push_cast; ring
      rw [he, zpow_natCast, pow_add]; ring
    have hx : ∀ k, 1 ≤ k → k ≤ n → 1 - cB * qB ^ M * qB ^ k ≠ 0 := by
      intro k _ _; rw [hpm k]; exact one_sub_cqpow_ne (by omega)
    have hprodeq : ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + M))⁻¹
        = (∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ M * qB ^ k))⁻¹ := by
      simp only [hconv, Finset.prod_inv_distrib]
    rw [hprodeq, partial_fraction qB one_lt_qB n hn (cB * qB ^ M) hx]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpm j]
    rfl
  rw [Iterm_prod_form n M hn, hC, Dterm_expand n M]
  rw [Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `Stail`'s summand is summable (dominated by the geometric `(1/2)^m`). -/
lemma Stail_summable {n : ℕ} (hn : 1 ≤ n) (i j : ℕ) :
    Summable (fun m : ℕ => (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun m => (1 / 2 : ℝ) ^ m)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro m
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |(qB ^ (i * (n + m)))⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt one_lt_qB))
    have h2 : |(1 - cB * qB ^ ((n + m) + j))⁻¹| ≤ qB ^ (-(((n + m) + j : ℕ) : ℤ)) := by
      have h := inv_cqpow_le (a := (((n + m) + j : ℕ) : ℤ)) (by exact_mod_cast (by omega : 1 ≤ (n + m) + j))
      rwa [zpow_natCast] at h
    have h3 : qB ^ (-(((n + m) + j : ℕ) : ℤ)) ≤ (1 / 2 : ℝ) ^ m := by
      rw [show (-(((n + m) + j : ℕ) : ℤ)) = -((m : ℤ) + (n + j)) from by push_cast; ring]
      calc qB ^ (-((m : ℤ) + (n + j))) ≤ qB ^ (-(m : ℤ)) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
        _ = (1 / 2 : ℝ) ^ m := qB_neg_zpow m
    calc |(qB ^ (i * (n + m)))⁻¹| * |(1 - cB * qB ^ ((n + m) + j))⁻¹|
        ≤ 1 * qB ^ (-(((n + m) + j : ℕ) : ℤ)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) ^ m := by rw [one_mul]; exact h3

/-- **The pull-out**: `Eterm n` as a finite double sum of `Stail`'s, via `Iterm_triple` and pulling
the two finite sums out of `∑'_m` (`Summable.tsum_finsetSum`). -/
lemma Eterm_eq_Stail {n : ℕ} (hn : 1 ≤ n) :
    Eterm n = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * Stail t.card j n := by
  have hStail : ∀ (t : Finset ℕ) (j : ℕ),
      (fun m : ℕ => (∏ k ∈ t, (-qB ^ k)) * muW n j
          * (((qB ^ (n + m))⁻¹) ^ t.card * (1 - cB * qB ^ ((n + m) + j))⁻¹))
        = (fun m : ℕ => (∏ k ∈ t, (-qB ^ k)) * muW n j
          * ((qB ^ (t.card * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹)) := by
    intro t j; funext m
    rw [inv_pow, ← pow_mul, mul_comm (n + m) t.card]
  -- summability of each constant-scaled Stail summand
  have hsum : ∀ (t : Finset ℕ) (j : ℕ), Summable (fun m : ℕ =>
      (∏ k ∈ t, (-qB ^ k)) * muW n j
        * (((qB ^ (n + m))⁻¹) ^ t.card * (1 - cB * qB ^ ((n + m) + j))⁻¹)) := by
    intro t j
    rw [hStail t j]
    exact ((Stail_summable hn t.card j).mul_left _)
  rw [Eterm, tsum_congr (fun m => Iterm_triple hn (n + m)), tsum_neg]
  congr 1
  rw [Summable.tsum_finsetSum (fun t _ => summable_sum (fun j _ => hsum t j))]
  apply Finset.sum_congr rfl; intro t _
  rw [Summable.tsum_finsetSum (fun j _ => hsum t j)]
  apply Finset.sum_congr rfl; intro j _
  rw [hStail t j, tsum_mul_left]
  congr 1

/-- The finite rational "head" removed when reindexing `Stail` onto the `Tser` grid. -/
noncomputable def headS (i j n : ℕ) : ℝ :=
  ∑ m' ∈ Finset.range (n + j - 1), (qB ^ (i * (m' + 1)))⁻¹ * (1 - cB * qB ^ (m' + 1))⁻¹

/-- The explicit **rational correction** `Aₙ` of the residue identity `Eₙ = −pFirst·z + Aₙ`. -/
noncomputable def Acorr (n : ℕ) : ℝ :=
  -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
    (∏ k ∈ t, (-qB ^ k)) * muW n j
      * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n))

/-- **The residue identity** (contour-free, elementary): `Eₙ = −pFirst n · z + Aₙ`, with `Aₙ` an
explicit rational. Assembled from `Eterm_eq_Stail` (pull-out) + `Stail_collapse` (reindex) +
`Tser_collapse` (Piece II) + `pFirst_powerset` (z-coefficient). This is Borwein's Lemma 1 with the
first-form denominator `pFirst`; `pFirst_eq_pVal` (Piece III, mod q-Lagrange) connects it to `pVal`. -/
theorem Eterm_eq_pFirst {n : ℕ} (hn : 1 ≤ n) :
    Eterm n = -pFirst n * zB + Acorr n := by
  have key : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∀ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-qB ^ k)) * muW n j * Stail t.card j n
        = ((∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * cB ^ t.card)) * zB
          + (∏ k ∈ t, (-qB ^ k)) * muW n j
              * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n)) := by
    intro t _ j _
    rw [Stail_collapse t.card j n (by omega), Tser_collapse]
    rw [headS]
    ring
  -- z-coefficient (summed over t,j) equals pFirst n
  have hzcoef : ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * cB ^ t.card) = pFirst n := by
    rw [pFirst_powerset n]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hpt : ∏ k ∈ t, (-cB * qB ^ k) = cB ^ t.card * ∏ k ∈ t, (-qB ^ k) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun k _ => by ring)
    have hqp : ((qB ^ j) ^ t.card : ℝ) = qB ^ (t.card * j) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpt, hqp]; ring
  rw [Eterm_eq_Stail hn,
    Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun j hj => key t ht j hj))]
  simp_rw [Finset.sum_add_distrib]
  rw [neg_add, Acorr]
  congr 1
  rw [← hzcoef, neg_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_mul]

/-- **Residue identity with the `pVal` denominator** (`Eₙ = −pVal n · z + Aₙ`), conditional on the
q-Lagrange identity `qLag` (Piece IIIb). This is exactly the shape the `residue_open` axiom feeds;
once `qLag` is discharged (Aristotle `aristotle/QLagrange.lean`) and the numerator integrality
`β^{2n}·Wₙ·Aₙ ∈ ℤ` (Borwein Lemma 3) is proved, `residue_open` becomes a theorem and `erdos_1050`
is axiom-clean. -/
theorem Eterm_eq_pVal {n : ℕ} (hn : 1 ≤ n)
    (qLag : ∀ i, i < n →
      ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1)) :
    Eterm n = -pVal n * zB + Acorr n := by
  rw [Eterm_eq_pFirst hn, pFirst_eq_pVal hn qLag]

/- ### Toward Lemma 3 (numerator integrality): denominator-exposing forms

`Acorr`'s denominators come from `muW`, `Rrat`, `headS`. The first building block: the q-Lagrange
weight `μ_j` as `(q^j)^{n-1} / ∏_{l≠j}(q^j − q^l)` — a single explicit denominator `∏_{l≠j}(q^j−q^l)`
(a Vandermonde-type product). The eventual integrality argument shows `β^{2n}·Wₙ` clears these. -/

/-- `q^j − q^l ≠ 0` for `j ≠ l` (q-powers are distinct since `q > 1`). -/
lemma qpow_sub_ne {j l : ℕ} (hlj : l ≠ j) : (qB ^ j - qB ^ l : ℝ) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  apply hlj
  rcases Nat.lt_trichotomy l j with hlt | heq | hgt
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_right₀ one_lt_qB hlt))
  · exact heq
  · exact absurd h (ne_of_lt (pow_lt_pow_right₀ one_lt_qB hgt))

/-- **Denominator-exposing closed form** of the q-Lagrange weight:
`μ_j = (q^j)^{|erase j|} · (∏_{l≠j}(q^j − q^l))⁻¹`. -/
lemma muW_closed (n j : ℕ) :
    muW n j = (qB ^ j) ^ ((Finset.Icc 1 n).erase j).card
      * (∏ l ∈ (Finset.Icc 1 n).erase j, (qB ^ j - qB ^ l))⁻¹ := by
  rw [muW]
  have hfac : ∀ l ∈ (Finset.Icc 1 n).erase j,
      (1 - qB ^ l / qB ^ j)⁻¹ = qB ^ j * (qB ^ j - qB ^ l)⁻¹ := by
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hjne : (qB ^ j : ℝ) ≠ 0 := pow_ne_zero _ qB_ne
    have hsub : (qB ^ j - qB ^ l : ℝ) ≠ 0 := qpow_sub_ne hlj
    rw [show (1 - qB ^ l / qB ^ j : ℝ) = (qB ^ j - qB ^ l) / qB ^ j from by field_simp,
      inv_div, div_eq_mul_inv]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    ← Finset.prod_inv_distrib]

/-- **Closed form of the rational correction term** `Rrat i = ∑_{l=1}^i c^{i-l}/(q^l − 1)`, exposing
its denominators `(q^l − 1)` and the `c`-powers (which clear under `3^{…}`). -/
lemma Rrat_closed (i : ℕ) : Rrat i = ∑ l ∈ Finset.Icc 1 i, cB ^ (i - l) / (qB ^ l - 1) := by
  induction i with
  | zero => simp [Rrat]
  | succ i ih =>
    rw [show Rrat (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Rrat i from rfl, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1), Nat.sub_self, pow_zero, Finset.mul_sum,
      add_comm (1 / (qB ^ (i + 1) - 1))]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_Icc] at hl
    rw [show (i + 1) - l = (i - l) + 1 from by omega, pow_succ]
    ring

/-- **`headS` with integer denominators exposed**: each factor `(1 − c·q^{m'+1})⁻¹` clears to
`3·(3 − 8·q^{m'+1})⁻¹` (`c = 8/3`), surfacing the integer denominators `3 − 8·2^{m'+1}` (the same
factors as `CPint`) that `Wₙ`'s `∏(1 − c·q^k)` clears. -/
lemma headS_clear (i j n : ℕ) :
    headS i j n = ∑ m' ∈ Finset.range (n + j - 1),
      3 * (qB ^ (i * (m' + 1)))⁻¹ * (3 - 8 * qB ^ (m' + 1))⁻¹ := by
  rw [headS]
  apply Finset.sum_congr rfl
  intro m' _
  have h : (1 - cB * qB ^ (m' + 1))⁻¹ = 3 * (3 - 8 * qB ^ (m' + 1))⁻¹ := by
    rw [show (1 - cB * qB ^ (m' + 1) : ℝ) = (3 - 8 * qB ^ (m' + 1)) / 3 from by
      simp only [cB]; ring, inv_div, div_eq_mul_inv]
  rw [h]; ring

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/QLagrange.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# The q-Lagrange identity (Borwein Lemma 2, "Piece IIIb")

With the q-Lagrange weights `μ_j = ∏_{l≠j}(1 − q^l/q^j)⁻¹` (j,l ∈ [1,n]) and `1 < q`, for any `k`:

    ∑_{j=1}^n  μ_j · (q^j)^k   =   q^k · [n+k−1, n−1]_q .

This is the harder half of Borwein's first-form = second-form identity for the q-Padé denominator
`pₙ`; together with the Cauchy expansion (`cprod_cauchy`) it gives `pFirst n = pVal n`, discharging
the qLag hypothesis of `Eterm_eq_pVal` and the first clause of `residue_open`.

**Provenance**: auto-formalized by Harmonic's Aristotle (run `e53ca6e8`), then ported onto the repo's
`qBin` (which is the *same* q-Pascal recurrence Aristotle used) and verified axiom-clean in our kernel
(`#print axioms qLagrange = [propext, Classical.choice, Quot.sound]`).

The proof recognizes the LHS as a **divided-difference** sum `Dsum x s m = ∑_j (x j)^m/∏_{l≠j}(x j−x l)`
of the monomial `t^m` at the nodes `x j = q^j`, which satisfies the recurrence `Dsum_rec`, vanishes in
low degree (`Dsum_low`), and has the closed form `Dsum_main` by a double induction using q-Pascal.
-/

open Finset

namespace LeanGallery.NumberTheory.Erdos1050

/-- The product `∏_{l ∈ s, l ≠ j} (x j - x l)`, the denominator of the `j`-th divided-difference
weight. -/
noncomputable def Wprod (x : ℕ → ℝ) (s : Finset ℕ) (j : ℕ) : ℝ :=
  ∏ l ∈ s.erase j, (x j - x l)

/-- The divided difference of the monomial `t^m` at the nodes `x j`, `j ∈ s`. -/
noncomputable def Dsum (x : ℕ → ℝ) (s : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ j ∈ s, (x j) ^ m / Wprod x s j

/-- The node function `j ↦ q^j` is injective when `1 < q`. -/
lemma qpow_injective (q : ℝ) (hq : 1 < q) : Function.Injective (fun j : ℕ => q ^ j) := by
  exact fun a b h => le_antisymm ( le_of_not_gt fun h' => by have := pow_lt_pow_right₀ hq h'; aesop ) ( le_of_not_gt fun h' => by have := pow_lt_pow_right₀ hq h'; aesop )

/-- The node function `j ↦ q^j` is injective when `1 < |q|` (any sign of `q`). `q^a = q^b` ⟹
`|q|^a = |q|^b` ⟹ `a = b`. The entry point for the negative-base (`q ≤ −2`) q-Lagrange identity. -/
lemma qpow_injective_abs (q : ℝ) (hq : 1 < |q|) : Function.Injective (fun j : ℕ => q ^ j) := by
  intro a b h
  have habs : |q| ^ a = |q| ^ b := by rw [← abs_pow, ← abs_pow]; exact congrArg abs h
  exact qpow_injective |q| hq habs

/-- The fundamental divided-difference recurrence: removing any node `a ∈ s`. -/
lemma Dsum_rec (x : ℕ → ℝ) (hx : Function.Injective x) (s : Finset ℕ) (a : ℕ) (ha : a ∈ s)
    (m : ℕ) :
    Dsum x s (m + 1) = Dsum x (s.erase a) m + x a * Dsum x s m := by
  unfold Dsum Wprod;
  have h_split : ∑ j ∈ s, (x j ^ m * (x j - x a)) / (∏ l ∈ s.erase j, (x j - x l)) = ∑ j ∈ s.erase a, x j ^ m / (∏ l ∈ (s.erase a).erase j, (x j - x l)) := by
    have h_split : ∀ j ∈ s.erase a, (x j ^ m * (x j - x a)) / (∏ l ∈ s.erase j, (x j - x l)) = x j ^ m / (∏ l ∈ (s.erase a).erase j, (x j - x l)) := by
      intro j hj; rw [ Finset.prod_eq_prod_sdiff_singleton_mul <| Finset.mem_erase_of_ne_of_mem ( by aesop ) ha ] ; ring_nf;
      rw [ show ( s.erase a ).erase j = s.erase j \ { a } by ext; aesop ] ; ring_nf;
      grind;
    rw [ ← Finset.sum_congr rfl h_split, Finset.sum_erase_eq_sub ha ] ; aesop;
  simp_all +decide [ mul_sub, sub_div, pow_succ, mul_div_assoc, Finset.mul_sum _ _ _ ];
  grind

/-- For at least two distinct nodes, `∑_j 1/∏_{l≠j}(x j - x l) = 0`. -/
lemma Dsum_zero (x : ℕ → ℝ) (hx : Function.Injective x) (s : Finset ℕ) (hs : 2 ≤ s.card) :
    Dsum x s 0 = 0 := by
  induction' s using Finset.strongInduction with s ih;
  by_cases h_two_elements : s.card = 2;
  · rw [ Finset.card_eq_two ] at h_two_elements;
    rcases h_two_elements with ⟨ a, b, hab, rfl ⟩ ; unfold Dsum; simp +decide [ hab ] ; ring_nf;
    unfold Wprod; simp +decide [ *, Finset.prod ] ; ring_nf;
    rw [ show -x a + x b = - ( x a - x b ) by ring, inv_neg ] ; ring;
  · obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ s, ∃ b ∈ s, a ≠ b :=
      one_lt_card.mp hs
    have h_rec_a : Dsum x s 1 = Dsum x (s.erase a) 0 + x a * Dsum x s 0 := by
      exact Dsum_rec x hx s a ha 0
    have h_rec_b : Dsum x s 1 = Dsum x (s.erase b) 0 + x b * Dsum x s 0 := by
      exact Dsum_rec x hx s b hb 0;
    grind +splitIndPred

/-- The divided difference of a monomial of degree below `card - 1` vanishes. -/
lemma Dsum_low (x : ℕ → ℝ) (hx : Function.Injective x) :
    ∀ (s : Finset ℕ) (m : ℕ), m + 1 < s.card → Dsum x s m = 0 := by
  intro s m hm;
  induction' m with m ih generalizing s;
  · exact Dsum_zero x hx s hm;
  · obtain ⟨ a, ha ⟩ := Finset.card_pos.mp ( by linarith );
    rw [ Dsum_rec x hx s a ha m ];
    rw [ ih s ( by linarith ), ih ( s.erase a ) ( by rw [ Finset.card_erase_of_mem ha ] ; omega ), MulZeroClass.mul_zero, add_zero ]

/-- The closed form of the divided difference of `t^{N+k}` at the nodes `q, q^2, …, q^{N+1}`.
Only node *injectivity* is needed (the Gaussian-binomial closed form is a polynomial identity), so this
holds for any `q` with `q^j` injective — both `1 < q` and `1 < |q|` (`q ≤ −2`). -/
lemma Dsum_main (q : ℝ) (hinj : Function.Injective (fun j : ℕ => q ^ j)) :
    ∀ N k : ℕ, Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 1)) (N + k)
      = q ^ k * qBin q (N + k) N := by
  intros N k
  induction' N with N ih generalizing k;
  · unfold Dsum Wprod qBin; norm_num;
  · induction' k with k ihk;
    · have := Dsum_rec ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) ( N + 2 ) ( by norm_num ) N;
      simp_all +decide;
      rw [ show Dsum ( fun j => q ^ j ) ( Icc 1 ( N + 2 ) ) N = 0 from _ ] ; norm_num [ qBin_self ];
      · -- v4.31: `convert … using 1` no longer auto-unifies `Ico 1 (N+2)` with
        -- `Icc 1 (N+1)`, so it leaves a separate interval-reindex goal alongside the
        -- numeric one. Discharge both explicitly.
        convert ih 0 using 1
        · simp only [Nat.add_zero]
          rw [show Finset.Ico 1 (N + 2) = Finset.Icc 1 (N + 1) from by
                ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
        · norm_num [qBin_self]
      · convert Dsum_low ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) N _ using 1 ; simp +arith +decide;
    · have h_rec : Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 2)) (N + 1 + k + 1) = Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 1)) (N + k + 1) + q ^ (N + 2) * Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 2)) (N + 1 + k) := by
        convert Dsum_rec ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) ( N + 2 ) ( by norm_num ) ( N + 1 + k ) using 1;
        simp +arith +decide;
        rfl;
      have hpascal := qBin_succ_succ q (N + k + 1) N
      grind +locals [qBin_succ_succ]

/-- The original q-Lagrange LHS rewritten as a divided-difference sum. Needs only `q ≠ 0`. -/
lemma lhs_eq_Dsum (q : ℝ) (hq0 : q ≠ 0) (n : ℕ) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = Dsum (fun j => q ^ j) (Finset.Icc 1 n) (n - 1 + k) := by
  refine' Finset.sum_congr rfl fun j hj => _;
  have h_term : ∀ l ∈ Finset.erase (Finset.Icc 1 n) j, (1 - q ^ l / q ^ j)⁻¹ = q ^ j / (q ^ j - q ^ l) := by
    intro l hl; rw [ one_sub_div ( pow_ne_zero j hq0 ) ] ; norm_num;
  rw [ Finset.prod_congr rfl h_term, Finset.prod_div_distrib, Finset.prod_const, Finset.card_erase_of_mem hj, Nat.card_Icc, ( by aesop : n - 1 = n - 1 ) ] ; ring!;

/-- **The q-Lagrange identity** (`1 < q`).  (The hypothesis `hk : k ≤ n - 1` is unnecessary — the identity
holds for every `k` — but is kept for faithfulness with the `residue_open` clause.) -/
theorem qLagrange (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n - 1) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = q ^ k * qBin q (n + k - 1) (n - 1) := by
  rw [lhs_eq_Dsum q (by linarith) n k]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := Dsum_main q (qpow_injective q hq) N k
  have e1 : N + 1 - 1 + k = N + k := by omega
  have e2 : N + 1 + k - 1 = N + k := by omega
  have e3 : N + 1 - 1 = N := by omega
  rw [e1, e2, e3]
  exact h

/-- **The q-Lagrange identity for `1 < |q|`** (both signs of `q`, e.g. negative base `q ≤ −2`). Same
divided-difference proof, using `qpow_injective_abs` for node distinctness. A brick toward the
negative-base discharge of `borwein_approximants`. -/
theorem qLagrange_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n - 1) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = q ^ k * qBin q (n + k - 1) (n - 1) := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  rw [lhs_eq_Dsum q hq0 n k]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := Dsum_main q (qpow_injective_abs q hq) N k
  have e1 : N + 1 - 1 + k = N + k := by omega
  have e2 : N + 1 + k - 1 = N + k := by omega
  have e3 : N + 1 - 1 = N := by omega
  rw [e1, e2, e3]
  exact h

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/Integrality.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Denominator integrality (Borwein Lemma 2) + the q-Lagrange identity

Part of the now-complete, **axiom-clean** proof of Erdős #1050 (`#print axioms erdos_1050 =
[propext, Classical.choice, Quot.sound]`). This file machine-checks **Borwein Lemma 2** (integrality of
the q-Padé denominator `pₙ`) and pins the approximant to the actual Padé denominator `pVal`: the
coefficient `β^{2n}·Wₙ·pVal n` is the PROVEN integer `Bden n` (`Bden_cast`), built from `pInt`
(Lemma 2 via the Cauchy q-binomial theorem `qBin_cauchy`) and the 3-power / 2-power clearings of `Wₙ`.
It also derives `qLag_thm` (the q-Lagrange identity at `q = 2`) from `qLagrange` (`QLagrange.lean`).

The downstream chain `borwein_integrality → irrational_zB → erdos_1050` lives in `Lemma3.lean` (after
the elementary Lemma-3 machinery, which is what made the whole proof axiom-clean).
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Filter Topology

/-- The `3^n`-cleared `c`-product `∏_{k=1}^n (3 − 8·2^k) ∈ ℤ` (clears `∏(1 − c·q^k)`, `c = 8/3`). -/
def CPint (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc 1 n, (3 - 8 * 2 ^ k)

/-- The integer `q`-product `∏_{k=⌈n/2⌉}^n (1 − 2^k) ∈ ℤ` (equals `∏(1 − q^k)`, `q = 2`). -/
def QPint (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - 2 ^ k)

/-- The cleared **integer denominator** `β^{2n}·Wₙ·pₙ`, assembled from the factorial, the cleared
products, and the cleared Padé denominator `pInt`. -/
def Bden (n : ℕ) : ℤ :=
  3 * (Nat.factorial (n - 2)) * CPint n * QPint n * pInt n

/-- `(CPint n : ℝ) = 3^n · ∏_{k=1}^n (1 − c·q^k)`. -/
lemma CPint_cast (n : ℕ) :
    (CPint n : ℝ) = 3 ^ n * ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k) := by
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  rw [CPint]
  push_cast
  rw [show (3 : ℝ) ^ n = ∏ _k ∈ Finset.Icc 1 n, (3 : ℝ) from by rw [Finset.prod_const, hcard],
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [cB, qB]; ring

/-- `(QPint n : ℝ) = ∏_{k=⌈n/2⌉}^n (1 − q^k)`. -/
lemma QPint_cast (n : ℕ) :
    (QPint n : ℝ) = ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k) := by
  rw [QPint]
  push_cast
  apply Finset.prod_congr rfl
  intro k _
  simp only [qB]

/-- **Denominator integrality (Borwein Lemma 2, USED).** `(Bden n : ℝ) = β^{2n}·Wₙ·pVal n`, so the
Padé denominator coefficient is a machine-checked integer. -/
lemma Bden_cast {n : ℕ} (hn : 1 ≤ n) :
    (Bden n : ℝ) = (βB : ℝ) ^ (2 * n) * Wterm n * pVal n := by
  have hb : (βB : ℝ) ^ (2 * n) = 3 ^ (2 * n) := by simp [βB]
  have key : (3 : ℝ) * 3 ^ n * 3 ^ (n - 1) = 3 ^ (2 * n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show 2 * (m + 1) = (m + 1) + m + 1 from by ring,
      pow_add, pow_add, pow_one]
    ring
  rw [Bden]
  push_cast
  rw [CPint_cast, QPint_cast, pInt_cast, Wterm, hb]
  rw [← key]
  ring

/-- **The q-Lagrange identity (Piece IIIb), now a THEOREM.** `∑_j μ_j (q^j)^i = q^i·[n+i−1,n−1]_q`
for `i < n`. This was the first clause of the former `residue_open` axiom; it is now discharged by
`qLagrange` (auto-formalized by Aristotle, ported + verified axiom-clean in `QLagrange.lean`),
specialized to `q = qB = 2`. It discharges `pFirst_eq_pVal`'s hypothesis, making `Eterm_eq_pVal`
unconditional. -/
theorem qLag_thm {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1) := by
  have h := qLagrange qB one_lt_qB n hn i (by omega)
  simpa only [muW] using h

/- **Numerator integrality (Borwein Lemma 3)** is proved elementarily in `Lemma3.lean`, where the
downstream chain `borwein_integrality → irrational_zB → erdos_1050` is also assembled (it needs the
Lemma-3 machinery). With Lemma 3 machine-checked there, `erdos_1050` is axiom-clean. -/

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/Lemma3.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Borwein Lemma 3 (numerator integrality) — elementary route

Discharges `residue_open`'s second clause: `∃ a:ℕ→ℤ, ∀ n≥1, (a n:ℝ) = −β^{2n}·Wₙ·Acorr n`.

See `LEMMA3-ELEMENTARY-STRATEGY.md`. The key simplification over Borwein's residue/derivative proof:
the same q-Lagrange identity that gives `pFirst = pVal` also clears the Vandermonde `μ_j`
denominators in the numerator. This file builds the clearing infrastructure bottom-up.

## Section 1: the `QPint` divisibility (number-theoretic clearing of `Rrat`'s `q^l−1` denominators)
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-- For `1 ≤ l ≤ n` the interval `[⌈n/2⌉, n]` (here `⌈n/2⌉ = (n+1)/2`) contains a multiple of `l`.
Either `l` is small enough that the interval (length `⌊(n+1)/2⌋ ≥ l`) spans a full residue cycle, or
`l` itself lies in `[⌈n/2⌉, n]`. -/
lemma interval_has_multiple {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n) :
    ∃ k ∈ Finset.Icc ((n + 1) / 2) n, l ∣ k := by
  -- largest multiple of `l` not exceeding `n`
  have hdiv : n = l * (n / l) + n % l := (Nat.div_add_mod n l).symm
  have hmod : n % l < l := Nat.mod_lt n (by omega)
  have h1 : 1 ≤ n / l := (Nat.one_le_div_iff (by omega)).mpr hln
  have h2 : l ≤ l * (n / l) := Nat.le_mul_of_pos_right l h1
  refine ⟨l * (n / l), Finset.mem_Icc.mpr ⟨?_, by omega⟩, Dvd.intro _ rfl⟩
  -- `l * (n/l) ≥ (n+1)/2`: either `l` small (interval spans a full cycle) or `l` itself qualifies
  by_cases hsmall : l ≤ (n + 1) / 2
  · omega
  · omega

/-- `(2^l − 1) ∣ (2^k − 1)` in `ℤ` whenever `l ∣ k`. -/
lemma two_pow_sub_one_dvd {l k : ℕ} (h : l ∣ k) :
    ((2 : ℤ) ^ l - 1) ∣ ((2 : ℤ) ^ k - 1) := by
  obtain ⟨s, rfl⟩ := h
  have := sub_dvd_pow_sub_pow ((2 : ℤ) ^ l) 1 s
  simpa [pow_mul] using this

/-- **`QPint` divisibility.** For `1 ≤ l ≤ n−1`, `(2^l − 1) ∣ QPint n`. This clears `Rrat`'s
denominators `q^l − 1` (Borwein's note: `(1−q^m) | ∏_{k=⌈n/2⌉}^n (1−q^k)`). -/
lemma QPint_dvd {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n - 1) :
    ((2 : ℤ) ^ l - 1) ∣ QPint n := by
  have hln' : l ≤ n := by omega
  obtain ⟨k, hk, hdvd⟩ := interval_has_multiple hl hln'
  have hfactor : ((2 : ℤ) ^ k - 1) ∣ QPint n := by
    have hmem : (1 - 2 ^ k) ∈ (Finset.Icc ((n + 1) / 2) n).image (fun k => (1 - 2 ^ k : ℤ)) := by
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    rw [QPint]
    have : ((2 : ℤ) ^ k - 1) ∣ (1 - 2 ^ k) := ⟨-1, by ring⟩
    exact this.trans (Finset.dvd_prod_of_mem _ hk)
  exact (two_pow_sub_one_dvd hdvd).trans hfactor

/- ## Section 2: reorganizing `Acorr`'s headS-part

The headS-part of `Acorr` is `∑_t (∏_{k∈t}-q^k) ∑_j muW n j q^{|t|j} headS|t| j n`. Summing the
subset `t` first turns the inner factor into `∏_{k=1}^{n-1}(1-q^{k+j-h})`, which vanishes for `h>j`,
so the head sum truncates. See `LEMMA3-ELEMENTARY-STRATEGY.md`. -/

/-- `headS` with the inner sum reindexed from `range (n+j-1)` to `Icc 1 (n+j-1)` (set `h = m'+1`). -/
lemma headS_Icc (i j n : ℕ) :
    headS i j n = ∑ h ∈ Finset.Icc 1 (n + j - 1), (qB ^ (i * h))⁻¹ * (1 - cB * qB ^ h)⁻¹ := by
  rw [headS, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro m' _
  rw [Nat.add_comm 1 m']

/-- **Subset-product collapse** (signed, with a scalar `w`): `∑_{t⊆[1,m]} (∏_{k∈t}-q^k)·w^{|t|}
= ∏_{k=1}^m (1 - q^k·w)`. The engine of the headS reorganization (reverse of `Dterm_expand`). -/
lemma subset_prod_local (w : ℝ) (m : ℕ) :
    ∑ t ∈ (Finset.Icc 1 m).powerset, (∏ k ∈ t, (-qB ^ k)) * w ^ t.card
      = ∏ k ∈ Finset.Icc 1 m, (1 - qB ^ k * w) := by
  have hf : ∀ k, (1 : ℝ) - qB ^ k * w = 1 + (-qB ^ k) * w := by intro k; ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- `qB^{t·j}·(qB^{t·h})⁻¹ = (qB^{j−h})^t` (mixing nat powers and a zpow base). -/
lemma wpow (j h t : ℕ) : (qB ^ (t * j) : ℝ) * (qB ^ (t * h))⁻¹ = (qB ^ ((j : ℤ) - h)) ^ t := by
  rw [← zpow_natCast (qB ^ ((j : ℤ) - h)) t, ← zpow_mul, ← zpow_natCast qB (t * j),
    ← zpow_natCast qB (t * h), ← zpow_neg, ← zpow_add₀ qB_ne]
  congr 1
  push_cast; ring

/-- **Per-`j` headS reorganization.** Summing the subset `t ⊆ [1,n−1]` first collapses the headS-part
into a single product `∏_{k=1}^{n−1}(1−q^{k+j−h})` over the head index `h`:

`∑_t (∏_{k∈t}−q^k)·(q^{|t|·j}·headS|t| j n) = ∑_{h=1}^{n+j−1} u_h·∏_{k=1}^{n−1}(1−q^{k+j−h})`,
`u_h = (1−c·q^h)⁻¹`. -/
lemma headPart_inner (n j : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-qB ^ k)) * (qB ^ (t.card * j) * headS t.card j n)
      = ∑ h ∈ Finset.Icc 1 (n + j - 1),
        (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  -- substitute headS_Icc and distribute the t-term over the h-sum
  have hstep : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset,
      (∏ k ∈ t, (-qB ^ k)) * (qB ^ (t.card * j) * headS t.card j n)
        = ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - cB * qB ^ h)⁻¹ * ((∏ k ∈ t, (-qB ^ k)) * (qB ^ ((j : ℤ) - h)) ^ t.card) := by
    intro t _
    rw [headS_Icc, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← wpow j h t.card]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hprod : (∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ k * qB ^ ((j : ℤ) - h)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [← zpow_natCast qB k, ← zpow_add₀ qB_ne]
    congr 2
    ring
  rw [hprod, ← subset_prod_local (qB ^ ((j : ℤ) - h)) (n - 1), Finset.mul_sum]

/-- The full headS-part of `Acorr`, reorganized: pull `muW n j` out and apply `headPart_inner`. -/
lemma AccH_reorg (n : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * headS t.card j n)
      = ∑ j ∈ Finset.Icc 1 n, muW n j *
          ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← headPart_inner n j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **`Acorr` reorganized** into its Rrat-part (first sum) and the reorganized headS-part (second
sum). The headS-part's high-`h` heads have cancelled (via `headPart_inner`'s product collapse). -/
lemma Acorr_reorg (n : ℕ) :
    Acorr n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                  (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card))
              + ∑ j ∈ Finset.Icc 1 n, muW n j *
                  ∑ h ∈ Finset.Icc 1 (n + j - 1),
                    (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  have key : (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card))
              - (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * headS t.card j n))
            = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro t _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [Acorr, ← key, AccH_reorg]
  abel

/- ## Section 3: head truncation + q-Lagrange clearing

`head_truncate` (auto-formalized by Aristotle, run `332e491b`, verified axiom-clean) removes the
high-`h` heads `h ∈ [j+1, n+j−1]` (the product `∏(1−q^{k+j−h})` vanishes there). The surviving
`∑_{h=1}^j` then re-indexes (j,h)-swap with the j-sum extended to `[1,n]` (the added `j<h` terms also
vanish), exposing the q-Lagrange combination `N_h = ∑_j muW n j ∏(1−q^{k+j−h}) ∈ ℤ`. -/

/-- **Head truncation** (Aristotle `332e491b`): for `1 ≤ n`, the head sum over `h ∈ [1, n+j−1]`
truncates to `h ∈ [1, j]` because the product `∏_{k=1}^{n−1}(1−q^{k+j−h})` vanishes for `h > j`
(the `k = h−j ∈ [1,n−1]` factor is `1 − q^0 = 0`). -/
theorem head_truncate (q : ℝ) (u : ℕ → ℝ) (n j : ℕ) (hn : 1 ≤ n) :
    ∑ h ∈ Finset.Icc 1 (n + j - 1),
        u h * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 j,
        u h * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  rw [ ← Finset.sum_subset ( Finset.Icc_subset_Icc_right ( show j ≤ n + j - 1 from Nat.le_sub_one_of_lt ( by omega ) ) ) ];
  intros x hx hnx
  obtain ⟨k, hk⟩ : ∃ k ∈ Finset.Icc 1 (n - 1), (k : ℤ) + j - x = 0 := by
    exact ⟨ x - j, Finset.mem_Icc.mpr ⟨ Nat.sub_pos_of_lt <| lt_of_not_ge fun h => hnx <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], h ⟩, Nat.sub_le_of_le_add <| by linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel <| show 1 ≤ n from hn, Nat.sub_add_cancel <| show 1 ≤ n + j from by linarith ] ⟩, by rw [ Nat.cast_sub <| by linarith [ Finset.mem_Icc.mp hx, not_le.mp fun h => hnx <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], h ⟩ ] ] ; ring ⟩;
  rw [ Finset.prod_eq_zero hk.1 ] <;> aesop

/-- The product `∏_{k=1}^{n−1}(1−q^{k+j−h})` vanishes for `j < h ≤ n` (the `k = h−j ∈ [1,n−1]`
factor is `1 − q^0 = 0`). Used to extend partial `j`-sums to full ones. -/
lemma prod_vanish {n j h : ℕ} (hj : 1 ≤ j) (hjh : j < h) (hhn : h ≤ n) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 := by
  apply Finset.prod_eq_zero (i := h - j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have : ((h - j : ℕ) : ℤ) + j - h = 0 := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [this, zpow_zero, sub_self]

/-- **headS-part in `N_h` form.** After truncation (`head_truncate`) the (j,h)-sum swaps and the
inner `j`-sum extends to `[1,n]` (the added `j<h` terms vanish by `prod_vanish`), exposing the
q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})`:

`∑_j muW n j ∑_{h=1}^{n+j−1} u_h ∏(…) = ∑_{h=1}^n u_h · (∑_j muW n j ∏(…))`. -/
lemma headSPart_NhForm (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j *
        ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
          ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  -- Step 1: truncate each head sum to h ≤ j, and bring muW inside.
  have h1 : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
        = ∑ h ∈ Finset.Icc 1 j,
            muW n j * ((1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) := by
    intro j _
    rw [head_truncate qB (fun h => (1 - cB * qB ^ h)⁻¹) n j hn, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  -- Step 2: swap the triangular double sum ∑_{j} ∑_{h≤j} = ∑_{h} ∑_{j≥h}.
  rw [Finset.sum_comm' (s := Finset.Icc 1 n) (t := fun j => Finset.Icc 1 j)
        (t' := Finset.Icc 1 n) (s' := fun h => Finset.Icc h n)
        (by intro j h
            show (j ∈ Finset.Icc 1 n ∧ h ∈ Finset.Icc 1 j)
              ↔ (j ∈ Finset.Icc h n ∧ h ∈ Finset.Icc 1 n)
            simp only [Finset.mem_Icc]; omega)]
  -- Step 3: extend the inner j-sum to [1,n] and pull u_h out.
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega : (1 : ℕ) ≤ h))]
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j hj hjh
    rw [Finset.mem_Icc] at hj hjh
    have : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 :=
      prod_vanish (by omega) (by omega) hh.2
    rw [this]; ring

/-- **Rrat-part via q-Lagrange.** Each `t`-term's `j`-sum `∑_j muW n j (q^j)^{|t|}` is the Gaussian
binomial `q^{|t|}·[n+|t|−1,n−1]_q` (`qLag_thm`, valid as `|t| ≤ n−1 < n`), eliminating the Vandermonde
`muW` denominators. The result is `muW`-free: integer products times `Rrat |t|`. -/
lemma RratPart_qLag (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card)
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1
    omega
  have hpull : ∑ j ∈ Finset.Icc 1 n, (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card)
      = (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ t.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, Nat.mul_comm j t.card]; ring
  rw [hpull, qLag_thm hn t.card hcard]

/-- **`Acorr` in clean form** — the structural target of the elementary Lemma-3 route. The Rrat-part
is now `muW`-free (Gaussian binomials), and the headS-part is `∑_{h=1}^n u_h·N_h` with the
q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})`. Integrality of
`β^{2n}·Wₙ·Acorr n` reduces to: (i) `β^{2n}·Wₙ·(Rrat-part) ∈ ℤ` (clear `Rrat`'s `q^l−1` denominators
by `QPint_dvd` and `c`-powers by `β`); (ii) `N_h ∈ ℤ` (out to Aristotle, `Lemma3-Nh-Leaf.lean`) with
`β^{2n}·Wₙ·u_h ∈ ℤ` (clear `u_h` by `CPint`). -/
theorem Acorr_clean (n : ℕ) (hn : 1 ≤ n) :
    Acorr n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
                  (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)))
              + ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
                  ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Acorr_reorg n, RratPart_qLag n hn, headSPart_NhForm n hn]

/- ## Section 4: the integer clearing factor `β^{2n}·Wₙ` -/

/-- The cleared **integer** form of `β^{2n}·Wₙ = 3^{2n}·(n−2)!·∏(1−c·q^k)·∏(1−q^k)`. Since
`3^n·∏(1−c·q^k) = CPint` and `∏(1−q^k) = QPint`, this is `3^n·(n−2)!·CPint·QPint ∈ ℤ`. -/
def WI (n : ℕ) : ℤ := 3 ^ n * (Nat.factorial (n - 2)) * CPint n * QPint n

/-- `(WI n : ℝ) = β^{2n}·Wₙ`: the clearing factor is a machine-checked integer. -/
lemma WI_cast (n : ℕ) : (WI n : ℝ) = (βB : ℝ) ^ (2 * n) * Wterm n := by
  rw [WI, Wterm]
  push_cast
  rw [CPint_cast, QPint_cast]
  have hb : (βB : ℝ) ^ (2 * n) = 3 ^ n * 3 ^ n := by
    rw [show (βB : ℝ) = 3 from by simp [βB], ← pow_add]; congr 1; omega
  rw [hb]; ring

/-- The integer witness for `β^{2n}·Wₙ·(c^{i−l}/(q^l−1))`: clears `3^{i−l}` by `3^n` and `q^l−1` by
`QPint` (via `QPint_dvd`). -/
def RratTermInt (n i l : ℕ) : ℤ :=
  8 ^ (i - l) * 3 ^ (n - (i - l)) * (Nat.factorial (n - 2)) * CPint n * (QPint n / (2 ^ l - 1))

/-- **Per-term Rrat clearing**: `(RratTermInt n i l : ℝ) = WI n · c^{i−l}/(q^l−1)` for `1 ≤ l ≤ n−1`,
`l ≤ i ≤ n−1`. -/
lemma RratTermInt_cast {n i l : ℕ} (hn : 1 ≤ n) (hl1 : 1 ≤ l) (hli : l ≤ i) (hin : i ≤ n - 1) :
    (RratTermInt n i l : ℝ) = (WI n : ℝ) * (cB ^ (i - l) / (qB ^ l - 1)) := by
  obtain ⟨d, hd⟩ := QPint_dvd (l := l) (n := n) hl1 (by omega)
  have hne : ((2 : ℤ) ^ l - 1) ≠ 0 := by
    have : (1 : ℤ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℤ) ^ l ≠ 1 := by
      have : (2 : ℤ) ^ 1 ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl1
      omega
    omega
  have hdiv : QPint n / (2 ^ l - 1) = d := by rw [hd]; exact Int.mul_ediv_cancel_left d hne
  have hq : (qB ^ l - 1 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ qB ^ l := two_le_pow hl1
    simp only [qB] at this ⊢; linarith
  have hQ : (QPint n : ℝ) = (qB ^ l - 1) * (d : ℝ) := by
    have h1 : (QPint n : ℝ) = (((2 ^ l - 1) * d : ℤ) : ℝ) := by rw [← hd]
    rw [h1]; push_cast; simp only [qB]
  have h3 : (3 : ℝ) ^ n = 3 ^ (i - l) * 3 ^ (n - (i - l)) := by rw [← pow_add]; congr 1; omega
  rw [RratTermInt, hdiv, WI]
  push_cast
  rw [hQ, h3, show (cB : ℝ) = 8 / 3 from rfl, div_pow]
  field_simp

/-- **Rrat clearing.** `WI n · Rrat i ∈ ℤ` for `i ≤ n−1`: each `Rrat_closed` term clears. -/
lemma WI_mul_Rrat_int {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : i ≤ n - 1) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) * Rrat i := by
  refine ⟨∑ l ∈ Finset.Icc 1 i, RratTermInt n i l, ?_⟩
  rw [Rrat_closed, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_Icc] at hl
  exact RratTermInt_cast hn hl.1 hl.2 hi

/-- Per-`t` integer witness for the whole Rrat-part of `Acorr_clean`. -/
def RratCleanTermInt (n : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-(2 : ℤ) ^ k)) * (2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1))
    * (∑ l ∈ Finset.Icc 1 t.card, RratTermInt n t.card l)

/-- Each Rrat-part `t`-term, times `β^{2n}·Wₙ`, is the integer `RratCleanTermInt n t`. -/
lemma RratCleanTermInt_cast {n : ℕ} (hn : 1 ≤ n) {t : Finset ℕ}
    (ht : t ∈ (Finset.Icc 1 (n - 1)).powerset) :
    (RratCleanTermInt n t : ℝ) = (WI n : ℝ) *
      ((∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1))) := by
  have hcard : t.card ≤ n - 1 := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have e1 : ((∏ k ∈ t, (-(2 : ℤ) ^ k) : ℤ) : ℝ) = ∏ k ∈ t, (-qB ^ k) := by
    rw [Int.cast_prod]; apply Finset.prod_congr rfl; intro k _; push_cast; simp [qB]
  have e4 : ((∑ l ∈ Finset.Icc 1 t.card, RratTermInt n t.card l : ℤ) : ℝ)
      = (WI n : ℝ) * Rrat t.card := by
    rw [Rrat_closed, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl; intro l hl; rw [Finset.mem_Icc] at hl
    exact RratTermInt_cast hn hl.1 hl.2 hcard
  rw [RratCleanTermInt, Int.cast_mul, Int.cast_mul, e4, e1,
    show ((2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1) : ℤ) : ℝ)
        = qB ^ t.card * qBin qB (n + t.card - 1) (n - 1) from by
      push_cast [← qBin_two_cast]; simp [qB]]
  ring

/-- **Rrat-part integrality.** `β^{2n}·Wₙ · (Rrat-part of `Acorr_clean`) ∈ ℤ` — the entire `muW`-free
Rrat-part clears (integer products × `WI·Rrat`). The "clean half" of Lemma 3. -/
lemma WI_mul_RratClean_int (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) * ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, RratCleanTermInt n t, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact RratCleanTermInt_cast hn ht

/- ## Section 5: the headS-part `u_h` clearing (toward headS-part integrality)

The headS-part is `∑_{h=1}^n u_h·N_h`, `u_h = (1−c·q^h)⁻¹`. `β^{2n}·Wₙ·u_h ∈ ℤ` because
`CPint = ∏_{k=1}^n(3−8·2^k)` carries the factor `(3−8·2^h)` that `u_h = 3/(3−8·2^h)` exposes. The
other factor `N_h ∈ ℤ` is the q-Lagrange crux (Aristotle leaf `06c2c62c`). -/

/-- `CPint` with its `h`-th factor removed (`h ∈ [1,n]`). -/
def CPdrop (n h : ℕ) : ℤ := ∏ k ∈ (Finset.Icc 1 n).erase h, (3 - 8 * 2 ^ k)

/-- `(3 − 8·2^h)·CPdrop n h = CPint n` for `h ∈ [1,n]`. -/
lemma CPint_factor {n h : ℕ} (hh : h ∈ Finset.Icc 1 n) :
    (3 - 8 * 2 ^ h) * CPdrop n h = CPint n :=
  Finset.mul_prod_erase (Finset.Icc 1 n) (fun k => 3 - 8 * 2 ^ k) hh

/-- The integer witness for `β^{2n}·Wₙ·u_h = 3^{n+1}·(n−2)!·QPint·CPdrop`. -/
def uClearInt (n h : ℕ) : ℤ := 3 ^ (n + 1) * (Nat.factorial (n - 2)) * QPint n * CPdrop n h

/-- **`u_h` clearing**: `(uClearInt n h : ℝ) = β^{2n}·Wₙ·(1−c·q^h)⁻¹` for `1 ≤ h ≤ n`. -/
lemma uClearInt_cast {n h : ℕ} (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    (uClearInt n h : ℝ) = (WI n : ℝ) * (1 - cB * qB ^ h)⁻¹ := by
  have hmem : h ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hh1, hhn⟩
  have hfac : (3 - 8 * 2 ^ h) * CPdrop n h = CPint n := CPint_factor hmem
  have h2 : (2 : ℝ) ≤ qB ^ h := two_le_pow hh1
  have hne : (3 - 8 * qB ^ h : ℝ) ≠ 0 := by simp only [qB] at h2 ⊢; nlinarith
  have hu : (1 - cB * qB ^ h)⁻¹ = 3 / (3 - 8 * qB ^ h) := by
    rw [show (1 - cB * qB ^ h : ℝ) = (3 - 8 * qB ^ h) / 3 from by simp only [cB]; ring, inv_div]
  have hCP : (CPint n : ℝ) = (3 - 8 * qB ^ h) * (CPdrop n h : ℝ) := by
    rw [← hfac]; push_cast; simp only [qB]
  rw [uClearInt, WI]
  push_cast
  rw [hu, hCP]
  field_simp
  ring

/- ## Section 6: headS-part integrality and the full numerator clearing (conditional on `N_h ∈ ℤ`) -/

/-- **headS-part integrality**, given integer witnesses `Nz h = N_h`. `β^{2n}·Wₙ·(headS-part)
= ∑_h (β^{2n}·Wₙ·u_h)·N_h = ∑_h uClearInt·Nz h ∈ ℤ`. -/
lemma WI_mul_headS_int (n : ℕ) (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) *
      ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
        ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  refine ⟨∑ h ∈ Finset.Icc 1 n, uClearInt n h * Nz h, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Int.cast_mul, uClearInt_cast hh.1 hh.2, hNz h hh.1 hh.2]
  ring

/-- **Borwein Lemma 3 (numerator integrality), conditional on `N_h ∈ ℤ`.** Combines the Rrat-part
(`WI_mul_RratClean_int`) and headS-part (`WI_mul_headS_int`) integralities via `Acorr_clean` and
`WI_cast`: `−β^{2n}·Wₙ·Acorr n ∈ ℤ`. -/
lemma Acorr_int (n : ℕ) (hn : 1 ≤ n) (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) :
    ∃ a : ℤ, (a : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
  obtain ⟨rInt, hr⟩ := WI_mul_RratClean_int n hn
  obtain ⟨hInt, hh⟩ := WI_mul_headS_int n Nz hNz
  refine ⟨rInt - hInt, ?_⟩
  rw [← WI_cast]
  push_cast
  rw [hr, hh, Acorr_clean n hn]
  ring

/- ## Section 6b: toward `N_h ∈ ℤ` — the 2-adic cleared product (port scaffold)

The crux integrality `N_h ∈ ℤ` rests on a 2-adic clearing: `qB^{(n−1)h}·∏_{k=1}^{n−1}(1−q^{k+j−h})`
is an INTEGER-coefficient polynomial in `qB^j` (`clearedProd`), so `qB^{(n−1)h}·N_h ∈ ℤ` via q-Lagrange;
combined with `μ_j`'s odd denominator this gives `N_h ∈ ℤ`. This lemma is the foundation either way
(local proof or porting the Aristotle result). -/

/-- **Cleared product**: `(qB^h)^{n−1}·∏_{k=1}^{n−1}(1−qB^{k+j−h}) = ∏_{k=1}^{n−1}(qB^h−qB^{k+j})`,
turning the zpow product (with `q^{−h}` denominators) into an integer-valued nat-power product. -/
lemma clearedProd (n j h : ℕ) :
    (qB ^ h) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j)) := by
  have hcard : (qB ^ h) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), qB ^ h := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [mul_sub, mul_one]
  congr 1
  rw [← zpow_natCast qB h, ← zpow_add₀ qB_ne, ← zpow_natCast qB (k + j)]
  congr 1
  push_cast
  ring

/-- **2-adic clearing of `N_h`**: `qB^{(n−1)h}·N_h = ∑_j muW n j ∏_{k=1}^{n−1}(qB^h−qB^{k+j})`. The RHS
product is an INTEGER-coefficient polynomial in `qB^j` (each factor `2^h−2^{k+j} ∈ ℤ`), so by
`qLag_thm` (termwise, after expanding the product) the RHS — hence `qB^{(n−1)h}·N_h` — is an integer.
This is the 2-adic half (`N_h ∈ ℤ[1/2]`) of `N_h ∈ ℤ`. -/
lemma Nh_2adic (n h : ℕ) :
    (qB ^ h) ^ (n - 1) *
        ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, clearedProd n j h]

/-- Expand `∏_{k=1}^{n−1}(qB^h − qB^{k+j})` over subsets `t ⊆ [1,n−1]` as a polynomial in `qB^j`. -/
lemma prod_diff_expand (n j h : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * (qB ^ j) ^ t.card * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card) := by
  have hf : ∀ k, (qB ^ h - qB ^ (k + j) : ℝ) = (-qB ^ (k + j)) + qB ^ h := fun k => by ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const]
  have hexp : ∏ k ∈ t, (-qB ^ (k + j)) = (∏ k ∈ t, (-qB ^ k)) * (qB ^ j) ^ t.card := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k _; rw [pow_add]; ring
  rw [hexp]

/-- **q-Lagrange reduction of the cleared `N_h`** (the `muW`-free form): `∑_j muW n j ∏(qB^h−qB^{k+j})`
equals a sum over subsets `t` of integer-valued terms (Gaussian binomials), via `prod_diff_expand` +
`qLag_thm`. With `Nh_2adic`, this gives `qB^{(n−1)h}·N_h ∈ ℤ` (the 2-adic half of `N_h ∈ ℤ`). -/
lemma Nh_prod_qLag (n h : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
            * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
        = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
              * (muW n j * (qB ^ j) ^ t.card) := by
    intro j _
    rw [prod_diff_expand n j h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1; omega
  rw [← Finset.mul_sum, qLag_thm hn t.card hcard]

/-- Per-`t` integer witness for the cleared `N_h`. -/
def Nh2TermInt (n h : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-(2 : ℤ) ^ k)) * (2 ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
    * (2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1))

/-- Each `Nh_prod_qLag` `t`-term is the integer `Nh2TermInt n h t`. -/
lemma Nh2TermInt_cast (n h : ℕ) (t : Finset ℕ) :
    (Nh2TermInt n h t : ℝ) = (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
      * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  rw [Nh2TermInt]
  push_cast [← qBin_two_cast]
  simp only [qB]

/-- **Part (a) of `N_h ∈ ℤ`: the 2-adic half.** `(qB^h)^{n−1}·N_h ∈ ℤ`. (Combined with `μ_j`'s odd
denominator — part (b), still TODO — this gives `N_h ∈ ℤ`, discharging `Nh_integral`.) -/
lemma Nh_2adic_int (n h : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (qB ^ h) ^ (n - 1) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Nh_2adic n h, Nh_prod_qLag n h hn]
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, Nh2TermInt n h t, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Nh2TermInt_cast n h t

/-- **The combine** `ℤ[1/2] ∩ ℤ[1/odd] = ℤ`: if `2^m·N` and `D·N` are integers with `D` odd, then
`N` is an integer. (`A·D = 2^m·B`, `IsCoprime 2^m D` ⟹ `2^m ∣ A` ⟹ `N = A/2^m ∈ ℤ`.) -/
lemma int_of_clearings {N : ℝ} {A B D : ℤ} {m : ℕ} (hD : Odd D)
    (hA : (A : ℝ) = (2 : ℝ) ^ m * N) (hB : (B : ℝ) = (D : ℝ) * N) :
    ∃ z : ℤ, (z : ℝ) = N := by
  have hAD : A * D = 2 ^ m * B := by
    have hr : ((A * D : ℤ) : ℝ) = ((2 ^ m * B : ℤ) : ℝ) := by
      push_cast; rw [hA, hB]; ring
    exact_mod_cast hr
  have hmod : D % 2 = 1 := Int.odd_iff.mp hD
  have hnd : ¬ (2 : ℤ) ∣ D := by rw [Int.dvd_iff_emod_eq_zero]; omega
  have hdvd : (2 : ℤ) ^ m ∣ A :=
    (Int.prime_two).pow_dvd_of_dvd_mul_right m hnd ⟨B, hAD⟩
  obtain ⟨C, hC⟩ := hdvd
  refine ⟨C, ?_⟩
  have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
  have : (2 : ℝ) ^ m * (C : ℝ) = (2 : ℝ) ^ m * N := by
    rw [← hA, hC]; push_cast; ring
  exact mul_left_cancel₀ h2m this

/- ### Part (b): `μ_j` has odd denominator (the last piece of `N_h ∈ ℤ`)

`muW n j = ∏_{l≠j}(1−q^l/q^j)⁻¹`. Multiplying the `l`-factor by the ODD integer `2^{|j−l|}−1` gives an
integer (`−1` if `l>j`, `2^{j−l}` if `l<j`), so the odd product `Vodd n j = ∏_{l≠j}(2^{|j−l|}−1)`
clears `muW n j`. Hence `N_h ∈ ℤ[1/odd]`, which with part (a) and `int_of_clearings` gives `N_h ∈ ℤ`. -/

/-- The explicit integer value of the cleared `l`-factor: `2^{j−l}` if `l<j`, else `−1`. -/
def zfac (j l : ℕ) : ℤ := if l < j then 2 ^ (j - l) else -1

/-- Per-factor odd clearing: `(2^{|j−l|}−1)·(1−q^l/q^j)⁻¹ = zfac j l ∈ ℤ`. -/
lemma factor_clear {j l : ℕ} (hlj : l ≠ j) :
    ((zfac j l : ℤ) : ℝ) = (((2 : ℤ) ^ (max j l - min j l) - 1 : ℤ) : ℝ) * (1 - qB ^ l / qB ^ j)⁻¹ := by
  have hq2 : (qB : ℝ) = 2 := rfl
  rw [zfac]
  rcases lt_or_gt_of_ne hlj with hlt | hgt
  · -- l < j : value 2^{j−l}
    rw [if_pos hlt]
    have hmm : max j l - min j l = j - l := by omega
    have ha1 : (2 : ℝ) ^ (j - l) - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (j - l) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hdiv : (qB ^ l / qB ^ j : ℝ) = ((2 : ℝ) ^ (j - l))⁻¹ := by
      rw [hq2, show (2 : ℝ) ^ j = 2 ^ (j - l) * 2 ^ l from by rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    field_simp
  · -- l > j : value −1
    rw [if_neg (by omega)]
    have hmm : max j l - min j l = l - j := by omega
    have ha1 : (2 : ℝ) ^ (l - j) - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (l - j) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hdiv : (qB ^ l / qB ^ j : ℝ) = (2 : ℝ) ^ (l - j) := by
      rw [hq2, show (2 : ℝ) ^ l = 2 ^ (l - j) * 2 ^ j from by rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    rw [show (1 : ℝ) - 2 ^ (l - j) = -(2 ^ (l - j) - 1) from by ring, inv_neg]
    field_simp

/-- The **odd** clearing product `Vodd n j = ∏_{l≠j}(2^{|j−l|}−1)`. -/
def Vodd (n j : ℕ) : ℤ := ∏ l ∈ (Finset.Icc 1 n).erase j, ((2 : ℤ) ^ (max j l - min j l) - 1)

/-- `Vodd n j` is odd (product of `2^{|j−l|}−1`, each odd since `|j−l| ≥ 1`). -/
lemma Vodd_odd (n j : ℕ) : Odd (Vodd n j) := by
  rw [Vodd]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro l hl
  have hne : max j l - min j l ≠ 0 := by
    have : l ≠ j := (Finset.mem_erase.mp hl).1; omega
  have heven : Even ((2 : ℤ) ^ (max j l - min j l)) := by
    rw [Int.even_pow]; exact ⟨by decide, hne⟩
  exact heven.sub_odd odd_one

/-- **Part (b): the odd clearing.** `Vodd n j · muW n j ∈ ℤ` — the odd product clears `μ_j`'s
denominator (per-factor `factor_clear`). -/
lemma Vodd_muW_int (n j : ℕ) : ∃ z : ℤ, (z : ℝ) = (Vodd n j : ℝ) * muW n j := by
  refine ⟨∏ l ∈ (Finset.Icc 1 n).erase j, zfac j l, ?_⟩
  rw [Int.cast_prod, Vodd, Int.cast_prod, muW, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  exact factor_clear (Finset.mem_erase.mp hl).1

/-- The odd common denominator `Dfull n = ∏_{j∈[1,n]} Vodd n j`, clearing every `muW n j`. -/
def Dfull (n : ℕ) : ℤ := ∏ j ∈ Finset.Icc 1 n, Vodd n j

/-- `Dfull n` is odd. -/
lemma Dfull_odd (n : ℕ) : Odd (Dfull n) := by
  rw [Dfull]
  exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun j _ => Vodd_odd n j)

/-- `Dfull n · muW n j ∈ ℤ` for `j ∈ [1,n]`. -/
lemma Dfull_muW_int {n j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    ∃ m : ℤ, (m : ℝ) = (Dfull n : ℝ) * muW n j := by
  obtain ⟨z, hz⟩ := Vodd_muW_int n j
  refine ⟨(∏ j' ∈ (Finset.Icc 1 n).erase j, Vodd n j') * z, ?_⟩
  have hD : (Dfull n : ℝ)
      = (Vodd n j : ℝ) * ((∏ j' ∈ (Finset.Icc 1 n).erase j, Vodd n j' : ℤ) : ℝ) := by
    rw [Dfull, ← Finset.mul_prod_erase (Finset.Icc 1 n) (Vodd n) hj]; push_cast; ring
  rw [hD]; push_cast; rw [hz]; ring

/-- `P_j = ∏_{k=1}^{n−1}(1−q^{k+j−h})` is an integer when `j ≥ h` (all exponents `≥ 1`). -/
lemma Pj_int {n j h : ℕ} (hjh : h ≤ j) :
    ∃ p : ℤ, (p : ℝ) = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  refine ⟨∏ k ∈ Finset.Icc 1 (n - 1), (1 - 2 ^ (k + j - h)), ?_⟩
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [show ((k : ℤ) + j - h) = ((k + j - h : ℕ) : ℤ) from by omega, zpow_natCast]
  push_cast
  simp [qB]

/-- **Part (b) at the `N_h` level**: `Dfull n · N_h ∈ ℤ`, with `Dfull n` odd. So `N_h ∈ ℤ[1/odd]`. -/
lemma Nh_odd_int (n h : ℕ) (_hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (Dfull n : ℝ) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.Icc 1 n, ∃ b : ℤ, (b : ℝ) = (Dfull n : ℝ) *
      (muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) := by
    intro j hj
    rcases Nat.lt_or_ge j h with hlt | hge
    · refine ⟨0, ?_⟩
      rw [Finset.mem_Icc] at hj
      have hv : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 :=
        prod_vanish hj.1 hlt hhn
      rw [hv]; push_cast; ring
    · obtain ⟨m, hm⟩ := Dfull_muW_int hj
      obtain ⟨p, hp⟩ := Pj_int (n := n) hge
      exact ⟨m * p, by push_cast; rw [hm, hp]; ring⟩
  choose b hb using hterm
  refine ⟨∑ j ∈ (Finset.Icc 1 n).attach, b j.1 j.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.Icc 1 n) _]
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  exact hb j hj

/-- **`N_h ∈ ℤ`** (per `(n,h)`): combine part (a) (`Nh_2adic_int`, 2-adic) and part (b)
(`Nh_odd_int`, odd) via `int_of_clearings`. -/
lemma Nh_int (n h : ℕ) (hn : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) =
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  obtain ⟨A, hA⟩ := Nh_2adic_int n h hn
  obtain ⟨B, hB⟩ := Nh_odd_int n h hh1 hhn
  have hA' : (A : ℝ) = (2 : ℝ) ^ (h * (n - 1)) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
    rw [hA, show (qB ^ h) ^ (n - 1) = (2 : ℝ) ^ (h * (n - 1)) from by
      rw [show qB = (2 : ℝ) from rfl, ← pow_mul]]
  exact int_of_clearings (Dfull_odd n) hA' hB

/- ## Section 7: `N_h ∈ ℤ` DISCHARGED — and the now axiom-clean headline

The integrality of the q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})` — the
last open input — is now **machine-checked** (`Nh_int`), via 2-adic (`Nh_2adic_int`) ∧ odd-denominator
(`Nh_odd_int`) ⟹ `int_of_clearings`. So `Nh_integral` is a THEOREM and `erdos_1050_S` is axiom-clean. -/

/-- **`N_h ∈ ℤ`, now a THEOREM** (was the last axiom). For each `n ≥ 1` there are integer witnesses
`Nz h = N_h` (`1 ≤ h ≤ n`), assembled from the per-`(n,h)` integrality `Nh_int`. -/
theorem Nh_integral : ∀ n, 1 ≤ n → ∃ Nz : ℕ → ℤ, ∀ h, 1 ≤ h → h ≤ n →
    (Nz h : ℝ) = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  intro n hn
  choose Nz hNz using fun h (hh1 : 1 ≤ h) (hhn : h ≤ n) => Nh_int n h hn hh1 hhn
  refine ⟨fun h => if H : 1 ≤ h ∧ h ≤ n then Nz h H.1 H.2 else 0, fun h hh1 hhn => ?_⟩
  show ((dite (1 ≤ h ∧ h ≤ n) (fun H => Nz h H.1 H.2) (fun _ => 0) : ℤ) : ℝ) = _
  rw [dif_pos (⟨hh1, hhn⟩ : 1 ≤ h ∧ h ≤ n)]
  exact hNz h hh1 hhn

/-- **Borwein Lemma 3 (numerator integrality), now a THEOREM** modulo `Nh_integral`: there is an
integer sequence `aₙ = −β^{2n}·Wₙ·Acorr n`. -/
theorem numerator_integrality : ∃ a : ℕ → ℤ, ∀ n, 1 ≤ n →
    (a n : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
  have key : ∀ n, 1 ≤ n → ∃ a : ℤ, (a : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
    intro n hn
    obtain ⟨Nz, hNz⟩ := Nh_integral n hn
    exact Acorr_int n hn Nz hNz
  choose a ha using key
  exact ⟨fun n => if h : 1 ≤ n then a n h else 0, fun n hn => by simp only [dif_pos hn]; exact ha n hn⟩

/-- **O1 — Borwein Lemmas 1+2+3, all discharged modulo `Nh_integral`.** -/
theorem borwein_integrality : ∃ a b : ℕ → ℤ, ∀ n, 1 ≤ n →
    (b n : ℝ) * zB - a n = (βB : ℝ) ^ (2 * n) * Wterm n * Eterm n := by
  obtain ⟨a, ha⟩ := numerator_integrality
  refine ⟨a, fun n => -Bden n, fun n hn => ?_⟩
  rw [Eterm_eq_pVal hn (qLag_thm hn)]
  have hB := Bden_cast hn
  push_cast
  rw [ha n hn, hB]
  ring

/-- The reduced q-harmonic value `z = ∑_{j≥1} 1/(1 − (8/3)·2^j)` is irrational. -/
theorem irrational_zB : Irrational zB := by
  obtain ⟨a, b, hab⟩ := borwein_integrality
  apply irrational_of_intApprox zB (fun n => a (n + 1)) (fun n => b (n + 1))
  · intro n
    rw [hab (n + 1) (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ (Wterm_ne_zero (by omega))) (Eterm_ne_zero (by omega))
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (by decide))
  · have hshift : Filter.Tendsto
        (fun n => (βB : ℝ) ^ (2 * (n + 1)) * Wterm (n + 1) * Eterm (n + 1)) Filter.atTop (nhds 0) :=
      cleared_error_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
    exact hshift.congr (fun n => (hab (n + 1) (by omega)).symm)

/-- **Erdős #1050**, positive-denominator tail form: the engine's series `S = ∑_{n ≥ 0} 1/(2^(n+2) − 3)`
is irrational. The literal, as-posed headline `erdos_1050 : Irrational (∑' n, 1/(2^(n+1) − 3))` is
derived from this in `Statement.lean` (they differ by the single rational term `1/(2¹ − 3) = −1`). -/
theorem erdos_1050_S : Irrational S := irrational_S_iff_zB.mpr irrational_zB

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/Statement.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Erdős Problem #1050 — is `∑_{n ≥ 1} 1/(2ⁿ − 3)` irrational?

## The statement

> The real number `∑_{n ≥ 1} 1/(2ⁿ − 3)` is irrational.

exactly as posed on erdosproblems.com (`Is ∑_{n=1}^∞ 1/(2ⁿ − 3) irrational?`, answer: yes).

Formalised as `erdos_1050 : Irrational (∑' n : ℕ, 1/(2^(n+1) − 3))`. Lean's `∑' n : ℕ` ranges over
`n ≥ 0`, so the source's `n ≥ 1` sum is encoded by the standard reindex `n ↦ n + 1` (the tsum's
`n = 0` summand is the source's first term, `1/(2¹ − 3)`). That `(n+1)` shift is the *only* thing to
reconcile against the source, and it is transparent.

**This file is the audit surface.** To check that this repository proves the *right thing*, read only
this file: the theorem `erdos_1050` is the entire trusted statement. Everything else
(`Basic.lean`, `Criterion.lean`, `Approximants.lean`, `Lemma3.lean`, …) is the proof engine.

## Provenance

* **Problem source.** P. Erdős & R. Graham, relayed at <https://www.erdosproblems.com/1050>
  ("Is `∑_{n=1}^∞ 1/(2ⁿ − 3)` irrational?", answer yes).
* **Resolving theorem.** P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory
  **37** (1991) 253–259 (and the cleaner *On the irrationality of certain series*, Math. Proc. Camb.
  Phil. Soc. **112** (1992) 141–146), specialized to `q = 2, r = −3`.

## Faithfulness notes

* **Indexing.** The series runs over `n ≥ 1` (the source's `∑_{n=1}^∞`). In Lean it is the tsum
  `∑' n : ℕ, 1/(2^(n+1) − 3)`, whose `n = 0` summand `1/(2¹ − 3) = −1` is the source's first term.
* **Well-definedness.** `2ⁿ − 3` is never `0` (`2ⁿ = 3` has no solution), so every term `1/(2ⁿ − 3)`
  is a genuine real.
* **Reduction (proved, not asserted).** The proof engine works with the positive-denominator tail
  `S = ∑_{n ≥ 0} 1/(2^(n+2) − 3)` (see `Basic.lean`); the headline reduces the literal series to it by
  `(∑_{n ≥ 1} 1/(2ⁿ − 3)) = -1 + S` — the single low term `1/(2¹−3) = -1` is rational, and
  irrationality is invariant under adding a rational, so `erdos_1050 ↔ erdos_1050_irrational`. This
  equivalence is `Sliteral_eq`, proved below.
* **Axiom footprint.** `#print axioms erdos_1050` should end at
  `[propext, Classical.choice, Quot.sound]` (kernel-pure; no `native_decide`, no custom axioms).
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-- The literal Erdős–Graham series `∑_{n ≥ 1} 1/(2ⁿ − 3)`, exactly as posed on erdosproblems.com,
encoded over `ℕ` by the reindex `n ↦ n + 1` (so the tsum's `n = 0` summand is the source's first
term, `1/(2¹ − 3)`). -/
noncomputable def Sliteral : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)

/-- The literal series is the positive-denominator tail `S` shifted by the one rational low term:
`∑_{n ≥ 1} 1/(2ⁿ − 3) = -1 + S`, since its first term is `1/(2¹−3) = -1`. -/
theorem Sliteral_eq : Sliteral = -1 + S := by
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) 1)
    exact h.mp (by simpa using S_summable)
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) 1 hsummable
  have hfin : (∑ i ∈ Finset.range 1, (1 : ℝ) / ((2 : ℝ) ^ (i + 1) - 3)) = -1 := by
    simp only [Finset.sum_range_one]; norm_num
  rw [hfin] at hsplit
  simp only [Sliteral, S]
  rw [← hsplit]

/-- **Erdős Problem #1050.** The series `∑_{n ≥ 1} 1/(2ⁿ − 3)` is irrational, exactly as posed on
erdosproblems.com and encoded over `ℕ` by the reindex `n ↦ n + 1`. This is the trusted headline; its
statement is character-for-character the one published to `formal-conjectures`. -/
theorem erdos_1050 : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
  show Irrational Sliteral
  rw [Sliteral_eq, show (-1 : ℝ) + S = S + ((-1 : ℚ) : ℝ) by push_cast; ring,
    irrational_add_ratCast_iff]
  exact erdos_1050_S

/-- **Erdős Problem #1050** (positive-denominator tail form, used by the proof engine). -/
theorem erdos_1050_irrational : Irrational S := erdos_1050_S

/- ### Non-vacuity anchors

Executable evidence that the series computes as intended, so the irrationality claim is not an
artifact of a mis-stated series. (The claim is already self-certifying against the worst failure
mode: mathlib sets a non-summable `tsum` to `0`, and `Irrational 0` is false — so
`erdos_1050` is provable only because the series genuinely converges to a non-rational real,
never vacuously.) -/

/-- Well-definedness: no term is a junk `1/0`, since the denominator `2ⁿ − 3` is never zero. -/
example (n : ℕ) : (2 : ℝ) ^ n - 3 ≠ 0 := by
  rcases lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num
  · have h4 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    intro hc; nlinarith

/-- The first terms of the series (`n ≥ 1`) compute to the expected values; the series first goes
positive at `n = 2`. (`n = 0` is *not* in the sum.) -/
example : (1 : ℝ) / (2 ^ 1 - 3) = -1 := by norm_num
example : (1 : ℝ) / (2 ^ 2 - 3) = 1 := by norm_num
example : (1 : ℝ) / (2 ^ 3 - 3) = 1 / 5 := by norm_num

/-- The rational shift connecting the literal series to the engine's tail `S`: the single low term
`n = 1` is exactly `−1` (this is the content of `Sliteral_eq`). -/
example : (∑ i ∈ Finset.range 1, (1 : ℝ) / (2 ^ (i + 1) - 3)) = -1 := by
  simp only [Finset.sum_range_one]; norm_num

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/General.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Borwein's general Theorem 1 — `∑ 1/(qⁿ + c)` is irrational (GENERALIZATION, in progress)

The headline result of this repository, `erdos_1050_irrational : Irrational S` (`Statement.lean`),
is the `q = 2, c = −3` instance of a far more general theorem of Borwein:

> **Theorem 1** (P. B. Borwein, *On the irrationality of certain series*, Math. Proc. Camb. Phil.
> Soc. **112** (1992) 141–146). Let `q` be an integer with `|q| > 1` and `c` a non-zero rational
> with `c ≠ −qⁿ` for all `n`. Then `∑_{n≥1} 1/(qⁿ + c)` is irrational.

This file states that theorem faithfully in Lean (`borwein_thm1`) and **reduces it, provably and in
full generality, to a single q-harmonic irrationality core** — exactly the form Borwein himself reduces
to (his eq. (2) and the remark immediately after Lemma 1: "the irrationality of `∑ 1/(q^n+c)` is
equivalent to the irrationality of `∑ 1/(1 − c·qʰ)`"). The reduction here is the *elementary* affine
one: writing `C = −1/c`,
  `1/(qⁿ + c) = (1/c)·(1 − C·qⁿ)⁻¹`,
so `c·(∑ 1/(qⁿ+c)) = ∑ (1 − C·qⁿ)⁻¹`, and irrationality is invariant under the nonzero-rational
scaling by `c` (`irrational_ratCast_mul_iff`). Both steps are **unconditional** (`tsum_mul_left`,
`tsum_congr`) — no summability hypothesis is needed for the algebraic identity — so the reduction
holds verbatim for every integer `q` with `|q| > 1`, negative `q` included.

## Status of the core
The remaining content — that the reduced value `∑ (1 − C·qⁿ)⁻¹` is irrational — is Borwein's
Padé/contour engine (his Lemmas 1–5: residue identity, denominator integrality, numerator
integrality, super-exponential error bound, non-vanishing). It is stated here as the disclosed,
cited **`axiom qharmonic_irrational`**.

That axiom is **already discharged in this repo for `q = 2`**: `LeanGallery.NumberTheory.Erdos1050.irrational_zB` proves exactly
`Irrational (∑ (1 − (8/3)·2ʲ)⁻¹)`, axiom-clean, via the elementary route (`Residue.lean`,
`QLagrange.lean`, `Lemma3.lean`). Discharging `qharmonic_irrational` in general is the live target:
parametrise that engine in `(q, c)`. The `q = 2` discharge shows the wall is breachable; the general
case needs the residue/integrality lemmas re-derived parametrically (the numerator integrality `N_h`,
proved 2-adically for `q = 2`, is the genuine nub).

**This file does not touch `erdos_1050_irrational`, which remains axiom-clean** (`#print axioms`
shows only `propext, Classical.choice, Quot.sound`). `borwein_thm1` is a strictly more general
statement, proved modulo the one cited core axiom.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/-- **The general q-harmonic value converges.** For real `q` with `|q| ≥ 2` and `C ≠ 0`, the series
`∑ₙ (1 − C·q^{n+1})⁻¹` is summable. (So the reduced value in `borwein_approximants` /
`qharmonic_irrational` is the genuine convergent sum, not the junk default of a divergent `tsum`.)

Proof: eventually `|1 − C·q^{n+1}| ≥ |C|·|q|^{n+1} − 1 ≥ |C|·|q|^{n+1}/2`, so the terms are bounded by
the convergent geometric majorant `(2/|C|)·(|q|⁻¹)ⁿ`. -/
theorem qharmonic_summable (q C : ℝ) (hq : 2 ≤ |q|) (hC : C ≠ 0) :
    Summable (fun n : ℕ => (1 - C * q ^ (n + 1))⁻¹) := by
  have hq1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hCpos : (0 : ℝ) < |C| := abs_pos.mpr hC
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n => (2 / |C|) * (|q|⁻¹) ^ n)
    ((summable_geometric_of_lt_one (by positivity) hinvlt).mul_left (2 / |C|)) ?_
  have htend : Filter.Tendsto (fun n : ℕ => |C| * |q| ^ (n + 1)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hCpos
      ((tendsto_pow_atTop_atTop_of_one_lt hq1).comp (Filter.tendsto_add_atTop_nat 1))
  filter_upwards [htend.eventually_ge_atTop 2] with n hn
  rw [Real.norm_eq_abs, abs_inv]
  have hlow : |C| * |q| ^ (n + 1) / 2 ≤ |1 - C * q ^ (n + 1)| := by
    have htri := abs_sub_abs_le_abs_sub (C * q ^ (n + 1)) 1
    rw [abs_one, abs_mul, abs_pow, abs_sub_comm] at htri
    linarith [htri, hn]
  have h2pos : (0 : ℝ) < |C| * |q| ^ (n + 1) / 2 := by positivity
  calc |1 - C * q ^ (n + 1)|⁻¹
      ≤ (|C| * |q| ^ (n + 1) / 2)⁻¹ := inv_anti₀ h2pos hlow
    _ = (2 / |C|) * (|q|⁻¹) ^ (n + 1) := by
        rw [inv_pow]
        field_simp
    _ ≤ (2 / |C|) * (|q|⁻¹) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (|q|⁻¹) ^ (n + 1) = (|q|⁻¹) ^ n * |q|⁻¹ := pow_succ _ _
          _ ≤ (|q|⁻¹) ^ n * 1 :=
              mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (le_of_lt hq1))
                (pow_nonneg (by positivity) n)
          _ = (|q|⁻¹) ^ n := mul_one _

/- ### Down-payment on `borwein_approximants`: denominator integrality (Borwein Lemma 2), general

`pValG q C n` is Borwein's q-Padé denominator `pₙ(C,q)` (second/Gaussian-binomial form), real-valued;
`pIntG q α β n` is its `β^{n-1}`-cleared integer version for integer `q` and `C = α/β`. The lemma
`pIntG_cast` says they agree after clearing — so `β^{n-1}·pₙ(α/β,q) ∈ ℤ` for ALL integer `q` and
rational `C = α/β`. This generalizes `pInt_cast` (the `q=2, C=8/3` case in `Pade.lean`) and is the
Lemma-2 sub-obligation of the general engine (`PENDING_WORK.md`, path 2). Self-contained: rests only on
the general Gaussian-binomial bridge `qBin_map` (`QBinom.lean`). -/

/-- General real-valued q-Padé denominator `pₙ(C,q)` (Borwein Lemma 2, Gaussian-binomial form). -/
noncomputable def pValG (q C : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-C) ^ k * q ^ (k * (k + 3) / 2)
    * qBin q (n - 1) k * qBin q (n + k - 1) (n - 1)

/-- The `β^{n-1}`-cleared **integer** q-Padé denominator for integer `q` and `C = α/β`. -/
def pIntG (q α β : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-α) ^ k * β ^ (n - 1 - k) * q ^ (k * (k + 3) / 2)
    * qBin q (n - 1) k * qBin q (n + k - 1) (n - 1)

/-- **Borwein Lemma 2, general form.** `(pIntG q α β n : ℝ) = β^{n-1} · pₙ(α/β, q)`. So for every
integer `q` and rational `C = α/β`, the `β^{n-1}`-cleared q-Padé denominator is an integer.
Generalizes `pInt_cast` (`q=2, C=8/3`); a down-payment on discharging `borwein_approximants`. -/
lemma pIntG_cast (q α β : ℤ) (hβ : β ≠ 0) (n : ℕ) :
    (pIntG q α β n : ℝ) = (β : ℝ) ^ (n - 1) * pValG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  have hβr : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  rw [pIntG, pValG, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hclear : (β : ℝ) ^ (n - 1) * (-((α : ℝ) / (β : ℝ))) ^ k
      = (-(α : ℝ)) ^ k * (β : ℝ) ^ (n - 1 - k) := by
    have hbk : (β : ℝ) ^ (n - 1) = (β : ℝ) ^ (n - 1 - k) * (β : ℝ) ^ k := by
      rw [← pow_add]; congr 1; omega
    have hkey : (β : ℝ) ^ k * (-((α : ℝ) / (β : ℝ))) ^ k = (-(α : ℝ)) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hbk, mul_assoc, hkey]; ring
  have hb1 : qBin ((q : ℤ) : ℝ) (n - 1) k = ((qBin q (n - 1) k : ℤ) : ℝ) :=
    qBin_map (Int.castRingHom ℝ) q (n - 1) k
  have hb2 : qBin ((q : ℤ) : ℝ) (n + k - 1) (n - 1) = ((qBin q (n + k - 1) (n - 1) : ℤ) : ℝ) :=
    qBin_map (Int.castRingHom ℝ) q (n + k - 1) (n - 1)
  rw [hb1, hb2, ← hclear]
  ring

/-- General `β^n`-cleared `c`-product `∏_{k=1}^n (β − α·qᵏ) ∈ ℤ` (clears `∏(1 − C·qᵏ)`, `C = α/β`). -/
def CPintG (q α β : ℤ) (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc 1 n, (β - α * q ^ k)

/-- General integer `q`-product `∏_{k=⌈n/2⌉}^n (1 − qᵏ) ∈ ℤ` (equals `∏(1 − qᵏ)` for integer `q`). -/
def QPintG (q : ℤ) (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)

/-- `(CPintG q α β n : ℝ) = βⁿ · ∏_{k=1}^n (1 − (α/β)·qᵏ)` (generalizes `CPint_cast`, `q=2,C=8/3`). -/
lemma CPintG_cast (q α β : ℤ) (hβ : β ≠ 0) (n : ℕ) :
    (CPintG q α β n : ℝ)
      = (β : ℝ) ^ n * ∏ k ∈ Finset.Icc 1 n, (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ k) := by
  have hβr : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  rw [CPintG]
  push_cast
  rw [show (β : ℝ) ^ n = ∏ _k ∈ Finset.Icc 1 n, (β : ℝ) from by rw [Finset.prod_const, hcard],
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  field_simp

/-- `(QPintG q n : ℝ) = ∏_{k=⌈n/2⌉}^n (1 − qᵏ)` (generalizes `QPint_cast`, `q=2`). -/
lemma QPintG_cast (q : ℤ) (n : ℕ) :
    (QPintG q n : ℝ) = ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - (q : ℝ) ^ k) := by
  rw [QPintG]
  push_cast
  rfl

/-- General clearing factor `Wₙ(C,q) = (n−2)!·∏_{k=1}^n(1−C·qᵏ)·∏_{k=⌈n/2⌉}^n(1−qᵏ)`
(generalizes `Wterm`, the `q=2,C=8/3` case). -/
noncomputable def WtermG (q C : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ)
    * (∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k))
    * (∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k))

/-- The general cleared **integer denominator** `β^{2n}·Wₙ·pₙ`, for integer `q` and `C = α/β`. -/
def BdenG (q α β : ℤ) (n : ℕ) : ℤ :=
  β * (Nat.factorial (n - 2)) * CPintG q α β n * QPintG q n * pIntG q α β n

/-- **Borwein Lemma 2 (denominator integrality), general form — MILESTONE.** For every integer `q`
and rational `C = α/β` (β ≠ 0, n ≥ 1), `(BdenG q α β n : ℝ) = β^{2n}·Wₙ(α/β,q)·pₙ(α/β,q)`, so the
q-Padé denominator coefficient `β^{2n}·Wₙ·pₙ` is an integer. Generalizes `Bden_cast` (the `q=2,C=8/3`
case) by assembling `CPintG_cast`, `QPintG_cast`, `pIntG_cast`. This fully discharges the Lemma-2
sub-obligation of the general `borwein_approximants` (`PENDING_WORK.md`, path 2). -/
lemma BdenG_cast (q α β : ℤ) (hβ : β ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (BdenG q α β n : ℝ)
      = (β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
          * pValG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  have hb : (β : ℝ) ^ (2 * n) = (β : ℝ) ^ n * (β : ℝ) ^ (n - 1) * (β : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show 2 * (m + 1) = (m + 1) + m + 1 from by ring,
      pow_add, pow_add, pow_one]
  rw [BdenG]
  push_cast
  rw [CPintG_cast q α β hβ, QPintG_cast q, pIntG_cast q α β hβ, WtermG, hb]
  ring

/-- **The series in `borwein_thm1` converges.** For integer `q` with `|q| ≥ 2` and any rational `c`,
`∑ₙ 1/(qⁿ⁺¹ + c)` is summable — so the headline general statement is about a genuine convergent sum.
(Same geometric-majorant argument as `qharmonic_summable`.) -/
theorem Sgen_summable (q : ℤ) (hq : 2 ≤ |q|) (c : ℚ) :
    Summable (fun n : ℕ => (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have hq1 : (1 : ℝ) < |(q : ℝ)| := by linarith
  have hqpos : (0 : ℝ) < |(q : ℝ)| := by linarith
  have hinvlt : |(q : ℝ)|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n => (2 : ℝ) * (|(q : ℝ)|⁻¹) ^ n)
    ((summable_geometric_of_lt_one (by positivity) hinvlt).mul_left 2) ?_
  have htend : Filter.Tendsto (fun n : ℕ => |(q : ℝ)| ^ (n + 1)) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hq1).comp (Filter.tendsto_add_atTop_nat 1)
  filter_upwards [htend.eventually_ge_atTop (2 * |(c : ℝ)| + 2)] with n hn
  rw [Real.norm_eq_abs, abs_div, abs_one]
  have hlow : |(q : ℝ)| ^ (n + 1) / 2 ≤ |(q : ℝ) ^ (n + 1) + (c : ℝ)| := by
    have htri := abs_sub_abs_le_abs_sub ((q : ℝ) ^ (n + 1)) (-(c : ℝ))
    rw [abs_pow, abs_neg, sub_neg_eq_add] at htri
    linarith [htri, hn]
  have h2pos : (0 : ℝ) < |(q : ℝ)| ^ (n + 1) / 2 := by positivity
  calc (1 : ℝ) / |(q : ℝ) ^ (n + 1) + (c : ℝ)|
      ≤ 1 / (|(q : ℝ)| ^ (n + 1) / 2) := one_div_le_one_div_of_le h2pos hlow
    _ = 2 * (|(q : ℝ)|⁻¹) ^ (n + 1) := by rw [inv_pow]; field_simp
    _ ≤ 2 * (|(q : ℝ)|⁻¹) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc (|(q : ℝ)|⁻¹) ^ (n + 1) = (|(q : ℝ)|⁻¹) ^ n * |(q : ℝ)|⁻¹ := pow_succ _ _
          _ ≤ (|(q : ℝ)|⁻¹) ^ n * 1 :=
              mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (le_of_lt hq1))
                (pow_nonneg (by positivity) n)
          _ = (|(q : ℝ)|⁻¹) ^ n := mul_one _

/- ### Down-payment on the GENERAL numerator integrality (Borwein Lemma 3, path 3b)

Borwein's general numerator-integrality proof (paper p.143) needs the divisibility
`(1 − qᵐ) | ∏_{k=⌈n/2⌉}^n (1 − qᵏ)` for `1 ≤ m ≤ n` (it lets the `q`-denominators of the residue
derivative cancel). Proved here in full for integer `q`. -/

/-- The interval `⌈n/2⌉ .. n` contains a multiple of `m` (for `1 ≤ m ≤ n`): either the largest
multiple `m·⌊n/m⌋` (when it reaches `⌈n/2⌉`) or `m` itself (which then lies in the interval). -/
theorem mult_in_upper_half (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∃ k ∈ Finset.Icc ((n + 1) / 2) n, m ∣ k := by
  have hmod : n % m < m := Nat.mod_lt n (by omega)
  have hdm : m * (n / m) + n % m = n := Nat.div_add_mod n m
  set q0 := m * (n / m) with hq0
  by_cases hc : (n + 1) / 2 ≤ q0
  · exact ⟨q0, Finset.mem_Icc.mpr ⟨hc, by omega⟩, hq0 ▸ dvd_mul_right m (n / m)⟩
  · exact ⟨m, Finset.mem_Icc.mpr ⟨by omega, hmn⟩, dvd_refl m⟩

/-- **Borwein's divisibility fact** (Lemma 3 proof, general `q`): for integer `q` and `1 ≤ m ≤ n`,
`(1 − qᵐ)` divides `∏_{k=⌈n/2⌉}^n (1 − qᵏ)`. -/
theorem borwein_div (q : ℤ) (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (1 - q ^ m) ∣ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k) := by
  obtain ⟨k, hk, j, hj⟩ := mult_in_upper_half n m hm hmn
  have hdvd : (1 - q ^ m) ∣ (1 - q ^ k) := by
    have hqk : q ^ k = (q ^ m) ^ j := by rw [hj, pow_mul]
    rw [hqk]
    simpa using sub_dvd_pow_sub_pow (1 : ℤ) (q ^ m) j
  exact hdvd.trans (Finset.dvd_prod_of_mem _ hk)

/-- **Path-3a building block:** `qᵃ⁺¹ − 1` is coprime to `q` (`qᵃ⁺¹ − 1 ≡ −1 mod q`). This is why the
q-Lagrange coefficients `μⱼ` — whose denominators are products of factors `q^d − 1` — have
denominators coprime to `q`; combined with the `q`-power clearing it gives `N_h ∈ ℤ` for general `q`
(the general analog of the `q=2` 2-adic ∧ odd-denominator argument, `PENDING_WORK.md` path 3a). -/
theorem coprime_qpow_sub_one (q : ℤ) (a : ℕ) : IsCoprime (q ^ (a + 1) - 1) q :=
  ⟨-1, q ^ a, by rw [pow_succ]; ring⟩

/- The former `axiom borwein_approximants` (and the theorems `qharmonic_irrational`, `borwein_thm1`,
`irrational_sum_two_pow_sub_one` it underwrote) have been **fully discharged**: every one of Borwein's
five lemmas — including Lemma 5 non-vanishing for negative base `q ≤ −2` via the sign dichotomy — is
now machine-checked. The axiom-free headlines live in `GeneralAssembly.lean`:
`qharmonic_irrational_abs`, `borwein_thm1_abs`, `irrational_sum_two_pow_sub_one_abs`, all for
`2 ≤ |q|` (both signs), with `#print axioms = [propext, Classical.choice, Quot.sound]`. -/

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/GeneralNumerator.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# General numerator integrality (Borwein Lemma 3) — the genuine nub, for integer `q ≥ 2`

This file discharges the hardest sub-obligation of the general `borwein_approximants` axiom
(`General.lean`): **numerator integrality**, i.e. that the q-Lagrange combination

    `N_h(q,n) = ∑_{j=1}^n μ_j(q,n) · ∏_{k=1}^{n-1} (1 − q^{k+j−h})`,    `μ_j = ∏_{l≠j}(1 − q^l/q^j)⁻¹`,

is an **integer**, for every integer `q ≥ 2`. This is `PENDING_WORK.md` path 3a, generalized from the
`q = 2` case (`Lemma3.lean`, `Nh_int`) to all bases `q ≥ 2` (an infinite family).

The argument is the `q = 2` template with `2` replaced by a general integer `q`, made possible because
the underlying engine is already general: the q-Lagrange identity `qLagrange` (`QLagrange.lean`, valid
for real `q > 1`), the Gaussian binomial `qBin` (`QBinom.lean`, any `CommRing`), and the standalone
bricks `coprime_qpow_sub_one`, `borwein_div` (`General.lean`).

`N_h ∈ ℤ` follows from two *coprime* clearings:
* **part (a), q-adic** (`nh_qadic_int`): `(q^h)^{n−1}·N_h ∈ ℤ`. The factor `(q^h)^{n−1}` absorbs the
  negative q-powers; q-Lagrange collapses the `μ_j`-sum to Gaussian binomials. So `N_h ∈ ℤ[1/q]`.
* **part (b), coprime-to-q** (`DfullG_NhG_int`): `D·N_h ∈ ℤ` where `D = ∏_j ∏_{l≠j}(q^{|j−l|}−1)` is
  coprime to `q` (each `q^d − 1 ≡ −1 mod q`, `coprime_qpow_sub_one`). So `N_h ∈ ℤ[1/D]`.
The combine `int_of_coprime_clearings` (general `ℤ[1/e] ∩ ℤ[1/f] = ℤ` for `IsCoprime e f`) then gives
`N_h ∈ ℤ` (`NhG_int`).

(Only `q ≥ 2` — positive — is covered, because part (a) routes through `qLagrange`'s `1 < q`. The
`q ≤ −2` case needs the q-Lagrange node-distinctness re-derived for negative `q`; noted as a TODO.)

This file is additive; it does not touch `erdos_1050_irrational` (axiom-clean) and does not yet wire
`NhG_int` into a parametric `Eterm` (the residue-identity layer), which remains the open work toward
fully discharging `borwein_approximants`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Finset

/- ### Generic facts for integer `q` with `2 ≤ |q|`. -/

/-- `(q : ℝ) ≠ 0` when `2 ≤ |q|`. -/
lemma qcast_ne_zero {q : ℤ} (hq : 2 ≤ |q|) : (q : ℝ) ≠ 0 := by
  have hq0 : q ≠ 0 := by rintro rfl; norm_num at hq
  exact Int.cast_ne_zero.mpr hq0

/-- `(q : ℝ)^d ≠ 1` for `d ≥ 1` when `2 ≤ |q|` (since `|q^d| = |q|^d ≥ 2`). -/
lemma qcast_pow_ne_one {q : ℤ} (hq : 2 ≤ |q|) {d : ℕ} (hd : 1 ≤ d) : (q : ℝ) ^ d ≠ 1 := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have h1 : (1 : ℝ) ≤ |(q : ℝ)| := by linarith
  have hge : (2 : ℝ) ≤ |(q : ℝ)| ^ d := by
    calc (2 : ℝ) ≤ |(q : ℝ)| := hqabs
      _ = |(q : ℝ)| ^ 1 := (pow_one _).symm
      _ ≤ |(q : ℝ)| ^ d := pow_le_pow_right₀ h1 hd
  intro h
  rw [← abs_pow, h, abs_one] at hge
  norm_num at hge

/-- General q-Lagrange weight `μ_j = ∏_{l∈[1,n], l≠j}(1 − q^l/q^j)⁻¹` (real `q`). -/
noncomputable def muWG (q : ℝ) (n j : ℕ) : ℝ :=
  ∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹

/-- General q-Lagrange combination `N_h(q,n) = ∑_j μ_j ∏_{k=1}^{n-1}(1 − q^{k+j−h})`. -/
noncomputable def NhG (q : ℝ) (n h : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, muWG q n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h))

/-- **General coprime clearing** `ℤ[1/e] ∩ ℤ[1/f] = ℤ`: if `e·N` and `f·N` are integers with
`IsCoprime e f`, then `N` is an integer. Generalizes `int_of_clearings` (`2`/odd) to arbitrary
coprime denominators — the combine step of the general numerator integrality (path 3a). -/
lemma int_of_coprime_clearings {N : ℝ} {A B e f : ℤ} (hef : IsCoprime e f)
    (hA : (A : ℝ) = (e : ℝ) * N) (hB : (B : ℝ) = (f : ℝ) * N) :
    ∃ z : ℤ, (z : ℝ) = N := by
  obtain ⟨u, v, huv⟩ := hef
  refine ⟨u * A + v * B, ?_⟩
  have hcast : ((u * A + v * B : ℤ) : ℝ) = (u : ℝ) * (A : ℝ) + (v : ℝ) * (B : ℝ) := by
    push_cast; ring
  rw [hcast, hA, hB]
  have key : (u : ℝ) * ((e : ℝ) * N) + (v : ℝ) * ((f : ℝ) * N) = ((u * e + v * f : ℤ) : ℝ) * N := by
    push_cast; ring
  rw [key, huv, Int.cast_one, one_mul]

/- ### Part (a): the q-adic clearing `(q^h)^{n−1}·N_h ∈ ℤ`. -/

/-- General q-Lagrange identity for integer `q ≥ 2`: `∑_j μ_j (q^j)^i = q^i·[n+i−1,n−1]_q`, `i < n`. -/
theorem qLagG {q : ℤ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ i
      = (q : ℝ) ^ i * qBin (q : ℝ) (n + i - 1) (n - 1) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have h := qLagrange (q : ℝ) hq1 n hn i (by omega)
  simpa only [muWG] using h

/-- General q-Lagrange identity for `2 ≤ |q|` (both signs, e.g. negative base `q ≤ −2`):
`∑_j μ_j (q^j)^i = q^i·[n+i−1,n−1]_q`. Same as `qLagG` but via `qLagrange_abs`. -/
theorem qLagG_abs {q : ℤ} (hq : 2 ≤ |q|) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ i
      = (q : ℝ) ^ i * qBin (q : ℝ) (n + i - 1) (n - 1) := by
  have hq1 : (1 : ℝ) < |(q : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (by omega : (1 : ℤ) < |q|)
  have h := qLagrange_abs (q : ℝ) hq1 n hn i (by omega)
  simpa only [muWG] using h

/-- Cleared product (general `q`): `(q^h)^{n-1}·∏(1−q^{k+j−h}) = ∏(q^h−q^{k+j})`. -/
lemma clearedProdG {q : ℤ} (hq : 2 ≤ |q|) (n j h : ℕ) :
    ((q : ℝ) ^ h) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))
      = ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j)) := by
  have hqne : (q : ℝ) ≠ 0 := qcast_ne_zero hq
  have hcard : ((q : ℝ) ^ h) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (q : ℝ) ^ h := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [mul_sub, mul_one]
  congr 1
  rw [← zpow_natCast (q : ℝ) h, ← zpow_add₀ hqne, ← zpow_natCast (q : ℝ) (k + j)]
  congr 1
  push_cast
  ring

/-- Expand `∏(q^h − q^{k+j})` over subsets `t ⊆ [1,n-1]` as a polynomial in `q^j`. -/
lemma prod_diff_expandG (q : ℤ) (n j h : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ j) ^ t.card
            * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card) := by
  have hf : ∀ k, ((q : ℝ) ^ h - (q : ℝ) ^ (k + j) : ℝ) = (-(q : ℝ) ^ (k + j)) + (q : ℝ) ^ h :=
    fun k => by ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const]
  have hexp : ∏ k ∈ t, (-(q : ℝ) ^ (k + j))
      = (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ j) ^ t.card := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k _; rw [pow_add]; ring
  rw [hexp]

/-- q-Lagrange reduction of the cleared `N_h` (the `muW`-free form). -/
lemma Nh_prod_qLagG {q : ℤ} (hq : 2 ≤ q) (n h : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n,
        muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
            * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
        = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
              * (muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ t.card) := by
    intro j _
    rw [prod_diff_expandG q n j h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1; omega
  rw [← Finset.mul_sum, qLagG hq hn t.card hcard]

/-- Per-`t` integer witness for the cleared `N_h`. -/
def Nh2TermIntG (q : ℤ) (n h : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-q ^ k)) * (q ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
    * (q ^ t.card * qBin q (n + t.card - 1) (n - 1))

/-- Each `Nh_prod_qLagG` `t`-term is the integer `Nh2TermIntG q n h t`. -/
lemma Nh2TermIntG_cast (q : ℤ) (n h : ℕ) (t : Finset ℕ) :
    (Nh2TermIntG q n h t : ℝ)
      = (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
        * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  have hbin : ((qBin q (n + t.card - 1) (n - 1) : ℤ) : ℝ) = qBin (q : ℝ) (n + t.card - 1) (n - 1) :=
    (qBin_map (Int.castRingHom ℝ) q (n + t.card - 1) (n - 1)).symm
  rw [Nh2TermIntG]
  push_cast [hbin]
  ring

/-- The clearing identity `(q^h)^{n−1}·N_h = ∑_j μ_j ∏(q^h − q^{k+j})`. -/
lemma Nh_2adicG {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) :
    ((q : ℝ) ^ h) ^ (n - 1) * NhG (q : ℝ) n h
      = ∑ j ∈ Finset.Icc 1 n,
          muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j)) := by
  rw [NhG, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, clearedProdG hq n j h]

/-- **Part (a): q-adic clearing.** `(q^h)^{n−1}·N_h ∈ ℤ`, so `N_h ∈ ℤ[1/q]`. -/
lemma nh_qadic_int {q : ℤ} (hq : 2 ≤ q) (n h : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = ((q : ℝ) ^ h) ^ (n - 1) * NhG (q : ℝ) n h := by
  have habs : 2 ≤ |q| := by rw [abs_of_pos (by omega : (0 : ℤ) < q)]; exact hq
  rw [Nh_2adicG habs n h, Nh_prod_qLagG hq n h hn]
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, Nh2TermIntG q n h t, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Nh2TermIntG_cast q n h t

/- ### Part (b): the coprime-to-q clearing `D·N_h ∈ ℤ` with `IsCoprime D q`. -/

/-- The cleared `l`-factor value: `q^{j−l}` if `l<j`, else `−1`. -/
def zfacG (q : ℤ) (j l : ℕ) : ℤ := if l < j then q ^ (j - l) else -1

/-- Per-factor coprime clearing: `(q^{|j−l|}−1)·(1 − q^l/q^j)⁻¹ = zfacG q j l ∈ ℤ`. -/
lemma factor_clearG {q : ℤ} (hq : 2 ≤ |q|) {j l : ℕ} (hlj : l ≠ j) :
    ((zfacG q j l : ℤ) : ℝ)
      = (((q ^ (max j l - min j l) - 1 : ℤ)) : ℝ) * (1 - (q : ℝ) ^ l / (q : ℝ) ^ j)⁻¹ := by
  have hqne : (q : ℝ) ≠ 0 := qcast_ne_zero hq
  rw [zfacG]
  rcases lt_or_gt_of_ne hlj with hlt | hgt
  · rw [if_pos hlt]
    have hmm : max j l - min j l = j - l := by omega
    have hd1 : 1 ≤ j - l := by omega
    have ha1 : (q : ℝ) ^ (j - l) - 1 ≠ 0 := sub_ne_zero.mpr (qcast_pow_ne_one hq hd1)
    have hQ0 : (q : ℝ) ^ (j - l) ≠ 0 := pow_ne_zero _ hqne
    have hdiv : ((q : ℝ) ^ l / (q : ℝ) ^ j) = ((q : ℝ) ^ (j - l))⁻¹ := by
      rw [show (q : ℝ) ^ j = (q : ℝ) ^ (j - l) * (q : ℝ) ^ l from by
        rw [← pow_add]; congr 1; omega]
      rw [mul_comm]; field_simp
    rw [hmm, hdiv]
    push_cast
    field_simp
  · rw [if_neg (by omega)]
    have hmm : max j l - min j l = l - j := by omega
    have hd1 : 1 ≤ l - j := by omega
    have ha1 : (q : ℝ) ^ (l - j) - 1 ≠ 0 := sub_ne_zero.mpr (qcast_pow_ne_one hq hd1)
    have hdiv : ((q : ℝ) ^ l / (q : ℝ) ^ j) = (q : ℝ) ^ (l - j) := by
      rw [show (q : ℝ) ^ l = (q : ℝ) ^ (l - j) * (q : ℝ) ^ j from by
        rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    rw [show (1 : ℝ) - (q : ℝ) ^ (l - j) = -((q : ℝ) ^ (l - j) - 1) from by ring, inv_neg]
    field_simp

/-- The coprime-to-q clearing product `VgenW q n j = ∏_{l≠j}(q^{|j−l|}−1)`. -/
def VgenW (q : ℤ) (n j : ℕ) : ℤ :=
  ∏ l ∈ (Finset.Icc 1 n).erase j, (q ^ (max j l - min j l) - 1)

/-- `VgenW q n j` is coprime to `q` (each factor `q^d − 1 ≡ −1 mod q`, `d ≥ 1`). -/
lemma VgenW_coprime (q : ℤ) (n j : ℕ) : IsCoprime (VgenW q n j) q := by
  rw [VgenW]
  apply IsCoprime.prod_left
  intro l hl
  rw [Finset.mem_erase] at hl
  obtain ⟨hlj, _⟩ := hl
  obtain ⟨d, hd⟩ : ∃ d, max j l - min j l = d + 1 := ⟨max j l - min j l - 1, by omega⟩
  rw [hd]
  exact coprime_qpow_sub_one q d

/-- `VgenW q n j · μ_j ∈ ℤ` — the coprime product clears `μ_j`'s denominator (per-factor). -/
lemma VgenW_muWG_int {q : ℤ} (hq : 2 ≤ |q|) (n j : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (VgenW q n j : ℝ) * muWG (q : ℝ) n j := by
  refine ⟨∏ l ∈ (Finset.Icc 1 n).erase j, zfacG q j l, ?_⟩
  rw [Int.cast_prod, VgenW, Int.cast_prod, muWG, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  exact factor_clearG hq (Finset.mem_erase.mp hl).1

/-- The coprime common denominator `DfullG q n = ∏_{j∈[1,n]} VgenW q n j`, clearing every `μ_j`. -/
def DfullG (q : ℤ) (n : ℕ) : ℤ := ∏ j ∈ Finset.Icc 1 n, VgenW q n j

/-- `DfullG q n` is coprime to `q`. -/
lemma DfullG_coprime (q : ℤ) (n : ℕ) : IsCoprime (DfullG q n) q := by
  rw [DfullG]
  apply IsCoprime.prod_left
  intro j _
  exact VgenW_coprime q n j

/-- `DfullG q n · μ_j ∈ ℤ` for `j ∈ [1,n]`. -/
lemma DfullG_muWG_int {q : ℤ} (hq : 2 ≤ |q|) {n j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    ∃ m : ℤ, (m : ℝ) = (DfullG q n : ℝ) * muWG (q : ℝ) n j := by
  obtain ⟨z, hz⟩ := VgenW_muWG_int hq n j
  refine ⟨(∏ j' ∈ (Finset.Icc 1 n).erase j, VgenW q n j') * z, ?_⟩
  rw [DfullG, ← Finset.mul_prod_erase (Finset.Icc 1 n) (VgenW q n) hj]
  push_cast
  rw [hz]
  ring

/-- `P_j = ∏_{k=1}^{n−1}(1 − q^{k+j−h})` is an integer when `j ≥ h` (all exponents `≥ 1`). -/
lemma PjG_int {q : ℤ} {n j h : ℕ} (hjh : h ≤ j) :
    ∃ p : ℤ, (p : ℝ) = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  refine ⟨∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ (k + j - h)), ?_⟩
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [show ((k : ℤ) + j - h) = ((k + j - h : ℕ) : ℤ) from by omega, zpow_natCast]
  norm_cast

/-- `P_j = 0` when `1 ≤ j < h ≤ n` (the factor with exponent `0` vanishes). -/
lemma prod_vanishG {q : ℤ} {n j h : ℕ} (hj : 1 ≤ j) (hjh : j < h) (hhn : h ≤ n) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) = 0 := by
  apply Finset.prod_eq_zero (i := h - j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have : ((h - j : ℕ) : ℤ) + j - h = 0 := by rw [Nat.cast_sub (by omega)]; ring
  rw [this, zpow_zero, sub_self]

/-- **Part (b): the coprime-to-q clearing of `N_h`.** `DfullG q n · N_h ∈ ℤ`, with
`IsCoprime (DfullG q n) q`. So `N_h ∈ ℤ[1/D]` for `D` coprime to `q`. -/
lemma DfullG_NhG_int {q : ℤ} (hq : 2 ≤ |q|) {n : ℕ} (h : ℕ) (_hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (DfullG q n : ℝ) * NhG (q : ℝ) n h := by
  rw [NhG, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.Icc 1 n, ∃ b : ℤ, (b : ℝ) = (DfullG q n : ℝ) *
      (muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) := by
    intro j hj
    rcases Nat.lt_or_ge j h with hlt | hge
    · refine ⟨0, ?_⟩
      rw [Finset.mem_Icc] at hj
      have hv : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) = 0 :=
        prod_vanishG hj.1 hlt hhn
      rw [hv]; push_cast; ring
    · obtain ⟨m, hm⟩ := DfullG_muWG_int hq hj
      obtain ⟨p, hp⟩ := PjG_int (q := q) (n := n) hge
      exact ⟨m * p, by push_cast; rw [hm, hp]; ring⟩
  choose b hb using hterm
  refine ⟨∑ j ∈ (Finset.Icc 1 n).attach, b j.1 j.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.Icc 1 n) _]
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  exact hb j hj

/- ### Combine: `N_h ∈ ℤ` for integer `q ≥ 2`. -/

/-- **General numerator integrality (Borwein Lemma 3), for integer `q ≥ 2`.** The q-Lagrange
combination `N_h(q,n) = ∑_j μ_j ∏_{k=1}^{n-1}(1 − q^{k+j−h})` is an integer. Combine the q-adic
clearing (part a, `nh_qadic_int`) and the coprime-to-q clearing (part b, `DfullG_NhG_int`) via
`int_of_coprime_clearings`, using `IsCoprime (q^{(n-1)h}) (DfullG q n)` (a power of `q` is coprime to
`DfullG`, which is coprime to `q`). This discharges the genuine nub of the general
`borwein_approximants` for every base `q ≥ 2`. -/
theorem NhG_int {q : ℤ} (hq : 2 ≤ q) (n h : ℕ) (hn : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = NhG (q : ℝ) n h := by
  have habs : 2 ≤ |q| := by rw [abs_of_pos (by omega : (0 : ℤ) < q)]; exact hq
  obtain ⟨A, hA⟩ := nh_qadic_int hq n h hn
  obtain ⟨B, hB⟩ := DfullG_NhG_int habs h hh1 hhn
  -- part (a) gives `(q^h)^{n−1}·N_h = q^{(n−1)h}·N_h`.
  have hA' : (A : ℝ) = (q : ℝ) ^ ((n - 1) * h) * NhG (q : ℝ) n h := by
    rw [hA, ← pow_mul, mul_comm h (n - 1)]
  -- `q^{(n−1)h}` is coprime to `DfullG q n` (power of q vs coprime-to-q).
  have hcop : IsCoprime ((q : ℤ) ^ ((n - 1) * h)) (DfullG q n) :=
    (IsCoprime.pow_left ((DfullG_coprime q n).symm))
  have hA'' : ((A : ℤ) : ℝ) = ((q ^ ((n - 1) * h) : ℤ) : ℝ) * NhG (q : ℝ) n h := by
    push_cast; exact hA'
  exact int_of_coprime_clearings hcop hA'' hB

/- ### Negative base `q ≤ −2`: the numerator nub `N_h ∈ ℤ` for `2 ≤ |q|`.

The magnitude bricks (`clearedProdG`, `Nh_2adicG`, `DfullG_NhG_int`, `DfullG_coprime`) already hold for
`2 ≤ |q|`; only the q-Lagrange reduction needed the positive variant. With `qLagG_abs` the whole q-adic
clearing — and hence `N_h ∈ ℤ` — generalizes to `2 ≤ |q|`, covering negative base. -/

/-- q-Lagrange reduction of the cleared `N_h` for `2 ≤ |q|` (via `qLagG_abs`). -/
lemma Nh_prod_qLagG_abs {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n,
        muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
            * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muWG (q : ℝ) n j * ∏ k ∈ Finset.Icc 1 (n - 1), ((q : ℝ) ^ h - (q : ℝ) ^ (k + j))
        = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-(q : ℝ) ^ k)) * ((q : ℝ) ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
              * (muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ t.card) := by
    intro j _
    rw [prod_diff_expandG q n j h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1; omega
  rw [← Finset.mul_sum, qLagG_abs hq hn t.card hcard]

/-- **Part (a) for `2 ≤ |q|`**: `(q^h)^{n−1}·N_h ∈ ℤ`. -/
lemma nh_qadic_int_abs {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = ((q : ℝ) ^ h) ^ (n - 1) * NhG (q : ℝ) n h := by
  rw [Nh_2adicG hq n h, Nh_prod_qLagG_abs hq n h hn]
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, Nh2TermIntG q n h t, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Nh2TermIntG_cast q n h t

/-- **Borwein Lemma 3 numerator nub for `2 ≤ |q|`** (both signs, incl. negative base `q ≤ −2`):
the q-Lagrange combination `N_h = NhG q n h ∈ ℤ`. Via the q-adic clearing (`nh_qadic_int_abs`) and the
coprime-to-q clearing (`DfullG_NhG_int`, already general). A brick toward `AcorrG_int` for negative base. -/
theorem NhG_int_abs {q : ℤ} (hq : 2 ≤ |q|) (n h : ℕ) (hn : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = NhG (q : ℝ) n h := by
  obtain ⟨A, hA⟩ := nh_qadic_int_abs hq n h hn
  obtain ⟨B, hB⟩ := DfullG_NhG_int hq h hh1 hhn
  have hA' : (A : ℝ) = (q : ℝ) ^ ((n - 1) * h) * NhG (q : ℝ) n h := by
    rw [hA, ← pow_mul, mul_comm h (n - 1)]
  have hcop : IsCoprime ((q : ℤ) ^ ((n - 1) * h)) (DfullG q n) :=
    (IsCoprime.pow_left ((DfullG_coprime q n).symm))
  have hA'' : ((A : ℤ) : ℝ) = ((q ^ ((n - 1) * h) : ℤ) : ℝ) * NhG (q : ℝ) n h := by
    push_cast; exact hA'
  exact int_of_coprime_clearings hcop hA'' hB

/- ### General first-form = second-form denominator identity (Borwein Lemma 2, "Piece III").

`pₙ(C,q)` has a *first* form (a `μ_j`-weighted sum, the residue form) and a *second* form (the
Gaussian-binomial `pValG`). They agree (`pFirstG_eq_pValG`), via the Cauchy q-binomial expansion
(`cprod_cauchyG`) and the general q-Lagrange identity (`qLagrange`). This is a building block of the
general residue identity (Lemma 1), parametric in `(q, C)`. -/

/-- q-Lagrange identity in `muWG` form for `1 < |q|` (both signs, negative base allowed). -/
lemma qLagrange_muWG {q : ℝ} (hq1 : 1 < |q|) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muWG q n j * (q ^ j) ^ i = q ^ i * qBin q (n + i - 1) (n - 1) := by
  have h := qLagrange_abs q hq1 n hn i (by omega)
  simpa only [muWG] using h

/-- Exponent bookkeeping `i(i−1)/2 + 2i = i(i+3)/2`. -/
private lemma exp_idenG (i : ℕ) : i * (i - 1) / 2 + 2 * i = i * (i + 3) / 2 := by
  rcases i with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1) * (m + 1 + 3) = (c + 2 * (m + 1)) + (c + 2 * (m + 1)) := by
      have : (m + 1) * (m + 1 + 3) = m * (m + 1) + 4 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- The Cauchy expansion of the `c`-product (general `q, C`). -/
lemma cprod_cauchyG (q C : ℝ) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))
      = ∑ i ∈ Finset.range n,
          q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ ((j + 1) * i) := by
  have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.prod_Ico_eq_prod_range]
  have hterm : ∀ k, (1 - C * q ^ (1 + k + j)) = 1 + q ^ k * (-C * q ^ (j + 1)) := by
    intro k
    rw [show 1 + k + j = k + (j + 1) from by ring, pow_add]; ring
  rw [Finset.prod_congr rfl (fun k _ => hterm k), qBin_cauchy q (-C * q ^ (j + 1)) (n - 1),
    Nat.sub_add_cancel hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← pow_mul]
  ring

/-- Borwein's q-Padé denominator in **first form** `pₙ = ∑_{j=1}^n μ_j·∏_{k=1}^{n-1}(1−C q^{k+j})`. -/
noncomputable def pFirstG (q C : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, muWG q n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))

/-- **First form = second form** (Borwein Lemma 2), general `(q, C)`, `1 < |q|` (negative base
allowed): `pFirstG = pValG`. -/
theorem pFirstG_eq_pValG {q : ℝ} (hq1 : 1 < |q|) (C : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    pFirstG q C n = pValG q C n := by
  rw [pFirstG, pValG]
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muWG q n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))
        = ∑ i ∈ Finset.range n,
            muWG q n j * (q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ ((j + 1) * i)) := by
    intro j _
    rw [cprod_cauchyG q C hn j, Finset.mul_sum]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hfac : ∀ j ∈ Finset.Icc 1 n,
      muWG q n j * (q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ ((j + 1) * i))
        = (q ^ (i * (i - 1) / 2) * qBin q (n - 1) i * (-C) ^ i * q ^ i)
          * (muWG q n j * (q ^ j) ^ i) := by
    intro j _
    rw [show (j + 1) * i = i + j * i from by ring, pow_add, pow_mul]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, qLagrange_muWG hq1 hn i hi]
  rw [show i * (i + 3) / 2 = i * (i - 1) / 2 + 2 * i from (exp_idenG i).symm, pow_add]
  ring

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/GeneralResidue.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# General residue identity, Piece II — the auxiliary-series collapse (parametric in `(q, C)`)

Toward discharging the general `borwein_approximants` (`General.lean`), this file ports Borwein's
"Piece II" — the collapse of the auxiliary series

    `T_i(q,C) = ∑_{j≥0} q^{−i(j+1)}·(1 − C·q^{j+1})⁻¹`

into `T_i = C^i·z + R_i`, where `z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹` is the q-harmonic value and
`R_i = ∑_{l=1}^i C^{i−l}/(q^l − 1)` is a rational correction — from the `q = 2, C = 8/3` case
(`Residue.lean`, `Tser_collapse`) to all real `q > 1` and `C ≠ 0`.

This is the analytic heart of the residue identity (Lemma 1): every inner tail series of `Eterm`
reindexes onto the `T_i` grid, and this collapse is what produces the `−pVal·z + (rational)` form.
All summability is genuine (geometric majorant, same estimate as `qharmonic_summable`); nothing is
cited. Restricted to `q > 1` (positive `q`) because the geometric sums use a nonneg ratio `q^{−1}`;
the `q < −1` case needs the alternating-geometric variant (TODO).

Additive; does not touch `erdos_1050_irrational` (axiom-clean).
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Filter Topology

/-- The general q-harmonic value `z = ∑_{j≥0} (1 − C·q^{j+1})⁻¹` (the value in `borwein_approximants`). -/
noncomputable def zG (q C : ℝ) : ℝ := ∑' j : ℕ, (1 - C * q ^ (j + 1))⁻¹

/-- The rational correction `R_i = ∑_{l=1}^i C^{i−l}/(q^l − 1)`, via `R_{i+1} = 1/(q^{i+1}−1) + C·R_i`. -/
noncomputable def RratG (q C : ℝ) : ℕ → ℝ
  | 0 => 0
  | (i + 1) => 1 / (q ^ (i + 1) - 1) + C * RratG q C i

/-- The auxiliary series `T_i = ∑_{j≥0} q^{−i(j+1)}·(1 − C·q^{j+1})⁻¹`. -/
noncomputable def TserG (q C : ℝ) (i : ℕ) : ℝ :=
  ∑' j : ℕ, (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹

variable {q C : ℝ}

/-- For `q > 1`, `q^k − 1 ≠ 0` (any `k ≥ 1`). -/
private lemma qpowk_sub_one_ne (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k) : q ^ k - 1 ≠ 0 := by
  have : (1 : ℝ) < q ^ k := by
    calc (1 : ℝ) < q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := pow_le_pow_right₀ (le_of_lt hq) hk
  linarith

/-- Per-term collapse identity. With `P = q^{j+1}`: `(P^{i+1})⁻¹(1−CP)⁻¹ = (P^{i+1})⁻¹ + C(P^i)⁻¹(1−CP)⁻¹`. -/
private lemma key_termG (P : ℝ) (i : ℕ) (hP : P ≠ 0) (hcP : 1 - C * P ≠ 0) :
    (P ^ (i + 1))⁻¹ * (1 - C * P)⁻¹
      = (P ^ (i + 1))⁻¹ + C * (P ^ i)⁻¹ * (1 - C * P)⁻¹ := by
  have hPi : P ^ i ≠ 0 := pow_ne_zero i hP
  have hPi1 : P ^ (i + 1) ≠ 0 := pow_ne_zero (i + 1) hP
  field_simp
  ring

/-- The non-degeneracy hypothesis `C·q^{j+1} ≠ 1` makes `1 − C·q^{j+1} ≠ 0`. -/
private lemma one_sub_ne (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) (j : ℕ) : 1 - C * q ^ (j + 1) ≠ 0 := by
  intro h; exact hCn j (by linarith)

/-- **Summability of `T_i`** (geometric majorant `|q|⁻¹`; works for both signs of `q`, `1 < |q|`). -/
lemma TserG_summable (hq : 1 < |q|) (hC : C ≠ 0) (i : ℕ) :
    Summable (fun j : ℕ => (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹) := by
  have hqabs : 0 < |q| := by linarith
  have hCpos : 0 < |C| := abs_pos.mpr hC
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeo : Summable (fun j : ℕ => (2 / |C|) * (|q|⁻¹) ^ (j + 1)) :=
    (((summable_geometric_of_lt_one (by positivity) hinvlt).comp_injective
      (add_left_injective 1)).mul_left (2 / |C|))
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun j => (2 / |C|) * (|q|⁻¹) ^ (j + 1)) hgeo ?_
  have htend : Filter.Tendsto (fun j : ℕ => |C| * |q| ^ (j + 1)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hCpos
      ((tendsto_pow_atTop_atTop_of_one_lt hq).comp (Filter.tendsto_add_atTop_nat 1))
  filter_upwards [htend.eventually_ge_atTop 2] with j hj
  rw [Real.norm_eq_abs, abs_mul]
  have hqpw : 0 < |q| ^ (j + 1) := pow_pos hqabs _
  -- |(q^{i(j+1)})⁻¹| ≤ 1
  have hA : |(q ^ (i * (j + 1)))⁻¹| ≤ 1 := by
    rw [abs_inv, abs_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hq))
  -- |(1 - C q^{j+1})⁻¹| ≤ (2/|C|)·(|q|⁻¹)^{j+1}
  have hlow : |C| * |q| ^ (j + 1) / 2 ≤ |1 - C * q ^ (j + 1)| := by
    have htri := abs_sub_abs_le_abs_sub (C * q ^ (j + 1)) 1
    rw [abs_one, abs_mul, abs_pow, abs_sub_comm] at htri
    linarith [htri, hj]
  have h2pos : 0 < |C| * |q| ^ (j + 1) / 2 := by positivity
  have hB : |(1 - C * q ^ (j + 1))⁻¹| ≤ (2 / |C|) * (|q|⁻¹) ^ (j + 1) := by
    rw [abs_inv]
    calc |1 - C * q ^ (j + 1)|⁻¹ ≤ (|C| * |q| ^ (j + 1) / 2)⁻¹ := inv_anti₀ h2pos hlow
      _ = (2 / |C|) * (|q|⁻¹) ^ (j + 1) := by rw [inv_pow]; field_simp
  calc |(q ^ (i * (j + 1)))⁻¹| * |(1 - C * q ^ (j + 1))⁻¹|
      ≤ 1 * ((2 / |C|) * (|q|⁻¹) ^ (j + 1)) :=
        mul_le_mul hA hB (abs_nonneg _) (by norm_num)
    _ = (2 / |C|) * (|q|⁻¹) ^ (j + 1) := by rw [one_mul]

/-- `T_0 = z`. -/
lemma TserG_zero : TserG q C 0 = zG q C := by
  unfold TserG zG
  apply tsum_congr
  intro j
  simp

/-- The geometric piece `∑_j q^{−(i+1)(j+1)} = 1/(q^{i+1} − 1)` (norm-geometric; `1 < |q|`, any sign). -/
lemma geom_pieceG (hq : 1 < |q|) (i : ℕ) :
    ∑' j : ℕ, (q ^ ((i + 1) * (j + 1)))⁻¹ = 1 / (q ^ (i + 1) - 1) := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  set r : ℝ := (q ^ (i + 1))⁻¹ with hr
  have hqgt : (1 : ℝ) < |q| ^ (i + 1) := by
    calc (1 : ℝ) < |q| := hq
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ (i + 1) := pow_le_pow_right₀ (le_of_lt hq) (by omega)
  have hrnorm : ‖r‖ < 1 := by
    rw [hr, Real.norm_eq_abs, abs_inv, abs_pow]
    exact inv_lt_one_of_one_lt₀ hqgt
  have hconv : ∀ j : ℕ, (q ^ ((i + 1) * (j + 1)))⁻¹ = r * r ^ j := by
    intro j; rw [hr, ← pow_succ', inv_pow, ← pow_mul]
  rw [tsum_congr hconv, tsum_mul_left, tsum_geometric_of_norm_lt_one hrnorm, hr]
  have hx0 : (q : ℝ) ^ (i + 1) ≠ 0 := pow_ne_zero _ hqne
  have hx2 : (q : ℝ) ^ (i + 1) - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h
    have habs : |q ^ (i + 1)| = 1 := by rw [h]; norm_num
    rw [abs_pow] at habs; linarith
  field_simp

/-- The geometric piece is summable (`|q|⁻¹` majorant). -/
lemma geom_summableG (hq : 1 < |q|) (i : ℕ) :
    Summable (fun j : ℕ => (q ^ ((i + 1) * (j + 1)))⁻¹) := by
  have hqabs : 0 < |q| := by linarith
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeo : Summable (fun j : ℕ => (|q|⁻¹) ^ (j + 1)) :=
    (summable_geometric_of_lt_one (by positivity) hinvlt).comp_injective (add_left_injective 1)
  apply Summable.of_norm_bounded hgeo
  intro j
  rw [Real.norm_eq_abs, abs_inv, abs_pow, inv_pow]
  exact inv_anti₀ (pow_pos hqabs _) (pow_le_pow_right₀ (le_of_lt hq) (by rw [Nat.succ_mul]; omega))

/-- **The collapse recurrence** `T_{i+1} = 1/(q^{i+1} − 1) + C·T_i` (`1 < |q|`, any sign). -/
lemma TserG_succ (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) (i : ℕ) :
    TserG q C (i + 1) = 1 / (q ^ (i + 1) - 1) + C * TserG q C i := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  unfold TserG
  have hterm : ∀ j : ℕ,
      (q ^ ((i + 1) * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹
        = (q ^ ((i + 1) * (j + 1)))⁻¹
          + C * (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹ := by
    intro j
    have hk := key_termG (C := C) (q ^ (j + 1)) i (pow_ne_zero _ hqne) (one_sub_ne hCn j)
    have e1 : q ^ ((i + 1) * (j + 1)) = (q ^ (j + 1)) ^ (i + 1) := by rw [← pow_mul, Nat.mul_comm]
    have e2 : q ^ (i * (j + 1)) = (q ^ (j + 1)) ^ i := by rw [← pow_mul, Nat.mul_comm]
    rw [e1, e2]; exact hk
  rw [tsum_congr hterm]
  have hsum_rest : Summable
      (fun j : ℕ => C * (q ^ (i * (j + 1)))⁻¹ * (1 - C * q ^ (j + 1))⁻¹) := by
    simp_rw [mul_assoc]
    exact (TserG_summable hq hC i).mul_left C
  rw [Summable.tsum_add (geom_summableG hq i) hsum_rest, geom_pieceG hq i]
  congr 1
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- **Piece II — the collapse** `T_i = C^i·z + R_i` (induction from the recurrence; `1 < |q|`). -/
theorem TserG_collapse (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) (i : ℕ) :
    TserG q C i = C ^ i * zG q C + RratG q C i := by
  induction i with
  | zero => rw [TserG_zero, show RratG q C 0 = 0 from rfl]; ring
  | succ i ih =>
      rw [TserG_succ hq hC hCn, ih, show RratG q C (i + 1) = 1 / (q ^ (i + 1) - 1) + C * RratG q C i from rfl]
      ring

/- ### Assembly bricks for the residue identity (Lemma 1, first form), parametric in `(q, C)`. -/

/-- The `m`-th term of the explicit (contour-free) error series, general `(q, C)`. -/
noncomputable def ItermG (q C : ℝ) (n m : ℕ) : ℝ :=
  -(1 - C * q ^ ((m : ℤ) + n))⁻¹ *
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹

/-- The error term `Eₙ = ∑_{m≥n} Iₘ`, reindexed `∑_{j≥0} I_{n}(n+j)`, general `(q, C)`. -/
noncomputable def EtermG (q C : ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, ItermG q C n (n + j)

/-- `Iₘ = −(∏_{k=1}^{n-1}(1−q^{k−m}))·∏_{k=1}^{n}(1−C·q^{k+m})⁻¹` (for `n ≥ 1`). -/
lemma ItermG_prod_form (n m : ℕ) (hn : 1 ≤ n) :
    ItermG q C n m
      = -((∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) - m)))
          * ∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ ((k : ℤ) + m))⁻¹) := by
  rw [ItermG, Finset.prod_mul_distrib,
    show ((m : ℤ) + n) = ((n : ℤ) + m) from by ring,
    show Finset.Icc 1 n = Finset.Icc 1 ((n - 1) + 1) from by rw [Nat.sub_add_cancel hn],
    Finset.prod_Icc_succ_top (by omega : 1 ≤ (n - 1) + 1), Nat.sub_add_cancel hn]
  ring

/-- **`q`-numerator expansion** `∏_{k=1}^{n-1}(1−q^{k−m}) = ∑_t (∏_{k∈t}−q^k)·(q^{−m})^{|t|}`. -/
lemma DtermG_expand (hq : 1 < |q|) (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) - m)))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-q ^ k)) * ((q ^ m)⁻¹) ^ t.card := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  have hfac : ∀ k : ℕ, (1 : ℝ) - q ^ ((k : ℤ) - m) = 1 + (-(q ^ k)) * (q ^ m)⁻¹ := by
    intro k
    rw [zpow_sub₀ hqne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    ring
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The inner tail series `∑_{m≥0} q^{−i(n+m)}·u_{(n+m)+j}` of the assembly. -/
noncomputable def StailG (q C : ℝ) (i j n : ℕ) : ℝ :=
  ∑' m : ℕ, (q ^ (i * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹

/-- The finite rational "head" removed when reindexing `StailG` onto the `TserG` grid. -/
noncomputable def headSG (q C : ℝ) (i j n : ℕ) : ℝ :=
  ∑ m' ∈ Finset.range (n + j - 1), (q ^ (i * (m' + 1)))⁻¹ * (1 - C * q ^ (m' + 1))⁻¹

/-- **Tail collapse**: `StailG = q^{ij}·(TserG i − headSG)`, a finite reindex onto the `TserG` grid. -/
lemma StailG_collapse (hq : 1 < |q|) (hC : C ≠ 0) (i j n : ℕ) (hnj : 1 ≤ n + j) :
    StailG q C i j n = q ^ (i * j) * (TserG q C i - headSG q C i j n) := by
  have hqne : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  have hterm : ∀ m : ℕ,
      (q ^ (i * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹
        = q ^ (i * j) * ((q ^ (i * ((m + (n + j - 1)) + 1)))⁻¹
            * (1 - C * q ^ ((m + (n + j - 1)) + 1))⁻¹) := by
    intro m
    have h1 : (m + (n + j - 1)) + 1 = (n + m) + j := by omega
    have hw : (q ^ (i * (n + m)))⁻¹ = q ^ (i * j) * (q ^ (i * ((n + m) + j)))⁻¹ := by
      rw [show i * ((n + m) + j) = i * j + i * (n + m) from by ring, pow_add, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hqne), one_mul]
    rw [h1, hw]; ring
  rw [StailG, tsum_congr hterm, tsum_mul_left]
  congr 1
  have hsum := Summable.sum_add_tsum_nat_add (n + j - 1) (TserG_summable hq hC i)
  rw [show TserG q C i = ∑' m : ℕ, (q ^ (i * (m + 1)))⁻¹ * (1 - C * q ^ (m + 1))⁻¹ from rfl, headSG]
  linarith [hsum]

/-- **z-coefficient bridge**: `pFirstG` re-expanded over the same subsets `t ⊆ [1,n−1]` that the
`q`-numerator `DtermG_expand` produces. -/
lemma pFirstG_powerset (n : ℕ) :
    pFirstG q C n = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-C * q ^ k)) * ∑ j ∈ Finset.Icc 1 n, muWG q n j * (q ^ j) ^ t.card := by
  rw [pFirstG]
  have hexp : ∀ j, ∏ k ∈ Finset.Icc 1 (n - 1), (1 - C * q ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-C * q ^ k)) * (q ^ j) ^ t.card := by
    intro j
    have hf : ∀ k, (1 : ℝ) - C * q ^ (k + j) = 1 + (-C * q ^ k) * q ^ j := by
      intro k; rw [pow_add]; ring
    rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hexp j])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `StailG`'s summand is summable (geometric majorant `|q|⁻¹`; `1 < |q|`, any sign). -/
lemma StailG_summable (hq : 1 < |q|) (hC : C ≠ 0) (n i j : ℕ) :
    Summable (fun m : ℕ => (q ^ (i * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹) := by
  have hqabs : 0 < |q| := by linarith
  have hCpos : 0 < |C| := abs_pos.mpr hC
  have hinvlt : |q|⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeo : Summable (fun m : ℕ => ((2 / |C|) * (|q|⁻¹) ^ (n + j)) * (|q|⁻¹) ^ m) :=
    (summable_geometric_of_lt_one (by positivity) hinvlt).mul_left _
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun m => ((2 / |C|) * (|q|⁻¹) ^ (n + j)) * (|q|⁻¹) ^ m) hgeo ?_
  have hexp : ∀ m : ℕ, (n + m) + j = m + (n + j) := fun m => by omega
  have htend : Filter.Tendsto (fun m : ℕ => |C| * |q| ^ ((n + m) + j)) Filter.atTop Filter.atTop := by
    have h : Filter.Tendsto (fun m : ℕ => |C| * |q| ^ (m + (n + j))) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hCpos
        ((tendsto_pow_atTop_atTop_of_one_lt hq).comp (Filter.tendsto_add_atTop_nat (n + j)))
    simpa only [hexp] using h
  filter_upwards [htend.eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs, abs_mul]
  have hqpw : 0 < |q| ^ ((n + m) + j) := pow_pos hqabs _
  have hA : |(q ^ (i * (n + m)))⁻¹| ≤ 1 := by
    rw [abs_inv, abs_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hq))
  have hlow : |C| * |q| ^ ((n + m) + j) / 2 ≤ |1 - C * q ^ ((n + m) + j)| := by
    have htri := abs_sub_abs_le_abs_sub (C * q ^ ((n + m) + j)) 1
    rw [abs_one, abs_mul, abs_pow, abs_sub_comm] at htri
    linarith [htri, hm]
  have h2pos : 0 < |C| * |q| ^ ((n + m) + j) / 2 := by positivity
  have hB : |(1 - C * q ^ ((n + m) + j))⁻¹| ≤ (2 / |C|) * (|q|⁻¹) ^ ((n + m) + j) := by
    rw [abs_inv]
    calc |1 - C * q ^ ((n + m) + j)|⁻¹ ≤ (|C| * |q| ^ ((n + m) + j) / 2)⁻¹ := inv_anti₀ h2pos hlow
      _ = (2 / |C|) * (|q|⁻¹) ^ ((n + m) + j) := by rw [inv_pow]; field_simp
  have hsplit : (|q|⁻¹) ^ ((n + m) + j) = (|q|⁻¹) ^ (n + j) * (|q|⁻¹) ^ m := by
    rw [← pow_add]; congr 1; omega
  calc |(q ^ (i * (n + m)))⁻¹| * |(1 - C * q ^ ((n + m) + j))⁻¹|
      ≤ 1 * ((2 / |C|) * (|q|⁻¹) ^ ((n + m) + j)) := mul_le_mul hA hB (abs_nonneg _) (by norm_num)
    _ = ((2 / |C|) * (|q|⁻¹) ^ (n + j)) * (|q|⁻¹) ^ m := by rw [one_mul, hsplit]; ring

/-- Each `Iₘ` (here `M` general) as a finite double sum over subsets `t ⊆ [1,n−1]` and poles
`j ∈ [1,n]`, via `ItermG_prod_form` + `partial_fraction` (Piece I, general) + `DtermG_expand`. -/
lemma ItermG_triple (hq : 1 < |q|) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    ItermG q C n M
      = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ t, (-q ^ k)) * muWG q n j
            * (((q ^ M)⁻¹) ^ t.card * (1 - C * q ^ (M + j))⁻¹) := by
  have hpm : ∀ a : ℕ, C * q ^ M * q ^ a = C * q ^ (M + a) := by
    intro a; rw [pow_add]; ring
  have hCprod : ∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ ((k : ℤ) + M))⁻¹
      = ∑ j ∈ Finset.Icc 1 n, muWG q n j * (1 - C * q ^ (M + j))⁻¹ := by
    have hconv : ∀ k : ℕ, (1 : ℝ) - C * q ^ ((k : ℤ) + M) = 1 - C * q ^ M * q ^ k := by
      intro k
      have he : ((k : ℤ) + M) = ((k + M : ℕ) : ℤ) := by push_cast; ring
      rw [he, zpow_natCast, pow_add]; ring
    have hx : ∀ k, 1 ≤ k → k ≤ n → 1 - C * q ^ M * q ^ k ≠ 0 := by
      intro k hk1 _
      rw [hpm k]
      obtain ⟨h', hh'⟩ : ∃ h', M + k = h' + 1 := ⟨M + k - 1, by omega⟩
      rw [hh']; exact one_sub_ne hCn h'
    have hprodeq : ∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ ((k : ℤ) + M))⁻¹
        = (∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ M * q ^ k))⁻¹ := by
      simp only [hconv, Finset.prod_inv_distrib]
    rw [hprodeq, partial_fraction_abs q hq n hn (C * q ^ M) hx]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpm j]
    rfl
  rw [ItermG_prod_form n M hn, hCprod, DtermG_expand hq n M]
  rw [Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- **The pull-out**: `EtermG n` as a finite double sum of `StailG`'s. -/
lemma EtermG_eq_StailG (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-q ^ k)) * muWG q n j * StailG q C t.card j n := by
  have hStail : ∀ (t : Finset ℕ) (j : ℕ),
      (fun m : ℕ => (∏ k ∈ t, (-q ^ k)) * muWG q n j
          * (((q ^ (n + m))⁻¹) ^ t.card * (1 - C * q ^ ((n + m) + j))⁻¹))
        = (fun m : ℕ => (∏ k ∈ t, (-q ^ k)) * muWG q n j
          * ((q ^ (t.card * (n + m)))⁻¹ * (1 - C * q ^ ((n + m) + j))⁻¹)) := by
    intro t j; funext m
    rw [inv_pow, ← pow_mul, mul_comm (n + m) t.card]
  have hsum : ∀ (t : Finset ℕ) (j : ℕ), Summable (fun m : ℕ =>
      (∏ k ∈ t, (-q ^ k)) * muWG q n j
        * (((q ^ (n + m))⁻¹) ^ t.card * (1 - C * q ^ ((n + m) + j))⁻¹)) := by
    intro t j
    rw [hStail t j]
    exact ((StailG_summable hq hC n t.card j).mul_left _)
  rw [EtermG, tsum_congr (fun m => ItermG_triple hq hCn hn (n + m)), tsum_neg]
  congr 1
  rw [Summable.tsum_finsetSum (fun t _ => summable_sum (fun j _ => hsum t j))]
  apply Finset.sum_congr rfl; intro t _
  rw [Summable.tsum_finsetSum (fun j _ => hsum t j)]
  apply Finset.sum_congr rfl; intro j _
  rw [hStail t j, tsum_mul_left]
  congr 1

/-- The explicit **rational correction** `Aₙ` of the residue identity `Eₙ = −pFirst·z + Aₙ`. -/
noncomputable def AcorrG (q C : ℝ) (n : ℕ) : ℝ :=
  -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
    (∏ k ∈ t, (-q ^ k)) * muWG q n j
      * (q ^ (t.card * j) * (RratG q C t.card - headSG q C t.card j n))

/-- **The residue identity** (contour-free, first form): `Eₙ = −pFirstG n · z + AcorrG n`. The general
`(q, C)` analog of `Eterm_eq_pFirst` (Borwein Lemma 1). -/
theorem EtermG_eq_pFirstG (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n = -pFirstG q C n * zG q C + AcorrG q C n := by
  have key : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∀ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-q ^ k)) * muWG q n j * StailG q C t.card j n
        = ((∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * C ^ t.card)) * zG q C
          + (∏ k ∈ t, (-q ^ k)) * muWG q n j
              * (q ^ (t.card * j) * (RratG q C t.card - headSG q C t.card j n)) := by
    intro t _ j _
    rw [StailG_collapse hq hC t.card j n (by omega), TserG_collapse hq hC hCn]
    ring
  have hzcoef : ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * C ^ t.card) = pFirstG q C n := by
    rw [pFirstG_powerset n]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hpt : ∏ k ∈ t, (-C * q ^ k) = C ^ t.card * ∏ k ∈ t, (-q ^ k) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun k _ => by ring)
    have hqp : ((q ^ j) ^ t.card : ℝ) = q ^ (t.card * j) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpt, hqp]; ring
  rw [EtermG_eq_StailG hq hC hCn hn,
    Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun j hj => key t ht j hj))]
  simp_rw [Finset.sum_add_distrib]
  rw [neg_add, AcorrG]
  congr 1
  rw [← hzcoef, neg_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_mul]

/-- **The residue identity with the `pValG` denominator**: `Eₙ = −pValG n · z + AcorrG n`, for real
`q > 1` and non-degenerate `C ≠ 0`. The general `(q, C)` analog of `Eterm_eq_pVal` (Borwein Lemma 1
with the Gaussian-binomial denominator). This is the full parametric residue identity. -/
theorem EtermG_eq_pValG (hq : 1 < |q|) (hC : C ≠ 0) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n = -pValG q C n * zG q C + AcorrG q C n := by
  rw [EtermG_eq_pFirstG hq hC hCn hn, pFirstG_eq_pValG hq C hn]

/- ### Denominator-exposing closed forms (toward the general Lemma-3 numerator integrality).

`AcorrG`'s denominators come from `muWG`, `RratG`, `headSG`. Exposing them as the products
`∏_{l≠j}(q^j − q^l)`, `q^l − 1`, and `β − α·q^{m'+1}` is the entry point to showing `β^{2n}·Wₙ·AcorrG`
is an integer (Borwein Lemma 3). These generalize `muW_closed`/`Rrat_closed`/`headS_clear`. -/

/-- `q^j − q^l ≠ 0` for `j ≠ l` (q-powers distinct since `q > 1`). -/
lemma qpowG_sub_ne (hq : 1 < q) {j l : ℕ} (hlj : l ≠ j) : (q ^ j - q ^ l : ℝ) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  apply hlj
  rcases Nat.lt_trichotomy l j with hlt | heq | hgt
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_right₀ hq hlt))
  · exact heq
  · exact absurd h (ne_of_lt (pow_lt_pow_right₀ hq hgt))

/-- **Denominator-exposing closed form** of the q-Lagrange weight:
`μ_j = (q^j)^{|erase j|}·(∏_{l≠j}(q^j − q^l))⁻¹`. -/
lemma muWG_closed (hq : 1 < q) (n j : ℕ) :
    muWG q n j = (q ^ j) ^ ((Finset.Icc 1 n).erase j).card
      * (∏ l ∈ (Finset.Icc 1 n).erase j, (q ^ j - q ^ l))⁻¹ := by
  have hqpos : 0 < q := by linarith
  rw [muWG]
  have hfac : ∀ l ∈ (Finset.Icc 1 n).erase j,
      (1 - q ^ l / q ^ j)⁻¹ = q ^ j * (q ^ j - q ^ l)⁻¹ := by
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hjne : (q ^ j : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hqpos)
    have hsub : (q ^ j - q ^ l : ℝ) ≠ 0 := qpowG_sub_ne hq hlj
    rw [show (1 - q ^ l / q ^ j : ℝ) = (q ^ j - q ^ l) / q ^ j from by field_simp,
      inv_div, div_eq_mul_inv]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    ← Finset.prod_inv_distrib]

/-- **Closed form of the rational correction** `RratG i = ∑_{l=1}^i C^{i-l}/(q^l − 1)`, exposing the
denominators `(q^l − 1)` and the `C`-powers. -/
lemma RratG_closed (_hq : 1 < |q|) (i : ℕ) :
    RratG q C i = ∑ l ∈ Finset.Icc 1 i, C ^ (i - l) / (q ^ l - 1) := by
  induction i with
  | zero => simp [RratG]
  | succ i ih =>
    rw [show RratG q C (i + 1) = 1 / (q ^ (i + 1) - 1) + C * RratG q C i from rfl, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1), Nat.sub_self, pow_zero, Finset.mul_sum,
      add_comm (1 / (q ^ (i + 1) - 1))]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_Icc] at hl
    rw [show (i + 1) - l = (i - l) + 1 from by omega, pow_succ]
    ring

/-- **`headSG` with denominators exposed**: with `C = α/β`, each factor `(1 − C·q^{m'+1})⁻¹` clears to
`β·(β − α·q^{m'+1})⁻¹`, surfacing the integer denominators `β − α·q^{m'+1}` that `Wₙ`'s `∏(1−C·q^k)`
clears. -/
lemma headSG_clear (α β : ℝ) (hβ : β ≠ 0) (i j n : ℕ) :
    headSG q (α / β) i j n = ∑ m' ∈ Finset.range (n + j - 1),
      β * (q ^ (i * (m' + 1)))⁻¹ * (β - α * q ^ (m' + 1))⁻¹ := by
  rw [headSG]
  apply Finset.sum_congr rfl
  intro m' _
  have h : (1 - (α / β) * q ^ (m' + 1))⁻¹ = β * (β - α * q ^ (m' + 1))⁻¹ := by
    rw [show (1 - (α / β) * q ^ (m' + 1) : ℝ) = (β - α * q ^ (m' + 1)) / β from by
      field_simp, inv_div, div_eq_mul_inv]
  rw [h]; ring

/-- `1 − q^k ≠ 0` for `k ≥ 1` and `q > 1` (then `q^k > 1`). -/
lemma one_sub_qpowG_ne (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k) : (1 - q ^ k : ℝ) ≠ 0 := by
  have hgt : (1 : ℝ) < q ^ k := by
    calc (1 : ℝ) < q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := pow_le_pow_right₀ (le_of_lt hq) hk
  linarith

/-- `1 − q^k ≠ 0` for `1 < |q|`, `k ≥ 1`: `|q^k| = |q|^k > 1`, so `q^k ≠ 1` (both signs of `q`). -/
lemma one_sub_qpowG_ne_abs (hq : 1 < |q|) {k : ℕ} (hk : 1 ≤ k) : (1 - q ^ k : ℝ) ≠ 0 := by
  intro h
  have hqk : q ^ k = 1 := by linarith
  have hgt : (1 : ℝ) < |q| ^ k := by
    calc (1 : ℝ) < |q| := hq
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ k := pow_le_pow_right₀ (le_of_lt hq) hk
  rw [← abs_pow, hqk, abs_one] at hgt
  exact lt_irrefl 1 hgt

/-- **`Wₙ ≠ 0`** for `q > 1`, non-degenerate `C`, `n ≥ 1`: a nonzero factorial times two products of
nonzero factors. (The `b_n ≠ 0` ingredient for the final approximant assembly.) -/
lemma WtermG_ne_zero (hq : 1 < q) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    WtermG q C n ≠ 0 := by
  rw [WtermG]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast Nat.factorial_ne_zero _
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    obtain ⟨h', hh'⟩ : ∃ h', k = h' + 1 := ⟨k - 1, by omega⟩
    rw [hh']
    exact one_sub_ne hCn h'
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    exact one_sub_qpowG_ne hq (by omega)

/-- **`Wₙ ≠ 0`, both signs of base** (`1 < |q|`). The negative-base analog of `WtermG_ne_zero`. -/
lemma WtermG_ne_zero_abs (hq : 1 < |q|) (hCn : ∀ h : ℕ, C * q ^ (h + 1) ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    WtermG q C n ≠ 0 := by
  rw [WtermG]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast Nat.factorial_ne_zero _
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    obtain ⟨h', hh'⟩ : ∃ h', k = h' + 1 := ⟨k - 1, by omega⟩
    rw [hh']
    exact one_sub_ne hCn h'
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    exact one_sub_qpowG_ne_abs hq (by omega)

/-- **`RratG` denominators clear to an integer**: for integer `q ≥ 2` and `C = α/β`,
`β^i·(∏_{l=1}^i (q^l−1))·R_i(α/β,q) ∈ ℤ`. The `C`-powers clear under `β^i`; the `(q^l−1)`
denominators clear because each summand keeps the complementary product `∏_{l'≠l}(q^{l'}−1)`. A
clearing brick toward the general Lemma-3 numerator integrality (`AcorrG`'s `RratG`-part). -/
lemma RratG_int (q α β : ℤ) (hq : 2 ≤ q) (hβ : β ≠ 0) (i : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (β : ℝ) ^ i * (∏ l ∈ Finset.Icc 1 i, ((q : ℝ) ^ l - 1))
        * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) i := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by rw [abs_of_pos (by linarith : (0 : ℝ) < (q : ℝ))]; exact hq1
  have hβr : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  refine ⟨∑ l ∈ Finset.Icc 1 i,
      β ^ l * α ^ (i - l) * ∏ l' ∈ (Finset.Icc 1 i).erase l, (q ^ l' - 1), ?_⟩
  rw [RratG_closed hq1abs, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_Icc] at hl
  have hql : (q : ℝ) ^ l - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < (q : ℝ) ^ l := by
      calc (1 : ℝ) < (q : ℝ) := hq1
        _ = (q : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℝ) ^ l := pow_le_pow_right₀ (le_of_lt hq1) hl.1
    linarith
  have hβsplit : (β : ℝ) ^ i = (β : ℝ) ^ l * (β : ℝ) ^ (i - l) := by
    rw [← pow_add]; congr 1; omega
  push_cast
  rw [← Finset.mul_prod_erase (Finset.Icc 1 i) (fun l' => ((q : ℝ) ^ l' - 1))
      (Finset.mem_Icc.mpr hl), div_pow, hβsplit]
  field_simp

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/GeneralLemma3.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Borwein Lemma 3 (numerator integrality) — general `(q, C)` engine

Ports the `q = 2, C = 8/3` Lemma-3 assembly (`Lemma3.lean`) to general integer `q ≥ 2` and rational
`C = α/β`. The target is `AcorrG_int`: `∃ a : ℤ, (a : ℝ) = −(β^{2n}·Wₙ(C,q)·AcorrG n)`, i.e. the
rational correction of the residue identity clears to an integer once scaled by `β^{2n}·Wₙ`.

The route mirrors the `q = 2` one exactly (it is ~mechanical, per the lap-6 heuristic):
1. **reorg** `AcorrG n` into a `muW`-free Rrat-part (Gaussian binomials via q-Lagrange) plus a headS-part
   `∑_{h=1}^n u_h·N_h` with `N_h = NhG (q) n h` the q-Lagrange combination;
2. **clear** each part by `β^{2n}·Wₙ` = `WIG` (an integer): the Rrat-part via `RratG_int` + `borwein_div`,
   the headS-part via `uClearIntG` (clears `u_h` by `CPintG`'s `(β−α·q^h)` factor) and `NhG_int`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

/- ## Section 1: reorganizing `AcorrG`'s headS-part (pure real-`q` algebra) -/

/-- `headSG` with the inner range sum reindexed to `Icc 1 (n+j−1)` (set `h = m'+1`). -/
lemma headSG_Icc (q C : ℝ) (i j n : ℕ) :
    headSG q C i j n = ∑ h ∈ Finset.Icc 1 (n + j - 1), (q ^ (i * h))⁻¹ * (1 - C * q ^ h)⁻¹ := by
  rw [headSG, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro m' _
  rw [Nat.add_comm 1 m']

/-- **Subset-product collapse** (signed, with a scalar `w`): `∑_{t⊆[1,m]} (∏_{k∈t}-q^k)·w^{|t|}
= ∏_{k=1}^m (1 - q^k·w)`. The engine of the headS reorganization. -/
lemma subset_prod_localG (q w : ℝ) (m : ℕ) :
    ∑ t ∈ (Finset.Icc 1 m).powerset, (∏ k ∈ t, (-q ^ k)) * w ^ t.card
      = ∏ k ∈ Finset.Icc 1 m, (1 - q ^ k * w) := by
  have hf : ∀ k, (1 : ℝ) - q ^ k * w = 1 + (-q ^ k) * w := by intro k; ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- `q^{t·j}·(q^{t·h})⁻¹ = (q^{j−h})^t` (mixing nat powers and a zpow base). -/
lemma wpowG {q : ℝ} (hq0 : q ≠ 0) (j h t : ℕ) :
    (q ^ (t * j) : ℝ) * (q ^ (t * h))⁻¹ = (q ^ ((j : ℤ) - h)) ^ t := by
  rw [← zpow_natCast (q ^ ((j : ℤ) - h)) t, ← zpow_mul, ← zpow_natCast q (t * j),
    ← zpow_natCast q (t * h), ← zpow_neg, ← zpow_add₀ hq0]
  congr 1
  push_cast; ring

/-- **Per-`j` headS reorganization.** Summing the subset `t ⊆ [1,n−1]` first collapses the headS-part
into a single product `∏_{k=1}^{n−1}(1−q^{k+j−h})` over the head index `h`. -/
lemma headPartG_inner {q : ℝ} (C : ℝ) (hq0 : q ≠ 0) (n j : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-q ^ k)) * (q ^ (t.card * j) * headSG q C t.card j n)
      = ∑ h ∈ Finset.Icc 1 (n + j - 1),
        (1 - C * q ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  have hstep : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset,
      (∏ k ∈ t, (-q ^ k)) * (q ^ (t.card * j) * headSG q C t.card j n)
        = ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - C * q ^ h)⁻¹ * ((∏ k ∈ t, (-q ^ k)) * (q ^ ((j : ℤ) - h)) ^ t.card) := by
    intro t _
    rw [headSG_Icc, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← wpowG hq0 j h t.card]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hprod : (∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ k * q ^ ((j : ℤ) - h)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [← zpow_natCast q k, ← zpow_add₀ hq0]
    congr 2
    ring
  rw [hprod, ← subset_prod_localG q (q ^ ((j : ℤ) - h)) (n - 1), Finset.mul_sum]

/-- The full headS-part of `AcorrG`, reorganized: pull `muWG n j` out and apply `headPartG_inner`. -/
lemma AccHG_reorg {q : ℝ} (C : ℝ) (hq0 : q ≠ 0) (n : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * headSG q C t.card j n)
      = ∑ j ∈ Finset.Icc 1 n, muWG q n j *
          ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - C * q ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← headPartG_inner C hq0 n j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **`AcorrG` reorganized** into its Rrat-part (first sum) and the reorganized headS-part (second
sum). -/
lemma AcorrG_reorg {q : ℝ} (C : ℝ) (hq0 : q ≠ 0) (n : ℕ) :
    AcorrG q C n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                  (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * RratG q C t.card))
              + ∑ j ∈ Finset.Icc 1 n, muWG q n j *
                  ∑ h ∈ Finset.Icc 1 (n + j - 1),
                    (1 - C * q ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  have key : (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * RratG q C t.card))
              - (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-q ^ k)) * muWG q n j * (q ^ (t.card * j) * headSG q C t.card j n))
            = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-q ^ k)) * muWG q n j
                  * (q ^ (t.card * j) * (RratG q C t.card - headSG q C t.card j n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro t _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [AcorrG, ← key, AccHG_reorg C hq0]
  abel

/- ## Section 2: head truncation + q-Lagrange clearing → `AcorrG_clean` -/

/-- **Rrat-part via q-Lagrange** (integer `q ≥ 2`). Each `t`-term's `j`-sum
`∑_j μ_j (q^j)^{|t|}` is the Gaussian binomial `q^{|t|}·[n+|t|−1,n−1]_q` (`qLagG`, valid as
`|t| ≤ n−1 < n`), eliminating the Vandermonde `muWG` denominators. -/
lemma RratPartG_qLag {q : ℤ} (hq : 2 ≤ |q|) (C : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-(q : ℝ) ^ k)) * muWG (q : ℝ) n j
          * ((q : ℝ) ^ (t.card * j) * RratG (q : ℝ) C t.card)
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) C t.card
            * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1
    omega
  have hpull : ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-(q : ℝ) ^ k)) * muWG (q : ℝ) n j
          * ((q : ℝ) ^ (t.card * j) * RratG (q : ℝ) C t.card)
      = (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) C t.card
          * ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j * ((q : ℝ) ^ j) ^ t.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, Nat.mul_comm j t.card]; ring
  rw [hpull, qLagG_abs hq hn t.card hcard]

/-- **headS-part in `N_h` form** (integer `q`). After truncation (`head_truncate`) the (j,h)-sum swaps
and the inner `j`-sum extends to `[1,n]` (added `j<h` terms vanish by `prod_vanishG`), exposing the
q-Lagrange combination `N_h = ∑_j μ_j ∏_{k=1}^{n−1}(1−q^{k+j−h})`. -/
lemma headSPartG_NhForm {q : ℤ} (C : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j *
        ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - C * (q : ℝ) ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 n, (1 - C * (q : ℝ) ^ h)⁻¹ *
          ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
            * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  have h1 : ∀ j ∈ Finset.Icc 1 n,
      muWG (q : ℝ) n j * ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - C * (q : ℝ) ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))
        = ∑ h ∈ Finset.Icc 1 j,
            muWG (q : ℝ) n j * ((1 - C * (q : ℝ) ^ h)⁻¹
              * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) := by
    intro j _
    rw [head_truncate (q : ℝ) (fun h => (1 - C * (q : ℝ) ^ h)⁻¹) n j hn, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (s := Finset.Icc 1 n) (t := fun j => Finset.Icc 1 j)
        (t' := Finset.Icc 1 n) (s' := fun h => Finset.Icc h n)
        (by intro j h
            show (j ∈ Finset.Icc 1 n ∧ h ∈ Finset.Icc 1 j)
              ↔ (j ∈ Finset.Icc h n ∧ h ∈ Finset.Icc 1 n)
            simp only [Finset.mem_Icc]; omega)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega : (1 : ℕ) ≤ h))]
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j hj hjh
    rw [Finset.mem_Icc] at hj hjh
    have : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) = 0 :=
      prod_vanishG (by omega) (by omega) hh.2
    rw [this]; ring

/-- **`AcorrG` in clean form** (integer `q ≥ 2`, `C` real): the Rrat-part is now `muWG`-free
(Gaussian binomials), and the headS-part is `∑_{h=1}^n u_h·N_h` with `N_h = NhG q n h`. This is the
structural target of the elementary Lemma-3 route, ported to general `(q, C)`. -/
theorem AcorrG_clean {q : ℤ} (hq : 2 ≤ |q|) (C : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    AcorrG (q : ℝ) C n
      = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) C t.card
              * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)))
        + ∑ h ∈ Finset.Icc 1 n, (1 - C * (q : ℝ) ^ h)⁻¹ *
            ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
              * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have hqz : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; exact absurd hq (by norm_num)
    exact_mod_cast hqz
  rw [AcorrG_reorg C hq0 n, RratPartG_qLag hq C n hn, headSPartG_NhForm C n hn]

/- ## Section 3: the integer clearing factor `β^{2n}·Wₙ = WIG` and the numerator integrality -/

/-- The cleared **integer** form of `β^{2n}·Wₙ(C,q)`, `C = α/β`: since `β^n·∏(1−C·qᵏ) = CPintG` and
`∏(1−qᵏ) = QPintG`, this is `β^n·(n−2)!·CPintG·QPintG ∈ ℤ`. (Generalizes `WI`, the `q=2,C=8/3` case.) -/
def WIG (q α β : ℤ) (n : ℕ) : ℤ :=
  β ^ n * (Nat.factorial (n - 2)) * CPintG q α β n * QPintG q n

/-- `(WIG q α β n : ℝ) = β^{2n}·Wₙ(α/β,q)`: the clearing factor is a machine-checked integer. -/
lemma WIG_cast (q α β : ℤ) (hβ : β ≠ 0) (n : ℕ) :
    (WIG q α β n : ℝ) = (β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  rw [WIG, WtermG]
  push_cast
  rw [CPintG_cast q α β hβ, QPintG_cast q]
  have hb : (β : ℝ) ^ (2 * n) = (β : ℝ) ^ n * (β : ℝ) ^ n := by rw [← pow_add]; congr 1; omega
  rw [hb]; ring

/-- `(q^l − 1)` divides `QPintG q n` for `1 ≤ l ≤ n−1` (Borwein's note, via `borwein_div`). -/
lemma QPintG_dvd {q : ℤ} {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n - 1) :
    (q ^ l - 1) ∣ QPintG q n := by
  have h := borwein_div q n l hl (by omega)
  rw [QPintG]
  have hsign : (q ^ l - 1) = -(1 - q ^ l) := by ring
  rw [hsign]
  exact h.neg_left

/-- The integer witness for `β^{2n}·Wₙ·(C^{i−l}/(q^l−1))`: clears `α^{i−l}` by `β` and `q^l−1` by
`QPintG` (via `QPintG_dvd`). -/
def RratTermIntG (q α β : ℤ) (n i l : ℕ) : ℤ :=
  α ^ (i - l) * β ^ (n - (i - l)) * (Nat.factorial (n - 2)) * CPintG q α β n * (QPintG q n / (q ^ l - 1))

/-- **Per-term Rrat clearing**: `(RratTermIntG q α β n i l : ℝ) = WIG · (C^{i−l}/(q^l−1))` for
`1 ≤ l ≤ i ≤ n−1`. -/
lemma RratTermIntG_cast {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) {n i l : ℕ}
    (hl1 : 1 ≤ l) (hli : l ≤ i) (hin : i ≤ n - 1) :
    (RratTermIntG q α β n i l : ℝ)
      = (WIG q α β n : ℝ) * (((α : ℝ) / (β : ℝ)) ^ (i - l) / ((q : ℝ) ^ l - 1)) := by
  obtain ⟨d, hd⟩ := QPintG_dvd (q := q) hl1 (by omega : l ≤ n - 1)
  -- `q^l ≠ 1` since `|q^l| = |q|^l ≥ |q| ≥ 2 > 1` (works for both signs of `q`).
  have hne : (q ^ l - 1 : ℤ) ≠ 0 := by
    have habs : (2 : ℤ) ≤ |q ^ l| := by
      rw [abs_pow]
      calc (2 : ℤ) ≤ |q| := hq
        _ = |q| ^ 1 := (pow_one _).symm
        _ ≤ |q| ^ l := pow_le_pow_right₀ (by linarith) hl1
    have hne1 : (q ^ l : ℤ) ≠ 1 := by intro h; rw [h] at habs; norm_num at habs
    exact sub_ne_zero.mpr hne1
  have hdiv : QPintG q n / (q ^ l - 1) = d := by rw [hd]; exact Int.mul_ediv_cancel_left d hne
  have hqR : ((q : ℝ) ^ l - 1) ≠ 0 := by
    have hq2 : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
    have hgt : (1 : ℝ) < |(q : ℝ)| ^ l := by
      calc (1 : ℝ) < 2 := by norm_num
        _ ≤ |(q : ℝ)| := hq2
        _ = |(q : ℝ)| ^ 1 := (pow_one _).symm
        _ ≤ |(q : ℝ)| ^ l := pow_le_pow_right₀ (by linarith) hl1
    intro h; rw [sub_eq_zero] at h
    have hone : |(q : ℝ) ^ l| = 1 := by rw [h]; norm_num
    rw [abs_pow] at hone; linarith
  have hQ : (QPintG q n : ℝ) = ((q : ℝ) ^ l - 1) * (d : ℝ) := by
    have h1 : (QPintG q n : ℝ) = (((q ^ l - 1) * d : ℤ) : ℝ) := by rw [← hd]
    rw [h1]; push_cast; ring
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hbsplit : (β : ℝ) ^ n = (β : ℝ) ^ (i - l) * (β : ℝ) ^ (n - (i - l)) := by
    rw [← pow_add]; congr 1; omega
  rw [RratTermIntG, hdiv, WIG]
  push_cast
  rw [hQ, hbsplit, div_pow]
  field_simp

/-- Per-`t` integer witness for the whole Rrat-part of `AcorrG_clean`. -/
def RratCleanTermIntG (q α β : ℤ) (n : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-q ^ k)) * (q ^ t.card * qBin q (n + t.card - 1) (n - 1))
    * (∑ l ∈ Finset.Icc 1 t.card, RratTermIntG q α β n t.card l)

/-- Each Rrat-part `t`-term, times `β^{2n}·Wₙ`, is the integer `RratCleanTermIntG`. -/
lemma RratCleanTermIntG_cast {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) {n : ℕ} {t : Finset ℕ}
    (ht : t ∈ (Finset.Icc 1 (n - 1)).powerset) :
    (RratCleanTermIntG q α β n t : ℝ) = (WIG q α β n : ℝ) *
      ((∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) t.card
        * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1))) := by
  have hcard : t.card ≤ n - 1 := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have hqr1 : (1 : ℝ) < |(q : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (by linarith : (1 : ℤ) < |q|)
  have e1 : ((∏ k ∈ t, (-q ^ k) : ℤ) : ℝ) = ∏ k ∈ t, (-(q : ℝ) ^ k) := by
    rw [Int.cast_prod]; apply Finset.prod_congr rfl; intro k _; push_cast; ring
  have e4 : ((∑ l ∈ Finset.Icc 1 t.card, RratTermIntG q α β n t.card l : ℤ) : ℝ)
      = (WIG q α β n : ℝ) * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) t.card := by
    rw [RratG_closed hqr1, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl; intro l hl; rw [Finset.mem_Icc] at hl
    exact RratTermIntG_cast hq hβ hl.1 hl.2 hcard
  have hqb : qBin ((q : ℤ) : ℝ) (n + t.card - 1) (n - 1)
      = ((qBin q (n + t.card - 1) (n - 1) : ℤ) : ℝ) :=
    qBin_map (Int.castRingHom ℝ) q (n + t.card - 1) (n - 1)
  have e3 : ((q ^ t.card * qBin q (n + t.card - 1) (n - 1) : ℤ) : ℝ)
      = (q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1) := by
    rw [hqb]; push_cast; ring
  rw [RratCleanTermIntG, Int.cast_mul, Int.cast_mul, e4, e1, e3]
  ring

/-- **Rrat-part integrality.** `β^{2n}·Wₙ · (Rrat-part of `AcorrG_clean`) ∈ ℤ`. -/
lemma WIG_mul_RratClean_int {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) (n : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (WIG q α β n : ℝ) * ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-(q : ℝ) ^ k)) * RratG (q : ℝ) ((α : ℝ) / (β : ℝ)) t.card
          * ((q : ℝ) ^ t.card * qBin (q : ℝ) (n + t.card - 1) (n - 1)) := by
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, RratCleanTermIntG q α β n t, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact RratCleanTermIntG_cast hq hβ ht

/-- `CPintG` with its `h`-th factor `(β − α·q^h)` removed (`h ∈ [1,n]`). -/
def CPdropG (q α β : ℤ) (n h : ℕ) : ℤ := ∏ k ∈ (Finset.Icc 1 n).erase h, (β - α * q ^ k)

/-- `(β − α·q^h)·CPdropG = CPintG` for `h ∈ [1,n]`. -/
lemma CPintG_factor {q α β : ℤ} {n h : ℕ} (hh : h ∈ Finset.Icc 1 n) :
    (β - α * q ^ h) * CPdropG q α β n h = CPintG q α β n :=
  Finset.mul_prod_erase (Finset.Icc 1 n) (fun k => β - α * q ^ k) hh

/-- The integer witness for `β^{2n}·Wₙ·u_h = β^{n+1}·(n−2)!·QPintG·CPdropG`. -/
def uClearIntG (q α β : ℤ) (n h : ℕ) : ℤ :=
  β ^ (n + 1) * (Nat.factorial (n - 2)) * QPintG q n * CPdropG q α β n h

/-- **`u_h` clearing**: `(uClearIntG q α β n h : ℝ) = β^{2n}·Wₙ·(1−C·q^h)⁻¹` for `1 ≤ h ≤ n`, where
`C = α/β` and `C·q^h ≠ 1` (so the `(β − α·q^h)` factor of `CPintG` clears the `u_h` denominator). -/
lemma uClearIntG_cast {q α β : ℤ} (hβ : β ≠ 0) {n h : ℕ} (hh1 : 1 ≤ h) (hhn : h ≤ n)
    (hCh : ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1) :
    (uClearIntG q α β n h : ℝ)
      = (WIG q α β n : ℝ) * (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)⁻¹ := by
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hmem : h ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hh1, hhn⟩
  have hfac : (β - α * q ^ h) * CPdropG q α β n h = CPintG q α β n := CPintG_factor hmem
  have hu0 : (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h) ≠ 0 := sub_ne_zero.mpr (Ne.symm hCh)
  have hne : ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) ≠ 0 := by
    have hb : ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h)
        = (β : ℝ) * (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h) := by field_simp
    rw [hb]; exact mul_ne_zero hβ0 hu0
  have hu : (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)⁻¹
      = (β : ℝ) / ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) := by
    rw [show (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)
          = ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) / (β : ℝ) from by field_simp, inv_div]
  have hCP : (CPintG q α β n : ℝ)
      = ((β : ℝ) - (α : ℝ) * (q : ℝ) ^ h) * (CPdropG q α β n h : ℝ) := by
    rw [← hfac]; push_cast; ring
  rw [uClearIntG, WIG]
  push_cast
  rw [hu, hCP]
  field_simp
  ring

/-- **headS-part integrality**, given integer witnesses `Nz h = N_h` and non-degeneracy `C·q^h ≠ 1`.
`β^{2n}·Wₙ·(headS-part) = ∑_h (β^{2n}·Wₙ·u_h)·N_h = ∑_h uClearIntG·Nz h ∈ ℤ`. -/
lemma WIG_mul_headS_int {q α β : ℤ} (hβ : β ≠ 0) (n : ℕ)
    (hCn : ∀ h, 1 ≤ h → h ≤ n → ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1)
    (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) :
    ∃ z : ℤ, (z : ℝ) = (WIG q α β n : ℝ) *
      ∑ h ∈ Finset.Icc 1 n, (1 - ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h)⁻¹ *
        ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  refine ⟨∑ h ∈ Finset.Icc 1 n, uClearIntG q α β n h * Nz h, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Int.cast_mul, uClearIntG_cast hβ hh.1 hh.2 (hCn h hh.1 hh.2), hNz h hh.1 hh.2]
  ring

/-- **Borwein Lemma 3 (numerator integrality), general `(q,C)`, conditional on `N_h ∈ ℤ`.** Combines
the Rrat-part (`WIG_mul_RratClean_int`) and headS-part (`WIG_mul_headS_int`) integralities via
`AcorrG_clean` and `WIG_cast`: `−β^{2n}·Wₙ·AcorrG n ∈ ℤ`. -/
lemma AcorrG_int_of_Nz {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (hCn : ∀ h, 1 ≤ h → h ≤ n → ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1)
    (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h))) :
    ∃ a : ℤ, (a : ℝ)
      = -((β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * AcorrG (q : ℝ) ((α : ℝ) / (β : ℝ)) n) := by
  obtain ⟨rInt, hr⟩ := WIG_mul_RratClean_int hq hβ n
  obtain ⟨hInt, hh⟩ := WIG_mul_headS_int hβ n hCn Nz hNz
  refine ⟨rInt - hInt, ?_⟩
  rw [← WIG_cast q α β hβ]
  push_cast
  rw [hr, hh, AcorrG_clean hq ((α : ℝ) / (β : ℝ)) n hn]
  ring

/-- Total integer witness function for `N_h` (zero off `[1,n]`), packaging `NhG_int`. -/
theorem NhG_integral {q : ℤ} (hq : 2 ≤ |q|) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Nz : ℕ → ℤ, ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muWG (q : ℝ) n j
          * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - (q : ℝ) ^ ((k : ℤ) + j - h)) := by
  choose Nz hNz using fun h (hh1 : 1 ≤ h) (hhn : h ≤ n) => NhG_int_abs hq n h hn hh1 hhn
  refine ⟨fun h => if H : 1 ≤ h ∧ h ≤ n then Nz h H.1 H.2 else 0, fun h hh1 hhn => ?_⟩
  show ((dite (1 ≤ h ∧ h ≤ n) (fun H => Nz h H.1 H.2) (fun _ => 0) : ℤ) : ℝ) = _
  rw [dif_pos (⟨hh1, hhn⟩ : 1 ≤ h ∧ h ≤ n)]
  have hspec := hNz h hh1 hhn
  rw [hspec, NhG]

/-- **Borwein Lemma 3 (numerator integrality), general `(q,C)` — MILESTONE.** For integer `q ≥ 2`,
`C = α/β` with `β ≠ 0` and `C·q^h ≠ 1` (`1 ≤ h ≤ n`), the rational correction `AcorrG n` of the
residue identity clears to an integer when scaled by `β^{2n}·Wₙ`: `∃ a : ℤ, (a:ℝ) = −β^{2n}·Wₙ·AcorrG n`.
The general analog of `numerator_integrality` (the `q=2,C=8/3` case), discharging the Lemma-3
sub-obligation of `borwein_approximants` for the `(q,C)` range. -/
theorem AcorrG_int {q α β : ℤ} (hq : 2 ≤ |q|) (hβ : β ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (hCn : ∀ h, 1 ≤ h → h ≤ n → ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ h ≠ 1) :
    ∃ a : ℤ, (a : ℝ)
      = -((β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * AcorrG (q : ℝ) ((α : ℝ) / (β : ℝ)) n) := by
  obtain ⟨Nz, hNz⟩ := NhG_integral hq n hn
  exact AcorrG_int_of_Nz hq hβ n hn hCn Nz hNz

/- ## Section 4: general Lemmas 1+2+3 assembled — the integer approximant identity

With the residue identity (Lemma 1, `EtermG_eq_pValG`), denominator integrality (Lemma 2,
`BdenG_cast`) and numerator integrality (Lemma 3, `AcorrG_int`) all general and machine-checked, the
cleared error `β^{2n}·Wₙ·Eₙ` is exactly `bₙ·z − aₙ` for integer sequences `aₙ, bₙ` (`bₙ = −BdenG`,
`aₙ = −β^{2n}·Wₙ·AcorrG`). This is the general analog of `borwein_integrality` (`Lemma3.lean`). The only
sub-obligations of `borwein_approximants` still open are Lemma 4 (`bₙ·z − aₙ → 0`) and Lemma 5
(`bₙ·z − aₙ ≠ 0`), both requiring a magnitude condition `|C| ≥ 2`. -/

/-- **Borwein Lemmas 1+2+3, assembled, general `(q,C)`.** For integer `q ≥ 2` and `C = α/β` with
`α, β ≠ 0` and `C·q^h ≠ 1`, there are integer sequences `aₙ, bₙ` with
`bₙ·z − aₙ = β^{2n}·Wₙ(C,q)·Eₙ(C,q)` for all `n ≥ 1`, where `z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹`. The cleared
error of the q-Padé approximants is an explicit integer combination of `z`. (General analog of
`borwein_integrality`.) -/
theorem borwein_integralityG {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hCn : ∀ h : ℕ, ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1) ≠ 1) :
    ∃ a b : ℕ → ℤ, ∀ n, 1 ≤ n →
      (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n
        = (β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n := by
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (by linarith : (1 : ℤ) < |q|)
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hα0 : (α : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hα
  have hC0 : ((α : ℝ) / (β : ℝ)) ≠ 0 := div_ne_zero hα0 hβ0
  -- Lemma 3 gives a per-`n` integer numerator `aₙ = −β^{2n}·Wₙ·AcorrG n`.
  have key : ∀ n, 1 ≤ n → ∃ a : ℤ, (a : ℝ)
      = -((β : ℝ) ^ (2 * n) * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) n
            * AcorrG (q : ℝ) ((α : ℝ) / (β : ℝ)) n) := by
    intro n hn
    refine AcorrG_int hq hβ n hn ?_
    intro h hh1 _
    have hh := hCn (h - 1)
    rwa [Nat.sub_add_cancel hh1] at hh
  choose a ha using key
  refine ⟨fun n => if h : 1 ≤ n then a n h else 0, fun n => -BdenG q α β n, fun n hn => ?_⟩
  simp only [dif_pos hn]
  have hE := EtermG_eq_pValG hq1abs hC0 hCn hn
  have hB := BdenG_cast q α β hβ hn
  have hA := ha n hn
  rw [hE]
  push_cast
  rw [hB, hA]
  ring

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/GeneralError.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Borwein Lemma 5 (non-vanishing) and the summable majorant — general `(q, C)`

Ports the `q = 2, C = 8/3` error-sign machinery (`Approximants.lean`, Lemma 5) to general real `q ≥ 2`
and `C > 2` (Borwein's shifted magnitude regime; `cB = 8/3 > 2` is the concrete instance). Every term
`ItermG q C n m` (`m ≥ n ≥ 1`) has the same nonzero sign `(-1)^{n-1}`, so the error
`EtermG q C n = ∑_{j} ItermG q C n (n+j)` cannot vanish.

The summable geometric majorant `|ItermG q C n (n+j)| ≤ (q⁻¹)^j` (also used for `EtermG_summable`,
the Lemma-4 convergence half) is proved here too.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators

variable {q C : ℝ}

/-- `q^a ≥ 2` for `a ≥ 1` when `q ≥ 2` (zpow version). -/
lemma qzpow_ge_two (hq : 2 ≤ q) {a : ℤ} (ha : 1 ≤ a) : (2 : ℝ) ≤ q ^ a := by
  have hq1 : (1 : ℝ) < q := by linarith
  calc (2 : ℝ) ≤ q := hq
    _ = q ^ (1 : ℤ) := (zpow_one q).symm
    _ ≤ q ^ a := zpow_le_zpow_right₀ (le_of_lt hq1) ha

/-- **Magnitude bound** (sign-independent): for `|C| > 2`, `q ≥ 2`, `a ≥ 1`, `|(1 − C·q^a)⁻¹| ≤ q^{-a}`.
Reverse triangle: `|1 − C·q^a| ≥ |C|·q^a − 1 ≥ 2q^a − 1 ≥ q^a`. -/
lemma inv_cqpowG_le (hq : 2 ≤ q) (hC : 2 < |C|) {a : ℤ} (ha : 1 ≤ a) :
    |(1 - C * q ^ a)⁻¹| ≤ q ^ (-a) := by
  have hqa : (2 : ℝ) ≤ q ^ a := qzpow_ge_two hq ha
  have hqpos : (0 : ℝ) < q ^ a := zpow_pos (by linarith) a
  have hge : q ^ a ≤ |1 - C * q ^ a| := by
    have h1 : |C * q ^ a| - |(1 : ℝ)| ≤ |C * q ^ a - 1| := abs_sub_abs_le_abs_sub _ _
    have h2 : |C * q ^ a| = |C| * q ^ a := by rw [abs_mul, abs_of_pos hqpos]
    have h3 : |C * q ^ a - 1| = |1 - C * q ^ a| := abs_sub_comm _ _
    rw [h2, abs_one, h3] at h1
    nlinarith [h1, hqa, hC, hqpos, mul_pos (show (0 : ℝ) < |C| - 2 by linarith) hqpos]
  rw [abs_inv, zpow_neg]
  exact inv_anti₀ hqpos hge

/- ### Negative-BASE (`q ≤ -2`, i.e. `2 ≤ |q|`) magnitude bounds — Lemma 4 convergence half.

For negative base the powers `q^a` alternate sign, so the bounds must be stated in terms of `|q|`.
The reverse-triangle estimate `|1 − C·q^a| ≥ |C|·|q|^a − 1 ≥ |q|^a` (using `|C| > 2`) survives unchanged,
and although the cross factor `|1 − q^{k−m}|` now costs `≤ 2` (vs `≤ 1` for positive `q`), the extra
`2`'s are harmless: `2·|q|⁻¹ ≤ 1` since `|q| ≥ 2`, so the geometric majorant `(|q|⁻¹)^j` is recovered
exactly. These feed `EtermG_summable_abs`, the negative-base analog of `EtermG_summable`. -/

/-- **Cross-factor positivity** (negative base): for `2 ≤ |q|` and `k < m`, the factor
`1 − q^{k−m} > 0`, because `|q^{k−m}| = |q|^{k−m} ≤ |q|⁻¹ ≤ 1/2 < 1` (the exponent `k−m ≤ −1`).
This holds for BOTH signs of `q` and is the reason the cross product never affects the sign of
`ItermG` — a key brick for the negative-base non-vanishing (Lemma 5) sign analysis. -/
lemma one_sub_qzpow_pos (hq : 2 ≤ |q|) {k m : ℕ} (hkm : k < m) :
    0 < 1 - q ^ ((k : ℤ) - m) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hlt : q ^ ((k : ℤ) - m) < 1 := by
    have h1 : |q ^ ((k : ℤ) - m)| ≤ |q| ^ (-1 : ℤ) := by
      rw [abs_zpow]; exact zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
    have h2 : |q| ^ (-1 : ℤ) < 1 := by
      rw [zpow_neg, zpow_one]; exact inv_lt_one_of_one_lt₀ hqabs1
    calc q ^ ((k : ℤ) - m) ≤ |q ^ ((k : ℤ) - m)| := le_abs_self _
      _ ≤ |q| ^ (-1 : ℤ) := h1
      _ < 1 := h2
  linarith

/-- **Magnitude bound, both signs of `q`**: for `2 ≤ |q|`, `2 < |C|`, `a ≥ 1`,
`|(1 − C·q^a)⁻¹| ≤ |q|^{-a}`. -/
lemma inv_cqpow_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {a : ℤ} (ha : 1 ≤ a) :
    |(1 - C * q ^ a)⁻¹| ≤ |q| ^ (-a) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqa : (2 : ℝ) ≤ |q| ^ a := by
    calc (2 : ℝ) ≤ |q| := hq
      _ = |q| ^ (1 : ℤ) := (zpow_one _).symm
      _ ≤ |q| ^ a := zpow_le_zpow_right₀ (le_of_lt hqabs1) ha
  have hqpos : (0 : ℝ) < |q| ^ a := zpow_pos (by linarith) a
  have hge : |q| ^ a ≤ |1 - C * q ^ a| := by
    have h1 : |C * q ^ a| - |(1 : ℝ)| ≤ |C * q ^ a - 1| := abs_sub_abs_le_abs_sub _ _
    have h2 : |C * q ^ a| = |C| * |q| ^ a := by rw [abs_mul, abs_zpow]
    have h3 : |C * q ^ a - 1| = |1 - C * q ^ a| := abs_sub_comm _ _
    rw [h2, abs_one, h3] at h1
    nlinarith [h1, hqa, hC, hqpos, mul_pos (show (0 : ℝ) < |C| - 2 by linarith) hqpos]
  rw [abs_inv, zpow_neg]
  exact inv_anti₀ hqpos hge

/-- Each product factor has `|·| ≤ 2·|q|⁻¹` for `1 ≤ k < m`, `2 ≤ |q|`, `2 < |C|`. The cross factor
`|1 − q^{k−m}| ≤ 1 + |q|^{k−m} ≤ 2` and the leading inverse `≤ |q|^{−(k+m)} ≤ |q|⁻¹`. -/
lemma factor_bound_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ 2 * |q|⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  rw [abs_mul]
  have hle1 : |q| ^ ((k : ℤ) - m) ≤ 1 := by
    calc |q| ^ ((k : ℤ) - m) ≤ |q| ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
      _ = 1 := by norm_num
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 2 := by
    calc |1 - q ^ ((k : ℤ) - m)| = |(1 : ℝ) + -(q ^ ((k : ℤ) - m))| := by rw [sub_eq_add_neg]
      _ ≤ |(1 : ℝ)| + |-(q ^ ((k : ℤ) - m))| := abs_add_le _ _
      _ = 1 + |q| ^ ((k : ℤ) - m) := by rw [abs_one, abs_neg, abs_zpow]
      _ ≤ 2 := by linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ |q| ^ (-((k : ℤ) + m)) := inv_cqpow_le_abs hq hC (by omega)
  have h3 : |q| ^ (-((k : ℤ) + m)) ≤ |q|⁻¹ := by
    calc |q| ^ (-((k : ℤ) + m)) ≤ |q| ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
      _ = |q|⁻¹ := by rw [zpow_neg, zpow_one]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 2 * |q| ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ ≤ 2 * |q|⁻¹ := mul_le_mul_of_nonneg_left h3 (by norm_num)

/-- Crude per-term bound (negative base): `|ItermG q C n m| ≤ |q|^{-(m+n)}·(2|q|⁻¹)^{n−1}`. -/
lemma ItermG_abs_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ |q| ^ (-((m : ℤ) + n)) * (2 * |q|⁻¹) ^ (n - 1) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  rw [ItermG, abs_mul, abs_neg]
  have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ |q| ^ (-((m : ℤ) + n)) := inv_cqpow_le_abs hq hC (by omega)
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ (2 * |q|⁻¹) ^ (n - 1) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 (n - 1), |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ _k ∈ Finset.Icc 1 (n - 1), (2 * |q|⁻¹) :=
          Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => by
            rw [Finset.mem_Icc] at hk
            exact factor_bound_abs hq hC hk.1 (by omega))
      _ = (2 * |q|⁻¹) ^ (n - 1) := by rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hbnn : (0 : ℝ) ≤ |q| ^ (-((m : ℤ) + n)) := le_of_lt (zpow_pos (by linarith) _)
  exact mul_le_mul hlead hprod (abs_nonneg _) hbnn

/-- The reindexed term `ItermG q C n (n+j)` is bounded by `(|q|⁻¹)^j` (negative base). The `(2|q|⁻¹)^{n−1}`
constant is `≤ 1` because `2|q|⁻¹ ≤ 1`, so the geometric majorant is recovered exactly. -/
lemma ItermG_shift_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    |ItermG q C n (n + j)| ≤ (|q|⁻¹) ^ j := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have h := ItermG_abs_le_abs hq hC hn (Nat.le_add_right n j)
  have hexp : |q| ^ (-(((n + j : ℕ) : ℤ) + n)) ≤ |q| ^ (-(j : ℤ)) := by
    apply zpow_le_zpow_right₀ (le_of_lt hqabs1); push_cast; omega
  have hjeq : |q| ^ (-(j : ℤ)) = (|q|⁻¹) ^ j := by rw [zpow_neg, zpow_natCast, inv_pow]
  have hconst : (2 * |q|⁻¹) ≤ 1 := by
    have hinv : |q|⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
    calc 2 * |q|⁻¹ ≤ 2 * (2 : ℝ)⁻¹ := by linarith
      _ = 1 := by norm_num
  have hconst' : (2 * |q|⁻¹) ^ (n - 1) ≤ 1 := pow_le_one₀ (by positivity) hconst
  calc |ItermG q C n (n + j)| ≤ |q| ^ (-(((n + j : ℕ) : ℤ) + n)) * (2 * |q|⁻¹) ^ (n - 1) := h
    _ ≤ |q| ^ (-(j : ℤ)) * 1 :=
        mul_le_mul hexp hconst' (by positivity) (le_of_lt (zpow_pos (by linarith) _))
    _ = (|q|⁻¹) ^ j := by rw [mul_one, hjeq]

/-- **Error series summable, negative base** `q ≤ -2` (`2 ≤ |q|`, `2 < |C|`, `n ≥ 1`). The Lemma-4
convergence half for the negative-base regime. -/
lemma EtermG_summable_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun j => ItermG q C n (n + j)) := by
  have hr : |q|⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  apply Summable.of_norm_bounded (g := fun j => (|q|⁻¹) ^ j)
  · exact summable_geometric_of_lt_one (by positivity) hr
  · intro j; rw [Real.norm_eq_abs]; exact ItermG_shift_le_abs hq hC hn j

/- ### Sharp negative-base error bound (Lemma 4 endgame for `q ≤ -2`). -/

/-- Sharp per-factor bound (negative base): `|(1−q^{k−m})(1−C·q^{k+m})⁻¹| ≤ 2·(|q|^{k+m})⁻¹`. -/
lemma factor_abs_le_sharp_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ 2 * (|q| ^ (k + m))⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  rw [abs_mul]
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 2 := by
    have hle1 : |q| ^ ((k : ℤ) - m) ≤ 1 := by
      calc |q| ^ ((k : ℤ) - m) ≤ |q| ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hqabs1) (by omega)
        _ = 1 := by norm_num
    calc |1 - q ^ ((k : ℤ) - m)| = |(1 : ℝ) + -(q ^ ((k : ℤ) - m))| := by rw [sub_eq_add_neg]
      _ ≤ |(1 : ℝ)| + |-(q ^ ((k : ℤ) - m))| := abs_add_le _ _
      _ = 1 + |q| ^ ((k : ℤ) - m) := by rw [abs_one, abs_neg, abs_zpow]
      _ ≤ 2 := by linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ |q| ^ (-((k : ℤ) + m)) := inv_cqpow_le_abs hq hC (by omega)
  have h3 : |q| ^ (-((k : ℤ) + m)) = (|q| ^ (k + m))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast |q| (k + m), Nat.cast_add]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 2 * |q| ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 2 * (|q| ^ (k + m))⁻¹ := by rw [h3]

/-- Closed-form sharp per-term bound (negative base): `|Iₘ| ≤ 2^{n−1}·Cₙ·((|q|^n)⁻¹)^m` with
`Cₙ = (|q|^{n + ∑_{k<n} k})⁻¹`. The `2^{n−1}` (one `2` per cross factor) is a harmless constant. -/
lemma ItermG_abs_le_geom_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ m := by
  have hqabs : (0 : ℝ) < |q| := by linarith
  have hsharp : |ItermG q C n m|
      ≤ (|q| ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (2 * (|q| ^ (k + m))⁻¹) := by
    rw [ItermG, abs_mul, abs_neg]
    have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ (|q| ^ (m + n))⁻¹ := by
      have h := inv_cqpow_le_abs hq hC (a := (m : ℤ) + n) (by omega)
      have he : |q| ^ (-((m : ℤ) + n)) = (|q| ^ (m + n))⁻¹ := by
        rw [zpow_neg, ← zpow_natCast |q| (m + n), Nat.cast_add]
      rwa [he] at h
    have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
          (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ k ∈ Finset.Icc 1 (n - 1), (2 * (|q| ^ (k + m))⁻¹) := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k hk; rw [Finset.mem_Icc] at hk
      exact factor_abs_le_sharp_abs hq hC hk.1 (by omega)
    exact mul_le_mul hlead hprod (abs_nonneg _) (le_of_lt (inv_pos.mpr (pow_pos hqabs _)))
  refine hsharp.trans (le_of_eq ?_)
  have hL : (|q| ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (2 * (|q| ^ (k + m))⁻¹)
      = 2 ^ (n - 1) * (|q| ^ ((m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹ := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel,
      Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
    rw [show (|q| ^ (m + n))⁻¹ * (2 ^ (n - 1) * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹)
          = 2 ^ (n - 1) * ((|q| ^ (m + n))⁻¹ * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹) from by
        ring]
    rw [← mul_inv, ← pow_add]
  have hR : 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ m
      = 2 ^ (n - 1) * (|q| ^ ((n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m))⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_assoc, ← mul_inv, ← pow_add]
  rw [hL, hR, exp_identity hn m]

/-- The error bound (negative base): `|Eₙ| ≤ 2^{n−1}·Cₙ·(|q|^{-n})ⁿ·(1 − |q|^{-n})⁻¹`. -/
lemma EtermG_abs_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ n
        * (1 - (|q| ^ n)⁻¹)⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hr1lt : |q|⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  set r : ℝ := (|q| ^ n)⁻¹ with hr_def
  set Cn : ℝ := 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ with hCn_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact le_of_lt (inv_pos.mpr (pow_pos hqpos n))
  have hqn1 : (1 : ℝ) < |q| ^ n := by
    calc (1 : ℝ) < |q| := hqabs1
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ n := pow_le_pow_right₀ (le_of_lt hqabs1) hn
  have hr1 : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ hqn1
  have hsummabs : Summable (fun j => |ItermG q C n (n + j)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ItermG_shift_le_abs hq hC hn j)
      (summable_geometric_of_lt_one (by positivity) hr1lt)
  have h1 : |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun j => ItermG q C n (n + j))
      (by simpa [Real.norm_eq_abs] using hsummabs)
    simpa [EtermG, Real.norm_eq_abs] using hnorm
  have hge : ∀ j, |ItermG q C n (n + j)| ≤ Cn * r ^ (n + j) := fun j => by
    have h := ItermG_abs_le_geom_abs hq hC hn (Nat.le_add_right n j)
    rw [hCn_def, hr_def]; exact h
  have hsummaj : Summable (fun j => Cn * r ^ (n + j)) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).mul_left _
  have h2 : ∑' j, |ItermG q C n (n + j)| ≤ ∑' j, Cn * r ^ (n + j) :=
    hsummabs.tsum_le_tsum hge hsummaj
  have h3 : ∑' j, Cn * r ^ (n + j) = Cn * r ^ n * (1 - r)⁻¹ := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  calc |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := h1
    _ ≤ ∑' j, Cn * r ^ (n + j) := h2
    _ = Cn * r ^ n * (1 - r)⁻¹ := h3

/-- Clean closed-form error bound (negative base): `|Eₙ| ≤ 2ⁿ·(|q|^{n + ∑_{k<n}k + n²})⁻¹`. -/
lemma EtermG_abs_le'_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ 2 ^ n * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  refine (EtermG_abs_le_abs hq hC hn).trans ?_
  have hC' : (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ n
      = (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add, sq]
  have hqn2 : (2 : ℝ) ≤ |q| ^ n := by
    calc (2 : ℝ) ≤ |q| := hq
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ n := pow_le_pow_right₀ (le_of_lt hqabs1) hn
  have h1 : (|q| ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqn2
  have htail : (1 - (|q| ^ n)⁻¹)⁻¹ ≤ 2 := by
    have hb : (0 : ℝ) < 1 / 2 := by norm_num
    calc (1 - (|q| ^ n)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ hb (by linarith)
      _ = 2 := by norm_num
  have hCnn : (0 : ℝ) ≤ 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    have := pow_pos hqpos (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2); positivity
  have h2n : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
  calc 2 ^ (n - 1) * (|q| ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((|q| ^ n)⁻¹) ^ n
        * (1 - (|q| ^ n)⁻¹)⁻¹
      = 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
          * (1 - (|q| ^ n)⁻¹)⁻¹ := by rw [mul_assoc (2 ^ (n - 1)), hC']
    _ ≤ 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htail hCnn
    _ = 2 ^ n * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
        rw [show 2 ^ (n - 1) * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2
              = 2 ^ (n - 1) * 2 * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ from by ring,
          h2n]

/-- The leading factor `(1 − C·q^a)⁻¹` is negative for `a ≥ 1`, `C > 2`. -/
lemma leading_negG (hq : 2 ≤ q) (hC : 2 < C) {a : ℤ} (ha : 1 ≤ a) : (1 - C * q ^ a)⁻¹ < 0 := by
  have h2 : (2 : ℝ) ≤ q ^ a := qzpow_ge_two hq ha
  have hneg : (1 - C * q ^ a) < 0 := by nlinarith [h2, hC, zpow_pos (show (0:ℝ) < q by linarith) a]
  exact inv_neg''.mpr hneg

/-- Each product factor `(1 − q^{k−m})·(1 − C·q^{k+m})⁻¹` is negative for `1 ≤ k < m`. -/
lemma factor_negG (hq : 2 ≤ q) (hC : 2 < C) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹ < 0 := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hnum : 0 < 1 - q ^ ((k : ℤ) - m) := by
    have hle : q ^ ((k : ℤ) - m) ≤ q ^ (0 : ℤ) :=
      zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
    rw [zpow_zero] at hle
    have hpos : 0 < q ^ ((k : ℤ) - m) := zpow_pos (by linarith) _
    -- strict: the exponent is < 0, so q^{k-m} < 1
    have hlt : q ^ ((k : ℤ) - m) < 1 := by
      have : q ^ ((k : ℤ) - m) ≤ q ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
      have hq1' : q ^ (-1 : ℤ) < 1 := by
        rw [zpow_neg, zpow_one]; rw [inv_lt_one_iff₀]; right; linarith
      linarith
    linarith
  exact mul_neg_of_pos_of_neg hnum (leading_negG hq hC (by omega))

/-- `(-1)^{n-1}` times the product of the `n−1` (negative) factors is positive. -/
lemma prod_factor_signG (hq : 2 ≤ q) (hC : 2 < C) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < (-1 : ℝ) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1),
          (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹ := by
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h1 : (-1 : ℝ) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) := by
    rw [Finset.prod_const, hcard]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hf := factor_negG hq hC hk.1 (show k < m by omega)
  linarith

/-- The sign of `ItermG q C n m` (for `m ≥ n ≥ 1`) is exactly `(-1)^{n-1}`, nonzero. -/
lemma ItermG_sign (hq : 2 ≤ q) (hC : 2 < C) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < (-1 : ℝ) ^ (n - 1) * ItermG q C n m := by
  rw [ItermG]
  have hL : (1 - C * q ^ ((m : ℤ) + n))⁻¹ < 0 := leading_negG hq hC (by omega)
  have hP := prod_factor_signG hq hC hn hnm
  have hnegL : (0 : ℝ) < -(1 - C * q ^ ((m : ℤ) + n))⁻¹ := by linarith
  have := mul_pos hnegL hP
  convert this using 1 <;> first | rfl | ring

/- ### Summable geometric majorant `|ItermG q C n (n+j)| ≤ (q⁻¹)^j`. -/

/-- Each product factor has absolute value at most `q⁻¹` (for `1 ≤ k < m`, `q ≥ 2`, `C > 2`). -/
lemma factor_boundG (hq : 2 ≤ q) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ q⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  rw [abs_mul]
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : q ^ ((k : ℤ) - m) ≤ 1 := by
      calc q ^ ((k : ℤ) - m) ≤ q ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) hexp
        _ = 1 := by norm_num
    have hpos : 0 < q ^ ((k : ℤ) - m) := zpow_pos (by linarith) _
    rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ q ^ (-((k : ℤ) + m)) := inv_cqpowG_le hq hC (by omega)
  have h3 : q ^ (-((k : ℤ) + m)) ≤ q⁻¹ := by
    calc q ^ (-((k : ℤ) + m)) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
      _ = q⁻¹ := by rw [zpow_neg, zpow_one]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * q⁻¹ := mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
    _ = q⁻¹ := by ring

/-- Crude per-term bound: `|ItermG q C n m| ≤ q^{-(m+n)}·(q⁻¹)^{n-1}` for `1 ≤ n ≤ m`. -/
lemma ItermG_abs_le (hq : 2 ≤ q) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ q ^ (-((m : ℤ) + n)) * (q⁻¹) ^ (n - 1) := by
  have hq1 : (1 : ℝ) < q := by linarith
  rw [ItermG, abs_mul, abs_neg]
  have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ q ^ (-((m : ℤ) + n)) := inv_cqpowG_le hq hC (by omega)
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ (q⁻¹) ^ (n - 1) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 (n - 1), |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ _k ∈ Finset.Icc 1 (n - 1), q⁻¹ :=
          Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => by
            rw [Finset.mem_Icc] at hk
            exact factor_boundG hq hC hk.1 (by omega))
      _ = (q⁻¹) ^ (Finset.Icc 1 (n - 1)).card := by rw [Finset.prod_const]
      _ = (q⁻¹) ^ (n - 1) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hbnn : (0 : ℝ) ≤ q ^ (-((m : ℤ) + n)) := le_of_lt (zpow_pos (by linarith) _)
  exact mul_le_mul hlead hprod (abs_nonneg _) hbnn

/-- The reindexed term `ItermG q C n (n+j)` is bounded by `(q⁻¹)^j`. -/
lemma ItermG_shift_le (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    |ItermG q C n (n + j)| ≤ (q⁻¹) ^ j := by
  have hq1 : (1 : ℝ) < q := by linarith
  have h := ItermG_abs_le hq hC hn (Nat.le_add_right n j)
  have hexp : q ^ (-(((n + j : ℕ) : ℤ) + n)) ≤ q ^ (-(j : ℤ)) := by
    apply zpow_le_zpow_right₀ (le_of_lt hq1)
    push_cast; omega
  have hpow1 : (q⁻¹) ^ (n - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [inv_le_one_iff₀]; right; linarith)
  have hjeq : q ^ (-(j : ℤ)) = (q⁻¹) ^ j := by rw [zpow_neg, zpow_natCast, inv_pow]
  calc |ItermG q C n (n + j)| ≤ q ^ (-(((n + j : ℕ) : ℤ) + n)) * (q⁻¹) ^ (n - 1) := h
    _ ≤ q ^ (-(j : ℤ)) * 1 := mul_le_mul hexp hpow1 (by positivity) (le_of_lt (zpow_pos (by linarith) _))
    _ = (q⁻¹) ^ j := by rw [mul_one, hjeq]

/-- The error series `EtermG q C n = ∑_j ItermG q C n (n+j)` is summable (`q ≥ 2, C > 2`). The
Lemma-4 convergence half. -/
lemma EtermG_summable (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun j => ItermG q C n (n + j)) := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hr : q⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  apply Summable.of_norm_bounded (g := fun j => (q⁻¹) ^ j)
  · exact summable_geometric_of_lt_one (by positivity) hr
  · intro j; rw [Real.norm_eq_abs]; exact ItermG_shift_le hq hC hn j

/-- **Borwein Lemma 5 (non-vanishing), general `(q,C)`.** `EtermG q C n ≠ 0` for `n ≥ 1`, `q ≥ 2`,
`C > 2`: the error is a tsum of same-sign nonzero terms `(-1)^{n-1}·ItermG > 0`. -/
theorem EtermG_ne_zero (hq : 2 ≤ q) (hC : 2 < C) {n : ℕ} (hn : 1 ≤ n) : EtermG q C n ≠ 0 := by
  have hCabs : 2 < |C| := by rw [abs_of_pos (by linarith)]; exact hC
  have hsum : Summable (fun j => (-1 : ℝ) ^ (n - 1) * ItermG q C n (n + j)) :=
    (EtermG_summable hq hCabs hn).mul_left _
  have hpos : ∀ j, 0 < (-1 : ℝ) ^ (n - 1) * ItermG q C n (n + j) :=
    fun j => ItermG_sign hq hC hn (Nat.le_add_right n j)
  have hp : 0 < ∑' j, (-1 : ℝ) ^ (n - 1) * ItermG q C n (n + j) :=
    hsum.tsum_pos (fun j => le_of_lt (hpos j)) 0 (hpos 0)
  rw [tsum_mul_left] at hp
  intro h0
  rw [show (∑' j, ItermG q C n (n + j)) = EtermG q C n from rfl, h0, mul_zero] at hp
  exact lt_irrefl 0 hp

/- ### Negative regime `C < -2`: non-vanishing (no alternation — all terms same sign). -/

/-- For `C < -2`, `q ≥ 2`: every term `ItermG q C n m` is strictly negative (`1 ≤ n ≤ m`). The leading
inverse and each product factor are positive (since `C < 0`), so `ItermG = -(positive) < 0`. -/
lemma ItermG_neg (hq : 2 ≤ q) (hC : C < -2) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    ItermG q C n m < 0 := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hL : 0 < (1 - C * q ^ ((m : ℤ) + n))⁻¹ := by
    apply inv_pos.mpr
    nlinarith [zpow_pos hqpos ((m : ℤ) + n), hC,
      mul_pos (show (0 : ℝ) < -C by linarith) (zpow_pos hqpos ((m : ℤ) + n))]
  have hPprod : 0 < ∏ k ∈ Finset.Icc 1 (n - 1),
      (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹ := by
    apply Finset.prod_pos
    intro k hk; rw [Finset.mem_Icc] at hk
    have hf1 : 0 < 1 - q ^ ((k : ℤ) - m) := by
      have hle : q ^ ((k : ℤ) - m) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) (by omega)
      have hlt1 : q ^ (-1 : ℤ) < 1 := by rw [zpow_neg, zpow_one, inv_lt_one_iff₀]; right; linarith
      linarith
    have hf2 : 0 < (1 - C * q ^ ((k : ℤ) + m))⁻¹ := by
      apply inv_pos.mpr
      nlinarith [zpow_pos hqpos ((k : ℤ) + m), hC,
        mul_pos (show (0 : ℝ) < -C by linarith) (zpow_pos hqpos ((k : ℤ) + m))]
    exact mul_pos hf1 hf2
  rw [ItermG, neg_mul]
  have := mul_pos hL hPprod
  linarith

/-- **Borwein Lemma 5 (non-vanishing), negative regime.** `EtermG q C n ≠ 0` for `n ≥ 1`, `q ≥ 2`,
`C < -2`: the error is a tsum of strictly negative summable terms. -/
theorem EtermG_ne_zero_neg (hq : 2 ≤ q) (hC : C < -2) {n : ℕ} (hn : 1 ≤ n) : EtermG q C n ≠ 0 := by
  have hCabs : 2 < |C| := by rw [abs_of_neg (by linarith)]; linarith
  have hsum : Summable (fun j => ItermG q C n (n + j)) := EtermG_summable hq hCabs hn
  have hneg : ∀ j, ItermG q C n (n + j) < 0 := fun j => ItermG_neg hq hC hn (Nat.le_add_right n j)
  have hp : 0 < ∑' j, -ItermG q C n (n + j) :=
    hsum.neg.tsum_pos (fun j => by linarith [hneg j]) 0 (by linarith [hneg 0])
  rw [tsum_neg] at hp
  intro h0
  rw [show (∑' j, ItermG q C n (n + j)) = EtermG q C n from rfl, h0, neg_zero] at hp
  exact lt_irrefl 0 hp

/- ### Negative BASE `q ≤ -2` non-vanishing (Borwein Lemma 5): the sign DICHOTOMY.

For negative base the powers `q^a` alternate, so terms `Iₙ(n+j)` do NOT share a sign. The exact
structure (worked out and numerically verified): with the cross factors `1 − q^{k−m}` always
positive (`one_sub_qzpow_pos`) and each inverse factor `(1 − C·q^a)⁻¹` carrying the sign
`sign(C)·(−1)^{a+1}` (since `|C·q^a| > 1`), the sign of `Iₙ(n+j)` is `sₙ·(−1)^{n·j}` for a fixed
`sₙ`. Hence the **dichotomy**: `n` even ⟹ all terms share sign `sₙ` (same-sign tsum, `≠ 0`);
`n` odd ⟹ terms alternate (alternating-series bracket, `≠ 0`).

The bookkeeping is captured by an explicit sign multiplier `EsignG C n m` with
`0 < EsignG C n m · Iₙ(m)` and the recurrence `EsignG C n (m+1) = (−1)^n · EsignG C n m`. -/

/-- If `0 < z·w` then `0 < z·w⁻¹` (same-sign of `w` and `w⁻¹`). -/
lemma pos_of_pos_mul_inv {z w : ℝ} (h : 0 < z * w) : 0 < z * w⁻¹ := by
  rw [← div_eq_mul_inv, div_pos_iff]
  rcases mul_pos_iff.mp h with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · exact Or.inl ⟨hz, hw⟩
  · exact Or.inr ⟨hz, hw⟩

/-- **Inverse-factor sign (negative base).** For `q ≤ -2`, `2 < |C|`, `a ≥ 1`:
`0 < C·(−1)^{a+1}·(1 − C·q^a)⁻¹`. Writing `q^a = (−1)^a·|q|^a`, the factor `1 − C·q^a` has sign
`sign(C)·(−1)^{a+1}` (its magnitude exceeds `1`), matching the multiplier `C·(−1)^{a+1}`. -/
lemma inv_factor_sign_neg (hq : q ≤ -2) (hC : 2 < |C|) (a : ℕ) (ha : 1 ≤ a) :
    0 < C * (-1) ^ (a + 1) * (1 - C * q ^ a)⁻¹ := by
  have hqneg : q < 0 := by linarith
  have habs : |q| = -q := abs_of_neg hqneg
  have hq2 : (2 : ℝ) ≤ |q| := by rw [habs]; linarith
  have hCsq : (4 : ℝ) < C ^ 2 := by nlinarith [hC, abs_nonneg C, sq_abs C]
  have hq_eq : q = -|q| := by rw [habs]; ring
  set s : ℝ := (-1) ^ a with hs
  set Q : ℝ := |q| ^ a with hQdef
  have hss : s ^ 2 = 1 := by rw [hs, ← pow_mul]; exact Even.neg_one_pow ⟨a, by ring⟩
  have hQ2 : (2 : ℝ) ≤ Q := by
    rw [hQdef]
    calc (2 : ℝ) ≤ |q| := hq2
      _ = |q| ^ 1 := (pow_one _).symm
      _ ≤ |q| ^ a := pow_le_pow_right₀ (by linarith) ha
  have hqa : q ^ a = s * Q := by
    rw [hs, hQdef]
    conv_lhs => rw [hq_eq]
    rw [neg_pow]
  have key : 0 < (C * (-1) ^ (a + 1)) * (1 - C * q ^ a) := by
    have hexp : (-1 : ℝ) ^ (a + 1) = -s := by rw [pow_succ, hs]; ring
    rw [hexp, hqa]
    have heq : (C * -s) * (1 - C * (s * Q)) = -(C * s) + C ^ 2 * s ^ 2 * Q := by ring
    rw [heq, hss, mul_one]
    have hbound : 2 * (C * s) ≤ C ^ 2 + 1 := by nlinarith [sq_nonneg (C * s - 1), hss, sq_nonneg C]
    nlinarith [hbound, hQ2, hCsq, sq_nonneg C]
  exact pos_of_pos_mul_inv key

/- The explicit per-`m` sign multiplier. `EsignG C n m · Iₙ(m) > 0`, and the recurrence
`EsignG C n (m+1) = (−1)^n · EsignG C n m` gives `EsignG C n (n+j) = (−1)^{nj}·EsignG C n n`. -/

/-- Sign multiplier making `EsignG C n m · ItermG q C n m > 0` for negative base. -/
noncomputable def EsignG (C : ℝ) (n m : ℕ) : ℝ :=
  -C ^ n * (-1) ^ (m + n + 1) * ∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + m + 1)

/-- **The per-term sign positivity (negative base).** `0 < EsignG C n m · Iₙ(m)` for `q ≤ -2`,
`2 < |C|`, `1 ≤ n ≤ m`. The cross factors `1 − q^{k−m} > 0`, the leading & inner inverse factors
each pair with their `C·(−1)^{a+1}` multiplier into a positive (`inv_factor_sign_neg`). -/
lemma ItermG_sign_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < EsignG C n m * ItermG q C n m := by
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg (show q < 0 by linarith)]; linarith
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hCn : C ^ n = C * ∏ _k ∈ Finset.Icc 1 (n - 1), C := by
    rw [Finset.prod_const, hcard, ← pow_succ', Nat.sub_add_cancel hn]
  -- leading positive bracket
  have hlead : 0 < C * (-1) ^ (m + n + 1) * (1 - C * q ^ ((m : ℤ) + n))⁻¹ := by
    have h := inv_factor_sign_neg hq hC (m + n) (by omega)
    rwa [show q ^ (m + n) = q ^ ((m : ℤ) + n) by rw [← Nat.cast_add, zpow_natCast]] at h
  -- each positive `k`-bracket
  have hk : ∀ k ∈ Finset.Icc 1 (n - 1),
      0 < C * (-1) ^ (k + m + 1) * ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹) := by
    intro k hk'
    rw [Finset.mem_Icc] at hk'
    have hkm : k < m := by omega
    have h1 := inv_factor_sign_neg hq hC (k + m) (by omega)
    rw [show q ^ (k + m) = q ^ ((k : ℤ) + m) by rw [← Nat.cast_add, zpow_natCast]] at h1
    have h2 := one_sub_qzpow_pos hqabs hkm
    nlinarith [mul_pos h1 h2]
  -- the product identity, then positivity
  have hsplit : ∏ k ∈ Finset.Icc 1 (n - 1),
        (C * (-1) ^ (k + m + 1) * ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹))
      = (∏ _k ∈ Finset.Icc 1 (n - 1), C) * (∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + m + 1))
        * (∏ k ∈ Finset.Icc 1 (n - 1), ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have heq : EsignG C n m * ItermG q C n m
      = (C * (-1) ^ (m + n + 1) * (1 - C * q ^ ((m : ℤ) + n))⁻¹)
        * ∏ k ∈ Finset.Icc 1 (n - 1),
            (C * (-1) ^ (k + m + 1) * ((1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹)) := by
    rw [hsplit, EsignG, ItermG, hCn]; ring
  rw [heq]
  exact mul_pos hlead (Finset.prod_pos hk)

/-- **Sign recurrence**: `EsignG C n (m+1) = (−1)^n · EsignG C n m`. Each `(−1)`-exponent in the
multiplier gains one `m`, and there are exactly `1 + (n−1) = n` of them. -/
lemma EsignG_step {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    EsignG C n (m + 1) = (-1) ^ n * EsignG C n m := by
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hprod : ∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + (m + 1) + 1)
      = (∏ k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) ^ (k + m + 1)) * (-1) ^ (n - 1) := by
    rw [show (-1 : ℝ) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) by rw [Finset.prod_const, hcard],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => by rw [show k + (m + 1) + 1 = (k + m + 1) + 1 from by ring, pow_succ])
  rw [EsignG, EsignG, hprod,
    show (-1 : ℝ) ^ (m + 1 + n + 1) = (-1) ^ (m + n + 1) * (-1) by
      rw [show m + 1 + n + 1 = (m + n + 1) + 1 from by ring, pow_succ],
    show (-1 : ℝ) ^ n = (-1) ^ (n - 1) * (-1) by rw [← pow_succ, Nat.sub_add_cancel hn]]
  ring

/-- `EsignG C n (n+j) = (−1)^{nj} · EsignG C n n`. -/
lemma EsignG_shift {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    EsignG C n (n + j) = (-1) ^ (n * j) * EsignG C n n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show n + (j + 1) = (n + j) + 1 from by ring, EsignG_step hn, ih, ← mul_assoc, ← pow_add,
      show n * (j + 1) = n + n * j from by ring]

/-- **Lemma 5, negative base, `n` even.** `(−1)^{nj}=1`, so all terms `EsignG C n n · Iₙ(n+j)`
are strictly positive ⟹ the error tsum is nonzero. -/
theorem EtermG_ne_zero_even_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n : ℕ}
    (hn : 1 ≤ n) (hne : Even n) : EtermG q C n ≠ 0 := by
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg (show q < 0 by linarith)]; linarith
  have hpos : ∀ j, 0 < EsignG C n n * ItermG q C n (n + j) := by
    intro j
    have h := ItermG_sign_negbase hq hC hn (Nat.le_add_right n j)
    rwa [EsignG_shift hn, Even.neg_one_pow (hne.mul_right j), one_mul] at h
  have hsum : Summable (fun j => EsignG C n n * ItermG q C n (n + j)) :=
    (EtermG_summable_abs hqabs hC hn).mul_left _
  have hp : 0 < ∑' j, EsignG C n n * ItermG q C n (n + j) :=
    hsum.tsum_pos (fun j => le_of_lt (hpos j)) 0 (hpos 0)
  rw [tsum_mul_left] at hp
  intro h0
  rw [show (∑' j, ItermG q C n (n + j)) = EtermG q C n from rfl, h0, mul_zero] at hp
  exact lt_irrefl 0 hp

/- ### Magnitude antitonicity `|Iₙ(m+1)| < |Iₙ(m)|` (negative base) — the odd-case prerequisite.

The consecutive ratio of magnitudes **telescopes**: the inverse factors form a contiguous block
`∏_{a=M+1}^{M+n}|1−C·q^a|⁻¹` and the cross factors a contiguous block, so
`|Iₙ(m+1)|/|Iₙ(m)| = [|1−q^{−m}|·|1−C·q^{m+1}|] / [|1−q^{(n−1)−m}|·|1−C·q^{m+n+1}|]`, reducing the whole
inequality to the single two-factor estimate `|1−q^{−m}|·|1−C·q^{m+1}| < |1−q^{(n−1)−m}|·|1−C·q^{m+n+1}|`
(split `n=1` / `n≥2`). -/

/-- Magnitude factorization `|Iₙ(M)| = (∏ cross)·∏ inv`. -/
lemma ItermG_abs_factor (n M : ℕ) (hn : 1 ≤ n) :
    |ItermG q C n M|
      = (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - M)|)
        * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + M)|⁻¹ := by
  rw [ItermG_prod_form n M hn, abs_neg, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  exact Finset.prod_congr rfl (fun k _ => abs_inv _)

/-- Generic shift-telescope over `range`: `(∏_{i<N} g i)·g N = (∏_{i<N} g(i+1))·g 0`. -/
lemma prod_range_shift_telescope (g : ℕ → ℝ) (N : ℕ) :
    (∏ i ∈ Finset.range N, g i) * g N = (∏ i ∈ Finset.range N, g (i + 1)) * g 0 := by
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']

/-- `∏_{k∈Icc 1 N} f k = ∏_{i<N} f (i+1)`. -/
lemma prod_Icc_one_eq_range (f : ℕ → ℝ) (N : ℕ) :
    ∏ k ∈ Finset.Icc 1 N, f k = ∏ i ∈ Finset.range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Finset.prod_range_succ]

/-- Cross-factor telescoping: `Across(m+1)·c(n−1−m) = Across(m)·c(−m)`. -/
lemma cross_telescopeG (q : ℝ) (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - ((m + 1 : ℕ) : ℤ))|)
        * |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))|
      = (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m : ℤ))|)
        * |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| := by
  rw [prod_Icc_one_eq_range, prod_Icc_one_eq_range]
  have key := prod_range_shift_telescope (fun i => |1 - q ^ ((i : ℤ) - (m : ℤ))|) (n - 1)
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring_nf)
  · rfl

/-- Inverse-denominator telescoping: `Dinv(m+1)·d(m+1) = Dinv(m)·d(m+n+1)`. -/
lemma inv_telescopeG (q C : ℝ) (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + ((m + 1 : ℕ) : ℤ))|)
        * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
      = (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m : ℤ))|)
        * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
  rw [prod_Icc_one_eq_range, prod_Icc_one_eq_range]
  have key := prod_range_shift_telescope (fun i => |1 - C * q ^ ((i : ℤ) + ((m + 1 : ℕ) : ℤ))|) n
  refine Eq.trans ?_ (key.symm.trans ?_)
  · rfl
  · congr 1
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring_nf)

/-- The **reduced two-factor inequality**: `|1−q^{−m}|·|1−C·q^{m+1}| < |1−q^{(n−1)−m}|·|1−C·q^{m+n+1}|`,
to which the whole magnitude antitonicity collapses after telescoping. Split `n=1` (cross factors equal,
reduce to the inverse comparison) / `n≥2` (crude `3/2`,`1/2` cross bounds, since `|q|^n ≥ 4`). -/
lemma reduced_two_factor (hq : q ≤ -2) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
      < |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
  have hqneg : q < 0 := by linarith
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg hqneg]; linarith
  have hq1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hq0 : |q| ≠ 0 := by linarith
  have hCpos : (0 : ℝ) < |C| := by linarith
  -- triangle helpers
  have tri_up : ∀ x : ℝ, |1 - x| ≤ 1 + |x| := fun x => by
    calc |1 - x| = |(1 : ℝ) + (-x)| := by ring_nf
      _ ≤ |(1 : ℝ)| + |-x| := abs_add_le _ _
      _ = 1 + |x| := by rw [abs_one, abs_neg]
  have tri_lo : ∀ x : ℝ, 1 - |x| ≤ |1 - x| := fun x => by
    have := abs_sub_abs_le_abs_sub (1 : ℝ) x; rw [abs_one] at this; linarith
  -- cross-factor bounds (exponent ≤ -1)
  have cross_le : ∀ e : ℤ, e ≤ -1 → |1 - q ^ e| ≤ 3 / 2 := by
    intro e he
    have hqe : |q| ^ e ≤ 1 / 2 := by
      calc |q| ^ e ≤ |q| ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) he
        _ = |q|⁻¹ := by rw [zpow_neg, zpow_one]
        _ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqabs
    calc |1 - q ^ e| ≤ 1 + |q ^ e| := tri_up _
      _ = 1 + |q| ^ e := by rw [abs_zpow]
      _ ≤ 3 / 2 := by linarith
  have cross_ge : ∀ e : ℤ, e ≤ -1 → 1 / 2 ≤ |1 - q ^ e| := by
    intro e he
    have hqe : |q| ^ e ≤ 1 / 2 := by
      calc |q| ^ e ≤ |q| ^ (-1 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) he
        _ = |q|⁻¹ := by rw [zpow_neg, zpow_one]
        _ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqabs
    calc (1 : ℝ) / 2 ≤ 1 - |q| ^ e := by linarith
      _ = 1 - |q ^ e| := by rw [abs_zpow]
      _ ≤ |1 - q ^ e| := tri_lo _
  have cross_pos : ∀ e : ℤ, e ≤ -1 → 0 < |1 - q ^ e| := fun e he => by
    have := cross_ge e he; linarith
  -- inverse-denominator bounds (exponent ≥ 1)
  have inv_le : ∀ a : ℤ, |1 - C * q ^ a| ≤ 1 + |C| * |q| ^ a := fun a => by
    calc |1 - C * q ^ a| ≤ 1 + |C * q ^ a| := tri_up _
      _ = 1 + |C| * |q| ^ a := by rw [abs_mul, abs_zpow]
  have inv_ge : ∀ a : ℤ, |C| * |q| ^ a - 1 ≤ |1 - C * q ^ a| := fun a => by
    have h2 := abs_sub_abs_le_abs_sub (C * q ^ a) 1
    rw [abs_one, abs_sub_comm] at h2
    calc |C| * |q| ^ a - 1 = |C * q ^ a| - 1 := by rw [abs_mul, abs_zpow]
      _ ≤ |1 - C * q ^ a| := h2
  -- abbreviations
  set P : ℝ := |C| * |q| ^ (m + 1) with hP
  have hqm1 : (4 : ℝ) ≤ |q| ^ (m + 1) := by
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ |q| * |q| := by nlinarith [hqabs]
      _ = |q| ^ 2 := by ring
      _ ≤ |q| ^ (m + 1) := pow_le_pow_right₀ (le_of_lt hq1) (by omega)
  have hP8 : (8 : ℝ) ≤ P := by rw [hP]; nlinarith [hqm1, hC, hCpos]
  -- D0 = |1 - C q^{m+1}|, exponent normalizations
  have hexpD0 : (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ)) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  have hD0le : |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| ≤ P + 1 := by
    rw [hexpD0, zpow_natCast, hP]
    have h := inv_le ((m + 1 : ℕ) : ℤ)
    rw [zpow_natCast, zpow_natCast] at h
    linarith [h]
  have hD0pos : 0 < |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
    rw [hexpD0]; apply abs_pos.mpr; rw [sub_ne_zero]
    intro h
    have hmag : |C * q ^ ((m + 1 : ℕ) : ℤ)| = |C| * |q| ^ (m + 1) := by rw [abs_mul, abs_zpow, zpow_natCast]
    have : |C * q ^ ((m + 1 : ℕ) : ℤ)| = 1 := by rw [← h, abs_one]
    rw [hmag] at this; nlinarith [hqm1, hC, hCpos, this]
  -- A0 = |1 - q^{-m}|
  have hA0pos : 0 < |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| := cross_pos _ (by push_cast; omega)
  rcases eq_or_lt_of_le hn with hn1 | hn2
  · -- n = 1: cross factors coincide, reduce to D0 < D1
    subst hn1
    have hDn : |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| ≥ 2 * P - 1 := by
      have he : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [he]
      have := inv_ge ((m + 2 : ℕ) : ℤ)
      rw [zpow_natCast] at this
      have h2 : |q| ^ (m + 2) = |q| * |q| ^ (m + 1) := by rw [pow_succ]; ring
      rw [hP]; nlinarith [this, h2, hqabs, hCpos, mul_pos hCpos (pow_pos hqpos (m + 1))]
    have : |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| < |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
      have h1 := hD0le; nlinarith [h1, hDn, hP8]
    calc |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
        < |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| :=
          mul_lt_mul_of_pos_left this hA0pos
      _ = |1 - q ^ (((1 - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((1 : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
          norm_num
  · -- n ≥ 2: crude bounds
    have hA0le : |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| ≤ 3 / 2 := cross_le _ (by push_cast; omega)
    have hAnge : 1 / 2 ≤ |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| := cross_ge _ (by
      have : (1 : ℕ) ≤ n - 1 := by omega
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; omega)
    have hqn4 : (4 : ℝ) ≤ |q| ^ n := by
      calc (4 : ℝ) = 2 * 2 := by norm_num
        _ ≤ |q| * |q| := by nlinarith [hqabs]
        _ = |q| ^ 2 := by ring
        _ ≤ |q| ^ n := pow_le_pow_right₀ (le_of_lt hq1) (by omega)
    have hDnge : P * |q| ^ n - 1 ≤ |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| := by
      have he : (n : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + (n : ℤ) := by push_cast; ring
      rw [he]
      have hzadd : |q| ^ (((m + 1 : ℕ) : ℤ) + (n : ℤ)) = |q| ^ (m + 1) * |q| ^ n := by
        rw [zpow_add₀ hq0, zpow_natCast, zpow_natCast]
      have hge := inv_ge (((m + 1 : ℕ) : ℤ) + (n : ℤ))
      rw [hzadd] at hge
      rw [hP]; nlinarith [hge]
    have hD0nn : (0 : ℝ) ≤ P + 1 := by linarith [hP8]
    have hub : |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|
        ≤ (3 / 2) * (P + 1) :=
      mul_le_mul hA0le hD0le (le_of_lt hD0pos) (by norm_num)
    have hPqn0 : (0 : ℝ) ≤ P * |q| ^ n - 1 := by nlinarith [hP8, hqn4]
    have hlb : (1 / 2) * (P * |q| ^ n - 1)
        ≤ |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))| :=
      mul_le_mul hAnge hDnge hPqn0 (by linarith [hAnge])
    have hmid : (3 / 2) * (P + 1) < (1 / 2) * (P * |q| ^ n - 1) := by
      nlinarith [hP8, hqn4, mul_nonneg (show (0:ℝ) ≤ P by linarith) (show (0:ℝ) ≤ |q| ^ n - 4 by linarith)]
    exact (hub.trans_lt hmid).trans_le hlb

/-- **Magnitude antitonicity (negative base).** `|Iₙ(m+1)| < |Iₙ(m)|` for `q ≤ -2`, `2 < |C|`,
`1 ≤ n ≤ m`. The consecutive ratio telescopes (`cross_telescopeG`, `inv_telescopeG`) and collapses to
`reduced_two_factor`. This is the odd-case prerequisite for non-vanishing. -/
lemma ItermG_abs_anti_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n (m + 1)| < |ItermG q C n m| := by
  have hqneg : q < 0 := by linarith
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg hqneg]; linarith
  have hq1 : (1 : ℝ) < |q| := by linarith
  have hCpos : (0 : ℝ) < |C| := by linarith
  -- positivity of factors
  have cross_pos : ∀ M k : ℕ, k < M → 0 < |1 - q ^ ((k : ℤ) - M)| := by
    intro M k hkM; rw [abs_of_pos (one_sub_qzpow_pos hqabs hkM)]; exact one_sub_qzpow_pos hqabs hkM
  have inv_pos' : ∀ a : ℤ, 1 ≤ a → 0 < |1 - C * q ^ a| := by
    intro a ha
    rw [abs_pos, sub_ne_zero]; intro h
    have hqa : (2 : ℝ) ≤ |q| ^ a := by
      calc (2 : ℝ) ≤ |q| := hqabs
        _ = |q| ^ (1 : ℤ) := (zpow_one _).symm
        _ ≤ |q| ^ a := zpow_le_zpow_right₀ (le_of_lt hq1) ha
    have hmag : |C * q ^ a| = |C| * |q| ^ a := by rw [abs_mul, abs_zpow]
    have heq1 : |C| * |q| ^ a = 1 := by rw [← hmag, ← h, abs_one]
    nlinarith [hqa, hC, hCpos, heq1, mul_le_mul (le_of_lt hC) hqa (by norm_num) (le_of_lt hCpos)]
  have hDinv_pos : ∀ M : ℕ, 0 < ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + M)| := fun M => by
    apply Finset.prod_pos; intro k hk; rw [Finset.mem_Icc] at hk; exact inv_pos' _ (by omega)
  have hAcr_pos : ∀ M : ℕ, n ≤ M → 0 < ∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - M)| := by
    intro M hM; apply Finset.prod_pos; intro k hk; rw [Finset.mem_Icc] at hk; exact cross_pos M k (by omega)
  -- magnitude in division form
  have hdiv : ∀ M : ℕ, |ItermG q C n M|
      = (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - M)|)
        / (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + M)|) := by
    intro M; rw [ItermG_abs_factor n M hn, Finset.prod_inv_distrib, div_eq_mul_inv]
  rw [hdiv m, hdiv (m + 1), div_lt_div_iff₀ (hDinv_pos (m + 1)) (hDinv_pos m)]
  -- endpoint factors
  have hcc0 : 0 < |1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| := cross_pos m 0 (by omega)
  have hccn : 0 < |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| := cross_pos m (n - 1) (by omega)
  have hdd0 : 0 < |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| := inv_pos' _ (by push_cast; omega)
  have hpos : 0 < |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))| :=
    mul_pos hccn hdd0
  have hADpos : 0 < (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
      * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)| := mul_pos (hAcr_pos m hnm) (hDinv_pos m)
  refine lt_of_mul_lt_mul_right ?_ hpos.le
  have e1 : (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m + 1 : ℕ))|)
        * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
        * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
      = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
        * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
        * (|1 - q ^ (((0 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|) := by
    rw [show (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m + 1 : ℕ))|)
          * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
          * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
        = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - (m + 1 : ℕ))|)
            * |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))|)
          * ((∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
            * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|) from by ring,
      cross_telescopeG q n m]
    ring
  have e2 : (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
        * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m + 1 : ℕ))|)
        * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
      = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
        * ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + m)|)
        * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ ((n : ℤ) + ((m + 1 : ℕ) : ℤ))|) := by
    rw [show (∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
          * (∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m + 1 : ℕ))|)
          * (|1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))| * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|)
        = ((∏ k ∈ Finset.Icc 1 (n - 1), |1 - q ^ ((k : ℤ) - m)|)
            * |1 - q ^ (((n - 1 : ℕ) : ℤ) - (m : ℤ))|)
          * ((∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ ((k : ℤ) + (m + 1 : ℕ))|)
            * |1 - C * q ^ (((0 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ))|) from by ring,
      inv_telescopeG q C n m]
    ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left (reduced_two_factor hq hC hn hnm) hADpos

/- ### Sharp super-exponential error bound (Borwein Lemma 4) and the cleared error `→ 0`. -/

open Filter Topology

/-- Tight per-factor bound: `|(1 − q^{k−m})·(1 − C·q^{k+m})⁻¹| ≤ (q^{k+m})⁻¹` for `1 ≤ k < m`. -/
lemma factor_abs_leG (hq : 2 ≤ q) (hC : 2 < |C|) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ (q ^ (k + m))⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  rw [abs_mul]
  have h1 : |1 - q ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : q ^ ((k : ℤ) - m) ≤ 1 := by
      calc q ^ ((k : ℤ) - m) ≤ q ^ (0 : ℤ) := zpow_le_zpow_right₀ (le_of_lt hq1) hexp
        _ = 1 := by norm_num
    have hpos : 0 < q ^ ((k : ℤ) - m) := zpow_pos (by linarith) _
    rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : |(1 - C * q ^ ((k : ℤ) + m))⁻¹| ≤ q ^ (-((k : ℤ) + m)) := inv_cqpowG_le hq hC (by omega)
  have h3 : q ^ (-((k : ℤ) + m)) = (q ^ (k + m))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast q (k + m), Nat.cast_add]
  calc |1 - q ^ ((k : ℤ) - m)| * |(1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * q ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (q ^ (k + m))⁻¹ := by rw [one_mul, h3]

/-- Sharp per-term bound in product form. -/
lemma ItermG_abs_le_sharp (hq : 2 ≤ q) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ (q ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (q ^ (k + m))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by linarith
  rw [ItermG, abs_mul, abs_neg]
  have hlead : |(1 - C * q ^ ((m : ℤ) + n))⁻¹| ≤ (q ^ (m + n))⁻¹ := by
    have h := inv_cqpowG_le hq hC (a := (m : ℤ) + n) (by omega)
    have he : q ^ (-((m : ℤ) + n)) = (q ^ (m + n))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast q (m + n), Nat.cast_add]
    rwa [he] at h
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - q ^ ((k : ℤ) - m)) * (1 - C * q ^ ((k : ℤ) + m))⁻¹|
      ≤ ∏ k ∈ Finset.Icc 1 (n - 1), (q ^ (k + m))⁻¹ := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
    intro k hk; rw [Finset.mem_Icc] at hk
    exact factor_abs_leG hq hC hk.1 (by omega)
  exact mul_le_mul hlead hprod (abs_nonneg _) (le_of_lt (inv_pos.mpr (pow_pos hqpos _)))

/-- Closed-form sharp per-term bound: `|Iₘ| ≤ Cₙ·(q^{-n})^m` with `Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. -/
lemma ItermG_abs_le_geom (hq : 2 ≤ q) (hC : 2 < |C|) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |ItermG q C n m| ≤ (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ m := by
  have hqpos : (0 : ℝ) < q := by linarith
  refine (ItermG_abs_le_sharp hq hC hn hnm).trans (le_of_eq ?_)
  have hL : (q ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (q ^ (k + m))⁻¹
      = (q ^ ((m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
  have hR : (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ m
      = (q ^ ((n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add]
  rw [hL, hR, exp_identity hn m]

/-- The error bound `|Eₙ| ≤ Cₙ·(q^{-n})ⁿ·(1 − q^{-n})⁻¹`. -/
lemma EtermG_abs_le (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ n
        * (1 - (q ^ n)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hr1lt : q⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
  set r : ℝ := (q ^ n)⁻¹ with hr_def
  set Cn : ℝ := (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ with hCn_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact le_of_lt (inv_pos.mpr (pow_pos hqpos n))
  have hqn1 : (1 : ℝ) < q ^ n := by
    calc (1 : ℝ) < q := hq1
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := pow_le_pow_right₀ (le_of_lt hq1) hn
  have hr1 : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ hqn1
  have hsummabs : Summable (fun j => |ItermG q C n (n + j)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ItermG_shift_le hq hC hn j)
      (summable_geometric_of_lt_one (by positivity) hr1lt)
  have h1 : |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun j => ItermG q C n (n + j))
      (by simpa [Real.norm_eq_abs] using hsummabs)
    simpa [EtermG, Real.norm_eq_abs] using hnorm
  have hge : ∀ j, |ItermG q C n (n + j)| ≤ Cn * r ^ (n + j) := fun j =>
    ItermG_abs_le_geom hq hC hn (Nat.le_add_right n j)
  have hsummaj : Summable (fun j => Cn * r ^ (n + j)) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).mul_left _
  have h2 : ∑' j, |ItermG q C n (n + j)| ≤ ∑' j, Cn * r ^ (n + j) :=
    hsummabs.tsum_le_tsum hge hsummaj
  have h3 : ∑' j, Cn * r ^ (n + j) = Cn * r ^ n * (1 - r)⁻¹ := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  calc |EtermG q C n| ≤ ∑' j, |ItermG q C n (n + j)| := h1
    _ ≤ ∑' j, Cn * r ^ (n + j) := h2
    _ = Cn * r ^ n * (1 - r)⁻¹ := h3

/-- Clean closed form: `|Eₙ| ≤ 2·(q^{n + ∑_{k<n}k + n²})⁻¹`. -/
lemma EtermG_abs_le' (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |EtermG q C n| ≤ 2 * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  refine (EtermG_abs_le hq hC hn).trans ?_
  have hC' : (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ n
      = (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add, sq]
  have hqn2 : (2 : ℝ) ≤ q ^ n := by
    calc (2 : ℝ) ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := pow_le_pow_right₀ (le_of_lt hq1) hn
  have h1 : (q ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqn2
  have htail : (1 - (q ^ n)⁻¹)⁻¹ ≤ 2 := by
    have hb : (0 : ℝ) < 1 / 2 := by norm_num
    calc (1 - (q ^ n)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ hb (by linarith)
      _ = 2 := by norm_num
  have hCnn : (0 : ℝ) ≤ (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ :=
    le_of_lt (inv_pos.mpr (pow_pos hqpos _))
  calc (q ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((q ^ n)⁻¹) ^ n * (1 - (q ^ n)⁻¹)⁻¹
      = (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * (1 - (q ^ n)⁻¹)⁻¹ := by rw [hC']
    _ ≤ (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htail hCnn
    _ = 2 * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by ring

/-- **Wₙ growth bound** (sign-independent). `|Wₙ(C,q)| ≤ (n−2)!·(2|C|)ⁿ·(q^{∑_{k≤n}k})²` for `q ≥ 2`,
`|C| > 2`. Each `|1 − C·q^k| ≤ 1 + |C|q^k ≤ 2|C|q^k`. -/
lemma WtermG_abs_le (hq : 2 ≤ q) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |WtermG q C n| ≤ (Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n
        * q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hCnn : (0 : ℝ) ≤ 2 * |C| := by positivity
  have hfac : (0:ℝ) ≤ (Nat.factorial (n-2) : ℝ) := by positivity
  have hqS : (0:ℝ) ≤ q ^ (∑ k ∈ Finset.Icc 1 n, k) := pow_nonneg (le_of_lt hqpos) _
  rw [WtermG, abs_mul, abs_mul, abs_of_nonneg hfac]
  have hP1 : |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)| ≤ (2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ k|
        ≤ ∏ k ∈ Finset.Icc 1 n, (2 * |C|) * q ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          have hqkpos : (0:ℝ) < q ^ k := pow_pos hqpos k
          have hqk1 : (1:ℝ) ≤ q ^ k := one_le_pow₀ (le_of_lt hq1)
          have htri : |1 - C * q ^ k| ≤ 1 + |C| * q ^ k := by
            rw [show (1:ℝ) - C * q ^ k = 1 + -(C * q ^ k) from by ring]
            calc |(1:ℝ) + -(C * q ^ k)| ≤ |(1:ℝ)| + |-(C * q ^ k)| := abs_add_le _ _
              _ = 1 + |C| * q ^ k := by rw [abs_one, abs_neg, abs_mul, abs_of_pos hqkpos]
          have h2le : (2:ℝ) * 1 ≤ |C| * q ^ k :=
            mul_le_mul (le_of_lt hC) hqk1 (by norm_num) (by linarith)
          nlinarith [htri, h2le]
      _ = (2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hP2 : |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)| ≤ q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc ((n + 1) / 2) n, |1 - q ^ k|
        ≤ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, q ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          have hqk1 : (1:ℝ) ≤ q ^ k := one_le_pow₀ (le_of_lt hq1)
          rw [abs_of_nonpos (by linarith : (1 - q ^ k) ≤ 0)]
          linarith
      _ = q ^ (∑ k ∈ Finset.Icc ((n + 1) / 2) n, k) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ q ^ (∑ k ∈ Finset.Icc 1 n, k) :=
          pow_le_pow_right₀ (le_of_lt hq1)
            (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) (le_refl n)))
  calc (Nat.factorial (n - 2) : ℝ) * |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)|
        * |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)|
      ≤ (Nat.factorial (n - 2) : ℝ) * ((2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k))
          * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
        apply mul_le_mul _ hP2 (abs_nonneg _)
          (mul_nonneg hfac (mul_nonneg (pow_nonneg hCnn n) hqS))
        exact mul_le_mul_of_nonneg_left hP1 hfac
    _ = (Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n * q ^ (∑ k ∈ Finset.Icc 1 n, k)
          * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by ring

/-- **The combine majorant** (sign-independent, abstract clearing factor `B`). The cleared error
`B^{2n}·Wₙ·Eₙ` is bounded by `2·(n−2)!·(B²·2|C|)ⁿ·(q^{∑_{k<n}k})⁻¹`. -/
lemma cleared_error_leG (hq : 2 ≤ q) (hC : 2 < |C|) {B : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    |B ^ (2 * n) * WtermG q C n * EtermG q C n|
      ≤ 2 * (Nat.factorial (n - 2) : ℝ) * (B ^ 2 * (2 * |C|)) ^ n
          * (q ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by linarith
  have hCnn : (0 : ℝ) ≤ 2 * |C| := by positivity
  have hB2 : (B : ℝ) ^ (2 * n) = (B ^ 2) ^ n := by rw [pow_mul]
  have h2 : n + n ^ 2 = (∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [← two_mul, gauss_Icc n]; ring
  have hexp : n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k))
        + (∑ k ∈ Finset.Icc 1 (n - 1), k) := by omega
  have hqcancel : q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k)
        * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
      = (q ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
    rw [← pow_add, hexp]
    nth_rewrite 2 [pow_add]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hqpos _)), one_mul]
  have hWnn : (0:ℝ) ≤ (Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n
      * q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg hCnn n)) ?_) ?_ <;> exact pow_nonneg (le_of_lt hqpos) _
  have hBnn : (0:ℝ) ≤ (B : ℝ) ^ (2 * n) := by rw [hB2]; positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hBnn]
  calc (B : ℝ) ^ (2 * n) * |WtermG q C n| * |EtermG q C n|
      ≤ (B : ℝ) ^ (2 * n) * ((Nat.factorial (n - 2) : ℝ) * (2 * |C|) ^ n
          * q ^ (∑ k ∈ Finset.Icc 1 n, k) * q ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 * (q ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹) := by
        apply mul_le_mul _ (EtermG_abs_le' hq hC hn) (abs_nonneg _)
          (mul_nonneg hBnn hWnn)
        exact mul_le_mul_of_nonneg_left (WtermG_abs_le hq hC hn) hBnn
    _ = 2 * (Nat.factorial (n - 2) : ℝ) * (B ^ 2 * (2 * |C|)) ^ n
          * (q ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
        rw [hB2, mul_pow, ← hqcancel]; ring

/-- **Borwein Lemma 4 (error → 0), general `(q,C)`** (sign-independent). The cleared error
`B^{2n}·Wₙ·Eₙ → 0` for `q ≥ 2`, `|C| > 2`, any nonzero `B`. Squeeze `cleared_error_leG` against
`combine_asymptotic q (B²·2|C|)`. -/
theorem cleared_error_tendstoG (hq : 2 ≤ q) (hC : 2 < |C|) {B : ℝ} (hB : B ≠ 0) :
    Tendsto (fun n => B ^ (2 * n) * WtermG q C n * EtermG q C n) atTop (𝓝 0) := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hBC : (0 : ℝ) < B ^ 2 * (2 * |C|) := by
    have hB2 : (0:ℝ) < B ^ 2 := by positivity
    have hCp : (0:ℝ) < 2 * |C| := by positivity
    positivity
  have hg : Tendsto (fun n => 2 * ((Nat.factorial (n - 2) : ℝ) * (B ^ 2 * (2 * |C|)) ^ n
      * (q ^ (n * (n - 1) / 2))⁻¹)) atTop (𝓝 0) := by
    simpa using (combine_asymptotic q (B ^ 2 * (2 * |C|)) hq1 hBC).const_mul 2
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have h := cleared_error_leG hq hC (B := B) hn
  rw [gauss_Icc' n] at h
  refine h.trans (le_of_eq ?_)
  ring

/- ### Cleared error → 0 for negative base `q ≤ -2` (Lemma 4 endgame, `2 ≤ |q|`). -/

/-- **Wₙ growth bound, negative base** `|Wₙ(C,q)| ≤ (n−2)!·(4|C|)ⁿ·|q|^{2∑_{k≤n}k}`. Each
`|1 − C·q^k| ≤ 2|C||q|^k` and `|1 − q^k| ≤ 2|q|^k` (the cross-term `2`'s give the `4ⁿ` vs the
positive-base `2ⁿ`). -/
lemma WtermG_abs_le_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    |WtermG q C n| ≤ (Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n
        * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hfac : (0 : ℝ) ≤ (Nat.factorial (n - 2) : ℝ) := by positivity
  have hqS : (0 : ℝ) ≤ |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := pow_nonneg (le_of_lt hqpos) _
  rw [WtermG, abs_mul, abs_mul, abs_of_nonneg hfac]
  have hP1 : |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)|
      ≤ (2 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 n, |1 - C * q ^ k|
        ≤ ∏ k ∈ Finset.Icc 1 n, (2 * |C|) * |q| ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          have hqk1 : (1 : ℝ) ≤ |q| ^ k := one_le_pow₀ (le_of_lt hqabs1)
          have htri : |1 - C * q ^ k| ≤ 1 + |C| * |q| ^ k := by
            calc |1 - C * q ^ k| = |(1 : ℝ) + -(C * q ^ k)| := by rw [sub_eq_add_neg]
              _ ≤ |(1 : ℝ)| + |-(C * q ^ k)| := abs_add_le _ _
              _ = 1 + |C| * |q| ^ k := by rw [abs_one, abs_neg, abs_mul, abs_pow]
          have h2le : (2 : ℝ) * 1 ≤ |C| * |q| ^ k :=
            mul_le_mul (le_of_lt hC) hqk1 (by norm_num) (by linarith)
          nlinarith [htri, h2le]
      _ = (2 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hP2 : |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)|
      ≤ 2 ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc ((n + 1) / 2) n, |1 - q ^ k|
        ≤ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (2 * |q| ^ k) := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk
          have hqk1 : (1 : ℝ) ≤ |q| ^ k := one_le_pow₀ (le_of_lt hqabs1)
          calc |1 - q ^ k| = |(1 : ℝ) + -(q ^ k)| := by rw [sub_eq_add_neg]
            _ ≤ |(1 : ℝ)| + |-(q ^ k)| := abs_add_le _ _
            _ = 1 + |q| ^ k := by rw [abs_one, abs_neg, abs_pow]
            _ ≤ 2 * |q| ^ k := by linarith
      _ = 2 ^ ((Finset.Icc ((n + 1) / 2) n).card) * |q| ^ (∑ k ∈ Finset.Icc ((n + 1) / 2) n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
      _ ≤ 2 ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          have hsub : Finset.Icc ((n + 1) / 2) n ⊆ Finset.Icc 1 n :=
            Finset.Icc_subset_Icc (by omega) (le_refl n)
          have hcard : (Finset.Icc ((n + 1) / 2) n).card ≤ n := by
            calc (Finset.Icc ((n + 1) / 2) n).card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
              _ = n := by rw [Nat.card_Icc, Nat.add_sub_cancel]
          apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard)
            (pow_le_pow_right₀ (le_of_lt hqabs1) (Finset.sum_le_sum_of_subset hsub))
            (pow_nonneg (le_of_lt hqpos) _) (by positivity)
  calc (Nat.factorial (n - 2) : ℝ) * |∏ k ∈ Finset.Icc 1 n, (1 - C * q ^ k)|
        * |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - q ^ k)|
      ≤ (Nat.factorial (n - 2) : ℝ) * ((2 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k)) := by
        apply mul_le_mul _ hP2 (abs_nonneg _)
          (mul_nonneg hfac (mul_nonneg (pow_nonneg (by positivity) n) hqS))
        exact mul_le_mul_of_nonneg_left hP1 hfac
    _ = (Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n * |q| ^ (∑ k ∈ Finset.Icc 1 n, k)
          * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
        have hconst : (4 * |C|) ^ n = (2 * |C|) ^ n * 2 ^ n := by rw [← mul_pow]; congr 1; ring
        rw [hconst]; ring

/-- **The combine majorant, negative base** (abstract clearing factor `B`): the cleared error
`B^{2n}·Wₙ·Eₙ` is bounded by `(n−2)!·(8·B²·|C|)ⁿ·(|q|^{∑_{k<n}k})⁻¹`. -/
lemma cleared_error_leG_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {B : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    |B ^ (2 * n) * WtermG q C n * EtermG q C n|
      ≤ (Nat.factorial (n - 2) : ℝ) * (8 * (B ^ 2 * |C|)) ^ n
          * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
  have hqpos : (0 : ℝ) < |q| := by linarith
  have hB2 : (B : ℝ) ^ (2 * n) = (B ^ 2) ^ n := by rw [pow_mul]
  have hexp : n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k))
        + (∑ k ∈ Finset.Icc 1 (n - 1), k) := by
    have h2 : n + n ^ 2 = (∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k) := by
      rw [← two_mul, gauss_Icc n]; ring
    omega
  have hqcancel : |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k)
        * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
      = (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
    rw [← pow_add, hexp]
    nth_rewrite 2 [pow_add]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hqpos _)), one_mul]
  have hWnn : (0 : ℝ) ≤ (Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n
      * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_) ?_ <;>
      exact pow_nonneg (le_of_lt hqpos) _
  have hBnn : (0 : ℝ) ≤ (B : ℝ) ^ (2 * n) := by rw [hB2]; positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hBnn]
  calc (B : ℝ) ^ (2 * n) * |WtermG q C n| * |EtermG q C n|
      ≤ (B : ℝ) ^ (2 * n) * ((Nat.factorial (n - 2) : ℝ) * (4 * |C|) ^ n
          * |q| ^ (∑ k ∈ Finset.Icc 1 n, k) * |q| ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 ^ n * (|q| ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹) := by
        apply mul_le_mul _ (EtermG_abs_le'_abs hq hC hn) (abs_nonneg _) (mul_nonneg hBnn hWnn)
        exact mul_le_mul_of_nonneg_left (WtermG_abs_le_abs hq hC hn) hBnn
    _ = (Nat.factorial (n - 2) : ℝ) * (8 * (B ^ 2 * |C|)) ^ n
          * (|q| ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
        rw [hB2, show (8 : ℝ) * (B ^ 2 * |C|) = B ^ 2 * (4 * |C|) * 2 from by ring,
          mul_pow, mul_pow, ← hqcancel]; ring

/-- **Borwein Lemma 4 (error → 0), negative base** `q ≤ -2` (`2 ≤ |q|`, `2 < |C|`, any nonzero `B`).
The cleared error `B^{2n}·Wₙ·Eₙ → 0`, squeezing `cleared_error_leG_abs` against
`combine_asymptotic |q| (8·B²·|C|)`. -/
theorem cleared_error_tendstoG_abs (hq : 2 ≤ |q|) (hC : 2 < |C|) {B : ℝ} (hB : B ≠ 0) :
    Tendsto (fun n => B ^ (2 * n) * WtermG q C n * EtermG q C n) atTop (𝓝 0) := by
  have hqabs1 : (1 : ℝ) < |q| := by linarith
  have hBC : (0 : ℝ) < 8 * (B ^ 2 * |C|) := by
    have hB2 : (0 : ℝ) < B ^ 2 := by positivity
    have hCp : (0 : ℝ) < |C| := by linarith
    positivity
  have hg : Tendsto (fun n => (Nat.factorial (n - 2) : ℝ) * (8 * (B ^ 2 * |C|)) ^ n
      * (|q| ^ (n * (n - 1) / 2))⁻¹) atTop (𝓝 0) := by
    simpa using combine_asymptotic |q| (8 * (B ^ 2 * |C|)) hqabs1 hBC
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have h := cleared_error_leG_abs hq hC (B := B) hn
  rw [gauss_Icc' n] at h
  exact h

/-- **Lemma 5, negative base, `n` odd.** `(−1)^{nj}=(−1)^j`, so the terms `EsignG C n n · Iₙ(n+j)`
ALTERNATE in sign, with magnitudes `f j = |σ|·|Iₙ(n+j)|` strictly antitone (`ItermG_abs_anti_negbase`)
and `f 0 > f 1`. The alternating-series bracket gives `σ·Eₙ ≥ f 0 − f 1 > 0`, hence `Eₙ ≠ 0`. -/
theorem EtermG_ne_zero_odd_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n : ℕ}
    (hn : 1 ≤ n) (hno : Odd n) : EtermG q C n ≠ 0 := by
  have hqabs : (2 : ℝ) ≤ |q| := by rw [abs_of_neg (show q < 0 by linarith)]; linarith
  set σ := EsignG C n n with hσ
  set f : ℕ → ℝ := fun j => (-1) ^ j * σ * ItermG q C n (n + j) with hf
  have hfpos : ∀ j, 0 < f j := by
    intro j
    have h := ItermG_sign_negbase hq hC hn (Nat.le_add_right n j)
    rw [EsignG_shift hn, ← hσ] at h
    have hpar : (-1 : ℝ) ^ (n * j) = (-1) ^ j := by
      rcases hno with ⟨t, ht⟩
      rw [ht, show (2 * t + 1) * j = 2 * (t * j) + j from by ring, pow_add, pow_mul, neg_one_sq,
        one_pow, one_mul]
    rw [hpar] at h
    exact h
  have hσne : σ ≠ 0 := fun h0 => by
    have h := hfpos 0
    rw [hf] at h
    simp only [pow_zero, one_mul, Nat.add_zero] at h
    rw [h0, zero_mul] at h
    exact lt_irrefl 0 h
  have hfeq : ∀ j, f j = |σ| * |ItermG q C n (n + j)| := by
    intro j
    rw [← abs_of_pos (hfpos j), hf]
    simp only
    rw [abs_mul, abs_mul, abs_pow, show |(-1 : ℝ)| = 1 from by norm_num, one_pow, one_mul]
  have hf_anti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro j
    rw [hfeq, hfeq]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg σ)
    rw [show n + (j + 1) = (n + j) + 1 from by ring]
    exact le_of_lt (ItermG_abs_anti_negbase hq hC hn (by omega))
  have hf01 : f 1 < f 0 := by
    rw [hfeq, hfeq, show n + 0 = n from by ring]
    exact mul_lt_mul_of_pos_left (ItermG_abs_anti_negbase hq hC hn (le_refl n)) (abs_pos.mpr hσne)
  have hfsum : Summable f := by
    apply Summable.of_norm_bounded (g := fun j => |σ| * (|q|⁻¹) ^ j)
    · exact (summable_geometric_of_lt_one (by positivity)
        (show |q|⁻¹ < 1 by rw [inv_lt_one_iff₀]; right; linarith)).mul_left _
    · intro j
      rw [Real.norm_eq_abs, abs_of_pos (hfpos j), hfeq j]
      exact mul_le_mul_of_nonneg_left (ItermG_shift_le_abs hqabs hC hn j) (abs_nonneg σ)
  have htend := hfsum.tendsto_alternating_series_tsum
  have hbr := hf_anti.alternating_series_le_tendsto htend 1
  simp only [Nat.mul_one] at hbr
  have hsum2 : (∑ i ∈ Finset.range 2, (-1 : ℝ) ^ i * f i) = f 0 - f 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]; ring
  rw [hsum2] at hbr
  have hlval : (∑' i, (-1 : ℝ) ^ i * f i) = σ * EtermG q C n := by
    have hterm : ∀ i, (-1 : ℝ) ^ i * f i = σ * ItermG q C n (n + i) := by
      intro i
      rw [hf]
      simp only
      rw [show (-1 : ℝ) ^ i * ((-1) ^ i * σ * ItermG q C n (n + i))
            = ((-1) ^ i * (-1) ^ i) * (σ * ItermG q C n (n + i)) from by ring,
        show (-1 : ℝ) ^ i * (-1) ^ i = 1 from by rw [← pow_add]; exact Even.neg_one_pow ⟨i, rfl⟩,
        one_mul]
    rw [tsum_congr hterm, tsum_mul_left]; rfl
  rw [hlval] at hbr
  have hSE : 0 < σ * EtermG q C n := lt_of_lt_of_le (by linarith [hf01]) hbr
  intro h0
  rw [h0, mul_zero] at hSE
  exact lt_irrefl 0 hSE

/-- **Borwein Lemma 5 (non-vanishing), negative base `q ≤ -2`.** `EtermG q C n ≠ 0` for `n ≥ 1`,
`2 < |C|`. The sign DICHOTOMY: `n` even ⟹ same-sign terms (`EtermG_ne_zero_even_negbase`);
`n` odd ⟹ alternating series (`EtermG_ne_zero_odd_negbase`). -/
theorem EtermG_ne_zero_negbase (hq : q ≤ -2) (hC : 2 < |C|) {n : ℕ} (hn : 1 ≤ n) :
    EtermG q C n ≠ 0 := by
  rcases Nat.even_or_odd n with he | ho
  · exact EtermG_ne_zero_even_negbase hq hC hn he
  · exact EtermG_ne_zero_odd_negbase hq hC hn ho

end LeanGallery.NumberTheory.Erdos1050

end

-- LeanGallery/NumberTheory/Erdos1050/GeneralAssembly.lean
section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-
# Borwein Theorem 1 — full assembly for the `C > 2` regime (no cited axiom)

With all five Borwein lemmas now general and machine-checked —
* Lemma 1 (residue identity) `EtermG_eq_pValG`,
* Lemma 2 (denominator integrality) `BdenG_cast`,
* Lemma 3 (numerator integrality) `AcorrG_int`, assembled with 1+2 into `borwein_integralityG`,
* Lemma 4 (error → 0) `cleared_error_tendstoG`,
* Lemma 5 (non-vanishing) `EtermG_ne_zero` —
the integer-approximant existence `borwein_approximants` is now a **THEOREM** (not a cited axiom) for
integer `q ≥ 2` and `C = α/β > 2` (Borwein's shifted magnitude regime). Hence the reduced q-harmonic
value `z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹` is **unconditionally irrational** for every such `(q, C)` — no
appeal to `borwein_approximants`.
-/

namespace LeanGallery.NumberTheory.Erdos1050

open scoped BigOperators
open Filter Topology

/-- **Borwein's integer approximants — a THEOREM for `|C| = |α/β| > 2`** (general analog of the
discharged `q=2` chain, with no cited axiom). For integer `q ≥ 2` and `α, β` with `|α/β| > 2`, there are
integer sequences `aₙ, bₙ` with `bₙ·z − aₙ ≠ 0` and `bₙ·z − aₙ → 0`, where
`z = ∑_{j≥0}(1 − (α/β)·q^{j+1})⁻¹`. Exactly the conclusion of the `borwein_approximants` axiom for the
`(q, α/β)` instances with `|α/β| > 2` (both signs — non-vanishing by Lemma 5's positive/negative
regimes; error → 0 by the sign-independent Lemma 4). -/
theorem borwein_approximantsG {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    ∃ a b : ℕ → ℤ,
      (∀ n, (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n ≠ 0) ∧
      Tendsto (fun n => (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n) atTop (𝓝 0) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  -- `|C| > 2` makes every `|C·q^{h+1}| ≥ |C| > 2 > 1`, so the non-degeneracy hypothesis is automatic.
  have hCn : ∀ h : ℕ, ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1) ≠ 1 := by
    intro h hcontra
    have hqp : (1 : ℝ) ≤ (q : ℝ) ^ (h + 1) := one_le_pow₀ (by linarith)
    have habs : |((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1)| = 1 := by rw [hcontra]; norm_num
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ (h + 1))] at habs
    nlinarith [hC2, hqp, habs]
  -- non-vanishing of the error term, by the sign regime of `C`.
  have hEne : ∀ k, 1 ≤ k → EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) k ≠ 0 := by
    intro k hk
    rcases lt_abs.mp hC2 with hCp | hCm
    · exact EtermG_ne_zero hq2 hCp hk
    · exact EtermG_ne_zero_neg hq2 (by linarith : (α : ℝ) / (β : ℝ) < -2) hk
  have hqabs : 2 ≤ |q| := by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ q)]; exact hq
  obtain ⟨a, b, hab⟩ := borwein_integralityG hqabs hα hβ hCn
  -- Shift the index by 1 to land in `n ≥ 1`, where the identity and Lemmas 4/5 apply.
  refine ⟨fun n => a (n + 1), fun n => b (n + 1), ?_, ?_⟩
  · intro n
    rw [hab (n + 1) (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ (WtermG_ne_zero hq1 hCn (by omega)))
      (hEne (n + 1) (by omega))
    exact pow_ne_zero _ hβ0
  · have hshift : Tendsto (fun n => (β : ℝ) ^ (2 * (n + 1))
        * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)
        * EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)) atTop (𝓝 0) :=
      (cleared_error_tendstoG hq2 hC2 hβ0).comp (tendsto_add_atTop_nat 1)
    exact hshift.congr (fun n => (hab (n + 1) (by omega)).symm)

/-- **Borwein Theorem 1, reduced q-harmonic value, UNCONDITIONAL for `|C| = |α/β| > 2`.** The value
`z = ∑_{j≥0}(1 − (α/β)·q^{j+1})⁻¹` is irrational for integer `q ≥ 2` and `|α/β| > 2` (both signs), with
**no cited axiom** — every Borwein lemma is machine-checked. -/
theorem zG_irrational_of_abs_gt_two {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  obtain ⟨a, b, hne, hlim⟩ := borwein_approximantsG hq hα hβ hC2
  exact irrational_of_intApprox _ a b hne hlim

/- ## The magnitude shift `C → C·qᵐ` — extending to all `C = α/β > 0`

`z = ∑_{j≥0}(1 − C·q^{j+1})⁻¹` and `z' = ∑_{j≥0}(1 − (C·qᵐ)·q^{j+1})⁻¹` differ by the finite rational
head `∑_{j<m}(1 − C·q^{j+1})⁻¹` (`z = head + z'`). For `C > 0` the shifted parameter `C·qᵐ → ∞`, so some
`m` lands in the `> 2` regime; then `z'` is irrational by `zG_irrational_of_gt_two`, hence so is `z`.
This is Borwein's reduction remark (`c → c·qᵐ` to reach `|c| > 2`), in the reduced parametrisation. -/

/-- **Shift decomposition**: `z(C) = (finite head) + z(C·qᵐ)`, for `2 ≤ |q|`, `C ≠ 0`. The tail of the
`z(C)` series is exactly the `z(C·qᵐ)` series (reindex `j ↦ j+m`). -/
lemma zG_shift {q C : ℝ} (hq : 2 ≤ |q|) (hC : C ≠ 0) (m : ℕ) :
    zG q C = (∑ j ∈ Finset.range m, (1 - C * q ^ (j + 1))⁻¹) + zG q (C * q ^ m) := by
  have hsum := qharmonic_summable q C hq hC
  unfold zG
  rw [← Summable.sum_add_tsum_nat_add m hsum]
  congr 1
  apply tsum_congr
  intro i
  rw [show (i + m) + 1 = (i + 1) + m from by ring, pow_add]
  ring

/-- **Borwein Theorem 1, UNCONDITIONAL for `C = α/β > 0`** (no cited axiom). For integer `q ≥ 2` and
`α, β` with `α/β > 0`, the value `z = ∑_{j≥0}(1 − (α/β)·q^{j+1})⁻¹` is irrational. Proof: shift
`C → C·qᵐ` with `m` large enough that `C·qᵐ > 2`; `z = (rational head) + z(C·qᵐ)`, and `z(C·qᵐ)` is
irrational by `zG_irrational_of_gt_two`. Extends the `> 2` family to the entire positive half-line. -/
theorem zG_irrational_of_pos {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hCpos : 0 < (α : ℝ) / (β : ℝ)) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [abs_of_pos (by linarith)]; exact hq2
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hC0 : ((α : ℝ) / (β : ℝ)) ≠ 0 := ne_of_gt hCpos
  -- pick `m` with `C·qᵐ > 2` (since `C > 0` and `qᵐ → ∞`)
  have htend : Tendsto (fun m : ℕ => ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m) atTop atTop :=
    Tendsto.const_mul_atTop hCpos (tendsto_pow_atTop_atTop_of_one_lt hq1)
  obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop 2).exists
  -- the shifted value is irrational (`> 2` regime), via the integer numerator `α·qᵐ`
  have hαqm : (α * q ^ m : ℤ) ≠ 0 := mul_ne_zero hα (pow_ne_zero _ (by omega : (q : ℤ) ≠ 0))
  have hCqm_eq : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) = ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m := by
    push_cast; ring
  have hC2 : 2 < ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) := by rw [hCqm_eq]; exact hm
  have hC2abs : 2 < |((α * q ^ m : ℤ) : ℝ) / (β : ℝ)| := by rw [abs_of_pos (by linarith)]; exact hC2
  have h_tail : Irrational (zG (q : ℝ) (((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m)) := by
    have := zG_irrational_of_abs_gt_two hq hαqm hβ hC2abs
    rwa [hCqm_eq] at this
  -- decompose and transfer irrationality across the rational head
  rw [zG_shift hqabs hC0 m]
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = ∑ j ∈ Finset.range m, (1 - (α : ℝ) / (β : ℝ) * (q : ℝ) ^ (j + 1))⁻¹ := by
    refine ⟨∑ j ∈ Finset.range m, (1 - (α : ℚ) / (β : ℚ) * (q : ℚ) ^ (j + 1))⁻¹, ?_⟩
    push_cast
    rfl
  rw [← hr]
  exact irrational_ratCast_add_iff.mpr h_tail

/-- **Borwein Theorem 1, UNCONDITIONAL for `C = α/β < 0`** (no cited axiom). Mirror of
`zG_irrational_of_pos`: for `C < 0`, `C·qᵐ → −∞`, so some `m` lands `C·qᵐ < −2` (`|·| > 2` regime);
`z = (rational head) + z(C·qᵐ)` then transfers irrationality. -/
theorem zG_irrational_of_neg {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hCneg : (α : ℝ) / (β : ℝ) < 0) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [abs_of_pos (by linarith)]; exact hq2
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hC0 : ((α : ℝ) / (β : ℝ)) ≠ 0 := ne_of_lt hCneg
  -- pick `m` with `C·qᵐ < −2` (since `−C > 0` and `qᵐ → ∞`)
  have htend : Tendsto (fun m : ℕ => (-((α : ℝ) / (β : ℝ))) * (q : ℝ) ^ m) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < -((α : ℝ) / (β : ℝ)))
      (tendsto_pow_atTop_atTop_of_one_lt hq1)
  obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop 2).exists
  have hαqm : (α * q ^ m : ℤ) ≠ 0 := mul_ne_zero hα (pow_ne_zero _ (by omega : (q : ℤ) ≠ 0))
  have hCqm_eq : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) = ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m := by
    push_cast; ring
  have hCqm_neg : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) < -2 := by rw [hCqm_eq]; nlinarith [hm]
  have hC2abs : 2 < |((α * q ^ m : ℤ) : ℝ) / (β : ℝ)| := by
    rw [abs_of_neg (by linarith)]; linarith
  have h_tail : Irrational (zG (q : ℝ) (((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m)) := by
    have := zG_irrational_of_abs_gt_two hq hαqm hβ hC2abs
    rwa [hCqm_eq] at this
  rw [zG_shift hqabs hC0 m]
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = ∑ j ∈ Finset.range m, (1 - (α : ℝ) / (β : ℝ) * (q : ℝ) ^ (j + 1))⁻¹ := by
    refine ⟨∑ j ∈ Finset.range m, (1 - (α : ℚ) / (β : ℚ) * (q : ℚ) ^ (j + 1))⁻¹, ?_⟩
    push_cast
    rfl
  rw [← hr]
  exact irrational_ratCast_add_iff.mpr h_tail

/-- **Borwein Theorem 1, reduced value, UNCONDITIONAL for every nonzero `C = α/β`** (`q ≥ 2`), no cited
axiom. Combines the positive (`zG_irrational_of_pos`) and negative (`zG_irrational_of_neg`) regimes. -/
theorem zG_irrational {q α β : ℤ} (hq : 2 ≤ q) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC0 : (α : ℝ) / (β : ℝ) ≠ 0) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  rcases lt_or_gt_of_ne hC0 with h | h
  · exact zG_irrational_of_neg hq hα hβ h
  · exact zG_irrational_of_pos hq hα hβ h

/- ## NEGATIVE base `q ≤ −2`: the full axiom-free chain for `2 ≤ |q|` (both signs of base)

Mirrors the positive-base assembly, routing non-vanishing through `EtermG_ne_zero_negbase`
(the sign dichotomy) for `q ≤ −2`. The magnitude shift uses `|C·qᵐ| = |C|·|q|ᵐ → ∞`, which lands
some `m` in the `|·| > 2` regime regardless of the alternating sign of `qᵐ`. -/

/-- **Borwein approximants, both signs of integer base** (`2 ≤ |q|`, `|α/β| > 2`), no cited axiom. -/
theorem borwein_approximantsG_abs {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    ∃ a b : ℕ → ℤ,
      (∀ n, (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n ≠ 0) ∧
      Tendsto (fun n => (b n : ℝ) * zG (q : ℝ) ((α : ℝ) / (β : ℝ)) - a n) atTop (𝓝 0) := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by linarith
  have hβ0 : (β : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hβ
  have hCn : ∀ h : ℕ, ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1) ≠ 1 := by
    intro h hcontra
    have hqp : (1 : ℝ) ≤ |(q : ℝ)| ^ (h + 1) := one_le_pow₀ (by linarith)
    have habs : |((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ (h + 1)| = 1 := by rw [hcontra]; norm_num
    rw [abs_mul, abs_pow] at habs
    nlinarith [hC2, hqp, habs, abs_nonneg ((α : ℝ) / (β : ℝ)),
      mul_le_mul (le_of_lt hC2) hqp zero_le_one (abs_nonneg ((α : ℝ) / (β : ℝ)))]
  have hEne : ∀ k, 1 ≤ k → EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) k ≠ 0 := by
    intro k hk
    by_cases hq0 : 0 ≤ q
    · have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
        rwa [abs_of_nonneg (by exact_mod_cast hq0 : (0 : ℝ) ≤ (q : ℝ))] at hqabs
      rcases lt_abs.mp hC2 with hCp | hCm
      · exact EtermG_ne_zero hq2 hCp hk
      · exact EtermG_ne_zero_neg hq2 (by linarith) hk
    · push Not at hq0
      have hqn2 : (q : ℝ) ≤ -2 := by
        rw [abs_of_neg (by exact_mod_cast hq0 : (q : ℝ) < 0)] at hqabs; linarith
      exact EtermG_ne_zero_negbase hqn2 hC2 hk
  obtain ⟨a, b, hab⟩ := borwein_integralityG hq hα hβ hCn
  refine ⟨fun n => a (n + 1), fun n => b (n + 1), ?_, ?_⟩
  · intro n
    rw [hab (n + 1) (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ (WtermG_ne_zero_abs hq1abs hCn (by omega)))
      (hEne (n + 1) (by omega))
    exact pow_ne_zero _ hβ0
  · have hshift : Tendsto (fun n => (β : ℝ) ^ (2 * (n + 1))
        * WtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)
        * EtermG (q : ℝ) ((α : ℝ) / (β : ℝ)) (n + 1)) atTop (𝓝 0) :=
      (cleared_error_tendstoG_abs hqabs hC2 hβ0).comp (tendsto_add_atTop_nat 1)
    exact hshift.congr (fun n => (hab (n + 1) (by omega)).symm)

/-- Reduced value irrational for `2 ≤ |q|`, `|α/β| > 2`. -/
theorem zG_irrational_of_abs_gt_two_abs {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC2 : 2 < |(α : ℝ) / (β : ℝ)|) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  obtain ⟨a, b, hne, hlim⟩ := borwein_approximantsG_abs hq hα hβ hC2
  exact irrational_of_intApprox _ a b hne hlim

/-- **Reduced value irrational, every nonzero `C`, both signs of base** (`2 ≤ |q|`), no cited axiom.
The magnitude shift `C → C·qᵐ` reaches `|C·qᵐ| = |C|·|q|ᵐ > 2` for large `m` (works for `q < 0` too,
since only the magnitude matters); `z = (rational head) + z(C·qᵐ)` then transfers irrationality. -/
theorem zG_irrational_abs {q α β : ℤ} (hq : 2 ≤ |q|) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hC0 : (α : ℝ) / (β : ℝ) ≠ 0) :
    Irrational (zG (q : ℝ) ((α : ℝ) / (β : ℝ))) := by
  have hqabs : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq
  have hq1abs : (1 : ℝ) < |(q : ℝ)| := by linarith
  have hqZ : (q : ℤ) ≠ 0 := by rintro rfl; norm_num at hq
  have htend : Tendsto (fun m : ℕ => |(α : ℝ) / (β : ℝ)| * |(q : ℝ)| ^ m) atTop atTop :=
    Tendsto.const_mul_atTop (abs_pos.mpr hC0) (tendsto_pow_atTop_atTop_of_one_lt hq1abs)
  obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop 2).exists
  have hαqm : (α * q ^ m : ℤ) ≠ 0 := mul_ne_zero hα (pow_ne_zero _ hqZ)
  have hCqm_eq : ((α * q ^ m : ℤ) : ℝ) / (β : ℝ) = ((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m := by
    push_cast; ring
  have hC2abs : 2 < |((α * q ^ m : ℤ) : ℝ) / (β : ℝ)| := by rw [hCqm_eq, abs_mul, abs_pow]; exact hm
  have h_tail : Irrational (zG (q : ℝ) (((α : ℝ) / (β : ℝ)) * (q : ℝ) ^ m)) := by
    have := zG_irrational_of_abs_gt_two_abs hq hαqm hβ hC2abs
    rwa [hCqm_eq] at this
  rw [zG_shift hqabs hC0 m]
  obtain ⟨r, hr⟩ : ∃ r : ℚ,
      (r : ℝ) = ∑ j ∈ Finset.range m, (1 - (α : ℝ) / (β : ℝ) * (q : ℝ) ^ (j + 1))⁻¹ := by
    refine ⟨∑ j ∈ Finset.range m, (1 - (α : ℚ) / (β : ℚ) * (q : ℚ) ^ (j + 1))⁻¹, ?_⟩
    push_cast; rfl
  rw [← hr]
  exact irrational_ratCast_add_iff.mpr h_tail

/- ## Axiom-free headline corollaries (all nonzero `C`, all `c`; `q ≥ 2`) -/

/-- **Borwein Theorem 1, reduced form, AXIOM-FREE for `C > 0`.** The reduced q-harmonic value
`∑_{n≥0}(1 − C·q^{n+1})⁻¹` is irrational for every integer `q ≥ 2` and rational `C` with `(C:ℝ) > 0`.
This is the axiom-free analog of `qharmonic_irrational` (which routes through `borwein_approximants`),
covering both `C`-signs. -/
theorem qharmonic_irrational' (q : ℤ) (hq : 2 ≤ q) (C : ℚ) (hCne : C ≠ 0) :
    Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) := by
  have hαne : C.num ≠ 0 := Rat.num_ne_zero.mpr hCne
  have hβne : (C.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr C.den_nz
  have hcast : ((C.num : ℝ) / ((C.den : ℤ) : ℝ)) = (C : ℝ) := by
    push_cast; exact (Rat.cast_def C).symm
  have hC0 : (C.num : ℝ) / ((C.den : ℤ) : ℝ) ≠ 0 := by rw [hcast]; exact Rat.cast_ne_zero.mpr hCne
  have h := zG_irrational hq hαne hβne hC0
  rw [hcast] at h
  exact h

/-- **Borwein Theorem 1, FULLY AXIOM-FREE for every nonzero `c`** (and `q ≥ 2`). The series
`∑_{n≥1} 1/(qⁿ + c)` is irrational for integer `q ≥ 2` and any nonzero rational `c` with `qⁿ⁺¹ + c ≠ 0`.
**No appeal to `borwein_approximants`** — every one of Borwein's five lemmas is machine-checked, and the
magnitude shift `c → c·qᵐ` covers all `c`. (The original `borwein_thm1` allows `q ≤ −2` too but cites
the axiom; this is the axiom-free version for positive base `q ≥ 2`.) -/
theorem borwein_thm1' (q : ℤ) (hq : 2 ≤ q) (c : ℚ) (hc0 : c ≠ 0)
    (hcn : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) := by
  set C : ℚ := -1 / c with hCdef
  have hCne : C ≠ 0 := by
    rw [hCdef]; intro h; rw [div_eq_zero_iff] at h
    rcases h with h | h
    · norm_num at h
    · exact hc0 h
  -- Affine identity (unconditional): `c · ∑ 1/(qⁿ+c) = ∑ (1 − C·qⁿ)⁻¹` (as in `borwein_thm1`).
  have key : (c : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ)))
      = ∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hden : (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0 := hcn n
    rw [hCdef]
    push_cast
    generalize hx : (q : ℝ) ^ (n + 1) = x at hden ⊢
    field_simp
    rw [eq_div_iff (show (c : ℝ) - -x ≠ 0 by rw [sub_neg_eq_add, add_comm]; exact hden)]
    ring
  have hirr : Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) :=
    qharmonic_irrational' q hq C hCne
  rw [← key] at hirr
  exact (irrational_ratCast_mul_iff.mp hirr).2

/- ## Axiom-free headlines for `2 ≤ |q|` (both signs of base) — the discharge of `borwein_approximants` -/

/-- **Borwein Theorem 1, reduced form, AXIOM-FREE for `2 ≤ |q|`** (both signs of base). -/
theorem qharmonic_irrational_abs (q : ℤ) (hq : 2 ≤ |q|) (C : ℚ) (hCne : C ≠ 0) :
    Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) := by
  have hαne : C.num ≠ 0 := Rat.num_ne_zero.mpr hCne
  have hβne : (C.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr C.den_nz
  have hcast : ((C.num : ℝ) / ((C.den : ℤ) : ℝ)) = (C : ℝ) := by
    push_cast; exact (Rat.cast_def C).symm
  have hC0 : (C.num : ℝ) / ((C.den : ℤ) : ℝ) ≠ 0 := by rw [hcast]; exact Rat.cast_ne_zero.mpr hCne
  have h := zG_irrational_abs hq hαne hβne hC0
  rw [hcast] at h
  exact h

/-- **Borwein's Theorem 1, FULLY AXIOM-FREE for `2 ≤ |q|`** (integer base of either sign, every nonzero
rational `c`). The series `∑_{n≥1} 1/(qⁿ + c)` is irrational. **No appeal to `borwein_approximants`** —
all five Borwein lemmas (incl. Lemma 5 non-vanishing for negative base via the sign dichotomy) are
machine-checked. This discharges the `borwein_approximants` axiom entirely. -/
theorem borwein_thm1_abs (q : ℤ) (hq : 2 ≤ |q|) (c : ℚ) (hc0 : c ≠ 0)
    (hcn : ∀ n : ℕ, (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0) :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ))) := by
  set C : ℚ := -1 / c with hCdef
  have hCne : C ≠ 0 := by
    rw [hCdef]; intro h; rw [div_eq_zero_iff] at h
    rcases h with h | h
    · norm_num at h
    · exact hc0 h
  have key : (c : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (c : ℝ)))
      = ∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hden : (q : ℝ) ^ (n + 1) + (c : ℝ) ≠ 0 := hcn n
    rw [hCdef]
    push_cast
    generalize hx : (q : ℝ) ^ (n + 1) = x at hden ⊢
    field_simp
    rw [eq_div_iff (show (c : ℝ) - -x ≠ 0 by rw [sub_neg_eq_add, add_comm]; exact hden)]
    ring
  have hirr : Irrational (∑' n : ℕ, (1 - (C : ℝ) * (q : ℝ) ^ (n + 1))⁻¹) :=
    qharmonic_irrational_abs q hq C hCne
  rw [← key] at hirr
  exact (irrational_ratCast_mul_iff.mp hirr).2

/-- The reduced Erdős–Borwein-type series `∑_{n≥1} 1/(2ⁿ − 1)`, now axiom-free (`q = 2`). -/
theorem irrational_sum_two_pow_sub_one_abs :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) := by
  have h := borwein_thm1_abs 2 (by norm_num) (-1) (by norm_num) (by
    intro n
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    intro hc; push_cast at hc; linarith)
  have hcongr : (fun n : ℕ => (1 : ℝ) / (((2 : ℤ) : ℝ) ^ (n + 1) + ((-1 : ℚ) : ℝ)))
      = fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) := by
    funext n; push_cast; ring_nf
  rwa [hcongr] at h

end LeanGallery.NumberTheory.Erdos1050

end

theorem OMA.solution : OMA.R_Erdos1050_erdos_1050_variants_transcendental_R1.H1 := by
  intro t ht hshift
  have hr : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  have hne (n : ℕ) : (2 : ℝ) ^ (n + 1) + (t : ℝ) ≠ 0 := by
    intro h
    apply hshift (n + 1) n.succ_pos
    have hreal : (t : ℝ) = -(2 : ℝ) ^ (n + 1) := by linarith
    exact_mod_cast hreal
  have htwo : (2 : ℤ) ≤ |(2 : ℤ)| := by norm_num
  simpa only [Int.cast_ofNat, Rat.cast_intCast] using
    LeanGallery.NumberTheory.Erdos1050.borwein_thm1_abs 2 htwo (t : ℚ)
      hr (by simpa only [Int.cast_ofNat, Rat.cast_intCast] using hne)
