import FormalConjectures.ErdosProblems.«643»

-- Reduction Erdos643.erdos_643.parts.ii.R3 of Erdős Problem 643 (part ii)
-- Credit: @Salofe

/-!
# Erdős 643 (ii): star lower bound and the asymptotic upper bound

Let `e(n)` be the largest number of `t`-sets on `n` labelled vertices containing no two distinct
disjoint pairs with the same union. The forcing threshold is `e(n) + 1`, and the problem asks
whether it is asymptotic to `C(n, t - 1)` for `t ≥ 3`.

* `H1` (the star lower bound): for `1 ≤ t ≤ n`, the `C(n - 1, t - 1)` sets of size `t` through a
  fixed vertex pairwise intersect, so no two of them are disjoint and the family is admissible.
  Hence `C(n - 1, t - 1) ≤ e(n)`.
* `H2` (the open upper bound): for `t ≥ 3` and every `ε > 0`, eventually
  `e(n) ≤ (1 + ε) C(n, t - 1)`.

Since `C(n - 1, t - 1) = C(n, t - 1) (1 - (t - 1) / n)` and `C(n, t - 1)` tends to infinity,
the ratio `(e(n) + 1) / C(n, t - 1)` is squeezed to `1`.
-/

namespace OMA.R_Erdos643_erdos_643_parts_ii_R3

open Filter Asymptotics

/-- The star lower bound for the avoiding extremal number. -/
def H1 : Prop := ∀ t n : ℕ, 1 ≤ t → t ≤ n →
  (n - 1).choose (t - 1) ≤ Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion)

/-- The asymptotic upper bound. -/
def H2 : Prop := ∀ t : ℕ, 3 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
  (Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion) : ℝ) ≤
    (1 + ε) * (n.choose (t - 1) : ℝ)

/-- `C(m + k, k) ≥ m + 1` for `k ≥ 1`. -/
lemma choose_ge_of_add (m k : ℕ) (hk : 1 ≤ k) : m + 1 ≤ (m + k).choose k := by
  rw [← Nat.choose_symm_add]
  have h1 : (m + 1).choose m = m + 1 := by
    rw [show m + 1 = m + 1 from rfl, Nat.choose_succ_self_right]
  calc m + 1 = (m + 1).choose m := h1.symm
    _ ≤ (m + k).choose m := Nat.choose_le_choose m (by omega)

theorem main : H1 → H2 → type_of% @Erdos643.erdos_643.parts.ii := by
  intro h1 h2 t ht
  set k := t - 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  apply isEquivalent_of_tendsto_one
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hE := h2 t ht (ε / 2) (by positivity)
  have hbig := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop
    ((t : ℝ) + 2 * k / ε + 2 / ε + 1)
  filter_upwards [hE, hbig] with n hn hnb
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have h2e : (0 : ℝ) < 2 * k / ε := by positivity
  have h2e' : (0 : ℝ) < 2 / ε := by positivity
  have htn : t ≤ n := by
    have : (t : ℝ) < n := by linarith
    exact_mod_cast this.le
  have hkn : k < n := by omega
  -- the binomial identity
  have hid : (n - 1).choose k * n = n.choose k * (n - k) := by
    have := Nat.choose_mul_succ_eq (n - 1) k
    rwa [show n - 1 + 1 = n by omega] at this
  have hcge : n - k + 1 ≤ n.choose k := by
    have := choose_ge_of_add (n - k) k hk1
    rwa [show n - k + k = n by omega] at this
  set c : ℕ := n.choose k with hc
  set e : ℕ := Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion) with he
  have hlow : (n - 1).choose k ≤ e := h1 t n (by omega) htn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcR : ((n : ℝ) - k) + 1 ≤ (c : ℝ) := by
    have : ((n - k + 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast hcge
    push_cast [Nat.cast_sub hkn.le] at this
    linarith
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hktR : (k : ℝ) + 1 = t := by
    have : k + 1 = t := by omega
    exact_mod_cast this
  have hcpos : (0 : ℝ) < c := by linarith
  have hidR : ((n - 1).choose k : ℝ) * n = (c : ℝ) * ((n : ℝ) - k) := by
    have : (((n - 1).choose k * n : ℕ) : ℝ) = ((c * (n - k) : ℕ) : ℝ) := by
      rw [hid]
    push_cast [Nat.cast_sub hkn.le] at this
    linarith
  have hlowR : ((n - 1).choose k : ℝ) ≤ e := by exact_mod_cast hlow
  have hthr : ((Erdos643.forcingThreshold n t : ℕ) : ℝ) = (e : ℝ) + 1 := by
    simp [Erdos643.forcingThreshold, he]
  show dist ((Erdos643.forcingThreshold n t : ℝ) / (n.choose (t - 1) : ℝ)) 1 < ε
  rw [hthr, ← hkdef, ← hc, Real.dist_eq, abs_sub_lt_iff]
  constructor
  · -- upper bound
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hcpos]
    have hc2 : 2 / ε < c := by linarith
    have : 1 < ε / 2 * c := by
      have := (div_lt_iff₀ hε).1 hc2
      linarith
    nlinarith
  · -- lower bound
    rw [sub_lt_comm, lt_div_iff₀ hcpos]
    have hk_n : k / (n : ℝ) < ε := by
      rw [div_lt_iff₀ hnR]
      have : 2 * k / ε < n := by linarith
      have := (div_lt_iff₀ hε).1 this
      nlinarith
    have : (1 - ε) * (n : ℝ) < (n : ℝ) - k := by
      have := (div_lt_iff₀ hnR).1 hk_n
      nlinarith
    have hmul : (1 - ε) * c * n < (e : ℝ) * n := by
      nlinarith
    have : (1 - ε) * c < e := lt_of_mul_lt_mul_right hmul hnR.le
    linarith

end OMA.R_Erdos643_erdos_643_parts_ii_R3
