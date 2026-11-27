import FormalConjectures.ErdosProblems.«1191»
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Finite

/-!
# Finite difference packings for Erdős problem 1191(ii)

Hypothesis H1 asks for two fixed natural numbers d and K. At each finite
horizon N it asks for a subset of [1,N] satisfying an integer counting
inequality at every cutoff from K through N. Each positive difference
made by points in the same dyadic interval
must have a unique representation among all such pairs. Cross-interval
differences are unrestricted. Hypothesis H2 asks for an integer encoding
whose pair sums determine both the original sum and the unordered pair of
dyadic intervals. A polylogarithmic bound on the encoding preserves the
required counting estimate after increasing the log exponent.

The forward proof takes a limit of the finite witnesses, encodes the resulting
set, and transfers the counting estimate. The converse restricts a Sidon set
to its finite prefixes. The accompanying H2 proof supplies the encoding.
-/

-- Credit: @NicholasWierenga

namespace OMA.R_Erdos1191_erdos_1191_parts_ii_R1

open Filter Real Set
open Asymptotics

/-- For fixed d, K, and N, the search and all checks range over finite sets. -/
def H1 : Prop :=
  ∃ d K : ℕ, ∀ N : ℕ, ∃ S ∈ (Finset.Icc 1 N).powerset,
    (∀ k ∈ Finset.Icc K N,
      k ≤ (S.filter (· ≤ k)).card ^ 2 * (1 + Nat.log 2 k) ^ d) ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ u ∈ S, ∀ v ∈ S,
      b < a → v < u → Nat.log 2 a = Nat.log 2 b → Nat.log 2 u = Nat.log 2 v →
      a - b = u - v → a = u ∧ b = v

def H2 : Prop :=
  ∃ (E : ℕ → ℕ) (d : ℕ),
    (∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
    ∀ᶠ x : ℕ in atTop, ∀ a ∈ Icc 1 (x / (1 + Nat.log 2 x) ^ d), E a ∈ Icc 1 x

theorem finite_prefix_compact
    (P : ℕ → Set ℕ → Prop)
    (hloc : ∀ k S T, (∀ a ≤ k, a ∈ S ↔ a ∈ T) → P k S → P k T)
    (hfin : ∀ M, ∃ S : Set ℕ, ∀ k ≤ M, P k S) :
    ∃ S : Set ℕ, ∀ k, P k S := by
  classical
  choose W hW using hfin
  let F : Ultrafilter ℕ := hyperfilter ℕ
  let S : Set ℕ := {a | ∀ᶠ n in (F : Filter ℕ), a ∈ W n}
  refine ⟨S, fun k => ?_⟩
  have hPoint (a : ℕ) : ∀ᶠ n in (F : Filter ℕ), a ∈ W n ↔ a ∈ S := by
    by_cases h : a ∈ S
    · have hp : ∀ᶠ n in (F : Filter ℕ), a ∈ W n := h
      exact hp.mono fun _ hn => iff_of_true hn h
    · have hp : ∀ᶠ n in (F : Filter ℕ), a ∉ W n := Ultrafilter.eventually_not.mpr h
      exact hp.mono fun _ hn => iff_of_false hn h
  have hAgree : ∀ᶠ n in (F : Filter ℕ), ∀ a ∈ Finset.range (k + 1), a ∈ W n ↔ a ∈ S :=
    (eventually_all_finset (Finset.range (k + 1))).2 fun a _ => hPoint a
  have hLarge : ∀ᶠ n in (F : Filter ℕ), k ≤ n :=
    Nat.hyperfilter_le_atTop (eventually_ge_atTop k)
  obtain ⟨n, hnk, hn⟩ := (hLarge.and hAgree).exists
  exact hloc k (W n) S
    (fun a ha => hn a (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))) (hW n k hnk)

/-- If an encoded sum determines the unencoded sum and the multiset of its
block labels, uniqueness of the internal positive differences suffices. -/
theorem sidon_of_block_sums
    (B : Nat → Prop) (j E : Nat → Nat)
    (hSum : ∀ a b c d : Nat, E a + E b = E c + E d →
      a + b = c + d ∧ ((j a = j c ∧ j b = j d) ∨ (j a = j d ∧ j b = j c)))
    (hDif : ∀ ⦃a b c d : Nat⦄, B a → B b → B c → B d →
      b < a → d < c → j a = j b → j c = j d → a - b = c - d →
      a = c ∧ b = d)
    ⦃a b c d : Nat⦄ (ha : B a) (hb : B b) (hc : B c) (hd : B d)
    (hEncoded : E a + E b = E c + E d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have matched :
      ∀ ⦃a b c d : Nat⦄, B a → B b → B c → B d →
        a + b = c + d → j a = j c → j b = j d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro a b c d ha hb hc hd hsum hac hbd
    rcases Nat.lt_trichotomy a c with hlt | heq | hgt
    · have hdb : d < b := by omega
      have hdiff : c - a = b - d := by omega
      have hpair := hDif hc ha hb hd hlt hdb hac.symm hbd hdiff
      exact Or.inr ⟨hpair.2, hpair.1.symm⟩
    · exact Or.inl ⟨heq, by omega⟩
    · have hbd' : b < d := by omega
      have hdiff : a - c = d - b := by omega
      have hpair := hDif ha hc hd hb hgt hbd' hac hbd.symm hdiff
      exact Or.inr ⟨hpair.1, hpair.2.symm⟩
  obtain ⟨hsum, hlabels⟩ := hSum a b c d hEncoded
  rcases hlabels with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact matched ha hb hc hd hsum hac hbd
  · exact (matched ha hb hd hc (by omega) had hbc).symm

lemma eventually_denom_le (d : ℕ) :
    ∀ᶠ x : ℕ in atTop, (((1 + Nat.log 2 x)^d : ℕ) : ℝ) ≤
      log (x : ℝ) ^ (2 * (d : ℝ)) := by
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hlog.eventually_ge_atTop (1 + (log (2 : ℝ))⁻¹)] with x hx hxlog
  change 1 + (log (2 : ℝ))⁻¹ ≤ log (x : ℝ) at hxlog
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hinv : 0 < (log (2 : ℝ))⁻¹ := inv_pos.mpr hlog2
  have hx1 : 1 ≤ log (x : ℝ) := by linarith
  have hPow : (2 : ℝ) ^ Nat.log 2 x ≤ (x : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : x ≠ 0)
  have hlogs := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 x) hPow
  rw [Real.log_pow] at hlogs
  have hcap : (Nat.log 2 x : ℝ) ≤ log (x : ℝ) / log (2 : ℝ) :=
    (le_div_iff₀ hlog2).2 hlogs
  rw [div_eq_mul_inv] at hcap
  have hbase : 1 + (Nat.log 2 x : ℝ) ≤ log (x : ℝ) ^ (2 : ℕ) := calc
    _ ≤ log (x : ℝ) + log (x : ℝ) * (log (2 : ℝ))⁻¹ := add_le_add hx1 hcap
    _ = (1 + (log (2 : ℝ))⁻¹) * log (x : ℝ) := by ring
    _ ≤ log (x : ℝ) * log (x : ℝ) := mul_le_mul_of_nonneg_right hxlog (by linarith)
    _ = _ := by ring
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    show 2 * (d : ℝ) = ((2 * d : ℕ) : ℝ) by simp,
    Real.rpow_natCast, pow_mul]
  gcongr

lemma eventually_mul_denom_le (d n : ℕ) :
    ∀ᶠ x : ℕ in atTop, n * (1 + Nat.log 2 x)^d ≤ x := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := 1) (2 * (d : ℝ)) zero_lt_one).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hsmall.bound (show 0 < (1 : ℝ) / ((n : ℝ) + 1) by positivity)
  filter_upwards [eventually_denom_le d, hbound, eventually_ge_atTop (1 : ℕ)]
    with x hden hbound hx
  have hlog0 : 0 ≤ log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx)
  change ‖log (x : ℝ) ^ (2 * (d : ℝ))‖ ≤
    (1 / ((n : ℝ) + 1)) * ‖(x : ℝ) ^ (1 : ℝ)‖ at hbound
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _), Real.rpow_one,
    Real.norm_of_nonneg (by positivity : 0 ≤ (x : ℝ))] at hbound
  have hxreal : (n : ℝ) * (((1 + Nat.log 2 x)^d : ℕ) : ℝ) ≤ (x : ℝ) := calc
    _ ≤ ((n : ℝ) + 1) * (((1 + Nat.log 2 x)^d : ℕ) : ℝ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ ((n : ℝ) + 1) * (log (x : ℝ) ^ (2 * (d : ℝ))) := by gcongr
    _ ≤ ((n : ℝ) + 1) * ((1 / ((n : ℝ) + 1)) * (x : ℝ)) := by gcongr
    _ = _ := by field_simp
  exact_mod_cast hxreal

lemma tendsto_logShrink_atTop (d : ℕ) :
    Tendsto (fun x : ℕ ↦ x / (1 + Nat.log 2 x)^d) atTop atTop := by
  refine tendsto_atTop.2 fun n ↦ ?_
  filter_upwards [eventually_mul_denom_le d n] with x hx
  exact (Nat.le_div_iff_mul_le (by positivity)).2 hx

lemma eventually_sqrt_le_shrunk (d : ℕ) :
    ∀ᶠ x : ℕ in atTop, sqrt (x : ℝ) ≤
      2 * sqrt ((x / (1 + Nat.log 2 x)^d : ℕ) : ℝ) * log (x : ℝ) ^ (d : ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_denom_le d, eventually_mul_denom_le d 1,
    hlog.eventually_ge_atTop 1] with x hden hx hxlog
  change 1 ≤ log (x : ℝ) at hxlog
  set D : ℕ := (1 + Nat.log 2 x)^d with hD
  set y : ℕ := x / D with hy
  change sqrt (x : ℝ) ≤ 2 * sqrt (y : ℝ) * log (x : ℝ) ^ (d : ℝ)
  have hDpos : 0 < D := by subst D; positivity
  have hy1 : 1 ≤ y := (Nat.le_div_iff_mul_le hDpos).2 hx
  have hDy : D ≤ D * y := calc
    D = D * 1 := (mul_one D).symm
    _ ≤ D * y := Nat.mul_le_mul_left _ hy1
  have hxd : x ≤ 2 * (D * y) := by
    have hmod : x % D + D * y = x := Nat.mod_add_div x D
    have hlt := Nat.mod_lt x hDpos
    omega
  have hlogpos : 0 < log (x : ℝ) := by linarith
  set u := log (x : ℝ) ^ (d : ℝ) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hlogpos.le _
  have hu2 : log (x : ℝ) ^ (2 * (d : ℝ)) = u * u := by
    rw [two_mul, Real.rpow_add hlogpos, hu]
  have hcomp : (x : ℝ) ≤ 2 * (u * u) * (y : ℝ) := calc
    _ ≤ 2 * (D : ℝ) * (y : ℝ) := by exact_mod_cast (by simpa [mul_assoc] using hxd)
    _ ≤ _ := by rw [← hu2]; gcongr
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hEq : (2 * sqrt (y : ℝ) * u)^2 = 4 * (y : ℝ) * (u * u) := calc
    _ = 4 * (sqrt (y : ℝ))^2 * (u * u) := by ring
    _ = _ := by rw [Real.sq_sqrt hy0]
  have hsq : (x : ℝ) ≤ (2 * sqrt (y : ℝ) * u)^2 := by
    rw [hEq]
    have hnonneg := mul_nonneg hy0 (mul_nonneg hu0 hu0)
    nlinarith
  simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2 * sqrt (y : ℝ) * u)]
    using Real.sqrt_le_sqrt hsq

lemma positive_liminf_iff {f : ℕ → ℝ} :
    0 < liminf (fun x ↦ ENNReal.ofReal (f x)) atTop ↔
      ∃ a > (0 : ℝ), ∀ᶠ x in atTop, a ≤ f x := by
  constructor
  · intro h
    obtain ⟨a, ha, halt⟩ := exists_between h
    have hfin : a ≠ ⊤ := ne_top_of_lt halt
    have ha0 : 0 < a.toReal := ENNReal.toReal_pos ha.ne' hfin
    refine ⟨a.toReal, ha0, ?_⟩
    filter_upwards [eventually_lt_of_lt_liminf halt] with x hx
    have hf0 := ENNReal.ofReal_pos.mp (ha.trans hx)
    apply (ENNReal.ofReal_le_ofReal_iff hf0.le).1
    simpa only [ENNReal.ofReal_toReal hfin] using hx.le
  · rintro ⟨a, ha, h⟩
    exact (ENNReal.ofReal_pos.mpr ha).trans_le
      ((le_liminf_of_le) (h.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx))

theorem density_transfer (B E : Set ℕ)
    (hB : ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((B ∩ Set.Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log (x : ℝ) ^ c)) atTop)
    (hE : ∃ d : ℕ, ∀ᶠ x : ℕ in atTop,
      (B ∩ Set.Icc 1 (x / (1 + Nat.log 2 x)^d)).ncard ≤ (E ∩ Set.Icc 1 x).ncard) :
    ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((E ∩ Set.Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log (x : ℝ) ^ c)) atTop := by
  rcases hB with ⟨c, hc, hB⟩
  rcases hE with ⟨d, hE⟩
  obtain ⟨a, ha, hA⟩ := positive_liminf_iff.mp hB
  refine ⟨c + d, by positivity, positive_liminf_iff.mpr ⟨a / 2, by positivity, ?_⟩⟩
  have hy := tendsto_logShrink_atTop d
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hy.eventually hA, hE, eventually_sqrt_le_shrunk d,
    hy.eventually_ge_atTop 1, hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)]
    with x haB hBE hxroot hy1 hxlog hx1
  change 1 ≤ log (x : ℝ) at hxlog
  set y := x / (1 + Nat.log 2 x)^d
  change a ≤ (↑(B ∩ Set.Icc 1 y).ncard : ℝ) / (y : ℝ) ^ (1 / 2 : ℝ) * log (y : ℝ)^c at haB
  rw [← Real.sqrt_eq_rpow] at haB ⊢
  change (B ∩ Set.Icc 1 y).ncard ≤ (E ∩ Set.Icc 1 x).ncard at hBE
  have hyx : y ≤ x := Nat.div_le_self _ _
  have hyreal : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hxreal : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hsY : 0 < sqrt (y : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsX : 0 < sqrt (x : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hlogY : 0 ≤ log (y : ℝ) := Real.log_nonneg hyreal
  have hlogX : 0 < log (x : ℝ) := by linarith
  have hlogYX : log (y : ℝ) ≤ log (x : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hyx)
  have hpow := Real.rpow_le_rpow hlogY hlogYX hc.le
  have ha' : a * sqrt (y : ℝ) ≤ (↑(B ∩ Set.Icc 1 y).ncard : ℝ) * log (y : ℝ)^c := by
    apply (le_div_iff₀ hsY).1
    simpa only [div_mul_eq_mul_div₀] using haB
  have hcast : (↑(B ∩ Set.Icc 1 y).ncard : ℝ) ≤ ↑(E ∩ Set.Icc 1 x).ncard := by
    exact_mod_cast hBE
  have hmid : a * sqrt (x : ℝ) ≤
      2 * (↑(E ∩ Set.Icc 1 x).ncard : ℝ) * log (x : ℝ)^(c + (d : ℝ)) := calc
    _ ≤ a * (2 * sqrt (y : ℝ) * log (x : ℝ) ^ (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hxroot ha.le
    _ = 2 * (a * sqrt (y : ℝ)) * log (x : ℝ) ^ (d : ℝ) := by ring
    _ ≤ 2 * ((↑(B ∩ Set.Icc 1 y).ncard : ℝ) * log (y : ℝ)^c) * log (x : ℝ)^(d : ℝ) := by
      gcongr
    _ ≤ 2 * ((↑(E ∩ Set.Icc 1 x).ncard : ℝ) * log (x : ℝ)^c) * log (x : ℝ)^(d : ℝ) := by
      gcongr
    _ = _ := by rw [Real.rpow_add hlogX]; ring
  simp only [div_mul_eq_mul_div₀]
  apply (le_div_iff₀ hsX).2
  linarith

lemma ncard_prefix_eq_filter {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.Icc 1 N) (k : ℕ) :
    ((S : Set ℕ) ∩ Icc 1 k).ncard = (S.filter (· ≤ k)).card := by
  have h : (S : Set ℕ) ∩ Icc 1 k = ↑(S.filter (· ≤ k)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun ⟨ha, _, hk⟩ ↦ ⟨ha, hk⟩,
      fun ⟨ha, hk⟩ ↦ ⟨ha, (Finset.mem_Icc.mp (hS ha)).1, hk⟩⟩
  rw [h, Set.ncard_coe_finset]

lemma density_of_integer_bound (A : Set ℕ) (d : ℕ)
    (h : ∀ᶠ x : ℕ in atTop, x ≤ (A ∩ Set.Icc 1 x).ncard ^ 2 * (1 + Nat.log 2 x) ^ d) :
    A.Infinite ∧ ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ Set.Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ c)) atTop := by
  constructor
  · intro hfin
    obtain ⟨x, hx, hlarge⟩ := (h.and (eventually_mul_denom_le d (A.ncard ^ 2 + 1))).exists
    have hle : (A ∩ Set.Icc 1 x).ncard ≤ A.ncard :=
      Set.ncard_le_ncard inter_subset_left hfin
    have hxle : x ≤ A.ncard ^ 2 * (1 + Nat.log 2 x) ^ d :=
      hx.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hle 2))
    have hstrict : A.ncard ^ 2 * (1 + Nat.log 2 x) ^ d <
        (A.ncard ^ 2 + 1) * (1 + Nat.log 2 x) ^ d :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by positivity)
    exact (not_lt_of_ge (hlarge.trans hxle)) hstrict
  · refine ⟨(d : ℝ) + 1, by positivity, positive_liminf_iff.mpr ⟨1, zero_lt_one, ?_⟩⟩
    have hlog := Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [h, eventually_denom_le d, hlog.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℕ)] with x hx hden hlog hx1
    change 1 ≤ log (x : ℝ) at hlog
    have hx0 : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
    have hlogpos : 0 < log (x : ℝ) := zero_lt_one.trans_le hlog
    let n : ℝ := (A ∩ Set.Icc 1 x).ncard
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hpow : (log (x : ℝ) ^ (d : ℝ)) ^ 2 = log (x : ℝ) ^ (2 * (d : ℝ)) := by
      rw [two_mul, Real.rpow_add hlogpos, pow_two]
    have hx' : (x : ℝ) ≤ n ^ 2 * (((1 + Nat.log 2 x) ^ d : ℕ) : ℝ) := by
      dsimp only [n]
      exact_mod_cast hx
    have hsq : (x : ℝ) ≤ (n * log (x : ℝ) ^ (d : ℝ)) ^ 2 := by
      rw [mul_pow, hpow]
      exact hx'.trans (mul_le_mul_of_nonneg_left hden (sq_nonneg n))
    have hmul0 : 0 ≤ n * log (x : ℝ) ^ (d : ℝ) :=
      mul_nonneg hn0 (Real.rpow_nonneg hlogpos.le _)
    have hsqrt : Real.sqrt (x : ℝ) ≤ n * log (x : ℝ) ^ (d : ℝ) := by
      simpa only [Real.sqrt_sq hmul0] using Real.sqrt_le_sqrt hsq
    change 1 ≤ n / (x : ℝ) ^ (1 / 2 : ℝ) * log (x : ℝ) ^ ((d : ℝ) + 1)
    rw [← Real.sqrt_eq_rpow, div_mul_eq_mul_div₀]
    apply (le_div_iff₀ (Real.sqrt_pos.2 hx0)).2
    rw [one_mul, Real.rpow_add hlogpos, Real.rpow_one, ← mul_assoc]
    exact hsqrt.trans (le_mul_of_one_le_right hmul0 hlog)

theorem integer_bound_of_density (A : Set ℕ)
    (hA : ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ c)) atTop) :
    ∃ d : ℕ, ∀ᶠ x : ℕ in atTop,
      x ≤ (A ∩ Icc 1 x).ncard ^ 2 * (1 + Nat.log 2 x) ^ d := by
  obtain ⟨c, hc, hlim⟩ := hA
  obtain ⟨a, ha, hlower⟩ := positive_liminf_iff.mp hlim
  obtain ⟨m, hm⟩ := exists_nat_ge c
  obtain ⟨K, hK⟩ := exists_nat_ge a⁻¹
  refine ⟨(m + 1) * 2, ?_⟩
  filter_upwards [hlower, eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop ((2 : ℕ) ^ K)] with x hxlower hx hxK
  rw [← Real.sqrt_eq_rpow] at hxlower
  let q : ℝ := ((1 + Nat.log 2 x : ℕ) : ℝ)
  let C : ℝ := ((A ∩ Icc 1 x).ncard : ℝ)
  have hx1 : 1 ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : 0 < (x : ℝ) := by linarith
  have hsqrt : 0 < sqrt (x : ℝ) := Real.sqrt_pos.2 hxpos
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (by omega : 1 ≤ 1 + Nat.log 2 x)
  have hq0 : 0 ≤ q := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog0 : 0 ≤ log (x : ℝ) := Real.log_nonneg hx1
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    norm_num at h
    exact h
  have hxpow : (x : ℝ) ≤ 2 ^ (Nat.log 2 x + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) x).le
  have hlogle := Real.log_le_log hxpos hxpow
  rw [Real.log_pow] at hlogle
  have hlogq : log (x : ℝ) ≤ q := calc
    _ ≤ ((Nat.log 2 x + 1 : ℕ) : ℝ) * log 2 := hlogle
    _ ≤ ((Nat.log 2 x + 1 : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
    _ = q := by simp [q, Nat.add_comm]
  have hpow : log (x : ℝ) ^ c ≤ q ^ m := calc
    _ ≤ q ^ c := Real.rpow_le_rpow hlog0 hlogq hc.le
    _ ≤ q ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 hm
    _ = q ^ m := Real.rpow_natCast q m
  have hKNat : K ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by decide) hxK
  have hinv : a⁻¹ ≤ q := hK.trans (by
    dsimp [q]
    exact_mod_cast (by omega : K ≤ 1 + Nat.log 2 x))
  have hscale : a * sqrt (x : ℝ) ≤ C * log (x : ℝ) ^ c := by
    apply (le_div_iff₀ hsqrt).1
    simpa only [div_mul_eq_mul_div₀] using hxlower
  have hroot : sqrt (x : ℝ) ≤ C * q ^ (m + 1) := calc
    _ = a⁻¹ * (a * sqrt (x : ℝ)) := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    _ ≤ a⁻¹ * (C * log (x : ℝ) ^ c) := mul_le_mul_of_nonneg_left hscale (inv_nonneg.mpr ha.le)
    _ ≤ q * (C * q ^ m) :=
      mul_le_mul hinv (mul_le_mul_of_nonneg_left hpow hC) (by positivity) hq0
    _ = C * q ^ (m + 1) := by rw [pow_succ]; ring
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rw [Real.sq_sqrt (Nat.cast_nonneg x), mul_pow, ← pow_mul] at hsquare
  dsimp [q, C] at hsquare
  exact_mod_cast hsquare

theorem main : H1 → H2 → type_of% @Erdos1191.erdos_1191.parts.ii := by
  rintro ⟨D, K, hfinite⟩ ⟨E, d, hsum, hsize⟩
  let pack (S : Set ℕ) : Prop :=
    ∀ ⦃a b u v : ℕ⦄, a ∈ S → b ∈ S → u ∈ S → v ∈ S →
      b < a → v < u → Nat.log 2 a = Nat.log 2 b → Nat.log 2 u = Nat.log 2 v →
      a - b = u - v → a = u ∧ b = v
  let P (k : ℕ) (S : Set ℕ) : Prop :=
    (K ≤ k → k ≤ (S ∩ Icc 1 k).ncard ^ 2 * (1 + Nat.log 2 k) ^ D) ∧ pack (S ∩ Iic k)
  have hlocal : ∀ k S T, (∀ a ≤ k, a ∈ S ↔ a ∈ T) → P k S → P k T := by
    intro k S T h hS
    have h₁ : S ∩ Icc 1 k = T ∩ Icc 1 k := by
      ext a
      exact ⟨fun ⟨ha, hb⟩ ↦ ⟨(h a hb.2).mp ha, hb⟩,
             fun ⟨ha, hb⟩ ↦ ⟨(h a hb.2).mpr ha, hb⟩⟩
    have h₂ : S ∩ Iic k = T ∩ Iic k := by
      ext a
      exact ⟨fun ⟨ha, hb⟩ ↦ ⟨(h a hb).mp ha, hb⟩,
             fun ⟨ha, hb⟩ ↦ ⟨(h a hb).mpr ha, hb⟩⟩
    exact ⟨h₁ ▸ hS.1, h₂ ▸ hS.2⟩
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, ∀ k, P k B := by
    apply finite_prefix_compact P hlocal
    intro N
    obtain ⟨S, hsub, hcount, hpack⟩ := hfinite N
    refine ⟨(S : Set ℕ), fun k hk ↦ ⟨?_, ?_⟩⟩
    · intro hK
      rw [ncard_prefix_eq_filter (Finset.mem_powerset.mp hsub)]
      exact hcount k (Finset.mem_Icc.mpr ⟨hK, hk⟩)
    · intro a b u v ha hb hu hv
      exact hpack a ha.1 b hb.1 u hu.1 v hv.1
  have hpackB : pack B := by
    intro a b u v ha hb hu hv
    let k := a + b + u + v
    exact (hB k).2 ⟨ha, by change a ≤ a + b + u + v; omega⟩ ⟨hb, by change b ≤ a + b + u + v; omega⟩
      ⟨hu, by change u ≤ a + b + u + v; omega⟩ ⟨hv, by change v ≤ a + b + u + v; omega⟩
  obtain ⟨hBinf, hlimB⟩ := density_of_integer_bound B D
    ((eventually_ge_atTop K).mono (fun k hk ↦ (hB k).1 hk))
  have hEinj : Function.Injective E := by
    intro a b hab
    have h := (hsum a a b b (by rw [hab])).1
    omega
  refine ⟨E '' B, (Set.infinite_image_iff hEinj.injOn).2 hBinf, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨v, hv, rfl⟩ heq
    rcases sidon_of_block_sums B (Nat.log 2) E hsum hpackB ha hb hu hv heq with h | h
    · exact Or.inl ⟨congrArg E h.1, congrArg E h.2⟩
    · exact Or.inr ⟨congrArg E h.1, congrArg E h.2⟩
  · apply density_transfer B (E '' B) hlimB
    refine ⟨d, ?_⟩
    filter_upwards [hsize] with x hx
    apply Set.ncard_le_ncard_of_injOn E _ hEinj.injOn
      (Set.finite_Icc 1 x |>.subset inter_subset_right)
    intro a ha
    exact ⟨⟨a, ha.1, rfl⟩, hx a ha.2⟩

/-- Restricting an infinite Sidon witness to finite prefixes gives the packing hypothesis. -/
theorem H1_of_target
    (h : ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
      ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
        ((A ∩ Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ c)) atTop) : H1 := by
  classical
  obtain ⟨A, _, hsid, hdensity⟩ := h
  obtain ⟨D, hD⟩ := integer_bound_of_density A hdensity
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hD
  refine ⟨D, K, ?_⟩
  intro N
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hsub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  refine ⟨S, Finset.mem_powerset.mpr hsub, ?_, ?_⟩
  · intro k hk
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    rw [← ncard_prefix_eq_filter hsub]
    have hprefix : (S : Set ℕ) ∩ Icc 1 k = A ∩ Icc 1 k := by
      ext a
      constructor
      · rintro ⟨ha, hka⟩
        exact ⟨(Finset.mem_filter.mp ha).2, hka⟩
      · rintro ⟨ha, hka⟩
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hka.1, hka.2.trans hk₂⟩, ha⟩, hka⟩
    rw [hprefix]
    exact hK k hk₁
  · intro a ha b hb u hu v hv hba hvu _ _ hdiff
    have mem_A (n : ℕ) (hn : n ∈ S) : n ∈ A := (Finset.mem_filter.mp hn).2
    have hsum : a + v = u + b := by omega
    rcases hsid a (mem_A a ha) u (mem_A u hu) v (mem_A v hv) b (mem_A b hb) hsum with
      ⟨hau, hvb⟩ | ⟨hab, _⟩
    · exact ⟨hau, hvb.symm⟩
    · omega

end OMA.R_Erdos1191_erdos_1191_parts_ii_R1
