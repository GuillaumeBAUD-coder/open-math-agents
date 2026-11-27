import FormalConjectures.ErdosProblems.«785»
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A linear lower bound for exact additive complements

The Lean proof of the Chen–Fang estimate below is from Genbox's contribution
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2472
(commit 6501a23e3423274e4e2ca0cbafca797d0ff981cb). It includes the Ruzsa
lower bound and the Narkiewicz dichotomy. The final argument takes exponent
two and uses that the smaller counting function is a natural number. This
gives the Sárközy–Szemerédi estimate with constant one.
-/

/- Chen and Fang's bound (https://doi.org/10.4064/aa169-1-3, Theorem 0.2) follows from
Ruzsa's lower bound (https://arxiv.org/abs/1510.00812, Theorem 1.2) and Narkiewicz's
dichotomy, proved below by counting the pairs that exceed twice the cutoff.
In the sparse complement, every fixed power of the counting function is sublinear. -/

open Filter Set Erdos785
open scoped Topology Pointwise BigOperators

namespace RuzsaProof

open Erdos785

lemma trunc_bdd (A : Set ℕ) (x : ℕ) : BddAbove (A ∩ Icc 1 x) :=
  ⟨x, fun _ ha => ha.2.2⟩

lemma le_star {A : Set ℕ} {x a : ℕ} (ha : a ∈ A ∩ Icc 1 x) : a ≤ aStar A x :=
  le_csSup (trunc_bdd A x) ha

lemma star_mem {A : Set ℕ} {x : ℕ} (h : (A ∩ Icc 1 x).Nonempty) :
    aStar A x ∈ A ∩ Icc 1 x :=
  Nat.sSup_mem h (trunc_bdd A x)

lemma trunc_eq {A : Set ℕ} {x y : ℕ} (hy : y ≤ x) (hstar : aStar A x ≤ y) :
    A ∩ Icc 1 y = A ∩ Icc 1 x := by
  apply Subset.antisymm
  · intro a ha
    exact ⟨ha.1, ha.2.1, ha.2.2.trans hy⟩
  · intro a ha
    exact ⟨ha.1, ha.2.1, (le_star ha).trans hstar⟩

lemma counting_eq {A : Set ℕ} {x y : ℕ} (hy : y ≤ x) (hstar : aStar A x ≤ y) :
    counting A y = counting A x :=
  congrArg Set.ncard (trunc_eq hy hstar)

lemma star_eventually_mem {A : Set ℕ} (hA : A.Infinite) :
    ∀ᶠ x : ℕ in atTop, aStar A x ∈ A ∩ Icc 1 x := by
  obtain ⟨a, ha, ha1⟩ := hA.exists_gt 1
  filter_upwards [eventually_ge_atTop a] with x hax
  exact star_mem ⟨a, ha, ha1.le, hax⟩

lemma star_tendsto {A : Set ℕ} (hA : A.Infinite) :
    Tendsto (aStar A) atTop atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  obtain ⟨x, hx, hMx⟩ := hA.exists_gt (max M 1)
  filter_upwards [eventually_ge_atTop x] with y hy
  exact (le_max_left M 1).trans (hMx.le.trans (le_star
    ⟨hx, (le_max_right M 1).trans hMx.le, hy⟩))

lemma count_tendsto {A : Set ℕ} (hA : A.Infinite) (hA0 : 0 ∉ A) :
    Tendsto (counting A) atTop atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  obtain ⟨S, hSA, hSf, hc⟩ := hA.exists_subset_ncard_eq M
  obtain ⟨m, hm⟩ := hSf.bddAbove
  filter_upwards [eventually_ge_atTop m] with x hx
  have hh : S ⊆ A ∩ Icc 1 x := by
    intro a ha
    refine ⟨hSA ha, ?_, (hm ha).trans hx⟩
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hA0 (h ▸ hSA ha))
  unfold counting
  rw [← hc]
  exact Set.ncard_le_ncard hh ((finite_Icc 1 x).subset inter_subset_right)

lemma sparse {A B : Set ℕ} (hB : B.Infinite) (hB0 : 0 ∉ B)
    (hprod : Tendsto (fun x : ℕ => (counting A x : ℝ) * counting B x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℕ => (counting A x : ℝ) / x) atTop (𝓝 0) := by
  have hBt : Tendsto (fun x : ℕ => (counting B x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (count_tendsto hB hB0)
  have hi : Tendsto (fun x : ℕ => (counting B x : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hBt
  have hj : Tendsto (fun x : ℕ => ((counting A x : ℝ) * counting B x / x) *
      (counting B x : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_mul, Pi.mul_def] using hprod.mul hi
  refine hj.congr' ?_
  filter_upwards [(tendsto_atTop.mp hBt) 1] with x hB1
  have hp : (counting B x : ℝ) ≠ 0 := (zero_lt_one.trans_le hB1).ne'
  field_simp [hp]

lemma prod_bounds {A B : Set ℕ}
    (hprod : Tendsto (fun x : ℕ => (counting A x : ℝ) * counting B x / x) atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) : ∀ᶠ x : ℕ in atTop,
    (1 - η) * (x : ℝ) ≤ (counting A x : ℝ) * counting B x ∧
      (counting A x : ℝ) * counting B x ≤ (1 + η) * (x : ℝ) := by
  have h : Ioo (1 - η) (1 + η) ∈ 𝓝 (1 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hprod.eventually h, eventually_ge_atTop (1 : ℕ)] with x hx h1
  have hx0 : 0 < (x : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp h1)
  exact ⟨((lt_div_iff₀ hx0).mp hx.1).le, ((div_lt_iff₀ hx0).mp hx.2).le⟩

lemma loss_small {s t K η : ℝ} (hs : 1 ≤ s) (ht : 0 < t)
    (hK : 0 ≤ K) (hloss : 2 * (K + 1) * (s / t) < η) :
    2 * K * s < η * t := by
  have h := (mul_lt_mul_iff_of_pos_right ht).mpr hloss
  have hh : 2 * (K + 1) * (s / t) * t = 2 * (K + 1) * s := by field_simp
  rw [hh] at h
  linarith only [h, hs, hK]

lemma finish_small {s B V S D x t K ε η : ℝ}
    (hs : 1 ≤ s) (ht : 0 < t) (hη : 0 < η) (hε : 8 * η ≤ ε) (hK : 0 ≤ K)
    (hloss : 2 * K * s < η * t)
    (hex : s * V - S + B - V ≤ s * B - x + K)
    (henergy : s * V - D ≤ s * (s * V - S))
    (hdiff : D ≤ x - (1 - 3 * η) * t)
    (hbase : -K ≤ s * B - x) :
    (1 - ε) * t / s < s * B - x := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  apply (div_lt_iff₀ hspos).mpr
  have hm := mul_le_mul_of_nonneg_left hex hspos.le
  have hKs : K ≤ s * K := by simpa using mul_le_mul_of_nonneg_right hs hK
  have hc := mul_lt_mul_of_pos_right (show 4 * η < ε by linarith) ht
  nlinarith only [hm, henergy, hdiff, hbase, hKs, hloss, hc]

lemma finish_large {s B V x t K ε η : ℝ}
    (hs : 1 ≤ s) (ht : 0 < t) (hη : 0 < η) (hε : 8 * η ≤ ε) (hK : 0 ≤ K)
    (hloss : 2 * K * s < η * t) (hxt : x ≤ 2 * t)
    (hex : B - V ≤ s * B - x + K)
    (hlo : (1 - η) * x ≤ s * B) (hV : s * V ≤ x - t + η * x) :
    (1 - ε) * t / s < s * B - x := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  apply (div_lt_iff₀ hspos).mpr
  have hm := mul_le_mul_of_nonneg_left hex hspos.le
  have hxη := mul_le_mul_of_nonneg_left hxt hη.le
  have hKs := mul_nonneg hK hspos.le
  have hc := mul_lt_mul_of_pos_right (show 5 * η < ε by linarith) ht
  nlinarith only [hm, hxη, hKs, hloss, hlo, hV, hc]

end RuzsaProof

namespace RuzsaLimits

open scoped Classical in
noncomputable def slice (A : Set ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun a => a ∈ A)

private lemma mem_slice {A : Set ℕ} {x a : ℕ} :
    a ∈ slice A x ↔ a ∈ A ∧ 1 ≤ a ∧ a ≤ x := by
  classical
  simp only [slice,Finset.mem_filter,Finset.mem_Icc]
  tauto

theorem slice_card (A : Set ℕ) (x : ℕ) : (slice A x).card = counting A x := by
  rw [counting, ← Set.ncard_coe_finset]
  congr 1
  ext a
  exact mem_slice

private lemma slice_mono (A : Set ℕ) {x y : ℕ} (h : x ≤ y) :
    slice A x ⊆ slice A y := by
  intro a ha
  obtain ⟨haA,ha₁,hax⟩ := mem_slice.1 ha
  exact mem_slice.2 ⟨haA,ha₁,hax.trans h⟩

theorem counting_monotone (A : Set ℕ) : Monotone (counting A) := by
  intro x y hxy
  rw [← slice_card A x,← slice_card A y]
  exact Finset.card_le_card (slice_mono A hxy)

private lemma eventually_counting_pos {A : Set ℕ}
    (hsmall : Tendsto (fun x : ℕ => (counting A (2*x) : ℝ) / counting A x) atTop (𝓝 1)) :
    ∀ᶠ x : ℕ in atTop, 0 < counting A x := by
  filter_upwards [hsmall.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx
  by_contra! hn
  have he : counting A x = 0 := Nat.eq_zero_of_le_zero hn
  change 0 < (counting A (2*x) : ℝ) / counting A x at hx
  simp [he] at hx

theorem dyadic_ratio {A : Set ℕ}
    (hsmall : Tendsto (fun x : ℕ => (counting A (2*x) : ℝ) / counting A x) atTop (𝓝 1))
    (k : ℕ) :
    Tendsto (fun x : ℕ => (counting A (2^k*x) : ℝ) / counting A x) atTop (𝓝 1) := by
  have hp := eventually_counting_pos hsmall
  induction k with
  | zero =>
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [hp] with x hx
    have hn : (counting A x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    change (1 : ℝ) = (counting A (2^0*x) : ℝ) / counting A x
    rw [pow_zero,one_mul,div_self hn]
  | succ k ih =>
    have hle (x : ℕ) : x ≤ 2^k*x := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right x (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2))
    have hscale : Tendsto (fun x : ℕ => (2^k*x : ℕ)) atTop atTop :=
      tendsto_atTop_mono hle tendsto_id
    have h := (hsmall.comp hscale).mul ih
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [hp] with x hx
    have hn : (counting A (2^k*x) : ℝ) ≠ 0 := by
      exact_mod_cast (hx.trans_le (counting_monotone A (hle x))).ne'
    change ((counting A (2*(2^k*x)) : ℝ) / counting A (2^k*x)) *
      ((counting A (2^k*x) : ℝ) / counting A x) =
        (counting A (2^(k+1)*x) : ℝ) / counting A x
    rw [pow_succ',mul_assoc]
    exact div_mul_div_cancel₀ hn

private lemma dyadic_bound {A : Set ℕ}
    (hsmall : Tendsto (fun x : ℕ => (counting A (2*x) : ℝ) / counting A x) atTop (𝓝 1))
    (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, (counting A (2^k*x) : ℝ) ≤ (1+δ) * counting A x := by
  filter_upwards [eventually_counting_pos hsmall,
    (dyadic_ratio hsmall k).eventually (gt_mem_nhds (lt_add_of_pos_right (1 : ℝ) hδ))] with x hx h
  have hp : 0 < (counting A x : ℝ) := by exact_mod_cast hx
  exact (div_le_iff₀ hp).1 h.le

private def cutoff (k x : ℕ) : ℕ := x / 2^k + 1

private lemma cutoff_estimates {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, Tendsto (cutoff k) atTop atTop ∧
      ∀ᶠ x in atTop, cutoff k x ≤ x ∧ x ≤ 2^k * cutoff k x ∧ (cutoff k x : ℝ) ≤ ε * (x : ℝ) := by
  have hPow : Tendsto (fun k : ℕ => (2 : ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨k,hk,hLarge⟩ := ((eventually_ge_atTop (1 : ℕ)).and (tendsto_atTop.1 hPow (2/ε))).exists
  let K : ℕ := 2^k
  have hK₂ : 2 ≤ K := by
    simpa only [pow_one] using pow_right_mono₀ (by decide : (1 : ℕ) ≤ 2) hk
  have hK : 0 < K := by omega
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hLarge' : 2/ε ≤ (K : ℝ) := by simpa only [K,Nat.cast_pow,Nat.cast_ofNat] using hLarge
  have hKInv : (1 : ℝ)/(K : ℝ) ≤ ε/2 := by
    apply (div_le_iff₀ hKR).2
    have h := (div_le_iff₀ hε).1 hLarge'
    nlinarith only [h]
  refine ⟨k,?_,?_⟩
  · apply tendsto_atTop.2
    intro m
    filter_upwards [eventually_ge_atTop (m*K)] with x hx
    have hd : m ≤ x/K := (Nat.le_div_iff_mul_le hK).2 hx
    exact hd.trans (Nat.le_add_right _ _)
  · have hCast : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (2 : ℕ),tendsto_atTop.1 hCast (2/ε)] with x hx hX
    have hD := Nat.div_mul_le_self x K
    have hD₂ : (x/K)*2 ≤ x := (Nat.mul_le_mul_left _ hK₂).trans hD
    have hLe : cutoff k x ≤ x := by change x/K+1 ≤ x; omega
    have hMul : x ≤ 2^k * cutoff k x := (Nat.lt_mul_div_succ x hK).le
    have hdiv : ((x/K : ℕ) : ℝ) ≤ (x : ℝ)/(K : ℝ) :=
      (le_div_iff₀ hKR).2 (by exact_mod_cast hD)
    have hhalf : (x : ℝ)/(K : ℝ) ≤ (ε/2)*(x : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hKInv (Nat.cast_nonneg x)
      rw [show ((1 : ℝ)/(K : ℝ))*(x : ℝ) = (x : ℝ)/(K : ℝ) by ring] at h
      exact h
    have hOne : 1 ≤ (ε/2)*(x : ℝ) := by
      have h := (div_le_iff₀ hε).1 hX
      nlinarith only [h]
    refine ⟨hLe,hMul,?_⟩
    change ((x/K+1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [hdiv,hhalf,hOne]


theorem uniform_upper {A B : Set ℕ}
    (hprod : Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) / (x : ℝ)) atTop (𝓝 1))
    (hsmall : Tendsto (fun x : ℕ => (counting A (2*x) : ℝ) / counting A x) atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop, ∀ y ≤ x, (counting A x * counting B y : ℝ) ≤ y + η*x := by
  let δ : ℝ := min (η/8) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδη : δ ≤ η/8 := min_le_left _ _
  have hδ₀ : δ ≤ 1/2 := min_le_right _ _
  have hδSq : (1+δ)^2 ≤ 1+η/2 := by
    nlinarith only [mul_nonneg hδ.le (sub_nonneg.2 hδ₀),hδη,hη]
  have hδOne : 0 ≤ 1 + δ := by positivity
  obtain ⟨k,huLim,hu⟩ := cutoff_estimates (half_pos hη)
  have hUpper : ∀ᶠ t : ℕ in atTop, (counting A t * counting B t : ℝ) ≤ (1+δ)*t := by
    filter_upwards [hprod.eventually (gt_mem_nhds (lt_add_of_pos_right (1 : ℝ) hδ)),
      eventually_gt_atTop (0 : ℕ)] with t ht ht₀
    have hpos : 0 < (t : ℝ) := by exact_mod_cast ht₀
    exact (div_le_iff₀ hpos).1 ht.le
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((dyadic_bound hsmall k hδ).and hUpper)
  filter_upwards [hu,tendsto_atTop.1 huLim N] with x hcut hx
  obtain ⟨huX,hxMul,huSmall⟩ := hcut
  intro y hy
  let u := cutoff k x
  let z := max y u
  have huz : u ≤ z := le_max_right _ _
  have hyz : y ≤ z := le_max_left _ _
  have hzX : z ≤ x := max_le hy huX
  have hxz : x ≤ 2^k*z := hxMul.trans (Nat.mul_le_mul_left _ huz)
  obtain ⟨hA,hB⟩ := hN z (hx.trans huz)
  have hAz : (counting A x : ℝ) ≤ (1+δ)*counting A z := by
    have hAx : (counting A x : ℝ) ≤ counting A (2^k*z) := by
      exact_mod_cast counting_monotone A hxz
    exact hAx.trans hA
  have hBy : (counting B y : ℝ) ≤ counting B z := by exact_mod_cast counting_monotone B hyz
  have hAB : (counting A x * counting B y : ℝ) ≤ (1+δ)^2 * (z : ℝ) := by
    calc
      _ ≤ ((1+δ)*(counting A z : ℝ)) * counting B z :=
        mul_le_mul hAz hBy (by positivity) (by positivity)
      _ = (1+δ) * ((counting A z : ℝ) * counting B z) := by ring
      _ ≤ (1+δ) * ((1+δ)*(z : ℝ)) := mul_le_mul_of_nonneg_left hB hδOne
      _ = _ := by ring
  have hzLe : (z : ℝ) ≤ (x : ℝ) := by exact_mod_cast hzX
  have hzSum : (z : ℝ) ≤ (y : ℝ) + (u : ℝ) := by
    exact_mod_cast (show z ≤ y+u from max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
  have hzScale := mul_le_mul_of_nonneg_left hzLe (half_pos hη).le
  refine hAB.trans ((mul_le_mul_of_nonneg_right hδSq (Nat.cast_nonneg z)).trans ?_)
  change (u : ℝ) ≤ η/2 * (x : ℝ) at huSmall
  nlinarith only [hzSum,huSmall,hzScale]

theorem mean_small {A : Set ℕ}
    (hsmall : Tendsto (fun x : ℕ => (counting A (2*x) : ℝ) / counting A x) atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop, (∑ a ∈ slice A x, (a : ℝ)) ≤ η*(x : ℝ)*counting A x := by
  obtain ⟨k,huLim,hu⟩ := cutoff_estimates (half_pos hη)
  have hDyad := huLim.eventually (dyadic_bound hsmall k (half_pos hη))
  filter_upwards [hu,hDyad] with x hCut hDyad
  obtain ⟨huX,hxMul,huSmall⟩ := hCut
  let u := cutoff k x
  let D := slice A x \ slice A u
  have hSub : slice A u ⊆ slice A x := slice_mono A huX
  have hDecomp : (∑ a ∈ D, (a : ℝ)) + (∑ a ∈ slice A u, (a : ℝ)) =
      ∑ a ∈ slice A x, (a : ℝ) := Finset.sum_sdiff hSub
  have hCards : (D.card : ℝ) = (counting A x : ℝ) - counting A u := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    change D.card + (slice A u).card = (slice A x).card at h
    rw [slice_card, slice_card] at h
    have h' : (D.card : ℝ) + (counting A u : ℝ) = counting A x := by exact_mod_cast h
    linarith only [h']
  have hMono : (counting A u : ℝ) ≤ counting A x := by
    exact_mod_cast counting_monotone A huX
  have hAx : (counting A x : ℝ) ≤ (counting A (2^k*u) : ℝ) := by
    exact_mod_cast counting_monotone A hxMul
  have hRem : (D.card : ℝ) ≤ η/2 * (counting A x : ℝ) := by
    have hA : (counting A x : ℝ) ≤ (1+η/2)*counting A u := hAx.trans hDyad
    have hScaled := mul_le_mul_of_nonneg_left hMono (half_pos hη).le
    rw [hCards]
    nlinarith only [hA,hScaled]
  have hSmallSum : (∑ a ∈ slice A u, (a : ℝ)) ≤ (u : ℝ) * (counting A u : ℝ) := by
    calc
      _ ≤ ∑ a ∈ slice A u, (u : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact_mod_cast (mem_slice.1 ha).2.2
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,slice_card,mul_comm]
  have hBigSum : (∑ a ∈ D, (a : ℝ)) ≤ (x : ℝ) * (D.card : ℝ) := by
    calc
      _ ≤ ∑ a ∈ D, (x : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact_mod_cast (mem_slice.1 (Finset.mem_sdiff.1 ha).1).2.2
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
  change (u : ℝ) ≤ η/2 * (x : ℝ) at huSmall
  have hSmallProduct : (u : ℝ) * (counting A u : ℝ) ≤
      (η/2 * (x : ℝ)) * (counting A x : ℝ) :=
    mul_le_mul huSmall hMono (by positivity) (by positivity)
  have hLargeProduct : (x : ℝ) * (D.card : ℝ) ≤
      (x : ℝ) * (η/2 * (counting A x : ℝ)) :=
    mul_le_mul_of_nonneg_left hRem (Nat.cast_nonneg x)
  calc
    _ = (∑ a ∈ D, (a : ℝ)) + (∑ a ∈ slice A u, (a : ℝ)) := hDecomp.symm
    _ ≤ _ := add_le_add (hBigSum.trans hLargeProduct) (hSmallSum.trans hSmallProduct)
    _ = _ := by ring
end RuzsaLimits

namespace RuzsaEnergy

open scoped BigOperators

def sums (U V : Finset ℕ) : Finset ℕ :=
  (U ×ˢ V).image (fun p => p.1 + p.2)

def diffs (U V : Finset ℕ) : Finset ℤ :=
  (U ×ˢ V).image (fun p => (p.2 : ℤ) - p.1)

private def sumValue (p : ℕ × ℕ) : ℕ := p.1 + p.2

private def diffValue (p : ℕ × ℕ) : ℤ := (p.2 : ℤ) - p.1

section Fibers

variable {α β : Type*} [DecidableEq β]

private def fiber (S : Finset α) (f : α → β) (b : β) : Finset α :=
  S.filter (fun a => f a = b)

private def collisions (S : Finset α) (f : α → β) : Finset (α × α) :=
  S.offDiag.filter (fun p => f p.1 = f p.2)

private lemma mem_collisions {S : Finset α} {f : α → β} {p : α × α} :
    p ∈ collisions S f ↔ (p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2) ∧ f p.1 = f p.2 := by
  rw [collisions, Finset.mem_filter, Finset.mem_offDiag]

private lemma fiber_pos (S : Finset α) (f : α → β) {b : β} (hb : b ∈ S.image f) :
    1 ≤ (fiber S f b).card := by
  obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hb
  exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha,hfa⟩⟩

private lemma fiber_collisions (S : Finset α) (f : α → β) (b : β) :
    fiber (collisions S f) (fun p => f p.1) b = (fiber S f b).offDiag := by
  ext p
  simp only [fiber, collisions, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨⟨h₁,h₂,hne⟩,hEq⟩,h₃⟩
    exact ⟨⟨h₁,h₃⟩,⟨h₂,hEq.symm.trans h₃⟩,hne⟩
  · rintro ⟨⟨h₁,h₃⟩,⟨h₂,h₄⟩,hne⟩
    exact ⟨⟨⟨h₁,h₂,hne⟩,h₃.trans h₄.symm⟩,h₃⟩

private lemma collision_count (S : Finset α) (f : α → β) :
    ((collisions S f).card : ℝ) =
      ∑ b ∈ S.image f, ((fiber S f b).card : ℝ) * ((fiber S f b).card - 1 : ℝ) := by
  have hMaps : ((collisions S f : Finset (α × α)) : Set (α × α)).MapsTo
      (fun p => f p.1) (S.image f : Set β) := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_image_of_mem f hp'.1
  rw [Finset.card_eq_sum_card_fiberwise hMaps, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b hb
  change (((fiber (collisions S f) (fun p => f p.1) b).card : ℕ) : ℝ) = _
  rw [fiber_collisions, Finset.offDiag_card]
  have hLe : (fiber S f b).card ≤ (fiber S f b).card * (fiber S f b).card := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (fiber S f b).card (fiber_pos S f hb)
  rw [Nat.cast_sub hLe, Nat.cast_mul]
  ring

private lemma sum_excess (S : Finset α) (f : α → β) :
    (∑ b ∈ S.image f, (((fiber S f b).card : ℝ) - 1)) = (S.card : ℝ) - (S.image f).card := by
  have hCast : (∑ b ∈ S.image f, ((fiber S f b).card : ℝ)) = (S.card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image f S).symm
  rw [Finset.sum_sub_distrib, hCast, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma excess_le_collisions (S : Finset α) (f : α → β) :
    (S.card : ℝ) - (S.image f).card ≤ ((collisions S f).card : ℝ) := by
  rw [← sum_excess S f, collision_count]
  apply Finset.sum_le_sum
  intro b hb
  have hb' : (1 : ℝ) ≤ (fiber S f b).card := by exact_mod_cast fiber_pos S f hb
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb' (sub_nonneg.mpr hb')

private lemma collisions_le_excess (S : Finset α) (f : α → β) (M : ℕ)
    (hM : ∀ b ∈ S.image f, (fiber S f b).card ≤ M) :
    ((collisions S f).card : ℝ) ≤ (M : ℝ) * ((S.card : ℝ) - (S.image f).card) := by
  rw [collision_count, ← sum_excess S f, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hb' : (1 : ℝ) ≤ (fiber S f b).card := by exact_mod_cast fiber_pos S f hb
  have ht : ((fiber S f b).card : ℝ) ≤ M := by exact_mod_cast hM b hb
  exact mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hb')

end Fibers

private lemma sum_fiber_le (U V : Finset ℕ) (b : ℕ) :
    (fiber (U ×ˢ V) sumValue b).card ≤ U.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hEq
    apply Prod.ext hEq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    unfold sumValue at hp' hq'
    omega

private lemma collision_bijection (U V : Finset ℕ) :
    (collisions (U ×ˢ V) diffValue).card = (collisions (U ×ˢ V) sumValue).card := by
  let swap (q : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
    ((q.2.1,q.1.2),(q.1.1,q.2.2))
  have hInv : Function.Involutive swap := by
    intro q
    rfl
  have hMem (q : (ℕ × ℕ) × (ℕ × ℕ)) :
      q ∈ collisions (U ×ˢ V) diffValue ↔ swap q ∈ collisions (U ×ˢ V) sumValue := by
    rw [mem_collisions, mem_collisions]
    rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
    simp only [Finset.mem_product, swap, diffValue, sumValue]
    constructor
    · rintro ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩,hne⟩,he⟩
      refine ⟨⟨⟨hc,hb⟩,⟨ha,hd⟩,?_⟩,by omega⟩
      intro h
      have hL := congrArg Prod.fst h
      have hR := congrArg Prod.snd h
      exact hne (Prod.ext hL.symm hR)
    · rintro ⟨⟨⟨hc,hb⟩,⟨ha,hd⟩,hne⟩,he⟩
      refine ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩,?_⟩,by omega⟩
      intro h
      have hL := congrArg Prod.fst h
      have hR := congrArg Prod.snd h
      exact hne (Prod.ext hL.symm hR)
  apply Finset.card_bij (fun q _ => swap q)
  · exact fun q hq => (hMem q).mp hq
  · exact fun _ _ _ _ h => hInv.injective h
  · intro q hq
    refine ⟨swap q, (hMem (swap q)).mpr ?_, hInv q⟩
    simpa only [hInv q] using hq

/-- The excess multiplicity of differences is bounded by the excess multiplicity of sums
times the number of possible first coordinates (Ruzsa, Exact additive complements, Lemma 2.1,
https://arxiv.org/abs/1510.00812). -/
theorem excess (U V : Finset ℕ) :
    ((U.card : ℝ) * V.card - (diffs U V).card) ≤
      (U.card : ℝ) * ((U.card : ℝ) * V.card - (sums U V).card) := by
  have hDiff := excess_le_collisions (U ×ˢ V) diffValue
  have hSum := collisions_le_excess (U ×ˢ V) sumValue U.card (fun b _ => sum_fiber_le U V b)
  rw [collision_bijection U V] at hDiff
  have h := hDiff.trans hSum
  rw [Finset.card_product, Nat.cast_mul] at h
  exact h

end RuzsaEnergy

namespace RuzsaCount

/-- The positive elements of a set up to a finite cutoff. -/
noncomputable def slice (S : Set ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter (fun a => a ∈ S)

theorem mem_slice {S : Set ℕ} {x a : ℕ} :
    a ∈ slice S x ↔ a ∈ S ∧ 1 ≤ a ∧ a ≤ x := by
  classical
  simp only [slice, Finset.mem_filter, Finset.mem_Icc, and_comm]

theorem card_slice (S : Set ℕ) (x : ℕ) : (slice S x).card = Erdos785.counting S x := by
  have h : ((slice S x : Finset ℕ) : Set ℕ) = S ∩ Set.Icc 1 x := by
    ext a
    simp only [Finset.mem_coe, mem_slice, Set.mem_inter_iff, Set.mem_Icc]
  rw [Erdos785.counting, ← h, Set.ncard_coe_finset]

theorem slice_mono (S : Set ℕ) : Monotone (slice S) := by
  intro x y hxy a ha
  obtain ⟨hS, h₁, hx⟩ := mem_slice.mp ha
  exact mem_slice.mpr ⟨hS, h₁, hx.trans hxy⟩

/-- Among pairs whose second coordinate lies beyond `x - t`, the pairs
whose first coordinate is `t` cannot contribute to covering `[K,x]`. -/
theorem excess (A B : Set ℕ) (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) (K x t : ℕ)
    (hcov : ∀ n ≥ K, n ∈ A + B) (ht : t ∈ slice A x) :
    let U := slice A x
    let V := slice B (x - t)
    (U.card : ℝ) * V.card - ((U ×ˢ V).image (fun p => p.1 + p.2)).card +
      (Erdos785.counting B x : ℝ) - Erdos785.counting B (x - t) ≤
        (Erdos785.counting A x : ℝ) * Erdos785.counting B x - x + K := by
  let U := slice A x
  let V := slice B (x - t)
  let W := slice B x
  let f (p : ℕ × ℕ) : ℕ := p.1 + p.2
  let S := (U ×ˢ V).image f
  let T := ((U.erase t) ×ˢ (W \ V)).image f
  change (U.card : ℝ) * V.card - S.card + (Erdos785.counting B x : ℝ) -
    Erdos785.counting B (x - t) ≤ (Erdos785.counting A x : ℝ) * Erdos785.counting B x - x + K
  have hsub : Finset.Icc K x ⊆ S ∪ T := by
    intro n hn
    obtain ⟨hKn, hnx⟩ := Finset.mem_Icc.mp hn
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp (hcov n hKn)
    have ha₁ : 1 ≤ a := Nat.pos_of_ne_zero (fun h => hA0 (h ▸ ha))
    have hb₁ : 1 ≤ b := Nat.pos_of_ne_zero (fun h => hB0 (h ▸ hb))
    have haU : a ∈ U := mem_slice.mpr ⟨ha, ha₁, by omega⟩
    have hbW : b ∈ W := mem_slice.mpr ⟨hb, hb₁, by omega⟩
    by_cases hbV : b ∈ V
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨(a, b), Finset.mem_product.mpr ⟨haU, hbV⟩, hab⟩)
    · have hbt : x - t < b := by
        by_contra! h
        exact hbV (mem_slice.mpr ⟨hb, hb₁, h⟩)
      have hat : a ≠ t := by
        intro h
        omega
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hat, haU⟩,
          Finset.mem_sdiff.mpr ⟨hbW, hbV⟩⟩, hab⟩)
  have hT : T.card ≤ (U.erase t).card * (W \ V).card :=
    Finset.card_image_le.trans_eq (Finset.card_product _ _)
  have hST : (Finset.Icc K x).card ≤ S.card + (U.erase t).card * (W \ V).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hT _))
  have hNat : x ≤ S.card + (U.erase t).card * (W \ V).card + K := by
    rw [Nat.card_Icc] at hST
    omega
  have hReal : (x : ℝ) ≤ (S.card : ℝ) + (U.erase t).card * (W \ V).card + K := by
    exact_mod_cast hNat
  have hVW : V ⊆ W := slice_mono B (Nat.sub_le x t)
  have hUpos : 1 ≤ U.card := Finset.card_pos.mpr ⟨t, ht⟩
  rw [Finset.card_erase_of_mem ht, Finset.card_sdiff_of_subset hVW,
    Nat.cast_sub hUpos, Nat.cast_sub (Finset.card_le_card hVW), Nat.cast_one] at hReal
  rw [← card_slice A x, ← card_slice B x, ← card_slice B (x - t)]
  change (U.card : ℝ) * V.card - S.card + (W.card : ℝ) - V.card ≤
    (U.card : ℝ) * W.card - x + K
  nlinarith only [hReal]

/-- For a difference at most `t`, the second coordinate lies in the slice
up to the first coordinate plus `t`. Larger differences occupy a short interval. -/
theorem diff_upper (A B : Set ℕ) (x t : ℕ) (hxt : 2 * t ≤ x) :
    let U := slice A x
    let V := slice B (x - t)
    ((U ×ˢ V).image (fun p => (p.2 : ℤ) - (p.1 : ℤ))).card ≤
      (∑ a ∈ U, Erdos785.counting B (a + t)) + (x - 2 * t) := by
  let U := slice A x
  let V := slice B (x - t)
  let L (a : ℕ) : Finset ℤ := (slice B (a + t)).image (fun b : ℕ => (b : ℤ) - (a : ℤ))
  let T := Finset.Icc ((t : ℤ) + 1) ((x : ℤ) - (t : ℤ))
  let D := (U ×ˢ V).image (fun p => (p.2 : ℤ) - (p.1 : ℤ))
  have hsub : D ⊆ U.biUnion L ∪ T := by
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨_, ha₁, _⟩ := mem_slice.mp ha
    obtain ⟨hbB, hb₁, hbx⟩ := mem_slice.mp hb
    by_cases h : (b : ℤ) - (a : ℤ) ≤ (t : ℤ)
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨b, mem_slice.mpr ⟨hbB, hb₁, by omega⟩, rfl⟩⟩
    · apply Finset.mem_union_right
      apply Finset.mem_Icc.mpr
      omega
  have hL : (U.biUnion L).card ≤ ∑ a ∈ U, Erdos785.counting B (a + t) := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro a _
    rw [← card_slice]
    exact Finset.card_image_le
  have hT : T.card = x - 2 * t := by
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hL hT.le))

end RuzsaCount

namespace RuzsaProof

open Erdos785

private lemma sum_bound (U : Finset ℕ) (f : ℕ → ℝ) {s t η : ℝ}
    (hcard : (U.card : ℝ) = s) (hs : 0 < s) (ht : 0 ≤ t) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hmean : ∑ a ∈ U, (a : ℝ) ≤ η * t * s)
    (hpoint : ∀ a ∈ U, s * f a ≤ (1 + η) * ((a : ℝ) + t)) :
    (∑ a ∈ U, f a) ≤ (1 + 3 * η) * t := by
  have hcoef : (1 + η) ^ 2 ≤ 1 + 3 * η := by
    nlinarith only [mul_nonneg hη (sub_nonneg.mpr hη1)]
  apply (mul_le_mul_iff_of_pos_left hs).mp
  calc
    s * (∑ a ∈ U, f a) = ∑ a ∈ U, s * f a := Finset.mul_sum _ _ _
    _ ≤ ∑ a ∈ U, (1 + η) * ((a : ℝ) + t) := Finset.sum_le_sum hpoint
    _ = (1 + η) * ((∑ a ∈ U, (a : ℝ)) + s * t) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (1 + η) * (η * t * s + s * t) :=
      mul_le_mul_of_nonneg_left (add_le_add hmean (le_refl (s * t))) (by positivity)
    _ = s * ((1 + η) ^ 2 * t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef ht) hs.le

end RuzsaProof

open Erdos785 RuzsaProof in
theorem RuzsaProof.lower_bound : type_of% @Erdos785.erdos_785.variants.ruzsa_lower_bound := by
  intro A B hA hB hA0 hB0 h hsmall ε hε
  classical
  obtain ⟨K, hCov⟩ := eventually_atTop.mp h.1
  let η := min (ε / 8) (1 / 8)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηε : 8 * η ≤ ε := by
    have hle : η ≤ ε / 8 := min_le_left _ _
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (prod_bounds h.2 hη)
  have hstar := star_tendsto hA
  have hUniform := RuzsaLimits.uniform_upper h.2 hsmall hη
  have hMean := hstar.eventually (RuzsaLimits.mean_small hsmall hη)
  have hAone := (tendsto_atTop.mp (count_tendsto hA hA0)) 1
  have hScaled : Tendsto (fun x : ℕ => 2 * ((K : ℝ) + 1) * ((counting A x : ℝ) / x)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => 2 * ((K : ℝ) + 1)) atTop (𝓝 (2 * ((K : ℝ) + 1))) :=
      tendsto_const_nhds
    simpa only [mul_zero, Pi.mul_def] using hc.mul (sparse hB hB0 h.2)
  have hLoss := hstar.eventually (hScaled.eventually (Iio_mem_nhds hη))
  filter_upwards [star_eventually_mem hA, (tendsto_atTop.mp hstar) N, hUniform, hMean, hAone, hLoss]
    with x ht hNt huniform hmean hAone hloss
  let t := aStar A x
  let U := RuzsaCount.slice A x
  let V := RuzsaCount.slice B (x - t)
  have ht1 : 1 ≤ t := ht.2.1
  have htx : t ≤ x := ht.2.2
  have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht1
  have hcardU : U.card = counting A x := RuzsaCount.card_slice A x
  have hcardV : V.card = counting B (x - t) := RuzsaCount.card_slice B (x - t)
  have hAt : counting A t = counting A x := counting_eq htx le_rfl
  have hA1 : 1 ≤ (counting A x : ℝ) := by exact_mod_cast hAone
  have hApos : 0 < (counting A x : ℝ) := zero_lt_one.trans_le hA1
  have htU : t ∈ U := RuzsaCount.mem_slice.mpr ht
  have hMax (a : ℕ) (ha : a ∈ U) : a ≤ t := le_star (RuzsaCount.mem_slice.mp ha)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hloss' : 2 * (K : ℝ) * (counting A x : ℝ) < η * (t : ℝ) := by
    apply loss_small hA1 ht0 hK0
    change 2 * ((K : ℝ) + 1) * ((counting A t : ℝ) / (t : ℝ)) < η at hloss
    simpa only [hAt] using hloss
  have hEx : (counting A x : ℝ) * counting B (x - t) - (RuzsaEnergy.sums U V).card +
      (counting B x : ℝ) - counting B (x - t) ≤ (counting A x : ℝ) * counting B x - x + K := by
    have hh := RuzsaCount.excess A B hA0 hB0 K x t hCov htU
    change (U.card : ℝ) * V.card - (RuzsaEnergy.sums U V).card +
      (counting B x : ℝ) - counting B (x - t) ≤ (counting A x : ℝ) * counting B x - x + K at hh
    simpa only [hcardU, hcardV] using hh
  have hSC : (RuzsaEnergy.sums U V).card ≤ U.card * V.card := by
    unfold RuzsaEnergy.sums
    exact Finset.card_image_le.trans_eq (Finset.card_product U V)
  have hSCr : ((RuzsaEnergy.sums U V).card : ℝ) ≤ (counting A x : ℝ) * counting B (x - t) := by
    rw [hcardU, hcardV] at hSC
    exact_mod_cast hSC
  have hWaste : (counting B x : ℝ) - counting B (x - t) ≤
      (counting A x : ℝ) * counting B x - x + K := by linarith only [hEx, hSCr]
  have hBmono : (counting B (x - t) : ℝ) ≤ counting B x := by
    have hh := Finset.card_le_card (RuzsaCount.slice_mono B (Nat.sub_le x t))
    rw [RuzsaCount.card_slice, RuzsaCount.card_slice] at hh
    exact_mod_cast hh
  change (1 - ε) * (t : ℝ) / (counting A x : ℝ) < (counting A x : ℝ) * counting B x - x
  by_cases hx : 2 * t ≤ x
  · have hbase : -(K : ℝ) ≤ (counting A x : ℝ) * counting B x - x := by
      linarith only [hWaste, hBmono]
    have hSlice : RuzsaLimits.slice A t = U := by
      ext a
      change a ∈ ((Finset.Icc 1 t).filter fun z => z ∈ A) ↔
        a ∈ ((Finset.Icc 1 x).filter fun z => z ∈ A)
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have ht' := Set.ext_iff.mp (trunc_eq (A := A) htx (le_refl t)) a
      simpa only [Set.mem_inter_iff, Set.mem_Icc, and_comm] using ht'
    have hMeanU : ∑ a ∈ U, (a : ℝ) ≤ η * (t : ℝ) * counting A x := by
      change (∑ a ∈ RuzsaLimits.slice A t, (a : ℝ)) ≤ η * (t : ℝ) * counting A t at hmean
      simpa only [hSlice, hAt] using hmean
    have hPoint (a : ℕ) (ha : a ∈ U) :
        (counting A x : ℝ) * counting B (a + t) ≤ (1 + η) * ((a : ℝ) + t) := by
      have hax : a + t ≤ x := by have hh := hMax a ha; omega
      have hAat : counting A (a + t) = counting A x := counting_eq hax (by omega : t ≤ a + t)
      have hb := (hN (a + t) (hNt.trans (by omega : t ≤ a + t))).2
      simpa only [hAat, Nat.cast_add] using hb
    have hUS := sum_bound U (fun a => (counting B (a + t) : ℝ))
      (by exact_mod_cast hcardU) hApos ht0.le hη.le hη1 hMeanU hPoint
    have hD : (RuzsaEnergy.diffs U V).card ≤ (∑ a ∈ U, counting B (a + t)) + (x - 2 * t) :=
      RuzsaCount.diff_upper A B x t hx
    have hD' : ((RuzsaEnergy.diffs U V).card : ℝ) ≤
        (∑ a ∈ U, (counting B (a + t) : ℝ)) + ((x : ℝ) - 2 * (t : ℝ)) := by
      have hh : ((RuzsaEnergy.diffs U V).card : ℝ) ≤
          (((∑ a ∈ U, counting B (a + t)) + (x - 2 * t) : ℕ) : ℝ) := by exact_mod_cast hD
      simpa only [Nat.cast_add, Nat.cast_sum, Nat.cast_sub hx, Nat.cast_mul, Nat.cast_ofNat] using hh
    have hDb : ((RuzsaEnergy.diffs U V).card : ℝ) ≤ (x : ℝ) - (1 - 3 * η) * (t : ℝ) := by
      linarith only [hD', hUS]
    have hEnergy := RuzsaEnergy.excess U V
    rw [hcardU, hcardV] at hEnergy
    exact finish_small hA1 ht0 hη hηε hK0 hloss' hEx hEnergy hDb hbase
  · have hxt : (x : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast (le_of_not_ge hx)
    have hV := huniform (x - t) (Nat.sub_le x t)
    rw [Nat.cast_sub htx] at hV
    exact finish_large hA1 ht0 hη hηε hK0 hloss' hxt hWaste (hN x (hNt.trans htx)).1 hV

namespace ChenFinish

open Erdos785

lemma sparse_bound (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) (h : IsExactAdditiveComplement A B)
    (hslow : Tendsto (fun n : ℕ => (counting A (2 * n) : ℝ) / counting A n) atTop (𝓝 1))
    (hPow : ∀ p : ℕ, Tendsto (fun n : ℕ => (counting A n : ℝ) ^ p / (n : ℝ)) atTop (𝓝 0))
    (M : ℝ) (hM : 1 < M) :
    ∀ᶠ x : ℕ in atTop, (min (counting A x) (counting B x) : ℝ) ^ M ≤
      (counting A x * counting B x : ℝ) - (x : ℝ) := by
  obtain ⟨p, hp⟩ := exists_nat_ge (M + 1)
  have hp1 : 1 ≤ p := by
    have hh : (1 : ℝ) ≤ p := by linarith
    exact_mod_cast hh
  have hpM : M ≤ ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp1, Nat.cast_one]
    linarith
  have hTail := (RuzsaProof.star_tendsto hA).eventually
    ((hPow p).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hR := RuzsaProof.lower_bound A B hA hB hA0 hB0 h hslow (1 / 2) (by norm_num)
  have hAone := (tendsto_atTop.mp (RuzsaProof.count_tendsto hA hA0)) 1
  filter_upwards [hTail, hR, RuzsaProof.star_eventually_mem hA, hAone] with x hx hR hstar hone
  let t := aStar A x
  have ht0 : 0 < (t : ℝ) := Nat.cast_pos.mpr hstar.2.1
  have hcount : counting A t = counting A x := RuzsaProof.counting_eq hstar.2.2 le_rfl
  have hAx1 : 1 ≤ (counting A x : ℝ) := by exact_mod_cast hone
  have hAx0 : 0 < (counting A x : ℝ) := zero_lt_one.trans_le hAx1
  change (counting A t : ℝ) ^ p / (t : ℝ) < 1 / 2 at hx
  rw [hcount] at hx
  have hxp : (counting A x : ℝ) ^ p < (1 / 2 : ℝ) * (t : ℝ) :=
    (div_lt_iff₀ ht0).mp hx
  have hPowEff : (counting A x : ℝ) ^ (p - 1 : ℕ) <
      (1 / 2 : ℝ) * (t : ℝ) / (counting A x : ℝ) := by
    apply (lt_div_iff₀ hAx0).mpr
    rw [← pow_succ, Nat.sub_add_cancel hp1]
    exact hxp
  have hmin : (min (counting A x) (counting B x) : ℝ) ≤ (counting A x : ℝ) := by
    exact_mod_cast min_le_left (counting A x) (counting B x)
  change (1 - (1 / 2 : ℝ)) * (t : ℝ) / (counting A x : ℝ) <
      (counting A x * counting B x : ℝ) - (x : ℝ) at hR
  norm_num at hR
  calc
    (min (counting A x) (counting B x) : ℝ) ^ M ≤ (counting A x : ℝ) ^ M :=
      Real.rpow_le_rpow (by positivity) hmin (zero_lt_one.trans hM).le
    _ ≤ (counting A x : ℝ) ^ ((p - 1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hAx1 hpM
    _ = (counting A x : ℝ) ^ (p - 1 : ℕ) := Real.rpow_natCast _ _
    _ ≤ _ := (hPowEff.trans hR).le

end ChenFinish

namespace ChenCount

open Erdos785 (counting)
open RuzsaCount (slice mem_slice card_slice slice_mono)

theorem jump (A : Set ℕ) (n : ℕ) : counting A (n + 1) ≤ counting A n + 1 := by
  have hsub : slice A (n + 1) ⊆ insert (n + 1) (slice A n) := by
    intro a ha
    obtain ⟨hA, ha1, hax⟩ := mem_slice.mp ha
    by_cases he : a = n + 1
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (mem_slice.mpr ⟨hA, ha1, by omega⟩))
  rw [← card_slice, ← card_slice]
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- Coverage by sums through `2*x` omits the rectangle in which both coordinates exceed `x`. -/
theorem rectangle (A B : Set ℕ) (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) (K : ℕ)
    (hCov : ∀ j ≥ K, j ∈ A + B) (x : ℕ) :
    ((counting A (2 * x) : ℝ) - counting A x) * ((counting B (2 * x) : ℝ) - counting B x) ≤
      (counting A (2 * x) : ℝ) * counting B (2 * x) - (2 * x : ℕ) + K := by
  let U := slice A (2 * x)
  let V := slice B (2 * x)
  let U₀ := slice A x
  let V₀ := slice B x
  let P := U ×ˢ V
  let Q := (U \ U₀) ×ˢ (V \ V₀)
  let f (p : ℕ × ℕ) : ℕ := p.1 + p.2
  have hU : U₀ ⊆ U := slice_mono A (by omega)
  have hV : V₀ ⊆ V := slice_mono B (by omega)
  have hQP : Q ⊆ P := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp hb).1⟩
  have hsub : Finset.Icc K (2 * x) ⊆ (P \ Q).image f := by
    intro j hj
    obtain ⟨hKj, hjx⟩ := Finset.mem_Icc.mp hj
    obtain ⟨a, haA, b, hbB, hab⟩ := Set.mem_add.mp (hCov j hKj)
    have ha : 1 ≤ a := Nat.pos_of_ne_zero (fun h => hA0 (h ▸ haA))
    have hb : 1 ≤ b := Nat.pos_of_ne_zero (fun h => hB0 (h ▸ hbB))
    have haU : a ∈ U := mem_slice.mpr ⟨haA, ha, by omega⟩
    have hbV : b ∈ V := mem_slice.mpr ⟨hbB, hb, by omega⟩
    refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_sdiff.mpr
      ⟨Finset.mem_product.mpr ⟨haU, hbV⟩, ?_⟩, hab⟩
    intro h
    obtain ⟨haQ, hbQ⟩ := Finset.mem_product.mp h
    have hax : x < a := by
      by_contra! hn
      exact (Finset.mem_sdiff.mp haQ).2 (mem_slice.mpr ⟨haA, ha, hn⟩)
    have hbx : x < b := by
      by_contra! hn
      exact (Finset.mem_sdiff.mp hbQ).2 (mem_slice.mpr ⟨hbB, hb, hn⟩)
    omega
  have hcount := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Nat.card_Icc, Finset.card_sdiff_of_subset hQP] at hcount
  have hN : 2 * x + Q.card ≤ P.card + K := by
    have hcard := Finset.card_le_card hQP
    omega
  have hR : ((2 * x : ℕ) : ℝ) + (Q.card : ℝ) ≤ (P.card : ℝ) + K := by
    exact_mod_cast hN
  have hQprod : (Q.card : ℝ) = ((U.card : ℝ) - U₀.card) * ((V.card : ℝ) - V₀.card) := by
    change ((((U \ U₀) ×ˢ (V \ V₀)).card : ℝ)) = _
    rw [Finset.card_product, Finset.card_sdiff_of_subset hU,
      Finset.card_sdiff_of_subset hV, Nat.cast_mul, Nat.cast_sub (Finset.card_le_card hU),
      Nat.cast_sub (Finset.card_le_card hV)]
  have hPprod : (P.card : ℝ) = (U.card : ℝ) * V.card := by
    change (((U ×ˢ V).card : ℝ)) = _
    rw [Finset.card_product, Nat.cast_mul]
  rw [hQprod, hPprod] at hR
  rw [← card_slice A (2 * x), ← card_slice A x, ← card_slice B (2 * x), ← card_slice B x]
  change ((U.card : ℝ) - U₀.card) * ((V.card : ℝ) - V₀.card) ≤
    (U.card : ℝ) * V.card - (2 * x : ℕ) + K
  linarith only [hR]

end ChenCount

namespace ChenSparse

private lemma log2_div_tendsto {N : ℕ} (hN : 0 < N) :
    Tendsto (fun n : ℕ => (n/N).log2) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2^k*N)] with n hn
  have hpow : 2^k ≤ n/N := (Nat.le_div_iff_mul_le hN).2 hn
  have hq : n/N ≠ 0 := (lt_of_lt_of_le (by positivity) hpow).ne'
  exact (Nat.le_log2 hq).2 hpow

private lemma ratio_tendsto_of_doubling {f : ℕ → ℝ} (h₀ : ∀ n, 0 ≤ f n)
    (hf : Monotone f) (hd : ∀ᶠ n in atTop, f (2*n) ≤ (3/2 : ℝ)*f n) :
    Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 hd
  let s := N+1
  have hs : 0 < s := by positivity
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hNs : N ≤ s := Nat.le_succ N
  have hScale (k : ℕ) : s ≤ 2^k*s := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right s (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2))
  have hExp (k : ℕ) : f (2^k*s) ≤ (3/2 : ℝ)^k*f s := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' (2 : ℕ),mul_assoc,pow_succ' (3/2 : ℝ),mul_assoc]
      exact (hN _ (hNs.trans (hScale k))).trans
        (mul_le_mul_of_nonneg_left ih (by norm_num))
  let C : ℝ := (3/2 : ℝ)*f s / (s : ℝ)
  have hC : Tendsto (fun k : ℕ => C * (3/4 : ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4)
        (by norm_num)).const_mul C
  have hLim : Tendsto (fun n : ℕ => C * (3/4 : ℝ)^(n/s).log2) atTop (𝓝 0) :=
    hC.comp (log2_div_tendsto hs)
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (h₀ n) (Nat.cast_nonneg n))) _ hLim
  filter_upwards [eventually_ge_atTop s] with n hn
  let k := (n/s).log2
  have hq : n/s ≠ 0 := by
    have h₁ : 1 ≤ n/s := (Nat.le_div_iff_mul_le hs).2 (by simpa only [one_mul] using hn)
    omega
  have hlo : (2 : ℕ)^k*s ≤ n :=
    (Nat.le_div_iff_mul_le hs).1 ((Nat.le_log2 hq).1 (le_refl k))
  have hhi : n < (2 : ℕ)^(k+1)*s :=
    (Nat.div_lt_iff_lt_mul hs).1 ((Nat.log2_lt hq).1 (Nat.lt_succ_self k))
  have hd₀ : 0 < (2 : ℝ)^k*(s : ℝ) := by positivity
  have hd₁ : (2 : ℝ)^k*(s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
  change f n / (n : ℝ) ≤ C * (3/4 : ℝ)^k
  calc
    _ ≤ f n / ((2 : ℝ)^k*(s : ℝ)) := div_le_div_of_nonneg_left (h₀ n) hd₀ hd₁
    _ ≤ ((3/2 : ℝ)^(k+1)*f s) / ((2 : ℝ)^k*(s : ℝ)) :=
      div_le_div_of_nonneg_right ((hf hhi.le).trans (hExp (k+1))) hd₀.le
    _ = _ := by
      have hRatio : (3/4 : ℝ)^k = (3/2 : ℝ)^k / (2 : ℝ)^k := by
        rw [← div_pow]
        norm_num
      rw [hRatio,pow_succ' (3/2 : ℝ)]
      dsimp [C]
      field_simp [hsR.ne', pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]

theorem power_ratio {a : ℕ → ℕ} (ha : Monotone a)
    (hslow : Tendsto (fun n : ℕ => (a (2*n) : ℝ) / a n) atTop (𝓝 1)) (p : ℕ) :
    Tendsto (fun n : ℕ => (a n : ℝ)^p/(n : ℝ)) atTop (𝓝 0) := by
  let f (n : ℕ) : ℝ := (a n : ℝ)^p
  have h₀ (n : ℕ) : 0 ≤ f n := pow_nonneg (Nat.cast_nonneg _) _
  have hf : Monotone f := by
    intro m n hmn
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast ha hmn) _
  have hT : Tendsto (fun n : ℕ => ((a (2*n) : ℝ) / a n)^p) atTop (𝓝 1) := by
    simpa only [one_pow,Pi.pow_def] using hslow.pow p
  have hd : ∀ᶠ n in atTop, f (2*n) ≤ (3/2 : ℝ)*f n := by
    filter_upwards [hT.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 3/2)),
      hslow.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n h hn
    have ha₀ : 0 < (a n : ℝ) := by
      change 0 < (a (2*n) : ℝ) / (a n : ℝ) at hn
      by_contra! h
      have hz := le_antisymm h (Nat.cast_nonneg (a n))
      rw [hz,div_zero] at hn
      exact (lt_irrefl 0) hn
    change ((a (2*n) : ℝ)/(a n : ℝ))^p < (3/2 : ℝ) at h
    rw [div_pow] at h
    exact (div_le_iff₀ (pow_pos ha₀ _)).1 h.le
  exact ratio_tendsto_of_doubling h₀ hf hd

end ChenSparse

namespace ChenDichotomy

open Filter
open scoped Topology

private lemma separated {r s : ℝ} (hs : 1 ≤ s) (hp : 19 / 10 < r * s)
    (hd : (r - 1) * (s - 1) < 1 / 20) : r < 5 / 4 ∨ 3 / 2 < r := by
  by_contra! h
  have hS : 6 / 5 < s := by
    by_contra! hs'
    have hmul : r * s ≤ (3 / 2 : ℝ) * (6 / 5) :=
      mul_le_mul h.2 hs' (zero_le_one.trans hs) (by norm_num)
    linarith
  have hmul : (1 / 20 : ℝ) ≤ (r - 1) * (s - 1) := by
    calc
      _ = (1 / 4 : ℝ) * (1 / 5) := by norm_num
      _ ≤ _ := mul_le_mul (by linarith [h.1]) (by linarith) (by norm_num) (by linarith [h.1])
  linarith

private lemma step_bound {A A' T T' : ℝ} (hA : 32 ≤ A) (hAlo : A ≤ A')
    (hAhi : A' ≤ A + 1) (hTlo : T ≤ T') (hThi : T' ≤ T + 2) (hr0 : 0 ≤ T / A)
    (hr3 : T / A ≤ 3) : |T' / A' - T / A| < 1 / 4 := by
  have hApos : 0 < A := by linarith
  have hApos' : 0 < A' := by linarith
  let r := T / A
  change |T' / A' - r| < 1 / 4
  have hR : r * A = T := div_mul_cancel₀ _ hApos.ne'
  have hEq : T' / A' - r = ((T' - T) - r * (A' - A)) / A' := by
    apply (eq_div_iff hApos'.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hApos'.ne', mul_sub, hR]
    ring
  have hOn : 0 ≤ r * (A' - A) := mul_nonneg hr0 (sub_nonneg.mpr hAlo)
  have hOff : r * (A' - A) ≤ 3 := by
    calc
      _ ≤ 3 * (1 : ℝ) := mul_le_mul hr3 (by linarith) (sub_nonneg.mpr hAlo) (by norm_num)
      _ = _ := by norm_num
  rw [hEq, abs_div, abs_of_pos hApos', div_lt_iff₀ hApos']
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private lemma stable (r : ℕ → ℝ)
    (hGap : ∀ᶠ n in atTop, r n < 5 / 4 ∨ 3 / 2 < r n)
    (hStep : ∀ᶠ n in atTop, |r (n + 1) - r n| < 1 / 4) :
    (∀ᶠ n in atTop, r n < 5 / 4) ∨ (∀ᶠ n in atTop, 3 / 2 < r n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hGap.and hStep)
  have hSame (k : ℕ) : r (N + k) < 5 / 4 ↔ r N < 5 / 4 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hHere := (hN (N + k) (by omega)).1
      have hNext := (hN (N + k + 1) (by omega)).1
      obtain ⟨hl,hu⟩ := abs_lt.mp (hN (N + k) (by omega)).2
      have hIff : r (N + k + 1) < 5 / 4 ↔ r (N + k) < 5 / 4 := by
        rcases hHere with h | h <;> rcases hNext with h' | h' <;>
          constructor <;> intro hh <;> linarith
      exact hIff.trans ih
  have hUniform : ∀ᶠ n in atTop, r n < 5 / 4 ↔ r N < 5 / 4 :=
    eventually_atTop.mpr ⟨N,fun n hn => by
      have h := hSame (n - N)
      rwa [show N + (n - N) = n by omega] at h⟩
  by_cases hBase : r N < 5 / 4
  · exact Or.inl (hUniform.mono fun _ hn => hn.mpr hBase)
  · right
    filter_upwards [hUniform, hGap] with n hn hg
    exact hg.resolve_left (fun hl => hBase (hn.mp hl))

private lemma near_one {r s D : ℕ → ℝ} (hD : Tendsto D atTop (𝓝 0))
    (hFactor : ∀ᶠ n in atTop, (r n - 1) * (s n - 1) = D n)
    (hr : ∀ᶠ n in atTop, 1 ≤ r n) (hs : ∀ᶠ n in atTop, 3 / 2 < s n) :
    Tendsto r atTop (𝓝 1) := by
  have hUp : Tendsto (fun n => 1 + 2 * D n) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := (2 : ℝ))).mul hD)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUp hr ?_
  filter_upwards [hFactor, hr, hs] with n hf hr hs
  have hmul : (r n - 1) * (1 / 2) ≤ (r n - 1) * (s n - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hr)
  linarith

/-- Under exact product asymptotics and the rectangle bound, one side is sparse. -/
theorem sparse_side {a b : ℕ → ℕ} {K : ℝ} (ha : Monotone a) (hb : Monotone b)
    (haInf : Tendsto a atTop atTop) (hbInf : Tendsto b atTop atTop)
    (hJump : ∀ n, a (n + 1) ≤ a n + 1)
    (hprod : Tendsto (fun n => (a n : ℝ) * b n / (n : ℝ)) atTop (𝓝 1))
    (hRect : ∀ᶠ n in atTop,
      ((a (2 * n) : ℝ) - a n) * ((b (2 * n) : ℝ) - b n) ≤
        (a (2 * n) : ℝ) * b (2 * n) - (2 * n : ℕ) + K) :
    Tendsto (fun n => (a (2 * n) : ℝ) / a n) atTop (𝓝 1) ∨
      Tendsto (fun n => (b (2 * n) : ℝ) / b n) atTop (𝓝 1) := by
  let r (n : ℕ) : ℝ := (a (2 * n) : ℝ) / a n
  let s (n : ℕ) : ℝ := (b (2 * n) : ℝ) / b n
  let p (n : ℕ) : ℝ := (a n : ℝ) * b n / n
  let D (n : ℕ) : ℝ := (r n - 1) * (s n - 1)
  let U (n : ℕ) : ℝ := (2 * (p (2 * n) - 1) + K / (n : ℝ)) / p n
  change Tendsto r atTop (𝓝 1) ∨ Tendsto s atTop (𝓝 1)
  have haBig : ∀ᶠ n in atTop, 32 ≤ a n := tendsto_atTop.mp haInf 32
  have hbBig : ∀ᶠ n in atTop, 1 ≤ b n := tendsto_atTop.mp hbInf 1
  have hPos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < a n ∧ (0 : ℝ) < b n ∧ (0 : ℝ) < n := by
    filter_upwards [haBig,hbBig,eventually_ge_atTop (1 : ℕ)] with n haN hbN hn
    exact ⟨by exact_mod_cast (show 0 < a n by omega),
      by exact_mod_cast (show 0 < b n by omega),
      by exact_mod_cast (show 0 < n by omega)⟩
  have hOne : ∀ᶠ n in atTop, 1 ≤ r n ∧ 1 ≤ s n := by
    filter_upwards [hPos] with n hn
    have hn' : n ≤ 2 * n := by omega
    constructor
    · exact (le_div_iff₀ hn.1).mpr (by simpa using (show (a n : ℝ) ≤ a (2 * n) by exact_mod_cast ha hn'))
    · exact (le_div_iff₀ hn.2.1).mpr (by simpa using (show (b n : ℝ) ≤ b (2 * n) by exact_mod_cast hb hn'))
  have hP : Tendsto p atTop (𝓝 1) := hprod
  have hDouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id
  have hP₂ : Tendsto (fun n => p (2 * n)) atTop (𝓝 1) := hP.comp hDouble
  have hProd : Tendsto (fun n => r n * s n) atTop (𝓝 2) := by
    have hPrep : Tendsto (fun n => 2 * (p (2 * n) / p n)) atTop (𝓝 2) := by
      simpa only [Pi.div_apply, div_one, mul_one] using
        (tendsto_const_nhds (x := (2 : ℝ))).mul (hP₂.div hP one_ne_zero)
    apply hPrep.congr'
    filter_upwards [hPos] with n hn
    obtain ⟨haN,hbN,hn⟩ := hn
    simp only [r, s, p, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [haN.ne', hbN.ne', hn.ne']
  have hU : Tendsto U atTop (𝓝 0) := by
    have hNum := ((tendsto_const_nhds (x := (2 : ℝ))).mul
      (hP₂.sub (tendsto_const_nhds (x := (1 : ℝ))))).add
      (tendsto_const_div_atTop_nhds_zero_nat K)
    simpa only [U, Pi.div_def, sub_self, mul_zero, add_zero, zero_div] using hNum.div hP one_ne_zero
  have hD : Tendsto D atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
    · exact hOne.mono fun _ hn => mul_nonneg (sub_nonneg.mpr hn.1) (sub_nonneg.mpr hn.2)
    · filter_upwards [hPos,hRect] with n hn hrect
      obtain ⟨haN,hbN,hn⟩ := hn
      have hR : r n - 1 = ((a (2 * n) : ℝ) - a n) / a n := by
        rw [sub_div, div_self haN.ne']
      have hS : s n - 1 = ((b (2 * n) : ℝ) - b n) / b n := by
        rw [sub_div, div_self hbN.ne']
      have hUR : U n = ((a (2 * n) : ℝ) * b (2 * n) - (2 * n : ℕ) + K) /
          ((a n : ℝ) * b n) := by
        simp only [U, p, Nat.cast_mul, Nat.cast_ofNat]
        field_simp [haN.ne', hbN.ne', hn.ne']
      change (r n - 1) * (s n - 1) ≤ U n
      rw [hR, hS, hUR, div_mul_div_comm]
      exact div_le_div_of_nonneg_right hrect (mul_nonneg haN.le hbN.le)
  have hProdLo : ∀ᶠ n in atTop, 19 / 10 < r n * s n :=
    hProd.eventually (Ioi_mem_nhds (by norm_num))
  have hProdHi : ∀ᶠ n in atTop, r n * s n < 3 :=
    hProd.eventually (Iio_mem_nhds (by norm_num))
  have hSeparated : ∀ᶠ n in atTop, r n < 5 / 4 ∨ 3 / 2 < r n := by
    filter_upwards [hOne, hProdLo, hD.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))]
      with n hn hp hd
    exact separated hn.2 hp hd
  have hStep : ∀ᶠ n in atTop, |r (n + 1) - r n| < 1 / 4 := by
    filter_upwards [haBig, hOne, hProdHi] with n haN ho hp
    have hr0 : 0 ≤ r n := by linarith [ho.1]
    have hr3 : r n ≤ 3 := by
      have hrle : r n ≤ r n * s n := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left ho.2 hr0
      exact hrle.trans hp.le
    have haDouble : a (2 * (n + 1)) ≤ a (2 * n) + 2 := by
      have h₁ := hJump (2 * n)
      have h₂ := hJump (2 * n + 1)
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      omega
    change |(a (2 * (n + 1)) : ℝ) / a (n + 1) - (a (2 * n) : ℝ) / a n| < 1 / 4
    exact step_bound (by exact_mod_cast haN) (by exact_mod_cast ha (Nat.le_succ n))
      (by exact_mod_cast hJump n) (by exact_mod_cast ha (by omega : 2 * n ≤ 2 * (n + 1)))
      (by exact_mod_cast haDouble) hr0 hr3
  rcases stable r hSeparated hStep with hlo | hhi
  · left
    have hsHi : ∀ᶠ n in atTop, 3 / 2 < s n := by
      filter_upwards [hlo, hProdLo, hOne] with n hr hp ho
      by_contra! hs
      have hmul : r n * s n ≤ (5 / 4 : ℝ) * (3 / 2) :=
        mul_le_mul hr.le hs (by linarith [ho.2]) (by norm_num)
      linarith
    exact near_one hD (Eventually.of_forall fun _ => rfl) (hOne.mono fun _ hn => hn.1) hsHi
  · right
    exact near_one hD (Eventually.of_forall fun _ => mul_comm _ _) (hOne.mono fun _ hn => hn.2) hhi

end ChenDichotomy

private theorem chenFangEstimate : type_of% @Erdos785.erdos_785.variants.chen_fang := by
  intro A B hA hB hA0 hB0 h M hM
  obtain ⟨K, hCov⟩ := eventually_atTop.mp h.1
  have ha := RuzsaLimits.counting_monotone A
  have hb := RuzsaLimits.counting_monotone B
  have hD := ChenDichotomy.sparse_side (K := (K : ℝ)) ha hb
    (RuzsaProof.count_tendsto hA hA0) (RuzsaProof.count_tendsto hB hB0)
    (ChenCount.jump A) h.2 (Eventually.of_forall (ChenCount.rectangle A B hA0 hB0 K hCov))
  rcases hD with hSlow | hSlow
  · exact ChenFinish.sparse_bound A B hA hB hA0 hB0 h hSlow
      (ChenSparse.power_ratio ha hSlow) M hM
  · have hSwap : IsExactAdditiveComplement B A :=
      ⟨h.1.symm, by simpa only [mul_comm] using h.2⟩
    have hBound := ChenFinish.sparse_bound B A hB hA hB0 hA0 hSwap hSlow
      (ChenSparse.power_ratio hb hSlow) M hM
    simpa only [min_comm, mul_comm] using hBound

theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.sarkozy_szemeredi := by
  intro A B hA hB hA0 hB0 h
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [chenFangEstimate A B hA hB hA0 hB0 h 2 (by norm_num)] with x hx
  rw [Real.rpow_two] at hx
  rw [one_mul]
  have count_le_sq (k : ℕ) : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    exact_mod_cast (Nat.le_self_pow (by decide : 2 ≠ 0) k)
  rw [← Nat.cast_min] at hx ⊢
  exact (count_le_sq _).trans hx
