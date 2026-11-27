import OMAReductions.R_Erdos470_erdos_470_variants_weird_pos_density_R1
import Mathlib

/-! # Existence of the natural density of abundant numbers

Credit: @marcusbuffett. The two estimates below prove the hypotheses of the periodic approximation reduction.
-/
section

-- Credit: @marcusbuffett
-- Periodic counting follows @VinnyMo’s merged proof of Erdos697.density_exists, which credits @GMoney4362.
namespace OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1
open Filter
open scoped Topology
private lemma periodic_hasDensity {p : ℕ → Prop} {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) :
    ∃ δ : ℝ, {n : ℕ | p n}.HasDensity δ := by
  classical
  let count := Nat.count p
  let density : ℝ := (count d : ℝ) / (d : ℝ)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdensity : 0 ≤ density := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hdensity_le : density ≤ 1 := by
    apply (div_le_one hd').mpr
    exact_mod_cast Nat.count_le (p := p) (n := d)
  have hshift (n : ℕ) : Nat.count (fun i ↦ p (i + d)) n = count n := by
    change Nat.count (fun i ↦ p (i + d)) n = Nat.count p n
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [Finset.mem_filter, hp i]
  have hblocks (q r : ℕ) : count (q * d + r) = q * count d + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      change Nat.count p ((q + 1) * d + r) = (q + 1) * count d + count r
      rw [Nat.succ_mul, add_right_comm (q * d) d r, Nat.count_add', hshift]
      change count (q * d + r) + count d = (q + 1) * count d + count r
      rw [ih, Nat.succ_mul, add_right_comm]
  have hncard (n : ℕ) : ({m : ℕ | p m} ∩ Set.Iio n).ncard = count n := by
    rw [show {m : ℕ | p m} ∩ Set.Iio n =
        (↑((Finset.range n).filter p) : Set ℕ) by ext m; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
  have herr : ∀ᶠ n : ℕ in atTop, |(count n : ℝ) / (n : ℝ) - density| ≤ (d : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let r := n % d
    let q := n / d
    have hsplit : q * d + r = n := by simpa [q, r, mul_comm] using Nat.div_add_mod n d
    have hcount : q * count d + count r = count n := (hblocks q r).symm.trans (congrArg count hsplit)
    have hsplit' : (q : ℝ) * (d : ℝ) + (r : ℝ) = (n : ℝ) := by exact_mod_cast hsplit
    have hcount' : (q : ℝ) * (count d : ℝ) + (count r : ℝ) = (count n : ℝ) := by
      exact_mod_cast hcount
    have hd_mul : (d : ℝ) * density = (count d : ℝ) :=
      mul_div_cancel₀ _ hd'.ne'
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn).bot_lt
    have hr : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt n hd).le
    have hcount_r : (count r : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.count_le (p := p)
    have herror : (count n : ℝ) / (n : ℝ) - density =
        ((count r : ℝ) - (r : ℝ) * density) / (n : ℝ) := by
      apply (eq_div_iff hn'.ne').mpr
      calc
        _ = (count n : ℝ) - (n : ℝ) * density := by field_simp
        _ = _ := by rw [← hcount', ← hsplit', add_mul, mul_assoc, hd_mul]; ring
    rw [herror, abs_div, abs_of_pos hn']
    apply div_le_div_of_nonneg_right _ hn'.le
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left hdensity_le (Nat.cast_nonneg r)
      linarith [Nat.cast_nonneg (α := ℝ) (count r)]
    · have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hdensity
      linarith
  have ht : Tendsto (fun n : ℕ ↦ (count n : ℝ) / (n : ℝ) - density) atTop (𝓝 0) := by
    have hu := tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
    have hl : Tendsto (fun n : ℕ ↦ -((d : ℝ) / n)) atTop (𝓝 0) := by
      simpa only [neg_zero] using hu.neg
    refine hl.squeeze' hu ?_ ?_
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).1
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).2
  refine ⟨density, ?_⟩
  simpa [Set.HasDensity, Set.partialDensity, hncard] using ht.add_const density

open Filter Set
open scoped Topology


def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ᶠ b : ℕ in atTop,
    {n : ℕ | δ ≤ |(n.abundancyIndex : ℝ) - ((n.gcd K.factorial).abundancyIndex : ℝ)|}.partialDensity univ b < ε

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ K : ℕ in atTop, ∀ᶠ b : ℕ in atTop,
    {n : ℕ | |((n.gcd K.factorial).abundancyIndex : ℝ) - 2| ≤ δ}.partialDensity univ b < ε

private lemma union_bound {S A B : Set ℕ} (h : S ⊆ A ∪ B) (b : ℕ) :
    S.partialDensity univ b ≤ A.partialDensity univ b + B.partialDensity univ b := by
  simp only [partialDensity,inter_univ,univ_inter,← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hs : S ∩ Iio b ⊆ (A ∩ Iio b) ∪ (B ∩ Iio b) := by
    intro x hx
    rcases h hx.1 with ha | hb
    · exact Or.inl ⟨ha,hx.2⟩
    · exact Or.inr ⟨hb,hx.2⟩
  exact_mod_cast (ncard_le_ncard hs (((finite_Iio b).subset inter_subset_right).union
    ((finite_Iio b).subset inter_subset_right))).trans (ncard_union_le _ _)

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H1 := by
  intro htail hboundary
  let A : Set ℕ := {n | n.Abundant}
  change ∃ a : ℝ, Tendsto (fun b => A.partialDensity univ b) atTop (𝓝 a)
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have he : 0 < ε / 8 := by positivity
  obtain ⟨δ,hδ,hband⟩ := hboundary (ε/8) he
  obtain ⟨K,hK,hJ⟩ := (hband.and (htail δ hδ (ε/8) he)).exists
  let T : Set ℕ := {n | 2 < ((n.gcd K.factorial).abundancyIndex : ℝ)}
  let V : Set ℕ := {n : ℕ | |((n.gcd K.factorial).abundancyIndex : ℝ) - 2| ≤ δ}
  let W : Set ℕ := {n : ℕ | δ ≤ |(n.abundancyIndex : ℝ) - ((n.gcd K.factorial).abundancyIndex : ℝ)|}
  have eqv (n : ℕ) (hv : n ∉ V) (hw : n ∉ W) : n ∈ A ↔ n ∈ T := by
    change ¬ |((n.gcd K.factorial).abundancyIndex : ℝ) - 2| ≤ δ at hv
    change ¬ δ ≤ |(n.abundancyIndex : ℝ) - ((n.gcd K.factorial).abundancyIndex : ℝ)| at hw
    have h := abs_lt.mp (lt_of_not_ge hw)
    change n.Abundant ↔ 2 < ((n.gcd K.factorial).abundancyIndex : ℝ)
    rw [Nat.abundant_iff_two_lt_abundancyIndex]
    have hc : (2 < n.abundancyIndex) ↔ (2 : ℝ) < (n.abundancyIndex : ℝ) := by constructor <;> intro h <;> exact_mod_cast h
    rw [hc]
    have hp := lt_of_not_ge hv
    rcases lt_abs.mp hp with hp | hp <;> constructor <;> intro hx <;> linarith
  have hab : A ⊆ T ∪ (V ∪ W) := by
    intro n hn
    by_cases h : n ∈ V ∪ W
    · exact Or.inr h
    · exact Or.inl ((eqv n (fun hv => h (Or.inl hv)) (fun hw => h (Or.inr hw))).mp hn)
  have hba : T ⊆ A ∪ (V ∪ W) := by
    intro n hn
    by_cases h : n ∈ V ∪ W
    · exact Or.inr h
    · exact Or.inl ((eqv n (fun hv => h (Or.inl hv)) (fun hw => h (Or.inr hw))).mpr hn)
  obtain ⟨a,ha⟩ := periodic_hasDensity (p := fun n => n ∈ T) (Nat.factorial_pos K) (by
    intro n
    simp only [T,mem_setOf_eq,Nat.gcd_comm, Nat.gcd_add_self_right])
  change Tendsto (fun b => T.partialDensity univ b) atTop (𝓝 a) at ha
  have hh := Metric.tendsto_nhds.mp ha (ε/8) he
  have hall : ∀ᶠ b : ℕ in atTop, |A.partialDensity univ b - a| < 3 * (ε/8) := by
    filter_upwards [hK,hJ,hh] with b hb hj ht
    have hsmall := union_bound (S := V ∪ W) Subset.rfl b
    have h1 := union_bound hab b
    have h2 := union_bound hba b
    change V.partialDensity univ b < ε/8 at hb
    change W.partialDensity univ b < ε/8 at hj
    rw [Real.dist_eq] at ht
    obtain ⟨hl,hu⟩ := abs_lt.mp ht
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [Real.dist_eq]
  obtain ⟨hml,hmu⟩ := abs_lt.mp (hN m hm)
  obtain ⟨hnl,hnu⟩ := abs_lt.mp (hN n hn)
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

end OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1
end
section
/-!
# Large-divisor tail for the abundancy index

Credit: @marcusbuffett. Divisors at most K already divide K factorial.
Count the multiples of each remaining divisor before taking the reciprocal-square tail.
-/
open Filter Finset
open scoped Topology
namespace Tail470
lemma index_sum {n : ℕ} (hn : 0<n) :
    (n.abundancyIndex:ℝ) = ∑ d ∈ n.divisors, (1:ℝ)/d := by
  simp only [Nat.abundancyIndex,Rat.cast_div,Rat.cast_natCast,Nat.cast_sum,Rat.cast_sum]
  rw [←Nat.sum_div_divisors n (fun d : ℕ => (d:ℝ)),Finset.sum_div]
  apply sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
  have hn' : (n:ℝ) ≠ 0 := by positivity
  field_simp
lemma point {K n b : ℕ} (hn : 0<n) (hnb : n≤b) :
    |(n.abundancyIndex:ℝ) - ((n.gcd K.factorial).abundancyIndex:ℝ)| ≤
      ∑ d ∈ Ioc K b, if d∣n then (1:ℝ)/d else 0 := by
  let g := n.gcd K.factorial
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ hn
  have hsub : g.divisors ⊆ n.divisors := by
    intro d hd
    exact Nat.mem_divisors.2 ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left ..),hn.ne'⟩
  have hmono : (g.abundancyIndex:ℝ) ≤ n.abundancyIndex := by
    exact_mod_cast Nat.abundancyIndex_le_of_dvd hn.ne' (Nat.gcd_dvd_left n K.factorial)
  change |(n.abundancyIndex:ℝ) - (g.abundancyIndex:ℝ)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.2 hmono),index_sum hn,index_sum hg,
    ← sum_sdiff hsub (f:=fun d : ℕ => (1:ℝ)/d),add_sub_cancel_right,←sum_filter]
  apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
  intro d hd
  obtain ⟨hd,hdg⟩ := Finset.mem_sdiff.1 hd
  have hdn := Nat.dvd_of_mem_divisors hd
  have hdp := Nat.pos_of_dvd_of_pos hdn hn
  have hKd : K<d := by
    by_contra! h
    exact hdg (Nat.mem_divisors.2 ⟨Nat.dvd_gcd hdn (Nat.dvd_factorial hdp h),hg.ne'⟩)
  exact mem_filter.2 ⟨mem_Ioc.2 ⟨hKd,(Nat.le_of_dvd hn hdn).trans hnb⟩,hdn⟩
noncomputable abbrev err (K n : ℕ) := |(n.abundancyIndex:ℝ) - ((n.gcd K.factorial).abundancyIndex:ℝ)|
lemma total {b K : ℕ} (hK : 0<K) (hb : K≤b) :
    ∑ n ∈ Ioc 0 b, err K n ≤ (b:ℝ)/K := by
  calc _ ≤ ∑ n ∈ Ioc 0 b, ∑ d ∈ Ioc K b, if d∣n then (1:ℝ)/d else 0 :=
          sum_le_sum fun n hn => point (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2
       _ = ∑ d ∈ Ioc K b, ∑ n ∈ Ioc 0 b, if d∣n then (1:ℝ)/d else 0 := sum_comm
       _ ≤ ∑ d ∈ Ioc K b, (b:ℝ)*((d:ℝ)^2)⁻¹ := by
          apply sum_le_sum
          intro d _
          rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
          calc ((b/d:ℕ):ℝ)*(1/d) ≤ ((b:ℝ)/d)*(1/d) := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
               _ = _ := by ring
       _ ≤ _ := by
          rw [← mul_sum,div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          have := sum_Ioc_inv_sq_le_sub (α:=ℝ) hK.ne' hb
          linarith [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) b)]
end Tail470

open Tail470 in
theorem Tail470.tail : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1.H1 := by
  classical
  intro δ hδ ε hε
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (2/(δ*ε)), eventually_gt_atTop 0] with K hKe hK
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (2/ε),eventually_ge_atTop K] with b hbe hKb
  let B := (Ioc 0 b).filter fun n => δ ≤ err K n
  let A := {n : ℕ | δ ≤ err K n}
  have hmark : δ*(B.card:ℝ) ≤ (b:ℝ)/K := by
    calc _ = ∑ _ ∈ B, δ := by simp [mul_comm]
         _ ≤ ∑ n ∈ B, err K n := sum_le_sum fun n hn => (mem_filter.1 hn).2
         _ ≤ ∑ n ∈ Ioc 0 b, err K n := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => abs_nonneg _)
         _ ≤ _ := total hK hKb
  have hsub : A ∩ Set.Iio b ⊆ (↑(insert 0 B) : Set ℕ) := by
    rintro n ⟨hn,hn'⟩
    apply Finset.mem_insert.2
    rcases Nat.eq_zero_or_pos n with h|h
    · exact Or.inl h
    · exact Or.inr (mem_filter.2 ⟨mem_Ioc.2 ⟨h,hn'.le⟩,hn⟩)
  have hcard : (A ∩ Set.Iio b).ncard ≤ B.card+1 := by
    have h := Set.ncard_le_ncard hsub (insert 0 B).finite_toSet
    rw [Set.ncard_coe_finset] at h
    exact h.trans (card_insert_le ..)
  have hcard' : ((A ∩ Set.Iio b).ncard:ℝ) ≤ B.card+1 := by exact_mod_cast hcard
  change A.partialDensity Set.univ b < ε
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Set.ncard_Iio_nat]
  have hb' := Nat.cast_pos (α:=ℝ).2 (hK.trans_le hKb)
  have hk' := Nat.cast_pos (α:=ℝ).2 hK
  apply (div_lt_iff₀ hb').2
  have heK := (div_lt_iff₀ (mul_pos hδ hε)).1 hKe
  have heb := (div_lt_iff₀ hε).1 hbe
  have hmid : (b:ℝ)/K < δ*(ε*b/2) := by
    apply (div_lt_iff₀ hk').2
    nlinarith only [mul_lt_mul_of_pos_right heK hb']
  have hsmall : (B.card:ℝ) < ε*b/2 := (mul_lt_mul_iff_right₀ hδ).1 (hmark.trans_lt hmid)
  linarith
end
section

/-!
# Anti-concentration of the truncated abundancy index

Credit: @marcusbuffett. Select finitely many large odd primes for which the
product of (1 − 1/p) is small. Among squarefree products of these primes,
the largest differing prime separates any two abundancy indices. After removing
square multiples, at most one product can hit a sufficiently short interval
for each fixed part coprime to the chosen primes. Counting gcd classes with
Euler's totient bounds the size of the interval event over a complete period.
-/


section
open Finset
namespace Sep470
noncomputable abbrev idx (n : ℕ) := (n.abundancyIndex:ℝ)
noncomputable def rat (s : Finset ℕ) := ∏ p ∈ s, (((p:ℝ)+1)/p)
lemma idx_mul {a b : ℕ} (hc : a.Coprime b) : idx (a*b)=idx a*idx b := by
  unfold idx Nat.abundancyIndex
  rw [hc.sum_divisors_mul]; push_cast; ring
lemma idx_one_le {n : ℕ} (hn : 0<n) : 1 ≤ idx n := by
  have h := Nat.abundancyIndex_le_of_dvd hn.ne' (one_dvd n)
  have h1 : (1:ℕ).abundancyIndex=1 := by simp [Nat.abundancyIndex]
  rw [h1] at h; exact_mod_cast h
lemma idx_prod (s : Finset ℕ) (hs : ∀ p∈s,p.Prime) : idx (∏ p∈s,p)=rat s := by
  induction s using Finset.induction_on with
  | empty => simp [idx,rat,Nat.abundancyIndex]
  | @insert p s hn ih =>
    have hp := hs p (mem_insert_self ..)
    have hs' (q : ℕ) (hq : q∈s) := hs q (mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q∈s,q) := by
      apply hp.coprime_iff_not_dvd.2
      rw [hp.prime.dvd_finsetProd_iff]
      rintro ⟨q,hq,hd⟩
      exact hn (((Nat.prime_dvd_prime_iff_eq hp (hs' q hq)).1 hd) ▸ hq)
    have hval : idx p=((p:ℝ)+1)/p := by
      unfold idx Nat.abundancyIndex
      rw [hp.sum_divisors]; push_cast; ring
    rw [prod_insert hn,idx_mul hc,hval,ih hs']
    simp only [rat,prod_insert hn]
lemma rat_eq_cross {s t : Finset ℕ} (hs : ∀ p∈s,0<p) (ht : ∀ p∈t,0<p) (he : rat s=rat t) :
    (∏ q∈s,(q+1))*(∏ q∈t,q)=(∏ q∈t,(q+1))*(∏ q∈s,q) := by
  have hsp : (0:ℝ) < ∏ p∈s,(p:ℝ) := prod_pos fun p hp => by exact_mod_cast hs p hp
  have htp : (0:ℝ) < ∏ p∈t,(p:ℝ) := prod_pos fun p hp => by exact_mod_cast ht p hp
  simp only [rat,prod_div_distrib] at he
  apply Nat.cast_injective (R:=ℝ)
  push_cast
  exact (div_eq_div_iff hsp.ne' htp.ne').1 he
lemma nodvd_next {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : 2<p) (hq2 : 2<q) (hle : q≤p) :
    ¬p∣q+1 := by
  intro hd
  have hqp := Nat.le_of_dvd (Nat.succ_pos q) hd
  by_cases he : q=p
  · subst q
    have hone := (Nat.dvd_add_right (dvd_refl p)).1 hd
    have := Nat.le_of_dvd (by decide : 0<1) hone
    omega
  · have he' : q+1=p := by omega
    have hodd := hp.odd_of_ne_two (by omega)
    have hodd' := hq.odd_of_ne_two (by omega)
    obtain ⟨a,ha⟩ := hodd; obtain ⟨b,hb⟩ := hodd'; omega
lemma no_max {s t : Finset ℕ} {p : ℕ} (hp : p∈s) (hpn : p∉t)
    (hs : ∀ q∈s,q.Prime ∧ 2<q ∧ q≤p)
    (ht : ∀ q∈t,q.Prime ∧ 2<q ∧ q≤p) (he : rat s=rat t) : False := by
  obtain ⟨hpr,h2,_⟩ := hs p hp
  have hcross := rat_eq_cross (fun i hi => (hs i hi).1.pos) (fun i hi => (ht i hi).1.pos) he
  have hd : p∣ (∏ q∈t,(q+1))*(∏ q∈s,q) := dvd_mul_of_dvd_right (dvd_prod_of_mem id hp) _
  rw [←hcross,hpr.dvd_mul] at hd
  rcases hd with hd|hd <;> obtain ⟨q,hq,h⟩ := (hpr.prime.dvd_finsetProd_iff _).1 hd
  · exact nodvd_next hpr (hs q hq).1 h2 (hs q hq).2.1 (hs q hq).2.2 h
  · exact hpn (((Nat.prime_dvd_prime_iff_eq hpr (ht q hq).1).1 h) ▸ hq)
lemma rat_inj {s t : Finset ℕ} (hs : ∀ p∈s,p.Prime ∧ 2<p) (ht : ∀ p∈t,p.Prime ∧ 2<p)
    (he : rat s=rat t) : s=t := by
  let I := s∩t
  let A := s\I
  let B := t\I
  have hI : 0<rat I := prod_pos fun p hp => div_pos (by positivity) (Nat.cast_pos.2 (hs p (mem_inter.1 hp).1).1.pos)
  have he' : rat A=rat B := by
    apply mul_right_cancel₀ hI.ne' (b:=rat I)
    change rat (s\I)*rat I = rat (t\I)*rat I
    simpa only [rat,Finset.prod_sdiff (inter_subset_left (s₁:=s) (s₂:=t)),Finset.prod_sdiff (inter_subset_right (s₁:=s) (s₂:=t)),I] using he
  by_contra hne
  have hu : (A∪B).Nonempty := by
    by_contra! hn
    apply hne
    ext p
    have hh : p∉A∪B := by simp [hn]
    simp only [A,B,I,mem_union,Finset.mem_sdiff,mem_inter] at hh
    tauto
  let p := (A∪B).max' hu
  have hm := Finset.max'_mem (A∪B) hu
  have ha (q : ℕ) (hq : q∈A) : q.Prime ∧ 2<q ∧ q≤p :=
    ⟨(hs q (Finset.mem_sdiff.1 hq).1).1,(hs q (Finset.mem_sdiff.1 hq).1).2,le_max' _ _ (mem_union_left _ hq)⟩
  have hb (q : ℕ) (hq : q∈B) : q.Prime ∧ 2<q ∧ q≤p :=
    ⟨(ht q (Finset.mem_sdiff.1 hq).1).1,(ht q (Finset.mem_sdiff.1 hq).1).2,le_max' _ _ (mem_union_right _ hq)⟩
  have hd (hp : p∈A) (hq : p∈B) : False := (Finset.mem_sdiff.1 hp).2 (mem_inter.2 ⟨(Finset.mem_sdiff.1 hp).1,(Finset.mem_sdiff.1 hq).1⟩)
  rcases mem_union.1 hm with h|h
  · exact no_max h (hd h) ha hb he'
  · exact no_max h (fun hh => hd hh h) hb ha he'.symm
end Sep470
end

section
open Filter Finset Real
open scoped Topology
namespace Sep470
noncomputable abbrev avoid (S : Finset ℕ) := ∏ p∈S,(1-(p:ℝ)⁻¹)
lemma choose_primes (L : ℕ) {η : ℝ} (hη : 0<η) : ∃ S : Finset ℕ,
    (∀ p∈S,p.Prime ∧ L<p) ∧ avoid S < η := by
  classical
  let f (p : ℕ) := if p.Prime ∧ L<p then (1:ℝ)/p else 0
  have hE : f =ᶠ[atTop] Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1:ℝ)/n) := by
    filter_upwards [eventually_gt_atTop L] with p hp
    by_cases h : p.Prime <;> simp [f,Set.indicator,h,hp]
  have hns : ¬Summable f := fun h => not_summable_one_div_on_primes ((summable_congr_atTop hE).1 h)
  have htop := (not_summable_iff_tendsto_nat_atTop_of_nonneg (f:=f) (fun p => by dsimp [f]; split_ifs <;> positivity)).1 hns
  obtain ⟨N,hN⟩ := (htop.eventually_gt_atTop (-log η)).exists
  let S := (range N).filter (fun p => p.Prime ∧ L<p)
  have hs (p : ℕ) (hp : p∈S) : p.Prime ∧ L<p := (mem_filter.1 hp).2
  refine ⟨S,hs,?_⟩
  have hsum : ∑ p∈S,(p:ℝ)⁻¹ = ∑ p∈range N,f p := by simp [S,f,sum_filter,one_div]
  calc avoid S ≤ ∏ p∈S,exp (-(p:ℝ)⁻¹) := by
          apply Finset.prod_le_prod
          · intro p hp
            have h1 : (1:ℝ)≤p := by exact_mod_cast (hs p hp).1.one_le
            exact sub_nonneg.2 (inv_le_one_of_one_le₀ h1)
          · intro p _
            linarith [add_one_le_exp (-(p:ℝ)⁻¹)]
       _ = exp (-(∑ p∈S,(p:ℝ)⁻¹)) := by rw [←Real.exp_sum,Finset.sum_neg_distrib]
       _ < η := by rw [←lt_log_iff_exp_lt hη,hsum]; linarith
lemma split_prime_parts (D : ℕ) (hD : 0<D) (S : Finset ℕ) (hS : S ⊆ D.primeFactors) :
    ∃ Q R : ℕ, 0<Q ∧ 0<R ∧ D=Q*R ∧ Q.Coprime R ∧ R.primeFactors=S := by
  let pp (p : ℕ) := p^(D.factorization p)
  let Q := ∏ p∈D.primeFactors\S, pp p
  let R := ∏ p∈S, pp p
  have hpos {p : ℕ} (hp : p∈D.primeFactors) : 0<pp p := pow_pos (Nat.pos_of_mem_primeFactors hp) _
  have hQ : 0<Q := prod_pos fun p hp => hpos (Finset.mem_sdiff.1 hp).1
  have hR : 0<R := prod_pos fun p hp => hpos (hS hp)
  have hd : D=Q*R := by
    dsimp [Q,R,pp]
    rw [Finset.prod_sdiff hS]
    exact (Nat.prod_factorization_pow_eq_self hD.ne').symm
  have hmem (T : Finset ℕ) (hT : T⊆D.primeFactors) {p : ℕ} (hp : p.Prime) :
      p ∣ ∏ q∈T,pp q ↔ p∈T := by
    rw [hp.prime.dvd_finsetProd_iff]
    constructor
    · rintro ⟨q,hq,h⟩
      have hq' := Nat.prime_of_mem_primeFactors (hT hq)
      exact ((Nat.prime_dvd_prime_iff_eq hp hq').1 (hp.dvd_of_dvd_pow h)) ▸ hq
    · intro h
      refine ⟨p,h, dvd_pow_self _ ?_⟩
      exact Finsupp.mem_support_iff.1 (show p∈D.factorization.support from hT h)
  refine ⟨Q,R,hQ,hR,hd,Nat.coprime_of_dvd (fun p hp hq hr => ?_),?_⟩
  · exact (Finset.mem_sdiff.1 ((hmem _ sdiff_subset hp).1 hq)).2 ((hmem _ hS hp).1 hr)
  · ext p
    rw [Nat.mem_primeFactors]
    exact ⟨fun ⟨hp,h,_⟩ => (hmem _ hS hp).1 h,
      fun h => ⟨Nat.prime_of_mem_primeFactors (hS h),(hmem _ hS (Nat.prime_of_mem_primeFactors (hS h))).2 h,hR.ne'⟩⟩
lemma totient_ratio {R : ℕ} (hR : 0<R) : (R.totient:ℝ) = R * avoid R.primeFactors := by
  have h := congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors R)
  simpa [avoid] using h
end Sep470
end

section
open Finset
namespace Sep470
def clean (S : Finset ℕ) (n : ℕ) := ∀ p∈S, ¬p*p∣n
lemma clean_squarefree {S : Finset ℕ} {R s : ℕ} (hR : 0<R) (hRs : R.primeFactors=S)
    (hs : s∣R) (h : clean S s) : Squarefree s := by
  apply Nat.squarefree_iff_prime_squarefree.2
  intro p hp hd
  have hdiv : p∣R := (dvd_mul_right p p).trans (hd.trans hs)
  exact h p (hRs ▸ Nat.mem_primeFactors.2 ⟨hp,hdiv,hR.ne'⟩) hd
lemma idx_eq_rat {s : ℕ} (hs : Squarefree s) : idx s=rat s.primeFactors := by
  simpa only [Nat.prod_primeFactors_of_squarefree hs] using idx_prod s.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
lemma separation (S : Finset ℕ) (hs : ∀ p∈S,p.Prime ∧ 2<p) :
    ∃ δ : ℝ, 0<δ ∧ ∀ s u : ℕ, Squarefree s → Squarefree u →
      s.primeFactors⊆S → u.primeFactors⊆S → ∀ z : ℝ, 1≤z →
      |z*idx s-2|≤δ → |z*idx u-2|≤δ → s=u := by
  classical
  let F := S.powerset ×ˢ S.powerset
  let d (x : Finset ℕ × Finset ℕ) := if x.1=x.2 then (1:ℝ) else |rat x.1-rat x.2|
  have hF : F.Nonempty := ⟨(∅,∅),by simp [F]⟩
  let m := F.inf' hF d
  have hm : 0 < m := (Finset.lt_inf'_iff ..).2 fun x hx => by
    dsimp [d]; split_ifs with he
    · norm_num
    · apply abs_pos.2 (sub_ne_zero.2 (fun hr => he (rat_inj (fun p hp => hs p ((mem_powerset.1 (mem_product.1 hx).1) hp)) (fun p hp => hs p ((mem_powerset.1 (mem_product.1 hx).2) hp)) hr)))
  refine ⟨m/4,by positivity,?_⟩
  intro s u hsq huq hsS huS z hz hsδ huδ
  by_contra hsu
  have hne : s.primeFactors≠u.primeFactors := by
    intro h
    exact hsu (by rw [←Nat.prod_primeFactors_of_squarefree hsq,←Nat.prod_primeFactors_of_squarefree huq,h])
  have hx : (s.primeFactors,u.primeFactors)∈F := mem_product.2 ⟨mem_powerset.2 hsS,mem_powerset.2 huS⟩
  have hl := Finset.inf'_le (f:=d) hx
  change m ≤ d (s.primeFactors,u.primeFactors) at hl
  simp only [d,if_neg hne,←idx_eq_rat hsq,←idx_eq_rat huq] at hl
  have hdist := abs_sub_le (z*idx s) 2 (z*idx u)
  rw [abs_sub_comm 2 (z*idx u),←mul_sub,abs_mul,abs_of_nonneg (by linarith : 0≤z)] at hdist
  have hmult := mul_le_mul_of_nonneg_right hz (abs_nonneg (idx s-idx u))
  linarith
end Sep470
end

section
open Finset
open scoped Classical
namespace Sep470
lemma gcd_count {D : ℕ} (hD : 0<D) (G : ℕ → Prop) [DecidablePred G] :
    ((range D).filter (fun n => G (D.gcd n))).card =
      ∑ d∈D.divisors, if G d then (D/d).totient else 0 := by
  classical
  have hm (n : ℕ) (_ : n∈range D) : D.gcd n ∈ D.divisors :=
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left ..,hD.ne'⟩
  calc _ = ∑ n∈range D, if G (D.gcd n) then 1 else 0 := by simp [←sum_filter]
       _ = ∑ d∈D.divisors, ∑ _n ∈ (range D).filter (fun n => D.gcd n=d), if G d then 1 else 0 :=
          (sum_fiberwise_of_maps_to' hm (fun d => if G d then 1 else 0)).symm
       _ = _ := by
          apply sum_congr rfl
          intro d hd
          by_cases h : G d
          · simp [h,Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
          · simp [h]
lemma divisor_split_sum {Q R : ℕ} (hc : Q.Coprime R) (f : ℕ → ℕ) :
    (∑ d∈(Q*R).divisors, f d) = ∑ t∈Q.divisors, ∑ s∈R.divisors,f (t*s) := by
  rw [hc.divisors_mul,Finset.sum_map]
  change (∑ u∈(Q.divisors ×ˢ R.divisors).attach, f (u.1.1*u.1.2)) = _
  rw [Finset.sum_attach (s:=Q.divisors ×ˢ R.divisors) (f:=fun p => f (p.1*p.2)),Finset.sum_product]
lemma good_count {Q R : ℕ} (hQ : 0<Q) (hR : 0<R) (hc : Q.Coprime R) (S : Finset ℕ)
    (hRS : R.primeFactors=S) (δ : ℝ)
    (hsep : ∀ s u : ℕ, Squarefree s → Squarefree u → s.primeFactors⊆S → u.primeFactors⊆S →
      ∀ z : ℝ, 1≤z → |z*idx s-2|≤δ → |z*idx u-2|≤δ → s=u) :
    ((range (Q*R)).filter (fun n => clean S ((Q*R).gcd n) ∧ |idx ((Q*R).gcd n)-2|≤δ)).card ≤ Q*R.totient := by
  classical
  let G (d : ℕ) := clean S d ∧ |idx d-2|≤δ
  change ((range (Q*R)).filter (fun n => G ((Q*R).gcd n))).card ≤ _
  rw [gcd_count (mul_pos hQ hR) G,divisor_split_sum hc]
  calc _ ≤ ∑ t∈Q.divisors, ((Q/t).totient*R.totient) := by
         apply sum_le_sum
         intro t ht
         have htQ := Nat.dvd_of_mem_divisors ht
         have htpos := Nat.pos_of_mem_divisors ht
         let T := R.divisors.filter fun s => G (t*s)
         have hf : ∀ s∈T, Squarefree s ∧ s.primeFactors⊆S ∧ |idx t*idx s-2|≤δ := by
           intro s hs
           obtain ⟨hsR,hg⟩ := mem_filter.1 hs
           have hd := Nat.dvd_of_mem_divisors hsR
           have hc' := (hc.coprime_dvd_left htQ).coprime_dvd_right hd
           refine ⟨clean_squarefree hR hRS hd (fun p hp hpp => hg.1 p hp (hpp.trans (dvd_mul_left s t))),?_,?_⟩
           · rw [←hRS]; exact Nat.primeFactors_mono hd hR.ne'
           · simpa only [idx_mul hc'] using hg.2
         have hT : T.card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => hsep a b (hf a ha).1 (hf b hb).1
             (hf a ha).2.1 (hf b hb).2.1 (idx t) (idx_one_le htpos) (hf a ha).2.2 (hf b hb).2.2)
         rw [←sum_filter]
         change (∑ s∈T,((Q*R)/(t*s)).totient) ≤ _
         calc _ ≤ ∑ _s∈T, (Q/t).totient*R.totient := by
                apply sum_le_sum
                intro s hs
                have hsR := Nat.dvd_of_mem_divisors (mem_filter.1 hs).1
                have hdQ : Q/t∣Q := Nat.div_dvd_of_dvd htQ
                have hdR : R/s∣R := Nat.div_dvd_of_dvd hsR
                rw [←Nat.div_mul_div_comm htQ hsR,Nat.totient_mul ((hc.coprime_dvd_left hdQ).coprime_dvd_right hdR)]
                exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.totient_pos.2 hR) (Nat.totient_dvd_of_dvd hdR))
              _ ≤ _ := by simpa using Nat.mul_le_mul_right ((Q/t).totient*R.totient) hT
       _ = _ := by rw [←sum_mul,Nat.sum_div_divisors Q Nat.totient,Nat.sum_totient]
end Sep470
end

section
open Filter Finset
open scoped Classical Topology
namespace Sep470
lemma block_count (P : ℕ → Prop) [DecidablePred P] (D : ℕ) (hper : Function.Periodic P D) (q : ℕ) :
    Nat.count P (q*D) = q*Nat.count P D := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h : (fun n : ℕ => P (D+n))=P := funext fun n => by rw [add_comm]; exact hper n
    have hs : Nat.count (fun n : ℕ => P (D+n)) (q*D) = Nat.count P (q*D) := by
      simp only [Nat.count_eq_card_filter_range]
      congr 1
      ext n
      simp only [mem_filter,add_comm D n,hper n]
    rw [Nat.succ_mul,add_comm (q*D),Nat.count_add,hs,ih,Nat.succ_mul,add_comm]
lemma periodic_upper (P : ℕ → Prop) [DecidablePred P] {D b : ℕ} (hd : 0<D) (hb : D≤b)
    (hp : Function.Periodic P D) :
    (((range b).filter P).card:ℝ) ≤ 2*(b:ℝ)/D * ((range D).filter P).card := by
  have hh : ((range b).filter P).card ≤ (b/D+1)*((range D).filter P).card := by
    rw [←Nat.count_eq_card_filter_range,←Nat.count_eq_card_filter_range,←block_count P D hp]
    apply Nat.count_monotone
    simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ b hd).le
  have hr : (1:ℝ) ≤ (b:ℝ)/D := (one_le_div (Nat.cast_pos.2 hd)).2 (by exact_mod_cast hb)
  have hdv : ((b/D:ℕ):ℝ) ≤ (b:ℝ)/D := Nat.cast_div_le
  calc _ ≤ (((b/D:ℕ):ℝ)+1)*((range D).filter P).card := by exact_mod_cast hh
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
         rw [mul_div_assoc]; linarith
lemma square_bad (S : Finset ℕ) {L : ℕ} (hL : 0<L) (hS : ∀ p∈S,L<p) (b : ℕ) :
    (((range b).filter (fun n => ∃ p∈S,p*p∣n)).card : ℝ) ≤ 1+(b:ℝ)/L := by
  let B (p : ℕ) := (Ioc 0 b).filter (fun n => p*p∣n)
  have ht : (range b).filter (fun n => ∃ p∈S,p*p∣n) ⊆ insert 0 (S.biUnion B) := by
    intro n hn
    obtain ⟨hnb,p,hp,h⟩ := mem_filter.1 hn
    rcases n.eq_zero_or_pos with rfl|hpos
    · simp
    · exact mem_insert_of_mem (mem_biUnion.2 ⟨p,hp,mem_filter.2 ⟨mem_Ioc.2 ⟨hpos,(mem_range.1 hnb).le⟩,h⟩⟩)
  have hc := (card_le_card ht).trans (card_insert_le ..)
  have hu := card_biUnion_le (s:=S) (t:=B)
  have hnum : ((range b).filter (fun n => ∃ p∈S,p*p∣n)).card ≤ (∑ p∈S,b/(p*p))+1 := by
    simpa only [B,Nat.Ioc_filter_dvd_card_eq_div] using hc.trans (Nat.succ_le_succ hu)
  let U := max L (S.sup id)
  have hsub : S ⊆ Ioc L U := fun p hp => mem_Ioc.2 ⟨hS p hp,(le_sup (f:=id) hp).trans (le_max_right ..)⟩
  have htail : (∑ p∈S, ((p:ℝ)^2)⁻¹) ≤ (L:ℝ)⁻¹ := by
    apply (sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)).trans
    have := sum_Ioc_inv_sq_le_sub (α:=ℝ) hL.ne' (le_max_left L (S.sup id))
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) U)]
  calc _ ≤ (∑ p∈S, ((b/(p*p):ℕ):ℝ))+1 := by exact_mod_cast hnum
       _ ≤ (∑ p∈S, (b:ℝ)*((p:ℝ)^2)⁻¹)+1 := by
           gcongr with p hp
           simpa only [Nat.cast_mul,pow_two,div_eq_mul_inv] using (Nat.cast_div_le (m:=b) (n:=p*p) (α:=ℝ))
       _ ≤ _ := by rw [←mul_sum,div_eq_mul_inv]; linarith [mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg (α:=ℝ) b)]
end Sep470
end

section
open Filter Finset
open scoped Classical Topology
namespace Sep470
theorem boundary : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1.H2 := by
  classical
  intro ε hε
  obtain ⟨L,hLε,hL2⟩ := (((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (4/ε)).and (eventually_ge_atTop 2)).exists
  have hL : 0<L := by omega
  obtain ⟨S,hS,ha⟩ := choose_primes L (show 0<ε/8 by positivity)
  obtain ⟨δ,hδ,hsep⟩ := separation S (fun p hp => ⟨(hS p hp).1,by have := (hS p hp).2; omega⟩)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_ge_atTop (S.sup id)] with K hK
  let D := K.factorial
  have hD : 0<D := Nat.factorial_pos _
  have hset : S⊆D.primeFactors := by
    intro p hp
    have hpr := (hS p hp).1
    exact Nat.mem_primeFactors.2 ⟨hpr,Nat.dvd_factorial hpr.pos ((le_sup (f:=id) hp).trans hK),hD.ne'⟩
  obtain ⟨Q,R,hQ,hR,he,hc,hRS⟩ := split_prime_parts D hD S hset
  let good (n : ℕ) := clean S (D.gcd n) ∧ |idx (D.gcd n)-2|≤δ
  have hgc : ((range D).filter good).card ≤ Q*R.totient := by
    dsimp only [good]
    rw [he]
    exact good_count hQ hR hc S hRS δ hsep
  have hperiod : Function.Periodic good D := by intro n; simp only [good,Nat.gcd_add_self_right]
  filter_upwards [eventually_ge_atTop D,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (4/ε)] with b hDb hbε
  have hb : 0<(b:ℝ) := Nat.cast_pos.2 (hD.trans_le hDb)
  let G := (range b).filter good
  let B := (range b).filter (fun n => ∃ p∈S,p*p∣n)
  let A := {n : ℕ | |idx (n.gcd D)-2|≤δ}
  have haSub : A ∩ Set.Iio b ⊆ (↑(G∪B) : Set ℕ) := by
    rintro n ⟨hn,hnb⟩
    change |idx (n.gcd D)-2|≤δ at hn
    rw [Nat.gcd_comm] at hn
    apply mem_union.2
    by_cases h : clean S (D.gcd n)
    · exact Or.inl (mem_filter.2 ⟨mem_range.2 hnb,⟨h,hn⟩⟩)
    · change ¬∀p∈S,¬p*p∣D.gcd n at h
      push Not at h
      obtain ⟨p,hp,hdiv⟩ := h
      exact Or.inr (mem_filter.2 ⟨mem_range.2 hnb,p,hp,hdiv.trans (Nat.gcd_dvd_right ..)⟩)
  have hcard : ((A ∩ Set.Iio b).ncard:ℝ) ≤ G.card+B.card := by
    have hh := Set.ncard_le_ncard haSub (G∪B).finite_toSet
    rw [Set.ncard_coe_finset] at hh
    exact_mod_cast hh.trans (card_union_le ..)
  have hg : (G.card:ℝ) ≤ 2*b*avoid S := by
    have hgc' : (((range D).filter good).card:ℝ) ≤ (Q:ℝ)*R.totient := by exact_mod_cast hgc
    calc _ ≤ _ := periodic_upper good hD hDb hperiod
         _ ≤ 2*b/D*((Q:ℝ)*R.totient) := mul_le_mul_of_nonneg_left hgc' (by positivity)
         _ = 2*b*avoid S := by
           rw [he,Nat.cast_mul,totient_ratio hR,hRS]
           field_simp [Nat.ne_of_gt hR,Nat.ne_of_gt hQ]
  have hbad : (B.card:ℝ) ≤ 1+(b:ℝ)/L := square_bad S hL (fun p hp => (hS p hp).2) _
  have hsmallL : (b:ℝ)/L < b*ε/4 := by
    have heL := (div_lt_iff₀ hε).1 hLε
    apply (div_lt_iff₀ (Nat.cast_pos.2 hL : 0<(L:ℝ))).2
    nlinarith only [mul_lt_mul_of_pos_right heL hb]
  have hsmallb := (div_lt_iff₀ hε).1 hbε
  have hmass := mul_lt_mul_of_pos_left ha (by positivity : 0<2*(b:ℝ))
  change A.partialDensity Set.univ b < ε
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Set.ncard_Iio_nat]
  apply (div_lt_iff₀ hb).2
  linarith
end Sep470
end

theorem Sep470.band : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1.H2 := Sep470.boundary
end
theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H1 := OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1.main Tail470.tail Sep470.band
