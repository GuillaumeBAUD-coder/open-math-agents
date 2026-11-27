import OMAReductions.R_Erdos470_erdos_470_variants_weird_pos_density_R1
import Mathlib.Data.Nat.Periodic

-- Credit: @marcusbuffett
-- Periodic counting follows the checked proof of Erdos697.density_exists.
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
