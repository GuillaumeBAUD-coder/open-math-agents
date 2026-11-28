import OMAReductions.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Prime-endpoint rise in Erdős 692

The reduction follows Claim 4 and Theorem 3 of Stijn Cambie's paper
Resolution of Erdős' problems about unimodularity, https://arxiv.org/abs/2501.10333.
The finite Chinese-remainder count gives the exact change in density and isolates the
remaining density comparison and the supply of separated prime windows.

Credit: @justusklocke-cloud
-/

open Filter
open scoped Topology

namespace Erdos692PrimeInsertion

/-- On inserting `p`, one keeps the old qualifying nonmultiples and adds the
multiples which had no qualifying divisor before insertion. -/
theorem insertion_decomposition {n p : ℕ} (hn : n < p) :
    Erdos692.exactlyOneDivisorIn n (p + 1) =
      {x | x ∈ Erdos692.exactlyOneDivisorIn n p ∧ ¬ p ∣ x} ∪
      {x | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0 ∧ p ∣ x} := by
  ext x
  let D := {d ∈ Set.Ioo n p | d ∣ x}
  let E := {d ∈ Set.Ioo n (p + 1) | d ∣ x}
  change E.ncard = 1 ↔ (D.ncard = 1 ∧ ¬ p ∣ x) ∨ (D.ncard = 0 ∧ p ∣ x)
  by_cases hpx : p ∣ x
  · have hE : E = insert p D := by
      ext d
      change (d ∈ Set.Ioo n (p + 1) ∧ d ∣ x) ↔ d ∈ insert p D
      rw [Set.mem_insert_iff]
      constructor
      · rintro ⟨⟨hdn, hdp⟩, hd⟩
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ hdp) with he | hl
        · exact Or.inl he
        · exact Or.inr ⟨⟨hdn, hl⟩, hd⟩
      · rintro (rfl | ⟨⟨hdn, hdp⟩, hd⟩)
        · exact ⟨⟨hn, Nat.lt_succ_self _⟩, hpx⟩
        · exact ⟨⟨hdn, hdp.trans (Nat.lt_succ_self _)⟩, hd⟩
    have hpD : p ∉ D := fun hd => (lt_irrefl p) hd.1.2
    have hD : D.Finite := (Set.finite_Ioo n p).subset fun _ hd => hd.1
    rw [hE, Set.ncard_insert_of_notMem hpD hD]
    simp [hpx]
  · have hE : E = D := by
      ext d
      change (d ∈ Set.Ioo n (p + 1) ∧ d ∣ x) ↔ (d ∈ Set.Ioo n p ∧ d ∣ x)
      constructor
      · rintro ⟨⟨hdn, hdp⟩, hd⟩
        refine ⟨⟨hdn, lt_of_le_of_ne (Nat.le_of_lt_succ hdp) ?_⟩, hd⟩
        rintro rfl
        exact hpx hd
      · rintro ⟨⟨hdn, hdp⟩, hd⟩
        exact ⟨⟨hdn, hdp.trans (Nat.lt_succ_self _)⟩, hd⟩
    simp [hE, hpx]

private theorem ncard_inter_Iio_eq_card_filter (S : Set ℕ) (T : ℕ) [DecidablePred (· ∈ S)] :
    (S ∩ Set.Iio T).ncard = ((Finset.range T).filter (· ∈ S)).card := by
  rw [show S ∩ Set.Iio T = (↑((Finset.range T).filter (· ∈ S)) : Set ℕ) by
    ext x
    simp [and_comm], Set.ncard_coe_finset]

/-- Over one common period, every prescribed residue modulo a modulus coprime
to the period selects one copy of the qualifying residues. -/
theorem crt_count {p T : ℕ} (hp : 0 < p) (hT : 0 < T) (hcop : p.Coprime T)
    (S : Set ℕ) (hper : Function.Periodic (fun x => x ∈ S) T)
    (R : Finset ℕ) (hR : R ⊆ Finset.range p) :
    ({x | x ∈ S ∧ x % p ∈ R} ∩ Set.Iio (p * T)).ncard =
      R.card * (S ∩ Set.Iio T).ncard := by
  classical
  rw [ncard_inter_Iio_eq_card_filter, ncard_inter_Iio_eq_card_filter, ← Finset.card_product]
  apply Finset.card_nbij (fun x => (x % p, x % T))
  · intro x hx
    obtain ⟨_, hxS, hxR⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_product.mpr ⟨hxR, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hT), ?_⟩⟩
    simpa only [hper.map_mod_nat x] using hxS
  · intro x hx y hy hxy
    have hxp : x ≡ y [MOD p] := congrArg Prod.fst hxy
    have hxT : x ≡ y [MOD T] := congrArg Prod.snd hxy
    have hmods : x ≡ y [MOD p * T] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hxp, hxT⟩
    exact hmods.eq_of_lt_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hy).1)
  · rintro ⟨a, b⟩ hmem
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hmem
    obtain ⟨hbT, hbS⟩ := Finset.mem_filter.mp hb
    let x := Nat.chineseRemainder hcop a b
    have hxp : x.val % p = a := by
      have he : x.val % p = a % p := x.prop.1
      rw [he, Nat.mod_eq_of_lt (show a < p from Finset.mem_range.mp (hR ha))]
    have hxT : x.val % T = b := by
      have he : x.val % T = b % T := x.prop.2
      rw [he, Nat.mod_eq_of_lt (show b < T from Finset.mem_range.mp hbT)]
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.chineseRemainder_lt_mul hcop _ _ hp.ne' hT.ne'), ?_⟩, Prod.ext hxp hxT⟩
    refine ⟨?_, hxp.symm ▸ ha⟩
    rw [← hper.map_mod_nat x.val, hxT]
    exact hbS

private theorem periodic_divisor_count {n m T r : ℕ} (hT : ∀ d ∈ Set.Ioo n m, d ∣ T) :
    Function.Periodic (fun x : ℕ => {d ∈ Set.Ioo n m | d ∣ x}.ncard = r) T := by
  intro x
  have heq : {d ∈ Set.Ioo n m | d ∣ x + T} = {d ∈ Set.Ioo n m | d ∣ x} := by
    ext d
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hd => ?_
    exact (Nat.dvd_add_iff_left (hT d hd)).symm
  change ({d ∈ Set.Ioo n m | d ∣ x + T}.ncard = r) = ({d ∈ Set.Ioo n m | d ∣ x}.ncard = r)
  rw [heq]

private theorem density_eq_period_count {S : Set ℕ} {T : ℕ} {δ : ℝ}
    (hT : 0 < T) (hper : Function.Periodic (fun x => x ∈ S) T) (hδ : S.HasDensity δ) :
    δ = ((S ∩ Set.Iio T).ncard : ℝ) / T := by
  classical
  let P (x : ℕ) := x ∈ S
  have hshift (k : ℕ) : Nat.count (fun x => P (x + T)) k = Nat.count P k := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext x
    simp only [Finset.mem_filter, P, hper x]
  have hcount (k : ℕ) : Nat.count P (k * T) = k * Nat.count P T := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, Nat.count_add', hshift, ih, Nat.succ_mul]
  have hncard (k : ℕ) : (S ∩ Set.Iio k).ncard = Nat.count P k := by
    rw [ncard_inter_Iio_eq_card_filter, Nat.count_eq_card_filter_range]
  have hlim : Tendsto (fun k : ℕ => (Nat.count P k : ℝ) / (k : ℝ)) atTop (𝓝 δ) := by
    simpa only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter, hncard,
      Set.ncard_Iio_nat] using hδ
  have hmul : Tendsto (fun k : ℕ => k * T) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (eventually_ge_atTop b).mono fun k hk => hk.trans (Nat.le_mul_of_pos_right k hT)
  have hconstant : (fun k : ℕ => (Nat.count P (k * T) : ℝ) / ((k * T : ℕ) : ℝ)) =ᶠ[atTop]
      (fun _ : ℕ => (Nat.count P T : ℝ) / T) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    simp only [hcount, Nat.cast_mul]
    exact mul_div_mul_left _ _ (by exact_mod_cast hk.ne')
  rw [hncard]
  exact tendsto_nhds_unique (hlim.comp hmul) (tendsto_const_nhds.congr' hconstant.symm)

private theorem old_dvd_factorial {n p d : ℕ} (hd : d ∈ Set.Ioo n p) : d ∣ (p - 1).factorial :=
  Nat.dvd_factorial ((Nat.zero_le n).trans_lt hd.1) (by have := hd.2; omega)

/-- The new one-divisor count over `p * (p-1)!` is the sum of the two CRT counts. -/
theorem insertion_period_count {n p : ℕ} (hn : n < p) (hp : p.Prime) :
    let T := (p - 1).factorial
    (Erdos692.exactlyOneDivisorIn n (p + 1) ∩ Set.Iio (p * T)).ncard =
      (p - 1) * (Erdos692.exactlyOneDivisorIn n p ∩ Set.Iio T).ncard +
        ({x | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0} ∩ Set.Iio T).ncard := by
  let T := (p - 1).factorial
  let S₁ := Erdos692.exactlyOneDivisorIn n p
  let S₀ : Set ℕ := {x | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0}
  let X : Set ℕ := {x | x ∈ S₁ ∧ ¬ p ∣ x} ∩ Set.Iio (p * T)
  let Y : Set ℕ := {x | x ∈ S₀ ∧ p ∣ x} ∩ Set.Iio (p * T)
  have hT : 0 < T := Nat.factorial_pos _
  have hpT : p.Coprime T := hp.coprime_factorial_of_lt (by have := hp.pos; omega)
  have hper₁ : Function.Periodic (fun x => x ∈ S₁) T := periodic_divisor_count fun _ => old_dvd_factorial
  have hper₀ : Function.Periodic (fun x => x ∈ S₀) T := periodic_divisor_count fun _ => old_dvd_factorial
  have hX : X.ncard = (p - 1) * (S₁ ∩ Set.Iio T).ncard := by
    have heq : X = {x | x ∈ S₁ ∧ x % p ∈ (Finset.range p).erase 0} ∩ Set.Iio (p * T) := by
      ext x
      simp [X, Nat.dvd_iff_mod_eq_zero, Nat.mod_lt _ hp.pos]
    rw [heq, crt_count hp.pos hT hpT S₁ hper₁ _ (Finset.erase_subset _ _),
      Finset.card_erase_of_mem (Finset.mem_range.mpr hp.pos), Finset.card_range]
  have hY : Y.ncard = (S₀ ∩ Set.Iio T).ncard := by
    have heq : Y = {x | x ∈ S₀ ∧ x % p ∈ ({0} : Finset ℕ)} ∩ Set.Iio (p * T) := by
      ext x
      simp [Y, Nat.dvd_iff_mod_eq_zero]
    have hsub : ({0} : Finset ℕ) ⊆ Finset.range p :=
      Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hp.pos)
    rw [heq, crt_count hp.pos hT hpT S₀ hper₀ _ hsub, Finset.card_singleton, one_mul]
  have hset : Erdos692.exactlyOneDivisorIn n (p + 1) ∩ Set.Iio (p * T) = X ∪ Y := by
    ext x
    simp only [insertion_decomposition hn, X, Y, S₁, S₀, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hdisj : Disjoint X Y := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.1.2 hy.1.2
  have hXfin : X.Finite := (Set.finite_Iio _).subset Set.inter_subset_right
  have hYfin : Y.Finite := (Set.finite_Iio _).subset Set.inter_subset_right
  change (Erdos692.exactlyOneDivisorIn n (p + 1) ∩ Set.Iio (p * T)).ncard =
    (p - 1) * (S₁ ∩ Set.Iio T).ncard + (S₀ ∩ Set.Iio T).ncard
  rw [hset, Set.ncard_union_eq hdisj hXfin hYfin, hX, hY]

/-- Inserting a new prime endpoint mixes the old one- and zero-divisor densities. -/
theorem insertion_density {n p : ℕ} (hn : n < p) (hp : p.Prime) {δ₁ δ₀ δnew : ℝ}
    (h₁ : Erdos692.IsDelta₁ n p δ₁)
    (h₀ : {x | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0}.HasDensity δ₀)
    (hnew : Erdos692.IsDelta₁ n (p + 1) δnew) :
    δnew = (1 - 1 / (p : ℝ)) * δ₁ + (1 / (p : ℝ)) * δ₀ := by
  let T := (p - 1).factorial
  have hT : 0 < T := Nat.factorial_pos _
  have hbig (d : ℕ) (hd : d ∈ Set.Ioo n (p + 1)) : d ∣ p * T := by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hd.2) with he | hlt
    · rw [he]
      exact dvd_mul_right p T
    · exact (old_dvd_factorial (show d ∈ Set.Ioo n p from ⟨hd.1, hlt⟩)).trans (dvd_mul_left T p)
  have hper₁ : Function.Periodic (fun x => x ∈ Erdos692.exactlyOneDivisorIn n p) T :=
    periodic_divisor_count fun _ => old_dvd_factorial
  have hper₀ : Function.Periodic (fun x : ℕ => {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0) T :=
    periodic_divisor_count fun _ => old_dvd_factorial
  have hperNew : Function.Periodic (fun x => x ∈ Erdos692.exactlyOneDivisorIn n (p + 1)) (p * T) :=
    periodic_divisor_count hbig
  rw [density_eq_period_count (Nat.mul_pos hp.pos hT) hperNew hnew,
    density_eq_period_count hT hper₁ h₁, density_eq_period_count hT hper₀ h₀, insertion_period_count hn hp]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt hp.pos), Nat.cast_one]
  let c₁ : ℝ := (Erdos692.exactlyOneDivisorIn n p ∩ Set.Iio T).ncard
  let c₀ : ℝ := ({x | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0} ∩ Set.Iio T).ncard
  change (((p : ℝ) - 1) * c₁ + c₀) / ((p : ℝ) * T) =
    (1 - 1 / (p : ℝ)) * (c₁ / T) + (1 / (p : ℝ)) * (c₀ / T)
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp [hp', hT']

/-- If the zero-divisor density is larger, inserting the prime strictly increases the one-divisor density. -/
theorem strict_rise {n p : ℕ} (hn : n < p) (hp : p.Prime) {δ₁ δ₀ δnew : ℝ}
    (h₁ : Erdos692.IsDelta₁ n p δ₁)
    (h₀ : {x | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0}.HasDensity δ₀)
    (hnew : Erdos692.IsDelta₁ n (p + 1) δnew) (hgap : δ₁ < δ₀) : δ₁ < δnew := by
  rw [insertion_density hn hp h₁ h₀ hnew]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpos : 0 < (1 / (p : ℝ)) * (δ₀ - δ₁) := mul_pos (one_div_pos.mpr hp') (sub_pos.mpr hgap)
  nlinarith only [hpos]

end Erdos692PrimeInsertion

namespace OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1_H1_R1

open Filter
open Erdos692 (IsDelta₁)

/-- Cambie's comparison of zero-divisor and one-divisor densities. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, n < p → p.Prime →
      Real.exp (3 * (n : ℝ) ^ c) < (p : ℝ) →
      (p : ℝ) < 2 * Real.exp (3 * (n : ℝ) ^ c) →
        ∃ z : ℝ, {x | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0}.HasDensity z ∧ δ n p < z

/-- The prime-gap input supplies the separated windows in the required dyadic interval. -/
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
    ∃ p q : Fin (n ^ k) → ℕ,
      (∀ i, (p i).Prime ∧ (q i).Prime ∧ n + 1 ≤ p i ∧ n < q i ∧
        Real.exp (3 * (n : ℝ) ^ c) < (p i : ℝ) ∧
        (2 * q i : ℝ) < 2 * Real.exp (3 * (n : ℝ) ^ c) ∧ p i < 2 * q i) ∧
      (∀ i j, i < j → 2 * q i ≤ p j)

theorem main : H1 → H2 → OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1.H1 := by
  intro hcomp hwin k δ hδ
  obtain ⟨c, hc, hcompare⟩ := hcomp
  filter_upwards [hcompare δ hδ, hwin c hc k] with n hcompare hwin
  obtain ⟨p, q, hpq, hsep⟩ := hwin
  refine ⟨p, q, ?_, hsep⟩
  intro i
  obtain ⟨hp, hq, hn, hqgt, hfirst, hlast, hpair⟩ := hpq i
  have hnp : n < p i := hn
  have hpband : (p i : ℝ) < 2 * Real.exp (3 * (n : ℝ) ^ c) := by
    have hcast : (p i : ℝ) < 2 * (q i : ℝ) := by exact_mod_cast hpair
    exact hcast.trans hlast
  obtain ⟨z, hz, hgap⟩ := hcompare (p i) hnp hp hfirst hpband
  exact ⟨hn, hqgt, hq, hpair, Erdos692PrimeInsertion.strict_rise hnp hp
    (hδ n (p i)) hz (hδ n (p i + 1)) hgap⟩

end OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1_H1_R1
