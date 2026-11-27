import FormalConjectures.ErdosProblems.«955»
import Mathlib.Data.Nat.Periodic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! A sieve by finitely many independent residue conditions for aliquot sums. -/

open Filter Finset ArithmeticFunction
open scoped Topology BigOperators ArithmeticFunction.sigma

namespace OMA.Pollack

-- Periodic counting adapted from the accepted Erdős 697 density proof.
lemma periodic_hasDensity {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) :
    {n : ℕ | p n}.HasDensity (Nat.count p d / (d : ℝ)) := by
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
  simpa [Set.HasDensity, Set.partialDensity, hncard, density, count] using ht.add_const density

noncomputable def residues (m : ℕ) (P : ZMod m → Prop) : ℕ :=
  Nat.card {x : ZMod m // P x}

lemma density_of_residues {m : ℕ} (hm : 0 < m) (P : ZMod m → Prop) :
    {n : ℕ | P (n : ZMod m)}.HasDensity (residues m P / (m : ℝ)) := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have hper : Function.Periodic (fun n : ℕ => P (n : ZMod m)) m := by
    intro n
    change P ((↑(n + m) : ZMod m)) = P (n : ZMod m)
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  have hc : Nat.count (fun n : ℕ => P (n : ZMod m)) m = residues m P := by
    rw [Nat.count_eq_card_filter_range, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨(x.val : ZMod m), (Finset.mem_filter.mp x.property).2⟩
        invFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (ZMod.val_lt x.val), by simpa only [ZMod.natCast_zmod_val] using x.property⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp x.property).1)
    · intro x
      apply Subtype.ext
      exact ZMod.natCast_zmod_val x.val
  simpa only [hc] using periodic_hasDensity hm hper

lemma residue_system (S : Finset ℕ) (d : ℕ → ℕ) (hd : ∀ i ∈ S, 0 < d i)
    (hcop : (S : Set ℕ).Pairwise fun i j => (d i).Coprime (d j))
    (P : (i : ℕ) → ZMod (d i) → Prop) :
    ∃ R : ZMod (∏ i ∈ S, d i) → Prop,
      (∀ n : ℕ, R (n : ZMod (∏ i ∈ S, d i)) ↔ ∀ i ∈ S, P i (n : ZMod (d i))) ∧
      residues _ R = ∏ i ∈ S, residues (d i) (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => True, by simp, ?_⟩
    simp [residues]
  | @insert i S hi ih =>
    have hdi := hd i (Finset.mem_insert_self _ _)
    have hds : ∀ j ∈ S, 0 < d j := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hcs : (S : Set ℕ).Pairwise (fun i j => (d i).Coprime (d j)) :=
      hcop.mono fun _ hj => Finset.mem_insert_of_mem hj
    obtain ⟨RS, hRS, hcRS⟩ := ih hds hcs
    rw [Finset.prod_insert hi]
    have hci : (d i).Coprime (∏ j ∈ S, d j) := Nat.Coprime.prod_right fun j hj =>
      hcop (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (fun h => hi (h.symm ▸ hj))
    let e := ZMod.chineseRemainder hci
    refine ⟨fun x => P i (e x).1 ∧ RS (e x).2, ?_, ?_⟩
    · intro n
      change (P i (e (↑n)).1 ∧ RS (e (↑n)).2) ↔ _
      simp only [map_natCast, Prod.fst_natCast, Prod.snd_natCast, hRS, Finset.forall_mem_insert]
    · rw [Finset.prod_insert hi, ← hcRS]
      unfold residues
      rw [← Nat.card_prod]
      apply Nat.card_congr
      exact
        { toFun := fun x => (⟨(e x.val).1, x.property.1⟩, ⟨(e x.val).2, x.property.2⟩)
          invFun := fun x => ⟨e.symm (x.1.val, x.2.val), by simpa only [e.apply_symm_apply]
            using ⟨x.1.property, x.2.property⟩⟩
          left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
          right_inv := fun x => Prod.ext
            (Subtype.ext (congrArg Prod.fst (e.apply_symm_apply _)))
            (Subtype.ext (congrArg Prod.snd (e.apply_symm_apply _))) }

lemma density_system (S : Finset ℕ) (d : ℕ → ℕ) (hd : ∀ i ∈ S, 0 < d i)
    (hcop : (S : Set ℕ).Pairwise fun i j => (d i).Coprime (d j))
    (P : (i : ℕ) → ZMod (d i) → Prop) :
    {n : ℕ | ∀ i ∈ S, P i (n : ZMod (d i))}.HasDensity
      (∏ i ∈ S, residues (d i) (P i) / (d i : ℝ)) := by
  obtain ⟨R, he, hR⟩ := residue_system S d hd hcop P
  have hpos : 0 < ∏ i ∈ S, d i := Finset.prod_pos hd
  have h := density_of_residues hpos R
  rw [show {n : ℕ | R (n : ZMod (∏ i ∈ S, d i))} =
      {n : ℕ | ∀ i ∈ S, P i (n : ZMod (d i))} by ext n; exact he n,
    hR, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib] at h
  exact h

open ArithmeticFunction in
lemma not_summable_primes_class {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ (p : ZMod q) = a then (1 : ℝ) / p else 0) := by
  classical
  intro hsum
  let c := vonMangoldt.residueClass a
  let g (t : ℝ) (n : ℕ) := (t - 1) * (c n / (n : ℝ) ^ t)
  let bound (n : ℕ) :=
    (if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / n else 0) +
      (if n.Prime then 0 else c n) / n
  have hb : Summable bound := hsum.add (vonMangoldt.summable_residueClass_non_primes_div a)
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), t ∈ Set.Ioc (1 : ℝ) 2 := by
    have h₁ : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), 1 < t := self_mem_nhdsWithin
    have h₂ : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), t < 2 := Iio_mem_nhds (by norm_num)
    exact (h₁.and (h₂.filter_mono nhdsWithin_le_nhds)).mono fun _ h => ⟨h.1, h.2.le⟩
  have ht : Tendsto (fun t : ℝ => ∑' n, g t n) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have H : Tendsto (fun t : ℝ => ∑' n, g t n) (𝓝[>] (1 : ℝ))
        (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence hb (fun n => ?_) (hnear.mono fun t ht n => ?_)
      · have hc : ContinuousAt (fun t : ℝ => g t n) 1 := by
          by_cases hn : n = 0
          · simpa [g, c, hn] using
              (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) (1 : ℝ))
          · exact (continuousAt_id.sub continuousAt_const).mul
              (continuousAt_const.div
                (Real.continuousAt_const_rpow (by exact_mod_cast hn))
                (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _).ne')
        have he : g 1 n = 0 := by simp [g]
        rw [← he]
        exact hc.continuousWithinAt
      · have h0 : 0 ≤ g t n := mul_nonneg (sub_nonneg.mpr ht.1.le)
          (div_nonneg (vonMangoldt.residueClass_nonneg a n)
            (Real.rpow_nonneg (Nat.cast_nonneg n) t))
        rw [Real.norm_of_nonneg h0]
        by_cases hn0 : n = 0
        · simp [g, c, bound, hn0]
        have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        by_cases hp : n.Prime
        · by_cases hclass : (n : ZMod q) = a
          · have hc : c n = Real.log n := by
              simp [c, vonMangoldt.residueClass, hclass, vonMangoldt_apply_prime hp]
            simp only [g, hc, bound, hp, hclass, and_self, if_true, zero_div, add_zero]
            rw [← mul_div_assoc]
            have hden : (n : ℝ) ^ t = (n : ℝ) ^ (t - 1) * n := by
              calc
                _ = (n : ℝ) ^ ((t - 1) + 1) := by ring_nf
                _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]
            rw [hden, div_mul_eq_div_div]
            apply div_le_div_of_nonneg_right _ hn.le
            apply (div_le_one (Real.rpow_pos_of_pos hn _)).mpr
            rw [Real.rpow_def_of_pos hn, mul_comm (Real.log n)]
            exact (le_add_of_nonneg_right (by norm_num : 0 ≤ (1 : ℝ))).trans
              (Real.add_one_le_exp _)
          · simp [g, bound, c, vonMangoldt.residueClass, hp, hclass]
        · simp only [bound, hp, false_and, if_false, zero_add]
          have hden : (n : ℝ) ≤ (n : ℝ) ^ t := calc
            (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 ht.1.le
          exact (mul_le_of_le_one_left
            (div_nonneg (vonMangoldt.residueClass_nonneg a n) (Real.rpow_nonneg hn.le _))
            (by linarith [ht.2])).trans
            (div_le_div_of_nonneg_left (vonMangoldt.residueClass_nonneg a n) hn hden)
    simpa only [tsum_zero] using H
  obtain ⟨C, hC⟩ := vonMangoldt.LSeries_residueClass_lower_bound ha
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      (q.totient : ℝ)⁻¹ - C * (t - 1) ≤ ∑' n, g t n := by
    filter_upwards [hnear] with t ht
    simp only [g, tsum_mul_left]
    have hc := mul_le_mul_of_nonneg_left (hC ht) (sub_nonneg.mpr ht.1.le)
    have he : (t - 1) * ((q.totient : ℝ)⁻¹ / (t - 1)) = (q.totient : ℝ)⁻¹ := by
      field_simp [sub_ne_zero.mpr ht.1.ne']
    rw [mul_sub, he] at hc
    simpa only [mul_comm C] using hc
  have hlim : Tendsto (fun t : ℝ => (q.totient : ℝ)⁻¹ - C * (t - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
    have hcont : ContinuousAt (fun t : ℝ => (q.totient : ℝ)⁻¹ - C * (t - 1)) 1 :=
      continuousAt_const.sub (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
    have hh : Tendsto (fun t : ℝ => (q.totient : ℝ)⁻¹ - C * (t - 1))
        (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹ - C * (1 - 1))) :=
      hcont.continuousWithinAt
    simpa only [sub_self, mul_zero, sub_zero] using hh
  have hnonpos := le_of_tendsto_of_tendsto hlim ht hbound
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  exact (inv_pos.mpr hpos).not_ge hnonpos

lemma small_product {P : ℕ → Prop} [DecidablePred P] {w : ℕ → ℝ}
    (hw : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    (hs : ¬ Summable (fun p => if P p then w p else 0)) {ε : ℝ} (he : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, P p) ∧ (∏ p ∈ S, (1 - w p)) < ε := by
  have hd := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => by split_ifs <;> simp [hw])).mp hs
  obtain ⟨N, hN⟩ := (eventually_atTop.mp ((tendsto_atTop.mp hd) (1 - Real.log ε)))
  let S := (Finset.range N).filter P
  have hsum : 1 - Real.log ε ≤ ∑ p ∈ S, w p := by
    simpa only [S, Finset.sum_filter] using hN N le_rfl
  refine ⟨S, fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  calc
    _ ≤ ∏ p ∈ S, Real.exp (-w p) :=
      Finset.prod_le_prod (fun p _ => sub_nonneg.mpr (hw1 p)) fun p _ => by
        simpa only [neg_add_eq_sub] using Real.add_one_le_exp (-w p)
    _ = Real.exp (-∑ p ∈ S, w p) := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ < ε := by
      rw [← Real.exp_log he, Real.exp_lt_exp]
      linarith

lemma residues_ne_zero (p : ℕ) (hp : p.Prime) :
    residues p (fun x => x ≠ 0) / (p : ℝ) = 1 - 1 / p := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  simp only [residues, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ZMod.card]
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one, sub_div, div_self hpos.ne']

noncomputable def hit (p : ℕ) : Finset (ZMod (p ^ 2)) := by
  classical
  exact (Finset.Ico 1 p).image fun k => ((p * k : ℕ) : ZMod (p ^ 2))

lemma mem_hit {p n : ℕ} (hp : p.Prime) :
    (n : ZMod (p ^ 2)) ∈ hit p ↔ p ∣ n ∧ ¬ p ^ 2 ∣ n := by
  classical
  have hpos : 0 < p ^ 2 := pow_pos hp.pos _
  have hdiv : p ∣ p ^ 2 := dvd_pow_self p (by decide)
  change _ ∈ Finset.image (fun k : ℕ => ((p * k : ℕ) : ZMod (p ^ 2))) (.Ico 1 p) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, he⟩
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Ico.mp hk
    have hlt : p * k < p ^ 2 := by rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left hk₂ hp.pos
    have hr : n % p ^ 2 = p * k :=
      ((ZMod.natCast_eq_natCast_iff' _ _ _).mp he.symm).trans (Nat.mod_eq_of_lt hlt)
    refine ⟨(Nat.dvd_mod_iff hdiv).mp ⟨k, hr⟩, ?_⟩
    intro h
    rw [Nat.mod_eq_zero_of_dvd h] at hr
    exact (Nat.mul_pos hp.pos (by omega : 0 < k)).ne' hr.symm
  · rintro ⟨hd, hn⟩
    obtain ⟨k, hk⟩ := (Nat.dvd_mod_iff hdiv).mpr hd
    have hlt := Nat.mod_lt n hpos
    rw [hk, pow_two] at hlt
    have hk₂ := lt_of_mul_lt_mul_left' hlt
    have hk₁ : 1 ≤ k := by
      by_contra! H
      have : k = 0 := by omega
      exact hn (Nat.dvd_of_mod_eq_zero (by simpa [this] using hk))
    refine ⟨k, Finset.mem_Ico.mpr ⟨hk₁, hk₂⟩, ?_⟩
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      ((Nat.mod_eq_of_lt (hk ▸ Nat.mod_lt n hpos)).trans hk.symm)

lemma residues_avoids_hit (p : ℕ) (hp : p.Prime) :
    residues (p ^ 2) (fun x => x ∉ hit p) / ((p ^ 2 : ℕ) : ℝ) =
      1 - (p - 1 : ℕ) / (p : ℝ) ^ 2 := by
  classical
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hc : (hit p).card = p - 1 := by
    change ((Finset.Ico 1 p).image (fun k => ((p * k : ℕ) : ZMod (p ^ 2)))).card = _
    rw [Finset.card_image_of_injOn, Nat.card_Ico]
    intro i hi j hj he
    have hlt (k : ℕ) (hk : k ∈ Finset.Ico 1 p) : p * k < p ^ 2 := by
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_left (Finset.mem_Ico.mp hk).2 hp.pos
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (hlt i hi), ZMod.val_natCast_of_lt (hlt j hj)] at hv
    exact Nat.eq_of_mul_eq_mul_left hp.pos hv
  simp only [residues, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe,
    ZMod.card, hc]
  have hlt : p - 1 ≤ p ^ 2 := (Nat.sub_le _ _).trans (by rw [pow_two]; exact Nat.le_mul_self _)
  have hpos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity [hp.pos]
  rw [Nat.cast_sub hlt, Nat.cast_pow, sub_div, div_self hpos.ne']

lemma divisor_of_aliquot {n p q : ℕ} (hp : p.Prime) (hclass : (p : ZMod q) = -1)
    (hq : q ∣ n) (hd : p ∣ n) (hn : ¬ p ^ 2 ∣ n) : q ∣ Erdos955.s n := by
  obtain ⟨k, rfl⟩ := hd
  have hpk : p.Coprime k := hp.coprime_iff_not_dvd.mpr (fun ⟨j, hj⟩ =>
    hn ⟨j, by rw [hj, pow_two, mul_assoc]⟩)
  have hpr : σ 1 p = 1 + p := by
    have h := sigma_one_apply_prime_pow (i := 1) hp
    simpa [Finset.sum_range_succ] using h
  have hq' : q ∣ 1 + p := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp [hclass]
  unfold Erdos955.s
  rw [isMultiplicative_sigma.map_mul_of_coprime hpk, hpr]
  exact Nat.dvd_sub (dvd_mul_of_dvd_left hq' _) hq

lemma lt_aliquot_of_sq_lt {n q : ℕ} (hq : q.Prime) (hd : q ∣ n) (hn : q ^ 2 < n) :
    q < Erdos955.s n := by
  obtain ⟨k, rfl⟩ := hd
  have hk : q < k := by rw [pow_two] at hn; exact lt_of_mul_lt_mul_left' hn
  have hneq : q * k ≠ 0 := Nat.mul_ne_zero hq.ne_zero (by omega)
  have hlt : k < q * k := by nlinarith [hq.two_le, hk]
  classical
  have hsub : ({q * k, k} : Finset ℕ) ⊆ Nat.divisors (q * k) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨dvd_refl _, hneq⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, hneq⟩
  have hs := Finset.sum_le_sum_of_subset hsub (f := id)
  have hm : q * k ∉ ({k} : Finset ℕ) := by simp [hlt.ne']
  simp only [Finset.sum_insert hm, Finset.sum_singleton, id_eq] at hs
  unfold Erdos955.s
  rw [ArithmeticFunction.sigma_one_apply]
  exact lt_of_lt_of_le hk (Nat.le_sub_of_add_le (by omega))

lemma density_small_sieve {q : ℕ} (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ZMod q) = -1) ∧
      ∃ ρ : ℝ, ρ < ε ∧ {n : ℕ | ∀ p ∈ S, (n : ZMod (p ^ 2)) ∉ hit p}.HasDensity ρ := by
  classical
  have : NeZero q := ⟨hq.ne_zero⟩
  let w (p : ℕ) := (p - 1 : ℕ) / (p : ℝ) ^ 2
  have hw₀ (p : ℕ) : 0 ≤ w p := by dsimp [w]; positivity
  have hw₁ (p : ℕ) : w p ≤ 1 := by
    apply div_le_one_of_le₀ _ (sq_nonneg _)
    exact_mod_cast ((Nat.sub_le p 1).trans (by rw [pow_two]; exact Nat.le_mul_self _))
  let P (p : ℕ) := p.Prime ∧ (p : ZMod q) = -1
  have hsum : ¬ Summable (fun p : ℕ => if P p then w p else 0) := by
    intro h
    apply not_summable_primes_class (-1 : ZMod q) (by simp)
    refine (h.mul_left 2).of_nonneg_of_le (fun n => by split_ifs <;> positivity) fun n => ?_
    change (if P n then (1 : ℝ) / n else 0) ≤ 2 * if P n then w n else 0
    by_cases hn : P n
    · simp only [hn, if_true, w]
      have hp := hn.1.two_le
      have hp' : (2 : ℝ) ≤ n := by exact_mod_cast hp
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      field_simp
      nlinarith
    · simp [hn]
  obtain ⟨S, hS, hs⟩ := small_product hw₀ hw₁ hsum hε
  refine ⟨S, hS, _, hs, ?_⟩
  have hd : ∀ p ∈ S, 0 < p ^ 2 := fun p hp => pow_pos (hS p hp).1.pos _
  have hc : (S : Set ℕ).Pairwise (fun p r => (p ^ 2).Coprime (r ^ 2)) := by
    intro p hp r hr hpr
    exact Nat.Coprime.pow _ _ (((hS p hp).1.coprime_iff_not_dvd).mpr fun hd =>
      hpr (((Nat.dvd_prime (hS r hr).1).mp hd).resolve_left (hS p hp).1.ne_one))
  have hD := density_system S (fun p => p ^ 2) hd hc (fun p x => x ∉ hit p)
  convert hD using 1
  exact Finset.prod_congr rfl fun p hp => (residues_avoids_hit p (hS p hp).1).symm

noncomputable def countSet (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (· ∈ A)

lemma mem_countSet {n N : ℕ} {A : Set ℕ} :
    n ∈ countSet A N ↔ n < N ∧ n ∈ A := by
  classical
  simp [countSet]

lemma partial_density_count (A : Set ℕ) (N : ℕ) :
    A.partialDensity Set.univ N = (countSet A N).card / (N : ℝ) := by
  rw [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  congr 1
  rw [show A ∩ Set.Iio N = (↑(countSet A N) : Set ℕ) by
    ext k; simp [mem_countSet, and_comm], Set.ncard_coe_finset]

end OMA.Pollack

open OMA.Pollack in
theorem OMA.solution : type_of% @Erdos955.erdos_955.variants.pollack_primes := by
  classical
  let A : Set ℕ := {n | (Erdos955.s n).Prime}
  change Tendsto (fun n => A.partialDensity Set.univ n) atTop (𝓝 (0 : ℝ))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsum : ¬ Summable (fun p : ℕ => if p.Prime then (1 : ℝ) / p else 0) := by
    have hfun : (fun p : ℕ => if p.Prime then (1 : ℝ) / p else 0) =
        {p : ℕ | p.Prime}.indicator (fun p : ℕ => (1 : ℝ) / p) := by
      ext p
      by_cases hp : p.Prime <;> simp [Set.indicator, hp]
    rw [hfun]
    exact not_summable_one_div_on_primes
  have hw (p : ℕ) : (1 : ℝ) / p ≤ 1 := by
    rcases p with _ | p
    · simp
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast Nat.succ_pos p
  obtain ⟨Q, hQ, hsmall⟩ := small_product (fun _ => by positivity) hw hsum
    (show 0 < ε / 4 by positivity)
  let B : Set ℕ := {n | ∀ q ∈ Q, ¬ q ∣ n}
  have hB : B.HasDensity (∏ q ∈ Q, (1 - 1 / (q : ℝ))) := by
    have h := density_system Q id (fun q hq => (hQ q hq).pos)
      (fun q hq r hr hne => (hQ q hq).coprime_iff_not_dvd.mpr fun hd =>
        hne (((Nat.dvd_prime (hQ r hr)).mp hd).resolve_left (hQ q hq).ne_one))
      (fun _ z => z ≠ 0)
    have heq : (∏ q ∈ Q, residues q (fun x => x ≠ 0) / (q : ℝ)) =
        ∏ q ∈ Q, (1 - 1 / (q : ℝ)) :=
      Finset.prod_congr rfl fun q hq => residues_ne_zero q (hQ q hq)
    have he : {n : ℕ | ∀ q ∈ Q, (n : ZMod q) ≠ 0} = B := by
      ext n
      simp [B, ZMod.natCast_eq_zero_iff]
    change {n : ℕ | ∀ q ∈ Q, (n : ZMod q) ≠ 0}.HasDensity
      (∏ q ∈ Q, residues q (fun x => x ≠ 0) / (q : ℝ)) at h
    rwa [he, heq] at h
  let η : ℝ := ε / (4 * ((Q.card : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hex q (hq : q ∈ Q) := density_small_sieve (hQ q hq) hη
  choose S hS ρ hρ hE using hex
  let E (q : ℕ) : Set ℕ :=
    if hq : q ∈ Q then {n | ∀ p ∈ S q hq, (n : ZMod (p ^ 2)) ∉ hit p} else ∅
  have hEt q (hq : q ∈ Q) : ∀ᶠ n in atTop, (E q).partialDensity Set.univ n < η := by
    have hD : (E q).HasDensity (ρ q hq) := by simpa [E, hq] using hE q hq
    exact hD.eventually_lt tendsto_const_nhds (hρ q hq)
  have hbnd : ∀ᶠ n in atTop, B.partialDensity Set.univ n < ε / 4 :=
    hB.eventually_lt tendsto_const_nhds hsmall
  let K : ℕ := Q.sup (fun q => q ^ 2) + 1
  have cover : ∀ n ≥ K, n ∈ A → n ∈ B ∨ ∃ q ∈ Q, n ∈ E q := by
    intro n hn ha
    by_cases hb : n ∈ B
    · exact Or.inl hb
    right
    obtain ⟨q, hq, hd⟩ : ∃ q ∈ Q, q ∣ n := by
      by_contra! hc
      exact hb (fun q hq => hc q hq)
    refine ⟨q, hq, ?_⟩
    simp only [E, dif_pos hq, Set.mem_ofPred_eq]
    intro p hp hhit
    obtain ⟨hdp, hnp⟩ := (mem_hit (hS q hq p hp).1).mp hhit
    have hds := divisor_of_aliquot (hS q hq p hp).1 (hS q hq p hp).2 hd hdp hnp
    have hqK : q ^ 2 ≤ Q.sup (fun q => q ^ 2) := Finset.le_sup (f := fun q : ℕ => q ^ 2) hq
    have hlt := lt_aliquot_of_sq_lt (hQ q hq) hd (by omega)
    have hprime : (Erdos955.s n).Prime := ha
    rcases (Nat.dvd_prime hprime).mp hds with h | h
    · exact (hQ q hq).ne_one h
    · exact hlt.ne h
  have hke : ∀ᶠ n : ℕ in atTop, (K : ℝ) / (n : ℝ) < ε / 4 :=
    (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).eventually_lt tendsto_const_nhds (by positivity)
  filter_upwards [hbnd, (eventually_all_finset Q).mpr hEt, hke] with N hnB hnE hnK
  let C (U : Set ℕ) := countSet U N
  have hc : C A ⊆ (Finset.range K) ∪ (C B ∪ Q.biUnion (fun q => C (E q))) := by
    intro n hn
    obtain ⟨hnN, hnA⟩ := mem_countSet.mp hn
    by_cases hk : n < K
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hk)
    apply Finset.mem_union_right
    rcases cover n (by omega) hnA with hb | ⟨q, hq, he⟩
    · exact Finset.mem_union_left _ (mem_countSet.mpr ⟨hnN, hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq, mem_countSet.mpr ⟨hnN, he⟩⟩)
  have hcards : (C A).card ≤ K + ((C B).card + ∑ q ∈ Q, (C (E q)).card) := by
    calc
      _ ≤ ((Finset.range K) ∪ (C B ∪ Q.biUnion (fun q => C (E q)))).card := Finset.card_le_card hc
      _ ≤ (Finset.range K).card + (C B ∪ Q.biUnion (fun q => C (E q))).card := Finset.card_union_le _ _
      _ ≤ _ := by
        rw [Finset.card_range]
        exact Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left Finset.card_biUnion_le _)) _
  have hparts : A.partialDensity Set.univ N ≤
      (K : ℝ) / N + (B.partialDensity Set.univ N + ∑ q ∈ Q, (E q).partialDensity Set.univ N) := by
    simp only [partial_density_count, ← Finset.sum_div, ← add_div, ← Nat.cast_sum, ← Nat.cast_add]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact_mod_cast hcards
  have hs : ∑ q ∈ Q, (E q).partialDensity Set.univ N ≤ ε / 4 := by
    calc
      _ ≤ ∑ q ∈ Q, η := Finset.sum_le_sum fun q hq => (hnE q hq).le
      _ = (Q.card : ℝ) * η := by simp [nsmul_eq_mul]
      _ ≤ ε / 4 := by
        have heq : ((Q.card : ℝ) + 1) * η = ε / 4 := by
          dsimp [η]
          field_simp
        linarith only [heq, hη]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  linarith only [hparts, hnB, hnK, hs, hε]
