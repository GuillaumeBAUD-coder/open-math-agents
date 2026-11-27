import FormalConjectures.Arxiv.«2604.08040».Conjecture5_5
import Mathlib.Tactic

open Arxiv.«2604.08040»

universe u

namespace OMA.Cyc
open Finset

section part1
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

lemma frob_pow_eq_of_modEq {K : Type*} [Group K] {x : K} {n m m' : ℕ} (hx : x ^ n = 1)
    (h : m ≡ m' [MOD n]) : x ^ m = x ^ m' :=
  pow_eq_pow_iff_modEq.mpr (h.of_dvd (orderOf_dvd_of_pow_eq_one hx))

lemma frob_natCard_eq_card {K : Type*} [Fintype K] (P : K → Prop) [DecidablePred P] :
    Nat.card {x : K // P x} = (univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

-- F0
lemma frob_decomp {K : Type*} [Group K] [Fintype K] [DecidableEq K] {a b : ℕ}
    (hab : Nat.Coprime a b) :
    (univ.filter fun x : K => x ^ (a * b) = 1).card =
      ∑ v ∈ univ.filter (fun v : K => v ^ b = 1),
        (univ.filter fun u : K => u ^ a = 1 ∧ u * v = v * u).card := by
  obtain ⟨α, hα0, hα1⟩ := Nat.chineseRemainder hab 0 1
  obtain ⟨β, hβ1, hβ0⟩ := Nat.chineseRemainder hab 1 0
  have haα : a ∣ α := Nat.modEq_zero_iff_dvd.mp hα0
  have hbβ : b ∣ β := Nat.modEq_zero_iff_dvd.mp hβ0
  have hsum : β + α ≡ 1 [MOD a * b] := by
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hab]
    constructor
    · have := Nat.ModEq.add hβ1 hα0
      simpa using this
    · have := Nat.ModEq.add hβ0 hα1
      simpa using this
  have hβa : a * b ∣ β * a := by
    rw [mul_comm β]; exact Nat.mul_dvd_mul_left a hbβ
  have hαb : a * b ∣ α * b := Nat.mul_dvd_mul_right haα b
  rw [card_eq_sum_card_fiberwise (f := fun x : K => x ^ α)
    (t := univ.filter (fun v : K => v ^ b = 1))]
  · refine sum_congr rfl fun v hv => ?_
    simp only [mem_filter, mem_univ, true_and] at hv
    refine card_nbij' (fun x => x * v⁻¹) (fun u => u * v) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      obtain ⟨hx1, rfl⟩ := hx
      have key : x * (x ^ α)⁻¹ = x ^ β := by
        rw [mul_inv_eq_iff_eq_mul, ← pow_add]
        rw [frob_pow_eq_of_modEq hx1 hsum, pow_one]
      rw [key]
      refine ⟨?_, ?_⟩
      · rw [← pow_mul]
        obtain ⟨c, hc⟩ := hβa
        rw [hc, pow_mul, hx1, one_pow]
      · rw [← pow_add, ← pow_add, add_comm]
    · intro u hu
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
      obtain ⟨hu1, hu2⟩ := hu
      have hc : Commute u v := hu2
      refine ⟨?_, ?_⟩
      · rw [hc.mul_pow, pow_mul, hu1, one_pow, one_mul, mul_comm, pow_mul, hv, one_pow]
      · rw [hc.mul_pow]
        obtain ⟨c, hc'⟩ := haα
        rw [hc', pow_mul, hu1, one_pow, one_mul, ← hc', frob_pow_eq_of_modEq hv hα1, pow_one]
    · intro x _
      simp
    · intro u _
      simp
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [← pow_mul]
    obtain ⟨c, hc⟩ := hαb
    rw [hc, pow_mul, hx, one_pow]

section ClassSums
variable {K : Type*} [Group K] [Fintype K] [DecidableEq K]

-- conjugacy class as a finset
def frob_cls (v : K) : Finset K :=
  univ.image fun h : K => h * v * h⁻¹

lemma frob_mem_cls {v w : K} : w ∈ frob_cls v ↔ ∃ h, h * v * h⁻¹ = w := by
  simp [frob_cls]

lemma frob_self_mem_cls (v : K) : v ∈ frob_cls v := frob_mem_cls.mpr ⟨1, by simp⟩

lemma frob_cls_conj (v h : K) : frob_cls (h * v * h⁻¹) = frob_cls v := by
  ext w
  simp only [frob_mem_cls]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k * h, by group⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k * h⁻¹, by group⟩

lemma frob_cls_card_mul (v : K) :
    (frob_cls v).card * (univ.filter fun h : K => h * v = v * h).card = Fintype.card K := by
  have h1 : (univ : Finset K).card =
      ∑ w ∈ frob_cls v, (univ.filter fun h : K => h * v * h⁻¹ = w).card :=
    card_eq_sum_card_fiberwise (fun h _ => frob_mem_cls.mpr ⟨h, rfl⟩)
  have hfib : ∀ w ∈ frob_cls v, (univ.filter fun h : K => h * v * h⁻¹ = w).card =
      (univ.filter fun h : K => h * v = v * h).card := by
    intro w hw
    obtain ⟨h0, rfl⟩ := frob_mem_cls.mp hw
    refine card_nbij' (fun h => h0⁻¹ * h) (fun k => h0 * k) ?_ ?_ ?_ ?_
    · intro h hh
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
      calc h0⁻¹ * h * v = h0⁻¹ * (h * v * h⁻¹) * h := by group
        _ = h0⁻¹ * (h0 * v * h0⁻¹) * h := by rw [hh]
        _ = v * (h0⁻¹ * h) := by group
    · intro k hk
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
      calc h0 * k * v * (h0 * k)⁻¹ = h0 * (k * v) * k⁻¹ * h0⁻¹ := by group
        _ = h0 * (v * k) * k⁻¹ * h0⁻¹ := by rw [hk]
        _ = h0 * v * h0⁻¹ := by group
    · intro h _
      simp
    · intro k _
      simp
  rw [← card_univ, h1, sum_congr rfl hfib, sum_const, smul_eq_mul]

-- F1
lemma frob_class_sum (V : Finset K) (hV : ∀ v ∈ V, ∀ h : K, h * v * h⁻¹ ∈ V) (f : K → ℕ)
    (hf : ∀ v h : K, f (h * v * h⁻¹) = f v) (M : ℕ)
    (hM : ∀ v ∈ V, M ∣ f v * (frob_cls v).card) : M ∣ ∑ v ∈ V, f v := by
  rw [← sum_fiberwise_of_maps_to (g := frob_cls) (t := V.image frob_cls)
    (fun v hv => mem_image_of_mem _ hv)]
  refine dvd_sum fun c hc => ?_
  obtain ⟨v0, hv0, rfl⟩ := mem_image.mp hc
  have hfib : V.filter (fun v => frob_cls v = frob_cls v0) = frob_cls v0 := by
    ext w
    simp only [mem_filter]
    constructor
    · rintro ⟨_, hw⟩
      rw [← hw]
      exact frob_self_mem_cls w
    · intro hw
      obtain ⟨h, rfl⟩ := frob_mem_cls.mp hw
      exact ⟨hV v0 hv0 h, frob_cls_conj v0 h⟩
  rw [hfib, sum_congr rfl (g := fun _ => f v0), sum_const, smul_eq_mul, mul_comm]
  · exact hM v0 hv0
  · intro w hw
    obtain ⟨h, rfl⟩ := frob_mem_cls.mp hw
    exact hf v0 h

lemma frob_f_conj (a : ℕ) (v h : K) :
    (univ.filter fun u : K => u ^ a = 1 ∧ u * (h * v * h⁻¹) = (h * v * h⁻¹) * u).card =
      (univ.filter fun u : K => u ^ a = 1 ∧ u * v = v * u).card := by
  refine card_nbij' (fun u => h⁻¹ * u * h) (fun u => h * u * h⁻¹) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    obtain ⟨h1, h2⟩ := hu
    refine ⟨?_, ?_⟩
    · have := conj_pow (a := h⁻¹) (b := u) (i := a)
      rw [inv_inv] at this
      rw [this, h1]
      group
    · calc h⁻¹ * u * h * v = h⁻¹ * (u * (h * v * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * v * h⁻¹) * u) * h := by rw [h2]
        _ = v * (h⁻¹ * u * h) := by group
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    obtain ⟨h1, h2⟩ := hu
    refine ⟨?_, ?_⟩
    · rw [conj_pow, h1]
      group
    · calc h * u * h⁻¹ * (h * v * h⁻¹) = h * (u * v) * h⁻¹ := by group
        _ = h * (v * u) * h⁻¹ := by rw [h2]
        _ = h * v * h⁻¹ * (h * u * h⁻¹) := by group
  · intro u _
    simp only
    group
  · intro u _
    simp only
    group

lemma frob_natCard_centralizer (v : K) :
    Nat.card (Subgroup.centralizer {v}) = (univ.filter fun h : K => h * v = v * h).card := by
  rw [← frob_natCard_eq_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun h => Subgroup.mem_centralizer_singleton_iff)

lemma frob_natCard_centralizer_pow (v : K) (e : ℕ) :
    Nat.card {y : Subgroup.centralizer {v} // y ^ e = 1} =
      (univ.filter fun u : K => u ^ e = 1 ∧ u * v = v * u).card := by
  rw [← frob_natCard_eq_card]
  refine Nat.card_congr ((Equiv.subtypeEquivRight
    (q := fun y : Subgroup.centralizer {v} => (y : K) ^ e = 1) ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ Subgroup.centralizer {v})
      (fun u => u ^ e = 1)).trans (Equiv.subtypeEquivRight ?_)))
  · intro y
    rw [← Subgroup.coe_pow, OneMemClass.coe_eq_one]
  · intro u
    rw [Subgroup.mem_centralizer_singleton_iff, and_comm]

end ClassSums

lemma frob_zpowers_eq_iff {K : Type*} [Group K] [Fintype K] {x g : K} :
    Subgroup.zpowers x = Subgroup.zpowers g ↔ x ∈ Subgroup.zpowers g ∧ orderOf x = orderOf g := by
  constructor
  · intro h
    refine ⟨h ▸ Subgroup.mem_zpowers x, ?_⟩
    rw [← Nat.card_zpowers, ← Nat.card_zpowers, h]
  · rintro ⟨hx, ho⟩
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hx
    · rw [Nat.card_zpowers, Nat.card_zpowers, ho]

lemma frob_fiber_card {K : Type*} [Group K] [Fintype K] [DecidableEq (Subgroup K)] (g : K) :
    (univ.filter fun x : K => Subgroup.zpowers x = Subgroup.zpowers g).card =
      (orderOf g).totient := by
  classical
  have h1 := IsCyclic.card_orderOf_eq_totient (α := Subgroup.zpowers g) (d := orderOf g)
    (by rw [← Nat.card_eq_fintype_card, Nat.card_zpowers])
  rw [← h1]
  symm
  refine card_bij (fun a _ => (a : K)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [frob_zpowers_eq_iff, Subgroup.orderOf_coe]
    exact ⟨a.2, ha⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hx1, hx2⟩ := frob_zpowers_eq_iff.mp hx
    refine ⟨⟨x, hx1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [← Subgroup.orderOf_coe]
    exact hx2

section Cyclic
variable {K : Type*} [Group K] [Fintype K]

lemma frob_totient_dvd (d : ℕ) : d.totient ∣ (univ.filter fun x : K => orderOf x = d).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun x : K => Subgroup.zpowers x)
    (s := univ.filter fun x : K => orderOf x = d)
    (t := (univ.filter fun x : K => orderOf x = d).image fun x => Subgroup.zpowers x)
    (fun x hx => mem_image_of_mem _ hx)]
  refine dvd_sum fun C hC => ?_
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hC
  simp only [mem_filter, mem_univ, true_and] at hg
  have : ((univ.filter fun x : K => orderOf x = d).filter
      fun x => Subgroup.zpowers x = Subgroup.zpowers g) =
      univ.filter fun x : K => Subgroup.zpowers x = Subgroup.zpowers g := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨(frob_zpowers_eq_iff.mp h).2.trans hg, h⟩
  rw [this]
  refine dvd_of_eq ?_
  rw [← hg]
  convert (frob_fiber_card g).symm

lemma frob_cyc_eq_sum : (cyc K : ℚ) = ∑ x : K, 1 / ((orderOf x).totient : ℚ) := by
  classical
  set T : Finset (Subgroup K) := univ.image fun x : K => Subgroup.zpowers x with hT
  have hcyc : cyc K = T.card := by
    unfold cyc
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun H => by
      rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
      simp [T])
  rw [hcyc, ← sum_fiberwise_of_maps_to (g := fun x : K => Subgroup.zpowers x) (t := T)
    (fun x _ => mem_image_of_mem _ (mem_univ x)), card_eq_sum_ones, Nat.cast_sum]
  refine sum_congr rfl fun C hC => ?_
  obtain ⟨g, _, rfl⟩ := mem_image.mp hC
  rw [sum_congr rfl (g := fun _ => 1 / ((orderOf g).totient : ℚ)), sum_const, nsmul_eq_mul]
  · have h3 : (univ.filter fun i : K => Subgroup.zpowers i = Subgroup.zpowers g).card =
        (orderOf g).totient := by
      convert frob_fiber_card g
    rw [h3]
    have : ((orderOf g).totient : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (orderOf_pos g)).ne'
    simp [this]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [(frob_zpowers_eq_iff.mp hx).2]

end Cyclic

section Frob

lemma frob_card_pow_succ {K : Type*} [Group K] [Fintype K] [DecidableEq K] {p : ℕ}
    (hp : p.Prime) (b : ℕ) :
    (univ.filter fun x : K => x ^ p ^ (b + 1) = 1).card =
      (univ.filter fun x : K => x ^ p ^ b = 1).card +
        (univ.filter fun x : K => orderOf x = p ^ (b + 1)).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_union, ← orderOf_dvd_iff_pow_eq_one]
    constructor
    · intro h
      obtain ⟨i, hi, hx⟩ := (Nat.dvd_prime_pow hp).mp h
      rcases Nat.lt_or_ge i (b + 1) with h' | h'
      · left
        rw [hx]
        exact pow_dvd_pow p (by omega)
      · right
        rw [hx, show i = b + 1 by omega]
    · rintro (h | h)
      · exact h.trans (pow_dvd_pow p (Nat.le_succ b))
      · rw [h]
  · rw [disjoint_filter]
    intro x _ h1 h2
    rw [← orderOf_dvd_iff_pow_eq_one, h2] at h1
    have h3 := Nat.le_of_dvd (pow_pos hp.pos _) h1
    have h4 := Nat.pow_lt_pow_right hp.one_lt (show b < b + 1 by omega)
    omega

-- central elements with v ^ k = 1
def frob_Zk (K : Type*) [Group K] (k : ℕ) : Subgroup K where
  carrier := {v | v ^ k = 1 ∧ ∀ g : K, g * v = v * g}
  one_mem' := ⟨one_pow k, fun g => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · have hab : Commute a b := (ha2 b).symm
      rw [hab.mul_pow, ha1, hb1, one_mul]
    · intro g
      calc g * (a * b) = (g * a) * b := (mul_assoc _ _ _).symm
        _ = a * (g * b) := by rw [ha2 g, mul_assoc]
        _ = a * b * g := by rw [hb2 g, mul_assoc]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨by rw [inv_pow, ha1, inv_one], fun g => ?_⟩
    exact Commute.inv_right (ha2 g)

lemma frob_Zk_card {K : Type*} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime) (hk : ¬ p ∣ k) :
    ¬ p ∣ Nat.card (frob_Zk K k) := by
  intro h
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  apply hk
  rw [← hx]
  apply orderOf_dvd_of_pow_eq_one
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  exact x.2.1

lemma frob_local {K : Type*} [Group K] [Fintype K] [DecidableEq K] (v : K) (P : ℕ)
    (hP : P ∣ Fintype.card K)
    (hIH : Nat.gcd P (Nat.card (Subgroup.centralizer {v})) ∣
      Nat.card {y : Subgroup.centralizer {v} //
        y ^ Nat.gcd P (Nat.card (Subgroup.centralizer {v})) = 1}) :
    P ∣ (univ.filter fun u : K => u ^ P = 1 ∧ u * v = v * u).card * (frob_cls v).card := by
  set C := Subgroup.centralizer {v} with hC
  set g := Nat.gcd P (Nat.card C) with hg
  have h1 : Nat.card {y : C // y ^ P = 1} = Nat.card {y : C // y ^ g = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one]
    constructor
    · intro h
      exact Nat.dvd_gcd h (orderOf_dvd_natCard y)
    · intro h
      exact h.trans (Nat.gcd_dvd_left _ _)
  have h2 : g ∣ (univ.filter fun u : K => u ^ P = 1 ∧ u * v = v * u).card := by
    rw [← frob_natCard_centralizer_pow, h1]
    exact hIH
  have h3 : P ∣ g * (frob_cls v).card := by
    have hc := frob_cls_card_mul v
    rw [← frob_natCard_centralizer] at hc
    have : P ∣ Nat.gcd (P * (frob_cls v).card) (Nat.card C * (frob_cls v).card) :=
      Nat.dvd_gcd (dvd_mul_right _ _) (by rw [mul_comm, hc]; exact hP)
    rwa [Nat.gcd_mul_right] at this
  exact h3.trans (Nat.mul_dvd_mul_right h2 _)

-- F2
theorem frob_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ (K : Type*) [Group K] [Finite K], Nat.card K = n → ∀ b : ℕ, p ^ b ∣ Nat.card K →
      p ^ b ∣ Nat.card {x : K // x ^ p ^ b = 1} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K _ _ hK
  have : DecidableEq K := Classical.decEq K
  have : Fintype K := Fintype.ofFinite K
  have hn0 : Fintype.card K ≠ 0 := Fintype.card_ne_zero
  set N := Fintype.card K with hN
  set m := N.factorization p with hm
  set k := N / p ^ m with hk
  have hNk : p ^ m * k = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hkp : ¬ p ∣ k := Nat.not_dvd_ordCompl hp hn0
  have hcop : Nat.Coprime (p ^ m) k := (Nat.coprime_ordCompl hp hn0).pow_left m
  -- Step A
  have hA : p ^ m ∣ (univ.filter fun x : K => x ^ p ^ m = 1).card := by
    have h1 := frob_decomp (K := K) hcop
    rw [hNk] at h1
    have hall : (univ.filter fun x : K => x ^ N = 1) = univ := by
      ext x
      simp [hN, pow_card_eq_one]
    rw [hall, card_univ, ← sum_filter_add_sum_filter_not _
      (fun v : K => ∀ g : K, g * v = v * g)] at h1
    have hcen : ∑ v ∈ (univ.filter fun v : K => v ^ k = 1).filter
        (fun v => ∀ g : K, g * v = v * g),
        (univ.filter fun u : K => u ^ p ^ m = 1 ∧ u * v = v * u).card =
        ((univ.filter fun v : K => v ^ k = 1).filter (fun v => ∀ g : K, g * v = v * g)).card *
          (univ.filter fun u : K => u ^ p ^ m = 1).card := by
      rw [← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun v hv => ?_
      simp only [mem_filter, mem_univ, true_and] at hv
      congr 1
      ext u
      simp [hv.2 u]
    have hnc : p ^ m ∣ ∑ v ∈ (univ.filter fun v : K => v ^ k = 1).filter
        (fun v => ¬ ∀ g : K, g * v = v * g),
        (univ.filter fun u : K => u ^ p ^ m = 1 ∧ u * v = v * u).card := by
      refine frob_class_sum _ ?_
        (fun v => (univ.filter fun u : K => u ^ p ^ m = 1 ∧ u * v = v * u).card) ?_ _ ?_
      · intro v hv h
        simp only [mem_filter, mem_univ, true_and] at hv ⊢
        refine ⟨by rw [conj_pow, hv.1]; group, fun hc => hv.2 fun g => ?_⟩
        have := hc (h * g * h⁻¹)
        calc g * v = h⁻¹ * ((h * g * h⁻¹) * (h * v * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * v * h⁻¹) * (h * g * h⁻¹)) * h := by rw [this]
          _ = v * g := by group
      · intro v h
        exact frob_f_conj _ v h
      · intro v hv
        simp only [mem_filter, mem_univ, true_and] at hv
        apply frob_local v (p ^ m) (Dvd.intro k hNk)
        have hne : Subgroup.centralizer {v} ≠ ⊤ := by
          intro htop
          apply hv.2
          intro g
          have : g ∈ Subgroup.centralizer {v} := htop ▸ Subgroup.mem_top g
          exact Subgroup.mem_centralizer_singleton_iff.mp this
        have hlt : Nat.card (Subgroup.centralizer {v}) < n := by
          rw [← hK]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group _)
            (fun h => hne ((Subgroup.card_eq_iff_eq_top _).mp h))
        obtain ⟨c, _, hc⟩ := (Nat.dvd_prime_pow hp).mp
          (Nat.gcd_dvd_left (p ^ m) (Nat.card (Subgroup.centralizer {v})))
        rw [hc]
        exact ih _ hlt _ rfl c (hc ▸ Nat.gcd_dvd_right _ _)
    rw [hcen] at h1
    have h2 : p ^ m ∣ ((univ.filter fun v : K => v ^ k = 1).filter
        (fun v => ∀ g : K, g * v = v * g)).card *
          (univ.filter fun u : K => u ^ p ^ m = 1).card :=
      by
        have hdiv : p ^ m ∣ Fintype.card K := Dvd.intro k hNk
        rw [h1] at hdiv
        exact (Nat.dvd_add_left hnc).mp hdiv
    have hZ : ¬ p ∣ ((univ.filter fun v : K => v ^ k = 1).filter
        (fun v => ∀ g : K, g * v = v * g)).card := by
      have := frob_Zk_card (K := K) hp hkp
      rwa [show Nat.card (frob_Zk K k) = ((univ.filter fun v : K => v ^ k = 1).filter
        (fun v => ∀ g : K, g * v = v * g)).card by
          rw [filter_filter, ← frob_natCard_eq_card]
          rfl] at this
    exact (Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ)).dvd_of_dvd_mul_left h2
  -- Step B
  have hB : ∀ j, p ^ (m - j) ∣ (univ.filter fun x : K => x ^ p ^ (m - j) = 1).card := by
    intro j
    induction j with
    | zero => simpa using hA
    | succ j ihj =>
      rcases Nat.eq_zero_or_pos (m - j) with h0 | hpos
      · rw [show m - (j + 1) = 0 by omega, pow_zero]
        exact one_dvd _
      · rw [show m - j = (m - (j + 1)) + 1 by omega, frob_card_pow_succ hp] at ihj
        have ht : p ^ (m - (j + 1)) ∣
            (univ.filter fun x : K => orderOf x = p ^ (m - (j + 1) + 1)).card := by
          refine dvd_trans ?_ (frob_totient_dvd _)
          rw [Nat.totient_prime_pow_succ hp]
          exact dvd_mul_right _ _
        exact (Nat.dvd_add_left ht).mp ((pow_dvd_pow p (Nat.le_succ _)).trans ihj)
  intro b hb
  rw [Nat.card_eq_fintype_card] at hb
  have hbm : b ≤ m := (hp.pow_dvd_iff_le_factorization hn0).mp hb
  have := hB (m - b)
  rw [show m - (m - b) = b by omega] at this
  rw [frob_natCard_eq_card]
  exact this

-- F3
theorem frob_main {K : Type*} [Group K] [Fintype K] [DecidableEq K] {n : ℕ}
    (hn : n ∣ Fintype.card K) : n ∣ (univ.filter fun x : K => x ^ n = 1).card := by
  have hcard0 : Fintype.card K ≠ 0 := Fintype.card_ne_zero
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hcard0 (zero_dvd_iff.mp hn)
  have hL0 : (univ.filter fun x : K => x ^ n = 1).card ≠ 0 := by
    apply card_ne_zero_of_mem (a := 1)
    simp
  rw [← Nat.factorization_prime_le_iff_dvd hn0 hL0]
  intro p hp
  rw [← hp.pow_dvd_iff_le_factorization hL0]
  set b := n.factorization p with hb
  have hcop : Nat.Coprime (p ^ b) (n / p ^ b) := (Nat.coprime_ordCompl hp hn0).pow_left b
  have hnb : p ^ b * (n / p ^ b) = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have h1 := frob_decomp (K := K) hcop
  rw [hnb] at h1
  rw [h1]
  refine frob_class_sum _ ?_
    (fun v => (univ.filter fun u : K => u ^ p ^ b = 1 ∧ u * v = v * u).card) ?_ _ ?_
  · intro v hv h
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    rw [conj_pow, hv]
    group
  · intro v h
    exact frob_f_conj _ v h
  · intro v _
    apply frob_local v (p ^ b) ((Nat.ordProj_dvd n p).trans hn)
    obtain ⟨c, _, hc⟩ := (Nat.dvd_prime_pow hp).mp
      (Nat.gcd_dvd_left (p ^ b) (Nat.card (Subgroup.centralizer {v})))
    rw [hc]
    exact frob_prime_pow hp _ _ rfl c (hc ▸ Nat.gcd_dvd_right _ _)

end Frob

theorem totient_dvd_card_orderOf_eq (d : ℕ) :
    d.totient ∣ (univ.filter fun x : G => orderOf x = d).card :=
  frob_totient_dvd d

theorem cyc_eq_sum (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    (cyc G : ℚ) = ∑ x : G, 1 / ((orderOf x).totient : ℚ) :=
  frob_cyc_eq_sum

theorem frobenius {n : ℕ} (hn : n ∣ Fintype.card G) :
    n ∣ (univ.filter fun x : G => x ^ n = 1).card :=
  frob_main hn
end part1

section part2
theorem rich_sum_mul {m n : ℕ} (hmn : m.Coprime n) (f : ℕ → ℚ) :
    ∑ e ∈ (m * n).divisors, f e = ∑ e₁ ∈ m.divisors, ∑ e₂ ∈ n.divisors, f (e₁ * e₂) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hmn.mul_injOn_divisors,
    Finset.sum_product]

theorem rich_coprime {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (hmk : m.Coprime k)
    (Pm : ∀ a : ℕ → ℚ, (∀ d ∈ m.divisors, (d : ℚ) ≤ ∑ e ∈ d.divisors, a e) →
      (m.divisors.card : ℚ) ≤ ∑ e ∈ m.divisors, a e / (e.totient : ℚ))
    (Pk : ∀ a : ℕ → ℚ, (∀ d ∈ k.divisors, (d : ℚ) ≤ ∑ e ∈ d.divisors, a e) →
      (k.divisors.card : ℚ) ≤ ∑ e ∈ k.divisors, a e / (e.totient : ℚ))
    (a : ℕ → ℚ) (h : ∀ d ∈ (m * k).divisors, (d : ℚ) ≤ ∑ e ∈ d.divisors, a e) :
    ((m * k).divisors.card : ℚ) ≤ ∑ e ∈ (m * k).divisors, a e / (e.totient : ℚ) := by
  have hτk : (0 : ℚ) < k.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hk.ne')
  set c : ℕ → ℚ := fun e₁ => ∑ e₂ ∈ k.divisors, a (e₁ * e₂) / (e₂.totient : ℚ) with hc
  have hrhs : ∑ e ∈ (m * k).divisors, a e / (e.totient : ℚ)
      = ∑ e₁ ∈ m.divisors, c e₁ / (e₁.totient : ℚ) := by
    rw [rich_sum_mul hmk]
    apply Finset.sum_congr rfl
    intro e₁ he₁
    rw [hc, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e₂ he₂
    have hcop : e₁.Coprime e₂ :=
      Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors he₁)
        (Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors he₂) hmk)
    rw [Nat.totient_mul hcop, Nat.cast_mul, div_div, mul_comm (e₂.totient : ℚ)]
  have hkey : ∀ d₁ ∈ m.divisors, (d₁ : ℚ) * k.divisors.card ≤ ∑ e₁ ∈ d₁.divisors, c e₁ := by
    intro d₁ hd₁
    have hd₁pos : (0 : ℚ) < d₁ := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
    have hcop1 : d₁.Coprime k := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd₁) hmk
    have hP := Pk (fun e₂ => (∑ e₁ ∈ d₁.divisors, a (e₁ * e₂)) / d₁) ?_
    · have heq : ∑ e₂ ∈ k.divisors, (∑ e₁ ∈ d₁.divisors, a (e₁ * e₂)) / d₁ / (e₂.totient : ℚ)
          = (∑ e₁ ∈ d₁.divisors, c e₁) / d₁ := by
        rw [hc]
        simp only [Finset.sum_div]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [heq, le_div_iff₀ hd₁pos] at hP
      linarith
    · intro d₂ hd₂
      have hcop : d₁.Coprime d₂ :=
        Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd₂) hcop1
      have hmem : d₁ * d₂ ∈ (m * k).divisors := by
        rw [Nat.mem_divisors]
        exact ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd₁) (Nat.dvd_of_mem_divisors hd₂),
          by positivity⟩
      have hh := h _ hmem
      rw [rich_sum_mul hcop, Nat.cast_mul] at hh
      rw [← Finset.sum_div, Finset.sum_comm, le_div_iff₀ hd₁pos]
      linarith
  have hP := Pm (fun e₁ => c e₁ / k.divisors.card) ?_
  · rw [hrhs, Nat.Coprime.card_divisors_mul hmk, Nat.cast_mul]
    have heq : ∑ e₁ ∈ m.divisors, c e₁ / k.divisors.card / (e₁.totient : ℚ)
        = (∑ e₁ ∈ m.divisors, c e₁ / (e₁.totient : ℚ)) / k.divisors.card := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq, le_div_iff₀ hτk] at hP
    linarith
  · intro d₁ hd₁
    rw [← Finset.sum_div, le_div_iff₀ hτk]
    exact hkey d₁ hd₁

theorem rich_chain {p : ℕ} (hp : p.Prime) (x : ℕ → ℚ) (A : ℕ)
    (hx : ∀ j ≤ A, (p : ℚ) ^ j ≤ ∑ i ∈ range (j + 1), x i) :
    (A + 1 : ℚ) + (∑ i ∈ range (A + 1), x i - (p : ℚ) ^ A) / ((p ^ A).totient : ℚ)
      ≤ ∑ j ∈ range (A + 1), x j / ((p ^ j).totient : ℚ) := by
  induction A with
  | zero => simp
  | succ A ih =>
    have ih' := ih (fun j hj => hx j (by omega))
    have hA := hx A (by omega)
    have hA1 := hx (A + 1) le_rfl
    rw [Finset.sum_range_succ] at hA1
    rw [Finset.sum_range_succ x (A + 1), Finset.sum_range_succ (fun j => x j / _) (A + 1)]
    have hφA : (0 : ℚ) < ((p ^ A).totient : ℚ) := by
      exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos _)
    have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    have hφ1 : (((p ^ (A + 1)).totient : ℕ) : ℚ) = (p : ℚ) ^ A * ((p : ℚ) - 1) := by
      rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_sub hp.one_le]
      push_cast
      ring
    have hle : ((p ^ A).totient : ℚ) ≤ ((p ^ (A + 1)).totient : ℚ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr (pow_pos hp.pos _))
        (Nat.totient_dvd_of_dvd (pow_dvd_pow p (Nat.le_succ A)))
    have hu : 0 ≤ ∑ i ∈ range (A + 1), x i - (p : ℚ) ^ A := by linarith
    have h1 : (∑ i ∈ range (A + 1), x i - (p : ℚ) ^ A) / ((p ^ (A + 1)).totient : ℚ)
        ≤ (∑ i ∈ range (A + 1), x i - (p : ℚ) ^ A) / ((p ^ A).totient : ℚ) :=
      div_le_div_of_nonneg_left hu hφA hle
    have hp0 : (p : ℚ) ≠ 0 := by positivity
    have hpm : (p : ℚ) - 1 ≠ 0 := by linarith
    have h2 : (∑ i ∈ range (A + 1), x i + x (A + 1) - (p : ℚ) ^ (A + 1))
          / ((p ^ (A + 1)).totient : ℚ)
        = (∑ i ∈ range (A + 1), x i - (p : ℚ) ^ A) / ((p ^ (A + 1)).totient : ℚ)
          + x (A + 1) / ((p ^ (A + 1)).totient : ℚ) - 1 := by
      rw [hφ1]
      field_simp
      ring
    rw [h2]
    push_cast
    linarith

theorem rich_prime_pow {p : ℕ} (hp : p.Prime) (A : ℕ) (a : ℕ → ℚ)
    (h : ∀ d ∈ (p ^ A).divisors, (d : ℚ) ≤ ∑ e ∈ d.divisors, a e) :
    ((p ^ A).divisors.card : ℚ) ≤ ∑ e ∈ (p ^ A).divisors, a e / (e.totient : ℚ) := by
  have hx : ∀ j ≤ A, (p : ℚ) ^ j ≤ ∑ i ∈ range (j + 1), a (p ^ i) := by
    intro j hj
    have hmem : p ^ j ∈ (p ^ A).divisors := by
      rw [Nat.mem_divisors]
      exact ⟨pow_dvd_pow p hj, pow_ne_zero _ hp.ne_zero⟩
    have hh := h _ hmem
    rw [Nat.sum_divisors_prime_pow hp] at hh
    exact_mod_cast hh
  have key := rich_chain hp (fun i => a (p ^ i)) A hx
  have hφA : (0 : ℚ) < ((p ^ A).totient : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos _)
  have hnn : 0 ≤ (∑ i ∈ range (A + 1), a (p ^ i) - (p : ℚ) ^ A) / ((p ^ A).totient : ℚ) :=
    div_nonneg (by linarith [hx A le_rfl]) hφA.le
  rw [Nat.sum_divisors_prime_pow hp, Nat.divisors_prime_pow hp, Finset.card_map,
    Finset.card_range]
  push_cast
  linarith

theorem richard_arith (n : ℕ) (hn : 0 < n) (a : ℕ → ℚ)
    (h : ∀ d ∈ n.divisors, (d : ℚ) ≤ ∑ e ∈ d.divisors, a e) :
    (n.divisors.card : ℚ) ≤ ∑ e ∈ n.divisors, a e / (e.totient : ℚ) := by
  clear hn
  revert a h
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p A hp _ => intro a h; exact rich_prime_pow hp A a h
  | zero => intro a _; simp
  | one => intro a h; simpa using h 1 (by simp)
  | coprime m k hm hk hmk Pm Pk => intro a h; exact rich_coprime (by omega) (by omega) hmk Pm Pk a h
end part2

section part3
theorem sqf_normal_prime_of_comm_normal {H : Type*} [Group H] [Finite H]
    (hsq : Squarefree (Nat.card H)) (C : Subgroup H) [C.Normal] (hC : IsMulCommutative C)
    (h1 : 1 < Nat.card C) :
    ∃ (p : ℕ) (N : Subgroup H), p.Prime ∧ N.Normal ∧ Nat.card N = p := by
  have hp : (Nat.card C).minFac.Prime := Nat.minFac_prime (ne_of_gt h1)
  have : Fact (Nat.card C).minFac.Prime := ⟨hp⟩
  let P : Sylow (Nat.card C).minFac C := default
  have hPn : (P : Subgroup C).Normal := Subgroup.normal_of_isMulCommutative _
  have hPc : (P : Subgroup C).Characteristic := Sylow.characteristic_of_normal P hPn
  refine ⟨(Nat.card C).minFac, (P : Subgroup C).map C.subtype, hp, inferInstance, ?_⟩
  rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
  have hsqC : Squarefree (Nat.card C) :=
    hsq.squarefree_of_dvd (Subgroup.card_subgroup_dvd_card C)
  have h0 : Nat.card C ≠ 0 := by omega
  have hle := hsqC.natFactorization_le_one (Nat.card C).minFac
  have hpos := hp.factorization_pos_of_dvd h0 (Nat.minFac_dvd _)
  have h2 : (Nat.card C).factorization (Nat.card C).minFac = 1 := by omega
  rw [h2, pow_one]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem exists_normal_prime_subgroup (hsq : Squarefree (Fintype.card G))
    (h1 : 1 < Fintype.card G) :
    ∃ (p : ℕ) (N : Subgroup G), p.Prime ∧ N.Normal ∧ Nat.card N = p := by
  rw [← Nat.card_eq_fintype_card] at hsq h1
  have hZ : IsZGroup G := IsZGroup.of_squarefree hsq
  by_cases hc : commutator G = ⊥
  · have hcen : (⊤ : Subgroup G) ≤ Subgroup.centralizer (⊤ : Subgroup G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← commutator_def]
      exact hc
    have hcomm : ∀ x y : G, x * y = y * x := by
      intro x y
      exact (Subgroup.mem_centralizer_iff.mp (hcen (Subgroup.mem_top y)) x
        (Subgroup.mem_top x))
    refine sqf_normal_prime_of_comm_normal hsq ⊤ ⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩ ?_
    rwa [Subgroup.card_top]
  · have : IsCyclic (commutator G) := IsZGroup.isCyclic_commutator G
    refine sqf_normal_prime_of_comm_normal hsq (commutator G) ?_
      ((Subgroup.one_lt_card_iff_ne_bot _).mpr hc)
    exact ⟨⟨IsCyclic.commGroup.mul_comm⟩⟩

theorem isCyclic_of_nilpotent_squarefree [Group.IsNilpotent G]
    (hsq : Squarefree (Fintype.card G)) : IsCyclic G := by
  rw [← Nat.card_eq_fintype_card] at hsq
  have hZ : IsZGroup G := IsZGroup.of_squarefree hsq
  infer_instance
end part3

section part4
section
variable {G : Type*} [Group G]

lemma cmp_mk_eq_one {N : Subgroup G} [N.Normal] {x : G} (hx : x ∈ N) :
    QuotientGroup.mk' N x = 1 := by
  rw [QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff x).mpr hx

lemma cmp_map_mk_zpowers_mul {N : Subgroup G} [N.Normal] (g x : G) (hx : x ∈ N) :
    (Subgroup.zpowers (g * x)).map (QuotientGroup.mk' N) =
      (Subgroup.zpowers g).map (QuotientGroup.mk' N) := by
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, map_mul, cmp_mk_eq_one hx, mul_one]

lemma cmp_map_mk_conj {N : Subgroup G} [N.Normal] (g n : G) (hn : n ∈ N) :
    (Subgroup.zpowers (n * g * n⁻¹)).map (QuotientGroup.mk' N) =
      (Subgroup.zpowers g).map (QuotientGroup.mk' N) := by
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, map_mul, map_mul, map_inv,
    cmp_mk_eq_one hn, one_mul, inv_one, mul_one]

lemma cmp_le_of_map_le {N H D D' : Subgroup G} [N.Normal] (hdisj : N ⊓ H = ⊥)
    (hD : D ≤ H) (hD' : D' ≤ H)
    (h : D.map (QuotientGroup.mk' N) ≤ D'.map (QuotientGroup.mk' N)) : D ≤ D' := by
  intro d hd
  obtain ⟨d', hd', he⟩ := h ⟨d, hd, rfl⟩
  have h1 : d'⁻¹ * d ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    exact he
  have h2 : d'⁻¹ * d ∈ H := H.mul_mem (H.inv_mem (hD' hd')) (hD hd)
  have h3 : d'⁻¹ * d ∈ N ⊓ H := ⟨h1, h2⟩
  rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h3
  rw [← h3]
  exact hd'

lemma cmp_mul_not_mem {N H : Subgroup G} (hdisj : N ⊓ H = ⊥) {y x : G} (hy : y ∈ H)
    (hx : x ∈ N) (hx1 : x ≠ 1) : y * x ∉ H := by
  intro hyx
  have h1 : x ∈ H := by
    have := H.mul_mem (H.inv_mem hy) hyx
    rwa [inv_mul_cancel_left] at this
  have h3 : x ∈ N ⊓ H := ⟨hx, h1⟩
  rw [hdisj, Subgroup.mem_bot] at h3
  exact hx1 h3

lemma cmp_conj_inj {p : ℕ} (hp : p.Prime) {N H : Subgroup G} [hNn : N.Normal]
    (hN : Nat.card N = p) (hdisj : N ⊓ H = ⊥) {g n n' : G} (hgH : g ∈ H)
    (hcent : ¬ Subgroup.zpowers g ≤ Subgroup.centralizer (N : Set G))
    (hn : n ∈ N) (hn' : n' ∈ N)
    (hmem : n * g * n⁻¹ ∈ Subgroup.zpowers (n' * g * n'⁻¹)) : n = n' := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [conj_zpow] at hk
  set m := n'⁻¹ * n with hm
  have hmN : m ∈ N := N.mul_mem (N.inv_mem hn') hn
  have hconj : m * g * m⁻¹ = g ^ k := by
    rw [hm, mul_inv_rev, inv_inv]
    have : n' * g ^ k * n'⁻¹ = n * g * n⁻¹ := hk
    calc n'⁻¹ * n * g * (n⁻¹ * n') = n'⁻¹ * (n * g * n⁻¹) * n' := by group
      _ = n'⁻¹ * (n' * g ^ k * n'⁻¹) * n' := by rw [this]
      _ = g ^ k := by group
  have hcH : m * g * m⁻¹ * g⁻¹ ∈ H := by
    rw [hconj]
    exact H.mul_mem (H.zpow_mem hgH k) (H.inv_mem hgH)
  have hcN : m * g * m⁻¹ * g⁻¹ ∈ N := by
    have h1 : g * m⁻¹ * g⁻¹ ∈ N := hNn.conj_mem _ (N.inv_mem hmN) g
    have := N.mul_mem hmN h1
    rwa [← mul_assoc, ← mul_assoc] at this
  have hc : m * g * m⁻¹ * g⁻¹ ∈ N ⊓ H := ⟨hcN, hcH⟩
  rw [hdisj, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
  have hcomm : Commute m g := hc
  by_contra hne
  have hm1 : m ≠ 1 := by
    intro h1
    apply hne
    rw [hm, inv_mul_eq_one] at h1
    exact h1.symm
  apply hcent
  intro d hd
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have : Fact p.Prime := ⟨hp⟩
  have hm1' : (⟨m, hmN⟩ : N) ≠ 1 := by
    intro h1
    apply hm1
    exact congrArg Subtype.val h1
  have hyz : (⟨y, hy⟩ : N) ∈ Subgroup.zpowers (⟨m, hmN⟩ : N) :=
    mem_zpowers_of_prime_card hN hm1'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyz
  have hi' : m ^ i = y := by
    have := congrArg Subtype.val hi
    simpa using this
  rw [← hi']
  exact (hcomm.zpow_zpow i j).eq

end

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem cyc_ge_of_complement {p : ℕ} (hp : p.Prime) {N H : Subgroup G} [N.Normal]
    (hN : Nat.card N = p) (hNH : N.IsComplement' H) :
    2 * Nat.card {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧ D ≤ Subgroup.centralizer (N : Set G)}
      + p * Nat.card {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧ ¬ D ≤ Subgroup.centralizer (N : Set G)}
      ≤ cyc G := by
  classical
  set A := {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧ D ≤ Subgroup.centralizer (N : Set G)}
    with hA
  set B := {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧ ¬ D ≤ Subgroup.centralizer (N : Set G)}
    with hB
  have hdisj : N ⊓ H = ⊥ := hNH.disjoint.eq_bot
  have gen : ∀ D : Subgroup G, IsCyclic D → ∃ g : G, Subgroup.zpowers g = D :=
    fun D hD => (D.isCyclic_iff_exists_zpowers_eq_top).mp hD
  choose g hg using gen
  have hgmem : ∀ (D : Subgroup G) (hD : IsCyclic D), g D hD ∈ D := by
    intro D hD
    have := Subgroup.mem_zpowers (g D hD)
    rwa [hg D hD] at this
  have hNnt : Nontrivial N := by
    rw [← Finite.one_lt_card_iff_nontrivial, hN]
    exact hp.one_lt
  obtain ⟨x, hx1⟩ := exists_ne (1 : N)
  have hxN : (x : G) ∈ N := x.2
  have hx1' : (x : G) ≠ 1 := by
    intro h
    apply hx1
    exact Subtype.ext h
  let f : (A ⊕ A) ⊕ (B × N) → {C : Subgroup G // IsCyclic C} := fun z =>
    match z with
    | Sum.inl (Sum.inl a) => ⟨a.1, a.2.1⟩
    | Sum.inl (Sum.inr a) => ⟨Subgroup.zpowers (g a.1 a.2.1 * x), inferInstance⟩
    | Sum.inr (b, n) => ⟨Subgroup.zpowers ((n : G) * g b.1 b.2.1 * (n : G)⁻¹), inferInstance⟩
  let base : (A ⊕ A) ⊕ (B × N) → Subgroup G := fun z =>
    match z with
    | Sum.inl (Sum.inl a) => a.1
    | Sum.inl (Sum.inr a) => a.1
    | Sum.inr (b, _) => b.1
  have hbaseH : ∀ z, base z ≤ H := by
    rintro ((a | a) | ⟨b, n⟩)
    · exact a.2.2.1
    · exact a.2.2.1
    · exact b.2.2.1
  have hq : ∀ z, (f z).1.map (QuotientGroup.mk' N) = (base z).map (QuotientGroup.mk' N) := by
    rintro ((a | a) | ⟨b, n⟩)
    · rfl
    · show (Subgroup.zpowers (g a.1 a.2.1 * x)).map _ = a.1.map _
      rw [cmp_map_mk_zpowers_mul _ _ hxN, hg]
    · show (Subgroup.zpowers ((n : G) * g b.1 b.2.1 * (n : G)⁻¹)).map _ = b.1.map _
      rw [cmp_map_mk_conj _ _ n.2, hg]
  have hbase : ∀ z z', f z = f z' → base z = base z' := by
    intro z z' h
    have h2 := congrArg (fun C : {C : Subgroup G // IsCyclic C} =>
      C.1.map (QuotientGroup.mk' N)) h
    simp only [hq] at h2
    exact le_antisymm (cmp_le_of_map_le hdisj (hbaseH z) (hbaseH z') h2.le)
      (cmp_le_of_map_le hdisj (hbaseH z') (hbaseH z) h2.ge)
  have hinj : Function.Injective f := by
    intro z z' h
    have hb := hbase z z' h
    rcases z with ((a | a) | ⟨b, n⟩) <;> rcases z' with ((a' | a') | ⟨b', n'⟩)
    · have : a = a' := Subtype.ext hb
      subst this
      rfl
    · exfalso
      have h1 : a.1 = Subgroup.zpowers (g a'.1 a'.2.1 * x) := congrArg Subtype.val h
      have h2 : g a'.1 a'.2.1 * x ∈ H := by
        apply a.2.2.1
        rw [h1]
        exact Subgroup.mem_zpowers _
      have h3 : g a'.1 a'.2.1 ∈ H := by
        exact a'.2.2.1 (hgmem a'.1 a'.2.1)
      exact cmp_mul_not_mem hdisj h3 hxN hx1' h2
    · change a.1 = b'.1 at hb
      exact absurd (hb ▸ a.2.2.2) b'.2.2.2
    · exfalso
      have h1 : a'.1 = Subgroup.zpowers (g a.1 a.2.1 * x) := (congrArg Subtype.val h).symm
      have h2 : g a.1 a.2.1 * x ∈ H := by
        apply a'.2.2.1
        rw [h1]
        exact Subgroup.mem_zpowers _
      have h3 : g a.1 a.2.1 ∈ H := by
        exact a.2.2.1 (hgmem a.1 a.2.1)
      exact cmp_mul_not_mem hdisj h3 hxN hx1' h2
    · have : a = a' := Subtype.ext hb
      subst this
      rfl
    · change a.1 = b'.1 at hb
      exact absurd (hb ▸ a.2.2.2) b'.2.2.2
    · change b.1 = a'.1 at hb
      exact absurd (hb ▸ a'.2.2.2) b.2.2.2
    · change b.1 = a'.1 at hb
      exact absurd (hb ▸ a'.2.2.2) b.2.2.2
    · have : b = b' := Subtype.ext hb
      subst this
      have h1 : Subgroup.zpowers ((n : G) * g b.1 b.2.1 * (n : G)⁻¹) =
          Subgroup.zpowers ((n' : G) * g b.1 b.2.1 * (n' : G)⁻¹) := congrArg Subtype.val h
      have hmem : (n : G) * g b.1 b.2.1 * (n : G)⁻¹ ∈
          Subgroup.zpowers ((n' : G) * g b.1 b.2.1 * (n' : G)⁻¹) := by
        rw [← h1]
        exact Subgroup.mem_zpowers _
      have hgH : g b.1 b.2.1 ∈ H := by
        exact b.2.2.1 (hgmem b.1 b.2.1)
      have hcent : ¬ Subgroup.zpowers (g b.1 b.2.1) ≤ Subgroup.centralizer (N : Set G) := by
        rw [hg b.1 b.2.1]
        exact b.2.2.2
      have := cmp_conj_inj hp hN hdisj hgH hcent n.2 n'.2 hmem
      have hn : n = n' := Subtype.ext this
      rw [hn]
  have hle := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_sum, Nat.card_sum, Nat.card_prod, hN] at hle
  unfold cyc
  linarith
end part4


section main

theorem main_natcard_split {α : Type*} [Finite α] (Q P : α → Prop) :
    Nat.card {x // Q x} = Nat.card {x // Q x ∧ P x} + Nat.card {x // Q x ∧ ¬ P x} := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype,
    ← Finset.card_filter_add_card_filter_not (s := univ.filter Q) P,
    Finset.filter_filter, Finset.filter_filter]

theorem main_card_divisors_sqf {m : ℕ} (hm : Squarefree m) :
    m.divisors.card = 2 ^ m.primeFactors.card := by
  have hm0 : m ≠ 0 := hm.ne_zero
  rw [Nat.card_divisors hm0]
  rw [Finset.prod_congr rfl (g := fun _ => 2)]
  · simp
  · intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    rw [Nat.factorization_eq_one_of_squarefree hm hqp hqd]

theorem main_numPF_le_one_nilpotent (G : Type*) [Group G] [Fintype G]
    (h : numPrimeFactors G ≤ 1) : Group.IsNilpotent G := by
  unfold numPrimeFactors at h
  have hn0 : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  obtain ⟨p, hp, hpu⟩ : ∃ p : ℕ, p.Prime ∧ ∀ {d : ℕ}, d.Prime → d ∣ Fintype.card G → d = p := by
    rcases Finset.card_le_one_iff_subset_singleton.mp h with ⟨q, hq⟩
    by_cases hqp : q.Prime
    · refine ⟨q, hqp, fun hd hdn => ?_⟩
      have : _ ∈ (Fintype.card G).primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdn, hn0⟩
      simpa using hq this
    · refine ⟨2, Nat.prime_two, fun hd hdn => ?_⟩
      have : _ ∈ (Fintype.card G).primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdn, hn0⟩
      have := hq this
      simp at this
      exact absurd (this ▸ hd) hqp
  have hcard := Nat.eq_prime_pow_of_unique_prime_dvd hn0 hpu
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G := IsPGroup.of_card (n := (Fintype.card G).primeFactorsList.length)
    (by rw [Nat.card_eq_fintype_card]; exact hcard)
  exact hpg.isNilpotent

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem main_richard : (Fintype.card G).divisors.card ≤ cyc G := by
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have key := richard_arith (Fintype.card G) hpos
    (fun e => ((univ.filter fun x : G => orderOf x = e).card : ℚ)) (by
      intro d hd
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      rw [← Nat.cast_sum, sum_card_orderOf_eq_card_pow_eq_one hd0]
      have hdv := frobenius (G := G) (Nat.dvd_of_mem_divisors hd)
      have hpos' : 0 < (univ.filter fun x : G => x ^ d = 1).card :=
        Finset.card_pos.mpr ⟨1, by simp⟩
      exact_mod_cast Nat.le_of_dvd hpos' hdv)
  have hsum : ∑ e ∈ (Fintype.card G).divisors,
      ((univ.filter fun x : G => orderOf x = e).card : ℚ) / (e.totient : ℚ)
        = ∑ x : G, 1 / ((orderOf x).totient : ℚ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := orderOf) (t := (Fintype.card G).divisors)
      (fun x _ => Nat.mem_divisors.mpr ⟨orderOf_dvd_card, Fintype.card_ne_zero⟩)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => 1 / (e.totient : ℚ))]
    · rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_one_div]
    · intro x hx
      rw [(Finset.mem_filter.mp hx).2]
  have := key.trans (le_of_eq (hsum.trans (cyc_eq_sum G).symm))
  exact_mod_cast this

theorem main_eq_of_card_eq {H D D' : Subgroup G} [IsCyclic H] (hD : D ≤ H) (hD' : D' ≤ H)
    (h : Nat.card D = Nat.card D') : D = D' := by
  classical
  set k := Nat.card D with hk
  have hk0 : 0 < k := Nat.card_pos
  have hle := IsCyclic.card_pow_eq_one_le (α := H) hk0
  set S : Finset H := univ.filter fun y : H => y ^ k = 1 with hS
  have key : ∀ E : Subgroup G, E ≤ H → Nat.card E = k →
      ((E.subgroupOf H : Set H)).toFinset = S := by
    intro E hE hEk
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      have : ((y : G)) ^ k = 1 := by
        have := pow_card_eq_one' (G := E) (x := ⟨(y : G), hy⟩)
        rw [hEk] at this
        exact congrArg Subtype.val this
      simpa using this
    · refine hle.trans (le_of_eq ?_)
      rw [Set.toFinset_card, ← hEk]
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv).symm
  have h1 := key D hD rfl
  have h2 := key D' hD' h.symm
  have h3 : D.subgroupOf H = D'.subgroupOf H := by
    apply SetLike.coe_injective
    have := h1.trans h2.symm
    exact Set.toFinset_inj.mp this
  rw [← Subgroup.map_subgroupOf_eq_of_le hD, ← Subgroup.map_subgroupOf_eq_of_le hD', h3]

theorem main_cyc_subgroup (H : Subgroup G) :
    cyc H = Nat.card {D : Subgroup G // IsCyclic D ∧ D ≤ H} := by
  unfold cyc
  apply Nat.card_congr
  refine
    { toFun := fun K => ⟨K.1.map H.subtype, ?_, ?_⟩
      invFun := fun D => ⟨D.1.subgroupOf H, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · haveI := K.2
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective K.1 H.subtype H.subtype_injective)).mp
      inferInstance
  · exact Subgroup.map_le_iff_le_comap.mpr (fun x _ => x.2)
  · haveI := D.2.1
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe D.2.2)).mpr inferInstance
  · intro K
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective K.1
  · intro D
    apply Subtype.ext
    exact Subgroup.map_subgroupOf_eq_of_le D.2.2

theorem main_two_le_numPF {X : Type*} [Group X] [Fintype X] (h : ¬ Group.IsNilpotent X) :
    2 ≤ numPrimeFactors X := by
  by_contra hc
  exact h (main_numPF_le_one_nilpotent X (by omega))

theorem main_p_ne_two {p : ℕ} {N D : Subgroup G} [hNn : N.Normal] (hN : Nat.card N = p)
    (hD : ¬ D ≤ Subgroup.centralizer (N : Set G)) : p ≠ 2 := by
  rintro rfl
  apply hD
  intro d _
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  by_cases hm1 : m = 1
  · simp [hm1]
  have hc : d * m * d⁻¹ ∈ N := hNn.conj_mem m hm d
  obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (⟨1, N.one_mem⟩ : N)).mp hN
  have e1 : (⟨m, hm⟩ : N) = y := hy _ (by
    intro h; apply hm1; exact congrArg Subtype.val h)
  have e2 : (⟨d * m * d⁻¹, hc⟩ : N) = y := hy _ (by
    intro h
    apply hm1
    have h' : d * m * d⁻¹ = 1 := congrArg Subtype.val h
    have : d * m = d := by
      calc d * m = d * m * d⁻¹ * d := by group
        _ = d := by rw [h', one_mul]
    simpa using this)
  have : d * m * d⁻¹ = m := by
    have := e2.trans e1.symm
    exact congrArg Subtype.val this
  calc m * d = d * m * d⁻¹ * d := by rw [this]
    _ = d * m := by group

theorem main_sqf (n : ℕ) : ∀ (G : Type u) [Group G] [Fintype G], Fintype.card G = n →
    Squarefree (Fintype.card G) → ¬ Group.IsNilpotent G →
      5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hsq hnil
  classical
  have ht := main_two_le_numPF hnil
  have hn1 : 1 < Fintype.card G := by
    by_contra hc
    apply hnil
    apply main_numPF_le_one_nilpotent
    unfold numPrimeFactors
    have : Fintype.card G ≤ 1 := by omega
    interval_cases h : Fintype.card G
    · exact absurd h Fintype.card_ne_zero
    · simp
  obtain ⟨p, N, hp, hNn, hNc⟩ := exists_normal_prime_subgroup hsq hn1
  haveI := hNn
  haveI : Fact p.Prime := ⟨hp⟩
  have hGc : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
  have hmul := N.card_mul_index
  rw [hNc] at hmul
  have hsq' : Squarefree (p * N.index) := by rw [hmul, hGc]; exact hsq
  have hcop : (Nat.card N).Coprime N.index := by
    rw [hNc]; exact (Nat.squarefree_mul_iff.mp hsq').1
  obtain ⟨H, hNH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcardH := hNH.card_mul_card
  rw [hNc] at hcardH
  have hHc : Fintype.card H = Nat.card H := Nat.card_eq_fintype_card.symm
  have hsqH : Squarefree (Fintype.card H) := by
    rw [hHc]; have := hsq; rw [← hGc, ← hcardH] at this; exact this.of_mul_right
  have hpH : ¬ p ∣ Nat.card H := by
    have := hsq; rw [← hGc, ← hcardH] at this
    exact (hp.coprime_iff_not_dvd).mp (Nat.squarefree_mul_iff.mp this).1
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have htH : numPrimeFactors H + 1 = numPrimeFactors G := by
    unfold numPrimeFactors
    rw [hHc, ← hGc, ← hcardH, Nat.Coprime.primeFactors_mul
      ((hp.coprime_iff_not_dvd).mpr hpH), hp.primeFactors]
    rw [Finset.card_union_of_disjoint]
    · simp [add_comm]
    · rw [Finset.disjoint_singleton_left]
      intro hm
      exact hpH (Nat.dvd_of_mem_primeFactors hm)
  have hlt : Fintype.card H < n := by
    rw [← hn, ← hGc, ← hcardH, hHc]
    have := hp.two_le
    have : 0 < Nat.card H := Nat.pos_of_ne_zero hH0
    nlinarith
  have hcount := cyc_ge_of_complement hp hNc hNH
  have hsplit := main_natcard_split (fun D : Subgroup G => IsCyclic D ∧ D ≤ H)
    (fun D => D ≤ Subgroup.centralizer (N : Set G))
  simp only [and_assoc] at hsplit
  rw [← main_cyc_subgroup H] at hsplit
  set A := Nat.card {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧ D ≤ Subgroup.centralizer (N : Set G)}
  set B := Nat.card {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧ ¬ D ≤ Subgroup.centralizer (N : Set G)}
  have hp2 := hp.two_le
  by_cases hHn : Group.IsNilpotent H
  · by_cases hB : B = 0
    · exfalso
      apply hnil
      have hcent : H ≤ Subgroup.centralizer (N : Set G) := by
        intro h hh
        by_contra hc
        have hmem : IsCyclic (Subgroup.zpowers h) ∧ Subgroup.zpowers h ≤ H ∧
            ¬ Subgroup.zpowers h ≤ Subgroup.centralizer (N : Set G) :=
          ⟨inferInstance, Subgroup.zpowers_le.mpr hh, fun hz => hc (hz (Subgroup.mem_zpowers h))⟩
        have : 0 < B := by
          haveI : Nonempty {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧
            ¬ D ≤ Subgroup.centralizer (N : Set G)} := ⟨⟨_, hmem⟩⟩
          exact Nat.card_pos
        omega
      haveI : IsCyclic N := isCyclic_of_prime_card hNc
      have hNcomm : ∀ a b : N, a * b = b * a := fun a b => by
        letI := IsCyclic.commGroup (α := N)
        exact mul_comm a b
      have hNcen : N ≤ Subgroup.center G := by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ (H ⊔ N : Subgroup G) := by
          rw [sup_comm, hNH.sup_eq_top]; exact Subgroup.mem_top g
        rw [← SetLike.mem_coe, Subgroup.mul_normal H N] at hg
        obtain ⟨h, hh, m, hm, rfl⟩ := hg
        have h1 : h * x = x * h := by
          have := (Subgroup.mem_centralizer_iff.mp (hcent hh)) x hx
          exact this.symm
        have h2 : m * x = x * m := by
          have := hNcomm ⟨m, hm⟩ ⟨x, hx⟩
          exact congrArg Subtype.val this
        calc h * m * x = h * (m * x) := by group
          _ = h * (x * m) := by rw [h2]
          _ = (h * x) * m := by group
          _ = (x * h) * m := by rw [h1]
          _ = x * (h * m) := by group
      haveI : Group.IsNilpotent (G ⧸ N) := by
        apply Group.nilpotent_of_surjective ((QuotientGroup.mk' N).comp H.subtype)
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
        have hg : g ∈ (H ⊔ N : Subgroup G) := by
          rw [sup_comm, hNH.sup_eq_top]; exact Subgroup.mem_top g
        rw [← SetLike.mem_coe, Subgroup.mul_normal H N] at hg
        obtain ⟨h, hh, m, hm, rfl⟩ := hg
        refine ⟨⟨h, hh⟩, ?_⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply]
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).mpr hm, mul_one]
      exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N)
        (by rw [QuotientGroup.ker_mk']; exact hNcen)
    · -- nontrivial action, H nilpotent
      obtain ⟨⟨D0, hD0c, hD0H, hD0n⟩⟩ : Nonempty {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧
          ¬ D ≤ Subgroup.centralizer (N : Set G)} := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        exact hB (Nat.card_of_isEmpty)
      have hp3 : 3 ≤ p := by
        have := main_p_ne_two hNc hD0n
        omega
      haveI : IsCyclic H := isCyclic_of_nilpotent_squarefree hsqH
      have hRich : 2 ^ numPrimeFactors H ≤ cyc H := by
        have := main_richard (G := H)
        rw [main_card_divisors_sqf hsqH] at this
        exact this
      set K := H ⊓ Subgroup.centralizer (N : Set G) with hK
      have hKH : K ≤ H := inf_le_left
      have hKne : Nat.card K ≠ Nat.card H := by
        intro hc
        have : K = H := Subgroup.eq_of_le_of_card_ge hKH (le_of_eq hc.symm)
        apply hD0n
        exact hD0H.trans (this ▸ inf_le_right)
      have hKdvd : Nat.card K ∣ Nat.card H := Subgroup.card_dvd_of_le hKH
      have hsqK : Squarefree (Nat.card K) := by
        rw [← hHc] at hKdvd; exact Squarefree.squarefree_of_dvd hKdvd hsqH
      have hpfK : (Nat.card K).primeFactors.card + 1 ≤ numPrimeFactors H := by
        unfold numPrimeFactors
        rw [hHc]
        have hsub : (Nat.card K).primeFactors ⊆ (Nat.card H).primeFactors :=
          Nat.primeFactors_mono hKdvd hH0
        have hne : (Nat.card K).primeFactors ≠ (Nat.card H).primeFactors := by
          intro he
          apply hKne
          rw [← Nat.prod_primeFactors_of_squarefree hsqK, he,
            Nat.prod_primeFactors_of_squarefree (hHc ▸ hsqH)]
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
        omega
      have hA : A ≤ 2 ^ (numPrimeFactors H - 1) := by
        have hinj : Function.Injective (fun D : {D : Subgroup G // IsCyclic D ∧ D ≤ H ∧
            D ≤ Subgroup.centralizer (N : Set G)} =>
            (⟨Nat.card D.1, Nat.mem_divisors.mpr ⟨Subgroup.card_dvd_of_le
              (le_inf D.2.2.1 D.2.2.2), Nat.card_pos.ne'⟩⟩ : (Nat.card K).divisors)) := by
          intro D1 D2 h12
          apply Subtype.ext
          exact main_eq_of_card_eq D1.2.2.1 D2.2.2.1 (congrArg Subtype.val h12)
        have := Nat.card_le_card_of_injective _ hinj
        rw [Nat.card_eq_fintype_card (α := (Nat.card K).divisors), Fintype.card_coe,
          main_card_divisors_sqf hsqK] at this
        exact this.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hpB : 3 * B ≤ p * B := Nat.mul_le_mul_right B hp3
      obtain ⟨k, hk⟩ : ∃ k, numPrimeFactors H = k + 1 := ⟨numPrimeFactors H - 1, by omega⟩
      have e1 : numPrimeFactors G - 2 = k := by omega
      rw [e1]
      rw [hk, Nat.add_sub_cancel] at hA
      rw [hk, pow_succ] at hRich
      nlinarith
  · have hrec := ih (Fintype.card H) hlt H rfl hsqH hHn
    have htH2 := main_two_le_numPF hHn
    obtain ⟨k, hk⟩ : ∃ k, numPrimeFactors H = k + 2 := ⟨numPrimeFactors H - 2, by omega⟩
    rw [← htH]
    have e1 : numPrimeFactors H + 1 - 2 = k + 1 := by omega
    rw [e1, pow_succ]
    rw [hk, Nat.add_sub_cancel] at hrec
    have hpB : 2 * B ≤ p * B := Nat.mul_le_mul_right B hp2
    nlinarith

theorem main_target (G : Type u) [Group G] [Fintype G]
    (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) : Group.IsNilpotent G := by
  classical
  by_contra hnil
  by_cases hsq : Squarefree (Fintype.card G)
  · exact absurd h (not_lt.mpr (main_sqf _ G rfl hsq hnil))
  · have ht := main_two_le_numPF hnil
    have hR := main_richard (G := G)
    have hn0 : Fintype.card G ≠ 0 := Fintype.card_ne_zero
    obtain ⟨q, hq, hqq⟩ : ∃ q, q.Prime ∧ q * q ∣ Fintype.card G := by
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push_neg at hsq
      exact hsq
    have hf : 2 ≤ (Fintype.card G).factorization q :=
      (hq.pow_dvd_iff_le_factorization hn0).mp (by rwa [sq])
    have hqm : q ∈ (Fintype.card G).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, dvd_trans (dvd_mul_right q q) hqq, hn0⟩
    rw [Nat.card_divisors hn0, ← Finset.mul_prod_erase _ _ hqm] at hR
    have hprod : 2 ^ ((Fintype.card G).primeFactors.erase q).card ≤
        ∏ x ∈ (Fintype.card G).primeFactors.erase q, ((Fintype.card G).factorization x + 1) := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod'
      intro x hx
      have hxm := Finset.mem_of_mem_erase hx
      have := (Nat.prime_of_mem_primeFactors hxm).factorization_pos_of_dvd hn0
        (Nat.dvd_of_mem_primeFactors hxm)
      omega
    have hcard : ((Fintype.card G).primeFactors.erase q).card + 1 = numPrimeFactors G := by
      unfold numPrimeFactors
      exact Finset.card_erase_add_one hqm
    obtain ⟨k, hk⟩ : ∃ k, numPrimeFactors G = k + 2 := ⟨numPrimeFactors G - 2, by omega⟩
    rw [hk] at hcard h
    simp only [Nat.add_sub_cancel] at h
    have hk1 : ((Fintype.card G).primeFactors.erase q).card = k + 1 := by omega
    rw [hk1, pow_succ] at hprod
    have h3 : 3 * (2 ^ k * 2) ≤ ((Fintype.card G).factorization q + 1) *
        ∏ x ∈ (Fintype.card G).primeFactors.erase q, ((Fintype.card G).factorization x + 1) :=
      Nat.mul_le_mul (by omega) hprod
    have := h3.trans hR
    omega

end main

end OMA.Cyc

theorem OMA.solution : type_of% @Arxiv.«2604.08040».nilpotent_of_cyc_lt := by
  intro G _ _ h
  exact OMA.Cyc.main_target G h
