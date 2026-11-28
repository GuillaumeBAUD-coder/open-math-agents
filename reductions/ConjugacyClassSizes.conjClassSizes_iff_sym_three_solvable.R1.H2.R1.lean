import OMAReductions.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1

/-!
# Arithmetic and Sylow reduction for anti-homogeneous `{2, 3, 5}`-groups

For any nontrivial finite group `G` with `HasDistinctConjClassSizes G` and prime divisors
contained in `{2, 3, 5}`, we prove completely (without assuming solvability):
* `2 ∣ |G|` (from `IsConj x x⁻¹` for any non-involution);
* `|G|` is not a prime power (from trivial center vs. nontrivial center of a `p`-group);
* `5 ∣ |G| → 4 ∣ |G|` (an element `x` of order `5` satisfies `IsConj x (x ^ 2)`, forcing
  an element whose order is a multiple of `4`);
* if `p ^ 2 ∣ |G|`, no conjugacy class has size `|G| / p` (by the Sylow `p`-subgroup center);
* no `{2, 5}`-group exists (`σ(2^a 5^c) - |G| - |G|/2 < |G|`);
* among `{2, 3}`-groups, the cases `a = 1, b ≥ 2`, `a ∈ {2, 3}, b ≥ 2`, and `a ≥ 2, b = 1`
  (where `|G|/3` and `|G|/6` cannot both occur by conjugacy of Sylow `3`-subgroups) are all
  impossible, leaving only `|G| = 6` or the two residual regimes `H1` (`16 ∣ |G| ∧ 9 ∣ |G| ∧ 5 ∤ |G|`)
  and `H2` (`4 ∣ |G| ∧ 3 ∣ |G| ∧ 5 ∣ |G|`).
-/

-- Credit: @lettucrisp

namespace OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H2_R1

open ConjugacyClassSizes ConjClasses Subgroup Finset
open scoped Classical Pointwise

/-- Residual `{2, 3}`-case: `|G| = 2^a 3^b` with `a ≥ 4` and `b ≥ 2`. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G],
    (∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3) →
    16 ∣ Nat.card G → 9 ∣ Nat.card G →
    HasDistinctConjClassSizes G → False

/-- Residual `{2, 3, 5}`-case: `|G| = 2^a 3^b 5^c` with `a ≥ 2`, `b ≥ 1`, `c ≥ 1`. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G],
    (∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3 ∨ p = 5) →
    4 ∣ Nat.card G → 3 ∣ Nat.card G → 5 ∣ Nat.card G →
    HasDistinctConjClassSizes G → False

lemma conjClassCard_mul_centralizer {G : Type*} [Group G] [Fintype G] (x : G) :
    conjClassCard (ConjClasses.mk x) * Nat.card (Subgroup.centralizer {x}) = Nat.card G := by
  have horb : (ConjClasses.mk x).carrier = MulAction.orbit (ConjAct G) x := by
    ext y
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, MulAction.mem_orbit_iff]
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := isConj_iff.mp hy
      refine ⟨ConjAct.toConjAct g⁻¹, ?_⟩
      rw [ConjAct.smul_def]
      change g⁻¹ * x * (g⁻¹)⁻¹ = y
      rw [← hg]; group
    · rintro ⟨g, rfl⟩
      rw [ConjAct.smul_def]
      refine isConj_iff.mpr ⟨(ConjAct.ofConjAct g)⁻¹, ?_⟩
      group
  have hstab : Nat.card (MulAction.stabilizer (ConjAct G) x) = Nat.card (Subgroup.centralizer {x}) := by
    apply Nat.card_congr
    refine
      { toFun := fun ⟨g, hg⟩ => ⟨ConjAct.ofConjAct g, ?_⟩
        invFun := fun ⟨g, hg⟩ => ⟨ConjAct.toConjAct g, ?_⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def] at hg
      calc ConjAct.ofConjAct g * x = (ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹) * ConjAct.ofConjAct g := by group
        _ = x * ConjAct.ofConjAct g := by rw [hg]
    · rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def]
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      change g * x * g⁻¹ = x
      calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hg]
        _ = x := by group
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hos
  have hcardG : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [conjClassCard, horb, ← hstab, hos, hcardG]

lemma conjClassCard_dvd_card {G : Type*} [Group G] [Fintype G] (c : ConjClasses G) :
    conjClassCard c ∣ Nat.card G := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  exact ⟨Nat.card (Subgroup.centralizer {x}), (conjClassCard_mul_centralizer x).symm⟩

lemma conjClassCard_pos {G : Type*} [Group G] [Fintype G] (c : ConjClasses G) :
    0 < conjClassCard c := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  have hmul := conjClassCard_mul_centralizer x
  have hG : 0 < Nat.card G := Nat.card_pos
  exact Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hmul; omega

lemma centralizer_one_eq_top {G : Type*} [Group G] :
    Subgroup.centralizer ({1} : Set G) = ⊤ := by
  ext g; simp [Subgroup.mem_centralizer_singleton_iff]

lemma orderOf_dvd_card_of_mem {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) {z : G} (hz : z ∈ H) : orderOf z ∣ Nat.card H := by
  have h1 : orderOf (⟨z, hz⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard (⟨z, hz⟩ : H)
  rwa [Subgroup.orderOf_mk] at h1

lemma sum_conjClassCard_eq_card {G : Type*} [Group G] [Fintype G] :
    ∑ c : ConjClasses G, conjClassCard c = Nat.card G := by
  have hpart : (∑ c : ConjClasses G, (Finset.univ.filter (fun x : G => ConjClasses.mk x = c)).card) =
      Fintype.card G := by
    rw [← Finset.card_biUnion]
    · congr 1; ext x; simp
    · intro a _ b _ hab
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro x ha hb
      exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  rw [Nat.card_eq_fintype_card, ← hpart]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [conjClassCard, Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1; ext x
  simp [ConjClasses.mem_carrier_iff_mk_eq]

lemma sum_le_divisors_sdiff {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (S : Finset ℕ)
    (hS_dvd : ∀ s ∈ S, s ∣ Nat.card G)
    (hS_miss : ∀ s ∈ S, ∀ c : ConjClasses G, conjClassCard c ≠ s) :
    Nat.card G + ∑ s ∈ S, s ≤ ∑ d ∈ (Nat.card G).divisors, d := by
  let I : Finset ℕ := Finset.univ.image (conjClassCard (G := G))
  have hI_sum : ∑ d ∈ I, d = Nat.card G := by
    rw [Finset.sum_image (fun a _ b _ hab => h hab), sum_conjClassCard_eq_card]
  have hdisj : Disjoint I S := by
    rw [Finset.disjoint_left]
    intro d hdI hdS
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hdI
    exact hS_miss _ hdS c rfl
  have hsub : I ∪ S ⊆ (Nat.card G).divisors := by
    intro d hd
    rw [Nat.mem_divisors]
    refine ⟨?_, Nat.card_pos.ne'⟩
    rcases Finset.mem_union.mp hd with hdI | hdS
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hdI
      exact conjClassCard_dvd_card c
    · exact hS_dvd d hdS
  calc Nat.card G + ∑ s ∈ S, s
      = (∑ d ∈ I, d) + ∑ s ∈ S, s := by rw [hI_sum]
    _ = ∑ d ∈ I ∪ S, d := (Finset.sum_union hdisj).symm
    _ ≤ ∑ d ∈ (Nat.card G).divisors, d := Finset.sum_le_sum_of_subset hsub

lemma conjClassCard_ne_card {G : Type*} [Group G] [Fintype G] [Nontrivial G] (c : ConjClasses G) :
    conjClassCard c ≠ Nat.card G := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  have hmul := conjClassCard_mul_centralizer x
  have hG2 : 2 ≤ Nat.card G := Fintype.one_lt_card.trans_eq Nat.card_eq_fintype_card.symm
  by_cases hx : x = 1
  · subst hx
    have hcent : Nat.card (Subgroup.centralizer ({1} : Set G)) = Nat.card G := by
      rw [centralizer_one_eq_top]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hcent] at hmul
    intro heq; rw [heq] at hmul; nlinarith
  · have hcent2 : 2 ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      have h1 : (1 : G) ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.one_mem _
      have hxmem : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have hne : (⟨1, h1⟩ : Subgroup.centralizer ({x} : Set G)) ≠ ⟨x, hxmem⟩ :=
        fun he => hx (congrArg Subtype.val he).symm
      have : Nontrivial (Subgroup.centralizer ({x} : Set G)) := ⟨⟨⟨1, h1⟩, ⟨x, hxmem⟩, hne⟩⟩
      exact Fintype.one_lt_card.trans_eq Nat.card_eq_fintype_card.symm
    have hpos := conjClassCard_pos (ConjClasses.mk x)
    intro heq; rw [heq] at hmul; nlinarith

lemma centralizer_inv_eq {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor <;> intro h
  · calc g * x = x * (x⁻¹ * g) * x := by group
      _ = x * (g * x⁻¹) * x := by rw [← h]
      _ = x * g := by group
  · calc g * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by group
      _ = x⁻¹ * (g * x) * x⁻¹ := by rw [← h]
      _ = x⁻¹ * g := by group

lemma isConj_inv_of_distinct {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (x : G) : IsConj x x⁻¹ := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  apply h
  have h1 := conjClassCard_mul_centralizer x
  have h2 := conjClassCard_mul_centralizer x⁻¹
  rw [centralizer_inv_eq] at h2
  have hpos : 0 < Nat.card (Subgroup.centralizer ({x} : Set G)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

lemma even_card_of_distinct {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) : 2 ∣ Nat.card G := by
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  by_cases hinv : x = x⁻¹
  · have hord : orderOf x = 2 := by
      have hx2 : x ^ 2 = 1 := by
        calc x ^ 2 = x * x := sq x
          _ = x * x⁻¹ := by rw [← hinv]
          _ = 1 := mul_inv_cancel x
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      have hne1 : orderOf x ≠ 1 := fun h1 => hx (orderOf_eq_one_iff.mp h1)
      have hle := Nat.le_of_dvd (by omega) hdvd
      have hpos : 0 < orderOf x := orderOf_pos x
      omega
    rw [← hord]
    exact orderOf_dvd_natCard x
  · obtain ⟨g, hconj⟩ := isConj_iff.mp (isConj_inv_of_distinct h x)
    have hconj_pow : ∀ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = if Even k then x else x⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hstep : g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
        rw [hstep, ih]
        by_cases hk : Even k
        · have hodd : ¬ Even (k + 1) := by obtain ⟨m, rfl⟩ := hk; intro ⟨r, hr⟩; omega
          simp only [hk, ↓reduceIte, hodd, hconj]
        · have hev : Even (k + 1) := by
            rcases Nat.even_or_odd k with h1 | ⟨m, rfl⟩
            · exact absurd h1 hk
            · exact ⟨m + 1, by omega⟩
          simp only [hk, ↓reduceIte, hev]
          calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
            _ = (x⁻¹)⁻¹ := by rw [hconj]
            _ = x := inv_inv x
    have hord_even : 2 ∣ orderOf g := by
      have heq := hconj_pow (orderOf g)
      rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at heq
      by_cases hev : Even (orderOf g)
      · obtain ⟨m, hm⟩ := hev; exact ⟨m, by omega⟩
      · simp only [hev, ↓reduceIte] at heq
        exact absurd heq hinv
    exact hord_even.trans (orderOf_dvd_natCard g)

lemma four_dvd_of_five_dvd {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (h5 : 5 ∣ Nat.card G) : 4 ∣ Nat.card G := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 h5
  have hcent : Subgroup.centralizer ({x ^ 2} : Set G) = Subgroup.centralizer ({x} : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h2
      have hx_eq : x = (x ^ 2) ^ 3 := by
        rw [← pow_mul, show 2 * 3 = 5 + 1 by omega, pow_succ, ← hx5, pow_orderOf_eq_one, one_mul]
      rw [hx_eq]
      exact Commute.pow_right h2 3
    · intro h1
      exact Commute.pow_right h1 2
  have hisc : IsConj x (x ^ 2) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    apply h
    have h1 := conjClassCard_mul_centralizer x
    have h2 := conjClassCard_mul_centralizer (x ^ 2)
    rw [hcent] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  obtain ⟨g, hconj⟩ := isConj_iff.mp hisc
  have hconj_pow : ∀ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = x ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [hstep, ih, ← conj_pow, hconj, ← pow_mul, ← pow_succ']
  have hpow : x ^ (2 ^ orderOf g) = x := by
    have := hconj_pow (orderOf g)
    rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at this
    exact this.symm
  have hmod : 2 ^ orderOf g ≡ 1 [MOD 5] := by
    have h1 : x ^ (2 ^ orderOf g) = x ^ 1 := by simpa using hpow
    rw [pow_eq_pow_iff_modEq, hx5] at h1
    exact h1
  have h4 : 4 ∣ orderOf g := by
    have hrem : (2 ^ (orderOf g % 4)) % 5 = 1 := by
      have hdiv : orderOf g = 4 * (orderOf g / 4) + orderOf g % 4 := (Nat.div_add_mod _ _).symm
      have h24 : 2 ^ 4 ≡ 1 [MOD 5] := by decide
      have hpow4 : (2 ^ 4) ^ (orderOf g / 4) ≡ 1 [MOD 5] := by
        simpa using h24.pow (orderOf g / 4)
      have heq : 2 ^ orderOf g = (2 ^ 4) ^ (orderOf g / 4) * 2 ^ (orderOf g % 4) := by
        rw [← pow_mul, ← pow_add, ← hdiv]
      have hmul : 2 ^ orderOf g ≡ 1 * 2 ^ (orderOf g % 4) [MOD 5] := by
        rw [heq]; exact hpow4.mul_right _
      have htrans := hmod.symm.trans hmul
      simp only [Nat.ModEq, one_mul] at htrans
      exact htrans.symm
    have hlt : orderOf g % 4 < 4 := Nat.mod_lt _ (by omega)
    have hz : orderOf g % 4 = 0 := by
      interval_cases h : orderOf g % 4 <;> simp_all
    exact Nat.dvd_of_mod_eq_zero hz
  exact h4.trans (orderOf_dvd_natCard g)

lemma not_prime_pow_card {G : Type*} [Group G] [Fintype G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) : ¬ IsPrimePow (Nat.card G) := by
  rintro ⟨p, k, hp, hk, hcard⟩
  have hp' : p.Prime := hp.nat_prime
  have : Fact p.Prime := ⟨hp'⟩
  have hpg : IsPGroup p G := IsPGroup.of_card hcard.symm
  have hzn := hpg.center_nontrivial
  rw [trivial_center_of_hasDistinctConjClassSizes h] at hzn
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hzn
  rw [Subgroup.mem_bot] at ha hb
  exact hab (Subtype.ext (ha.trans hb.symm))

lemma prime_sq_dvd_centralizer_of_order {G : Type*} [Group G] [Fintype G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ^ 2 ∣ Nat.card G) {x : G} (hx : orderOf x = p) :
    p ^ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hzx : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨P, hle⟩ := hzx.exists_le_sylow
  have hxP : x ∈ (P : Subgroup G) := hle (Subgroup.mem_zpowers x)
  have hPcard : Nat.card P = p ^ (Nat.card G).factorization p := P.card_eq_multiplicity
  have hfac : 2 ≤ (Nat.card G).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hp2
  have hp2P : p ^ 2 ∣ Nat.card P := by
    rw [hPcard]
    exact Nat.pow_dvd_pow p hfac
  have : Nontrivial P := by
    have hgt : 1 < Fintype.card P := by
      rw [← Nat.card_eq_fintype_card]
      have : p ^ 2 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hp2P
      have := hp.two_le
      nlinarith
    exact Fintype.one_lt_card_iff_nontrivial.mp hgt
  have hZnt : Nontrivial (Subgroup.center P) := P.2.center_nontrivial
  let Q : Subgroup P := (Subgroup.centralizer ({x} : Set G)).comap P.toSubgroup.subtype
  have hQ_dvd_cent : Nat.card Q ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    let f : Q →* Subgroup.centralizer ({x} : Set G) :=
      { toFun := fun ⟨⟨g, _⟩, hgC⟩ => ⟨g, hgC⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      intro ⟨⟨a, _⟩, _⟩ ⟨⟨b, _⟩, _⟩ hab
      have : a = b := congrArg Subtype.val hab
      subst this; rfl
    have hcard_eq : Nat.card Q = Nat.card f.range :=
      Nat.card_congr (Equiv.ofBijective f.rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩)
    rw [hcard_eq]
    exact Subgroup.card_subgroup_dvd_card f.range
  have hQ_pgrp : IsPGroup p Q := by
    intro ⟨a, _⟩
    obtain ⟨k, hk⟩ := P.2 a
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨r, hr⟩ := hQ_pgrp.exists_card_eq
  have hr2 : 2 ≤ r := by
    by_cases hxc : (⟨x, hxP⟩ : P) ∈ Subgroup.center P
    · have htop : Q = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro g
        rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_center_iff.mp hxc g
        exact congrArg Subtype.val this
      have hQP : Nat.card Q = Nat.card P := by
        rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
      rw [hQP, hPcard] at hr
      have := Nat.pow_right_injective hp.two_le hr
      omega
    · have hZleQ : Subgroup.center P ≤ Q := by
        intro z hz
        rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_center_iff.mp hz ⟨x, hxP⟩
        exact congrArg Subtype.val this.symm
      have hxQ : (⟨x, hxP⟩ : P) ∈ Q := by
        rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
      have hcard_lt : Nat.card (Subgroup.center P) < Nat.card Q := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        refine Fintype.card_lt_of_injective_of_notMem (Subgroup.inclusion hZleQ)
          (Subgroup.inclusion_injective hZleQ) (b := ⟨⟨x, hxP⟩, hxQ⟩) ?_
        rintro ⟨⟨z, hz⟩, hzeq⟩
        have hzx_eq : z = ⟨x, hxP⟩ := congrArg Subtype.val hzeq
        exact hxc (hzx_eq ▸ hz)
      have hZcard_ge : p ≤ Nat.card (Subgroup.center P) := by
        have hZp : IsPGroup p (Subgroup.center P) := by
          intro ⟨a, _⟩
          obtain ⟨k, hk⟩ := P.2 a
          exact ⟨k, Subtype.ext hk⟩
        obtain ⟨m, hm⟩ := hZp.exists_card_eq
        have hgt1 : 1 < Nat.card (Subgroup.center P) := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.one_lt_card_iff_nontrivial.mpr hZnt
        have hmpos : 1 ≤ m := by
          by_contra h0
          have hm0 : m = 0 := by omega
          rw [hm0, pow_zero] at hm; omega
        rw [hm]
        exact Nat.le_pow hmpos
      rw [hr] at hcard_lt
      by_contra hlt2
      have : p ^ r ≤ p := by
        rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
        · simp [hp.one_lt.le]
        · simp
      omega
  exact (Nat.pow_dvd_pow p hr2).trans (hr ▸ hQ_dvd_cent)

lemma conjClassCard_ne_div_prime {G : Type*} [Group G] [Fintype G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ^ 2 ∣ Nat.card G) (c : ConjClasses G) :
    conjClassCard c ≠ Nat.card G / p := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  intro heq
  have hmul := conjClassCard_mul_centralizer x
  rw [heq] at hmul
  have hp_dvd : p ∣ Nat.card G := (dvd_pow_self p (by omega : 2 ≠ 0)).trans hp2
  have hdiv_pos : 0 < Nat.card G / p := Nat.div_pos (Nat.le_of_dvd Nat.card_pos hp_dvd) hp.pos
  have hcent : Nat.card (Subgroup.centralizer ({x} : Set G)) = p := by
    have hGeq : Nat.card G / p * p = Nat.card G := Nat.div_mul_cancel hp_dvd
    exact Nat.eq_of_mul_eq_mul_left hdiv_pos (hmul.trans hGeq.symm)
  have hx1 : x ≠ 1 := by
    rintro rfl
    have htop : Nat.card (Subgroup.centralizer ({1} : Set G)) = Nat.card G := by
      rw [centralizer_one_eq_top]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    have hle : p ^ 2 ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hp2
    rw [← htop, hcent] at hle
    have := hp.two_le
    nlinarith
  have hxord : orderOf x = p := by
    have hxmem : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hdvd : orderOf x ∣ p := hcent ▸ orderOf_dvd_card_of_mem _ hxmem
    have hne1 : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
    exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  have hp2_dvd := prime_sq_dvd_centralizer_of_order hp hp2 hxord
  rw [hcent] at hp2_dvd
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hp2_dvd
  have := hp.two_le
  nlinarith

lemma no_div3_and_div6_of_two_pow_mul_three {G : Type*} [Group G] [Fintype G]
    {a : ℕ} (ha : 2 ≤ a) (hcard : Nat.card G = 2 ^ a * 3) :
    ¬ ((∃ c : ConjClasses G, conjClassCard c = Nat.card G / 3) ∧
       (∃ c : ConjClasses G, conjClassCard c = Nat.card G / 6)) := by
  rintro ⟨⟨cx, hcx⟩, ⟨cy, hcy⟩⟩
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective cx
  obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective cy
  have hmulx := conjClassCard_mul_centralizer x
  have hmuly := conjClassCard_mul_centralizer y
  rw [hcx, hcard] at hmulx
  rw [hcy, hcard] at hmuly
  have hdiv3 : 2 ^ a * 3 / 3 = 2 ^ a := Nat.mul_div_cancel _ (by omega)
  have hdiv6 : 2 ^ a * 3 / 6 = 2 ^ (a - 1) := by
    have h2a : 2 ^ a = 2 ^ (a - 1) * 2 := by
      conv_lhs => rw [show a = a - 1 + 1 by omega, pow_succ]
    rw [h2a, mul_assoc, show 2 * 3 = 6 by omega, Nat.mul_div_cancel _ (by omega)]
  rw [hdiv3] at hmulx
  rw [hdiv6] at hmuly
  have h2a_pos : 0 < 2 ^ a := by positivity
  have h2am1_pos : 0 < 2 ^ (a - 1) := by positivity
  have hcentx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 3 :=
    Nat.eq_of_mul_eq_mul_left h2a_pos hmulx
  have hcenty : Nat.card (Subgroup.centralizer ({y} : Set G)) = 6 := by
    have h2a : 2 ^ a * 3 = 2 ^ (a - 1) * 6 := by
      have : 2 ^ a = 2 ^ (a - 1) * 2 := by
        conv_lhs => rw [show a = a - 1 + 1 by omega, pow_succ]
      rw [this]; ring
    rw [h2a] at hmuly
    exact Nat.eq_of_mul_eq_mul_left h2am1_pos hmuly
  have hG12 : 12 ≤ Nat.card G := by
    rw [hcard]
    have : 4 ≤ 2 ^ a := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
    omega
  have hx1 : x ≠ 1 := by
    rintro rfl
    have htop : Nat.card (Subgroup.centralizer ({1} : Set G)) = Nat.card G := by
      rw [centralizer_one_eq_top]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    omega
  have hy1 : y ≠ 1 := by
    rintro rfl
    have htop : Nat.card (Subgroup.centralizer ({1} : Set G)) = Nat.card G := by
      rw [centralizer_one_eq_top]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    omega
  have hxord : orderOf x = 3 := by
    have hxmem : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hdvd : orderOf x ∣ 3 := hcentx ▸ orderOf_dvd_card_of_mem _ hxmem
    have hne1 : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
    exact ((by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  have hyord_dvd : orderOf y ∣ 6 := by
    have hymem : y ∈ Subgroup.centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    exact hcenty ▸ orderOf_dvd_card_of_mem _ hymem
  have hyord_ne1 : orderOf y ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
  have hy_cases : orderOf y = 2 ∨ orderOf y = 3 ∨ orderOf y = 6 := by
    have hle := Nat.le_of_dvd (by omega) hyord_dvd
    have hpos : 0 < orderOf y := orderOf_pos y
    interval_cases h : orderOf y <;> simp_all
  have h4_dvd : 4 ∣ Nat.card G := by
    rw [hcard]
    have : 2 ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
    exact dvd_mul_of_dvd_left this 3
  have hcent3 : ∀ z : G, orderOf z = 3 → Nat.card (Subgroup.centralizer ({z} : Set G)) = 3 := by
    intro z hz
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hfac3 : (Nat.card G).factorization 3 = 1 := by
      rw [hcard, Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
        Nat.Prime.factorization_pow (by decide), Finsupp.single_eq_of_ne (by omega),
        Nat.Prime.factorization_self (by decide), zero_add]
    have hPx : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one])
    have hPz : IsPGroup 3 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
    obtain ⟨Px, hlePx⟩ := hPx.exists_le_sylow
    obtain ⟨Pz, hlePz⟩ := hPz.exists_le_sylow
    have hcardPx : Nat.card Px = 3 := by rw [Px.card_eq_multiplicity, hfac3, pow_one]
    have hcardPz : Nat.card Pz = 3 := by rw [Pz.card_eq_multiplicity, hfac3, pow_one]
    have heqPx : Subgroup.zpowers x = (Px : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hlePx (by rw [hcardPx, Nat.card_zpowers, hxord])
    have heqPz : Subgroup.zpowers z = (Pz : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hlePz (by rw [hcardPz, Nat.card_zpowers, hz])
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Px Pz
    have hz_in : z ∈ ((g • Px : Sylow 3 G) : Subgroup G) := by
      rw [hg, ← heqPz]; exact Subgroup.mem_zpowers z
    have hginv : g⁻¹ * z * g ∈ Subgroup.zpowers x := by
      rw [heqPx]
      have hz_set : z ∈ MulAut.conj g • (Px : Set G) := by
        rw [← Sylow.coe_smul]; exact hz_in
      obtain ⟨w, hw, hgw⟩ := Set.mem_smul_set.mp hz_set
      have hwg : w = g⁻¹ * z * g := by
        change g * w * g⁻¹ = z at hgw
        rw [← hgw]; group
      exact hwg ▸ hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hginv
    have hne0 : g⁻¹ * z * g ≠ 1 := by
      intro h1
      have : z = 1 := by
        calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = g * 1 * g⁻¹ := by rw [h1]
          _ = 1 := by group
      rw [this, orderOf_one] at hz; omega
    have hcent_eq : Subgroup.centralizer ({g⁻¹ * z * g} : Set G) = Subgroup.centralizer ({x} : Set G) := by
      have hkmod : x ^ k = x ∨ x ^ k = x⁻¹ := by
        have hkm := zpow_mod_orderOf x k
        rw [hxord] at hkm
        have hlt : (k % (3 : ℕ)).toNat < 3 := by
          have hnn : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by omega)
          have hltZ : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by omega)
          omega
        have hmod_eq : x ^ k = x ^ (k % (3 : ℕ)).toNat := by
          have hnn : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg k (by omega)
          rw [← hkm, ← zpow_natCast, Int.toNat_of_nonneg hnn]
        rw [hmod_eq]
        interval_cases h : (k % (3 : ℕ)).toNat
        · rw [pow_zero] at hmod_eq
          exact absurd (hk.symm.trans hmod_eq) hne0
        · left; simp
        · right
          calc x ^ 2 = x ^ 3 * x⁻¹ := by group
            _ = 1 * x⁻¹ := by rw [← hxord, pow_orderOf_eq_one]
            _ = x⁻¹ := one_mul _
      rw [← hk]
      rcases hkmod with h1 | h2
      · rw [h1]
      · rw [h2, centralizer_inv_eq]
    have hconj_cent : Nat.card (Subgroup.centralizer ({z} : Set G)) =
        Nat.card (Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) := by
      apply Nat.card_congr
      refine
        { toFun := fun ⟨u, hu⟩ => ⟨g⁻¹ * u * g, ?_⟩
          invFun := fun ⟨u, hu⟩ => ⟨g * u * g⁻¹, ?_⟩
          left_inv := fun ⟨u, _⟩ => Subtype.ext (by group)
          right_inv := fun ⟨u, _⟩ => Subtype.ext (by group) }
      · rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
        calc (g⁻¹ * u * g) * (g⁻¹ * z * g) = g⁻¹ * (u * z) * g := by group
          _ = g⁻¹ * (z * u) * g := by rw [hu]
          _ = (g⁻¹ * z * g) * (g⁻¹ * u * g) := by group
      · rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
        calc (g * u * g⁻¹) * z = g * (u * (g⁻¹ * z * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * z * g) * u) * g⁻¹ := by rw [hu]
          _ = z * (g * u * g⁻¹) := by group
    rw [hconj_cent, hcent_eq, hcentx]
  rcases hy_cases with hy2 | hy3 | hy6
  · have h4y := prime_sq_dvd_centralizer_of_order (by decide : Nat.Prime 2) h4_dvd hy2
    rw [hcenty] at h4y
    norm_num at h4y
  · have := hcent3 y hy3
    omega
  · have hy2_ord : orderOf (y ^ 2) = 3 := by
      rw [orderOf_pow, hy6]
      norm_num
    have hcy2 := hcent3 (y ^ 2) hy2_ord
    have hy_in : y ∈ Subgroup.centralizer ({y ^ 2} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.refl y).pow_right 2
    have h6dvd3 : 6 ∣ 3 := by
      have h1 : orderOf y ∣ 3 := hcy2 ▸ orderOf_dvd_card_of_mem _ hy_in
      rwa [hy6] at h1
    norm_num at h6dvd3

lemma sum_divisors_mul_coprime {m n : ℕ} (h : m.Coprime n) :
    (∑ d ∈ (m * n).divisors, d) = (∑ d ∈ m.divisors, d) * (∑ d ∈ n.divisors, d) := by
  have h1 := ArithmeticFunction.isMultiplicative_sigma (k := 1) |>.map_mul_of_coprime h
  simpa [ArithmeticFunction.sigma_apply] using h1

lemma sum_divisors_two_pow (a : ℕ) : ∑ d ∈ (2 ^ a).divisors, d = 2 ^ (a + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 2)]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ih]
    have hpos : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    have hpow : 2 ^ (a + 1 + 1) = 2 ^ (a + 1) + 2 ^ (a + 1) := by rw [pow_succ]; ring
    omega

lemma sum_divisors_three_pow (b : ℕ) : 2 * (∑ d ∈ (3 ^ b).divisors, d) = 3 ^ (b + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 3)]
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hpos : 1 ≤ 3 ^ (b + 1) := Nat.one_le_pow _ _ (by omega)
    have hpow : 3 ^ (b + 1 + 1) = 3 ^ (b + 1) + 2 * 3 ^ (b + 1) := by rw [pow_succ]; ring
    omega

lemma sum_divisors_five_pow (c : ℕ) : 4 * (∑ d ∈ (5 ^ c).divisors, d) = 5 ^ (c + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 5)]
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hpos : 1 ≤ 5 ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
    have hpow : 5 ^ (c + 1 + 1) = 5 ^ (c + 1) + 4 * 5 ^ (c + 1) := by rw [pow_succ]; ring
    omega

lemma eq_two_three_five_pow {n : ℕ} (hn : n ≠ 0)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3 ∨ p = 5) :
    ∃ a b c : ℕ, n = 2 ^ a * 3 ^ b * 5 ^ c := by
  refine ⟨n.factorization 2, n.factorization 3, n.factorization 5, ?_⟩
  have hprod := Nat.prod_factorization_pow_eq_self hn
  have hsub : n.factorization.support ⊆ ({2, 3, 5} : Finset ℕ) := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rcases hprimes p hp.1 hp.2.1 with rfl | rfl | rfl <;> simp
  have hfin : (∏ p ∈ n.factorization.support, p ^ n.factorization p) =
      ∏ p ∈ ({2, 3, 5} : Finset ℕ), p ^ n.factorization p := by
    refine Finset.prod_subset hsub fun p _ hp => ?_
    have h0 : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [h0]
  calc n = ∏ p ∈ n.factorization.support, p ^ n.factorization p := hprod.symm
    _ = ∏ p ∈ ({2, 3, 5} : Finset ℕ), p ^ n.factorization p := hfin
    _ = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 5 ^ n.factorization 5 := by
          rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton, mul_assoc]

theorem main : H1 → H2 → OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1.H2 := by
  intro h23 h235 G _ _ _ hprimes hdist
  have hne0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, b, c, hcard⟩ := eq_two_three_five_pow hne0 hprimes
  have h2dvd : 2 ∣ Nat.card G := even_card_of_distinct hdist
  have ha1 : 1 ≤ a := by
    by_contra ha0
    have haeq : a = 0 := by omega
    rw [haeq, pow_zero, one_mul] at hcard
    rw [hcard] at h2dvd
    have hcop : Nat.Coprime 2 (3 ^ b * 5 ^ c) :=
      (Nat.Coprime.pow_right b (by decide)).mul_right (Nat.Coprime.pow_right c (by decide))
    have hd1 : 2 ∣ 1 := by
      have := Nat.dvd_gcd dvd_rfl h2dvd
      rwa [hcop.gcd_eq_one] at this
    omega
  -- Case 1: c ≥ 1 (5 ∣ |G|)
  by_cases hc : 1 ≤ c
  · have h5dvd : 5 ∣ Nat.card G := by
      rw [hcard]
      exact dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _
    have h4dvd : 4 ∣ Nat.card G := four_dvd_of_five_dvd hdist h5dvd
    have ha2 : 2 ≤ a := by
      by_contra hlt
      have haeq : a = 1 := by omega
      rw [haeq, pow_one] at hcard
      rw [hcard] at h4dvd
      have h2div : 2 ∣ 3 ^ b * 5 ^ c := by
        obtain ⟨k, hk⟩ := h4dvd
        rw [mul_assoc] at hk
        exact ⟨k, by omega⟩
      have hcop : Nat.Coprime 2 (3 ^ b * 5 ^ c) :=
        (Nat.Coprime.pow_right b (by decide)).mul_right (Nat.Coprime.pow_right c (by decide))
      have hd1 : 2 ∣ 1 := by
        have := Nat.dvd_gcd dvd_rfl h2div
        rwa [hcop.gcd_eq_one] at this
      omega
    by_cases hb : 1 ≤ b
    · have h3dvd : 3 ∣ Nat.card G := by
        rw [hcard]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) _) _
      exact False.elim (h235 G hprimes h4dvd h3dvd h5dvd hdist)
    · -- {2, 5}-group: b = 0, a ≥ 2, c ≥ 1 -> impossible by divisor-sum bound
      exfalso
      have hb0 : b = 0 := by omega
      rw [hb0, pow_zero, mul_one] at hcard
      have hS := sum_le_divisors_sdiff hdist ({Nat.card G, Nat.card G / 2} : Finset ℕ)
        (by
          intro s hs
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact dvd_rfl
          · exact Nat.div_dvd_of_dvd h2dvd)
        (by
          intro s hs x
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact conjClassCard_ne_card x
          · exact conjClassCard_ne_div_prime (by decide : Nat.Prime 2) h4dvd x)
      have hne_pair : Nat.card G ≠ Nat.card G / 2 := by
        have hpos : 0 < Nat.card G := Nat.card_pos
        omega
      rw [Finset.sum_pair hne_pair] at hS
      have hsig : 4 * (∑ d ∈ (Nat.card G).divisors, d) = (2 ^ (a + 1) - 1) * (5 ^ (c + 1) - 1) := by
        rw [hcard, sum_divisors_mul_coprime ((Nat.Coprime.pow_right c (by decide)).pow_left a),
          sum_divisors_two_pow, ← mul_assoc, mul_comm 4, mul_assoc, sum_divisors_five_pow]
      have h2a_pos : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      have h5c_pos : 1 ≤ 5 ^ c := Nat.one_le_pow _ _ (by omega)
      have hdiv2 : 2 * (Nat.card G / 2) = Nat.card G := Nat.mul_div_cancel' h2dvd
      have hLHS : 4 * (Nat.card G + (Nat.card G + Nat.card G / 2)) = 10 * (2 ^ a * 5 ^ c) := by
        rw [← hcard]; omega
      have hRHS : (2 ^ (a + 1) - 1) * (5 ^ (c + 1) - 1) < 10 * (2 ^ a * 5 ^ c) := by
        have h2p : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
        have h5p : 5 ^ (c + 1) = 5 * 5 ^ c := by rw [pow_succ]; ring
        rw [h2p, h5p]
        zify [show 1 ≤ 2 * 2 ^ a by omega, show 1 ≤ 5 * 5 ^ c by omega]
        nlinarith
      omega
  -- Case 2: c = 0 ({2, 3}-group, |G| = 2^a * 3^b)
  have hc0 : c = 0 := by omega
  rw [hc0, pow_zero, mul_one] at hcard
  have hb1 : 1 ≤ b := by
    by_contra hb0
    have hbeq : b = 0 := by omega
    rw [hbeq, pow_zero, mul_one] at hcard
    exact not_prime_pow_card hdist ⟨2, a, Nat.Prime.prime (by decide), by omega, hcard.symm⟩
  -- Subcase 2a: a = 1, b = 1 -> |G| = 6
  by_cases ha1eq : a = 1
  · by_cases hb1eq : b = 1
    · rw [hcard, ha1eq, hb1eq]; norm_num
    · -- a = 1, b ≥ 2: exclude |G| and |G|/3
      exfalso
      have hb2 : 2 ≤ b := by omega
      have h9dvd : 9 ∣ Nat.card G := by
        rw [hcard]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 hb2) _
      have h3dvd : 3 ∣ Nat.card G := (by decide : 3 ∣ 9).trans h9dvd
      have hS := sum_le_divisors_sdiff hdist ({Nat.card G, Nat.card G / 3} : Finset ℕ)
        (by
          intro s hs
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact dvd_rfl
          · exact Nat.div_dvd_of_dvd h3dvd)
        (by
          intro s hs x
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact conjClassCard_ne_card x
          · exact conjClassCard_ne_div_prime (by decide : Nat.Prime 3) h9dvd x)
      have hne_pair : Nat.card G ≠ Nat.card G / 3 := by
        have hpos : 0 < Nat.card G := Nat.card_pos; omega
      rw [Finset.sum_pair hne_pair] at hS
      have hsig : 2 * (∑ d ∈ (Nat.card G).divisors, d) = 3 * (3 ^ (b + 1) - 1) := by
        rw [hcard, ha1eq, sum_divisors_mul_coprime ((Nat.Coprime.pow_right b (by decide)).pow_left 1),
          sum_divisors_two_pow, ← mul_assoc, mul_comm 2, mul_assoc, sum_divisors_three_pow]
        norm_num
      have h3bm1 : 3 ^ b = 3 * 3 ^ (b - 1) := by
        calc 3 ^ b = 3 ^ (b - 1 + 1) := by congr 1; omega
          _ = 3 * 3 ^ (b - 1) := by rw [pow_succ]; ring
      have h3bp1 : 3 ^ (b + 1) = 9 * 3 ^ (b - 1) := by
        rw [pow_succ, h3bm1]; ring
      have hdiv3 : 3 * (Nat.card G / 3) = Nat.card G := Nat.mul_div_cancel' h3dvd
      have hcard_eq : Nat.card G = 6 * 3 ^ (b - 1) := by rw [hcard, ha1eq, pow_one, h3bm1]; ring
      have hpos3 : 1 ≤ 3 ^ (b - 1) := Nat.one_le_pow _ _ (by omega)
      omega
  -- Now a ≥ 2
  have ha2 : 2 ≤ a := by omega
  have h4dvd : 4 ∣ Nat.card G := by
    rw [hcard]; exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ha2) _
  -- Subcase 2b: b = 1, a ≥ 2 -> |G|/3 and |G|/6 cannot both occur
  by_cases hb1eq : b = 1
  · exfalso
    rw [hb1eq, pow_one] at hcard
    have hno := no_div3_and_div6_of_two_pow_mul_three ha2 hcard
    have hmiss : (∀ c : ConjClasses G, conjClassCard c ≠ Nat.card G / 3) ∨
        (∀ c : ConjClasses G, conjClassCard c ≠ Nat.card G / 6) := by
      by_contra hboth
      push Not at hboth
      exact hno hboth
    have h3dvd : 3 ∣ Nat.card G := by rw [hcard]; exact dvd_mul_left 3 _
    have h6dvd : 6 ∣ Nat.card G := by
      rw [hcard]
      have : 2 ^ a = 2 ^ (a - 1) * 2 := by
        calc 2 ^ a = 2 ^ (a - 1 + 1) := by congr 1; omega
          _ = 2 ^ (a - 1) * 2 := pow_succ 2 (a - 1)
      rw [this, mul_assoc]; exact dvd_mul_left 6 _
    have hsig : (∑ d ∈ (Nat.card G).divisors, d) = 4 * (2 ^ (a + 1) - 1) := by
      rw [hcard, show (3 : ℕ) = 3 ^ 1 by norm_num,
        sum_divisors_mul_coprime ((Nat.Coprime.pow_right 1 (by decide)).pow_left a),
        sum_divisors_two_pow]
      have h3sum : ∑ d ∈ (3 ^ 1).divisors, d = 4 := by decide
      rw [h3sum, mul_comm]
    have h2p : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
    have h2pos : 4 ≤ 2 ^ a := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha2
    have hdiv2 : 2 * (Nat.card G / 2) = Nat.card G := Nat.mul_div_cancel' h2dvd
    have hdiv3 : 3 * (Nat.card G / 3) = Nat.card G := Nat.mul_div_cancel' h3dvd
    have hdiv6 : 6 * (Nat.card G / 6) = Nat.card G := Nat.mul_div_cancel' h6dvd
    rcases hmiss with hm3 | hm6
    · have hS := sum_le_divisors_sdiff hdist ({Nat.card G, Nat.card G / 2, Nat.card G / 3} : Finset ℕ)
        (by
          intro s hs; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl
          · exact dvd_rfl
          · exact Nat.div_dvd_of_dvd h2dvd
          · exact Nat.div_dvd_of_dvd h3dvd)
        (by
          intro s hs x; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl
          · exact conjClassCard_ne_card x
          · exact conjClassCard_ne_div_prime (by decide : Nat.Prime 2) h4dvd x
          · exact hm3 x)
      have hnotmem : Nat.card G ∉ ({Nat.card G / 2, Nat.card G / 3} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      rw [Finset.sum_insert hnotmem, Finset.sum_pair (by omega)] at hS
      omega
    · have hS := sum_le_divisors_sdiff hdist ({Nat.card G, Nat.card G / 2, Nat.card G / 6} : Finset ℕ)
        (by
          intro s hs; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl
          · exact dvd_rfl
          · exact Nat.div_dvd_of_dvd h2dvd
          · exact Nat.div_dvd_of_dvd h6dvd)
        (by
          intro s hs x; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl
          · exact conjClassCard_ne_card x
          · exact conjClassCard_ne_div_prime (by decide : Nat.Prime 2) h4dvd x
          · exact hm6 x)
      have hnotmem : Nat.card G ∉ ({Nat.card G / 2, Nat.card G / 6} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      rw [Finset.sum_insert hnotmem, Finset.sum_pair (by omega)] at hS
      omega
  -- Now a ≥ 2, b ≥ 2, c = 0
  have hb2 : 2 ≤ b := by omega
  have h9dvd : 9 ∣ Nat.card G := by
    rw [hcard]; exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 hb2) _
  -- Subcase 2c: a ∈ {2, 3}, b ≥ 2 -> impossible by divisor-sum bound
  by_cases ha4 : 4 ≤ a
  · have h16dvd : 16 ∣ Nat.card G := by
      rw [hcard]; exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ha4) _
    have hprimes23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3 := by
      intro p hp hdvd
      rcases hprimes p hp hdvd with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rw [hcard] at hdvd
        have hcop : Nat.Coprime 5 (2 ^ a * 3 ^ b) :=
          (Nat.Coprime.pow_right a (by decide)).mul_right (Nat.Coprime.pow_right b (by decide))
        have hd1 : 5 ∣ 1 := by
          have := Nat.dvd_gcd dvd_rfl hdvd
          rwa [hcop.gcd_eq_one] at this
        omega
    exact False.elim (h23 G hprimes23 h16dvd h9dvd hdist)
  · exfalso
    have h3dvd : 3 ∣ Nat.card G := (by decide : 3 ∣ 9).trans h9dvd
    have hS := sum_le_divisors_sdiff hdist ({Nat.card G, Nat.card G / 2, Nat.card G / 3} : Finset ℕ)
      (by
        intro s hs; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl
        · exact dvd_rfl
        · exact Nat.div_dvd_of_dvd h2dvd
        · exact Nat.div_dvd_of_dvd h3dvd)
      (by
        intro s hs x; simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl
        · exact conjClassCard_ne_card x
        · exact conjClassCard_ne_div_prime (by decide : Nat.Prime 2) h4dvd x
        · exact conjClassCard_ne_div_prime (by decide : Nat.Prime 3) h9dvd x)
    have hdiv2 : 2 * (Nat.card G / 2) = Nat.card G := Nat.mul_div_cancel' h2dvd
    have hdiv3 : 3 * (Nat.card G / 3) = Nat.card G := Nat.mul_div_cancel' h3dvd
    have hGpos : 12 ≤ Nat.card G := by
      rw [hcard]
      have h2a : 4 ≤ 2 ^ a := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha2
      have h3b : 9 ≤ 3 ^ b := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ b := Nat.pow_le_pow_right (by omega) hb2
      nlinarith
    have hnotmem : Nat.card G ∉ ({Nat.card G / 2, Nat.card G / 3} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    rw [Finset.sum_insert hnotmem, Finset.sum_pair (by omega)] at hS
    have hsig : 2 * (∑ d ∈ (Nat.card G).divisors, d) = (2 ^ (a + 1) - 1) * (3 ^ (b + 1) - 1) := by
      rw [hcard, sum_divisors_mul_coprime ((Nat.Coprime.pow_right b (by decide)).pow_left a),
        sum_divisors_two_pow, ← mul_assoc, mul_comm 2, mul_assoc, sum_divisors_three_pow]
    have h3bm1 : 3 ^ b = 3 * 3 ^ (b - 1) := by
      calc 3 ^ b = 3 ^ (b - 1 + 1) := by congr 1; omega
        _ = 3 * 3 ^ (b - 1) := by rw [pow_succ]; ring
    have h3bp1 : 3 ^ (b + 1) = 9 * 3 ^ (b - 1) := by
      rw [pow_succ, h3bm1]; ring
    have hpos3 : 1 ≤ 3 ^ (b - 1) := Nat.one_le_pow _ _ (by omega)
    have ha23 : a = 2 ∨ a = 3 := by omega
    rcases ha23 with rfl | rfl
    · have hcard_eq : Nat.card G = 12 * 3 ^ (b - 1) := by rw [hcard, h3bm1]; ring
      have hsig_eq : 2 * (∑ d ∈ (Nat.card G).divisors, d) = 7 * (9 * 3 ^ (b - 1) - 1) := by
        rw [hsig, h3bp1]; norm_num
      omega
    · have hcard_eq : Nat.card G = 24 * 3 ^ (b - 1) := by rw [hcard, h3bm1]; ring
      have hsig_eq : 2 * (∑ d ∈ (Nat.card G).divisors, d) = 15 * (9 * 3 ^ (b - 1) - 1) := by
        rw [hsig, h3bp1]; norm_num
      omega

end OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H2_R1
