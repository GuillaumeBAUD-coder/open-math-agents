import FormalConjectures.Arxiv.«2604.08040».Conjecture5_5
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.GroupAction.ConjAct

open scoped Classical

private lemma isNilpotent_of_numPrimeFactors_le_one {G : Type*} [Group G] [Fintype G]
    (ht : Arxiv.«2604.08040».numPrimeFactors G ≤ 1) : Group.IsNilpotent G := by
  unfold Arxiv.«2604.08040».numPrimeFactors at ht
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h0 | h1
  · have hcard : Fintype.card G = 1 := by
      have hpos : 0 < Fintype.card G := Fintype.card_pos
      have hpf : (Fintype.card G).primeFactors = ∅ := Finset.card_eq_zero.mp h0
      by_contra hne
      have hge : 1 < Fintype.card G := lt_of_le_of_ne hpos (Ne.symm hne)
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hge.ne'
      have hmem : p ∈ (Fintype.card G).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpd, hpos.ne'⟩
      rw [hpf] at hmem
      exact Finset.notMem_empty p hmem
    letI : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp hcard.le
    letI : CommGroup G := { ‹Group G› with mul_comm := fun a b => Subsingleton.elim (a * b) (b * a) }
    exact CommGroup.isNilpotent (G := G)
  · obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp h1
    have hp_mem : p ∈ (Fintype.card G).primeFactors := by
      rw [hp_eq]
      exact Finset.mem_singleton_self p
    have hp : p.Prime := (Nat.mem_primeFactors.mp hp_mem).1
    have hcard : Nat.card G = p ^ (Fintype.card G).factorization p := by
      have hne : Fintype.card G ≠ 0 := Fintype.card_ne_zero
      rw [Nat.card_eq_fintype_card]
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hne]
      rw [Finsupp.prod, Nat.support_factorization, hp_eq, Finset.prod_singleton]
    letI : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p G := IsPGroup.of_card hcard
    exact hpg.isNilpotent

private noncomputable def roots (H : Type*) [Group H] [Fintype H] (d : ℕ) : Finset H :=
  Finset.univ.filter (fun x : H => x ^ d = 1)

private lemma mem_roots {H : Type*} [Group H] [Fintype H] {d : ℕ} {x : H} :
    x ∈ roots H d ↔ x ^ d = 1 := by
  simp [roots]

private lemma roots_top_card {H : Type*} [Group H] [Fintype H] (d : ℕ) :
    (roots (⊤ : Subgroup H) d).card = (roots H d).card := by
  refine Finset.card_bij (fun x _ => (x : H)) ?_ ?_ ?_
  · intro x hx
    rw [mem_roots] at hx ⊢
    exact congrArg Subtype.val hx
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    rw [mem_roots] at hx
    refine ⟨⟨x, Subgroup.mem_top x⟩, ?_, rfl⟩
    rw [mem_roots]
    exact Subtype.ext hx

private lemma roots_dvd_gcd {H : Type*} [Group H] [Fintype H] (d : ℕ) :
    roots H d = roots H (Nat.gcd d (Fintype.card H)) := by
  ext x
  simp only [mem_roots, ← orderOf_dvd_iff_pow_eq_one, Nat.dvd_gcd_iff]
  exact ⟨fun h => ⟨h, orderOf_dvd_card⟩, fun h => h.1⟩

private lemma roots_coprime_card {H : Type*} [Group H] [Fintype H] {a b : ℕ}
    (hab : Nat.Coprime a b) :
    (roots H (a * b)).card =
      ∑ y ∈ roots H a, (roots (Subgroup.centralizer ({y} : Set H)) b).card := by
  have hbez : (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b = 1 := by
    have := Nat.gcd_eq_gcd_ab a b
    rw [hab.gcd_eq_one] at this
    omega
  let f : roots H (a * b) → Σ y : roots H a, roots (Subgroup.centralizer ({y.1} : Set H)) b :=
    fun x =>
      let y : H := x.1 ^ ((b : ℤ) * Nat.gcdB a b)
      let z : H := x.1 ^ ((a : ℤ) * Nat.gcdA a b)
      have hx : x.1 ^ (a * b) = 1 := (mem_roots.mp x.2)
      have hy : y ∈ roots H a := by
        rw [mem_roots]
        change (x.1 ^ ((b : ℤ) * Nat.gcdB a b)) ^ a = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm ((b : ℤ) * _), ← mul_assoc,
          ← Int.natCast_mul, zpow_mul, zpow_natCast, hx, one_zpow]
      have hcomm : y * z = z * y := by
        dsimp [y, z]
        rw [← zpow_add, ← zpow_add, add_comm]
      have hz_mem : z ∈ Subgroup.centralizer ({y} : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hcomm
      have hz : (⟨z, hz_mem⟩ : Subgroup.centralizer ({y} : Set H)) ∈
          roots (Subgroup.centralizer ({y} : Set H)) b := by
        rw [mem_roots]
        ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        change (x.1 ^ ((a : ℤ) * Nat.gcdA a b)) ^ b = 1
        rw [← zpow_natCast, ← zpow_mul, mul_assoc (a : ℤ), mul_comm (Nat.gcdA a b),
          ← mul_assoc, ← Int.natCast_mul, zpow_mul, zpow_natCast, hx, one_zpow]
      ⟨⟨y, hy⟩, ⟨⟨z, hz_mem⟩, hz⟩⟩
  let g : (Σ y : roots H a, roots (Subgroup.centralizer ({y.1} : Set H)) b) → roots H (a * b) :=
    fun p =>
      ⟨p.1.1 * p.2.1.1, by
        rw [mem_roots]
        have hcomm : Commute p.1.1 p.2.1.1 := by
          exact Subgroup.mem_centralizer_iff.mp p.2.1.2 p.1.1 (Set.mem_singleton p.1.1)
        rw [hcomm.mul_pow, pow_mul, mem_roots.mp p.1.2, one_pow, one_mul,
          mul_comm a b, pow_mul]
        have hzb : p.2.1 ^ b = 1 := mem_roots.mp p.2.2
        have hzb' : p.2.1.1 ^ b = 1 := congrArg Subtype.val hzb
        rw [hzb', one_pow]⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    ext
    dsimp [f, g]
    rw [← zpow_add, add_comm ((b : ℤ) * _), hbez, zpow_one]
  have hgf : Function.RightInverse g f := by
    intro ⟨⟨y, hy⟩, ⟨⟨z, hz_mem⟩, hz⟩⟩
    have hcomm : Commute y z :=
      Subgroup.mem_centralizer_iff.mp hz_mem y (Set.mem_singleton y)
    have hy_a : y ^ a = 1 := mem_roots.mp hy
    have hz_b : z ^ b = 1 := congrArg Subtype.val (mem_roots.mp hz)
    have hy_eq : (y * z) ^ ((b : ℤ) * Nat.gcdB a b) = y := by
      rw [hcomm.mul_zpow]
      have hz1 : z ^ ((b : ℤ) * Nat.gcdB a b) = 1 := by
        rw [zpow_mul, zpow_natCast, hz_b, one_zpow]
      have hy1 : y ^ ((b : ℤ) * Nat.gcdB a b) = y := by
        have hb : (b : ℤ) * Nat.gcdB a b = 1 - (a : ℤ) * Nat.gcdA a b := by omega
        rw [hb, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hy_a, one_zpow,
          inv_one, mul_one]
      rw [hz1, hy1, mul_one]
    have hz_eq : (y * z) ^ ((a : ℤ) * Nat.gcdA a b) = z := by
      rw [hcomm.mul_zpow]
      have hy1 : y ^ ((a : ℤ) * Nat.gcdA a b) = 1 := by
        rw [zpow_mul, zpow_natCast, hy_a, one_zpow]
      have hz1 : z ^ ((a : ℤ) * Nat.gcdA a b) = z := by
        have ha : (a : ℤ) * Nat.gcdA a b = 1 - (b : ℤ) * Nat.gcdB a b := by omega
        rw [ha, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hz_b, one_zpow,
          inv_one, mul_one]
      rw [hy1, hz1, one_mul]
    have hheq : ∀ (y₁ y₂ : roots H a), y₁ = y₂ →
        ∀ (z₁ : roots (Subgroup.centralizer ({y₁.1} : Set H)) b)
          (z₂ : roots (Subgroup.centralizer ({y₂.1} : Set H)) b),
          z₁.1.1 = z₂.1.1 → z₁ ≍ z₂ := by
      rintro y₁ y₂ rfl z₁ z₂ h
      exact heq_of_eq (Subtype.ext (Subtype.ext h))
    exact Sigma.ext (Subtype.ext hy_eq) (hheq _ _ (Subtype.ext hy_eq) _ _ hz_eq)
  have hcard := Fintype.card_congr ⟨f, g, hfg, hgf⟩
  simp only [Fintype.card_coe, Fintype.card_sigma] at hcard
  rw [hcard, ← Finset.sum_coe_sort (roots H a)]

private lemma roots_centralizer_conj_eq {H : Type*} [Group H] [Fintype H]
    (g : ConjAct H) (y : H) (b : ℕ) :
    (roots (Subgroup.centralizer ({y} : Set H)) b).card =
      (roots (Subgroup.centralizer ({g • y} : Set H)) b).card := by
  let h : H := ConjAct.ofConjAct g
  have hsmul : g • y = h * y * h⁻¹ := rfl
  let e : Subgroup.centralizer ({y} : Set H) ≃* Subgroup.centralizer ({g • y} : Set H) :=
    { toFun := fun x => ⟨h * x.1 * h⁻¹, by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have hx : y * x.1 = x.1 * y :=
          Subgroup.mem_centralizer_iff.mp x.2 y (Set.mem_singleton y)
        rw [hsmul]
        calc h * y * h⁻¹ * (h * x.1 * h⁻¹) = h * (y * x.1) * h⁻¹ := by group
        _ = h * (x.1 * y) * h⁻¹ := by rw [hx]
        _ = h * x.1 * h⁻¹ * (h * y * h⁻¹) := by group⟩
      invFun := fun x => ⟨h⁻¹ * x.1 * h, by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have hx : (h * y * h⁻¹) * x.1 = x.1 * (h * y * h⁻¹) :=
          Subgroup.mem_centralizer_iff.mp x.2 (g • y) (Set.mem_singleton _)
        calc y * (h⁻¹ * x.1 * h) = h⁻¹ * (h * y * h⁻¹ * x.1) * h := by group
        _ = h⁻¹ * (x.1 * (h * y * h⁻¹)) * h := by rw [hx]
        _ = h⁻¹ * x.1 * h * y := by group⟩
      left_inv := fun x => by ext; dsimp [h]; group
      right_inv := fun x => by ext; dsimp [h]; group
      map_mul' := fun x₁ x₂ => by ext; dsimp [h]; group }
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    rw [mem_roots] at hx ⊢
    rw [← map_pow, hx, map_one]
  · intro x₁ _ x₂ _ h12
    exact e.injective h12
  · intro z hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rw [mem_roots] at hz ⊢
    rw [← map_pow, hz, map_one]

private lemma card_orbit_mul_card_centralizer {H : Type*} [Group H] [Fintype H] (y : H) :
    Fintype.card (MulAction.orbit (ConjAct H) y) *
      Fintype.card (Subgroup.centralizer ({y} : Set H)) = Fintype.card H := by
  have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct H) y
  have h2 : Fintype.card (ConjAct H) = Fintype.card H := Fintype.card_congr ConjAct.toConjAct.toEquiv.symm
  have h3 : Fintype.card (MulAction.stabilizer (ConjAct H) y) =
      Fintype.card (Subgroup.centralizer ({y} : Set H)) := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun g => ⟨ConjAct.ofConjAct g.1, by
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          have hg : g.1 • y = y := g.2
          change ConjAct.ofConjAct g.1 * y * (ConjAct.ofConjAct g.1)⁻¹ = y at hg
          calc y * ConjAct.ofConjAct g.1 = (ConjAct.ofConjAct g.1 * y * (ConjAct.ofConjAct g.1)⁻¹) * ConjAct.ofConjAct g.1 := by rw [hg]
          _ = ConjAct.ofConjAct g.1 * y := by group⟩
        invFun := fun g => ⟨ConjAct.toConjAct g.1, by
          change g.1 * y * g.1⁻¹ = y
          have hg := Subgroup.mem_centralizer_iff.mp g.2 y (Set.mem_singleton y)
          calc g.1 * y * g.1⁻¹ = y * g.1 * g.1⁻¹ := by rw [hg]
          _ = y := by group⟩
        left_inv := fun g => by ext; simp
        right_inv := fun g => by ext; simp }
  rw [h2, h3] at h1
  exact h1

private lemma sum_roots_centralizer_orbits_dvd {H : Type*} [Group H] [Fintype H]
    (S : Finset H) (hS : ∀ (g : ConjAct H) (y : H), y ∈ S → g • y ∈ S) (b d : ℕ)
    (hd : ∀ y ∈ S, d ∣ (Fintype.card (MulAction.orbit (ConjAct H) y)) *
      (roots (Subgroup.centralizer ({y} : Set H)) b).card) :
    d ∣ ∑ y ∈ S, (roots (Subgroup.centralizer ({y} : Set H)) b).card := by
  let q : H → Quotient (MulAction.orbitRel (ConjAct H) H) := Quotient.mk''
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image q) (g := q)
    (fun y hy => Finset.mem_image_of_mem q hy)]
  apply Finset.dvd_sum
  intro c hc
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hc
  have hconst : ∀ y ∈ S.filter (fun y => q y = q y₀),
      (roots (Subgroup.centralizer ({y} : Set H)) b).card =
        (roots (Subgroup.centralizer ({y₀} : Set H)) b).card := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have hrel : MulAction.orbitRel (ConjAct H) H y y₀ := Quotient.eq''.mp hy.2
    obtain ⟨g, hg⟩ := hrel
    rw [← hg]
    exact (roots_centralizer_conj_eq g y₀ b).symm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  have hcard : (S.filter (fun y => q y = q y₀)).card =
      Fintype.card (MulAction.orbit (ConjAct H) y₀) := by
    refine Finset.card_bij (fun y hy => ⟨y, by
      rw [Finset.mem_filter] at hy
      have hrel : MulAction.orbitRel (ConjAct H) H y y₀ := Quotient.eq''.mp hy.2
      exact hrel⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro _ _ _ _ h; exact congrArg Subtype.val h
    · intro ⟨y, hy⟩ _
      obtain ⟨g, hg⟩ := hy
      refine ⟨y, Finset.mem_filter.mpr ⟨?_, Quotient.eq''.mpr ⟨g, hg⟩⟩, rfl⟩
      rw [← hg]
      exact hS g y₀ hy₀
  rw [hcard]
  exact hd y₀ hy₀

private lemma normal_zpowers_of_mem_center {H : Type*} [Group H] {z : H}
    (hz : z ∈ Subgroup.center H) : (Subgroup.zpowers z).Normal where
  conj_mem n hn g := by
    have hcomm := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hz hn) g
    have hgn : g * n * g⁻¹ = n := by
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcomm]
      _ = n := by group
    rw [hgn]
    exact hn

private lemma roots_quotient_center_card {H : Type*} [Group H] [Fintype H]
    {z : H} (hz : z ∈ Subgroup.center H) [(Subgroup.zpowers z).Normal] {d : ℕ}
    (hcop : Nat.Coprime d (Fintype.card (Subgroup.zpowers z))) :
    (roots H d).card = (roots (H ⧸ Subgroup.zpowers z) d).card := by
  let Z := Subgroup.zpowers z
  have hZ_le : Z ≤ Subgroup.center H := Subgroup.zpowers_le.mpr hz
  have hbez : (d : ℤ) * Nat.gcdA d (Fintype.card Z) +
      (Fintype.card Z : ℤ) * Nat.gcdB d (Fintype.card Z) = 1 := by
    have := Nat.gcd_eq_gcd_ab d (Fintype.card Z)
    rw [hcop.gcd_eq_one] at this
    omega
  refine Finset.card_bij (fun x _ => QuotientGroup.mk x) ?_ ?_ ?_
  · intro x hx
    rw [mem_roots] at hx ⊢
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  · intro x₁ hx₁ x₂ hx₂ h12
    rw [mem_roots] at hx₁ hx₂
    have hq : QuotientGroup.mk (x₂⁻¹ * x₁) = (1 : H ⧸ Z) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h12, inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff] at hq
    have hcomm : Commute x₂ (x₂⁻¹ * x₁) :=
      Subgroup.mem_center_iff.mp (hZ_le hq) x₂
    have hpow : (x₂⁻¹ * x₁) ^ d = 1 := by
      have hx1_eq : x₁ = x₂ * (x₂⁻¹ * x₁) := by group
      have h1 : x₁ ^ d = x₂ ^ d * (x₂⁻¹ * x₁) ^ d := by
        conv_lhs => rw [hx1_eq]
        exact hcomm.mul_pow d
      rw [hx₁, hx₂, one_mul] at h1
      exact h1.symm
    have hord' : orderOf (x₂⁻¹ * x₁) ∣ Fintype.card Z := by
      have hord : orderOf (⟨x₂⁻¹ * x₁, hq⟩ : Z) ∣ Fintype.card Z := orderOf_dvd_card
      rwa [← Subgroup.orderOf_coe] at hord
    have hdvd : orderOf (x₂⁻¹ * x₁) ∣ d := orderOf_dvd_iff_pow_eq_one.mpr hpow
    have h1 : orderOf (x₂⁻¹ * x₁) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd hord'
    rw [orderOf_eq_one_iff] at h1
    exact (eq_of_inv_mul_eq_one h1).symm
  · intro q hq
    rw [mem_roots] at hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxd : x ^ d ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hq
    let w : H := (x ^ d) ^ Nat.gcdA d (Fintype.card Z)
    have hw_mem : w ∈ Z := Subgroup.zpow_mem Z hxd _
    have hw_center : w ∈ Subgroup.center H := hZ_le hw_mem
    have hwd : w ^ d = x ^ d := by
      have hpowZ : (x ^ d) ^ (Fintype.card Z) = 1 := by
        have h1 : (⟨x ^ d, hxd⟩ : Z) ^ Fintype.card Z = 1 := pow_card_eq_one
        exact congrArg Subtype.val h1
      dsimp [w]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have hd1 : (d : ℤ) * Nat.gcdA d (Fintype.card Z) =
          1 - (Fintype.card Z : ℤ) * Nat.gcdB d (Fintype.card Z) := by omega
      rw [← zpow_natCast, ← zpow_mul, hd1, zpow_sub, zpow_one,
        zpow_mul, zpow_natCast, hpowZ, one_zpow, inv_one, mul_one]
    refine ⟨x * w⁻¹, ?_, ?_⟩
    · rw [mem_roots]
      have hcomm : Commute x w⁻¹ :=
        Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hw_center) x
      rw [hcomm.mul_pow, inv_pow, hwd, mul_inv_cancel]
    · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (Subgroup.inv_mem _ hw_mem),
        mul_one]

private lemma dvd_card_roots_prime_pow_of_succ {H : Type*} [Group H] [Fintype H]
    {p k : ℕ} (hp : p.Prime) (hsucc : p ^ (k + 1) ∣ (roots H (p ^ (k + 1))).card) :
    p ^ k ∣ (roots H (p ^ k)).card := by
  have hsub : roots H (p ^ k) ⊆ roots H (p ^ (k + 1)) := by
    intro x hx
    rw [mem_roots] at hx ⊢
    rw [pow_succ, pow_mul, hx, one_pow]
  have hsum : (roots H (p ^ (k + 1)) \ roots H (p ^ k)).card + (roots H (p ^ k)).card =
      (roots H (p ^ (k + 1))).card := Finset.card_sdiff_add_card_eq_card hsub
  have hdvd_succ : p ^ k ∣ (roots H (p ^ (k + 1))).card :=
    dvd_trans (pow_dvd_pow p (Nat.le_succ k)) hsucc
  suffices hdvd_diff : p ^ k ∣ (roots H (p ^ (k + 1)) \ roots H (p ^ k)).card by
    exact (Nat.dvd_add_right hdvd_diff).mp (hsum.symm ▸ hdvd_succ)
  have hdiff_eq : roots H (p ^ (k + 1)) \ roots H (p ^ k) =
      Finset.univ.filter (fun x : H => orderOf x = p ^ (k + 1)) := by
    ext x
    simp only [Finset.mem_sdiff, mem_roots, Finset.mem_filter, Finset.mem_univ, true_and,
      ← orderOf_dvd_iff_pow_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      rw [Nat.dvd_prime_pow hp] at h1
      obtain ⟨j, hj, hj_eq⟩ := h1
      rcases Nat.lt_or_eq_of_le hj with hlt | rfl
      · exfalso
        apply h2
        rw [hj_eq]
        exact pow_dvd_pow p (Nat.lt_succ_iff.mp hlt)
      · exact hj_eq
    · intro hord
      rw [hord]
      refine ⟨dvd_rfl, ?_⟩
      intro hdvd
      have hle : k + 1 ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
      omega
  rw [hdiff_eq]
  let S := Finset.univ.filter (fun x : H => orderOf x = p ^ (k + 1))
  change p ^ k ∣ S.card
  have hfib : S.card = ∑ L ∈ S.image Subgroup.zpowers,
      (S.filter (fun x => Subgroup.zpowers x = L)).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (s := S)
      (t := S.image Subgroup.zpowers) (g := Subgroup.zpowers)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [Finset.card_eq_sum_ones]
  rw [hfib]
  apply Finset.dvd_sum
  intro L hL
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hL
  have hx₀_ord : orderOf x₀ = p ^ (k + 1) := (Finset.mem_filter.mp hx₀).2
  have hL_card : Fintype.card (Subgroup.zpowers x₀) = p ^ (k + 1) := by
    rw [Fintype.card_zpowers, hx₀_ord]
  have hbij : (S.filter (fun x => Subgroup.zpowers x = Subgroup.zpowers x₀)).card =
      (Finset.univ.filter (fun y : Subgroup.zpowers x₀ => orderOf y = p ^ (k + 1))).card := by
    refine Finset.card_bij (fun x hx => ⟨x, by
      have hx' := (Finset.mem_filter.mp hx).2
      rw [← hx']
      exact Subgroup.mem_zpowers x⟩) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← Subgroup.orderOf_coe]
      exact (Finset.mem_filter.mp hx.1).2
    · intro x₁ _ x₂ _ h12
      exact congrArg Subtype.val h12
    · intro ⟨y, hy⟩ hy_filt
      rw [Finset.mem_filter] at hy_filt
      have hy_ord : orderOf y = p ^ (k + 1) := by
        simpa [Subgroup.orderOf_coe] using hy_filt.2
      have hsub_le : Subgroup.zpowers y ≤ Subgroup.zpowers x₀ := Subgroup.zpowers_le.mpr hy
      have hcard_eq : Fintype.card (Subgroup.zpowers y) = Fintype.card (Subgroup.zpowers x₀) := by
        rw [Fintype.card_zpowers, hy_ord, hL_card]
      have hzpow_eq : Subgroup.zpowers y = Subgroup.zpowers x₀ :=
        Subgroup.eq_of_le_of_card_ge hsub_le (by
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard_eq])
      refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_ord⟩, hzpow_eq⟩, rfl⟩
  rw [hbij]
  have htot : (Finset.univ.filter (fun y : Subgroup.zpowers x₀ => orderOf y = p ^ (k + 1))).card =
      Nat.totient (p ^ (k + 1)) := by
    have := IsCyclic.card_orderOf_eq_totient (α := Subgroup.zpowers x₀) (d := p ^ (k + 1))
    rw [hL_card] at this
    exact this (dvd_refl _)
  rw [htot, Nat.totient_prime_pow hp (Nat.succ_pos k)]
  exact dvd_mul_right _ _

private lemma frobenius_dvd_card :
    ∀ (n : ℕ) {H : Type u} [Group H] [Fintype H],
      Fintype.card H = n → ∀ d : ℕ, d ∣ n → d ∣ (roots H d).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H _ _ hcard d hd
    have hn_pos : 0 < n := hcard ▸ Fintype.card_pos
    have hprime_pow : ∀ (p k : ℕ), p.Prime → p ^ k ∣ n → p ^ k ∣ (roots H (p ^ k)).card := by
      intro p k hp hpk
      let c := n.factorization p
      have hkc : k ≤ c := by
        rw [← hp.pow_dvd_iff_le_factorization hn_pos.ne']
        exact hpk
      suffices hc_all : ∀ j ≤ c, p ^ j ∣ (roots H (p ^ j)).card from hc_all k hkc
      have htop : p ^ c ∣ (roots H (p ^ c)).card := by
        by_cases hc0 : c = 0
        · rw [hc0, pow_zero]; exact one_dvd _
        have hc_pos : 0 < c := Nat.pos_of_ne_zero hc0
        let m := n / p ^ c
        have hpc_dvd : p ^ c ∣ n := Nat.ordProj_dvd n p
        have hnm : p ^ c * m = n := Nat.mul_div_cancel' hpc_dvd
        have hnot_dvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn_pos.ne'
        have hcop : Nat.Coprime (p ^ c) m := (hp.coprime_iff_not_dvd.mpr hnot_dvd).pow_left c
        by_cases hm1 : m = 1
        · have hn_eq : n = p ^ c := by rw [← hnm, hm1, mul_one]
          have hall : roots H (p ^ c) = Finset.univ := by
            ext x
            simp only [mem_roots, Finset.mem_univ, iff_true]
            rw [← hn_eq, ← hcard]
            exact pow_card_eq_one
          rw [hall, Finset.card_univ, hcard, hn_eq]
        have hm_gt1 : 1 < m := by
          have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn_pos hpc_dvd) (pow_pos hp.pos c)
          omega
        by_cases hcenter : ∃ z ∈ roots H m, z ≠ 1 ∧ z ∈ Subgroup.center H
        · obtain ⟨z, hz_roots, hz_ne, hz_cent⟩ := hcenter
          let Z := Subgroup.zpowers z
          letI : Z.Normal := normal_zpowers_of_mem_center hz_cent
          have hZ_card_gt1 : 1 < Fintype.card Z := by
            rw [Fintype.card_zpowers]
            exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
              ⟨(orderOf_pos z).ne', mt orderOf_eq_one_iff.mp hz_ne⟩
          have hZ_dvd_m : Fintype.card Z ∣ m := by
            rw [Fintype.card_zpowers, orderOf_dvd_iff_pow_eq_one]
            exact mem_roots.mp hz_roots
          have hcopZ : Nat.Coprime (p ^ c) (Fintype.card Z) := hcop.coprime_dvd_right hZ_dvd_m
          have hq_mul : Fintype.card (H ⧸ Z) * Fintype.card Z = n := by
            rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
              ← Nat.card_eq_fintype_card]
            exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
          have hq_lt : Fintype.card (H ⧸ Z) < n := by
            nlinarith [Fintype.card_pos (α := H ⧸ Z)]
          have hpc_dvd_q : p ^ c ∣ Fintype.card (H ⧸ Z) := by
            apply hcopZ.dvd_of_dvd_mul_right
            rw [hq_mul]
            exact hpc_dvd
          rw [roots_quotient_center_card hz_cent hcopZ]
          exact ih (Fintype.card (H ⧸ Z)) hq_lt rfl (p ^ c) hpc_dvd_q
        · push Not at hcenter
          have hroots_n : (roots H n).card = n := by
            have hall : roots H n = Finset.univ := by
              ext x
              simp only [mem_roots, Finset.mem_univ, iff_true, ← hcard]
              exact pow_card_eq_one
            rw [hall, Finset.card_univ, hcard]
          have hsplit : n = (roots H (p ^ c)).card +
              ∑ z ∈ (roots H m).erase 1, (roots (Subgroup.centralizer ({z} : Set H)) (p ^ c)).card := by
            have h1 : n = (roots H (m * p ^ c)).card := by rw [mul_comm, hnm, hroots_n]
            rw [h1, roots_coprime_card hcop.symm]
            have h1_mem : (1 : H) ∈ roots H m := by rw [mem_roots, one_pow]
            rw [← Finset.add_sum_erase (roots H m) _ h1_mem]
            congr 1
            have hcent1 : Subgroup.centralizer ({(1 : H)} : Set H) = ⊤ := by
              ext x; simp [Subgroup.mem_centralizer_iff]
            rw [hcent1, roots_top_card]
          suffices hdvd_sum : p ^ c ∣ ∑ z ∈ (roots H m).erase 1,
              (roots (Subgroup.centralizer ({z} : Set H)) (p ^ c)).card by
            exact (Nat.dvd_add_left hdvd_sum).mp (hsplit ▸ hpc_dvd)
          apply sum_roots_centralizer_orbits_dvd
          · intro g y hy
            rw [Finset.mem_erase, mem_roots] at hy ⊢
            refine ⟨?_, ?_⟩
            · intro h1
              apply hy.1
              have : g⁻¹ • (g • y) = g⁻¹ • (1 : H) := congrArg (g⁻¹ • ·) h1
              simpa using this
            · change (ConjAct.ofConjAct g * y * (ConjAct.ofConjAct g)⁻¹) ^ m = 1
              rw [conj_pow, hy.2, mul_one, mul_inv_cancel]
          · intro z hz
            rw [Finset.mem_erase] at hz
            have hz_not_cent : z ∉ Subgroup.center H := hcenter z hz.2 hz.1
            let K := Subgroup.centralizer ({z} : Set H)
            have hK_lt : Fintype.card K < n := by
              have hK_ne : K ≠ ⊤ := by
                intro htop
                apply hz_not_cent
                rw [Subgroup.mem_center_iff]
                intro g
                have hg : g ∈ K := htop ▸ Subgroup.mem_top g
                exact (Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)).symm
              by_contra hle
              apply hK_ne
              apply Subgroup.eq_top_of_card_eq K
              rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
              have hdvd : Fintype.card K ∣ Fintype.card H := by
                rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
                exact Subgroup.card_subgroup_dvd_card K
              have hle' : Fintype.card K ≤ Fintype.card H := Nat.le_of_dvd Fintype.card_pos hdvd
              omega
            let a := (Fintype.card K).factorization p
            have hK_pos : 0 < Fintype.card K := Fintype.card_pos
            have hpa_dvd : p ^ a ∣ Fintype.card K := Nat.ordProj_dvd (Fintype.card K) p
            have hgcd : Nat.gcd (p ^ c) (Fintype.card K) = p ^ a := by
              have hK_dvd_n : Fintype.card K ∣ n := by
                rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
                exact Subgroup.card_subgroup_dvd_card K
              have hac : a ≤ c := (Nat.factorization_le_iff_dvd hK_pos.ne' hn_pos.ne').mpr hK_dvd_n p
              apply Nat.dvd_antisymm
              · have hd1 : Nat.gcd (p ^ c) (Fintype.card K) ∣ p ^ c := Nat.gcd_dvd_left _ _
                rw [Nat.dvd_prime_pow hp] at hd1
                obtain ⟨j, _, hj_eq⟩ := hd1
                rw [hj_eq]
                have hj_dvd_K : p ^ j ∣ Fintype.card K := hj_eq ▸ Nat.gcd_dvd_right _ _
                have hja : j ≤ a := (hp.pow_dvd_iff_le_factorization hK_pos.ne').mp hj_dvd_K
                exact pow_dvd_pow p hja
              · exact Nat.dvd_gcd (pow_dvd_pow p hac) hpa_dvd
            have hroots_eq : (roots K (p ^ c)).card = (roots K (p ^ a)).card := by
              rw [roots_dvd_gcd (p ^ c), hgcd]
            have hpa_roots : p ^ a ∣ (roots K (p ^ a)).card :=
              ih (Fintype.card K) hK_lt rfl (p ^ a) hpa_dvd
            have hpc_a_orb : p ^ (c - a) ∣ Fintype.card (MulAction.orbit (ConjAct H) z) := by
              have hK_dvd_n : Fintype.card K ∣ n := by
                rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
                exact Subgroup.card_subgroup_dvd_card K
              have hac : a ≤ c := (Nat.factorization_le_iff_dvd hK_pos.ne' hn_pos.ne').mpr hK_dvd_n p
              have horb_mul := card_orbit_mul_card_centralizer z
              rw [hcard] at horb_mul
              have hK_eq : Fintype.card K = p ^ a * (Fintype.card K / p ^ a) :=
                (Nat.mul_div_cancel' hpa_dvd).symm
              have hnot : ¬ p ∣ (Fintype.card K / p ^ a) := Nat.not_dvd_ordCompl hp hK_pos.ne'
              have hcop_ca : Nat.Coprime (p ^ (c - a)) (Fintype.card K / p ^ a) :=
                (hp.coprime_iff_not_dvd.mpr hnot).pow_left (c - a)
              apply hcop_ca.dvd_of_dvd_mul_right
              have hpc_eq : p ^ c = p ^ (c - a) * p ^ a := by
                rw [← pow_add, Nat.sub_add_cancel hac]
              have hdvd_prod : p ^ (c - a) * p ^ a ∣
                  (Fintype.card (MulAction.orbit (ConjAct H) z) * (Fintype.card K / p ^ a)) * p ^ a := by
                have h_assoc : (Fintype.card (MulAction.orbit (ConjAct H) z) *
                    (Fintype.card K / p ^ a)) * p ^ a = n := by
                  calc _ = Fintype.card (MulAction.orbit (ConjAct H) z) *
                        (p ^ a * (Fintype.card K / p ^ a)) := by ring
                    _ = Fintype.card (MulAction.orbit (ConjAct H) z) * Fintype.card K := by rw [← hK_eq]
                    _ = n := horb_mul
                rw [h_assoc, ← hpc_eq]
                exact hpc_dvd
              exact Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.pos a) hdvd_prod
            have hK_dvd_n : Fintype.card K ∣ n := by
              rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
              exact Subgroup.card_subgroup_dvd_card K
            have hac : a ≤ c := (Nat.factorization_le_iff_dvd hK_pos.ne' hn_pos.ne').mpr hK_dvd_n p
            have hpc_eq : p ^ c = p ^ (c - a) * p ^ a := by
              rw [← pow_add, Nat.sub_add_cancel hac]
            rw [hroots_eq]
            conv_lhs => rw [hpc_eq]
            exact mul_dvd_mul hpc_a_orb hpa_roots
      intro j hj
      induction' hk : c - j with diff ih_diff generalizing j
      · have hjc : j = c := by omega
        subst hjc; exact htop
      · have hj1 : j + 1 ≤ c := by omega
        have hdiff' : c - (j + 1) = diff := by omega
        exact dvd_card_roots_prime_pow_of_succ hp (ih_diff (j + 1) hj1 hdiff')
    -- General d ∣ n by strong induction on d
    induction d using Nat.strong_induction_on with
    | h d ih_d =>
      rcases Nat.lt_trichotomy d 1 with hd0 | rfl | hd_gt1
      · have : d = 0 := by omega
        subst this
        exfalso
        exact hn_pos.ne' (zero_dvd_iff.mp hd)
      · exact one_dvd _
      · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd_gt1.ne'
        let k := d.factorization p
        let a := p ^ k
        let m := d / a
        have ha_dvd : a ∣ d := Nat.ordProj_dvd d p
        have hdam : a * m = d := Nat.mul_div_cancel' ha_dvd
        have hnot_dvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (by omega)
        have hcop : Nat.Coprime a m := (hp.coprime_iff_not_dvd.mpr hnot_dvd).pow_left k
        by_cases hm1 : m = 1
        · have hda : d = a := by rw [← hdam, hm1, mul_one]
          rw [hda] at hd ⊢
          exact hprime_pow p k hp hd
        have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) ha_dvd) (pow_pos hp.pos k)
        have hm_gt1 : 1 < m := by omega
        have hk_pos : 0 < k := hp.factorization_pos_of_dvd (by omega) hpd
        have ha_gt1 : 1 < a := one_lt_pow₀ hp.one_lt hk_pos.ne'
        have ha_lt : a < d := by
          calc a = a * 1 := (mul_one a).symm
          _ < a * m := Nat.mul_lt_mul_of_pos_left hm_gt1 (pow_pos hp.pos k)
          _ = d := hdam
        have hm_lt : m < d := by
          calc m = 1 * m := (one_mul m).symm
          _ < a * m := Nat.mul_lt_mul_of_pos_right ha_gt1 hm_pos
          _ = d := hdam
        have hstep : ∀ {u v : ℕ}, u ∣ n → v < d → v ∣ n → Nat.Coprime u v →
            v ∣ (roots H (u * v)).card := by
          intro u v _ hv_lt hv_dvd huv
          rw [roots_coprime_card huv]
          apply sum_roots_centralizer_orbits_dvd
          · intro g y hy
            rw [mem_roots] at hy ⊢
            change (ConjAct.ofConjAct g * y * (ConjAct.ofConjAct g)⁻¹) ^ u = 1
            rw [conj_pow, hy, mul_one, mul_inv_cancel]
          · intro y _
            by_cases hy_cent : y ∈ Subgroup.center H
            · have hK_top : Subgroup.centralizer ({y} : Set H) = ⊤ := by
                ext g
                simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
                  Subgroup.mem_top, iff_true]
                exact (Subgroup.mem_center_iff.mp hy_cent g).symm
              rw [hK_top, roots_top_card]
              exact dvd_mul_of_dvd_right (ih_d v hv_lt hv_dvd) _
            · let K := Subgroup.centralizer ({y} : Set H)
              have hK_lt : Fintype.card K < n := by
                have hK_ne : K ≠ ⊤ := by
                  intro htop
                  apply hy_cent
                  rw [Subgroup.mem_center_iff]
                  intro g
                  have hg : g ∈ K := htop ▸ Subgroup.mem_top g
                  exact (Subgroup.mem_centralizer_iff.mp hg y (Set.mem_singleton y)).symm
                by_contra hle
                apply hK_ne
                apply Subgroup.eq_top_of_card_eq K
                rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
                have hdvd : Fintype.card K ∣ Fintype.card H := by
                  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
                  exact Subgroup.card_subgroup_dvd_card K
                have hle' : Fintype.card K ≤ Fintype.card H := Nat.le_of_dvd Fintype.card_pos hdvd
                omega
              let v_y := Nat.gcd v (Fintype.card K)
              have hv_y_dvd_K : v_y ∣ Fintype.card K := Nat.gcd_dvd_right _ _
              have hv_y_dvd_v : v_y ∣ v := Nat.gcd_dvd_left _ _
              have hroots_eq : (roots K v).card = (roots K v_y).card := by
                rw [roots_dvd_gcd v]
              have hv_y_roots : v_y ∣ (roots K v_y).card :=
                ih (Fintype.card K) hK_lt rfl v_y hv_y_dvd_K
              have hdiv_orb : v / v_y ∣ Fintype.card (MulAction.orbit (ConjAct H) y) := by
                have hv_y_pos : 0 < v_y := Nat.gcd_pos_of_pos_right _ Fintype.card_pos
                have hcop_div : Nat.Coprime (v / v_y) (Fintype.card K / v_y) :=
                  Nat.coprime_div_gcd_div_gcd hv_y_pos
                apply hcop_div.dvd_of_dvd_mul_right
                have horb_mul := card_orbit_mul_card_centralizer y
                rw [hcard] at horb_mul
                have hv_eq : v = (v / v_y) * v_y := (Nat.div_mul_cancel hv_y_dvd_v).symm
                have hK_eq : Fintype.card K = (Fintype.card K / v_y) * v_y :=
                  (Nat.div_mul_cancel hv_y_dvd_K).symm
                have hdvd_prod : (v / v_y) * v_y ∣
                    (Fintype.card (MulAction.orbit (ConjAct H) y) * (Fintype.card K / v_y)) * v_y := by
                  have h_assoc : (Fintype.card (MulAction.orbit (ConjAct H) y) *
                      (Fintype.card K / v_y)) * v_y = n := by
                    calc _ = Fintype.card (MulAction.orbit (ConjAct H) y) *
                          ((Fintype.card K / v_y) * v_y) := by ring
                      _ = Fintype.card (MulAction.orbit (ConjAct H) y) * Fintype.card K := by
                          rw [← hK_eq]
                      _ = n := horb_mul
                  rw [h_assoc, ← hv_eq]
                  exact hv_dvd
                exact Nat.dvd_of_mul_dvd_mul_right hv_y_pos hdvd_prod
              have hv_eq : v = (v / v_y) * v_y := (Nat.div_mul_cancel hv_y_dvd_v).symm
              rw [hroots_eq]
              conv_lhs => rw [hv_eq]
              exact mul_dvd_mul hdiv_orb hv_y_roots
        have ha_dvd_n : a ∣ n := dvd_trans ha_dvd hd
        have hm_dvd_n : m ∣ n := dvd_trans (Dvd.intro_left a hdam) hd
        have hm_dvd_roots : m ∣ (roots H d).card := by
          rw [← hdam]
          exact hstep ha_dvd_n hm_lt hm_dvd_n hcop
        have ha_dvd_roots : a ∣ (roots H d).card := by
          rw [← hdam, mul_comm]
          exact hstep hm_dvd_n ha_lt ha_dvd_n hcop.symm
        rw [← hdam] at ha_dvd_roots hm_dvd_roots ⊢
        exact hcop.mul_dvd_of_dvd_of_dvd ha_dvd_roots hm_dvd_roots

private lemma card_orderOf_eq_mul_cycCount {G : Type*} [Group G] [Fintype G] (k : ℕ) (hk : 0 < k) :
    (Finset.univ.filter (fun x : G => orderOf x = k)).card =
      Nat.totient k * (Finset.univ.filter (fun H : {H : Subgroup G // IsCyclic H} =>
        Fintype.card H.1 = k)).card := by
  let S := Finset.univ.filter (fun x : G => orderOf x = k)
  let T := Finset.univ.filter (fun H : {H : Subgroup G // IsCyclic H} => Fintype.card H.1 = k)
  change S.card = Nat.totient k * T.card
  have hfib : S.card = ∑ L ∈ S.image Subgroup.zpowers,
      (S.filter (fun x => Subgroup.zpowers x = L)).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (s := S)
      (t := S.image Subgroup.zpowers) (g := Subgroup.zpowers)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [Finset.card_eq_sum_ones]
  have himg : (S.image Subgroup.zpowers).card = T.card := by
    refine Finset.card_bij (fun L hL => ⟨L, by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hL
      infer_instance⟩) ?_ ?_ ?_
    · intro L hL
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hL
        rw [Fintype.card_zpowers]
        exact (Finset.mem_filter.mp hx).2⟩
    · intro L₁ _ L₂ _ h12
      exact congrArg Subtype.val h12
    · intro ⟨L, hL_cyc⟩ hL_mem
      have hL_card : Fintype.card L = k := (Finset.mem_filter.mp hL_mem).2
      obtain ⟨g, hg⟩ := hL_cyc.exists_generator
      have hg_ord : orderOf (g : G) = k := by
        rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hL_card]
      have hzpow : Subgroup.zpowers (g : G) = L := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          exact (L.zpow_mem g.2 n)
        · intro hx
          obtain ⟨n, hn⟩ := hg ⟨x, hx⟩
          rw [Subgroup.mem_zpowers_iff]
          exact ⟨n, congrArg Subtype.val hn⟩
      refine ⟨L, Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_ord⟩, hzpow⟩, rfl⟩
  rw [hfib, ← himg, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun L hL => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hL
  have hx₀_ord : orderOf x₀ = k := (Finset.mem_filter.mp hx₀).2
  have hL_card : Fintype.card (Subgroup.zpowers x₀) = k := by
    rw [Fintype.card_zpowers, hx₀_ord]
  have hbij : (S.filter (fun x => Subgroup.zpowers x = Subgroup.zpowers x₀)).card =
      (Finset.univ.filter (fun y : Subgroup.zpowers x₀ => orderOf y = k)).card := by
    refine Finset.card_bij (fun x hx => ⟨x, by
      have hx' := (Finset.mem_filter.mp hx).2
      rw [← hx']
      exact Subgroup.mem_zpowers x⟩) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← Subgroup.orderOf_coe]
      exact (Finset.mem_filter.mp hx.1).2
    · intro _ _ _ _ h12
      exact congrArg Subtype.val h12
    · intro ⟨y, hy⟩ hy_filt
      rw [Finset.mem_filter] at hy_filt
      have hy_ord : orderOf y = k := by
        simpa [Subgroup.orderOf_coe] using hy_filt.2
      have hsub_le : Subgroup.zpowers y ≤ Subgroup.zpowers x₀ := Subgroup.zpowers_le.mpr hy
      have hzpow_eq : Subgroup.zpowers y = Subgroup.zpowers x₀ :=
        Subgroup.eq_of_le_of_card_ge hsub_le (by
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          simp only [Fintype.card_zpowers, hy_ord, hx₀_ord]
          exact le_rfl)
      refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_ord⟩, hzpow_eq⟩, rfl⟩
  rw [hbij]
  have htot := IsCyclic.card_orderOf_eq_totient (α := Subgroup.zpowers x₀) (d := k)
  rw [hL_card] at htot
  exact htot (dvd_refl _)

private lemma card_roots_eq_sum_totient_mul_cycCount {G : Type*} [Group G] [Fintype G]
    {d : ℕ} (hd : 0 < d) :
    (roots G d).card = ∑ k ∈ d.divisors,
      Nat.totient k * (Finset.univ.filter (fun H : {H : Subgroup G // IsCyclic H} =>
        Fintype.card H.1 = k)).card := by
  have hfib : (roots G d).card = ∑ k ∈ (roots G d).image orderOf,
      ((roots G d).filter (fun x => orderOf x = k)).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (s := roots G d)
      (t := (roots G d).image orderOf) (g := orderOf)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.card_eq_sum_ones]
  have himg_sub : (roots G d).image orderOf ⊆ d.divisors := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    rw [mem_roots, ← orderOf_dvd_iff_pow_eq_one] at hx
    exact Nat.mem_divisors.mpr ⟨hx, hd.ne'⟩
  rw [hfib, Finset.sum_subset himg_sub]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hk_dvd : k ∣ d := Nat.dvd_of_mem_divisors hk
    have hfilt : (roots G d).filter (fun x => orderOf x = k) =
        Finset.univ.filter (fun x : G => orderOf x = k) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_roots,
        ← orderOf_dvd_iff_pow_eq_one]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hk_dvd, h⟩⟩
    rw [hfilt, card_orderOf_eq_mul_cycCount k hk_pos]
  · intro k _ hk_not
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hord
    apply hk_not
    exact Finset.mem_image.mpr ⟨x, hx, hord⟩

private lemma euler_sum_nonneg (d M : ℕ) (hd : 0 < d) (hM : 0 < M) :
    (0 : ℚ) ≤ ∑ m ∈ M.divisors, (ArithmeticFunction.moebius m : ℚ) / (Nat.totient (d * m) : ℚ) := by
  have htot_d : (0 : ℚ) < (Nat.totient d : ℚ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  rw [← mul_nonneg_iff_of_pos_left htot_d, Finset.mul_sum]
  let h : ℕ → ℚ := fun p => if p ∣ d then (p : ℚ) else (p : ℚ) - 1
  have h_pos : ∀ p ∈ M.primeFactors, (1 : ℚ) ≤ h p := by
    intro p hp
    have hp_prime := (Nat.mem_primeFactors.mp hp).1
    have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_prime.two_le
    dsimp [h]
    split_ifs <;> linarith
  have h_tot_mul : ∀ m ∈ M.divisors, Squarefree m →
      (Nat.totient (d * m) : ℚ) = (Nat.totient d : ℚ) * ∏ p ∈ m.primeFactors, h p := by
    intro m hm hsq
    have hm_pos : 0 < m := Nat.pos_of_mem_divisors hm
    have hdm_pos : 0 < d * m := Nat.mul_pos hd hm_pos
    rw [Nat.totient_eq_mul_prod_factors (d * m), Nat.totient_eq_mul_prod_factors d]
    have hpf : (d * m).primeFactors = d.primeFactors ∪ m.primeFactors :=
      Nat.primeFactors_mul hd.ne' hm_pos.ne'
    have hm_eq : (m : ℚ) = ∏ p ∈ m.primeFactors, (p : ℚ) := by
      have hm_nat : m = ∏ p ∈ m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
      conv_lhs => rw [hm_nat]
      simp
    rw [hpf, ← Finset.union_sdiff_self_eq_union,
      Finset.prod_union disjoint_sdiff_self_right, Nat.cast_mul, hm_eq]
    have hm_split : (∏ p ∈ m.primeFactors, (p : ℚ)) =
        (∏ p ∈ m.primeFactors ∩ d.primeFactors, (p : ℚ)) *
        (∏ p ∈ m.primeFactors \ d.primeFactors, (p : ℚ)) :=
      (Finset.prod_inter_mul_prod_sdiff m.primeFactors d.primeFactors _).symm
    have h_ite : (∏ p ∈ m.primeFactors, h p) =
        (∏ p ∈ m.primeFactors ∩ d.primeFactors, (p : ℚ)) *
        (∏ p ∈ m.primeFactors \ d.primeFactors, ((p : ℚ) - 1)) := by
      have h_eq : ∀ p ∈ m.primeFactors, h p =
          if p ∈ d.primeFactors then (p : ℚ) else (p : ℚ) - 1 := by
        intro p hp
        have hp_prime := (Nat.mem_primeFactors.mp hp).1
        dsimp [h]
        simp [Nat.mem_primeFactors, hp_prime, hd.ne']
      rw [Finset.prod_congr rfl h_eq, Finset.prod_ite, Finset.filter_mem_eq_inter]
      congr 2
      ext p
      simp [Finset.mem_filter, Finset.mem_sdiff]
    have h_cancel : (∏ p ∈ m.primeFactors \ d.primeFactors, (p : ℚ)) *
        (∏ p ∈ m.primeFactors \ d.primeFactors, (1 - (p : ℚ)⁻¹)) =
        ∏ p ∈ m.primeFactors \ d.primeFactors, ((p : ℚ) - 1) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_prime := (Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
      field_simp [hp0]
    rw [h_ite]
    calc (d : ℚ) * (∏ p ∈ m.primeFactors, (p : ℚ)) *
          ((∏ p ∈ d.primeFactors, (1 - (p : ℚ)⁻¹)) *
           (∏ p ∈ m.primeFactors \ d.primeFactors, (1 - (p : ℚ)⁻¹)))
        = (d : ℚ) * (∏ p ∈ d.primeFactors, (1 - (p : ℚ)⁻¹)) *
          ((∏ p ∈ m.primeFactors ∩ d.primeFactors, (p : ℚ)) *
           ((∏ p ∈ m.primeFactors \ d.primeFactors, (p : ℚ)) *
            (∏ p ∈ m.primeFactors \ d.primeFactors, (1 - (p : ℚ)⁻¹)))) := by
          rw [hm_split]; ring
      _ = _ := by rw [h_cancel]
  have h_sum_eq : (∑ m ∈ M.divisors, (Nat.totient d : ℚ) *
      ((ArithmeticFunction.moebius m : ℚ) / (Nat.totient (d * m) : ℚ))) =
      ∑ s ∈ M.primeFactors.powerset, ∏ p ∈ s, (-1 / h p) := by
    rw [← Finset.sum_filter_add_sum_filter_not M.divisors Squarefree]
    have h_not_sq : (∑ m ∈ M.divisors.filter (fun m => ¬ Squarefree m),
        (Nat.totient d : ℚ) * ((ArithmeticFunction.moebius m : ℚ) / (Nat.totient (d * m) : ℚ))) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      have hnsq : ¬ Squarefree m := (Finset.mem_filter.mp hm).2
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
      simp
    rw [h_not_sq, add_zero]
    refine Finset.sum_bij (fun m _ => m.primeFactors) ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hm.1) hM.ne'
    · intro m₁ hm₁ m₂ hm₂ h12
      rw [Finset.mem_filter] at hm₁ hm₂
      rw [← Nat.prod_primeFactors_of_squarefree hm₁.2,
          ← Nat.prod_primeFactors_of_squarefree hm₂.2, h12]
    · intro s hs
      rw [Finset.mem_powerset] at hs
      let m := ∏ p ∈ s, p
      have hsq : Squarefree m := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro p hp hpp
        have hp_mem : p ∈ s := by
          have := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff id).mp (dvd_trans (dvd_mul_right p p) hpp)
          obtain ⟨q, hqs, hq⟩ := this
          have hq_prime := (Nat.mem_primeFactors.mp (hs hqs)).1
          rwa [(Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hq]
        have h1 : m = p * ∏ q ∈ s.erase p, q := (Finset.mul_prod_erase s id hp_mem).symm
        rw [h1] at hpp
        have hp_dvd : p ∣ ∏ q ∈ s.erase p, q := (mul_dvd_mul_iff_left hp.ne_zero).mp hpp
        obtain ⟨q, hqs, hq⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff id).mp hp_dvd
        have hq_prime := (Nat.mem_primeFactors.mp (hs (Finset.mem_of_mem_erase hqs))).1
        have hpq := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hq
        exact (Finset.mem_erase.mp hqs).1 hpq.symm
      have hm_dvd : m ∣ M := by
        dsimp [m]
        clear hsq
        induction s using Finset.induction_on with
        | empty => simp
        | insert p s hps ih_s =>
          rw [Finset.prod_insert hps]
          have hp_mem : p ∈ M.primeFactors := hs (Finset.mem_insert_self p s)
          have hp_prime := (Nat.mem_primeFactors.mp hp_mem).1
          have hp_dvd : p ∣ M := (Nat.mem_primeFactors.mp hp_mem).2.1
          have hs_dvd : (∏ q ∈ s, q) ∣ M :=
            ih_s (fun q hq => hs (Finset.mem_insert_of_mem hq))
          have hcop_ps : Nat.Coprime p (∏ q ∈ s, q) := by
            rw [hp_prime.coprime_iff_not_dvd]
            intro hdvd
            obtain ⟨q, hqs, hq⟩ := ((Nat.prime_iff.mp hp_prime).dvd_finsetProd_iff id).mp hdvd
            have hq_prime := (Nat.mem_primeFactors.mp (hs (Finset.mem_insert_of_mem hqs))).1
            exact hps ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hq ▸ hqs)
          exact hcop_ps.mul_dvd_of_dvd_of_dvd hp_dvd hs_dvd
      have hm_pf : m.primeFactors = s := by
        ext p
        rw [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hpm, _⟩
          obtain ⟨q, hqs, hq⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff id).mp hpm
          have hq_prime := (Nat.mem_primeFactors.mp (hs hqs)).1
          rwa [(Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hq]
        · intro hps
          have hp_prime := (Nat.mem_primeFactors.mp (hs hps)).1
          refine ⟨hp_prime, Finset.dvd_prod_of_mem _ hps, ?_⟩
          exact Finset.prod_ne_zero_iff.mpr fun q hq =>
            (Nat.mem_primeFactors.mp (hs hq)).1.ne_zero
      refine ⟨m, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hm_dvd, hM.ne'⟩, hsq⟩, hm_pf⟩
    · intro m hm
      rw [Finset.mem_filter] at hm
      rw [h_tot_mul m hm.1 hm.2]
      have hmoeb : (ArithmeticFunction.moebius m : ℚ) = (-1 : ℚ) ^ m.primeFactors.card := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hm.2]
        have hcf : ArithmeticFunction.cardFactors m = m.primeFactors.card := by
          have hm_pos : 0 < m := Nat.pos_of_mem_divisors hm.1
          rw [ArithmeticFunction.cardFactors_apply]
          have hnodup : m.primeFactorsList.Nodup :=
            (Nat.squarefree_iff_nodup_primeFactorsList hm_pos.ne').mp hm.2
          have h_pf : m.primeFactorsList.toFinset = m.primeFactors := by
            ext q
            simp [Nat.mem_primeFactorsList hm_pos.ne', Nat.mem_primeFactors, hm_pos.ne']
          rw [← h_pf, List.toFinset_card_of_nodup hnodup]
        rw [hcf]
        push_cast
        rfl
      have htot_d_ne : (Nat.totient d : ℚ) ≠ 0 := htot_d.ne'
      have hprod_ne : (∏ p ∈ m.primeFactors, h p) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
        have hp_pf : p ∈ M.primeFactors :=
          Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hm.1) hM.ne' hp
        linarith [h_pos p hp_pf]
      rw [hmoeb]
      calc (Nat.totient d : ℚ) * ((-1 : ℚ) ^ m.primeFactors.card /
            ((Nat.totient d : ℚ) * ∏ p ∈ m.primeFactors, h p))
          = (-1 : ℚ) ^ m.primeFactors.card / ∏ p ∈ m.primeFactors, h p := by
            field_simp [htot_d_ne, hprod_ne]
        _ = (∏ _p ∈ m.primeFactors, (-1 : ℚ)) / ∏ p ∈ m.primeFactors, h p := by
            simp [Finset.prod_const]
        _ = ∏ p ∈ m.primeFactors, (-1 / h p) := by
            rw [← Finset.prod_div_distrib]
  rw [h_sum_eq, ← Finset.prod_one_add]
  refine Finset.prod_nonneg fun p hp => ?_
  have hp1 := h_pos p hp
  have h1 : (-1 : ℚ) / h p ≥ -1 := by
    rw [ge_iff_le, neg_div, neg_le_neg_iff]
    exact div_le_one_of_le₀ hp1 (by linarith)
  linarith

private lemma card_divisors_le_cyc (G : Type*) [Group G] [Fintype G] :
    (Fintype.card G).divisors.card ≤ Arxiv.«2604.08040».cyc G := by
  let N := Fintype.card G
  have hN_pos : 0 < N := Fintype.card_pos
  let c : ℕ → ℕ := fun k =>
    (Finset.univ.filter (fun H : {H : Subgroup G // IsCyclic H} => Fintype.card H.1 = k)).card
  have hcyc : Arxiv.«2604.08040».cyc G = ∑ k ∈ N.divisors, c k := by
    rw [Arxiv.«2604.08040».cyc, Nat.card_eq_fintype_card, ← Finset.card_univ]
    conv_lhs =>
      rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
        (t := N.divisors) (g := fun H : {H : Subgroup G // IsCyclic H} => Fintype.card H.1)
        (fun H _ => Nat.mem_divisors.mpr ⟨by
          change Fintype.card H.1 ∣ Fintype.card G
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
          exact Subgroup.card_subgroup_dvd_card H.1, hN_pos.ne'⟩)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.card_eq_sum_ones]
  let S : ℕ → ℚ := fun d => ((roots G d).card : ℚ) - (d : ℚ)
  have hS_nonneg : ∀ d ∈ N.divisors, (0 : ℚ) ≤ S d := by
    intro d hd
    have hd_dvd : d ∣ N := Nat.dvd_of_mem_divisors hd
    have hd_roots : d ∣ (roots G d).card := frobenius_dvd_card N rfl d hd_dvd
    have hroots_pos : 0 < (roots G d).card := Finset.card_pos.mpr ⟨1, by rw [mem_roots, one_pow]⟩
    have hle : d ≤ (roots G d).card := Nat.le_of_dvd hroots_pos hd_roots
    dsimp [S]
    linarith [show (d : ℚ) ≤ ((roots G d).card : ℚ) by exact_mod_cast hle]
  let h : ℕ → ℚ := fun k => (Nat.totient k : ℚ) * ((c k : ℚ) - 1)
  have h_sum_h : ∀ d : ℕ, 0 < d → ∑ j ∈ d.divisors, h j = S d := by
    intro d hd
    dsimp [h, S]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    have h1 : (∑ j ∈ d.divisors, (Nat.totient j : ℚ) * (c j : ℚ)) = ((roots G d).card : ℚ) := by
      exact_mod_cast (card_roots_eq_sum_totient_mul_cycCount (G := G) hd).symm
    have h2 : (∑ j ∈ d.divisors, (Nat.totient j : ℚ)) = (d : ℚ) := by
      exact_mod_cast Nat.sum_totient d
    rw [h1, h2]
  have h_moeb : ∀ k ∈ N.divisors, h k =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℚ) * S d := by
    intro k hk
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)).mp
      (fun n hn => h_sum_h n hn) k hk_pos
    rw [← hm, Nat.sum_divisorsAntidiagonal' (f := fun a b => (ArithmeticFunction.moebius a : ℚ) * S b)]
  have h_diff_nonneg : (0 : ℚ) ≤ (Arxiv.«2604.08040».cyc G : ℚ) - (N.divisors.card : ℚ) := by
    have h_eq1 : (Arxiv.«2604.08040».cyc G : ℚ) - (N.divisors.card : ℚ) =
        ∑ k ∈ N.divisors, ((c k : ℚ) - 1) := by
      rw [hcyc, Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h_eq1]
    have h_eq2 : (∑ k ∈ N.divisors, ((c k : ℚ) - 1)) =
        ∑ k ∈ N.divisors, ∑ d ∈ k.divisors,
          S d * ((ArithmeticFunction.moebius (k / d) : ℚ) / (Nat.totient k : ℚ)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
      have htot_pos : (0 : ℚ) < (Nat.totient k : ℚ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hk_pos)
      have h_ck : (c k : ℚ) - 1 = h k / (Nat.totient k : ℚ) := by
        dsimp [h]
        field_simp [htot_pos.ne']
      rw [h_ck, h_moeb k hk, Finset.sum_div]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [h_eq2]
    have h_swap : (∑ k ∈ N.divisors, ∑ d ∈ k.divisors,
          S d * ((ArithmeticFunction.moebius (k / d) : ℚ) / (Nat.totient k : ℚ))) =
        ∑ d ∈ N.divisors, S d * ∑ k ∈ N.divisors.filter (d ∣ ·),
          (ArithmeticFunction.moebius (k / d) : ℚ) / (Nat.totient k : ℚ) := by
      have h_lhs : (∑ k ∈ N.divisors, ∑ d ∈ k.divisors,
            S d * ((ArithmeticFunction.moebius (k / d) : ℚ) / (Nat.totient k : ℚ))) =
          ∑ k ∈ N.divisors, ∑ d ∈ N.divisors,
            if d ∣ k then S d * ((ArithmeticFunction.moebius (k / d) : ℚ) / (Nat.totient k : ℚ)) else 0 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨fun ⟨hdk, _⟩ => ⟨⟨dvd_trans hdk (Nat.dvd_of_mem_divisors hk), hN_pos.ne'⟩, hdk⟩,
          fun ⟨_, hdk⟩ => ⟨hdk, (Nat.pos_of_mem_divisors hk).ne'⟩⟩
      rw [h_lhs, Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_filter]
    rw [h_swap]
    refine Finset.sum_nonneg fun d hd => ?_
    refine mul_nonneg (hS_nonneg d hd) ?_
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_dvd : d ∣ N := Nat.dvd_of_mem_divisors hd
    have hM_pos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN_pos hd_dvd) hd_pos
    have h_bij : (∑ k ∈ N.divisors.filter (d ∣ ·),
          (ArithmeticFunction.moebius (k / d) : ℚ) / (Nat.totient k : ℚ)) =
        ∑ m ∈ (N / d).divisors,
          (ArithmeticFunction.moebius m : ℚ) / (Nat.totient (d * m) : ℚ) := by
      refine Finset.sum_bij (fun k _ => k / d) ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_filter] at hk
        rw [Nat.mem_divisors]
        refine ⟨?_, hM_pos.ne'⟩
        rw [← Nat.mul_dvd_mul_iff_left hd_pos, Nat.mul_div_cancel' hk.2, Nat.mul_div_cancel' hd_dvd]
        exact Nat.dvd_of_mem_divisors hk.1
      · intro k₁ hk₁ k₂ hk₂ h12
        rw [Finset.mem_filter] at hk₁ hk₂
        rw [← Nat.mul_div_cancel' hk₁.2, ← Nat.mul_div_cancel' hk₂.2, h12]
      · intro m hm
        have hm_dvd : m ∣ N / d := Nat.dvd_of_mem_divisors hm
        refine ⟨d * m, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hN_pos.ne'⟩, dvd_mul_right d m⟩, ?_⟩
        · exact (Nat.mul_dvd_of_dvd_div hd_dvd hm_dvd)
        · exact Nat.mul_div_cancel_left m hd_pos
      · intro k hk
        rw [Finset.mem_filter] at hk
        rw [Nat.mul_div_cancel' hk.2]
    rw [h_bij]
    exact euler_sum_nonneg d (N / d) hd_pos hM_pos
  have hq : (N.divisors.card : ℚ) ≤ (Arxiv.«2604.08040».cyc G : ℚ) := by linarith
  exact_mod_cast hq

private lemma squarefree_of_cyc_lt {G : Type*} [Group G] [Fintype G]
    (ht : 2 ≤ Arxiv.«2604.08040».numPrimeFactors G)
    (hcyc : Arxiv.«2604.08040».cyc G < 5 * 2 ^ (Arxiv.«2604.08040».numPrimeFactors G - 2)) :
    Squarefree (Fintype.card G) := by
  by_contra hnsq
  let N := Fintype.card G
  have hN_pos : 0 < N := Fintype.card_pos
  have h_ex : ∃ p ∈ N.primeFactors, 2 ≤ N.factorization p := by
    by_contra h_all
    push_neg at h_all
    apply hnsq
    rw [Nat.squarefree_iff_factorization_le_one hN_pos.ne']
    intro p
    by_cases hp : p ∈ N.primeFactors
    · exact Nat.lt_succ_iff.mp (h_all p hp)
    · rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])]
      omega
  obtain ⟨p, hp_mem, hp_ge2⟩ := h_ex
  have hdiv_card : N.divisors.card = ∏ q ∈ N.primeFactors, (N.factorization q + 1) :=
    Nat.card_divisors hN_pos.ne'
  have hprod_ge : 3 * 2 ^ (N.primeFactors.card - 1) ≤ N.divisors.card := by
    rw [hdiv_card, ← Finset.mul_prod_erase N.primeFactors (fun q => N.factorization q + 1) hp_mem]
    have h1 : 3 ≤ N.factorization p + 1 := by omega
    have h2 : 2 ^ (N.primeFactors.card - 1) ≤
        ∏ q ∈ N.primeFactors.erase p, (N.factorization q + 1) := by
      have hcard_erase : (N.primeFactors.erase p).card = N.primeFactors.card - 1 :=
        Finset.card_erase_of_mem hp_mem
      rw [← hcard_erase, ← Finset.prod_const]
      refine Finset.prod_le_prod' fun q hq => ?_
      have hq_mem : q ∈ N.primeFactors := Finset.mem_of_mem_erase hq
      have hq_pos : 1 ≤ N.factorization q :=
        (Nat.mem_primeFactors.mp hq_mem).1.factorization_pos_of_dvd hN_pos.ne'
          (Nat.mem_primeFactors.mp hq_mem).2.1
      omega
    exact Nat.mul_le_mul h1 h2
  have ht_eq : Arxiv.«2604.08040».numPrimeFactors G = N.primeFactors.card := rfl
  have hpow_eq : 3 * 2 ^ (N.primeFactors.card - 1) = 6 * 2 ^ (N.primeFactors.card - 2) := by
    have hsub : N.primeFactors.card - 1 = (N.primeFactors.card - 2) + 1 := by
      rw [← ht_eq]; omega
    rw [hsub, pow_succ]
    ring
  have hle_cyc := card_divisors_le_cyc G
  rw [ht_eq] at hcyc
  rw [hpow_eq] at hprod_ge
  have h56 : 5 * 2 ^ (N.primeFactors.card - 2) < 6 * 2 ^ (N.primeFactors.card - 2) := by
    nlinarith [Nat.one_le_pow (N.primeFactors.card - 2) 2 (by decide)]
  linarith

private lemma cyc_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : Arxiv.«2604.08040».cyc G = Arxiv.«2604.08040».cyc H := by
  unfold Arxiv.«2604.08040».cyc
  refine Nat.card_congr ?_
  refine
    { toFun := fun L => ⟨L.1.map e.toMonoidHom, by
        letI := L.2
        exact isCyclic_of_surjective _ (e.toMonoidHom.subgroupMap_surjective L.1)⟩
      invFun := fun L => ⟨L.1.map e.symm.toMonoidHom, by
        letI := L.2
        exact isCyclic_of_surjective _ (e.symm.toMonoidHom.subgroupMap_surjective L.1)⟩
      left_inv := fun L => Subtype.ext (by
        ext x
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          simpa using hz
        · intro hx
          exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩)
      right_inv := fun L => Subtype.ext (by
        ext x
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          simpa using hz
        · intro hx
          exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩) }

private lemma zpowers_eq_of_orderOf_dvd_prime {N : Type*} [Group N] [Fintype N] [IsCyclic N]
    {x y : N} {p : ℕ} (hp : p.Prime) (hx : orderOf x = p) (hy : orderOf y = p) :
    y ∈ Subgroup.zpowers x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := N)
  have hg_ord : orderOf g = Fintype.card N := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hx_dvd : p ∣ Fintype.card N := hx ▸ orderOf_dvd_card
  have hx_pow : x ∈ Subgroup.zpowers (g ^ (Fintype.card N / p)) := by
    obtain ⟨a, ha⟩ := hg x
    have ha' : g ^ a = x := ha
    have hpow : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    rw [← ha', ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hg_ord] at hpow
    have hdvd : (Fintype.card N : ℤ) ∣ a * p := hpow
    have h1 : (Fintype.card N / p : ℤ) ∣ a := by
      have hN_eq : (Fintype.card N : ℤ) = (Fintype.card N / p : ℤ) * p := by
        exact_mod_cast (Nat.div_mul_cancel hx_dvd).symm
      rw [hN_eq] at hdvd
      exact Int.dvd_of_mul_dvd_mul_right (Int.natCast_ne_zero.mpr hp.ne_zero) hdvd
    obtain ⟨b, hb⟩ := h1
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨b, ?_⟩
    rw [← ha', hb, zpow_mul, ← Int.natCast_ediv, zpow_natCast]
  have hy_pow : y ∈ Subgroup.zpowers (g ^ (Fintype.card N / p)) := by
    obtain ⟨a, ha⟩ := hg y
    have ha' : g ^ a = y := ha
    have hpow : y ^ p = 1 := hy ▸ pow_orderOf_eq_one y
    rw [← ha', ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hg_ord] at hpow
    have hdvd : (Fintype.card N : ℤ) ∣ a * p := hpow
    have h1 : (Fintype.card N / p : ℤ) ∣ a := by
      have hN_eq : (Fintype.card N : ℤ) = (Fintype.card N / p : ℤ) * p := by
        exact_mod_cast (Nat.div_mul_cancel hx_dvd).symm
      rw [hN_eq] at hdvd
      exact Int.dvd_of_mul_dvd_mul_right (Int.natCast_ne_zero.mpr hp.ne_zero) hdvd
    obtain ⟨b, hb⟩ := h1
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨b, ?_⟩
    rw [← ha', hb, zpow_mul, ← Int.natCast_ediv, zpow_natCast]
  have hcard_x : Fintype.card (Subgroup.zpowers x) = p := by rw [Fintype.card_zpowers, hx]
  have hcard_g : Fintype.card (Subgroup.zpowers (g ^ (Fintype.card N / p))) = p := by
    rw [Fintype.card_zpowers, orderOf_pow, hg_ord,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hx_dvd), Nat.div_div_self hx_dvd Fintype.card_pos.ne']
  have h_eq : Subgroup.zpowers x = Subgroup.zpowers (g ^ (Fintype.card N / p)) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx_pow) (by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard_x, hcard_g])
  rw [h_eq]
  exact hy_pow

private lemma five_mul_pow_le_cyc_semidirect {N H : Type*} [Group N] [Fintype N] [IsCyclic N]
    [Group H] [Fintype H] [IsCyclic H] (φ : H →* MulAut N) (hφ : ∃ h : H, φ h ≠ 1)
    (hsq_N : Squarefree (Fintype.card N)) (hsq_H : Squarefree (Fintype.card H))
    (hcop : Nat.Coprime (Fintype.card N) (Fintype.card H))
    (ht : 2 ≤ (Fintype.card N).primeFactors.card + (Fintype.card H).primeFactors.card) :
    5 * 2 ^ ((Fintype.card N).primeFactors.card + (Fintype.card H).primeFactors.card - 2) ≤
      Arxiv.«2604.08040».cyc (N ⋊[φ] H) := by
  let m := Fintype.card N
  let k := Fintype.card H
  have hm_pos : 0 < m := Fintype.card_pos
  have hk_pos : 0 < k := Fintype.card_pos
  obtain ⟨gN, hgN⟩ := IsCyclic.exists_generator (α := N)
  obtain ⟨gH, hgH⟩ := IsCyclic.exists_generator (α := H)
  have hgN_ord : orderOf gN = m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgN, Nat.card_eq_fintype_card]
  have hgH_ord : orderOf gH = k := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgH, Nat.card_eq_fintype_card]
  have hφ_gH : φ gH ≠ 1 := by
    intro h1
    obtain ⟨h, hh⟩ := hφ
    obtain ⟨a, rfl⟩ := hgH h
    apply hh
    rw [map_zpow, h1, one_zpow]
  obtain ⟨q, hq_prime, hq_dvd_ord⟩ :=
    Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.mp hφ_gH)
  have hord_dvd_k : orderOf (φ gH) ∣ k := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, ← hgH_ord, pow_orderOf_eq_one, map_one]
  have hq_dvd_k : q ∣ k := dvd_trans hq_dvd_ord hord_dvd_k
  have hq_mem : q ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_k, hk_pos.ne'⟩
  let h₀ : H := gH ^ (k / q)
  have hh₀_ne : φ h₀ ≠ 1 := by
    intro h1
    dsimp [h₀] at h1
    rw [map_pow] at h1
    have hdvd : orderOf (φ gH) ∣ k / q := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hq_dvd_kq : q ∣ k / q := dvd_trans hq_dvd_ord hdvd
    have hqq : q * q ∣ k := by
      have hk_eq : k = q * (k / q) := (Nat.mul_div_cancel' hq_dvd_k).symm
      rw [hk_eq]
      exact mul_dvd_mul_left q hq_dvd_kq
    exact (Nat.prime_iff.mp hq_prime).not_unit (hsq_H q hqq)
  have hh₀_ord : orderOf h₀ = q := by
    dsimp [h₀]
    rw [orderOf_pow, hgH_ord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hq_dvd_k),
      Nat.div_div_self hq_dvd_k hk_pos.ne']
  have hφ_gN : φ h₀ gN ≠ gN := by
    intro h1
    apply hh₀_ne
    ext x
    obtain ⟨a, rfl⟩ := hgN x
    rw [map_zpow, h1, MulAut.one_apply]
  let diffN : N := φ h₀ gN * gN⁻¹
  have hdiffN_ne : diffN ≠ 1 := by
    intro h1
    exact hφ_gN (eq_of_mul_inv_eq_one h1)
  obtain ⟨p, hp_prime, hp_dvd_ord⟩ :=
    Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.mp hdiffN_ne)
  have hp_dvd_m : p ∣ m := dvd_trans hp_dvd_ord orderOf_dvd_card
  have hp_mem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_m, hm_pos.ne'⟩
  let n₀ : N := gN ^ (m / p)
  have hn₀_ord : orderOf n₀ = p := by
    dsimp [n₀]
    rw [orderOf_pow, hgN_ord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hp_dvd_m),
      Nat.div_div_self hp_dvd_m hm_pos.ne']
  have hn₀_ne : φ h₀ n₀ ≠ n₀ := by
    intro h1
    dsimp [n₀] at h1
    have hpow : diffN ^ (m / p) = 1 := by
      dsimp [diffN]
      letI : CommGroup N := IsCyclic.commGroup
      rw [mul_pow, inv_pow, ← map_pow, h1, mul_inv_cancel]
    have hdvd : orderOf diffN ∣ m / p := orderOf_dvd_iff_pow_eq_one.mpr hpow
    have hp_dvd_mp : p ∣ m / p := dvd_trans hp_dvd_ord hdvd
    have hpp : p * p ∣ m := by
      have hm_eq : m = p * (m / p) := (Nat.mul_div_cancel' hp_dvd_m).symm
      rw [hm_eq]
      exact mul_dvd_mul_left p hp_dvd_mp
    exact (Nat.prime_iff.mp hp_prime).not_unit (hsq_N p hpp)
  have hp_ne_two : p ≠ 2 := by
    rintro rfl
    have h1 : (φ h₀ n₀) ^ 2 = 1 := by
      rw [← map_pow, ← hn₀_ord, pow_orderOf_eq_one, map_one]
    have hord_dvd : orderOf (φ h₀ n₀) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hne1 : φ h₀ n₀ ≠ 1 := by
      intro h0
      have : n₀ = 1 := (φ h₀).injective (h0.trans (map_one _).symm)
      rw [this, orderOf_one] at hn₀_ord
      omega
    have hord2 : orderOf (φ h₀ n₀) = 2 := by
      rcases Nat.dvd_prime Nat.prime_two |>.mp hord_dvd with h | h
      · exfalso; exact hne1 (orderOf_eq_one_iff.mp h)
      · exact h
    have hmem_z : φ h₀ n₀ ∈ Subgroup.zpowers n₀ :=
      zpowers_eq_of_orderOf_dvd_prime Nat.prime_two hn₀_ord hord2
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hmem_z
    have ha' : n₀ ^ a = φ h₀ n₀ := ha
    have h_eq : φ h₀ n₀ = n₀ := by
      have h2z : n₀ ^ (2 : ℤ) = 1 := by
        rw [zpow_ofNat, ← hn₀_ord, pow_orderOf_eq_one]
      rcases Int.emod_two_eq_zero_or_one a with h0 | h1
      · obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero h0
        exfalso
        apply hne1
        rw [← ha', hb, zpow_mul, h2z, one_zpow]
      · have h2 : a = 1 + 2 * (a / 2) := by omega
        rw [← ha', h2, zpow_add, zpow_one, zpow_mul, h2z, one_zpow, mul_one]
    exact hn₀_ne h_eq
  have hp_ge3 : 3 ≤ p := by
    have := hp_prime.two_le
    omega
  -- Now define H_d, C_d, and the injective map!
  let Hd : ℕ → Subgroup H := fun d => Subgroup.zpowers (gH ^ (k / d))
  let Cd : ℕ → Subgroup N := fun d =>
    { carrier := {n : N | ∀ h ∈ Hd d, φ h n = n}
      mul_mem' := fun ha hb h hh => by rw [map_mul, ha h hh, hb h hh]
      one_mem' := fun _ _ => map_one _
      inv_mem' := fun ha h hh => by rw [map_inv, ha h hh] }
  let c : ℕ → ℕ := fun d => Fintype.card (Cd d)
  let u : ℕ → ℕ := fun d => m / c d
  let h_gen : ℕ → H := fun d => gH ^ (k / d)
  have hh_gen_ord : ∀ d ∈ k.divisors, orderOf (h_gen d) = d := by
    intro d hd
    have hd_dvd : d ∣ k := Nat.dvd_of_mem_divisors hd
    dsimp [h_gen]
    rw [orderOf_pow, hgH_ord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd_dvd),
      Nat.div_div_self hd_dvd hk_pos.ne']
  have hk_gen_exists : ∀ d a : ℕ, a ∈ (c d).divisors →
      ∃ x : N, x ∈ Cd d ∧ orderOf x = a := by
    intro d a ha
    haveI : IsCyclic (Cd d) := Subgroup.isCyclic (Cd d)
    obtain ⟨gC, hgC⟩ := IsCyclic.exists_generator (α := Cd d)
    have hgC_ord : orderOf gC = c d := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hgC, Nat.card_eq_fintype_card]
    have ha_dvd : a ∣ c d := Nat.dvd_of_mem_divisors ha
    have hc_pos : 0 < c d := Fintype.card_pos
    refine ⟨(gC ^ (c d / a) : Cd d).1, (gC ^ (c d / a)).2, ?_⟩
    rw [Subgroup.orderOf_coe, orderOf_pow, hgC_ord,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd ha_dvd), Nat.div_div_self ha_dvd hc_pos.ne']
  let k_gen : ∀ (d : ℕ) (a : ℕ), a ∈ (c d).divisors → N :=
    fun d a ha => Classical.choose (hk_gen_exists d a ha)
  have hk_gen_mem : ∀ d a ha, k_gen d a ha ∈ Cd d :=
    fun d a ha => (Classical.choose_spec (hk_gen_exists d a ha)).1
  have hk_gen_ord : ∀ d a ha, orderOf (k_gen d a ha) = a :=
    fun d a ha => (Classical.choose_spec (hk_gen_exists d a ha)).2
  let Dom := Σ d : {d // d ∈ k.divisors}, (N ⧸ Cd d.1) × {a // a ∈ (c d.1).divisors}
  let mkGen : Dom → N ⋊[φ] H := fun ⟨d, xbar, a⟩ =>
    let x := Quotient.out xbar
    SemidirectProduct.inl (k_gen d.1 a.1 a.2) *
      (SemidirectProduct.inl x * SemidirectProduct.inr (h_gen d.1) *
        (SemidirectProduct.inl x)⁻¹)
  let F : Dom → {L : Subgroup (N ⋊[φ] H) // IsCyclic L} := fun p =>
    ⟨Subgroup.zpowers (mkGen p), inferInstance⟩
  have hcomm_gen : ∀ (d : {d // d ∈ k.divisors}) (x : N) (a : {a // a ∈ (c d.1).divisors}),
      Commute (SemidirectProduct.inl (k_gen d.1 a.1 a.2) : N ⋊[φ] H)
        (SemidirectProduct.inl x * SemidirectProduct.inr (h_gen d.1) *
          (SemidirectProduct.inl x)⁻¹) := by
    intro d x a
    letI : CommGroup N := IsCyclic.commGroup
    have hfix : φ (h_gen d.1) (k_gen d.1 a.1 a.2) = k_gen d.1 a.1 a.2 :=
      hk_gen_mem d.1 a.1 a.2 (h_gen d.1) (Subgroup.mem_zpowers (h_gen d.1))
    ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.left_inl, SemidirectProduct.left_inr,
        SemidirectProduct.right_inl, SemidirectProduct.right_inr,
        SemidirectProduct.inv_left, SemidirectProduct.inv_right,
        map_one, MulAut.one_apply, map_inv, mul_one, one_mul, hfix, inv_one]
      ac_rfl
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
        SemidirectProduct.right_inr, SemidirectProduct.inv_right,
        inv_one, mul_one, one_mul]
  have hord_mkGen : ∀ pt : Dom, orderOf (mkGen pt) = pt.2.2.1 * pt.1.1 := by
    intro ⟨d, xbar, a⟩
    let x := Quotient.out xbar
    have h1 : orderOf (SemidirectProduct.inl (k_gen d.1 a.1 a.2) : N ⋊[φ] H) = a.1 := by
      rw [orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective]
      exact hk_gen_ord d.1 a.1 a.2
    have h2 : orderOf ((SemidirectProduct.inl x : N ⋊[φ] H) * SemidirectProduct.inr (h_gen d.1) *
        (SemidirectProduct.inl x)⁻¹) = d.1 := by
      have hconj : (SemidirectProduct.inl x : N ⋊[φ] H) * SemidirectProduct.inr (h_gen d.1) *
          (SemidirectProduct.inl x)⁻¹ =
          (MulAut.conj (SemidirectProduct.inl x)) (SemidirectProduct.inr (h_gen d.1)) := rfl
      rw [hconj, MulEquiv.orderOf_eq,
        orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective]
      exact hh_gen_ord d.1 d.2
    have ha_dvd_m : a.1 ∣ m := dvd_trans (Nat.dvd_of_mem_divisors a.2) (by
      change Fintype.card (Cd d.1) ∣ Fintype.card N
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card (Cd d.1))
    have hd_dvd_k : d.1 ∣ k := Nat.dvd_of_mem_divisors d.2
    have hcop_ad : Nat.Coprime a.1 d.1 := hcop.coprime_dvd_left ha_dvd_m |>.coprime_dvd_right hd_dvd_k
    exact (hcomm_gen d x a).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [h1, h2]; exact hcop_ad) |>.trans
      (by rw [h1, h2])
  have hF_inj : Function.Injective F := by
    rintro ⟨d₁, xbar₁, a₁⟩ ⟨d₂, xbar₂, a₂⟩ hF
    have hcard_eq : Nat.card (Subgroup.zpowers (mkGen ⟨d₁, xbar₁, a₁⟩)) =
        Nat.card (Subgroup.zpowers (mkGen ⟨d₂, xbar₂, a₂⟩)) := by
      have hF' : Subgroup.zpowers (mkGen ⟨d₁, xbar₁, a₁⟩) =
          Subgroup.zpowers (mkGen ⟨d₂, xbar₂, a₂⟩) := congrArg Subtype.val hF
      rw [hF']
    simp only [Nat.card_zpowers, hord_mkGen] at hcard_eq
    have ha₁_dvd : a₁.1 ∣ m := dvd_trans (Nat.dvd_of_mem_divisors a₁.2) (by
      change Fintype.card (Cd d₁.1) ∣ Fintype.card N
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card (Cd d₁.1))
    have ha₂_dvd : a₂.1 ∣ m := dvd_trans (Nat.dvd_of_mem_divisors a₂.2) (by
      change Fintype.card (Cd d₂.1) ∣ Fintype.card N
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card (Cd d₂.1))
    have hd₁_dvd : d₁.1 ∣ k := Nat.dvd_of_mem_divisors d₁.2
    have hd₂_dvd : d₂.1 ∣ k := Nat.dvd_of_mem_divisors d₂.2
    have ha_eq : a₁.1 = a₂.1 := by
      have h1 : Nat.gcd (a₁.1 * d₁.1) m = a₁.1 := by
        rw [Nat.gcd_comm, (hcop.symm.coprime_dvd_left hd₁_dvd).gcd_mul_right_cancel_right,
          Nat.gcd_comm]
        exact Nat.gcd_eq_left ha₁_dvd
      have h2 : Nat.gcd (a₂.1 * d₂.1) m = a₂.1 := by
        rw [Nat.gcd_comm, (hcop.symm.coprime_dvd_left hd₂_dvd).gcd_mul_right_cancel_right,
          Nat.gcd_comm]
        exact Nat.gcd_eq_left ha₂_dvd
      rw [← h1, ← h2, hcard_eq]
    have hd_eq : d₁.1 = d₂.1 := by
      have h1 : Nat.gcd (a₁.1 * d₁.1) k = d₁.1 := by
        rw [mul_comm, Nat.gcd_comm, (hcop.coprime_dvd_left ha₁_dvd).gcd_mul_right_cancel_right,
          Nat.gcd_comm]
        exact Nat.gcd_eq_left hd₁_dvd
      have h2 : Nat.gcd (a₂.1 * d₂.1) k = d₂.1 := by
        rw [mul_comm, Nat.gcd_comm, (hcop.coprime_dvd_left ha₂_dvd).gcd_mul_right_cancel_right,
          Nat.gcd_comm]
        exact Nat.gcd_eq_left hd₂_dvd
      rw [← h1, ← h2, hcard_eq]
    have hd_sub : d₁ = d₂ := Subtype.ext hd_eq
    subst hd_sub
    have ha_sub : a₁ = a₂ := Subtype.ext ha_eq
    subst ha_sub
    let x₁ := Quotient.out xbar₁
    let x₂ := Quotient.out xbar₂
    let z₁ : N ⋊[φ] H :=
      SemidirectProduct.inl x₁ * SemidirectProduct.inr (h_gen d₁.1) * (SemidirectProduct.inl x₁)⁻¹
    let z₂ : N ⋊[φ] H :=
      SemidirectProduct.inl x₂ * SemidirectProduct.inr (h_gen d₁.1) * (SemidirectProduct.inl x₂)⁻¹
    have hd_pos : 0 < d₁.1 := Nat.pos_of_mem_divisors d₁.2
    have ha_pos : 0 < a₁.1 := Nat.pos_of_mem_divisors a₁.2
    have hcop_ad : Nat.Coprime a₁.1 d₁.1 := hcop.coprime_dvd_left ha₁_dvd |>.coprime_dvd_right hd₁_dvd
    have hbez : (a₁.1 : ℤ) * Nat.gcdA a₁.1 d₁.1 + (d₁.1 : ℤ) * Nat.gcdB a₁.1 d₁.1 = 1 := by
      have := Nat.gcd_eq_gcd_ab a₁.1 d₁.1
      rw [hcop_ad.gcd_eq_one] at this
      omega
    have hk_pow : (k_gen d₁.1 a₁.1 a₁.2) ^ a₁.1 = 1 := by
      have hord := hk_gen_ord d₁.1 a₁.1 a₁.2
      calc (k_gen d₁.1 a₁.1 a₁.2) ^ a₁.1
          = (k_gen d₁.1 a₁.1 a₁.2) ^ orderOf (k_gen d₁.1 a₁.1 a₁.2) := by rw [hord]
        _ = 1 := pow_orderOf_eq_one _
    have hh_pow : (h_gen d₁.1) ^ d₁.1 = 1 := by
      have hord := hh_gen_ord d₁.1 d₁.2
      calc (h_gen d₁.1) ^ d₁.1 = (h_gen d₁.1) ^ orderOf (h_gen d₁.1) := by rw [hord]
        _ = 1 := pow_orderOf_eq_one _
    have hz₁_pow_a : (mkGen ⟨d₁, xbar₁, a₁⟩) ^ a₁.1 = z₁ ^ a₁.1 := by
      change (SemidirectProduct.inl (k_gen d₁.1 a₁.1 a₁.2) * z₁) ^ a₁.1 = z₁ ^ a₁.1
      rw [(hcomm_gen d₁ x₁ a₁).mul_pow, ← map_pow, hk_pow, map_one, one_mul]
    have hz₁_mem : z₁ ∈ Subgroup.zpowers (mkGen ⟨d₁, xbar₁, a₁⟩) := by
      have hz₁_ord : z₁ ^ d₁.1 = 1 := by
        dsimp [z₁]
        rw [conj_pow, ← map_pow, hh_pow, map_one, mul_one, mul_inv_cancel]
      have hz₁_eq : z₁ = (mkGen ⟨d₁, xbar₁, a₁⟩) ^ ((a₁.1 : ℤ) * Nat.gcdA a₁.1 d₁.1) := by
        rw [zpow_mul, zpow_natCast, hz₁_pow_a, ← zpow_natCast, ← zpow_mul]
        have h1 : (a₁.1 : ℤ) * Nat.gcdA a₁.1 d₁.1 = 1 - (d₁.1 : ℤ) * Nat.gcdB a₁.1 d₁.1 := by
          omega
        rw [h1, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hz₁_ord, one_zpow, inv_one, mul_one]
      rw [hz₁_eq]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    have hF' : Subgroup.zpowers (mkGen ⟨d₁, xbar₁, a₁⟩) =
        Subgroup.zpowers (mkGen ⟨d₁, xbar₂, a₁⟩) := congrArg Subtype.val hF
    rw [hF', Subgroup.mem_zpowers_iff] at hz₁_mem
    obtain ⟨r, hr⟩ := hz₁_mem
    have hr_pow_d : (mkGen ⟨d₁, xbar₂, a₁⟩) ^ (r * (d₁.1 : ℤ)) = 1 := by
      rw [zpow_mul, hr, zpow_natCast]
      dsimp [z₁]
      rw [conj_pow, ← map_pow, hh_pow, map_one, mul_one, mul_inv_cancel]
    have hdvd_rd : ((a₁.1 * d₁.1 : ℕ) : ℤ) ∣ r * (d₁.1 : ℤ) := by
      rw [← hord_mkGen ⟨d₁, xbar₂, a₁⟩, orderOf_dvd_iff_zpow_eq_one]
      exact hr_pow_d
    have ha_dvd_r : (a₁.1 : ℤ) ∣ r := by
      rw [Int.natCast_mul] at hdvd_rd
      exact Int.dvd_of_mul_dvd_mul_right (Int.natCast_ne_zero.mpr hd_pos.ne') hdvd_rd
    obtain ⟨s, rfl⟩ := ha_dvd_r
    have hz₁_eq_z₂ : z₁ = z₂ := by
      have hz₂_pow_a : (mkGen ⟨d₁, xbar₂, a₁⟩) ^ a₁.1 = z₂ ^ a₁.1 := by
        change (SemidirectProduct.inl (k_gen d₁.1 a₁.1 a₁.2) * z₂) ^ a₁.1 = z₂ ^ a₁.1
        rw [(hcomm_gen d₁ x₂ a₁).mul_pow, ← map_pow, hk_pow, map_one, one_mul]
      have hz₁_pow : z₁ = z₂ ^ ((a₁.1 : ℤ) * s) := by
        rw [← hr, zpow_mul, zpow_natCast, hz₂_pow_a, ← zpow_natCast, ← zpow_mul]
      have hright : z₁.right = (z₂ ^ ((a₁.1 : ℤ) * s)).right := congrArg SemidirectProduct.right hz₁_pow
      have hz₁_r : z₁.right = h_gen d₁.1 := by simp [z₁]
      have hz₂_r : (z₂ ^ ((a₁.1 : ℤ) * s)).right = (h_gen d₁.1) ^ ((a₁.1 : ℤ) * s) := by
        have hright_hom : (z₂ ^ ((a₁.1 : ℤ) * s)).right = z₂.right ^ ((a₁.1 : ℤ) * s) :=
          map_zpow SemidirectProduct.rightHom z₂ _
        rw [hright_hom]
        simp [z₂]
      rw [hz₁_r, hz₂_r] at hright
      have hz₂_eq : z₂ ^ ((a₁.1 : ℤ) * s) = z₂ := by
        dsimp [z₂]
        have hconj : (SemidirectProduct.inl x₂ : N ⋊[φ] H) * SemidirectProduct.inr (h_gen d₁.1) *
            (SemidirectProduct.inl x₂)⁻¹ =
            (MulAut.conj (SemidirectProduct.inl x₂)) (SemidirectProduct.inr (h_gen d₁.1)) := rfl
        rw [hconj, ← map_zpow, ← map_zpow, ← hright]
      rw [hz₁_pow, hz₂_eq]
    have hconj_eq : (SemidirectProduct.inl (x₂⁻¹ * x₁) : N ⋊[φ] H) *
        SemidirectProduct.inr (h_gen d₁.1) =
        SemidirectProduct.inr (h_gen d₁.1) * SemidirectProduct.inl (x₂⁻¹ * x₁) := by
      calc (SemidirectProduct.inl (x₂⁻¹ * x₁) : N ⋊[φ] H) * SemidirectProduct.inr (h_gen d₁.1)
          = (SemidirectProduct.inl x₂)⁻¹ * z₁ * SemidirectProduct.inl x₁ := by
            dsimp [z₁]
            rw [map_mul, map_inv]
            group
        _ = (SemidirectProduct.inl x₂)⁻¹ * z₂ * SemidirectProduct.inl x₁ := by rw [hz₁_eq_z₂]
        _ = SemidirectProduct.inr (h_gen d₁.1) * SemidirectProduct.inl (x₂⁻¹ * x₁) := by
            dsimp [z₂]
            rw [map_mul, map_inv]
            group
    have hleft : ((SemidirectProduct.inl (x₂⁻¹ * x₁) : N ⋊[φ] H) *
        SemidirectProduct.inr (h_gen d₁.1)).left =
        (SemidirectProduct.inr (h_gen d₁.1) * SemidirectProduct.inl (x₂⁻¹ * x₁)).left :=
      congrArg SemidirectProduct.left hconj_eq
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply, mul_one, one_mul] at hleft
    have hmem_Cd : x₂⁻¹ * x₁ ∈ Cd d₁.1 := by
      have hpow_nat : ∀ n : ℕ, (φ (h_gen d₁.1) ^ n) (x₂⁻¹ * x₁) = x₂⁻¹ * x₁ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih_n => rw [pow_succ', MulAut.mul_apply, ih_n, ← hleft]
      have hinv : (φ (h_gen d₁.1))⁻¹ (x₂⁻¹ * x₁) = x₂⁻¹ * x₁ := by
        apply (φ (h_gen d₁.1)).injective
        rw [MulAut.apply_inv_self, ← hleft]
      have hpow_inv_nat : ∀ n : ℕ, ((φ (h_gen d₁.1))⁻¹ ^ n) (x₂⁻¹ * x₁) = x₂⁻¹ * x₁ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih_n => rw [pow_succ', MulAut.mul_apply, ih_n, hinv]
      intro h hh
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      change (φ ((h_gen d₁.1) ^ b)) (x₂⁻¹ * x₁) = x₂⁻¹ * x₁
      rw [map_zpow]
      rcases b with n | n
      · exact hpow_nat n
      · rw [zpow_negSucc, ← inv_pow]
        exact hpow_inv_nat (n + 1)
    have hq_eq : (QuotientGroup.mk x₁ : N ⧸ Cd d₁.1) = QuotientGroup.mk x₂ := by
      rw [eq_comm, QuotientGroup.eq]
      exact hmem_Cd
    have hx₁_out : QuotientGroup.mk x₁ = xbar₁ := Quotient.out_eq xbar₁
    have hx₂_out : QuotientGroup.mk x₂ = xbar₂ := Quotient.out_eq xbar₂
    rw [← hx₁_out, ← hx₂_out, hq_eq]
  have hdom_le : Fintype.card Dom ≤ Arxiv.«2604.08040».cyc (N ⋊[φ] H) := by
    let eProd : N ⋊[φ] H ≃ N × H :=
      { toFun := fun p => (p.left, p.right)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    letI : Fintype (N ⋊[φ] H) := Fintype.ofEquiv (N × H) eProd.symm
    rw [Arxiv.«2604.08040».cyc, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective F hF_inj
  have hquot_card : ∀ d : ℕ, Fintype.card (N ⧸ Cd d) = u d := by
    intro d
    have hmul : Fintype.card (N ⧸ Cd d) * c d = m := by
      change Fintype.card (N ⧸ Cd d) * Fintype.card (Cd d) = Fintype.card N
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (Cd d)).symm
    have hc_pos : 0 < c d := Fintype.card_pos
    dsimp [u]
    rw [← hmul, Nat.mul_div_cancel _ hc_pos]
  have hdom_card : Fintype.card Dom = ∑ d ∈ k.divisors, u d * (c d).divisors.card := by
    simp only [Dom, Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe]
    rw [← Finset.sum_coe_sort k.divisors]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hquot_card d]
  have hc_dvd : ∀ d : ℕ, c d ∣ m := fun d => by
    change Fintype.card (Cd d) ∣ Fintype.card N
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card (Cd d)
  have hu_mul_c : ∀ d : ℕ, u d * c d = m := fun d => Nat.div_mul_cancel (hc_dvd d)
  have hu_not_even : ∀ d : ℕ, ¬ 2 ∣ u d := by
    intro d h2u
    have h2m : 2 ∣ m := dvd_trans h2u (Dvd.intro _ (hu_mul_c d))
    let n₂ : N := gN ^ (m / 2)
    have hn₂_ord : orderOf n₂ = 2 := by
      dsimp [n₂]
      rw [orderOf_pow, hgN_ord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd h2m),
        Nat.div_div_self h2m hm_pos.ne']
    have hn₂_mem : n₂ ∈ Cd d := by
      intro h _
      have h1 : (φ h n₂) ^ 2 = 1 := by
        rw [← map_pow, ← hn₂_ord, pow_orderOf_eq_one, map_one]
      have hord_dvd : orderOf (φ h n₂) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
      have hne1 : φ h n₂ ≠ 1 := by
        intro h0
        have : n₂ = 1 := (φ h).injective (h0.trans (map_one _).symm)
        rw [this, orderOf_one] at hn₂_ord
        omega
      have hord2 : orderOf (φ h n₂) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with h0 | h0
        · exfalso; exact hne1 (orderOf_eq_one_iff.mp h0)
        · exact h0
      have hmem_z : φ h n₂ ∈ Subgroup.zpowers n₂ :=
        zpowers_eq_of_orderOf_dvd_prime Nat.prime_two hn₂_ord hord2
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hmem_z
      have ha' : n₂ ^ a = φ h n₂ := ha
      have h2z : n₂ ^ (2 : ℤ) = 1 := by
        rw [zpow_ofNat, ← hn₂_ord, pow_orderOf_eq_one]
      rcases Int.emod_two_eq_zero_or_one a with h0 | h1
      · obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero h0
        exfalso
        apply hne1
        rw [← ha', hb, zpow_mul, h2z, one_zpow]
      · have h2 : a = 1 + 2 * (a / 2) := by omega
        rw [← ha', h2, zpow_add, zpow_one, zpow_mul, h2z, one_zpow, mul_one]
    have h2c : 2 ∣ c d := by
      have hdvd : Fintype.card (Subgroup.zpowers n₂) ∣ Fintype.card (Cd d) := by
        have hle : Subgroup.zpowers n₂ ≤ Cd d := Subgroup.zpowers_le.mpr hn₂_mem
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact Subgroup.card_dvd_of_le hle
      rwa [Fintype.card_zpowers, hn₂_ord] at hdvd
    have h4m : 2 * 2 ∣ m := by
      rw [← hu_mul_c d]
      exact mul_dvd_mul h2u h2c
    exact (Nat.prime_iff.mp Nat.prime_two).not_isUnit (hsq_N 2 h4m)
  have hu_ge_pow : ∀ d : ℕ, 2 ^ (u d).primeFactors.card ≤ u d := by
    intro d
    have hu_pos : 0 < u d := by
      have := hu_mul_c d
      nlinarith [Fintype.card_pos (α := Cd d)]
    have hsq_u : Squarefree (u d) := hsq_N.squarefree_of_dvd (Dvd.intro _ (hu_mul_c d))
    have hu_prod : u d = ∏ r ∈ (u d).primeFactors, r :=
      (Nat.prod_primeFactors_of_squarefree hsq_u).symm
    conv_rhs => rw [hu_prod]
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' fun r hr => ?_
    have hr_prime := (Nat.mem_primeFactors.mp hr).1
    have hr_ne2 : r ≠ 2 := by
      rintro rfl
      exact hu_not_even d (Nat.mem_primeFactors.mp hr).2.1
    have := hr_prime.two_le
    omega
  have hc_div_card : ∀ d : ℕ, (c d).divisors.card = 2 ^ (c d).primeFactors.card := by
    intro d
    have hc_pos : 0 < c d := Fintype.card_pos
    have hsq_c : Squarefree (c d) := hsq_N.squarefree_of_dvd (hc_dvd d)
    rw [Nat.card_divisors hc_pos.ne', ← Finset.prod_const]
    refine Finset.prod_congr rfl fun r hr => ?_
    have hle : (c d).factorization r ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hc_pos.ne').mp hsq_c r
    have hge : 1 ≤ (c d).factorization r :=
      (Nat.mem_primeFactors.mp hr).1.factorization_pos_of_dvd hc_pos.ne'
        (Nat.mem_primeFactors.mp hr).2.1
    omega
  have hpf_sum : ∀ d : ℕ, (u d).primeFactors.card + (c d).primeFactors.card = m.primeFactors.card := by
    intro d
    have hu_pos : 0 < u d := by
      have := hu_mul_c d
      nlinarith [Fintype.card_pos (α := Cd d)]
    have hc_pos : 0 < c d := Fintype.card_pos
    have hcop_uc : Nat.Coprime (u d) (c d) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
      have hrr : r * r ∣ m := by
        rw [← hu_mul_c d]
        exact mul_dvd_mul (dvd_trans hr_dvd (Nat.gcd_dvd_left _ _))
          (dvd_trans hr_dvd (Nat.gcd_dvd_right _ _))
      exact (Nat.prime_iff.mp hr_prime).not_unit (hsq_N r hrr)
    rw [← Finset.card_union_of_disjoint hcop_uc.disjoint_primeFactors,
      ← Nat.primeFactors_mul hu_pos.ne' hc_pos.ne', hu_mul_c d]
  have hterm_ge : ∀ d : ℕ, 2 ^ m.primeFactors.card ≤ u d * (c d).divisors.card := by
    intro d
    rw [hc_div_card d, ← hpf_sum d, pow_add]
    exact Nat.mul_le_mul (hu_ge_pow d) le_rfl
  have hterm_ge_q : ∀ d ∈ k.divisors, q ∣ d →
      3 * 2 ^ m.primeFactors.card ≤ 2 * (u d * (c d).divisors.card) := by
    intro d hd hqd
    have hd_dvd : d ∣ k := Nat.dvd_of_mem_divisors hd
    have hh₀_mem : h₀ ∈ Hd d := by
      have hdiv : k / d ∣ k / q := by
        rw [← Nat.mul_dvd_mul_iff_left (Nat.pos_of_mem_divisors hd),
          mul_comm d (k / d), Nat.div_mul_cancel hd_dvd]
        have hd_eq : d = q * (d / q) := (Nat.mul_div_cancel' hqd).symm
        have hkd : d * (k / q) = k * (d / q) := by
          calc d * (k / q) = (q * (d / q)) * (k / q) := by conv_lhs => rw [hd_eq]
            _ = (q * (k / q)) * (d / q) := by ring
            _ = k * (d / q) := by rw [Nat.mul_div_cancel' hq_dvd_k]
        rw [hkd]
        exact dvd_mul_right k (d / q)
      obtain ⟨t, ht_eq⟩ := hdiv
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨(t : ℤ), ?_⟩
      dsimp [h₀]
      rw [zpow_natCast, ← pow_mul, ← ht_eq]
    have hn₀_not : n₀ ∉ Cd d := fun hmem => hn₀_ne (hmem h₀ hh₀_mem)
    have hp_not_c : ¬ p ∣ c d := by
      intro hpc
      haveI : IsCyclic (Cd d) := Subgroup.isCyclic (Cd d)
      obtain ⟨gC, hgC⟩ := IsCyclic.exists_generator (α := Cd d)
      have hgC_ord : orderOf gC = c d := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hgC, Nat.card_eq_fintype_card]
      let yC : Cd d := gC ^ (c d / p)
      have hyC_ord : orderOf (yC : N) = p := by
        rw [Subgroup.orderOf_coe]
        dsimp [yC]
        rw [orderOf_pow, hgC_ord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpc),
          Nat.div_div_self hpc (Fintype.card_pos (α := Cd d)).ne']
      have hmem_z : n₀ ∈ Subgroup.zpowers (yC : N) :=
        zpowers_eq_of_orderOf_dvd_prime hp_prime hyC_ord hn₀_ord
      have hle : Subgroup.zpowers (yC : N) ≤ Cd d := Subgroup.zpowers_le.mpr yC.2
      exact hn₀_not (hle hmem_z)
    have hp_dvd_u : p ∣ u d := by
      have hp_dvd_uc : p ∣ u d * c d := (hu_mul_c d).symm ▸ hp_dvd_m
      exact (hp_prime.dvd_mul.mp hp_dvd_uc).resolve_right hp_not_c
    have hu_eq : u d = p * (u d / p) := (Nat.mul_div_cancel' hp_dvd_u).symm
    have hup_ge : 2 ^ ((u d).primeFactors.card - 1) ≤ u d / p := by
      have hu_pos : 0 < u d := by
        have := hu_mul_c d
        nlinarith [Fintype.card_pos (α := Cd d)]
      have hup_pos : 0 < u d / p := Nat.div_pos (Nat.le_of_dvd hu_pos hp_dvd_u) hp_prime.pos
      have hsq_up : Squarefree (u d / p) :=
        hsq_N.squarefree_of_dvd (dvd_trans (Nat.div_dvd_of_dvd hp_dvd_u) (Dvd.intro _ (hu_mul_c d)))
      have hpf_up : (u d / p).primeFactors.card = (u d).primeFactors.card - 1 := by
        have hcop_pup : Nat.Coprime p (u d / p) := by
          rw [hp_prime.coprime_iff_not_dvd]
          intro hdvd
          have hpp : p * p ∣ m := by
            rw [← hu_mul_c d, hu_eq]
            exact dvd_trans (mul_dvd_mul_left p hdvd) (dvd_mul_right _ _)
          exact (Nat.prime_iff.mp hp_prime).not_unit (hsq_N p hpp)
        have hpf_u : (u d).primeFactors = insert p (u d / p).primeFactors := by
          conv_lhs => rw [hu_eq]
          rw [Nat.primeFactors_mul hp_prime.ne_zero hup_pos.ne', hp_prime.primeFactors]
          simp
        rw [hpf_u, Finset.card_insert_of_notMem]
        · omega
        · intro hmem
          exact (hp_prime.coprime_iff_not_dvd.mp hcop_pup) (Nat.mem_primeFactors.mp hmem).2.1
      rw [← hpf_up]
      have hup_prod : u d / p = ∏ r ∈ (u d / p).primeFactors, r :=
        (Nat.prod_primeFactors_of_squarefree hsq_up).symm
      conv_rhs => rw [hup_prod]
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod' fun r hr => ?_
      have hr_prime := (Nat.mem_primeFactors.mp hr).1
      have hr_ne2 : r ≠ 2 := by
        rintro rfl
        exact hu_not_even d (dvd_trans (Nat.mem_primeFactors.mp hr).2.1 (Nat.div_dvd_of_dvd hp_dvd_u))
      have := hr_prime.two_le
      omega
    have hu_ge : 3 * 2 ^ (u d).primeFactors.card ≤ 2 * u d := by
      have hp_mem_u : p ∈ (u d).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_u, by
          have := hu_mul_c d; nlinarith [Fintype.card_pos (α := Cd d)]⟩
      have h1 : 1 ≤ (u d).primeFactors.card := Finset.card_pos.mpr ⟨p, hp_mem_u⟩
      have hpow_u : 2 ^ (u d).primeFactors.card = 2 * 2 ^ ((u d).primeFactors.card - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel h1, pow_add, pow_one]
        ring
      rw [hpow_u]
      conv_rhs => rw [hu_eq]
      calc 3 * (2 * 2 ^ ((u d).primeFactors.card - 1))
          = 6 * 2 ^ ((u d).primeFactors.card - 1) := by ring
        _ ≤ (2 * p) * (u d / p) := Nat.mul_le_mul (by omega) hup_ge
        _ = 2 * (p * (u d / p)) := by ring
    rw [hc_div_card d, ← hpf_sum d, pow_add]
    calc 3 * (2 ^ (u d).primeFactors.card * 2 ^ (c d).primeFactors.card)
        = (3 * 2 ^ (u d).primeFactors.card) * 2 ^ (c d).primeFactors.card := by ring
      _ ≤ (2 * u d) * 2 ^ (c d).primeFactors.card := Nat.mul_le_mul_right _ hu_ge
      _ = 2 * (u d * 2 ^ (c d).primeFactors.card) := by ring
  -- Partition k.divisors by q ∣ d
  have hdiv_k_card : k.divisors.card = 2 ^ k.primeFactors.card := by
    rw [Nat.card_divisors hk_pos.ne', ← Finset.prod_const]
    refine Finset.prod_congr rfl fun r hr => ?_
    have hle : k.factorization r ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hk_pos.ne').mp hsq_H r
    have hge : 1 ≤ k.factorization r :=
      (Nat.mem_primeFactors.mp hr).1.factorization_pos_of_dvd hk_pos.ne'
        (Nat.mem_primeFactors.mp hr).2.1
    omega
  have hq_bij : (k.divisors.filter (fun d => ¬ q ∣ d)).card =
      (k.divisors.filter (fun d => q ∣ d)).card := by
    refine Finset.card_bij (fun d _ => q * d) ?_ ?_ ?_
    · intro d hd
      rw [Finset.mem_filter] at hd
      have hd_dvd : d ∣ k := Nat.dvd_of_mem_divisors hd.1
      have hcop_qd : Nat.Coprime q d := hq_prime.coprime_iff_not_dvd.mpr hd.2
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hcop_qd.mul_dvd_of_dvd_of_dvd hq_dvd_k hd_dvd, hk_pos.ne'⟩,
         dvd_mul_right q d⟩
    · intro d₁ _ d₂ _ h12
      exact mul_left_cancel₀ hq_prime.ne_zero h12
    · intro d hd
      rw [Finset.mem_filter] at hd
      refine ⟨d / q, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨dvd_trans (Nat.div_dvd_of_dvd hd.2) (Nat.dvd_of_mem_divisors hd.1), hk_pos.ne'⟩, ?_⟩,
        Nat.mul_div_cancel' hd.2⟩
      intro hqd
      have hqq : q * q ∣ k := by
        have hd_eq : d = q * (d / q) := (Nat.mul_div_cancel' hd.2).symm
        exact dvd_trans (hd_eq ▸ mul_dvd_mul_left q hqd) (Nat.dvd_of_mem_divisors hd.1)
      exact (Nat.prime_iff.mp hq_prime).not_unit (hsq_H q hqq)
  have hpart_sum : (k.divisors.filter (fun d => ¬ q ∣ d)).card +
      (k.divisors.filter (fun d => q ∣ d)).card = 2 ^ k.primeFactors.card := by
    rw [← hdiv_k_card, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
      Finset.card_eq_sum_ones, add_comm]
    exact Finset.sum_filter_add_sum_filter_not k.divisors (fun d => q ∣ d) (fun _ => 1)
  have h1_k : 1 ≤ k.primeFactors.card := Finset.card_pos.mpr ⟨q, hq_mem⟩
  have hfilt_card : (k.divisors.filter (fun d => ¬ q ∣ d)).card = 2 ^ (k.primeFactors.card - 1) ∧
      (k.divisors.filter (fun d => q ∣ d)).card = 2 ^ (k.primeFactors.card - 1) := by
    have hpow_k : 2 ^ k.primeFactors.card = 2 * 2 ^ (k.primeFactors.card - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel h1_k, pow_add, pow_one]
      ring
    omega
  have h_final : 2 * (5 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 2)) ≤
      2 * Fintype.card Dom := by
    rw [hdom_card, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not k.divisors (fun d => q ∣ d)]
    have hsum1 : 3 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 1) ≤
        ∑ d ∈ k.divisors.filter (fun d => q ∣ d), 2 * (u d * (c d).divisors.card) := by
      have hle : ∑ d ∈ k.divisors.filter (fun d => q ∣ d), 3 * 2 ^ m.primeFactors.card ≤
          ∑ d ∈ k.divisors.filter (fun d => q ∣ d), 2 * (u d * (c d).divisors.card) := by
        refine Finset.sum_le_sum fun d hd => hterm_ge_q d (Finset.mem_filter.mp hd).1
          (Finset.mem_filter.mp hd).2
      rw [Finset.sum_const, smul_eq_mul, hfilt_card.2] at hle
      have hpow_eq : 2 ^ (k.primeFactors.card - 1) * (3 * 2 ^ m.primeFactors.card) =
          3 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 1) := by
        have hsub : m.primeFactors.card + k.primeFactors.card - 1 =
            m.primeFactors.card + (k.primeFactors.card - 1) := by omega
        rw [hsub, pow_add]
        ring
      linarith
    have hsum2 : 2 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 1) ≤
        ∑ d ∈ k.divisors.filter (fun d => ¬ q ∣ d), 2 * (u d * (c d).divisors.card) := by
      have hle : ∑ d ∈ k.divisors.filter (fun d => ¬ q ∣ d), 2 * 2 ^ m.primeFactors.card ≤
          ∑ d ∈ k.divisors.filter (fun d => ¬ q ∣ d), 2 * (u d * (c d).divisors.card) := by
        refine Finset.sum_le_sum fun d _ => Nat.mul_le_mul_left 2 (hterm_ge d)
      rw [Finset.sum_const, smul_eq_mul, hfilt_card.1] at hle
      have hpow_eq : 2 ^ (k.primeFactors.card - 1) * (2 * 2 ^ m.primeFactors.card) =
          2 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 1) := by
        have hsub : m.primeFactors.card + k.primeFactors.card - 1 =
            m.primeFactors.card + (k.primeFactors.card - 1) := by omega
        rw [hsub, pow_add]
        ring
      linarith
    have hpow_tot : 2 * (5 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 2)) =
        3 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 1) +
        2 * 2 ^ (m.primeFactors.card + k.primeFactors.card - 1) := by
      have ht' : 2 ≤ m.primeFactors.card + k.primeFactors.card := ht
      have hsub : m.primeFactors.card + k.primeFactors.card - 1 =
          (m.primeFactors.card + k.primeFactors.card - 2) + 1 := by omega
      rw [hsub, pow_succ]
      ring
    linarith
  exact Nat.le_of_mul_le_mul_left (le_trans h_final (Nat.mul_le_mul_left 2 hdom_le)) (by decide)

theorem OMA.solution : type_of% @Arxiv.«2604.08040».nilpotent_of_cyc_lt := by
  intro G _ _ hcyc
  by_cases ht : Arxiv.«2604.08040».numPrimeFactors G ≤ 1
  · exact isNilpotent_of_numPrimeFactors_le_one ht
  have ht2 : 2 ≤ Arxiv.«2604.08040».numPrimeFactors G := by omega
  have hsq : Squarefree (Fintype.card G) := squarefree_of_cyc_lt ht2 hcyc
  have hsq' : Squarefree (Nat.card G) := by rwa [Nat.card_eq_fintype_card]
  have hz : IsZGroup G := IsZGroup.of_squarefree hsq'
  rw [isZGroup_iff_exists_mulEquiv] at hz
  obtain ⟨N, H, φ, e, hN_cyc, hH_cyc, hcop⟩ := hz
  by_cases htriv : ∀ h : H, φ h = 1
  · have hcomm : ∀ x y : N ⋊[φ] H, x * y = y * x := by
      intro ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
      letI : CommGroup N := IsCyclic.commGroup
      letI : CommGroup H := IsCyclic.commGroup
      ext
      · simp only [SemidirectProduct.mul_left, htriv h₁, htriv h₂, MulAut.one_apply]
        exact congrArg Subtype.val (mul_comm n₁ n₂)
      · simp only [SemidirectProduct.mul_right]
        exact congrArg Subtype.val (mul_comm h₁ h₂)
    have hcommG : ∀ x y : G, x * y = y * x := by
      intro x y
      apply e.injective
      rw [map_mul, map_mul, hcomm]
    letI : CommGroup G := { ‹Group G› with mul_comm := hcommG }
    exact CommGroup.isNilpotent (G := G)
  · push Not at htriv
    exfalso
    have hcyc_eq : Arxiv.«2604.08040».cyc G = Arxiv.«2604.08040».cyc (N ⋊[φ] H) := cyc_congr e
    let eProd : N ⋊[φ] H ≃ N × H :=
      { toFun := fun p => (p.left, p.right)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    letI : Fintype (N ⋊[φ] H) := Fintype.ofEquiv (N × H) eProd.symm
    have hcard_eq : Fintype.card G = Fintype.card N * Fintype.card H := by
      rw [Fintype.card_congr e.toEquiv, Fintype.card_congr eProd, Fintype.card_prod]
    have hsq_mul : Squarefree (Fintype.card N * Fintype.card H) := hcard_eq ▸ hsq
    have hsq_N : Squarefree (Fintype.card N) := hsq_mul.of_mul_left
    have hsq_H : Squarefree (Fintype.card H) := hsq_mul.of_mul_right
    have hcop' : Nat.Coprime (Fintype.card N) (Fintype.card H) := by
      rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have ht_eq : Arxiv.«2604.08040».numPrimeFactors G =
        (Fintype.card N).primeFactors.card + (Fintype.card H).primeFactors.card := by
      unfold Arxiv.«2604.08040».numPrimeFactors
      rw [hcard_eq, Nat.primeFactors_mul Fintype.card_ne_zero Fintype.card_ne_zero,
        Finset.card_union_of_disjoint hcop'.disjoint_primeFactors]
    have hle := five_mul_pow_le_cyc_semidirect φ htriv hsq_N hsq_H hcop' (ht_eq ▸ ht2)
    rw [← ht_eq, ← hcyc_eq] at hle
    omega
