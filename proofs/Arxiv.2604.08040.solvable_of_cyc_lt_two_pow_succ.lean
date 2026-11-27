import FormalConjectures.Arxiv.«2604.08040».Conjecture5_5
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Proof of Arxiv.2604.08040.solvable_of_cyc_lt_two_pow_succ -/

section Frobenius

open Classical
open scoped Pointwise

private def powEqOneEquivSigma {G : Type*} [Group G] (a m : ℕ) (hcop : Nat.Coprime a m) :
    {x : G // x ^ (a * m) = 1} ≃
      Σ y : {y : G // y ^ m = 1},
        {u : Subgroup.centralizer ({y.1} : Set G) // (u : G) ^ a = 1} where
  toFun x :=
    let r : ℤ := Nat.gcdA a m
    let s : ℤ := Nat.gcdB a m
    let y : G := x.1 ^ ((a : ℤ) * r)
    let u : G := x.1 ^ ((m : ℤ) * s)
    have hxam : x.1 ^ ((a : ℤ) * (m : ℤ)) = 1 := by
      rw [← Int.natCast_mul, zpow_natCast]
      exact x.2
    have hy : y ^ m = 1 := by
      dsimp [y]
      rw [← zpow_natCast, ← zpow_mul, show (a : ℤ) * r * (m : ℤ) = (a : ℤ) * (m : ℤ) * r by ring,
        zpow_mul, hxam, one_zpow]
    have hyu : y * u = u * y := by
      dsimp [y, u]
      rw [← zpow_add, ← zpow_add, add_comm]
    have hu_mem : u ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hyu
    have hu : u ^ a = 1 := by
      dsimp [u]
      rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * s * (a : ℤ) = (a : ℤ) * (m : ℤ) * s by ring,
        zpow_mul, hxam, one_zpow]
    ⟨⟨y, hy⟩, ⟨⟨u, hu_mem⟩, hu⟩⟩
  invFun p :=
    have hcomm : Commute p.1.1 (p.2.1 : G) :=
      Subgroup.mem_centralizer_iff.mp p.2.1.2 p.1.1 (Set.mem_singleton _)
    have hpow : (p.1.1 * (p.2.1 : G)) ^ (a * m) = 1 := by
      rw [hcomm.mul_pow, mul_comm a m, pow_mul, p.1.2, one_pow, one_mul,
        mul_comm m a, pow_mul, p.2.2, one_pow]
    ⟨p.1.1 * (p.2.1 : G), hpow⟩
  left_inv x := by
    ext
    dsimp
    have hbez : (a : ℤ) * Nat.gcdA a m + (m : ℤ) * Nat.gcdB a m = 1 := by
      have h := Nat.gcd_eq_gcd_ab a m
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      exact h.symm
    rw [← zpow_add, hbez, zpow_one]
  right_inv p := by
    rcases p with ⟨⟨y, hy⟩, ⟨⟨u, hu_mem⟩, hu⟩⟩
    have hcomm : Commute y u :=
      Subgroup.mem_centralizer_iff.mp hu_mem y (Set.mem_singleton _)
    have hbez : (a : ℤ) * Nat.gcdA a m + (m : ℤ) * Nat.gcdB a m = 1 := by
      have h := Nat.gcd_eq_gcd_ab a m
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      exact h.symm
    have h1 : (y * u) ^ ((a : ℤ) * Nat.gcdA a m) = y := by
      rw [hcomm.mul_zpow, zpow_mul u, show u ^ (a : ℤ) = 1 from by rw [zpow_natCast, hu],
        one_zpow, mul_one]
      have hsub : (a : ℤ) * Nat.gcdA a m = 1 - (m : ℤ) * Nat.gcdB a m := by linarith
      rw [hsub, zpow_sub, zpow_one, zpow_mul, show y ^ (m : ℤ) = 1 from by rw [zpow_natCast, hy],
        one_zpow, inv_one, mul_one]
    have h2 : (y * u) ^ ((m : ℤ) * Nat.gcdB a m) = u := by
      rw [hcomm.mul_zpow, zpow_mul y, show y ^ (m : ℤ) = 1 from by rw [zpow_natCast, hy],
        one_zpow, one_mul]
      have hsub : (m : ℤ) * Nat.gcdB a m = 1 - (a : ℤ) * Nat.gcdA a m := by linarith
      rw [hsub, zpow_sub, zpow_one, zpow_mul, show u ^ (a : ℤ) = 1 from by rw [zpow_natCast, hu],
        one_zpow, inv_one, mul_one]
    have hy_eq : (⟨(y * u) ^ ((a : ℤ) * Nat.gcdA a m), by
        rw [← zpow_natCast, ← zpow_mul]
        have hxam : (y * u) ^ ((a : ℤ) * (m : ℤ)) = 1 := by
          rw [← Int.natCast_mul, zpow_natCast, hcomm.mul_pow, mul_comm a m, pow_mul, hy, one_pow,
            one_mul, mul_comm m a, pow_mul, hu, one_pow]
        rw [show (a : ℤ) * Nat.gcdA a m * (m : ℤ) = (a : ℤ) * (m : ℤ) * Nat.gcdA a m by ring,
          zpow_mul, hxam, one_zpow]⟩ : {y : G // y ^ m = 1}) = ⟨y, hy⟩ := Subtype.ext h1
    have h_heq : ∀ {y₁ y₂ : {y : G // y ^ m = 1}} (_ : y₁ = y₂)
        (u₁ : {u : Subgroup.centralizer ({y₁.1} : Set G) // (u : G) ^ a = 1})
        (u₂ : {u : Subgroup.centralizer ({y₂.1} : Set G) // (u : G) ^ a = 1}),
        (u₁ : G) = (u₂ : G) → HEq u₁ u₂ := by
      rintro y₁ _ rfl u₁ u₂ h
      exact heq_of_eq (Subtype.ext (Subtype.ext h))
    refine Sigma.ext hy_eq (h_heq hy_eq _ _ h2)

private lemma card_pow_eq_one_mul_coprime {G : Type*} [Group G] [Fintype G]
    (a m : ℕ) (hcop : Nat.Coprime a m) :
    Fintype.card {x : G // x ^ (a * m) = 1} =
      ∑ y : {y : G // y ^ m = 1},
        Fintype.card {u : Subgroup.centralizer ({y.1} : Set G) // (u : G) ^ a = 1} := by
  rw [Fintype.card_congr (powEqOneEquivSigma a m hcop), Fintype.card_sigma]

private lemma card_pow_eq_one_eq_of_conj {G : Type*} [Group G] [Fintype G]
    (a : ℕ) (c : ConjAct G) (y : G) :
    Fintype.card {u : Subgroup.centralizer ({c • y} : Set G) // (u : G) ^ a = 1} =
      Fintype.card {u : Subgroup.centralizer ({y} : Set G) // (u : G) ^ a = 1} := by
  let g : G := ConjAct.ofConjAct c
  refine Fintype.card_congr ?_
  exact
    { toFun := fun ⟨⟨u, hu⟩, hua⟩ =>
        ⟨⟨g⁻¹ * u * g, by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          have hcz : c • y = g * y * g⁻¹ := ConjAct.smul_def c y
          have h1 := Subgroup.mem_centralizer_iff.mp hu (c • y) (Set.mem_singleton _)
          rw [hcz] at h1
          calc y * (g⁻¹ * u * g) = g⁻¹ * ((g * y * g⁻¹) * u) * g := by group
            _ = g⁻¹ * (u * (g * y * g⁻¹)) * g := by rw [h1]
            _ = (g⁻¹ * u * g) * y := by group⟩, by
          dsimp
          have hcp := conj_pow (a := g⁻¹) (b := u) (i := a)
          have hinv : g⁻¹ * u * (g⁻¹)⁻¹ = g⁻¹ * u * g := by simp
          rw [← hinv, hcp, hua]
          group⟩
      invFun := fun ⟨⟨u, hu⟩, hua⟩ =>
        ⟨⟨g * u * g⁻¹, by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          have hcz : c • y = g * y * g⁻¹ := ConjAct.smul_def c y
          have h1 := Subgroup.mem_centralizer_iff.mp hu y (Set.mem_singleton _)
          rw [hcz]
          calc (g * y * g⁻¹) * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
            _ = g * (u * y) * g⁻¹ := by rw [h1]
            _ = (g * u * g⁻¹) * (g * y * g⁻¹) := by group⟩, by
          dsimp
          rw [conj_pow, hua]
          group⟩
      left_inv := fun ⟨⟨u, hu⟩, hua⟩ => by ext; dsimp; group
      right_inv := fun ⟨⟨u, hu⟩, hua⟩ => by ext; dsimp; group }

private lemma card_stabilizer_conjAct {G : Type*} [Group G] [Fintype G] (y : G) :
    Fintype.card (MulAction.stabilizer (ConjAct G) y) =
      Fintype.card (Subgroup.centralizer ({y} : Set G)) := by
  refine Fintype.card_congr ?_
  exact
    { toFun := fun ⟨c, hc⟩ => ⟨ConjAct.ofConjAct c, by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have h : c • y = y := hc
        rw [ConjAct.smul_def c y] at h
        calc y * ConjAct.ofConjAct c =
            (ConjAct.ofConjAct c * y * (ConjAct.ofConjAct c)⁻¹) * ConjAct.ofConjAct c := by rw [h]
          _ = ConjAct.ofConjAct c * y := by group⟩
      invFun := fun ⟨g, hg⟩ => ⟨ConjAct.toConjAct g, by
        change ConjAct.toConjAct g • y = y
        rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
        have h1 := Subgroup.mem_centralizer_iff.mp hg y (Set.mem_singleton _)
        calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [h1]
          _ = y := by group⟩
      left_inv := fun ⟨c, _⟩ => by ext; simp
      right_inv := fun ⟨g, _⟩ => by ext; simp }

private lemma card_orbit_mul_centralizer {G : Type*} [Group G] [Fintype G] (y : G) :
    Fintype.card (MulAction.orbit (ConjAct G) y) *
        Fintype.card (Subgroup.centralizer ({y} : Set G)) = Fintype.card G := by
  rw [← card_stabilizer_conjAct y]
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) y
  simpa using h

private lemma dvd_pow_sub_of_dvd_mul {p a b k m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hdiv : p ^ a ∣ k * m) (hb : b = m.factorization p) :
    p ^ (a - b) ∣ k := by
  by_cases hab : a ≤ b
  · rw [Nat.sub_eq_zero_of_le hab, pow_zero]
    exact one_dvd _
  · have hba : b < a := Nat.lt_of_not_le hab
    have hpb : p ^ b ∣ m := by rw [hb]; exact Nat.ordProj_dvd m p
    have hndvd : ¬ p ∣ m / p ^ b := by
      rw [hb]
      exact Nat.not_dvd_ordCompl hp hm
    have hmul : p ^ b * (m / p ^ b) = m := Nat.mul_div_cancel' hpb
    rw [← hmul, ← mul_assoc] at hdiv
    have ha_eq : a = b + (a - b) := (Nat.add_sub_cancel' hba.le).symm
    rw [ha_eq, pow_add, mul_comm (p ^ b) (p ^ (a - b))] at hdiv
    have hdiv2 : p ^ (a - b) ∣ k * (m / p ^ b) := by
      rcases hdiv with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have hpos : 0 < p ^ b := pow_pos hp.pos b
      nlinarith
    have hcop : Nat.Coprime (p ^ (a - b)) (m / p ^ b) :=
      (hp.coprime_iff_not_dvd.mpr hndvd).pow_left _
    exact hcop.dvd_of_dvd_mul_right hdiv2

private lemma card_pow_eq_one_min_exp {G : Type*} [Group G] [Fintype G]
    (p a : ℕ) (hp : p.Prime) :
    Fintype.card {u : G // u ^ (p ^ a) = 1} =
      Fintype.card {u : G // u ^ (p ^ min a ((Fintype.card G).factorization p)) = 1} := by
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl G) fun u => ?_)
  constructor
  · intro hu
    have h1 : orderOf u ∣ p ^ a := orderOf_dvd_iff_pow_eq_one.mpr hu
    have h2 : orderOf u ∣ Fintype.card G := orderOf_dvd_card
    have hgcd : orderOf u ∣ Nat.gcd (p ^ a) (Fintype.card G) := Nat.dvd_gcd h1 h2
    have hgcd_dvd : Nat.gcd (p ^ a) (Fintype.card G) ∣
        p ^ min a ((Fintype.card G).factorization p) := by
      rw [← Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left (pow_ne_zero a hp.ne_zero))
        (pow_ne_zero _ hp.ne_zero)]
      intro q
      rw [Nat.factorization_gcd (pow_ne_zero a hp.ne_zero) Fintype.card_ne_zero,
        Finsupp.inf_apply, hp.factorization_pow, hp.factorization_pow]
      by_cases hqp : q = p
      · subst hqp
        simp
      · simp [Ne.symm hqp]
    exact orderOf_dvd_iff_pow_eq_one.mp (hgcd.trans hgcd_dvd)
  · intro hu
    have h1 : orderOf u ∣ p ^ min a ((Fintype.card G).factorization p) :=
      orderOf_dvd_iff_pow_eq_one.mpr hu
    have h2 : p ^ min a ((Fintype.card G).factorization p) ∣ p ^ a :=
      Nat.pow_dvd_pow p (min_le_left _ _)
    exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans h2)

private lemma dvd_card_pow_eq_one_sylow_aux :
    ∀ (N : ℕ) (G : Type u) [Group G] [Fintype G],
      Fintype.card G = N → ∀ (p : ℕ), p.Prime →
        p ^ (N.factorization p) ∣ Fintype.card {x : G // x ^ (p ^ (N.factorization p)) = 1} := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro G _ _ hN p hp
    have hNpos : 0 < N := hN ▸ Fintype.card_pos
    have hNne : N ≠ 0 := hNpos.ne'
    set c := N.factorization p
    set m := N / p ^ c
    have hpc_dvd : p ^ c ∣ N := Nat.ordProj_dvd N p
    have hm_mul : p ^ c * m = N := Nat.mul_div_cancel' hpc_dvd
    have hm_ndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hNne
    have hcop : Nat.Coprime (p ^ c) m := (hp.coprime_iff_not_dvd.mpr hm_ndvd).pow_left _
    have hsum := card_pow_eq_one_mul_coprime (G := G) (p ^ c) m hcop
    have hlhs : Fintype.card {x : G // x ^ (p ^ c * m) = 1} = N := by
      rw [hm_mul, ← hN]
      exact Fintype.card_congr
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, pow_card_eq_one⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
    rw [hlhs] at hsum
    let f : G → ℕ := fun y =>
      Fintype.card {u : Subgroup.centralizer ({y} : Set G) // (u : G) ^ (p ^ c) = 1}
    have hsum2 : N = ∑ y ∈ Finset.univ.filter (fun y : G => y ^ m = 1), f y := by
      rw [hsum, ← Finset.sum_coe_sort (Finset.univ.filter (fun y : G => y ^ m = 1))]
      refine Fintype.sum_equiv (Equiv.subtypeEquiv (Equiv.refl G) fun y => by simp) _ _ fun y => rfl
    let S := Finset.univ.filter (fun y : G => y ^ m = 1)
    let S1 := S.filter (fun y : G => y ∈ Subgroup.center G)
    let S2 := S.filter (fun y : G => y ∉ Subgroup.center G)
    have hsplit : ∑ y ∈ S, f y = ∑ y ∈ S1, f y + ∑ y ∈ S2, f y := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun y : G => y ∈ Subgroup.center G)]
    have hS1 : ∑ y ∈ S1, f y = S1.card * Fintype.card {u : G // u ^ (p ^ c) = 1} := by
      have hconst : ∀ y ∈ S1, f y = Fintype.card {u : G // u ^ (p ^ c) = 1} := by
        intro y hy
        have hyZ : y ∈ Subgroup.center G := (Finset.mem_filter.mp hy).2
        have hcent : Subgroup.centralizer ({y} : Set G) = ⊤ := by
          ext z
          simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
            Subgroup.mem_top, iff_true]
          exact (Subgroup.mem_center_iff.mp hyZ z).symm
        dsimp [f]
        refine Fintype.card_congr ?_
        exact
          { toFun := fun ⟨u, hu⟩ => ⟨u.1, hu⟩
            invFun := fun ⟨u, hu⟩ => ⟨⟨u, hcent ▸ Subgroup.mem_top u⟩, hu⟩
            left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl }
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    have hS1_cop : Nat.Coprime S1.card (p ^ c) := by
      refine (hp.coprime_iff_not_dvd.mpr ?_).symm.pow_right _
      intro hdvd
      let Z_m : Subgroup (Subgroup.center G) :=
        { carrier := {y : Subgroup.center G | (y : G) ^ m = 1}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            change ((a : G) * (b : G)) ^ m = 1
            have hcomm : Commute (a : G) (b : G) := (Subgroup.mem_center_iff.mp a.2 (b : G)).symm
            rw [hcomm.mul_pow, ha, hb, mul_one]
          inv_mem' := fun {a} ha => by
            change ((a : G)⁻¹) ^ m = 1
            rw [inv_pow, ha, inv_one] }
      have hcard_Zm : Fintype.card Z_m = S1.card := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr ?_
        exact
          { toFun := fun ⟨⟨y, hyZ⟩, hym⟩ => ⟨y, by
              change y ^ m = 1 at hym
              simp [S1, S, hyZ, hym]⟩
            invFun := fun ⟨y, hy⟩ => ⟨⟨y, (Finset.mem_filter.mp hy).2⟩,
              (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2⟩
            left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl }
      rw [← hcard_Zm] at hdvd
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card p hdvd
      have hz_p : (z : G) ^ p = 1 := by
        have h1 : z ^ p = 1 := by rw [← hz, pow_orderOf_eq_one]
        exact congrArg (fun t : Z_m => ((t : Subgroup.center G) : G)) h1
      have hz_m : (z : G) ^ m = 1 := z.2
      have hcop_pm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hm_ndvd
      have hord_1 : orderOf (z : G) = 1 := by
        have h1 : orderOf (z : G) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hz_p
        have h2 : orderOf (z : G) ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hz_m
        exact Nat.dvd_one.mp (hcop_pm ▸ Nat.dvd_gcd h1 h2)
      have hz_eq_1 : (z : G) = 1 := orderOf_eq_one_iff.mp hord_1
      have hz_eq_1' : z = 1 := by ext; exact hz_eq_1
      rw [hz_eq_1', orderOf_one] at hz
      exact hp.ne_one hz.symm
    have hS2_dvd : p ^ c ∣ ∑ y ∈ S2, f y := by
      let orb := MulAction.orbitRel (ConjAct G) G
      rw [← Finset.sum_fiberwise_of_maps_to (g := Quotient.mk orb)
        (t := (Finset.univ : Finset (Quotient orb))) (fun _ _ => Finset.mem_univ _)]
      refine Finset.dvd_sum fun q _ => ?_
      by_cases hne : (S2.filter (fun y => Quotient.mk orb y = q)).Nonempty
      · obtain ⟨y₀, hy₀⟩ := hne
        have hy₀_S2 : y₀ ∈ S2 := (Finset.mem_filter.mp hy₀).1
        have hy₀_q : Quotient.mk orb y₀ = q := (Finset.mem_filter.mp hy₀).2
        have hy₀_m : y₀ ^ m = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy₀_S2).1).2
        have hy₀_nZ : y₀ ∉ Subgroup.center G := (Finset.mem_filter.mp hy₀_S2).2
        have hconst : ∀ y ∈ S2.filter (fun y => Quotient.mk orb y = q), f y = f y₀ := by
          intro y hy
          have hq : Quotient.mk orb y = Quotient.mk orb y₀ :=
            (Finset.mem_filter.mp hy).2.trans hy₀_q.symm
          obtain ⟨g, hg⟩ := Quotient.exact hq
          dsimp [f]
          rw [← hg, card_pow_eq_one_eq_of_conj]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
        have hfilt_eq : S2.filter (fun y => Quotient.mk orb y = q) =
            Finset.univ.filter (fun y : G => Quotient.mk orb y = q) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S2, S]
          constructor
          · intro h; exact h.2
          · intro hq
            have hq' : Quotient.mk orb y = Quotient.mk orb y₀ := hq.trans hy₀_q.symm
            obtain ⟨g, hg⟩ := Quotient.exact hq'
            change g • y₀ = y at hg
            refine ⟨⟨?_, ?_⟩, hq⟩
            · rw [← hg, ConjAct.smul_def, conj_pow, hy₀_m]
              group
            · intro hyZ
              apply hy₀_nZ
              have hcomm := Subgroup.mem_center_iff.mp hyZ (ConjAct.ofConjAct g)
              have hinv_eq : y = y₀ := by
                have hconj : ConjAct.ofConjAct g * y₀ * (ConjAct.ofConjAct g)⁻¹ = y := by
                  rw [← ConjAct.smul_def, hg]
                calc y = (ConjAct.ofConjAct g)⁻¹ * (ConjAct.ofConjAct g * y) := by group
                  _ = (ConjAct.ofConjAct g)⁻¹ * (y * ConjAct.ofConjAct g) := by rw [hcomm]
                  _ = (ConjAct.ofConjAct g)⁻¹ * (ConjAct.ofConjAct g * y₀ * (ConjAct.ofConjAct g)⁻¹) * ConjAct.ofConjAct g := by
                      rw [hconj]; group
                  _ = y₀ := by group
              rwa [← hinv_eq]
        have hcard_orb : (Finset.univ.filter (fun y : G => Quotient.mk orb y = q)).card =
            Fintype.card (MulAction.orbit (ConjAct G) y₀) := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr ?_
          exact
            { toFun := fun ⟨y, hy⟩ => ⟨y, by
                have hq' : Quotient.mk orb y = Quotient.mk orb y₀ :=
                  (Finset.mem_filter.mp hy).2.trans hy₀_q.symm
                exact Quotient.exact hq'⟩
              invFun := fun ⟨y, hy⟩ => ⟨y, by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact (Quotient.sound hy).trans hy₀_q⟩
              left_inv := fun ⟨_, _⟩ => rfl
              right_inv := fun ⟨_, _⟩ => rfl }
        rw [hfilt_eq, hcard_orb]
        set M := Fintype.card (Subgroup.centralizer ({y₀} : Set G))
        have hmul_N : Fintype.card (MulAction.orbit (ConjAct G) y₀) * M = N := by
          rw [← hN]
          exact card_orbit_mul_centralizer y₀
        have hM_lt : M < N := by
          rw [← hN]
          have hnot : ∃ g : G, g ∉ Subgroup.centralizer ({y₀} : Set G) := by
            by_contra h_all
            push Not at h_all
            apply hy₀_nZ
            rw [Subgroup.mem_center_iff]
            intro g
            exact (Subgroup.mem_centralizer_iff.mp (h_all g) y₀ (Set.mem_singleton _)).symm
          obtain ⟨g, hg⟩ := hnot
          exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective (by simpa using hg)
        set b := M.factorization p
        have hbc : b ≤ c := by
          have hM_dvd : M ∣ N := ⟨Fintype.card (MulAction.orbit (ConjAct G) y₀), by rw [mul_comm]; exact hmul_N.symm⟩
          exact (Nat.factorization_le_iff_dvd Fintype.card_ne_zero hNne).mpr hM_dvd p
        have hf_eq : f y₀ =
            Fintype.card {u : Subgroup.centralizer ({y₀} : Set G) // u ^ (p ^ b) = 1} := by
          dsimp [f]
          have h1 : Fintype.card {u : Subgroup.centralizer ({y₀} : Set G) // (u : G) ^ (p ^ c) = 1} =
              Fintype.card {u : Subgroup.centralizer ({y₀} : Set G) // u ^ (p ^ c) = 1} :=
            Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun u => by simp [Subtype.ext_iff])
          rw [h1]
          convert card_pow_eq_one_min_exp (G := Subgroup.centralizer ({y₀} : Set G)) p c hp
          rw [min_eq_right hbc]
        have hf_dvd : p ^ b ∣ f y₀ := by
          rw [hf_eq]
          have ih_M := ih M hM_lt (Subgroup.centralizer ({y₀} : Set G)) rfl p hp
          convert ih_M
        have horb_dvd : p ^ (c - b) ∣ Fintype.card (MulAction.orbit (ConjAct G) y₀) := by
          apply dvd_pow_sub_of_dvd_mul hp Fintype.card_ne_zero _ rfl
          rw [hmul_N]
          exact hpc_dvd
        have hmul_dvd := mul_dvd_mul horb_dvd hf_dvd
        rw [← pow_add, Nat.sub_add_cancel hbc] at hmul_dvd
        exact hmul_dvd
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
        exact dvd_zero _
    rw [hsum2, hsplit, hS1] at hpc_dvd
    have hS1_dvd : p ^ c ∣ S1.card * Fintype.card {u : G // u ^ (p ^ c) = 1} :=
      (Nat.dvd_add_left hS2_dvd).mp hpc_dvd
    exact hS1_cop.symm.dvd_of_dvd_mul_left hS1_dvd

private lemma dvd_card_pow_eq_one_prime_pow {G : Type*} [Group G] [Fintype G]
    (p a : ℕ) (hp : p.Prime) (ha : a ≤ (Fintype.card G).factorization p) :
    p ^ a ∣ Fintype.card {x : G // x ^ (p ^ a) = 1} := by
  set c := (Fintype.card G).factorization p
  suffices h : ∀ k a, a + k = c → p ^ a ∣ Fintype.card {x : G // x ^ (p ^ a) = 1} by
    exact h (c - a) a (Nat.add_sub_cancel' ha)
  intro k
  induction k with
  | zero =>
    intro a ha_eq
    rw [add_zero] at ha_eq
    subst ha_eq
    exact dvd_card_pow_eq_one_sylow_aux (Fintype.card G) G rfl p hp
  | succ k ih =>
    intro a ha_eq
    have ha1 : (a + 1) + k = c := by omega
    have ih1 := ih (a + 1) ha1
    let S_a1 := Finset.univ.filter (fun x : G => x ^ (p ^ (a + 1)) = 1)
    let S_a := Finset.univ.filter (fun x : G => x ^ (p ^ a) = 1)
    let A := Finset.univ.filter (fun x : G => orderOf x = p ^ (a + 1))
    have hpart : S_a1 = S_a ∪ A := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        S_a1, S_a, A, ← orderOf_dvd_iff_pow_eq_one]
      rw [Nat.dvd_prime_pow hp]
      constructor
      · rintro ⟨i, hi, hord⟩
        rcases eq_or_lt_of_le hi with rfl | hlt
        · right; exact hord
        · left; rw [hord]; exact Nat.pow_dvd_pow p (Nat.lt_succ_iff.mp hlt)
      · rintro (hdvd | hord)
        · obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow hp).mp hdvd
          exact ⟨i, hi.trans (Nat.le_succ a), hord⟩
        · exact ⟨a + 1, le_rfl, hord⟩
    have hdisj : Disjoint S_a A := by
      rw [Finset.disjoint_left]
      intro x hxS hxA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_a, A] at hxS hxA
      have hdvd : p ^ (a + 1) ∣ p ^ a := hxA ▸ orderOf_dvd_iff_pow_eq_one.mpr hxS
      have hle := (Nat.pow_le_pow_iff_right hp.one_lt).mp (Nat.le_of_dvd (pow_pos hp.pos a) hdvd)
      omega
    have hcard_eq : Fintype.card {x : G // x ^ (p ^ (a + 1)) = 1} = S_a.card + A.card := by
      rw [← Finset.card_union_of_disjoint hdisj, ← hpart, ← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl G) fun x => by simp [S_a1])
    have hA_dvd : p ^ a ∣ A.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Subgroup.zpowers)
        (t := A.image Subgroup.zpowers) (fun x hx => Finset.mem_image_of_mem _ hx)]
      refine Finset.dvd_sum fun H hH => ?_
      obtain ⟨x₀, hx₀A, rfl⟩ := Finset.mem_image.mp hH
      have hx₀_ord : orderOf x₀ = p ^ (a + 1) := (Finset.mem_filter.mp hx₀A).2
      have hfib : (A.filter (fun x => Subgroup.zpowers x = Subgroup.zpowers x₀)).card =
          Nat.totient (p ^ (a + 1)) := by
        have hset : (A.filter (fun x => Subgroup.zpowers x = Subgroup.zpowers x₀)).card =
            Fintype.card {x : Subgroup.zpowers x₀ // orderOf x = p ^ (a + 1)} := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr ?_
          exact
            { toFun := fun ⟨x, hx⟩ => ⟨⟨x, by
                have hzx : Subgroup.zpowers x = Subgroup.zpowers x₀ := (Finset.mem_filter.mp hx).2
                rw [← hzx]
                exact Subgroup.mem_zpowers x⟩, by
                simpa [Subgroup.orderOf_coe] using (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2⟩
              invFun := fun ⟨⟨x, hxH⟩, hxord⟩ => ⟨x, by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
                have hxord' : orderOf x = p ^ (a + 1) := by simpa [Subgroup.orderOf_coe] using hxord
                refine ⟨hxord', ?_⟩
                have hcard_x : Fintype.card (Subgroup.zpowers x) = p ^ (a + 1) := by
                  rw [Fintype.card_zpowers, hxord']
                have hcard_x0 : Fintype.card (Subgroup.zpowers x₀) = p ^ (a + 1) := by
                  rw [Fintype.card_zpowers, hx₀_ord]
                exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hxH)
                  (by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard_x, hcard_x0])⟩
              left_inv := fun ⟨_, _⟩ => rfl
              right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
        rw [hset]
        have hdvd_H : p ^ (a + 1) ∣ Fintype.card (Subgroup.zpowers x₀) := by
          rw [Fintype.card_zpowers, hx₀_ord]
        have htot := IsCyclic.card_orderOf_eq_totient (α := Subgroup.zpowers x₀) hdvd_H
        rw [← htot, ← Fintype.card_coe]
        exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun x => by simp)
      rw [hfib, Nat.totient_prime_pow hp (Nat.succ_pos a), Nat.succ_sub_one]
      exact dvd_mul_right _ _
    have hSa_eq : Fintype.card {x : G // x ^ (p ^ a) = 1} = S_a.card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl G) fun x => by simp [S_a])
    rw [hSa_eq]
    have hdvd_sum : p ^ a ∣ S_a.card + A.card :=
      (Nat.pow_dvd_pow p (Nat.le_succ a)).trans (hcard_eq ▸ ih1)
    exact (Nat.dvd_add_left hA_dvd).mp hdvd_sum

private lemma dvd_card_pow_eq_one {G : Type*} [Group G] [Fintype G]
    {d : ℕ} (hd : d ∣ Fintype.card G) :
    d ∣ Fintype.card {x : G // x ^ d = 1} := by
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd Fintype.card_pos
  have hcard_pos : 0 < Fintype.card {x : G // x ^ d = 1} :=
    Fintype.card_pos_iff.mpr ⟨⟨1, one_pow d⟩⟩
  rw [← Nat.factorization_le_iff_dvd hd_pos.ne' hcard_pos.ne']
  intro p
  by_cases hp : p.Prime
  · rw [← hp.pow_dvd_iff_le_factorization hcard_pos.ne']
    set a := d.factorization p
    set m := d / p ^ a
    have hpa_dvd : p ^ a ∣ d := Nat.ordProj_dvd d p
    have hm_mul : p ^ a * m = d := Nat.mul_div_cancel' hpa_dvd
    have hm_ndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hd_pos.ne'
    have hcop : Nat.Coprime (p ^ a) m := (hp.coprime_iff_not_dvd.mpr hm_ndvd).pow_left _
    have hsum := card_pow_eq_one_mul_coprime (G := G) (p ^ a) m hcop
    rw [hm_mul] at hsum
    let f : G → ℕ := fun y =>
      Fintype.card {u : Subgroup.centralizer ({y} : Set G) // (u : G) ^ (p ^ a) = 1}
    have hsum2 : Fintype.card {x : G // x ^ d = 1} =
        ∑ y ∈ Finset.univ.filter (fun y : G => y ^ m = 1), f y := by
      rw [hsum, ← Finset.sum_coe_sort (Finset.univ.filter (fun y : G => y ^ m = 1))]
      refine Fintype.sum_equiv (Equiv.subtypeEquiv (Equiv.refl G) fun y => by simp) _ _ fun y => rfl
    rw [hsum2]
    let S := Finset.univ.filter (fun y : G => y ^ m = 1)
    let orb := MulAction.orbitRel (ConjAct G) G
    rw [← Finset.sum_fiberwise_of_maps_to (g := Quotient.mk orb)
      (t := (Finset.univ : Finset (Quotient orb))) (fun _ _ => Finset.mem_univ _)]
    refine Finset.dvd_sum fun q _ => ?_
    by_cases hne : (S.filter (fun y => Quotient.mk orb y = q)).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      have hy₀_S : y₀ ∈ S := (Finset.mem_filter.mp hy₀).1
      have hy₀_q : Quotient.mk orb y₀ = q := (Finset.mem_filter.mp hy₀).2
      have hy₀_m : y₀ ^ m = 1 := (Finset.mem_filter.mp hy₀_S).2
      have hconst : ∀ y ∈ S.filter (fun y => Quotient.mk orb y = q), f y = f y₀ := by
        intro y hy
        have hq : Quotient.mk orb y = Quotient.mk orb y₀ :=
          (Finset.mem_filter.mp hy).2.trans hy₀_q.symm
        obtain ⟨g, hg⟩ := Quotient.exact hq
        dsimp [f]
        rw [← hg, card_pow_eq_one_eq_of_conj]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
      have hfilt_eq : S.filter (fun y => Quotient.mk orb y = q) =
          Finset.univ.filter (fun y : G => Quotient.mk orb y = q) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
        constructor
        · intro h; exact h.2
        · intro hq
          have hq' : Quotient.mk orb y = Quotient.mk orb y₀ := hq.trans hy₀_q.symm
          obtain ⟨g, hg⟩ := Quotient.exact hq'
          change g • y₀ = y at hg
          refine ⟨?_, hq⟩
          rw [← hg, ConjAct.smul_def, conj_pow, hy₀_m]
          group
      have hcard_orb : (Finset.univ.filter (fun y : G => Quotient.mk orb y = q)).card =
          Fintype.card (MulAction.orbit (ConjAct G) y₀) := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr ?_
        exact
          { toFun := fun ⟨y, hy⟩ => ⟨y, Quotient.exact ((Finset.mem_filter.mp hy).2.trans hy₀_q.symm)⟩
            invFun := fun ⟨y, hy⟩ => ⟨y, by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact (Quotient.sound hy).trans hy₀_q⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl }
      rw [hfilt_eq, hcard_orb]
      set M := Fintype.card (Subgroup.centralizer ({y₀} : Set G))
      have hmul_N : Fintype.card (MulAction.orbit (ConjAct G) y₀) * M = Fintype.card G :=
        card_orbit_mul_centralizer y₀
      set b := M.factorization p
      have hf_eq : f y₀ =
          Fintype.card {u : Subgroup.centralizer ({y₀} : Set G) // u ^ (p ^ min a b) = 1} := by
        dsimp [f]
        have h1 : Fintype.card {u : Subgroup.centralizer ({y₀} : Set G) // (u : G) ^ (p ^ a) = 1} =
            Fintype.card {u : Subgroup.centralizer ({y₀} : Set G) // u ^ (p ^ a) = 1} :=
          Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun u => by simp [Subtype.ext_iff])
        rw [h1]
        convert card_pow_eq_one_min_exp (G := Subgroup.centralizer ({y₀} : Set G)) p a hp
      have hf_dvd : p ^ min a b ∣ f y₀ := by
        rw [hf_eq]
        have hle : min a b ≤ M.factorization p := min_le_right _ _
        have hpp := dvd_card_pow_eq_one_prime_pow (G := Subgroup.centralizer ({y₀} : Set G))
          p (min a b) hp hle
        convert hpp
      have horb_dvd : p ^ (a - min a b) ∣ Fintype.card (MulAction.orbit (ConjAct G) y₀) := by
        have h1 : p ^ (a - b) ∣ Fintype.card (MulAction.orbit (ConjAct G) y₀) := by
          apply dvd_pow_sub_of_dvd_mul hp Fintype.card_ne_zero _ rfl
          rw [hmul_N]
          exact hpa_dvd.trans hd
        have hsub_eq : a - min a b = a - b := by omega
        rwa [hsub_eq]
      have hmul_dvd := mul_dvd_mul horb_dvd hf_dvd
      rw [← pow_add, Nat.sub_add_cancel (min_le_left a b)] at hmul_dvd
      exact hmul_dvd
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact dvd_zero _
  · simp [Nat.factorization_eq_zero_of_not_prime d hp]

end Frobenius

section Richards

open Classical ArithmeticFunction
open scoped ArithmeticFunction

private lemma totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (hdvd : p ∣ n) :
    (p * n).totient = p * n.totient := by
  by_cases hn : n = 0
  · subst hn; simp
  set c := n.factorization p
  have hc_pos : 0 < c := Nat.Prime.factorization_pos_of_dvd hp hn hdvd
  set r := n / p ^ c
  have hmul : p ^ c * r = n := Nat.mul_div_cancel' (Nat.ordProj_dvd n p)
  have hcop : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hn)
  have hcop_c : Nat.Coprime (p ^ c) r := hcop.pow_left c
  have hcop_c1 : Nat.Coprime (p ^ (c + 1)) r := hcop.pow_left (c + 1)
  rw [← hmul, ← mul_assoc, ← pow_succ', Nat.totient_mul hcop_c1, Nat.totient_mul hcop_c,
    Nat.totient_prime_pow_succ hp c, Nat.totient_prime_pow hp hc_pos]
  have hc1 : c - 1 + 1 = c := Nat.sub_add_cancel hc_pos
  calc p ^ c * (p - 1) * r.totient
      = p * (p ^ (c - 1) * (p - 1) * r.totient) := by
          conv_lhs => rw [← hc1, pow_succ']
          ring
    _ = p * (p ^ (c - 1) * (p - 1) * r.totient) := rfl

private lemma totient_squarefree_mul {d m : ℕ} (hm : Squarefree m) :
    ((m * d).totient : ℚ) = (d.totient : ℚ) *
      ∏ p ∈ m.primeFactors, (if p ∣ d then (p : ℚ) else (p - 1 : ℚ)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hm0 : m ≠ 0 := hm.ne_zero
    by_cases hm1 : m = 1
    · subst hm1; simp
    have hm_gt1 : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    set m' := m / p
    have hm_eq : m = p * m' := (Nat.mul_div_cancel' hpm).symm
    have hm'_lt : m' < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
    have hm'_sq : Squarefree m' := hm.squarefree_of_dvd (Nat.div_dvd_of_dvd hpm)
    have hp_ndvd : ¬ p ∣ m' := by
      intro hdiv
      have hsq : p * p ∣ m := by
        rw [hm_eq]
        exact mul_dvd_mul_left p hdiv
      exact hp.ne_one (Nat.isUnit_iff.mp (hm p hsq))
    have ih_m' := ih m' hm'_lt hm'_sq
    have hpf : m.primeFactors = insert p m'.primeFactors := by
      rw [hm_eq, Nat.primeFactors_mul hp.ne_zero hm'_sq.ne_zero, hp.primeFactors]
      ext q
      simp
    have hp_not_mem : p ∉ m'.primeFactors := by
      rw [Nat.mem_primeFactors]
      intro h
      exact hp_ndvd h.2.1
    rw [hpf, Finset.prod_insert hp_not_mem, hm_eq, mul_assoc]
    by_cases hpd : p ∣ d
    · have hpd' : p ∣ m' * d := hpd.trans (dvd_mul_left d m')
      rw [totient_prime_mul_of_dvd hp hpd', Nat.cast_mul, ih_m', if_pos hpd]
      ring
    · have hcop : Nat.Coprime p (m' * d) :=
        (hp.coprime_iff_not_dvd.mpr hp_ndvd).mul_right (hp.coprime_iff_not_dvd.mpr hpd)
      rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul, ih_m', if_neg hpd,
        Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      ring

private lemma prod_primeFactors_of_squarefree {m : ℕ} (hm : Squarefree m) :
    ∏ p ∈ m.primeFactors, p = m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst hm1; simp
    have hm0 : m ≠ 0 := hm.ne_zero
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    set m' := m / p
    have hm_eq : m = p * m' := (Nat.mul_div_cancel' hpm).symm
    have hm'_lt : m' < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
    have hm'_sq : Squarefree m' := hm.squarefree_of_dvd (Nat.div_dvd_of_dvd hpm)
    have hp_ndvd : ¬ p ∣ m' := fun hdiv => hp.ne_one (Nat.isUnit_iff.mp (hm p (hm_eq ▸ mul_dvd_mul_left p hdiv)))
    have hpf : m.primeFactors = insert p m'.primeFactors := by
      rw [hm_eq, Nat.primeFactors_mul hp.ne_zero hm'_sq.ne_zero, hp.primeFactors]
      ext q
      simp
    have hp_not_mem : p ∉ m'.primeFactors := fun h =>
      hp_ndvd (Nat.mem_primeFactors.mp h).2.1
    rw [hpf, Finset.prod_insert hp_not_mem, ih m' hm'_lt hm'_sq, ← hm_eq]

private lemma cardFactors_of_squarefree {m : ℕ} (hm : Squarefree m) :
    cardFactors m = m.primeFactors.card := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst hm1; simp
    have hm0 : m ≠ 0 := hm.ne_zero
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    set m' := m / p
    have hm_eq : m = p * m' := (Nat.mul_div_cancel' hpm).symm
    have hm'_lt : m' < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
    have hm'_sq : Squarefree m' := hm.squarefree_of_dvd (Nat.div_dvd_of_dvd hpm)
    have hp_ndvd : ¬ p ∣ m' := fun hdiv => hp.ne_one (Nat.isUnit_iff.mp (hm p (hm_eq ▸ mul_dvd_mul_left p hdiv)))
    have hpf : m.primeFactors = insert p m'.primeFactors := by
      rw [hm_eq, Nat.primeFactors_mul hp.ne_zero hm'_sq.ne_zero, hp.primeFactors]
      ext q; simp
    have hp_not_mem : p ∉ m'.primeFactors := fun h =>
      hp_ndvd (Nat.mem_primeFactors.mp h).2.1
    rw [hm_eq, cardFactors_mul hp.ne_zero hm'_sq.ne_zero, cardFactors_apply_prime hp,
      ih m' hm'_lt hm'_sq, ← hm_eq, hpf, Finset.card_insert_of_notMem hp_not_mem]
    ring

private lemma sum_moebius_div_totient {M d : ℕ} (hM : 0 < M) (hd : 0 < d) :
    ∑ m ∈ M.divisors, (moebius m : ℚ) / ((m * d).totient : ℚ) =
      (1 / (d.totient : ℚ)) *
        ∏ p ∈ M.primeFactors, (1 - 1 / (if p ∣ d then (p : ℚ) else (p - 1 : ℚ))) := by
  let w : ℕ → ℚ := fun p => if p ∣ d then (p : ℚ) else (p - 1 : ℚ)
  have hterm : ∀ m ∈ M.divisors,
      (moebius m : ℚ) / ((m * d).totient : ℚ) =
        (1 / (d.totient : ℚ)) *
          (if Squarefree m then ∏ p ∈ m.primeFactors, (-1 / w p) else 0) := by
    intro m hm
    by_cases hsq : Squarefree m
    · rw [if_pos hsq, moebius_apply_of_squarefree hsq, totient_squarefree_mul hsq,
        cardFactors_of_squarefree hsq]
      push_cast
      rw [Finset.prod_div_distrib, Finset.prod_const]
      have hd_ne : (d.totient : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hd).ne'
      have hprod_ne : ∏ p ∈ m.primeFactors, w p ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro p hp
        have hp_prime := (Nat.mem_primeFactors.mp hp).1
        dsimp [w]
        split_ifs
        · exact Nat.cast_ne_zero.mpr hp_prime.ne_zero
        · have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_prime.two_le
          linarith
      change (-1 : ℚ) ^ m.primeFactors.card / (↑d.totient * ∏ p ∈ m.primeFactors, w p) =
        1 / ↑d.totient * ((-1 : ℚ) ^ m.primeFactors.card / ∏ p ∈ m.primeFactors, w p)
      field_simp [hd_ne, hprod_ne]
    · rw [if_neg hsq, moebius_eq_zero_of_not_squarefree hsq]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hbij : ∑ m ∈ M.divisors, (if Squarefree m then ∏ p ∈ m.primeFactors, (-1 / w p) else 0) =
      ∑ T ∈ M.primeFactors.powerset, ∏ p ∈ T, (-1 / w p) := by
    rw [← Finset.sum_filter_ne_zero]
    refine Finset.sum_bij (fun m _ => m.primeFactors) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Nat.mem_divisors] at hm
      rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono hm.1.1 hM.ne'
    · intro m₁ hm₁ m₂ hm₂ h
      simp only [Finset.mem_filter, Nat.mem_divisors] at hm₁ hm₂
      have hsq1 : Squarefree m₁ := by by_contra hc; simp [hc] at hm₁
      have hsq2 : Squarefree m₂ := by by_contra hc; simp [hc] at hm₂
      rw [← prod_primeFactors_of_squarefree hsq1, ← prod_primeFactors_of_squarefree hsq2, h]
    · intro T hT
      rw [Finset.mem_powerset] at hT
      refine ⟨∏ p ∈ T, p, ?_, ?_⟩
      · have hsqT : Squarefree (∏ p ∈ T, p) := by
          rw [Nat.squarefree_iff_prime_squarefree]
          intro p hp hdvd
          have hmem : p ∈ T := by
            have := (Prime.dvd_finsetProd_iff hp.prime _).mp (dvd_trans (dvd_mul_right p p) hdvd)
            rcases this with ⟨q, hqT, hpq⟩
            have hq_prime := (Nat.mem_primeFactors.mp (hT hqT)).1
            rwa [(Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq]
          have hdiv_erase : p * p ∣ p * ∏ q ∈ T.erase p, q := by
            rwa [Finset.mul_prod_erase T (fun q => q) hmem]
          have hdiv2 : p ∣ ∏ q ∈ T.erase p, q := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdiv_erase
          obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdiv2
          have hq_prime := (Nat.mem_primeFactors.mp (hT (Finset.mem_of_mem_erase hq))).1
          have heq := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq
          subst heq
          exact Finset.notMem_erase p T hq
        have hdvd_M : ∏ p ∈ T, p ∣ M := by
          have h1 : ∏ p ∈ T, p ∣ ∏ p ∈ M.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset T M.primeFactors (fun p => p) hT
          exact h1.trans (Nat.prod_primeFactors_dvd M)
        simp only [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨hdvd_M, hM.ne'⟩, ?_⟩
        rw [if_pos hsqT, Finset.prod_ne_zero_iff]
        intro q hqT
        have hq_prime := (Nat.mem_primeFactors.mp hqT).1
        dsimp [w]
        split_ifs
        · exact div_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hq_prime.ne_zero)
        · have : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq_prime.two_le
          exact div_ne_zero (by norm_num) (by linarith)
      · ext p
        rw [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hp_dvd, _⟩
          obtain ⟨q, hqT, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hp_dvd
          have hq_prime := (Nat.mem_primeFactors.mp (hT hqT)).1
          rwa [(Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq]
        · intro hpT
          have hp_prime := (Nat.mem_primeFactors.mp (hT hpT)).1
          refine ⟨hp_prime, Finset.dvd_prod_of_mem _ hpT, ?_⟩
          exact (Finset.prod_ne_zero_iff.mpr fun q hq =>
            (Nat.mem_primeFactors.mp (hT hq)).1.ne_zero)
    · intro m hm
      simp only [Finset.mem_filter] at hm
      have hsq : Squarefree m := by by_contra hc; simp [hc] at hm
      simp [hsq]
  rw [hbij, ← Finset.prod_one_add]
  refine Finset.prod_congr rfl fun p _ => by ring

private lemma powCount_eq_sum_cycCount {G : Type*} [Group G] [Fintype G]
    {d : ℕ} (hd : 0 < d) :
    Fintype.card {x : G // x ^ d = 1} =
      ∑ k ∈ d.divisors, Fintype.card {H : Subgroup G // IsCyclic H ∧ Nat.card H = k} * k.totient := by
  let A := Finset.univ.filter (fun x : G => x ^ d = 1)
  have hA : Fintype.card {x : G // x ^ d = 1} = A.card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl G) fun x => by simp [A])
  rw [hA, Finset.card_eq_sum_card_fiberwise (f := Subgroup.zpowers)
    (t := A.image Subgroup.zpowers) (fun x hx => Finset.mem_image_of_mem _ hx)]
  have himg : A.image Subgroup.zpowers =
      Finset.univ.filter (fun H : Subgroup G => IsCyclic H ∧ Nat.card H ∣ d) := by
    ext H
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, A]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨inferInstance, ?_⟩
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx
    · rintro ⟨hcyc, hdvd⟩
      obtain ⟨⟨x, hxH⟩, hxgen⟩ := IsCyclic.exists_generator (α := H)
      have hH_eq : Subgroup.zpowers x = H := by
        apply le_antisymm (Subgroup.zpowers_le_of_mem hxH)
        intro y hy
        obtain ⟨k, hk⟩ := hxgen ⟨y, hy⟩
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨k, congrArg Subtype.val hk⟩
      refine ⟨x, ?_, hH_eq⟩
      rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, hH_eq]
      exact hdvd
  rw [himg]
  have hfib : ∀ H ∈ Finset.univ.filter (fun H : Subgroup G => IsCyclic H ∧ Nat.card H ∣ d),
      (A.filter (fun x => Subgroup.zpowers x = H)).card = (Nat.card H).totient := by
    intro H hH
    obtain ⟨hcyc, hdvd⟩ := (Finset.mem_filter.mp hH).2
    have hset : (A.filter (fun x => Subgroup.zpowers x = H)).card =
        (Finset.univ.filter (fun x : H => orderOf x = Fintype.card H)).card := by
      rw [← Fintype.card_coe, ← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun ⟨x, hx⟩ => ⟨⟨x, by
            have hzx : Subgroup.zpowers x = H := (Finset.mem_filter.mp hx).2
            rw [← hzx]
            exact Subgroup.mem_zpowers x⟩, by
            have hzx : Subgroup.zpowers x = H := (Finset.mem_filter.mp hx).2
            have hxH : x ∈ H := hzx ▸ Subgroup.mem_zpowers x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← Nat.card_eq_fintype_card]
            have hord : orderOf (⟨x, hxH⟩ : H) = orderOf x := (Subgroup.orderOf_coe ⟨x, hxH⟩).symm
            rw [hord, ← hzx, Nat.card_zpowers]⟩
          invFun := fun ⟨⟨x, hxH⟩, hxord⟩ => ⟨x, by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
            have hxord' : orderOf x = Fintype.card H := by simpa [Subgroup.orderOf_coe] using hxord
            have hxord'' : orderOf x = Nat.card H := by rw [Nat.card_eq_fintype_card]; exact hxord'
            refine ⟨orderOf_dvd_iff_pow_eq_one.mp (hxord'' ▸ hdvd), ?_⟩
            exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hxH)
              (by rw [Nat.card_zpowers, hxord''])⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    rw [hset, IsCyclic.card_orderOf_eq_totient dvd_rfl, ← Nat.card_eq_fintype_card]
  rw [Finset.sum_congr rfl hfib]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun H : Subgroup G => Nat.card H)
    (t := d.divisors) (fun H hH => Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hH).2.2, hd.ne'⟩)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_const : ∀ H ∈ (Finset.univ.filter (fun H : Subgroup G => IsCyclic H ∧ Nat.card H ∣ d)).filter
      (fun H : Subgroup G => Nat.card H = k), (Nat.card H).totient = k.totient := by
    intro H hH
    rw [(Finset.mem_filter.mp hH).2]
  rw [Finset.sum_congr rfl hk_const, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [← Fintype.card_coe]
  refine Fintype.card_congr ?_
  exact Equiv.subtypeEquiv (Equiv.refl _) fun H => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, rfl⟩; exact ⟨⟨h1, (Nat.mem_divisors.mp hk).1⟩, rfl⟩

private lemma cyc_eq_sum_cycCount (G : Type*) [Group G] [Fintype G] :
    Arxiv.«2604.08040».cyc G =
      ∑ k ∈ (Fintype.card G).divisors,
        Fintype.card {H : Subgroup G // IsCyclic H ∧ Nat.card H = k} := by
  unfold Arxiv.«2604.08040».cyc
  rw [Nat.card_eq_fintype_card]
  have h1 : Fintype.card {H : Subgroup G // IsCyclic H} =
      (Finset.univ.filter (fun H : Subgroup G => IsCyclic H)).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun _ => by simp)
  rw [h1, Finset.card_eq_sum_card_fiberwise (f := fun H : Subgroup G => Nat.card H)
    (t := (Fintype.card G).divisors) (fun H _ => Nat.mem_divisors.mpr
      ⟨by rw [← Nat.card_eq_fintype_card]; exact Subgroup.card_subgroup_dvd_card H,
       Fintype.card_ne_zero⟩)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun H => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.card_eq_fintype_card]
    tauto)

private lemma richards_identity (G : Type*) [Group G] [Fintype G] :
    (Arxiv.«2604.08040».cyc G : ℚ) - ((Fintype.card G).divisors.card : ℚ) =
      ∑ d ∈ (Fintype.card G).divisors,
        (((Fintype.card {x : G // x ^ d = 1} : ℚ) - (d : ℚ)) / (d.totient : ℚ)) *
          ∏ p ∈ (Fintype.card G / d).primeFactors,
            (1 - 1 / (if p ∣ d then (p : ℚ) else (p - 1 : ℚ))) := by
  set N := Fintype.card G
  have hNpos : 0 < N := Fintype.card_pos
  let c : ℕ → ℚ := fun k => (Fintype.card {H : Subgroup G // IsCyclic H ∧ Nat.card H = k} : ℚ)
  let S : ℕ → ℚ := fun d => (Fintype.card {x : G // x ^ d = 1} : ℚ) - (d : ℚ)
  let f : ℕ → ℚ := fun k => if k ∣ N then (c k - 1) * (k.totient : ℚ) else 0
  let g : ℕ → ℚ := fun d => if d ∣ N then S d else ∑ k ∈ d.divisors, f k
  have hfg : ∀ d > 0, ∑ k ∈ d.divisors, f k = g d := by
    intro d hd
    by_cases hdN : d ∣ N
    · dsimp [g]
      rw [if_pos hdN]
      have hcongr : ∀ k ∈ d.divisors, f k = (c k - 1) * (k.totient : ℚ) := by
        intro k hk
        dsimp [f]
        rw [if_pos ((Nat.mem_divisors.mp hk).1.trans hdN)]
      rw [Finset.sum_congr rfl hcongr]
      have hsub : ∑ k ∈ d.divisors, (c k - 1) * (k.totient : ℚ) =
          ∑ k ∈ d.divisors, c k * (k.totient : ℚ) - ∑ k ∈ d.divisors, (k.totient : ℚ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsub]
      have hpow : ∑ k ∈ d.divisors, c k * (k.totient : ℚ) =
          (Fintype.card {x : G // x ^ d = 1} : ℚ) := by
        dsimp [c]
        exact_mod_cast (powCount_eq_sum_cycCount (G := G) hd).symm
      have htot : ∑ k ∈ d.divisors, (k.totient : ℚ) = (d : ℚ) := by
        exact_mod_cast Nat.sum_totient d
      rw [hpow, htot]
    · dsimp [g]
      rw [if_neg hdN]
  have hmob := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq).mp hfg
  have hcyc : (Arxiv.«2604.08040».cyc G : ℚ) - (N.divisors.card : ℚ) =
      ∑ k ∈ N.divisors, (c k - 1) := by
    rw [cyc_eq_sum_cycCount G]
    push_cast
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by push_cast; rfl
  rw [hcyc]
  have hterm_k : ∀ k ∈ N.divisors,
      c k - 1 = ∑ x ∈ k.divisorsAntidiagonal, (moebius x.1 : ℚ) * S x.2 / (k.totient : ℚ) := by
    intro k hk
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hkN : k ∣ N := (Nat.mem_divisors.mp hk).1
    have hktot_ne : (k.totient : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hk_pos).ne'
    have hmk := hmob k hk_pos
    dsimp [f] at hmk
    rw [if_pos hkN] at hmk
    have hsum_eq : ∑ x ∈ k.divisorsAntidiagonal, (moebius x.1 : ℚ) * g x.2 =
        ∑ x ∈ k.divisorsAntidiagonal, (moebius x.1 : ℚ) * S x.2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx2_dvd : x.2 ∣ k := Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
      dsimp [g]
      rw [if_pos (hx2_dvd.trans hkN)]
    rw [hsum_eq] at hmk
    rw [← Finset.sum_div, hmk, mul_div_cancel_right₀ _ hktot_ne]
  rw [Finset.sum_congr rfl hterm_k]
  have hswap : (∑ k ∈ N.divisors, ∑ x ∈ k.divisorsAntidiagonal, (moebius x.1 : ℚ) * S x.2 / (k.totient : ℚ)) =
      ∑ d ∈ N.divisors, S d * ∑ m ∈ (N / d).divisors, (moebius m : ℚ) / ((m * d).totient : ℚ) := by
    rw [Finset.sum_sigma']
    have hswap2 : (∑ d ∈ N.divisors, S d * ∑ m ∈ (N / d).divisors, (moebius m : ℚ) / ((m * d).totient : ℚ)) =
        ∑ x ∈ N.divisors.sigma (fun d => (N / d).divisors),
          (moebius x.2 : ℚ) * S x.1 / ((x.2 * x.1).totient : ℚ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hswap2]
    refine Finset.sum_bij (fun p _ => ⟨p.2.2, p.2.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨k, m, d⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisors, Nat.mem_divisorsAntidiagonal] at hp ⊢
      rcases hp with ⟨⟨hkN, hN0⟩, ⟨hmd, hk0⟩⟩
      have hd0 : d ≠ 0 := by intro h; subst h; simp at hmd; exact hk0 hmd.symm
      have hdk : d ∣ k := ⟨m, by rw [← hmd, mul_comm]⟩
      have hdN : d ∣ N := hdk.trans hkN
      refine ⟨⟨hdN, hN0⟩, ⟨?_, (Nat.div_pos (Nat.le_of_dvd hNpos hdN) (Nat.pos_of_ne_zero hd0)).ne'⟩⟩
      rw [Nat.dvd_div_iff_mul_dvd hdN, mul_comm d m, hmd]
      exact hkN
    · rintro ⟨k₁, m₁, d₁⟩ hp₁ ⟨k₂, m₂, d₂⟩ hp₂ h
      simp only [Sigma.ext_iff] at h
      obtain ⟨rfl, h2⟩ := h
      rw [heq_eq_eq] at h2
      subst h2
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hp₁ hp₂
      have hk_eq : k₁ = k₂ := hp₁.2.1.symm.trans hp₂.2.1
      subst hk_eq
      rfl
    · rintro ⟨d, m⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
      rcases hp with ⟨⟨hdN, hN0⟩, ⟨hmNd, hNd0⟩⟩
      have hmd_dvd : m * d ∣ N := by rw [mul_comm]; exact (Nat.dvd_div_iff_mul_dvd hdN).mp hmNd
      have hm0 : m ≠ 0 := by intro h; subst h; exact hNd0 (Nat.eq_zero_of_zero_dvd hmNd)
      have hd0 : d ≠ 0 := by intro h; subst h; exact hN0 (Nat.eq_zero_of_zero_dvd hdN)
      refine ⟨⟨m * d, m, d⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Nat.mem_divisors, Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨hmd_dvd, hN0⟩, by simp [hm0, hd0]⟩
    · rintro ⟨k, m, d⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.2.1]
  rw [hswap]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdN : d ∣ N := (Nat.mem_divisors.mp hd).1
  have hNd_pos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hNpos hdN) hd_pos
  rw [sum_moebius_div_totient hNd_pos hd_pos]
  ring

private lemma richards_factor_nonneg (d p : ℕ) (hp : p.Prime) :
    0 ≤ 1 - 1 / (if p ∣ d then (p : ℚ) else (p - 1 : ℚ)) := by
  split_ifs
  · have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hp1
  · have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith

private lemma divisors_card_le_cyc (G : Type*) [Group G] [Fintype G] :
    (Fintype.card G).divisors.card ≤ Arxiv.«2604.08040».cyc G := by
  have hq : ((Fintype.card G).divisors.card : ℚ) ≤ (Arxiv.«2604.08040».cyc G : ℚ) := by
    rw [← sub_nonneg, richards_identity G]
    refine Finset.sum_nonneg fun d hd => ?_
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdN : d ∣ Fintype.card G := (Nat.mem_divisors.mp hd).1
    have hS : 0 ≤ (Fintype.card {x : G // x ^ d = 1} : ℚ) - (d : ℚ) := by
      rw [sub_nonneg]
      have hdvd := dvd_card_pow_eq_one hdN
      have hpos : 0 < Fintype.card {x : G // x ^ d = 1} :=
        Fintype.card_pos_iff.mpr ⟨⟨1, one_pow d⟩⟩
      exact_mod_cast Nat.le_of_dvd hpos hdvd
    have htot : (0 : ℚ) < (d.totient : ℚ) := by exact_mod_cast Nat.totient_pos.mpr hd_pos
    refine mul_nonneg (div_nonneg hS htot.le) ?_
    refine Finset.prod_nonneg fun p hp => richards_factor_nonneg d p (Nat.mem_primeFactors.mp hp).1
  exact_mod_cast hq

end Richards

section Solvable

open Classical
open scoped Pointwise

private lemma card_divisors_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card = ∏ q ∈ n.primeFactors, (n.factorization q + 1) := by
  exact Nat.card_divisors hn

private lemma prod_ge_two_pow_of_ge_two {S : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ q ∈ S, 2 ≤ f q) : 2 ^ S.card ≤ ∏ q ∈ S, f q := by
  have h1 : ∏ _q ∈ S, 2 ≤ ∏ q ∈ S, f q := Finset.prod_le_prod' hf
  simpa [Finset.prod_const] using h1

private lemma sum_powerset_rat_identity (S : Finset ℕ) (hS : ∀ q ∈ S, 2 ≤ q) :
    ∑ T ∈ S.powerset,
        (∏ q ∈ T, (q : ℚ) / ((q : ℚ) - 1)) * (∏ q ∈ S \ T, (((q : ℚ) - 2) / ((q : ℚ) - 1))) =
      (2 : ℚ) ^ S.card := by
  have hprod : ∏ q ∈ S, ((q : ℚ) / ((q : ℚ) - 1) + ((q : ℚ) - 2) / ((q : ℚ) - 1)) =
      ∑ T ∈ S.powerset,
        (∏ q ∈ T, (q : ℚ) / ((q : ℚ) - 1)) * (∏ q ∈ S \ T, (((q : ℚ) - 2) / ((q : ℚ) - 1))) := by
    rw [Finset.prod_add]
  rw [← hprod]
  have hterm : ∀ q ∈ S,
      (q : ℚ) / ((q : ℚ) - 1) + ((q : ℚ) - 2) / ((q : ℚ) - 1) = 2 := by
    intro q hq
    have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hS q hq
    have hne : (q : ℚ) - 1 ≠ 0 := by linarith
    field_simp [hne]
    ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_const]

private lemma isZGroup_of_cyc_lt_two_pow_succ {G : Type*} [Group G] [Fintype G]
    (hcyc : Arxiv.«2604.08040».cyc G < 2 ^ (Arxiv.«2604.08040».numPrimeFactors G + 1)) :
    IsZGroup G := by
  by_contra hnotZ
  rw [isZGroup_iff] at hnotZ
  push Not at hnotZ
  obtain ⟨p, hp, P, hP_not_cyc⟩ := hnotZ
  have hp_prime : p.Prime := hp
  have : Fact p.Prime := ⟨hp⟩
  set N := Fintype.card G
  set t := N.primeFactors.card
  have hNpos : 0 < N := Fintype.card_pos
  have hNne : N ≠ 0 := hNpos.ne'
  have hcyc' : Arxiv.«2604.08040».cyc G < 2 ^ (t + 1) := hcyc
  have hdiv_le : N.divisors.card ≤ Arxiv.«2604.08040».cyc G := divisors_card_le_cyc G
  have hdiv_lt : N.divisors.card < 2 ^ (t + 1) := hdiv_le.trans_lt hcyc'
  have hP_card : Nat.card P = p ^ (N.factorization p) := by
    simpa [N, Nat.card_eq_fintype_card] using Sylow.card_eq_multiplicity P
  have hp_exp_ge2 : 2 ≤ N.factorization p := by
    by_contra hlt
    have hle1 : N.factorization p ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
    · rw [h0, pow_zero] at hP_card
      have : Subsingleton P := Finite.card_le_one_iff_subsingleton.mp hP_card.le
      exact hP_not_cyc (isCyclic_of_subsingleton)
    · rw [h1, pow_one] at hP_card
      have : Fact (Nat.Prime (Nat.card P)) := ⟨by rw [hP_card]; exact hp_prime⟩
      exact hP_not_cyc (isCyclic_of_prime_card rfl)
  have hp_mem : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime,
      (dvd_pow_self p (by norm_num)).trans (hp_prime.pow_dvd_iff_le_factorization hNne |>.mpr hp_exp_ge2),
      hNne⟩
  have ht_pos : 1 ≤ t := Finset.card_pos.mpr ⟨p, hp_mem⟩
  have hdiv_prod : N.divisors.card = ∏ q ∈ N.primeFactors, (N.factorization q + 1) :=
    card_divisors_eq_prod_factorization hNne
  have h_exp_lt3 : N.factorization p < 3 := by
    by_contra hge3
    have hge3' : 3 ≤ N.factorization p := by omega
    have hsplit := Finset.mul_prod_erase N.primeFactors (fun q => N.factorization q + 1) hp_mem
    have hge2 : ∀ q ∈ N.primeFactors.erase p, 2 ≤ N.factorization q + 1 := by
      intro q hq
      have hq_mem := Finset.mem_of_mem_erase hq
      have hq_pos : 0 < N.factorization q :=
        (Nat.mem_primeFactors.mp hq_mem).1.factorization_pos_of_dvd hNne
          (Nat.mem_primeFactors.mp hq_mem).2.1
      omega
    have hprod_ge := prod_ge_two_pow_of_ge_two hge2
    rw [Finset.card_erase_of_mem hp_mem] at hprod_ge
    have hcard_ge : 2 ^ (t + 1) ≤ N.divisors.card := by
      rw [hdiv_prod, ← hsplit]
      have h4 : 4 * 2 ^ (t - 1) ≤ (N.factorization p + 1) * ∏ q ∈ N.primeFactors.erase p, (N.factorization q + 1) :=
        Nat.mul_le_mul (by omega) hprod_ge
      have hpow : 4 * 2 ^ (t - 1) = 2 ^ (t + 1) := by
        have ht1 : t + 1 = 2 + (t - 1) := by omega
        rw [ht1, pow_add]
        norm_num
      omega
    omega
  have hp_exp_eq2 : N.factorization p = 2 := by omega
  have h_other_exp : ∀ q ∈ N.primeFactors, q ≠ p → N.factorization q = 1 := by
    intro q hq hqp
    have hq_pos : 0 < N.factorization q :=
      (Nat.mem_primeFactors.mp hq).1.factorization_pos_of_dvd hNne (Nat.mem_primeFactors.mp hq).2.1
    by_contra hne1
    have hq_ge2 : 2 ≤ N.factorization q := by omega
    have hq_mem_erase : q ∈ N.primeFactors.erase p := Finset.mem_erase.mpr ⟨hqp, hq⟩
    have hsplit1 := Finset.mul_prod_erase N.primeFactors (fun r => N.factorization r + 1) hp_mem
    have hsplit2 := Finset.mul_prod_erase (N.primeFactors.erase p)
      (fun r => N.factorization r + 1) hq_mem_erase
    have hge2 : ∀ r ∈ (N.primeFactors.erase p).erase q, 2 ≤ N.factorization r + 1 := by
      intro r hr
      have hr_mem := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
      have hr_pos : 0 < N.factorization r :=
        (Nat.mem_primeFactors.mp hr_mem).1.factorization_pos_of_dvd hNne
          (Nat.mem_primeFactors.mp hr_mem).2.1
      omega
    have hprod_ge := prod_ge_two_pow_of_ge_two hge2
    rw [Finset.card_erase_of_mem hq_mem_erase, Finset.card_erase_of_mem hp_mem] at hprod_ge
    have ht_ge2 : 2 ≤ t := by
      have : 1 ≤ (N.primeFactors.erase p).card := Finset.card_pos.mpr ⟨q, hq_mem_erase⟩
      rw [Finset.card_erase_of_mem hp_mem] at this
      omega
    have hcard_ge : 9 * 2 ^ (t - 2) ≤ N.divisors.card := by
      rw [hdiv_prod, ← hsplit1, ← hsplit2, hp_exp_eq2]
      have h33 : 3 * 3 * 2 ^ (t - 2) ≤
          3 * ((N.factorization q + 1) * ∏ r ∈ (N.primeFactors.erase p).erase q, (N.factorization r + 1)) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul (by omega) hprod_ge)
      simpa [Nat.sub_sub] using h33
    have hpow : 2 ^ (t + 1) = 8 * 2 ^ (t - 2) := by
      have ht2 : t + 1 = 3 + (t - 2) := by omega
      rw [ht2, pow_add]
      norm_num
    have hpos2 : 0 < 2 ^ (t - 2) := pow_pos (by norm_num) _
    omega
  set m := N / p ^ 2
  have hm_mul : p ^ 2 * m = N := Nat.mul_div_cancel' (by rw [← hp_exp_eq2]; exact Nat.ordProj_dvd N p)
  have hm_ndvd : ¬ p ∣ m := by
    dsimp [m]
    rw [← hp_exp_eq2]
    exact Nat.not_dvd_ordCompl hp_prime hNne
  have hm_ne : m ≠ 0 := by intro h; rw [h, mul_zero] at hm_mul; exact hNne hm_mul.symm
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
  have hm_sq : Squarefree m := by
    rw [Nat.squarefree_iff_factorization_le_one hm_ne]
    intro q
    by_cases hqp : q = p
    · subst hqp
      rw [Nat.factorization_eq_zero_of_not_dvd hm_ndvd]
      exact Nat.zero_le _
    · have hm_dvd : m ∣ N := ⟨p ^ 2, by rw [mul_comm]; exact hm_mul.symm⟩
      by_cases hqm : q ∈ m.primeFactors
      · have hqN : q ∈ N.primeFactors := Nat.primeFactors_mono hm_dvd hNne hqm
        have hle := (Nat.factorization_le_iff_dvd hm_ne hNne).mpr hm_dvd q
        rw [h_other_exp q hqN hqp] at hle
        exact hle
      · by_cases hqd : q ∣ m
        · by_cases hq_prime : q.Prime
          · exact False.elim (hqm (Nat.mem_primeFactors.mpr ⟨hq_prime, hqd, hm_ne⟩))
          · rw [Nat.factorization_eq_zero_of_not_prime m hq_prime]
            exact Nat.zero_le _
        · rw [Nat.factorization_eq_zero_of_not_dvd hqd]
          exact Nat.zero_le _
  have hm_pf : m.primeFactors = N.primeFactors.erase p := by
    ext q
    rw [Finset.mem_erase, Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hq, hqm, _⟩
      have hqp : q ≠ p := fun h => hm_ndvd (h ▸ hqm)
      exact ⟨hqp, hq, hqm.trans ⟨p ^ 2, by rw [mul_comm]; exact hm_mul.symm⟩, hNne⟩
    · rintro ⟨hqp, hq, hqN, _⟩
      refine ⟨hq, ?_, hm_ne⟩
      rw [← hm_mul] at hqN
      exact (hq.dvd_mul.mp hqN).resolve_left (fun h => hqp (Nat.prime_dvd_prime_iff_eq hq hp_prime |>.mp (hq.dvd_of_dvd_pow h)))
  have hm_pf_card : m.primeFactors.card = t - 1 := by
    rw [hm_pf, Finset.card_erase_of_mem hp_mem]
  have hdiv_card_eq : N.divisors.card = 3 * 2 ^ (t - 1) := by
    rw [hdiv_prod, ← Finset.mul_prod_erase N.primeFactors (fun q => N.factorization q + 1) hp_mem,
      hp_exp_eq2, ← hm_pf]
    have h2 : ∀ q ∈ m.primeFactors, N.factorization q + 1 = 2 := by
      intro q hq
      have hq' := hm_pf ▸ hq
      rw [h_other_exp q (Finset.mem_of_mem_erase hq') (Finset.ne_of_mem_erase hq')]
    rw [Finset.prod_congr rfl h2, Finset.prod_const, hm_pf_card]
  have hP_card' : Nat.card (P : Subgroup G) = p ^ 2 := by simpa [hp_exp_eq2] using hP_card
  have hP_pow_p : ∀ u : P, u ^ p = 1 := by
    intro u
    have hdvd : orderOf u ∣ p ^ 2 := by
      rw [← hP_card', Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    rw [Nat.dvd_prime_pow hp_prime] at hdvd
    obtain ⟨i, hi, hord⟩ := hdvd
    interval_cases i
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord]; exact one_dvd p)
    · rw [pow_one] at hord
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    · exfalso
      apply hP_not_cyc
      refine ⟨u, fun v => ?_⟩
      have hzp : Subgroup.zpowers u = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers, hord]
        exact hP_card'.symm
      have hv : v ∈ Subgroup.zpowers u := hzp ▸ Subgroup.mem_top v
      exact Subgroup.mem_zpowers_iff.mp hv
  have hx_pow_p : ∀ x : G, x ^ (p ^ 2) = 1 → x ^ p = 1 := by
    intro x hx
    have hz_pgroup : IsPGroup p (Subgroup.zpowers x) := by
      rw [IsPGroup.iff_card]
      have hord : orderOf x ∣ p ^ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx
      obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp_prime).mp hord
      refine ⟨i, ?_⟩
      rw [Nat.card_zpowers, hi]
    obtain ⟨Q, hQ⟩ := hz_pgroup.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
    have hxQ : x ∈ ((g • P : Sylow p G) : Set G) := hQ (Subgroup.mem_zpowers x)
    rw [Sylow.coe_smul] at hxQ
    obtain ⟨u, huP, hgu⟩ := Set.mem_smul_set.mp hxQ
    have hgu' : g * u * g⁻¹ = x := hgu
    have hu_pow : u ^ p = 1 := congrArg Subtype.val (hP_pow_p ⟨u, huP⟩)
    rw [← hgu', conj_pow, hu_pow]
    group
  have hS_lower : ∀ e ∈ m.divisors,
      (p : ℚ) * ((p : ℚ) - 1) * (e : ℚ) ≤
        (Fintype.card {x : G // x ^ (p * e) = 1} : ℚ) - ((p * e : ℕ) : ℚ) := by
    intro e he
    have he_dvd : e ∣ m := (Nat.mem_divisors.mp he).1
    have hpe_eq : Fintype.card {x : G // x ^ (p * e) = 1} =
        Fintype.card {x : G // x ^ (p ^ 2 * e) = 1} := by
      refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl G) fun x => ?_)
      constructor
      · intro hx
        dsimp
        rw [show p ^ 2 * e = (p * e) * p by ring, pow_mul, hx, one_pow]
      · intro hx
        have hx2 : (x ^ e) ^ (p ^ 2) = 1 := by
          rw [← pow_mul, mul_comm e (p ^ 2)]
          exact hx
        have hxp := hx_pow_p (x ^ e) hx2
        rwa [← pow_mul, mul_comm e p] at hxp
    have hdvd_N : p ^ 2 * e ∣ N := by
      rw [← hm_mul]
      exact Nat.mul_dvd_mul_left (p ^ 2) he_dvd
    have hcard_ge : p ^ 2 * e ≤ Fintype.card {x : G // x ^ (p * e) = 1} := by
      rw [hpe_eq]
      have hpos : 0 < Fintype.card {x : G // x ^ (p ^ 2 * e) = 1} :=
        Fintype.card_pos_iff.mpr ⟨⟨1, one_pow _⟩⟩
      exact Nat.le_of_dvd hpos (dvd_card_pow_eq_one hdvd_N)
    have hq : ((p ^ 2 * e : ℕ) : ℚ) ≤ (Fintype.card {x : G // x ^ (p * e) = 1} : ℚ) := by
      exact_mod_cast hcard_ge
    push_cast at hq ⊢
    linarith
  have hrich := richards_identity G
  let term : ℕ → ℚ := fun d =>
    (((Fintype.card {x : G // x ^ d = 1} : ℚ) - (d : ℚ)) / (d.totient : ℚ)) *
      ∏ q ∈ (N / d).primeFactors, (1 - 1 / (if q ∣ d then (q : ℚ) else (q - 1 : ℚ)))
  have hterm_nonneg : ∀ d ∈ N.divisors, 0 ≤ term d := by
    intro d hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdN : d ∣ N := (Nat.mem_divisors.mp hd).1
    have hS : 0 ≤ (Fintype.card {x : G // x ^ d = 1} : ℚ) - (d : ℚ) := by
      rw [sub_nonneg]
      have hpos : 0 < Fintype.card {x : G // x ^ d = 1} :=
        Fintype.card_pos_iff.mpr ⟨⟨1, one_pow d⟩⟩
      exact_mod_cast Nat.le_of_dvd hpos (dvd_card_pow_eq_one hdN)
    have htot : (0 : ℚ) < (d.totient : ℚ) := by exact_mod_cast Nat.totient_pos.mpr hd_pos
    refine mul_nonneg (div_nonneg hS htot.le) ?_
    exact Finset.prod_nonneg fun q hq => richards_factor_nonneg d q (Nat.mem_primeFactors.mp hq).1
  have hsub_div : m.divisors.image (fun e => p * e) ⊆ N.divisors := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    rw [Nat.mem_divisors]
    refine ⟨?_, hNne⟩
    rw [← hm_mul]
    exact mul_dvd_mul (dvd_pow_self p (by norm_num)) (Nat.mem_divisors.mp he).1
  have hsum_ge : ∑ e ∈ m.divisors, term (p * e) ≤ ∑ d ∈ N.divisors, term d := by
    have hinj : Set.InjOn (fun e => p * e) m.divisors := by
      intro e₁ _ e₂ _ h
      exact Nat.eq_of_mul_eq_mul_left hp_prime.pos h
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub_div (fun d hd _ => hterm_nonneg d hd)
  have hsum_m : ((p : ℚ) - 1) * (2 : ℚ) ^ (t - 1) ≤ ∑ e ∈ m.divisors, term (p * e) := by
    have hterm_e : ∀ e ∈ m.divisors,
        ((p : ℚ) - 1) * ((e : ℚ) / (e.totient : ℚ)) *
            ∏ q ∈ (m / e).primeFactors, (((q : ℚ) - 2) / ((q : ℚ) - 1)) ≤
          term (p * e) := by
      intro e he
      have he_pos : 0 < e := Nat.pos_of_mem_divisors he
      have he_dvd : e ∣ m := (Nat.mem_divisors.mp he).1
      have hp_ndvd_e : ¬ p ∣ e := fun h => hm_ndvd (h.trans he_dvd)
      have hcop_pe : Nat.Coprime p e := hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_e
      have htot_pe : ((p * e).totient : ℚ) = ((p : ℚ) - 1) * (e.totient : ℚ) := by
        rw [Nat.totient_mul hcop_pe, Nat.totient_prime hp_prime, Nat.cast_mul,
          Nat.cast_sub hp_prime.one_lt.le, Nat.cast_one]
      have hNd_eq : N / (p * e) = p * (m / e) := by
        rw [← hm_mul, show p ^ 2 * m = p * (p * m) by ring,
          Nat.mul_div_mul_left _ _ hp_prime.pos]
        exact Nat.mul_div_assoc p he_dvd
      have hme_ne : m / e ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm_pos he_dvd) he_pos).ne'
      have hpf_Nd : (N / (p * e)).primeFactors = insert p (m / e).primeFactors := by
        rw [hNd_eq, Nat.primeFactors_mul hp_prime.ne_zero hme_ne, hp_prime.primeFactors]
        ext q; simp
      have hp_ndvd_me : ¬ p ∣ m / e := fun h => hm_ndvd (h.trans (Nat.div_dvd_of_dvd he_dvd))
      have hp_not_mem_me : p ∉ (m / e).primeFactors := fun h =>
        hp_ndvd_me (Nat.mem_primeFactors.mp h).2.1
      have hprod_Nd : ∏ q ∈ (N / (p * e)).primeFactors,
            (1 - 1 / (if q ∣ p * e then (q : ℚ) else (q - 1 : ℚ))) =
          (((p : ℚ) - 1) / (p : ℚ)) *
            ∏ q ∈ (m / e).primeFactors, (((q : ℚ) - 2) / ((q : ℚ) - 1)) := by
        rw [hpf_Nd, Finset.prod_insert hp_not_mem_me, if_pos (dvd_mul_right p e)]
        have hp_ne0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
        have hp_fac : 1 - 1 / (p : ℚ) = ((p : ℚ) - 1) / (p : ℚ) := by field_simp [hp_ne0]
        rw [hp_fac]
        congr 1
        refine Finset.prod_congr rfl fun q hq => ?_
        have hq_prime := (Nat.mem_primeFactors.mp hq).1
        have hq_me : q ∣ m / e := (Nat.mem_primeFactors.mp hq).2.1
        have hqp : q ≠ p := fun h => hp_not_mem_me (h ▸ hq)
        have hq_ndvd_pe : ¬ q ∣ p * e := by
          intro hq_pe
          rcases hq_prime.dvd_mul.mp hq_pe with hqp_dvd | hqe
          · exact hqp (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime |>.mp hqp_dvd)
          · have hmul_me : e * (m / e) = m := Nat.mul_div_cancel' he_dvd
            have hsq_q : q * q ∣ m := by
              rw [← hmul_me]
              exact mul_dvd_mul hqe hq_me
            exact hq_prime.ne_one (Nat.isUnit_iff.mp (hm_sq q hsq_q))
        rw [if_neg hq_ndvd_pe]
        have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq_prime.two_le
        have hq1_ne : (q : ℚ) - 1 ≠ 0 := by linarith
        field_simp [hq1_ne]
        ring
      dsimp [term]
      rw [htot_pe, hprod_Nd]
      have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_prime.two_le
      have hp_ne : (p : ℚ) ≠ 0 := by linarith
      have hp1_ne : (p : ℚ) - 1 ≠ 0 := by linarith
      have hetot_pos : (0 : ℚ) < (e.totient : ℚ) := by exact_mod_cast Nat.totient_pos.mpr he_pos
      have hprod_nonneg : 0 ≤ ∏ q ∈ (m / e).primeFactors, (((q : ℚ) - 2) / ((q : ℚ) - 1)) := by
        refine Finset.prod_nonneg fun q hq => ?_
        have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.two_le
        exact div_nonneg (by linarith) (by linarith)
      have hS_e := hS_lower e he
      have hdiv_le_e : (p : ℚ) * (e : ℚ) / (e.totient : ℚ) ≤
          ((Fintype.card {x : G // x ^ (p * e) = 1} : ℚ) - ((p * e : ℕ) : ℚ)) /
            (((p : ℚ) - 1) * (e.totient : ℚ)) := by
        rw [div_le_div_iff₀ hetot_pos (mul_pos (by linarith) hetot_pos)]
        have hmul := mul_le_mul_of_nonneg_right hS_e hetot_pos.le
        ring_nf at hmul ⊢
        linarith
      have hp_fac_nonneg : (0 : ℚ) ≤ ((p : ℚ) - 1) / (p : ℚ) := div_nonneg (by linarith) (by linarith)
      have hmul_le := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdiv_le_e hp_fac_nonneg) hprod_nonneg
      refine le_trans (le_of_eq ?_) (hmul_le.trans (le_of_eq (mul_assoc _ _ _)))
      field_simp [hp_ne, hp1_ne]
    have hsum_lb := Finset.sum_le_sum hterm_e
    have hbij_m : ∑ e ∈ m.divisors,
          ((p : ℚ) - 1) * ((e : ℚ) / (e.totient : ℚ)) *
            ∏ q ∈ (m / e).primeFactors, (((q : ℚ) - 2) / ((q : ℚ) - 1)) =
        ((p : ℚ) - 1) * ∑ T ∈ m.primeFactors.powerset,
          (∏ q ∈ T, (q : ℚ) / ((q : ℚ) - 1)) *
            (∏ q ∈ m.primeFactors \ T, (((q : ℚ) - 2) / ((q : ℚ) - 1))) := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      congr 1
      refine Finset.sum_bij (fun e _ => e.primeFactors) ?_ ?_ ?_ ?_
      · intro e he
        rw [Finset.mem_powerset]
        exact Nat.primeFactors_mono (Nat.mem_divisors.mp he).1 hm_ne
      · intro e₁ he₁ e₂ he₂ h
        have hsq1 := hm_sq.squarefree_of_dvd (Nat.mem_divisors.mp he₁).1
        have hsq2 := hm_sq.squarefree_of_dvd (Nat.mem_divisors.mp he₂).1
        rw [← prod_primeFactors_of_squarefree hsq1, ← prod_primeFactors_of_squarefree hsq2, h]
      · intro T hT
        rw [Finset.mem_powerset] at hT
        refine ⟨∏ q ∈ T, q, Nat.mem_divisors.mpr ⟨?_, hm_ne⟩, ?_⟩
        · exact (Finset.prod_dvd_prod_of_subset T m.primeFactors (fun q => q) hT).trans
            (Nat.prod_primeFactors_dvd m)
        · ext q
          rw [Nat.mem_primeFactors]
          constructor
          · rintro ⟨hq, hq_dvd, _⟩
            obtain ⟨r, hrT, hqr⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hq_dvd
            have hr_prime := (Nat.mem_primeFactors.mp (hT hrT)).1
            rwa [(Nat.prime_dvd_prime_iff_eq hq hr_prime).mp hqr]
          · intro hqT
            have hq_prime := (Nat.mem_primeFactors.mp (hT hqT)).1
            refine ⟨hq_prime, Finset.dvd_prod_of_mem _ hqT, ?_⟩
            exact Finset.prod_ne_zero_iff.mpr fun r hr =>
              (Nat.mem_primeFactors.mp (hT hr)).1.ne_zero
      · intro e he
        have he_dvd := (Nat.mem_divisors.mp he).1
        have hsq_e := hm_sq.squarefree_of_dvd he_dvd
        have he_prod : (e : ℚ) = ∏ q ∈ e.primeFactors, (q : ℚ) := by
          conv_lhs => rw [← prod_primeFactors_of_squarefree hsq_e]
          rw [Nat.cast_prod]
        have htot_e : (e.totient : ℚ) = ∏ q ∈ e.primeFactors, ((q : ℚ) - 1) := by
          have h1 := totient_squarefree_mul (d := 1) hsq_e
          simp only [mul_one, Nat.totient_one, Nat.cast_one, one_mul] at h1
          rw [h1]
          refine Finset.prod_congr rfl fun q hq => ?_
          have hq_prime := (Nat.mem_primeFactors.mp hq).1
          rw [if_neg (fun h => hq_prime.ne_one (Nat.dvd_one.mp h))]
        have hpf_div : (m / e).primeFactors = m.primeFactors \ e.primeFactors := by
          ext q
          rw [Finset.mem_sdiff, Nat.mem_primeFactors, Nat.mem_primeFactors, Nat.mem_primeFactors]
          have hme_ne : m / e ≠ 0 :=
            (Nat.div_pos (Nat.le_of_dvd hm_pos he_dvd) (Nat.pos_of_mem_divisors he)).ne'
          constructor
          · rintro ⟨hq, hq_me, _⟩
            have hq_m := hq_me.trans (Nat.div_dvd_of_dvd he_dvd)
            refine ⟨⟨hq, hq_m, hm_ne⟩, ?_⟩
            rintro ⟨_, hq_e, _⟩
            have hmul_me : e * (m / e) = m := Nat.mul_div_cancel' he_dvd
            have hsq_q : q * q ∣ m := by rw [← hmul_me]; exact mul_dvd_mul hq_e hq_me
            exact hq.ne_one (Nat.isUnit_iff.mp (hm_sq q hsq_q))
          · rintro ⟨⟨hq, hq_m, _⟩, hq_not_e⟩
            refine ⟨hq, ?_, hme_ne⟩
            have hmul_me : e * (m / e) = m := Nat.mul_div_cancel' he_dvd
            rw [← hmul_me] at hq_m
            refine (hq.dvd_mul.mp hq_m).resolve_left fun hq_e => ?_
            exact hq_not_e ⟨hq, hq_e, (Nat.pos_of_mem_divisors he).ne'⟩
        rw [he_prod, htot_e, ← Finset.prod_div_distrib, hpf_div]
    rw [hbij_m, sum_powerset_rat_identity m.primeFactors
      (fun q hq => (Nat.mem_primeFactors.mp hq).1.two_le), hm_pf_card] at hsum_lb
    exact hsum_lb
  have hcyc_lb : (2 : ℚ) ^ (t + 1) ≤ (Arxiv.«2604.08040».cyc G : ℚ) := by
    have h1 : ((N.divisors.card : ℚ)) + ((p : ℚ) - 1) * (2 : ℚ) ^ (t - 1) ≤
        (Arxiv.«2604.08040».cyc G : ℚ) := by
      have h2 := hsum_m.trans hsum_ge
      rw [← hrich] at h2
      linarith
    rw [hdiv_card_eq] at h1
    push_cast at h1
    have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp_prime.two_le
    have hpow2 : (2 : ℚ) ^ (t + 1) = 4 * (2 : ℚ) ^ (t - 1) := by
      have ht1 : t + 1 = 2 + (t - 1) := by omega
      rw [ht1, pow_add]
      norm_num
    have hpos_pow : (0 : ℚ) ≤ (2 : ℚ) ^ (t - 1) := by positivity
    nlinarith
  have hcyc_lt_q : (Arxiv.«2604.08040».cyc G : ℚ) < (2 : ℚ) ^ (t + 1) := by
    exact_mod_cast hcyc'
  linarith

end Solvable

theorem OMA.solution : type_of% @Arxiv.«2604.08040».solvable_of_cyc_lt_two_pow_succ := by
  intro G _ _ hcyc
  have : IsZGroup G := isZGroup_of_cyc_lt_two_pow_succ hcyc
  infer_instance
