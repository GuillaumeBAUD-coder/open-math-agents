import OMAReductions.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_R1

/-!
# Proof of `ConjugacyClassSizes.conjClassSizes_iff_sym_three.R1.H1`

Proves the elementary structure of finite nontrivial anti-homogeneous groups `G`:
1. Rationality: for every `x : G` and `n` coprime to `Nat.card G`, `x ↦ x ^ n` is a bijection on
   `G` that maps the conjugacy class of `x` onto that of `x ^ n`. Hence the two classes have equal
   cardinality and therefore coincide, giving `IsConj x (x ^ n)`.
2. Trivial center: directly `ConjugacyClassSizes.trivial_center_of_hasDistinctConjClassSizes`.
3. Even order: if `Nat.card G` were odd, then `Nat.card G - 1` is coprime to `Nat.card G`, so
   every element `g : G` is conjugate to `g ^ (Nat.card G - 1) = g⁻¹`. Choosing `g ≠ 1` and
   `c * g * c⁻¹ = g⁻¹`, `c ^ 2` commutes with `g`; since `c` has odd order, `c` is a power of
   `c ^ 2` and also commutes with `g`, forcing `g ^ 2 = 1` and hence `g = 1`, contradiction.
-/

namespace ConjugacyClassSizesR1H1Proof

open ConjugacyClassSizes

private lemma isConj_pow_of_coprime {G : Type} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (x : G) (n : ℕ) (hcop : (Nat.card G).Coprime n) :
    IsConj x (x ^ n) := by
  -- Find inverse m of n mod Nat.card G
  have hcard_pos : 0 < Nat.card G := Nat.card_pos
  have : NeZero (Nat.card G) := ⟨hcard_pos.ne'⟩
  -- pow n is a bijection on G because gcd(|G|, n) = 1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n * m) % Nat.card G = 1 % Nat.card G := by
    have hu : IsUnit (n : ZMod (Nat.card G)) := (ZMod.isUnit_iff_coprime n (Nat.card G)).mpr hcop.symm
    obtain ⟨u, hu'⟩ := hu
    refine ⟨((u⁻¹ : (ZMod (Nat.card G))ˣ) : ZMod (Nat.card G)).val, ?_⟩
    have h1 : ((n * ((u⁻¹ : (ZMod (Nat.card G))ˣ) : ZMod (Nat.card G)).val : ℕ) : ZMod (Nat.card G)) = 1 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ← hu']
      exact_mod_cast u.mul_inv
    exact (ZMod.natCast_eq_natCast_iff _ 1 (Nat.card G)).mp (by simpa using h1)
  have hpow_inv : ∀ y : G, (y ^ n) ^ m = y := fun y => by
    rw [← pow_mul]
    have hord : orderOf y ∣ Nat.card G := orderOf_dvd_natCard y
    have hmod : n * m ≡ 1 [MOD orderOf y] := Nat.ModEq.of_dvd hord hm
    simpa [pow_one] using pow_eq_pow_iff_modEq.mpr hmod
  have hpow_inv' : ∀ y : G, (y ^ m) ^ n = y := fun y => by
    rw [← pow_mul, mul_comm, pow_mul, hpow_inv]
  have hbij : Function.Bijective (fun y : G => y ^ n) :=
    Function.bijective_iff_has_inverse.mpr ⟨fun y => y ^ m, hpow_inv, hpow_inv'⟩
  have hconj_pow : ∀ {a b : G} (k : ℕ), IsConj a b → IsConj (a ^ k) (b ^ k) := by
    intro a b k hab
    obtain ⟨c, rfl⟩ := isConj_iff.mp hab
    rw [isConj_iff]
    exact ⟨c, by simp [conj_pow]⟩
  -- Build a bijection between carriers of ConjClasses.mk x and ConjClasses.mk (x ^ n)
  let c1 : ConjClasses G := ConjClasses.mk x
  let c2 : ConjClasses G := ConjClasses.mk (x ^ n)
  have hcard_eq : conjClassCard c1 = conjClassCard c2 := by
    unfold conjClassCard
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1 ^ n, by
          have hy : IsConj y.1 x :=
            (ConjClasses.mk_eq_mk_iff_isConj).mp (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)
          rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
          exact hconj_pow n hy⟩
        invFun := fun z => ⟨z.1 ^ m, by
          have hz : IsConj z.1 (x ^ n) :=
            (ConjClasses.mk_eq_mk_iff_isConj).mp (ConjClasses.mem_carrier_iff_mk_eq.mp z.2)
          rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
          have := hconj_pow m hz
          rwa [hpow_inv x] at this⟩
        left_inv := fun y => Subtype.ext (hpow_inv y.1)
        right_inv := fun z => Subtype.ext (hpow_inv' z.1) }
  have hmk : c1 = c2 := h hcard_eq
  exact (ConjClasses.mk_eq_mk_iff_isConj).mp hmk

private lemma even_card_of_rational {G : Type} [Group G] [Fintype G] [Nontrivial G]
    (hrat : ∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n)) :
    Even (Nat.card G) := by
  by_contra hnot
  have hodd : Odd (Nat.card G) := Nat.not_even_iff_odd.mp hnot
  obtain ⟨g, hg1⟩ := exists_ne (1 : G)
  have hcard_gt1 : 1 < Nat.card G := by
    have := Fintype.one_lt_card (α := G)
    rwa [Nat.card_eq_fintype_card]
  have hcop : (Nat.card G).Coprime (Nat.card G - 1) := by
    have : Nat.card G = (Nat.card G - 1) + 1 := by omega
    conv_lhs => rw [this]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have hconj_pow : IsConj g (g ^ (Nat.card G - 1)) := hrat g (Nat.card G - 1) hcop
  have hginv : g ^ (Nat.card G - 1) = g⁻¹ := by
    have h1 : g ^ (Nat.card G - 1) * g = 1 := by
      rw [← pow_succ, show Nat.card G - 1 + 1 = Nat.card G by omega]
      exact pow_card_eq_one'
    exact eq_inv_of_mul_eq_one_left h1
  rw [hginv] at hconj_pow
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj_pow
  -- hc : c * g * c⁻¹ = g⁻¹
  have hc2 : c ^ 2 * g * (c ^ 2)⁻¹ = g := by
    have hinv_hc : c * g⁻¹ * c⁻¹ = g := by
      have := congrArg (·⁻¹) hc
      simp only [mul_inv_rev, inv_inv] at this
      simpa [mul_assoc] using this
    calc c ^ 2 * g * (c ^ 2)⁻¹
        = c * (c * g * c⁻¹) * c⁻¹ := by rw [sq, mul_inv_rev]; group
      _ = c * g⁻¹ * c⁻¹ := by rw [hc]
      _ = g := hinv_hc
  have hc2_comm : Commute (c ^ 2) g := by
    rw [Commute, SemiconjBy]
    have := congrArg (· * c ^ 2) hc2
    simpa [mul_assoc] using this
  -- Since |G| is odd, orderOf c is odd, so c is a power of c ^ 2
  have hord_dvd : orderOf c ∣ Nat.card G := orderOf_dvd_natCard c
  have hord_odd : Odd (orderOf c) := hodd.of_dvd_nat hord_dvd
  obtain ⟨k, hk⟩ := hord_odd
  have hc_pow : (c ^ 2) ^ (k + 1) = c := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf c + 1 by omega, pow_succ', pow_orderOf_eq_one,
      mul_one]
  have hc_comm : Commute c g := by
    rw [← hc_pow]
    exact hc2_comm.pow_left (k + 1)
  have hgeq : g = g⁻¹ := by
    calc g = c * g * c⁻¹ := by rw [hc_comm.eq, mul_inv_cancel_right]
      _ = g⁻¹ := hc
  have hg2 : g ^ 2 = 1 := by
    rw [sq]
    conv_lhs => rhs; rw [hgeq]
    exact mul_inv_cancel g
  have hord_g_dvd2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  have hord_g_odd : Odd (orderOf g) := hodd.of_dvd_nat (orderOf_dvd_natCard g)
  have hord_g1 : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord_g_dvd2 with h | h
    · exact h
    · rw [h] at hord_g_odd
      exact absurd hord_g_odd (by decide)
  exact hg1 (orderOf_eq_one_iff.mp hord_g1)

end ConjugacyClassSizesR1H1Proof

theorem OMA.solution : OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_R1.H1 := by
  intro G _ _ _ h
  have hrat := ConjugacyClassSizesR1H1Proof.isConj_pow_of_coprime h
  exact ⟨hrat, ConjugacyClassSizes.trivial_center_of_hasDistinctConjClassSizes h,
    ConjugacyClassSizesR1H1Proof.even_card_of_rational hrat⟩
