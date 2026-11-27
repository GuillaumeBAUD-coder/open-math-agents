import OMAReductions.R_Erdos170_erdos170_existing_bounds_R1
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

namespace OMA.H1Proof

/-! # Scratch proof of Erdos170 H1 (Erdos-Gal 1948 limit existence) -/

open scoped BigOperators

section Singer

lemma pow_sub_one_roots_eq_image {F K : Type*} [Field F] [Fintype F] [Field K]
    (φ : F →+* K) (x : K) (hx : x ^ (Fintype.card F - 1) = 1) :
    ∃ u : Fˣ, φ u = x := by
  classical
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  let m := Fintype.card F - 1
  have hm : 0 < m := by omega
  let p : Polynomial K := Polynomial.X ^ m - 1
  have hp_ne : p ≠ 0 := by
    intro h0
    have hcoeff : p.coeff m = 0 := by rw [h0, Polynomial.coeff_zero]
    simp only [p, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one] at hcoeff
    simp [hm.ne'] at hcoeff
  have hdeg : p.natDegree ≤ m := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp [Polynomial.natDegree_one]
  have hroots_card : p.roots.toFinset.card ≤ m :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans hdeg)
  let S : Finset K := (Finset.univ : Finset Fˣ).image (fun u : Fˣ => φ (u : F))
  have hS_card : S.card = m := by
    rw [Finset.card_image_of_injective _ (fun a b h => Units.ext (φ.injective h)),
      Finset.card_univ, Fintype.card_units]
  have hS_sub : S ⊆ p.roots.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨u, _, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot.def]
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    have hu : u ^ m = 1 := by
      change u ^ (Fintype.card F - 1) = 1
      rw [← Fintype.card_units]
      exact pow_card_eq_one
    have h1 : (φ (u : F)) ^ m = φ ((u ^ m : Fˣ) : F) := by
      rw [Units.val_pow_eq_pow_val, map_pow]
    rw [h1, hu, Units.val_one, map_one, sub_self]
  have hS_eq : S = p.roots.toFinset := Finset.eq_of_subset_of_card_le hS_sub (by omega)
  have hx_mem : x ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot.def]
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    rw [show m = Fintype.card F - 1 from rfl, hx, sub_self]
  rw [← hS_eq, Finset.mem_image] at hx_mem
  obtain ⟨u, _, hu_eq⟩ := hx_mem
  exact ⟨u, hu_eq⟩

lemma singer_difference_set (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : 1 ≤ a) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (p ^ (2 * a) + p ^ a + 1) ∧
      0 ∈ S ∧ S.card = p ^ a + 1 ∧
      ∀ r ∈ Finset.range (p ^ (2 * a) + p ^ a + 1),
        ∃ s₁ ∈ S, ∃ s₀ ∈ S, (s₁ : ℤ) - (s₀ : ℤ) ≡ (r : ℤ) [ZMOD (p ^ (2 * a) + p ^ a + 1)] := by
  classical
  let q := p ^ a
  let P := q ^ 2 + q + 1
  have hq_ge : 2 ≤ q := by
    have hp : 2 ≤ p := Fact.out (p := p.Prime) |>.two_le
    calc 2 ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
  have hP_eq : p ^ (2 * a) + p ^ a + 1 = P := by
    change p ^ (2 * a) + q + 1 = q ^ 2 + q + 1
    rw [show 2 * a = a * 2 from mul_comm 2 a, pow_mul]
  rw [hP_eq]
  have hP_pos : 0 < P := by positivity
  let F := GaloisField p a
  let K := GaloisField p (3 * a)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card F = q := by
    dsimp only [F, q]
    rw [Fintype.card_eq_nat_card, GaloisField.card p a (by omega)]
  have hcardK : Fintype.card K = q ^ 3 := by
    dsimp only [K, q]
    rw [Fintype.card_eq_nat_card, GaloisField.card p (3 * a) (by omega)]
    rw [mul_comm 3 a, pow_mul]
  have hdvd : Module.finrank (ZMod p) F ∣ Module.finrank (ZMod p) K := by
    rw [GaloisField.finrank p (by omega), GaloisField.finrank p (by omega)]
    exact dvd_mul_left a 3
  obtain ⟨algF⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  let φ : F →+* K := algF.toRingHom
  obtain ⟨α, hα_gen⟩ := IsCyclic.exists_generator (α := Kˣ)
  let g : K := (α : K)
  have hord : orderOf α = (q - 1) * P := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hα_gen, Nat.card_eq_fintype_card,
      Fintype.card_units, hcardK]
    have hq1 : 1 ≤ q := by omega
    have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q (by omega)
    zify [hq1, hq3]
    dsimp only [P]
    push_cast
    ring
  have hgP_pow : (g ^ P) ^ (q - 1) = 1 := by
    have : (α ^ P) ^ (q - 1) = 1 := by
      rw [← pow_mul, mul_comm P (q - 1), ← hord, pow_orderOf_eq_one]
    simpa [g] using congrArg (fun u : Kˣ => (u : K)) this
  have hcardF_eq : Fintype.card F - 1 = q - 1 := by rw [hcardF]
  obtain ⟨u₀, hu₀⟩ := pow_sub_one_roots_eq_image φ (g ^ P) (hcardF_eq ▸ hgP_pow)
  have hlin_inj : Function.Injective (fun ab : F × F => φ ab.1 + φ ab.2 * g) := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
    have hb : b₁ = b₂ := by
      by_contra hne
      have hg_mem : g ∈ Set.range φ := by
        refine ⟨(a₂ - a₁) * (b₁ - b₂)⁻¹, ?_⟩
        have hsub : φ (b₁ - b₂) * g = φ (a₂ - a₁) := by
          simp only [map_sub]
          linear_combination heq
        have hne' : φ (b₁ - b₂) ≠ 0 := by
          intro h0
          apply hne
          exact sub_eq_zero.mp (φ.injective (h0.trans (map_zero φ).symm))
        rw [map_mul, map_inv₀, mul_comm (φ (a₂ - a₁)) _, ← hsub, ← mul_assoc,
          inv_mul_cancel₀ hne', one_mul]
      have hall_pow : ∀ m : ℕ, (g ^ m : K) ∈ Set.range φ := by
        intro m
        induction m with
        | zero => exact ⟨1, by simp⟩
        | succ m ih =>
          obtain ⟨c₁, hc₁⟩ := ih
          obtain ⟨c₂, hc₂⟩ := hg_mem
          exact ⟨c₁ * c₂, by simp [pow_succ, hc₁, hc₂]⟩
      have hK_sub : ∀ x : K, x ∈ Set.range φ := by
        intro x
        by_cases hx0 : x = 0
        · exact ⟨0, by simp [hx0]⟩
        · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hα_gen (Units.mk0 x hx0))
          have hm_nat : (α ^ (m % (orderOf α : ℤ)).toNat : Kˣ) = Units.mk0 x hx0 := by
            have hpos : (0 : ℤ) < orderOf α := by
              rw [hord]; exact_mod_cast Nat.mul_pos (by omega) hP_pos
            have hrem : 0 ≤ m % (orderOf α : ℤ) := Int.emod_nonneg m hpos.ne'
            rw [← zpow_natCast, Int.toNat_of_nonneg hrem]
            calc α ^ (m % (orderOf α : ℤ)) = α ^ (m % (orderOf α : ℤ) + (orderOf α : ℤ) * (m / (orderOf α : ℤ))) := by
                  rw [zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
              _ = α ^ m := by rw [Int.emod_add_mul_ediv]
              _ = Units.mk0 x hx0 := hm
          have hgx : g ^ (m % (orderOf α : ℤ)).toNat = x := by
            simpa [g] using congrArg (fun u : Kˣ => (u : K)) hm_nat
          rw [← hgx]
          exact hall_pow _
      have hsurj : Function.Surjective φ := hK_sub
      have hle := Fintype.card_le_of_surjective φ hsurj
      rw [hcardF, hcardK] at hle
      have hq2 : 4 ≤ q * q := by nlinarith
      have hq3 : q ^ 3 = q * (q * q) := by ring
      nlinarith
    subst hb
    have ha_eq : a₁ = a₂ := φ.injective (by linear_combination heq)
    subst ha_eq
    rfl
  let V : Finset K := (Finset.univ : Finset (F × F)).image (fun ab => φ ab.1 + φ ab.2 * g)
  have hV_card : V.card = q ^ 2 := by
    rw [Finset.card_image_of_injective _ hlin_inj, Finset.card_univ, Fintype.card_prod, hcardF]
    ring
  have hV_smul : ∀ (c : F) (v : K), v ∈ V → φ c * v ∈ V := by
    intro c v hv
    rw [Finset.mem_image] at hv ⊢
    obtain ⟨⟨a₁, b₁⟩, _, rfl⟩ := hv
    refine ⟨(c * a₁, c * b₁), Finset.mem_univ _, ?_⟩
    simp only [map_mul]
    ring
  have hV_sub : ∀ v₁ v₂ : K, v₁ ∈ V → v₂ ∈ V → v₁ - v₂ ∈ V := by
    intro v₁ v₂ hv₁ hv₂
    rw [Finset.mem_image] at hv₁ hv₂ ⊢
    obtain ⟨⟨a₁, b₁⟩, _, rfl⟩ := hv₁
    obtain ⟨⟨a₂, b₂⟩, _, rfl⟩ := hv₂
    refine ⟨(a₁ - a₂, b₁ - b₂), Finset.mem_univ _, ?_⟩
    simp only [map_sub]
    ring
  let S₀ : Finset ℕ := (Finset.range P).filter (fun i => g ^ i ∈ V)
  let Vpos : Finset K := V.erase 0
  have h0_mem_V : (0 : K) ∈ V := by
    rw [Finset.mem_image]
    exact ⟨(0, 0), Finset.mem_univ _, by simp⟩
  have hVpos_card : Vpos.card = q ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem h0_mem_V, hV_card]
  let ψ : Fˣ × S₀ → K := fun p => φ p.1 * g ^ (p.2 : ℕ)
  have hψ_mem : ∀ x : Fˣ × S₀, ψ x ∈ Vpos := by
    rintro ⟨u, ⟨i, hi⟩⟩
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_erase]
    refine ⟨?_, hV_smul u (g ^ i) hi.2⟩
    apply mul_ne_zero
    · intro h0
      exact Units.ne_zero u (φ.injective (h0.trans (map_zero φ).symm))
    · exact pow_ne_zero i (Units.ne_zero α)
  have hψ_inj : Function.Injective ψ := by
    rintro ⟨u₁, ⟨i₁, hi₁⟩⟩ ⟨u₂, ⟨i₂, hi₂⟩⟩ heq
    rw [Finset.mem_filter, Finset.mem_range] at hi₁ hi₂
    have hPow_eq : ∀ (x y : ℕ) (ux uy : Fˣ), x ≤ y → y < P → φ ux * g ^ x = φ uy * g ^ y →
        x = y ∧ ux = uy := by
      intro x y ux uy hxy hy_lt hmul
      have hdiff_pow : g ^ (y - x) = φ (ux * uy⁻¹ : Fˣ) := by
        have h1 : (g ^ y : K) = g ^ x * g ^ (y - x) := by
          rw [← pow_add, Nat.add_sub_of_le hxy]
        have hgx0 : g ^ x ≠ 0 := pow_ne_zero x (Units.ne_zero α)
        have huy0 : φ (uy : F) ≠ 0 := fun h0 => Units.ne_zero uy (φ.injective (h0.trans (map_zero φ).symm))
        rw [h1] at hmul
        have hmul' : g ^ (y - x) * φ (uy : F) = φ (ux : F) := by
          apply mul_right_cancel₀ hgx0
          linear_combination -hmul
        calc g ^ (y - x) = (φ (uy : F))⁻¹ * (φ (ux : F)) := by
              rw [← hmul', mul_comm (g ^ (y - x)) _, ← mul_assoc, inv_mul_cancel₀ huy0, one_mul]
          _ = φ ((ux * uy⁻¹ : Fˣ) : F) := by
              rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, mul_comm]
      have hpow_q1 : (α ^ (y - x)) ^ (q - 1) = 1 := by
        apply Units.ext
        push_cast
        change (g ^ (y - x)) ^ (q - 1) = 1
        rw [hdiff_pow]
        have h_u : (ux * uy⁻¹) ^ (q - 1) = 1 := by
          rw [← hcardF_eq, ← Fintype.card_units]
          exact pow_card_eq_one
        have : (φ ((ux * uy⁻¹ : Fˣ) : F)) ^ (q - 1) = φ (((ux * uy⁻¹) ^ (q - 1) : Fˣ) : F) := by
          rw [Units.val_pow_eq_pow_val, map_pow]
        rw [this, h_u, Units.val_one, map_one]
      rw [← pow_mul] at hpow_q1
      have hdvd_ord : orderOf α ∣ (y - x) * (q - 1) := orderOf_dvd_of_pow_eq_one hpow_q1
      rw [hord, mul_comm (q - 1) P] at hdvd_ord
      have hPdvd : P ∣ (y - x) := Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd_ord
      have hyx_eq : y = x := by
        by_contra hne
        have hpos : 0 < y - x := by omega
        have := Nat.le_of_dvd hpos hPdvd
        omega
      have hu_eq : ux = uy := by
        apply Units.ext
        apply φ.injective
        have hmul'' : φ (ux : F) * g ^ y = φ (uy : F) * g ^ y := by
          rwa [← hyx_eq] at hmul
        have hgy0 : g ^ y ≠ 0 := pow_ne_zero y (Units.ne_zero α)
        exact mul_right_cancel₀ hgy0 hmul''
      exact ⟨hyx_eq.symm, hu_eq⟩
    by_cases h12 : i₁ ≤ i₂
    · obtain ⟨hi_eq, hu_eq⟩ := hPow_eq i₁ i₂ u₁ u₂ h12 hi₂.1 heq
      ext <;> simp [hi_eq, hu_eq]
    · obtain ⟨hi_eq, hu_eq⟩ := hPow_eq i₂ i₁ u₂ u₁ (by omega) hi₁.1 heq.symm
      ext <;> simp [hi_eq.symm, hu_eq.symm]
  have hψ_surj : ∀ v ∈ Vpos, ∃ x : Fˣ × S₀, ψ x = v := by
    intro v hv
    rw [Finset.mem_erase] at hv
    obtain ⟨hv0, hvV⟩ := hv
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hα_gen (Units.mk0 v hv0))
    have hpos : (0 : ℤ) < orderOf α := by
      rw [hord]; exact_mod_cast Nat.mul_pos (by omega) hP_pos
    let m₀ := (m % (orderOf α : ℤ)).toNat
    have hm₀ : (α ^ m₀ : Kˣ) = Units.mk0 v hv0 := by
      have hrem : 0 ≤ m % (orderOf α : ℤ) := Int.emod_nonneg m hpos.ne'
      dsimp only [m₀]
      rw [← zpow_natCast, Int.toNat_of_nonneg hrem]
      calc α ^ (m % (orderOf α : ℤ)) = α ^ (m % (orderOf α : ℤ) + (orderOf α : ℤ) * (m / (orderOf α : ℤ))) := by
            rw [zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
        _ = α ^ m := by rw [Int.emod_add_mul_ediv]
        _ = Units.mk0 v hv0 := hm
    have hgm₀ : g ^ m₀ = v := by
      simpa [g] using congrArg (fun u : Kˣ => (u : K)) hm₀
    let j := m₀ / P
    let i := m₀ % P
    have hi_lt : i < P := Nat.mod_lt m₀ hP_pos
    have hm₀_eq : m₀ = j * P + i := by
      have := Nat.div_add_mod m₀ P
      rw [Nat.mul_comm] at this
      exact this.symm
    have hgv : v = φ (u₀ ^ j : Fˣ) * g ^ i := by
      rw [← hgm₀, hm₀_eq, pow_add, mul_comm j P, pow_mul, ← hu₀, ← map_pow]
      simp [Units.val_pow_eq_pow_val]
    have hgi_mem : g ^ i ∈ V := by
      have h1 : g ^ i = φ ((u₀ ^ j)⁻¹ : Fˣ) * v := by
        rw [hgv, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val]
        rw [inv_mul_cancel₀ (Units.ne_zero _), map_one, one_mul]
      rw [h1]
      exact hV_smul _ v hvV
    refine ⟨(u₀ ^ j, ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi_lt, hgi_mem⟩⟩), ?_⟩
    exact hgv.symm
  have hS₀_card : S₀.card = q + 1 := by
    have hcard_eq : (Finset.univ : Finset (Fˣ × S₀)).card = Vpos.card := by
      refine Finset.card_bij (fun x _ => ψ x) (fun x _ => hψ_mem x) (fun _ _ _ _ h => hψ_inj h) ?_
      intro b hb
      obtain ⟨x, hx⟩ := hψ_surj b hb
      exact ⟨x, Finset.mem_univ _, hx⟩
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_units, Fintype.card_coe, hcardF, hVpos_card] at hcard_eq
    have hq2_sub : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h1 : 1 ≤ q := by omega
      zify [h1, show 1 ≤ q ^ 2 by nlinarith]
      ring
    rw [hq2_sub] at hcard_eq
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q - 1) hcard_eq
  have hS₀_diff : ∀ r ∈ Finset.range P,
      ∃ s₁ ∈ S₀, ∃ s₀ ∈ S₀, (s₁ : ℤ) - (s₀ : ℤ) ≡ (r : ℤ) [ZMOD P] := by
    intro r hr_mem
    rw [Finset.mem_range] at hr_mem
    by_cases hr0 : r = 0
    · obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S₀.card)
      refine ⟨s, hs, s, hs, ?_⟩
      simp [hr0]
    · let fr : V × V → K := fun p => (p.1 : K) - g ^ r * (p.2 : K)
      have hcard_lt : Fintype.card K < Fintype.card (V × V) := by
        rw [Fintype.card_prod, Fintype.card_coe, hV_card, hcardK]
        nlinarith
      obtain ⟨⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩, ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩, hne, heq⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt fr hcard_lt
      dsimp only [fr] at heq
      let x := v₁ - w₁
      let y := v₂ - w₂
      have hxV : x ∈ V := hV_sub v₁ w₁ hv₁ hw₁
      have hyV : y ∈ V := hV_sub v₂ w₂ hv₂ hw₂
      have hxy : x = g ^ r * y := by dsimp only [x, y]; linear_combination heq
      have hy0 : y ≠ 0 := by
        intro hy_zero
        have hv2w2 : v₂ = w₂ := sub_eq_zero.mp hy_zero
        have hx0 : x = 0 := by rw [hxy, hy_zero, mul_zero]
        have hv1w1 : v₁ = w₁ := sub_eq_zero.mp hx0
        apply hne
        ext <;> simp [hv1w1, hv2w2]
      have hx0 : x ≠ 0 := by
        rw [hxy]
        exact mul_ne_zero (pow_ne_zero r (Units.ne_zero α)) hy0
      obtain ⟨⟨u₁, ⟨s₁, hs₁⟩⟩, hψ₁⟩ := hψ_surj x (Finset.mem_erase.mpr ⟨hx0, hxV⟩)
      obtain ⟨⟨u₂, ⟨s₀, hs₀⟩⟩, hψ₀⟩ := hψ_surj y (Finset.mem_erase.mpr ⟨hy0, hyV⟩)
      dsimp only [ψ] at hψ₁ hψ₀
      have hgx_eq : φ (u₁ : F) * g ^ s₁ = φ (u₂ : F) * g ^ (s₀ + r) := by
        calc φ (u₁ : F) * g ^ s₁ = x := hψ₁
          _ = g ^ r * y := hxy
          _ = g ^ r * (φ (u₂ : F) * g ^ s₀) := by rw [← hψ₀]
          _ = φ (u₂ : F) * (g ^ s₀ * g ^ r) := by ring
          _ = φ (u₂ : F) * g ^ (s₀ + r) := by rw [← pow_add]
      have hpow_k : (g ^ s₁) ^ (q - 1) = (g ^ (s₀ + r)) ^ (q - 1) := by
        have h1 : (g ^ s₁ : K) = φ ((u₁⁻¹ * u₂ : Fˣ) : F) * g ^ (s₀ + r) := by
          have hu1_ne : φ (u₁ : F) ≠ 0 := fun h0 => Units.ne_zero u₁ (φ.injective (h0.trans (map_zero φ).symm))
          calc g ^ s₁ = (φ (u₁ : F))⁻¹ * (φ (u₁ : F) * g ^ s₁) := by rw [← mul_assoc, inv_mul_cancel₀ hu1_ne, one_mul]
            _ = (φ (u₁ : F))⁻¹ * (φ (u₂ : F) * g ^ (s₀ + r)) := by rw [hgx_eq]
            _ = ((φ (u₁ : F))⁻¹ * φ (u₂ : F)) * g ^ (s₀ + r) := by ring
            _ = φ ((u₁⁻¹ * u₂ : Fˣ) : F) * g ^ (s₀ + r) := by
              rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
        have hu_pow : (φ ((u₁⁻¹ * u₂ : Fˣ) : F)) ^ (q - 1) = 1 := by
          have h_u : (u₁⁻¹ * u₂) ^ (q - 1) = 1 := by
            rw [← hcardF_eq, ← Fintype.card_units]
            exact pow_card_eq_one
          have : (φ ((u₁⁻¹ * u₂ : Fˣ) : F)) ^ (q - 1) = φ (((u₁⁻¹ * u₂) ^ (q - 1) : Fˣ) : F) := by
            rw [Units.val_pow_eq_pow_val, map_pow]
          rw [this, h_u, Units.val_one, map_one]
        rw [h1, mul_pow, hu_pow, one_mul]
      have hα_pow : α ^ (s₁ * (q - 1)) = α ^ ((s₀ + r) * (q - 1)) := by
        apply Units.ext
        push_cast
        change (g ^ (s₁ * (q - 1))) = g ^ ((s₀ + r) * (q - 1))
        simpa only [pow_mul] using hpow_k
      have hdvd_z : ((q - 1 : ℕ) : ℤ) * (P : ℤ) ∣ ((q - 1 : ℕ) : ℤ) * ((s₁ : ℤ) - ((s₀ : ℤ) + (r : ℤ))) := by
        have hdiff_pow : α ^ (((s₁ : ℤ) - ((s₀ : ℤ) + (r : ℤ))) * ((q - 1 : ℕ) : ℤ)) = 1 := by
          have heq_exp : ((s₁ : ℤ) - ((s₀ : ℤ) + (r : ℤ))) * ((q - 1 : ℕ) : ℤ) =
              ((s₁ * (q - 1) : ℕ) : ℤ) - (((s₀ + r) * (q - 1) : ℕ) : ℤ) := by push_cast; ring
          rw [heq_exp, zpow_sub, zpow_natCast, zpow_natCast, hα_pow, mul_inv_cancel]
        have hdvd1 : (orderOf α : ℤ) ∣ ((s₁ : ℤ) - ((s₀ : ℤ) + (r : ℤ))) * ((q - 1 : ℕ) : ℤ) :=
          orderOf_dvd_iff_zpow_eq_one.mpr hdiff_pow
        rw [hord] at hdvd1
        push_cast at hdvd1 ⊢
        simpa only [mul_comm] using hdvd1
      have hP_dvd : (P : ℤ) ∣ (s₁ : ℤ) - ((s₀ : ℤ) + (r : ℤ)) :=
        Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast (by omega : q - 1 ≠ 0)) hdvd_z
      refine ⟨s₁, hs₁, s₀, hs₀, ?_⟩
      rw [Int.modEq_iff_dvd]
      have : (r : ℤ) - ((s₁ : ℤ) - (s₀ : ℤ)) = -((s₁ : ℤ) - ((s₀ : ℤ) + (r : ℤ))) := by ring
      rw [this]
      exact dvd_neg.mpr hP_dvd
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < S₀.card)
  have hc_lt : c < P := (Finset.mem_range.mp (Finset.mem_filter.mp hc).1)
  let shift : ℕ → ℕ := fun s => (s + P - c) % P
  let S : Finset ℕ := S₀.image shift
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨s, _, rfl⟩ := hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hP_pos)
  · rw [Finset.mem_image]
    refine ⟨c, hc, ?_⟩
    dsimp only [shift]
    have : c + P - c = P := by omega
    rw [this, Nat.mod_self]
  · rw [Finset.card_image_of_injOn ?_, hS₀_card]
    intro x hx y hy heq
    have hx_lt : x < P := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hy_lt : y < P := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    dsimp only [shift] at heq
    have hmod : ((x + P - c : ℕ) : ℤ) ≡ ((y + P - c : ℕ) : ℤ) [ZMOD P] := by
      rw [Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod, heq]
    have hdvd_xy : (P : ℤ) ∣ (x : ℤ) - (y : ℤ) := by
      have h1 := Int.modEq_iff_dvd.mp hmod
      have hxc : c ≤ x + P := by omega
      have hyc : c ≤ y + P := by omega
      have hrew : ((y + P - c : ℕ) : ℤ) - ((x + P - c : ℕ) : ℤ) = (y : ℤ) - (x : ℤ) := by
        rw [Nat.cast_sub hxc, Nat.cast_sub hyc]; push_cast; ring
      rw [hrew] at h1
      have : (x : ℤ) - (y : ℤ) = -((y : ℤ) - (x : ℤ)) := by ring
      rw [this]; exact dvd_neg.mpr h1
    by_contra hne
    have hne_z : (x : ℤ) - (y : ℤ) ≠ 0 := by omega
    have hdvd_nat : P ∣ ((x : ℤ) - (y : ℤ)).natAbs := Int.natCast_dvd.mp hdvd_xy
    have hpos_nat : 0 < ((x : ℤ) - (y : ℤ)).natAbs := Int.natAbs_pos.mpr hne_z
    have hle := Nat.le_of_dvd hpos_nat hdvd_nat
    omega
  · intro r hr_mem
    obtain ⟨s₁, hs₁, s₀, hs₀, hmod⟩ := hS₀_diff r hr_mem
    have hs₁_lt : s₁ < P := Finset.mem_range.mp (Finset.mem_filter.mp hs₁).1
    have hs₀_lt : s₀ < P := Finset.mem_range.mp (Finset.mem_filter.mp hs₀).1
    refine ⟨shift s₁, Finset.mem_image_of_mem shift hs₁, shift s₀, Finset.mem_image_of_mem shift hs₀, ?_⟩
    dsimp only [shift]
    have h1 : (((s₁ + P - c) % P : ℕ) : ℤ) ≡ (s₁ : ℤ) - (c : ℤ) [ZMOD P] := by
      rw [Int.ModEq, Int.natCast_mod, Int.emod_emod]
      have hle1 : c ≤ s₁ + P := by omega
      rw [← Int.ModEq, Int.modEq_iff_dvd, Nat.cast_sub hle1]
      push_cast
      exact ⟨-1, by ring⟩
    have h0 : (((s₀ + P - c) % P : ℕ) : ℤ) ≡ (s₀ : ℤ) - (c : ℤ) [ZMOD P] := by
      rw [Int.ModEq, Int.natCast_mod, Int.emod_emod]
      have hle0 : c ≤ s₀ + P := by omega
      rw [← Int.ModEq, Int.modEq_iff_dvd, Nat.cast_sub hle0]
      push_cast
      exact ⟨-1, by ring⟩
    have hP_z : (P : ℤ) = (p : ℤ) ^ (2 * a) + (p : ℤ) ^ a + 1 := by
      have := congrArg (Nat.cast (R := ℤ)) hP_eq.symm
      simpa using this
    rw [← hP_z]
    calc (((s₁ + P - c) % P : ℕ) : ℤ) - (((s₀ + P - c) % P : ℕ) : ℤ)
        ≡ ((s₁ : ℤ) - (c : ℤ)) - ((s₀ : ℤ) - (c : ℤ)) [ZMOD P] := h1.sub h0
      _ = (s₁ : ℤ) - (s₀ : ℤ) := by ring
      _ ≡ (r : ℤ) [ZMOD P] := hmod

end Singer

section ErdosGal

open scoped Topology

lemma exists_grid_ruler (N : ℕ) :
    ∃ R ∈ Erdos170.PerfectRulersLengthN N, R.card ≤ 2 * Nat.sqrt N + 5 := by
  by_cases hN : N ≤ 4
  · refine ⟨Erdos170.TrivialRuler N, Erdos170.trivial_ruler_is_perfect N, ?_⟩
    rw [Erdos170.TrivialRuler, Finset.card_range]
    omega
  · have h5 : 5 ≤ N := by omega
    let s := Nat.sqrt N
    have hs2 : 2 ≤ s := Nat.le_sqrt.mpr (by omega)
    have hs_sq : s * s ≤ N := Nat.sqrt_le N
    let m := s + 1
    have hm_le_N : m ≤ N := by dsimp only [m]; nlinarith
    have hN_lt_m2 : N < m * m := Nat.lt_succ_sqrt N
    let R : Finset ℕ :=
      Finset.range (m + 1) ∪ ((Finset.range (m + 1)).image (fun j => j * m)).filter (· ≤ N) ∪ {N}
    refine ⟨R, ?_, ?_⟩
    · rw [Erdos170.PerfectRulersLengthN, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_range]
        simp only [R, Finset.mem_union, Finset.mem_filter, Finset.mem_image,
          Finset.mem_range, Finset.mem_singleton] at hx
        rcases hx with (hx | ⟨⟨j, _, rfl⟩, hle⟩) | rfl <;> omega
      · intro k hk
        rw [Finset.mem_range] at hk
        by_cases hkm : k + m ≤ N
        · let q := k / m
          let r := k % m
          have hm_pos : 0 < m := by omega
          have hr_lt : r < m := Nat.mod_lt k hm_pos
          have hdiv : q * m + r = k := by rw [Nat.mul_comm]; exact Nat.div_add_mod k m
          have hq_lt : q < m := by
            by_contra hge
            have h1 : m * m ≤ q * m := Nat.mul_le_mul_right m (Nat.not_lt.mp hge)
            omega
          by_cases hr0 : r = 0
          · refine ⟨0, ?_, q * m, ?_, by omega⟩
            · simp only [R, Finset.mem_union, Finset.mem_range]
              left; left; omega
            · simp only [R, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
              left; right; exact ⟨⟨q, by omega, rfl⟩, by omega⟩
          · refine ⟨m - r, ?_, (q + 1) * m, ?_, ?_⟩
            · simp only [R, Finset.mem_union, Finset.mem_range]
              left; left; omega
            · simp only [R, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
              left; right
              refine ⟨⟨q + 1, by omega, rfl⟩, ?_⟩
              have hmul : (q + 1) * m = q * m + m := by ring
              omega
            · have hmul : (q + 1) * m = q * m + m := by ring
              omega
        · refine ⟨N - k, ?_, N, ?_, by omega⟩
          · simp only [R, Finset.mem_union, Finset.mem_range]
            left; left; omega
          · simp only [R, Finset.mem_union, Finset.mem_singleton, or_true]
    · have h1 : (Finset.range (m + 1)).card = m + 1 := Finset.card_range _
      have h2 : (((Finset.range (m + 1)).image (fun j => j * m)).filter (· ≤ N)).card ≤ m + 1 :=
        (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (Finset.card_range _).le)
      have h3 : ({N} : Finset ℕ).card = 1 := Finset.card_singleton N
      have hu1 := Finset.card_union_le (Finset.range (m + 1))
        (((Finset.range (m + 1)).image (fun j => j * m)).filter (· ≤ N))
      have hu2 := Finset.card_union_le
        (Finset.range (m + 1) ∪ ((Finset.range (m + 1)).image (fun j => j * m)).filter (· ≤ N)) {N}
      have hR_le : R.card ≤ 2 * m + 3 := by dsimp only [R]; omega
      dsimp only [m, s] at hR_le
      omega

lemma F_le_card_of_mem {N : ℕ} {A : Finset ℕ} (hA : A ∈ Erdos170.PerfectRulersLengthN N) :
    Erdos170.F N ≤ A.card := by
  unfold Erdos170.F
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem Finset.card hA)

lemma F_le_real_grid (N : ℕ) : (Erdos170.F N : ℝ) ≤ 2 * √(N : ℝ) + 5 := by
  obtain ⟨R, hR_mem, hR_card⟩ := exists_grid_ruler N
  have h1 : (Erdos170.F N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) + 5 := by
    exact_mod_cast (F_le_card_of_mem hR_mem).trans hR_card
  have h2 : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
    have hsq : ((Nat.sqrt N : ℝ)) ^ 2 ≤ (N : ℝ) := by
      exact_mod_cast Nat.sqrt_le' N
    calc (Nat.sqrt N : ℝ) = √(((Nat.sqrt N : ℝ)) ^ 2) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ √(N : ℝ) := Real.sqrt_le_sqrt hsq
  linarith

lemma exists_ruler_mul_singer {M P q : ℕ} (hM : 1 ≤ M) (hP : 1 ≤ P)
    (A : Finset ℕ) (hA : A ∈ Erdos170.PerfectRulersLengthN M)
    (S : Finset ℕ) (hS_sub : S ⊆ Finset.range P) (hS_card : S.card = q + 1)
    (hS_diff : ∀ r ∈ Finset.range P,
      ∃ s₁ ∈ S, ∃ s₀ ∈ S, (s₁ : ℤ) - (s₀ : ℤ) ≡ (r : ℤ) [ZMOD P]) :
    ∃ B ∈ Erdos170.PerfectRulersLengthN ((M + 1) * P),
      B.card ≤ (q + 1) * A.card + 4 * Nat.sqrt P + 10 := by
  obtain ⟨R, hR_mem, hR_card⟩ := exists_grid_ruler P
  have hA_sub : A ⊆ Finset.range (M + 1) := (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
  have hA_perf : Erdos170.PerfectRuler M A := (Finset.mem_filter.mp hA).2
  have hR_sub : R ⊆ Finset.range (P + 1) := (Finset.mem_powerset.mp (Finset.mem_filter.mp hR_mem).1)
  have hR_perf : Erdos170.PerfectRuler P R := (Finset.mem_filter.mp hR_mem).2
  let B : Finset ℕ := (S ×ˢ A).image (fun p => p.1 + p.2 * P) ∪ R ∪ R.image (fun u => M * P + u)
  refine ⟨B, ?_, ?_⟩
  · rw [Erdos170.PerfectRulersLengthN, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_range]
      simp only [B, Finset.mem_union, Finset.mem_image, Finset.mem_product] at hx
      rcases hx with (⟨⟨s, a⟩, ⟨hs, ha⟩, rfl⟩ | hxR) | ⟨u, hu, rfl⟩
      · have hs' : s < P := Finset.mem_range.mp (hS_sub hs)
        have ha' : a ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hA_sub ha))
        have hmul : a * P ≤ M * P := Nat.mul_le_mul_right P ha'
        have hsum : (M + 1) * P = M * P + P := by ring
        dsimp only
        omega
      · have hx' : x ≤ P := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hR_sub hxR))
        have hle : P ≤ (M + 1) * P := Nat.le_mul_of_pos_left P (by omega)
        omega
      · have hu' : u ≤ P := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hR_sub hu))
        have hsum : (M + 1) * P = M * P + P := by ring
        omega
    · intro d hd
      rw [Finset.mem_range] at hd
      by_cases hd_lt : d < M * P
      · let m := d / P
        let r := d % P
        have hr_lt : r < P := Nat.mod_lt d hP
        have hdiv : m * P + r = d := by rw [Nat.mul_comm]; exact Nat.div_add_mod d P
        have hm_lt : m < M := by
          by_contra hge
          have h1 : M * P ≤ m * P := Nat.mul_le_mul_right P (Nat.not_lt.mp hge)
          omega
        obtain ⟨s₁, hs₁, s₀, hs₀, hmod⟩ := hS_diff r (Finset.mem_range.mpr hr_lt)
        have hs₁_lt : s₁ < P := Finset.mem_range.mp (hS_sub hs₁)
        have hs₀_lt : s₀ < P := Finset.mem_range.mp (hS_sub hs₀)
        obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hmod
        have ht_cases : t = 0 ∨ t = 1 := by
          have ht_bnd : -(P : ℤ) < (P : ℤ) * t ∧ (P : ℤ) * t < 2 * (P : ℤ) := by
            constructor <;> linarith [show (0 : ℤ) ≤ s₁ from Nat.cast_nonneg _,
              show (0 : ℤ) ≤ s₀ from Nat.cast_nonneg _,
              show (0 : ℤ) ≤ r from Nat.cast_nonneg _,
              show (s₁ : ℤ) < P from by exact_mod_cast hs₁_lt,
              show (s₀ : ℤ) < P from by exact_mod_cast hs₀_lt,
              show (r : ℤ) < P from by exact_mod_cast hr_lt]
          have ht_gt : -1 < t := by
            by_contra hle
            have h1 : (P : ℤ) * t ≤ (P : ℤ) * (-1) :=
              Int.mul_le_mul_of_nonneg_left (by omega) (by exact_mod_cast (by omega : 0 ≤ P))
            linarith
          have ht_lt : t < 2 := by
            by_contra hge
            have h1 : (P : ℤ) * 2 ≤ (P : ℤ) * t :=
              Int.mul_le_mul_of_nonneg_left (by omega) (by exact_mod_cast (by omega : 0 ≤ P))
            linarith
          omega
        rcases ht_cases with rfl | rfl
        · have hs_eq : (s₁ : ℤ) - (s₀ : ℤ) = (r : ℤ) := by linarith
          by_cases hm0 : m = 0
          · obtain ⟨a₀, ha₀, _, _, _⟩ := hA_perf 0 (Finset.mem_range.mpr (by omega))
            refine ⟨s₀ + a₀ * P, ?_, s₁ + a₀ * P, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(s₀, a₀), Finset.mem_product.mpr ⟨hs₀, ha₀⟩, rfl⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(s₁, a₀), Finset.mem_product.mpr ⟨hs₁, ha₀⟩, rfl⟩))
            · have hs_nat : s₁ - s₀ = r := by omega
              rw [hm0, zero_mul, zero_add] at hdiv
              omega
          · obtain ⟨a₀, ha₀, a₁, ha₁, ha_diff⟩ := hA_perf m (Finset.mem_range.mpr (by omega))
            have ha_le : a₀ ≤ a₁ := by
              by_contra hlt
              have hsub : a₁ - a₀ = 0 := Nat.sub_eq_zero_of_le (by omega)
              rw [hsub] at ha_diff
              exact hm0 ha_diff
            have ha_eq : a₁ = a₀ + m := by
              have h1 := (Nat.sub_eq_iff_eq_add ha_le).mp ha_diff.symm
              omega
            refine ⟨s₀ + a₀ * P, ?_, s₁ + a₁ * P, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(s₀, a₀), Finset.mem_product.mpr ⟨hs₀, ha₀⟩, rfl⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(s₁, a₁), Finset.mem_product.mpr ⟨hs₁, ha₁⟩, rfl⟩))
            · rw [ha_eq, add_mul]
              omega
        · have hs_eq : (s₁ : ℤ) - (s₀ : ℤ) = (r : ℤ) - (P : ℤ) := by linarith
          obtain ⟨a₀, ha₀, a₁, ha₁, ha_diff⟩ := hA_perf (m + 1) (Finset.mem_range.mpr (by omega))
          have ha_le : a₀ ≤ a₁ := by
            by_contra hlt
            have hsub : a₁ - a₀ = 0 := Nat.sub_eq_zero_of_le (by omega)
            rw [hsub] at ha_diff
            exact Nat.succ_ne_zero m ha_diff
          have ha_eq : a₁ = a₀ + (m + 1) := by
            have h1 := (Nat.sub_eq_iff_eq_add ha_le).mp ha_diff.symm
            omega
          refine ⟨s₀ + a₀ * P, ?_, s₁ + a₁ * P, ?_, ?_⟩
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨(s₀, a₀), Finset.mem_product.mpr ⟨hs₀, ha₀⟩, rfl⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨(s₁, a₁), Finset.mem_product.mpr ⟨hs₁, ha₁⟩, rfl⟩))
          · have hmul : a₁ * P = a₀ * P + m * P + P := by rw [ha_eq]; ring
            have hle_el : s₀ + a₀ * P ≤ s₁ + a₁ * P := by
              have hz : (0 : ℤ) ≤ (d : ℤ) := Nat.cast_nonneg _
              have heq_z : ((s₁ + a₁ * P : ℕ) : ℤ) - ((s₀ + a₀ * P : ℕ) : ℤ) = (d : ℤ) := by
                have hdiv_z : (m : ℤ) * (P : ℤ) + (r : ℤ) = (d : ℤ) := by exact_mod_cast hdiv
                have hmul_z : ((a₁ * P : ℕ) : ℤ) = ((a₀ * P : ℕ) : ℤ) + (m : ℤ) * (P : ℤ) + (P : ℤ) := by
                  exact_mod_cast hmul
                push_cast
                linarith
              omega
            have heq_z : ((s₁ + a₁ * P : ℕ) : ℤ) - ((s₀ + a₀ * P : ℕ) : ℤ) = (d : ℤ) := by
              have hdiv_z : (m : ℤ) * (P : ℤ) + (r : ℤ) = (d : ℤ) := by exact_mod_cast hdiv
              have hmul_z : ((a₁ * P : ℕ) : ℤ) = ((a₀ * P : ℕ) : ℤ) + (m : ℤ) * (P : ℤ) + (P : ℤ) := by
                exact_mod_cast hmul
              push_cast
              linarith
            omega
      · have hd_ge : M * P ≤ d := by omega
        let r := d - M * P
        have hr_le : r ≤ P := by
          have hsum : (M + 1) * P = M * P + P := by ring
          omega
        by_cases hr0 : r = 0
        · obtain ⟨v, hv, _, _, _⟩ := hR_perf 0 (Finset.mem_range.mpr (by omega))
          refine ⟨v, Finset.mem_union_left _ (Finset.mem_union_right _ hv),
            M * P + v, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv), ?_⟩
          omega
        · obtain ⟨v, hv, u, hu, hdiff⟩ := hR_perf r (Finset.mem_range.mpr (by omega))
          have hvu : v ≤ u := by
            by_contra hlt
            have : u - v = 0 := Nat.sub_eq_zero_of_le (by omega)
            omega
          refine ⟨v, Finset.mem_union_left _ (Finset.mem_union_right _ hv),
            M * P + u, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu), ?_⟩
          omega
  · have hu1 := Finset.card_union_le ((S ×ˢ A).image (fun p => p.1 + p.2 * P)) R
    have hu2 := Finset.card_union_le
      ((S ×ˢ A).image (fun p => p.1 + p.2 * P) ∪ R) (R.image (fun u => M * P + u))
    have h1 : ((S ×ˢ A).image (fun p => p.1 + p.2 * P)).card ≤ (q + 1) * A.card := by
      calc ((S ×ˢ A).image (fun p => p.1 + p.2 * P)).card
          ≤ (S ×ˢ A).card := Finset.card_image_le
        _ = S.card * A.card := Finset.card_product S A
        _ = (q + 1) * A.card := by rw [hS_card]
    have h2 : (R.image (fun u => M * P + u)).card ≤ R.card := Finset.card_image_le
    dsimp only [B]
    omega

lemma exists_ruler_extend {N₁ N : ℕ} (hle : N₁ ≤ N)
    (B : Finset ℕ) (hB : B ∈ Erdos170.PerfectRulersLengthN N₁) :
    ∃ C ∈ Erdos170.PerfectRulersLengthN N, C.card ≤ B.card + 4 * Nat.sqrt (N - N₁) + 10 := by
  obtain ⟨R, hR_mem, hR_card⟩ := exists_grid_ruler (N - N₁)
  have hB_sub : B ⊆ Finset.range (N₁ + 1) := (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)
  have hB_perf : Erdos170.PerfectRuler N₁ B := (Finset.mem_filter.mp hB).2
  have hR_sub : R ⊆ Finset.range (N - N₁ + 1) := (Finset.mem_powerset.mp (Finset.mem_filter.mp hR_mem).1)
  have hR_perf : Erdos170.PerfectRuler (N - N₁) R := (Finset.mem_filter.mp hR_mem).2
  let C : Finset ℕ := B ∪ R ∪ R.image (fun u => N₁ + u)
  refine ⟨C, ?_, ?_⟩
  · rw [Erdos170.PerfectRulersLengthN, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_range]
      simp only [C, Finset.mem_union, Finset.mem_image] at hx
      rcases hx with (hxB | hxR) | ⟨u, hu, rfl⟩
      · have := Finset.mem_range.mp (hB_sub hxB); omega
      · have := Finset.mem_range.mp (hR_sub hxR); omega
      · have := Finset.mem_range.mp (hR_sub hu); omega
    · intro d hd
      rw [Finset.mem_range] at hd
      by_cases hd₁ : d ≤ N₁
      · obtain ⟨a₀, ha₀, a₁, ha₁, hdiff⟩ := hB_perf d (Finset.mem_range.mpr (by omega))
        exact ⟨a₀, Finset.mem_union_left _ (Finset.mem_union_left _ ha₀),
          a₁, Finset.mem_union_left _ (Finset.mem_union_left _ ha₁), hdiff⟩
      · have hd_gt : N₁ < d := by omega
        let r := d - N₁
        obtain ⟨v, hv, u, hu, hdiff⟩ := hR_perf r (Finset.mem_range.mpr (by omega))
        have hvu : v ≤ u := by
          by_contra hlt
          have : u - v = 0 := Nat.sub_eq_zero_of_le (by omega)
          omega
        refine ⟨v, Finset.mem_union_left _ (Finset.mem_union_right _ hv),
          N₁ + u, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu), ?_⟩
        omega
  · have hu1 := Finset.card_union_le B R
    have hu2 := Finset.card_union_le (B ∪ R) (R.image (fun u => N₁ + u))
    have himg : (R.image (fun u => N₁ + u)).card ≤ R.card := Finset.card_image_le
    dsimp only [C]
    omega

lemma approx_pow4_pow9 (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1 / 4) (A₀ B₀ : ℕ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ a b : ℕ, A₀ ≤ a ∧ B₀ ≤ b ∧ (1 - 3 * γ) * X ≤ (4 : ℝ) ^ a * (9 : ℝ) ^ b ∧
        (4 : ℝ) ^ a * (9 : ℝ) ^ b ≤ (1 - 2 * γ) * X := by
  let α : ℝ := Real.log 9 / Real.log 4
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog9_pos : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hα_pos : 0 < α := div_pos hlog9_pos hlog4_pos
  have hα_irrat : ∀ (d : ℕ) (c : ℤ), 0 < d → (d : ℝ) * α - (c : ℝ) ≠ 0 := by
    intro d c hd h0
    have hdc : (d : ℝ) * Real.log 9 = (c : ℝ) * Real.log 4 := by
      have h1 : (d : ℝ) * (Real.log 9 / Real.log 4) = (c : ℝ) := sub_eq_zero.mp h0
      rw [← h1]
      field_simp [hlog4_pos.ne']
    have hc_pos : (0 : ℤ) < c := by
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
      have hcr : (0 : ℝ) < (c : ℝ) := by
        have : 0 < (c : ℝ) * Real.log 4 := hdc ▸ mul_pos hd_pos hlog9_pos
        exact pos_of_mul_pos_left this hlog4_pos.le
      exact_mod_cast hcr
    let c₀ : ℕ := c.toNat
    have hc₀_pos : 0 < c₀ := by omega
    have hc_eq : (c : ℝ) = (c₀ : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hc_pos.le).symm
    rw [hc_eq] at hdc
    have hlog_eq : Real.log ((9 : ℝ) ^ d) = Real.log ((4 : ℝ) ^ c₀) := by
      rw [Real.log_pow, Real.log_pow]; exact hdc
    have hpow_eq : (9 : ℝ) ^ d = (4 : ℝ) ^ c₀ :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog_eq
    have hnat_eq : 9 ^ d = 4 ^ c₀ := by exact_mod_cast hpow_eq
    have hmod1 : (9 ^ d) % 2 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have hmod0 : (4 ^ c₀) % 2 = 0 := by
      have hc1 : ∃ k, c₀ = k + 1 := ⟨c₀ - 1, by omega⟩
      obtain ⟨k, hk⟩ := hc1
      rw [hk, pow_succ, Nat.mul_mod]; norm_num
    omega
  have hratio_gt : 1 < (1 - 2 * γ) / (1 - 3 * γ) := by
    rw [one_lt_div (by linarith)]
    linarith
  have hθ_pos : 0 < Real.log ((1 - 2 * γ) / (1 - 3 * γ)) / Real.log 4 :=
    div_pos (Real.log_pos hratio_gt) hlog4_pos
  obtain ⟨K₀, hK₀⟩ := exists_nat_one_div_lt hθ_pos
  let K : ℕ := K₀ + 2
  have hK_ge2 : 2 ≤ K := by omega
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  have hK_lt : 1 / (K : ℝ) < Real.log ((1 - 2 * γ) / (1 - 3 * γ)) / Real.log 4 := by
    have hle : (1 : ℝ) / (K : ℝ) ≤ 1 / ((K₀ : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (by omega : K₀ + 1 ≤ K)
    exact hle.trans_lt hK₀
  let f : Fin (K + 1) → Fin K := fun k =>
    ⟨Nat.floor ((K : ℝ) * Int.fract (((k : ℕ) : ℝ) * α)), by
      rw [Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _))]
      have hlt : Int.fract (((k : ℕ) : ℝ) * α) < 1 := Int.fract_lt_one _
      nlinarith⟩
  have hcard_lt : Fintype.card (Fin K) < Fintype.card (Fin (K + 1)) := by simp
  obtain ⟨i₁, i₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard_lt
  have hne_nat : i₁.1 ≠ i₂.1 := fun h => hne (Fin.ext h)
  obtain ⟨k₁, k₂, hk_lt, hk₂_le, hk_eq⟩ : ∃ k₁ k₂ : ℕ, k₁ < k₂ ∧ k₂ ≤ K ∧
      Nat.floor ((K : ℝ) * Int.fract ((k₁ : ℝ) * α)) =
      Nat.floor ((K : ℝ) * Int.fract ((k₂ : ℝ) * α)) := by
    rcases lt_or_gt_of_ne hne_nat with hlt | hlt
    · exact ⟨i₁.1, i₂.1, hlt, by omega, congrArg Fin.val heq⟩
    · exact ⟨i₂.1, i₁.1, hlt, by omega, (congrArg Fin.val heq).symm⟩
  let d : ℕ := k₂ - k₁
  have hd_pos : 0 < d := by omega
  let c : ℤ := ⌊(k₂ : ℝ) * α⌋ - ⌊(k₁ : ℝ) * α⌋
  have hdc_eq : (d : ℝ) * α - (c : ℝ) = Int.fract ((k₂ : ℝ) * α) - Int.fract ((k₁ : ℝ) * α) := by
    have hd_cast : (d : ℝ) = (k₂ : ℝ) - (k₁ : ℝ) := by exact_mod_cast (Nat.cast_sub hk_lt.le)
    rw [hd_cast]
    push_cast [c]
    rw [← Int.self_sub_floor ((k₂ : ℝ) * α), ← Int.self_sub_floor ((k₁ : ℝ) * α)]
    ring
  have hdc_abs : |(d : ℝ) * α - (c : ℝ)| < 1 / (K : ℝ) := by
    rw [hdc_eq]
    let m : ℕ := Nat.floor ((K : ℝ) * Int.fract ((k₁ : ℝ) * α))
    have hm1_lo : (m : ℝ) ≤ (K : ℝ) * Int.fract ((k₁ : ℝ) * α) :=
      Nat.floor_le (mul_nonneg hK_pos.le (Int.fract_nonneg _))
    have hm1_hi : (K : ℝ) * Int.fract ((k₁ : ℝ) * α) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hm2_lo : (m : ℝ) ≤ (K : ℝ) * Int.fract ((k₂ : ℝ) * α) := by
      dsimp only [m]
      rw [hk_eq]
      exact Nat.floor_le (mul_nonneg hK_pos.le (Int.fract_nonneg _))
    have hm2_hi : (K : ℝ) * Int.fract ((k₂ : ℝ) * α) < (m : ℝ) + 1 := by
      dsimp only [m]
      rw [hk_eq]
      exact Nat.lt_floor_add_one _
    have hmul_lo : -1 < (K : ℝ) * (Int.fract ((k₂ : ℝ) * α) - Int.fract ((k₁ : ℝ) * α)) := by nlinarith
    have hmul_hi : (K : ℝ) * (Int.fract ((k₂ : ℝ) * α) - Int.fract ((k₁ : ℝ) * α)) < 1 := by nlinarith
    rw [abs_lt]
    constructor
    · rw [← neg_div]
      exact (div_lt_iff₀' hK_pos).mpr hmul_lo
    · exact (lt_div_iff₀' hK_pos).mpr hmul_hi
  obtain ⟨Δa, Δb, hη_pos, hη_lt⟩ : ∃ Δa Δb : ℤ,
      0 < (Δa : ℝ) + (Δb : ℝ) * α ∧ (Δa : ℝ) + (Δb : ℝ) * α < 1 / (K : ℝ) := by
    have hne0 := hα_irrat d c hd_pos
    rw [abs_lt] at hdc_abs
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · exact ⟨c, -(d : ℤ), by push_cast; linarith, by push_cast; linarith⟩
    · exact ⟨-c, (d : ℤ), by push_cast; linarith, by push_cast; linarith⟩
  let η : ℝ := (Δa : ℝ) + (Δb : ℝ) * α
  let T : ℕ := Nat.ceil (2 / η)
  have hT_pos : 0 < T := Nat.ceil_pos.mpr (by positivity)
  have hT_mul : 2 ≤ (T : ℝ) * η := by
    have := Nat.le_ceil (2 / η)
    exact (div_le_iff₀ hη_pos).mp this
  let b_base : ℕ := B₀ + T * Δb.natAbs
  let X₀ : ℝ := (1 - 2 * γ)⁻¹ *
    Real.exp (((A₀ : ℝ) + (b_base : ℝ) * α + (T : ℝ) * (Δa.natAbs : ℝ) + 2) * Real.log 4)
  have h12_pos : 0 < 1 - 2 * γ := by linarith
  have hX₀_pos : 0 < X₀ := mul_pos (inv_pos.mpr h12_pos) (Real.exp_pos _)
  refine ⟨X₀, hX₀_pos, fun X hX => ?_⟩
  let y : ℝ := Real.log ((1 - 2 * γ) * X) / Real.log 4
  have hX_pos : 0 < X := lt_of_lt_of_le hX₀_pos hX
  have hy_lb : (A₀ : ℝ) + (b_base : ℝ) * α + (T : ℝ) * (Δa.natAbs : ℝ) + 2 ≤ y := by
    have hle_exp :
        Real.exp (((A₀ : ℝ) + (b_base : ℝ) * α + (T : ℝ) * (Δa.natAbs : ℝ) + 2) * Real.log 4) ≤
          (1 - 2 * γ) * X := by
      have h1 : (1 - 2 * γ) * X₀ ≤ (1 - 2 * γ) * X := mul_le_mul_of_nonneg_left hX h12_pos.le
      have h2 : (1 - 2 * γ) * X₀ =
          Real.exp (((A₀ : ℝ) + (b_base : ℝ) * α + (T : ℝ) * (Δa.natAbs : ℝ) + 2) * Real.log 4) := by
        dsimp only [X₀]
        rw [← mul_assoc, mul_inv_cancel₀ h12_pos.ne', one_mul]
      linarith
    have hle_log := Real.log_le_log (Real.exp_pos _) hle_exp
    rw [Real.log_exp] at hle_log
    exact (le_div_iff₀ hlog4_pos).mpr hle_log
  let a_base : ℤ := Int.floor (y - (b_base : ℝ) * α)
  have ha_base_lo : y - (b_base : ℝ) * α - 1 < (a_base : ℝ) := Int.sub_one_lt_floor _
  have ha_base_hi : (a_base : ℝ) ≤ y - (b_base : ℝ) * α := Int.floor_le _
  let s : ℕ → ℝ := fun j => (a_base : ℝ) + (b_base : ℝ) * α + (j : ℝ) * η
  have hs0_le : s 0 ≤ y := by dsimp only [s]; simp; linarith
  have hs0_gt : y - 1 < s 0 := by dsimp only [s]; simp; linarith
  have hsT_gt : y < s T := by
    dsimp only [s]
    linarith
  let S_j : Finset ℕ := (Finset.range (T + 1)).filter (fun j => s j ≤ y)
  have hS_ne : S_j.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs0_le⟩⟩
  let j := S_j.max' hS_ne
  have hj_mem := Finset.mem_filter.mp (Finset.max'_mem S_j hS_ne)
  have hj_le_T : j ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj_mem.1)
  have hj_s_le : s j ≤ y := hj_mem.2
  have hj_ne_T : j ≠ T := by
    intro h_eq
    rw [h_eq] at hj_s_le
    linarith
  have hj1_not : j + 1 ∉ S_j := fun hm => absurd (Finset.le_max' S_j (j + 1) hm) (by omega)
  have hj1_gt : y < s (j + 1) := by
    by_contra hle
    push Not at hle
    exact hj1_not (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hle⟩)
  have hsj1_eq : s (j + 1) = s j + η := by
    dsimp only [s]
    push_cast
    ring
  have hsj_gt : y - 1 / (K : ℝ) < s j := by linarith
  let a_int : ℤ := a_base + (j : ℤ) * Δa
  let b_int : ℤ := (b_base : ℤ) + (j : ℤ) * Δb
  have ha_ge : (A₀ : ℤ) ≤ a_int := by
    have h_abs : -(Δa.natAbs : ℤ) ≤ Δa := by omega
    have hj_nn : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have hmul : -(j : ℤ) * (Δa.natAbs : ℤ) ≤ (j : ℤ) * Δa := by
      have := Int.mul_le_mul_of_nonneg_left h_abs hj_nn
      linarith
    have hT_mul_z : (j : ℤ) * (Δa.natAbs : ℤ) ≤ (T : ℤ) * (Δa.natAbs : ℤ) :=
      Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hj_le_T) (Int.natCast_nonneg _)
    have ha_base_z : (A₀ : ℤ) + (T : ℤ) * (Δa.natAbs : ℤ) ≤ a_base := by
      have h_real : ((A₀ : ℤ) + (T : ℤ) * (Δa.natAbs : ℤ) : ℝ) < (a_base : ℝ) := by
        simp only [Int.cast_natCast]
        linarith
      exact_mod_cast h_real.le
    dsimp only [a_int]
    linarith
  have hb_ge : (B₀ : ℤ) ≤ b_int := by
    have h_abs : -(Δb.natAbs : ℤ) ≤ Δb := by omega
    have hj_nn : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have hmul : -(j : ℤ) * (Δb.natAbs : ℤ) ≤ (j : ℤ) * Δb := by
      have := Int.mul_le_mul_of_nonneg_left h_abs hj_nn
      linarith
    have hT_mul_z : (j : ℤ) * (Δb.natAbs : ℤ) ≤ (T : ℤ) * (Δb.natAbs : ℤ) :=
      Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hj_le_T) (Int.natCast_nonneg _)
    have hb_base_z : (b_base : ℤ) = (B₀ : ℤ) + (T : ℤ) * (Δb.natAbs : ℤ) := by
      dsimp only [b_base]; push_cast; rfl
    dsimp only [b_int]
    linarith
  let a := a_int.toNat
  let b := b_int.toNat
  have ha_nat : A₀ ≤ a := by omega
  have hb_nat : B₀ ≤ b := by omega
  have ha_cast : (a : ℝ) = (a_int : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ a_int)
  have hb_cast : (b : ℝ) = (b_int : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ b_int)
  have hs_exp : (a : ℝ) + (b : ℝ) * α = s j := by
    rw [ha_cast, hb_cast]
    dsimp only [a_int, b_int, s, η]
    push_cast
    ring
  have hpow_exp : (4 : ℝ) ^ a * (9 : ℝ) ^ b = Real.exp (s j * Real.log 4) := by
    have h4 : (4 : ℝ) ^ a = Real.exp ((a : ℝ) * Real.log 4) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h9 : (9 : ℝ) ^ b = Real.exp ((b : ℝ) * Real.log 9) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [h4, h9, ← Real.exp_add]
    congr 1
    have hlog9 : Real.log 9 = α * Real.log 4 := by
      dsimp only [α]
      field_simp [hlog4_pos.ne']
    rw [hlog9, ← hs_exp]
    ring
  refine ⟨a, b, ha_nat, hb_nat, ?_, ?_⟩
  · have h_exp_lo : Real.exp ((y - 1 / (K : ℝ)) * Real.log 4) ≤ Real.exp (s j * Real.log 4) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hsj_gt.le hlog4_pos.le
    have h_exp_K : (1 - 3 * γ) / (1 - 2 * γ) ≤ Real.exp (-Real.log 4 / (K : ℝ)) := by
      have h1 : Real.log ((1 - 3 * γ) / (1 - 2 * γ)) ≤ -Real.log 4 / (K : ℝ) := by
        rw [Real.log_div (by linarith) (by linarith)]
        have h2 : Real.log ((1 - 2 * γ) / (1 - 3 * γ)) = Real.log (1 - 2 * γ) - Real.log (1 - 3 * γ) :=
          Real.log_div (by linarith) (by linarith)
        have h3 : Real.log 4 / (K : ℝ) < Real.log ((1 - 2 * γ) / (1 - 3 * γ)) := by
          calc Real.log 4 / (K : ℝ) = (1 / (K : ℝ)) * Real.log 4 := by ring
            _ < Real.log ((1 - 2 * γ) / (1 - 3 * γ)) := (lt_div_iff₀ hlog4_pos).mp hK_lt
        rw [neg_div]
        linarith
      calc (1 - 3 * γ) / (1 - 2 * γ)
          = Real.exp (Real.log ((1 - 3 * γ) / (1 - 2 * γ))) :=
            (Real.exp_log (div_pos (by linarith) (by linarith))).symm
        _ ≤ Real.exp (-Real.log 4 / (K : ℝ)) := Real.exp_le_exp.mpr h1
    have hy_exp : Real.exp (y * Real.log 4) = (1 - 2 * γ) * X := by
      have : y * Real.log 4 = Real.log ((1 - 2 * γ) * X) := by
        dsimp only [y]
        field_simp [hlog4_pos.ne']
      rw [this, Real.exp_log (mul_pos h12_pos hX_pos)]
    have h_split : Real.exp ((y - 1 / (K : ℝ)) * Real.log 4) =
        Real.exp (y * Real.log 4) * Real.exp (-Real.log 4 / (K : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hpow_exp]
    calc (1 - 3 * γ) * X = X * (1 - 3 * γ) := mul_comm _ _
      _ = X * ((1 - 2 * γ) * ((1 - 3 * γ) / (1 - 2 * γ))) := by
          rw [mul_div_cancel₀ _ h12_pos.ne']
      _ = ((1 - 2 * γ) * X) * ((1 - 3 * γ) / (1 - 2 * γ)) := by ring
      _ ≤ ((1 - 2 * γ) * X) * Real.exp (-Real.log 4 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left h_exp_K (mul_pos h12_pos hX_pos).le
      _ = Real.exp ((y - 1 / (K : ℝ)) * Real.log 4) := by rw [h_split, hy_exp]
      _ ≤ Real.exp (s j * Real.log 4) := h_exp_lo
  · rw [hpow_exp]
    have h1 : s j * Real.log 4 ≤ Real.log ((1 - 2 * γ) * X) := by
      have : y * Real.log 4 = Real.log ((1 - 2 * γ) * X) := by
        dsimp only [y]
        field_simp [hlog4_pos.ne']
      rw [← this]
      exact mul_le_mul_of_nonneg_right hj_s_le hlog4_pos.le
    calc Real.exp (s j * Real.log 4) ≤ Real.exp (Real.log ((1 - 2 * γ) * X)) := Real.exp_le_exp.mpr h1
      _ = (1 - 2 * γ) * X := Real.exp_log (mul_pos h12_pos hX_pos)

lemma quad_eps_le (q γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 100) (hq : 100 / γ ≤ q) :
    q ^ 2 + q + 1 ≤ (1 + γ / 4) * q ^ 2 := by
  have h1 : 100 ≤ q * γ := (div_le_iff₀ hγ).mp hq
  have hq_ge : (10000 : ℝ) ≤ q := by nlinarith
  have h2 : 100 * q ≤ q * γ * q := mul_le_mul_of_nonneg_right h1 (by positivity)
  nlinarith

lemma q_add_one_le_mul_sqrt (q δ γ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hγδ : γ ≤ δ ^ 2 / 100) (hδ1 : δ ≤ 1 / 100) (hq : 100 / γ ≤ q) :
    q + 1 ≤ (1 + δ) * √(q ^ 2 + q + 1) := by
  have h1 : 100 ≤ q * γ := (div_le_iff₀ hγ).mp hq
  have h2 : 1 ≤ δ * q := by nlinarith
  have h3 : (1 : ℝ) ≤ q := by nlinarith
  have hsq : (q + 1) ^ 2 ≤ (1 + δ) ^ 2 * (q ^ 2 + q + 1) := by nlinarith
  calc q + 1 = √((q + 1) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √((1 + δ) ^ 2 * (q ^ 2 + q + 1)) := Real.sqrt_le_sqrt hsq
    _ = (1 + δ) * √(q ^ 2 + q + 1) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

lemma poly3_le_one (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 100) :
    (1 + γ / 4) ^ 3 * (1 - 2 * γ) ≤ 1 := by
  have hcube : (1 + γ / 4) ^ 3 = 1 + 3 / 4 * γ + 3 / 16 * γ ^ 2 + 1 / 64 * γ ^ 3 := by ring
  have h1 : (1 + γ / 4) ^ 3 ≤ 1 + γ := by
    rw [hcube]
    have hg2 : γ ^ 2 ≤ γ / 100 := by nlinarith
    have hg3 : γ ^ 3 ≤ γ / 10000 := by nlinarith
    linarith
  have h2 : (1 + γ) * (1 - 2 * γ) ≤ 1 := by nlinarith
  have h3 : 0 ≤ 1 - 2 * γ := by linarith
  calc (1 + γ / 4) ^ 3 * (1 - 2 * γ) ≤ (1 + γ) * (1 - 2 * γ) := mul_le_mul_of_nonneg_right h1 h3
    _ ≤ 1 := h2

lemma poly_delta_L_le (δ L : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100) (hL : 0 ≤ L) :
    (1 + δ) ^ 2 * (L + δ) ≤ L + 10 * δ * (L + 10) := by
  have hexp : (1 + δ) ^ 2 * (L + δ) = L + (2 * δ + δ ^ 2) * L + (1 + δ) ^ 2 * δ := by ring
  rw [hexp]
  have hd_le : 2 * δ + δ ^ 2 ≤ 10 * δ := by nlinarith
  have h1 : (2 * δ + δ ^ 2) * L ≤ (10 * δ) * L := mul_le_mul_of_nonneg_right hd_le hL
  have h2 : (1 + δ) ^ 2 * δ ≤ 100 * δ := by nlinarith
  linarith

lemma erdos_gal_upper_bound (L : ℝ) (hL_nonneg : 0 ≤ L) (ε : ℝ) (hε : 0 < ε)
    (h_sub : ∀ (K : ℕ) (δ : ℝ), 0 < δ → ∃ M ≥ K, (Erdos170.F M : ℝ) / √(M : ℝ) < L + δ) :
    ∀ᶠ N : ℕ in Filter.atTop, (Erdos170.F N : ℝ) / √(N : ℝ) ≤ L + ε := by
  let δ : ℝ := min (ε / (100 * (L + 10))) (1 / 100)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ_le1 : δ ≤ 1 / 100 := min_le_right _ _
  have hδ_le2 : δ ≤ ε / (100 * (L + 10)) := min_le_left _ _
  have hδL_raw : δ * (100 * (L + 10)) ≤ ε := (le_div_iff₀ (by positivity)).mp hδ_le2
  have hδL : δ * (L + 10) ≤ ε / 100 := by linarith
  let γ : ℝ := min (δ ^ 2 / 100) (1 / 100)
  have hγ_pos : 0 < γ := lt_min (by positivity) (by norm_num)
  have hγ_le1 : γ ≤ δ ^ 2 / 100 := min_le_left _ _
  have hγ_le2 : γ ≤ 1 / 100 := min_le_right _ _
  have hγ_lt : γ < 1 / 4 := by linarith
  have h4sqrt_γ : 4 * √(3 * γ) ≤ δ := by
    have hsq : 3 * γ ≤ (δ / 4) ^ 2 := by nlinarith
    have h1 : √(3 * γ) ≤ δ / 4 := by
      calc √(3 * γ) ≤ √((δ / 4) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = δ / 4 := Real.sqrt_sq (by linarith)
    linarith
  let M_min : ℕ := Nat.ceil ((30 / δ) ^ 2) + 1
  obtain ⟨M, hM_ge, hFM_lt⟩ := h_sub M_min δ hδ_pos
  have hM_pos : 1 ≤ M := by omega
  have hM_sqrt : 30 / δ ≤ √(M : ℝ) := by
    have h1 : (30 / δ) ^ 2 ≤ (M : ℝ) := by
      have := Nat.le_ceil ((30 / δ) ^ 2)
      have h2 : (M_min : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge
      have h3 : (Nat.ceil ((30 / δ) ^ 2) : ℝ) ≤ (M_min : ℝ) := by exact_mod_cast (by omega : Nat.ceil ((30 / δ) ^ 2) ≤ M_min)
      linarith
    calc 30 / δ = √((30 / δ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(M : ℝ) := Real.sqrt_le_sqrt h1
  have hM_inv : 30 / √(M : ℝ) ≤ δ := by
    have hsqrt_pos : 0 < √(M : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < M))
    rw [div_le_iff₀ hsqrt_pos]
    have := (div_le_iff₀ hδ_pos).mp hM_sqrt
    linarith
  have hF_mem : Erdos170.F M ∈ Finset.image Finset.card (Erdos170.PerfectRulersLengthN M) :=
    Finset.min'_mem _ _
  rw [Finset.mem_image] at hF_mem
  obtain ⟨A, hA_mem, hA_card⟩ := hF_mem
  let K_ab : ℕ := Nat.ceil (100 / γ) + 1
  have hK_ab_ge : 1 ≤ K_ab := by omega
  have hpow2_ge : ∀ a : ℕ, K_ab ≤ a → (100 : ℝ) / γ ≤ (2 ^ a : ℕ) := by
    intro a ha
    have h1 : (100 : ℝ) / γ ≤ (K_ab : ℝ) := by
      have := Nat.le_ceil (100 / γ)
      have h2 : (Nat.ceil (100 / γ) : ℝ) ≤ (K_ab : ℝ) := by exact_mod_cast (by omega : Nat.ceil (100 / γ) ≤ K_ab)
      linarith
    have h2 : K_ab ≤ 2 ^ a := ha.trans (Nat.lt_pow_self (by norm_num : 1 < 2)).le
    exact h1.trans (by exact_mod_cast h2)
  have hpow3_ge : ∀ b : ℕ, K_ab ≤ b → (100 : ℝ) / γ ≤ (3 ^ b : ℕ) := by
    intro b hb
    have h1 := hpow2_ge b hb
    have h2 : 2 ^ b ≤ 3 ^ b := Nat.pow_le_pow_left (by norm_num) b
    exact h1.trans (by exact_mod_cast h2)
  obtain ⟨X₀, hX₀_pos, h_approx⟩ := approx_pow4_pow9 γ hγ_pos hγ_lt K_ab K_ab
  let N₀ : ℕ := Nat.ceil (max (X₀ * ((M : ℝ) + 1)) ((100 / δ) ^ 2)) + 1
  refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
  have hN_pos : 1 ≤ N := by omega
  have hN_ge_X : X₀ * ((M : ℝ) + 1) ≤ (N : ℝ) := by
    have := Nat.le_ceil (max (X₀ * ((M : ℝ) + 1)) ((100 / δ) ^ 2))
    have h1 : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : (Nat.ceil (max (X₀ * ((M : ℝ) + 1)) ((100 / δ) ^ 2)) : ℝ) ≤ N₀ := by
      exact_mod_cast (by omega : Nat.ceil (max (X₀ * ((M : ℝ) + 1)) ((100 / δ) ^ 2)) ≤ N₀)
    exact (le_max_left _ _).trans (this.trans (h2.trans h1))
  have hN_sqrt : 100 / δ ≤ √(N : ℝ) := by
    have h1 : (100 / δ) ^ 2 ≤ (N : ℝ) := by
      have := Nat.le_ceil (max (X₀ * ((M : ℝ) + 1)) ((100 / δ) ^ 2))
      have h2 : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have h3 : (Nat.ceil (max (X₀ * ((M : ℝ) + 1)) ((100 / δ) ^ 2)) : ℝ) ≤ N₀ := by
        exact_mod_cast (by omega : Nat.ceil (max (X₀ * ((M : ℝ) + 1)) ((100 / δ) ^ 2)) ≤ N₀)
      exact (le_max_right _ _).trans (this.trans (h3.trans h2))
    calc 100 / δ = √((100 / δ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(N : ℝ) := Real.sqrt_le_sqrt h1
  have hN_inv : 100 / √(N : ℝ) ≤ δ := by
    have hsqrt_pos : 0 < √(N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
    rw [div_le_iff₀ hsqrt_pos]
    have := (div_le_iff₀ hδ_pos).mp hN_sqrt
    linarith
  let X : ℝ := (N : ℝ) / ((M : ℝ) + 1)
  have hX_ge : X₀ ≤ X := (le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)).mpr hN_ge_X
  obtain ⟨a, b, ha_ge, hb_ge, hpow_lo, hpow_hi⟩ := h_approx X hX_ge
  have ha_1 : 1 ≤ a := by omega
  have hb_1 : 1 ≤ b := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₁, hS₁_sub, _, hS₁_card, hS₁_diff⟩ := singer_difference_set 2 a ha_1
  obtain ⟨S₂, hS₂_sub, _, hS₂_card, hS₂_diff⟩ := singer_difference_set 3 b hb_1
  let P₁ : ℕ := 2 ^ (2 * a) + 2 ^ a + 1
  let P₂ : ℕ := 3 ^ (2 * b) + 3 ^ b + 1
  have hP₁_pos : 1 ≤ P₁ := Nat.le_add_left 1 _
  have hP₂_pos : 1 ≤ P₂ := Nat.le_add_left 1 _
  obtain ⟨B₁, hB₁_mem, hB₁_card⟩ :=
    exists_ruler_mul_singer hM_pos hP₁_pos A hA_mem S₁ hS₁_sub hS₁_card hS₁_diff
  obtain ⟨B₂, hB₂_mem, hB₂_card⟩ :=
    exists_ruler_mul_singer (Nat.mul_pos (Nat.succ_pos M) hP₁_pos)
      hP₂_pos B₁ hB₁_mem S₂ hS₂_sub hS₂_card hS₂_diff
  let N₁ : ℕ := ((M + 1) * P₁ + 1) * P₂
  have h2a_ge := hpow2_ge a ha_ge
  have h3b_ge := hpow3_ge b hb_ge
  have hP₁_eq : (P₁ : ℝ) = ((2 ^ a : ℕ) : ℝ) ^ 2 + ((2 ^ a : ℕ) : ℝ) + 1 := by
    dsimp only [P₁]
    push_cast
    rw [show 2 * a = a * 2 from mul_comm 2 a, pow_mul]
  have hP₂_eq : (P₂ : ℝ) = ((3 ^ b : ℕ) : ℝ) ^ 2 + ((3 ^ b : ℕ) : ℝ) + 1 := by
    dsimp only [P₂]
    push_cast
    rw [show 2 * b = b * 2 from mul_comm 2 b, pow_mul]
  have h4a_eq : (4 : ℝ) ^ a = ((2 ^ a : ℕ) : ℝ) ^ 2 := by
    have : (4 : ℕ) ^ a = (2 ^ a) ^ 2 := by rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 a, pow_mul]
    exact_mod_cast this
  have h9b_eq : (9 : ℝ) ^ b = ((3 ^ b : ℕ) : ℝ) ^ 2 := by
    have : (9 : ℕ) ^ b = (3 ^ b) ^ 2 := by rw [show 9 = 3 ^ 2 by norm_num, ← pow_mul, mul_comm 2 b, pow_mul]
    exact_mod_cast this
  have hP₁_le : (P₁ : ℝ) ≤ (1 + γ / 4) * (4 : ℝ) ^ a := by
    rw [hP₁_eq, h4a_eq]
    exact quad_eps_le ((2 ^ a : ℕ) : ℝ) γ hγ_pos hγ_le2 h2a_ge
  have hP₂_le : (P₂ : ℝ) ≤ (1 + γ / 4) * (9 : ℝ) ^ b := by
    rw [hP₂_eq, h9b_eq]
    exact quad_eps_le ((3 ^ b : ℕ) : ℝ) γ hγ_pos hγ_le2 h3b_ge
  have hMP₁_le : ((M : ℝ) + 1) * (P₁ : ℝ) + 1 ≤ (1 + γ / 4) * (((M : ℝ) + 1) * (P₁ : ℝ)) := by
    have hP₁_ge_q : ((2 ^ a : ℕ) : ℝ) ≤ (P₁ : ℝ) := by
      rw [hP₁_eq]
      linarith [sq_nonneg ((2 ^ a : ℕ) : ℝ)]
    have hP₁_ge : 100 / γ ≤ (P₁ : ℝ) := h2a_ge.trans hP₁_ge_q
    have h1 : 1 ≤ (γ / 4) * (P₁ : ℝ) := by
      have := (div_le_iff₀ hγ_pos).mp hP₁_ge
      linarith
    have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ M from Nat.cast_nonneg _]
    have h2 : 1 ≤ (γ / 4) * (((M : ℝ) + 1) * (P₁ : ℝ)) := by
      calc (1 : ℝ) ≤ (γ / 4) * (P₁ : ℝ) := h1
        _ = ((γ / 4) * (P₁ : ℝ)) * 1 := (mul_one _).symm
        _ ≤ ((γ / 4) * (P₁ : ℝ)) * ((M : ℝ) + 1) := mul_le_mul_of_nonneg_left hM1 (by positivity)
        _ = (γ / 4) * (((M : ℝ) + 1) * (P₁ : ℝ)) := by ring
    linarith
  have hN₁_le : N₁ ≤ N := by
    have hN₁_real : (N₁ : ℝ) ≤ (N : ℝ) := by
      have hcast : (N₁ : ℝ) = (((M : ℝ) + 1) * (P₁ : ℝ) + 1) * (P₂ : ℝ) := by
        dsimp only [N₁]; push_cast; ring
      rw [hcast]
      have h1 : (((M : ℝ) + 1) * (P₁ : ℝ) + 1) * (P₂ : ℝ) ≤
          ((1 + γ / 4) * (((M : ℝ) + 1) * (P₁ : ℝ))) * ((1 + γ / 4) * (9 : ℝ) ^ b) :=
        mul_le_mul hMP₁_le hP₂_le (by positivity) (by positivity)
      have h2 : ((1 + γ / 4) * (((M : ℝ) + 1) * (P₁ : ℝ))) * ((1 + γ / 4) * (9 : ℝ) ^ b) ≤
          (1 + γ / 4) ^ 3 * (((M : ℝ) + 1) * ((4 : ℝ) ^ a * (9 : ℝ) ^ b)) := by
        calc ((1 + γ / 4) * (((M : ℝ) + 1) * (P₁ : ℝ))) * ((1 + γ / 4) * (9 : ℝ) ^ b)
            ≤ ((1 + γ / 4) * (((M : ℝ) + 1) * ((1 + γ / 4) * (4 : ℝ) ^ a))) * ((1 + γ / 4) * (9 : ℝ) ^ b) := by
              gcongr
          _ = (1 + γ / 4) ^ 3 * (((M : ℝ) + 1) * ((4 : ℝ) ^ a * (9 : ℝ) ^ b)) := by ring
      have h3 : (1 + γ / 4) ^ 3 * (((M : ℝ) + 1) * ((4 : ℝ) ^ a * (9 : ℝ) ^ b)) ≤
          (1 + γ / 4) ^ 3 * ((1 - 2 * γ) * (N : ℝ)) := by
        have hN_eq : ((M : ℝ) + 1) * X = (N : ℝ) := by
          dsimp only [X]
          field_simp [show (M : ℝ) + 1 ≠ 0 from by positivity]
        have hmul := mul_le_mul_of_nonneg_left hpow_hi (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)
        rw [mul_left_comm ((M : ℝ) + 1) (1 - 2 * γ) X, hN_eq] at hmul
        exact mul_le_mul_of_nonneg_left hmul (by positivity)
      have h4 : (1 + γ / 4) ^ 3 * (1 - 2 * γ) ≤ 1 := poly3_le_one γ hγ_pos.le hγ_le2
      have h5 : (1 + γ / 4) ^ 3 * ((1 - 2 * γ) * (N : ℝ)) ≤ (N : ℝ) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left (Nat.cast_nonneg _) h4
      linarith
    exact_mod_cast hN₁_real
  have hN₁_ge : (1 - 3 * γ) * (N : ℝ) ≤ (N₁ : ℝ) := by
    have h1 : ((M : ℝ) + 1) * ((4 : ℝ) ^ a * (9 : ℝ) ^ b) ≤ (N₁ : ℝ) := by
      have hP₁_ge4 : (4 : ℝ) ^ a ≤ (P₁ : ℝ) := by rw [hP₁_eq, h4a_eq]; linarith [show (0 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) from Nat.cast_nonneg _]
      have hP₂_ge9 : (9 : ℝ) ^ b ≤ (P₂ : ℝ) := by rw [hP₂_eq, h9b_eq]; linarith [show (0 : ℝ) ≤ ((3 ^ b : ℕ) : ℝ) from Nat.cast_nonneg _]
      have hcast : (N₁ : ℝ) = (((M : ℝ) + 1) * (P₁ : ℝ) + 1) * (P₂ : ℝ) := by
        dsimp only [N₁]; push_cast; ring
      rw [hcast]
      calc ((M : ℝ) + 1) * ((4 : ℝ) ^ a * (9 : ℝ) ^ b)
          = (((M : ℝ) + 1) * (4 : ℝ) ^ a) * (9 : ℝ) ^ b := by ring
        _ ≤ (((M : ℝ) + 1) * (P₁ : ℝ) + 1) * (P₂ : ℝ) := by
          gcongr; linarith [mul_le_mul_of_nonneg_left hP₁_ge4 (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)]
    have hN_eq : ((M : ℝ) + 1) * X = (N : ℝ) := by
      dsimp only [X]; field_simp [show (M : ℝ) + 1 ≠ 0 from by positivity]
    have hmul := mul_le_mul_of_nonneg_left hpow_lo (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)
    rw [mul_left_comm ((M : ℝ) + 1) (1 - 3 * γ) X, hN_eq] at hmul
    linarith
  obtain ⟨C, hC_mem, hC_card⟩ := exists_ruler_extend hN₁_le B₂ hB₂_mem
  have hF_le_C : Erdos170.F N ≤ C.card := F_le_card_of_mem hC_mem
  have hq1_bound : ((2 ^ a : ℕ) : ℝ) + 1 ≤ (1 + δ) * √(P₁ : ℝ) := by
    rw [hP₁_eq]
    exact q_add_one_le_mul_sqrt ((2 ^ a : ℕ) : ℝ) δ γ hγ_pos hδ_pos hγ_le1 hδ_le1 h2a_ge
  have hq2_bound : ((3 ^ b : ℕ) : ℝ) + 1 ≤ (1 + δ) * √(P₂ : ℝ) := by
    rw [hP₂_eq]
    exact q_add_one_le_mul_sqrt ((3 ^ b : ℕ) : ℝ) δ γ hγ_pos hδ_pos hγ_le1 hδ_le1 h3b_ge
  have hsqrt_MP1P2 : √(M : ℝ) * √(P₁ : ℝ) * √(P₂ : ℝ) ≤ √(N : ℝ) := by
    have hle : (M : ℝ) * (P₁ : ℝ) * (P₂ : ℝ) ≤ (N : ℝ) := by
      have h1 : M * P₁ * P₂ ≤ N₁ := by
        dsimp only [N₁]
        exact Nat.mul_le_mul_right P₂ (Nat.le_succ_of_le (Nat.mul_le_mul_right P₁ (Nat.le_succ M)))
      exact_mod_cast h1.trans hN₁_le
    calc √(M : ℝ) * √(P₁ : ℝ) * √(P₂ : ℝ)
        = √((M : ℝ) * (P₁ : ℝ) * (P₂ : ℝ)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      _ ≤ √(N : ℝ) := Real.sqrt_le_sqrt hle
  have hsqrt_P1P2 : √(P₁ : ℝ) * √(P₂ : ℝ) ≤ √(N : ℝ) := by
    have h1 : (1 : ℝ) ≤ √(M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hM_pos)
    calc √(P₁ : ℝ) * √(P₂ : ℝ) = 1 * √(P₁ : ℝ) * √(P₂ : ℝ) := by ring
      _ ≤ √(M : ℝ) * √(P₁ : ℝ) * √(P₂ : ℝ) := by gcongr
      _ ≤ √(N : ℝ) := hsqrt_MP1P2
  have hsqrt_P2 : √(P₂ : ℝ) ≤ √(N : ℝ) := by
    have h1 : (1 : ℝ) ≤ √(P₁ : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hP₁_pos)
    calc √(P₂ : ℝ) = 1 * √(P₂ : ℝ) := (one_mul _).symm
      _ ≤ √(P₁ : ℝ) * √(P₂ : ℝ) := by gcongr
      _ ≤ √(N : ℝ) := hsqrt_P1P2
  have hsqrt_diff : √((N - N₁ : ℕ) : ℝ) ≤ √(3 * γ) * √(N : ℝ) := by
    have h1 : ((N - N₁ : ℕ) : ℝ) ≤ 3 * γ * (N : ℝ) := by
      rw [Nat.cast_sub hN₁_le]; linarith
    calc √((N - N₁ : ℕ) : ℝ) ≤ √(3 * γ * (N : ℝ)) := Real.sqrt_le_sqrt h1
      _ = √(3 * γ) * √(N : ℝ) := Real.sqrt_mul (by positivity) _
  have hnat_sqrt : ∀ k : ℕ, (Nat.sqrt k : ℝ) ≤ √(k : ℝ) := fun k => by
    have hsq : ((Nat.sqrt k : ℝ)) ^ 2 ≤ (k : ℝ) := by exact_mod_cast Nat.sqrt_le' k
    calc (Nat.sqrt k : ℝ) = √(((Nat.sqrt k : ℝ)) ^ 2) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ √(k : ℝ) := Real.sqrt_le_sqrt hsq
  have hC_real : (Erdos170.F N : ℝ) ≤
      ((3 ^ b : ℕ) + 1 : ℝ) * (((2 ^ a : ℕ) + 1 : ℝ) * (A.card : ℝ) + 4 * √(P₁ : ℝ) + 10) +
      4 * √(P₂ : ℝ) + 10 + 4 * √((N - N₁ : ℕ) : ℝ) + 10 := by
    have hnat : Erdos170.F N ≤
        (3 ^ b + 1) * ((2 ^ a + 1) * A.card + 4 * Nat.sqrt P₁ + 10) +
        4 * Nat.sqrt P₂ + 10 + 4 * Nat.sqrt (N - N₁) + 10 := by
      have h3 := hC_card
      have h2 := hB₂_card
      have h1 := hB₁_card
      have h0 := hF_le_C
      have : (3 ^ b + 1) * B₁.card ≤ (3 ^ b + 1) * ((2 ^ a + 1) * A.card + 4 * Nat.sqrt P₁ + 10) :=
        Nat.mul_le_mul_left _ h1
      omega
    have hreal : (Erdos170.F N : ℝ) ≤
        ((3 ^ b : ℕ) + 1 : ℝ) * (((2 ^ a : ℕ) + 1 : ℝ) * (A.card : ℝ) + 4 * (Nat.sqrt P₁ : ℝ) + 10) +
        4 * (Nat.sqrt P₂ : ℝ) + 10 + 4 * (Nat.sqrt (N - N₁) : ℝ) + 10 := by
      exact_mod_cast hnat
    have s1 := hnat_sqrt P₁
    have s2 := hnat_sqrt P₂
    have s3 := hnat_sqrt (N - N₁)
    have hmul_s1 : ((3 ^ b : ℕ) + 1 : ℝ) * (((2 ^ a : ℕ) + 1 : ℝ) * (A.card : ℝ) + 4 * (Nat.sqrt P₁ : ℝ) + 10) ≤
        ((3 ^ b : ℕ) + 1 : ℝ) * (((2 ^ a : ℕ) + 1 : ℝ) * (A.card : ℝ) + 4 * √(P₁ : ℝ) + 10) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hsqrt_N_pos : 0 < √(N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
  have hsqrt_M_pos : 0 < √(M : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < M))
  have hA_bound : (A.card : ℝ) ≤ (L + δ) * √(M : ℝ) := by
    rw [hA_card]
    exact (div_lt_iff₀ hsqrt_M_pos).mp hFM_lt |>.le
  have hstep1 : ((2 ^ a : ℕ) + 1 : ℝ) * (A.card : ℝ) + 4 * √(P₁ : ℝ) + 10 ≤
      ((1 + δ) * (L + δ) * √(M : ℝ) + 14) * √(P₁ : ℝ) := by
    have h1P1 : (1 : ℝ) ≤ √(P₁ : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hP₁_pos)
    have hmul := mul_le_mul_of_nonneg_right hq1_bound (Nat.cast_nonneg A.card)
    have hmul2 := mul_le_mul_of_nonneg_left hA_bound (by positivity : 0 ≤ (1 + δ) * √(P₁ : ℝ))
    calc ((2 ^ a : ℕ) + 1 : ℝ) * (A.card : ℝ) + 4 * √(P₁ : ℝ) + 10
        ≤ ((1 + δ) * √(P₁ : ℝ)) * (A.card : ℝ) + 4 * √(P₁ : ℝ) + 10 * √(P₁ : ℝ) := by linarith
      _ ≤ ((1 + δ) * √(P₁ : ℝ)) * ((L + δ) * √(M : ℝ)) + 4 * √(P₁ : ℝ) + 10 * √(P₁ : ℝ) := by linarith
      _ = ((1 + δ) * (L + δ) * √(M : ℝ) + 14) * √(P₁ : ℝ) := by ring
  have hstep2 : ((3 ^ b : ℕ) + 1 : ℝ) * (((2 ^ a : ℕ) + 1 : ℝ) * (A.card : ℝ) + 4 * √(P₁ : ℝ) + 10) ≤
      ((1 + δ) ^ 2 * (L + δ) * √(M : ℝ) + 14 * (1 + δ)) * √(P₁ : ℝ) * √(P₂ : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hstep1 (by positivity : (0 : ℝ) ≤ ((3 ^ b : ℕ) + 1 : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hq2_bound (by positivity : (0 : ℝ) ≤ ((1 + δ) * (L + δ) * √(M : ℝ) + 14) * √(P₁ : ℝ))
    linarith
  have hstep3 : ((1 + δ) ^ 2 * (L + δ) * √(M : ℝ) + 14 * (1 + δ)) * √(P₁ : ℝ) * √(P₂ : ℝ) ≤
      ((1 + δ) ^ 2 * (L + δ) + 15 / √(M : ℝ)) * √(N : ℝ) := by
    have h_split : ((1 + δ) ^ 2 * (L + δ) * √(M : ℝ) + 14 * (1 + δ)) * √(P₁ : ℝ) * √(P₂ : ℝ) =
        (1 + δ) ^ 2 * (L + δ) * (√(M : ℝ) * √(P₁ : ℝ) * √(P₂ : ℝ)) + 14 * (1 + δ) * (√(P₁ : ℝ) * √(P₂ : ℝ)) := by ring
    rw [h_split]
    have h1 : (1 + δ) ^ 2 * (L + δ) * (√(M : ℝ) * √(P₁ : ℝ) * √(P₂ : ℝ)) ≤
        (1 + δ) ^ 2 * (L + δ) * √(N : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt_MP1P2 (by positivity)
    have h2 : 14 * (1 + δ) * (√(P₁ : ℝ) * √(P₂ : ℝ)) ≤ 15 * (√(N : ℝ) / √(M : ℝ)) := by
      have hP12_le : √(P₁ : ℝ) * √(P₂ : ℝ) ≤ √(N : ℝ) / √(M : ℝ) := by
        rw [le_div_iff₀ hsqrt_M_pos]
        linarith [hsqrt_MP1P2]
      have h14 : 14 * (1 + δ) ≤ 15 := by linarith
      calc 14 * (1 + δ) * (√(P₁ : ℝ) * √(P₂ : ℝ))
          ≤ 15 * (√(P₁ : ℝ) * √(P₂ : ℝ)) := mul_le_mul_of_nonneg_right h14 (by positivity)
        _ ≤ 15 * (√(N : ℝ) / √(M : ℝ)) := mul_le_mul_of_nonneg_left hP12_le (by norm_num)
    have heq : ((1 + δ) ^ 2 * (L + δ) + 15 / √(M : ℝ)) * √(N : ℝ) =
        (1 + δ) ^ 2 * (L + δ) * √(N : ℝ) + 15 * (√(N : ℝ) / √(M : ℝ)) := by ring
    linarith
  have hstep4 : (Erdos170.F N : ℝ) ≤
      ((1 + δ) ^ 2 * (L + δ) + 15 / √(M : ℝ) + 4 / √(M : ℝ) + 20 / √(N : ℝ) + 4 * √(3 * γ)) * √(N : ℝ) := by
    have h4P2 : 4 * √(P₂ : ℝ) ≤ 4 / √(M : ℝ) * √(N : ℝ) := by
      have hP2_le : √(P₂ : ℝ) ≤ √(N : ℝ) / √(M : ℝ) := by
        have h1P1 : (1 : ℝ) ≤ √(P₁ : ℝ) := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hP₁_pos)
        rw [le_div_iff₀ hsqrt_M_pos]
        calc √(P₂ : ℝ) * √(M : ℝ) = √(M : ℝ) * 1 * √(P₂ : ℝ) := by ring
          _ ≤ √(M : ℝ) * √(P₁ : ℝ) * √(P₂ : ℝ) := by gcongr
          _ ≤ √(N : ℝ) := hsqrt_MP1P2
      calc 4 * √(P₂ : ℝ) ≤ 4 * (√(N : ℝ) / √(M : ℝ)) := by linarith
        _ = 4 / √(M : ℝ) * √(N : ℝ) := by ring
    have heq_rhs : ((1 + δ) ^ 2 * (L + δ) + 15 / √(M : ℝ) + 4 / √(M : ℝ) + 20 / √(N : ℝ) + 4 * √(3 * γ)) * √(N : ℝ) =
        ((1 + δ) ^ 2 * (L + δ) + 15 / √(M : ℝ)) * √(N : ℝ) + 4 / √(M : ℝ) * √(N : ℝ) + 20 + 4 * (√(3 * γ) * √(N : ℝ)) := by
      field_simp [hsqrt_N_pos.ne']
    linarith
  have h_final_coef :
      (1 + δ) ^ 2 * (L + δ) + 15 / √(M : ℝ) + 4 / √(M : ℝ) + 20 / √(N : ℝ) + 4 * √(3 * γ) ≤ L + ε := by
    have hM19 : 15 / √(M : ℝ) + 4 / √(M : ℝ) ≤ δ := by
      have : 15 / √(M : ℝ) + 4 / √(M : ℝ) ≤ 30 / √(M : ℝ) := by
        have : (0 : ℝ) ≤ 1 / √(M : ℝ) := by positivity
        linarith [show 15 / √(M : ℝ) + 4 / √(M : ℝ) = 19 * (1 / √(M : ℝ)) from by ring,
          show 30 / √(M : ℝ) = 30 * (1 / √(M : ℝ)) from by ring]
      linarith
    have hN20 : 20 / √(N : ℝ) ≤ δ := by
      have : 20 / √(N : ℝ) ≤ 100 / √(N : ℝ) := by
        have : (0 : ℝ) ≤ 1 / √(N : ℝ) := by positivity
        linarith [show 20 / √(N : ℝ) = 20 * (1 / √(N : ℝ)) from by ring,
          show 100 / √(N : ℝ) = 100 * (1 / √(N : ℝ)) from by ring]
      linarith
    have hpoly : (1 + δ) ^ 2 * (L + δ) ≤ L + 10 * δ * (L + 10) :=
      poly_delta_L_le δ L hδ_pos.le hδ_le1 hL_nonneg
    have h10δ : 10 * δ * (L + 10) ≤ ε / 10 := by
      rw [mul_assoc]
      linarith only [hδL]
    have h3δ : 3 * δ ≤ ε / 10 := by
      have h1 : 10 * δ ≤ δ * (L + 10) := by nlinarith only [hδ_pos, hL_nonneg]
      linarith only [h1, hδL, hδ_pos]
    calc (1 + δ) ^ 2 * (L + δ) + 15 / √(M : ℝ) + 4 / √(M : ℝ) + 20 / √(N : ℝ) + 4 * √(3 * γ)
        = (1 + δ) ^ 2 * (L + δ) + (15 / √(M : ℝ) + 4 / √(M : ℝ)) + 20 / √(N : ℝ) + 4 * √(3 * γ) := by ring
      _ ≤ (L + 10 * δ * (L + 10)) + δ + δ + δ := by gcongr
      _ ≤ L + ε / 10 + ε / 10 := by linarith only [h10δ, h3δ]
      _ ≤ L + ε := by linarith only [hε]
  rw [div_le_iff₀ hsqrt_N_pos]
  exact hstep4.trans (mul_le_mul_of_nonneg_right h_final_coef hsqrt_N_pos.le)

lemma H1_proof :
    ∃ x : ℝ, Filter.Tendsto (fun N : ℕ => (Erdos170.F N : ℝ) / √(N : ℝ)) Filter.atTop (nhds x) := by
  let f : ℕ → ℝ := fun N => (Erdos170.F N : ℝ) / √(N : ℝ)
  let S_inf : Set ℝ := { c : ℝ | ∀ K : ℕ, ∃ N ≥ K, f N ≤ c }
  have hS_ne : S_inf.Nonempty := by
    refine ⟨7, fun K => ⟨max K 1, le_max_left K 1, ?_⟩⟩
    let N := max K 1
    have hN1 : 1 ≤ N := le_max_right K 1
    have hsqrt1 : 1 ≤ √(N : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
    have hF := F_le_real_grid N
    have hdiv : (Erdos170.F N : ℝ) ≤ 7 * √(N : ℝ) := by linarith
    exact (div_le_iff₀ (by positivity : 0 < √(N : ℝ))).mpr hdiv
  have hS_bdd : BddBelow S_inf := by
    refine ⟨0, fun c hc => ?_⟩
    obtain ⟨N, _, hNc⟩ := hc 0
    have hnn : 0 ≤ f N := by positivity
    linarith
  let L : ℝ := sInf S_inf
  have hL_nonneg : 0 ≤ L := le_csInf hS_ne fun c hc => by
    obtain ⟨N, _, hNc⟩ := hc 0
    have hnn : 0 ≤ f N := by positivity
    linarith
  have h_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, L - ε ≤ f N := by
    intro ε hε
    have hnot : ¬ ∀ K : ℕ, ∃ N ≥ K, f N ≤ L - ε := fun hmem => by
      have hle := csInf_le hS_bdd hmem
      linarith
    push Not at hnot
    obtain ⟨K, hK⟩ := hnot
    exact Filter.eventually_atTop.mpr ⟨K, fun N hN => (hK N hN).le⟩
  have h_sub : ∀ (K : ℕ) (δ : ℝ), 0 < δ → ∃ M ≥ K, f M < L + δ := by
    intro K δ hδ
    obtain ⟨c, hc_mem, hc_lt⟩ := exists_lt_of_csInf_lt hS_ne (by linarith : sInf S_inf < L + δ)
    obtain ⟨M, hM_ge, hM_le⟩ := hc_mem K
    exact ⟨M, hM_ge, hM_le.trans_lt hc_lt⟩
  have h_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, f N ≤ L + ε :=
    fun ε hε => erdos_gal_upper_bound L hL_nonneg ε hε h_sub
  refine ⟨L, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  have hev : ∀ᶠ N : ℕ in Filter.atTop, dist (f N) L < ε := by
    have h1 := h_lower (ε / 2) (by positivity)
    have h2 := h_upper (ε / 2) (by positivity)
    filter_upwards [h1, h2] with N hN1 hN2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith only [hN1, hN2, hε]
  exact Filter.eventually_atTop.mp hev

end ErdosGal

end OMA.H1Proof

theorem OMA.solution : OMA.R_Erdos170_erdos170_existing_bounds_R1.H1 :=
  OMA.H1Proof.H1_proof
