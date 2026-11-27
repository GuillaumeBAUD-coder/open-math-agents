import OMAReductions.R_Kourovka_20_51_kourovka_20_51_R1
import Mathlib

/-!
# Step Proof for Kourovka 20.51 (`Kourovka.20.51.kourovka_20_51.R1.H2`)
-/

namespace Kourovka2051Step

structure Frob (p q : ℕ) (u : (ZMod q)ˣ) : Type where
  x : ZMod q
  y : ZMod p
deriving DecidableEq

lemma Frob.ext {p q : ℕ} {u : (ZMod q)ˣ} {a b : Frob p q u}
    (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a
  cases b
  cases hx
  cases hy
  rfl

lemma Frob.ext_iff {p q : ℕ} {u : (ZMod q)ˣ} {a b : Frob p q u} :
    a = b ↔ a.x = b.x ∧ a.y = b.y :=
  ⟨fun h => ⟨congrArg Frob.x h, congrArg Frob.y h⟩, fun ⟨hx, hy⟩ => Frob.ext hx hy⟩

def frobEquivProd (p q : ℕ) (u : (ZMod q)ˣ) : Frob p q u ≃ ZMod q × ZMod p where
  toFun g := (g.x, g.y)
  invFun P := ⟨P.1, P.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance frobFintype (p q : ℕ) (u : (ZMod q)ˣ) [NeZero p] [NeZero q] : Fintype (Frob p q u) :=
  Fintype.ofEquiv (ZMod q × ZMod p) (frobEquivProd p q u).symm

def act {p q : ℕ} (u : (ZMod q)ˣ) (y : ZMod p) : ZMod q :=
  ((u ^ y.val : (ZMod q)ˣ) : ZMod q)

lemma act_zero {p q : ℕ} [NeZero p] (u : (ZMod q)ˣ) : act (p := p) u 0 = 1 := by
  simp [act]

lemma act_add {p q : ℕ} [NeZero p] (u : (ZMod q)ˣ) (hu_pow : u ^ p = 1) (y₁ y₂ : ZMod p) :
    act u (y₁ + y₂) = act u y₁ * act u y₂ := by
  have hmod : ∀ n : ℕ, u ^ (n % p) = u ^ n := fun n => by
    conv_rhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hu_pow, one_pow, one_mul]
  simp only [act, ZMod.val_add, hmod, pow_add, Units.val_mul]

lemma act_eq_one_iff {p q : ℕ} [Fact p.Prime] (u : (ZMod q)ˣ) (hu_ord : orderOf u = p)
    (y : ZMod p) : act u y = 1 ↔ y = 0 := by
  constructor
  · intro h
    have hu1 : u ^ y.val = 1 := Units.ext (by simpa [act] using h)
    have hdvd : orderOf u ∣ y.val := orderOf_dvd_iff_pow_eq_one.mpr hu1
    rw [hu_ord] at hdvd
    have hy0 : y.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt y)
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) hy0
    rwa [ZMod.natCast_zmod_val, Nat.cast_zero] at hcast
  · rintro rfl
    exact act_zero u

instance frobGroup {p q : ℕ} [NeZero p] (u : (ZMod q)ˣ) [hu : Fact (u ^ p = 1)] :
    Group (Frob p q u) where
  mul g h := ⟨g.x + act u g.y * h.x, g.y + h.y⟩
  one := ⟨0, 0⟩
  inv g := ⟨- (act u (-g.y) * g.x), -g.y⟩
  mul_assoc a b c := by
    apply Frob.ext
    · change a.x + act u a.y * b.x + act u (a.y + b.y) * c.x =
        a.x + act u a.y * (b.x + act u b.y * c.x)
      rw [act_add u hu.out]
      ring
    · exact add_assoc a.y b.y c.y
  one_mul a := by
    apply Frob.ext
    · change 0 + act u 0 * a.x = a.x
      rw [act_zero]
      ring
    · exact zero_add a.y
  mul_one a := by
    apply Frob.ext
    · change a.x + act u a.y * 0 = a.x
      ring
    · exact add_zero a.y
  inv_mul_cancel a := by
    apply Frob.ext
    · change - (act u (-a.y) * a.x) + act u (-a.y) * a.x = 0
      ring
    · exact neg_add_cancel a.y

def pairCount {p q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (y₁ y₂ : ZMod p) : ℕ :=
  ((Finset.univ : Finset (ZMod q × ZMod q)).filter
    (fun x => (act u y₁ - 1) * x.2 = (act u y₂ - 1) * x.1)).card

lemma pairCount_ne_zero {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (u : (ZMod q)ˣ) (hu_ord : orderOf u = p) {y₁ : ZMod p} (hy₁ : y₁ ≠ 0) (y₂ : ZMod p) :
    pairCount u y₁ y₂ = q := by
  have hc₁ : act u y₁ - 1 ≠ 0 :=
    sub_ne_zero.mpr (mt (act_eq_one_iff u hu_ord y₁).mp hy₁)
  have himg : ((Finset.univ : Finset (ZMod q × ZMod q)).filter
      (fun x => (act u y₁ - 1) * x.2 = (act u y₂ - 1) * x.1)) =
      (Finset.univ : Finset (ZMod q)).image
        (fun x₁ => (x₁, (act u y₁ - 1)⁻¹ * ((act u y₂ - 1) * x₁))) := by
    ext ⟨x₁, x₂⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨x₁, rfl, ?_⟩
      rw [← h, inv_mul_cancel_left₀ hc₁]
    · rintro ⟨_, rfl, rfl⟩
      rw [mul_inv_cancel_left₀ hc₁]
  unfold pairCount
  rw [himg, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h),
    Finset.card_univ, ZMod.card]

lemma pairCount_zero_zero {p q : ℕ} [NeZero p] [NeZero q] (u : (ZMod q)ˣ) :
    pairCount (p := p) u 0 0 = q * q := by
  unfold pairCount
  simp [act_zero, ZMod.card]

lemma pairCount_zero_ne {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (u : (ZMod q)ˣ) (hu_ord : orderOf u = p) {y₂ : ZMod p} (hy₂ : y₂ ≠ 0) :
    pairCount u 0 y₂ = q := by
  have hc₂ : act u y₂ - 1 ≠ 0 :=
    sub_ne_zero.mpr (mt (act_eq_one_iff u hu_ord y₂).mp hy₂)
  have himg : ((Finset.univ : Finset (ZMod q × ZMod q)).filter
      (fun x => (act u (0 : ZMod p) - 1) * x.2 = (act u y₂ - 1) * x.1)) =
      (Finset.univ : Finset (ZMod q)).image (fun x₂ => ((0 : ZMod q), x₂)) := by
    ext ⟨x₁, x₂⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq,
      act_zero, sub_self, zero_mul]
    constructor
    · intro h
      have hx₁ : x₁ = 0 := (mul_eq_zero.mp h.symm).resolve_left hc₂
      exact ⟨x₂, hx₁.symm, rfl⟩
    · rintro ⟨_, hx₁, rfl⟩
      rw [← hx₁, mul_zero]
  unfold pairCount
  rw [himg, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
    Finset.card_univ, ZMod.card]

lemma card_units_zmod (q : ℕ) [Fact q.Prime] : Fintype.card (ZMod q)ˣ = q - 1 := by
  have e : (ZMod q)ˣ ≃ {x : ZMod q // x ≠ 0} :=
    { toFun := fun u => ⟨u.val, u.ne_zero⟩
      invFun := fun x => Units.mk0 x.1 x.2
      left_inv := fun u => Units.ext rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [Fintype.card_congr e]
  have hsub : Fintype.card {x : ZMod q // x ≠ 0} =
      ((Finset.univ : Finset (ZMod q)).erase 0).card := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x _
      exact Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩
    · intro x₁ _ x₂ _ h
      exact Subtype.ext h
    · intro x hx
      exact ⟨⟨x, (Finset.mem_erase.mp hx).1⟩, Finset.mem_univ _, rfl⟩
  rw [hsub, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]

end Kourovka2051Step

theorem prove_Kourovka_20_51_H2 :
    ∀ p q : ℕ, p.Prime → Odd p → q.Prime → Odd q → p ∣ q - 1 →
      ∃ (G : Type) (_ : Group G), Finite G ∧ (∃ a b : G, a * b ≠ b * a) ∧
        Odd (Nat.card G) ∧ Nat.card (ConjClasses G) = p + (q - 1) / p := by
  intro p q hp hp_odd hq hq_odd hpq
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hp3 : 3 ≤ p := by obtain ⟨k, hk⟩ := hp_odd; have := hp.two_le; omega
  have hq3 : 3 ≤ q := by obtain ⟨k, hk⟩ := hq_odd; have := hq.two_le; omega
  obtain ⟨u, hu_ord⟩ : ∃ u : (ZMod q)ˣ, orderOf u = p := by
    apply exists_prime_orderOf_dvd_card p
    rwa [Kourovka2051Step.card_units_zmod q]
  have hu_pow : u ^ p = 1 := hu_ord ▸ pow_orderOf_eq_one u
  have : Fact (u ^ p = 1) := ⟨hu_pow⟩
  have hcardG : Nat.card (Kourovka2051Step.Frob p q u) = q * p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_congr (Kourovka2051Step.frobEquivProd p q u),
      Fintype.card_prod, ZMod.card, ZMod.card]
  refine ⟨Kourovka2051Step.Frob p q u, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_⟩
    intro hab
    have hx := congrArg Kourovka2051Step.Frob.x hab
    change (1 : ZMod q) + Kourovka2051Step.act u (0 : ZMod p) * 0 =
      0 + Kourovka2051Step.act u (1 : ZMod p) * 1 at hx
    simp only [mul_zero, add_zero, zero_add, mul_one] at hx
    have h10 : ((1 : ℕ) : ZMod p) = 0 := by
      simpa using (Kourovka2051Step.act_eq_one_iff u hu_ord 1).mp hx.symm
    have hd1 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp h10
    have := Nat.le_of_dvd (by omega) hd1
    omega
  · rw [hcardG]
    exact hq_odd.mul hp_odd
  · classical
    have hcomm_iff : ∀ g h : Kourovka2051Step.Frob p q u,
        Commute g h ↔
          (Kourovka2051Step.act u g.y - 1) * h.x = (Kourovka2051Step.act u h.y - 1) * g.x := by
      intro g h
      rw [Commute, SemiconjBy, Kourovka2051Step.Frob.ext_iff]
      change (g.x + Kourovka2051Step.act u g.y * h.x =
          h.x + Kourovka2051Step.act u h.y * g.x ∧ g.y + h.y = h.y + g.y) ↔ _
      simp only [add_comm g.y h.y, and_true]
      constructor <;> intro heq <;> linear_combination heq
    have hcomm_card : Nat.card
          {P : Kourovka2051Step.Frob p q u × Kourovka2051Step.Frob p q u // Commute P.1 P.2} =
          q * (p ^ 2 + q - 1) := by
      rw [Nat.card_eq_fintype_card]
      let eComm :
          {P : Kourovka2051Step.Frob p q u × Kourovka2051Step.Frob p q u // Commute P.1 P.2} ≃
          {t : (ZMod p × ZMod p) × (ZMod q × ZMod q) //
            (Kourovka2051Step.act u t.1.1 - 1) * t.2.2 =
              (Kourovka2051Step.act u t.1.2 - 1) * t.2.1} :=
        { toFun := fun P => ⟨((P.1.1.y, P.1.2.y), (P.1.1.x, P.1.2.x)), (hcomm_iff _ _).mp P.2⟩
          invFun := fun t =>
            ⟨(⟨t.1.2.1, t.1.1.1⟩, ⟨t.1.2.2, t.1.1.2⟩), (hcomm_iff _ _).mpr t.2⟩
          left_inv := fun ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩ => rfl
          right_inv := fun ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩ => rfl }
      rw [Fintype.card_congr eComm]
      have hsub : Fintype.card {t : (ZMod p × ZMod p) × (ZMod q × ZMod q) //
            (Kourovka2051Step.act u t.1.1 - 1) * t.2.2 =
              (Kourovka2051Step.act u t.1.2 - 1) * t.2.1} =
          ∑ y₁ : ZMod p, ∑ y₂ : ZMod p, Kourovka2051Step.pairCount u y₁ y₂ := by
        rw [← Finset.card_univ]
        have hbij : (Finset.univ : Finset {t : (ZMod p × ZMod p) × (ZMod q × ZMod q) //
              (Kourovka2051Step.act u t.1.1 - 1) * t.2.2 =
                (Kourovka2051Step.act u t.1.2 - 1) * t.2.1}).card =
            ((Finset.univ : Finset ((ZMod p × ZMod p) × (ZMod q × ZMod q))).filter
              (fun t => (Kourovka2051Step.act u t.1.1 - 1) * t.2.2 =
                (Kourovka2051Step.act u t.1.2 - 1) * t.2.1)).card := by
          refine Finset.card_bij (fun t _ => t.1) ?_ ?_ ?_
          · intro t _
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2⟩
          · intro t₁ _ t₂ _ h
            exact Subtype.ext h
          · intro t ht
            exact ⟨⟨t, (Finset.mem_filter.mp ht).2⟩, Finset.mem_univ _, rfl⟩
        rw [hbij, Finset.card_filter]
        simp only [Kourovka2051Step.pairCount, Finset.card_filter]
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      rw [hsub]
      have hcard_nz : ((Finset.univ : Finset (ZMod p)).erase 0).card = p - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
      have hsum0 : ∑ y₂ : ZMod p, Kourovka2051Step.pairCount u 0 y₂ = q * q + (p - 1) * q := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)),
          Kourovka2051Step.pairCount_zero_zero]
        congr 1
        calc ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, Kourovka2051Step.pairCount u 0 x
            = ∑ _x ∈ (Finset.univ : Finset (ZMod p)).erase 0, q := by
              refine Finset.sum_congr rfl fun x hx => ?_
              exact Kourovka2051Step.pairCount_zero_ne u hu_ord (Finset.mem_erase.mp hx).1
          _ = (p - 1) * q := by rw [Finset.sum_const, hcard_nz, smul_eq_mul]
      have hsum_nz : ∑ y₁ ∈ (Finset.univ : Finset (ZMod p)).erase 0,
            ∑ y₂ : ZMod p, Kourovka2051Step.pairCount u y₁ y₂ = (p - 1) * (p * q) := by
        calc ∑ y₁ ∈ (Finset.univ : Finset (ZMod p)).erase 0,
              ∑ y₂ : ZMod p, Kourovka2051Step.pairCount u y₁ y₂
            = ∑ _y₁ ∈ (Finset.univ : Finset (ZMod p)).erase 0, (p * q) := by
              refine Finset.sum_congr rfl fun y₁ hy₁ => ?_
              have hy₁0 : y₁ ≠ 0 := (Finset.mem_erase.mp hy₁).1
              calc ∑ y₂ : ZMod p, Kourovka2051Step.pairCount u y₁ y₂
                  = ∑ _y₂ : ZMod p, q :=
                    Finset.sum_congr rfl fun y₂ _ =>
                      Kourovka2051Step.pairCount_ne_zero u hu_ord hy₁0 y₂
                _ = p * q := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
          _ = (p - 1) * (p * q) := by rw [Finset.sum_const, hcard_nz, smul_eq_mul]
      rw [hsum0, hsum_nz]
      have hp1 : 1 ≤ p := by omega
      have hp2q : 1 ≤ p ^ 2 + q := by nlinarith
      zify [hp1, hp2q]
      ring
    have hconj_mul : Nat.card
          {P : Kourovka2051Step.Frob p q u × Kourovka2051Step.Frob p q u // Commute P.1 P.2} =
        Nat.card (ConjClasses (Kourovka2051Step.Frob p q u)) *
          Nat.card (Kourovka2051Step.Frob p q u) :=
      card_comm_eq_card_conjClasses_mul_card (Kourovka2051Step.Frob p q u)
    rw [hcomm_card, hcardG] at hconj_mul
    have hdiv_eq : p * ((q - 1) / p) = q - 1 := Nat.mul_div_cancel' hpq
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < q * p)
    rw [← hconj_mul]
    calc q * (p ^ 2 + q - 1) = q * (p * p + (q - 1)) := by
          congr 1
          have : 1 ≤ q := by omega
          have : p ^ 2 = p * p := by ring
          omega
      _ = q * (p * p + p * ((q - 1) / p)) := by rw [hdiv_eq]
      _ = (p + (q - 1) / p) * (q * p) := by ring

theorem OMA.solution : OMA.R_Kourovka_20_51_kourovka_20_51_R1.H2 :=
  prove_Kourovka_20_51_H2
