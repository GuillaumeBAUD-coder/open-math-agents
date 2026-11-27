import FormalConjectures.ErdosProblems.«1085»
import Mathlib.NumberTheory.Primorial

/-!
Erdos 1960 lower bound for 3D unit distances:
f_3(n) = Omega(n^(4/3) * log (log n)).
-/

open Filter Real Finset
open scoped EuclideanGeometry Sym2

namespace OMA

section ZModCount

/-- For an odd prime p, if -1 is a square in ZMod p, then there are p * (p + 1) triples
(a, b, c) in (ZMod p)^3 with a^2 + b^2 + c^2 = -1. -/
private lemma card_sum_three_sq_eq_neg_one_of_sq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (i : ZMod p) (hi : i ^ 2 = -1) :
    ((Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card = p * (p + 1) := by
  classical
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (le_antisymm hle hge)
  have hine : i ≠ 0 := by
    intro h0
    rw [h0] at hi
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hi
    have h1 : (1 : ZMod p) = 0 := by
      have := congrArg Neg.neg hi
      simpa using this.symm
    exact one_ne_zero h1
  have h2ine : (2 * i : ZMod p) ≠ 0 := mul_ne_zero h2ne hine
  let e : (ZMod p × ZMod p × ZMod p) ≃ (ZMod p × ZMod p × ZMod p) :=
    { toFun := fun x => (x.1 + i * x.2.1, x.1 - i * x.2.1, x.2.2)
      invFun := fun y => ((y.1 + y.2.1) * (2 : ZMod p)⁻¹, (y.1 - y.2.1) * (2 * i)⁻¹, y.2.2)
      left_inv := fun ⟨a, b, c⟩ => by
        ext <;> dsimp
        · have : a + i * b + (a - i * b) = 2 * a := by ring
          rw [this, mul_comm (2 : ZMod p) a, mul_assoc, mul_inv_cancel₀ h2ne, mul_one]
        · have : a + i * b - (a - i * b) = (2 * i) * b := by ring
          rw [this, mul_comm (2 * i) b, mul_assoc, mul_inv_cancel₀ h2ine, mul_one]
      right_inv := fun ⟨u, v, c⟩ => by
        ext <;> dsimp
        · field_simp [h2ne, hine]
          ring
        · field_simp [h2ne, hine]
          ring }
  have hcard_eq :
      ((Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
        (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card =
      ((Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
        (fun y => y.1 * y.2.1 = -(y.2.2 ^ 2 + 1))).card := by
    refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
    · intro ⟨a, b, c⟩ hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      dsimp [e]
      have hprod : (a + i * b) * (a - i * b) = a ^ 2 + b ^ 2 := by
        calc (a + i * b) * (a - i * b) = a ^ 2 - i ^ 2 * b ^ 2 := by ring
        _ = a ^ 2 - (-1) * b ^ 2 := by rw [hi]
        _ = a ^ 2 + b ^ 2 := by ring
      rw [hprod]
      linear_combination hx
    · intro x₁ _ x₂ _ h
      exact e.injective h
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨u, v, c⟩ := y
      dsimp [e] at hy ⊢
      have hu : (u + v) * (2 : ZMod p)⁻¹ + i * ((u - v) * (2 * i)⁻¹) = u := by
        field_simp [h2ne, hine]; ring
      have hv : (u + v) * (2 : ZMod p)⁻¹ - i * ((u - v) * (2 * i)⁻¹) = v := by
        field_simp [h2ne, hine]; ring
      have hprod : ((u + v) * (2 : ZMod p)⁻¹) ^ 2 + ((u - v) * (2 * i)⁻¹) ^ 2 = u * v := by
        calc ((u + v) * (2 : ZMod p)⁻¹) ^ 2 + ((u - v) * (2 * i)⁻¹) ^ 2
            = ((u + v) * (2 : ZMod p)⁻¹) ^ 2 - i ^ 2 * ((u - v) * (2 * i)⁻¹) ^ 2 := by
                rw [hi]; ring
          _ = ((u + v) * (2 : ZMod p)⁻¹ + i * ((u - v) * (2 * i)⁻¹)) *
              ((u + v) * (2 : ZMod p)⁻¹ - i * ((u - v) * (2 * i)⁻¹)) := by ring
          _ = u * v := by rw [hu, hv]
      rw [hprod, hy]
      ring
  rw [hcard_eq]
  have hfiber :
      ((Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
        (fun y => y.1 * y.2.1 = -(y.2.2 ^ 2 + 1))).card =
      ∑ c : ZMod p, ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun uv => uv.1 * uv.2 = -(c ^ 2 + 1))).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun y : ZMod p × ZMod p × ZMod p => y.2.2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.card_bij (fun y _ => (y.1, y.2.1)) ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [← hy.2]; exact hy.1
    · intro y₁ hy₁ y₂ hy₂ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2 (hy₁.2.trans hy₂.2.symm))
    · intro uv huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv
      exact ⟨(uv.1, uv.2, c), by simp [huv], rfl⟩
  rw [hfiber]
  have hzero : ((Finset.univ : Finset (ZMod p × ZMod p)).filter
      (fun uv => uv.1 * uv.2 = 0)).card = 2 * p - 1 := by
    have hsplit : (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.1 * uv.2 = 0) =
        ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.1 = 0)) ∪
        ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.2 = 0)) := by
      ext ⟨u, v⟩
      simp [mul_eq_zero]
    rw [hsplit, Finset.card_union]
    have h1 : ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.1 = 0)).card = p := by
      have : (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.1 = 0) =
          Finset.univ.image (fun v : ZMod p => ((0 : ZMod p), v)) := by
        ext ⟨u, v⟩
        simp [eq_comm]
      rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        Finset.card_univ, ZMod.card]
    have h2 : ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.2 = 0)).card = p := by
      have : (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.2 = 0) =
          Finset.univ.image (fun u : ZMod p => (u, (0 : ZMod p))) := by
        ext ⟨u, v⟩
        simp [eq_comm]
      rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        Finset.card_univ, ZMod.card]
    have h3 : (((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.1 = 0)) ∩
        ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.2 = 0))).card = 1 := by
      have : ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.1 = 0)) ∩
          ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun uv => uv.2 = 0)) =
          {((0 : ZMod p), (0 : ZMod p))} := by
        ext ⟨u, v⟩; simp
      rw [this, Finset.card_singleton]
    rw [h1, h2, h3]
    omega
  have hnonzero : ∀ t : ZMod p, t ≠ 0 →
      ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun uv => uv.1 * uv.2 = t)).card = p - 1 := by
    intro t ht
    have hbij : ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun uv => uv.1 * uv.2 = t)).card =
        ((Finset.univ : Finset (ZMod p)).filter (fun u => u ≠ 0)).card := by
      refine Finset.card_bij (fun uv _ => uv.1) ?_ ?_ ?_
      · intro uv huv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢
        intro h0
        rw [h0, zero_mul] at huv
        exact ht huv.symm
      · intro uv₁ h₁ uv₂ h₂ heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
        have hu1 : uv₁.1 ≠ 0 := by intro h0; rw [h0, zero_mul] at h₁; exact ht h₁.symm
        ext
        · exact heq
        · apply mul_left_cancel₀ hu1
          rw [h₁, heq, h₂]
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        exact ⟨(u, u⁻¹ * t), by simp [← mul_assoc, mul_inv_cancel₀ hu], rfl⟩
    rw [hbij]
    have : ((Finset.univ : Finset (ZMod p)).filter (fun u => u ≠ 0)) =
        Finset.univ.erase 0 := by ext u; simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hroots : ∀ c : ZMod p, -(c ^ 2 + 1) = 0 ↔ c = i ∨ c = -i := by
    intro c
    constructor
    · intro h
      have hc : c ^ 2 = i ^ 2 := by
        rw [hi]
        have h1 : c ^ 2 + 1 = 0 := neg_eq_zero.mp h
        linear_combination h1
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hc
    · intro h
      rcases h with rfl | rfl <;> simp [hi]
  have hi_ne_neg : i ≠ -i := by
    intro h
    have : 2 * i = 0 := by linear_combination h
    exact h2ine this
  have hsum_eval :
      (∑ c : ZMod p, ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun uv => uv.1 * uv.2 = -(c ^ 2 + 1))).card) =
      ∑ c : ZMod p, if c = i ∨ c = -i then 2 * p - 1 else p - 1 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c = i ∨ c = -i
    · rw [if_pos h, (hroots c).mpr h, hzero]
    · rw [if_neg h, hnonzero _ (mt (hroots c).mp h)]
  rw [hsum_eval]
  have hsplit_sum :
      (∑ c : ZMod p, if c = i ∨ c = -i then 2 * p - 1 else p - 1) =
      ((Finset.univ : Finset (ZMod p)).filter (fun c => c = i ∨ c = -i)).card * (2 * p - 1) +
      ((Finset.univ : Finset (ZMod p)).filter (fun c => ¬(c = i ∨ c = -i))).card * (p - 1) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  rw [hsplit_sum]
  have hset : (Finset.univ : Finset (ZMod p)).filter (fun c => c = i ∨ c = -i) = {i, -i} := by
    ext c; simp
  have hcard2 : ((Finset.univ : Finset (ZMod p)).filter (fun c => c = i ∨ c = -i)).card = 2 := by
    rw [hset, Finset.card_pair hi_ne_neg]
  have hcard_comp :
      ((Finset.univ : Finset (ZMod p)).filter (fun c => ¬(c = i ∨ c = -i))).card = p - 2 := by
    have hcomp : (Finset.univ : Finset (ZMod p)).filter (fun c => ¬(c = i ∨ c = -i)) =
        (Finset.univ : Finset (ZMod p)) \ {i, -i} := by
      ext c; simp
    rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card,
      Finset.card_pair hi_ne_neg]
  rw [hcard2, hcard_comp]
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  zify [hp3, (by omega : 1 ≤ p), (by omega : 2 ≤ p), (by omega : 1 ≤ 2 * p)]
  ring

/-- For an odd prime p, if -1 is not a square in ZMod p, then there are p * (p + 1) triples
(a, b, c) in (ZMod p)^3 with a^2 + b^2 + c^2 = -1. -/
private lemma card_sum_three_sq_eq_neg_one_of_not_sq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hnsq : ∀ i : ZMod p, i ^ 2 ≠ -1) :
    ((Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card = p * (p + 1) := by
  classical
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have hzero_iff : ∀ a b : ZMod p, a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
    intro a b
    constructor
    · intro h
      by_cases hb : b = 0
      · subst hb
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
          sq_eq_zero_iff] at h
        exact ⟨h, rfl⟩
      · exfalso
        apply hnsq (a * b⁻¹)
        have h1 : a ^ 2 = -(b ^ 2) := eq_neg_of_add_eq_zero_left h
        rw [mul_pow, inv_pow, h1, neg_mul, mul_inv_cancel₀ (pow_ne_zero 2 hb)]
    · rintro ⟨rfl, rfl⟩; simp
  have hex_rep : ∀ t : ZMod p, ∃ a b : ZMod p, a ^ 2 + b ^ 2 = t := by
    intro t
    let S : Finset (ZMod p) := Finset.univ.image (fun a : ZMod p => a ^ 2)
    let T : Finset (ZMod p) := Finset.univ.image (fun b : ZMod p => t - b ^ 2)
    have hScard : p < 2 * S.card := by
      have h2le : ∀ s ∈ S, ((Finset.univ : Finset (ZMod p)).filter (fun a => a ^ 2 = s)).card ≤ 2 := by
        intro s hs
        rcases Finset.mem_image.mp hs with ⟨a₀, _, rfl⟩
        have hsub : (Finset.univ : Finset (ZMod p)).filter (fun a => a ^ 2 = a₀ ^ 2) ⊆ {a₀, -a₀} := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact sq_eq_sq_iff_eq_or_eq_neg.mp ha
        exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
      have htot : p = ∑ s ∈ S, ((Finset.univ : Finset (ZMod p)).filter (fun a => a ^ 2 = s)).card := by
        rw [← Finset.card_eq_sum_card_fiberwise (f := fun a : ZMod p => a ^ 2)
          (s := Finset.univ) (t := S) (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a))]
        rw [Finset.card_univ, ZMod.card]
      have h0in : (0 : ZMod p) ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩
      have h0card : ((Finset.univ : Finset (ZMod p)).filter (fun a => a ^ 2 = 0)).card = 1 := by
        have : (Finset.univ : Finset (ZMod p)).filter (fun a => a ^ 2 = 0) = {0} := by
          ext a; simp [sq_eq_zero_iff]
        rw [this, Finset.card_singleton]
      have hsum_le : ∑ s ∈ S, ((Finset.univ : Finset (ZMod p)).filter (fun a => a ^ 2 = s)).card ≤
          1 + 2 * (S.card - 1) := by
        rw [← Finset.add_sum_erase _ _ h0in, h0card]
        have hrest : ∑ s ∈ S.erase 0,
            ((Finset.univ : Finset (ZMod p)).filter (fun a => a ^ 2 = s)).card ≤
            ∑ _s ∈ S.erase 0, 2 :=
          Finset.sum_le_sum fun s hs => h2le s (Finset.mem_of_mem_erase hs)
        rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0in, mul_comm] at hrest
        omega
      have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, h0in⟩
      omega
    have hTcard : T.card = S.card := by
      have hTeq : T = S.image (fun x => t - x) := by
        ext y
        simp only [T, S, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨b, rfl⟩; exact ⟨b ^ 2, ⟨b, rfl⟩, rfl⟩
        · rintro ⟨x, ⟨b, rfl⟩, rfl⟩; exact ⟨b, rfl⟩
      rw [hTeq, Finset.card_image_of_injective _ (fun x y h => by linear_combination -h)]
    have hnonempty : (S ∩ T).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have hdisj : Disjoint S T := Finset.disjoint_iff_inter_eq_empty.mpr h
      have hle : (S ∪ T).card ≤ (Finset.univ : Finset (ZMod p)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdisj, hTcard, Finset.card_univ, ZMod.card] at hle
      omega
    rcases hnonempty with ⟨y, hy⟩
    rcases Finset.mem_inter.mp hy with ⟨hyS, hyT⟩
    rcases Finset.mem_image.mp hyS with ⟨a, _, ha⟩
    rcases Finset.mem_image.mp hyT with ⟨b, _, hb⟩
    refine ⟨a, b, ?_⟩
    linear_combination ha - hb
  have hfiber_eq : ∀ t : ZMod p, t ≠ 0 →
      ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = t)).card =
      ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = 1)).card := by
    intro t ht
    obtain ⟨a₀, b₀, hab₀⟩ := hex_rep t
    refine Finset.card_bij
      (fun ab _ => ((a₀ * ab.1 + b₀ * ab.2) * t⁻¹, (a₀ * ab.2 - b₀ * ab.1) * t⁻¹)) ?_ ?_ ?_
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
      have hid : (a₀ * a + b₀ * b) ^ 2 + (a₀ * b - b₀ * a) ^ 2 =
          (a₀ ^ 2 + b₀ ^ 2) * (a ^ 2 + b ^ 2) := by ring
      calc ((a₀ * a + b₀ * b) * t⁻¹) ^ 2 + ((a₀ * b - b₀ * a) * t⁻¹) ^ 2
          = ((a₀ * a + b₀ * b) ^ 2 + (a₀ * b - b₀ * a) ^ 2) * (t⁻¹) ^ 2 := by ring
        _ = (t * t) * (t⁻¹) ^ 2 := by rw [hid, hab₀, hab]
        _ = 1 := by field_simp [ht]
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      have h1 : a₀ * a₁ + b₀ * b₁ = a₀ * a₂ + b₀ * b₂ :=
        mul_right_cancel₀ (inv_ne_zero ht) heq.1
      have h2 : a₀ * b₁ - b₀ * a₁ = a₀ * b₂ - b₀ * a₂ :=
        mul_right_cancel₀ (inv_ne_zero ht) heq.2
      have ha : t * (a₁ - a₂) = 0 := by
        rw [← hab₀]
        linear_combination a₀ * h1 - b₀ * h2
      have hb : t * (b₁ - b₂) = 0 := by
        rw [← hab₀]
        linear_combination b₀ * h1 + a₀ * h2
      have ha' : a₁ = a₂ := sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_left ht)
      have hb' : b₁ = b₂ := sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left ht)
      exact Prod.ext ha' hb'
    · intro ⟨u, v⟩ huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv
      refine ⟨(a₀ * u - b₀ * v, b₀ * u + a₀ * v), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        calc (a₀ * u - b₀ * v) ^ 2 + (b₀ * u + a₀ * v) ^ 2
            = (a₀ ^ 2 + b₀ ^ 2) * (u ^ 2 + v ^ 2) := by ring
          _ = t * 1 := by rw [hab₀, huv]
          _ = t := mul_one t
      · ext <;> dsimp
        · calc (a₀ * (a₀ * u - b₀ * v) + b₀ * (b₀ * u + a₀ * v)) * t⁻¹
              = (a₀ ^ 2 + b₀ ^ 2) * u * t⁻¹ := by ring
            _ = t * u * t⁻¹ := by rw [hab₀]
            _ = u := by field_simp [ht]
        · calc (a₀ * (b₀ * u + a₀ * v) - b₀ * (a₀ * u - b₀ * v)) * t⁻¹
              = (a₀ ^ 2 + b₀ ^ 2) * v * t⁻¹ := by ring
            _ = t * v * t⁻¹ := by rw [hab₀]
            _ = v := by field_simp [ht]
  have hunit_card :
      ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = 1)).card =
      p + 1 := by
    have htot : (Finset.univ : Finset (ZMod p × ZMod p)).card =
        ∑ t : ZMod p, ((Finset.univ : Finset (ZMod p × ZMod p)).filter
          (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = t)).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun ab : ZMod p × ZMod p => ab.1 ^ 2 + ab.2 ^ 2)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at htot
    have h0 : ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = 0)).card = 1 := by
      have : (Finset.univ : Finset (ZMod p × ZMod p)).filter (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = 0) =
          {((0 : ZMod p), (0 : ZMod p))} := by
        ext ⟨a, b⟩; simp [hzero_iff]
      rw [this, Finset.card_singleton]
    rw [h0] at htot
    have hsum : ∑ t ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        ((Finset.univ : Finset (ZMod p × ZMod p)).filter
          (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = t)).card =
        (p - 1) * ((Finset.univ : Finset (ZMod p × ZMod p)).filter
          (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = 1)).card := by
      have hcongr : ∑ t ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          ((Finset.univ : Finset (ZMod p × ZMod p)).filter
            (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = t)).card =
          ∑ _t ∈ (Finset.univ : Finset (ZMod p)).erase 0,
            ((Finset.univ : Finset (ZMod p × ZMod p)).filter
              (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = 1)).card :=
        Finset.sum_congr rfl fun t ht => hfiber_eq t (Finset.ne_of_mem_erase ht)
      rw [hcongr, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, ZMod.card]
    rw [hsum] at htot
    have hmul : (p - 1) * ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = 1)).card = (p - 1) * (p + 1) := by
      have hp1 : 1 ≤ p := by omega
      zify [hp1] at htot ⊢
      linarith
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p - 1) hmul
  have hfiber :
      ((Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
        (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card =
      ∑ c : ZMod p, ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = -1 - c ^ 2)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod p × ZMod p × ZMod p => x.2.2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.card_bij (fun x _ => (x.1, x.2.1)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← hx.2]; linear_combination hx.1
    · intro x₁ h₁ x₂ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.1 (Prod.ext heq.2 (h₁.2.trans h₂.2.symm))
    · intro ab hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
      refine ⟨(ab.1, ab.2, c), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by linear_combination hab, trivial⟩
  rw [hfiber]
  have hcongr : ∑ c : ZMod p, ((Finset.univ : Finset (ZMod p × ZMod p)).filter
      (fun ab => ab.1 ^ 2 + ab.2 ^ 2 = -1 - c ^ 2)).card = ∑ _c : ZMod p, (p + 1) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have hne : (-1 - c ^ 2 : ZMod p) ≠ 0 := by
      intro h
      apply hnsq c
      linear_combination -h
    rw [hfiber_eq _ hne, hunit_card]
  rw [hcongr, Finset.sum_const, smul_eq_mul, Finset.card_univ, ZMod.card]

/-- For every odd prime p, there are p * (p + 1) triples (a, b, c) in (ZMod p)^3 with
a^2 + b^2 + c^2 = -1. -/
private lemma card_sum_three_sq_eq_neg_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card = p * (p + 1) := by
  by_cases h : ∃ i : ZMod p, i ^ 2 = -1
  · rcases h with ⟨i, hi⟩
    exact card_sum_three_sq_eq_neg_one_of_sq p hp2 i hi
  · push_neg at h
    exact card_sum_three_sq_eq_neg_one_of_not_sq p hp2 h

private lemma card_sum_three_sq_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    ((Finset.univ : Finset (ZMod a × ZMod a × ZMod a)).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card =
    ((Finset.univ : Finset (ZMod b × ZMod b × ZMod b)).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card := by
  subst h; rfl

/-- CRT lift: for any finite set P of odd primes, the number of triples (a, b, c) in
(ZMod (prod P))^3 with a^2 + b^2 + c^2 = -1 is prod_{p in P} p * (p + 1). -/
private lemma card_sum_three_sq_eq_neg_one_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    ∀ [NeZero (∏ p ∈ P, p)],
    ((Finset.univ : Finset (ZMod (∏ p ∈ P, p) × ZMod (∏ p ∈ P, p) × ZMod (∏ p ∈ P, p))).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card =
      ∏ p ∈ P, (p * (p + 1)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro _
    rw [card_sum_three_sq_congr Finset.prod_empty, Finset.prod_empty]
    decide
  | @insert p s hp_not_mem ih =>
    intro _
    have hp_prime : p.Prime := (hP p (Finset.mem_insert_self p s)).1
    have hp2 : p ≠ 2 := (hP p (Finset.mem_insert_self p s)).2
    have hs : ∀ q ∈ s, q.Prime ∧ q ≠ 2 := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_prime : q.Prime := (hs q hq).1
      have hne : p ≠ q := fun h => hp_not_mem (h ▸ hq)
      exact (hp_prime.coprime_iff_not_dvd).mpr fun hdvd => hne ((hq_prime.eq_one_or_self_of_dvd p hdvd).resolve_left hp_prime.ne_one)
    have : Fact p.Prime := ⟨hp_prime⟩
    have : NeZero (∏ q ∈ s, q) := ⟨Finset.prod_ne_zero_iff.mpr fun q hq => (hs q hq).1.ne_zero⟩
    have : NeZero (p * ∏ q ∈ s, q) := ⟨mul_ne_zero hp_prime.ne_zero (NeZero.ne _)⟩
    rw [card_sum_three_sq_congr (Finset.prod_insert hp_not_mem), Finset.prod_insert hp_not_mem]
    let e : ZMod (p * ∏ q ∈ s, q) ≃+* ZMod p × ZMod (∏ q ∈ s, q) := ZMod.chineseRemainder hcop
    let S₁ := (Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)
    let S₂ := (Finset.univ : Finset (ZMod (∏ q ∈ s, q) × ZMod (∏ q ∈ s, q) × ZMod (∏ q ∈ s, q))).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)
    have hbij :
        ((Finset.univ : Finset (ZMod (p * ∏ q ∈ s, q) × ZMod (p * ∏ q ∈ s, q) × ZMod (p * ∏ q ∈ s, q))).filter
          (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)).card = (S₁ ×ˢ S₂).card := by
      refine Finset.card_bij
        (fun x _ => (((e x.1).1, (e x.2.1).1, (e x.2.2).1), ((e x.1).2, (e x.2.1).2, (e x.2.2).2))) ?_ ?_ ?_
      · intro ⟨a, b, c⟩ hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have heq : e (a ^ 2 + b ^ 2 + c ^ 2) = e (-1) := congrArg e hx
        simp only [map_add, map_pow, map_neg, map_one] at heq
        have h1 : (e a).1 ^ 2 + (e b).1 ^ 2 + (e c).1 ^ 2 = -1 := congrArg Prod.fst heq
        have h2 : (e a).2 ^ 2 + (e b).2 ^ 2 + (e c).2 ^ 2 = -1 := congrArg Prod.snd heq
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
      · intro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ _ h
        simp only [Prod.mk.injEq] at h
        have ha : e a₁ = e a₂ := Prod.ext h.1.1 h.2.1
        have hb : e b₁ = e b₂ := Prod.ext h.1.2.1 h.2.2.1
        have hc : e c₁ = e c₂ := Prod.ext h.1.2.2 h.2.2.2
        exact Prod.ext (e.injective ha) (Prod.ext (e.injective hb) (e.injective hc))
      · intro ⟨⟨a₁, b₁, c₁⟩, ⟨a₂, b₂, c₂⟩⟩ hy
        rcases Finset.mem_product.mp hy with ⟨hy₁, hy₂⟩
        simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
        refine ⟨(e.symm (a₁, a₂), e.symm (b₁, b₂), e.symm (c₁, c₂)), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          apply e.injective
          simp only [map_add, map_pow, map_neg, map_one, RingEquiv.apply_symm_apply]
          exact Prod.ext hy₁ hy₂
        · simp
    rw [hbij, Finset.card_product, card_sum_three_sq_eq_neg_one p hp2, ih hs]

end ZModCount

section Pigeonhole

/-- Given a finite set P of odd primes with Q = prod P >= 3 and M = k * Q (k >= 1),
there exists r with 0 < r < 3 * M^2 such that the number of triples (a, b, c) in [0, M)^3
with a^2 + b^2 + c^2 = r is at least (k / 3) * prod_{p in P} (p + 1). -/
private lemma exists_radius_many_reps (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hQ3 : 3 ≤ ∏ p ∈ P, p) (k : ℕ) (hk : 1 ≤ k) :
    ∃ r : ℕ, 0 < r ∧ r < 3 * (k * ∏ p ∈ P, p) ^ 2 ∧
      ((k : ℝ) / 3) * ∏ p ∈ P, ((p : ℝ) + 1) ≤
        ((((Finset.range (k * ∏ p ∈ P, p)) ×ˢ (Finset.range (k * ∏ p ∈ P, p)) ×ˢ
            (Finset.range (k * ∏ p ∈ P, p))).filter
          (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)).card : ℝ) := by
  classical
  set Q := ∏ p ∈ P, p with hQ_def
  have hQ_pos : 0 < Q := by omega
  haveI : NeZero Q := ⟨by omega⟩
  set M := k * Q with hM_def
  set Box := (Finset.range M) ×ˢ (Finset.range M) ×ˢ (Finset.range M)
  set Good := Box.filter (fun x => ((x.1 : ZMod Q) ^ 2 + (x.2.1 : ZMod Q) ^ 2 + (x.2.2 : ZMod Q) ^ 2 = -1))
  have hGood_card : Good.card = k ^ 3 * ∏ p ∈ P, (p * (p + 1)) := by
    let ZGood := (Finset.univ : Finset (ZMod Q × ZMod Q × ZMod Q)).filter
      (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = -1)
    let K3 := (Finset.range k) ×ˢ (Finset.range k) ×ˢ (Finset.range k)
    have hbij : Good.card = (K3 ×ˢ ZGood).card := by
      refine Finset.card_bij
        (fun x _ => ((x.1 / Q, x.2.1 / Q, x.2.2 / Q), ((x.1 : ZMod Q), (x.2.1 : ZMod Q), (x.2.2 : ZMod Q))))
        ?_ ?_ ?_
      · intro ⟨a, b, c⟩ hx
        simp only [Good, Box, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
        refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · simp only [K3, Finset.mem_product, Finset.mem_range]
          have hMcomm : M = Q * k := mul_comm k Q
          exact ⟨Nat.div_lt_of_lt_mul (hMcomm ▸ hx.1.1),
            Nat.div_lt_of_lt_mul (hMcomm ▸ hx.1.2.1),
            Nat.div_lt_of_lt_mul (hMcomm ▸ hx.1.2.2)⟩
        · simp only [ZGood, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hx.2
      · intro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ _ h
        simp only [Prod.mk.injEq] at h
        have hmod : ∀ u v : ℕ, (u : ZMod Q) = (v : ZMod Q) → u % Q = v % Q := by
          intro u v huv
          have := congrArg ZMod.val huv
          simpa [ZMod.val_natCast] using this
        have ha : a₁ = a₂ := by
          have hm := hmod a₁ a₂ h.2.1
          have hd := h.1.1
          have h1 := Nat.div_add_mod a₁ Q
          have h2 := Nat.div_add_mod a₂ Q
          rw [hd, hm] at h1
          linarith
        have hb : b₁ = b₂ := by
          have hm := hmod b₁ b₂ h.2.2.1
          have hd := h.1.2.1
          have h1 := Nat.div_add_mod b₁ Q
          have h2 := Nat.div_add_mod b₂ Q
          rw [hd, hm] at h1
          linarith
        have hc : c₁ = c₂ := by
          have hm := hmod c₁ c₂ h.2.2.2
          have hd := h.1.2.2
          have h1 := Nat.div_add_mod c₁ Q
          have h2 := Nat.div_add_mod c₂ Q
          rw [hd, hm] at h1
          linarith
        exact Prod.ext ha (Prod.ext hb hc)
      · intro ⟨⟨q₁, q₂, q₃⟩, ⟨r₁, r₂, r₃⟩⟩ hy
        rcases Finset.mem_product.mp hy with ⟨hq, hr⟩
        simp only [K3, Finset.mem_product, Finset.mem_range] at hq
        simp only [ZGood, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        let a := q₁ * Q + r₁.val
        let b := q₂ * Q + r₂.val
        let c := q₃ * Q + r₃.val
        have hr1 : r₁.val < Q := r₁.val_lt
        have hr2 : r₂.val < Q := r₂.val_lt
        have hr3 : r₃.val < Q := r₃.val_lt
        have ha_lt : a < M := by dsimp [a, M]; nlinarith
        have hb_lt : b < M := by dsimp [b, M]; nlinarith
        have hc_lt : c < M := by dsimp [c, M]; nlinarith
        have ha_cast : (a : ZMod Q) = r₁ := by
          dsimp [a]; push_cast; simp [ZMod.natCast_self, ZMod.natCast_zmod_val]
        have hb_cast : (b : ZMod Q) = r₂ := by
          dsimp [b]; push_cast; simp [ZMod.natCast_self, ZMod.natCast_zmod_val]
        have hc_cast : (c : ZMod Q) = r₃ := by
          dsimp [c]; push_cast; simp [ZMod.natCast_self, ZMod.natCast_zmod_val]
        refine ⟨(a, b, c), ?_, ?_⟩
        · simp only [Good, Box, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨ha_lt, hb_lt, hc_lt⟩, by rw [ha_cast, hb_cast, hc_cast]; exact hr⟩
        · have hda : a / Q = q₁ := by
            dsimp [a]
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ_pos, Nat.div_eq_of_lt hr1, zero_add]
          have hdb : b / Q = q₂ := by
            dsimp [b]
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ_pos, Nat.div_eq_of_lt hr2, zero_add]
          have hdc : c / Q = q₃ := by
            dsimp [c]
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ_pos, Nat.div_eq_of_lt hr3, zero_add]
          simp [hda, hdb, hdc, ha_cast, hb_cast, hc_cast]
    rw [hbij, Finset.card_product]
    have hK3 : K3.card = k ^ 3 := by
      simp [K3, Finset.card_product, pow_three]
    rw [hK3, card_sum_three_sq_eq_neg_one_prod P hP]
  set Rset : Finset ℕ := (Finset.range (3 * k ^ 2 * Q)).image (fun j => j * Q + (Q - 1))
  have hRset_card : Rset.card = 3 * k ^ 2 * Q := by
    rw [Finset.card_image_of_injective _ (fun j₁ j₂ h => by
      have : j₁ * Q = j₂ * Q := by omega
      exact Nat.eq_of_mul_eq_mul_right hQ_pos this), Finset.card_range]
  have hmaps : ∀ x ∈ Good, x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 ∈ Rset := by
    intro ⟨a, b, c⟩ hx
    simp only [Good, Box, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    set r := a ^ 2 + b ^ 2 + c ^ 2
    have hr_lt : r < 3 * M ^ 2 := by
      have ha : a ^ 2 < M ^ 2 := Nat.pow_lt_pow_left hx.1.1 (by norm_num)
      have hb : b ^ 2 < M ^ 2 := Nat.pow_lt_pow_left hx.1.2.1 (by norm_num)
      have hc : c ^ 2 < M ^ 2 := Nat.pow_lt_pow_left hx.1.2.2 (by norm_num)
      dsimp [r]; omega
    have hr_cast : (r : ZMod Q) = -1 := by
      dsimp [r]; push_cast; exact hx.2
    have hr_mod : r % Q = Q - 1 := by
      have h1 : ((r + 1 : ℕ) : ZMod Q) = 0 := by
        push_cast; rw [hr_cast]; ring
      have hdvd : Q ∣ r + 1 := (ZMod.natCast_eq_zero_iff (r + 1) Q).mp h1
      rcases hdvd with ⟨t, ht⟩
      have ht_pos : 1 ≤ t := by nlinarith
      have hr_eq : r = (Q - 1) + Q * (t - 1) := by
        have hQ1 : 1 ≤ Q := by omega
        zify [ht_pos, hQ1] at ht ⊢
        linarith
      rw [hr_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hj_lt : r / Q < 3 * k ^ 2 * Q := by
      have h3M : 3 * M ^ 2 = Q * (3 * k ^ 2 * Q) := by dsimp [M]; ring
      rw [h3M] at hr_lt
      exact Nat.div_lt_of_lt_mul hr_lt
    refine Finset.mem_image.mpr ⟨r / Q, Finset.mem_range.mpr hj_lt, ?_⟩
    rw [← hr_mod, mul_comm]
    exact Nat.div_add_mod r Q
  have hRset_nonempty : Rset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := congrArg Finset.card h
    rw [hRset_card, Finset.card_empty] at this
    have : 0 < 3 * k ^ 2 * Q := by positivity
    omega
  have hsum : Good.card = ∑ r ∈ Rset, (Good.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  obtain ⟨r, hr_mem, hr_ge⟩ : ∃ r ∈ Rset,
      Good.card ≤ Rset.card * (Good.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)).card := by
    by_contra hall
    push_neg at hall
    have hlt : ∑ r ∈ Rset, (Good.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)).card * Rset.card <
        ∑ _r ∈ Rset, Good.card := by
      refine Finset.sum_lt_sum_of_nonempty hRset_nonempty fun r hr => ?_
      rw [mul_comm]
      exact hall r hr
    rw [← Finset.sum_mul, ← hsum, Finset.sum_const, smul_eq_mul, mul_comm] at hlt
    exact lt_irrefl _ hlt
  rcases Finset.mem_image.mp hr_mem with ⟨j, hj, rfl⟩
  rw [Finset.mem_range] at hj
  refine ⟨j * Q + (Q - 1), by omega, ?_, ?_⟩
  · have h3M : 3 * M ^ 2 = (3 * k ^ 2 * Q) * Q := by dsimp [M]; ring
    rw [h3M]
    have hmul : (j + 1) * Q ≤ (3 * k ^ 2 * Q) * Q := Nat.mul_le_mul_right Q hj
    have hadd : j * Q + Q = (j + 1) * Q := by ring
    omega
  · have hsub : Good.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = j * Q + (Q - 1)) ⊆
        Box.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = j * Q + (Q - 1)) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have hcard_le : Good.card ≤ Rset.card *
        (Box.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = j * Q + (Q - 1))).card :=
      hr_ge.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))
    rw [hGood_card, hRset_card] at hcard_le
    have hcast : ((k ^ 3 * ∏ p ∈ P, (p * (p + 1)) : ℕ) : ℝ) ≤
        ((3 * k ^ 2 * Q * (Box.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = j * Q + (Q - 1))).card : ℕ) : ℝ) := by
      exact_mod_cast hcard_le
    push_cast at hcast
    have hprod_split : (∏ p ∈ P, ((p : ℝ) * ((p : ℝ) + 1))) = (Q : ℝ) * ∏ p ∈ P, ((p : ℝ) + 1) := by
      rw [Finset.prod_mul_distrib, hQ_def]; push_cast; rfl
    rw [hprod_split] at hcast
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hQ_posR : (0 : ℝ) < Q := by exact_mod_cast hQ_pos
    have hfac_pos : (0 : ℝ) < (k : ℝ) ^ 2 * (Q : ℝ) := by positivity
    have hmul_le : ((k : ℝ) ^ 2 * (Q : ℝ)) * ((k : ℝ) * ∏ p ∈ P, ((p : ℝ) + 1)) ≤
        ((k : ℝ) ^ 2 * (Q : ℝ)) * (3 * ((Box.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = j * Q + (Q - 1))).card : ℝ)) := by
      linarith
    have hcancel := le_of_mul_le_mul_left hmul_le hfac_pos
    rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith

end Pigeonhole

section AnalyticBounds

/-- Weierstrass product inequality: 1 - sum a <= prod (1 - a) for a in [0, 1]. -/
private lemma one_sub_sum_le_prod_one_sub {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha0 : ∀ x ∈ s, 0 ≤ a x) (ha1 : ∀ x ∈ s, a x ≤ 1) :
    1 - ∑ x ∈ s, a x ≤ ∏ x ∈ s, (1 - a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hx0 : 0 ≤ a x := ha0 x (Finset.mem_insert_self x s)
    have hx1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self x s)
    have hs0 : ∀ y ∈ s, 0 ≤ a y := fun y hy => ha0 y (Finset.mem_insert_of_mem hy)
    have hs1 : ∀ y ∈ s, a y ≤ 1 := fun y hy => ha1 y (Finset.mem_insert_of_mem hy)
    have hih := ih hs0 hs1
    have hsum_nonneg : 0 ≤ ∑ y ∈ s, a y := Finset.sum_nonneg hs0
    have hprod_nonneg : 0 ≤ 1 - a x := by linarith
    nlinarith

/-- Sum of 1/k for k in 1..y is at least log(y + 1). -/
private lemma log_succ_le_harmonic (y : ℕ) :
    Real.log ((y : ℝ) + 1) ≤ ∑ k ∈ Finset.Icc 1 y, (1 : ℝ) / k := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [show Finset.Icc 1 (y + 1) = insert (y + 1) (Finset.Icc 1 y) from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.sum_insert (by simp)]
    have hy1 : (0 : ℝ) < (y : ℝ) + 1 := by positivity
    have hy2 : (0 : ℝ) < (y : ℝ) + 2 := by positivity
    have hstep : Real.log ((y : ℝ) + 2) - Real.log ((y : ℝ) + 1) ≤ 1 / ((y : ℝ) + 1) := by
      rw [← Real.log_div (ne_of_gt hy2) (ne_of_gt hy1)]
      have hle := Real.log_le_sub_one_of_pos (div_pos hy2 hy1)
      have heq : ((y : ℝ) + 2) / ((y : ℝ) + 1) - 1 = 1 / ((y : ℝ) + 1) := by
        field_simp [ne_of_gt hy1]; ring
      linarith
    push_cast
    rw [show (y : ℝ) + 1 + 1 = (y : ℝ) + 2 by ring]
    linarith

/-- Euler product lower bound: prod_{p <= y prime} (1 - 1/p)^(-1) >= sum_{k=1}^y 1/k. -/
private lemma harmonic_le_prod_inv_one_sub (y : ℕ) :
    ∑ k ∈ Finset.Icc 1 y, (1 : ℝ) / k ≤
      ∏ p ∈ (Finset.range (y + 1)).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ := by
  classical
  set Pall := (Finset.range (y + 1)).filter Nat.Prime
  have hgeom : ∀ p ∈ Pall, ∑ j ∈ Finset.range (y + 1), ((1 : ℝ) / p) ^ j ≤ (1 - (1 : ℝ) / p)⁻¹ := by
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
    have hlt1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by positivity)]; linarith
    have hnonneg : (0 : ℝ) ≤ 1 / p := by positivity
    rw [geom_sum_eq (ne_of_lt hlt1)]
    have hpos : 0 < 1 - (1 : ℝ) / p := by linarith
    rw [div_eq_mul_inv]
    have hnum : ((1 : ℝ) / p) ^ (y + 1) - 1 ≤ 1 - 1 := by
      have : ((1 : ℝ) / p) ^ (y + 1) ≤ 1 := pow_le_one₀ hnonneg (le_of_lt hlt1)
      linarith
    have hrewrite : (((1 : ℝ) / p) ^ (y + 1) - 1) * ((1 : ℝ) / p - 1)⁻¹ =
        (1 - ((1 : ℝ) / p) ^ (y + 1)) * (1 - (1 : ℝ) / p)⁻¹ := by
      have hneg : (1 : ℝ) / p - 1 = -(1 - (1 : ℝ) / p) := by ring
      rw [hneg, inv_neg]
      ring
    rw [hrewrite]
    have hpow_nonneg : 0 ≤ ((1 : ℝ) / p) ^ (y + 1) := pow_nonneg hnonneg _
    nlinarith [inv_pos.mpr hpos]
  have hprod_ge :
      ∏ p ∈ Pall, ∑ j ∈ Finset.range (y + 1), ((1 : ℝ) / p) ^ j ≤
      ∏ p ∈ Pall, (1 - (1 : ℝ) / p)⁻¹ :=
    Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun j _ => by positivity) hgeom
  refine le_trans ?_ hprod_ge
  rw [Finset.prod_sum]
  let idx : ℕ → ∀ p ∈ Pall, ℕ := fun k p _ => k.factorization p
  have hmem : ∀ k ∈ Finset.Icc 1 y, idx k ∈ Pall.pi (fun _ => Finset.range (y + 1)) := by
    intro k hk
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk_le : k ≤ y := (Finset.mem_Icc.mp hk).2
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hle_k : k.factorization p ≤ k := by
      have hpow : p ^ k.factorization p ∣ k := Nat.ordProj_dvd k p
      have hle1 : p ^ k.factorization p ≤ k := Nat.le_of_dvd hk_pos hpow
      have hle2 : k.factorization p < 2 ^ k.factorization p := Nat.lt_two_pow_self
      have hle3 : 2 ^ k.factorization p ≤ p ^ k.factorization p :=
        Nat.pow_le_pow_left hp_prime.two_le _
      exact le_of_lt (lt_of_lt_of_le hle2 (hle3.trans hle1))
    dsimp [idx]
    omega
  have hval : ∀ k ∈ Finset.Icc 1 y,
      (∏ p ∈ Pall.attach, ((1 : ℝ) / p.1) ^ (idx k p.1 p.2)) = (1 : ℝ) / k := by
    intro k hk
    have hk_ne : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    have hk_le : k ≤ y := (Finset.mem_Icc.mp hk).2
    have hprod_eq : ∏ p ∈ Pall.attach, (p.1 : ℕ) ^ (idx k p.1 p.2) = k := by
      have hattach : ∏ p ∈ Pall.attach, p.1 ^ (k.factorization p.1) =
          ∏ p ∈ Pall, p ^ (k.factorization p) := Finset.prod_attach Pall (fun p => p ^ k.factorization p)
      rw [show (∏ p ∈ Pall.attach, p.1 ^ (idx k p.1 p.2)) = ∏ p ∈ Pall, p ^ (k.factorization p) from hattach]
      have hsupp : k.factorization.support ⊆ Pall := by
        intro p hp
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hp_dvd : p ∣ k := Nat.dvd_of_mem_primeFactors hp
        have hp_le : p ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk_ne) hp_dvd
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime⟩
      rw [← Finset.prod_subset hsupp (fun p _ hp_not => by
        have : k.factorization p = 0 := by
          by_contra hne
          exact hp_not (Finsupp.mem_support_iff.mpr hne)
        simp [this])]
      exact Nat.prod_factorization_pow_eq_self hk_ne
    calc ∏ p ∈ Pall.attach, ((1 : ℝ) / p.1) ^ (idx k p.1 p.2)
        = ∏ p ∈ Pall.attach, (1 : ℝ) / ((p.1 : ℝ) ^ (idx k p.1 p.2)) := by
            refine Finset.prod_congr rfl fun p _ => by rw [one_div, inv_pow, one_div]
      _ = 1 / ∏ p ∈ Pall.attach, ((p.1 : ℝ) ^ (idx k p.1 p.2)) := by
            rw [Finset.prod_div_distrib, Finset.prod_const_one]
      _ = 1 / ((∏ p ∈ Pall.attach, (p.1 : ℕ) ^ (idx k p.1 p.2) : ℕ) : ℝ) := by
            push_cast; rfl
      _ = (1 : ℝ) / k := by rw [hprod_eq]
  have hinj : Set.InjOn idx (Finset.Icc 1 y : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ h
    have h1 := hval k₁ hk₁
    have h2 := hval k₂ hk₂
    rw [h] at h1
    have heq : (1 : ℝ) / k₁ = (1 : ℝ) / k₂ := h1.symm.trans h2
    have hk1_pos : (0 : ℝ) < k₁ := by exact_mod_cast (Finset.mem_Icc.mp hk₁).1
    have hk2_pos : (0 : ℝ) < k₂ := by exact_mod_cast (Finset.mem_Icc.mp hk₂).1
    have hreal : (k₁ : ℝ) = (k₂ : ℝ) := by
      have := (div_eq_div_iff (ne_of_gt hk1_pos) (ne_of_gt hk2_pos)).mp heq
      linarith
    exact_mod_cast hreal
  calc ∑ k ∈ Finset.Icc 1 y, (1 : ℝ) / k
      = ∑ k ∈ Finset.Icc 1 y, ∏ p ∈ Pall.attach, ((1 : ℝ) / p.1) ^ (idx k p.1 p.2) :=
          Finset.sum_congr rfl fun k hk => (hval k hk).symm
    _ = ∑ f ∈ (Finset.Icc 1 y).image idx, ∏ p ∈ Pall.attach, ((1 : ℝ) / p.1) ^ (f p.1 p.2) :=
          (Finset.sum_image (f := fun f => ∏ p ∈ Pall.attach, ((1 : ℝ) / p.1) ^ (f p.1 p.2))
            (fun k₁ hk₁ k₂ hk₂ h => hinj hk₁ hk₂ h)).symm
    _ ≤ ∑ f ∈ Pall.pi (fun _ => Finset.range (y + 1)),
          ∏ p ∈ Pall.attach, ((1 : ℝ) / p.1) ^ (f p.1 p.2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun f _ _ => Finset.prod_nonneg fun p _ => by positivity)
          intro f hf
          rcases Finset.mem_image.mp hf with ⟨k, hk, rfl⟩
          exact hmem k hk

/-- Product of (1 + 1/p) over odd primes p <= y is at least (1/4) * log y. -/
private lemma quarter_log_le_prod_odd_primes (y : ℕ) (hy : 3 ≤ y) :
    (1 / 4 : ℝ) * Real.log (y : ℝ) ≤
      ∏ p ∈ ((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≠ 2)), (1 + (1 : ℝ) / p) := by
  classical
  set Podd := (Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
  set Pall := (Finset.range (y + 1)).filter Nat.Prime
  have h2mem : 2 ∈ Pall := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hPodd_eq : Podd = Pall.erase 2 := by
    ext p
    simp only [Podd, Pall, Finset.mem_filter, Finset.mem_erase]
    tauto
  have hsq_prod : (1 / 2 : ℝ) ≤ ∏ p ∈ Podd, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
    have hw := one_sub_sum_le_prod_one_sub Podd (fun p => (1 : ℝ) / (p : ℝ) ^ 2)
      (fun p _ => by positivity)
      (fun p hp => by
        have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
        rw [div_le_one (by positivity)]; nlinarith)
    refine le_trans ?_ hw
    have hsum_le : ∑ p ∈ Podd, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 2 := by
      have hsub : Podd ⊆ Finset.Icc 3 y := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hr, hpr, hp2⟩
        rw [Finset.mem_range] at hr
        have h2 := hpr.two_le
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have h1 : ∑ p ∈ Podd, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ k ∈ Finset.Icc 3 y, (1 : ℝ) / (k : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
      have h2 : ∑ k ∈ Finset.Icc 3 y, (1 : ℝ) / (k : ℝ) ^ 2 ≤
          ∑ k ∈ Finset.Icc 3 y, ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        have hdiff : (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) = 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
          field_simp [show (k : ℝ) ≠ 0 by linarith, show (k : ℝ) - 1 ≠ 0 by linarith]; ring
        rw [hdiff]
        exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
      have htele : ∀ n : ℕ, 2 ≤ n →
          ∑ k ∈ Finset.Icc 3 n, ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) = 1 / 2 - 1 / (n : ℝ) := by
        intro n hn
        induction n with
        | zero => omega
        | succ m ihm =>
          by_cases hm : m = 1
          · subst hm; simp
          · have hm2 : 2 ≤ m := by omega
            rw [show Finset.Icc 3 (m + 1) = insert (m + 1) (Finset.Icc 3 m) from by
              ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
            rw [Finset.sum_insert (by simp), ihm hm2]
            push_cast
            ring
      have h3 := htele y (by omega)
      have hy_pos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
      linarith [h1, h2, h3, div_pos one_pos hy_pos]
    linarith
  have hfactor : ∀ p ∈ Podd, (1 + (1 : ℝ) / p) = (1 - (1 : ℝ) / (p : ℝ) ^ 2) * (1 - (1 : ℝ) / p)⁻¹ := by
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
    have hne : (1 - (1 : ℝ) / p) ≠ 0 := by
      have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by positivity)]; linarith
      linarith
    have hdiff : (1 - (1 : ℝ) / (p : ℝ) ^ 2) = (1 + (1 : ℝ) / p) * (1 - (1 : ℝ) / p) := by ring
    rw [hdiff, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib]
  have hsplit : ∏ p ∈ Pall, (1 - (1 : ℝ) / p)⁻¹ = 2 * ∏ p ∈ Podd, (1 - (1 : ℝ) / p)⁻¹ := by
    rw [hPodd_eq, ← Finset.mul_prod_erase Pall (fun p => (1 - (1 : ℝ) / p)⁻¹) h2mem]
    norm_num
  have hharm : Real.log (y : ℝ) ≤ ∏ p ∈ Pall, (1 - (1 : ℝ) / p)⁻¹ := by
    have h1 : Real.log (y : ℝ) ≤ Real.log ((y : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by linarith)
    exact h1.trans ((log_succ_le_harmonic y).trans (harmonic_le_prod_inv_one_sub y))
  have hodd_inv : (1 / 2 : ℝ) * Real.log (y : ℝ) ≤ ∏ p ∈ Podd, (1 - (1 : ℝ) / p)⁻¹ := by
    linarith
  have hlog_nonneg : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y))
  have hprod_nonneg : 0 ≤ ∏ p ∈ Podd, (1 - (1 : ℝ) / p)⁻¹ :=
    Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
      have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by positivity)]; linarith
      exact inv_nonneg.mpr (by linarith)
  nlinarith

/-- Product of odd primes <= y is at most 4^y. -/
private lemma prod_odd_primes_le_four_pow (y : ℕ) :
    ∏ p ∈ ((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≠ 2)), p ≤ 4 ^ y := by
  have hsub : (Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≠ 2) ⊆
      (Finset.range (y + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hle : ∏ p ∈ ((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≠ 2)), p ≤
      ∏ p ∈ ((Finset.range (y + 1)).filter Nat.Prime), p :=
    Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _ => (Finset.mem_filter.mp hp).2.one_le)
  exact hle.trans (by simpa [primorial] using primorial_le_4_pow y)

end AnalyticBounds

section Geometry

/-- Geometric realization: if m^3 <= n, M <= m / 2, r > 0, and V is the set of triples
(a, b, c) in [0, M)^3 with a^2 + b^2 + c^2 = r, then (m / 2)^3 * V.card <= Erdos1085.f 3 n. -/
private lemma grid_unit_dist_lower_bound (n m M r : ℕ) (hmn : m ^ 3 ≤ n) (hMm : M ≤ m / 2)
    (hr : 0 < r) :
    (m / 2) ^ 3 *
      (((Finset.range M) ×ˢ (Finset.range M) ×ˢ (Finset.range M)).filter
        (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)).card ≤
      Erdos1085.f 3 n := by
  classical
  have hsr_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  let g : Fin m × Fin m × Fin m → (ℝ^ 3) := fun x =>
    WithLp.toLp 2 ![((x.1 : ℕ) : ℝ) / Real.sqrt r,
                    ((x.2.1 : ℕ) : ℝ) / Real.sqrt r,
                    ((x.2.2 : ℕ) : ℝ) / Real.sqrt r]
  have hg_inj : Function.Injective g := by
    intro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h
    have h0 : ((a₁ : ℕ) : ℝ) / Real.sqrt r = ((a₂ : ℕ) : ℝ) / Real.sqrt r :=
      congrArg (fun z : ℝ^ 3 => z 0) h
    have h1 : ((b₁ : ℕ) : ℝ) / Real.sqrt r = ((b₂ : ℕ) : ℝ) / Real.sqrt r :=
      congrArg (fun z : ℝ^ 3 => z 1) h
    have h2 : ((c₁ : ℕ) : ℝ) / Real.sqrt r = ((c₂ : ℕ) : ℝ) / Real.sqrt r :=
      congrArg (fun z : ℝ^ 3 => z 2) h
    have ha : (a₁ : ℕ) = (a₂ : ℕ) := by
      exact_mod_cast div_left_inj' (ne_of_gt hsr_pos) |>.mp h0
    have hb : (b₁ : ℕ) = (b₂ : ℕ) := by
      exact_mod_cast div_left_inj' (ne_of_gt hsr_pos) |>.mp h1
    have hc : (c₁ : ℕ) = (c₂ : ℕ) := by
      exact_mod_cast div_left_inj' (ne_of_gt hsr_pos) |>.mp h2
    exact Prod.ext (Fin.ext ha) (Prod.ext (Fin.ext hb) (Fin.ext hc))
  let G : Finset (ℝ^ 3) := Finset.univ.image g
  have hG_card : G.card = m ^ 3 := by
    rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ]
    simp [pow_three]
  obtain ⟨S, hGS, hS_card⟩ := Infinite.exists_superset_card_eq G n (by omega)
  set V := ((Finset.range M) ×ˢ (Finset.range M) ×ˢ (Finset.range M)).filter
    (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)
  set Half := (Finset.range (m / 2)) ×ˢ (Finset.range (m / 2)) ×ˢ (Finset.range (m / 2))
  have hHalf_card : Half.card = (m / 2) ^ 3 := by
    simp [Half, Finset.card_product, pow_three]
  have hpair_le : (Half ×ˢ V).card ≤ unitDistNum S := by
    unfold unitDistNum
    let mkPt : (ℕ × ℕ × ℕ) → (ℝ^ 3) := fun x =>
      WithLp.toLp 2 ![((x.1 : ℕ) : ℝ) / Real.sqrt r,
                      ((x.2.1 : ℕ) : ℝ) / Real.sqrt r,
                      ((x.2.2 : ℕ) : ℝ) / Real.sqrt r]
    have hmk_inj : Function.Injective mkPt := by
      intro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h
      have h0 : ((a₁ : ℕ) : ℝ) / Real.sqrt r = ((a₂ : ℕ) : ℝ) / Real.sqrt r :=
        congrArg (fun z : ℝ^ 3 => z 0) h
      have h1 : ((b₁ : ℕ) : ℝ) / Real.sqrt r = ((b₂ : ℕ) : ℝ) / Real.sqrt r :=
        congrArg (fun z : ℝ^ 3 => z 1) h
      have h2 : ((c₁ : ℕ) : ℝ) / Real.sqrt r = ((c₂ : ℕ) : ℝ) / Real.sqrt r :=
        congrArg (fun z : ℝ^ 3 => z 2) h
      have ha : a₁ = a₂ := by exact_mod_cast div_left_inj' (ne_of_gt hsr_pos) |>.mp h0
      have hb : b₁ = b₂ := by exact_mod_cast div_left_inj' (ne_of_gt hsr_pos) |>.mp h1
      have hc : c₁ = c₂ := by exact_mod_cast div_left_inj' (ne_of_gt hsr_pos) |>.mp h2
      exact Prod.ext ha (Prod.ext hb hc)
    let φ : ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) → Sym2 (ℝ^ 3) := fun xv =>
      s(mkPt xv.1, mkPt (xv.1.1 + xv.2.1, xv.1.2.1 + xv.2.2.1, xv.1.2.2 + xv.2.2.2))
    apply Finset.card_le_card_of_injOn φ
    · intro ⟨⟨x₁, x₂, x₃⟩, ⟨a, b, c⟩⟩ hxv
      rcases Finset.mem_product.mp hxv with ⟨hx, hv⟩
      simp only [Half, Finset.mem_product, Finset.mem_range] at hx
      simp only [V, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hv
      have hx1 : x₁ < m := by omega
      have hx2 : x₂ < m := by omega
      have hx3 : x₃ < m := by omega
      have hy1 : x₁ + a < m := by omega
      have hy2 : x₂ + b < m := by omega
      have hy3 : x₃ + c < m := by omega
      have hp1 : mkPt (x₁, x₂, x₃) ∈ S :=
        hGS (Finset.mem_image.mpr ⟨(⟨x₁, hx1⟩, ⟨x₂, hx2⟩, ⟨x₃, hx3⟩), Finset.mem_univ _, rfl⟩)
      have hp2 : mkPt (x₁ + a, x₂ + b, x₃ + c) ∈ S :=
        hGS (Finset.mem_image.mpr ⟨(⟨x₁ + a, hy1⟩, ⟨x₂ + b, hy2⟩, ⟨x₃ + c, hy3⟩), Finset.mem_univ _, rfl⟩)
      have hdist : dist (mkPt (x₁, x₂, x₃)) (mkPt (x₁ + a, x₂ + b, x₃ + c)) = 1 := by
        have hsq : dist (mkPt (x₁, x₂, x₃)) (mkPt (x₁ + a, x₂ + b, x₃ + c)) ^ 2 = 1 := by
          rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
          change ((x₁ : ℝ) / Real.sqrt r - ((x₁ + a : ℕ) : ℝ) / Real.sqrt r) ^ 2 +
            ((x₂ : ℝ) / Real.sqrt r - ((x₂ + b : ℕ) : ℝ) / Real.sqrt r) ^ 2 +
            ((x₃ : ℝ) / Real.sqrt r - ((x₃ + c : ℕ) : ℝ) / Real.sqrt r) ^ 2 = 1
          push_cast
          have hr_eq : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 = (r : ℝ) := by
            exact_mod_cast hv.2
          have hsr_sq : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt (by positivity)
          have hsr_ne : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt hsr_pos
          field_simp [hsr_ne]
          calc ((x₁ : ℝ) - ((x₁ : ℝ) + (a : ℝ))) ^ 2 +
               ((x₂ : ℝ) - ((x₂ : ℝ) + (b : ℝ))) ^ 2 +
               ((x₃ : ℝ) - ((x₃ : ℝ) + (c : ℝ))) ^ 2
              = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 := by ring
            _ = (r : ℝ) := hr_eq
            _ = Real.sqrt (r : ℝ) ^ 2 := hsr_sq.symm
        nlinarith [dist_nonneg (x := mkPt (x₁, x₂, x₃)) (y := mkPt (x₁ + a, x₂ + b, x₃ + c))]
      refine Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr ⟨hp1, hp2⟩, ?_⟩
      have hout := Quot.out_eq (φ ((x₁, x₂, x₃), (a, b, c)))
      change s((Quot.out (φ ((x₁, x₂, x₃), (a, b, c)))).1,
        (Quot.out (φ ((x₁, x₂, x₃), (a, b, c)))).2) = _ at hout
      rcases Sym2.eq_iff.mp hout with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]; exact hdist
      · rw [h₁, h₂, dist_comm]; exact hdist
    · intro ⟨⟨x₁, x₂, x₃⟩, ⟨a, b, c⟩⟩ h1 ⟨⟨x₁', x₂', x₃'⟩, ⟨a', b', c'⟩⟩ h2 heq
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have h1' := hmk_inj ha
        have h2' := hmk_inj hb
        dsimp only at h1' h2'
        simp only [Prod.mk.injEq] at h1' h2'
        rcases h1' with ⟨hx1e, hx2e, hx3e⟩
        rcases h2' with ⟨hy1e, hy2e, hy3e⟩
        refine Prod.ext (Prod.ext hx1e (Prod.ext hx2e hx3e)) ?_
        refine Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) (by dsimp only; omega))
      · exfalso
        have h1' := hmk_inj ha
        have h2' := hmk_inj hb
        dsimp only at h1' h2'
        simp only [Prod.mk.injEq] at h1' h2'
        rcases h1' with ⟨hx1e, hx2e, hx3e⟩
        rcases h2' with ⟨hy1e, hy2e, hy3e⟩
        have ha0 : a = 0 := by omega
        have hb0 : b = 0 := by omega
        have hc0 : c = 0 := by omega
        rcases Finset.mem_product.mp h1 with ⟨_, hv⟩
        simp only [V, Finset.mem_filter] at hv
        rw [ha0, hb0, hc0] at hv
        omega
  rw [Finset.card_product, hHalf_card] at hpair_le
  refine hpair_le.trans ?_
  unfold Erdos1085.f
  refine le_ciSup₂ (f := fun (T : Finset (ℝ^ 3)) (_ : T.card = n) => unitDistNum T) ?_ S hS_card
  refine ⟨n.choose 2, ?_⟩
  intro k hk
  rcases Set.mem_iUnion.mp hk with ⟨T, hT⟩
  obtain ⟨hcard, rfl⟩ := Set.mem_range.mp hT
  simpa only [hcard] using unitDistNum_le_choose_two T

end Geometry

end OMA

theorem OMA.solution : type_of% @Erdos1085.erdos_1085.variants.lower_d3 := by
  classical
  have hev : ∀ᶠ n : ℕ in atTop,
      (1 / 50000 : ℝ) * ((n : ℝ) ^ (4 / 3 : ℝ) * Real.log (Real.log (n : ℝ))) ≤
        (Erdos1085.f 3 n : ℝ) := by
    have hlog4 : Real.log 4 / 4 < 1 / 2 := by
      have h4 : (4 : ℝ) < Real.exp 2 := by
        have h1 : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      have hlt : Real.log 4 < 2 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]; exact h4
      linarith
    have hexp_dom : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ ((Real.log 4 / 4) * (1 / 3 : ℝ)) ≤ (1 / 16 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hsub : (0 : ℝ) < (1 / 3 : ℝ) - (Real.log 4 / 4) * (1 / 3 : ℝ) := by nlinarith
      have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 / 3 : ℝ) - (Real.log 4 / 4) * (1 / 3 : ℝ)))
          atTop atTop :=
        (tendsto_rpow_atTop hsub).comp tendsto_natCast_atTop_atTop
      filter_upwards [htend.eventually_ge_atTop 16, eventually_ge_atTop 1] with n hn hn1
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hmul : (n : ℝ) ^ ((Real.log 4 / 4) * (1 / 3 : ℝ)) *
          (n : ℝ) ^ ((1 / 3 : ℝ) - (Real.log 4 / 4) * (1 / 3 : ℝ)) = (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hn_pos]; ring_nf
      have hp_pos : 0 < (n : ℝ) ^ ((Real.log 4 / 4) * (1 / 3 : ℝ)) := Real.rpow_pos_of_pos hn_pos _
      nlinarith
    have hlog_dom : ∀ᶠ n : ℕ in atTop,
        16 ≤ Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) / 4 ∧
        (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
          Real.log (Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) / 8) := by
      have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      filter_upwards [hlogn.eventually_ge_atTop 2000, eventually_ge_atTop 100] with n hln hn100
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlog_half : Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) = (1 / 3 : ℝ) * Real.log (n : ℝ) - Real.log 2 := by
        rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hn_pos _)) (by norm_num),
          Real.log_rpow hn_pos]
      have hlog2_lt : Real.log 2 < 1 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        exact lt_trans (by norm_num) Real.exp_one_gt_d9
      have h1 : 16 ≤ Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) / 4 := by
        rw [hlog_half]; linarith
      have h2 : (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
          Real.log (Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) / 8) := by
        have harg : (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) / 8 := by
          have hlin : (1 / 4 : ℝ) * Real.log (n : ℝ) ≤ Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) := by
            rw [hlog_half]; linarith
          have hsq : Real.sqrt (Real.log (n : ℝ)) ≤ (1 / 32 : ℝ) * Real.log (n : ℝ) := by
            have hnn : 0 ≤ Real.log (n : ℝ) := by linarith
            rw [Real.sqrt_le_iff]
            exact ⟨by positivity, by nlinarith⟩
          have hrp : (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt (Real.log (n : ℝ)) := by
            rw [Real.sqrt_eq_rpow]
          rw [hrp]; linarith
        have hpos1 : 0 < (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
        calc (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ))
            = Real.log ((Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) :=
              (Real.log_rpow (by linarith : (0 : ℝ) < Real.log (n : ℝ)) (1 / 2 : ℝ)).symm
          _ ≤ Real.log (Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) / 8) := Real.log_le_log hpos1 harg
      exact ⟨h1, h2⟩
    filter_upwards [hexp_dom, hlog_dom, eventually_ge_atTop (1000 : ℕ)] with n hexp hlog hn1000
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hcube_ge : (10 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      have h10 : (10 : ℝ) ^ (3 : ℝ) = 1000 := by norm_num
      have hle : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1000
      calc (10 : ℝ) = ((10 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by norm_num)]; norm_num
        _ = (1000 : ℝ) ^ (1 / 3 : ℝ) := by rw [h10]
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hle (by norm_num)
    set m : ℕ := Nat.floor ((n : ℝ) ^ (1 / 3 : ℝ))
    have hm_le : (m : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
    have hm_gt : (n : ℝ) ^ (1 / 3 : ℝ) - 1 < (m : ℝ) := by
      have := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 3 : ℝ)); linarith
    have hm_ge_half : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (m : ℝ) := by linarith
    have hm3_le : m ^ 3 ≤ n := by
      have h3 : (m : ℝ) ^ 3 ≤ (n : ℝ) := by
        calc (m : ℝ) ^ 3 = (m : ℝ) ^ (3 : ℝ) := by norm_cast
          _ ≤ ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg m) hm_le (by norm_num)
          _ = (n : ℝ) := by rw [← Real.rpow_mul (le_of_lt hn_pos)]; norm_num
      exact_mod_cast h3
    have hm_ge10 : 10 ≤ m := by
      have : (10 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.le_floor hcube_ge
      exact_mod_cast this
    set y : ℕ := Nat.floor (Real.log (m : ℝ) / 4)
    have hy_ge16 : 16 ≤ y := by
      have hlog_m : Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by positivity) hm_ge_half
      have h16 : (16 : ℝ) ≤ Real.log (m : ℝ) / 4 := by linarith [hlog.1]
      exact Nat.le_floor h16
    have hy_le : (y : ℝ) ≤ Real.log (m : ℝ) / 4 := Nat.floor_le (by linarith [hlog.1, Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ (1 / 3 : ℝ) / 2) hm_ge_half])
    have hy_ge_half : Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) / 8 ≤ (y : ℝ) := by
      have hlog_m : Real.log ((n : ℝ) ^ (1 / 3 : ℝ) / 2) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by positivity) hm_ge_half
      have hlt : Real.log (m : ℝ) / 4 - 1 < (y : ℝ) := by
        have := Nat.lt_floor_add_one (Real.log (m : ℝ) / 4); linarith
      linarith [hlog.1]
    set Podd := (Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
    have hPodd : ∀ p ∈ Podd, p.Prime ∧ p ≠ 2 := fun p hp => (Finset.mem_filter.mp hp).2
    set Q := ∏ p ∈ Podd, p
    have hQ3 : 3 ≤ Q := by
      have h3mem : 3 ∈ Podd := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_three, by norm_num⟩
      have hle : 3 ≤ ∏ p ∈ Podd, p := by
        rw [← Finset.mul_prod_erase Podd (fun p => p) h3mem]
        have hpos : 1 ≤ ∏ p ∈ Podd.erase 3, p :=
          Finset.one_le_prod' fun p hp => (hPodd p (Finset.mem_of_mem_erase hp)).1.one_le
        exact le_mul_of_one_le_right (by norm_num) hpos
      exact hle
    have hQ_le : (Q : ℝ) ≤ (m : ℝ) / 8 := by
      have hQ4 : (Q : ℝ) ≤ (4 : ℝ) ^ y := by exact_mod_cast OMA.prod_odd_primes_le_four_pow y
      have h4_rpow : (4 : ℝ) ^ y ≤ (n : ℝ) ^ ((Real.log 4 / 4) * (1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast]
        have h1 : (4 : ℝ) ^ (y : ℝ) ≤ (4 : ℝ) ^ (Real.log (m : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hy_le
        have h2 : (4 : ℝ) ^ (Real.log (m : ℝ) / 4) = (m : ℝ) ^ (Real.log 4 / 4) := by
          have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_def_of_pos hm_pos]
          congr 1; ring
        have h3 : (m : ℝ) ^ (Real.log 4 / 4) ≤ ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (Real.log 4 / 4) :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) hm_le (by positivity)
        have h4 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (Real.log 4 / 4) =
            (n : ℝ) ^ ((Real.log 4 / 4) * (1 / 3 : ℝ)) := by
          rw [← Real.rpow_mul (le_of_lt hn_pos)]; ring_nf
        linarith
      linarith
    set k := (m / 2) / Q
    have hQ_le_nat : Q ≤ m / 8 := by
      have : (Q : ℝ) ≤ (m : ℝ) / 8 := hQ_le
      have h8 : 8 * Q ≤ m := by
        have : (8 * Q : ℝ) ≤ (m : ℝ) := by linarith
        exact_mod_cast this
      omega
    have hk_ge1 : 1 ≤ k := by
      dsimp [k]
      exact Nat.div_pos (by omega) (by omega)
    set M := k * Q
    have hMm : M ≤ m / 2 := Nat.div_mul_le_self (m / 2) Q
    have hM_ge : (m : ℝ) / 4 ≤ (M : ℝ) := by
      have hdiv : m / 2 < (k + 1) * Q := by
        dsimp [k]
        have := Nat.lt_div_mul_add (a := m / 2) (b := Q) (by omega)
        linarith
      have hM_nat : m / 2 - Q ≤ M := by
        have hMQ : (k + 1) * Q = M + Q := by dsimp [M]; ring
        omega
      have h1 : ((m / 2 : ℕ) : ℝ) - (Q : ℝ) ≤ (M : ℝ) := by
        have : m / 2 ≤ M + Q := by omega
        have hcast : ((m / 2 : ℕ) : ℝ) ≤ (M : ℝ) + (Q : ℝ) := by exact_mod_cast this
        linarith
      have h2 : (m : ℝ) / 2 - 1 ≤ ((m / 2 : ℕ) : ℝ) := by
        have : m ≤ 2 * (m / 2) + 1 := by omega
        have hcast : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
        linarith
      have hm10R : (10 : ℝ) ≤ m := by exact_mod_cast hm_ge10
      linarith
    obtain ⟨r, hr_pos, _, hr_reps⟩ := OMA.exists_radius_many_reps Podd hPodd hQ3 k hk_ge1
    have hgeom := OMA.grid_unit_dist_lower_bound n m M r hm3_le hMm hr_pos
    have hgeomR : (((m / 2 : ℕ) : ℝ) ^ 3) *
        ((((Finset.range M) ×ˢ (Finset.range M) ×ˢ (Finset.range M)).filter
          (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)).card : ℝ) ≤
        (Erdos1085.f 3 n : ℝ) := by
      exact_mod_cast hgeom
    have hprod_id : ((k : ℝ) / 3) * ∏ p ∈ Podd, ((p : ℝ) + 1) =
        ((M : ℝ) / 3) * ∏ p ∈ Podd, (1 + (1 : ℝ) / p) := by
      have hfactor : ∀ p ∈ Podd, ((p : ℝ) + 1) = (p : ℝ) * (1 + (1 : ℝ) / p) := by
        intro p hp
        have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (hPodd p hp).1.ne_zero
        field_simp [hp_ne]
      rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib]
      have hQcast : (∏ p ∈ Podd, (p : ℝ)) = (Q : ℝ) := by simp [Q]
      rw [hQcast]
      have hMcast : (M : ℝ) = (k : ℝ) * (Q : ℝ) := by simp [M]
      rw [hMcast]; ring
    rw [hprod_id] at hr_reps
    have hprod_lb : (1 / 4 : ℝ) * Real.log (y : ℝ) ≤ ∏ p ∈ Podd, (1 + (1 : ℝ) / p) :=
      OMA.quarter_log_le_prod_odd_primes y (by omega)
    have hlog_y : (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) ≤ Real.log (y : ℝ) :=
      hlog.2.trans (Real.log_le_log (by linarith [hlog.1]) hy_ge_half)
    have hm_half_lb : (n : ℝ) ^ (1 / 3 : ℝ) / 6 ≤ ((m / 2 : ℕ) : ℝ) := by
      have : m ≤ 2 * (m / 2) + 1 := by omega
      have hcast : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hM_lb : (n : ℝ) ^ (1 / 3 : ℝ) / 8 ≤ (M : ℝ) := by linarith
    have hn13_pos : 0 < (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
    have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
      have : (1 : ℝ) ≤ Real.log (n : ℝ) := by
        have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
        have h3 : Real.exp 1 ≤ (n : ℝ) := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
        exact (Real.le_log_iff_exp_le hn_pos).mpr h3
      exact Real.log_nonneg this
    have hr_reps_lb :
        ((n : ℝ) ^ (1 / 3 : ℝ) / 24) * ((1 / 8 : ℝ) * Real.log (Real.log (n : ℝ))) ≤
        ((((Finset.range M) ×ˢ (Finset.range M) ×ˢ (Finset.range M)).filter
          (fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = r)).card : ℝ) := by
      have h1 : (1 / 8 : ℝ) * Real.log (Real.log (n : ℝ)) ≤ ∏ p ∈ Podd, (1 + (1 : ℝ) / p) := by
        linarith
      have h2 : (n : ℝ) ^ (1 / 3 : ℝ) / 24 ≤ (M : ℝ) / 3 := by linarith
      exact le_trans (mul_le_mul h2 h1 (by positivity) (by positivity)) hr_reps
    have hcube_lb : ((n : ℝ) ^ (1 / 3 : ℝ) / 6) ^ 3 ≤ ((m / 2 : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hm_half_lb 3
    have h43 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 * (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hn_pos), ← Real.rpow_add hn_pos]
      norm_num
    have hcomb :
        (((n : ℝ) ^ (1 / 3 : ℝ) / 6) ^ 3) *
          (((n : ℝ) ^ (1 / 3 : ℝ) / 24) * ((1 / 8 : ℝ) * Real.log (Real.log (n : ℝ)))) ≤
        (Erdos1085.f 3 n : ℝ) :=
      (mul_le_mul hcube_lb hr_reps_lb (by positivity) (by positivity)).trans hgeomR
    have hsimp :
        (((n : ℝ) ^ (1 / 3 : ℝ) / 6) ^ 3) *
          (((n : ℝ) ^ (1 / 3 : ℝ) / 24) * ((1 / 8 : ℝ) * Real.log (Real.log (n : ℝ)))) =
        (1 / 41472 : ℝ) * ((n : ℝ) ^ (4 / 3 : ℝ) * Real.log (Real.log (n : ℝ))) := by
      calc (((n : ℝ) ^ (1 / 3 : ℝ) / 6) ^ 3) *
            (((n : ℝ) ^ (1 / 3 : ℝ) / 24) * ((1 / 8 : ℝ) * Real.log (Real.log (n : ℝ))))
          = (1 / 41472 : ℝ) * ((((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 * (n : ℝ) ^ (1 / 3 : ℝ)) *
              Real.log (Real.log (n : ℝ))) := by ring
        _ = (1 / 41472 : ℝ) * ((n : ℝ) ^ (4 / 3 : ℝ) * Real.log (Real.log (n : ℝ))) := by rw [h43]
    rw [hsimp] at hcomb
    have hnn : 0 ≤ (n : ℝ) ^ (4 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) := by positivity
    linarith
  rw [Asymptotics.isBigO_iff]
  refine ⟨50000, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 10] with n hn hn10
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
    have h3 : Real.exp 1 ≤ (n : ℝ) := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
    exact Real.log_nonneg ((Real.le_log_iff_exp_le hn_pos).mpr h3)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  linarith
