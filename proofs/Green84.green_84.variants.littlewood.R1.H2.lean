import OMAReductions.R_Green84_green_84_variants_littlewood_R1
import Mathlib

/-!
# Signed interval packing on the circle (`Green84.green_84.variants.littlewood.R1.H2`)

Reduces dimension to 2 via base-B projection, discretizes Z/NZ into slots of length L with
uniform Fin Q coloring choosing signed type and shift, bounds total excess degree by finite
second moment, trims excess edges, and applies the Rodl nibble matching theorem
(nibble section adapted from @preternatural-tocsin in Erdos81.erdos_81.R1.H2).
-/


namespace Green84H2Nibble
open Finset

lemma one_sub_mul_le_pow {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * p ≤ (1 - p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ]
    have h1 : (1 - (k : ℝ) * p) * (1 - p) ≤ (1 - p) ^ k * (1 - p) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg p)]

lemma pow_mul_one_add_le_one {ε : ℝ} (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (T : ℕ) :
    (1 - ε) ^ T * (1 + (T : ℝ) * ε) ≤ 1 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [pow_succ, Nat.cast_succ]
    have h1 : (1 - ε) * (1 + ((T : ℝ) + 1) * ε) ≤ 1 + (T : ℝ) * ε := by
      nlinarith [mul_nonneg (Nat.cast_nonneg T) (sq_nonneg ε), sq_nonneg ε]
    have h2 : (1 - ε) ^ T * ((1 - ε) * (1 + ((T : ℝ) + 1) * ε)) ≤
        (1 - ε) ^ T * (1 + (T : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) T)
    linarith

lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have hx : |x| ≤ 1 := by rwa [abs_of_nonneg hx0]
  have h := Real.exp_bound hx (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
    Nat.succ_eq_add_one, Nat.factorial_two, Nat.cast_ofNat] at h
  push_cast at h
  have h1 : Real.exp x - (1 + x) ≤ |x| ^ 2 * ((3 : ℝ) / (2 * 2)) := (abs_le.mp h).2
  rw [sq_abs] at h1
  nlinarith

lemma inv_one_sub_pow_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (k : ℕ)
    (hk : 2 * (k : ℝ) * p ≤ 1) :
    ((1 - p) ^ k)⁻¹ ≤ 1 + 4 * (k : ℝ) * p := by
  have h1p : 0 < 1 - p := by linarith
  have hinv : (1 - p)⁻¹ ≤ Real.exp (2 * p) := by
    have h1 : (1 - p)⁻¹ ≤ 1 + 2 * p := by
      rw [inv_le_iff_one_le_mul₀ h1p]
      nlinarith
    exact h1.trans (by linarith [Real.add_one_le_exp (2 * p)])
  calc ((1 - p) ^ k)⁻¹ = ((1 - p)⁻¹) ^ k := (inv_pow (1 - p) k).symm
    _ ≤ (Real.exp (2 * p)) ^ k := pow_le_pow_left₀ (inv_nonneg.mpr h1p.le) hinv k
    _ = Real.exp ((k : ℝ) * (2 * p)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (2 * (k : ℝ) * p) := by congr 1; ring
    _ ≤ 1 + 2 * (2 * (k : ℝ) * p) := exp_le_one_add_two_mul (by positivity) hk
    _ = 1 + 4 * (k : ℝ) * p := by ring

lemma abs_pow_sub_pow_le {a b : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (k : ℕ) : |a ^ k - b ^ k| ≤ (k : ℝ) * (2 : ℝ) ^ k * |a - b| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, pow_succ, Nat.cast_succ]
    have hsplit : a ^ k * a - b ^ k * b = (a ^ k - b ^ k) * a + b ^ k * (a - b) := by ring
    rw [hsplit]
    have hbk : b ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ hb0 hb2 k
    calc |(a ^ k - b ^ k) * a + b ^ k * (a - b)|
        ≤ |(a ^ k - b ^ k) * a| + |b ^ k * (a - b)| := abs_add_le _ _
      _ = |a ^ k - b ^ k| * a + b ^ k * |a - b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (pow_nonneg hb0 k)]
      _ ≤ ((k : ℝ) * (2 : ℝ) ^ k * |a - b|) * 2 + (2 : ℝ) ^ k * |a - b| :=
          add_le_add (mul_le_mul ih ha2 ha0 (by positivity))
            (mul_le_mul_of_nonneg_right hbk (abs_nonneg _))
      _ ≤ ((k : ℝ) + 1) * ((2 : ℝ) ^ k * 2) * |a - b| := by
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k, abs_nonneg (a - b)]

lemma bern_sum_one {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    ∑ ω : ι → Bool, (∏ e : ι, if ω e then p else 1 - p) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : ι) (b : Bool) ↦ if b then p else 1 - p)]
  simp

lemma bern_sum_all_false {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (A : Finset ι) :
    ∑ ω ∈ (Finset.univ : Finset (ι → Bool)).filter (fun ω ↦ ∀ e ∈ A, ω e = false),
      (∏ e : ι, if ω e then p else 1 - p) = (1 - p) ^ A.card := by
  let g : ι → Bool → ℝ := fun e b ↦ if e ∈ A then (if b = false then 1 else 0) else 1
  have hrew : ∀ ω : ι → Bool,
      (if (∀ e ∈ A, ω e = false) then (∏ e : ι, if ω e then p else 1 - p) else 0) =
        ∏ e : ι, ((if ω e then p else 1 - p) * g e (ω e)) := by
    intro ω
    rw [Finset.prod_mul_distrib]
    by_cases h : ∀ e ∈ A, ω e = false
    · rw [if_pos h]
      have hg : ∏ e : ι, g e (ω e) = 1 := Finset.prod_eq_one fun e _ ↦ by
        simp only [g]; split_ifs with he hb
        · rfl
        · exact absurd (h e he) hb
        · rfl
      rw [hg, mul_one]
    · rw [if_neg h]
      push Not at h
      obtain ⟨e₀, he₀A, he₀⟩ := h
      have hg : ∏ e : ι, g e (ω e) = 0 :=
        Finset.prod_eq_zero (mem_univ e₀) (by simp [g, he₀A, he₀])
      rw [hg, mul_zero]
  rw [Finset.sum_filter]
  simp_rw [hrew]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  have hterm : ∀ e : ι, ∑ b : Bool, (if b then p else 1 - p) * g e b =
      if e ∈ A then 1 - p else 1 := by
    intro e
    by_cases he : e ∈ A <;> simp [g, he]
  simp_rw [hterm]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 2
  ext e; simp

lemma bern_sum_one_true_rest_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (e₀ : ι) (A : Finset ι) (he₀ : e₀ ∉ A) :
    ∑ ω ∈ (Finset.univ : Finset (ι → Bool)).filter
        (fun ω ↦ ω e₀ = true ∧ ∀ e ∈ A, ω e = false),
      (∏ e : ι, if ω e then p else 1 - p) = p * (1 - p) ^ A.card := by
  let g : ι → Bool → ℝ := fun e b ↦
    if e = e₀ then (if b = true then 1 else 0)
    else if e ∈ A then (if b = false then 1 else 0) else 1
  have hrew : ∀ ω : ι → Bool,
      (if (ω e₀ = true ∧ ∀ e ∈ A, ω e = false) then (∏ e : ι, if ω e then p else 1 - p) else 0) =
        ∏ e : ι, ((if ω e then p else 1 - p) * g e (ω e)) := by
    intro ω
    rw [Finset.prod_mul_distrib]
    by_cases h : ω e₀ = true ∧ ∀ e ∈ A, ω e = false
    · rw [if_pos h]
      have hg : ∏ e : ι, g e (ω e) = 1 := Finset.prod_eq_one fun e _ ↦ by
        simp only [g]; split_ifs with h1 h2 h3 h4
        · rfl
        · subst h1; exact absurd h.1 h2
        · rfl
        · exact absurd (h.2 e h3) h4
        · rfl
      rw [hg, mul_one]
    · rw [if_neg h]
      by_cases h0 : ω e₀ = true
      · have hnot : ¬(∀ e ∈ A, ω e = false) := fun ha ↦ h ⟨h0, ha⟩
        push Not at hnot
        obtain ⟨e₁, he₁A, he₁⟩ := hnot
        have hne : e₁ ≠ e₀ := fun heq ↦ he₀ (heq ▸ he₁A)
        have hg : ∏ e : ι, g e (ω e) = 0 :=
          Finset.prod_eq_zero (mem_univ e₁) (by simp [g, hne, he₁A, he₁])
        rw [hg, mul_zero]
      · have hg : ∏ e : ι, g e (ω e) = 0 :=
          Finset.prod_eq_zero (mem_univ e₀) (by simp [g, h0])
        rw [hg, mul_zero]
  rw [Finset.sum_filter]
  simp_rw [hrew]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  have hterm : ∀ e : ι, ∑ b : Bool, (if b then p else 1 - p) * g e b =
      if e = e₀ then p else if e ∈ A then 1 - p else 1 := by
    intro e
    by_cases h1 : e = e₀
    · simp [g, h1]
    · by_cases h2 : e ∈ A <;> simp [g, h1, h2]
  simp_rw [hterm]
  rw [← Finset.mul_prod_erase Finset.univ _ (mem_univ e₀), if_pos rfl]
  congr 1
  have hrest : ∀ e ∈ Finset.univ.erase e₀,
      (if e = e₀ then p else if e ∈ A then 1 - p else 1) = if e ∈ A then 1 - p else 1 := by
    intro e he; rw [if_neg (mem_erase.mp he).1]
  rw [Finset.prod_congr rfl hrest, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  congr 2
  ext e
  simp only [mem_filter, mem_erase, mem_univ, and_true]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun heq ↦ he₀ (heq ▸ h), h⟩⟩

/- ### Section 2: Prime-Field Affine-Line Hypergraph Regularization -/

lemma regularize_hypergraph {α : Type*} [DecidableEq α]
    (U : Finset α) (ℰ : Finset (Finset α)) (r D Δ₂ : ℕ)
    (hr : 2 ≤ r) (_hD : 1 ≤ D)
    (hunif : ∀ e ∈ ℰ, e ⊆ U ∧ e.card = r)
    (hdeg : ∀ x ∈ U, (ℰ.filter (fun e ↦ x ∈ e)).card ≤ D)
    (hcodeg : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card ≤ Δ₂) :
    ∃ (p_prime : ℕ) (_ : Fact p_prime.Prime),
      let W : Finset (Fin r × ZMod p_prime) := Finset.univ
      ∃ (ℰ_orig ℰ_reg : Finset (Finset ((Fin r × ZMod p_prime) × α))),
        ℰ_orig ⊆ ℰ_reg ∧
        (∀ e ∈ ℰ_reg, e ⊆ W ×ˢ U ∧ e.card = r) ∧
        (∀ v ∈ W ×ˢ U, (ℰ_reg.filter (fun e ↦ v ∈ e)).card = D) ∧
        (∀ v₁ ∈ W ×ˢ U, ∀ v₂ ∈ W ×ˢ U, v₁ ≠ v₂ →
          (ℰ_reg.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card ≤ max Δ₂ 1) ∧
        ℰ_orig.card = W.card * ℰ.card ∧
        (∀ ℳ : Finset (Finset ((Fin r × ZMod p_prime) × α)),
          ℳ ⊆ ℰ_orig →
          (∀ e₁ ∈ ℳ, ∀ e₂ ∈ ℳ, e₁ ≠ e₂ → Disjoint e₁ e₂) →
          ∃ ℳ_orig : Finset (Finset α), ℳ_orig ⊆ ℰ ∧
            (∀ e₁ ∈ ℳ_orig, ∀ e₂ ∈ ℳ_orig, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
            (ℳ.card : ℝ) ≤ (W.card : ℝ) * (ℳ_orig.card : ℝ)) := by
  classical
  obtain ⟨p_prime, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max D r)
  have : Fact p_prime.Prime := ⟨hp_prime⟩
  have hp_D : D ≤ p_prime := le_trans (le_max_left _ _) hp_ge
  have hp_r : r ≤ p_prime := le_trans (le_max_right _ _) hp_ge
  let W : Finset (Fin r × ZMod p_prime) := Finset.univ
  -- Original edges lifted to each copy `w ∈ W`.
  let liftOrig : (Fin r × ZMod p_prime) → Finset α → Finset ((Fin r × ZMod p_prime) × α) :=
    fun w e ↦ e.image (fun x ↦ (w, x))
  let ℰ_orig : Finset (Finset ((Fin r × ZMod p_prime) × α)) :=
    (W ×ˢ ℰ).image (fun p ↦ liftOrig p.1 p.2)
  -- Padding affine lines on `W × {x}` for slopes `a < D - deg(x)`.
  let lineOf : ZMod p_prime → ZMod p_prime → α → Finset ((Fin r × ZMod p_prime) × α) :=
    fun a b x ↦ (Finset.univ : Finset (Fin r)).image (fun i ↦ ((i, a * (i.1 : ZMod p_prime) + b), x))
  let defOf : α → ℕ := fun x ↦ D - (ℰ.filter (fun e ↦ x ∈ e)).card
  let padTriples : Finset (α × Fin p_prime × ZMod p_prime) :=
    (U ×ˢ ((Finset.univ : Finset (Fin p_prime)) ×ˢ (Finset.univ : Finset (ZMod p_prime)))).filter
      (fun t ↦ t.2.1.1 < defOf t.1)
  let ℰ_pad : Finset (Finset ((Fin r × ZMod p_prime) × α)) :=
    padTriples.image (fun t ↦ lineOf (t.2.1.1 : ZMod p_prime) t.2.2 t.1)
  let ℰ_reg : Finset (Finset ((Fin r × ZMod p_prime) × α)) := ℰ_orig ∪ ℰ_pad
  -- Helper: injectivity of `Fin r → ZMod p_prime`.
  have hfin_inj : ∀ i j : Fin r, ((i.1 : ZMod p_prime) = (j.1 : ZMod p_prime)) → i = j := by
    intro i j hij
    have hi : i.1 < p_prime := lt_of_lt_of_le i.2 hp_r
    have hj : j.1 < p_prime := lt_of_lt_of_le j.2 hp_r
    have hval : i.1 % p_prime = j.1 % p_prime := by
      have := (ZMod.natCast_eq_natCast_iff' i.1 j.1 p_prime).mp hij
      exact this
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hval
    exact Fin.ext hval
  -- Helper: `ℰ_orig` and `ℰ_pad` are disjoint (orig has ≥ 2 distinct `x`, pad has constant `x`).
  have hdisj_op : Disjoint ℰ_orig ℰ_pad := by
    rw [Finset.disjoint_left]
    intro E hEo hEp
    obtain ⟨⟨w, e⟩, hwe, rfl⟩ := mem_image.mp hEo
    obtain ⟨⟨x, a, b⟩, _, heq⟩ := mem_image.mp hEp
    have he_card : e.card = r := (hunif e (mem_product.mp hwe).2).2
    obtain ⟨x₁, hx₁, x₂, hx₂, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
    have h1 : (w, x₁) ∈ lineOf (a.1 : ZMod p_prime) b x := heq ▸ mem_image_of_mem _ hx₁
    have h2 : (w, x₂) ∈ lineOf (a.1 : ZMod p_prime) b x := heq ▸ mem_image_of_mem _ hx₂
    obtain ⟨_, _, h1'⟩ := mem_image.mp h1
    obtain ⟨_, _, h2'⟩ := mem_image.mp h2
    have hx1 : x₁ = x := (Prod.mk.inj h1').2.symm
    have hx2 : x₂ = x := (Prod.mk.inj h2').2.symm
    exact hxne (hx1.trans hx2.symm)
  -- Helper: `liftOrig` is injective on `W ×ˢ ℰ`.
  have hlift_inj : Set.InjOn (fun p : (Fin r × ZMod p_prime) × Finset α ↦ liftOrig p.1 p.2)
      ((W ×ˢ ℰ : Finset ((Fin r × ZMod p_prime) × Finset α)) : Set ((Fin r × ZMod p_prime) × Finset α)) := by
    intro ⟨w₁, e₁⟩ h₁ ⟨w₂, e₂⟩ h₂ heq
    dsimp only at heq
    have he₁_mem : e₁ ∈ ℰ := (mem_product.mp (mem_coe.mp h₁)).2
    have he₁_ne : e₁.Nonempty := card_pos.mp (by have := (hunif e₁ he₁_mem).2; omega)
    obtain ⟨x₀, hx₀⟩ := he₁_ne
    have hmem : (w₁, x₀) ∈ liftOrig w₂ e₂ := by
      rw [← heq]; exact mem_image_of_mem _ hx₀
    obtain ⟨_, _, hw⟩ := mem_image.mp hmem
    have hweq : w₁ = w₂ := (Prod.mk.inj hw).1.symm
    subst hweq
    have heeq : e₁ = e₂ := by
      ext x
      constructor
      · intro hx
        have h1 : (w₁, x) ∈ liftOrig w₁ e₂ := by rw [← heq]; exact mem_image_of_mem _ hx
        obtain ⟨y, hy, hxy⟩ := mem_image.mp h1
        exact (Prod.mk.inj hxy).2 ▸ hy
      · intro hx
        have h1 : (w₁, x) ∈ liftOrig w₁ e₁ := by rw [heq]; exact mem_image_of_mem _ hx
        obtain ⟨y, hy, hxy⟩ := mem_image.mp h1
        exact (Prod.mk.inj hxy).2 ▸ hy
    exact Prod.ext rfl heeq
  -- Helper: `lineOf` is injective on `padTriples`.
  have hline_inj : ∀ a₁ a₂ : Fin p_prime, ∀ b₁ b₂ : ZMod p_prime, ∀ x₁ x₂ : α,
      lineOf (a₁.1 : ZMod p_prime) b₁ x₁ = lineOf (a₂.1 : ZMod p_prime) b₂ x₂ →
      x₁ = x₂ ∧ a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ a₂ b₁ b₂ x₁ x₂ heq
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    have h0 : ((i0, (a₁.1 : ZMod p_prime) * (i0.1 : ZMod p_prime) + b₁), x₁) ∈
        lineOf (a₂.1 : ZMod p_prime) b₂ x₂ := heq ▸ mem_image_of_mem _ (mem_univ i0)
    have h1 : ((i1, (a₁.1 : ZMod p_prime) * (i1.1 : ZMod p_prime) + b₁), x₁) ∈
        lineOf (a₂.1 : ZMod p_prime) b₂ x₂ := heq ▸ mem_image_of_mem _ (mem_univ i1)
    obtain ⟨j0, _, hj0⟩ := mem_image.mp h0
    obtain ⟨j1, _, hj1⟩ := mem_image.mp h1
    have hx : x₁ = x₂ := (Prod.mk.inj hj0).2.symm
    have hj0_eq : j0 = i0 := (Prod.mk.inj (Prod.mk.inj hj0).1).1
    have hj1_eq : j1 = i1 := (Prod.mk.inj (Prod.mk.inj hj1).1).1
    have hb_eq : b₁ = b₂ := by
      have hy := (Prod.mk.inj (Prod.mk.inj hj0).1).2
      rw [hj0_eq] at hy
      simpa [i0] using hy.symm
    have ha_zmod : (a₁.1 : ZMod p_prime) = (a₂.1 : ZMod p_prime) := by
      have hy := (Prod.mk.inj (Prod.mk.inj hj1).1).2
      rw [hj1_eq, hb_eq] at hy
      simpa [i1] using hy.symm
    have ha_eq : a₁ = a₂ := by
      have hmod := (ZMod.natCast_eq_natCast_iff' a₁.1 a₂.1 p_prime).mp ha_zmod
      rw [Nat.mod_eq_of_lt a₁.2, Nat.mod_eq_of_lt a₂.2] at hmod
      exact Fin.ext hmod
    exact ⟨hx, ha_eq, hb_eq⟩
  refine ⟨p_prime, ⟨hp_prime⟩, ℰ_orig, ℰ_reg, subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · -- Uniformity: every `E ∈ ℰ_reg` has `E ⊆ W ×ˢ U` and `E.card = r`.
    intro E hE
    rcases mem_union.mp hE with hEo | hEp
    · obtain ⟨⟨w, e⟩, hwe, rfl⟩ := mem_image.mp hEo
      have he_sub := (hunif e (mem_product.mp hwe).2).1
      have he_card := (hunif e (mem_product.mp hwe).2).2
      refine ⟨fun p hp ↦ ?_, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
        exact mem_product.mpr ⟨mem_univ w, he_sub hx⟩
      · rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2), he_card]
    · obtain ⟨⟨x, a, b⟩, ht, rfl⟩ := mem_image.mp hEp
      have hxU : x ∈ U := (mem_product.mp (mem_filter.mp ht).1).1
      refine ⟨fun p hp ↦ ?_, ?_⟩
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact mem_product.mpr ⟨mem_univ _, hxU⟩
      · rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj (Prod.mk.inj h).1).1)]
        simp
  · -- Exact `D`-regularity: every `(w, x) ∈ W ×ˢ U` has degree `D` in `ℰ_reg`.
    intro ⟨w, x⟩ hv
    have hxU : x ∈ U := (mem_product.mp hv).2
    have hsplit : (ℰ_reg.filter (fun E ↦ (w, x) ∈ E)).card =
        (ℰ_orig.filter (fun E ↦ (w, x) ∈ E)).card + (ℰ_pad.filter (fun E ↦ (w, x) ∈ E)).card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint
        (hdisj_op.mono (filter_subset _ _) (filter_subset _ _))]
    rw [hsplit]
    have hdeg_orig : (ℰ_orig.filter (fun E ↦ (w, x) ∈ E)).card =
        (ℰ.filter (fun e ↦ x ∈ e)).card := by
      refine Finset.card_bij (fun E _ ↦ E.image Prod.snd) ?_ ?_ ?_
      · intro E hE
        obtain ⟨hEo, hwx⟩ := mem_filter.mp hE
        obtain ⟨⟨w', e⟩, hwe, rfl⟩ := mem_image.mp hEo
        obtain ⟨x', hx', hwx'⟩ := mem_image.mp hwx
        have hx_eq : x' = x := (Prod.mk.inj hwx').2
        have him : (liftOrig w' e).image Prod.snd = e := by
          ext y; simp [liftOrig]
        rw [him]
        exact mem_filter.mpr ⟨(mem_product.mp hwe).2, hx_eq ▸ hx'⟩
      · intro E₁ hE₁ E₂ hE₂ heq
        obtain ⟨hEo₁, hwx₁⟩ := mem_filter.mp hE₁
        obtain ⟨hEo₂, hwx₂⟩ := mem_filter.mp hE₂
        obtain ⟨⟨w₁, e₁⟩, _, rfl⟩ := mem_image.mp hEo₁
        obtain ⟨⟨w₂, e₂⟩, _, rfl⟩ := mem_image.mp hEo₂
        obtain ⟨_, _, h1⟩ := mem_image.mp hwx₁
        obtain ⟨_, _, h2⟩ := mem_image.mp hwx₂
        have hw1 : w₁ = w := (Prod.mk.inj h1).1
        have hw2 : w₂ = w := (Prod.mk.inj h2).1
        have him1 : (liftOrig w₁ e₁).image Prod.snd = e₁ := by ext y; simp [liftOrig]
        have him2 : (liftOrig w₂ e₂).image Prod.snd = e₂ := by ext y; simp [liftOrig]
        rw [him1, him2] at heq
        rw [hw1, hw2, heq]
      · intro e he
        obtain ⟨heℰ, hxe⟩ := mem_filter.mp he
        refine ⟨liftOrig w e, mem_filter.mpr
          ⟨mem_image.mpr ⟨(w, e), mem_product.mpr ⟨mem_univ w, heℰ⟩, rfl⟩,
            mem_image_of_mem _ hxe⟩, ?_⟩
        ext y; simp [liftOrig]
    have hdeg_pad : (ℰ_pad.filter (fun E ↦ (w, x) ∈ E)).card = defOf x := by
      have hdef_le : defOf x ≤ p_prime := (Nat.sub_le D _).trans hp_D
      have hcard_fin : (Finset.univ.filter (fun a : Fin p_prime ↦ a.1 < defOf x)).card = defOf x := by
        have hbij : (Finset.univ.filter (fun a : Fin p_prime ↦ a.1 < defOf x)).card =
            (Finset.range (defOf x)).card := by
          refine Finset.card_bij (fun a _ ↦ a.1) ?_ ?_ ?_
          · intro a ha; exact mem_range.mpr (mem_filter.mp ha).2
          · intro a₁ _ a₂ _ h; exact Fin.ext h
          · intro k hk; exact ⟨⟨k, lt_of_lt_of_le (mem_range.mp hk) hdef_le⟩,
              mem_filter.mpr ⟨mem_univ _, mem_range.mp hk⟩, rfl⟩
        rw [hbij, card_range]
      rw [← hcard_fin]
      symm
      refine Finset.card_bij
        (fun a _ ↦ lineOf (a.1 : ZMod p_prime) (w.2 - (a.1 : ZMod p_prime) * (w.1.1 : ZMod p_prime)) x)
        ?_ ?_ ?_
      · intro a ha
        refine mem_filter.mpr ⟨mem_image.mpr ⟨(x, a, w.2 - (a.1 : ZMod p_prime) * (w.1.1 : ZMod p_prime)),
          mem_filter.mpr ⟨mem_product.mpr ⟨hxU, mem_product.mpr ⟨mem_univ _, mem_univ _⟩⟩,
            (mem_filter.mp ha).2⟩, rfl⟩, ?_⟩
        exact mem_image.mpr ⟨w.1, mem_univ w.1, by ext <;> simp⟩
      · intro a₁ _ a₂ _ heq
        exact (hline_inj a₁ a₂ _ _ x x heq).2.1
      · intro E hE
        obtain ⟨hEp, hwx⟩ := mem_filter.mp hE
        obtain ⟨⟨x', a, b⟩, ht, rfl⟩ := mem_image.mp hEp
        obtain ⟨i, _, hi_eq⟩ := mem_image.mp hwx
        have hx_eq : x' = x := (Prod.mk.inj hi_eq).2
        have hi_w1 : i = w.1 := (Prod.mk.inj (Prod.mk.inj hi_eq).1).1
        have hy_w2 : (a.1 : ZMod p_prime) * (i.1 : ZMod p_prime) + b = w.2 :=
          (Prod.mk.inj (Prod.mk.inj hi_eq).1).2
        have hb_eq : b = w.2 - (a.1 : ZMod p_prime) * (w.1.1 : ZMod p_prime) := by
          rw [hi_w1] at hy_w2; exact eq_sub_of_add_eq' hy_w2
        subst hx_eq
        refine ⟨a, mem_filter.mpr ⟨mem_univ a, (mem_filter.mp ht).2⟩, by rw [hb_eq]⟩
    rw [hdeg_orig, hdeg_pad]
    have hle := hdeg x hxU
    simp only [defOf]
    omega
  · -- Codegree bound: `codeg ≤ max Δ₂ 1`.
    intro ⟨w₁, x₁⟩ hv₁ ⟨w₂, x₂⟩ hv₂ hne
    have hx₁U : x₁ ∈ U := (mem_product.mp hv₁).2
    have hx₂U : x₂ ∈ U := (mem_product.mp hv₂).2
    have hsplit : (ℰ_reg.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card =
        (ℰ_orig.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card +
        (ℰ_pad.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint
        (hdisj_op.mono (filter_subset _ _) (filter_subset _ _))]
    rw [hsplit]
    by_cases hw : w₁ = w₂
    · subst hw
      have hxne : x₁ ≠ x₂ := fun h ↦ hne (Prod.ext rfl h)
      have hpad0 : (ℰ_pad.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₁, x₂) ∈ E)).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro E hE
        obtain ⟨hEp, h1, h2⟩ := mem_filter.mp hE
        obtain ⟨⟨x, a, b⟩, _, rfl⟩ := mem_image.mp hEp
        obtain ⟨_, _, h1'⟩ := mem_image.mp h1
        obtain ⟨_, _, h2'⟩ := mem_image.mp h2
        exact hxne ((Prod.mk.inj h1').2.symm.trans (Prod.mk.inj h2').2)
      have horig_le : (ℰ_orig.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₁, x₂) ∈ E)).card ≤ Δ₂ := by
        refine (Finset.card_le_card_of_injOn (fun E ↦ E.image Prod.snd) ?_ ?_).trans
          (hcodeg x₁ hx₁U x₂ hx₂U hxne)
        · intro E hE
          obtain ⟨hEo, h1, h2⟩ := mem_filter.mp (mem_coe.mp hE)
          obtain ⟨⟨w', e⟩, hwe, rfl⟩ := mem_image.mp hEo
          obtain ⟨y₁, hy₁, h1'⟩ := mem_image.mp h1
          obtain ⟨y₂, hy₂, h2'⟩ := mem_image.mp h2
          have him : (liftOrig w' e).image Prod.snd = e := by ext y; simp [liftOrig]
          dsimp only
          rw [mem_coe, him]
          exact mem_filter.mpr ⟨(mem_product.mp hwe).2,
            (Prod.mk.inj h1').2 ▸ hy₁, (Prod.mk.inj h2').2 ▸ hy₂⟩
        · intro E₁ hE₁ E₂ hE₂ heq
          obtain ⟨hEo₁, h1₁, _⟩ := mem_filter.mp (mem_coe.mp hE₁)
          obtain ⟨hEo₂, h1₂, _⟩ := mem_filter.mp (mem_coe.mp hE₂)
          obtain ⟨⟨w₁', e₁⟩, _, rfl⟩ := mem_image.mp hEo₁
          obtain ⟨⟨w₂', e₂⟩, _, rfl⟩ := mem_image.mp hEo₂
          obtain ⟨_, _, hw1'⟩ := mem_image.mp h1₁
          obtain ⟨_, _, hw2'⟩ := mem_image.mp h1₂
          have him1 : (liftOrig w₁' e₁).image Prod.snd = e₁ := by ext y; simp [liftOrig]
          have him2 : (liftOrig w₂' e₂).image Prod.snd = e₂ := by ext y; simp [liftOrig]
          dsimp only at heq
          rw [him1, him2] at heq
          rw [(Prod.mk.inj hw1').1, (Prod.mk.inj hw2').1, heq]
      rw [hpad0, add_zero]
      exact horig_le.trans (le_max_left _ _)
    · -- `w₁ ≠ w₂`: no original edge contains both; at most 1 padding line contains both.
      have horig0 : (ℰ_orig.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro E hE
        obtain ⟨hEo, h1, h2⟩ := mem_filter.mp hE
        obtain ⟨⟨w', e⟩, _, rfl⟩ := mem_image.mp hEo
        obtain ⟨_, _, h1'⟩ := mem_image.mp h1
        obtain ⟨_, _, h2'⟩ := mem_image.mp h2
        exact hw ((Prod.mk.inj h1').1.symm.trans (Prod.mk.inj h2').1)
      have hpad_le1 : (ℰ_pad.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro E₁ hE₁ E₂ hE₂
        obtain ⟨hEp₁, h1₁, h2₁⟩ := mem_filter.mp hE₁
        obtain ⟨hEp₂, h1₂, h2₂⟩ := mem_filter.mp hE₂
        obtain ⟨⟨x, a₁, b₁⟩, _, rfl⟩ := mem_image.mp hEp₁
        obtain ⟨⟨x', a₂, b₂⟩, _, rfl⟩ := mem_image.mp hEp₂
        obtain ⟨i₁, _, hi₁⟩ := mem_image.mp h1₁
        obtain ⟨j₁, _, hj₁⟩ := mem_image.mp h2₁
        obtain ⟨i₂, _, hi₂⟩ := mem_image.mp h1₂
        obtain ⟨j₂, _, hj₂⟩ := mem_image.mp h2₂
        have hx_eq : x = x' := (Prod.mk.inj hi₁).2.trans (Prod.mk.inj hi₂).2.symm
        have hi1 : i₁ = w₁.1 := (Prod.mk.inj (Prod.mk.inj hi₁).1).1
        have hj1 : j₁ = w₂.1 := (Prod.mk.inj (Prod.mk.inj hj₁).1).1
        have hi2 : i₂ = w₁.1 := (Prod.mk.inj (Prod.mk.inj hi₂).1).1
        have hj2 : j₂ = w₂.1 := (Prod.mk.inj (Prod.mk.inj hj₂).1).1
        have hy1_1 : (a₁.1 : ZMod p_prime) * (w₁.1.1 : ZMod p_prime) + b₁ = w₁.2 :=
          hi1 ▸ (Prod.mk.inj (Prod.mk.inj hi₁).1).2
        have hy2_1 : (a₁.1 : ZMod p_prime) * (w₂.1.1 : ZMod p_prime) + b₁ = w₂.2 :=
          hj1 ▸ (Prod.mk.inj (Prod.mk.inj hj₁).1).2
        have hy1_2 : (a₂.1 : ZMod p_prime) * (w₁.1.1 : ZMod p_prime) + b₂ = w₁.2 :=
          hi2 ▸ (Prod.mk.inj (Prod.mk.inj hi₂).1).2
        have hy2_2 : (a₂.1 : ZMod p_prime) * (w₂.1.1 : ZMod p_prime) + b₂ = w₂.2 :=
          hj2 ▸ (Prod.mk.inj (Prod.mk.inj hj₂).1).2
        have hw12_ne : w₁.1 ≠ w₂.1 := by
          intro hsame
          have : w₁.2 = w₂.2 := by rw [← hy1_1, ← hy2_1, hsame]
          exact hw (Prod.ext hsame this)
        have hdiff_ne : (w₁.1.1 : ZMod p_prime) - (w₂.1.1 : ZMod p_prime) ≠ 0 := by
          intro h0
          exact hw12_ne (hfin_inj w₁.1 w₂.1 (sub_eq_zero.mp h0))
        have ha_eq : (a₁.1 : ZMod p_prime) = (a₂.1 : ZMod p_prime) := by
          have hsub : ((a₁.1 : ZMod p_prime) - (a₂.1 : ZMod p_prime)) *
              ((w₁.1.1 : ZMod p_prime) - (w₂.1.1 : ZMod p_prime)) = 0 := by
            linear_combination (hy1_1 - hy2_1) - (hy1_2 - hy2_2)
          exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hdiff_ne)
        have hb_eq : b₁ = b₂ := by
          linear_combination hy1_1 - hy1_2 - (w₁.1.1 : ZMod p_prime) * ha_eq
        rw [hx_eq, ha_eq, hb_eq]
      rw [horig0, zero_add]
      exact hpad_le1.trans (le_max_right _ _)
  · -- `ℰ_orig.card = W.card * ℰ.card`.
    rw [Finset.card_image_of_injOn hlift_inj, Finset.card_product]
  · -- Pigeonhole extraction of a matching in `ℰ` from a matching `ℳ ⊆ ℰ_orig`.
    intro ℳ hℳ_sub hℳ_disj
    let slice : (Fin r × ZMod p_prime) → Finset (Finset α) := fun w ↦
      ℰ.filter (fun e ↦ liftOrig w e ∈ ℳ)
    have hsum_slice : ∑ w ∈ W, (slice w).card = ℳ.card := by
      have hbi : ℳ = W.biUnion (fun w ↦ (slice w).image (liftOrig w)) := by
        ext E
        simp only [mem_biUnion, mem_image, slice, mem_filter]
        constructor
        · intro hE
          obtain ⟨⟨w, e⟩, hwe, rfl⟩ := mem_image.mp (hℳ_sub hE)
          exact ⟨w, mem_univ w, e, ⟨(mem_product.mp hwe).2, hE⟩, rfl⟩
        · rintro ⟨w, _, e, ⟨_, hE⟩, rfl⟩; exact hE
      conv_rhs => rw [hbi]
      rw [Finset.card_biUnion]
      · refine sum_congr rfl fun w _ ↦ ?_
        rw [Finset.card_image_of_injOn]
        intro e₁ he₁ e₂ he₂ heq
        have h1 := hlift_inj
          (x₁ := (w, e₁)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w, (mem_filter.mp (mem_coe.mp he₁)).1⟩))
          (x₂ := (w, e₂)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w, (mem_filter.mp (mem_coe.mp he₂)).1⟩))
          heq
        exact (Prod.mk.inj h1).2
      · intro w₁ _ w₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro E h1 h2
        obtain ⟨e₁, he₁, rfl⟩ := mem_image.mp h1
        obtain ⟨e₂, he₂, heq⟩ := mem_image.mp h2
        have hpair := hlift_inj
          (x₁ := (w₂, e₂)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₂, (mem_filter.mp he₂).1⟩))
          (x₂ := (w₁, e₁)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₁, (mem_filter.mp he₁).1⟩))
          heq
        exact hne (Prod.mk.inj hpair).1.symm
    have hW_ne : W.Nonempty := ⟨(⟨0, by omega⟩, 0), mem_univ _⟩
    obtain ⟨w₀, _, hw₀_max⟩ := Finset.exists_max_image W (fun w ↦ (slice w).card) hW_ne
    refine ⟨slice w₀, filter_subset _ _, ?_, ?_⟩
    · intro e₁ he₁ e₂ he₂ hne
      have h1 : liftOrig w₀ e₁ ∈ ℳ := (mem_filter.mp he₁).2
      have h2 : liftOrig w₀ e₂ ∈ ℳ := (mem_filter.mp he₂).2
      have hne' : liftOrig w₀ e₁ ≠ liftOrig w₀ e₂ := fun heq ↦
        hne (Prod.mk.inj (hlift_inj
          (x₁ := (w₀, e₁)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₀, (mem_filter.mp he₁).1⟩))
          (x₂ := (w₀, e₂)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₀, (mem_filter.mp he₂).1⟩))
          heq)).2
      have hd := hℳ_disj _ h1 _ h2 hne'
      rw [Finset.disjoint_left] at hd ⊢
      intro x hx₁ hx₂
      exact hd (mem_image_of_mem _ hx₁) (mem_image_of_mem _ hx₂)
    · have hle : ℳ.card ≤ W.card * (slice w₀).card := by
        calc ℳ.card = ∑ w ∈ W, (slice w).card := hsum_slice.symm
          _ ≤ ∑ _w ∈ W, (slice w₀).card := sum_le_sum fun w hw ↦ hw₀_max w hw
          _ = W.card * (slice w₀).card := by simp
      exact_mod_cast hle

/- ### Section 3: One-Step Nibble & `T`-Round Frankl--Rödl / Pippenger Matching Theorem -/

set_option maxHeartbeats 1200000 in
lemma nibble_one_step {α : Type*} [DecidableEq α]
    (U : Finset α) (ℰ_orig ℰ_reg : Finset (Finset α)) (r D Δ₂ : ℕ)
    (ε η₁ c_next : ℝ)
    (hr : 2 ≤ r) (hD : 1 ≤ D)
    (hε0 : 0 < ε) (hε_small : 4 * (r : ℝ) * ε ≤ 1)
    (hη₁0 : 0 < η₁) (hη₁_le : η₁ ≤ 1 / 4)
    (hc_nn : 0 ≤ c_next)
    (hβ_small : 4 * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤ η₁)
    (hβ_cheb : 32 * ((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (r : ℝ) ≤ η₁ ^ 3)
    (hD_η : 2 ≤ η₁ * (D : ℝ))
    (hsub : ℰ_orig ⊆ ℰ_reg)
    (hunif : ∀ e ∈ ℰ_reg, e ⊆ U ∧ e.card = r)
    (hreg : ∀ v ∈ U, (ℰ_reg.filter (fun e ↦ v ∈ e)).card = D)
    (hcodeg : ∀ v₁ ∈ U, ∀ v₂ ∈ U, v₁ ≠ v₂ →
      (ℰ_reg.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card ≤ Δ₂) :
    let p : ℝ := ε / (D : ℝ)
    let D' : ℕ := Nat.ceil ((1 + η₁) * (1 - p) ^ ((r - 1) * D) * (D : ℝ))
    ∃ (ℳ₁ ℰ_rem : Finset (Finset α)),
      ℳ₁ ⊆ ℰ_orig ∧ ℰ_rem ⊆ ℰ_orig ∧
      (∀ e₁ ∈ ℳ₁, ∀ e₂ ∈ ℳ₁, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
      (∀ e₁ ∈ ℳ₁, ∀ e₂ ∈ ℰ_rem, Disjoint e₁ e₂) ∧
      (∀ v ∈ U, (ℰ_rem.filter (fun e ↦ v ∈ e)).card ≤ D') ∧
      (D : ℝ) / 2 ≤ (D' : ℝ) ∧
      (ε * (1 - (r : ℝ) * ε) + c_next * (1 - ε - 4 * η₁)) * ((ℰ_orig.card : ℝ) / (D : ℝ)) ≤
        (ℳ₁.card : ℝ) + c_next * ((ℰ_rem.card : ℝ) / (D' : ℝ)) := by
  classical
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let p : ℝ := ε / (D : ℝ)
  have hp0 : 0 ≤ p := by positivity
  have hp_half : p ≤ 1 / 2 := by
    have : ε ≤ (D : ℝ) / 2 := by
      have h1 : 1 ≤ (D : ℝ) := by exact_mod_cast hD
      have h2 : 2 ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    exact (div_le_iff₀ hD_pos).mpr (by linarith)
  have hp1 : p ≤ 1 := hp_half.trans (by norm_num)
  let D_exp : ℝ := (1 - p) ^ ((r - 1) * D) * (D : ℝ)
  let D' : ℕ := Nat.ceil ((1 + η₁) * (1 - p) ^ ((r - 1) * D) * (D : ℝ))
  have hD'_arg : (1 + η₁) * (1 - p) ^ ((r - 1) * D) * (D : ℝ) = (1 + η₁) * D_exp := by
    simp only [D_exp]; ring
  have hpow_r1 : 1 / 2 ≤ (1 - p) ^ ((r - 1) * D) := by
    have h1 := one_sub_mul_le_pow hp0 hp1 ((r - 1) * D)
    have h2 : (((r - 1) * D : ℕ) : ℝ) * p = ((r : ℝ) - 1) * ε := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      simp only [p]; field_simp
    rw [h2] at h1
    nlinarith
  have hD_exp_ge : (D : ℝ) / 2 ≤ D_exp := by
    simp only [D_exp]; nlinarith
  have hD'_ge : (D : ℝ) / 2 ≤ (D' : ℝ) := by
    have h1 : (1 + η₁) * D_exp ≤ (D' : ℝ) := hD'_arg ▸ Nat.le_ceil _
    nlinarith
  have hD'_pos : (0 : ℝ) < (D' : ℝ) := by linarith
  have hD'_le : (D' : ℝ) ≤ (1 + 2 * η₁) * D_exp := by
    have h1 : (D' : ℝ) < (1 + η₁) * D_exp + 1 := by
      rw [← hD'_arg]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ η₁ * D_exp := by nlinarith
    linarith
  -- Probability space `Ω := { e // e ∈ ℰ_reg } → Bool` with Bernoulli(`p`) weight `P ω`.
  let P : ({ e // e ∈ ℰ_reg } → Bool) → ℝ := fun ω ↦ ∏ e : { e // e ∈ ℰ_reg }, if ω e then p else 1 - p
  have hP_nn : ∀ ω, 0 ≤ P ω := fun ω ↦ Finset.prod_nonneg fun _ _ ↦ by split_ifs <;> linarith
  have hP_sum : ∑ ω : { e // e ∈ ℰ_reg } → Bool, P ω = 1 :=
    bern_sum_one (ι := { e // e ∈ ℰ_reg }) p
  -- Helper: neighbor edges of `e` in `ℰ_reg`.
  let N_all : Finset α → Finset { e // e ∈ ℰ_reg } := fun s ↦
    Finset.univ.filter (fun f ↦ (f.1 ∩ s).Nonempty)
  have hN_card_le : ∀ s ⊆ U, (N_all s).card ≤ s.card * D := by
    intro s hs
    have hsubN : (N_all s).image Subtype.val ⊆ s.biUnion (fun v ↦ ℰ_reg.filter (fun f ↦ v ∈ f)) := by
      intro f hf
      obtain ⟨f', hf', rfl⟩ := mem_image.mp hf
      obtain ⟨v, hv⟩ := (mem_filter.mp hf').2
      exact mem_biUnion.mpr ⟨v, (mem_inter.mp hv).2, mem_filter.mpr ⟨f'.2, (mem_inter.mp hv).1⟩⟩
    calc (N_all s).card
        = ((N_all s).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (s.biUnion (fun v ↦ ℰ_reg.filter (fun f ↦ v ∈ f))).card := card_le_card hsubN
      _ ≤ ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card := card_biUnion_le
      _ = ∑ _v ∈ s, D := sum_congr rfl fun v hv ↦ hreg v (hs hv)
      _ = s.card * D := by simp
  -- Inclusion-exclusion lower bound on `(N_all s).card` for `s ⊆ U`.
  have hN_card_ge : ∀ s ⊆ U, s.card * D ≤ (N_all s).card + s.card * s.card * Δ₂ := by
    intro s hs
    have h1 : s.card * D = ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card := by
      rw [sum_congr rfl fun v hv ↦ hreg v (hs hv)]; simp
    have h2 : ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card =
        ∑ f ∈ N_all s, (f.1 ∩ s).card := by
      have hlhs : ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card =
          ∑ v ∈ s, ∑ f : { e // e ∈ ℰ_reg }, if v ∈ f.1 then 1 else 0 := by
        refine sum_congr rfl fun v _ ↦ ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        refine Finset.card_bij (fun f _ ↦ ⟨f, (mem_filter.mp ‹_›).1⟩) ?_ ?_ ?_
        · intro f hf; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2⟩
        · intro _ _ _ _ h; exact congrArg Subtype.val h
        · intro f hf; exact ⟨f.1, mem_filter.mpr ⟨f.2, (mem_filter.mp hf).2⟩, rfl⟩
      rw [hlhs, Finset.sum_comm]
      have hsub2 : ∑ f : { e // e ∈ ℰ_reg }, ∑ v ∈ s, (if v ∈ f.1 then 1 else 0) =
          ∑ f ∈ N_all s, ∑ v ∈ s, (if v ∈ f.1 then 1 else 0) := by
        symm
        refine sum_subset (subset_univ _) fun f _ hf ↦ ?_
        have hemp : f.1 ∩ s = ∅ := by
          rw [← Finset.not_nonempty_iff_eq_empty]
          exact fun hne ↦ hf (mem_filter.mpr ⟨mem_univ f, hne⟩)
        refine sum_eq_zero fun v hv ↦ ?_
        rw [if_neg]
        intro hvf
        have : v ∈ f.1 ∩ s := mem_inter.mpr ⟨hvf, hv⟩
        rw [hemp] at this; exact notMem_empty v this
      rw [hsub2]
      refine sum_congr rfl fun f _ ↦ ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1; ext v; simp [and_comm]
    have h3 : ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) ≤ s.card * s.card * Δ₂ := by
      have hpair : ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) =
          ∑ p ∈ s.offDiag, (ℰ_reg.filter (fun f ↦ p.1 ∈ f ∧ p.2 ∈ f)).card := by
        have hl : ∀ f ∈ N_all s, (f.1 ∩ s).card * ((f.1 ∩ s).card - 1) =
            ((f.1 ∩ s).offDiag).card := fun f _ ↦ by
          rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
        rw [sum_congr rfl hl]
        calc ∑ f ∈ N_all s, ((f.1 ∩ s).offDiag).card
            = ∑ f ∈ N_all s, ∑ p ∈ s.offDiag, if (p.1 ∈ f.1 ∧ p.2 ∈ f.1) then 1 else 0 := by
              refine sum_congr rfl fun f _ ↦ ?_
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
              congr 1; ext ⟨u, v⟩; simp [mem_offDiag]; tauto
          _ = ∑ p ∈ s.offDiag, ∑ f ∈ N_all s, if (p.1 ∈ f.1 ∧ p.2 ∈ f.1) then 1 else 0 :=
              Finset.sum_comm
          _ = ∑ p ∈ s.offDiag, (ℰ_reg.filter (fun f ↦ p.1 ∈ f ∧ p.2 ∈ f)).card := by
              refine sum_congr rfl fun p hp ↦ ?_
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
              refine Finset.card_bij (fun f _ ↦ f.1) ?_ ?_ ?_
              · intro f hf; exact mem_filter.mpr ⟨f.2, (mem_filter.mp hf).2⟩
              · intro _ _ _ _ h; exact Subtype.ext h
              · intro f hf
                obtain ⟨hfℰ, h1, h2⟩ := mem_filter.mp hf
                exact ⟨⟨f, hfℰ⟩, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
                  ⟨p.1, mem_inter.mpr ⟨h1, (mem_offDiag.mp hp).1⟩⟩⟩, h1, h2⟩, rfl⟩
      rw [hpair]
      calc ∑ p ∈ s.offDiag, (ℰ_reg.filter (fun f ↦ p.1 ∈ f ∧ p.2 ∈ f)).card
          ≤ ∑ _p ∈ s.offDiag, Δ₂ := sum_le_sum fun p hp ↦
            hcodeg p.1 (hs (mem_offDiag.mp hp).1) p.2 (hs (mem_offDiag.mp hp).2.1)
              (mem_offDiag.mp hp).2.2
        _ = s.offDiag.card * Δ₂ := by simp
        _ ≤ s.card * s.card * Δ₂ := by
            rw [Finset.offDiag_card]
            exact Nat.mul_le_mul_right Δ₂ (Nat.sub_le _ _)
    have h4 : ∑ f ∈ N_all s, (f.1 ∩ s).card ≤
        (N_all s).card + ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) := by
      have : (N_all s).card + ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) =
          ∑ f ∈ N_all s, (1 + (f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rw [this]
      refine sum_le_sum fun f _ ↦ ?_
      cases hk : (f.1 ∩ s).card with
      | zero => omega
      | succ m =>
        cases m with
        | zero => simp
        | succ m' =>
          have hsub1 : m' + 1 + 1 - 1 = m' + 1 := by omega
          rw [hsub1]
          have hmul : m' + 1 + 1 ≤ (m' + 1 + 1) * (m' + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega
    omega
  -- Define random outcomes for each `ω : { e // e ∈ ℰ_reg } → Bool`.
  let ℳ₁_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset (Finset α) := fun ω ↦
    ℰ_orig.filter (fun e ↦ ∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧
      ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false)
  let ℰ'_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset (Finset α) := fun ω ↦
    ℰ_orig.filter (fun e ↦ ∀ f ∈ N_all e, ω f = false)
  let X_of : α → ({ e // e ∈ ℰ_reg } → Bool) → ℕ := fun v ω ↦
    (ℰ_reg.filter (fun e ↦ v ∈ e ∧ ∀ f ∈ N_all (e.erase v), ω f = false)).card
  let B_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset α := fun ω ↦
    U.filter (fun v ↦ D' < X_of v ω)
  let ℰ_rem_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset (Finset α) := fun ω ↦
    (ℰ'_of ω).filter (fun e ↦ Disjoint e (B_of ω))
  -- Expectation of `ℳ₁_of`.
  have hE_M1 : ε * (1 - (r : ℝ) * ε) * ((ℰ_orig.card : ℝ) / (D : ℝ)) ≤
      ∑ ω, P ω * ((ℳ₁_of ω).card : ℝ) := by
    have hsw : ∑ ω, P ω * ((ℳ₁_of ω).card : ℝ) =
        ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦
          ∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false), P ω := by
      have h1 : ∀ ω, P ω * ((ℳ₁_of ω).card : ℝ) =
          ∑ e ∈ ℰ_orig, if (∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧
            ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false) then P ω else 0 := by
        intro ω; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun e _ ↦ (Finset.sum_filter _ _).symm
    rw [hsw]
    calc ε * (1 - (r : ℝ) * ε) * ((ℰ_orig.card : ℝ) / (D : ℝ))
        = ∑ _e ∈ ℰ_orig, (p * (1 - (r : ℝ) * ε)) := by
          simp only [p, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦
            ∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false),
            P ω := by
          refine sum_le_sum fun e he ↦ ?_
          have he_reg : e ∈ ℰ_reg := hsub he
          have hfilt : Finset.univ.filter (fun ω : { e // e ∈ ℰ_reg } → Bool ↦
              ∃ he' : e ∈ ℰ_reg, ω ⟨e, he'⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he'⟩, ω f = false) =
              Finset.univ.filter (fun ω : { e // e ∈ ℰ_reg } → Bool ↦
                ω ⟨e, he_reg⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he_reg⟩, ω f = false) := by
            ext ω; simp [he_reg]
          rw [hfilt]
          have hbern_eq : ∑ ω ∈ Finset.univ.filter (fun ω : { e // e ∈ ℰ_reg } → Bool ↦
                ω ⟨e, he_reg⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he_reg⟩, ω f = false), P ω =
              p * (1 - p) ^ ((N_all e).erase ⟨e, he_reg⟩).card := by
            convert bern_sum_one_true_rest_false p ⟨e, he_reg⟩ ((N_all e).erase ⟨e, he_reg⟩)
              (notMem_erase _ _) using 1
          rw [hbern_eq]
          have hcard : ((N_all e).erase ⟨e, he_reg⟩).card ≤ r * D :=
            (card_erase_le).trans ((hunif e he_reg).2 ▸ hN_card_le e (hunif e he_reg).1)
          have hpow : (1 - p) ^ (r * D) ≤ (1 - p) ^ ((N_all e).erase ⟨e, he_reg⟩).card :=
            pow_le_pow_of_le_one (by linarith) (by linarith) hcard
          have hbern : 1 - (r : ℝ) * ε ≤ (1 - p) ^ (r * D) := by
            have := one_sub_mul_le_pow hp0 hp1 (r * D)
            have hmul : ((r * D : ℕ) : ℝ) * p = (r : ℝ) * ε := by
              rw [Nat.cast_mul]; simp only [p]; field_simp
            rwa [hmul] at this
          exact mul_le_mul_of_nonneg_left (hbern.trans hpow) hp0
  -- Expectation of `ℰ'_of`.
  have hE_E' : (1 - p) ^ (r * D) * (ℰ_orig.card : ℝ) ≤ ∑ ω, P ω * ((ℰ'_of ω).card : ℝ) := by
    have hsw : ∑ ω, P ω * ((ℰ'_of ω).card : ℝ) =
        ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦ ∀ f ∈ N_all e, ω f = false), P ω := by
      have h1 : ∀ ω, P ω * ((ℰ'_of ω).card : ℝ) =
          ∑ e ∈ ℰ_orig, if (∀ f ∈ N_all e, ω f = false) then P ω else 0 := by
        intro ω; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun e _ ↦ (Finset.sum_filter _ _).symm
    rw [hsw]
    calc (1 - p) ^ (r * D) * (ℰ_orig.card : ℝ)
        = ∑ _e ∈ ℰ_orig, (1 - p) ^ (r * D) := by simp [mul_comm]
      _ ≤ ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦ ∀ f ∈ N_all e, ω f = false), P ω := by
          refine sum_le_sum fun e he ↦ ?_
          rw [bern_sum_all_false p (N_all e)]
          have hcard : (N_all e).card ≤ r * D :=
            (hunif e (hsub he)).2 ▸ hN_card_le e (hunif e (hsub he)).1
          exact pow_le_pow_of_le_one (by linarith) (by linarith) hcard
  -- Chebyshev bound on `Pr[D' < X_of v ω]` for every fixed `v ∈ U`.
  have hbad_prob : ∀ v ∈ U,
      ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω ≤ η₁ / (r : ℝ) := by
    intro v hv
    let Ev : Finset (Finset α) := ℰ_reg.filter (fun e ↦ v ∈ e)
    have hEv_card : Ev.card = D := hreg v hv
    let μ : ℝ := ∑ ω, P ω * (X_of v ω : ℝ)
    -- Exact formula for `μ = ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card`.
    have hμ_eq : μ = ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card := by
      have h1 : ∀ ω, P ω * (X_of v ω : ℝ) =
          ∑ e ∈ Ev, if (∀ f ∈ N_all (e.erase v), ω f = false) then P ω else 0 := by
        intro ω
        have hcard_eq : X_of v ω = (Ev.filter (fun e ↦ ∀ f ∈ N_all (e.erase v), ω f = false)).card := by
          simp only [X_of, Ev, Finset.filter_filter]
        rw [hcard_eq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      simp only [μ]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun e _ ↦ ?_
      rw [← Finset.sum_filter, bern_sum_all_false p (N_all (e.erase v))]
    -- Factor `inv_c := ((1 - p) ^ (r * r * Δ₂))⁻¹ ≤ 1 + η₁ / 2` (actually `1 + 4 * r^2 * ε * Δ₂ / D`).
    have hε_half : ε ≤ 1 / 2 := by
      have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    have hk_small : 2 * ((r * r * Δ₂ : ℕ) : ℝ) * p ≤ 1 := by
      have h1 : 2 * ((r * r * Δ₂ : ℕ) : ℝ) * p = 2 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
        push_cast; simp only [p]; ring
      rw [h1]
      have h2 : 4 * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤ 1 / 4 := hβ_small.trans hη₁_le
      have h3 := mul_le_mul_of_nonneg_left h2 hε0.le
      have h4 : 2 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤ (1 / 8) * ε := by linarith
      linarith
    have hinv_le : ((1 - p) ^ (r * r * Δ₂))⁻¹ ≤ 1 + 4 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
      have h := inv_one_sub_pow_le hp0 hp_half (r * r * Δ₂) hk_small
      have h1 : 4 * ((r * r * Δ₂ : ℕ) : ℝ) * p = 4 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
        push_cast; simp only [p]; ring
      rwa [h1] at h
    -- Upper bound `μ ≤ (1 + η₁ / 2) * D_exp`.
    have hμ_le : μ ≤ (1 + η₁ / 2) * D_exp := by
      have hterm : ∀ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card ≤
          ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D) := by
        intro e he
        have he_reg : e ∈ ℰ_reg := (mem_filter.mp he).1
        have hve : v ∈ e := (mem_filter.mp he).2
        have herase_sub : e.erase v ⊆ U := (erase_subset v e).trans (hunif e he_reg).1
        have herase_card : (e.erase v).card = r - 1 := by
          rw [card_erase_of_mem hve, (hunif e he_reg).2]
        have hge := hN_card_ge (e.erase v) herase_sub
        rw [herase_card] at hge
        have hle2 : (r - 1) * D ≤ (N_all (e.erase v)).card + r * r * Δ₂ := by
          have : (r - 1) * (r - 1) ≤ r * r := Nat.mul_le_mul (Nat.sub_le r 1) (Nat.sub_le r 1)
          have : (r - 1) * (r - 1) * Δ₂ ≤ r * r * Δ₂ := Nat.mul_le_mul_right Δ₂ this
          omega
        have hpow_le : (1 - p) ^ ((N_all (e.erase v)).card + r * r * Δ₂) ≤
            (1 - p) ^ ((r - 1) * D) :=
          pow_le_pow_of_le_one (by linarith) (by linarith) hle2
        rw [pow_add] at hpow_le
        have hpos_f : 0 < (1 - p) ^ (r * r * Δ₂) := pow_pos (by linarith) _
        calc (1 - p) ^ (N_all (e.erase v)).card
            = ((1 - p) ^ (r * r * Δ₂))⁻¹ * ((1 - p) ^ (N_all (e.erase v)).card *
                (1 - p) ^ (r * r * Δ₂)) := by field_simp
          _ ≤ ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D) :=
              mul_le_mul_of_nonneg_left hpow_le (inv_nonneg.mpr hpos_f.le)
      have h1 : μ ≤ ((1 - p) ^ (r * r * Δ₂))⁻¹ * D_exp := by
        rw [hμ_eq]
        calc ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card
            ≤ ∑ _e ∈ Ev, (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D)) :=
              sum_le_sum hterm
          _ = (D : ℝ) * (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D)) := by
              rw [Finset.sum_const, nsmul_eq_mul, hEv_card]
          _ = ((1 - p) ^ (r * r * Δ₂))⁻¹ * D_exp := by simp only [D_exp]; ring
      have hinv2 : ((1 - p) ^ (r * r * Δ₂))⁻¹ ≤ 1 + η₁ / 2 := by
        have hmul : 4 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤
            2 * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
          have hnn : 0 ≤ (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by positivity
          have := mul_le_mul_of_nonneg_right hε_half hnn
          linarith
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right hinv2 (by positivity))
    -- Upper bound `E[X_v^2]`.
    have hE_X2 : ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 ≤
        (r : ℝ) * (Δ₂ : ℝ) * (D : ℝ) + ((1 - p) ^ (r * r * Δ₂))⁻¹ * μ ^ 2 := by
      have hexp : ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 =
          ∑ e₁ ∈ Ev, ∑ e₂ ∈ Ev,
            (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card := by
        have h1 : ∀ ω, P ω * (X_of v ω : ℝ) ^ 2 =
            ∑ e₁ ∈ Ev, ∑ e₂ ∈ Ev,
              if (∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false) then P ω else 0 := by
          intro ω
          have hcard : (X_of v ω : ℝ) = ∑ e ∈ Ev, if (∀ f ∈ N_all (e.erase v), ω f = false) then (1 : ℝ) else 0 := by
            have hce : X_of v ω = (Ev.filter (fun e ↦ ∀ f ∈ N_all (e.erase v), ω f = false)).card := by
              simp only [X_of, Ev, Finset.filter_filter]
            rw [hce, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [sq, hcard, Finset.sum_mul, Finset.mul_sum]
          refine sum_congr rfl fun e₁ _ ↦ ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine sum_congr rfl fun e₂ _ ↦ ?_
          by_cases h1 : ∀ f ∈ N_all (e₁.erase v), ω f = false
          · by_cases h2 : ∀ f ∈ N_all (e₂.erase v), ω f = false
            · have hu : ∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false := fun f hf ↦ by
                rcases mem_union.mp hf with hf1 | hf2
                · exact h1 f hf1
                · exact h2 f hf2
              rw [if_pos h1, if_pos h2, if_pos hu]; ring
            · have hu : ¬(∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false) := fun ha ↦
                h2 fun f hf ↦ ha f (mem_union_right _ hf)
              rw [if_pos h1, if_neg h2, if_neg hu]; ring
          · have hu : ¬(∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false) := fun ha ↦
              h1 fun f hf ↦ ha f (mem_union_left _ hf)
            rw [if_neg h1, if_neg hu]; ring
        simp_rw [h1]
        rw [Finset.sum_comm]
        refine sum_congr rfl fun e₁ _ ↦ ?_
        rw [Finset.sum_comm]
        refine sum_congr rfl fun e₂ _ ↦ ?_
        rw [← Finset.sum_filter, bern_sum_all_false p _]
      rw [hexp]
      -- Split each inner sum into overlapping (`(e₁.erase v ∩ e₂.erase v).Nonempty`) and disjoint.
      have hterm_split : ∀ e₁ ∈ Ev,
          ∑ e₂ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
            (r : ℝ) * (Δ₂ : ℝ) +
            ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ := by
        intro e₁ he₁
        let Ev_ov : Finset (Finset α) := Ev.filter (fun e₂ ↦ (e₁.erase v ∩ e₂.erase v).Nonempty)
        let Ev_dj : Finset (Finset α) := Ev.filter (fun e₂ ↦ ¬(e₁.erase v ∩ e₂.erase v).Nonempty)
        have hpart : ∑ e₂ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card =
            ∑ e₂ ∈ Ev_ov, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card +
            ∑ e₂ ∈ Ev_dj, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card :=
          (Finset.sum_filter_add_sum_filter_not Ev _ _).symm
        rw [hpart]
        -- Bound overlapping part by `r * Δ₂`.
        have hov_le : ∑ e₂ ∈ Ev_ov, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
            (r : ℝ) * (Δ₂ : ℝ) := by
          have hov_card : Ev_ov.card ≤ r * Δ₂ := by
            have hsub_ov : Ev_ov ⊆ (e₁.erase v).biUnion (fun u ↦ ℰ_reg.filter (fun f ↦ v ∈ f ∧ u ∈ f)) := by
              intro e₂ he₂
              obtain ⟨he₂Ev, ⟨u, hu⟩⟩ := mem_filter.mp he₂
              exact mem_biUnion.mpr ⟨u, (mem_inter.mp hu).1,
                mem_filter.mpr ⟨(mem_filter.mp he₂Ev).1, (mem_filter.mp he₂Ev).2,
                  (mem_erase.mp (mem_inter.mp hu).2).2⟩⟩
            calc Ev_ov.card
                ≤ ((e₁.erase v).biUnion (fun u ↦ ℰ_reg.filter (fun f ↦ v ∈ f ∧ u ∈ f))).card :=
                  card_le_card hsub_ov
              _ ≤ ∑ u ∈ e₁.erase v, (ℰ_reg.filter (fun f ↦ v ∈ f ∧ u ∈ f)).card := card_biUnion_le
              _ ≤ ∑ _u ∈ e₁.erase v, Δ₂ := sum_le_sum fun u hu ↦
                  hcodeg v hv u ((hunif e₁ (mem_filter.mp he₁).1).1 (mem_erase.mp hu).2)
                    (mem_erase.mp hu).1.symm
              _ = (e₁.erase v).card * Δ₂ := by simp
              _ ≤ r * Δ₂ := Nat.mul_le_mul_right Δ₂
                  ((card_erase_le).trans (hunif e₁ (mem_filter.mp he₁).1).2.le)
          calc ∑ e₂ ∈ Ev_ov, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
              ≤ ∑ _e₂ ∈ Ev_ov, (1 : ℝ) := sum_le_sum fun _ _ ↦ pow_le_one₀ (by linarith) (by linarith)
            _ = (Ev_ov.card : ℝ) := by simp
            _ ≤ (r : ℝ) * (Δ₂ : ℝ) := by exact_mod_cast hov_card
        -- Bound disjoint part by `((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p)^(N_all (e₁.erase v)) * μ`.
        have hdj_le : ∑ e₂ ∈ Ev_dj, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
            ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ := by
          have hterm_dj : ∀ e₂ ∈ Ev_dj,
              (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
                ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card *
                  (1 - p) ^ (N_all (e₂.erase v)).card := by
            intro e₂ he₂
            have he₂Ev : e₂ ∈ Ev := (mem_filter.mp he₂).1
            have hdisj12 : Disjoint (e₁.erase v) (e₂.erase v) :=
              Finset.disjoint_iff_inter_eq_empty.mpr
                (Finset.not_nonempty_iff_eq_empty.mp (mem_filter.mp he₂).2)
            have hinter_le : (N_all (e₁.erase v) ∩ N_all (e₂.erase v)).card ≤ r * r * Δ₂ := by
              have hsubI : (N_all (e₁.erase v) ∩ N_all (e₂.erase v)).image Subtype.val ⊆
                  ((e₁.erase v) ×ˢ (e₂.erase v)).biUnion
                    (fun q ↦ ℰ_reg.filter (fun f ↦ q.1 ∈ f ∧ q.2 ∈ f)) := by
                intro f hf
                obtain ⟨f', hf', rfl⟩ := mem_image.mp hf
                obtain ⟨hf1, hf2⟩ := mem_inter.mp hf'
                obtain ⟨u₁, hu₁⟩ := (mem_filter.mp hf1).2
                obtain ⟨u₂, hu₂⟩ := (mem_filter.mp hf2).2
                exact mem_biUnion.mpr ⟨(u₁, u₂), mem_product.mpr ⟨(mem_inter.mp hu₁).2, (mem_inter.mp hu₂).2⟩,
                  mem_filter.mpr ⟨f'.2, (mem_inter.mp hu₁).1, (mem_inter.mp hu₂).1⟩⟩
              calc (N_all (e₁.erase v) ∩ N_all (e₂.erase v)).card
                  = ((N_all (e₁.erase v) ∩ N_all (e₂.erase v)).image Subtype.val).card :=
                    (Finset.card_image_of_injective _ Subtype.val_injective).symm
                _ ≤ (((e₁.erase v) ×ˢ (e₂.erase v)).biUnion
                      (fun q ↦ ℰ_reg.filter (fun f ↦ q.1 ∈ f ∧ q.2 ∈ f))).card := card_le_card hsubI
                _ ≤ ∑ q ∈ (e₁.erase v) ×ˢ (e₂.erase v),
                      (ℰ_reg.filter (fun f ↦ q.1 ∈ f ∧ q.2 ∈ f)).card := card_biUnion_le
                _ ≤ ∑ _q ∈ (e₁.erase v) ×ˢ (e₂.erase v), Δ₂ := by
                    refine sum_le_sum fun q hq ↦ ?_
                    have hq1 := (mem_product.mp hq).1
                    have hq2 := (mem_product.mp hq).2
                    have hqne : q.1 ≠ q.2 := fun h ↦ Finset.disjoint_left.mp hdisj12 hq1 (h ▸ hq2)
                    exact hcodeg q.1 ((hunif e₁ (mem_filter.mp he₁).1).1 (mem_erase.mp hq1).2)
                      q.2 ((hunif e₂ (mem_filter.mp he₂Ev).1).1 (mem_erase.mp hq2).2) hqne
                _ = (e₁.erase v).card * (e₂.erase v).card * Δ₂ := by simp [card_product]
                _ ≤ r * r * Δ₂ := Nat.mul_le_mul_right Δ₂ (Nat.mul_le_mul
                    ((card_erase_le).trans (hunif e₁ (mem_filter.mp he₁).1).2.le)
                    ((card_erase_le).trans (hunif e₂ (mem_filter.mp he₂Ev).1).2.le))
            have hcard_u : (N_all (e₁.erase v)).card + (N_all (e₂.erase v)).card ≤
                (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card + r * r * Δ₂ := by
              have := Finset.card_union_add_card_inter (N_all (e₁.erase v)) (N_all (e₂.erase v))
              omega
            have hpow_le : (1 - p) ^ ((N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card + r * r * Δ₂) ≤
                (1 - p) ^ ((N_all (e₁.erase v)).card + (N_all (e₂.erase v)).card) :=
              pow_le_pow_of_le_one (by linarith) (by linarith) hcard_u
            rw [pow_add, pow_add] at hpow_le
            have hpos_f : 0 < (1 - p) ^ (r * r * Δ₂) := pow_pos (by linarith) _
            calc (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
                = ((1 - p) ^ (r * r * Δ₂))⁻¹ *
                    ((1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card *
                      (1 - p) ^ (r * r * Δ₂)) := by field_simp
              _ ≤ ((1 - p) ^ (r * r * Δ₂))⁻¹ *
                    ((1 - p) ^ (N_all (e₁.erase v)).card * (1 - p) ^ (N_all (e₂.erase v)).card) :=
                  mul_le_mul_of_nonneg_left hpow_le (inv_nonneg.mpr hpos_f.le)
              _ = _ := by ring
          calc ∑ e₂ ∈ Ev_dj, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
              ≤ ∑ e₂ ∈ Ev_dj, (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card *
                  (1 - p) ^ (N_all (e₂.erase v)).card) := sum_le_sum hterm_dj
            _ ≤ ∑ e₂ ∈ Ev, (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card *
                  (1 - p) ^ (N_all (e₂.erase v)).card) :=
                sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                  (fun _ _ _ ↦ by positivity)
            _ = ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ := by
                rw [← Finset.mul_sum, ← hμ_eq]
        exact add_le_add hov_le hdj_le
      calc ∑ e₁ ∈ Ev, ∑ e₂ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
          ≤ ∑ e₁ ∈ Ev, ((r : ℝ) * (Δ₂ : ℝ) +
              ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ) :=
            sum_le_sum hterm_split
        _ = (D : ℝ) * ((r : ℝ) * (Δ₂ : ℝ)) +
            ((1 - p) ^ (r * r * Δ₂))⁻¹ * (∑ e₁ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v)).card) * μ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hEv_card,
              ← Finset.sum_mul, ← Finset.mul_sum]
        _ = (r : ℝ) * (Δ₂ : ℝ) * (D : ℝ) + ((1 - p) ^ (r * r * Δ₂))⁻¹ * μ ^ 2 := by
            rw [← hμ_eq]; ring
    -- Apply Chebyshev to `X_of v`.
    have hμ_le_D : μ ≤ (D : ℝ) := by
      rw [hμ_eq]
      calc ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card
          ≤ ∑ _e ∈ Ev, (1 : ℝ) := sum_le_sum fun _ _ ↦ pow_le_one₀ (by linarith) (by linarith)
        _ = (D : ℝ) := by simp [hEv_card]
    have hμ_nn : 0 ≤ μ := by
      rw [hμ_eq]; exact sum_nonneg fun _ _ ↦ pow_nonneg (by linarith) _
    have hvar : ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 ≤
        ((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2 := by
      have hid : ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 =
          ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 - μ ^ 2 := by
        have h1 : ∀ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 =
            P ω * (X_of v ω : ℝ) ^ 2 - 2 * μ * (P ω * (X_of v ω : ℝ)) + μ ^ 2 * P ω := fun ω ↦ by ring
        simp_rw [h1]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hP_sum]
        change ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 - 2 * μ * μ + μ ^ 2 * 1 = _
        ring
      rw [hid]
      have hε_q : 4 * ε ≤ 1 := by
        have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
        nlinarith
      have hdiff_inv : ((1 - p) ^ (r * r * Δ₂))⁻¹ - 1 ≤ (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
        have : 0 ≤ (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by positivity
        nlinarith
      have hμ2 : μ ^ 2 ≤ (D : ℝ) ^ 2 := pow_le_pow_left₀ hμ_nn hμ_le_D 2
      have h1 : (((1 - p) ^ (r * r * Δ₂))⁻¹ - 1) * μ ^ 2 ≤
          ((r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ))) * (D : ℝ) ^ 2 :=
        mul_le_mul hdiff_inv hμ2 (sq_nonneg μ) (by positivity)
      have h2 : (r : ℝ) * (Δ₂ : ℝ) * (D : ℝ) = (r : ℝ) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2 := by
        field_simp
      linarith
    have hgap : (η₁ / 4) * (D : ℝ) ≤ (D' : ℝ) - μ := by
      have hD'_lo : (1 + η₁) * D_exp ≤ (D' : ℝ) := hD'_arg ▸ Nat.le_ceil _
      nlinarith
    have hcheb : ((η₁ / 4) * (D : ℝ)) ^ 2 *
        ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω ≤
        ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), ((η₁ / 4) * (D : ℝ)) ^ 2 * P ω
          ≤ ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω * ((X_of v ω : ℝ) - μ) ^ 2 := by
            refine sum_le_sum fun ω hω ↦ ?_
            have hlt : (D' : ℝ) < (X_of v ω : ℝ) := by exact_mod_cast (mem_filter.mp hω).2
            have hle_sq : ((η₁ / 4) * (D : ℝ)) ^ 2 ≤ ((X_of v ω : ℝ) - μ) ^ 2 :=
              pow_le_pow_left₀ (by positivity) (by linarith) 2
            rw [mul_comm (P ω)]
            exact mul_le_mul_of_nonneg_right hle_sq (hP_nn ω)
        _ ≤ ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _)
              (fun ω _ _ ↦ mul_nonneg (hP_nn ω) (sq_nonneg _))
    have hcomb := hcheb.trans hvar
    have hpos_den : 0 < ((η₁ / 4) * (D : ℝ)) ^ 2 := by positivity
    have hdiv : ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω ≤
        (((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2) /
          (((η₁ / 4) * (D : ℝ)) ^ 2) := (le_div_iff₀' hpos_den).mpr hcomb
    have hsimp : (((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2) /
        (((η₁ / 4) * (D : ℝ)) ^ 2) =
        16 * ((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) / η₁ ^ 2 := by
      field_simp; ring
    rw [hsimp] at hdiv
    refine hdiv.trans ?_
    rw [div_le_div_iff₀ (sq_pos_of_pos hη₁0) hr_pos]
    nlinarith
  -- Expectation of deleted edges `ℰ'_of ω \ ℰ_rem_of ω`.
  have hE_lost : ∑ ω, P ω * ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) ≤ η₁ * (ℰ_orig.card : ℝ) := by
    have hdet : ∀ ω, ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) ≤
        ∑ v ∈ U, if D' < X_of v ω then ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) else 0 := by
      intro ω
      have hsub_l : ℰ'_of ω \ ℰ_rem_of ω ⊆
          (B_of ω).biUnion (fun v ↦ ℰ_orig.filter (fun e ↦ v ∈ e)) := by
        intro e he
        obtain ⟨he', hnot⟩ := mem_sdiff.mp he
        have he_orig : e ∈ ℰ_orig := (mem_filter.mp he').1
        have hnd : ¬Disjoint e (B_of ω) := fun hd ↦ hnot (mem_filter.mpr ⟨he', hd⟩)
        rw [Finset.not_disjoint_iff] at hnd
        obtain ⟨v, hve, hvB⟩ := hnd
        exact mem_biUnion.mpr ⟨v, hvB, mem_filter.mpr ⟨he_orig, hve⟩⟩
      have hcard_l : (ℰ'_of ω \ ℰ_rem_of ω).card ≤
          ∑ v ∈ B_of ω, (ℰ_orig.filter (fun e ↦ v ∈ e)).card :=
        (card_le_card hsub_l).trans card_biUnion_le
      have hcard_r : ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) ≤
          ∑ v ∈ B_of ω, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) := by exact_mod_cast hcard_l
      rwa [Finset.sum_filter] at hcard_r
    calc ∑ ω, P ω * ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ)
        ≤ ∑ ω, P ω * (∑ v ∈ U, if D' < X_of v ω then ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) else 0) :=
          sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hdet ω) (hP_nn ω)
      _ = ∑ v ∈ U, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) *
            ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine sum_congr rfl fun v _ ↦ ?_
          rw [Finset.sum_filter]
          refine sum_congr rfl fun ω _ ↦ by split_ifs <;> ring
      _ ≤ ∑ v ∈ U, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) * (η₁ / (r : ℝ)) :=
          sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left (hbad_prob v hv) (Nat.cast_nonneg _)
      _ = (η₁ / (r : ℝ)) * ∑ v ∈ U, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]
      _ = (η₁ / (r : ℝ)) * ((r : ℝ) * (ℰ_orig.card : ℝ)) := by
          congr 1
          have hdc : ∑ v ∈ U, (ℰ_orig.filter (fun e ↦ v ∈ e)).card = r * ℰ_orig.card := by
            calc ∑ v ∈ U, (ℰ_orig.filter (fun e ↦ v ∈ e)).card
                = ∑ v ∈ U, ∑ e ∈ ℰ_orig, if v ∈ e then 1 else 0 := by
                  refine sum_congr rfl fun v _ ↦ by
                    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
              _ = ∑ e ∈ ℰ_orig, ∑ v ∈ U, if v ∈ e then 1 else 0 := Finset.sum_comm
              _ = ∑ e ∈ ℰ_orig, r := by
                  refine sum_congr rfl fun e he ↦ ?_
                  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
                  have hesub := (hunif e (hsub he)).1
                  have heq : U.filter (fun v ↦ v ∈ e) = e := by
                    ext v; simp only [mem_filter]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hesub h, h⟩⟩
                  rw [heq, (hunif e (hsub he)).2]
              _ = r * ℰ_orig.card := by simp [mul_comm]
          exact_mod_cast hdc
      _ = η₁ * (ℰ_orig.card : ℝ) := by field_simp
  -- Combine expectations for `ℰ_rem_of` and `ℳ₁_of`.
  have hE_rem : ((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ) ≤
      ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) := by
    have hcard_diff : ∀ ω, ((ℰ'_of ω).card : ℝ) - ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) =
        ((ℰ_rem_of ω).card : ℝ) := by
      intro ω
      have := Finset.card_sdiff_add_card_eq_card (filter_subset (fun e ↦ Disjoint e (B_of ω)) (ℰ'_of ω))
      have : ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) + ((ℰ_rem_of ω).card : ℝ) = ((ℰ'_of ω).card : ℝ) := by
        exact_mod_cast this
      linarith
    have hsum_eq : ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) =
        ∑ ω, P ω * ((ℰ'_of ω).card : ℝ) - ∑ ω, P ω * ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine sum_congr rfl fun ω _ ↦ by rw [← hcard_diff ω]; ring
    linarith
  have hratio : 1 - ε - 4 * η₁ ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) / (D' : ℝ) := by
    have hsplit_pow : (1 - p) ^ (r * D) = (1 - p) ^ D * (1 - p) ^ ((r - 1) * D) := by
      rw [← pow_add]; congr 1
      have : D + (r - 1) * D = (1 + (r - 1)) * D := by ring
      rw [this, Nat.add_sub_cancel' (by omega : 1 ≤ r)]
    have h1pD : 1 - ε ≤ (1 - p) ^ D := by
      have := one_sub_mul_le_pow hp0 hp1 D
      have hmul : (D : ℝ) * p = ε := by simp only [p]; field_simp
      rwa [hmul] at this
    have hnum : (1 - ε - 2 * η₁) * D_exp ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) := by
      rw [hsplit_pow]
      have h1 : (1 - p) ^ D * (1 - p) ^ ((r - 1) * D) * (D : ℝ) - η₁ * (D : ℝ) =
          (1 - p) ^ D * D_exp - η₁ * (D : ℝ) := by simp only [D_exp]; ring
      have h2 : η₁ * (D : ℝ) ≤ 2 * η₁ * D_exp := by nlinarith
      nlinarith
    have h3 : (1 - ε - 4 * η₁) * (1 + 2 * η₁) ≤ 1 - ε - 2 * η₁ := by
      have : ε ≤ 1 / 4 := by
        have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
        nlinarith
      nlinarith
    rw [le_div_iff₀ hD'_pos]
    by_cases hneg : 0 ≤ 1 - ε - 4 * η₁
    · calc (1 - ε - 4 * η₁) * (D' : ℝ)
          ≤ (1 - ε - 4 * η₁) * ((1 + 2 * η₁) * D_exp) := mul_le_mul_of_nonneg_left hD'_le hneg
        _ = ((1 - ε - 4 * η₁) * (1 + 2 * η₁)) * D_exp := by ring
        _ ≤ (1 - ε - 2 * η₁) * D_exp := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) := hnum
    · push Not at hneg
      have hle1 : (1 - ε - 4 * η₁) * (D' : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg.le hD'_pos.le
      have h1prD : 1 - (r : ℝ) * ε ≤ (1 - p) ^ (r * D) := by
        have := one_sub_mul_le_pow hp0 hp1 (r * D)
        have hmul : ((r * D : ℕ) : ℝ) * p = (r : ℝ) * ε := by
          rw [Nat.cast_mul]; simp only [p]; field_simp
        rwa [hmul] at this
      have hrhs_nn : 0 ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) :=
        mul_nonneg (by linarith) hD_pos.le
      exact hle1.trans hrhs_nn
  -- Linearity of expectation gives an outcome `ω₀` attaining at least the mean!
  let target : ℝ :=
    (ε * (1 - (r : ℝ) * ε) + c_next * (1 - ε - 4 * η₁)) * ((ℰ_orig.card : ℝ) / (D : ℝ))
  have hE_total : target ≤
      ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) := by
    have h1 : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) =
        ∑ ω, P ω * ((ℳ₁_of ω).card : ℝ) +
        (c_next / (D' : ℝ)) * ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      refine sum_congr rfl fun ω _ ↦ by ring
    rw [h1]
    have h2 : c_next * (1 - ε - 4 * η₁) * ((ℰ_orig.card : ℝ) / (D : ℝ)) ≤
        (c_next / (D' : ℝ)) * (((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hratio (div_nonneg (Nat.cast_nonneg ℰ_orig.card) hD_pos.le)) hc_nn
      have hrew : c_next * (((1 - p) ^ (r * D) - η₁) * (D : ℝ) / (D' : ℝ) *
          ((ℰ_orig.card : ℝ) / (D : ℝ))) =
          (c_next / (D' : ℝ)) * (((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ)) := by
        field_simp
      linarith
    have h3 : (c_next / (D' : ℝ)) * (((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ)) ≤
        (c_next / (D' : ℝ)) * ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) :=
      mul_le_mul_of_nonneg_left hE_rem (div_nonneg hc_nn hD'_pos.le)
    simp only [target]
    linarith
  have hex_ω : ∃ ω, target ≤
      ((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ)) := by
    by_contra hall
    push Not at hall
    have hlt : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) <
        target := by
      have hle_t : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) ≤
          ∑ ω, P ω * target := sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hall ω).le (hP_nn ω)
      have hstrict : ∃ ω, 0 < P ω := by
        by_contra h0
        push Not at h0
        have : ∑ ω, P ω ≤ 0 := sum_nonpos fun ω _ ↦ h0 ω
        linarith
      obtain ⟨ω₁, hω₁⟩ := hstrict
      have hlt_s : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) <
          ∑ ω, P ω * target :=
        Finset.sum_lt_sum (fun ω _ ↦ mul_le_mul_of_nonneg_left (hall ω).le (hP_nn ω))
          ⟨ω₁, mem_univ ω₁, mul_lt_mul_of_pos_left (hall ω₁) hω₁⟩
      rwa [← Finset.sum_mul, hP_sum, one_mul] at hlt_s
    linarith
  obtain ⟨ω₀, hω₀⟩ := hex_ω
  refine ⟨ℳ₁_of ω₀, ℰ_rem_of ω₀, filter_subset _ _, (filter_subset _ _).trans (filter_subset _ _),
    ?_, ?_, ?_, hD'_ge, hω₀⟩
  · -- `ℳ₁_of ω₀` is a matching!
    intro e₁ he₁ e₂ he₂ hne
    obtain ⟨he₁_reg, hω₁, hiso₁⟩ := (mem_filter.mp he₁).2
    obtain ⟨he₂_reg, hω₂, _⟩ := (mem_filter.mp he₂).2
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hf_mem : (⟨e₂, he₂_reg⟩ : { e // e ∈ ℰ_reg }) ∈ (N_all e₁).erase ⟨e₁, he₁_reg⟩ :=
      mem_erase.mpr ⟨fun h ↦ hne (congrArg Subtype.val h).symm,
        mem_filter.mpr ⟨mem_univ _, ⟨v, mem_inter.mpr ⟨hv₂, hv₁⟩⟩⟩⟩
    have := hiso₁ ⟨e₂, he₂_reg⟩ hf_mem
    rw [hω₂] at this
    exact Bool.noConfusion this
  · -- `ℳ₁_of ω₀` and `ℰ_rem_of ω₀` are vertex-disjoint!
    intro e₁ he₁ e₂ he₂
    obtain ⟨he₁_reg, hω₁, _⟩ := (mem_filter.mp he₁).2
    have hrem2 := (mem_filter.mp (mem_filter.mp he₂).1).2
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hf_mem : (⟨e₁, he₁_reg⟩ : { e // e ∈ ℰ_reg }) ∈ N_all e₂ :=
      mem_filter.mpr ⟨mem_univ _, ⟨v, mem_inter.mpr ⟨hv₁, hv₂⟩⟩⟩
    have := hrem2 ⟨e₁, he₁_reg⟩ hf_mem
    rw [hω₁] at this
    exact Bool.noConfusion this
  · -- Max degree of `ℰ_rem_of ω₀` is `≤ D'`!
    intro v hv
    by_cases hvB : v ∈ B_of ω₀
    · have hemp : (ℰ_rem_of ω₀).filter (fun e ↦ v ∈ e) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨her, hve⟩ := mem_filter.mp he
        exact Finset.disjoint_left.mp (mem_filter.mp her).2 hve hvB
      simp [hemp]
    · have hle_X : X_of v ω₀ ≤ D' := by
        by_contra hgt; push Not at hgt
        exact hvB (mem_filter.mpr ⟨hv, hgt⟩)
      have hsub_X : (ℰ_rem_of ω₀).filter (fun e ↦ v ∈ e) ⊆
          ℰ_reg.filter (fun e ↦ v ∈ e ∧ ∀ f ∈ N_all (e.erase v), ω₀ f = false) := by
        intro e he
        obtain ⟨her, hve⟩ := mem_filter.mp he
        have he' := (mem_filter.mp her).1
        refine mem_filter.mpr ⟨hsub (mem_filter.mp he').1, hve, fun f hf ↦ ?_⟩
        apply (mem_filter.mp he').2 f
        obtain ⟨u, hu⟩ := (mem_filter.mp hf).2
        exact mem_filter.mpr ⟨mem_univ f, ⟨u, mem_inter.mpr ⟨(mem_inter.mp hu).1,
          (mem_erase.mp (mem_inter.mp hu).2).2⟩⟩⟩
      exact (card_le_card hsub_X).trans hle_X

lemma nibble_T_rounds (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε0 : 0 < ε) (hε_small : 4 * (r : ℝ) * ε ≤ 1)
    (T : ℕ) :
    let η₁ : ℝ := ε ^ 2
    let c_T : ℝ := (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T)
    ∃ β : ℝ, 0 < β ∧ ∃ D₀ : ℕ, 1 ≤ D₀ ∧
      ∀ {α : Type*} [DecidableEq α] (U : Finset α) (ℰ : Finset (Finset α)) (D : ℕ),
        D₀ ≤ D →
        (∀ e ∈ ℰ, e ⊆ U ∧ e.card = r) →
        (∀ x ∈ U, (ℰ.filter (fun e ↦ x ∈ e)).card ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → ((ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card : ℝ) ≤ β * (D : ℝ)) →
        ∃ ℳ : Finset (Finset α), ℳ ⊆ ℰ ∧
          (∀ e₁ ∈ ℳ, ∀ e₂ ∈ ℳ, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
          c_T * ((ℰ.card : ℝ) / (D : ℝ)) ≤ (ℳ.card : ℝ) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hε_le_q : ε ≤ 1 / 8 := by
    have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  let η₁ : ℝ := ε ^ 2
  have hη₁0 : 0 < η₁ := sq_pos_of_pos hε0
  have hη₁_le : η₁ ≤ 1 / 4 := by simp only [η₁]; nlinarith
  induction T with
  | zero =>
    refine ⟨1, zero_lt_one, 1, le_rfl, fun U ℰ D _ _ _ _ ↦ ⟨∅, empty_subset _, by simp, by simp⟩⟩
  | succ T ih =>
    obtain ⟨β_T, hβ_T0, D_T, hD_T1, hIH⟩ := ih
    let c_T : ℝ := (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T)
    have hc_T_nn : 0 ≤ c_T := by
      have h1 : 0 ≤ 1 - (r : ℝ) * ε := by nlinarith
      have h2 : (1 - ε - 4 * η₁) ^ T ≤ 1 := pow_le_one₀ (by simp only [η₁]; nlinarith)
        (by simp only [η₁]; nlinarith)
      exact mul_nonneg (div_nonneg (mul_nonneg hε0.le h1) (by positivity)) (by linarith)
    let β_raw : ℝ := min (β_T / 4) (min (η₁ / (8 * (r : ℝ) ^ 2))
      (η₁ ^ 3 / (64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ))))
    have hβ0 : 0 < β_raw := lt_min (by positivity) (lt_min (by positivity) (by positivity))
    let D₀ : ℕ := max (max (2 * D_T) (Nat.ceil (2 / η₁))) (Nat.ceil (1 / β_raw))
    have hD₀1 : 1 ≤ D₀ := le_trans (by omega : 1 ≤ 2 * D_T)
      (le_trans (le_max_left _ _) (le_max_left _ _))
    refine ⟨β_raw, hβ0, D₀, hD₀1, fun {α} _ U ℰ D hD hunif hdeg hcodeg ↦ ?_⟩
    have hD1 : 1 ≤ D := hD₀1.trans hD
    have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
    let Δ₂ : ℕ := Nat.floor (β_raw * (D : ℝ))
    have hΔ₂_le : (Δ₂ : ℝ) ≤ β_raw * (D : ℝ) := Nat.floor_le (by positivity)
    have hcodeg_nat : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card ≤ Δ₂ :=
      fun x hx y hy hxy ↦ Nat.le_floor (hcodeg x hx y hy hxy)
    -- Step A: Regularize `ℋ` via affine lines over `ZMod p_prime`.
    obtain ⟨p_prime, hp_fact, ℰ_orig, ℰ_reg, hsub_or, hunif_reg, hreg_deg, hreg_codeg,
      hcard_orig, hpigeon⟩ := regularize_hypergraph U ℰ r D Δ₂ hr hD1 hunif hdeg hcodeg_nat
    let W : Finset (Fin r × ZMod p_prime) := Finset.univ
    -- Note `max Δ₂ 1 ≤ 2 * β_raw * D` since `D ≥ 1 / β_raw`.
    have h1_le_βD : 1 ≤ β_raw * (D : ℝ) := by
      have h1 : 1 / β_raw ≤ (D : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hD)
      have := (div_le_iff₀ hβ0).mp h1
      linarith
    have hΔ₂_reg_le : ((max Δ₂ 1 : ℕ) : ℝ) / (D : ℝ) ≤ 2 * β_raw := by
      have hmax : ((max Δ₂ 1 : ℕ) : ℝ) ≤ 2 * β_raw * (D : ℝ) := by
        rw [Nat.cast_max]; simp only [Nat.cast_one]
        exact max_le (by linarith) (by linarith)
      exact (div_le_iff₀ hD_pos).mpr hmax
    have hβ_small' : 4 * (r : ℝ) ^ 2 * (((max Δ₂ 1 : ℕ) : ℝ) / (D : ℝ)) ≤ η₁ := by
      have h1 : β_raw ≤ η₁ / (8 * (r : ℝ) ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
      have h2 : 8 * (r : ℝ) ^ 2 * β_raw ≤ η₁ := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r : ℝ) ^ 2)).mp h1
        linarith
      have h3 := mul_le_mul_of_nonneg_left hΔ₂_reg_le (by positivity : (0 : ℝ) ≤ 4 * (r : ℝ) ^ 2)
      linarith
    have hβ_cheb' : 32 * ((r : ℝ) + (r : ℝ) ^ 2) * (((max Δ₂ 1 : ℕ) : ℝ) / (D : ℝ)) * (r : ℝ) ≤ η₁ ^ 3 := by
      have h1 : β_raw ≤ η₁ ^ 3 / (64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have h2 : 64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ) * β_raw ≤ η₁ ^ 3 := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ))).mp h1
        linarith
      have h3 := mul_le_mul_of_nonneg_left hΔ₂_reg_le
        (by positivity : (0 : ℝ) ≤ 32 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ))
      linarith
    have hD_η' : 2 ≤ η₁ * (D : ℝ) := by
      have h1 : 2 / η₁ ≤ (D : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_left _ _)).trans hD)
      have := (div_le_iff₀ hη₁0).mp h1
      linarith
    -- Step B: Apply one nibble step to `(ℰ_orig, ℰ_reg)`.
    obtain ⟨ℳ₁, ℰ_rem, hℳ₁_sub, hℰ_rem_sub, hℳ₁_disj, hdisj_12, hdeg_rem, hD'_ge, hgain⟩ :=
      nibble_one_step (W ×ˢ U) ℰ_orig ℰ_reg r D (max Δ₂ 1) ε η₁ c_T hr hD1 hε0 hε_small
        hη₁0 hη₁_le hc_T_nn hβ_small' hβ_cheb' hD_η' hsub_or hunif_reg hreg_deg hreg_codeg
    let D' : ℕ := Nat.ceil ((1 + η₁) * (1 - ε / (D : ℝ)) ^ ((r - 1) * D) * (D : ℝ))
    -- Step C: Apply induction hypothesis for `T` rounds to `ℰ_rem`!
    have hD'_ge_DT : D_T ≤ D' := by
      have h2DT : 2 * D_T ≤ D := ((le_max_left _ _).trans (le_max_left _ _)).trans hD
      have h2DT_r : (D_T : ℝ) ≤ (D : ℝ) / 2 := by
        have : (2 * D_T : ℝ) ≤ (D : ℝ) := by exact_mod_cast h2DT
        linarith
      exact_mod_cast h2DT_r.trans hD'_ge
    have hcodeg_rem : ∀ v₁ ∈ W ×ˢ U, ∀ v₂ ∈ W ×ˢ U, v₁ ≠ v₂ →
        ((ℰ_rem.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card : ℝ) ≤ β_T * (D' : ℝ) := by
      intro v₁ hv₁ v₂ hv₂ hne
      have h1 : (ℰ_rem.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card ≤ max Δ₂ 1 :=
        (card_le_card (filter_subset_filter _ (hℰ_rem_sub.trans hsub_or))).trans
          (hreg_codeg v₁ hv₁ v₂ hv₂ hne)
      have h2 : ((max Δ₂ 1 : ℕ) : ℝ) ≤ 2 * β_raw * (D : ℝ) := (div_le_iff₀ hD_pos).mp hΔ₂_reg_le
      have h3 : 2 * β_raw * (D : ℝ) ≤ β_T * (D' : ℝ) := by
        have hβ_le : β_raw ≤ β_T / 4 := min_le_left _ _
        nlinarith
      exact (by exact_mod_cast h1 : ((ℰ_rem.filter _).card : ℝ) ≤ ((max Δ₂ 1 : ℕ) : ℝ)).trans
        (h2.trans h3)
    obtain ⟨ℳ₂, hℳ₂_sub, hℳ₂_disj, hℳ₂_card⟩ :=
      hIH (W ×ˢ U) ℰ_rem D' hD'_ge_DT
        (fun e he ↦ hunif_reg e (hsub_or (hℰ_rem_sub he))) hdeg_rem hcodeg_rem
    -- Step D: Combine `ℳ₁ ∪ ℳ₂ ⊆ ℰ_orig` and apply pigeonhole over `W`!
    have hdisj_M12 : Disjoint ℳ₁ ℳ₂ := by
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      have hd := hdisj_12 e he₁ e (hℳ₂_sub he₂)
      have hne : e.Nonempty := card_pos.mp (by have := (hunif_reg e (hsub_or (hℳ₁_sub he₁))).2; omega)
      obtain ⟨v, hv⟩ := hne
      exact Finset.disjoint_left.mp hd hv hv
    have hM12_disj : ∀ e₁ ∈ ℳ₁ ∪ ℳ₂, ∀ e₂ ∈ ℳ₁ ∪ ℳ₂, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
      intro e₁ h1 e₂ h2 hne
      rcases mem_union.mp h1 with h1a | h1b <;> rcases mem_union.mp h2 with h2a | h2b
      · exact hℳ₁_disj e₁ h1a e₂ h2a hne
      · exact hdisj_12 e₁ h1a e₂ (hℳ₂_sub h2b)
      · exact (hdisj_12 e₂ h2a e₁ (hℳ₂_sub h1b)).symm
      · exact hℳ₂_disj e₁ h1b e₂ h2b hne
    obtain ⟨ℳ_out, hℳ_out_sub, hℳ_out_disj, hℳ_out_card⟩ :=
      hpigeon (ℳ₁ ∪ ℳ₂) (union_subset hℳ₁_sub (hℳ₂_sub.trans hℰ_rem_sub)) hM12_disj
    refine ⟨ℳ_out, hℳ_out_sub, hℳ_out_disj, ?_⟩
    have hcard_u : ((ℳ₁ ∪ ℳ₂).card : ℝ) = (ℳ₁.card : ℝ) + (ℳ₂.card : ℝ) := by
      exact_mod_cast Finset.card_union_of_disjoint hdisj_M12
    have hrec : (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ (T + 1)) =
        ε * (1 - (r : ℝ) * ε) + c_T * (1 - ε - 4 * η₁) := by
      simp only [c_T, pow_succ]
      have hden : ε + 4 * η₁ ≠ 0 := by positivity
      field_simp; ring
    have hbig : (ε * (1 - (r : ℝ) * ε) + c_T * (1 - ε - 4 * η₁)) *
        ((W.card : ℝ) * ((ℰ.card : ℝ) / (D : ℝ))) ≤ (W.card : ℝ) * (ℳ_out.card : ℝ) := by
      have hcard_r : (ℰ_orig.card : ℝ) = (W.card : ℝ) * (ℰ.card : ℝ) := by exact_mod_cast hcard_orig
      have hrew : (W.card : ℝ) * ((ℰ.card : ℝ) / (D : ℝ)) = (ℰ_orig.card : ℝ) / (D : ℝ) := by
        rw [hcard_r]; ring
      rw [hrew]
      linarith
    have hW_pos : (0 : ℝ) < (W.card : ℝ) := by
      have : 0 < W.card := card_pos.mpr ⟨(⟨0, by omega⟩, 0), mem_univ _⟩
      exact_mod_cast this
    rw [hrec]
    nlinarith

lemma rodl_nibble_matching (r : ℕ) (hr : 2 ≤ r) (γ : ℝ) (hγ : 0 < γ) :
    ∃ β : ℝ, 0 < β ∧ ∃ D₀ : ℕ, 1 ≤ D₀ ∧
      ∀ {α : Type*} [DecidableEq α] (U : Finset α) (ℰ : Finset (Finset α)) (D : ℕ),
        D₀ ≤ D →
        (∀ e ∈ ℰ, e ⊆ U ∧ e.card = r) →
        (∀ x ∈ U, (ℰ.filter (fun e ↦ x ∈ e)).card ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → ((ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card : ℝ) ≤ β * (D : ℝ)) →
        ∃ ℳ : Finset (Finset α), ℳ ⊆ ℰ ∧
          (∀ e₁ ∈ ℳ, ∀ e₂ ∈ ℳ, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
          (1 - γ) * ((ℰ.card : ℝ) / (D : ℝ)) ≤ (ℳ.card : ℝ) := by
  let γ' : ℝ := min γ (1 / 2)
  have hγ'0 : 0 < γ' := lt_min hγ (by norm_num)
  have hγ'_le : γ' ≤ γ := min_le_left _ _
  let ε : ℝ := min (1 / (8 * (r : ℝ))) (γ' / (4 * ((r : ℝ) + 4)))
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_small : 4 * (r : ℝ) * ε ≤ 1 := by
    have : ε ≤ 1 / (8 * (r : ℝ)) := min_le_left _ _
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r : ℝ))).mp this
    linarith
  have hε_γ : ((r : ℝ) + 4) * ε ≤ γ' / 4 := by
    have : ε ≤ γ' / (4 * ((r : ℝ) + 4)) := min_le_right _ _
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((r : ℝ) + 4))).mp this
    linarith
  let T : ℕ := Nat.ceil (2 / (γ' * ε))
  obtain ⟨β, hβ0, D₀, hD₀1, hspec⟩ := nibble_T_rounds r hr ε hε0 hε_small T
  refine ⟨β, hβ0, D₀, hD₀1, fun U ℰ D hD hunif hdeg hcodeg ↦ ?_⟩
  obtain ⟨ℳ, hℳ_sub, hℳ_disj, hℳ_card⟩ := hspec U ℰ D hD hunif hdeg hcodeg
  refine ⟨ℳ, hℳ_sub, hℳ_disj, ?_⟩
  let η₁ : ℝ := ε ^ 2
  have hε_le1 : ε ≤ 1 / 8 := by
    have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  have hfrac : 1 - γ' / 4 ≤ (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) := by
    rw [le_div_iff₀ (by positivity)]
    simp only [η₁]
    have : γ' / 4 * (4 * ε) ≥ 0 := by positivity
    nlinarith
  have hpow_le : (1 - ε - 4 * η₁) ^ T ≤ γ' / 2 := by
    have h1 : (1 - ε - 4 * η₁) ^ T ≤ (1 - ε) ^ T :=
      pow_le_pow_left₀ (by simp only [η₁]; nlinarith) (by simp only [η₁]; nlinarith) T
    have h2 : (1 - ε) ^ T * (1 + (T : ℝ) * ε) ≤ 1 :=
      pow_mul_one_add_le_one hε0.le (by linarith) T
    have hT : 2 / (γ' * ε) ≤ (T : ℝ) := Nat.le_ceil _
    have h3 : 2 / γ' ≤ 1 + (T : ℝ) * ε := by
      have : 2 ≤ (T : ℝ) * (γ' * ε) := (div_le_iff₀ (by positivity)).mp hT
      have : 2 / γ' ≤ (T : ℝ) * ε := (div_le_iff₀ hγ'0).mpr (by linarith)
      linarith
    have h4 : (1 - ε) ^ T * (2 / γ') ≤ 1 := by
      calc (1 - ε) ^ T * (2 / γ') ≤ (1 - ε) ^ T * (1 + (T : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left h3 (pow_nonneg (by linarith) T)
        _ ≤ 1 := h2
    have h5 : (1 - ε) ^ T ≤ γ' / 2 := by
      have hpos : 0 < 2 / γ' := by positivity
      calc (1 - ε) ^ T ≤ 1 / (2 / γ') := (le_div_iff₀ hpos).mpr h4
        _ = γ' / 2 := by field_simp
    exact h1.trans h5
  have hc_ge : 1 - γ ≤ (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T) := by
    have hprod : (1 - γ' / 4) * (1 - γ' / 2) ≤
        (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T) :=
      mul_le_mul hfrac (by linarith) (by have : γ' ≤ 1 / 2 := min_le_right _ _; linarith)
        (div_nonneg (mul_nonneg hε0.le (by linarith)) (by positivity))
    have : 1 - γ' ≤ (1 - γ' / 4) * (1 - γ' / 2) := by nlinarith
    linarith
  exact (mul_le_mul_of_nonneg_right hc_ge
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans hℳ_card


end Green84H2Nibble


/-
# Proof body for `Green84.green_84.variants.littlewood.R1.H2`
-/

namespace Green84H2Proof

open Finset
open scoped Classical

/- ### Section 1: Base-B uniqueness and dimension reduction to ℤ × ℤ -/

lemma abs_sum_range_pow_lt (B : ℕ) (hB : 2 ≤ B) (f : ℕ → ℤ) :
    ∀ k : ℕ, (∀ j < k, 2 * |f j| ≤ (B : ℤ) - 1) →
      2 * |∑ j ∈ range k, f j * (B : ℤ) ^ j| < (B : ℤ) ^ k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hf
    rw [sum_range_succ, pow_succ]
    have h1 := ih (fun j hj ↦ hf j (Nat.lt_succ_of_lt hj))
    have h2 : 2 * |f k| ≤ (B : ℤ) - 1 := hf k (Nat.lt_succ_self k)
    have hBk : (0 : ℤ) < (B : ℤ) ^ k := pow_pos (by omega) k
    have htri : |∑ j ∈ range k, f j * (B : ℤ) ^ j + f k * (B : ℤ) ^ k| ≤
        |∑ j ∈ range k, f j * (B : ℤ) ^ j| + |f k| * (B : ℤ) ^ k := by
      calc |∑ j ∈ range k, f j * (B : ℤ) ^ j + f k * (B : ℤ) ^ k|
          ≤ |∑ j ∈ range k, f j * (B : ℤ) ^ j| + |f k * (B : ℤ) ^ k| := abs_add_le _ _
        _ = |∑ j ∈ range k, f j * (B : ℤ) ^ j| + |f k| * (B : ℤ) ^ k := by
            rw [abs_mul, abs_of_pos hBk]
    nlinarith only [h1, h2, hBk, htri]

lemma sum_fin_pow_ne_zero {n : ℕ} (c : Fin n → ℤ) (B : ℕ) (hB : 2 ≤ B)
    (hc : ∀ i, 2 * |c i| ≤ (B : ℤ) - 1) (hne : ∃ i, c i ≠ 0) :
    ∑ i : Fin n, c i * (B : ℤ) ^ (i : ℕ) ≠ 0 := by
  let S : Finset (Fin n) := univ.filter (fun i ↦ c i ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  let k : Fin n := S.max' hS
  have hkS : k ∈ S := max'_mem S hS
  have hck : c k ≠ 0 := (mem_filter.mp hkS).2
  have hzero : ∀ i : Fin n, k < i → c i = 0 := by
    intro i hi
    by_contra hci
    have hiS : i ∈ S := mem_filter.mpr ⟨mem_univ i, hci⟩
    exact absurd hi (not_lt.mpr (le_max' S i hiS))
  let f : ℕ → ℤ := fun j ↦ if h : j < n then c ⟨j, h⟩ else 0
  have hsum_eq : ∑ i : Fin n, c i * (B : ℤ) ^ (i : ℕ) =
      (∑ j ∈ range k.val, f j * (B : ℤ) ^ j) + c k * (B : ℤ) ^ k.val := by
    have h1 : ∑ i : Fin n, c i * (B : ℤ) ^ (i : ℕ) =
        ∑ j ∈ range n, f j * (B : ℤ) ^ j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ f j * (B : ℤ) ^ j)]
      refine sum_congr rfl fun i _ ↦ ?_
      simp [f, i.isLt]
    rw [h1]
    have hsub : range (k.val + 1) ⊆ range n := range_mono (Nat.succ_le_of_lt k.isLt)
    have h2 : ∑ j ∈ range n, f j * (B : ℤ) ^ j =
        ∑ j ∈ range (k.val + 1), f j * (B : ℤ) ^ j := by
      symm
      refine sum_subset hsub fun j hj hjk ↦ ?_
      have hjn : j < n := mem_range.mp hj
      have hlt : k.val < j := by
        have := mt mem_range.mpr hjk
        omega
      have hcj : c ⟨j, hjn⟩ = 0 := hzero ⟨j, hjn⟩ hlt
      simp [f, hjn, hcj]
    rw [h2, sum_range_succ]
    simp [f, k.isLt]
  rw [hsum_eq]
  have hlt := abs_sum_range_pow_lt B hB f k.val (fun j hj ↦ by
    dsimp [f]
    split_ifs with hjn
    · exact hc ⟨j, hjn⟩
    · omega)
  have hBk : (0 : ℤ) < (B : ℤ) ^ k.val := pow_pos (by omega) k.val
  have hck1 : 1 ≤ |c k| := Int.one_le_abs hck
  have hlead : 2 * (B : ℤ) ^ k.val ≤ 2 * |c k * (B : ℤ) ^ k.val| := by
    rw [abs_mul, abs_of_pos hBk]
    nlinarith only [hBk, hck1]
  intro h0
  have heq : ∑ j ∈ range k.val, f j * (B : ℤ) ^ j = -(c k * (B : ℤ) ^ k.val) := by linarith
  have habs : |∑ j ∈ range k.val, f j * (B : ℤ) ^ j| = |c k * (B : ℤ) ^ k.val| := by
    rw [heq, abs_neg]
  linarith only [hlt, hlead, habs, hBk]

lemma reduce_dim_two (r m : ℕ) (a : Fin r → Fin m → ℤ)
    (ha0 : ∀ i, ∃ k, a i k ≠ 0)
    (hnp : ∀ i j, i ≠ j → ∀ t : ℝ, ¬ ∀ k, (a j k : ℝ) = t * (a i k : ℝ)) :
    ∃ (u v : Fin m → ℤ) (A : Fin r → ℤ × ℤ),
      (∀ i, (A i).1 = ∑ k, a i k * u k ∧ (A i).2 = ∑ k, a i k * v k) ∧
      (∀ i, (A i).1 ≠ 0) ∧
      (∀ i j, i ≠ j → (A i).1 * (A j).2 - (A i).2 * (A j).1 ≠ 0) := by
  let M : ℕ := 1 + ∑ i : Fin r, ∑ k : Fin m, (a i k).natAbs
  let B : ℕ := 4 * M ^ 2 + 2
  have hB2 : 2 ≤ B := by dsimp [B]; omega
  have hbound : ∀ i k, |a i k| ≤ (M : ℤ) := by
    intro i k
    have h1 : (a i k).natAbs ≤ ∑ k' : Fin m, (a i k').natAbs :=
      single_le_sum (f := fun k' : Fin m ↦ (a i k').natAbs) (fun _ _ ↦ Nat.zero_le _) (mem_univ k)
    have h2 : ∑ k' : Fin m, (a i k').natAbs ≤ ∑ i' : Fin r, ∑ k' : Fin m, (a i' k').natAbs :=
      single_le_sum (f := fun i' : Fin r ↦ ∑ k' : Fin m, (a i' k').natAbs)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
    have h3 : (a i k).natAbs ≤ M := by dsimp [M]; omega
    rw [← Int.natCast_natAbs]
    exact_mod_cast h3
  let u : Fin m → ℤ := fun k ↦ (B : ℤ) ^ (k : ℕ)
  let v : Fin m → ℤ := fun k ↦ (B : ℤ) ^ (m * (k : ℕ))
  let A : Fin r → ℤ × ℤ := fun i ↦ (∑ k, a i k * u k, ∑ k, a i k * v k)
  refine ⟨u, v, A, fun i ↦ ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro i
    refine sum_fin_pow_ne_zero (a i) B hB2 (fun k ↦ ?_) (ha0 i)
    have hM1 : (1 : ℤ) ≤ M := by dsimp [M]; omega
    have hle := hbound i k
    have hsq : (M : ℤ) ≤ (M : ℤ) ^ 2 := by nlinarith only [hM1]
    have hBval : (B : ℤ) = 4 * (M : ℤ) ^ 2 + 2 := by simp [B]
    linarith only [hle, hsq, hBval]
  · intro i j hij
    by_cases hm0 : m = 0
    · obtain ⟨k, _⟩ := ha0 i
      have hk := k.isLt
      omega
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    let c : Fin (m * m) → ℤ := fun idx ↦
      let k₁ : Fin m := ⟨idx.val % m, Nat.mod_lt _ hm_pos⟩
      let k₂ : Fin m := ⟨idx.val / m, Nat.div_lt_of_lt_mul idx.isLt⟩
      a i k₁ * a j k₂ - a i k₂ * a j k₁
    have hdet_eq : (A i).1 * (A j).2 - (A i).2 * (A j).1 =
        ∑ idx : Fin (m * m), c idx * (B : ℤ) ^ (idx : ℕ) := by
      have hexp : (A i).1 * (A j).2 - (A i).2 * (A j).1 =
          ∑ k₁ : Fin m, ∑ k₂ : Fin m,
            (a i k₁ * a j k₂ - a i k₂ * a j k₁) * (B : ℤ) ^ (k₁.val + m * k₂.val) := by
        dsimp [A, u, v]
        rw [sum_mul, sum_mul]
        simp_rw [mul_sum]
        rw [sum_comm (s := univ) (t := univ) (f := fun k₂ k₁ ↦ a i k₂ * (B : ℤ) ^ (m * (k₂ : ℕ)) * (a j k₁ * (B : ℤ) ^ (k₁ : ℕ)))]
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun k₁ _ ↦ ?_
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun k₂ _ ↦ ?_
        rw [pow_add]
        ring
      rw [hexp]
      let e : Fin m × Fin m ≃ Fin (m * m) :=
        { toFun := fun p ↦ ⟨p.1.val + m * p.2.val, by nlinarith only [p.1.isLt, p.2.isLt]⟩
          invFun := fun idx ↦ (⟨idx.val % m, Nat.mod_lt _ hm_pos⟩,
            ⟨idx.val / m, Nat.div_lt_of_lt_mul idx.isLt⟩)
          left_inv := fun ⟨k₁, k₂⟩ ↦ by
            ext
            · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k₁.isLt]
            · simp [Nat.add_mul_div_left _ _ hm_pos, Nat.div_eq_of_lt k₁.isLt]
          right_inv := fun idx ↦ by
            ext
            simp [Nat.mod_add_div] }
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv e _ _ fun ⟨k₁, k₂⟩ ↦ ?_
      have h1 : (k₁.val + m * k₂.val) % m = k₁.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k₁.isLt]
      have h2 : (k₁.val + m * k₂.val) / m = k₂.val := by
        rw [Nat.add_mul_div_left _ _ hm_pos, Nat.div_eq_of_lt k₁.isLt, zero_add]
      simp [e, c, h1, h2]
    rw [hdet_eq]
    refine sum_fin_pow_ne_zero c B hB2 (fun idx ↦ ?_) ?_
    · dsimp [c]
      set k₁ : Fin m := ⟨idx.val % m, Nat.mod_lt _ hm_pos⟩
      set k₂ : Fin m := ⟨idx.val / m, Nat.div_lt_of_lt_mul idx.isLt⟩
      have h1 := hbound i k₁
      have h2 := hbound j k₂
      have h3 := hbound i k₂
      have h4 := hbound j k₁
      have habs : |a i k₁ * a j k₂ - a i k₂ * a j k₁| ≤ 2 * (M : ℤ) ^ 2 := by
        calc |a i k₁ * a j k₂ - a i k₂ * a j k₁|
            ≤ |a i k₁ * a j k₂| + |a i k₂ * a j k₁| := abs_sub _ _
          _ = |a i k₁| * |a j k₂| + |a i k₂| * |a j k₁| := by rw [abs_mul, abs_mul]
          _ ≤ (M : ℤ) * (M : ℤ) + (M : ℤ) * (M : ℤ) := by gcongr
          _ = 2 * (M : ℤ) ^ 2 := by ring
      have hBval : (B : ℤ) = 4 * (M : ℤ) ^ 2 + 2 := by simp [B]
      linarith only [habs, hBval]
    · obtain ⟨k₁, hk₁⟩ := ha0 i
      have hneR : (a i k₁ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk₁
      have hnot := hnp i j hij ((a j k₁ : ℝ) / (a i k₁ : ℝ))
      push Not at hnot
      obtain ⟨k₂, hk₂⟩ := hnot
      refine ⟨⟨k₁.val + m * k₂.val, by nlinarith only [k₁.isLt, k₂.isLt]⟩, ?_⟩
      have h1 : (k₁.val + m * k₂.val) % m = k₁.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k₁.isLt]
      have h2 : (k₁.val + m * k₂.val) / m = k₂.val := by
        rw [Nat.add_mul_div_left _ _ hm_pos, Nat.div_eq_of_lt k₁.isLt, zero_add]
      dsimp [c]
      simp only [h1, h2]
      intro hzero
      apply hk₂
      have hzeroR : (a i k₁ : ℝ) * (a j k₂ : ℝ) - (a i k₂ : ℝ) * (a j k₁ : ℝ) = 0 := by
        exact_mod_cast hzero
      field_simp [hneR]
      linarith only [hzeroR]

/- ### Section 2: Hypergraph degree trimming -/

lemma trim_hypergraph {α : Type*} [DecidableEq α] (U : Finset α) (D : ℕ) :
    ∀ ℰ₀ : Finset (Finset α),
      ∃ ℰ ⊆ ℰ₀, (∀ v ∈ U, (ℰ.filter (fun e ↦ v ∈ e)).card ≤ D) ∧
        ℰ₀.card ≤ ℰ.card + ∑ v ∈ U, ((ℰ₀.filter (fun e ↦ v ∈ e)).card - D) := by
  intro ℰ₀
  induction hM : (∑ v ∈ U, ((ℰ₀.filter (fun e ↦ v ∈ e)).card - D)) using Nat.strong_induction_on
      generalizing ℰ₀ with
  | h M ih =>
    by_cases hM0 : M = 0
    · refine ⟨ℰ₀, Subset.rfl, fun v hv ↦ ?_, by omega⟩
      have hle : (ℰ₀.filter (fun e ↦ v ∈ e)).card - D ≤
          ∑ w ∈ U, ((ℰ₀.filter (fun e ↦ w ∈ e)).card - D) :=
        single_le_sum (f := fun w ↦ (ℰ₀.filter (fun e ↦ w ∈ e)).card - D)
          (fun _ _ ↦ Nat.zero_le _) hv
      omega
    · have hex : ∃ v ∈ U, D < (ℰ₀.filter (fun e ↦ v ∈ e)).card := by
        by_contra hall
        push Not at hall
        have hsum0 : ∑ v ∈ U, ((ℰ₀.filter (fun e ↦ v ∈ e)).card - D) = 0 :=
          sum_eq_zero fun v hv ↦ Nat.sub_eq_zero_of_le (hall v hv)
        omega
      obtain ⟨v₀, hv₀U, hv₀D⟩ := hex
      have hne : (ℰ₀.filter (fun e ↦ v₀ ∈ e)).Nonempty := card_pos.mp (by omega)
      obtain ⟨e₀, he₀⟩ := hne
      have he₀ℰ : e₀ ∈ ℰ₀ := (mem_filter.mp he₀).1
      let ℰ₁ := ℰ₀.erase e₀
      have hle_deg : ∀ v, (ℰ₁.filter (fun e ↦ v ∈ e)).card ≤ (ℰ₀.filter (fun e ↦ v ∈ e)).card := by
        intro v
        exact card_le_card (filter_subset_filter _ (erase_subset e₀ ℰ₀))
      have hv₀_deg : (ℰ₁.filter (fun e ↦ v₀ ∈ e)).card + 1 = (ℰ₀.filter (fun e ↦ v₀ ∈ e)).card := by
        have hEq : ℰ₁.filter (fun e ↦ v₀ ∈ e) = (ℰ₀.filter (fun e ↦ v₀ ∈ e)).erase e₀ := by
          ext e; simp [ℰ₁, and_comm, and_left_comm]
        rw [hEq]
        exact card_erase_add_one he₀
      let M₁ := ∑ v ∈ U, ((ℰ₁.filter (fun e ↦ v ∈ e)).card - D)
      have hM₁_lt : M₁ + 1 ≤ M := by
        rw [← hM]
        dsimp [M₁]
        rw [← add_sum_erase _ _ hv₀U, ← add_sum_erase _ _ hv₀U]
        have hrest : ∑ v ∈ U.erase v₀, ((ℰ₁.filter (fun e ↦ v ∈ e)).card - D) ≤
            ∑ v ∈ U.erase v₀, ((ℰ₀.filter (fun e ↦ v ∈ e)).card - D) :=
          sum_le_sum fun v _ ↦ Nat.sub_le_sub_right (hle_deg v) D
        omega
      obtain ⟨ℰ, hℰsub, hℰdeg, hℰcard⟩ := ih M₁ (by omega) ℰ₁ rfl
      refine ⟨ℰ, hℰsub.trans (erase_subset e₀ ℰ₀), hℰdeg, ?_⟩
      have hcard1 : ℰ₁.card + 1 = ℰ₀.card := card_erase_add_one he₀ℰ
      omega

/- ### Section 3: Finite product space uniform counting -/

lemma card_filter_eq_on {S Q : ℕ} (T : Finset (Fin S)) (val : Fin S → Fin Q) :
    (univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ T, ω t = val t)).card * Q ^ T.card =
      Q ^ S := by
  let e : {ω : Fin S → Fin Q // ∀ t ∈ T, ω t = val t} ≃ ({t : Fin S // t ∉ T} → Fin Q) :=
    { toFun := fun ω t ↦ ω.1 t.1
      invFun := fun f ↦ ⟨fun t ↦ if h : t ∈ T then val t else f ⟨t, h⟩,
        fun t ht ↦ by simp [ht]⟩
      left_inv := fun ω ↦ by
        ext t
        by_cases h : t ∈ T
        · simp [h, ω.2 t h]
        · simp [h]
      right_inv := fun f ↦ by
        ext ⟨t, ht⟩
        simp [ht] }
  have h1 : (univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ T, ω t = val t)).card =
      Fintype.card {ω : Fin S → Fin Q // ∀ t ∈ T, ω t = val t} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  have hcompl : Fintype.card {t : Fin S // t ∉ T} = S - T.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    congr 1
    exact Fintype.card_coe T
  rw [hcompl, ← pow_add]
  have hle : T.card ≤ S := by
    have := card_le_univ T
    simpa using this
  rw [Nat.sub_add_cancel hle]

/- ### Section 4: Circle separation from disjoint intervals in ZMod N -/

lemma zmod_interval_sep {N : ℕ} (hN : 0 < N) (b₁ b₂ : ℕ) (z₁ z₂ : ℤ)
    (hdisj : ∀ t₁ t₂ : ℤ, -(b₁ : ℤ) ≤ t₁ → t₁ ≤ b₁ → -(b₂ : ℤ) ≤ t₂ → t₂ ≤ b₂ →
      ((z₁ + t₁ : ℤ) : ZMod N) ≠ ((z₂ + t₂ : ℤ) : ZMod N)) :
    ∀ q : ℤ, ((2 * b₁ + 1 : ℕ) + (2 * b₂ + 1 : ℕ) : ℝ) / (2 * (N : ℝ)) ≤
      |(z₁ : ℝ) / (N : ℝ) - (z₂ : ℝ) / (N : ℝ) - (q : ℝ)| := by
  intro q
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let d : ℤ := z₁ - z₂ - q * (N : ℤ)
  have hd_gt : (b₁ : ℤ) + (b₂ : ℤ) + 1 ≤ |d| := by
    by_contra hlt
    push Not at hlt
    have habs : -(b₁ + b₂ : ℤ) ≤ d ∧ d ≤ (b₁ + b₂ : ℤ) := by
      have := abs_le.mp (show |d| ≤ (b₁ : ℤ) + (b₂ : ℤ) by omega)
      omega
    let t₁ : ℤ := max (-(b₁ : ℤ)) (min (b₁ : ℤ) (-d))
    let t₂ : ℤ := t₁ + d
    have ht₁_lo : -(b₁ : ℤ) ≤ t₁ := le_max_left _ _
    have ht₁_hi : t₁ ≤ (b₁ : ℤ) := max_le (by omega) (min_le_left _ _)
    have ht₂_lo : -(b₂ : ℤ) ≤ t₂ := by
      dsimp [t₂, t₁]
      rcases le_total (b₁ : ℤ) (-d) with h | h
      · rw [min_eq_left h, max_eq_right (by omega)]; omega
      · rw [min_eq_right h]
        rcases le_total (-(b₁ : ℤ)) (-d) with h' | h'
        · rw [max_eq_right h']; omega
        · rw [max_eq_left h']; omega
    have ht₂_hi : t₂ ≤ (b₂ : ℤ) := by
      dsimp [t₂, t₁]
      rcases le_total (b₁ : ℤ) (-d) with h | h
      · rw [min_eq_left h, max_eq_right (by omega)]; omega
      · rw [min_eq_right h]
        rcases le_total (-(b₁ : ℤ)) (-d) with h' | h'
        · rw [max_eq_right h']; omega
        · rw [max_eq_left h']; omega
    apply hdisj t₁ t₂ ht₁_lo ht₁_hi ht₂_lo ht₂_hi
    have heq : z₁ + t₁ = (z₂ + t₂) + q * (N : ℤ) := by dsimp [t₂, d]; ring
    rw [heq]
    push_cast
    simp
  have hd_eq : (z₁ : ℝ) / (N : ℝ) - (z₂ : ℝ) / (N : ℝ) - (q : ℝ) = (d : ℝ) / (N : ℝ) := by
    dsimp [d]
    push_cast
    field_simp
  rw [hd_eq, abs_div, abs_of_pos hNR]
  have h1 : ((b₁ : ℤ) + (b₂ : ℤ) + 1 : ℝ) ≤ |(d : ℝ)| := by
    have : ((b₁ : ℤ) + (b₂ : ℤ) + 1 : ℝ) ≤ ((|d| : ℤ) : ℝ) := by exact_mod_cast hd_gt
    simpa [Int.cast_abs] using this
  have h2 : (((2 * b₁ + 1 : ℕ) + (2 * b₂ + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) =
      ((b₁ : ℤ) + (b₂ : ℤ) + 1 : ℝ) / (N : ℝ) := by
    push_cast
    field_simp
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right h1 hNR.le

/- ### Section 5: 2x2 Linear Algebra over ZMod N -/

def linEval (A : ℤ × ℤ) (N : ℕ) (x : ZMod N × ZMod N) : ZMod N :=
  (A.1 : ZMod N) * x.1 + (A.2 : ZMod N) * x.2

def evalPairEquiv {N : ℕ} [Fact N.Prime] (A₁ A₂ : ℤ × ℤ)
    (hdet : ((A₁.1 * A₂.2 - A₁.2 * A₂.1 : ℤ) : ZMod N) ≠ 0) :
    (ZMod N × ZMod N) ≃ (ZMod N × ZMod N) :=
  let d : ZMod N := ((A₁.1 * A₂.2 - A₁.2 * A₂.1 : ℤ) : ZMod N)
  { toFun := fun x ↦ (linEval A₁ N x, linEval A₂ N x)
    invFun := fun y ↦
      (((A₂.2 : ZMod N) * y.1 - (A₁.2 : ZMod N) * y.2) * d⁻¹,
       (-(A₂.1 : ZMod N) * y.1 + (A₁.1 : ZMod N) * y.2) * d⁻¹)
    left_inv := fun ⟨x₁, x₂⟩ ↦ by
      have hd : (A₁.1 : ZMod N) * (A₂.2 : ZMod N) - (A₁.2 : ZMod N) * (A₂.1 : ZMod N) = d := by
        dsimp [d]; push_cast; ring
      ext
      · dsimp [linEval]
        calc ((A₂.2 : ZMod N) * ((A₁.1 : ZMod N) * x₁ + (A₁.2 : ZMod N) * x₂) -
              (A₁.2 : ZMod N) * ((A₂.1 : ZMod N) * x₁ + (A₂.2 : ZMod N) * x₂)) * d⁻¹
            = x₁ * (((A₁.1 : ZMod N) * (A₂.2 : ZMod N) - (A₁.2 : ZMod N) * (A₂.1 : ZMod N)) * d⁻¹) := by ring
          _ = x₁ * (d * d⁻¹) := by rw [hd]
          _ = x₁ := by rw [mul_inv_cancel₀ hdet, mul_one]
      · dsimp [linEval]
        calc (-(A₂.1 : ZMod N) * ((A₁.1 : ZMod N) * x₁ + (A₁.2 : ZMod N) * x₂) +
              (A₁.1 : ZMod N) * ((A₂.1 : ZMod N) * x₁ + (A₂.2 : ZMod N) * x₂)) * d⁻¹
            = x₂ * (((A₁.1 : ZMod N) * (A₂.2 : ZMod N) - (A₁.2 : ZMod N) * (A₂.1 : ZMod N)) * d⁻¹) := by ring
          _ = x₂ * (d * d⁻¹) := by rw [hd]
          _ = x₂ := by rw [mul_inv_cancel₀ hdet, mul_one]
    right_inv := fun ⟨y₁, y₂⟩ ↦ by
      have hd : (A₁.1 : ZMod N) * (A₂.2 : ZMod N) - (A₁.2 : ZMod N) * (A₂.1 : ZMod N) = d := by
        dsimp [d]; push_cast; ring
      ext
      · dsimp [linEval]
        calc (A₁.1 : ZMod N) * (((A₂.2 : ZMod N) * y₁ - (A₁.2 : ZMod N) * y₂) * d⁻¹) +
              (A₁.2 : ZMod N) * ((-(A₂.1 : ZMod N) * y₁ + (A₁.1 : ZMod N) * y₂) * d⁻¹)
            = y₁ * (((A₁.1 : ZMod N) * (A₂.2 : ZMod N) - (A₁.2 : ZMod N) * (A₂.1 : ZMod N)) * d⁻¹) := by ring
          _ = y₁ * (d * d⁻¹) := by rw [hd]
          _ = y₁ := by rw [mul_inv_cancel₀ hdet, mul_one]
      · dsimp [linEval]
        calc (A₂.1 : ZMod N) * (((A₂.2 : ZMod N) * y₁ - (A₁.2 : ZMod N) * y₂) * d⁻¹) +
              (A₂.2 : ZMod N) * ((-(A₂.1 : ZMod N) * y₁ + (A₁.1 : ZMod N) * y₂) * d⁻¹)
            = y₂ * (((A₁.1 : ZMod N) * (A₂.2 : ZMod N) - (A₁.2 : ZMod N) * (A₂.1 : ZMod N)) * d⁻¹) := by ring
          _ = y₂ * (d * d⁻¹) := by rw [hd]
          _ = y₂ := by rw [mul_inv_cancel₀ hdet, mul_one] }

/- ### Section 6: Slot structure and disjointness -/

section SlotPacking

variable {r : ℕ} (b : Fin r → ℕ)

def ell (i : Fin r) : ℕ := 2 * b i + 1

def Lmax : ℕ := ∑ i : Fin r, ell b i

def off (i : Fin r) : ℕ := ∑ j ∈ univ.filter (· < i), ell b j

lemma ell_pos (i : Fin r) : 0 < ell b i := by dsimp [ell]; omega

lemma ell_le_Lmax (i : Fin r) : ell b i ≤ Lmax b :=
  single_le_sum (f := fun j ↦ ell b j) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)

lemma off_add_ell_le_Lmax (i : Fin r) : off b i + ell b i ≤ Lmax b := by
  dsimp [off, Lmax]
  have hnot : i ∉ univ.filter (· < i) := by simp
  rw [add_comm, ← sum_insert hnot]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)

lemma off_add_ell_le_off_of_lt {i j : Fin r} (hij : i < j) : off b i + ell b i ≤ off b j := by
  dsimp [off]
  have hnot : i ∉ univ.filter (· < i) := by simp
  rw [add_comm, ← sum_insert hnot]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ Nat.zero_le _)
  intro k hk
  simp only [mem_insert, mem_filter, mem_univ, true_and] at hk ⊢
  rcases hk with rfl | hk
  · exact hij
  · exact lt_trans hk hij

def encodeKey (Q : ℕ) (hQ : 2 * Lmax b < Q) (e : Bool) (i : Fin r) (τ : ℕ) (hτ : τ < ell b i) :
    Fin Q :=
  ⟨(if e then 0 else Lmax b) + off b i + τ, by
    have h1 := off_add_ell_le_Lmax b i
    cases e <;> simp <;> omega⟩

lemma encodeKey_inj {Q : ℕ} {hQ : 2 * Lmax b < Q} {e₁ e₂ : Bool} {i₁ i₂ : Fin r}
    {τ₁ τ₂ : ℕ} {hτ₁ : τ₁ < ell b i₁} {hτ₂ : τ₂ < ell b i₂}
    (heq : encodeKey b Q hQ e₁ i₁ τ₁ hτ₁ = encodeKey b Q hQ e₂ i₂ τ₂ hτ₂) :
    e₁ = e₂ ∧ i₁ = i₂ ∧ τ₁ = τ₂ := by
  have hval := congrArg Fin.val heq
  dsimp [encodeKey] at hval
  have h1 := off_add_ell_le_Lmax b i₁
  have h2 := off_add_ell_le_Lmax b i₂
  have he : e₁ = e₂ := by
    cases e₁ <;> cases e₂ <;> simp at hval ⊢ <;> omega
  subst he
  have hi : i₁ = i₂ := by
    rcases lt_trichotomy i₁ i₂ with hlt | heq' | hgt
    · have := off_add_ell_le_off_of_lt b hlt; omega
    · exact heq'
    · have := off_add_ell_le_off_of_lt b hgt; omega
  subst hi
  exact ⟨rfl, rfl, by omega⟩

def isPosHalf (N S L : ℕ) (v : ZMod N) : Prop :=
  1 ≤ v.val ∧ v.val ≤ S * L

def isNegHalf (N S L : ℕ) (v : ZMod N) : Prop :=
  1 ≤ (-v).val ∧ (-v).val ≤ S * L

lemma not_pos_and_neg {N S L : ℕ} [NeZero N] (h2SL : 2 * S * L < N) (v : ZMod N) :
    ¬ (isPosHalf N S L v ∧ isNegHalf N S L v) := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hneg : (-v).val = N - v.val := by
    rw [ZMod.neg_val', Nat.mod_eq_of_lt]
    have := ZMod.val_lt v
    omega
  have hSL : S * L + S * L < N := by nlinarith only [h2SL]
  omega

def isInterior (N S L : ℕ) (v : ZMod N) : Prop :=
  (isPosHalf N S L v ∧ 2 * Lmax b ≤ (v.val - 1) % L ∧ (v.val - 1) % L + 2 * Lmax b < L) ∨
  (isNegHalf N S L v ∧ 2 * Lmax b ≤ ((-v).val - 1) % L ∧ ((-v).val - 1) % L + 2 * Lmax b < L)

noncomputable def posSign (N S L : ℕ) (v : ZMod N) : Bool :=
  decide (isPosHalf N S L v)

noncomputable def slotOf (N S L : ℕ) (v : ZMod N) : ℕ :=
  if posSign N S L v then (v.val - 1) / L else ((-v).val - 1) / L

noncomputable def slotFin (N S L : ℕ) (hS : 0 < S) (v : ZMod N) : Fin S :=
  ⟨min (slotOf N S L v) (S - 1), by omega⟩

noncomputable def offsetOf (N S L : ℕ) (v : ZMod N) : ℕ :=
  if posSign N S L v then (v.val - 1) % L else ((-v).val - 1) % L

lemma posSign_eq_true_iff {N S L : ℕ} (v : ZMod N) :
    posSign N S L v = true ↔ isPosHalf N S L v := by
  unfold posSign
  exact decide_eq_true_iff

lemma posSign_eq_false_iff {N S L : ℕ} (v : ZMod N) :
    posSign N S L v = false ↔ ¬ isPosHalf N S L v := by
  unfold posSign
  exact decide_eq_false_iff_not

lemma slotOf_lt {N S L : ℕ} (_hL : 0 < L) {v : ZMod N}
    (hv : isPosHalf N S L v ∨ isNegHalf N S L v) : slotOf N S L v < S := by
  dsimp [slotOf]
  split_ifs with h
  · have hpos : isPosHalf N S L v := (posSign_eq_true_iff v).mp h
    have hlt : v.val - 1 < L * S := by
      have h1 := hpos.1; have h2 := hpos.2; rw [mul_comm]; omega
    exact Nat.div_lt_of_lt_mul hlt
  · have hnot : ¬ isPosHalf N S L v := (posSign_eq_false_iff v).mp (Bool.eq_false_iff.mpr h)
    have hneg : isNegHalf N S L v := hv.resolve_left hnot
    have hlt : (-v).val - 1 < L * S := by
      have h1 := hneg.1; have h2 := hneg.2; rw [mul_comm]; omega
    exact Nat.div_lt_of_lt_mul hlt

lemma slotFin_val {N S L : ℕ} (hS : 0 < S) (hL : 0 < L) {v : ZMod N}
    (hv : isPosHalf N S L v ∨ isNegHalf N S L v) :
    (slotFin N S L hS v).val = slotOf N S L v := by
  have hlt := slotOf_lt hL hv
  dsimp [slotFin]
  omega

lemma isInterior_neg {N S L : ℕ} {v : ZMod N} (hv : isInterior b N S L v) :
    isInterior b N S L (-v) := by
  rcases hv with h | h
  · right; simpa [isPosHalf, isNegHalf] using h
  · left; simpa [isPosHalf, isNegHalf] using h

lemma slotOf_neg {N S L : ℕ} [NeZero N] (h2SL : 2 * S * L < N) {v : ZMod N}
    (hv : isPosHalf N S L v ∨ isNegHalf N S L v) :
    slotOf N S L (-v) = slotOf N S L v := by
  rcases hv with hp | hn
  · have hnn : ¬ isNegHalf N S L v := fun h ↦ not_pos_and_neg h2SL v ⟨hp, h⟩
    have h1 : posSign N S L v = true := (posSign_eq_true_iff v).mpr hp
    have h2 : posSign N S L (-v) = false :=
      (posSign_eq_false_iff (-v)).mpr (by simpa [isPosHalf, isNegHalf] using hnn)
    simp [slotOf, h1, h2]
  · have hnp : ¬ isPosHalf N S L v := fun h ↦ not_pos_and_neg h2SL v ⟨h, hn⟩
    have h1 : posSign N S L v = false := (posSign_eq_false_iff v).mpr hnp
    have h2 : posSign N S L (-v) = true :=
      (posSign_eq_true_iff (-v)).mpr (by simpa [isPosHalf, isNegHalf] using hn)
    simp [slotOf, h1, h2]

lemma offsetOf_neg {N S L : ℕ} [NeZero N] (h2SL : 2 * S * L < N) {v : ZMod N}
    (hv : isPosHalf N S L v ∨ isNegHalf N S L v) :
    offsetOf N S L (-v) = offsetOf N S L v := by
  rcases hv with hp | hn
  · have hnn : ¬ isNegHalf N S L v := fun h ↦ not_pos_and_neg h2SL v ⟨hp, h⟩
    have h1 : posSign N S L v = true := (posSign_eq_true_iff v).mpr hp
    have h2 : posSign N S L (-v) = false :=
      (posSign_eq_false_iff (-v)).mpr (by simpa [isPosHalf, isNegHalf] using hnn)
    simp [offsetOf, h1, h2]
  · have hnp : ¬ isPosHalf N S L v := fun h ↦ not_pos_and_neg h2SL v ⟨h, hn⟩
    have h1 : posSign N S L v = false := (posSign_eq_false_iff v).mpr hnp
    have h2 : posSign N S L (-v) = true :=
      (posSign_eq_true_iff (-v)).mpr (by simpa [isPosHalf, isNegHalf] using hn)
    simp [offsetOf, h1, h2]

lemma posSign_neg {N S L : ℕ} [NeZero N] (h2SL : 2 * S * L < N) {v : ZMod N}
    (hv : isPosHalf N S L v ∨ isNegHalf N S L v) :
    posSign N S L (-v) = !(posSign N S L v) := by
  rcases hv with hp | hn
  · have hnn : ¬ isNegHalf N S L v := fun h ↦ not_pos_and_neg h2SL v ⟨hp, h⟩
    have h1 : posSign N S L v = true := (posSign_eq_true_iff v).mpr hp
    have h2 : posSign N S L (-v) = false :=
      (posSign_eq_false_iff (-v)).mpr (by simpa [isPosHalf, isNegHalf] using hnn)
    simp [h1, h2]
  · have hnp : ¬ isPosHalf N S L v := fun h ↦ not_pos_and_neg h2SL v ⟨h, hn⟩
    have h1 : posSign N S L v = false := (posSign_eq_false_iff v).mpr hnp
    have h2 : posSign N S L (-v) = true :=
      (posSign_eq_true_iff (-v)).mpr (by simpa [isPosHalf, isNegHalf] using hn)
    simp [h1, h2]

lemma eq_of_posSign_slot_offset {N S L : ℕ} [NeZero N]
    {u v : ZMod N} (hu : isPosHalf N S L u ∨ isNegHalf N S L u)
    (hv : isPosHalf N S L v ∨ isNegHalf N S L v)
    (hps : posSign N S L u = posSign N S L v)
    (hsl : slotOf N S L u = slotOf N S L v)
    (hof : offsetOf N S L u = offsetOf N S L v) : u = v := by
  have hval_eq : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → (a - 1) / L = (b - 1) / L →
      (a - 1) % L = (b - 1) % L → a = b := by
    intro a b ha hb hd hm
    have e1 := Nat.div_add_mod (a - 1) L
    have e2 := Nat.div_add_mod (b - 1) L
    rw [hd, hm] at e1
    omega
  by_cases hp : posSign N S L u = true
  · have hpv : posSign N S L v = true := hps ▸ hp
    have hu' : isPosHalf N S L u := (posSign_eq_true_iff u).mp hp
    have hv' : isPosHalf N S L v := (posSign_eq_true_iff v).mp hpv
    simp only [slotOf, offsetOf, hp, hpv, ↓reduceIte] at hsl hof
    have hveq : u.val = v.val := hval_eq u.val v.val hu'.1 hv'.1 hsl hof
    exact ZMod.val_injective N hveq
  · have hp' : posSign N S L u = false := Bool.eq_false_iff.mpr hp
    have hpv : posSign N S L v = false := hps ▸ hp'
    have hu' : isNegHalf N S L u := hu.resolve_left ((posSign_eq_false_iff u).mp hp')
    have hv' : isNegHalf N S L v := hv.resolve_left ((posSign_eq_false_iff v).mp hpv)
    simp only [slotOf, offsetOf, hp', hpv, Bool.false_eq_true, ↓reduceIte] at hsl hof
    have hveq : (-u).val = (-v).val := hval_eq (-u).val (-v).val hu'.1 hv'.1 hsl hof
    exact neg_injective (ZMod.val_injective N hveq)

lemma shift_in_same_slot {N S L : ℕ} [NeZero N] (h2SL : 2 * S * L < N) (hL : 0 < L)
    {c : ZMod N} (hc : isInterior b N S L c) {k : ℕ} (hk : k ≤ Lmax b)
    {t : ℤ} (ht1 : -(k : ℤ) ≤ t) (ht2 : t ≤ k) :
    (isPosHalf N S L (c + (t : ZMod N)) ∨ isNegHalf N S L (c + (t : ZMod N))) ∧
    posSign N S L (c + (t : ZMod N)) = posSign N S L c ∧
    slotOf N S L (c + (t : ZMod N)) = slotOf N S L c ∧
    |(offsetOf N S L (c + (t : ZMod N)) : ℤ) - (offsetOf N S L c : ℤ)| ≤ k := by
  have helper : ∀ (x : ZMod N) (d : ℤ),
      isPosHalf N S L x → 2 * Lmax b ≤ (x.val - 1) % L → (x.val - 1) % L + 2 * Lmax b < L →
      -(k : ℤ) ≤ d → d ≤ k →
      isPosHalf N S L (x + (d : ZMod N)) ∧
      ((x + (d : ZMod N)).val - 1) / L = (x.val - 1) / L ∧
      |((((x + (d : ZMod N)).val - 1) % L : ℕ) : ℤ) - ((((x.val - 1) % L : ℕ) : ℤ))| ≤ k := by
    intro x d hx hlo hhi hd1 hd2
    set s := (x.val - 1) / L
    set off0 := (x.val - 1) % L
    have hxval : x.val = 1 + L * s + off0 := by
      have e := Nat.div_add_mod (x.val - 1) L
      have h1 := hx.1
      dsimp [s, off0]
      omega
    have hs : s < S := by
      have hlt : x.val - 1 < L * S := by have := hx.1; have := hx.2; rw [mul_comm]; omega
      exact Nat.div_lt_of_lt_mul hlt
    have hoff_new_pos : 0 ≤ (off0 : ℤ) + d := by omega
    have hoff_new_lt : (off0 : ℤ) + d < (L : ℤ) := by omega
    set off1 : ℕ := ((off0 : ℤ) + d).toNat
    have hoff1_eq : (off1 : ℤ) = (off0 : ℤ) + d := Int.toNat_of_nonneg hoff_new_pos
    have hoff1_lt : off1 < L := by omega
    set w : ℕ := 1 + L * s + off1
    have hw_le_SL : w ≤ S * L := by
      have h1 : L * s + L ≤ S * L := by have : s + 1 ≤ S := hs; nlinarith only [this]
      dsimp [w]; omega
    have hSL_lt_N : S * L < N := by nlinarith only [h2SL]
    have hw_lt : w < N := lt_of_le_of_lt hw_le_SL hSL_lt_N
    have hxd : x + (d : ZMod N) = (w : ZMod N) := by
      have h1 : ((x.val : ℤ) + d : ℤ) = (w : ℤ) := by
        dsimp [w]; omega
      calc x + (d : ZMod N) = ((x.val : ℤ) : ZMod N) + (d : ZMod N) := by
              rw [Int.cast_natCast, ZMod.natCast_zmod_val]
        _ = (((x.val : ℤ) + d : ℤ) : ZMod N) := by push_cast; rfl
        _ = ((w : ℤ) : ZMod N) := by rw [h1]
        _ = (w : ZMod N) := by push_cast; rfl
    have hval_xd : (x + (d : ZMod N)).val = w := by
      rw [hxd, ZMod.val_natCast_of_lt hw_lt]
    have hpos_xd : isPosHalf N S L (x + (d : ZMod N)) := by
      rw [isPosHalf, hval_xd]
      exact ⟨by dsimp [w]; omega, hw_le_SL⟩
    have hw1 : w - 1 = off1 + L * s := by
      dsimp [w]; omega
    have hdiv : (w - 1) / L = s := by
      rw [hw1, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hoff1_lt, zero_add]
    have hmod : (w - 1) % L = off1 := by
      rw [hw1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hoff1_lt]
    refine ⟨hpos_xd, by rw [hval_xd, hdiv], ?_⟩
    rw [hval_xd, hmod, hoff1_eq]
    rw [show (off0 : ℤ) + d - (off0 : ℤ) = d by ring]
    exact abs_le.mpr ⟨hd1, hd2⟩
  rcases hc with ⟨hp, hlo, hhi⟩ | ⟨hn, hlo, hhi⟩
  · obtain ⟨hp', hdiv, hmod⟩ := helper c t hp hlo hhi ht1 ht2
    have hps_c : posSign N S L c = true := (posSign_eq_true_iff c).mpr hp
    have hps_ct : posSign N S L (c + (t : ZMod N)) = true := (posSign_eq_true_iff _).mpr hp'
    refine ⟨Or.inl hp', by rw [hps_c, hps_ct], ?_, ?_⟩
    · simp only [slotOf, hps_c, hps_ct, ↓reduceIte]; exact hdiv
    · simp only [offsetOf, hps_c, hps_ct, ↓reduceIte]; exact hmod
  · have hnp_c : ¬ isPosHalf N S L c := fun h ↦ not_pos_and_neg h2SL c ⟨h, hn⟩
    obtain ⟨hp', hdiv, hmod⟩ := helper (-c) (-t) hn hlo hhi (by omega) (by omega)
    have hneg_eq : -(c + (t : ZMod N)) = -c + ((-t : ℤ) : ZMod N) := by push_cast; ring
    have hn' : isNegHalf N S L (c + (t : ZMod N)) := by
      simpa [isPosHalf, isNegHalf, hneg_eq] using hp'
    have hnp_ct : ¬ isPosHalf N S L (c + (t : ZMod N)) :=
      fun h ↦ not_pos_and_neg h2SL (c + (t : ZMod N)) ⟨h, hn'⟩
    have hps_c : posSign N S L c = false := (posSign_eq_false_iff c).mpr hnp_c
    have hps_ct : posSign N S L (c + (t : ZMod N)) = false := (posSign_eq_false_iff _).mpr hnp_ct
    refine ⟨Or.inr hn', by rw [hps_c, hps_ct], ?_, ?_⟩
    · simp only [slotOf, hps_c, hps_ct, Bool.false_eq_true, ↓reduceIte, hneg_eq]
      exact hdiv
    · simp only [offsetOf, hps_c, hps_ct, Bool.false_eq_true, ↓reduceIte, hneg_eq]
      exact hmod

noncomputable def keyOf (Q : ℕ) (hQ : 2 * Lmax b < Q) (N S L : ℕ) (i : Fin r) (v : ZMod N) :
    Fin Q :=
  encodeKey b Q hQ (posSign N S L v) i ((offsetOf N S L v - b i) % ell b i)
    (Nat.mod_lt _ (ell_pos b i))

lemma slot_intervals_disjoint {Q N S L : ℕ} [NeZero N] (hQ : 2 * Lmax b < Q)
    (h2SL : 2 * S * L < N) (hS : 0 < S) (hL : 0 < L)
    (ω : Fin S → Fin Q)
    {e₁ e₂ : Bool} {i₁ i₂ : Fin r} {u₁ u₂ : ZMod N}
    (hu₁ : isInterior b N S L u₁) (hu₂ : isInterior b N S L u₂)
    (hω₁ : ω (slotFin N S L hS u₁) = keyOf b Q hQ N S L i₁ u₁)
    (hω₂ : ω (slotFin N S L hS u₂) = keyOf b Q hQ N S L i₂ u₂)
    (hne : (e₁, i₁, u₁) ≠ (e₂, i₂, u₂)) :
    ∀ t₁ t₂ : ℤ, -(b i₁ : ℤ) ≤ t₁ → t₁ ≤ b i₁ → -(b i₂ : ℤ) ≤ t₂ → t₂ ≤ b i₂ →
      (if e₁ then (1 : ZMod N) else -1) * u₁ + (t₁ : ZMod N) ≠
        (if e₂ then (1 : ZMod N) else -1) * u₂ + (t₂ : ZMod N) := by
  intro t₁ t₂ ht₁1 ht₁2 ht₂1 ht₂2 heq
  set c₁ : ZMod N := (if e₁ then (1 : ZMod N) else -1) * u₁
  set c₂ : ZMod N := (if e₂ then (1 : ZMod N) else -1) * u₂
  have hu₁h : isPosHalf N S L u₁ ∨ isNegHalf N S L u₁ := hu₁.imp And.left And.left
  have hu₂h : isPosHalf N S L u₂ ∨ isNegHalf N S L u₂ := hu₂.imp And.left And.left
  have hc₁_int : isInterior b N S L c₁ := by
    cases e₁ <;> simp [c₁, hu₁, isInterior_neg b hu₁]
  have hc₂_int : isInterior b N S L c₂ := by
    cases e₂ <;> simp [c₂, hu₂, isInterior_neg b hu₂]
  have hc₁_slot : slotOf N S L c₁ = slotOf N S L u₁ := by
    cases e₁ <;> simp [c₁, slotOf_neg h2SL hu₁h]
  have hc₂_slot : slotOf N S L c₂ = slotOf N S L u₂ := by
    cases e₂ <;> simp [c₂, slotOf_neg h2SL hu₂h]
  have hc₁_off : offsetOf N S L c₁ = offsetOf N S L u₁ := by
    cases e₁ <;> simp [c₁, offsetOf_neg h2SL hu₁h]
  have hc₂_off : offsetOf N S L c₂ = offsetOf N S L u₂ := by
    cases e₂ <;> simp [c₂, offsetOf_neg h2SL hu₂h]
  have hc₁_ps : posSign N S L c₁ = (if e₁ then posSign N S L u₁ else !(posSign N S L u₁)) := by
    cases e₁ <;> simp [c₁, posSign_neg h2SL hu₁h]
  have hc₂_ps : posSign N S L c₂ = (if e₂ then posSign N S L u₂ else !(posSign N S L u₂)) := by
    cases e₂ <;> simp [c₂, posSign_neg h2SL hu₂h]
  have hb₁ : b i₁ ≤ Lmax b := by have := ell_le_Lmax b i₁; dsimp [ell] at this; omega
  have hb₂ : b i₂ ≤ Lmax b := by have := ell_le_Lmax b i₂; dsimp [ell] at this; omega
  obtain ⟨_, hps1, hsl1, hof1⟩ := shift_in_same_slot b h2SL hL hc₁_int hb₁ ht₁1 ht₁2
  obtain ⟨_, hps2, hsl2, hof2⟩ := shift_in_same_slot b h2SL hL hc₂_int hb₂ ht₂1 ht₂2
  have hps_eq : posSign N S L c₁ = posSign N S L c₂ := by
    rw [← hps1, heq, hps2]
  have hsl_eq : slotOf N S L u₁ = slotOf N S L u₂ := by
    rw [← hc₁_slot, ← hsl1, heq, hsl2, hc₂_slot]
  have hsf_eq : slotFin N S L hS u₁ = slotFin N S L hS u₂ := by
    ext
    rw [slotFin_val hS hL hu₁h, slotFin_val hS hL hu₂h, hsl_eq]
  have hkey_eq : keyOf b Q hQ N S L i₁ u₁ = keyOf b Q hQ N S L i₂ u₂ := by
    rw [← hω₁, ← hω₂, hsf_eq]
  obtain ⟨hu_ps, hi_eq, hmod_eq⟩ := encodeKey_inj b hkey_eq
  subst hi_eq
  have he_eq : e₁ = e₂ := by
    rw [hc₁_ps, hc₂_ps, hu_ps] at hps_eq
    cases e₁ <;> cases e₂ <;> simp at hps_eq ⊢
  subst he_eq
  have hoff_diff : |(offsetOf N S L u₁ : ℤ) - (offsetOf N S L u₂ : ℤ)| ≤ 2 * (b i₁ : ℤ) := by
    rw [← hc₁_off, ← hc₂_off]
    have htri := abs_sub_le (offsetOf N S L c₁ : ℤ) (offsetOf N S L (c₁ + (t₁ : ZMod N)) : ℤ)
      (offsetOf N S L c₂ : ℤ)
    have hcomm := abs_sub_comm (offsetOf N S L c₁ : ℤ) (offsetOf N S L (c₁ + (t₁ : ZMod N)) : ℤ)
    rw [hcomm] at htri
    rw [← heq] at hof2
    linarith only [htri, hof1, hof2]
  have hoff₁_ge : b i₁ ≤ offsetOf N S L u₁ := by
    have h2l : 2 * Lmax b ≤ offsetOf N S L u₁ := by
      rcases hu₁ with ⟨hp, hlo, _⟩ | ⟨hn, hlo, _⟩
      · have h1 := (posSign_eq_true_iff u₁).mpr hp
        simp [offsetOf, h1, hlo]
      · have hnp : ¬ isPosHalf N S L u₁ := fun h ↦ not_pos_and_neg h2SL u₁ ⟨h, hn⟩
        have h1 := (posSign_eq_false_iff u₁).mpr hnp
        simp [offsetOf, h1, hlo]
    omega
  have hoff₂_ge : b i₁ ≤ offsetOf N S L u₂ := by
    have h2l : 2 * Lmax b ≤ offsetOf N S L u₂ := by
      rcases hu₂ with ⟨hp, hlo, _⟩ | ⟨hn, hlo, _⟩
      · have h1 := (posSign_eq_true_iff u₂).mpr hp
        simp [offsetOf, h1, hlo]
      · have hnp : ¬ isPosHalf N S L u₂ := fun h ↦ not_pos_and_neg h2SL u₂ ⟨h, hn⟩
        have h1 := (posSign_eq_false_iff u₂).mpr hnp
        simp [offsetOf, h1, hlo]
    omega
  have hoff_eq : offsetOf N S L u₁ = offsetOf N S L u₂ := by
    set x₁ := offsetOf N S L u₁ - b i₁
    set x₂ := offsetOf N S L u₂ - b i₁
    have hx_sub : (x₁ : ℤ) - (x₂ : ℤ) = (offsetOf N S L u₁ : ℤ) - (offsetOf N S L u₂ : ℤ) := by
      dsimp [x₁, x₂]; omega
    have hdiff : |(x₁ : ℤ) - (x₂ : ℤ)| < (ell b i₁ : ℤ) := by
      rw [hx_sub]; dsimp [ell]; omega
    have he1 := Nat.div_add_mod x₁ (ell b i₁)
    have he2 := Nat.div_add_mod x₂ (ell b i₁)
    have hqeq : x₁ / ell b i₁ = x₂ / ell b i₁ := by
      by_contra hqne
      have habs_lt := abs_lt.mp hdiff
      have he1Z : (ell b i₁ : ℤ) * (x₁ / ell b i₁ : ℕ) + (x₁ % ell b i₁ : ℕ) = (x₁ : ℤ) := by
        exact_mod_cast he1
      have he2Z : (ell b i₁ : ℤ) * (x₂ / ell b i₁ : ℕ) + (x₂ % ell b i₁ : ℕ) = (x₂ : ℤ) := by
        exact_mod_cast he2
      have hmodZ : ((x₁ % ell b i₁ : ℕ) : ℤ) = ((x₂ % ell b i₁ : ℕ) : ℤ) := by exact_mod_cast hmod_eq
      rcases lt_or_gt_of_ne hqne with hlt | hgt
      · have h1 : ((x₁ / ell b i₁ : ℕ) : ℤ) + 1 ≤ ((x₂ / ell b i₁ : ℕ) : ℤ) := by exact_mod_cast hlt
        have hpos : (0 : ℤ) < (ell b i₁ : ℤ) := by exact_mod_cast ell_pos b i₁
        nlinarith only [h1, hpos, he1Z, he2Z, hmodZ, habs_lt.1]
      · have h1 : ((x₂ / ell b i₁ : ℕ) : ℤ) + 1 ≤ ((x₁ / ell b i₁ : ℕ) : ℤ) := by exact_mod_cast hgt
        have hpos : (0 : ℤ) < (ell b i₁ : ℤ) := by exact_mod_cast ell_pos b i₁
        nlinarith only [h1, hpos, he1Z, he2Z, hmodZ, habs_lt.2]
    have hx_eq : x₁ = x₂ := by rw [hqeq, hmod_eq] at he1; omega
    dsimp [x₁, x₂] at hx_eq
    omega
  have hu_eq : u₁ = u₂ := eq_of_posSign_slot_offset hu₁h hu₂h hu_ps hsl_eq hoff_eq
  exact hne (by rw [hu_eq])

/- ### Section 7: Counting Valid Vectors and Variance Bound -/

lemma card_slot_fiber_le {N S L : ℕ} [NeZero N] (hL : 0 < L) (s : ℕ) :
    (univ.filter (fun v : ZMod N ↦ (isPosHalf N S L v ∨ isNegHalf N S L v) ∧ slotOf N S L v = s)).card
      ≤ 2 * L := by
  let Ppos : Finset (ZMod N) := (range L).image (fun t ↦ ((1 + L * s + t : ℕ) : ZMod N))
  let Pneg : Finset (ZMod N) := (range L).image (fun t ↦ -((1 + L * s + t : ℕ) : ZMod N))
  have hsub : univ.filter (fun v : ZMod N ↦ (isPosHalf N S L v ∨ isNegHalf N S L v) ∧ slotOf N S L v = s)
      ⊆ Ppos ∪ Pneg := by
    intro v hv
    obtain ⟨_, hvh, hsl⟩ := mem_filter.mp hv
    by_cases hp : posSign N S L v = true
    · have hp' : isPosHalf N S L v := (posSign_eq_true_iff v).mp hp
      simp only [slotOf, hp, ↓reduceIte] at hsl
      refine mem_union_left _ (mem_image.mpr ⟨(v.val - 1) % L, mem_range.mpr (Nat.mod_lt _ hL), ?_⟩)
      have hv1 : 1 + L * s + (v.val - 1) % L = v.val := by
        have e := Nat.div_add_mod (v.val - 1) L
        rw [hsl] at e
        have := hp'.1
        omega
      rw [hv1, ZMod.natCast_zmod_val]
    · have hp' : posSign N S L v = false := Bool.eq_false_iff.mpr hp
      have hn' : isNegHalf N S L v := hvh.resolve_left ((posSign_eq_false_iff v).mp hp')
      simp only [slotOf, hp', Bool.false_eq_true, ↓reduceIte] at hsl
      refine mem_union_right _ (mem_image.mpr ⟨((-v).val - 1) % L, mem_range.mpr (Nat.mod_lt _ hL), ?_⟩)
      have hv1 : 1 + L * s + ((-v).val - 1) % L = (-v).val := by
        have e := Nat.div_add_mod ((-v).val - 1) L
        rw [hsl] at e
        have := hn'.1
        omega
      rw [hv1, ZMod.natCast_zmod_val, neg_neg]
  calc (univ.filter _).card ≤ (Ppos ∪ Pneg).card := card_le_card hsub
    _ ≤ Ppos.card + Pneg.card := card_union_le _ _
    _ ≤ (range L).card + (range L).card := add_le_add card_image_le card_image_le
    _ = 2 * L := by simp; ring

lemma card_not_interior_le {N S L : ℕ} [NeZero N] (h2SL : 2 * S * L < N) (hL : 4 * Lmax b < L)
    (hSN : N ≤ 2 * S * L + 2 * L + 1) :
    (univ.filter (fun v : ZMod N ↦ ¬ isInterior b N S L v)).card ≤
      8 * S * Lmax b + 2 * L + 1 := by
  have hLpos : 0 < L := by omega
  have hSL_lt_N : S * L < N := by nlinarith only [h2SL]
  let idxSet : Finset (ℕ × ℕ) := range S ×ˢ Ico (2 * Lmax b) (L - 2 * Lmax b)
  let goodPos : Finset (ZMod N) := idxSet.image (fun p ↦ ((1 + L * p.1 + p.2 : ℕ) : ZMod N))
  let goodNeg : Finset (ZMod N) := goodPos.image (fun v ↦ -v)
  have hval_le_SL : ∀ s t : ℕ, s < S → t < L → 1 + L * s + t ≤ S * L := by
    intro s t hs ht
    have h1 : L * s + L ≤ S * L := by have : s + 1 ≤ S := hs; nlinarith only [this]
    omega
  have hdisj : Disjoint goodPos goodNeg := by
    rw [disjoint_left]
    intro v hv1 hv2
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := mem_image.mp hv1
    obtain ⟨w, hw, hwv⟩ := mem_image.mp hv2
    obtain ⟨⟨s', t'⟩, hst', rfl⟩ := mem_image.mp hw
    simp only [idxSet, mem_product, mem_range, mem_Ico] at hst hst'
    have hle1 : 1 + L * s + t ≤ S * L := hval_le_SL s t hst.1 (by omega)
    have hle2 : 1 + L * s' + t' ≤ S * L := hval_le_SL s' t' hst'.1 (by omega)
    have hp1 : isPosHalf N S L ((1 + L * s + t : ℕ) : ZMod N) := by
      rw [isPosHalf, ZMod.val_natCast_of_lt (lt_of_le_of_lt hle1 hSL_lt_N)]
      omega
    have hp2 : isPosHalf N S L ((1 + L * s' + t' : ℕ) : ZMod N) := by
      rw [isPosHalf, ZMod.val_natCast_of_lt (lt_of_le_of_lt hle2 hSL_lt_N)]
      omega
    have hn1 : isNegHalf N S L ((1 + L * s + t : ℕ) : ZMod N) := by
      rw [← hwv]; simpa [isPosHalf, isNegHalf] using hp2
    exact not_pos_and_neg h2SL _ ⟨hp1, hn1⟩
  have hsub : goodPos ∪ goodNeg ⊆ univ.filter (fun v : ZMod N ↦ isInterior b N S L v) := by
    intro v hv
    rw [mem_filter]
    refine ⟨mem_univ v, ?_⟩
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨⟨s, t⟩, hst, rfl⟩ := mem_image.mp hv
      simp only [idxSet, mem_product, mem_range, mem_Ico] at hst
      have hle : 1 + L * s + t ≤ S * L := hval_le_SL s t hst.1 (by omega)
      have hval : (((1 + L * s + t : ℕ) : ZMod N)).val = 1 + L * s + t :=
        ZMod.val_natCast_of_lt (lt_of_le_of_lt hle hSL_lt_N)
      have hmod : (1 + L * s + t - 1) % L = t := by
        rw [show 1 + L * s + t - 1 = t + L * s by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      left
      refine ⟨⟨by rw [hval]; omega, by rw [hval]; exact hle⟩, ?_, ?_⟩
      · rw [hval, hmod]; exact hst.2.1
      · rw [hval, hmod]; omega
    · obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
      obtain ⟨⟨s, t⟩, hst, rfl⟩ := mem_image.mp hw
      simp only [idxSet, mem_product, mem_range, mem_Ico] at hst
      have hle : 1 + L * s + t ≤ S * L := hval_le_SL s t hst.1 (by omega)
      have hval : (((1 + L * s + t : ℕ) : ZMod N)).val = 1 + L * s + t :=
        ZMod.val_natCast_of_lt (lt_of_le_of_lt hle hSL_lt_N)
      have hmod : (1 + L * s + t - 1) % L = t := by
        rw [show 1 + L * s + t - 1 = t + L * s by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      right
      refine ⟨⟨by rw [neg_neg, hval]; omega, by rw [neg_neg, hval]; exact hle⟩, ?_, ?_⟩
      · rw [neg_neg, hval, hmod]; exact hst.2.1
      · rw [neg_neg, hval, hmod]; omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ ↦ ((1 + L * p.1 + p.2 : ℕ) : ZMod N))
      (idxSet : Set (ℕ × ℕ)) := by
    intro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
    have h1' : s₁ < S ∧ 2 * Lmax b ≤ t₁ ∧ t₁ < L - 2 * Lmax b := by
      simpa [idxSet] using h1
    have h2' : s₂ < S ∧ 2 * Lmax b ≤ t₂ ∧ t₂ < L - 2 * Lmax b := by
      simpa [idxSet] using h2
    have hlt1 : 1 + L * s₁ + t₁ < N := lt_of_le_of_lt (hval_le_SL s₁ t₁ h1'.1 (by omega)) hSL_lt_N
    have hlt2 : 1 + L * s₂ + t₂ < N := lt_of_le_of_lt (hval_le_SL s₂ t₂ h2'.1 (by omega)) hSL_lt_N
    have hveq : 1 + L * s₁ + t₁ = 1 + L * s₂ + t₂ := by
      have := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at this
    have ht1 : t₁ < L := by omega
    have ht2 : t₂ < L := by omega
    have hdiv : s₁ = s₂ := by
      have e1 : (t₁ + L * s₁) / L = s₁ := by
        rw [Nat.add_mul_div_left _ _ hLpos, Nat.div_eq_of_lt ht1, zero_add]
      have e2 : (t₂ + L * s₂) / L = s₂ := by
        rw [Nat.add_mul_div_left _ _ hLpos, Nat.div_eq_of_lt ht2, zero_add]
      rw [← e1, ← e2, show t₁ + L * s₁ = t₂ + L * s₂ by omega]
    subst hdiv
    ext <;> omega
  have hcard_pos : goodPos.card = S * (L - 4 * Lmax b) := by
    rw [card_image_of_injOn hinj]
    dsimp [idxSet]
    rw [card_product, card_range, Nat.card_Ico]
    congr 1; omega
  have hcard_neg : goodNeg.card = S * (L - 4 * Lmax b) := by
    rw [card_image_of_injective _ neg_injective, hcard_pos]
  have hcard_good : 2 * S * (L - 4 * Lmax b) ≤
      (univ.filter (fun v : ZMod N ↦ isInterior b N S L v)).card := by
    calc 2 * S * (L - 4 * Lmax b) = goodPos.card + goodNeg.card := by
            rw [hcard_pos, hcard_neg]; ring
      _ = (goodPos ∪ goodNeg).card := (card_union_of_disjoint hdisj).symm
      _ ≤ (univ.filter (fun v : ZMod N ↦ isInterior b N S L v)).card := card_le_card hsub
  have htot : (univ.filter (fun v : ZMod N ↦ isInterior b N S L v)).card +
      (univ.filter (fun v : ZMod N ↦ ¬ isInterior b N S L v)).card = N := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (ZMod N)))
      (p := fun v : ZMod N ↦ isInterior b N S L v)
    simpa [ZMod.card] using h
  have hmul : 2 * S * (L - 4 * Lmax b) + 8 * S * Lmax b = 2 * S * L := by
    zify [show 4 * Lmax b ≤ L by omega]
    ring
  omega

/-- Lower bound on the cardinality of `Valid`. -/
lemma valid_card_ge {N S L : ℕ} [Fact N.Prime] (hr : 2 ≤ r)
    (A : Fin r → ℤ × ℤ)
    (hN_det : ∀ i j : Fin r, i ≠ j →
      (((A i).1 * (A j).2 - (A i).2 * (A j).1 : ℤ) : ZMod N) ≠ 0)
    (h2SL : 2 * S * L < N) (hL_gt : 4 * Lmax b < L)
    (hSN : N ≤ 2 * S * L + 2 * L + 1)
    (ε : ℝ) (hε_pos : 0 < ε)
    (hL_frac : 8 * (r : ℝ) * (Lmax b : ℝ) / (L : ℝ) ≤ ε / 5)
    (hN_bad : 20 * ((r : ℝ) * (2 * (L : ℝ) + 1) + (r : ℝ) ^ 2 * (2 * (L : ℝ))) / ε ≤ (N : ℝ)) :
    (1 - ε / 4) * (N : ℝ) ^ 2 ≤
      ((univ.filter fun x : ZMod N × ZMod N ↦
        (∀ i : Fin r, isInterior b N S L (linEval (A i) N x)) ∧
        (∀ i j : Fin r, i ≠ j →
          slotOf N S L (linEval (A i) N x) ≠ slotOf N S L (linEval (A j) N x))).card : ℝ) := by
  have hL_pos : 0 < L := by omega
  have hN_pos : 0 < N := (Fact.out : N.Prime).pos
  have hN_R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have h2SL_R : (2 * S * L : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2SL.le
  set Valid : Finset (ZMod N × ZMod N) := univ.filter fun x ↦
    (∀ i : Fin r, isInterior b N S L (linEval (A i) N x)) ∧
    (∀ i j : Fin r, i ≠ j → slotOf N S L (linEval (A i) N x) ≠ slotOf N S L (linEval (A j) N x))
  let badInt (i : Fin r) : Finset (ZMod N × ZMod N) :=
    univ.filter (fun x ↦ ¬ isInterior b N S L (linEval (A i) N x))
  let badSlot (i j : Fin r) : Finset (ZMod N × ZMod N) :=
    univ.filter (fun x ↦
      (isPosHalf N S L (linEval (A i) N x) ∨ isNegHalf N S L (linEval (A i) N x)) ∧
      (isPosHalf N S L (linEval (A j) N x) ∨ isNegHalf N S L (linEval (A j) N x)) ∧
      slotOf N S L (linEval (A i) N x) = slotOf N S L (linEval (A j) N x))
  have hbadInt_card : ∀ i : Fin r, (badInt i).card ≤ (8 * S * Lmax b + 2 * L + 1) * N := by
    intro i
    have hexj : ∃ j : Fin r, i ≠ j := by
      have hr0 : 0 < r := by omega
      have hr1 : 1 < r := by omega
      by_cases hi0 : i.val = 0
      · exact ⟨⟨1, hr1⟩, fun h ↦ by have h' := congrArg Fin.val h; dsimp at h'; omega⟩
      · exact ⟨⟨0, hr0⟩, fun h ↦ by have h' := congrArg Fin.val h; dsimp at h'; omega⟩
    obtain ⟨j, hij⟩ := hexj
    let eqv := evalPairEquiv (A i) (A j) (hN_det i j hij)
    have hcard_eq : (badInt i).card =
        ((univ.filter (fun v : ZMod N ↦ ¬ isInterior b N S L v)) ×ˢ (univ : Finset (ZMod N))).card := by
      refine Finset.card_bij (fun x _ ↦ eqv x) ?_ ?_ ?_
      · intro x hx
        simp only [badInt, mem_filter, mem_univ, true_and] at hx
        simp [eqv, evalPairEquiv, mem_product, hx]
      · intro x₁ _ x₂ _ h; exact eqv.injective h
      · intro y hy
        simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hy
        refine ⟨eqv.symm y, ?_, eqv.apply_symm_apply y⟩
        simp only [badInt, mem_filter, mem_univ, true_and]
        have hfst : linEval (A i) N (eqv.symm y) = y.1 := by
          have := congrArg Prod.fst (eqv.apply_symm_apply y)
          simpa [eqv, evalPairEquiv] using this
        rwa [hfst]
    rw [hcard_eq, card_product, card_univ, ZMod.card]
    exact Nat.mul_le_mul_right N (card_not_interior_le b h2SL hL_gt hSN)
  have hbadSlot_card : ∀ i j : Fin r, i ≠ j → (badSlot i j).card ≤ 2 * L * N := by
    intro i j hij
    let eqv := evalPairEquiv (A i) (A j) (hN_det i j hij)
    let fibers : Finset (ZMod N × ZMod N) :=
      (univ : Finset (ZMod N)).biUnion fun u ↦
        (univ.filter (fun v : ZMod N ↦
          (isPosHalf N S L v ∨ isNegHalf N S L v) ∧ slotOf N S L v = slotOf N S L u)).image (fun v ↦ (u, v))
    have hsub : (badSlot i j).image eqv ⊆ fibers := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      simp only [badSlot, mem_filter, mem_univ, true_and] at hx
      simp only [fibers, mem_biUnion, mem_univ, true_and, mem_image, mem_filter]
      exact ⟨linEval (A i) N x, linEval (A j) N x, ⟨hx.2.1, hx.2.2.symm⟩, rfl⟩
    calc (badSlot i j).card = ((badSlot i j).image eqv).card := (card_image_of_injective _ eqv.injective).symm
      _ ≤ fibers.card := card_le_card hsub
      _ ≤ ∑ u : ZMod N, ((univ.filter (fun v : ZMod N ↦
            (isPosHalf N S L v ∨ isNegHalf N S L v) ∧ slotOf N S L v = slotOf N S L u)).image (fun v ↦ (u, v))).card :=
          card_biUnion_le
      _ ≤ ∑ _u : ZMod N, (2 * L) := sum_le_sum fun u _ ↦
          card_image_le.trans (card_slot_fiber_le hL_pos (slotOf N S L u))
      _ = 2 * L * N := by rw [sum_const, card_univ, ZMod.card, smul_eq_mul, mul_comm]
  have hcompl_sub : (univ \ Valid) ⊆
      (univ.biUnion badInt) ∪ (univ.biUnion fun i ↦ (univ.filter (· ≠ i)).biUnion fun j ↦ badSlot i j) := by
    intro x hx
    simp only [mem_sdiff, mem_univ, true_and, Valid, mem_filter] at hx
    rw [mem_union]
    by_cases hint : ∀ i : Fin r, isInterior b N S L (linEval (A i) N x)
    · right
      have hnot : ¬ ∀ i j : Fin r, i ≠ j → slotOf N S L (linEval (A i) N x) ≠ slotOf N S L (linEval (A j) N x) :=
        fun h ↦ hx ⟨hint, h⟩
      push Not at hnot
      obtain ⟨i, j, hij, heq⟩ := hnot
      simp only [mem_biUnion, mem_univ, true_and, mem_filter]
      exact ⟨i, j, hij.symm, by
        simp only [badSlot, mem_filter, mem_univ, true_and]
        exact ⟨(hint i).imp And.left And.left, (hint j).imp And.left And.left, heq⟩⟩
    · left
      push Not at hint
      obtain ⟨i, hi⟩ := hint
      simp only [mem_biUnion, mem_univ, true_and, badInt, mem_filter]
      exact ⟨i, hi⟩
  have hcompl_le : (univ \ Valid).card ≤
      r * ((8 * S * Lmax b + 2 * L + 1) * N) + r * r * (2 * L * N) := by
    calc (univ \ Valid).card
        ≤ ((univ.biUnion badInt) ∪
            (univ.biUnion fun i ↦ (univ.filter (· ≠ i)).biUnion fun j ↦ badSlot i j)).card :=
          card_le_card hcompl_sub
      _ ≤ (univ.biUnion badInt).card +
            (univ.biUnion fun i ↦ (univ.filter (· ≠ i)).biUnion fun j ↦ badSlot i j).card :=
          card_union_le _ _
      _ ≤ (∑ i : Fin r, (badInt i).card) +
            ∑ i : Fin r, ((univ.filter (· ≠ i)).biUnion fun j ↦ badSlot i j).card :=
          add_le_add card_biUnion_le card_biUnion_le
      _ ≤ (∑ _i : Fin r, ((8 * S * Lmax b + 2 * L + 1) * N)) +
            ∑ i : Fin r, ∑ j ∈ univ.filter (· ≠ i), (badSlot i j).card :=
          add_le_add (sum_le_sum fun i _ ↦ hbadInt_card i)
            (sum_le_sum fun i _ ↦ card_biUnion_le)
      _ ≤ (∑ _i : Fin r, ((8 * S * Lmax b + 2 * L + 1) * N)) +
            ∑ _i : Fin r, ∑ _j : Fin r, (2 * L * N) := by
          gcongr with i _
          calc ∑ j ∈ univ.filter (· ≠ i), (badSlot i j).card
              ≤ ∑ j ∈ univ.filter (· ≠ i), (2 * L * N) :=
                sum_le_sum fun j hj ↦ hbadSlot_card i j (mem_filter.mp hj).2.symm
            _ ≤ ∑ _j : Fin r, (2 * L * N) :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
      _ = r * ((8 * S * Lmax b + 2 * L + 1) * N) + r * r * (2 * L * N) := by
          simp [mul_assoc]
  have hsum_v : Valid.card + (univ \ Valid).card = N * N := by
    have h1 := card_sdiff_add_card_eq_card (subset_univ Valid)
    rw [card_univ, Fintype.card_prod, ZMod.card] at h1
    omega
  set C_bad : ℝ := (r : ℝ) * (2 * (L : ℝ) + 1) + (r : ℝ) ^ 2 * (2 * (L : ℝ))
  have hcompl_R : ((univ \ Valid).card : ℝ) ≤ (ε / 4) * (N : ℝ) ^ 2 := by
    have h1 : ((univ \ Valid).card : ℝ) ≤
        (r : ℝ) * ((8 * (S : ℝ) * (Lmax b : ℝ) + 2 * (L : ℝ) + 1) * (N : ℝ)) +
          (r : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ)) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcompl_le
      push_cast at this; linarith only [this]
    have h2 : (r : ℝ) * (8 * (S : ℝ) * (Lmax b : ℝ)) * (N : ℝ) ≤ (ε / 5) * (N : ℝ) ^ 2 := by
      have hS_le : (S : ℝ) ≤ (N : ℝ) / (2 * (L : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]; linarith only [h2SL_R]
      have hL_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos
      calc (r : ℝ) * (8 * (S : ℝ) * (Lmax b : ℝ)) * (N : ℝ)
          ≤ (r : ℝ) * (8 * ((N : ℝ) / (2 * (L : ℝ))) * (Lmax b : ℝ)) * (N : ℝ) := by gcongr
        _ = (1 / 2) * (8 * (r : ℝ) * (Lmax b : ℝ) / (L : ℝ)) * (N : ℝ) ^ 2 := by
            field_simp
        _ ≤ (1 / 2) * (ε / 5) * (N : ℝ) ^ 2 := by gcongr
        _ ≤ (ε / 5) * (N : ℝ) ^ 2 := by nlinarith only [hε_pos, sq_nonneg (N : ℝ)]
    have h3 : C_bad * (N : ℝ) ≤ (ε / 20) * (N : ℝ) ^ 2 := by
      have hmul : 20 * C_bad ≤ (N : ℝ) * ε := (div_le_iff₀ hε_pos).mp hN_bad
      nlinarith only [hmul, hN_R]
    have hsplit : (r : ℝ) * ((8 * (S : ℝ) * (Lmax b : ℝ) + 2 * (L : ℝ) + 1) * (N : ℝ)) +
        (r : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ)) =
        (r : ℝ) * (8 * (S : ℝ) * (Lmax b : ℝ)) * (N : ℝ) + C_bad * (N : ℝ) := by
      dsimp [C_bad]; ring
    linarith only [h1, h2, h3, hsplit]
  have hsum_R : (Valid.card : ℝ) + ((univ \ Valid).card : ℝ) = (N : ℝ) ^ 2 := by
    have := congrArg (Nat.cast (R := ℝ)) hsum_v
    push_cast at this; linarith only [this]
  linarith only [hcompl_R, hsum_R]

/-- Variance / second-moment upper bound on a single vertex `(i, u)` over all colorings `ω`. -/
lemma vertex_excess_sum_le {S Q N L : ℕ} [Fact N.Prime] (hS : 0 < S) (hQ : 2 * Lmax b < Q)
    (hL : 0 < L)
    (hr : 2 ≤ r) (A : Fin r → ℤ × ℤ)
    (hN_det : ∀ i j : Fin r, i ≠ j →
      (((A i).1 * (A j).2 - (A i).2 * (A j).1 : ℤ) : ZMod N) ≠ 0)
    (Valid : Finset (ZMod N × ZMod N))
    (hValid : ∀ x ∈ Valid,
      (∀ i : Fin r, isInterior b N S L (linEval (A i) N x)) ∧
      (∀ i j : Fin r, i ≠ j → slotOf N S L (linEval (A i) N x) ≠ slotOf N S L (linEval (A j) N x)))
    (i : Fin r) (u : ZMod N) (D : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hD_ge : (1 + ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) ≤ (D : ℝ)) :
    ∑ ω : Fin S → Fin Q,
      ((((Valid.filter (fun x ↦ linEval (A i) N x = u ∧
          ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
            keyOf b Q hQ N S L j (linEval (A j) N x))).card - D : ℕ) : ℝ)) ≤
      (8 * (r : ℝ) ^ 2 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε) * ((Q : ℝ) ^ S) := by
  have hQpos : 0 < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
  let Liu : Finset (ZMod N × ZMod N) := Valid.filter (fun x ↦ linEval (A i) N x = u)
  have hLiu_le : Liu.card ≤ N := by
    have hexj : ∃ j : Fin r, i ≠ j := by
      have hr0 : 0 < r := by omega
      have hr1 : 1 < r := by omega
      by_cases hi0 : i.val = 0
      · exact ⟨⟨1, hr1⟩, fun h ↦ by have h' := congrArg Fin.val h; dsimp at h'; omega⟩
      · exact ⟨⟨0, hr0⟩, fun h ↦ by have h' := congrArg Fin.val h; dsimp at h'; omega⟩
    obtain ⟨j, hij⟩ := hexj
    let eqv := evalPairEquiv (A i) (A j) (hN_det i j hij)
    have hinj : Set.InjOn (fun x ↦ linEval (A j) N x) (Liu : Set (ZMod N × ZMod N)) := by
      intro x₁ hx₁ x₂ hx₂ heq
      have h1 : linEval (A i) N x₁ = u := (mem_filter.mp hx₁).2
      have h2 : linEval (A i) N x₂ = u := (mem_filter.mp hx₂).2
      apply eqv.injective
      ext
      · change linEval (A i) N x₁ = linEval (A i) N x₂; rw [h1, h2]
      · exact heq
    calc Liu.card = (Liu.image (fun x ↦ linEval (A j) N x)).card :=
            (card_image_of_injOn hinj).symm
      _ ≤ (univ : Finset (ZMod N)).card := card_le_card (subset_univ _)
      _ = N := ZMod.card N
  by_cases hLiu_empty : Liu = ∅
  · have hzero : ∀ ω : Fin S → Fin Q,
        (Valid.filter (fun x ↦ linEval (A i) N x = u ∧
          ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
            keyOf b Q hQ N S L j (linEval (A j) N x))).card = 0 := by
      intro ω
      refine card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_)
      have hxLiu : x ∈ Liu := mem_filter.mpr ⟨(mem_filter.mp hx).1, (mem_filter.mp hx).2.1⟩
      rw [hLiu_empty] at hxLiu
      exact notMem_empty x hxLiu
    simp_rw [hzero, Nat.zero_sub, Nat.cast_zero, sum_const_zero]
    positivity
  have hLiu_ne : Liu.Nonempty := nonempty_iff_ne_empty.mpr hLiu_empty
  obtain ⟨x_any, hx_any⟩ := hLiu_ne
  have hu_int : isInterior b N S L u := by
    have h1 := (hValid x_any (mem_filter.mp hx_any).1).1 i
    rwa [(mem_filter.mp hx_any).2] at h1
  let s₀ : Fin S := slotFin N S L hS u
  let k₀ : Fin Q := keyOf b Q hQ N S L i u
  let E0 (ω : Fin S → Fin Q) : Prop := ω s₀ = k₀
  let Ex (x : ZMod N × ZMod N) (ω : Fin S → Fin Q) : Prop :=
    ∀ j : Fin r, j ≠ i →
      ω (slotFin N S L hS (linEval (A j) N x)) = keyOf b Q hQ N S L j (linEval (A j) N x)
  let Z (ω : Fin S → Fin Q) : ℝ := ∑ x ∈ Liu, if Ex x ω then (1 : ℝ) else 0
  let μ : ℝ := (Liu.card : ℝ) / ((Q : ℝ) ^ (r - 1))
  have hdeg_eq : ∀ ω : Fin S → Fin Q,
      ((Valid.filter (fun x ↦ linEval (A i) N x = u ∧
          ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
            keyOf b Q hQ N S L j (linEval (A j) N x))).card : ℝ) =
        if E0 ω then Z ω else 0 := by
    intro ω
    by_cases h0 : E0 ω
    · rw [if_pos h0]
      dsimp [Z]
      rw [sum_boole]
      exact_mod_cast congrArg Finset.card (by
        ext x
        simp only [Liu, mem_filter]
        constructor
        · rintro ⟨hxV, hxu, hall⟩
          exact ⟨⟨hxV, hxu⟩, fun j _ ↦ hall j⟩
        · rintro ⟨⟨hxV, hxu⟩, hrest⟩
          refine ⟨hxV, hxu, fun j ↦ ?_⟩
          by_cases hji : j = i
          · subst hji; rw [hxu]; exact h0
          · exact hrest j hji)
    · rw [if_neg h0]
      have hcard0 : (Valid.filter (fun x ↦ linEval (A i) N x = u ∧
          ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
            keyOf b Q hQ N S L j (linEval (A j) N x))).card = 0 := by
        refine card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_)
        have h1 := (mem_filter.mp hx).2.2 i
        rw [(mem_filter.mp hx).2.1] at h1
        exact h0 h1
      simp [hcard0]
  let T' (x : ZMod N × ZMod N) : Finset (Fin S) :=
    (univ.erase i).image (fun j ↦ slotFin N S L hS (linEval (A j) N x))
  have hT'_spec : ∀ x ∈ Liu, s₀ ∉ T' x ∧ (T' x).card = r - 1 := by
    intro x hx
    have hxV := (mem_filter.mp hx).1
    have hxu := (mem_filter.mp hx).2
    have hV := hValid x hxV
    have hinj : Set.InjOn (fun j : Fin r ↦ slotFin N S L hS (linEval (A j) N x))
        ((univ.erase i : Finset (Fin r)) : Set (Fin r)) := by
      intro j₁ _ j₂ _ heq
      by_contra hne
      have h1 := congrArg Fin.val heq
      rw [slotFin_val hS hL ((hV.1 j₁).imp And.left And.left),
          slotFin_val hS hL ((hV.1 j₂).imp And.left And.left)] at h1
      exact hV.2 j₁ j₂ hne h1
    constructor
    · intro hmem
      obtain ⟨j, hj, heq⟩ := mem_image.mp hmem
      have hji : j ≠ i := (mem_erase.mp hj).1
      have h1 := congrArg Fin.val heq
      dsimp [s₀] at h1
      rw [slotFin_val hS hL ((hV.1 j).imp And.left And.left),
          slotFin_val hS hL (hu_int.imp And.left And.left), ← hxu] at h1
      exact hV.2 j i hji h1
    · rw [card_image_of_injOn hinj, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have hE0_cnt : ((univ.filter E0).card : ℝ) * (Q : ℝ) = (Q : ℝ) ^ S := by
    have h := card_filter_eq_on (S := S) (Q := Q) ({s₀} : Finset (Fin S)) (fun _ ↦ k₀)
    have hEq : univ.filter E0 = univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ ({s₀} : Finset (Fin S)), ω t = k₀) := by
      ext ω; simp [E0]
    rw [hEq]
    have hnat : (univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ ({s₀} : Finset (Fin S)), ω t = k₀)).card * Q = Q ^ S := by
      simpa using h
    exact_mod_cast hnat
  have hE0x_cnt : ∀ x ∈ Liu,
      ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω)).card : ℝ) * (Q : ℝ) ^ r = (Q : ℝ) ^ S := by
    intro x hx
    have hxV := (mem_filter.mp hx).1
    have hxu := (mem_filter.mp hx).2
    have hV := hValid x hxV
    let T := insert s₀ (T' x)
    let val : Fin S → Fin Q := fun s ↦
      if h : ∃ j : Fin r, slotFin N S L hS (linEval (A j) N x) = s
      then keyOf b Q hQ N S L (Classical.choose h) (linEval (A (Classical.choose h)) N x)
      else ⟨0, hQpos⟩
    have hval_at : ∀ j : Fin r,
        val (slotFin N S L hS (linEval (A j) N x)) = keyOf b Q hQ N S L j (linEval (A j) N x) := by
      intro j
      have hex : ∃ j' : Fin r, slotFin N S L hS (linEval (A j') N x) = slotFin N S L hS (linEval (A j) N x) :=
        ⟨j, rfl⟩
      dsimp [val]
      rw [dif_pos hex]
      have hch := Classical.choose_spec hex
      have hjeq : Classical.choose hex = j := by
        by_contra hne
        have h1 := congrArg Fin.val hch
        rw [slotFin_val hS hL ((hV.1 _).imp And.left And.left),
            slotFin_val hS hL ((hV.1 j).imp And.left And.left)] at h1
        exact hV.2 _ j hne h1
      rw [hjeq]
    have hTcard : T.card = r := by
      obtain ⟨hnot, hcard⟩ := hT'_spec x hx
      rw [card_insert_of_notMem hnot, hcard]
      omega
    have hEq : univ.filter (fun ω ↦ E0 ω ∧ Ex x ω) =
        univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ T, ω t = val t) := by
      ext ω
      simp only [mem_filter, mem_univ, true_and, T, mem_insert, T', mem_image, mem_erase]
      constructor
      · rintro ⟨h0, hrest⟩ t ht
        rcases ht with rfl | ⟨j, ⟨hji, _⟩, rfl⟩
        · have hv0 := hval_at i
          rw [hxu] at hv0
          rw [hv0]; exact h0
        · rw [hval_at j]; exact hrest j hji
      · intro hall
        refine ⟨?_, fun j hji ↦ ?_⟩
        · have h1 := hall s₀ (Or.inl rfl)
          have hv0 := hval_at i
          rw [hxu] at hv0
          rwa [hv0] at h1
        · have h1 := hall (slotFin N S L hS (linEval (A j) N x))
            (Or.inr ⟨j, ⟨hji, trivial⟩, rfl⟩)
          rwa [hval_at j] at h1
    rw [hEq]
    have h := card_filter_eq_on T val
    rw [hTcard] at h
    exact_mod_cast h
  have hE0xx'_cnt : ∀ x ∈ Liu, ∀ x' ∈ Liu, Disjoint (T' x) (T' x') →
      ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω ∧ Ex x' ω)).card : ℝ) * (Q : ℝ) ^ (2 * r - 1) =
        (Q : ℝ) ^ S := by
    intro x hx x' hx' hdisj
    have hxV := (mem_filter.mp hx).1
    have hx'V := (mem_filter.mp hx').1
    have hV := hValid x hxV
    have hV' := hValid x' hx'V
    let T := insert s₀ (T' x ∪ T' x')
    let val : Fin S → Fin Q := fun s ↦
      if s = s₀ then k₀
      else if h : ∃ j : Fin r, j ≠ i ∧ slotFin N S L hS (linEval (A j) N x) = s
      then keyOf b Q hQ N S L (Classical.choose h) (linEval (A (Classical.choose h)) N x)
      else if h' : ∃ j : Fin r, j ≠ i ∧ slotFin N S L hS (linEval (A j) N x') = s
      then keyOf b Q hQ N S L (Classical.choose h') (linEval (A (Classical.choose h')) N x')
      else ⟨0, hQpos⟩
    have hval_x : ∀ j : Fin r, j ≠ i →
        val (slotFin N S L hS (linEval (A j) N x)) = keyOf b Q hQ N S L j (linEval (A j) N x) := by
      intro j hji
      have hne0 : slotFin N S L hS (linEval (A j) N x) ≠ s₀ := by
        intro heq
        exact (hT'_spec x hx).1 (heq ▸ mem_image.mpr ⟨j, mem_erase.mpr ⟨hji, mem_univ j⟩, rfl⟩)
      have hex : ∃ j' : Fin r, j' ≠ i ∧
          slotFin N S L hS (linEval (A j') N x) = slotFin N S L hS (linEval (A j) N x) :=
        ⟨j, hji, rfl⟩
      dsimp [val]
      rw [if_neg hne0, dif_pos hex]
      have hch := (Classical.choose_spec hex).2
      have hjeq : Classical.choose hex = j := by
        by_contra hne
        have h1 := congrArg Fin.val hch
        rw [slotFin_val hS hL ((hV.1 _).imp And.left And.left),
            slotFin_val hS hL ((hV.1 j).imp And.left And.left)] at h1
        exact hV.2 _ j hne h1
      rw [hjeq]
    have hval_x' : ∀ j : Fin r, j ≠ i →
        val (slotFin N S L hS (linEval (A j) N x')) = keyOf b Q hQ N S L j (linEval (A j) N x') := by
      intro j hji
      have hmem' : slotFin N S L hS (linEval (A j) N x') ∈ T' x' :=
        mem_image.mpr ⟨j, mem_erase.mpr ⟨hji, mem_univ j⟩, rfl⟩
      have hne0 : slotFin N S L hS (linEval (A j) N x') ≠ s₀ := by
        intro heq; exact (hT'_spec x' hx').1 (heq ▸ hmem')
      have hnotx : ¬ ∃ j' : Fin r, j' ≠ i ∧
          slotFin N S L hS (linEval (A j') N x) = slotFin N S L hS (linEval (A j) N x') := by
        rintro ⟨j', hj'i, heq⟩
        have hmemx : slotFin N S L hS (linEval (A j) N x') ∈ T' x :=
          heq ▸ mem_image.mpr ⟨j', mem_erase.mpr ⟨hj'i, mem_univ j'⟩, rfl⟩
        exact Finset.disjoint_left.mp hdisj hmemx hmem'
      have hex' : ∃ j' : Fin r, j' ≠ i ∧
          slotFin N S L hS (linEval (A j') N x') = slotFin N S L hS (linEval (A j) N x') :=
        ⟨j, hji, rfl⟩
      dsimp [val]
      rw [if_neg hne0, dif_neg hnotx, dif_pos hex']
      have hch := (Classical.choose_spec hex').2
      have hjeq : Classical.choose hex' = j := by
        by_contra hne
        have h1 := congrArg Fin.val hch
        rw [slotFin_val hS hL ((hV'.1 _).imp And.left And.left),
            slotFin_val hS hL ((hV'.1 j).imp And.left And.left)] at h1
        exact hV'.2 _ j hne h1
      rw [hjeq]
    have hTcard : T.card = 2 * r - 1 := by
      obtain ⟨hnot1, hc1⟩ := hT'_spec x hx
      obtain ⟨hnot2, hc2⟩ := hT'_spec x' hx'
      have hnotU : s₀ ∉ T' x ∪ T' x' := by simp [hnot1, hnot2]
      rw [card_insert_of_notMem hnotU, card_union_of_disjoint hdisj, hc1, hc2]
      omega
    have hEq : univ.filter (fun ω ↦ E0 ω ∧ Ex x ω ∧ Ex x' ω) =
        univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ T, ω t = val t) := by
      ext ω
      simp only [mem_filter, mem_univ, true_and, T, mem_insert, mem_union, T', mem_image, mem_erase]
      constructor
      · rintro ⟨h0, h1, h2⟩ t ht
        rcases ht with rfl | ⟨j, ⟨hji, _⟩, rfl⟩ | ⟨j, ⟨hji, _⟩, rfl⟩
        · dsimp [val]; rw [if_pos rfl]; exact h0
        · rw [hval_x j hji]; exact h1 j hji
        · rw [hval_x' j hji]; exact h2 j hji
      · intro hall
        refine ⟨?_, fun j hji ↦ ?_, fun j hji ↦ ?_⟩
        · have := hall s₀ (Or.inl rfl); simpa [val, E0] using this
        · have := hall _ (Or.inr (Or.inl ⟨j, ⟨hji, trivial⟩, rfl⟩))
          rwa [hval_x j hji] at this
        · have := hall _ (Or.inr (Or.inr ⟨j, ⟨hji, trivial⟩, rfl⟩))
          rwa [hval_x' j hji] at this
    rw [hEq]
    have h := card_filter_eq_on T val
    rw [hTcard] at h
    exact_mod_cast h
  have hoverlap_le : ∀ x ∈ Liu,
      (Liu.filter (fun x' ↦ ¬ Disjoint (T' x) (T' x'))).card ≤ 2 * r * r * L := by
    intro x hx
    have hsub : Liu.filter (fun x' ↦ ¬ Disjoint (T' x) (T' x')) ⊆
        (univ.erase i).biUnion fun j ↦ (univ.erase i).biUnion fun k ↦
          Liu.filter (fun x' ↦ slotOf N S L (linEval (A k) N x') = slotOf N S L (linEval (A j) N x)) := by
      intro x' hx'
      obtain ⟨hx'L, hnd⟩ := mem_filter.mp hx'
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨s, hs1, hs2⟩ := hnd
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hs1
      obtain ⟨k, hk, heq⟩ := mem_image.mp hs2
      simp only [mem_biUnion, mem_filter]
      refine ⟨j, hj, k, hk, hx'L, ?_⟩
      have h1 := congrArg Fin.val heq
      rw [slotFin_val hS hL (((hValid x' (mem_filter.mp hx'L).1).1 k).imp And.left And.left),
          slotFin_val hS hL (((hValid x (mem_filter.mp hx).1).1 j).imp And.left And.left)] at h1
      exact h1
    have hinner : ∀ j ∈ univ.erase i, ∀ k ∈ univ.erase i,
        (Liu.filter (fun x' ↦ slotOf N S L (linEval (A k) N x') =
          slotOf N S L (linEval (A j) N x))).card ≤ 2 * L := by
      intro j _ k hk
      have hki : k ≠ i := (mem_erase.mp hk).1
      let eqv := evalPairEquiv (A i) (A k) (hN_det i k hki.symm)
      have hinj : Set.InjOn (fun x' ↦ linEval (A k) N x')
          ((Liu.filter (fun x' ↦ slotOf N S L (linEval (A k) N x') =
            slotOf N S L (linEval (A j) N x))) : Set (ZMod N × ZMod N)) := by
        intro x₁ hx₁ x₂ hx₂ heq
        have h1 : linEval (A i) N x₁ = u := (mem_filter.mp (mem_filter.mp hx₁).1).2
        have h2 : linEval (A i) N x₂ = u := (mem_filter.mp (mem_filter.mp hx₂).1).2
        apply eqv.injective
        ext
        · change linEval (A i) N x₁ = linEval (A i) N x₂; rw [h1, h2]
        · exact heq
      have himg_sub : (Liu.filter (fun x' ↦ slotOf N S L (linEval (A k) N x') =
            slotOf N S L (linEval (A j) N x))).image (fun x' ↦ linEval (A k) N x') ⊆
          univ.filter (fun v : ZMod N ↦ (isPosHalf N S L v ∨ isNegHalf N S L v) ∧
            slotOf N S L v = slotOf N S L (linEval (A j) N x)) := by
        intro v hv
        obtain ⟨x', hx', rfl⟩ := mem_image.mp hv
        obtain ⟨hx'L, hsl⟩ := mem_filter.mp hx'
        exact mem_filter.mpr ⟨mem_univ _,
          ((hValid x' (mem_filter.mp hx'L).1).1 k).imp And.left And.left, hsl⟩
      calc (Liu.filter _).card = ((Liu.filter _).image (fun x' ↦ linEval (A k) N x')).card :=
              (card_image_of_injOn hinj).symm
        _ ≤ (univ.filter _).card := card_le_card himg_sub
        _ ≤ 2 * L := card_slot_fiber_le hL _
    calc (Liu.filter (fun x' ↦ ¬ Disjoint (T' x) (T' x'))).card
        ≤ ((univ.erase i).biUnion fun j ↦ (univ.erase i).biUnion fun k ↦
            Liu.filter (fun x' ↦ slotOf N S L (linEval (A k) N x') =
              slotOf N S L (linEval (A j) N x))).card := card_le_card hsub
      _ ≤ ∑ j ∈ univ.erase i, ((univ.erase i).biUnion fun k ↦
            Liu.filter (fun x' ↦ slotOf N S L (linEval (A k) N x') =
              slotOf N S L (linEval (A j) N x))).card := card_biUnion_le
      _ ≤ ∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i,
            (Liu.filter (fun x' ↦ slotOf N S L (linEval (A k) N x') =
              slotOf N S L (linEval (A j) N x))).card :=
          sum_le_sum fun _ _ ↦ card_biUnion_le
      _ ≤ ∑ _j ∈ univ.erase i, ∑ _k ∈ univ.erase i, (2 * L) :=
          sum_le_sum fun j hj ↦ sum_le_sum fun k hk ↦ hinner j hj k hk
      _ ≤ ∑ _j : Fin r, ∑ _k : Fin r, (2 * L) := by
          refine (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)).trans ?_
          refine sum_le_sum fun _ _ ↦
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
      _ = 2 * r * r * L := by simp; ring
  have hvar : ∑ ω : Fin S → Fin Q, (if E0 ω then (Z ω - μ) ^ 2 else 0) ≤
      (2 * (r : ℝ) ^ 2 * (L : ℝ) * (N : ℝ) / (Q : ℝ)) * ((Q : ℝ) ^ S) := by
    have hexpand : ∑ ω : Fin S → Fin Q, (if E0 ω then (Z ω - μ) ^ 2 else 0) =
        (∑ ω : Fin S → Fin Q, if E0 ω then (Z ω) ^ 2 else 0) -
        2 * μ * (∑ ω : Fin S → Fin Q, if E0 ω then Z ω else 0) +
        μ ^ 2 * (∑ ω : Fin S → Fin Q, if E0 ω then (1 : ℝ) else 0) := by
      simp_rw [mul_sum]
      rw [← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun ω _ ↦ ?_
      split_ifs <;> ring
    have hsum1 : (∑ ω : Fin S → Fin Q, if E0 ω then (1 : ℝ) else 0) = (Q : ℝ) ^ S / (Q : ℝ) := by
      rw [sum_boole, ← hE0_cnt]
      field_simp
    have hsumZ : (∑ ω : Fin S → Fin Q, if E0 ω then Z ω else 0) = μ * ((Q : ℝ) ^ S / (Q : ℝ)) := by
      have hswap : (∑ ω : Fin S → Fin Q, if E0 ω then Z ω else 0) =
          ∑ x ∈ Liu, ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω)).card : ℝ) := by
        have hstep : (∑ ω : Fin S → Fin Q, if E0 ω then Z ω else 0) =
            ∑ ω : Fin S → Fin Q, ∑ x ∈ Liu, (if E0 ω ∧ Ex x ω then (1 : ℝ) else 0) := by
          refine sum_congr rfl fun ω _ ↦ ?_
          by_cases h0 : E0 ω
          · rw [if_pos h0]; dsimp [Z]; refine sum_congr rfl fun x _ ↦ by simp [h0]
          · rw [if_neg h0]; symm; exact sum_eq_zero fun x _ ↦ by simp [h0]
        rw [hstep, sum_comm]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sum_boole]
      rw [hswap]
      have hterm : ∀ x ∈ Liu, ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω)).card : ℝ) =
          (Q : ℝ) ^ S / (Q : ℝ) ^ r := by
        intro x hx
        rw [← hE0x_cnt x hx]
        field_simp
      rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
      dsimp [μ]
      have hpow : (Q : ℝ) ^ r = (Q : ℝ) ^ (r - 1) * (Q : ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hpow]
      field_simp
    have hsumZ2 : (∑ ω : Fin S → Fin Q, if E0 ω then (Z ω) ^ 2 else 0) ≤
        μ ^ 2 * ((Q : ℝ) ^ S / (Q : ℝ)) +
        (2 * (r : ℝ) ^ 2 * (L : ℝ) * (N : ℝ) / (Q : ℝ)) * ((Q : ℝ) ^ S) := by
      have hswap : (∑ ω : Fin S → Fin Q, if E0 ω then (Z ω) ^ 2 else 0) =
          ∑ x ∈ Liu, ∑ x' ∈ Liu,
            ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω ∧ Ex x' ω)).card : ℝ) := by
        have hsq : ∀ ω : Fin S → Fin Q,
            (if E0 ω then (Z ω) ^ 2 else 0) =
              ∑ x ∈ Liu, ∑ x' ∈ Liu, (if E0 ω ∧ Ex x ω ∧ Ex x' ω then (1 : ℝ) else 0) := by
          intro ω
          by_cases h0 : E0 ω
          · rw [if_pos h0, pow_two]
            dsimp [Z]
            rw [sum_mul]
            refine sum_congr rfl fun x _ ↦ ?_
            rw [mul_sum]
            refine sum_congr rfl fun x' _ ↦ ?_
            by_cases h1 : Ex x ω <;> by_cases h2 : Ex x' ω <;> simp [h0, h1, h2]
          · simp [h0]
        simp_rw [hsq]
        rw [sum_comm]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun x' _ ↦ ?_
        rw [sum_boole]
      rw [hswap]
      have hterm : ∀ x ∈ Liu, ∀ x' ∈ Liu,
          ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω ∧ Ex x' ω)).card : ℝ) ≤
            (Q : ℝ) ^ S / (Q : ℝ) ^ (2 * r - 1) +
            if ¬ Disjoint (T' x) (T' x') then (Q : ℝ) ^ S / (Q : ℝ) else 0 := by
        intro x hx x' hx'
        by_cases hd : Disjoint (T' x) (T' x')
        · rw [if_neg (not_not.mpr hd), add_zero]
          have := hE0xx'_cnt x hx x' hx' hd
          rw [← this]
          field_simp
          exact le_rfl
        · rw [if_pos hd]
          have hsub : ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω ∧ Ex x' ω)).card : ℝ) ≤
              ((univ.filter E0).card : ℝ) := by
            have hle : (univ.filter (fun ω ↦ E0 ω ∧ Ex x ω ∧ Ex x' ω)).card ≤ (univ.filter E0).card := by
              refine card_le_card fun ω hω ↦ ?_
              exact mem_filter.mpr ⟨mem_univ ω, (mem_filter.mp hω).2.1⟩
            exact_mod_cast hle
          have hE0_eq : ((univ.filter E0).card : ℝ) = (Q : ℝ) ^ S / (Q : ℝ) := by
            rw [← hE0_cnt]; field_simp
          have hnn : 0 ≤ (Q : ℝ) ^ S / (Q : ℝ) ^ (2 * r - 1) := by positivity
          linarith only [hsub, hE0_eq, hnn]
      calc ∑ x ∈ Liu, ∑ x' ∈ Liu, ((univ.filter (fun ω ↦ E0 ω ∧ Ex x ω ∧ Ex x' ω)).card : ℝ)
          ≤ ∑ x ∈ Liu, ∑ x' ∈ Liu,
              ((Q : ℝ) ^ S / (Q : ℝ) ^ (2 * r - 1) +
                if ¬ Disjoint (T' x) (T' x') then (Q : ℝ) ^ S / (Q : ℝ) else 0) :=
            sum_le_sum fun x hx ↦ sum_le_sum fun x' hx' ↦ hterm x hx x' hx'
        _ = (∑ _x ∈ Liu, ∑ _x' ∈ Liu, ((Q : ℝ) ^ S / (Q : ℝ) ^ (2 * r - 1))) +
              ∑ x ∈ Liu, ∑ x' ∈ Liu,
                (if ¬ Disjoint (T' x) (T' x') then (Q : ℝ) ^ S / (Q : ℝ) else 0) := by
            simp_rw [sum_add_distrib]
        _ ≤ μ ^ 2 * ((Q : ℝ) ^ S / (Q : ℝ)) +
              (2 * (r : ℝ) ^ 2 * (L : ℝ) * (N : ℝ) / (Q : ℝ)) * ((Q : ℝ) ^ S) := by
            apply add_le_add
            · simp only [sum_const, nsmul_eq_mul]
              dsimp [μ]
              have hpow : (Q : ℝ) ^ (2 * r - 1) = ((Q : ℝ) ^ (r - 1)) ^ 2 * (Q : ℝ) := by
                rw [← pow_mul, ← pow_succ]
                congr 1; omega
              rw [hpow]
              field_simp
              exact le_rfl
            · have hinner_sum : ∀ x ∈ Liu,
                  (∑ x' ∈ Liu, if ¬ Disjoint (T' x) (T' x') then (Q : ℝ) ^ S / (Q : ℝ) else 0) ≤
                    (2 * (r : ℝ) ^ 2 * (L : ℝ)) * ((Q : ℝ) ^ S / (Q : ℝ)) := by
                intro x hx
                rw [← sum_filter, sum_const, nsmul_eq_mul]
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                have := (Nat.cast_le (α := ℝ)).mpr (hoverlap_le x hx)
                push_cast at this; linarith only [this]
              calc ∑ x ∈ Liu, ∑ x' ∈ Liu,
                    (if ¬ Disjoint (T' x) (T' x') then (Q : ℝ) ^ S / (Q : ℝ) else 0)
                  ≤ ∑ _x ∈ Liu, ((2 * (r : ℝ) ^ 2 * (L : ℝ)) * ((Q : ℝ) ^ S / (Q : ℝ))) :=
                    sum_le_sum hinner_sum
                _ = (Liu.card : ℝ) * ((2 * (r : ℝ) ^ 2 * (L : ℝ)) * ((Q : ℝ) ^ S / (Q : ℝ))) := by
                    rw [sum_const, nsmul_eq_mul]
                _ ≤ (N : ℝ) * ((2 * (r : ℝ) ^ 2 * (L : ℝ)) * ((Q : ℝ) ^ S / (Q : ℝ))) := by
                    refine mul_le_mul_of_nonneg_right (by exact_mod_cast hLiu_le) (by positivity)
                _ = (2 * (r : ℝ) ^ 2 * (L : ℝ) * (N : ℝ) / (Q : ℝ)) * ((Q : ℝ) ^ S) := by ring
    rw [hexpand, hsumZ, hsum1]
    linarith only [hsumZ2]
  have hgap : (ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) ≤ (D : ℝ) - μ := by
    have hμ_le : μ ≤ (N : ℝ) / ((Q : ℝ) ^ (r - 1)) := by
      dsimp [μ]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hLiu_le) (by positivity)
    have h1 : (1 + ε / 4) * (N : ℝ) / (Q : ℝ) ^ (r - 1) - (N : ℝ) / (Q : ℝ) ^ (r - 1) =
        (ε / 4) * (N : ℝ) / (Q : ℝ) ^ (r - 1) := by ring
    linarith only [hD_ge, hμ_le, h1]
  have hgap_pos : 0 < (ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Fact.out : N.Prime).pos
    positivity
  have hpt : ∀ ω : Fin S → Fin Q,
      ((((Valid.filter (fun x ↦ linEval (A i) N x = u ∧
          ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
            keyOf b Q hQ N S L j (linEval (A j) N x))).card - D : ℕ) : ℝ)) ≤
        (if E0 ω then (Z ω - μ) ^ 2 else 0) / ((ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1))) := by
    intro ω
    set d := (Valid.filter (fun x ↦ linEval (A i) N x = u ∧
      ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
        keyOf b Q hQ N S L j (linEval (A j) N x))).card
    by_cases hdD : d ≤ D
    · rw [Nat.sub_eq_zero_of_le hdD, Nat.cast_zero]
      split_ifs <;> positivity
    · push Not at hdD
      have hcast : ((d - D : ℕ) : ℝ) = (d : ℝ) - (D : ℝ) := Nat.cast_sub hdD.le
      rw [hcast]
      have hE0_true : E0 ω := by
        by_contra h0
        have := hdeg_eq ω
        rw [if_neg h0] at this
        have hd0 : (d : ℝ) = 0 := this
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
        linarith only [hd0, hdpos]
      have hdZ : (d : ℝ) = Z ω := by
        have := hdeg_eq ω
        rwa [if_pos hE0_true] at this
      rw [if_pos hE0_true, hdZ, le_div_iff₀ hgap_pos]
      have hZ_gt_D : (D : ℝ) < Z ω := by rw [← hdZ]; exact_mod_cast hdD
      nlinarith only [hgap, hZ_gt_D, hgap_pos]
  calc ∑ ω : Fin S → Fin Q, _
      ≤ ∑ ω : Fin S → Fin Q,
          ((if E0 ω then (Z ω - μ) ^ 2 else 0) / ((ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)))) :=
        sum_le_sum fun ω _ ↦ hpt ω
    _ = (∑ ω : Fin S → Fin Q, if E0 ω then (Z ω - μ) ^ 2 else 0) /
          ((ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1))) := (sum_div _ _ _).symm
    _ ≤ ((2 * (r : ℝ) ^ 2 * (L : ℝ) * (N : ℝ) / (Q : ℝ)) * ((Q : ℝ) ^ S)) /
          ((ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1))) :=
        div_le_div_of_nonneg_right hvar hgap_pos.le
    _ ≤ (8 * (r : ℝ) ^ 2 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε) * ((Q : ℝ) ^ S) := by
        have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Fact.out : N.Prime).pos
        have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
        have heq : ((2 * (r : ℝ) ^ 2 * (L : ℝ) * (N : ℝ) / (Q : ℝ)) * ((Q : ℝ) ^ S)) /
            ((ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1))) =
            (8 * (r : ℝ) ^ 2 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / (ε * (Q : ℝ))) * ((Q : ℝ) ^ S) := by
          field_simp; ring
        rw [heq]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hdiv : ε ≤ ε * (Q : ℝ) := by nlinarith only [hε, hQ1]
        exact div_le_div_of_nonneg_left (by positivity) hε hdiv

/-- Existence of a coloring `ω` with large `|G ω| - Exc ω`. -/
lemma exists_good_coloring {S Q N L : ℕ} [Fact N.Prime] (hS : 0 < S) (hQ : 2 * Lmax b < Q)
    (hL : 0 < L) (hr : 2 ≤ r) (A : Fin r → ℤ × ℤ)
    (hN_det : ∀ i j : Fin r, i ≠ j →
      (((A i).1 * (A j).2 - (A i).2 * (A j).1 : ℤ) : ZMod N) ≠ 0)
    (Valid : Finset (ZMod N × ZMod N))
    (hValid : ∀ x ∈ Valid,
      (∀ i : Fin r, isInterior b N S L (linEval (A i) N x)) ∧
      (∀ i j : Fin r, i ≠ j → slotOf N S L (linEval (A i) N x) ≠ slotOf N S L (linEval (A j) N x)))
    (D : ℕ) (ε : ℝ) (hε_pos : 0 < ε)
    (hValid_card : (1 - ε / 4) * (N : ℝ) ^ 2 ≤ (Valid.card : ℝ))
    (hD_ge : (1 + ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) ≤ (D : ℝ))
    (hN_exc : 20 * (Q : ℝ) ^ r * (8 * (r : ℝ) ^ 3 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε) / ε ≤ (N : ℝ)) :
    ∃ ω : Fin S → Fin Q,
      (1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r ≤
        ((Valid.filter (fun x ↦ ∀ i : Fin r,
            ω (slotFin N S L hS (linEval (A i) N x)) =
              keyOf b Q hQ N S L i (linEval (A i) N x))).card : ℝ) -
        ∑ p : Fin r × ZMod N,
          ((((Valid.filter (fun x ↦ linEval (A p.1) N x = p.2 ∧
              ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
                keyOf b Q hQ N S L j (linEval (A j) N x))).card - D : ℕ) : ℝ)) := by
  have hQ_pos : 0 < Q := by omega
  have hN_pos : 0 < N := (Fact.out : N.Prime).pos
  have hN_R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  set C_exc : ℝ := 8 * (r : ℝ) ^ 3 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε
  let G (ω : Fin S → Fin Q) : Finset (ZMod N × ZMod N) :=
    Valid.filter (fun x ↦ ∀ i : Fin r,
      ω (slotFin N S L hS (linEval (A i) N x)) = keyOf b Q hQ N S L i (linEval (A i) N x))
  let Exc (ω : Fin S → Fin Q) : ℝ :=
    ∑ p : Fin r × ZMod N,
      ((((Valid.filter (fun x ↦ linEval (A p.1) N x = p.2 ∧
          ∀ j : Fin r, ω (slotFin N S L hS (linEval (A j) N x)) =
            keyOf b Q hQ N S L j (linEval (A j) N x))).card - D : ℕ) : ℝ))
  have hG_sum : ∑ ω : Fin S → Fin Q, ((G ω).card : ℝ) = (Valid.card : ℝ) * ((Q : ℝ) ^ S / (Q : ℝ) ^ r) := by
    have hswap : ∑ ω : Fin S → Fin Q, ((G ω).card : ℝ) =
        ∑ x ∈ Valid, ((univ.filter (fun ω : Fin S → Fin Q ↦
          ∀ i : Fin r, ω (slotFin N S L hS (linEval (A i) N x)) =
            keyOf b Q hQ N S L i (linEval (A i) N x))).card : ℝ) := by
      have h1 : ∀ ω : Fin S → Fin Q, ((G ω).card : ℝ) =
          ∑ x ∈ Valid, (if ∀ i : Fin r, ω (slotFin N S L hS (linEval (A i) N x)) =
            keyOf b Q hQ N S L i (linEval (A i) N x) then (1 : ℝ) else 0) := by
        intro ω; simp [G, sum_boole]
      simp_rw [h1]
      rw [sum_comm]
      refine sum_congr rfl fun x _ ↦ ?_
      rw [sum_boole]
    rw [hswap]
    have hterm : ∀ x ∈ Valid,
        ((univ.filter (fun ω : Fin S → Fin Q ↦
          ∀ i : Fin r, ω (slotFin N S L hS (linEval (A i) N x)) =
            keyOf b Q hQ N S L i (linEval (A i) N x))).card : ℝ) =
        (Q : ℝ) ^ S / (Q : ℝ) ^ r := by
      intro x hx
      have hV := hValid x hx
      let T : Finset (Fin S) := univ.image (fun i : Fin r ↦ slotFin N S L hS (linEval (A i) N x))
      let val : Fin S → Fin Q := fun s ↦
        if h : ∃ i : Fin r, slotFin N S L hS (linEval (A i) N x) = s
        then keyOf b Q hQ N S L (Classical.choose h) (linEval (A (Classical.choose h)) N x)
        else ⟨0, hQ_pos⟩
      have hval_at : ∀ i : Fin r,
          val (slotFin N S L hS (linEval (A i) N x)) =
            keyOf b Q hQ N S L i (linEval (A i) N x) := by
        intro i
        have hex : ∃ j : Fin r, slotFin N S L hS (linEval (A j) N x) =
            slotFin N S L hS (linEval (A i) N x) := ⟨i, rfl⟩
        dsimp [val]
        rw [dif_pos hex]
        have hch := Classical.choose_spec hex
        have hieq : Classical.choose hex = i := by
          by_contra hne
          have h1 := congrArg Fin.val hch
          rw [slotFin_val hS hL ((hV.1 _).imp And.left And.left),
              slotFin_val hS hL ((hV.1 i).imp And.left And.left)] at h1
          exact hV.2 _ i hne h1
        rw [hieq]
      have hinj : Set.InjOn (fun i : Fin r ↦ slotFin N S L hS (linEval (A i) N x))
          ((univ : Finset (Fin r)) : Set (Fin r)) := by
        intro i₁ _ i₂ _ heq
        by_contra hne
        have h1 := congrArg Fin.val heq
        rw [slotFin_val hS hL ((hV.1 i₁).imp And.left And.left),
            slotFin_val hS hL ((hV.1 i₂).imp And.left And.left)] at h1
        exact hV.2 i₁ i₂ hne h1
      have hTcard : T.card = r := by
        rw [card_image_of_injOn hinj, card_univ, Fintype.card_fin]
      have hEq : univ.filter (fun ω : Fin S → Fin Q ↦
          ∀ i : Fin r, ω (slotFin N S L hS (linEval (A i) N x)) =
            keyOf b Q hQ N S L i (linEval (A i) N x)) =
          univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ T, ω t = val t) := by
        ext ω
        simp only [mem_filter, mem_univ, true_and, T, mem_image]
        constructor
        · rintro hall t ⟨i, rfl⟩; rw [hval_at i]; exact hall i
        · intro hall i; have := hall (slotFin N S L hS (linEval (A i) N x)) ⟨i, rfl⟩; rwa [hval_at i] at this
      rw [hEq]
      have hcnt : ((univ.filter (fun ω : Fin S → Fin Q ↦ ∀ t ∈ T, ω t = val t)).card : ℝ) * (Q : ℝ) ^ r =
          (Q : ℝ) ^ S := by
        have := card_filter_eq_on T val
        rw [hTcard] at this
        exact_mod_cast this
      rw [← hcnt]
      field_simp
    rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
  have hExc_sum : ∑ ω : Fin S → Fin Q, Exc ω ≤ C_exc * (N : ℝ) * ((Q : ℝ) ^ S) := by
    dsimp [Exc]
    rw [sum_comm]
    calc ∑ p : Fin r × ZMod N, ∑ ω : Fin S → Fin Q, _
        ≤ ∑ _p : Fin r × ZMod N, ((8 * (r : ℝ) ^ 2 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε) * ((Q : ℝ) ^ S)) :=
          sum_le_sum fun p _ ↦
            vertex_excess_sum_le b hS hQ hL hr A hN_det Valid hValid p.1 p.2 D ε hε_pos hD_ge
      _ = ((r * N : ℕ) : ℝ) * ((8 * (r : ℝ) ^ 2 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε) * ((Q : ℝ) ^ S)) := by
          rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, ZMod.card, nsmul_eq_mul]
      _ = C_exc * (N : ℝ) * ((Q : ℝ) ^ S) := by
          dsimp [C_exc]; push_cast; ring
  by_contra hall
  push Not at hall
  have hlt_sum : ∑ ω : Fin S → Fin Q, (((G ω).card : ℝ) - Exc ω) <
      ∑ _ω : Fin S → Fin Q, ((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) :=
    sum_lt_sum_of_nonempty (univ_nonempty_iff.mpr ⟨fun _ ↦ ⟨0, hQ_pos⟩⟩) (fun ω _ ↦ hall ω)
  rw [sum_sub_distrib, hG_sum, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul] at hlt_sum
  have hQS : (0 : ℝ) < (Q : ℝ) ^ S := by positivity
  have hQr : (0 : ℝ) < (Q : ℝ) ^ r := by positivity
  have hG_lo : (1 - ε / 4) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r * (Q : ℝ) ^ S ≤
      (Valid.card : ℝ) * ((Q : ℝ) ^ S / (Q : ℝ) ^ r) := by
    have h1 := mul_le_mul_of_nonneg_right hValid_card (show 0 ≤ (Q : ℝ) ^ S / (Q : ℝ) ^ r by positivity)
    have h2 : (1 - ε / 4) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r * (Q : ℝ) ^ S =
        (1 - ε / 4) * (N : ℝ) ^ 2 * ((Q : ℝ) ^ S / (Q : ℝ) ^ r) := by ring
    linarith only [h1, h2]
  have hExc_hi : C_exc * (N : ℝ) ≤ (ε / 4) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r := by
    have hmul : 20 * (Q : ℝ) ^ r * C_exc ≤ (N : ℝ) * ε := (div_le_iff₀ hε_pos).mp hN_exc
    rw [le_div_iff₀ hQr]
    have hCnn : 0 ≤ C_exc := by dsimp [C_exc]; positivity
    have h1 : 20 * C_exc * (N : ℝ) * (Q : ℝ) ^ r ≤ ε * (N : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hmul hN_R.le
      linarith only [this]
    nlinarith only [h1, hN_R, hQr, hCnn, hε_pos]
  have hExc_hi' : C_exc * (N : ℝ) * (Q : ℝ) ^ S ≤
      (ε / 4) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r * (Q : ℝ) ^ S :=
    mul_le_mul_of_nonneg_right hExc_hi hQS.le
  have hcast_QS : ((Q ^ S : ℕ) : ℝ) = (Q : ℝ) ^ S := by push_cast; rfl
  rw [hcast_QS] at hlt_sum
  have halg : (1 - ε / 4) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r * (Q : ℝ) ^ S -
      (ε / 4) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r * (Q : ℝ) ^ S =
      (Q : ℝ) ^ S * ((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) := by ring
  linarith only [hlt_sum, hG_lo, hExc_sum, hExc_hi', halg]

/- Main existence theorem: given the Rodl nibble matching theorem as an input,
we prove `OMA.R_Green84_green_84_variants_littlewood_R1.H2`. -/
set_option maxHeartbeats 800000 in
theorem h2_from_nibble
    (hnibble : ∀ (r : ℕ), 2 ≤ r → ∀ (γ : ℝ), 0 < γ →
      ∃ β : ℝ, 0 < β ∧ ∃ D₀ : ℕ, 1 ≤ D₀ ∧
        ∀ {α : Type} [DecidableEq α] (U : Finset α) (ℰ : Finset (Finset α)) (D : ℕ),
          D₀ ≤ D →
          (∀ e ∈ ℰ, e ⊆ U ∧ e.card = r) →
          (∀ x ∈ U, (ℰ.filter (fun e ↦ x ∈ e)).card ≤ D) →
          (∀ x ∈ U, ∀ y ∈ U, x ≠ y →
            ((ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card : ℝ) ≤ β * (D : ℝ)) →
          ∃ ℳ : Finset (Finset α), ℳ ⊆ ℰ ∧
            (∀ e₁ ∈ ℳ, ∀ e₂ ∈ ℳ, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
            (1 - γ) * ((ℰ.card : ℝ) / (D : ℝ)) ≤ (ℳ.card : ℝ)) :
    OMA.R_Green84_green_84_variants_littlewood_R1.H2 := by
  intro r m hr a ha0 hnp w hw_pos hw_sum
  obtain ⟨uvec, vvec, A, hA_eq, _, hAdet⟩ := reduce_dim_two r m a ha0 hnp
  set W : ℝ := 2 * ∑ i : Fin r, w i
  have hW_pos : 0 < W := by
    have hsum_pos : 0 < ∑ i : Fin r, w i :=
      sum_pos (fun i _ ↦ hw_pos i) ⟨⟨0, by omega⟩, mem_univ _⟩
    dsimp [W]; linarith only [hsum_pos]
  have hW_lt : W < 1 := hw_sum
  set ε : ℝ := (1 - W) / 20
  have hε_pos : 0 < ε := by dsimp [ε]; linarith only [hW_lt]
  have hε_small : ε ≤ 1 / 20 := by dsimp [ε]; linarith only [hW_pos]
  have hw_min_ex : ∃ wmin : ℝ, 0 < wmin ∧ ∀ i : Fin r, wmin ≤ w i := by
    have hne : (univ : Finset (Fin r)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
    let Simg := univ.image w
    have hSne : Simg.Nonempty := hne.image w
    refine ⟨Simg.min' hSne, ?_, fun i ↦ min'_le Simg (w i) (mem_image_of_mem w (mem_univ i))⟩
    obtain ⟨i, _, hi⟩ := mem_image.mp (min'_mem Simg hSne)
    rw [← hi]; exact hw_pos i
  obtain ⟨wmin, hwmin_pos, hwmin_le⟩ := hw_min_ex
  let Q : ℕ := max 10 (Nat.ceil (4 / (ε * wmin)))
  have hQ_pos : 0 < Q := by dsimp [Q]; omega
  have hQ_R : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ_pos
  have hQ_bound : ∀ i : Fin r, 4 ≤ ε * (Q : ℝ) * w i := by
    intro i
    have h1 : 4 / (ε * wmin) ≤ (Q : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 10 _)
    have h2 : 4 ≤ (Q : ℝ) * (ε * wmin) := (div_le_iff₀ (mul_pos hε_pos hwmin_pos)).mp h1
    have h3 : (Q : ℝ) * (ε * wmin) ≤ ε * (Q : ℝ) * w i := by
      have := mul_le_mul_of_nonneg_left (hwmin_le i) (mul_nonneg hε_pos.le hQ_R.le)
      linarith only [this]
    linarith only [h2, h3]
  let b : Fin r → ℕ := fun i ↦ Nat.floor ((Q : ℝ) * (1 + 2 * ε) * w i / 2) + 1
  have hell_lo : ∀ i : Fin r, (1 + 2 * ε) * (Q : ℝ) * w i < (ell b i : ℝ) := by
    intro i
    dsimp [ell, b]
    have hlt := Nat.lt_floor_add_one ((Q : ℝ) * (1 + 2 * ε) * w i / 2)
    push_cast
    linarith only [hlt]
  have hell_hi : ∀ i : Fin r, (ell b i : ℝ) < (1 + 3 * ε) * (Q : ℝ) * w i := by
    intro i
    dsimp [ell, b]
    have hnn : 0 ≤ (Q : ℝ) * (1 + 2 * ε) * w i / 2 := by
      have := hw_pos i; positivity
    have hle := Nat.floor_le hnn
    have h4 := hQ_bound i
    push_cast
    linarith only [hle, h4]
  have h2Lmax_lt_Q : 2 * Lmax b < Q := by
    have hsumR : (2 * Lmax b : ℝ) < (Q : ℝ) := by
      dsimp [Lmax]
      push_cast
      have h1 : 2 * ∑ i : Fin r, (ell b i : ℝ) < 2 * ∑ i : Fin r, ((1 + 3 * ε) * (Q : ℝ) * w i) := by
        have hlt : ∑ i : Fin r, (ell b i : ℝ) < ∑ i : Fin r, ((1 + 3 * ε) * (Q : ℝ) * w i) :=
          sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, mem_univ _⟩ (fun i _ ↦ hell_hi i)
        linarith only [hlt]
      have h2 : 2 * ∑ i : Fin r, ((1 + 3 * ε) * (Q : ℝ) * w i) = (1 + 3 * ε) * W * (Q : ℝ) := by
        rw [← mul_sum]
        dsimp [W]; ring
      have h3 : (1 + 3 * ε) * W < 1 := by
        have hε_eq : ε = (1 - W) / 20 := rfl
        nlinarith only [hε_eq, hW_pos, hW_lt]
      nlinarith only [h1, h2, h3, hQ_R]
    exact_mod_cast hsumR
  have hLmax_pos : 0 < Lmax b := by
    have := ell_le_Lmax b ⟨0, by omega⟩
    have := ell_pos b ⟨0, by omega⟩
    omega
  let L : ℕ := (Nat.ceil (40 * (r : ℝ) / ε) + 5) * Lmax b
  have hL_gt : 4 * Lmax b < L := by dsimp [L]; nlinarith only [hLmax_pos]
  have hL_pos : 0 < L := by omega
  have hL_frac : 8 * (r : ℝ) * (Lmax b : ℝ) / (L : ℝ) ≤ ε / 5 := by
    have hL_ge : (40 * (r : ℝ) / ε) * (Lmax b : ℝ) ≤ (L : ℝ) := by
      dsimp [L]; push_cast
      have h1 : 40 * (r : ℝ) / ε ≤ (Nat.ceil (40 * (r : ℝ) / ε) : ℝ) := Nat.le_ceil _
      have h2 : (0 : ℝ) ≤ (Lmax b : ℝ) := Nat.cast_nonneg _
      nlinarith only [h1, h2]
    have hL_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos
    rw [div_le_iff₀ hL_R]
    have h3 : 8 * (r : ℝ) * (Lmax b : ℝ) = (ε / 5) * ((40 * (r : ℝ) / ε) * (Lmax b : ℝ)) := by
      field_simp; ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left hL_ge (by positivity)
  obtain ⟨β, hβ_pos, D₀, hD₀_pos, hnibble_spec⟩ := hnibble r hr (ε / 4) (by positivity)
  let detMax : ℕ := ∑ i : Fin r, ∑ j : Fin r, ((A i).1 * (A j).2 - (A i).2 * (A j).1).natAbs
  let C_bad : ℝ := (r : ℝ) * (2 * (L : ℝ) + 1) + (r : ℝ) ^ 2 * (2 * (L : ℝ))
  let C_exc : ℝ := 8 * (r : ℝ) ^ 3 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε
  let N_bound : ℕ := max (max (detMax + 4 * L + 10) (Q ^ r * (D₀ + 10)))
    (max (Nat.ceil ((Q : ℝ) ^ r / β) + 10)
      (max (Nat.ceil (20 * C_bad / ε) + 10)
        (max (Nat.ceil (20 * (Q : ℝ) ^ r * C_exc / ε) + 10)
          (max (Nat.ceil (20 * (Q : ℝ) ^ r / ε) + 10)
            (Nat.ceil (4 * (Q : ℝ)) + 10)))))
  obtain ⟨N, hN_ge, hN_prime⟩ := Nat.exists_infinite_primes N_bound
  have : Fact N.Prime := ⟨hN_prime⟩
  have hN_pos : 0 < N := hN_prime.pos
  have hN_R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_det_le : detMax + 4 * L + 10 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN_ge
  have hN_D0_le : Q ^ r * (D₀ + 10) ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN_ge
  have hN_beta_le : Nat.ceil ((Q : ℝ) ^ r / β) + 10 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN_ge
  have hN_bad_le : Nat.ceil (20 * C_bad / ε) + 10 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN_ge
  have hN_exc_le : Nat.ceil (20 * (Q : ℝ) ^ r * C_exc / ε) + 10 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN_ge
  have hN_small_le : Nat.ceil (20 * (Q : ℝ) ^ r / ε) + 10 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))) hN_ge
  have hN_4Q_le : Nat.ceil (4 * (Q : ℝ)) + 10 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))) hN_ge
  have hN_det : ∀ i j : Fin r, i ≠ j →
      (((A i).1 * (A j).2 - (A i).2 * (A j).1 : ℤ) : ZMod N) ≠ 0 := by
    intro i j hij h0
    have hdvd : (N : ℤ) ∣ (A i).1 * (A j).2 - (A i).2 * (A j).1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have hne := hAdet i j hij
    have hle1 : ((A i).1 * (A j).2 - (A i).2 * (A j).1).natAbs ≤ detMax := by
      dsimp [detMax]
      exact (single_le_sum (f := fun j' ↦ ((A i).1 * (A j').2 - (A i).2 * (A j').1).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ j)).trans
        (single_le_sum (f := fun i' ↦ ∑ j' : Fin r, ((A i').1 * (A j').2 - (A i').2 * (A j').1).natAbs)
          (fun _ _ ↦ Nat.zero_le _) (mem_univ i))
    have hle2 : N ≤ ((A i).1 * (A j).2 - (A i).2 * (A j).1).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp hdvd)
    omega
  let S : ℕ := (N - 1) / (2 * L)
  have hS_pos : 0 < S := Nat.div_pos (by omega) (by omega)
  have h2SL : 2 * S * L < N := by
    have h1 : S * (2 * L) ≤ N - 1 := Nat.div_mul_le_self (N - 1) (2 * L)
    have h2 : 2 * S * L = S * (2 * L) := by ring
    omega
  have hSN : N ≤ 2 * S * L + 2 * L + 1 := by
    have h1 : N - 1 < S * (2 * L) + 2 * L := Nat.lt_div_mul_add (a := N - 1) (by omega : 0 < 2 * L)
    have h2 : 2 * S * L = S * (2 * L) := by ring
    omega
  let Valid : Finset (ZMod N × ZMod N) := univ.filter fun x ↦
    (∀ i : Fin r, isInterior b N S L (linEval (A i) N x)) ∧
    (∀ i j : Fin r, i ≠ j → slotOf N S L (linEval (A i) N x) ≠ slotOf N S L (linEval (A j) N x))
  have hValid_spec : ∀ x ∈ Valid,
      (∀ i : Fin r, isInterior b N S L (linEval (A i) N x)) ∧
      (∀ i j : Fin r, i ≠ j → slotOf N S L (linEval (A i) N x) ≠ slotOf N S L (linEval (A j) N x)) :=
    fun x hx ↦ (mem_filter.mp hx).2
  have hN_bad_R : 20 * ((r : ℝ) * (2 * (L : ℝ) + 1) + (r : ℝ) ^ 2 * (2 * (L : ℝ))) / ε ≤ (N : ℝ) := by
    have h1 : Nat.ceil (20 * C_bad / ε) ≤ N := by omega
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr h1)
  have hValid_card : (1 - ε / 4) * (N : ℝ) ^ 2 ≤ (Valid.card : ℝ) :=
    valid_card_ge b hr A hN_det h2SL hL_gt hSN ε hε_pos hL_frac hN_bad_R
  let D : ℕ := Nat.ceil ((1 + ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)))
  have hD_ge_expr : (1 + ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) ≤ (D : ℝ) := Nat.le_ceil _
  have hQpow : (Q : ℝ) ^ (r - 1) ≤ (Q : ℝ) ^ r :=
    pow_le_pow_right₀ (by exact_mod_cast hQ_pos) (Nat.sub_le r 1)
  have hD_le_expr : (D : ℝ) ≤ (1 + ε / 3) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) := by
    have h1 : (D : ℝ) < (1 + ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hN_big : 20 * (Q : ℝ) ^ r / ε ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
    have h2 : 1 ≤ (ε / 12) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) := by
      rw [le_div_iff₀ (by positivity)]
      have hmul : 20 * (Q : ℝ) ^ r ≤ (N : ℝ) * ε := (div_le_iff₀ hε_pos).mp hN_big
      have hQ1 : (0 : ℝ) < (Q : ℝ) ^ (r - 1) := by positivity
      nlinarith only [hmul, hQpow, hQ1]
    have h3 : (1 + ε / 4) * (N : ℝ) / (Q : ℝ) ^ (r - 1) + (ε / 12) * (N : ℝ) / (Q : ℝ) ^ (r - 1) =
        (1 + ε / 3) * (N : ℝ) / (Q : ℝ) ^ (r - 1) := by ring
    linarith only [h1, h2, h3]
  have hN_exc_R : 20 * (Q : ℝ) ^ r * (8 * (r : ℝ) ^ 3 * (L : ℝ) * (Q : ℝ) ^ (r - 1) / ε) / ε ≤ (N : ℝ) := by
    have h1 : Nat.ceil (20 * (Q : ℝ) ^ r * C_exc / ε) ≤ N := by omega
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr h1)
  obtain ⟨ω, hω_good⟩ := exists_good_coloring b hS_pos h2Lmax_lt_Q hL_pos hr A hN_det Valid hValid_spec
    D ε hε_pos hValid_card hD_ge_expr hN_exc_R
  let G : Finset (ZMod N × ZMod N) :=
    Valid.filter (fun x ↦ ∀ i : Fin r,
      ω (slotFin N S L hS_pos (linEval (A i) N x)) = keyOf b Q h2Lmax_lt_Q N S L i (linEval (A i) N x))
  let U : Finset (Fin r × ZMod N) := univ
  let edgeOf (x : ZMod N × ZMod N) : Finset (Fin r × ZMod N) :=
    univ.image (fun i : Fin r ↦ (i, linEval (A i) N x))
  have hedge_card : ∀ x, (edgeOf x).card = r := by
    intro x
    rw [card_image_of_injective _ (fun i₁ i₂ h ↦ (Prod.mk.inj h).1), card_univ, Fintype.card_fin]
  have hedge_inj : Function.Injective edgeOf := by
    intro x₁ x₂ heq
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := fun h ↦ by have h' := congrArg Fin.val h; dsimp [i0, i1] at h'; omega
    have hm0 : (i0, linEval (A i0) N x₁) ∈ edgeOf x₂ :=
      heq ▸ mem_image_of_mem _ (mem_univ i0)
    have hm1 : (i1, linEval (A i1) N x₁) ∈ edgeOf x₂ :=
      heq ▸ mem_image_of_mem _ (mem_univ i1)
    obtain ⟨j0, _, hj0⟩ := mem_image.mp hm0
    obtain ⟨j1, _, hj1⟩ := mem_image.mp hm1
    have h0eq : j0 = i0 := (Prod.mk.inj hj0).1
    have h1eq : j1 = i1 := (Prod.mk.inj hj1).1
    subst h0eq h1eq
    have hev0 : linEval (A i0) N x₂ = linEval (A i0) N x₁ := (Prod.mk.inj hj0).2
    have hev1 : linEval (A i1) N x₂ = linEval (A i1) N x₁ := (Prod.mk.inj hj1).2
    let eqv := evalPairEquiv (A i0) (A i1) (hN_det i0 i1 hi01)
    apply eqv.injective
    ext
    · exact hev0.symm
    · exact hev1.symm
  let ℰ₀ : Finset (Finset (Fin r × ZMod N)) := G.image edgeOf
  have hℰ₀_card : ℰ₀.card = G.card := card_image_of_injective _ hedge_inj
  have hℰ₀_deg : ∀ p : Fin r × ZMod N,
      (ℰ₀.filter (fun E ↦ p ∈ E)).card =
        (Valid.filter (fun x ↦ linEval (A p.1) N x = p.2 ∧
          ∀ j : Fin r, ω (slotFin N S L hS_pos (linEval (A j) N x)) =
            keyOf b Q h2Lmax_lt_Q N S L j (linEval (A j) N x))).card := by
    intro p
    have hEq : ℰ₀.filter (fun E ↦ p ∈ E) =
        (Valid.filter (fun x ↦ linEval (A p.1) N x = p.2 ∧
          ∀ j : Fin r, ω (slotFin N S L hS_pos (linEval (A j) N x)) =
            keyOf b Q h2Lmax_lt_Q N S L j (linEval (A j) N x))).image edgeOf := by
      ext E
      simp only [ℰ₀, G, mem_filter, mem_image]
      constructor
      · rintro ⟨⟨x, ⟨hxV, hxω⟩, rfl⟩, hpE⟩
        obtain ⟨j, _, hj⟩ := mem_image.mp hpE
        have h1 : j = p.1 := (Prod.mk.inj hj).1
        have h2 : linEval (A j) N x = p.2 := (Prod.mk.inj hj).2
        subst h1
        exact ⟨x, ⟨hxV, h2, hxω⟩, rfl⟩
      · rintro ⟨x, ⟨hxV, hxp, hxω⟩, rfl⟩
        exact ⟨⟨x, ⟨hxV, hxω⟩, rfl⟩, mem_image.mpr ⟨p.1, mem_univ p.1, Prod.ext rfl hxp⟩⟩
    rw [hEq, card_image_of_injective _ hedge_inj]
  obtain ⟨ℰ, hℰ_sub, hℰ_deg, hℰ_card_nat⟩ := trim_hypergraph U D ℰ₀
  have hℰ_card : (1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r ≤ (ℰ.card : ℝ) := by
    have hnat := (Nat.cast_le (α := ℝ)).mpr hℰ_card_nat
    push_cast at hnat
    have hExc_eq : ∑ p ∈ U, (((ℰ₀.filter (fun E ↦ p ∈ E)).card - D : ℕ) : ℝ) =
        ∑ p : Fin r × ZMod N,
          ((((Valid.filter (fun x ↦ linEval (A p.1) N x = p.2 ∧
              ∀ j : Fin r, ω (slotFin N S L hS_pos (linEval (A j) N x)) =
                keyOf b Q h2Lmax_lt_Q N S L j (linEval (A j) N x))).card - D : ℕ) : ℝ)) := by
      dsimp [U]
      refine sum_congr rfl fun p _ ↦ ?_
      rw [hℰ₀_deg p]
    rw [hExc_eq, hℰ₀_card] at hnat
    linarith only [hnat, hω_good]
  have hℰ_codeg_nat : ∀ p₁ ∈ U, ∀ p₂ ∈ U, p₁ ≠ p₂ →
      (ℰ.filter (fun E ↦ p₁ ∈ E ∧ p₂ ∈ E)).card ≤ 1 := by
    intro p₁ _ p₂ _ hp12
    refine card_le_one.mpr fun E₁ hE₁ E₂ hE₂ ↦ ?_
    obtain ⟨hE₁ℰ, hp1E1, hp2E1⟩ := mem_filter.mp hE₁
    obtain ⟨hE₂ℰ, hp1E2, hp2E2⟩ := mem_filter.mp hE₂
    obtain ⟨x₁, _, rfl⟩ := mem_image.mp (hℰ_sub hE₁ℰ)
    obtain ⟨x₂, _, rfl⟩ := mem_image.mp (hℰ_sub hE₂ℰ)
    obtain ⟨j1, _, hj1⟩ := mem_image.mp hp1E1
    obtain ⟨j2, _, hj2⟩ := mem_image.mp hp2E1
    obtain ⟨k1, _, hk1⟩ := mem_image.mp hp1E2
    obtain ⟨k2, _, hk2⟩ := mem_image.mp hp2E2
    have h1 : j1 = p₁.1 := (Prod.mk.inj hj1).1
    have h2 : j2 = p₂.1 := (Prod.mk.inj hj2).1
    have h3 : k1 = p₁.1 := (Prod.mk.inj hk1).1
    have h4 : k2 = p₂.1 := (Prod.mk.inj hk2).1
    have he1 : linEval (A p₁.1) N x₁ = p₁.2 := by rw [← h1]; exact (Prod.mk.inj hj1).2
    have he2 : linEval (A p₂.1) N x₁ = p₂.2 := by rw [← h2]; exact (Prod.mk.inj hj2).2
    have hf1 : linEval (A p₁.1) N x₂ = p₁.2 := by rw [← h3]; exact (Prod.mk.inj hk1).2
    have hf2 : linEval (A p₂.1) N x₂ = p₂.2 := by rw [← h4]; exact (Prod.mk.inj hk2).2
    have hj12 : p₁.1 ≠ p₂.1 := by
      intro heq
      apply hp12
      exact Prod.ext heq (by rw [← he1, ← he2, heq])
    let eqv := evalPairEquiv (A p₁.1) (A p₂.1) (hN_det p₁.1 p₂.1 hj12)
    have hx12 : x₁ = x₂ := by
      apply eqv.injective
      ext
      · change linEval (A p₁.1) N x₁ = linEval (A p₁.1) N x₂; rw [he1, hf1]
      · change linEval (A p₂.1) N x₁ = linEval (A p₂.1) N x₂; rw [he2, hf2]
    rw [hx12]
  have hD_ge_D0 : D₀ ≤ D := by
    have h1 : (D₀ : ℝ) ≤ (D : ℝ) := by
      have hND : (Q : ℝ) ^ r * ((D₀ : ℝ) + 10) ≤ (N : ℝ) := by
        have := (Nat.cast_le (α := ℝ)).mpr hN_D0_le
        push_cast at this; linarith only [this]
      have hQr_pos : (0 : ℝ) < (Q : ℝ) ^ r := by positivity
      have hND' : (D₀ : ℝ) ≤ (N : ℝ) / ((Q : ℝ) ^ (r - 1)) := by
        rw [le_div_iff₀ (by positivity)]
        have hmul : (D₀ : ℝ) * (Q : ℝ) ^ (r - 1) ≤ (D₀ : ℝ) * (Q : ℝ) ^ r :=
          mul_le_mul_of_nonneg_left hQpow (Nat.cast_nonneg _)
        nlinarith only [hND, hmul, hQr_pos]
      have hND'' : (N : ℝ) / ((Q : ℝ) ^ (r - 1)) ≤ (1 + ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith only [hε_pos, hN_R]
      linarith only [hND', hND'', hD_ge_expr]
    exact_mod_cast h1
  have hℰ_codeg : ∀ p₁ ∈ U, ∀ p₂ ∈ U, p₁ ≠ p₂ →
      ((ℰ.filter (fun E ↦ p₁ ∈ E ∧ p₂ ∈ E)).card : ℝ) ≤ β * (D : ℝ) := by
    intro p₁ hp₁ p₂ hp₂ hp12
    have h1 : ((ℰ.filter (fun E ↦ p₁ ∈ E ∧ p₂ ∈ E)).card : ℝ) ≤ 1 := by
      exact_mod_cast hℰ_codeg_nat p₁ hp₁ p₂ hp₂ hp12
    have h2 : 1 ≤ β * (D : ℝ) := by
      have hNb : (Q : ℝ) ^ r / β ≤ (N : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil ((Q : ℝ) ^ r / β) ≤ N by omega))
      have hmul : (Q : ℝ) ^ r ≤ (N : ℝ) * β := (div_le_iff₀ hβ_pos).mp hNb
      have h3 : 1 ≤ β * ((N : ℝ) / ((Q : ℝ) ^ (r - 1))) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        linarith only [hmul, hQpow]
      have h4 : (N : ℝ) / ((Q : ℝ) ^ (r - 1)) ≤ (D : ℝ) := by
        have h4a : (N : ℝ) / ((Q : ℝ) ^ (r - 1)) ≤ (1 + ε / 4) * (N : ℝ) / ((Q : ℝ) ^ (r - 1)) := by
          apply div_le_div_of_nonneg_right _ (by positivity); nlinarith only [hε_pos, hN_R]
        linarith only [h4a, hD_ge_expr]
      have h5 := mul_le_mul_of_nonneg_left h4 hβ_pos.le
      linarith only [h3, h5]
    linarith only [h1, h2]
  have hℰ_unif : ∀ E ∈ ℰ, E ⊆ U ∧ E.card = r := by
    intro E hE
    obtain ⟨x, _, rfl⟩ := mem_image.mp (hℰ_sub hE)
    exact ⟨subset_univ _, hedge_card x⟩
  obtain ⟨ℳ, hℳ_sub, hℳ_disj, hℳ_card⟩ :=
    @hnibble_spec (Fin r × ZMod N) _ U ℰ D hD_ge_D0 hℰ_unif hℰ_deg hℰ_codeg
  let H : ℕ := ℳ.card
  have hH_lo : (N : ℝ) / ((1 + 2 * ε) * (Q : ℝ)) < (H : ℝ) := by
    have hD_pos : (0 : ℝ) < (D : ℝ) := by
      have : 1 ≤ D := le_trans hD₀_pos hD_ge_D0
      exact_mod_cast (show 0 < D by omega)
    have hfrac1 : ((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) /
        ((1 + ε / 3) * (N : ℝ) / (Q : ℝ) ^ (r - 1)) ≤ (ℰ.card : ℝ) / (D : ℝ) := by
      have h1 : ((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) / (D : ℝ) ≤ (ℰ.card : ℝ) / (D : ℝ) :=
        div_le_div_of_nonneg_right hℰ_card hD_pos.le
      have h2 : ((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) /
          ((1 + ε / 3) * (N : ℝ) / (Q : ℝ) ^ (r - 1)) ≤
          ((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) / (D : ℝ) :=
        div_le_div_of_nonneg_left
          (div_nonneg (mul_nonneg (by linarith only [hε_small]) (sq_nonneg _))
            (pow_nonneg (Nat.cast_nonneg _) _))
          hD_pos hD_le_expr
      exact h2.trans h1
    have hpow_r : (Q : ℝ) ^ r = (Q : ℝ) ^ (r - 1) * (Q : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hsimp : (1 - ε / 4) * (((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) /
        ((1 + ε / 3) * (N : ℝ) / (Q : ℝ) ^ (r - 1))) =
        ((1 - ε / 4) * (1 - ε / 2) / (1 + ε / 3)) * ((N : ℝ) / (Q : ℝ)) := by
      rw [hpow_r]; field_simp
    have hcoeff : 1 / (1 + 2 * ε) < (1 - ε / 4) * (1 - ε / 2) / (1 + ε / 3) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hsq : ε ^ 2 ≤ ε / 20 := by nlinarith only [hε_pos, hε_small]
      have hcube : 0 ≤ ε ^ 3 := by positivity
      have hpoly : (1 - ε / 4) * (1 - ε / 2) * (1 + 2 * ε) - 1 * (1 + ε / 3) =
          (11 / 12) * ε - (11 / 8) * ε ^ 2 + (1 / 4) * ε ^ 3 := by ring
      linarith only [hpoly, hsq, hcube, hε_pos]
    have hstep1 : (1 - ε / 4) * (((1 - ε / 2) * (N : ℝ) ^ 2 / (Q : ℝ) ^ r) /
        ((1 + ε / 3) * (N : ℝ) / (Q : ℝ) ^ (r - 1))) ≤ (H : ℝ) :=
      (mul_le_mul_of_nonneg_left hfrac1 (by linarith only [hε_small])).trans hℳ_card
    have hstep2 : (N : ℝ) / ((1 + 2 * ε) * (Q : ℝ)) =
        (1 / (1 + 2 * ε)) * ((N : ℝ) / (Q : ℝ)) := by field_simp
    rw [hstep2]
    have hstep3 : (1 / (1 + 2 * ε)) * ((N : ℝ) / (Q : ℝ)) <
        ((1 - ε / 4) * (1 - ε / 2) / (1 + ε / 3)) * ((N : ℝ) / (Q : ℝ)) :=
      mul_lt_mul_of_pos_right hcoeff (by positivity)
    linarith only [hsimp, hstep1, hstep3]
  have hH_pos : 1 ≤ H := by
    have h1 : (1 : ℝ) < (H : ℝ) := by
      have hN4Q : 4 * (Q : ℝ) ≤ (N : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (4 * (Q : ℝ)) ≤ N by omega))
      have h2 : (1 : ℝ) ≤ (N : ℝ) / ((1 + 2 * ε) * (Q : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith only [hN4Q, hε_small, hQ_R]
      linarith only [h2, hH_lo]
    have h0 : 0 < H := by exact_mod_cast (show (0 : ℝ) < (H : ℝ) by linarith only [h1])
    omega
  let enumℳ : Fin H ≃ ℳ := ℳ.equivFin.symm
  have hx_ex : ∀ h : Fin H, ∃ x ∈ G, edgeOf x = (enumℳ h).1 := by
    intro h
    exact mem_image.mp (hℰ_sub (hℳ_sub (enumℳ h).2))
  let xvec : Fin H → ZMod N × ZMod N := fun h ↦ Classical.choose (hx_ex h)
  have hxvec_mem : ∀ h : Fin H, xvec h ∈ G := fun h ↦ (Classical.choose_spec (hx_ex h)).1
  have hxvec_edge : ∀ h : Fin H, edgeOf (xvec h) = (enumℳ h).1 :=
    fun h ↦ (Classical.choose_spec (hx_ex h)).2
  let θ : Fin H → Fin m → ℝ := fun h k ↦
    ((xvec h).1.val : ℝ) / (N : ℝ) * (uvec k : ℝ) + ((xvec h).2.val : ℝ) / (N : ℝ) * (vvec k : ℝ)
  refine ⟨H, hH_pos, θ, ?_⟩
  intro e₁ e₂ i j h s hne q
  let z₁ : ℤ := (if e₁ then (1 : ℤ) else -1) *
    ((A i).1 * ((xvec h).1.val : ℤ) + (A i).2 * ((xvec h).2.val : ℤ))
  let z₂ : ℤ := (if e₂ then (1 : ℤ) else -1) *
    ((A j).1 * ((xvec s).1.val : ℤ) + (A j).2 * ((xvec s).2.val : ℤ))
  have hsum_eval : ∀ (i' : Fin r) (h' : Fin H),
      ∑ k : Fin m, (a i' k : ℝ) * θ h' k =
        (((A i').1 * ((xvec h').1.val : ℤ) + (A i').2 * ((xvec h').2.val : ℤ) : ℤ) : ℝ) / (N : ℝ) := by
    intro i' h'
    dsimp [θ]
    have hA1 : ((A i').1 : ℝ) = ∑ k : Fin m, (a i' k : ℝ) * (uvec k : ℝ) := by
      have := congrArg (Int.cast (R := ℝ)) (hA_eq i').1
      simpa using this
    have hA2 : ((A i').2 : ℝ) = ∑ k : Fin m, (a i' k : ℝ) * (vvec k : ℝ) := by
      have := congrArg (Int.cast (R := ℝ)) (hA_eq i').2
      simpa using this
    calc ∑ k : Fin m, (a i' k : ℝ) *
            (((xvec h').1.val : ℝ) / (N : ℝ) * (uvec k : ℝ) +
             ((xvec h').2.val : ℝ) / (N : ℝ) * (vvec k : ℝ))
        = (∑ k : Fin m, ((a i' k : ℝ) * (uvec k : ℝ)) * (((xvec h').1.val : ℝ) / (N : ℝ))) +
          (∑ k : Fin m, ((a i' k : ℝ) * (vvec k : ℝ)) * (((xvec h').2.val : ℝ) / (N : ℝ))) := by
            rw [← sum_add_distrib]
            refine sum_congr rfl fun k _ ↦ by ring
      _ = ((∑ k : Fin m, (a i' k : ℝ) * (uvec k : ℝ)) * (((xvec h').1.val : ℝ) / (N : ℝ))) +
          ((∑ k : Fin m, (a i' k : ℝ) * (vvec k : ℝ)) * (((xvec h').2.val : ℝ) / (N : ℝ))) := by
            rw [← sum_mul, ← sum_mul]
      _ = (((A i').1 * ((xvec h').1.val : ℤ) + (A i').2 * ((xvec h').2.val : ℤ) : ℤ) : ℝ) / (N : ℝ) := by
            rw [← hA1, ← hA2]; push_cast; ring
  have hRHS_eq :
      (if e₁ then (1 : ℝ) else -1) * (∑ k : Fin m, (a i k : ℝ) * θ h k) -
      (if e₂ then (1 : ℝ) else -1) * (∑ k : Fin m, (a j k : ℝ) * θ s k) - (q : ℝ) =
      (z₁ : ℝ) / (N : ℝ) - (z₂ : ℝ) / (N : ℝ) - (q : ℝ) := by
    rw [hsum_eval i h, hsum_eval j s]
    dsimp [z₁, z₂]
    cases e₁ <;> cases e₂ <;> simp <;> ring
  rw [hRHS_eq]
  set u₁ : ZMod N := linEval (A i) N (xvec h)
  set u₂ : ZMod N := linEval (A j) N (xvec s)
  have hu_ne : (e₁, i, u₁) ≠ (e₂, j, u₂) := by
    intro heq
    have he12 : e₁ = e₂ := congrArg (fun p ↦ p.1) heq
    have hij : i = j := congrArg (fun p ↦ p.2.1) heq
    have hu12 : u₁ = u₂ := congrArg (fun p ↦ p.2.2) heq
    subst he12 hij
    have hhs : h ≠ s := fun hh ↦ hne (by rw [hh])
    have hedge_ne : (enumℳ h).1 ≠ (enumℳ s).1 :=
      fun heq' ↦ hhs (enumℳ.injective (Subtype.ext heq'))
    have hdisj := hℳ_disj (enumℳ h).1 (enumℳ h).2 (enumℳ s).1 (enumℳ s).2 hedge_ne
    have hm1 : (i, u₁) ∈ (enumℳ h).1 := by
      rw [← hxvec_edge h]; exact mem_image_of_mem _ (mem_univ i)
    have hm2 : (i, u₁) ∈ (enumℳ s).1 := by
      rw [← hxvec_edge s, hu12]; exact mem_image_of_mem _ (mem_univ i)
    exact Finset.disjoint_left.mp hdisj hm1 hm2
  have hu₁_int : isInterior b N S L u₁ := (hValid_spec (xvec h) (mem_filter.mp (hxvec_mem h)).1).1 i
  have hu₂_int : isInterior b N S L u₂ := (hValid_spec (xvec s) (mem_filter.mp (hxvec_mem s)).1).1 j
  have hω₁ : ω (slotFin N S L hS_pos u₁) = keyOf b Q h2Lmax_lt_Q N S L i u₁ :=
    (mem_filter.mp (hxvec_mem h)).2 i
  have hω₂ : ω (slotFin N S L hS_pos u₂) = keyOf b Q h2Lmax_lt_Q N S L j u₂ :=
    (mem_filter.mp (hxvec_mem s)).2 j
  have hz₁_cast : (z₁ : ZMod N) = (if e₁ then (1 : ZMod N) else -1) * u₁ := by
    dsimp [z₁, u₁, linEval]
    cases e₁ <;> simp
  have hz₂_cast : (z₂ : ZMod N) = (if e₂ then (1 : ZMod N) else -1) * u₂ := by
    dsimp [z₂, u₂, linEval]
    cases e₂ <;> simp
  have hdisj_int : ∀ t₁ t₂ : ℤ, -(b i : ℤ) ≤ t₁ → t₁ ≤ b i → -(b j : ℤ) ≤ t₂ → t₂ ≤ b j →
      ((z₁ + t₁ : ℤ) : ZMod N) ≠ ((z₂ + t₂ : ℤ) : ZMod N) := by
    intro t₁ t₂ ht11 ht12 ht21 ht22
    push_cast
    rw [hz₁_cast, hz₂_cast]
    exact slot_intervals_disjoint b h2Lmax_lt_Q h2SL hS_pos hL_pos ω hu₁_int hu₂_int hω₁ hω₂ hu_ne
      t₁ t₂ ht11 ht12 ht21 ht22
  have hsep := zmod_interval_sep hN_pos (b i) (b j) z₁ z₂ hdisj_int q
  have hstrict : (w i + w j) / (2 * (H : ℝ)) <
      (((2 * b i + 1 : ℕ) + (2 * b j + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) := by
    have hH_R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
    have h1 : (1 + 2 * ε) * (Q : ℝ) * (w i + w j) < ((2 * b i + 1 : ℕ) : ℝ) + ((2 * b j + 1 : ℕ) : ℝ) := by
      have hi : (1 + 2 * ε) * (Q : ℝ) * w i < ((2 * b i + 1 : ℕ) : ℝ) := hell_lo i
      have hj : (1 + 2 * ε) * (Q : ℝ) * w j < ((2 * b j + 1 : ℕ) : ℝ) := hell_lo j
      linarith only [hi, hj]
    have h2 : (w i + w j) / (2 * (H : ℝ)) <
        ((1 + 2 * ε) * (Q : ℝ) * (w i + w j)) / (2 * (N : ℝ)) := by
      have h2H : (0 : ℝ) < 2 * (H : ℝ) := mul_pos two_pos hH_R
      have h2N : (0 : ℝ) < 2 * (N : ℝ) := mul_pos two_pos hN_R
      have h12eQ : (0 : ℝ) < (1 + 2 * ε) * (Q : ℝ) :=
        mul_pos (by linarith only [hε_pos]) hQ_R
      rw [div_lt_div_iff₀ h2H h2N]
      have hw_ij : 0 < w i + w j := add_pos (hw_pos i) (hw_pos j)
      have hHmul : (N : ℝ) < (H : ℝ) * ((1 + 2 * ε) * (Q : ℝ)) :=
        (div_lt_iff₀ h12eQ).mp hH_lo
      nlinarith only [hw_ij, hHmul]
    have h3 : ((1 + 2 * ε) * (Q : ℝ) * (w i + w j)) / (2 * (N : ℝ)) <
        (((2 * b i + 1 : ℕ) : ℝ) + ((2 * b j + 1 : ℕ) : ℝ)) / (2 * (N : ℝ)) :=
      div_lt_div_of_pos_right h1 (mul_pos two_pos hN_R)
    exact h2.trans h3
  exact lt_of_lt_of_le hstrict hsep

end SlotPacking

end Green84H2Proof

theorem OMA.solution : OMA.R_Green84_green_84_variants_littlewood_R1.H2 :=
  Green84H2Proof.h2_from_nibble (fun r hr γ hγ ↦
    Green84H2Nibble.rodl_nibble_matching r hr γ hγ)
