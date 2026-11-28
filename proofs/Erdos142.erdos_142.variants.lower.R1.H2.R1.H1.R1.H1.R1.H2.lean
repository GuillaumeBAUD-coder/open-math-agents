import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1.H2
-- Credit: @Carson1903

lemma OMA.sq_sum_mul_le {ι : Type*} [Fintype ι] (g h : ι → ℝ) (hg : ∀ i, |g i| ≤ 1) :
    (∑ i : ι, g i * h i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (h i) ^ 2 := by
  calc (∑ i : ι, g i * h i) ^ 2
      ≤ (∑ i : ι, (g i) ^ 2) * ∑ i : ι, (h i) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g h
    _ ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (h i) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        calc ∑ i : ι, (g i) ^ 2
            ≤ ∑ _i : ι, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro i _
              have hle := abs_le.mp (hg i)
              nlinarith
          _ = (Fintype.card ι : ℝ) := by simp

lemma OMA.sum_sq_eq_sum_diff {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℝ) :
    (∑ d : G, F d) ^ 2 = ∑ h : G, ∑ d : G, F d * F (d + h) := by
  rw [sq, Finset.sum_mul_sum]
  calc ∑ d₁ : G, ∑ d₂ : G, F d₁ * F d₂
      = ∑ d₁ : G, ∑ h : G, F d₁ * F (d₁ + h) := by
        refine Finset.sum_congr rfl fun d₁ _ ↦ ?_
        exact (Equiv.sum_comp (Equiv.addLeft d₁) (fun y ↦ F d₁ * F y)).symm
    _ = ∑ h : G, ∑ d : G, F d * F (d + h) := Finset.sum_comm

lemma OMA.sum_add_right {G : Type*} [AddCommGroup G] [Fintype G] (a : G) (F : G → ℝ) :
    ∑ x : G, F (x + a) = ∑ x : G, F x :=
  Equiv.sum_comp (Equiv.addRight a) F

lemma OMA.sum_mul_left {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) (F : ZMod p → ℝ) :
    ∑ h : ZMod p, F (a * h) = ∑ h : ZMod p, F h :=
  Equiv.sum_comp (Equiv.mulLeft₀ a ha) F

lemma OMA.abs_mul_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]
  calc |x| * |y| ≤ 1 * 1 := mul_le_mul hx hy (abs_nonneg y) (by norm_num)
    _ = 1 := one_mul 1

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro p hp c₀ c₁ c₂ c₃ h01 h02 h03 h12 h13 h23 f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set a₁ : ZMod p := c₁ - c₀
  set a₂ : ZMod p := c₂ - c₀
  set a₃ : ZMod p := c₃ - c₀
  set b₂ : ZMod p := c₂ - c₁
  set b₃ : ZMod p := c₃ - c₁
  set e₃ : ZMod p := c₃ - c₂
  have ha₃ : a₃ ≠ 0 := sub_ne_zero.mpr h03.symm
  have hb₃ : b₃ ≠ 0 := sub_ne_zero.mpr h13.symm
  have he₃ : e₃ ≠ 0 := sub_ne_zero.mpr h23.symm
  let S : ℝ := ∑ x : ZMod p, ∑ d : ZMod p,
    f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)
  let g₁ : ZMod p → ZMod p → ℝ := fun h₁ y ↦ f₁ y * f₁ (y + a₁ * h₁)
  let g₂ : ZMod p → ZMod p → ℝ := fun h₁ y ↦ f₂ y * f₂ (y + a₂ * h₁)
  let g₃ : ZMod p → ZMod p → ℝ := fun h₁ y ↦ f₃ y * f₃ (y + a₃ * h₁)
  let g₂' : ZMod p → ZMod p → ZMod p → ℝ := fun h₁ h₂ y ↦ g₂ h₁ y * g₂ h₁ (y + b₂ * h₂)
  let g₃' : ZMod p → ZMod p → ZMod p → ℝ := fun h₁ h₂ y ↦ g₃ h₁ y * g₃ h₁ (y + b₃ * h₂)
  let T₁ : ℝ := ∑ h₁ : ZMod p, ∑ u : ZMod p, ∑ d : ZMod p,
    g₁ h₁ (u + a₁ * d) * g₂ h₁ (u + a₂ * d) * g₃ h₁ (u + a₃ * d)
  let T₂ : ℝ := ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ v : ZMod p, ∑ d : ZMod p,
    g₂' h₁ h₂ (v + b₂ * d) * g₃' h₁ h₂ (v + b₃ * d)
  let T₃ : ℝ := ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ w : ZMod p, ∑ d : ZMod p,
    g₃' h₁ h₂ (w + e₃ * d) * g₃' h₁ h₂ (w + e₃ * d + e₃ * h₃)
  have hS_rew : S = ∑ u : ZMod p, f₀ u * ∑ d : ZMod p,
      f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d) := by
    dsimp [S]
    rw [Finset.sum_comm]
    have hshift : ∀ d : ZMod p,
        ∑ x : ZMod p, f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d) =
        ∑ u : ZMod p, f₀ u * (f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) := by
      intro d
      rw [← OMA.sum_add_right (c₀ * d) (fun u ↦ f₀ u * (f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)))]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have h1 : x + c₀ * d + a₁ * d = x + c₁ * d := by dsimp [a₁]; ring
      have h2 : x + c₀ * d + a₂ * d = x + c₂ * d := by dsimp [a₂]; ring
      have h3 : x + c₀ * d + a₃ * d = x + c₃ * d := by dsimp [a₃]; ring
      rw [h1, h2, h3]; ring
    simp_rw [hshift, Finset.mul_sum]
    exact Finset.sum_comm
  have hstep1 : S ^ 2 ≤ (p : ℝ) * T₁ := by
    rw [hS_rew]
    have hcs := OMA.sq_sum_mul_le f₀
      (fun u ↦ ∑ d : ZMod p, f₁ (u + a₁ * d) * f₂ (u + a₂ * d) * f₃ (u + a₃ * d)) hf₀
    rw [ZMod.card] at hcs
    refine hcs.trans_eq ?_
    congr 1
    simp_rw [OMA.sum_sq_eq_sum_diff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h₁ _ ↦ Finset.sum_congr rfl fun u _ ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    have h1 : u + a₁ * (d + h₁) = u + a₁ * d + a₁ * h₁ := by ring
    have h2 : u + a₂ * (d + h₁) = u + a₂ * d + a₂ * h₁ := by ring
    have h3 : u + a₃ * (d + h₁) = u + a₃ * d + a₃ * h₁ := by ring
    dsimp [g₁, g₂, g₃]
    rw [h1, h2, h3]; ring
  have hT₁_rew : T₁ = ∑ q : ZMod p × ZMod p,
      g₁ q.1 q.2 * ∑ d : ZMod p, g₂ q.1 (q.2 + b₂ * d) * g₃ q.1 (q.2 + b₃ * d) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h₁ _ ↦ ?_
    rw [Finset.sum_comm]
    have hshift : ∀ d : ZMod p,
        ∑ u : ZMod p, g₁ h₁ (u + a₁ * d) * g₂ h₁ (u + a₂ * d) * g₃ h₁ (u + a₃ * d) =
        ∑ v : ZMod p, g₁ h₁ v * (g₂ h₁ (v + b₂ * d) * g₃ h₁ (v + b₃ * d)) := by
      intro d
      rw [← OMA.sum_add_right (a₁ * d) (fun v ↦ g₁ h₁ v * (g₂ h₁ (v + b₂ * d) * g₃ h₁ (v + b₃ * d)))]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      have h2 : u + a₁ * d + b₂ * d = u + a₂ * d := by dsimp [a₁, a₂, b₂]; ring
      have h3 : u + a₁ * d + b₃ * d = u + a₃ * d := by dsimp [a₁, a₃, b₃]; ring
      rw [h2, h3]; ring
    simp_rw [hshift, Finset.mul_sum]
    exact Finset.sum_comm
  have hstep2 : T₁ ^ 2 ≤ (p : ℝ) ^ 2 * T₂ := by
    rw [hT₁_rew]
    have hg₁ : ∀ q : ZMod p × ZMod p, |g₁ q.1 q.2| ≤ 1 := fun q ↦
      OMA.abs_mul_le_one (hf₁ _) (hf₁ _)
    have hcs := OMA.sq_sum_mul_le (fun q : ZMod p × ZMod p ↦ g₁ q.1 q.2)
      (fun q ↦ ∑ d : ZMod p, g₂ q.1 (q.2 + b₂ * d) * g₃ q.1 (q.2 + b₃ * d)) hg₁
    have hcard : (Fintype.card (ZMod p × ZMod p) : ℝ) = (p : ℝ) ^ 2 := by
      simp [Fintype.card_prod, ZMod.card, sq]
    rw [hcard] at hcs
    refine hcs.trans_eq ?_
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h₁ _ ↦ ?_
    simp_rw [OMA.sum_sq_eq_sum_diff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h₂ _ ↦ Finset.sum_congr rfl fun v _ ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    have h2 : v + b₂ * (d + h₂) = v + b₂ * d + b₂ * h₂ := by ring
    have h3 : v + b₃ * (d + h₂) = v + b₃ * d + b₃ * h₂ := by ring
    dsimp [g₂', g₃']
    rw [h2, h3]; ring
  have hT₂_rew : T₂ = ∑ q : (ZMod p × ZMod p) × ZMod p,
      g₂' q.1.1 q.1.2 q.2 * ∑ d : ZMod p, g₃' q.1.1 q.1.2 (q.2 + e₃ * d) := by
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h₁ _ ↦ Finset.sum_congr rfl fun h₂ _ ↦ ?_
    rw [Finset.sum_comm]
    have hshift : ∀ d : ZMod p,
        ∑ v : ZMod p, g₂' h₁ h₂ (v + b₂ * d) * g₃' h₁ h₂ (v + b₃ * d) =
        ∑ w : ZMod p, g₂' h₁ h₂ w * g₃' h₁ h₂ (w + e₃ * d) := by
      intro d
      rw [← OMA.sum_add_right (b₂ * d) (fun w ↦ g₂' h₁ h₂ w * g₃' h₁ h₂ (w + e₃ * d))]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      have h3 : v + b₂ * d + e₃ * d = v + b₃ * d := by dsimp [b₂, b₃, e₃]; ring
      rw [h3]
    simp_rw [hshift, Finset.mul_sum]
    exact Finset.sum_comm
  have hstep3 : T₂ ^ 2 ≤ (p : ℝ) ^ 3 * T₃ := by
    rw [hT₂_rew]
    have hg₂' : ∀ q : (ZMod p × ZMod p) × ZMod p, |g₂' q.1.1 q.1.2 q.2| ≤ 1 := fun q ↦
      OMA.abs_mul_le_one (OMA.abs_mul_le_one (hf₂ _) (hf₂ _))
        (OMA.abs_mul_le_one (hf₂ _) (hf₂ _))
    have hcs := OMA.sq_sum_mul_le (fun q : (ZMod p × ZMod p) × ZMod p ↦ g₂' q.1.1 q.1.2 q.2)
      (fun q ↦ ∑ d : ZMod p, g₃' q.1.1 q.1.2 (q.2 + e₃ * d)) hg₂'
    have hcard : (Fintype.card ((ZMod p × ZMod p) × ZMod p) : ℝ) = (p : ℝ) ^ 3 := by
      simp [Fintype.card_prod, ZMod.card]; ring
    rw [hcard] at hcs
    refine hcs.trans_eq ?_
    congr 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h₁ _ ↦ Finset.sum_congr rfl fun h₂ _ ↦ ?_
    simp_rw [OMA.sum_sq_eq_sum_diff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h₃ _ ↦ Finset.sum_congr rfl fun w _ ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    have h3 : w + e₃ * (d + h₃) = w + e₃ * d + e₃ * h₃ := by ring
    rw [h3]
  have hT₃_eq : T₃ = (p : ℝ) * ∑ x : ZMod p, ∑ k₁ : ZMod p, ∑ k₂ : ZMod p, ∑ k₃ : ZMod p,
      f₃ x * f₃ (x + k₁) * f₃ (x + k₂) * f₃ (x + k₁ + k₂) *
      f₃ (x + k₃) * f₃ (x + k₁ + k₃) * f₃ (x + k₂ + k₃) * f₃ (x + k₁ + k₂ + k₃) := by
    have hinner : ∀ h₁ h₂ h₃ : ZMod p,
        ∑ w : ZMod p, ∑ d : ZMod p, g₃' h₁ h₂ (w + e₃ * d) * g₃' h₁ h₂ (w + e₃ * d + e₃ * h₃) =
        (p : ℝ) * ∑ x : ZMod p, g₃' h₁ h₂ x * g₃' h₁ h₂ (x + e₃ * h₃) := by
      intro h₁ h₂ h₃
      rw [Finset.sum_comm]
      have hconst : ∀ d : ZMod p,
          ∑ w : ZMod p, g₃' h₁ h₂ (w + e₃ * d) * g₃' h₁ h₂ (w + e₃ * d + e₃ * h₃) =
          ∑ x : ZMod p, g₃' h₁ h₂ x * g₃' h₁ h₂ (x + e₃ * h₃) := fun d ↦
        OMA.sum_add_right (e₃ * d) (fun x ↦ g₃' h₁ h₂ x * g₃' h₁ h₂ (x + e₃ * h₃))
      simp_rw [hconst, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    dsimp [T₃]
    simp_rw [hinner, ← Finset.mul_sum]
    congr 1
    have hrew : ∀ h₁ h₂ h₃ x : ZMod p,
        g₃' h₁ h₂ x * g₃' h₁ h₂ (x + e₃ * h₃) =
        f₃ x * f₃ (x + a₃ * h₁) * f₃ (x + b₃ * h₂) * f₃ (x + a₃ * h₁ + b₃ * h₂) *
        f₃ (x + e₃ * h₃) * f₃ (x + a₃ * h₁ + e₃ * h₃) * f₃ (x + b₃ * h₂ + e₃ * h₃) *
        f₃ (x + a₃ * h₁ + b₃ * h₂ + e₃ * h₃) := by
      intro h₁ h₂ h₃ x
      dsimp [g₃', g₃]
      have e1 : x + b₃ * h₂ + a₃ * h₁ = x + a₃ * h₁ + b₃ * h₂ := by ring
      have e2 : x + e₃ * h₃ + a₃ * h₁ = x + a₃ * h₁ + e₃ * h₃ := by ring
      have e3 : x + e₃ * h₃ + b₃ * h₂ = x + b₃ * h₂ + e₃ * h₃ := by ring
      have e4 : x + b₃ * h₂ + e₃ * h₃ + a₃ * h₁ = x + a₃ * h₁ + b₃ * h₂ + e₃ * h₃ := by ring
      rw [e1, e2, e3, e4]
      ring
    simp_rw [hrew]
    let Q : ZMod p → ZMod p → ZMod p → ZMod p → ℝ := fun x k₁ k₂ k₃ ↦
      f₃ x * f₃ (x + k₁) * f₃ (x + k₂) * f₃ (x + k₁ + k₂) *
      f₃ (x + k₃) * f₃ (x + k₁ + k₃) * f₃ (x + k₂ + k₃) * f₃ (x + k₁ + k₂ + k₃)
    change ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p, ∑ x : ZMod p,
        Q x (a₃ * h₁) (b₃ * h₂) (e₃ * h₃) =
      ∑ x : ZMod p, ∑ k₁ : ZMod p, ∑ k₂ : ZMod p, ∑ k₃ : ZMod p, Q x k₁ k₂ k₃
    have h3 : ∀ h₁ h₂ : ZMod p,
        ∑ h₃ : ZMod p, ∑ x : ZMod p, Q x (a₃ * h₁) (b₃ * h₂) (e₃ * h₃) =
        ∑ k₃ : ZMod p, ∑ x : ZMod p, Q x (a₃ * h₁) (b₃ * h₂) k₃ := fun h₁ h₂ ↦
      OMA.sum_mul_left he₃ (fun k₃ ↦ ∑ x : ZMod p, Q x (a₃ * h₁) (b₃ * h₂) k₃)
    simp_rw [h3]
    have h2 : ∀ h₁ : ZMod p,
        ∑ h₂ : ZMod p, ∑ k₃ : ZMod p, ∑ x : ZMod p, Q x (a₃ * h₁) (b₃ * h₂) k₃ =
        ∑ k₂ : ZMod p, ∑ k₃ : ZMod p, ∑ x : ZMod p, Q x (a₃ * h₁) k₂ k₃ := fun h₁ ↦
      OMA.sum_mul_left hb₃ (fun k₂ ↦ ∑ k₃ : ZMod p, ∑ x : ZMod p, Q x (a₃ * h₁) k₂ k₃)
    simp_rw [h2]
    rw [OMA.sum_mul_left ha₃ (fun k₁ ↦ ∑ k₂ : ZMod p, ∑ k₃ : ZMod p, ∑ x : ZMod p, Q x k₁ k₂ k₃)]
    trans ∑ k₁ : ZMod p, ∑ k₂ : ZMod p, ∑ x : ZMod p, ∑ k₃ : ZMod p, Q x k₁ k₂ k₃
    · refine Finset.sum_congr rfl fun k₁ _ ↦ Finset.sum_congr rfl fun k₂ _ ↦ Finset.sum_comm
    trans ∑ k₁ : ZMod p, ∑ x : ZMod p, ∑ k₂ : ZMod p, ∑ k₃ : ZMod p, Q x k₁ k₂ k₃
    · refine Finset.sum_congr rfl fun k₁ _ ↦ Finset.sum_comm
    exact Finset.sum_comm
  have hT₁_nn : 0 ≤ T₁ := by
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    have hsq : (0 : ℝ) ≤ S ^ 2 := sq_nonneg S
    nlinarith
  have hT₂_nn : 0 ≤ T₂ := by
    have hp_pos : (0 : ℝ) < (p : ℝ) ^ 2 := pow_pos (by exact_mod_cast hp.out.pos) 2
    have hsq : (0 : ℝ) ≤ T₁ ^ 2 := sq_nonneg T₁
    nlinarith
  have hS4 : S ^ 4 ≤ (p : ℝ) ^ 4 * T₂ := by
    calc S ^ 4 = (S ^ 2) ^ 2 := by ring
      _ ≤ ((p : ℝ) * T₁) ^ 2 := pow_le_pow_left₀ (sq_nonneg S) hstep1 2
      _ = (p : ℝ) ^ 2 * T₁ ^ 2 := by ring
      _ ≤ (p : ℝ) ^ 2 * ((p : ℝ) ^ 2 * T₂) :=
          mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ = (p : ℝ) ^ 4 * T₂ := by ring
  have hS8 : S ^ 8 ≤ (p : ℝ) ^ 11 * T₃ := by
    calc S ^ 8 = (S ^ 4) ^ 2 := by ring
      _ ≤ ((p : ℝ) ^ 4 * T₂) ^ 2 := pow_le_pow_left₀ (by positivity) hS4 2
      _ = (p : ℝ) ^ 8 * T₂ ^ 2 := by ring
      _ ≤ (p : ℝ) ^ 8 * ((p : ℝ) ^ 3 * T₃) :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)
      _ = (p : ℝ) ^ 11 * T₃ := by ring
  rw [hT₃_eq] at hS8
  calc S ^ 8
      ≤ (p : ℝ) ^ 11 * ((p : ℝ) * ∑ x : ZMod p, ∑ k₁ : ZMod p, ∑ k₂ : ZMod p, ∑ k₃ : ZMod p,
          f₃ x * f₃ (x + k₁) * f₃ (x + k₂) * f₃ (x + k₁ + k₂) *
          f₃ (x + k₃) * f₃ (x + k₁ + k₃) * f₃ (x + k₂ + k₃) * f₃ (x + k₁ + k₂ + k₃)) := hS8
    _ = (p : ℝ) ^ 12 * ∑ x : ZMod p, ∑ k₁ : ZMod p, ∑ k₂ : ZMod p, ∑ k₃ : ZMod p,
          f₃ x * f₃ (x + k₁) * f₃ (x + k₂) * f₃ (x + k₁ + k₂) *
          f₃ (x + k₃) * f₃ (x + k₁ + k₃) * f₃ (x + k₂ + k₃) * f₃ (x + k₁ + k₂ + k₃) := by ring
