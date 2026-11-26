import FormalConjectures.ErdosProblems.«785»

/-!
# Proof of Erdős Problem 785 (Narkiewicz's theorem)
-/

-- Problem: Erdős Problem 785 — narkiewicz
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/785.lean:131 (declaration Erdos785.erdos_785.variants.narkiewicz)
-- Credit: @Goidelg (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Narkiewicz

open Filter Pointwise
open scoped Topology

private lemma counting_mono {A : Set ℕ} {x y : ℕ} (hxy : x ≤ y) :
    Erdos785.counting A x ≤ Erdos785.counting A y := by
  unfold Erdos785.counting
  apply Set.ncard_le_ncard
  · intro n hn
    exact ⟨hn.1, hn.2.1, le_trans hn.2.2 hxy⟩
  · exact (Set.finite_Icc 1 y).subset Set.inter_subset_right

private lemma counting_succ_le (A : Set ℕ) (x : ℕ) :
    Erdos785.counting A (x + 1) ≤ Erdos785.counting A x + 1 := by
  unfold Erdos785.counting
  have hsub : A ∩ Set.Icc 1 (x + 1) ⊆ (A ∩ Set.Icc 1 x) ∪ {x + 1} := by
    intro n hn
    rcases hn with ⟨hnA, h1, h2⟩
    by_cases hle : n ≤ x
    · exact Or.inl ⟨hnA, h1, hle⟩
    · exact Or.inr (by simp; omega)
  have hfin : ((A ∩ Set.Icc 1 x) ∪ ({x + 1} : Set ℕ)).Finite :=
    ((Set.finite_Icc 1 x).subset Set.inter_subset_right).union (Set.finite_singleton _)
  calc
    (A ∩ Set.Icc 1 (x + 1)).ncard
        ≤ ((A ∩ Set.Icc 1 x) ∪ ({x + 1} : Set ℕ)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (A ∩ Set.Icc 1 x).ncard + ({x + 1} : Set ℕ).ncard := Set.ncard_union_le _ _
    _ = (A ∩ Set.Icc 1 x).ncard + 1 := by simp

private lemma counting_add_two_le (A : Set ℕ) (x : ℕ) :
    Erdos785.counting A (x + 2) ≤ Erdos785.counting A x + 2 := by
  have h1 := counting_succ_le A x
  have h2 := counting_succ_le A (x + 1)
  have heq : x + 1 + 1 = x + 2 := by omega
  rw [heq] at h2
  omega

private lemma tendsto_counting_nat {A : Set ℕ} (hA : A.Infinite) (hA₀ : 0 ∉ A) :
    Tendsto (Erdos785.counting A) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨s, hsA, hscard⟩ := hA.exists_subset_card_eq M
  refine ⟨s.sup id, fun x hx => ?_⟩
  unfold Erdos785.counting
  have hsub : (s : Set ℕ) ⊆ A ∩ Set.Icc 1 x := by
    intro a ha
    have haA : a ∈ A := hsA ha
    have ha0 : a ≠ 0 := fun h0 => hA₀ (h0 ▸ haA)
    have hale : a ≤ x := le_trans (Finset.le_sup (f := id) ha) hx
    exact ⟨haA, by omega, hale⟩
  have hfin : (A ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).subset Set.inter_subset_right
  calc
    M = s.card := hscard.symm
    _ = (s : Set ℕ).ncard := (Set.ncard_coe_finset s).symm
    _ ≤ (A ∩ Set.Icc 1 x).ncard := Set.ncard_le_ncard hsub hfin

private lemma tendsto_counting_real {A : Set ℕ} (hA : A.Infinite) (hA₀ : 0 ∉ A) :
    Tendsto (fun x : ℕ => (Erdos785.counting A x : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_counting_nat hA hA₀)

private lemma counting_sumset_bound {A B : Set ℕ} (hA₀ : 0 ∉ A) (hB₀ : 0 ∉ B)
    {N₀ : ℕ} (hN₀ : ∀ n ≥ N₀, n ∈ A + B) (x : ℕ) :
    2 * x - max 1 N₀ + Erdos785.counting A x * Erdos785.counting B x ≤
      Erdos785.counting A x * Erdos785.counting B (2 * x) +
      Erdos785.counting A (2 * x) * Erdos785.counting B x := by
  set N₁ := max 1 N₀
  set A1 := A ∩ Set.Icc 1 x
  set A2 := A ∩ Set.Icc 1 (2 * x)
  set B1 := B ∩ Set.Icc 1 x
  set B2 := B ∩ Set.Icc 1 (2 * x)
  set S : Set (ℕ × ℕ) := (A1 ×ˢ B2) ∪ (A2 ×ˢ B1)
  have hA1_fin : A1.Finite := (Set.finite_Icc 1 x).subset Set.inter_subset_right
  have hA2_fin : A2.Finite := (Set.finite_Icc 1 (2 * x)).subset Set.inter_subset_right
  have hB1_fin : B1.Finite := (Set.finite_Icc 1 x).subset Set.inter_subset_right
  have hB2_fin : B2.Finite := (Set.finite_Icc 1 (2 * x)).subset Set.inter_subset_right
  have hS_fin : S.Finite := (hA1_fin.prod hB2_fin).union (hA2_fin.prod hB1_fin)
  have hsub : Set.Icc N₁ (2 * x) ⊆ (fun p : ℕ × ℕ => p.1 + p.2) '' S := by
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    have hnN0 : n ≥ N₀ := le_trans (le_max_right 1 N₀) hn1
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp (hN₀ n hnN0)
    have ha0 : a ≠ 0 := fun h0 => hA₀ (h0 ▸ ha)
    have hb0 : b ≠ 0 := fun h0 => hB₀ (h0 ▸ hb)
    have ha2 : a ≤ 2 * x := by omega
    have hb2 : b ≤ 2 * x := by omega
    refine ⟨(a, b), ?_, hab⟩
    by_cases hax : a ≤ x
    · exact Or.inl ⟨⟨ha, by omega, hax⟩, ⟨hb, by omega, hb2⟩⟩
    · exact Or.inr ⟨⟨ha, by omega, ha2⟩, ⟨hb, by omega, by omega⟩⟩
  have hcard_icc : 2 * x - N₁ ≤ (Set.Icc N₁ (2 * x)).ncard := by
    rw [show Set.Icc N₁ (2 * x) = (Finset.Icc N₁ (2 * x) : Set ℕ) by ext; simp]
    rw [Set.ncard_coe_finset, Nat.card_Icc]
    omega
  have hcard_le : (Set.Icc N₁ (2 * x)).ncard ≤ S.ncard :=
    le_trans (Set.ncard_le_ncard hsub (hS_fin.image _)) (Set.ncard_image_le hS_fin)
  have hinter : (A1 ×ˢ B2) ∩ (A2 ×ˢ B1) = A1 ×ˢ B1 := by
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, A1, A2, B1, B2, Set.mem_Icc]
    constructor
    · rintro ⟨⟨⟨ha, h1a, hxa⟩, _⟩, ⟨_, ⟨hb, h1b, hxb⟩⟩⟩
      exact ⟨⟨ha, h1a, hxa⟩, ⟨hb, h1b, hxb⟩⟩
    · rintro ⟨⟨ha, h1a, hxa⟩, ⟨hb, h1b, hxb⟩⟩
      exact ⟨⟨⟨ha, h1a, hxa⟩, ⟨hb, h1b, by omega⟩⟩, ⟨⟨ha, h1a, by omega⟩, ⟨hb, h1b, hxb⟩⟩⟩
  have hinc := Set.ncard_union_add_ncard_inter (A1 ×ˢ B2) (A2 ×ˢ B1)
    (hA1_fin.prod hB2_fin) (hA2_fin.prod hB1_fin)
  rw [hinter] at hinc
  simp only [Set.ncard_prod] at hinc
  have hS_eq : S.ncard + A1.ncard * B1.ncard = A1.ncard * B2.ncard + A2.ncard * B1.ncard := hinc
  change 2 * x - N₁ + A1.ncard * B1.ncard ≤ A1.ncard * B2.ncard + A2.ncard * B1.ncard
  omega

private lemma real_sumset_bound {A B : Set ℕ} (hA₀ : 0 ∉ A) (hB₀ : 0 ∉ B)
    {N₀ : ℕ} (hN₀ : ∀ n ≥ N₀, n ∈ A + B) (x : ℕ) :
    (2 * (x : ℝ) - (max 1 N₀ : ℝ)) + (Erdos785.counting A x : ℝ) * (Erdos785.counting B x : ℝ) ≤
      (Erdos785.counting A x : ℝ) * (Erdos785.counting B (2 * x) : ℝ) +
      (Erdos785.counting A (2 * x) : ℝ) * (Erdos785.counting B x : ℝ) := by
  have hnat := counting_sumset_bound hA₀ hB₀ hN₀ x
  have hreal : ((2 * x - max 1 N₀ + Erdos785.counting A x * Erdos785.counting B x : ℕ) : ℝ) ≤
      ((Erdos785.counting A x * Erdos785.counting B (2 * x) +
        Erdos785.counting A (2 * x) * Erdos785.counting B x : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hreal
  have hsub : (2 * (x : ℝ) - (max 1 N₀ : ℝ)) ≤ ((2 * x - max 1 N₀ : ℕ) : ℝ) := by
    by_cases hle : max 1 N₀ ≤ 2 * x
    · rw [Nat.cast_sub hle]
      push_cast
      linarith
    · have h0 : (2 * x - max 1 N₀ : ℕ) = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hle)
      rw [h0, Nat.cast_zero]
      have hlt : (2 * x : ℝ) < (max 1 N₀ : ℝ) := by exact_mod_cast (lt_of_not_ge hle)
      linarith
  linarith

private lemma no_switch_lt {u : ℕ → ℝ} {X₀ : ℕ}
    (hgap : ∀ x ≥ X₀, u x < 4 / 3 ∨ 5 / 3 < u x)
    (hstep : ∀ x ≥ X₀, |u (x + 1) - u x| < 1 / 4)
    (h0 : u X₀ < 4 / 3) : ∀ x ≥ X₀, u x < 4 / 3 := by
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hx
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hprev : u (X₀ + k) < 4 / 3 := ih (Nat.le_add_right X₀ k)
    have hst : |u (X₀ + k + 1) - u (X₀ + k)| < 1 / 4 := hstep (X₀ + k) (Nat.le_add_right X₀ k)
    have hnext_lt : u (X₀ + k + 1) < 5 / 3 := by
      have := (abs_lt.mp hst).2
      linarith
    rcases hgap (X₀ + (k + 1)) (Nat.le_add_right X₀ (k + 1)) with hlt | hgt
    · exact hlt
    · exfalso
      have : X₀ + (k + 1) = X₀ + k + 1 := by omega
      rw [this] at hgt
      linarith

private lemma no_switch_gt {u : ℕ → ℝ} {X₀ : ℕ}
    (hgap : ∀ x ≥ X₀, u x < 4 / 3 ∨ 5 / 3 < u x)
    (hstep : ∀ x ≥ X₀, |u (x + 1) - u x| < 1 / 4)
    (h0 : 5 / 3 < u X₀) : ∀ x ≥ X₀, 5 / 3 < u x := by
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hx
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hprev : 5 / 3 < u (X₀ + k) := ih (Nat.le_add_right X₀ k)
    have hst : |u (X₀ + k + 1) - u (X₀ + k)| < 1 / 4 := hstep (X₀ + k) (Nat.le_add_right X₀ k)
    have hnext_gt : 4 / 3 < u (X₀ + k + 1) := by
      have := (abs_lt.mp hst).1
      linarith
    rcases hgap (X₀ + (k + 1)) (Nat.le_add_right X₀ (k + 1)) with hlt | hgt
    · exfalso
      have : X₀ + (k + 1) = X₀ + k + 1 := by omega
      rw [this] at hlt
      linarith
    · exact hgt

end OMA.Narkiewicz

open Filter
open scoped Topology

theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.narkiewicz := by
  intro A B hA hB hA₀ hB₀ h
  rcases h with ⟨hadd, hasymp⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hadd
  set N₁ : ℕ := max 1 N₀
  let a : ℕ → ℝ := fun x => (Erdos785.counting A x : ℝ)
  let b : ℕ → ℝ := fun x => (Erdos785.counting B x : ℝ)
  let u : ℕ → ℝ := fun x => a (2 * x) / a x
  let v : ℕ → ℝ := fun x => b (2 * x) / b x
  let f : ℕ → ℝ := fun x => (a x * b x) / (x : ℝ)
  have ha_inf : Tendsto a atTop atTop := OMA.Narkiewicz.tendsto_counting_real hA hA₀
  have hb_inf : Tendsto b atTop atTop := OMA.Narkiewicz.tendsto_counting_real hB hB₀
  have ha_pos : ∀ᶠ x in atTop, 0 < a x := ha_inf.eventually_gt_atTop 0
  have hb_pos : ∀ᶠ x in atTop, 0 < b x := hb_inf.eventually_gt_atTop 0
  have hx_pos : ∀ᶠ x : ℕ in atTop, 0 < (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop 0
  have hu_ge1 : ∀ᶠ x in atTop, 1 ≤ u x := by
    filter_upwards [ha_pos] with x hax
    change 1 ≤ a (2 * x) / a x
    rw [one_le_div hax]
    dsimp only [a]
    exact_mod_cast OMA.Narkiewicz.counting_mono (A := A) (by omega : x ≤ 2 * x)
  have hv_ge1 : ∀ᶠ x in atTop, 1 ≤ v x := by
    filter_upwards [hb_pos] with x hbx
    change 1 ≤ b (2 * x) / b x
    rw [one_le_div hbx]
    dsimp only [b]
    exact_mod_cast OMA.Narkiewicz.counting_mono (A := B) (by omega : x ≤ 2 * x)
  have hf : Tendsto f atTop (𝓝 1) := hasymp
  have h2x : Tendsto (fun x : ℕ => 2 * x) atTop atTop := by
    rw [tendsto_atTop_atTop]
    exact fun M => ⟨M, fun x hx => by omega⟩
  have hf2 : Tendsto (fun x => f (2 * x)) atTop (𝓝 1) := hf.comp h2x
  have huv : Tendsto (fun x => u x * v x) atTop (𝓝 2) := by
    have hlim : Tendsto (fun x => 2 * f (2 * x) / f x) atTop (𝓝 (2 * 1 / 1)) :=
      ((hf2.const_mul 2).div hf (by norm_num))
    rw [show (2 * 1 / 1 : ℝ) = 2 by norm_num] at hlim
    refine hlim.congr' ?_
    filter_upwards [ha_pos, hb_pos, hx_pos] with x hax hbx hxp
    have hax' : a x ≠ 0 := ne_of_gt hax
    have hbx' : b x ≠ 0 := ne_of_gt hbx
    have hxp' : (x : ℝ) ≠ 0 := ne_of_gt hxp
    dsimp only [f, u, v]
    push_cast
    field_simp
  have hratio : Tendsto (fun x : ℕ => (2 * (x : ℝ) - (N₁ : ℝ)) / (a x * b x)) atTop (𝓝 2) := by
    have hNx : Tendsto (fun x : ℕ => (N₁ : ℝ) / (x : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hnum : Tendsto (fun x : ℕ => 2 - (N₁ : ℝ) / (x : ℝ)) atTop (𝓝 (2 - 0)) :=
      tendsto_const_nhds.sub hNx
    have hlim : Tendsto (fun x : ℕ => (2 - (N₁ : ℝ) / (x : ℝ)) / f x) atTop (𝓝 ((2 - 0) / 1)) :=
      hnum.div hf (by norm_num)
    rw [show ((2 - 0) / 1 : ℝ) = 2 by norm_num] at hlim
    refine hlim.congr' ?_
    filter_upwards [ha_pos, hb_pos, hx_pos] with x hax hbx hxp
    have hax' : a x ≠ 0 := ne_of_gt hax
    have hbx' : b x ≠ 0 := ne_of_gt hbx
    have hxp' : (x : ℝ) ≠ 0 := ne_of_gt hxp
    dsimp only [f]
    field_simp
  have hprod0 : Tendsto (fun x => (u x - 1) * (v x - 1)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun x => u x * v x - (2 * (x : ℝ) - (N₁ : ℝ)) / (a x * b x))
        atTop (𝓝 (2 - 2)) := huv.sub hratio
    rw [sub_self] at hupper
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [hu_ge1, hv_ge1] with x hux hvx
      nlinarith
    · filter_upwards [ha_pos, hb_pos] with x hax hbx
      have hbound := OMA.Narkiewicz.real_sumset_bound hA₀ hB₀ hN₀ x
      have hab_pos : 0 < a x * b x := mul_pos hax hbx
      have hdiv : (2 * (x : ℝ) - (N₁ : ℝ)) / (a x * b x) ≤ u x + v x - 1 := by
        rw [div_le_iff₀ hab_pos]
        have hax' : a x ≠ 0 := ne_of_gt hax
        have hbx' : b x ≠ 0 := ne_of_gt hbx
        have heq : (u x + v x - 1) * (a x * b x) =
            a (2 * x) * b x + a x * b (2 * x) - a x * b x := by
          dsimp only [u, v]
          field_simp
        rw [heq]
        dsimp only [a, b, N₁] at hbound ⊢
        rw [Nat.cast_max, Nat.cast_one]
        linarith
      linarith
  have hu_le3 : ∀ᶠ x in atTop, u x ≤ 3 := by
    filter_upwards [huv.eventually (Iio_mem_nhds (by norm_num : (2 : ℝ) < 3)), hv_ge1] with x hlt hv1
    nlinarith
  have hu_step : ∀ᶠ x in atTop, |u (x + 1) - u x| < 1 / 4 := by
    filter_upwards [ha_inf.eventually_gt_atTop 12, hu_le3] with x ha12 hu3
    have hax : 0 < a x := by linarith
    have ha1_ge : a x ≤ a (x + 1) := by
      dsimp only [a]
      exact_mod_cast OMA.Narkiewicz.counting_mono (A := A) (Nat.le_succ x)
    have ha1_le : a (x + 1) ≤ a x + 1 := by
      dsimp only [a]
      exact_mod_cast OMA.Narkiewicz.counting_succ_le A x
    have ha1_pos : 0 < a (x + 1) := by linarith
    have ha2_ge : a (2 * x) ≤ a (2 * (x + 1)) := by
      dsimp only [a]
      exact_mod_cast OMA.Narkiewicz.counting_mono (A := A) (by omega : 2 * x ≤ 2 * (x + 1))
    have ha2_le : a (2 * (x + 1)) ≤ a (2 * x) + 2 := by
      have h2 := OMA.Narkiewicz.counting_add_two_le A (2 * x)
      rw [show 2 * (x + 1) = 2 * x + 2 by omega]
      dsimp only [a]
      exact_mod_cast h2
    have hupper : u (x + 1) - u x < 1 / 4 := by
      have h1 : a (2 * (x + 1)) / a (x + 1) ≤ (a (2 * x) + 2) / a x := by
        calc
          a (2 * (x + 1)) / a (x + 1)
              ≤ (a (2 * x) + 2) / a (x + 1) := div_le_div_of_nonneg_right ha2_le (le_of_lt ha1_pos)
          _ ≤ (a (2 * x) + 2) / a x := by
            apply div_le_div_of_nonneg_left _ hax ha1_ge
            have : 0 ≤ a (2 * x) := Nat.cast_nonneg _
            linarith
      have h2 : (a (2 * x) + 2) / a x - a (2 * x) / a x = 2 / a x := by
        field_simp
        ring
      have h3 : 2 / a x < 1 / 4 := by
        rw [div_lt_div_iff₀ hax (by norm_num : (0 : ℝ) < 4)]
        linarith
      dsimp only [u]
      linarith
    have hlower : -(1 / 4 : ℝ) < u (x + 1) - u x := by
      have h1 : a (2 * x) / (a x + 1) ≤ a (2 * (x + 1)) / a (x + 1) := by
        calc
          a (2 * x) / (a x + 1)
              ≤ a (2 * x) / a (x + 1) :=
                div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha1_pos ha1_le
          _ ≤ a (2 * (x + 1)) / a (x + 1) :=
                div_le_div_of_nonneg_right ha2_ge (le_of_lt ha1_pos)
      have h2 : a (2 * x) / a x - a (2 * x) / (a x + 1) = u x / (a x + 1) := by
        have hax' : a x ≠ 0 := ne_of_gt hax
        have hax1' : a x + 1 ≠ 0 := by linarith
        dsimp only [u]
        field_simp
        ring
      have h3 : u x / (a x + 1) < 1 / 4 := by
        rw [div_lt_div_iff₀ (by linarith : 0 < a x + 1) (by norm_num : (0 : ℝ) < 4)]
        linarith
      dsimp only [u]
      linarith
    exact abs_lt.mpr ⟨hlower, hupper⟩
  have hmain_ev : ∀ᶠ x in atTop,
      19 / 10 ≤ u x * v x ∧
      (u x - 1) * (v x - 1) < 1 / 30 ∧
      1 ≤ u x ∧
      1 ≤ v x ∧
      |u (x + 1) - u x| < 1 / 4 := by
    filter_upwards [
      huv.eventually (Ioi_mem_nhds (by norm_num : (19 / 10 : ℝ) < 2)),
      hprod0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 30)),
      hu_ge1, hv_ge1, hu_step] with x h1 h2 h3 h4 h5
    exact ⟨le_of_lt h1, h2, h3, h4, h5⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hmain_ev
  have hgap : ∀ x ≥ X₀, u x < 4 / 3 ∨ 5 / 3 < u x := by
    intro x hx
    obtain ⟨h19, h30, _, hv1, _⟩ := hX₀ x hx
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨hge, hle⟩
    have hv_ge : 57 / 50 ≤ v x := by nlinarith
    nlinarith
  have hst : ∀ x ≥ X₀, |u (x + 1) - u x| < 1 / 4 := fun x hx => (hX₀ x hx).2.2.2.2
  rcases hgap X₀ le_rfl with h0lt | h0gt
  · left
    have hall : ∀ x ≥ X₀, u x < 4 / 3 := OMA.Narkiewicz.no_switch_lt hgap hst h0lt
    have hu1 : Tendsto u atTop (𝓝 1) := by
      have hsub0 : Tendsto (fun x => u x - 1) atTop (𝓝 0) := by
        have hup : Tendsto (fun x => (40 / 17 : ℝ) * ((u x - 1) * (v x - 1))) atTop (𝓝 0) := by
          simpa using hprod0.const_mul (40 / 17 : ℝ)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
        · filter_upwards [hu_ge1] with x hx; linarith
        · filter_upwards [eventually_ge_atTop X₀] with x hx
          obtain ⟨h19, _, hu1x, hv1x, _⟩ := hX₀ x hx
          have hult := hall x hx
          have hvge : 57 / 40 ≤ v x := by nlinarith
          nlinarith
      simpa using hsub0.add_const (1 : ℝ)
    have hv2 : Tendsto v atTop (𝓝 2) := by
      have hdiv : Tendsto (fun x => (u x * v x) / u x) atTop (𝓝 (2 / 1)) :=
        huv.div hu1 (by norm_num)
      rw [div_one] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [hu_ge1] with x hux
      have hux' : u x ≠ 0 := by linarith
      field_simp
    exact ⟨hu1, hv2⟩
  · right
    have hall : ∀ x ≥ X₀, 5 / 3 < u x := OMA.Narkiewicz.no_switch_gt hgap hst h0gt
    have hv1 : Tendsto v atTop (𝓝 1) := by
      have hsub0 : Tendsto (fun x => v x - 1) atTop (𝓝 0) := by
        have hup : Tendsto (fun x => (3 / 2 : ℝ) * ((u x - 1) * (v x - 1))) atTop (𝓝 0) := by
          simpa using hprod0.const_mul (3 / 2 : ℝ)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
        · filter_upwards [hv_ge1] with x hx; linarith
        · filter_upwards [eventually_ge_atTop X₀] with x hx
          obtain ⟨_, _, _, hv1x, _⟩ := hX₀ x hx
          have hugt := hall x hx
          nlinarith
      simpa using hsub0.add_const (1 : ℝ)
    have hu2 : Tendsto u atTop (𝓝 2) := by
      have hdiv : Tendsto (fun x => (u x * v x) / v x) atTop (𝓝 (2 / 1)) :=
        huv.div hv1 (by norm_num)
      rw [div_one] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [hv_ge1] with x hvx
      have hvx' : v x ≠ 0 := by linarith
      field_simp
    exact ⟨hv1, hu2⟩
