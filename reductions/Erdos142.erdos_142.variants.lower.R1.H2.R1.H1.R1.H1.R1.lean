import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R1 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1
-- Credit: @joshuadc11
-- uses note #172878

/-!
# Gowers U^3 reduction for four-term arithmetic progressions in ZMod p

Using Bertrand's postulate (`2N < p ≤ 4N`) and the no-wrap modular embedding, any
4-AP-free subset `S ⊆ [1, N]` embeds into a 4-AP-free subset `B ⊆ ZMod p` of the same
cardinality. Telescoping `1_B = δ + (1_B - δ)` together with the Gowers `U^3` generalized
von Neumann inequality (`H2`) forces a quantitative `U^3` lower bound on `1_B - δ` whenever
`|B| ≥ (2 p^2)^{1/3}`. The remaining core (`H1`) is the super-polylogarithmic density bound
for 4-AP-free subsets of `ZMod p` satisfying that `U^3` lower bound.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1

open Erdos142 Filter Finset Real
open scoped BigOperators

/-- A 4-AP-free subset of `ZMod p` satisfying the Gowers `U^3` lower bound from generalized
von Neumann has density at most `exp (-c * (log (log p)) ^ A)` for some `A > 1, c > 0`. -/
def H1 : Prop :=
  ∃ (A c : ℝ) (P₀ : ℕ), 1 < A ∧ 0 < c ∧ ∀ (p : ℕ) [Fact p.Prime], P₀ ≤ p →
    ∀ B : Finset (ZMod p),
      (∀ a d : ZMod p, (∀ i : Fin 4, a + (i.val : ZMod p) * d ∈ B) → d = 0) →
      (let δ : ℝ := (B.card : ℝ) / (p : ℝ)
       let f : ZMod p → ℝ := fun x => (if x ∈ B then 1 else 0) - δ
       δ ^ 32 * (p : ℝ) ^ 4 ≤ 8 ^ 8 *
         (∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
           f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
           f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃))) →
      (B.card : ℝ) ≤ (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A)

/-- Gowers `U^3` generalized von Neumann inequality for 4-term progressions in `ZMod p`:
the 8th power of the 4-AP multilinear form is controlled by the unnormalized `U^3` norm
of each of its four 1-bounded inputs. -/
def H2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    ∀ f₀ f₁ f₂ f₃ : ZMod p → ℝ,
      (∀ x, |f₀ x| ≤ 1) → (∀ x, |f₁ x| ≤ 1) → (∀ x, |f₂ x| ≤ 1) → (∀ x, |f₃ x| ≤ 1) →
        let L := ∑ x : ZMod p, ∑ d : ZMod p, f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d)
        let U := fun f : ZMod p → ℝ =>
          ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
            f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
            f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃)
        L ^ 8 ≤ (p : ℝ) ^ 12 * U f₀ ∧ L ^ 8 ≤ (p : ℝ) ^ 12 * U f₁ ∧
          L ^ 8 ≤ (p : ℝ) ^ 12 * U f₂ ∧ L ^ 8 ≤ (p : ℝ) ^ 12 * U f₃

lemma lift_midpoint {p N a b c : ℕ} (hp : 2 * N < p)
    (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (h : (a : ZMod p) + c = b + b) : a + c = b + b := by
  have h' : ((a + c : ℕ) : ZMod p) = ((b + b : ℕ) : ZMod p) := by
    simpa only [Nat.cast_add] using h
  have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h'
  rwa [Nat.mod_eq_of_lt (show a + c < p by omega),
    Nat.mod_eq_of_lt (show b + b < p by omega)] at hm

lemma lift_four {p N a b c d : ℕ} (hp : 2 * N < p)
    (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N)
    (hab : a ≠ b) (h₁ : (a : ZMod p) + c = b + b)
    (h₂ : (b : ZMod p) + d = c + c) :
    ∃ s : ℕ, 0 < s ∧
      ((b = a + s ∧ c = a + 2 * s ∧ d = a + 3 * s) ∨
       (c = d + s ∧ b = d + 2 * s ∧ a = d + 3 * s)) := by
  have e₁ := lift_midpoint hp ha hb hc h₁
  have e₂ := lift_midpoint hp hb hc hd h₂
  by_cases h : a < b
  · exact ⟨b - a, by omega, Or.inl (by omega)⟩
  · exact ⟨a - b, by omega, Or.inr (by omega)⟩

lemma embed_apFree {p N : ℕ} (hp : 2 * N < p) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N)
    (hfree : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) :
    let B := S.image (fun x : ℕ => (x : ZMod p))
    B.card = S.card ∧
      ∀ a d : ZMod p, (∀ i : Fin 4, a + (i.val : ZMod p) * d ∈ B) → d = 0 := by
  classical
  intro B
  have bound : ∀ x ∈ S, x ≤ N := fun x hx => (Finset.mem_Icc.mp (hS hx)).2
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) S := by
    intro x hx y hy he
    have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp he
    rwa [Nat.mod_eq_of_lt (by have := bound x hx; omega),
      Nat.mod_eq_of_lt (by have := bound y hy; omega)] at hm
  refine ⟨Finset.card_image_of_injOn hinj, ?_⟩
  intro a d hAP
  by_contra hd0
  obtain ⟨x₀, hx₀, hx₀e⟩ := Finset.mem_image.mp (hAP 0)
  obtain ⟨x₁, hx₁, hx₁e⟩ := Finset.mem_image.mp (hAP 1)
  obtain ⟨x₂, hx₂, hx₂e⟩ := Finset.mem_image.mp (hAP 2)
  obtain ⟨x₃, hx₃, hx₃e⟩ := Finset.mem_image.mp (hAP 3)
  have hne : x₀ ≠ x₁ := by
    rintro rfl
    have heq : a + ((0 : Fin 4).val : ZMod p) * d = a + ((1 : Fin 4).val : ZMod p) * d :=
      hx₀e.symm.trans hx₁e
    apply hd0
    simpa using heq.symm
  have hmid₁ : (x₀ : ZMod p) + x₂ = x₁ + x₁ := by
    rw [hx₀e, hx₁e, hx₂e]
    norm_num
    ring
  have hmid₂ : (x₁ : ZMod p) + x₃ = x₂ + x₂ := by
    rw [hx₁e, hx₂e, hx₃e]
    norm_num
    ring
  obtain ⟨s, hs, hcases⟩ := lift_four hp (bound x₀ hx₀) (bound x₁ hx₁) (bound x₂ hx₂)
    (bound x₃ hx₃) hne hmid₁ hmid₂
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine hfree ⟨x₀, s, hs, fun i hi => ?_⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · simpa using hx₀
    · simpa using hx₁
    · simpa using hx₂
    · simpa using hx₃
  · refine hfree ⟨x₃, s, hs, fun i hi => ?_⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · simpa using hx₃
    · simpa using hx₂
    · simpa using hx₁
    · simpa using hx₀

lemma u3_lower_of_gvn (h2 : H2) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (B : Finset (ZMod p))
    (hfree : ∀ a d : ZMod p, (∀ i : Fin 4, a + (i.val : ZMod p) * d ∈ B) → d = 0)
    (hlarge : 2 * (p : ℝ) ^ 3 * ((B.card : ℝ) / (p : ℝ)) ≤ (B.card : ℝ) ^ 4) :
    let δ : ℝ := (B.card : ℝ) / (p : ℝ)
    let f : ZMod p → ℝ := fun x => (if x ∈ B then 1 else 0) - δ
    δ ^ 32 * (p : ℝ) ^ 4 ≤ 8 ^ 8 *
      (∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
        f x * f (x + h₁) * f (x + h₂) * f (x + h₁ + h₂) *
        f (x + h₃) * f (x + h₁ + h₃) * f (x + h₂ + h₃) * f (x + h₁ + h₂ + h₃)) := by
  let δ : ℝ := (B.card : ℝ) / (p : ℝ)
  let g : ZMod p → ℝ := fun x => if x ∈ B then 1 else 0
  let c : ZMod p → ℝ := fun _ => δ
  let f : ZMod p → ℝ := fun x => g x - δ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hBcard : (B.card : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (B.card_le_univ.trans_eq (ZMod.card p))
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := (div_le_one hp0).mpr hBcard
  have hg : ∀ x, |g x| ≤ 1 := fun x => by dsimp [g]; split_ifs <;> norm_num
  have hc : ∀ x, |c x| ≤ 1 := fun _ => by dsimp [c]; rw [abs_of_nonneg hδ0]; exact hδ1
  have hf : ∀ x, |f x| ≤ 1 := fun x => by
    dsimp [f, g]
    split_ifs
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  let L : (ZMod p → ℝ) → (ZMod p → ℝ) → (ZMod p → ℝ) → (ZMod p → ℝ) → ℝ :=
    fun a₀ a₁ a₂ a₃ =>
      ∑ x : ZMod p, ∑ d : ZMod p, a₀ x * a₁ (x + d) * a₂ (x + 2 * d) * a₃ (x + 3 * d)
  let U : (ZMod p → ℝ) → ℝ := fun u =>
    ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
      u x * u (x + h₁) * u (x + h₂) * u (x + h₁ + h₂) *
      u (x + h₃) * u (x + h₁ + h₃) * u (x + h₂ + h₃) * u (x + h₁ + h₂ + h₃)
  have hΛg : L g g g g = (B.card : ℝ) := by
    dsimp [L]
    have hterm (x d : ZMod p) : g x * g (x + d) * g (x + 2 * d) * g (x + 3 * d) =
        if x ∈ B ∧ x + d ∈ B ∧ x + 2 * d ∈ B ∧ x + 3 * d ∈ B then (1 : ℝ) else 0 := by
      dsimp [g]
      by_cases h0 : x ∈ B <;> by_cases h1 : x + d ∈ B <;>
        by_cases h2 : x + 2 * d ∈ B <;> by_cases h3 : x + 3 * d ∈ B <;>
        simp [h0, h1, h2, h3]
    simp_rw [hterm]
    have hinner (x : ZMod p) :
        (∑ d : ZMod p, if x ∈ B ∧ x + d ∈ B ∧ x + 2 * d ∈ B ∧ x + 3 * d ∈ B then (1 : ℝ) else 0) =
        if x ∈ B then 1 else 0 := by
      by_cases hx : x ∈ B
      · rw [if_pos hx, Finset.sum_eq_single (0 : ZMod p)]
        · simp only [add_zero, mul_zero, and_self, if_pos hx]
        · intro d _ hd0
          rw [if_neg]
          rintro ⟨h0, h1, h2, h3⟩
          apply hd0
          apply hfree x d
          intro i
          fin_cases i <;> simpa using ‹_›
        · simp
      · rw [if_neg hx]
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [if_neg]
        exact fun h => hx h.1
    simp_rw [hinner]
    simp [Finset.sum_ite_mem]
  have hΛc : L c c c c = (p : ℝ) ^ 2 * δ ^ 4 := by
    dsimp [L, c]
    simp [ZMod.card]
    ring
  have htel : L g g g g - L c c c c =
      L f g g g + L c f g g + L c c f g + L c c c f := by
    dsimp [L]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
    dsimp [f, c]
    ring
  have hb0 : (L f g g g) ^ 8 ≤ (p : ℝ) ^ 12 * U f := (h2 p hp f g g g hf hg hg hg).1
  have hb1 : (L c f g g) ^ 8 ≤ (p : ℝ) ^ 12 * U f := (h2 p hp c f g g hc hf hg hg).2.1
  have hb2 : (L c c f g) ^ 8 ≤ (p : ℝ) ^ 12 * U f := (h2 p hp c c f g hc hc hf hg).2.2.1
  have hb3 : (L c c c f) ^ 8 ≤ (p : ℝ) ^ 12 * U f := (h2 p hp c c c f hc hc hc hf).2.2.2
  have hdiff : (p : ℝ) ^ 2 * δ ^ 4 / 2 ≤ |L g g g g - L c c c c| := by
    rw [hΛg, hΛc]
    have hle : (B.card : ℝ) ≤ (p : ℝ) ^ 2 * δ ^ 4 / 2 := by
      dsimp [δ]
      have hmul := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (p : ℝ))
      have hlhs : 2 * (p : ℝ) ^ 3 * ((B.card : ℝ) / (p : ℝ)) * (p : ℝ) ^ 2 =
          (B.card : ℝ) * 2 * (p : ℝ) ^ 4 := by
        calc 2 * (p : ℝ) ^ 3 * ((B.card : ℝ) / (p : ℝ)) * (p : ℝ) ^ 2
            = 2 * (B.card : ℝ) * (p : ℝ) ^ 4 * ((p : ℝ) * (p : ℝ)⁻¹) := by
                rw [div_eq_mul_inv]; ring
          _ = (B.card : ℝ) * 2 * (p : ℝ) ^ 4 := by
                rw [mul_inv_cancel₀ hp0.ne', mul_one]; ring
      rw [hlhs] at hmul
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), div_pow, ← mul_div_assoc,
        le_div_iff₀ (pow_pos hp0 4)]
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hmax : (p : ℝ) ^ 2 * δ ^ 4 / 8 ≤
      max (max |L f g g g| |L c f g g|) (max |L c c f g| |L c c c f|) := by
    have htri : |L g g g g - L c c c c| ≤
        |L f g g g| + |L c f g g| + |L c c f g| + |L c c c f| := by
      rw [htel]
      exact (abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    linarith [le_max_left (max |L f g g g| |L c f g g|) (max |L c c f g| |L c c c f|),
      le_max_right (max |L f g g g| |L c f g g|) (max |L c c f g| |L c c c f|),
      le_max_left |L f g g g| |L c f g g|, le_max_right |L f g g g| |L c f g g|,
      le_max_left |L c c f g| |L c c c f|, le_max_right |L c c f g| |L c c c f|]
  have hpow : ((p : ℝ) ^ 2 * δ ^ 4 / 8) ^ 8 ≤ (p : ℝ) ^ 12 * U f := by
    have hpos : (0 : ℝ) ≤ (p : ℝ) ^ 2 * δ ^ 4 / 8 :=
      div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hδ0 4)) (by norm_num)
    have hstep : ∀ t : ℝ, (p : ℝ) ^ 2 * δ ^ 4 / 8 ≤ |t| → t ^ 8 ≤ (p : ℝ) ^ 12 * U f →
        ((p : ℝ) ^ 2 * δ ^ 4 / 8) ^ 8 ≤ (p : ℝ) ^ 12 * U f := by
      intro t ht htb
      calc ((p : ℝ) ^ 2 * δ ^ 4 / 8) ^ 8 ≤ |t| ^ 8 := pow_le_pow_left₀ hpos ht 8
        _ = t ^ 8 := by rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, sq_abs, ← pow_mul]
        _ ≤ (p : ℝ) ^ 12 * U f := htb
    rcases le_max_iff.mp hmax with h1 | h2'
    · rcases le_max_iff.mp h1 with ha | hb
      · exact hstep _ ha hb0
      · exact hstep _ hb hb1
    · rcases le_max_iff.mp h2' with ha | hb
      · exact hstep _ ha hb2
      · exact hstep _ hb hb3
  have h12pos : (0 : ℝ) < (p : ℝ) ^ 12 := pow_pos hp0 12
  have hgoal : (p : ℝ) ^ 12 * (δ ^ 32 * (p : ℝ) ^ 4) ≤ (p : ℝ) ^ 12 * (8 ^ 8 * U f) := by
    calc (p : ℝ) ^ 12 * (δ ^ 32 * (p : ℝ) ^ 4)
        = 8 ^ 8 * ((p : ℝ) ^ 2 * δ ^ 4 / 8) ^ 8 := by ring
      _ ≤ 8 ^ 8 * ((p : ℝ) ^ 12 * U f) := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (p : ℝ) ^ 12 * (8 ^ 8 * U f) := by ring
  exact le_of_mul_le_mul_left hgoal h12pos

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨A, c, P₀, hA, hc, hP₀⟩ := h1
  refine ⟨A, c / 2, hA, by linarith, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hpows : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ A) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hloglog
  have hlittle : (fun x : ℝ => (3 * (c / 2)) * Real.log x ^ A) =o[atTop] (fun x => x) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop A (s := 1) zero_lt_one).const_mul_left (3 * (c / 2))
  filter_upwards [eventually_ge_atTop (max 33 P₀), hlog.eventually_ge_atTop 1,
    hloglog.eventually_ge_atTop 1,
    hpows.eventually_ge_atTop (Real.log 4 / (c / 2)),
    hlog.eventually (hlittle.def (by norm_num : (0 : ℝ) < 1 / 2)),
    hlog.eventually_ge_atTop (2 * Real.log 32)] with N hN hL1 hLL1 h4 hlit hL32
  have hN2 : 2 ≤ N := by omega
  have hNP : P₀ ≤ N := (le_max_right _ _).trans hN
  have hN33 : 33 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨S, hS, hfree, hcard⟩ :=
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.extremizer (by omega : 1 < 4) N
  obtain ⟨p, hp_prime, hp_lo, hp_hi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have hp_gt3 : 3 < p := by omega
  have hp_geP : P₀ ≤ p := hNP.trans (by omega)
  have hp_2N : 2 * N < p := hp_lo
  have hno := OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.no_positive_step (by omega : 1 < 4) hfree
  obtain ⟨hBcard, hBfree⟩ := embed_apFree hp_2N hS hno
  let B := S.image (fun x : ℕ => (x : ZMod p))
  change B.card = S.card at hBcard
  change ∀ a d : ZMod p, (∀ i : Fin 4, a + (i.val : ZMod p) * d ∈ B) → d = 0 at hBfree
  rw [← hcard, ← hBcard]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  by_cases hbig : 2 * (p : ℝ) ^ 3 * ((B.card : ℝ) / (p : ℝ)) ≤ (B.card : ℝ) ^ 4
  · have : Fact p.Prime := ⟨hp_prime⟩
    have hu3 := u3_lower_of_gvn h2 hp_gt3 B hBfree hbig
    have hbound := hP₀ p hp_geP B hBfree hu3
    have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : N ≤ p)
    have hp4N : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (by omega : p ≤ 4 * N)
    have hlog_le : Real.log (N : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hNpos hNp
    have hloglog_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (p : ℝ)) :=
      Real.log_le_log (by linarith) hlog_le
    have hpow_le : Real.log (Real.log (N : ℝ)) ^ A ≤ Real.log (Real.log (p : ℝ)) ^ A :=
      Real.rpow_le_rpow (by linarith) hloglog_le (by linarith)
    have hexp_le : Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) ≤
        Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have h4_le : (4 : ℝ) ≤ Real.exp ((c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
      rw [← Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 4)]
      rw [mul_comm]
      exact (div_le_iff₀ (by linarith : (0 : ℝ) < c / 2)).mp h4
    calc (B.card : ℝ)
        ≤ (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) := hbound
      _ ≤ (4 * (N : ℝ)) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) :=
          mul_le_mul hp4N hexp_le (Real.exp_pos _).le (by positivity)
      _ ≤ (Real.exp ((c / 2) * Real.log (Real.log (N : ℝ)) ^ A) * (N : ℝ)) *
            Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) := by
          gcongr
      _ = (N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
          rw [mul_comm _ (N : ℝ), mul_assoc, ← Real.exp_add]
          congr 2
          ring
  · push Not at hbig
    by_cases hB0 : B.card = 0
    · rw [hB0, Nat.cast_zero]
      positivity
    · have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hB0)
      have hcube : (B.card : ℝ) ^ 3 ≤ 32 * (N : ℝ) ^ 2 := by
        have h1 : 2 * (p : ℝ) ^ 3 * ((B.card : ℝ) / (p : ℝ)) = 2 * (p : ℝ) ^ 2 * (B.card : ℝ) := by
          field_simp
        rw [h1] at hbig
        have h2' : (B.card : ℝ) ^ 3 ≤ 2 * (p : ℝ) ^ 2 := by
          have : (B.card : ℝ) ^ 4 = (B.card : ℝ) ^ 3 * (B.card : ℝ) := by ring
          nlinarith
        have hp4N : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (by omega : p ≤ 4 * N)
        nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp_pos.le hp4N 2) (by norm_num : (0 : ℝ) ≤ 2)]
      have hlit' : 3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A ≤ (1 / 2) * Real.log (N : ℝ) := by
        have hL0 : 0 ≤ Real.log (N : ℝ) := by linarith
        calc 3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A
            ≤ ‖3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A‖ := Real.le_norm_self _
          _ ≤ 1 / 2 * ‖Real.log (N : ℝ)‖ := hlit
          _ = 1 / 2 * Real.log (N : ℝ) := by rw [Real.norm_of_nonneg hL0]
      have h32 : 32 ≤ (N : ℝ) * Real.exp (-3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
        have : Real.log 32 + 3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A ≤ Real.log (N : ℝ) := by
          linarith
        have hexp : 32 * Real.exp (3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A) ≤ (N : ℝ) := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 32), ← Real.exp_add]
          exact (Real.exp_le_exp.mpr this).trans_eq (Real.exp_log hNpos)
        calc (32 : ℝ)
            = (32 * Real.exp (3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A)) *
                Real.exp (-3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
              rw [mul_assoc, ← Real.exp_add]; simp
          _ ≤ (N : ℝ) * Real.exp (-3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A) :=
              mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      have hcube2 : (B.card : ℝ) ^ 3 ≤
          ((N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A)) ^ 3 := by
        calc (B.card : ℝ) ^ 3
            ≤ 32 * (N : ℝ) ^ 2 := hcube
          _ ≤ ((N : ℝ) * Real.exp (-3 * (c / 2) * Real.log (Real.log (N : ℝ)) ^ A)) * (N : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right h32 (sq_nonneg _)
          _ = (N : ℝ) ^ 3 * Real.exp (3 * (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A)) := by
              ring_nf
          _ = ((N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A)) ^ 3 := by
              rw [mul_pow, ← Real.exp_nat_mul]
              push_cast
              ring_nf
      exact (pow_le_pow_iff_left₀ hBpos.le (by positivity) (by norm_num : 3 ≠ 0)).mp hcube2

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
