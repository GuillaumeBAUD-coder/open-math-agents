import FormalConjectures.Paper.KaplanskyUInvariant

/-!
Kaplansky's proof that no field of characteristic != 2 has u-invariant 7.
-/

-- Problem: Kaplansky's problem on the values of the $u$-invariant - not seven
-- Upstream: formal-conjectures FormalConjectures/Paper/KaplanskyUInvariant.lean:163 (declaration KaplanskyUInvariant.u_invariant_values.variants.not_seven)
-- Credit: @kintonc (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.KaplanskyNotSeven

open QuadraticMap QuadraticForm

/-- If the pure 3D form <u, v, u * v> is anisotropic, then <1, u, v, u * v> is anisotropic. -/
lemma pfister2_anisotropic_of_pure {F : Type} [Field F] {u v : F} (hu : u ≠ 0)
    (hpure : (weightedSumSquares F ![u, v, u * v]).Anisotropic) :
    (weightedSumSquares F ![1, u, v, u * v]).Anisotropic := by
  have hpure' : ∀ a b c : F, u * a ^ 2 + v * b ^ 2 + u * v * c ^ 2 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c habc
    have h0 : weightedSumSquares F ![u, v, u * v] ![a, b, c] = 0 := by
      simp only [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul]
      have hw0 : ![u, v, u * v] 0 = u := rfl
      have hw1 : ![u, v, u * v] 1 = v := rfl
      have hw2 : ![u, v, u * v] 2 = u * v := rfl
      have hv0 : ![a, b, c] 0 = a := rfl
      have hv1 : ![a, b, c] 1 = b := rfl
      have hv2 : ![a, b, c] 2 = c := rfl
      rw [hw0, hw1, hw2, hv0, hv1, hv2]
      linear_combination habc
    have hvec := hpure _ h0
    exact ⟨by simpa using congr_fun hvec 0,
      by simpa using congr_fun hvec 1,
      by simpa using congr_fun hvec 2⟩
  intro x hx
  simp only [weightedSumSquares_apply, Fin.sum_univ_four, smul_eq_mul] at hx
  have hw0 : ![1, u, v, u * v] 0 = 1 := rfl
  have hw1 : ![1, u, v, u * v] 1 = u := rfl
  have hw2 : ![1, u, v, u * v] 2 = v := rfl
  have hw3 : ![1, u, v, u * v] 3 = u * v := rfl
  rw [hw0, hw1, hw2, hw3] at hx
  set w := x 0
  set t₁ := x 1
  set t₂ := x 2
  set t₃ := x 3
  have heq : w ^ 2 + u * t₁ ^ 2 + v * t₂ ^ 2 + u * v * t₃ ^ 2 = 0 := by
    linear_combination hx
  by_cases hN : w ^ 2 + u * t₁ ^ 2 = 0
  · have h1 : u * 0 ^ 2 + v * t₂ ^ 2 + u * v * t₃ ^ 2 = 0 := by
      linear_combination heq - hN
    obtain ⟨-, ht₂, ht₃⟩ := hpure' 0 t₂ t₃ h1
    have h2 : u * 0 ^ 2 + v * (u * t₁) ^ 2 + u * v * w ^ 2 = 0 := by
      linear_combination u * v * hN
    obtain ⟨-, hut₁, hw⟩ := hpure' 0 (u * t₁) w h2
    have ht₁ : t₁ = 0 := (mul_eq_zero.mp hut₁).resolve_left hu
    funext i
    fin_cases i
    · exact hw
    · exact ht₁
    · exact ht₂
    · exact ht₃
  · exfalso
    have h3 : u * (w ^ 2 + u * t₁ ^ 2) ^ 2 + v * (u * t₁ * t₂ - u * w * t₃) ^ 2 +
        u * v * (u * t₁ * t₃ + w * t₂) ^ 2 = 0 := by
      linear_combination u * (w ^ 2 + u * t₁ ^ 2) * heq
    obtain ⟨hzero, -, -⟩ := hpure' _ _ _ h3
    exact hN hzero

/-- Quaternion multiplication on Fin 4 -> F for norm form <1, u, v, u * v>. -/
def qMul {F : Type} [CommRing F] (u v : F) (p q : Fin 4 → F) : Fin 4 → F :=
  ![p 0 * q 0 - u * p 1 * q 1 - v * p 2 * q 2 - u * v * p 3 * q 3,
    p 0 * q 1 + p 1 * q 0 + v * (p 2 * q 3 - p 3 * q 2),
    p 0 * q 2 + p 2 * q 0 + u * (p 3 * q 1 - p 1 * q 3),
    p 0 * q 3 + p 3 * q 0 + p 1 * q 2 - p 2 * q 1]

lemma qMul_norm {F : Type} [CommRing F] (u v : F) (p q : Fin 4 → F) :
    weightedSumSquares F ![1, u, v, u * v] (qMul u v p q) =
      weightedSumSquares F ![1, u, v, u * v] p *
        weightedSumSquares F ![1, u, v, u * v] q := by
  simp only [weightedSumSquares_apply, Fin.sum_univ_four, smul_eq_mul]
  have hw0 : ![1, u, v, u * v] 0 = 1 := rfl
  have hw1 : ![1, u, v, u * v] 1 = u := rfl
  have hw2 : ![1, u, v, u * v] 2 = v := rfl
  have hw3 : ![1, u, v, u * v] 3 = u * v := rfl
  have hq0 : qMul u v p q 0 =
      p 0 * q 0 - u * p 1 * q 1 - v * p 2 * q 2 - u * v * p 3 * q 3 := rfl
  have hq1 : qMul u v p q 1 = p 0 * q 1 + p 1 * q 0 + v * (p 2 * q 3 - p 3 * q 2) := rfl
  have hq2 : qMul u v p q 2 = p 0 * q 2 + p 2 * q 0 + u * (p 3 * q 1 - p 1 * q 3) := rfl
  have hq3 : qMul u v p q 3 = p 0 * q 3 + p 3 * q 0 + p 1 * q 2 - p 2 * q 1 := rfl
  rw [hw0, hw1, hw2, hw3, hq0, hq1, hq2, hq3]
  ring

def qMulLin {F : Type} [CommRing F] (u v : F) (p : Fin 4 → F) :
    (Fin 4 → F) →ₗ[F] (Fin 4 → F) where
  toFun := qMul u v p
  map_add' q r := by
    funext i
    fin_cases i <;>
    · dsimp [qMul, Pi.add_apply]
      ring
  map_smul' a q := by
    funext i
    fin_cases i <;>
    · dsimp [qMul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

noncomputable def qMulEquiv {F : Type} [Field F] (u v : F) (p : Fin 4 → F)
    (haniso : (weightedSumSquares F ![1, u, v, u * v]).Anisotropic)
    (hp : weightedSumSquares F ![1, u, v, u * v] p ≠ 0) :
    (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) :=
  LinearEquiv.ofInjectiveEndo (qMulLin u v p) (by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have hn : weightedSumSquares F ![1, u, v, u * v] p *
        weightedSumSquares F ![1, u, v, u * v] q = 0 := by
      rw [← qMul_norm]
      change weightedSumSquares F ![1, u, v, u * v] (qMulLin u v p q) = 0
      rw [hq, map_zero]
    exact haniso q ((mul_eq_zero.mp hn).resolve_left hp))

/-- Every nonzero element of F is represented by an anisotropic 2-fold Pfister form when 8 not in anisotropicDims F. -/
lemma pfister2_universal {F : Type} [Field F] [NeZero (2 : F)] {u v : F}
    (haniso : (weightedSumSquares F ![1, u, v, u * v]).Anisotropic)
    (h8 : ¬ (8 ∈ anisotropicDims F)) {r : F} (hr : r ≠ 0) :
    ∃ p : Fin 4 → F, weightedSumSquares F ![1, u, v, u * v] p = r := by
  let w₈ : Fin 8 → F := ![1, u, v, u * v, -r, -r * u, -r * v, -r * u * v]
  have ⟨z, hz_ne, hz_eq⟩ : ∃ z : Fin 8 → F, z ≠ 0 ∧ weightedSumSquares F w₈ z = 0 := by
    by_contra h
    push Not at h
    exact h8 (mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F w₈,
      fun x hx => by_contra fun hx0 => h x hx0 hx⟩)
  let z_top : Fin 4 → F := ![z 0, z 1, z 2, z 3]
  let z_bot : Fin 4 → F := ![z 4, z 5, z 6, z 7]
  have hsplit : weightedSumSquares F ![1, u, v, u * v] z_top =
      r * weightedSumSquares F ![1, u, v, u * v] z_bot := by
    simp only [weightedSumSquares_apply, Fin.sum_univ_eight, Fin.sum_univ_four, smul_eq_mul] at hz_eq ⊢
    have h0 : w₈ 0 = 1 := rfl
    have h1 : w₈ 1 = u := rfl
    have h2 : w₈ 2 = v := rfl
    have h3 : w₈ 3 = u * v := rfl
    have h4 : w₈ 4 = -r := rfl
    have h5 : w₈ 5 = -r * u := rfl
    have h6 : w₈ 6 = -r * v := rfl
    have h7 : w₈ 7 = -r * u * v := rfl
    have hw0 : ![1, u, v, u * v] 0 = 1 := rfl
    have hw1 : ![1, u, v, u * v] 1 = u := rfl
    have hw2 : ![1, u, v, u * v] 2 = v := rfl
    have hw3 : ![1, u, v, u * v] 3 = u * v := rfl
    have ht0 : z_top 0 = z 0 := rfl
    have ht1 : z_top 1 = z 1 := rfl
    have ht2 : z_top 2 = z 2 := rfl
    have ht3 : z_top 3 = z 3 := rfl
    have hb0 : z_bot 0 = z 4 := rfl
    have hb1 : z_bot 1 = z 5 := rfl
    have hb2 : z_bot 2 = z 6 := rfl
    have hb3 : z_bot 3 = z 7 := rfl
    rw [h0, h1, h2, h3, h4, h5, h6, h7] at hz_eq
    rw [hw0, hw1, hw2, hw3, ht0, ht1, ht2, ht3, hb0, hb1, hb2, hb3]
    linear_combination hz_eq
  have hbot_ne : weightedSumSquares F ![1, u, v, u * v] z_bot ≠ 0 := by
    intro hbot0
    have htop0 : weightedSumSquares F ![1, u, v, u * v] z_top = 0 := by
      rw [hsplit, hbot0, mul_zero]
    have hbot_z := haniso z_bot hbot0
    have htop_z := haniso z_top htop0
    apply hz_ne
    funext i
    fin_cases i
    · exact by simpa [z_top] using congr_fun htop_z 0
    · exact by simpa [z_top] using congr_fun htop_z 1
    · exact by simpa [z_top] using congr_fun htop_z 2
    · exact by simpa [z_top] using congr_fun htop_z 3
    · exact by simpa [z_bot] using congr_fun hbot_z 0
    · exact by simpa [z_bot] using congr_fun hbot_z 1
    · exact by simpa [z_bot] using congr_fun hbot_z 2
    · exact by simpa [z_bot] using congr_fun hbot_z 3
  refine ⟨(weightedSumSquares F ![1, u, v, u * v] z_bot)⁻¹ • qMul u v z_top z_bot, ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, qMul_norm, hsplit]
  field_simp [hbot_ne]

/-- Witt cancellation of a single nonzero diagonal entry c. -/
lemma witt_cancel_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    {c : F} (hc : c ≠ 0) (w₁ w₂ : Fin n → F)
    (f : (Fin (n + 1) → F) ≃ₗ[F] (Fin (n + 1) → F))
    (hf : ∀ x, weightedSumSquares F (Fin.cons c w₂) (f x) =
      weightedSumSquares F (Fin.cons c w₁) x) :
    ∃ g : (Fin n → F) ≃ₗ[F] (Fin n → F),
      ∀ y, weightedSumSquares F w₂ (g y) = weightedSumSquares F w₁ y := by
  let v₁ : Fin (n + 1) → F := Fin.cons c w₁
  let v₂ : Fin (n + 1) → F := Fin.cons c w₂
  let Q₁ := weightedSumSquares F v₁
  let Q₂ := weightedSumSquares F v₂
  let B₁ (a b : Fin (n + 1) → F) : F := ∑ i : Fin (n + 1), v₁ i * a i * b i
  let B₂ (a b : Fin (n + 1) → F) : F := ∑ i : Fin (n + 1), v₂ i * a i * b i
  have hQ₁_add : ∀ a b, Q₁ (a + b) = Q₁ a + 2 * B₁ a b + Q₁ b := by
    intro a b
    simp only [Q₁, B₁, weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hQ₂_add : ∀ a b, Q₂ (a + b) = Q₂ a + 2 * B₂ a b + Q₂ b := by
    intro a b
    simp only [Q₂, B₂, weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hQ₂_sub : ∀ a b, Q₂ (a - b) = Q₂ a - 2 * B₂ a b + Q₂ b := by
    intro a b
    simp only [Q₂, B₂, weightedSumSquares_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  let e₀ : Fin (n + 1) → F := Pi.single 0 1
  have hQ₁e₀ : Q₁ e₀ = c := by
    simp [Q₁, v₁, weightedSumSquares_apply, e₀, Pi.single_apply]
  have hQ₂e₀ : Q₂ e₀ = c := by
    simp [Q₂, v₂, weightedSumSquares_apply, e₀, Pi.single_apply]
  let v := f e₀
  have hQ₂v : Q₂ v = c := (hf e₀).trans hQ₁e₀
  have hsum4 : Q₂ (v - e₀) + Q₂ (v + e₀) = 4 * c := by
    rw [hQ₂_sub, hQ₂_add, hQ₂v, hQ₂e₀]
    ring
  have h4c : (4 : F) * c ≠ 0 := by
    have h4 : (4 : F) = 2 * 2 := by ring
    rw [h4]
    exact mul_ne_zero (mul_ne_zero h2 h2) hc
  have hex_u : ∃ u : Fin (n + 1) → F, Q₂ u ≠ 0 ∧
      ((u = v - e₀) ∨ (u = v + e₀)) := by
    by_cases h1 : Q₂ (v - e₀) ≠ 0
    · exact ⟨v - e₀, h1, Or.inl rfl⟩
    · push Not at h1
      refine ⟨v + e₀, ?_, Or.inr rfl⟩
      intro h2'
      rw [h1, h2', zero_add] at hsum4
      exact h4c hsum4.symm
  obtain ⟨u, hu_ne, hu_eq⟩ := hex_u
  let reflFun : (Fin (n + 1) → F) → (Fin (n + 1) → F) :=
    fun x => x - (2 * B₂ u x / Q₂ u) • u
  have hB₂_add : ∀ a b, B₂ u (a + b) = B₂ u a + B₂ u b := fun a b => by
    simp only [B₂, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hB₂_smul : ∀ s : F, ∀ a, B₂ u (s • a) = s * B₂ u a := fun s a => by
    simp only [B₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hB₂_uu : B₂ u u = Q₂ u := by
    simp only [B₂, Q₂, weightedSumSquares_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  let hrefl_lin : (Fin (n + 1) → F) →ₗ[F] (Fin (n + 1) → F) :=
    { toFun := reflFun
      map_add' := fun a b => by
        simp only [reflFun, hB₂_add, mul_add, add_div, add_smul]
        abel
      map_smul' := fun s a => by
        simp only [reflFun, RingHom.id_apply, hB₂_smul, smul_sub, smul_smul]
        congr 2
        ring }
  have hrefl_Q₂ : ∀ x, Q₂ (hrefl_lin x) = Q₂ x := by
    intro x
    change Q₂ (x - (2 * B₂ u x / Q₂ u) • u) = Q₂ x
    rw [hQ₂_sub]
    have hB : B₂ x ((2 * B₂ u x / Q₂ u) • u) = (2 * B₂ u x / Q₂ u) * B₂ u x := by
      simp only [B₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hQu : Q₂ ((2 * B₂ u x / Q₂ u) • u) = (2 * B₂ u x / Q₂ u) ^ 2 * Q₂ u := by
      simp only [Q₂, weightedSumSquares_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hB, hQu]
    field_simp [hu_ne]
    ring
  have hrefl_inj : Function.Injective hrefl_lin := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hB0 : B₂ u (hrefl_lin x) = 0 := by
      rw [hx]
      simp [B₂]
    have hBx : B₂ u (hrefl_lin x) = -B₂ u x := by
      change B₂ u (x - (2 * B₂ u x / Q₂ u) • u) = -B₂ u x
      have hsub : x - (2 * B₂ u x / Q₂ u) • u = x + (-(2 * B₂ u x / Q₂ u)) • u := by
        simp [sub_eq_add_neg, neg_smul]
      rw [hsub, hB₂_add, hB₂_smul, hB₂_uu]
      field_simp [hu_ne]
      ring
    rw [hBx] at hB0
    have hBx0 : B₂ u x = 0 := neg_eq_zero.mp hB0
    have h0 : x - (2 * B₂ u x / Q₂ u) • u = 0 := hx
    rw [hBx0, mul_zero, zero_div, zero_smul, sub_zero] at h0
    exact h0
  let rEquiv := LinearEquiv.ofInjectiveEndo hrefl_lin hrefl_inj
  have hex_k : ∃ k : (Fin (n + 1) → F) ≃ₗ[F] (Fin (n + 1) → F),
      (∀ x, Q₂ (k x) = Q₁ x) ∧ k e₀ = e₀ := by
    rcases hu_eq with rfl | rfl
    · refine ⟨f.trans rEquiv, fun x => (hrefl_Q₂ (f x)).trans (hf x), ?_⟩
      change hrefl_lin v = e₀
      have hBuv : 2 * B₂ (v - e₀) v = Q₂ (v - e₀) := by
        have h1 : Q₂ (v - e₀) = Q₂ v - 2 * B₂ v e₀ + Q₂ e₀ := hQ₂_sub v e₀
        have h2' : B₂ (v - e₀) v = Q₂ v - B₂ v e₀ := by
          simp only [B₂, Q₂, weightedSumSquares_apply, Pi.sub_apply, smul_eq_mul]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [h2', h1, hQ₂v, hQ₂e₀]
        ring
      change v - (2 * B₂ (v - e₀) v / Q₂ (v - e₀)) • (v - e₀) = e₀
      rw [hBuv, div_self hu_ne, one_smul]
      abel
    · let negEquiv : (Fin (n + 1) → F) ≃ₗ[F] (Fin (n + 1) → F) :=
        { toFun := fun x => -x
          invFun := fun x => -x
          left_inv := neg_neg
          right_inv := neg_neg
          map_add' := neg_add
          map_smul' := fun s x => by simp }
      refine ⟨f.trans (rEquiv.trans negEquiv),
        fun x => ?_, ?_⟩
      · change Q₂ (-(hrefl_lin (f x))) = Q₁ x
        have hneg : ∀ y, Q₂ (-y) = Q₂ y := fun y => by
          simp [Q₂, weightedSumSquares_apply]
        rw [hneg, hrefl_Q₂, hf]
      · change -(hrefl_lin v) = e₀
        have hBuv : 2 * B₂ (v + e₀) v = Q₂ (v + e₀) := by
          have h1 : Q₂ (v + e₀) = Q₂ v + 2 * B₂ v e₀ + Q₂ e₀ := hQ₂_add v e₀
          have h2' : B₂ (v + e₀) v = Q₂ v + B₂ v e₀ := by
            simp only [B₂, Q₂, weightedSumSquares_apply, Pi.add_apply, smul_eq_mul]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [h2', h1, hQ₂v, hQ₂e₀]
          ring
        change -(v - (2 * B₂ (v + e₀) v / Q₂ (v + e₀)) • (v + e₀)) = e₀
        rw [hBuv, div_self hu_ne, one_smul]
        abel
  obtain ⟨k, hkQ, hke₀⟩ := hex_k
  have hk_zero : ∀ y : Fin n → F, k (Fin.cons 0 y) 0 = 0 := by
    intro y
    have hpol : 2 * B₂ (k e₀) (k (Fin.cons 0 y)) = 2 * B₁ e₀ (Fin.cons 0 y) := by
      have hL : Q₂ (k (e₀ + Fin.cons 0 y)) = Q₂ (k e₀) + 2 * B₂ (k e₀) (k (Fin.cons 0 y)) +
          Q₂ (k (Fin.cons 0 y)) := by
        rw [map_add, hQ₂_add]
      have hR : Q₁ (e₀ + Fin.cons 0 y) = Q₁ e₀ + 2 * B₁ e₀ (Fin.cons 0 y) +
          Q₁ (Fin.cons 0 y) := hQ₁_add e₀ (Fin.cons 0 y)
      rw [hkQ, hkQ, hkQ] at hL
      rw [hL] at hR
      linear_combination hR
    have hB₁_0 : B₁ e₀ (Fin.cons 0 y) = 0 := by
      simp only [B₁, e₀]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        simp [hi]
      · intro h0
        exact absurd (Finset.mem_univ 0) h0
    have hB₂_0 : B₂ e₀ (k (Fin.cons 0 y)) = c * k (Fin.cons 0 y) 0 := by
      simp only [B₂, e₀]
      rw [Finset.sum_eq_single 0]
      · simp [v₂]
      · intro i _ hi
        simp [hi]
      · intro h0
        exact absurd (Finset.mem_univ 0) h0
    rw [hke₀, hB₂_0, hB₁_0, mul_zero] at hpol
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hpol).resolve_left h2)).resolve_left hc
  let g_lin : (Fin n → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun y => Fin.tail (k (Fin.cons 0 y))
      map_add' := fun y₁ y₂ => by
        have hcons : (Fin.cons (0 : F) (y₁ + y₂) : Fin (n + 1) → F) =
            (Fin.cons (0 : F) y₁ : Fin (n + 1) → F) +
            (Fin.cons (0 : F) y₂ : Fin (n + 1) → F) := by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp
        rw [hcons, map_add]
        rfl
      map_smul' := fun a y => by
        have hcons : (Fin.cons (0 : F) (a • y) : Fin (n + 1) → F) =
            a • (Fin.cons (0 : F) y : Fin (n + 1) → F) := by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp
        rw [hcons, map_smul]
        rfl }
  have hg_Q : ∀ y, weightedSumSquares F w₂ (g_lin y) = weightedSumSquares F w₁ y := by
    intro y
    have hcons : Fin.cons (0 : F) (g_lin y) = k (Fin.cons 0 y) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · exact (hk_zero y).symm
      · intro j
        rfl
    have hQ₂_cons : Q₂ (Fin.cons 0 (g_lin y)) = weightedSumSquares F w₂ (g_lin y) := by
      simp only [Q₂, v₂, weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul,
        Fin.cons_zero, Fin.cons_succ]
      ring
    have hQ₁_cons : Q₁ (Fin.cons 0 y) = weightedSumSquares F w₁ y := by
      simp only [Q₁, v₁, weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul,
        Fin.cons_zero, Fin.cons_succ]
      ring
    rw [← hQ₂_cons, hcons, hkQ, hQ₁_cons]
  have hg_inj : Function.Injective g_lin := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hcons : k (Fin.cons 0 y) = 0 := by
      funext i
      refine Fin.cases (hk_zero y) ?_ i
      intro j
      exact congr_fun hy j
    have hy0 : Fin.cons (0 : F) y = 0 := k.injective (hcons.trans (map_zero k).symm)
    funext j
    exact congr_fun hy0 j.succ
  exact ⟨LinearEquiv.ofInjectiveEndo g_lin hg_inj, hg_Q⟩

def pack8 {F : Type} (q₁ q₂ : Fin 4 → F) : Fin 8 → F
  | 0 => q₁ 0
  | 1 => q₂ 0
  | 2 => q₁ 1
  | 3 => q₁ 2
  | 4 => q₁ 3
  | 5 => q₂ 1
  | 6 => q₂ 2
  | 7 => q₂ 3

lemma step6_equiv {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {a b x y r : F} (hr : r ≠ 0)
    (hρ₁ : (weightedSumSquares F ![1, a, b, a * b]).Anisotropic)
    (hρ₂ : (weightedSumSquares F ![1, x, y, x * y]).Anisotropic)
    {p₁ p₂ : Fin 4 → F}
    (hp₁ : weightedSumSquares F ![1, a, b, a * b] p₁ = r)
    (hp₂ : weightedSumSquares F ![1, x, y, x * y] p₂ = r) :
    ∃ f₈ : (Fin 8 → F) ≃ₗ[F] (Fin 8 → F), ∀ z,
      weightedSumSquares F (Fin.cons 1 (Fin.cons (-1) ![a, b, a * b, -x, -y, -(x * y)])) (f₈ z) =
      weightedSumSquares F
        (Fin.cons 1 (Fin.cons (-1) (fun i => r * ![a, b, a * b, -x, -y, -(x * y)] i))) z := by
  have hp₁_ne : weightedSumSquares F ![1, a, b, a * b] p₁ ≠ 0 := by rw [hp₁]; exact hr
  have hp₂_ne : weightedSumSquares F ![1, x, y, x * y] p₂ ≠ 0 := by rw [hp₂]; exact hr
  let eq₁ := qMulEquiv a b p₁ hρ₁ hp₁_ne
  let eq₂ := qMulEquiv x y p₂ hρ₂ hp₂_ne
  let w_α : Fin 6 → F := ![a, b, a * b, -x, -y, -(x * y)]
  let w_left : Fin 8 → F := Fin.cons 1 (Fin.cons (-1) (fun i => r * w_α i))
  let w_right : Fin 8 → F := Fin.cons 1 (Fin.cons (-1) w_α)
  let c₁ := (1 / r + 1) / 2
  let c₂ := (1 / r - 1) / 2
  let f₈_lin : (Fin 8 → F) →ₗ[F] (Fin 8 → F) :=
    { toFun := fun z =>
        let s' := c₁ * z 0 + c₂ * z 1
        let t' := c₂ * z 0 + c₁ * z 1
        let q₁ := qMul a b p₁ ![s', z 2, z 3, z 4]
        let q₂ := qMul x y p₂ ![t', z 5, z 6, z 7]
        pack8 q₁ q₂
      map_add' := fun z₁ z₂ => by
        have hs1 : ![c₁ * (z₁ + z₂) 0 + c₂ * (z₁ + z₂) 1, (z₁ + z₂) 2, (z₁ + z₂) 3, (z₁ + z₂) 4] =
            ![c₁ * z₁ 0 + c₂ * z₁ 1, z₁ 2, z₁ 3, z₁ 4] +
            ![c₁ * z₂ 0 + c₂ * z₂ 1, z₂ 2, z₂ 3, z₂ 4] := by
          funext i; fin_cases i <;> simp [Pi.add_apply]; ring
        have ht1 : ![c₂ * (z₁ + z₂) 0 + c₁ * (z₁ + z₂) 1, (z₁ + z₂) 5, (z₁ + z₂) 6, (z₁ + z₂) 7] =
            ![c₂ * z₁ 0 + c₁ * z₁ 1, z₁ 5, z₁ 6, z₁ 7] +
            ![c₂ * z₂ 0 + c₁ * z₂ 1, z₂ 5, z₂ 6, z₂ 7] := by
          funext i; fin_cases i <;> simp [Pi.add_apply]; ring
        dsimp only
        change pack8 (eq₁ _) (eq₂ _) = _
        rw [hs1, ht1, map_add, map_add]
        funext i; fin_cases i <;> rfl
      map_smul' := fun k z => by
        have hs1 : ![c₁ * (k • z) 0 + c₂ * (k • z) 1, (k • z) 2, (k • z) 3, (k • z) 4] =
            k • ![c₁ * z 0 + c₂ * z 1, z 2, z 3, z 4] := by
          funext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]; ring
        have ht1 : ![c₂ * (k • z) 0 + c₁ * (k • z) 1, (k • z) 5, (k • z) 6, (k • z) 7] =
            k • ![c₂ * z 0 + c₁ * z 1, z 5, z 6, z 7] := by
          funext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]; ring
        dsimp only
        change pack8 (eq₁ _) (eq₂ _) = _
        rw [RingHom.id_apply, hs1, ht1, map_smul, map_smul]
        funext i; fin_cases i <;> rfl }
  have hf₈_Q : ∀ z, weightedSumSquares F w_right (f₈_lin z) =
      weightedSumSquares F w_left z := by
    intro z
    let s' := c₁ * z 0 + c₂ * z 1
    let t' := c₂ * z 0 + c₁ * z 1
    let v₁ : Fin 4 → F := ![s', z 2, z 3, z 4]
    let v₂ : Fin 4 → F := ![t', z 5, z 6, z 7]
    let q₁ := qMul a b p₁ v₁
    let q₂ := qMul x y p₂ v₂
    have hq₁ : weightedSumSquares F ![1, a, b, a * b] q₁ =
        r * weightedSumSquares F ![1, a, b, a * b] v₁ := by
      rw [qMul_norm, hp₁]
    have hq₂ : weightedSumSquares F ![1, x, y, x * y] q₂ =
        r * weightedSumSquares F ![1, x, y, x * y] v₂ := by
      rw [qMul_norm, hp₂]
    have h22 : r * (s' ^ 2 - t' ^ 2) = z 0 ^ 2 - z 1 ^ 2 := by
      simp only [s', t', c₁, c₂]
      field_simp [h2, hr]
      ring
    simp only [weightedSumSquares_apply, Fin.sum_univ_eight, Fin.sum_univ_four, smul_eq_mul]
      at hq₁ hq₂ ⊢
    have hwr0 : w_right 0 = 1 := rfl
    have hwr1 : w_right 1 = -1 := rfl
    have hwr2 : w_right 2 = a := rfl
    have hwr3 : w_right 3 = b := rfl
    have hwr4 : w_right 4 = a * b := rfl
    have hwr5 : w_right 5 = -x := rfl
    have hwr6 : w_right 6 = -y := rfl
    have hwr7 : w_right 7 = -(x * y) := rfl
    have hwl0 : w_left 0 = 1 := rfl
    have hwl1 : w_left 1 = -1 := rfl
    have hwl2 : w_left 2 = r * a := rfl
    have hwl3 : w_left 3 = r * b := rfl
    have hwl4 : w_left 4 = r * (a * b) := rfl
    have hwl5 : w_left 5 = r * -x := rfl
    have hwl6 : w_left 6 = r * -y := rfl
    have hwl7 : w_left 7 = r * -(x * y) := rfl
    have hf0 : f₈_lin z 0 = q₁ 0 := rfl
    have hf1 : f₈_lin z 1 = q₂ 0 := rfl
    have hf2 : f₈_lin z 2 = q₁ 1 := rfl
    have hf3 : f₈_lin z 3 = q₁ 2 := rfl
    have hf4 : f₈_lin z 4 = q₁ 3 := rfl
    have hf5 : f₈_lin z 5 = q₂ 1 := rfl
    have hf6 : f₈_lin z 6 = q₂ 2 := rfl
    have hf7 : f₈_lin z 7 = q₂ 3 := rfl
    have ha0 : ![1, a, b, a * b] 0 = 1 := rfl
    have ha1 : ![1, a, b, a * b] 1 = a := rfl
    have ha2 : ![1, a, b, a * b] 2 = b := rfl
    have ha3 : ![1, a, b, a * b] 3 = a * b := rfl
    have hx0 : ![1, x, y, x * y] 0 = 1 := rfl
    have hx1 : ![1, x, y, x * y] 1 = x := rfl
    have hx2 : ![1, x, y, x * y] 2 = y := rfl
    have hx3 : ![1, x, y, x * y] 3 = x * y := rfl
    have hv10 : v₁ 0 = s' := rfl
    have hv11 : v₁ 1 = z 2 := rfl
    have hv12 : v₁ 2 = z 3 := rfl
    have hv13 : v₁ 3 = z 4 := rfl
    have hv20 : v₂ 0 = t' := rfl
    have hv21 : v₂ 1 = z 5 := rfl
    have hv22 : v₂ 2 = z 6 := rfl
    have hv23 : v₂ 3 = z 7 := rfl
    rw [ha0, ha1, ha2, ha3, hv10, hv11, hv12, hv13] at hq₁
    rw [hx0, hx1, hx2, hx3, hv20, hv21, hv22, hv23] at hq₂
    rw [hwr0, hwr1, hwr2, hwr3, hwr4, hwr5, hwr6, hwr7,
      hwl0, hwl1, hwl2, hwl3, hwl4, hwl5, hwl6, hwl7,
      hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]
    linear_combination hq₁ - hq₂ + h22
  have hf₈_inj : Function.Injective f₈_lin := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    let s' := c₁ * z 0 + c₂ * z 1
    let t' := c₂ * z 0 + c₁ * z 1
    have hq₁0 : qMul a b p₁ ![s', z 2, z 3, z 4] = 0 := by
      have hz0 : f₈_lin z 0 = 0 := congr_fun hz 0
      have hz2 : f₈_lin z 2 = 0 := congr_fun hz 2
      have hz3 : f₈_lin z 3 = 0 := congr_fun hz 3
      have hz4 : f₈_lin z 4 = 0 := congr_fun hz 4
      funext i; fin_cases i
      · exact hz0
      · exact hz2
      · exact hz3
      · exact hz4
    have hq₂0 : qMul x y p₂ ![t', z 5, z 6, z 7] = 0 := by
      have hz1 : f₈_lin z 1 = 0 := congr_fun hz 1
      have hz5 : f₈_lin z 5 = 0 := congr_fun hz 5
      have hz6 : f₈_lin z 6 = 0 := congr_fun hz 6
      have hz7 : f₈_lin z 7 = 0 := congr_fun hz 7
      funext i; fin_cases i
      · exact hz1
      · exact hz5
      · exact hz6
      · exact hz7
    have hv₁0 : ![s', z 2, z 3, z 4] = 0 :=
      eq₁.injective (by change qMul a b p₁ ![s', z 2, z 3, z 4] = eq₁ 0; rw [hq₁0, map_zero])
    have hv₂0 : ![t', z 5, z 6, z 7] = 0 :=
      eq₂.injective (by change qMul x y p₂ ![t', z 5, z 6, z 7] = eq₂ 0; rw [hq₂0, map_zero])
    have hs'0 : s' = 0 := by simpa using congr_fun hv₁0 0
    have ht'0 : t' = 0 := by simpa using congr_fun hv₂0 0
    have hz0 : z 0 = 0 := by
      have h : z 0 = (r * (s' + t') + (s' - t')) / 2 := by
        simp only [s', t', c₁, c₂]
        field_simp [h2, hr]
        ring
      rw [hs'0, ht'0] at h
      simpa using h
    have hz1 : z 1 = 0 := by
      have h : z 1 = (r * (s' + t') - (s' - t')) / 2 := by
        simp only [s', t', c₁, c₂]
        field_simp [h2, hr]
        ring
      rw [hs'0, ht'0] at h
      simpa using h
    have hz2 : z 2 = 0 := congr_fun hv₁0 1
    have hz3 : z 3 = 0 := congr_fun hv₁0 2
    have hz4 : z 4 = 0 := congr_fun hv₁0 3
    have hz5 : z 5 = 0 := congr_fun hv₂0 1
    have hz6 : z 6 = 0 := congr_fun hv₂0 2
    have hz7 : z 7 = 0 := congr_fun hv₂0 3
    funext i
    match i with
    | 0 => exact hz0
    | 1 => exact hz1
    | 2 => exact hz2
    | 3 => exact hz3
    | 4 => exact hz4
    | 5 => exact hz5
    | 6 => exact hz6
    | 7 => exact hz7
  exact ⟨LinearEquiv.ofInjectiveEndo f₈_lin hf₈_inj, hf₈_Q⟩

lemma step6_contradiction {F : Type} [Field F] [NeZero (2 : F)] (h2 : (2 : F) ≠ 0)
    (h8_not : ¬ (8 ∈ anisotropicDims F)) {e₇ a b x y : F} (he₇ : e₇ ≠ 0) (ha : a ≠ 0)
    (hQ₇_aniso : (weightedSumSquares F ![e₇, a, b, a * b, -x, -y, -(x * y)]).Anisotropic)
    (hρ₁ : (weightedSumSquares F ![1, a, b, a * b]).Anisotropic)
    (hρ₂ : (weightedSumSquares F ![1, x, y, x * y]).Anisotropic) : False := by
  let r := -e₇ / a
  have hr : r ≠ 0 := div_ne_zero (neg_ne_zero.mpr he₇) ha
  obtain ⟨p₁, hp₁⟩ := pfister2_universal hρ₁ h8_not hr
  obtain ⟨p₂, hp₂⟩ := pfister2_universal hρ₂ h8_not hr
  let w_α : Fin 6 → F := ![a, b, a * b, -x, -y, -(x * y)]
  obtain ⟨f₈, hf₈_Q⟩ := step6_equiv h2 hr hρ₁ hρ₂ hp₁ hp₂
  obtain ⟨f₇, hf₇⟩ := witt_cancel_one h2 one_ne_zero
    (Fin.cons (-1) (fun i => r * w_α i)) (Fin.cons (-1) w_α) f₈ hf₈_Q
  obtain ⟨g, hg⟩ := witt_cancel_one h2 (neg_ne_zero.mpr one_ne_zero)
    (fun i => r * w_α i) w_α f₇ hf₇
  let z₀ : Fin 6 → F := Pi.single 0 1
  have hg_val : weightedSumSquares F w_α (g z₀) = -e₇ := by
    rw [hg z₀]
    have hmul : weightedSumSquares F (fun i => r * w_α i) z₀ = r * a := by
      simp only [weightedSumSquares_apply, z₀]
      rw [Finset.sum_eq_single 0]
      · simp [w_α]
      · intro i _ hi; simp [hi]
      · intro h0; exact absurd (Finset.mem_univ 0) h0
    rw [hmul]
    simp only [r]
    field_simp [ha]
  let v₇ : Fin 7 → F := Fin.cons 1 (g z₀)
  have hv₇_ne : v₇ ≠ 0 := by
    intro h0
    have h0' : (1 : F) = 0 := congr_fun h0 0
    exact one_ne_zero h0'
  have hv₇_eq : weightedSumSquares F ![e₇, a, b, a * b, -x, -y, -(x * y)] v₇ = 0 := by
    have hQ₇_cons : weightedSumSquares F ![e₇, a, b, a * b, -x, -y, -(x * y)] v₇ =
        e₇ * 1 ^ 2 + weightedSumSquares F w_α (g z₀) := by
      simp only [weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul, v₇,
        Fin.cons_zero, Fin.cons_succ]
      have hsucc : ∀ i : Fin 6, ![e₇, a, b, a * b, -x, -y, -(x * y)] i.succ = w_α i :=
        fun i => by fin_cases i <;> rfl
      have h0eq : ![e₇, a, b, a * b, -x, -y, -(x * y)] 0 = e₇ := rfl
      rw [h0eq]
      simp_rw [hsucc]
      ring
    rw [hQ₇_cons, hg_val]
    ring
  exact hv₇_ne (hQ₇_aniso v₇ hv₇_eq)

end OMA.KaplanskyNotSeven

open QuadraticMap QuadraticForm OMA.KaplanskyNotSeven in
theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.not_seven := by
  rintro ⟨F, _, _, hmax, hub⟩
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmax
  have : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have h2 : (2 : F) ≠ 0 := NeZero.ne (2 : F)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hQ0 : (weightedSumSquares F w).Anisotropic := by
    intro v hv
    have h0 : Q (e.symm v) = 0 := by
      rw [← e.map_app (e.symm v)]
      simpa using hv
    simpa using hQ _ h0
  have hm : Module.finrank F (Fin 7 → F) = 7 := by simp
  generalize Module.finrank F (Fin 7 → F) = m at w hQ0 hm
  subst hm
  have hw : ∀ i : Fin 7, w i ≠ 0 := by
    intro i hi
    have h0 : weightedSumSquares F w (Pi.single i (1 : F)) = 0 := by
      simp [weightedSumSquares_apply, Pi.single_apply, hi]
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa using congr_fun (hQ0 _ h0) i)
  set d : F := ∏ i : Fin 7, w i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hw i
  have h8_not : ¬ (8 ∈ anisotropicDims F) := fun h => by
    have := hub h
    omega
  -- Step 1: Find v₀ with weightedSumSquares F w v₀ = -d
  let w₈ : Fin 8 → F := ![w 0, w 1, w 2, w 3, w 4, w 5, w 6, d]
  have ⟨z, hz_ne, hz_eq⟩ : ∃ z : Fin 8 → F, z ≠ 0 ∧ weightedSumSquares F w₈ z = 0 := by
    by_contra h
    push Not at h
    exact h8_not (mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F w₈,
      fun x hx => by_contra fun hx0 => h x hx0 hx⟩)
  have hz_sum : ∑ i : Fin 7, w i * z i.castSucc ^ 2 + d * z 7 ^ 2 = 0 := by
    have hw₈ : ∀ i : Fin 7, w₈ i.castSucc = w i := fun i => by fin_cases i <;> rfl
    have hw₈_7 : w₈ (Fin.last 7) = d := rfl
    have hlast : z (Fin.last 7) = z 7 := rfl
    rw [weightedSumSquares_apply, Fin.sum_univ_castSucc] at hz_eq
    simp only [smul_eq_mul] at hz_eq
    rw [hw₈_7, hlast] at hz_eq
    have hsum7 : ∑ i : Fin 7, w₈ i.castSucc * (z i.castSucc * z i.castSucc) =
        ∑ i : Fin 7, w i * z i.castSucc ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hw₈]; ring
    rw [hsum7] at hz_eq
    linear_combination hz_eq
  have hz7 : z 7 ≠ 0 := by
    intro hz7_0
    have hz'_eq : weightedSumSquares F w (fun i : Fin 7 => z i.castSucc) = 0 := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
      have hsum7' : ∑ x : Fin 7, w x * (z x.castSucc * z x.castSucc) =
          ∑ i : Fin 7, w i * z i.castSucc ^ 2 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hsum7']
      rw [hz7_0] at hz_sum
      linear_combination hz_sum
    have hz'_0 := hQ0 _ hz'_eq
    apply hz_ne
    funext i
    fin_cases i
    · exact congr_fun hz'_0 0
    · exact congr_fun hz'_0 1
    · exact congr_fun hz'_0 2
    · exact congr_fun hz'_0 3
    · exact congr_fun hz'_0 4
    · exact congr_fun hz'_0 5
    · exact congr_fun hz'_0 6
    · exact hz7_0
  let v₀ : Fin 7 → F := fun i => z i.castSucc / z 7
  have hv₀ : weightedSumSquares F w v₀ = -d := by
    simp only [weightedSumSquares_apply, smul_eq_mul, v₀]
    have hmul : (∑ i : Fin 7, w i * (z i.castSucc / z 7 * (z i.castSucc / z 7))) * z 7 ^ 2 =
        ∑ i : Fin 7, w i * z i.castSucc ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [hz7]
    have hnum : ∑ i : Fin 7, w i * z i.castSucc ^ 2 = -d * z 7 ^ 2 := by
      linear_combination hz_sum
    exact mul_right_cancel₀ (pow_ne_zero 2 hz7) (hmul.trans hnum)
  -- Orthogonal complement W of v₀ and diagonalization of Q₀|_W
  let φ : (Fin 7 → F) →ₗ[F] F :=
    { toFun := fun x => ∑ i : Fin 7, w i * v₀ i * x i
      map_add' := fun x y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have hφv₀ : φ v₀ = -d := by
    have : φ v₀ = weightedSumSquares F w v₀ := by
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, weightedSumSquares_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, hv₀]
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨(c / -d) • v₀, ?_⟩
    rw [map_smul, smul_eq_mul, hφv₀, div_mul_cancel₀ _ (neg_ne_zero.mpr hd)]
  let W : Submodule F (Fin 7 → F) := LinearMap.ker φ
  have hW_rank : Module.finrank F W = 6 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    have hr : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
    rw [hr, finrank_top, Module.finrank_self] at h
    have h7 : Module.finrank F (Fin 7 → F) = 7 := by simp
    rw [h7] at h
    change 1 + Module.finrank F W = 7 at h
    omega
  have hQ_orth : ∀ t : F, ∀ y ∈ W,
      weightedSumSquares F w (t • v₀ + y) = -d * t ^ 2 + weightedSumSquares F w y := by
    intro t y hy
    have hφy : φ y = 0 := LinearMap.mem_ker.mp hy
    have hcross : ∑ i : Fin 7, w i * v₀ i * y i = 0 := hφy
    have hsum : weightedSumSquares F w (t • v₀ + y) =
        t ^ 2 * weightedSumSquares F w v₀ +
        2 * t * (∑ i : Fin 7, w i * v₀ i * y i) +
        weightedSumSquares F w y := by
      simp only [weightedSumSquares_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, hv₀, hcross]
    ring
  let Q_W : QuadraticForm F W := (weightedSumSquares F w).comp W.subtype
  obtain ⟨p, ⟨eW⟩⟩ := Q_W.equivalent_weightedSumSquares
  generalize Module.finrank F W = mW at p eW hW_rank
  subst hW_rank
  let E : (Fin 7 → F) →ₗ[F] (Fin 7 → F) :=
    { toFun := fun x => (x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ))
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul]
        have : (fun j : Fin 6 => x j.succ + y j.succ) =
            (fun j : Fin 6 => x j.succ) + (fun j : Fin 6 => y j.succ) := rfl
        rw [this, map_add, map_add]
        abel
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]
        have : (fun j : Fin 6 => a * x j.succ) = a • (fun j : Fin 6 => x j.succ) := rfl
        rw [this, map_smul, map_smul] }
  let w₂ : Fin 7 → F := ![-d, p 0, p 1, p 2, p 3, p 4, p 5]
  have hQE : ∀ x : Fin 7 → F, weightedSumSquares F w (E x) = weightedSumSquares F w₂ x := by
    intro x
    have hmem : W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) ∈ W := Submodule.coe_mem _
    have h1 := hQ_orth (x 0) _ hmem
    have h2' : weightedSumSquares F w (W.subtype (eW.symm (fun j : Fin 6 => x j.succ))) =
        Q_W (eW.symm (fun j : Fin 6 => x j.succ)) := rfl
    have h3 : Q_W (eW.symm (fun j : Fin 6 => x j.succ)) =
        weightedSumSquares F p (fun j : Fin 6 => x j.succ) := by
      rw [← eW.map_app (eW.symm (fun j : Fin 6 => x j.succ))]
      simp
    have h4 : weightedSumSquares F w₂ x =
        -d * x 0 ^ 2 + weightedSumSquares F p (fun j : Fin 6 => x j.succ) := by
      simp only [weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul]
      have hw₂0 : w₂ 0 = -d := rfl
      have hw₂s : ∀ j : Fin 6, w₂ j.succ = p j := fun j => by fin_cases j <;> rfl
      simp only [hw₂0, hw₂s]
      ring
    change weightedSumSquares F w ((x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ))) = _
    rw [h1, h2', h3, h4]
  have hE_inj : Function.Injective E := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hφx : φ (E x) = 0 := by rw [hx, map_zero]
    have hker : φ (W.subtype (eW.symm (fun j : Fin 6 => x j.succ))) = 0 :=
      LinearMap.mem_ker.mp (Submodule.coe_mem _)
    have hφE : φ (E x) = x 0 * (-d) := by
      change φ ((x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ))) = _
      rw [map_add, map_smul, smul_eq_mul, hφv₀, hker, add_zero]
    rw [hφE] at hφx
    have hx0 : x 0 = 0 := (mul_eq_zero.mp hφx).resolve_right (neg_ne_zero.mpr hd)
    have hW0 : W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) = 0 := by
      have hEx : (x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) = 0 := hx
      rw [hx0, zero_smul, zero_add] at hEx
      exact hEx
    have heW0 : eW.symm (fun j : Fin 6 => x j.succ) = 0 := Subtype.ext hW0
    have hsucc0 : (fun j : Fin 6 => x j.succ) = 0 :=
      eW.symm.injective (heW0.trans (map_zero eW.symm).symm)
    funext i
    refine Fin.cases hx0 ?_ i
    intro j
    exact congr_fun hsucc0 j
  let eE := LinearEquiv.ofInjectiveEndo E hE_inj
  let M : Matrix (Fin 7) (Fin 7) F := LinearMap.toMatrix' eE.toLinearMap
  let M_inv : Matrix (Fin 7) (Fin 7) F := LinearMap.toMatrix' eE.symm.toLinearMap
  have hc₀ : M.det ≠ 0 := by
    have hMM : M * M_inv = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have hcomp : eE.toLinearMap.comp eE.symm.toLinearMap = LinearMap.id :=
        LinearMap.ext fun x => eE.apply_symm_apply x
      rw [hcomp, LinearMap.toMatrix'_id]
    have hdet := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact left_ne_zero_of_mul_eq_one hdet
  have hgram : M.transpose * Matrix.diagonal w * M = Matrix.diagonal w₂ := by
    have hpol : ∀ x y : Fin 7 → F,
        (∑ k : Fin 7, w k * E x k * E y k) = ∑ k : Fin 7, w₂ k * x k * y k := by
      intro x y
      have hdiff : 2 * (∑ k : Fin 7, w k * E x k * E y k) =
          2 * (∑ k : Fin 7, w₂ k * x k * y k) := by
        have h1 : weightedSumSquares F w (E (x + y)) = weightedSumSquares F w₂ (x + y) := hQE (x + y)
        have h2' : weightedSumSquares F w (E x) = weightedSumSquares F w₂ x := hQE x
        have h3 : weightedSumSquares F w (E y) = weightedSumSquares F w₂ y := hQE y
        rw [map_add] at h1
        have hL : weightedSumSquares F w (E x + E y) - weightedSumSquares F w (E x) -
            weightedSumSquares F w (E y) = 2 * (∑ k : Fin 7, w k * E x k * E y k) := by
          simp only [weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        have hR : weightedSumSquares F w₂ (x + y) - weightedSumSquares F w₂ x -
            weightedSumSquares F w₂ y = 2 * (∑ k : Fin 7, w₂ k * x k * y k) := by
          simp only [weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [h1, h2', h3] at hL
        rw [hL] at hR
        exact hR
      exact mul_left_cancel₀ h2 hdiff
    ext i j
    have hij := hpol (Pi.single i 1) (Pi.single j 1)
    have hM_col : ∀ a k : Fin 7, E (Pi.single a 1) k = M k a := by
      intro a k
      have heE : (eE.toLinearMap : (Fin 7 → F) → (Fin 7 → F)) = E := rfl
      simp [M, LinearMap.toMatrix'_apply, heE]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    have hL' : (∑ x : Fin 7, (∑ x_1 : Fin 7, M x_1 i *
        (if x_1 = x then w x_1 else 0)) * M x j) =
        ∑ k : Fin 7, w k * E (Pi.single i 1) k * E (Pi.single j 1) k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k (fun a _ ha => by simp [ha]) (fun hk => absurd (Finset.mem_univ k) hk)]
      simp only [ite_true, hM_col i k, hM_col j k]
      ring
    have hR' : (if i = j then w₂ i else 0) =
        ∑ k : Fin 7, w₂ k * (Pi.single i (1 : F) : Fin 7 → F) k *
          (Pi.single j (1 : F) : Fin 7 → F) k := by
      rw [Finset.sum_eq_single i]
      · by_cases h : i = j <;> simp [h]
      · intro k _ hk; simp [Pi.single_apply, hk]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hL', hR', hij]
  have hdet_gram := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Matrix.det_diagonal] at hdet_gram
  have hprod_w : (∏ i : Fin 7, w i) = d := rfl
  have hprod_w2 : (∏ i : Fin 7, w₂ i) = -d * (p 0 * p 1 * p 2 * p 3 * p 4 * p 5) := by
    simp [Fin.prod_univ_seven, w₂, mul_assoc]
  rw [hprod_w, hprod_w2] at hdet_gram
  set c₀ := M.det
  have hp_sq : p 0 * p 1 * p 2 * p 3 * p 4 * p 5 = -(c₀ ^ 2) := by
    have h1 : d * (c₀ ^ 2) = d * (-(p 0 * p 1 * p 2 * p 3 * p 4 * p 5)) := by
      linear_combination hdet_gram
    have h2' := (mul_left_cancel₀ hd h1).symm
    linear_combination -h2'
  have hp_ne : p 0 * p 1 * p 2 * p 3 * p 4 * p 5 ≠ 0 := by
    rw [hp_sq]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hc₀)
  have hp0 : p 0 ≠ 0 := fun h => hp_ne (by simp [h])
  have hp1 : p 1 ≠ 0 := fun h => hp_ne (by simp [h])
  have hp2 : p 2 ≠ 0 := fun h => hp_ne (by simp [h])
  have hp3 : p 3 ≠ 0 := fun h => hp_ne (by simp [h])
  have hp4 : p 4 ≠ 0 := fun h => hp_ne (by simp [h])
  have hp5 : p 5 ≠ 0 := fun h => hp_ne (by simp [h])
  -- Step 2: Rescale to Q₇ = <e, a, b, a * b, -x, -y, -(x * y)>
  set s := p 0 * p 1 * p 2
  have hs : s ≠ 0 := mul_ne_zero (mul_ne_zero hp0 hp1) hp2
  set a := p 0 / s
  set b := p 1 / s
  set x := -p 3 / s
  set y := -p 4 / s
  set e₇ := -d / s
  have ha : a ≠ 0 := div_ne_zero hp0 hs
  have hb : b ≠ 0 := div_ne_zero hp1 hs
  have hx : x ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp3) hs
  have hy : y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp4) hs
  have he₇ : e₇ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hd) hs
  let Q₇ := weightedSumSquares F ![e₇, a, b, a * b, -x, -y, -(x * y)]
  have hQ₇_aniso : Q₇.Anisotropic := by
    intro z hz
    set lam := s * p 5 / c₀
    have hlam : lam ≠ 0 := div_ne_zero (mul_ne_zero hs hp5) hc₀
    let vec : Fin 7 → F := ![z 0, z 1, z 2, z 3 / p 2, z 4, z 5, z 6 / lam]
    have hQ_vec : weightedSumSquares F w (E vec) = 0 := by
      rw [hQE vec]
      simp only [weightedSumSquares_apply, Fin.sum_univ_seven, smul_eq_mul, w₂, vec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
      have h5v : ![-d, p 0, p 1, p 2, p 3, p 4, p 5] 5 = p 4 := rfl
      have h6v : ![-d, p 0, p 1, p 2, p 3, p 4, p 5] 6 = p 5 := rfl
      have hv5 : ![z 0, z 1, z 2, z 3 / p 2, z 4, z 5, z 6 / lam] 5 = z 5 := rfl
      have hv6 : ![z 0, z 1, z 2, z 3 / p 2, z 4, z 5, z 6 / lam] 6 = z 6 / lam := rfl
      simp only [Q₇, weightedSumSquares_apply, Fin.sum_univ_seven, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at hz
      have h5q : ![e₇, a, b, a * b, -x, -y, -(x * y)] 5 = -y := rfl
      have h6q : ![e₇, a, b, a * b, -x, -y, -(x * y)] 6 = -(x * y) := rfl
      have hp34 : p 3 * p 4 = -(c₀ ^ 2) / (s * p 5) := by
        rw [← hp_sq]
        field_simp [hs, hp5]
      have hid : -d * (z 0 * z 0) + p 0 * (z 1 * z 1) + p 1 * (z 2 * z 2) +
          p 2 * (z 3 / p 2 * (z 3 / p 2)) + p 3 * (z 4 * z 4) +
          p 4 * (z 5 * z 5) + p 5 * (z 6 / lam * (z 6 / lam)) =
          s * (e₇ * (z 0 * z 0) + a * (z 1 * z 1) + b * (z 2 * z 2) +
          a * b * (z 3 * z 3) + -x * (z 4 * z 4) +
          -y * (z 5 * z 5) + -(x * y) * (z 6 * z 6)) := by
        simp only [e₇, a, b, x, y, lam]
        have hmul_ab : (p 0 / s) * (p 1 / s) = 1 / (s * p 2) := by
          simp only [s]
          field_simp [hp0, hp1, hp2]
        have hmul_xy : (-p 3 / s) * (-p 4 / s) = -(c₀ ^ 2) / (s ^ 3 * p 5) := by
          calc (-p 3 / s) * (-p 4 / s) = (p 3 * p 4) / s ^ 2 := by ring
            _ = (-(c₀ ^ 2) / (s * p 5)) / s ^ 2 := by rw [hp34]
            _ = -(c₀ ^ 2) / (s ^ 3 * p 5) := by ring
        rw [hmul_ab, hmul_xy]
        field_simp [hp0, hp1, hp2, hp3, hp4, hp5, hs, hc₀]
      rw [h5v, h6v, hv5, hv6]
      rw [h5q, h6q] at hz
      rw [hid, hz, mul_zero]
    have hvec : vec = 0 := hE_inj ((hQ0 _ hQ_vec).trans (map_zero E).symm)
    funext i
    fin_cases i
    · exact by simpa [vec] using congr_fun hvec 0
    · exact by simpa [vec] using congr_fun hvec 1
    · exact by simpa [vec] using congr_fun hvec 2
    · have h3 : z 3 / p 2 = 0 := by simpa [vec] using congr_fun hvec 3
      exact (div_eq_zero_iff.mp h3).resolve_right hp2
    · exact by simpa [vec] using congr_fun hvec 4
    · exact by simpa [vec] using congr_fun hvec 5
    · have h6 : z 6 / lam = 0 := by simpa [vec] using congr_fun hvec 6
      exact (div_eq_zero_iff.mp h6).resolve_right hlam
  -- Step 3: ρ₁ = <1, a, b, a * b> and ρ₂ = <1, x, y, x * y> are anisotropic
  have hpure1 : (weightedSumSquares F ![a, b, a * b]).Anisotropic := by
    intro t ht
    let v : Fin 7 → F := ![0, t 0, t 1, t 2, 0, 0, 0]
    have hv : Q₇ v = 0 := by
      simp only [Q₇, weightedSumSquares_apply, Fin.sum_univ_seven, smul_eq_mul]
      simp only [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul] at ht
      have hq1 : ![e₇, a, b, a * b, -x, -y, -(x * y)] 1 = a := rfl
      have hq2 : ![e₇, a, b, a * b, -x, -y, -(x * y)] 2 = b := rfl
      have hq3 : ![e₇, a, b, a * b, -x, -y, -(x * y)] 3 = a * b := rfl
      have hv0 : v 0 = 0 := rfl
      have hv1 : v 1 = t 0 := rfl
      have hv2 : v 2 = t 1 := rfl
      have hv3 : v 3 = t 2 := rfl
      have hv4 : v 4 = 0 := rfl
      have hv5 : v 5 = 0 := rfl
      have hv6 : v 6 = 0 := rfl
      have ht0 : ![a, b, a * b] 0 = a := rfl
      have ht1 : ![a, b, a * b] 1 = b := rfl
      have ht2 : ![a, b, a * b] 2 = a * b := rfl
      rw [hq1, hq2, hq3, hv0, hv1, hv2, hv3, hv4, hv5, hv6]
      rw [ht0, ht1, ht2] at ht
      linear_combination ht
    have hv0 := hQ₇_aniso v hv
    funext i
    fin_cases i
    · exact by simpa [v] using congr_fun hv0 1
    · exact by simpa [v] using congr_fun hv0 2
    · exact by simpa [v] using congr_fun hv0 3
  have hpure2 : (weightedSumSquares F ![x, y, x * y]).Anisotropic := by
    intro t ht
    let v : Fin 7 → F := ![0, 0, 0, 0, t 0, t 1, t 2]
    have hv : Q₇ v = 0 := by
      simp only [Q₇, weightedSumSquares_apply, Fin.sum_univ_seven, smul_eq_mul]
      simp only [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul] at ht
      have hq4 : ![e₇, a, b, a * b, -x, -y, -(x * y)] 4 = -x := rfl
      have hq5 : ![e₇, a, b, a * b, -x, -y, -(x * y)] 5 = -y := rfl
      have hq6 : ![e₇, a, b, a * b, -x, -y, -(x * y)] 6 = -(x * y) := rfl
      have hv0 : v 0 = 0 := rfl
      have hv1 : v 1 = 0 := rfl
      have hv2 : v 2 = 0 := rfl
      have hv3 : v 3 = 0 := rfl
      have hv4 : v 4 = t 0 := rfl
      have hv5 : v 5 = t 1 := rfl
      have hv6 : v 6 = t 2 := rfl
      have ht0 : ![x, y, x * y] 0 = x := rfl
      have ht1 : ![x, y, x * y] 1 = y := rfl
      have ht2 : ![x, y, x * y] 2 = x * y := rfl
      rw [hq4, hq5, hq6, hv0, hv1, hv2, hv3, hv4, hv5, hv6]
      rw [ht0, ht1, ht2] at ht
      linear_combination -ht
    have hv0 := hQ₇_aniso v hv
    funext i
    fin_cases i
    · exact by simpa [v] using congr_fun hv0 4
    · exact by simpa [v] using congr_fun hv0 5
    · exact by simpa [v] using congr_fun hv0 6
  have hρ₁ : (weightedSumSquares F ![1, a, b, a * b]).Anisotropic :=
    pfister2_anisotropic_of_pure ha hpure1
  have hρ₂ : (weightedSumSquares F ![1, x, y, x * y]).Anisotropic :=
    pfister2_anisotropic_of_pure hx hpure2
  exact step6_contradiction h2 h8_not he₇ ha hQ₇_aniso hρ₁ hρ₂
