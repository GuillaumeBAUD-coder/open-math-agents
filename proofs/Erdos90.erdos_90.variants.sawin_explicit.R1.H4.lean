import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1

/-!
# Proof of Sawin `H4` (`Erdos90.erdos_90.variants.sawin_explicit.R1.H4`)

Ideal family construction, CM norm-1 identity on complex embeddings, and Euclidean lattice embedding.
-/

open NumberField EuclideanGeometry
open scoped EuclideanGeometry

namespace H4Proof

private lemma cm_norm_one_embedding_norm
    (F K : Type) [Field F] [CharZero F] [NumberField F] [IsTotallyReal F]
    [Field K] [CharZero K] [NumberField K] [IsTotallyComplex K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K]
    {β : K} (hβ : Algebra.norm F β = 1) (φ : K →+* ℂ) : ‖φ β‖ = 1 := by
  classical
  have : IsCMField K := IsCMField.ofCMExtension F K
  let τ : K ≃ₐ[F] K :=
    { toRingEquiv := (IsCMField.complexConj K).toRingEquiv
      commutes' := fun r => by
        change IsCMField.complexConj K
            (algebraMap (maximalRealSubfield K) K (CMExtension.equivMaximalRealSubfield F K r)) =
          algebraMap (maximalRealSubfield K) K (CMExtension.equivMaximalRealSubfield F K r)
        exact (IsCMField.complexConj K).commutes _ }
  have hτ_ne : τ ≠ 1 := by
    intro h
    apply IsCMField.complexConj_ne_one K
    ext x
    exact congr_arg (fun σ : K ≃ₐ[F] K => σ x) h
  have : IsGalois F K := Algebra.IsQuadraticExtension.isGalois F K
  have hcard : Nat.card (K ≃ₐ[F] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank F K, Algebra.IsQuadraticExtension.finrank_eq_two F K]
  have huniv : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, τ} := by
    refine (Finset.eq_univ_of_card {1, τ} ?_).symm
    rw [Finset.card_pair hτ_ne.symm, ← Nat.card_eq_fintype_card, hcard]
  have hprod : algebraMap F K (Algebra.norm F β) = β * IsCMField.complexConj K β := by
    rw [Algebra.norm_eq_prod_automorphisms F β, huniv, Finset.prod_pair hτ_ne.symm]
    rfl
  rw [hβ, map_one] at hprod
  have hφ : φ β * starRingEnd ℂ (φ β) = 1 := by
    have h0 := congr_arg φ hprod.symm
    rwa [map_mul, map_one, IsCMField.complexEmbedding_complexConj] at h0
  have hnorm : ‖φ β‖ * ‖φ β‖ = 1 := by
    have h0 := congr_arg (fun z : ℂ => ‖z‖) hφ
    simpa [norm_mul, Complex.norm_conj] using h0
  by_contra! hne
  rcases lt_or_gt_of_ne hne with h | h <;> nlinarith [norm_nonneg (φ β)]

private lemma inv_ideal_norm_lower
    (K : Type) [Field K] [NumberField K]
    (J₀ : Ideal (𝓞 K)) (hJ₀ : J₀ ≠ ⊥) (habs_pos : 0 < Ideal.absNorm J₀)
    {x : K} (hx0 : x ≠ 0)
    (hxJ : ∀ a ∈ J₀, ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = x * algebraMap (𝓞 K) K a) :
    (Ideal.absNorm J₀ : ℝ)⁻¹ ≤ |(Algebra.norm ℚ x : ℝ)| := by
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨n, m, hm_nzd, rfl⟩
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm_nzd
  have hmK : algebraMap (𝓞 K) K m ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hm0
  have hn0 : n ≠ 0 := by
    intro h
    apply hx0
    simp [h]
  have hle : Ideal.span {n} * J₀ ≤ Ideal.span {m} := by
    rw [Ideal.mul_le]
    intro r hr a ha
    rw [Ideal.mem_span_singleton] at hr
    rcases hr with ⟨c, rfl⟩
    rcases hxJ a ha with ⟨b, hb⟩
    have hmul : algebraMap (𝓞 K) K (n * a) = algebraMap (𝓞 K) K (m * b) := by
      calc algebraMap (𝓞 K) K (n * a)
          = (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m * algebraMap (𝓞 K) K m) *
              algebraMap (𝓞 K) K a := by rw [map_mul, div_mul_cancel₀ _ hmK]
        _ = algebraMap (𝓞 K) K m *
              (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m * algebraMap (𝓞 K) K a) := by
            ring
        _ = algebraMap (𝓞 K) K (m * b) := by rw [← hb, map_mul]
    have hna : n * a = m * b := (IsFractionRing.injective (𝓞 K) K) hmul
    rw [Ideal.mem_span_singleton]
    refine ⟨c * b, ?_⟩
    calc (n * c) * a = c * (n * a) := by ring
      _ = c * (m * b) := by rw [hna]
      _ = m * (c * b) := by ring
  have hdvd : Ideal.absNorm (Ideal.span {m}) ∣
      Ideal.absNorm (Ideal.span {n}) * Ideal.absNorm J₀ := by
    rw [← map_mul]
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  have hnorm_n0 : Algebra.norm ℤ n ≠ 0 := by
    intro h0
    have hq0 : Algebra.norm ℚ (algebraMap (𝓞 K) K n) = 0 := by
      rw [← Algebra.coe_norm_int, h0, Int.cast_zero]
    rw [Algebra.norm_eq_zero_iff] at hq0
    exact hn0 ((IsFractionRing.injective (𝓞 K) K) (by simpa using hq0))
  have hrhs_pos : 0 < Ideal.absNorm (Ideal.span {n}) * Ideal.absNorm J₀ := by
    rw [Ideal.absNorm_span_singleton]
    exact Nat.mul_pos (Int.natAbs_pos.mpr hnorm_n0) habs_pos
  have hnat_le : Ideal.absNorm (Ideal.span {m}) ≤
      Ideal.absNorm (Ideal.span {n}) * Ideal.absNorm J₀ :=
    Nat.le_of_dvd hrhs_pos hdvd
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hnat_le
  have hreal_le : |(Algebra.norm ℤ m : ℝ)| ≤ |(Algebra.norm ℤ n : ℝ)| * (Ideal.absNorm J₀ : ℝ) := by
    have hcast : ((Algebra.norm ℤ m).natAbs : ℝ) ≤
        ((Algebra.norm ℤ n).natAbs : ℝ) * (Ideal.absNorm J₀ : ℝ) := by
      exact_mod_cast hnat_le
    simpa [Nat.cast_natAbs] using hcast
  have hm_norm_ne : Algebra.norm ℚ (algebraMap (𝓞 K) K m) ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]
    exact hmK
  have hq_rel : Algebra.norm ℚ (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K n) / Algebra.norm ℚ (algebraMap (𝓞 K) K m) := by
    rw [eq_div_iff hm_norm_ne, ← map_mul, div_mul_cancel₀ _ hmK]
  have hr_eq : (Algebra.norm ℤ m : ℝ) = (Algebra.norm ℚ (algebraMap (𝓞 K) K m) : ℝ) := by
    have h := congr_arg ((↑) : ℚ → ℝ) (Algebra.coe_norm_int m)
    simpa using h
  have hr_eq_n : (Algebra.norm ℤ n : ℝ) = (Algebra.norm ℚ (algebraMap (𝓞 K) K n) : ℝ) := by
    have h := congr_arg ((↑) : ℚ → ℝ) (Algebra.coe_norm_int n)
    simpa using h
  have hxm_abs : |(Algebra.norm ℚ (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m) : ℝ)| =
      |(Algebra.norm ℚ (algebraMap (𝓞 K) K n) : ℝ)| /
        |(Algebra.norm ℚ (algebraMap (𝓞 K) K m) : ℝ)| := by
    rw [hq_rel, Rat.cast_div, abs_div]
  have hm_abs_pos : 0 < |(Algebra.norm ℚ (algebraMap (𝓞 K) K m) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hm_norm_ne
  have hJ_pos : (0 : ℝ) < (Ideal.absNorm J₀ : ℝ) := by exact_mod_cast habs_pos
  rw [hr_eq, hr_eq_n] at hreal_le
  rw [hxm_abs, le_div_iff₀ hm_abs_pos]
  calc (Ideal.absNorm J₀ : ℝ)⁻¹ * |(Algebra.norm ℚ (algebraMap (𝓞 K) K m) : ℝ)|
      ≤ (Ideal.absNorm J₀ : ℝ)⁻¹ * (|(Algebra.norm ℚ (algebraMap (𝓞 K) K n) : ℝ)| *
          (Ideal.absNorm J₀ : ℝ)) := by gcongr
    _ = |(Algebra.norm ℚ (algebraMap (𝓞 K) K n) : ℝ)| := by
          rw [mul_left_comm, inv_mul_cancel₀ hJ_pos.ne', mul_one]

private noncomputable def idxEquiv (d : ℕ) : Fin d × Fin 2 ≃ Fin (2 * d) where
  toFun p := ⟨2 * p.1.1 + p.2.1, by omega⟩
  invFun q := (⟨q.1 / 2, by omega⟩, ⟨q.1 % 2, by omega⟩)
  left_inv p := by
    rcases p with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    ext <;> dsimp <;> omega
  right_inv q := by
    rcases q with ⟨q, hq⟩
    ext
    dsimp
    omega

private lemma h4_aux
    (F K : Type) [Field F] [CharZero F] [NumberField F] [IsTotallyReal F]
    [Field K] [CharZero K] [NumberField K] [IsTotallyComplex K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K]
    (hd_pos : 1 ≤ Module.finrank ℚ F)
    (S_Q : Finset ℕ) (e f k : ℕ → ℕ) (C_loss : ℝ)
    (_hC_pos : 0 < C_loss)
    (hSQ : ∀ p ∈ S_Q, p.Prime ∧ 1 ≤ e p ∧ 1 ≤ f p ∧ 1 ≤ k p)
    (hP_hyp : ∀ p ∈ S_Q, ∀ 𝔭 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
      𝔭.ramificationIdx ℤ = e p ∧ 𝔭.inertiaDeg ℤ ≤ f p ∧ Nat.card (𝔭.primesOver (𝓞 K)) = 2)
    (hH3 : ∀ (L : Finset (Ideal (𝓞 K))),
      L.Nonempty → (∀ J ∈ L, J ≠ ⊥) →
      (∀ J₁ ∈ L, ∀ J₂ ∈ L, Ideal.relNorm (𝓞 F) J₁ = Ideal.relNorm (𝓞 F) J₂) →
      ∃ J₀ ∈ L, ∃ B : Finset K,
        (∀ β ∈ B, (∀ a ∈ J₀, ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = β * algebraMap (𝓞 K) K a) ∧
          Algebra.norm F β = 1) ∧
        (L.card : ℝ) ≤ (B.card : ℝ) * C_loss) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * Module.finrank ℚ F))))
      (ρ : ℝ) (π : Λ →+ ℝ²) (S : Finset Λ),
      0 < ρ ∧
      (∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * Module.finrank ℚ F)))‖) ∧
      Function.Injective π ∧
      (∀ v ∈ S, ‖(v : EuclideanSpace ℝ (Fin (2 * Module.finrank ℚ F)))‖ ≤ 1) ∧
      (∀ v ∈ S, ‖π v‖ = 1) ∧
      ρ⁻¹ ≤ ∏ p ∈ S_Q, (p : ℝ) ^ ((k p : ℝ) / (2 * (e p : ℝ))) ∧
      ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((Module.finrank ℚ F : ℝ) / ((e p : ℝ) * (f p : ℝ))) ≤
        (S.card : ℝ) * C_loss := by
  classical
  let d : ℕ := Module.finrank ℚ F
  have hfin_OF_OK : Module.finrank (𝓞 F) (𝓞 K) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K,
      Algebra.IsQuadraticExtension.finrank_eq_two F K]
  have hfin_Z_OF : Module.finrank ℤ (𝓞 F) = d := by
    exact NumberField.RingOfIntegers.rank F
  have hIp_max : ∀ p : {p // p ∈ S_Q}, (Ideal.span {(p.1 : ℤ)} : Ideal ℤ).IsMaximal := fun p =>
    have hp : p.1.Prime := (hSQ p.1 p.2).1
    have hne : (Ideal.span {(p.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Int.natCast_ne_zero.mpr hp.ne_zero
    ((Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal hne
  let Idx := Σ p : {p // p ∈ S_Q}, ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F))
  have h_pair : ∀ x : Idx,
      ∃ (q₁ q₂ : (x.2.1).primesOver (𝓞 K)),
        q₁ ≠ q₂ ∧ (q₁.1.inertiaDeg (𝓞 F) = 1 ∧ q₂.1.inertiaDeg (𝓞 F) = 1) := by
    intro x
    have hp_prime : x.1.1.Prime := (hSQ x.1.1 x.1.2).1
    have hIp_ne : (Ideal.span {(x.1.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Int.natCast_ne_zero.mpr hp_prime.ne_zero
    have h𝔭_prime : x.2.1.IsPrime := x.2.2.1
    have h𝔭_ne : x.2.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hIp_ne x.2.2
    have h𝔭_max : x.2.1.IsMaximal := h𝔭_prime.isMaximal h𝔭_ne
    have hcard2 : Nat.card ((x.2.1).primesOver (𝓞 K)) = 2 :=
      (hP_hyp x.1.1 x.1.2 x.2.1 x.2.2).2.2
    rcases Nat.card_eq_two_iff.mp hcard2 with ⟨q₁, q₂, hq_ne, hq_univ⟩
    have hsum := Ideal.sum_ramification_inertia_eq_finrank x.2.1 (𝓞 K)
    rw [hfin_OF_OK] at hsum
    have huniv : (Finset.univ : Finset ((x.2.1).primesOver (𝓞 K))) = {q₁, q₂} := by
      ext q
      have hmem : q ∈ ({q₁, q₂} : Set ((x.2.1).primesOver (𝓞 K))) := by
        rw [hq_univ]; trivial
      simpa using hmem
    rw [huniv, Finset.sum_pair hq_ne] at hsum
    have : q₁.1.IsPrime := q₁.2.1
    have : q₂.1.IsPrime := q₂.2.1
    have hpos_e1 : 0 < q₁.1.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos q₁.1 (𝓞 F)
    have hpos_f1 : 0 < q₁.1.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos q₁.1 (𝓞 F)
    have hpos_e2 : 0 < q₂.1.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos q₂.1 (𝓞 F)
    have hpos_f2 : 0 < q₂.1.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos q₂.1 (𝓞 F)
    have hmul1 : 1 ≤ q₁.1.ramificationIdx (𝓞 F) * q₁.1.inertiaDeg (𝓞 F) :=
      Nat.succ_le_of_lt (Nat.mul_pos hpos_e1 hpos_f1)
    have hmul2 : 1 ≤ q₂.1.ramificationIdx (𝓞 F) * q₂.1.inertiaDeg (𝓞 F) :=
      Nat.succ_le_of_lt (Nat.mul_pos hpos_e2 hpos_f2)
    have heq1 : q₁.1.ramificationIdx (𝓞 F) * q₁.1.inertiaDeg (𝓞 F) = 1 := by omega
    have heq2 : q₂.1.ramificationIdx (𝓞 F) * q₂.1.inertiaDeg (𝓞 F) = 1 := by omega
    have hf1 : q₁.1.inertiaDeg (𝓞 F) = 1 := by
      by_contra h
      have : 2 ≤ q₁.1.inertiaDeg (𝓞 F) := by omega
      nlinarith
    have hf2 : q₂.1.inertiaDeg (𝓞 F) = 1 := by
      by_contra h
      have : 2 ≤ q₂.1.inertiaDeg (𝓞 F) := by omega
      nlinarith
    exact ⟨q₁, q₂, hq_ne, hf1, hf2⟩
  choose q₁ q₂ hq_ne hq_inert using h_pair
  have hrelNorm_q1 : ∀ x : Idx, Ideal.relNorm (𝓞 F) (q₁ x).1 = x.2.1 := by
    intro x
    have hp_prime : x.1.1.Prime := (hSQ x.1.1 x.1.2).1
    have hIp_ne : (Ideal.span {(x.1.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Int.natCast_ne_zero.mpr hp_prime.ne_zero
    have h𝔭_ne : x.2.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hIp_ne x.2.2
    have h𝔭_max : x.2.1.IsMaximal := x.2.2.1.isMaximal h𝔭_ne
    have hq1_ne : (q₁ x).1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver h𝔭_ne (q₁ x).2
    have hq1_max : (q₁ x).1.IsMaximal := (q₁ x).2.1.isMaximal hq1_ne
    have hlo : (q₁ x).1.LiesOver x.2.1 := (q₁ x).2.2
    rw [Ideal.relNorm_eq_pow_of_isMaximal (R := 𝓞 F) (q₁ x).1 x.2.1,
      (hq_inert x).1, pow_one]
  have hrelNorm_q2 : ∀ x : Idx, Ideal.relNorm (𝓞 F) (q₂ x).1 = x.2.1 := by
    intro x
    have hp_prime : x.1.1.Prime := (hSQ x.1.1 x.1.2).1
    have hIp_ne : (Ideal.span {(x.1.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Int.natCast_ne_zero.mpr hp_prime.ne_zero
    have h𝔭_ne : x.2.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hIp_ne x.2.2
    have h𝔭_max : x.2.1.IsMaximal := x.2.2.1.isMaximal h𝔭_ne
    have hq2_ne : (q₂ x).1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver h𝔭_ne (q₂ x).2
    have hq2_max : (q₂ x).1.IsMaximal := (q₂ x).2.1.isMaximal hq2_ne
    have hlo : (q₂ x).1.LiesOver x.2.1 := (q₂ x).2.2
    rw [Ideal.relNorm_eq_pow_of_isMaximal (R := 𝓞 F) (q₂ x).1 x.2.1,
      (hq_inert x).2, pow_one]
  let G := ∀ x : Idx, Fin (k x.1.1 + 1)
  let Jfun : G → Ideal (𝓞 K) := fun g =>
    ∏ x : Idx, (q₁ x).1 ^ (g x : ℕ) * (q₂ x).1 ^ (k x.1.1 - (g x : ℕ))
  let L : Finset (Ideal (𝓞 K)) := Finset.univ.image Jfun
  have hL_ne : L.Nonempty := Finset.Nonempty.image Finset.univ_nonempty Jfun
  have hq1_ne_bot : ∀ x : Idx, (q₁ x).1 ≠ ⊥ := fun x => by
    have hp_prime : x.1.1.Prime := (hSQ x.1.1 x.1.2).1
    have hIp_ne : (Ideal.span {(x.1.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Int.natCast_ne_zero.mpr hp_prime.ne_zero
    exact Ideal.ne_bot_of_mem_primesOver
      (Ideal.ne_bot_of_mem_primesOver hIp_ne x.2.2) (q₁ x).2
  have hq2_ne_bot : ∀ x : Idx, (q₂ x).1 ≠ ⊥ := fun x => by
    have hp_prime : x.1.1.Prime := (hSQ x.1.1 x.1.2).1
    have hIp_ne : (Ideal.span {(x.1.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Int.natCast_ne_zero.mpr hp_prime.ne_zero
    exact Ideal.ne_bot_of_mem_primesOver
      (Ideal.ne_bot_of_mem_primesOver hIp_ne x.2.2) (q₂ x).2
  have hJ_ne_bot : ∀ g : G, Jfun g ≠ ⊥ := fun g => by
    change (∏ x : Idx, (q₁ x).1 ^ (g x : ℕ) * (q₂ x).1 ^ (k x.1.1 - (g x : ℕ))) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro x _
    exact mul_ne_zero (pow_ne_zero _ (hq1_ne_bot x)) (pow_ne_zero _ (hq2_ne_bot x))
  have hL_ne_bot : ∀ J ∈ L, J ≠ ⊥ := by
    intro J hJ
    rcases Finset.mem_image.mp hJ with ⟨g, _, rfl⟩
    exact hJ_ne_bot g
  have hrelNorm_J : ∀ g : G, Ideal.relNorm (𝓞 F) (Jfun g) = ∏ x : Idx, x.2.1 ^ (k x.1.1) := by
    intro g
    simp only [Jfun, map_prod, map_mul, map_pow, hrelNorm_q1, hrelNorm_q2]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← pow_add]
    congr 1
    have hle : (g x : ℕ) ≤ k x.1.1 := Nat.le_of_lt_succ (g x).isLt
    omega
  have hL_rel : ∀ J₁ ∈ L, ∀ J₂ ∈ L, Ideal.relNorm (𝓞 F) J₁ = Ideal.relNorm (𝓞 F) J₂ := by
    intro J₁ hJ₁ J₂ hJ₂
    rcases Finset.mem_image.mp hJ₁ with ⟨g₁, _, rfl⟩
    rcases Finset.mem_image.mp hJ₂ with ⟨g₂, _, rfl⟩
    rw [hrelNorm_J g₁, hrelNorm_J g₂]
  have hidx_eq : ∀ {x y : Idx}, x.2.1 = y.2.1 → x = y := by
    intro x y hxy
    rcases x with ⟨⟨p, hp⟩, ⟨𝔭, h𝔭⟩⟩
    rcases y with ⟨⟨q, hq⟩, ⟨𝔮, h𝔮⟩⟩
    dsimp at hxy
    have hcomap : Ideal.span {(p : ℤ)} = Ideal.span {(q : ℤ)} := by
      have h1 : Ideal.comap (algebraMap ℤ (𝓞 F)) 𝔭 = Ideal.span {(p : ℤ)} :=
        (Ideal.liesOver_iff _ _).mp h𝔭.2 |>.symm
      have h2 : Ideal.comap (algebraMap ℤ (𝓞 F)) 𝔮 = Ideal.span {(q : ℤ)} :=
        (Ideal.liesOver_iff _ _).mp h𝔮.2 |>.symm
      rw [← h1, ← h2, hxy]
    have hpq : p = q := by
      have hnorm := congr_arg Ideal.absNorm hcomap
      simpa [Ideal.absNorm_span_natCast] using hnorm
    subst hpq
    have h𝔭𝔮 : (⟨𝔭, h𝔭⟩ : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F)) = ⟨𝔮, h𝔮⟩ :=
      Subtype.ext hxy
    rw [h𝔭𝔮]
  have hq1_q1 : ∀ {x y : Idx}, (q₁ x).1 = (q₁ y).1 → x = y := by
    intro x y h
    apply hidx_eq
    have h1 : x.2.1 = Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (q₁ x).1 :=
      (Ideal.liesOver_iff _ _).mp (q₁ x).2.2
    have h2 : y.2.1 = Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (q₁ y).1 :=
      (Ideal.liesOver_iff _ _).mp (q₁ y).2.2
    rw [h1, h2, h]
  have hq1_q2 : ∀ x y : Idx, (q₁ x).1 ≠ (q₂ y).1 := by
    intro x y h
    have hxy : x = y := by
      apply hidx_eq
      have h1 : x.2.1 = Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (q₁ x).1 :=
        (Ideal.liesOver_iff _ _).mp (q₁ x).2.2
      have h2 : y.2.1 = Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (q₂ y).1 :=
        (Ideal.liesOver_iff _ _).mp (q₂ y).2.2
      rw [h1, h2, h]
    subst hxy
    exact hq_ne x (Subtype.ext h)
  have hJ_inj : Function.Injective Jfun := by
    intro g₁ g₂ heq
    ext x
    have hcount : ∀ g : G,
        (UniqueFactorizationMonoid.normalizedFactors (Jfun g)).count (q₁ x).1 = (g x : ℕ) := by
      intro g
      have hnorm_prod : ∀ s : Finset Idx, ∀ u : Idx → Ideal (𝓞 K),
          (∀ y ∈ s, u y ≠ ⊥) →
          UniqueFactorizationMonoid.normalizedFactors (∏ y ∈ s, u y) =
            ∑ y ∈ s, UniqueFactorizationMonoid.normalizedFactors (u y) := by
        intro s u hu
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.prod_empty, Finset.sum_empty]
          exact UniqueFactorizationMonoid.normalizedFactors_one
        | @insert a s has ih =>
          rw [Finset.prod_insert has, Finset.sum_insert has]
          have ha : u a ≠ 0 := hu a (Finset.mem_insert_self a s)
          have hs : ∏ y ∈ s, u y ≠ 0 := by
            rw [Finset.prod_ne_zero_iff]
            intro y hy
            exact hu y (Finset.mem_insert_of_mem hy)
          rw [UniqueFactorizationMonoid.normalizedFactors_mul ha hs, ih]
          intro y hy
          exact hu y (Finset.mem_insert_of_mem hy)
      have hfac := hnorm_prod Finset.univ
        (fun y => (q₁ y).1 ^ (g y : ℕ) * (q₂ y).1 ^ (k y.1.1 - (g y : ℕ)))
        (fun y _ => mul_ne_zero (pow_ne_zero _ (hq1_ne_bot y)) (pow_ne_zero _ (hq2_ne_bot y)))
      have hcount_sum : ∀ (s : Finset Idx) (m : Idx → Multiset (Ideal (𝓞 K))),
          Multiset.count (q₁ x).1 (∑ y ∈ s, m y) = ∑ y ∈ s, Multiset.count (q₁ x).1 (m y) := by
        intro s m
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s has ih =>
          rw [Finset.sum_insert has, Finset.sum_insert has, Multiset.count_add, ih]
      change (UniqueFactorizationMonoid.normalizedFactors
        (∏ y : Idx, (q₁ y).1 ^ (g y : ℕ) * (q₂ y).1 ^ (k y.1.1 - (g y : ℕ)))).count (q₁ x).1 = _
      rw [hfac, hcount_sum]
      have hterm : ∀ y : Idx,
          (UniqueFactorizationMonoid.normalizedFactors
            ((q₁ y).1 ^ (g y : ℕ) * (q₂ y).1 ^ (k y.1.1 - (g y : ℕ)))).count (q₁ x).1 =
            if y = x then (g x : ℕ) else 0 := by
        intro y
        rw [UniqueFactorizationMonoid.normalizedFactors_mul
            (pow_ne_zero _ (hq1_ne_bot y)) (pow_ne_zero _ (hq2_ne_bot y)),
          Multiset.count_add,
          UniqueFactorizationMonoid.normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_pow]
        have hp1 : Prime (q₁ y).1 := Ideal.prime_of_isPrime (hq1_ne_bot y) (q₁ y).2.1
        have hp2 : Prime (q₂ y).1 := Ideal.prime_of_isPrime (hq2_ne_bot y) (q₂ y).2.1
        rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hp1.irreducible,
          UniqueFactorizationMonoid.normalizedFactors_irreducible hp2.irreducible,
          normalize_eq, normalize_eq]
        simp only [Multiset.count_nsmul, Multiset.count_singleton]
        have hne2 : (q₁ x).1 ≠ (q₂ y).1 := hq1_q2 x y
        rw [if_neg hne2, mul_zero, add_zero]
        by_cases hyx : y = x
        · subst hyx
          simp
        · have hne1 : (q₁ x).1 ≠ (q₁ y).1 := fun h => hyx (hq1_q1 h).symm
          rw [if_neg hne1, if_neg hyx]
          simp
      simp_rw [hterm]
      rw [Finset.sum_eq_single x (fun y _ hy => if_neg hy)
        (fun hx => absurd (Finset.mem_univ x) hx), if_pos rfl]
    have hc1 := hcount g₁
    have hc2 := hcount g₂
    rw [heq] at hc1
    omega
  obtain ⟨J₀, hJ₀_mem, B, hB_prop, hL_card⟩ := hH3 L hL_ne hL_ne_bot hL_rel
  have hJ₀_bot : J₀ ≠ ⊥ := hL_ne_bot J₀ hJ₀_mem
  have hrelNorm_J₀ : Ideal.relNorm (𝓞 F) J₀ = ∏ x : Idx, x.2.1 ^ (k x.1.1) := by
    rcases Finset.mem_image.mp hJ₀_mem with ⟨g₀, _, rfl⟩
    exact hrelNorm_J g₀
  have habsNorm_J₀ : Ideal.absNorm J₀ =
      ∏ p : {p // p ∈ S_Q},
        p.1 ^ (k p.1 * ∑ 𝔭 : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F), 𝔭.1.inertiaDeg ℤ) := by
    rw [← Ideal.absNorm_relNorm (R := 𝓞 F) (I := J₀), hrelNorm_J₀, map_prod]
    simp only [map_pow]
    have hx_norm : ∀ x : Idx, Ideal.absNorm x.2.1 = x.1.1 ^ (x.2.1.inertiaDeg ℤ) := by
      intro x
      have hp_prime : x.1.1.Prime := (hSQ x.1.1 x.1.2).1
      have hIp_ne : (Ideal.span {(x.1.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact Int.natCast_ne_zero.mpr hp_prime.ne_zero
      have hIp_max : (Ideal.span {(x.1.1 : ℤ)} : Ideal ℤ).IsMaximal :=
        ((Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp_prime.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp_prime)).isMaximal hIp_ne
      have h𝔭_ne : x.2.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hIp_ne x.2.2
      have h𝔭_max : x.2.1.IsMaximal := x.2.2.1.isMaximal h𝔭_ne
      have hlo : x.2.1.LiesOver (Ideal.span {(x.1.1 : ℤ)}) := x.2.2.2
      rw [← Ideal.absNorm_relNorm (R := ℤ) (I := x.2.1),
        Ideal.relNorm_eq_pow_of_isMaximal (R := ℤ) x.2.1 (Ideal.span {(x.1.1 : ℤ)}),
        map_pow, Ideal.absNorm_span_natCast, Module.finrank_self, pow_one]
    simp_rw [hx_norm, ← pow_mul]
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun p _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul, mul_comm]
  have hfsum_eq : ∀ p : {p // p ∈ S_Q},
      e p.1 * (∑ 𝔭 : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F), 𝔭.1.inertiaDeg ℤ) = d := by
    intro p
    have hp_prime : p.1.Prime := (hSQ p.1 p.2).1
    have hIp_prime : (Ideal.span {(p.1 : ℤ)} : Ideal ℤ).IsPrime :=
      (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp_prime.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp_prime)
    have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p.1 : ℤ)}) (𝓞 F)
    rw [hfin_Z_OF] at hsum
    rw [← hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔭 _ => ?_
    rw [(hP_hyp p.1 p.2 𝔭.1 𝔭.2).1]
  have habs_pos : 0 < Ideal.absNorm J₀ := by
    rw [habsNorm_J₀]
    refine Finset.prod_pos fun p _ => pow_pos (hSQ p.1 p.2).1.pos _
  have hL_card_eq : L.card = ∏ p : {p // p ∈ S_Q},
      (k p.1 + 1) ^ Fintype.card ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F)) := by
    rw [Finset.card_image_of_injective Finset.univ hJ_inj, Finset.card_univ,
      Fintype.card_pi, Fintype.prod_sigma]
    simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  have hprod_lb :
      ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((d : ℝ) / ((e p : ℝ) * (f p : ℝ))) ≤ (L.card : ℝ) := by
    rw [hL_card_eq, Nat.cast_prod, ← Finset.prod_coe_sort S_Q]
    refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
    have he_pos : (0 : ℝ) < e p.1 := by exact_mod_cast (hSQ p.1 p.2).2.1
    have hf_pos : (0 : ℝ) < f p.1 := by exact_mod_cast (hSQ p.1 p.2).2.2.1
    have hk_ge : (1 : ℝ) ≤ (k p.1 : ℝ) + 1 := by
      have : (0 : ℝ) ≤ k p.1 := Nat.cast_nonneg _
      linarith
    have hp_prime : p.1.Prime := (hSQ p.1 p.2).1
    have hIp_prime : (Ideal.span {(p.1 : ℤ)} : Ideal ℤ).IsPrime :=
      (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp_prime.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp_prime)
    have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p.1 : ℤ)}) (𝓞 F)
    rw [hfin_Z_OF] at hsum
    have hd_le_nat :
        d ≤ Fintype.card ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F)) * (e p.1 * f p.1) := by
      calc d = ∑ 𝔭 : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F),
              𝔭.1.ramificationIdx ℤ * 𝔭.1.inertiaDeg ℤ := hsum.symm
        _ ≤ ∑ _ : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F), e p.1 * f p.1 := by
          refine Finset.sum_le_sum fun 𝔭 _ => ?_
          rw [(hP_hyp p.1 p.2 𝔭.1 𝔭.2).1]
          exact Nat.mul_le_mul_left _ (hP_hyp p.1 p.2 𝔭.1 𝔭.2).2.1
        _ = Fintype.card ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F)) * (e p.1 * f p.1) := by
          simp [Finset.sum_const, smul_eq_mul]
    have hd_le_real : (d : ℝ) / ((e p.1 : ℝ) * (f p.1 : ℝ)) ≤
        (Fintype.card ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F)) : ℝ) := by
      rw [div_le_iff₀ (mul_pos he_pos hf_pos)]
      exact_mod_cast hd_le_nat
    calc ((k p.1 : ℝ) + 1) ^ ((d : ℝ) / ((e p.1 : ℝ) * (f p.1 : ℝ)))
        ≤ ((k p.1 : ℝ) + 1) ^
            (Fintype.card ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F)) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hk_ge hd_le_real
      _ = ((k p.1 + 1) ^ Fintype.card ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F)) : ℕ) := by
          rw [Real.rpow_natCast]
          push_cast
          rfl
  have hd_real_pos : (0 : ℝ) < d := by exact_mod_cast hd_pos
  have hcardW : Fintype.card (InfinitePlace K) = d := by
    have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at h1
    have h2 : Module.finrank ℚ K = 2 * InfinitePlace.nrComplexPlaces K :=
      IsTotallyComplex.finrank K
    have h3 : Module.finrank ℚ K = d * 2 := by
      rw [← Algebra.IsQuadraticExtension.finrank_eq_two F K]
      exact (Module.finrank_mul_finrank ℚ F K).symm
    omega
  let eW : InfinitePlace K ≃ Fin d := Fintype.equivFinOfCardEq hcardW
  let φ : Fin d → (K →+* ℂ) := fun i => (eW.symm i).embedding
  have hprod_inf : ∀ x : K, ∏ i : Fin d, ‖φ i x‖ ^ 2 = |(Algebra.norm ℚ x : ℝ)| := by
    intro x
    have hterm : ∀ i : Fin d, ‖φ i x‖ ^ 2 = (eW.symm i) x ^ (eW.symm i).mult := by
      intro i
      rw [InfinitePlace.norm_embedding_eq, IsTotallyComplex.mult_eq]
    simp_rw [hterm]
    rw [Equiv.prod_comp eW.symm (fun w : InfinitePlace K => w x ^ w.mult)]
    have hinf := InfinitePlace.prod_eq_abs_norm x
    simpa [Rat.cast_abs] using hinf
  let embedFun : K → (Fin (2 * d) → ℝ) := fun x q =>
    let p := idxEquiv d |>.symm q
    if p.2 = 0 then (φ p.1 x).re / √(d : ℝ) else (φ p.1 x).im / √(d : ℝ)
  let embed : K →+ EuclideanSpace ℝ (Fin (2 * d)) :=
    { toFun := fun x => (EuclideanSpace.equiv (Fin (2 * d)) ℝ).symm (embedFun x)
      map_zero' := by
        apply (EuclideanSpace.equiv (Fin (2 * d)) ℝ).injective
        ext q
        simp [embedFun]
      map_add' := fun x y => by
        apply (EuclideanSpace.equiv (Fin (2 * d)) ℝ).injective
        ext q
        simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply, embedFun]
        split_ifs <;> simp [add_div] }
  have hsqrt_ne : √(d : ℝ) ≠ 0 := by positivity
  have hnorm_sq : ∀ x : K, ‖embed x‖ ^ 2 = (d : ℝ)⁻¹ * ∑ i : Fin d, ‖φ i x‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    have hcomp : ∀ q : Fin (2 * d), (embed x) q = embedFun x q := fun q => rfl
    simp_rw [hcomp]
    rw [← Equiv.sum_comp (idxEquiv d)]
    have hsplit : ∀ i : Fin d,
        (∑ j : Fin 2, (embedFun x (idxEquiv d (i, j))) ^ 2) = ‖φ i x‖ ^ 2 / (d : ℝ) := by
      intro i
      rw [Fin.sum_univ_two]
      have h0 : embedFun x (idxEquiv d (i, 0)) = (φ i x).re / √(d : ℝ) := by
        simp [embedFun, Equiv.symm_apply_apply]
      have h1 : embedFun x (idxEquiv d (i, 1)) = (φ i x).im / √(d : ℝ) := by
        simp [embedFun, Equiv.symm_apply_apply]
      rw [h0, h1, div_pow, div_pow, ← add_div, Real.sq_sqrt hd_real_pos.le]
      have hz : ‖φ i x‖ ^ 2 = (φ i x).re ^ 2 + (φ i x).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      rw [hz]
    simp_rw [Fintype.sum_prod_type, hsplit, ← Finset.sum_div, div_eq_inv_mul]
  let i₀ : Fin d := ⟨0, hd_pos⟩
  have hembed_inj : Function.Injective embed := by
    intro x y hxy
    have h0 := congr_arg (fun v : EuclideanSpace ℝ (Fin (2 * d)) => v (idxEquiv d (i₀, 0))) hxy
    have h1 := congr_arg (fun v : EuclideanSpace ℝ (Fin (2 * d)) => v (idxEquiv d (i₀, 1))) hxy
    have h0' : (φ i₀ x).re / √(d : ℝ) = (φ i₀ y).re / √(d : ℝ) := by
      simpa [embed, embedFun, Equiv.symm_apply_apply] using h0
    have h1' : (φ i₀ x).im / √(d : ℝ) = (φ i₀ y).im / √(d : ℝ) := by
      simpa [embed, embedFun, Equiv.symm_apply_apply] using h1
    have hre : (φ i₀ x).re = (φ i₀ y).re := by
      have h := congr_arg (· * √(d : ℝ)) h0'
      simpa [div_mul_cancel₀ _ hsqrt_ne] using h
    have him : (φ i₀ x).im = (φ i₀ y).im := by
      have h := congr_arg (· * √(d : ℝ)) h1'
      simpa [div_mul_cancel₀ _ hsqrt_ne] using h
    exact (φ i₀).injective (Complex.ext hre him)
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * d))) :=
    { carrier := {v | ∃ x : K,
        (∀ a ∈ J₀, ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = x * algebraMap (𝓞 K) K a) ∧
        embed x = v}
      zero_mem' := ⟨0, fun a _ => ⟨0, by simp⟩, by simp⟩
      add_mem' := by
        rintro u v ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        refine ⟨x + y, fun a ha => ?_, map_add embed x y⟩
        rcases hx a ha with ⟨bx, hbx⟩
        rcases hy a ha with ⟨byy, hby⟩
        refine ⟨bx + byy, ?_⟩
        rw [map_add, hbx, hby, add_mul]
      smul_mem' := by
        rintro c v ⟨x, hx, rfl⟩
        refine ⟨(c : ℤ) • x, fun a ha => ?_, map_zsmul embed c x⟩
        rcases hx a ha with ⟨bx, hbx⟩
        refine ⟨c • bx, ?_⟩
        rw [zsmul_eq_mul, map_mul, map_intCast, hbx, zsmul_eq_mul, mul_assoc] }
  let πFun : EuclideanSpace ℝ (Fin (2 * d)) →+ ℝ² :=
    { toFun := fun v => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        ![√(d : ℝ) * v (idxEquiv d (i₀, 0)), √(d : ℝ) * v (idxEquiv d (i₀, 1))]
      map_zero' := by
        apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
        ext j
        fin_cases j <;> simp
      map_add' := fun u v => by
        apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
        ext j
        fin_cases j <;> simp [mul_add] }
  let π : Λ →+ ℝ² := πFun.comp Λ.subtype.toAddMonoidHom
  have hπ_embed : ∀ (x : K) (hx : embed x ∈ Λ),
      π ⟨embed x, hx⟩ = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(φ i₀ x).re, (φ i₀ x).im] := by
    intro x hx
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    ext j
    fin_cases j
    · simp [π, πFun, embed, embedFun, Equiv.symm_apply_apply, mul_div_cancel₀ _ hsqrt_ne]
    · simp [π, πFun, embed, embedFun, Equiv.symm_apply_apply, mul_div_cancel₀ _ hsqrt_ne]
  have hπ_norm : ∀ (x : K) (hx : embed x ∈ Λ), ‖π ⟨embed x, hx⟩‖ = ‖φ i₀ x‖ := by
    intro x hx
    rw [hπ_embed x hx]
    have hsq : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm ![(φ i₀ x).re, (φ i₀ x).im]‖ ^ 2 =
        ‖φ i₀ x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      have h0 : ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![(φ i₀ x).re, (φ i₀ x).im]) 0 =
          (φ i₀ x).re := rfl
      have h1 : ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![(φ i₀ x).re, (φ i₀ x).im]) 1 =
          (φ i₀ x).im := rfl
      rw [h0, h1, Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![(φ i₀ x).re, (φ i₀ x).im]),
      norm_nonneg (φ i₀ x)]
  have hπ_inj : Function.Injective π := by
    intro u v huv
    rcases u with ⟨u, x, hx, rfl⟩
    rcases v with ⟨v, y, hy, rfl⟩
    rw [hπ_embed x ⟨x, hx, rfl⟩, hπ_embed y ⟨y, hy, rfl⟩] at huv
    have hc := congr_arg (EuclideanSpace.equiv (Fin 2) ℝ) huv
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hc
    have hre : (φ i₀ x).re = (φ i₀ y).re := congr_fun hc 0
    have him : (φ i₀ x).im = (φ i₀ y).im := congr_fun hc 1
    have hxy : x = y := (φ i₀).injective (Complex.ext hre him)
    exact Subtype.ext (congr_arg embed hxy)
  let ρ : ℝ := (Ideal.absNorm J₀ : ℝ) ^ (-(1 : ℝ) / (2 * (d : ℝ)))
  have habs_real_pos : (0 : ℝ) < Ideal.absNorm J₀ := by exact_mod_cast habs_pos
  have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos habs_real_pos _
  have hρ_lb : ∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖ := by
    intro v hv_ne
    rcases v with ⟨v, x, hxJ, rfl⟩
    have hx0 : x ≠ 0 := by
      intro h0
      apply hv_ne
      exact Subtype.ext (by simp [h0])
    have hlow : (Ideal.absNorm J₀ : ℝ)⁻¹ ≤ |(Algebra.norm ℚ x : ℝ)| :=
      inv_ideal_norm_lower K J₀ hJ₀_bot habs_pos hx0 hxJ
    have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun _ : Fin d => (d : ℝ)⁻¹) (fun i : Fin d => ‖φ i x‖ ^ 2)
      (fun _ _ => by positivity)
      (by simp [Finset.sum_const, mul_inv_cancel₀ hd_real_pos.ne'])
      (fun _ _ => by positivity)
    have hlhs : ∏ i : Fin d, (‖φ i x‖ ^ 2) ^ (d : ℝ)⁻¹ =
        |(Algebra.norm ℚ x : ℝ)| ^ (d : ℝ)⁻¹ := by
      rw [Real.finsetProd_rpow Finset.univ (fun i : Fin d => ‖φ i x‖ ^ 2)
        (fun _ _ => by positivity), hprod_inf x]
    have hrhs : ∑ i : Fin d, (d : ℝ)⁻¹ * ‖φ i x‖ ^ 2 = ‖embed x‖ ^ 2 := by
      rw [← Finset.mul_sum, hnorm_sq x]
    have hrpow : ((Ideal.absNorm J₀ : ℝ)⁻¹) ^ (d : ℝ)⁻¹ ≤ ‖embed x‖ ^ 2 := by
      calc ((Ideal.absNorm J₀ : ℝ)⁻¹) ^ (d : ℝ)⁻¹
          ≤ |(Algebra.norm ℚ x : ℝ)| ^ (d : ℝ)⁻¹ :=
            Real.rpow_le_rpow (by positivity) hlow (by positivity)
        _ = ∏ i : Fin d, (‖φ i x‖ ^ 2) ^ (d : ℝ)⁻¹ := hlhs.symm
        _ ≤ ∑ i : Fin d, (d : ℝ)⁻¹ * ‖φ i x‖ ^ 2 := hamgm
        _ = ‖embed x‖ ^ 2 := hrhs
    have hρsq : ρ ^ 2 = ((Ideal.absNorm J₀ : ℝ)⁻¹) ^ (d : ℝ)⁻¹ := by
      dsimp [ρ]
      rw [← Real.rpow_natCast, ← Real.rpow_mul habs_real_pos.le, Real.inv_rpow habs_real_pos.le,
        ← Real.rpow_neg habs_real_pos.le]
      congr 1
      push_cast
      field_simp [hd_real_pos.ne']
    rw [← hρsq] at hrpow
    by_contra! hlt
    nlinarith [norm_nonneg (embed x), hρ_pos]
  have hρ_inv : ρ⁻¹ = ∏ p ∈ S_Q, (p : ℝ) ^ ((k p : ℝ) / (2 * (e p : ℝ))) := by
    dsimp [ρ]
    rw [neg_div, Real.rpow_neg habs_real_pos.le, inv_inv]
    rw [habsNorm_J₀, Nat.cast_prod]
    have hprod_rpow :
        (∏ p : {p // p ∈ S_Q},
          ((p.1 ^ (k p.1 * ∑ 𝔭 : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F),
            𝔭.1.inertiaDeg ℤ) : ℕ) : ℝ)) ^ (1 / (2 * (d : ℝ))) =
        ∏ p : {p // p ∈ S_Q},
          ((p.1 ^ (k p.1 * ∑ 𝔭 : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F),
            𝔭.1.inertiaDeg ℤ) : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ))) :=
      (Real.finsetProd_rpow Finset.univ _ (fun _ _ => Nat.cast_nonneg _) _).symm
    rw [hprod_rpow, ← Finset.prod_coe_sort S_Q]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hp_pos : (0 : ℝ) < p.1 := by exact_mod_cast (hSQ p.1 p.2).1.pos
    have he_pos : (0 : ℝ) < e p.1 := by exact_mod_cast (hSQ p.1 p.2).2.1
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
    congr 1
    push_cast
    have hfsum := congr_arg ((↑) : ℕ → ℝ) (hfsum_eq p)
    push_cast at hfsum
    rw [← hfsum]
    have hfsum_ne : (∑ 𝔭 : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 F),
        (𝔭.1.inertiaDeg ℤ : ℝ)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfsum
      exact hd_real_pos.ne' hfsum.symm
    field_simp [he_pos.ne', hfsum_ne]
  let toΛ : {β // β ∈ B} → Λ := fun β =>
    ⟨embed β.1, β.1, (hB_prop β.1 β.2).1, rfl⟩
  let S : Finset Λ := B.attach.image toΛ
  have hS_card : S.card = B.card := by
    rw [Finset.card_image_of_injective, Finset.card_attach]
    intro a b hab
    exact Subtype.ext (hembed_inj (congr_arg Subtype.val hab))
  have hS_norm : ∀ v ∈ S, ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖ ≤ 1 := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨⟨β, hβB⟩, _, rfl⟩
    have hnorm_all : ∀ i : Fin d, ‖φ i β‖ = 1 :=
      fun i => cm_norm_one_embedding_norm F K (hB_prop β hβB).2 (φ i)
    have hsq : ‖embed β‖ ^ 2 = 1 := by
      rw [hnorm_sq β]
      simp [hnorm_all, Finset.sum_const, inv_mul_cancel₀ hd_real_pos.ne']
    by_contra! hlt
    nlinarith [norm_nonneg (embed β)]
  have hS_π : ∀ v ∈ S, ‖π v‖ = 1 := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨⟨β, hβB⟩, _, rfl⟩
    rw [hπ_norm β ⟨β, (hB_prop β hβB).1, rfl⟩]
    exact cm_norm_one_embedding_norm F K (hB_prop β hβB).2 (φ i₀)
  refine ⟨Λ, ρ, π, S, hρ_pos, hρ_lb, hπ_inj, hS_norm, hS_π, hρ_inv.le, ?_⟩
  rw [hS_card]
  exact hprod_lb.trans hL_card

end H4Proof

theorem OMA.solution : OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1.H4 := by
  intro F K _ _ _ _ _ _ _ _ _ _ hd S_Q e f k C_loss hC hSQ hP hH3
  exact H4Proof.h4_aux F K hd S_Q e f k C_loss hC hSQ hP hH3
