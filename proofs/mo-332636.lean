import OMAStatements.S_mo_332636
import Mathlib

namespace H332636
open Matrix OMA.S_mo_332636

lemma normsq {m n : ℕ} (R : Rect m n) (v : Fin n → ℝ) :
    ‖(R.toEuclideanLin.toContinuousLinearMap) (WithLp.toLp 2 v)‖ ^ 2 = (R *ᵥ v) ⬝ᵥ (R *ᵥ v) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

lemma normsq' {n : ℕ} (v : Fin n → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

lemma inner_eq {n : ℕ} (u w : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 w) = u ⬝ᵥ w := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma adj {m n : ℕ} (R : Rect m n) (u : Fin n → ℝ) (w : Fin m → ℝ) :
    (R *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Rᵀ *ᵥ w) := by
  rw [mulVec_transpose, dotProduct_comm u, ← dotProduct_mulVec, dotProduct_comm]

lemma le_iff {m n : ℕ} (R : Rect m n) {c : ℝ} (hc : 0 ≤ c) :
    specNorm R ≤ c ↔ ∀ v, (R *ᵥ v) ⬝ᵥ (R *ᵥ v) ≤ c ^ 2 * (v ⬝ᵥ v) := by
  constructor
  · intro h v
    have h1 := (R.toEuclideanLin.toContinuousLinearMap).le_opNorm (WithLp.toLp 2 v)
    have h2 : ‖(R.toEuclideanLin.toContinuousLinearMap) (WithLp.toLp 2 v)‖ ≤ c * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ :=
      h1.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    rw [← normsq, ← normsq', ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  · intro h
    unfold specNorm
    refine ContinuousLinearMap.opNorm_le_bound _ hc ?_
    intro x
    have := h (WithLp.ofLp x)
    rw [← normsq, ← normsq'] at this
    simp only [WithLp.toLp_ofLp] at this
    rw [← mul_pow] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this

lemma eq_of_active {m n : ℕ} {R : Rect m n} {c : ℝ} {v : Fin n → ℝ} (hv : active R c v) :
    (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = c ^ 2 * (v ⬝ᵥ v) := by
  rw [adj, hv, dotProduct_smul, smul_eq_mul]

lemma zero_of_quad (A B : ℝ) (h : ∀ t : ℝ, 2 * t * A + t ^ 2 * B ≤ 0) : A = 0 := by
  have hk : 0 < |B| + 1 := by positivity
  have h1 := h (A / (|B| + 1))
  have h2 : A ^ 2 * (2 * (|B| + 1) + B) ≤ 0 := by
    have : 2 * (A / (|B| + 1)) * A + (A / (|B| + 1)) ^ 2 * B
        = A ^ 2 * (2 * (|B| + 1) + B) / (|B| + 1) ^ 2 := by
      field_simp
    rw [this] at h1
    exact (div_nonpos_iff.mp h1).elim (fun h => absurd h.2 (not_le.mpr (by positivity))) (fun h => h.1)
  have h3 : 0 < 2 * (|B| + 1) + B := by
    have := neg_abs_le B
    linarith
  have : A ^ 2 ≤ 0 := by
    by_contra hh
    push Not at hh
    have := mul_pos hh h3
    linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg A))

lemma active_of_eq {m n : ℕ} {R : Rect m n} {c : ℝ}
    (hR : ∀ u, (R *ᵥ u) ⬝ᵥ (R *ᵥ u) ≤ c ^ 2 * (u ⬝ᵥ u)) {v : Fin n → ℝ}
    (hv : (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = c ^ 2 * (v ⬝ᵥ v)) : active R c v := by
  have key : ∀ u, (R *ᵥ v) ⬝ᵥ (R *ᵥ u) - c ^ 2 * (v ⬝ᵥ u) = 0 := by
    intro u
    apply zero_of_quad _ ((R *ᵥ u) ⬝ᵥ (R *ᵥ u) - c ^ 2 * (u ⬝ᵥ u))
    intro t
    have := hR (v + t • u)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_comm (R *ᵥ u) (R *ᵥ v), dotProduct_comm u v] at this
    nlinarith [this, hv]
  obtain ⟨z, hz⟩ : ∃ z, z = Rᵀ *ᵥ (R *ᵥ v) - c ^ 2 • v := ⟨_, rfl⟩
  have hz0 : z ⬝ᵥ z = 0 := by
    have h1 := key z
    have e : (R *ᵥ v) ⬝ᵥ (R *ᵥ z) = (Rᵀ *ᵥ (R *ᵥ v)) ⬝ᵥ z := by
      rw [dotProduct_comm, adj, dotProduct_comm]
    rw [e] at h1
    have e2 : z ⬝ᵥ z = (Rᵀ *ᵥ (R *ᵥ v)) ⬝ᵥ z - c ^ 2 * (v ⬝ᵥ z) := by
      rw [hz]
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [e2, h1]
  have : z = 0 := dotProduct_self_eq_zero.mp hz0
  unfold active
  rw [hz] at this
  exact sub_eq_zero.mp this

end H332636

namespace H332636
open Matrix OMA.S_mo_332636

def actSub {m n : ℕ} (R0 : Rect m n) (c : ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {x | active R0 c (WithLp.ofLp x)}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, active] at hx hy ⊢
    simp [mulVec_add, hx, hy, smul_add]
  zero_mem' := by simp [active]
  smul_mem' := by
    intro t x hx
    simp only [Set.mem_ofPred_eq, active] at hx ⊢
    simp [mulVec_smul, hx, smul_comm t]

lemma gapc {m n : ℕ} (R0 : Rect m n) {c : ℝ} (hc : 0 < c)
    (hR : ∀ u, (R0 *ᵥ u) ⬝ᵥ (R0 *ᵥ u) ≤ c ^ 2 * (u ⬝ᵥ u)) :
    ∃ c', 0 ≤ c' ∧ c' < c ∧ ∀ b ∈ (actSub R0 c)ᗮ,
      ‖(R0.toEuclideanLin.toContinuousLinearMap) b‖ ≤ c' * ‖b‖ := by
  set A := actSub R0 c
  set T0 := R0.toEuclideanLin.toContinuousLinearMap
  have hsq : ∀ b : EuclideanSpace ℝ (Fin n), ‖T0 b‖ ^ 2 ≤ c ^ 2 * ‖b‖ ^ 2 := by
    intro b
    have := hR (WithLp.ofLp b)
    rw [← normsq, ← normsq'] at this
    simp only [WithLp.toLp_ofLp] at this
    exact this
  have hle : ∀ b : EuclideanSpace ℝ (Fin n), ‖T0 b‖ ≤ c * ‖b‖ := by
    intro b
    have := hsq b
    rw [← mul_pow] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this
  set S := (Aᗮ : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.sphere 0 1
  have hcomp : IsCompact S := (isCompact_sphere 0 1).inter_left (Submodule.isClosed_orthogonal A)
  have hnorm : ∀ b ∈ Aᗮ, b ≠ 0 → ‖b‖⁻¹ • b ∈ S := by
    intro b hb hb0
    refine ⟨Aᗮ.smul_mem _ hb, ?_⟩
    simp [norm_smul, hb0]
  by_cases hS : S.Nonempty
  · obtain ⟨b0, hb0, hmax⟩ := hcomp.exists_isMaxOn hS
      (continuous_norm.comp T0.continuous).continuousOn
    refine ⟨‖T0 b0‖, norm_nonneg _, ?_, ?_⟩
    · have h1 : ‖b0‖ = 1 := by simpa using hb0.2
      have h2 := hle b0
      rw [h1, mul_one] at h2
      refine lt_of_le_of_ne h2 ?_
      intro heq
      have hact : b0 ∈ A := by
        show active R0 c (WithLp.ofLp b0)
        apply active_of_eq hR
        rw [← normsq, ← normsq']
        simp only [WithLp.toLp_ofLp]
        rw [show T0 b0 = R0.toEuclideanLin.toContinuousLinearMap b0 from rfl] at heq
        rw [heq, h1]; ring
      have hz := Submodule.inner_right_of_mem_orthogonal hact hb0.1
      rw [real_inner_self_eq_norm_sq, h1] at hz
      norm_num at hz
    · intro b hb
      by_cases hb0' : b = 0
      · simp [hb0']
      · have := hmax (hnorm b hb hb0')
        simp only [Function.comp_apply, Set.mem_ofPred_eq, map_smul, norm_smul, norm_inv,
          norm_norm] at this
        have hpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0'
        rw [inv_mul_le_iff₀ hpos] at this
        linarith [mul_comm ‖b‖ ‖T0 b0‖]
  · refine ⟨0, le_refl _, hc, ?_⟩
    intro b hb
    by_cases hb0' : b = 0
    · simp [hb0']
    · exact absurd ⟨_, hnorm b hb hb0'⟩ hS

end H332636

namespace H332636
open Matrix OMA.S_mo_332636

lemma perturb {m n : ℕ} (R0 H : Rect m n) {c : ℝ} (hc : 0 < c)
    (hR : ∀ u, (R0 *ᵥ u) ⬝ᵥ (R0 *ᵥ u) ≤ c ^ 2 * (u ⬝ᵥ u))
    (hH : ∀ v, active R0 c v → H *ᵥ v = 0 ∧ Hᵀ *ᵥ (R0 *ᵥ v) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ((R0 - ε • H) *ᵥ x) ⬝ᵥ ((R0 - ε • H) *ᵥ x) ≤ c ^ 2 * (x ⬝ᵥ x) := by
  obtain ⟨c', hc'0, hc'c, hgap⟩ := gapc R0 hc hR
  set A := actSub R0 c
  set h := specNorm H
  have h0 : 0 ≤ h := norm_nonneg _
  refine ⟨(c - c') / (h + 1), by apply div_pos <;> linarith, ?_⟩
  set ε := (c - c') / (h + 1) with hε
  have hε0 : 0 < ε := by apply div_pos <;> linarith
  have hεh : ε * h ≤ c - c' := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  intro x
  set X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  set a := A.starProjection X
  set b := X - a
  have ha : a ∈ A := A.starProjection_apply_mem X
  have hb : b ∈ Aᗮ := A.sub_starProjection_mem_orthogonal X
  set ua := WithLp.ofLp a
  set ub := WithLp.ofLp b
  have hx : x = ua + ub := by
    simp [ua, ub, b, X]
  have hact : active R0 c ua := ha
  have hab : ua ⬝ᵥ ub = 0 := by
    have := Submodule.inner_right_of_mem_orthogonal ha hb
    rw [← inner_eq]
    simpa [ua, ub] using this
  obtain ⟨hHa, hHta⟩ := hH ua hact
  -- the bound on the orthogonal part
  have hbnd : ((R0 - ε • H) *ᵥ ub) ⬝ᵥ ((R0 - ε • H) *ᵥ ub) ≤ c ^ 2 * (ub ⬝ᵥ ub) := by
    have e1 : WithLp.toLp 2 ((R0 - ε • H) *ᵥ ub) =
        (R0.toEuclideanLin.toContinuousLinearMap) b - ε • (H.toEuclideanLin.toContinuousLinearMap) b := by
      simp only [sub_mulVec, smul_mulVec]
      rfl
    have n1 := hgap b hb
    have n2 : ‖(H.toEuclideanLin.toContinuousLinearMap) b‖ ≤ h * ‖b‖ :=
      (H.toEuclideanLin.toContinuousLinearMap).le_opNorm b
    have n3 : ‖WithLp.toLp 2 ((R0 - ε • H) *ᵥ ub)‖ ≤ c * ‖b‖ := by
      rw [e1]
      calc _ ≤ ‖(R0.toEuclideanLin.toContinuousLinearMap) b‖ + ‖ε • (H.toEuclideanLin.toContinuousLinearMap) b‖ :=
            norm_sub_le _ _
        _ ≤ c' * ‖b‖ + ε * (h * ‖b‖) := by
            rw [norm_smul, Real.norm_of_nonneg hε0.le]
            gcongr
        _ ≤ c * ‖b‖ := by nlinarith [norm_nonneg b]
    have n4 := pow_le_pow_left₀ (norm_nonneg _) n3 2
    rw [normsq', mul_pow] at n4
    have : ‖b‖ ^ 2 = ub ⬝ᵥ ub := by
      rw [← normsq']
    rw [this] at n4
    exact n4
  have hsplit : (R0 - ε • H) *ᵥ x = R0 *ᵥ ua + (R0 - ε • H) *ᵥ ub := by
    rw [hx, mulVec_add]
    congr 1
    rw [sub_mulVec, smul_mulVec, hHa, smul_zero, sub_zero]
  have hcross : (R0 *ᵥ ua) ⬝ᵥ ((R0 - ε • H) *ᵥ ub) = 0 := by
    rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_comm,
      adj, hact, dotProduct_comm (R0 *ᵥ ua), adj, hHta]
    simp [dotProduct_smul, dotProduct_comm ub ua, hab]
  have hQa := eq_of_active hact
  rw [hsplit, hx]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm ((R0 - ε • H) *ᵥ ub) (R0 *ᵥ ua), hcross, dotProduct_comm ub ua, hab, hQa]
  nlinarith [hbnd]

end H332636

namespace H332636
open Matrix OMA.S_mo_332636

lemma dsn {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

lemma mid_bound {n : ℕ} (a b : Fin n → ℝ) :
    ((1 / 2 : ℝ) • (a + b)) ⬝ᵥ ((1 / 2 : ℝ) • (a + b)) =
      (a ⬝ᵥ a + b ⬝ᵥ b) / 2 - ((a - b) ⬝ᵥ (a - b)) / 4 := by
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub, smul_eq_mul, dotProduct_comm b a]
  ring

lemma key {m n : ℕ} {L : Submodule ℝ (Rect m n)} {X : Rect m n} {c : ℝ} (hc : 0 < c)
    (hlow : ∀ M ∈ L, c ≤ specNorm (X - M)) {M M0 : Rect m n}
    (hM : M ∈ opt L X c) (hM0 : M0 ∈ opt L X c) :
    (1 / 2 : ℝ) • (M + M0) ∈ opt L X c ∧
    ∀ v, active (X - (1 / 2 : ℝ) • (M + M0)) c v →
      (X - M) *ᵥ v = (X - M0) *ᵥ v ∧ active (X - M) c v ∧ active (X - M0) c v := by
  have hb1 := (le_iff _ hc.le).1 hM.2.le
  have hb0 := (le_iff _ hc.le).1 hM0.2.le
  have hN : X - (1 / 2 : ℝ) • (M + M0) = (1 / 2 : ℝ) • ((X - M) + (X - M0)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hNv : ∀ u, (X - (1 / 2 : ℝ) • (M + M0)) *ᵥ u = (1 / 2 : ℝ) • ((X - M) *ᵥ u + (X - M0) *ᵥ u) := by
    intro u
    rw [hN, smul_mulVec, add_mulVec]
  have hNb : ∀ u, ((X - (1 / 2 : ℝ) • (M + M0)) *ᵥ u) ⬝ᵥ ((X - (1 / 2 : ℝ) • (M + M0)) *ᵥ u)
      ≤ c ^ 2 * (u ⬝ᵥ u) := by
    intro u
    rw [hNv, mid_bound]
    have := dsn ((X - M) *ᵥ u - (X - M0) *ᵥ u)
    nlinarith [hb1 u, hb0 u]
  have hNL : (1 / 2 : ℝ) • (M + M0) ∈ L := L.smul_mem _ (L.add_mem hM.1 hM0.1)
  refine ⟨⟨hNL, le_antisymm ((le_iff _ hc.le).2 hNb) (hlow _ hNL)⟩, ?_⟩
  intro v hv
  have hq := eq_of_active hv
  rw [hNv, mid_bound] at hq
  have h1 := hb1 v
  have h0 := hb0 v
  have hd := dsn ((X - M) *ᵥ v - (X - M0) *ᵥ v)
  have hd0 : ((X - M) *ᵥ v - (X - M0) *ᵥ v) ⬝ᵥ ((X - M) *ᵥ v - (X - M0) *ᵥ v) = 0 := by
    nlinarith
  have heq : (X - M) *ᵥ v = (X - M0) *ᵥ v := sub_eq_zero.mp (dotProduct_self_eq_zero.mp hd0)
  rw [heq, sub_self, dotProduct_zero] at hq
  refine ⟨heq, active_of_eq hb1 ?_, active_of_eq hb0 ?_⟩
  · rw [heq]; linarith
  · linarith

end H332636

open Matrix OMA.S_mo_332636 H332636 in
theorem OMA.solution : type_of% @OMA.S_mo_332636.main := by
  intro m n L X c hc hleast
  obtain ⟨⟨M1, hM1L, hM1eq⟩, hlow⟩ := hleast
  have hlow' : ∀ M ∈ L, c ≤ specNorm (X - M) := fun M hM => hlow ⟨M, hM, rfl⟩
  have hne : (opt L X c).Nonempty := ⟨M1, hM1L, hM1eq⟩
  let f : Rect m n → ℕ := fun M => Module.finrank ℝ (actSub (X - M) c)
  set M0 := Function.argminOn f (opt L X c) hne with hM0def
  have hM0 : M0 ∈ opt L X c := Function.argminOn_mem f _ hne
  have hmin : ∀ M ∈ opt L X c, f M0 ≤ f M := fun M hM => not_lt.1 (Function.not_lt_argminOn f _ hM)
  have hkey : ∀ M ∈ opt L X c, ∀ v, active (X - M0) c v →
      (X - M) *ᵥ v = (X - M0) *ᵥ v ∧ active (X - M) c v := by
    intro M hM v hv
    obtain ⟨hNopt, hNact⟩ := key hc hlow' hM hM0
    have hle : actSub (X - (1 / 2 : ℝ) • (M + M0)) c ≤ actSub (X - M0) c :=
      fun w hw => (hNact _ hw).2.2
    have heq := Submodule.eq_of_le_of_finrank_le hle (hmin _ hNopt)
    have hv' : WithLp.toLp 2 v ∈ actSub (X - M0) c := hv
    rw [← heq] at hv'
    obtain ⟨h1, h2, _⟩ := hNact _ hv'
    exact ⟨h1, h2⟩
  have hC3 : ∀ M ∈ opt L X c, ∀ v, active (X - M0) c v →
      (X - M) *ᵥ v = (X - M0) *ᵥ v ∧ (X - M)ᵀ *ᵥ ((X - M0) *ᵥ v) = c ^ 2 • v := by
    intro M hM v hv
    obtain ⟨h1, h2⟩ := hkey M hM v hv
    exact ⟨h1, by rw [← h1]; exact h2⟩
  have hspan : Submodule.span ℝ ((fun M => M - M0) '' opt L X c) = directions L (X - M0) c := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨M, hM, rfl⟩
      refine ⟨L.sub_mem hM.1 hM0.1, fun v hv => ?_⟩
      obtain ⟨h1, h2⟩ := hC3 M hM v hv
      show (M - M0) *ᵥ v = 0 ∧ (M - M0)ᵀ *ᵥ ((X - M0) *ᵥ v) = 0
      have e : M - M0 = (X - M0) - (X - M) := by abel
      constructor
      · rw [e, Matrix.sub_mulVec (X - M0) (X - M) v, h1, sub_self]
      · rw [e, transpose_sub, Matrix.sub_mulVec (X - M0)ᵀ (X - M)ᵀ, h2]
        unfold active at hv
        rw [hv, sub_self]
    · rintro H ⟨hHL, hHa⟩
      obtain ⟨ε, hε, hQ⟩ := perturb (X - M0) H hc ((le_iff _ hc.le).1 hM0.2.le) hHa
      have hM'L : M0 + ε • H ∈ L := L.add_mem hM0.1 (L.smul_mem _ hHL)
      have hX : X - (M0 + ε • H) = (X - M0) - ε • H := by abel
      have hM' : M0 + ε • H ∈ opt L X c :=
        ⟨hM'L, le_antisymm (by rw [hX]; exact (le_iff _ hc.le).2 hQ) (hlow' _ hM'L)⟩
      have e : H = ε⁻¹ • ((M0 + ε • H) - M0) := by
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hM', rfl⟩)
  refine ⟨M0, hM0, hspan, ?_, hC3⟩
  constructor
  · rintro ⟨M', _, huniq⟩
    rw [← hspan, Submodule.span_eq_bot]
    rintro _ ⟨M, hM, rfl⟩
    dsimp only
    rw [huniq M hM, huniq M0 hM0, sub_self]
  · intro hbot
    refine ⟨M0, hM0, fun M hM => ?_⟩
    have hmem : M - M0 ∈ Submodule.span ℝ ((fun M => M - M0) '' opt L X c) :=
      Submodule.subset_span ⟨M, hM, rfl⟩
    rw [hspan, hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
