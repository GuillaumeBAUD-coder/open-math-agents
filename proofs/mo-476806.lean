import OMAStatements.S_mo_476806
import Mathlib

namespace OMA.P476806
open Matrix Finset OMA.S_mo_476806

section generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pd_iff (A : Matrix ι ι ℝ) :
    A.PosDef ↔ Aᵀ = A ∧ ∀ x : ι → ℝ, x ≠ 0 → 0 < quad A x := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  simp [quad, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]

lemma pd_sym {A : Matrix ι ι ℝ} (h : A.PosDef) : Aᵀ = A := ((pd_iff A).1 h).1

lemma pd_pos {A : Matrix ι ι ℝ} (h : A.PosDef) {x : ι → ℝ} (hx : x ≠ 0) : 0 < quad A x :=
  ((pd_iff A).1 h).2 x hx

lemma pd_nonneg {A : Matrix ι ι ℝ} (h : A.PosDef) (x : ι → ℝ) : 0 ≤ quad A x := by
  by_cases hx : x = 0
  · subst hx; simp [quad]
  · exact (pd_pos h hx).le

lemma pd_mul_inv {A : Matrix ι ι ℝ} (h : A.PosDef) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 h.isUnit)

lemma pd_inv_mul {A : Matrix ι ι ℝ} (h : A.PosDef) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 h.isUnit)

lemma sym_swap {A : Matrix ι ι ℝ} (h : Aᵀ = A) (x y : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h, dotProduct_comm]

lemma quad_add (A B : Matrix ι ι ℝ) (x : ι → ℝ) : quad (A + B) x = quad A x + quad B x := by
  simp [quad, Matrix.add_mulVec, dotProduct_add]

lemma quad_sub_vec {A : Matrix ι ι ℝ} (h : Aᵀ = A) (x y : ι → ℝ) :
    quad A (x - y) = quad A x - 2 * (x ⬝ᵥ (A *ᵥ y)) + quad A y := by
  simp only [quad, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [sym_swap h y x]; ring

/-- variational identity -/
lemma var_id {A : Matrix ι ι ℝ} (h : A.PosDef) (v x : ι → ℝ) :
    quad A⁻¹ v = 2 * (v ⬝ᵥ x) - quad A x + quad A (x - A⁻¹ *ᵥ v) := by
  rw [quad_sub_vec (pd_sym h)]
  have h1 : A *ᵥ (A⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, pd_mul_inv h, Matrix.one_mulVec]
  simp only [quad, h1]
  rw [dotProduct_comm x v, dotProduct_comm (A⁻¹ *ᵥ v) v]; ring

lemma var_le {A : Matrix ι ι ℝ} (h : A.PosDef) (v x : ι → ℝ) :
    2 * (v ⬝ᵥ x) - quad A x ≤ quad A⁻¹ v := by
  rw [var_id h v x]; linarith [pd_nonneg h (x - A⁻¹ *ᵥ v)]

lemma var_eq {A : Matrix ι ι ℝ} (h : A.PosDef) (v : ι → ℝ) :
    quad A⁻¹ v = 2 * (v ⬝ᵥ (A⁻¹ *ᵥ v)) - quad A (A⁻¹ *ᵥ v) := by
  rw [var_id h v (A⁻¹ *ᵥ v)]; simp [quad]

lemma disc {α β γ : ℝ} (hg0 : 0 ≤ γ) (h : ∀ t : ℝ, 0 ≤ α - 2 * t * β + t ^ 2 * γ) :
    β ^ 2 ≤ α * γ := by
  rcases lt_or_eq_of_le hg0 with hg | hg
  · have := h (β / γ)
    have e : α - 2 * (β / γ) * β + (β / γ) ^ 2 * γ = (α * γ - β ^ 2) / γ := by
      field_simp; ring
    rw [e] at this
    have := mul_nonneg this hg.le
    rw [div_mul_cancel₀ _ hg.ne'] at this
    linarith
  · subst hg
    by_contra hb
    have hb0 : β ≠ 0 := by rintro rfl; simp at hb
    have := h ((α + 1) / (2 * β))
    have e : α - 2 * ((α + 1) / (2 * β)) * β + ((α + 1) / (2 * β)) ^ 2 * 0 = -1 := by
      field_simp; ring
    linarith

lemma cs {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (hn : ∀ x, 0 ≤ quad A x) (p q : ι → ℝ) :
    (p ⬝ᵥ (A *ᵥ q)) ^ 2 ≤ quad A p * quad A q := by
  apply disc (hn q)
  intro t
  have := hn (p - t • q)
  rw [quad_sub_vec hs] at this
  simpa [quad, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, pow_two, mul_assoc, mul_comm, mul_left_comm] using this

end generic

section spec
variable {n : ℕ}

def wv (v : Vec n) : Fin n × Fin 2 → ℝ := fun i => v i.1
def c0 (ξ : Fin n × Fin 2 → ℝ) : Fin n → ℝ := fun i => ξ (i, 0)
def c1 (ξ : Fin n × Fin 2 → ℝ) : Fin n → ℝ := fun i => ξ (i, 1)

lemma quad2 (M : Sq 2) (u : Fin 2 → ℝ) :
    quad M u = M 0 0 * u 0 ^ 2 + (M 0 1 + M 1 0) * u 0 * u 1 + M 1 1 * u 1 ^ 2 := by
  simp [quad, dotProduct, Matrix.mulVec, Fin.sum_univ_two]; ring

lemma quad_lift2 (M : Sq 2) (ξ : Fin n × Fin 2 → ℝ) :
    quad (lift2 n M) ξ = ∑ i, quad M (fun p => ξ (i, p)) := by
  simp only [quad, dotProduct, Matrix.mulVec, lift2, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

lemma quad_blk (P Q : Sq n) (ξ : Fin n × Fin 2 → ℝ) :
    quad (blockDiagonal ![P, Q]) ξ = quad P (c0 ξ) + quad Q (c1 ξ) := by
  simp only [quad, dotProduct, Matrix.mulVec, blockDiagonal_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, c0, c1]
  simp [Finset.sum_add_distrib]

lemma dot_w (v : Vec n) (ξ : Fin n × Fin 2 → ℝ) :
    wv v ⬝ᵥ ξ = v ⬝ᵥ c0 ξ + v ⬝ᵥ c1 ξ := by
  simp [dotProduct, wv, c0, c1, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib,
    mul_add]

lemma blk_sym {P Q : Sq n} (hP : Pᵀ = P) (hQ : Qᵀ = Q) : (blockDiagonal ![P, Q])ᵀ = blockDiagonal ![P, Q] := by
  rw [blockDiagonal_transpose]
  congr 1
  ext k : 1
  fin_cases k <;> simp [hP, hQ]

lemma blk_pd {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) : (blockDiagonal ![P, Q]).PosDef := by
  rw [pd_iff]
  refine ⟨blk_sym (pd_sym hP) (pd_sym hQ), fun ξ hξ => ?_⟩
  rw [quad_blk]
  by_cases h0 : c0 ξ = 0
  · have h1 : c1 ξ ≠ 0 := by
      intro h1; apply hξ; ext ⟨i, k⟩
      fin_cases k
      · exact congrFun h0 i
      · exact congrFun h1 i
    linarith [pd_nonneg hP (c0 ξ), pd_pos hQ h1]
  · linarith [pd_pos hP h0, pd_nonneg hQ (c1 ξ)]

lemma lift2_transpose (M : Sq 2) : (lift2 n M)ᵀ = lift2 n Mᵀ := by
  ext i j; simp [lift2, eq_comm]

lemma lift2_mul (A B : Sq 2) : lift2 n A * lift2 n B = lift2 n (A * B) := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp only [lift2, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = j <;> simp [h]
  · intro k _ hk; simp [Ne.symm hk]
  · simp

lemma lift2_one : lift2 n (1 : Sq 2) = 1 := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp only [lift2, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h : i = j <;> by_cases h' : p = q <;> simp [h, h']

lemma small_sym (a b : ℝ) : (small a b)ᵀ = small a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [small]

lemma det_small (a b : ℝ) : (small a b).det = a * (1 - a) - b ^ 2 := by
  simp [small, Matrix.det_fin_two_of]; ring

lemma small_inv {a b : ℝ} (h : a * (1 - a) - b ^ 2 ≠ 0) :
    (small a b)⁻¹ = !![(1 - a) / (a * (1 - a) - b ^ 2), -b / (a * (1 - a) - b ^ 2);
      -b / (a * (1 - a) - b ^ 2), a / (a * (1 - a) - b ^ 2)] := by
  apply Matrix.inv_eq_right_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [small, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

lemma quadK (a b : ℝ) (y : Fin n × Fin 2 → ℝ) :
    quad (lift2 n (small a b)) y = ∑ i, y (i, 1) ^ 2 + a * (score y).1 + b * (score y).2 := by
  rw [quad_lift2]
  simp only [quad2, score, small]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp; ring

end spec

section dsk
variable {n : ℕ}

noncomputable def Sm (P Q : Sq n) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  (blockDiagonal ![P, Q])⁻¹
noncomputable def Km (n : ℕ) (z : ℝ × ℝ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  lift2 n (small z.1 z.2)
noncomputable def Gf (P Q : Sq n) (v : Vec n) (y : Fin n × Fin 2 → ℝ) (z : ℝ × ℝ) : ℝ :=
  quad (Sm P Q) (wv v - y) + quad (Km n z) y

lemma S_pd {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) : (Sm P Q).PosDef :=
  (blk_pd hP hQ).inv

lemma small_nonneg {a b : ℝ} (h : (a - 1/2) ^ 2 + b ^ 2 ≤ 1/4) (u : Fin 2 → ℝ) :
    0 ≤ quad (small a b) u := by
  rw [quad2]; simp only [small, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, head_cons]
  have hD : 0 ≤ a * (1 - a) - b ^ 2 := by nlinarith
  nlinarith [sq_nonneg (a * u 0 + b * u 1), sq_nonneg (b * u 0 + (1 - a) * u 1),
    mul_nonneg hD (add_nonneg (sq_nonneg (u 0)) (sq_nonneg (u 1)))]

lemma K_nonneg {z : ℝ × ℝ} (hz : z ∈ disk) (y : Fin n × Fin 2 → ℝ) : 0 ≤ quad (Km n z) y := by
  rw [Km, quad_lift2]
  exact Finset.sum_nonneg fun i _ => small_nonneg hz _

lemma K_sym (z : ℝ × ℝ) : (Km n z)ᵀ = Km n z := by
  rw [Km, lift2_transpose, small_sym]

lemma A_pd {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) {z : ℝ × ℝ} (hz : z ∈ disk) :
    (Km n z + Sm P Q).PosDef := by
  rw [pd_iff]
  refine ⟨by rw [Matrix.transpose_add, K_sym, pd_sym (S_pd hP hQ)], fun y hy => ?_⟩
  rw [quad_add]
  linarith [K_nonneg hz y, pd_pos (S_pd hP hQ) hy]

lemma resp_eq (P Q : Sq n) (v : Vec n) (z : ℝ × ℝ) :
    response P Q v z = (Km n z + Sm P Q)⁻¹ *ᵥ (Sm P Q *ᵥ wv v) := rfl

lemma G_form {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) (y : Fin n × Fin 2 → ℝ)
    (z : ℝ × ℝ) :
    Gf P Q v y z = quad (Sm P Q) (wv v) -
      (2 * ((Sm P Q *ᵥ wv v) ⬝ᵥ y) - quad (Km n z + Sm P Q) y) := by
  have hs := pd_sym (S_pd hP hQ)
  rw [Gf, quad_sub_vec hs, quad_add, dotProduct_comm (Sm P Q *ᵥ wv v) y,
    sym_swap hs y (wv v)]
  ring

lemma G_ge {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {z : ℝ × ℝ} (hz : z ∈ disk)
    (y : Fin n × Fin 2 → ℝ) : Gf P Q v (response P Q v z) z ≤ Gf P Q v y z := by
  have hA := A_pd hP hQ hz
  rw [G_form hP hQ, G_form hP hQ, resp_eq, ← var_eq hA]
  linarith [var_le hA (Sm P Q *ᵥ wv v) y]

lemma dv_eq {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {z : ℝ × ℝ} (hz : z ∈ disk) :
    diskValue P Q v z.1 z.2 = Gf P Q v (response P Q v z) z := by
  have hA := A_pd hP hQ hz
  have hs := pd_sym (S_pd hP hQ)
  rw [G_form hP hQ, resp_eq, ← var_eq hA]
  have e : diskValue P Q v z.1 z.2 = quad (Sm P Q * (Km n z + Sm P Q)⁻¹ * Km n z) (wv v) := rfl
  have e2 : Sm P Q * (Km n z + Sm P Q)⁻¹ * Km n z =
      Sm P Q - Sm P Q * (Km n z + Sm P Q)⁻¹ * Sm P Q := by
    have h3 : Sm P Q * (Km n z + Sm P Q)⁻¹ * (Km n z + Sm P Q) = Sm P Q := by
      rw [Matrix.mul_assoc, pd_inv_mul hA, Matrix.mul_one]
    rw [Matrix.mul_add] at h3
    exact eq_sub_of_add_eq h3
  rw [e, e2]
  simp only [quad, Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec]
  rw [sym_swap hs (wv v) ((Km n z + Sm P Q)⁻¹ *ᵥ (Sm P Q *ᵥ wv v)),
    dotProduct_comm ((Km n z + Sm P Q)⁻¹ *ᵥ Sm P Q *ᵥ wv v)]

lemma G_aff (P Q : Sq n) (v : Vec n) (y : Fin n × Fin 2 → ℝ) (z z' : ℝ × ℝ) :
    Gf P Q v y z' = Gf P Q v y z + (score y).1 * (z'.1 - z.1) + (score y).2 * (z'.2 - z.2) := by
  simp only [Gf, Km, quadK]; ring

end dsk

section geo

lemma geo1 {z d : ℝ × ℝ} (ho : optimality z d) (u : ℝ × ℝ) (hu : u ∈ disk) :
    d.1 * (u.1 - z.1) + d.2 * (u.2 - z.2) ≤ 0 := by
  obtain ⟨h1, h2⟩ := ho
  simp only [disk, Set.mem_setOf_eq] at hu
  set s := (z.1 - 1/2) * d.1 + z.2 * d.2 with hs
  set m := d.1 * (u.1 - 1/2) + d.2 * u.2 with hm
  have hm2 : m ^ 2 ≤ s ^ 2 := by
    have : m ^ 2 + (d.1 * u.2 - d.2 * (u.1 - 1/2)) ^ 2 = (d.1 ^ 2 + d.2 ^ 2) * ((u.1 - 1/2) ^ 2 + u.2 ^ 2) := by
      rw [hm]; ring
    nlinarith [sq_nonneg (d.1 * u.2 - d.2 * (u.1 - 1/2)), sq_nonneg d.1, sq_nonneg d.2]
  have hms : m ≤ s := by nlinarith [sq_nonneg (m - s), sq_nonneg (m + s)]
  have : d.1 * (u.1 - z.1) + d.2 * (u.2 - z.2) = m - s := by rw [hm, hs]; ring
  linarith

lemma geo2 {z d : ℝ × ℝ} (hz : z ∈ disk)
    (h : ∀ u ∈ disk, d.1 * (u.1 - z.1) + d.2 * (u.2 - z.2) ≤ 0) : optimality z d := by
  simp only [disk, Set.mem_setOf_eq] at hz
  by_cases hd : d.1 ^ 2 + d.2 ^ 2 = 0
  · have e1 : d.1 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
    have e2 : d.2 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
    simp [optimality, e1, e2]
  have hpos : 0 < d.1 ^ 2 + d.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hd)
  set N := Real.sqrt (d.1 ^ 2 + d.2 ^ 2) with hN
  have hN0 : 0 < N := Real.sqrt_pos.2 hpos
  have hNN : N ^ 2 = d.1 ^ 2 + d.2 ^ 2 := Real.sq_sqrt hpos.le
  have hu := h (1/2 + d.1 / (2 * N), d.2 / (2 * N)) (by
    simp only [disk, Set.mem_setOf_eq]
    field_simp
    nlinarith)
  simp only at hu
  set s := (z.1 - 1/2) * d.1 + z.2 * d.2 with hs
  have e : d.1 * (1 / 2 + d.1 / (2 * N) - z.1) + d.2 * (d.2 / (2 * N) - z.2) = N / 2 - s := by
    rw [hs]; field_simp; nlinarith
  rw [e] at hu
  have hs2 : s ^ 2 ≤ N ^ 2 / 4 := by
    have : s ^ 2 + ((z.1 - 1/2) * d.2 - z.2 * d.1) ^ 2 = (d.1 ^ 2 + d.2 ^ 2) * ((z.1 - 1/2) ^ 2 + z.2 ^ 2) := by
      rw [hs]; ring
    nlinarith [sq_nonneg ((z.1 - 1/2) * d.2 - z.2 * d.1)]
  have hsN : s ≤ N / 2 := by nlinarith [sq_nonneg (s - N / 2), sq_nonneg (s + N/2)]
  have : s = N / 2 := by linarith
  refine ⟨by rw [← hs]; linarith, ?_⟩
  rw [← hs, this, ← hNN]; ring

lemma disk_seg {z u : ℝ × ℝ} (hz : z ∈ disk) (hu : u ∈ disk) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (z.1 + t * (u.1 - z.1), z.2 + t * (u.2 - z.2)) ∈ disk := by
  simp only [disk, Set.mem_setOf_eq] at *
  have ht : 0 ≤ t * (1 - t) := mul_nonneg h0 (by linarith)
  nlinarith [mul_nonneg ht (sq_nonneg (z.1 - u.1)), mul_nonneg ht (sq_nonneg (z.2 - u.2)),
    mul_nonneg h0 h0, mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)]

lemma disk_compact : IsCompact disk := by
  apply (isCompact_Icc.prod isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1)).of_isClosed_subset
  · exact isClosed_le (by fun_prop) continuous_const
  · intro z hz
    simp only [disk, Set.mem_setOf_eq] at hz
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg (z.1 - 1/2), sq_nonneg z.2]

end geo

section cont
variable {n : ℕ}

lemma Km_cont : Continuous (fun z : ℝ × ℝ => Km n z) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  simp only [Km, lift2, Matrix.of_apply]
  by_cases h : i1 = j1
  · simp only [h, if_true]
    fin_cases i2 <;> fin_cases j2 <;> simp [small] <;> fun_prop
  · simp only [h, if_false]; exact continuous_const

lemma score_cont : Continuous (fun g : Fin n × Fin 2 → ℝ => score g) := by
  unfold score; fun_prop

lemma resp_cont {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {z : ℝ × ℝ}
    (hz : z ∈ disk) : ContinuousAt (response P Q v) z := by
  have hA := A_pd hP hQ hz
  have hdet : (Km n z + Sm P Q).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit).ne_zero
  have hinv : ContinuousAt Inv.inv (Km n z + Sm P Q) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hf : Continuous (fun z : ℝ × ℝ => Km n z + Sm P Q) := Km_cont.add continuous_const
  have hm : Continuous (fun M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ => M *ᵥ (Sm P Q *ᵥ wv v)) :=
    continuous_id.matrix_mulVec continuous_const
  have h2 : ContinuousAt (fun z : ℝ × ℝ => (Km n z + Sm P Q)⁻¹) z :=
    ContinuousAt.comp (g := Inv.inv) (f := fun z : ℝ × ℝ => Km n z + Sm P Q) (x := z) hinv
      hf.continuousAt
  exact ContinuousAt.comp (g := fun M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ => M *ᵥ (Sm P Q *ᵥ wv v))
    (f := fun z : ℝ × ℝ => (Km n z + Sm P Q)⁻¹) (x := z) hm.continuousAt h2

lemma Gf_cont (P Q : Sq n) (v : Vec n) :
    Continuous (fun p : (Fin n × Fin 2 → ℝ) × (ℝ × ℝ) => Gf P Q v p.1 p.2) := by
  have : (fun p : (Fin n × Fin 2 → ℝ) × (ℝ × ℝ) => Gf P Q v p.1 p.2) = fun p =>
      quad (Sm P Q) (wv v - p.1) + (∑ i, p.1 (i, 1) ^ 2 + p.2.1 * (score p.1).1 + p.2.2 * (score p.1).2) := by
    funext p; simp only [Gf, Km, quadK]
  rw [this]
  unfold quad score
  fun_prop

lemma dv_contAt {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {z : ℝ × ℝ}
    (hz : z ∈ disk) : ContinuousAt (fun z => Gf P Q v (response P Q v z) z) z := by
  have := (Gf_cont P Q v).continuousAt.comp ((resp_cont hP hQ v hz).prodMk continuousAt_id)
  exact this

lemma exists_max {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) :
    ∃ z ∈ disk, IsMaxOn (fun z => diskValue P Q v z.1 z.2) disk z := by
  have hc : ContinuousOn (fun z : ℝ × ℝ => diskValue P Q v z.1 z.2) disk := by
    refine ContinuousOn.congr (f := fun z => Gf P Q v (response P Q v z) z) ?_ ?_
    · exact fun z hz => (dv_contAt hP hQ v hz).continuousWithinAt
    · intro z hz; exact dv_eq hP hQ v hz
  exact disk_compact.exists_isMaxOn ⟨(1/2, 0), by simp [disk]⟩ hc

end cont

section kkt
variable {n : ℕ}

lemma opt_max {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {z : ℝ × ℝ}
    (hz : z ∈ disk) (ho : optimality z (score (response P Q v z))) (u : ℝ × ℝ) (hu : u ∈ disk) :
    diskValue P Q v u.1 u.2 ≤ diskValue P Q v z.1 z.2 := by
  rw [dv_eq hP hQ v hu, dv_eq hP hQ v hz]
  have h1 := G_ge hP hQ v hu (response P Q v z)
  have h2 := G_aff P Q v (response P Q v z) z u
  have h3 := geo1 ho u hu
  linarith

lemma max_opt {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {z : ℝ × ℝ}
    (hz : z ∈ disk) (hmax : IsMaxOn (fun z => diskValue P Q v z.1 z.2) disk z) :
    optimality z (score (response P Q v z)) := by
  apply geo2 hz
  intro u hu
  set zt : ℝ → ℝ × ℝ := fun t => (z.1 + t * (u.1 - z.1), z.2 + t * (u.2 - z.2)) with hzt
  set φ : ℝ → ℝ := fun t => (score (response P Q v (zt t))).1 * (u.1 - z.1) +
    (score (response P Q v (zt t))).2 * (u.2 - z.2) with hφ
  have hpos : ∀ t, 0 < t → t ≤ 1 → φ t ≤ 0 := by
    intro t ht0 ht1
    have hd := disk_seg hz hu ht0.le ht1
    have h1 := G_ge hP hQ v hz (response P Q v (zt t))
    have h2 := G_aff P Q v (response P Q v (zt t)) (zt t) z
    have h3 : diskValue P Q v (zt t).1 (zt t).2 ≤ diskValue P Q v z.1 z.2 := hmax hd
    rw [dv_eq hP hQ v hd, dv_eq hP hQ v hz] at h3
    have e : (score (response P Q v (zt t))).1 * (z.1 - (zt t).1) +
        (score (response P Q v (zt t))).2 * (z.2 - (zt t).2) = - t * φ t := by
      simp only [hzt, hφ]; ring
    have : t * φ t ≤ 0 := by linarith
    by_contra hc; push_neg at hc
    linarith [mul_pos ht0 hc]
  have hz0 : zt 0 = z := by simp [hzt]
  have hc : ContinuousAt φ 0 := by
    have hztc : Continuous zt := by simp only [hzt]; fun_prop
    have hr : ContinuousAt (fun t => response P Q v (zt t)) 0 := by
      apply ContinuousAt.comp (g := response P Q v) (f := zt) (x := 0)
      · rw [hz0]; exact resp_cont hP hQ v hz
      · exact hztc.continuousAt
    have hs := score_cont.continuousAt.comp hr
    simp only [hφ]
    exact ((continuous_fst.continuousAt.comp hs).mul continuousAt_const).add
      ((continuous_snd.continuousAt.comp hs).mul continuousAt_const)
  have hφ0 : φ 0 = (score (response P Q v z)).1 * (u.1 - z.1) +
      (score (response P Q v z)).2 * (u.2 - z.2) := by simp only [hφ, hz0]
  rw [← hφ0]
  by_contra hcon; push_neg at hcon
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (lt_mem_nhds hcon))
  have ht : dist (min (ε / 2) 1) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) one_pos)]
    linarith [min_le_left (ε / 2) 1]
  have := hball ht
  linarith [hpos (min (ε / 2) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)]

end kkt

section dual
variable {n : ℕ}

lemma int_disk {a b : ℝ} (hb : b ^ 2 < a * (1 - a)) : ((a, b) : ℝ × ℝ) ∈ disk := by
  simp only [disk, Set.mem_setOf_eq]; nlinarith

lemma red_eq {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {a b : ℝ} (ha : 0 < a)
    (hb : b ^ 2 < a * (1 - a)) : reduced P Q v a b = diskValue P Q v a b := by
  have hdet : IsUnit (small a b).det := by
    rw [det_small]; exact isUnit_iff_ne_zero.2 (by nlinarith)
  have hKiK : lift2 n (small a b)⁻¹ * Km n (a, b) = 1 := by
    rw [Km, lift2_mul, Matrix.nonsing_inv_mul _ hdet, lift2_one]
  have hBS : blockDiagonal ![P, Q] * Sm P Q = 1 := pd_mul_inv (blk_pd hP hQ)
  have hA := A_pd hP hQ (int_disk hb) (n := n)
  have hAA := pd_mul_inv hA
  have key : (blockDiagonal ![P, Q] + lift2 n (small a b)⁻¹) *
      (Sm P Q * (Km n (a, b) + Sm P Q)⁻¹ * Km n (a, b)) = 1 := by
    have h1 : (blockDiagonal ![P, Q] + lift2 n (small a b)⁻¹) * Sm P Q =
        lift2 n (small a b)⁻¹ * (Km n (a, b) + Sm P Q) := by
      rw [Matrix.add_mul, hBS, Matrix.mul_add, hKiK]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc _ _ (Km n (a, b) + Sm P Q)⁻¹,
      hAA, Matrix.mul_one, hKiK]
  have e : (reducedMatrix P Q (small a b))⁻¹ = Sm P Q * (Km n (a, b) + Sm P Q)⁻¹ * Km n (a, b) :=
    Matrix.inv_eq_right_inv key
  show quad (reducedMatrix P Q (small a b))⁻¹ (wv v) =
    quad (Sm P Q * (Km n (a, b) + Sm P Q)⁻¹ * Km n (a, b)) (wv v)
  rw [e]

def Xm (x y : Fin n → ℝ) (α β γ δ : ℝ) : Sq n :=
  Matrix.of fun j k => α * x j * x k + β * (x j * y k + y j * x k) + γ * y j * y k +
    if j = k then δ else 0

lemma Xm_mulVec (x y u : Fin n → ℝ) (α β γ δ : ℝ) :
    Xm x y α β γ δ *ᵥ u = (α * (x ⬝ᵥ u)) • x + β • ((y ⬝ᵥ u) • x + (x ⬝ᵥ u) • y) +
      (γ * (y ⬝ᵥ u)) • y + δ • u := by
  ext j
  simp only [Xm, mulVec, dotProduct, of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show δ * u j = ∑ k, (if j = k then δ else 0) * u k by simp]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma Xm_quad (x y u : Fin n → ℝ) (α β γ δ : ℝ) :
    quad (Xm x y α β γ δ) u = α * (x ⬝ᵥ u) ^ 2 + 2 * β * (x ⬝ᵥ u) * (y ⬝ᵥ u) +
      γ * (y ⬝ᵥ u) ^ 2 + δ * (u ⬝ᵥ u) := by
  rw [quad, Xm_mulVec]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm u x, dotProduct_comm u y]
  ring

lemma Xm_trace (x y : Fin n → ℝ) (α β γ δ : ℝ) :
    (Xm x y α β γ δ).trace = α * (x ⬝ᵥ x) + 2 * β * (x ⬝ᵥ y) + γ * (y ⬝ᵥ y) + δ * n := by
  simp only [Matrix.trace, Xm, Matrix.diag, of_apply, if_true, Finset.sum_add_distrib, dotProduct,
    Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∀ i, 2 * β * (x i * y i) = β * (x i * y i + y i * x i) := fun i => by ring
  simp only [this, mul_assoc]; ring

lemma Xm_sym (x y : Fin n → ℝ) (α β γ δ : ℝ) : (Xm x y α β γ δ)ᵀ = Xm x y α β γ δ := by
  ext j k
  simp only [Xm, transpose_apply, of_apply]
  by_cases h : j = k
  · subst h; ring
  · simp [h, Ne.symm h]; ring

lemma quad_Hinv {a b : ℝ} (hD : a * (1 - a) - b ^ 2 ≠ 0) (u : Fin 2 → ℝ) :
    quad (small a b)⁻¹ u = ((1 - a) * u 0 ^ 2 - 2 * b * u 0 * u 1 + a * u 1 ^ 2) /
      (a * (1 - a) - b ^ 2) := by
  rw [small_inv hD, quad2]; simp; field_simp; ring

lemma quad_R {P Q : Sq n} {a b : ℝ} (hD : a * (1 - a) - b ^ 2 ≠ 0) (ξ : Fin n × Fin 2 → ℝ) :
    quad (reducedMatrix P Q (small a b)) ξ = quad P (c0 ξ) + quad Q (c1 ξ) +
      ((1 - a) * (c0 ξ ⬝ᵥ c0 ξ) - 2 * b * (c0 ξ ⬝ᵥ c1 ξ) + a * (c1 ξ ⬝ᵥ c1 ξ)) /
        (a * (1 - a) - b ^ 2) := by
  have e : reducedMatrix P Q (small a b) = blockDiagonal ![P, Q] + lift2 n (small a b)⁻¹ := rfl
  rw [e, quad_add, quad_blk, quad_lift2]
  simp only [quad_Hinv hD, ← Finset.sum_div, dotProduct, c0, c1, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => by ring

lemma Hform_nonneg {a b : ℝ} (ha : 0 < a) (hb : b ^ 2 < a * (1 - a)) (p q : ℝ) :
    0 ≤ (1 - a) * p ^ 2 - 2 * b * p * q + a * q ^ 2 := by
  have hD : 0 ≤ a * (1 - a) - b ^ 2 := by linarith
  nlinarith [sq_nonneg ((1 - a) * p - b * q), sq_nonneg (-b * p + a * q),
    mul_nonneg hD (add_nonneg (sq_nonneg p) (sq_nonneg q))]

lemma R_pd {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) {a b : ℝ} (ha : 0 < a)
    (hb : b ^ 2 < a * (1 - a)) : (reducedMatrix P Q (small a b)).PosDef := by
  have hD : 0 < a * (1 - a) - b ^ 2 := by linarith
  rw [pd_iff]
  constructor
  · have e : reducedMatrix P Q (small a b) = blockDiagonal ![P, Q] + lift2 n (small a b)⁻¹ := rfl
    rw [e, Matrix.transpose_add, lift2_transpose, Matrix.transpose_nonsing_inv, small_sym,
      pd_sym (blk_pd hP hQ)]
  · intro ξ hξ
    have h1 := pd_pos (blk_pd hP hQ) hξ
    rw [quad_blk] at h1
    rw [quad_R hD.ne']
    have : 0 ≤ ((1 - a) * (c0 ξ ⬝ᵥ c0 ξ) - 2 * b * (c0 ξ ⬝ᵥ c1 ξ) + a * (c1 ξ ⬝ᵥ c1 ξ)) /
        (a * (1 - a) - b ^ 2) := by
      apply div_nonneg _ hD.le
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_nonneg fun i _ => by nlinarith [Hform_nonneg ha hb (c0 ξ i) (c1 ξ i)]
    linarith

lemma quad_comb {M : Sq n} (hs : Mᵀ = M) (c d : ℝ) (x y : Fin n → ℝ) :
    quad M (c • x + d • y) = c ^ 2 * quad M x + 2 * c * d * (x ⬝ᵥ (M *ᵥ y)) + d ^ 2 * quad M y := by
  simp only [quad, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [sym_swap hs y x]; ring

lemma diag_bound {X : Sq n} (hX : X.PosDef) (x y : Fin n → ℝ) {ε α β γ : ℝ} (hε : 0 < ε)
    (hα : α = quad X⁻¹ x + ε) (hβ : β = x ⬝ᵥ (X⁻¹ *ᵥ y)) (hγ : γ = quad X⁻¹ y + ε)
    (hE : 0 < α * γ - β ^ 2) (i : Fin n) :
    (γ * x i ^ 2 - 2 * β * x i * y i + α * y i ^ 2) / (α * γ - β ^ 2) ≤ X i i := by
  set E := α * γ - β ^ 2 with hEd
  have hXi := hX.inv
  have hs := pd_sym hXi
  set c := (γ * x i - β * y i) / E with hc
  set d := (α * y i - β * x i) / E with hd
  have r1 : c * α + d * β = x i := by rw [hc, hd]; field_simp; ring
  have r2 : c * β + d * γ = y i := by rw [hc, hd]; field_simp; ring
  have hsi : (γ * x i ^ 2 - 2 * β * x i * y i + α * y i ^ 2) / E = c * x i + d * y i := by
    rw [hc, hd]; field_simp; ring
  rw [hsi]
  set q := c • x + d • y with hq
  have hQq : quad X⁻¹ q = c ^ 2 * quad X⁻¹ x + 2 * c * d * β + d ^ 2 * quad X⁻¹ y := by
    rw [hq, quad_comb hs, ← hβ]
  have hsq : c * x i + d * y i = quad X⁻¹ q + ε * (c ^ 2 + d ^ 2) := by
    rw [hQq]
    have : c * x i + d * y i = c * (c * α + d * β) + d * (c * β + d * γ) := by rw [r1, r2]
    rw [this, hα, hγ]; ring
  set p := X *ᵥ Pi.single i 1 with hp
  have hXp : X⁻¹ *ᵥ p = Pi.single i 1 := by
    rw [hp, Matrix.mulVec_mulVec, pd_inv_mul hX, Matrix.one_mulVec]
  have hpi : p i = X i i := by rw [hp, Matrix.mulVec_single_one]; rfl
  have e1 : p ⬝ᵥ (X⁻¹ *ᵥ q) = c * x i + d * y i := by
    rw [sym_swap hs, hXp, dotProduct_single, mul_one, hq]; simp
  have e2 : quad X⁻¹ p = X i i := by
    rw [quad, hXp, dotProduct_single, mul_one, hpi]
  have hcs := cs hs (pd_nonneg hXi) p q
  rw [e1, e2] at hcs
  have h0 := pd_nonneg hXi q
  have h0p := pd_nonneg hXi p
  rw [e2] at h0p
  set s := c * x i + d * y i
  have hs0 : quad X⁻¹ q ≤ s := by nlinarith [sq_nonneg c, sq_nonneg d]
  have hss : 0 ≤ s := le_trans h0 hs0
  have : s ^ 2 ≤ X i i * s := le_trans hcs (mul_le_mul_of_nonneg_left hs0 h0p)
  rcases lt_or_eq_of_le hss with h | h
  · have : s * s ≤ X i i * s := by nlinarith
    exact le_of_mul_le_mul_right this h
  · rw [← h]; exact h0p

lemma A1 {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {X : Sq n} (hX : X.PosDef)
    (htr : X.trace ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℝ, 0 < a ∧ b ^ 2 < a * (1 - a) ∧ objective P Q X v ≤ reduced P Q v a b + 2 * ε := by
  have hXi := hX.inv
  set x := (P + X⁻¹)⁻¹ *ᵥ v with hx
  set y := (Q + X⁻¹)⁻¹ *ᵥ v with hy
  have hobj : objective P Q X v = (2 * (v ⬝ᵥ x) - (quad P x + quad X⁻¹ x)) +
      (2 * (v ⬝ᵥ y) - (quad Q y + quad X⁻¹ y)) := by
    have : objective P Q X v = quad (P + X⁻¹)⁻¹ v + quad (Q + X⁻¹)⁻¹ v := rfl
    rw [this, var_eq (hP.add hXi), var_eq (hQ.add hXi), quad_add, quad_add]
  set α := quad X⁻¹ x + ε with hα
  set β := x ⬝ᵥ (X⁻¹ *ᵥ y) with hβ
  set γ := quad X⁻¹ y + ε with hγ
  have hN0 := pd_nonneg hXi x
  have hN1 := pd_nonneg hXi y
  have hcs := cs (pd_sym hXi) (pd_nonneg hXi) x y
  have hE : 0 < α * γ - β ^ 2 := by
    rw [hα, hγ]; nlinarith [mul_pos hε hε]
  set E := α * γ - β ^ 2 with hEd
  set t := α + γ with ht
  have ht0 : 0 < t := by rw [ht, hα, hγ]; linarith
  have hα0 : 0 < α := by rw [hα]; linarith
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  -- the sum bound
  have hW : (γ * (x ⬝ᵥ x) - 2 * β * (x ⬝ᵥ y) + α * (y ⬝ᵥ y)) / E ≤ 1 := by
    have hsum : (γ * (x ⬝ᵥ x) - 2 * β * (x ⬝ᵥ y) + α * (y ⬝ᵥ y)) / E =
        ∑ i, (γ * x i ^ 2 - 2 * β * x i * y i + α * y i ^ 2) / E := by
      rw [← Finset.sum_div]
      congr 1
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    refine le_trans (Finset.sum_le_sum fun i _ => diag_bound hX x y hε hα hβ hγ hE i) ?_
    exact htr
  refine ⟨α / t, β / t, div_pos hα0 ht0, ?_, ?_⟩
  · have e1 : α / t * (1 - α / t) = α * γ / t ^ 2 := by rw [ht]; field_simp; ring
    rw [e1, div_pow, div_lt_div_iff_of_pos_right (by positivity)]
    linarith
  · set a := α / t with ha
    set b := β / t with hb
    have hD : a * (1 - a) - b ^ 2 = E / t ^ 2 := by rw [ha, hb, hEd, ht]; field_simp; ring
    have hD0 : a * (1 - a) - b ^ 2 ≠ 0 := by rw [hD]; positivity
    set ξ : Fin n × Fin 2 → ℝ := fun p => if p.2 = 0 then x p.1 else y p.1 with hξ
    have hc0 : c0 ξ = x := by funext i; simp [c0, hξ]
    have hc1 : c1 ξ = y := by funext i; simp [c1, hξ]
    have hR := R_pd hP hQ (div_pos hα0 ht0) (n := n) (b := b) (by
      have e1 : α / t * (1 - α / t) = α * γ / t ^ 2 := by rw [ht]; field_simp; ring
      rw [hb, e1, div_pow, div_lt_div_iff_of_pos_right (by positivity)]
      linarith)
    have hred := var_le hR (wv v) ξ
    have e : reduced P Q v a b = quad (reducedMatrix P Q (small a b))⁻¹ (wv v) := rfl
    rw [← e, dot_w, quad_R hD0, hc0, hc1] at hred
    have hT : ((1 - a) * (x ⬝ᵥ x) - 2 * b * (x ⬝ᵥ y) + a * (y ⬝ᵥ y)) / (a * (1 - a) - b ^ 2) =
        t * ((γ * (x ⬝ᵥ x) - 2 * β * (x ⬝ᵥ y) + α * (y ⬝ᵥ y)) / E) := by
      rw [hD, ha, hb, ht]; field_simp; ring
    rw [hT] at hred
    have : t * ((γ * (x ⬝ᵥ x) - 2 * β * (x ⬝ᵥ y) + α * (y ⬝ᵥ y)) / E) ≤ t := by
      nlinarith
    rw [hobj]
    have : t = quad X⁻¹ x + quad X⁻¹ y + 2 * ε := by rw [ht, hα, hγ]; ring
    linarith

lemma A2 (hn : 0 < n) {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {a b : ℝ}
    (ha : 0 < a) (hb : b ^ 2 < a * (1 - a)) {η : ℝ} (hη : 0 < η) :
    ∃ X : Sq n, X.PosDef ∧ X.trace ≤ 1 ∧ reduced P Q v a b - η ≤ objective P Q X v := by
  have hD : 0 < a * (1 - a) - b ^ 2 := by linarith
  have hR := R_pd hP hQ ha hb
  set D := a * (1 - a) - b ^ 2 with hDdef
  set ξ := (reducedMatrix P Q (small a b))⁻¹ *ᵥ wv v with hξ
  set x := c0 ξ with hx
  set y := c1 ξ with hy
  set T := ((1 - a) * (x ⬝ᵥ x) - 2 * b * (x ⬝ᵥ y) + a * (y ⬝ᵥ y)) / D with hT
  have hT0 : 0 ≤ T := by
    apply div_nonneg _ hD.le
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_nonneg fun i _ => by nlinarith [Hform_nonneg ha hb (x i) (y i)]
  have hred : reduced P Q v a b = 2 * (v ⬝ᵥ x + v ⬝ᵥ y) - (quad P x + quad Q y + T) := by
    have := var_eq hR (wv v)
    show quad (reducedMatrix P Q (small a b))⁻¹ (wv v) = _
    rw [this, dot_w, quad_R hD.ne']
  set K := T + η with hK
  have hK0 : 0 < K := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set δ := η / (K * n) with hδ
  have hδ0 : 0 < δ := by positivity
  set X := Xm x y ((1 - a) / (K * D)) (-b / (K * D)) (a / (K * D)) δ with hXdef
  have hXq : ∀ u, quad X u = ((1 - a) * (x ⬝ᵥ u) ^ 2 - 2 * b * (x ⬝ᵥ u) * (y ⬝ᵥ u) +
      a * (y ⬝ᵥ u) ^ 2) / (K * D) + δ * (u ⬝ᵥ u) := by
    intro u; rw [hXdef, Xm_quad]; field_simp; ring
  have hX : X.PosDef := by
    rw [pd_iff]
    refine ⟨Xm_sym _ _ _ _ _ _, fun u hu => ?_⟩
    rw [hXq]
    have h1 : 0 ≤ ((1 - a) * (x ⬝ᵥ u) ^ 2 - 2 * b * (x ⬝ᵥ u) * (y ⬝ᵥ u) +
      a * (y ⬝ᵥ u) ^ 2) / (K * D) := div_nonneg (Hform_nonneg ha hb _ _) (by positivity)
    have h2 : 0 < u ⬝ᵥ u := by
      have hne : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.1 h)
      have hnn : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
      exact lt_of_le_of_ne hnn (Ne.symm hne)
    nlinarith
  have htr : X.trace = 1 := by
    rw [hXdef, Xm_trace]
    have e : (1 - a) / (K * D) * (x ⬝ᵥ x) + 2 * (-b / (K * D)) * (x ⬝ᵥ y) +
        a / (K * D) * (y ⬝ᵥ y) = T / K := by
      rw [hT]; field_simp; ring
    have e2 : δ * n = η / K := by rw [hδ]; field_simp
    rw [e, e2, ← add_div, ← hK, div_self hK0.ne']
  have hXi := hX.inv
  have hmv : ∀ q, X *ᵥ (X⁻¹ *ᵥ q) = q := fun q => by
    rw [Matrix.mulVec_mulVec, pd_mul_inv hX, Matrix.one_mulVec]
  have hsx : quad X⁻¹ x ≤ a * K := by
    set u := X⁻¹ *ᵥ x with hu
    have e1 : quad X u = quad X⁻¹ x := by
      rw [quad, hmv, dotProduct_comm]; rfl
    have e2 : x ⬝ᵥ u = quad X⁻¹ x := rfl
    have hs0 : 0 ≤ quad X⁻¹ x := pd_nonneg hXi x
    rw [hXq, e2] at e1
    set s := quad X⁻¹ x
    set r := y ⬝ᵥ u
    have huu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
    have h3 : ((1 - a) * s ^ 2 - 2 * b * s * r + a * r ^ 2) / (K * D) ≤ s := by
      nlinarith [mul_nonneg hδ0.le huu]
    rw [div_le_iff₀ (by positivity)] at h3
    have h4 : D * s ^ 2 ≤ a * ((1 - a) * s ^ 2 - 2 * b * s * r + a * r ^ 2) := by
      nlinarith [sq_nonneg (b * s - a * r)]
    have h5 : s ^ 2 ≤ a * K * s := by
      have h6 := mul_le_mul_of_nonneg_left h3 ha.le
      have : D * s ^ 2 ≤ D * (a * K * s) := by linarith
      exact le_of_mul_le_mul_left this hD
    rcases lt_or_eq_of_le hs0 with hs | hs
    · have : s * s ≤ (a * K) * s := by linarith
      exact le_of_mul_le_mul_right this hs
    · rw [← hs]; positivity
  have hsy : quad X⁻¹ y ≤ (1 - a) * K := by
    set u := X⁻¹ *ᵥ y with hu
    have e1 : quad X u = quad X⁻¹ y := by
      rw [quad, hmv, dotProduct_comm]; rfl
    have e2 : y ⬝ᵥ u = quad X⁻¹ y := rfl
    have hs0 : 0 ≤ quad X⁻¹ y := pd_nonneg hXi y
    rw [hXq, e2] at e1
    set s := quad X⁻¹ y
    set r := x ⬝ᵥ u
    have huu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
    have h3 : ((1 - a) * r ^ 2 - 2 * b * r * s + a * s ^ 2) / (K * D) ≤ s := by
      nlinarith [mul_nonneg hδ0.le huu]
    rw [div_le_iff₀ (by positivity)] at h3
    have h1a : 0 < 1 - a := by nlinarith
    have h4 : D * s ^ 2 ≤ (1 - a) * ((1 - a) * r ^ 2 - 2 * b * r * s + a * s ^ 2) := by
      nlinarith [sq_nonneg ((1 - a) * r - b * s)]
    have h5 : s ^ 2 ≤ (1 - a) * K * s := by
      have h6 := mul_le_mul_of_nonneg_left h3 h1a.le
      have : D * s ^ 2 ≤ D * ((1 - a) * K * s) := by linarith
      exact le_of_mul_le_mul_left this hD
    rcases lt_or_eq_of_le hs0 with hs | hs
    · have : s * s ≤ ((1 - a) * K) * s := by linarith
      exact le_of_mul_le_mul_right this hs
    · rw [← hs]; positivity
  refine ⟨X, hX, htr.le, ?_⟩
  have o1 := var_le (hP.add hXi) v x
  have o2 := var_le (hQ.add hXi) v y
  rw [quad_add] at o1 o2
  have : objective P Q X v = quad (P + X⁻¹)⁻¹ v + quad (Q + X⁻¹)⁻¹ v := rfl
  rw [this, hred]
  have hsum : quad X⁻¹ x + quad X⁻¹ y ≤ T + η := by linarith
  linarith

lemma near_int {P Q : Sq n} (hP : P.PosDef) (hQ : Q.PosDef) (v : Vec n) {z : ℝ × ℝ}
    (hz : z ∈ disk) {t : ℝ} (ht : t < diskValue P Q v z.1 z.2) :
    ∃ a b : ℝ, 0 < a ∧ b ^ 2 < a * (1 - a) ∧ t < diskValue P Q v a b := by
  set c : ℝ × ℝ := (1/2, 0) with hc
  have hcd : c ∈ disk := by simp [hc, disk]
  set V := diskValue P Q v z.1 z.2 with hV
  set D := V - diskValue P Q v c.1 c.2 with hD
  set s := (V - t) / (2 * (|D| + (V - t))) with hs
  have hVt : 0 < V - t := by linarith
  have hden : 0 < 2 * (|D| + (V - t)) := by positivity
  have hs0 : 0 < s := div_pos hVt hden
  have hs1 : s < 1 := by
    rw [hs, div_lt_one hden]; linarith [abs_nonneg D]
  have hsD : s * D ≤ (V - t) / 2 := by
    have : s * |D| ≤ (V - t) / 2 := by
      rw [hs, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith [abs_nonneg D]
    linarith [mul_le_mul_of_nonneg_left (le_abs_self D) hs0.le]
  set zs : ℝ × ℝ := (z.1 + s * (c.1 - z.1), z.2 + s * (c.2 - z.2)) with hzs
  have hzsd : zs = ((zs.1, zs.2) : ℝ × ℝ) := rfl
  have hin : zs.2 ^ 2 < zs.1 * (1 - zs.1) := by
    simp only [hzs, hc, disk, Set.mem_setOf_eq] at hz ⊢
    have h1s : 0 < (1 - s) := by linarith
    nlinarith [mul_pos hs0 h1s, sq_nonneg (z.1 - 1/2), sq_nonneg z.2, mul_pos hs0 hs0]
  have hzsdisk : zs ∈ disk := int_disk hin
  refine ⟨zs.1, zs.2, by nlinarith [sq_nonneg zs.2], hin, ?_⟩
  have e1 := dv_eq hP hQ v hzsdisk
  have g1 := G_ge hP hQ v hz (response P Q v zs)
  have g2 := G_ge hP hQ v hcd (response P Q v zs)
  have a1 := G_aff P Q v (response P Q v zs) z zs
  have a2 := G_aff P Q v (response P Q v zs) z c
  rw [← dv_eq hP hQ v hz] at g1
  rw [← dv_eq hP hQ v hcd] at g2
  have e3 : diskValue P Q v zs.1 zs.2 = (1 - s) * Gf P Q v (response P Q v zs) z +
      s * Gf P Q v (response P Q v zs) c := by
    rw [e1, a1, a2]; simp only [hzs]; ring
  rw [e3]
  have h1s : 0 < (1 - s) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left g1 h1s.le, mul_le_mul_of_nonneg_left g2 hs0.le]

end dual

theorem solution_aux : type_of% @OMA.S_mo_476806.main := by
  intro n hn P Q v hP hQ
  obtain ⟨z0, hz0, hmax⟩ := exists_max hP hQ v
  have hmax' : ∀ u ∈ disk, diskValue P Q v u.1 u.2 ≤ diskValue P Q v z0.1 z0.2 :=
    fun u hu => isMaxOn_iff.1 hmax u hu
  generalize hV : diskValue P Q v z0.1 z0.2 = V at hmax'
  have hub : ∀ X : Sq n, X.PosDef → X.trace ≤ 1 → objective P Q X v ≤ V := by
    intro X hX htr
    by_contra h; push_neg at h
    obtain ⟨a, b, ha, hb, hle⟩ := A1 hP hQ v hX htr (ε := (objective P Q X v - V) / 4) (by linarith)
    have h2 : diskValue P Q v a b ≤ V := hmax' (a, b) (int_disk hb)
    rw [red_eq hP hQ v ha hb] at hle
    linarith
  have hlow : ∀ t < V, ∃ X : Sq n, X.PosDef ∧ X.trace ≤ 1 ∧ t < objective P Q X v := by
    intro t ht
    obtain ⟨a, b, ha, hb, hdv⟩ := near_int hP hQ v hz0 (t := t) (by rw [hV]; exact ht)
    obtain ⟨X, hX, htr, hle⟩ := A2 hn hP hQ v ha hb (η := (diskValue P Q v a b - t) / 2) (by linarith)
    rw [red_eq hP hQ v ha hb] at hle
    exact ⟨X, hX, htr, by linarith⟩
  have hsup : sSup {y | ∃ X : Sq n, X.PosDef ∧ X.trace ≤ 1 ∧ y = objective P Q X v} = V := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · obtain ⟨X, hX, htr, -⟩ := hlow (V - 1) (by linarith)
      exact ⟨_, X, hX, htr, rfl⟩
    · rintro y ⟨X, hX, htr, rfl⟩; exact hub X hX htr
    · intro t ht
      obtain ⟨X, hX, htr, hlt⟩ := hlow t ht
      exact ⟨_, ⟨X, hX, htr, rfl⟩, hlt⟩
  refine ⟨⟨z0, hz0, max_opt hP hQ v hz0 hmax⟩, fun z hz => ⟨fun ho => ?_, fun he => ?_⟩,
    fun t => ⟨?_, ?_⟩⟩
  · rw [hsup]
    rw [← hV]
    exact le_antisymm (opt_max hP hQ v hz ho z0 hz0) (hV ▸ hmax' z hz)
  · rw [hsup] at he
    apply max_opt hP hQ v hz
    intro u hu
    have := hmax' u hu
    show diskValue P Q v u.1 u.2 ≤ diskValue P Q v z.1 z.2
    linarith
  · rintro ⟨X, hX, htr, hlt⟩
    obtain ⟨a, b, ha, hb, hle⟩ := A1 hP hQ v hX htr (ε := (objective P Q X v - t) / 4) (by linarith)
    exact ⟨a, b, ha, hb, by linarith⟩
  · rintro ⟨a, b, ha, hb, hlt⟩
    obtain ⟨X, hX, htr, hle⟩ := A2 hn hP hQ v ha hb (η := (reduced P Q v a b - t) / 2) (by linarith)
    exact ⟨X, hX, htr, by linarith⟩

end OMA.P476806

theorem OMA.solution : type_of% @OMA.S_mo_476806.main := by
  exact OMA.P476806.solution_aux
