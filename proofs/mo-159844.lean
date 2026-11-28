import OMAStatements.S_mo_159844

open Finset Matrix OMA.S_mo_159844

namespace OMA.Proof_mo_159844

private lemma sym_add {ι : Type*} {A B : Mat ι} (hA : sym A) (hB : sym B) :
    sym (A + B) := fun i j => by
  simp [hA i j, hB i j]

private lemma sym_neg {ι : Type*} {A : Mat ι} (hA : sym A) : sym (-A) := fun i j => by
  simp [hA i j]

private lemma sym_one {ι : Type*} [DecidableEq ι] : sym (1 : Mat ι) := fun i j => by
  by_cases h : i = j
  · subst h; rfl
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

private lemma sym_principal {ι : Type*} {A : Mat (Option ι)} (hA : sym A) :
    sym (principal A) := fun i j => hA (some i) (some j)

private lemma rows_neg {ι : Type*} [Fintype ι] {A : Mat ι} {δ : ℝ} (hA : rows A δ) :
    rows (-A) δ := fun i => by
  simpa [abs_neg] using hA i

private lemma sym_dot_mulVec {ι : Type*} [Fintype ι] {A : Mat ι} (hA : sym A)
    (x y : ι → ℝ) :
    ∑ i, x i * A.mulVec y i = ∑ i, A.mulVec x i * y i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA j i]
  ring

private lemma bijective_of_mulVec_eq_zero {ι : Type*} [Fintype ι] (A : Mat ι)
    (h : ∀ v, A.mulVec v = 0 → v = 0) : Function.Bijective A.mulVec := by
  classical
  have hinj : Function.Injective (Matrix.mulVecLin A) := by
    intro x y hxy
    have hsub : A.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (h (x - y) hsub)
  have hsurj : Function.Surjective (Matrix.mulVecLin A) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨hinj, hsurj⟩

private lemma sym_rows_quad_bound {ι : Type*} [Fintype ι] {E : Mat ι} {δ : ℝ}
    (hE : sym E) (hrows : rows E δ) (x : ι → ℝ) :
    -(δ * ∑ i, (x i) ^ 2) ≤ ∑ i, x i * E.mulVec x i := by
  have hpoint : ∀ i j, 0 ≤ |E i j| * (x i) ^ 2 / 2 + |E i j| * (x j) ^ 2 / 2 +
      E i j * x i * x j := by
    intro i j
    rcases le_total 0 (E i j) with h | h
    · rw [abs_of_nonneg h]
      nlinarith [sq_nonneg (x i + x j)]
    · rw [abs_of_nonpos h]
      nlinarith [sq_nonneg (x i - x j)]
  have hsum : 0 ≤ ∑ i, ∑ j, (|E i j| * (x i) ^ 2 / 2 + |E i j| * (x j) ^ 2 / 2 +
      E i j * x i * x j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hpoint i j
  have h1 : ∑ i, ∑ j, |E i j| * (x i) ^ 2 / 2 ≤ δ * (∑ i, (x i) ^ 2) / 2 := by
    have hrew : ∑ i, ∑ j, |E i j| * (x i) ^ 2 / 2 =
        (∑ i, (∑ j, |E i j|) * (x i) ^ 2) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_div, ← Finset.sum_mul]
    rw [hrew, Finset.mul_sum, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := hrows i
    have hsq : 0 ≤ (x i) ^ 2 := sq_nonneg (x i)
    nlinarith
  have h2 : ∑ i, ∑ j, |E i j| * (x j) ^ 2 / 2 ≤ δ * (∑ i, (x i) ^ 2) / 2 := by
    rw [Finset.sum_comm]
    have hrew : ∑ j, ∑ i, |E i j| * (x j) ^ 2 / 2 =
        (∑ j, (∑ i, |E j i|) * (x j) ^ 2) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_div, ← Finset.sum_mul]
      have hsymj : ∑ i, |E i j| = ∑ i, |E j i| :=
        Finset.sum_congr rfl fun i _ => by rw [hE i j]
      rw [hsymj]
    rw [hrew, Finset.mul_sum, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := hrows j
    have hsq : 0 ≤ (x j) ^ 2 := sq_nonneg (x j)
    nlinarith
  have h3 : ∑ i, ∑ j, E i j * x i * x j = ∑ i, x i * E.mulVec x i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∑ i, ∑ j, (|E i j| * (x i) ^ 2 / 2 + |E i j| * (x j) ^ 2 / 2 +
      E i j * x i * x j) =
      (∑ i, ∑ j, |E i j| * (x i) ^ 2 / 2) + (∑ i, ∑ j, |E i j| * (x j) ^ 2 / 2) +
      ∑ i, ∑ j, E i j * x i * x j := by
    simp only [Finset.sum_add_distrib]
  linarith

private lemma coercive_add {ι : Type*} [Fintype ι] {A E : Mat ι} {μ δ : ℝ}
    (hA : coercive A μ) (hEsym : sym E) (hErows : rows E δ) :
    coercive (A + E) (μ - δ) := fun x => by
  have h1 := hA x
  have h2 := sym_rows_quad_bound hEsym hErows x
  have h3 : ∑ i, x i * (A + E).mulVec x i =
      (∑ i, x i * A.mulVec x i) + ∑ i, x i * E.mulVec x i := by
    simp only [Matrix.add_mulVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  linarith

private lemma coercive_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    coercive (1 : Mat ι) 1 := fun x => by
  simp only [Matrix.one_mulVec, one_mul, sq]
  exact le_rfl

private lemma coercive_bijective {ι : Type*} [Fintype ι] {A : Mat ι} {c : ℝ}
    (hA : coercive A c) (hc : 0 < c) : Function.Bijective A.mulVec := by
  refine bijective_of_mulVec_eq_zero A fun v hv => ?_
  have h1 := hA v
  rw [hv] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
  have hsum_le : ∑ i, (v i) ^ 2 ≤ 0 := by nlinarith
  have hsum_ge : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hsum_eq : ∑ i, (v i) ^ 2 = 0 := le_antisymm hsum_le hsum_ge
  funext i
  have hi : (v i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (v j)).mp hsum_eq i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

private lemma coercive_principal {ι : Type*} [Fintype ι] {A : Mat (Option ι)} {μ : ℝ}
    (hA : coercive A μ) : coercive (principal A) μ := fun x => by
  let y : Option ι → ℝ := Option.elim' 0 x
  have hy := hA y
  have hnorm : ∑ i : Option ι, (y i) ^ 2 = ∑ i : ι, (x i) ^ 2 := by
    rw [Fintype.sum_option]
    simp [y]
  have hquad : ∑ i : Option ι, y i * A.mulVec y i =
      ∑ i : ι, x i * (principal A).mulVec x i := by
    rw [Fintype.sum_option]
    simp only [y, Option.elim'_none, zero_mul, zero_add, Option.elim'_some]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [Matrix.mulVec, dotProduct, principal]
    rw [Fintype.sum_option]
    simp
  rw [hnorm, hquad] at hy
  exact hy

private lemma schur_pos_iff {ι : Type*} [Fintype ι] {M : Mat (Option ι)} {c : ℝ}
    (hMsym : sym M) (hMcoerc : coercive M c) (hc : 0 < c)
    {x : Option ι → ℝ} {u : ι → ℝ}
    (hx : M.mulVec x = 1) (hu : (principal M).mulVec u = 1) :
    0 < x none ↔ ∑ j, M none (some j) * u j < 1 := by
  let P : Mat ι := principal M
  let b : ι → ℝ := fun j => M none (some j)
  have hPsym : sym P := sym_principal hMsym
  have hPcoerc : coercive P c := coercive_principal hMcoerc
  have hPbij : Function.Bijective P.mulVec := coercive_bijective hPcoerc hc
  obtain ⟨w, hw⟩ := hPbij.2 b
  let S : ℝ := M none none - ∑ j, b j * w j
  have hSpos : 0 < S := by
    let z : Option ι → ℝ := Option.elim' 1 (fun j => -w j)
    have hz := hMcoerc z
    have hz_norm : 1 ≤ ∑ i : Option ι, (z i) ^ 2 := by
      rw [Fintype.sum_option]
      simp only [z, Option.elim'_none, one_pow, Option.elim'_some]
      have hnn : 0 ≤ ∑ j : ι, (-w j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith
    have hMz_some : ∀ j : ι, M.mulVec z (some j) = 0 := by
      intro j
      simp only [Matrix.mulVec, dotProduct]
      rw [Fintype.sum_option]
      simp only [z, Option.elim'_none, mul_one, Option.elim'_some]
      have hPj : P.mulVec w j = b j := congrFun hw j
      simp only [Matrix.mulVec, dotProduct, P, principal] at hPj
      have hsymj : M (some j) none = b j := hMsym (some j) none
      rw [hsymj]
      have hneg : ∑ k : ι, M (some j) (some k) * -w k = -(∑ k : ι, M (some j) (some k) * w k) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hneg, hPj]
      ring
    have hMz_none : M.mulVec z none = S := by
      simp only [Matrix.mulVec, dotProduct, S, b]
      rw [Fintype.sum_option]
      simp only [z, Option.elim'_none, mul_one, Option.elim'_some]
      have hneg : ∑ j : ι, M none (some j) * -w j = -(∑ j : ι, M none (some j) * w j) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hneg]
      ring
    have hquad : ∑ i : Option ι, z i * M.mulVec z i = S := by
      rw [Fintype.sum_option]
      simp only [z, Option.elim'_none, one_mul, Option.elim'_some, hMz_none, hMz_some,
        mul_zero, Finset.sum_const_zero, add_zero]
    rw [hquad] at hz
    nlinarith
  have hschur_eq : S * x none = 1 - ∑ j, b j * u j := by
    let v : ι → ℝ := fun j => x (some j)
    have hx_none : M none none * x none + ∑ j, b j * v j = 1 := by
      have h0 := congrFun hx none
      simp only [Matrix.mulVec, dotProduct, Pi.one_apply] at h0
      rw [Fintype.sum_option] at h0
      exact h0
    have hx_some : ∀ j, P.mulVec v j = 1 - b j * x none := by
      intro j
      have hj := congrFun hx (some j)
      simp only [Matrix.mulVec, dotProduct, Pi.one_apply] at hj
      rw [Fintype.sum_option] at hj
      have hsymj : M (some j) none = b j := hMsym (some j) none
      rw [hsymj] at hj
      have hPv : P.mulVec v j = ∑ k, M (some j) (some k) * v k := rfl
      linarith
    have hbv : ∑ j, b j * v j = (∑ j, b j * u j) - x none * ∑ j, b j * w j := by
      have h1 : ∑ j, b j * v j = ∑ j, P.mulVec w j * v j := by
        refine Finset.sum_congr rfl fun j _ => by rw [congrFun hw j]
      have h2 : ∑ j, P.mulVec w j * v j = ∑ j, w j * P.mulVec v j :=
        (sym_dot_mulVec hPsym w v).symm
      have h3 : ∑ j, w j * P.mulVec v j =
          (∑ j, w j * P.mulVec u j) - x none * ∑ j, b j * w j := by
        have hstep : ∑ j, w j * P.mulVec v j = ∑ j, (w j * 1 - x none * (b j * w j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hx_some j]
          ring
        rw [hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => by rw [congrFun hu j, Pi.one_apply]
      have h4 : ∑ j, w j * P.mulVec u j = ∑ j, b j * u j := by
        rw [sym_dot_mulVec hPsym w u]
        refine Finset.sum_congr rfl fun j _ => by rw [congrFun hw j]
      rw [h1, h2, h3, h4]
    dsimp only [S]
    linarith
  constructor
  · intro hxpos
    have hprod : 0 < S * x none := mul_pos hSpos hxpos
    linarith
  · intro hsum_lt
    have hprod : 0 < S * x none := by linarith
    exact (mul_pos_iff_of_pos_left hSpos).mp hprod

private theorem part1 :
    ∀ {ι : Type} [Fintype ι] (A : Mat (Option ι)) (μ r : ℝ),
      sym A → coercive A μ → r ≤ μ → (protectedAt A none r ↔ test A r) := by
  intro ι _ A μ r hAsym hAcoerc hrμ
  constructor
  · intro hprot δ hδ0 hδr F e hFsym hes hFe u hu
    have hδμ : 0 < μ - δ := by linarith
    let E : Mat (Option ι) := fun a b =>
      match a, b with
      | none, none => 0
      | none, some j => e j
      | some j, none => e j
      | some j, some k => F j k
    have hEsym : sym E := by
      intro a b
      cases a <;> cases b <;> simp [E]
      exact hFsym _ _
    have hErows : rows E δ := by
      intro a
      cases a with
      | none =>
        rw [Fintype.sum_option]
        simpa [E] using hes
      | some j =>
        rw [Fintype.sum_option]
        simpa [E] using hFe j
    obtain ⟨hbij, hpos⟩ := hprot δ hδ0 hδr E hEsym hErows
    obtain ⟨x, hx⟩ := hbij.2 1
    have hxpos : 0 < x none := hpos x hx
    have hMsym : sym (A + E) := sym_add hAsym hEsym
    have hMcoerc : coercive (A + E) (μ - δ) := coercive_add hAcoerc hEsym hErows
    have hPeq : principal (A + E) = principal A + F := by
      ext j k
      rfl
    have hu' : (principal (A + E)).mulVec u = 1 := by
      rw [hPeq]
      exact hu
    have hiff := schur_pos_iff hMsym hMcoerc hδμ hx hu'
    exact hiff.mp hxpos
  · intro htest δ hδ0 hδr E hEsym hErows
    have hδμ : 0 < μ - δ := by linarith
    have hMsym : sym (A + E) := sym_add hAsym hEsym
    have hMcoerc : coercive (A + E) (μ - δ) := coercive_add hAcoerc hEsym hErows
    refine ⟨coercive_bijective hMcoerc hδμ, fun x hx => ?_⟩
    let F : Mat ι := principal E
    let e : ι → ℝ := fun j => E none (some j)
    have hFsym : sym F := sym_principal hEsym
    have hes : ∑ j, |e j| ≤ δ := by
      have h0 := hErows none
      rw [Fintype.sum_option] at h0
      have hnn : 0 ≤ |E none none| := abs_nonneg _
      linarith
    have hFe : ∀ j, |e j| + ∑ k, |F j k| ≤ δ := by
      intro j
      have hj := hErows (some j)
      rw [Fintype.sum_option] at hj
      have hsymj : E (some j) none = e j := hEsym (some j) none
      rw [hsymj] at hj
      exact hj
    have hPcoerc : coercive (principal (A + E)) (μ - δ) := coercive_principal hMcoerc
    have hPbij : Function.Bijective (principal (A + E)).mulVec :=
      coercive_bijective hPcoerc hδμ
    obtain ⟨u, hu⟩ := hPbij.2 1
    have hPeq : principal (A + E) = principal A + F := by
      ext j k
      rfl
    have hu' : (principal A + F).mulVec u = 1 := by
      rw [← hPeq]
      exact hu
    have hlt := htest δ hδ0 hδr F e hFsym hes hFe u hu'
    have hiff := schur_pos_iff hMsym hMcoerc hδμ hx hu
    exact hiff.mpr hlt

private lemma rows_mul {ι : Type*} [Fintype ι] {B E : Mat ι} {K δ : ℝ}
    (hB : rows B K) (hE : rows E δ) (hδ : 0 ≤ δ) :
    rows (B * E) (K * δ) := by
  intro a
  calc ∑ c, |(B * E) a c|
      = ∑ c, |∑ b, B a b * E b c| := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp [Matrix.mul_apply]
    _ ≤ ∑ c, ∑ b, |B a b * E b c| :=
        Finset.sum_le_sum fun c _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, ∑ c, |B a b| * |E b c| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => abs_mul _ _
    _ = ∑ b, |B a b| * (∑ c, |E b c|) := by
        refine Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ b, |B a b| * δ := by
        refine Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hE b) (abs_nonneg _)
    _ = (∑ b, |B a b|) * δ := (Finset.sum_mul _ _ _).symm
    _ ≤ K * δ := mul_le_mul_of_nonneg_right (hB a) hδ

private lemma mulVec_abs_le {ι : Type*} [Fintype ι] {C : Mat ι} {q M : ℝ}
    (hC : rows C q) (v : ι → ℝ) (hM : 0 ≤ M) (hv : ∀ c, |v c| ≤ M) (a : ι) :
    |C.mulVec v a| ≤ q * M := by
  calc |C.mulVec v a|
      = |∑ c, C a c * v c| := rfl
    _ ≤ ∑ c, |C a c * v c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, |C a c| * |v c| :=
        Finset.sum_congr rfl fun c _ => abs_mul _ _
    _ ≤ ∑ c, |C a c| * M :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hv c) (abs_nonneg _)
    _ = (∑ c, |C a c|) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ q * M := mul_le_mul_of_nonneg_right (hC a) hM

private theorem part2 :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Mat ι) (K : ℝ), 0 < K →
      B * A = 1 → A.mulVec 1 = 1 → rows B K → ∀ i, protectedAt A i (1 / (2 * K)) := by
  intro ι _ _ A B K hK hBA hA1 hBK i δ hδ0 hδr E _ hErows
  have hBE : rows (B * E) (K * δ) := rows_mul hBK hErows hδ0
  set q : ℝ := K * δ
  have hq0 : 0 ≤ q := mul_nonneg (le_of_lt hK) hδ0
  have hq_half : 2 * q < 1 := by
    have h2K : 0 < 2 * K := by linarith
    have h1 : δ * (2 * K) < 1 := (lt_div_iff₀ h2K).mp hδr
    linarith
  have hB1 : B.mulVec 1 = 1 := by
    calc B.mulVec 1 = B.mulVec (A.mulVec 1) := by rw [hA1]
      _ = (B * A).mulVec 1 := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Mat ι).mulVec 1 := by rw [hBA]
      _ = 1 := Matrix.one_mulVec 1
  have hBAE : ∀ v : ι → ℝ, B.mulVec ((A + E).mulVec v) = v + (B * E).mulVec v := by
    intro v
    rw [Matrix.mulVec_mulVec, mul_add, hBA, Matrix.add_mulVec, Matrix.one_mulVec]
  constructor
  · refine bijective_of_mulVec_eq_zero (A + E) fun v hv => ?_
    obtain ⟨c₀, _, hc₀⟩ :=
      Finset.exists_max_image Finset.univ (fun c => |v c|) ⟨i, Finset.mem_univ i⟩
    have hM0 : 0 ≤ |v c₀| := abs_nonneg _
    have hvc : ∀ c, |v c| ≤ |v c₀| := fun c => hc₀ c (Finset.mem_univ c)
    have hEq : v + (B * E).mulVec v = 0 := by
      rw [← hBAE v, hv, Matrix.mulVec_zero]
    have hneg : v c₀ = -((B * E).mulVec v c₀) :=
      eq_neg_of_add_eq_zero_left (congrFun hEq c₀)
    have hbound : |v c₀| ≤ q * |v c₀| := by
      calc |v c₀| = |((B * E).mulVec v) c₀| := by rw [hneg, abs_neg]
        _ ≤ q * |v c₀| := mulVec_abs_le hBE v hM0 hvc c₀
    have hzero : |v c₀| = 0 := by nlinarith
    funext c
    have hc : |v c| ≤ 0 := by linarith [hvc c]
    exact abs_eq_zero.mp (le_antisymm hc (abs_nonneg _))
  · intro x hx
    obtain ⟨c₀, _, hc₀⟩ :=
      Finset.exists_max_image Finset.univ (fun c => |x c|) ⟨i, Finset.mem_univ i⟩
    set M : ℝ := |x c₀|
    have hM0 : 0 ≤ M := abs_nonneg _
    have hxc : ∀ c, |x c| ≤ M := fun c => hc₀ c (Finset.mem_univ c)
    have hEq : x + (B * E).mulVec x = 1 := by
      rw [← hBAE x, hx, hB1]
    have hdiff : ∀ a, |x a - 1| ≤ q * M := by
      intro a
      have ha : x a - 1 = -((B * E).mulVec x a) := by
        have h0 := congrFun hEq a
        simp only [Pi.add_apply, Pi.one_apply] at h0
        linarith
      rw [ha, abs_neg]
      exact mulVec_abs_le hBE x hM0 hxc a
    have hMle : M ≤ q * M + 1 := by
      have h1 : |x c₀| = |(x c₀ - 1) + 1| := by ring_nf
      have h2 : |(x c₀ - 1) + 1| ≤ |x c₀ - 1| + |1| := abs_add_le _ _
      rw [abs_one] at h2
      have h3 := hdiff c₀
      linarith
    have hqM : q * M < 1 := by
      by_cases hMzero : M = 0
      · rw [hMzero, mul_zero]; norm_num
      · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hMzero)
        nlinarith
    have hi := hdiff i
    have hle : 1 - x i ≤ |x i - 1| := by
      rw [abs_sub_comm]
      exact le_abs_self (1 - x i)
    linarith

private lemma protectedAt_one_of_none {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : Option ι) (r : ℝ) (h : protectedAt (1 : Mat (Option ι)) none r) :
    protectedAt (1 : Mat (Option ι)) i r := by
  intro δ hδ0 hδr E hEsym hErows
  let σ : Option ι ≃ Option ι := Equiv.swap none i
  let E' : Mat (Option ι) := fun a b => E (σ a) (σ b)
  have hE'sym : sym E' := fun a b => hEsym (σ a) (σ b)
  have hE'rows : rows E' δ := by
    intro a
    dsimp only [E']
    rw [Equiv.sum_comp σ (fun c => |E (σ a) c|)]
    exact hErows (σ a)
  obtain ⟨hbij', hpos'⟩ := h δ hδ0 hδr E' hE'sym hE'rows
  have hconj : ∀ (y : Option ι → ℝ) (a : Option ι),
      ((1 + E').mulVec (y ∘ σ)) a = ((1 + E).mulVec y) (σ a) := by
    intro y a
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Function.comp_apply, E']
    have h1 : ∀ b : Option ι, ((1 : Mat (Option ι)) a b + E (σ a) (σ b)) * y (σ b) =
        ((1 : Mat (Option ι)) (σ a) (σ b) + E (σ a) (σ b)) * y (σ b) := by
      intro b
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have hne : σ a ≠ σ b := fun hEq => hab (σ.injective hEq)
        rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hne]
    calc ∑ b : Option ι, ((1 : Mat (Option ι)) a b + E (σ a) (σ b)) * y (σ b)
        = ∑ b : Option ι, ((1 : Mat (Option ι)) (σ a) (σ b) + E (σ a) (σ b)) * y (σ b) :=
          Finset.sum_congr rfl fun b _ => h1 b
      _ = ∑ c : Option ι, ((1 : Mat (Option ι)) (σ a) c + E (σ a) c) * y c :=
          Equiv.sum_comp σ (fun c => ((1 : Mat (Option ι)) (σ a) c + E (σ a) c) * y c)
  have hσ_inv : ∀ a, σ (σ a) = a := Equiv.swap_apply_self none i
  constructor
  · constructor
    · intro x y hxy
      have h' : (1 + E').mulVec (x ∘ σ) = (1 + E').mulVec (y ∘ σ) := by
        funext a
        rw [hconj, hconj, hxy]
      have heq := hbij'.1 h'
      funext a
      have ha := congrFun heq (σ a)
      simpa [Function.comp_apply, hσ_inv a] using ha
    · intro y
      obtain ⟨z, hz⟩ := hbij'.2 (y ∘ σ)
      refine ⟨z ∘ σ, ?_⟩
      funext a
      have h1 := hconj (z ∘ σ) (σ a)
      have hcomp : (z ∘ σ) ∘ σ = z := by
        funext b; simp [Function.comp_apply, hσ_inv b]
      rw [hcomp, hσ_inv a] at h1
      have h2 := congrFun hz (σ a)
      simpa [Function.comp_apply, hσ_inv a, ← h1] using h2
  · intro x hx
    have hx' : (1 + E').mulVec (x ∘ σ) = 1 := by
      funext a
      rw [hconj, hx]
      rfl
    have h0 := hpos' (x ∘ σ) hx'
    simpa [Function.comp_apply, σ] using h0

private lemma test_one_of_le_radius (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : r ≤ radius n) :
    test (1 : Mat (Option (Fin n))) r := by
  intro δ hδ0 hδr F e hFsym hes hFe u hu
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenom_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hrad_le1 : radius n ≤ 1 := by
    unfold radius
    rw [div_le_one hdenom_pos]
    linarith
  have hδ_lt_rad : δ < radius n := lt_of_lt_of_le hδr hr
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ_lt_rad hrad_le1
  have h1δ_pos : 0 < 1 - δ := by linarith
  have h2n1_δ : (2 * (n : ℝ) - 1) * δ < n := by
    unfold radius at hδ_lt_rad
    have h1 := (lt_div_iff₀ hdenom_pos).mp hδ_lt_rad
    linarith
  let x : Fin n → ℝ := fun j => |e j|
  let d : Fin n → ℝ := fun j => δ - x j - ∑ k, |F j k|
  have hd_nn : ∀ j, 0 ≤ d j := fun j => by
    dsimp only [d, x]
    linarith [hFe j]
  let H : Mat (Fin n) := fun j k => |F j k| + if j = k then d j else 0
  have hH_nn : ∀ j k, 0 ≤ H j k := fun j k => by
    dsimp only [H]
    split_ifs
    · linarith [abs_nonneg (F j k), hd_nn j]
    · linarith [abs_nonneg (F j k)]
  have hH_sym : sym H := fun j k => by
    dsimp only [H]
    rw [hFsym j k]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk, Ne.symm hjk]
  have hH_rowsum : ∀ j, ∑ k, H j k = δ - x j := by
    intro j
    dsimp only [H]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    dsimp only [d]
    ring
  have hH_rows : rows H δ := fun j => by
    have hrew : ∑ k, |H j k| = ∑ k, H j k :=
      Finset.sum_congr rfl fun k _ => abs_of_nonneg (hH_nn j k)
    rw [hrew, hH_rowsum j]
    linarith [abs_nonneg (e j)]
  let M : Mat (Fin n) := 1 + (-H)
  have hMsym : sym M := sym_add sym_one (sym_neg hH_sym)
  have hMcoerc : coercive M (1 - δ) :=
    coercive_add coercive_one (sym_neg hH_sym) (rows_neg hH_rows)
  have hMbij : Function.Bijective M.mulVec := coercive_bijective hMcoerc h1δ_pos
  obtain ⟨s, hs⟩ := hMbij.2 1
  have hs_eq : ∀ j, s j - ∑ k, H j k * s k = 1 := by
    intro j
    have h1 : (1 + -H).mulVec s = 1 := hs
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec] at h1
    have hj := congrFun h1 j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.one_apply, Matrix.mulVec, dotProduct] at hj
    linarith
  have hu_le_s : ∀ j, |u j| ≤ s j := by
    let w : Fin n → ℝ := fun j => s j - |u j|
    have hw_ineq : ∀ j, ∑ k, H j k * w k ≤ w j := by
      intro j
      have huj : u j + ∑ k, F j k * u k = 1 := by
        have hP1 : principal (1 : Mat (Option (Fin n))) = (1 : Mat (Fin n)) := by
          ext a b
          by_cases hab : a = b
          · subst hab; simp [principal]
          · simp only [principal]
            rw [Matrix.one_apply_ne (fun h => hab (Option.some.inj h)), Matrix.one_apply_ne hab]
        have hu1 : (1 + F).mulVec u = 1 := by rwa [hP1] at hu
        rw [Matrix.add_mulVec, Matrix.one_mulVec] at hu1
        have h0 := congrFun hu1 j
        simpa [Pi.add_apply, Pi.one_apply, Matrix.mulVec, dotProduct] using h0
      have habs_u : |u j| ≤ 1 + ∑ k, |F j k| * |u k| := by
        have h1 : u j = 1 - ∑ k, F j k * u k := by linarith
        rw [h1]
        calc |1 - ∑ k, F j k * u k|
            ≤ |1| + |∑ k, F j k * u k| := abs_sub _ _
          _ ≤ 1 + ∑ k, |F j k * u k| := by
              rw [abs_one]
              linarith [Finset.abs_sum_le_sum_abs (fun k => F j k * u k) Finset.univ]
          _ = 1 + ∑ k, |F j k| * |u k| := by
              congr 1
              exact Finset.sum_congr rfl fun k _ => abs_mul _ _
      have habs_H : ∑ k, |F j k| * |u k| ≤ ∑ k, H j k * |u k| := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hle : |F j k| ≤ H j k := by
          dsimp only [H]
          split_ifs
          · linarith [hd_nn j]
          · linarith
        exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      have hsub : ∑ k, H j k * w k = (∑ k, H j k * s k) - ∑ k, H j k * |u k| := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by dsimp only [w]; ring
      dsimp only [w]
      linarith [hs_eq j]
    have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
    obtain ⟨j₀, _, hj₀⟩ := Finset.exists_min_image Finset.univ w hne
    have hmin_nn : 0 ≤ w j₀ := by
      by_contra hlt
      push Not at hlt
      have h1 : (∑ k, H j₀ k) * w j₀ ≤ ∑ k, H j₀ k * w k := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hj₀ k (Finset.mem_univ k)) (hH_nn j₀ k)
      have h2 : δ * w j₀ ≤ (δ - x j₀) * w j₀ := by
        have hx0 : 0 ≤ x j₀ := abs_nonneg _
        nlinarith
      rw [hH_rowsum j₀] at h1
      have h3 := hw_ineq j₀
      nlinarith
    intro j
    have hj : 0 ≤ w j := le_trans hmin_nn (hj₀ j (Finset.mem_univ j))
    dsimp only [w] at hj
    linarith
  set T : ℝ := ∑ j, s j
  have hs_nn : ∀ j, 0 ≤ s j := fun j => le_trans (abs_nonneg _) (hu_le_s j)
  have hT_pos : 0 < T := by
    have hq := hMcoerc s
    have hqs : ∑ j, s j * M.mulVec s j = T := by
      simp [hs, T]
    rw [hqs] at hq
    have hs_ne : s ≠ 0 := by
      intro hs0
      have h0 := congrFun hs ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩
      rw [hs0, Matrix.mulVec_zero] at h0
      simp at h0
    have hsq_pos : 0 < ∑ j, (s j) ^ 2 := by
      have hge : 0 ≤ ∑ j, (s j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      refine lt_of_le_of_ne hge ?_
      intro heq
      apply hs_ne
      funext j
      have hj : (s j) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _).mp heq.symm j (Finset.mem_univ j)
      exact sq_eq_zero_iff.mp hj
    nlinarith
  have hxs_eq : ∑ j, x j * s j = (n : ℝ) - (1 - δ) * T := by
    have hsum1 : ∑ j : Fin n, (s j - ∑ k, H j k * s k) = (n : ℝ) := by
      simp [hs_eq]
    have hcomm : ∑ j, ∑ k, H j k * s k = ∑ k, (δ - x k) * s k := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      have hsym : ∑ j, H j k = ∑ j, H k j :=
        Finset.sum_congr rfl fun j _ => hH_sym j k
      rw [hsym, hH_rowsum k]
    rw [Finset.sum_sub_distrib, hcomm] at hsum1
    have hsplit : ∑ k, (δ - x k) * s k = δ * T - ∑ k, x k * s k := by
      have : ∑ k, (δ - x k) * s k = ∑ k, (δ * s k - x k * s k) :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  let Q : ℝ := ∑ j, M.mulVec 1 j
  have hQ_le : Q ≤ (n : ℝ) * (1 - δ) + δ := by
    have hM1 : ∀ j, M.mulVec 1 j = (1 - δ) + x j := by
      intro j
      have h1 : M.mulVec 1 = 1 + -(H.mulVec 1) := by
        dsimp only [M]
        rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec]
      rw [h1]
      simp only [Pi.add_apply, Pi.neg_apply, Pi.one_apply, Matrix.mulVec, dotProduct, mul_one]
      rw [hH_rowsum j]
      ring
    have hQeq : Q = (n : ℝ) * (1 - δ) + ∑ j, x j := by
      dsimp only [Q]
      simp_rw [hM1]
      rw [Finset.sum_add_distrib]
      simp
      ring
    linarith
  have hn2_le : (n : ℝ) ^ 2 ≤ T * Q := by
    let v : Fin n → ℝ := fun j => T - (n : ℝ) * s j
    have hv_quad : 0 ≤ ∑ j, v j * M.mulVec v j := by
      have h1 := hMcoerc v
      have h2 : 0 ≤ (1 - δ) * ∑ j, (v j) ^ 2 :=
        mul_nonneg (le_of_lt h1δ_pos) (Finset.sum_nonneg fun j _ => sq_nonneg _)
      linarith
    have hMv : ∀ j, M.mulVec v j = T * M.mulVec 1 j - (n : ℝ) := by
      intro j
      have hv_eq : v = T • (1 : Fin n → ℝ) - (n : ℝ) • s := by
        funext k; simp [v]
      rw [hv_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hs]
      simp
    have hsM1 : ∑ j, s j * M.mulVec 1 j = (n : ℝ) := by
      rw [sym_dot_mulVec hMsym s 1]
      simp [hs]
    have hexpand : ∑ j, v j * M.mulVec v j = T * (T * Q - (n : ℝ) ^ 2) := by
      have hstep : ∑ j, v j * M.mulVec v j =
          ∑ j, (T ^ 2 * M.mulVec 1 j - T * (n : ℝ) - (n : ℝ) * T * (s j * M.mulVec 1 j) +
            (n : ℝ) ^ 2 * s j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hMv j]
        dsimp only [v]
        ring
      rw [hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp_rw [← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hsM1]
      dsimp only [Q, T]
      ring
    rw [hexpand] at hv_quad
    have hinner : 0 ≤ T * Q - (n : ℝ) ^ 2 := nonneg_of_mul_nonneg_right hv_quad hT_pos
    linarith
  set D : ℝ := (n : ℝ) * (1 - δ) + δ
  have hD_pos : 0 < D := by nlinarith
  have hTD : (n : ℝ) ^ 2 ≤ T * D := by
    have : T * Q ≤ T * D := mul_le_mul_of_nonneg_left hQ_le (le_of_lt hT_pos)
    linarith
  have hmain_le : ∑ j, ((1 : Mat (Option (Fin n))) none (some j) + e j) * u j ≤
      (n : ℝ) - (1 - δ) * T := by
    have hzero : ∀ j : Fin n, (1 : Mat (Option (Fin n))) none (some j) = 0 := fun j =>
      Matrix.one_apply_ne (by simp)
    simp_rw [hzero, zero_add]
    calc ∑ j, e j * u j
        ≤ ∑ j, |e j * u j| := Finset.sum_le_sum fun j _ => le_abs_self _
      _ = ∑ j, x j * |u j| := Finset.sum_congr rfl fun j _ => abs_mul _ _
      _ ≤ ∑ j, x j * s j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hu_le_s j) (abs_nonneg _)
      _ = (n : ℝ) - (1 - δ) * T := hxs_eq
  have hmul : D * (∑ j, ((1 : Mat (Option (Fin n))) none (some j) + e j) * u j) < D := by
    have h1 : D * (∑ j, ((1 : Mat (Option (Fin n))) none (some j) + e j) * u j) ≤
        D * ((n : ℝ) - (1 - δ) * T) :=
      mul_le_mul_of_nonneg_left hmain_le (le_of_lt hD_pos)
    have h2 : D * ((n : ℝ) - (1 - δ) * T) = (n : ℝ) * D - (1 - δ) * (T * D) := by ring
    have h3 : (n : ℝ) * D - (1 - δ) * (T * D) ≤ (n : ℝ) * D - (1 - δ) * (n : ℝ) ^ 2 := by
      nlinarith
    have h4 : (n : ℝ) * D - (1 - δ) * (n : ℝ) ^ 2 = (n : ℝ) * δ := by
      dsimp only [D]; ring
    have h5 : (n : ℝ) * δ < D := by
      dsimp only [D]; linarith
    linarith
  have hlt1 : D * (∑ j, ((1 : Mat (Option (Fin n))) none (some j) + e j) * u j) < D * 1 := by
    simpa [mul_one] using hmul
  exact lt_of_mul_lt_mul_left hlt1 (le_of_lt hD_pos)

private theorem part3 :
    ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ,
      (∀ i : Option (Fin n), protectedAt 1 i r) ↔ r ≤ radius n := by
  intro n hn r
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  constructor
  · intro hprot
    by_contra hgt
    push Not at hgt
    set d : ℝ := 2 * (n : ℝ) - 1
    set δ : ℝ := radius n
    have hδ0 : 0 ≤ δ := div_nonneg (le_of_lt hn_pos) (le_of_lt hd_pos)
    let E : Mat (Option (Fin n)) := fun a b =>
      match a, b with
      | none, none => 0
      | none, some _ => 1 / d
      | some _, none => 1 / d
      | some j, some k => if j = k then -(((n : ℝ) - 1) / d) else 0
    have hEsym : sym E := by
      intro a b
      cases a <;> cases b <;> simp [E]
      rename_i j k
      by_cases hjk : j = k
      · subst hjk; simp
      · simp [hjk, Ne.symm hjk]
    have hErows : rows E δ := by
      intro a
      cases a with
      | none =>
        rw [Fintype.sum_option]
        simp only [E, abs_zero, zero_add, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [abs_of_pos (div_pos zero_lt_one hd_pos)]
        dsimp only [δ, radius, d]
        rw [mul_one_div]
      | some j =>
        rw [Fintype.sum_option]
        simp only [E]
        have hsum_diag : ∑ k : Fin n, |if j = k then -(((n : ℝ) - 1) / d) else 0| =
            ((n : ℝ) - 1) / d := by
          have hrew : ∀ k : Fin n, |if j = k then -(((n : ℝ) - 1) / d) else 0| =
              if j = k then ((n : ℝ) - 1) / d else 0 := by
            intro k
            split_ifs
            · rw [abs_neg, abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hd_pos))]
            · exact abs_zero
          simp_rw [hrew]
          simp [Finset.sum_ite_eq]
        rw [hsum_diag, abs_of_pos (div_pos zero_lt_one hd_pos)]
        dsimp only [δ, radius, d]
        have hEq : 1 / (2 * (n : ℝ) - 1) + ((n : ℝ) - 1) / (2 * (n : ℝ) - 1) =
            (n : ℝ) / (2 * (n : ℝ) - 1) := by
          rw [← add_div]
          ring
        linarith
    let x : Option (Fin n) → ℝ := Option.elim' 0 (fun _ => d / (n : ℝ))
    have hx : (1 + E).mulVec x = 1 := by
      funext a
      cases a with
      | none =>
        simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Pi.one_apply]
        rw [Fintype.sum_option]
        simp only [x, E, Option.elim'_none, mul_zero, zero_add, Option.elim'_some]
        have h0 : ∀ j : Fin n, (1 : Mat (Option (Fin n))) none (some j) = 0 := fun j =>
          Matrix.one_apply_ne (by simp)
        simp_rw [h0, zero_add]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hd_pos, ne_of_gt hn_pos]
      | some j =>
        simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Pi.one_apply]
        rw [Fintype.sum_option]
        simp only [x, E, Option.elim'_none, mul_zero, zero_add, Option.elim'_some]
        have hrew : ∀ k : Fin n,
            ((1 : Mat (Option (Fin n))) (some j) (some k) +
              if j = k then -(((n : ℝ) - 1) / d) else 0) * (d / (n : ℝ)) =
            if j = k then (1 - ((n : ℝ) - 1) / d) * (d / (n : ℝ)) else 0 := by
          intro k
          by_cases hjk : j = k
          · subst hjk; simp [sub_eq_add_neg]
          · have hne : (some j : Option (Fin n)) ≠ some k := fun h => hjk (Option.some.inj h)
            rw [Matrix.one_apply_ne hne]
            simp [hjk]
        simp_rw [hrew]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        have hd_ne : d ≠ 0 := ne_of_gt hd_pos
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hnum : d - ((n : ℝ) - 1) = (n : ℝ) := by dsimp only [d]; ring
        field_simp [hd_ne, hn_ne]
        linarith
    have hpos := (hprot none δ hδ0 hgt E hEsym hErows).2 x hx
    simp [x] at hpos
  · intro hr i
    apply protectedAt_one_of_none i r
    have hrad_le1 : radius n ≤ 1 := by
      unfold radius
      rw [div_le_one hd_pos]
      linarith
    have hr1 : r ≤ 1 := le_trans hr hrad_le1
    exact (part1 (1 : Mat (Option (Fin n))) 1 r sym_one coercive_one hr1).mpr
      (test_one_of_le_radius n hn r hr)

private theorem part4 :
    ∀ c : ℝ, 1 / 2 < c → ∃ n : ℕ, 1 ≤ n ∧ radius n < c := by
  intro c hc
  have h2c : 0 < 2 * c - 1 := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (c / (2 * c - 1))
  refine ⟨max 1 m, le_max_left 1 m, ?_⟩
  have hn1 : (1 : ℝ) ≤ (max 1 m : ℕ) := by exact_mod_cast le_max_left 1 m
  have hnm : (m : ℝ) ≤ (max 1 m : ℕ) := by exact_mod_cast le_max_right 1 m
  have hdenom : 0 < 2 * ((max 1 m : ℕ) : ℝ) - 1 := by linarith
  unfold radius
  rw [div_lt_iff₀ hdenom]
  have h1 : c < (2 * c - 1) * (m : ℝ) := by
    have := (div_lt_iff₀ h2c).mp hm
    linarith
  nlinarith

end OMA.Proof_mo_159844

theorem OMA.solution : type_of% @OMA.S_mo_159844.main :=
  ⟨OMA.Proof_mo_159844.part1, OMA.Proof_mo_159844.part2,
   OMA.Proof_mo_159844.part3, OMA.Proof_mo_159844.part4⟩
