import OMAStatements.S_mo_10356
import Mathlib

namespace OMA.Mo10356

open Filter Topology

structure L1Fin : Type where
  val : ℕ →₀ ℝ

namespace L1Fin

noncomputable instance : Zero L1Fin := ⟨⟨0⟩⟩
noncomputable instance : Add L1Fin := ⟨fun x y => ⟨x.val + y.val⟩⟩
noncomputable instance : Neg L1Fin := ⟨fun x => ⟨-x.val⟩⟩
noncomputable instance : Sub L1Fin := ⟨fun x y => ⟨x.val - y.val⟩⟩
noncomputable instance : SMul ℕ L1Fin := ⟨fun n x => ⟨n • x.val⟩⟩
noncomputable instance : SMul ℤ L1Fin := ⟨fun n x => ⟨n • x.val⟩⟩
noncomputable instance : SMul ℝ L1Fin := ⟨fun c x => ⟨c • x.val⟩⟩

lemma ext {x y : L1Fin} (h : x.val = y.val) : x = y := by
  cases x; cases y; congr

lemma val_injective : Function.Injective L1Fin.val := fun _ _ h => ext h

noncomputable def l1AddCommGroup : AddCommGroup L1Fin :=
  val_injective.addCommGroup L1Fin.val rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

noncomputable def l1Norm (x : L1Fin) : ℝ :=
  x.val.sum fun _ r => |r|

lemma l1Norm_eq_sum (x : L1Fin) :
    l1Norm x = ∑ n ∈ x.val.support, |x.val n| := rfl

lemma l1Norm_zero : l1Norm 0 = 0 := by
  change (0 : ℕ →₀ ℝ).sum (fun _ r => |r|) = 0
  simp

lemma l1Norm_nonneg (x : L1Fin) : 0 ≤ l1Norm x := by
  rw [l1Norm_eq_sum]
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1Norm_eq_zero_iff (x : L1Fin) : l1Norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [l1Norm_eq_sum] at h
    apply ext
    ext n
    by_cases hn : n ∈ x.val.support
    · have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (x.val i))).mp h n hn
      exact abs_eq_zero.mp h0
    · exact Finsupp.notMem_support_iff.mp hn
  · rintro rfl
    exact l1Norm_zero

lemma l1Norm_add_le (x y : L1Fin) : l1Norm (x + y) ≤ l1Norm x + l1Norm y := by
  let S := x.val.support ∪ y.val.support
  have hxy : l1Norm (x + y) = ∑ n ∈ S, |x.val n + y.val n| := by
    rw [l1Norm_eq_sum]
    apply Finset.sum_subset Finsupp.support_add
    intro n _ hn
    have h0 : (x.val + y.val) n = 0 := Finsupp.notMem_support_iff.mp hn
    change |x.val n + y.val n| = 0
    have : x.val n + y.val n = 0 := h0
    rw [this, abs_zero]
  have hx : l1Norm x = ∑ n ∈ S, |x.val n| := by
    rw [l1Norm_eq_sum]
    apply Finset.sum_subset Finset.subset_union_left
    intro n _ hn
    simp [Finsupp.notMem_support_iff.mp hn]
  have hy : l1Norm y = ∑ n ∈ S, |y.val n| := by
    rw [l1Norm_eq_sum]
    apply Finset.sum_subset Finset.subset_union_right
    intro n _ hn
    simp [Finsupp.notMem_support_iff.mp hn]
  rw [hxy, hx, hy, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun n _ => abs_add_le _ _

lemma l1Norm_neg (x : L1Fin) : l1Norm (-x) = l1Norm x := by
  rw [l1Norm_eq_sum, l1Norm_eq_sum]
  have hsupp : (-x).val.support = x.val.support := Finsupp.support_neg x.val
  rw [hsupp]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact abs_neg (x.val n)

lemma l1Norm_smul (c : ℝ) (x : L1Fin) : l1Norm (c • x) = |c| * l1Norm x := by
  by_cases hc : c = 0
  · subst hc
    have h0 : (0 : ℝ) • x = 0 := ext (zero_smul ℝ x.val)
    rw [h0, abs_zero, zero_mul, l1Norm_zero]
  · rw [l1Norm_eq_sum, l1Norm_eq_sum, Finset.mul_sum]
    have hsupp : (c • x).val.support = x.val.support := Finsupp.support_smul_eq hc
    rw [hsupp]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact abs_mul c (x.val n)

noncomputable instance : NormedAddCommGroup L1Fin :=
  { l1AddCommGroup with
    norm := l1Norm
    dist := fun x y => l1Norm (x - y)
    dist_self := fun x => by
      have h0 : x - x = 0 := ext (sub_self x.val)
      rw [h0, l1Norm_zero]
    dist_comm := fun x y => by
      have h1 : x - y = -(y - x) := ext (neg_sub y.val x.val).symm
      rw [h1, l1Norm_neg]
    dist_triangle := fun x y z => by
      have h : x - z = (x - y) + (y - z) := ext (show x.val - z.val = (x.val - y.val) + (y.val - z.val) by abel)
      rw [h]
      exact l1Norm_add_le _ _
    eq_of_dist_eq_zero := fun {x y} h => by
      have h0 : x - y = 0 := (l1Norm_eq_zero_iff (x - y)).mp h
      exact ext (sub_eq_zero.mp (congrArg L1Fin.val h0))
    dist_eq := fun x y => by
      have h : x - y = -(-x + y) := ext (show x.val - y.val = -(-x.val + y.val) by abel)
      rw [h, l1Norm_neg]
      rfl }

noncomputable instance : NormedSpace ℝ L1Fin where
  one_smul a := ext (one_smul ℝ a.val)
  mul_smul r s a := ext (mul_smul r s a.val)
  smul_zero r := ext (smul_zero r)
  smul_add r a b := ext (smul_add r a.val b.val)
  add_smul r s a := ext (add_smul r s a.val)
  zero_smul a := ext (zero_smul ℝ a.val)
  norm_smul_le c x := by
    change l1Norm (c • x) ≤ ‖c‖ * l1Norm x
    rw [l1Norm_smul, Real.norm_eq_abs]

lemma norm_eq_l1Norm (x : L1Fin) : ‖x‖ = ∑ n ∈ x.val.support, |x.val n| := rfl

noncomputable def eb (n : ℕ) : L1Fin := ⟨Finsupp.single n 1⟩

lemma norm_eb (n : ℕ) : ‖eb n‖ = 1 := by
  rw [norm_eq_l1Norm, eb]
  simp

lemma decomp (x : L1Fin) : x = ∑ n ∈ x.val.support, x.val n • eb n := by
  apply ext
  have hval : ∀ S : Finset ℕ, (∑ n ∈ S, x.val n • eb n).val = ∑ n ∈ S, x.val n • Finsupp.single n (1 : ℝ) := by
    intro S
    induction S using Finset.cons_induction with
    | empty => rfl
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      change (x.val a • eb a).val + (∑ n ∈ s, x.val n • eb n).val = _
      rw [ih]
      rfl
  rw [hval]
  ext k
  rw [Finsupp.finsetSum_apply]
  by_cases hk : k ∈ x.val.support
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      simp [Finsupp.single_apply, hbk]
    · intro h
      exact absurd hk h
  · rw [Finset.sum_eq_zero]
    · exact Finsupp.notMem_support_iff.mp hk
    · intro b hb
      have hbk : b ≠ k := fun h => hk (h ▸ hb)
      simp [Finsupp.single_apply, hbk]

lemma apply_eq_sum (φ : L1Fin →L[ℝ] ℝ) (x : L1Fin) :
    φ x = ∑ n ∈ x.val.support, x.val n * φ (eb n) := by
  conv_lhs => rw [decomp x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, smul_eq_mul]

lemma abs_apply_eb_le (φ : L1Fin →L[ℝ] ℝ) (n : ℕ) : |φ (eb n)| ≤ ‖φ‖ := by
  have h := φ.le_opNorm (eb n)
  rw [Real.norm_eq_abs, norm_eb, mul_one] at h
  exact h

noncomputable def mkDual (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) :
    L1Fin →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.val.sum fun n r => r * a n
      map_add' := fun x y => by
        change (x.val + y.val).sum (fun n r => r * a n) =
          x.val.sum (fun n r => r * a n) + y.val.sum (fun n r => r * a n)
        exact Finsupp.sum_add_index (fun _ _ => zero_mul _) (fun _ _ _ _ => add_mul _ _ _)
      map_smul' := fun c x => by
        change (c • x.val).sum (fun n r => r * a n) = c * x.val.sum (fun n r => r * a n)
        rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
        simp only [Finsupp.sum, Finset.mul_sum, mul_assoc] }
    C
    (fun x => by
      change |∑ n ∈ x.val.support, x.val n * a n| ≤ C * ∑ n ∈ x.val.support, |x.val n|
      calc
        |∑ n ∈ x.val.support, x.val n * a n|
            ≤ ∑ n ∈ x.val.support, |x.val n * a n| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ n ∈ x.val.support, |x.val n| * |a n| := by
              refine Finset.sum_congr rfl fun n _ => abs_mul _ _
        _ ≤ ∑ n ∈ x.val.support, |x.val n| * C := by
              refine Finset.sum_le_sum fun n _ =>
                mul_le_mul_of_nonneg_left (ha n) (abs_nonneg _)
        _ = C * ∑ n ∈ x.val.support, |x.val n| := by
              rw [← Finset.sum_mul, mul_comm])

lemma mkDual_eb (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) (n : ℕ) :
    mkDual a C hC ha (eb n) = a n := by
  change (Finsupp.single n (1 : ℝ)).sum (fun k r => r * a k) = a n
  rw [Finsupp.sum_single_index (zero_mul _), one_mul]

lemma opNorm_le_of_eb (φ : L1Fin →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, |φ (eb n)| ≤ C) : ‖φ‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound φ hC fun x => ?_
  rw [Real.norm_eq_abs, apply_eq_sum, norm_eq_l1Norm]
  calc
    |∑ n ∈ x.val.support, x.val n * φ (eb n)|
        ≤ ∑ n ∈ x.val.support, |x.val n * φ (eb n)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ x.val.support, |x.val n| * |φ (eb n)| :=
          Finset.sum_congr rfl fun n _ => abs_mul _ _
    _ ≤ ∑ n ∈ x.val.support, |x.val n| * C :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (h n) (abs_nonneg _)
    _ = C * ∑ n ∈ x.val.support, |x.val n| := by rw [← Finset.sum_mul, mul_comm]

end L1Fin

noncomputable def bump (t : ℝ) : ℝ := t ^ 2 / (1 + t ^ 2)

lemma bump_zero : bump 0 = 0 := by simp [bump]

lemma bump_nonneg (t : ℝ) : 0 ≤ bump t := by
  unfold bump
  positivity

lemma bump_le_one (t : ℝ) : bump t ≤ 1 := by
  unfold bump
  rw [div_le_one (by positivity)]
  linarith

lemma abs_bump_le_one (t : ℝ) : |bump t| ≤ 1 := by
  rw [abs_of_nonneg (bump_nonneg t)]
  exact bump_le_one t

lemma bump_lipschitz (a b : ℝ) : |bump a - bump b| ≤ |a - b| := by
  unfold bump
  have ha : 0 < 1 + a ^ 2 := by positivity
  have hb : 0 < 1 + b ^ 2 := by positivity
  have hdiff : a ^ 2 / (1 + a ^ 2) - b ^ 2 / (1 + b ^ 2) =
      (a - b) * (a + b) / ((1 + a ^ 2) * (1 + b ^ 2)) := by
    field_simp
    ring
  rw [hdiff, abs_div, abs_mul, abs_of_pos (mul_pos ha hb), div_le_iff₀ (mul_pos ha hb)]
  have hbound : |a + b| ≤ (1 + a ^ 2) * (1 + b ^ 2) := by
    have h1 : |a| ≤ (1 + a ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    have h2 : |b| ≤ (1 + b ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 1)]
    have h3 : |a + b| ≤ |a| + |b| := abs_add_le a b
    nlinarith [sq_nonneg a, sq_nonneg b]
  exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)

lemma continuous_bump : Continuous bump := by
  unfold bump
  refine (continuous_pow 2).div (continuous_const.add (continuous_pow 2)) fun t => by positivity

lemma bump_ge_four_fifths {t : ℝ} (ht : 2 ≤ |t|) : (4 : ℝ) / 5 ≤ bump t := by
  unfold bump
  have hsq : 4 ≤ t ^ 2 := by
    have h1 : (2 : ℝ) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ (by norm_num) ht 2
    rw [sq_abs] at h1
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

noncomputable def T (φ : L1Fin →L[ℝ] ℝ) : L1Fin →L[ℝ] ℝ :=
  L1Fin.mkDual (fun n => bump (φ (L1Fin.eb n))) 1 zero_le_one (fun n => abs_bump_le_one _)

lemma T_eb (φ : L1Fin →L[ℝ] ℝ) (n : ℕ) : T φ (L1Fin.eb n) = bump (φ (L1Fin.eb n)) :=
  L1Fin.mkDual_eb _ _ _ _ n

lemma T_zero : T 0 = 0 := by
  ext x
  rw [L1Fin.apply_eq_sum]
  simp [T_eb, bump_zero]

lemma T_norm_continuous : Continuous T := by
  have hlip : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul fun φ ψ => ?_
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    refine L1Fin.opNorm_le_of_eb (T φ - T ψ) (norm_nonneg _) fun n => ?_
    change |T φ (L1Fin.eb n) - T ψ (L1Fin.eb n)| ≤ ‖φ - ψ‖
    rw [T_eb, T_eb]
    calc
      |bump (φ (L1Fin.eb n)) - bump (ψ (L1Fin.eb n))|
          ≤ |φ (L1Fin.eb n) - ψ (L1Fin.eb n)| := bump_lipschitz _ _
      _ = |(φ - ψ) (L1Fin.eb n)| := rfl
      _ ≤ ‖φ - ψ‖ := L1Fin.abs_apply_eb_le (φ - ψ) n
  exact hlip.continuous

lemma induced_comp_apply {α ι β : Type*} [TopologicalSpace β] (g : α → ι → β) (i : ι) :
    @Continuous α β (TopologicalSpace.induced g inferInstance) _ (fun a => g a i) := by
  letI : TopologicalSpace α := TopologicalSpace.induced g inferInstance
  exact (continuous_apply i).comp continuous_induced_dom

lemma continuous_to_induced_pi {α β ι γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]
    (g : β → ι → γ) (F : α → β) (h : ∀ i, Continuous fun a => g (F a) i) :
    @Continuous α β _ (TopologicalSpace.induced g inferInstance) F :=
  continuous_induced_rng.mpr (continuous_pi h)

lemma continuous_finset_sum_top {α : Type*} [TopologicalSpace α] {ι : Type*} (s : Finset ι)
    (f : ι → α → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a => ∑ i ∈ s, f i a) :=
  continuous_finset_sum s hf

lemma continuous_const_mul_comp {α : Type*} [TopologicalSpace α] (c : ℝ) (g : ℝ → ℝ) (f : α → ℝ)
    (hg : Continuous g) (hf : Continuous f) : Continuous (fun a => c * g (f a)) :=
  continuous_const.mul (hg.comp hf)

lemma preimage_mem_nhds_induced {α ι β : Type*} [TopologicalSpace β] (g : α → ι → β) (a : α)
    (f : α → ℝ) (hf : @Continuous α ℝ (TopologicalSpace.induced g inferInstance) _ f)
    {r : ℝ} (hr : |f a| < r) :
    ∃ (S : Finset ι) (t : ι → Set β), (∀ i, t i ∈ nhds (g a i)) ∧
      ∀ x, (∀ i ∈ S, g x i ∈ t i) → |f x| < r := by
  letI : TopologicalSpace α := TopologicalSpace.induced g inferInstance
  have hopen : IsOpen {y : ℝ | |y| < r} := isOpen_lt continuous_abs continuous_const
  have hnhds : f ⁻¹' {y : ℝ | |y| < r} ∈ nhds a :=
    hf.continuousAt.preimage_mem_nhds (hopen.mem_nhds hr)
  rw [nhds_induced, Filter.mem_comap] at hnhds
  rcases hnhds with ⟨U, hU, hUsub⟩
  rw [nhds_pi, Filter.mem_pi'] at hU
  rcases hU with ⟨S, t, ht, htsub⟩
  exact ⟨S, t, ht, fun x hx => hUsub (htsub hx)⟩

lemma T_weakStar_continuous :
    @Continuous _ _ (OMA.S_mo_10356.weakStar L1Fin) (OMA.S_mo_10356.weakStar L1Fin) T := by
  refine @continuous_to_induced_pi _ _ _ _ (OMA.S_mo_10356.weakStar L1Fin) _
    (fun φ x => φ x) T fun x => ?_
  have hfun : (fun φ : L1Fin →L[ℝ] ℝ => (T φ) x) =
      fun φ => ∑ n ∈ x.val.support, x.val n * bump (φ (L1Fin.eb n)) := by
    funext φ
    rw [L1Fin.apply_eq_sum]
    refine Finset.sum_congr rfl fun n _ => by rw [T_eb]
  rw [hfun]
  refine @continuous_finset_sum_top _ (OMA.S_mo_10356.weakStar L1Fin) _ x.val.support _ fun n _ => ?_
  exact @continuous_const_mul_comp _ (OMA.S_mo_10356.weakStar L1Fin) (x.val n) bump
    (fun φ => φ (L1Fin.eb n)) continuous_bump
    (induced_comp_apply (fun (φ : L1Fin →L[ℝ] ℝ) (y : L1Fin) => φ y) (L1Fin.eb n))

noncomputable def cesAvg (φ : L1Fin →L[ℝ] ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, φ (L1Fin.eb n)

def hasCesLim (φ : L1Fin →L[ℝ] ℝ) (L : ℝ) : Prop :=
  Tendsto (cesAvg φ) atTop (nhds L)

noncomputable def cesSubmodule : Submodule ℝ (L1Fin →L[ℝ] ℝ) where
  carrier := {φ | ∃ L : ℝ, hasCesLim φ L}
  add_mem' := by
    rintro φ ψ ⟨L₁, h₁⟩ ⟨L₂, h₂⟩
    refine ⟨L₁ + L₂, ?_⟩
    unfold hasCesLim
    have heq : cesAvg (φ + ψ) = fun N => cesAvg φ N + cesAvg ψ N := by
      funext N
      unfold cesAvg
      simp only [ContinuousLinearMap.add_apply, Finset.sum_add_distrib, mul_add]
    rw [heq]
    exact h₁.add h₂
  zero_mem' := by
    refine ⟨0, ?_⟩
    unfold hasCesLim
    have heq : cesAvg 0 = fun _ => (0 : ℝ) := by
      funext N
      simp [cesAvg]
    rw [heq]
    exact tendsto_const_nhds
  smul_mem' := by
    rintro c φ ⟨L, h⟩
    refine ⟨c * L, ?_⟩
    unfold hasCesLim
    have heq : cesAvg (c • φ) = fun N => c * cesAvg φ N := by
      funext N
      unfold cesAvg
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [heq]
    exact h.const_mul c

noncomputable def cesLimFun (x : cesSubmodule) : ℝ :=
  Classical.choose x.2

lemma cesLimFun_spec (x : cesSubmodule) : hasCesLim x.1 (cesLimFun x) :=
  Classical.choose_spec x.2

lemma cesLimFun_eq {x : cesSubmodule} {L : ℝ} (h : hasCesLim x.1 L) :
    cesLimFun x = L :=
  tendsto_nhds_unique (cesLimFun_spec x) h

lemma abs_cesAvg_le (φ : L1Fin →L[ℝ] ℝ) (N : ℕ) : |cesAvg φ N| ≤ ‖φ‖ := by
  by_cases hN : N = 0
  · subst hN
    simp [cesAvg, norm_nonneg]
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    unfold cesAvg
    rw [abs_mul, abs_inv, abs_of_pos hNpos]
    calc
      (N : ℝ)⁻¹ * |∑ n ∈ Finset.range N, φ (L1Fin.eb n)|
          ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, |φ (L1Fin.eb n)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hNpos.le)
      _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, ‖φ‖ :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => L1Fin.abs_apply_eb_le φ n)
              (inv_nonneg.mpr hNpos.le)
      _ = (N : ℝ)⁻¹ * ((N : ℝ) * ‖φ‖) := by simp
      _ = ‖φ‖ := by field_simp

noncomputable def cesCLM : cesSubmodule →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := cesLimFun
      map_add' := fun x y => by
        apply cesLimFun_eq
        have heq : cesAvg (x.1 + y.1) = fun N => cesAvg x.1 N + cesAvg y.1 N := by
          funext N
          unfold cesAvg
          simp only [ContinuousLinearMap.add_apply, Finset.sum_add_distrib, mul_add]
        change Tendsto (cesAvg (x.1 + y.1)) atTop (nhds (cesLimFun x + cesLimFun y))
        rw [heq]
        exact (cesLimFun_spec x).add (cesLimFun_spec y)
      map_smul' := fun c x => by
        apply cesLimFun_eq
        have heq : cesAvg (c • x.1) = fun N => c * cesAvg x.1 N := by
          funext N
          unfold cesAvg
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
          ring
        change Tendsto (cesAvg (c • x.1)) atTop (nhds (c * cesLimFun x))
        rw [heq]
        exact (cesLimFun_spec x).const_mul c }
    1
    (fun x => by
      rw [one_mul, Real.norm_eq_abs]
      have hlim : Tendsto (fun N => |cesAvg x.1 N|) atTop (nhds |cesLimFun x|) :=
        (cesLimFun_spec x).abs
      exact le_of_tendsto hlim (Eventually.of_forall fun N => abs_cesAvg_le x.1 N))

noncomputable def oneDual : L1Fin →L[ℝ] ℝ :=
  L1Fin.mkDual (fun _ => 1) 1 zero_le_one (fun _ => by norm_num)

lemma oneDual_eb (n : ℕ) : oneDual (L1Fin.eb n) = 1 :=
  L1Fin.mkDual_eb _ _ _ _ n

lemma oneDual_hasCesLim : hasCesLim oneDual 1 := by
  unfold hasCesLim cesAvg
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  simp [oneDual_eb, hNpos]

noncomputable def modDual (m : ℕ) (j : Fin m) : L1Fin →L[ℝ] ℝ :=
  L1Fin.mkDual (fun n => if n % m = j.val then 1 else 0) 1 zero_le_one
    (fun n => by split_ifs <;> norm_num)

lemma modDual_eb (m : ℕ) (j : Fin m) (n : ℕ) :
    modDual m j (L1Fin.eb n) = if n % m = j.val then 1 else 0 :=
  L1Fin.mkDual_eb _ _ _ _ n

lemma card_filter_mod_bounds (m : ℕ) (j : Fin m) (N : ℕ) :
    N / m ≤ ((Finset.range N).filter (fun n => n % m = j.val)).card ∧
      ((Finset.range N).filter (fun n => n % m = j.val)).card ≤ N / m + 1 := by
  have hm : 0 < m := Fin.pos j
  let f : ℕ → ℕ := fun q => q * m + j.val
  have hfinj : Function.Injective f := by
    intro q₁ q₂ h
    dsimp only [f] at h
    have : q₁ * m = q₂ * m := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_right hm this
  constructor
  · have hsub : (Finset.range (N / m)).image f ⊆
        (Finset.range N).filter (fun n => n % m = j.val) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
      rw [Finset.mem_range] at hq
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have h1 : (q + 1) * m ≤ (N / m) * m := Nat.mul_le_mul_right m hq
        have h2 : (N / m) * m ≤ N := Nat.div_mul_le_self N m
        have h3 : q * m + j.val < (q + 1) * m := by
          rw [Nat.add_mul, one_mul]
          exact Nat.add_lt_add_left j.isLt (q * m)
        exact lt_of_lt_of_le h3 (h1.trans h2)
      · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    calc
      N / m = (Finset.range (N / m)).card := (Finset.card_range _).symm
      _ = ((Finset.range (N / m)).image f).card :=
            (Finset.card_image_of_injective _ hfinj).symm
      _ ≤ ((Finset.range N).filter (fun n => n % m = j.val)).card :=
            Finset.card_le_card hsub
  · have hsub : (Finset.range N).filter (fun n => n % m = j.val) ⊆
        (Finset.range (N / m + 1)).image f := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_image]
      refine ⟨n / m, ?_, ?_⟩
      · rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.le)
      · dsimp only [f]
        rw [← hn.2, mul_comm, Nat.div_add_mod]
    calc
      ((Finset.range N).filter (fun n => n % m = j.val)).card
          ≤ ((Finset.range (N / m + 1)).image f).card := Finset.card_le_card hsub
      _ ≤ (Finset.range (N / m + 1)).card := Finset.card_image_le
      _ = N / m + 1 := Finset.card_range _

lemma modDual_hasCesLim (m : ℕ) (j : Fin m) : hasCesLim (modDual m j) ((m : ℝ)⁻¹) := by
  have hm_pos : 0 < m := Fin.pos j
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
  rw [hasCesLim, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  refine ⟨max K 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right K 1).trans hN
  have hNK : K ≤ N := (le_max_left K 1).trans hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hsum : ∑ n ∈ Finset.range N, modDual m j (L1Fin.eb n) =
      (((Finset.range N).filter (fun n => n % m = j.val)).card : ℝ) := by
    simp [modDual_eb]
  have hcard := card_filter_mod_bounds m j N
  have hdiv_lo : (N : ℝ) - (m : ℝ) < ((N / m : ℕ) : ℝ) * (m : ℝ) := by
    have h1 : N < (N / m + 1) * m := by
      have := Nat.div_add_mod N m
      have := Nat.mod_lt N hm_pos
      nlinarith
    have h1R : (N : ℝ) < (((N / m : ℕ) : ℝ) + 1) * (m : ℝ) := by exact_mod_cast h1
    linarith
  have hdiv_hi : ((N / m : ℕ) : ℝ) * (m : ℝ) ≤ (N : ℝ) := by
    have h1 : (N / m) * m ≤ N := Nat.div_mul_le_self N m
    exact_mod_cast h1
  have hlo : (N : ℝ) / (m : ℝ) - 1 < ((N / m : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hmR]
    linarith
  have hhi : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmR]
    exact hdiv_hi
  have hcl : (N : ℝ) / (m : ℝ) - 1 < (((Finset.range N).filter (fun n => n % m = j.val)).card : ℝ) :=
    lt_of_lt_of_le hlo (by exact_mod_cast hcard.1)
  have hcu : (((Finset.range N).filter (fun n => n % m = j.val)).card : ℝ) ≤ (N : ℝ) / (m : ℝ) + 1 := by
    have h2 : (((Finset.range N).filter (fun n => n % m = j.val)).card : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by
      exact_mod_cast hcard.2
    linarith
  rw [Real.dist_eq, cesAvg, hsum]
  have habs : |(N : ℝ)⁻¹ * (((Finset.range N).filter (fun n => n % m = j.val)).card : ℝ) - (m : ℝ)⁻¹| ≤
      (N : ℝ)⁻¹ := by
    rw [abs_le]
    have h1 : (N : ℝ)⁻¹ * ((N : ℝ) / (m : ℝ) - 1) = (m : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
      field_simp
    have h2 : (N : ℝ)⁻¹ * ((N : ℝ) / (m : ℝ) + 1) = (m : ℝ)⁻¹ + (N : ℝ)⁻¹ := by
      field_simp
    constructor
    · have := mul_le_mul_of_nonneg_left hcl.le (inv_nonneg.mpr hNpos.le)
      linarith
    · have := mul_le_mul_of_nonneg_left hcu (inv_nonneg.mpr hNpos.le)
      linarith
  have hlt : (N : ℝ)⁻¹ < ε := by
    rw [inv_lt_iff_one_lt_mul₀ hNpos]
    have hK' : 2 / ε < (N : ℝ) := lt_of_lt_of_le hK (by exact_mod_cast hNK)
    have h2 : 2 < ε * (N : ℝ) := by
      rwa [div_lt_iff₀ hε, mul_comm] at hK'
    linarith
  exact lt_of_le_of_lt habs hlt

lemma exists_large_support {m r : ℕ} (W : Submodule ℝ (Fin m → ℝ))
    (hr : r ≤ Module.finrank ℝ W) :
    ∃ c ∈ W, r ≤ (Finset.univ.filter fun j : Fin m => c j ≠ 0).card := by
  classical
  let supp : (Fin m → ℝ) → Finset (Fin m) := fun c => Finset.univ.filter fun j => c j ≠ 0
  let sizes : Finset ℕ := (Finset.range (m + 1)).filter fun s => ∃ c ∈ W, (supp c).card = s
  have hne : sizes.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ m), 0, W.zero_mem, ?_⟩⟩
    simp [supp]
  let sMax := sizes.max' hne
  have hsMax_mem : sMax ∈ sizes := Finset.max'_mem sizes hne
  rcases (Finset.mem_filter.mp hsMax_mem).2 with ⟨c, hcW, hcCard⟩
  have hmax : ∀ w ∈ W, (supp w).card ≤ (supp c).card := by
    intro w hw
    rw [hcCard]
    refine Finset.le_max' sizes (supp w).card ?_
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, w, hw, rfl⟩
    have hle : (supp w).card ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa using Nat.lt_succ_of_le hle
  have hsubset : ∀ w ∈ W, supp w ⊆ supp c := by
    intro w hw j₀ hj₀
    by_contra hnot
    have hwj₀ : w j₀ ≠ 0 := (Finset.mem_filter.mp hj₀).2
    have hcj₀ : c j₀ = 0 := by
      by_contra hne0
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hne0⟩)
    let bad : Finset ℝ := insert (0 : ℝ) ((supp c).image fun j => -(c j) / w j)
    have hex : ∃ t : ℝ, t ∉ bad := by
      obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
      exact ⟨t, ht⟩
    rcases hex with ⟨t, ht⟩
    have ht0 : t ≠ 0 := fun h => ht (h ▸ Finset.mem_insert_self 0 _)
    let u : Fin m → ℝ := c + t • w
    have huW : u ∈ W := W.add_mem hcW (W.smul_mem t hw)
    have hinc : insert j₀ (supp c) ⊆ supp u := by
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ j, ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hjc
      · change c j + t * w j ≠ 0
        rw [hcj₀, zero_add]
        exact mul_ne_zero ht0 hwj₀
      · change c j + t * w j ≠ 0
        have hcj : c j ≠ 0 := (Finset.mem_filter.mp hjc).2
        by_cases hwj : w j = 0
        · rw [hwj, mul_zero, add_zero]
          exact hcj
        · intro heq
          have htval : t = -(c j) / w j := by
            field_simp [hwj]
            linarith
          apply ht
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hjc, htval.symm⟩)
    have hgt : (supp c).card < (supp u).card := by
      calc
        (supp c).card < (insert j₀ (supp c)).card := by
          rw [Finset.card_insert_of_notMem hnot]
          exact Nat.lt_succ_self _
        _ ≤ (supp u).card := Finset.card_le_card hinc
    exact absurd (hmax u huW) (not_le.mpr hgt)
  let restr : W →ₗ[ℝ] (↥(supp c) → ℝ) :=
    { toFun := fun w j => w.1 j.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective restr := by
    intro w₁ w₂ h
    ext j
    by_cases hj : j ∈ supp c
    · exact congrFun h ⟨j, hj⟩
    · have hw₁ : w₁.1 j = 0 := by
        by_contra hne0
        exact hj (hsubset w₁.1 w₁.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne0⟩))
      have hw₂ : w₂.1 j = 0 := by
        by_contra hne0
        exact hj (hsubset w₂.1 w₂.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne0⟩))
      rw [hw₁, hw₂]
  have hle_rank : Module.finrank ℝ W ≤ Module.finrank ℝ (↥(supp c) → ℝ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hcard_rank : Module.finrank ℝ (↥(supp c) → ℝ) = (supp c).card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  exact ⟨c, hcW, hr.trans (hle_rank.trans_eq hcard_rank)⟩

lemma T_not_weak_continuous :
    ¬ @Continuous _ _ (OMA.S_mo_10356.weak L1Fin) (OMA.S_mo_10356.weak L1Fin) T := by
  intro hcont
  obtain ⟨ℓ, hℓ_ext, hℓ_norm⟩ := exists_extension_norm_eq cesSubmodule cesCLM
  have hℓ_le1 : ‖ℓ‖ ≤ 1 := by
    rw [hℓ_norm]
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hℓ_one : ℓ oneDual = 1 := by
    have hmem : oneDual ∈ cesSubmodule := ⟨1, oneDual_hasCesLim⟩
    have h1 := hℓ_ext ⟨oneDual, hmem⟩
    have h2 : cesCLM ⟨oneDual, hmem⟩ = 1 := cesLimFun_eq oneDual_hasCesLim
    simpa [h2] using h1
  have hℓ_mod : ∀ (m : ℕ) (j : Fin m), ℓ (modDual m j) = (m : ℝ)⁻¹ := by
    intro m j
    have hmem : modDual m j ∈ cesSubmodule := ⟨(m : ℝ)⁻¹, modDual_hasCesLim m j⟩
    have h1 := hℓ_ext ⟨modDual m j, hmem⟩
    have h2 : cesCLM ⟨modDual m j, hmem⟩ = (m : ℝ)⁻¹ := cesLimFun_eq (modDual_hasCesLim m j)
    simpa [h2] using h1
  have hℓ_nonneg : ∀ ψ : L1Fin →L[ℝ] ℝ,
      (∀ n, 0 ≤ ψ (L1Fin.eb n) ∧ ψ (L1Fin.eb n) ≤ 1) → 0 ≤ ℓ ψ := by
    intro ψ hψ
    have hnorm : ‖(2 : ℝ) • ψ - oneDual‖ ≤ 1 := by
      refine L1Fin.opNorm_le_of_eb _ zero_le_one fun n => ?_
      change |2 * ψ (L1Fin.eb n) - oneDual (L1Fin.eb n)| ≤ 1
      rw [oneDual_eb, abs_le]
      rcases hψ n with ⟨h0, h1⟩
      constructor <;> linarith
    have hbd : |ℓ ((2 : ℝ) • ψ - oneDual)| ≤ 1 := by
      have h1 := ℓ.le_opNorm ((2 : ℝ) • ψ - oneDual)
      rw [Real.norm_eq_abs] at h1
      calc
        |ℓ ((2 : ℝ) • ψ - oneDual)| ≤ ‖ℓ‖ * ‖(2 : ℝ) • ψ - oneDual‖ := h1
        _ ≤ 1 * 1 := mul_le_mul hℓ_le1 hnorm (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [map_sub, map_smul, smul_eq_mul, hℓ_one, abs_le] at hbd
    linarith
  have hℓ_mono : ∀ ψ₁ ψ₂ : L1Fin →L[ℝ] ℝ,
      (∀ n, 0 ≤ ψ₁ (L1Fin.eb n) ∧ ψ₁ (L1Fin.eb n) ≤ ψ₂ (L1Fin.eb n) ∧ ψ₂ (L1Fin.eb n) ≤ 1) →
      ℓ ψ₁ ≤ ℓ ψ₂ := by
    intro ψ₁ ψ₂ h
    have hdiff : 0 ≤ ℓ (ψ₂ - ψ₁) := by
      apply hℓ_nonneg
      intro n
      rcases h n with ⟨h0, h12, h2⟩
      change 0 ≤ ψ₂ (L1Fin.eb n) - ψ₁ (L1Fin.eb n) ∧ ψ₂ (L1Fin.eb n) - ψ₁ (L1Fin.eb n) ≤ 1
      constructor <;> linarith
    rw [map_sub] at hdiff
    linarith
  have hcomp : @Continuous _ _ (OMA.S_mo_10356.weak L1Fin) _ (fun φ => ℓ (T φ)) := by
    have hev : @Continuous _ _ (OMA.S_mo_10356.weak L1Fin) _ (fun φ => ℓ φ) :=
      induced_comp_apply (fun (φ : L1Fin →L[ℝ] ℝ) (μ : (L1Fin →L[ℝ] ℝ) →L[ℝ] ℝ) => μ φ) ℓ
    exact @Continuous.comp _ _ _ (OMA.S_mo_10356.weak L1Fin) (OMA.S_mo_10356.weak L1Fin) _ _ _ hev hcont
  have h0 : |ℓ (T 0)| < (1 : ℝ) / 3 := by
    rw [T_zero, map_zero, abs_zero]
    norm_num
  obtain ⟨S, t, ht, hSbound⟩ := preimage_mem_nhds_induced
    (fun (φ : L1Fin →L[ℝ] ℝ) (μ : (L1Fin →L[ℝ] ℝ) →L[ℝ] ℝ) => μ φ) 0 (fun φ => ℓ (T φ)) hcomp h0
  let k := S.card
  let m := 2 * k + 1
  have hm_pos : 0 < m := by omega
  let Φ : (Fin m → ℝ) →ₗ[ℝ] (↥S → ℝ) :=
    { toFun := fun c μ => μ.1 (∑ j : Fin m, c j • modDual m j)
      map_add' := fun c₁ c₂ => by
        ext μ
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
      map_smul' := fun r c => by
        ext μ
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul,
          RingHom.id_apply] }
  have hker_rank : k + 1 ≤ Module.finrank ℝ (LinearMap.ker Φ) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    have hdom : Module.finrank ℝ (Fin m → ℝ) = 2 * k + 1 := by
      simp [m]
    have hrng : Module.finrank ℝ (LinearMap.range Φ) ≤ k := by
      have h1 := Submodule.finrank_le (LinearMap.range Φ)
      have h2 : Module.finrank ℝ (↥S → ℝ) = k := by
        rw [Module.finrank_pi, Fintype.card_coe]
      exact h1.trans_eq h2
    omega
  obtain ⟨c, hcKer, hcCard⟩ := exists_large_support (LinearMap.ker Φ) hker_rank
  let I : Finset (Fin m) := Finset.univ.filter fun j => c j ≠ 0
  have hI_card : k + 1 ≤ I.card := hcCard
  have hI_nonempty : I.Nonempty := Finset.card_pos.mp (by omega)
  let minAbs : ℝ := I.inf' hI_nonempty fun j => |c j|
  have hminAbs_pos : 0 < minAbs := by
    rw [Finset.lt_inf'_iff]
    intro j hj
    exact abs_pos.mpr (Finset.mem_filter.mp hj).2
  let M : ℝ := 2 / minAbs
  have hM_nonneg : 0 ≤ M := div_nonneg (by norm_num) hminAbs_pos.le
  let φ : L1Fin →L[ℝ] ℝ := M • ∑ j : Fin m, c j • modDual m j
  have hφ_ker : ∀ μ ∈ S, μ φ = 0 := by
    intro μ hμ
    change μ (M • ∑ j : Fin m, c j • modDual m j) = 0
    rw [map_smul, smul_eq_mul]
    have h0 : Φ c ⟨μ, hμ⟩ = 0 := by
      rw [LinearMap.mem_ker] at hcKer
      exact congrFun hcKer ⟨μ, hμ⟩
    change M * Φ c ⟨μ, hμ⟩ = 0
    rw [h0, mul_zero]
  have hlt : |ℓ (T φ)| < (1 : ℝ) / 3 := by
    apply hSbound φ
    intro μ hμ
    have hzero_mem : (0 : ℝ) ∈ t μ := by
      have hmem0 := mem_of_mem_nhds (ht μ)
      simpa using hmem0
    have heq : μ φ = 0 := hφ_ker μ hμ
    simpa [heq] using hzero_mem
  let ψLower : L1Fin →L[ℝ] ℝ := ((4 : ℝ) / 5) • ∑ j ∈ I, modDual m j
  have hφ_eb : ∀ n : ℕ, φ (L1Fin.eb n) = M * c ⟨n % m, Nat.mod_lt n hm_pos⟩ := by
    intro n
    change M * (∑ j : Fin m, c j • modDual m j) (L1Fin.eb n) = _
    rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
    have hterm : ∑ j : Fin m, (c j • modDual m j) (L1Fin.eb n) =
        c ⟨n % m, Nat.mod_lt n hm_pos⟩ := by
      rw [Finset.sum_eq_single ⟨n % m, Nat.mod_lt n hm_pos⟩]
      · simp [modDual_eb]
      · intro j _ hjne
        have hneq : n % m ≠ j.val := fun heq => hjne (Fin.ext heq.symm)
        simp [modDual_eb, hneq]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hterm]
  have hψLower_eb : ∀ n : ℕ,
      ψLower (L1Fin.eb n) = if ⟨n % m, Nat.mod_lt n hm_pos⟩ ∈ I then (4 : ℝ) / 5 else 0 := by
    intro n
    change ((4 : ℝ) / 5) * (∑ j ∈ I, modDual m j) (L1Fin.eb n) = _
    rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
    by_cases hmem : ⟨n % m, Nat.mod_lt n hm_pos⟩ ∈ I
    · rw [if_pos hmem, Finset.sum_eq_single ⟨n % m, Nat.mod_lt n hm_pos⟩]
      · simp [modDual_eb]
      · intro j _ hjne
        have hneq : n % m ≠ j.val := fun heq => hjne (Fin.ext heq.symm)
        simp [modDual_eb, hneq]
      · intro h
        exact absurd hmem h
    · rw [if_neg hmem, Finset.sum_eq_zero]
      · ring
      · intro j hj
        have hneq : n % m ≠ j.val := fun heq => hmem (by
          have : (⟨n % m, Nat.mod_lt n hm_pos⟩ : Fin m) = j := Fin.ext heq
          rwa [this])
        simp [modDual_eb, hneq]
  have hcomp_le : ℓ ψLower ≤ ℓ (T φ) := by
    apply hℓ_mono
    intro n
    rw [hψLower_eb, T_eb, hφ_eb]
    refine ⟨?_, ?_, bump_le_one _⟩
    · split_ifs <;> norm_num
    · split_ifs with hmem
      · apply bump_ge_four_fifths
        rw [abs_mul, abs_of_nonneg hM_nonneg]
        have hmin_le : minAbs ≤ |c ⟨n % m, Nat.mod_lt n hm_pos⟩| :=
          Finset.inf'_le (f := fun j => |c j|) hmem
        have h1 : (2 / minAbs) * minAbs ≤ (2 / minAbs) * |c ⟨n % m, Nat.mod_lt n hm_pos⟩| :=
          mul_le_mul_of_nonneg_left hmin_le hM_nonneg
        have h2 : (2 / minAbs) * minAbs = 2 := by field_simp [hminAbs_pos.ne']
        linarith
      · exact bump_nonneg _
  have hℓ_lower_val : ℓ ψLower = ((4 : ℝ) / 5) * ((I.card : ℝ) / (m : ℝ)) := by
    change ℓ (((4 : ℝ) / 5) • ∑ j ∈ I, modDual m j) = _
    rw [map_smul, smul_eq_mul, map_sum]
    have hsum : ∑ j ∈ I, ℓ (modDual m j) = (I.card : ℝ) * (m : ℝ)⁻¹ := by
      simp [hℓ_mod]
    rw [hsum, ← div_eq_mul_inv]
  have hge_two_fifths : (2 : ℝ) / 5 ≤ ℓ ψLower := by
    rw [hℓ_lower_val]
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
    have hrat : (1 : ℝ) / 2 ≤ (I.card : ℝ) / (m : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hmR]
      have h1 : 2 * k + 1 ≤ 2 * I.card := by omega
      have h1R : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * I.card : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1R
      change (1 : ℝ) * (m : ℝ) ≤ (I.card : ℝ) * 2
      have hm_eq : (m : ℝ) = 2 * (k : ℝ) + 1 := by
        dsimp [m]
        push_cast
        ring
      linarith
    linarith
  have hbad : (2 : ℝ) / 5 ≤ ℓ (T φ) := hge_two_fifths.trans hcomp_le
  have hlt' : ℓ (T φ) < (1 : ℝ) / 3 := (abs_lt.mp hlt).2
  linarith

end OMA.Mo10356

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_10356.main) := by
  intro h
  exact OMA.Mo10356.T_not_weak_continuous
    (h OMA.Mo10356.L1Fin OMA.Mo10356.T OMA.Mo10356.T_norm_continuous
      OMA.Mo10356.T_weakStar_continuous)
