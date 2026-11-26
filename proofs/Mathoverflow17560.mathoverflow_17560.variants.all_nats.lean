import FormalConjectures.Mathoverflow.«17560»

/-!
If n to the power x is a natural number for every natural number n, then x is a natural number.
-/

namespace AllNats

open Real Set Finset Filter Topology

def shiftDiff (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (t + 1) - f t

def delta : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, t => f t
  | k + 1, f, t => delta k (shiftDiff f) t

theorem delta_int (k N : ℕ) (f : ℝ → ℝ) (hf : ∀ i : ℕ, ∃ z : ℤ, f (↑N + ↑i) = z) :
    ∃ z : ℤ, delta k f ↑N = z := by
  induction k generalizing f with
  | zero =>
    simpa [delta] using hf 0
  | succ k ih =>
    simp only [delta]
    refine ih (shiftDiff f) ?_
    intro i
    obtain ⟨z1, hz1⟩ := hf (i + 1)
    obtain ⟨z0, hz0⟩ := hf i
    refine ⟨z1 - z0, ?_⟩
    have hz1' : f (↑N + ↑i + 1) = ↑z1 := by
      rw [show (↑N : ℝ) + ↑i + 1 = ↑N + ↑(i + 1) by push_cast; ring]
      exact hz1
    simp [shiftDiff, hz1', hz0, Int.cast_sub]

theorem iter_rpow (k : ℕ) (x t : ℝ) (ht : 0 < t) :
    iteratedDeriv k (fun s => s ^ x) t =
      (∏ i ∈ range k, (x - ↑i)) * t ^ (x - ↑k) := by
  induction k generalizing t with
  | zero =>
    simp [iteratedDeriv_zero, sub_zero]
  | succ k ih =>
    have hmem : ∀ s ∈ Ioi (0 : ℝ),
        iteratedDeriv k (fun u => u ^ x) s =
          (∏ i ∈ range k, (x - ↑i)) * s ^ (x - ↑k) := fun s hs => ih s hs
    let C := ∏ i ∈ range k, (x - ↑i)
    have hformula : HasDerivAt (fun s => C * s ^ (x - ↑k))
        (C * ((x - ↑k) * t ^ (x - ↑k - 1))) t :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).const_mul C
    have hAt : HasDerivAt (iteratedDeriv k (fun s => s ^ x))
        (C * ((x - ↑k) * t ^ (x - ↑k - 1))) t := by
      refine hformula.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simpa [C] using hmem s hs
    rw [iteratedDeriv_succ, hAt.deriv, Finset.prod_range_succ]
    have hexp : x - ↑(k + 1) = x - ↑k - 1 := by push_cast; ring
    rw [hexp]
    ring

theorem delta_has (k : ℕ) (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (h : ContDiffOn ℝ k f (Ioi 0)) :
    ∃ ξ, t ≤ ξ ∧ ξ ≤ t + ↑k ∧ delta k f t = iteratedDeriv k f ξ := by
  induction k generalizing f t with
  | zero =>
    exact ⟨t, le_rfl, by simp, by simp [delta, iteratedDeriv_zero]⟩
  | succ k ih =>
    let g := shiftDiff f
    have hplus : ContDiffOn ℝ (k + 1) (fun s => f (s + 1)) (Ioi 0) :=
      h.comp ((contDiff_id.add contDiff_const).contDiffOn) fun s hs =>
        add_pos_of_pos_of_nonneg hs (by norm_num : (0 : ℝ) ≤ 1)
    have hgHigh : ContDiffOn ℝ (k + 1) g (Ioi 0) := hplus.sub h
    have hg : ContDiffOn ℝ k g (Ioi 0) :=
      hgHigh.of_le (Nat.cast_le.mpr (Nat.le_succ k) : (k : WithTop ℕ∞) ≤ (k + 1 : ℕ))
    obtain ⟨ξ, hξ1, hξ2, hξ⟩ := ih g ht hg
    have htξ : 0 < ξ := lt_of_lt_of_le ht hξ1
    have hφc : ContinuousOn (iteratedDeriv k f) (Icc ξ (ξ + 1)) := by
      have hW : ContinuousOn (iteratedDerivWithin k f (Ioi 0)) (Ioi 0) :=
        h.continuousOn_iteratedDerivWithin (m := k) (by exact_mod_cast Nat.le_succ k)
          (uniqueDiffOn_Ioi 0)
      have hEq : EqOn (iteratedDerivWithin k f (Ioi 0)) (iteratedDeriv k f) (Ioi 0) :=
        iteratedDerivWithin_of_isOpen isOpen_Ioi
      refine (hW.mono ?_).congr (fun z hz => (hEq (lt_of_lt_of_le htξ hz.1)).symm)
      intro z hz
      exact lt_of_lt_of_le htξ hz.1
    have hφd : DifferentiableOn ℝ (iteratedDeriv k f) (Ioo ξ (ξ + 1)) := by
      have hW : DifferentiableOn ℝ (iteratedDerivWithin k f (Ioi 0)) (Ioi 0) :=
        h.differentiableOn_iteratedDerivWithin (m := k)
          (by exact_mod_cast (Nat.lt_succ_self k)) (uniqueDiffOn_Ioi 0)
      have hEq : EqOn (iteratedDerivWithin k f (Ioi 0)) (iteratedDeriv k f) (Ioi 0) :=
        iteratedDerivWithin_of_isOpen isOpen_Ioi
      refine (hW.mono ?_).congr (fun z hz => (hEq (lt_of_lt_of_le htξ (le_of_lt hz.1))).symm)
      intro z hz
      exact lt_of_lt_of_le htξ (le_of_lt hz.1)
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope (iteratedDeriv k f) (by linarith : ξ < ξ + 1) hφc hφd
    have hdiff : iteratedDeriv k g ξ =
        iteratedDeriv k f (ξ + 1) - iteratedDeriv k f ξ := by
      have hk : (k : WithTop ℕ∞) ≤ (k + 1 : ℕ) := Nat.cast_le.mpr (Nat.le_succ k)
      have hξ1pos : 0 < ξ + 1 := by linarith
      have houter : ContDiffAt ℝ (k + 1) f (ξ + 1) :=
        (h (ξ + 1) hξ1pos).contDiffAt (Ioi_mem_nhds hξ1pos)
      have hcomp : ContDiffAt ℝ k (fun s => f (s + 1)) ξ :=
        ContDiffAt.comp ξ (houter.of_le hk) (contDiffAt_id.add contDiffAt_const)
      have hfAt : ContDiffAt ℝ k f ξ :=
        ((h ξ htξ).contDiffAt (Ioi_mem_nhds htξ)).of_le hk
      have hsub := iteratedDeriv_sub (n := k) hcomp hfAt
      have hshift := congrFun (iteratedDeriv_comp_add_const k f 1) ξ
      have hfun : shiftDiff f = (fun s => f (s + 1)) - f := by
        funext s
        rfl
      simpa [g, hfun, hshift] using hsub
    refine ⟨c, le_trans hξ1 (le_of_lt hc.1), ?_, ?_⟩
    · have hc2 : c < ξ + 1 := hc.2
      have hξtop : ξ + 1 ≤ t + ↑k + 1 := by linarith
      have hkcast : (↑(k + 1) : ℝ) = ↑k + 1 := by push_cast; ring
      linarith
    · have hden : (ξ + 1) - ξ = 1 := by ring
      rw [delta, hξ, hdiff]
      have hquot : iteratedDeriv k f (ξ + 1) - iteratedDeriv k f ξ =
          deriv (iteratedDeriv k f) c := by
        rw [hcderiv, hden, div_one]
      rw [hquot, ← iteratedDeriv_succ]

end AllNats

open AllNats Real Set Finset Filter Topology

theorem OMA.solution : type_of% @Mathoverflow17560.mathoverflow_17560.variants.all_nats := by
  intro x hx
  have hx0 : 0 ≤ x := by
    by_contra hlt
    have hlt : x < 0 := lt_of_not_ge hlt
    obtain ⟨m, hm⟩ := hx 2
    have hsmall : (↑(2 : ℕ) : ℝ) ^ x < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) hlt
    have hpos : 0 < (↑(2 : ℕ) : ℝ) ^ x := rpow_pos_of_pos (by norm_num) x
    rw [hm] at hsmall hpos
    have hm0 : m = 0 := Nat.lt_one_iff.mp (by exact_mod_cast hsmall)
    simp [hm0] at hpos
  by_cases hfloor : x = ↑(Nat.floor x)
  · exact ⟨Nat.floor x, hfloor⟩
  · have hlow : (Nat.floor x : ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx0) (Ne.symm hfloor)
    have hhigh : x < Nat.floor x + 1 := Nat.lt_floor_add_one x
    let m : ℕ := Nat.floor x + 1
    have hm1 : 1 ≤ m := by simp [m]
    have hxm : (Nat.floor x : ℝ) < x ∧ x < ↑m := by
      constructor
      · exact hlow
      · simpa [m, Nat.cast_add, Nat.cast_one] using hhigh
    let c : ℝ := ∏ i ∈ range m, (x - ↑i)
    have hcpos : 0 < c := by
      refine Finset.prod_pos ?_
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have hiFloor : (i : ℝ) ≤ Nat.floor x := by
        have : i ≤ Nat.floor x := by omega
        exact_mod_cast this
      linarith
    have hε : 0 < (m : ℝ) - x := by linarith [hxm.2]
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ((m : ℝ) - x)) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    rw [tendsto_atTop_atTop] at htend
    obtain ⟨N0, hN0⟩ := htend (c + 1)
    let N : ℕ := max N0 1
    have hN0le : N0 ≤ N := le_max_left _ _
    have hN1 : 1 ≤ N := le_max_right _ _
    have hpow : c + 1 ≤ (N : ℝ) ^ ((m : ℝ) - x) := hN0 _ hN0le
    have hsmall : c * (N : ℝ) ^ (x - ↑m) < 1 := by
      have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
      have hposp : 0 < (N : ℝ) ^ ((m : ℝ) - x) := rpow_pos_of_pos hNp _
      rw [show x - ↑m = -((m : ℝ) - x) by ring, rpow_neg hNp.le, mul_inv_lt_iff₀ hposp]
      linarith
    have hf : ContDiffOn ℝ m (fun s : ℝ => s ^ x) (Ioi 0) :=
      (contDiff_id.contDiffOn (s := Ioi (0 : ℝ))).rpow_const_of_ne fun s hs => ne_of_gt hs
    have hNposℝ : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    obtain ⟨ξ, hξ1, hξ2, hδ⟩ := delta_has m (fun s => s ^ x) hNposℝ hf
    have hξpos : 0 < ξ := lt_of_lt_of_le hNposℝ hξ1
    have hval : delta m (fun s => s ^ x) ↑N = c * ξ ^ (x - ↑m) := by
      rw [hδ, iter_rpow m x ξ hξpos]
    have hposδ : 0 < delta m (fun s => s ^ x) ↑N := by
      rw [hval]
      exact mul_pos hcpos (rpow_pos_of_pos hξpos _)
    have hltδ : delta m (fun s => s ^ x) ↑N < 1 := by
      rw [hval]
      have hξle : (N : ℝ) ≤ ξ := hξ1
      have hexp : x - ↑m ≤ 0 := by linarith [hxm.2]
      have hbase : 0 < (N : ℝ) := hNposℝ
      have hcmp : ξ ^ (x - ↑m) ≤ (N : ℝ) ^ (x - ↑m) := by
        have hlog : Real.log (N : ℝ) ≤ Real.log ξ := Real.log_le_log hbase hξle
        have hmul : (x - ↑m) * Real.log ξ ≤ (x - ↑m) * Real.log (N : ℝ) :=
          mul_le_mul_of_nonpos_left hlog hexp
        rw [Real.rpow_def_of_pos hξpos, Real.rpow_def_of_pos hbase]
        exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hmul)
      have : c * ξ ^ (x - ↑m) ≤ c * (N : ℝ) ^ (x - ↑m) :=
        mul_le_mul_of_nonneg_left hcmp hcpos.le
      exact this.trans_lt hsmall
    have hint : ∀ i : ℕ, ∃ z : ℤ, (fun s : ℝ => s ^ x) (↑N + ↑i) = ↑z := by
      intro i
      obtain ⟨a, ha⟩ := hx (N + i)
      refine ⟨(a : ℤ), ?_⟩
      have hcoe : ((a : ℤ) : ℝ) = (a : ℝ) := by norm_cast
      have hadd : (↑(N + i) : ℝ) = ↑N + ↑i := by push_cast; ring
      rw [hcoe, ← hadd]
      exact ha
    obtain ⟨z, hz⟩ := delta_int m N (fun s => s ^ x) hint
    have hz0 : (0 : ℝ) < z := by simpa [hz] using hposδ
    have hz1 : (z : ℝ) < 1 := by simpa [hz] using hltδ
    have hz0' : 0 < z := by exact_mod_cast hz0
    have hz1' : z < 1 := by exact_mod_cast hz1
    omega
