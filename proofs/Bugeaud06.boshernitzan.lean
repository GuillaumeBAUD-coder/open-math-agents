import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6

/-! # Boshernitzan's theorem on dense dilates

We use a finite Fourier test, a mean-square estimate for separated points, and the first crossing of each large scale by the sublacunary sequence. The resulting uniform local packing bound gives zero Hausdorff dimension, even for a sequence that is not monotone. -/

/- A finite Fourier test for density on the unit circle. The unnormalized Fejér
kernel is the squared norm of a geometric sum: it is bounded away from its peak,
whereas its empirical mean is large when all the low modes are small. -/
namespace OMA.FejerB106
open Finset AddCircle Complex
open scoped ComplexConjugate

private abbrev T := AddCircle (1:ℝ)

private theorem separation {ε : ℝ} (hε : 0<ε) :
    ∃ c>0, ∀ u : T, ε ≤ dist u 0 → c ≤ ‖fourier 1 u - 1‖ := by
  let h := AddCircle.homeomorphCircle (T:=(1:ℝ)) one_ne_zero
  obtain ⟨c,hc,ctrl⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous h.symm.continuous) ε hε
  refine ⟨c,hc,fun u hu => ?_⟩
  by_contra! bad
  have near : dist (h u) (h 0) < c := by
    change dist ((h u : Circle) : ℂ) ((h 0 : Circle) : ℂ) < c
    rw [dist_eq_norm]
    simpa only [h,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_zero,Circle.coe_one,
      fourier_one] using bad
  exact (not_lt.mpr hu) (by simpa using ctrl near)

private theorem fpower (u : T) (i : ℕ) : fourier (i:ℤ) u = (fourier 1 u)^i := by
  simp [fourier_apply,toCircle_nsmul]

private noncomputable def kernel (m : ℕ) (u : T) : ℝ :=
  ‖∑ a : Fin m, fourier (a.val:ℤ) u‖^2

private theorem kernel_small (m : ℕ) (u : T) {c : ℝ} (hc : 0<c)
    (hu : c ≤ ‖fourier 1 u - 1‖) : kernel m u ≤ (2/c)^2 := by
  let z := fourier 1 u
  have hz : ‖z‖ = 1 := Circle.norm_coe _
  have h : ‖∑ i ∈ range m, z^i‖ * ‖z-1‖ ≤ 2 := by
    rw [← norm_mul,geom_sum_mul]
    calc _ ≤ ‖z^m‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
         _ = 2 := by simp [hz]; norm_num
  have h' : ‖∑ i ∈ range m, z^i‖ ≤ 2/c := (le_div_iff₀ hc).mpr
    ((mul_le_mul_of_nonneg_left hu (norm_nonneg _)).trans h)
  simpa only [kernel,fpower,Fin.sum_univ_eq_sum_range] using
    (sq_le_sq' (by linarith [norm_nonneg (∑ i ∈ range m, z^i)]) h')

private theorem kernel_expand (m : ℕ) (u : T) :
    kernel m u = ∑ a : Fin m, ∑ b : Fin m, (fourier ((a.val:ℤ)-b.val) u).re := by
  have eq : (∑ a : Fin m, fourier (a.val:ℤ) u) *
        conj (∑ b : Fin m, fourier (b.val:ℤ) u) =
      ∑ a : Fin m, ∑ b : Fin m, fourier ((a.val:ℤ)-b.val) u := by
    simp only [map_sum,Finset.sum_mul,Finset.mul_sum,sub_eq_add_neg,fourier_add,fourier_neg]
    rw [Finset.sum_comm]
  rw [Complex.mul_conj'] at eq
  simpa only [kernel,Complex.ofReal_re,←Complex.ofReal_pow,Complex.re_sum] using
    congrArg Complex.re eq

private theorem shifted {N : ℕ} (x : Fin N → T) (y : T) (k : ℤ) :
    ‖∑ j, fourier k (x j-y)‖ = ‖∑ j, fourier k (x j)‖ := by
  have eq (u : T) : fourier k (u-y) = fourier k u * fourier k (-y) := by
    simp only [sub_eq_add_neg,fourier_apply,zsmul_add,toCircle_add,Circle.coe_mul]
  simp only [eq,←Finset.sum_mul,norm_mul]
  rw [show ‖fourier k (-y)‖ = 1 from Circle.norm_coe _,mul_one]

private theorem mode {N m : ℕ} (x : Fin N → T) (δ : ℝ)
    (ctrl : ∀ k : ℕ, 0<k → k ≤ m → ‖∑ j, fourier (k:ℤ) (x j)‖ ≤ δ*N)
    (y : T) (a b : Fin m) (hne : a ≠ b) :
    ‖∑ j, fourier ((a.val:ℤ)-b.val) (x j-y)‖ ≤ δ*N := by
  rw [shifted]
  rcases lt_or_gt_of_ne hne with hab|hba
  · have eq : (a.val:ℤ)-b.val = -((b.val-a.val:ℕ):ℤ) := by omega
    rw [eq]
    simp only [fourier_neg,←map_sum, Complex.norm_conj]
    exact ctrl _ (by omega) (by omega)
  · have eq : (a.val:ℤ)-b.val = ((a.val-b.val:ℕ):ℤ) := by omega
    rw [eq]; exact ctrl _ (by omega) (by omega)

theorem net (ε : ℝ) (hε : 0<ε) :
    ∃ H : ℕ, ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (x : Fin N → T), 0<N →
      (∀ k : ℕ, 0<k → k≤H → ‖∑ j, fourier (k:ℤ) (x j)‖ ≤ δ*N) →
      ∀ y : T, ∃ j, dist y (x j)<ε := by
  classical
  obtain ⟨c,hc,sep⟩ := separation hε
  obtain ⟨m,hm⟩ := exists_nat_gt (2*(2/c)^2)
  have mp : 0 < (m:ℝ) := by linarith [sq_nonneg (2/c)]
  let δ : ℝ := 1/(2*m)
  have hd : 0<δ := by dsimp [δ]; positivity
  refine ⟨m,δ,hd,fun N x hN ctrl y => ?_⟩
  by_contra! hole
  have np : 0 < (N:ℝ) := by exact_mod_cast hN
  have upper : ∑ j, kernel m (x j-y) ≤ (N:ℝ)*(2/c)^2 := by
    calc
      _ ≤ ∑ _j : Fin N, (2/c)^2 := Finset.sum_le_sum fun j _ =>
        kernel_small _ _ hc (sep _ (by simpa [dist_eq_norm_sub, norm_sub_rev] using hole j))
      _ = _ := by simp
  let f (a b : Fin m) (j : Fin N) := (fourier ((a.val:ℤ)-b.val) (x j-y)).re
  have e (a b : Fin m) : (if a=b then (N:ℝ) else 0)-δ*N ≤ ∑ j, f a b j := by
    by_cases eq : a=b
    · subst b; simp [f]
      positivity
    · rw [if_neg eq,zero_sub]
      have h := mode x δ ctrl y a b eq
      have h' := (abs_le.mp ((Complex.abs_re_le_norm _).trans h)).1
      simpa only [f,Complex.re_sum] using h'
  have total : (∑ a : Fin m, ∑ b : Fin m, ∑ j, f a b j) = ∑ j, kernel m (x j-y) := by
    simp_rw [kernel_expand]
    change _ = ∑ j, ∑ a, ∑ b, f a b j
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have lower : (m:ℝ) * (N-(m:ℝ)*(δ*N)) ≤ ∑ j, kernel m (x j-y) := by
    rw [←total]
    calc _ = ∑ a : Fin m, ∑ b : Fin m, ((if a=b then (N:ℝ) else 0)-δ*N) := by
               simp [Finset.sum_sub_distrib,mul_sub]
         _ ≤ _ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => e a b
  have delta : (m:ℝ)*(δ*N) = N/2 := by dsimp [δ]; field_simp
  rw [delta] at lower
  nlinarith [mul_pos (sub_pos.mpr hm) np]

end OMA.FejerB106

/- Mean-square estimates for a separated finite configuration under real dilations. -/

namespace OMA.BosMean06
open Finset MeasureTheory Real
noncomputable section

private def kernel {M : ℕ} (x : Fin M → ℝ) (k : ℕ) (i j : Fin M) (t : ℝ) :=
  Real.cos (t*(2*Real.pi*k*(x i-x j)))

private def energy {M : ℕ} (x : Fin M → ℝ) (k : ℕ) (t : ℝ) :=
  ∑ i, ∑ j, kernel x k i j t

private theorem energy_eq {M : ℕ} (x : Fin M → ℝ) (k : ℕ) (t : ℝ) :
    energy x k t = ‖∑ i, fourier (k:ℤ) ((t*x i:ℝ):AddCircle (1:ℝ))‖^2 := by
  let θ (i : Fin M) := t*(2*Real.pi*k*x i)
  have f (i : Fin M) : fourier (k:ℤ) ((t*x i:ℝ):AddCircle (1:ℝ)) =
      Complex.exp ((θ i:ℂ)*Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [θ]
    push_cast
    ring
  have hker (i j : Fin M) : kernel x k i j t =
      Real.cos (θ i)*Real.cos (θ j) + Real.sin (θ i)*Real.sin (θ j) := by
    rw [←Real.cos_sub]; unfold kernel θ; congr 1; ring
  simp only [energy,hker,f,Complex.sq_norm,Complex.normSq_apply,Complex.re_sum,Complex.im_sum,
    Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,sub_zero,Real.exp_zero,one_mul,
    sum_add_distrib,←mul_sum,←sum_mul]

private theorem energy_cont {M : ℕ} (x : Fin M → ℝ) (k : ℕ) :
    Continuous (energy x k) := by unfold energy kernel; fun_prop

private theorem pair_estimate {M : ℕ} (x : Fin M → ℝ) {δ : ℝ} (hδ : 0<δ)
    (sep : ∀ i j, i≠j → δ≤|x i-x j|) (k : ℕ) (hk : 0<k) (i j : Fin M) (T : ℝ) :
    (∫ t in 1..T, kernel x k i j t) ≤ (if i=j then T-1 else 0)+2/δ := by
  by_cases same : i=j
  · subst j
    simp [kernel]
    positivity
  simp only [if_neg same,zero_add]
  let c := 2*Real.pi*k*(x i-x j)
  have hc : δ≤|c| := by
    have hk' : (1:ℝ)≤k := by exact_mod_cast hk
    have half : (1:ℝ)≤2*Real.pi := by linarith [Real.pi_gt_three]
    have big : (1:ℝ)≤2*Real.pi*k := one_le_mul_of_one_le_of_one_le half hk'
    dsimp [c]; rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*Real.pi*k)]
    exact (sep i j same).trans (le_mul_of_one_le_left (abs_nonneg _) big)
  have hc' : c≠0 := by intro e; simp [e] at hc; linarith
  change (∫ t in 1..T, Real.cos (t*c)) ≤ 2/δ
  rw [intervalIntegral.integral_comp_mul_right _ hc',integral_cos,smul_eq_mul]
  apply (le_abs_self _).trans
  rw [abs_mul,abs_inv]
  have hsin : |Real.sin (T*c)-Real.sin (1*c)|≤2 := by
    exact abs_le.mpr ⟨by linarith [Real.neg_one_le_sin (T*c),Real.sin_le_one (1*c)],
      by linarith [Real.sin_le_one (T*c),Real.neg_one_le_sin (1*c)]⟩
  calc
    _ ≤ |c|⁻¹*2 := by gcongr
    _ = 2/|c| := by ring
    _ ≤ 2/δ := by gcongr

private theorem integral_energy {M : ℕ} (x : Fin M → ℝ) {δ : ℝ} (hδ : 0<δ)
    (sep : ∀ i j, i≠j → δ≤|x i-x j|) (k : ℕ) (hk : 0<k) (T : ℝ) :
    (∫ t in 1..T, energy x k t) ≤ M*(T-1)+(M:ℝ)^2*(2/δ) := by
  have cont (i j : Fin M) : Continuous (kernel x k i j) := by unfold kernel; fun_prop
  unfold energy
  rw [intervalIntegral.integral_finsetSum (fun i _ => (continuous_finsetSum _ fun j _ => cont i j).intervalIntegrable ..)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => (cont _ j).intervalIntegrable ..)]
  apply (sum_le_sum (fun i _ => sum_le_sum (fun j _ => pair_estimate x hδ sep k hk i j T))).trans_eq
  simp [sum_add_distrib,nsmul_eq_mul]
  ring

/-- The mean square of each nonconstant empirical Fourier coefficient costs
at most twice the number of points on a sufficiently long dilation interval. -/
theorem mixing_modes (H : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ M : ℕ, 0<M ∧ ∀ δ : ℝ, 0<δ → ∃ T : ℝ, 1≤T ∧ ∀ x : Fin M→ℝ,
    (∀ i j, i≠j → δ≤|x i-x j|) → ∃ t ∈ Set.Icc 1 T, ∀ k : ℕ, 0<k → k≤H →
      ‖∑ i, fourier (k:ℤ) ((t*x i:ℝ):AddCircle (1:ℝ))‖ ≤ η*M := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (2*(H:ℝ)/η^2))
  have mpos : 0<(M:ℝ) := by linarith [le_max_left (1:ℝ) (2*H/η^2)]
  have hb : 2*(H:ℝ)<M*η^2 := (div_lt_iff₀ (sq_pos_of_pos hη)).mp
    ((le_max_right (1:ℝ) _).trans_lt hM)
  have hm : 2*(H:ℝ)*M < (η*M)^2 := by nlinarith only [mul_lt_mul_of_pos_right hb mpos]
  refine ⟨M,by exact_mod_cast mpos,?_⟩
  intro δ hδ
  let T : ℝ := 2+2*M/δ
  have long : 2*(M:ℝ)/δ ≤ T-1 := by dsimp [T]; linarith
  have ht : 1<T := by dsimp [T]; linarith [div_nonneg (by positivity : 0≤2*(M:ℝ)) hδ.le]
  refine ⟨T,ht.le,?_⟩
  intro x sep
  let F (t : ℝ) := ∑ j : Fin H, energy x (j.val+1) t
  have cont : Continuous F := continuous_finsetSum _ (fun j _ => energy_cont x (j.val+1))
  have integ : (∫ t in 1..T, F t) ≤ (T-1)*(2*H*M) := by
    unfold F
    rw [intervalIntegral.integral_finsetSum (fun j _ => (energy_cont x (j.val+1)).intervalIntegrable ..)]
    apply (sum_le_sum (fun j _ => integral_energy x hδ sep (j.val+1) (by omega) T)).trans
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hlim : (M:ℝ)^2*(2/δ) ≤ M*(T-1) := by
      calc
        _ = (M:ℝ)*(2*M/δ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left long mpos.le
    nlinarith only [mul_le_mul_of_nonneg_left hlim (Nat.cast_nonneg (α:=ℝ) H)]
  by_contra! miss
  have major (t : ℝ) (tin : t ∈ Set.Icc 1 T) : (η*M)^2 ≤ F t := by
    obtain ⟨k,hk,kH,bad⟩ := miss t tin
    let j : Fin H := ⟨k-1,by omega⟩
    have kj : j.val+1=k := by dsimp [j]; omega
    have hsingle : energy x (j.val+1) t ≤ F t := single_le_sum
      (f:=fun z : Fin H => energy x (z.val+1) t)
      (fun z _ => by rw [energy_eq]; positivity) (mem_univ j)
    rw [kj,energy_eq] at hsingle
    exact (pow_le_pow_left₀ (by positivity) bad.le 2).trans hsingle
  have lo := intervalIntegral.integral_mono_on (μ:=volume) ht.le (intervalIntegrable_const)
    (cont.intervalIntegrable ..) major
  rw [intervalIntegral.integral_const,smul_eq_mul] at lo
  exact (not_lt_of_ge (lo.trans integ)) (mul_lt_mul_of_pos_left hm (sub_pos.mpr ht))

/-- Finitely many separated points admit a dilation from a common bounded
interval that forms an ε-net on the circle. -/
theorem mixing_of_test (test : ∀ ε : ℝ, 0<ε → ∃ H : ℕ, ∃ η > (0:ℝ),
    ∀ (M : ℕ) (z : Fin M → AddCircle (1:ℝ)), 0<M →
    (∀ k : ℕ, 0<k → k≤H → ‖∑ i, fourier (k:ℤ) (z i)‖ ≤ η*M) →
    ∀ y : AddCircle (1:ℝ), ∃ i, dist y (z i)<ε) :
    ∀ ε : ℝ, 0<ε → ∃ M : ℕ, 0<M ∧ ∀ δ : ℝ, 0<δ → ∃ T : ℝ, 1≤T ∧
    ∀ x : Fin M→ℝ, (∀ i, x i∈Set.Icc (0:ℝ) 1) → (∀ i j, i≠j → δ≤|x i-x j|) →
    ∃ t∈Set.Icc 1 T, ∀ y : AddCircle (1:ℝ), ∃ i, dist ((t*x i:ℝ):AddCircle (1:ℝ)) y<ε := by
  intro ε hε
  obtain ⟨H,η,hη,small⟩ := test ε hε
  obtain ⟨M,hM,major⟩ := mixing_modes H η hη
  refine ⟨M,hM,?_⟩
  intro δ hδ
  obtain ⟨T,hT,work⟩ := major δ hδ
  refine ⟨T,hT,?_⟩
  intro x _ sep
  obtain ⟨t,ht,modes⟩ := work x sep
  refine ⟨t,ht,?_⟩
  intro y
  obtain ⟨i,v⟩ := small M (fun i => ((t*x i:ℝ):AddCircle (1:ℝ))) hM modes y
  exact ⟨i,(dist_comm ..).trans_lt v⟩

end
end OMA.BosMean06

/- A sublacunary family of dilations cannot avoid the same open arc on
arbitrarily large separated clusters. The original sequence need not be
monotone: use its first crossing of the requested scale. -/

namespace OMA.Bos06

open Filter Set

private theorem mesh (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hunb : ¬ BddAbove (range r))
    (hsub : Tendsto (fun n => r (n+1) / r n) atTop (nhds 1))
    (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ≥ R, ∃ n, y ≤ r n ∧ r n ≤ (1+η)*y := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hsub.eventually_lt_const (by linarith : 1 < 1+η))
  let R := 1 + ∑ i ∈ Finset.range (N+1), r i
  have hsum : 0 ≤ ∑ i ∈ Finset.range (N+1), r i := Finset.sum_nonneg fun i _ => (hr i).le
  refine ⟨R, by dsimp [R]; linarith, fun y hy => ?_⟩
  have hex : ∃ i, y ≤ r i := by
    by_contra! h
    exact hunb ⟨y, fun _ ⟨i,hi⟩ => hi ▸ (h i).le⟩
  let i := Nat.find hex
  have hi : y ≤ r i := Nat.find_spec hex
  have hiN : N < i := by
    by_contra! hle
    have hh := Finset.single_le_sum (fun n (_ : n ∈ Finset.range (N+1)) => (hr n).le)
      (Finset.mem_range.mpr (show i < N+1 by omega))
    dsimp [R] at hy
    linarith
  have hprev : r (i-1) < y := lt_of_not_ge (Nat.find_min hex (show i-1 < i by omega))
  have hratio := (div_lt_iff₀ (hr (i-1))).1 (hN (i-1) (by omega))
  rw [show i-1+1 = i by omega] at hratio
  exact ⟨i, hi, hratio.le.trans (mul_le_mul_of_nonneg_left hprev.le (by linarith))⟩

private theorem coe_dist_le (x y : ℝ) : dist (x : AddCircle (1:ℝ)) (y : AddCircle (1:ℝ)) ≤ |x-y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, ← Real.norm_eq_abs]
  exact QuotientAddGroup.norm_mk_le_norm

/-- A common omitted ball imposes a local packing bound independent of the
separation ratio B. Only the threshold for small intervals depends on B. -/
theorem packing
    (mix : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 0 < M ∧ ∀ δ : ℝ, 0 < δ →
      ∃ T : ℝ, 1 ≤ T ∧ ∀ x : Fin M → ℝ, (∀ i, x i ∈ Icc 0 1) →
        (∀ i j, i ≠ j → δ ≤ |x i - x j|) →
          ∃ t ∈ Icc 1 T, ∀ y : AddCircle (1 : ℝ), ∃ i,
            dist ((t*x i : ℝ) : AddCircle (1:ℝ)) y < ε)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hunb : ¬ BddAbove (range r))
    (hsub : Tendsto (fun n => r (n+1) / r n) atTop (nhds 1))
    (c : AddCircle (1 : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ B : ℕ, 0 < B → ∃ δ : ℝ, 0 < δ ∧ ∀ a L : ℝ, 0 < L → L ≤ δ →
      ∀ S : Finset ℝ, (∀ x∈S, x ∈ Icc a (a+L)) →
        (∀ x∈S, ∀ n : ℕ, ε ≤ dist ((x*r n : ℝ) : AddCircle (1:ℝ)) c) →
        (∀ x∈S, ∀ y∈S, x ≠ y → L/(B:ℝ) ≤ |x-y|) → S.card ≤ K := by
  classical
  obtain ⟨M, _, hM⟩ := mix (ε/2) (by positivity)
  refine ⟨M, fun B hB => ?_⟩
  have hB' : 0 < (B:ℝ) := by exact_mod_cast hB
  obtain ⟨T,hT,hmix⟩ := hM (1/(B:ℝ)) (by positivity)
  have hT' : 0 < T := by linarith
  let η := (ε/2) / T
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨R,hR,hm⟩ := mesh r hr hunb hsub η hη
  refine ⟨1/R, by positivity, fun a L hL hLs S hbox hgap hsep => ?_⟩
  by_contra! hcard
  let e (i : Fin M) : S := S.equivFin.symm (i.castLE hcard.le)
  have einj : Function.Injective e := fun i j hij =>
    Fin.ext (congrArg (fun j : Fin S.card => j.val) (S.equivFin.symm.injective hij))
  let f (i : Fin M) := ((e i : ℝ) - a) / L
  have hf (i : Fin M) : f i ∈ Icc 0 1 := by
    obtain ⟨lo,hi⟩ := hbox _ (e i).property
    exact ⟨div_nonneg (by linarith) hL.le, (div_le_one hL).2 (by linarith)⟩
  have hs (i j : Fin M) (hne : i ≠ j) : 1 / (B:ℝ) ≤ |f i-f j| := by
    have h := hsep _ (e i).property _ (e j).property
      (fun hh => hne (einj (Subtype.ext hh)))
    dsimp only [f]
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hL, le_div_iff₀ hL]
    simpa [div_eq_mul_inv, mul_comm] using h
  obtain ⟨t,ht,hdense⟩ := hmix f hf hs
  obtain ⟨n,hmlo,hmhi⟩ := hm (t/L) (by
    apply (le_div_iff₀ hL).2
    have h := (le_div_iff₀ hR).1 hLs
    linarith [ht.1, mul_comm L R])
  have hlo := (div_le_iff₀ hL).1 hmlo
  have hhi : r n * L ≤ (1+η)*t := by
    rw [← mul_div_assoc] at hmhi
    exact (le_div_iff₀ hL).1 hmhi
  have herr : |r n * L - t| ≤ ε/2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    have hscale : η*T = ε/2 := div_mul_cancel₀ _ hT'.ne'
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hη.le]
  let shift : AddCircle (1:ℝ) := ↑(a*r n)
  obtain ⟨i,hi⟩ := hdense (c-shift)
  have hident : (e i:ℝ)*r n - a*r n - t*f i = (r n * L - t)* f i := by
    have h := div_mul_cancel₀ ((e i:ℝ)-a) hL.ne'
    change f i * L = (e i:ℝ)-a at h
    linear_combination -r n * h
  have hdist : dist (((e i:ℝ)*r n - a*r n : ℝ) : AddCircle (1:ℝ))
      ((t*f i : ℝ) : AddCircle (1:ℝ)) ≤ ε/2 := by
    apply (coe_dist_le _ _).trans
    rw [hident, abs_mul, abs_of_nonneg (hf i).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hf i).2).trans herr
  have htriangle := dist_triangle (((e i:ℝ)*r n - a*r n : ℝ) : AddCircle (1:ℝ))
      ((t*f i : ℝ) : AddCircle (1:ℝ)) (c-shift)
  rw [AddCircle.coe_sub, show ((a*r n:ℝ):AddCircle (1:ℝ)) = shift from rfl,
    dist_sub_right] at htriangle
  rw [AddCircle.coe_sub, show ((a*r n:ℝ):AddCircle (1:ℝ)) = shift from rfl] at hdist
  linarith [hgap _ (e i).property n]

/-- Nondense orbits omit one of a countable family of balls. -/
theorem exceptional (r : ℕ → ℝ)
    (gap : ∀ (c : AddCircle (1:ℝ)) (ε : ℝ), 0 < ε →
      dimH {x : ℝ | ∀ n, ε ≤ dist ((x*r n : ℝ) : AddCircle (1:ℝ)) c} = 0) :
    dimH {x : ℝ | ¬ Dense (range fun n => ((x*r n : ℝ) : AddCircle (1:ℝ)))} = 0 := by
  obtain ⟨D, hD, hden⟩ := TopologicalSpace.exists_countable_dense (AddCircle (1:ℝ))
  let : Countable D := hD.to_subtype
  let G (j : D × {q : ℚ // 0 < q}) : Set ℝ :=
    {x | ∀ n, (j.2.val:ℝ) ≤ dist ((x*r n : ℝ) : AddCircle (1:ℝ)) j.1.val}
  have hg (j : D × {q : ℚ // 0 < q}) : dimH (G j) = 0 := gap _ _ (by exact_mod_cast j.2.property)
  have hs : {x : ℝ | ¬ Dense (range fun n => ((x*r n : ℝ) : AddCircle (1:ℝ)))} ⊆ ⋃ j, G j := by
    intro x hx
    change ¬ Dense _ at hx
    rw [Metric.dense_iff] at hx
    push Not at hx
    obtain ⟨y, ε, hε, hempty⟩ := hx
    obtain ⟨c,hc,hDmem⟩ := (Metric.dense_iff.1 hden y (ε/2) (by positivity))
    obtain ⟨q,hq,hqε⟩ := exists_rat_btwn (show (0:ℝ) < ε/2 by positivity)
    apply mem_iUnion.2 ⟨(⟨c,hDmem⟩, ⟨q,by exact_mod_cast hq⟩), ?_⟩
    intro n
    by_contra! hh
    have hn := dist_triangle (((x*r n : ℝ) : AddCircle (1:ℝ))) c y
    have hm : ((x*r n : ℝ) : AddCircle (1:ℝ)) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball] at hc ⊢
      change dist _ c < (q:ℝ) at hh
      linarith
    exact (Set.not_nonempty_iff_eq_empty.mpr hempty) ⟨_, hm, ⟨n,rfl⟩⟩
  apply le_antisymm _ bot_le
  exact (dimH_mono hs).trans (by rw [dimH_iUnion]; exact iSup_le fun j => (hg j).le)

end OMA.Bos06

/- Uniform local packing at arbitrarily fine scale forces Hausdorff dimension zero. -/

open MeasureTheory Filter Set Finset
open scoped Topology ENNReal NNReal
namespace OMA.HausPacking06

private theorem net {E : Set ℝ} {a L s : ℝ} {K : ℕ} (hs : 0<s)
    (pack : ∀ S : Finset ℝ, (∀ x∈S, x∈Icc a (a+L)) → (∀ x∈S, x∈E) →
      (∀ x∈S, ∀ y∈S, x≠y → s≤|x-y|) → S.card ≤ K) :
    ∃ T : Finset ℝ, T.card ≤ K ∧ ∀ x∈E, x∈Icc a (a+L) → ∃ y∈T, |x-y| < s := by
  classical
  let good (S : Finset ℝ) := (∀ x∈S, x∈Icc a (a+L)) ∧ (∀ x∈S, x∈E) ∧
      (∀ x∈S, ∀ y∈S, x≠y → s≤|x-y|)
  let sizes := (range (K+1)).filter (fun k => ∃ S : Finset ℝ, good S ∧ S.card=k)
  have h0 : 0∈sizes := by
    apply mem_filter.mpr
    exact ⟨by simp, ∅, by simp [good], by simp⟩
  let m := sizes.max' ⟨0,h0⟩
  have hm : m∈sizes := max'_mem ..
  obtain ⟨S,ok,hcard⟩ := (mem_filter.mp hm).2
  refine ⟨S,pack S ok.1 ok.2.1 ok.2.2,?_⟩
  intro x hx hI
  by_contra! bad
  have nx : x ∉ S := by intro h; simpa using (lt_of_lt_of_le hs (bad x h))
  have ins : good (insert x S) := by
    refine ⟨?_,?_,?_⟩
    · exact (Finset.forall_mem_insert _ _ _).mpr ⟨hI,ok.1⟩
    · exact (Finset.forall_mem_insert _ _ _).mpr ⟨hx,ok.2.1⟩
    · intro u hu v hv uv
      rcases mem_insert.mp hu with rfl|hus
      · rcases mem_insert.mp hv with rfl|hvs
        · exact (uv rfl).elim
        · exact bad v hvs
      · rcases mem_insert.mp hv with rfl|hvs
        · rw [abs_sub_comm]; exact bad u hus
        · exact ok.2.2 _ hus _ hvs uv
  have bigger : (insert x S).card ∈ sizes := by
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by have := pack _ ins.1 ins.2.1 ins.2.2; omega),_,ins,rfl⟩
  have le : (insert x S).card ≤ m := le_max' sizes _ bigger
  rw [card_insert_of_notMem nx, hcard] at le
  omega

private theorem levels {E : Set ℝ} {δ q : ℝ} (hδ : 0<δ) (hq : 0<q) (hq1 : q≤1) {K : ℕ}
    (next : ∀ a L : ℝ, 0<L → L≤δ → ∃ S : Finset ℝ, S.card ≤ K ∧
      ∀ x∈E, x∈Icc a (a+L) → ∃ b∈S, x∈Icc b (b+L*q))
    (a : ℝ) (j : ℕ) : ∃ S : Finset ℝ, S.card ≤ K^j ∧
      ∀ x∈E, x∈Icc a (a+δ) → ∃ b∈S, x∈Icc b (b+δ*q^j) := by
  classical
  induction j with
  | zero => exact ⟨{a},by simp, fun x _ hx => ⟨a,by simp,by simpa using hx⟩⟩
  | succ j ih =>
    obtain ⟨S,size,cover⟩ := ih
    let w := δ*q^j
    have pos : 0<w := by dsimp [w]; positivity
    have ub : w≤δ := by dsimp [w]; exact mul_le_of_le_one_right hδ.le (pow_le_one₀ hq.le hq1)
    choose T count hit using (fun b => next b w pos ub)
    refine ⟨S.biUnion T,?_,?_⟩
    · calc (S.biUnion T).card ≤ ∑ b∈S,(T b).card := card_biUnion_le
           _ ≤ ∑ _∈S, K := sum_le_sum fun b _ => count b
           _ = S.card*K := by simp
           _ ≤ K^(j+1) := by rw [pow_succ]; gcongr
    · intro x hx hi
      obtain ⟨b,hb,hc⟩ := cover x hx hi
      obtain ⟨c,hc',mem⟩ := hit b x hx hc
      exact ⟨c,mem_biUnion.mpr ⟨b,hb,hc'⟩, by simpa [w,pow_succ,mul_assoc] using mem⟩

/-- An arbitrarily fine separated-packing bound implies an interval cover
of bounded total d-content at every level, for every positive exponent. -/
theorem covers (E : Set ℝ) (pack : ∃ K : ℕ, ∀ B : ℕ, 0<B →
    ∃ δ : ℝ, 0<δ ∧ ∀ a L : ℝ, 0<L → L≤δ → ∀ S : Finset ℝ,
      (∀ x∈S, x∈Icc a (a+L)) → (∀ x∈S, x∈E) →
      (∀ x∈S, ∀ y∈S, x≠y → L/(B:ℝ)≤|x-y|) → S.card≤K)
    (d : ℝ≥0) (hd : 0<d) : ∃ δ q : ℝ, ∃ K : ℕ,
    0<δ ∧ 0<q ∧ q<1 ∧ (K:ℝ)*q^(d:ℝ)≤1 ∧
    ∀ (a:ℝ) (n:ℕ), ∃ S : Finset ℝ, S.card≤K^n ∧
      ∀ x∈E, x∈Icc a (a+δ) → ∃ b∈S, x∈Icc b (b+δ*q^n) := by
  classical
  obtain ⟨K,hK⟩ := pack
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)
  have hpow : Tendsto (fun b : ℕ => (K:ℝ)*(2/(b:ℝ))^(d:ℝ)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (d:ℝ) (.inr hd'.le)).tendsto.comp hlim
    simpa [Function.comp_def,Real.zero_rpow hd'.ne'] using h.const_mul (K:ℝ)
  obtain ⟨B,hB,hq,hsmall⟩ := ((eventually_gt_atTop (0:ℕ)).and
    ((hlim.eventually_lt_const (by norm_num : (0:ℝ)<1)).and
      (hpow.eventually_lt_const (by norm_num : (0:ℝ)<1)))).exists
  obtain ⟨δ,hδ,packed⟩ := hK B hB
  have hb' : 0<(B:ℝ) := by exact_mod_cast hB
  have qpos : 0<2/(B:ℝ) := by positivity
  refine ⟨δ,2/(B:ℝ),K,hδ,qpos,hq,hsmall.le,levels hδ qpos hq.le (fun a L hL hLδ => ?_)⟩
  have spos : 0<L/(B:ℝ) := by positivity
  obtain ⟨T,card,hits⟩ := net spos (packed a L hL hLδ)
  refine ⟨T.image (fun y => y-L/(B:ℝ)),card_image_le.trans card,?_⟩
  intro x hx hi
  obtain ⟨y,hy,hxy⟩ := hits x hx hi
  refine ⟨y-L/(B:ℝ),mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
  obtain ⟨h1,h2⟩ := abs_lt.mp hxy
  constructor
  · linarith
  · have e : L*(2/(B:ℝ)) = 2*(L/(B:ℝ)) := by ring
    rw [e]; linarith

end OMA.HausPacking06

/- Fine interval covers with bounded total (d)-content give a local dimension
bound. A countable grid extends the bound to the whole exceptional set. -/
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace OMA.HausMeasure06

private theorem local_bound (E : Set ℝ) (a δ q : ℝ) (d : ℝ≥0) (K : ℕ)
    (hδ : 0<δ) (hq : 0<q) (hq1 : q<1) (cost : (K:ℝ)*q^(d:ℝ) ≤ 1)
    (cover : ∀ n : ℕ, ∃ S : Finset ℝ, S.card ≤ K^n ∧
      ∀ x∈E, x∈Icc a (a+δ) → ∃ b∈S, x∈Icc b (b+δ*q^n)) :
    dimH (E ∩ Icc a (a+δ)) ≤ d := by
  classical
  choose S card hit using cover
  let t (n : ℕ) (b : ↥(S n)) : Set ℝ := Icc b.val (b.val+δ*q^n)
  let r (n : ℕ) := ENNReal.ofReal (δ*q^n)
  have diam (n : ℕ) (b : ↥(S n)) : ediam (t n b) = r n := by simp [t,r,Real.ediam_Icc]
  have small : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul δ
    simpa [r,Function.comp_def] using (ENNReal.continuous_ofReal.tendsto _).comp h
  have covered (n : ℕ) : E ∩ Icc a (a+δ) ⊆ ⋃ b, t n b := by
    intro x hx
    obtain ⟨b,hb,hx'⟩ := hit n x hx.1 hx.2
    exact mem_iUnion.mpr ⟨⟨b,hb⟩,hx'⟩
  have sum_le (n : ℕ) : (∑ b : ↥(S n), ediam (t n b) ^ (d:ℝ)) ≤ ENNReal.ofReal (δ^(d:ℝ)) := by
    simp only [diam,r,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    rw [ENNReal.ofReal_rpow_of_pos (x:=δ*q^n) (p:=(d:ℝ)) (by positivity),
      ←ENNReal.ofReal_natCast (S n).card,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((K:ℝ)^n)*(δ*q^n)^(d:ℝ) := by gcongr; exact_mod_cast card n
      _ = δ^(d:ℝ) * ((K:ℝ)*q^(d:ℝ))^n := by
        rw [Real.mul_rpow hδ.le (by positivity),← Real.rpow_natCast_mul hq.le,
          mul_comm (n:ℝ) (d:ℝ),Real.rpow_mul_natCast hq.le,mul_pow]
        ring
      _ ≤ δ^(d:ℝ) := mul_le_of_le_one_right (by positivity)
        (pow_le_one₀ (by positivity) cost)
  have bound := Measure.hausdorffMeasure_le_liminf_sum (d:ℝ) _ r small t
    (Eventually.of_forall fun n b => (diam n b).le) (Eventually.of_forall covered)
  have lim : liminf (fun n => ∑ b : ↥(S n), ediam (t n b)^(d:ℝ)) atTop ≤
      ENNReal.ofReal (δ^(d:ℝ)) := calc
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (δ^(d:ℝ))) atTop :=
      liminf_le_liminf (Eventually.of_forall sum_le)
    _ = _ := liminf_const _
  exact dimH_le_of_hausdorffMeasure_ne_top ((bound.trans lim).trans_lt ENNReal.ofReal_lt_top).ne

theorem zero_of_levels (E : Set ℝ)
    (h : ∀ d : ℝ≥0, 0<d → ∃ δ q : ℝ, ∃ K : ℕ, 0<δ ∧ 0<q ∧ q<1 ∧
      (K:ℝ)*q^(d:ℝ) ≤ 1 ∧ ∀ (a : ℝ) (n : ℕ), ∃ S : Finset ℝ, S.card ≤ K^n ∧
      ∀ x∈E, x∈Icc a (a+δ) → ∃ b∈S, x∈Icc b (b+δ*q^n)) : dimH E=0 := by
  classical
  by_contra! nz
  obtain ⟨d,hd,lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr nz)
  obtain ⟨δ,q,K,hδ,hq,hq1,cost,cover⟩ := h d (by exact_mod_cast hd)
  let U (i : ℤ) := E ∩ Icc ((i:ℝ)*δ) ((i:ℝ)*δ+δ)
  have all : E ⊆ ⋃ i : ℤ, U i := by
    intro x hx
    let i := ⌊x/δ⌋
    refine mem_iUnion.mpr ⟨i,hx,?_,?_⟩
    · exact (le_div_iff₀ hδ).mp (Int.floor_le _)
    · have hi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x/δ))
      simpa [i,add_mul] using hi.le
  apply lt.not_ge
  calc dimH E ≤ dimH (⋃ i : ℤ, U i) := dimH_mono all
       _ = _ := dimH_iUnion U
       _ ≤ _ := iSup_le fun i => local_bound E _ δ q d K hδ hq hq1 cost (cover _)

end OMA.HausMeasure06

theorem OMA.solution : type_of% @Bugeaud06.boshernitzan := by
  intro r hr hunb hsub
  apply OMA.Bos06.exceptional r
  intro c ε hε
  apply OMA.HausMeasure06.zero_of_levels
  apply OMA.HausPacking06.covers
  exact OMA.Bos06.packing (OMA.BosMean06.mixing_of_test OMA.FejerB106.net) r hr hunb hsub c ε hε
