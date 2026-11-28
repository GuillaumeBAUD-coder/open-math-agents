import OMAStatements.S_mo_342070
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
 
/-!
Matched binomial tails and likelihood at the Clopper–Pearson endpoints.
Source: MathOverflow question 342070, asked by user113925.
The argument below proves both comparisons for every tail probability below one half.
-/

open Set Filter
open scoped BigOperators Topology
open OMA.S_mo_342070
namespace MatchedBinomial

lemma mass_cont (n k : ℕ) : Continuous (mass n k) := by
  unfold mass
  fun_prop

lemma lower_cont (n k : ℕ) : Continuous (lowerTail n k) := by
  unfold lowerTail mass
  fun_prop

lemma upper_cont (n k : ℕ) : Continuous (upperTail n k) := by
  unfold upperTail mass
  fun_prop

lemma mass_pos_int {n k : ℕ} (hk : k ≤ n) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    0 < mass n k x := by
  have hc : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  exact mul_pos (mul_pos hc (pow_pos hx.1 _)) (pow_pos (sub_pos.mpr hx.2) _)

lemma pow_rate (x : ℝ) (hx : x ≠ 0) (k : ℕ) :
    (k:ℝ) * x^(k-1) = (k:ℝ)*x^k/x := by
  cases k with
  | zero => simp
  | succ k => simp only [Nat.succ_sub_one, pow_succ]; field_simp

lemma mass_d {n k : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    HasDerivAt (mass n k)
      (mass n k x * ((k:ℝ)/x - ((n-k:ℕ):ℝ)/(1-x))) x := by
  have hh := (((hasDerivAt_id x).pow k).const_mul (n.choose k : ℝ)).mul
    (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).pow (n-k))
  apply hh.congr_deriv
  simp only [Pi.pow_apply, Pi.sub_apply, id_eq, mul_one, zero_sub, mul_neg]
  rw [pow_rate x (ne_of_gt hx.1), pow_rate (1-x) (ne_of_gt (sub_pos.mpr hx.2))]
  unfold mass
  ring

lemma adj_mass {n k : ℕ} (hk : k < n) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    ((k+1:ℕ):ℝ)*mass n (k+1) x/x = ((n-k:ℕ):ℝ)*mass n k x/(1-x) := by
  have hc : (n.choose (k+1):ℝ) * ((k+1:ℕ):ℝ) = (n.choose k:ℝ) * ((n-k:ℕ):ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have e : n-k = n-(k+1)+1 := by omega
  have hp : x ≠ 0 := ne_of_gt hx.1
  have hq : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  unfold mass
  rw [show (1-x)^(n-k) = (1-x)^(n-(k+1))*(1-x) by rw [e, pow_succ], pow_succ x k]
  calc
    _ = ((n.choose (k+1):ℝ)*((k+1:ℕ):ℝ)) * x^k * (1-x)^(n-(k+1)) := by field_simp
    _ = _ := by rw [hc]; field_simp

lemma lower_d {n k : ℕ} (hk : k ≤ n) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    HasDerivAt (lowerTail n k) (- (((n-k:ℕ):ℝ) * mass n k x / (1-x))) x := by
  induction k with
  | zero =>
    have eqf : lowerTail n 0 = mass n 0 := by funext y; simp [lowerTail]
    rw [eqf]
    apply (mass_d (n:=n) (k:=0) hx).congr_deriv
    push_cast; ring
  | succ k ih =>
    have hl := (ih (by omega)).add (mass_d (n:=n) (k:=k+1) hx)
    have ha := adj_mass (n:=n) (k:=k) (by omega) hx
    have eqf : lowerTail n (k+1) = lowerTail n k + mass n (k+1) := by
      funext y; simp [lowerTail, Finset.sum_range_succ]
    rw [eqf]
    apply hl.congr_deriv
    linear_combination ha

lemma tail_sum {n k : ℕ} (hk : k ≤ n) (x : ℝ) :
    lowerTail n k x + upperTail n k x = 1 + mass n k x := by
  have full : ∑ j ∈ Finset.range (n+1), mass n j x = 1 := by
    simpa [mass, mul_comm, mul_left_comm, mul_assoc] using (add_pow x (1-x) n).symm
  have join := Finset.sum_range_add_sum_Ico (fun j => mass n j x) (show k ≤ n+1 by omega)
  rw [Finset.Ico_add_one_right_eq_Icc] at join
  unfold lowerTail upperTail
  rw [Finset.sum_range_succ]
  linarith

lemma upper_d {n k : ℕ} (hk : k ≤ n) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    HasDerivAt (upperTail n k) ((k:ℝ)*mass n k x/x) x := by
  have hh := ((hasDerivAt_const x (1:ℝ)).add (mass_d (n:=n) (k:=k) hx)).sub (lower_d hk hx)
  have eqf : upperTail n k = (fun _ => (1:ℝ)) + mass n k - lowerTail n k := by
    funext y
    have := tail_sum hk y
    change upperTail n k y = 1 + mass n k y - lowerTail n k y
    linarith
  rw [eqf]
  apply hh.congr_deriv
  ring

lemma mass_zero_left {n k : ℕ} (hk : 0 < k) : mass n k 0 = 0 := by
  simp [mass,zero_pow (Nat.ne_of_gt hk)]
lemma mass_zero_right {n k : ℕ} (hk : k < n) : mass n k 1 = 0 := by
  simp [mass,zero_pow (show n-k ≠ 0 by omega)]
lemma lower_one {n k : ℕ} (hk : k < n) : lowerTail n k 1 = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact mass_zero_right (by have := Finset.mem_range.mp hi; omega)
lemma upper_zero {n k : ℕ} (hk : 0 < k) : upperTail n k 0 = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact mass_zero_left (lt_of_lt_of_le hk (Finset.mem_Icc.mp hi).1)

lemma inverse_unit {f : ℝ → ℝ} (hm : StrictMonoOn f (Icc 0 1)) (hc : Continuous f)
    (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ t, g t ∈ Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc 0 1, f (g t) = t) ∧ g 0 = 0 ∧
      ∀ t ∈ Set.Ioo 0 1, g t ∈ Set.Ioo 0 1 := by
  let I := Icc (0:ℝ) 1
  have image : f '' I = I := by
    dsimp [I]; rw [hc.continuousOn.image_Icc_of_monotoneOn zero_le_one hm.monotoneOn,h₀,h₁]
  let e : I ≃o I := (hm.orderIso f I).trans (OrderIso.setCongr _ _ image)
  let g (t : ℝ) : ℝ := (e.symm (projIcc 0 1 zero_le_one t) : I)
  have mem (t : ℝ) : g t ∈ Set.Icc 0 1 := (e.symm _).property
  have eqn (t : ℝ) (ht : t ∈ Set.Icc 0 1) : f (g t) = t := by
    have he := congrArg Subtype.val (e.apply_symm_apply (projIcc 0 1 zero_le_one t))
    change f (g t) = (projIcc 0 1 zero_le_one t : I) at he
    simpa [projIcc_of_mem zero_le_one ht] using he
  refine ⟨g, continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc), mem, eqn, ?_, ?_⟩
  · apply hm.injOn (mem 0) (by simp)
    rw [eqn 0 (by simp),h₀]
  · intro t ht
    have h := eqn t ⟨ht.1.le,ht.2.le⟩
    constructor
    · refine (mem t).1.lt_of_ne ?_
      intro z; rw [← z,h₀] at h; exact ht.1.ne h
    · refine (mem t).2.lt_of_ne ?_
      intro z; rw [z,h₁] at h; exact ht.2.ne h.symm

lemma positive_barrier {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hc : Continuous f) (hz : f 0 = 0)
    (hd : ∀ t ∈ Set.Ioc (0:ℝ) T, f t < 0 → ∃ d, 0 < d ∧ HasDerivAt f d t) :
    0 ≤ f T := by
  by_contra! hneg
  obtain ⟨c,hcI,hmin⟩ := isCompact_Icc.exists_isMinOn (s:=Icc 0 T)
    (Set.nonempty_Icc.mpr hT.le) hc.continuousOn
  have cneg : f c < 0 := (isMinOn_iff.mp hmin T (right_mem_Icc.mpr hT.le)).trans_lt hneg
  have cpos : 0 < c := hcI.1.lt_of_ne (fun h => by rw [← h,hz] at cneg; exact lt_irrefl _ cneg)
  obtain ⟨d,dpos,dh⟩ := hd c ⟨cpos,hcI.2⟩ cneg
  have hs := dh.tendsto_slope_zero_left.eventually (Ioi_mem_nhds dpos)
  have hleft : ∀ᶠ t : ℝ in 𝓝[<] 0, t < 0 := self_mem_nhdsWithin
  have hright : ∀ᶠ t : ℝ in 𝓝[<] 0, -c < t := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (neg_neg_of_pos cpos))
  obtain ⟨t,ht,hleft,hright⟩ := (hs.and (hleft.and hright)).exists
  have hmin' := isMinOn_iff.mp hmin (c+t) (show c+t ∈ Set.Icc 0 T from ⟨by linarith, by linarith [hcI.2]⟩)
  change 0 < t⁻¹ * (f (c+t)-f c) at ht
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hleft.le) (sub_nonneg.mpr hmin'))) ht

/-- Log likelihood on a pair of odds symmetric around the geometric mean s. -/
noncomputable def gap (a b s r : ℝ) : ℝ :=
  (a-b) * Real.log r + (a+b) * (Real.log (s+r) - Real.log (1+s*r))

lemma gap_nonpos {a b s r : ℝ} (hab : a ≤ b) (hs : 0 < s) (hc : a ≤ b*s) (hr : 1 ≤ r) :
    gap a b s r ≤ 0 := by
  let g := gap a b s
  have dh (z : ℝ) (hz : 0 < z) : HasDerivAt g
      ((a-b)/z + (a+b)*(1/(s+z)-s/(1+s*z))) z := by
    have d₁ := (Real.hasDerivAt_log hz.ne').const_mul (a-b)
    have d₂ := ((hasDerivAt_id z).const_add s).log (by positivity : s+z ≠ 0)
    have d₃ := (((hasDerivAt_id z).const_mul s).const_add 1).log (by positivity : 1+s*z ≠ 0)
    apply (d₁.add ((d₂.sub d₃).const_mul (a+b))).congr_deriv
    simp [div_eq_mul_inv]
  have hg : AntitoneOn g (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    · intro z hz; exact (dh z hz).continuousAt.continuousWithinAt
    · intro z hz; exact (dh z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : 0 < z := interior_subset hz
      rw [(dh z hz').deriv]
      have den : 0 < z*(s+z)*(1+s*z) := by positivity
      apply nonpos_of_mul_nonpos_left (b := z*(s+z)*(1+s*z)) _ den
      calc
        _ = (a-b)*s*(z-1)^2 + 2*z*(1+s)*(a-b*s) := by
          field_simp [ne_of_gt hz',show s+z ≠ 0 by positivity,show 1+s*z ≠ 0 by positivity]
          ring
        _ ≤ 0 := add_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hab) hs.le) (sq_nonneg _))
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hc))
  have z := hg (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) (show r ∈ Set.Ioi 0 from lt_of_lt_of_le zero_lt_one hr) hr
  simpa [g,gap,add_comm s 1] using z

lemma matched_odds {n k : ℕ} (hkn : 2*k ≤ n) (hk : 0 < k)
    {u v : ℝ} (hu : u ∈ Set.Ioo 0 1) (hv : v ∈ Set.Ioo 0 1) (huv : u < v)
    (hm : mass n k u < mass n k v) :
    (((n-k:ℕ):ℝ))^2*u*v < (k:ℝ)^2*(1-u)*(1-v) := by
  let a : ℝ := k
  let b : ℝ := n-k
  have hbval : b = ((n-k:ℕ):ℝ) := by dsimp [b]; exact (Nat.cast_sub (by omega : k ≤ n)).symm
  have ha : 0 < a := by dsimp [a]; exact_mod_cast hk
  have hab : a ≤ b := by rw [hbval]; dsimp [a]; exact_mod_cast (show k ≤ n-k by omega)
  have hb : 0 < b := ha.trans_le hab
  have hu' : 0 < 1-u := sub_pos.mpr hu.2
  have hv' : 0 < 1-v := sub_pos.mpr hv.2
  let x := u/(1-u)
  let y := v/(1-v)
  have hx : 0 < x := div_pos hu.1 hu'
  have hy : 0 < y := div_pos hv.1 hv'
  have hxy : x < y := by
    dsimp [x,y]; apply (div_lt_div_iff₀ hu' hv').2; nlinarith
  let r := Real.sqrt (y/x)
  have hr0 : 0 < r := Real.sqrt_pos.2 (div_pos hy hx)
  have hr2 : r^2 = y/x := Real.sq_sqrt (div_nonneg hy.le hx.le)
  have hr2x : r^2*x=y := (eq_div_iff hx.ne').mp hr2
  have hr : 1 ≤ r := by
    have : 1 < y/x := (one_lt_div hx).2 hxy
    nlinarith
  let s := x*r
  have hs : 0 < s := mul_pos hx hr0
  have sy : s*r = y := by dsimp [s]; nlinarith only [hr2x]
  have su : s/(s+r)=u := by
    apply (div_eq_iff (show s+r ≠ 0 by positivity)).2
    have hxu : x*(1-u)=u := div_mul_cancel₀ _ hu'.ne'
    dsimp [s]; linear_combination r*hxu
  have sv : (s*r)/(1+s*r)=v := by
    apply (div_eq_iff (show 1+s*r ≠ 0 by positivity)).2
    rw [sy]
    have hyv : y*(1-v)=v := div_mul_cancel₀ _ hv'.ne'
    linarith
  have su' : r/(s+r)=1-u := by rw [← su]; field_simp; ring
  have sv' : 1/(1+s*r)=1-v := by rw [← sv]; field_simp; ring
  have hc : (0:ℝ)<n.choose k := by exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have pl (p : ℝ) (hp : p ∈ Set.Ioo 0 1) : 0 < mass n k p :=
    mul_pos (mul_pos hc (pow_pos hp.1 _)) (pow_pos (sub_pos.mpr hp.2) _)
  have hl := Real.log_lt_log (pl u hu) hm
  have logm (p : ℝ) (hp : p ∈ Set.Ioo 0 1) :
      Real.log (mass n k p)=Real.log (n.choose k : ℝ)+a*Real.log p+b*Real.log (1-p) := by
    simp only [mass,Real.log_mul (ne_of_gt (mul_pos hc (pow_pos hp.1 _))) (pow_ne_zero _ (sub_pos.mpr hp.2).ne'),
      Real.log_mul hc.ne' (pow_ne_zero _ hp.1.ne'),Real.log_pow,hbval,a]
  rw [logm u hu,logm v hv,← su',← sv',← su,← sv] at hl
  have ha₁ : s+r ≠ 0 := by positivity
  have ha₂ : 1+s*r ≠ 0 := by positivity
  have ha₃ : s*r ≠ 0 := by positivity
  simp only [Real.log_div hs.ne' ha₁, Real.log_div hr0.ne' ha₁, Real.log_div ha₃ ha₂,
    Real.log_div one_ne_zero ha₂, Real.log_mul hs.ne' hr0.ne', Real.log_one, zero_sub] at hl
  by_contra! h
  have habs : a ≤ b*s := by
    have hs2 : s^2=x*y := by dsimp [s]; linear_combination x*hr2x
    have he : s^2*(1-u)*(1-v)=u*v := by rw [hs2]; dsimp [x,y]; field_simp
    rw [← hbval] at h
    change a^2*(1-u)*(1-v) ≤ b^2*u*v at h
    rw [mul_assoc (b^2) u v, ← he] at h
    have h' : a^2 ≤ b^2*s^2 := by
      exact (mul_le_mul_iff_left₀ (mul_pos hu' hv')).mp (by nlinarith only [h])
    by_contra! hlt
    have hh := mul_self_lt_mul_self (mul_pos hb hs).le hlt
    nlinarith only [hh,h']
  have := gap_nonpos hab hs habs hr
  unfold gap at this
  linarith

lemma compare_matched {n k : ℕ} (hk : 0 < k) (hkn : 2*k ≤ n)
    (odds_bound : ∀ {u v : ℝ}, u ∈ Set.Ioo 0 1 → v ∈ Set.Ioo 0 1 → u < v →
        mass n k u < mass n k v →
        ((n-k:ℕ):ℝ)^2*u*v < (k:ℝ)^2*(1-u)*(1-v))
    {δ pBig pSmall : ℝ} (hδ : 0 < δ) (hhalf : δ < 1/2)
    (hB : pBig ∈ Set.Icc 0 1) (hS : pSmall ∈ Set.Icc 0 1)
    (hL : lowerTail n k pBig = δ) (hU : upperTail n k pSmall = δ) :
    mass n (k-1) pBig ≤ mass n (k-1) pSmall ∧ mass n k pBig ≤ mass n k pSmall := by
  have hlt : k < n := by omega
  have ha : (0:ℝ) < k := by exact_mod_cast hk
  have hb : (0:ℝ) < (n-k:ℕ) := by exact_mod_cast (show 0 < n-k by omega)
  let U := upperTail n k
  let L := lowerTail n k
  let M := mass n k
  have monoU : StrictMonoOn U (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (upper_cont n k).continuousOn
    intro x hx; rw [interior_Icc] at hx
    rw [(upper_d hlt.le hx).deriv]
    exact div_pos (mul_pos ha (mass_pos_int hlt.le hx)) hx.1
  have antiL : StrictAntiOn L (Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (lower_cont n k).continuousOn
    intro x hx; rw [interior_Icc] at hx
    rw [(lower_d hlt.le hx).deriv]
    exact neg_neg_of_pos (div_pos (mul_pos hb (mass_pos_int hlt.le hx)) (sub_pos.mpr hx.2))
  have u0 : U 0 = 0 := upper_zero hk
  have l1 : L 1 = 0 := lower_one hlt
  have u1 : U 1 = 1 := by
    have hh := tail_sum hlt.le 1; rw [lower_one hlt,mass_zero_right hlt] at hh; simpa [U] using hh
  have l0 : L 0 = 1 := by
    have hh := tail_sum hlt.le 0; rw [upper_zero hk,mass_zero_left hk] at hh; simpa [L] using hh
  obtain ⟨u,uc,umem,ue,uz,ui⟩ := inverse_unit monoU (upper_cont n k) u0 u1
  have monoQ : StrictMonoOn (fun x => 1-L x) (Icc 0 1) :=
    fun _ hx _ hy hxy => sub_lt_sub_left (antiL hx hy hxy) _
  have q0 : 1 - L 0 = 0 := by rw [l0]; ring
  have q1 : 1 - L 1 = 1 := by rw [l1]; ring
  obtain ⟨w,wc,wmem,we,_,wi⟩ := inverse_unit monoQ (continuous_const.sub (lower_cont n k)) q0 q1
  let v (t : ℝ) := w (1-t)
  have vc : Continuous v := wc.comp (continuous_const.sub continuous_id)
  have vmem (t : ℝ) : v t ∈ Set.Icc 0 1 := wmem _
  have ve (t : ℝ) (ht : t ∈ Set.Icc 0 1) : L (v t) = t := by
    have h := we (1-t) (show 1-t ∈ Set.Icc 0 1 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)
    change 1 - L (v t) = 1-t at h
    linarith
  have vi (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : v t ∈ Set.Ioo 0 1 :=
    wi _ ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have vz : v 0 = 1 := antiL.injOn (vmem 0) (by simp) (by rw [ve 0 (by simp),l1])
  have sep (t : ℝ) (ht : t ∈ Set.Ioo 0 (1/2)) : u t < v t := by
    have hin : t ∈ Set.Ioo 0 1 := ⟨ht.1,by linarith [ht.2]⟩
    have hclosed : t ∈ Set.Icc 0 1 := ⟨hin.1.le,hin.2.le⟩
    by_contra! h
    have h' := monoU.monotoneOn (vmem t) (umem t) h
    have h'' := tail_sum hlt.le (v t)
    change L (v t) + U (v t) = 1 + M (v t) at h''
    rw [ve t hclosed] at h''
    rw [ue t hclosed] at h'
    have hp : 0 < M (v t) := mass_pos_int hlt.le (vi t hin)
    linarith [ht.2]
  let f (t : ℝ) := M (u t)-M (v t)
  have fc : Continuous f := ((mass_cont n k).comp uc).sub ((mass_cont n k).comp vc)
  have fz : f 0 = 0 := by dsimp [f,M]; rw [uz,vz,mass_zero_left hk,mass_zero_right hlt]; ring
  have deriv_pos (t : ℝ) (ht : t ∈ Set.Ioc 0 δ) (hn : f t < 0) :
      ∃ d, 0 < d ∧ HasDerivAt f d t := by
    have ht₀ : t ∈ Set.Ioo 0 (1/2) := ⟨ht.1,ht.2.trans_lt hhalf⟩
    have hin : t ∈ Set.Ioo 0 1 := ⟨ht.1,by linarith [ht₀.2]⟩
    have hu := ui t hin
    have hv := vi t hin
    have hMu : 0 < M (u t) := mass_pos_int hlt.le hu
    have hMv : 0 < M (v t) := mass_pos_int hlt.le hv
    have eu : ∀ᶠ z in 𝓝 t, U (u z) = z := by
      filter_upwards [Ioo_mem_nhds hin.1 hin.2] with z hz
      exact ue z ⟨hz.1.le,hz.2.le⟩
    have ev : ∀ᶠ z in 𝓝 t, L (v z) = z := by
      filter_upwards [Ioo_mem_nhds hin.1 hin.2] with z hz
      exact ve z ⟨hz.1.le,hz.2.le⟩
    have du := (upper_d hlt.le hu).of_local_left_inverse uc.continuousAt
      (ne_of_gt (div_pos (mul_pos ha hMu) hu.1)) eu
    have dv := (lower_d hlt.le hv).of_local_left_inverse vc.continuousAt
      (ne_of_lt (neg_neg_of_pos (div_pos (mul_pos hb hMv) (sub_pos.mpr hv.2)))) ev
    have dh := ((mass_d (n:=n) (k:=k) hu).comp t du).sub ((mass_d (n:=n) (k:=k) hv).comp t dv)
    let a : ℝ := k
    let b : ℝ := (n-k:ℕ)
    let d := 1 - b*(u t)/(a*(1-u t)) + a*(1-v t)/(b*v t) - 1
    have hu' := sub_pos.mpr hu.2
    have hv' := sub_pos.mpr hv.2
    have hcomp : M (u t) < M (v t) := sub_neg.mp hn
    have ho := odds_bound hu hv (sep t ht₀) hcomp
    refine ⟨d, ?_, ?_⟩
    · have hdiv : b*u t/(a*(1-u t)) < a*(1-v t)/(b*v t) := by
        apply (div_lt_div_iff₀ (mul_pos ha hu') (mul_pos hb hv.1)).2
        change b^2 * u t * v t < a^2*(1-u t)*(1-v t) at ho
        nlinarith only [ho]
      dsimp [d]; linarith
    · apply dh.congr_deriv
      change (M (u t) * (a/u t-b/(1-u t)))*(a*M (u t)/u t)⁻¹ -
        (M (v t) * (a/v t-b/(1-v t)))*(-(b*M (v t)/(1-v t)))⁻¹ = d
      dsimp only [d]
      field_simp [ha.ne',hb.ne',hu.1.ne',hv.1.ne',hu'.ne',hv'.ne',hMu.ne',hMv.ne',
        (show a ≠ 0 from ha.ne'),(show b ≠ 0 from hb.ne')]
      ring
  have hmass := positive_barrier hδ fc fz deriv_pos
  have hdin : δ ∈ Set.Ioo 0 1 := ⟨hδ,by linarith⟩
  have hdI : δ ∈ Set.Icc 0 1 := ⟨hδ.le,hdin.2.le⟩
  have huS : u δ = pSmall := monoU.injOn (umem _) hS ((ue _ hdI).trans hU.symm)
  have hvB : v δ = pBig := antiL.injOn (vmem _) hB ((ve _ hdI).trans hL.symm)
  change 0 ≤ mass n k (u δ) - mass n k (v δ) at hmass
  rw [huS,hvB] at hmass
  have hmass' := sub_nonneg.mp hmass
  have hs := ui δ hdin; rw [huS] at hs
  have hb' := vi δ hdin; rw [hvB] at hb'
  have hsep := sep δ ⟨hδ,hhalf⟩; rw [huS,hvB] at hsep
  refine ⟨?_,hmass'⟩
  have pred (p : ℝ) (hp : p ∈ Set.Ioo 0 1) : ((n-(k-1):ℕ):ℝ) * mass n (k-1) p =
      (k:ℝ) * mass n k p * ((1-p)/p) := by
    have h := adj_mass (n:=n) (k:=k-1) (by omega) hp
    rw [show k-1+1=k by omega] at h
    field_simp [hp.1.ne',(sub_pos.mpr hp.2).ne'] at h ⊢
    linarith
  have hpcoef : (0:ℝ)<(n-(k-1):ℕ) := by exact_mod_cast (show 0<n-(k-1) by omega)
  apply le_of_mul_le_mul_left _ hpcoef
  rw [pred _ hb',pred _ hs]
  apply mul_le_mul (mul_le_mul_of_nonneg_left hmass' ha.le) _ (div_nonneg (sub_pos.mpr hb'.2).le hb'.1.le)
    (mul_pos ha (mass_pos_int hlt.le hs)).le
  apply (div_le_div_iff₀ hb'.1 hs.1).2
  nlinarith only [hsep.le]

theorem below_half {n k : ℕ} (hk : 0 < k) (hkn : 2*k ≤ n)
    {δ pBig pSmall : ℝ} (hδ : 0 < δ) (hhalf : δ < 1/2)
    (hB : pBig ∈ Set.Icc 0 1) (hS : pSmall ∈ Set.Icc 0 1)
    (hL : lowerTail n k pBig = δ) (hU : upperTail n k pSmall = δ) :
    mass n (k-1) pBig ≤ mass n (k-1) pSmall ∧ mass n k pBig ≤ mass n k pSmall :=
  compare_matched hk hkn (matched_odds hkn hk) hδ hhalf hB hS hL hU

end MatchedBinomial

theorem OMA.solution : type_of% @OMA.S_mo_342070.main := by
  intro n k hk hkn δ hδ hthird pBig pSmall hB hS hL hU
  exact MatchedBinomial.below_half hk hkn hδ (by linarith) hB hS hL hU
