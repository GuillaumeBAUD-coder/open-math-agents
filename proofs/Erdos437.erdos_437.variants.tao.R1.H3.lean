import OMAReductions.R_Erdos437_erdos_437_variants_tao_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-! Count smooth integers from above using Rankin's Euler product, and from below
by iterating a weighted count of prime divisors. Chebyshev's bounds control the weighted prime sum on geometric blocks.
Convexity of the exponential controls the truncated Euler product. -/

namespace OMA.Smooth437

open Filter Real Finset Chebyshev
open scoped Topology

-- Rankin's finite-cutoff inequality, also valid when s is below one.
private theorem rankin (x y : ℕ) (s : ℝ) (hs : 0 < s) :
    ((x.smoothNumbersUpTo y).card : ℝ) ≤ (x:ℝ)^s *
      ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-s))⁻¹ := by
  classical
  let f : ℕ →* ℝ := {
    toFun := fun n => (n:ℝ)^(-s)
    map_one' := by simp
    map_mul' := fun a b => by push_cast; exact Real.mul_rpow (by positivity) (by positivity) }
  have hf {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change |(p:ℝ)^(-s)| < 1
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hs)
  obtain ⟨_,series⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric (f:=f) hf y
  let W := x.smoothNumbersUpTo y
  let emb : W ↪ y.smoothNumbers :=
    ⟨fun n => ⟨n.val,(Nat.mem_smoothNumbersUpTo.mp n.property).2⟩,fun a b e => Subtype.ext (congrArg (fun v : y.smoothNumbers => v.val) e)⟩
  let V := (univ : Finset W).map emb
  have bound := sum_le_hasSum V (fun n _ => Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (n:ℕ)) (-s)) series
  have one (n : W) : 1 ≤ (x:ℝ)^s * f n.val := by
    obtain ⟨hn,hm⟩ := Nat.mem_smoothNumbersUpTo.mp n.property
    have pos : (0:ℝ) < n.val := by exact_mod_cast (Nat.pos_of_ne_zero hm.1)
    have inc := Real.rpow_le_rpow pos.le (Nat.cast_le.mpr hn : (n.val:ℝ) ≤ x) hs.le
    change 1 ≤ _ * (n.val:ℝ)^(-s)
    rw [Real.rpow_neg pos.le, ←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos pos _),one_mul]
    exact inc
  change (W.card:ℝ) ≤ _
  calc
    _ = ∑ _ : W, (1:ℝ) := by simp
    _ ≤ ∑ n : W, (x:ℝ)^s * f n.val := sum_le_sum fun n _ => one n
    _ = (x:ℝ)^s * ∑ n ∈ V, f (n:ℕ) := by rw [←mul_sum]; congr 1; rw [sum_map]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (Real.rpow_nonneg (by positivity) _)

-- Count a smooth integer once for each chosen prime divisor, weighted by log p.
private theorem divisor_recurrence (z y : ℕ) (P : Finset ℕ) (hP : P ⊆ y.primesBelow) :
    (∑ p ∈ P, log (p:ℝ) * ((z/p).smoothNumbersUpTo y).card) ≤
       log (z:ℝ) * (z.smoothNumbersUpTo y).card := by
  classical
  let W := z.smoothNumbersUpTo y
  have count (p : ℕ) (hp : p ∈ P) :
      ((z/p).smoothNumbersUpTo y).card ≤ (W.filter fun n => p ∣ n).card := by
    obtain ⟨py, prime⟩ := Nat.mem_primesBelow.mp (hP hp)
    apply card_le_card_of_injOn (fun m => p*m)
    · intro m hm
      obtain ⟨hz,sm⟩ := Nat.mem_smoothNumbersUpTo.mp hm
      apply mem_filter.mpr
      refine ⟨Nat.mem_smoothNumbersUpTo.mpr ⟨?_,?_⟩, dvd_mul_right _ _⟩
      · change p*m ≤ z; rw [mul_comm]; exact (Nat.le_div_iff_mul_le prime.pos).mp hz
      · exact Nat.mul_mem_smoothNumbers (Nat.mem_smoothNumbers_of_lt prime.pos py) sm
    · intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left prime.pos h
  have inner (n : ℕ) (hn : n ∈ W) : ∑ p ∈ P, (if p ∣ n then log (p:ℝ) else 0) ≤ log (z:ℝ) := by
    obtain ⟨nz,sm⟩ := Nat.mem_smoothNumbersUpTo.mp hn
    have pos := Nat.pos_of_ne_zero sm.1
    rw [←sum_filter]
    calc
      _ = ∑ p ∈ P.filter (fun p => p ∣ n), ArithmeticFunction.vonMangoldt p := by
        apply sum_congr rfl; intro p hp
        rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.mem_primesBelow.mp (hP (mem_filter.mp hp).1)).2]
      _ ≤ ∑ p ∈ n.divisors, ArithmeticFunction.vonMangoldt p :=
        sum_le_sum_of_subset_of_nonneg (fun p hp => Nat.mem_divisors.mpr ⟨(mem_filter.mp hp).2,pos.ne'⟩)
          (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = log n := ArithmeticFunction.vonMangoldt_sum
      _ ≤ _ := Real.log_le_log (by exact_mod_cast pos) (by exact_mod_cast nz)
  calc
    _ ≤ ∑ p ∈ P, log (p:ℝ) * ((W.filter fun n => p ∣ n).card : ℝ) := by
      apply sum_le_sum; intro p hp
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (count p hp)) (Real.log_natCast_nonneg p)
    _ = ∑ p ∈ P, ∑ n ∈ W, (if p ∣ n then log (p:ℝ) else 0) := by
      apply sum_congr rfl; intro p _
      rw [←sum_filter]; simp [mul_comm]
    _ = ∑ n ∈ W, ∑ p ∈ P, (if p ∣ n then log (p:ℝ) else 0) := sum_comm
    _ ≤ ∑ _ ∈ W, log (z:ℝ) := sum_le_sum inner
    _ = _ := by simp [W,mul_comm]

private lemma small_all_smooth {z y : ℕ} (hz : z < y) :
    (z.smoothNumbersUpTo y).card = z := by
  have eq : z.smoothNumbersUpTo y = Finset.Icc 1 z := by
    ext n
    rw [Nat.mem_smoothNumbersUpTo,Finset.mem_Icc]
    constructor
    · rintro ⟨le,sm⟩; exact ⟨Nat.pos_of_ne_zero sm.1,le⟩
    · rintro ⟨pos,le⟩; exact ⟨le,Nat.mem_smoothNumbers_of_lt pos (le.trans_lt hz)⟩
  simp [eq]

-- Iterate the prime-divisor count. The factor two accounts for integer division.
private theorem lower_iterate (x y : ℕ) (hx : 2 ≤ x) (P : Finset ℕ) (hP : P ⊆ y.primesBelow)
    (b q : ℝ) (hb : 0 < b) (hq : 0 ≤ q) (q1 : q ≤ 1)
    (large : ∀ p ∈ P, b ≤ (p:ℝ))
    (mass : 2*q*log x ≤ ∑ p ∈ P, log (p:ℝ)/p) (d : ℕ) :
    ∀ z ≤ x, (z:ℝ) < b^d → (z:ℝ)*q^d ≤ (z.smoothNumbersUpTo y).card := by
  have lx : 0 < log (x:ℝ) := log_pos (by exact_mod_cast (show 1 < x by omega))
  induction d with
  | zero =>
    intro z _ hbnd
    simp only [pow_zero,Nat.cast_lt_one] at hbnd
    simp [hbnd]
  | succ d ih =>
    intro z zx zb
    by_cases zy : z < y
    · rw [small_all_smooth zy]
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq q1 (n:=d+1)) (Nat.cast_nonneg (α:=ℝ) z)
    have term (p : ℕ) (hp : p ∈ P) :
        (log (p:ℝ)/p) * ((z:ℝ)*q^d/2) ≤ log (p:ℝ)*((z/p).smoothNumbersUpTo y).card := by
      have py := (Nat.mem_primesBelow.mp (hP hp)).1
      have prime := (Nat.mem_primesBelow.mp (hP hp)).2
      have pp : (0:ℝ)<p := by exact_mod_cast prime.pos
      have zn : 1 ≤ z/p := (Nat.le_div_iff_mul_le prime.pos).mpr (by omega)
      have divLo : (z:ℝ) ≤ 2*((z/p:ℕ):ℝ)*p := by
        have rem := Nat.mod_lt z prime.pos
        have modEq := Nat.mod_add_div z p
        have hmul : p ≤ p*(z/p) := by simpa using Nat.mul_le_mul_left p zn
        exact_mod_cast (show z ≤ 2*(z/p)*p by nlinarith only [rem,modEq,hmul])
      have divHi : ((z/p:ℕ):ℝ)*p ≤ (z:ℝ) := by exact_mod_cast Nat.div_mul_le_self z p
      have smaller : ((z/p:ℕ):ℝ) < b^d := by
        apply (mul_lt_mul_iff_of_pos_right hb).mp
        calc
          _ ≤ ((z/p:ℕ):ℝ)*p := mul_le_mul_of_nonneg_left (large p hp) (by positivity)
          _ ≤ _ := divHi
          _ < _ := by simpa [pow_succ] using zb
      have step := ih (z/p) ((Nat.div_le_self z p).trans zx) smaller
      have floorBound : (z:ℝ)/(2*p) ≤ ((z/p:ℕ):ℝ) :=
        (div_le_iff₀ (by positivity)).mpr (by linarith only [divLo])
      calc
        _ = log (p:ℝ)*(((z:ℝ)/(2*p))*q^d) := by ring
        _ ≤ log (p:ℝ)*(((z/p:ℕ):ℝ)*q^d) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left step (log_natCast_nonneg _)
    have sum := sum_le_sum term
    rw [←sum_mul] at sum
    have scale := mul_le_mul_of_nonneg_right mass (show 0 ≤ (z:ℝ)*q^d/2 by positivity)
    have divisors := divisor_recurrence z y P hP
    have logle : log (z:ℝ) ≤ log x := by
      rcases Nat.eq_zero_or_pos z with h|h
      · simp [h,lx.le]
      · exact log_le_log (by exact_mod_cast h) (by exact_mod_cast zx)
    have endBound := mul_le_mul_of_nonneg_right logle (show 0 ≤ ((z.smoothNumbersUpTo y).card:ℝ) by positivity)
    apply (mul_le_mul_iff_of_pos_left lx).mp
    rw [pow_succ]
    nlinarith only [scale,sum,divisors,endBound]

private lemma smooth_scale :
    Tendsto (fun x : ℕ =>
      let t := sqrt (log (x:ℝ) * log (log (x:ℝ)))
      let u := log (x:ℝ) / ((sqrt 2)⁻¹*t)
      u*log u/t) atTop (𝓝 (sqrt 2)⁻¹) := by
  let s (x : ℕ) := log (log (x:ℝ))
  have grows : Tendsto s atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have low : Tendsto (fun x => log (s x)/s x) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp grows
  have constant : Tendsto (fun x => log 2 / s x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop grows
  have lim : Tendsto (fun x => (sqrt 2)⁻¹ * (1 + (log 2 / s x - log (s x)/s x))) atTop (𝓝 (sqrt 2)⁻¹) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.add (constant.sub low)) :
      Tendsto _ atTop (𝓝 ((sqrt 2)⁻¹ * (1 + (0-0)))))
  apply lim.congr'
  filter_upwards [grows.eventually_gt_atTop 0,
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop 0] with x hs hx
  let a := log (x:ℝ)
  let t := sqrt (a*s x)
  let u := a/((sqrt 2)⁻¹*t)
  change (sqrt 2)⁻¹ * (1 + (log 2 / s x - log (s x) / s x)) = u*log u/t
  have ha : 0<a := hx
  have ht : 0<t := Real.sqrt_pos.2 (mul_pos ha hs)
  have h₂ : 0<sqrt 2 := by positivity
  have tsq : t^2=a*s x := sq_sqrt (mul_nonneg ha.le hs.le)
  have ts : u/t = sqrt 2 / s x := by
    dsimp only [u]
    field_simp [ne_of_gt ha,ne_of_gt hs,ne_of_gt ht, ne_of_gt h₂]
    nlinarith only [tsq]
  have lu : log u = (log 2+s x-log (s x))/2 := by
    dsimp only [u,t]
    rw [log_div ha.ne' (mul_ne_zero (inv_ne_zero h₂.ne') ht.ne'),
      log_mul (inv_ne_zero h₂.ne') ht.ne',log_inv,
      log_sqrt (by norm_num),log_sqrt (mul_nonneg ha.le hs.le),log_mul ha.ne' hs.ne']
    change s x - (-(log 2 / 2) + (s x + log (s x))/2) = _
    ring
  rw [show u*log u/t=(u/t)*log u by ring,ts,lu]
  field_simp [ne_of_gt hs,ne_of_gt h₂]
  rw [sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

-- Recover growth of u from the positive limiting cost u log(u) / t.
private lemma parameter_grows {u t : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hu : ∀ᶠ x in atTop, 0 < u x) (ht : Tendsto t atTop atTop)
    (scale : Tendsto (fun x => u x*log (u x)/t x) atTop (𝓝 c)) :
    Tendsto u atTop atTop := by
  have prod : Tendsto (fun x => u x*log (u x)) atTop atTop := by
    apply (scale.pos_mul_atTop hc ht).congr'
    filter_upwards [ht.eventually_gt_atTop 0] with x h
    exact div_mul_cancel₀ _ h.ne'
  apply tendsto_atTop.2
  intro M
  let B := max 1 M
  have hB : 1 ≤ B := le_max_left _ _
  filter_upwards [hu,prod.eventually_gt_atTop (B*log B)] with x hx large
  by_contra! small
  have le : u x ≤ B := small.le.trans (le_max_right _ _)
  have logle := log_le_log hx le
  have hlog := log_nonneg hB
  exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left logle hx.le).trans
    (mul_le_mul_of_nonneg_right le hlog))) large

private lemma iteration_cost {u t : ℕ → ℝ} {c a K : ℝ} (ha : 0<a) (hK : 0<K)
    (grow : Tendsto u atTop atTop)
    (scale : Tendsto (fun x => u x*log (u x)/t x) atTop (𝓝 c)) :
    Tendsto (fun x => (u x/a+1)*log (K*u x)/t x) atTop (𝓝 (c/a)) := by
  have invu : Tendsto (fun x => (1:ℝ)/u x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop grow
  have invlog : Tendsto (fun x => log K/log (u x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp grow)
  have lim := (scale.mul ((tendsto_const_nhds (x:=(1:ℝ)/a)).add invu)).mul
    ((tendsto_const_nhds (x:=(1:ℝ))).add invlog)
  simp only [add_zero,mul_one,mul_div_assoc, mul_one_div] at lim
  apply lim.congr'
  filter_upwards [grow.eventually_gt_atTop 1] with x hx
  have pos : 0 < u x := by linarith
  have lp := log_pos hx
  rw [log_mul hK.ne' pos.ne']
  by_cases h : t x = 0
  · simp [h]
  field_simp [h,ha.ne',pos.ne',lp.ne']
  ring

-- Convert a window estimate to a lower bound after rounding the number of iterations.
private lemma from_window (x : ℕ) (hx : 2 ≤ x) (a T D u E : ℝ)
    (ha : 0<a) (hT : 0<T) (hD : 0<D) (hu : 0<u) (relation : u*T=log (x:ℝ))
    (big : 1 ≤ (2/D)*u)
    (mass : D*T ≤ ∑ p ∈ (⌈exp T⌉₊.primesBelow.filter fun (p : ℕ) => exp (a*T) ≤ (p:ℝ)), log (p:ℝ)/p)
    (cost : (u/a+1)*log ((2/D)*u) ≤ E) :
    (x:ℝ)*exp (-E) ≤ (x.smoothNumbersUpTo ⌈exp T⌉₊).card := by
  let P := ⌈exp T⌉₊.primesBelow.filter fun (p : ℕ) => exp (a*T) ≤ (p:ℝ)
  let v := (2/D)*u
  let d := ⌊u/a⌋₊+1
  have hv : 0<v := by dsimp [v]; positivity
  have dx : u/a < (d:ℝ) := by simpa [d] using Nat.lt_floor_add_one (u/a)
  have dx' : (d:ℝ) ≤ u/a+1 := by
    dsimp [d]; push_cast; linarith only [Nat.floor_le (show 0≤u/a by positivity)]
  have hxp : (0:ℝ)<x := by exact_mod_cast (show 0<x by omega)
  have db : (x:ℝ) < exp (a*T)^d := by
    rw [←Real.exp_nat_mul,←exp_log hxp]
    apply exp_lt_exp.mpr
    rw [←relation]
    have ineq := (div_lt_iff₀ ha).mp dx
    nlinarith only [mul_lt_mul_of_pos_right ineq hT]
  have m : 2*v⁻¹*log (x:ℝ) ≤ ∑ p ∈ P, log (p:ℝ)/p := by
    apply le_trans _ mass
    apply le_of_eq
    rw [←relation]
    dsimp [v]
    field_simp
  have lower := lower_iterate x ⌈exp T⌉₊ hx P (filter_subset _ _) (exp (a*T)) v⁻¹
    (exp_pos _) (inv_nonneg.mpr hv.le) ((inv_le_one₀ hv).mpr big)
    (fun p hp => (mem_filter.mp hp).2) m d x le_rfl db
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hxp.le) lower
  rw [←exp_log (inv_pos.mpr hv), ←Real.exp_nat_mul,log_inv]
  apply exp_le_exp.mpr
  have dcost := mul_le_mul_of_nonneg_right dx' (log_nonneg big)
  dsimp only [v]
  linarith

-- Apply Rankin's bound at the tilted exponent and account for the prime product.
private lemma from_product (x : ℕ) (hx : 0 < (x:ℝ)) (T u ε t c δ : ℝ)
    (hT : 0<T) (relation : u*T=log (x:ℝ)) (hs : 0<1-log u/T)
    (mass : ∏ p ∈ (⌈exp T⌉₊).primesBelow, (1-(p:ℝ)^(-(1-log u/T)))⁻¹ ≤ exp (ε*t))
    (cost : (c-δ)*t+ε*t ≤ u*log u) :
    ((x.smoothNumbersUpTo ⌈exp T⌉₊).card:ℝ) ≤ (x:ℝ)*exp (-(c-δ)*t) := by
  apply (rankin x _ _ hs).trans
  apply (mul_le_mul_of_nonneg_left mass (rpow_nonneg hx.le _)).trans
  rw [rpow_def_of_pos hx,←exp_add,←exp_log hx,←exp_add]
  rw [log_exp]
  apply exp_le_exp.mpr
  rw [←relation]
  field_simp [hT.ne']
  linarith only [cost]


private noncomputable def primeSum (v : ℝ) : ℝ := ∑ p ∈ ⌊v⌋₊.primesLE, log (p:ℝ)/p

-- Partial summation on a single interval, using only positivity of the weights.
private lemma prime_increment {A B : ℝ} (a : 0≤A) (ab : A≤B) :
    theta B-theta A ≤ B*(primeSum B-primeSum A) := by
  let P := ⌊A⌋₊.primesLE
  let Q := ⌊B⌋₊.primesLE
  have sub : P ⊆ Q := by
    intro p hp
    obtain ⟨l,h⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨l.trans (Nat.floor_le_floor ab),h⟩
  have split (f : ℕ→ℝ) : (∑ p ∈ Q, f p)-(∑ p ∈ P, f p)=∑ p ∈ Q \ P, f p := by
    linarith only [sum_sdiff sub (f:=f)]
  simp only [theta_eq_sum_primesLE,primeSum]
  change (∑ p ∈ Q, log (p:ℝ))-(∑ p ∈ P, log (p:ℝ)) ≤ B*((∑ p ∈ Q, log (p:ℝ)/p)-(∑ p ∈ P, log (p:ℝ)/p))
  rw [split,split,mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨l,h⟩ := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
  have pb : (p:ℝ) ≤ B := (Nat.le_floor_iff (a.trans ab)).mp l
  have pp : (0:ℝ) < p := by exact_mod_cast h.pos
  calc
    log (p:ℝ) = (p:ℝ)*(log (p:ℝ)/p) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right pb (div_nonneg (log_natCast_nonneg _) pp.le)

private lemma theta_lower_eventually :
    ∀ᶠ v : ℝ in atTop, (log 2/2)*v ≤ theta v := by
  have l2 := log_pos (show (1:ℝ)<2 by norm_num)
  have lim : Tendsto (fun v : ℝ => log v / sqrt v) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop (8:ℝ),lim.eventually (gt_mem_nhds
    (show 0<log 2/16 by positivity))] with v big small
  have vpos : 0<v := by linarith
  have rpos := sqrt_pos.mpr vpos
  have logB := (div_lt_iff₀ rpos).mp small
  have rsq := sq_sqrt vpos.le
  have rle : sqrt v ≤ v := by nlinarith [sq_nonneg (sqrt v-1)]
  have dbl : log (v+2) ≤ log 2 + log v := by
    rw [←log_mul (by norm_num : (2:ℝ)≠0) vpos.ne']
    exact log_le_log (by positivity) (by linarith)
  have upper := theta_ge' (show 1≤v by linarith)
  nlinarith only [upper,dbl,logB,rsq,mul_le_mul_of_nonneg_left rle l2.le,
    mul_lt_mul_of_pos_left logB rpos,mul_le_mul_of_nonneg_left big l2.le,
    congrArg (fun z : ℝ => log 2*z) rsq]

-- Each geometric block contributes a fixed positive amount of prime weight.
private lemma block_sum {V₀ : ℝ} (vpos : 0<V₀)
    (lower : ∀ v ≥ V₀, log 2/2*v ≤ theta v) (n : ℕ) :
    (n:ℝ)*(log 2/4) ≤ primeSum (V₀*(16:ℝ)^n)-primeSum V₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    let A := V₀*(16:ℝ)^n
    have ap : 0<A := by dsimp [A]; positivity
    have va : V₀ ≤ A := by
      dsimp only [A]
      exact le_mul_of_one_le_right vpos.le (one_le_pow₀ (by norm_num))
    have av : A ≤ A*16 := by linarith
    have weight := prime_increment ap.le av
    have low := lower (A*16) (va.trans av)
    have high := theta_le_log4_mul_x ap.le
    have four : log 4=2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num
    rw [four] at high
    have inc : log 2/4 ≤ primeSum (A*16)-primeSum A := by
      apply (mul_le_mul_iff_of_pos_left (show 0<A*16 by positivity)).mp
      have l2 := log_pos (show (1:ℝ)<2 by norm_num)
      nlinarith only [weight,low,high,mul_pos ap l2]
    rw [pow_succ,←mul_assoc,Nat.cast_succ]
    change ((n:ℝ)+1)*(log 2/4) ≤ primeSum (A*16)-primeSum V₀
    change (n:ℝ)*(log 2/4) ≤ primeSum A-primeSum V₀ at ih
    linarith only [ih,inc]

private lemma window_contains {A B Y : ℝ} (ha : 0 ≤ A) (ab : A ≤ B) (bylt : B < Y) :
    primeSum B-primeSum A ≤
      ∑ p ∈ ⌈Y⌉₊.primesBelow.filter (fun (p:ℕ) => A ≤ (p:ℝ)), log (p:ℝ)/p := by
  have sub : ⌊A⌋₊.primesLE ⊆ ⌊B⌋₊.primesLE := by
    intro p hp
    obtain ⟨l,h⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨l.trans (Nat.floor_le_floor ab),h⟩
  unfold primeSum
  rw [←sum_sdiff sub,add_sub_cancel_right]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hB,hA⟩ := mem_sdiff.mp hp
    obtain ⟨l,pr⟩ := Nat.mem_primesLE.mp hB
    have lp := (Nat.le_floor_iff (ha.trans ab)).mp l
    refine mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨?_,pr⟩,?_⟩
    · exact_mod_cast (lp.trans_lt bylt).trans_le (Nat.le_ceil _)
    · by_contra! contra
      exact hA (Nat.mem_primesLE.mpr ⟨Nat.le_floor contra.le,pr⟩)
  · intro p _ _
    exact div_nonneg (log_natCast_nonneg p) (by positivity)

private theorem prime_window :
  ∀ a : ℝ, 0 < a → a < 1 → ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop,
    D*T ≤ ∑ p ∈ (⌈exp T⌉₊.primesBelow.filter fun (p : ℕ) => exp (a*T) ≤ (p:ℝ)), log (p:ℝ)/p := by
  intro a ha a1
  let r := (1-a)/(2*log 16)
  have log16 := log_pos (show (1:ℝ)<16 by norm_num)
  have log2 := log_pos (show (1:ℝ)<2 by norm_num)
  have hr : 0<r := div_pos (sub_pos.mpr a1) (by positivity)
  refine ⟨r*(log 2/8),by positivity,?_⟩
  obtain ⟨X,hX⟩ := eventually_atTop.1 theta_lower_eventually
  have grow : Tendsto (fun T : ℝ => exp (a*T)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
  filter_upwards [grow.eventually_ge_atTop X,(tendsto_id.const_mul_atTop hr).eventually_ge_atTop 2,
    eventually_gt_atTop (0:ℝ)] with T large rounds ht
  let A := exp (a*T)
  let n := ⌊r*T⌋₊
  let B := A*16^n
  have av : A≤B := le_mul_of_one_le_right (exp_pos _).le (one_le_pow₀ (by norm_num))
  have nle : (n:ℝ)≤r*T := Nat.floor_le (by positivity)
  have nlo : r*T<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have endpt : B < exp T := by
    have eq : B = exp (a*T+(n:ℝ)*log 16) := by
      dsimp only [B,A]
      rw [exp_add,Real.exp_nat_mul,exp_log (by norm_num : (0:ℝ)<16)]
    rw [eq,exp_lt_exp]
    have rel : r*log 16=(1-a)/2 := by dsimp only [r]; field_simp
    have bound := mul_le_mul_of_nonneg_right nle log16.le
    have adapt := congrArg (fun z : ℝ => z*T) rel
    nlinarith only [bound,adapt,mul_pos (sub_pos.mpr a1) ht]
  have lower := block_sum (exp_pos (a*T)) (fun v hv => hX v (large.trans hv)) n
  have cover := window_contains (exp_pos (a*T)).le av endpt
  apply le_trans _ (lower.trans cover)
  change 2 ≤ r*T at rounds
  have nbig : r*T/2 ≤ (n:ℝ) := by linarith only [nlo,rounds]
  nlinarith only [mul_le_mul_of_nonneg_right nbig log2.le]

-- Each prime contributes at least y/(2p) multiples up to y.
private lemma weighted_bound (y : ℕ) (hy : 0 < y) :
    (∑ p ∈ y.primesBelow, log (p:ℝ)/p) ≤ 2*log (y:ℝ) := by
  have hs : y.primesBelow ⊆ (y+1).primesBelow := by
    intro p hp
    obtain ⟨py,pr⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,pr⟩
  have recu := divisor_recurrence y (y+1) y.primesBelow hs
  rw [small_all_smooth (Nat.lt_succ_self y)] at recu
  have term (p : ℕ) (hp : p ∈ y.primesBelow) :
      (log (p:ℝ)/p)*((y:ℝ)/2) ≤ log (p:ℝ)*((y/p).smoothNumbersUpTo (y+1)).card := by
    obtain ⟨py,pr⟩ := Nat.mem_primesBelow.mp hp
    rw [small_all_smooth (Nat.lt_succ_of_le (Nat.div_le_self y p))]
    have pos : (0:ℝ) < p := by exact_mod_cast pr.pos
    have z : 1 ≤ y/p := (Nat.le_div_iff_mul_le pr.pos).mpr (by omega)
    have pl : p ≤ p*(y/p) := by simpa using Nat.mul_le_mul_left p z
    have nbound : y ≤ 2*(y/p)*p := by nlinarith only [Nat.mod_lt y pr.pos,Nat.mod_add_div y p,pl]
    have db : (y:ℝ)/(2*p) ≤ ((y/p:ℕ):ℝ) := (div_le_iff₀ (by positivity)).mpr
      (by exact_mod_cast (show y ≤ y/p*(2*p) by nlinarith only [nbound]))
    calc
      _ = log (p:ℝ)*((y:ℝ)/(2*p)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left db (log_natCast_nonneg _)
  have sum := sum_le_sum term
  rw [←sum_mul] at sum
  have big := sum.trans recu
  apply (mul_le_mul_iff_of_pos_right (show (0:ℝ)<y/2 by positivity)).mp
  linarith only [big]

-- As the prime cutoff tends to infinity, the unweighted reciprocal sum is o(log y).
private lemma reciprocal_bound (y B : ℕ) (hB : 1 < B) (hy : 0 < y) :
    (∑ p ∈ y.primesBelow, (1:ℝ)/p) ≤ B + (2*log (y:ℝ))/log (B:ℝ) := by
  let S := y.primesBelow.filter fun p => p < B
  have ss : S ⊆ y.primesBelow := filter_subset _ _
  have bpos : 0 < log (B:ℝ) := log_pos (by exact_mod_cast hB)
  have lo : ∑ p ∈ S, (1:ℝ)/p ≤ B := by
    have sb : S ⊆ range B := fun p hp => mem_range.mpr (mem_filter.mp hp).2
    calc
      _ ≤ ∑ _p ∈ S, (1:ℝ) := by
        apply sum_le_sum
        intro p hp
        have pr := (Nat.mem_primesBelow.mp (ss hp)).2
        exact (div_le_one (by exact_mod_cast pr.pos)).mpr (by exact_mod_cast pr.one_le)
      _ ≤ B := by simpa using (Nat.cast_le (α:=ℝ)).mpr (card_le_card sb)
  have hi : ∑ p ∈ y.primesBelow \ S, (1:ℝ)/p ≤ (2*log (y:ℝ))/log (B:ℝ) := by
    apply (le_div_iff₀ bpos).mpr
    rw [sum_mul]
    apply le_trans _ (weighted_bound y hy)
    have subset : y.primesBelow \ S ⊆ y.primesBelow := sdiff_subset
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (f:=fun (p:ℕ) => log (p:ℝ)/p) subset (fun p _ _ => div_nonneg (log_natCast_nonneg _) (by positivity)))
    apply sum_le_sum
    intro p hp
    obtain ⟨py,h⟩ := mem_sdiff.mp hp
    have le : B ≤ p := by by_contra! s; exact h (mem_filter.mpr ⟨py,s⟩)
    have lg := log_le_log (show 0 < (B:ℝ) by positivity) (by exact_mod_cast le : (B:ℝ) ≤ p)
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using mul_le_mul_of_nonneg_right lg (show 0 ≤ (p:ℝ)⁻¹ by positivity)
  linarith only [lo,hi,sum_sdiff ss (f:=fun (p:ℕ) => (1:ℝ)/p)]

private lemma tilted_weight {p : ℕ} (hp : p.Prime) {T u : ℝ}
    (hT : 0 < T) (hi : log (p:ℝ) ≤ T) (hu : 1 ≤ u) :
    (p:ℝ)^(-(1-log u/T)) ≤ (1:ℝ)/p + (u/T)*(log (p:ℝ)/p) := by
  let v := log (p:ℝ)/T
  have vp : 0 ≤ v := div_nonneg (log_natCast_nonneg _) hT.le
  have vl : v ≤ 1 := (div_le_one hT).mpr hi
  have pp : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have up : 0 < u := by linarith
  have cv := convexOn_exp.2 (show (0:ℝ) ∈ Set.univ from Set.mem_univ _)
    (show log u ∈ Set.univ from Set.mem_univ _) (sub_nonneg.mpr vl) vp (sub_add_cancel 1 v)
  simp only [smul_eq_mul,mul_zero,zero_add,exp_zero,mul_one,exp_log up] at cv
  rw [Real.rpow_def_of_pos pp]
  have form : log (p:ℝ) * -(1-log u/T) = v*log u-log (p:ℝ) := by dsimp only [v]; ring
  rw [form,exp_sub,exp_log pp]
  apply (div_le_iff₀ pp).mpr
  have eq : ((1:ℝ)/p+(u/T)*(log (p:ℝ)/p))*(p:ℝ) = 1+v*u := by
    dsimp only [v]; field_simp
  rw [eq]
  linarith only [cv,vp]

private lemma euler_factor_bound {p : ℕ} (hp : p.Prime) {σ : ℝ} (hs : 1/2 ≤ σ) :
    (1-(p:ℝ)^(-σ))⁻¹ ≤ exp (4*(p:ℝ)^(-σ)) := by
  let z := (p:ℝ)^(-σ)
  have pp : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have zp : 0 < z := rpow_pos_of_pos (by positivity) _
  have sqrt2 : (4:ℝ)/3 ≤ sqrt 2 := by
    nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
  have root : (4:ℝ)/3 ≤ (p:ℝ)^σ := calc
    _ ≤ sqrt 2 := sqrt2
    _ ≤ sqrt (p:ℝ) := sqrt_le_sqrt pp
    _ = (p:ℝ)^(1/2:ℝ) := sqrt_eq_rpow _
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by linarith) hs
  have cap : z ≤ 3/4 := by
    dsimp [z]
    rw [rpow_neg (by positivity)]
    exact (inv_le_comm₀ (by positivity) (by norm_num)).mpr (by norm_num; linarith only [root])
  have om : 0 < 1-z := by linarith
  change (1-z)⁻¹ ≤ exp (4*z)
  rw [←Real.log_le_iff_le_exp (inv_pos.mpr om)]
  apply (log_le_sub_one_of_pos (inv_pos.mpr om)).trans
  rw [sub_le_iff_le_add,inv_le_iff_one_le_mul₀ om]
  nlinarith only [mul_le_mul_of_nonneg_right cap zp.le]

private lemma product_estimate {u T : ℝ} (hu : 1 ≤ u) (hT : 0 < T)
    (time : log 2 ≤ T) (tilt : 1/2 ≤ 1-log u/T) {B : ℕ} (hB : 1 < B) :
    ∏ p ∈ (⌈exp T⌉₊).primesBelow, (1-(p:ℝ)^(-(1-log u/T)))⁻¹ ≤
      exp (4*B+16*T/log (B:ℝ)+16*u) := by
  let y := ⌈exp T⌉₊
  let σ := 1-log u/T
  let P := y.primesBelow
  have yp : 0 < y := Nat.ceil_pos.mpr (exp_pos _)
  have pp : 0 < (y:ℝ) := by exact_mod_cast yp
  have logy : log (y:ℝ) ≤ 2*T := calc
    _ ≤ log (2*exp T) := by
      apply log_le_log pp
      have lt := Nat.ceil_lt_add_one (exp_pos T).le
      have ep : 1 ≤ exp T := one_le_exp hT.le
      dsimp only [y]
      linarith only [lt,ep]
    _ ≤ _ := by rw [log_mul (by norm_num) (exp_pos _).ne',log_exp]; linarith
  have low (p : ℕ) (hp : p ∈ P) : log (p:ℝ) ≤ T := by
    have less := Nat.lt_ceil.mp (Nat.mem_primesBelow.mp hp).1
    exact (log_le_iff_le_exp (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos)).mpr less.le
  have bounds := sum_le_sum (fun (p:ℕ) (hp : p ∈ P) =>
    tilted_weight (Nat.mem_primesBelow.mp hp).2 hT (low p hp) hu)
  rw [sum_add_distrib,←mul_sum] at bounds
  have weighted := mul_le_mul_of_nonneg_left (weighted_bound y yp) (show 0≤u/T by positivity)
  have wc : (u/T)*(2*log (y:ℝ)) ≤ 4*u := by
    calc _ ≤ (u/T)*(2*(2*T)) := by gcongr
         _ = _ := by field_simp; ring
  have rc := reciprocal_bound y B hB yp
  have divb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left logy (show (0:ℝ)≤2 by norm_num))
    (log_natCast_nonneg B)
  change ∏ p ∈ P, (1-(p:ℝ)^(-σ))⁻¹ ≤ _
  calc
    _ ≤ ∏ p ∈ P, exp (4*(p:ℝ)^(-σ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt)
          (by dsimp [σ]; linarith only [tilt])).le
      · exact fun p hp => euler_factor_bound (Nat.mem_primesBelow.mp hp).2 tilt
    _ = exp (4*∑ p ∈ P, (p:ℝ)^(-σ)) := by rw [mul_sum,exp_sum]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      change 4*(∑ p ∈ P, (p:ℝ)^(-(1-log u/T))) ≤ _
      change (∑ p ∈ P, (1:ℝ)/p) ≤ _ at rc
      change (u/T)*(∑ p ∈ P, log (p:ℝ)/p) ≤ _ at weighted
      simp only [div_eq_mul_inv] at bounds weighted wc rc divb ⊢
      linarith only [bounds,weighted,wc,rc,divb]

private lemma prime_product_small :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
    let t := sqrt (log (x:ℝ)*log (log (x:ℝ)))
    let T := (sqrt 2)⁻¹*t
    let u := log (x:ℝ)/T
    let σ := 1-log u/T
    ∏ p ∈ (⌈exp T⌉₊).primesBelow, (1-(p:ℝ)^(-σ))⁻¹ ≤ exp (ε*t) := by
  intro ε hε
  let c := (sqrt 2)⁻¹
  let t (x:ℕ) := sqrt (log (x:ℝ)*log (log (x:ℝ)))
  let T (x:ℕ) := c*t x
  let u (x:ℕ) := log (x:ℝ)/T x
  have hc : 0 < c := by positivity
  have logs : Tendsto (fun x:ℕ => log (x:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tg : Tendsto t atTop atTop :=
    tendsto_sqrt_atTop.comp (logs.atTop_mul_atTop₀ (tendsto_log_atTop.comp logs))
  have Tg : Tendsto T atTop atTop := tg.const_mul_atTop hc
  have pos : ∀ᶠ x in atTop, 0 < u x := by
    filter_upwards [logs.eventually_gt_atTop 0,Tg.eventually_gt_atTop 0] with x l v
    exact div_pos l v
  have scale : Tendsto (fun x => u x*log (u x)/t x) atTop (𝓝 c) := smooth_scale
  have ug := parameter_grows hc pos tg scale
  have ur : Tendsto (fun x => u x/t x) atTop (𝓝 0) := by
    apply (scale.div_atTop (tendsto_log_atTop.comp ug)).congr'
    filter_upwards [ug.eventually_gt_atTop 1,tg.eventually_gt_atTop 0] with x hu ht
    simp only [Function.comp_apply]
    field_simp [(log_pos hu).ne',ht.ne']
  have sig : Tendsto (fun x => log (u x)/T x) atTop (𝓝 0) := by
    have lim := (scale.div_atTop ug).div_const c
    simp only [zero_div] at lim
    apply lim.congr'
    filter_upwards [pos,tg.eventually_gt_atTop 0] with x hu ht
    dsimp only [T]
    field_simp [hu.ne',ht.ne',hc.ne']
  obtain ⟨B,hB,big⟩ := ((eventually_gt_atTop (1:ℕ)).and (logs.eventually_gt_atTop (32*c/ε))).exists
  have lB := log_pos (by exact_mod_cast hB : (1:ℝ) < B)
  have coef : 16*c/log (B:ℝ) ≤ ε/2 := by
    apply (div_le_iff₀ lB).mpr
    have := (div_lt_iff₀ hε).mp big
    linarith
  have br : Tendsto (fun x => (4*(B:ℝ))/t x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tg
  have sub : Tendsto (fun x => 4*(B:ℝ)/t x+16*(u x/t x)) atTop (𝓝 0) := by
    simpa using br.add ((tendsto_const_nhds (x:=(16:ℝ))).mul ur)
  filter_upwards [ug.eventually_ge_atTop 1,Tg.eventually_ge_atTop (log 2),Tg.eventually_gt_atTop 0,
    tg.eventually_gt_atTop 0,sig.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    sub.eventually (gt_mem_nhds (half_pos hε))] with x hu hl hT ht hs hsub
  apply (product_estimate hu hT hl (by linarith only [hs]) hB).trans
  apply exp_le_exp.mpr
  have low := (div_le_iff₀ ht).mp (show (4*(B:ℝ)+16*u x)/t x ≤ ε/2 by
    rw [add_div,mul_div_assoc 16]; exact hsub.le)
  have high := mul_le_mul_of_nonneg_right coef ht.le
  change 4*(B:ℝ)+16*(c*t x)/log (B:ℝ)+16*u x ≤ ε*t x
  simp only [div_eq_mul_inv] at low high ⊢
  linarith only [low,high]

/-- The truncated prime Euler product at the Rankin exponent has subexponential size. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
    let t := sqrt (log (x:ℝ)*log (log (x:ℝ)))
    let T := (sqrt 2)⁻¹*t
    let u := log (x:ℝ)/T
    let σ := 1-log u/T
    ∏ p ∈ (⌈exp T⌉₊).primesBelow, (1-(p:ℝ)^(-σ))⁻¹ ≤ exp (ε*t)

/-- Every fixed logarithmic window carries a positive share of the weighted prime sum. -/
def H2 : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop,
    D*T ≤ ∑ p ∈ (⌈exp T⌉₊.primesBelow.filter fun (p : ℕ) => exp (a*T) ≤ (p:ℝ)), log (p:ℝ)/p

private theorem combine : H1 → H2 → OMA.R_Erdos437_erdos_437_variants_tao_R1.H3 := by
  intro h₁ h₂ δ hδ
  let t (x:ℕ) := sqrt (log (x:ℝ)*log (log (x:ℝ)))
  let c : ℝ := (sqrt 2)⁻¹
  let T (x:ℕ) := c*t x
  let u (x:ℕ) := log (x:ℝ)/T x
  have hc : 0<c := by positivity
  let a := c/(c+δ/2)
  have hden : 0<c+δ/2 := by positivity
  have ha : 0<a := div_pos hc hden
  have a1 : a<1 := (div_lt_one hden).mpr (by linarith)
  have ca : c/a=c+δ/2 := by dsimp only [a]; field_simp
  obtain ⟨D,hD,window⟩ := h₂ a ha a1
  have hK : 0<2/D := by positivity
  have logs : Tendsto (fun x:ℕ => log (x:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tg : Tendsto t atTop atTop :=
    tendsto_sqrt_atTop.comp (logs.atTop_mul_atTop₀ (tendsto_log_atTop.comp logs))
  have Tg : Tendsto T atTop atTop := tg.const_mul_atTop hc
  have pos : ∀ᶠ x in atTop, 0<u x := by
    filter_upwards [logs.eventually_gt_atTop 0,Tg.eventually_gt_atTop 0] with x h ht
    exact div_pos h ht
  have scale : Tendsto (fun x => u x*log (u x)/t x) atTop (𝓝 c) := smooth_scale
  have ug := parameter_grows hc pos tg scale
  have it := iteration_cost ha hK ug scale
  have sig : Tendsto (fun x => log (u x)/T x) atTop (𝓝 0) := by
    have lim := (scale.div_atTop ug).div_const c
    simp only [zero_div] at lim
    apply lim.congr'
    filter_upwards [pos,tg.eventually_gt_atTop 0] with x hu ht
    dsimp only [T]
    field_simp [hu.ne',ht.ne',hc.ne']
  have costLimit : c/a < c+δ := by rw [ca]; linarith
  have εpos : 0<δ/2 := half_pos hδ
  filter_upwards [Tg.eventually window, (ug.const_mul_atTop hK).eventually_ge_atTop 1,
    sig.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)), it.eventually (gt_mem_nhds costLimit),
    scale.eventually (lt_mem_nhds (show c-δ/2<c by linarith)), h₁ (δ/2) εpos,
    eventually_ge_atTop (2:ℕ),pos,tg.eventually_gt_atTop 0,Tg.eventually_gt_atTop 0]
    with x mass big hs iter sc prod hx hu ht hT
  have rel : u x*T x=log (x:ℝ) := div_mul_cancel₀ _ hT.ne'
  constructor
  · have bnd := from_window x hx a (T x) D (u x) ((c+δ)*t x) ha hT hD hu rel big mass
      ((div_le_iff₀ ht).mp iter.le)
    simpa only [neg_mul] using bnd
  · apply from_product x (by exact_mod_cast (show 0<x by omega)) (T x) (u x) (δ/2) (t x)
      c δ hT rel (by linarith only [hs]) prod
    have lower := (le_div_iff₀ ht).mp sc.le
    linarith only [lower]

end OMA.Smooth437

theorem OMA.solution : OMA.R_Erdos437_erdos_437_variants_tao_R1.H3 := by
  exact OMA.Smooth437.combine OMA.Smooth437.prime_product_small OMA.Smooth437.prime_window
