import OMAReductions.R_Erdos437_erdos_437_variants_tao_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-! Count smooth integers from above using Rankin's Euler product, and from below
by iterating a weighted count of prime divisors. Only estimates for sums and
products indexed by primes remain. -/

namespace OMA.R_Erdos437_erdos_437_variants_tao_R1_H3_R1

open Filter Real Finset
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

theorem main : H1 → H2 → OMA.R_Erdos437_erdos_437_variants_tao_R1.H3 := by
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

end OMA.R_Erdos437_erdos_437_variants_tao_R1_H3_R1
