import FormalConjectures.ErdosProblems.«710»
import Mathlib

/-! # Weighted matching for distinct multiples

A common multiplier places all large inputs in a lower interval. The small inputs use prime multiples in a disjoint upper interval. Fractional Hall counting turns a prime-interval lower estimate and a weighted prime-divisor upper estimate into an actual matching. The equation exp(-r)=r balances the two estimates; cf. Erdős and Pomerance, Matching the natural numbers up to n with distinct multiples in another interval (1980), §3. -/

namespace OMA.R_Erdos710_erdos_710_variants_upper_bound_R1


open Finset Filter Real Topology
open scoped Classical

lemma weighted_matching {I J : Type*} [Fintype I] [DecidableEq J]
    (T : I → Finset J) (w : I → ℝ) (t : ℝ) (wt : 0<t) (non : ∀ i, 0≤w i)
    (row : ∀ i, t ≤ (T i).card*w i)
    (col : ∀ j, (∑ i : I, if j ∈ T i then w i else 0) ≤ t) :
    ∃ f : I → J, Function.Injective f ∧ ∀ i, f i ∈ T i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp
  intro S
  let U := S.biUnion T
  have byrow (i : I) (hi : i ∈ S) : (T i).card*w i = ∑ j ∈ U, if j ∈ T i then w i else 0 := by
    have inc : T i ⊆ U := fun j hj => mem_biUnion.mpr ⟨i,hi,hj⟩
    rw [← Finset.sum_filter,filter_mem_eq_inter,inter_eq_right.mpr inc]
    simp
  have bycol (j : J) : (∑ i ∈ S, if j ∈ T i then w i else 0) ≤ t := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ S) ?_) (col j)
    intro i _ _
    by_cases h : j ∈ T i <;> simp [h,non i]
  have estimate : (S.card:ℝ)*t ≤ U.card*t := calc
    _ = ∑ _i ∈ S,t := by simp
    _ ≤ ∑ i ∈ S, ((T i).card:ℝ)*w i := sum_le_sum (fun i _ => row i)
    _ = ∑ i ∈ S,∑ j ∈ U, if j ∈ T i then w i else 0 := sum_congr rfl byrow
    _ = ∑ j ∈ U,∑ i ∈ S, if j ∈ T i then w i else 0 := sum_comm
    _ ≤ ∑ _j ∈ U,t := sum_le_sum (fun j _ => bycol j)
    _ = _ := by simp
  exact_mod_cast (mul_le_mul_iff_left₀ wt).mp estimate


-- A fixed-ratio interval of primes has its prime-number-theorem lower density.
def H1 : Prop := ∀ a b : ℝ, 0 < a → a < b → ∀ δ > (0:ℝ), ∀ᶠ x : ℝ in atTop,
    b-a-δ ≤ (((Nat.primesLE ⌊b*x⌋₊).filter (fun p : ℕ => a*x < (p:ℝ))).card:ℝ) * (log x/x)

-- A weighted sum over prime co-divisors in a single integer in the target interval.
def H2 : Prop := ∀ a b : ℝ, 0 < a → a < b → ∀ δ > (0:ℝ), ∀ᶠ n : ℕ in atTop,
    let X := (n:ℝ)*√(log n)
    let m := ⌈a*√(log n)⌉₊
    ∀ j : ℕ, n*m < j → (j:ℝ) ≤ b*X →
      (∑ i : Fin (n/m), if (i.val+1) ∣ j ∧ (j/(i.val+1)).Prime then
        log (X/(i.val+1:ℝ))/(X/(i.val+1:ℝ)) else 0) ≤ b*log (1+1/(a*b))+δ

lemma exp_fixed : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ exp (-r) = r := by
  let g (x : ℝ) := exp (-x)-x
  have cont : Continuous g := by dsimp [g]; fun_prop
  have g0 : 0 < g 0 := by simp [g]
  have g1 : g 1 < 0 := by dsimp [g]; have z : exp (-1:ℝ) < exp 0 := exp_lt_exp.mpr (by norm_num); rw [exp_zero] at z; linarith
  obtain ⟨r,hr,e⟩ := intermediate_value_Icc' (show (0:ℝ)≤1 by norm_num) cont.continuousOn (show (0:ℝ) ∈ Set.Icc (g 1) (g 0) from ⟨g1.le,g0.le⟩)
  have p : 0 < r := lt_of_le_of_ne hr.1 (by intro eq; subst r; linarith)
  have l : r < 1 := lt_of_le_of_ne hr.2 (by intro eq; subst r; linarith)
  exact ⟨r,p,l,sub_eq_zero.mp e⟩

lemma matching_slack {r β : ℝ} (rp : 0 < r) (r1 : r < 1) (eq : exp (-r)=r)
    (bigger : √r/(1-r) < β) :
    0 < √r ∧ √r < β ∧ β*log (1+1/(√r*β)) < β-√r := by
  let a := √r
  have ap : 0 < a := sqrt_pos.mpr rp
  have den : 0 < 1-r := by linarith
  have bound : a < β*(1-r) := (div_lt_iff₀ den).mp bigger
  have bp : 0 < β := (div_pos ap den).trans bigger
  have aβ : a < β := by nlinarith [mul_pos bp rp]
  have prod : r/(1-r) < a*β := by
    rw [div_lt_iff₀ den]
    have w := mul_lt_mul_of_pos_left bound ap
    nlinarith only [w,show a^2 = r from sq_sqrt rp.le]
  have prodpos : 0 < a*β := mul_pos ap bp
  have inverse : 1/(a*β) < (1-r)/r := by
    rw [div_lt_div_iff₀ prodpos rp]
    exact (by have h := (div_lt_iff₀ den).mp prod; linarith)
  have ee : exp r = 1/r := by
    have inv : (exp r)⁻¹ = r := by simpa only [exp_neg] using eq
    calc
      exp r = ((exp r)⁻¹)⁻¹ := (inv_inv _).symm
      _ = 1/r := by rw [inv,one_div]
  have q : log (1+1/(a*β)) < r := by
    apply (log_lt_iff_lt_exp (by positivity)).mpr
    rw [ee]
    calc
      _ < 1 + (1-r)/r := by linarith
      _ = _ := by field_simp; ring
  exact ⟨ap,aβ,by nlinarith only [mul_lt_mul_of_pos_left q bp,bound]⟩


lemma paste_matching (n m L : ℕ) (hn : 0 < n) (hm : 0 < m) (bulk : n*m ≤ L)
    (f : Fin (n/m) → ℕ) (inj : Function.Injective f)
    (ok : ∀ i, n*m < f i ∧ f i ≤ L ∧ (i.val+1) ∣ f i) : Erdos710.f n ≤ L := by
  let a (i : Fin n) := if h : i.val < n/m then f ⟨i.val,h⟩ else (i.val+1)*m
  have hi (i : Fin n) : (i.val+1)*m ≤ n*m := Nat.mul_le_mul_right _ (by omega)
  have big (i : Fin n) (h : ¬ i.val < n/m) : n < (i.val+1)*m := by
    exact (Nat.div_lt_iff_lt_mul hm).mp (by omega)
  have less : n ≤ n*m := by simpa using Nat.mul_le_mul_left n (show 1 ≤ m by omega)
  apply Erdos710.f_le
  refine ⟨a,?_,?_⟩
  · intro i j e
    by_cases li : i.val < n/m <;> by_cases lj : j.val < n/m
    · simp only [a,dif_pos li,dif_pos lj] at e
      exact Fin.ext (congrArg (fun k : Fin (n/m) => k.val) (inj e))
    · simp only [a,dif_pos li,dif_neg lj] at e
      exact False.elim ((not_le_of_gt (ok ⟨i.val,li⟩).1) (e ▸ hi j))
    · simp only [a,dif_neg li,dif_pos lj] at e
      exact False.elim ((not_le_of_gt (ok ⟨j.val,lj⟩).1) (e ▸ hi i))
    · simp only [a,dif_neg li,dif_neg lj] at e
      exact Fin.ext (by have := Nat.eq_of_mul_eq_mul_right hm e; omega)
  · intro i
    by_cases h : i.val < n/m
    · simp only [a,dif_pos h]
      have v := ok ⟨i.val,h⟩
      exact ⟨less.trans_lt v.1,by omega,v.2.2⟩
    · simp only [a,dif_neg h]
      exact ⟨big i h,by have := hi i; omega,dvd_mul_right _ _⟩


lemma prime_row (x X a b : ℝ) (d n m : ℕ) (hd : 0 < d) (hx : x=X/d)
    (low : (n*m:ℕ) ≤ a*X) :
    ((Nat.primesLE ⌊b*x⌋₊).filter (fun p : ℕ => a*x < (p:ℝ))).card ≤
      ((Finset.Ioc (n*m) ⌊b*X⌋₊).filter (fun j => d ∣ j ∧ (j/d).Prime)).card := by
  classical
  have dr : 0 < (d:ℝ) := by exact_mod_cast hd
  apply Finset.card_le_card_of_injOn (fun p : ℕ => p*d)
  · intro p hp
    obtain ⟨hp,above⟩ := mem_filter.mp hp
    obtain ⟨below,prime⟩ := Nat.mem_primesLE.mp hp
    have fl : 0 < ⌊b*x⌋₊ := prime.pos.trans_le below
    have pos : 0 < b*x := (show (0:ℝ) < 1 by norm_num).trans_le (Nat.floor_pos.mp fl)
    have up : (p:ℝ) ≤ b*x := (Nat.le_floor_iff pos.le).mp below
    have eq : x*d = X := by rw [hx]; exact div_mul_cancel₀ _ dr.ne'
    have lower : (n*m:ℕ) < p*d := by
      have e := mul_lt_mul_of_pos_right above dr
      rw [mul_assoc,eq] at e
      exact_mod_cast low.trans_lt e
    have upper : p*d ≤ ⌊b*X⌋₊ := by
      apply Nat.le_floor
      push_cast
      have e := mul_le_mul_of_nonneg_right up dr.le
      rwa [mul_assoc,eq] at e
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lower,upper⟩,dvd_mul_left _ _,by simpa [hd] using prime⟩
  · intro p _ q _ h
    exact Nat.eq_of_mul_eq_mul_right hd h

theorem main : H1 → H2 → type_of% @Erdos710.erdos_710.variants.upper_bound := by
  intro primeEstimate divisorEstimate
  obtain ⟨r,rp,r1,eq⟩ := exp_fixed
  refine ⟨r,eq,?_⟩
  intro ε εp
  let a := √r
  let b := a/(1-r)+ε
  obtain ⟨ap,ab,gap⟩ := matching_slack rp r1 eq (show a/(1-r) < b by dsimp [b]; linarith)
  let E := b*log (1+1/(a*b))
  change E < b-a at gap
  have bp : 0 < b := ap.trans ab
  have nonE : 0 ≤ E := mul_nonneg bp.le (log_nonneg (le_add_of_nonneg_right (by positivity)))
  let η := (b-a-E)/5
  have ηp : 0 < η := by dsimp [η]; linarith
  have middle : a+η < b := by dsimp [η]; linarith
  let t := E+η
  have tp : 0 < t := add_pos_of_nonneg_of_pos nonE ηp
  have margin : t ≤ b-(a+η)-η := by dsimp [t,η]; linarith
  obtain ⟨Y,count⟩ := eventually_atTop.mp (primeEstimate (a+η) b (by positivity) middle η ηp)
  have logs := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_gt_atTop 1,logs.eventually_ge_atTop ((1/η)^2),
    logs.eventually_ge_atTop (max 1 (Y/a)),divisorEstimate a b ap ab η ηp] with n n1 large far col
  let y := √(log (n:ℝ))
  let X := (n:ℝ)*y
  let m := ⌈a*y⌉₊
  have hn : 0 < n := by omega
  have nr : 0 < (n:ℝ) := by exact_mod_cast hn
  change max 1 (Y/a) ≤ log (n:ℝ) at far
  change (1/η)^2 ≤ log (n:ℝ) at large
  have lg : 1 ≤ log (n:ℝ) := (le_max_left _ _).trans far
  have yp : 0 < y := sqrt_pos.mpr (by linarith)
  have xp : 0 < X := mul_pos nr yp
  have sqy : y^2 = log (n:ℝ) := sq_sqrt (by linarith)
  have y1 : 1 ≤ y := by nlinarith [sqy]
  have er : 1 ≤ η*y := by
    have ll : 1/η ≤ y := (le_sqrt (by positivity) (by linarith)).mpr large
    linarith [(div_le_iff₀ ηp).mp ll]
  have ce : a*y ≤ (m:ℝ) := Nat.le_ceil _
  have mpos : 0 < m := Nat.ceil_pos.mpr (mul_pos ap yp)
  have mupper : (m:ℝ) ≤ (a+η)*y := by
    have h := Nat.ceil_lt_add_one (mul_nonneg ap.le yp.le)
    change (m:ℝ) < a*y+1 at h
    nlinarith
  have lower : ((n*m:ℕ):ℝ) ≤ (a+η)*X := by
    push_cast
    dsimp [X]
    nlinarith only [mul_le_mul_of_nonneg_left mupper nr.le]
  let L := ⌊b*X⌋₊
  have bulk : n*m ≤ L := Nat.le_floor (lower.trans (mul_le_mul_of_nonneg_right middle.le xp.le))
  let d (i : Fin (n/m)) := i.val+1
  let x (i : Fin (n/m)) := X/d i
  let T (i : Fin (n/m)) := (Finset.Ioc (n*m) L).filter (fun j => d i ∣ j ∧ (j/d i).Prime)
  let w (i : Fin (n/m)) := log (x i)/x i
  have number (i : Fin (n/m)) : d i*m ≤ n := (Nat.le_div_iff_mul_le mpos).mp i.isLt
  have minx (i : Fin (n/m)) : a*log n ≤ x i := by
    have dp : 0 < (d i:ℝ) := by dsimp [d]; positivity
    rw [show x i = X/d i from rfl,le_div_iff₀ dp]
    have h : (d i:ℝ)*m ≤ n := by exact_mod_cast number i
    have h1 := mul_le_mul_of_nonneg_left ce dp.le
    have h2 := mul_le_mul_of_nonneg_right (h1.trans h) yp.le
    dsimp [X]
    rw [← sqy]
    nlinarith only [h2]
  have x1 (i : Fin (n/m)) : 1 ≤ x i := by
    have dp : 0 < (d i:ℝ) := by dsimp [d]; positivity
    have di : d i ≤ n := (Nat.le_mul_of_pos_right _ mpos).trans (number i)
    apply (le_div_iff₀ dp).mpr
    dsimp [X]
    have cast : (d i:ℝ) ≤ n := by exact_mod_cast di
    nlinarith only [cast,mul_le_mul_of_nonneg_left y1 nr.le]
  have non (i : Fin (n/m)) : 0 ≤ w i := div_nonneg (log_nonneg (x1 i)) (by linarith [x1 i])
  have row (i : Fin (n/m)) : t ≤ (T i).card*w i := by
    have hw : Y ≤ x i := ((div_le_iff₀ ap).mp ((le_max_right _ _).trans far)).trans (by simpa only [mul_comm] using minx i)
    have c := count (x i) hw
    have inc := prime_row (x i) X (a+η) b (d i) n m (by dsimp [d]; omega) rfl lower
    have cr : (((Nat.primesLE ⌊b*x i⌋₊).filter (fun p : ℕ => (a+η)*x i < (p:ℝ))).card:ℝ) ≤ (T i).card := by exact_mod_cast inc
    exact margin.trans (c.trans (mul_le_mul_of_nonneg_right cr (non i)))
  have column (j : ℕ) : (∑ i : Fin (n/m), if j ∈ T i then w i else 0) ≤ t := by
    by_cases h : j ∈ Finset.Ioc (n*m) L
    · have bd := mem_Ioc.mp h
      have le := (Nat.le_floor_iff (mul_nonneg bp.le xp.le)).mp bd.2
      have c := col j bd.1 le
      simpa only [T,mem_filter,h,true_and,d,w,x,X,y,t,E,Nat.cast_add,Nat.cast_one] using c
    · simpa only [T,mem_filter,h,false_and,if_false,sum_const_zero] using tp.le
  obtain ⟨f,inj,ok⟩ := weighted_matching T w t tp non row column
  have bound := paste_matching n m L hn mpos bulk f inj (fun i => by
    obtain ⟨h,dvd,_⟩ := mem_filter.mp (ok i)
    exact ⟨(mem_Ioc.mp h).1,(mem_Ioc.mp h).2,dvd⟩)
  have rr : (Erdos710.f n:ℝ) ≤ L := by exact_mod_cast bound
  simpa only [b,a,X,y,mul_assoc] using rr.trans (Nat.floor_le (mul_nonneg bp.le xp.le))


end OMA.R_Erdos710_erdos_710_variants_upper_bound_R1
