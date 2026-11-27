import FormalConjectures.ErdosProblems.«978»
import Mathlib

/-! # Power-free polynomial values and finite congruence sieves

The local densities factor by the Chinese remainder theorem. A uniform bound on
congruence roots and Chebyshev's estimate for the number of primes control all
primes up to the input bound. Only primes beyond that bound require the large-prime
estimate from Hooley's method (Mathematika 14 (1967), 21–26). -/

namespace OMA.R_Erdos978_erdos_978_parts_i_R1

open Polynomial Finset Function Filter Real Topology
open scoped Classical

-- At good primes the polynomial has at most its degree many roots modulo p^(degree-1).
def H1 : Prop := ∀ f : ℤ[X], Irreducible f → 2 < f.natDegree →
  ∀ᶠ p : ℕ in atTop, p.Prime →
    Nat.count (fun r : ℕ => (p:ℤ)^(f.natDegree-1) ∣ f.eval (r:ℤ)) (p^(f.natDegree-1)) ≤ f.natDegree

-- The large-prime estimate counts only primes beyond the entire interval of inputs.
def H2 : Prop := ∀ f : ℤ[X], Irreducible f → 2 < f.natDegree →
  (∀ e : ℕ, f.natDegree ≠ 2^e) → 0 < f.leadingCoeff →
  ∀ ε > (0:ℝ), ∀ᶠ N : ℕ in atTop,
    {n : ℕ | ∃ p : ℕ, p.Prime ∧ N < p ∧ (p:ℤ)^(f.natDegree-1) ∣ f.eval (n:ℤ)}.partialDensity Set.univ N < ε

/-  Passing from finite sieves to natural density -/
open Set Filter Topology Real

lemma partial_split {S T : Set ℕ} (sub : S ⊆ T) (N : ℕ) :
    (T \ S).partialDensity univ N + S.partialDensity univ N = T.partialDensity univ N := by
  unfold Set.partialDensity
  simp only [inter_univ]
  rw [← add_div, ← Nat.cast_add]
  congr 2
  have sub' : S ∩ Set.Iio N ⊆ T ∩ Set.Iio N := inter_subset_inter_left _ sub
  have finite : (T ∩ Set.Iio N).Finite := (finite_Iio N).subset inter_subset_right
  have eq : (T \ S) ∩ Set.Iio N = (T ∩ Set.Iio N) \ (S ∩ Set.Iio N) := by ext; simp only [mem_inter_iff,Set.mem_sdiff]; tauto
  rw [eq]
  exact ncard_sdiff_add_ncard_of_subset sub' finite

lemma density_of_finite_sieves (S : Set ℕ) (F : ℕ → Set ℕ) (d : ℕ → ℝ)
    (sub : ∀ k, S ⊆ F k) (nested : Antitone F) (density : ∀ k, (F k).HasDensity (d k))
    (positive : ∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ d k)
    (tail : ∀ ε > (0:ℝ), ∀ᶠ k : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      ((F k) \ S).partialDensity univ n < ε) : S.HasPosDensity := by
  obtain ⟨c,hc,lb⟩ := positive
  have anti : Antitone d := fun i j h => Set.HasDensity.mono (nested h) (density j) (density i)
  have below : BddBelow (range d) := ⟨c,by rintro _ ⟨k,rfl⟩; exact lb k⟩
  let D := ⨅ k, d k
  have den : Tendsto d atTop (𝓝 D) := tendsto_atTop_ciInf anti below
  have low : c ≤ D := le_ciInf lb
  refine ⟨D,hc.trans_le low,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have small := tail (ε/3) (by positivity)
  have nearby := (Metric.tendsto_nhds.mp den (ε/3) (by positivity)).and small
  obtain ⟨k,hclose,error⟩ := nearby.exists
  have localD := Metric.tendsto_nhds.mp (density k) (ε/3) (by positivity)
  filter_upwards [localD,error] with n finiteD missed
  have split := partial_split (sub k) n
  have non : 0 ≤ ((F k) \ S).partialDensity univ n := by unfold Set.partialDensity; positivity
  rw [Real.dist_eq, abs_lt] at finiteD hclose ⊢
  constructor <;> linarith


/-  Finite products of local sieve factors -/
open Finset Filter Topology
lemma positive_sieve_products (w : ℕ → ℝ) (pos : ∀ p, 0 ≤ w p) (lt : ∀ p, w p < 1)
    (hs : Summable w) : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ ∏ p ∈ range n, (1-w p) := by
  classical
  have approx (s : Finset ℕ) : 1-(∑ i ∈ s, w i) ≤ ∏ i ∈ s, (1-w i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s h ih =>
      rw [sum_insert h,prod_insert h]
      have non := sum_nonneg (fun i (_ : i ∈ s) => pos i)
      calc
        _ ≤ (1-w p)*(1-∑ i ∈ s,w i) := by nlinarith [mul_nonneg (pos p) non]
        _ ≤ _ := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (lt p).le)
  have tend := hs.hasSum.tendsto_sum_nat
  obtain ⟨K,hK⟩ := (tend.eventually_const_lt (show (∑' j,w j)-1/2 < ∑' j,w j by linarith)).exists
  let z := ∏ i ∈ range K, (1-w i)
  have hz : 0 < z := prod_pos (fun i _ => sub_pos.mpr (lt i))
  refine ⟨z/2, by positivity,?_⟩
  intro n
  rcases le_total n K with small | large
  · apply (show z/2 ≤ z by linarith).trans
    exact prod_le_prod_of_subset_of_le_one (range_mono small) (fun i _ => sub_nonneg.mpr (lt i).le)
      (fun i _ _ => by linarith [pos i])
  · let s := range n \ range K
    have incl := range_mono large
    have eq : (∑ i ∈ s, w i) + ∑ i ∈ range K, w i = ∑ i ∈ range n, w i := sum_sdiff incl
    have bound := hs.sum_le_tsum (range n) (fun i _ => pos i)
    have tr : 1/2 ≤ ∏ i ∈ s, (1-w i) := by linarith [approx s]
    have mult : (∏ i ∈ s, (1-w i))*z = ∏ i ∈ range n, (1-w i) := prod_sdiff incl
    rw [← mult]
    nlinarith [mul_nonneg (sub_nonneg.mpr tr) hz.le]


/-  Natural density of a set of residue classes -/
open Set Filter Topology Real Finset
lemma complete_periods (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hp : Function.Periodic P d)
    (j : ℕ) : Nat.count P (j*d) = j * Nat.count P d := by
  induction j with
  | zero => simp
  | succ j ih =>
    have shift : (fun k => P (j*d+k)) = P := by
      funext k
      simpa [Nat.nsmul_eq_mul, Nat.add_comm] using hp.nsmul j k
    have cs : Nat.count (fun k => P (j*d + k)) d = Nat.count P d := by
      simp only [Nat.count_eq_card_filter_range]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro k _
      exact (congrFun shift k).to_iff
    rw [Nat.succ_mul, Nat.count_add, cs, ih, Nat.succ_mul]

lemma period_density (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hd : 0 < d)
    (hp : Function.Periodic P d) :
    {n : ℕ | P n}.HasDensity ((Nat.count P d:ℝ)/d) := by
  let c : ℝ := Nat.count P d
  let a := c/d
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hc' : c ≤ d := by dsimp [c]; exact_mod_cast Nat.count_le (p:=P)
  have ha : 0 ≤ a := div_nonneg hc hd'.le
  have collapse : (d:ℝ)*a = c := mul_div_cancel₀ _ hd'.ne'
  have counts (n : ℕ) : ({m : ℕ | P m} ∩ Set.Iio n).ncard = Nat.count P n := by
    rw [show {m : ℕ | P m} ∩ Set.Iio n =
        (↑((Finset.range n).filter P) : Set ℕ) by ext m; simp [and_comm],
        Set.ncard_coe_finset,Nat.count_eq_card_filter_range]
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have tend := (tendsto_const_div_atTop_nhds_zero_nat (d:ℝ)).eventually_lt_const he
  filter_upwards [tend,eventually_ge_atTop 1] with n err pos
  let q := n/d
  have low : q*d ≤ n := Nat.div_mul_le_self n d
  have upper : n ≤ (q+1)*d := (show n < q*d+d from Nat.lt_div_mul_add hd).le.trans_eq (by ring)
  have clo : q*Nat.count P d ≤ Nat.count P n := (complete_periods P d hp q) ▸ (Nat.count_monotone P low)
  have chi : Nat.count P n ≤ (q+1)*Nat.count P d :=
    (complete_periods P d hp (q+1)) ▸ (Nat.count_monotone P upper)
  have l : (q:ℝ)*d ≤ n := by exact_mod_cast low
  have u : (n:ℝ) ≤ ((q:ℝ)+1)*d := by exact_mod_cast upper
  have cl : (q:ℝ)*c ≤ Nat.count P n := by dsimp [c]; exact_mod_cast clo
  have cu : (Nat.count P n:ℝ) ≤ ((q:ℝ)+1)*c := by dsimp [c]; exact_mod_cast chi
  have posn : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have l' := mul_le_mul_of_nonneg_right l ha
  have u' := mul_le_mul_of_nonneg_right u ha
  rw [mul_assoc,collapse] at l'
  rw [mul_assoc,collapse] at u'
  have cardI : (Set.Iio n).ncard = n := by simp
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,counts,cardI,
    Real.dist_eq,abs_lt]
  change -ε < (Nat.count P n:ℝ)/n-a ∧ (Nat.count P n:ℝ)/n-a < ε
  have tiny : (d:ℝ)< ε*n := (div_lt_iff₀ posn).mp err
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ posn]; nlinarith
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ posn]; nlinarith


/-  The density of simultaneous congruence restrictions -/
open Finset Function
open scoped Classical
lemma crt_count (P : Finset ℕ) (m : ℕ → ℕ) (hm : ∀ i ∈ P, 0 < m i)
    (cop : (P : Set ℕ).Pairwise (Nat.Coprime on m)) (ok : ℕ → ℕ → Prop) :
    Nat.count (fun n => ∀ i ∈ P, ok i (n % m i)) (∏ i ∈ P, m i) =
      ∏ i ∈ P, Nat.count (ok i) (m i) := by
  classical
  let D := ∏ i ∈ P, m i
  let M := (i : ↥P) → Fin (m i.val)
  let rems (r : Fin D) : M := fun i => ⟨r.val % m i.val, Nat.mod_lt _ (hm i.val i.prop)⟩
  have surj : Function.Surjective rems := by
    intro v
    let a (i : ℕ) := if h : i ∈ P then (v ⟨i,h⟩).val else 0
    let z := Nat.chineseRemainderOfFinset a m P (fun i hi => (hm i hi).ne') cop
    have below : z.val < D := Nat.chineseRemainderOfFinset_lt_prod a m _ _
    refine ⟨⟨z.val,below⟩,?_⟩
    funext i
    apply Fin.ext
    have h := (z.prop i.val i.prop)
    change z.val % m i.val = a i.val % m i.val at h
    simpa only [a,dif_pos i.prop,Nat.mod_eq_of_lt (v i).isLt] using h
  have cards : Fintype.card (Fin D) = Fintype.card M := by
    simp only [M,D,Fintype.card_fin,Fintype.card_pi,prod_coe_sort]
  let e := Equiv.ofBijective rems ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨surj,cards⟩)
  let wt (v : M) := ∏ i : ↥P, (if ok i.val (v i).val then 1 else 0 : ℕ)
  have point (r : Fin D) : (if ∀ i ∈ P, ok i (r.val % m i) then 1 else 0 : ℕ) = wt (e r) := by
    change _ = ∏ i : ↥P, (if ok i.val (r.val % m i.val) then 1 else 0 : ℕ)
    by_cases h : ∀ i ∈ P, ok i (r.val % m i)
    · rw [if_pos h]
      symm
      exact prod_eq_one (fun i _ => if_pos (h i.val i.prop))
    · rw [if_neg h]
      push Not at h
      obtain ⟨i,hi,bad⟩ := h
      exact (Finset.prod_eq_zero (i:=⟨i,hi⟩) (mem_univ _) (if_neg bad)).symm
  have one (i : ℕ) : (∑ j : Fin (m i), (if ok i j.val then 1 else 0 : ℕ)) = Nat.count (ok i) (m i) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if ok i n then (1:ℕ) else 0), Nat.count_eq_card_filter_range,card_filter]
  rw [Nat.count_eq_card_filter_range,card_filter, ← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ r : Fin D, wt (e r) := sum_congr rfl (fun r _ => point r)
    _ = ∑ v : M, wt v := Equiv.sum_comp e wt
    _ = ∏ i : ↥P, (∑ j : Fin (m i.val), (if ok i.val j.val then 1 else 0 : ℕ)) :=
      (Fintype.prod_sum (fun (i : ↥P) (j : Fin (m i.val)) => if ok i.val j.val then (1:ℕ) else 0)).symm
    _ = _ := by simp_rw [one]; exact prod_coe_sort P (fun i => Nat.count (ok i) (m i))


/-  Prime-power divisibility over the integers -/
open Polynomial
lemma integer_powerfree (k : ℕ) (a : ℤ) :
    Powerfree k a ↔ ∀ p : ℕ, p.Prime → ¬(p:ℤ)^k ∣ a := by
  constructor
  · intro h p hp hd
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (h hd)
  · intro h z hz
    by_contra no
    obtain ⟨p,hp,dp⟩ := Nat.exists_prime_and_dvd (fun e => no (Int.isUnit_iff_natAbs_eq.mpr e))
    exact h p hp ((pow_dvd_pow_of_dvd (Int.natCast_dvd.mpr dp) k).trans hz)


open scoped Classical
lemma finite_density (P : Finset ℕ) (m : ℕ → ℕ) (hm : ∀ i ∈ P, 0 < m i)
    (cop : (P : Set ℕ).Pairwise (Nat.Coprime on m)) (ok : ℕ → ℕ → Prop) :
    {n : ℕ | ∀ i ∈ P, ok i (n % m i)}.HasDensity
      (∏ i ∈ P, ((Nat.count (ok i) (m i) : ℝ)/m i)) := by
  classical
  let D := ∏ i ∈ P, m i
  have per : Function.Periodic (fun n : ℕ => ∀ i ∈ P, ok i (n % m i)) D := by
    intro n
    apply propext
    have eq (i : ℕ) (hi : i ∈ P) : (n+D)%m i = n % m i := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (Finset.dvd_prod_of_mem m hi)]
      simp
    exact ⟨fun h i hi => (eq i hi) ▸ h i hi,fun h i hi => (eq i hi).symm ▸ h i hi⟩
  have den := period_density _ D (prod_pos hm) per
  have same := crt_count P m hm cop ok
  change Nat.count _ D = _ at same
  rw [same] at den
  simpa only [D, Nat.cast_prod,prod_div_distrib] using den


lemma divides_period (f : ℤ[X]) (d : ℕ) :
    Function.Periodic (fun n : ℕ => (d:ℤ) ∣ f.eval (n:ℤ)) d := by
  intro n
  apply propext
  have delta := Polynomial.sub_dvd_eval_sub ((n+d:ℕ):ℤ) (n:ℤ) f
  have h : (d:ℤ) ∣ f.eval ((n+d:ℕ):ℤ) - f.eval (n:ℤ) := by simpa using delta
  constructor
  · intro hnd
    simpa using dvd_sub hnd h
  · intro hn
    simpa using dvd_add h hn


lemma prime_ratio_small (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (N.primeCounting:ℝ) < δ*N := by
  have ub := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le (show 0 < (1:ℝ) by norm_num))
  have lg := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop ((log 4+1)/δ)
  filter_upwards [ub,lg,eventually_gt_atTop 1] with N hi large n1
  simp only [Nat.floor_natCast] at hi
  change (log 4+1)/δ < log (N:ℝ) at large
  have lp : 0 < log (N:ℝ) := log_pos (by exact_mod_cast n1)
  refine hi.trans_lt ((div_lt_iff₀ lp).mpr ?_)
  have a := (div_lt_iff₀ hδ).mp large
  have b := mul_lt_mul_of_pos_right a (show 0 < (N:ℝ) by exact_mod_cast (by omega : 0 < N))
  linarith only [b,show log (N:ℝ)*δ*N = δ*N*log (N:ℝ) by ring]

lemma sum_tail_lt {w : ℕ → ℝ} (hw : Summable w) (nw : ∀ p, 0 ≤ w p) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ K : ℕ in atTop, ∀ s : Finset ℕ, (∀ p ∈ s, K ≤ p) → ∑ p ∈ s,w p < δ := by
  have app := hw.hasSum.tendsto_sum_nat.eventually_const_lt (show (∑' p,w p)-δ < ∑' p,w p by linarith)
  filter_upwards [app] with K hK
  intro s hs
  have dis : Disjoint (range K) s := disjoint_left.mpr (fun _ hp h => (Nat.not_le_of_gt (mem_range.mp hp)) (hs _ h))
  have le := hw.sum_le_tsum ((range K) ∪ s) (fun p _ => nw p)
  rw [sum_union dis] at le
  linarith

lemma count_union_le (s : Finset ℕ) (bad : ℕ → ℕ → Prop) [∀ p, DecidablePred (bad p)] (N : ℕ) :
    Nat.count (fun n => ∃ p ∈ s, bad p n) N ≤ ∑ p ∈ s,Nat.count (bad p) N := by
  classical
  simp only [Nat.count_eq_card_filter_range]
  let A (p : ℕ) := (range N).filter (bad p)
  have eq : (range N).filter (fun n => ∃ p ∈ s, bad p n) = s.biUnion A := by
    ext n
    simp only [mem_filter,A]
    aesop
  have res := Finset.card_biUnion_le (s:=s) (t:=A)
  rw [← eq] at res
  convert! res using 1


lemma count_up_to (P : ℕ → Prop) [DecidablePred P] (d N : ℕ) (hd : 0<d)
    (hp : Function.Periodic P d) :
    (Nat.count P N:ℝ) ≤ (N:ℝ)*((Nat.count P d:ℝ)/d) + Nat.count P d := by
  let q := N/d
  have upper : N ≤ (q+1)*d := (show N < q*d+d from Nat.lt_div_mul_add hd).le.trans_eq (by ring)
  have ch : Nat.count P N ≤ (q+1)*Nat.count P d :=
    (complete_periods P d hp (q+1)) ▸ (Nat.count_monotone P upper)
  have chr : (Nat.count P N:ℝ) ≤ ((q:ℝ)+1)*Nat.count P d := by exact_mod_cast ch
  have low : (q:ℝ)*d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
  have dr : 0 < (d:ℝ) := by exact_mod_cast hd
  have r : (q:ℝ) ≤ (N:ℝ)/d := (le_div_iff₀ dr).mpr low
  apply chr.trans
  have h := mul_le_mul_of_nonneg_right r (Nat.cast_nonneg (Nat.count P d) (α:=ℝ))
  rw [add_mul,one_mul]
  calc
    _ ≤ ((N:ℝ)/d)*Nat.count P d + Nat.count P d := by linarith
    _ = _ := by ring


open scoped Classical
lemma density_eq_count (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    {n : ℕ | P n}.partialDensity Set.univ N = (Nat.count P N : ℝ)/N := by
  have c : ({n : ℕ | P n} ∩ Set.Iio N).ncard = Nat.count P N := by
    rw [show {n : ℕ | P n} ∩ Set.Iio N =
        (↑((Finset.range N).filter P) : Set ℕ) by ext n; simp [and_comm],
        Set.ncard_coe_finset,Nat.count_eq_card_filter_range]
  have cardI : (Set.Iio N).ncard = N := by simp
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,c,cardI]

lemma medium_prime_tail (bad : ℕ → ℕ → Prop) [∀ p, DecidablePred (bad p)] (m : ℕ → ℕ) (D : ℕ)
    (mp : ∀ p, p.Prime → 0 < m p) (per : ∀ p, Function.Periodic (bad p) (m p))
    (few : ∀ᶠ p : ℕ in atTop, p.Prime → Nat.count (bad p) (m p) ≤ D)
    (w : ℕ → ℝ) (sw : Summable w) (nw : ∀ p, 0 ≤ w p)
    (wt : ∀ p, p.Prime → w p = (Nat.count (bad p) (m p):ℝ)/(m p:ℝ)) :
    ∀ ε > (0:ℝ), ∀ᶠ K : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      {n : ℕ | ∃ p : ℕ, p.Prime ∧ K ≤ p ∧ p ≤ N ∧ bad p n}.partialDensity Set.univ N < ε := by
  classical
  intro ε he
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.1 few
  filter_upwards [eventually_ge_atTop K₀,sum_tail_lt sw nw (show 0 < ε/2 by positivity)] with K Kbig short
  have den : 0 < (D:ℝ)+1 := by positivity
  filter_upwards [prime_ratio_small (ε/2/((D:ℝ)+1)) (by positivity),eventually_gt_atTop 0] with N primes pos
  let s := N.primesLE.filter (fun p => K ≤ p)
  have mem (p : ℕ) : p ∈ s ↔ p.Prime ∧ K ≤ p ∧ p ≤ N := by
    simp [s,Nat.mem_primesLE,and_assoc,and_comm]
  have idset : {n : ℕ | ∃ p : ℕ, p.Prime ∧ K ≤ p ∧ p ≤ N ∧ bad p n} = {n | ∃ p ∈ s, bad p n} := by
    ext n
    simp only [Set.mem_ofPred_eq,mem]
    aesop
  rw [idset,density_eq_count,div_lt_iff₀ (show 0 < (N:ℝ) by exact_mod_cast pos)]
  have cu := count_union_le s bad N
  have cu' : (Nat.count (fun n => ∃ p ∈ s,bad p n) N:ℝ) ≤ ∑ p ∈ s,(Nat.count (bad p) N:ℝ) := by exact_mod_cast cu
  apply cu'.trans_lt
  have upper : ∑ p ∈ s,(Nat.count (bad p) N:ℝ) ≤ ∑ p ∈ s, ((N:ℝ)*w p + D) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨prime,large,_⟩ := (mem p).mp hp
    rw [wt p prime]
    exact (count_up_to (bad p) (m p) N (mp p prime) (per p)).trans
      (add_le_add_right (by exact_mod_cast hK₀ p (Kbig.trans large) prime) _)
  refine upper.trans_lt ?_
  rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]
  have number : (s.card:ℝ) ≤ N.primeCounting := by exact_mod_cast
    ((card_filter_le _ _).trans_eq (Nat.primesLE_card_eq_primeCounting N) : s.card ≤ N.primeCounting)
  have one := mul_lt_mul_of_pos_left (short s (fun p hp => ((mem p).mp hp).2.1)) (show 0 < (N:ℝ) by exact_mod_cast pos)
  have two := mul_lt_mul_of_pos_right primes den
  have cancel : ε / 2 / ((D:ℝ)+1)*N*((D:ℝ)+1) = ε/2*N := by field_simp
  rw [cancel] at two
  have three := mul_le_mul_of_nonneg_right number (Nat.cast_nonneg D)
  nlinarith only [one,two,three,Nat.cast_nonneg (α:=ℝ) N.primeCounting]


open scoped Classical
lemma density_of_union_le {S T U : Set ℕ} (sub : S ⊆ T ∪ U) (N : ℕ) :
    S.partialDensity Set.univ N ≤ T.partialDensity Set.univ N + U.partialDensity Set.univ N := by
  let I := Set.Iio N
  have hem : S ∩ I ⊆ (T ∩ I) ∪ (U ∩ I) := by
    rintro n ⟨hn,hi⟩
    rcases sub hn with t|u
    · exact Or.inl ⟨t,hi⟩
    · exact Or.inr ⟨u,hi⟩
  have fin : ((T ∩ I) ∪ (U ∩ I)).Finite := (Set.finite_Iio N).subset (by intro n h; rcases h with h|h <;> exact h.2)
  have b := (Set.ncard_le_ncard hem fin).trans (Set.ncard_union_le _ _)
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,← add_div,← Nat.cast_add]
  exact div_le_div_of_nonneg_right (by exact_mod_cast b) (Nat.cast_nonneg _)


theorem main : H1 → H2 → type_of% @Erdos978.erdos_978.parts.i := by
  classical
  intro good huge f hi hd hp2 hlc noFixed
  let k := f.natDegree-1
  let m (p : ℕ) := p^k
  let bad (p n : ℕ) := (p:ℤ)^k ∣ f.eval (n:ℤ)
  let w (p : ℕ) : ℝ := if p.Prime then (Nat.count (bad p) (m p):ℝ)/(m p:ℝ) else 0
  let A (L : ℕ) := (Finset.range L).filter Nat.Prime
  let F (L : ℕ) := {n : ℕ | ∀ p ∈ A L, ¬bad p n}
  let S := {n : ℕ | Powerfree k (f.eval (n:ℤ))}
  let d (L : ℕ) := ∏ p ∈ Finset.range L, (1-w p)
  have per (p : ℕ) : Function.Periodic (bad p) (m p) := by
    simpa only [bad,m,Nat.cast_pow] using divides_period f (m p)
  have cond (n : ℕ) : n ∈ S ↔ ∀ p : ℕ, p.Prime → ¬bad p n := integer_powerfree k _
  have sub (L : ℕ) : S ⊆ F L := fun n hn p hp => (cond n).mp hn p (mem_filter.mp hp).2
  have nested : Antitone F := by
    intro i j le n hn p hp
    exact hn p (mem_filter.mpr ⟨range_mono le (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩)
  have total (p : ℕ) : Nat.count (bad p) (m p) + Nat.count (fun r => ¬bad p r) (m p) = m p := by
    simp only [Nat.count_eq_card_filter_range,card_filter_add_card_filter_not,card_range]
  have non (p : ℕ) : 0 ≤ w p := by dsimp [w]; split <;> positivity
  have strict (p : ℕ) : w p < 1 := by
    by_cases prime : p.Prime
    · obtain ⟨n,hn⟩ := noFixed p prime
      have miss : ¬bad p (n % m p) := by rw [(per p).map_mod_nat]; exact hn
      have mp : 0 < m p := pow_pos prime.pos _
      have cp := (Nat.count_ne_iff_exists (p:=fun r => ¬bad p r)).mpr ⟨n % m p,Nat.mod_lt _ mp,miss⟩
      have few : Nat.count (bad p) (m p) < m p := by have := total p; omega
      change (if p.Prime then _ else _) < _
      rw [if_pos prime,div_lt_one (by exact_mod_cast mp)]
      exact_mod_cast few
    · simp [w,prime]
  have counts : ∀ᶠ p : ℕ in atTop, p.Prime → Nat.count (bad p) (m p) ≤ f.natDegree := good f hi hd
  have sumw : Summable w := by
    have major : Summable (fun p : ℕ => (f.natDegree:ℝ)*((p:ℝ)^2)⁻¹) :=
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left _
    apply major.of_norm_bounded_eventually_nat
    filter_upwards [counts] with p bound
    rw [Real.norm_eq_abs,abs_of_nonneg (non p)]
    by_cases prime : p.Prime
    · simp only [w,m,Nat.cast_pow,if_pos prime,← div_eq_mul_inv]
      exact div_le_div₀ (Nat.cast_nonneg _) (by exact_mod_cast bound prime)
        (pow_pos (by exact_mod_cast prime.pos : 0 < (p:ℝ)) 2)
        (pow_le_pow_right₀ (by exact_mod_cast prime.one_le) (by dsimp [k]; omega))
    · simp only [w,if_neg prime]
      positivity
  have localD (L : ℕ) : (F L).HasDensity (d L) := by
    have hp {p : ℕ} (h : p ∈ A L) : p.Prime := (mem_filter.mp h).2
    have cop : (A L : Set ℕ).Pairwise (Nat.Coprime on m) := by
      intro p pp q qq ne
      exact ((Nat.coprime_primes (hp pp) (hp qq)).mpr ne).pow_left k |>.pow_right k
    have den := finite_density (A L) m (fun p h => pow_pos (hp h).pos _) cop (fun p n => ¬bad p n)
    have eqset : {n : ℕ | ∀ p ∈ A L, ¬bad p (n % m p)} = F L := by
      ext n
      simp only [F,Set.mem_ofPred_eq, (per _).map_mod_nat]
    rw [eqset] at den
    have prod : (∏ p ∈ A L, (Nat.count (fun r => ¬bad p r) (m p):ℝ)/(m p:ℝ)) = d L := by
      calc
        _ = ∏ p ∈ A L,(1-w p) := by
          apply prod_congr rfl
          intro p h
          have mp : 0 < (m p:ℝ) := by exact_mod_cast (pow_pos (hp h).pos k)
          have sum : (Nat.count (bad p) (m p):ℝ) + (Nat.count (fun r => ¬bad p r) (m p):ℝ) = m p := by exact_mod_cast total p
          simp only [w,if_pos (hp h)]
          field_simp
          linarith
        _ = _ := by
          change (∏ p ∈ (Finset.range L).filter Nat.Prime, (1-w p)) = ∏ p ∈ Finset.range L, (1-w p)
          rw [prod_filter]
          exact prod_congr rfl (fun p _ => by by_cases h : p.Prime <;> simp [h,w])
    rw [← prod]
    convert! den using 1
    congr!
  refine density_of_finite_sieves S F d sub nested localD (positive_sieve_products w non strict sumw) ?_
  intro ε he
  have half : 0 < ε / 2 := by positivity
  have small := medium_prime_tail bad m f.natDegree (fun p h => pow_pos h.pos _) per counts w sumw non
    (fun p h => by simp only [w,if_pos h]) (ε/2) half
  filter_upwards [small] with L hL
  filter_upwards [hL,huge f hi hd hp2 hlc (ε/2) half] with N hN hHuge
  let U := {n : ℕ | ∃ p : ℕ, p.Prime ∧ L ≤ p ∧ bad p n}
  have missing : F L \ S ⊆ U := by
    intro n hn
    have failed := mt (cond n).mpr hn.2
    push Not at failed
    obtain ⟨p,prime,hit⟩ := failed
    have large : L ≤ p := by
      by_contra! small
      exact hn.1 p (mem_filter.mpr ⟨mem_range.mpr small,prime⟩) hit
    exact ⟨p,prime,large,hit⟩
  have split := partial_split missing N
  have pos : 0 ≤ (U \ (F L \ S)).partialDensity Set.univ N := by unfold Set.partialDensity; positivity
  let V := {n : ℕ | ∃ p : ℕ, p.Prime ∧ L ≤ p ∧ p ≤ N ∧ bad p n}
  let W := {n : ℕ | ∃ p : ℕ, p.Prime ∧ N < p ∧ bad p n}
  have incl : U ⊆ V ∪ W := by
    rintro n ⟨p,prime,large,hit⟩
    rcases le_or_gt p N with h|h
    · exact Or.inl ⟨p,prime,large,h,hit⟩
    · exact Or.inr ⟨p,prime,h,hit⟩
  have b := density_of_union_le incl N
  change V.partialDensity Set.univ N < ε/2 at hN
  change W.partialDensity Set.univ N < ε/2 at hHuge
  linarith

end OMA.R_Erdos978_erdos_978_parts_i_R1
