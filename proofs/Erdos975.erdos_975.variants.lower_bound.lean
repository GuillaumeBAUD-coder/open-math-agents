import FormalConjectures.ErdosProblems.«975»
import Mathlib

/-!
# The lower bound for sums of divisors of polynomial values

For irreducible integral f with positive leading coefficient, Erdős's
lower bound is x log x. We first pass to the monic integral normalization,
keeping the congruence root counts away from the leading coefficient.
Counting complete periods in the tail reduces the theorem to two estimates.

For the first estimate, the ideal-counting asymptotic for a number field
gives a logarithmic lower bound for the sum of reciprocal ideal norms.
Unique factorization bounds that sum by finite products over primes.
Kummer–Dedekind identifies the degree-one prime ideals outside a finite set
with the distinct roots of the polynomial modulo the rational prime.
All terms of higher degree contribute a bounded multiplicative factor.

For the second estimate, the Chinese remainder theorem and the logarithmic
moment of a finite Euler product show that moduli bounded by N retain a
fixed positive fraction of that product.

Reference: P. Erdős, On the sum ∑ d(f(k)) (1952), Sections 4–5.
https://users.renyi.hu/~p_erdos/1952-08.pdf
-/

namespace OMA.Erdos975Lower

open Polynomial Finset Filter Asymptotics Erdos975
open scoped ArithmeticFunction.sigma

-- A Mertens-type lower bound for the roots of an irreducible polynomial at primes.
def primeRootEstimate : Prop := ∀ g : ℤ[X], g.Monic → Irreducible g → g.natDegree ≠ 0 →
  ∀ b : ℕ, 0 < b → ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
    c * Real.log ((N:ℝ)+1) ≤ (∏ p ∈ (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b),
        (1 + ((Nat.count (fun r : ℕ => (p:ℤ) ∣ g.eval (r:ℤ)) p : ℕ) : ℝ) / p))

-- A fixed share of the Euler product is captured by moduli d ≤ N. This is
-- a separate sieve estimate for arbitrary monic polynomials, including reducible ones.
def shortModulusEstimate : Prop := ∀ g : ℤ[X], g.Monic → ∀ b : ℕ, 0 < b →
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
    c * (∏ p ∈ (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b),
        (1 + ((Nat.count (fun r : ℕ => (p:ℤ) ∣ g.eval (r:ℤ)) p : ℕ) : ℝ) / p)) ≤
      ∑ i ∈ range N, if (i+1).Coprime b then
        ((Nat.count (fun r : ℕ => ((i+1:ℕ):ℤ) ∣ g.eval (r:ℤ)) (i+1):ℕ):ℝ) / ((i:ℝ)+1) else 0


-- Over ℚ, scaling the variable is an automorphism. Gauss's lemma transfers
-- irreducibility back to the monic integral polynomial.
lemma irreducible_monic_replacement (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    Irreducible f.integralNormalization := by
  let F := f.map (Int.castRingHom ℚ)
  let G := f.integralNormalization.map (Int.castRingHom ℚ)
  let a := (f.leadingCoeff : ℚ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (leadingCoeff_ne_zero.mpr hf.ne_zero)
  let : Invertible a := invertibleOfNonzero ha
  let e := algEquivCMulXAddC a 0
  have mon := monic_integralNormalization hf.ne_zero
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mpr
  change Irreducible G
  apply (MulEquiv.irreducible_iff e).mp
  have he : e G = C (a^(f.natDegree-1))*F := by
    apply Polynomial.funext
    intro x
    change (G.comp (C a * X + C 0)).eval x = (C (a^(f.natDegree-1))*F).eval x
    simp only [map_zero, add_zero, eval_comp, eval_mul, eval_C, eval_X, G, F, eval_map]
    exact integralNormalization_eval₂_leadingCoeff_mul (p:=f) (by omega) (Int.castRingHom ℚ) x
  rw [he]
  have unit : IsUnit (C (a^(f.natDegree-1)) : ℚ[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha))
  exact (irreducible_isUnit_mul unit).2
    ((IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive hd)).mp hf)

-- The representatives in [0,d) enumerate the entire residue ring.
lemma count_root_ring (f : ℤ[X]) (d : ℕ) [NeZero d] :
    Nat.count (fun r : ℕ => (d:ℤ) ∣ f.eval (r:ℤ)) d =
      ∑ x : ZMod d, (if f.eval₂ (Int.castRingHom (ZMod d)) x = 0 then 1 else 0 : ℕ) := by
  classical
  rw [Nat.count_eq_card_filter_range, Finset.card_filter, ← Fin.sum_univ_eq_sum_range,
    ← Equiv.sum_comp (ZMod.finEquiv d).toEquiv]
  apply sum_congr rfl
  intro i _
  have coeff : (ZMod.finEquiv d) i = (i.val : ZMod d) := by
    have v : ((ZMod.finEquiv d) i).val = i.val := by
      cases d with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => rfl
    rw [← v, ZMod.natCast_zmod_val]
  rw [show (ZMod.finEquiv d).toEquiv i = (i.val:ZMod d) from coeff]
  have h := Polynomial.eval₂_hom (p:=f) (Int.castRingHom (ZMod d)) (i.val:ℤ)
  simp only [Int.coe_castRingHom, Int.cast_natCast] at h
  simp only [h, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma unit_residue_of_coprime (a : ℤ) (d : ℕ) (hc : d.Coprime a.natAbs) :
    IsUnit (a : ZMod d) := by
  cases a with
  | ofNat n => simpa using (ZMod.isUnit_iff_coprime n d).mpr hc.symm
  | negSucc n =>
    have u : IsUnit ((n+1 : ℕ) : ZMod d) :=
      (ZMod.isUnit_iff_coprime (n+1) d).mpr hc.symm
    simpa using u.neg

-- Multiplication by the leading coefficient permutes the residue ring when
-- it is a unit, so normalization preserves the number of zeros.
lemma monic_residue_counts (f : ℤ[X]) (hf : f.natDegree ≠ 0) (d : ℕ) (hd : 0 < d)
    (hc : d.Coprime f.leadingCoeff.natAbs) :
    Nat.count (fun r : ℕ => (d:ℤ) ∣ f.integralNormalization.eval (r:ℤ)) d =
      Nat.count (fun r : ℕ => (d:ℤ) ∣ f.eval (r:ℤ)) d := by
  classical
  let : NeZero d := ⟨by omega⟩
  rw [count_root_ring, count_root_ring]
  let φ := Int.castRingHom (ZMod d)
  have hu := unit_residue_of_coprime f.leadingCoeff d hc
  let e := Units.mulLeft hu.unit
  have changeSum := Equiv.sum_comp e
    (fun x => if f.integralNormalization.eval₂ φ x = 0 then (1:ℕ) else 0)
  rw [← changeSum]
  apply sum_congr rfl
  intro y _
  have hy : e y = φ f.leadingCoeff * y := by
    change (hu.unit : ZMod d)*y = _
    rw [hu.unit_spec]
    rfl
  rw [hy, integralNormalization_eval₂_leadingCoeff_mul (by omega)]
  have u : IsUnit ((φ f.leadingCoeff)^(f.natDegree-1)) := hu.pow _
  simp only [u.isRegular.left.mul_left_eq_zero_iff]
  rfl

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

lemma blocks_le (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hp : Function.Periodic P d)
    (s L : ℕ) : (L/d) * Nat.count P d ≤ ((Ico s (s+L)).filter P).card := by
  have period : Function.Periodic P (L/d*d) := by simpa [Nat.nsmul_eq_mul] using hp.nsmul (L/d)
  rw [← complete_periods P d hp, ← Nat.filter_Ico_card_eq_of_periodic s _ P period]
  apply card_le_card
  apply filter_subset_filter
  apply Ico_subset_Ico (le_refl _)
  exact Nat.add_le_add_left (Nat.div_mul_le_self L d) s

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

-- Counting first over d and then over n includes one contribution for each
-- positive small divisor of f(n). The tail ensures f(n) is positive.
lemma divisor_blocks (f : ℤ[X]) (s N : ℕ) (hpos : ∀ n ≥ s, 1 ≤ f.eval (n:ℤ)) :
    ∑ i ∈ range N, (N/(i+1)) * Nat.count (fun r : ℕ => ((i+1:ℕ):ℤ) ∣ f.eval r) (i+1) ≤
    ∑ n ∈ Ico s (s+N), σ 0 ⌊f.eval (n:ℤ)⌋₊ := by
  classical
  let T := Ico s (s+N)
  let ok (i r : ℕ) := ((i+1:ℕ):ℤ) ∣ f.eval r
  have cardinal (n : ℕ) (hn : n ∈ T) :
      ((range N).filter (fun i => ok i n)).card ≤ (⌊f.eval (n:ℤ)⌋₊).divisors.card := by
    have hp := hpos n (mem_Ico.mp hn).1
    have cast : ((⌊f.eval (n:ℤ)⌋₊:ℕ):ℤ) = f.eval (n:ℤ) := by
      rw [Nat.floor_int, Int.toNat_of_nonneg (by omega)]
    apply card_le_card_of_injOn (fun i : ℕ => i+1) _ (fun _ _ _ _ h => Nat.succ.inj h)
    intro i hi
    have h := (mem_filter.mp hi).2
    change ((i+1:ℕ):ℤ) ∣ f.eval (n:ℤ) at h
    rw [← cast] at h
    exact Nat.mem_divisors.mpr ⟨by exact_mod_cast h, by omega⟩
  calc
    _ ≤ ∑ i ∈ range N, (T.filter (ok i)).card :=
      sum_le_sum (fun i _ => blocks_le (ok i) (i+1) (divides_period f _) s N)
    _ = ∑ n ∈ T, ((range N).filter (fun i => ok i n)).card := by
      calc
        _ = ∑ i ∈ range N, ∑ n ∈ T, (if ok i n then 1 else 0 : ℕ) := by simp only [Finset.card_filter]
        _ = ∑ n ∈ T, ∑ i ∈ range N, (if ok i n then 1 else 0 : ℕ) := sum_comm
        _ = _ := by simp only [Finset.card_filter]
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      simpa [ArithmeticFunction.sigma_zero_apply] using cardinal n hn

lemma integer_quotient {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    (N:ℝ)/2/(d:ℝ) ≤ ((N/d:ℕ):ℝ) := by
  have hq := Nat.div_pos hdN hd
  have small := Nat.mod_lt N hd
  have split := Nat.div_add_mod N d
  have dsmall : d ≤ d*(N/d) := by simpa using Nat.mul_le_mul_left d hq
  have h : N ≤ 2*(N/d)*d := by nlinarith
  have hR : (N:ℝ) ≤ 2 * ((N/d:ℕ):ℝ) * d := by exact_mod_cast h
  apply (div_le_iff₀ (by exact_mod_cast hd)).mpr
  linarith

lemma lower_on_interval (f : ℤ[X]) (s N : ℕ) (hpos : ∀ n ≥ s, 1 ≤ f.eval (n:ℤ))
    (c : ℝ)
    (weighted : c * Real.log ((N:ℝ)+1) ≤ ∑ i ∈ range N,
      ((Nat.count (fun r : ℕ => ((i+1:ℕ):ℤ) ∣ f.eval (r:ℤ)) (i+1):ℕ):ℝ) / ((i:ℝ)+1)) :
    c/2 * N * Real.log ((N:ℝ)+1) ≤
      ((∑ n ∈ Ico s (s+N), σ 0 ⌊f.eval (n:ℤ)⌋₊ : ℕ):ℝ) := by
  let rho (i : ℕ) := Nat.count (fun r : ℕ => ((i+1:ℕ):ℤ) ∣ f.eval (r:ℤ)) (i+1)
  calc
    _ = ((N:ℝ)/2) * (c * Real.log ((N:ℝ)+1)) := by ring
    _ ≤ ((N:ℝ)/2) * ∑ i ∈ range N, (rho i:ℝ) / ((i:ℝ)+1) :=
      mul_le_mul_of_nonneg_left weighted (by positivity)
    _ ≤ ∑ i ∈ range N, ((N/(i+1):ℕ):ℝ) * (rho i:ℝ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have q := integer_quotient (d:=i+1) (N:=N) (by omega) (by have := mem_range.mp hi; omega)
      push_cast at q
      calc
        _ = ((N:ℝ)/2/((i:ℝ)+1))*(rho i:ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right q (by positivity)
    _ ≤ _ := by exact_mod_cast divisor_blocks f s N hpos

lemma lower_bound_of_estimates : primeRootEstimate → shortModulusEstimate → type_of% @Erdos975.erdos_975.variants.lower_bound := by
  classical
  intro primeGrowth truncation f firr fdeg hpos
  let g := f.integralNormalization
  let b := f.leadingCoeff.natAbs
  have mon : g.Monic := monic_integralNormalization firr.ne_zero
  have gi : Irreducible g := irreducible_monic_replacement f firr fdeg
  have gd : g.natDegree ≠ 0 := by simpa only [g, natDegree_integralNormalization] using fdeg
  have hb : 0 < b := Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr firr.ne_zero)
  obtain ⟨k, hk, grow⟩ := primeGrowth g mon gi gd b hb
  obtain ⟨t, ht, truncate⟩ := truncation g mon b hb
  let c := t*k
  have hc : 0 < c := mul_pos ht hk
  have weight (j : ℕ) (hj : 1 ≤ j) : c*Real.log ((j:ℝ)+1) ≤ ∑ i ∈ range j,
      ((Nat.count (fun r : ℕ => ((i+1:ℕ):ℤ) ∣ f.eval (r:ℤ)) (i+1):ℕ):ℝ) / ((i:ℝ)+1) := by
    change (t*k)*_ ≤ _
    rw [mul_assoc]
    refine (mul_le_mul_of_nonneg_left (grow j hj) ht.le).trans ((truncate j hj).trans ?_)
    apply sum_le_sum
    intro i _
    split_ifs with good
    · rw [show Nat.count (fun r : ℕ => ((i+1:ℕ):ℤ) ∣ g.eval (r:ℤ)) (i+1) = _ from
        monic_residue_counts f fdeg (i+1) (by omega) good]
    · positivity
  obtain ⟨z, hz⟩ := eventually_atTop.mp hpos
  let s := z.toNat
  have positive (n : ℕ) (hn : s ≤ n) : 1 ≤ f.eval (n:ℤ) := by
    apply hz
    dsimp [s] at hn
    omega
  apply Asymptotics.IsBigO.of_bound (16/c)
  filter_upwards [eventually_ge_atTop ((2*(s:ℝ))+4)] with x hx
  let n := ⌊x⌋₊
  have hr : x < (n:ℝ)+1 := Nat.lt_floor_add_one x
  have hsn : s ≤ n := by
    by_contra! h
    have : (n:ℝ) < s := by exact_mod_cast h
    linarith [Nat.cast_nonneg (α:=ℝ) s]
  let N := n-s
  have finish : s+N = n := Nat.add_sub_of_le hsn
  have realN : (N:ℝ) = n-s := by dsimp [N]; rw [Nat.cast_sub hsn]
  have xN : x ≤ 4*(N:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) s]
  have xp : 1 ≤ x := by linarith [Nat.cast_nonneg (α:=ℝ) s]
  have logBound : Real.log x ≤ 2 * Real.log ((N:ℝ)+1) := by
    calc
      Real.log x ≤ Real.log (((N:ℝ)+1)^2) :=
        Real.log_le_log (by linarith) (by nlinarith [sq_nonneg ((N:ℝ)-1)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hN : 1 ≤ N := by
    by_contra! h
    have zero : (N:ℝ) = 0 := by exact_mod_cast (show N=0 by omega)
    linarith
  have interval := lower_on_interval f s N positive c (weight N hN)
  have included : Ico s (s+N) ⊆ Iic n := fun u hu => mem_Iic.mpr (by
    have := (mem_Ico.mp hu).2
    omega)
  have castSum : ((∑ u ∈ Ico s (s+N), σ 0 ⌊f.eval (u:ℤ)⌋₊ : ℕ):ℝ) ≤ Erdos975Sum f x := by
    have subsum := sum_le_sum_of_subset_of_nonneg (f:=fun u : ℕ => σ 0 ⌊f.eval (u:ℤ)⌋₊)
      included (fun _ _ _ => Nat.zero_le _)
    unfold Erdos975Sum
    exact_mod_cast subsum
  have bound := interval.trans castSum
  have non : 0 ≤ Erdos975Sum f x := by unfold Erdos975Sum; positivity
  have hxlog : 0 ≤ x*Real.log x := mul_nonneg (by linarith) (Real.log_nonneg xp)
  simp only [Real.norm_eq_abs, abs_of_nonneg hxlog, abs_of_nonneg non]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  have uu := mul_le_mul xN logBound (Real.log_nonneg xp) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right uu hc.le]


namespace Sieve

open Finset Real Polynomial

noncomputable def rootsMod (g : ℤ[X]) (d : ℕ) : ℕ :=
  Nat.count (fun r : ℕ => (d:ℤ) ∣ g.eval (r:ℤ)) d

lemma prime_roots_bound (g : ℤ[X]) (hm : g.Monic) (p : ℕ) (hp : p.Prime) :
    rootsMod g p ≤ g.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let h := g.map (Int.castRingHom (ZMod p))
  have zero : h ≠ 0 := (hm.map _).ne_zero
  rw [rootsMod, count_root_ring]
  have same : univ.filter (fun x => g.eval₂ (Int.castRingHom (ZMod p)) x = 0) = h.roots.toFinset := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Multiset.mem_toFinset, mem_roots zero,
      IsRoot, h, eval_map]
  rw [← Finset.card_filter, same]
  exact (Multiset.toFinset_card_le _).trans (card_roots_map_le_natDegree g)

lemma crt_roots (g : ℤ[X]) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (ab : a.Coprime b) :
    rootsMod g (a*b) = rootsMod g a * rootsMod g b := by
  classical
  let : NeZero a := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  let e := ZMod.chineseRemainder ab
  let root (d : ℕ) (x : ZMod d) := g.eval₂ (Int.castRingHom (ZMod d)) x
  let wt (d : ℕ) (x : ZMod d) : ℕ := if root d x = 0 then 1 else 0
  have project {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
      f (g.eval₂ (Int.castRingHom A) x) = g.eval₂ (Int.castRingHom B) (f x) := by
    rw [Polynomial.hom_eval₂]
    congr 1
    ext z
    simp
  have factors (x : ZMod (a*b)) : wt (a*b) x = wt a (e x).1 * wt b (e x).2 := by
    have h1 := project ((RingHom.fst _ _).comp e.toRingHom) x
    have h2 := project ((RingHom.snd _ _).comp e.toRingHom) x
    change (e (root (a*b) x)).1 = root a (e x).1 at h1
    change (e (root (a*b) x)).2 = root b (e x).2 at h2
    have iff : root (a*b) x = 0 ↔ root a (e x).1 = 0 ∧ root b (e x).2 = 0 := by
      rw [← h1, ← h2]
      constructor
      · intro hz
        simp [hz]
      · rintro ⟨u,v⟩
        apply e.injective
        rw [map_zero]
        exact Prod.ext u v
    by_cases u : root a (e x).1 = 0 <;> by_cases v : root b (e x).2 = 0 <;>
      simp only [wt, iff, u, v, and_self, and_false, false_and, if_true, if_false,
        mul_one, mul_zero]
  simp only [rootsMod, count_root_ring]
  change ∑ x, wt (a*b) x = (∑ x, wt a x) * ∑ y, wt b y
  simp_rw [factors]
  calc
    _ = ∑ z : ZMod a × ZMod b, wt a z.1 * wt b z.2 := Equiv.sum_comp e.toEquiv _
    _ = _ := by rw [Fintype.sum_prod_type]; exact (Fintype.sum_mul_sum _ _).symm


lemma product_roots (g : ℤ[X]) (B : Finset ℕ) (pr : ∀ p ∈ B, p.Prime) :
    rootsMod g (∏ p ∈ B, p) = ∏ p ∈ B, rootsMod g p := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [rootsMod]
  | @insert p B fresh ih =>
    have hp := pr p (mem_insert_self ..)
    have hB : ∀ q ∈ B, q.Prime := fun q hq => pr q (mem_insert_of_mem hq)
    have positive : 0 < ∏ q ∈ B, q := prod_pos (fun q hq => (hB q hq).pos)
    have cop : p.Coprime (∏ q ∈ B, q) := Nat.coprime_prod_right_iff.mpr fun q hq =>
      (Nat.coprime_primes hp (hB q hq)).mpr (fun e => fresh (e ▸ hq))
    rw [prod_insert fresh, prod_insert fresh, crt_roots g hp.pos positive cop, ih hB]

lemma count_short_subsets (g : ℤ[X]) (P : Finset ℕ) (N b : ℕ) (hN : 0 < N)
    (pr : ∀ p ∈ P, p.Prime ∧ p.Coprime b) :
    ∑ B ∈ P.powerset.filter (fun B : Finset ℕ => (∑ p ∈ B, Real.log (p:ℝ)) ≤ Real.log (N:ℝ)),
        ∏ p ∈ B, ((rootsMod g p:ℝ)/p) ≤
    ∑ i ∈ range N, if (i+1).Coprime b then ((rootsMod g (i+1):ℝ)/((i:ℝ)+1)) else 0 := by
  classical
  let short := P.powerset.filter (fun B : Finset ℕ => (∑ p ∈ B, Real.log (p:ℝ)) ≤ Real.log (N:ℝ))
  let D (B : Finset ℕ) := ∏ p ∈ B, p
  let F (i : ℕ) : ℝ := if (i+1).Coprime b then (rootsMod g (i+1):ℝ)/((i:ℝ)+1) else 0
  have subset {B : Finset ℕ} (h : B ∈ short) : B ⊆ P := mem_powerset.mp (mem_filter.mp h).1
  have good {B : Finset ℕ} (h : B ∈ short) : ∀ p ∈ B, p.Prime := fun p hp => (pr p (subset h hp)).1
  have positive {B : Finset ℕ} (h : B ∈ short) : 0 < D B := prod_pos fun p hp => (good h p hp).pos
  have below {B : Finset ℕ} (h : B ∈ short) : D B ≤ N := by
    have hp : (0:ℝ)< D B := by exact_mod_cast positive h
    have hn : (0:ℝ)< N := by exact_mod_cast hN
    have logD : Real.log (D B : ℝ) = ∑ p ∈ B, Real.log (p:ℝ) := by
      simp only [D, Nat.cast_prod]
      exact Real.log_prod fun p hp => (Nat.cast_ne_zero.mpr (good h p hp).ne_zero)
    exact_mod_cast (Real.log_le_log_iff hp hn).mp (logD.trans_le (mem_filter.mp h).2)
  have inj : Set.InjOn (fun B => D B-1) (short : Set (Finset ℕ)) := by
    intro A hA B hB e
    change D A - 1 = D B - 1 at e
    have hAB : D A = D B := by have := positive hA; have := positive hB; omega
    simpa only [D, Nat.primeFactors_prod (good hA), Nat.primeFactors_prod (good hB)]
      using congrArg Nat.primeFactors hAB
  have value (B : Finset ℕ) (hB : B ∈ short) :
      ∏ p ∈ B, ((rootsMod g p:ℝ)/p) = F (D B-1) := by
    have hd := positive hB
    have one : D B-1+1 = D B := by omega
    have cop : (D B).Coprime b := Nat.coprime_prod_left_iff.mpr fun p hp => (pr p (subset hB hp)).2
    simp only [F, one, if_pos cop, prod_div_distrib, ← Nat.cast_prod]
    rw [← Nat.cast_add_one, one, product_roots g B (good hB)]
    simp only [D, Nat.cast_prod]
  calc
    _ = ∑ B ∈ short, F (D B-1) := sum_congr rfl value
    _ = ∑ i ∈ short.image (fun B => D B-1), F i := (sum_image inj).symm
    _ ≤ ∑ i ∈ range N, F i := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        obtain ⟨B,hB,rfl⟩ := mem_image.mp hi
        exact mem_range.mpr (by have := positive hB; have := below hB; omega)
      · intro i _ _
        dsimp [F]
        split <;> positivity


-- Each prime p ≤ M has at least M/(2p) multiples up to M.
-- For every n, the product of its distinct prime factors divides n.
lemma prime_log_weight (M : ℕ) (hM : 0 < M) (P : Finset ℕ)
    (pr : ∀ p ∈ P, p.Prime ∧ p ≤ M) :
    (∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ)) ≤ 2*Real.log (M:ℝ) := by
  classical
  let term (p i : ℕ) : ℝ := if p ∣ i+1 then Real.log (p:ℝ) else 0
  have lower (p : ℕ) (hp : p ∈ P) :
      (M:ℝ)*(Real.log (p:ℝ)/p) ≤ 2*(∑ i ∈ range M, term p i) := by
    have prime := (pr p hp).1
    have leM := (pr p hp).2
    have hq : 1 ≤ M/p := (Nat.div_pos leM prime.pos)
    have hm : M ≤ 2*(M/p)*p := by
      have hdiv := Nat.mod_add_div M p
      have hmod := Nat.mod_lt M prime.pos
      have hprod : p ≤ p*(M/p) := by simpa using Nat.mul_le_mul_left p hq
      nlinarith
    have realM : (M:ℝ) ≤ 2*((M/p:ℕ):ℝ)*p := by exact_mod_cast hm
    have lg : 0 ≤ log (p:ℝ) := log_nonneg (by exact_mod_cast prime.one_le)
    have pos : (0:ℝ)<p := by exact_mod_cast prime.pos
    have summ : (∑ i ∈ range M, term p i) = ((M/p:ℕ):ℝ)*log (p:ℝ) := by
      simp only [term, ← Finset.sum_filter, sum_const, nsmul_eq_mul, Nat.card_multiples]
    rw [summ, ← mul_div_assoc, div_le_iff₀ pos]
    nlinarith [mul_le_mul_of_nonneg_right realM lg]
  have upper (i : ℕ) (hi : i ∈ range M) : (∑ p ∈ P, term p i) ≤ log (M:ℝ) := by
    let B := P.filter (fun p : ℕ => p ∣ i+1)
    have sub : B ⊆ (i+1).primeFactors := by
      intro p hp
      obtain ⟨hP,hd⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨(pr p hP).1, hd, by omega⟩
    have dvd : (∏ p ∈ B, p) ∣ i+1 :=
      (Finset.prod_dvd_prod_of_subset B (i+1).primeFactors (fun p => p) sub).trans
        (Nat.prod_primeFactors_dvd _)
    have pos : 0 < ∏ p ∈ B, p := prod_pos (fun p hp => (pr p (mem_filter.mp hp).1).1.pos)
    have lp : (∏ p ∈ B, p) ≤ M := (Nat.le_of_dvd (Nat.succ_pos _) dvd).trans (mem_range.mp hi)
    have castp : (0:ℝ) < ↑(∏ p ∈ B, p) := by exact_mod_cast pos
    have castle : (↑(∏ p ∈ B, p):ℝ) ≤ M := by exact_mod_cast lp
    calc
      _ = ∑ p ∈ B, log (p:ℝ) := by simp only [B, term, Finset.sum_filter]
      _ = log (↑(∏ p ∈ B, p):ℝ) := by
        rw [Nat.cast_prod, Real.log_prod]
        exact fun p hp => Nat.cast_ne_zero.mpr (pr p (mem_filter.mp hp).1).1.ne_zero
      _ ≤ _ := Real.log_le_log castp castle
  have result : (M:ℝ)*(∑ p ∈ P, log (p:ℝ)/p) ≤ (M:ℝ)*(2*log (M:ℝ)) := by
    calc
      _ = ∑ p ∈ P, (M:ℝ)*(log (p:ℝ)/p) := mul_sum ..
      _ ≤ ∑ p ∈ P, 2*(∑ i ∈ range M, term p i) := sum_le_sum lower
      _ = 2*∑ i ∈ range M, ∑ p ∈ P, term p i := by rw [← mul_sum, sum_comm]
      _ ≤ 2*∑ i ∈ range M, log (M:ℝ) := mul_le_mul_of_nonneg_left (sum_le_sum upper) (by norm_num)
      _ = _ := by simp; ring
  exact (mul_le_mul_iff_of_pos_left (by exact_mod_cast hM : (0:ℝ)<M)).mp result


lemma euler_moment (w l : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) (hl : ∀ p, 0 ≤ l p)
    (S : Finset ℕ) :
    ∑ B ∈ S.powerset, (∑ p ∈ B, l p) * ∏ p ∈ B, w p ≤
      (∑ p ∈ S, l p*w p) * ∏ p ∈ S, (1+w p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    let Z := ∏ q ∈ S, (1+w q)
    let M := ∑ B ∈ S.powerset, (∑ q ∈ B, l q) * ∏ q ∈ B, w q
    let A := ∑ q ∈ S, l q*w q
    have hz : 0 ≤ Z := prod_nonneg fun i _ => by linarith [hw i]
    have big : ∑ B ∈ S.powerset, (∑ q ∈ insert p B, l q)* ∏ q ∈ insert p B, w q =
          (l p*w p)*Z + w p*M := by
      dsimp [Z,M]
      rw [prod_one_add, mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro B hB
      have fresh : p ∉ B := fun h => hp (mem_powerset.mp hB h)
      rw [sum_insert fresh, prod_insert fresh]
      ring
    rw [sum_powerset_insert hp, big, sum_insert hp, prod_insert hp]
    change M + (l p*w p*Z + w p*M) ≤ (l p*w p + A)*((1+w p)*Z)
    have im : M ≤ A*Z := ih
    have pos : 0 ≤ l p*w p*w p*Z := by positivity [hl p, hw p]
    nlinarith [mul_le_mul_of_nonneg_left im (hw p)]

lemma short_products (S : Finset ℕ) (w l : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) (hl : ∀ p, 0 ≤ l p)
    (L : ℝ) (hL : 0 < L) (small : ∑ p ∈ S, l p*w p ≤ L/2) :
    (∏ p ∈ S, (1+w p))/2 ≤
      ∑ B ∈ S.powerset.filter (fun B => (∑ p ∈ B, l p) ≤ L), ∏ p ∈ B, w p := by
  classical
  let short := S.powerset.filter (fun B => (∑ p ∈ B, l p) ≤ L)
  let tail := S.powerset \ short
  let weight (B : Finset ℕ) := ∏ p ∈ B, w p
  let Z := ∏ p ∈ S, (1+w p)
  have non (B : Finset ℕ) : 0 ≤ weight B := prod_nonneg (fun p _ => hw p)
  have znon : 0 ≤ Z := prod_nonneg fun i _ => by linarith [hw i]
  have total : (∑ B ∈ tail, weight B) + ∑ B ∈ short, weight B = Z := by
    rw [sum_sdiff (filter_subset _ _)]
    exact (prod_one_add S).symm
  have bound : L * ∑ B ∈ tail, weight B ≤ L/2*Z := by
    rw [mul_sum]
    calc
      _ ≤ ∑ B ∈ tail, (∑ p ∈ B, l p)*weight B := by
        apply sum_le_sum
        intro B hB
        obtain ⟨hS, hnot⟩ := mem_sdiff.mp hB
        have too : L ≤ ∑ p ∈ B, l p := by
          by_contra! no
          exact hnot (mem_filter.mpr ⟨hS, no.le⟩)
        exact mul_le_mul_of_nonneg_right too (non B)
      _ ≤ ∑ B ∈ S.powerset, (∑ p ∈ B, l p)*weight B :=
        sum_le_sum_of_subset_of_nonneg sdiff_subset (fun B _ _ =>
          mul_nonneg (sum_nonneg (fun p _ => hl p)) (non B))
      _ ≤ _ := (euler_moment w l hw hl S).trans (mul_le_mul_of_nonneg_right small znon)
  have tailBound : (∑ B ∈ tail, weight B) ≤ Z/2 :=
    (mul_le_mul_iff_of_pos_left hL).mp (by linarith [bound])
  change Z/2 ≤ ∑ B ∈ short, weight B
  linarith


-- Split primes at N^(1/K). Large primes contribute only a constant factor.
lemma split_euler_product (r : ℝ) (hr : 0 ≤ r) (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (wprime : ∀ p : ℕ, p.Prime → w p ≤ r/p) (N : ℕ) (hN : 1 < N) (P : Finset ℕ)
    (pr : ∀ p ∈ P, p.Prime ∧ p ≤ N) :
    ∃ S ⊆ P, (∑ p ∈ S, log (p:ℝ)*w p) ≤ log (N:ℝ)/2 ∧
      (∏ p ∈ P, (1+w p)) ≤ exp (2*r*(4*(r+1)))*(∏ p ∈ S, (1+w p)) := by
  classical
  let K := 4*(r+1)
  let L := log (N:ℝ)
  let A := L/K
  have hK : 0 < K := by dsimp [K]; linarith
  have hL : 0 < L := log_pos (by exact_mod_cast hN)
  have hA : 0 < A := div_pos hL hK
  have hAK : A*K = L := div_mul_cancel₀ _ hK.ne'
  let M := ⌊exp A⌋₊
  have hM : 0 < M := Nat.floor_pos.mpr (one_le_exp hA.le)
  have logM : log (M:ℝ) ≤ A := by
    rw [← log_exp A]
    exact log_le_log (by exact_mod_cast hM) (Nat.floor_le (exp_pos A).le)
  let S := P.filter (fun p => p ≤ M)
  let T := P \ S
  have ssub : S ⊆ P := filter_subset ..
  have tsub : T ⊆ P := sdiff_subset
  have bound (Q : Finset ℕ) (m : ℕ) (hm : 0 < m) (good : ∀ p ∈ Q, p.Prime ∧ p ≤ m) :
      (∑ p ∈ Q, log (p:ℝ)*w p) ≤ r*(2*log (m:ℝ)) := by
    calc
      _ ≤ ∑ p ∈ Q, r*(log (p:ℝ)/p) := by
        apply sum_le_sum
        intro p hp
        have prime := (good p hp).1
        have lg : 0 ≤ log (p:ℝ) := log_nonneg (by exact_mod_cast prime.one_le)
        calc
          _ ≤ log (p:ℝ)*(r/p) := mul_le_mul_of_nonneg_left (wprime p prime) lg
          _ = _ := by ring
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (prime_log_weight m hm Q good) hr
  have small : (∑ p ∈ S, log (p:ℝ)*w p) ≤ L/2 := by
    have bs := bound S M hM (fun p hp => ⟨(pr p (ssub hp)).1, (mem_filter.mp hp).2⟩)
    have ba := mul_le_mul_of_nonneg_left logM hr
    dsimp [K] at hAK
    nlinarith
  have large : (∑ p ∈ T, w p) ≤ 2*r*K := by
    have weighted := bound T N (by omega) (fun p hp => pr p (tsub hp))
    have low : A*(∑ p ∈ T, w p) ≤ ∑ p ∈ T, log (p:ℝ)*w p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      obtain ⟨hP,hS⟩ := mem_sdiff.mp hp
      have gt : M < p := lt_of_not_ge (fun le => hS (mem_filter.mpr ⟨hP,le⟩))
      have gt' : exp A < (p:ℝ) := (Nat.floor_lt (exp_pos A).le).mp gt
      have lg : A ≤ log (p:ℝ) := by rw [← log_exp A]; exact (log_lt_log (exp_pos A) gt').le
      exact mul_le_mul_of_nonneg_right lg (hw p)
    apply (mul_le_mul_iff_of_pos_left hA).mp
    calc
      _ ≤ r*(2*L) := low.trans weighted
      _ = A*(2*r*K) := by rw [← hAK]; ring
  have tail : (∏ p ∈ T, (1+w p)) ≤ exp (2*r*K) := by
    calc
      _ ≤ ∏ p ∈ T, exp (w p) := prod_le_prod (fun p _ => by linarith [hw p])
        (fun p _ => by linarith [add_one_le_exp (w p)])
      _ = exp (∑ p ∈ T, w p) := (exp_sum ..).symm
      _ ≤ _ := exp_le_exp.mpr large
  refine ⟨S,ssub,small,?_⟩
  have mult := prod_sdiff ssub (f:=fun p => 1+w p)
  change (∏ p ∈ T, (1+w p))*(∏ p ∈ S, (1+w p)) = _ at mult
  rw [← mult]
  exact mul_le_mul_of_nonneg_right tail (prod_nonneg (fun p _ => by linarith [hw p]))

lemma short_modulus_estimate : shortModulusEstimate := by
  classical
  intro g hm b _hb
  let r : ℝ := g.natDegree
  let C := 2*r*(4*(r+1))
  let w (p : ℕ) : ℝ := (rootsMod g p:ℝ)/p
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE := exp_pos C
  have hw (p : ℕ) : 0 ≤ w p := by dsimp [w]; positivity
  have wp (p : ℕ) (hp : p.Prime) : w p ≤ r / p := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    dsimp [r]
    exact_mod_cast prime_roots_bound g hm p hp
  refine ⟨1/(2*exp C), by positivity, ?_⟩
  intro N hN
  rcases eq_or_lt_of_le hN with he | hN'
  · subst N
    have hc : 1/(2*exp C) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]; linarith [one_le_exp hC]
    simpa using hc
  let P := (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b)
  have pr : ∀ p ∈ P, p.Prime ∧ p ≤ N := fun p hp =>
    ⟨(mem_filter.mp hp).2.1,(mem_Icc.mp (mem_filter.mp hp).1).2⟩
  obtain ⟨S,sub,small,full⟩ := split_euler_product r hr w hw wp N hN' P pr
  have mass := short_products S w (fun p : ℕ => log (p:ℝ)) hw log_natCast_nonneg (log (N:ℝ))
    (log_pos (by exact_mod_cast hN')) small
  have inject := count_short_subsets g S N b (by omega)
    (fun p hp => (mem_filter.mp (sub hp)).2)
  change (1/(2*exp C))*(∏ p ∈ P, (1+w p)) ≤ _
  calc
    _ ≤ (1/(2*exp C))*(exp C*(∏ p ∈ S, (1+w p))) :=
      mul_le_mul_of_nonneg_left full (by positivity)
    _ = (∏ p ∈ S, (1+w p))/2 := by field_simp
    _ ≤ _ := mass.trans inject

end Sieve

namespace PrimeIdeals

open Finset Polynomial UniqueFactorizationMonoid

open Finset Polynomial UniqueFactorizationMonoid
lemma linear_factor_count {k : Type*} [Field k] [Fintype k] [DecidableEq k] (f : k[X])
    (hf : f ≠ 0) :
    ((normalizedFactors f).toFinset.filter (fun q => q.natDegree = 1)).card =
      (univ.filter (fun x : k => f.eval x = 0)).card := by
  classical
  let R := univ.filter (fun x : k => f.eval x = 0)
  let L := (normalizedFactors f).toFinset.filter (fun q => q.natDegree = 1)
  let q (x : k) : k[X] := X-C x
  have same : R.image q = L := by
    ext a
    constructor
    · intro ha
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      refine mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ?_,natDegree_X_sub_C _⟩
      exact (Polynomial.mem_normalizedFactors_iff hf).mpr
        ⟨irreducible_X_sub_C _,monic_X_sub_C _,dvd_iff_isRoot.mpr (mem_filter.mp hx).2⟩
    · intro ha
      obtain ⟨hfactor,hdeg⟩ := mem_filter.mp ha
      have facts := (Polynomial.mem_normalizedFactors_iff hf).mp (Multiset.mem_toFinset.mp hfactor)
      have eq : q (-(a.coeff 0)) = a := by simpa [q] using (facts.2.1.eq_X_add_C hdeg).symm
      have root : f.IsRoot (-(a.coeff 0)) := dvd_iff_isRoot.mp (show q _ ∣ f by rw [eq]; exact facts.2.2)
      exact mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,root⟩,eq⟩
  have inj : Function.Injective q := fun a b h => C_injective (sub_right_inj.mp h)
  change L.card = R.card
  rw [← same,card_image_of_injective _ inj]


open Ideal NumberField Algebra Polynomial
lemma powerbasis_exponent_pos (K : Type*) [Field K] [NumberField K]
    (B : PowerBasis ℚ K) (θ : 𝓞 K) (gen : B.gen = (θ:K)) :
    0 < RingOfIntegers.exponent θ := by
  have hint : IsIntegral ℤ B.gen := gen ▸ θ.2
  have dint : IsIntegral ℤ (discr ℚ B.basis) := discr_isIntegral ℚ (fun i => by
    rw [B.basis_eq_pow]; exact hint.pow _)
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp dint
  have dn := (discr_isUnit_of_basis ℚ B.basis).ne_zero
  have zn : z ≠ 0 := by intro h; apply dn; rw [← hz,h,map_zero]
  have mem : z ∈ Ideal.under ℤ (conductor ℤ θ) := by
    change (algebraMap ℤ (𝓞 K) z) ∈ conductor ℤ θ
    apply mem_conductor_iff.mpr
    intro t
    have into := discr_mul_isIntegral_mem_adjoin ℚ hint t.2
    rw [gen, adjoin_singleton_eq_range_aeval] at into
    obtain ⟨q,hq⟩ := into
    rw [adjoin_singleton_eq_range_aeval]
    refine ⟨q, NumberField.RingOfIntegers.ext ?_⟩
    have project := Polynomial.aeval_algebraMap_apply K θ q
    change algebraMap (𝓞 K) K (aeval θ q) = algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) z * t)
    rw [← project, map_mul, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq]
    change aeval ((algebraMap (𝓞 K) K) θ) q = discr ℚ B.basis • (t:K) at hq
    rw [hq, ← hz, Algebra.smul_def]
    simp
  by_contra! no
  have h0 : RingOfIntegers.exponent θ = 0 := by omega
  have bot := Ideal.absNorm_eq_zero_iff.mp h0
  rw [bot] at mem
  exact zn (Ideal.mem_bot.mp mem)


lemma choose_field (g : ℤ[X]) (hm : g.Monic) (irr : Irreducible g) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (θ : 𝓞 K),
        minpoly ℤ θ = g ∧ 0 < RingOfIntegers.exponent θ := by
  let F := g.map (algebraMap ℤ ℚ)
  have irF : Irreducible F := hm.irreducible_iff_irreducible_map_fraction_map.mp irr
  let : Fact (Irreducible F) := ⟨irF⟩
  let K := AdjoinRoot F
  let B := AdjoinRoot.powerBasis irF.ne_zero
  let : FiniteDimensional ℚ K := B.finite
  let : NumberField K := ⟨⟩
  have zero : aeval (AdjoinRoot.root F) g = 0 := by
    rw [AdjoinRoot.aeval_eq_of_algebra]
    exact AdjoinRoot.mk_self
  let θ : 𝓞 K := ⟨AdjoinRoot.root F,⟨g,hm,zero⟩⟩
  have gen : B.gen = (θ:K) := AdjoinRoot.powerBasis_gen irF.ne_zero
  refine ⟨K,inferInstance,inferInstance,θ,?_,powerbasis_exponent_pos K B θ gen⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral]
  change minpoly ℚ (AdjoinRoot.root F) = F
  apply (minpoly.eq_of_irreducible_of_monic irF ?_ (hm.map _)).symm
  change aeval (AdjoinRoot.root F) (g.map (algebraMap ℤ ℚ)) = 0
  rw [Polynomial.aeval_map_algebraMap]
  exact zero


open NumberField Ideal IsDedekindDomain
noncomputable abbrev fiber (K : Type*) [Field K] [NumberField K] (p : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)

lemma fiber_spec (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    (fiber K p : Set (Ideal (𝓞 K))) = (Ideal.span {(p:ℤ)}).primesOver (𝓞 K) := by
  let : Fact p.Prime := ⟨hp⟩
  let : (Ideal.span {(p:ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  exact IsDedekindDomain.coe_primesOverFinset (by simp [hp.ne_zero]) _

lemma fiber_count (K : Type*) [Field K] [NumberField K] (θ : 𝓞 K)
    {p : ℕ} (hp : p.Prime) (good : ¬p ∣ RingOfIntegers.exponent θ) :
    ((fiber K p).filter (fun I => I.inertiaDeg ℤ = 1)).card =
      Nat.count (fun r : ℕ => (p:ℤ) ∣ (minpoly ℤ θ).eval (r:ℤ)) p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let G := RingOfIntegers.monicFactorsMod θ p
  let e : ↥(fiber K p) ≃ ↥G := (Equiv.setCongr (fiber_spec K hp)).trans
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod good)
  have eq (i : ↥(fiber K p)) : i.val.inertiaDeg ℤ = (e i).val.natDegree := by
    have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      good (e i).prop
    change ((e.symm (e i)).val).inertiaDeg ℤ = _ at h
    rwa [Equiv.symm_apply_apply] at h
  have bij : ((fiber K p).filter (fun I => I.inertiaDeg ℤ = 1)).card =
      (G.filter (fun q => q.natDegree = 1)).card := by
    apply card_bij (fun i hi => (e ⟨i,(mem_filter.mp hi).1⟩).val)
    · intro i hi
      exact mem_filter.mpr ⟨(e _).prop,(eq ⟨i,(mem_filter.mp hi).1⟩).symm.trans (mem_filter.mp hi).2⟩
    · intro i hi j hj h
      exact congrArg Subtype.val (e.injective (Subtype.ext h))
    · intro q hq
      let a : ↥G := ⟨q,(mem_filter.mp hq).1⟩
      let i := e.symm a
      have hi : i.val.inertiaDeg ℤ = 1 := (eq i).trans (by simpa [i,a] using (mem_filter.mp hq).2)
      exact ⟨i.val,mem_filter.mpr ⟨i.prop,hi⟩,congrArg Subtype.val (e.apply_symm_apply a)⟩
  rw [bij, count_root_ring]
  rw [← Finset.card_filter]
  have non := ((minpoly.monic θ.isIntegral).map (Int.castRingHom (ZMod p))).ne_zero
  simpa only [G,RingOfIntegers.monicFactorsMod,Polynomial.eval_map] using
    linear_factor_count _ non


lemma fiber_info (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    {I : Ideal (𝓞 K)} (h : I ∈ fiber K p) :
    I.IsPrime ∧ I.under ℤ = Ideal.span {(p:ℤ)} ∧ 0 < I.inertiaDeg ℤ ∧
      p^(I.inertiaDeg ℤ) = I.absNorm := by
  have hh : I ∈ (Ideal.span {(p:ℤ)}).primesOver (𝓞 K) := (fiber_spec K hp) ▸ h
  let : I.IsPrime := hh.1
  let : I.LiesOver (Ideal.span {(p:ℤ)}) := hh.2
  exact ⟨hh.1,hh.2.over.symm,I.inertiaDeg_pos ℤ,I.pow_inertiaDeg p⟩

lemma fiber_card_le (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    (fiber K p).card ≤ Module.finrank ℤ (𝓞 K) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : (Ideal.span {(p:ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let V := (Ideal.span {(p:ℤ)}).primesOver (𝓞 K)
  let e : ↥(fiber K p) ≃ ↥V := Equiv.setCongr (fiber_spec K hp)
  have id := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p:ℤ)}) (𝓞 K)
  rw [← id, ← Fintype.card_coe, Fintype.card_congr e, ← @Finset.card_univ (↥V) _, Finset.card_eq_sum_ones]
  apply sum_le_sum
  intro i _
  let : i.val.IsPrime := i.prop.1
  exact Nat.mul_pos (i.val.ramificationIdx_pos ℤ) (i.val.inertiaDeg_pos ℤ)

lemma belongs_to_fiber (K : Type*) [Field K] [NumberField K] {Q I : Ideal (𝓞 K)}
    (hQ : Prime Q) (hI : I ≠ 0) (dvd : Q ∣ I) :
    ∃ p : ℕ, p.Prime ∧ p ≤ I.absNorm ∧ Q ∈ fiber K p := by
  let : Q.IsPrime := Ideal.isPrime_of_prime hQ
  let m : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ.ne_zero
  obtain ⟨p,n,hn,mem,hp,eq⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
  let : Fact p.Prime := ⟨hp⟩
  have maxp := Int.ideal_span_isMaximal_of_prime p
  have under : Ideal.span {(p:ℤ)} = Q.under ℤ := maxp.eq_of_le
    (inferInstance : (Q.under ℤ).IsPrime).ne_top (by rw [Ideal.span_singleton_le_iff_mem]; change algebraMap ℤ (𝓞 K) (p:ℤ) ∈ Q; simpa using mem)
  have pd : p ∣ Q.absNorm := eq ▸ dvd_pow_self p (by omega)
  have pos : 0 < I.absNorm := Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨p,hp,Nat.le_of_dvd pos (pd.trans (map_dvd Ideal.absNorm dvd)),?_⟩
  have hmem : Q ∈ (Ideal.span {(p:ℤ)}).primesOver (𝓞 K) := ⟨inferInstance,⟨under⟩⟩
  change Q ∈ (fiber K p : Set (Ideal (𝓞 K)))
  rw [fiber_spec K hp]
  exact hmem

open Finset Real Filter Ideal NumberField Topology

lemma weighted_prefix_lower (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (density : ∀ n : ℕ, c*n ≤ ∑ j ∈ range n, a j) (n : ℕ) :
    c*log ((n:ℝ)+1) ≤ ∑ j ∈ range n, a j/((j:ℝ)+1) := by
  let A (n : ℕ) := ∑ j ∈ range n, a j
  have strong (k : ℕ) : (A k-c*k)/((k:ℝ)+1) ≤
      (∑ j ∈ range k, a j/((j:ℝ)+1)) - c*(harmonic k:ℝ) := by
    induction k with
    | zero => simp [A]
    | succ k ih =>
      have step : A (k+1) = A k + a k := sum_range_succ ..
      have h1 : 0 < (k:ℝ)+1 := by positivity
      have h2 : 0 < ((k+1:ℕ):ℝ)+1 := by positivity
      have mono : (A (k+1)-c*(k+1:ℕ))/(((k+1:ℕ):ℝ)+1) ≤
          (A (k+1)-c*(k+1:ℕ))/((k:ℝ)+1) := by
        apply div_le_div_of_nonneg_left (sub_nonneg.mpr (density (k+1))) h1
        push_cast
        linarith
      calc
        _ ≤ _ := mono
        _ = (A k-c*k)/((k:ℝ)+1) + a k/((k:ℝ)+1) - c/((k:ℝ)+1) := by
          rw [step]; push_cast; field_simp; ring
        _ ≤ _ := by
          rw [sum_range_succ, harmonic_succ]
          push_cast
          rw [mul_add, ← div_eq_mul_inv]
          linarith
  have hn : 0 ≤ (A n-c*n)/((n:ℝ)+1) := div_nonneg (sub_nonneg.mpr (density n)) (by positivity)
  have hlog := mul_le_mul_of_nonneg_left (log_add_one_le_harmonic n) hc
  push_cast at hlog
  linarith [strong n]

noncomputable def idealCount (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

lemma ideal_harmonic_lower (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*log ((n:ℝ)+1) ≤
      ∑ j ∈ range n, (idealCount K (j+1):ℝ)/((j:ℝ)+1) := by
  classical
  let a (j : ℕ) : ℝ := idealCount K (j+1)
  have shift (n : ℕ) : (∑ j ∈ range n, a j) = ∑ k ∈ Icc 1 n, (idealCount K k:ℝ) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]
  have lim : Tendsto (fun n : ℕ => (∑ j ∈ range n, a j)/(n:ℝ)) atTop
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
    apply ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    intro n
    rw [shift]
    simp only [Function.comp_apply, Nat.cast_le, idealCount, ← Nat.cast_sum]
    congr 2
    -- Count by norm fibers, as in Mathlib's proof of the class number formula.
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  let R := NumberField.dedekindZeta_residue K
  have hR : 0 < R := NumberField.dedekindZeta_residue_pos K
  have ev := lim.eventually_const_lt (show R/2 < R by linarith)
  obtain ⟨M,hM⟩ := eventually_atTop.1 ev
  let c := min (R/2) (1/((M:ℝ)+1))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c,hc,fun n => weighted_prefix_lower a c hc.le (fun m => ?_) n⟩
  rcases m with _ | m
  · simp
  have hm : (0:ℝ)<((m+1:ℕ):ℝ) := by positivity
  by_cases h : M ≤ m+1
  · have hh := (lt_div_iff₀ hm).mp (hM (m+1) h)
    exact (mul_le_mul_of_nonneg_right (min_le_left ..) hm.le).trans hh.le
  · have one : a 0 = 1 := by simp [a, idealCount, Ideal.absNorm_eq_one_iff]
    have atleast : 1 ≤ ∑ j ∈ range (m+1), a j := by
      rw [← one]
      exact single_le_sum (fun j _ => by dsimp [a]; positivity) (mem_range.mpr (Nat.succ_pos _))
    apply le_trans _ atleast
    calc
      _ ≤ (1/((M:ℝ)+1))*((m+1:ℕ):ℝ) := mul_le_mul_of_nonneg_right (min_le_right ..) hm.le
      _ ≤ 1 := by
        have lb : ((m+1:ℕ):ℝ) ≤ (M:ℝ)+1 := by exact_mod_cast (by omega : m+1 ≤ M+1)
        rw [one_div, inv_mul_eq_div, div_le_iff₀ (by positivity)]
        linarith


open Finset Real
set_option maxHeartbeats 1000000 in
lemma finite_euler_majorant {ι κ : Type*} [Fintype ι] (S : Finset κ)
    (e : κ → ι → ℕ) (inj : Set.InjOn e (S : Set κ)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (lt : ∀ i, w i < 1) :
    (∑ a ∈ S, ∏ i, (w i)^(e a i)) ≤ ∏ i, (1-w i)⁻¹ := by
  classical
  let M := S.sup (fun a => univ.sup (e a))
  have cap (a : κ) (ha : a ∈ S) (i : ι) : e a i < M+1 :=
    Nat.lt_succ_of_le ((le_sup (s:=univ) (f:=e a) (mem_univ i)).trans (le_sup (f:=fun a => univ.sup (e a)) ha))
  let Z (a : κ) : ι → Fin (M+1) := fun i => ⟨min (e a i) M, by omega⟩
  have val (a : κ) (ha : a ∈ S) (i : ι) : (Z a i).val = e a i :=
    min_eq_left (Nat.le_of_lt_succ (cap a ha i))
  have zj : Set.InjOn Z (S : Set κ) := by
    intro a ha b hb h
    apply inj ha hb
    funext i
    rw [← val a ha, ← val b hb, h]
  let F (v : ι → Fin (M+1)) := ∏ i, (w i)^((v i).val)
  have localbound (i : ι) : (∑ j : Fin (M+1), (w i)^j.val) ≤ (1-w i)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range]
    have hpos : 0 < 1-w i := by linarith [lt i]
    rw [← one_div, le_div_iff₀ hpos]
    have eq := geom_sum_mul (w i) (M+1)
    nlinarith [pow_nonneg (hw i) (M+1)]
  calc
    _ = ∑ a ∈ S, F (Z a) := by
      apply sum_congr rfl
      intro a ha
      simp only [F,val a ha]
    _ = ∑ v ∈ S.image Z, F v := (sum_image zj).symm
    _ ≤ ∑ v : ι → Fin (M+1), F v := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun v _ _ => prod_nonneg (fun i _ => pow_nonneg (hw i) _))
    _ = ∏ i, ∑ j : Fin (M+1), (w i)^j.val := (Fintype.prod_sum (fun (i : ι) (j : Fin (M+1)) => (w i)^j.val)).symm
    _ ≤ _ := prod_le_prod (fun i _ => sum_nonneg fun j _ => pow_nonneg (hw i) _) (fun i _ => localbound i)


-- Every ideal of norm at most N is a product of prime ideals over p ≤ N.
lemma ideal_euler_upper (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    (∑ j ∈ range N, (idealCount K (j+1):ℝ)/((j:ℝ)+1)) ≤
      ∏ p ∈ (Icc 2 N).filter Nat.Prime, ∏ I ∈ fiber K p, (1-((p:ℝ)⁻¹)^(I.inertiaDeg ℤ))⁻¹ := by
  classical
  let A := (Icc 2 N).filter Nat.Prime
  let U := A.biUnion (fiber K)
  let T (j : ℕ) : Finset (Ideal (𝓞 K)) := (Ideal.finite_setOfPred_absNorm_eq (j+1)).toFinset
  let S := (range N).biUnion T
  let norm (I : Ideal (𝓞 K)) : ℝ := I.absNorm
  have atn (j : ℕ) (I : Ideal (𝓞 K)) : I ∈ T j ↔ I.absNorm = j+1 := Set.Finite.mem_toFinset _
  have norm_at (j : ℕ) (I : Ideal (𝓞 K)) (h : I ∈ T j) : norm I = (j:ℝ)+1 := by
    dsimp [norm]; exact_mod_cast (atn j I).mp h
  have sdisj : (range N : Set ℕ).PairwiseDisjoint T := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro I hi hj
    exact ne (Nat.succ.inj (((atn i I).mp hi).symm.trans ((atn j I).mp hj)))
  have mass : (∑ j ∈ range N, (idealCount K (j+1):ℝ)/((j:ℝ)+1)) =
      ∑ I ∈ S, (norm I)⁻¹ := by
    rw [sum_biUnion sdisj]
    apply sum_congr rfl
    intro j _
    have cnt : idealCount K (j+1) = (T j).card :=
      Nat.card_eq_card_finite_toFinset (Ideal.finite_setOfPred_absNorm_eq (j+1))
    rw [cnt]
    simp_rw [sum_congr rfl (fun I (hi : I ∈ T j) => congrArg Inv.inv (norm_at j I hi))]
    simp [div_eq_mul_inv]
  have ns (I : Ideal (𝓞 K)) (h : I ∈ S) : I ≠ 0 ∧ I.absNorm ≤ N := by
    obtain ⟨j,hj,hi⟩ := mem_biUnion.mp h
    have eq := (atn j I).mp hi
    have pos : 0 < I.absNorm := by omega
    exact ⟨fun hz => (Nat.ne_of_gt pos) (Ideal.absNorm_eq_zero_iff.mpr hz),eq ▸ mem_range.mp hj⟩
  let e (I : Ideal (𝓞 K)) (q : ↥U) : ℕ := (normalizedFactors I).count q.val
  have repr (I : Ideal (𝓞 K)) (h : I ∈ S) : (∏ q : ↥U, q.val^(e I q)) = I := by
    have hin : (normalizedFactors I).toFinset ⊆ U := by
      intro q hq
      have mem := Multiset.mem_toFinset.mp hq
      obtain ⟨p,hp,hle,inc⟩ := belongs_to_fiber K (prime_of_normalized_factor q mem) (ns I h).1
        (dvd_of_mem_normalizedFactors mem)
      exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,hle.trans (ns I h).2⟩,hp⟩,inc⟩
    change (∏ q : ↥U, q.val^((normalizedFactors I).count q.val)) = I
    rw [prod_coe_sort U (fun q => q^((normalizedFactors I).count q)), ← prod_multiset_count_of_subset _ _ hin]
    exact associated_iff_eq.mp (prod_normalizedFactors (ns I h).1)
  have inj : Set.InjOn e (S : Set (Ideal (𝓞 K))) := by
    intro I hI J hJ eq
    rw [← repr I hI, ← repr J hJ, eq]
  have wgt (q : ↥U) : 1 < norm q.val := by
    obtain ⟨p,hp,hq⟩ := mem_biUnion.mp q.prop
    have prime := (mem_filter.mp hp).2
    have inf := fiber_info K prime hq
    change (1:ℝ) < (q.val.absNorm:ℝ)
    exact_mod_cast (inf.2.2.2 ▸ (one_lt_pow₀ prime.one_lt inf.2.2.1.ne'))
  have vals (I : Ideal (𝓞 K)) (hi : I ∈ S) :
      (norm I)⁻¹ = ∏ q : ↥U, ((norm q.val)⁻¹)^(e I q) := by
    have eq := congrArg Ideal.absNorm (repr I hi)
    simp only [map_prod,map_pow] at eq
    dsimp [norm]
    rw [← eq, Nat.cast_prod, ← prod_inv_distrib]
    apply prod_congr rfl
    intro i _
    simp
  have disj : (A : Set ℕ).PairwiseDisjoint (fiber K) := by
    intro p hp q hq ne
    apply Finset.disjoint_left.mpr
    intro I hP hQ
    have E := (fiber_info K (mem_filter.mp hp).2 hP).2.1.symm.trans
      (fiber_info K (mem_filter.mp hq).2 hQ).2.1
    exact ne (by simpa using congrArg Ideal.absNorm E)
  calc
    _ = ∑ I ∈ S, ∏ q : ↥U, ((norm q.val)⁻¹)^(e I q) := mass.trans (sum_congr rfl vals)
    _ ≤ ∏ q : ↥U, (1-(norm q.val)⁻¹)⁻¹ := finite_euler_majorant S e inj _
      (fun q => inv_nonneg.mpr (zero_le_one.trans (wgt q).le))
      (fun q => inv_lt_one_of_one_lt₀ (wgt q))
    _ = ∏ p ∈ A, ∏ I ∈ fiber K p, (1-(norm I)⁻¹)⁻¹ := by rw [prod_coe_sort U (fun q => (1-(norm q)⁻¹)⁻¹),prod_biUnion disj]
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      apply prod_congr rfl
      intro I hI
      simp only [norm, ← (fiber_info K (mem_filter.mp hp).2 hI).2.2.2, Nat.cast_pow,inv_pow]


open Finset Real

-- Compare a complete local prime-ideal factor with its degree-one term.
lemma local_euler_compare {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, 0 < f i) (x : ℝ) (hx : 0 ≤ x) (hh : x ≤ 1/2) :
    (∏ i ∈ S, (1-x^(f i))⁻¹) ≤
      (1+((S.filter (fun i => f i = 1)).card:ℝ)*x)*exp ((2*(S.card:ℝ)+(S.card:ℝ)^2)*x^2) := by
  classical
  let d := (S.card:ℝ)
  let r := ((S.filter (fun i => f i = 1)).card:ℝ)
  let v (i : ι) := if f i = 1 then x else 0
  have hx1 : x ≤ 1 := by linarith
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hrd : r ≤ d := by dsimp [r,d]; exact_mod_cast (card_filter_le S (fun i => f i = 1))
  have localbound (i : ι) (hi : i ∈ S) : (1-x^(f i))⁻¹ ≤ exp (v i + 2*x^2) := by
    have hp : x^(f i) ≤ x := by
      simpa using pow_le_pow_of_le_one hx hx1 (hf i hi)
    have pos : 0 < 1-x^(f i) := by linarith
    apply le_trans _ (add_one_le_exp (v i + 2*x^2))
    rw [inv_le_iff_one_le_mul₀ pos]
    by_cases h : f i = 1
    · simp only [v,h,if_true,pow_one]
      nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*x by linarith)]
    · have h2 : 2 ≤ f i := by have := hf i hi; omega
      have hs := pow_le_pow_of_le_one hx hx1 h2
      simp only [v,h,if_false,zero_add]
      nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*x^(f i) by linarith)]
  have sumv : (∑ i ∈ S, v i) = r*x := by
    simp only [v,r,← sum_filter,sum_const,nsmul_eq_mul]
  have ry : 0 ≤ r*x := mul_nonneg hr hx
  have corr : r*x-(r*x)^2 ≤ log (1+r*x) := by
    apply le_trans _ (one_sub_inv_le_log_of_pos (by linarith))
    have hpos : 0<1+r*x := by linarith
    have id : (1-(1+r*x)⁻¹)*(1+r*x) = r*x := by field_simp; ring
    apply (mul_le_mul_iff_of_pos_right hpos).mp
    rw [id]
    nlinarith [pow_nonneg ry 3]
  have rd2 : (r*x)^2 ≤ d^2*x^2 := by
    rw [mul_pow]
    gcongr
  calc
    _ ≤ ∏ i ∈ S, exp (v i + 2*x^2) := prod_le_prod (fun i hi => by
      have : x^(f i) ≤ x := by simpa using pow_le_pow_of_le_one hx hx1 (hf i hi)
      exact inv_nonneg.mpr (by linarith)) localbound
    _ = exp (r*x+d*(2*x^2)) := by rw [← exp_sum, sum_add_distrib,sumv,sum_const,nsmul_eq_mul]
    _ ≤ exp (log (1+r*x)+(2*d+d^2)*x^2) := exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [exp_add, exp_log (by linarith : 0<1+r*x)]


open Ideal NumberField Finset Real
lemma euler_product_correction {ι : Type*} (A : Finset ℕ) (pr : ∀ p ∈ A, p.Prime)
    (S : ℕ → Finset ι) (f : ι → ℕ) (pos : ∀ p ∈ A, ∀ i ∈ S p, 0 < f i)
    (D : ℕ) (bound : ∀ p ∈ A, (S p).card ≤ D) :
    (∏ p ∈ A, ∏ i ∈ S p, (1-((p:ℝ)⁻¹)^(f i))⁻¹) ≤
      exp ((2*(D:ℝ)+(D:ℝ)^2) * ∑' k : ℕ, ((k:ℝ)^2)⁻¹) *
        ∏ p ∈ A, (1 + (((S p).filter (fun i => f i = 1)).card:ℝ)/p) := by
  classical
  let C := 2*(D:ℝ)+(D:ℝ)^2
  let W (p : ℕ) := 1 + (((S p).filter (fun i => f i = 1)).card:ℝ)/p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have point (p : ℕ) (hp : p ∈ A) : (∏ i ∈ S p, (1-((p:ℝ)⁻¹)^(f i))⁻¹) ≤
      W p * exp (C*((p:ℝ)^2)⁻¹) := by
    have hpn : (0:ℝ)<p := by exact_mod_cast (pr p hp).pos
    have half : (p:ℝ)⁻¹ ≤ 1/2 := by
      rw [← one_div, div_le_div_iff₀ hpn (by norm_num : (0:ℝ)<2)]
      have : (2:ℝ)≤p := by exact_mod_cast (pr p hp).two_le
      linarith
    have first := local_euler_compare (S p) f (pos p hp) (p:ℝ)⁻¹ (by positivity) half
    rw [← div_eq_mul_inv, inv_pow] at first
    apply first.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc : ((S p).card:ℝ) ≤ D := by exact_mod_cast bound p hp
    dsimp [C]
    gcongr
  have nonneg (p : ℕ) (hp : p ∈ A) : 0 ≤ ∏ i ∈ S p, (1-((p:ℝ)⁻¹)^(f i))⁻¹ := by
    apply prod_nonneg
    intro i hi
    have h1 : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (pr p hp).one_le)
    exact inv_nonneg.mpr (sub_nonneg.mpr (pow_le_one₀ (by positivity) h1))
  have sumsq : (∑ p ∈ A, ((p:ℝ)^2)⁻¹) ≤ ∑' k : ℕ, ((k:ℝ)^2)⁻¹ :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).sum_le_tsum _ (fun _ _ => by positivity)
  calc
    _ ≤ ∏ p ∈ A, W p*exp (C*((p:ℝ)^2)⁻¹) := prod_le_prod nonneg point
    _ = (∏ p ∈ A, W p)*exp (C*∑ p ∈ A, ((p:ℝ)^2)⁻¹) := by
      rw [prod_mul_distrib, ← exp_sum, mul_sum]
    _ ≤ _ := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right (exp_le_exp.mpr (mul_le_mul_of_nonneg_left sumsq hC))
      exact prod_nonneg (fun p _ => by dsimp [W]; positivity)


open Finset Real
lemma omit_bad_primes (N b t D : ℕ) (hb : 0 < b) (ht : 0 < t)
    (a r : ℕ → ℕ) (bound : ∀ p : ℕ, p.Prime → a p ≤ D)
    (good : ∀ p : ℕ, p.Prime → ¬p ∣ t → a p = r p) :
    (∏ p ∈ (Icc 2 N).filter Nat.Prime, (1+(a p:ℝ)/p)) ≤
      (1+(D:ℝ))^((b*t).primeFactors.card) *
        ∏ p ∈ (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b), (1+(r p:ℝ)/p) := by
  classical
  let A := (Icc 2 N).filter Nat.Prime
  let B := A.filter (fun p => p ∣ b*t)
  let G := A \ B
  let T := (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b)
  have sub : B ⊆ A := filter_subset ..
  have subB : B ⊆ (b*t).primeFactors := by
    intro p hp
    obtain ⟨hA,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hA).2,hd,(Nat.mul_pos hb ht).ne'⟩
  have hpG {p : ℕ} (hp : p ∈ G) : p ∈ T ∧ a p = r p := by
    obtain ⟨hA,hB⟩ := mem_sdiff.mp hp
    obtain ⟨hN,prime⟩ := mem_filter.mp hA
    have hd : ¬ p ∣ b*t := fun h => hB (mem_filter.mpr ⟨hA,h⟩)
    have h1 : ¬p ∣ b := fun h => hd (dvd_mul_of_dvd_left h t)
    have h2 : ¬p ∣ t := fun h => hd (dvd_mul_of_dvd_right h b)
    exact ⟨mem_filter.mpr ⟨hN,prime,prime.coprime_iff_not_dvd.mpr h1⟩,good p prime h2⟩
  have bad : (∏ p ∈ B, (1+(a p:ℝ)/p)) ≤ (1+(D:ℝ))^((b*t).primeFactors.card) := by
    calc
      _ ≤ ∏ _p ∈ B, (1+(D:ℝ)) := by
        apply prod_le_prod (fun p _ => by positivity)
        intro p hp
        have prime := (mem_filter.mp (sub hp)).2
        have hp1 : (1:ℝ) ≤ p := by exact_mod_cast prime.one_le
        have leD : (a p:ℝ) ≤ D := by exact_mod_cast bound p prime
        linarith [div_le_self (Nat.cast_nonneg (a p)) hp1]
      _ ≤ _ := by
        rw [prod_const]
        exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) D]) (card_le_card subB)
  have clean : (∏ p ∈ G, (1+(a p:ℝ)/p)) ≤ ∏ p ∈ T, (1+(r p:ℝ)/p) := calc
    _ = ∏ p ∈ G, (1+(r p:ℝ)/p) := prod_congr rfl (fun p hp => by rw [(hpG hp).2])
    _ ≤ _ := prod_le_prod_of_subset_of_one_le (fun _ h => (hpG h).1)
      (fun p _ => by positivity) (fun p _ _ => le_add_of_nonneg_right (by positivity))
  have mult := prod_sdiff sub (f:=fun p => 1+(a p:ℝ)/p)
  change (∏ p ∈ G, (1+(a p:ℝ)/p))*(∏ p ∈ B, (1+(a p:ℝ)/p)) = _ at mult
  rw [← mult,mul_comm]
  exact mul_le_mul bad clean (prod_nonneg (fun p _ => by positivity)) (by positivity)


lemma prime_roots_mertens : primeRootEstimate := by
  classical
  intro g hm irr _degree b hb
  obtain ⟨K,field,nf,θ,hg,ht⟩ := choose_field g hm irr
  let D := Module.finrank ℤ (𝓞 K)
  let E := exp ((2*(D:ℝ)+(D:ℝ)^2) * ∑' k : ℕ, ((k:ℝ)^2)⁻¹)
  let B := (1+(D:ℝ))^((b*RingOfIntegers.exponent θ).primeFactors.card)
  let a (p : ℕ) := ((fiber K p).filter (fun I => I.inertiaDeg ℤ = 1)).card
  let r (p : ℕ) := Nat.count (fun k : ℕ => (p:ℤ) ∣ g.eval (k:ℤ)) p
  have hd : ∀ p : ℕ, p.Prime → a p ≤ D := fun p hp => (card_filter_le ..).trans (fiber_card_le K hp)
  have eq (p : ℕ) (hp : p.Prime) (nd : ¬p ∣ RingOfIntegers.exponent θ) : a p = r p := by
    simpa only [a,r,← hg] using fiber_count K θ hp nd
  obtain ⟨c,hc,lb⟩ := ideal_harmonic_lower K
  have posE : 0 < E := exp_pos _
  have posB : 0 < B := by dsimp [B]; positivity
  refine ⟨c/(E*B),by positivity,?_⟩
  intro N _hN
  let A := (Icc 2 N).filter Nat.Prime
  let T := (Icc 2 N).filter (fun p : ℕ => p.Prime ∧ p.Coprime b)
  let Z := ∏ p ∈ T, (1+(r p:ℝ)/p)
  have bound := euler_product_correction A (fun p hp => (mem_filter.mp hp).2) (fiber K)
    (fun I => I.inertiaDeg ℤ) (fun p hp I hI => (fiber_info K (mem_filter.mp hp).2 hI).2.2.1)
    D (fun p hp => fiber_card_le K (mem_filter.mp hp).2)
  have final : c*log ((N:ℝ)+1) ≤ E*B*Z := calc
    _ ≤ _ := lb N
    _ ≤ _ := ideal_euler_upper K N
    _ ≤ E * (∏ p ∈ A, (1+(a p:ℝ)/p)) := bound
    _ ≤ E*(B*Z) := mul_le_mul_of_nonneg_left (omit_bad_primes N b _ D hb ht a r hd eq) posE.le
    _ = _ := by ring
  change (c/(E*B))*log ((N:ℝ)+1) ≤ Z
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos posE posB)]
  linarith only [final,mul_comm (E*B) Z]

end PrimeIdeals

end OMA.Erdos975Lower

theorem OMA.solution : type_of% @Erdos975.erdos_975.variants.lower_bound := by
  exact Erdos975Lower.lower_bound_of_estimates Erdos975Lower.PrimeIdeals.prime_roots_mertens
    Erdos975Lower.Sieve.short_modulus_estimate
