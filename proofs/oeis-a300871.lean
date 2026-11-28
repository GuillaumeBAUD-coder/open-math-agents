import OMAStatements.S_oeis_a300871
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- Credit: @HBreitkreutz
namespace OMA.A300871Proof

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The Euler derivative multiplies the coefficient in degree n by n. -/
noncomputable def euler (f : PowerSeries R) : PowerSeries R :=
  X * derivative R f

lemma euler_coeff (f : PowerSeries R) (n : ℕ) :
    coeff n (euler f) = (n : R) * coeff n f := by
  cases n with
  | zero => simp [euler, coeff_zero_X_mul]
  | succ n =>
    rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]
    ring

lemma euler_mul (f g : PowerSeries R) :
    euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, Derivation.leibniz, smul_eq_mul]
  ring

noncomputable def exponential (g : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  subst (C (n : ℚ) * g) (PowerSeries.exp ℚ)

lemma exponential_zero (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    coeff 0 (exponential g n) = 1 := by
  let t := C (n : ℚ) * g
  have ht : constantCoeff t = 0 := by simp [t, hg]
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero ht
  have h1 : subst t (1 : PowerSeries ℚ) = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have he : constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by simp [constantCoeff_exp]
  have h := constantCoeff_subst_eq_zero (a := t) ht _ he
  change constantCoeff (subst t (PowerSeries.exp ℚ - 1)) = 0 at h
  rw [subst_sub hs, h1, map_sub, map_one, sub_eq_zero] at h
  change coeff 0 (subst t (PowerSeries.exp ℚ)) = 1
  simpa only [coeff_zero_eq_constantCoeff] using h

lemma euler_exponential (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    euler (exponential g n) = C (n : ℚ) * (euler g * exponential g n) := by
  have ht : constantCoeff (C (n : ℚ) * g) = 0 := by simp [hg]
  have hs : HasSubst (C (n : ℚ) * g) := HasSubst.of_constantCoeff_zero ht
  unfold euler exponential
  rw [derivative_subst hs, derivative_exp, Derivation.leibniz, derivative_C]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

lemma first_product_coeff {n : ℕ} (f e : PowerSeries ℚ)
    (hf : ∀ i < n, coeff i f = 0) (he : coeff 0 e = 1) :
    coeff n (f * e) = coeff n f := by
  rw [coeff_mul, Finset.sum_eq_single (n, 0)]
  · simp [he]
  · rintro ⟨i, j⟩ hij hp
    have heq : i + j = n := by simpa using hij
    have hi : i < n := by
      by_contra! hh
      exact hp (Prod.ext (by dsimp; omega) (by dsimp; omega))
    simp [hf i hi]
  · simp

/-- A unit series in each degree gives a triangular test for a series to vanish. -/
lemma diagonal_vanish (f : PowerSeries ℚ) (e : ℕ → PowerSeries ℚ)
    (he : ∀ n, coeff 0 (e n) = 1) (hf : ∀ n, coeff n (f * e n) = 0) :
    f = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih => exact (first_product_coeff f (e n) ih (he n)).symm.trans (hf n)



/-- A triangular map with unit diagonal can be inverted one coefficient at a time. -/
noncomputable def restore (E : ℕ → PowerSeries ℚ) (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  b n - ∑ j : Fin n, restore E b j.val * coeff (n - j.val) (E n)
termination_by n
decreasing_by exact j.isLt

lemma restore_spec (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    (b : ℕ → ℚ) (n : ℕ) :
    coeff n ((mk (restore E b) : PowerSeries ℚ) * E n) = b n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (mk (restore E b) : PowerSeries ℚ) * coeff j (E n)),
    Finset.sum_range_succ]
  simp only [coeff_mk, Nat.sub_self, hE, mul_one]
  rw [restore.eq_1 E b n, Fin.sum_univ_eq_sum_range
    (fun j => restore E b j * coeff (n - j) (E n)) n]
  ring

noncomputable def transfer (E : ℕ → PowerSeries ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  mk (restore E fun n => (n : ℚ) * coeff n (f * E n))

lemma transfer_spec (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (transfer E f * E n) = (n : ℚ) * coeff n (f * E n) :=
  restore_spec E hE _ n

lemma diagonal_inj (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    {f g : PowerSeries ℚ} (h : ∀ n, coeff n (f * E n) = coeff n (g * E n)) :
    f = g := by
  apply sub_eq_zero.mp
  apply diagonal_vanish _ E hE
  intro n
  simp only [sub_mul, map_sub, h, sub_self]

noncomputable abbrev family (g : PowerSeries ℚ) (n : ℕ) := exponential g (n * (n+1))

lemma family_derivative (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    euler (family g n) = C (((n : ℚ) * ((n : ℚ)+1))) * (euler g * family g n) := by
  unfold family
  rw [euler_exponential g hg, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

lemma transfer_recursion (g f : PowerSeries ℚ) (hg : constantCoeff g = 0) :
    transfer (family g) f =
      euler f + (transfer (family g) (transfer (family g) (f * euler g)) +
        transfer (family g) (f * euler g)) := by
  have hE (n : ℕ) := exponential_zero g hg (n * (n+1))
  apply diagonal_inj (family g) hE
  intro n
  simp only [add_mul, map_add, transfer_spec _ hE]
  have h := euler_coeff (f * family g n) n
  rw [euler_mul, map_add, family_derivative g hg,
    show f * (C (((n : ℚ) * ((n : ℚ)+1))) * (euler g * family g n)) =
      C (((n : ℚ) * ((n : ℚ)+1))) * ((f * euler g) * family g n) by ring, coeff_C_mul] at h
  linear_combination -h

lemma transfer_source (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hsource : ∀ n : ℕ, 0 < n → coeff n (family g n) =
      ((n : ℚ) * ((n : ℚ)+1)) * coeff (n - 1) (family g n)) :
    transfer (family g) X = euler g := by
  have hE (n : ℕ) := exponential_zero g hg (n * (n+1))
  apply diagonal_inj (family g) hE
  intro n
  rw [transfer_spec _ hE]
  cases n with
  | zero => simp [euler, coeff_zero_eq_constantCoeff]
  | succ k =>
    rw [coeff_succ_X_mul]
    have h := euler_coeff (family g (k+1)) (k+1)
    rw [family_derivative g hg, coeff_C_mul, hsource (k+1) (by omega),
      Nat.add_sub_cancel] at h
    have hn : (((k+1 : ℕ) : ℚ) * (((k+1 : ℕ) : ℚ)+1)) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    linear_combination -h

/-- Coefficients below a given degree vanish. -/
def vanishes (f : PowerSeries ℚ) (k : ℕ) : Prop := ∀ i < k, coeff i f = 0

lemma transfer_vanishes (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    {f : PowerSeries ℚ} {k : ℕ} (hf : vanishes f k) : vanishes (transfer E f) k := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have prev (j : ℕ) (hj : j < i) : coeff j (transfer E f) = 0 := ih j hj (by omega)
    rw [← first_product_coeff _ (E i) prev (hE i), transfer_spec _ hE,
      first_product_coeff f (E i) (fun j hj => hf j (by omega)) (hE i), hf i hi, mul_zero]

lemma vanishes_mul_euler {f g : PowerSeries ℚ} {k : ℕ} (hf : vanishes f k) :
    vanishes (f * euler g) (k + 1) := by
  intro i hi
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a,b⟩ hab
  have hs : a+b=i := by simpa using hab
  change coeff a f * coeff b (euler g) = 0
  by_cases hz : b = 0
  · simp [hz, euler_coeff]
  · rw [hf a (by omega), zero_mul]

/-- Integrality through a finite order. -/
def integralTo (f : PowerSeries ℚ) (N : ℕ) : Prop :=
  ∀ i ≤ N, ∃ a : ℤ, coeff i f = (a : ℚ)

lemma integral_sum {α : Type*} (s : Finset α) (v : α → ℚ)
    (h : ∀ a ∈ s, ∃ b : ℤ, v a = (b : ℚ)) :
    ∃ b : ℤ, ∑ a ∈ s, v a = (b : ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨c, hc⟩ := h a (by simp)
    obtain ⟨b, hb⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    exact ⟨c+b, by rw [Finset.sum_insert ha, hc, hb, Int.cast_add]⟩

lemma integral_mul_euler {f g : PowerSeries ℚ} {N : ℕ}
    (hg : ∀ j < N, ∃ b : ℤ, coeff j g = (b : ℚ))
    (f0 : coeff 0 f = 0) (hf : integralTo f N) :
    integralTo (f * euler g) N := by
  intro i hi
  rw [coeff_mul]
  apply integral_sum
  rintro ⟨a,b⟩ hab
  have hs : a + b = i := by simpa using hab
  change ∃ z : ℤ, coeff a f * coeff b (euler g) = (z : ℚ)
  by_cases h : a = 0
  · exact ⟨0, by simp [h, f0]⟩
  · obtain ⟨u, hu⟩ := hf a (by omega)
    obtain ⟨v, hv⟩ := hg b (by omega)
    exact ⟨u*((b:ℤ)*v), by rw [euler_coeff, hu, hv]; push_cast; rfl⟩

/-- Starting one degree higher at each application makes the recursion finite.
The correction to the Euler derivative in degree i is a multiple of i times i+1. -/
lemma transfer_congruence (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (N : ℕ)
    (prefixInt : ∀ j < N, ∃ b : ℤ, coeff j g = (b : ℚ))
    (k : ℕ) (hk : 0 < k) (f : PowerSeries ℚ) (hf : vanishes f k)
    (hiF : integralTo f N) (i : ℕ) (hi : i ≤ N) :
    ∃ z : ℤ, coeff i (transfer (family g) f) =
      (i : ℚ) * coeff i f + ((i : ℚ)*((i : ℚ)+1)) * (z : ℚ) := by
  have hE (j : ℕ) := exponential_zero g hg (j * (j+1))
  suffices aux : ∀ d k : ℕ, N < k+d → 0 < k →
      ∀ f : PowerSeries ℚ, vanishes f k → integralTo f N →
      ∀ i ≤ N, ∃ z : ℤ, coeff i (transfer (family g) f) =
        (i : ℚ)*coeff i f + ((i : ℚ)*((i : ℚ)+1))*(z : ℚ) from
    aux (N+1) k (by omega) hk f hf hiF i hi
  intro d
  induction d with
  | zero =>
    intro k hbound hk f hf hiF i hi
    exact ⟨0, by rw [transfer_vanishes _ hE hf i (by omega), hf i (by omega)]; simp⟩
  | succ d ih =>
    intro k hbound hk f hf hiF i hi
    let b := f * euler g
    have bv : vanishes b (k+1) := vanishes_mul_euler hf
    have bi : integralTo b N := integral_mul_euler prefixInt (hf 0 hk) hiF
    have nextBound : N < k+1+d := by omega
    have stepB := ih (k+1) nextBound (by omega) b bv bi
    have tv := transfer_vanishes _ hE bv
    have ti : integralTo (transfer (family g) b) N := by
      intro j hj
      obtain ⟨a, ha⟩ := bi j hj
      obtain ⟨u, hu⟩ := stepB j hj
      exact ⟨(j:ℤ)*a+((j:ℤ)*((j:ℤ)+1))*u, by rw [hu, ha]; push_cast; rfl⟩
    obtain ⟨v, hv⟩ := ih (k+1) nextBound (by omega) _ tv ti i hi
    obtain ⟨a, ha⟩ := bi i hi
    obtain ⟨u, hu⟩ := stepB i hi
    refine ⟨a+((i:ℤ)+1)*u+v, ?_⟩
    rw [transfer_recursion g f hg, map_add, map_add, euler_coeff]
    change (i : ℚ) * coeff i f + (coeff i (transfer _ (transfer _ b)) + coeff i (transfer _ b)) = _
    rw [hv, hu, ha]
    push_cast
    ring


lemma ordinary_integrality (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hsource : ∀ n : ℕ, 0 < n → coeff n (family g n) =
      ((n : ℚ)*((n : ℚ)+1)) * coeff (n - 1) (family g n)) (n : ℕ) :
    ∃ z : ℤ, coeff n g = (z : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn, coeff_zero_eq_constantCoeff, hg]⟩
    have vanishX : vanishes (X : PowerSeries ℚ) 1 := by
      intro j hj
      have : j = 0 := by omega
      simp [this]
    have intX : integralTo (X : PowerSeries ℚ) n := by
      intro j hj
      by_cases h : j = 1
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [coeff_X, h]⟩
    obtain ⟨z, hz⟩ := transfer_congruence g hg n ih 1 (by omega) X vanishX intX n le_rfl
    obtain ⟨d, hd⟩ := intX n le_rfl
    rw [transfer_source g hg hsource, euler_coeff, hd] at hz
    refine ⟨d+((n:ℤ)+1)*z, ?_⟩
    apply mul_left_cancel₀ (show (n : ℚ) ≠ 0 by exact_mod_cast hn)
    push_cast
    linear_combination hz


/-- The subring of rationals whose reduced denominators are prime to p. -/
def localInts (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | 0 ≤ padicValRat p q}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change 0 ≤ padicValRat p (a+b)
    by_cases h : a+b = 0
    · simp [h]
    · exact (le_min ha hb).trans (padicValRat.min_le_padicValRat_add h)
  neg_mem' := by
    intro a ha
    simpa only [Set.mem_ofPred_eq, padicValRat.neg] using ha
  mul_mem' := by
    intro a b ha hb
    change 0 ≤ padicValRat p (a*b)
    by_cases az : a = 0
    · simp [az]
    by_cases bz : b = 0
    · simp [bz]
    rw [padicValRat.mul az bz]
    exact add_nonneg ha hb

lemma integer_of_local (q : ℚ)
    (hq : ∀ (p : ℕ) (hp : p.Prime), q ∈ @localInts p ⟨hp⟩) :
    ∃ a : ℤ, q = (a : ℚ) := by
  refine ⟨q.num, (Rat.coe_int_num_of_den_eq_one ?_).symm⟩
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  let : Fact p.Prime := ⟨hp⟩
  have hn : ¬ p ∣ q.num.natAbs := by
    intro hnum
    have hh := Nat.dvd_gcd hnum hpd
    rw [q.reduced.gcd_eq_one] at hh
    exact hp.not_dvd_one hh
  have nv : padicValInt p q.num = 0 := padicValNat.eq_zero_of_not_dvd hn
  have dv := one_le_padicValNat_of_dvd q.den_nz hpd
  have h := hq p hp
  change 0 ≤ padicValRat p q at h
  rw [padicValRat_def, nv] at h
  omega

/-- Legendre's estimate loses at most the factor of two appearing in a triangular number. -/
lemma factorial_bound (p k : ℕ) [hprime : Fact p.Prime] :
    padicValNat p (k+2).factorial ≤ k + padicValNat p 2 := by
  by_cases h : p = 2
  · subst p
    rw [padicValNat_self]
    have v := padicValNat_factorial_lt_of_ne_zero 2 (n := k+2) (by omega)
    omega
  · have hp := hprime.out.two_le
    have hv := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := k+2) (by omega)
    have bound := Nat.mul_le_mul_right (padicValNat p (k+2).factorial) (show 2 ≤ p-1 by omega)
    omega

lemma scaled_factorial (p m k : ℕ) [Fact p.Prime] (hm : 0 < m) (hd : p ∣ m) :
    2*(m : ℚ)^k / ((k+2).factorial : ℚ) ∈ localInts p := by
  change 0 ≤ padicValRat p (2*(m : ℚ)^k / ((k+2).factorial : ℚ))
  have ht : padicValRat p (2 : ℚ) = (padicValNat p 2 : ℤ) :=
    padicValRat.of_nat
  rw [padicValRat.div (by positivity) (by positivity),
    padicValRat.mul (by norm_num) (by positivity), padicValRat.pow, ht,
    padicValRat.of_nat, padicValRat.of_nat]
  have vm := one_le_padicValNat_of_dvd (Nat.ne_of_gt hm) hd
  have va := factorial_bound p k
  have vb := Nat.mul_le_mul_left k vm
  have vb' : (k : ℤ) ≤ (k : ℤ)*(padicValNat p m : ℤ) := by
    exact_mod_cast (show k ≤ k * padicValNat p m by simpa using vb)
  have va' : (padicValNat p (k+2).factorial : ℤ) ≤ (k : ℤ)+(padicValNat p 2 : ℤ) := by
    exact_mod_cast va
  omega

lemma lower_factorial (p m k : ℕ) [Fact p.Prime] (hm : 0 < m) (hd : p ∣ m) :
    2*(m : ℚ)^k / ((k+1).factorial : ℚ) ∈ localInts p := by
  have h := (localInts p).mul_mem (scaled_factorial p m k hm hd)
    (natCast_mem (localInts p) (k+2))
  convert h using 1
  rw [Nat.factorial_succ (k+1), Nat.cast_mul]
  push_cast
  field_simp
  ring

lemma integral_powers (p : ℕ) [Fact p.Prime] (g : PowerSeries ℚ)
    (hint : ∀ n, ∃ z : ℤ, coeff n g = (z : ℚ)) (i n : ℕ) :
    coeff n (g^i) ∈ localInts p := by
  induction i generalizing n with
  | zero =>
    by_cases h : n = 0 <;> simp [h, coeff_one]
  | succ i ih =>
    rw [pow_succ, coeff_mul]
    apply (localInts p).sum_mem
    rintro ⟨a,b⟩ hab
    obtain ⟨z,hz⟩ := hint b
    change coeff a (g^i) * coeff b g ∈ _
    rw [hz]
    exact (localInts p).mul_mem (ih a) (intCast_mem _ z)

lemma exponential_coeff (a : PowerSeries ℚ) (ha : constantCoeff a = 0) (n k : ℕ) :
    coeff k (exponential a n) =
      ∑ i ∈ Finset.range (k + 1), (n : ℚ) ^ i / (i.factorial : ℚ) * coeff k (a ^ i) := by
  let t := C (n : ℚ) * a
  have ht : constantCoeff t = 0 := by simp [t, ha]
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero ht
  change coeff k (subst t (PowerSeries.exp ℚ)) = _
  rw [coeff_subst' hs, finsum_eq_sum_of_support_subset _ (s := Finset.range (k + 1)) ?_]
  · apply Finset.sum_congr rfl
    intro i _
    dsimp only [t]
    rw [coeff_exp, mul_pow, ← map_pow, coeff_C_mul]
    simp only [Algebra.algebraMap_self_apply, smul_eq_mul]
    ring
  · intro i hi
    apply Finset.mem_range.mpr
    by_contra! h
    have lt : (k : ℕ∞) < (i : ℕ∞) := by exact_mod_cast (show k < i by omega)
    have hz : coeff k (t ^ i) = 0 :=
      coeff_of_lt_order k (lt.trans_le (le_order_pow_of_constantCoeff_eq_zero i ht))
    exact hi (by simp [hz])



/-- After removing the constant and linear terms only powers of order at least two remain. -/
lemma exp_top (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (m k : ℕ) :
    coeff (k+2) (exponential g m) = (m : ℚ)*coeff (k+2) g +
      ∑ j ∈ Finset.range (k+1),
        (m : ℚ)^(j+2) / ((j+2).factorial : ℚ) * coeff (k+2) (g^(j+2)) := by
  rw [exponential_coeff g hg m (k+2), Finset.sum_range_succ', Finset.sum_range_succ']
  simp [coeff_one, add_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show 1+(j+1) = j+2 by omega]

lemma local_low (p m k : ℕ) [Fact p.Prime] (hm : 0 < m) (hd : p ∣ m)
    (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hint : ∀ n, ∃ z : ℤ, coeff n g = (z : ℚ)) :
    2/(m : ℚ) * coeff (k+1) (exponential g m) ∈ localInts p := by
  rw [exponential_coeff g hg m (k+1), Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    coeff_one, Nat.add_one_ne_zero, if_false, add_zero, Finset.mul_sum]
  apply (localInts p).sum_mem
  intro j hj
  have h := (localInts p).mul_mem (lower_factorial p m j hm hd)
    (integral_powers p g hint (j+1) (k+1))
  convert h using 1
  rw [pow_succ]
  field_simp

lemma local_top (p m k : ℕ) [Fact p.Prime] (hm : 0 < m) (hd : p ∣ m)
    (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hint : ∀ n, ∃ z : ℤ, coeff n g = (z : ℚ)) :
    2/(m : ℚ)^2 * (coeff (k+2) (exponential g m) - (m : ℚ)*coeff (k+2) g)
      ∈ localInts p := by
  rw [exp_top g hg, add_sub_cancel_left, Finset.mul_sum]
  apply (localInts p).sum_mem
  intro j hj
  have h := (localInts p).mul_mem (scaled_factorial p m j hm hd)
    (integral_powers p g hint (j+2) (k+2))
  convert h using 1
  rw [pow_add (m : ℚ) j 2]
  field_simp

lemma local_divisibility (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hint : ∀ n, ∃ z : ℤ, coeff n g = (z : ℚ)) (m k : ℕ) (hm : 0 < m)
    (hs : coeff (k+2) (exponential g m) =
      (m : ℚ)*coeff (k+1) (exponential g m)) :
    ∃ z : ℤ, 2*coeff (k+2) g/(m : ℚ) = (z : ℚ) := by
  apply integer_of_local
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hd : p ∣ m
  · have h := (localInts p).sub_mem (local_low p m k hm hd g hg hint)
      (local_top p m k hm hd g hg hint)
    convert h using 1
    rw [hs]
    field_simp
    ring
  · have hu : (m : ℚ)⁻¹ ∈ localInts p := by
      change 0 ≤ padicValRat p (m : ℚ)⁻¹
      rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
      simp
    obtain ⟨a, ha⟩ := hint (k+2)
    rw [div_eq_mul_inv, ha]
    exact (localInts p).mul_mem ((localInts p).mul_mem (natCast_mem _ 2) (intCast_mem _ a)) hu

end OMA.A300871Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a300871.main := by
  intro g h n hn
  obtain ⟨hg, hs⟩ := h
  have hsource (j : ℕ) (hj : 0 < j) :
      PowerSeries.coeff j (OMA.A300871Proof.family g j) =
        (j : ℚ)*((j : ℚ)+1)*PowerSeries.coeff (j-1) (OMA.A300871Proof.family g j) := by
    simpa only [OMA.A300871Proof.family, OMA.A300871Proof.exponential, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, OMA.S_oeis_a300871.expMultiple] using hs j hj
  have hint := OMA.A300871Proof.ordinary_integrality g hg hsource
  obtain _ | _ | k := n
  · omega
  · obtain ⟨a,ha⟩ := hint 1
    exact ⟨a, ha, by simp⟩
  · let m := (k+2)*(k+2+1)
    have hm : 0 < m := by dsimp [m]; positivity
    have src : PowerSeries.coeff (k+2) (OMA.A300871Proof.exponential g m) =
        (m : ℚ) * PowerSeries.coeff (k+1) (OMA.A300871Proof.exponential g m) := by
      simpa only [m, OMA.A300871Proof.family, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_one, show k+2-1 = k+1 by omega] using hsource (k+2) (by omega)
    obtain ⟨z, hz⟩ := OMA.A300871Proof.local_divisibility g hg hint m k hm src
    have ht : 2 * ((m/2 : ℕ) : ℚ) = (m : ℚ) := by
      exact_mod_cast Nat.mul_div_cancel' (k+2).two_dvd_mul_add_one
    refine ⟨((m/2 : ℕ) : ℤ)*z, ?_, z, rfl⟩
    rw [Int.cast_mul, Int.cast_natCast]
    have hnz : (m : ℚ) ≠ 0 := by positivity
    rw [div_eq_iff hnz] at hz
    linear_combination (hz - (z : ℚ)*ht) / 2
