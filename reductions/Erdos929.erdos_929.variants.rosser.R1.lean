import FormalConjectures.ErdosProblems.«929»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-! # From Jacobsthal's interval estimate to the least covering prime

At the least admissible prime bound a covered block actually exists. We use
factorial periodicity to pass from density to a finite block. Chebyshev's
explicit estimate then converts a bound in terms of the number of prime
divisors into a square-root lower bound for the size of the largest prime. -/

namespace OMA.R_Erdos929_erdos_929_variants_rosser_R1
open Finset Filter Erdos929

-- Iwaniec's bound for a block covered by r distinct primes.
def H1 : Prop := ∃ C : ℝ, 0<C ∧ ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
  ∀ k n : ℕ, (∀ i ∈ Icc 1 k, ∃ p ∈ P, p ∣ n+i) →
    (k:ℝ) ≤ C*((P.card:ℝ)*Real.log ((P.card:ℝ)+1))^2

-- A periodic set of natural numbers has positive density exactly when nonempty.
def H2 : Prop := ∀ (T : Set ℕ) (m : ℕ), 0 < m →
  (∀ n : ℕ, n+m∈T ↔ n∈T) → (T.HasPosDensity ↔ T.Nonempty)

lemma factor_period (x k n : ℕ) :
    AllHaveSmallPrimeFactor x k (n+x.factorial) ↔ AllHaveSmallPrimeFactor x k n := by
  have shift (p i : ℕ) (pr : p.Prime) (px : p≤x) :
      p ∣ n+x.factorial+i ↔ p ∣ n+i := by
    rw [Nat.add_right_comm]
    exact (Nat.dvd_add_iff_left (Nat.dvd_factorial pr.pos px)).symm
  constructor <;> intro h i hi <;> obtain ⟨p,pr,px,dvd⟩ := h i hi
  · exact ⟨p,pr,px,(shift p i pr px).mp dvd⟩
  · exact ⟨p,pr,px,(shift p i pr px).mpr dvd⟩

lemma least_witness (periodic : H2) (k : ℕ) : ∃ n, AllHaveSmallPrimeFactor (S k) k n := by
  have equiv (x:ℕ) := periodic {n | AllHaveSmallPrimeFactor x k n} x.factorial
    (Nat.factorial_pos _) (factor_period x k)
  have first : AllHaveSmallPrimeFactor (k+1) k 1 := by
    intro i hi
    obtain ⟨lo,up⟩ := mem_Icc.mp hi
    obtain ⟨p,pr,dv⟩ := Nat.exists_prime_and_dvd (show 1+i≠1 by omega)
    exact ⟨p,pr,by have := Nat.le_of_dvd (show 0<1+i by omega) dv; omega,dv⟩
  let choices := {x : ℕ | {n : ℕ | AllHaveSmallPrimeFactor x k n}.HasPosDensity}
  have nonempty : choices.Nonempty := ⟨k+1,(equiv _).mpr ⟨1,first⟩⟩
  exact (equiv _).mp (Nat.sInf_mem nonempty)

-- π(x) log(π(x)+1) is bounded by a constant times x, with an explicit constant.
lemma prime_count_log (x:ℕ) (hx : 2≤x) :
    ((Nat.primesLE x).card:ℝ)*Real.log (((Nat.primesLE x).card:ℝ)+1)
      ≤ (4*Real.log 4+4)*x := by
  let r := (Nat.primesLE x).card
  have hr : r ≤ x+1 := by
    dsimp [r]
    rw [Nat.primesLE_eq_filter_range]
    simpa using card_le_card (filter_subset Nat.Prime (range (x+1)))
  have x2 : (2:ℝ)≤x := by exact_mod_cast hx
  have xp : 0<(x:ℝ) := by linarith
  have lp := Real.log_pos (show 1<(x:ℝ) by linarith)
  have le : (r:ℝ)+1 ≤ (x:ℝ)^2 := by
    have hr' : (r:ℝ) ≤ (x:ℝ)+1 := by exact_mod_cast hr
    nlinarith [mul_nonneg (sub_nonneg.mpr x2) (show 0≤(x:ℝ)+1 by positivity)]
  have logs : Real.log ((r:ℝ)+1) ≤ 2*Real.log (x:ℝ) := by
    have h := Real.log_le_log (show 0<(r:ℝ)+1 by positivity) le
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have small : Real.sqrt (x:ℝ) * Real.log x ≤ 2*x := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr xp)
    rw [Real.log_sqrt xp.le] at h
    nlinarith [mul_nonneg (Real.sqrt_nonneg (x:ℝ))
      (show 0≤2*Real.sqrt (x:ℝ)-Real.log x by linarith),Real.sq_sqrt xp.le]
  have est := Chebyshev.pi_le_log4_mul_div (x:=(x:ℝ)) (by linarith)
  rw [Nat.floor_natCast,Real.log_sqrt xp.le,←Nat.primesLE_card_eq_primeCounting] at est
  change (r:ℝ) ≤ _ at est
  have prod : (r:ℝ)*Real.log x ≤ (2*Real.log 4+2)*x := by
    have h : (r:ℝ)-Real.sqrt x ≤ Real.log 4*x/(Real.log x/2) := by linarith
    have hh := (le_div_iff₀ (show 0<Real.log x/2 by linarith)).mp h
    nlinarith
  change (r:ℝ)*_ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left logs (show 0≤(r:ℝ) by positivity)]

theorem main : H1 → H2 → type_of% @Erdos929.erdos_929.variants.rosser := by
  rintro ⟨C,cp,sieve⟩ periodic ε hε
  let K : ℝ := 4*Real.log 4+4
  have kp : 0<K := by dsimp [K]; positivity
  have far : ∀ᶠ k : ℕ in atTop, Real.sqrt C*K ≤ (k:ℝ)^ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [far,eventually_ge_atTop 1] with k hk h1
  obtain ⟨n,hn⟩ := least_witness periodic k
  let x := S k
  obtain ⟨p,pp,px,_⟩ := hn 1 (mem_Icc.mpr ⟨by decide,h1⟩)
  have hx : 2≤x := pp.two_le.trans px
  let P := Nat.primesLE x
  have count := sieve P (fun q hq => Nat.prime_of_mem_primesLE hq) k n (by
    intro i hi
    obtain ⟨q,pr,qx,dv⟩ := hn i hi
    exact ⟨q,Nat.mem_primesLE.mpr ⟨qx,pr⟩,dv⟩)
  have fac : 0 ≤ (P.card:ℝ)*Real.log ((P.card:ℝ)+1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) P.card; linarith))
  have root := Real.sqrt_le_sqrt count
  rw [Real.sqrt_mul cp.le,Real.sqrt_sq fac] at root
  have bound := mul_le_mul_of_nonneg_left (prime_count_log x hx) (Real.sqrt_nonneg C)
  change Real.sqrt C*((P.card:ℝ)*Real.log ((P.card:ℝ)+1)) ≤ Real.sqrt C*(K*x) at bound
  have kn : 0<(k:ℝ) := by exact_mod_cast h1
  rw [Real.rpow_sub kn,←Real.sqrt_eq_rpow,div_le_iff₀ (Real.rpow_pos_of_pos kn ε)]
  change Real.sqrt (k:ℝ) ≤ (x:ℝ)*(k:ℝ)^ε
  nlinarith [root.trans bound,mul_le_mul_of_nonneg_left hk (show 0≤(x:ℝ) by positivity)]

end OMA.R_Erdos929_erdos_929_variants_rosser_R1
