import FormalConjectures.ErdosProblems.«912»
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Algebra.Order.Chebyshev

/-!
Split the prime counts at the scale `√(n * log n)` from the upper-bound
sieve estimate for close pairs of primes. Large primes contribute exponents
`n / p`, and coincident exponents at the counting scale force a short gap.
The lower bound follows by a Cauchy–Schwarz count of these collisions.
See Erdős (1982), Miscellaneous problems in number theory, Theorem 1.
-/

-- Credit: @dk8827

open Finset Filter Asymptotics
open scoped BigOperators Pointwise Topology

namespace OMA.R_Erdos912_erdos_912_variants_selfridge_R1

private theorem factorization_of_large_prime {p n : ℕ} (hp : p.Prime) (hn : n < p * p) :
    n.factorial.factorization p = n / p := by
  have hl : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) (by simpa [pow_two] using hn)
  rw [Nat.factorization_factorial hp hl]
  norm_num

private theorem energy_le {α : Type} (P : Finset α) (f : α → ℕ) (Q : Finset (α × α))
    (hc : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → f p = f q → (p, q) ∈ Q) :
    P.card ^ 2 ≤ (P.image f).card * (P.card + Q.card) := by
  classical
  let F := P.image f
  let L (k : ℕ) := P.filter (fun p => f p = k)
  let C := (P ×ˢ P).filter (fun x => f x.1 = f x.2)
  have hSub : C ⊆ P.diag ∪ Q := by
    intro x hx
    obtain ⟨hpair, he⟩ := mem_filter.1 hx
    obtain ⟨hp, hq⟩ := mem_product.1 hpair
    by_cases h : x.1 = x.2
    · exact mem_union_left _ (mem_diag.2 ⟨hp, h⟩)
    · exact mem_union_right _ (hc x.1 hp x.2 hq h he)
  have hC : C.card ≤ P.card + Q.card :=
    (card_le_card hSub).trans (by simpa using card_union_le P.diag Q)
  have hsum : (∑ k ∈ F, (L k).card) = P.card := by
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    ext x
    exact ⟨fun hx => (mem_filter.1 hx).1, fun hx => mem_filter.2 ⟨hx, mem_image_of_mem f hx⟩⟩
  have henergy : (∑ k ∈ F, (L k).card ^ 2) = C.card := by
    have hfiber (k : ℕ) :
        (C.filter (fun x => f x.1 = k)) = L k ×ˢ L k := by
      ext x
      simp only [C, L, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨hp, hq⟩, he⟩, hk⟩
        exact ⟨⟨hp, hk⟩, ⟨hq, he.symm.trans hk⟩⟩
      · rintro ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩
        exact ⟨⟨⟨hp, hq⟩, hp'.trans hq'.symm⟩, hp'⟩
    calc
      _ = ∑ k ∈ F, (C.filter (fun x => f x.1 = k)).card := by
        apply sum_congr rfl
        intro k _
        rw [hfiber, card_product, pow_two]
      _ = C.card := by
        rw [sum_card_fiberwise_eq_card_filter]
        congr 1
        ext x
        exact ⟨fun h => (mem_filter.1 h).1, fun h =>
          mem_filter.2 ⟨h, mem_image_of_mem f (mem_product.1 (mem_filter.1 h).1).1⟩⟩
  calc
    _ = (∑ k ∈ F, (L k).card) ^ 2 := by rw [hsum]
    _ ≤ F.card * ∑ k ∈ F, (L k).card ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by rw [henergy]; exact Nat.mul_le_mul_left _ hC

private theorem close_of_div_eq {n p q : ℕ} {X : ℝ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (hpX : (p : ℝ) ≤ X) (hqX : (q : ℝ) ≤ X) (hX : X ^ 2 = (n : ℝ) * Real.log n)
    (h : n / p = n / q) : |(p : ℝ) - (q : ℝ)| < Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpx : (p : ℝ) ≤ X) (hqx : (q : ℝ) ≤ X)
      (he : n / p = n / q) : (q : ℝ) - p < Real.log n := by
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hlow : ((n / q : ℕ) : ℝ) ≤ (n : ℝ) / q := by
      apply (le_div_iff₀ hq').2
      exact_mod_cast Nat.div_mul_le_self n q
    have hhi : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      apply (div_lt_iff₀ hp').2
      exact_mod_cast (Nat.div_lt_iff_lt_mul hp).1 (Nat.lt_succ_self (n / p))
    have h' : (n : ℝ) / p - (n : ℝ) / q < 1 := by rw [he] at hhi; linarith only [hhi, hlow]
    apply (mul_lt_mul_iff_right₀ hn').1
    calc
      (n : ℝ) * ((q : ℝ) - p) = ((n : ℝ) / p - (n : ℝ) / q) * ((p : ℝ) * q) := by
        field_simp
      _ < 1 * ((p : ℝ) * q) := mul_lt_mul_of_pos_right h' (mul_pos hp' hq')
      _ ≤ (n : ℝ) * Real.log n := by
        rw [← hX, one_mul, pow_two]
        exact mul_le_mul hpx hqx hq'.le (hp'.le.trans hpx)
  exact abs_lt.2 ⟨by linarith only [hdiff hp hq hpX hqX h], hdiff hq hp hqX hpX h.symm⟩

def H1 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    let X := √((n : ℝ) * Real.log n)
    let P := Nat.primesLE ⌊X⌋₊
    c * √((n : ℝ) / Real.log n) ≤ ((P.filter (fun p => p ≤ n ∧ n < p * p)).card : ℝ) ∧
    (P.card : ℝ) ≤ C * √((n : ℝ) / Real.log n)

def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    let P := Nat.primesLE ⌊√((n : ℝ) * Real.log n)⌋₊
    let Q := (P ×ˢ P).filter (fun x => x.1 ≠ x.2 ∧ |(x.1 : ℝ) - (x.2 : ℝ)| < Real.log n)
    (Q.card : ℝ) ≤ C * √((n : ℝ) / Real.log n)

set_option maxHeartbeats 950000 in
theorem main : H1 → H2 → type_of% @Erdos912.erdos_912.variants.selfridge := by
  classical
  intro hprime hpairs
  obtain ⟨c, C, hc, hC, hprime⟩ := hprime
  obtain ⟨D, hD, hpairs⟩ := hpairs
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      (Erdos912.h n : ℝ) ≤ (C + 1) * √((n : ℝ) / Real.log n) ∧
      √((n : ℝ) / Real.log n) ≤ ((C + D) / c ^ 2) * (Erdos912.h n : ℝ) := by
    filter_upwards [hprime, hpairs, hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with
      n hprime hpairs hL hn
    let X := √((n : ℝ) * Real.log n)
    let Y := √((n : ℝ) / Real.log n)
    let P := Nat.primesLE ⌊X⌋₊
    let R := P.filter (fun p => p ≤ n ∧ n < p * p)
    let Q := (P ×ˢ P).filter (fun x => x.1 ≠ x.2 ∧ |(x.1 : ℝ) - (x.2 : ℝ)| < Real.log n)
    let e := n.factorial.factorization
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hL' : 0 < Real.log n := zero_lt_one.trans_le hL
    have hX0 : 0 < X := Real.sqrt_pos.2 (mul_pos hn' hL')
    have hY0 : 0 < Y := Real.sqrt_pos.2 (div_pos hn' hL')
    have hX : X ^ 2 = (n : ℝ) * Real.log n := Real.sq_sqrt (mul_nonneg hn'.le hL'.le)
    have hXY : X * Y = (n : ℝ) := by
      dsimp only [X, Y]
      rw [← Real.sqrt_mul (mul_nonneg hn'.le hL'.le)]
      have he : (n : ℝ) * Real.log n * ((n : ℝ) / Real.log n) = (n : ℝ) ^ 2 := by
        field_simp
      rw [he, Real.sqrt_sq hn'.le]
    obtain ⟨hlo, hhi⟩ : c * Y ≤ (R.card : ℝ) ∧ (P.card : ℝ) ≤ C * Y := hprime
    have hQ : (Q.card : ℝ) ≤ D * Y := hpairs
    constructor
    · have hs : e.frange ⊆ P.image e ∪ Icc 1 ⌊Y⌋₊ := by
        intro k hk
        obtain ⟨hk0, p, rfl⟩ := Finsupp.mem_frange.1 hk
        have hpprime : p.Prime := by
          by_contra h
          exact hk0 (Nat.factorization_eq_zero_of_not_prime _ h)
        by_cases hp : p ≤ ⌊X⌋₊
        · exact mem_union_left _ (mem_image_of_mem e (Nat.mem_primesLE.2 ⟨hp, hpprime⟩))
        · have hpX : X < (p : ℝ) := (Nat.floor_lt hX0.le).1 (lt_of_not_ge hp)
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
          have hpsq : n < p * p := by
            have h := mul_lt_mul_of_pos_right hpX hX0
            have h' := mul_le_mul_of_nonneg_left hpX.le hp0.le
            have h'' := mul_le_mul_of_nonneg_left hL hn'.le
            exact_mod_cast (show (n : ℝ) < (p : ℝ) * p by nlinarith only [h, h', h'', hX])
          have hval : ((e p : ℕ) : ℝ) ≤ Y := by
            rw [show e p = n / p from factorization_of_large_prime hpprime hpsq]
            apply (le_of_mul_le_mul_right · hp0)
            calc
              _ ≤ (n : ℝ) := by exact_mod_cast Nat.div_mul_le_self n p
              _ = X * Y := hXY.symm
              _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hpX.le hY0.le
          exact mem_union_right _ (mem_Icc.2 ⟨by omega, (Nat.le_floor_iff hY0.le).2 hval⟩)
      have hnat : Erdos912.h n ≤ P.card + ⌊Y⌋₊ := by
        calc
          _ ≤ (P.image e ∪ Icc 1 ⌊Y⌋₊).card := card_le_card hs
          _ ≤ (P.image e).card + (Icc 1 ⌊Y⌋₊).card := card_union_le _ _
          _ ≤ _ := by simpa using Nat.add_le_add_right card_image_le ⌊Y⌋₊
      have hcast : (Erdos912.h n : ℝ) ≤ (P.card : ℝ) + ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnat
      change (Erdos912.h n : ℝ) ≤ (C + 1) * Y
      linarith only [hcast, hhi, Nat.floor_le hY0.le]
    · have hsub : R.image (fun p => n / p) ⊆ e.frange := by
        intro k hk
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hk
        obtain ⟨hP, hpN, hpn⟩ := mem_filter.1 hp
        have hpprime := Nat.prime_of_mem_primesLE hP
        have hh : e p = n / p := factorization_of_large_prime hpprime hpn
        exact Finsupp.mem_frange.2 ⟨(Nat.div_pos hpN hpprime.pos).ne', p, hh⟩
      have hnenergy := energy_le R (fun p => n / p) Q (fun p hp q hq hne he => by
        have hpP := (mem_filter.1 hp).1
        have hqP := (mem_filter.1 hq).1
        have hpr := Nat.mem_primesLE.1 hpP
        have hqr := Nat.mem_primesLE.1 hqP
        have hpX : (p : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hpr.1
        have hqX : (q : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hqr.1
        exact mem_filter.2 ⟨mem_product.2 ⟨hpP, hqP⟩, hne,
          close_of_div_eq (by omega) hpr.2.pos hqr.2.pos hpX hqX hX he⟩)
      have he' : R.card ^ 2 ≤ Erdos912.h n * (R.card + Q.card) :=
        hnenergy.trans (Nat.mul_le_mul_right _ (card_le_card hsub))
      have hE : (R.card : ℝ) ^ 2 ≤ (Erdos912.h n : ℝ) * ((R.card : ℝ) + Q.card) := by
        exact_mod_cast he'
      have hR : (R.card : ℝ) ≤ C * Y :=
        (show (R.card : ℝ) ≤ P.card by exact_mod_cast card_filter_le P _).trans hhi
      have hsum : (R.card : ℝ) + Q.card ≤ (C + D) * Y := by linarith only [hR, hQ]
      have hlow : (c * Y) ^ 2 ≤ (R.card : ℝ) ^ 2 := by gcongr
      have hmul : c ^ 2 * (Y * Y) ≤ (Erdos912.h n : ℝ) * ((C + D) * Y) := by
        rw [← show (c * Y) ^ 2 = c ^ 2 * (Y * Y) by ring]
        exact hlow.trans (hE.trans (mul_le_mul_of_nonneg_left hsum (by positivity)))
      have hcancel : c ^ 2 * Y ≤ (C + D) * (Erdos912.h n : ℝ) := by
        apply (mul_le_mul_iff_left₀ hY0).1
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      change Y ≤ ((C + D) / c ^ 2) * (Erdos912.h n : ℝ)
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ (sq_pos_of_pos hc)).2 (by simpa [mul_comm] using hcancel)
  constructor
  · refine IsBigO.of_bound (C + 1) ?_
    filter_upwards [hbound] with n hn
    simpa only [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show (0 : ℝ) ≤ (Erdos912.h n : ℝ) by positivity)] using hn.1
  · refine IsBigO.of_bound ((C + D) / c ^ 2) ?_
    filter_upwards [hbound] with n hn
    simpa only [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show (0 : ℝ) ≤ (Erdos912.h n : ℝ) by positivity)] using hn.2

end OMA.R_Erdos912_erdos_912_variants_selfridge_R1
