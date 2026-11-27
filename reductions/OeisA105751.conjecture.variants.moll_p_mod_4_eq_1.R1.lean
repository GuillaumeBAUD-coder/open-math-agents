import FormalConjectures.OEIS.«105751»

-- Reduction OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1 of Imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, $i = \sqrt{-1}$ — moll p mod 4 eq 1
-- Credit: @ZenimXD
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The limit splits into a lower bound and an upper bound.
-- * Lower bound (H1 + H2, both known): for p ≡ 1 (mod 4), p splits in ℤ[i] as π·π̄, and the
--   π-adic and π̄-adic valuations of ∏_{k ≤ n} (1 + k·i) are each at least ν_p(n!) (each residue
--   class mod p^e meets {1, …, n} at least ⌊n/p^e⌋ times). Since 2·i·a(n) = P - P̄ and p is odd,
--   ν_p(a(n)) ≥ ν_p(n!), which is H1. H2 (a(n) ≠ 0 for n ≥ 4, i.e. Σ_{k ≤ n} arctan k is a
--   multiple of π only for n = 0 and n = 3) makes that divisibility a bound on padicValInt.
--   Legendre's formula (p - 1)·ν_p(n!) = n - s_p(n) and s_p(n) = O(log n) then give the liminf.
-- * Upper bound (H3): the open core of Moll's conjecture for type 2 primes.
-- Numerically (n ≤ 3000, p ∈ {5, 13, 17, 29, 37, 41, 53}) H1 and H2 hold for every n.

namespace OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

open Filter Topology

/-- For a prime `p ≡ 1 (mod 4)`, `p ^ ν_p(n!)` divides `a n`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ n : ℕ,
    (p : ℤ) ^ padicValNat p n.factorial ∣ OeisA105751.a n

/-- `a n ≠ 0` for `n ≥ 4` (the product `∏ (1 + k i)` is real only for `n = 0` and `n = 3`). -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → OeisA105751.a n ≠ 0

/-- The upper half of Moll's conjecture for primes `p ≡ 1 (mod 4)`. -/
def H3 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ ε : ℚ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) ≤ 1 + ε

lemma digits_sum_le_mul (p n : ℕ) (hp : 1 < p) (hn : n ≠ 0) :
    (p.digits n).sum ≤ (p - 1) * (Nat.log p n + 1) := by
  have h := List.sum_le_card_nsmul (p.digits n) (p - 1)
    (fun x hx => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp hx))
  rw [Nat.length_digits p n hp hn, smul_eq_mul] at h
  simpa [Nat.mul_comm] using h

lemma lower_bound (h1 : H1) (h2 : H2) (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (n : ℕ)
    (hn : 4 ≤ n) :
    1 - ((p : ℚ) - 1) * ((Nat.log p n : ℚ) + 1) / (n : ℚ) ≤
      ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) := by
  have := Fact.mk hp
  have hn0 : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hv : padicValNat p n.factorial ≤ padicValInt p (OeisA105751.a n) := by
    rcases (padicValInt_dvd_iff _ _).1 (h1 p hp hmod n) with h | h
    · exact absurd h (h2 n hn)
    · exact h
  have hfact := sub_one_mul_padicValNat_factorial (p := p) n
  have hS : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  have hS2 := digits_sum_le_mul p n hp.one_lt (by omega)
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpq : (1 : ℚ) ≤ p := by exact_mod_cast hp1
  have e1 : ((p : ℚ) - 1) * (padicValNat p n.factorial : ℚ) = (n : ℚ) - ((p.digits n).sum : ℚ) := by
    have := congrArg (Nat.cast : ℕ → ℚ) hfact
    rw [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_sub hS, Nat.cast_one] at this
    exact this
  have e2 : ((p.digits n).sum : ℚ) ≤ ((p : ℚ) - 1) * ((Nat.log p n : ℚ) + 1) := by
    have := (Nat.cast_le (α := ℚ)).2 hS2
    rw [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_add, Nat.cast_one] at this
    exact this
  have e3 : ((p : ℚ) - 1) * (padicValNat p n.factorial : ℚ) ≤
      ((p : ℚ) - 1) * (padicValInt p (OeisA105751.a n) : ℚ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hv) (by linarith)
  have e4 : 1 - ((p : ℚ) - 1) * ((Nat.log p n : ℚ) + 1) / (n : ℚ) =
      ((n : ℚ) - ((p : ℚ) - 1) * ((Nat.log p n : ℚ) + 1)) / (n : ℚ) := by
    field_simp
  rw [e4]
  gcongr
  linarith

lemma log_term_tendsto (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n : ℕ => ((p : ℝ) - 1) / Real.log p * (Real.log n / n) + ((p : ℝ) - 1) * (1 / n))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
    have := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
    simpa [Function.comp_def] using this
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  simpa using (hlog.const_mul (((p : ℝ) - 1) / Real.log p)).add (hinv.const_mul ((p : ℝ) - 1))

lemma log_term_le (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 0 < n) :
    ((p : ℝ) - 1) * ((Nat.log p n : ℝ) + 1) / (n : ℝ) ≤
      ((p : ℝ) - 1) / Real.log p * (Real.log n / n) + ((p : ℝ) - 1) * (1 / n) := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  have hL : (Nat.log p n : ℝ) ≤ Real.log n / Real.log p := by
    have := Real.natLog_le_logb n p
    rwa [Real.logb] at this
  have hrhs : ((p : ℝ) - 1) / Real.log p * (Real.log n / n) + ((p : ℝ) - 1) * (1 / n) =
      ((p : ℝ) - 1) * (Real.log n / Real.log p + 1) / (n : ℝ) := by
    field_simp
  rw [hrhs]
  gcongr

theorem main : H1 → H2 → H3 → type_of% @OeisA105751.conjecture.variants.moll_p_mod_4_eq_1 := by
  intro h1 h2 h3 p hp hmod
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hδ : (0 : ℝ) < 1 - (c : ℝ) := by
      have : (c : ℝ) < 1 := by exact_mod_cast hc
      linarith
    have hev := (log_term_tendsto p hp).eventually (gt_mem_nhds hδ)
    filter_upwards [hev, eventually_ge_atTop 4] with n hn hn4
    have hle := log_term_le p hp n (by omega)
    have hG : ((p : ℚ) - 1) * ((Nat.log p n : ℚ) + 1) / (n : ℚ) < 1 - c := by
      have : ((((p : ℚ) - 1) * ((Nat.log p n : ℚ) + 1) / (n : ℚ) : ℚ) : ℝ) < ((1 - c : ℚ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have := lower_bound h1 h2 p hp hmod n hn4
    linarith
  · have hε : (0 : ℚ) < (c - 1) / 2 := by linarith
    filter_upwards [h3 p hp hmod ((c - 1) / 2) hε] with n hn
    linarith

end OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1
