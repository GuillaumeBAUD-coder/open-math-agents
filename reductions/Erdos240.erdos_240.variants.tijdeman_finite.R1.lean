import FormalConjectures.ErdosProblems.«240»

-- Reduction Erdos240.erdos_240.variants.tijdeman_finite.R1
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Follows Tijdeman (Compositio Math. 1973), whose proof rests on Baker's theorem; no new result is claimed.

/-!
# Gaps between `P`-smooth numbers, after Tijdeman

* `H1` (Baker's theorem on linear forms in logarithms, Baker 1966–67, quantitative form as in
  Baker's book *Transcendental Number Theory*, Thm 3.1): for a fixed finite set `S` of primes
  there are `C, c > 0` with `|∑_{p ∈ S} b_p log p| ≥ c B^{-C}` whenever the integers `b_p` are
  not all zero and `|b_p| ≤ B`, `B ≥ 2`. (The form is nonzero by unique factorisation.)
* `H2` (bookkeeping for `a P = Nat.nth (· ∈ composedOf P)`): `a P` is strictly increasing,
  takes values in `composedOf P`, and `a P (i+1) ≤ p * a P i` for `p ∈ P`, because
  `p * a P i` is a larger `P`-smooth number.
* `H3` (exponent vectors): for `S`-smooth `x, y > 0`,
  `log y - log x = ∑_{p ∈ S} b_p log p` with `b_p = v_p(y) - v_p(x)` and
  `|b_p| ≤ log (max x y) / log 2`.

Assembly (proved below): for consecutive `x = a P i < y = a P (i+1)`, `y ≤ p₀ x`, so the
`b_p` are `O(log x)`; Baker gives `log (y/x) ≥ c' (log x)^{-C}`, and
`y - x ≥ x log (y/x) ≥ c' x / (log x)^C`.
-/

namespace OMA.R_Erdos240_erdos_240_variants_tijdeman_finite_R1

open Filter Asymptotics

/-- Baker's lower bound for linear forms in logarithms of primes. -/
def H1 : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (b : ℕ → ℤ) (B : ℝ), 2 ≤ B → (∀ p ∈ S, |(b p : ℝ)| ≤ B) → (∃ p ∈ S, b p ≠ 0) →
      c * B ^ (-C) ≤ |∑ p ∈ S, (b p : ℝ) * Real.log p|

/-- Elementary structure of the enumeration `a P` of `P`-smooth numbers. -/
def H2 : Prop :=
  ∀ P : Set ℕ, P.Finite → P.Nonempty → P ⊆ {p : ℕ | p.Prime} →
    StrictMono (Erdos240.a P) ∧ (∀ i, Erdos240.a P i ∈ Erdos675.composedOf P) ∧
      ∀ p ∈ P, ∀ i, Erdos240.a P (i + 1) ≤ p * Erdos240.a P i

/-- Logarithms of `S`-smooth numbers are integer combinations of `log p`, `p ∈ S`, with
coefficients bounded by `log₂`. -/
def H3 : Prop :=
  ∀ (S : Finset ℕ) (x y : ℕ), 0 < x → 0 < y →
    (∀ p : ℕ, p.Prime → p ∣ x → p ∈ S) → (∀ p : ℕ, p.Prime → p ∣ y → p ∈ S) →
    ∃ b : ℕ → ℤ, Real.log (y : ℝ) - Real.log (x : ℝ) = ∑ p ∈ S, (b p : ℝ) * Real.log p ∧
      ∀ p ∈ S, |(b p : ℝ)| ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2

theorem main : H1 → H2 → H3 → type_of% @Erdos240.erdos_240.variants.tijdeman_finite := by
  intro h1 h2 h3 P hP hne hpr
  obtain ⟨hmono, hmem, hstep⟩ := h2 P hP hne hpr
  obtain ⟨p0, hp0⟩ := hne
  have hp0prime : p0.Prime := hpr hp0
  set S := hP.toFinset with hS
  have hSP : ∀ p, p ∈ S ↔ p ∈ P := fun p => Set.Finite.mem_toFinset hP
  obtain ⟨C, c, hC, hc, hbaker⟩ := h1 S (fun p hp => hpr ((hSP p).1 hp))
  refine ⟨C, hC, ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlp0 : 0 ≤ Real.log (p0 : ℝ) := Real.log_nonneg (by exact_mod_cast hp0prime.one_lt.le)
  set K0 : ℝ := (Real.log (p0 : ℝ) + 1) / Real.log 2 + 2 with hK0
  have hK0pos : 0 < K0 := by positivity
  set κ : ℝ := c * K0 ^ (-C) with hκ
  have hκpos : 0 < κ := by positivity
  refine IsBigO.of_bound κ⁻¹ ?_
  have hev : ∀ᶠ i in atTop, 3 ≤ Erdos240.a P i :=
    hmono.tendsto_atTop.eventually (eventually_ge_atTop 3)
  filter_upwards [hev] with i hi
  set x := Erdos240.a P i with hx
  set y := Erdos240.a P (i + 1) with hy
  have hxy : x < y := hmono (Nat.lt_succ_self i)
  have hyx : y ≤ p0 * x := hstep p0 hp0 i
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hxyR : (x : ℝ) < y := by exact_mod_cast hxy
  have hmx := hmem i
  have hmy := hmem (i + 1)
  obtain ⟨b, hlog, hb⟩ := h3 S x y (by omega) (by omega)
    (fun p hp hd => (hSP p).2 (hmx.2 p hp hd)) (fun p hp hd => (hSP p).2 (hmy.2 p hp hd))
  rw [max_eq_right hxy.le] at hb
  -- the linear form is `log y - log x > 0`
  have hΛpos : 0 < Real.log (y : ℝ) - Real.log (x : ℝ) := by
    have := Real.log_lt_log hxpos hxyR
    linarith
  have hlogy : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  set B : ℝ := Real.log (y : ℝ) / Real.log 2 + 2 with hB
  have hB2 : 2 ≤ B := by
    have : 0 ≤ Real.log (y : ℝ) / Real.log 2 := div_nonneg hlogy hl2.le
    linarith
  have hbB : ∀ p ∈ S, |(b p : ℝ)| ≤ B := by
    intro p hp
    have := hb p hp
    linarith
  have hnz : ∃ p ∈ S, b p ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : ∑ p ∈ S, (b p : ℝ) * Real.log p = 0 :=
      Finset.sum_eq_zero fun p hp => by rw [hall p hp]; simp
    linarith
  have hbak := hbaker b B hB2 hbB hnz
  rw [← hlog, abs_of_pos hΛpos] at hbak
  -- `B ≤ K0 * log x`
  have hlogx1 : 1 ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le hxpos]
    have h3x : (3 : ℝ) ≤ x := by exact_mod_cast hi
    have := Real.exp_one_lt_d9
    linarith
  have hlogyx : Real.log (y : ℝ) ≤ Real.log (p0 : ℝ) + Real.log (x : ℝ) := by
    rw [← Real.log_mul (by exact_mod_cast hp0prime.ne_zero) hxpos.ne']
    exact Real.log_le_log hypos (by exact_mod_cast hyx)
  have hBK : B ≤ K0 * Real.log (x : ℝ) := by
    have e1 : Real.log (y : ℝ) / Real.log 2 ≤
        (Real.log (p0 : ℝ) + 1) / Real.log 2 * Real.log (x : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2]
      nlinarith
    rw [hB, hK0]
    nlinarith
  have hBpos : 0 < B := by linarith
  have hpow : (K0 * Real.log (x : ℝ)) ^ (-C) ≤ B ^ (-C) :=
    Real.rpow_le_rpow_of_nonpos hBpos hBK (by linarith)
  rw [Real.mul_rpow hK0pos.le (by linarith)] at hpow
  -- `y - x ≥ x * log (y / x)`
  have hgap : (x : ℝ) * (Real.log (y : ℝ) - Real.log (x : ℝ)) ≤ (y : ℝ) - x := by
    rw [← Real.log_div hypos.ne' hxpos.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
    have e : (x : ℝ) * ((y : ℝ) / x - 1) = y - x := by field_simp
    nlinarith
  have hlx : 0 < Real.log (x : ℝ) := by linarith
  have hfx : (x : ℝ) / Real.log (x : ℝ) ^ C = (x : ℝ) * Real.log (x : ℝ) ^ (-C) := by
    rw [Real.rpow_neg hlx.le, div_eq_mul_inv]
  have hrp : 0 < Real.log (x : ℝ) ^ (-C) := Real.rpow_pos_of_pos hlx _
  have hcast : (((y - x : ℕ)) : ℝ) = (y : ℝ) - x := by rw [Nat.cast_sub hxy.le]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hcast, hfx,
    abs_of_pos (mul_pos hxpos hrp), abs_of_pos (by linarith)]
  rw [inv_mul_eq_div, le_div_iff₀ hκpos]
  -- `x (log x)^{-C} κ ≤ x c B^{-C} ≤ x Λ ≤ y - x`
  calc (x : ℝ) * Real.log (x : ℝ) ^ (-C) * κ
      = (x : ℝ) * (c * (K0 ^ (-C) * Real.log (x : ℝ) ^ (-C))) := by rw [hκ]; ring
    _ ≤ (x : ℝ) * (c * B ^ (-C)) := by gcongr
    _ ≤ (x : ℝ) * (Real.log (y : ℝ) - Real.log (x : ℝ)) := by gcongr
    _ ≤ (y : ℝ) - x := hgap

end OMA.R_Erdos240_erdos_240_variants_tijdeman_finite_R1
