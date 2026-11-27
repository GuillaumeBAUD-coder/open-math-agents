import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1

-- Reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1 of Step H2 of Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1
-- Credit: @santiemanuel
-- Each H becomes its own step once this file is accepted. Proving all of them closes R1.H2.R1.H2.R1.H2.

/-!
# Spectral $L^2$ Parseval & Bad-Set Multiplicity Reduction of `R1.H2.R1.H2.R1.H2`

We isolate the unconditional **$L^2$ spectral Parseval / almost-all-shifts minor-arc variance bound**
on `ℤ / Q ℤ` (`Q = ∏_{p ≤ x} p`) from the remaining CRT concentration / non-isolation property of
extremal minor-arc troughs:

1. `H1`: **Unconditional $L^2$ minor-arc mean-square bound on `ℤ / Q ℤ`**:
   there exists `C > 0` such that for all `x ≥ 2` and `L ≥ 1` (`D = L / (Nat.log 2 L + 1)`),
   `∑_{M < Q} S_min(M)^2 ≤ C * Q * L * log x` (equivalently, the normalized minor-arc second moment
   is `O(log x / L)`).
2. `H2`: **CRT bad-set multiplicity / non-isolation of deep minor-arc troughs**:
   there exists `θ ∈ (0, 1)` such that for `ε ∈ (0, 1)` and large `x`, if some residue class
   `M₀ < Q` had `S_min(M₀) < -θ * L`, then at least `Q / √L` residue classes `M < Q` would satisfy
   `S_min(M) < -(θ / 2) * L`.

Inside this reduction we prove unconditionally:
- `cos_add_int_mul_two_pi` and `minor_arc_mod_Q`: exact `Q`-periodicity `S_min(M) = S_min(M % Q)`.
- `spectral_orthogonality_on_primorial`: exact `ℤ / Q ℤ` orthogonality of distinct reduced fractions
  `r / d` (`d ∣ Q`, `gcd(r, d) = 1`).
- `chebyshev_lower_tail`: discrete lower-tail Chebyshev inequality on `Finset.range Q`.
- `main`: combining `H1` and `H2` via `Q`-periodicity, Chebyshev's inequality at `-(θ / 2) * L`, and
  `log x = o(√L)` yields `OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H2`.
-/

namespace OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1

open Filter Finset Real

/-- Unconditional $L^2$ minor-arc mean-square bound over a full primorial period `Q = ∏_{p ≤ x} p`:
there exists `C > 0` such that for every `x ≥ 2` and `L ≥ 1` (`D = L / (Nat.log 2 L + 1)`),
the sum of squares of the minor-arc Ramanujan–Fejér sum over `M ∈ range Q` is at most
`C * Q * L * log x`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x → ∀ L : ℕ, 1 ≤ L →
    let D := L / (Nat.log 2 L + 1)
    let Q := ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p;
    (∑ M ∈ Finset.range Q,
      (∑ d ∈ Q.divisors.filter (fun d => D < d),
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
              (‖∑ u ∈ Finset.range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ))) ^ 2) ≤
      C * (Q : ℝ) * (L : ℝ) * Real.log (x : ℝ)

/-- CRT bad-set multiplicity (non-isolation of deep minor-arc troughs):
there exists `θ ∈ (0, 1)` such that for every `ε ∈ (0, 1)` and all sufficiently large `x`
(`L = ⌈x ^ (1 + ε)⌉₊ / 2`, `D = L / (Nat.log 2 L + 1)`, `Q = ∏_{p ≤ x} p`), if some residue class
`M₀ < Q` drops below `-θ * L`, then at least `Q / √L` residue classes `M < Q` lie below
`-(θ / 2) * L`. -/
def H2 : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ᶠ x : ℕ in Filter.atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊ / 2
      let D := L / (Nat.log 2 L + 1)
      let Q := ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p;
      (∃ M₀ ∈ Finset.range Q,
        ∑ d ∈ Q.divisors.filter (fun d => D < d),
          ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
            ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
              Real.cos (2 * Real.pi * (r : ℝ) * ((M₀ + L : ℕ) : ℝ) / (d : ℝ)) *
                (‖∑ u ∈ Finset.range L,
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                  (L : ℝ)) < -(θ * (L : ℝ))) →
      (Q : ℝ) / Real.sqrt (L : ℝ) ≤
        (((Finset.range Q).filter fun M =>
          ∑ d ∈ Q.divisors.filter (fun d => D < d),
            ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
              ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
                Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                  (‖∑ u ∈ Finset.range L,
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                    (L : ℝ)) < -((θ / 2) * (L : ℝ))).card : ℝ)

lemma cos_add_int_mul_two_pi (t : ℝ) (m : ℤ) :
    Real.cos (t + 2 * Real.pi * (m : ℝ)) = Real.cos t := by
  rw [← Complex.exp_ofReal_mul_I_re, ← Complex.exp_ofReal_mul_I_re]
  have h : ((t + 2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I =
      (t : ℂ) * Complex.I + ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add,
    OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.exp_two_pi_I_int m, mul_one]

/-- Exact `Q`-periodicity of the minor-arc Ramanujan–Fejér sum in the shift `M`. -/
lemma minor_arc_mod_Q (Q D L M : ℕ) (hQ : 0 < Q) :
    (∑ d ∈ Q.divisors.filter (fun d => D < d),
      ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))) =
    (∑ d ∈ Q.divisors.filter (fun d => D < d),
      ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M % Q + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))) := by
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdQ : d ∣ Q := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdQ hQ
  have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  obtain ⟨k, hk⟩ := hdQ
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have hM : M = Q * (M / Q) + M % Q := (Nat.div_add_mod M Q).symm
  let qM : ℕ := M / Q
  have harg : 2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ) =
      2 * Real.pi * (r : ℝ) * ((M % Q + L : ℕ) : ℝ) / (d : ℝ) +
        2 * Real.pi * (((r * k * qM : ℕ) : ℤ) : ℝ) := by
    have hML : ((M + L : ℕ) : ℝ) = (d : ℝ) * (k : ℝ) * (qM : ℝ) + ((M % Q + L : ℕ) : ℝ) := by
      have hnat : M + L = d * k * qM + (M % Q + L) := by
        dsimp [qM]
        calc
          M + L = (Q * (M / Q) + M % Q) + L := by rw [← hM]
          _ = (d * k) * (M / Q) + (M % Q + L) := by rw [← hk, Nat.add_assoc]
      exact_mod_cast hnat
    rw [hML]
    push_cast
    field_simp
    ring
  rw [harg, cos_add_int_mul_two_pi]

/-- Exact spectral orthogonality of distinct reduced fractions `r₁ / d₁` and `r₂ / d₂`
(`d₁ ∣ Q`, `d₂ ∣ Q`) summed over a full primorial period `M ∈ range Q`. -/
lemma spectral_orthogonality_on_primorial {Q : ℕ} (hQ : 1 ≤ Q) (L : ℕ)
    {d₁ d₂ r₁ r₂ : ℕ} (hd₁ : d₁ ∈ Q.divisors) (hd₂ : d₂ ∈ Q.divisors)
    (hr₁ : r₁ < d₁) (hc₁ : Nat.Coprime r₁ d₁)
    (hr₂ : r₂ < d₂) (hc₂ : Nat.Coprime r₂ d₂) :
    (∑ M ∈ range Q,
      Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
        starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I))) =
    if d₁ = d₂ ∧ r₁ = r₂ then (Q : ℂ) else 0 := by
  have hd₁_dvd : d₁ ∣ Q := (Nat.mem_divisors.mp hd₁).1
  have hd₂_dvd : d₂ ∣ Q := (Nat.mem_divisors.mp hd₂).1
  have hd₁_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hd₁_dvd (by omega)
  have hd₂_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos hd₂_dvd (by omega)
  let q₁ := Q / d₁
  let q₂ := Q / d₂
  have hq₁_mul : d₁ * q₁ = Q := Nat.mul_div_cancel' hd₁_dvd
  have hq₂_mul : d₂ * q₂ = Q := Nat.mul_div_cancel' hd₂_dvd
  have hq₁_pos : 0 < q₁ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq₁_mul; omega
  have hq₂_pos : 0 < q₂ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq₂_mul; omega
  let m : ℤ := (r₁ * q₁ : ℤ) - (r₂ * q₂ : ℤ)
  have hterm : ∀ M : ℕ,
      Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
        starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((2 * Real.pi * (m : ℝ) * (L : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (M : ℝ) * (m : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro M
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hd₁_ne : (d₁ : ℝ) ≠ 0 := by exact_mod_cast hd₁_pos.ne'
    have hd₂_ne : (d₂ : ℝ) ≠ 0 := by exact_mod_cast hd₂_pos.ne'
    have hQ_ne : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    have hq₁_r : (d₁ : ℝ) * (q₁ : ℝ) = (Q : ℝ) := by exact_mod_cast hq₁_mul
    have hq₂_r : (d₂ : ℝ) * (q₂ : ℝ) = (Q : ℝ) := by exact_mod_cast hq₂_mul
    have harg_r : 2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) -
        2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) =
        2 * Real.pi * (m : ℝ) * (L : ℝ) / (Q : ℝ) +
          2 * Real.pi * (M : ℝ) * (m : ℝ) / (Q : ℝ) := by
      have hm_r : (m : ℝ) = (r₁ : ℝ) * (q₁ : ℝ) - (r₂ : ℝ) * (q₂ : ℝ) := by
        dsimp [m]
        push_cast
        ring
      have hd1_eq : (r₁ : ℝ) / (d₁ : ℝ) = ((r₁ : ℝ) * (q₁ : ℝ)) / (Q : ℝ) := by
        rw [← hq₁_r]
        field_simp
      have hd2_eq : (r₂ : ℝ) / (d₂ : ℝ) = ((r₂ : ℝ) * (q₂ : ℝ)) / (Q : ℝ) := by
        rw [← hq₂_r]
        field_simp
      calc
        2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) -
            2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ)
            = 2 * Real.pi * ((M + L : ℕ) : ℝ) * ((r₁ : ℝ) / (d₁ : ℝ) - (r₂ : ℝ) / (d₂ : ℝ)) := by ring
        _ = 2 * Real.pi * ((M + L : ℕ) : ℝ) *
              (((r₁ : ℝ) * (q₁ : ℝ)) / (Q : ℝ) - ((r₂ : ℝ) * (q₂ : ℝ)) / (Q : ℝ)) := by
              rw [hd1_eq, hd2_eq]
        _ = 2 * Real.pi * (m : ℝ) * (L : ℝ) / (Q : ℝ) +
              2 * Real.pi * (M : ℝ) * (m : ℝ) / (Q : ℝ) := by
              rw [hm_r]
              push_cast
              ring
    have harg_c := congrArg (fun t : ℝ => (t : ℂ) * Complex.I) harg_r
    push_cast at harg_c ⊢
    linear_combination harg_c
  simp_rw [hterm, ← Finset.mul_sum,
    OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.sum_exp_int_div hQ m]
  by_cases heq : d₁ = d₂ ∧ r₁ = r₂
  · rw [if_pos heq]
    rcases heq with ⟨rfl, rfl⟩
    have hm0 : m = 0 := by dsimp [m, q₁, q₂]; ring
    rw [hm0, if_pos (dvd_zero _)]
    simp
  · rw [if_neg heq]
    have hndvd : ¬ ((Q : ℤ) ∣ m) := by
      intro ⟨k, hk⟩
      have hlt1 : r₁ * q₁ < Q := by
        calc
          r₁ * q₁ < d₁ * q₁ := Nat.mul_lt_mul_of_pos_right hr₁ hq₁_pos
          _ = Q := hq₁_mul
      have hlt2 : r₂ * q₂ < Q := by
        calc
          r₂ * q₂ < d₂ * q₂ := Nat.mul_lt_mul_of_pos_right hr₂ hq₂_pos
          _ = Q := hq₂_mul
      have hm_lo : -(Q : ℤ) < m := by
        dsimp [m]
        omega
      have hm_hi : m < (Q : ℤ) := by
        dsimp [m]
        omega
      have hk0 : k = 0 := by nlinarith
      rw [hk0, mul_zero] at hk
      have hrq_eq : r₁ * q₁ = r₂ * q₂ := by
        dsimp [m] at hk
        omega
      have hcross_Q : (r₁ * d₂) * Q = (r₂ * d₁) * Q := by
        calc
          (r₁ * d₂) * Q = (r₁ * d₂) * (d₁ * q₁) := by rw [hq₁_mul]
          _ = d₁ * d₂ * (r₁ * q₁) := by ring
          _ = d₁ * d₂ * (r₂ * q₂) := by rw [hrq_eq]
          _ = (r₂ * d₁) * (d₂ * q₂) := by ring
          _ = (r₂ * d₁) * Q := by rw [hq₂_mul]
      have hcross : r₁ * d₂ = r₂ * d₁ := Nat.eq_of_mul_eq_mul_right (by omega) hcross_Q
      have hd₁_d₂ : d₁ ∣ d₂ := by
        have hdvd : d₁ ∣ r₁ * d₂ := ⟨r₂, by rw [hcross, Nat.mul_comm]⟩
        exact hc₁.symm.dvd_of_dvd_mul_left hdvd
      have hd₂_d₁ : d₂ ∣ d₁ := by
        have hdvd : d₂ ∣ r₂ * d₁ := ⟨r₁, by rw [← hcross, Nat.mul_comm]⟩
        exact hc₂.symm.dvd_of_dvd_mul_left hdvd
      have hd_eq : d₁ = d₂ := Nat.dvd_antisymm hd₁_d₂ hd₂_d₁
      subst hd_eq
      have hr_eq : r₁ = r₂ := Nat.eq_of_mul_eq_mul_right hd₁_pos hcross
      exact heq ⟨rfl, hr_eq⟩
    rw [if_neg hndvd, mul_zero]

/-- Discrete lower-tail Chebyshev inequality on any finite set `S`. -/
lemma chebyshev_lower_tail (S : Finset ℕ) (g : ℕ → ℝ) {A : ℝ} (hA : 0 < A) :
    A ^ 2 * ((S.filter fun m => g m < -A).card : ℝ) ≤ ∑ m ∈ S, (g m) ^ 2 := by
  calc
    A ^ 2 * ((S.filter fun m => g m < -A).card : ℝ)
        = ∑ _m ∈ S.filter (fun m => g m < -A), A ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ m ∈ S.filter (fun m => g m < -A), (g m) ^ 2 := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hlt : g m < -A := (mem_filter.mp hm).2
          nlinarith
    _ ≤ ∑ m ∈ S, (g m) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) (fun _ _ _ => sq_nonneg _)

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H2 := by
  intro hH1 hH2
  obtain ⟨C, hC_pos, hL2⟩ := hH1
  obtain ⟨θ, hθ_pos, hθ_lt1, hMult⟩ := hH2
  refine ⟨θ, hθ_lt1, fun ε hε hε1 => ?_⟩
  -- Choose threshold `N₀` so that `6 * C < (θ ^ 2 / 4) * √√L` whenever `L ≥ N₀`.
  obtain ⟨K, hK⟩ := exists_nat_gt (24 * C / θ ^ 2)
  let N₀ := max 4 (K ^ 4)
  filter_upwards [eventually_ge_atTop (2 * N₀ + 2), hMult ε hε hε1] with x hx hMult_x M
  intro L D Q
  have hx2 : 2 ≤ x := by omega
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hx_le_ceil : x ≤ ⌈(x : ℝ) ^ (1 + ε)⌉₊ := by
    have h1 : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
      calc
        (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (x : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
    exact_mod_cast h1.trans (Nat.le_ceil _)
  have hL_ge_N0 : N₀ ≤ L := by dsimp [L]; omega
  have hL_ge4 : 4 ≤ L := le_trans (le_max_left 4 (K ^ 4)) hL_ge_N0
  have hL_ge1 : 1 ≤ L := by omega
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_ge1
  have hQ_pos : 0 < Q := Finset.prod_pos fun _ hp => (mem_filter.mp hp).2.pos
  have hQ_pos_r : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ_pos
  -- Reduce arbitrary `M : ℕ` to `M₀ = M % Q ∈ range Q` via `minor_arc_mod_Q`.
  rw [minor_arc_mod_Q Q D L M hQ_pos]
  let g : ℕ → ℝ := fun m =>
    ∑ d ∈ Q.divisors.filter (fun d => D < d),
      ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((m + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))
  change -(θ * (L : ℝ)) ≤ g (M % Q)
  by_contra hlt
  push Not at hlt
  have hmem : M % Q ∈ range Q := mem_range.mpr (Nat.mod_lt M hQ_pos)
  have hcard_lo : (Q : ℝ) / Real.sqrt (L : ℝ) ≤
      (((range Q).filter fun m => g m < -((θ / 2) * (L : ℝ))).card : ℝ) :=
    hMult_x ⟨M % Q, hmem, hlt⟩
  have hcheb : ((θ / 2) * (L : ℝ)) ^ 2 *
      (((range Q).filter fun m => g m < -((θ / 2) * (L : ℝ))).card : ℝ) ≤
      ∑ m ∈ range Q, (g m) ^ 2 :=
    chebyshev_lower_tail (range Q) g (by positivity)
  have hvar : ∑ m ∈ range Q, (g m) ^ 2 ≤ C * (Q : ℝ) * (L : ℝ) * Real.log (x : ℝ) :=
    hL2 x hx2 L hL_ge1
  -- Combine lower and upper bounds on the bad-set cardinality.
  have hcomb1 : ((θ / 2) * (L : ℝ)) ^ 2 * ((Q : ℝ) / Real.sqrt (L : ℝ)) ≤
      C * (Q : ℝ) * (L : ℝ) * Real.log (x : ℝ) :=
    (mul_le_mul_of_nonneg_left hcard_lo (sq_nonneg _)).trans (hcheb.trans hvar)
  -- Simplify `(L : ℝ) ^ 2 / √L = (L : ℝ) * √L` and cancel `Q * L > 0`.
  have hsqrtL_pos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hL_pos
  have hlhs_eq : ((θ / 2) * (L : ℝ)) ^ 2 * ((Q : ℝ) / Real.sqrt (L : ℝ)) =
      (Q : ℝ) * (L : ℝ) * ((θ ^ 2 / 4) * Real.sqrt (L : ℝ)) := by
    have hsq : Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) = (L : ℝ) := Real.mul_self_sqrt hL_pos.le
    field_simp
    nlinarith [hsq]
  rw [hlhs_eq] at hcomb1
  have hcomb2 : (θ ^ 2 / 4) * Real.sqrt (L : ℝ) ≤ C * Real.log (x : ℝ) := by
    have hQL_pos : 0 < (Q : ℝ) * (L : ℝ) := mul_pos hQ_pos_r hL_pos
    have h1 : (Q : ℝ) * (L : ℝ) * ((θ ^ 2 / 4) * Real.sqrt (L : ℝ)) ≤
        (Q : ℝ) * (L : ℝ) * (C * Real.log (x : ℝ)) := by linarith
    exact le_of_mul_le_mul_left h1 hQL_pos
  -- Bound `log x ≤ 6 * √√L` while `√L = √√L * √√L`, contradicting `√√L > 24 * C / θ ^ 2`.
  let qL := Real.sqrt (Real.sqrt (L : ℝ))
  have hqL_ge1 : 1 ≤ qL := by
    dsimp [qL]
    have h1 : (1 : ℝ) ≤ Real.sqrt (L : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hL_ge1)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt h1
  have hqL_pos : 0 < qL := by linarith
  have hqL_sq : qL * qL = Real.sqrt (L : ℝ) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hqL_pow4 : qL ^ 4 = (L : ℝ) := by
    calc
      qL ^ 4 = (qL * qL) * (qL * qL) := by ring
      _ = Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) := by rw [hqL_sq]
      _ = (L : ℝ) := Real.mul_self_sqrt hL_pos.le
  have hK_le_qL : (K : ℝ) ≤ qL := by
    have hKL : ((K ^ 4 : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (le_max_right 4 (K ^ 4)).trans hL_ge_N0
    rw [Nat.cast_pow, ← hqL_pow4] at hKL
    by_contra hlt_q
    push Not at hlt_q
    have hp4 : qL ^ 4 < (K : ℝ) ^ 4 := pow_lt_pow_left₀ hlt_q hqL_pos.le (by norm_num)
    linarith
  have hqL_gt : 24 * C / θ ^ 2 < qL := lt_of_lt_of_le hK hK_le_qL
  have hlogL_le : Real.log (L : ℝ) ≤ 4 * qL := by
    have hs1 : Real.log (Real.sqrt (L : ℝ)) = Real.log (L : ℝ) / 2 := Real.log_sqrt hL_pos.le
    have hs2 : Real.log qL = Real.log (Real.sqrt (L : ℝ)) / 2 :=
      Real.log_sqrt (Real.sqrt_nonneg _)
    have hlu : Real.log qL ≤ qL - 1 := Real.log_le_sub_one_of_pos hqL_pos
    linarith
  have hx_le_3L : (x : ℝ) ≤ 3 * (L : ℝ) := by
    have hx_le_2L1 : x ≤ 2 * L + 1 := by
      have : ⌈(x : ℝ) ^ (1 + ε)⌉₊ ≤ 2 * L + 1 := by dsimp [L]; omega
      omega
    have hnat : x ≤ 3 * L := by omega
    exact_mod_cast hnat
  have hlog3_le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlogx_le : Real.log (x : ℝ) ≤ 6 * qL := by
    have h1 : Real.log (x : ℝ) ≤ Real.log (3 * (L : ℝ)) :=
      Real.log_le_log (by exact_mod_cast (show 0 < x by omega)) hx_le_3L
    rw [Real.log_mul (by norm_num) hL_pos.ne'] at h1
    linarith
  have hClogx_le : C * Real.log (x : ℝ) ≤ 6 * C * qL := by nlinarith
  have hgt_mul : 6 * C < (θ ^ 2 / 4) * qL := by
    have hθ2_pos : 0 < θ ^ 2 := sq_pos_of_pos hθ_pos
    have h := (div_lt_iff₀ hθ2_pos).mp hqL_gt
    linarith
  have hstrict : 6 * C * qL < (θ ^ 2 / 4) * Real.sqrt (L : ℝ) := by
    calc
      6 * C * qL < ((θ ^ 2 / 4) * qL) * qL := mul_lt_mul_of_pos_right hgt_mul hqL_pos
      _ = (θ ^ 2 / 4) * (qL * qL) := by ring
      _ = (θ ^ 2 / 4) * Real.sqrt (L : ℝ) := by rw [hqL_sq]
  linarith

end OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1
