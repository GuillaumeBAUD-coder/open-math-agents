import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1

-- Reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1 of Step H2 of Erdos687.erdos_687.parts.iii.R1.H2.R1
-- Credit: @santiemanuel
-- Each H becomes its own step once this file is accepted. Proving all of them closes R1.H2.R1.H2.

/-!
# Ramanujan–Fejér Harmonic Reduction of `Erdos687.erdos_687.parts.iii.R1.H2.R1.H2`

We reduce the short-interval `x`-rough number lower bound
`OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.H2` via discrete Fourier / Ramanujan–Fejér analysis
on `ℤ / Q ℤ` (`Q = ∏_{p ≤ x} p`) to two cleanly decoupled statements:

1. `H1`: **Mertens' third theorem lower bound**:
   `∃ c₀ > 0, ∀ x ≥ 2, c₀ / Real.log x ≤ ∏_{p ≤ x} (1 - 1 / p)` (unconditionally provable via
   Legendre's formula, Chebyshev's bound, and discrete Abel summation).
2. `H2`: **One-sided Ramanujan–Fejér minor-arc cancellation** above the major-arc cutoff
   `D = L / (Nat.log 2 L + 1) ≍ y / log y` (`L = ⌈x ^ (1 + ε)⌉₊ / 2`):
   the minor-arc Ramanujan–Fejér sum over squarefree divisors `d ∣ Q` with `d > D` stays above
   `-θ * L` for some fixed `θ < 1`.

Inside this reduction we prove unconditionally:
- `ramanujan_mul`: Multiplicativity of Ramanujan sums `c(d₁ * d₂, n) = c(d₁, n) * c(d₂, n)`.
- `rough_indicator_eq_ramanujan`: Exact Ramanujan-sum expansion of the `x`-rough indicator
  `1_{∀ p ≤ x, p ∤ n} = V(x) * ∑_{d ∣ Q} (μ(d) / φ(d)) * c(d, n)`.
- `ramanujan_fejer_identity`: Exact Fejér-weighted count of `x`-rough numbers in `[M + 1, M + y]`.
- `fejer_sum_parseval`: Exact Parseval identity
  `∑_{1 ≤ r < d} ‖∑_{u < L} e(r u / d)‖ ^ 2 = (L % d) * (d - L % d) ≤ d ^ 2 / 4`.
- `ramanujan_major_arc_bound`: Complete unconditional discharge of all major arcs `1 < d ≤ D`
  with error at most `3 * D ^ 2 / (4 * L) = o(L)` via `∑_{d ∣ Q, d ≤ D} d / φ(d) ≤ 3 * D`.
-/

namespace OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1

open Filter Finset Real

/-- Mertens' third theorem lower bound: there exists `c₀ > 0` such that
`c₀ / log x ≤ ∏_{p ≤ x} (1 - 1 / p)` for all `x ≥ 2`. -/
def H1 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℕ, 2 ≤ x →
    c₀ / Real.log (x : ℝ) ≤
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)

/-- One-sided Ramanujan–Fejér minor-arc lower bound above the major-arc cutoff
`D = L / (Nat.log 2 L + 1)` (`L = ⌈x ^ (1 + ε)⌉₊ / 2`, `Q = ∏_{p ≤ x} p`):
there exists `θ < 1` such that for every `ε ∈ (0, 1)`, all sufficiently large `x`, and every
shift `M : ℕ`, the minor-arc Ramanujan–Fejér sum over divisors `d ∣ Q` with `d > D` is at
least `-θ * L`. -/
def H2 : Prop :=
  ∃ θ : ℝ, θ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ᶠ x : ℕ in Filter.atTop, ∀ M : ℕ,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊ / 2
      let D := L / (Nat.log 2 L + 1)
      let Q := ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p;
      -(θ * (L : ℝ)) ≤
        ∑ d ∈ Q.divisors.filter (fun d => D < d),
          ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
            ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
              Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                (‖∑ u ∈ Finset.range L,
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                  (L : ℝ))

lemma exp_two_pi_I_int (k : ℤ) :
    Complex.exp (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  have h : ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma sum_exp_int_div {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    ∑ r ∈ range d, Complex.exp (((2 * Real.pi * (r : ℝ) * (m : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) =
      if (d : ℤ) ∣ m then (d : ℂ) else 0 := by
  let w : ℂ := Complex.exp (((2 * Real.pi * (m : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)
  have hterm : ∀ r : ℕ,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (m : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) = w ^ r := by
    intro r
    dsimp [w]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  have hd_r : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  by_cases hdvd : (d : ℤ) ∣ m
  · rw [if_pos hdvd]
    obtain ⟨k, rfl⟩ := hdvd
    have hw1 : w = 1 := by
      dsimp [w]
      have harg : 2 * Real.pi * ((d * k : ℤ) : ℝ) / (d : ℝ) = 2 * Real.pi * (k : ℝ) := by
        push_cast
        field_simp
      rw [harg]
      exact exp_two_pi_I_int k
    simp [hw1]
  · rw [if_neg hdvd]
    have hw_ne1 : w ≠ 1 := by
      intro hw1
      rw [Complex.exp_eq_one_iff] at hw1
      obtain ⟨k, hk⟩ := hw1
      have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
        exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hmul : (((m : ℝ) / (d : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I) =
          ((k : ℝ) : ℂ) * (2 * Real.pi * Complex.I) := by
        calc
          (((m : ℝ) / (d : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
              = ((2 * Real.pi * (m : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
          _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
          _ = ((k : ℝ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; rfl
      have hceq := mul_right_cancel₀ h2piI hmul
      have hreq : (m : ℝ) / (d : ℝ) = (k : ℝ) := Complex.ofReal_injective hceq
      have hmeq_r : (m : ℝ) = ((d : ℤ) * k : ℤ) := by
        push_cast
        rw [← hreq]
        field_simp
      have hmeq : m = (d : ℤ) * k := Int.cast_injective hmeq_r
      exact hdvd ⟨k, hmeq⟩
    rw [geom_sum_eq hw_ne1]
    have hwd : w ^ d = 1 := by
      dsimp [w]
      rw [← Complex.exp_nat_mul]
      have harg : (d : ℂ) * (((2 * Real.pi * (m : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) =
          ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I := by
        have hd_c : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
        push_cast
        field_simp
      rw [harg]
      exact exp_two_pi_I_int m
    rw [hwd, sub_self, zero_div]

private lemma coprime_mod_left_iff {a b : ℕ} : Nat.Coprime (a % b) b ↔ Nat.Coprime a b := by
  rw [Nat.Coprime, Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]

/-- Multiplicativity of Ramanujan sums for coprime moduli `d₁, d₂`. -/
lemma ramanujan_mul {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hcop : Nat.Coprime d₁ d₂) (n : ℕ) :
    (∑ r ∈ (range (d₁ * d₂)).filter (fun r => Nat.Coprime r (d₁ * d₂)),
      Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / ((d₁ * d₂ : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) =
    (∑ r₁ ∈ (range d₁).filter (fun r => Nat.Coprime r d₁),
      Complex.exp (((2 * Real.pi * (r₁ : ℝ) * (n : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I)) *
    (∑ r₂ ∈ (range d₂).filter (fun r => Nat.Coprime r d₂),
      Complex.exp (((2 * Real.pi * (r₂ : ℝ) * (n : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij (fun x : ℕ × ℕ => (x.1 * d₂ + x.2 * d₁) % (d₁ * d₂)) ?_ ?_ ?_ ?_).symm
  · intro x hx
    rw [mem_product, mem_filter, mem_filter] at hx
    have hpos : 0 < d₁ * d₂ := Nat.mul_pos (by omega) (by omega)
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hpos), ?_⟩
    rw [Nat.coprime_mul_iff_right]
    have hmod1 : ((x.1 * d₂ + x.2 * d₁) % (d₁ * d₂)) % d₁ = (x.1 * d₂) % d₁ := by
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_right d₁ d₂), Nat.add_mul_mod_self_right]
    have hmod2 : ((x.1 * d₂ + x.2 * d₁) % (d₁ * d₂)) % d₂ = (x.2 * d₁) % d₂ := by
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_left d₂ d₁), Nat.mul_add_mod_self_right]
    constructor
    · rw [← coprime_mod_left_iff, hmod1, coprime_mod_left_iff]
      exact (Nat.coprime_mul_iff_left.mpr ⟨hx.1.2, hcop.symm⟩)
    · rw [← coprime_mod_left_iff, hmod2, coprime_mod_left_iff]
      exact (Nat.coprime_mul_iff_left.mpr ⟨hx.2.2, hcop⟩)
  · intro x hx y hy hxy
    rw [mem_coe, mem_product, mem_filter, mem_filter] at hx hy
    dsimp only at hxy
    have h1 : x.1 * d₂ ≡ y.1 * d₂ [MOD d₁] := by
      have hm := congrArg (· % d₁) hxy
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_right d₁ d₂), Nat.mod_mod_of_dvd _ (dvd_mul_right d₁ d₂),
        Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at hm
      exact hm
    have hx1y1 : x.1 = y.1 := by
      have hc : x.1 ≡ y.1 [MOD d₁] := Nat.ModEq.cancel_right_of_coprime hcop h1
      have hlt1 : x.1 < d₁ := mem_range.mp hx.1.1
      have hlt2 : y.1 < d₁ := mem_range.mp hy.1.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hc
      exact hc
    have h2 : x.2 * d₁ ≡ y.2 * d₁ [MOD d₂] := by
      have hm := congrArg (· % d₂) hxy
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_left d₂ d₁), Nat.mod_mod_of_dvd _ (dvd_mul_left d₂ d₁),
        Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right] at hm
      exact hm
    have hx2y2 : x.2 = y.2 := by
      have hc : x.2 ≡ y.2 [MOD d₂] := Nat.ModEq.cancel_right_of_coprime hcop.symm h2
      have hlt1 : x.2 < d₂ := mem_range.mp hx.2.1
      have hlt2 : y.2 < d₂ := mem_range.mp hy.2.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hc
      exact hc
    exact Prod.ext hx1y1 hx2y2
  · intro r hr
    rw [mem_coe, mem_filter, mem_range] at hr
    let e₁ := Nat.chineseRemainder hcop 1 0
    let e₂ := Nat.chineseRemainder hcop 0 1
    have he₁_dvd : d₂ ∣ e₁.1 := Nat.dvd_of_mod_eq_zero e₁.2.2
    have he₂_dvd : d₁ ∣ e₂.1 := Nat.dvd_of_mod_eq_zero e₂.2.1
    let r₁ := (r * (e₁.1 / d₂)) % d₁
    let r₂ := (r * (e₂.1 / d₁)) % d₂
    have hr_cop := Nat.coprime_mul_iff_right.mp hr.2
    have hr₁_mod : r₁ * d₂ ≡ r [MOD d₁] := by
      calc
        r₁ * d₂ ≡ (r * (e₁.1 / d₂)) * d₂ [MOD d₁] :=
          Nat.ModEq.mul_right d₂ (Nat.mod_modEq _ d₁)
        _ = r * ((e₁.1 / d₂) * d₂) := by ring
        _ = r * e₁.1 := by rw [Nat.div_mul_cancel he₁_dvd]
        _ ≡ r * 1 [MOD d₁] := Nat.ModEq.mul_left r e₁.2.1
        _ = r := mul_one r
    have hr₂_mod : r₂ * d₁ ≡ r [MOD d₂] := by
      calc
        r₂ * d₁ ≡ (r * (e₂.1 / d₁)) * d₁ [MOD d₂] :=
          Nat.ModEq.mul_right d₁ (Nat.mod_modEq _ d₂)
        _ = r * ((e₂.1 / d₁) * d₁) := by ring
        _ = r * e₂.1 := by rw [Nat.div_mul_cancel he₂_dvd]
        _ ≡ r * 1 [MOD d₂] := Nat.ModEq.mul_left r e₂.2.2
        _ = r := mul_one r
    have hr₁_cop : Nat.Coprime r₁ d₁ := by
      have hcop_prod : Nat.Coprime (r₁ * d₂) d₁ := by
        rw [← coprime_mod_left_iff, hr₁_mod, coprime_mod_left_iff]
        exact hr_cop.1
      exact (Nat.coprime_mul_iff_left.mp hcop_prod).1
    have hr₂_cop : Nat.Coprime r₂ d₂ := by
      have hcop_prod : Nat.Coprime (r₂ * d₁) d₂ := by
        rw [← coprime_mod_left_iff, hr₂_mod, coprime_mod_left_iff]
        exact hr_cop.2
      exact (Nat.coprime_mul_iff_left.mp hcop_prod).1
    have hcomb1 : r₁ * d₂ + r₂ * d₁ ≡ r [MOD d₁] := by
      change (r₁ * d₂ + r₂ * d₁) % d₁ = r % d₁
      rw [Nat.add_mul_mod_self_right]
      exact hr₁_mod
    have hcomb2 : r₁ * d₂ + r₂ * d₁ ≡ r [MOD d₂] := by
      change (r₁ * d₂ + r₂ * d₁) % d₂ = r % d₂
      rw [Nat.mul_add_mod_self_right]
      exact hr₂_mod
    have hcomb : r₁ * d₂ + r₂ * d₁ ≡ r [MOD d₁ * d₂] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hcomb1, hcomb2⟩
    have hmem : (r₁, r₂) ∈ ((range d₁).filter fun r => Nat.Coprime r d₁) ×ˢ
        ((range d₂).filter fun r => Nat.Coprime r d₂) := by
      refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by omega)), hr₁_cop⟩,
        mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by omega)), hr₂_cop⟩⟩
    refine ⟨(r₁, r₂), mem_coe.mpr hmem, ?_⟩
    dsimp only
    rw [Nat.ModEq, Nat.mod_eq_of_lt hr.1] at hcomb
    exact hcomb
  · intro x _
    rw [← Complex.exp_add]
    let q := (x.1 * d₂ + x.2 * d₁) / (d₁ * d₂)
    let r := (x.1 * d₂ + x.2 * d₁) % (d₁ * d₂)
    have hdm : x.1 * d₂ + x.2 * d₁ = d₁ * d₂ * q + r := (Nat.div_add_mod _ _).symm
    have hd₁_r : (d₁ : ℝ) ≠ 0 := by exact_mod_cast (show d₁ ≠ 0 by omega)
    have hd₂_r : (d₂ : ℝ) ≠ 0 := by exact_mod_cast (show d₂ ≠ 0 by omega)
    have harg_r : 2 * Real.pi * (x.1 : ℝ) * (n : ℝ) / (d₁ : ℝ) +
        2 * Real.pi * (x.2 : ℝ) * (n : ℝ) / (d₂ : ℝ) =
        2 * Real.pi * ((q * n : ℕ) : ℝ) +
          2 * Real.pi * (r : ℝ) * (n : ℝ) / ((d₁ * d₂ : ℕ) : ℝ) := by
      have hdm_r : (x.1 : ℝ) * (d₂ : ℝ) + (x.2 : ℝ) * (d₁ : ℝ) =
          (d₁ : ℝ) * (d₂ : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hdm
      push_cast
      field_simp
      nlinarith
    have harg_c : (((2 * Real.pi * (x.1 : ℝ) * (n : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * (x.2 : ℝ) * (n : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * (((q * n : ℕ) : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * (r : ℝ) * (n : ℝ) / ((d₁ * d₂ : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
      have := congrArg (fun t : ℝ => (t : ℂ) * Complex.I) harg_r
      push_cast at this ⊢
      linear_combination this
    rw [harg_c, Complex.exp_add, exp_two_pi_I_int ((q * n : ℕ) : ℤ), one_mul]

private lemma divisors_mul_prime_of_coprime {q Q : ℕ} (hq : q.Prime) (hQ : 0 < Q)
    (_hcop : Nat.Coprime q Q) :
    (q * Q).divisors = Q.divisors ∪ Q.divisors.image (fun d => q * d) := by
  ext d
  simp only [Nat.mem_divisors, mem_union, mem_image]
  have hqQ : q * Q ≠ 0 := Nat.mul_ne_zero hq.ne_zero (by omega)
  constructor
  · rintro ⟨hdvd, _⟩
    by_cases hqd : q ∣ d
    · right
      obtain ⟨d', rfl⟩ := hqd
      refine ⟨d', ⟨?_, by omega⟩, rfl⟩
      exact (Nat.mul_dvd_mul_iff_left hq.pos).mp hdvd
    · left
      have hcop_qd : Nat.Coprime q d := (hq.coprime_iff_not_dvd).mpr hqd
      exact ⟨hcop_qd.symm.dvd_of_dvd_mul_left hdvd, by omega⟩
  · rintro (⟨hdQ, _⟩ | ⟨d', ⟨hd'Q, _⟩, rfl⟩)
    · exact ⟨dvd_mul_of_dvd_right hdQ q, hqQ⟩
    · exact ⟨Nat.mul_dvd_mul_left q hd'Q, hqQ⟩

private lemma disjoint_divisors_mul_prime {q Q : ℕ} (hq : q.Prime) (hcop : Nat.Coprime q Q) :
    Disjoint Q.divisors (Q.divisors.image (fun d => q * d)) := by
  rw [Finset.disjoint_left]
  intro d hdQ hdim
  obtain ⟨d', _, rfl⟩ := mem_image.mp hdim
  have hqQ : q ∣ Q := dvd_trans (dvd_mul_right q d') (Nat.mem_divisors.mp hdQ).1
  have h1 := Nat.dvd_gcd dvd_rfl hqQ
  rw [hcop.gcd_eq_one] at h1
  exact hq.not_dvd_one h1

/-- Exact Ramanujan-sum expansion of the `P`-rough indicator for any finite set of primes `P`. -/
lemma rough_indicator_eq_ramanujan (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (if ∀ p ∈ P, ¬ (p ∣ n) then (1 : ℂ) else 0) =
      (∏ p ∈ P, ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) *
        ∑ d ∈ (∏ p ∈ P, p).divisors,
          (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
            ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
              Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
  induction P using Finset.cons_induction with
  | empty =>
    simp
  | cons q T hqT ih =>
    have hq : q.Prime := hP q (mem_cons_self q T)
    have hT : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_cons_of_mem hp)
    let QT := ∏ p ∈ T, p
    have hQT_pos : 0 < QT := Finset.prod_pos fun p hp => (hT p hp).pos
    have hcop_qQT : Nat.Coprime q QT :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq (hT p hp)).2 (fun heq => hqT (heq ▸ hp))
    -- Single-prime factor identity.
    have hprime_fac :
        (if ¬ (q ∣ n) then (1 : ℂ) else 0) =
          ((1 - (q : ℝ)⁻¹ : ℝ) : ℂ) *
            (1 + (((ArithmeticFunction.moebius q : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
              ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
                Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      have hfilt_q : (range q).filter (fun r => Nat.Coprime r q) = (range q).erase 0 := by
        ext r
        simp only [mem_filter, mem_range, mem_erase]
        constructor
        · rintro ⟨hr, hrc⟩
          refine ⟨?_, hr⟩
          intro hr0
          subst hr0
          rw [Nat.coprime_zero_left] at hrc
          exact hq.ne_one hrc
        · rintro ⟨hr0, hr⟩
          refine ⟨hr, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
          intro hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
      have hsum_full := sum_exp_int_div hq.one_le (n : ℤ)
      have h0mem : 0 ∈ range q := mem_range.mpr hq.pos
      have hsum_split :
          (∑ r ∈ (range q).erase 0,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) + 1 =
          ∑ r ∈ range q,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
        have h := Finset.add_sum_erase (range q)
          (fun r => Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) h0mem
        simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Complex.ofReal_zero,
          Complex.exp_zero] at h
        rw [add_comm] at h
        exact h
      have hsum_ram :
          ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
            Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I) =
          (if q ∣ n then (q : ℂ) else 0) - 1 := by
        rw [hfilt_q]
        have hdiv_iff : ((q : ℤ) ∣ (n : ℤ)) ↔ q ∣ n := Int.ofNat_dvd
        have hfull' :
            ∑ r ∈ range q,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I) =
            if q ∣ n then (q : ℂ) else 0 := by
          simpa [hdiv_iff] using hsum_full
        rw [hfull'] at hsum_split
        exact eq_sub_of_add_eq hsum_split
      rw [hsum_ram, ArithmeticFunction.moebius_apply_prime hq, Nat.totient_prime hq]
      have hq_ne : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hq1_ne : ((q - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show q - 1 ≠ 0 by have := hq.two_le; omega)
      have hq_sub : ((q - 1 : ℕ) : ℂ) = (q : ℂ) - 1 := by
        rw [Nat.cast_sub hq.one_le, Nat.cast_one]
      have hq1_ne' : (q : ℂ) - 1 ≠ 0 := by rwa [hq_sub] at hq1_ne
      by_cases hqn : q ∣ n
      · rw [if_neg (not_not.mpr hqn), if_pos hqn]
        push_cast
        rw [hq_sub]
        field_simp
        ring
      · rw [if_pos hqn, if_neg hqn]
        push_cast
        rw [hq_sub]
        field_simp
        ring
    -- Combine prime `q` with `T`.
    have hind_split :
        (if ∀ p ∈ cons q T hqT, ¬ (p ∣ n) then (1 : ℂ) else 0) =
          (if ¬ (q ∣ n) then (1 : ℂ) else 0) * (if ∀ p ∈ T, ¬ (p ∣ n) then (1 : ℂ) else 0) := by
      simp only [mem_cons, forall_eq_or_imp]
      by_cases h1 : ¬ (q ∣ n) <;> by_cases h2 : ∀ p ∈ T, ¬ (p ∣ n) <;> simp [h1, h2]
    rw [hind_split, hprime_fac, ih hT, Finset.prod_cons hqT, Finset.prod_cons hqT]
    have hmul_rearr :
        ((1 - (q : ℝ)⁻¹ : ℝ) : ℂ) *
          (1 + (((ArithmeticFunction.moebius q : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
            ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
              Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) *
          ((∏ p ∈ T, ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) *
            ∑ d ∈ QT.divisors,
              (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
                ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (((1 - (q : ℝ)⁻¹ : ℝ) : ℂ) * ∏ p ∈ T, ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) *
          ((∑ d ∈ QT.divisors,
              (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
                ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)) +
            ∑ d ∈ QT.divisors,
              ((((ArithmeticFunction.moebius q : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
                (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ)) *
                ((∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) *
                  (∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)))) := by
      have hsum_eq :
          (((ArithmeticFunction.moebius q : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
            (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
              Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) *
            (∑ d ∈ QT.divisors,
              (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
                ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)) =
          ∑ d ∈ QT.divisors,
            ((((ArithmeticFunction.moebius q : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) *
              (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ)) *
              ((∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) *
                (∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [← hsum_eq]
      ring
    rw [show (∏ p ∈ T, p) = QT from rfl, hmul_rearr]
    congr 1
    rw [divisors_mul_prime_of_coprime hq hQT_pos hcop_qQT,
      Finset.sum_union (disjoint_divisors_mul_prime hq hcop_qQT)]
    congr 1
    rw [Finset.sum_image (fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hq.pos h)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hQT_pos
    have hcop_qd : Nat.Coprime q d :=
      hcop_qQT.coprime_dvd_right (Nat.mem_divisors.mp hd).1
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_qd,
      Nat.totient_mul hcop_qd, ramanujan_mul hq.one_le hd_pos hcop_qd n]
    push_cast
    ring

/-- Exact Ramanujan–Fejér Fourier identity for `x`-rough numbers in `[M + 1, M + 2 * L - 1]`. -/
lemma ramanujan_fejer_identity (x M L : ℕ) (hL : 1 ≤ L) :
    let Q := ∏ p ∈ (range (x + 1)).filter Nat.Prime, p
    (∑ u ∈ range L, ∑ v ∈ range L,
      (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℝ) else 0)) / (L : ℝ) =
    (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) *
      ∑ d ∈ Q.divisors,
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
              (‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ)) := by
  intro Q
  let P := (range (x + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  -- Establish the unnormalized identity in `ℂ` and take `Complex.re`.
  have hind_iff : ∀ n : ℕ,
      (∀ p ≤ x, p.Prime → ¬ (p ∣ n)) ↔ (∀ p ∈ P, ¬ (p ∣ n)) := by
    intro n
    simp only [P, mem_filter, mem_range]
    constructor
    · intro h p ⟨hpx, hpp⟩; exact h p (by omega) hpp
    · intro h p hpx hpp; exact h p ⟨by omega, hpp⟩
  have hsum_c :
      (∑ u ∈ range L, ∑ v ∈ range L,
        (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℂ) else 0)) =
      (∏ p ∈ P, ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) *
        ∑ d ∈ Q.divisors,
          (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
            ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
              Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) *
                ((‖∑ u ∈ range L,
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
    have hstep1 :
        (∑ u ∈ range L, ∑ v ∈ range L,
          (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℂ) else 0)) =
        (∏ p ∈ P, ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) *
          ∑ d ∈ Q.divisors,
            (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
              ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                ∑ u ∈ range L, ∑ v ∈ range L,
                  Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L + u - v : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
      have hrw : ∀ u v : ℕ,
          (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℂ) else 0) =
          (∏ p ∈ P, ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) *
            ∑ d ∈ Q.divisors,
              (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
                ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                  Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L + u - v : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
        intro u v
        simp_rw [hind_iff]
        exact rough_indicator_eq_ramanujan P hP (M + L + u - v)
      simp_rw [hrw, ← Finset.mul_sum]
      congr 1
      trans (∑ d ∈ Q.divisors, ∑ u ∈ range L, ∑ v ∈ range L,
        (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
          ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
            Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L + u - v : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I))
      · trans (∑ u ∈ range L, ∑ d ∈ Q.divisors, ∑ v ∈ range L,
          (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
            ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
              Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L + u - v : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I))
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        · exact Finset.sum_comm
      · refine Finset.sum_congr rfl fun d _ => ?_
        simp_rw [← Finset.mul_sum]
        congr 1
        trans (∑ u ∈ range L, ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d), ∑ v ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L + u - v : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I))
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        · exact Finset.sum_comm
    rw [hstep1]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    have hsplit_uv :
        ∑ u ∈ range L, ∑ v ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L + u - v : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) *
          ((∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)) *
          (∑ v ∈ range L,
            Complex.exp (((-(2 * Real.pi * (r : ℝ) * (v : ℝ) / (d : ℝ)) : ℝ) : ℂ) * Complex.I))) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv_lt : v < L := mem_range.mp hv
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have hsub_r : ((M + L + u - v : ℕ) : ℝ) = ((M + L : ℕ) : ℝ) + (u : ℝ) - (v : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hsub_r]
      push_cast
      ring
    rw [hsplit_uv]
    congr 1
    have hconj :
        (∑ v ∈ range L,
          Complex.exp (((-(2 * Real.pi * (r : ℝ) * (v : ℝ) / (d : ℝ)) : ℝ) : ℂ) * Complex.I)) =
        starRingEnd ℂ (∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      congr 1
      push_cast
      ring
    rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre := congrArg Complex.re hsum_c
  have hlhs_re :
      (∑ u ∈ range L, ∑ v ∈ range L,
        (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℂ) else 0)).re =
      ∑ u ∈ range L, ∑ v ∈ range L,
        (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℝ) else 0) := by
    simp [Complex.re_sum]
  have hrhs_re :
      ((∏ p ∈ P, ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ)) *
        ∑ d ∈ Q.divisors,
          (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ) : ℝ) : ℂ) *
            ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
              Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) *
                ((‖∑ u ∈ range L,
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)).re =
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) *
        ∑ d ∈ Q.divisors,
          ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
            ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
              Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                ‖∑ u ∈ range L,
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    rw [← Complex.ofReal_prod, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  rw [hlhs_re, hrhs_re] at hre
  rw [hre, mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- Exact Parseval variance bound for the Fejér exponential sum over `1 ≤ r < d`. -/
lemma fejer_sum_parseval {d L : ℕ} (hd : 1 ≤ d) :
    ∑ r ∈ (range d).filter (fun r => r ≠ 0),
      ‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      (d : ℝ) ^ 2 / 4 := by
  -- Full Parseval sum over `r ∈ range d` equals `d * #{(u, v) ∈ (range L)^2 | u ≡ v [MOD d]}`.
  have hfull_c :
      (∑ r ∈ range d,
        ((‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)) =
      (d : ℂ) * ∑ u ∈ range L, ∑ v ∈ range L, (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℂ) else 0) := by
    have hnorm : ∀ r ∈ range d,
        ((‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
        ∑ u ∈ range L, ∑ v ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (((u : ℤ) - (v : ℤ) : ℤ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
      intro r _
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl hnorm]
    trans (∑ u ∈ range L, ∑ v ∈ range L, ∑ r ∈ range d,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (((u : ℤ) - (v : ℤ) : ℤ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I))
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
    · simp_rw [sum_exp_int_div hd]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> simp
  -- Count pairs `(u, v)` with `u ≡ v [MOD d]` by residue class `m ∈ range d`.
  have hpair_count :
      (∑ u ∈ range L, ∑ v ∈ range L, (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℝ) else 0)) =
      ((L % d : ℕ) : ℝ) * (((L / d + 1 : ℕ) : ℝ) ^ 2) +
        ((d - L % d : ℕ) : ℝ) * (((L / d : ℕ) : ℝ) ^ 2) := by
    have hdiv_iff : ∀ u v : ℕ, ((d : ℤ) ∣ ((u : ℤ) - (v : ℤ))) ↔ u % d = v % d := by
      intro u v
      rw [← Int.modEq_iff_dvd, Int.natCast_modEq_iff, Nat.ModEq, eq_comm]
    simp_rw [hdiv_iff]
    let cnt : ℕ → ℕ := fun m => ((range L).filter fun u => u % d = m).card
    have hsum_sq :
        (∑ u ∈ range L, ∑ v ∈ range L, (if u % d = v % d then (1 : ℝ) else 0)) =
        ∑ m ∈ range d, ((cnt m : ℝ) ^ 2) := by
      have h1 : ∀ u ∈ range L,
          (∑ v ∈ range L, (if u % d = v % d then (1 : ℝ) else 0)) = (cnt (u % d) : ℝ) := by
        intro u _
        dsimp [cnt]
        rw [Finset.sum_boole]
        congr 2
        ext v
        simp only [mem_filter]
        exact and_congr_right fun _ => eq_comm
      rw [Finset.sum_congr rfl h1]
      have hpart : range L = (range d).biUnion (fun m => (range L).filter fun u => u % d = m) := by
        ext u
        simp only [mem_biUnion, mem_range, mem_filter]
        constructor
        · intro hu; exact ⟨u % d, Nat.mod_lt u (by omega), hu, rfl⟩
        · rintro ⟨_, _, hu, _⟩; exact hu
      have hpw : (range d : Set ℕ).PairwiseDisjoint (fun m => (range L).filter fun u => u % d = m) := by
        intro m₁ _ m₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu₁ hu₂
        exact hne ((mem_filter.mp hu₁).2.symm.trans (mem_filter.mp hu₂).2)
      conv_lhs => rw [hpart]
      rw [Finset.sum_biUnion hpw]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hconst : ∑ u ∈ (range L).filter (fun u => u % d = m), (cnt (u % d) : ℝ) =
          ∑ _u ∈ (range L).filter (fun u => u % d = m), (cnt m : ℝ) :=
        Finset.sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2]
      rw [hconst, Finset.sum_const, nsmul_eq_mul, sq]
    have hcnt_lt : ∀ m < L % d, cnt m = L / d + 1 := by
      intro m hm
      have hm_d : m < d := hm.trans (Nat.mod_lt L (by omega))
      dsimp [cnt]
      have himg : (range L).filter (fun u => u % d = m) =
          (range (L / d + 1)).image (fun j => j * d + m) := by
        ext u
        simp only [mem_filter, mem_range, mem_image]
        constructor
        · rintro ⟨huL, hum⟩
          refine ⟨u / d, ?_, by rw [Nat.mul_comm, ← hum]; exact Nat.div_add_mod u d⟩
          have hdm1 : d * (u / d) + m = u := by rw [← hum]; exact Nat.div_add_mod u d
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          have hml := Nat.mod_lt L (by omega : 0 < d)
          by_contra hge
          push Not at hge
          have : d * (L / d + 1) ≤ d * (u / d) := Nat.mul_le_mul_left d hge
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
        · rintro ⟨j, hj, rfl⟩
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          have hmul : j * d ≤ d * (L / d) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left d (by omega)
          refine ⟨by omega, ?_⟩
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hm_d]
      rw [himg, Finset.card_image_of_injective _ (fun j₁ j₂ h =>
        Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)), Finset.card_range]
    have hcnt_ge : ∀ m, L % d ≤ m → m < d → cnt m = L / d := by
      intro m hm1 hm2
      dsimp [cnt]
      have himg : (range L).filter (fun u => u % d = m) =
          (range (L / d)).image (fun j => j * d + m) := by
        ext u
        simp only [mem_filter, mem_range, mem_image]
        constructor
        · rintro ⟨huL, hum⟩
          refine ⟨u / d, ?_, by rw [Nat.mul_comm, ← hum]; exact Nat.div_add_mod u d⟩
          have hdm1 : d * (u / d) + m = u := by rw [← hum]; exact Nat.div_add_mod u d
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          by_contra hge
          push Not at hge
          have : d * (L / d) ≤ d * (u / d) := Nat.mul_le_mul_left d hge
          omega
        · rintro ⟨j, hj, rfl⟩
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          have hmul : (j + 1) * d ≤ d * (L / d) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left d (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hmul
          refine ⟨by omega, ?_⟩
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hm2]
      rw [himg, Finset.card_image_of_injective _ (fun j₁ j₂ h =>
        Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)), Finset.card_range]
    rw [hsum_sq]
    have hsplit : range d = range (L % d) ∪ Ico (L % d) d := by
      ext m
      simp only [mem_range, mem_union, mem_Ico]
      have := Nat.mod_lt L (by omega : 0 < d)
      omega
    have hdisj : Disjoint (range (L % d)) (Ico (L % d) d) := by
      rw [Finset.disjoint_left]
      intro m h1 h2
      have := mem_range.mp h1
      have := (mem_Ico.mp h2).1
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hs1 : ∑ m ∈ range (L % d), ((cnt m : ℝ) ^ 2) =
        ((L % d : ℕ) : ℝ) * (((L / d + 1 : ℕ) : ℝ) ^ 2) := by
      have hc : ∑ m ∈ range (L % d), ((cnt m : ℝ) ^ 2) =
          ∑ _m ∈ range (L % d), (((L / d + 1 : ℕ) : ℝ) ^ 2) :=
        Finset.sum_congr rfl fun m hm => by rw [hcnt_lt m (mem_range.mp hm)]
      rw [hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hs2 : ∑ m ∈ Ico (L % d) d, ((cnt m : ℝ) ^ 2) =
        ((d - L % d : ℕ) : ℝ) * (((L / d : ℕ) : ℝ) ^ 2) := by
      have hc : ∑ m ∈ Ico (L % d) d, ((cnt m : ℝ) ^ 2) =
          ∑ _m ∈ Ico (L % d) d, (((L / d : ℕ) : ℝ) ^ 2) :=
        Finset.sum_congr rfl fun m hm => by
          have hm' := mem_Ico.mp hm
          rw [hcnt_ge m hm'.1 hm'.2]
      rw [hc, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [hs1, hs2]
  -- Extract real part of `hfull_c` and subtract the `r = 0` term `L ^ 2`.
  have hfull_r :
      (∑ r ∈ range d,
        ‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
      (d : ℝ) * (((L % d : ℕ) : ℝ) * (((L / d + 1 : ℕ) : ℝ) ^ 2) +
        ((d - L % d : ℕ) : ℝ) * (((L / d : ℕ) : ℝ) ^ 2)) := by
    have hre := congrArg Complex.re hfull_c
    rw [Complex.re_sum, ← Complex.ofReal_natCast, Complex.re_ofReal_mul] at hre
    simp only [Complex.ofReal_re, Complex.re_sum, apply_ite Complex.re,
      Complex.one_re, Complex.zero_re] at hre
    rw [hre, hpair_count]
  have hfilt_eq : (range d).filter (fun r => r ≠ 0) = (range d).erase 0 := by
    ext r
    simp only [mem_filter, mem_erase, mem_range]
    tauto
  have h0_term :
      ‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * ((0 : ℕ) : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      (L : ℝ) ^ 2 := by
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Complex.ofReal_zero, Complex.exp_zero,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  have hsplit0 := Finset.add_sum_erase (range d)
    (fun r => ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2)
    (show 0 ∈ range d from mem_range.mpr (by omega))
  rw [h0_term, hfull_r] at hsplit0
  have hrem_eq :
      ∑ r ∈ (range d).filter (fun r => r ≠ 0),
        ‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      ((L % d : ℕ) : ℝ) * ((d : ℝ) - ((L % d : ℕ) : ℝ)) := by
    rw [hfilt_eq]
    have hdm_r : (L : ℝ) = (d : ℝ) * ((L / d : ℕ) : ℝ) + ((L % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod L d).symm
    have hsub_r : ((d - L % d : ℕ) : ℝ) = (d : ℝ) - ((L % d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.mod_lt L (by omega)).le]
    rw [hsub_r, Nat.cast_add, Nat.cast_one] at hsplit0
    nlinarith
  rw [hrem_eq]
  nlinarith [sq_nonneg (2 * ((L % d : ℕ) : ℝ) - (d : ℝ))]

private lemma divisors_properties_of_prime_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    let Q := ∏ p ∈ P, p
    (∀ d ∈ Q.divisors, |(ArithmeticFunction.moebius d : ℝ)| ≤ 1) ∧
    (∀ d ∈ Q.divisors, (d : ℝ) / (Nat.totient d : ℝ) = ∑ k ∈ d.divisors, (Nat.totient k : ℝ)⁻¹) ∧
    (∑ k ∈ Q.divisors, ((k : ℝ) * (Nat.totient k : ℝ))⁻¹ =
      ∏ p ∈ P, (1 + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹)) := by
  induction P using Finset.cons_induction with
  | empty =>
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      simp only [Finset.prod_empty, Nat.divisors_one, mem_singleton] at hd
      subst hd
      simp
    · intro d hd
      simp only [Finset.prod_empty, Nat.divisors_one, mem_singleton] at hd
      subst hd
      simp
    · simp
  | cons q T hqT ih =>
    have hq : q.Prime := hP q (mem_cons_self q T)
    have hT : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_cons_of_mem hp)
    obtain ⟨ih_mob, ih_tot, ih_sum⟩ := ih hT
    let QT := ∏ p ∈ T, p
    have hQT_pos : 0 < QT := Finset.prod_pos fun p hp => (hT p hp).pos
    have hcop_qQT : Nat.Coprime q QT :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq (hT p hp)).2 (fun heq => hqT (heq ▸ hp))
    have hQ_eq : ∏ p ∈ cons q T hqT, p = q * QT := Finset.prod_cons hqT
    have hdiv_eq := divisors_mul_prime_of_coprime hq hQT_pos hcop_qQT
    have hdiv_disj := disjoint_divisors_mul_prime hq hcop_qQT
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      rw [hQ_eq, hdiv_eq, mem_union] at hd
      rcases hd with hdT | hdim
      · exact ih_mob d hdT
      · obtain ⟨d', hd'T, rfl⟩ := mem_image.mp hdim
        have hcop_qd' : Nat.Coprime q d' := hcop_qQT.coprime_dvd_right (Nat.mem_divisors.mp hd'T).1
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_qd',
          ArithmeticFunction.moebius_apply_prime hq]
        push_cast
        rw [abs_mul, abs_neg, abs_one, one_mul]
        exact ih_mob d' hd'T
    · intro d hd
      rw [hQ_eq, hdiv_eq, mem_union] at hd
      rcases hd with hdT | hdim
      · exact ih_tot d hdT
      · obtain ⟨d', hd'T, rfl⟩ := mem_image.mp hdim
        have hd'_pos : 0 < d' := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd'T).1 hQT_pos
        have hcop_qd' : Nat.Coprime q d' := hcop_qQT.coprime_dvd_right (Nat.mem_divisors.mp hd'T).1
        rw [Nat.totient_mul hcop_qd', Nat.totient_prime hq,
          divisors_mul_prime_of_coprime hq hd'_pos hcop_qd',
          Finset.sum_union (disjoint_divisors_mul_prime hq hcop_qd'),
          Finset.sum_image (fun k₁ _ k₂ _ h => Nat.eq_of_mul_eq_mul_left hq.pos h)]
        have hsum2 : ∑ k ∈ d'.divisors, (Nat.totient (q * k) : ℝ)⁻¹ =
            ((q - 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ d'.divisors, (Nat.totient k : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hcop_qk : Nat.Coprime q k := hcop_qd'.coprime_dvd_right (Nat.mem_divisors.mp hk).1
          rw [Nat.totient_mul hcop_qk, Nat.totient_prime hq, Nat.cast_mul, mul_inv]
        rw [hsum2, ← ih_tot d' hd'T]
        have hq1_ne : ((q - 1 : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (show q - 1 ≠ 0 by have := hq.two_le; omega)
        have hq_sub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub hq.one_le, Nat.cast_one]
        push_cast
        rw [hq_sub]
        have hq1_ne' : (q : ℝ) - 1 ≠ 0 := by rwa [hq_sub] at hq1_ne
        have htd'_ne : (Nat.totient d' : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr hd'_pos).ne'
        field_simp
        ring
    · rw [hQ_eq, hdiv_eq, Finset.sum_union hdiv_disj,
        Finset.sum_image (fun k₁ _ k₂ _ h => Nat.eq_of_mul_eq_mul_left hq.pos h),
        Finset.prod_cons hqT]
      have hsum2 : ∑ k ∈ QT.divisors, (((q * k : ℕ) : ℝ) * (Nat.totient (q * k) : ℝ))⁻¹ =
          ((q : ℝ) * ((q - 1 : ℕ) : ℝ))⁻¹ * ∑ k ∈ QT.divisors, ((k : ℝ) * (Nat.totient k : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hcop_qk : Nat.Coprime q k := hcop_qQT.coprime_dvd_right (Nat.mem_divisors.mp hk).1
        rw [Nat.totient_mul hcop_qk, Nat.totient_prime hq]
        push_cast
        ring
      rw [hsum2, ih_sum]
      ring

/-- Unconditional major-arc Ramanujan–Fejér bound over all squarefree divisors `1 < d ≤ D`. -/
lemma ramanujan_major_arc_bound (x M L D : ℕ) (hL : 1 ≤ L) :
    let Q := ∏ p ∈ (range (x + 1)).filter Nat.Prime, p
    |∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D),
      ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))| ≤
    3 * (D : ℝ) ^ 2 / (4 * (L : ℝ)) := by
  intro Q
  let P := (range (x + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have hQ_pos : 0 < Q := Finset.prod_pos fun p hp => (hP p hp).pos
  obtain ⟨hmob, htot_eq, hsum_inv⟩ := divisors_properties_of_prime_prod P hP
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  -- Step 1: Bound each `d`-term using `|μ(d)| ≤ 1`, `|cos| ≤ 1`, and `fejer_sum_parseval`.
  have hterm_d : ∀ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D),
      |((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))| ≤
      ((D : ℝ) / (4 * (L : ℝ))) * ((d : ℝ) / (Nat.totient d : ℝ)) := by
    intro d hd
    have hdQ : d ∈ Q.divisors := (mem_filter.mp hd).1
    have hd1 : 1 < d := (mem_filter.mp hd).2.1
    have hdD : d ≤ D := (mem_filter.mp hd).2.2
    have hphi_pos : (0 : ℝ) < (Nat.totient d : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hinner :
        |∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))| ≤
        (d : ℝ) ^ 2 / (4 * (L : ℝ)) := by
      calc
        |∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
              (‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ))|
            ≤ ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                |Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                  (‖∑ u ∈ range L,
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                    (L : ℝ))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
              ‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ) := by
          refine Finset.sum_le_sum fun r _ => ?_
          have hterm_nn :
              0 ≤ ‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ) := by positivity
          rw [abs_mul, abs_of_nonneg hterm_nn]
          exact mul_le_of_le_one_left hterm_nn (Real.abs_cos_le_one _)
        _ ≤ ∑ r ∈ (range d).filter (fun r => r ≠ 0),
              ‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro r hr
          obtain ⟨hr_rng, hr_cop⟩ := mem_filter.mp hr
          refine mem_filter.mpr ⟨hr_rng, fun hr0 => ?_⟩
          subst hr0
          rw [Nat.coprime_zero_left] at hr_cop
          omega
        _ = (∑ r ∈ (range d).filter (fun r => r ≠ 0),
              ‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2) /
              (L : ℝ) := (Finset.sum_div _ _ _).symm
        _ ≤ ((d : ℝ) ^ 2 / 4) / (L : ℝ) :=
          div_le_div_of_nonneg_right (fejer_sum_parseval (by omega)) hL_pos.le
        _ = (d : ℝ) ^ 2 / (4 * (L : ℝ)) := by ring
    rw [abs_mul, abs_div, abs_of_pos hphi_pos]
    have hcoeff : |(ArithmeticFunction.moebius d : ℝ)| / (Nat.totient d : ℝ) ≤
        1 / (Nat.totient d : ℝ) :=
      div_le_div_of_nonneg_right (hmob d hdQ) hphi_pos.le
    calc
      (|(ArithmeticFunction.moebius d : ℝ)| / (Nat.totient d : ℝ)) *
          |∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
              (‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ))|
          ≤ (1 / (Nat.totient d : ℝ)) * ((d : ℝ) ^ 2 / (4 * (L : ℝ))) :=
        mul_le_mul hcoeff hinner (abs_nonneg _) (by positivity)
      _ = ((d : ℝ) / (4 * (L : ℝ))) * ((d : ℝ) / (Nat.totient d : ℝ)) := by ring
      _ ≤ ((D : ℝ) / (4 * (L : ℝ))) * ((d : ℝ) / (Nat.totient d : ℝ)) := by
        have hdD_r : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
        gcongr
  -- Step 2: Bound `∑_{d ∣ Q, d ≤ D} d / φ(d) ≤ 3 * D`.
  have hsum_d_phi :
      ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), (d : ℝ) / (Nat.totient d : ℝ) ≤
        3 * (D : ℝ) := by
    have h1 : ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), (d : ℝ) / (Nat.totient d : ℝ) ≤
        ∑ d ∈ Q.divisors.filter (fun d => d ≤ D), (d : ℝ) / (Nat.totient d : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro d hd
      have h := mem_filter.mp hd
      exact mem_filter.mpr ⟨h.1, h.2.2⟩
    have h2 : ∑ d ∈ Q.divisors.filter (fun d => d ≤ D), (d : ℝ) / (Nat.totient d : ℝ) =
        ∑ d ∈ Q.divisors.filter (fun d => d ≤ D), ∑ k ∈ d.divisors, (Nat.totient k : ℝ)⁻¹ :=
      Finset.sum_congr rfl fun d hd => htot_eq d (mem_filter.mp hd).1
    have h3 : ∑ d ∈ Q.divisors.filter (fun d => d ≤ D), ∑ k ∈ d.divisors, (Nat.totient k : ℝ)⁻¹ ≤
        ∑ k ∈ Q.divisors, (((Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d)).card : ℝ) * (Nat.totient k : ℝ)⁻¹) := by
      have hswap :
          ∑ d ∈ Q.divisors.filter (fun d => d ≤ D), ∑ k ∈ d.divisors, (Nat.totient k : ℝ)⁻¹ =
          ∑ k ∈ Q.divisors,
            ∑ d ∈ Q.divisors.filter (fun d => d ≤ D),
              if k ∈ d.divisors then (Nat.totient k : ℝ)⁻¹ else 0 := by
        trans (∑ d ∈ Q.divisors.filter (fun d => d ≤ D), ∑ k ∈ Q.divisors,
          if k ∈ d.divisors then (Nat.totient k : ℝ)⁻¹ else 0)
        · refine Finset.sum_congr rfl fun d hd => ?_
          rw [← Finset.sum_filter]
          congr 1
          ext k
          simp only [mem_filter, Nat.mem_divisors]
          have hdQ := Nat.mem_divisors.mp (mem_filter.mp hd).1
          constructor
          · rintro ⟨hkd, hdn⟩; exact ⟨⟨dvd_trans hkd hdQ.1, hdQ.2⟩, hkd, hdn⟩
          · rintro ⟨_, hkd, hdn⟩; exact ⟨hkd, hdn⟩
        · exact Finset.sum_comm
      rw [hswap]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hsub : (Q.divisors.filter fun d => d ≤ D).filter (fun d => k ∈ d.divisors) ⊆
          Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d) := by
        intro d hd
        have h1 := mem_filter.mp hd
        have h2 := mem_filter.mp h1.1
        exact mem_filter.mpr ⟨h2.1, h2.2, (Nat.mem_divisors.mp h1.2).1⟩
      exact_mod_cast Finset.card_le_card hsub
    have h4 : ∑ k ∈ Q.divisors,
        (((Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d)).card : ℝ) * (Nat.totient k : ℝ)⁻¹) ≤
        (D : ℝ) * ∑ k ∈ Q.divisors, ((k : ℝ) * (Nat.totient k : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hk).1 hQ_pos
      have hcard_le : (Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d)).card ≤ D / k := by
        have himg : Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d) ⊆
            (Icc 1 (D / k)).image (fun m => k * m) := by
          intro d hd
          have h := mem_filter.mp hd
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h.1).1 hQ_pos
          obtain ⟨m, rfl⟩ := h.2.2
          refine mem_image.mpr ⟨m, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
          · exact Nat.pos_of_ne_zero fun hm0 => by rw [hm0, mul_zero] at hd_pos; omega
          · exact (Nat.le_div_iff_mul_le hk_pos).mpr (by rw [Nat.mul_comm]; exact h.2.1)
        exact (Finset.card_le_card himg).trans ((Finset.card_image_le).trans (by simp))
      have hcard_r : ((Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d)).card : ℝ) ≤ (D : ℝ) / (k : ℝ) := by
        have h1 : ((Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d)).card : ℝ) ≤ ((D / k : ℕ) : ℝ) := by
          exact_mod_cast hcard_le
        have h2 : ((D / k : ℕ) : ℝ) ≤ (D : ℝ) / (k : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast hk_pos)]
          exact_mod_cast Nat.div_mul_le_self D k
        exact h1.trans h2
      calc
        ((Q.divisors.filter (fun d => d ≤ D ∧ k ∣ d)).card : ℝ) * (Nat.totient k : ℝ)⁻¹
            ≤ ((D : ℝ) / (k : ℝ)) * (Nat.totient k : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard_r (by positivity)
        _ = (D : ℝ) * ((k : ℝ) * (Nat.totient k : ℝ))⁻¹ := by
          rw [div_eq_mul_inv, mul_assoc, mul_inv]
    have hprod_le_3 : ∏ p ∈ P, (1 + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) ≤ 3 := by
      have htele : ∑ n ∈ Icc 2 (max 2 x), ((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
        have hstep : ∀ m : ℕ, 1 ≤ m →
            ∑ n ∈ Icc 2 (m + 1), ((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹ = 1 - ((m + 1 : ℕ) : ℝ)⁻¹ := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => norm_num
          | succ k hk ih =>
            rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1 + 1), ih]
            have hsub : k + 1 + 1 - 1 = k + 1 := by omega
            rw [hsub]
            have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hk2 : ((k + 1 + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            push_cast
            field_simp
            ring
        have hmx : 1 ≤ max 2 x - 1 := by omega
        have heq := hstep (max 2 x - 1) hmx
        have hadd : max 2 x - 1 + 1 = max 2 x := by omega
        rw [hadd] at heq
        rw [heq]
        have hnn : (0 : ℝ) ≤ ((max 2 x : ℕ) : ℝ)⁻¹ := by positivity
        linarith
      have hP_sub : P ⊆ Icc 2 (max 2 x) := by
        intro p hp
        have h := mem_filter.mp hp
        have hr := mem_range.mp h.1
        exact mem_Icc.mpr ⟨h.2.two_le, by omega⟩
      have hsum_P : ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤ 1 :=
        (Finset.sum_le_sum_of_subset_of_nonneg hP_sub (fun _ _ _ => by positivity)).trans htele
      have hexp : ∏ p ∈ P, (1 + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) ≤
          Real.exp (∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by
        rw [Real.exp_sum]
        apply Finset.prod_le_prod
        · intro _ _; positivity
        · intro p _; linarith [Real.add_one_le_exp (((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹)]
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact hexp.trans ((Real.exp_le_exp.mpr hsum_P).trans he1)
    calc
      ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), (d : ℝ) / (Nat.totient d : ℝ)
          ≤ (D : ℝ) * ∑ k ∈ Q.divisors, ((k : ℝ) * (Nat.totient k : ℝ))⁻¹ :=
        h1.trans ((h2.le.trans h3).trans h4)
      _ = (D : ℝ) * ∏ p ∈ P, (1 + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by rw [hsum_inv]
      _ ≤ (D : ℝ) * 3 := mul_le_mul_of_nonneg_left hprod_le_3 (Nat.cast_nonneg D)
      _ = 3 * (D : ℝ) := mul_comm _ _
  calc
    |∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D),
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
              (‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ))|
        ≤ ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D),
            |((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
              ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
                Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                  (‖∑ u ∈ range L,
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                    (L : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D),
          ((D : ℝ) / (4 * (L : ℝ))) * ((d : ℝ) / (Nat.totient d : ℝ)) :=
      Finset.sum_le_sum hterm_d
    _ = ((D : ℝ) / (4 * (L : ℝ))) *
          ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), (d : ℝ) / (Nat.totient d : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((D : ℝ) / (4 * (L : ℝ))) * (3 * (D : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum_d_phi (by positivity)
    _ = 3 * (D : ℝ) ^ 2 / (4 * (L : ℝ)) := by ring

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.H2 := by
  intro hH1 hH2
  obtain ⟨c₀, hc₀_pos, hMertens⟩ := hH1
  obtain ⟨θ, hθ_lt1, hMinor⟩ := hH2
  have h1θ_pos : 0 < 1 - θ := by linarith
  let c : ℝ := c₀ * (1 - θ) / 6
  refine ⟨c, by dsimp [c]; positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 / (1 - θ))
  let N₁ := max 2 N₀
  filter_upwards [eventually_ge_atTop (max 4 (2 ^ (N₁ + 1))), hMinor ε hε hε1] with x hx hMin M
  intro y
  have hx4 : 4 ≤ x := le_trans (le_max_left _ _) hx
  have hxN : 2 ^ (N₁ + 1) ≤ x := le_trans (le_max_right _ _) hx
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hx_le_y : x ≤ y := by
    have h1 : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
      calc
        (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (x : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
    exact_mod_cast h1.trans (Nat.le_ceil _)
  let L := y / 2
  let D := L / (Nat.log 2 L + 1)
  let Q := ∏ p ∈ (range (x + 1)).filter Nat.Prime, p
  have hL_ge2 : 2 ≤ L := by dsimp [L]; omega
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have h2L_le_y : 2 * L ≤ y := by dsimp [L]; omega
  have hy_le_3L : (y : ℝ) / 3 ≤ (L : ℝ) := by
    have : y ≤ 3 * L := by dsimp [L]; omega
    have h_r : (y : ℝ) ≤ 3 * (L : ℝ) := by exact_mod_cast this
    linarith
  have hD_ge1 : 1 ≤ D := by
    dsimp [D]
    have hlt : Nat.log 2 L < L := Nat.log_lt_self 2 (by omega)
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlogL_ge : N₁ ≤ Nat.log 2 L + 1 := by
    have hL_ge_pow : 2 ^ N₁ ≤ L := by
      have : 2 * 2 ^ N₁ ≤ x := by rw [← pow_succ']; exact hxN
      dsimp [L]
      omega
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hL_ge_pow
    omega
  -- Step 1: Fejér average is at most the `x`-rough count in `[M + 1, M + y]`.
  have hfejer_le_card :
      (∑ u ∈ range L, ∑ v ∈ range L,
        (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℝ) else 0)) / (L : ℝ) ≤
      (((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ) := by
    rw [div_le_iff₀ hL_pos]
    calc
      ∑ u ∈ range L, ∑ v ∈ range L,
          (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℝ) else 0)
          ≤ ∑ _u ∈ range L,
              (((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ) := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hu_lt : u < L := mem_range.mp hu
        rw [Finset.sum_boole]
        have hcard : ((range L).filter fun v => ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v))).card ≤
            ((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card := by
          refine Finset.card_le_card_of_injOn (fun v => M + L + u - v) ?_ ?_
          · intro v hv
            rw [mem_coe, mem_filter, mem_range] at hv
            dsimp only
            rw [mem_coe, mem_filter, mem_Icc]
            exact ⟨⟨by omega, by omega⟩, hv.2⟩
          · intro v₁ hv₁ v₂ hv₂ heq
            rw [mem_coe, mem_filter, mem_range] at hv₁ hv₂
            dsimp only at heq
            omega
        exact_mod_cast hcard
      _ = (((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ) * (L : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  -- Step 2: Split `Q.divisors` into `{1}`, major arcs `1 < d ≤ D`, and minor arcs `D < d`.
  let f : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
      ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
          (‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
            (L : ℝ))
  have hQ_pos : 0 < Q := Finset.prod_pos fun _ hp => (mem_filter.mp hp).2.pos
  have h1_mem : 1 ∈ Q.divisors := Nat.mem_divisors.mpr ⟨one_dvd Q, hQ_pos.ne'⟩
  have hdiv_part :
      Q.divisors = ({1} ∪ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D)) ∪
        Q.divisors.filter (fun d => D < d) := by
    ext d
    simp only [mem_union, mem_singleton, mem_filter]
    constructor
    · intro hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hQ_pos
      by_cases hdeq : d = 1
      · exact Or.inl (Or.inl hdeq)
      · by_cases hdD : d ≤ D
        · exact Or.inl (Or.inr ⟨hd, by omega, hdD⟩)
        · exact Or.inr ⟨hd, by omega⟩
    · rintro ((rfl | ⟨hd, _⟩) | ⟨hd, _⟩)
      · exact h1_mem
      · exact hd
      · exact hd
  have hdisj1 : Disjoint ({1} : Finset ℕ) (Q.divisors.filter (fun d => 1 < d ∧ d ≤ D)) := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    rw [mem_singleton] at h1
    have := (mem_filter.mp h2).2.1
    omega
  have hdisj2 : Disjoint ({1} ∪ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D))
      (Q.divisors.filter (fun d => D < d)) := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    have hgt := (mem_filter.mp h2).2
    rcases mem_union.mp h1 with h1' | h1'
    · rw [mem_singleton] at h1'; omega
    · have := (mem_filter.mp h1').2.2; omega
  have hf1 : f 1 = (L : ℝ) := by
    dsimp [f]
    have h0 : ({0} : Finset ℕ).filter (fun r => Nat.Coprime r 1) = {0} := by decide
    rw [h0]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one, div_one, one_mul,
      Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, Complex.ofReal_zero,
      Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      Complex.norm_natCast]
    field_simp
  have hsum_split :
      ∑ d ∈ Q.divisors, f d =
        (L : ℝ) + ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f d +
          ∑ d ∈ Q.divisors.filter (fun d => D < d), f d := by
    conv_lhs => rw [hdiv_part]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton, hf1]
  -- Step 3: Combine major-arc upper bound, minor-arc lower bound, and Mertens lower bound.
  have hmaj : |∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f d| ≤
      ((1 - θ) / 2) * (L : ℝ) := by
    have h1 := ramanujan_major_arc_bound x M L D (by omega)
    have hD_le : (D : ℝ) ≤ (L : ℝ) / ((Nat.log 2 L + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast Nat.div_mul_le_self L (Nat.log 2 L + 1)
    have hlog_ge_r : (2 : ℝ) / (1 - θ) ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) := by
      have hN1_le : (N₀ : ℝ) ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) := by
        exact_mod_cast (le_max_right 2 N₀).trans hlogL_ge
      exact hN₀.trans hN1_le
    have hlog_ge2 : (2 : ℝ) ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) := by
      exact_mod_cast (le_max_left 2 N₀).trans hlogL_ge
    have hratio : 3 / (4 * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2) ≤ (1 - θ) / 2 := by
      have hsq : 4 / (1 - θ) ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2 := by
        calc
          4 / (1 - θ) = 2 * (2 / (1 - θ)) := by ring
          _ ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) * ((Nat.log 2 L + 1 : ℕ) : ℝ) :=
            mul_le_mul hlog_ge2 hlog_ge_r (by positivity) (by positivity)
          _ = ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2 := (sq _).symm
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hmul : 4 ≤ (1 - θ) * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2 := by
        have := (div_le_iff₀ h1θ_pos).mp hsq
        linarith
      linarith
    have h2 : 3 * (D : ℝ) ^ 2 / (4 * (L : ℝ)) ≤
        (3 / (4 * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2)) * (L : ℝ) := by
      have hDsq : (D : ℝ) ^ 2 ≤ ((L : ℝ) / ((Nat.log 2 L + 1 : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg D) hD_le 2
      have hcalc : 3 * ((L : ℝ) / ((Nat.log 2 L + 1 : ℕ) : ℝ)) ^ 2 / (4 * (L : ℝ)) =
          (3 / (4 * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2)) * (L : ℝ) := by
        have hln : ((Nat.log 2 L + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      calc
        3 * (D : ℝ) ^ 2 / (4 * (L : ℝ))
            ≤ 3 * ((L : ℝ) / ((Nat.log 2 L + 1 : ℕ) : ℝ)) ^ 2 / (4 * (L : ℝ)) := by gcongr
        _ = (3 / (4 * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2)) * (L : ℝ) := hcalc
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right hratio hL_pos.le))
  have hmin : -(θ * (L : ℝ)) ≤ ∑ d ∈ Q.divisors.filter (fun d => D < d), f d := hMin M
  have htotal : ((1 - θ) / 2) * (L : ℝ) ≤ ∑ d ∈ Q.divisors, f d := by
    rw [hsum_split]
    have hmaj_lo := (abs_le.mp hmaj).1
    linarith
  have hVx_lo : c₀ / Real.log (x : ℝ) ≤
      ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := hMertens x (by omega)
  have hlogx_pos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hVx_pos : 0 < ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  have hident := ramanujan_fejer_identity x M L (by omega)
  calc
    c * (y : ℝ) / Real.log (x : ℝ)
        = (c₀ / Real.log (x : ℝ)) * (((1 - θ) / 2) * ((y : ℝ) / 3)) := by dsimp [c]; ring
    _ ≤ (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) * (((1 - θ) / 2) * (L : ℝ)) := by
      have h1 : ((1 - θ) / 2) * ((y : ℝ) / 3) ≤ ((1 - θ) / 2) * (L : ℝ) :=
        mul_le_mul_of_nonneg_left hy_le_3L (by positivity)
      exact mul_le_mul hVx_lo h1 (by positivity) hVx_pos.le
    _ ≤ (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) * ∑ d ∈ Q.divisors, f d :=
      mul_le_mul_of_nonneg_left htotal hVx_pos.le
    _ = (∑ u ∈ range L, ∑ v ∈ range L,
          (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℝ) else 0)) / (L : ℝ) :=
      hident.symm
    _ ≤ (((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ) :=
      hfejer_le_card

end OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1
