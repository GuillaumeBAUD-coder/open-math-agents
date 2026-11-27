import OMAStatements.S_oeis_a387471
import Mathlib

/-!
# Proof of OEIS A387471 Conjecture

Original proof that for every `n ≥ 1`, the count `d (2 * n - 1)` of interior equal-angle
triple intersections in an equilateral triangle (via trigonometric Ceva) equals
`6 * n + 7` when `5 ∣ n` and `6 * n - 5` otherwise.

Proof outline:
1. Trigonometric reduction: Using `4 sin x sin y sin z = sin(x+y-z) + sin(y+z-x) + sin(z+x-y) - sin(x+y+z)`,
   the last term cancels identically against `sin(π - (x+y+z)) = sin(x+y+z)` on the RHS,
   and `sin A - sin(π/3 - A) = √3 sin(A - π/6)` reduces `ratio x * ratio y * ratio z = 1`
   equivalently to the 3-term rational sine equation `sin u + sin v + sin w = 0`.
2. Trivial family: Solutions with `a = n`, `b = n`, or `c = n` correspond precisely to
   `u + w = 0`, `u + v = 0`, or `v + w = 0`, yielding exactly `6 * n - 5` triples.
3. Mann's theorem for length `≤ 6`: Using irreducibility of `Φ_M` over `ℚ` and discrete
   Fourier orthogonality at `k = 1 + q * m`, any minimal vanishing `ℚ`-linear combination
   of at most 6 roots of unity with constant term has every ratio exponent dividing `30`.
4. Non-trivial exclusion and classification: For `a, b, c ≠ n`, the bounds `x, y, z ∈ (0, π/3)`
   strictly exclude all proper vanishing subsums of the resulting 4- or 6-term root-of-unity sum.
   Mann's theorem forces all angles into `(π / 30) ℤ`, and exact reduction modulo `Φ_60`
   leaves the unique ordered solution `sin(π/10) + sin(π/6) = sin(3π/10)`, producing
   exactly 12 sporadic triples if and only if `5 ∣ n`.
-/

namespace OMA.OeisA387471Proof

open OMA.S_oeis_a387471

/-! ### Part 1: Trigonometric product-to-sum reduction -/

private lemma four_mul_sin_mul_sin_mul_sin (x y z : ℝ) :
    4 * (Real.sin x * Real.sin y * Real.sin z) =
      Real.sin (x + y - z) + Real.sin (y + z - x) + Real.sin (z + x - y) -
        Real.sin (x + y + z) := by
  have h1 : Real.sin (x + y - z) = Real.sin ((x + y) - z) := by congr 1
  have h2 : Real.sin (y + z - x) = Real.sin (z - (x - y)) := by congr 1; ring
  have h3 : Real.sin (z + x - y) = Real.sin (z + (x - y)) := by congr 1; ring
  have h4 : Real.sin (x + y + z) = Real.sin ((x + y) + z) := by congr 1
  rw [h1, h2, h3, h4]
  simp only [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
  ring

private lemma sin_sub_sin_pi_div_three_sub (A : ℝ) :
    Real.sin A - Real.sin (Real.pi / 3 - A) = Real.sqrt 3 * Real.sin (A - Real.pi / 6) := by
  have h1 : Real.sin A = Real.sin ((A - Real.pi / 6) + Real.pi / 6) := by congr 1; ring
  have h2 : Real.sin (Real.pi / 3 - A) = Real.sin (Real.pi / 6 - (A - Real.pi / 6)) := by
    congr 1; ring
  rw [h1, h2, Real.sin_add (A - Real.pi / 6), Real.sin_sub (Real.pi / 6),
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

private lemma trig_prod_sub_eq (x y z : ℝ) :
    4 * (Real.sin x * Real.sin y * Real.sin z -
      Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) * Real.sin (Real.pi / 3 - z)) =
    Real.sqrt 3 * (Real.sin (x + y - z - Real.pi / 6) +
      Real.sin (y + z - x - Real.pi / 6) + Real.sin (z + x - y - Real.pi / 6)) := by
  rw [mul_sub, four_mul_sin_mul_sin_mul_sin, four_mul_sin_mul_sin_mul_sin]
  have hs1 : (Real.pi / 3 - x) + (Real.pi / 3 - y) - (Real.pi / 3 - z) =
      Real.pi / 3 - (x + y - z) := by ring
  have hs2 : (Real.pi / 3 - y) + (Real.pi / 3 - z) - (Real.pi / 3 - x) =
      Real.pi / 3 - (y + z - x) := by ring
  have hs3 : (Real.pi / 3 - z) + (Real.pi / 3 - x) - (Real.pi / 3 - y) =
      Real.pi / 3 - (z + x - y) := by ring
  have hs4 : (Real.pi / 3 - x) + (Real.pi / 3 - y) + (Real.pi / 3 - z) =
      Real.pi - (x + y + z) := by ring
  rw [hs1, hs2, hs3, hs4, Real.sin_pi_sub]
  have e1 := sin_sub_sin_pi_div_three_sub (x + y - z)
  have e2 := sin_sub_sin_pi_div_three_sub (y + z - x)
  have e3 := sin_sub_sin_pi_div_three_sub (z + x - y)
  linarith

private lemma ratio_prod_eq_one_iff {n : ℕ} (hn : 1 ≤ n) (i j k : Fin (2 * n - 1)) :
    ratio (2 * n - 1) i.val * ratio (2 * n - 1) j.val * ratio (2 * n - 1) k.val = 1 ↔
      Real.sin ((((i.val + 1 : ℕ) : ℤ) + ((j.val + 1 : ℕ) : ℤ) - ((k.val + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) *
          Real.pi / (6 * (n : ℝ))) +
      Real.sin ((((j.val + 1 : ℕ) : ℤ) + ((k.val + 1 : ℕ) : ℤ) - ((i.val + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) *
          Real.pi / (6 * (n : ℝ))) +
      Real.sin ((((k.val + 1 : ℕ) : ℤ) + ((i.val + 1 : ℕ) : ℤ) - ((j.val + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) *
          Real.pi / (6 * (n : ℝ))) = 0 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hden : 3 * (((2 * n - 1 : ℕ) : ℝ) + 1) = 6 * (n : ℝ) := by
    have hsub : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
      push_cast
      ring
    rw [hsub]
    ring
  have hpos_sin : ∀ r : Fin (2 * n - 1),
      0 < Real.sin (Real.pi / 3 - ((r.val : ℝ) + 1) * Real.pi / (6 * (n : ℝ))) := by
    intro r
    have hr : (r.val : ℝ) + 1 < 2 * (n : ℝ) := by exact_mod_cast (show r.val + 1 < 2 * n by omega)
    have hlt : ((r.val : ℝ) + 1) * Real.pi / (6 * (n : ℝ)) < Real.pi / 3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    have hpos : 0 < ((r.val : ℝ) + 1) * Real.pi / (6 * (n : ℝ)) := by
      have : (0 : ℝ) < (r.val : ℝ) + 1 := by positivity
      positivity
    apply Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set x : ℝ := ((i.val : ℝ) + 1) * Real.pi / (6 * (n : ℝ))
  set y : ℝ := ((j.val : ℝ) + 1) * Real.pi / (6 * (n : ℝ))
  set z : ℝ := ((k.val : ℝ) + 1) * Real.pi / (6 * (n : ℝ))
  have hx := hpos_sin i
  have hy := hpos_sin j
  have hz := hpos_sin k
  have hrat : ratio (2 * n - 1) i.val * ratio (2 * n - 1) j.val * ratio (2 * n - 1) k.val =
      (Real.sin x * Real.sin y * Real.sin z) /
      (Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) * Real.sin (Real.pi / 3 - z)) := by
    simp only [ratio, hden, x, y, z]
    ring
  have hdenom_pos : 0 < Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) *
      Real.sin (Real.pi / 3 - z) := by positivity
  have hiff1 : ratio (2 * n - 1) i.val * ratio (2 * n - 1) j.val * ratio (2 * n - 1) k.val = 1 ↔
      Real.sin x * Real.sin y * Real.sin z -
      Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) * Real.sin (Real.pi / 3 - z) = 0 := by
    rw [hrat, div_eq_one_iff_eq hdenom_pos.ne', sub_eq_zero]
  have hiff2 : Real.sin x * Real.sin y * Real.sin z -
      Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 - y) * Real.sin (Real.pi / 3 - z) = 0 ↔
      Real.sin (x + y - z - Real.pi / 6) + Real.sin (y + z - x - Real.pi / 6) +
        Real.sin (z + x - y - Real.pi / 6) = 0 := by
    have htr := trig_prod_sub_eq x y z
    have hsq3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    constructor
    · intro h
      rw [h, mul_zero] at htr
      exact (mul_eq_zero.mp htr.symm).resolve_left hsq3.ne'
    · intro h
      rw [h, mul_zero] at htr
      linarith
  have hu : x + y - z - Real.pi / 6 =
      ((((i.val + 1 : ℕ) : ℤ) + ((j.val + 1 : ℕ) : ℤ) - ((k.val + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) *
        Real.pi / (6 * (n : ℝ)) := by
    simp only [x, y, z]; push_cast; field_simp
  have hv : y + z - x - Real.pi / 6 =
      ((((j.val + 1 : ℕ) : ℤ) + ((k.val + 1 : ℕ) : ℤ) - ((i.val + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) *
        Real.pi / (6 * (n : ℝ)) := by
    simp only [x, y, z]; push_cast; field_simp
  have hw : z + x - y - Real.pi / 6 =
      ((((k.val + 1 : ℕ) : ℤ) + ((i.val + 1 : ℕ) : ℤ) - ((j.val + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) *
        Real.pi / (6 * (n : ℝ)) := by
    simp only [x, y, z]; push_cast; field_simp
  rw [hiff1, hiff2, hu, hv, hw]

/-! ### Part 2: Mann's Theorem for minimal vanishing sums of at most 6 roots of unity -/

private lemma aeval_cyclotomic_eq_zero {M : ℕ} (hM : 0 < M) {ζ : ℂ} (hprim : IsPrimitiveRoot ζ M) :
    Polynomial.aeval ζ (Polynomial.cyclotomic M ℚ) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hmap : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.cyclotomic M ℚ) =
      Polynomial.cyclotomic M ℂ := Polynomial.map_cyclotomic M (algebraMap ℚ ℂ)
  rw [hmap]
  exact hprim.isRoot_cyclotomic hM

private lemma minpoly_primitive_root {M : ℕ} (hM : 0 < M) {ζ : ℂ} (hprim : IsPrimitiveRoot ζ M) :
    minpoly ℚ ζ = Polynomial.cyclotomic M ℚ := by
  have hirr : Irreducible (Polynomial.cyclotomic M ℚ) := Polynomial.cyclotomic.irreducible_rat hM
  have hmon : (Polynomial.cyclotomic M ℚ).Monic := Polynomial.cyclotomic.monic M ℚ
  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic M ℚ) = 0 := aeval_cyclotomic_eq_zero hM hprim
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm

private lemma aeval_pow_eq_zero_of_coprime {M : ℕ} (hM : 0 < M) {ζ : ℂ}
    (hprim : IsPrimitiveRoot ζ M) {P : Polynomial ℚ} (hP : Polynomial.aeval ζ P = 0)
    {k : ℕ} (hk : Nat.Coprime k M) :
    Polynomial.aeval (ζ ^ k) P = 0 := by
  have hdvd : Polynomial.cyclotomic M ℚ ∣ P := by
    rw [← minpoly_primitive_root hM hprim]
    exact minpoly.dvd ℚ ζ hP
  rcases hdvd with ⟨Q, rfl⟩
  have hprim_k : IsPrimitiveRoot (ζ ^ k) M := hprim.pow_of_coprime k hk
  rw [map_mul, aeval_cyclotomic_eq_zero hM hprim_k, zero_mul]

private lemma isPrimitiveRoot_pow_of_mul {p m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hprim : IsPrimitiveRoot ζ (p * m)) :
    IsPrimitiveRoot (ζ ^ m) p := by
  rw [IsPrimitiveRoot.iff_def]
  refine ⟨?_, ?_⟩
  · rw [← pow_mul, mul_comm, hprim.pow_eq_one]
  · intro l hl
    rw [← pow_mul] at hl
    have hd := hprim.dvd_of_pow_eq_one (m * l) hl
    rw [mul_comm p m] at hd
    exact Nat.dvd_of_mul_dvd_mul_left hm hd

private lemma geom_sum_primitive_root {p : ℕ} {ξ : ℂ} (hξ : IsPrimitiveRoot ξ p) (d : ℕ) :
    ∑ q ∈ Finset.range p, (ξ ^ d) ^ q = if p ∣ d then (p : ℂ) else 0 := by
  split_ifs with hdvd
  · rcases hdvd with ⟨r, rfl⟩
    simp [pow_mul, hξ.pow_eq_one]
  · have hne : ξ ^ d ≠ 1 := fun h => hdvd (hξ.dvd_of_pow_eq_one d h)
    have hgeom : (∑ q ∈ Finset.range p, (ξ ^ d) ^ q) * (ξ ^ d - 1) = (ξ ^ d) ^ p - 1 :=
      geom_sum_mul (ξ ^ d) p
    have hpow : (ξ ^ d) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

private lemma coprime_one_add_mul_left (q m : ℕ) : Nat.Coprime (1 + q * m) m := by
  rw [Nat.coprime_comm, add_comm, mul_comm q m, Nat.coprime_mul_left_add_right]
  exact Nat.coprime_one_right m

private lemma mann_step {M p m : ℕ} (hp : p.Prime) (hM : M = p * m) (hm : 0 < m)
    {ζ : ℂ} (hprim : IsPrimitiveRoot ζ M)
    {S : Finset ℕ} {c : ℕ → ℚ} (h0 : 0 ∈ S)
    (hsum : ∑ e ∈ S, (c e : ℂ) * ζ ^ e = 0)
    (hmin : ∀ T ⊂ S, T.Nonempty → ∑ e ∈ T, (c e : ℂ) * ζ ^ e ≠ 0)
    (hcase : p ∣ m ∨ S.card < p) :
    ∀ e ∈ S, p ∣ e := by
  have hMpos : 0 < M := by rw [hM]; exact Nat.mul_pos hp.pos hm
  have hprim' : IsPrimitiveRoot ζ (p * m) := hM ▸ hprim
  set ξ : ℂ := ζ ^ m
  have hξ : IsPrimitiveRoot ξ p := isPrimitiveRoot_pow_of_mul hm hprim'
  let P : Polynomial ℚ := ∑ e ∈ S, Polynomial.C (c e) * Polynomial.X ^ e
  have hP : Polynomial.aeval ζ P = 0 := by
    simp only [P, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    simpa using hsum
  let F : ℕ → ℂ := fun q => ∑ e ∈ S, (c e : ℂ) * ζ ^ e * (ξ ^ e) ^ q
  have hF_eval : ∀ q : ℕ, F q = Polynomial.aeval (ζ ^ (1 + q * m)) P := by
    intro q
    simp only [P, F, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hpow : (ζ ^ (1 + q * m)) ^ e = ζ ^ e * (ξ ^ e) ^ q := by
      simp only [ξ, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [hpow, mul_assoc]
    rfl
  have hF_zero : ∀ q : ℕ, ¬ p ∣ 1 + q * m → F q = 0 := by
    intro q hndvd
    rw [hF_eval q]
    apply aeval_pow_eq_zero_of_coprime hMpos hprim hP
    rw [hM]
    refine Nat.Coprime.mul_right ?_ (coprime_one_add_mul_left q m)
    exact (hp.coprime_iff_not_dvd.mpr hndvd).symm
  have hsum_F_shift : ∀ s : ℕ, s < p →
      ∑ q ∈ Finset.range p, F q * (ξ ^ (p - s)) ^ q =
        (p : ℂ) * ∑ e ∈ S.filter (fun e => p ∣ e + (p - s)), (c e : ℂ) * ζ ^ e := by
    intro s _
    simp only [F, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hinner : ∀ e ∈ S,
        ∑ q ∈ Finset.range p, (c e : ℂ) * ζ ^ e * (ξ ^ e) ^ q * (ξ ^ (p - s)) ^ q =
          (p : ℂ) * (if p ∣ e + (p - s) then (c e : ℂ) * ζ ^ e else 0) := by
      intro e _
      have hfac : ∀ q : ℕ,
          (c e : ℂ) * ζ ^ e * (ξ ^ e) ^ q * (ξ ^ (p - s)) ^ q =
            ((c e : ℂ) * ζ ^ e) * (ξ ^ (e + (p - s))) ^ q := by
        intro q
        rw [pow_add, mul_pow]
        ring
      simp_rw [hfac]
      rw [← Finset.mul_sum, geom_sum_primitive_root hξ (e + (p - s))]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, Finset.sum_filter]
  have hfinish : (∑ e ∈ S.filter (fun e => p ∣ e), (c e : ℂ) * ζ ^ e = 0) →
      ∀ e ∈ S, p ∣ e := by
    intro hfilt0
    let T := S.filter (fun e => p ∣ e)
    have hTsub : T ⊆ S := Finset.filter_subset _ _
    have hTne : T.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨h0, dvd_zero p⟩⟩
    have hTeq : T = S := by
      by_contra hne
      exact hmin T (Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, hne⟩) hTne hfilt0
    intro e he
    rw [← hTeq] at he
    exact (Finset.mem_filter.mp he).2
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rcases hcase with hpm | hcard
  · have hFall : ∀ q ∈ Finset.range p, F q = 0 := by
      intro q _
      apply hF_zero q
      intro hdvd
      have hqm : p ∣ q * m := dvd_mul_of_dvd_right hpm q
      have h1 : p ∣ 1 := (Nat.dvd_add_left hqm).mp hdvd
      exact hp.not_dvd_one h1
    have h0eq := hsum_F_shift 0 hp.pos
    have hLHS : ∑ q ∈ Finset.range p, F q * (ξ ^ (p - 0)) ^ q = 0 :=
      Finset.sum_eq_zero fun q hq => by rw [hFall q hq, zero_mul]
    rw [hLHS] at h0eq
    have hfilt : S.filter (fun e => p ∣ e + (p - 0)) = S.filter (fun e => p ∣ e) := by
      ext e
      simp only [Finset.mem_filter, Nat.sub_zero, Nat.dvd_add_self_right]
    rw [hfilt] at h0eq
    exact hfinish ((mul_eq_zero.mp h0eq.symm).resolve_left hpC)
  · by_cases hpm : p ∣ m
    · have hFall : ∀ q ∈ Finset.range p, F q = 0 := by
        intro q _
        apply hF_zero q
        intro hdvd
        exact hp.not_dvd_one ((Nat.dvd_add_left (dvd_mul_of_dvd_right hpm q)).mp hdvd)
      have h0eq := hsum_F_shift 0 hp.pos
      have hLHS : ∑ q ∈ Finset.range p, F q * (ξ ^ (p - 0)) ^ q = 0 :=
        Finset.sum_eq_zero fun q hq => by rw [hFall q hq, zero_mul]
      rw [hLHS] at h0eq
      have hfilt : S.filter (fun e => p ∣ e + (p - 0)) = S.filter (fun e => p ∣ e) := by
        ext e
        simp only [Finset.mem_filter, Nat.sub_zero, Nat.dvd_add_self_right]
      rw [hfilt] at h0eq
      exact hfinish ((mul_eq_zero.mp h0eq.symm).resolve_left hpC)
    · let Bad := (Finset.range p).filter (fun q => p ∣ 1 + q * m)
      have hBad_le : Bad.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro q₁ hq₁ q₂ hq₂
        simp only [Bad, Finset.mem_filter, Finset.mem_range] at hq₁ hq₂
        have hstep : ∀ a b : ℕ, a < p → b < p → p ∣ 1 + a * m → p ∣ 1 + b * m → a ≤ b → a = b := by
          intro a b _ hb ha_d hb_d hab
          have hdiff : p ∣ (b - a) * m := by
            have heq : (1 + a * m) + (b - a) * m = 1 + b * m := by
              have : a * m + (b - a) * m = b * m := by
                rw [← add_mul, Nat.add_sub_of_le hab]
              omega
            exact (Nat.dvd_add_right ha_d).mp (heq.symm ▸ hb_d)
          have hq : p ∣ b - a := (hp.dvd_mul.mp hdiff).resolve_right hpm
          rcases hq with ⟨r, hr⟩
          have hr0 : r = 0 := by
            by_contra hrne
            have : p ≤ b - a := hr ▸ Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hrne)
            omega
          subst hr0; omega
        rcases le_total q₁ q₂ with hle | hle
        · exact hstep q₁ q₂ hq₁.1 hq₂.1 hq₁.2 hq₂.2 hle
        · exact (hstep q₂ q₁ hq₂.1 hq₁.1 hq₂.2 hq₁.2 hle).symm
      have hFall : ∀ q ∈ Finset.range p, F q = 0 := by
        rcases Finset.card_le_one_iff_subset_singleton.mp hBad_le with ⟨q₀, hBad_sub⟩
        by_cases hq₀_in : q₀ ∈ Finset.range p
        · have hne_q₀ : ∀ q ∈ Finset.range p, q ≠ q₀ → F q = 0 := by
            intro q hq hne
            apply hF_zero q
            intro hdvd
            have : q ∈ Bad := Finset.mem_filter.mpr ⟨hq, hdvd⟩
            exact hne (Finset.mem_singleton.mp (hBad_sub this))
          have hmiss : ∃ t < p, ∀ e ∈ S, e % p ≠ t := by
            have hlt : (S.image (· % p)).card < (Finset.range p).card := by
              rw [Finset.card_range]
              exact (Finset.card_image_le).trans_lt hcard
            obtain ⟨t, ht_mem, ht_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
            refine ⟨t, Finset.mem_range.mp ht_mem, fun e he heq => ht_not ?_⟩
            exact Finset.mem_image.mpr ⟨e, he, heq⟩
          rcases hmiss with ⟨t, ht_lt, ht_miss⟩
          have hteq := hsum_F_shift t ht_lt
          have hLHS : ∑ q ∈ Finset.range p, F q * (ξ ^ (p - t)) ^ q =
              F q₀ * (ξ ^ (p - t)) ^ q₀ := by
            rw [← Finset.add_sum_erase _ _ hq₀_in]
            have hrest : ∑ q ∈ (Finset.range p).erase q₀, F q * (ξ ^ (p - t)) ^ q = 0 :=
              Finset.sum_eq_zero fun q hq => by
                rw [hne_q₀ q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq), zero_mul]
            rw [hrest, add_zero]
          have hRHS : S.filter (fun e => p ∣ e + (p - t)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro e he hdvd
            apply ht_miss e he
            have hrem : p ∣ e % p + (p - t) := by
              have heq : e + (p - t) = p * (e / p) + (e % p + (p - t)) := by
                have := Nat.div_add_mod e p; omega
              exact (Nat.dvd_add_right (dvd_mul_right p (e / p))).mp (heq ▸ hdvd)
            rcases hrem with ⟨q, hq⟩
            have hlt : e % p < p := Nat.mod_lt e hp.pos
            have hq1 : q = 1 := by
              by_contra hne
              have : q = 0 ∨ 2 ≤ q := by omega
              rcases this with rfl | h2
              · omega
              · have : 2 * p ≤ p * q := by nlinarith
                omega
            subst hq1; omega
          rw [hLHS, hRHS, Finset.sum_empty, mul_zero] at hteq
          have hξne : (ξ ^ (p - t)) ^ q₀ ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hξ.ne_zero hp.ne_zero))
          have hFq₀ : F q₀ = 0 := (mul_eq_zero.mp hteq).resolve_right hξne
          intro q hq
          by_cases heq : q = q₀
          · rwa [heq]
          · exact hne_q₀ q hq heq
        · intro q hq
          apply hF_zero q
          intro hdvd
          have hmem : q ∈ Bad := Finset.mem_filter.mpr ⟨hq, hdvd⟩
          have hqq : q = q₀ := Finset.mem_singleton.mp (hBad_sub hmem)
          exact hq₀_in (hqq ▸ hq)
      have h0eq := hsum_F_shift 0 hp.pos
      have hLHS : ∑ q ∈ Finset.range p, F q * (ξ ^ (p - 0)) ^ q = 0 :=
        Finset.sum_eq_zero fun q hq => by rw [hFall q hq, zero_mul]
      rw [hLHS] at h0eq
      have hfilt : S.filter (fun e => p ∣ e + (p - 0)) = S.filter (fun e => p ∣ e) := by
        ext e
        simp only [Finset.mem_filter, Nat.sub_zero, Nat.dvd_add_self_right]
      rw [hfilt] at h0eq
      exact hfinish ((mul_eq_zero.mp h0eq.symm).resolve_left hpC)

private lemma exists_prime_factor_of_not_dvd_thirty {M : ℕ} (hM : 0 < M) (hndvd : ¬ M ∣ 30) :
    ∃ p m : ℕ, p.Prime ∧ M = p * m ∧ 0 < m ∧ (p ∣ m ∨ 6 < p) := by
  by_cases hbig : ∃ p, p.Prime ∧ p ∣ M ∧ 6 < p
  · rcases hbig with ⟨p, hp, ⟨m, rfl⟩, h6⟩
    exact ⟨p, m, hp, rfl, Nat.pos_of_ne_zero (by intro hm0; subst hm0; simp at hM), Or.inr h6⟩
  · push Not at hbig
    have hsq : 4 ∣ M ∨ 9 ∣ M ∨ 25 ∣ M := by
      by_contra hno
      push Not at hno
      have hall : ∀ p, p.Prime → p ∣ M → p = 2 ∨ p = 3 ∨ p = 5 := by
        intro p hp hdvd
        have hle := hbig p hp hdvd
        have hge := hp.two_le
        have h4 : p ≠ 4 := fun h => by subst h; norm_num at hp
        have h6 : p ≠ 6 := fun h => by subst h; norm_num at hp
        omega
      have hval : ∀ p, p.Prime → M.factorization p ≤ (30 : ℕ).factorization p := by
        intro p hp
        by_cases hdvd : p ∣ M
        · have hp235 := hall p hp hdvd
          have hle1 : M.factorization p ≤ 1 := by
            by_contra hgt
            have hge2 : 2 ≤ M.factorization p := by omega
            have hpp : p ^ 2 ∣ M := (hp.pow_dvd_iff_le_factorization hM.ne').mpr hge2
            rcases hp235 with rfl | rfl | rfl
            · exact hno.1 hpp
            · exact hno.2.1 hpp
            · exact hno.2.2 hpp
          have h30 : 1 ≤ (30 : ℕ).factorization p := by
            rw [← hp.pow_dvd_iff_le_factorization (by norm_num : (30 : ℕ) ≠ 0), pow_one]
            rcases hp235 with rfl | rfl | rfl <;> decide
          omega
        · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
          exact Nat.zero_le _
      have hdvd30 : M ∣ 30 := by
        rw [← Nat.factorization_le_iff_dvd hM.ne' (by norm_num)]
        intro p
        by_cases hp : p.Prime
        · exact hval p hp
        · rw [Nat.factorization_eq_zero_of_not_prime M hp]
          exact Nat.zero_le _
      exact hndvd hdvd30
    rcases hsq with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine ⟨2, 2 * k, by norm_num, by ring, ?_, Or.inl (dvd_mul_right 2 k)⟩
      omega
    · refine ⟨3, 3 * k, by norm_num, by ring, ?_, Or.inl (dvd_mul_right 3 k)⟩
      omega
    · refine ⟨5, 5 * k, by norm_num, by ring, ?_, Or.inl (dvd_mul_right 5 k)⟩
      omega

private lemma mann_dvd_thirty : ∀ M : ℕ, 0 < M →
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ M →
    ∀ (S : Finset ℕ) (c : ℕ → ℚ), 0 ∈ S → S.card ≤ 6 →
    (∑ e ∈ S, (c e : ℂ) * ζ ^ e = 0) →
    (∀ T ⊂ S, T.Nonempty → ∑ e ∈ T, (c e : ℂ) * ζ ^ e ≠ 0) →
    ∀ e ∈ S, M ∣ 30 * e := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro hM ζ hprim S c h0 hcard hsum hmin
    by_cases h30 : M ∣ 30
    · intro e _
      exact dvd_mul_of_dvd_left h30 e
    · rcases exists_prime_factor_of_not_dvd_thirty hM h30 with ⟨p, m, hp, hMpm, hmpos, hpm_or⟩
      have hcase : p ∣ m ∨ S.card < p := hpm_or.imp id (fun h6 => by omega)
      have hdvd_all : ∀ e ∈ S, p ∣ e := mann_step hp hMpm hmpos hprim h0 hsum hmin hcase
      have hm_lt : m < M := by
        rw [hMpm]
        exact lt_mul_of_one_lt_left hmpos hp.one_lt
      have hprim' : IsPrimitiveRoot (ζ ^ p) m := by
        rw [mul_comm] at hMpm
        exact isPrimitiveRoot_pow_of_mul hp.pos (hMpm ▸ hprim)
      let S' : Finset ℕ := S.image (· / p)
      let c' : ℕ → ℚ := fun k => c (p * k)
      have h0' : 0 ∈ S' := Finset.mem_image.mpr ⟨0, h0, Nat.zero_div p⟩
      have hcard' : S'.card ≤ 6 := Finset.card_image_le.trans hcard
      have hinj : Set.InjOn (· / p) S := by
        intro x hx y hy hxy
        dsimp only at hxy
        have hdx := hdvd_all x hx
        have hdy := hdvd_all y hy
        rw [← Nat.mul_div_cancel' hdx, ← Nat.mul_div_cancel' hdy, hxy]
      have hsum_sub : ∀ T ⊆ S,
          ∑ k ∈ T.image (· / p), (c' k : ℂ) * (ζ ^ p) ^ k = ∑ e ∈ T, (c e : ℂ) * ζ ^ e := by
        intro T hT
        rw [Finset.sum_image (hinj.mono (by exact_mod_cast hT))]
        refine Finset.sum_congr rfl fun e he => ?_
        have hd := hdvd_all e (hT he)
        simp only [c', Nat.mul_div_cancel' hd, ← pow_mul]
      have hsum' : ∑ k ∈ S', (c' k : ℂ) * (ζ ^ p) ^ k = 0 := by
        rw [hsum_sub S (Finset.Subset.refl S)]
        exact hsum
      have hmin' : ∀ T' ⊂ S', T'.Nonempty → ∑ k ∈ T', (c' k : ℂ) * (ζ ^ p) ^ k ≠ 0 := by
        intro T' hT'sub hT'ne
        let T := S.filter (fun e => e / p ∈ T')
        have hTsub : T ⊆ S := Finset.filter_subset _ _
        have hTimg : T.image (· / p) = T' := by
          ext k
          simp only [Finset.mem_image, T, Finset.mem_filter]
          constructor
          · rintro ⟨e, ⟨_, he'⟩, rfl⟩; exact he'
          · intro hk
            have hkS' : k ∈ S' := hT'sub.1 hk
            rcases Finset.mem_image.mp hkS' with ⟨e, heS, rfl⟩
            exact ⟨e, ⟨heS, hk⟩, rfl⟩
        have hTne : T.Nonempty := by
          rcases hT'ne with ⟨k, hk⟩
          rw [← hTimg] at hk
          rcases Finset.mem_image.mp hk with ⟨e, heT, _⟩
          exact ⟨e, heT⟩
        have hTssub : T ⊂ S := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨hTsub, fun hEq => ?_⟩
          have : T' = S' := by rw [← hTimg, hEq]
          exact hT'sub.2 (this ▸ Finset.Subset.refl S')
        rw [← hTimg, hsum_sub T hTsub]
        exact hmin T hTssub hTne
      have hrec := ih m hm_lt hmpos (ζ ^ p) hprim' S' c' h0' hcard' hsum' hmin'
      intro e he
      have hd := hdvd_all e he
      have hm_dvd : m ∣ 30 * (e / p) := hrec (e / p) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      rw [hMpm]
      have heq : 30 * e = p * (30 * (e / p)) := by
        have := Nat.mul_div_cancel' hd
        linarith
      rw [heq]
      exact mul_dvd_mul_left p hm_dvd

/-! ### Part 3: Fast exact reduction modulo Φ_60 for the finite mod-30 sine classification -/

private structure Vec16 where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  c4 : ℤ
  c5 : ℤ
  c6 : ℤ
  c7 : ℤ
  c8 : ℤ
  c9 : ℤ
  c10 : ℤ
  c11 : ℤ
  c12 : ℤ
  c13 : ℤ
  c14 : ℤ
  c15 : ℤ
  deriving DecidableEq

private def Vec16.zero : Vec16 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def Vec16.one : Vec16 :=
  ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def Vec16.add (u v : Vec16) : Vec16 :=
  ⟨u.c0 + v.c0, u.c1 + v.c1, u.c2 + v.c2, u.c3 + v.c3,
   u.c4 + v.c4, u.c5 + v.c5, u.c6 + v.c6, u.c7 + v.c7,
   u.c8 + v.c8, u.c9 + v.c9, u.c10 + v.c10, u.c11 + v.c11,
   u.c12 + v.c12, u.c13 + v.c13, u.c14 + v.c14, u.c15 + v.c15⟩

private def Vec16.sub (u v : Vec16) : Vec16 :=
  ⟨u.c0 - v.c0, u.c1 - v.c1, u.c2 - v.c2, u.c3 - v.c3,
   u.c4 - v.c4, u.c5 - v.c5, u.c6 - v.c6, u.c7 - v.c7,
   u.c8 - v.c8, u.c9 - v.c9, u.c10 - v.c10, u.c11 - v.c11,
   u.c12 - v.c12, u.c13 - v.c13, u.c14 - v.c14, u.c15 - v.c15⟩

private def Vec16.get (v : Vec16) (i : Fin 16) : ℤ :=
  match i.val with
  | 0 => v.c0 | 1 => v.c1 | 2 => v.c2 | 3 => v.c3
  | 4 => v.c4 | 5 => v.c5 | 6 => v.c6 | 7 => v.c7
  | 8 => v.c8 | 9 => v.c9 | 10 => v.c10 | 11 => v.c11
  | 12 => v.c12 | 13 => v.c13 | 14 => v.c14 | _ => v.c15

private def redStep (v : Vec16) : Vec16 :=
  let c := v.c15
  ⟨-c, v.c0, v.c1 - c, v.c2, v.c3, v.c4, v.c5 + c, v.c6,
   v.c7 + c, v.c8, v.c9 + c, v.c10, v.c11, v.c12, v.c13 - c, v.c14⟩

private def redPow : ℕ → Vec16
  | 0 => Vec16.one
  | k + 1 => redStep (redPow k)

private def vTriple (A B C : ℕ) : Vec16 :=
  Vec16.sub
    (Vec16.sub
      (Vec16.add (Vec16.add (redPow A) (redPow (30 - A)))
        (Vec16.add (redPow B) (redPow (30 - B))))
      (redPow C))
    (redPow (30 - C))

private def eval16 (v : Vec16) (ω : ℂ) : ℂ :=
  ∑ i : Fin 16, (v.get i : ℂ) * ω ^ i.val

private lemma eval16_expand (v : Vec16) (ω : ℂ) :
    eval16 v ω =
      (v.c0 : ℂ) + (v.c1 : ℂ) * ω + (v.c2 : ℂ) * ω ^ 2 + (v.c3 : ℂ) * ω ^ 3 +
      (v.c4 : ℂ) * ω ^ 4 + (v.c5 : ℂ) * ω ^ 5 + (v.c6 : ℂ) * ω ^ 6 + (v.c7 : ℂ) * ω ^ 7 +
      (v.c8 : ℂ) * ω ^ 8 + (v.c9 : ℂ) * ω ^ 9 + (v.c10 : ℂ) * ω ^ 10 + (v.c11 : ℂ) * ω ^ 11 +
      (v.c12 : ℂ) * ω ^ 12 + (v.c13 : ℂ) * ω ^ 13 + (v.c14 : ℂ) * ω ^ 14 + (v.c15 : ℂ) * ω ^ 15 := by
  simp only [eval16, Fin.sum_univ_succ, Fin.sum_univ_zero, Vec16.get]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero]
  ring

private lemma eval16_add (u v : Vec16) (ω : ℂ) :
    eval16 (Vec16.add u v) ω = eval16 u ω + eval16 v ω := by
  simp only [eval16_expand, Vec16.add]
  push_cast
  ring

private lemma eval16_sub (u v : Vec16) (ω : ℂ) :
    eval16 (Vec16.sub u v) ω = eval16 u ω - eval16 v ω := by
  simp only [eval16_expand, Vec16.sub]
  push_cast
  ring

private lemma eval16_redStep {ω : ℂ}
    (hphi : ω ^ 16 + ω ^ 14 - ω ^ 10 - ω ^ 8 - ω ^ 6 + ω ^ 2 + 1 = 0)
    (v : Vec16) :
    eval16 (redStep v) ω = ω * eval16 v ω := by
  simp only [eval16_expand, redStep]
  push_cast
  linear_combination -(v.c15 : ℂ) * hphi

private lemma eval16_redPow {ω : ℂ}
    (hphi : ω ^ 16 + ω ^ 14 - ω ^ 10 - ω ^ 8 - ω ^ 6 + ω ^ 2 + 1 = 0) :
    ∀ k : ℕ, eval16 (redPow k) ω = ω ^ k
  | 0 => by
    simp only [redPow, eval16_expand, Vec16.one]
    simp
  | k + 1 => by
    rw [redPow, eval16_redStep hphi, eval16_redPow hphi k, pow_succ']

private lemma eval16_vTriple {ω : ℂ}
    (hphi : ω ^ 16 + ω ^ 14 - ω ^ 10 - ω ^ 8 - ω ^ 6 + ω ^ 2 + 1 = 0)
    (A B C : ℕ) :
    eval16 (vTriple A B C) ω =
      ω ^ A + ω ^ (30 - A) + ω ^ B + ω ^ (30 - B) - ω ^ C - ω ^ (30 - C) := by
  simp only [vTriple, eval16_sub, eval16_add, eval16_redPow hphi]
  ring

private lemma phi60_eq_zero {ω : ℂ} (hω : IsPrimitiveRoot ω 60) (h30 : ω ^ 30 = -1) :
    ω ^ 16 + ω ^ 14 - ω ^ 10 - ω ^ 8 - ω ^ 6 + ω ^ 2 + 1 = 0 := by
  have h10ne : ω ^ 10 + 1 ≠ 0 := by
    intro h
    have h20 : ω ^ 20 = 1 := by linear_combination (ω ^ 10 - 1) * h
    have hd := hω.dvd_of_pow_eq_one 20 h20
    omega
  have h20 : ω ^ 20 - ω ^ 10 + 1 = 0 := by
    have hmul : (ω ^ 10 + 1) * (ω ^ 20 - ω ^ 10 + 1) = 0 := by linear_combination h30
    exact (mul_eq_zero.mp hmul).resolve_left h10ne
  have h4ne : ω ^ 4 - ω ^ 2 + 1 ≠ 0 := by
    intro h
    have h6 : ω ^ 6 = -1 := by linear_combination (ω ^ 2 + 1) * h
    have h12 : ω ^ 12 = 1 := by linear_combination (ω ^ 6 - 1) * h6
    have hd := hω.dvd_of_pow_eq_one 12 h12
    omega
  have hmul : (ω ^ 4 - ω ^ 2 + 1) *
      (ω ^ 16 + ω ^ 14 - ω ^ 10 - ω ^ 8 - ω ^ 6 + ω ^ 2 + 1) = 0 := by
    linear_combination h20
  exact (mul_eq_zero.mp hmul).resolve_left h4ne

private lemma eval16_eq_zero_iff {ω : ℂ} (hω : IsPrimitiveRoot ω 60) (v : Vec16) :
    eval16 v ω = 0 ↔ v = Vec16.zero := by
  constructor
  · intro hv
    let Q : Polynomial ℚ := ∑ i : Fin 16, Polynomial.C (v.get i : ℚ) * Polynomial.X ^ i.val
    have hQeval : Polynomial.aeval ω Q = 0 := by
      simp only [Q, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
      simpa [eval16] using hv
    have hdvd : Polynomial.cyclotomic 60 ℚ ∣ Q := by
      rw [← minpoly_primitive_root (by norm_num) hω]
      exact minpoly.dvd ℚ ω hQeval
    have hQ0 : Q = 0 := by
      by_contra hne
      have hdeg_le : (Polynomial.cyclotomic 60 ℚ).natDegree ≤ Q.natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
      have hdeg_phi : (Polynomial.cyclotomic 60 ℚ).natDegree = 16 := by
        rw [Polynomial.natDegree_cyclotomic]; decide
      have hdeg_Q : Q.natDegree ≤ 15 :=
        Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ fun i _ =>
          (Polynomial.natDegree_C_mul_X_pow_le (v.get i : ℚ) i.val).trans (by omega)
      omega
    have hget0 : ∀ i : Fin 16, v.get i = 0 := by
      intro i
      have hcoeff : Q.coeff i.val = 0 := by rw [hQ0, Polynomial.coeff_zero]
      simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hcoeff
      have hsingle : (∑ j : Fin 16, (v.get j : ℚ) * if i.val = j.val then 1 else 0) = (v.get i : ℚ) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          have : i.val ≠ j.val := fun h => hji (Fin.ext h).symm
          simp [this]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [hsingle] at hcoeff
      exact_mod_cast hcoeff
    cases v
    have h0 := hget0 0; have h1 := hget0 1; have h2 := hget0 2; have h3 := hget0 3
    have h4 := hget0 4; have h5 := hget0 5; have h6 := hget0 6; have h7 := hget0 7
    have h8 := hget0 8; have h9 := hget0 9; have h10 := hget0 10; have h11 := hget0 11
    have h12 := hget0 12; have h13 := hget0 13; have h14 := hget0 14; have h15 := hget0 15
    simp only [Vec16.get] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    simp only [Vec16.zero, Vec16.mk.injEq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · intro hv
    subst hv
    simp [eval16_expand, Vec16.zero]

private def checkTripleBool (A B C : ℕ) : Bool :=
  if A > 0 ∧ A ≤ B ∧ B < C ∧ A + B < 10 then
    if vTriple A B C = Vec16.zero then (A == 3) && (B == 5) && (C == 9) else true
  else true

private lemma checkTripleBool_all :
    (List.range 15).all (fun A =>
      (List.range 15).all (fun B =>
        (List.range 15).all (fun C => checkTripleBool A B C))) = true := by
  decide

private lemma vTriple_3_5_9 : vTriple 3 5 9 = Vec16.zero := by
  decide

private lemma vTriple_classification {A B C : ℕ}
    (hA0 : 0 < A) (hAB : A ≤ B) (hBC : B < C) (hC15 : C < 15) (hsum10 : A + B < 10)
    (hv : vTriple A B C = Vec16.zero) :
    A = 3 ∧ B = 5 ∧ C = 9 := by
  have h1 := List.all_eq_true.mp checkTripleBool_all A (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 B (List.mem_range.mpr (by omega))
  have h3 := List.all_eq_true.mp h2 C (List.mem_range.mpr hC15)
  simp only [checkTripleBool, hA0, hAB, hBC, hsum10, and_self, ↓reduceIte, hv,
    Bool.and_eq_true, beq_iff_eq] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

private lemma two_I_mul_sin_eq_exp_sub {θ : ℝ} :
    2 * Complex.I * (Real.sin θ : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp (-(θ : ℂ) * Complex.I) := by
  have hneg : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private lemma sin_thirty_classification {A B C : ℕ}
    (hA0 : 0 < A) (hAB : A ≤ B) (hBC : B < C) (hC15 : C < 15) (hsum10 : A + B < 10)
    (heq : Real.sin ((A : ℝ) * Real.pi / 30) + Real.sin ((B : ℝ) * Real.pi / 30) =
      Real.sin ((C : ℝ) * Real.pi / 30)) :
    A = 3 ∧ B = 5 ∧ C = 9 := by
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 60)
  have hω : IsPrimitiveRoot ω 60 := Complex.isPrimitiveRoot_exp 60 (by norm_num)
  have hpow : ∀ k : ℕ, ω ^ k = Complex.exp ((k : ℂ) * Real.pi / 30 * Complex.I) := by
    intro k
    simp only [ω, ← Complex.exp_nat_mul]
    congr 1; ring
  have h30 : ω ^ 30 = -1 := by
    rw [hpow 30]
    have : ((30 : ℕ) : ℂ) * Real.pi / 30 * Complex.I = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  have hphi := phi60_eq_zero hω h30
  have hsin_pow : ∀ k : ℕ, k ≤ 30 →
      ω ^ k + ω ^ (30 - k) = 2 * Complex.I * (Real.sin ((k : ℝ) * Real.pi / 30) : ℂ) := by
    intro k hk
    rw [two_I_mul_sin_eq_exp_sub, hpow k, hpow (30 - k)]
    have hcast : (((k : ℝ) * Real.pi / 30 : ℝ) : ℂ) = (k : ℂ) * Real.pi / 30 := by
      push_cast; ring
    have hsub : ((30 - k : ℕ) : ℂ) * Real.pi / 30 * Complex.I =
        (Real.pi : ℂ) * Complex.I + (-((k : ℂ) * Real.pi / 30 * Complex.I)) := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [hcast, hsub, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have heval0 : eval16 (vTriple A B C) ω = 0 := by
    rw [eval16_vTriple hphi]
    have h1 := hsin_pow A (by omega)
    have h2 := hsin_pow B (by omega)
    have h3 := hsin_pow C (by omega)
    have hsumC : (Real.sin ((A : ℝ) * Real.pi / 30) : ℂ) +
        (Real.sin ((B : ℝ) * Real.pi / 30) : ℂ) -
        (Real.sin ((C : ℝ) * Real.pi / 30) : ℂ) = 0 := by
      exact_mod_cast (sub_eq_zero.mpr heq)
    linear_combination h1 + h2 - h3 + 2 * Complex.I * hsumC
  have hv0 := (eval16_eq_zero_iff hω (vTriple A B C)).mp heval0
  exact vTriple_classification hA0 hAB hBC hC15 hsum10 hv0

private lemma sin_thirty_3_5_9 :
    Real.sin (3 * Real.pi / 30) + Real.sin (5 * Real.pi / 30) = Real.sin (9 * Real.pi / 30) := by
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 60)
  have hω : IsPrimitiveRoot ω 60 := Complex.isPrimitiveRoot_exp 60 (by norm_num)
  have hpow : ∀ k : ℕ, ω ^ k = Complex.exp ((k : ℂ) * Real.pi / 30 * Complex.I) := by
    intro k
    simp only [ω, ← Complex.exp_nat_mul]
    congr 1; ring
  have h30 : ω ^ 30 = -1 := by
    rw [hpow 30]
    have : ((30 : ℕ) : ℂ) * Real.pi / 30 * Complex.I = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  have hphi := phi60_eq_zero hω h30
  have hsin_pow : ∀ k : ℕ, k ≤ 30 →
      ω ^ k + ω ^ (30 - k) = 2 * Complex.I * (Real.sin ((k : ℝ) * Real.pi / 30) : ℂ) := by
    intro k hk
    rw [two_I_mul_sin_eq_exp_sub, hpow k, hpow (30 - k)]
    have hcast : (((k : ℝ) * Real.pi / 30 : ℝ) : ℂ) = (k : ℂ) * Real.pi / 30 := by
      push_cast; ring
    have hsub : ((30 - k : ℕ) : ℂ) * Real.pi / 30 * Complex.I =
        (Real.pi : ℂ) * Complex.I + (-((k : ℂ) * Real.pi / 30 * Complex.I)) := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [hcast, hsub, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have heval0 : eval16 (vTriple 3 5 9) ω = 0 :=
    (eval16_eq_zero_iff hω (vTriple 3 5 9)).mpr vTriple_3_5_9
  rw [eval16_vTriple hphi] at heval0
  have h1 := hsin_pow 3 (by omega)
  have h2 := hsin_pow 5 (by omega)
  have h3 := hsin_pow 9 (by omega)
  have h2I : (2 : ℂ) * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  have hC : (Real.sin (3 * Real.pi / 30) : ℂ) + (Real.sin (5 * Real.pi / 30) : ℂ) -
      (Real.sin (9 * Real.pi / 30) : ℂ) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left h2I
    simp only [Nat.cast_ofNat] at h1 h2 h3
    linear_combination heval0 - h1 - h2 + h3
  have hR : Real.sin (3 * Real.pi / 30) + Real.sin (5 * Real.pi / 30) -
      Real.sin (9 * Real.pi / 30) = 0 := by
    exact_mod_cast hC
  linarith

/-! ### Part 4: Excluding proper subsums and classifying positive solutions sin α + sin β = sin γ -/

private lemma exp_add_exp_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) {x y : ℕ}
    (_hx : x < 12 * n) (hy : y < 12 * n) (hxy : x < y) :
    (Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))) ^ x +
      (Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))) ^ y = 0 ↔ y - x = 6 * n := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))
  have hprim : IsPrimitiveRoot ζ (12 * n) := Complex.isPrimitiveRoot_exp (12 * n) (by omega)
  have hζne : ζ ^ x ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have h6n : ζ ^ (6 * n) = -1 := by
    simp only [ζ, ← Complex.exp_nat_mul]
    have : ((6 * n : ℕ) : ℂ) * (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ)) =
        (Real.pi : ℂ) * Complex.I := by
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast; field_simp; ring
    rw [this, Complex.exp_pi_mul_I]
  constructor
  · intro h
    have hfac : ζ ^ x * (1 + ζ ^ (y - x)) = 0 := by
      have hpow : ζ ^ x * ζ ^ (y - x) = ζ ^ y := by rw [← pow_add, Nat.add_sub_of_le hxy.le]
      linear_combination h + hpow
    have h1 : ζ ^ (y - x) = -1 := eq_neg_of_add_eq_zero_right ((mul_eq_zero.mp hfac).resolve_left hζne)
    have hsq : ζ ^ (2 * (y - x)) = 1 := by
      rw [mul_comm, pow_mul, h1]; norm_num
    have hdvd := hprim.dvd_of_pow_eq_one (2 * (y - x)) hsq
    rcases hdvd with ⟨r, hr⟩
    have hr1 : r = 1 := by
      by_contra hne
      have hlt : y - x < 12 * n := by omega
      have : r = 0 ∨ 2 ≤ r := by omega
      rcases this with rfl | h2
      · omega
      · nlinarith
    subst hr1; omega
  · intro h
    have hpow : ζ ^ y = ζ ^ x * ζ ^ (6 * n) := by rw [← pow_add, show x + 6 * n = y by omega]
    rw [hpow, h6n]
    ring

private lemma three_roots_sum_zero_gap {n : ℕ} (hn : 1 ≤ n) {x y z : ℕ}
    (hxy : x < y) (hyz : y < z) (hz : z < 12 * n) :
    (Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))) ^ x +
      (Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))) ^ y +
      (Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))) ^ z = 0 →
    y - x = 4 * n ∧ z - y = 4 * n := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))
  have hcos_gap : ∀ a b c : ℕ, a < b → b < 12 * n → c < 12 * n →
      ζ ^ a + ζ ^ b + ζ ^ c = 0 → b - a = 4 * n ∨ b - a = 8 * n := by
    intro a b c hab hb hc hsum
    have hnorm1 : ∀ k : ℕ, Complex.normSq (ζ ^ k) = 1 := by
      intro k
      rw [Complex.normSq_eq_norm_sq]
      simp only [ζ, ← Complex.exp_nat_mul]
      have harg : (k : ℂ) * (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ)) =
          (((k : ℝ) * Real.pi / (6 * n) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]; norm_num
    have hfac : ζ ^ a * (1 + ζ ^ (b - a)) = -(ζ ^ c) := by
      have hpow : ζ ^ a * ζ ^ (b - a) = ζ ^ b := by rw [← pow_add, Nat.add_sub_of_le hab.le]
      linear_combination hsum + hpow
    have hns := congrArg Complex.normSq hfac
    rw [map_mul, hnorm1 a, one_mul, Complex.normSq_neg, hnorm1 c] at hns
    set θ : ℝ := ((b - a : ℕ) : ℝ) * Real.pi / (6 * (n : ℝ))
    have hpow : ζ ^ (b - a) = Complex.exp ((θ : ℂ) * Complex.I) := by
      simp only [ζ, θ, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    rw [hpow, Complex.exp_mul_I] at hns
    have hre : (1 + (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)).re =
        1 + Real.cos θ := by
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have him : (1 + (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)).im =
        Real.sin θ := by
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [Complex.normSq_apply, hre, him] at hns
    have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have hcos : Real.cos θ = -(1 / 2 : ℝ) := by nlinarith
    have hθ_pos : 0 < θ := by
      have : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by exact_mod_cast (show 0 < b - a by omega)
      positivity
    have hθ_lt : θ < 2 * Real.pi := by
      have h1 : ((b - a : ℕ) : ℝ) < 12 * (n : ℝ) := by exact_mod_cast (show b - a < 12 * n by omega)
      have hnR : (0 : ℝ) < (n : ℝ) := by positivity
      rw [show θ = ((b - a : ℕ) : ℝ) * Real.pi / (6 * (n : ℝ)) from rfl, div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    have hcases : θ = 2 * Real.pi / 3 ∨ θ = 4 * Real.pi / 3 := by
      by_cases hle : θ ≤ Real.pi
      · left
        have hinj := Real.injOn_cos
        have h23 : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
          rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
            Real.cos_pi_sub, Real.cos_pi_div_three]
        exact hinj ⟨hθ_pos.le, hle⟩ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          (hcos.trans h23.symm)
      · right
        have hinj := Real.injOn_cos
        have hcos' : Real.cos (2 * Real.pi - θ) = -(1 / 2 : ℝ) := by
          rw [Real.cos_two_pi_sub, hcos]
        have h23 : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
          rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
            Real.cos_pi_sub, Real.cos_pi_div_three]
        have heq := hinj ⟨by linarith, by linarith⟩
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (hcos'.trans h23.symm)
        linarith
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rcases hcases with h1 | h2
    · left
      have hR : ((b - a : ℕ) : ℝ) = (4 * n : ℕ) := by
        simp only [θ] at h1
        push_cast
        field_simp at h1
        linarith
      exact_mod_cast hR
    · right
      have hR : ((b - a : ℕ) : ℝ) = (8 * n : ℕ) := by
        simp only [θ] at h2
        push_cast
        field_simp at h2
        linarith
      exact_mod_cast hR
  intro hsum
  have h1 := hcos_gap x y z hxy (by omega) hz hsum
  have h2 := hcos_gap y z x hyz hz (by omega) (by linear_combination hsum)
  have h3 := hcos_gap x z y (by omega) hz (by omega) (by linear_combination hsum)
  omega

private lemma dvd_five_of_dvd_thirty_sub {n A₀ : ℕ} (hn : 1 ≤ n) (hA : 2 * A₀ ≤ 6 * n)
    (hd : 12 * n ∣ 30 * (6 * n - 2 * A₀)) : n ∣ 5 * A₀ := by
  rcases hd with ⟨q, hq⟩
  have hsub : 30 * (6 * n - 2 * A₀) + 60 * A₀ = 180 * n := by omega
  have h1 : 60 * A₀ + 12 * (n * q) = 180 * n := by
    linarith [hq, show 12 * n * q = 12 * (n * q) by ring]
  have h2 : 5 * A₀ + n * q = 15 * n := by omega
  have hqle : q ≤ 15 := by
    by_contra hgt
    have : 15 * n < n * q := by nlinarith
    omega
  refine ⟨15 - q, ?_⟩
  have hmul : n * (15 - q) + n * q = 15 * n := by
    rw [← mul_add, Nat.sub_add_cancel hqle]; ring
  omega

private lemma dvd_five_of_dvd_thirty_diff {n A₀ B₀ : ℕ} (hAB : A₀ ≤ B₀)
    (hA : n ∣ 5 * A₀) (hd : 12 * n ∣ 30 * (B₀ - A₀)) : n ∣ 5 * B₀ := by
  rcases hA with ⟨a, ha⟩
  rcases hd with ⟨q, hq⟩
  have hsub : 30 * (B₀ - A₀) + 30 * A₀ = 30 * B₀ := by omega
  have h1 : 30 * B₀ = 30 * A₀ + 12 * (n * q) := by
    linarith [hq, show 12 * n * q = 12 * (n * q) by ring]
  have h2 : 5 * B₀ = 5 * A₀ + 2 * (n * q) := by omega
  refine ⟨2 * q + a, ?_⟩
  rw [h2, ha]
  ring

private lemma dvd_five_of_dvd_thirty_add_sub {n A₀ C₀ : ℕ} (hn : 1 ≤ n) (hAC : A₀ ≤ 6 * n + C₀)
    (hA : n ∣ 5 * A₀) (hd : 12 * n ∣ 30 * (6 * n + C₀ - A₀)) : n ∣ 5 * C₀ := by
  rcases hA with ⟨a, ha⟩
  rcases hd with ⟨q, hq⟩
  have hsub : 30 * (6 * n + C₀ - A₀) + 30 * A₀ = 180 * n + 30 * C₀ := by omega
  have h1 : 180 * n + 30 * C₀ = 12 * (n * q) + 30 * A₀ := by
    linarith [hq, show 12 * n * q = 12 * (n * q) by ring]
  have h2 : 30 * n + 5 * C₀ = 2 * (n * q) + n * a := by omega
  have hle : 30 ≤ 2 * q + a := by
    by_contra hlt
    have : n * (2 * q + a) < n * 30 := Nat.mul_lt_mul_of_pos_left (by omega) hn
    linarith
  refine ⟨2 * q + a - 30, ?_⟩
  have hmul : n * (2 * q + a - 30) + 30 * n = 2 * (n * q) + n * a := by
    have : n * (2 * q + a - 30) + n * 30 = n * (2 * q + a) := by
      rw [← mul_add, Nat.sub_add_cancel hle]
    linarith
  omega

private lemma classify_pos_sin_sum {n A₀ B₀ C₀ : ℕ} (hn : 1 ≤ n)
    (hA0 : 0 < A₀) (hAB : A₀ ≤ B₀) (hBC : B₀ < C₀) (hC3 : C₀ < 3 * n)
    (hAB2 : A₀ + B₀ < 2 * n) (_hCA2 : C₀ - A₀ < 2 * n)
    (heq : Real.sin ((A₀ : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin ((B₀ : ℝ) * Real.pi / (6 * (n : ℝ))) =
      Real.sin ((C₀ : ℝ) * Real.pi / (6 * (n : ℝ)))) :
    5 * A₀ = 3 * n ∧ 5 * B₀ = 5 * n ∧ 5 * C₀ = 9 * n := by
  set M : ℕ := 12 * n
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ))
  have hMpos : 0 < M := by omega
  have hprim : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hMpos.ne'
  have hpow : ∀ k : ℕ, ζ ^ k = Complex.exp ((k : ℂ) * Real.pi / (6 * (n : ℂ)) * Complex.I) := by
    intro k
    simp only [ζ, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h6n : ζ ^ (6 * n) = -1 := by
    rw [hpow (6 * n)]
    have : ((6 * n : ℕ) : ℂ) * Real.pi / (6 * (n : ℂ)) * Complex.I =
        (Real.pi : ℂ) * Complex.I := by
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast; field_simp
    rw [this, Complex.exp_pi_mul_I]
  have hsin_pow : ∀ k : ℕ, k ≤ 6 * n →
      ζ ^ k + ζ ^ (6 * n - k) = 2 * Complex.I * (Real.sin ((k : ℝ) * Real.pi / (6 * (n : ℝ))) : ℂ) := by
    intro k hk
    rw [two_I_mul_sin_eq_exp_sub, hpow k, hpow (6 * n - k)]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : (((k : ℝ) * Real.pi / (6 * (n : ℝ)) : ℝ) : ℂ) =
        (k : ℂ) * Real.pi / (6 * (n : ℂ)) := by push_cast; ring
    have hsub : ((6 * n - k : ℕ) : ℂ) * Real.pi / (6 * (n : ℂ)) * Complex.I =
        (Real.pi : ℂ) * Complex.I + (-((k : ℂ) * Real.pi / (6 * (n : ℂ)) * Complex.I)) := by
      rw [Nat.cast_sub hk]
      push_cast; field_simp; ring
    rw [hcast, hsub, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hsum6 : ζ ^ A₀ + ζ ^ (6 * n - A₀) + ζ ^ B₀ + ζ ^ (6 * n - B₀) +
      ζ ^ (6 * n + C₀) + ζ ^ (12 * n - C₀) = 0 := by
    have h1 := hsin_pow A₀ (by omega)
    have h2 := hsin_pow B₀ (by omega)
    have h3 := hsin_pow C₀ (by omega)
    have hneg1 : ζ ^ (6 * n + C₀) = -(ζ ^ C₀) := by rw [pow_add, h6n]; ring
    have hneg2 : ζ ^ (12 * n - C₀) = -(ζ ^ (6 * n - C₀)) := by
      rw [show 12 * n - C₀ = 6 * n + (6 * n - C₀) by omega, pow_add, h6n]; ring
    have hC : (Real.sin ((A₀ : ℝ) * Real.pi / (6 * (n : ℝ))) : ℂ) +
        (Real.sin ((B₀ : ℝ) * Real.pi / (6 * (n : ℝ))) : ℂ) -
        (Real.sin ((C₀ : ℝ) * Real.pi / (6 * (n : ℝ))) : ℂ) = 0 := by
      exact_mod_cast (sub_eq_zero.mpr heq)
    linear_combination h1 + h2 - h3 + hneg1 + hneg2 + 2 * Complex.I * hC
  have hshift : ζ ^ 0 + ζ ^ (6 * n - 2 * A₀) + ζ ^ (B₀ - A₀) + ζ ^ (6 * n - B₀ - A₀) +
      ζ ^ (6 * n + C₀ - A₀) + ζ ^ (12 * n - C₀ - A₀) = 0 := by
    have hζne : ζ ^ A₀ ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
    apply (mul_eq_zero.mp ?_).resolve_left hζne
    have p1 : ζ ^ A₀ * ζ ^ 0 = ζ ^ A₀ := by simp
    have p2 : ζ ^ A₀ * ζ ^ (6 * n - 2 * A₀) = ζ ^ (6 * n - A₀) := by
      rw [← pow_add]; congr 1; omega
    have p3 : ζ ^ A₀ * ζ ^ (B₀ - A₀) = ζ ^ B₀ := by
      rw [← pow_add]; congr 1; omega
    have p4 : ζ ^ A₀ * ζ ^ (6 * n - B₀ - A₀) = ζ ^ (6 * n - B₀) := by
      rw [← pow_add]; congr 1; omega
    have p5 : ζ ^ A₀ * ζ ^ (6 * n + C₀ - A₀) = ζ ^ (6 * n + C₀) := by
      rw [← pow_add]; congr 1; omega
    have p6 : ζ ^ A₀ * ζ ^ (12 * n - C₀ - A₀) = ζ ^ (12 * n - C₀) := by
      rw [← pow_add]; congr 1; omega
    linear_combination p1 + p2 + p3 + p4 + p5 + p6 + hsum6
  have hdvd30_all : n ∣ 5 * A₀ ∧ n ∣ 5 * B₀ ∧ n ∣ 5 * C₀ := by
    by_cases hAeqB : A₀ = B₀
    · subst hAeqB
      set e₂ : ℕ := 6 * n - 2 * A₀
      set e₅ : ℕ := 6 * n + C₀ - A₀
      set e₆ : ℕ := 12 * n - C₀ - A₀
      have hord : 0 < e₂ ∧ e₂ < e₅ ∧ e₅ < e₆ ∧ e₆ < 12 * n := by omega
      let S : Finset ℕ := {0, e₂, e₅, e₆}
      let c : ℕ → ℚ := fun e => if e = 0 ∨ e = e₂ then 2 else 1
      have hS0 : 0 ∈ S := by simp [S]
      have hScard4 : S.card = 4 := by
        simp only [S]
        rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hSsum : ∑ e ∈ S, (c e : ℂ) * ζ ^ e = 0 := by
        simp only [S]
        rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
          Finset.sum_insert (by simp; omega), Finset.sum_singleton]
        have hc0 : c 0 = 2 := by simp [c]
        have hc2 : c e₂ = 2 := by simp [c]
        have hc5 : c e₅ = 1 := by simp [c]; omega
        have hc6 : c e₆ = 1 := by simp [c]; omega
        rw [hc0, hc2, hc5, hc6]
        simp only [Nat.sub_self, show 6 * n - A₀ - A₀ = e₂ by omega] at hshift
        push_cast
        linear_combination hshift
      have hSmin : ∀ T ⊂ S, T.Nonempty → ∑ e ∈ T, (c e : ℂ) * ζ ^ e ≠ 0 := by
        intro T hTssub hTne hT0
        have hcomp0 : ∑ e ∈ S \ T, (c e : ℂ) * ζ ^ e = 0 := by
          have := Finset.sum_sdiff hTssub.1 (f := fun e => (c e : ℂ) * ζ ^ e)
          linear_combination this + hSsum - hT0
        have hTcard_lt : T.card < 4 := hScard4 ▸ Finset.card_lt_card hTssub
        have hTcard_pos : 0 < T.card := Finset.card_pos.mpr hTne
        have hsmall : ∃ U ⊆ S, (U.card = 1 ∨ U.card = 2) ∧ ∑ e ∈ U, (c e : ℂ) * ζ ^ e = 0 := by
          by_cases hle2 : T.card ≤ 2
          · exact ⟨T, hTssub.1, by omega, hT0⟩
          · refine ⟨S \ T, Finset.sdiff_subset, ?_, hcomp0⟩
            have := Finset.card_sdiff_add_card_eq_card hTssub.1
            omega
        rcases hsmall with ⟨U, hUsub, hU1 | hU2, hU0⟩
        · rcases Finset.card_eq_one.mp hU1 with ⟨u, rfl⟩
          rw [Finset.sum_singleton] at hU0
          have hcne : (c u : ℂ) ≠ 0 := by simp only [c]; split_ifs <;> norm_num
          exact pow_ne_zero _ (Complex.exp_ne_zero _) ((mul_eq_zero.mp hU0).resolve_left hcne)
        · rcases Finset.card_eq_two.mp hU2 with ⟨u, v, huv, rfl⟩
          rw [Finset.sum_pair huv] at hU0
          have hnorm_z : ∀ k : ℕ, ‖ζ ^ k‖ = 1 := by
            intro k
            simp only [ζ, ← Complex.exp_nat_mul]
            have harg : (k : ℂ) * (2 * Real.pi * Complex.I / ((12 * n : ℕ) : ℂ)) =
                (((k : ℝ) * Real.pi / (6 * n) : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [harg, Complex.norm_exp_ofReal_mul_I]
          have hceq : c u = c v := by
            have h1 : (c u : ℂ) * ζ ^ u = -((c v : ℂ) * ζ ^ v) := eq_neg_of_add_eq_zero_left hU0
            have hn1 := congrArg (‖·‖) h1
            simp only [norm_neg, norm_mul, hnorm_z, mul_one, Complex.norm_ratCast] at hn1
            have hcu : 0 < c u := by simp only [c]; split_ifs <;> norm_num
            have hcv : 0 < c v := by simp only [c]; split_ifs <;> norm_num
            rw [abs_of_pos (by exact_mod_cast hcu), abs_of_pos (by exact_mod_cast hcv)] at hn1
            exact_mod_cast hn1
          have hhc : (c u : ℂ) ≠ 0 := by simp only [c]; split_ifs <;> norm_num
          have hsumz : ζ ^ u + ζ ^ v = 0 := by
            rw [← hceq] at hU0
            exact (mul_eq_zero.mp (by linear_combination hU0)).resolve_left hhc
          have huS : u ∈ S := hUsub (by simp)
          have hvS : v ∈ S := hUsub (by simp)
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at huS hvS
          have hgap : (u < v ∧ v - u = 6 * n) ∨ (v < u ∧ u - v = 6 * n) := by
            rcases lt_or_gt_of_ne huv with h1 | h2
            · left; exact ⟨h1, (exp_add_exp_eq_zero_iff hn (by omega) (by omega) h1).mp hsumz⟩
            · right; exact ⟨h2, (exp_add_exp_eq_zero_iff hn (by omega) (by omega) h2).mp
                (by linear_combination hsumz)⟩
          have hc0 : c 0 = 2 := by simp [c]
          have hc2 : c e₂ = 2 := by simp [c]
          have hc5 : c e₅ = 1 := by simp [c]; omega
          have hc6 : c e₆ = 1 := by simp [c]; omega
          rcases huS with rfl | rfl | rfl | rfl <;> rcases hvS with rfl | rfl | rfl | rfl <;>
            (try rw [hc0] at hceq) <;> (try rw [hc2] at hceq) <;>
            (try rw [hc5] at hceq) <;> (try rw [hc6] at hceq) <;>
            (try norm_num at hceq) <;> omega
      have hmann := mann_dvd_thirty M hMpos ζ hprim S c hS0 (by omega) hSsum hSmin
      have hd2 : 12 * n ∣ 30 * (6 * n - 2 * A₀) := hmann e₂ (by simp [S])
      have hd5 : 12 * n ∣ 30 * (6 * n + C₀ - A₀) := hmann e₅ (by simp [S])
      have hA : n ∣ 5 * A₀ := dvd_five_of_dvd_thirty_sub hn (by omega) hd2
      have hC : n ∣ 5 * C₀ := dvd_five_of_dvd_thirty_add_sub hn (by omega) hA hd5
      exact ⟨hA, hA, hC⟩
    · have hAltB : A₀ < B₀ := lt_of_le_of_ne hAB hAeqB
      set e₃ : ℕ := B₀ - A₀
      set e₄ : ℕ := 6 * n - B₀ - A₀
      set e₂ : ℕ := 6 * n - 2 * A₀
      set e₅ : ℕ := 6 * n + C₀ - A₀
      set e₆ : ℕ := 12 * n - C₀ - A₀
      have hord : 0 < e₃ ∧ e₃ < e₄ ∧ e₄ < e₂ ∧ e₂ < e₅ ∧ e₅ < e₆ ∧ e₆ < 12 * n := by omega
      let S : Finset ℕ := {0, e₃, e₄, e₂, e₅, e₆}
      let c : ℕ → ℚ := fun _ => 1
      have hS0 : 0 ∈ S := by simp [S]
      have hScard6 : S.card = 6 := by
        simp only [S]
        rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hSsum : ∑ e ∈ S, (c e : ℂ) * ζ ^ e = 0 := by
        simp only [S, c, Rat.cast_one, one_mul]
        rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
          Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
          Finset.sum_insert (by simp; omega), Finset.sum_singleton]
        linear_combination hshift
      have hSmin : ∀ T ⊂ S, T.Nonempty → ∑ e ∈ T, (c e : ℂ) * ζ ^ e ≠ 0 := by
        intro T hTssub hTne hT0
        have hcomp0 : ∑ e ∈ S \ T, (c e : ℂ) * ζ ^ e = 0 := by
          have := Finset.sum_sdiff hTssub.1 (f := fun e => (c e : ℂ) * ζ ^ e)
          linear_combination this + hSsum - hT0
        have hTcard_lt : T.card < 6 := hScard6 ▸ Finset.card_lt_card hTssub
        have hTcard_pos : 0 < T.card := Finset.card_pos.mpr hTne
        have hsmall : ∃ U ⊆ S, (U.card = 1 ∨ U.card = 2 ∨ U.card = 3) ∧
            ∑ e ∈ U, ζ ^ e = 0 := by
          by_cases hle3 : T.card ≤ 3
          · refine ⟨T, hTssub.1, by omega, ?_⟩
            simpa [c] using hT0
          · refine ⟨S \ T, Finset.sdiff_subset, ?_, ?_⟩
            · have := Finset.card_sdiff_add_card_eq_card hTssub.1; omega
            · simpa [c] using hcomp0
        rcases hsmall with ⟨U, hUsub, hU1 | hU2 | hU3, hU0⟩
        · rcases Finset.card_eq_one.mp hU1 with ⟨u, rfl⟩
          rw [Finset.sum_singleton] at hU0
          exact pow_ne_zero _ (Complex.exp_ne_zero _) hU0
        · rcases Finset.card_eq_two.mp hU2 with ⟨u, v, huv, rfl⟩
          rw [Finset.sum_pair huv] at hU0
          have huS : u ∈ S := hUsub (by simp)
          have hvS : v ∈ S := hUsub (by simp)
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at huS hvS
          have hgap : (u < v ∧ v - u = 6 * n) ∨ (v < u ∧ u - v = 6 * n) := by
            rcases lt_or_gt_of_ne huv with h1 | h2
            · left; exact ⟨h1, (exp_add_exp_eq_zero_iff hn (by omega) (by omega) h1).mp hU0⟩
            · right; exact ⟨h2, (exp_add_exp_eq_zero_iff hn (by omega) (by omega) h2).mp
                (by linear_combination hU0)⟩
          rcases huS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases hvS with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        · rcases Finset.card_eq_three.mp hU3 with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
          have hsum3 : ζ ^ x + ζ ^ y + ζ ^ z = 0 := by
            rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
              Finset.sum_singleton] at hU0
            linear_combination hU0
          have hxS : x ∈ S := hUsub (by simp)
          have hyS : y ∈ S := hUsub (by simp)
          have hzS : z ∈ S := hUsub (by simp)
          have hsorted : ∃ a b c' : ℕ, a ∈ S ∧ b ∈ S ∧ c' ∈ S ∧ a < b ∧ b < c' ∧
              ζ ^ a + ζ ^ b + ζ ^ c' = 0 := by
            rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
              rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
              rcases lt_or_gt_of_ne hyz with h3 | h3
            · exact ⟨x, y, z, hxS, hyS, hzS, h1, h3, hsum3⟩
            · exact ⟨x, z, y, hxS, hzS, hyS, h2, h3, by linear_combination hsum3⟩
            · omega
            · exact ⟨z, x, y, hzS, hxS, hyS, h2, h1, by linear_combination hsum3⟩
            · exact ⟨y, x, z, hyS, hxS, hzS, h1, h2, by linear_combination hsum3⟩
            · omega
            · exact ⟨y, z, x, hyS, hzS, hxS, h3, h2, by linear_combination hsum3⟩
            · exact ⟨z, y, x, hzS, hyS, hxS, h3, h1, by linear_combination hsum3⟩
          rcases hsorted with ⟨a, b, c', haS, hbS, hcS, hab, hbc, h3⟩
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at haS hbS hcS
          have hgaps := three_roots_sum_zero_gap hn hab hbc (by omega) h3
          have hc6 : c' = e₆ := by
            rcases hcS with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          subst hc6
          rcases haS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases hbS with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hmann := mann_dvd_thirty M hMpos ζ hprim S c hS0 (by omega) hSsum hSmin
      have hd2 : 12 * n ∣ 30 * (6 * n - 2 * A₀) := hmann e₂ (by simp [S])
      have hd3 : 12 * n ∣ 30 * (B₀ - A₀) := hmann e₃ (by simp [S])
      have hd5 : 12 * n ∣ 30 * (6 * n + C₀ - A₀) := hmann e₅ (by simp [S])
      have hA : n ∣ 5 * A₀ := dvd_five_of_dvd_thirty_sub hn (by omega) hd2
      have hB : n ∣ 5 * B₀ := dvd_five_of_dvd_thirty_diff hAB hA hd3
      have hC : n ∣ 5 * C₀ := dvd_five_of_dvd_thirty_add_sub hn (by omega) hA hd5
      exact ⟨hA, hB, hC⟩
  rcases hdvd30_all with ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩⟩
  have hApos : 0 < A := by nlinarith
  have hAB' : A ≤ B := by nlinarith
  have hBC' : B < C := by nlinarith
  have hC15 : C < 15 := by nlinarith
  have hsum10 : A + B < 10 := by nlinarith
  have heq30 : Real.sin ((A : ℝ) * Real.pi / 30) + Real.sin ((B : ℝ) * Real.pi / 30) =
      Real.sin ((C : ℝ) * Real.pi / 30) := by
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have cA : (A₀ : ℝ) * Real.pi / (6 * (n : ℝ)) = (A : ℝ) * Real.pi / 30 := by
      have : (5 : ℝ) * (A₀ : ℝ) = (n : ℝ) * (A : ℝ) := by exact_mod_cast hA
      field_simp; linarith
    have cB : (B₀ : ℝ) * Real.pi / (6 * (n : ℝ)) = (B : ℝ) * Real.pi / 30 := by
      have : (5 : ℝ) * (B₀ : ℝ) = (n : ℝ) * (B : ℝ) := by exact_mod_cast hB
      field_simp; linarith
    have cC : (C₀ : ℝ) * Real.pi / (6 * (n : ℝ)) = (C : ℝ) * Real.pi / 30 := by
      have : (5 : ℝ) * (C₀ : ℝ) = (n : ℝ) * (C : ℝ) := by exact_mod_cast hC
      field_simp; linarith
    rwa [cA, cB, cC] at heq
  rcases sin_thirty_classification hApos hAB' hBC' hC15 hsum10 heq30 with ⟨rfl, rfl, rfl⟩
  omega

/-! ### Part 5: Complete characterization and counting of triples -/

private lemma sin_eq_zero_of_abs_lt_pi_div_two {x : ℝ} (h1 : -(Real.pi / 2) < x)
    (h2 : x < Real.pi / 2) (h : Real.sin x = 0) : x = 0 := by
  have hstrict := Real.strictMonoOn_sin
  have hx : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨h1.le, h2.le⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rcases lt_trichotomy x 0 with hlt | rfl | hgt
  · have := hstrict hx h0 hlt; rw [Real.sin_zero] at this; linarith
  · rfl
  · have := hstrict h0 hx hgt; rw [Real.sin_zero] at this; linarith

private lemma sin_add_sin_eq_zero_of_abs_lt {x y : ℝ}
    (hx1 : -(Real.pi / 2) < x) (hx2 : x < Real.pi / 2)
    (hy1 : -(Real.pi / 2) < y) (hy2 : y < Real.pi / 2)
    (h : Real.sin x + Real.sin y = 0) : x + y = 0 := by
  have hstrict := Real.strictMonoOn_sin
  have hx : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨hx1.le, hx2.le⟩
  have hny : -y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hsin : Real.sin x = Real.sin (-y) := by rw [Real.sin_neg]; linarith
  rcases lt_trichotomy x (-y) with hlt | heq | hgt
  · have := hstrict hx hny hlt; linarith
  · linarith
  · have := hstrict hny hx hgt; linarith

private def isTriv (n a b c : ℕ) : Prop :=
  (a = n ∧ b + c = 2 * n) ∨ (b = n ∧ c + a = 2 * n) ∨ (c = n ∧ a + b = 2 * n)

private def isExtra (n a b c : ℕ) : Prop :=
  ∃ k : ℕ, n = 5 * k ∧
    ((a = k ∧ b = 7 * k ∧ c = 8 * k) ∨
     (a = k ∧ b = 8 * k ∧ c = 7 * k) ∨
     (a = 7 * k ∧ b = k ∧ c = 8 * k) ∨
     (a = 7 * k ∧ b = 8 * k ∧ c = k) ∨
     (a = 8 * k ∧ b = k ∧ c = 7 * k) ∨
     (a = 8 * k ∧ b = 7 * k ∧ c = k) ∨
     (a = 2 * k ∧ b = 3 * k ∧ c = 9 * k) ∨
     (a = 2 * k ∧ b = 9 * k ∧ c = 3 * k) ∨
     (a = 3 * k ∧ b = 2 * k ∧ c = 9 * k) ∨
     (a = 3 * k ∧ b = 9 * k ∧ c = 2 * k) ∨
     (a = 9 * k ∧ b = 2 * k ∧ c = 3 * k) ∨
     (a = 9 * k ∧ b = 3 * k ∧ c = 2 * k))

private lemma classify_pos_two_one {n : ℕ} (hn : 1 ≤ n) {X Y Z : ℤ}
    (hX1 : 0 < X) (hX2 : X < 3 * (n : ℤ))
    (hY1 : 0 < Y) (hY2 : Y < 3 * (n : ℤ))
    (hZ1 : -(3 * (n : ℤ)) < Z) (hZ2 : Z < 0)
    (hXY : X + Y < 2 * (n : ℤ))
    (hXZ1 : -(2 * (n : ℤ)) < X + Z) (hXZ2 : X + Z < 2 * (n : ℤ))
    (hYZ1 : -(2 * (n : ℤ)) < Y + Z) (hYZ2 : Y + Z < 2 * (n : ℤ))
    (hs : Real.sin ((X : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin ((Y : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin ((Z : ℝ) * Real.pi / (6 * (n : ℝ))) = 0) :
    ∃ k : ℕ, n = 5 * k ∧
      ((X = 3 * k ∧ Y = 5 * k ∧ Z = -9 * k) ∨ (X = 5 * k ∧ Y = 3 * k ∧ Z = -9 * k)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hbound : ∀ W : ℤ, -(3 * (n : ℤ)) < W → W < 3 * (n : ℤ) →
      -(Real.pi / 2) < (W : ℝ) * Real.pi / (6 * (n : ℝ)) ∧
        (W : ℝ) * Real.pi / (6 * (n : ℝ)) < Real.pi / 2 := by
    intro W hW1 hW2
    have h1 : -(3 * (n : ℝ)) < (W : ℝ) := by exact_mod_cast hW1
    have h2 : (W : ℝ) < 3 * (n : ℝ) := by exact_mod_cast hW2
    exact ⟨by rw [lt_div_iff₀ (by positivity)]; nlinarith,
           by rw [div_lt_iff₀ (by positivity)]; nlinarith⟩
  have hsin_pos : ∀ W : ℤ, 0 < W → W < 3 * (n : ℤ) →
      0 < Real.sin ((W : ℝ) * Real.pi / (6 * (n : ℝ))) := by
    intro W h1 h2
    have hW1 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast h1
    have hW2 : (W : ℝ) < 3 * (n : ℝ) := by exact_mod_cast h2
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hZeq : Real.sin ((X : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin ((Y : ℝ) * Real.pi / (6 * (n : ℝ))) =
      Real.sin (((-Z : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ))) := by
    have : ((-Z : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ)) =
        -((Z : ℝ) * Real.pi / (6 * (n : ℝ))) := by push_cast; ring
    rw [this, Real.sin_neg]; linarith
  have hltZ : ∀ W : ℤ, 0 < W → W < 3 * (n : ℤ) →
      Real.sin ((W : ℝ) * Real.pi / (6 * (n : ℝ))) <
        Real.sin (((-Z : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ))) → W < -Z := by
    intro W hW1 hW2 hgt
    by_contra hge
    have hle : ((-Z : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ)) ≤ (W : ℝ) * Real.pi / (6 * (n : ℝ)) := by
      have : ((-Z : ℤ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast (show -Z ≤ W by omega)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hpi.le) (by positivity)
    have hmono := Real.strictMonoOn_sin.monotoneOn
      ⟨(hbound (-Z) (by omega) (by omega)).1.le, (hbound (-Z) (by omega) (by omega)).2.le⟩
      ⟨(hbound W (by omega) hW2).1.le, (hbound W (by omega) hW2).2.le⟩ hle
    linarith
  have hXltZ : X < -Z := hltZ X hX1 hX2 (by linarith [hsin_pos Y hY1 hY2])
  have hYltZ : Y < -Z := hltZ Y hY1 hY2 (by linarith [hsin_pos X hX1 hX2])
  rcases le_total X Y with hle | hle
  · have hcl := classify_pos_sin_sum hn (A₀ := X.toNat) (B₀ := Y.toNat) (C₀ := (-Z).toNat)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
        have c1 : (X.toNat : ℝ) = (X : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
        have c2 : (Y.toNat : ℝ) = (Y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
        have c3 : ((-Z).toNat : ℝ) = ((-Z : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega)
        rw [c1, c2, c3]; exact hZeq)
    have h5n : 5 ∣ n :=
      Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 5 3) ⟨X.toNat, hcl.1.symm⟩
    rcases h5n with ⟨k, rfl⟩
    refine ⟨k, rfl, Or.inl ⟨by omega, by omega, by omega⟩⟩
  · have hcl := classify_pos_sin_sum hn (A₀ := Y.toNat) (B₀ := X.toNat) (C₀ := (-Z).toNat)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
        have c1 : (Y.toNat : ℝ) = (Y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
        have c2 : (X.toNat : ℝ) = (X : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
        have c3 : ((-Z).toNat : ℝ) = ((-Z : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega)
        rw [c1, c2, c3]; linarith)
    have h5n : 5 ∣ n :=
      Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 5 3) ⟨Y.toNat, hcl.1.symm⟩
    rcases h5n with ⟨k, rfl⟩
    refine ⟨k, rfl, Or.inr ⟨by omega, by omega, by omega⟩⟩

private lemma classify_signed_three_sines {n : ℕ} (hn : 1 ≤ n) {U V W : ℤ}
    (hU1 : -(3 * (n : ℤ)) < U) (hU2 : U < 3 * (n : ℤ))
    (hV1 : -(3 * (n : ℤ)) < V) (hV2 : V < 3 * (n : ℤ))
    (hW1 : -(3 * (n : ℤ)) < W) (hW2 : W < 3 * (n : ℤ))
    (hUV1 : -(2 * (n : ℤ)) < U + V) (hUV2 : U + V < 2 * (n : ℤ))
    (hVW1 : -(2 * (n : ℤ)) < V + W) (hVW2 : V + W < 2 * (n : ℤ))
    (hWU1 : -(2 * (n : ℤ)) < W + U) (hWU2 : W + U < 2 * (n : ℤ))
    (hUV0 : U + V ≠ 0) (hVW0 : V + W ≠ 0) (hWU0 : W + U ≠ 0)
    (heq : Real.sin ((U : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin ((V : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin ((W : ℝ) * Real.pi / (6 * (n : ℝ))) = 0) :
    ∃ k : ℕ, n = 5 * k ∧
      ((U = 3 * k ∧ V = 5 * k ∧ W = -9 * k) ∨
       (U = 5 * k ∧ V = 3 * k ∧ W = -9 * k) ∨
       (U = 3 * k ∧ V = -9 * k ∧ W = 5 * k) ∨
       (U = 5 * k ∧ V = -9 * k ∧ W = 3 * k) ∨
       (U = -9 * k ∧ V = 3 * k ∧ W = 5 * k) ∨
       (U = -9 * k ∧ V = 5 * k ∧ W = 3 * k) ∨
       (U = -3 * k ∧ V = -5 * k ∧ W = 9 * k) ∨
       (U = -5 * k ∧ V = -3 * k ∧ W = 9 * k) ∨
       (U = -3 * k ∧ V = 9 * k ∧ W = -5 * k) ∨
       (U = -5 * k ∧ V = 9 * k ∧ W = -3 * k) ∨
       (U = 9 * k ∧ V = -3 * k ∧ W = -5 * k) ∨
       (U = 9 * k ∧ V = -5 * k ∧ W = -3 * k)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hbound : ∀ X : ℤ, -(3 * (n : ℤ)) < X → X < 3 * (n : ℤ) →
      -(Real.pi / 2) < (X : ℝ) * Real.pi / (6 * (n : ℝ)) ∧
        (X : ℝ) * Real.pi / (6 * (n : ℝ)) < Real.pi / 2 := by
    intro X hX1 hX2
    have h1 : -(3 * (n : ℝ)) < (X : ℝ) := by exact_mod_cast hX1
    have h2 : (X : ℝ) < 3 * (n : ℝ) := by exact_mod_cast hX2
    exact ⟨by rw [lt_div_iff₀ (by positivity)]; nlinarith,
           by rw [div_lt_iff₀ (by positivity)]; nlinarith⟩
  have hpair0 : ∀ X Y : ℤ, -(3 * (n : ℤ)) < X → X < 3 * (n : ℤ) →
      -(3 * (n : ℤ)) < Y → Y < 3 * (n : ℤ) →
      Real.sin ((X : ℝ) * Real.pi / (6 * (n : ℝ))) +
        Real.sin ((Y : ℝ) * Real.pi / (6 * (n : ℝ))) = 0 → X + Y = 0 := by
    intro X Y hX1 hX2 hY1 hY2 hsum
    have h0 := sin_add_sin_eq_zero_of_abs_lt (hbound X hX1 hX2).1 (hbound X hX1 hX2).2
      (hbound Y hY1 hY2).1 (hbound Y hY1 hY2).2 hsum
    have hR : ((X + Y : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ)) = 0 := by
      push_cast; rw [add_mul, add_div]; exact h0
    have hZ : ((X + Y : ℤ) : ℝ) = 0 :=
      (mul_eq_zero.mp ((div_eq_zero_iff.mp hR).resolve_right (by positivity))).resolve_right hpi.ne'
    exact_mod_cast hZ
  have hU0 : U ≠ 0 := by
    intro h0; subst h0
    simp only [Int.cast_zero, zero_mul, zero_div, Real.sin_zero, zero_add] at heq
    exact hVW0 (hpair0 V W hV1 hV2 hW1 hW2 heq)
  have hV0 : V ≠ 0 := by
    intro h0; subst h0
    simp only [Int.cast_zero, zero_mul, zero_div, Real.sin_zero, add_zero] at heq
    exact hWU0 (hpair0 W U hW1 hW2 hU1 hU2 (by linarith))
  have hW0 : W ≠ 0 := by
    intro h0; subst h0
    simp only [Int.cast_zero, zero_mul, zero_div, Real.sin_zero, add_zero] at heq
    exact hUV0 (hpair0 U V hU1 hU2 hV1 hV2 heq)
  have hsin_pos : ∀ X : ℤ, 0 < X → X < 3 * (n : ℤ) →
      0 < Real.sin ((X : ℝ) * Real.pi / (6 * (n : ℝ))) := by
    intro X h1 h2
    have hX1 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast h1
    have hX2 : (X : ℝ) < 3 * (n : ℝ) := by exact_mod_cast h2
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hsin_neg : ∀ X : ℤ, X < 0 → -(3 * (n : ℤ)) < X →
      Real.sin ((X : ℝ) * Real.pi / (6 * (n : ℝ))) < 0 := by
    intro X h1 h2
    have hpos := hsin_pos (-X) (by omega) (by omega)
    have : ((-X : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ)) = -((X : ℝ) * Real.pi / (6 * (n : ℝ))) := by
      push_cast; ring
    rw [this, Real.sin_neg] at hpos
    linarith
  have hneg_eq : Real.sin (((-U : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin (((-V : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ))) +
      Real.sin (((-W : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ))) = 0 := by
    have f : ∀ X : ℤ, Real.sin (((-X : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ))) =
        -Real.sin ((X : ℝ) * Real.pi / (6 * (n : ℝ))) := by
      intro X
      rw [show ((-X : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ)) =
        -((X : ℝ) * Real.pi / (6 * (n : ℝ))) by push_cast; ring, Real.sin_neg]
    rw [f U, f V, f W]; linarith
  rcases lt_or_gt_of_ne hU0 with hUn | hUp <;>
    rcases lt_or_gt_of_ne hV0 with hVn | hVp <;>
    rcases lt_or_gt_of_ne hW0 with hWn | hWp
  · exfalso; linarith [hsin_neg U hUn hU1, hsin_neg V hVn hV1, hsin_neg W hWn hW1]
  · obtain ⟨k, rfl, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := classify_pos_two_one hn (X := -U) (Y := -V)
      (Z := -W) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hneg_eq
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))⟩
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩
  · obtain ⟨k, rfl, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := classify_pos_two_one hn (X := -U) (Y := -W)
      (Z := -V) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by linarith)
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))⟩
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))))⟩
  · obtain ⟨k, rfl, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := classify_pos_two_one hn (X := V) (Y := W)
      (Z := U) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by linarith)
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))⟩
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))⟩
  · obtain ⟨k, rfl, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := classify_pos_two_one hn (X := -V) (Y := -W)
      (Z := -U) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by linarith)
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))⟩
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))))))))))⟩
  · obtain ⟨k, rfl, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := classify_pos_two_one hn (X := U) (Y := W)
      (Z := V) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by linarith)
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))⟩
    · exact ⟨k, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))⟩
  · obtain ⟨k, rfl, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := classify_pos_two_one hn (X := U) (Y := V)
      (Z := W) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) heq
    · exact ⟨k, rfl, Or.inl ⟨by omega, by omega, by omega⟩⟩
    · exact ⟨k, rfl, Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)⟩
  · exfalso; linarith [hsin_pos U hUp hU2, hsin_pos V hVp hV2, hsin_pos W hWp hW2]

private lemma extra_of_signed_uvw {n k a b c : ℕ} (hn : n = 5 * k)
    (hcases :
      (((a : ℤ) + b - c - n = 3 * k ∧ (b : ℤ) + c - a - n = 5 * k ∧ (c : ℤ) + a - b - n = -9 * k) ∨
       ((a : ℤ) + b - c - n = 5 * k ∧ (b : ℤ) + c - a - n = 3 * k ∧ (c : ℤ) + a - b - n = -9 * k) ∨
       ((a : ℤ) + b - c - n = 3 * k ∧ (b : ℤ) + c - a - n = -9 * k ∧ (c : ℤ) + a - b - n = 5 * k) ∨
       ((a : ℤ) + b - c - n = 5 * k ∧ (b : ℤ) + c - a - n = -9 * k ∧ (c : ℤ) + a - b - n = 3 * k) ∨
       ((a : ℤ) + b - c - n = -9 * k ∧ (b : ℤ) + c - a - n = 3 * k ∧ (c : ℤ) + a - b - n = 5 * k) ∨
       ((a : ℤ) + b - c - n = -9 * k ∧ (b : ℤ) + c - a - n = 5 * k ∧ (c : ℤ) + a - b - n = 3 * k) ∨
       ((a : ℤ) + b - c - n = -3 * k ∧ (b : ℤ) + c - a - n = -5 * k ∧ (c : ℤ) + a - b - n = 9 * k) ∨
       ((a : ℤ) + b - c - n = -5 * k ∧ (b : ℤ) + c - a - n = -3 * k ∧ (c : ℤ) + a - b - n = 9 * k) ∨
       ((a : ℤ) + b - c - n = -3 * k ∧ (b : ℤ) + c - a - n = 9 * k ∧ (c : ℤ) + a - b - n = -5 * k) ∨
       ((a : ℤ) + b - c - n = -5 * k ∧ (b : ℤ) + c - a - n = 9 * k ∧ (c : ℤ) + a - b - n = -3 * k) ∨
       ((a : ℤ) + b - c - n = 9 * k ∧ (b : ℤ) + c - a - n = -3 * k ∧ (c : ℤ) + a - b - n = -5 * k) ∨
       ((a : ℤ) + b - c - n = 9 * k ∧ (b : ℤ) + c - a - n = -5 * k ∧ (c : ℤ) + a - b - n = -3 * k))) :
    isExtra n a b c := by
  refine ⟨k, hn, ?_⟩
  subst hn
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · right; right; right; right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; right; right; right; right; right; right; right; right; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; right; right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; left; exact ⟨by omega, by omega, by omega⟩
  · left; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; left; exact ⟨by omega, by omega, by omega⟩
  · right; right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩

private lemma sol_iff {n : ℕ} (hn : 1 ≤ n) (i j k : Fin (2 * n - 1)) :
    ratio (2 * n - 1) i.val * ratio (2 * n - 1) j.val * ratio (2 * n - 1) k.val = 1 ↔
      isTriv n (i.val + 1) (j.val + 1) (k.val + 1) ∨
      isExtra n (i.val + 1) (j.val + 1) (k.val + 1) := by
  rw [ratio_prod_eq_one_iff hn i j k]
  set a : ℕ := i.val + 1
  set b : ℕ := j.val + 1
  set c : ℕ := k.val + 1
  set U : ℤ := (a : ℤ) + (b : ℤ) - (c : ℤ) - (n : ℤ)
  set V : ℤ := (b : ℤ) + (c : ℤ) - (a : ℤ) - (n : ℤ)
  set W : ℤ := (c : ℤ) + (a : ℤ) - (b : ℤ) - (n : ℤ)
  have ha : 1 ≤ a ∧ a < 2 * n := ⟨by omega, by omega⟩
  have hb : 1 ≤ b ∧ b < 2 * n := ⟨by omega, by omega⟩
  have hc : 1 ≤ c ∧ c < 2 * n := ⟨by omega, by omega⟩
  have hU1 : -(3 * (n : ℤ)) < U := by omega
  have hU2 : U < 3 * (n : ℤ) := by omega
  have hV1 : -(3 * (n : ℤ)) < V := by omega
  have hV2 : V < 3 * (n : ℤ) := by omega
  have hW1 : -(3 * (n : ℤ)) < W := by omega
  have hW2 : W < 3 * (n : ℤ) := by omega
  have hsin0_iff : ∀ X : ℤ, -(3 * (n : ℤ)) < X → X < 3 * (n : ℤ) →
      (Real.sin ((X : ℝ) * Real.pi / (6 * (n : ℝ))) = 0 ↔ X = 0) := by
    intro X hX1 hX2
    constructor
    · intro h
      have hnR : (0 : ℝ) < (n : ℝ) := by positivity
      have h1 : -(3 * (n : ℝ)) < (X : ℝ) := by exact_mod_cast hX1
      have h2 : (X : ℝ) < 3 * (n : ℝ) := by exact_mod_cast hX2
      have h0 := sin_eq_zero_of_abs_lt_pi_div_two
        (by rw [lt_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos])
        (by rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]) h
      have h3 := (div_eq_zero_iff.mp h0).resolve_right (by positivity)
      have h4 := (mul_eq_zero.mp h3).resolve_right Real.pi_pos.ne'
      exact_mod_cast h4
    · intro h; subst h; simp
  constructor
  · intro heq
    by_cases han : a = n
    · left; left
      have hUW : W = -U := by omega
      have hcancel : Real.sin ((U : ℝ) * Real.pi / (6 * (n : ℝ))) +
          Real.sin ((W : ℝ) * Real.pi / (6 * (n : ℝ))) = 0 := by
        rw [hUW]; push_cast
        rw [show -(U : ℝ) * Real.pi / (6 * (n : ℝ)) = -((U : ℝ) * Real.pi / (6 * (n : ℝ))) by ring,
          Real.sin_neg]; ring
      have hV0 : V = 0 := (hsin0_iff V hV1 hV2).mp (by linarith)
      exact ⟨han, by omega⟩
    · by_cases hbn : b = n
      · left; right; left
        have hUV : V = -U := by omega
        have hcancel : Real.sin ((U : ℝ) * Real.pi / (6 * (n : ℝ))) +
            Real.sin ((V : ℝ) * Real.pi / (6 * (n : ℝ))) = 0 := by
          rw [hUV]; push_cast
          rw [show -(U : ℝ) * Real.pi / (6 * (n : ℝ)) = -((U : ℝ) * Real.pi / (6 * (n : ℝ))) by ring,
            Real.sin_neg]; ring
        have hW0 : W = 0 := (hsin0_iff W hW1 hW2).mp (by linarith)
        exact ⟨hbn, by omega⟩
      · by_cases hcn : c = n
        · left; right; right
          have hVW : W = -V := by omega
          have hcancel : Real.sin ((V : ℝ) * Real.pi / (6 * (n : ℝ))) +
              Real.sin ((W : ℝ) * Real.pi / (6 * (n : ℝ))) = 0 := by
            rw [hVW]; push_cast
            rw [show -(V : ℝ) * Real.pi / (6 * (n : ℝ)) = -((V : ℝ) * Real.pi / (6 * (n : ℝ))) by ring,
              Real.sin_neg]; ring
          have hU0 : U = 0 := (hsin0_iff U hU1 hU2).mp (by linarith)
          exact ⟨hcn, by omega⟩
        · right
          rcases classify_signed_three_sines hn hU1 hU2 hV1 hV2 hW1 hW2
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) heq with ⟨k0, hk0, hcases⟩
          exact extra_of_signed_uvw hk0 hcases
  · rintro (htriv | hextra)
    · rcases htriv with ⟨han, hbc⟩ | ⟨hbn, hca⟩ | ⟨hcn, hab⟩
      · have hW' : W = -U := by omega
        have hV' : V = 0 := by omega
        rw [hW', hV']; push_cast
        rw [show -(U : ℝ) * Real.pi / (6 * (n : ℝ)) = -((U : ℝ) * Real.pi / (6 * (n : ℝ))) by ring,
          Real.sin_neg]; simp
      · have hV' : V = -U := by omega
        have hW' : W = 0 := by omega
        rw [hV', hW']; push_cast
        rw [show -(U : ℝ) * Real.pi / (6 * (n : ℝ)) = -((U : ℝ) * Real.pi / (6 * (n : ℝ))) by ring,
          Real.sin_neg]; simp
      · have hW' : W = -V := by omega
        have hU' : U = 0 := by omega
        rw [hW', hU']; push_cast
        rw [show -(V : ℝ) * Real.pi / (6 * (n : ℝ)) = -((V : ℝ) * Real.pi / (6 * (n : ℝ))) by ring,
          Real.sin_neg]; simp
    · rcases hextra with ⟨k0, hk0, hcases⟩
      have hk0_pos : (0 : ℝ) < (k0 : ℝ) := by exact_mod_cast (show 0 < k0 by omega)
      have hscale : ∀ r : ℤ,
          ((r * (k0 : ℤ) : ℤ) : ℝ) * Real.pi / (6 * (n : ℝ)) = (r : ℝ) * Real.pi / 30 := by
        intro r
        rw [hk0]; push_cast; field_simp; ring
      have h359 := sin_thirty_3_5_9
      have hneg : ∀ r : ℤ, Real.sin (((-r : ℤ) : ℝ) * Real.pi / 30) =
          -Real.sin ((r : ℝ) * Real.pi / 30) := by
        intro r
        rw [show ((-r : ℤ) : ℝ) * Real.pi / 30 = -((r : ℝ) * Real.pi / 30) by push_cast; ring,
          Real.sin_neg]
      rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
        ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
        ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · have eU : U = -5 * k0 := by omega
        have eV : V = 9 * k0 := by omega
        have eW : W = -3 * k0 := by omega
        rw [eU, eV, eW, hscale (-5), hscale 9, hscale (-3), hneg 5, hneg 3]; push_cast; linarith
      · have eU : U = -3 * k0 := by omega
        have eV : V = 9 * k0 := by omega
        have eW : W = -5 * k0 := by omega
        rw [eU, eV, eW, hscale (-3), hscale 9, hscale (-5), hneg 3, hneg 5]; push_cast; linarith
      · have eU : U = -5 * k0 := by omega
        have eV : V = -3 * k0 := by omega
        have eW : W = 9 * k0 := by omega
        rw [eU, eV, eW, hscale (-5), hscale (-3), hscale 9, hneg 5, hneg 3]; push_cast; linarith
      · have eU : U = 9 * k0 := by omega
        have eV : V = -3 * k0 := by omega
        have eW : W = -5 * k0 := by omega
        rw [eU, eV, eW, hscale 9, hscale (-3), hscale (-5), hneg 3, hneg 5]; push_cast; linarith
      · have eU : U = -3 * k0 := by omega
        have eV : V = -5 * k0 := by omega
        have eW : W = 9 * k0 := by omega
        rw [eU, eV, eW, hscale (-3), hscale (-5), hscale 9, hneg 3, hneg 5]; push_cast; linarith
      · have eU : U = 9 * k0 := by omega
        have eV : V = -5 * k0 := by omega
        have eW : W = -3 * k0 := by omega
        rw [eU, eV, eW, hscale 9, hscale (-5), hscale (-3), hneg 5, hneg 3]; push_cast; linarith
      · have eU : U = -9 * k0 := by omega
        have eV : V = 5 * k0 := by omega
        have eW : W = 3 * k0 := by omega
        rw [eU, eV, eW, hscale (-9), hscale 5, hscale 3, hneg 9]; push_cast; linarith
      · have eU : U = 3 * k0 := by omega
        have eV : V = 5 * k0 := by omega
        have eW : W = -9 * k0 := by omega
        rw [eU, eV, eW, hscale 3, hscale 5, hscale (-9), hneg 9]; push_cast; linarith
      · have eU : U = -9 * k0 := by omega
        have eV : V = 3 * k0 := by omega
        have eW : W = 5 * k0 := by omega
        rw [eU, eV, eW, hscale (-9), hscale 3, hscale 5, hneg 9]; push_cast; linarith
      · have eU : U = 5 * k0 := by omega
        have eV : V = 3 * k0 := by omega
        have eW : W = -9 * k0 := by omega
        rw [eU, eV, eW, hscale 5, hscale 3, hscale (-9), hneg 9]; push_cast; linarith
      · have eU : U = 3 * k0 := by omega
        have eV : V = -9 * k0 := by omega
        have eW : W = 5 * k0 := by omega
        rw [eU, eV, eW, hscale 3, hscale (-9), hscale 5, hneg 9]; push_cast; linarith
      · have eU : U = 5 * k0 := by omega
        have eV : V = -9 * k0 := by omega
        have eW : W = 3 * k0 := by omega
        rw [eU, eV, eW, hscale 5, hscale (-9), hscale 3, hneg 9]; push_cast; linarith

open Classical in
private lemma card_triv {n : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.filter fun t : Fin (2 * n - 1) × Fin (2 * n - 1) × Fin (2 * n - 1) =>
      isTriv n (t.1.val + 1) (t.2.1.val + 1) (t.2.2.val + 1)).card = 6 * n - 5 := by
  let m := 2 * n - 1
  let mid : Fin m := ⟨n - 1, by omega⟩
  have hmid : mid.val = n - 1 := rfl
  let S0 : Finset (Fin m × Fin m × Fin m) := {(mid, mid, mid)}
  let S1 : Finset (Fin m × Fin m × Fin m) := Finset.univ.filter fun t =>
    t.1.val + 1 = n ∧ t.2.1.val + 1 ≠ n ∧ (t.2.1.val + 1) + (t.2.2.val + 1) = 2 * n
  let S2 : Finset (Fin m × Fin m × Fin m) := Finset.univ.filter fun t =>
    t.2.1.val + 1 = n ∧ t.2.2.val + 1 ≠ n ∧ (t.2.2.val + 1) + (t.1.val + 1) = 2 * n
  let S3 : Finset (Fin m × Fin m × Fin m) := Finset.univ.filter fun t =>
    t.2.2.val + 1 = n ∧ t.1.val + 1 ≠ n ∧ (t.1.val + 1) + (t.2.1.val + 1) = 2 * n
  have hunion : (Finset.univ.filter fun t : Fin m × Fin m × Fin m =>
      isTriv n (t.1.val + 1) (t.2.1.val + 1) (t.2.2.val + 1)) = S0 ∪ S1 ∪ S2 ∪ S3 := by
    ext ⟨i, j, k⟩
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton,
      S0, S1, S2, S3, Finset.mem_filter, isTriv, Prod.mk.injEq, Fin.ext_iff, hmid]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · by_cases hj : j.val + 1 = n
        · left; left; left; exact ⟨by omega, by omega, by omega⟩
        · left; left; right; exact ⟨h1, hj, h2⟩
      · by_cases hk : k.val + 1 = n
        · left; left; left; exact ⟨by omega, by omega, by omega⟩
        · left; right; exact ⟨h1, hk, h2⟩
      · by_cases hi : i.val + 1 = n
        · left; left; left; exact ⟨by omega, by omega, by omega⟩
        · right; exact ⟨h1, hi, h2⟩
    · rintro (((⟨h1, h2, h3⟩ | ⟨h1, _, h2⟩) | ⟨h1, _, h2⟩) | ⟨h1, _, h2⟩)
      · left; omega
      · left; exact ⟨h1, h2⟩
      · right; left; exact ⟨h1, h2⟩
      · right; right; exact ⟨h1, h2⟩
  have hd01 : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro ⟨i, j, k⟩ h0 h1
    simp only [S0, S1, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.mk.injEq, Fin.ext_iff, hmid] at h0 h1
    omega
  have hd02 : Disjoint (S0 ∪ S1) S2 := by
    rw [Finset.disjoint_left]
    intro ⟨i, j, k⟩ h01 h2
    simp only [S0, S1, S2, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and, Prod.mk.injEq, Fin.ext_iff, hmid] at h01 h2
    omega
  have hd03 : Disjoint (S0 ∪ S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]
    intro ⟨i, j, k⟩ h012 h3
    simp only [S0, S1, S2, S3, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and, Prod.mk.injEq, Fin.ext_iff, hmid] at h012 h3
    omega
  have hcard_other : (Finset.univ.erase mid).card = 2 * n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ mid), Finset.card_univ, Fintype.card_fin]
    omega
  have hS1 : S1.card = 2 * n - 2 := by
    rw [← hcard_other]
    symm
    refine Finset.card_nbij (fun j : Fin m => (mid, j, ⟨2 * n - 2 - j.val, by omega⟩)) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
        Fin.ext_iff, hmid] at hj
      simp only [Finset.mem_coe, S1, Finset.mem_filter, Finset.mem_univ, true_and, hmid]
      omega
    · intro j₁ _ j₂ _ h
      exact (Prod.mk.inj (Prod.mk.inj h).2).1
    · intro ⟨i, j, k⟩ h
      simp only [Finset.mem_coe, S1, Finset.mem_filter, Finset.mem_univ, true_and] at h
      refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
          Fin.ext_iff, hmid]
        omega
      · ext <;> simp only [hmid] <;> omega
  have hS2 : S2.card = 2 * n - 2 := by
    rw [← hcard_other]
    symm
    refine Finset.card_nbij (fun k : Fin m => (⟨2 * n - 2 - k.val, by omega⟩, mid, k)) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
        Fin.ext_iff, hmid] at hk
      simp only [Finset.mem_coe, S2, Finset.mem_filter, Finset.mem_univ, true_and, hmid]
      omega
    · intro k₁ _ k₂ _ h
      exact (Prod.mk.inj (Prod.mk.inj h).2).2
    · intro ⟨i, j, k⟩ h
      simp only [Finset.mem_coe, S2, Finset.mem_filter, Finset.mem_univ, true_and] at h
      refine ⟨k, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
          Fin.ext_iff, hmid]
        omega
      · ext <;> simp only [hmid] <;> omega
  have hS3 : S3.card = 2 * n - 2 := by
    rw [← hcard_other]
    symm
    refine Finset.card_nbij (fun i : Fin m => (i, ⟨2 * n - 2 - i.val, by omega⟩, mid)) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
        Fin.ext_iff, hmid] at hi
      simp only [Finset.mem_coe, S3, Finset.mem_filter, Finset.mem_univ, true_and, hmid]
      omega
    · intro i₁ _ i₂ _ h
      exact (Prod.mk.inj h).1
    · intro ⟨i, j, k⟩ h
      simp only [Finset.mem_coe, S3, Finset.mem_filter, Finset.mem_univ, true_and] at h
      refine ⟨i, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
          Fin.ext_iff, hmid]
        omega
      · ext <;> simp only [hmid] <;> omega
  rw [hunion, Finset.card_union_of_disjoint hd03, Finset.card_union_of_disjoint hd02,
    Finset.card_union_of_disjoint hd01, Finset.card_singleton, hS1, hS2, hS3]
  omega

private def extraPattern (r : Fin 12) : ℕ × ℕ × ℕ :=
  match r.val with
  | 0 => (1, 7, 8)
  | 1 => (1, 8, 7)
  | 2 => (7, 1, 8)
  | 3 => (7, 8, 1)
  | 4 => (8, 1, 7)
  | 5 => (8, 7, 1)
  | 6 => (2, 3, 9)
  | 7 => (2, 9, 3)
  | 8 => (3, 2, 9)
  | 9 => (3, 9, 2)
  | 10 => (9, 2, 3)
  | _ => (9, 3, 2)

private lemma extraPattern_inj : Function.Injective extraPattern := by
  decide

private lemma extraPattern_bounds (r : Fin 12) :
    1 ≤ (extraPattern r).1 ∧ (extraPattern r).1 ≤ 9 ∧
    1 ≤ (extraPattern r).2.1 ∧ (extraPattern r).2.1 ≤ 9 ∧
    1 ≤ (extraPattern r).2.2 ∧ (extraPattern r).2.2 ≤ 9 := by
  revert r; decide

open Classical in
private lemma card_extra_of_dvd {k : ℕ} (hk : 1 ≤ k) :
    (Finset.univ.filter fun t : Fin (2 * (5 * k) - 1) × Fin (2 * (5 * k) - 1) × Fin (2 * (5 * k) - 1) =>
      isExtra (5 * k) (t.1.val + 1) (t.2.1.val + 1) (t.2.2.val + 1)).card = 12 := by
  let m := 2 * (5 * k) - 1
  let f : Fin 12 → Fin m × Fin m × Fin m := fun r =>
    let p := extraPattern r
    have hp := extraPattern_bounds r
    have h1 : p.1 * k - 1 < m := by
      have : p.1 * k ≤ 9 * k := Nat.mul_le_mul_right k hp.2.1
      omega
    have h2 : p.2.1 * k - 1 < m := by
      have : p.2.1 * k ≤ 9 * k := Nat.mul_le_mul_right k hp.2.2.2.1
      omega
    have h3 : p.2.2 * k - 1 < m := by
      have : p.2.2 * k ≤ 9 * k := Nat.mul_le_mul_right k hp.2.2.2.2.2
      omega
    (⟨p.1 * k - 1, h1⟩, ⟨p.2.1 * k - 1, h2⟩, ⟨p.2.2 * k - 1, h3⟩)
  have hf_val : ∀ r : Fin 12,
      (f r).1.val + 1 = (extraPattern r).1 * k ∧
      (f r).2.1.val + 1 = (extraPattern r).2.1 * k ∧
      (f r).2.2.val + 1 = (extraPattern r).2.2 * k := by
    intro r
    have hp := extraPattern_bounds r
    have hpos1 : 1 ≤ (extraPattern r).1 * k := Nat.mul_pos hp.1 hk
    have hpos2 : 1 ≤ (extraPattern r).2.1 * k := Nat.mul_pos hp.2.2.1 hk
    have hpos3 : 1 ≤ (extraPattern r).2.2 * k := Nat.mul_pos hp.2.2.2.2.1 hk
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only [f] <;> omega
  have hbij : (Finset.univ : Finset (Fin 12)).card =
      (Finset.univ.filter fun t : Fin m × Fin m × Fin m =>
        isExtra (5 * k) (t.1.val + 1) (t.2.1.val + 1) (t.2.2.val + 1)).card := by
    refine Finset.card_nbij f ?_ ?_ ?_
    · intro r _
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, k, rfl, ?_⟩
      rcases hf_val r with ⟨h1, h2, h3⟩
      rw [h1, h2, h3]
      fin_cases r <;> simp [extraPattern]
    · intro r₁ _ r₂ _ h
      have h1 := hf_val r₁
      have h2 := hf_val r₂
      have heq1 : (extraPattern r₁).1 * k = (extraPattern r₂).1 * k := by
        rw [← h1.1, ← h2.1, h]
      have heq2 : (extraPattern r₁).2.1 * k = (extraPattern r₂).2.1 * k := by
        rw [← h1.2.1, ← h2.2.1, h]
      have heq3 : (extraPattern r₁).2.2 * k = (extraPattern r₂).2.2 * k := by
        rw [← h1.2.2, ← h2.2.2, h]
      apply extraPattern_inj
      exact Prod.ext (Nat.eq_of_mul_eq_mul_right hk heq1)
        (Prod.ext (Nat.eq_of_mul_eq_mul_right hk heq2) (Nat.eq_of_mul_eq_mul_right hk heq3))
    · intro ⟨i, j, l⟩ h
      have h' : isExtra (5 * k) (i.val + 1) (j.val + 1) (l.val + 1) :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp h)).2
      rcases h' with ⟨k', hk', hcases⟩
      have hkk : k' = k := by omega
      rw [hkk] at hcases
      have mk_wit : ∀ r : Fin 12,
          i.val + 1 = (extraPattern r).1 * k →
          j.val + 1 = (extraPattern r).2.1 * k →
          l.val + 1 = (extraPattern r).2.2 * k →
          ∃ r ∈ ((Finset.univ : Finset (Fin 12)) : Set (Fin 12)), f r = (i, j, l) := by
        intro r h1 h2 h3
        refine ⟨r, Finset.mem_coe.mpr (Finset.mem_univ r), ?_⟩
        rcases hf_val r with ⟨hf1, hf2, hf3⟩
        exact Prod.ext (Fin.ext (by dsimp only; omega))
          (Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega)))
      rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
        ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
        ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact mk_wit 0 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 1 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 2 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 3 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 4 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 5 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 6 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 7 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 8 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 9 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 10 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
      · exact mk_wit 11 (by simp [extraPattern, h1]) (by simp [extraPattern, h2]) (by simp [extraPattern, h3])
  rw [← hbij, Finset.card_univ, Fintype.card_fin]

open Classical in
theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    d (2 * n - 1) = if 5 ∣ n then 6 * n + 7 else 6 * n - 5 := by
  intro n hn
  let m := 2 * n - 1
  let Sol : Finset (Fin m × Fin m × Fin m) := Finset.univ.filter fun t =>
    ratio m t.1.val * ratio m t.2.1.val * ratio m t.2.2.val = 1
  have hncard : d m = Sol.card := by
    unfold d
    have hset : {t : Fin m × Fin m × Fin m |
        ratio m t.1 * ratio m t.2.1 * ratio m t.2.2 = 1} = (Sol : Set _) := by
      ext t; simp [Sol]
    rw [hset, Set.ncard_coe_finset]
  rw [hncard]
  let T : Finset (Fin m × Fin m × Fin m) := Finset.univ.filter fun t =>
    isTriv n (t.1.val + 1) (t.2.1.val + 1) (t.2.2.val + 1)
  let E : Finset (Fin m × Fin m × Fin m) := Finset.univ.filter fun t =>
    isExtra n (t.1.val + 1) (t.2.1.val + 1) (t.2.2.val + 1)
  have hSol : Sol = T ∪ E := by
    ext ⟨i, j, k⟩
    simp only [Sol, T, E, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact sol_iff hn i j k
  have hdisj : Disjoint T E := by
    rw [Finset.disjoint_left]
    intro ⟨i, j, k⟩ hT hE
    have hT' : isTriv n (i.val + 1) (j.val + 1) (k.val + 1) := (Finset.mem_filter.mp hT).2
    have hE' : isExtra n (i.val + 1) (j.val + 1) (k.val + 1) := (Finset.mem_filter.mp hE).2
    rcases hE' with ⟨k0, hk0, hcases⟩
    simp only [isTriv] at hT'
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  rw [hSol, Finset.card_union_of_disjoint hdisj, card_triv hn]
  split_ifs with h5
  · rcases h5 with ⟨k, rfl⟩
    have hk : 1 ≤ k := by omega
    have hEcard : E.card = 12 := card_extra_of_dvd hk
    rw [hEcard]
    omega
  · have hE0 : E = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro ⟨i, j, k⟩ _ hE
      rcases hE with ⟨k0, hk0, _⟩
      exact h5 ⟨k0, hk0⟩
    rw [hE0, Finset.card_empty, add_zero]

end OMA.OeisA387471Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a387471.main :=
  OMA.OeisA387471Proof.main_proof
