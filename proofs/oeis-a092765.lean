import OMAStatements.S_oeis_a092765

/-!
# Proof of OEIS A092765 (Peter Bala's stronger Gauss congruences)

Credit: Daniel Whorlow (@draonbioetl)

We prove that for every prime `p ≠ 3` and positive integers `n, k`,
`a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (2 * k)]`,
where `a n = ((1 + X + X ^ 3 + X ^ 4 : ℕ[X]) ^ n).coeff (2 * n)`.

Proof structure:
1. Factor `1 + X + X ^ 3 + X ^ 4 = (1 + X) * (1 + X ^ 3)` to obtain the explicit binomial sum
   `a n = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => 3 * j ≤ 2 * n),
            n.choose j * n.choose (2 * n - 3 * j)`.
2. For `M = n * p ^ k` and `N = n * p ^ (k - 1)`:
   - Every term with `¬ p ∣ j` also has `¬ p ∣ (2 * M - 3 * j)` (since `p ≠ 3`), so both
     `M.choose j` and `M.choose (2 * M - 3 * j)` are divisible by `p ^ k`, hence their product
     is divisible by `p ^ (2 * k)`.
   - Every term with `j = p * j'` satisfies
     `M.choose (p * j') * M.choose (2 * M - 3 * p * j') ≡ N.choose j' * N.choose (2 * N - 3 * j')`
     modulo `p ^ (2 * k)`, proved term-by-term via:
     * General Jacobsthal / Kazandzidis congruence for `p ≥ 5`, and
     * Signed 2-adic Jacobsthal congruence `C(2a, 2b) ≡ (-1)^(b*(a-b)) C(a, b)` for `p = 2`,
       where the signs `(-1)^(j'*(N-j'))` and `(-1)^(c*(N-c))` (for `c = 2*N - 3*j'`) agree
       and cancel out.
-/

open OMA.S_oeis_a092765

namespace OMA_A092765

open Finset Polynomial

/-! ### Part 1: Factorization of `a n` into a single binomial sum -/

private lemma coeff_one_add_X_pow_three (n m : ℕ) :
    ((1 + X ^ 3 : ℕ[X]) ^ n).coeff m = if 3 ∣ m then n.choose (m / 3) else 0 := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, finsetSum_coeff, ← pow_mul, coeff_mul_natCast, coeff_X_pow]
  by_cases h3 : 3 ∣ m
  · simp only [h3, ↓reduceIte]
    rcases h3 with ⟨q, rfl⟩
    rw [Nat.mul_div_cancel_left q (by decide : 0 < 3)]
    by_cases hq : q < n + 1
    · rw [Finset.sum_eq_single q]
      · simp
      · intro k _ hkq
        have : 3 * q ≠ 3 * k := fun h => hkq (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h).symm
        simp [this]
      · intro hnot; exact absurd (Finset.mem_range.mpr hq) hnot
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      have : 3 * q ≠ 3 * k := by omega
      simp [this]
  · simp only [h3, ↓reduceIte]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : m ≠ 3 * k := fun h => h3 ⟨k, h⟩
    simp [this]

private lemma coeff_one_add_X_pow (n m : ℕ) :
    ((1 + X : ℕ[X]) ^ n).coeff m = n.choose m := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, finsetSum_coeff, coeff_mul_natCast, coeff_X_pow]
  by_cases hm : m < n + 1
  · rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hkm; simp [hkm.symm]
    · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    have : m ≠ k := by omega
    simp [this]

private lemma a_eq_sum_choose (n : ℕ) :
    a n = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => 3 * j ≤ 2 * n),
      n.choose j * n.choose (2 * n - 3 * j) := by
  unfold a
  have hfac : (1 + X + X ^ 3 + X ^ 4 : ℕ[X]) = (1 + X) * (1 + X ^ 3) := by ring
  rw [hfac, mul_pow, coeff_mul]
  simp only [coeff_one_add_X_pow, coeff_one_add_X_pow_three]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
    n.choose x * (if 3 ∣ y then n.choose (y / 3) else 0)) (2 * n)]
  have hsum :
      ∑ k ∈ Finset.range (2 * n + 1),
          n.choose k * (if 3 ∣ (2 * n - k) then n.choose ((2 * n - k) / 3) else 0) =
      ∑ k ∈ (Finset.range (2 * n + 1)).filter (fun k => 3 ∣ (2 * n - k)),
          n.choose k * n.choose ((2 * n - k) / 3) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [hsum]
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => 2 * n - 3 * j) ?_ ?_ ?_ ?_
  · intro j hj _
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨by omega, ?_⟩
    rw [show 2 * n - (2 * n - 3 * j) = 3 * j by omega]
    exact dvd_mul_right 3 j
  · intro j1 hj1 _ j2 hj2 _ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2
    omega
  · intro k hk hne
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rcases hk.2 with ⟨j, hj⟩
    have hj_le : j ≤ n := by
      by_contra hgt
      have h0 : n.choose ((2 * n - k) / 3) = 0 := by
        rw [hj, Nat.mul_div_cancel_left j (by decide : 0 < 3)]
        exact Nat.choose_eq_zero_of_lt (by omega)
      exact hne (by rw [h0, mul_zero])
    refine ⟨j, ?_, ?_, by omega⟩
    · simp only [Finset.mem_filter, Finset.mem_range]; omega
    · intro h0
      apply hne
      have hdiv : (2 * n - k) / 3 = j := by rw [hj, Nat.mul_div_cancel_left j (by decide : 0 < 3)]
      rw [hdiv, show k = 2 * n - 3 * j by omega, mul_comm]
      exact h0
  · intro j hj _
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rw [show 2 * n - (2 * n - 3 * j) = 3 * j by omega,
      Nat.mul_div_cancel_left j (by decide : 0 < 3), mul_comm]

/-! ### Part 2: Elementary binomial and unit-sum lemmas -/

private lemma succ_mul_choose_eq (n k : ℕ) :
    (n + 1) * Nat.choose n k = (k + 1) * Nat.choose (n + 1) (k + 1) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Nat.choose_eq_zero_of_lt (show 1 < k + 2 by omega)]
  | succ n ih =>
    cases k with
    | zero => simp [Nat.choose_one_right]
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      have hpas1 : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
        Nat.choose_succ_succ n k
      have hpas2 : Nat.choose (n + 1 + 1) (k + 1 + 1) =
          Nat.choose (n + 1) (k + 1) + Nat.choose (n + 1) (k + 1 + 1) :=
        Nat.choose_succ_succ (n + 1) (k + 1)
      calc (n + 1 + 1) * Nat.choose (n + 1) (k + 1)
          = (n + 1) * Nat.choose n k + (n + 1) * Nat.choose n (k + 1) +
            Nat.choose (n + 1) (k + 1) := by rw [hpas1]; ring
        _ = (k + 1) * Nat.choose (n + 1) (k + 1) +
            (k + 1 + 1) * Nat.choose (n + 1) (k + 1 + 1) +
            Nat.choose (n + 1) (k + 1) := by rw [h1, h2]
        _ = (k + 1 + 1) * Nat.choose (n + 1 + 1) (k + 1 + 1) := by rw [hpas2]; ring

private lemma isUnit_prod_of_mem {R : Type*} [CommMonoid R] {α : Type*}
    (s : Finset α) (f : α → R) (h : ∀ x ∈ s, IsUnit (f x)) :
    IsUnit (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private lemma coprime_of_not_dvd_prime {p u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    Nat.Coprime u p :=
  (hp.coprime_iff_not_dvd.mpr hu).symm

private lemma isUnit_zmod_pow {p s u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    IsUnit (u : ZMod (p ^ s)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (coprime_of_not_dvd_prime hp hu).pow_right s

private lemma zmod_pow_mul_inv {p s u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    (u : ZMod (p ^ s)) * (u : ZMod (p ^ s))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_zmod_pow hp hu)

private lemma choose_dvd_pow_of_lt_val {p N b m v : ℕ} (hp : p.Prime)
    (hN : 0 < N) (hb : 0 < b) (hNm : p ^ m ∣ N) (hv : v = padicValNat p b) (hvm : v < m) :
    p ^ (m - v) ∣ N.choose b := by
  have : Fact p.Prime := ⟨hp⟩
  have hrel : b * N.choose b = N * (N - 1).choose (b - 1) := by
    have h := succ_mul_choose_eq (N - 1) (b - 1)
    rw [show N - 1 + 1 = N by omega, show b - 1 + 1 = b by omega] at h
    linarith
  have hbv : p ^ v ∣ b := hv ▸ pow_padicValNat_dvd
  rcases hbv with ⟨u, hu⟩
  have hund : ¬ p ∣ u := by
    intro hpu
    rcases hpu with ⟨u', rfl⟩
    have hd : p ^ (v + 1) ∣ b := ⟨u', by rw [hu, pow_succ]; ring⟩
    have := (padicValNat_dvd_iff_le (by omega : b ≠ 0)).mp hd
    omega
  have hd1 : p ^ m ∣ b * N.choose b := by
    rw [hrel]; exact dvd_mul_of_dvd_left hNm _
  have hd1' : p ^ v * p ^ (m - v) ∣ p ^ v * (u * N.choose b) := by
    rw [← pow_add, show v + (m - v) = m by omega, ← mul_assoc, ← hu]
    exact hd1
  have hd2 : p ^ (m - v) ∣ u * N.choose b := by
    rcases hd1' with ⟨q, hq⟩
    exact ⟨q, Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos v) (by linarith)⟩
  exact ((hp.coprime_iff_not_dvd.mpr hund).pow_left (m - v)).dvd_of_dvd_mul_left hd2

private lemma choose_dvd_of_not_dvd {p M j k : ℕ} (hp : p.Prime)
    (hM : 0 < M) (hMk : p ^ k ∣ M) (hnd : ¬ p ∣ j) :
    p ^ k ∣ M.choose j := by
  have hjpos : 0 < j := Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero p)
  have hrel : j * M.choose j = M * (M - 1).choose (j - 1) := by
    have h := succ_mul_choose_eq (M - 1) (j - 1)
    rw [show M - 1 + 1 = M by omega, show j - 1 + 1 = j by omega] at h
    linarith
  have hd1 : p ^ k ∣ j * M.choose j := by
    rw [hrel]; exact dvd_mul_of_dvd_left hMk _
  exact ((hp.coprime_iff_not_dvd.mpr hnd).pow_left k).dvd_of_dvd_mul_left hd1

private lemma prod_Icc_split_dvd (p m : ℕ) (hp : 1 ≤ p) (f : ℕ → ℕ) :
    ∏ u ∈ Finset.Icc 1 (p * m), f u =
      (∏ j ∈ Finset.Icc 1 m, f (p * j)) *
        (∏ u ∈ (Finset.range (p * m)).filter (fun u => ¬ p ∣ u), f u) := by
  have hpart : Finset.Icc 1 (p * m) =
      (Finset.Icc 1 m).image (fun j => p * j) ∪
      (Finset.range (p * m)).filter (fun u => ¬ p ∣ u) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨hu1, hum⟩
      by_cases hd : p ∣ u
      · left
        rcases hd with ⟨j, rfl⟩
        exact ⟨j, ⟨by nlinarith, by nlinarith⟩, rfl⟩
      · right
        refine ⟨?_, hd⟩
        have hne : u ≠ p * m := fun h => hd (h ▸ dvd_mul_right p m)
        omega
    · rintro (⟨j, ⟨hj1, hjm⟩, rfl⟩ | ⟨hult, hnd⟩)
      · exact ⟨by nlinarith, by nlinarith⟩
      · refine ⟨?_, by omega⟩
        by_contra h0
        exact hnd ((show u = 0 by omega) ▸ dvd_zero p)
  have hdisj : Disjoint ((Finset.Icc 1 m).image (fun j => p * j))
      ((Finset.range (p * m)).filter (fun u => ¬ p ∣ u)) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_image, Finset.mem_filter] at hu1 hu2
    rcases hu1 with ⟨j, _, rfl⟩
    exact hu2.2 (dvd_mul_right p j)
  rw [hpart, Finset.prod_union hdisj,
    Finset.prod_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]

private lemma choose_mul_prod_Icc (d b : ℕ) :
    Nat.choose (d + b) b * (∏ j ∈ Finset.Icc 1 b, j) =
      ∏ j ∈ Finset.Icc 1 b, (d + j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hIcc : Finset.Icc 1 (b + 1) = insert (b + 1) (Finset.Icc 1 b) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
    have hstep : (b + 1) * Nat.choose (d + (b + 1)) (b + 1) =
        (d + (b + 1)) * Nat.choose (d + b) b := by
      have h := succ_mul_choose_eq (d + b) b
      rw [show d + (b + 1) = d + b + 1 by omega]
      linarith
    calc Nat.choose (d + (b + 1)) (b + 1) * ((b + 1) * ∏ j ∈ Finset.Icc 1 b, j)
        = ((b + 1) * Nat.choose (d + (b + 1)) (b + 1)) * ∏ j ∈ Finset.Icc 1 b, j := by ring
      _ = (d + (b + 1)) * (Nat.choose (d + b) b * ∏ j ∈ Finset.Icc 1 b, j) := by rw [hstep]; ring
      _ = (d + (b + 1)) * ∏ j ∈ Finset.Icc 1 b, (d + j) := by rw [ih]

private lemma choose_mul_prod_nonmul (p a b : ℕ) (hp : 1 ≤ p) (hab : b ≤ a) :
    Nat.choose (p * a) (p * b) *
        (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), u) =
      Nat.choose a b *
        (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), (p * (a - b) + u)) := by
  set d := a - b
  have ha : d + b = a := Nat.sub_add_cancel hab
  have hpa : p * d + p * b = p * a := by rw [← mul_add, ha]
  have h1 := choose_mul_prod_Icc (p * d) (p * b)
  rw [hpa] at h1
  rw [prod_Icc_split_dvd p b hp (fun u => u),
      prod_Icc_split_dvd p b hp (fun u => p * d + u)] at h1
  have h2 := choose_mul_prod_Icc d b
  rw [ha] at h2
  have hpmul1 : ∏ j ∈ Finset.Icc 1 b, (p * j) = p ^ b * ∏ j ∈ Finset.Icc 1 b, j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]; simp
  have hpmul2 : ∏ j ∈ Finset.Icc 1 b, (p * d + p * j) =
      p ^ b * ∏ j ∈ Finset.Icc 1 b, (d + j) := by
    have : ∀ j, p * d + p * j = p * (d + j) := fun j => by ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]; simp
  rw [hpmul1, hpmul2, ← h2] at h1
  have hpos : 0 < p ^ b * ∏ j ∈ Finset.Icc 1 b, j :=
    mul_pos (pow_pos (by omega) b) (Finset.prod_pos fun j hj => (Finset.mem_Icc.mp hj).1)
  apply Nat.eq_of_mul_eq_mul_left hpos
  linarith

private lemma prod_one_add_of_sq_zero {R : Type*} [CommRing R] {α : Type*}
    (s : Finset α) (c : R) (hc : c ^ 2 = 0) (f : α → R) :
    ∏ x ∈ s, (1 + c * f x) = 1 + c * ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    linear_combination (f a * ∑ x ∈ s, f x) * hc

/-! ### Part 3: General Jacobsthal lemma for primes `p ≥ 5` -/

private lemma sum_inv_sq_units {p s : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  set N := p ^ s
  set S := (Finset.range N).filter (fun u => ¬ p ∣ u)
  have hNpos : 0 < N := pow_pos hp.pos s
  have h2nd : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
  have h3nd : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
  have h2u : IsUnit (2 : ZMod N) := by
    change IsUnit ((2 : ℕ) : ZMod N); exact isUnit_zmod_pow hp h2nd
  have h3u : IsUnit (3 : ZMod N) := by
    change IsUnit ((3 : ℕ) : ZMod N); exact isUnit_zmod_pow hp h3nd
  have hbij : ∑ u ∈ S, (((2 * u % N : ℕ) : ZMod N)⁻¹) ^ 2 = ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    refine Finset.sum_bij (fun u _ => 2 * u % N) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu ⊢
      refine ⟨Nat.mod_lt _ hNpos, ?_⟩
      intro hd
      have hpN : p ∣ N := dvd_pow_self p (by omega)
      have h2u_dvd : p ∣ 2 * u := by
        have hmod := Nat.div_add_mod (2 * u) N
        have : p ∣ N * (2 * u / N) + 2 * u % N := dvd_add (dvd_mul_of_dvd_left hpN _) hd
        rwa [hmod] at this
      rcases hp.dvd_mul.mp h2u_dvd with h2 | hu'
      · exact h2nd h2
      · exact hu.2 hu'
    · intro u1 hu1 u2 hu2 heq
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu1 hu2
      have hcast : ((2 * u1 % N : ℕ) : ZMod N) = ((2 * u2 % N : ℕ) : ZMod N) := by rw [heq]
      simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat] at hcast
      have hcancel := h2u.mul_left_cancel hcast
      have hval := congrArg ZMod.val hcancel
      rwa [ZMod.val_natCast_of_lt hu1.1, ZMod.val_natCast_of_lt hu2.1] at hval
    · intro v hv
      simp only [S, Finset.mem_filter, Finset.mem_range] at hv
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      set u := ((2 : ZMod N)⁻¹ * (v : ZMod N)).val
      have hu_lt : u < N := ZMod.val_lt _
      have hu_cast : (u : ZMod N) = (2 : ZMod N)⁻¹ * (v : ZMod N) := ZMod.natCast_zmod_val _
      have h2u_eq : ((2 * u % N : ℕ) : ZMod N) = (v : ZMod N) := by
        rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, hu_cast, ← mul_assoc,
          ZMod.mul_inv_of_unit _ h2u, one_mul]
      have h2u_nat : 2 * u % N = v := by
        have hval := congrArg ZMod.val h2u_eq
        rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ hNpos), ZMod.val_natCast_of_lt hv.1] at hval
      refine ⟨u, ?_, h2u_nat⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨hu_lt, fun hdu => hv.2 ?_⟩
      have hpN : p ∣ N := dvd_pow_self p (by omega)
      have hmod := Nat.div_add_mod (2 * u) N
      have h1 : p ∣ 2 * u := dvd_mul_of_dvd_right hdu 2
      rw [← h2u_nat]
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hpN _)).mp (hmod.symm ▸ h1)
    · intro _ _; rfl
  have h4 : ∑ u ∈ S, (((2 * u % N : ℕ) : ZMod N)⁻¹) ^ 2 =
      ((2 : ZMod N)⁻¹ ^ 2) * ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
    have hu_u : IsUnit (u : ZMod N) := isUnit_zmod_pow hp (Finset.mem_filter.mp hu).2
    have hmul_inv : ((2 : ZMod N) * (u : ZMod N))⁻¹ = (2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹ := by
      have h1 : ((2 : ZMod N) * (u : ZMod N)) * ((2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹) = 1 := by
        calc ((2 : ZMod N) * (u : ZMod N)) * ((2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹)
            = ((2 : ZMod N) * (2 : ZMod N)⁻¹) * ((u : ZMod N) * (u : ZMod N)⁻¹) := by ring
          _ = 1 := by rw [ZMod.mul_inv_of_unit _ h2u, ZMod.mul_inv_of_unit _ hu_u, mul_one]
      exact (h2u.mul hu_u).mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ (h2u.mul hu_u), h1])
    rw [hmul_inv, mul_pow]
  rw [h4] at hbij
  have h4_eq : (4 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) =
      ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    have h2sq : (4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2) = 1 := by
      calc (4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2)
          = ((2 : ZMod N) * (2 : ZMod N)⁻¹) ^ 2 := by ring
        _ = 1 := by rw [ZMod.mul_inv_of_unit _ h2u, one_pow]
    calc (4 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2)
        = (4 : ZMod N) * (((2 : ZMod N)⁻¹ ^ 2) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2)) := by rw [hbij]
      _ = ((4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2)) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) := by ring
      _ = ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by rw [h2sq, one_mul]
  have h3_eq : (3 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) = 0 := by
    linear_combination h4_eq
  exact h3u.mul_left_cancel (by rw [h3_eq, mul_zero])

private lemma sum_inv_sq_mul_block {p s c : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ u ∈ (Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hsplit : (Finset.range ((c + 1) * p ^ s)).filter (fun u => ¬ p ∣ u) =
        (Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u) ∪
        ((Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u)).image (fun u => c * p ^ s + u) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx, hnd⟩
        by_cases hlt : x < c * p ^ s
        · exact Or.inl ⟨hlt, hnd⟩
        · right
          have hlt2 : x - c * p ^ s < p ^ s := by rw [add_mul, one_mul] at hx; omega
          refine ⟨x - c * p ^ s, ⟨hlt2, ?_⟩, by omega⟩
          intro hd
          apply hnd
          have hpN : p ∣ c * p ^ s := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
          have := dvd_add hpN hd
          rwa [show c * p ^ s + (x - c * p ^ s) = x by omega] at this
      · rintro (⟨hlt, hnd⟩ | ⟨u, ⟨hu, hnd⟩, rfl⟩)
        · exact ⟨by nlinarith, hnd⟩
        · refine ⟨by nlinarith, fun hd => hnd ?_⟩
          have hpN : p ∣ c * p ^ s := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
          exact (Nat.dvd_add_right hpN).mp hd
    have hdisj : Disjoint
        ((Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u))
        (((Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u)).image (fun u => c * p ^ s + u)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx1 hx2
      rcases hx2 with ⟨u, _, rfl⟩; omega
    rw [hsplit, Finset.sum_union hdisj, ih, zero_add,
      Finset.sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)]
    have hcongr : ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u),
        (((c * p ^ s + u : ℕ) : ZMod (p ^ s))⁻¹) ^ 2 =
        ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u), ((u : ZMod (p ^ s))⁻¹) ^ 2 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [hcongr]
    exact sum_inv_sq_units hp h5 hs

private lemma sum_inv_pair_block {p t B : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (ht : 1 ≤ t)
    (hB : p ^ t ∣ B) :
    ∑ u ∈ (Finset.range B).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t)))⁻¹ = 0 := by
  rcases hB with ⟨c, rfl⟩
  rw [mul_comm]
  have hcongr : ∑ u ∈ (Finset.range (c * p ^ t)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ t)) * ((c * p ^ t - u : ℕ) : ZMod (p ^ t)))⁻¹ =
      - ∑ u ∈ (Finset.range (c * p ^ t)).filter (fun u => ¬ p ∣ u),
        ((u : ZMod (p ^ t))⁻¹) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    have hcast : ((c * p ^ t - u : ℕ) : ZMod (p ^ t)) = -(u : ZMod (p ^ t)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_sub]
    rw [hcast, mul_neg, ← sq]
    have huu : IsUnit ((u : ZMod (p ^ t)) ^ 2) := (isUnit_zmod_pow hp hu.2).pow 2
    have hneg_inv : (-((u : ZMod (p ^ t)) ^ 2))⁻¹ = -((u : ZMod (p ^ t))⁻¹ ^ 2) := by
      have h1 : (-((u : ZMod (p ^ t)) ^ 2)) * (-((u : ZMod (p ^ t))⁻¹ ^ 2)) = 1 := by
        calc (-((u : ZMod (p ^ t)) ^ 2)) * (-((u : ZMod (p ^ t))⁻¹ ^ 2))
            = ((u : ZMod (p ^ t)) * (u : ZMod (p ^ t))⁻¹) ^ 2 := by ring
          _ = 1 := by rw [zmod_pow_mul_inv hp hu.2, one_pow]
      exact huu.neg.mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ huu.neg, h1])
    exact hneg_inv
  rw [hcongr, sum_inv_sq_mul_block hp h5 ht, neg_zero]

private lemma P_sq_eq_one_plus_sum {p a b N : ℕ} (_hp : p.Prime) (hab : b ≤ a)
    (hc_sq : (((p * (a - b) * (p * a) : ℕ) : ZMod N)) ^ 2 = 0)
    (hcop_N : ∀ u, ¬ p ∣ u → IsUnit (u : ZMod N)) :
    let B := p * b
    let D := p * (a - b)
    let S := (Finset.range B).filter (fun u => ¬ p ∣ u)
    let P : ZMod N := ∏ u ∈ S, (1 + (D : ZMod N) * (u : ZMod N)⁻¹)
    P ^ 2 = 1 + ((D * (p * a) : ℕ) : ZMod N) *
      ∑ u ∈ S, ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹ := by
  intro B D S P
  have hP_rev : P = ∏ u ∈ S, (1 + (D : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) := by
    refine Finset.prod_bij (fun u _ => B - u) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu ⊢
      have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu.2 (h ▸ dvd_zero p))
      refine ⟨by omega, fun hd => hu.2 ?_⟩
      have hpB : p ∣ B := dvd_mul_right p b
      exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
    · intro u1 hu1 u2 hu2 heq
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu1 hu2; omega
    · intro v hv
      simp only [S, Finset.mem_filter, Finset.mem_range] at hv
      have hv1 : 1 ≤ v := Nat.pos_of_ne_zero (fun h => hv.2 (h ▸ dvd_zero p))
      refine ⟨B - v, ?_, by omega⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, fun hd => hv.2 ?_⟩
      have hpB : p ∣ B := dvd_mul_right p b
      exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
    · intro u hu
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
      rw [Nat.sub_sub_self (by omega)]
  have hDA_eq : (D : ZMod N) * ((D + B : ℕ) : ZMod N) = ((D * (p * a) : ℕ) : ZMod N) := by
    have : D + B = p * a := by simp only [D, B]; rw [← mul_add, Nat.sub_add_cancel hab]
    rw [this, ← Nat.cast_mul]
  have hP2 : P ^ 2 = ∏ u ∈ S, (1 + ((D * (p * a) : ℕ) : ZMod N) *
      ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹) := by
    rw [sq]
    conv_lhs => rhs; rw [hP_rev]
    simp only [P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    have hnd1 : ¬ p ∣ u := (Finset.mem_filter.mp hu).2
    have hult : u < B := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    have hnd2 : ¬ p ∣ (B - u) := fun hd => hnd1 <| by
      have hpB : p ∣ B := dvd_mul_right p b
      exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
    have hu1 := hcop_N u hnd1
    have hu2 := hcop_N (B - u) hnd2
    have hmul_inv : ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹ =
        (u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹ := by
      have h1 : ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) *
          ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) = 1 := by
        calc ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) *
              ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹)
            = ((u : ZMod N) * (u : ZMod N)⁻¹) *
              (((B - u : ℕ) : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
          _ = 1 := by rw [ZMod.mul_inv_of_unit _ hu1, ZMod.mul_inv_of_unit _ hu2, mul_one]
      exact (hu1.mul hu2).mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ (hu1.mul hu2), h1])
    rw [hmul_inv, ← hDA_eq]
    have hBu : (B : ZMod N) = (u : ZMod N) + ((B - u : ℕ) : ZMod N) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
    have hinv1 := ZMod.mul_inv_of_unit _ hu1
    have hinv2 := ZMod.mul_inv_of_unit _ hu2
    have hsum_inv : (u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹ =
        (B : ZMod N) * ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by
      rw [hBu]
      calc (u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹
          = (u : ZMod N)⁻¹ * (((B - u : ℕ) : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) +
            ((u : ZMod N) * (u : ZMod N)⁻¹) * ((B - u : ℕ) : ZMod N)⁻¹ := by rw [hinv1, hinv2]; ring
        _ = ((u : ZMod N) + ((B - u : ℕ) : ZMod N)) *
            ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
    push_cast
    calc (1 + (D : ZMod N) * (u : ZMod N)⁻¹) * (1 + (D : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹)
        = 1 + (D : ZMod N) * ((u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹) +
          (D : ZMod N) ^ 2 * ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
      _ = 1 + (D : ZMod N) * ((D : ZMod N) + (B : ZMod N)) *
          ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by rw [hsum_inv]; ring
  rw [hP2, prod_one_add_of_sq_zero S _ hc_sq]

private lemma jacobsthal_gen {p a b t e : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hab : b ≤ a)
    (ht : 1 ≤ t) (hte : t ≤ e) (hB : p ^ t ∣ p * b) (hDA : p ^ e ∣ (p * (a - b)) * (p * a)) :
    (Nat.choose (p * a) (p * b) : ZMod (p ^ (e + t))) =
      (Nat.choose a b : ZMod (p ^ (e + t))) := by
  set N := p ^ (e + t)
  set B := p * b
  set D := p * (a - b)
  set S := (Finset.range B).filter (fun u => ¬ p ∣ u)
  have hNpos : 0 < N := pow_pos hp.pos _
  have hprod_nat := choose_mul_prod_nonmul p a b hp.one_le hab
  have hprod_z : (Nat.choose (p * a) (p * b) : ZMod N) * (∏ u ∈ S, (u : ZMod N)) =
      (Nat.choose a b : ZMod N) * (∏ u ∈ S, ((D + u : ℕ) : ZMod N)) := by
    have hc := congrArg (fun n : ℕ => (n : ZMod N)) hprod_nat
    simpa only [Nat.cast_mul, Nat.cast_prod] using hc
  have hU : IsUnit (∏ u ∈ S, (u : ZMod N)) :=
    isUnit_prod_of_mem _ _ fun u hu => isUnit_zmod_pow hp (Finset.mem_filter.mp hu).2
  set P : ZMod N := ∏ u ∈ S, (1 + (D : ZMod N) * (u : ZMod N)⁻¹)
  have hprod_P : (∏ u ∈ S, ((D + u : ℕ) : ZMod N)) = (∏ u ∈ S, (u : ZMod N)) * P := by
    simp only [P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    have hinv := zmod_pow_mul_inv (s := e + t) hp (Finset.mem_filter.mp hu).2
    push_cast
    calc (D : ZMod N) + (u : ZMod N)
        = (u : ZMod N) + (D : ZMod N) * ((u : ZMod N) * (u : ZMod N)⁻¹) := by rw [hinv, mul_one]; ring
      _ = (u : ZMod N) * (1 + (D : ZMod N) * (u : ZMod N)⁻¹) := by ring
  have hP_eq_one : P = 1 := by
    have hc_sq : (((D * (p * a) : ℕ) : ZMod N)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact dvd_trans (by rw [← pow_mul]; exact pow_dvd_pow p (by omega))
        (pow_dvd_pow_of_dvd hDA 2)
    have hP2 := P_sq_eq_one_plus_sum (p := p) (a := a) (b := b) (N := N) hp hab hc_sq
      (fun u hu => isUnit_zmod_pow (s := e + t) hp hu)
    dsimp only at hP2
    set sum_inv : ZMod N := ∑ u ∈ S, ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹
    have hproj_sum : ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t)) sum_inv = 0 := by
      set φ := ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t))
      have hmap : φ sum_inv = ∑ u ∈ S, ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t)))⁻¹ := by
        simp only [sum_inv, map_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hnd1 : ¬ p ∣ u := (Finset.mem_filter.mp hu).2
        have hult : u < B := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
        have hnd2 : ¬ p ∣ (B - u) := fun hd => hnd1 <| by
          have hpB : p ∣ B := dvd_mul_right p b
          exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
        have huN : IsUnit ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) :=
          (isUnit_zmod_pow hp hnd1).mul (isUnit_zmod_pow hp hnd2)
        have hut : IsUnit ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t))) :=
          (isUnit_zmod_pow hp hnd1).mul (isUnit_zmod_pow hp hnd2)
        have h1 := congrArg φ (ZMod.mul_inv_of_unit _ huN)
        simp only [map_mul, map_natCast, map_one] at h1
        exact hut.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ hut])
      rw [hmap]
      exact sum_inv_pair_block hp h5 ht hB
    have hmul_zero : ((D * (p * a) : ℕ) : ZMod N) * sum_inv = 0 := by
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      have hdvd_sum : p ^ t ∣ sum_inv.val := by
        rw [← ZMod.natCast_eq_zero_iff]
        have h1 : ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t))
            (sum_inv.val : ZMod N) = (sum_inv.val : ZMod (p ^ t)) := map_natCast _ _
        rw [← h1, ZMod.natCast_zmod_val, hproj_sum]
      rcases hDA with ⟨q1, hq1⟩
      rcases hdvd_sum with ⟨q2, hq2⟩
      rw [← ZMod.natCast_zmod_val sum_inv, hq1, hq2, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      dsimp only [N]
      rw [pow_add]
      exact ⟨q1 * q2, by ring⟩
    rw [hmul_zero, add_zero] at hP2
    have hP_mod_p : ZMod.castHom (dvd_pow_self p (by omega : e + t ≠ 0)) (ZMod p) P = 1 := by
      simp only [P, map_prod, map_add, map_one, map_mul, map_natCast]
      have hD0 : (D : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact dvd_mul_right p (a - b)
      simp [hD0]
    have hP1_unit : IsUnit (P + 1) := by
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      rw [← ZMod.natCast_zmod_val (P + 1), ZMod.isUnit_iff_coprime]
      refine (coprime_of_not_dvd_prime hp ?_).pow_right (e + t)
      intro hd
      have h0 : ((P + 1).val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
      have h1 : ZMod.castHom (dvd_pow_self p (by omega : e + t ≠ 0)) (ZMod p) (P + 1) = 0 := by
        rw [← ZMod.natCast_zmod_val (P + 1), map_natCast, h0]
      rw [map_add, map_one, hP_mod_p] at h1
      have h20 : ((2 : ℕ) : ZMod p) = 0 := by simpa only [Nat.cast_ofNat, one_add_one_eq_two] using h1
      have hd2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
      have := Nat.le_of_dvd (by decide) hd2; omega
    have hdiff : (P + 1) * (P - 1) = 0 := by linear_combination hP2
    exact sub_eq_zero.mp (hP1_unit.mul_left_cancel (by rw [hdiff, mul_zero]))
  rw [hprod_P, hP_eq_one, mul_one] at hprod_z
  exact hU.mul_right_cancel hprod_z

/-! ### Part 4: Signed 2-adic Jacobsthal lemma for `p = 2` -/

private lemma sum_inv_sq_units_two (t : ℕ) :
    ∑ u ∈ (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
      ((u : ZMod (2 ^ t))⁻¹) ^ 2 = 0 := by
  induction t with
  | zero =>
    change (∑ u ∈ (Finset.range (2 ^ (0 + 1))).filter (fun u => ¬ 2 ∣ u),
      ((u : ZMod 1)⁻¹) ^ 2) = 0
    exact Subsingleton.elim _ _
  | succ t ih =>
    have hsplit : (Finset.range (2 ^ (t + 2))).filter (fun u => ¬ 2 ∣ u) =
        (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u) ∪
        ((Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u)).image (fun u => 2 ^ (t + 1) + u) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx, hnd⟩
        by_cases hlt : x < 2 ^ (t + 1)
        · exact Or.inl ⟨hlt, hnd⟩
        · right
          have hpow : 2 ^ (t + 2) = 2 ^ (t + 1) + 2 ^ (t + 1) := by rw [pow_succ]; ring
          refine ⟨x - 2 ^ (t + 1), ⟨by omega, ?_⟩, by omega⟩
          intro hd
          apply hnd
          have h2 : 2 ∣ 2 ^ (t + 1) := dvd_pow_self 2 (by omega)
          have := dvd_add h2 hd
          rwa [show 2 ^ (t + 1) + (x - 2 ^ (t + 1)) = x by omega] at this
      · rintro (⟨hlt, hnd⟩ | ⟨u, ⟨hu, hnd⟩, rfl⟩)
        · have hpow : 2 ^ (t + 2) = 2 ^ (t + 1) + 2 ^ (t + 1) := by rw [pow_succ]; ring
          exact ⟨by omega, hnd⟩
        · have hpow : 2 ^ (t + 2) = 2 ^ (t + 1) + 2 ^ (t + 1) := by rw [pow_succ]; ring
          refine ⟨by omega, fun hd => hnd ?_⟩
          have h2 : 2 ∣ 2 ^ (t + 1) := dvd_pow_self 2 (by omega)
          exact (Nat.dvd_add_right h2).mp hd
    have hdisj : Disjoint
        ((Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u))
        (((Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u)).image (fun u => 2 ^ (t + 1) + u)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx1 hx2
      rcases hx2 with ⟨u, _, rfl⟩; omega
    rw [hsplit, Finset.sum_union hdisj,
      Finset.sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)]
    have hshift : ∑ u ∈ (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
        (((2 ^ (t + 1) + u : ℕ) : ZMod (2 ^ (t + 1)))⁻¹) ^ 2 =
        ∑ u ∈ (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
          ((u : ZMod (2 ^ (t + 1)))⁻¹) ^ 2 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
    rw [hshift, ← two_mul]
    set S : ZMod (2 ^ (t + 1)) :=
      ∑ u ∈ (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u), ((u : ZMod (2 ^ (t + 1)))⁻¹) ^ 2
    have hproj : ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ t)) (ZMod (2 ^ t)) S = 0 := by
      set φ := ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ t)) (ZMod (2 ^ t))
      have hmap : φ S = ∑ u ∈ (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
          ((u : ZMod (2 ^ t))⁻¹) ^ 2 := by
        simp only [S, map_sum, map_pow]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hnd : ¬ 2 ∣ u := (Finset.mem_filter.mp hu).2
        have hu1 := isUnit_zmod_pow (s := t + 1) Nat.prime_two hnd
        have hu0 := isUnit_zmod_pow (s := t) Nat.prime_two hnd
        have h1 := congrArg φ (ZMod.mul_inv_of_unit _ hu1)
        simp only [map_mul, map_natCast, map_one] at h1
        congr 1
        exact hu0.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ hu0])
      rw [hmap]
      exact ih
    have : NeZero (2 ^ (t + 1)) := ⟨pow_ne_zero _ (by decide)⟩
    have hdvd : 2 ^ t ∣ S.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      have h1 : ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ t)) (ZMod (2 ^ t))
          (S.val : ZMod (2 ^ (t + 1))) = (S.val : ZMod (2 ^ t)) := map_natCast _ _
      rw [← h1, ZMod.natCast_zmod_val, hproj]
    rcases hdvd with ⟨q, hq⟩
    rw [← ZMod.natCast_zmod_val S, hq]
    have h2eq : (2 : ZMod (2 ^ (t + 1))) * ((2 ^ t * q : ℕ) : ZMod (2 ^ (t + 1))) =
        ((2 ^ (t + 1) * q : ℕ) : ZMod (2 ^ (t + 1))) := by
      rw [pow_succ']; push_cast; ring
    rw [h2eq, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private lemma sum_inv_pair_block_two {t b : ℕ} (hB : 2 ^ t ∣ b) :
    ∑ u ∈ (Finset.range (2 * b)).filter (fun u => ¬ 2 ∣ u),
      ((u : ZMod (2 ^ t)) * ((2 * b - u : ℕ) : ZMod (2 ^ t)))⁻¹ = 0 := by
  rcases hB with ⟨c, rfl⟩
  rw [show 2 * (2 ^ t * c) = c * 2 ^ (t + 1) by rw [pow_succ']; ring]
  have hcongr : ∑ u ∈ (Finset.range (c * 2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
      ((u : ZMod (2 ^ t)) * ((c * 2 ^ (t + 1) - u : ℕ) : ZMod (2 ^ t)))⁻¹ =
      - ∑ u ∈ (Finset.range (c * 2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
        ((u : ZMod (2 ^ t))⁻¹) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    have hcast : ((c * 2 ^ (t + 1) - u : ℕ) : ZMod (2 ^ t)) = -(u : ZMod (2 ^ t)) := by
      rw [Nat.cast_sub (by omega), pow_succ, show c * (2 ^ t * 2) = (2 * c) * 2 ^ t by ring,
        Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_sub]
    rw [hcast, mul_neg, ← sq]
    have huu : IsUnit ((u : ZMod (2 ^ t)) ^ 2) := (isUnit_zmod_pow Nat.prime_two hu.2).pow 2
    have hneg_inv : (-((u : ZMod (2 ^ t)) ^ 2))⁻¹ = -((u : ZMod (2 ^ t))⁻¹ ^ 2) := by
      have h1 : (-((u : ZMod (2 ^ t)) ^ 2)) * (-((u : ZMod (2 ^ t))⁻¹ ^ 2)) = 1 := by
        calc (-((u : ZMod (2 ^ t)) ^ 2)) * (-((u : ZMod (2 ^ t))⁻¹ ^ 2))
            = ((u : ZMod (2 ^ t)) * (u : ZMod (2 ^ t))⁻¹) ^ 2 := by ring
          _ = 1 := by rw [zmod_pow_mul_inv Nat.prime_two hu.2, one_pow]
      exact huu.neg.mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ huu.neg, h1])
    exact hneg_inv
  rw [hcongr, neg_eq_zero]
  clear hcongr
  induction c with
  | zero => simp
  | succ c ih =>
    have hsplit : (Finset.range ((c + 1) * 2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u) =
        (Finset.range (c * 2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u) ∪
        ((Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u)).image
          (fun u => c * 2 ^ (t + 1) + u) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx, hnd⟩
        by_cases hlt : x < c * 2 ^ (t + 1)
        · exact Or.inl ⟨hlt, hnd⟩
        · right
          have hlt2 : x - c * 2 ^ (t + 1) < 2 ^ (t + 1) := by rw [add_mul, one_mul] at hx; omega
          refine ⟨x - c * 2 ^ (t + 1), ⟨hlt2, ?_⟩, by omega⟩
          intro hd
          apply hnd
          have h2 : 2 ∣ c * 2 ^ (t + 1) := dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) c
          have := dvd_add h2 hd
          rwa [show c * 2 ^ (t + 1) + (x - c * 2 ^ (t + 1)) = x by omega] at this
      · rintro (⟨hlt, hnd⟩ | ⟨u, ⟨hu, hnd⟩, rfl⟩)
        · exact ⟨by nlinarith, hnd⟩
        · refine ⟨by nlinarith, fun hd => hnd ?_⟩
          have h2 : 2 ∣ c * 2 ^ (t + 1) := dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) c
          exact (Nat.dvd_add_right h2).mp hd
    have hdisj : Disjoint
        ((Finset.range (c * 2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u))
        (((Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u)).image
          (fun u => c * 2 ^ (t + 1) + u)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx1 hx2
      rcases hx2 with ⟨u, _, rfl⟩; omega
    rw [hsplit, Finset.sum_union hdisj, ih, zero_add,
      Finset.sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)]
    have hshift : ∑ u ∈ (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
        (((c * 2 ^ (t + 1) + u : ℕ) : ZMod (2 ^ t))⁻¹) ^ 2 =
        ∑ u ∈ (Finset.range (2 ^ (t + 1))).filter (fun u => ¬ 2 ∣ u),
          ((u : ZMod (2 ^ t))⁻¹) ^ 2 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      have hc : c * 2 ^ (t + 1) = (2 * c) * 2 ^ t := by rw [pow_succ]; ring
      rw [hc]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [hshift]
    exact sum_inv_sq_units_two t

private lemma jacobsthal_two_signed {a b t e d : ℕ} (hab : b ≤ a)
    (he : 2 ≤ e) (hte : t ≤ e) (hB : 2 ^ t ∣ b) (hDA : 2 ^ e ∣ (2 * (a - b)) * (2 * a))
    (hd : 2 ^ d ∣ Nat.choose a b) :
    ((2 ^ (d + e + t - 1) : ℕ) : ℤ) ∣
      ((Nat.choose (2 * a) (2 * b) : ℤ) - (-1 : ℤ) ^ (b * (a - b)) * (Nat.choose a b : ℤ)) := by
  set N := 2 ^ (e + t)
  set B := 2 * b
  set D := 2 * (a - b)
  set S := (Finset.range B).filter (fun u => ¬ 2 ∣ u)
  have hNpos : 0 < N := pow_pos (by decide) _
  set P : ZMod N := ∏ u ∈ S, (1 + (D : ZMod N) * (u : ZMod N)⁻¹)
  have hc_sq : (((D * (2 * a) : ℕ) : ZMod N)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact dvd_trans (by rw [← pow_mul]; exact pow_dvd_pow 2 (by omega))
      (pow_dvd_pow_of_dvd hDA 2)
  have hP2 := P_sq_eq_one_plus_sum (p := 2) (a := a) (b := b) (N := N) Nat.prime_two hab hc_sq
    (fun u hu => isUnit_zmod_pow (s := e + t) Nat.prime_two hu)
  dsimp only at hP2
  set sum_inv : ZMod N := ∑ u ∈ S, ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹
  have hproj_sum : ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left t e)) (ZMod (2 ^ t)) sum_inv = 0 := by
    set φ := ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left t e)) (ZMod (2 ^ t))
    have hmap : φ sum_inv = ∑ u ∈ S, ((u : ZMod (2 ^ t)) * ((B - u : ℕ) : ZMod (2 ^ t)))⁻¹ := by
      simp only [sum_inv, map_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hnd1 : ¬ 2 ∣ u := (Finset.mem_filter.mp hu).2
      have hult : u < B := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
      have hnd2 : ¬ 2 ∣ (B - u) := fun hd2 => hnd1 <| by
        have hpB : 2 ∣ B := dvd_mul_right 2 b
        exact (Nat.dvd_add_right hd2).mp (by rwa [Nat.sub_add_cancel (by omega)])
      have huN : IsUnit ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) :=
        (isUnit_zmod_pow Nat.prime_two hnd1).mul (isUnit_zmod_pow Nat.prime_two hnd2)
      have hut : IsUnit ((u : ZMod (2 ^ t)) * ((B - u : ℕ) : ZMod (2 ^ t))) :=
        (isUnit_zmod_pow Nat.prime_two hnd1).mul (isUnit_zmod_pow Nat.prime_two hnd2)
      have h1 := congrArg φ (ZMod.mul_inv_of_unit _ huN)
      simp only [map_mul, map_natCast, map_one] at h1
      exact hut.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ hut])
    rw [hmap]
    exact sum_inv_pair_block_two hB
  have hmul_zero : ((D * (2 * a) : ℕ) : ZMod N) * sum_inv = 0 := by
    have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
    have hdvd_sum : 2 ^ t ∣ sum_inv.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      have h1 : ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left t e)) (ZMod (2 ^ t))
          (sum_inv.val : ZMod N) = (sum_inv.val : ZMod (2 ^ t)) := map_natCast _ _
      rw [← h1, ZMod.natCast_zmod_val, hproj_sum]
    rcases hDA with ⟨q1, hq1⟩
    rcases hdvd_sum with ⟨q2, hq2⟩
    rw [← ZMod.natCast_zmod_val sum_inv, hq1, hq2, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    dsimp only [N]
    rw [pow_add]
    exact ⟨q1 * q2, by ring⟩
  rw [hmul_zero, add_zero] at hP2
  -- Compute P mod 4 = (-1)^(b * (a - b))!
  have h4_dvd : 4 ∣ N := by
    dsimp only [N]
    exact dvd_trans (by decide : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 (by omega))
  set ψ := ZMod.castHom h4_dvd (ZMod 4)
  have hScard : S.card = b := by
    have hSeq : S = (Finset.range b).image (fun k => 2 * k + 1) := by
      ext u
      simp only [S, B, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hu, hnd⟩
        exact ⟨u / 2, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨by omega, by omega⟩
    rw [hSeq, Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have hP_mod4 : ψ P = (((-1 : ℤ) ^ (b * (a - b)) : ℤ) : ZMod 4) := by
    simp only [P, map_prod, map_add, map_one, map_mul, map_natCast]
    have hterm : ∀ u ∈ S, (1 : ZMod 4) + (D : ZMod 4) * ψ ((u : ZMod N)⁻¹) =
        (((-1 : ℤ) ^ (a - b) : ℤ) : ZMod 4) := by
      intro u hu
      have hnd : ¬ 2 ∣ u := (Finset.mem_filter.mp hu).2
      have huN := isUnit_zmod_pow (s := e + t) Nat.prime_two hnd
      have hu4 : IsUnit (u : ZMod 4) := by
        change IsUnit (u : ZMod (2 ^ 2)); exact isUnit_zmod_pow Nat.prime_two hnd
      have hinv4 : ψ ((u : ZMod N)⁻¹) = (u : ZMod 4)⁻¹ := by
        have h1 := congrArg ψ (ZMod.mul_inv_of_unit _ huN)
        simp only [map_mul, map_natCast, map_one] at h1
        exact hu4.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ hu4])
      rw [hinv4]
      have hu_odd : (u : ZMod 4)⁻¹ = 1 ∨ (u : ZMod 4)⁻¹ = 3 := by
        have hmod : u % 4 = 1 ∨ u % 4 = 3 := by omega
        rcases hmod with h1 | h3
        · left
          have hu1 : (u : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
          rw [hu1, ← one_mul (1 : ZMod 4)⁻¹, ZMod.mul_inv_of_unit _ isUnit_one]
        · right
          have hu3 : (u : ZMod 4) = 3 := by rw [← ZMod.natCast_mod, h3]; rfl
          rw [hu3] at hu4 ⊢
          have h33 : (3 : ZMod 4) * 3 = 1 := by decide
          exact hu4.mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ hu4, h33])
      have hDu : (D : ZMod 4) * (u : ZMod 4)⁻¹ = (D : ZMod 4) := by
        dsimp only [D]
        rcases hu_odd with h1 | h3
        · rw [h1, mul_one]
        · rw [h3]; push_cast
          have h6 : (2 : ZMod 4) * 3 = 2 := by decide
          calc (2 : ZMod 4) * ((a - b : ℕ) : ZMod 4) * 3
              = (2 * 3 : ZMod 4) * ((a - b : ℕ) : ZMod 4) := by ring
            _ = 2 * ((a - b : ℕ) : ZMod 4) := by rw [h6]
      rw [hDu]
      dsimp only [D]
      have h4z : (4 : ZMod 4) = 0 := by decide
      rcases Nat.even_or_odd (a - b) with ⟨q, hq⟩ | ⟨q, hq⟩
      · have h2q : ((2 * (a - b) : ℕ) : ZMod 4) = 0 := by
          rw [hq, show 2 * (q + q) = 4 * q by ring, Nat.cast_mul, Nat.cast_ofNat, h4z, zero_mul]
        rw [h2q, add_zero, hq, show q + q = 2 * q by ring, pow_mul]
        norm_num
      · have h2q : ((2 * (a - b) : ℕ) : ZMod 4) = 2 := by
          rw [hq, show 2 * (2 * q + 1) = 4 * q + 2 by ring]
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h4z, zero_mul, zero_add]
        rw [h2q, hq, pow_add, pow_mul]
        norm_num; decide
    rw [Finset.prod_congr rfl hterm, Finset.prod_const, hScard, ← Int.cast_pow, ← pow_mul, mul_comm]
  -- Deduce P = (-1)^(b*(a-b)) in ZMod (2^(e+t-1))!
  set s : ℤ := (-1 : ℤ) ^ (b * (a - b))
  have hs_sq : s ^ 2 = 1 := by
    dsimp only [s]; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hP_sub : ((2 ^ (e + t - 1) : ℕ) : ℤ) ∣ ((P.val : ℤ) - s) := by
    have h4_sub : (4 : ℤ) ∣ ((P.val : ℤ) - s) := by
      change ((4 : ℕ) : ℤ) ∣ ((P.val : ℤ) - s)
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, sub_eq_zero]
      have h1 : ψ (P.val : ZMod N) = (P.val : ZMod 4) := map_natCast _ _
      rw [← h1, ZMod.natCast_zmod_val, hP_mod4]
    have hN_sq : ((N : ℕ) : ℤ) ∣ (((P.val : ℤ) - s) * ((P.val : ℤ) + s)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hcast : (((P.val : ℤ) - s) * ((P.val : ℤ) + s) : ℤ) = (P.val : ℤ) ^ 2 - 1 := by
        linear_combination -hs_sq
      rw [hcast, Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one,
        ZMod.natCast_zmod_val, hP2, sub_self]
    rcases h4_sub with ⟨q, hq⟩
    have hadd : (P.val : ℤ) + s = 2 * (2 * q + s) := by linarith
    have hodd_w : IsCoprime ((2 ^ (e + t - 1) : ℕ) : ℤ) (2 * q + s) := by
      have hs_odd : s = 1 ∨ s = -1 := by
        rcases Nat.even_or_odd (b * (a - b)) with ⟨k, hk⟩ | ⟨k, hk⟩
        · left; dsimp only [s]; rw [hk, show k + k = 2 * k by ring, pow_mul]; norm_num
        · right; dsimp only [s]; rw [hk, pow_add, pow_mul]; norm_num
      have h2_cop : IsCoprime (2 : ℤ) (2 * q + s) := by
        rcases hs_odd with hs1 | hsm1
        · exact ⟨-q, 1, by rw [hs1]; ring⟩
        · exact ⟨q, -1, by rw [hsm1]; ring⟩
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using h2_cop.pow_left (m := e + t - 1)
    rw [hadd] at hN_sq
    have hN_split : ((N : ℕ) : ℤ) = 2 * ((2 ^ (e + t - 1) : ℕ) : ℤ) := by
      dsimp only [N]
      have : 2 ^ (e + t) = 2 * 2 ^ (e + t - 1) := by
        conv_lhs => rw [show e + t = (e + t - 1) + 1 by omega, pow_succ']
      exact_mod_cast this
    rw [hN_split] at hN_sq
    have hcancel : ((2 ^ (e + t - 1) : ℕ) : ℤ) ∣ (2 * q + s) * ((P.val : ℤ) - s) := by
      rcases hN_sq with ⟨r, hr⟩
      exact ⟨r, by linarith⟩
    exact hodd_w.dvd_of_dvd_mul_left hcancel
  -- Convert P ≡ s (mod 2^(e+t-1)) to product congruence and multiply by C(a, b)!
  have hprod_P : (∏ u ∈ S, ((D + u : ℕ) : ZMod N)) = (∏ u ∈ S, (u : ZMod N)) * P := by
    simp only [P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    have hinv := zmod_pow_mul_inv (s := e + t) Nat.prime_two (Finset.mem_filter.mp hu).2
    push_cast
    calc (D : ZMod N) + (u : ZMod N)
        = (u : ZMod N) + (D : ZMod N) * ((u : ZMod N) * (u : ZMod N)⁻¹) := by rw [hinv, mul_one]; ring
      _ = (u : ZMod N) * (1 + (D : ZMod N) * (u : ZMod N)⁻¹) := by ring
  have hprod_dvd : ((2 ^ (e + t - 1) : ℕ) : ℤ) ∣
      ((∏ u ∈ S, (D + u) : ℕ) - s * ((∏ u ∈ S, u : ℕ) : ℤ)) := by
    have h1 : ((N : ℕ) : ℤ) ∣ ((∏ u ∈ S, (D + u) : ℕ) - (∏ u ∈ S, u : ℕ) * (P.val : ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
      simpa only [Nat.cast_prod] using hprod_P
    have h1' : ((2 ^ (e + t - 1) : ℕ) : ℤ) ∣
        ((∏ u ∈ S, (D + u) : ℕ) - (∏ u ∈ S, u : ℕ) * (P.val : ℤ)) :=
      dvd_trans (by exact_mod_cast pow_dvd_pow 2 (show e + t - 1 ≤ e + t by omega)) h1
    have h2 : ((2 ^ (e + t - 1) : ℕ) : ℤ) ∣ ((∏ u ∈ S, u : ℕ) : ℤ) * ((P.val : ℤ) - s) :=
      dvd_mul_of_dvd_right hP_sub _
    have heq : (((∏ u ∈ S, (D + u) : ℕ) : ℤ) - s * ((∏ u ∈ S, u : ℕ) : ℤ)) =
        (((∏ u ∈ S, (D + u) : ℕ) : ℤ) - ((∏ u ∈ S, u : ℕ) : ℤ) * (P.val : ℤ)) +
          ((∏ u ∈ S, u : ℕ) : ℤ) * ((P.val : ℤ) - s) := by ring
    rw [heq]
    exact dvd_add h1' h2
  have hprod_nat := choose_mul_prod_nonmul 2 a b (by decide) hab
  have hprod_int : (Nat.choose (2 * a) (2 * b) : ℤ) * ((∏ u ∈ S, u : ℕ) : ℤ) =
      (Nat.choose a b : ℤ) * ((∏ u ∈ S, (D + u) : ℕ) : ℤ) := by exact_mod_cast hprod_nat
  have hd_int : ((2 ^ d : ℕ) : ℤ) ∣ (Nat.choose a b : ℤ) := by exact_mod_cast hd
  have hmul_dvd : ((2 ^ (d + e + t - 1) : ℕ) : ℤ) ∣
      (((Nat.choose (2 * a) (2 * b) : ℤ) - s * (Nat.choose a b : ℤ)) * ((∏ u ∈ S, u : ℕ) : ℤ)) := by
    have hsplit : d + e + t - 1 = d + (e + t - 1) := by omega
    rw [hsplit, pow_add, Nat.cast_mul]
    have heq : (((Nat.choose (2 * a) (2 * b) : ℤ) - s * (Nat.choose a b : ℤ)) *
          ((∏ u ∈ S, u : ℕ) : ℤ)) =
        (Nat.choose a b : ℤ) * (((∏ u ∈ S, (D + u) : ℕ) : ℤ) - s * ((∏ u ∈ S, u : ℕ) : ℤ)) := by
      linear_combination hprod_int
    rw [heq]
    exact mul_dvd_mul hd_int hprod_dvd
  have hcop_U : IsCoprime ((2 ^ (d + e + t - 1) : ℕ) : ℤ) ((∏ u ∈ S, u : ℕ) : ℤ) := by
    have hodd_prod : ¬ 2 ∣ ∏ u ∈ S, u := by
      intro hd2
      rcases (Nat.prime_two.prime.dvd_finsetProd_iff id).mp hd2 with ⟨u, hu, h2u⟩
      exact (Finset.mem_filter.mp hu).2 h2u
    have hc : Nat.Coprime (2 ^ (d + e + t - 1)) (∏ u ∈ S, u) :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr hodd_prod).pow_left _
    exact_mod_cast hc.isCoprime
  exact hcop_U.dvd_of_dvd_mul_right hmul_dvd

/-! ### Part 5: Term-by-term congruence for `p ∣ j` and final assembly -/

private lemma term_div_cong_ge5 {p n k j : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hj : j ≤ n * p ^ (k - 1)) (h3j : 3 * j ≤ 2 * (n * p ^ (k - 1))) :
    let M := n * p ^ k
    let N := n * p ^ (k - 1)
    ((M.choose (p * j) * M.choose (2 * M - 3 * (p * j)) : ℕ) : ZMod (p ^ (2 * k))) =
      ((N.choose j * N.choose (2 * N - 3 * j) : ℕ) : ZMod (p ^ (2 * k))) := by
  intro M N
  have hMp : M = p * N := by
    simp only [M, N]
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hNpos : 0 < N := Nat.mul_pos hn (pow_pos hp.pos (k - 1))
  set c := 2 * N - 3 * j
  have h2M : 2 * M - 3 * (p * j) = p * c := by
    simp only [c, hMp]
    have h1 : 2 * (p * N) = p * (2 * N) := by ring
    have h2 : 3 * (p * j) = p * (3 * j) := by ring
    rw [h1, h2, ← Nat.mul_sub_left_distrib]
  rw [h2M, hMp]
  by_cases hcN : N < c
  · rw [Nat.choose_eq_zero_of_lt hcN, Nat.choose_eq_zero_of_lt (show p * N < p * c by nlinarith),
      mul_zero, mul_zero]
  push Not at hcN
  have : Fact p.Prime := ⟨hp⟩
  set m := padicValNat p N
  have hm_ge : k - 1 ≤ m :=
    (padicValNat_dvd_iff_le (by omega : N ≠ 0)).mp (dvd_mul_left (p ^ (k - 1)) n)
  have hNm : p ^ m ∣ N := pow_padicValNat_dvd
  -- Helper: for any b ≤ N, if v_p(b) < m then p^(m+v+3) | C(pN, pb) - C(N, b) (actually p^(m+2v+3)),
  -- and if v_p(b) ≥ m then p^(2k) | C(pN, pb) - C(N, b)!
  have hchoose_ge : ∀ b, b ≤ N → m ≤ padicValNat p b →
      (Nat.choose (p * N) (p * b) : ZMod (p ^ (2 * k))) = (Nat.choose N b : ZMod (p ^ (2 * k))) := by
    intro b hb hvm
    by_cases hb0 : b = 0
    · subst hb0; simp
    by_cases hbN : b = N
    · subst hbN; simp
    have hNb : p ^ m ∣ (N - b) := by
      have hbm : p ^ m ∣ b := dvd_trans (pow_dvd_pow p hvm) pow_padicValNat_dvd
      exact Nat.dvd_sub hNm hbm
    have hB : p ^ (m + 1) ∣ p * b := by
      rw [pow_succ']
      exact mul_dvd_mul_left p (dvd_trans (pow_dvd_pow p hvm) pow_padicValNat_dvd)
    have hDA : p ^ (2 * m + 2) ∣ (p * (N - b)) * (p * N) := by
      rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, pow_add]
      exact mul_dvd_mul (by rw [pow_succ']; exact mul_dvd_mul_left p hNb)
        (by rw [pow_succ']; exact mul_dvd_mul_left p hNm)
    have hjac := jacobsthal_gen (p := p) (a := N) (b := b) (t := m + 1) (e := 2 * m + 2)
      hp h5 hb (by omega) (by omega) hB hDA
    have hle : 2 * k ≤ (2 * m + 2) + (m + 1) := by omega
    have hcast := congrArg (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ (2 * k)))) hjac
    simpa only [map_natCast] using hcast
  have hchoose_lt : ∀ b, b ≤ N → padicValNat p b < m →
      ((p ^ (m + 2 * padicValNat p b + 3) : ℕ) : ℤ) ∣
        ((Nat.choose (p * N) (p * b) : ℤ) - (Nat.choose N b : ℤ)) := by
    intro b hb hvm
    set v := padicValNat p b
    by_cases hbz : b = 0
    · subst hbz; simp
    have hbv : p ^ v ∣ b := pow_padicValNat_dvd
    have hNb : p ^ v ∣ (N - b) :=
      Nat.dvd_sub (dvd_trans (pow_dvd_pow p (by omega)) hNm) hbv
    have hB : p ^ (v + 1) ∣ p * b := by rw [pow_succ']; exact mul_dvd_mul_left p hbv
    have hDA : p ^ (m + v + 2) ∣ (p * (N - b)) * (p * N) := by
      rw [show m + v + 2 = (v + 1) + (m + 1) by omega, pow_add]
      exact mul_dvd_mul (by rw [pow_succ']; exact mul_dvd_mul_left p hNb)
        (by rw [pow_succ']; exact mul_dvd_mul_left p hNm)
    have hjac := jacobsthal_gen (p := p) (a := N) (b := b) (t := v + 1) (e := m + v + 2)
      hp h5 hb (by omega) (by omega) hB hDA
    have hsum : m + v + 2 + (v + 1) = m + 2 * v + 3 := by omega
    rw [hsum] at hjac
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
      sub_eq_zero]
    exact hjac
  by_cases hj0 : j = 0
  · subst hj0
    simp only [mul_zero, Nat.choose_zero_right, one_mul, Nat.sub_zero, c]
    have h2N : 2 * N = N → False := by omega
    have hlt : N < 2 * N := by omega
    omega
  by_cases hc0 : c = 0
  · simp only [hc0, mul_zero, Nat.choose_zero_right, mul_one]
    have h3j_eq : 3 * j = 2 * N := by omega
    have h3cop : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
    have h2cop : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
    have hvj : padicValNat p j = m := by
      have h1 : padicValNat p (3 * j) = padicValNat p (2 * N) := by rw [h3j_eq]
      rw [padicValNat.mul (by decide) hj0, padicValNat.mul (by decide) (by omega),
        padicValNat.eq_zero_of_not_dvd h3cop, padicValNat.eq_zero_of_not_dvd h2cop,
        zero_add, zero_add] at h1
      exact h1
    exact hchoose_ge j hj (by omega)
  -- Now both j > 0 and c > 0!
  set vj := padicValNat p j
  set vc := padicValNat p c
  by_cases hvm : vj < m
  · -- Then vc = vj < m as well!
    have hvc : vc = vj := by
      have h3cop : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
      have h3j_v : padicValNat p (3 * j) = vj := by
        rw [padicValNat.mul (by decide) hj0, padicValNat.eq_zero_of_not_dvd h3cop, zero_add]
      have hle1 : vj ≤ vc := by
        have h1 : p ^ vj ∣ 2 * N := dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow p (by omega)) hNm) 2
        have h2 : p ^ vj ∣ 3 * j := dvd_mul_of_dvd_right pow_padicValNat_dvd 3
        exact (padicValNat_dvd_iff_le hc0).mp (Nat.dvd_sub h1 h2)
      have hle2 : vc ≤ vj := by
        by_contra hgt
        have h1 : p ^ (vj + 1) ∣ c := dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd
        have h2 : p ^ (vj + 1) ∣ 2 * N :=
          dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow p (by omega)) hNm) 2
        have h3 : p ^ (vj + 1) ∣ 3 * j := by
          have := Nat.dvd_sub h2 h1
          rwa [show 2 * N - c = 3 * j by omega] at this
        have h4 : p ^ (vj + 1) ∣ j :=
          ((hp.coprime_iff_not_dvd.mpr h3cop).pow_left (vj + 1)).dvd_of_dvd_mul_left h3
        have := (padicValNat_dvd_iff_le hj0).mp h4
        omega
      omega
    have hd_j := hchoose_lt j hj hvm
    have hd_c := hchoose_lt c hcN (by omega)
    have hdiv_jN : ((p ^ (m - vj) : ℕ) : ℤ) ∣ (Nat.choose N j : ℤ) := by
      exact_mod_cast choose_dvd_pow_of_lt_val hp hNpos (Nat.pos_of_ne_zero hj0) hNm rfl hvm
    have hdiv_cM : ((p ^ (m - vj) : ℕ) : ℤ) ∣ (Nat.choose (p * N) (p * c) : ℤ) := by
      have hpc_v : padicValNat p (p * c) = vc + 1 := by
        rw [padicValNat.mul hp.ne_zero hc0, padicValNat.self hp.one_lt]; omega
      have hMp_m : p ^ (m + 1) ∣ p * N := by rw [pow_succ']; exact mul_dvd_mul_left p hNm
      have h := choose_dvd_pow_of_lt_val hp (Nat.mul_pos hp.pos hNpos)
        (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hc0)) hMp_m hpc_v.symm (by omega)
      rw [show m + 1 - (vc + 1) = m - vj by omega] at h
      exact_mod_cast h
    have hdvd1 : ((p ^ (2 * k) : ℕ) : ℤ) ∣
        ((Nat.choose (p * N) (p * j) : ℤ) - (Nat.choose N j : ℤ)) *
          (Nat.choose (p * N) (p * c) : ℤ) := by
      have hm1 := mul_dvd_mul hd_j hdiv_cM
      rw [← Nat.cast_mul, ← pow_add] at hm1
      exact dvd_trans (by exact_mod_cast pow_dvd_pow p (show 2 * k ≤ m + 2 * vj + 3 + (m - vj) by omega)) hm1
    have hdvd2 : ((p ^ (2 * k) : ℕ) : ℤ) ∣
        (Nat.choose N j : ℤ) *
          ((Nat.choose (p * N) (p * c) : ℤ) - (Nat.choose N c : ℤ)) := by
      have hm2 := mul_dvd_mul hdiv_jN hd_c
      rw [← Nat.cast_mul, ← pow_add] at hm2
      exact dvd_trans (by exact_mod_cast pow_dvd_pow p (show 2 * k ≤ (m - vj) + (m + 2 * vc + 3) by omega)) hm2
    have htot := dvd_add hdvd1 hdvd2
    have h0 : (((Nat.choose (p * N) (p * j) * Nat.choose (p * N) (p * c) : ℕ) : ℤ) -
        ((Nat.choose N j * Nat.choose N c : ℕ) : ℤ)) =
        ((Nat.choose (p * N) (p * j) : ℤ) - (Nat.choose N j : ℤ)) *
          (Nat.choose (p * N) (p * c) : ℤ) +
        (Nat.choose N j : ℤ) *
          ((Nat.choose (p * N) (p * c) : ℤ) - (Nat.choose N c : ℤ)) := by
      push_cast; ring
    rw [← h0, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
      sub_eq_zero] at htot
    exact htot
  · -- Case m ≤ vj: then m ≤ vc as well, so both factors agree individually mod p^(2*k)!
    have hvc : m ≤ vc := by
      have h1 : p ^ m ∣ 2 * N := dvd_mul_of_dvd_right hNm 2
      have h2 : p ^ m ∣ 3 * j := dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow p (by omega)) pow_padicValNat_dvd) 3
      exact (padicValNat_dvd_iff_le hc0).mp (Nat.dvd_sub h1 h2)
    rw [Nat.cast_mul, Nat.cast_mul, hchoose_ge j hj (by omega), hchoose_ge c hcN hvc]

private lemma term_div_cong_two {n k j : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hj : j ≤ n * 2 ^ (k - 1)) (h3j : 3 * j ≤ 2 * (n * 2 ^ (k - 1))) :
    let M := n * 2 ^ k
    let N := n * 2 ^ (k - 1)
    ((M.choose (2 * j) * M.choose (2 * M - 3 * (2 * j)) : ℕ) : ZMod (2 ^ (2 * k))) =
      ((N.choose j * N.choose (2 * N - 3 * j) : ℕ) : ZMod (2 ^ (2 * k))) := by
  intro M N
  have hMp : M = 2 * N := by
    simp only [M, N]
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hNpos : 0 < N := Nat.mul_pos hn (pow_pos (by decide : 0 < 2) (k - 1))
  set c := 2 * N - 3 * j
  have h2M : 2 * M - 3 * (2 * j) = 2 * c := by
    simp only [c, hMp]
    have h1 : 2 * (2 * N) = 2 * (2 * N) := rfl
    have h2 : 3 * (2 * j) = 2 * (3 * j) := by ring
    rw [h2, ← Nat.mul_sub_left_distrib]
  rw [h2M, hMp]
  by_cases hcN : N < c
  · rw [Nat.choose_eq_zero_of_lt hcN, Nat.choose_eq_zero_of_lt (show 2 * N < 2 * c by nlinarith),
      mul_zero, mul_zero]
  push Not at hcN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set m := padicValNat 2 N
  have hm_ge : k - 1 ≤ m :=
    (padicValNat_dvd_iff_le (by omega : N ≠ 0)).mp (dvd_mul_left (2 ^ (k - 1)) n)
  have hNm : 2 ^ m ∣ N := pow_padicValNat_dvd
  -- Helper: signed congruence for C(2N, 2b) - s_b * C(N, b)!
  have hsigned : ∀ b, b ≤ N →
      let sb : ℤ := (-1 : ℤ) ^ (b * (N - b))
      let vb := padicValNat 2 b
      (m ≤ vb → ((2 ^ (2 * k) : ℕ) : ℤ) ∣ ((Nat.choose (2 * N) (2 * b) : ℤ) - sb * (Nat.choose N b : ℤ))) ∧
      (vb < m → ((2 ^ (2 * m + vb + 1) : ℕ) : ℤ) ∣ ((Nat.choose (2 * N) (2 * b) : ℤ) - sb * (Nat.choose N b : ℤ))) := by
    intro b hb sb vb
    constructor
    · intro hvm
      by_cases hb0 : b = 0
      · subst hb0; simp [sb]
      by_cases hbN : b = N
      · subst hbN; simp [sb]
      have hNb_v : 2 ^ m ∣ (N - b) :=
        Nat.dvd_sub hNm (dvd_trans (pow_dvd_pow 2 hvm) pow_padicValNat_dvd)
      -- If m = 0 (so N is odd), one of b and N - b is even!
      by_cases hm0 : m = 0
      · -- k = 1, need 2^2 | ...
        have hk1 : k = 1 := by omega
        have hN_odd : ¬ 2 ∣ N := fun hd => by
          have := (padicValNat_dvd_iff_le (by omega : N ≠ 0)).mp (show 2 ^ 1 ∣ N by simpa using hd)
          omega
        by_cases h2b : 2 ∣ b
        · have hDA : 2 ^ 2 ∣ (2 * (N - b)) * (2 * N) := by
            rw [show (2 * (N - b)) * (2 * N) = 4 * ((N - b) * N) by ring]; exact dvd_mul_right 4 _
          have h := jacobsthal_two_signed (a := N) (b := b) (t := 1) (e := 2) (d := 0)
            hb (by decide) (by decide) (by simpa using h2b) hDA (by simp)
          simpa only [hk1] using h
        · have h2Nb : 2 ∣ (N - b) := by omega
          have hDA : 2 ^ 3 ∣ (2 * (N - b)) * (2 * N) := by
            rcases h2Nb with ⟨q, hq⟩
            exact ⟨q * N, by rw [hq]; ring⟩
          have h := jacobsthal_two_signed (a := N) (b := b) (t := 0) (e := 3) (d := 0)
            hb (by decide) (by decide) (by simp) hDA (by simp)
          simpa only [hk1] using h
      · have hDA : 2 ^ (2 * m + 2) ∣ (2 * (N - b)) * (2 * N) := by
          rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, pow_add]
          exact mul_dvd_mul (by rw [pow_succ']; exact mul_dvd_mul_left 2 hNb_v)
            (by rw [pow_succ']; exact mul_dvd_mul_left 2 hNm)
        have hB : 2 ^ m ∣ b := dvd_trans (pow_dvd_pow 2 hvm) pow_padicValNat_dvd
        have h := jacobsthal_two_signed (a := N) (b := b) (t := m) (e := 2 * m + 2) (d := 0)
          hb (by omega) (by omega) hB hDA (by simp)
        exact dvd_trans (by exact_mod_cast pow_dvd_pow 2 (show 2 * k ≤ 0 + (2 * m + 2) + m - 1 by omega)) h
    · intro hvm
      by_cases hb0 : b = 0
      · subst hb0; simp [sb]
      have hbv : 2 ^ vb ∣ b := pow_padicValNat_dvd
      have hNb : 2 ^ vb ∣ (N - b) :=
        Nat.dvd_sub (dvd_trans (pow_dvd_pow 2 (by omega)) hNm) hbv
      have hDA : 2 ^ (m + vb + 2) ∣ (2 * (N - b)) * (2 * N) := by
        rw [show m + vb + 2 = (vb + 1) + (m + 1) by omega, pow_add]
        exact mul_dvd_mul (by rw [pow_succ']; exact mul_dvd_mul_left 2 hNb)
          (by rw [pow_succ']; exact mul_dvd_mul_left 2 hNm)
      have hd : 2 ^ (m - vb) ∣ Nat.choose N b :=
        choose_dvd_pow_of_lt_val Nat.prime_two hNpos (Nat.pos_of_ne_zero hb0) hNm rfl hvm
      have h := jacobsthal_two_signed (a := N) (b := b) (t := vb) (e := m + vb + 2) (d := m - vb)
        hb (by omega) (by omega) hbv hDA hd
      rwa [show m - vb + (m + vb + 2) + vb - 1 = 2 * m + vb + 1 by omega] at h
  -- Check signs sj * sc = 1!
  set sj : ℤ := (-1 : ℤ) ^ (j * (N - j))
  set sc : ℤ := (-1 : ℤ) ^ (c * (N - c))
  have hs_prod : sj * sc = 1 := by
    simp only [sj, sc, ← pow_add]
    have heven : 2 ∣ (j * (N - j) + c * (N - c)) := by
      have hc_par : c % 2 = j % 2 := by omega
      have hNc_par : (N - c) % 2 = (N - j) % 2 := by omega
      have h1 : (c * (N - c)) % 2 = (j * (N - j)) % 2 := by
        rw [Nat.mul_mod, hc_par, hNc_par, ← Nat.mul_mod]
      omega
    rcases heven with ⟨q, hq⟩
    rw [hq, pow_mul]; norm_num
  by_cases hj0 : j = 0
  · subst hj0; omega
  by_cases hc0 : c = 0
  · simp only [hc0, mul_zero, Nat.choose_zero_right, mul_one]
    have h3j_eq : 3 * j = 2 * N := by omega
    have h2j_v : padicValNat 2 j = m + 1 := by
      have h1 : padicValNat 2 (3 * j) = padicValNat 2 (2 * N) := by rw [h3j_eq]
      rw [padicValNat.mul (by decide) hj0, padicValNat.mul (by decide) (by omega),
        padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3), padicValNat.self (by decide),
        zero_add] at h1
      omega
    have hsj_eq : sj = 1 := by
      have h2j : 2 ∣ j := by
        have := pow_padicValNat_dvd (p := 2) (n := j)
        rw [h2j_v] at this
        exact dvd_trans (dvd_pow_self 2 (by omega)) this
      rcases h2j with ⟨q, hq⟩
      dsimp only [sj]; rw [hq, mul_assoc, pow_mul]; norm_num
    have hdj := (hsigned j hj).1 (by omega)
    dsimp only [sj] at hsj_eq
    rw [hsj_eq, one_mul, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, sub_eq_zero] at hdj
    exact hdj
  set vj := padicValNat 2 j
  set vc := padicValNat 2 c
  by_cases hvm : vj < m
  · have hvc : vc = vj := by
      have h3nd : ¬ 2 ∣ 3 := by decide
      have hle1 : vj ≤ vc := by
        have h1 : 2 ^ vj ∣ 2 * N := dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow 2 (by omega)) hNm) 2
        have h2 : 2 ^ vj ∣ 3 * j := dvd_mul_of_dvd_right pow_padicValNat_dvd 3
        exact (padicValNat_dvd_iff_le hc0).mp (Nat.dvd_sub h1 h2)
      have hle2 : vc ≤ vj := by
        by_contra hgt
        have h1 : 2 ^ (vj + 1) ∣ c := dvd_trans (pow_dvd_pow 2 (by omega)) pow_padicValNat_dvd
        have h2 : 2 ^ (vj + 1) ∣ 2 * N :=
          dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow 2 (by omega)) hNm) 2
        have h3 : 2 ^ (vj + 1) ∣ 3 * j := by
          have := Nat.dvd_sub h2 h1
          rwa [show 2 * N - c = 3 * j by omega] at this
        have h4 : 2 ^ (vj + 1) ∣ j :=
          ((Nat.prime_two.coprime_iff_not_dvd.mpr h3nd).pow_left (vj + 1)).dvd_of_dvd_mul_left h3
        have := (padicValNat_dvd_iff_le hj0).mp h4
        omega
      omega
    have hdj := (hsigned j hj).2 hvm
    have hdc := (hsigned c hcN).2 (by omega)
    have hdiv_jN : ((2 ^ (m - vj) : ℕ) : ℤ) ∣ (Nat.choose N j : ℤ) := by
      exact_mod_cast choose_dvd_pow_of_lt_val Nat.prime_two hNpos (Nat.pos_of_ne_zero hj0) hNm rfl hvm
    have hdiv_cM : ((2 ^ (m - vj) : ℕ) : ℤ) ∣ (Nat.choose (2 * N) (2 * c) : ℤ) := by
      have h2c_v : padicValNat 2 (2 * c) = vc + 1 := by
        rw [padicValNat.mul (by decide) hc0, padicValNat.self (by decide)]; omega
      have h2N_m : 2 ^ (m + 1) ∣ 2 * N := by rw [pow_succ']; exact mul_dvd_mul_left 2 hNm
      have h := choose_dvd_pow_of_lt_val Nat.prime_two (Nat.mul_pos (by decide) hNpos)
        (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hc0)) h2N_m h2c_v.symm (by omega)
      rw [show m + 1 - (vc + 1) = m - vj by omega] at h
      exact_mod_cast h
    have hdvd1 : ((2 ^ (2 * k) : ℕ) : ℤ) ∣
        ((Nat.choose (2 * N) (2 * j) : ℤ) - sj * (Nat.choose N j : ℤ)) *
          (Nat.choose (2 * N) (2 * c) : ℤ) := by
      have hm1 := mul_dvd_mul hdj hdiv_cM
      rw [← Nat.cast_mul, ← pow_add] at hm1
      exact dvd_trans (by exact_mod_cast pow_dvd_pow 2 (show 2 * k ≤ 2 * m + vj + 1 + (m - vj) by omega)) hm1
    have hdvd2 : ((2 ^ (2 * k) : ℕ) : ℤ) ∣
        (sj * (Nat.choose N j : ℤ)) *
          ((Nat.choose (2 * N) (2 * c) : ℤ) - sc * (Nat.choose N c : ℤ)) := by
      have hm2 := mul_dvd_mul (dvd_mul_of_dvd_right hdiv_jN sj) hdc
      rw [← Nat.cast_mul, ← pow_add] at hm2
      exact dvd_trans (by exact_mod_cast pow_dvd_pow 2 (show 2 * k ≤ (m - vj) + (2 * m + vc + 1) by omega)) hm2
    have htot := dvd_add hdvd1 hdvd2
    have h0 : (((Nat.choose (2 * N) (2 * j) * Nat.choose (2 * N) (2 * c) : ℕ) : ℤ) -
        ((Nat.choose N j * Nat.choose N c : ℕ) : ℤ)) =
        ((Nat.choose (2 * N) (2 * j) : ℤ) - sj * (Nat.choose N j : ℤ)) *
          (Nat.choose (2 * N) (2 * c) : ℤ) +
        (sj * (Nat.choose N j : ℤ)) *
          ((Nat.choose (2 * N) (2 * c) : ℤ) - sc * (Nat.choose N c : ℤ)) := by
      push_cast
      linear_combination (Nat.choose N j : ℤ) * (Nat.choose N c : ℤ) * hs_prod
    rw [← h0, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
      sub_eq_zero] at htot
    exact htot
  · have hvc : m ≤ vc := by
      have h1 : 2 ^ m ∣ 2 * N := dvd_mul_of_dvd_right hNm 2
      have h2 : 2 ^ m ∣ 3 * j := dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow 2 (by omega)) pow_padicValNat_dvd) 3
      exact (padicValNat_dvd_iff_le hc0).mp (Nat.dvd_sub h1 h2)
    have hdj := (hsigned j hj).1 (by omega)
    have hdc := (hsigned c hcN).1 hvc
    have h1 : ((Nat.choose (2 * N) (2 * j) : ℤ) : ZMod (2 ^ (2 * k))) =
        (sj : ZMod (2 ^ (2 * k))) * (Nat.choose N j : ZMod (2 ^ (2 * k))) := by
      rw [← sub_eq_zero]
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdj
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using this
    have h2 : ((Nat.choose (2 * N) (2 * c) : ℤ) : ZMod (2 ^ (2 * k))) =
        (sc : ZMod (2 ^ (2 * k))) * (Nat.choose N c : ZMod (2 ^ (2 * k))) := by
      rw [← sub_eq_zero]
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdc
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using this
    rw [Nat.cast_mul, Nat.cast_mul]
    have h1' : (Nat.choose (2 * N) (2 * j) : ZMod (2 ^ (2 * k))) =
        (sj : ZMod (2 ^ (2 * k))) * (Nat.choose N j : ZMod (2 ^ (2 * k))) := by
      simpa only [Int.cast_natCast] using h1
    have h2' : (Nat.choose (2 * N) (2 * c) : ZMod (2 ^ (2 * k))) =
        (sc : ZMod (2 ^ (2 * k))) * (Nat.choose N c : ZMod (2 ^ (2 * k))) := by
      simpa only [Int.cast_natCast] using h2
    rw [h1', h2']
    have hs_z : (sj : ZMod (2 ^ (2 * k))) * (sc : ZMod (2 ^ (2 * k))) = 1 := by
      rw [← Int.cast_mul, hs_prod, Int.cast_one]
    calc (sj : ZMod (2 ^ (2 * k))) * (Nat.choose N j : ZMod (2 ^ (2 * k))) *
            ((sc : ZMod (2 ^ (2 * k))) * (Nat.choose N c : ZMod (2 ^ (2 * k))))
        = ((sj : ZMod (2 ^ (2 * k))) * (sc : ZMod (2 ^ (2 * k)))) *
            ((Nat.choose N j : ZMod (2 ^ (2 * k))) * (Nat.choose N c : ZMod (2 ^ (2 * k)))) := by ring
      _ = (Nat.choose N j : ZMod (2 ^ (2 * k))) * (Nat.choose N c : ZMod (2 ^ (2 * k))) := by
          rw [hs_z, one_mul]

private lemma a_cong {p n k : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hn : 0 < n) (hk : 0 < k) :
    (a (n * p ^ k) : ZMod (p ^ (2 * k))) = (a (n * p ^ (k - 1)) : ZMod (p ^ (2 * k))) := by
  set M := n * p ^ k
  set N := n * p ^ (k - 1)
  have hMp : M = p * N := by
    simp only [M, N]
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hMpos : 0 < M := Nat.mul_pos hn (pow_pos hp.pos k)
  rw [a_eq_sum_choose M, a_eq_sum_choose N]
  simp only [Nat.cast_sum]
  set SM := (Finset.range (M + 1)).filter (fun j => 3 * j ≤ 2 * M)
  set SN := (Finset.range (N + 1)).filter (fun j => 3 * j ≤ 2 * N)
  have hsplit : SM = SN.image (fun j => p * j) ∪ SM.filter (fun j => ¬ p ∣ j) := by
    ext x
    simp only [SM, SN, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hxM, hx3⟩
      by_cases hd : p ∣ x
      · left
        rcases hd with ⟨j, rfl⟩
        refine ⟨j, ⟨?_, ?_⟩, rfl⟩
        · have : p * j ≤ p * N := by omega
          exact Nat.lt_succ_of_le (Nat.le_of_mul_le_mul_left this hp.pos)
        · have : p * (3 * j) ≤ p * (2 * N) := by linarith
          exact Nat.le_of_mul_le_mul_left this hp.pos
      · exact Or.inr ⟨⟨hxM, hx3⟩, hd⟩
    · rintro (⟨j, ⟨hjN, hj3⟩, rfl⟩ | ⟨⟨hxM, hx3⟩, _⟩)
      · refine ⟨?_, ?_⟩
        · have : p * j ≤ p * N := Nat.mul_le_mul_left p (Nat.lt_succ_iff.mp hjN)
          omega
        · nlinarith
      · exact ⟨hxM, hx3⟩
  have hdisj : Disjoint (SN.image (fun j => p * j)) (SM.filter (fun j => ¬ p ∣ j)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_image, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨j, _, rfl⟩
    exact h2.2 (dvd_mul_right p j)
  rw [hsplit, Finset.sum_union hdisj,
    Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
  have hndiv : ∑ j ∈ SM.filter (fun j => ¬ p ∣ j),
      ((M.choose j * M.choose (2 * M - 3 * j) : ℕ) : ZMod (p ^ (2 * k))) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    simp only [SM, Finset.mem_filter, Finset.mem_range] at hj
    rw [ZMod.natCast_eq_zero_iff]
    have hMk : p ^ k ∣ M := dvd_mul_left (p ^ k) n
    have hd1 : p ^ k ∣ M.choose j := choose_dvd_of_not_dvd hp hMpos hMk hj.2
    have hnd2 : ¬ p ∣ (2 * M - 3 * j) := by
      intro hd
      have h2M : p ∣ 2 * M := dvd_mul_of_dvd_right (dvd_trans (dvd_pow_self p (by omega)) hMk) 2
      have h3j : p ∣ 3 * j := by
        have := Nat.dvd_sub h2M hd
        rwa [show 2 * M - (2 * M - 3 * j) = 3 * j by omega] at this
      rcases hp.dvd_mul.mp h3j with h3 | hj'
      · have h3le := Nat.le_of_dvd (by decide) h3
        have hp2 := hp.two_le
        have hp_eq2 : p = 2 := by omega
        subst hp_eq2; exact absurd h3 (by decide)
      · exact hj.2 hj'
    have hd2 : p ^ k ∣ M.choose (2 * M - 3 * j) := choose_dvd_of_not_dvd hp hMpos hMk hnd2
    rw [show 2 * k = k + k by omega, pow_add]
    exact mul_dvd_mul hd1 hd2
  rw [hndiv, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [SN, Finset.mem_filter, Finset.mem_range] at hj
  have hjle : j ≤ N := Nat.lt_succ_iff.mp hj.1
  by_cases hp2 : p = 2
  · subst hp2
    exact term_div_cong_two hn hk hjle hj.2
  · have h5 : 5 ≤ p := by
      have := hp.two_le
      have hp4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
      omega
    exact term_div_cong_ge5 hp h5 hn hk hjle hj.2

end OMA_A092765

theorem OMA.solution : type_of% @OMA.S_oeis_a092765.main := by
  intro p n k hp hp3 hn hk
  rw [← ZMod.natCast_eq_natCast_iff]
  exact OMA_A092765.a_cong hp hp3 hn hk
