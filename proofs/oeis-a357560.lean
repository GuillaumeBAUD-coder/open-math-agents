import OMAStatements.S_oeis_a357560
import Mathlib

/-!
# OEIS A357560: `a(p-1) == 0 (mod p^4)` for every prime `p >= 7` (conjecture of Peter Bala, 2022)

`a(n)` is the numerator of `s(n) = Sum_{k=1..n} (-1)^(n+k) * (1/k) * C(n,k) * C(n+k,k)^2`.

Proof. Put `n = p - 1` and work in `R = ZMod (p^2)`, with `H(m) = Sum_{i=1..m} 1/i` in `R`.

1. For `1 <= k < p`: `C(p-1+k,k) = p * e_k` with `e_k * k = C(p+k-1,k-1)` (naturals), and
   `C(p+m,m) = 1 + p * H(m)` in `R` for `m < p`, so `e_k * k = 1 + p * H(k-1)`.
2. `(-1)^k * C(p-1,k) = 1 - p * H(k)` in `R` for `k < p`.
3. Hence `(1/k) * (-1)^(p-1+k) * C(p-1,k) * e_k^2 = 1/k^3 - p/k^4 + p * H(k-1)/k^3` in `R`.
4. `1/k^3 + 1/(p-k)^3 = -3*p/k^4` in `R`, so `2 * Sum 1/k^3 = -3 * p * Sum 1/k^4`.
5. In `ZMod p`: `Sum_{k=1..p-1} 1/k^j = 0` for `0 < j < p - 1` (used for `j = 1` and `j = 4`, which
   needs `p >= 7`). Hence `p * Sum 1/k^4 = 0` and `Sum 1/k^3 = 0` in `R`.
6. In `ZMod p`, with `G(m) = Sum_{i=1..m} 1/i`: `G(p-1) = 0`, so `G(p-1-m) = G(m)`. The reflection
   `k -> p-k` turns `A = Sum 1/k^3 * G(k-1)` into `-Sum 1/k^3 * G(k) = -A - Sum 1/k^4 = -A`, so
   `A = 0`, and `p * Sum H(k-1)/k^3 = 0` in `R`.
7. So the sum over `k` of the terms in 3 vanishes in `R`. With `D = (p-1)!` and `c_k = D / k` (an
   integer), `s(p-1) * D = p^2 * Sum c_k * (-1)^(p-1+k) * C(p-1,k) * e_k^2 = p^4 * N` for an
   integer `N`.
8. `num(s) * D = p^4 * N * den(s)` and `p` does not divide `D`, so `p^4` divides the numerator.
-/

private lemma p_sq_zero (p : ℕ) : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma coprime_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    Nat.Coprime k (p ^ 2) :=
  ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)).symm).pow_right 2

private lemma mul_inv_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one k (coprime_p2 hp hk0 hkp)

/-- `harmR p m = Sum_{i=1..m} 1/i` in `ZMod (p^2)`. -/
private def harmR (p m : ℕ) : ZMod (p ^ 2) := ∑ i ∈ Finset.Icc 1 m, (i : ZMod (p ^ 2))⁻¹

private lemma harmR_zero (p : ℕ) : harmR p 0 = 0 := by
  unfold harmR
  rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by omega), Finset.sum_empty]

private lemma harmR_succ (p m : ℕ) :
    harmR p (m + 1) = harmR p m + ((m + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
  unfold harmR
  exact Finset.sum_Icc_succ_top (by omega) _

/-- `harmF p m = Sum_{i=1..m} 1/i` in `ZMod p`. -/
private def harmF (p m : ℕ) : ZMod p := ∑ i ∈ Finset.Icc 1 m, (i : ZMod p)⁻¹

private lemma harmF_zero (p : ℕ) : harmF p 0 = 0 := by
  unfold harmF
  rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by omega), Finset.sum_empty]

private lemma harmF_succ (p m : ℕ) :
    harmF p (m + 1) = harmF p m + ((m + 1 : ℕ) : ZMod p)⁻¹ := by
  unfold harmF
  exact Finset.sum_Icc_succ_top (by omega) _

/-- Ring step for `C(p+m,m)`: from `(y + x) * (1 + y*w) = X * x`, `x * u = 1`, `y^2 = 0`. -/
private lemma ring_step_add {R : Type*} [CommRing R] (X x u y w : R) (hinv : x * u = 1)
    (h0 : y ^ 2 = 0) (hc : (y + x) * (1 + y * w) = X * x) : X = 1 + y * (w + u) := by
  linear_combination (-X + 1 + y * w) * hinv - u * hc + (w * u) * h0

/-- Ring step for `(-1)^k * C(p-1,k)`. -/
private lemma ring_step_sub {R : Type*} [CommRing R] (X X' s x u y w : R) (hinv : x * u = 1)
    (h0 : y ^ 2 = 0) (hc : X' * x = X * (y - x)) (ih : s * X = 1 - y * w) :
    s * (-1) * X' = 1 - y * (w + u) := by
  linear_combination (-(s * u)) * hc + (s * X' + 1 - y * w) * hinv - (u * (y - x)) * ih +
    (u * w) * h0

/-- `C(p+m, m) = 1 + p * H(m)` modulo `p^2`, for `m < p`. -/
private lemma choose_add_zmod {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m < p) :
    (((p + m).choose m : ℕ) : ZMod (p ^ 2)) = 1 + (p : ZMod (p ^ 2)) * harmR p m := by
  induction m with
  | zero =>
    rw [harmR_zero]
    simp
  | succ m ih =>
    have ih' := ih (by omega)
    have hN : (p + (m + 1)) * (p + m).choose m = (p + (m + 1)).choose (m + 1) * (m + 1) :=
      Nat.add_one_mul_choose_eq (p + m) m
    have hc := congrArg (Nat.cast (R := ZMod (p ^ 2))) hN
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add p (m + 1), ih'] at hc
    have hinv := mul_inv_p2 hp (k := m + 1) (by omega) hm
    rw [harmR_succ]
    exact ring_step_add _ _ _ _ _ hinv (p_sq_zero p) hc

/-- `(-1)^k * C(p-1, k) = 1 - p * H(k)` modulo `p^2`, for `k < p`. -/
private lemma neg_one_pow_mul_choose_zmod {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (-1 : ZMod (p ^ 2)) ^ k * (((p - 1).choose k : ℕ) : ZMod (p ^ 2)) =
      1 - (p : ZMod (p ^ 2)) * harmR p k := by
  induction k with
  | zero =>
    rw [harmR_zero]
    simp
  | succ k ih =>
    have ih' := ih (by omega)
    have hN : (p - 1).choose (k + 1) * (k + 1) = (p - 1).choose k * (p - 1 - k) :=
      Nat.choose_succ_right_eq (p - 1) k
    have hc := congrArg (Nat.cast (R := ZMod (p ^ 2))) hN
    have hsub : ((p - 1 - k : ℕ) : ZMod (p ^ 2)) =
        (p : ZMod (p ^ 2)) - ((k + 1 : ℕ) : ZMod (p ^ 2)) := by
      have h : p - 1 - k = p - (k + 1) := by omega
      rw [h, Nat.cast_sub (show k + 1 ≤ p by omega)]
    rw [Nat.cast_mul, Nat.cast_mul, hsub] at hc
    have hinv := mul_inv_p2 hp (k := k + 1) (by omega) hk
    rw [harmR_succ, pow_succ (-1 : ZMod (p ^ 2)) k]
    exact ring_step_sub _ _ _ _ _ _ _ hinv (p_sq_zero p) hc ih'

/-- `C(p+m, m+1) = p * e` with `e * (m+1) = C(p+m, m)`, for `m + 1 < p`. -/
private lemma choose_eq_p_mul {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m + 1 < p) :
    ∃ e : ℕ, (p + m).choose (m + 1) = p * e ∧ e * (m + 1) = (p + m).choose m := by
  have hN : (p + m).choose (m + 1) * (m + 1) = (p + m).choose m * (p + m - m) :=
    Nat.choose_succ_right_eq (p + m) m
  rw [Nat.add_sub_cancel] at hN
  have hcop : Nat.Coprime p (m + 1) :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hm)
  have hdvd : p ∣ (p + m).choose (m + 1) :=
    hcop.dvd_of_dvd_mul_right ⟨(p + m).choose m, by rw [hN, mul_comm]⟩
  obtain ⟨e, he⟩ := hdvd
  refine ⟨e, he, ?_⟩
  rw [he] at hN
  have h : p * (e * (m + 1)) = p * (p + m).choose m := by
    rw [← mul_assoc, hN, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hp.pos h

/-- Ring identity for one term: with `x * u = 1`, `y^2 = 0`, `c = 1 - y * (w + u)` and
`e * x = 1 + y * w`: `u * c * e^2 = u^3 - y * u^4 + y * (u^3 * w)`. -/
private lemma ring_term {R : Type*} [CommRing R] (x y u w c e : R) (h1 : x * u = 1)
    (h0 : y ^ 2 = 0) (hc : c = 1 - y * (w + u)) (he : e * x = 1 + y * w) :
    u * c * e ^ 2 = u ^ 3 - y * u ^ 4 + y * (u ^ 3 * w) := by
  have he' : e = u * (1 + y * w) := by
    linear_combination u * he - e * h1
  rw [hc, he']
  linear_combination (u ^ 3 * (-(w ^ 2) - 2 * u * w - y * w ^ 3 - y * u * w ^ 2)) * h0

/-- Ring identity: `c = D * u` when `x * u = 1` and `x * c = D`, applied inside a product. -/
private lemma ring_scale {R : Type*} [CommRing R] (x u cc D a b : R) (h1 : x * u = 1)
    (h2 : x * cc = D) : cc * a * b = D * (u * a * b) := by
  linear_combination (-(cc * a * b)) * h1 + (u * a * b) * h2

/-- A sum over `k = 1..p-1` of a function of the residue of `k` is the sum over the whole field,
when the function vanishes at `0`. -/
private lemma sum_Icc_eq_sum_univ {p : ℕ} [Fact p.Prime] (f : ZMod p → ZMod p) (hf : f 0 = 0) :
    ∑ k ∈ Finset.Icc 1 (p - 1), f (k : ZMod p) = ∑ x : ZMod p, f x := by
  symm
  rw [← Finset.sum_erase Finset.univ hf]
  refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
    have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h => hx ((ZMod.val_eq_zero x).mp h)
    have hlt : x.val < p := x.val_lt
    exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩
  · intro x _ y _ h
    exact ZMod.val_injective p h
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_Icc] at hk
    refine ⟨(k : ZMod p), ?_, ZMod.val_natCast_of_lt (by omega)⟩
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
    intro h0
    exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
  · intro x _
    rw [ZMod.natCast_zmod_val]

/-- `Sum_{k=1..p-1} k^(-j) = 0` in `ZMod p` for `0 < j < p - 1`. -/
private lemma sum_inv_pow_zmod_p {p : ℕ} (hp : p.Prime) (j : ℕ) (hj0 : 0 < j) (hj : j < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ j = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : (fun x : ZMod p => (x⁻¹) ^ j) 0 = 0 := by
    show ((0 : ZMod p)⁻¹) ^ j = 0
    rw [inv_zero, zero_pow hj0.ne']
  refine (sum_Icc_eq_sum_univ (fun x : ZMod p => (x⁻¹) ^ j) hf).trans ?_
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ j = ∑ x : ZMod p, x ^ j :=
    Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ j)
  rw [hinv]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) j (by rw [ZMod.card]; exact hj)

/-- An element of `ZMod (p^2)` that reduces to `0` modulo `p` is killed by `p`. -/
private lemma p_mul_eq_zero_of_castHom {p : ℕ} (hp : p.Prime) (w : ZMod (p ^ 2))
    (h : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) w = 0) :
    (p : ZMod (p ^ 2)) * w = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  have hval : p ∣ w.val := (ZMod.natCast_eq_zero_iff _ _).mp h
  rw [← ZMod.natCast_zmod_val w, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  exact dvd_trans (dvd_of_eq (sq p)) (mul_dvd_mul_left p hval)

/-- Reduction modulo `p` sends `1/k` in `ZMod (p^2)` to `1/k` in `ZMod p`, for `0 < k < p`. -/
private lemma castHom_inv {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) ((k : ZMod (p ^ 2))⁻¹) =
      (k : ZMod p)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hm := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) (mul_inv_p2 hp hk0 hkp)
  simp only [map_mul, map_one, map_natCast] at hm
  have hkne : (k : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt hk0 hkp ((ZMod.natCast_eq_zero_iff k p).mp h)
  exact mul_left_cancel₀ hkne (by rw [hm, mul_inv_cancel₀ hkne])

private lemma castHom_harmR {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m < p) :
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (harmR p m) = harmF p m := by
  unfold harmR harmF
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Icc] at hi
  exact castHom_inv hp (by omega) (by omega)

/-- `p * Sum_{k=1..p-1} k^(-4) = 0` in `ZMod (p^2)` for a prime `p >= 7`. -/
private lemma p_mul_sum_inv_pow4 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4 = 0 := by
  apply p_mul_eq_zero_of_castHom hp
  rw [map_sum]
  refine Eq.trans ?_ (sum_inv_pow_zmod_p hp 4 (by omega) (by omega))
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rw [map_pow, castHom_inv hp (k := k) (by omega) (by omega)]

/-- The reflection `k -> p - k` of a sum over `k = 1..p-1`. -/
private lemma sum_reflect {M : Type*} [AddCommMonoid M] (p : ℕ) (F : ℕ → M) :
    ∑ k ∈ Finset.Icc 1 (p - 1), F k = ∑ k ∈ Finset.Icc 1 (p - 1), F (p - k) := by
  refine Finset.sum_nbij (fun k => p - k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro x hx y hy h
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
    dsimp only at h
    omega
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_Icc] at hk
    exact ⟨p - k, by simp only [Finset.mem_coe, Finset.mem_Icc]; omega, by dsimp only; omega⟩
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [Nat.sub_sub_self (by omega)]

/-- Ring identity behind the reflection `k -> p - k`: if `x * u = 1`, `(y - x) * v = 1` and
`y^2 = 0`, then `u^3 + v^3 = -3 * y * u^4`. -/
private lemma ring_reflect {R : Type*} [CommRing R] (x y u v : R) (h1 : x * u = 1)
    (h2 : (y - x) * v = 1) (h0 : y ^ 2 = 0) : u ^ 3 + v ^ 3 = -(3 * (y * u ^ 4)) := by
  have hv : v = -u - y * u ^ 2 := by
    linear_combination (-v * (1 + y * u)) * h1 + (v * u ^ 2) * h0 + (-u - y * u ^ 2) * h2
  rw [hv]
  linear_combination (-(3 * u ^ 5 + y * u ^ 6)) * h0

/-- `1/k^3 + 1/(p-k)^3 = -3*p/k^4` in `ZMod (p^2)`. -/
private lemma inv_cube_add_reflect {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ((k : ZMod (p ^ 2))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 =
      -(3 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
  have h1 := mul_inv_p2 hp hk0 hkp
  have h2 := mul_inv_p2 hp (k := p - k) (by omega) (by omega)
  have hcast : ((p - k : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
    Nat.cast_sub (by omega)
  rw [hcast] at h2 ⊢
  exact ring_reflect _ _ _ _ h1 h2 (p_sq_zero p)

/-- `2 * Sum_{k=1..p-1} 1/k^3 = -3 * p * Sum_{k=1..p-1} 1/k^4` in `ZMod (p^2)`. -/
private lemma two_mul_sum_inv_cube {p : ℕ} (hp : p.Prime) :
    2 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 =
      -(3 * ((p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
  have hrefl : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 =
      ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 :=
    sum_reflect p (fun k => ((k : ZMod (p ^ 2))⁻¹) ^ 3)
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      ((k : ZMod (p ^ 2))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 =
        -(3 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact inv_cube_add_reflect hp (by omega) (by omega)
  calc 2 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3
      = ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 +
          ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 := by
        rw [← hrefl, two_mul]
    _ = ∑ k ∈ Finset.Icc 1 (p - 1),
          (((k : ZMod (p ^ 2))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3) :=
        Finset.sum_add_distrib.symm
    _ = ∑ k ∈ Finset.Icc 1 (p - 1),
          -(3 * ((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4)) :=
        Finset.sum_congr rfl hterm
    _ = -(3 * ((p : ZMod (p ^ 2)) *
          ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4)) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum]

/-- `1/(p-k) = -1/k` in `ZMod p`. -/
private lemma inv_sub_zmod_p {p k : ℕ} [Fact p.Prime] (hk : k ≤ p) :
    (((p - k : ℕ) : ZMod p))⁻¹ = -((k : ZMod p))⁻¹ := by
  rw [Nat.cast_sub hk, ZMod.natCast_self, zero_sub, inv_neg]

/-- If `G(p-1) = 0` then `G(p-1-m) = G(m)` for `m <= p - 1`, where `G = harmF p`. -/
private lemma harmF_reflect {p : ℕ} [Fact p.Prime] (hH1 : harmF p (p - 1) = 0) (m : ℕ)
    (hm : m ≤ p - 1) : harmF p (p - 1 - m) = harmF p m := by
  induction m with
  | zero => rw [Nat.sub_zero, hH1, harmF_zero]
  | succ m ih =>
    have ih' := ih (by omega)
    obtain ⟨j, hj⟩ : ∃ j, p - 1 - m = j + 1 := ⟨p - 1 - (m + 1), by omega⟩
    have hj2 : p - 1 - (m + 1) = j := by omega
    have hj3 : j + 1 = p - (m + 1) := by omega
    rw [hj, harmF_succ, hj3, inv_sub_zmod_p (p := p) (k := m + 1) (by omega)] at ih'
    rw [hj2, harmF_succ]
    linear_combination ih'

/-- `Sum_{k=1..p-1} k^(-3) * G(k-1) = 0` in `ZMod p` for a prime `p >= 7`. -/
private lemma sum_inv_cube_mul_harm {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3 * harmF p (k - 1) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hH1 : harmF p (p - 1) = 0 := by
    have h := sum_inv_pow_zmod_p hp 1 (by omega) (by omega)
    simp only [pow_one] at h
    unfold harmF
    exact h
  have hH4 := sum_inv_pow_zmod_p hp 4 (by omega) (by omega)
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (((p - k : ℕ) : ZMod p)⁻¹) ^ 3 * harmF p (p - k - 1) =
        -(((k : ZMod p)⁻¹) ^ 3 * harmF p (k - 1)) - ((k : ZMod p)⁻¹) ^ 4 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h1 : harmF p (p - k - 1) = harmF p k := by
      have h : p - k - 1 = p - 1 - k := by omega
      rw [h]
      exact harmF_reflect hH1 k hk.2
    have h2 : harmF p k = harmF p (k - 1) + ((k : ZMod p))⁻¹ := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [harmF_succ, Nat.add_sub_cancel]
    rw [inv_sub_zmod_p (p := p) (k := k) (by omega), h1, h2]
    ring
  have hsum : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3 * harmF p (k - 1) =
      ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod p)⁻¹) ^ 3 * harmF p (p - k - 1) :=
    sum_reflect p (fun k => ((k : ZMod p)⁻¹) ^ 3 * harmF p (k - 1))
  have hsum2 : ∑ k ∈ Finset.Icc 1 (p - 1),
      (((p - k : ℕ) : ZMod p)⁻¹) ^ 3 * harmF p (p - k - 1) =
        -∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3 * harmF p (k - 1) -
          ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hle := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h')
    omega
  have h2A : 2 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3 * harmF p (k - 1) = 0 := by
    linear_combination hsum + hsum2 - hH4
  exact (mul_eq_zero.mp h2A).resolve_left h2ne

/-- `p * Sum_{k=1..p-1} k^(-3) * H(k-1) = 0` in `ZMod (p^2)` for a prime `p >= 7`. -/
private lemma p_mul_sum_inv_cube_mul_harm {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 2)) *
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 * harmR p (k - 1) = 0 := by
  apply p_mul_eq_zero_of_castHom hp
  rw [map_sum]
  refine Eq.trans ?_ (sum_inv_cube_mul_harm hp hp7)
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rw [map_mul, map_pow, castHom_inv hp (k := k) (by omega) (by omega),
    castHom_harmR hp (k - 1) (by omega)]

/-- The sum of `1/k^3 - p/k^4 + p * H(k-1)/k^3` over `k = 1..p-1` vanishes in `ZMod (p^2)`. -/
private lemma sum_zmod_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1),
      (((k : ZMod (p ^ 2))⁻¹) ^ 3 - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4 +
        (p : ZMod (p ^ 2)) * (((k : ZMod (p ^ 2))⁻¹) ^ 3 * harmR p (k - 1))) = 0 := by
  have hsplit : ∑ k ∈ Finset.Icc 1 (p - 1),
      (((k : ZMod (p ^ 2))⁻¹) ^ 3 - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4 +
        (p : ZMod (p ^ 2)) * (((k : ZMod (p ^ 2))⁻¹) ^ 3 * harmR p (k - 1))) =
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 -
        (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4 +
        (p : ZMod (p ^ 2)) *
          ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3 * harmR p (k - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  have hW := two_mul_sum_inv_cube hp
  have hF := p_mul_sum_inv_pow4 hp hp7
  have hG := p_mul_sum_inv_cube_mul_harm hp hp7
  have h2u : IsUnit (2 : ZMod (p ^ 2)) := by
    have h := (ZMod.isUnit_iff_coprime 2 (p ^ 2)).mpr (coprime_p2 hp (by norm_num) (by omega))
    exact_mod_cast h
  apply h2u.mul_left_cancel
  rw [mul_zero]
  linear_combination hW - 5 * hF + 2 * hG

/-- If `q * D = p^4 * N` with `D` prime to `p`, then `p^4` divides the numerator of `q`. -/
private lemma num_dvd_aux {p : ℕ} (q : ℚ) (D : ℕ) (N : ℤ) (hD : Nat.Coprime p D)
    (hq : q * (D : ℚ) = (p : ℚ) ^ 4 * (N : ℚ)) : ((p : ℤ) ^ 4) ∣ q.num := by
  have h3 : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
  have h2 : ((q.num * (D : ℤ) : ℤ) : ℚ) = (((p : ℤ) ^ 4 * (N * (q.den : ℤ)) : ℤ) : ℚ) := by
    push_cast
    linear_combination (q.den : ℚ) * hq - (D : ℚ) * h3
  have h4 : q.num * (D : ℤ) = (p : ℤ) ^ 4 * (N * (q.den : ℤ)) := Int.cast_injective h2
  have hcop : IsCoprime ((p : ℤ) ^ 4) (D : ℤ) := (Nat.isCoprime_iff_coprime.mpr hD).pow_left
  exact hcop.dvd_of_dvd_mul_right (Dvd.intro _ h4.symm)

theorem OMA.solution : type_of% @OMA.S_oeis_a357560.main := by
  intro p hp hp7
  -- the naturals `e k` with `C(p-1+k,k) = p * e k` and `e k * k = 1 + p * H(k-1)` modulo `p^2`
  have hex : ∀ k : ℕ, ∃ e : ℕ, 1 ≤ k → k < p →
      ((p - 1 + k).choose k = p * e ∧
        (e : ZMod (p ^ 2)) * (k : ZMod (p ^ 2)) =
          1 + (p : ZMod (p ^ 2)) * harmR p (k - 1)) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k < p
    · obtain ⟨hk1, hkp⟩ := hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      obtain ⟨e, h1, h2⟩ := choose_eq_p_mul hp m hkp
      refine ⟨e, fun _ _ => ⟨?_, ?_⟩⟩
      · have h : p - 1 + (m + 1) = p + m := by omega
        rw [h]
        exact h1
      · rw [Nat.add_sub_cancel, ← Nat.cast_mul, h2]
        exact choose_add_zmod hp m (by omega)
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose e he using hex
  -- the naturals `c k = (p-1)! / k`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, ∀ k ∈ Finset.Icc 1 (p - 1), k * c k = (p - 1).factorial :=
    ⟨fun k => (p - 1).factorial / k, fun k hk => by
      simp only [Finset.mem_Icc] at hk
      exact Nat.mul_div_cancel' (Nat.dvd_factorial (by omega) hk.2)⟩
  have heven : Even (p - 1) := hp.even_sub_one (by omega)
  -- each term modulo `p^2`
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (c k : ZMod (p ^ 2)) *
          ((-1 : ZMod (p ^ 2)) ^ (p - 1 + k) * (((p - 1).choose k : ℕ) : ZMod (p ^ 2))) *
          (e k : ZMod (p ^ 2)) ^ 2 =
        (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) *
          (((k : ZMod (p ^ 2))⁻¹) ^ 3 - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4 +
            (p : ZMod (p ^ 2)) * (((k : ZMod (p ^ 2))⁻¹) ^ 3 * harmR p (k - 1))) := by
    intro k hk
    have h2 : (k : ZMod (p ^ 2)) * (c k : ZMod (p ^ 2)) =
        (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) := by
      rw [← Nat.cast_mul, hc k hk]
    simp only [Finset.mem_Icc] at hk
    have h1 := mul_inv_p2 hp (k := k) (by omega) (by omega)
    have h3 := neg_one_pow_mul_choose_zmod hp k (by omega)
    have hsign : (-1 : ZMod (p ^ 2)) ^ (p - 1 + k) = (-1) ^ k := by
      rw [pow_add (-1 : ZMod (p ^ 2)) (p - 1) k, heven.neg_one_pow, one_mul]
    have hh : harmR p k = harmR p (k - 1) + (k : ZMod (p ^ 2))⁻¹ := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [harmR_succ, Nat.add_sub_cancel]
    rw [hh] at h3
    have hA := ring_term _ _ _ _ _ _ h1 (p_sq_zero p) h3 (he k hk.1 (by omega)).2
    rw [hsign, ring_scale _ _ _ _ _ _ h1 h2, hA]
  -- `p^2` divides the integer sum
  have hS : ((p : ℤ) ^ 2) ∣ ∑ k ∈ Finset.Icc 1 (p - 1),
      (c k : ℤ) * ((-1 : ℤ) ^ (p - 1 + k) * ((p - 1).choose k : ℤ)) * (e k : ℤ) ^ 2 := by
    have hcast : ((∑ k ∈ Finset.Icc 1 (p - 1),
        (c k : ℤ) * ((-1 : ℤ) ^ (p - 1 + k) * ((p - 1).choose k : ℤ)) * (e k : ℤ) ^ 2 : ℤ) :
          ZMod (p ^ 2)) = 0 := by
      have h4 : ((∑ k ∈ Finset.Icc 1 (p - 1),
          (c k : ℤ) * ((-1 : ℤ) ^ (p - 1 + k) * ((p - 1).choose k : ℤ)) * (e k : ℤ) ^ 2 : ℤ) :
            ZMod (p ^ 2)) =
          ∑ k ∈ Finset.Icc 1 (p - 1), (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) *
            (((k : ZMod (p ^ 2))⁻¹) ^ 3 - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 4 +
              (p : ZMod (p ^ 2)) * (((k : ZMod (p ^ 2))⁻¹) ^ 3 * harmR p (k - 1))) := by
        rw [Int.cast_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [← hterm k hk]
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
      rw [h4, ← Finset.mul_sum, sum_zmod_zero hp hp7, mul_zero]
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
    exact_mod_cast h
  obtain ⟨N, hN⟩ := hS
  have hNq : ∑ k ∈ Finset.Icc 1 (p - 1),
      (c k : ℚ) * ((-1 : ℚ) ^ (p - 1 + k) * ((p - 1).choose k : ℚ)) * (e k : ℚ) ^ 2 =
        (p : ℚ) ^ 2 * (N : ℚ) := by
    have h := congrArg (Int.cast (R := ℚ)) hN
    push_cast at h
    exact h
  -- `s(p-1) * (p-1)! = p^2 * (the integer sum)`
  have hsum : OMA.S_oeis_a357560.s (p - 1) * (((p - 1).factorial : ℕ) : ℚ) =
      (p : ℚ) ^ 2 * ∑ k ∈ Finset.Icc 1 (p - 1),
        (c k : ℚ) * ((-1 : ℚ) ^ (p - 1 + k) * ((p - 1).choose k : ℚ)) * (e k : ℚ) ^ 2 := by
    unfold OMA.S_oeis_a357560.s
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hD : (((p - 1).factorial : ℕ) : ℚ) = (k : ℚ) * (c k : ℚ) := by
      rw [← Nat.cast_mul, hc k hk]
    simp only [Finset.mem_Icc] at hk
    obtain ⟨h1, -⟩ := he k hk.1 (by omega)
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1q : ((p - 1 + k).choose k : ℚ) = (p : ℚ) * (e k : ℚ) := by
      exact_mod_cast h1
    rw [hD, h1q]
    calc (-1 : ℚ) ^ (p - 1 + k) * (1 / (k : ℚ)) * ((p - 1).choose k : ℚ) *
          ((p : ℚ) * (e k : ℚ)) ^ 2 * ((k : ℚ) * (c k : ℚ))
        = (1 / (k : ℚ) * (k : ℚ)) * ((p : ℚ) ^ 2 *
            ((c k : ℚ) * ((-1 : ℚ) ^ (p - 1 + k) * ((p - 1).choose k : ℚ)) *
              (e k : ℚ) ^ 2)) := by ring
      _ = (p : ℚ) ^ 2 * ((c k : ℚ) * ((-1 : ℚ) ^ (p - 1 + k) * ((p - 1).choose k : ℚ)) *
            (e k : ℚ) ^ 2) := by
          rw [one_div_mul_cancel hk0, one_mul]
  have hq : OMA.S_oeis_a357560.s (p - 1) * (((p - 1).factorial : ℕ) : ℚ) =
      (p : ℚ) ^ 4 * (N : ℚ) := by
    rw [hsum, hNq]
    ring
  have hcop : Nat.Coprime p (p - 1).factorial :=
    hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := hp.dvd_factorial.mp hd
      omega)
  exact num_dvd_aux _ _ N hcop hq
