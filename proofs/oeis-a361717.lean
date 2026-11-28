import OMAStatements.S_oeis_a361717
import Mathlib

/-!
# OEIS A361717: two supercongruences conjectured by Peter Bala (Mar 26 2023)

`a(n) = Sum_{k<n} C(n-1,k)^2 C(n+k,k)`.
1. `a(p) == 0 (mod p^4)` for every prime `p >= 5`;
2. `a(p-1) == 1 - 2p - p^2 (mod p^3)` for every prime `p` other than `3`.

Everything is done in the rationals, `D p e x` meaning that `x` lies in `p^e Z_(p)`.
Write `H1, H2, H3` for the harmonic numbers of order 1, 2, 3 (`Hn j n = Sum_{i=1..n} 1/i^j`).

* `T(k) = C(p-1,k)^2 C(p+k,k) = Prod_{i<=k} (1 - p/i)^2 (1 + p/i)`, and
  `(1-x)^2 (1+x) = 1 - x - x^2 + x^3`, so for `k < p`
  `T(k) == 1 - p H1(k) + p^2 (H1(k)^2 - 3 H2(k))/2
           + p^3 (-H3(k)/3 + 3 H1(k) H2(k)/2 - H1(k)^3/6)  (mod p^4)`.
* The sums over `k = 0..n` of `H1(k)`, `H2(k)`, `H3(k)`, `H1(k)^2`, `H1(k)^3` have closed forms in
  `H1(n)`, `H2(n)`, `H3(n)`.
* Wolstenholme: `H2(p-1) == 0 (mod p)` (the map `u -> 2u mod p` permutes the residues, and `3` is a
  unit) and `H1(p-1) == 0 (mod p^2)` (pairing `u` with `p - u`), for `p >= 5`.
* Reflection: `H1(p-1-k) == H1(k)` and `H2(p-1-k) == -H2(k) (mod p)`, hence
  `Sum_{k<p} H1(k) H2(k) == 0 (mod p)`.
* Conjecture 1 follows by summing the expansion over `k < p`.
* For Conjecture 2, `C(p-2,k)^2 C(p-1+k,k) = p c_k T(k)` with
  `c_k = (p-1-k)^2 / ((p-1)^2 (p+k))` for `1 <= k <= p-1` (the term `k = p-1` vanishes), and
  `c_k T(k) == (k+1)^2/k (1 + 2p - p H1(k)) - 2p (k+1)/k - p (k+1)^2/k^2  (mod p^2)`;
  the sum of the right-hand sides over `k = 1..p-1` has a closed form, which is `-2 - p` modulo `p^2`.
  The prime `p = 2` is checked directly.
-/

namespace A361717

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### the predicate `x ∈ p^e ℤ_(p)` -/

/-- `D p e x` : the rational `x` lies in `p^e * ℤ_(p)`. -/
private def D (p e : ℕ) (x : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, ¬ p ∣ b ∧ x * (b : ℚ) = (p : ℚ) ^ e * (a : ℚ)

private lemma D.zero (e : ℕ) : D p e 0 := ⟨0, 1, hp.out.not_dvd_one, by simp⟩

omit hp in
private lemma D.neg {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (-x) := by
  obtain ⟨a, b, hb, h⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h⟩

private lemma D.add {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x + y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    linear_combination (b' : ℚ) * h + (b : ℚ) * h'

private lemma D.sub {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

private lemma D.mul {e f : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p f y) : D p (e + f) (x * y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * a', b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    rw [pow_add]
    linear_combination (y * (b' : ℚ)) * h + ((p : ℚ) ^ e * (a : ℚ)) * h'

omit hp in
private lemma D.le {e f : ℕ} {x : ℚ} (hx : D p e x) (hfe : f ≤ e) : D p f x := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hfe
  exact ⟨(p : ℤ) ^ c * a, b, hb, by push_cast; rw [h, pow_add]; ring⟩

private lemma D.nat (n : ℕ) : D p 0 (n : ℚ) := ⟨(n : ℤ), 1, hp.out.not_dvd_one, by simp⟩

private lemma D.one : D p 0 (1 : ℚ) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

private lemma D.ppow (e : ℕ) : D p e ((p : ℚ) ^ e) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

private lemma D.mul0 {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p 0 y) : D p e (x * y) :=
  (hx.mul hy).le (by omega)

private lemma D.mul0' {e : ℕ} {x y : ℚ} (hy : D p 0 y) (hx : D p e x) : D p e (y * x) :=
  (hy.mul hx).le (by omega)

private lemma D.mul00 {x y : ℚ} (hx : D p 0 x) (hy : D p 0 y) : D p 0 (x * y) := hx.mul0 hy

omit hp in
private lemma D.inv {u : ℕ} (hu : ¬ p ∣ u) : D p 0 ((u : ℚ)⁻¹) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h
    apply hu
    have h0 : u = 0 := by exact_mod_cast h
    rw [h0]; exact dvd_zero p
  exact ⟨1, u, hu, by rw [inv_mul_cancel₀ hu0]; simp⟩

private lemma D.sum {ι : Type*} {e : ℕ} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p e (∑ i ∈ s, f i) :=
  Finset.sum_induction f (D p e) (fun _ _ ha hb => ha.add hb) (D.zero e) h

private lemma D.pow {e : ℕ} {x : ℚ} (hx : D p e x) (n : ℕ) : D p (e * n) (x ^ n) := by
  induction n with
  | zero => simpa using (D.one (p := p))
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hx

private lemma D.pow0 {x : ℚ} (hx : D p 0 x) (n : ℕ) : D p 0 (x ^ n) :=
  (hx.pow n).le (Nat.zero_le _)

private lemma D.cancel {e c : ℕ} {x : ℚ} (h : D p (e + c) ((p : ℚ) ^ c * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, b, hb, ?_⟩
  have hpc : ((p : ℚ) ^ c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply mul_left_cancel₀ hpc
  rw [pow_add] at h
  linear_combination h

private lemma D.ucancel {e u : ℕ} {x : ℚ} (hu : ¬ p ∣ u) (h : D p e ((u : ℚ) * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, u * b, ?_, by push_cast; linear_combination h⟩
  intro hd
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
  · exact hu h1
  · exact hb h1

private lemma D.dvd {e : ℕ} {z : ℤ} (h : D p e (z : ℚ)) : (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, b, hb, h⟩ := h
  have h2 : z * (b : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast h
  have hc : IsCoprime ((p : ℤ) ^ e) (b : ℤ) := by
    have h3 : Nat.Coprime (p ^ e) b :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
    have h4 := Nat.isCoprime_iff_coprime.mpr h3
    simpa using h4
  exact hc.dvd_of_dvd_mul_right ⟨a, h2⟩

omit hp in
private lemma D.congr {e : ℕ} {x y : ℚ} (h : D p e x) (hxy : x = y) : D p e y := hxy ▸ h

private lemma D.exists_eq {e : ℕ} {x : ℚ} (h : D p e x) :
    ∃ y : ℚ, D p 0 y ∧ x = (p : ℚ) ^ e * y := by
  have hpe : ((p : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hx : (p : ℚ) ^ e * (x / (p : ℚ) ^ e) = x := by field_simp
  refine ⟨x / (p : ℚ) ^ e, ?_, hx.symm⟩
  apply D.cancel (c := e)
  rw [zero_add, hx]
  exact h

private lemma D.ofNat (n : ℕ) [n.AtLeastTwo] : D p 0 (OfNat.ofNat n : ℚ) := D.nat n

private lemma D.three : D p 0 (3 : ℚ) := by simpa using D.nat (p := p) 3

omit hp in
private lemma nd2 (h5 : 5 ≤ p) : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)

omit hp in
private lemma nd3 (h5 : 5 ≤ p) : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)

omit hp in
private lemma nd4 (h5 : 5 ≤ p) : ¬ p ∣ 4 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)

private lemma D.div2 (h5 : 5 ≤ p) {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (x / 2) := by
  have h2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) (nd2 h5)
  rw [div_eq_mul_inv]
  exact hx.mul0 h2

private lemma D.div3 (h5 : 5 ≤ p) {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (x / 3) := by
  have h3 : D p 0 ((3 : ℚ)⁻¹) := by simpa using D.inv (p := p) (nd3 h5)
  rw [div_eq_mul_inv]
  exact hx.mul0 h3

/-! ### harmonic numbers -/

/-- `Hn j n = ∑_{i=1}^{n} 1 / i^j` -/
private def Hn (j n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (((i : ℚ) + 1)⁻¹) ^ j

private lemma Hn_succ (j n : ℕ) : Hn j (n + 1) = Hn j n + (((n : ℚ) + 1)⁻¹) ^ j := by
  unfold Hn; rw [Finset.sum_range_succ]

private lemma Hn_zero (j : ℕ) : Hn j 0 = 0 := by simp [Hn]

omit hp in
private lemma inv_D0 {i : ℕ} (hi : i + 1 < p) : D p 0 (((i : ℚ) + 1)⁻¹) := by
  have h : ¬ p ∣ (i + 1) := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) hi
  have h2 := D.inv h
  push_cast at h2
  exact h2

private lemma Hn_D0 (j : ℕ) {n : ℕ} (hn : n < p) : D p 0 (Hn j n) :=
  D.sum _ _ fun i hi => (inv_D0 (by have := Finset.mem_range.mp hi; omega)).pow0 j

private lemma sum_H1 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Hn 1 k = ((n : ℚ) + 1) * Hn 1 n - n := by
  induction n with
  | zero => simp [Hn]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Hn_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma sum_H2 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Hn 2 k = ((n : ℚ) + 1) * Hn 2 n - Hn 1 n := by
  induction n with
  | zero => simp [Hn]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Hn_succ, Hn_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma sum_H3 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Hn 3 k = ((n : ℚ) + 1) * Hn 3 n - Hn 2 n := by
  induction n with
  | zero => simp [Hn]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Hn_succ, Hn_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma sum_H11 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Hn 1 k ^ 2 =
      ((n : ℚ) + 1) * Hn 1 n ^ 2 - (2 * (n : ℚ) + 1) * Hn 1 n + 2 * n := by
  induction n with
  | zero => simp [Hn]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Hn_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma sum_H111 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Hn 1 k ^ 3 =
      ((n : ℚ) + 1) * Hn 1 n ^ 3 - 3 / 2 * (2 * (n : ℚ) + 1) * Hn 1 n ^ 2 +
        3 * (2 * (n : ℚ) + 1) * Hn 1 n + Hn 2 n / 2 - 6 * n := by
  induction n with
  | zero => simp [Hn]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Hn_succ, Hn_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-! ### the terms of `a(p)` and their expansion -/

/-- `T p k = C(p-1,k)^2 C(p+k,k)` -/
private def T (p k : ℕ) : ℚ := ((p - 1).choose k : ℚ) ^ 2 * ((p + k).choose k : ℚ)

omit hp in
private lemma T_succ {k : ℕ} (hk : k + 1 < p) :
    T p (k + 1) = T p k * (1 + (p : ℚ) * (-((k : ℚ) + 1)⁻¹) +
      (p : ℚ) ^ 2 * (-(((k : ℚ) + 1)⁻¹) ^ 2) + (p : ℚ) ^ 3 * (((k : ℚ) + 1)⁻¹) ^ 3) := by
  have h1 := Nat.choose_succ_right_eq (p - 1) k
  have h2 := Nat.add_one_mul_choose_eq (p + k) k
  have hk0 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h1' : ((p - 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) =
      ((p - 1).choose k : ℚ) * ((p : ℚ) - 1 - (k : ℚ)) := by
    have h := congrArg (Nat.cast (R := ℚ)) h1
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : k ≤ p - 1),
      Nat.cast_sub (by omega : 1 ≤ p)] at h
    push_cast at h
    exact h
  have h2' : ((p : ℚ) + (k : ℚ) + 1) * ((p + k).choose k : ℚ) =
      ((p + (k + 1)).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
    have h := congrArg (Nat.cast (R := ℚ)) h2
    push_cast at h
    exact h
  have e1 : ((p - 1).choose (k + 1) : ℚ) =
      ((p - 1).choose k : ℚ) * ((p : ℚ) - 1 - (k : ℚ)) * ((k : ℚ) + 1)⁻¹ := by
    rw [← h1', mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  have e2 : ((p + (k + 1)).choose (k + 1) : ℚ) =
      ((p : ℚ) + (k : ℚ) + 1) * ((p + k).choose k : ℚ) * ((k : ℚ) + 1)⁻¹ := by
    rw [h2', mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  unfold T
  rw [e1, e2]
  field_simp
  ring

private def cA (k : ℕ) : ℚ := -(Hn 1 k)

private def cB (k : ℕ) : ℚ := (Hn 1 k ^ 2 - 3 * Hn 2 k) / 2

private def cC (k : ℕ) : ℚ := -(Hn 3 k) / 3 + 3 * Hn 1 k * Hn 2 k / 2 - Hn 1 k ^ 3 / 6

/-- third order expansion of `T p k` -/
private def E (p k : ℕ) : ℚ := 1 + (p : ℚ) * cA k + (p : ℚ) ^ 2 * cB k + (p : ℚ) ^ 3 * cC k

private lemma cA_D0 {k : ℕ} (hk : k < p) : D p 0 (cA k) := (Hn_D0 1 hk).neg

private lemma cB_D0 (h5 : 5 ≤ p) {k : ℕ} (hk : k < p) : D p 0 (cB k) :=
  D.div2 h5 (((Hn_D0 1 hk).pow0 2).sub (D.three.mul0 (Hn_D0 2 hk)))

private lemma cC_D0 (h5 : 5 ≤ p) {k : ℕ} (hk : k < p) : D p 0 (cC k) := by
  have e : cC k = -(Hn 3 k) / 3 + 3 * Hn 1 k * Hn 2 k / 2 - Hn 1 k ^ 3 / 2 / 3 := by
    unfold cC; ring
  rw [e]
  exact ((D.div3 h5 (Hn_D0 3 hk).neg).add
    (D.div2 h5 ((D.three.mul0 (Hn_D0 1 hk)).mul0 (Hn_D0 2 hk)))).sub
      (D.div3 h5 (D.div2 h5 ((Hn_D0 1 hk).pow0 3)))

private lemma expand_step {u v A B C α β γ : ℚ} (hA : D p 0 A) (hB : D p 0 B) (hC : D p 0 C)
    (hα : D p 0 α) (hβ : D p 0 β) (hγ : D p 0 γ)
    (hu : D p 4 (u - (1 + (p : ℚ) * A + (p : ℚ) ^ 2 * B + (p : ℚ) ^ 3 * C)))
    (hv : v = 1 + (p : ℚ) * α + (p : ℚ) ^ 2 * β + (p : ℚ) ^ 3 * γ) :
    D p 4 (u * v - (1 + (p : ℚ) * (A + α) + (p : ℚ) ^ 2 * (B + A * α + β) +
      (p : ℚ) ^ 3 * (C + B * α + A * β + γ))) := by
  have hP : D p 0 (p : ℚ) := D.nat p
  have hv0 : D p 0 v := by
    rw [hv]
    exact ((D.one.add (hP.mul0 hα)).add ((hP.pow0 2).mul0 hβ)).add ((hP.pow0 3).mul0 hγ)
  have e : u * v - (1 + (p : ℚ) * (A + α) + (p : ℚ) ^ 2 * (B + A * α + β) +
      (p : ℚ) ^ 3 * (C + B * α + A * β + γ)) =
      (u - (1 + (p : ℚ) * A + (p : ℚ) ^ 2 * B + (p : ℚ) ^ 3 * C)) * v +
        (p : ℚ) ^ 4 * (C * α + B * β + A * γ + (p : ℚ) * (C * β + B * γ) +
          (p : ℚ) ^ 2 * (C * γ)) := by
    rw [hv]; ring
  rw [e]
  refine (hu.mul0 hv0).add ((D.ppow 4).mul0 ?_)
  exact ((((hC.mul0 hα).add (hB.mul0 hβ)).add (hA.mul0 hγ)).add
    (hP.mul0 ((hC.mul0 hβ).add (hB.mul0 hγ)))).add ((hP.pow0 2).mul0 (hC.mul0 hγ))

private lemma T_expand (h5 : 5 ≤ p) : ∀ k : ℕ, k < p → D p 4 (T p k - E p k) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : T p 0 - E p 0 = 0 := by simp [T, E, cA, cB, cC, Hn]
    rw [h0]; exact D.zero 4
  | succ k ih =>
    intro hk
    have hk' : k < p := by omega
    have hy : D p 0 (((k : ℚ) + 1)⁻¹) := inv_D0 hk
    have hstep := expand_step (cA_D0 hk') (cB_D0 h5 hk') (cC_D0 h5 hk') hy.neg
      (hy.pow0 2).neg (hy.pow0 3) (ih hk') rfl
    rw [T_succ hk]
    refine hstep.congr ?_
    unfold E cA cB cC
    simp only [Hn_succ]
    ring

omit hp in
private lemma sum_E (n : ℕ) : ∑ k ∈ Finset.range n, E p k =
    (n : ℚ) - (p : ℚ) * ∑ k ∈ Finset.range n, Hn 1 k +
      (p : ℚ) ^ 2 * ((∑ k ∈ Finset.range n, Hn 1 k ^ 2 - 3 * ∑ k ∈ Finset.range n, Hn 2 k) / 2) +
      (p : ℚ) ^ 3 * (-(∑ k ∈ Finset.range n, Hn 3 k) / 3 +
        3 * (∑ k ∈ Finset.range n, Hn 1 k * Hn 2 k) / 2 -
        (∑ k ∈ Finset.range n, Hn 1 k ^ 3) / 6) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    unfold E cA cB cC
    push_cast
    ring

/-! ### Wolstenholme -/

private lemma Hn_eq_range {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    Hn j n = ∑ u ∈ Finset.range (n + 1), ((u : ℚ)⁻¹) ^ j := by
  rw [Finset.sum_range_succ']
  simp [Hn, hj]

private lemma sum_range_double (hp2 : ¬ p ∣ 2) (f : ℕ → ℚ) :
    ∑ u ∈ Finset.range p, f (2 * u % p) = ∑ u ∈ Finset.range p, f u := by
  have hq : Nat.Coprime p 2 := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hp2
  have hinj : Set.InjOn (fun u => 2 * u % p) (Finset.range p : Set ℕ) := by
    intro u hu v hv h
    have hu' := Finset.mem_range.mp (Finset.mem_coe.mp hu)
    have hv' := Finset.mem_range.mp (Finset.mem_coe.mp hv)
    have h1 : 2 * u ≡ 2 * v [MOD p] := h
    have h2 : u ≡ v [MOD p] := Nat.ModEq.cancel_left_of_coprime hq h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hu' hv'
  have himg : (Finset.range p).image (fun u => 2 * u % p) = Finset.range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp.out.pos)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ u ∈ Finset.range p, f (2 * u % p)
      = ∑ w ∈ (Finset.range p).image (fun u => 2 * u % p), f w := by
        rw [Finset.sum_image hinj]
    _ = ∑ u ∈ Finset.range p, f u := by rw [himg]

private lemma D_inv_pow_congr {s x y : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : D p s ((x : ℚ) - (y : ℚ))) (j : ℕ) :
    D p s (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    intro h0
    apply hx
    have h1 : x = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hy0 : (y : ℚ) ≠ 0 := by
    intro h0
    apply hy
    have h1 : y = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hxx : (x : ℚ) * (x : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hyy : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have h1 : D p s ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) := by
    have h2 : (x : ℚ)⁻¹ - (y : ℚ)⁻¹ = -(((x : ℚ) - (y : ℚ)) * ((x : ℚ)⁻¹ * (y : ℚ)⁻¹)) := by
      linear_combination (y : ℚ)⁻¹ * hxx - (x : ℚ)⁻¹ * hyy
    rw [h2]
    exact (h.mul0 (((D.inv hx).mul (D.inv hy)).le (by omega))).neg
  induction j with
  | zero => simpa using D.zero (p := p) s
  | succ j ih =>
    have h3 : ((x : ℚ)⁻¹) ^ (j + 1) - ((y : ℚ)⁻¹) ^ (j + 1) =
        (x : ℚ)⁻¹ * (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) +
          ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) * ((y : ℚ)⁻¹) ^ j := by ring
    rw [h3]
    exact ((D.inv hx).mul0' ih).add (h1.mul0 ((D.inv hy).pow0 j))

/-- `∑_{i<p} 1/i^2 ≡ 0 (mod p)` for `p ≥ 5` -/
private lemma W2 (h5 : 5 ≤ p) : D p 1 (Hn 2 (p - 1)) := by
  have hp2 := nd2 (p := p) h5
  have hp3 := nd3 (p := p) h5
  have e0 : Hn 2 (p - 1) = ∑ u ∈ Finset.range p, ((u : ℚ)⁻¹) ^ 2 := by
    rw [Hn_eq_range (j := 2) (by norm_num) (p - 1), Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have e1 : ∑ u ∈ Finset.range p, (((2 * u % p : ℕ) : ℚ)⁻¹) ^ 2 =
      ∑ u ∈ Finset.range p, ((u : ℚ)⁻¹) ^ 2 :=
    sum_range_double hp2 (fun w => ((w : ℚ)⁻¹) ^ 2)
  have e2 : D p 1 (∑ u ∈ Finset.range p,
      ((((2 * u % p : ℕ) : ℚ)⁻¹) ^ 2 - (((2 * u : ℕ) : ℚ)⁻¹) ^ 2)) := by
    apply D.sum
    intro u hu
    have hup := Finset.mem_range.mp hu
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · simpa using D.zero (p := p) 1
    · have hnd : ¬ p ∣ u := Nat.not_dvd_of_pos_of_lt hu0 hup
      have h2u : ¬ p ∣ 2 * u := by
        intro hd
        rcases (Nat.Prime.dvd_mul hp.out).mp hd with h4 | h4
        · exact hp2 h4
        · exact hnd h4
      have hmod : ¬ p ∣ 2 * u % p := fun hd => h2u ((Nat.dvd_mod_iff (dvd_refl p)).mp hd)
      apply D_inv_pow_congr hmod h2u
      have h6 : ((2 * u % p : ℕ) : ℚ) - ((2 * u : ℕ) : ℚ) =
          -((p : ℚ) ^ 1 * ((2 * u / p : ℕ) : ℚ)) := by
        have h7 := Nat.div_add_mod (2 * u) p
        have h8 : ((p * (2 * u / p) + 2 * u % p : ℕ) : ℚ) = ((2 * u : ℕ) : ℚ) := by rw [h7]
        rw [pow_one]
        push_cast at h8 ⊢
        linarith
      rw [h6]
      exact ((D.ppow 1).mul0 (D.nat _)).neg
  have e3 : ∑ u ∈ Finset.range p, (((2 * u : ℕ) : ℚ)⁻¹) ^ 2 =
      (1 / 4) * ∑ u ∈ Finset.range p, ((u : ℚ)⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    ring
  rw [Finset.sum_sub_distrib, e1, e3, ← e0] at e2
  have e4 : D p 1 (((3 : ℕ) : ℚ) * Hn 2 (p - 1)) :=
    ((D.nat 4).mul0' e2).congr (by push_cast; ring)
  exact D.ucancel hp3 e4

/-- Wolstenholme: `∑_{i<p} 1/i ≡ 0 (mod p^2)` for `p ≥ 5` -/
private lemma W1 (h5 : 5 ≤ p) : D p 2 (Hn 1 (p - 1)) := by
  have hp2 := nd2 (p := p) h5
  have hW2 := W2 h5
  have href : ∑ i ∈ Finset.range (p - 1), ((((p - 1 - 1 - i : ℕ) : ℚ) + 1)⁻¹) ^ 1 =
      Hn 1 (p - 1) :=
    Finset.sum_range_reflect (fun i => (((i : ℚ) + 1)⁻¹) ^ 1) (p - 1)
  have hterm : ∀ i ∈ Finset.range (p - 1),
      (((i : ℚ) + 1)⁻¹) ^ 1 + ((((p - 1 - 1 - i : ℕ) : ℚ) + 1)⁻¹) ^ 1 =
        (p : ℚ) ^ 1 * (-((((i : ℚ) + 1)⁻¹) ^ 2) + (p : ℚ) ^ 1 *
          ((((i : ℚ) + 1)⁻¹) ^ 2 * (((p - 1 - 1 - i : ℕ) : ℚ) + 1)⁻¹)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    obtain ⟨w, hw⟩ : ∃ w : ℕ, p - 1 - 1 - i = w := ⟨_, rfl⟩
    rw [hw]
    have hc : ((w : ℚ) + 1) + ((i : ℚ) + 1) = (p : ℚ) := by
      have h1 : w + 1 + (i + 1) = p := by omega
      exact_mod_cast h1
    have hi0 : ((i : ℚ) + 1) ≠ 0 := by positivity
    have hw0 : ((w : ℚ) + 1) ≠ 0 := by positivity
    rw [← hc]
    field_simp
    ring
  have hsum : Hn 1 (p - 1) + Hn 1 (p - 1) =
      ∑ i ∈ Finset.range (p - 1),
        ((((i : ℚ) + 1)⁻¹) ^ 1 + ((((p - 1 - 1 - i : ℕ) : ℚ) + 1)⁻¹) ^ 1) := by
    rw [Finset.sum_add_distrib, href]
    rfl
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have hrest : D p 0 (∑ i ∈ Finset.range (p - 1),
      (((i : ℚ) + 1)⁻¹) ^ 2 * (((p - 1 - 1 - i : ℕ) : ℚ) + 1)⁻¹) := by
    apply D.sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact ((inv_D0 (by omega)).pow0 2).mul0 (inv_D0 (by omega))
  have hW2' : D p 1 (∑ i ∈ Finset.range (p - 1), (((i : ℚ) + 1)⁻¹) ^ 2) := hW2
  have h2 : D p 2 (Hn 1 (p - 1) + Hn 1 (p - 1)) := by
    rw [hsum]
    exact ((D.ppow 1).mul (hW2'.neg.add ((D.ppow 1).mul0 hrest))).le (by norm_num)
  exact D.ucancel hp2 (h2.congr (by push_cast; ring))

/-! ### reflection `k ↦ p - 1 - k` -/

private lemma refl_H (h5 : 5 ≤ p) : ∀ k : ℕ, k < p →
    D p 1 (Hn 1 (p - 1 - k) - Hn 1 k) ∧ D p 1 (Hn 2 (p - 1 - k) + Hn 2 k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · have h := (W1 h5).le (by norm_num : 1 ≤ 2)
      simpa [Hn_zero] using h
    · simpa [Hn_zero] using W2 h5
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨m, hm⟩ : ∃ m, p - 1 - k = m + 1 := ⟨p - 1 - k - 1, by omega⟩
    have hm' : p - 1 - (k + 1) = m := by omega
    rw [hm, Hn_succ] at ih1 ih2
    rw [hm', Hn_succ, Hn_succ]
    have hmk : (m : ℚ) + 1 + ((k : ℚ) + 1) = (p : ℚ) := by
      have h1 : m + 1 + (k + 1) = p := by omega
      exact_mod_cast h1
    have hm0 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have hk0 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hDm : D p 0 (((m : ℚ) + 1)⁻¹) := inv_D0 (by omega)
    have hDk : D p 0 (((k : ℚ) + 1)⁻¹) := inv_D0 hk
    refine ⟨?_, ?_⟩
    · have e : Hn 1 m - (Hn 1 k + (((k : ℚ) + 1)⁻¹) ^ 1) =
          (Hn 1 m + (((m : ℚ) + 1)⁻¹) ^ 1 - Hn 1 k) -
            (p : ℚ) ^ 1 * (((m : ℚ) + 1)⁻¹ * ((k : ℚ) + 1)⁻¹) := by
        rw [← hmk]; field_simp; ring
      rw [e]
      exact ih1.sub ((D.ppow 1).mul0 (hDm.mul0 hDk))
    · have e : Hn 2 m + (Hn 2 k + (((k : ℚ) + 1)⁻¹) ^ 2) =
          (Hn 2 m + (((m : ℚ) + 1)⁻¹) ^ 2 + Hn 2 k) +
            (p : ℚ) ^ 1 * ((((m : ℚ) + 1) - ((k : ℚ) + 1)) *
              ((((m : ℚ) + 1)⁻¹) ^ 2 * (((k : ℚ) + 1)⁻¹) ^ 2)) := by
        rw [← hmk]; field_simp; ring
      rw [e]
      exact ih2.add ((D.ppow 1).mul0 ((((D.nat m).add D.one).sub ((D.nat k).add D.one)).mul0
        ((hDm.pow0 2).mul0 (hDk.pow0 2))))

private lemma S12_D (h5 : 5 ≤ p) : D p 1 (∑ k ∈ Finset.range p, Hn 1 k * Hn 2 k) := by
  have hp2 := nd2 (p := p) h5
  have href : ∑ k ∈ Finset.range p, Hn 1 (p - 1 - k) * Hn 2 (p - 1 - k) =
      ∑ k ∈ Finset.range p, Hn 1 k * Hn 2 k :=
    Finset.sum_range_reflect (fun k => Hn 1 k * Hn 2 k) p
  have h2 : ((2 : ℕ) : ℚ) * ∑ k ∈ Finset.range p, Hn 1 k * Hn 2 k =
      ∑ k ∈ Finset.range p, (Hn 1 k * Hn 2 k + Hn 1 (p - 1 - k) * Hn 2 (p - 1 - k)) := by
    rw [Finset.sum_add_distrib, href]
    push_cast; ring
  apply D.ucancel hp2
  rw [h2]
  apply D.sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  obtain ⟨r1, r2⟩ := refl_H h5 k hk'
  have e : Hn 1 k * Hn 2 k + Hn 1 (p - 1 - k) * Hn 2 (p - 1 - k) =
      (Hn 1 (p - 1 - k) - Hn 1 k) * Hn 2 (p - 1 - k) +
        Hn 1 k * (Hn 2 (p - 1 - k) + Hn 2 k) := by ring
  rw [e]
  exact (r1.mul0 (Hn_D0 2 (by omega))).add ((Hn_D0 1 hk').mul0' r2)

/-! ### Conjecture 1 -/

private lemma cast_a (n : ℕ) : ((OMA.S_oeis_a361717.a n : ℤ) : ℚ) =
    ∑ k ∈ Finset.range n, ((n - 1).choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) := by
  simp only [OMA.S_oeis_a361717.a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]

private lemma claim1 (h5 : 5 ≤ p) : (p : ℤ) ^ 4 ∣ OMA.S_oeis_a361717.a p := by
  apply D.dvd
  rw [cast_a]
  have hp3 := nd3 (p := p) h5
  have h1 : D p 4 (∑ k ∈ Finset.range p, T p k - ∑ k ∈ Finset.range p, E p k) := by
    rw [← Finset.sum_sub_distrib]
    exact D.sum _ _ fun k hk => T_expand h5 k (Finset.mem_range.mp hk)
  obtain ⟨H', hH', eH⟩ := (W1 h5).exists_eq
  obtain ⟨H2', hH2', eH2⟩ := (W2 h5).exists_eq
  obtain ⟨S', hS', eS⟩ := (S12_D h5).exists_eq
  have hH3 : D p 0 (Hn 3 (p - 1)) := Hn_D0 3 (by omega)
  have hP : D p 0 (p : ℚ) := D.nat p
  have hpp : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hc : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; simp
  have s1 := sum_H1 (p - 1)
  have s2 := sum_H2 (p - 1)
  have s3 := sum_H3 (p - 1)
  have s11 := sum_H11 (p - 1)
  have s111 := sum_H111 (p - 1)
  rw [hpp, hc] at s1 s2 s3 s11 s111
  have h2 : ((12 : ℕ) : ℚ) * ∑ k ∈ Finset.range p, E p k = (p : ℚ) ^ 4 *
      (-15 * H2' - 4 * Hn 3 (p - 1) - 2 * H' ^ 3 * (p : ℚ) ^ 6 + 6 * H' ^ 2 * (p : ℚ) ^ 4 +
        3 * H' ^ 2 * (p : ℚ) ^ 3 - 12 * H' * (p : ℚ) ^ 2 - 6 * H' * (p : ℚ) + 12 * H' +
        18 * S' + 12) := by
    rw [sum_E, s1, s2, s3, s11, s111, eS, eH, eH2]
    push_cast
    ring
  have h3 : D p 4 (((12 : ℕ) : ℚ) * ∑ k ∈ Finset.range p, E p k) := by
    rw [h2]
    refine (D.ppow 4).mul0 ?_
    repeat' first
      | exact hH' | exact hH2' | exact hS' | exact hH3 | exact hP | exact D.one
      | apply D.add | apply D.sub | apply D.mul00 | apply D.pow0 | apply D.neg
      | exact D.ofNat _
  have h12 : ¬ p ∣ 12 := by
    intro h
    have h' : p ∣ 4 * 3 := h
    rcases (Nat.Prime.dvd_mul hp.out).mp h' with h4 | h4
    · exact nd4 h5 h4
    · exact hp3 h4
  have h4 : D p 4 (∑ k ∈ Finset.range p, E p k) := D.ucancel h12 h3
  exact (h1.add h4).congr (by unfold T; ring)

/-! ### Conjecture 2 -/

/-- `T2 p k = C(p-2,k)^2 C(p-1+k,k)`, the terms of `a(p-1)` -/
private def T2 (p k : ℕ) : ℚ := ((p - 1 - 1).choose k : ℚ) ^ 2 * ((p - 1 + k).choose k : ℚ)

omit hp in
private lemma T2_eq (h5 : 5 ≤ p) {k : ℕ} (hk : k < p) :
    T2 p k * ((p : ℚ) - 1) ^ 2 * ((p : ℚ) + k) = (p : ℚ) * ((p : ℚ) - 1 - k) ^ 2 * T p k := by
  have h1 := Nat.choose_mul_succ_eq (p - 1 - 1) k
  have h2 := Nat.choose_mul_succ_eq (p - 1 + k) k
  rw [show p - 1 - 1 + 1 = p - 1 by omega] at h1
  rw [show p - 1 + k + 1 = p + k by omega, Nat.add_sub_cancel] at h2
  have h1' : ((p - 1 - 1).choose k : ℚ) * ((p : ℚ) - 1) =
      ((p - 1).choose k : ℚ) * ((p : ℚ) - 1 - (k : ℚ)) := by
    have h := congrArg (Nat.cast (R := ℚ)) h1
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : k ≤ p - 1),
      Nat.cast_sub (by omega : 1 ≤ p)] at h
    push_cast at h
    exact h
  have h2' : ((p - 1 + k).choose k : ℚ) * ((p : ℚ) + (k : ℚ)) =
      ((p + k).choose k : ℚ) * (p : ℚ) := by
    have h := congrArg (Nat.cast (R := ℚ)) h2
    push_cast at h
    exact h
  unfold T2 T
  linear_combination
    (((p - 1 - 1).choose k : ℚ) * ((p : ℚ) - 1) + ((p - 1).choose k : ℚ) * ((p : ℚ) - 1 - (k : ℚ))) *
      (((p - 1 + k).choose k : ℚ) * ((p : ℚ) + (k : ℚ))) * h1' +
    (((p - 1).choose k : ℚ) * ((p : ℚ) - 1 - (k : ℚ))) ^ 2 * h2'

private def cc (p k : ℕ) : ℚ :=
  ((p : ℚ) - 1 - k) ^ 2 * (((p : ℚ) - 1)⁻¹) ^ 2 * ((p : ℚ) + k)⁻¹

private def cpp (q : ℚ) (k : ℕ) : ℚ :=
  ((k : ℚ) + 1) ^ 2 * (k : ℚ)⁻¹ * (1 + 2 * q - q * Hn 1 k) - 2 * q * ((k : ℚ) + 1) * (k : ℚ)⁻¹ -
    q * ((k : ℚ) + 1) ^ 2 * ((k : ℚ)⁻¹) ^ 2

omit hp in
private lemma T2_cc (h5 : 5 ≤ p) {k : ℕ} (hk : k < p) :
    T2 p k = (p : ℚ) * (cc p k * T p k) := by
  have h := T2_eq h5 hk
  have h5q : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h5
  have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
  have hp1 : (p : ℚ) - 1 ≠ 0 := by linarith
  have hpk : (p : ℚ) + k ≠ 0 := by linarith
  have i1 : ((p : ℚ) - 1) * ((p : ℚ) - 1)⁻¹ = 1 := mul_inv_cancel₀ hp1
  have i2 : ((p : ℚ) + k) * ((p : ℚ) + k)⁻¹ = 1 := mul_inv_cancel₀ hpk
  unfold cc
  linear_combination ((((p : ℚ) - 1)⁻¹) ^ 2 * ((p : ℚ) + k)⁻¹) * h -
    T2 p k * (((p : ℚ) - 1) * ((p : ℚ) - 1)⁻¹) ^ 2 * i2 -
    T2 p k * (((p : ℚ) - 1) * ((p : ℚ) - 1)⁻¹ + 1) * i1

private lemma sum_cpp (q : ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), cpp q k =
      (1 + 2 * q) * ((n : ℚ) * ((n : ℚ) + 1) / 2 + 2 * n + Hn 1 n) - 2 * q * ((n : ℚ) + Hn 1 n) -
        q * ((n : ℚ) + 2 * Hn 1 n + Hn 2 n) -
        q * ((n : ℚ) * ((n : ℚ) + 1) / 2 * Hn 1 n - (n : ℚ) * ((n : ℚ) - 1) / 4 +
          2 * (((n : ℚ) + 1) * Hn 1 n - n) + (Hn 1 n ^ 2 + Hn 2 n) / 2) := by
  induction n with
  | zero => simp [cpp, Hn]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold cpp
    simp only [Hn_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma cT_D (h5 : 5 ≤ p) {k : ℕ} (hk0 : 0 < k) (hk : k < p) :
    D p 2 (cc p k * T p k - cpp (p : ℚ) k) := by
  have hnk : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt hk0 hk
  have hnpk : ¬ p ∣ p + k := fun h => hnk ((Nat.dvd_add_right (dvd_refl p)).mp h)
  have hnp1 : ¬ p ∣ p - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hDk : D p 0 ((k : ℚ)⁻¹) := D.inv hnk
  have hDpk : D p 0 (((p : ℚ) + k)⁻¹) := by
    have h := D.inv hnpk
    push_cast at h
    exact h
  have hDp1 : D p 0 (((p : ℚ) - 1)⁻¹) := by
    have h := D.inv hnp1
    rw [Nat.cast_sub (by omega : 1 ≤ p)] at h
    push_cast at h
    exact h
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h5q : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h5
  have hk0q : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
  have hp1q : (p : ℚ) - 1 ≠ 0 := by linarith
  have hpkq : (p : ℚ) + k ≠ 0 := by linarith
  have hDh : D p 0 (Hn 1 k) := Hn_D0 1 hk
  have hP : D p 0 (p : ℚ) := D.nat p
  have hK : D p 0 (k : ℚ) := D.nat k
  have hT2 : D p 2 (T p k - (1 - (p : ℚ) * Hn 1 k)) := by
    have h1 := T_expand h5 k hk
    have e : T p k - (1 - (p : ℚ) * Hn 1 k) =
        (T p k - E p k) + (p : ℚ) ^ 2 * (cB k + (p : ℚ) * cC k) := by
      unfold E cA; ring
    rw [e]
    exact (h1.le (by norm_num)).add
      ((D.ppow 2).mul0 ((cB_D0 h5 hk).add (hP.mul0 (cC_D0 h5 hk))))
  have hcc : D p 0 (cc p k) := by
    unfold cc
    exact ((((hP.sub D.one).sub hK).pow0 2).mul0 (hDp1.pow0 2)).mul0 hDpk
  have e2 : cc p k * (1 - (p : ℚ) * Hn 1 k) - cpp (p : ℚ) k = (p : ℚ) ^ 2 *
      ((Hn 1 k * (k : ℚ) ^ 4 * (p : ℚ) - 2 * Hn 1 k * (k : ℚ) ^ 4 +
        Hn 1 k * (k : ℚ) ^ 3 * (p : ℚ) ^ 2 - Hn 1 k * (k : ℚ) ^ 3 +
        2 * Hn 1 k * (k : ℚ) ^ 2 * (p : ℚ) ^ 2 - 4 * Hn 1 k * (k : ℚ) ^ 2 * (p : ℚ) +
        2 * Hn 1 k * (k : ℚ) ^ 2 + Hn 1 k * (k : ℚ) * (p : ℚ) ^ 2 -
        2 * Hn 1 k * (k : ℚ) * (p : ℚ) + Hn 1 k * (k : ℚ) - 2 * (k : ℚ) ^ 4 * (p : ℚ) +
        3 * (k : ℚ) ^ 4 - 2 * (k : ℚ) ^ 3 * (p : ℚ) ^ 2 + 2 * (k : ℚ) ^ 3 * (p : ℚ) -
        (k : ℚ) ^ 2 * (p : ℚ) ^ 2 + 2 * (k : ℚ) ^ 2 * (p : ℚ) - (k : ℚ) ^ 2 +
        2 * (k : ℚ) * (p : ℚ) ^ 2 - 4 * (k : ℚ) * (p : ℚ) + 2 * (k : ℚ) + (p : ℚ) ^ 2 -
        2 * (p : ℚ) + 1) *
        ((((p : ℚ) - 1)⁻¹) ^ 2 * ((p : ℚ) + k)⁻¹ * ((k : ℚ)⁻¹) ^ 2)) := by
    unfold cc cpp
    generalize Hn 1 k = h
    field_simp
    ring
  have e : cc p k * T p k - cpp (p : ℚ) k = cc p k * (T p k - (1 - (p : ℚ) * Hn 1 k)) +
      (cc p k * (1 - (p : ℚ) * Hn 1 k) - cpp (p : ℚ) k) := by ring
  rw [e, e2]
  refine (hcc.mul0' hT2).add ((D.ppow 2).mul0 ?_)
  refine D.mul00 ?_ (((hDp1.pow0 2).mul0 hDpk).mul0 (hDk.pow0 2))
  repeat' first
    | exact hDh | exact hK | exact hP | exact D.one
    | apply D.add | apply D.sub | apply D.mul00 | apply D.pow0
    | exact D.ofNat _

private lemma claim2 (h5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ (OMA.S_oeis_a361717.a (p - 1) - (1 - 2 * (p : ℤ) - (p : ℤ) ^ 2)) := by
  apply D.dvd
  push_cast
  rw [cast_a]
  have hpp : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hc : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; simp
  have hP : D p 0 (p : ℚ) := D.nat p
  have hlast : T2 p (p - 1) = 0 := by
    unfold T2
    rw [Nat.choose_eq_zero_of_lt (by omega : p - 1 - 1 < p - 1)]
    simp
  have hzero : T2 p 0 = 1 := by simp [T2]
  have hsum : ∑ k ∈ Finset.range (p - 1),
      ((p - 1 - 1).choose k : ℚ) ^ 2 * ((p - 1 + k).choose k : ℚ) =
      1 + (p : ℚ) ^ 1 * ∑ j ∈ Finset.range (p - 1), cc p (j + 1) * T p (j + 1) := by
    have e1 : ∑ k ∈ Finset.range (p - 1),
        ((p - 1 - 1).choose k : ℚ) ^ 2 * ((p - 1 + k).choose k : ℚ) =
        ∑ k ∈ Finset.range (p - 1 + 1), T2 p k := by
      rw [Finset.sum_range_succ, hlast, add_zero]
      rfl
    rw [e1, Finset.sum_range_succ', hzero, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [T2_cc h5 (by omega : j + 1 < p), pow_one]
  have s := sum_cpp (p : ℚ) (p - 1)
  rw [Finset.sum_range_succ', hc] at s
  have hcpp0 : cpp (p : ℚ) 0 = 0 := by simp [cpp]
  rw [hcpp0, add_zero] at s
  obtain ⟨H', hH', eH⟩ := (W1 h5).exists_eq
  obtain ⟨H2', hH2', eH2⟩ := (W2 h5).exists_eq
  have hA : D p 2 (∑ j ∈ Finset.range (p - 1),
      (cc p (j + 1) * T p (j + 1) - cpp (p : ℚ) (j + 1))) := by
    apply D.sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact cT_D h5 (Nat.succ_pos j) (by omega)
  have hB4 : ((4 : ℕ) : ℚ) * (∑ j ∈ Finset.range (p - 1), cpp (p : ℚ) (j + 1) + 2 + (p : ℚ)) =
      (p : ℚ) ^ 2 * (-6 * H2' - 2 * H' ^ 2 * (p : ℚ) ^ 3 - 2 * H' * (p : ℚ) ^ 3 -
        6 * H' * (p : ℚ) ^ 2 - 8 * H' * (p : ℚ) + 4 * H' + 5 * (p : ℚ) + 7) := by
    rw [s, eH, eH2]
    push_cast
    ring
  have hB : D p 2 (∑ j ∈ Finset.range (p - 1), cpp (p : ℚ) (j + 1) + 2 + (p : ℚ)) := by
    apply D.ucancel (nd4 h5)
    rw [hB4]
    refine (D.ppow 2).mul0 ?_
    repeat' first
      | exact hH' | exact hH2' | exact hP | exact D.one
      | apply D.add | apply D.sub | apply D.mul00 | apply D.pow0 | apply D.neg
      | exact D.ofNat _
  rw [hsum]
  have e : 1 + (p : ℚ) ^ 1 * ∑ j ∈ Finset.range (p - 1), cc p (j + 1) * T p (j + 1) -
      (1 - 2 * (p : ℚ) - (p : ℚ) ^ 2) =
      (p : ℚ) ^ 1 * (∑ j ∈ Finset.range (p - 1),
        (cc p (j + 1) * T p (j + 1) - cpp (p : ℚ) (j + 1)) +
        (∑ j ∈ Finset.range (p - 1), cpp (p : ℚ) (j + 1) + 2 + (p : ℚ))) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  exact ((D.ppow 1).mul (hA.add hB)).le (by norm_num)

end A361717

theorem OMA.solution : type_of% @OMA.S_oeis_a361717.main := by
  refine ⟨?_, ?_⟩
  · intro p hp h5
    have : Fact p.Prime := ⟨hp⟩
    exact A361717.claim1 h5
  · intro p hp h3
    by_cases h5 : 5 ≤ p
    · have : Fact p.Prime := ⟨hp⟩
      exact A361717.claim2 h5
    · have hlt : p < 5 := by omega
      interval_cases p
      · exact absurd hp (by norm_num)
      · exact absurd hp (by norm_num)
      · norm_num [OMA.S_oeis_a361717.a]
      · exact absurd rfl h3
      · exact absurd hp (by norm_num)
