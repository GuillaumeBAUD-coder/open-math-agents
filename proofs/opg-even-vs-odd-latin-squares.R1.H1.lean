import OMAReductions.R_opg_even_vs_odd_latin_squares_R1
import Mathlib

/-!
# Drisko's theorem: Alon–Tarsi conjecture for `n = p + 1` (step H1 of opg-even-vs-odd-latin-squares.R1)

We prove that for every odd prime `p` (given as `m.Prime` with `Even (m + 1)`), the numbers of
even and odd reduced Latin squares of order `p + 1` differ.

Proof outline:
1. Act on the set `R` of reduced Latin squares of order `p + 1` by simultaneous cyclic shift of the
   `p` nonzero indices (identified with `ZMod p`). This action preserves reducedness and `sign`, so
   non-fixed orbits have size `p` and cancel modulo `p`.
2. Every fixed point has `L(x, y) = x + f(y - x)` on `ZMod p` (with `0` fixed at `∞`). Summing
   `f(d) - d` over `d ≠ d0` forces `d0 = 0`, so fixed points correspond bijectively to pairs `(f, g)`
   of permutations of `ZMod p \ {0}` with `f(d) - g(d) = d`, and `sign L = u * sign f * sign g`
   for a fixed unit `u : ℤˣ`.
3. Encoding the bijection condition on `g` via a shifted Vandermonde determinant reduces
   `-∑_{(f, g)} sign f * sign g` modulo `p` to `∑ σ : Perm (Fin (p - 1)), det (CMat σ)`.
4. Expanding `det (CMat σ)` splits into Case 1 (`τ(last) = 0`, contributing `+2`) and Case 2
   (`τ(last) ≠ 0`), where every exponent tuple sums to `p - 1` and its permanent over `S_{p-1}`
   equals `-s⁻¹` (proved by a 5-line induction on the number `s` of positive exponents).
5. Representing `s⁻¹` by the formal integral `I(t^m) = (m + 1)⁻¹` on `Polynomial (ZMod p)` turns
   Case 2 into `-I(det M(t)) = ∑_{r=1}^{p-2} w_r`, where `w` is defined via binomial convolution
   powers of `u = δ - e₋`. A telescoping derivative identity gives `(u ★ w)(p - 1) = 0`, hence
   `∑_{r=1}^{p-2} w_r = -1`, so the total sum is `2 + (-1) = 1 ≠ 0` in `ZMod p`.
-/

namespace DriskoAlonTarsi

open OMA.S_opg_even_vs_odd_latin_squares
open OMA.R_opg_even_vs_odd_latin_squares_R1
open Equiv Finset Matrix Polynomial

/- ### Part 1: Elementary `ZMod p` and binomial helpers -/

private lemma choose_prime_sub_one (p : ℕ) [Fact p.Prime] :
    ∀ k : ℕ, k ≤ p - 1 → ((Nat.choose (p - 1) k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  intro k hk
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  induction k with
  | zero => simp
  | succ k ih =>
    have hk_lt : k < p - 1 := by omega
    have ihk := ih (by omega)
    have hrec : (k + 1) * Nat.choose (p - 1) (k + 1) = (p - 1 - k) * Nat.choose (p - 1) k := by
      have h3 := Nat.choose_succ_right_eq (p - 1) k
      linarith
    have hcast : ((k + 1 : ℕ) : ZMod p) * ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) =
        ((p - 1 - k : ℕ) : ZMod p) * ((Nat.choose (p - 1) k : ℕ) : ZMod p) := by
      have := congrArg (Nat.cast (R := ZMod p)) hrec
      simpa only [Nat.cast_mul] using this
    have hsub : ((p - 1 - k : ℕ) : ZMod p) = -((k + 1 : ℕ) : ZMod p) := by
      have : p - 1 - k + (k + 1) = p := by omega
      have hc : ((p - 1 - k : ℕ) : ZMod p) + ((k + 1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, this, ZMod.natCast_self]
      exact eq_neg_of_add_eq_zero_left hc
    have hkne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [hsub, ihk] at hcast
    have hcast' : ((k + 1 : ℕ) : ZMod p) * ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) =
        ((k + 1 : ℕ) : ZMod p) * (-1 : ZMod p) ^ (k + 1) := by
      rw [hcast, pow_succ]; ring
    exact mul_left_cancel₀ hkne hcast'

private lemma sum_zmod_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    ∑ x : ZMod p, x = 0 := by
  have h1 : ∑ x : ZMod p, x = ∑ x : ZMod p, (-x) :=
    (Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => x)).symm
  have h2 : (2 : ZMod p) * ∑ x : ZMod p, x = 0 := by
    calc (2 : ZMod p) * ∑ x : ZMod p, x
        = (∑ x : ZMod p, x) + (∑ x : ZMod p, (-x)) := by rw [two_mul, ← h1]
      _ = ∑ x : ZMod p, (x + -x) := (Finset.sum_add_distrib).symm
      _ = 0 := by simp
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hp2
  exact (mul_eq_zero.mp h2).resolve_left htwo

private lemma sum_pow_nonzero_eq {p : ℕ} [Fact p.Prime] {a : ℕ} (ha0 : 0 < a) (ha : a < p - 1) :
    ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ a = 0 := by
  have htot : ∑ x : ZMod p, x ^ a = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) a (by rw [ZMod.card]; exact ha)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), zero_pow ha0.ne', zero_add] at htot
  exact htot

private lemma sum_pow_nonzero_sub_one (p : ℕ) [Fact p.Prime] :
    ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ (p - 1) = -1 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  calc ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ (p - 1)
      = ∑ _x ∈ Finset.univ.erase (0 : ZMod p), (1 : ZMod p) :=
        Finset.sum_congr rfl fun x hx => ZMod.pow_card_sub_one_eq_one (Finset.ne_of_mem_erase hx)
    _ = ((p - 1 : ℕ) : ZMod p) := by
        rw [Finset.sum_const, nsmul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ZMod.card]
    _ = -1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]

/- ### Part 2: Binomial convolution and telescoping evaluation of `∑_{r=1}^{p-2} w_r = -1` -/

private def bconv {p : ℕ} (a b : ℕ → ZMod p) (n : ℕ) : ZMod p :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ZMod p) * a k * b (n - k)

private def bdelta (p : ℕ) (n : ℕ) : ZMod p :=
  if n = 0 then 1 else 0

private def bshift {p : ℕ} (a : ℕ → ZMod p) (n : ℕ) : ZMod p := a (n + 1)

private lemma bconv_comm {p : ℕ} (a b : ℕ → ZMod p) : bconv a b = bconv b a := by
  funext n
  unfold bconv
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsub : n - (n - k) = k := Nat.sub_sub_self hkn
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hkn, hsub]
  ring

private lemma bconv_delta_left {p : ℕ} (a : ℕ → ZMod p) : bconv (bdelta p) a = a := by
  funext n
  unfold bconv bdelta
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk0; simp [hk0]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h

private lemma bconv_delta_right {p : ℕ} (a : ℕ → ZMod p) : bconv a (bdelta p) = a := by
  rw [bconv_comm, bconv_delta_left]

private lemma bconv_add_left {p : ℕ} (a b c : ℕ → ZMod p) :
    bconv (fun n => a n + b n) c = fun n => bconv a c n + bconv b c n := by
  funext n; unfold bconv; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma bconv_add_right {p : ℕ} (a b c : ℕ → ZMod p) :
    bconv a (fun n => b n + c n) = fun n => bconv a b n + bconv a c n := by
  funext n; unfold bconv; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma bconv_smul_left {p : ℕ} (c : ZMod p) (a b : ℕ → ZMod p) :
    bconv (fun n => c * a n) b = fun n => c * bconv a b n := by
  funext n; unfold bconv; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma bconv_sub_left {p : ℕ} (a b c : ℕ → ZMod p) :
    bconv (fun n => a n - b n) c = fun n => bconv a c n - bconv b c n := by
  funext n; unfold bconv; rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma bconv_assoc {p : ℕ} (a b c : ℕ → ZMod p) :
    bconv (bconv a b) c = bconv a (bconv b c) := by
  funext n
  unfold bconv
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => ⟨x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨i1, j1⟩ hx1 ⟨i2, j2⟩ hx2 heq
    simp only [Finset.mem_sigma, Finset.mem_range] at hx1 hx2
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    obtain ⟨rfl, h2⟩ := heq
    have hi : i1 = i2 := by omega
    subst hi; rfl
  · rintro ⟨j, k⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    refine ⟨⟨j + k, j⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]; omega
    · exact Sigma.ext rfl (heq_of_eq (by dsimp only; omega))
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have hji : j ≤ i := by omega
    have hin : i ≤ n := by omega
    have hsub : n - j - (i - j) = n - i := by omega
    have hch : Nat.choose n i * Nat.choose i j = Nat.choose n j * Nat.choose (n - j) (i - j) := by
      have hf1 := Nat.choose_mul_factorial_mul_factorial hin
      have hf2 := Nat.choose_mul_factorial_mul_factorial hji
      have hf3 := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ n)
      have hf4 := Nat.choose_mul_factorial_mul_factorial (by omega : i - j ≤ n - j)
      rw [hsub] at hf4
      have hmul : (Nat.choose n i * Nat.choose i j) * (j.factorial * (i - j).factorial * (n - i).factorial) =
          (Nat.choose n j * Nat.choose (n - j) (i - j)) * (j.factorial * (i - j).factorial * (n - i).factorial) := by
        calc (Nat.choose n i * Nat.choose i j) * (j.factorial * (i - j).factorial * (n - i).factorial)
            = Nat.choose n i * (Nat.choose i j * j.factorial * (i - j).factorial) * (n - i).factorial := by ring
          _ = Nat.choose n i * i.factorial * (n - i).factorial := by rw [hf2]
          _ = n.factorial := hf1
          _ = Nat.choose n j * j.factorial * (n - j).factorial := hf3.symm
          _ = Nat.choose n j * j.factorial * (Nat.choose (n - j) (i - j) * (i - j).factorial * (n - i).factorial) := by rw [hf4]
          _ = (Nat.choose n j * Nat.choose (n - j) (i - j)) * (j.factorial * (i - j).factorial * (n - i).factorial) := by ring
      have hpos : 0 < j.factorial * (i - j).factorial * (n - i).factorial := by positivity
      exact Nat.eq_of_mul_eq_mul_right hpos hmul
    have hchZ : (Nat.choose n i : ZMod p) * (Nat.choose i j : ZMod p) =
        (Nat.choose n j : ZMod p) * (Nat.choose (n - j) (i - j) : ZMod p) := by
      have := congrArg (Nat.cast (R := ZMod p)) hch
      simpa only [Nat.cast_mul] using this
    rw [hsub]
    calc (Nat.choose n i : ZMod p) * ((Nat.choose i j : ZMod p) * a j * b (i - j)) * c (n - i)
        = ((Nat.choose n i : ZMod p) * (Nat.choose i j : ZMod p)) * a j * b (i - j) * c (n - i) := by ring
      _ = ((Nat.choose n j : ZMod p) * (Nat.choose (n - j) (i - j) : ZMod p)) * a j * b (i - j) * c (n - i) := by rw [hchZ]
      _ = (Nat.choose n j : ZMod p) * a j * ((Nat.choose (n - j) (i - j) : ZMod p) * b (i - j) * c (n - i)) := by ring

private lemma bshift_bconv {p : ℕ} (a b : ℕ → ZMod p) :
    bshift (bconv a b) = fun n => bconv (bshift a) b n + bconv a (bshift b) n := by
  funext n
  unfold bshift bconv
  rw [Finset.sum_range_succ']
  have h0 : (Nat.choose (n + 1) 0 : ZMod p) * a 0 * b (n + 1 - 0) =
      (Nat.choose n 0 : ZMod p) * a 0 * b (n - 0 + 1) := by simp
  rw [h0]
  have hsplit : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose (n + 1) (k + 1) : ZMod p) * a (k + 1) * b (n + 1 - (k + 1)) =
      (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ZMod p) * a (k + 1) * b (n - k)) +
      (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ZMod p) * a (k + 1) * b (n - k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ, Nat.cast_add, Nat.succ_sub_succ]
    ring
  rw [hsplit]
  have h2 : (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ZMod p) * a (k + 1) * b (n - k)) +
      (Nat.choose n 0 : ZMod p) * a 0 * b (n - 0 + 1) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ZMod p) * a k * b (n - k + 1) := by
    conv_rhs => rw [Finset.sum_range_succ']
    congr 1
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : k < n := Finset.mem_range.mp hk
    have hsub : n - (k + 1) + 1 = n - k := by omega
    rw [hsub]
  rw [add_assoc, h2]

private def bpow {p : ℕ} (a : ℕ → ZMod p) : ℕ → (ℕ → ZMod p)
  | 0 => bdelta p
  | m + 1 => bconv a (bpow a m)

private lemma bpow_succ_right {p : ℕ} (a : ℕ → ZMod p) (m : ℕ) :
    bpow a (m + 1) = bconv (bpow a m) a := by
  rw [bpow, bconv_comm]

private lemma bshift_bpow {p : ℕ} (a : ℕ → ZMod p) (m : ℕ) :
    bshift (bpow a (m + 1)) = fun n => ((m + 1 : ℕ) : ZMod p) * bconv (bshift a) (bpow a m) n := by
  induction m with
  | zero =>
    funext n
    simp [bpow, bconv_delta_right]
  | succ m ih =>
    have h1 : bshift (bpow a (m + 2)) =
        fun n => bconv (bshift a) (bpow a (m + 1)) n + bconv a (bshift (bpow a (m + 1))) n :=
      bshift_bconv a (bpow a (m + 1))
    rw [h1, ih]
    funext n
    have h2 : bconv a (fun k => ((m + 1 : ℕ) : ZMod p) * bconv (bshift a) (bpow a m) k) n =
        ((m + 1 : ℕ) : ZMod p) * bconv (bshift a) (bpow a (m + 1)) n := by
      rw [bconv_comm, bconv_smul_left, bconv_comm]
      dsimp only
      rw [bpow, ← bconv_assoc, bconv_comm a (bshift a), bconv_assoc]
    rw [h2]
    push_cast
    ring

private lemma bpow_eq_zero_of_lt {p : ℕ} {a : ℕ → ZMod p} (ha0 : a 0 = 0) :
    ∀ m n : ℕ, n < m → bpow a m n = 0 := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn
    rw [bpow, bconv]
    refine Finset.sum_eq_zero fun k hk => ?_
    by_cases hk0 : k = 0
    · subst hk0; simp [ha0]
    · have hlt : n - k < m := by
        have := Finset.mem_range.mp hk; omega
      rw [ih (n - k) hlt, mul_zero]

private def bU (p : ℕ) (n : ℕ) : ZMod p :=
  if n = 0 then 0 else -((-1 : ZMod p) ^ n)

private lemma bshift_bU (p : ℕ) :
    bshift (bU p) = fun n => bdelta p n - bU p n := by
  funext n
  unfold bshift bU bdelta
  cases n with
  | zero => simp
  | succ k => simp [pow_succ]

private def bW (p : ℕ) (k : ℕ) : ZMod p :=
  ∑ m ∈ Finset.range (p - 1), (((m + 1 : ℕ) : ZMod p)⁻¹) * bpow (bU p) m k

private lemma sum_bW_eq_neg_one (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) :
    ∑ k ∈ Finset.Ico 1 (p - 1), bW p k = -1 := by
  have hp : 1 < p := by omega
  have hS : ∀ n : ℕ, 1 ≤ n → n ≤ p - 1 →
      bconv (bU p) (bW p) n = if n = 1 then 1 else 0 := by
    intro n hn1 hnp
    have hexp : bconv (bU p) (bW p) = fun k =>
        ∑ m ∈ Finset.range (p - 1), (((m + 1 : ℕ) : ZMod p)⁻¹) * bpow (bU p) (m + 1) k := by
      funext k
      unfold bW bconv
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [bpow, bconv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hshift : bshift (bconv (bU p) (bW p)) (n - 1) =
        bdelta p (n - 1) - bpow (bU p) (p - 1) (n - 1) := by
      rw [hexp]
      change ∑ m ∈ Finset.range (p - 1), (((m + 1 : ℕ) : ZMod p)⁻¹) *
          bshift (bpow (bU p) (m + 1)) (n - 1) = _
      have hterm : ∀ m ∈ Finset.range (p - 1),
          (((m + 1 : ℕ) : ZMod p)⁻¹) * bshift (bpow (bU p) (m + 1)) (n - 1) =
            bpow (bU p) m (n - 1) - bpow (bU p) (m + 1) (n - 1) := by
        intro m hm
        have hmlt : m < p - 1 := Finset.mem_range.mp hm
        have hmne : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
        rw [bshift_bpow, ← mul_assoc, inv_mul_cancel₀ hmne, one_mul, bshift_bU,
          bconv_sub_left, bconv_delta_left]
        rfl
      rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' (fun m => bpow (bU p) m (n - 1)) (p - 1)]
      rfl
    have hzero : bpow (bU p) (p - 1) (n - 1) = 0 :=
      bpow_eq_zero_of_lt (by simp [bU]) (p - 1) (n - 1) (by omega)
    have heq : bconv (bU p) (bW p) n = bshift (bconv (bU p) (bW p)) (n - 1) := by
      unfold bshift; congr 1; omega
    rw [heq, hshift, hzero, sub_zero, bdelta]
    by_cases hn : n = 1
    · subst hn; simp
    · have : n - 1 ≠ 0 := by omega
      simp [hn, this]
  have hconv_zero : bconv (bU p) (bW p) (p - 1) = 0 := by
    rw [hS (p - 1) (by omega) le_rfl, if_neg (by omega)]
  have hconv_sum : bconv (bU p) (bW p) (p - 1) = -∑ k ∈ Finset.range (p - 1), bW p k := by
    rw [bconv_comm, bconv, Finset.sum_range_succ, Nat.sub_self]
    simp only [bU, ↓reduceIte, mul_zero, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : k < p - 1 := Finset.mem_range.mp hk
    have hsubne : p - 1 - k ≠ 0 := by omega
    rw [choose_prime_sub_one p k (by omega)]
    simp only [hsubne, ↓reduceIte]
    have heven : Even (p - 1) := by
      have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
      obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
    have hpow : (-1 : ZMod p) ^ k * -((-1 : ZMod p) ^ (p - 1 - k)) = -1 := by
      rw [mul_neg, ← pow_add, Nat.add_sub_of_le (by omega : k ≤ p - 1), heven.neg_one_pow]
    calc (-1 : ZMod p) ^ k * bW p k * -((-1 : ZMod p) ^ (p - 1 - k))
        = ((-1 : ZMod p) ^ k * -((-1 : ZMod p) ^ (p - 1 - k))) * bW p k := by ring
      _ = -bW p k := by rw [hpow]; ring
  have hsum_zero : ∑ k ∈ Finset.range (p - 1), bW p k = 0 :=
    neg_eq_zero.mp (hconv_sum.symm.trans hconv_zero)
  have hbW0 : bW p 0 = 1 := by
    unfold bW
    rw [Finset.sum_eq_single 0]
    · simp [bpow, bdelta]
    · intro m _ hm0
      rw [bpow_eq_zero_of_lt (by simp [bU]) m 0 (Nat.pos_of_ne_zero hm0), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hsplit : ∑ k ∈ Finset.range (p - 1), bW p k =
      bW p 0 + ∑ k ∈ Finset.Ico 1 (p - 1), bW p k := by
    have hr : Finset.range (p - 1) = insert 0 (Finset.Ico 1 (p - 1)) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hr, Finset.sum_insert (by simp)]
  rw [hsplit, hbW0] at hsum_zero
  exact eq_neg_of_add_eq_zero_right hsum_zero

/- ### Part 3: Permanent of monomials over `S_{p-1}` when `∑ e_k = p - 1` -/

private noncomputable def nzVal (p : ℕ) (i : Fin (p - 1)) : ZMod p := ((i.val + 1 : ℕ) : ZMod p)

private lemma nzVal_ne_zero {p : ℕ} [Fact p.Prime] (i : Fin (p - 1)) : nzVal p i ≠ 0 := by
  unfold nzVal
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

private lemma nzVal_injective {p : ℕ} [Fact p.Prime] : Function.Injective (nzVal p) := by
  intro i j h
  unfold nzVal at h
  have hval : (i.val + 1) % p = (j.val + 1) % p := by
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast] at this
    exact this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hval
  exact Fin.ext (by omega)

private lemma nzVal_range {p : ℕ} [Fact p.Prime] :
    Finset.univ.image (nzVal p) = Finset.univ.erase (0 : ZMod p) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  constructor
  · rintro ⟨i, rfl⟩; exact nzVal_ne_zero i
  · intro hx
    have hval0 : x.val ≠ 0 := fun h => hx (by rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero])
    have hlt : x.val - 1 < p - 1 := by have := x.val_lt; omega
    refine ⟨⟨x.val - 1, hlt⟩, ?_⟩
    unfold nzVal
    have : x.val - 1 + 1 = x.val := by omega
    rw [this, ZMod.natCast_zmod_val]

private lemma sum_inj_prod_pow {p : ℕ} [Fact p.Prime] :
    ∀ (s : ℕ) (a : Fin s → ℕ), 1 ≤ s → (∀ i, 0 < a i) → (∑ i : Fin s, a i = p - 1) →
      ∑ φ : {φ : Fin s → ZMod p // Function.Injective φ ∧ ∀ i, φ i ≠ 0},
          ∏ i : Fin s, (φ.1 i) ^ (a i) =
        (-1 : ZMod p) ^ s * ((s - 1).factorial : ZMod p) := by
  intro s
  induction s with
  | zero => intro _ h; omega
  | succ s ih =>
    intro a _ hpos hsum
    cases s with
    | zero =>
      have ha0 : a 0 = p - 1 := by simpa using hsum
      have heq : ∑ φ : {φ : Fin 1 → ZMod p // Function.Injective φ ∧ ∀ i, φ i ≠ 0},
            ∏ i : Fin 1, (φ.1 i) ^ (a i) =
          ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ (p - 1) := by
        let e : {φ : Fin 1 → ZMod p // Function.Injective φ ∧ ∀ i, φ i ≠ 0} ≃
            {x : ZMod p // x ∈ Finset.univ.erase (0 : ZMod p)} :=
          { toFun := fun φ => ⟨φ.1 0, Finset.mem_erase.mpr ⟨φ.2.2 0, Finset.mem_univ _⟩⟩
            invFun := fun x => ⟨fun _ => x.1, fun i j _ => Subsingleton.elim i j,
              fun _ => (Finset.mem_erase.mp x.2).1⟩
            left_inv := fun φ => Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0])
            right_inv := fun _ => rfl }
        rw [← Finset.sum_coe_sort (Finset.univ.erase (0 : ZMod p)) (fun x => x ^ (p - 1))]
        refine Fintype.sum_equiv e _ _ fun φ => ?_
        simp [e, ha0]
      rw [heq, sum_pow_nonzero_sub_one p]
      simp
    | succ m =>
      -- s + 1 = m + 2 >= 2. Split off the last coordinate `Fin.last (m + 1)`.
      let n1 := m + 1
      let S1 := {ψ : Fin n1 → ZMod p // Function.Injective ψ ∧ ∀ i, ψ i ≠ 0}
      let avail (ψ : S1) : Finset (ZMod p) :=
        (Finset.univ.erase (0 : ZMod p)) \ (Finset.univ.image ψ.1)
      let e : {φ : Fin (n1 + 1) → ZMod p // Function.Injective φ ∧ ∀ i, φ i ≠ 0} ≃
          Σ ψ : S1, {y : ZMod p // y ∈ avail ψ} :=
        { toFun := fun φ =>
            ⟨⟨fun i => φ.1 i.castSucc,
              fun i j h => Fin.castSucc_injective _ (φ.2.1 h),
              fun i => φ.2.2 i.castSucc⟩,
             ⟨φ.1 (Fin.last n1), by
                simp only [avail, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
                  Finset.mem_image, not_exists, not_and]
                exact ⟨φ.2.2 _, fun i _ h => (Fin.castSucc_ne_last i) (φ.2.1 h)⟩⟩⟩
          invFun := fun ⟨ψ, y⟩ =>
            ⟨Fin.snoc ψ.1 y.1,
              by
                intro i j
                refine Fin.lastCases ?_ (fun i' => ?_) i <;>
                  refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro h
                · rfl
                · exfalso
                  simp only [Fin.snoc_last, Fin.snoc_castSucc] at h
                  have hy := (Finset.mem_sdiff.mp y.2).2
                  exact hy (Finset.mem_image.mpr ⟨j', Finset.mem_univ _, h.symm⟩)
                · exfalso
                  simp only [Fin.snoc_last, Fin.snoc_castSucc] at h
                  have hy := (Finset.mem_sdiff.mp y.2).2
                  exact hy (Finset.mem_image.mpr ⟨i', Finset.mem_univ _, h⟩)
                · simp only [Fin.snoc_castSucc] at h
                  exact congrArg Fin.castSucc (ψ.2.1 h),
              fun i => Fin.lastCases (by simpa using (Finset.mem_erase.mp (Finset.mem_sdiff.mp y.2).1).1)
                (fun i' => by simpa using ψ.2.2 i') i⟩
          left_inv := fun φ => Subtype.ext (funext fun i => Fin.lastCases (by simp) (fun i' => by simp) i)
          right_inv := fun ⟨ψ, y⟩ => by
            refine Sigma.ext (Subtype.ext (funext fun i => by simp)) ?_
            dsimp only
            rw [Subtype.heq_iff_coe_eq]
            · simp
            · intro z; simp [avail] }
      have hsum_split : ∑ i : Fin n1, a i.castSucc + a (Fin.last n1) = p - 1 := by
        rw [← Fin.sum_univ_castSucc]; exact hsum
      have halast_lt : a (Fin.last n1) < p - 1 := by
        have hpos0 : 0 < ∑ i : Fin n1, a i.castSucc :=
          Finset.sum_pos (fun i _ => hpos i.castSucc) ⟨⟨0, Nat.succ_pos m⟩, Finset.mem_univ _⟩
        omega
      have havail_sum : ∀ ψ : S1, ∑ y ∈ avail ψ, y ^ (a (Fin.last n1)) =
          -∑ k : Fin n1, (ψ.1 k) ^ (a (Fin.last n1)) := by
        intro ψ
        have hsub : Finset.univ.image ψ.1 ⊆ Finset.univ.erase (0 : ZMod p) := by
          intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_erase.mpr ⟨ψ.2.2 i, Finset.mem_univ _⟩
        have hadd := Finset.sum_sdiff hsub (f := fun y : ZMod p => y ^ (a (Fin.last n1)))
        have htot : ∑ y ∈ Finset.univ.erase (0 : ZMod p), y ^ (a (Fin.last n1)) = 0 :=
          sum_pow_nonzero_eq (hpos (Fin.last n1)) halast_lt
        have himg : ∑ y ∈ Finset.univ.image ψ.1, y ^ (a (Fin.last n1)) =
            ∑ k : Fin n1, (ψ.1 k) ^ (a (Fin.last n1)) :=
          Finset.sum_image fun i _ j _ h => ψ.2.1 h
        rw [htot, himg] at hadd
        exact eq_neg_of_add_eq_zero_left hadd
      calc ∑ φ : {φ : Fin (n1 + 1) → ZMod p // Function.Injective φ ∧ ∀ i, φ i ≠ 0},
              ∏ i : Fin (n1 + 1), (φ.1 i) ^ (a i)
          = ∑ q : Σ ψ : S1, {y : ZMod p // y ∈ avail ψ},
              (∏ i : Fin n1, (q.1.1 i) ^ (a i.castSucc)) * (q.2.1) ^ (a (Fin.last n1)) := by
            refine Fintype.sum_equiv e _ _ fun φ => ?_
            rw [Fin.prod_univ_castSucc]
            rfl
        _ = ∑ ψ : S1, (∏ i : Fin n1, (ψ.1 i) ^ (a i.castSucc)) *
              ∑ y ∈ avail ψ, y ^ (a (Fin.last n1)) := by
            rw [Fintype.sum_sigma]
            refine Finset.sum_congr rfl fun ψ _ => ?_
            dsimp only
            rw [← Finset.mul_sum, Finset.sum_coe_sort (avail ψ) (fun y => y ^ (a (Fin.last n1)))]
        _ = -∑ k : Fin n1, ∑ ψ : S1,
              ∏ i : Fin n1, (ψ.1 i) ^ (if i = k then a i.castSucc + a (Fin.last n1) else a i.castSucc) := by
            simp_rw [havail_sum, mul_neg, Finset.sum_neg_distrib]
            congr 1
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ψ _ => ?_
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
            conv_rhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
            simp only [↓reduceIte, pow_add]
            have herase : ∏ x ∈ Finset.univ.erase k,
                (ψ.1 x) ^ (if x = k then a x.castSucc + a (Fin.last n1) else a x.castSucc) =
                ∏ x ∈ Finset.univ.erase k, (ψ.1 x) ^ (a x.castSucc) :=
              Finset.prod_congr rfl fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)]
            rw [herase]; ring
        _ = -∑ _k : Fin n1, ((-1 : ZMod p) ^ n1 * ((n1 - 1).factorial : ZMod p)) := by
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            refine ih (fun i => if i = k then a i.castSucc + a (Fin.last n1) else a i.castSucc)
              (by omega) (fun i => by split_ifs <;> [exact Nat.add_pos_left (hpos _) _; exact hpos _]) ?_
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), if_pos rfl]
            have herase : ∑ i ∈ Finset.univ.erase k,
                (if i = k then a i.castSucc + a (Fin.last n1) else a i.castSucc) =
                ∑ i ∈ Finset.univ.erase k, a i.castSucc :=
              Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)]
            rw [herase, add_right_comm,
              Finset.add_sum_erase Finset.univ (fun i : Fin n1 => a i.castSucc) (Finset.mem_univ k),
              hsum_split]
        _ = (-1 : ZMod p) ^ (n1 + 1) * ((n1).factorial : ZMod p) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have hfac : n1 * (n1 - 1).factorial = n1.factorial := by
              dsimp only [n1]; simp [Nat.factorial_succ]
            have hfacZ : (n1 : ZMod p) * ((n1 - 1).factorial : ZMod p) = (n1.factorial : ZMod p) := by
              have := congrArg (Nat.cast (R := ZMod p)) hfac
              simpa only [Nat.cast_mul] using this
            calc -((n1 : ZMod p) * ((-1 : ZMod p) ^ n1 * ((n1 - 1).factorial : ZMod p)))
                = (-1 : ZMod p) ^ n1 * -1 * ((n1 : ZMod p) * ((n1 - 1).factorial : ZMod p)) := by ring
              _ = (-1 : ZMod p) ^ n1 * -1 * (n1.factorial : ZMod p) := by rw [hfacZ]
              _ = (-1 : ZMod p) ^ (n1 + 1) * (n1.factorial : ZMod p) := by
                rw [show (-1 : ZMod p) ^ (n1 + 1) = (-1 : ZMod p) ^ n1 * -1 from pow_succ _ _]

private lemma sum_perm_prod_pow {p : ℕ} [Fact p.Prime] (e : Fin (p - 1) → ℕ)
    (hsum : ∑ k : Fin (p - 1), e k = p - 1) :
    ∑ σ : Equiv.Perm (Fin (p - 1)), ∏ k : Fin (p - 1), (nzVal p (σ k)) ^ (e k) =
      -(((Finset.univ.filter fun k : Fin (p - 1) => 0 < e k).card : ZMod p)⁻¹) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  let S := Finset.univ.filter fun k : Fin (p - 1) => 0 < e k
  let s := S.card
  have hs_pos : 1 ≤ s := by
    by_contra! h0
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    have hall0 : ∀ k : Fin (p - 1), e k = 0 := fun k => by
      by_contra hne
      have : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, Nat.pos_of_ne_zero hne⟩
      rw [hS0] at this; exact Finset.notMem_empty k this
    have : ∑ k : Fin (p - 1), e k = 0 := Finset.sum_eq_zero fun k _ => hall0 k
    omega
  have hs_le : s ≤ p - 1 := by
    calc s = S.card := rfl
      _ ≤ Finset.univ.card := Finset.card_le_univ S
      _ = p - 1 := Fintype.card_fin _
  let eS : Fin s ≃ {k : Fin (p - 1) // k ∈ S} := (Finset.equivFin S).symm
  let InjType := {φ : Fin s → Fin (p - 1) // Function.Injective φ}
  let restrictPerm (σ : Equiv.Perm (Fin (p - 1))) : InjType :=
    ⟨fun i => σ (eS i).1, σ.injective.comp (Subtype.val_injective.comp eS.injective)⟩
  have hprod_eq : ∀ σ : Equiv.Perm (Fin (p - 1)),
      ∏ k : Fin (p - 1), (nzVal p (σ k)) ^ (e k) =
        ∏ i : Fin s, (nzVal p ((restrictPerm σ).1 i)) ^ (e (eS i).1) := by
    intro σ
    calc ∏ k : Fin (p - 1), (nzVal p (σ k)) ^ (e k)
        = ∏ k ∈ S, (nzVal p (σ k)) ^ (e k) := by
          symm
          refine Finset.prod_subset (Finset.subset_univ S) fun k _ hk => ?_
          have he0 : e k = 0 := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hk
            exact hk
          rw [he0, pow_zero]
      _ = ∏ k : {k : Fin (p - 1) // k ∈ S}, (nzVal p (σ k.1)) ^ (e k.1) :=
          (Finset.prod_coe_sort S _).symm
      _ = ∏ i : Fin s, (nzVal p (σ (eS i).1)) ^ (e (eS i).1) :=
          (Fintype.prod_equiv eS _ _ (fun _ => rfl)).symm
  have hfiber : ∀ φ : InjType,
      Fintype.card {σ : Equiv.Perm (Fin (p - 1)) // restrictPerm σ = φ} = (p - 1 - s).factorial := by
    intro φ
    let T := Finset.univ.image φ.1
    have hTcard : T.card = s := by
      rw [Finset.card_image_of_injective _ φ.2, Finset.card_univ, Fintype.card_fin]
    have hSc_card : Fintype.card {k : Fin (p - 1) // k ∉ S} = p - 1 - s := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have hTc_card : Fintype.card {y : Fin (p - 1) // y ∉ T} = p - 1 - s := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hTcard]
    let eST : {k : Fin (p - 1) // k ∈ S} ≃ {y : Fin (p - 1) // y ∈ T} :=
      { toFun := fun k => ⟨φ.1 (eS.symm k), Finset.mem_image.mpr ⟨eS.symm k, Finset.mem_univ _, rfl⟩⟩
        invFun := fun y => eS (Classical.choose (Finset.mem_image.mp y.2))
        left_inv := fun k => by
          dsimp only
          have hmem : φ.1 (eS.symm k) ∈ T := Finset.mem_image.mpr ⟨eS.symm k, Finset.mem_univ _, rfl⟩
          have hch := (Classical.choose_spec (Finset.mem_image.mp hmem)).2
          rw [φ.2 hch, eS.apply_symm_apply]
        right_inv := fun y => Subtype.ext (by
          dsimp only
          rw [eS.symm_apply_apply]
          exact (Classical.choose_spec (Finset.mem_image.mp y.2)).2) }
    let eFib : {σ : Equiv.Perm (Fin (p - 1)) // restrictPerm σ = φ} ≃
        ({k : Fin (p - 1) // k ∉ S} ≃ {y : Fin (p - 1) // y ∉ T}) :=
      { toFun := fun σ =>
          { toFun := fun k => ⟨σ.1 k.1, by
              intro hmem
              obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
              have h1 : σ.1 (eS i).1 = φ.1 i := congrFun (congrArg Subtype.val σ.2) i
              have : k.1 = (eS i).1 := σ.1.injective (hi.symm.trans h1.symm)
              exact k.2 (this ▸ (eS i).2)⟩
            invFun := fun y => ⟨σ.1.symm y.1, by
              intro hmem
              have h1 : σ.1 (σ.1.symm y.1) = φ.1 (eS.symm ⟨σ.1.symm y.1, hmem⟩) := by
                have := congrFun (congrArg Subtype.val σ.2) (eS.symm ⟨σ.1.symm y.1, hmem⟩)
                dsimp only [restrictPerm] at this
                simpa using this
              rw [Equiv.apply_symm_apply] at h1
              exact y.2 (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h1.symm⟩)⟩
            left_inv := fun k => Subtype.ext (σ.1.symm_apply_apply k.1)
            right_inv := fun y => Subtype.ext (σ.1.apply_symm_apply y.1) }
        invFun := fun τ =>
          ⟨(Equiv.sumCompl (· ∈ S)).symm.trans ((Equiv.sumCongr eST τ).trans (Equiv.sumCompl (· ∈ T))),
            Subtype.ext (funext fun i => by
              change ((Equiv.sumCompl (· ∈ T)) ((Equiv.sumCongr eST τ)
                ((Equiv.sumCompl (· ∈ S)).symm (eS i).1))) = φ.1 i
              have h1 : (Equiv.sumCompl (· ∈ S)).symm (eS i).1 = Sum.inl (eS i) := by
                apply (Equiv.sumCompl (· ∈ S)).injective
                simp
              rw [h1]
              simp [eST])⟩
        left_inv := fun σ => by
          apply Subtype.ext; apply Equiv.ext; intro k
          by_cases hk : k ∈ S
          · have h1 : (Equiv.sumCompl (· ∈ S)).symm k = Sum.inl ⟨k, hk⟩ := by
              apply (Equiv.sumCompl (· ∈ S)).injective; simp
            have h2 : σ.1 k = φ.1 (eS.symm ⟨k, hk⟩) := by
              have := congrFun (congrArg Subtype.val σ.2) (eS.symm ⟨k, hk⟩)
              dsimp only [restrictPerm] at this
              simpa using this
            change (Equiv.sumCompl (· ∈ T)) ((Equiv.sumCongr eST _)
              ((Equiv.sumCompl (· ∈ S)).symm k)) = σ.1 k
            rw [h1]; simp [eST, h2]
          · have h1 : (Equiv.sumCompl (· ∈ S)).symm k = Sum.inr ⟨k, hk⟩ := by
              apply (Equiv.sumCompl (· ∈ S)).injective; simp
            change (Equiv.sumCompl (· ∈ T)) ((Equiv.sumCongr eST _)
              ((Equiv.sumCompl (· ∈ S)).symm k)) = σ.1 k
            rw [h1]; simp
        right_inv := fun τ => by
          apply Equiv.ext; intro k; apply Subtype.ext
          have h1 : (Equiv.sumCompl (· ∈ S)).symm k.1 = Sum.inr k := by
            apply (Equiv.sumCompl (· ∈ S)).injective; simp
          change (Equiv.sumCompl (· ∈ T)) ((Equiv.sumCongr eST τ)
            ((Equiv.sumCompl (· ∈ S)).symm k.1)) = (τ k).1
          rw [h1]; simp }
    rw [Fintype.card_congr eFib]
    have eEq : ({k : Fin (p - 1) // k ∉ S} ≃ {y : Fin (p - 1) // y ∉ T}) ≃
        Equiv.Perm (Fin (p - 1 - s)) :=
      Equiv.equivCongr (Fintype.equivFinOfCardEq hSc_card) (Fintype.equivFinOfCardEq hTc_card)
    rw [Fintype.card_congr eEq, Fintype.card_perm, Fintype.card_fin]
  let hInjEquiv : InjType ≃ {φ : Fin s → ZMod p // Function.Injective φ ∧ ∀ i, φ i ≠ 0} :=
    { toFun := fun φ => ⟨fun i => nzVal p (φ.1 i), nzVal_injective.comp φ.2, fun i => nzVal_ne_zero _⟩
      invFun := fun ψ =>
        ⟨fun i => Classical.choose (Finset.mem_image.mp ((nzVal_range (p := p)) ▸
            Finset.mem_erase.mpr ⟨ψ.2.2 i, Finset.mem_univ _⟩)),
          fun i j h => by
            have hi := (Classical.choose_spec (Finset.mem_image.mp ((nzVal_range (p := p)) ▸
              Finset.mem_erase.mpr ⟨ψ.2.2 i, Finset.mem_univ _⟩))).2
            have hj := (Classical.choose_spec (Finset.mem_image.mp ((nzVal_range (p := p)) ▸
              Finset.mem_erase.mpr ⟨ψ.2.2 j, Finset.mem_univ _⟩))).2
            exact ψ.2.1 (hi.symm.trans ((congrArg (nzVal p) h).trans hj))⟩
      left_inv := fun φ => Subtype.ext (funext fun i => by
        have hi := (Classical.choose_spec (Finset.mem_image.mp ((nzVal_range (p := p)) ▸
          Finset.mem_erase.mpr ⟨nzVal_ne_zero (φ.1 i), Finset.mem_univ _⟩))).2
        exact nzVal_injective hi)
      right_inv := fun ψ => Subtype.ext (funext fun i =>
        (Classical.choose_spec (Finset.mem_image.mp ((nzVal_range (p := p)) ▸
          Finset.mem_erase.mpr ⟨ψ.2.2 i, Finset.mem_univ _⟩))).2) }
  have hsum_a : ∑ i : Fin s, e (eS i).1 = p - 1 := by
    rw [Fintype.sum_equiv eS _ (fun k : {k : Fin (p - 1) // k ∈ S} => e k.1) (fun _ => rfl),
      Finset.sum_coe_sort]
    calc ∑ k ∈ S, e k = ∑ k : Fin (p - 1), e k :=
          Finset.sum_subset (Finset.subset_univ S) fun k _ hk => by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hk
            exact hk
      _ = p - 1 := hsum
  have hpos_a : ∀ i : Fin s, 0 < e (eS i).1 := fun i => (Finset.mem_filter.mp (eS i).2).2
  have hmain : ∑ σ : Equiv.Perm (Fin (p - 1)), ∏ k : Fin (p - 1), (nzVal p (σ k)) ^ (e k) =
      ((p - 1 - s).factorial : ZMod p) * ((-1 : ZMod p) ^ s * ((s - 1).factorial : ZMod p)) := by
    calc ∑ σ : Equiv.Perm (Fin (p - 1)), ∏ k : Fin (p - 1), (nzVal p (σ k)) ^ (e k)
        = ∑ σ : Equiv.Perm (Fin (p - 1)), ∏ i : Fin s, (nzVal p ((restrictPerm σ).1 i)) ^ (e (eS i).1) :=
          Finset.sum_congr rfl fun σ _ => hprod_eq σ
      _ = ∑ φ : InjType, ∑ _σ : {σ : Equiv.Perm (Fin (p - 1)) // restrictPerm σ = φ},
            ∏ i : Fin s, (nzVal p (φ.1 i)) ^ (e (eS i).1) := by
          rw [← Fintype.sum_fiberwise restrictPerm]
          refine Finset.sum_congr rfl fun φ _ => Finset.sum_congr rfl fun σ _ => ?_
          rw [σ.2]
      _ = ((p - 1 - s).factorial : ZMod p) *
            ∑ φ : InjType, ∏ i : Fin s, (nzVal p (φ.1 i)) ^ (e (eS i).1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun φ _ => ?_
          rw [Finset.sum_const, Finset.card_univ, hfiber φ, nsmul_eq_mul]
      _ = ((p - 1 - s).factorial : ZMod p) *
            ∑ ψ : {ψ : Fin s → ZMod p // Function.Injective ψ ∧ ∀ i, ψ i ≠ 0},
              ∏ i : Fin s, (ψ.1 i) ^ (e (eS i).1) := by
          congr 1
          refine Fintype.sum_equiv hInjEquiv _ _ fun φ => ?_
          rfl
      _ = ((p - 1 - s).factorial : ZMod p) * ((-1 : ZMod p) ^ s * ((s - 1).factorial : ZMod p)) := by
          rw [sum_inj_prod_pow s (fun i => e (eS i).1) hs_pos hpos_a hsum_a]
  rw [hmain]
  have hs_ne : (s : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hfac_s : s * (s - 1).factorial = s.factorial := Nat.mul_factorial_pred (by omega)
  have hmul : (s : ZMod p) *
      (((p - 1 - s).factorial : ZMod p) * ((-1 : ZMod p) ^ s * ((s - 1).factorial : ZMod p))) = -1 := by
    rw [← choose_prime_sub_one p s hs_le]
    have hnat : Nat.choose (p - 1) s * (s * (s - 1).factorial) * (p - 1 - s).factorial = (p - 1).factorial := by
      rw [hfac_s]
      exact Nat.choose_mul_factorial_mul_factorial hs_le
    have hZ : ((Nat.choose (p - 1) s : ℕ) : ZMod p) * ((s : ZMod p) * ((s - 1).factorial : ZMod p)) *
        ((p - 1 - s).factorial : ZMod p) = ((p - 1).factorial : ZMod p) := by
      have := congrArg (Nat.cast (R := ZMod p)) hnat
      simpa only [Nat.cast_mul] using this
    rw [ZMod.wilsons_lemma] at hZ
    linear_combination hZ
  have hmul' : (s : ZMod p) *
      (((p - 1 - s).factorial : ZMod p) * ((-1 : ZMod p) ^ s * ((s - 1).factorial : ZMod p))) =
      (s : ZMod p) * -((s : ZMod p)⁻¹) := by
    rw [hmul, mul_neg, mul_inv_cancel₀ hs_ne]
  exact mul_left_cancel₀ hs_ne hmul'

/- ### Part 4: Formal integral, matrix `M(t)`, and `∑ σ, det (CMat σ) = 1` -/

private noncomputable def polyInt (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) →ₗ[ZMod p] ZMod p where
  toFun f := f.sum fun m c => c * (((m + 1 : ℕ) : ZMod p)⁻¹)
  map_add' f g := Polynomial.sum_add_index f g _ (fun _ => by simp) (fun _ _ _ => by ring)
  map_smul' r f := by
    simp only [Polynomial.sum_def, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    by_cases hr : r = 0
    · simp [hr]
    · have hsupp : (r • f).support = f.support := by
        ext m
        simp only [Polynomial.mem_support_iff, Polynomial.coeff_smul, smul_eq_mul, ne_eq,
          mul_eq_zero, hr, false_or]
      rw [hsupp]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Polynomial.coeff_smul, smul_eq_mul, mul_assoc]

private lemma polyInt_monomial (p : ℕ) [Fact p.Prime] (m : ℕ) (c : ZMod p) :
    polyInt p (Polynomial.monomial m c) = c * (((m + 1 : ℕ) : ZMod p)⁻¹) := by
  change (Polynomial.monomial m c).sum (fun k a => a * (((k + 1 : ℕ) : ZMod p)⁻¹)) = _
  exact Polynomial.sum_monomial_index (n := m) (a := c)
    (f := fun k a => a * (((k + 1 : ℕ) : ZMod p)⁻¹)) (hf := zero_mul _)

private lemma polyInt_C_mul_X_pow (p : ℕ) [Fact p.Prime] (m : ℕ) (c : ZMod p) :
    polyInt p (Polynomial.C c * Polynomial.X ^ m) = c * (((m + 1 : ℕ) : ZMod p)⁻¹) := by
  rw [Polynomial.C_mul_X_pow_eq_monomial, polyInt_monomial]

private noncomputable def vPoly (p r : ℕ) : Polynomial (ZMod p) :=
  ∑ m ∈ Finset.range (p - 1), Polynomial.C (bpow (bU p) m r) * Polynomial.X ^ m

private lemma polyInt_vPoly (p : ℕ) [Fact p.Prime] (r : ℕ) : polyInt p (vPoly p r) = bW p r := by
  unfold vPoly bW
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [polyInt_C_mul_X_pow, mul_comm]

private lemma vPoly_zero (p : ℕ) (hp : 1 < p) : vPoly p 0 = 1 := by
  unfold vPoly
  rw [Finset.sum_eq_single 0]
  · simp [bpow, bdelta]
  · intro m _ hm0
    rw [bpow_eq_zero_of_lt (by simp [bU]) m 0 (Nat.pos_of_ne_zero hm0), map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private noncomputable def MMat (p : ℕ) : Matrix (Fin (p - 1)) (Fin (p - 1)) (Polynomial (ZMod p)) :=
  Matrix.of fun k r =>
    if k.val < p - 2 then
      if r.val = k.val + 1 then 1
      else if r.val < k.val + 1 then
        Polynomial.C (((Nat.choose (k.val + 1) r.val : ℕ) : ZMod p) * (-1 : ZMod p) ^ (k.val + 1 - r.val)) * Polynomial.X
      else 0
    else
      if r.val = 0 then 0 else 1

private lemma MMat_mul_vPoly_zero {p : ℕ} (hp2 : 2 < p) (k : Fin (p - 1)) (hk : k.val < p - 2) :
    ∑ r : Fin (p - 1), MMat p k r * vPoly p r.val = 0 := by
  let K := k.val + 1
  have hK_pos : 1 ≤ K := by omega
  have hK_lt : K < p - 1 := by omega
  ext m
  rw [Polynomial.coeff_zero, Polynomial.finsetSum_coeff]
  have hcoeff_v : ∀ r m, (vPoly p r).coeff m = if m < p - 1 then bpow (bU p) m r else 0 := by
    intro r m
    unfold vPoly
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    by_cases hm : m < p - 1
    · rw [Finset.sum_eq_single m]
      · simp [hm]
      · intro j _ hjm; simp [Ne.symm hjm]
      · intro h; exact absurd (Finset.mem_range.mpr hm) h
    · rw [if_neg hm]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjlt : j < p - 1 := Finset.mem_range.mp hj
      have : m ≠ j := by omega
      simp [this]
  have hterm : ∀ r : Fin (p - 1), (MMat p k r * vPoly p r.val).coeff m =
      if r.val = K then (vPoly p K).coeff m
      else if r.val < K then
        ((Nat.choose K r.val : ℕ) : ZMod p) * (-1 : ZMod p) ^ (K - r.val) *
          (if m = 0 then 0 else (vPoly p r.val).coeff (m - 1))
      else 0 := by
    intro r
    unfold MMat
    simp only [Matrix.of_apply, hk, ↓reduceIte]
    by_cases h1 : r.val = K
    · dsimp only [K] at h1 ⊢
      simp only [h1, ↓reduceIte, one_mul]
    · by_cases h2 : r.val < K
      · dsimp only [K] at h1 h2 ⊢
        simp only [h1, h2, ↓reduceIte]
        rw [mul_assoc, Polynomial.coeff_C_mul]
        cases m with
        | zero => simp
        | succ m' => simp [Polynomial.coeff_X_mul]
      · dsimp only [K] at h1 h2 ⊢
        simp only [h1, h2, ↓reduceIte, zero_mul, Polynomial.coeff_zero]
  simp_rw [hterm]
  cases m with
  | zero =>
    have hK_fin : (⟨K, hK_lt⟩ : Fin (p - 1)) ∈ Finset.univ := Finset.mem_univ _
    rw [Finset.sum_eq_single ⟨K, hK_lt⟩]
    · simp only [↓reduceIte, hcoeff_v, show (0 : ℕ) < p - 1 by omega, bpow, bdelta,
        show K ≠ 0 by omega]
    · intro r _ hrne
      have hrneK : r.val ≠ K := fun h => hrne (Fin.ext h)
      simp [hrneK]
    · intro h; exact absurd hK_fin h
  | succ m' =>
    by_cases hm : m' + 1 < p - 1
    · have hm' : m' < p - 1 := by omega
      have hsplit : ∑ r : Fin (p - 1),
          (if r.val = K then (vPoly p K).coeff (m' + 1)
           else if r.val < K then
             ((Nat.choose K r.val : ℕ) : ZMod p) * (-1 : ZMod p) ^ (K - r.val) *
               (if m' + 1 = 0 then 0 else (vPoly p r.val).coeff (m' + 1 - 1))
           else 0) =
          bpow (bU p) (m' + 1) K +
            ∑ r ∈ Finset.range K, ((Nat.choose K r : ℕ) : ZMod p) * (-1 : ZMod p) ^ (K - r) *
              bpow (bU p) m' r := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨K, hK_lt⟩ : Fin (p - 1)))]
        simp only [↓reduceIte, hcoeff_v, hm, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          Nat.add_sub_cancel]
        congr 1
        refine Finset.sum_bij_ne_zero (fun r _ _ => r.val) ?_ ?_ ?_ ?_
        · intro r hr hne
          have hrne : r.val ≠ K := fun h => (Finset.ne_of_mem_erase hr) (Fin.ext h)
          simp only [hrne, ↓reduceIte] at hne
          by_contra hnot
          have : ¬ r.val < K := by simpa [Finset.mem_range] using hnot
          exact hne (by simp [this])
        · intro r1 _ _ r2 _ _ h; exact Fin.ext h
        · intro j hj hne
          have hjlt : j < K := Finset.mem_range.mp hj
          refine ⟨⟨j, by omega⟩, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; dsimp at this; omega, Finset.mem_univ _⟩, ?_, rfl⟩
          simp only [show j ≠ K by omega, ↓reduceIte, hjlt, hm']
          exact hne
        · intro r hr hne
          have hrne : r.val ≠ K := fun h => (Finset.ne_of_mem_erase hr) (Fin.ext h)
          have hrlt : r.val < K := by
            by_contra hnot
            simp only [hrne, ↓reduceIte, hnot] at hne
            exact hne rfl
          simp [hrne, hrlt, hm']
      rw [hsplit, bpow_succ_right, bconv, Finset.sum_range_succ, Nat.sub_self]
      simp only [bU, ↓reduceIte, mul_zero, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hrlt : r < K := Finset.mem_range.mp hr
      have hsubne : K - r ≠ 0 := by omega
      simp only [hsubne, ↓reduceIte]
      ring
    · refine Finset.sum_eq_zero fun r _ => ?_
      by_cases h1 : r.val = K
      · simp only [h1, ↓reduceIte, hcoeff_v, hm]
      · by_cases h2 : r.val < K
        · simp only [h1, h2, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            Nat.add_sub_cancel, hcoeff_v]
          by_cases hm' : m' < p - 1
          · rw [if_pos hm', bpow_eq_zero_of_lt (by simp [bU]) m' r.val (by omega), mul_zero]
          · rw [if_neg hm', mul_zero]
        · simp only [h1, h2, ↓reduceIte]

private lemma det_MMat (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) :
    (MMat p).det = -∑ r ∈ Finset.Ico 1 (p - 1), vPoly p r := by
  have hp : 1 < p := by omega
  let m := p - 1
  have hm_ge2 : 2 ≤ m := by omega
  have hm_even : Even m := by
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  let U : Matrix (Fin m) (Fin m) (Polynomial (ZMod p)) :=
    Matrix.of fun i j => if i = j then 1 else if j.val = 0 then vPoly p i.val else 0
  have hU_lower : U.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.val < j.val := hij
    have hne : i ≠ j := fun h => by subst h; omega
    have hj0 : j.val ≠ 0 := by omega
    simp [U, hne, hj0]
  have hU_det : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U hU_lower]
    refine Finset.prod_eq_one fun i _ => by simp [U]
  -- Product P := MMat p * U
  let P : Matrix (Fin m) (Fin m) (Polynomial (ZMod p)) := MMat p * U
  have hP_col0 : ∀ k : Fin m, P k ⟨0, by omega⟩ =
      if k.val < p - 2 then 0 else ∑ r ∈ Finset.Ico 1 (p - 1), vPoly p r := by
    intro k
    have hU0 : ∀ r : Fin m, U r ⟨0, by omega⟩ = vPoly p r.val := by
      intro r
      unfold U
      simp only [Matrix.of_apply]
      by_cases hr0 : r = ⟨0, by omega⟩
      · subst hr0; simp [vPoly_zero p hp]
      · simp [hr0]
    calc P k ⟨0, by omega⟩
        = ∑ r : Fin m, MMat p k r * U r ⟨0, by omega⟩ := rfl
      _ = ∑ r : Fin m, MMat p k r * vPoly p r.val :=
          Finset.sum_congr rfl fun r _ => by rw [hU0 r]
      _ = if k.val < p - 2 then 0 else ∑ r ∈ Finset.Ico 1 (p - 1), vPoly p r := by
          split_ifs with hk
          · exact MMat_mul_vPoly_zero hp2 k hk
          · have hlast : ∀ r : Fin m, MMat p k r = if r.val = 0 then 0 else 1 := fun r => by
              simp [MMat, hk]
            simp_rw [hlast]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, by omega⟩ : Fin m))]
            simp only [↓reduceIte, zero_mul, zero_add]
            refine Finset.sum_bij (fun r _ => r.val) ?_ ?_ ?_ ?_
            · intro r hr
              have hrne : r.val ≠ 0 := fun h => (Finset.ne_of_mem_erase hr) (Fin.ext h)
              simp only [Finset.mem_Ico]; omega
            · intro r1 _ r2 _ h; exact Fin.ext h
            · intro j hj
              simp only [Finset.mem_Ico] at hj
              refine ⟨⟨j, by omega⟩, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; dsimp at this; omega, Finset.mem_univ _⟩, rfl⟩
            · intro r hr
              have hrne : r.val ≠ 0 := fun h => (Finset.ne_of_mem_erase hr) (Fin.ext h)
              simp [hrne]
  have hP_poscol : ∀ (k j : Fin m), j.val ≠ 0 → P k j = MMat p k j := by
    intro k j hj0
    calc P k j = ∑ r : Fin m, MMat p k r * U r j := rfl
      _ = MMat p k j * U j j := by
          rw [Finset.sum_eq_single j]
          · intro r _ hrj; simp [U, hrj, hj0]
          · intro h; exact absurd (Finset.mem_univ j) h
      _ = MMat p k j := by simp [U]
  -- Cyclically shift row `m - 1` to row `0`: ρ(0) = m - 1, ρ(i + 1) = i.
  -- Equiv: Fin (p - 1) ≃ Fin ((p - 2) + 1)
  let q := p - 2
  have hmq : m = q + 1 := by omega
  let eFin : Fin (q + 1) ≃ Fin m := finCongr hmq.symm
  let ρ : Equiv.Perm (Fin (q + 1)) :=
    { toFun := fun i => if h : i.val = 0 then Fin.last q else ⟨i.val - 1, by omega⟩
      invFun := fun i => if h : i.val = q then 0 else ⟨i.val + 1, by omega⟩
      left_inv := fun i => by
        by_cases h : i.val = 0
        · simp [h, Fin.last]; exact Fin.ext h.symm
        · have : i.val - 1 ≠ q := by omega
          simp [h, this]; ext; dsimp; omega
      right_inv := fun i => by
        by_cases h : i.val = q
        · simp [h, Fin.last]; ext; exact h.symm
        · simp [h] }
  have hρ_sign : (Equiv.Perm.sign ρ : Polynomial (ZMod p)) = -1 := by
    -- ρ is the inverse of Fin.cycleRange (Fin.last q), which has sign (-1)^q = -1 since q = p - 2 is odd!
    have hρ_eq : ρ.symm = Fin.cycleRange (Fin.last q) := by
      apply Equiv.ext
      intro i
      change (if h : i.val = q then (0 : Fin (q + 1)) else ⟨i.val + 1, by omega⟩) =
        Fin.cycleRange (Fin.last q) i
      by_cases h : i = Fin.last q
      · subst h; simp [Fin.last]
      · have hne : i.val ≠ q := fun hv => h (Fin.ext hv)
        have hlt : i < Fin.last q := lt_of_le_of_ne (Fin.le_last i) h
        rw [dif_neg hne, Fin.cycleRange_of_lt hlt]
        ext; exact (Fin.val_add_one_of_lt hlt).symm
    have hsign_symm : Equiv.Perm.sign ρ = Equiv.Perm.sign ρ.symm := by
      change Equiv.Perm.sign ρ = Equiv.Perm.sign ρ⁻¹
      rw [map_inv]
      exact (inv_eq_of_mul_eq_one_right (Int.units_mul_self _)).symm
    rw [hsign_symm, hρ_eq, Fin.sign_cycleRange]
    have hq_odd : Odd q := by
      obtain ⟨t, ht⟩ := hm_even
      exact ⟨t - 1, by omega⟩
    simp [hq_odd.neg_one_pow]
  let Q : Matrix (Fin (q + 1)) (Fin (q + 1)) (Polynomial (ZMod p)) :=
    (P.submatrix eFin eFin).submatrix ρ id
  have hQ_det : Q.det = (Equiv.Perm.sign ρ : Polynomial (ZMod p)) * P.det := by
    rw [Matrix.det_permute]
    congr 1
    exact Matrix.det_reindex_self eFin.symm P
  have hQ_col0 : ∀ i : Fin (q + 1), Q i 0 =
      if i = 0 then ∑ r ∈ Finset.Ico 1 (p - 1), vPoly p r else 0 := by
    intro i
    change P (eFin (ρ i)) (eFin 0) = _
    have he0 : eFin 0 = ⟨0, by omega⟩ := Fin.ext rfl
    rw [he0, hP_col0]
    by_cases hi : i = 0
    · subst hi
      have hρ0 : (eFin (ρ 0)).val = q := by simp [ρ, eFin, Fin.last]
      have hnot : ¬ (eFin (ρ 0)).val < p - 2 := by omega
      simp [hnot]
    · have hρi : (eFin (ρ i)).val = i.val - 1 := by simp [ρ, eFin, hi]
      have hlt : (eFin (ρ i)).val < p - 2 := by omega
      simp [hi, hlt]
  have hQ_sub_det : (Q.submatrix Fin.succ Fin.succ).det = 1 := by
    have hlt : (Q.submatrix Fin.succ Fin.succ).BlockTriangular OrderDual.toDual := by
      intro i j hij
      have hlt_ij : i.val < j.val := hij
      change P (eFin (ρ i.succ)) (eFin j.succ) = 0
      have hj0 : (eFin j.succ).val ≠ 0 := by simp [eFin]
      rw [hP_poscol _ _ hj0]
      have hρi : (eFin (ρ i.succ)).val = i.val := by simp [ρ, eFin]
      have hej : (eFin j.succ).val = j.val + 1 := by simp [eFin]
      unfold MMat
      simp only [Matrix.of_apply, hρi, hej]
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    rw [Matrix.det_of_isLowerTriangular _ hlt]
    refine Finset.prod_eq_one fun i _ => ?_
    change P (eFin (ρ i.succ)) (eFin i.succ) = 1
    have hi0 : (eFin i.succ).val ≠ 0 := by simp [eFin]
    rw [hP_poscol _ _ hi0]
    have hρi : (eFin (ρ i.succ)).val = i.val := by simp [ρ, eFin]
    have hei : (eFin i.succ).val = i.val + 1 := by simp [eFin]
    unfold MMat
    simp only [Matrix.of_apply, hρi, hei, show i.val < p - 2 by omega, ↓reduceIte]
  have hQ_val : Q.det = ∑ r ∈ Finset.Ico 1 (p - 1), vPoly p r := by
    rw [Matrix.det_succ_column_zero]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, pow_zero, one_mul, hQ_col0, ↓reduceIte, Fin.succAbove_zero]
      rw [hQ_sub_det, mul_one]
    · intro i _ hi0
      simp [hQ_col0 i, hi0]
    · intro h; exact absurd (Finset.mem_univ 0) h
  have hP_det : P.det = (MMat p).det := by rw [Matrix.det_mul, hU_det, mul_one]
  rw [hρ_sign, hP_det, hQ_val] at hQ_det
  linear_combination hQ_det

private noncomputable def CMat (p : ℕ) (σ : Equiv.Perm (Fin (p - 1))) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) (ZMod p) :=
  Matrix.of fun k r =>
    if k.val < p - 2 then
      if r.val ≤ k.val + 1 then
        ((Nat.choose (k.val + 1) r.val : ℕ) : ZMod p) * (-(nzVal p (σ k))) ^ (k.val + 1 - r.val)
      else 0
    else
      if r.val = 0 then 2
      else ((Nat.choose (p - 1) r.val : ℕ) : ZMod p) * (-(nzVal p (σ k))) ^ (p - 1 - r.val)

private lemma sum_det_CMat_eq_one (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) :
    ∑ σ : Equiv.Perm (Fin (p - 1)), (CMat p σ).det = 1 := by
  have hp : 1 < p := by omega
  let m := p - 1
  have hm_ge2 : 2 ≤ m := by omega
  have hm_even : Even m := by
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  let lastM : Fin m := ⟨p - 2, by omega⟩
  let zeroM : Fin m := ⟨0, by omega⟩
  -- Expand each det (CMat p σ) = (CMat p σ)ᵀ.det = ∑ τ, sign τ * ∏ k, CMat p σ k (τ k)
  have hswap : ∑ σ : Equiv.Perm (Fin m), (CMat p σ).det =
      ∑ τ : Equiv.Perm (Fin m), (Equiv.Perm.sign τ : ZMod p) *
        ∑ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ k) := by
    calc ∑ σ : Equiv.Perm (Fin m), (CMat p σ).det
        = ∑ σ : Equiv.Perm (Fin m), (CMat p σ)ᵀ.det :=
          Finset.sum_congr rfl fun σ _ => (Matrix.det_transpose _).symm
      _ = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
            (Equiv.Perm.sign τ : ZMod p) * ∏ k : Fin m, CMat p σ k (τ k) :=
          Finset.sum_congr rfl fun σ _ => by rw [Matrix.det_apply']; rfl
      _ = ∑ τ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
            (Equiv.Perm.sign τ : ZMod p) * ∏ k : Fin m, CMat p σ k (τ k) := Finset.sum_comm
      _ = ∑ τ : Equiv.Perm (Fin m), (Equiv.Perm.sign τ : ZMod p) *
            ∑ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ k) :=
          Finset.sum_congr rfl fun τ _ => (Finset.mul_sum ..).symm
  rw [hswap]
  -- Split τ into Case 1 (`τ lastM = zeroM`) and Case 2 (`τ lastM ≠ zeroM`).
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : Equiv.Perm (Fin m) => τ lastM = zeroM)]
  -- Case 1: Only the unique shift permutation `τ0` contributes, giving `2`!
  let τ0 : Equiv.Perm (Fin m) :=
    { toFun := fun k => if h : k.val < p - 2 then ⟨k.val + 1, by omega⟩ else zeroM
      invFun := fun r => if h : r.val = 0 then lastM else ⟨r.val - 1, by omega⟩
      left_inv := fun k => by
        by_cases h : k.val < p - 2
        · simp [h]
        · have hk : k.val = p - 2 := by omega
          simp [h, zeroM, lastM]; ext; exact hk.symm
      right_inv := fun r => by
        by_cases h : r.val = 0
        · simp [h, lastM, zeroM]; ext; exact h.symm
        · have : r.val - 1 < p - 2 := by omega
          simp [h, this]; ext; dsimp; omega }
  have hlastM_val : lastM.val = p - 2 := rfl
  have hτ0_sign : (Equiv.Perm.sign τ0 : ZMod p) = -1 := by
    let eFin : Fin ((p - 2) + 1) ≃ Fin m := finCongr (by omega)
    have hsign_eq : Equiv.Perm.sign τ0 = Equiv.Perm.sign (Fin.cycleRange (Fin.last (p - 2))) := by
      refine Equiv.Perm.sign_eq_sign_of_equiv τ0 (Fin.cycleRange (Fin.last (p - 2))) eFin.symm ?_
      intro k
      by_cases h : k.val < p - 2
      · have hlt : eFin.symm k < Fin.last (p - 2) := by
          change (eFin.symm k).val < p - 2; simpa [eFin] using h
        rw [Fin.cycleRange_of_lt hlt]
        have hval := Fin.val_add_one_of_lt hlt
        simp only [eFin, finCongr_symm, finCongr_apply, Fin.val_cast] at hval
        ext
        simp only [τ0, Equiv.coe_fn_mk, h, ↓reduceDIte, eFin, finCongr_symm, finCongr_apply,
          Fin.val_cast]
        exact hval.symm
      · have hlast : eFin.symm k = Fin.last (p - 2) := by
          ext; change k.val = p - 2; omega
        rw [hlast, Fin.cycleRange_self]
        ext; simp [τ0, eFin, h, zeroM]
    rw [hsign_eq, Fin.sign_cycleRange]
    have hq_odd : Odd (p - 2) := by
      obtain ⟨t, ht⟩ := hm_even; exact ⟨t - 1, by omega⟩
    simp [hq_odd.neg_one_pow]
  have hcase1 : ∑ τ ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin m) => τ lastM = zeroM),
      (Equiv.Perm.sign τ : ZMod p) * ∑ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ k) = 2 := by
    have hτ0_mem : τ0 ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin m) => τ lastM = zeroM) := by
      simp [τ0, lastM, zeroM]
    rw [Finset.sum_eq_single τ0]
    · have hprod_τ0 : ∀ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ0 k) = 2 := by
        intro σ
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ lastM)]
        have hlast_val : CMat p σ lastM (τ0 lastM) = 2 := by simp [CMat, τ0, lastM, zeroM]
        have hrest : ∏ k ∈ Finset.univ.erase lastM, CMat p σ k (τ0 k) = 1 := by
          refine Finset.prod_eq_one fun k hk => ?_
          have hklt : k.val < p - 2 := by
            have hne : k.val ≠ p - 2 := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
            omega
          simp [CMat, τ0, hklt]
        rw [hlast_val, hrest, mul_one]
      simp_rw [hprod_τ0]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
        ZMod.wilsons_lemma, hτ0_sign]
      ring
    · intro τ hτ hτne
      have hτ_last : τ lastM = zeroM := (Finset.mem_filter.mp hτ).2
      have hex_gt : ∃ k : Fin m, k.val < p - 2 ∧ k.val + 1 < (τ k).val := by
        by_contra! hle
        apply hτne
        have hsum_eq : ∑ k ∈ Finset.univ.erase lastM, (τ k).val =
            ∑ k ∈ Finset.univ.erase lastM, (k.val + 1) := by
          have h1 : ∑ k : Fin m, (τ k).val = ∑ k : Fin m, k.val :=
            Equiv.sum_comp τ (fun k : Fin m => k.val)
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ lastM), hτ_last] at h1
          have h3 : ∑ k ∈ Finset.univ.erase lastM, (k.val + 1) = ∑ r : Fin m, r.val := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ zeroM)]
            simp only [zeroM, zero_add]
            refine Finset.sum_bij (fun k _ => τ0 k) ?_ ?_ ?_ ?_
            · intro k hk
              have hklt : k.val < p - 2 := by
                have : k.val ≠ p - 2 := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
                omega
              refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
              intro h; have := congrArg Fin.val h; simp [τ0, hklt, zeroM] at this
            · intro k1 _ k2 _ h; exact τ0.injective h
            · intro r hr
              refine ⟨τ0.symm r, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, τ0.apply_symm_apply r⟩
              intro h
              have := congrArg τ0 h
              rw [τ0.apply_symm_apply] at this
              exact (Finset.ne_of_mem_erase hr) (this.trans (by simp [τ0, lastM, zeroM]))
            · intro k hk
              have hklt : k.val < p - 2 := by
                have : k.val ≠ p - 2 := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
                omega
              simp [τ0, hklt]
          simp only [zeroM, zero_add] at h1
          exact h1.trans h3.symm
        have hall_eq := (Finset.sum_eq_sum_iff_of_le fun k hk => hle k (by
          have : k.val ≠ p - 2 := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
          omega)).mp hsum_eq
        apply Equiv.ext; intro k
        by_cases hk : k = lastM
        · subst hk; rw [hτ_last]; simp [τ0, lastM]
        · have hklt : k.val < p - 2 := by
            have : k.val ≠ p - 2 := fun h => hk (Fin.ext h); omega
          have heqk := hall_eq k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
          ext; simp [τ0, hklt, heqk]
      obtain ⟨k0, hk0_lt, hk0_gt⟩ := hex_gt
      have hz : ∀ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ k) = 0 := fun σ =>
        Finset.prod_eq_zero (Finset.mem_univ k0) (by
          unfold CMat; simp only [Matrix.of_apply, hk0_lt, ↓reduceIte]
          rw [if_neg (by omega)])
      simp [hz]
    · intro h; exact absurd hτ0_mem h
  have hcase2 : ∑ τ ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin m) => ¬ τ lastM = zeroM),
      (Equiv.Perm.sign τ : ZMod p) * ∑ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ k) = -1 := by
    have hterm : ∀ τ ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin m) => ¬ τ lastM = zeroM),
        (Equiv.Perm.sign τ : ZMod p) * ∑ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ k) =
          -polyInt p ((Equiv.Perm.sign τ : Polynomial (ZMod p)) * ∏ k : Fin m, MMat p k (τ k)) := by
      intro τ hτ
      have hτ_last_ne : (τ lastM).val ≠ 0 := by
        intro h; exact (Finset.mem_filter.mp hτ).2 (Fin.ext h)
      by_cases hvalid : ∀ k : Fin m, k.val < p - 2 → (τ k).val ≤ k.val + 1
      · let e : Fin m → ℕ := fun k =>
          if k.val < p - 2 then k.val + 1 - (τ k).val else p - 1 - (τ k).val
        have he_sum : ∑ k : Fin m, e k = p - 1 := by
          have h1 : ∑ k : Fin m, (e k + (τ k).val) = ∑ k : Fin m, (k.val + 1) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            unfold e
            by_cases hk : k.val < p - 2
            · simp only [hk, ↓reduceIte]
              have := hvalid k hk; omega
            · simp only [hk, ↓reduceIte]
              have hk_eq : k.val = p - 2 := by omega
              have : (τ k).val ≤ p - 1 := by omega
              omega
          have h2 : ∑ k : Fin m, (τ k).val = ∑ k : Fin m, k.val :=
            Equiv.sum_comp τ (fun k : Fin m => k.val)
          rw [Finset.sum_add_distrib, h2] at h1
          have h3 : ∑ k : Fin m, (k.val + 1) = (∑ k : Fin m, k.val) + (p - 1) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul, mul_one]
          omega
        let c : Fin m → ZMod p := fun k =>
          if k.val < p - 2 then
            ((Nat.choose (k.val + 1) (τ k).val : ℕ) : ZMod p) * (-1 : ZMod p) ^ (k.val + 1 - (τ k).val)
          else 1
        have hC_factor : ∀ σ : Equiv.Perm (Fin m),
            ∏ k : Fin m, CMat p σ k (τ k) =
              (∏ k : Fin m, c k) * ∏ k : Fin m, (nzVal p (σ k)) ^ (e k) := by
          intro σ
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ => ?_
          unfold CMat c e
          simp only [Matrix.of_apply]
          by_cases hk : k.val < p - 2
          · simp only [hk, ↓reduceIte, hvalid k hk]
            rw [neg_eq_neg_one_mul (nzVal p (σ k)), mul_pow]
            ring
          · have hk_eq : k = lastM := Fin.ext (by omega)
            subst hk_eq
            simp only [hk, ↓reduceIte, hτ_last_ne]
            rw [choose_prime_sub_one p (τ lastM).val (by omega),
              neg_eq_neg_one_mul (nzVal p (σ lastM)), mul_pow]
            have hpow : (-1 : ZMod p) ^ (τ lastM).val * (-1 : ZMod p) ^ (p - 1 - (τ lastM).val) = 1 := by
              rw [← pow_add, Nat.add_sub_of_le (by omega : (τ lastM).val ≤ p - 1), hm_even.neg_one_pow]
            calc (-1 : ZMod p) ^ (τ lastM).val * ((-1 : ZMod p) ^ (p - 1 - (τ lastM).val) * nzVal p (σ lastM) ^ (p - 1 - (τ lastM).val))
                = ((-1 : ZMod p) ^ (τ lastM).val * (-1 : ZMod p) ^ (p - 1 - (τ lastM).val)) * nzVal p (σ lastM) ^ (p - 1 - (τ lastM).val) := by ring
              _ = 1 * nzVal p (σ lastM) ^ (p - 1 - (τ lastM).val) := by rw [hpow]
        let Spos := Finset.univ.filter fun k : Fin m => 0 < e k
        let Slt := (Finset.univ.erase lastM).filter fun k : Fin m => (τ k).val < k.val + 1
        have hSpos_eq : Spos = insert lastM Slt := by
          ext k
          simp only [Spos, Slt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_erase]
          by_cases hk : k = lastM
          · subst hk
            simp only [true_or, iff_true, e, lastM, lt_self_iff_false, ↓reduceIte]
            have : (τ ⟨p - 2, by omega⟩).val < p - 1 := (τ _).isLt
            omega
          · have hklt : k.val < p - 2 := by
              have : k.val ≠ p - 2 := fun h => hk (Fin.ext h); omega
            simp only [hk, false_or, ne_eq, not_false_eq_true, true_and, e, hklt, ↓reduceIte]
            have := hvalid k hklt
            omega
        have hSpos_card : Spos.card = Slt.card + 1 := by
          rw [hSpos_eq, Finset.card_insert_of_notMem (by simp [Slt])]
        have hM_prod : ∏ k : Fin m, MMat p k (τ k) =
            Polynomial.C (∏ k : Fin m, c k) * Polynomial.X ^ Slt.card := by
          have hM_each : ∀ k : Fin m, MMat p k (τ k) =
              Polynomial.C (c k) * Polynomial.X ^ (if k ∈ Slt then 1 else 0) := by
            intro k
            unfold MMat c
            simp only [Matrix.of_apply]
            by_cases hk : k.val < p - 2
            · have hk_ne_last : k ≠ lastM := fun h => by subst h; simp [lastM] at hk
              have hk_le := hvalid k hk
              by_cases heq : (τ k).val = k.val + 1
              · have hnot : k ∉ Slt := by
                  simp only [Slt, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
                    not_and, not_lt]
                  intro _; omega
                simp [hk, heq, hnot]
              · have hlt : (τ k).val < k.val + 1 := by omega
                have hmem : k ∈ Slt := Finset.mem_filter.mpr
                  ⟨Finset.mem_erase.mpr ⟨hk_ne_last, Finset.mem_univ k⟩, hlt⟩
                simp [hk, heq, hlt, hmem]
            · have hk_eq : k = lastM := Fin.ext (by omega)
              subst hk_eq
              have hnot : lastM ∉ Slt := by simp [Slt]
              simp [hk, hτ_last_ne, hnot]
          simp_rw [hM_each, Finset.prod_mul_distrib, map_prod, Finset.prod_pow_eq_pow_sum]
          congr 2
          simp
        simp_rw [hC_factor]
        rw [← Finset.mul_sum, sum_perm_prod_pow e he_sum, hM_prod,
          show (Equiv.Perm.sign τ : Polynomial (ZMod p)) = Polynomial.C (Equiv.Perm.sign τ : ZMod p) by simp]
        conv_rhs => rw [← mul_assoc, ← map_mul, polyInt_C_mul_X_pow]
        have hsc : ((Finset.univ.filter fun k : Fin m => 0 < e k).card : ZMod p) =
            ((Slt.card + 1 : ℕ) : ZMod p) := congrArg (Nat.cast (R := ZMod p)) hSpos_card
        rw [hsc]
        ring
      · push Not at hvalid
        obtain ⟨k0, hk0_lt, hk0_gt⟩ := hvalid
        have hzC : ∀ σ : Equiv.Perm (Fin m), ∏ k : Fin m, CMat p σ k (τ k) = 0 := fun σ =>
          Finset.prod_eq_zero (Finset.mem_univ k0) (by
            unfold CMat; simp only [Matrix.of_apply, hk0_lt, ↓reduceIte]; rw [if_neg (by omega)])
        have hzM : ∏ k : Fin m, MMat p k (τ k) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k0) (by
            unfold MMat; simp only [Matrix.of_apply, hk0_lt, ↓reduceIte]
            rw [if_neg (by omega), if_neg (by omega)])
        simp [hzC, hzM]
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← map_sum]
    -- Also for τ with τ lastM = zeroM, ∏ k, MMat p k (τ k) = 0 since MMat p lastM zeroM = 0!
    have hM_zero_case1 : ∀ τ : Equiv.Perm (Fin m), τ lastM = zeroM →
        (Equiv.Perm.sign τ : Polynomial (ZMod p)) * ∏ k : Fin m, MMat p k (τ k) = 0 := by
      intro τ hτ
      have hz : ∏ k : Fin m, MMat p k (τ k) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ lastM) (by
          unfold MMat; simp [lastM, hτ, zeroM])
      rw [hz, mul_zero]
    have hM_det : ∑ τ ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin m) => ¬ τ lastM = zeroM),
        (Equiv.Perm.sign τ : Polynomial (ZMod p)) * ∏ k : Fin m, MMat p k (τ k) = (MMat p).det := by
      have h1 : ∑ τ : Equiv.Perm (Fin m),
          (Equiv.Perm.sign τ : Polynomial (ZMod p)) * ∏ k : Fin m, MMat p k (τ k) = (MMat p).det := by
        rw [← Matrix.det_transpose (MMat p), Matrix.det_apply']; rfl
      rw [← h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : Equiv.Perm (Fin m) => τ lastM = zeroM)]
      have hz1 : ∑ τ ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin m) => τ lastM = zeroM),
          (Equiv.Perm.sign τ : Polynomial (ZMod p)) * ∏ k : Fin m, MMat p k (τ k) = 0 :=
        Finset.sum_eq_zero fun τ hτ => hM_zero_case1 τ (Finset.mem_filter.mp hτ).2
      rw [hz1, zero_add]
    rw [hM_det, det_MMat p hp2, map_neg, neg_neg, map_sum]
    have hsumW : ∑ r ∈ Finset.Ico 1 (p - 1), polyInt p (vPoly p r) =
        ∑ r ∈ Finset.Ico 1 (p - 1), bW p r :=
      Finset.sum_congr rfl fun r _ => polyInt_vPoly p r
    rw [hsumW, sum_bW_eq_neg_one p hp2]
  rw [hcase1, hcase2]
  ring

/- ### Part 5: Shifted Vandermonde reduction to `∑ σ, det (CMat p σ)` -/

private lemma det_shifted_vandermonde {p : ℕ} [Fact p.Prime] (g : Fin (p - 1) → ZMod p) :
    (Matrix.of fun (i k : Fin (p - 1)) => (g i) ^ (k.val + 1)).det =
      if h : ∃ τ : Equiv.Perm (Fin (p - 1)), ∀ i, g i = nzVal p (τ i) then
        -(Equiv.Perm.sign (Classical.choose h) : ZMod p) * (Matrix.vandermonde (nzVal p)).det
      else 0 := by
  have hfactor : (Matrix.of fun (i k : Fin (p - 1)) => (g i) ^ (k.val + 1)).det =
      (∏ i : Fin (p - 1), g i) * (Matrix.vandermonde g).det := by
    have heq : (Matrix.of fun (i k : Fin (p - 1)) => (g i) ^ (k.val + 1)) =
        Matrix.diagonal g * Matrix.vandermonde g := by
      ext i k
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vandermonde_apply, pow_succ']
    rw [heq, Matrix.det_mul, Matrix.det_diagonal]
  rw [hfactor]
  split_ifs with h
  · let τ := Classical.choose h
    have hτ : ∀ i, g i = nzVal p (τ i) := Classical.choose_spec h
    have hprod : ∏ i : Fin (p - 1), g i = -1 := by
      calc ∏ i : Fin (p - 1), g i
          = ∏ i : Fin (p - 1), nzVal p (τ i) := Finset.prod_congr rfl fun i _ => hτ i
        _ = ∏ i : Fin (p - 1), nzVal p i := Equiv.prod_comp τ (nzVal p)
        _ = ((p - 1).factorial : ZMod p) := by
            unfold nzVal
            rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun k => k + 1) (p - 1)]
            have : ∏ k ∈ Finset.range (p - 1), (k + 1) = (p - 1).factorial := by
              induction (p - 1) with
              | zero => simp
              | succ m ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ, mul_comm]
            rw [this]
        _ = -1 := ZMod.wilsons_lemma p
    have hvand : Matrix.vandermonde g = (Matrix.vandermonde (nzVal p)).submatrix τ id := by
      ext i k; simp [Matrix.vandermonde_apply, hτ i]
    rw [hprod, hvand, Matrix.det_permute]
    dsimp only [τ]
    ring
  · by_cases h0 : ∃ i : Fin (p - 1), g i = 0
    · obtain ⟨i0, hi0⟩ := h0
      rw [Finset.prod_eq_zero (Finset.mem_univ i0) hi0, zero_mul]
    · push Not at h0
      by_cases hinj : Function.Injective g
      · exfalso
        -- If g is injective and never 0, then g = nzVal p ∘ τ for some permutation τ!
        have himg : ∀ i : Fin (p - 1), ∃ j : Fin (p - 1), nzVal p j = g i := fun i =>
          let ⟨j, _, hj⟩ := Finset.mem_image.mp ((nzVal_range (p := p)) ▸ Finset.mem_erase.mpr ⟨h0 i, Finset.mem_univ _⟩)
          ⟨j, hj⟩
        let φ : Fin (p - 1) → Fin (p - 1) := fun i => Classical.choose (himg i)
        have hφ : ∀ i, nzVal p (φ i) = g i := fun i => Classical.choose_spec (himg i)
        have hφ_inj : Function.Injective φ := fun i1 i2 heq =>
          hinj ((hφ i1).symm.trans ((congrArg (nzVal p) heq).trans (hφ i2)))
        have hφ_bij : Function.Bijective φ := (Finite.injective_iff_bijective).mp hφ_inj
        exact h ⟨Equiv.ofBijective φ hφ_bij, fun i => (hφ i).symm⟩
      · obtain ⟨i1, i2, heq, hne⟩ : ∃ i1 i2, g i1 = g i2 ∧ i1 ≠ i2 := by
          unfold Function.Injective at hinj; push Not at hinj; exact hinj
        have hdet0 : (Matrix.vandermonde g).det = 0 :=
          Matrix.det_zero_of_row_eq hne (funext fun k => by simp [Matrix.vandermonde_apply, heq])
        rw [hdet0, mul_zero]

private lemma sum_ortho_pairs_eq_neg_one (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) :
    ∑ f : Equiv.Perm (Fin (p - 1)),
      (if h : ∃ g : Equiv.Perm (Fin (p - 1)), ∀ i, nzVal p (f i) - nzVal p i = nzVal p (g i) then
        (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign (Classical.choose h) : ZMod p)
      else 0) = -1 := by
  have hp : 1 < p := by omega
  let m := p - 1
  let V : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.vandermonde (nzVal p)
  have hV_ne : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hlt : i < j := (Finset.mem_Ioi.mp hj)
    exact sub_ne_zero.mpr fun heq => (ne_of_lt hlt) (nzVal_injective heq.symm)
  have hfactor_B : ∀ σ : Equiv.Perm (Fin m),
      Matrix.of (fun (k j : Fin m) => (nzVal p j - nzVal p (σ k)) ^ (k.val + 1)) =
        CMat p σ * Vᵀ := by
    intro σ
    ext k j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, V, Matrix.vandermonde_apply]
    unfold CMat
    simp only [Matrix.of_apply]
    by_cases hk : k.val < p - 2
    · simp only [hk, ↓reduceIte]
      rw [sub_eq_add_neg, add_pow]
      have hsub : ∑ r : Fin m,
          (if r.val ≤ k.val + 1 then
            ((Nat.choose (k.val + 1) r.val : ℕ) : ZMod p) * (-(nzVal p (σ k))) ^ (k.val + 1 - r.val)
          else 0) * nzVal p j ^ r.val =
          ∑ r ∈ Finset.range (k.val + 2),
            nzVal p j ^ r * (-(nzVal p (σ k))) ^ (k.val + 1 - r) * ((Nat.choose (k.val + 1) r : ℕ) : ZMod p) := by
        refine Finset.sum_bij_ne_zero (fun r _ _ => r.val) ?_ ?_ ?_ ?_
        · intro r _ hne
          by_contra hnot
          have : ¬ r.val ≤ k.val + 1 := by simp only [Finset.mem_range] at hnot; omega
          exact hne (by simp [this])
        · intro r1 _ _ r2 _ _ h; exact Fin.ext h
        · intro r hr hne
          have hrlt : r < k.val + 2 := Finset.mem_range.mp hr
          refine ⟨⟨r, by omega⟩, Finset.mem_univ _, ?_, rfl⟩
          simp only [show r ≤ k.val + 1 by omega, ↓reduceIte]
          intro hz; exact hne (by linear_combination hz)
        · intro r _ hne
          have hrle : r.val ≤ k.val + 1 := by
            by_contra hnot; exact hne (by simp [hnot])
          simp only [hrle, ↓reduceIte]; ring
      exact hsub.symm
    · have hk_eq : k.val = p - 2 := by omega
      have hk1 : k.val + 1 = p - 1 := by omega
      simp only [hk, ↓reduceIte, hk1]
      rw [sub_eq_add_neg, add_pow, Finset.sum_range_succ]
      conv_lhs => rw [show Finset.range (p - 1) = Finset.range ((p - 2) + 1) by congr 1; omega]
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_self, Nat.sub_self, Nat.sub_zero, pow_zero, mul_one, Nat.cast_one,
        Nat.choose_zero_right, one_mul]
      have hp1_j : nzVal p j ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one (nzVal_ne_zero j)
      have hp1_s : (-(nzVal p (σ k))) ^ (p - 1) = 1 :=
        ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr (nzVal_ne_zero (σ k)))
      rw [hp1_j, hp1_s]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, by omega⟩ : Fin m))]
      simp only [↓reduceIte, pow_zero, mul_one]
      have hrest : ∑ r ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin m),
          (if r.val = 0 then (2 : ZMod p)
           else ((Nat.choose (p - 1) r.val : ℕ) : ZMod p) * (-(nzVal p (σ k))) ^ (p - 1 - r.val)) *
            nzVal p j ^ r.val =
          ∑ r ∈ Finset.range (p - 2),
            nzVal p j ^ (r + 1) * (-(nzVal p (σ k))) ^ (p - 1 - (r + 1)) *
              ((Nat.choose (p - 1) (r + 1) : ℕ) : ZMod p) := by
        refine Finset.sum_bij (fun r _ => r.val - 1) ?_ ?_ ?_ ?_
        · intro r hr
          have hrne : r.val ≠ 0 := fun h => (Finset.ne_of_mem_erase hr) (Fin.ext h)
          simp only [Finset.mem_range]; omega
        · intro r1 hr1 r2 hr2 h
          have hr1ne : r1.val ≠ 0 := fun h0 => (Finset.ne_of_mem_erase hr1) (Fin.ext h0)
          have hr2ne : r2.val ≠ 0 := fun h0 => (Finset.ne_of_mem_erase hr2) (Fin.ext h0)
          exact Fin.ext (by omega)
        · intro r hr
          have hrlt : r < p - 2 := Finset.mem_range.mp hr
          refine ⟨⟨r + 1, by omega⟩, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; dsimp at this; omega, Finset.mem_univ _⟩, by simp⟩
        · intro r hr
          have hrne : r.val ≠ 0 := fun h => (Finset.ne_of_mem_erase hr) (Fin.ext h)
          have hadd : r.val - 1 + 1 = r.val := by omega
          simp only [hrne, ↓reduceIte, hadd]; ring
      rw [hrest]; ring
  have hmain : -(V.det) * ∑ f : Equiv.Perm (Fin m),
      (if h : ∃ g : Equiv.Perm (Fin m), ∀ i, nzVal p (f i) - nzVal p i = nzVal p (g i) then
        (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign (Classical.choose h) : ZMod p)
      else 0) = V.det := by
    calc -(V.det) * ∑ f : Equiv.Perm (Fin m),
          (if h : ∃ g : Equiv.Perm (Fin m), ∀ i, nzVal p (f i) - nzVal p i = nzVal p (g i) then
            (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign (Classical.choose h) : ZMod p)
          else 0)
        = ∑ f : Equiv.Perm (Fin m), (Equiv.Perm.sign f : ZMod p) *
            (Matrix.of fun (i k : Fin m) => (nzVal p (f i) - nzVal p i) ^ (k.val + 1)).det := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [det_shifted_vandermonde]
          split_ifs with h
          · ring
          · ring
      _ = ∑ f : Equiv.Perm (Fin m), ∑ π : Equiv.Perm (Fin m),
            (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign π : ZMod p) *
              ∏ i : Fin m, (nzVal p (f i) - nzVal p i) ^ ((π i).val + 1) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
          refine Finset.sum_congr rfl fun π _ => ?_
          simp only [Matrix.transpose_apply, Matrix.of_apply, mul_assoc]
      _ = ∑ π : Equiv.Perm (Fin m), (Equiv.Perm.sign π : ZMod p) *
            (Matrix.of fun (i j : Fin m) => (nzVal p j - nzVal p i) ^ ((π i).val + 1)).det := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          simp only [Matrix.transpose_apply, Matrix.of_apply]; ring
      _ = ∑ π : Equiv.Perm (Fin m),
            (Matrix.of fun (k j : Fin m) => (nzVal p j - nzVal p (π.symm k)) ^ (k.val + 1)).det := by
          refine Finset.sum_congr rfl fun π _ => ?_
          have hsub : (Matrix.of fun (i j : Fin m) => (nzVal p j - nzVal p i) ^ ((π i).val + 1)) =
              (Matrix.of fun (k j : Fin m) => (nzVal p j - nzVal p (π.symm k)) ^ (k.val + 1)).submatrix π id := by
            ext i j; simp
          rw [hsub, Matrix.det_permute, ← mul_assoc]
          have hsq : (Equiv.Perm.sign π : ZMod p) * (Equiv.Perm.sign π : ZMod p) = 1 := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
          rw [hsq, one_mul]
      _ = ∑ σ : Equiv.Perm (Fin m),
            (Matrix.of fun (k j : Fin m) => (nzVal p j - nzVal p (σ k)) ^ (k.val + 1)).det :=
          Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin m)))
            (fun σ => (Matrix.of fun (k j : Fin m) => (nzVal p j - nzVal p (σ k)) ^ (k.val + 1)).det)
      _ = ∑ σ : Equiv.Perm (Fin m), (CMat p σ).det * V.det := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hfactor_B σ, Matrix.det_mul, Matrix.det_transpose]
      _ = (∑ σ : Equiv.Perm (Fin m), (CMat p σ).det) * V.det := (Finset.sum_mul ..).symm
      _ = V.det := by rw [sum_det_CMat_eq_one p hp2, one_mul]
  have hmain' : V.det * -(∑ f : Equiv.Perm (Fin m),
      (if h : ∃ g : Equiv.Perm (Fin m), ∀ i, nzVal p (f i) - nzVal p i = nzVal p (g i) then
        (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign (Classical.choose h) : ZMod p)
      else 0)) = V.det * 1 := by
    linear_combination hmain
  have hneg := mul_left_cancel₀ hV_ne hmain'
  exact neg_eq_iff_eq_neg.mp hneg

/- ### Part 6: `ZMod p` action on reduced Latin squares and fixed-point bijection -/

private lemma sum_zmod_action_eq_fixed {p : ℕ} [Fact p.Prime] {α : Type*} [Fintype α]
    (act : ZMod p → α → α)
    (h0 : ∀ x, act 0 x = x)
    (hadd : ∀ a b x, act (a + b) x = act a (act b x))
    (w : α → ZMod p)
    (hw : ∀ a x, w (act a x) = w x)
    [Fintype {x : α // ∀ a : ZMod p, act a x = x}] :
    ∑ x : α, w x = ∑ x : {x : α // ∀ a : ZMod p, act a x = x}, w x.1 := by
  classical
  let Fix := Finset.univ.filter fun x : α => ∀ a : ZMod p, act a x = x
  have hsplit : ∑ x : α, w x = ∑ x ∈ Fix, w x + ∑ x ∈ Finset.univ \ Fix, w x := by
    rw [← Finset.sum_sdiff (Finset.subset_univ Fix), add_comm]
  have hnonfix : ∑ x ∈ Finset.univ \ Fix, w x = 0 := by
    -- Equivalence relation on nonfixed points: x ~ y ↔ ∃ a, act a x = y
    let NonFix := {x : α // x ∈ Finset.univ \ Fix}
    let rel : NonFix → NonFix → Prop := fun x y => ∃ a : ZMod p, act a x.1 = y.1
    have hsetoid : Equivalence rel :=
      { refl := fun x => ⟨0, h0 x.1⟩
        symm := fun ⟨a, ha⟩ => ⟨-a, by rw [← ha, ← hadd, neg_add_cancel, h0]⟩
        trans := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨b + a, by rw [hadd, ha, hb]⟩ }
    let instS : Setoid NonFix := ⟨rel, hsetoid⟩
    have hinj : ∀ x : NonFix, Function.Injective (fun a : ZMod p => act a x.1) := by
      intro x a b hab
      dsimp only at hab
      by_contra hne
      let d := b - a
      have hd_ne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hd_fix : act d x.1 = x.1 := by
        calc act (b - a) x.1 = act (-a + b) x.1 := by ring_nf
          _ = act (-a) (act b x.1) := hadd (-a) b x.1
          _ = act (-a) (act a x.1) := by rw [hab]
          _ = act (-a + a) x.1 := (hadd (-a) a x.1).symm
          _ = x.1 := by rw [neg_add_cancel, h0]
      have hmul_fix : ∀ k : ℕ, act ((k : ZMod p) * d) x.1 = x.1 := by
        intro k
        induction k with
        | zero => simp [h0]
        | succ k ih =>
          rw [Nat.cast_succ, add_mul, one_mul, add_comm, hadd, ih, hd_fix]
      have hall_fix : ∀ c : ZMod p, act c x.1 = x.1 := by
        intro c
        let k : ℕ := (c * d⁻¹).val
        have hk : (k : ZMod p) * d = c := by
          simp [k, mul_assoc, inv_mul_cancel₀ hd_ne]
        rw [← hk]
        exact hmul_fix k
      have hx_fix : x.1 ∈ Fix := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall_fix⟩
      exact (Finset.mem_sdiff.mp x.2).2 hx_fix
    -- Every orbit class of NonFix has cardinality p, and w is constant on each class!
    have hfib := Fintype.sum_fiberwise (Quotient.mk' : NonFix → Quotient instS) (fun x : NonFix => w x.1)
    rw [← Finset.sum_coe_sort (Finset.univ \ Fix)]
    trans (∑ q : Quotient instS, ∑ y : {y : NonFix // Quotient.mk' y = q}, w y.1.1)
    · convert hfib.symm
    refine Finset.sum_eq_zero fun q _ => ?_
    obtain ⟨x0, rfl⟩ := Quotient.exists_rep q
    have hconst : ∀ y : {y : NonFix // Quotient.mk' y = Quotient.mk' x0}, w y.1.1 = w x0.1 := by
      intro y
      have hrel : rel y.1 x0 := Quotient.exact y.2
      obtain ⟨a, ha⟩ := hrel
      rw [← ha, hw]
    have hcard : Fintype.card {y : NonFix // Quotient.mk' y = Quotient.mk' x0} = p := by
      let eOrb : ZMod p ≃ {y : NonFix // Quotient.mk' y = Quotient.mk' x0} :=
        { toFun := fun a =>
            ⟨⟨act a x0.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hfix => by
              have h0fix : x0.1 ∈ Fix := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => by
                have h1 := (Finset.mem_filter.mp hfix).2 c
                have := congrArg (act (-a)) h1
                simp only [← hadd] at this
                have hL : -a + (c + a) = c := by ring
                have hR : -a + a = 0 := neg_add_cancel a
                rw [hL, hR, h0] at this
                exact this⟩
              exact (Finset.mem_sdiff.mp x0.2).2 h0fix⟩⟩,
            Quotient.sound ⟨-a, by rw [← hadd, neg_add_cancel, h0]⟩⟩
          invFun := fun y => Classical.choose (Quotient.exact y.2.symm)
          left_inv := fun a => by
            dsimp only
            apply hinj x0
            exact Classical.choose_spec (p := fun b : ZMod p => act b x0.1 = act a x0.1) _
          right_inv := fun y => Subtype.ext (Subtype.ext (Classical.choose_spec (Quotient.exact y.2.symm))) }
      rw [← Fintype.card_congr eOrb, ZMod.card]
    calc ∑ y : {y : NonFix // Quotient.mk' y = Quotient.mk' x0}, w y.1.1
        = ∑ _y : {y : NonFix // Quotient.mk' y = Quotient.mk' x0}, w x0.1 :=
          Finset.sum_congr rfl fun y _ => hconst y
      _ = (p : ZMod p) * w x0.1 := by rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      _ = 0 := by simp
  rw [hsplit, hnonfix, add_zero]
  refine Finset.sum_bij (fun x hx => ⟨x, (Finset.mem_filter.mp hx).2⟩) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro _ _; exact Finset.mem_univ _
  · intro _ _ _ _ h; exact congrArg Subtype.val h
  · intro y _; exact ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩

private noncomputable def optZModEquivFin (p : ℕ) [NeZero p] : Option (ZMod p) ≃ Fin (p + 1) where
  toFun
    | none => 0
    | some x => ⟨x.val + 1, by have := x.val_lt; omega⟩
  invFun i := if h : i.val = 0 then none else some ((i.val - 1 : ℕ) : ZMod p)
  left_inv x := by
    cases x with
    | none => simp
    | some a => simp
  right_inv i := by
    by_cases h : i.val = 0
    · simp [h]; exact Fin.ext h.symm
    · have hlt : i.val - 1 < p := by omega
      simp [h, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      ext; dsimp; omega

private noncomputable def shiftPerm (p : ℕ) [NeZero p] (a : ZMod p) : Equiv.Perm (Fin (p + 1)) :=
  (optZModEquivFin p).symm.trans ((Equiv.optionCongr (Equiv.addRight a)).trans (optZModEquivFin p))

private lemma shiftPerm_zero_idx {p : ℕ} [NeZero p] (a : ZMod p) : shiftPerm p a 0 = 0 := by
  simp [shiftPerm, optZModEquivFin]

private lemma shiftPerm_some {p : ℕ} [NeZero p] (a x : ZMod p) :
    shiftPerm p a (optZModEquivFin p (some x)) = optZModEquivFin p (some (x + a)) := by
  simp [shiftPerm]

private lemma shiftPerm_zero {p : ℕ} [NeZero p] : shiftPerm p 0 = 1 := by
  apply Equiv.ext; intro i
  rcases (optZModEquivFin p).surjective i with ⟨o, rfl⟩
  cases o <;> simp [shiftPerm]

private lemma shiftPerm_add {p : ℕ} [NeZero p] (a b : ZMod p) :
    shiftPerm p (a + b) = (shiftPerm p b).trans (shiftPerm p a) := by
  apply Equiv.ext; intro i
  rcases (optZModEquivFin p).surjective i with ⟨o, rfl⟩
  cases o with
  | none => simp [shiftPerm]
  | some x => simp [shiftPerm, add_assoc, add_comm a b]

private abbrev RedLS (n : ℕ) [NeZero n] :=
  {L : LatinSquare n // (∀ j, L.val 0 j = j) ∧ ∀ i, L.val i 0 = i}

private noncomputable def actRedLS {p : ℕ} [NeZero p] (a : ZMod p) (L : RedLS (p + 1)) :
    RedLS (p + 1) :=
  ⟨⟨fun i j => shiftPerm p a (L.1.val (shiftPerm p (-a) i) (shiftPerm p (-a) j)),
    fun i => ((shiftPerm p a).bijective.comp ((L.1.property.1 _).comp (shiftPerm p (-a)).bijective)),
    fun j => ((shiftPerm p a).bijective.comp ((L.1.property.2 _).comp (shiftPerm p (-a)).bijective))⟩,
   ⟨fun j => by
      simp only [shiftPerm_zero_idx, L.2.1]
      change ((shiftPerm p (-a)).trans (shiftPerm p a)) j = j
      rw [← shiftPerm_add, add_neg_cancel, shiftPerm_zero]; rfl,
    fun i => by
      simp only [shiftPerm_zero_idx, L.2.2]
      change ((shiftPerm p (-a)).trans (shiftPerm p a)) i = i
      rw [← shiftPerm_add, add_neg_cancel, shiftPerm_zero]; rfl⟩⟩

private lemma sign_actRedLS {p : ℕ} [NeZero p] (a : ZMod p) (L : RedLS (p + 1)) :
    sign (actRedLS a L).1 = sign L.1 := by
  let row (M : LatinSquare (p + 1)) (i : Fin (p + 1)) := Equiv.ofBijective _ (M.property.1 i)
  let col (M : LatinSquare (p + 1)) (j : Fin (p + 1)) := Equiv.ofBijective _ (M.property.2 j)
  have hrow : ∀ i, row (actRedLS a L).1 i =
      (shiftPerm p (-a)).trans ((row L.1 (shiftPerm p (-a) i)).trans (shiftPerm p a)) := fun i =>
    Equiv.ext fun j => rfl
  have hcol : ∀ j, col (actRedLS a L).1 j =
      (shiftPerm p (-a)).trans ((col L.1 (shiftPerm p (-a) j)).trans (shiftPerm p a)) := fun j =>
    Equiv.ext fun i => rfl
  have hsh_prod : ∀ σ : Equiv.Perm (Fin (p + 1)),
      Equiv.Perm.sign ((shiftPerm p (-a)).trans (σ.trans (shiftPerm p a))) = Equiv.Perm.sign σ := by
    intro σ
    rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_trans]
    have hmul : Equiv.Perm.sign (shiftPerm p a) * Equiv.Perm.sign (shiftPerm p (-a)) = 1 := by
      rw [← map_mul]
      have : shiftPerm p a * shiftPerm p (-a) = 1 := by
        apply Equiv.ext; intro i
        change shiftPerm p a (shiftPerm p (-a) i) = i
        change ((shiftPerm p (-a)).trans (shiftPerm p a)) i = i
        rw [← shiftPerm_add, add_neg_cancel, shiftPerm_zero]; rfl
      rw [this, map_one]
    calc Equiv.Perm.sign (shiftPerm p a) * Equiv.Perm.sign σ * Equiv.Perm.sign (shiftPerm p (-a))
        = (Equiv.Perm.sign (shiftPerm p a) * Equiv.Perm.sign (shiftPerm p (-a))) * Equiv.Perm.sign σ := by ac_rfl
      _ = Equiv.Perm.sign σ := by rw [hmul, one_mul]
  change (∏ i, Equiv.Perm.sign (row (actRedLS a L).1 i)) *
      (∏ j, Equiv.Perm.sign (col (actRedLS a L).1 j)) =
    (∏ i, Equiv.Perm.sign (row L.1 i)) * (∏ j, Equiv.Perm.sign (col L.1 j))
  simp_rw [hrow, hcol, hsh_prod]
  congr 1
  · exact Equiv.prod_comp (shiftPerm p (-a)) (fun i => Equiv.Perm.sign (row L.1 i))
  · exact Equiv.prod_comp (shiftPerm p (-a)) (fun j => Equiv.Perm.sign (col L.1 j))

private abbrev FixedRedLS (p : ℕ) [NeZero p] :=
  {L : RedLS (p + 1) // ∀ a : ZMod p, actRedLS a L = L}

private abbrev OrthoPair (p : ℕ) :=
  {f : Equiv.Perm (Fin (p - 1)) // ∃ g : Equiv.Perm (Fin (p - 1)), ∀ i, nzVal p (f i) - nzVal p i = nzVal p (g i)}

private noncomputable def nzEquiv (p : ℕ) [Fact p.Prime] :
    Fin (p - 1) ≃ {x : ZMod p // x ≠ 0} where
  toFun i := ⟨nzVal p i, nzVal_ne_zero i⟩
  invFun x := ⟨x.1.val - 1, by
    have hne : x.1.val ≠ 0 := fun h => x.2 (by rw [← ZMod.natCast_zmod_val x.1, h, Nat.cast_zero])
    have hlt := x.1.val_lt
    omega⟩
  left_inv i := by
    ext; dsimp [nzVal]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  right_inv x := by
    apply Subtype.ext; dsimp [nzVal]
    have hne : x.1.val ≠ 0 := fun h => x.2 (by rw [← ZMod.natCast_zmod_val x.1, h, Nat.cast_zero])
    have : x.1.val - 1 + 1 = x.1.val := by omega
    rw [this, ZMod.natCast_zmod_val]

private lemma fixed_row0_zero {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (L : FixedRedLS p) :
    L.1.1.val (optZModEquivFin p (some 0)) (optZModEquivFin p (some 0)) = 0 := by
  let e := optZModEquivFin p
  let r0 (y : ZMod p) : Option (ZMod p) := e.symm (L.1.1.val (e (some 0)) (e (some y)))
  have hshift : ∀ x y : ZMod p,
      e.symm (L.1.1.val (e (some x)) (e (some y))) = (r0 (y - x)).map (· + x) := by
    intro x y
    have hfix := L.2 x
    have hval := congrFun (congrFun (congrArg (fun M : RedLS (p + 1) => M.1.val) hfix) (e (some x))) (e (some y))
    change shiftPerm p x (L.1.1.val (shiftPerm p (-x) (e (some x))) (shiftPerm p (-x) (e (some y)))) =
      L.1.1.val (e (some x)) (e (some y)) at hval
    rw [shiftPerm_some, shiftPerm_some, add_neg_cancel, ← sub_eq_add_neg] at hval
    rw [← hval]
    have hsh_symm : ∀ o : Option (ZMod p), e.symm (shiftPerm p x (e o)) = o.map (· + x) := by
      intro o; cases o <;> simp [shiftPerm, e]
    simpa [r0] using (hsh_symm (r0 (y - x)))
  have hr0_inj : Function.Injective r0 := by
    intro y1 y2 h
    have h1 := e.symm.injective h
    exact Option.some.inj (e.injective ((L.1.1.property.1 (e (some 0))).1 h1))
  have hr0_ne_zero : ∀ y : ZMod p, r0 y ≠ some 0 := by
    intro y h
    have h1 : L.1.1.val (e (some 0)) (e (some y)) = e (some 0) :=
      e.symm.injective (by simpa [r0] using h)
    have h2 : L.1.1.val (e (some 0)) 0 = e (some 0) := L.1.2.2 (e (some 0))
    have h3 : e (some y) = e none := (L.1.1.property.1 (e (some 0))).1 (h1.trans h2.symm)
    exact Option.some_ne_none y (e.injective h3)
  have hr0_none : ∃ d0 : ZMod p, r0 d0 = none := by
    obtain ⟨j, hj⟩ := (L.1.1.property.1 (e (some 0))).2 0
    rcases e.surjective j with ⟨o, rfl⟩
    cases o with
    | none =>
      exfalso
      have h0 : e none = 0 := rfl
      rw [h0, L.1.2.2] at hj
      exact Option.some_ne_none 0 (e.injective hj)
    | some d0 =>
      refine ⟨d0, ?_⟩
      change e.symm (L.1.1.val (e (some 0)) (e (some d0))) = none
      rw [hj]; simp [e, optZModEquivFin]
  obtain ⟨d0, hd0⟩ := hr0_none
  let fz (y : ZMod p) : ZMod p := (r0 y).getD 0
  have hfz_eq : ∀ y : ZMod p, y ≠ d0 → r0 y = some (fz y) ∧ fz y ≠ 0 := by
    intro y hy
    cases h : r0 y with
    | none => exact absurd (hr0_inj (h.trans hd0.symm)) hy
    | some z =>
      have hfz : fz y = z := by simp [fz, h]
      exact ⟨by rw [hfz], fun hz => hr0_ne_zero y (by rw [h, ← hfz, hz])⟩
  have hcol_inj : ∀ d1 d2 : ZMod p, d1 ≠ d0 → d2 ≠ d0 → fz d1 - d1 = fz d2 - d2 → d1 = d2 := by
    intro d1 d2 h1 h2 heq
    have hc1 : e.symm (L.1.1.val (e (some (-d1))) (e (some 0))) = some (fz d1 - d1) := by
      rw [hshift (-d1) 0, zero_sub, neg_neg, (hfz_eq d1 h1).1]; simp [sub_eq_add_neg]
    have hc2 : e.symm (L.1.1.val (e (some (-d2))) (e (some 0))) = some (fz d2 - d2) := by
      rw [hshift (-d2) 0, zero_sub, neg_neg, (hfz_eq d2 h2).1]; simp [sub_eq_add_neg]
    have hL_eq := e.symm.injective (hc1.trans ((congrArg some heq).trans hc2.symm))
    exact neg_injective (Option.some.inj (e.injective ((L.1.1.property.2 (e (some 0))).1 hL_eq)))
  have hcol_ne0 : ∀ d : ZMod p, d ≠ d0 → fz d - d ≠ 0 := by
    intro d hd h0
    have hc : e.symm (L.1.1.val (e (some (-d))) (e (some 0))) = some 0 := by
      rw [hshift (-d) 0, zero_sub, neg_neg, (hfz_eq d hd).1]
      simpa [sub_eq_add_neg] using congrArg some h0
    have hL1 : L.1.1.val (e (some (-d))) (e (some 0)) = e (some 0) :=
      e.symm.injective (by simpa using hc)
    have hL2 : L.1.1.val 0 (e (some 0)) = e (some 0) := L.1.2.1 (e (some 0))
    have harg : e (some (-d)) = e none := (L.1.1.property.2 (e (some 0))).1 (hL1.trans hL2.symm)
    exact Option.some_ne_none (-d) (e.injective harg)
  have himg_f : (Finset.univ.erase d0).image fz = Finset.univ.erase (0 : ZMod p) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_erase.mpr ⟨(hfz_eq d (Finset.ne_of_mem_erase hd)).2, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injOn (fun d1 hd1 d2 hd2 heq =>
        hr0_inj ((hfz_eq d1 (Finset.ne_of_mem_erase hd1)).1.trans
          ((congrArg some heq).trans (hfz_eq d2 (Finset.ne_of_mem_erase hd2)).1.symm))),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_erase_of_mem (Finset.mem_univ _)]
  have himg_g : (Finset.univ.erase d0).image (fun d => fz d - d) = Finset.univ.erase (0 : ZMod p) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_erase.mpr ⟨hcol_ne0 d (Finset.ne_of_mem_erase hd), Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injOn (fun d1 hd1 d2 hd2 heq =>
        hcol_inj d1 d2 (Finset.ne_of_mem_erase hd1) (Finset.ne_of_mem_erase hd2) heq),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_erase_of_mem (Finset.mem_univ _)]
  have hsum_f : ∑ d ∈ Finset.univ.erase d0, fz d = ∑ z ∈ Finset.univ.erase (0 : ZMod p), z := by
    rw [← himg_f, Finset.sum_image (fun d1 hd1 d2 hd2 heq =>
      hr0_inj ((hfz_eq d1 (Finset.ne_of_mem_erase hd1)).1.trans
        ((congrArg some heq).trans (hfz_eq d2 (Finset.ne_of_mem_erase hd2)).1.symm)))]
  have hsum_g : ∑ d ∈ Finset.univ.erase d0, (fz d - d) = ∑ z ∈ Finset.univ.erase (0 : ZMod p), z := by
    rw [← himg_g, Finset.sum_image (fun d1 hd1 d2 hd2 heq =>
      hcol_inj d1 d2 (Finset.ne_of_mem_erase hd1) (Finset.ne_of_mem_erase hd2) heq)]
  have hsum_d : ∑ d ∈ Finset.univ.erase d0, d = 0 := by
    rw [Finset.sum_sub_distrib, hsum_f] at hsum_g
    exact sub_eq_self.mp hsum_g
  have hd0_zero : d0 = 0 := by
    have htot := sum_zmod_eq_zero hp2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d0), hsum_d, add_zero] at htot
    exact htot
  subst hd0_zero
  apply e.symm.injective
  simpa [r0, e, optZModEquivFin] using hd0

private noncomputable def fixedToOrtho {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (L : FixedRedLS p) : OrthoPair p := by
  let e := optZModEquivFin p
  let r0 (y : ZMod p) : Option (ZMod p) := e.symm (L.1.1.val (e (some 0)) (e (some y)))
  have hshift : ∀ x y : ZMod p,
      e.symm (L.1.1.val (e (some x)) (e (some y))) = (r0 (y - x)).map (· + x) := by
    intro x y
    have hfix := L.2 x
    have hval := congrFun (congrFun (congrArg (fun M : RedLS (p + 1) => M.1.val) hfix) (e (some x))) (e (some y))
    change shiftPerm p x (L.1.1.val (shiftPerm p (-x) (e (some x))) (shiftPerm p (-x) (e (some y)))) =
      L.1.1.val (e (some x)) (e (some y)) at hval
    rw [shiftPerm_some, shiftPerm_some, add_neg_cancel, ← sub_eq_add_neg] at hval
    rw [← hval]
    have hsh_symm : ∀ o : Option (ZMod p), e.symm (shiftPerm p x (e o)) = o.map (· + x) := by
      intro o; cases o <;> simp [shiftPerm, e]
    simpa [r0] using (hsh_symm (r0 (y - x)))
  have hr0_inj : Function.Injective r0 := by
    intro y1 y2 h
    have h1 := e.symm.injective h
    exact Option.some.inj (e.injective ((L.1.1.property.1 (e (some 0))).1 h1))
  have hr0_ne_zero : ∀ y : ZMod p, r0 y ≠ some 0 := by
    intro y h
    have h1 : L.1.1.val (e (some 0)) (e (some y)) = e (some 0) :=
      e.symm.injective (by simpa [r0] using h)
    have h2 : L.1.1.val (e (some 0)) 0 = e (some 0) := L.1.2.2 (e (some 0))
    have h3 : e (some y) = e none := (L.1.1.property.1 (e (some 0))).1 (h1.trans h2.symm)
    exact Option.some_ne_none y (e.injective h3)
  have hd0 : r0 0 = none := by
    change e.symm (L.1.1.val (e (some 0)) (e (some 0))) = none
    rw [fixed_row0_zero hp2 L]
    simp [e, optZModEquivFin]
  let fz (y : ZMod p) : ZMod p := (r0 y).getD 0
  have hfz_eq : ∀ y : ZMod p, y ≠ 0 → r0 y = some (fz y) ∧ fz y ≠ 0 := by
    intro y hy
    cases h : r0 y with
    | none => exact absurd (hr0_inj (h.trans hd0.symm)) hy
    | some z =>
      have hfz : fz y = z := by simp [fz, h]
      exact ⟨by rw [hfz], fun hz => hr0_ne_zero y (by rw [h, ← hfz, hz])⟩
  have hfz_nz : ∀ i : Fin (p - 1), fz (nzVal p i) ≠ 0 := fun i =>
    (hfz_eq (nzVal p i) (nzVal_ne_zero i)).2
  let fFun : Fin (p - 1) → Fin (p - 1) := fun i => (nzEquiv p).symm ⟨fz (nzVal p i), hfz_nz i⟩
  have hf_bij : Function.Bijective fFun := by
    refine (Finite.injective_iff_bijective).mp fun i1 i2 h => ?_
    have h1 : fz (nzVal p i1) = fz (nzVal p i2) :=
      congrArg Subtype.val ((nzEquiv p).symm.injective h)
    have h2 : r0 (nzVal p i1) = r0 (nzVal p i2) :=
      (hfz_eq _ (nzVal_ne_zero i1)).1.trans
        ((congrArg some h1).trans (hfz_eq _ (nzVal_ne_zero i2)).1.symm)
    exact nzVal_injective (hr0_inj h2)
  have hgz_nz : ∀ i : Fin (p - 1), fz (nzVal p i) - nzVal p i ≠ 0 := by
    intro i h0
    have hd : nzVal p i ≠ 0 := nzVal_ne_zero i
    have hc : e.symm (L.1.1.val (e (some (-(nzVal p i)))) (e (some 0))) = some 0 := by
      rw [hshift (-(nzVal p i)) 0, zero_sub, neg_neg, (hfz_eq _ hd).1]
      simpa [sub_eq_add_neg] using congrArg some h0
    have hL1 : L.1.1.val (e (some (-(nzVal p i)))) (e (some 0)) = e (some 0) :=
      e.symm.injective (by simpa using hc)
    have hL2 : L.1.1.val 0 (e (some 0)) = e (some 0) := L.1.2.1 (e (some 0))
    have harg : e (some (-(nzVal p i))) = e none := (L.1.1.property.2 (e (some 0))).1 (hL1.trans hL2.symm)
    exact Option.some_ne_none _ (e.injective harg)
  let gFun : Fin (p - 1) → Fin (p - 1) :=
    fun i => (nzEquiv p).symm ⟨fz (nzVal p i) - nzVal p i, hgz_nz i⟩
  have hg_bij : Function.Bijective gFun := by
    refine (Finite.injective_iff_bijective).mp fun i1 i2 h => ?_
    have heq : fz (nzVal p i1) - nzVal p i1 = fz (nzVal p i2) - nzVal p i2 :=
      congrArg Subtype.val ((nzEquiv p).symm.injective h)
    have hc1 : e.symm (L.1.1.val (e (some (-(nzVal p i1)))) (e (some 0))) =
        some (fz (nzVal p i1) - nzVal p i1) := by
      rw [hshift _ 0, zero_sub, neg_neg, (hfz_eq _ (nzVal_ne_zero i1)).1]
      simp [sub_eq_add_neg]
    have hc2 : e.symm (L.1.1.val (e (some (-(nzVal p i2)))) (e (some 0))) =
        some (fz (nzVal p i2) - nzVal p i2) := by
      rw [hshift _ 0, zero_sub, neg_neg, (hfz_eq _ (nzVal_ne_zero i2)).1]
      simp [sub_eq_add_neg]
    have hL_eq := e.symm.injective (hc1.trans ((congrArg some heq).trans hc2.symm))
    have harg := Option.some.inj (e.injective ((L.1.1.property.2 (e (some 0))).1 hL_eq))
    exact nzVal_injective (neg_injective harg)
  refine ⟨Equiv.ofBijective fFun hf_bij, Equiv.ofBijective gFun hg_bij, fun i => ?_⟩
  change nzVal p (fFun i) - nzVal p i = nzVal p (gFun i)
  have hf_val : nzVal p (fFun i) = fz (nzVal p i) :=
    congrArg Subtype.val ((nzEquiv p).apply_symm_apply ⟨fz (nzVal p i), hfz_nz i⟩)
  have hg_val : nzVal p (gFun i) = fz (nzVal p i) - nzVal p i :=
    congrArg Subtype.val ((nzEquiv p).apply_symm_apply ⟨fz (nzVal p i) - nzVal p i, hgz_nz i⟩)
  rw [hf_val, hg_val]

private noncomputable def orthoToFixed {p : ℕ} [Fact p.Prime] (_hp2 : 2 < p)
    (F : OrthoPair p) : FixedRedLS p := by
  let e := optZModEquivFin p
  let g : Equiv.Perm (Fin (p - 1)) := Classical.choose F.2
  have hg : ∀ i, nzVal p (F.1 i) - nzVal p i = nzVal p (g i) := Classical.choose_spec F.2
  let r0 (d : ZMod p) : Option (ZMod p) :=
    if h : d = 0 then none else some (nzVal p (F.1 ((nzEquiv p).symm ⟨d, h⟩)))
  let gridOpt : Option (ZMod p) → Option (ZMod p) → Option (ZMod p)
    | none, j => j
    | some x, none => some x
    | some x, some y => (r0 (y - x)).map (· + x)
  have hrow_bij : ∀ a : Option (ZMod p), Function.Bijective (gridOpt a) := by
    intro a
    refine (Finite.injective_iff_bijective).mp ?_
    cases a with
    | none => intro j1 j2 h; exact h
    | some x =>
      intro j1 j2 h
      cases j1 with
      | none =>
        cases j2 with
        | none => rfl
        | some y2 =>
          exfalso
          simp only [gridOpt] at h
          by_cases hd : y2 - x = 0
          · simp [r0, hd] at h
          · simp only [r0, hd, ↓reduceDIte, Option.map_some, Option.some.injEq] at h
            have h0 : nzVal p (F.1 ((nzEquiv p).symm ⟨y2 - x, hd⟩)) = 0 := by linear_combination -h
            exact nzVal_ne_zero _ h0
      | some y1 =>
        cases j2 with
        | none =>
          exfalso
          simp only [gridOpt] at h
          by_cases hd : y1 - x = 0
          · simp [r0, hd] at h
          · simp only [r0, hd, ↓reduceDIte, Option.map_some, Option.some.injEq] at h
            have h0 : nzVal p (F.1 ((nzEquiv p).symm ⟨y1 - x, hd⟩)) = 0 := by linear_combination h
            exact nzVal_ne_zero _ h0
        | some y2 =>
          congr 1
          simp only [gridOpt] at h
          by_cases h1 : y1 - x = 0 <;> by_cases h2 : y2 - x = 0
          · exact (sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2).symm
          · simp [r0, h1, h2] at h
          · simp [r0, h1, h2] at h
          · simp only [r0, h1, h2, ↓reduceDIte, Option.map_some, Option.some.injEq] at h
            have heq := (nzEquiv p).symm.injective (F.1.injective (nzVal_injective (add_right_cancel h)))
            have hsub : y1 - x = y2 - x := congrArg Subtype.val heq
            exact sub_left_inj.mp hsub
  have hcol_bij : ∀ b : Option (ZMod p), Function.Bijective (fun a => gridOpt a b) := by
    intro b
    refine (Finite.injective_iff_bijective).mp ?_
    cases b with
    | none =>
      intro a1 a2 h
      cases a1 <;> cases a2 <;> exact h
    | some y =>
      intro a1 a2 h
      cases a1 with
      | none =>
        cases a2 with
        | none => rfl
        | some x2 =>
          exfalso
          simp only [gridOpt] at h
          by_cases hd : y - x2 = 0
          · simp [r0, hd] at h
          · simp only [r0, hd, ↓reduceDIte, Option.map_some, Option.some.injEq] at h
            let i2 := (nzEquiv p).symm ⟨y - x2, hd⟩
            have hi2 : nzVal p i2 = y - x2 := congrArg Subtype.val ((nzEquiv p).apply_symm_apply _)
            have hzero : nzVal p (g i2) = 0 := by
              rw [← hg i2, hi2]; linear_combination -h
            exact nzVal_ne_zero _ hzero
      | some x1 =>
        cases a2 with
        | none =>
          exfalso
          simp only [gridOpt] at h
          by_cases hd : y - x1 = 0
          · simp [r0, hd] at h
          · simp only [r0, hd, ↓reduceDIte, Option.map_some, Option.some.injEq] at h
            let i1 := (nzEquiv p).symm ⟨y - x1, hd⟩
            have hi1 : nzVal p i1 = y - x1 := congrArg Subtype.val ((nzEquiv p).apply_symm_apply _)
            have hzero : nzVal p (g i1) = 0 := by
              rw [← hg i1, hi1]; linear_combination h
            exact nzVal_ne_zero _ hzero
        | some x2 =>
          congr 1
          simp only [gridOpt] at h
          by_cases h1 : y - x1 = 0 <;> by_cases h2 : y - x2 = 0
          · exact (sub_eq_zero.mp h1).symm.trans (sub_eq_zero.mp h2)
          · simp [r0, h1, h2] at h
          · simp [r0, h1, h2] at h
          · simp only [r0, h1, h2, ↓reduceDIte, Option.map_some, Option.some.injEq] at h
            let i1 := (nzEquiv p).symm ⟨y - x1, h1⟩
            let i2 := (nzEquiv p).symm ⟨y - x2, h2⟩
            have hi1 : nzVal p i1 = y - x1 := congrArg Subtype.val ((nzEquiv p).apply_symm_apply _)
            have hi2 : nzVal p i2 = y - x2 := congrArg Subtype.val ((nzEquiv p).apply_symm_apply _)
            have hg_eq : nzVal p (g i1) = nzVal p (g i2) := by
              rw [← hg i1, ← hg i2, hi1, hi2]; linear_combination h
            have hi_eq : y - x1 = y - x2 := hi1 ▸ hi2 ▸ congrArg (nzVal p) (g.injective (nzVal_injective hg_eq))
            exact by linear_combination -hi_eq
  let L : RedLS (p + 1) :=
    ⟨⟨fun i j => e (gridOpt (e.symm i) (e.symm j)),
      fun i => e.bijective.comp ((hrow_bij (e.symm i)).comp e.symm.bijective),
      fun j => e.bijective.comp ((hcol_bij (e.symm j)).comp e.symm.bijective)⟩,
     ⟨fun j => by
        have h0 : e.symm 0 = none := by simp [e, optZModEquivFin]
        simp [h0, gridOpt],
      fun i => by
        dsimp only
        have h0 : e.symm 0 = none := by simp [e, optZModEquivFin]
        rw [h0]
        cases h : e.symm i with
        | none => exact (e.symm.injective (h.trans h0.symm)).symm
        | some x =>
          simp only [gridOpt]
          rw [← h, e.apply_symm_apply]⟩⟩
  refine ⟨L, fun a => ?_⟩
  apply Subtype.ext; apply Subtype.ext; funext i j
  rcases e.surjective i with ⟨oi, rfl⟩
  rcases e.surjective j with ⟨oj, rfl⟩
  cases oi with
  | none => simp [actRedLS, L, shiftPerm, e, gridOpt]
  | some x =>
    cases oj with
    | none => simp [actRedLS, L, shiftPerm, e, gridOpt]
    | some y =>
      dsimp only [actRedLS, L]
      rw [shiftPerm_some, shiftPerm_some]
      simp only [e, Equiv.symm_apply_apply, gridOpt]
      have hsub : (y + -a) - (x + -a) = y - x := by ring
      rw [hsub]
      cases r0 (y - x) with
      | none => simp [shiftPerm, optZModEquivFin]
      | some z =>
        simp only [Option.map_some, shiftPerm_some]
        congr 2; ring

private lemma orthoToFixed_apply_some {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (F : OrthoPair p) (x y : ZMod p) :
    (orthoToFixed hp2 F).1.1.val (optZModEquivFin p (some x)) (optZModEquivFin p (some y)) =
      optZModEquivFin p ((if h : y - x = 0 then none else
        some (nzVal p (F.1 ((nzEquiv p).symm ⟨y - x, h⟩)))).map (· + x)) := by
  simp only [orthoToFixed, Equiv.symm_apply_apply]

private lemma fixedToOrtho_spec {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (L : FixedRedLS p) (i : Fin (p - 1)) :
    L.1.1.val (optZModEquivFin p (some 0)) (optZModEquivFin p (some (nzVal p i))) =
      optZModEquivFin p (some (nzVal p ((fixedToOrtho hp2 L).1 i))) := by
  let e := optZModEquivFin p
  have h00 := fixed_row0_zero hp2 L
  have hval_ne0 : L.1.1.val (e (some 0)) (e (some (nzVal p i))) ≠ 0 := by
    intro h
    have heq := (L.1.1.property.1 (e (some 0))).1 (h.trans h00.symm)
    exact nzVal_ne_zero i (Option.some.inj (e.injective heq))
  have hsome : ∃ z : ZMod p, e.symm (L.1.1.val (e (some 0)) (e (some (nzVal p i)))) = some z := by
    cases h : e.symm (L.1.1.val (e (some 0)) (e (some (nzVal p i)))) with
    | none =>
      exfalso; apply hval_ne0
      apply e.symm.injective; simpa [e, optZModEquivFin] using h
    | some z => exact ⟨z, rfl⟩
  obtain ⟨z, hz⟩ := hsome
  have hget : (e.symm (L.1.1.val (e (some 0)) (e (some (nzVal p i))))).getD 0 = z := by simp [hz]
  have hf : nzVal p ((fixedToOrtho hp2 L).1 i) = z := by
    change (nzEquiv p ((nzEquiv p).symm ⟨(e.symm (L.1.1.val (e (some 0)) (e (some (nzVal p i))))).getD 0, _⟩)).1 = z
    rw [Equiv.apply_symm_apply]
    exact hget
  rw [hf]
  apply e.symm.injective
  simpa [e] using hz

private noncomputable def fixedEquivOrtho {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    FixedRedLS p ≃ OrthoPair p :=
  { toFun := fixedToOrtho hp2
    invFun := orthoToFixed hp2
    left_inv := fun L => by
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext i j
      let e := optZModEquivFin p
      rcases e.surjective i with ⟨oi, rfl⟩
      rcases e.surjective j with ⟨oj, rfl⟩
      cases oi with
      | none =>
        have h0 : e none = 0 := rfl
        rw [h0, L.1.2.1, (orthoToFixed hp2 (fixedToOrtho hp2 L)).1.2.1]
      | some x =>
        cases oj with
        | none =>
          have h0 : e none = 0 := rfl
          rw [h0, L.1.2.2, (orthoToFixed hp2 (fixedToOrtho hp2 L)).1.2.2]
        | some y =>
          have hL_shift : L.1.1.val (e (some x)) (e (some y)) =
              shiftPerm p x (L.1.1.val (e (some 0)) (e (some (y - x)))) := by
            have hfix := L.2 x
            have hval := congrFun (congrFun (congrArg (fun M : RedLS (p + 1) => M.1.val) hfix) (e (some x))) (e (some y))
            change shiftPerm p x (L.1.1.val (shiftPerm p (-x) (e (some x))) (shiftPerm p (-x) (e (some y)))) =
              L.1.1.val (e (some x)) (e (some y)) at hval
            rw [shiftPerm_some, shiftPerm_some, add_neg_cancel, ← sub_eq_add_neg] at hval
            exact hval.symm
          have hO_shift : (orthoToFixed hp2 (fixedToOrtho hp2 L)).1.1.val (e (some x)) (e (some y)) =
              shiftPerm p x ((orthoToFixed hp2 (fixedToOrtho hp2 L)).1.1.val (e (some 0)) (e (some (y - x)))) := by
            have hfix := (orthoToFixed hp2 (fixedToOrtho hp2 L)).2 x
            have hval := congrFun (congrFun (congrArg (fun M : RedLS (p + 1) => M.1.val) hfix) (e (some x))) (e (some y))
            change shiftPerm p x ((orthoToFixed hp2 (fixedToOrtho hp2 L)).1.1.val (shiftPerm p (-x) (e (some x))) (shiftPerm p (-x) (e (some y)))) = _ at hval
            rw [shiftPerm_some, shiftPerm_some, add_neg_cancel, ← sub_eq_add_neg] at hval
            exact hval.symm
          rw [hL_shift, hO_shift]
          congr 1
          set d := y - x
          by_cases hd : d = 0
          · rw [hd]
            have hO0 : (orthoToFixed hp2 (fixedToOrtho hp2 L)).1.1.val (e (some 0)) (e (some 0)) = 0 := by
              rw [orthoToFixed_apply_some]; simp [optZModEquivFin]
            rw [hO0, fixed_row0_zero hp2 L]
          · let idx := (nzEquiv p).symm ⟨d, hd⟩
            have hidx : nzVal p idx = d := congrArg Subtype.val ((nzEquiv p).apply_symm_apply ⟨d, hd⟩)
            rw [← hidx, fixedToOrtho_spec hp2 L idx, orthoToFixed_apply_some]
            have hne : nzVal p idx - 0 ≠ 0 := by simpa using nzVal_ne_zero idx
            simp only [hne, ↓reduceDIte, Option.map_some, add_zero]
            have hsub : (nzEquiv p).symm ⟨nzVal p idx - 0, hne⟩ = idx := by
              apply (nzEquiv p).injective; rw [Equiv.apply_symm_apply]; apply Subtype.ext; simp [nzEquiv]
            rw [hsub]
    right_inv := fun F => by
      apply Subtype.ext; apply Equiv.ext; intro i
      apply nzVal_injective
      have h1 := fixedToOrtho_spec hp2 (orthoToFixed hp2 F) i
      have h2 : (orthoToFixed hp2 F).1.1.val (optZModEquivFin p (some 0)) (optZModEquivFin p (some (nzVal p i))) =
          optZModEquivFin p (some (nzVal p (F.1 i))) := by
        rw [orthoToFixed_apply_some]
        have hne : nzVal p i - 0 ≠ 0 := by simpa using nzVal_ne_zero i
        simp only [hne, ↓reduceDIte, Option.map_some, add_zero]
        have hsub : (nzEquiv p).symm ⟨nzVal p i - 0, hne⟩ = i := by
          apply (nzEquiv p).injective; rw [Equiv.apply_symm_apply]; apply Subtype.ext; simp [nzEquiv]
        rw [hsub]
      exact Option.some.inj ((optZModEquivFin p).injective (h1.symm.trans h2)) }

private noncomputable def negNzPerm (p : ℕ) [Fact p.Prime] : Equiv.Perm (Fin (p - 1)) :=
  (nzEquiv p).trans
    (({ toFun := fun x => ⟨-x.1, neg_ne_zero.mpr x.2⟩
        invFun := fun x => ⟨-x.1, neg_ne_zero.mpr x.2⟩
        left_inv := fun x => Subtype.ext (neg_neg x.1)
        right_inv := fun x => Subtype.ext (neg_neg x.1) } : Equiv.Perm {x : ZMod p // x ≠ 0}).trans
      (nzEquiv p).symm)

private lemma sign_orthoToFixed {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (F : OrthoPair p) :
    sign (orthoToFixed hp2 F).1.1 =
      Equiv.Perm.sign (negNzPerm p) *
        Equiv.Perm.sign F.1 * Equiv.Perm.sign (Classical.choose F.2) := by
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let e := optZModEquivFin p
  let L := (orthoToFixed hp2 F).1.1
  let g := Classical.choose F.2
  have hg : ∀ i, nzVal p (F.1 i) - nzVal p i = nzVal p (g i) := Classical.choose_spec F.2
  let row (i : Fin (p + 1)) := Equiv.ofBijective _ (L.property.1 i)
  let col (j : Fin (p + 1)) := Equiv.ofBijective _ (L.property.2 j)
  -- Row 0 and Col 0 are identity (sign 1).
  have hrow0 : row 0 = 1 := Equiv.ext fun j => (orthoToFixed hp2 F).1.2.1 j
  have hcol0 : col 0 = 1 := Equiv.ext fun i => (orthoToFixed hp2 F).1.2.2 i
  -- Row e(some x) is conjugate to Row e(some 0) by shiftPerm p x!
  have hrow_x : ∀ x : ZMod p, Equiv.Perm.sign (row (e (some x))) = Equiv.Perm.sign (row (e (some 0))) := by
    intro x
    have hconj : row (e (some x)) =
        (shiftPerm p (-x)).trans ((row (e (some 0))).trans (shiftPerm p x)) := by
      apply Equiv.ext; intro j
      have hfix := (orthoToFixed hp2 F).2 x
      have hval := congrFun (congrFun (congrArg (fun M : RedLS (p + 1) => M.1.val) hfix) (e (some x))) j
      change shiftPerm p x (L.val (shiftPerm p (-x) (e (some x))) (shiftPerm p (-x) j)) = L.val (e (some x)) j at hval
      rw [shiftPerm_some, add_neg_cancel] at hval
      exact hval.symm
    rw [hconj, Equiv.Perm.sign_trans, Equiv.Perm.sign_trans]
    have hmul : Equiv.Perm.sign (shiftPerm p x) * Equiv.Perm.sign (shiftPerm p (-x)) = 1 := by
      rw [← map_mul]
      have : shiftPerm p x * shiftPerm p (-x) = 1 := by
        apply Equiv.ext; intro i
        change ((shiftPerm p (-x)).trans (shiftPerm p x)) i = i
        rw [← shiftPerm_add, add_neg_cancel, shiftPerm_zero]; rfl
      rw [this, map_one]
    calc Equiv.Perm.sign (shiftPerm p x) * Equiv.Perm.sign (row (e (some 0))) *
          Equiv.Perm.sign (shiftPerm p (-x))
        = (Equiv.Perm.sign (shiftPerm p x) * Equiv.Perm.sign (shiftPerm p (-x))) *
            Equiv.Perm.sign (row (e (some 0))) := by ac_rfl
      _ = Equiv.Perm.sign (row (e (some 0))) := by rw [hmul, one_mul]
  have hcol_y : ∀ y : ZMod p, Equiv.Perm.sign (col (e (some y))) = Equiv.Perm.sign (col (e (some 0))) := by
    intro y
    have hconj : col (e (some y)) =
        (shiftPerm p (-y)).trans ((col (e (some 0))).trans (shiftPerm p y)) := by
      apply Equiv.ext; intro i
      have hfix := (orthoToFixed hp2 F).2 y
      have hval := congrFun (congrFun (congrArg (fun M : RedLS (p + 1) => M.1.val) hfix) i) (e (some y))
      change shiftPerm p y (L.val (shiftPerm p (-y) i) (shiftPerm p (-y) (e (some y)))) = L.val i (e (some y)) at hval
      rw [shiftPerm_some, add_neg_cancel] at hval
      exact hval.symm
    rw [hconj, Equiv.Perm.sign_trans, Equiv.Perm.sign_trans]
    have hmul : Equiv.Perm.sign (shiftPerm p y) * Equiv.Perm.sign (shiftPerm p (-y)) = 1 := by
      rw [← map_mul]
      have : shiftPerm p y * shiftPerm p (-y) = 1 := by
        apply Equiv.ext; intro i
        change ((shiftPerm p (-y)).trans (shiftPerm p y)) i = i
        rw [← shiftPerm_add, add_neg_cancel, shiftPerm_zero]; rfl
      rw [this, map_one]
    calc Equiv.Perm.sign (shiftPerm p y) * Equiv.Perm.sign (col (e (some 0))) *
          Equiv.Perm.sign (shiftPerm p (-y))
        = (Equiv.Perm.sign (shiftPerm p y) * Equiv.Perm.sign (shiftPerm p (-y))) *
            Equiv.Perm.sign (col (e (some 0))) := by ac_rfl
      _ = Equiv.Perm.sign (col (e (some 0))) := by rw [hmul, one_mul]
  -- Unit ^ odd = unit!
  have hunit_odd : ∀ u : ℤˣ, u ^ p = u := fun u => by
    obtain ⟨k, hk⟩ := hp_odd
    rw [hk, pow_succ, pow_mul, sq, Int.units_mul_self, one_pow, one_mul]
  -- Product of row signs = sign (row (e (some 0))), product of col signs = sign (col (e (some 0)))!
  have hrow_prod : ∏ i : Fin (p + 1), Equiv.Perm.sign (row i) = Equiv.Perm.sign (row (e (some 0))) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (p + 1))), hrow0, map_one, one_mul]
    have hbij : ∏ i ∈ Finset.univ.erase (0 : Fin (p + 1)), Equiv.Perm.sign (row i) =
        ∏ x : ZMod p, Equiv.Perm.sign (row (e (some x))) := by
      refine (Finset.prod_bij (fun x _ => e (some x)) ?_ ?_ ?_ (fun _ _ => rfl)).symm
      · intro x _
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h; exact Option.some_ne_none x (e.injective (h.trans rfl))
      · intro x1 _ x2 _ h; exact Option.some.inj (e.injective h)
      · intro i hi
        rcases e.surjective i with ⟨o, rfl⟩
        cases o with
        | none => exact absurd rfl (Finset.ne_of_mem_erase hi)
        | some x => exact ⟨x, Finset.mem_univ x, rfl⟩
    rw [hbij]
    simp_rw [hrow_x]
    rw [Finset.prod_const, Finset.card_univ, ZMod.card, hunit_odd]
  have hcol_prod : ∏ j : Fin (p + 1), Equiv.Perm.sign (col j) = Equiv.Perm.sign (col (e (some 0))) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (p + 1))), hcol0, map_one, one_mul]
    have hbij : ∏ j ∈ Finset.univ.erase (0 : Fin (p + 1)), Equiv.Perm.sign (col j) =
        ∏ y : ZMod p, Equiv.Perm.sign (col (e (some y))) := by
      refine (Finset.prod_bij (fun y _ => e (some y)) ?_ ?_ ?_ (fun _ _ => rfl)).symm
      · intro y _
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h; exact Option.some_ne_none y (e.injective (h.trans rfl))
      · intro y1 _ y2 _ h; exact Option.some.inj (e.injective h)
      · intro j hj
        rcases e.surjective j with ⟨o, rfl⟩
        cases o with
        | none => exact absurd rfl (Finset.ne_of_mem_erase hj)
        | some y => exact ⟨y, Finset.mem_univ y, rfl⟩
    rw [hbij]
    simp_rw [hcol_y]
    rw [Finset.prod_const, Finset.card_univ, ZMod.card, hunit_odd]
  -- Now compare sign (row (e (some 0))) = -sign F.1 and sign (col (e (some 0))) = -sign (negNzPerm p) * sign g!
  -- Using the bijection Bool ⊕ Fin (p - 1) ≃ Fin (p + 1) sending inl false ↦ 0, inl true ↦ e (some 0), inr i ↦ e (some (nzVal p i))!
  let splitE : Bool ⊕ Fin (p - 1) ≃ Fin (p + 1) :=
    { toFun
        | Sum.inl false => 0
        | Sum.inl true => e (some 0)
        | Sum.inr i => e (some (nzVal p i))
      invFun k :=
        match e.symm k with
        | none => Sum.inl false
        | some x => if hx : x = 0 then Sum.inl true else Sum.inr ((nzEquiv p).symm ⟨x, hx⟩)
      left_inv s := by
        rcases s with (false | true) | i
        · simp [e, optZModEquivFin]
        · simp [e]
        · simp only [Equiv.symm_apply_apply, nzVal_ne_zero i, ↓reduceDIte]
          congr 1
          exact (nzEquiv p).symm_apply_apply i
      right_inv k := by
        rcases e.surjective k with ⟨o, rfl⟩
        cases o with
        | none => simp [e, optZModEquivFin]
        | some x =>
          by_cases hx : x = 0
          · subst hx; simp [e]
          · simp only [Equiv.symm_apply_apply, hx, ↓reduceDIte]
            congr 1; congr 1
            exact congrArg Subtype.val ((nzEquiv p).apply_symm_apply ⟨x, hx⟩) }
  have hrow_sign : Equiv.Perm.sign (row (e (some 0))) = -Equiv.Perm.sign F.1 := by
    let π := Equiv.sumCongr (Equiv.swap false true) F.1
    have hconj : Equiv.Perm.sign (row (e (some 0))) = Equiv.Perm.sign π := by
      refine Equiv.Perm.sign_eq_sign_of_equiv (row (e (some 0))) π splitE.symm ?_
      intro k
      rcases splitE.surjective k with ⟨s, rfl⟩
      rw [splitE.symm_apply_apply]
      apply splitE.injective
      rw [splitE.apply_symm_apply]
      rcases s with (false | true) | i
      · -- s = inl false: row (e (some 0)) 0 = e (some 0) = splitE (inl true)
        change L.val (e (some 0)) 0 = e (some 0)
        exact (orthoToFixed hp2 F).1.2.2 _
      · -- s = inl true: row (e (some 0)) (e (some 0)) = 0 = splitE (inl false)
        change L.val (e (some 0)) (e (some 0)) = 0
        rw [orthoToFixed_apply_some]
        simp [optZModEquivFin]
      · -- s = inr i: row (e (some 0)) (e (some (nzVal p i))) = e (some (nzVal p (F.1 i)))
        change L.val (e (some 0)) (e (some (nzVal p i))) = e (some (nzVal p (F.1 i)))
        rw [orthoToFixed_apply_some]
        have hne : nzVal p i - 0 ≠ 0 := by simpa using nzVal_ne_zero i
        simp only [hne, ↓reduceDIte, Option.map_some, add_zero]
        have hsub : (nzEquiv p).symm ⟨nzVal p i - 0, hne⟩ = i := by
          apply (nzEquiv p).injective; rw [Equiv.apply_symm_apply]; apply Subtype.ext; simp [nzEquiv]
        rw [hsub]
    rw [hconj]
    simp [π, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_swap (by decide : false ≠ true)]
  have hcol_sign : Equiv.Perm.sign (col (e (some 0))) =
      -(Equiv.Perm.sign (negNzPerm p) * Equiv.Perm.sign g) := by
    let π := Equiv.sumCongr (Equiv.swap false true) ((negNzPerm p).trans g)
    have hconj : Equiv.Perm.sign (col (e (some 0))) = Equiv.Perm.sign π := by
      refine Equiv.Perm.sign_eq_sign_of_equiv (col (e (some 0))) π splitE.symm ?_
      intro k
      rcases splitE.surjective k with ⟨s, rfl⟩
      rw [splitE.symm_apply_apply]
      apply splitE.injective
      rw [splitE.apply_symm_apply]
      rcases s with (false | true) | i
      · change L.val 0 (e (some 0)) = e (some 0)
        exact (orthoToFixed hp2 F).1.2.1 _
      · change L.val (e (some 0)) (e (some 0)) = 0
        rw [orthoToFixed_apply_some]
        simp [optZModEquivFin]
      · -- s = inr i: col (e (some 0)) (e (some (nzVal p i)))
        -- = e ((r0 (0 - nzVal p i)).map (+ nzVal p i))
        -- Let j = negNzPerm p i, so nzVal p j = -nzVal p i!
        -- Then r0 (nzVal p j) = some (nzVal p (F.1 j)), + nzVal p i = nzVal p (F.1 j) - nzVal p j = nzVal p (g j)!
        let j := negNzPerm p i
        have hj : nzVal p j = -nzVal p i := by
          change (nzEquiv p (negNzPerm p i)).1 = -nzVal p i
          simp [negNzPerm]; rfl
        change L.val (e (some (nzVal p i))) (e (some 0)) = e (some (nzVal p (g j)))
        rw [orthoToFixed_apply_some]
        have hne : 0 - nzVal p i ≠ 0 := by simpa using neg_ne_zero.mpr (nzVal_ne_zero i)
        simp only [hne, ↓reduceDIte, Option.map_some]
        congr 2
        have hidx : (nzEquiv p).symm ⟨0 - nzVal p i, hne⟩ = j := by
          apply (nzEquiv p).injective; apply Subtype.ext
          have := congrArg Subtype.val ((nzEquiv p).apply_symm_apply ⟨0 - nzVal p i, hne⟩)
          simpa [nzEquiv, hj] using this
        rw [hidx, ← hg j, hj]
        ring
    rw [hconj]
    simp [π, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_swap (by decide : false ≠ true),
      Equiv.Perm.sign_trans, mul_comm]
  change (∏ i, Equiv.Perm.sign (row i)) * (∏ j, Equiv.Perm.sign (col j)) = _
  rw [hrow_prod, hcol_prod, hrow_sign, hcol_sign]
  simp only [neg_mul_neg]
  dsimp only [g]
  ac_rfl

end DriskoAlonTarsi

theorem OMA.solution : OMA.R_opg_even_vs_odd_latin_squares_R1.H1 := by
  intro p he hp
  dsimp only
  intro hred
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := by
    have hge2 := hp.two_le
    by_contra! hle
    have : p = 2 := by omega
    subst this
    obtain ⟨k, hk⟩ := he
    omega
  have : NeZero p := ⟨by omega⟩
  classical
  have : Finite (OMA.S_opg_even_vs_odd_latin_squares.LatinSquare (p + 1)) :=
    inferInstanceAs (Finite {L : Fin (p + 1) → Fin (p + 1) → Fin (p + 1) //
      (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective fun i => L i j})
  let : Fintype (OMA.S_opg_even_vs_odd_latin_squares.LatinSquare (p + 1)) := Fintype.ofFinite _
  let : Fintype (DriskoAlonTarsi.RedLS (p + 1)) := Fintype.ofFinite _
  let : Fintype (DriskoAlonTarsi.FixedRedLS p) := Fintype.ofFinite _
  -- Step 1: Under `hred`, the sum of signs over all reduced Latin squares is 0 in `ZMod p`.
  have hsum_zero : ∑ L : DriskoAlonTarsi.RedLS (p + 1),
      ((OMA.S_opg_even_vs_odd_latin_squares.sign L.1 : ℤ) : ZMod p) = 0 := by
    have hsplit : ∑ L : DriskoAlonTarsi.RedLS (p + 1),
        ((OMA.S_opg_even_vs_odd_latin_squares.sign L.1 : ℤ) : ZMod p) =
        (∑ _L ∈ Finset.univ.filter (fun L : DriskoAlonTarsi.RedLS (p + 1) =>
          OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = 1), (1 : ZMod p)) +
        (∑ _L ∈ Finset.univ.filter (fun L : DriskoAlonTarsi.RedLS (p + 1) =>
          OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = -1), (-1 : ZMod p)) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun L : DriskoAlonTarsi.RedLS (p + 1) => OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = 1)
        (fun L : DriskoAlonTarsi.RedLS (p + 1) => ((OMA.S_opg_even_vs_odd_latin_squares.sign L.1 : ℤ) : ZMod p))]
      congr 1
      · exact Finset.sum_congr rfl fun L hL => by
          rw [(Finset.mem_filter.mp hL).2]; simp
      · have hfilt : Finset.univ.filter (fun L : DriskoAlonTarsi.RedLS (p + 1) =>
            ¬ OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = 1) =
            Finset.univ.filter (fun L : DriskoAlonTarsi.RedLS (p + 1) =>
            OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = -1) := by
          ext L
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases Int.units_eq_one_or (OMA.S_opg_even_vs_odd_latin_squares.sign L.1) with h | h <;>
            simp [h]
        rw [hfilt]
        exact Finset.sum_congr rfl fun L hL => by
          rw [(Finset.mem_filter.mp hL).2]; simp
    rw [hsplit]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
    have h1 : (Finset.univ.filter (fun L : DriskoAlonTarsi.RedLS (p + 1) =>
        OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = 1)).card =
        Nat.card {L : DriskoAlonTarsi.RedLS (p + 1) //
          OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h2 : (Finset.univ.filter (fun L : DriskoAlonTarsi.RedLS (p + 1) =>
        OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = -1)).card =
        Nat.card {L : DriskoAlonTarsi.RedLS (p + 1) //
          OMA.S_opg_even_vs_odd_latin_squares.sign L.1 = -1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1, h2, hred, add_neg_cancel]
  -- Step 2: By the `ZMod p` action, the sum equals the sum over fixed points, which is `±1 ≠ 0`!
  have hact0 : ∀ L : DriskoAlonTarsi.RedLS (p + 1), DriskoAlonTarsi.actRedLS 0 L = L := by
    intro L; apply Subtype.ext; apply Subtype.ext; funext i j
    simp [DriskoAlonTarsi.actRedLS, DriskoAlonTarsi.shiftPerm_zero]
  have hact_add : ∀ (a b : ZMod p) (L : DriskoAlonTarsi.RedLS (p + 1)),
      DriskoAlonTarsi.actRedLS (a + b) L = DriskoAlonTarsi.actRedLS a (DriskoAlonTarsi.actRedLS b L) := by
    intro a b L; apply Subtype.ext; apply Subtype.ext; funext i j
    have hneg : -(a + b) = -b + -a := by ring
    change DriskoAlonTarsi.shiftPerm p (a + b)
      (L.1.val (DriskoAlonTarsi.shiftPerm p (-(a + b)) i) (DriskoAlonTarsi.shiftPerm p (-(a + b)) j)) =
      DriskoAlonTarsi.shiftPerm p a (DriskoAlonTarsi.shiftPerm p b
        (L.1.val (DriskoAlonTarsi.shiftPerm p (-b) (DriskoAlonTarsi.shiftPerm p (-a) i))
          (DriskoAlonTarsi.shiftPerm p (-b) (DriskoAlonTarsi.shiftPerm p (-a) j))))
    rw [hneg, DriskoAlonTarsi.shiftPerm_add a b, DriskoAlonTarsi.shiftPerm_add (-b) (-a)]
    rfl
  have hsum_nz : ∑ L : DriskoAlonTarsi.RedLS (p + 1),
      ((OMA.S_opg_even_vs_odd_latin_squares.sign L.1 : ℤ) : ZMod p) =
      -((Equiv.Perm.sign (DriskoAlonTarsi.negNzPerm p) : ℤ) : ZMod p) := by
    calc ∑ L : DriskoAlonTarsi.RedLS (p + 1),
          ((OMA.S_opg_even_vs_odd_latin_squares.sign L.1 : ℤ) : ZMod p)
        = ∑ L : DriskoAlonTarsi.FixedRedLS p,
            ((OMA.S_opg_even_vs_odd_latin_squares.sign L.1.1 : ℤ) : ZMod p) :=
          DriskoAlonTarsi.sum_zmod_action_eq_fixed DriskoAlonTarsi.actRedLS hact0 hact_add
            (fun L => ((OMA.S_opg_even_vs_odd_latin_squares.sign L.1 : ℤ) : ZMod p))
            (fun a L => by rw [DriskoAlonTarsi.sign_actRedLS])
      _ = ∑ F : DriskoAlonTarsi.OrthoPair p,
            ((OMA.S_opg_even_vs_odd_latin_squares.sign (DriskoAlonTarsi.orthoToFixed hp2 F).1.1 : ℤ) : ZMod p) :=
          (Fintype.sum_equiv (DriskoAlonTarsi.fixedEquivOrtho hp2).symm _ _ (fun _ => rfl)).symm
      _ = ((Equiv.Perm.sign (DriskoAlonTarsi.negNzPerm p) : ℤ) : ZMod p) *
            ∑ F : DriskoAlonTarsi.OrthoPair p,
              (Equiv.Perm.sign F.1 : ZMod p) * (Equiv.Perm.sign (Classical.choose F.2) : ZMod p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun F _ => ?_
          rw [DriskoAlonTarsi.sign_orthoToFixed hp2 F]
          simp [Units.val_mul, mul_assoc]
      _ = ((Equiv.Perm.sign (DriskoAlonTarsi.negNzPerm p) : ℤ) : ZMod p) *
            ∑ f : Equiv.Perm (Fin (p - 1)),
              (if h : ∃ g : Equiv.Perm (Fin (p - 1)), ∀ i,
                  DriskoAlonTarsi.nzVal p (f i) - DriskoAlonTarsi.nzVal p i = DriskoAlonTarsi.nzVal p (g i) then
                (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign (Classical.choose h) : ZMod p)
              else 0) := by
          congr 1
          symm
          calc ∑ f : Equiv.Perm (Fin (p - 1)),
                (if h : ∃ g : Equiv.Perm (Fin (p - 1)), ∀ i,
                    DriskoAlonTarsi.nzVal p (f i) - DriskoAlonTarsi.nzVal p i = DriskoAlonTarsi.nzVal p (g i) then
                  (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign (Classical.choose h) : ZMod p)
                else 0)
              = ∑ f ∈ Finset.univ.filter (fun f : Equiv.Perm (Fin (p - 1)) =>
                  ∃ g : Equiv.Perm (Fin (p - 1)), ∀ i,
                    DriskoAlonTarsi.nzVal p (f i) - DriskoAlonTarsi.nzVal p i = DriskoAlonTarsi.nzVal p (g i)),
                  (if h : ∃ g : Equiv.Perm (Fin (p - 1)), ∀ i,
                      DriskoAlonTarsi.nzVal p (f i) - DriskoAlonTarsi.nzVal p i = DriskoAlonTarsi.nzVal p (g i) then
                    (Equiv.Perm.sign f : ZMod p) * (Equiv.Perm.sign (Classical.choose h) : ZMod p)
                  else 0) := by
                rw [Finset.sum_filter]
                refine Finset.sum_congr rfl fun f _ => ?_
                by_cases h : ∃ g : Equiv.Perm (Fin (p - 1)), ∀ i,
                    DriskoAlonTarsi.nzVal p (f i) - DriskoAlonTarsi.nzVal p i = DriskoAlonTarsi.nzVal p (g i) <;>
                  simp [h]
            _ = ∑ F : DriskoAlonTarsi.OrthoPair p,
                  (Equiv.Perm.sign F.1 : ZMod p) * (Equiv.Perm.sign (Classical.choose F.2) : ZMod p) := by
                refine Finset.sum_bij (fun f hf => ⟨f, (Finset.mem_filter.mp hf).2⟩)
                  (fun _ _ => Finset.mem_univ _)
                  (fun _ _ _ _ h => congrArg Subtype.val h)
                  (fun F _ => ⟨F.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.2⟩, rfl⟩)
                  (fun f hf => by simp [(Finset.mem_filter.mp hf).2])
      _ = -((Equiv.Perm.sign (DriskoAlonTarsi.negNzPerm p) : ℤ) : ZMod p) := by
          rw [DriskoAlonTarsi.sum_ortho_pairs_eq_neg_one p hp2, mul_neg_one]
  rw [hsum_nz] at hsum_zero
  have hu_zero : ((Equiv.Perm.sign (DriskoAlonTarsi.negNzPerm p) : ℤ) : ZMod p) = 0 :=
    neg_eq_zero.mp hsum_zero
  rcases Int.units_eq_one_or (Equiv.Perm.sign (DriskoAlonTarsi.negNzPerm p)) with hu | hu
  · rw [hu] at hu_zero; simp at hu_zero
  · rw [hu] at hu_zero; simp at hu_zero


