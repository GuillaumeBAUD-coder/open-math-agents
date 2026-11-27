import FormalConjectures.OEIS.«256544»
import Mathlib

/-!
# Sums of three rounded triangular numbers

Credit: @marcusbuffett

Three iterations of the interval bound in peel give a representation whenever
128n ≤ m⁷. Multiplication of m by an odd square preserves every represented
value. Gauss’s theorem and a finite residue test settle all inputs for the
base moduli 1, 3, 5, 13, and 15. The hypotheses therefore concern only larger
n at the remaining moduli, after removing all odd square factors.

The proof of Ankeny's squarefree three-square theorem below is adapted from
SumsThreeSquares/MinkowskiConvex.lean and SumsThreeSquares/SumThreeSquares.lean
in https://github.com/pitmonticone/SumsThreeSquares, commit
b2e98cd1585300cafcc237ab5daacde565089fba, used under the Apache License 2.0.
The two source files are by Abel Doñate Muñoz and Bhavik Mehta.

The residue argument for small moduli is the triangular analogue of the
criterion of Holdum, Klausen and Rasmussen (https://arxiv.org/abs/1507.00369).
See also Sun's Conjecture 1.1(ii) and Theorem 1.1(v)
(https://arxiv.org/abs/1504.01608).
-/

namespace RoundedTriangular

open MeasureTheory Module Submodule

private lemma classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : 2 ^ n < volume s) :
    ∃ x ≠ 0, (x ∈ s) ∧ (∀ i : Fin n, (∃ (m : ℤ), m = x i)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have : Countable (span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (span ℤ (Set.range b)))
  have fund : IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain' b volume
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [(ZSpan.fundamentalDomain_ae_parallelepiped b volume).measure_eq]
    exact (EuclideanSpace.basisFun _ _).volume_parallelepiped
  have hmeas : volume (ZSpan.fundamentalDomain b) *
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) < volume s := by
    simpa [hF, finrank_euclideanSpace_fin] using h
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv hmeas
  refine ⟨x, fun h0 => hx_ne (Subtype.ext h0), hx_mem, fun i => ?_⟩
  obtain ⟨m, hm⟩ := (b.mem_span_iff_repr_mem ℤ x.1).mp x.2 i
  exact ⟨m, by simpa [b, EuclideanSpace.basisFun_repr] using hm⟩

open scoped BigOperators Real Int Nat Classical Pointwise

noncomputable section


/-- If the `p`-adic valuation of `n` is odd, then `p ∣ n` (since `padicValInt p n = 0`
when `p ∤ n`, and `0` is not odd). -/
private lemma dvd_of_odd_padicValInt {p : ℕ} {n : ℤ}
    (h : Odd (padicValInt p n)) : (p : ℤ) ∣ n := by
  by_contra hpn
  rw [padicValInt.eq_zero_of_not_dvd hpn] at h
  exact absurd h (by decide)

/-- If `p` is prime and `p ∣ k`, then `jacobiSym k p ≠ 1` (it is in fact `0`). -/
private lemma not_jacobiSym_eq_one_of_dvd {p : ℕ} (hp : Nat.Prime p) {k : ℤ} (hpk : (p : ℤ) ∣ k) :
    jacobiSym k p ≠ 1 := by
  rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd hpk, jacobiSym.zero_left hp.one_lt]
  decide

/-
There exists a prime `q` with `q ≡ 1 (mod 4)` and `(-2q/p) = 1` for all prime factors `p` of `m`.
-/

/-- For any natural `a` and any odd natural `p`, some shift `a + k * p` is `≡ 1 (mod 4)`.
(Since `gcd(p, 4) = 1`, multiplication by `p` is a permutation on `ZMod 4`.) -/
private lemma exists_shift_mod4_eq_one (a : ℕ) {p : ℕ} (hp_odd : Odd p) :
    ∃ k : ℕ, (a + k * p) % 4 = 1 := by
  have hp2 : p ^ 2 % 4 = 1 := by
    have : (p : ℤ) ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd (by exact_mod_cast hp_odd)
    exact_mod_cast this
  have heq : a + (3 * a + 1) * p * p = a + (3 * a + 1) * p ^ 2 := by ring
  exact ⟨(3 * a + 1) * p, by grind [Nat.add_mod, Nat.mul_mod]⟩

/-- For an odd prime `p`, there is a natural `a ≡ 1 (mod 4)` coprime to `p` with `-2 * a`
a quadratic residue modulo `p`. Witness: `(p-1)/2` (giving `-2 * (p-1)/2 ≡ 1 (mod p)`),
shifted by a multiple of `p` to fix the residue modulo 4. -/
private lemma exists_residue_neg_two_qr_mod_odd_prime (p : ℕ) (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2) :
    ∃ a : ℕ, jacobiSym (-2 * a) p = 1 ∧ a % p ≠ 0 ∧ a % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hp.odd_of_ne_two hp_ne_two
  have hk_lt : k < 2 * k + 1 ∧ k ≠ 0 := by have := hp.two_le; omega
  obtain ⟨ks, hks⟩ := exists_shift_mod4_eq_one k ⟨k, rfl⟩
  refine ⟨k + ks * (2 * k + 1), ?_, ?_, hks⟩
  · have h1 : (-2 * ((k + ks * (2 * k + 1) : ℕ) : ℤ)) =
        1 + ↑(2 * k + 1) * (-1 - 2 * ks) := by push_cast; ring
    rw [jacobiSym.mod_left, h1, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
      jacobiSym.one_left]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk_lt.1]; exact hk_lt.2

/-- Chinese Remainder Theorem over the prime factors of an odd natural number `m`,
simultaneously achieving `≡ 1 (mod 4)`. Given per-prime residue data `a p`, we can find
a single `c` satisfying all the congruences `c ≡ a p (mod p)` for `p ∈ primeFactors m`
together with `c ≡ 1 (mod 4)`. -/
private lemma exists_crt_primeFactors_and_mod4 {m : ℕ} (hm_odd : Odd m) (a : ℕ → ℕ) :
    ∃ c : ℕ, (∀ p : ℕ, p ∣ m → Nat.Prime p → c ≡ a p [MOD p]) ∧ c ≡ 1 [MOD 4] := by
  have hodd : ∀ p ∈ m.primeFactors, Odd p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd'.resolve_left fun h2 => by
      subst h2
      have h2dvd := Nat.dvd_of_mem_primeFactors hp
      have := Nat.odd_iff.mp hm_odd
      omega
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset (fun p => if p = 4 then 1 else a p) id
    (insert 4 m.primeFactors)
    (fun p hp => by rcases Finset.mem_insert.mp hp with rfl | hp
                    · norm_num
                    · exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun p hp r hr hpr => by
      rcases Finset.mem_insert.mp hp with rfl | hp <;>
        rcases Finset.mem_insert.mp hr with rfl | hr
      · exact absurd rfl hpr
      · exact Nat.Coprime.pow_left 2 (hodd r hr).coprime_two_left
      · exact Nat.coprime_comm.mp (Nat.Coprime.pow_left 2 (hodd p hp).coprime_two_left)
      · exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hr)).mpr hpr)
  refine ⟨c, fun p hp_dvd hp_prime => ?_, by simpa using hc 4 (Finset.mem_insert_self _ _)⟩
  have hp_in : p ∈ insert 4 m.primeFactors := Finset.mem_insert_of_mem
    (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hm_odd.pos.ne'⟩)
  have hp_ne_4 : p ≠ 4 := fun h => absurd hp_prime (h ▸ by decide)
  simpa [if_neg hp_ne_4] using hc p hp_in

/-- Dirichlet's theorem, packaged as an existence statement: for `a : ℕ` coprime to `N > 0`,
there is a prime in the same residue class as `a` modulo `N`. -/
private lemma exists_prime_eq_mod {a N : ℕ} (hN : 0 < N) (hcop : Nat.Coprime a N) :
    ∃ q : ℕ, Nat.Prime q ∧ q % N = a % N := by
  have : NeZero N := ⟨hN.ne'⟩
  have h_dir : Set.Infinite {q : ℕ | Nat.Prime q ∧ q % N = a % N} := by
    convert Nat.infinite_setOfPred_prime_and_eq_mod (q := N) (a := (a : ZMod N))
      ((ZMod.isUnit_iff_coprime a N).mpr hcop) using 1
    norm_num [← ZMod.natCast_eq_natCast_iff']
  exact h_dir.nonempty

private lemma exists_prime_aux (m : ℕ) (hm_mod : m % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  have ha_p : ∀ p : ℕ, p ∣ m → Nat.Prime p → ∃ a_p : ℕ,
      jacobiSym (-2 * a_p) p = 1 ∧ a_p % p ≠ 0 ∧ a_p % 4 = 1 := fun p hp hp_prime =>
    exists_residue_neg_two_qr_mod_odd_prime p hp_prime fun h => by
      subst h; have : 2 ∣ m := hp; omega
  choose! a ha using ha_p
  obtain ⟨a_crt, ha_crt_p, ha_crt_4⟩ := exists_crt_primeFactors_and_mod4 hm_odd a
  have ha_crt_cop : Nat.Coprime a_crt (4 * m) := by
    refine Nat.Coprime.mul_right (ha_crt_4.gcd_eq.trans (by norm_num)) ?_
    refine Nat.coprime_of_dvd' fun k hk hk₁ hk₂ => ?_
    grind [Nat.ModEq, Nat.dvd_iff_mod_eq_zero]
  obtain ⟨q, hq_prime, hq_mod⟩ := exists_prime_eq_mod (by omega : 0 < 4 * m) ha_crt_cop
  refine ⟨q, hq_prime, ?_, fun p hp hp_prime => ?_⟩
  · rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 4 m), hq_mod,
        Nat.mod_mod_of_dvd _ (dvd_mul_right 4 m)]
    exact ha_crt_4
  · have h_qap : (q : ℤ) ≡ a p [ZMOD p] :=
      (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hp 4))
        (Int.natCast_modEq_iff.mpr hq_mod)).trans
        (Int.natCast_modEq_iff.mpr (ha_crt_p p hp hp_prime))
    rw [jacobiSym.mod_left (-2 * (q : ℤ)), (h_qap.mul_left (-2)), ← jacobiSym.mod_left]
    grind

/-
If `m ≡ 3 (mod 8)` is squarefree, `q ≡ 1 (mod 4)` is prime, and `(-2q/p) = 1` for all `p | m`,
then `(-m/q) = 1`.
-/
private lemma exists_odd_sq_mod_prime_of_jacobi_eq_one (m q : ℕ) (hq_prime : Nat.Prime q)
    (hq_mod : q % 4 = 1) (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b : ℤ, b ^ 2 ≡ -↑m [ZMOD ↑q] ∧ b % 2 = 1 := by
  have := Fact.mk hq_prime
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one h_jacobi
  have hb₀ : (x.val : ℤ) ^ 2 ≡ -(m : ℤ) [ZMOD q] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  by_cases hb₀_odd : (x.val : ℤ) % 2 = 1
  · exact ⟨x.val, hb₀, hb₀_odd⟩
  · refine ⟨x.val + q, (Int.add_modEq_right.pow 2).trans hb₀, ?_⟩
    have hq_odd : (q : ℤ) % 2 = 1 := mod_cast hq_prime.eq_two_or_odd.resolve_left (by grind)
    grind

private lemma jacobi_neg_m_q (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_mod : q % 4 = 1)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    jacobiSym (-m) q = 1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  have h_qm : jacobiSym (-2 * q) m = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_pmap.mp hx
    have hp_prime := Nat.prime_of_mem_primeFactorsList hp
    have := Fact.mk hp_prime
    simpa [jacobiSym, Nat.primeFactorsList_prime hp_prime] using
      h_jacobi p (Nat.dvd_of_mem_primeFactorsList hp) hp_prime
  have h_qm' : jacobiSym q m = jacobiSym (-2) m := by
    grind [jacobiSym.mul_left, Int.mul_eq_one_iff_eq_one_or_neg_one]
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hq_odd, ZMod.χ₄_nat_one_mod_four hq_mod, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' hm_odd hq_mod, h_qm',
      jacobiSym.mod_right _ hm_odd]
  norm_num [hm_mod]

/-
There exist integers $b$ and $h$ such that $b$ is odd and $b^2 - 4qh = -m$.
-/
private lemma exists_b_h (m : ℕ) (q : ℕ) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q) (hq_mod : q % 4 = 1)
    (h_jacobi : jacobiSym (-m) q = 1) :
    ∃ b h : ℤ, b^2 - 4 * q * h = -m := by
  obtain ⟨b, hb_mod_q, hb_odd⟩ :=
    exists_odd_sq_mod_prime_of_jacobi_eq_one m q hq_prime hq_mod h_jacobi
  have h_cop : ((4 : ℤ).natAbs).Coprime ((q : ℤ).natAbs) :=
    Nat.coprime_comm.mp (hq_prime.coprime_iff_not_dvd.mpr fun (h : q ∣ 4) => by
      have := Nat.le_of_dvd (by decide) h; have := hq_prime.two_le; omega)
  have hb_mod : b ^ 2 ≡ -↑m [ZMOD (4 * ↑q : ℤ)] :=
    (Int.modEq_and_modEq_iff_modEq_mul h_cop).mp
      ⟨by grind [Int.ModEq, Int.sq_mod_four_eq_one_of_odd], hb_mod_q⟩
  exact ⟨b, (b^2 + m) / (4 * q),
    by have := Int.ediv_mul_cancel hb_mod.symm.dvd; grind⟩

/-
There exists an integer $t$ such that $2q t^2 \equiv -1 \pmod m$.
-/
/-- Per-prime existence: for a prime `p` with `2q` coprime to `p` and `(-2q/p) = 1`, there is
an integer `t_p` with `2q·t_p² ≡ -1 (mod p)`. The witness is `s · (2q)⁻¹` where `s² ≡ -2q`. -/
private lemma exists_t_local_of_jacobi (p q : ℕ) (hp : Nat.Prime p)
    (hp_cop : Nat.Coprime (2 * q) p) (hjac : jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, 2 * q * t ^ 2 ≡ -1 [ZMOD p] := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one hjac
  have hs : (x.val : ℤ) ^ 2 ≡ -2 * q [ZMOD p] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  obtain ⟨inv_2q, hinv_2q⟩ : ∃ inv_2q : ℤ, (2 * q : ℤ) * inv_2q ≡ 1 [ZMOD p] :=
    Int.mod_coprime hp_cop
  refine ⟨x.val * inv_2q, ?_⟩
  convert hs.mul_left (2 * q * inv_2q ^ 2) |>.trans ?_ using 1 <;> ring_nf
  convert (hinv_2q.pow 2).neg using 1 <;> ring

private lemma exists_t (m : ℕ) (q : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 3) (hq_prime : Nat.Prime q)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → jacobiSym (-2 * q) p = 1) :
    ∃ t : ℤ, (2 * q : ℤ) * t^2 ≡ -1 [ZMOD m] := by
  have h_tp : ∀ p ∈ Nat.primeFactors m, ∃ t_p : ℤ, 2 * q * t_p ^ 2 ≡ -1 [ZMOD (p : ℤ)] := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    refine exists_t_local_of_jacobi p q hp_prime (Nat.Coprime.mul_left
      (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2p => by
        have : 2 ∣ m := dvd_trans h2p hpm; omega)
      ((Nat.coprime_primes hq_prime hp_prime).mpr fun heq => by
        subst heq
        exact not_jacobiSym_eq_one_of_dvd hq_prime (by simp) (h_jacobi q hpm hq_prime)))
      (h_jacobi p hpm hp_prime)
  choose! t ht using h_tp
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset (fun p => ((t p).emod p).toNat) id
    m.primeFactors (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun _ hp _ hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  refine ⟨c, ?_⟩
  rw [Int.modEq_iff_dvd, ← Nat.prod_primeFactors_of_squarefree hm_sq, Nat.cast_prod]
  refine Finset.prod_dvd_of_coprime
    (fun _ hp _ hq hpq => ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq).cast)
    (fun p hp => Int.modEq_iff_dvd.mp ?_)
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have h1 : (c : ℤ) ≡ ((t p).emod p).toNat [ZMOD (p : ℤ)] := by exact_mod_cast hc p hp
  have hcp : (c : ℤ) ≡ t p [ZMOD (p : ℤ)] :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ hp_ne) ▸ h1).trans (Int.emod_emod_of_dvd _ dvd_rfl)
  exact ((hcp.pow 2).mul_left _).trans (ht p hp)

private lemma quad_form_decomposition (m q : ℕ) (b h x y : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * q * h = -m) :
    (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y) ^ 2 +
      (Real.sqrt m / Real.sqrt (2 * q) * y) ^ 2 =
      2 * ((q : ℝ) * x ^ 2 + (b : ℝ) * x * y + (h : ℝ) * y ^ 2) := by
  have hb2 : (b : ℝ) ^ 2 = 4 * q * h - m :=
    by exact_mod_cast (by grind : (b : ℤ) ^ 2 = 4 * q * h - m)
  field_simp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * q),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  linear_combination (y : ℝ)^2 * hb2

private lemma exists_lattice_xyz_lt_two_m (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    ((2 * t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z)^2 +
      (Real.sqrt (2 * q) * x + (b : ℝ) / Real.sqrt (2 * q) * y)^2 +
      (Real.sqrt m / Real.sqrt (2 * q) * y)^2 < 2 * m := by
  let linear_map_M (m q : ℕ) (t b : ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    Matrix.toLin' (!![
      2 * t * q, t * b, m;
      Real.sqrt (2 * q), b / Real.sqrt (2 * q), 0;
      0, Real.sqrt m / Real.sqrt (2 * q), 0])

  have det_linear_map_M (m q : ℕ) (t b : ℤ) (hq : 0 < q) :
      LinearMap.det (linear_map_M m q t b) = m * Real.sqrt m := by
    unfold linear_map_M
    simp [Matrix.det_fin_three]
    rw [mul_assoc, mul_div_cancel₀ _ (by positivity)]

  let linear_map_M_euclidean (m q : ℕ) (t b : ℤ) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap ∘ₗ
      (linear_map_M m q t b) ∘ₗ (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap

  have det_linear_map_M_euclidean (m q : ℕ) (t b : ℤ) (hq : 0 < q) :
      LinearMap.det (linear_map_M_euclidean m q t b) = m * Real.sqrt m :=
    (LinearMap.det_conj (linear_map_M m q t b)
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv).trans (det_linear_map_M m q t b hq)

  /- Component formulas for the linear map `linear_map_M_euclidean`. -/
  have linear_map_M_euclidean_apply (m q : ℕ) (t b : ℤ) (x : EuclideanSpace ℝ (Fin 3)) :
      (linear_map_M_euclidean m q t b x) 0 = 2 * t * q * x 0 + t * b * x 1 + m * x 2 ∧
      (linear_map_M_euclidean m q t b x) 1 =
        Real.sqrt (2 * q) * x 0 + b / Real.sqrt (2 * q) * x 1 ∧
      (linear_map_M_euclidean m q t b x) 2 = Real.sqrt m / Real.sqrt (2 * q) * x 1 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      (simp [linear_map_M_euclidean, linear_map_M, Matrix.toLin'_apply, Matrix.vecHead,
        Matrix.vecTail]; try ring)

  /- Minkowski volume certificate: the preimage under `linear_map_M_euclidean` of the ball
  of radius `√(2m)` has volume strictly greater than `2^3 = 8`. -/
  have vol_preimage_ball_gt_eight (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
      (2 : ENNReal) ^ 3 < MeasureTheory.volume
        ((linear_map_M_euclidean m q t b) ⁻¹'
          Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
    have hdet_ne : LinearMap.det (linear_map_M_euclidean m q t b) ≠ 0 := by
      rw [det_linear_map_M_euclidean m q t b hq]; positivity
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet_ne,
        det_linear_map_M_euclidean m q t b hq, EuclideanSpace.volume_ball_fin_three,
        abs_inv, abs_of_nonneg (by positivity),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        (by norm_num : ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8),
        ENNReal.ofReal_lt_ofReal_iff (by positivity),
        (by rw [pow_succ, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m),
            Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; ring :
          (Real.sqrt (2 * m)) ^ 3 = 2 * Real.sqrt 2 * ((m : ℝ) * Real.sqrt m))]
    field_simp
    nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
      (by positivity : 0 < (m : ℝ) * Real.sqrt m)]

  obtain ⟨x, hx0, hxs, h⟩ :=
    classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (fun _ hx => by simpa using hx)
      (Convex.linear_preimage (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) _)
      (vol_preimage_ball_gt_eight m q t b hm hq)
  choose R hR using h
  refine ⟨R 0, R 1, R 2, ?_, ?_⟩
  · contrapose! hx0
    ext i; rw [← hR i]; fin_cases i <;> aesop
  · obtain ⟨h0, h1, h2⟩ := linear_map_M_euclidean_apply m q t b x
    have h_norm_sq : (‖linear_map_M_euclidean m q t b x‖ ^ 2 : ℝ) < 2 * m := by
      have : ‖linear_map_M_euclidean m q t b x‖ < Real.sqrt (2 * m) := by simpa using hxs
      nlinarith [norm_nonneg (linear_map_M_euclidean m q t b x),
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m)]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2] at h_norm_sq
    convert h_norm_sq using 1
    push_cast [hR 0, hR 1, hR 2]
    ring

private lemma rst_modEq_zero (m q : ℕ) (t b h x y z : ℤ)
    (hqt : 2 * q * t^2 ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * q * h = -m) :
    (2 * ↑t * ↑q * ↑x + ↑t * ↑b * ↑y + ↑m * ↑z) ^ 2 +
      2 * (↑q * ↑x ^ 2 + ↑b * ↑x * ↑y + ↑h * ↑y ^ 2) ≡ 0 [ZMOD m] := by
  obtain ⟨c, hc⟩ : (m : ℤ) ∣ 2 * q * t ^ 2 + 1 := by
    simpa [neg_sub] using (Int.modEq_iff_dvd.mp hqt).neg_right
  rw [Int.modEq_zero_iff_dvd]
  refine ⟨c * (2 * q * x ^ 2 + 2 * b * x * y + 2 * h * y ^ 2) +
    (4 * t * q * x * z + 2 * t * b * y * z + m * z ^ 2 - t ^ 2 * y ^ 2), ?_⟩
  linear_combination (2 * q * x ^ 2 + 2 * b * x * y + 2 * h * y ^ 2) * hc + t ^ 2 * y ^ 2 * hbqm

/-- The integer binary quadratic form `q·x² + b·x·y + h·y²` is nonnegative when its
discriminant is `-m < 0` (i.e. negative definite `-Δ`) and `q > 0`. -/
private lemma quadform_nonneg {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (x y : ℤ) :
    0 ≤ (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 := by
  nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y), sq_nonneg (y : ℤ), hbqm,
    Int.natCast_nonneg m]

/-- The binary form `q·x² + b·x·y + h·y²` with `q > 0` and discriminant `-m < 0` has only the
trivial zero: `qf = 0 ↔ x = y = 0`. (Reverse direction is trivial; stated as `x = 0 ∧ y = 0`.) -/
private lemma quadform_eq_zero_imp_xy_zero {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) {x y : ℤ}
    (h_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · exact ⟨by subst hy; nlinarith [sq_nonneg x, hq, h_zero], hy⟩
  · exact absurd h_zero <| by
      nlinarith [sq_nonneg (2 * (q:ℤ)*x + b*y), mul_self_pos.mpr hy, hbqm, Int.natCast_pos.mpr hm]

/-- A nonnegative integer `n ≡ 0 (mod m)` with `n < 2m` is either `0` or `m`. -/
private lemma eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul {m : ℤ} (hm : 0 < m)
    {n : ℤ} (h_nn : 0 ≤ n) (h_mod : n ≡ 0 [ZMOD m]) (h_lt : n < 2 * m) :
    n = 0 ∨ n = m := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h_mod
  have hk0 : 0 ≤ k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  interval_cases k <;> grind

/-- The discriminant `b² - 4qh` of an integer binary quadratic form cannot equal `-1`:
squares mod 4 are in `{0, 1}` but `-1 ≡ 3 (mod 4)`. -/
private lemma discriminant_ne_neg_one (q : ℕ) (b h : ℤ) : b ^ 2 - 4 * (q : ℤ) * h ≠ -1 := by
  intro hcon
  have hcon' : b ^ 2 = 4 * ((q : ℤ) * h) - 1 := by linarith [hcon]
  rcases Int.even_or_odd b with ⟨k, rfl⟩ | hodd
  · grind
  · grind [Int.sq_mod_four_eq_one_of_odd]

private lemma exists_Rv_from_Minkowski (m q : ℕ) (t b h : ℤ) (hm : 0 < m) (hq : 0 < q)
    (hqt : 2 * q * t ^ 2 ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) :
    ∃ (x y : ℤ) (R : ℤ) (v : ℕ),
      (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2 ∧
      R ^ 2 + 2 * (v : ℤ) = (m : ℤ) ∧
      0 < v := by
  obtain ⟨x, y, z, hne, hlt⟩ := exists_lattice_xyz_lt_two_m m q t b hm hq
  have hqf_nn : 0 ≤ (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 := quadform_nonneg hq hbqm x y
  -- `R² + 2·qf` is nonneg, `< 2m`, and `≡ 0 (mod m)`, hence `∈ {0, m}`.
  have h_lt : (2 * t * q * x + t * b * y + m * z : ℤ) ^ 2 +
      2 * ((q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2) < 2 * m := by
    have hqfd := quad_form_decomposition m q b h x y hq (by exact_mod_cast hbqm)
    have : ((2 * t * q * x + t * b * y + m * z : ℤ) : ℝ) ^ 2 +
        2 * (((q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 : ℤ) : ℝ) < 2 * m := by push_cast; linarith
    exact_mod_cast this
  have h_cases := eq_zero_or_eq_of_nonneg_modEq_zero_lt_two_mul
    (by exact_mod_cast hm : (0 : ℤ) < m) (by positivity)
    (rst_modEq_zero m q t b h x y z hqt hbqm) h_lt
  rcases h_cases with h_case1 | h_case2
  · have h_qf0 : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * t * q * x + t * b * y + m * z : ℤ)]
    obtain ⟨rfl, rfl⟩ := quadform_eq_zero_imp_xy_zero hq hm hbqm h_qf0
    obtain rfl : z = 0 :=
      (mul_eq_zero.mp (by nlinarith : (m : ℤ) * z = 0)).resolve_left (by exact_mod_cast hm.ne')
    exact absurd rfl hne
  · refine ⟨x, y, 2 * t * q * x + t * b * y + m * z,
      Int.toNat (q * x ^ 2 + b * x * y + h * y ^ 2), ?_, ?_, ?_⟩ <;> norm_num
    · exact hqf_nn
    · grind
    · contrapose! hne
      have hqf_zero : (q : ℤ) * x ^ 2 + b * x * y + h * y ^ 2 = 0 := by
        nlinarith [sq_nonneg (2 * (q : ℤ) * x + b * y)]
      obtain ⟨rfl, rfl⟩ := quadform_eq_zero_imp_xy_zero hq hm hbqm hqf_zero
      simp_all
      rcases m with _ | _ | m <;> norm_num at *
      · exact absurd hbqm (discriminant_ne_neg_one q b h)
      · have hz : z ^ 2 * (m + 1 + 1) = 1 := by nlinarith
        nlinarith [hz]

private lemma jacobi_neg_d_of_dvd_sq_add (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2) (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (hp_not_dvd_b : ¬ (p : ℤ) ∣ b') :
    jacobiSym (-d) p = 1 := by
  have := Fact.mk hp
  rw [jacobiSym]
  norm_num [Nat.primeFactorsList_prime hp]
  simp_all [← ZMod.intCast_zmod_eq_zero_iff_dvd, legendreSym.eq_one_iff]
  use a / b'
  grind

private lemma jacobi_neg_d_of_odd_padicVal (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (h_odd_val : Odd (padicValInt p (a ^ 2 + d * b' ^ 2))) :
    jacobiSym (-d) p = 1 := by
  induction' n : Int.natAbs a + Int.natAbs b' using Nat.strong_induction_on with n ih
    generalizing a b'
  by_cases h_div_b' : (p : ℤ) ∣ b'
  · obtain ⟨k, hk⟩ := h_div_b'
    obtain ⟨a', ha'⟩ : ∃ a', a = p * a' :=
      Int.Prime.dvd_pow' hp <| by
        simpa [hk, ← ZMod.intCast_zmod_eq_zero_iff_dvd] using dvd_of_odd_padicValInt h_odd_val
    contrapose! ih
    refine ⟨a'.natAbs + k.natAbs, ?_, a', k, ?_, rfl, ih⟩
    · rcases eq_or_ne a' 0 with ha0 | ha0 <;> rcases eq_or_ne k 0 with hk0 | hk0 <;>
        simp_all [Int.natAbs_mul]
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hk0) hp.one_lt
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr ha0) hp.one_lt
      · nlinarith [hp.two_le, abs_pos.mpr ha0, abs_pos.mpr hk0]
    · simp_all [padicValInt, parity_simps]
      have hfactor : (p * a') ^ 2 + d * (p * k) ^ 2 = p ^ 2 * (a' ^ 2 + d * k ^ 2) := by ring
      rw [hfactor, Int.natAbs_mul, Int.natAbs_pow] at h_odd_val
      have := Fact.mk hp
      rw [padicValNat.mul] at h_odd_val <;> simp_all +decide [parity_simps]
      · exact hp.ne_zero
      · intro H; simp_all
  · exact jacobi_neg_d_of_dvd_sq_add p a d b' hp (dvd_of_odd_padicValInt h_odd_val)
      hp_not_dvd_d h_div_b'

/-- Completing-the-square for the binary form: `4·q·v = (2·q·x + b·y)² + m·y²` when
`v = q·x² + b·x·y + h·y²` and `b² - 4·q·h = -m`. -/
private lemma four_q_v_eq_sq_plus_m_y_sq {m : ℕ} {q : ℤ} {b h x y v : ℤ}
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -(m : ℤ)) :
    4 * q * v = (2 * q * x + b * y) ^ 2 + (m : ℤ) * y ^ 2 := by
  rw [hv]; linear_combination -hbqm * y ^ 2

/-- If `R² ≡ a (mod p)` with `p ∤ a` and `p` an odd prime, then `(a/p) = 1` (Jacobi/Legendre). -/
private lemma jacobiSym_eq_one_of_sq_modEq {p : ℕ} (hp : Nat.Prime p) {a R : ℤ}
    (hpa : ¬ (p : ℤ) ∣ a) (hRa : R ^ 2 ≡ a [ZMOD p]) :
    jacobiSym a p = 1 := by
  have := Fact.mk hp
  simp_all [← ZMod.intCast_eq_intCast_iff, jacobiSym,
    Nat.primeFactorsList_prime hp]
  rw [legendreSym.eq_one_iff]
  · exact ⟨R, by simpa [sq] using hRa.symm⟩
  · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpa

/-- For an odd prime `p` coprime to `q` and dividing a nonzero integer `v`,
`padicValInt p (4qv) = padicValInt p v`. -/
private lemma padicValInt_four_q_v {p : ℕ} {q v : ℤ}
    (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hpq : ¬ (p : ℤ) ∣ q) (hpv : Odd (padicValInt p v)) :
    padicValInt p (4 * q * v) = padicValInt p v := by
  have := Fact.mk hp
  rw [padicValInt.mul, padicValInt.mul] <;> norm_num
  · refine ⟨Or.inr <| mod_cast fun h => hp_odd ?_, Or.inr <| Or.inr hpq⟩
    have := Nat.le_of_dvd (by decide) h
    interval_cases p <;> trivial
  all_goals aesop

private lemma p_mod4_eq1_of_dvd_v_not_dvd_m (p : ℕ) (q : ℤ) (b h x y v R m : ℤ)
    (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * q * h = -m)
    (hRv : R ^ 2 + 2 * v = m)
    (hpv : Odd (padicValInt p v))
    (hpm : ¬ (p : ℤ) ∣ m) :
    p % 4 = 1 := by
  have hpv_dvd : (p : ℤ) ∣ v := dvd_of_odd_padicValInt hpv
  have h_diff : (m - R ^ 2 : ℤ) = 2 * v := by grind
  have h_jacobi_m : jacobiSym m p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp hpm (R := R)
      (Int.modEq_iff_dvd.mpr (by rw [h_diff]; exact hpv_dvd.mul_left 2))
  have h_jacobi_neg_m : jacobiSym (-m) p = 1 := by
    by_cases hpq : (p : ℤ) ∣ q
    · -- `p | q`: then `b² - 4qh = -m` gives `b² ≡ -m (mod p)`, so `(-m/p) = 1`.
      refine jacobiSym_eq_one_of_sq_modEq hp (by simpa using hpm) (R := b) ?_
      exact Int.modEq_iff_dvd.mpr ⟨-4 * h * hpq.choose,
        by linear_combination -hbqm - 4 * h * hpq.choose_spec⟩
    · have h_padic := padicValInt_four_q_v hp hp_odd hpq hpv
      apply jacobi_neg_d_of_odd_padicVal p (2 * q * x + b * y) m y hp hpm
      grind
  rw [jacobiSym.neg _ (hp.odd_of_ne_two hp_odd), h_jacobi_m, mul_one,
    ZMod.χ₄_nat_mod_four] at h_jacobi_neg_m
  have := Nat.mod_lt p zero_lt_four
  interval_cases p % 4 <;> trivial

/-- If `R² + 2v = m`, `p` is a prime dividing both `v` and `m`, then `p ∣ R`. -/
private lemma dvd_R_of_dvd_v_dvd_m {p : ℕ} (hp : Nat.Prime p) {R v : ℤ} {m : ℕ}
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) : (p : ℤ) ∣ R :=
  Int.Prime.dvd_pow' hp <| by
    rw [← Int.dvd_add_left (dvd_mul_of_dvd_right hpv _)]
    exact hRv.symm ▸ Int.natCast_dvd_natCast.mpr hpm

/-- Given `v = qx² + bxy + hy²`, `b² - 4qh = -m`, a prime `p ∣ v` and `p ∣ m`, then
`p ∣ (2qx + by)`. Uses the identity `4qv = (2qx + by)² + m·y²`. -/
private lemma dvd_two_q_x_add_b_y_of_dvd_v_dvd_m {p q : ℕ} {b h x y v : ℤ} {m : ℕ}
    (hp : Nat.Prime p) (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) : (p : ℤ) ∣ (2 * q * x + b * y) := by
  have h_sum : (p : ℤ) ∣ ((2 * q * x + b * y) ^ 2 + m * y ^ 2) := by
    rw [← four_q_v_eq_sq_plus_m_y_sq hv hbqm]
    exact hpv.mul_left (4 * q)
  exact Int.Prime.dvd_pow' hp <|
    (Int.dvd_add_left ((Int.natCast_dvd_natCast.mpr hpm).mul_right _)).mp h_sum

/-- The quadratic residue extraction: given the problem hypotheses with `p` a prime
dividing both `v` and `m` (and `m` squarefree), we have `y² ≡ 2q (mod p)`. -/
private lemma y_sq_modEq_two_mul_q {p q : ℕ} {b h x y : ℤ} {R v : ℤ} {m : ℕ}
    (hp : Nat.Prime p) (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m) :
    y ^ 2 ≡ 2 * q [ZMOD p] := by
  have hp_R := dvd_R_of_dvd_v_dvd_m hp hRv hpv hpm
  have hp_2qx_by := dvd_two_q_x_add_b_y_of_dvd_v_dvd_m hp hv hbqm hpv hpm
  have h_div_p : (m / p : ℤ) * y ^ 2 ≡ (m / p : ℤ) * (2 * q) [ZMOD p] := by
    have h_div_p : (4 * q * v : ℤ) ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
      obtain ⟨k, hk⟩ := hpv
      simp_all [Int.modEq_iff_dvd]
      obtain ⟨a, ha⟩ := hp_R
      obtain ⟨b', hb'⟩ := hp_2qx_by
      simp_all [← eq_sub_iff_add_eq', ← mul_assoc]
      exact ⟨a ^ 2 * 2 * q, by nlinarith⟩
    have h_div_p : (4 * q * v : ℤ) ≡ (2 * q * x + b * y) ^ 2 + m * y ^ 2 [ZMOD p ^ 2] :=
      (four_q_v_eq_sq_plus_m_y_sq hv hbqm) ▸ .refl _
    have h_div_p : (m : ℤ) * y ^ 2 ≡ (m : ℤ) * (2 * q) [ZMOD p ^ 2] := by
      simp_all [Int.ModEq]
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at *
      aesop
    rw [Int.modEq_iff_dvd] at *
    obtain ⟨k, hk⟩ := h_div_p
    use k
    have hpm' : (p : ℤ) ∣ m := mod_cast hpm
    nlinarith [hp.two_le, Int.ediv_mul_cancel hpm']
  have := Fact.mk hp
  simp_all [← ZMod.intCast_eq_intCast_iff]
  cases h_div_p <;> simp_all [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_cast at *
  simp_all [Nat.squarefree_iff_prime_squarefree]

private lemma p_mod4_of_dvd_v_dvd_m (p : ℕ) (q : ℕ) (b h x y : ℤ) (R v : ℤ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hm_sq : Squarefree m)
    (hv : v = q * x ^ 2 + b * x * y + h * y ^ 2) (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + 2 * v = m) (hpv : (p : ℤ) ∣ v) (hpm : (p : ℕ) ∣ m)
    (hjac : jacobiSym (-2 * q) p = 1) :
    False := by
  have h_jacobi_2q_p : jacobiSym (2 * q) p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp
      (fun h2q => not_jacobiSym_eq_one_of_dvd hp (by simpa [neg_mul] using h2q.neg_right) hjac)
      (y_sq_modEq_two_mul_q hp hm_sq hv hbqm hRv hpv hpm)
  simp only [neg_mul] at hjac
  rw [jacobiSym.neg _ (hp.odd_of_ne_two (by omega)), ZMod.χ₄_nat_mod_four, hp3,
      h_jacobi_2q_p, mul_one] at hjac
  exact absurd hjac (by decide)

private lemma even_padicVal_of_mod4_eq3 (p : ℕ) (q : ℕ) (b h x y : ℤ) (R : ℤ) (v : ℕ) (m : ℕ)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hm_sq : Squarefree m) (hv_pos : 0 < v)
    (hv_def : (v : ℤ) = q * x ^ 2 + b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - 4 * (q : ℤ) * h = -(m : ℤ)) (hRv : R ^ 2 + 2 * (v : ℤ) = (m : ℤ))
    (hjac : ∀ p', p' ∣ m → Nat.Prime p' → jacobiSym (-2 * ↑q) ↑p' = 1) :
    Even (padicValNat p (2 * v)) := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hEven : Even (padicValInt p v) := by
    by_contra h_even
    have h_odd : Odd (padicValInt p v) := Nat.not_even_iff_odd.mp h_even
    by_cases hpm : (p : ℕ) ∣ m
    · exact p_mod4_of_dvd_v_dvd_m p q b h x y R v m hp hp3 hm_sq hv_def hbqm hRv
        (dvd_of_odd_padicValInt h_odd) hpm (hjac p hpm hp)
    · have := p_mod4_eq1_of_dvd_v_not_dvd_m p q b h x y v R m hp hp2 hv_def hbqm hRv h_odd
        (by exact_mod_cast hpm)
      omega
  rw [padicValNat.mul (by omega) hv_pos.ne',
    padicValNat.eq_zero_of_not_dvd fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h), zero_add,
    ← padicValInt.of_nat]
  exact hEven

/-- The final theorem -/
private lemma blueprint_case_mod8_eq3 (m : ℕ) (hm_sq : Squarefree m) (hm_pos : 0 < m)
    (hm_mod : m % 8 = 3) : (∃ a b c : ℕ, a^2 + b^2 + c^2 = m) := by
  obtain ⟨q, hq_prime, hq_mod, hjac⟩ := exists_prime_aux m hm_mod
  obtain ⟨b, h, hbqm⟩ :=
    exists_b_h m q hm_mod hq_prime hq_mod (jacobi_neg_m_q m q hm_mod hq_mod hjac)
  obtain ⟨t, hqt⟩ := exists_t m q hm_sq hm_mod hq_prime hjac
  obtain ⟨x, y, R, v, hv_def, hRv, hv_pos⟩ :=
    exists_Rv_from_Minkowski m q t b h hm_pos hq_prime.pos hqt hbqm
  have h2v : ∃ a b : ℕ, 2 * v = a ^ 2 + b ^ 2 := Nat.eq_sq_add_sq_iff.mpr fun p hp hp3 =>
    even_padicVal_of_mod4_eq3 p q b h x y R v m
      (Nat.prime_of_mem_primeFactors hp) hp3 hm_sq hv_pos hv_def hbqm hRv hjac
  obtain ⟨a, b, c, habc⟩ : ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
    obtain ⟨s, t, hst⟩ := h2v
    exact ⟨R, s, t, by zify at hst; linarith [hRv, hst]⟩
  refine ⟨a.natAbs, b.natAbs, c.natAbs, ?_⟩
  zify [Int.natCast_natAbs, sq_abs, habc]

end
open Nat

private lemma twiceTri (x : ℕ) : 2 * triangular x = x*(x+1) := by
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self x).two_dvd

private lemma triStep (x : ℕ) : triangular (x+1) = triangular x + (x+1) := by
  nlinarith only [twiceTri x, twiceTri (x+1)]

private lemma peel (m b : ℕ) (hm : 0 < m) {n : ℕ}
    (hn : n ≤ triangular (m*(b+1))/m) :
    ∃ x r : ℕ, r ≤ b ∧ n = triangular x / m + r := by
  have cover (k : ℕ) (hk : k ≤ m*(b+1)) (h : n ≤ triangular k/m) :
      ∃ x r : ℕ, r ≤ b ∧ n = triangular x / m + r := by
    induction k with
    | zero =>
      exact ⟨0, 0, Nat.zero_le _, by simpa using Nat.eq_zero_of_le_zero (by simpa using h)⟩
    | succ k ih =>
      by_cases prev : n ≤ triangular k / m
      · exact ih (by omega) prev
      by_cases eq : n = triangular (k+1)/m
      · exact ⟨k+1, 0, Nat.zero_le _, by simpa using eq⟩
      have step : triangular (k+1) / m ≤ triangular k / m + (b+1) := by
        rw [triStep]
        calc
          (triangular k + (k+1))/m ≤ (triangular k + m*(b+1))/m :=
            Nat.div_le_div_right (Nat.add_le_add_left hk _)
          _ = _ := by rw [Nat.add_mul_div_left _ _ hm]
      exact ⟨k, n - triangular k/m, by omega, by omega⟩
  exact cover _ le_rfl hn

private lemma smallRange (m n : ℕ) (hm : 0 < m) (hn : 128*n ≤ m^7) :
    ∃ x y z : ℕ, n = triangular x/m + triangular y/m + triangular z/m := by
  let g (b : ℕ) := triangular (m*(b+1))/m
  have bound (b : ℕ) : m*b^2 ≤ 2*g b ∧ m ≤ 2*g b := by
    have eq : g b = ((b+1)*(m*(b+1)+1))/2 := by
      dsimp [g, triangular]
      rw [Nat.div_div_eq_div_mul, Nat.mul_assoc, Nat.mul_comm 2 m,
        Nat.mul_div_mul_left _ _ hm]
    rw [eq]
    have h := Nat.mod_lt ((b+1)*(m*(b+1)+1)) (by decide : 0 < 2)
    have h' := Nat.mod_add_div ((b+1)*(m*(b+1)+1)) 2
    constructor <;> nlinarith only [h,h', Nat.zero_le (b*m), Nat.zero_le (b*b*m)]
  have b3 : m^3 ≤ 8 * g (g 0) := calc
    m^3 = m * m^2 := by ring
    _ ≤ m*(2*g 0)^2 := by gcongr; exact (bound 0).2
    _ = 4*(m*(g 0)^2) := by ring
    _ ≤ _ := by have := (bound (g 0)).1; omega
  have b7 : m^7 ≤ 128*g (g (g 0)) := calc
    m^7 = m*(m^3)^2 := by ring
    _ ≤ m*(8*g (g 0))^2 := by gcongr
    _ = 64*(m*(g (g 0))^2) := by ring
    _ ≤ _ := by have := (bound (g (g 0))).1; omega
  obtain ⟨z,r₂,h₂,rz⟩ := peel m (g (g 0)) hm (show n ≤ g (g (g 0)) by omega)
  obtain ⟨y,r₁,h₁,ry⟩ := peel m (g 0) hm h₂
  obtain ⟨x,r₀,h₀,rx⟩ := peel m 0 hm h₁
  exact ⟨x,y,z,by omega⟩

private lemma liftOdd (q m : ℕ) (hq : Odd q) (x : ℕ) :
    ∃ y : ℕ, triangular y/(q^2*m) = triangular x/m := by
  obtain ⟨k,rfl⟩ := hq
  let q := 2*k+1
  have hq : 0 < q^2 := by dsimp [q]; positivity
  have eq : triangular (q*x+k) = q^2*triangular x + triangular k := by
    have scaled := congrArg (q^2 * ·) (twiceTri x)
    dsimp [q] at *
    nlinarith only [scaled,twiceTri ((2*k+1)*x+k),twiceTri k]
  have small : triangular k < q^2 := by
    dsimp [q]; nlinarith only [twiceTri k,Nat.zero_le (k*k),Nat.zero_le k]
  refine ⟨q*x+k, ?_⟩
  change triangular (q*x+k)/(q^2*m) = _
  rw [eq, ← Nat.div_div_eq_div_mul, Nat.mul_add_div hq,
    Nat.div_eq_of_lt small, Nat.add_zero]

private lemma residuePeriod (m x : ℕ) :
    triangular (x%(2*m)) % m = triangular x % m := by
  unfold triangular
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self]
  congr 1
  have h := (Nat.mod_modEq x (2*m))
  exact (h.mul (h.add_right 1))

private lemma singleResidue (m r : ℕ) (hm : 0 < m) (hr : r < m)
    (unique : ∀ x y z : Fin (2*m),
      let s := triangular x.val % m + triangular y.val % m + triangular z.val % m
      s % m = r → s = r)
    (gauss : ∀ N : ℕ, ∃ x y z : ℕ, N = triangular x + triangular y + triangular z)
    (n : ℕ) : ∃ x y z : ℕ, n = triangular x/m + triangular y/m + triangular z/m := by
  obtain ⟨x,y,z,eq⟩ := gauss (m*n+r)
  let small (k : ℕ) : Fin (2*m) := ⟨k%(2*m), Nat.mod_lt _ (by omega)⟩
  have hsum : (triangular x % m + triangular y % m + triangular z % m) % m = r := by
    have h := ((Nat.mod_modEq (triangular x) m).add (Nat.mod_modEq (triangular y) m)).add
      (Nat.mod_modEq (triangular z) m)
    exact Eq.trans h (show (triangular x + triangular y + triangular z) % m = r by rw [← eq]; simp [Nat.mod_eq_of_lt hr])
  have u := unique (small x) (small y) (small z)
  dsimp only [small] at u
  simp only [residuePeriod] at u
  have hu := u hsum
  have e : m * n = m * (triangular x/m + triangular y/m + triangular z/m) := by
    have dx := Nat.mod_add_div (triangular x) m
    have dy := Nat.mod_add_div (triangular y) m
    have dz := Nat.mod_add_div (triangular z) m
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact ⟨x,y,z, Nat.eq_of_mul_eq_mul_left hm e⟩


private lemma gauss (n : ℕ) :
    ∃ x y z : ℕ, n = triangular x + triangular y + triangular z := by
  obtain ⟨s,b,eq,hs⟩ := Nat.sq_mul_squarefree (8*n+3)
  have hmod : ((b%8)^2*(s%8))%8 = 3 := by
    have h := ((Nat.mod_modEq b 8).pow 2).mul (Nat.mod_modEq s 8)
    exact Eq.trans h (show (b^2*s)%8 = 3 by rw [eq]; omega)
  have test : ∀ B S : Fin 8, (B.val^2*S.val)%8 = 3 → S.val = 3 := by decide
  have hsmod : s%8 = 3 := test ⟨_,Nat.mod_lt _ (by decide)⟩ ⟨_,Nat.mod_lt _ (by decide)⟩ hmod
  obtain ⟨u,v,w,he⟩ := blueprint_case_mod8_eq3 s hs (by omega) hsmod
  have hx : (b*u)^2 + (b*v)^2 + (b*w)^2 = 8*n+3 := by
    rw [← eq, ← he]; ring
  let X := b*u
  let Y := b*v
  let Z := b*w
  change X^2 + Y^2 + Z^2 = 8*n+3 at hx
  have parity : ∀ A B C : Fin 8, (A.val^2+B.val^2+C.val^2)%8 = 3 →
      A.val%2 = 1 ∧ B.val%2 = 1 ∧ C.val%2 = 1 := by decide
  have modsum := (((Nat.mod_modEq X 8).pow 2).add ((Nat.mod_modEq Y 8).pow 2)).add
    ((Nat.mod_modEq Z 8).pow 2)
  obtain ⟨hp,hq,hr⟩ := parity ⟨X%8, Nat.mod_lt _ (by decide)⟩
    ⟨Y%8, Nat.mod_lt _ (by decide)⟩ ⟨Z%8, Nat.mod_lt _ (by decide)⟩
    (Eq.trans modsum (show (X^2+Y^2+Z^2)%8 = 3 by rw [hx]; omega))
  dsimp at hp hq hr
  have hX : X = 2*(X/2)+1 := by omega
  have hY : Y = 2*(Y/2)+1 := by omega
  have hZ : Z = 2*(Z/2)+1 := by omega
  have hsq (t : ℕ) (ht : t = 2*(t/2)+1) : t^2 = 8*triangular (t/2)+1 := by
    calc
      t^2 = (2*(t/2)+1)^2 := congrArg (·^2) ht
      _ = _ := by nlinarith only [twiceTri (t/2)]
  refine ⟨X/2,Y/2,Z/2,?_⟩
  rw [hsq X hX, hsq Y hY, hsq Z hZ] at hx
  omega

set_option maxRecDepth 3000 in
set_option maxHeartbeats 2000000 in
private lemma baseModuli (m n : ℕ) (hm : m ∈ ({1,3,5,13,15} : Finset ℕ)) :
    ∃ x y z : ℕ, n = triangular x/m + triangular y/m + triangular z/m := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · simpa using gauss n
  · exact singleResidue 3 1 (by decide) (by decide) (by decide +kernel) gauss n
  · exact singleResidue 5 3 (by decide) (by decide) (by decide +kernel) gauss n
  · exact singleResidue 13 12 (by decide) (by decide) (by decide +kernel) gauss n
  · exact singleResidue 15 13 (by decide) (by decide) (by decide +kernel) gauss n

end RoundedTriangular

namespace OMA.R_OeisA256544_conjecture_R1

/-- The remaining odd moduli have squarefree denominator. -/
def H1 : Prop := ∀ m : ℕ, Odd m → Squarefree m → m ∉ ({1,3,5,13,15} : Finset ℕ) →
  ∀ n : ℕ, m^7 < 128*n →
    ∃ x y z : ℕ, n = Nat.triangular x/m + Nat.triangular y/m + Nat.triangular z/m

/-- For an even modulus all odd square factors can still be removed. -/
def H2 : Prop := ∀ m : ℕ, 0 < m → Even m →
  (∀ p : ℕ, p.Prime → Odd p → ¬p^2 ∣ m) → ∀ n : ℕ, m^7 < 128*n →
    ∃ x y z : ℕ, n = Nat.triangular x/m + Nat.triangular y/m + Nat.triangular z/m

theorem main : H1 → H2 → type_of% @OeisA256544.conjecture := by
  intro hodd heven m hm n
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases small : 128*n ≤ m^7
    · exact RoundedTriangular.smallRange m n hm small
    by_cases base : m ∈ ({1,3,5,13,15} : Finset ℕ)
    · exact RoundedTriangular.baseModuli m n base
    by_cases core : ∀ p : ℕ, p.Prime → Odd p → ¬ p^2 ∣ m
    · rcases Nat.even_or_odd m with e | o
      · exact heven m hm e core n (by omega)
      · apply hodd m o _ base n (by omega)
        apply Nat.squarefree_iff_prime_squarefree.mpr
        intro p hp
        rcases hp.eq_two_or_odd with rfl | hop
        · intro hd
          have d : 2 ∣ m := dvd_trans (by decide : 2 ∣ 2*2) hd
          exact (Nat.not_even_iff_odd.mpr o) (even_iff_two_dvd.mpr d)
        · simpa [pow_two] using core p hp (Nat.odd_iff.mpr hop)
    push Not at core
    obtain ⟨p,hp,po,d,eq⟩ := core
    have dpos : 0 < d := by by_contra! hz; simp [show d=0 by omega] at eq; omega
    have dlt : d < m := by rw [eq]; nlinarith [hp.two_le, Nat.mul_le_mul_right d hp.two_le]
    obtain ⟨x,y,z,repr⟩ := ih d dlt dpos
    obtain ⟨X,hX⟩ := RoundedTriangular.liftOdd p d po x
    obtain ⟨Y,hY⟩ := RoundedTriangular.liftOdd p d po y
    obtain ⟨Z,hZ⟩ := RoundedTriangular.liftOdd p d po z
    exact ⟨X,Y,Z,by simpa [eq,hX,hY,hZ] using repr⟩

end OMA.R_OeisA256544_conjecture_R1
