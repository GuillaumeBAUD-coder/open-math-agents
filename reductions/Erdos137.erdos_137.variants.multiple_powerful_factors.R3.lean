import FormalConjectures.ErdosProblems.«137»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization

/-!
For a block ending at X = m + n, each prime power in the binomial coefficient
is at most X. A prime above a cutoff T ≥ n whose square divides the block gives
a cofactor a with m < a p² ≤ X. Each a accounts for at most one such prime.
Taking T just below the next prime after the first ⌊n/8⌋ primes extends the
unconditional middle range beyond the cubic scale.

For the same cofactor counting device in the cubic range, see the proof of
Theorem 3.1 of S. Venkat, Ramanujan primes and primes of exponent one in
products of consecutive integers (2026).
-/

namespace OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R3

open Finset Filter

/-- A fixed relative interval contains arbitrarily many primes, a consequence
of the prime number theorem. -/
def H1 : Prop := ∀ k : ℕ, ∀ᶠ X : ℕ in atTop,
  ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧ p ≤ X ∧ 8191*X < 8192*p

/-- The remaining range of large starting points. -/
def H2 : Prop := ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
  let T := max (4*n) (Nat.nth Nat.Prime (n/8) - 1)
  n*T^2 < 16*(m+n) →
  ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
    p ∣ ∏ x ∈ Ioc m (m + n), x ∧ ¬ p ^ 2 ∣ ∏ x ∈ Ioc m (m + n), x

lemma block_eq (m n : ℕ) :
    (∏ x ∈ Ioc m (m + n), x) = n.factorial * (m + n).choose n := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, prod_Ioc_succ_top (by omega), Nat.ascFactorial_succ, ih]
    ring

lemma binomial_lower (m n : ℕ) :
    (m + n) ^ n ≤ n ^ n * (m + n).choose n := by
  have h := Finset.prod_le_prod' (s := range n) (f := fun i => (m + n) * (i + 1))
    (g := fun i => n * (m + 1 + i)) (fun i hi => by
      have h := Nat.mul_le_mul_left m (show i + 1 ≤ n from Finset.mem_range.mp hi)
      nlinarith)
  simp only [prod_mul_distrib, prod_const, card_range, prod_range_add_one_eq_factorial,
    ← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    using h) n.factorial_pos

lemma binomial_upper {m n : ℕ} (hn : 0 < n) :
    (m+n).choose n ≤ (m+n)^((m+n).choose n).primeFactors.card := calc
  _ = ∏ p ∈ ((m+n).choose n).primeFactors, p ^ ((m+n).choose n).factorization p :=
    Nat.prod_primeFactors_pow_factorization (Nat.choose_ne_zero (by omega))
  _ ≤ ∏ _p ∈ ((m+n).choose n).primeFactors, (m+n) := prod_le_prod' fun _ _ =>
    Nat.pow_factorization_choose_le (by omega)
  _ = _ := prod_const _

lemma many_factors {m n : ℕ} (hn : 2 ≤ n) (hlarge : n^2 ≤ m + n) :
    n ≤ 2 * ((m + n).choose n).primeFactors.card := by
  let X := m + n
  let B := X.choose n
  change n ≤ 2 * B.primeFactors.card
  have hX : 1 < X := by dsimp [X]; omega
  have hUpper : B ≤ X ^ B.primeFactors.card := binomial_upper (by omega)
  have hLow : X ^ n ≤ n ^ n * B := binomial_lower m n
  have hSq : (n ^ n)^2 ≤ X ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    exact Nat.pow_le_pow_left hlarge n
  have h : X^n * X^n ≤ X^n * B^2 := calc
    X^n * X^n ≤ (n^n * B)^2 := by simpa [pow_two] using Nat.mul_le_mul hLow hLow
    _ = (n^n)^2 * B^2 := mul_pow _ _ _
    _ ≤ _ := Nat.mul_le_mul_right _ hSq
  have h' := Nat.le_of_mul_le_mul_left h (pow_pos (by omega : 0 < X) _)
  have hh : X^n ≤ X^(2 * B.primeFactors.card) := calc
    _ ≤ B^2 := h'
    _ ≤ (X ^ B.primeFactors.card)^2 := Nat.pow_le_pow_left hUpper 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm]
  exact (pow_le_pow_iff_right₀ hX).mp hh

lemma unique_multiple {m n p x y : ℕ} (hp : n < p)
    (hx : x ∈ Ioc m (m+n)) (hy : y ∈ Ioc m (m+n)) (hpx : p ∣ x) (hpy : p ∣ y) :
    x = y := by
  obtain ⟨hx₁,hx₂⟩ := mem_Ioc.mp hx
  obtain ⟨hy₁,hy₂⟩ := mem_Ioc.mp hy
  rcases lt_trichotomy x y with h | h | h
  · have := Nat.le_of_dvd (by omega : 0 < y-x) (Nat.dvd_sub hpy hpx)
    omega
  · exact h
  · have := Nat.le_of_dvd (by omega : 0 < x-y) (Nat.dvd_sub hpx hpy)
    omega

lemma square_in_block {m n p : ℕ} (hprime : p.Prime) (hbig : n < p)
    (hsq : p^2 ∣ ∏ x ∈ Ioc m (m+n), x) :
    ∃ a : ℕ, 0 < a ∧ m < a*p^2 ∧ a*p^2 ≤ m+n := by
  let S := Ioc m (m+n)
  have hd : p ∣ ∏ x ∈ S, x := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hsq
  obtain ⟨x,hx,hpx⟩ := (hprime.prime.dvd_finsetProd_iff id).mp hd
  have hrest : ¬ p ∣ ∏ y ∈ S.erase x, y := by
    intro h
    obtain ⟨y,hy,hpy⟩ := (hprime.prime.dvd_finsetProd_iff id).mp h
    obtain ⟨hyne,hyS⟩ := mem_erase.mp hy
    exact hyne (unique_multiple hbig hyS hx hpy hpx)
  have hcop := (hprime.coprime_iff_not_dvd.mpr hrest).pow_left 2
  have hall : (∏ y ∈ S.erase x, y) * x = ∏ y ∈ S, y := prod_erase_mul _ _ hx
  rw [← hall] at hsq
  obtain ⟨a,ha⟩ := hcop.dvd_of_dvd_mul_left hsq
  obtain ⟨h1,h2⟩ := mem_Ioc.mp hx
  rw [ha, Nat.mul_comm (p^2) a] at h1 h2
  exact ⟨a, Nat.pos_of_ne_zero (by rintro rfl; simp at h1), h1,h2⟩

lemma square_spacing {a m n p q : ℕ} (ha : 0 < a) (hp : n < p) (hq : n < q)
    (h₁ : m < a*p^2) (h₂ : a*p^2 ≤ m+n) (h₃ : m < a*q^2) (h₄ : a*q^2 ≤ m+n) : p = q := by
  have sep : ∀ u v : ℕ, n < u → u < v → a*u^2 + n < a*v^2 := by
    intro u v hu huv
    have hv : (u+1)^2 ≤ v^2 := Nat.pow_le_pow_left huv 2
    have h := Nat.mul_le_mul_left a hv
    have ha' := Nat.mul_le_mul_right (2*u+1) (show 1 ≤ a from ha)
    nlinarith
  rcases lt_trichotomy p q with h | h | h
  · have := sep p q hp h; omega
  · exact h
  · have := sep q p hq h; omega

lemma bad_count {n m T : ℕ} {D : Finset ℕ} (hn : 0 < n) (hT : n ≤ T)
    (hsize : 16*(m+n) ≤ n*T^2)
    (hD : ∀ p ∈ D, p.Prime ∧ T < p ∧ p^2 ∣ ∏ x ∈ Ioc m (m+n), x) :
    D.card ≤ n / 16 := by
  classical
  have hex (p : ℕ) (hp : p ∈ D) :
      ∃ a : ℕ, 0 < a ∧ m < a*p^2 ∧ a*p^2 ≤ m+n := by
    obtain ⟨hpr, hgt, hd⟩ := hD p hp
    exact square_in_block hpr (by omega) hd
  let a (p : ℕ) := if h : p ∈ D then (hex p h).choose else 0
  have ha (p : ℕ) (hp : p ∈ D) :
      0 < a p ∧ m < a p * p^2 ∧ a p * p^2 ≤ m+n := by
    simpa [a,hp] using (hex p hp).choose_spec
  have hcard : D.card ≤ (Icc 1 (n / 16)).card := by
    apply card_le_card_of_injOn a
    · intro p hp
      obtain ⟨hpos,_,hmax⟩ := ha p hp
      obtain ⟨_, hgt, _⟩ := hD p hp
      have hsq := Nat.pow_le_pow_left hgt.le 2
      have hbound : (16 * a p) * T^2 ≤ n*T^2 := calc
        _ = 16*(a p * T^2) := by ring
        _ ≤ 16*(a p * p^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsq)
        _ ≤ 16*(m+n) := Nat.mul_le_mul_left _ hmax
        _ ≤ _ := hsize
      have hsmall := Nat.le_of_mul_le_mul_right hbound (pow_pos (hn.trans_le hT) 2)
      exact mem_Icc.mpr ⟨hpos, (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)⟩
    · intro p hp q hq heq
      obtain ⟨hap, h₁, h₂⟩ := ha p hp
      obtain ⟨_, h₃, h₄⟩ := ha q hq
      rw [← heq] at h₃ h₄
      have hgp := (hD p hp).2.1
      have hgq := (hD q hq).2.1
      exact square_spacing hap (by omega) (by omega) h₁ h₂ h₃ h₄
  simpa using hcard

lemma small_primes_sparse : ∀ᶠ n : ℕ in atTop, 8 * Nat.primeCounting (4*n) ≤ n := by
  have ht : Tendsto (fun n : ℕ => (4 : ℝ) * n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hπ := ht.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  have hl := (Real.tendsto_log_atTop.comp ht).eventually
    (eventually_ge_atTop (32 * (Real.log 4 + 1)))
  filter_upwards [hπ,hl,eventually_ge_atTop 1] with n hπ hl hn
  have hfloor : ⌊(4:ℝ) * n⌋₊ = 4*n := by
    rw [show (4:ℝ)*n = ((4*n:ℕ):ℝ) by norm_cast, Nat.floor_natCast]
  rw [hfloor] at hπ
  change 32 * (Real.log 4 + 1) ≤ Real.log (4 * (n:ℝ)) at hl
  have hlog : 0 < Real.log (4 * (n:ℝ)) :=
    Real.log_pos (by
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith)
  have hnum := (le_div_iff₀ hlog).mp hπ
  have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (Nat.primeCounting (4*n)) : (0:ℝ) ≤ _)
  have hpos : 0 < Real.log 4 + 1 := by positivity
  exact_mod_cast (show (8:ℝ) * Nat.primeCounting (4*n) ≤ n by
    apply le_of_mul_le_mul_right (a := Real.log 4 + 1) _ hpos
    nlinarith)

lemma sparse_cutoff_range {n m k T : ℕ} (hn : 2 ≤ n) (hk : 4*k ≤ n) (hT : n ≤ T)
    (hs : 8 * Nat.primeCounting T ≤ n) (hl : n^2 ≤ m+n) (hu : 16*(m+n) ≤ n*T^2) :
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ ∏ x ∈ Ioc m (m+n), x ∧ ¬ p^2 ∣ ∏ x ∈ Ioc m (m+n), x := by
  classical
  let F := ((m+n).choose n).primeFactors
  let L := F.filter (fun p => T < p)
  let N := ∏ x ∈ Ioc m (m+n), x
  let D := L.filter (fun p => p^2 ∣ N)
  let G := L.filter (fun p => ¬ p^2 ∣ N)
  have hF : n ≤ 2*F.card := many_factors hn hl
  have hL : F.card ≤ L.card + Nat.primeCounting T := by
    have hsub : F.filter (fun p => ¬ T < p) ⊆ Nat.primesLE T := by
      intro p hp
      obtain ⟨hmem,hgt⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_of_mem_primeFactors hmem⟩
    have hc := card_le_card hsub
    rw [Nat.primesLE_card_eq_primeCounting] at hc
    have := card_filter_add_card_filter_not (s := F) (p := fun p => T < p)
    dsimp [L]
    omega
  have hD : D.card ≤ n/16 := by
    apply bad_count (by omega : 0<n) hT hu
    intro p hp
    obtain ⟨hpL,hd⟩ := mem_filter.mp hp
    obtain ⟨hpF,hgt⟩ := mem_filter.mp hpL
    exact ⟨Nat.prime_of_mem_primeFactors hpF,hgt,hd⟩
  have hsum : D.card + G.card = L.card :=
    card_filter_add_card_filter_not (s := L) (p := fun p => p^2 ∣ N)
  obtain ⟨P,hP,hkP⟩ := exists_subset_card_eq (show k ≤ G.card by omega)
  refine ⟨P,hkP,?_⟩
  intro p hp
  obtain ⟨hpL,hgood⟩ := mem_filter.mp (hP hp)
  obtain ⟨hpF,_⟩ := mem_filter.mp hpL
  refine ⟨Nat.prime_of_mem_primeFactors hpF, ?_, hgood⟩
  rw [block_eq]
  exact dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hpF) _

lemma small_prime_power_bound : ∀ᶠ n : ℕ in atTop,
    (n^2)^(2*Nat.primeCounting n) ≤ (4096:ℕ)^n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hπ := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [hπ, eventually_ge_atTop 2] with n hπ hn
  simp only [Nat.floor_natCast] at hπ
  have hn' : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have h := (le_div_iff₀ (Real.log_pos hn')).mp hπ
  rw [show Real.log 4 = 2 * Real.log 2 by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num] at h
  have h4096 : Real.log 4096 = 12 * Real.log 2 := by
    convert Real.log_pow (2:ℝ) 12 using 1 <;> norm_num
  have hn0 : 0 < (n:ℝ) := by linarith
  have hreal : ((n:ℝ)^2)^(2*Nat.primeCounting n) ≤ (4096:ℝ)^n := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp only [Real.log_pow, h4096, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  exact_mod_cast hreal

lemma medium_range {m n k : ℕ} (hn : 0<n) (hk : k ≤ Nat.primeCounting n)
    (hpow : (n^2)^(2*Nat.primeCounting n) ≤ (4096:ℕ)^n)
    (hl : 8192*n ≤ m+n) (hu : m+n ≤ n^2) :
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ ∏ x ∈ Ioc m (m+n), x ∧ ¬ p^2 ∣ ∏ x ∈ Ioc m (m+n), x := by
  classical
  let B := (m+n).choose n
  let F := B.primeFactors
  let L := F.filter (fun p => n < p)
  have hlarge : (8192:ℕ)^n ≤ B := by
    have h : (8192*n)^n ≤ n^n * B :=
      (Nat.pow_le_pow_left hl n).trans (binomial_lower m n)
    rw [mul_pow, Nat.mul_comm (n^n)] at h
    exact Nat.le_of_mul_le_mul_right h (pow_pos hn _)
  have hc : k ≤ L.card := by
    by_contra! hbad
    have hsub : F.filter (fun p => ¬ n < p) ⊆ Nat.primesLE n := by
      intro p hp
      obtain ⟨hmem,hgt⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_of_mem_primeFactors hmem⟩
    have hf := card_le_card hsub
    rw [Nat.primesLE_card_eq_primeCounting] at hf
    have heq : L.card + (F.filter (fun p => ¬ n < p)).card = F.card :=
      card_filter_add_card_filter_not (s := F) _
    have hcard : F.card ≤ 2*Nat.primeCounting n := by omega
    have hB : B ≤ (4096:ℕ)^n := calc
      _ ≤ (m+n)^F.card := binomial_upper hn
      _ ≤ (n^2)^F.card := Nat.pow_le_pow_left hu _
      _ ≤ (n^2)^(2*Nat.primeCounting n) :=
        pow_right_mono₀ (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hn.ne')) hcard
      _ ≤ _ := hpow
    exact (Nat.pow_lt_pow_left (by decide : 4096 < 8192) hn.ne').not_ge (hlarge.trans hB)
  obtain ⟨P,hP,hPc⟩ := exists_subset_card_eq hc
  refine ⟨P,hPc,?_⟩
  intro p hp
  obtain ⟨hmem,hbig⟩ := mem_filter.mp (hP hp)
  have hpr := Nat.prime_of_mem_primeFactors hmem
  refine ⟨hpr, ?_, ?_⟩
  · rw [block_eq]
    exact dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hmem) _
  · intro hd
    obtain ⟨a,ha,_,hax⟩ := square_in_block hpr hbig hd
    have hle : p^2 ≤ a*p^2 := Nat.le_mul_of_pos_left _ ha
    exact (Nat.pow_lt_pow_left hbig (by decide : 2 ≠ 0)).not_ge (hle.trans (hax.trans hu))

lemma endpoint_prime {m n p : ℕ} (hpr : p.Prime) (hl : m < p)
    (hu : p ≤ m + n) (hmax : m + n < 2 * p) :
    p ∣ ∏ x ∈ Ioc m (m+n), x ∧ ¬ p^2 ∣ ∏ x ∈ Ioc m (m+n), x := by
  classical
  let S := Ioc m (m+n)
  have hpS : p ∈ S := mem_Ioc.mpr ⟨hl,hu⟩
  have heq : (∏ y ∈ S.erase p, y)*p = ∏ y ∈ S, y := prod_erase_mul _ _ hpS
  change p ∣ ∏ y ∈ S, y ∧ ¬ p^2 ∣ ∏ y ∈ S, y
  rw [← heq]
  refine ⟨dvd_mul_left _ _, ?_⟩
  intro h
  rw [pow_two] at h
  have hd := (Nat.dvd_of_mul_dvd_mul_right hpr.pos h)
  obtain ⟨y,hy,hpy⟩ := (hpr.prime.dvd_finsetProd_iff id).mp hd
  obtain ⟨hyne,hyS⟩ := mem_erase.mp hy
  obtain ⟨hy₁,hy₂⟩ := mem_Ioc.mp hyS
  obtain ⟨a,ha⟩ := hpy
  change y = p*a at ha
  have hlt : p*a < p*2 := by omega
  have hA := Nat.lt_of_mul_lt_mul_left hlt
  rcases a with _ | a
  · simp at ha; omega
  · have : a=0 := by omega
    simp_all

/-- Unconditional range, uniform in the starting point. -/
lemma uniform_range (k : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 8192*n ≤ m+n →
    let T := max (4*n) (Nat.nth Nat.Prime (n/8) - 1)
    16*(m+n) ≤ n*T^2 → ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ ∏ x ∈ Ioc m (m+n), x ∧ ¬ p^2 ∣ ∏ x ∈ Ioc m (m+n), x := by
  filter_upwards [small_primes_sparse, eventually_ge_atTop (4*k),
    eventually_ge_atTop 2, small_prime_power_bound,
    Nat.tendsto_primeCounting.eventually_ge_atTop k] with n hs hk hn hpow hπ
  intro m hlin
  dsimp only
  intro hu
  by_cases hl : m+n < n^2
  · exact medium_range (by omega) hπ hpow (by omega) hl.le
  let q := Nat.nth Nat.Prime (n/8) - 1
  let T := max (4*n) q
  have hq : Nat.primeCounting q = n/8 := by simp [q]
  have hsT : 8 * Nat.primeCounting T ≤ n := by
    rcases le_total (4*n) q with h | h
    · simpa [T, max_eq_right h, hq] using (show 8*(n/8) ≤ n by omega)
    · simpa [T, max_eq_left h] using hs
  exact sparse_cutoff_range hn hk (show n ≤ T from (by omega : n ≤ 4*n).trans (le_max_left _ _))
    hsT (by omega) hu

theorem main : H1 → H2 → type_of% @Erdos137.erdos_137.variants.multiple_powerful_factors := by
  intro h₁ h₂ k
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (h₁ k)
  filter_upwards [h₂ k, uniform_range k, eventually_ge_atTop X₀] with n hlarge hmid hx
  intro m hm
  by_cases hlin : m+n < 8192*n
  · obtain ⟨P,hP,hprops⟩ := hX₀ (m+n) (by omega)
    refine ⟨P,hP,?_⟩
    intro p hp
    obtain ⟨hpr,hu,hl⟩ := hprops p hp
    exact ⟨hpr, endpoint_prime hpr (by omega) hu (by omega)⟩
  let T := max (4*n) (Nat.nth Nat.Prime (n/8) - 1)
  by_cases hu : n*T^2 < 16*(m+n)
  · exact hlarge m hm hu
  exact hmid m (by omega) (Nat.le_of_not_gt hu)

end OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R3
