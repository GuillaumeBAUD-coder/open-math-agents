import FormalConjectures.Wikipedia.Mills

-- Reduction Mills.lower_bound_of_RH.R1 of Mills' constant lower bound
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- RH is already a premise of the target, so the hypotheses are the two explicit prime-counting
-- inputs that turn RH into primes between consecutive cubes.
--
-- H1: under RH, the explicit Chebyshev bound |psi(x) - x| < (1/8) sqrt(x) log(x)^2 for x >= 73.2
--     (Schoenfeld 1976, Theorem 10, has the constant 1/(8 pi); 1/8 is a weaker constant).
-- H2: unconditionally, psi(x) - theta(x) <= (1/8) sqrt(x) log(x)^2 for x >= 599
--     (from Costa Pereira's psi(x) - theta(x) <= psi(x^(1/2)) + psi(x^(1/3)) + psi(x^(1/5)),
--     in Mathlib, and Mathlib's psi(y) <= log 4 * y + 2 sqrt(y) log y).
--
-- main proves everything else:
-- 1. H1 and H2 give |theta(x) - x| < (1/4) sqrt(x) log(x)^2 for x >= 599.
-- 2. With a = x^3 and b = x^3 + 3x^2 + 3x, theta(b) > theta(a) once 3x^2 + 3x exceeds
--    (1/2) sqrt(b) log(b)^2, which holds for x >= 10^9: a prime lies strictly between x^3 and
--    (x+1)^3 for every x >= 10^9 (Caldwell and Cheng 2005 use Schoenfeld for x >= 2657).
-- 3. The greedy sequence g 0 = 2, g (n+1) = least prime >= (g n)^3 starts 2, 11, 1361,
--    2521008887 (primality of 2521008887 by a Lucas certificate, no native_decide). Every Mills
--    number A > 1 has g n <= floor(A^(3^(n+1))), so A^81 >= 2521008887 and A > 1.3063778838.
-- 4. Primes between cubes from g 3 = 2521008887 >= 10^9 on give g (n+1) + 1 < (g n + 1)^3, so
--    the limit of g(n)^(1/3^(n+1)) is a Mills number with A^81 <= 2521008888, hence the least
--    Mills number is < 1.3063778839.

namespace OMA.R_Mills_lower_bound_of_RH_R1

open Mills Chebyshev Real

/-- Under RH, `|ψ(x) − x| < √x log² x / 8` for `x ≥ 73.2`. -/
def H1 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 73.2 ≤ x →
    |Chebyshev.psi x - x| < 1 / 8 * (Real.sqrt x * Real.log x ^ 2)

/-- Unconditionally, `ψ(x) − θ(x) ≤ √x log² x / 8` for `x ≥ 599`. -/
def H2 : Prop :=
  ∀ x : ℝ, 599 ≤ x →
    Chebyshev.psi x - Chebyshev.theta x ≤ 1 / 8 * (Real.sqrt x * Real.log x ^ 2)

/-! ### Step 1: the θ bound -/

theorem theta_sub_lt_quarter (h1 : H1) (h2 : H2) (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 599 ≤ x) : |θ x - x| < 1 / 4 * (√x * Real.log x ^ 2) := by
  have hψ := h1 hRH x (by linarith)
  have hle := theta_le_psi x
  have hd := h2 x hx
  rw [abs_lt] at hψ ⊢
  constructor <;> linarith [hψ.1, hψ.2]

/-! ### Step 2: primes between consecutive cubes -/

/-- A strict increase of `θ` over `(a, b]` produces a prime there. -/
lemma exists_prime_of_theta_lt {a b : ℕ} (h : θ (a : ℝ) < θ (b : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  by_contra hne
  push Not at hne
  refine absurd h (not_lt.mpr ?_)
  unfold Chebyshev.theta
  simp only [Nat.floor_natCast]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨h0, hpb⟩, hpp⟩ := hp
    refine ⟨⟨h0, ?_⟩, hpp⟩
    by_contra hlt
    push Not at hlt
    exact absurd hpb (not_le.mpr (hne p hpp hlt))
  · intro p hp _
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)

lemma root_pow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (hm : m ≠ 0) : (x ^ ((1 : ℝ) / m)) ^ m = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have : (1 : ℝ) / m * m = 1 := by field_simp
  rw [this, Real.rpow_one]

lemma cubes_inequality (X : ℝ) (hX : (10 : ℝ) ^ 9 ≤ X) :
    1 / 2 * (√(X ^ 3 + 3 * X ^ 2 + 3 * X) * Real.log (X ^ 3 + 3 * X ^ 2 + 3 * X) ^ 2)
      < 3 * X ^ 2 + 3 * X := by
  have hX0 : 0 < X := by linarith
  set b := X ^ 3 + 3 * X ^ 2 + 3 * X with hb
  have hu : 0 < X + 1 := by linarith
  set t : ℝ := (X + 1) ^ ((1 : ℝ) / ((8 : ℕ) : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hu _
  have ht8 : t ^ 8 = X + 1 := root_pow _ hu.le 8 (by norm_num)
  have ht13 : 13 ≤ t := by
    by_contra hlt
    push Not at hlt
    have : t ^ 8 < 13 ^ 8 := pow_lt_pow_left₀ hlt ht0.le (by norm_num)
    norm_num at this
    nlinarith
  have hbpos : 1 ≤ b := by rw [hb]; nlinarith
  have hbu : b ≤ (X + 1) ^ 3 := by rw [hb]; nlinarith
  have hu3 : (X + 1) ^ 3 = (t ^ 12) ^ 2 := by rw [← ht8]; ring
  have hsq : √b ≤ t ^ 12 := by
    calc √b ≤ √((t ^ 12) ^ 2) := Real.sqrt_le_sqrt (hu3 ▸ hbu)
      _ = t ^ 12 := Real.sqrt_sq (by positivity)
  have hlog : Real.log b ≤ 24 * t := by
    calc Real.log b ≤ Real.log ((X + 1) ^ 3) := Real.log_le_log (by linarith) hbu
      _ = 24 * Real.log t := by rw [Real.log_pow, ← ht8, Real.log_pow]; push_cast; ring
      _ ≤ 24 * t := by
        have := Real.log_le_sub_one_of_pos ht0
        linarith
  have hlog0 : 0 ≤ Real.log b := Real.log_nonneg hbpos
  have hK : √b * Real.log b ^ 2 ≤ t ^ 12 * (24 * t) ^ 2 :=
    mul_le_mul hsq (pow_le_pow_left₀ hlog0 hlog 2) (by positivity) (by positivity)
  have hX8 : X = t ^ 8 - 1 := by linarith
  have h100 : 100 ≤ t ^ 8 := by
    have : (13 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht13 8
    norm_num at this; linarith
  have h169 : 169 * t ^ 14 ≤ t ^ 16 := by
    have : (169 : ℝ) ≤ t ^ 2 := by nlinarith
    calc 169 * t ^ 14 ≤ t ^ 2 * t ^ 14 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = t ^ 16 := by ring
  have hX2 : (99 / 100 * t ^ 8) ^ 2 ≤ X ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); rw [hX8]; linarith
  have h16 : (t ^ 8) ^ 2 = t ^ 16 := by ring
  have h14 : 0 < t ^ 14 := by positivity
  nlinarith [mul_pos h14 (by norm_num : (0:ℝ) < 1)]

/-- Under H1, H2 and RH: a prime strictly between `x³` and `(x+1)³` for every `x ≥ 10^9`. -/
theorem primeBetweenCubes (h1 : H1) (h2 : H2) (hRH : RiemannHypothesis) :
    ∀ x : ℕ, 10 ^ 9 ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3 := by
  intro x hx
  have hX : (10 : ℝ) ^ 9 ≤ (x : ℝ) := by exact_mod_cast hx
  set A : ℕ := x ^ 3 with hA
  set B : ℕ := x ^ 3 + 3 * x ^ 2 + 3 * x with hB
  have hAr : (A : ℝ) = (x : ℝ) ^ 3 := by simp [hA]
  have hBr : (B : ℝ) = (x : ℝ) ^ 3 + 3 * (x : ℝ) ^ 2 + 3 * x := by simp [hB]
  have hx0 : (0 : ℝ) < x := by linarith
  have hA599 : (599 : ℝ) ≤ A := by
    rw [hAr]; nlinarith [mul_pos hx0 hx0]
  have hAB : (A : ℝ) ≤ B := by rw [hAr, hBr]; nlinarith [mul_pos hx0 hx0]
  have hA1 := theta_sub_lt_quarter h1 h2 hRH hA599
  have hB1 := theta_sub_lt_quarter h1 h2 hRH (le_trans hA599 hAB)
  have hlogA : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by linarith)
  have hmono : √(A : ℝ) * Real.log (A : ℝ) ^ 2 ≤ √(B : ℝ) * Real.log (B : ℝ) ^ 2 :=
    mul_le_mul (Real.sqrt_le_sqrt hAB)
      (pow_le_pow_left₀ hlogA (Real.log_le_log (by linarith) hAB) 2) (by positivity)
      (Real.sqrt_nonneg _)
  have hkey := cubes_inequality (x : ℝ) hX
  rw [← hBr] at hkey
  rw [abs_lt] at hA1 hB1
  have hlt : θ (A : ℝ) < θ (B : ℝ) := by
    have : (B : ℝ) - A = 3 * (x : ℝ) ^ 2 + 3 * x := by rw [hAr, hBr]; ring
    nlinarith [hA1.1, hA1.2, hB1.1, hB1.2]
  obtain ⟨p, hp, hp1, hp2⟩ := exists_prime_of_theta_lt hlt
  refine ⟨p, hp, hp1, ?_⟩
  have : (x + 1) ^ 3 = B + 1 := by simp only [hB]; ring
  omega

/-! ### Step 3: the greedy sequence and the lower bound (no hypothesis)

A greedy sequence is any `g : ℕ → ℕ` with `g 0 = 2` such that `g (n+1)` is the least prime
`≥ (g n)^3`; the property is passed around as `hg`. -/

lemma exists_prime_ge (x : ℕ) : ∃ p, p.Prime ∧ x ≤ p := by
  obtain ⟨p, hp, hq⟩ := Nat.exists_infinite_primes x
  exact ⟨p, hq, hp⟩

lemma least_prime_eq {x p q : ℕ} (hq : q.Prime) (hxq : x ^ 3 ≤ q)
    (hmin : ∀ r, r.Prime → x ^ 3 ≤ r → q ≤ r) (hp : p.Prime) (h : x ^ 3 ≤ p)
    (hgap : ∀ r, x ^ 3 ≤ r → r < p → ¬ r.Prime) : q = p := by
  refine le_antisymm (hmin p hp h) ?_
  by_contra hlt
  exact hgap _ hxq (not_le.mp hlt) hq

/-- A Pratt/Lucas primality certificate: `5` is a primitive root mod `2521008887`, and
`2521008886 = 2 · 11 · 23 · 4982231` with `4982231` prime. -/
lemma prime_2521008887 : Nat.Prime 2521008887 := by
  have hp4 : Nat.Prime 4982231 := by norm_num
  have hfac : (2521008887 - 1 : ℕ) = 2 * 11 * 23 * 4982231 := by norm_num
  apply lucas_primality 2521008887 (5 : ZMod 2521008887)
  · show (5 : ZMod 2521008887) ^ 2521008886 = 1
    reduce_mod_char
  · intro q hq hdvd
    rw [hfac] at hdvd
    have key : q = 2 ∨ q = 11 ∨ q = 23 ∨ q = 4982231 := by
      rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq hp4).mp h
    rcases key with rfl | rfl | rfl | rfl
    · show (5 : ZMod 2521008887) ^ 1260504443 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 229182626 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 109609082 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 506 ≠ 1
      reduce_mod_char; decide

section Greedy

variable {g : ℕ → ℕ}

lemma g_one (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : g 1 = 11 := by
  obtain ⟨h0, hs⟩ := hg
  obtain ⟨hp, hc, hm⟩ := hs 0
  rw [h0] at hc hm
  refine least_prime_eq hp hc hm (by norm_num) (by norm_num) ?_
  intro q h1 h2
  have h1' : 8 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_two (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : g 2 = 1361 := by
  have e1 := g_one hg
  obtain ⟨hp, hc, hm⟩ := hg.2 1
  rw [e1] at hc hm
  refine least_prime_eq hp hc hm (by norm_num) (by norm_num) ?_
  intro q h1 h2
  have h1' : 1331 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_three (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : g 3 = 2521008887 := by
  have e2 := g_two hg
  obtain ⟨hp, hc, hm⟩ := hg.2 2
  rw [e2] at hc hm
  refine least_prime_eq hp hc hm prime_2521008887 (by norm_num) ?_
  intro q h1 h2
  have h1' : 2521008881 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_prime (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) (n : ℕ) : (g n).Prime := by
  cases n with
  | zero => rw [hg.1]; exact Nat.prime_two
  | succ n => exact (hg.2 n).1

lemma g_mono (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : Monotone g := by
  refine monotone_nat_of_le_succ fun n => ?_
  have := (hg.2 n).2.1
  calc g n ≤ g n ^ 3 := Nat.le_self_pow (by norm_num) _
    _ ≤ _ := this

/-- Any Mills number `A > 1` has `g n ≤ ⌊A^(3^(n+1))⌋₊`: the greedy sequence is minimal. -/
theorem g_le_floor (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {A : ℝ} (hA : 1 < A) (hM : IsMills A)
    (n : ℕ) : g n ≤ ⌊A ^ 3 ^ (n + 1)⌋₊ := by
  have hA0 : 0 ≤ A := by linarith
  have hprime : ∀ n : ℕ, (⌊A ^ 3 ^ (n + 1)⌋₊).Prime :=
    fun n => Nat.prime_iff.mpr (hM n.succPNat)
  induction n with
  | zero => rw [hg.1]; exact (hprime 0).two_le
  | succ n ih =>
    have hq : ⌊A ^ 3 ^ (n + 1)⌋₊ ^ 3 ≤ ⌊A ^ 3 ^ (n + 1 + 1)⌋₊ := by
      apply Nat.le_floor
      push_cast
      have h1 : ((⌊A ^ 3 ^ (n + 1)⌋₊ : ℕ) : ℝ) ≤ A ^ 3 ^ (n + 1) := Nat.floor_le (by positivity)
      calc ((⌊A ^ 3 ^ (n + 1)⌋₊ : ℕ) : ℝ) ^ 3 ≤ (A ^ 3 ^ (n + 1)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h1 3
        _ = A ^ 3 ^ (n + 1 + 1) := by rw [← pow_mul, ← pow_succ]
    exact (hg.2 n).2.2 _ (hprime (n + 1)) (le_trans (Nat.pow_le_pow_left ih 3) hq)

/-- **Lower bound, no hypotheses**: every Mills number `A > 1` exceeds `1.3063778838`. -/
theorem lower_bound (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {A : ℝ} (hA : 1 < A) (hM : IsMills A) :
    (1.3063778838 : ℝ) < A := by
  have h := le_trans (Nat.cast_le.mpr (g_le_floor hg hA hM 3))
    (Nat.floor_le (by positivity : (0 : ℝ) ≤ A ^ 3 ^ (3 + 1)))
  rw [g_three hg] at h
  norm_num at h
  by_contra hle
  push Not at hle
  have : A ^ 81 ≤ (1.3063778838 : ℝ) ^ 81 := pow_le_pow_left₀ (by linarith) hle 81
  have h2 : (1.3063778838 : ℝ) ^ 81 < 2521008887 := by norm_num
  linarith

/-! ### Step 4: the greedy limit is a Mills number below `1.3063778839` -/

/-- The strict step: `g (n+1) + 1 < (g n + 1)^3`, given primes between cubes from `x₀` on. -/
theorem g_succ_add_one_lt (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {x₀ : ℕ}
    (h : ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3)
    (hx : x₀ ≤ 2521008887) (n : ℕ) : g (n + 1) + 1 < (g n + 1) ^ 3 := by
  have hlt : g (n + 1) < (g n + 1) ^ 3 := by
    by_cases hn : 3 ≤ n
    · have h3 : x₀ ≤ g n := le_trans hx (by rw [← g_three hg]; exact g_mono hg hn)
      obtain ⟨p, hp, hp1, hp2⟩ := h (g n) h3
      exact lt_of_le_of_lt ((hg.2 n).2.2 p hp hp1.le) hp2
    · interval_cases n
      · rw [g_one hg, hg.1]; norm_num
      · rw [g_two hg, g_one hg]; norm_num
      · rw [g_three hg, g_two hg]; norm_num
  have hne : g (n + 1) + 1 ≠ (g n + 1) ^ 3 := by
    intro heq
    have hfac : g (n + 1) = g n * (g n ^ 2 + 3 * g n + 3) := by
      have : g (n + 1) + 1 = g n * (g n ^ 2 + 3 * g n + 3) + 1 := by rw [heq]; ring
      omega
    have hp := g_prime hg (n + 1)
    rw [hfac, Nat.prime_mul_iff] at hp
    have h2 := (g_prime hg n).two_le
    rcases hp with ⟨_, h1⟩ | ⟨_, h1⟩
    · nlinarith
    · omega
  omega

/-- The greedy limit `L = sup_n (g n)^(1/3^(n+1))` is a Mills number with `L^81 ≤ 2521008888`. -/
theorem exists_mills_lt (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {x₀ : ℕ}
    (h : ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3)
    (hx : x₀ ≤ 2521008887) :
    ∃ A : ℝ, A > 1 ∧ IsMills A ∧ A < 1.3063778839 := by
  -- the lower and upper roots
  have hpos : ∀ n, (0 : ℝ) < g n := fun n => by exact_mod_cast (g_prime hg n).pos
  have lo_pos : ∀ n, 0 < (g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) :=
    fun n => Real.rpow_pos_of_pos (hpos n) _
  have hi_pos : ∀ n, 0 < ((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) :=
    fun n => Real.rpow_pos_of_pos (by linarith [hpos n]) _
  have lo_pow : ∀ n, ((g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 1) = g n :=
    fun n => by
      have := root_pow (g n : ℝ) (hpos n).le (3 ^ (n + 1)) (by positivity)
      exact_mod_cast this
  have hi_pow : ∀ n, (((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 1)
      = (g n : ℝ) + 1 :=
    fun n => by
      have := root_pow ((g n : ℝ) + 1) (by linarith [hpos n]) (3 ^ (n + 1)) (by positivity)
      exact_mod_cast this
  set lo : ℕ → ℝ := fun n => (g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) with hlo
  set hi : ℕ → ℝ := fun n => ((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) with hhi
  have lo_le_hi : ∀ n, lo n ≤ hi n := fun n => by
    refine (pow_le_pow_iff_left₀ (lo_pos n).le (hi_pos n).le
      (by positivity : 3 ^ (n + 1) ≠ 0)).mp ?_
    rw [lo_pow, hi_pow]; linarith
  have lo_mono : Monotone lo := by
    refine monotone_nat_of_le_succ fun n => ?_
    refine (pow_le_pow_iff_left₀ (lo_pos n).le (lo_pos (n + 1)).le
      (by positivity : 3 ^ (n + 2) ≠ 0)).mp ?_
    have e1 : lo n ^ 3 ^ (n + 2) = (g n : ℝ) ^ 3 := by
      show ((g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 2) = _
      rw [pow_succ 3 (n + 1), pow_mul, lo_pow]
    have e2 : lo (n + 1) ^ 3 ^ (n + 2) = (g (n + 1) : ℝ) := lo_pow (n + 1)
    show lo n ^ 3 ^ (n + 2) ≤ lo (n + 1) ^ 3 ^ (n + 2)
    rw [e1, e2]
    exact_mod_cast (hg.2 n).2.1
  have hi_anti : Antitone hi := by
    refine antitone_nat_of_succ_le fun n => ?_
    refine (pow_le_pow_iff_left₀ (hi_pos (n + 1)).le (hi_pos n).le
      (by positivity : 3 ^ (n + 2) ≠ 0)).mp ?_
    have e1 : hi n ^ 3 ^ (n + 2) = ((g n : ℝ) + 1) ^ 3 := by
      show (((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 2) = _
      rw [pow_succ 3 (n + 1), pow_mul, hi_pow]
    have e2 : hi (n + 1) ^ 3 ^ (n + 2) = (g (n + 1) : ℝ) + 1 := hi_pow (n + 1)
    show hi (n + 1) ^ 3 ^ (n + 2) ≤ hi n ^ 3 ^ (n + 2)
    rw [e1, e2]
    have := g_succ_add_one_lt hg h hx n
    have h2 : ((g (n + 1) : ℝ) + 1) < ((g n : ℝ) + 1) ^ 3 := by exact_mod_cast this
    exact h2.le
  have lo_le_hi' : ∀ n m, lo n ≤ hi m := fun n m =>
    calc lo n ≤ lo (max n m) := lo_mono (le_max_left _ _)
      _ ≤ hi (max n m) := lo_le_hi _
      _ ≤ hi m := hi_anti (le_max_right _ _)
  set L : ℝ := ⨆ n, lo n with hL
  have lo_le_L : ∀ n, lo n ≤ L := fun n =>
    le_ciSup ⟨hi 0, by rintro _ ⟨m, rfl⟩; exact lo_le_hi' m 0⟩ n
  have L_le_hi : ∀ m, L ≤ hi m := fun m => ciSup_le fun n => lo_le_hi' n m
  have L0 : 0 ≤ L := le_trans (lo_pos 0).le (lo_le_L 0)
  have hfloor : ∀ k, ⌊L ^ 3 ^ (k + 1)⌋₊ = g k := fun k => by
    rw [Nat.floor_eq_iff (pow_nonneg L0 _)]
    constructor
    · calc (g k : ℝ) = lo k ^ 3 ^ (k + 1) := (lo_pow k).symm
        _ ≤ _ := pow_le_pow_left₀ (lo_pos k).le (lo_le_L k) _
    · have h1 : L ^ 3 ^ (k + 1) ≤ hi (k + 1) ^ 3 ^ (k + 1) :=
        pow_le_pow_left₀ L0 (L_le_hi (k + 1)) _
      have h2 : (hi (k + 1) ^ 3 ^ (k + 1)) ^ 3 < ((g k : ℝ) + 1) ^ 3 := by
        rw [← pow_mul, ← pow_succ, hi_pow]
        have := g_succ_add_one_lt hg h hx k
        exact_mod_cast this
      have h3 : hi (k + 1) ^ 3 ^ (k + 1) < (g k : ℝ) + 1 :=
        lt_of_pow_lt_pow_left₀ 3 (by positivity) h2
      linarith
  have hL1 : 1 < L := by
    have h1 : 1 < lo 0 := by
      by_contra hle
      push Not at hle
      have : lo 0 ^ 3 ^ (0 + 1) ≤ 1 := pow_le_one₀ (lo_pos 0).le hle
      rw [lo_pow, hg.1] at this
      norm_num at this
    linarith [lo_le_L 0]
  have hMills : IsMills L := by
    intro n
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    rw [hk, hfloor k]
    exact Nat.prime_iff.mp (g_prime hg k)
  have hL81 : L ^ 81 ≤ 2521008888 := by
    have h1 : L ^ 3 ^ (3 + 1) ≤ hi 3 ^ 3 ^ (3 + 1) := pow_le_pow_left₀ L0 (L_le_hi 3) _
    rw [hi_pow, g_three hg] at h1
    norm_num at h1 ⊢
    linarith
  refine ⟨L, hL1, hMills, ?_⟩
  by_contra hle
  push Not at hle
  have h1 : (1.3063778839 : ℝ) ^ 81 ≤ L ^ 81 := pow_le_pow_left₀ (by norm_num) hle 81
  have h3 : (2521008888 : ℝ) < (1.3063778839 : ℝ) ^ 81 := by norm_num
  linarith

end Greedy

/-- A greedy sequence exists: `g 0 = 2`, `g (n+1)` the least prime `≥ (g n)^3`. -/
lemma exists_greedy : ∃ g : ℕ → ℕ, g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
    ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p := by
  refine ⟨fun n => Nat.rec 2 (fun _ x => Nat.find (exists_prime_ge (x ^ 3))) n, rfl, ?_⟩
  intro n
  exact ⟨(Nat.find_spec (exists_prime_ge _)).1, (Nat.find_spec (exists_prime_ge _)).2,
    fun p hp h => Nat.find_min' (exists_prime_ge _) ⟨hp, h⟩⟩

theorem main : H1 → H2 → type_of% @Mills.lower_bound_of_RH := by
  intro h1 h2 hRH A hA
  obtain ⟨g, hg⟩ := exists_greedy
  refine ⟨lower_bound hg hA.1.1 hA.1.2, ?_⟩
  obtain ⟨B, hB1, hBM, hBlt⟩ :=
    exists_mills_lt hg (primeBetweenCubes h1 h2 hRH) (by norm_num)
  exact lt_of_le_of_lt (hA.2 ⟨hB1, hBM⟩) hBlt

end OMA.R_Mills_lower_bound_of_RH_R1
