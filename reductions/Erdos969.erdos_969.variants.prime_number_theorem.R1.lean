import FormalConjectures.ErdosProblems.«969»

-- Reduction Erdos969.erdos_969.variants.prime_number_theorem.R1 of Erdős Problem 969 — prime number theorem
-- Credit: @hyprspacecoyote
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# How the prime number theorem gives `E(x) = o(√x)`

Write `M(n) = ∑_{d ≤ n} μ(d)` (Mertens' function), `s = ⌊√x⌋` and `L = 6 / π²`. Three inputs:

* `H1`: the prime number theorem in Landau's equivalent form `M(n) = o(n)`;
* `H2`: the elementary identity `Q(x) = ∑_{d ≤ √x} μ(d) ⌊x / d²⌋`;
* `H3`: `∑_d μ(d) / d² = 6 / π²` (`= 1 / ζ(2)`).

Then `E(x) = -∑_{d ≤ s} μ(d) {x / d²} - x ∑_{d > s} μ(d) / d²`, and summation by parts bounds both
parts using only `M(n) = o(n)`:

* the tail `∑_{d > s} μ(d) / d²` is at most `6 ε / s`, so `x` times it is `≤ 24 ε s`;
* in the first sum, the terms `d ≤ s / K` contribute at most `s / K`, and the rest (where
  `{x / d²}` has total variation `≤ 2 x / (s / K)² ≤ 32 K²`) contribute `≤ 2 ε s (1 + 32 K²)`.

Choosing `K` large and then `ε` small gives `|E(x)| ≤ η √x` for large `x`. Everything except the three
inputs is proved here.
-/

namespace OMA.R_Erdos969_erdos_969_variants_prime_number_theorem_R1

open Filter Topology Asymptotics Finset

/-- The prime number theorem in the form `M(n) = o(n)`, where `M` is Mertens' function. -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    |∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius d : ℝ)| ≤ ε * n

/-- The squarefree counting function as a Möbius sum: `Q(x) = ∑_{d ≤ √x} μ(d) ⌊x / d²⌋`. -/
def H2 : Prop :=
  ∀ x : ℕ, (Erdos969.squarefreeCounting x : ℤ) =
    ∑ d ∈ Finset.Icc 1 (Nat.sqrt x), ArithmeticFunction.moebius d * ((x / d ^ 2 : ℕ) : ℤ)

/-- `∑_{d ≥ 1} μ(d) / d² = 1 / ζ(2) = 6 / π²`. -/
def H3 : Prop :=
  HasSum (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) (6 / Real.pi ^ 2)

/- ## Summation by parts -/

lemma abel (c g : ℕ → ℝ) (a : ℕ) : ∀ b, a ≤ b →
    ∑ d ∈ Ioc a b, c d * g d = (∑ d ∈ Ioc a b, c d) * g b +
      ∑ d ∈ Ico a b, (∑ e ∈ Ioc a d, c e) * (g d - g (d + 1)) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb, Finset.sum_Ioc_succ_top hb, Finset.sum_Ico_succ_top hb, ih]
    ring

lemma telescope (u : ℕ → ℝ) (a : ℕ) : ∀ b, a ≤ b →
    ∑ d ∈ Ico a b, (u d - u (d + 1)) = u a - u b := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih]
    ring

lemma abel_bound (c g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (B : ℝ)
    (hS : ∀ d, a ≤ d → d ≤ b → |∑ e ∈ Ioc a d, c e| ≤ B) :
    |∑ d ∈ Ioc a b, c d * g d| ≤ B * (|g b| + ∑ d ∈ Ico a b, |g d - g (d + 1)|) := by
  rw [abel c g a b hab]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hS b hab le_rfl)
  calc |(∑ d ∈ Ioc a b, c d) * g b + ∑ d ∈ Ico a b, (∑ e ∈ Ioc a d, c e) * (g d - g (d + 1))|
      ≤ |(∑ d ∈ Ioc a b, c d) * g b| +
          |∑ d ∈ Ico a b, (∑ e ∈ Ioc a d, c e) * (g d - g (d + 1))| := abs_add_le _ _
    _ ≤ B * |g b| + ∑ d ∈ Ico a b, B * |g d - g (d + 1)| := by
        gcongr
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hS b hab le_rfl) (abs_nonneg _)
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
          rw [Finset.mem_Ico] at hd
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hS d hd.1 hd.2.le) (abs_nonneg _)
    _ = B * (|g b| + ∑ d ∈ Ico a b, |g d - g (d + 1)|) := by rw [← Finset.mul_sum]; ring

/- ## Mertens' function -/

lemma sum_Ioc_eq_M_sub (a d : ℕ) (had : a ≤ d) :
    ∑ e ∈ Ioc a d, (ArithmeticFunction.moebius e : ℝ) = (∑ e ∈ Ioc 0 d, (ArithmeticFunction.moebius e : ℝ)) - (∑ e ∈ Ioc 0 a, (ArithmeticFunction.moebius e : ℝ)) := by
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) had]
  ring

lemma Icc_one_eq_Ioc (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n :=
  Finset.Icc_succ_left_eq_Ioc 0 n

lemma abs_moebius_le (d : ℕ) : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
  have := ArithmeticFunction.abs_moebius_le_one (n := d)
  exact_mod_cast this

/- ## The tail `∑_{d > a} μ(d) / d²` -/

lemma inv_sq_step (d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) * (1 / (d : ℝ) ^ 2 - 1 / ((d + 1 : ℕ) : ℝ) ^ 2) ≤
      2 * (1 / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ)) := by
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  push_cast
  have hpos : (0 : ℝ) < d := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity),
    mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  ring_nf
  nlinarith [pow_pos hpos 3, pow_pos hpos 4, pow_pos hpos 5, pow_pos hpos 6, pow_pos hpos 2]

lemma tail_finite (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : ∀ n, T ≤ n → |(∑ e ∈ Ioc 0 n, (ArithmeticFunction.moebius e : ℝ))| ≤ ε * n)
    (a b : ℕ) (ha : T ≤ a) (ha1 : 1 ≤ a) (hab : a ≤ b) :
    |∑ d ∈ Ioc a b, (ArithmeticFunction.moebius d : ℝ) * (1 / (d : ℝ) ^ 2)| ≤ 6 * ε / a := by
  rw [abel _ _ a b hab]
  have hS : ∀ d, a ≤ d → |∑ e ∈ Ioc a d, (ArithmeticFunction.moebius e : ℝ)| ≤ 2 * ε * d := by
    intro d hd
    rw [sum_Ioc_eq_M_sub a d hd]
    have h1 := hT d (le_trans ha hd)
    have h2 := hT a ha
    have : (a : ℝ) ≤ d := by exact_mod_cast hd
    calc |(∑ e ∈ Ioc 0 d, (ArithmeticFunction.moebius e : ℝ)) - (∑ e ∈ Ioc 0 a, (ArithmeticFunction.moebius e : ℝ))| ≤ |(∑ e ∈ Ioc 0 d, (ArithmeticFunction.moebius e : ℝ))| + |(∑ e ∈ Ioc 0 a, (ArithmeticFunction.moebius e : ℝ))| := abs_sub _ _
      _ ≤ ε * d + ε * a := add_le_add h1 h2
      _ ≤ 2 * ε * d := by nlinarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (le_trans ha1 hab)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hfirst : |(∑ d ∈ Ioc a b, (ArithmeticFunction.moebius d : ℝ)) * (1 / (b : ℝ) ^ 2)| ≤
      2 * ε / a := by
    rw [abs_mul]
    calc |∑ d ∈ Ioc a b, (ArithmeticFunction.moebius d : ℝ)| * |1 / (b : ℝ) ^ 2|
        ≤ (2 * ε * b) * (1 / (b : ℝ) ^ 2) := by
          rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (b : ℝ) ^ 2)]
          exact mul_le_mul_of_nonneg_right (hS b hab) (by positivity)
      _ = 2 * ε / b := by field_simp
      _ ≤ 2 * ε / a := div_le_div_of_nonneg_left (by positivity) ha0 hab'
  have hsecond : |∑ d ∈ Ico a b, (∑ e ∈ Ioc a d, (ArithmeticFunction.moebius e : ℝ)) *
      (1 / (d : ℝ) ^ 2 - 1 / ((d + 1 : ℕ) : ℝ) ^ 2)| ≤ 4 * ε / a := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ Ico a b, |(∑ e ∈ Ioc a d, (ArithmeticFunction.moebius e : ℝ)) *
          (1 / (d : ℝ) ^ 2 - 1 / ((d + 1 : ℕ) : ℝ) ^ 2)|
        ≤ ∑ d ∈ Ico a b, (4 * ε) * (1 / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Ico] at hd
          have hd1 : 1 ≤ d := le_trans ha1 hd.1
          have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
          have hnn : 0 ≤ 1 / (d : ℝ) ^ 2 - 1 / ((d + 1 : ℕ) : ℝ) ^ 2 := by
            rw [sub_nonneg]
            apply one_div_le_one_div_of_le (by positivity)
            push_cast
            nlinarith
          rw [abs_mul, abs_of_nonneg hnn]
          calc |∑ e ∈ Ioc a d, (ArithmeticFunction.moebius e : ℝ)| *
                (1 / (d : ℝ) ^ 2 - 1 / ((d + 1 : ℕ) : ℝ) ^ 2)
              ≤ (2 * ε * d) * (1 / (d : ℝ) ^ 2 - 1 / ((d + 1 : ℕ) : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right (hS d hd.1) hnn
            _ = (2 * ε) * ((d : ℝ) * (1 / (d : ℝ) ^ 2 - 1 / ((d + 1 : ℕ) : ℝ) ^ 2)) := by ring
            _ ≤ (2 * ε) * (2 * (1 / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_left (inv_sq_step d hd1) (by positivity)
            _ = (4 * ε) * (1 / (d : ℝ) - 1 / ((d + 1 : ℕ) : ℝ)) := by ring
      _ = (4 * ε) * (1 / (a : ℝ) - 1 / (b : ℝ)) := by
          rw [← Finset.mul_sum, telescope (fun d : ℕ => 1 / (d : ℝ)) a b hab]
      _ ≤ 4 * ε / a := by
          have h0 : 0 ≤ (4 * ε) * (1 / (b : ℝ)) := by positivity
          have h1 : (4 * ε) * (1 / (a : ℝ)) = 4 * ε / a := by ring
          rw [mul_sub, h1]
          linarith
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * ε / a + 4 * ε / a := add_le_add hfirst hsecond
    _ = 6 * ε / a := by ring

lemma range_succ_eq_Ioc (f : ℕ → ℝ) (hf : f 0 = 0) (b : ℕ) :
    ∑ d ∈ range (b + 1), f d = ∑ d ∈ Ioc 0 b, f d := by
  induction b with
  | zero => simp [hf]
  | succ b ih => rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le b)]

lemma tail_bound (h3 : H3) (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : ∀ n, T ≤ n → |(∑ e ∈ Ioc 0 n, (ArithmeticFunction.moebius e : ℝ))| ≤ ε * n)
    (a : ℕ) (ha : T ≤ a) (ha1 : 1 ≤ a) :
    |6 / Real.pi ^ 2 - ∑ d ∈ Ioc 0 a, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2| ≤
      6 * ε / a := by
  set f : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 with hf
  have hf0 : f 0 = 0 := by simp [hf]
  have ht : Tendsto (fun b : ℕ => ∑ d ∈ Ioc 0 b, f d) atTop (𝓝 (6 / Real.pi ^ 2)) := by
    have := (h3.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun b => ?_
    simp only [Function.comp]
    exact range_succ_eq_Ioc f hf0 b
  have ht2 : Tendsto (fun b : ℕ => |∑ d ∈ Ioc 0 b, f d - ∑ d ∈ Ioc 0 a, f d|) atTop
      (𝓝 |6 / Real.pi ^ 2 - ∑ d ∈ Ioc 0 a, f d|) := (ht.sub_const _).abs
  refine le_of_tendsto ht2 ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hb, add_sub_cancel_left]
  have := tail_finite ε hε T hT a b ha ha1 hb
  have e : ∑ d ∈ Ioc a b, f d =
      ∑ d ∈ Ioc a b, (ArithmeticFunction.moebius d : ℝ) * (1 / (d : ℝ) ^ 2) :=
    Finset.sum_congr rfl (fun d _ => by simp only [hf]; ring)
  rw [e]
  exact this

/- ## The fractional parts `{x / d²}` -/

lemma floor_div_sq (x d : ℕ) : ((x / d ^ 2 : ℕ) : ℝ) = ⌊(x : ℝ) / (d : ℝ) ^ 2⌋₊ := by
  have := Nat.floor_div_eq_div (K := ℝ) x (d ^ 2)
  push_cast at this
  rw [this]

lemma frac_bounds (x d : ℕ) :
    0 ≤ (x : ℝ) / (d : ℝ) ^ 2 - ((x / d ^ 2 : ℕ) : ℝ) ∧
      (x : ℝ) / (d : ℝ) ^ 2 - ((x / d ^ 2 : ℕ) : ℝ) ≤ 1 := by
  rw [floor_div_sq]
  have h0 : 0 ≤ (x : ℝ) / (d : ℝ) ^ 2 := by positivity
  constructor
  · linarith [Nat.floor_le h0]
  · linarith [Nat.lt_floor_add_one ((x : ℝ) / (d : ℝ) ^ 2)]

lemma frac_variation (x a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ d ∈ Ico a b, |((x : ℝ) / (d : ℝ) ^ 2 - ((x / d ^ 2 : ℕ) : ℝ)) -
      ((x : ℝ) / ((d + 1 : ℕ) : ℝ) ^ 2 - ((x / (d + 1) ^ 2 : ℕ) : ℝ))| ≤
      2 * ((x : ℝ) / (a : ℝ) ^ 2) := by
  have hstep : ∀ d ∈ Ico a b, |((x : ℝ) / (d : ℝ) ^ 2 - ((x / d ^ 2 : ℕ) : ℝ)) -
      ((x : ℝ) / ((d + 1 : ℕ) : ℝ) ^ 2 - ((x / (d + 1) ^ 2 : ℕ) : ℝ))| ≤
      ((x : ℝ) / (d : ℝ) ^ 2 - (x : ℝ) / ((d + 1 : ℕ) : ℝ) ^ 2) +
      (((x / d ^ 2 : ℕ) : ℝ) - ((x / (d + 1) ^ 2 : ℕ) : ℝ)) := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    have hd1 : 1 ≤ d := le_trans ha hd.1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hA : 0 ≤ (x : ℝ) / (d : ℝ) ^ 2 - (x : ℝ) / ((d + 1 : ℕ) : ℝ) ^ 2 := by
      rw [sub_nonneg]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      push_cast; nlinarith
    have hB : 0 ≤ ((x / d ^ 2 : ℕ) : ℝ) - ((x / (d + 1) ^ 2 : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact_mod_cast Nat.div_le_div_left (Nat.pow_le_pow_left (Nat.le_succ d) 2) (by positivity)
    rw [abs_le]
    constructor <;> linarith
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib,
    telescope (fun d : ℕ => (x : ℝ) / (d : ℝ) ^ 2) a b hab,
    telescope (fun d : ℕ => ((x / d ^ 2 : ℕ) : ℝ)) a b hab]
  have h1 : 0 ≤ (x : ℝ) / (b : ℝ) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ ((x / b ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : ((x / a ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) / (a : ℝ) ^ 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := x) (n := a ^ 2)
    push_cast at this
    exact this
  linarith

/- ## The main estimate -/

theorem main : H1 → H2 → H3 → type_of% @Erdos969.erdos_969.variants.prime_number_theorem := by
  intro h1 h2 h3
  rw [Asymptotics.isLittleO_iff]
  intro η hη
  obtain ⟨K, hK⟩ := exists_nat_ge (2 / η + 1)
  have hK1 : (1 : ℝ) ≤ K := by
    have : 0 < 2 / η := by positivity
    linarith
  have hKn : 1 ≤ K := by exact_mod_cast hK1
  have hKη : 1 / (K : ℝ) ≤ η / 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : 2 / η ≤ K := by linarith
    rw [div_le_iff₀ hη] at this
    linarith
  set C : ℝ := 26 + 64 * (K : ℝ) ^ 2 with hC
  have hCpos : 0 < C := by positivity
  set ε : ℝ := η / (2 * C) with hεdef
  have hε : 0 < ε := by positivity
  have hεC : ε * C = η / 2 := by rw [hεdef]; field_simp
  -- `|(∑ e ∈ Ioc 0 n, (ArithmeticFunction.moebius e : ℝ))| ≤ ε n` for `n ≥ T`
  obtain ⟨T, hT⟩ := eventually_atTop.1 (h1 ε hε)
  have hTM : ∀ n, T ≤ n → |(∑ e ∈ Ioc 0 n, (ArithmeticFunction.moebius e : ℝ))| ≤ ε * n := by
    intro n hn
    have := hT n hn
    rwa [← Icc_one_eq_Ioc]
  set N0 := T * K + 2 * K + T + 1 with hN0
  filter_upwards [eventually_ge_atTop (N0 * N0)] with x hx
  set s := Nat.sqrt x with hs
  have hsN : N0 ≤ s := Nat.le_sqrt.2 hx
  have hs1 : 1 ≤ s := by omega
  have hsT : T ≤ s := by omega
  set a := s / K with ha
  have haT : T ≤ a := by
    rw [ha, Nat.le_div_iff_mul_le (by omega)]
    nlinarith
  have ha1 : 1 ≤ a := by
    rw [ha, Nat.le_div_iff_mul_le (by omega)]
    omega
  have has : a ≤ s := Nat.div_le_self _ _
  have haK : a * K ≤ s := Nat.div_mul_le_self s K
  have hs2a : s < 2 * a * K := by
    have := Nat.lt_div_mul_add (a := s) (b := K) (by omega)
    rw [← ha] at this
    nlinarith
  have hxs : x < (s + 1) * (s + 1) := Nat.lt_succ_sqrt x
  -- real versions
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hxR : (x : ℝ) ≤ 4 * (s : ℝ) ^ 2 := by
    have : x ≤ 4 * s ^ 2 := by nlinarith
    exact_mod_cast this
  have hxa : (x : ℝ) / (a : ℝ) ^ 2 ≤ 16 * (K : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1' : (s : ℝ) < 2 * a * K := by exact_mod_cast hs2a
    have h2' : (0 : ℝ) ≤ s := by positivity
    nlinarith
  have haKR : (a : ℝ) ≤ s / K := by
    rw [le_div_iff₀ (by linarith)]
    exact_mod_cast haK
  -- decomposition of `E(x)`
  set g : ℕ → ℝ := fun d => (x : ℝ) / (d : ℝ) ^ 2 - ((x / d ^ 2 : ℕ) : ℝ) with hg
  set c : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) with hc
  set P := ∑ d ∈ Ioc 0 s, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 with hP
  have hQ : (Erdos969.squarefreeCounting x : ℝ) =
      ∑ d ∈ Ioc 0 s, c d * ((x / d ^ 2 : ℕ) : ℝ) := by
    have := h2 x
    rw [Icc_one_eq_Ioc] at this
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at this
    rw [← hs] at this
    exact_mod_cast this
  have hE : Erdos969.squarefreeCountingError x =
      -(∑ d ∈ Ioc 0 s, c d * g d) - x * (6 / Real.pi ^ 2 - P) := by
    have key : ∑ d ∈ Ioc 0 s, c d * ((x / d ^ 2 : ℕ) : ℝ) =
        -(∑ d ∈ Ioc 0 s, c d * g d) + (x : ℝ) * P := by
      rw [hP, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hg, hc]
      ring
    unfold Erdos969.squarefreeCountingError
    rw [hQ, key]
    ring
  -- part A1: `d ≤ a`
  have hA1 : |∑ d ∈ Ioc 0 a, c d * g d| ≤ a := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ Ioc 0 a, |c d * g d| ≤ ∑ d ∈ Ioc 0 a, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d _
          rw [abs_mul]
          have hg1 := frac_bounds x d
          have : |g d| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hg1.1, hg1.2]
          calc |c d| * |g d| ≤ 1 * 1 :=
                mul_le_mul (abs_moebius_le d) this (abs_nonneg _) zero_le_one
            _ = 1 := by ring
      _ = a := by simp
  -- part A2: `a < d ≤ s`
  have hA2 : |∑ d ∈ Ioc a s, c d * g d| ≤ 2 * ε * s * (1 + 32 * (K : ℝ) ^ 2) := by
    have hB : ∀ d, a ≤ d → d ≤ s → |∑ e ∈ Ioc a d, c e| ≤ 2 * ε * s := by
      intro d hd hds
      simp only [hc]
      rw [sum_Ioc_eq_M_sub a d hd]
      have h1' := hTM d (le_trans haT hd)
      have h2' := hTM a haT
      have : (d : ℝ) ≤ s := by exact_mod_cast hds
      have : (a : ℝ) ≤ s := by exact_mod_cast has
      calc |(∑ e ∈ Ioc 0 d, (ArithmeticFunction.moebius e : ℝ)) - (∑ e ∈ Ioc 0 a, (ArithmeticFunction.moebius e : ℝ))| ≤ |(∑ e ∈ Ioc 0 d, (ArithmeticFunction.moebius e : ℝ))| + |(∑ e ∈ Ioc 0 a, (ArithmeticFunction.moebius e : ℝ))| := abs_sub _ _
        _ ≤ ε * d + ε * a := add_le_add h1' h2'
        _ ≤ 2 * ε * s := by nlinarith
    refine (abel_bound c g a s has _ hB).trans ?_
    have hgs : |g s| ≤ 1 := by
      have hg1 := frac_bounds x s
      rw [abs_le]; constructor <;> linarith [hg1.1, hg1.2]
    have hvar := frac_variation x a s ha1 has
    have hvar' : ∑ d ∈ Ico a s, |g d - g (d + 1)| ≤ 32 * (K : ℝ) ^ 2 := by
      have : ∑ d ∈ Ico a s, |g d - g (d + 1)| ≤ 2 * ((x : ℝ) / (a : ℝ) ^ 2) := by
        simpa [hg] using hvar
      linarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  -- the tail
  have htail := tail_bound h3 ε hε T hTM s hsT hs1
  have hxtail : |(x : ℝ) * (6 / Real.pi ^ 2 - P)| ≤ 24 * ε * s := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg x)]
    calc (x : ℝ) * |6 / Real.pi ^ 2 - P| ≤ (4 * (s : ℝ) ^ 2) * (6 * ε / s) :=
          mul_le_mul hxR htail (abs_nonneg _) (by positivity)
      _ = 24 * ε * s := by field_simp; ring
  -- assemble
  have hsplit : ∑ d ∈ Ioc 0 s, c d * g d =
      ∑ d ∈ Ioc 0 a, c d * g d + ∑ d ∈ Ioc a s, c d * g d :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le a) has).symm
  have hsqrt : (s : ℝ) ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt
  have hbound : |Erdos969.squarefreeCountingError x| ≤ η * s := by
    rw [hE, hsplit]
    calc |-(∑ d ∈ Ioc 0 a, c d * g d + ∑ d ∈ Ioc a s, c d * g d) -
          (x : ℝ) * (6 / Real.pi ^ 2 - P)|
        ≤ |∑ d ∈ Ioc 0 a, c d * g d| + |∑ d ∈ Ioc a s, c d * g d| +
            |(x : ℝ) * (6 / Real.pi ^ 2 - P)| := by
          have := abs_sub (-(∑ d ∈ Ioc 0 a, c d * g d + ∑ d ∈ Ioc a s, c d * g d))
            ((x : ℝ) * (6 / Real.pi ^ 2 - P))
          rw [abs_neg] at this
          linarith [abs_add_le (∑ d ∈ Ioc 0 a, c d * g d) (∑ d ∈ Ioc a s, c d * g d)]
      _ ≤ s / K + 2 * ε * s * (1 + 32 * (K : ℝ) ^ 2) + 24 * ε * s := by
          linarith
      _ = (s : ℝ) * (1 / K) + (s : ℝ) * (ε * C) := by rw [hC]; field_simp; ring
      _ ≤ (s : ℝ) * (η / 2) + (s : ℝ) * (η / 2) := by
          rw [hεC]
          gcongr
      _ = η * s := by ring
  rw [Real.norm_eq_abs, abs_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc |Erdos969.squarefreeCountingError x| ≤ η * s := hbound
    _ ≤ η * Real.sqrt x := mul_le_mul_of_nonneg_left hsqrt hη.le

end OMA.R_Erdos969_erdos_969_variants_prime_number_theorem_R1
