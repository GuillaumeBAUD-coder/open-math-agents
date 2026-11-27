import FormalConjectures.ErdosProblems.«1070»

-- Reduction Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1 of Erdős Problem 1070 — matolcsi ruzsa varga zsamboki
-- Credit: @hyprspacecoyote
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `f(n) ≤ (1/4 + o(1)) n` from the Matolcsi–Ruzsa–Varga–Zsámboki graphs

* `H1` is the construction of [MRVZ23]: for every `ε > 0` a finite unit distance graph in the plane
  with independence number at most `(1/4 + ε)` times its order (this is the upstream statement
  `erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki_graphs`).
* `H2` is subadditivity, `f(a + b) ≤ f(a) + f(b)`: place an `a`-point configuration and a
  `b`-point configuration far apart (no unit distances between them), as in the docstring of
  `erdos_1070.parts.i`.

Given the `k`-point set `X` of `H1` with `f(k) ≤ α(X) ≤ (1/4 + ε/2) k`, write `n = q k + r` with
`r < k`; then `f(n) ≤ q f(k) + f(r) ≤ (1/4 + ε/2) n + k ≤ (1/4 + ε) n` for `n ≥ 2k/ε`.
Everything except `H1` and `H2` is proved here.
-/

namespace OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1

open Filter SimpleGraph

/-- [MRVZ23]: finite unit distance graphs with independence ratio at most `1/4 + ε`. -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∃ X : Finset (EuclideanSpace ℝ (Fin 2)), X.Nonempty ∧
    ((UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum : ℝ) ≤
      (1 / 4 + ε) * X.card

/-- Subadditivity of `f`: two configurations placed far apart. -/
def H2 : Prop := ∀ a b : ℕ, Erdos1070.f (a + b) ≤ Erdos1070.f a + Erdos1070.f b

lemma f_le_self (r : ℕ) : Erdos1070.f r ≤ r := by
  classical
  let φ : ℕ → EuclideanSpace ℝ (Fin 2) := fun t => !₂[(t : ℝ), 0]
  have hφ : Function.Injective φ := by
    intro a b h
    have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
    simp [φ] at this
    exact_mod_cast this
  set X := (Finset.range r).image φ with hX
  have hcard : X.card = r := by
    rw [hX, Finset.card_image_of_injective _ hφ, Finset.card_range]
  have hf := Erdos1070.f_le X
  rw [hcard] at hf
  refine hf.trans ?_
  obtain ⟨s, hs⟩ :=
    (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  calc s.card ≤ Fintype.card (X : Set (EuclideanSpace ℝ (Fin 2))) := Finset.card_le_univ s
    _ = X.card := by simp
    _ = r := hcard

lemma f_mul_add (h2 : H2) (k : ℕ) : ∀ q r : ℕ,
    Erdos1070.f (q * k + r) ≤ q * Erdos1070.f k + Erdos1070.f r := by
  intro q r
  induction q with
  | zero => simp
  | succ q ih =>
    have : (q + 1) * k + r = k + (q * k + r) := by ring
    rw [this]
    calc Erdos1070.f (k + (q * k + r)) ≤ Erdos1070.f k + Erdos1070.f (q * k + r) := h2 _ _
      _ ≤ Erdos1070.f k + (q * Erdos1070.f k + Erdos1070.f r) := by omega
      _ = (q + 1) * Erdos1070.f k + Erdos1070.f r := by ring

theorem main : H1 → H2 → type_of% @Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki := by
  intro h1 h2 ε hε
  obtain ⟨X, hXne, hX⟩ := h1 (ε / 2) (by positivity)
  set k := X.card with hk
  have hk1 : 1 ≤ k := Finset.card_pos.2 hXne
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hfk : (Erdos1070.f k : ℝ) ≤ (1 / 4 + ε / 2) * k := by
    have := Erdos1070.f_le X
    rw [← hk] at this
    exact le_trans (by exact_mod_cast this) hX
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * k / ε)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (2 * k / ε : ℝ) ≤ n := le_trans hN (by exact_mod_cast hn)
  have hkn : (k : ℝ) ≤ ε / 2 * n := by
    rw [div_le_iff₀ hε] at hnR
    linarith
  set q := n / k with hq
  set r := n % k with hr
  have hdecomp : n = q * k + r := by rw [hq, hr, mul_comm]; exact (Nat.div_add_mod n k).symm
  have hrk : r < k := Nat.mod_lt _ (by omega)
  have hmain := f_mul_add h2 k q r
  rw [← hdecomp] at hmain
  have hfr := f_le_self r
  have hmainR : (Erdos1070.f n : ℝ) ≤ q * (Erdos1070.f k : ℝ) + r := by
    have : (Erdos1070.f n : ℝ) ≤ ((q * Erdos1070.f k + Erdos1070.f r : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast at this
    have : (Erdos1070.f r : ℝ) ≤ r := by exact_mod_cast hfr
    linarith
  have hnR' : (n : ℝ) = q * k + r := by exact_mod_cast hdecomp
  have hrR : (r : ℝ) ≤ k := by exact_mod_cast hrk.le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  calc (Erdos1070.f n : ℝ) ≤ q * (Erdos1070.f k : ℝ) + r := hmainR
    _ ≤ q * ((1 / 4 + ε / 2) * k) + r := by gcongr
    _ ≤ (1 / 4 + ε / 2) * n + k := by rw [hnR']; nlinarith
    _ ≤ (1 / 4 + ε) * n := by linarith

end OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1
