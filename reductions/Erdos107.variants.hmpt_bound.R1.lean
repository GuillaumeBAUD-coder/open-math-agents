import FormalConjectures.ErdosProblems.«107»

-- Reduction Erdos107.variants.hmpt_bound.R1 of Erdős Problem 107 — hmpt bound
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The proof of Holmsen–Mojarrad–Pach–Tardos (following Suk) has two parts.

* `H1` is the positive-fraction Erdős–Szekeres theorem of Pór and Valtr (2002), with an
  unspecified absolute constant `A` (Pór–Valtr give `A = 32` for `k ≥ 4`; the cases
  `k ≤ 3` are trivial): a general-position set `X` with at least `2^(A k)` points has `k`
  parts `T i`, each holding at least a `2^(-A k)` fraction of `X`, such that every
  transversal consists of `k` distinct points in convex position.
* `H2` is the HMPT step inside such a configuration: for a suitable number of parts
  `k = O(sqrt (n log n))` (HMPT take `k ≈ sqrt (n / log n)`), if every part has more than
  `2^(n + C sqrt (n log n))` points, the union contains a convex `n`-gon.

`main` derives the target: the loss `2^(A k)` of `H1` is absorbed in the error term, the
finite prefix and the passage from thresholds to `f` are handled below.
-/

open Filter
open scoped Asymptotics EuclideanGeometry

namespace OMA.R_Erdos107_variants_hmpt_bound_R1

/-- Pór–Valtr positive-fraction Erdős–Szekeres theorem (weak form, some constant `A`). -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ X : Finset (EuclideanSpace ℝ (Fin 2)),
    (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z →
      ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) →
    2 ^ (A * k) ≤ X.card →
    ∃ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)),
      (∀ i, T i ⊆ X) ∧ (∀ i, X.card ≤ 2 ^ (A * k) * (T i).card) ∧
      ∀ g : Fin k → EuclideanSpace ℝ (Fin 2), (∀ i, g i ∈ T i) →
        Function.Injective g ∧ ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a})

/-- The Holmsen–Mojarrad–Pach–Tardos step inside a positive-fraction configuration. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, 1 ≤ k ∧
    (k : ℝ) ≤ C * Real.sqrt (n * Real.log n) ∧
    ∀ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)),
      (∀ i j l, ∀ x ∈ T i, ∀ y ∈ T j, ∀ z ∈ T l, x ≠ y → y ≠ z → x ≠ z →
        ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) →
      (∀ g : Fin k → EuclideanSpace ℝ (Fin 2), (∀ i, g i ∈ T i) →
        Function.Injective g ∧ ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a})) →
      (∀ i, (2 : ℝ) ^ ((n : ℝ) + C * Real.sqrt (n * Real.log n)) < (T i).card) →
      ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n ∧ (∀ p ∈ S, ∃ i, p ∈ T i) ∧
        ∀ a ∈ (S : Set (EuclideanSpace ℝ (Fin 2))),
          a ∉ convexHull ℝ ((S : Set (EuclideanSpace ℝ (Fin 2))) \ {a})

theorem cardSet_mono_polygon {m n N : ℕ} (hmn : m ≤ n)
    (hN : N ∈ Erdos107.cardSet n) : N ∈ Erdos107.cardSet m := by
  intro X hX hgp
  obtain ⟨Y, hY, hYX, hconv⟩ := hN X hX hgp
  obtain ⟨Z, hZY, hZ⟩ := Finset.exists_subset_card_eq (hY ▸ hmn)
  have hsub : (Z : Set ℝ²) ⊆ Y := hZY
  refine ⟨Z, hZ, hsub.trans hYX, ?_⟩
  intro z hz hmem
  have hdiff : (Z : Set ℝ²) \ {z} ⊆ (Y : Set ℝ²) \ {z} :=
    fun _ hw => ⟨hsub hw.1, hw.2⟩
  exact hconv z (hsub hz) (convexHull_mono hdiff hmem)

theorem of_eventually_cardSet (r : ℕ → ℝ)
    (hr : r =O[atTop] (fun n : ℕ => Real.sqrt (n * Real.log n)))
    (he : ∀ᶠ n : ℕ in atTop, ∃ N ∈ Erdos107.cardSet n, (N : ℝ) ≤ 2 ^ ((n : ℝ) + r n)) :
    ∃ s : ℕ → ℝ, s =O[atTop] (fun n : ℕ => Real.sqrt (n * Real.log n)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ 2 ^ ((n : ℝ) + s n) := by
  obtain ⟨m, hm⟩ := eventually_atTop.1 he
  obtain ⟨M, hM, _⟩ := hm m le_rfl
  let s (n : ℕ) : ℝ := if m ≤ n then r n else M
  refine ⟨s, ?_, fun n _ => ?_⟩
  · obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.1 hr
    refine Asymptotics.isBigO_iff.2 ⟨c, ?_⟩
    filter_upwards [eventually_ge_atTop m, hc] with n hn hcn
    simpa only [s, if_pos hn] using hcn
  · by_cases hn : m ≤ n
    · obtain ⟨N, hN, hbound⟩ := hm n hn
      have hf : (Erdos107.f n : ℝ) ≤ N := by exact_mod_cast Nat.sInf_le hN
      simpa only [s, if_pos hn] using hf.trans hbound
    · have hf : (Erdos107.f n : ℝ) ≤ M := by
        exact_mod_cast Nat.sInf_le (cardSet_mono_polygon (le_of_not_ge hn) hM)
      have hpow : (M : ℝ) ≤ (2 : ℝ) ^ (M : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast (Nat.lt_two_pow_self (n := M)).le
      have hrpow : (2 : ℝ) ^ (M : ℝ) ≤ 2 ^ ((n : ℝ) + M) := by
        apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
        exact le_add_of_nonneg_left (Nat.cast_nonneg n)
      simpa only [s, if_neg hn] using hf.trans (hpow.trans hrpow)

theorem one_le_scale {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.sqrt (n * Real.log n) := by
  have hcast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlin : (1 / 2 : ℝ) ≤ Real.log 2 := by
    calc
      (1 / 2 : ℝ) = 1 - (2 : ℝ)⁻¹ := by norm_num
      _ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hlog := hlin.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hcast)
  apply Real.le_sqrt_of_sq_le
  calc
    (1 : ℝ) ^ 2 = 2 * (1 / 2) := by norm_num
    _ ≤ (n : ℝ) * Real.log n := mul_le_mul hcast hlog (by norm_num) (by positivity)

theorem main : H1 → H2 → type_of% @Erdos107.variants.hmpt_bound := by
  rintro ⟨A, hPV⟩ ⟨C, hC, hev⟩
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  apply of_eventually_cardSet (fun n => (A * C + C + 1) * Real.sqrt (n * Real.log n))
  · refine Asymptotics.isBigO_iff.2 ⟨A * C + C + 1, Eventually.of_forall fun n => ?_⟩
    rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ A * C + C + 1)]
  · filter_upwards [eventually_ge_atTop (2 : ℕ), hev] with n hn h
    obtain ⟨k, hk1, hkC, hT⟩ := h
    set s := Real.sqrt (n * Real.log n) with hs
    have hs1 : 1 ≤ s := one_le_scale hn
    let a : ℝ := (n : ℝ) + (A * C + C) * s
    let B : ℝ := (2 : ℝ) ^ a
    have hB1 : 1 ≤ B := Real.one_le_rpow (by norm_num) (by positivity)
    refine ⟨⌊B⌋₊ + 1, ?_, ?_⟩
    · intro X hcard hgp
      have hBX : B < (X.card : ℝ) := by
        rw [hcard, Nat.cast_add, Nat.cast_one]
        exact Nat.lt_floor_add_one B
      have hAk : ((A * k : ℕ) : ℝ) ≤ a := by
        push_cast
        have h1 : (A : ℝ) * k ≤ A * (C * s) := mul_le_mul_of_nonneg_left hkC hA
        have h2 : 0 ≤ C * s := by positivity
        have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      have hpowAk : ((2 ^ (A * k) : ℕ) : ℝ) = (2 : ℝ) ^ ((A * k : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast; ring
      have hle : ((2 ^ (A * k) : ℕ) : ℝ) ≤ B := by
        rw [hpowAk]
        exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hAk
      have hcardX : 2 ^ (A * k) ≤ X.card := by
        exact_mod_cast (hle.trans hBX.le)
      have hgp' : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z →
          ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2))) :=
        fun x hx y hy z hz hxy hyz hxz => hgp hx hy hz hxy hyz hxz
      obtain ⟨T, hTX, hTcard, htrans⟩ := hPV k hk1 X hgp' hcardX
      have hbig : ∀ i, (2 : ℝ) ^ ((n : ℝ) + C * s) < (T i).card := by
        intro i
        have hc : (X.card : ℝ) ≤ ((2 ^ (A * k) : ℕ) : ℝ) * (T i).card := by
          exact_mod_cast hTcard i
        rw [hpowAk] at hc
        have hsplit : B = (2 : ℝ) ^ ((A * k : ℕ) : ℝ) * (2 : ℝ) ^ (a - ((A * k : ℕ) : ℝ)) := by
          show (2 : ℝ) ^ a = _
          rw [← Real.rpow_add (by norm_num)]; congr 1; ring
        have hmono : (2 : ℝ) ^ ((n : ℝ) + C * s) ≤ (2 : ℝ) ^ (a - ((A * k : ℕ) : ℝ)) := by
          apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
          have h1 : (A : ℝ) * k ≤ A * (C * s) := mul_le_mul_of_nonneg_left hkC hA
          push_cast
          dsimp only [a]
          nlinarith
        have hpos : (0 : ℝ) < (2 : ℝ) ^ ((A * k : ℕ) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
        have hlt : (2 : ℝ) ^ ((A * k : ℕ) : ℝ) * (2 : ℝ) ^ (a - ((A * k : ℕ) : ℝ)) <
            (2 : ℝ) ^ ((A * k : ℕ) : ℝ) * (T i).card := by
          rw [← hsplit]; exact hBX.trans_le hc
        exact hmono.trans_lt (lt_of_mul_lt_mul_left hlt hpos.le)
      have hgpT : ∀ i j l, ∀ x ∈ T i, ∀ y ∈ T j, ∀ z ∈ T l, x ≠ y → y ≠ z → x ≠ z →
          ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2))) :=
        fun i j l x hx y hy z hz => hgp' x (hTX i hx) y (hTX j hy) z (hTX l hz)
      obtain ⟨S, hSn, hSX, hSconv⟩ := hT T hgpT htrans hbig
      refine ⟨S, hSn, fun p hp => ?_, hSconv⟩
      obtain ⟨i, hi⟩ := hSX p hp
      exact hTX i hi
    · rw [Nat.cast_add, Nat.cast_one]
      calc
        (⌊B⌋₊ : ℝ) + 1 ≤ B + 1 := by
          have := Nat.floor_le (show 0 ≤ B from zero_le_one.trans hB1); linarith
        _ ≤ B * 2 := by linarith
        _ = (2 : ℝ) ^ (a + 1) := by rw [Real.rpow_add (by norm_num) a 1, Real.rpow_one]
        _ ≤ 2 ^ ((n : ℝ) + (A * C + C + 1) * s) := by
          apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
          dsimp only [a]
          nlinarith

end OMA.R_Erdos107_variants_hmpt_bound_R1
