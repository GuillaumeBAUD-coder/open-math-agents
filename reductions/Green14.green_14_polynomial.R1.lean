import FormalConjectures.GreensOpenProblems.«14»
import Mathlib.Combinatorics.HalesJewett

/-!
Reduction `Green14.green_14_polynomial.R1` of Ben Green's Open Problem 14 (`green_14_polynomial`).
Credit: @skhakim.

Follows Zach Hunter's elementary proof of a superpolynomial lower bound for `W(3, r)`
(arXiv:2111.01099, *Improved lower bounds for van der Waerden numbers*) with exact integer
dimensions `D = 200 * t`. This file proves completely:
- Van der Waerden's theorem (`mixedMonoAPGuaranteeSet_nonempty`) via Hales--Jewett,
- Monotonicity `W(4, X) ≥ N + 1` from a 2-coloring of `[1, N]` avoiding blue 3-APs and red `X`-APs,
- Blue 3-AP-freeness for every choice of radii via the parallelogram law (Hunter Prop. 3.2),
- Existence of radii avoiding all red `X`-APs by exact finite counting (Hunter Prop. 5.2),
- The superpolynomial asymptotic contradiction with `W(4, r) = O(r^d)`.

The three independent analytic/combinatorial pillars of Hunter's paper are isolated as steps:
- `H1`: Existence of well-distributed centers on `T^D` (Hunter Prop. 2.1 + Mahler's short basis),
- `H2`: Existence of a good Diophantine rotation on `T^D` (Hunter Prop. 3.2 + Prop. 4.2),
- `H3`: Fourier hitting lemma for long arithmetic progressions (Hunter Prop. 5.1 + Appendix B).
-/

namespace OMA.R_Green14_green_14_polynomial_R1

open Filter Set Green14

def H1 : Prop :=
  ∃ t₀ : ℕ, ∀ t ≥ t₀,
    let D := 200 * t
    let ρ : ℝ := ((D : ℝ) ^ 4)⁻¹
    let M := D ^ (208 * t)
    let Y := D ^ (8 * t)
    ∃ x : Fin M → Fin D → ℝ,
      (∀ i₁ i₂ i₃ : Fin M, ¬ (i₁ = i₂ ∧ i₂ = i₃) →
        ∃ b : Fin D, 10 * ρ < |x i₁ b - 2 * x i₂ b + x i₃ b -
          (round (x i₁ b - 2 * x i₂ b + x i₃ b) : ℝ)|) ∧
      (∀ (S : Set (Fin D → ℤ)),
        Module.finrank ℚ (Submodule.span ℚ ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) '' S)) ≤ 2 * t →
        ∀ xstar : Fin D → ℝ,
        ∃ (j : Fin Y → Fin M) (u : Fin Y → Fin D → ℝ),
          Function.Injective j ∧
          (∀ k : Fin Y, ∑ b : Fin D, (u k b) ^ 2 < (ρ / 10) ^ 2) ∧
          (∀ k : Fin Y, ∀ ξ ∈ S, (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) →
            |(∑ b : Fin D, (ξ b : ℝ) * (x (j k) b + u k b - xstar b)) -
              (round (∑ b : Fin D, (ξ b : ℝ) * (x (j k) b + u k b - xstar b)) : ℝ)| < 1 / 100))

def H2 : Prop :=
  ∃ t₀ : ℕ, ∀ t ≥ t₀,
    let D := 200 * t
    let N := D ^ (200 * t ^ 2)
    let X := D ^ (10000 * t)
    ∃ θ : Fin D → ℝ,
      (∀ d : ℕ, 1 ≤ d → d ≤ N →
        ∃ b : Fin D, (2 * (D : ℝ) ^ (2 * t))⁻¹ <
          |(d : ℝ) * θ b - (round ((d : ℝ) * θ b) : ℝ)|) ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ N →
        Module.finrank ℚ (Submodule.span ℚ
          ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) ''
            {ξ : Fin D → ℤ | (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) ∧
              |(d : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b) -
                (round ((d : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b)) : ℝ)| ≤
                (D : ℝ) ^ (8 * D) / (X : ℝ)})) ≤ 2 * t)

def H3 : Prop :=
  ∃ t₀ : ℕ, ∀ t ≥ t₀,
    let D := 200 * t
    let ρ : ℝ := ((D : ℝ) ^ 4)⁻¹
    let X := D ^ (10000 * t)
    ∀ (α x0 y u : Fin D → ℝ),
      (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
      (∀ ξ : Fin D → ℤ, (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) →
        |(∑ b : Fin D, (ξ b : ℝ) * α b) - (round (∑ b : Fin D, (ξ b : ℝ) * α b) : ℝ)| ≤
          (D : ℝ) ^ (8 * D) / (X : ℝ) →
        |(∑ b : Fin D, (ξ b : ℝ) * (y b + u b - x0 b)) -
          (round (∑ b : Fin D, (ξ b : ℝ) * (y b + u b - x0 b)) : ℝ)| < 1 / 100) →
      ∃ s : ℤ, |s| ≤ (X : ℤ) / 5 ∧
        ∑ b : Fin D, ((x0 b + (s : ℝ) * α b - y b) -
          (round (x0 b + (s : ℝ) * α b - y b) : ℝ)) ^ 2 < (ρ / 5) ^ 2

section Helpers

open scoped Classical

private lemma mixedMonoAPGuaranteeSet_nonempty (k r : ℕ) (_hk : 1 ≤ k) (_hr : 1 ≤ r) :
    (mixedMonoAPGuaranteeSet k r).Nonempty := by
  let m := max k r
  obtain ⟨ι, instι, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin m) (Fin 2)
  let _ : Fintype ι := instι
  let N := Fintype.card ι * (m - 1) + 1
  have word_sum_le (v : ι → Fin m) : ∑ i, (v i : ℕ) ≤ Fintype.card ι * (m - 1) := by
    calc ∑ i, (v i : ℕ) ≤ ∑ _i : ι, (m - 1) :=
          Finset.sum_le_sum fun i _ => Nat.le_pred_of_lt (v i).isLt
      _ = Fintype.card ι * (m - 1) := by simp
  refine ⟨N, fun coloring => ?_⟩
  let wordPoint (v : ι → Fin m) : Icc 1 N :=
    ⟨1 + ∑ i, (v i : ℕ), ⟨by omega, by dsimp only [N]; have := word_sum_le v; omega⟩⟩
  obtain ⟨line, color, hmono⟩ := hι (fun v => coloring (wordPoint v))
  set active : Finset ι := {i | line.idxFun i = none} with hactive
  let a : ℕ := active.card
  let b : ℕ := ∑ i ∈ activeᶜ, ((line.idxFun i).map fun x : Fin m => (x : ℕ)).getD 0
  have ha : 0 < a := by
    apply Finset.card_pos.mpr
    refine ⟨line.proper.choose, ?_⟩
    rw [hactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, line.proper.choose_spec⟩
  have line_sum (x : Fin m) : ∑ i, ((line x i : Fin m) : ℕ) = a * (x : ℕ) + b := by
    rw [← Finset.sum_add_sum_compl active]
    congr 1
    · calc ∑ i ∈ active, ((line x i : Fin m) : ℕ)
          = ∑ _i ∈ active, (x : ℕ) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hnone : line.idxFun i = none := by
              rw [hactive, Finset.mem_filter] at hi
              exact hi.2
            simp [Combinatorics.Line.coe_apply, hnone]
        _ = a * (x : ℕ) := by simp [a]
    · refine Finset.sum_congr rfl fun i hi => ?_
      cases hopt : line.idxFun i with
      | none =>
        have himem : i ∈ active := by
          rw [hactive, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hopt⟩
        exact ((Finset.mem_compl.mp hi) himem).elim
      | some y => simp [Combinatorics.Line.coe_apply, hopt]
  have build_progression (q : ℕ) (hqm : q ≤ m) :
      ∃ s : Finset (Icc 1 N), ({(z : ℕ) | z ∈ s}).IsAPOfLength q ∧ ∀ z ∈ s, coloring z = color := by
    let liftFin : Fin q → Fin m := fun x => Fin.castLE hqm x
    let value : Fin q → ℕ := fun x => a * (x : ℕ) + b + 1
    have hvalue_inj : Function.Injective value := by
      intro x y hxy
      apply Fin.ext
      dsimp only [value] at hxy
      exact Nat.eq_of_mul_eq_mul_left ha (by omega)
    let point : Fin q → Icc 1 N := fun x =>
      ⟨value x, ⟨by dsimp only [value]; omega, by
        have hp := (wordPoint (line (liftFin x))).property.2
        dsimp only [wordPoint] at hp
        rw [line_sum] at hp
        simpa [liftFin, value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩⟩
    have hpoint_inj : Function.Injective point := fun x y hxy =>
      hvalue_inj (Subtype.ext_iff.mp hxy)
    let emb : Fin q ↪ Icc 1 N := ⟨point, hpoint_inj⟩
    let s : Finset (Icc 1 N) := Finset.univ.map emb
    let T : Set ℕ := Set.range value
    have hT : T.IsAPOfLengthWith q (b + 1) a := by
      constructor
      · rw [_root_.ENat.card_coe_set_eq]
        have hTrange : T = value '' Set.univ := by ext z; simp [T]
        rw [hTrange, hvalue_inj.encard_image]
        simp
      · ext z
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨x, by exact_mod_cast x.isLt, ?_⟩
          simp [value, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
        · rintro ⟨n, hn, rfl⟩
          have hnq : n < q := by exact_mod_cast hn
          refine ⟨⟨n, hnq⟩, ?_⟩
          change a * n + b + 1 = b + 1 + n * a
          rw [Nat.mul_comm n a]; omega
    have hsT : ({(z : ℕ) | z ∈ s} : Set ℕ) = T := by ext z; simp [s, emb, point, T, value]
    refine ⟨s, by rw [hsT]; exact ⟨b + 1, a, hT⟩, fun z hz => ?_⟩
    rcases Finset.mem_map.mp hz with ⟨x, -, rfl⟩
    have hpoint_word : point x = wordPoint (line (liftFin x)) := by
      apply Subtype.ext
      dsimp only [point, value, wordPoint]
      rw [line_sum]
      simp [liftFin, Nat.add_comm]
    change coloring (point x) = color
    rw [hpoint_word]
    exact hmono (liftFin x)
  fin_cases color
  · exact Or.inl (build_progression k (le_max_left k r))
  · exact Or.inr (build_progression r (le_max_right k r))

private lemma mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) : N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x => ⟨x, x.2.1, x.2.2.trans hMN⟩, fun x y h =>
      Subtype.ext (congrArg (fun z : Icc 1 N => (z : ℕ)) h)⟩
  rcases hM (fun x => coloring (emb x)) with ⟨s, hsAP, hsC⟩ | ⟨s, hsAP, hsC⟩
  · left
    refine ⟨s.map emb, ?_, fun x hx => ?_⟩
    · have hsets : ({(x : ℕ) | x ∈ s.map emb} : Set ℕ) = {(x : ℕ) | x ∈ s} := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
          exact ⟨y, hy, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨emb y, Finset.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
      rwa [hsets]
    · rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact hsC y hy
  · right
    refine ⟨s.map emb, ?_, fun x hx => ?_⟩
    · have hsets : ({(x : ℕ) | x ∈ s.map emb} : Set ℕ) = {(x : ℕ) | x ∈ s} := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
          exact ⟨y, hy, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨emb y, Finset.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
      rwa [hsets]
    · rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact hsC y hy

private lemma W_ge_succ_of_not_mem (k r N : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hbad : N ∉ mixedMonoAPGuaranteeSet k r) : N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf (mixedMonoAPGuaranteeSet_nonempty k r hk hr)
  intro b hb
  by_contra hle
  exact hbad (mixedMonoAPGuaranteeSet_upward k r (by omega) hb)

private lemma isAPOfLength_extract {N k : ℕ} (hk : 2 ≤ k) {s : Finset (Icc 1 N)}
    (hAP : ({(x : ℕ) | x ∈ s} : Set ℕ).IsAPOfLength k) :
    ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
      ∀ i < k, ∃ x ∈ s, (x : ℕ) = a + i * d := by
  rcases hAP with ⟨a, d, hWith⟩
  let T : Set ℕ := {(x : ℕ) | x ∈ s}
  have hT : T.IsAPOfLengthWith k a d := hWith
  have term_mem : ∀ i < k, a + i * d ∈ T := by
    intro i hi
    rw [hT.2]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have hmem_iff : ∀ z, z ∈ T ↔ ∃ x ∈ s, (x : ℕ) = z := fun _ => Iff.rfl
  obtain ⟨x0, hx0s, hx0⟩ := (hmem_iff a).mp (by simpa using term_mem 0 (by omega))
  obtain ⟨xl, hxls, hxl⟩ := (hmem_iff _).mp (term_mem (k - 1) (by omega))
  have hdpos : 1 ≤ d := by
    by_contra h0
    have hd0 : d = 0 := by omega
    have hTsub : T ⊆ {a} := by
      intro z hz
      rw [hT.2] at hz
      rcases hz with ⟨i, _, rfl⟩
      simp [hd0]
    have hcard : T.encard ≤ 1 := by
      calc T.encard ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hTsub
        _ = 1 := Set.encard_singleton a
    have hcard_eq : T.encard = (k : ℕ∞) := by
      rw [← _root_.ENat.card_coe_set_eq]
      exact hT.1
    rw [hcard_eq] at hcard
    have hk1 : k ≤ 1 := by exact_mod_cast hcard
    omega
  refine ⟨a, d, by simpa [hx0] using x0.2.1, hdpos, by simpa [hxl] using xl.2.2, ?_⟩
  intro i hi
  exact (hmem_iff _).mp (term_mem i hi)

private lemma dist_round_le_of_int_diff (x y : ℝ) (h : ∃ m : ℤ, x - y = m) :
    |x - (round x : ℝ)| ≤ |y| := by
  obtain ⟨m, hm⟩ := h
  have hxy : y = x - (m : ℝ) := by linarith
  rw [hxy]
  by_cases heq : round x = m
  · rw [heq]
  · have hdiff : (1 : ℝ) ≤ |(round x : ℝ) - (m : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |round x - m| := by
        rw [le_abs]; omega
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|round x - m| : ℤ) : ℝ) := by exact_mod_cast h1
      simpa using h2
    have hhalf : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    have htri : |(round x : ℝ) - (m : ℝ)| ≤ |x - (round x : ℝ)| + |x - (m : ℝ)| := by
      have hsub : (round x : ℝ) - (m : ℝ) = ((round x : ℝ) - x) + (x - (m : ℝ)) := by ring
      rw [hsub]
      calc |((round x : ℝ) - x) + (x - (m : ℝ))|
          ≤ |(round x : ℝ) - x| + |x - (m : ℝ)| := abs_add_le _ _
        _ = |x - (round x : ℝ)| + |x - (m : ℝ)| := by rw [abs_sub_comm]
    linarith

private lemma int_eq_zero_of_abs_lt_half (m : ℤ) (h : |(m : ℝ)| < 1 / 2) : m = 0 := by
  have h1 : (|(m : ℤ)| : ℝ) < 1 / 2 := by simpa using h
  have h2 : |(m : ℤ)| < 1 := by
    by_contra hge
    push Not at hge
    have : (1 : ℝ) ≤ (|(m : ℤ)| : ℝ) := by exact_mod_cast hge
    linarith
  rw [abs_lt] at h2
  omega

private lemma pow_ge_two_mul_pred_pow (K : ℕ) (hK : 1 ≤ K) :
    2 * (K - 1) ^ K ≤ K ^ K := by
  have hKeq : (K - 1) + 1 = K := by omega
  have hexp : K ^ K = ∑ m ∈ Finset.range (K + 1), (K - 1) ^ m * 1 ^ (K - m) * K.choose m := by
    conv_lhs => rw [← hKeq]
    rw [add_pow]
    simp only [hKeq, Nat.cast_id]
  have hKmem : K ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have hKm1mem : K - 1 ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have hKne : K ≠ K - 1 := by omega
  have hsub2 : ({K, K - 1} : Finset ℕ) ⊆ Finset.range (K + 1) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hsum2 := Finset.sum_le_sum_of_subset (f := fun m => (K - 1) ^ m * 1 ^ (K - m) * K.choose m) hsub2
  rw [Finset.sum_pair hKne] at hsum2
  simp only [one_pow, mul_one, Nat.choose_self] at hsum2
  have hchoose : K.choose (K - 1) = K := by
    have := Nat.choose_symm (by omega : K - 1 ≤ K)
    rw [show K - (K - 1) = 1 by omega, Nat.choose_one_right] at this
    exact this.symm
  rw [hchoose] at hsum2
  have hterm : (K - 1) ^ K ≤ (K - 1) ^ (K - 1) * K := by
    conv_lhs => rw [show K = (K - 1) + 1 by omega, pow_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  rw [hexp]
  have hsum_eq : (∑ m ∈ Finset.range (K + 1), (K - 1) ^ m * 1 ^ (K - m) * K.choose m) =
      ∑ m ∈ Finset.range (K + 1), (K - 1) ^ m * K.choose m := by
    refine Finset.sum_congr rfl fun m _ => by simp
  rw [hsum_eq]
  omega

private lemma card_avoiding_funs {M Y K : ℕ} (j : Fin Y → Fin M) (hj : Function.Injective j)
    (r : Fin Y → Fin K) :
    (Finset.univ.filter (fun e : Fin M → Fin K => ∀ k : Fin Y, e (j k) ≠ r k)).card =
      (K - 1) ^ Y * K ^ (M - Y) := by
  let S : Finset (Fin M) := Finset.univ.image j
  have hScard : S.card = Y := by
    rw [Finset.card_image_of_injective _ hj]; simp
  have hScompl : Sᶜ.card = M - Y := by
    have htot := Finset.card_add_card_compl S
    rw [Fintype.card_fin, hScard] at htot
    omega
  let allowed : Fin M → Finset (Fin K) := fun i =>
    if h : ∃ k : Fin Y, j k = i then Finset.univ.erase (r h.choose) else Finset.univ
  have hfilt : Finset.univ.filter (fun e : Fin M → Fin K => ∀ k : Fin Y, e (j k) ≠ r k) =
      Fintype.piFinset allowed := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro he i
      dsimp only [allowed]
      split_ifs with h
      · rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        have h1 := he h.choose
        rwa [h.choose_spec] at h1
      · exact Finset.mem_univ _
    · intro he k
      have hi := he (j k)
      dsimp only [allowed] at hi
      have hex : ∃ k' : Fin Y, j k' = j k := ⟨k, rfl⟩
      rw [dif_pos hex, Finset.mem_erase] at hi
      have hch : hex.choose = k := hj hex.choose_spec
      rw [hch] at hi
      exact hi.1
  rw [hfilt, Fintype.card_piFinset, ← Finset.prod_mul_prod_compl S]
  have hprodS : ∏ i ∈ S, (allowed i).card = (K - 1) ^ Y := by
    have hpt : ∀ i ∈ S, (allowed i).card = K - 1 := by
      intro i hi
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      dsimp only [allowed]
      have hex : ∃ k' : Fin Y, j k' = j k := ⟨k, rfl⟩
      rw [dif_pos hex, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    rw [Finset.prod_congr rfl hpt, Finset.prod_const, hScard]
  have hprodSc : ∏ i ∈ Sᶜ, (allowed i).card = K ^ (M - Y) := by
    have hpt : ∀ i ∈ Sᶜ, (allowed i).card = K := by
      intro i hi
      have hni : ¬ ∃ k : Fin Y, j k = i := by
        rintro ⟨k, rfl⟩
        exact (Finset.mem_compl.mp hi) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
      dsimp only [allowed]
      rw [dif_neg hni, Finset.card_fin]
    rw [Finset.prod_congr rfl hpt, Finset.prod_const, hScompl]
  rw [hprodS, hprodSc]

end Helpers

set_option maxHeartbeats 4000000 in
theorem main : H1 → H2 → H3 → type_of% @Green14.green_14_polynomial := by
  intro h1 h2 h3 hpoly
  obtain ⟨d, hd⟩ := hpoly 4 (le_refl 4)
  rw [Asymptotics.isBigO_iff] at hd
  obtain ⟨C₀, hC₀⟩ := hd
  rw [Filter.eventually_atTop] at hC₀
  obtain ⟨r₀, hr₀⟩ := hC₀
  let C : ℝ := max C₀ 1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
  have hW_bound : ∀ r ≥ r₀, (W 4 r : ℝ) ≤ C * (r : ℝ) ^ d := by
    intro r hr
    have h := hr₀ r hr
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (by positivity))
  obtain ⟨t₁, ht₁⟩ := h1
  obtain ⟨t₂, ht₂⟩ := h2
  obtain ⟨t₃, ht₃⟩ := h3
  let t : ℕ := max t₁ (max t₂ (max t₃ (max 2 (max (50 * d + 2) (max r₀ (Nat.ceil C + 1))))))
  have ht_t1 : t ≥ t₁ := le_max_left _ _
  have ht_t2 : t ≥ t₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have ht_t3 : t ≥ t₃ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have ht2 : t ≥ 2 := by omega
  have ht_d : t ≥ 50 * d + 2 := by omega
  have ht_r0 : t ≥ r₀ := by omega
  have ht_C : C < (t : ℝ) := by
    have h1 : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
    have h2 : Nat.ceil C + 1 ≤ t := by omega
    have h3 : (Nat.ceil C : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast h2
    linarith
  let D : ℕ := 200 * t
  let ρ : ℝ := ((D : ℝ) ^ 4)⁻¹
  let M : ℕ := D ^ (208 * t)
  let Y : ℕ := D ^ (8 * t)
  let N : ℕ := D ^ (200 * t ^ 2)
  let X : ℕ := D ^ (10000 * t)
  let K : ℕ := D ^ (4 * t - 4)
  let δ : ℝ := ((D : ℝ) ^ (4 * t))⁻¹
  have hD_ge : 400 ≤ D := by dsimp only [D]; omega
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hρ_pos : 0 < ρ := inv_pos.mpr (pow_pos hD_pos 4)
  have hδ_pos : 0 < δ := inv_pos.mpr (pow_pos hD_pos (4 * t))
  have hK_ge : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  have hK_mul_δ : (K : ℝ) * δ = ρ := by
    dsimp only [K, δ, ρ]
    rw [Nat.cast_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hD_pos.ne')]
    rw [inv_mul_eq_div, eq_div_iff (pow_ne_zero _ hD_pos.ne'), ← pow_add]
    congr 1; omega
  have hρ_lt : ρ < 1 / 12 := by
    dsimp only [ρ]
    rw [inv_lt_comm₀ (pow_pos hD_pos 4) (by norm_num)]
    have hD4 : (400 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
    nlinarith [sq_nonneg ((D : ℝ) - 400), pow_pos hD_pos 2]
  -- Extract well-distributed centers x and Diophantine rotation θ
  obtain ⟨x, hx1, hx2⟩ := ht₁ t ht_t1
  obtain ⟨θ, hθ1, hθ2⟩ := ht₂ t ht_t2
  have hH3 := ht₃ t ht_t3
  -- Define coloring for each e : Fin M → Fin K
  let isBlue (e : Fin M → Fin K) (n : ℕ) : Prop :=
    ∃ i : Fin M,
      (((e i : ℕ) : ℝ) * δ) ^ 2 ≤
        ∑ b : Fin D, ((n : ℝ) * θ b - x i b - (round ((n : ℝ) * θ b - x i b) : ℝ)) ^ 2 ∧
      ∑ b : Fin D, ((n : ℝ) * θ b - x i b - (round ((n : ℝ) * θ b - x i b) : ℝ)) ^ 2 <
        ((((e i : ℕ) + 1 : ℕ) : ℝ) * δ) ^ 2
  -- Step 1: No blue 3-AP for ANY e : Fin M → Fin K (Hunter Prop. 3.2)
  have no_blue_3AP : ∀ (e : Fin M → Fin K) (a d_ap : ℕ),
      1 ≤ a → 1 ≤ d_ap → a + 2 * d_ap ≤ N →
      ¬ (isBlue e a ∧ isBlue e (a + d_ap) ∧ isBlue e (a + 2 * d_ap)) := by
    intro e a d_ap ha hd_pos hend ⟨hb0, hb1, hb2⟩
    obtain ⟨i0, h0lo, h0hi⟩ := hb0
    obtain ⟨i1, h1lo, h1hi⟩ := hb1
    obtain ⟨i2, h2lo, h2hi⟩ := hb2
    let r0 : Fin D → ℝ := fun b => (a : ℝ) * θ b - x i0 b - (round ((a : ℝ) * θ b - x i0 b) : ℝ)
    let r1 : Fin D → ℝ := fun b => ((a + d_ap : ℕ) : ℝ) * θ b - x i1 b -
      (round (((a + d_ap : ℕ) : ℝ) * θ b - x i1 b) : ℝ)
    let r2 : Fin D → ℝ := fun b => ((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i2 b -
      (round (((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i2 b) : ℝ)
    have hbound_rad : ∀ (i : Fin M), ((((e i : ℕ) + 1 : ℕ) : ℝ) * δ) ≤ ρ := by
      intro i
      have hle : ((e i : ℕ) + 1 : ℕ) ≤ K := (e i).isLt
      have hleR : (((e i : ℕ) + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hle
      calc (((e i : ℕ) + 1 : ℕ) : ℝ) * δ ≤ (K : ℝ) * δ :=
            mul_le_mul_of_nonneg_right hleR hδ_pos.le
        _ = ρ := hK_mul_δ
    have hr0_sq : ∑ b : Fin D, (r0 b) ^ 2 < ρ ^ 2 :=
      lt_of_lt_of_le h0hi (pow_le_pow_left₀ (by positivity) (hbound_rad i0) 2)
    have hr1_sq : ∑ b : Fin D, (r1 b) ^ 2 < ρ ^ 2 :=
      lt_of_lt_of_le h1hi (pow_le_pow_left₀ (by positivity) (hbound_rad i1) 2)
    have hr2_sq : ∑ b : Fin D, (r2 b) ^ 2 < ρ ^ 2 :=
      lt_of_lt_of_le h2hi (pow_le_pow_left₀ (by positivity) (hbound_rad i2) 2)
    have coord_lt_ρ : ∀ (f : Fin D → ℝ), ∑ b : Fin D, (f b) ^ 2 < ρ ^ 2 →
        ∀ b : Fin D, |f b| < ρ := by
      intro f hf b
      have hsq : (f b) ^ 2 < ρ ^ 2 :=
        lt_of_le_of_lt (Finset.single_le_sum (fun j _ => sq_nonneg (f j)) (Finset.mem_univ b)) hf
      nlinarith [sq_abs (f b), abs_nonneg (f b)]
    have hr0_lt := coord_lt_ρ r0 hr0_sq
    have hr1_lt := coord_lt_ρ r1 hr1_sq
    have hr2_lt := coord_lt_ρ r2 hr2_sq
    -- Show i0 = i1 = i2 using H1 condition 1
    have hi_eq : i0 = i1 ∧ i1 = i2 := by
      by_contra hne
      obtain ⟨b, hb⟩ := hx1 i0 i1 i2 hne
      have hint : ∃ m : ℤ, (x i0 b - 2 * x i1 b + x i2 b) - (-r0 b + 2 * r1 b - r2 b) = m := by
        refine ⟨-(round ((a : ℝ) * θ b - x i0 b)) +
          2 * round (((a + d_ap : ℕ) : ℝ) * θ b - x i1 b) -
          round (((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i2 b), ?_⟩
        dsimp only [r0, r1, r2]
        push_cast
        ring
      have hle := dist_round_le_of_int_diff _ _ hint
      have htri : |-r0 b + 2 * r1 b - r2 b| < 4 * ρ := by
        have h0 := abs_lt.mp (hr0_lt b)
        have h1 := abs_lt.mp (hr1_lt b)
        have h2 := abs_lt.mp (hr2_lt b)
        rw [abs_lt]
        constructor <;> linarith
      linarith
    obtain ⟨rfl, rfl⟩ := hi_eq
    -- Now i0 = i1 = i2; let v b = r1 b - r0 b and show r2 b = r0 b + 2 * v b
    let v : Fin D → ℝ := fun b => r1 b - r0 b
    have hr2_eq : ∀ b : Fin D, r2 b = r0 b + 2 * v b := by
      intro b
      let m : ℤ := round ((a : ℝ) * θ b - x i0 b) -
        2 * round (((a + d_ap : ℕ) : ℝ) * θ b - x i0 b) +
        round (((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i0 b)
      have hdiff : r2 b - (r0 b + 2 * v b) = -(m : ℝ) := by
        dsimp only [v, r0, r1, r2, m]
        push_cast
        ring
      have hlt : |(m : ℝ)| < 1 / 2 := by
        have h0 := abs_lt.mp (hr0_lt b)
        have h1 := abs_lt.mp (hr1_lt b)
        have h2 := abs_lt.mp (hr2_lt b)
        have habs : |r2 b - (r0 b + 2 * v b)| < 4 * ρ := by
          have : r2 b - (r0 b + 2 * v b) = r2 b - 2 * r1 b + r0 b := by dsimp only [v]; ring
          rw [this, abs_lt]
          constructor <;> linarith
        rw [hdiff, abs_neg] at habs
        linarith
      have hm0 : m = 0 := int_eq_zero_of_abs_lt_half m hlt
      rw [hm0] at hdiff
      simp at hdiff
      linarith
    -- Parallelogram law!
    have hpara : 2 * ∑ b : Fin D, (v b) ^ 2 =
        ∑ b : Fin D, (r0 b) ^ 2 + ∑ b : Fin D, (r2 b) ^ 2 - 2 * ∑ b : Fin D, (r1 b) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hr2_eq b]
      have : r1 b = r0 b + v b := by dsimp only [v]; ring
      rw [this]
      ring
    have hv_sq : ∑ b : Fin D, (v b) ^ 2 < ((2 * (D : ℝ) ^ (2 * t))⁻¹) ^ 2 := by
      let k : ℕ := (e i0 : ℕ)
      have hk_lt : k < K := (e i0).isLt
      have h1 : 2 * ∑ b : Fin D, (v b) ^ 2 <
          2 * ((((k + 1 : ℕ) : ℝ) * δ) ^ 2 - ((k : ℝ) * δ) ^ 2) := by
        linarith [h0hi, h2hi, h1lo]
      have h2 : ((((k + 1 : ℕ) : ℝ) * δ) ^ 2 - ((k : ℝ) * δ) ^ 2) =
          (2 * (k : ℝ) + 1) * δ ^ 2 := by push_cast; ring
      have h3 : (2 * (k : ℝ) + 1) ≤ 2 * (K : ℝ) := by
        have : 2 * k + 1 ≤ 2 * K := by omega
        exact_mod_cast this
      have h4 : (2 * (k : ℝ) + 1) * δ ^ 2 ≤ 2 * ρ * δ := by
        calc (2 * (k : ℝ) + 1) * δ ^ 2 ≤ (2 * (K : ℝ)) * δ ^ 2 :=
              mul_le_mul_of_nonneg_right h3 (sq_nonneg δ)
          _ = 2 * ((K : ℝ) * δ) * δ := by ring
          _ = 2 * ρ * δ := by rw [hK_mul_δ]
      have h5 : 2 * ρ * δ < (1 / 4) * δ := by nlinarith
      have h6 : (1 / 4 : ℝ) * δ = ((2 * (D : ℝ) ^ (2 * t))⁻¹) ^ 2 := by
        dsimp only [δ]
        rw [inv_pow, mul_pow, ← pow_mul, show 2 * t * 2 = 4 * t by omega]
        ring
      linarith
    -- Contradict H2 condition 1 at d_ap
    have hd_le_N : d_ap ≤ N := by omega
    obtain ⟨b, hb⟩ := hθ1 d_ap hd_pos hd_le_N
    have hint_v : ∃ m : ℤ, (d_ap : ℝ) * θ b - v b = m := by
      refine ⟨round (((a + d_ap : ℕ) : ℝ) * θ b - x i0 b) - round ((a : ℝ) * θ b - x i0 b), ?_⟩
      dsimp only [v, r1, r0]
      push_cast
      ring
    have hdist_le := dist_round_le_of_int_diff _ _ hint_v
    have hvb_sq : (v b) ^ 2 < ((2 * (D : ℝ) ^ (2 * t))⁻¹) ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ b)) hv_sq
    have hpos_rhs : (0 : ℝ) < (2 * (D : ℝ) ^ (2 * t))⁻¹ := by positivity
    have hvb_lt : |v b| < (2 * (D : ℝ) ^ (2 * t))⁻¹ := by
      nlinarith [sq_abs (v b), abs_nonneg (v b)]
    linarith
  -- Step 2: By finite counting on Fin M → Fin K, find e with no red X-AP (Hunter Prop. 5.2)
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let badFor (p : ℕ × ℕ) : Finset (Fin M → Fin K) :=
    Finset.univ.filter (fun e =>
      p.1 + (X - 1) * p.2 ≤ N ∧ ∀ m < X, ¬ isBlue e (p.1 + m * p.2))
  have hbad_card : ∀ p ∈ pairs, (badFor p).card ≤ (K - 1) ^ Y * K ^ (M - Y) := by
    intro p hp
    by_cases hvalid : p.1 + (X - 1) * p.2 ≤ N
    · have hp1 : 1 ≤ p.1 ∧ p.1 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
      have hp2 : 1 ≤ p.2 ∧ p.2 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
      let a := p.1
      let d_ap := p.2
      let n1 : ℕ := a + (X / 2) * d_ap
      let Λ : Set (Fin D → ℤ) :=
        {ξ : Fin D → ℤ | (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) ∧
          |(d_ap : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b) -
            (round ((d_ap : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b)) : ℝ)| ≤
            (D : ℝ) ^ (8 * D) / (X : ℝ)}
      have hdim := hθ2 d_ap hp2.1 hp2.2
      obtain ⟨j, u, hj_inj, hu_norm, hu_close⟩ :=
        hx2 Λ hdim (fun b => (n1 : ℝ) * θ b)
      -- For each k : Fin Y, apply H3 to get an AP element hitting B_{ρ/5}(x (j k))
      have hhit : ∀ k : Fin Y, ∃ (m : ℕ) (rk : Fin K), m < X ∧
          ∀ e : Fin M → Fin K, e (j k) = rk → isBlue e (a + m * d_ap) := by
        intro k
        have hclose_k : ∀ ξ : Fin D → ℤ, (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) →
            |(∑ b : Fin D, (ξ b : ℝ) * ((d_ap : ℝ) * θ b)) -
              (round (∑ b : Fin D, (ξ b : ℝ) * ((d_ap : ℝ) * θ b)) : ℝ)| ≤
              (D : ℝ) ^ (8 * D) / (X : ℝ) →
            |(∑ b : Fin D, (ξ b : ℝ) * (x (j k) b + u k b - (n1 : ℝ) * θ b)) -
              (round (∑ b : Fin D, (ξ b : ℝ) * (x (j k) b + u k b - (n1 : ℝ) * θ b)) : ℝ)| < 1 / 100 := by
          intro ξ hξ_bd hξ_small
          have hsum_eq : ∑ b : Fin D, (ξ b : ℝ) * ((d_ap : ℝ) * θ b) =
              (d_ap : ℝ) * ∑ b : Fin D, (ξ b : ℝ) * θ b := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
          rw [hsum_eq] at hξ_small
          exact hu_close k ξ ⟨hξ_bd, hξ_small⟩ hξ_bd
        obtain ⟨s, hs_abs, hs_hit⟩ :=
          hH3 (fun b => (d_ap : ℝ) * θ b) (fun b => (n1 : ℝ) * θ b) (x (j k)) (u k)
            (hu_norm k) hclose_k
        have hs_abs' : |s| ≤ (X : ℤ) / 5 := hs_abs
        have hX5 : 5 ≤ X := by
          dsimp only [X]
          calc 5 ≤ 400 := by omega
            _ ≤ D := hD_ge
            _ = D ^ 1 := (pow_one D).symm
            _ ≤ D ^ (10000 * t) := Nat.pow_le_pow_right (by omega) (by omega)
        have hm_nonneg : (0 : ℤ) ≤ ((X / 2 : ℕ) : ℤ) + s := by
          have hs1 := (abs_le.mp hs_abs').1
          omega
        let m : ℕ := (((X / 2 : ℕ) : ℤ) + s).toNat
        have hm_cast : (m : ℤ) = ((X / 2 : ℕ) : ℤ) + s := Int.toNat_of_nonneg hm_nonneg
        have hm_lt : m < X := by
          have hs2 := (abs_le.mp hs_abs').2
          omega
        have hval_eq : ((a + m * d_ap : ℕ) : ℝ) = (n1 : ℝ) + (s : ℝ) * (d_ap : ℝ) := by
          have hZ : ((a + m * d_ap : ℕ) : ℤ) = (n1 : ℤ) + s * (d_ap : ℤ) := by
            dsimp only [n1]
            rw [Nat.cast_add, Nat.cast_mul, hm_cast, Nat.cast_add, Nat.cast_mul]
            ring
          exact_mod_cast hZ
        let distSq : ℝ := ∑ b : Fin D,
          (((a + m * d_ap : ℕ) : ℝ) * θ b - x (j k) b -
            (round (((a + m * d_ap : ℕ) : ℝ) * θ b - x (j k) b) : ℝ)) ^ 2
        have hdistSq_eq : distSq = ∑ b : Fin D,
            (((n1 : ℝ) * θ b + (s : ℝ) * ((d_ap : ℝ) * θ b) - x (j k) b) -
              (round ((n1 : ℝ) * θ b + (s : ℝ) * ((d_ap : ℝ) * θ b) - x (j k) b) : ℝ)) ^ 2 := by
          dsimp only [distSq]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hval_eq]
          have : ((n1 : ℝ) + (s : ℝ) * (d_ap : ℝ)) * θ b - x (j k) b =
              (n1 : ℝ) * θ b + (s : ℝ) * ((d_ap : ℝ) * θ b) - x (j k) b := by ring
          rw [this]
        have hdistSq_lt : distSq < (ρ / 5) ^ 2 := hdistSq_eq ▸ hs_hit
        have hdistSq_nn : 0 ≤ distSq := Finset.sum_nonneg fun b _ => sq_nonneg _
        have hsqrt_lt : Real.sqrt distSq < ρ := by
          have h1 : Real.sqrt distSq < ρ / 5 := by
            rw [Real.sqrt_lt' (by positivity)]
            exact hdistSq_lt
          linarith
        let r_nat : ℕ := Nat.floor (Real.sqrt distSq * (D : ℝ) ^ (4 * t))
        have hr_lt : r_nat < K := by
          have hprod_lt : Real.sqrt distSq * (D : ℝ) ^ (4 * t) < (K : ℝ) := by
            calc Real.sqrt distSq * (D : ℝ) ^ (4 * t)
                < ρ * (D : ℝ) ^ (4 * t) := mul_lt_mul_of_pos_right hsqrt_lt (pow_pos hD_pos _)
              _ = ((K : ℝ) * δ) * (D : ℝ) ^ (4 * t) := by rw [hK_mul_δ]
              _ = (K : ℝ) := by dsimp only [δ]; field_simp
          exact (Nat.floor_lt (by positivity)).mpr hprod_lt
        have hlo_r : ((r_nat : ℝ) * δ) ^ 2 ≤ distSq := by
          have hfloor_le : (r_nat : ℝ) ≤ Real.sqrt distSq * (D : ℝ) ^ (4 * t) :=
            Nat.floor_le (by positivity)
          have hmul : (r_nat : ℝ) * δ ≤ Real.sqrt distSq := by
            have h1 := mul_le_mul_of_nonneg_right hfloor_le hδ_pos.le
            have h2 : Real.sqrt distSq * (D : ℝ) ^ (4 * t) * δ = Real.sqrt distSq := by
              dsimp only [δ]; field_simp
            linarith
          calc ((r_nat : ℝ) * δ) ^ 2 ≤ (Real.sqrt distSq) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hmul 2
            _ = distSq := Real.sq_sqrt hdistSq_nn
        have hhi_r : distSq < ((((r_nat + 1 : ℕ) : ℝ)) * δ) ^ 2 := by
          have hlt_floor : Real.sqrt distSq * (D : ℝ) ^ (4 * t) < ((r_nat + 1 : ℕ) : ℝ) := by
            push_cast
            exact Nat.lt_floor_add_one _
          have hmul : Real.sqrt distSq < ((r_nat + 1 : ℕ) : ℝ) * δ := by
            have h1 := mul_lt_mul_of_pos_right hlt_floor hδ_pos
            have h2 : Real.sqrt distSq * (D : ℝ) ^ (4 * t) * δ = Real.sqrt distSq := by
              dsimp only [δ]; field_simp
            linarith
          calc distSq = (Real.sqrt distSq) ^ 2 := (Real.sq_sqrt hdistSq_nn).symm
            _ < (((r_nat + 1 : ℕ) : ℝ) * δ) ^ 2 :=
                pow_lt_pow_left₀ hmul (Real.sqrt_nonneg _) (by omega)
        refine ⟨m, ⟨r_nat, hr_lt⟩, hm_lt, fun e heq => ⟨j k, ?_, ?_⟩⟩
        · have hval : (e (j k) : ℕ) = r_nat := congrArg Fin.val heq
          rw [hval]; exact hlo_r
        · have hval : (e (j k) : ℕ) = r_nat := congrArg Fin.val heq
          rw [hval]; exact hhi_r
      choose m_of r_of hm_lt hblue_of using hhit
      have hsub : badFor p ⊆
          Finset.univ.filter (fun e : Fin M → Fin K => ∀ k : Fin Y, e (j k) ≠ r_of k) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        refine ⟨Finset.mem_univ _, fun k heq => ?_⟩
        exact he.2.2 (m_of k) (hm_lt k) (hblue_of k e heq)
      calc (badFor p).card
          ≤ (Finset.univ.filter (fun e : Fin M → Fin K => ∀ k : Fin Y, e (j k) ≠ r_of k)).card :=
            Finset.card_le_card hsub
        _ = (K - 1) ^ Y * K ^ (M - Y) := card_avoiding_funs j hj_inj r_of
    · have hempty : badFor p = ∅ := by
        ext e; simp [badFor, hvalid]
      rw [hempty]; simp
  -- Union bound over all pairs in [1, N] × [1, N]
  have hunion_lt : (pairs.biUnion badFor).card < Fintype.card (Fin M → Fin K) := by
    have hcard_pairs : pairs.card = N ^ 2 := by
      simp [pairs, sq]
    have hcard_bi : (pairs.biUnion badFor).card ≤ N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y)) := by
      calc (pairs.biUnion badFor).card
          ≤ ∑ p ∈ pairs, (badFor p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ pairs, ((K - 1) ^ Y * K ^ (M - Y)) := Finset.sum_le_sum hbad_card
        _ = pairs.card * ((K - 1) ^ Y * K ^ (M - Y)) := by simp
        _ = N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y)) := by rw [hcard_pairs]
    -- Show N^2 * (K - 1)^Y * K^(M - Y) < K^M using K^K ≥ 2 * (K - 1)^K!
    let q : ℕ := D ^ (4 * t + 4)
    have hY_eq : Y = K * q := by
      dsimp only [Y, K, q]
      rw [← pow_add]
      congr 1; omega
    have hpow_q : 2 ^ q * (K - 1) ^ Y ≤ K ^ Y := by
      rw [hY_eq, pow_mul, pow_mul, ← mul_pow]
      exact Nat.pow_le_pow_left (pow_ge_two_mul_pred_pow K hK_ge) q
    have hN2_lt : N ^ 2 < 2 ^ q := by
      have hD_lt_2D : D < 2 ^ D := Nat.lt_two_pow_self
      have hN2_le : N ^ 2 ≤ 2 ^ (400 * D * t ^ 2) := by
        calc N ^ 2 = D ^ (400 * t ^ 2) := by
              dsimp only [N]; rw [← pow_mul]; congr 1; ring
          _ ≤ (2 ^ D) ^ (400 * t ^ 2) := Nat.pow_le_pow_left hD_lt_2D.le _
          _ = 2 ^ (400 * D * t ^ 2) := by rw [← pow_mul]; congr 1; ring
      have hexp_lt : 400 * D * t ^ 2 < q := by
        have hq_ge : D ^ 4 ≤ q := Nat.pow_le_pow_right (by omega) (by omega)
        have h4 : 400 * D * t ^ 2 < D ^ 4 := by
          dsimp only [D]
          have ht3pos : 0 < t ^ 3 := Nat.pow_pos (by omega)
          have hlt : 80000 * t ^ 3 < 1600000000 * t ^ 4 := by
            calc 80000 * t ^ 3 < 1600000000 * t ^ 3 := by omega
              _ ≤ 1600000000 * (t ^ 3 * t) :=
                  Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
              _ = 1600000000 * t ^ 4 := by ring
          calc 400 * (200 * t) * t ^ 2 = 80000 * t ^ 3 := by ring
            _ < 1600000000 * t ^ 4 := hlt
            _ = (200 * t) ^ 4 := by ring
        omega
      exact lt_of_le_of_lt hN2_le (Nat.pow_lt_pow_right (by omega) hexp_lt)
    have hYM : Y ≤ M := Nat.pow_le_pow_right (by omega) (by omega)
    have hstrict : N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y)) < K ^ M := by
      have hpos_KM : 0 < K ^ (M - Y) := Nat.pow_pos (by omega)
      have hpos_Km1 : 0 < (K - 1) ^ Y := by
        have hK2 : 2 ≤ K := by
          dsimp only [K]
          calc 2 ≤ 400 := by omega
            _ ≤ D := hD_ge
            _ = D ^ 1 := (pow_one D).symm
            _ ≤ D ^ (4 * t - 4) := Nat.pow_le_pow_right (by omega) (by omega)
        exact Nat.pow_pos (by omega)
      calc N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y))
          = (N ^ 2 * (K - 1) ^ Y) * K ^ (M - Y) := by ring
        _ < (2 ^ q * (K - 1) ^ Y) * K ^ (M - Y) :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hN2_lt hpos_Km1) hpos_KM
        _ ≤ K ^ Y * K ^ (M - Y) := Nat.mul_le_mul_right _ hpow_q
        _ = K ^ M := by rw [← pow_add, Nat.add_sub_cancel' hYM]
    have hcard_funs : Fintype.card (Fin M → Fin K) = K ^ M := by simp
    rw [hcard_funs]
    exact lt_of_le_of_lt hcard_bi hstrict
  -- Pick a good e!
  have hex_good : ∃ e : Fin M → Fin K, e ∉ pairs.biUnion badFor := by
    by_contra hall
    push Not at hall
    have hsub : Finset.univ ⊆ pairs.biUnion badFor := fun e _ => hall e
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨e, he_good⟩ := hex_good
  -- Construct the 2-coloring of Icc 1 N avoiding color-0 4-APs and color-1 X-APs!
  let coloring : Icc 1 N → Fin 2 := fun z => if isBlue e z.1 then 0 else 1
  have hnot_mem : N ∉ mixedMonoAPGuaranteeSet 4 X := by
    intro hmem
    rcases hmem coloring with ⟨s, hsAP, hsC⟩ | ⟨s, hsAP, hsC⟩
    · obtain ⟨a, d_ap, ha, hd_pos, hend, hterms⟩ := isAPOfLength_extract (by omega) hsAP
      have h0 : isBlue e a := by
        obtain ⟨x0, hx0s, hx0⟩ := hterms 0 (by omega)
        have hc := hsC x0 hx0s
        dsimp only [coloring] at hc
        rw [hx0, Nat.zero_mul, Nat.add_zero] at hc
        by_contra hnb
        simp [hnb] at hc
      have h1 : isBlue e (a + d_ap) := by
        obtain ⟨x1, hx1s, hx1⟩ := hterms 1 (by omega)
        have hc := hsC x1 hx1s
        dsimp only [coloring] at hc
        rw [hx1, Nat.one_mul] at hc
        by_contra hnb
        simp [hnb] at hc
      have h2 : isBlue e (a + 2 * d_ap) := by
        obtain ⟨x2, hx2s, hx2⟩ := hterms 2 (by omega)
        have hc := hsC x2 hx2s
        dsimp only [coloring] at hc
        rw [hx2] at hc
        by_contra hnb
        simp [hnb] at hc
      exact no_blue_3AP e a d_ap ha hd_pos (by omega) ⟨h0, h1, h2⟩
    · have hX2 : 2 ≤ X := by
        dsimp only [X]
        calc 2 ≤ 400 := by omega
          _ ≤ D := hD_ge
          _ = D ^ 1 := (pow_one D).symm
          _ ≤ D ^ (10000 * t) := Nat.pow_le_pow_right (by omega) (by omega)
      obtain ⟨a, d_ap, ha, hd_pos, hend, hterms⟩ := isAPOfLength_extract hX2 hsAP
      have ha_le : a ≤ N := by omega
      have hd_le : d_ap ≤ N := by
        have hX1 : 1 ≤ X - 1 := by omega
        have : d_ap ≤ (X - 1) * d_ap := Nat.le_mul_of_pos_left d_ap hX1
        omega
      have hin_pairs : (a, d_ap) ∈ pairs :=
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha, ha_le⟩, Finset.mem_Icc.mpr ⟨hd_pos, hd_le⟩⟩
      have hin_bad : e ∈ badFor (a, d_ap) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hend, fun m hm hbm => ?_⟩
        obtain ⟨xm, hxms, hxm⟩ := hterms m hm
        have hc := hsC xm hxms
        dsimp only [coloring] at hc
        rw [hxm] at hc
        simp [hbm] at hc
      exact he_good (Finset.mem_biUnion.mpr ⟨(a, d_ap), hin_pairs, hin_bad⟩)
  -- Derive W 4 X ≥ N + 1 and contradict W 4 X ≤ C * X^d!
  have hX_pos : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hW_ge : N + 1 ≤ W 4 X := W_ge_succ_of_not_mem 4 X N (by omega) hX_pos hnot_mem
  have hX_ge_r0 : r₀ ≤ X := by
    dsimp only [X]
    calc r₀ ≤ t := ht_r0
      _ ≤ D := by dsimp only [D]; omega
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ (10000 * t) := Nat.pow_le_pow_right (by omega) (by omega)
  have hW_le := hW_bound X hX_ge_r0
  have hN_gt : C * (X : ℝ) ^ d < (N : ℝ) := by
    have hexp : 10000 * t * d + 1 ≤ 200 * t ^ 2 := by nlinarith
    have hNat : D * X ^ d ≤ N := by
      dsimp only [X, N]
      rw [← pow_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by omega) hexp
    have hReal : (D : ℝ) * (X : ℝ) ^ d ≤ (N : ℝ) := by exact_mod_cast hNat
    have hCD : C < (D : ℝ) := by
      have : (t : ℝ) ≤ (D : ℝ) := by dsimp only [D]; exact_mod_cast (show t ≤ 200 * t by omega)
      linarith
    have hXd_pos : (0 : ℝ) < (X : ℝ) ^ d := by positivity
    calc C * (X : ℝ) ^ d < (D : ℝ) * (X : ℝ) ^ d := mul_lt_mul_of_pos_right hCD hXd_pos
      _ ≤ (N : ℝ) := hReal
  have hW_ge_R : (N : ℝ) + 1 ≤ (W 4 X : ℝ) := by exact_mod_cast hW_ge
  linarith

end OMA.R_Green14_green_14_polynomial_R1
