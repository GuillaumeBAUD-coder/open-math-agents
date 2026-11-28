import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1
import Mathlib

-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1.H4.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1.H4
-- Credit: @carterleffen

/-!
# Local arithmetic on aligned prime bins via sieve and prime-multiple pairs

This reduction splits the Section 10 aligned-bin lower bound into four classical
analytic and sieve components:

1. `H1`: an individual upper sieve bound for rough numbers in a squarefree
   arithmetic progression of length at least `m^2`.
2. `H2`: the uniform Euler-weighted small-factor lower bound (Lemma 10.4).
3. `H3`: the strong Prime Number Theorem with de la Vallee Poussin error term
   for `Chebyshev.psi`.
4. `H4`: the subbin prime sieve lower bound for primes in a short subinterval
   avoiding one nonzero residue class modulo each restricted prime below `m`.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1_H4_R1
open Filter Finset Real
open scoped Classical

def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
  ∀ (m : ℕ), m.Prime → N ≤ m → ∀ (Y d : ℕ) (a : ℕ → ℕ),
    0 < Y → Squarefree d → (∀ p ∈ d.primeFactors, m ≤ p) → (m : ℝ) ^ 2 ≤ (Y : ℝ) / d →
    (((Icc 1 Y).filter fun n =>
      (∀ p ∈ d.primeFactors, n ≡ a p [MOD p]) ∧
      ∀ p ∈ (range m).filter Nat.Prime, ¬ (n ≡ a p [MOD p])).card : ℝ) ≤
    C * ((Y : ℝ) / d) * ∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹)

def H2 : Prop := ∃ N : ℕ, 2 ≤ N ∧ ∀ (m : ℕ), m.Prime → N ≤ m →
  ∀ E : Finset ℕ, E ⊆ (range m).filter Nat.Prime →
    (939 / 1000 : ℝ) * Real.log m * (∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹)) ≤
    ∑ d ∈ (Icc 1 ⌊(m : ℝ) ^ (95 / 100 : ℝ)⌋₊).filter (fun d => d.primeFactors ⊆ E),
      (∏ p ∈ E.filter (fun p => ¬ p ∣ d), (1 - ((p : ℝ) - 1)⁻¹)) / (d : ℝ)

def H3 : Prop := ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
  |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2))

def H4 : Prop := ∀ C K x : ℝ, 0 ≤ C → 0 < K → 0 < x →
  ∃ W : ℝ, 3 ≤ W ∧ ∀ w : ℝ, W ≤ w →
  ∀ (m : ℕ) (R V : ℝ), 3 ≤ m → (m : ℝ) ≤ Real.exp (K * (Real.log w) ^ 3) →
  Real.exp (w ^ ((1 : ℝ) / 4) * Real.log w) ≤ R →
  x / (16 * w ^ (2 * C + 10)) ≤ V / R → V / R ≤ w ^ (-(2 * C + 10)) →
  ∀ (D : ℕ) (A B : ℤ) (a : ℕ → ℕ),
  0 < D → (D : ℝ) ≤ w ^ C → IsUnit (A : ZMod D) → IsUnit (B : ZMod D) →
  ∀ (S : Finset ℕ) (ρ : ∀ t : ℕ, ZMod t),
  (∀ t ∈ S, t.Prime ∧ t < m ∧ ¬ t ∣ D ∧ ρ t ≠ 0) →
  let J := Nat.primesLE ⌊R + V⌋₊ \ Nat.primesLE ⌊R⌋₊
  (19 / 20 : ℝ) * ((J.card : ℝ) / (D : ℝ)) * (∏ t ∈ S, (1 - ((t : ℝ) - 1)⁻¹)) ≤
  ((J.filter fun p : ℕ => (D : ℤ) ∣ A + B * (p : ℤ) ∧
    (∀ t ∈ D.primeFactors, (((A + B * (p : ℤ)) / (D : ℤ)) : ZMod t) ≠ (a t : ZMod t)) ∧
    (∀ t ∈ S, (p : ZMod t) ≠ ρ t)).card : ℝ)

/- ### Part 1: Near-full bin comparison and weight range -/

lemma prod_one_sub_inv_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, 1 ≤ p) :
    0 ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hS p hp
  have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  linarith

lemma prod_one_sub_inv_primesLE_nonneg (m : ℕ) :
    0 ≤ ∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹) :=
  prod_one_sub_inv_nonneg _ (fun _ hp => (Nat.mem_primesLE.mp hp).2.one_le)

lemma missing_weight_bound {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w : α → ℝ) (lo eta : ℝ) (hlo : 0 ≤ lo) (heta : 0 ≤ eta)
    (hNear : (1 - eta) * (P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P, lo ≤ w p ∧ w p ≤ 2 * lo) :
    (∑ p ∈ P \ G, w p) ≤ 2 * eta * (∑ p ∈ P, w p) := by
  have hcards : ((P \ G).card : ℝ) + (G.card : ℝ) = (P.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hGP
  have hmissing : ((P \ G).card : ℝ) ≤ eta * (P.card : ℝ) := by nlinarith
  have hsumlo : (P.card : ℝ) * lo ≤ ∑ p ∈ P, w p := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (fun p hp => (hW p hp).1)
  calc
    _ ≤ ∑ _p ∈ P \ G, 2 * lo :=
      Finset.sum_le_sum (fun p hp => (hW p (Finset.mem_sdiff.mp hp).1).2)
    _ = ((P \ G).card : ℝ) * (2 * lo) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (eta * (P.card : ℝ)) * (2 * lo) := mul_le_mul_of_nonneg_right hmissing (by positivity)
    _ = 2 * eta * ((P.card : ℝ) * lo) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumlo (by positivity)

lemma near_full_owner_lower {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w T : α → ℝ) (lo eta C V : ℝ) (hlo : 0 ≤ lo) (heta : 0 ≤ eta) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hNear : (1 - eta) * (P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P, lo ≤ w p ∧ w p ≤ 2 * lo)
    (hAll : (39 / 100 : ℝ) * V * (∑ p ∈ P, w p) ≤ ∑ p ∈ P, T p)
    (hUpper : ∀ p ∈ P, T p ≤ C * V * w p) (hBudget : 2 * C * eta ≤ (1 / 20 : ℝ)) :
    (33 / 100 : ℝ) * V * (∑ p ∈ G, w p) ≤ ∑ p ∈ G, T p := by
  have hw0 : ∀ p ∈ P, 0 ≤ w p := fun p hp => hlo.trans (hW p hp).1
  have hsum0 : 0 ≤ ∑ p ∈ P, w p := Finset.sum_nonneg hw0
  have hmiss := missing_weight_bound P G hGP w lo eta hlo heta hNear hW
  have hmissT : (∑ p ∈ P \ G, T p) ≤ (1 / 20 : ℝ) * V * (∑ p ∈ P, w p) := by
    calc
      _ ≤ ∑ p ∈ P \ G, C * V * w p :=
        Finset.sum_le_sum (fun p hp => hUpper p (Finset.mem_sdiff.mp hp).1)
      _ = C * V * (∑ p ∈ P \ G, w p) := (Finset.mul_sum _ _ _).symm
      _ ≤ C * V * (2 * eta * (∑ p ∈ P, w p)) :=
        mul_le_mul_of_nonneg_left hmiss (mul_nonneg hC hV)
      _ = (2 * C * eta) * (V * (∑ p ∈ P, w p)) := by ring
      _ ≤ (1 / 20 : ℝ) * (V * (∑ p ∈ P, w p)) :=
        mul_le_mul_of_nonneg_right hBudget (mul_nonneg hV hsum0)
      _ = _ := by ring
  have hsplit : (∑ p ∈ P \ G, T p) + (∑ p ∈ G, T p) = ∑ p ∈ P, T p := Finset.sum_sdiff hGP
  have hsub : (∑ p ∈ G, w p) ≤ ∑ p ∈ P, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hGP (fun p hp _ => hw0 p hp)
  have h34 : (34 / 100 : ℝ) * V * (∑ p ∈ P, w p) ≤ ∑ p ∈ G, T p := by nlinarith
  have h33 : (33 / 100 : ℝ) * V * (∑ p ∈ G, w p) ≤ (34 / 100 : ℝ) * V * (∑ p ∈ P, w p) := by
    have h1 := mul_le_mul_of_nonneg_left hsub (show 0 ≤ (33 / 100 : ℝ) * V by positivity)
    nlinarith [mul_nonneg hV hsum0]
  exact h33.trans h34

/- ### Part 2: Prime-difference bins and subbin partition -/

lemma mem_primeDiff_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    p ∈ Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊ ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, not_and]
  constructor
  · rintro ⟨⟨hpb, hp⟩, hna⟩
    have hpa : ⌊a⌋₊ < p := Nat.lt_of_not_ge (fun h => hna h hp)
    exact ⟨hp, (Nat.floor_lt ha).mp hpa, (Nat.le_floor_iff hb).mp hpb⟩
  · rintro ⟨hp, hap, hpb⟩
    refine ⟨⟨(Nat.le_floor_iff hb).mpr hpb, hp⟩, fun h _ => ?_⟩
    have : ⌊a⌋₊ < p := (Nat.floor_lt ha).mpr hap
    omega

lemma subbin_partition {s t : ℝ} {M : ℕ} (hs : 0 < s) (ht : 0 < t) (hM : 0 < M) :
    let step := t * s / (M : ℝ)
    let J := Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊
    let Ji := fun i : ℕ => Nat.primesLE ⌊s + ((i : ℝ) + 1) * step⌋₊ \ Nat.primesLE ⌊s + (i : ℝ) * step⌋₊
    J = (Finset.range M).biUnion Ji ∧
    (Finset.range M : Set ℕ).PairwiseDisjoint Ji := by
  intro step J Ji
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hstep : 0 < step := div_pos (mul_pos ht hs) hMpos
  have hleft_nn : ∀ i : ℕ, 0 ≤ s + (i : ℝ) * step := fun i => by positivity
  have hright_nn : ∀ i : ℕ, 0 ≤ s + ((i : ℝ) + 1) * step := fun i => by positivity
  have htop_nn : 0 ≤ (1 + t) * s := by positivity
  have hend : s + (M : ℝ) * step = (1 + t) * s := by
    dsimp [step]; field_simp
  constructor
  · ext p
    rw [mem_primeDiff_iff hs.le htop_nn, Finset.mem_biUnion]
    constructor
    · rintro ⟨hp, hps, hpt⟩
      let idx := ⌊((p : ℝ) - s) / step⌋₊
      have hdiff_pos : 0 < (p : ℝ) - s := by linarith
      have hq_pos : 0 < ((p : ℝ) - s) / step := div_pos hdiff_pos hstep
      have hq_le : ((p : ℝ) - s) / step ≤ (M : ℝ) := by
        rw [div_le_iff₀ hstep]
        linarith [hend]
      by_cases hgt : (p : ℝ) = (1 + t) * s
      · refine ⟨M - 1, Finset.mem_range.mpr (by omega), ?_⟩
        rw [mem_primeDiff_iff (hleft_nn _) (hright_nn _)]
        have hM1 : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
          rw [Nat.cast_sub hM, Nat.cast_one]; ring
        refine ⟨hp, ?_, ?_⟩
        · have : s + ((M - 1 : ℕ) : ℝ) * step < s + (M : ℝ) * step := by
            have hlt : ((M - 1 : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast Nat.sub_lt hM zero_lt_one
            nlinarith
          linarith [hend]
        · rw [hM1, hend, hgt]
      · have hq_lt : ((p : ℝ) - s) / step < (M : ℝ) := by
          rw [div_lt_iff₀ hstep]
          have hplt : (p : ℝ) < (1 + t) * s := lt_of_le_of_ne hpt hgt
          linarith [hend]
        by_cases heq : (idx : ℝ) = ((p : ℝ) - s) / step
        · have hidx_pos : 0 < idx := by
            by_contra h0
            have : idx = 0 := by omega
            rw [this, Nat.cast_zero] at heq
            linarith
          refine ⟨idx - 1, Finset.mem_range.mpr ?_, ?_⟩
          · have : (idx : ℝ) < (M : ℝ) := by linarith
            have : idx < M := by exact_mod_cast this
            omega
          · rw [mem_primeDiff_iff (hleft_nn _) (hright_nn _)]
            have hi1 : ((idx - 1 : ℕ) : ℝ) + 1 = (idx : ℝ) := by
              rw [Nat.cast_sub hidx_pos, Nat.cast_one]; ring
            have hpeq : (p : ℝ) = s + (idx : ℝ) * step := by
              have := (eq_div_iff hstep.ne').mp heq
              linarith
            refine ⟨hp, ?_, ?_⟩
            · have hlt : ((idx - 1 : ℕ) : ℝ) < (idx : ℝ) := by
                exact_mod_cast Nat.sub_lt hidx_pos zero_lt_one
              nlinarith
            · rw [hi1, hpeq]
        · have hidx_lt : (idx : ℝ) < ((p : ℝ) - s) / step :=
            lt_of_le_of_ne (Nat.floor_le hq_pos.le) heq
          have hidx_ltM : idx < M := by
            have : (idx : ℝ) < (M : ℝ) := hidx_lt.trans hq_lt
            exact_mod_cast this
          refine ⟨idx, Finset.mem_range.mpr hidx_ltM, ?_⟩
          rw [mem_primeDiff_iff (hleft_nn _) (hright_nn _)]
          refine ⟨hp, ?_, ?_⟩
          · have := (lt_div_iff₀ hstep).mp hidx_lt
            linarith
          · have hlt1 : ((p : ℝ) - s) / step < (idx : ℝ) + 1 := Nat.lt_floor_add_one _
            have := (div_lt_iff₀ hstep).mp hlt1
            linarith
    · rintro ⟨i, hi, hp⟩
      have hiM : i < M := Finset.mem_range.mp hi
      rw [mem_primeDiff_iff (hleft_nn i) (hright_nn i)] at hp
      have hi1 : ((i : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast hiM
      refine ⟨hp.1, ?_, ?_⟩
      · have : 0 ≤ (i : ℝ) * step := by positivity
        linarith [hp.2.1]
      · have : s + ((i : ℝ) + 1) * step ≤ s + (M : ℝ) * step := by nlinarith
        linarith [hp.2.2, hend]
  · intro i _ j _ hij
    change Disjoint (Ji i) (Ji j)
    rw [Finset.disjoint_left]
    intro p hpi hpj
    rw [mem_primeDiff_iff (hleft_nn i) (hright_nn i)] at hpi
    rw [mem_primeDiff_iff (hleft_nn j) (hright_nn j)] at hpj
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
      nlinarith [hpi.2.2, hpj.2.1]
    · have : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hgt
      nlinarith [hpj.2.2, hpi.2.1]

lemma subbin_scale_bounds {w C x s t : ℝ} (hw : 2 ≤ w) (hC : 0 ≤ C) (hx : 0 < x)
    (hs : 0 < s) (htlo : x / 4 ≤ t) (hthi : t ≤ 1) (i : ℕ) (hi : i < ⌈w ^ (2 * C + 10)⌉₊) :
    let M := ⌈w ^ (2 * C + 10)⌉₊
    let step := t * s / (M : ℝ)
    let Ri := s + (i : ℝ) * step
    0 < M ∧ 0 < step ∧ s ≤ Ri ∧ Ri + step ≤ (1 + t) * s ∧
    x / (16 * w ^ (2 * C + 10)) ≤ step / Ri ∧ step / Ri ≤ w ^ (-(2 * C + 10)) := by
  intro M step Ri
  have hw0 : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have ht0 : 0 < t := by linarith
  have hpow_ge1 : 1 ≤ w ^ (2 * C + 10) := Real.one_le_rpow hw1 (by linarith)
  have hpow_pos : 0 < w ^ (2 * C + 10) := by linarith
  have hM_pos : 0 < M := Nat.ceil_pos.mpr hpow_pos
  have hM_ge : w ^ (2 * C + 10) ≤ (M : ℝ) := Nat.le_ceil _
  have hM_le : (M : ℝ) ≤ 2 * w ^ (2 * C + 10) := by
    have hlt : (M : ℝ) < w ^ (2 * C + 10) + 1 := Nat.ceil_lt_add_one hpow_pos.le
    linarith
  have hM_rpos : (0 : ℝ) < M := by exact_mod_cast hM_pos
  have hstep : 0 < step := div_pos (mul_pos ht0 hs) hM_rpos
  have hRi_ge : s ≤ Ri := by dsimp [Ri]; nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hRi_pos : 0 < Ri := hs.trans_le hRi_ge
  have hi1 : (i : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hi
  have hend : s + (M : ℝ) * step = (1 + t) * s := by dsimp [step]; field_simp
  have hRi_end : Ri + step ≤ (1 + t) * s := by
    have : Ri + step = s + ((i : ℝ) + 1) * step := by dsimp [Ri]; ring
    rw [this]
    nlinarith [hend]
  have hRi_le2s : Ri ≤ 2 * s := by nlinarith
  refine ⟨hM_pos, hstep, hRi_ge, hRi_end, ?_, ?_⟩
  · have h1 : (x / 4) * s / (2 * w ^ (2 * C + 10)) ≤ step := by
      dsimp [step]
      exact div_le_div₀ (by positivity) (by nlinarith) hM_rpos hM_le
    calc
      x / (16 * w ^ (2 * C + 10)) = ((x / 4) * s / (2 * w ^ (2 * C + 10))) / (2 * s) := by
        field_simp; ring
      _ ≤ step / (2 * s) := div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ step / Ri := div_le_div_of_nonneg_left hstep.le hRi_pos hRi_le2s
  · calc
      step / Ri ≤ step / s := div_le_div_of_nonneg_left hstep.le hs hRi_ge
      _ = t / (M : ℝ) := by dsimp [step]; field_simp
      _ ≤ 1 / w ^ (2 * C + 10) := div_le_div₀ (by norm_num) hthi hpow_pos hM_ge
      _ = w ^ (-(2 * C + 10)) := by rw [one_div, ← Real.rpow_neg hw0.le]

/- ### Part 3: Common m-interval geometry and integer decode -/

lemma div_between_endpoints (a : ℝ) {R p T : ℝ} (hR : 0 < R)
    (hRp : R ≤ p) (hpT : p ≤ T) :
    min (a / R) (a / T) ≤ a / p ∧ a / p ≤ max (a / R) (a / T) := by
  have hp : 0 < p := hR.trans_le hRp
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_right _ _).trans (div_le_div_of_nonneg_left ha hp hpT),
      (div_le_div_of_nonneg_left ha hR hRp).trans (le_max_left _ _)⟩
  · have han : 0 ≤ -a := by linarith
    have h1 := div_le_div_of_nonneg_left han hp hpT
    have h2 := div_le_div_of_nonneg_left han hR hRp
    simp only [neg_div] at h1 h2
    exact ⟨(min_le_left _ _).trans (by linarith),
      (show a / p ≤ a / T by linarith).trans (le_max_right _ _)⟩

lemma common_affine_bounds {A D Y q R T p m0 : ℝ}
    (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ p) (hpT : p ≤ T)
    (hlo : max (-A / q / R) (-A / q / T) + 1 ≤ m0)
    (hhi : m0 ≤ min ((D * Y - A) / q / R) ((D * Y - A) / q / T)) :
    0 < A + p * q * m0 ∧ A + p * q * m0 ≤ D * Y := by
  have hp : 0 < p := hR.trans_le hRp
  have h1 := (div_between_endpoints (-A / q) hR hRp hpT).2.trans_lt (by linarith : max (-A / q / R) (-A / q / T) < m0)
  have h2 := hhi.trans (div_between_endpoints ((D * Y - A) / q) hR hRp hpT).1
  simp only [div_div] at h1 h2
  have hl := (div_lt_iff₀ (mul_pos hq hp)).mp h1
  have hu := (le_div_iff₀ (mul_pos hq hp)).mp h2
  constructor <;> nlinarith

lemma common_integer_decode {A m0 : ℤ} {D Y q p : ℕ} {R T : ℝ}
    (hD : 0 < D) (hq : 0 < q) (hR : 0 < R) (hRp : R ≤ (p : ℝ)) (hpT : (p : ℝ) ≤ T)
    (hlo : max (-(A : ℝ) / q / R) (-(A : ℝ) / q / T) + 1 ≤ (m0 : ℝ))
    (hhi : (m0 : ℝ) ≤ min (((D : ℝ) * Y - A) / q / R) (((D : ℝ) * Y - A) / q / T))
    (hdvd : (D : ℤ) ∣ A + (p : ℤ) * q * m0) :
    let n := ((A + (p : ℤ) * q * m0) / (D : ℤ)).toNat
    1 ≤ n ∧ n ≤ Y ∧ (D : ℤ) * (n : ℤ) = A + (p : ℤ) * q * m0 := by
  intro n
  have hb := common_affine_bounds (by exact_mod_cast hq) hR hRp hpT hlo hhi
  obtain ⟨k, hk⟩ := hdvd
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hDn : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hk_eq : (A + (p : ℤ) * q * m0) / (D : ℤ) = k := by
    rw [hk, Int.mul_ediv_cancel_left _ hDn]
  have hkr : (A : ℝ) + (p : ℝ) * q * m0 = (D : ℝ) * (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by nlinarith [hb.1]
  have hkY : (k : ℝ) ≤ Y := by nlinarith [hb.2]
  have hkint : (1 : ℤ) ≤ k := by
    have : (0 : ℤ) < k := by exact_mod_cast hkpos
    omega
  have hkYint : k ≤ (Y : ℤ) := by exact_mod_cast hkY
  have hn_eq : (n : ℤ) = k := by
    dsimp [n]; rw [hk_eq, Int.toNat_of_nonneg (by omega)]
  refine ⟨by omega, by omega, ?_⟩
  rw [hn_eq, ← hk]

lemma common_length_and_height {A D Y q R T H e : ℝ}
    (hD : 1 ≤ D) (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R) (hRT : R ≤ T)
    (hH : 0 ≤ H) (he : 0 ≤ e) (hwidth : T ≤ (1 + e) * R) (hA : |A| ≤ Y * H) :
    let x0 := max (-A / q / R) (-A / q / T) + 1
    let y0 := min ((D * Y - A) / q / R) ((D * Y - A) / q / T)
    let J0 := Y / (R * q)
    (1 - 2 * e * (1 + H)) * D * J0 - 1 ≤ y0 - x0 ∧
    (x0 ≤ y0 → max |x0| |y0| ≤ (D + H) * J0 + 1) := by
  intro x0 y0 J0
  have hT : 0 < T := hR.trans_le hRT
  have hd0 : 0 ≤ 1 / R - 1 / T := sub_nonneg.mpr (one_div_le_one_div_of_le hR hRT)
  have hd_le : 1 / R - 1 / T ≤ e / R := by
    have h1 : (1 / R - 1 / T) * T = T / R - 1 := by field_simp
    have h2 : T / R ≤ 1 + e := (div_le_iff₀ hR).mpr hwidth
    have h3 : 1 / R - 1 / T ≤ e / T := (le_div_iff₀ hT).mpr (by linarith)
    exact h3.trans (div_le_div_of_nonneg_left he hR hRT)
  have hlow_err : ∀ a : ℝ, max (a / R) (a / T) ≤ a / T + |a| * (1 / R - 1 / T) := by
    intro a
    apply max_le
    · have : a / R = a / T + a * (1 / R - 1 / T) := by ring
      rw [this]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_abs_self a) hd0)
    · exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg a) hd0)
  have hup_err : ∀ b : ℝ, b / T - |b| * (1 / R - 1 / T) ≤ min (b / R) (b / T) := by
    intro b
    apply le_min
    · have : b / R = b / T + b * (1 / R - 1 / T) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right (neg_abs_le b) hd0
      nlinarith
    · exact sub_le_self _ (mul_nonneg (abs_nonneg b) hd0)
  have hmag : |-A / q| + |(D * Y - A) / q| ≤ (D * Y + 2 * |A|) / q := by
    rw [abs_div, abs_div, abs_of_pos hq, abs_neg, ← add_div]
    apply div_le_div_of_nonneg_right _ hq.le
    have h := abs_sub_le (D * Y) 0 A
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (show 0 ≤ D * Y by positivity)] at h
    linarith
  have hnorm : D * Y / q + |-A / q| + |(D * Y - A) / q| ≤ 2 * D * Y * (1 + H) / q := by
    have hDH : Y * H ≤ D * Y * H := by nlinarith [mul_nonneg hY.le hH]
    have h1 : (D * Y + 2 * |A|) / q ≤ (D * Y + 2 * D * Y * H) / q :=
      div_le_div_of_nonneg_right (by linarith) hq.le
    have h2 : D * Y / q + (D * Y + 2 * D * Y * H) / q = 2 * D * Y * (1 + H) / q := by ring
    linarith
  constructor
  · have hl := hlow_err (-A / q)
    have hu := hup_err ((D * Y - A) / q)
    have hprod := mul_le_mul hnorm hd_le hd0 (by positivity : 0 ≤ 2 * D * Y * (1 + H) / q)
    have hbase : (D * Y - A) / q / T - (-A / q / T) = (D * Y / q) / T := by ring
    have heq1 : (D * Y / q) / T - (|-A / q| + |(D * Y - A) / q|) * (1 / R - 1 / T) =
        D * Y / (R * q) - (D * Y / q + |-A / q| + |(D * Y - A) / q|) * (1 / R - 1 / T) := by ring
    have heq2 : D * Y / (R * q) - (2 * D * Y * (1 + H) / q) * (e / R) =
        (1 - 2 * e * (1 + H)) * D * J0 := by dsimp [J0]; ring
    dsimp [x0, y0]
    linarith
  · intro hxy
    have ha_b : |-A / q| ≤ (D * Y + Y * H) / q := by
      rw [abs_div, abs_neg, abs_of_pos hq]
      exact div_le_div_of_nonneg_right (by nlinarith) hq.le
    have hb_b : |(D * Y - A) / q| ≤ (D * Y + Y * H) / q := by
      rw [abs_div, abs_of_pos hq]
      apply div_le_div_of_nonneg_right _ hq.le
      have h := abs_sub_le (D * Y) 0 A
      simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (show 0 ≤ D * Y by positivity)] at h
      linarith
    have hB : max |-A / q| |(D * Y - A) / q| / R ≤ (D + H) * J0 := by
      calc
        _ ≤ ((D * Y + Y * H) / q) / R := div_le_div_of_nonneg_right (max_le ha_b hb_b) hR.le
        _ = (D + H) * J0 := by dsimp [J0]; ring
    have hx_lo : -((D + H) * J0) ≤ x0 - 1 := by
      have h1 : -(max |-A / q| |(D * Y - A) / q|) ≤ -A / q :=
        (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
      have h2 := div_le_div_of_nonneg_right h1 hR.le
      rw [neg_div] at h2
      have h3 : -A / q / R ≤ x0 - 1 := by dsimp [x0]; linarith [le_max_left (-A / q / R) (-A / q / T)]
      linarith
    have hy_hi : y0 ≤ (D + H) * J0 := by
      have h1 : (D * Y - A) / q ≤ max |-A / q| |(D * Y - A) / q| :=
        (le_abs_self _).trans (le_max_right _ _)
      have h2 := div_le_div_of_nonneg_right h1 hR.le
      have h3 : y0 ≤ (D * Y - A) / q / R := min_le_left _ _
      linarith
    apply max_le
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith

/- ### Part 4: Strong PNT to open-interval prime count and signed prime multiples -/

lemma open_prime_count_from_psi {c C X₀ u v : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hX₀ : 3 ≤ X₀) (hu : X₀ ≤ u) (huv : u ≤ v)
    (hpsi : ∀ x : ℝ, X₀ ≤ x → |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2))) :
    let Puv := (Finset.Icc (1 : ℕ) ⌊v⌋₊).filter (fun p : ℕ => p.Prime ∧ u < (p : ℝ) ∧ (p : ℝ) < v)
    ((v - u) - 2 * C * v * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 2)) - 2 * √v * Real.log v) /
      Real.log v - 1 ≤ (Puv.card : ℝ) := by
  intro Puv
  have hu3 : 3 ≤ u := hX₀.trans hu
  have hv3 : 3 ≤ v := hu3.trans huv
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hlog_le : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  have hrpow_le : (Real.log u) ^ ((1 : ℝ) / 2) ≤ (Real.log v) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog_le (by norm_num)
  have hexp_le : Real.exp (-c * (Real.log v) ^ ((1 : ℝ) / 2)) ≤
      Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpsiu := (abs_le.mp (hpsi u hu)).2
  have hpsiv := (abs_le.mp (hpsi v (hu.trans huv))).1
  have hth_v := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ v)
  have hth_u := Chebyshev.theta_le_psi u
  have htheta_diff : (v - u) - 2 * C * v * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 2)) -
      2 * √v * Real.log v ≤ Chebyshev.theta v - Chebyshev.theta u := by
    have h1 : C * v * Real.exp (-c * (Real.log v) ^ ((1 : ℝ) / 2)) ≤
        C * v * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hexp_le (by positivity)
    have h2 : C * u * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 2)) ≤
        C * v * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huv hC.le) (Real.exp_pos _).le
    linarith
  let Qset := (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime
  have hsub_sets : (Finset.Ioc 0 ⌊u⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊v⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono huv)⟩, hp.2⟩
  have hsdiff_eq : ((Finset.Ioc 0 ⌊v⌋₊).filter Nat.Prime) \ ((Finset.Ioc 0 ⌊u⌋₊).filter Nat.Prime) = Qset := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Qset]
    constructor
    · rintro ⟨⟨⟨hp0, hpv⟩, hpr⟩, hnot⟩
      refine ⟨⟨?_, hpv⟩, hpr⟩
      by_contra hle
      exact hnot ⟨⟨hp0, by omega⟩, hpr⟩
    · rintro ⟨⟨hpu, hpv⟩, hpr⟩
      refine ⟨⟨⟨by omega, hpv⟩, hpr⟩, fun h => by omega⟩
  have htheta_eq : Chebyshev.theta v - Chebyshev.theta u = ∑ p ∈ Qset, Real.log p := by
    unfold Chebyshev.theta
    rw [← hsdiff_eq, Finset.sum_sdiff_eq_sub hsub_sets]
  have htheta_upper : Chebyshev.theta v - Chebyshev.theta u ≤ (Qset.card : ℝ) * Real.log v := by
    rw [htheta_eq]
    calc
      ∑ p ∈ Qset, Real.log p ≤ ∑ _p ∈ Qset, Real.log v := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hp_le : (p : ℝ) ≤ v := (Nat.le_floor_iff hv0.le).mp (Finset.mem_Ioc.mp hp'.1).2
        exact Real.log_le_log (by exact_mod_cast hp'.2.pos) hp_le
      _ = (Qset.card : ℝ) * Real.log v := by rw [Finset.sum_const, nsmul_eq_mul]
  have hQ_sub : Qset ⊆ Puv ∪ {⌊v⌋₊} := by
    intro p hp
    obtain ⟨hI, hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpu, hpv⟩ := Finset.mem_Ioc.mp hI
    have hpuR : u < (p : ℝ) := (Nat.floor_lt hu0.le).mp hpu
    have hpvR : (p : ℝ) ≤ v := (Nat.le_floor_iff hv0.le).mp hpv
    by_cases heq : (p : ℝ) = v
    · apply Finset.mem_union_right
      rw [Finset.mem_singleton, ← heq, Nat.floor_natCast]
    · apply Finset.mem_union_left
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, hpv⟩, hpr, hpuR,
        lt_of_le_of_ne hpvR heq⟩
  have hQ_card : (Qset.card : ℝ) ≤ (Puv.card : ℝ) + 1 := by
    have h := (Finset.card_le_card hQ_sub).trans (Finset.card_union_le Puv {⌊v⌋₊})
    simp only [Finset.card_singleton] at h
    exact_mod_cast h
  have hdiv : ((v - u) - 2 * C * v * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 2)) -
      2 * √v * Real.log v) / Real.log v ≤ (Qset.card : ℝ) := by
    rw [div_le_iff₀ hlogv]
    exact htheta_diff.trans htheta_upper
  linarith

lemma signed_retained_length {x y t : ℝ} (ht : 0 ≤ t) :
    (y - x) - 4 * t ≤
      (if t ≤ y - max x t then y - max x t else 0) +
      (if t ≤ -x - max (-y) t then -x - max (-y) t else 0) := by
  have h1 : (if t ≤ y - max x t then y - max x t else 0) ≥ max (y - max x t) 0 - t := by
    split_ifs with h
    · have : max (y - max x t) 0 = y - max x t := max_eq_left (by linarith)
      linarith
    · have : max (y - max x t) 0 ≤ t := max_le (by linarith) ht
      linarith
  have h2 : (if t ≤ -x - max (-y) t then -x - max (-y) t else 0) ≥ max (-x - max (-y) t) 0 - t := by
    split_ifs with h
    · have : max (-x - max (-y) t) 0 = -x - max (-y) t := max_eq_left (by linarith)
      linarith
    · have : max (-x - max (-y) t) 0 ≤ t := max_le (by linarith) ht
      linarith
  have hpos : max (y - max x t) 0 + max (-x - max (-y) t) 0 ≥ (y - x) - 2 * t := by
    by_cases hx : t ≤ x
    · have hm : max x t = x := max_eq_left hx
      have h1' : y - x ≤ max (y - max x t) 0 := by rw [hm]; exact le_max_left _ _
      have h2' : 0 ≤ max (-x - max (-y) t) 0 := le_max_right _ _
      linarith
    · by_cases hy : y ≤ -t
      · have hm : max (-y) t = -y := max_eq_left (by linarith)
        have h1' : 0 ≤ max (y - max x t) 0 := le_max_right _ _
        have h2' : y - x ≤ max (-x - max (-y) t) 0 := by
          rw [hm, show -x - -y = y - x by ring]; exact le_max_left _ _
        linarith
      · have h1' : y - t ≤ max (y - max x t) 0 := by
          have : max x t = t := max_eq_right (by linarith)
          rw [this]; exact le_max_left _ _
        have h2' : -x - t ≤ max (-x - max (-y) t) 0 := by
          have : max (-y) t = t := max_eq_right (by linarith)
          rw [this]; exact le_max_left _ _
        linarith
  linarith

lemma prime_multiple_disjoint_sets {m : ℕ} {x y : ℝ}
    {d1 d2 : ℕ} (hd2 : 0 < d2)
    (h2 : ∀ p ∈ d2.primeFactors, p < m) (hne : d1 ≠ d2) :
    let Mset := fun d : ℕ =>
      (Finset.Icc ⌊x⌋ ⌈y⌉).filter (fun z : ℤ => x < (z : ℝ) ∧ (z : ℝ) < y ∧
        ∃ ell : ℕ, ell.Prime ∧ m < ell ∧ z.natAbs = d * ell)
    Disjoint (Mset d1) (Mset d2) := by
  intro Mset
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨_, _, _, ell1, hp1, hm1, he1⟩ := Finset.mem_filter.mp hz1
  obtain ⟨_, _, _, ell2, hp2, hm2, he2⟩ := Finset.mem_filter.mp hz2
  have hprod : d1 * ell1 = d2 * ell2 := he1.symm.trans he2
  have hdvd : ell1 ∣ d2 * ell2 := ⟨d1, by linarith⟩
  rcases hp1.dvd_mul.mp hdvd with hdiv_d2 | hdiv_ell2
  · have hmem : ell1 ∈ d2.primeFactors := Nat.mem_primeFactors.mpr ⟨hp1, hdiv_d2, hd2.ne'⟩
    have := h2 ell1 hmem
    omega
  · have hell_eq : ell1 = ell2 := (hp2.eq_one_or_self_of_dvd ell1 hdiv_ell2).resolve_left hp1.ne_one
    rw [hell_eq] at hprod
    exact hne (Nat.eq_of_mul_eq_mul_right hp2.pos hprod)

lemma prime_piece_lower {c C X₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (hX₀ : 3 ≤ X₀)
    (hpsi : ∀ x : ℝ, X₀ ≤ x → |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))
    {w Cs : ℝ} (hw : 16000 ≤ w)
    {m d0 : ℕ} {s0 H a b : ℝ}
    (hm3 : 3 ≤ m) (hX₀m : X₀ ≤ (m : ℝ))
    (hs0_lo : 203 / 100 ≤ s0) (hs0_hi : s0 ≤ 219 / 100)
    (hheight_m : 2 * w ^ (Cs + 2) ≤ (m : ℝ) ^ (1 / 50 : ℝ))
    (hm_lower_cut : 2 * w ≤ (m : ℝ) ^ (8 / 100 : ℝ))
    (hpnt_err : 2 * C * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 1 / (64000 * w ^ (Cs + 3)))
    (hsqrt_err : 2 * Real.log ((m : ℝ) ^ (3 : ℝ)) / √(m : ℝ) ≤ 1 / (64000 * w ^ (Cs + 3)))
    (hH : (m : ℝ) ^ s0 / 2 ≤ H)
    (hd0_pos : 0 < d0) (hd0_le : (d0 : ℝ) ≤ (m : ℝ) ^ (95 / 100 : ℝ))
    (ha : H / w ≤ a) (hb : b ≤ 2 * w ^ (Cs + 2) * (m : ℝ) ^ s0) :
    (if H / w ≤ b - a then
      ((1 - 1 / 4000 : ℝ) * (b - a) / ((d0 : ℝ) * ((s0 + 1 / 50) * Real.log (m : ℝ))) - 1) else 0) ≤
    (((Finset.Icc (1 : ℕ) ⌊b / (d0 : ℝ)⌋₊).filter
      (fun ell : ℕ => ell.Prime ∧ a / (d0 : ℝ) < (ell : ℝ) ∧ (ell : ℝ) < b / (d0 : ℝ))).card : ℝ) := by
  have hw0 : 0 < w := by linarith
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hd0_rpos : (0 : ℝ) < d0 := by exact_mod_cast hd0_pos
  have hd0_ge1 : (1 : ℝ) ≤ d0 := by exact_mod_cast hd0_pos
  have hms_pos : 0 < (m : ℝ) ^ s0 := Real.rpow_pos_of_pos hm_pos _
  have hH_pos : 0 < H := by linarith
  let tcut := H / w
  let Den := (s0 + 1 / 50) * Real.log (m : ℝ)
  have htcut_pos : 0 < tcut := div_pos hH_pos hw0
  split_ifs with hret
  · have hab : a ≤ b := by linarith
    have hdiv_le : a / (d0 : ℝ) ≤ b / (d0 : ℝ) := div_le_div_of_nonneg_right hab hd0_rpos.le
    have ha_div_ge_m : (m : ℝ) ≤ a / (d0 : ℝ) := by
      rw [le_div_iff₀ hd0_rpos]
      have h1 : (m : ℝ) * (d0 : ℝ) ≤ (m : ℝ) ^ (195 / 100 : ℝ) := by
        calc
          (m : ℝ) * (d0 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (95 / 100 : ℝ) := by
            rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hd0_le hm_pos.le
          _ = (m : ℝ) ^ (1 + 95 / 100 : ℝ) := (Real.rpow_add hm_pos _ _).symm
          _ = _ := by norm_num
      have h2 : (m : ℝ) ^ (195 / 100 : ℝ) * (2 * w) ≤ (m : ℝ) ^ s0 := by
        calc
          (m : ℝ) ^ (195 / 100 : ℝ) * (2 * w) ≤
              (m : ℝ) ^ (195 / 100 : ℝ) * (m : ℝ) ^ (8 / 100 : ℝ) :=
            mul_le_mul_of_nonneg_left hm_lower_cut (Real.rpow_nonneg hm_pos.le _)
          _ = (m : ℝ) ^ (195 / 100 + 8 / 100 : ℝ) := (Real.rpow_add hm_pos _ _).symm
          _ = (m : ℝ) ^ (203 / 100 : ℝ) := by norm_num
          _ ≤ (m : ℝ) ^ s0 := Real.rpow_le_rpow_of_exponent_le hm1 hs0_lo
      have h3 : (m : ℝ) ^ s0 / (2 * w) ≤ H / w := by
        rw [div_le_div_iff₀ (by positivity) hw0]; nlinarith
      have h4 : (m : ℝ) ^ (195 / 100 : ℝ) ≤ (m : ℝ) ^ s0 / (2 * w) :=
        (le_div_iff₀ (by positivity)).mpr h2
      linarith
    have hb_div_le : b / (d0 : ℝ) ≤ (m : ℝ) ^ (s0 + 1 / 50) := by
      calc
        b / (d0 : ℝ) ≤ b := div_le_self (by linarith) hd0_ge1
        _ ≤ 2 * w ^ (Cs + 2) * (m : ℝ) ^ s0 := hb
        _ ≤ (m : ℝ) ^ (1 / 50 : ℝ) * (m : ℝ) ^ s0 :=
          mul_le_mul_of_nonneg_right hheight_m hms_pos.le
        _ = (m : ℝ) ^ (1 / 50 + s0) := (Real.rpow_add hm_pos _ _).symm
        _ = _ := by congr 1; ring
    have hb_div_le3 : b / (d0 : ℝ) ≤ (m : ℝ) ^ (3 : ℝ) :=
      hb_div_le.trans (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith))
    have hb_div_pos : 0 < b / (d0 : ℝ) := hm_pos.trans_le (ha_div_ge_m.trans hdiv_le)
    have hlog_b_le : Real.log (b / (d0 : ℝ)) ≤ Den := by
      calc
        Real.log (b / (d0 : ℝ)) ≤ Real.log ((m : ℝ) ^ (s0 + 1 / 50)) :=
          Real.log_le_log hb_div_pos hb_div_le
        _ = Den := by rw [Real.log_rpow hm_pos]
    have hlog_b_pos : 0 < Real.log (b / (d0 : ℝ)) := Real.log_pos (by linarith)
    have hlog_b_le3 : Real.log (b / (d0 : ℝ)) ≤ Real.log ((m : ℝ) ^ (3 : ℝ)) :=
      Real.log_le_log hb_div_pos hb_div_le3
    have hrel : b ≤ 4 * w ^ (Cs + 3) * (b - a) := by
      have hpow_div : w ^ (Cs + 3) / w = w ^ (Cs + 2) := by
        rw [← Real.rpow_sub_one hw0.ne']; congr 1; ring
      have h1 : 4 * w ^ (Cs + 3) * (H / w) = 4 * w ^ (Cs + 2) * H := by
        calc
          4 * w ^ (Cs + 3) * (H / w) = 4 * (w ^ (Cs + 3) / w) * H := by ring
          _ = 4 * w ^ (Cs + 2) * H := by rw [hpow_div]
      have h2 : b ≤ 2 * w ^ (Cs + 2) * (2 * H) := by
        nlinarith only [hb, hH, Real.rpow_pos_of_pos hw0 (Cs + 2)]
      have h3 : 4 * w ^ (Cs + 3) * (H / w) ≤ 4 * w ^ (Cs + 3) * (b - a) :=
        mul_le_mul_of_nonneg_left hret (by positivity)
      linarith only [h1, h2, h3]
    have hpnt := open_prime_count_from_psi hc hC hX₀ (hX₀m.trans ha_div_ge_m) hdiv_le hpsi
    have hlog_a_ge : Real.log (m : ℝ) ≤ Real.log (a / (d0 : ℝ)) :=
      Real.log_le_log hm_pos ha_div_ge_m
    have hexp_a : Real.exp (-c * (Real.log (a / (d0 : ℝ))) ^ ((1 : ℝ) / 2)) ≤
        Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) := by
      apply Real.exp_le_exp.mpr
      have := Real.rpow_le_rpow hlogm.le hlog_a_ge (by norm_num : (0 : ℝ) ≤ 1 / 2)
      nlinarith only [this, hc]
    have hwCs3_ne : w ^ (Cs + 3) ≠ 0 := (Real.rpow_pos_of_pos hw0 _).ne'
    have herr1 : 2 * C * (b / (d0 : ℝ)) * Real.exp (-c * (Real.log (a / (d0 : ℝ))) ^ ((1 : ℝ) / 2)) ≤
        (1 / 16000 : ℝ) * ((b - a) / (d0 : ℝ)) := by
      have hstep1 : 2 * C * (b / (d0 : ℝ)) * Real.exp (-c * (Real.log (a / (d0 : ℝ))) ^ ((1 : ℝ) / 2)) ≤
          (2 * C * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2))) * (b / (d0 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hexp_a (by positivity : 0 ≤ 2 * C * (b / (d0 : ℝ)))
        linarith only [this]
      have hstep2 : (1 / (64000 * w ^ (Cs + 3))) * (4 * w ^ (Cs + 3) * ((b - a) / (d0 : ℝ))) =
          (1 / 16000 : ℝ) * ((b - a) / (d0 : ℝ)) := by
        field_simp [hwCs3_ne]; ring
      have hstep3 : b / (d0 : ℝ) ≤ 4 * w ^ (Cs + 3) * ((b - a) / (d0 : ℝ)) := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hrel hd0_rpos.le
      calc
        _ ≤ (2 * C * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2))) * (b / (d0 : ℝ)) := hstep1
        _ ≤ (1 / (64000 * w ^ (Cs + 3))) * (b / (d0 : ℝ)) :=
          mul_le_mul_of_nonneg_right hpnt_err hb_div_pos.le
        _ ≤ (1 / (64000 * w ^ (Cs + 3))) * (4 * w ^ (Cs + 3) * ((b - a) / (d0 : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)
        _ = _ := hstep2
    have hsqrt_le : √(m : ℝ) ≤ √(b / (d0 : ℝ)) := Real.sqrt_le_sqrt (ha_div_ge_m.trans hdiv_le)
    have herr2 : 2 * √(b / (d0 : ℝ)) * Real.log (b / (d0 : ℝ)) ≤
        (1 / 16000 : ℝ) * ((b - a) / (d0 : ℝ)) := by
      have hsq : √(b / (d0 : ℝ)) * √(b / (d0 : ℝ)) = b / (d0 : ℝ) := Real.mul_self_sqrt hb_div_pos.le
      have hsqrt_ne : √(b / (d0 : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hb_div_pos).ne'
      have h1 : 2 * √(b / (d0 : ℝ)) * Real.log (b / (d0 : ℝ)) =
          (2 * Real.log (b / (d0 : ℝ)) / √(b / (d0 : ℝ))) * (b / (d0 : ℝ)) := by
        calc
          2 * √(b / (d0 : ℝ)) * Real.log (b / (d0 : ℝ)) =
              (2 * Real.log (b / (d0 : ℝ)) / √(b / (d0 : ℝ))) * (√(b / (d0 : ℝ)) * √(b / (d0 : ℝ))) := by
            field_simp [hsqrt_ne]
          _ = (2 * Real.log (b / (d0 : ℝ)) / √(b / (d0 : ℝ))) * (b / (d0 : ℝ)) := by rw [hsq]
      rw [h1]
      have h2 : 2 * Real.log (b / (d0 : ℝ)) / √(b / (d0 : ℝ)) ≤
          2 * Real.log ((m : ℝ) ^ (3 : ℝ)) / √(m : ℝ) :=
        div_le_div₀ (by linarith only [hlog_b_pos, hlog_b_le3]) (by linarith only [hlog_b_le3])
          (Real.sqrt_pos.mpr hm_pos) hsqrt_le
      have hstep2 : (1 / (64000 * w ^ (Cs + 3))) * (4 * w ^ (Cs + 3) * ((b - a) / (d0 : ℝ))) =
          (1 / 16000 : ℝ) * ((b - a) / (d0 : ℝ)) := by
        field_simp [hwCs3_ne]; ring
      have hstep3 : b / (d0 : ℝ) ≤ 4 * w ^ (Cs + 3) * ((b - a) / (d0 : ℝ)) := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hrel hd0_rpos.le
      calc
        _ ≤ (1 / (64000 * w ^ (Cs + 3))) * (b / (d0 : ℝ)) :=
          mul_le_mul_of_nonneg_right (h2.trans hsqrt_err) hb_div_pos.le
        _ ≤ (1 / (64000 * w ^ (Cs + 3))) * (4 * w ^ (Cs + 3) * ((b - a) / (d0 : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)
        _ = _ := hstep2
    have hba_nn : 0 ≤ (b - a) / (d0 : ℝ) := div_nonneg (by linarith only [hab]) hd0_rpos.le
    have hnum : (1 - 1 / 4000 : ℝ) * ((b - a) / (d0 : ℝ)) ≤
        (b / (d0 : ℝ) - a / (d0 : ℝ)) -
        2 * C * (b / (d0 : ℝ)) * Real.exp (-c * (Real.log (a / (d0 : ℝ))) ^ ((1 : ℝ) / 2)) -
        2 * √(b / (d0 : ℝ)) * Real.log (b / (d0 : ℝ)) := by
      rw [← sub_div]; linarith only [herr1, herr2, hba_nn]
    have hrat : (1 - 1 / 4000 : ℝ) * (b - a) / ((d0 : ℝ) * Den) ≤
        ((b / (d0 : ℝ) - a / (d0 : ℝ)) -
          2 * C * (b / (d0 : ℝ)) * Real.exp (-c * (Real.log (a / (d0 : ℝ))) ^ ((1 : ℝ) / 2)) -
          2 * √(b / (d0 : ℝ)) * Real.log (b / (d0 : ℝ))) / Real.log (b / (d0 : ℝ)) := by
      calc
        _ = ((1 - 1 / 4000 : ℝ) * ((b - a) / (d0 : ℝ))) / Den := by ring
        _ ≤ ((1 - 1 / 4000 : ℝ) * ((b - a) / (d0 : ℝ))) / Real.log (b / (d0 : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) hlog_b_pos hlog_b_le
        _ ≤ _ := div_le_div_of_nonneg_right hnum hlog_b_pos.le
    dsimp [Den] at hrat
    linarith
  · exact Nat.cast_nonneg _

lemma prime_multiples_card_lower {c C X₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (hX₀ : 3 ≤ X₀)
    (hpsi : ∀ x : ℝ, X₀ ≤ x → |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))
    {w Cs : ℝ} (hw : 16000 ≤ w)
    {m d0 : ℕ} {s0 x0 y0 : ℝ}
    (hm3 : 3 ≤ m) (hX₀m : X₀ ≤ (m : ℝ))
    (hs0_lo : 203 / 100 ≤ s0) (hs0_hi : s0 ≤ 219 / 100)
    (hheight_m : 2 * w ^ (Cs + 2) ≤ (m : ℝ) ^ (1 / 50 : ℝ))
    (hm_lower_cut : 2 * w ≤ (m : ℝ) ^ (8 / 100 : ℝ))
    (hpnt_err : 2 * C * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 1 / (64000 * w ^ (Cs + 3)))
    (hsqrt_err : 2 * Real.log ((m : ℝ) ^ (3 : ℝ)) / √(m : ℝ) ≤ 1 / (64000 * w ^ (Cs + 3)))
    (hloss_err : 24 * Real.log (m : ℝ) ≤ (1 / 2000 : ℝ) * (m : ℝ))
    (hH : (m : ℝ) ^ s0 / 2 ≤ y0 - x0) (hMax : max |x0| |y0| ≤ 2 * w ^ (Cs + 2) * (m : ℝ) ^ s0)
    (hd0_pos : 0 < d0) (hd0_le : (d0 : ℝ) ≤ (m : ℝ) ^ (95 / 100 : ℝ)) :
    let Mset := (Finset.Icc ⌊x0⌋ ⌈y0⌉).filter (fun z : ℤ => x0 < (z : ℝ) ∧ (z : ℝ) < y0 ∧
      ∃ ell : ℕ, ell.Prime ∧ m < ell ∧ z.natAbs = d0 * ell)
    (999 / 1000 : ℝ) * (y0 - x0) / ((d0 : ℝ) * (s0 + 1 / 50) * Real.log m) ≤ (Mset.card : ℝ) := by
  intro Mset
  have hw0 : 0 < w := by linarith
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hd0_rpos : (0 : ℝ) < d0 := by exact_mod_cast hd0_pos
  have hms_pos : 0 < (m : ℝ) ^ s0 := Real.rpow_pos_of_pos hm_pos _
  let H := y0 - x0
  have hH_pos : 0 < H := by dsimp [H]; linarith
  let tcut := H / w
  have htcut_pos : 0 < tcut := div_pos hH_pos hw0
  let Den := (s0 + 1 / 50) * Real.log (m : ℝ)
  have hDen_pos : 0 < Den := mul_pos (by linarith) hlogm
  have hden_pos : 0 < (d0 : ℝ) * Den := mul_pos hd0_rpos hDen_pos
  have hy0_le : y0 ≤ 2 * w ^ (Cs + 2) * (m : ℝ) ^ s0 :=
    (le_abs_self y0).trans ((le_max_right _ _).trans hMax)
  have hnx0_le : -x0 ≤ 2 * w ^ (Cs + 2) * (m : ℝ) ^ s0 :=
    (neg_le_abs x0).trans ((le_max_left _ _).trans hMax)
  let A := if tcut ≤ y0 - max x0 tcut then
      (Finset.Icc (1 : ℕ) ⌊y0 / (d0 : ℝ)⌋₊).filter
        (fun ell : ℕ => ell.Prime ∧ max x0 tcut / (d0 : ℝ) < (ell : ℝ) ∧ (ell : ℝ) < y0 / (d0 : ℝ))
    else ∅
  let B := if tcut ≤ -x0 - max (-y0) tcut then
      (Finset.Icc (1 : ℕ) ⌊(-x0) / (d0 : ℝ)⌋₊).filter
        (fun ell : ℕ => ell.Prime ∧ max (-y0) tcut / (d0 : ℝ) < (ell : ℝ) ∧ (ell : ℝ) < (-x0) / (d0 : ℝ))
    else ∅
  have ha_ge_m : (m : ℝ) ≤ tcut / (d0 : ℝ) := by
    rw [le_div_iff₀ hd0_rpos]
    have h1 : (m : ℝ) * (d0 : ℝ) ≤ (m : ℝ) ^ (195 / 100 : ℝ) := by
      calc
        (m : ℝ) * (d0 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (95 / 100 : ℝ) := by
          rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hd0_le hm_pos.le
        _ = (m : ℝ) ^ (1 + 95 / 100 : ℝ) := (Real.rpow_add hm_pos _ _).symm
        _ = _ := by norm_num
    have h2 : (m : ℝ) ^ (195 / 100 : ℝ) * (2 * w) ≤ (m : ℝ) ^ s0 := by
      calc
        _ ≤ (m : ℝ) ^ (195 / 100 : ℝ) * (m : ℝ) ^ (8 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hm_lower_cut (Real.rpow_nonneg hm_pos.le _)
        _ = (m : ℝ) ^ (203 / 100 : ℝ) := by rw [← Real.rpow_add hm_pos]; norm_num
        _ ≤ (m : ℝ) ^ s0 := Real.rpow_le_rpow_of_exponent_le hm1 hs0_lo
    have h3 : (m : ℝ) ^ s0 / (2 * w) ≤ tcut := by
      dsimp [tcut, H]; rw [div_le_div_iff₀ (by positivity) hw0]; nlinarith
    have h4 : (m : ℝ) ^ (195 / 100 : ℝ) ≤ (m : ℝ) ^ s0 / (2 * w) :=
      (le_div_iff₀ (by positivity)).mpr h2
    linarith
  let Aimg := A.image (fun ell : ℕ => ((d0 : ℤ) * (ell : ℤ)))
  let Bimg := B.image (fun ell : ℕ => -((d0 : ℤ) * (ell : ℤ)))
  have hA_sub : Aimg ⊆ Mset := by
    intro z hz
    obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hz
    have hret : tcut ≤ y0 - max x0 tcut := by
      by_contra hn; simp [A, hn] at hell
    simp only [A, hret, ite_true, Finset.mem_filter] at hell
    obtain ⟨_, hpr, hlo, hhi⟩ := hell
    have hlo' := (div_lt_iff₀ hd0_rpos).mp hlo
    have hhi' := (lt_div_iff₀ hd0_rpos).mp hhi
    have hm_ell : m < ell := by
      have : (m : ℝ) < (ell : ℝ) := ha_ge_m.trans_lt
        ((div_le_div_of_nonneg_right (le_max_right x0 tcut) hd0_rpos.le).trans_lt hlo)
      exact_mod_cast this
    have hz_lo : x0 < (((d0 : ℤ) * (ell : ℤ) : ℤ) : ℝ) := by
      push_cast; linarith only [hlo', le_max_left x0 tcut]
    have hz_hi : (((d0 : ℤ) * (ell : ℤ) : ℤ) : ℝ) < y0 := by
      push_cast; linarith only [hhi']
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Int.floor_le_iff.mpr (by linarith only [hz_lo]),
      Int.le_ceil_iff.mpr (by linarith only [hz_hi])⟩, hz_lo, hz_hi, ell, hpr, hm_ell, ?_⟩
    rw [← Nat.cast_mul, Int.natAbs_natCast]
  have hB_sub : Bimg ⊆ Mset := by
    intro z hz
    obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hz
    have hret : tcut ≤ -x0 - max (-y0) tcut := by
      by_contra hn; simp [B, hn] at hell
    simp only [B, hret, ite_true, Finset.mem_filter] at hell
    obtain ⟨_, hpr, hlo, hhi⟩ := hell
    have hlo' := (div_lt_iff₀ hd0_rpos).mp hlo
    have hhi' := (lt_div_iff₀ hd0_rpos).mp hhi
    have hm_ell : m < ell := by
      have : (m : ℝ) < (ell : ℝ) := ha_ge_m.trans_lt
        ((div_le_div_of_nonneg_right (le_max_right (-y0) tcut) hd0_rpos.le).trans_lt hlo)
      exact_mod_cast this
    have hz_lo : x0 < ((-((d0 : ℤ) * (ell : ℤ)) : ℤ) : ℝ) := by
      push_cast; linarith only [hhi']
    have hz_hi : ((-((d0 : ℤ) * (ell : ℤ)) : ℤ) : ℝ) < y0 := by
      push_cast; linarith only [hlo', le_max_left (-y0) tcut]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Int.floor_le_iff.mpr (by linarith only [hz_lo]),
      Int.le_ceil_iff.mpr (by linarith only [hz_hi])⟩, hz_lo, hz_hi, ell, hpr, hm_ell, ?_⟩
    rw [Int.natAbs_neg, ← Nat.cast_mul, Int.natAbs_natCast]
  have hAB_disj : Disjoint Aimg Bimg := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨e1, he1, rfl⟩ := Finset.mem_image.mp hzA
    obtain ⟨e2, he2, heq⟩ := Finset.mem_image.mp hzB
    have h1 : 0 < e1 := by
      by_cases hret : tcut ≤ y0 - max x0 tcut
      · simp only [A, hret, ite_true, Finset.mem_filter] at he1; exact he1.2.1.pos
      · simp [A, hret] at he1
    have h2 : 0 < e2 := by
      by_cases hret : tcut ≤ -x0 - max (-y0) tcut
      · simp only [B, hret, ite_true, Finset.mem_filter] at he2; exact he2.2.1.pos
      · simp [B, hret] at he2
    have hpos1 : (0 : ℤ) < (d0 : ℤ) * (e1 : ℤ) := by positivity
    have hpos2 : (0 : ℤ) < (d0 : ℤ) * (e2 : ℤ) := by positivity
    omega
  have hcard_AB : (A.card : ℝ) + (B.card : ℝ) ≤ (Mset.card : ℝ) := by
    have hA_inj : Aimg.card = A.card := Finset.card_image_of_injective A (fun e1 e2 h => by
      have : (d0 : ℤ) ≠ 0 := by exact_mod_cast hd0_pos.ne'
      have := mul_left_cancel₀ this h; exact_mod_cast this)
    have hB_inj : Bimg.card = B.card := Finset.card_image_of_injective B (fun e1 e2 h => by
      have h' : (d0 : ℤ) * (e1 : ℤ) = (d0 : ℤ) * (e2 : ℤ) := by omega
      have : (d0 : ℤ) ≠ 0 := by exact_mod_cast hd0_pos.ne'
      have := mul_left_cancel₀ this h'; exact_mod_cast this)
    have hu := Finset.card_le_card (Finset.union_subset hA_sub hB_sub)
    rw [Finset.card_union_of_disjoint hAB_disj, hA_inj, hB_inj] at hu
    exact_mod_cast hu
  have hAp : (if tcut ≤ y0 - max x0 tcut then
      ((1 - 1 / 4000 : ℝ) * (y0 - max x0 tcut) / ((d0 : ℝ) * Den) - 1) else 0) ≤ (A.card : ℝ) := by
    have hp := prime_piece_lower hc hC hX₀ hpsi hw hm3 hX₀m hs0_lo hs0_hi hheight_m hm_lower_cut
      hpnt_err hsqrt_err hH hd0_pos hd0_le (le_max_right x0 tcut) hy0_le
    by_cases hret : tcut ≤ y0 - max x0 tcut
    · simpa only [A, Den, tcut, H, hret, ite_true] using hp
    · simp only [A, hret, ite_false, Finset.card_empty, Nat.cast_zero, le_refl]
  have hBp : (if tcut ≤ -x0 - max (-y0) tcut then
      ((1 - 1 / 4000 : ℝ) * (-x0 - max (-y0) tcut) / ((d0 : ℝ) * Den) - 1) else 0) ≤ (B.card : ℝ) := by
    have hp := prime_piece_lower hc hC hX₀ hpsi hw hm3 hX₀m hs0_lo hs0_hi hheight_m hm_lower_cut
      hpnt_err hsqrt_err hH hd0_pos hd0_le (le_max_right (-y0) tcut) hnx0_le
    by_cases hret : tcut ≤ -x0 - max (-y0) tcut
    · simpa only [B, Den, tcut, H, hret, ite_true] using hp
    · simp only [B, hret, ite_false, Finset.card_empty, Nat.cast_zero, le_refl]
  have hA_lo : (1 - 1 / 4000 : ℝ) * (if tcut ≤ y0 - max x0 tcut then y0 - max x0 tcut else 0) /
      ((d0 : ℝ) * Den) - 1 ≤ (A.card : ℝ) := by
    by_cases hret : tcut ≤ y0 - max x0 tcut
    · simpa only [hret, ite_true] using hAp
    · simp only [hret, ite_false, mul_zero, zero_div, zero_sub]
      linarith [Nat.cast_nonneg (α := ℝ) A.card]
  have hB_lo : (1 - 1 / 4000 : ℝ) * (if tcut ≤ -x0 - max (-y0) tcut then -x0 - max (-y0) tcut else 0) /
      ((d0 : ℝ) * Den) - 1 ≤ (B.card : ℝ) := by
    by_cases hret : tcut ≤ -x0 - max (-y0) tcut
    · simpa only [hret, ite_true] using hBp
    · simp only [hret, ite_false, mul_zero, zero_div, zero_sub]
      linarith [Nat.cast_nonneg (α := ℝ) B.card]
  have hret_len := signed_retained_length (x := x0) (y := y0) htcut_pos.le
  have htrim : 4 * tcut ≤ (1 / 4000 : ℝ) * H := by
    dsimp [tcut]
    rw [show 4 * (H / w) = (4 / w) * H by ring]
    apply mul_le_mul_of_nonneg_right _ hH_pos.le
    rw [div_le_iff₀ hw0]; linarith only [hw]
  have h2_loss : (2 : ℝ) ≤ (1 / 2000 : ℝ) * H / ((d0 : ℝ) * Den) := by
    rw [le_div_iff₀ hden_pos]
    have hd_le_m : (d0 : ℝ) ≤ (m : ℝ) :=
      hd0_le.trans (Real.rpow_le_self_of_one_le hm1 (by norm_num))
    have hm2_le_2H : (m : ℝ) ^ 2 ≤ 2 * H := by
      have : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ s0 := by
        rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num; linarith only [hs0_lo])
      dsimp [H]; linarith only [this, hH]
    have hden_le : (d0 : ℝ) * Den ≤ 3 * (m : ℝ) * Real.log (m : ℝ) := by
      have hD3 : Den ≤ 3 * Real.log (m : ℝ) := by dsimp [Den]; nlinarith only [hs0_hi, hlogm]
      have h1 := mul_le_mul hd_le_m hD3 hDen_pos.le hm_pos.le
      linarith only [h1]
    have hmul2 : 24 * (m : ℝ) * Real.log (m : ℝ) ≤ (1 / 2000 : ℝ) * (m : ℝ) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hloss_err hm_pos.le
      nlinarith only [h1]
    have hmlog_nn : 0 ≤ (m : ℝ) * Real.log (m : ℝ) := mul_nonneg hm_pos.le hlogm.le
    linarith only [hden_le, hmul2, hm2_le_2H, hmlog_nn]
  have hcomb : (1 - 1 / 4000 : ℝ) * ((1 - 1 / 4000 : ℝ) * H) / ((d0 : ℝ) * Den) - 2 ≤ (Mset.card : ℝ) := by
    have hlen_ge : (1 - 1 / 4000 : ℝ) * H ≤
        (if tcut ≤ y0 - max x0 tcut then y0 - max x0 tcut else 0) +
        (if tcut ≤ -x0 - max (-y0) tcut then -x0 - max (-y0) tcut else 0) := by
      dsimp [H]; linarith only [hret_len, htrim]
    have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlen_ge (by norm_num : (0 : ℝ) ≤ 1 - 1 / 4000)) hden_pos.le
    have h2 : (1 - 1 / 4000 : ℝ) *
        ((if tcut ≤ y0 - max x0 tcut then y0 - max x0 tcut else 0) +
         (if tcut ≤ -x0 - max (-y0) tcut then -x0 - max (-y0) tcut else 0)) / ((d0 : ℝ) * Den) - 2 =
        ((1 - 1 / 4000 : ℝ) * (if tcut ≤ y0 - max x0 tcut then y0 - max x0 tcut else 0) / ((d0 : ℝ) * Den) - 1) +
        ((1 - 1 / 4000 : ℝ) * (if tcut ≤ -x0 - max (-y0) tcut then -x0 - max (-y0) tcut else 0) / ((d0 : ℝ) * Den) - 1) := by ring
    linarith only [h1, h2, hA_lo, hB_lo, hcard_AB]
  have hfinal_const : (999 / 1000 : ℝ) ≤ (1 - 1 / 4000 : ℝ) * (1 - 1 / 4000 : ℝ) - 1 / 2000 := by
    norm_num
  have hkey := mul_le_mul_of_nonneg_right hfinal_const (div_nonneg hH_pos.le hden_pos.le)
  have heq_main : (999 / 1000 : ℝ) * (y0 - x0) / ((d0 : ℝ) * (s0 + 1 / 50) * Real.log m) =
      (999 / 1000 : ℝ) * (H / ((d0 : ℝ) * Den)) := by dsimp [H, Den]; ring
  rw [heq_main]
  have heq_rhs : ((1 - 1 / 4000 : ℝ) * (1 - 1 / 4000 : ℝ) - 1 / 2000) * (H / ((d0 : ℝ) * Den)) =
      (1 - 1 / 4000 : ℝ) * ((1 - 1 / 4000 : ℝ) * H) / ((d0 : ℝ) * Den) - (1 / 2000 : ℝ) * H / ((d0 : ℝ) * Den) := by ring
  linarith

/- ### Part 5: Alignment, avoidance, and pair double-counting -/

lemma isUnit_intCast_of_coprime {D : ℕ} {z : ℤ} (h : z.natAbs.Coprime D) :
    IsUnit (z : ZMod D) := by
  have h1 : IsUnit ((z.natAbs : ℕ) : ZMod D) := (ZMod.isUnit_iff_coprime _ _).mpr h
  rcases Int.natAbs_eq z with hpos | hneg
  · have : (z : ZMod D) = ((z.natAbs : ℕ) : ZMod D) := by
      have := congrArg (Int.cast : ℤ → ZMod D) hpos; simpa using this
    rwa [this]
  · have : (z : ZMod D) = -((z.natAbs : ℕ) : ZMod D) := by
      have := congrArg (Int.cast : ℤ → ZMod D) hneg; simpa using this
    rw [this]; exact h1.neg

lemma actual_avoidance_from_tag {m q p d0 ell : ℕ} {r : ℚ} {a : ℕ → ℕ} {m0 : ℤ}
    (hq_ge : ∀ u ∈ q.primeFactors, m ≤ u) (hq_pos : 0 < q)
    (hp_prime : p.Prime) (hp_ge : m ≤ p)
    (hell_prime : ell.Prime) (hell_gt : m < ell) (hm0_abs : m0.natAbs = d0 * ell)
    (hd0_pos : 0 < d0)
    (hd0_supp : d0.primeFactors ⊆ ((range m).filter Nat.Prime).filter
      (fun u => ¬ u ∣ r.den ∧ (r.den : ZMod u) * (a u : ZMod u) ≠ (r.num : ZMod u)))
    (hD_avoid : ∀ u ∈ r.den.primeFactors,
      (((r.num + ((q : ℤ) * m0) * (p : ℤ)) / (r.den : ℤ)) : ZMod u) ≠ (a u : ZMod u))
    (hS_avoid : ∀ u ∈ (((range m).filter Nat.Prime).filter
      (fun u => ¬ u ∣ r.den ∧ (r.den : ZMod u) * (a u : ZMod u) ≠ (r.num : ZMod u))).filter (fun u => ¬ u ∣ d0),
      (p : ZMod u) ≠ (((q : ℤ) * m0 : ZMod u)⁻¹ * ((r.den : ZMod u) * (a u : ZMod u) - (r.num : ZMod u))))
    {n : ℕ} (hn_eq : (r.den : ℤ) * (n : ℤ) = r.num + (p : ℤ) * (q : ℤ) * m0) :
    ∀ u ∈ (range m).filter Nat.Prime, ¬ (n ≡ a u [MOD u]) := by
  intro u hu hmod
  obtain ⟨hu_lt, hu_pr⟩ := Finset.mem_filter.mp hu
  rw [Finset.mem_range] at hu_lt
  let _ : Fact u.Prime := ⟨hu_pr⟩
  have hn_cast : (n : ZMod u) = (a u : ZMod u) := (ZMod.natCast_eq_natCast_iff n (a u) u).mpr hmod
  have heq_z : (r.den : ℤ) * (n : ℤ) = r.num + ((q : ℤ) * m0) * (p : ℤ) := by linarith
  have hdiv_eq : (r.num + ((q : ℤ) * m0) * (p : ℤ)) / (r.den : ℤ) = (n : ℤ) := by
    rw [← heq_z, Int.mul_ediv_cancel_left _ (by exact_mod_cast r.den_pos.ne')]
  by_cases huD : u ∣ r.den
  · have hmemD : u ∈ r.den.primeFactors := Nat.mem_primeFactors.mpr ⟨hu_pr, huD, r.den_pos.ne'⟩
    have hne := hD_avoid u hmemD
    rw [hdiv_eq] at hne
    exact hne (by simpa using hn_cast)
  · have hmod_u := congrArg (fun z : ℤ => (z : ZMod u)) heq_z
    push_cast at hmod_u
    rw [hn_cast] at hmod_u
    have hu_not_q : ¬ u ∣ q := by
      intro hdivq
      have := hq_ge u (Nat.mem_primeFactors.mpr ⟨hu_pr, hdivq, hq_pos.ne'⟩)
      omega
    have hu_not_p : ¬ u ∣ p := by
      intro hdivp
      rcases hp_prime.eq_one_or_self_of_dvd u hdivp with h1 | h2
      · exact hu_pr.ne_one h1
      · omega
    have hu_not_ell : ¬ u ∣ ell := by
      intro hdive
      rcases hell_prime.eq_one_or_self_of_dvd u hdive with h1 | h2
      · exact hu_pr.ne_one h1
      · omega
    by_cases halign : (r.den : ZMod u) * (a u : ZMod u) = (r.num : ZMod u)
    · have hzero : ((q : ZMod u) * (m0 : ZMod u)) * (p : ZMod u) = 0 := by
        linear_combination -hmod_u + halign
      have hq0 : (q : ZMod u) ≠ 0 := by
        intro h; exact hu_not_q ((ZMod.natCast_eq_zero_iff q u).mp h)
      have hp0 : (p : ZMod u) ≠ 0 := by
        intro h; exact hu_not_p ((ZMod.natCast_eq_zero_iff p u).mp h)
      have hm0_zero : (m0 : ZMod u) = 0 := by
        rcases mul_eq_zero.mp hzero with hqm | hpz
        · rcases mul_eq_zero.mp hqm with hqz | hm0z
          · exact absurd hqz hq0
          · exact hm0z
        · exact absurd hpz hp0
      have hu_m0 : u ∣ m0.natAbs := by
        have h1 : (u : ℤ) ∣ m0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m0 u).mp hm0_zero
        exact Int.natCast_dvd.mp h1
      rw [hm0_abs] at hu_m0
      rcases hu_pr.dvd_mul.mp hu_m0 with hu_d0 | hu_ell
      · have hE := hd0_supp (Nat.mem_primeFactors.mpr ⟨hu_pr, hu_d0, hd0_pos.ne'⟩)
        exact (Finset.mem_filter.mp hE).2.2 halign
      · exact hu_not_ell hu_ell
    · by_cases hu_d0 : u ∣ d0
      · have hu_m0_nat : u ∣ m0.natAbs := by rw [hm0_abs]; exact dvd_mul_of_dvd_left hu_d0 ell
        have hu_m0 : (u : ℤ) ∣ m0 := Int.natCast_dvd.mpr hu_m0_nat
        have hm0_z : (m0 : ZMod u) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m0 u).mpr hu_m0
        rw [hm0_z, mul_zero, zero_mul, add_zero] at hmod_u
        exact halign hmod_u
      · have hu_S : u ∈ (((range m).filter Nat.Prime).filter
            (fun u => ¬ u ∣ r.den ∧ (r.den : ZMod u) * (a u : ZMod u) ≠ (r.num : ZMod u))).filter
            (fun u => ¬ u ∣ d0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu, huD, halign⟩, hu_d0⟩
        have hB_ne : ((q : ℤ) * m0 : ZMod u) ≠ 0 := by
          push_cast
          apply mul_ne_zero
          · intro h; exact hu_not_q ((ZMod.natCast_eq_zero_iff q u).mp h)
          · intro h
            have h1 : u ∣ m0.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd m0 u).mp h)
            rw [hm0_abs] at h1
            rcases hu_pr.dvd_mul.mp h1 with h2 | h2
            · exact hu_d0 h2
            · exact hu_not_ell h2
        have hlin : ((q : ℤ) * m0 : ZMod u) * (p : ZMod u) =
            (r.den : ZMod u) * (a u : ZMod u) - (r.num : ZMod u) := by
          push_cast; linear_combination -hmod_u
        have hpeq : (p : ZMod u) = ((q : ℤ) * m0 : ZMod u)⁻¹ *
            ((r.den : ZMod u) * (a u : ZMod u) - (r.num : ZMod u)) := by
          rw [← hlin, ← mul_assoc, inv_mul_cancel₀ hB_ne, one_mul]
        exact hS_avoid u hu_S hpeq

lemma hypothetical_modulus_congr {m p q : ℕ} {r : ℚ} {a : ℕ → ℕ} {m0 : ℤ} {n : ℕ}
    (hp_prime : p.Prime) (hq_pos : 0 < q)
    (hD_cop_p : r.den.Coprime p) (hD_lt_m : r.den < m)
    (hq_align : ∀ u ∈ q.primeFactors, m ≤ u ∧ (r.den : ZMod u) * (a u : ZMod u) = (r.num : ZMod u))
    (hn_eq : (r.den : ℤ) * (n : ℤ) = r.num + (p : ℤ) * (q : ℤ) * m0) :
    let ap := fun u : ℕ => if u = p then ((r.den : ZMod p)⁻¹ * (r.num : ZMod p)).val else a u
    ∀ u ∈ (p * q).primeFactors, n ≡ ap u [MOD u] := by
  intro ap u hu
  have hu_pr := Nat.prime_of_mem_primeFactors hu
  have hu_dvd := Nat.dvd_of_mem_primeFactors hu
  let _ : Fact u.Prime := ⟨hu_pr⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have hmod_u := congrArg (fun z : ℤ => (z : ZMod u)) hn_eq
  have hpq_z : (((p : ℤ) * (q : ℤ)) : ZMod u) = 0 := by
    have h0 : ((p * q : ℕ) : ZMod u) = 0 := (ZMod.natCast_eq_zero_iff (p * q) u).mpr hu_dvd
    simpa [Nat.cast_mul] using h0
  have hmul_zero : (r.den : ZMod u) * (n : ZMod u) = (r.num : ZMod u) := by
    push_cast at hmod_u
    have hz : ((p : ZMod u) * (q : ZMod u)) * (m0 : ZMod u) = 0 := by
      have hpq' : (p : ZMod u) * (q : ZMod u) = 0 := by simpa using hpq_z
      rw [hpq', zero_mul]
    rw [hz, add_zero] at hmod_u
    exact hmod_u
  by_cases hup : u = p
  · subst hup
    have hD_unit : IsUnit (r.den : ZMod u) := (ZMod.isUnit_iff_coprime _ _).mpr hD_cop_p
    have hD_ne : (r.den : ZMod u) ≠ 0 := hD_unit.ne_zero
    have hap_eq : (ap u : ZMod u) = (r.den : ZMod u)⁻¹ * (r.num : ZMod u) := by
      simp [ap]
    rw [hap_eq]
    apply mul_left_cancel₀ hD_ne
    rw [hmul_zero, ← mul_assoc, mul_inv_cancel₀ hD_ne, one_mul]
  · have hu_q : u ∈ q.primeFactors := by
      rcases hu_pr.dvd_mul.mp hu_dvd with hdivp | hdivq
      · exfalso
        rcases hp_prime.eq_one_or_self_of_dvd u hdivp with h1 | h2
        · exact hu_pr.ne_one h1
        · exact hup h2
      · exact Nat.mem_primeFactors.mpr ⟨hu_pr, hdivq, hq_pos.ne'⟩
    have ⟨hu_ge, hu_al⟩ := hq_align u hu_q
    have hD_cop_u : r.den.Coprime u := by
      apply Nat.Coprime.symm
      apply hu_pr.coprime_iff_not_dvd.mpr
      intro hdivD
      have := Nat.le_of_dvd r.den_pos hdivD
      omega
    have hD_ne : (r.den : ZMod u) ≠ 0 := ((ZMod.isUnit_iff_coprime _ _).mpr hD_cop_u).ne_zero
    have hap_eq : ap u = a u := by simp [ap, hup]
    rw [hap_eq]
    apply mul_left_cancel₀ hD_ne
    rw [hmul_zero, hu_al]

lemma eventually_threshold_params (c C_pnt X₀ C_s : ℝ)
    (hc : 0 < c) (hCp : 0 < C_pnt) (hCs : 0 ≤ C_s) :
    ∃ W : ℝ, 16000 ≤ W ∧ ∀ w : ℝ, W ≤ w →
      ∀ m : ℕ, Real.exp ((Real.log w) ^ 3) ≤ (m : ℝ) →
        3 ≤ m ∧ X₀ ≤ (m : ℝ) ∧
        w ^ C_s < (m : ℝ) ∧
        2 * w ^ (C_s + 2) ≤ (m : ℝ) ^ (1 / 50 : ℝ) ∧
        2 * w ≤ (m : ℝ) ^ (8 / 100 : ℝ) ∧
        2 * C_pnt * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) ≤
          1 / (64000 * w ^ (C_s + 3)) ∧
        2 * Real.log ((m : ℝ) ^ (3 : ℝ)) / √(m : ℝ) ≤ 1 / (64000 * w ^ (C_s + 3)) ∧
        24 * Real.log (m : ℝ) ≤ (1 / 2000 : ℝ) * (m : ℝ) ∧
        (999 / 1000 : ℝ) * (m : ℝ) ^ (203 / 100 : ℝ) ≤
          (1 - 4 * w ^ (-(8 : ℝ))) * (m : ℝ) ^ (203 / 100 : ℝ) - 1 := by
  have he1 : ∀ᶠ w : ℝ in atTop, 16000 ≤ w := eventually_ge_atTop 16000
  let Lthr : ℝ := max 10 (max (50 * (Real.log 2 + C_s + 3))
    (((C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1)) / c + 10) ^ 2))
  have he_log : ∀ᶠ w : ℝ in atTop, Lthr ≤ Real.log w :=
    Real.tendsto_log_atTop.eventually_ge_atTop Lthr
  have he_sqrt : ∀ᶠ t : ℝ in atTop, 48000 * Real.log t ≤ t := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).def (show (0 : ℝ) < 1 / 48000 by positivity)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1),
      abs_of_pos (by linarith : 0 < t)] at ht
    linarith
  have he_sq_log : ∀ᶠ t : ℝ in atTop, 384000 * Real.log t ≤ t ^ (1 / 4 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).def (show (0 : ℝ) < 1 / 384000 by positivity)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1),
      abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)] at ht
    linarith
  have hcube : Tendsto (fun w : ℝ => Real.exp ((Real.log w) ^ 3)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp Real.tendsto_log_atTop)
  have hall : ∀ᶠ w : ℝ in atTop, 16000 ≤ w ∧
      ∀ m : ℕ, Real.exp ((Real.log w) ^ 3) ≤ (m : ℝ) →
        3 ≤ m ∧ X₀ ≤ (m : ℝ) ∧ w ^ C_s < (m : ℝ) ∧
        2 * w ^ (C_s + 2) ≤ (m : ℝ) ^ (1 / 50 : ℝ) ∧
        2 * w ≤ (m : ℝ) ^ (8 / 100 : ℝ) ∧
        2 * C_pnt * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 1 / (64000 * w ^ (C_s + 3)) ∧
        2 * Real.log ((m : ℝ) ^ (3 : ℝ)) / √(m : ℝ) ≤ 1 / (64000 * w ^ (C_s + 3)) ∧
        24 * Real.log (m : ℝ) ≤ (1 / 2000 : ℝ) * (m : ℝ) ∧
        (999 / 1000 : ℝ) * (m : ℝ) ^ (203 / 100 : ℝ) ≤
          (1 - 4 * w ^ (-(8 : ℝ))) * (m : ℝ) ^ (203 / 100 : ℝ) - 1 := by
    obtain ⟨T1, hT1⟩ := eventually_atTop.mp he_sqrt
    obtain ⟨T2, hT2⟩ := eventually_atTop.mp he_sq_log
    filter_upwards [he1, he_log, hcube.eventually_ge_atTop (max (max T1 T2) (max X₀ 100000))] with w hw hL hM_big
    refine ⟨hw, ?_⟩
    intro m hm
    have hw0 : 0 < w := by linarith
    have hw1 : 1 ≤ w := by linarith
    have hL10 : 10 ≤ Real.log w := (le_max_left _ _).trans hL
    have hL_right : max (50 * (Real.log 2 + C_s + 3))
        (((C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1)) / c + 10) ^ 2) ≤ Real.log w :=
      (le_max_right _ _).trans hL
    have hL50 : 50 * (Real.log 2 + C_s + 3) ≤ Real.log w := (le_max_left _ _).trans hL_right
    have hLc_sq : ((C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1)) / c + 10) ^ 2 ≤ Real.log w :=
      (le_max_right _ _).trans hL_right
    have hm_big : max (max T1 T2) (max X₀ 100000) ≤ (m : ℝ) := hM_big.trans hm
    have hm_T1 : T1 ≤ (m : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hm_big)
    have hm_T2 : T2 ≤ (m : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hm_big)
    have hm_X0 : X₀ ≤ (m : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hm_big)
    have hm_1e5 : (100000 : ℝ) ≤ (m : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hm_big)
    have hm_pos : (0 : ℝ) < m := by linarith
    have hlogm_ge : (Real.log w) ^ 3 ≤ Real.log (m : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) hm
      rwa [Real.log_exp] at this
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL_sq : Real.log w ≤ (Real.log w) ^ 2 := by nlinarith
    have hL_cu : (Real.log w) ^ 2 ≤ (Real.log w) ^ 3 := by nlinarith
    have h2wC : 2 * w ^ (C_s + 2) ≤ (m : ℝ) ^ (1 / 50 : ℝ) := by
      have h1 : Real.log 2 + (C_s + 2) * Real.log w ≤ (1 / 50 : ℝ) * Real.log (m : ℝ) := by
        have : Real.log 2 + (C_s + 2) * Real.log w ≤ (Real.log 2 + C_s + 3) * Real.log w := by nlinarith
        have : 50 * ((Real.log 2 + C_s + 3) * Real.log w) ≤ (Real.log w) ^ 2 := by nlinarith
        nlinarith
      calc
        2 * w ^ (C_s + 2) = Real.exp (Real.log 2 + (C_s + 2) * Real.log w) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hw0]
          congr 1; congr 1; ring
        _ ≤ Real.exp ((1 / 50 : ℝ) * Real.log (m : ℝ)) := Real.exp_le_exp.mpr h1
        _ = (m : ℝ) ^ (1 / 50 : ℝ) := by rw [Real.rpow_def_of_pos hm_pos]; congr 1; ring
    have hwC_lt : w ^ C_s < (m : ℝ) := by
      have h1 : C_s * Real.log w < Real.log (m : ℝ) := by nlinarith
      rw [Real.rpow_def_of_pos hw0, ← Real.exp_log hm_pos]
      exact Real.exp_lt_exp.mpr (by linarith)
    have h2w_le : 2 * w ≤ (m : ℝ) ^ (8 / 100 : ℝ) := by
      have h1 : 2 * w ≤ 2 * w ^ (C_s + 2) := by
        have : w ≤ w ^ (C_s + 2) := by
          nth_rw 1 [← Real.rpow_one w]
          exact Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
        linarith
      exact h1.trans (h2wC.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)))
    have hsqrt_logm : (Real.log w) ^ (3 / 2 : ℝ) ≤ (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2) := by
      have h1 := Real.rpow_le_rpow (by positivity) hlogm_ge (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.rpow_natCast (Real.log w) 3, ← Real.rpow_mul (by linarith)] at h1
      norm_num at h1
      exact h1
    have hsqrt_L : (C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1)) / c + 10 ≤
        (Real.log w) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le hLc_sq
    have hL32 : ((C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1)) / c + 10) * Real.log w ≤
        (Real.log w) ^ (3 / 2 : ℝ) := by
      have : (Real.log w) ^ ((1 : ℝ) / 2) * Real.log w = (Real.log w) ^ (3 / 2 : ℝ) := by
        nth_rw 2 [← Real.rpow_one (Real.log w)]
        rw [← Real.rpow_add (by linarith only [hL10])]
        norm_num
      rw [← this]
      exact mul_le_mul_of_nonneg_right hsqrt_L (by linarith only [hL10])
    have hpnt_b : 2 * C_pnt * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) ≤
        1 / (64000 * w ^ (C_s + 3)) := by
      rw [le_div_iff₀ (by positivity)]
      have hK_ge : Real.log (128000 * C_pnt) + (C_s + 3) * Real.log w ≤
          c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2) := by
        have hlog_le1 : Real.log (128000 * C_pnt) ≤ Real.log (128000 * C_pnt + 128000 * 6 + 1) :=
          Real.log_le_log (by positivity) (by linarith only [hCp])
        have hlog_nn : 0 ≤ Real.log (128000 * C_pnt + 128000 * 6 + 1) :=
          Real.log_nonneg (by linarith only [hCp])
        have hstep1 : c * (((C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1)) / c + 10) * Real.log w) =
            (C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1) + 10 * c) * Real.log w := by
          field_simp [hc.ne']
        have hstep2 : Real.log (128000 * C_pnt + 128000 * 6 + 1) ≤
            Real.log (128000 * C_pnt + 128000 * 6 + 1) * Real.log w := by
          nlinarith only [hlog_nn, hL10]
        have hstep3 := mul_le_mul_of_nonneg_left (hL32.trans hsqrt_logm) hc.le
        rw [hstep1] at hstep3
        have hstep4 : (C_s + 3) * Real.log w + Real.log (128000 * C_pnt + 128000 * 6 + 1) * Real.log w ≤
            (C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1) + 10 * c) * Real.log w := by
          nlinarith only [hL10, hc]
        calc
          Real.log (128000 * C_pnt) + (C_s + 3) * Real.log w
              ≤ Real.log (128000 * C_pnt + 128000 * 6 + 1) + (C_s + 3) * Real.log w := by
            linarith only [hlog_le1]
          _ ≤ (C_s + 3) * Real.log w + Real.log (128000 * C_pnt + 128000 * 6 + 1) * Real.log w := by
            linarith only [hstep2]
          _ ≤ (C_s + 5 + Real.log (128000 * C_pnt + 128000 * 6 + 1) + 10 * c) * Real.log w := hstep4
          _ ≤ c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2) := hstep3
      have hexp_eq : 128000 * C_pnt * w ^ (C_s + 3) * Real.exp (-c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) =
          Real.exp (Real.log (128000 * C_pnt) + (C_s + 3) * Real.log w - c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log (by positivity), Real.rpow_def_of_pos hw0,
          neg_mul, Real.exp_neg, div_eq_mul_inv, mul_comm (C_s + 3)]
        ring
      have hle1 : Real.exp (Real.log (128000 * C_pnt) + (C_s + 3) * Real.log w -
          c * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hK_ge])
      linarith only [hexp_eq, hle1]
    have hsqrt_b : 2 * Real.log ((m : ℝ) ^ (3 : ℝ)) / √(m : ℝ) ≤ 1 / (64000 * w ^ (C_s + 3)) := by
      rw [Real.log_rpow hm_pos, div_le_div_iff₀ (Real.sqrt_pos.mpr hm_pos) (by positivity)]
      have h1 : 384000 * Real.log (m : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := hT2 (m : ℝ) hm_T2
      have h2 : w ^ (C_s + 3) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := by
        have h3 : (C_s + 3) * Real.log w ≤ (1 / 4 : ℝ) * Real.log (m : ℝ) := by
          nlinarith only [hL50, hL10, hL_sq, hL_cu, hlogm_ge, hlog2_pos]
        rw [Real.rpow_def_of_pos hw0, Real.rpow_def_of_pos hm_pos]
        exact Real.exp_le_exp.mpr (by linarith only [h3])
      have h3 : (m : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) = √(m : ℝ) := by
        rw [← Real.rpow_add hm_pos, Real.sqrt_eq_rpow]; norm_num
      have hprod := mul_le_mul h1 h2 (Real.rpow_nonneg hw0.le _) (Real.rpow_nonneg hm_pos.le _)
      rw [h3] at hprod
      linarith only [hprod]
    have hloss_b : 24 * Real.log (m : ℝ) ≤ (1 / 2000 : ℝ) * (m : ℝ) := by
      have := hT1 (m : ℝ) hm_T1; linarith only [this]
    have h4w8 : 4 * w ^ (-(8 : ℝ)) ≤ 1 / 2000 := by
      rw [Real.rpow_neg hw0.le, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h8k : (8000 : ℝ) ≤ w ^ 8 := by
        have h3 : (1 : ℝ) ≤ w ^ 7 := one_le_pow₀ hw1
        have h4 : w ^ 8 = w * w ^ 7 := by ring
        nlinarith only [hw, h3, h4]
      rw [mul_inv_le_iff₀ (pow_pos hw0 8)]
      linarith only [h8k]
    have hm203_ge : (2000 : ℝ) ≤ (m : ℝ) ^ (203 / 100 : ℝ) := by
      have h1 : (m : ℝ) ≤ (m : ℝ) ^ (203 / 100 : ℝ) := by
        nth_rw 1 [← Real.rpow_one (m : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hm_1e5]) (by norm_num)
      linarith only [h1, hm_1e5]
    refine ⟨by exact_mod_cast (by linarith only [hm_1e5] : (3 : ℝ) ≤ m), hm_X0, hwC_lt, h2wC, h2w_le,
      hpnt_b, hsqrt_b, hloss_b, ?_⟩
    nlinarith only [h4w8, hm203_ge]
  obtain ⟨W, hW⟩ := eventually_atTop.mp hall
  exact ⟨max 16000 W, le_max_left _ _, fun w hw => (hW w ((le_max_right _ _).trans hw)).2⟩

/- ### Part 6: Subbin hypothetical lower bound and main theorem -/

lemma subbin_hypothetical_lower
    {c_p C_p X₀ C w Ri step : ℝ} {Y m q : ℕ} {a : ℕ → ℕ} {r : ℚ}
    (hcp_pos : 0 < c_p) (hCp_pos : 0 < C_p) (hX₀ : 3 ≤ X₀)
    (hPNT : ∀ u : ℝ, X₀ ≤ u → |Chebyshev.psi u - u| ≤ C_p * u * Real.exp (-c_p * (Real.log u) ^ ((1 : ℝ) / 2)))
    (hEuler_m : ∀ E : Finset ℕ, E ⊆ (range m).filter Nat.Prime →
      (939 / 1000 : ℝ) * Real.log m * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) ≤
      ∑ d0 ∈ (Icc 1 ⌊(m : ℝ) ^ (95 / 100 : ℝ)⌋₊).filter (fun d0 => d0.primeFactors ⊆ E),
        (∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹)) / (d0 : ℝ))
    (hTag_sub : ∀ (B : ℤ) (S : Finset ℕ) (ρ : ∀ u : ℕ, ZMod u),
      IsUnit (r.num : ZMod r.den) → IsUnit (B : ZMod r.den) →
      (∀ u ∈ S, u.Prime ∧ u < m ∧ ¬ u ∣ r.den ∧ ρ u ≠ 0) →
      let Ji := Nat.primesLE ⌊Ri + step⌋₊ \ Nat.primesLE ⌊Ri⌋₊
      (19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ)) * (∏ u ∈ S, (1 - ((u : ℝ) - 1)⁻¹)) ≤
      ((Ji.filter fun p : ℕ => (r.den : ℤ) ∣ r.num + B * (p : ℤ) ∧
        (∀ u ∈ r.den.primeFactors, (((r.num + B * (p : ℤ)) / (r.den : ℤ)) : ZMod u) ≠ (a u : ZMod u)) ∧
        (∀ u ∈ S, (p : ZMod u) ≠ ρ u)).card : ℝ))
    (hC : 0 ≤ C) (hw16 : 16000 ≤ w)
    (hm_pr : m.Prime) (hm3 : 3 ≤ m) (hm_X0 : X₀ ≤ (m : ℝ))
    (hD_lt_m : r.den < m) (h2wC : 2 * w ^ (C + 2) ≤ (m : ℝ) ^ (1 / 50 : ℝ))
    (h2w_le : 2 * w ≤ (m : ℝ) ^ (8 / 100 : ℝ))
    (hpnt_err : 2 * C_p * Real.exp (-c_p * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 1 / (64000 * w ^ (C + 3)))
    (hsqrt_err : 2 * Real.log ((m : ℝ) ^ (3 : ℝ)) / √(m : ℝ) ≤ 1 / (64000 * w ^ (C + 3)))
    (hloss_err : 24 * Real.log (m : ℝ) ≤ (1 / 2000 : ℝ) * (m : ℝ))
    (hlen_cut : (999 / 1000 : ℝ) * (m : ℝ) ^ (203 / 100 : ℝ) ≤
      (1 - 4 * w ^ (-(8 : ℝ))) * (m : ℝ) ^ (203 / 100 : ℝ) - 1)
    (hY_pos : 0 < Y) (hq_pos : 0 < q) (hRi_pos : 0 < Ri) (hstep_pos : 0 < step)
    (hV_hi : step / Ri ≤ w ^ (-(2 * C + 10)))
    (hden_le : (r.den : ℝ) ≤ w ^ C) (hnum_le : |(r.num : ℝ)| ≤ (Y : ℝ) * w ^ (C + 2))
    (hs0_lo : 203 / 100 ≤ Real.log ((Y : ℝ) / (Ri * q)) / Real.log (m : ℝ))
    (hs0_hi : Real.log ((Y : ℝ) / (Ri * q)) / Real.log (m : ℝ) ≤ 219 / 100)
    (hq_al : ∀ u ∈ q.primeFactors, m ≤ u ∧ (r.den : ZMod u) * (a u : ZMod u) = (r.num : ZMod u))
    (hJi_geom : ∀ p ∈ Nat.primesLE ⌊Ri + step⌋₊ \ Nat.primesLE ⌊Ri⌋₊,
      m ≤ p ∧ r.den.Coprime p) :
    let Ji := Nat.primesLE ⌊Ri + step⌋₊ \ Nat.primesLE ⌊Ri⌋₊
    let small := (range m).filter Nat.Prime
    let hypA := fun p u : ℕ => if u = p then ((r.den : ZMod p)⁻¹ * (r.num : ZMod p)).val else a u
    let Tp := fun p : ℕ =>
      (((Icc 1 Y).filter fun n =>
        (∀ u ∈ (p * q).primeFactors, n ≡ hypA p u [MOD u]) ∧
        ∀ u ∈ small, ¬ (n ≡ hypA p u [MOD u])).card : ℝ)
    (39 / 100 : ℝ) * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) *
      ((Ji.card : ℝ) * ((Y : ℝ) / (Ri * q))) ≤ ∑ p ∈ Ji, Tp p := by
  intro Ji small hypA Tp
  have hw0 : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hY_rpos : (0 : ℝ) < Y := by exact_mod_cast hY_pos
  have hq_rpos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hm_rpos : (0 : ℝ) < m := by exact_mod_cast hm_pr.pos
  have hm1_lt : (1 : ℝ) < m := by exact_mod_cast hm_pr.one_lt
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm1_lt
  have hV_nn : 0 ≤ ∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹) := prod_one_sub_inv_primesLE_nonneg m
  let J0 := (Y : ℝ) / (Ri * q)
  let s0 := Real.log J0 / Real.log (m : ℝ)
  have hJ0_pos : 0 < J0 := div_pos hY_rpos (mul_pos hRi_pos hq_rpos)
  have hJ0_eq : (m : ℝ) ^ s0 = J0 := by
    dsimp [s0]; rw [Real.rpow_def_of_pos hm_rpos, mul_div_cancel₀ _ hlogm.ne', Real.exp_log hJ0_pos]
  let x0 := max (-(r.num : ℝ) / q / Ri) (-(r.num : ℝ) / q / (Ri + step)) + 1
  let y0 := min (((r.den : ℝ) * Y - r.num) / q / Ri) (((r.den : ℝ) * Y - r.num) / q / (Ri + step))
  have hwidth : Ri + step ≤ (1 + w ^ (-(2 * C + 10))) * Ri := by
    have := (div_le_iff₀ hRi_pos).mp hV_hi; linarith
  have hD1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hD_rpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hLH := common_length_and_height hD1 hY_rpos hq_rpos hRi_pos (by linarith)
    (Real.rpow_nonneg hw0.le _) (Real.rpow_nonneg hw0.le _) hwidth hnum_le
  have h2e : 2 * w ^ (-(2 * C + 10)) * (1 + w ^ (C + 2)) ≤ 4 * w ^ (-(8 : ℝ)) := by
    have h1 : 1 ≤ w ^ (C + 2) := Real.one_le_rpow hw1 (by linarith only [hC])
    have hmul : w ^ (-(2 * C + 10)) * w ^ (C + 2) = w ^ (-C - 8) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    have hle8 : w ^ (-C - 8) ≤ w ^ (-(8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hw1 (by linarith only [hC])
    have hnn : 0 ≤ w ^ (-(2 * C + 10)) := Real.rpow_nonneg hw0.le _
    have h2 : w ^ (-(2 * C + 10)) ≤ w ^ (-(2 * C + 10)) * w ^ (C + 2) := by
      nlinarith only [h1, hnn]
    linarith only [hmul, hle8, h2]
  have hlen_lower : (999 / 1000 : ℝ) * (r.den : ℝ) * J0 ≤ y0 - x0 := by
    have hJ0_ge203 : (m : ℝ) ^ (203 / 100 : ℝ) ≤ J0 := by
      rw [← hJ0_eq]; exact Real.rpow_le_rpow_of_exponent_le hm1_lt.le hs0_lo
    have hDJ0_ge : (m : ℝ) ^ (203 / 100 : ℝ) ≤ (r.den : ℝ) * J0 := by
      nlinarith only [hD1, hJ0_ge203, hJ0_pos]
    have hstep1 : (1 - 4 * w ^ (-(8 : ℝ))) * ((r.den : ℝ) * J0) - 1 ≤ y0 - x0 := by
      have hL1 := hLH.1
      dsimp [x0, y0, J0] at hL1 ⊢
      have hDJ_pos : 0 < (r.den : ℝ) * ((Y : ℝ) / (Ri * q)) := mul_pos hD_rpos hJ0_pos
      nlinarith only [hL1, h2e, hDJ_pos]
    have h4w_lt : 0 ≤ (1 - 4 * w ^ (-(8 : ℝ))) - 999 / 1000 := by
      have hp203 : 0 < (m : ℝ) ^ (203 / 100 : ℝ) := Real.rpow_pos_of_pos hm_rpos _
      nlinarith only [hlen_cut, hp203]
    have hdiff := mul_le_mul_of_nonneg_left hDJ0_ge h4w_lt
    linarith only [hstep1, hlen_cut, hdiff]
  have hH_half : (m : ℝ) ^ s0 / 2 ≤ y0 - x0 := by
    rw [hJ0_eq]; nlinarith only [hlen_lower, hD1, hJ0_pos]
  have hMax_xy : max |x0| |y0| ≤ 2 * w ^ (C + 2) * (m : ℝ) ^ s0 := by
    have hxy : x0 ≤ y0 := by linarith only [hH_half, Real.rpow_pos_of_pos hm_rpos s0]
    have h2 := hLH.2 hxy
    have h1_le : (1 : ℝ) ≤ ((1 / 2 : ℝ) * w ^ (C + 2)) * J0 := by
      have hwC2 : 1 ≤ w ^ (C + 2) := Real.one_le_rpow hw1 (by linarith only [hC])
      have hJ2 : 2 ≤ J0 := by
        rw [← hJ0_eq]
        have hms1 : (m : ℝ) ≤ (m : ℝ) ^ s0 := by
          nth_rw 1 [← Real.rpow_one (m : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le hm1_lt.le (by linarith only [hs0_lo])
        have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
        linarith only [hms1, hm3r]
      nlinarith only [hwC2, hJ2]
    have hDw : (r.den : ℝ) ≤ (1 / 2 : ℝ) * w ^ (C + 2) := by
      have h1 : w ^ C * 2 ≤ w ^ (C + 2) := by
        have heq : w ^ (C + 2) = w ^ C * w ^ (2 : ℝ) := Real.rpow_add hw0 C 2
        rw [heq, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hwsq : (2 : ℝ) ≤ w ^ 2 := by nlinarith only [hw16]
        exact mul_le_mul_of_nonneg_left hwsq (Real.rpow_pos_of_pos hw0 C).le
      linarith only [hden_le, h1]
    rw [hJ0_eq]
    dsimp [x0, y0, J0] at h2 ⊢
    nlinarith only [h2, h1_le, hDw, hJ0_pos]
  let E := small.filter (fun u => ¬ u ∣ r.den ∧ (r.den : ZMod u) * (a u : ZMod u) ≠ (r.num : ZMod u))
  let Dset := (Icc 1 ⌊(m : ℝ) ^ (95 / 100 : ℝ)⌋₊).filter (fun d0 => d0.primeFactors ⊆ E)
  let Mset := fun d0 : ℕ =>
    (Finset.Icc ⌊x0⌋ ⌈y0⌉).filter (fun z : ℤ => x0 < (z : ℝ) ∧ (z : ℝ) < y0 ∧
      ∃ ell : ℕ, ell.Prime ∧ m < ell ∧ z.natAbs = d0 * ell)
  let good := fun p : ℕ => fun z : ℤ =>
    (r.den : ℤ) ∣ r.num + ((q : ℤ) * z) * (p : ℤ) ∧
    ∀ u ∈ small, ¬ ((((r.num + (p : ℤ) * (q : ℤ) * z) / (r.den : ℤ)).toNat) ≡ a u [MOD u])
  have hM_disj : (Dset : Set ℕ).PairwiseDisjoint Mset := by
    intro d1 _ d2 hd2 hne
    have h2 := Finset.mem_filter.mp hd2
    exact prime_multiple_disjoint_sets (Finset.mem_Icc.mp h2.1).1
      (fun u hu => Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (h2.2 hu)).1).1) hne
  have hpairs_le : ∑ d0 ∈ Dset, ∑ z ∈ Mset d0, ((Ji.filter (fun p => good p z)).card : ℝ) ≤
      ∑ p ∈ Ji, Tp p := by
    have hswap : ∑ d0 ∈ Dset, ∑ z ∈ Mset d0, (Ji.filter (fun p => good p z)).card =
        ∑ p ∈ Ji, ((Dset.biUnion Mset).filter (fun z => good p z)).card := by
      rw [← Finset.sum_biUnion hM_disj]
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hnat : ∑ d0 ∈ Dset, ∑ z ∈ Mset d0, (Ji.filter (fun p => good p z)).card ≤
        ∑ p ∈ Ji, ((Icc 1 Y).filter fun n =>
          (∀ u ∈ (p * q).primeFactors, n ≡ hypA p u [MOD u]) ∧
          ∀ u ∈ small, ¬ (n ≡ hypA p u [MOD u])).card := by
      rw [hswap]
      apply Finset.sum_le_sum
      intro p hp
      have hp_b := (mem_primeDiff_iff hRi_pos.le (by positivity) p).mp hp
      have hp_pr : p.Prime := hp_b.1
      let f : ℤ → ℕ := fun z => ((r.num + (p : ℤ) * (q : ℤ) * z) / (r.den : ℤ)).toNat
      apply Finset.card_le_card_of_injOn f
      · intro z hz
        obtain ⟨hzM, hgood⟩ := Finset.mem_filter.mp hz
        obtain ⟨d0, _, hzd0⟩ := Finset.mem_biUnion.mp hzM
        obtain ⟨_, hzlo, hzhi, _⟩ := Finset.mem_filter.mp hzd0
        have hdiv' : (r.den : ℤ) ∣ r.num + (p : ℤ) * (q : ℤ) * z := by
          convert hgood.1 using 1; ring
        obtain ⟨hn1, hnY, hneq⟩ := common_integer_decode r.den_pos hq_pos hRi_pos
          hp_b.2.1.le hp_b.2.2 hzlo.le hzhi.le hdiv'
        have hcongr := hypothetical_modulus_congr hp_pr hq_pos
          (hJi_geom p hp).2 hD_lt_m hq_al hneq
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnY⟩, hcongr, ?_⟩
        intro u hu
        have hu_lt : u < m := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
        have hup : u ≠ p := by have := (hJi_geom p hp).1; omega
        simpa only [hypA, hup, ite_false] using hgood.2 u hu
      · intro z1 hz1 z2 hz2 hf
        obtain ⟨hz1M, hg1⟩ := Finset.mem_filter.mp hz1
        obtain ⟨hz2M, hg2⟩ := Finset.mem_filter.mp hz2
        obtain ⟨d1, _, hzd1⟩ := Finset.mem_biUnion.mp hz1M
        obtain ⟨d2, _, hzd2⟩ := Finset.mem_biUnion.mp hz2M
        have h1 := Finset.mem_filter.mp hzd1
        have h2 := Finset.mem_filter.mp hzd2
        have hdiv1 : (r.den : ℤ) ∣ r.num + (p : ℤ) * (q : ℤ) * z1 := by
          convert hg1.1 using 1; ring
        have hdiv2 : (r.den : ℤ) ∣ r.num + (p : ℤ) * (q : ℤ) * z2 := by
          convert hg2.1 using 1; ring
        have heq1 := (common_integer_decode r.den_pos hq_pos hRi_pos hp_b.2.1.le hp_b.2.2
          h1.2.1.le h1.2.2.1.le hdiv1).2.2
        have heq2 := (common_integer_decode r.den_pos hq_pos hRi_pos hp_b.2.1.le hp_b.2.2
          h2.2.1.le h2.2.2.1.le hdiv2).2.2
        have hf' : (f z1 : ℤ) = (f z2 : ℤ) := by exact_mod_cast hf
        have hmul : (p : ℤ) * (q : ℤ) * z1 = (p : ℤ) * (q : ℤ) * z2 := by
          dsimp [f] at hf'
          rw [hf'] at heq1
          linarith only [heq1, heq2]
        have hpq_ne : (p : ℤ) * (q : ℤ) ≠ 0 := by
          exact mul_ne_zero (by exact_mod_cast hp_pr.ne_zero) (by exact_mod_cast hq_pos.ne')
        exact mul_left_cancel₀ hpq_ne hmul
    simpa only [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hnat
  have hterm_lower : ∀ d0 ∈ Dset, ∀ z ∈ Mset d0,
      (19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ)) *
        (∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹)) ≤
      ((Ji.filter (fun p => good p z)).card : ℝ) := by
    intro d0 hd0 z hz
    obtain ⟨hd0_I, hd0_supp⟩ := Finset.mem_filter.mp hd0
    have hd0_pos : 0 < d0 := (Finset.mem_Icc.mp hd0_I).1
    obtain ⟨_, hzlo, hzhi, ell, hell_pr, hell_gt, hz_abs⟩ := Finset.mem_filter.mp hz
    let B : ℤ := (q : ℤ) * z
    have hA_unit : IsUnit (r.num : ZMod r.den) := isUnit_intCast_of_coprime r.reduced
    have hB_cop : B.natAbs.Coprime r.den := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨u, hu_pr, hu_dvd⟩ := Nat.exists_prime_and_dvd hne
      have hu_B : u ∣ B.natAbs := hu_dvd.trans (Nat.gcd_dvd_left _ _)
      have hu_D : u ∣ r.den := hu_dvd.trans (Nat.gcd_dvd_right _ _)
      have hu_lt_m : u < m := (Nat.le_of_dvd r.den_pos hu_D).trans_lt hD_lt_m
      have hB_abs : B.natAbs = q * (d0 * ell) := by
        dsimp [B]; rw [Int.natAbs_mul, Int.natAbs_natCast, hz_abs]
      rw [hB_abs] at hu_B
      rcases hu_pr.dvd_mul.mp hu_B with hu_q | hu_de
      · have := (hq_al u (Nat.mem_primeFactors.mpr ⟨hu_pr, hu_q, hq_pos.ne'⟩)).1
        omega
      · rcases hu_pr.dvd_mul.mp hu_de with hu_d0 | hu_ell
        · have hE := hd0_supp (Nat.mem_primeFactors.mpr ⟨hu_pr, hu_d0, hd0_pos.ne'⟩)
          exact (Finset.mem_filter.mp hE).2.1 hu_D
        · rcases hell_pr.eq_one_or_self_of_dvd u hu_ell with h1 | h2
          · exact hu_pr.ne_one h1
          · omega
    have hB_unit : IsUnit (B : ZMod r.den) := isUnit_intCast_of_coprime hB_cop
    let S := E.filter (fun u => ¬ u ∣ d0)
    let ρ : ∀ u : ℕ, ZMod u := fun u =>
      (B : ZMod u)⁻¹ * ((r.den : ZMod u) * (a u : ZMod u) - (r.num : ZMod u))
    have hS_spec : ∀ u ∈ S, u.Prime ∧ u < m ∧ ¬ u ∣ r.den ∧ ρ u ≠ 0 := by
      intro u hu
      obtain ⟨huE, hu_nd0⟩ := Finset.mem_filter.mp hu
      obtain ⟨hu_sm, hu_nD, hu_nal⟩ := Finset.mem_filter.mp huE
      obtain ⟨hu_lt, hu_pr⟩ := Finset.mem_filter.mp hu_sm
      rw [Finset.mem_range] at hu_lt
      let _ : Fact u.Prime := ⟨hu_pr⟩
      refine ⟨hu_pr, hu_lt, hu_nD, ?_⟩
      apply mul_ne_zero
      · apply inv_ne_zero
        intro hBz
        have hu_B : u ∣ B.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd B u).mp hBz)
        have hB_abs : B.natAbs = q * (d0 * ell) := by
          dsimp [B]; rw [Int.natAbs_mul, Int.natAbs_natCast, hz_abs]
        rw [hB_abs] at hu_B
        rcases hu_pr.dvd_mul.mp hu_B with hu_q | hu_de
        · have := (hq_al u (Nat.mem_primeFactors.mpr ⟨hu_pr, hu_q, hq_pos.ne'⟩)).1; omega
        · rcases hu_pr.dvd_mul.mp hu_de with hu_d0 | hu_ell
          · exact hu_nd0 hu_d0
          · rcases hell_pr.eq_one_or_self_of_dvd u hu_ell with h1 | h2
            · exact hu_pr.ne_one h1
            · omega
      · exact sub_ne_zero.mpr hu_nal
    have htag_call := hTag_sub B S ρ hA_unit hB_unit hS_spec
    refine htag_call.trans ?_
    exact_mod_cast Finset.card_le_card (fun p hp => by
      obtain ⟨hpJi, hdivp, hD_av, hS_av⟩ := Finset.mem_filter.mp hp
      have hp_b := (mem_primeDiff_iff hRi_pos.le (by positivity) p).mp hpJi
      have hdiv' : (r.den : ℤ) ∣ r.num + (p : ℤ) * (q : ℤ) * z := by
        convert hdivp using 1; dsimp [B]; ring
      have hn_eq := (common_integer_decode r.den_pos hq_pos hRi_pos hp_b.2.1.le hp_b.2.2
        hzlo.le hzhi.le hdiv').2.2
      refine Finset.mem_filter.mpr ⟨hpJi, hdivp, ?_⟩
      exact actual_avoidance_from_tag (fun u hu => (hq_al u hu).1) hq_pos
        hp_b.1 (hJi_geom p hpJi).1 hell_pr hell_gt hz_abs hd0_pos hd0_supp hD_av
        (fun u hu => by simpa only [B, ρ, Int.cast_mul, Int.cast_natCast] using hS_av u hu) hn_eq)
  have hsum_d0 :
      ((999 / 1000 : ℝ) * (y0 - x0) / ((s0 + 1 / 50) * Real.log m)) *
      ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ))) *
      (∑ d0 ∈ Dset, (∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹)) / (d0 : ℝ)) ≤
      ∑ d0 ∈ Dset, ∑ z ∈ Mset d0, ((Ji.filter (fun p => good p z)).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d0 hd0
    have hd0_I := (Finset.mem_filter.mp hd0).1
    have hd0_pos : 0 < d0 := (Finset.mem_Icc.mp hd0_I).1
    have hd0_le : (d0 : ℝ) ≤ (m : ℝ) ^ (95 / 100 : ℝ) :=
      (Nat.le_floor_iff (Real.rpow_nonneg hm_rpos.le _)).mp (Finset.mem_Icc.mp hd0_I).2
    have hM_lo := prime_multiples_card_lower hcp_pos hCp_pos hX₀ hPNT hw16 hm3 hm_X0
      hs0_lo hs0_hi h2wC h2w_le hpnt_err hsqrt_err hloss_err hH_half hMax_xy hd0_pos hd0_le
    have hW_nn : 0 ≤ ∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹) := by
      apply Finset.prod_nonneg
      intro u hu
      have hu_pr : u.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1).2
      have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu_pr.two_le
      have : ((u : ℝ) - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      linarith
    calc
      _ = ((999 / 1000 : ℝ) * (y0 - x0) / ((d0 : ℝ) * (s0 + 1 / 50) * Real.log m)) *
          ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ)) *
            (∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ ((Mset d0).card : ℝ) *
          ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ)) *
            (∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹))) :=
        mul_le_mul_of_nonneg_right hM_lo (by positivity)
      _ = ∑ _z ∈ Mset d0, (19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ)) *
            (∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun z hz => hterm_lower d0 hd0 z hz)
  have hE_lo := hEuler_m E (Finset.filter_subset _ _)
  have hcoeff_39 : (39 / 100 : ℝ) ≤
      (999 / 1000 : ℝ) * (999 / 1000 : ℝ) * (19 / 20 : ℝ) * (939 / 1000 : ℝ) / (221 / 100 : ℝ) := by
    norm_num
  have hchain : (39 / 100 : ℝ) * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) *
      ((Ji.card : ℝ) * J0) ≤
      ((999 / 1000 : ℝ) * (y0 - x0) / ((s0 + 1 / 50) * Real.log m)) *
      ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ))) *
      (∑ d0 ∈ Dset, (∏ u ∈ E.filter (fun u => ¬ u ∣ d0), (1 - ((u : ℝ) - 1)⁻¹)) / (d0 : ℝ)) := by
    have hs0_pos : 0 < s0 + 1 / 50 := by linarith only [hs0_lo]
    have hstep1 : (39 / 100 : ℝ) * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) *
        ((Ji.card : ℝ) * J0) ≤
        ((999 / 1000 : ℝ) * (999 / 1000 : ℝ) * (19 / 20 : ℝ) * (939 / 1000 : ℝ) / (s0 + 1 / 50)) *
        (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) * ((Ji.card : ℝ) * J0) := by
      have hs_div : (999 / 1000 : ℝ) * (999 / 1000 : ℝ) * (19 / 20 : ℝ) * (939 / 1000 : ℝ) / (221 / 100 : ℝ) ≤
          (999 / 1000 : ℝ) * (999 / 1000 : ℝ) * (19 / 20 : ℝ) * (939 / 1000 : ℝ) / (s0 + 1 / 50) :=
        div_le_div_of_nonneg_left (by norm_num) hs0_pos (by linarith only [hs0_hi])
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcoeff_39.trans hs_div) hV_nn)
        (mul_nonneg (Nat.cast_nonneg _) hJ0_pos.le)
    have hstep2 : ((999 / 1000 : ℝ) * (999 / 1000 : ℝ) * (19 / 20 : ℝ) * (939 / 1000 : ℝ) / (s0 + 1 / 50)) *
        (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) * ((Ji.card : ℝ) * J0) =
        ((999 / 1000 : ℝ) * ((999 / 1000 : ℝ) * (r.den : ℝ) * J0) / ((s0 + 1 / 50) * Real.log m)) *
        ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ))) *
        ((939 / 1000 : ℝ) * Real.log m * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹))) := by
      field_simp [hlogm.ne', hD_rpos.ne', hs0_pos.ne']
    rw [hstep2] at hstep1
    have hfac_nn : 0 ≤ (19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ)) :=
      mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) hD_rpos.le)
    have hden_nn : 0 ≤ (s0 + 1 / 50) * Real.log m := mul_nonneg hs0_pos.le hlogm.le
    have hstep3 : ((999 / 1000 : ℝ) * ((999 / 1000 : ℝ) * (r.den : ℝ) * J0) / ((s0 + 1 / 50) * Real.log m)) *
        ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ))) ≤
        ((999 / 1000 : ℝ) * (y0 - x0) / ((s0 + 1 / 50) * Real.log m)) *
        ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ hfac_nn
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlen_lower (by norm_num)) hden_nn
    have hyx_nn : 0 ≤ y0 - x0 := by linarith only [hH_half, Real.rpow_pos_of_pos hm_rpos s0]
    have hE_lhs_nn : 0 ≤ (939 / 1000 : ℝ) * Real.log m * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) :=
      mul_nonneg (mul_nonneg (by norm_num) hlogm.le) hV_nn
    have hL_rhs_nn : 0 ≤ ((999 / 1000 : ℝ) * (y0 - x0) / ((s0 + 1 / 50) * Real.log m)) *
        ((19 / 20 : ℝ) * ((Ji.card : ℝ) / (r.den : ℝ))) :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hyx_nn) hden_nn) hfac_nn
    exact hstep1.trans (mul_le_mul hstep3 hE_lo hE_lhs_nn hL_rhs_nn)
  exact hchain.trans (hsum_d0.trans hpairs_le)

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H4 := by
  intro hUpper hEuler hPNT hTag
  obtain ⟨C_U, hCU_pos, N1, _, hUpper⟩ := hUpper
  obtain ⟨N2, _, hEuler⟩ := hEuler
  obtain ⟨c_p, C_p, X₀, hcp_pos, hCp_pos, hX₀, hPNT⟩ := hPNT
  let d_eta : ℝ := min (1 / 4) (1 / (40 * C_U))
  have hd_pos : 0 < d_eta := lt_min (by norm_num) (by positivity)
  have hd_le : d_eta ≤ 1 / 4 := min_le_left _ _
  have hbudget : 2 * C_U * d_eta ≤ 1 / 20 := by
    have h1 := mul_le_mul_of_nonneg_left (min_le_right (1 / 4 : ℝ) (1 / (40 * C_U)))
      (show 0 ≤ 2 * C_U by positivity)
    have h2 : 2 * C_U * (1 / (40 * C_U)) = 1 / 20 := by field_simp; ring
    exact h1.trans_eq h2
  refine ⟨d_eta, hd_pos, hd_le, max N1 N2, ?_⟩
  intro C hC
  refine ⟨1, zero_lt_one, ?_⟩
  intro b x hb hx
  obtain ⟨W_tag, _, hTagB⟩ := hTag C b x hC (by linarith) hx
  obtain ⟨W_thr, hWthr, hThr⟩ := eventually_threshold_params c_p C_p X₀ C hcp_pos hCp_pos hC
  refine ⟨max W_tag W_thr, ?_⟩
  intro w hw Y a m q s t r
  dsimp only
  intro hh
  obtain ⟨hm_pr, hm_N, hm_lo, hm_hi, hs_lo, ht_lo, ht_hi, hY_pos, hq_pos,
    hden_le, hnum_le, hband, hq_al, hJ_geom, hnear⟩ := hh
  have hw_tag : W_tag ≤ w := (le_max_left _ _).trans hw
  have hw_thr : W_thr ≤ w := (le_max_right _ _).trans hw
  have hw16 : 16000 ≤ w := hWthr.trans hw_thr
  have hw0 : 0 < w := by linarith
  have hm_lo1 : Real.exp ((Real.log w) ^ 3) ≤ (m : ℝ) := by simpa using hm_lo
  have hm_hi1 : (m : ℝ) ≤ Real.exp (b * (Real.log w) ^ 3) := by simpa [mul_assoc] using hm_hi
  obtain ⟨hm3, hm_X0, hD_lt_mR, h2wC, h2w_le, hpnt_err, hsqrt_err, hloss_err, hlen_cut⟩ :=
    hThr w hw_thr m hm_lo1
  have hD_lt_m : r.den < m := by exact_mod_cast hden_le.trans_lt hD_lt_mR
  have hs_pos : 0 < s := (Real.exp_pos _).trans_le hs_lo
  have ht_pos : 0 < t := by linarith
  have hY_rpos : (0 : ℝ) < Y := by exact_mod_cast hY_pos
  have hq_rpos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hm_rpos : (0 : ℝ) < m := by exact_mod_cast hm_pr.pos
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm_pr.one_lt)
  have hV_nn : 0 ≤ ∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹) := prod_one_sub_inv_primesLE_nonneg m
  let J := Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊
  let A := fun p : ℕ => (r.den : ZMod p) * (a p : ZMod p) = (r.num : ZMod p)
  let G := J.filter A
  let small := (range m).filter Nat.Prime
  let hypA := fun p u : ℕ => if u = p then ((r.den : ZMod p)⁻¹ * (r.num : ZMod p)).val else a u
  let Tp := fun p : ℕ =>
    (((Icc 1 Y).filter fun n =>
      (∀ u ∈ (p * q).primeFactors, n ≡ hypA p u [MOD u]) ∧
      ∀ u ∈ small, ¬ (n ≡ hypA p u [MOD u])).card : ℝ)
  have hT_eq_on_G : ∀ p ∈ G, Tp p =
      (((Icc 1 Y).filter fun n =>
        (∀ u ∈ (p * q).primeFactors, n ≡ a u [MOD u]) ∧
        ∀ u ∈ small, ¬ (n ≡ a u [MOD u])).card : ℝ) := by
    intro p hp
    obtain ⟨hpJ, hpA⟩ := Finset.mem_filter.mp hp
    have hp_pr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hpJ).1).2
    have hcop_p : r.den.Coprime p := (hJ_geom p hpJ).2.2
    let _ : Fact p.Prime := ⟨hp_pr⟩
    have hD_ne : (r.den : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime _ _).mpr hcop_p).ne_zero
    have hap_p : hypA p p ≡ a p [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp only [hypA, ite_true, ZMod.natCast_val, ZMod.cast_id', id_eq]
      apply mul_left_cancel₀ hD_ne
      rw [← mul_assoc, mul_inv_cancel₀ hD_ne, one_mul, hpA]
    dsimp [Tp]
    congr 2
    apply Finset.filter_congr
    intro n _
    apply and_congr
    · apply forall₂_congr
      intro u _
      by_cases hup : u = p
      · subst hup
        exact ⟨fun h => h.trans hap_p, fun h => h.trans hap_p.symm⟩
      · simp [hypA, hup]
    · apply forall₂_congr
      intro u hu
      have hu_lt : u < m := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
      have hp_ge : m ≤ p := (hJ_geom p hpJ).1
      have hup : u ≠ p := by omega
      simp [hypA, hup]
  have hT_upper : ∀ p ∈ J, Tp p ≤ C_U * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) * ((Y : ℝ) / ((p : ℝ) * q)) := by
    intro p hpJ
    have hp_pr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hpJ).1).2
    have hp_bounds := (mem_primeDiff_iff hs_pos.le (by positivity) p).mp hpJ
    have hb_p := hband p ⟨hp_bounds.2.1.le, hp_bounds.2.2⟩
    have hJ_ge : (m : ℝ) ^ 2 ≤ (Y : ℝ) / ((p * q : ℕ) : ℝ) := by
      have h1 : 2 * Real.log (m : ℝ) ≤ Real.log ((Y : ℝ) / ((p : ℝ) * q)) := by
        have := (le_div_iff₀ hlogm).mp hb_p.1
        linarith
      have h2 := Real.exp_le_exp.mpr h1
      rw [Real.exp_log (div_pos hY_rpos (mul_pos (by exact_mod_cast hp_pr.pos) hq_rpos)),
        show 2 * Real.log (m : ℝ) = ((2 : ℕ) : ℝ) * Real.log (m : ℝ) by norm_num,
        ← Real.log_pow, Real.exp_log (pow_pos hm_rpos 2)] at h2
      simpa [Nat.cast_mul] using h2
    have hpf_ge : ∀ u ∈ (p * q).primeFactors, m ≤ u := by
      intro u hu
      have hu_pr := Nat.prime_of_mem_primeFactors hu
      rcases hu_pr.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hu) with hdivp | hdivq
      · rcases hp_pr.eq_one_or_self_of_dvd u hdivp with h1 | h2
        · exact absurd h1 hu_pr.ne_one
        · rw [h2]; exact (hJ_geom p hpJ).1
      · exact (hq_al u (Nat.mem_primeFactors.mpr ⟨hu_pr, hdivq, hq_pos.ne'⟩)).1
    have hu := hUpper m hm_pr ((le_max_left N1 N2).trans hm_N) Y (p * q) (hypA p)
      hY_pos (hJ_geom p hpJ).2.1 hpf_ge hJ_ge
    calc
      Tp p ≤ C_U * ((Y : ℝ) / ((p * q : ℕ) : ℝ)) * ∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹) := hu
      _ = _ := by push_cast; ring
  have hweight_range : 0 ≤ (Y : ℝ) / (((1 + t) * s) * q) ∧
      ∀ p ∈ J, (Y : ℝ) / (((1 + t) * s) * q) ≤ (Y : ℝ) / ((p : ℝ) * q) ∧
        (Y : ℝ) / ((p : ℝ) * q) ≤ 2 * ((Y : ℝ) / (((1 + t) * s) * q)) := by
    refine ⟨by positivity, ?_⟩
    intro p hpJ
    have hp_b := (mem_primeDiff_iff hs_pos.le (by positivity) p).mp hpJ
    have hp_pos : (0 : ℝ) < p := hs_pos.trans hp_b.2.1
    refine ⟨div_le_div_of_nonneg_left hY_rpos.le (mul_pos hp_pos hq_rpos)
      (mul_le_mul_of_nonneg_right hp_b.2.2 hq_rpos.le), ?_⟩
    calc
      (Y : ℝ) / ((p : ℝ) * q) ≤ (Y : ℝ) / (s * q) :=
        div_le_div_of_nonneg_left hY_rpos.le (mul_pos hs_pos hq_rpos)
          (mul_le_mul_of_nonneg_right hp_b.2.1.le hq_rpos.le)
      _ ≤ 2 * ((Y : ℝ) / (((1 + t) * s) * q)) := by
        rw [mul_div_assoc', div_le_div_iff₀ (mul_pos hs_pos hq_rpos) (by positivity)]
        have hsq_pos : 0 < s * q := mul_pos hs_pos hq_rpos
        have h1 : (1 + t) * s * q ≤ 2 * (s * q) := by nlinarith only [ht_hi, hsq_pos]
        nlinarith only [h1, hY_rpos]
  have hAll : (39 / 100 : ℝ) * (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹)) *
      (∑ p ∈ J, (Y : ℝ) / ((p : ℝ) * q)) ≤ ∑ p ∈ J, Tp p := by
    let M_bins := ⌈w ^ (2 * C + 10)⌉₊
    have hM_pos : 0 < M_bins := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hw0 _)
    let step := t * s / (M_bins : ℝ)
    let Ji := fun i : ℕ =>
      Nat.primesLE ⌊s + ((i : ℝ) + 1) * step⌋₊ \ Nat.primesLE ⌊s + (i : ℝ) * step⌋₊
    obtain ⟨hpart, hdisj⟩ := subbin_partition hs_pos ht_pos hM_pos
    have hJ_sum_w : ∑ p ∈ J, (Y : ℝ) / ((p : ℝ) * q) =
        ∑ i ∈ Finset.range M_bins, ∑ p ∈ Ji i, (Y : ℝ) / ((p : ℝ) * q) := by
      change ∑ p ∈ (Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊), _ = _
      rw [hpart, Finset.sum_biUnion hdisj]
    have hJ_sum_T : ∑ p ∈ J, Tp p = ∑ i ∈ Finset.range M_bins, ∑ p ∈ Ji i, Tp p := by
      change ∑ p ∈ (Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊), _ = _
      rw [hpart, Finset.sum_biUnion hdisj]
    rw [hJ_sum_w, hJ_sum_T, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi_lt : i < M_bins := Finset.mem_range.mp hi
    obtain ⟨_, hstep_pos, hRi_ge, hRi_end, hV_lo, hV_hi⟩ :=
      subbin_scale_bounds (by linarith) hC hx hs_pos ht_lo ht_hi i hi_lt
    let Ri := s + (i : ℝ) * step
    have hRi_pos : 0 < Ri := hs_pos.trans_le hRi_ge
    have hJi_eq : Ji i = Nat.primesLE ⌊Ri + step⌋₊ \ Nat.primesLE ⌊Ri⌋₊ := by
      dsimp [Ji, Ri]
      rw [show s + ((i : ℝ) + 1) * step = s + (i : ℝ) * step + step by ring]
    have hband_i := hband Ri ⟨hRi_ge, by linarith⟩
    have hw_sub : ∑ p ∈ Ji i, (Y : ℝ) / ((p : ℝ) * q) ≤ ((Ji i).card : ℝ) * ((Y : ℝ) / (Ri * q)) := by
      calc
        ∑ p ∈ Ji i, (Y : ℝ) / ((p : ℝ) * q) ≤ ∑ _p ∈ Ji i, (Y : ℝ) / (Ri * q) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [hJi_eq, mem_primeDiff_iff hRi_pos.le (by positivity)] at hp
          exact div_le_div_of_nonneg_left hY_rpos.le (mul_pos hRi_pos hq_rpos)
            (mul_le_mul_of_nonneg_right hp.2.1.le hq_rpos.le)
        _ = ((Ji i).card : ℝ) * ((Y : ℝ) / (Ri * q)) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hsub := subbin_hypothetical_lower
      hcp_pos hCp_pos hX₀ hPNT (hEuler m hm_pr ((le_max_right N1 N2).trans hm_N))
      (fun B S ρ hAu hBu hSs => hTagB w hw_tag m Ri step hm3 hm_hi1 (hs_lo.trans hRi_ge) hV_lo hV_hi
        r.den r.num B a r.den_pos hden_le hAu hBu S ρ hSs)
      hC hw16 hm_pr hm3 hm_X0 hD_lt_m h2wC h2w_le hpnt_err hsqrt_err hloss_err hlen_cut
      hY_pos hq_pos hRi_pos hstep_pos hV_hi hden_le hnum_le hband_i.1 hband_i.2 hq_al
      (fun p hp => by
        have hpJ : p ∈ J := by
          change p ∈ Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊
          rw [hpart]; exact Finset.mem_biUnion.mpr ⟨i, hi, by change p ∈ Ji i; rwa [hJi_eq]⟩
        exact ⟨(hJ_geom p hpJ).1, (hJ_geom p hpJ).2.2⟩)
    rw [← hJi_eq] at hsub
    exact (mul_le_mul_of_nonneg_left hw_sub (by positivity)).trans hsub
  have hG_lower := near_full_owner_lower J G (Finset.filter_subset _ _)
    (fun p => (Y : ℝ) / ((p : ℝ) * q)) Tp
    ((Y : ℝ) / (((1 + t) * s) * q)) d_eta C_U (∏ u ∈ Nat.primesLE m, (1 - (u : ℝ)⁻¹))
    hweight_range.1 hd_pos.le hCU_pos.le hV_nn hnear hweight_range.2 hAll hT_upper hbudget
  rw [Finset.sum_congr rfl hT_eq_on_G] at hG_lower
  simpa only [mul_assoc] using hG_lower

end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1_H4_R1
