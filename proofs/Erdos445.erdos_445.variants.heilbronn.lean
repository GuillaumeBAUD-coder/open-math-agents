import FormalConjectures.ErdosProblems.«445»

-- Problem: Erdős Problem 445 — heilbronn
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/445.lean:62 (declaration Erdos445.erdos_445.variants.heilbronn)
-- Credit: @NoahPuckett-IO (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Method: Kloosterman fourth moment bound (|K| <= (10 p^3)^(1/4)) plus Fourier counting of
-- inverse pairs in a smoothed interval; gives the statement with c0 = 9/10.

namespace OMA.Heil

open Finset

variable {p : ℕ} [Fact p.Prime]

noncomputable abbrev ψ (p : ℕ) [Fact p.Prime] : AddChar (ZMod p) ℂ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ZMod.stdAddChar

lemma prim : (ψ p).IsPrimitive := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ZMod.isPrimitive_stdAddChar p

lemma orth (b : ZMod p) : ∑ x : ZMod p, ψ p (x * b) = if b = 0 then (p : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b prim, ZMod.card]
  split_ifs <;> simp

lemma orth' (b : ZMod p) : ∑ x : ZMod p, ψ p (b * x) = if b = 0 then (p : ℂ) else 0 := by
  simp_rw [mul_comm b]; exact orth b

noncomputable def K (a b : ZMod p) : ℂ := ∑ x : ZMod p, ψ p (a * x + b * x⁻¹)

lemma K_zero_zero : K (p := p) 0 0 = p := by
  simp [K, ZMod.card]

lemma K_zero_left (b : ZMod p) (hb : b ≠ 0) : K 0 b = 0 := by
  unfold K
  simp only [zero_mul, zero_add]
  rw [show (∑ x : ZMod p, ψ p (b * x⁻¹)) = ∑ x : ZMod p, ψ p (b * x) from
    Fintype.sum_equiv (Equiv.inv (ZMod p)) _ _ (fun x => rfl)]
  rw [orth', if_neg hb]

lemma K_zero_right (a : ZMod p) (ha : a ≠ 0) : K a 0 = 0 := by
  unfold K
  simp only [zero_mul, add_zero]
  rw [orth', if_neg ha]

lemma K_scale (a b : ZMod p) (ha : a ≠ 0) : K a b = K 1 (a * b) := by
  unfold K
  refine (Fintype.sum_equiv (Equiv.mulLeft₀ a⁻¹ (inv_ne_zero ha)) _ _ (fun y => ?_)).symm
  have e : (Equiv.mulLeft₀ a⁻¹ (inv_ne_zero ha)) y = a⁻¹ * y := rfl
  rw [e]
  congr 1
  rw [mul_inv_rev, inv_inv]
  field_simp

/-- sum of pair -/
def sP (X : ZMod p × ZMod p) : ZMod p := X.1 + X.2
/-- sum of inverses of pair -/
def tP (X : ZMod p × ZMod p) : ZMod p := X.1⁻¹ + X.2⁻¹

lemma K_sq (a b : ZMod p) :
    K a b ^ 2 = ∑ X : ZMod p × ZMod p, ψ p (a * sP X + b * tP X) := by
  rw [sq, K, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [sP, tP]
  ring

lemma conj_K_sq (a b : ZMod p) :
    (starRingEnd ℂ) (K a b) ^ 2 = ∑ X : ZMod p × ZMod p, ψ p (-(a * sP X + b * tP X)) := by
  rw [← map_pow, K_sq, map_sum]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [AddChar.map_neg_eq_conj]

lemma moment_eq :
    ∑ a : ZMod p, ∑ b : ZMod p, K a b ^ 2 * (starRingEnd ℂ) (K a b) ^ 2 =
      (p : ℂ) ^ 2 * ∑ X : ZMod p × ZMod p, ∑ Y : ZMod p × ZMod p,
        (if sP X = sP Y ∧ tP X = tP Y then (1 : ℂ) else 0) := by
  have h1 : ∀ a b : ZMod p, K a b ^ 2 * (starRingEnd ℂ) (K a b) ^ 2 =
      ∑ X : ZMod p × ZMod p, ∑ Y : ZMod p × ZMod p,
        ψ p ((sP X - sP Y) * a) * ψ p ((tP X - tP Y) * b) := by
    intro a b
    rw [K_sq, conj_K_sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun X _ => Finset.sum_congr rfl (fun Y _ => ?_))
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [h1]
  have h2 : ∀ X Y : ZMod p × ZMod p, ∑ a : ZMod p, ∑ b : ZMod p,
      ψ p ((sP X - sP Y) * a) * ψ p ((tP X - tP Y) * b) =
      (p : ℂ) ^ 2 * (if sP X = sP Y ∧ tP X = tP Y then (1 : ℂ) else 0) := by
    intro X Y
    rw [← Finset.sum_mul_sum, orth', orth']
    simp only [sub_eq_zero]
    split_ifs <;> simp_all
    ring
  calc ∑ a : ZMod p, ∑ b : ZMod p, ∑ X : ZMod p × ZMod p, ∑ Y : ZMod p × ZMod p,
        ψ p ((sP X - sP Y) * a) * ψ p ((tP X - tP Y) * b)
      = ∑ a : ZMod p, ∑ X : ZMod p × ZMod p, ∑ b : ZMod p, ∑ Y : ZMod p × ZMod p,
        ψ p ((sP X - sP Y) * a) * ψ p ((tP X - tP Y) * b) :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ X : ZMod p × ZMod p, ∑ a : ZMod p, ∑ b : ZMod p, ∑ Y : ZMod p × ZMod p,
        ψ p ((sP X - sP Y) * a) * ψ p ((tP X - tP Y) * b) := Finset.sum_comm
    _ = ∑ X : ZMod p × ZMod p, ∑ a : ZMod p, ∑ Y : ZMod p × ZMod p, ∑ b : ZMod p,
        ψ p ((sP X - sP Y) * a) * ψ p ((tP X - tP Y) * b) :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
    _ = ∑ X : ZMod p × ZMod p, ∑ Y : ZMod p × ZMod p, ∑ a : ZMod p, ∑ b : ZMod p,
        ψ p ((sP X - sP Y) * a) * ψ p ((tP X - tP Y) * b) :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := by
        simp_rw [h2, Finset.mul_sum]


lemma alg (s y r : ZMod p) (hs : s ≠ 0) (hy0 : y ≠ 0) (hys : y ≠ s) (hr0 : r ≠ 0) (hrs : r ≠ s)
    (h : y⁻¹ + (s - y)⁻¹ = r⁻¹ + (s - r)⁻¹) : y = r ∨ y = s - r := by
  have hys' : s - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hys)
  have hrs' : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
  have h1 : y⁻¹ + (s - y)⁻¹ = s / (y * (s - y)) := by
    field_simp
    ring
  have h2 : r⁻¹ + (s - r)⁻¹ = s / (r * (s - r)) := by
    field_simp
    ring
  rw [h1, h2, div_eq_div_iff (mul_ne_zero hy0 hys') (mul_ne_zero hr0 hrs')] at h
  have key : s * ((y - r) * (s - y - r)) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp key with h3 | h3
  · exact absurd h3 hs
  rcases mul_eq_zero.mp h3 with h4 | h4
  · left; exact sub_eq_zero.mp h4
  · right; linear_combination -h4

lemma row_le_p (X : ZMod p × ZMod p) :
    (univ.filter (fun Y : ZMod p × ZMod p => sP X = sP Y ∧ tP X = tP Y)).card ≤ p := by
  calc (univ.filter (fun Y : ZMod p × ZMod p => sP X = sP Y ∧ tP X = tP Y)).card
      ≤ (univ : Finset (ZMod p)).card := by
        refine Finset.card_le_card_of_injOn (fun Y => Y.1) (fun _ _ => mem_univ _) ?_
        intro Y hY Y' hY' hYY
        rw [Finset.mem_coe, Finset.mem_filter] at hY hY'
        simp only [sP, Finset.mem_univ, true_and] at hY hY'
        have h2 : Y.2 = Y'.2 := by
          have := hY.1.symm.trans hY'.1
          simp only at hYY
          rw [hYY] at this
          exact add_left_cancel this
        exact Prod.ext hYY h2
    _ = p := by rw [card_univ, ZMod.card]

lemma row_le_4 (X : ZMod p × ZMod p) (hs : sP X ≠ 0) :
    (univ.filter (fun Y : ZMod p × ZMod p => sP X = sP Y ∧ tP X = tP Y)).card ≤ 4 := by
  set s := sP X with hsdef
  set t := tP X with htdef
  let f : ZMod p → ZMod p × ZMod p := fun y => (y, s - y)
  have hmem : ∀ Y ∈ univ.filter (fun Y : ZMod p × ZMod p => s = sP Y ∧ t = tP Y),
      Y = f Y.1 ∧ Y.1⁻¹ + (s - Y.1)⁻¹ = t := by
    intro Y hY
    rw [Finset.mem_filter] at hY
    simp only [sP, tP, Finset.mem_univ, true_and] at hY
    have h2 : Y.2 = s - Y.1 := by rw [hY.1]; ring
    refine ⟨Prod.ext rfl h2, ?_⟩
    rw [← h2, hY.2]
  by_cases hr : ∃ r : ZMod p, r ≠ 0 ∧ r ≠ s ∧ r⁻¹ + (s - r)⁻¹ = t
  · obtain ⟨r, hr0, hrs, hrt⟩ := hr
    calc (univ.filter (fun Y : ZMod p × ZMod p => s = sP Y ∧ t = tP Y)).card
        ≤ (({0, s, r, s - r} : Finset (ZMod p)).image f).card := by
          apply Finset.card_le_card
          intro Y hY
          obtain ⟨hYf, hYt⟩ := hmem Y hY
          rw [Finset.mem_image]
          refine ⟨Y.1, ?_, hYf.symm⟩
          simp only [mem_insert, mem_singleton]
          by_cases h0 : Y.1 = 0
          · left; exact h0
          by_cases h1 : Y.1 = s
          · right; left; exact h1
          rcases alg s Y.1 r hs h0 h1 hr0 hrs (hYt.trans hrt.symm) with h | h
          · right; right; left; exact h
          · right; right; right; exact h
      _ ≤ ({0, s, r, s - r} : Finset (ZMod p)).card := Finset.card_image_le
      _ ≤ 4 := Finset.card_le_four
  · push Not at hr
    calc (univ.filter (fun Y : ZMod p × ZMod p => s = sP Y ∧ t = tP Y)).card
        ≤ (({0, s} : Finset (ZMod p)).image f).card := by
          apply Finset.card_le_card
          intro Y hY
          obtain ⟨hYf, hYt⟩ := hmem Y hY
          rw [Finset.mem_image]
          refine ⟨Y.1, ?_, hYf.symm⟩
          simp only [mem_insert, mem_singleton]
          by_cases h0 : Y.1 = 0
          · left; exact h0
          by_cases h1 : Y.1 = s
          · right; exact h1
          exact absurd hYt (hr Y.1 h0 h1)
      _ ≤ ({0, s} : Finset (ZMod p)).card := Finset.card_image_le
      _ ≤ 4 := Finset.card_le_two.trans (by norm_num)

lemma zero_count_le :
    (univ.filter (fun X : ZMod p × ZMod p => sP X = 0)).card ≤ p := by
  calc (univ.filter (fun X : ZMod p × ZMod p => sP X = 0)).card
      ≤ (univ : Finset (ZMod p)).card := by
        refine Finset.card_le_card_of_injOn (fun Y => Y.1) (fun _ _ => mem_univ _) ?_
        intro Y hY Y' hY' hYY
        rw [Finset.mem_coe, Finset.mem_filter] at hY hY'
        simp only [sP, Finset.mem_univ, true_and] at hY hY'
        simp only at hYY
        have h2 : Y.2 = Y'.2 := by
          have := hY.trans hY'.symm
          rw [hYY] at this
          exact add_left_cancel this
        exact Prod.ext hYY h2
    _ = p := by rw [card_univ, ZMod.card]

lemma V_le :
    (∑ X : ZMod p × ZMod p,
      (univ.filter (fun Y : ZMod p × ZMod p => sP X = sP Y ∧ tP X = tP Y)).card) ≤ 5 * p ^ 2 := by
  calc (∑ X : ZMod p × ZMod p,
      (univ.filter (fun Y : ZMod p × ZMod p => sP X = sP Y ∧ tP X = tP Y)).card)
      ≤ ∑ X : ZMod p × ZMod p, ((if sP X = 0 then p else 0) + 4) := by
        apply Finset.sum_le_sum
        intro X _
        split_ifs with h
        · have := row_le_p X; omega
        · have := row_le_4 X h; omega
    _ = p * (univ.filter (fun X : ZMod p × ZMod p => sP X = 0)).card + 4 * (p * p) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
          card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul, smul_eq_mul]
        ring
    _ ≤ p * p + 4 * (p * p) := by
        have := zero_count_le (p := p)
        have : p * (univ.filter (fun X : ZMod p × ZMod p => sP X = 0)).card ≤ p * p :=
          Nat.mul_le_mul_left _ this
        omega
    _ = 5 * p ^ 2 := by ring

lemma moment_real :
    ∑ a : ZMod p, ∑ b : ZMod p, ‖K a b‖ ^ 4 =
      (p : ℝ) ^ 2 * ((∑ X : ZMod p × ZMod p,
      (univ.filter (fun Y : ZMod p × ZMod p => sP X = sP Y ∧ tP X = tP Y)).card : ℕ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have h := moment_eq (p := p)
  have e : ∀ a b : ZMod p, K a b ^ 2 * (starRingEnd ℂ) (K a b) ^ 2 = ((‖K a b‖ ^ 4 : ℝ) : ℂ) := by
    intro a b
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  simp_rw [e] at h
  push_cast at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [Finset.card_filter]
  push_cast
  rfl

lemma moment_le : ∑ a : ZMod p, ∑ b : ZMod p, ‖K a b‖ ^ 4 ≤ 5 * (p : ℝ) ^ 4 := by
  rw [moment_real]
  have := V_le (p := p)
  have h' : ((∑ X : ZMod p × ZMod p,
      (univ.filter (fun Y : ZMod p × ZMod p => sP X = sP Y ∧ tP X = tP Y)).card : ℕ) : ℝ)
      ≤ 5 * (p : ℝ) ^ 2 := by exact_mod_cast this
  have hp : (0 : ℝ) ≤ (p : ℝ) ^ 2 := by positivity
  calc (p : ℝ) ^ 2 * _ ≤ (p : ℝ) ^ 2 * (5 * (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h' hp
    _ = 5 * (p : ℝ) ^ 4 := by ring

lemma K_pow4_le (m : ZMod p) (hm : m ≠ 0) : ‖K 1 m‖ ^ 4 ≤ 10 * (p : ℝ) ^ 3 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hsum : ((p : ℝ) - 1) * ‖K 1 m‖ ^ 4 ≤ 5 * (p : ℝ) ^ 4 := by
    calc ((p : ℝ) - 1) * ‖K 1 m‖ ^ 4
        = ∑ a ∈ (univ : Finset (ZMod p)).erase 0, ‖K a (a⁻¹ * m)‖ ^ 4 := by
          rw [Finset.sum_congr rfl (g := fun _ => ‖K 1 m‖ ^ 4)]
          · rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ _), card_univ, ZMod.card,
              nsmul_eq_mul]
            have : 1 ≤ p := (Fact.out : p.Prime).one_le
            push_cast [this]
            ring
          · intro a ha
            have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
            rw [K_scale a _ ha0, mul_inv_cancel_left₀ ha0]
      _ ≤ ∑ a : ZMod p, ‖K a (a⁻¹ * m)‖ ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => by positivity)
      _ ≤ ∑ a : ZMod p, ∑ b : ZMod p, ‖K a b‖ ^ 4 := by
          apply Finset.sum_le_sum
          intro a _
          exact Finset.single_le_sum (f := fun b => ‖K a b‖ ^ 4) (fun _ _ => by positivity)
            (mem_univ _)
      _ ≤ 5 * (p : ℝ) ^ 4 := moment_le
  have hX : 0 ≤ ‖K 1 m‖ ^ 4 := by positivity
  have hp0 : (0 : ℝ) < p := by linarith
  have : (p : ℝ) * ‖K 1 m‖ ^ 4 ≤ (p : ℝ) * (10 * (p : ℝ) ^ 3) := by nlinarith
  exact le_of_mul_le_mul_left this hp0

/-- the Kloosterman bound constant -/
noncomputable def B (p : ℕ) : ℝ := Real.sqrt (Real.sqrt (10 * (p : ℝ) ^ 3))

lemma B_nonneg : 0 ≤ B p := Real.sqrt_nonneg _

lemma B_pow4 : B p ^ 4 = 10 * (p : ℝ) ^ 3 := by
  have h0 : (0 : ℝ) ≤ 10 * (p : ℝ) ^ 3 := by positivity
  rw [B, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt h0]

lemma K'_le (a b : ZMod p) :
    ‖K a b - (if a = 0 ∧ b = 0 then (p : ℂ) else 0)‖ ≤ B p := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst ha; subst hb
      simp [K_zero_zero, B_nonneg]
    · subst ha
      simp [K_zero_left b hb, hb, B_nonneg]
  · by_cases hb : b = 0
    · subst hb
      simp [K_zero_right a ha, ha, B_nonneg]
    · simp only [ha, false_and, if_false, sub_zero]
      rw [K_scale a b ha]
      have h4 := K_pow4_le (a * b) (mul_ne_zero ha hb)
      apply Real.le_sqrt_of_sq_le
      apply Real.le_sqrt_of_sq_le
      rw [← pow_mul]
      exact h4


lemma swap3 {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

lemma ind_eq (y x : ZMod p) :
    (p : ℂ) * (if y = x then (1 : ℂ) else 0) = ∑ k : ZMod p, ψ p (k * (y - x)) := by
  rw [orth]
  simp only [sub_eq_zero]
  split_ifs <;> simp

/-- the index set -/
def D (L : ℕ) : Finset (ℕ × ℕ) := Finset.range L ×ˢ Finset.range L

/-- the residue attached to an index -/
def aD (p n : ℕ) (d : ℕ × ℕ) : ZMod p := ((n + 1 + d.1 + d.2 : ℕ) : ZMod p)

/-- Fourier transform of the weight -/
noncomputable def W (n L : ℕ) (k : ZMod p) : ℂ := ∑ d ∈ D L, ψ p (k * aD p n d)

/-- the count of inverse pairs -/
noncomputable def Qn (p : ℕ) [Fact p.Prime] (n L : ℕ) : ℕ :=
  ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p, if aD p n d = x ∧ aD p n e = x⁻¹ then 1 else 0

lemma count_identity (n L : ℕ) :
    (p : ℂ) ^ 2 * (Qn p n L : ℂ) =
      ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * K (-k) (-h) := by
  have lhs : (p : ℂ) ^ 2 * (Qn p n L : ℂ) =
      ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p, ∑ k : ZMod p, ∑ h : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) := by
    unfold Qn
    push_cast
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ =>
      Finset.sum_congr rfl (fun x _ => ?_)))
    have e1 : (p : ℂ) ^ 2 * (if aD p n d = x ∧ aD p n e = x⁻¹ then (1 : ℂ) else 0) =
        ((p : ℂ) * (if aD p n d = x then (1 : ℂ) else 0)) *
        ((p : ℂ) * (if aD p n e = x⁻¹ then (1 : ℂ) else 0)) := by
      split_ifs <;> simp_all <;> ring
    rw [e1, ind_eq, ind_eq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun h _ => ?_))
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [lhs]
  have rhs : ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * K (-k) (-h) =
      ∑ k : ZMod p, ∑ h : ZMod p, ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) := by
    unfold W K
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun h _ => ?_))
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
  rw [rhs]
  calc ∑ d ∈ D L, ∑ e ∈ D L, ∑ x : ZMod p, ∑ k : ZMod p, ∑ h : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹)
      = ∑ d ∈ D L, ∑ e ∈ D L, ∑ k : ZMod p, ∑ h : ZMod p, ∑ x : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ =>
          swap3 _ _ _ (fun x k h => ψ p (k * aD p n d) * ψ p (h * aD p n e) *
            ψ p (-k * x + -h * x⁻¹))))
    _ = ∑ d ∈ D L, ∑ k : ZMod p, ∑ h : ZMod p, ∑ e ∈ D L, ∑ x : ZMod p,
        ψ p (k * aD p n d) * ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹) :=
        Finset.sum_congr rfl (fun d _ =>
          swap3 _ _ _ (fun e k h => ∑ x : ZMod p, ψ p (k * aD p n d) * ψ p (h * aD p n e) *
            ψ p (-k * x + -h * x⁻¹)))
    _ = _ := swap3 _ _ _ (fun d k h => ∑ e ∈ D L, ∑ x : ZMod p, ψ p (k * aD p n d) *
            ψ p (h * aD p n e) * ψ p (-k * x + -h * x⁻¹))

/-- the interval exponential sum -/
noncomputable def S (L : ℕ) (k : ZMod p) : ℂ := ∑ u ∈ Finset.range L, ψ p (k * (u : ZMod p))

lemma W_eq (n L : ℕ) (k : ZMod p) :
    W n L k = ψ p (k * ((n + 1 : ℕ) : ZMod p)) * S L k * S L k := by
  unfold W D S
  rw [Finset.sum_product, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [aD]
  push_cast
  ring

lemma norm_W (n L : ℕ) (k : ZMod p) : ‖W n L k‖ = ‖S L k‖ ^ 2 := by
  rw [W_eq, norm_mul, norm_mul, AddChar.norm_apply, one_mul, sq]

lemma parseval (L : ℕ) (hL : L ≤ p) : ∑ k : ZMod p, ‖S L k‖ ^ 2 = (p : ℝ) * L := by
  apply Complex.ofReal_injective
  push_cast
  have e : ∀ k : ZMod p, ((‖S L k‖ ^ 2 : ℝ) : ℂ) =
      ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L, ψ p (k * ((u : ZMod p) - (v : ZMod p))) := by
    intro k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, S, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have e' : ∀ k : ZMod p, ((‖S L k‖ : ℂ) ^ 2) =
      ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L, ψ p (k * ((u : ZMod p) - (v : ZMod p))) := by
    intro k
    exact_mod_cast e k
  simp_rw [e']
  rw [show (∑ k : ZMod p, ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L,
      ψ p (k * ((u : ZMod p) - (v : ZMod p)))) = ∑ u ∈ Finset.range L, ∑ v ∈ Finset.range L,
      ∑ k : ZMod p, ψ p (k * ((u : ZMod p) - (v : ZMod p))) from
    swap3 _ _ _ (fun (k : ZMod p) (u v : ℕ) => ψ p (k * ((u : ZMod p) - (v : ZMod p))))]
  have inner : ∀ u ∈ Finset.range L, ∑ v ∈ Finset.range L, ∑ k : ZMod p,
      ψ p (k * ((u : ZMod p) - (v : ZMod p))) = (p : ℂ) := by
    intro u hu
    simp_rw [orth, sub_eq_zero]
    have hinj : ∀ v ∈ Finset.range L, ((u : ZMod p) = (v : ZMod p) ↔ u = v) := by
      intro v hv
      rw [ZMod.natCast_eq_natCast_iff']
      have hu' : u < p := lt_of_lt_of_le (Finset.mem_range.mp hu) hL
      have hv' : v < p := lt_of_lt_of_le (Finset.mem_range.mp hv) hL
      rw [Nat.mod_eq_of_lt hu', Nat.mod_eq_of_lt hv']
    rw [Finset.sum_eq_single u]
    · simp
    · intro v hv hvu
      rw [if_neg]
      intro h
      exact hvu ((hinj v hv).mp h).symm
    · intro hu'
      exact absurd hu hu'
  rw [Finset.sum_congr rfl inner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

lemma W_zero (n L : ℕ) : W (p := p) n L 0 = (L : ℂ) * L := by
  simp [W, D, Finset.card_product]

lemma sum_norm_W (n L : ℕ) (hL : L ≤ p) : ∑ k : ZMod p, ‖W n L k‖ = (p : ℝ) * L := by
  simp_rw [norm_W]
  exact parseval L hL

lemma main_bound (n L : ℕ) (hL : L ≤ p) :
    (L : ℝ) ^ 4 * p - B p * ((p : ℝ) * L) ^ 2 ≤ (p : ℝ) ^ 2 * (Qn p n L : ℝ) := by
  set E : ZMod p → ZMod p → ℂ := fun k h =>
    K (-k) (-h) - (if -k = 0 ∧ -h = 0 then (p : ℂ) else 0) with hE
  have hsplit : ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * K (-k) (-h) =
      ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h +
      ∑ k : ZMod p, ∑ h : ZMod p,
        W n L k * W n L h * (if -k = 0 ∧ -h = 0 then (p : ℂ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [hE]
    ring
  have h2 : ∑ k : ZMod p, ∑ h : ZMod p,
      W n L k * W n L h * (if -k = 0 ∧ -h = 0 then (p : ℂ) else 0) =
      W (p := p) n L 0 * W (p := p) n L 0 * p := by
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · rw [Finset.sum_eq_single (0 : ZMod p)]
      · simp
      · intro h _ hh
        simp [hh]
      · simp
    · intro k _ hk
      apply Finset.sum_eq_zero
      intro h _
      simp [hk]
    · simp
  have hR : ‖∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h‖ ≤
      B p * ((p : ℝ) * L) ^ 2 := by
    calc ‖∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h‖
        ≤ ∑ k : ZMod p, ‖∑ h : ZMod p, W n L k * W n L h * E k h‖ := norm_sum_le _ _
      _ ≤ ∑ k : ZMod p, ∑ h : ZMod p, ‖W n L k‖ * ‖W n L h‖ * B p := by
          apply Finset.sum_le_sum
          intro k _
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun h _ => ?_))
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left (K'_le (-k) (-h)) (by positivity)
      _ = B p * ((∑ k : ZMod p, ‖W n L k‖) * (∑ h : ZMod p, ‖W n L h‖)) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          ring
      _ = B p * ((p : ℝ) * L) ^ 2 := by
          rw [sum_norm_W n L hL]
          ring
  have hid := count_identity (p := p) n L
  rw [hsplit, h2, W_zero] at hid
  have hreal : (((p : ℝ) ^ 2 * (Qn p n L : ℝ) - (L : ℝ) ^ 4 * p : ℝ) : ℂ) =
      ∑ k : ZMod p, ∑ h : ZMod p, W n L k * W n L h * E k h := by
    push_cast
    rw [hid]
    ring
  have habs : |(p : ℝ) ^ 2 * (Qn p n L : ℝ) - (L : ℝ) ^ 4 * p| ≤ B p * ((p : ℝ) * L) ^ 2 := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal]
    exact hR
  have := neg_abs_le ((p : ℝ) ^ 2 * (Qn p n L : ℝ) - (L : ℝ) ^ 4 * p)
  linarith

lemma inj_zero (n L : ℕ) (hL : L ≤ p) :
    ((D L).filter (fun d => aD p n d = 0)).card ≤ L := by
  calc ((D L).filter (fun d => aD p n d = 0)).card ≤ (Finset.range L).card := by
        refine Finset.card_le_card_of_injOn (fun d => d.1) ?_ ?_
        · intro d hd
          simp only [coe_filter, Set.mem_setOf_eq, D, Finset.mem_product] at hd
          exact hd.1.1
        · intro d hd d' hd' hdd
          simp only [coe_filter, Set.mem_setOf_eq, D, Finset.mem_product, Finset.mem_range] at hd hd'
          simp only at hdd
          have e : aD p n d = aD p n d' := hd.2.trans hd'.2.symm
          simp only [aD] at e
          push_cast at e
          rw [hdd] at e
          have e2 : ((d.2 : ℕ) : ZMod p) = ((d'.2 : ℕ) : ZMod p) := add_left_cancel e
          rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_lt_of_le hd.1.2 hL),
            Nat.mod_eq_of_lt (lt_of_lt_of_le hd'.1.2 hL)] at e2
          exact Prod.ext hdd e2
    _ = L := Finset.card_range L

lemma exists_pair (n L : ℕ) (hL : L ≤ p) (hQ : (L : ℝ) ^ 2 < (Qn p n L : ℝ)) :
    ∃ d ∈ D L, ∃ e ∈ D L, aD p n d * aD p n e = 1 := by
  by_contra hcon
  push Not at hcon
  have hle : Qn p n L ≤ ((D L).filter (fun d => aD p n d = 0)).card *
      ((D L).filter (fun d => aD p n d = 0)).card := by
    rw [Finset.card_filter, Finset.sum_mul_sum]
    unfold Qn
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.sum_eq_single (aD p n d)]
    · simp only [true_and]
      by_cases h1 : aD p n e = (aD p n d)⁻¹
      · by_cases h0 : aD p n d = 0
        · have h3 : aD p n e = 0 := by rw [h1, h0, inv_zero]
          simp [h0, h3]
        · exact absurd (by rw [h1]; exact mul_inv_cancel₀ h0) (hcon d hd e he)
      · simp [h1]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hx h.symm
    · simp
  have hz := inj_zero (p := p) n L hL
  have : Qn p n L ≤ L * L := hle.trans (Nat.mul_le_mul hz hz)
  have : (Qn p n L : ℝ) ≤ (L : ℝ) ^ 2 := by
    rw [sq]; exact_mod_cast this
  linarith

lemma core (n L : ℕ) (hL : L ≤ p) (hL0 : 0 < L) (hbig : (p : ℝ) * (B p + 1) < (L : ℝ) ^ 2) :
    ∃ d ∈ D L, ∃ e ∈ D L, aD p n d * aD p n e = 1 := by
  apply exists_pair n L hL
  have hmb := main_bound (p := p) n L hL
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have key : (p : ℝ) ^ 2 * (L : ℝ) ^ 2 < (p : ℝ) ^ 2 * (Qn p n L : ℝ) := by
    have h1 : (p : ℝ) ^ 2 * (L : ℝ) ^ 2 < (L : ℝ) ^ 4 * p - B p * ((p : ℝ) * L) ^ 2 := by
      have hpos : 0 < (p : ℝ) * (L : ℝ) ^ 2 := by positivity
      have : (p : ℝ) * (L : ℝ) ^ 2 * ((p : ℝ) * (B p + 1)) <
          (p : ℝ) * (L : ℝ) ^ 2 * (L : ℝ) ^ 2 := mul_lt_mul_of_pos_left hbig hpos
      nlinarith
    linarith
  exact lt_of_mul_lt_mul_left key (by positivity)

lemma big_of_pow8 (L : ℕ) (h : 160 * (p : ℝ) ^ 7 < (L : ℝ) ^ 8) :
    (p : ℝ) * (B p + 1) < (L : ℝ) ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hB := B_pow4 (p := p)
  have hB0 := B_nonneg (p := p)
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have h1 : 2 * (p : ℝ) * B p < (L : ℝ) ^ 2 := by
    have : (2 * (p : ℝ) * B p) ^ 4 < ((L : ℝ) ^ 2) ^ 4 := by
      rw [mul_pow, mul_pow, hB, ← pow_mul]
      norm_num
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 4 hL2 this
  have h2 : 2 * (p : ℝ) < (L : ℝ) ^ 2 := by
    have : (2 * (p : ℝ)) ^ 4 < ((L : ℝ) ^ 2) ^ 4 := by
      rw [← pow_mul]
      norm_num
      have : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 7 := pow_le_pow_right₀ hp1 (by norm_num)
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 4 hL2 this
  nlinarith

end OMA.Heil

open OMA.Heil

theorem OMA.solution : type_of% @Erdos445.erdos_445.variants.heilbronn := by
  refine ⟨9 / 10, by norm_num, ?_⟩
  intro c hc
  set c' : ℝ := min c 1 with hc'def
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'0 : 9 / 10 < c' := lt_min hc (by norm_num)
  have t1 : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ (8 * c' - 7)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have t2 : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ c') Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [t1.eventually_gt_atTop 10485760, t2.eventually_ge_atTop 4,
    Filter.eventually_ge_atTop 1] with p hp1 hp2 hp3 hprime n
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp3
  set H : ℝ := (p : ℝ) ^ c' with hH
  set L : ℕ := ⌊H / 2⌋₊ with hLdef
  have hH0 : 0 ≤ H := by positivity
  have hLle : (L : ℝ) ≤ H / 2 := Nat.floor_le (by positivity)
  have hLge : H / 2 - 1 < (L : ℝ) := Nat.sub_one_lt_floor _
  have hHp : H ≤ p := by
    have := Real.rpow_le_rpow_of_exponent_le hp1' hc'1
    rwa [Real.rpow_one] at this
  have hHc : H ≤ (p : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hp1' hc'c
  have hLp : L ≤ p := by
    have : (L : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hL4 : H / 4 ≤ (L : ℝ) := by linarith
  have hL0 : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hpow : 160 * (p : ℝ) ^ 7 < (L : ℝ) ^ 8 := by
    have e1 : H ^ 8 = (p : ℝ) ^ (8 * c' - 7) * (p : ℝ) ^ 7 := by
      rw [hH, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast (p : ℝ) 7,
        ← Real.rpow_add hp0]
      congr 1
      push_cast
      ring
    have e2 : (H / 4) ^ 8 ≤ (L : ℝ) ^ 8 := pow_le_pow_left₀ (by positivity) hL4 8
    have e3 : (H / 4) ^ 8 = H ^ 8 / 65536 := by ring
    have hp7 : 0 < (p : ℝ) ^ 7 := by positivity
    have : 160 * (p : ℝ) ^ 7 < H ^ 8 / 65536 := by
      rw [e1]
      nlinarith
    linarith
  obtain ⟨d, hd, e, he, hde⟩ := core n L hLp hL0 (big_of_pow8 L hpow)
  simp only [D, Finset.mem_product, Finset.mem_range] at hd he
  unfold Erdos445.Erdos445Prop
  refine ⟨n + 1 + d.1 + d.2, n + 1 + e.1 + e.2, by omega, ?_, by omega, ?_, ?_⟩
  · have : ((n + 1 + d.1 + d.2 : ℕ) : ℝ) ≤ n + 2 * L - 1 := by
      have : n + 1 + d.1 + d.2 + 1 ≤ n + 2 * L := by omega
      have : ((n + 1 + d.1 + d.2 + 1 : ℕ) : ℝ) ≤ ((n + 2 * L : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith
    linarith
  · have : ((n + 1 + e.1 + e.2 : ℕ) : ℝ) ≤ n + 2 * L - 1 := by
      have : n + 1 + e.1 + e.2 + 1 ≤ n + 2 * L := by omega
      have : ((n + 1 + e.1 + e.2 + 1 : ℕ) : ℝ) ≤ ((n + 2 * L : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith
    linarith
  · rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    simp only [aD] at hde
    push_cast at hde
    exact hde

