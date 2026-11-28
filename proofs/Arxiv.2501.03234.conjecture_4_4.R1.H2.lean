import OMAReductions.R_Arxiv_2501_03234_conjecture_4_4_R1

-- Step Arxiv.2501.03234.conjecture_4_4.R1.H2: hypothesis H2 of reduction Arxiv.2501.03234.conjecture_4_4.R1
-- Credit: @lettucrisp

open MeasureTheory Filter Topology Set

namespace Arxiv250103234H2

noncomputable section

private def A : ℕ → ℕ → ℕ → ℤ :=
  Nat.rec (fun _ _ => 0) (fun _ f a b =>
    if a = 0 then 0 else 1 - if b % (2 * a) < a then f (b % (2 * a)) a else -f (2 * a - b % (2 * a)) a)

private def E : ℕ → ℝ → ℝ :=
  Nat.rec (fun _ => 0) (fun _ f x =>
    let r := x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)
    if x = 0 then 0 else if r < 1 then 1 - f r else 1 + f (2 - r))

private lemma A_zero (a b : ℕ) : A 0 a b = 0 := rfl

private lemma A_succ (t a b : ℕ) :
    A (t + 1) a b =
      if a = 0 then 0 else 1 - if b % (2 * a) < a then A t (b % (2 * a)) a else -A t (2 * a - b % (2 * a)) a := rfl

private lemma E_zero (x : ℝ) : E 0 x = 0 := rfl

private lemma E_succ (t : ℕ) (x : ℝ) :
    E (t + 1) x =
      let r := x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)
      if x = 0 then 0 else if r < 1 then 1 - E t r else 1 + E t (2 - r) := rfl

private lemma E_abs_le : ∀ (t : ℕ) (x : ℝ), |E t x| ≤ (t : ℝ)
  | 0, x => by simp [E_zero]
  | t + 1, x => by
    rw [E_succ]
    dsimp only
    split_ifs with h0 hr
    · simp; positivity
    · have ih := E_abs_le t (x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ))
      rw [abs_le] at ih ⊢
      push_cast; constructor <;> linarith
    · have ih := E_abs_le t (2 - (x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)))
      rw [abs_le] at ih ⊢
      push_cast; constructor <;> linarith

private lemma E_measurable : ∀ t : ℕ, Measurable (E t)
  | 0 => measurable_const
  | t + 1 => by
    have hr : Measurable (fun x : ℝ => x⁻¹ - 2 * ((⌊x⁻¹ / 2⌋₊ : ℕ) : ℝ)) :=
      measurable_id.inv.sub
        (measurable_const.mul (measurable_from_top.comp (Nat.measurable_floor.comp (measurable_id.inv.div_const (2 : ℝ)))))
    have ih := E_measurable t
    have hbranch : Measurable (fun x : ℝ =>
        if x⁻¹ - 2 * ((⌊x⁻¹ / 2⌋₊ : ℕ) : ℝ) < 1
        then 1 - E t (x⁻¹ - 2 * ((⌊x⁻¹ / 2⌋₊ : ℕ) : ℝ))
        else 1 + E t (2 - (x⁻¹ - 2 * ((⌊x⁻¹ / 2⌋₊ : ℕ) : ℝ)))) :=
      Measurable.ite (measurableSet_lt hr measurable_const)
        (measurable_const.sub (ih.comp hr))
        (measurable_const.add (ih.comp (measurable_const.sub hr)))
    have heq : E (t + 1) = fun x : ℝ =>
        if x = 0 then 0
        else if x⁻¹ - 2 * ((⌊x⁻¹ / 2⌋₊ : ℕ) : ℝ) < 1
        then 1 - E t (x⁻¹ - 2 * ((⌊x⁻¹ / 2⌋₊ : ℕ) : ℝ))
        else 1 + E t (2 - (x⁻¹ - 2 * ((⌊x⁻¹ / 2⌋₊ : ℕ) : ℝ))) := by
      ext x; rfl
    rw [heq]
    exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const hbranch

private lemma E_intervalIntegrable (t : ℕ) (a b : ℝ) : IntervalIntegrable (E t) volume a b := by
  refine (IntegrableOn.of_bound (s := uIcc a b) measure_Icc_lt_top (E_measurable t).aestronglyMeasurable (t : ℝ) ?_).intervalIntegrable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact E_abs_le t x

-- Step 1: Exact pointwise identity A t a b = E t (a / b) for a ≤ b, 0 < b
private lemma A_eq_E : ∀ (t a b : ℕ), a ≤ b → 0 < b → ((A t a b : ℤ) : ℝ) = E t ((a : ℝ) / (b : ℝ))
  | 0, a, b, _, _ => by simp [A_zero, E_zero]
  | t + 1, a, b, hab, hb => by
    rw [A_succ, E_succ]
    dsimp only
    by_cases ha : a = 0
    · subst ha; simp
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha_pos
      have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
      have hx0 : (a : ℝ) / (b : ℝ) ≠ 0 := div_ne_zero haR.ne' hbR.ne'
      have hinv : ((a : ℝ) / (b : ℝ))⁻¹ = (b : ℝ) / (a : ℝ) := inv_div _ _
      have hfl : ⌊((a : ℝ) / (b : ℝ))⁻¹ / 2⌋₊ = b / (2 * a) := by
        rw [hinv, div_div, mul_comm (a : ℝ) 2]
        rw [Nat.floor_eq_iff (by positivity)]
        have hdm := Nat.div_add_mod b (2 * a)
        have hlt := Nat.mod_lt b (show 0 < 2 * a by omega)
        have hdmR : (b : ℝ) = 2 * (a : ℝ) * ((b / (2 * a) : ℕ) : ℝ) + ((b % (2 * a) : ℕ) : ℝ) := by
          exact_mod_cast hdm.symm
        have hltR : ((b % (2 * a) : ℕ) : ℝ) < 2 * (a : ℝ) := by exact_mod_cast hlt
        have hnnR : (0 : ℝ) ≤ ((b % (2 * a) : ℕ) : ℝ) := Nat.cast_nonneg _
        constructor
        · rw [le_div_iff₀ (by positivity)]
          linarith
        · rw [div_lt_iff₀ (by positivity)]
          linarith
      have hr : ((a : ℝ) / (b : ℝ))⁻¹ - 2 * ((⌊((a : ℝ) / (b : ℝ))⁻¹ / 2⌋₊ : ℕ) : ℝ) =
          ((b % (2 * a) : ℕ) : ℝ) / (a : ℝ) := by
        rw [hfl, hinv]
        have hdm := Nat.div_add_mod b (2 * a)
        have hdmR : (b : ℝ) = 2 * (a : ℝ) * ((b / (2 * a) : ℕ) : ℝ) + ((b % (2 * a) : ℕ) : ℝ) := by
          exact_mod_cast hdm.symm
        field_simp [haR.ne']
        linarith
      rw [if_neg ha, if_neg hx0, hr]
      have hcond : ((b % (2 * a) : ℕ) : ℝ) / (a : ℝ) < 1 ↔ b % (2 * a) < a := by
        rw [div_lt_one haR]
        exact_mod_cast Iff.rfl
      by_cases hlt : b % (2 * a) < a
      · rw [if_pos hlt, if_pos (hcond.mpr hlt)]
        push_cast
        rw [A_eq_E t (b % (2 * a)) a hlt.le ha_pos]
      · rw [if_neg hlt, if_neg (mt hcond.mp hlt)]
        have hmod_lt : b % (2 * a) < 2 * a := Nat.mod_lt b (by omega)
        have hsub_le : 2 * a - b % (2 * a) ≤ a := by omega
        have h2r : 2 - ((b % (2 * a) : ℕ) : ℝ) / (a : ℝ) = ((2 * a - b % (2 * a) : ℕ) : ℝ) / (a : ℝ) := by
          have hcast : ((2 * a - b % (2 * a) : ℕ) : ℝ) + ((b % (2 * a) : ℕ) : ℝ) = 2 * (a : ℝ) := by
            exact_mod_cast (show 2 * a - b % (2 * a) + b % (2 * a) = 2 * a by omega)
          field_simp [haR.ne']
          linarith
        rw [h2r, ← A_eq_E t (2 * a - b % (2 * a)) a hsub_le ha_pos]
        push_cast
        ring

-- Step 2: Sorted piecewise-constant covers of (0, 1)
private structure Piece where
  a : ℝ
  b : ℝ
  v : ℝ

private def lenSum (L : List Piece) : ℝ := (L.map (fun p => p.b - p.a)).sum

private def valSum (L : List Piece) : ℝ := (L.map (fun p => p.v * (p.b - p.a))).sum

private def SortedIn (lo hi : ℝ) : List Piece → Prop
  | [] => lo ≤ hi
  | p :: rest => lo ≤ p.a ∧ p.a < p.b ∧ SortedIn p.b hi rest

private def OnCover (t : ℕ) (L : List Piece) : Prop :=
  ∀ p ∈ L, ∀ x ∈ Ioo p.a p.b, E t x = p.v

private lemma sortedIn_bounds {lo hi : ℝ} : ∀ {L : List Piece}, SortedIn lo hi L →
    lo ≤ hi ∧ ∀ p ∈ L, lo ≤ p.a ∧ p.a < p.b ∧ p.b ≤ hi
  | [], h => ⟨h, fun _ hp => nomatch hp⟩
  | p :: rest, ⟨hlo, hab, hrest⟩ => by
    obtain ⟨hphi, hall⟩ := sortedIn_bounds hrest
    refine ⟨by linarith, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ⟨hlo, hab, hphi⟩
    · obtain ⟨h1, h2, h3⟩ := hall q hq'
      exact ⟨by linarith, h2, h3⟩

private lemma sortedIn_lenSum_le {lo hi : ℝ} : ∀ {L : List Piece}, SortedIn lo hi L →
    lenSum L ≤ hi - lo
  | [], h => by simp [lenSum, SortedIn] at h ⊢; linarith
  | p :: rest, ⟨hlo, hab, hrest⟩ => by
    have ih := sortedIn_lenSum_le hrest
    simp only [lenSum, List.map_cons, List.sum_cons] at ih ⊢
    linarith

private lemma sortedIn_append {lo mid hi : ℝ} : ∀ {L1 L2 : List Piece},
    SortedIn lo mid L1 → SortedIn mid hi L2 → SortedIn lo hi (L1 ++ L2)
  | [], L2, h1, h2 => by
    cases L2 with
    | nil => exact le_trans h1 h2
    | cons q rest => exact ⟨le_trans h1 h2.1, h2.2.1, h2.2.2⟩
  | p :: rest, L2, ⟨hlo, hab, hrest⟩, h2 =>
    ⟨hlo, hab, sortedIn_append hrest h2⟩

private lemma lenSum_append (L1 L2 : List Piece) :
    lenSum (L1 ++ L2) = lenSum L1 + lenSum L2 := by
  simp [lenSum]

private lemma sortedIn_map_inc {lo hi : ℝ} (φ : ℝ → ℝ) (c : ℝ)
    (hstrict : ∀ x y, lo ≤ x → x < y → y ≤ hi → φ x < φ y)
    (hmono : ∀ x y, lo ≤ x → x ≤ y → y ≤ hi → φ x ≤ φ y)
    (hlip : ∀ x y, lo ≤ x → x ≤ y → y ≤ hi → φ y - φ x ≤ y - x) :
    ∀ {L : List Piece}, SortedIn lo hi L →
      SortedIn (φ lo) (φ hi) (L.map (fun p => Piece.mk (φ p.a) (φ p.b) (c + p.v))) ∧
      (φ hi - φ lo) - lenSum (L.map (fun p => Piece.mk (φ p.a) (φ p.b) (c + p.v))) ≤
        (hi - lo) - lenSum L
  | [], h => ⟨hmono lo hi le_rfl h le_rfl, by simp only [lenSum, List.map_nil, List.sum_nil, sub_zero]; exact hlip lo hi le_rfl h le_rfl⟩
  | p :: rest, ⟨hlo, hab, hrest⟩ => by
    obtain ⟨hpbhi, _⟩ := sortedIn_bounds hrest
    have ih := sortedIn_map_inc φ c
      (fun x y hx hxy hy => hstrict x y (by linarith) hxy hy)
      (fun x y hx hxy hy => hmono x y (by linarith) hxy hy)
      (fun x y hx hxy hy => hlip x y (by linarith) hxy hy)
      hrest
    refine ⟨⟨hmono lo p.a le_rfl hlo (by linarith), hstrict p.a p.b hlo hab hpbhi, ih.1⟩, ?_⟩
    have hgap : φ p.a - φ lo ≤ p.a - lo := hlip lo p.a le_rfl hlo (by linarith)
    simp only [lenSum, List.map_cons, List.sum_cons] at ih ⊢
    linarith

private lemma sortedIn_map_dec_rev {lo hi : ℝ} (ψ : ℝ → ℝ) (c : ℝ)
    (hstrict : ∀ x y, lo ≤ x → x < y → y ≤ hi → ψ y < ψ x)
    (hmono : ∀ x y, lo ≤ x → x ≤ y → y ≤ hi → ψ y ≤ ψ x)
    (hlip : ∀ x y, lo ≤ x → x ≤ y → y ≤ hi → ψ x - ψ y ≤ y - x) :
    ∀ {L : List Piece}, SortedIn lo hi L →
      SortedIn (ψ hi) (ψ lo) (L.reverse.map (fun p => Piece.mk (ψ p.b) (ψ p.a) (c - p.v))) ∧
      (ψ lo - ψ hi) - lenSum (L.reverse.map (fun p => Piece.mk (ψ p.b) (ψ p.a) (c - p.v))) ≤
        (hi - lo) - lenSum L
  | [], h => ⟨hmono lo hi le_rfl h le_rfl, by simp only [lenSum, List.reverse_nil, List.map_nil, List.sum_nil, sub_zero]; exact hlip lo hi le_rfl h le_rfl⟩
  | p :: rest, ⟨hlo, hab, hrest⟩ => by
    obtain ⟨hpbhi, _⟩ := sortedIn_bounds hrest
    have ih := sortedIn_map_dec_rev ψ c
      (fun x y hx hxy hy => hstrict x y (by linarith) hxy hy)
      (fun x y hx hxy hy => hmono x y (by linarith) hxy hy)
      (fun x y hx hxy hy => hlip x y (by linarith) hxy hy)
      hrest
    have hsing : SortedIn (ψ p.b) (ψ lo) [Piece.mk (ψ p.b) (ψ p.a) (c - p.v)] :=
      ⟨le_rfl, hstrict p.a p.b hlo hab hpbhi, hmono lo p.a le_rfl hlo (by linarith)⟩
    have hsort : SortedIn (ψ hi) (ψ lo)
        ((rest.reverse.map (fun q => Piece.mk (ψ q.b) (ψ q.a) (c - q.v))) ++ [Piece.mk (ψ p.b) (ψ p.a) (c - p.v)]) :=
      sortedIn_append ih.1 hsing
    have hmap : (p :: rest).reverse.map (fun q => Piece.mk (ψ q.b) (ψ q.a) (c - q.v)) =
        (rest.reverse.map (fun q => Piece.mk (ψ q.b) (ψ q.a) (c - q.v))) ++ [Piece.mk (ψ p.b) (ψ p.a) (c - p.v)] := by
      simp
    rw [hmap]
    refine ⟨hsort, ?_⟩
    have hgap : ψ lo - ψ p.a ≤ p.a - lo := hlip lo p.a le_rfl hlo (by linarith)
    rw [lenSum_append]
    simp only [lenSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ih ⊢
    linarith

private lemma E_succ_even_branch (t k : ℕ) {x : ℝ}
    (hx1 : 1 / (2 * ((k : ℝ) + 1)) < x) (hx2 : x < 1 / (2 * ((k : ℝ) + 1) - 1)) :
    E (t + 1) x = 1 + E t (2 * ((k : ℝ) + 1) - x⁻¹) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx0 : 0 < x := lt_trans (by positivity) hx1
  have h1 : 2 * ((k : ℝ) + 1) - 1 < x⁻¹ := by
    rw [one_div, lt_inv_comm₀ hx0 (by linarith)] at hx2; exact hx2
  have h2 : x⁻¹ < 2 * ((k : ℝ) + 1) := by
    rw [one_div, inv_lt_comm₀ (by linarith) hx0] at hx1; exact hx1
  have hfl : ⌊x⁻¹ / 2⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  rw [E_succ]
  dsimp only
  rw [if_neg hx0.ne', hfl, if_neg (by linarith)]
  congr 1; ring

private lemma E_succ_odd_branch (t k : ℕ) {x : ℝ}
    (hx1 : 1 / (2 * ((k : ℝ) + 1) + 1) < x) (hx2 : x < 1 / (2 * ((k : ℝ) + 1))) :
    E (t + 1) x = 1 - E t (x⁻¹ - 2 * ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx0 : 0 < x := lt_trans (by positivity) hx1
  have h1 : 2 * ((k : ℝ) + 1) < x⁻¹ := by
    rw [one_div, lt_inv_comm₀ hx0 (by linarith)] at hx2; exact hx2
  have h2 : x⁻¹ < 2 * ((k : ℝ) + 1) + 1 := by
    rw [one_div, inv_lt_comm₀ (by linarith) hx0] at hx1; exact hx1
  have hfl : ⌊x⁻¹ / 2⌋₊ = k + 1 := by
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast
    constructor <;> linarith
  rw [E_succ]
  dsimp only
  rw [if_neg hx0.ne', hfl, if_pos (by push_cast; linarith)]
  congr 2; push_cast; ring

private lemma pullback_block (t k : ℕ) {L : List Piece} (hsort : SortedIn 0 1 L) (hon : OnCover t L) :
    ∃ B : List Piece,
      SortedIn (1 / (2 * ((k : ℝ) + 1) + 1)) (1 / (2 * ((k : ℝ) + 1) - 1)) B ∧
      OnCover (t + 1) B ∧
      (1 / (2 * ((k : ℝ) + 1) - 1) - 1 / (2 * ((k : ℝ) + 1) + 1)) - lenSum B ≤ 2 * (1 - lenSum L) := by
  let C : ℝ := 2 * ((k : ℝ) + 1)
  have hC : (2 : ℝ) ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) k]
  let φ : ℝ → ℝ := fun u => 1 / (C - u)
  let ψ : ℝ → ℝ := fun u => 1 / (C + u)
  have hφ := sortedIn_map_inc φ 1
    (fun x y hx hxy hy => by
      dsimp [φ]
      rw [one_div, one_div, inv_lt_inv₀ (by linarith) (by linarith)]
      linarith)
    (fun x y hx hxy hy => by
      dsimp [φ]
      rw [one_div, one_div, inv_le_inv₀ (by linarith) (by linarith)]
      linarith)
    (fun x y hx hxy hy => by
      dsimp [φ]
      have h1 : 1 ≤ C - x := by linarith
      have h2 : 1 ≤ C - y := by linarith
      have heq : 1 / (C - y) - 1 / (C - x) = (y - x) / ((C - x) * (C - y)) := by
        field_simp [show C - x ≠ 0 by linarith, show C - y ≠ 0 by linarith]; ring
      rw [heq]
      exact div_le_self (by linarith) (by nlinarith))
    hsort
  have hψ := sortedIn_map_dec_rev ψ 1
    (fun x y hx hxy hy => by
      dsimp [ψ]
      rw [one_div, one_div, inv_lt_inv₀ (by linarith) (by linarith)]
      linarith)
    (fun x y hx hxy hy => by
      dsimp [ψ]
      rw [one_div, one_div, inv_le_inv₀ (by linarith) (by linarith)]
      linarith)
    (fun x y hx hxy hy => by
      dsimp [ψ]
      have h1 : 1 ≤ C + x := by linarith
      have h2 : 1 ≤ C + y := by linarith
      have heq : 1 / (C + x) - 1 / (C + y) = (y - x) / ((C + x) * (C + y)) := by
        field_simp [show C + x ≠ 0 by linarith, show C + y ≠ 0 by linarith]; ring
      rw [heq]
      exact div_le_self (by linarith) (by nlinarith))
    hsort
  let Lodd := L.reverse.map (fun p => Piece.mk (ψ p.b) (ψ p.a) (1 - p.v))
  let Leven := L.map (fun p => Piece.mk (φ p.a) (φ p.b) (1 + p.v))
  have hψ0 : ψ 0 = 1 / C := by simp [ψ]
  have hψ1 : ψ 1 = 1 / (C + 1) := by simp [ψ]
  have hφ0 : φ 0 = 1 / C := by simp [φ]
  have hφ1 : φ 1 = 1 / (C - 1) := by simp [φ]
  refine ⟨Lodd ++ Leven, ?_, ?_, ?_⟩
  · have h1 : SortedIn (1 / (C + 1)) (1 / C) Lodd := by rw [← hψ1, ← hψ0]; exact hψ.1
    have h2 : SortedIn (1 / C) (1 / (C - 1)) Leven := by rw [← hφ0, ← hφ1]; exact hφ.1
    exact sortedIn_append h1 h2
  · intro q hq x hx
    rcases List.mem_append.mp hq with hq1 | hq2
    · rcases List.mem_map.mp hq1 with ⟨p, hp, rfl⟩
      have hpL : p ∈ L := List.mem_reverse.mp hp
      obtain ⟨_, hpb⟩ := sortedIn_bounds hsort
      obtain ⟨hpa0, hpab, hpb1⟩ := hpb p hpL
      have hx1 : 1 / (C + 1) < x := by
        have : 1 / (C + 1) ≤ ψ p.b := by
          dsimp [ψ]; rw [one_div, one_div, inv_le_inv₀ (by linarith) (by linarith)]; linarith
        exact lt_of_le_of_lt this hx.1
      have hx2 : x < 1 / C := by
        have : ψ p.a ≤ 1 / C := by
          dsimp [ψ]; rw [one_div, one_div, inv_le_inv₀ (by linarith) (by linarith)]; linarith
        exact lt_of_lt_of_le hx.2 this
      rw [E_succ_odd_branch t k hx1 hx2]
      have hx0 : 0 < x := lt_trans (by positivity) hx1
      have hu1 : p.a < x⁻¹ - C := by
        have := hx.2; dsimp [ψ] at this
        rw [one_div, lt_inv_comm₀ hx0 (by linarith)] at this; linarith
      have hu2 : x⁻¹ - C < p.b := by
        have := hx.1; dsimp [ψ] at this
        rw [one_div, inv_lt_comm₀ (by linarith) hx0] at this; linarith
      rw [hon p hpL (x⁻¹ - C) ⟨hu1, hu2⟩]
    · rcases List.mem_map.mp hq2 with ⟨p, hpL, rfl⟩
      obtain ⟨_, hpb⟩ := sortedIn_bounds hsort
      obtain ⟨hpa0, hpab, hpb1⟩ := hpb p hpL
      have hx1 : 1 / C < x := by
        have : 1 / C ≤ φ p.a := by
          dsimp [φ]; rw [one_div, one_div, inv_le_inv₀ (by linarith) (by linarith)]; linarith
        exact lt_of_le_of_lt this hx.1
      have hx2 : x < 1 / (C - 1) := by
        have : φ p.b ≤ 1 / (C - 1) := by
          dsimp [φ]; rw [one_div, one_div, inv_le_inv₀ (by linarith) (by linarith)]; linarith
        exact lt_of_lt_of_le hx.2 this
      rw [E_succ_even_branch t k hx1 hx2]
      have hx0 : 0 < x := lt_trans (by positivity) hx1
      have hu1 : p.a < C - x⁻¹ := by
        have := hx.1; dsimp [φ] at this
        rw [one_div, inv_lt_comm₀ (by linarith) hx0] at this; linarith
      have hu2 : C - x⁻¹ < p.b := by
        have := hx.2; dsimp [φ] at this
        rw [one_div, lt_inv_comm₀ hx0 (by linarith)] at this; linarith
      rw [hon p hpL (C - x⁻¹) ⟨hu1, hu2⟩]
  · rw [lenSum_append]
    have h1 := hψ.2
    have h2 := hφ.2
    rw [hψ0, hψ1] at h1
    rw [hφ0, hφ1] at h2
    linarith

private lemma pullback_blocks (t : ℕ) {L : List Piece} (hsort : SortedIn 0 1 L) (hon : OnCover t L) :
    ∀ K : ℕ, ∃ B : List Piece,
      SortedIn (1 / (2 * (K : ℝ) + 1)) 1 B ∧
      OnCover (t + 1) B ∧
      (1 - 1 / (2 * (K : ℝ) + 1)) - lenSum B ≤ 2 * (K : ℝ) * (1 - lenSum L)
  | 0 => by
    refine ⟨[], ?_, ?_, ?_⟩
    · norm_num [SortedIn]
    · intro _ h; exact nomatch h
    · norm_num [lenSum]
  | K + 1 => by
    obtain ⟨Brest, hsort_r, hon_r, hlen_r⟩ := pullback_blocks t hsort hon K
    obtain ⟨Bcur, hsort_c, hon_c, hlen_c⟩ := pullback_block t K hsort hon
    have hmid : 2 * ((K : ℝ) + 1) - 1 = 2 * (K : ℝ) + 1 := by ring
    have hlo : 2 * ((K : ℝ) + 1) + 1 = 2 * ((K + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hmid, hlo] at hsort_c hlen_c
    refine ⟨Bcur ++ Brest, sortedIn_append hsort_c hsort_r, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with h1 | h2
      · exact hon_c q h1
      · exact hon_r q h2
    · rw [lenSum_append]
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hlen_c ⊢
      have hmul : 2 * ((K : ℝ) + 1) * (1 - lenSum L) = 2 * (K : ℝ) * (1 - lenSum L) + 2 * (1 - lenSum L) := by ring
      linarith

private lemma exists_goodCover : ∀ (t : ℕ) (ε : ℝ), 0 < ε →
    ∃ L : List Piece, SortedIn 0 1 L ∧ OnCover t L ∧ 1 - ε < lenSum L
  | 0, ε, hε => by
    refine ⟨[⟨0, 1, 0⟩], ⟨le_rfl, zero_lt_one, le_rfl⟩, ?_, ?_⟩
    · intro p hp x _
      rcases List.mem_singleton.mp hp with rfl
      exact E_zero x
    · simp [lenSum]; linarith
  | t + 1, ε, hε => by
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    have hKpos : 1 ≤ K := by
      by_contra h0
      have hK0 : K = 0 := by omega
      rw [hK0, Nat.cast_zero] at hK
      have : (0 : ℝ) < 1 / ε := by positivity
      linarith
    have hKR : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
    have htail : 1 / (2 * (K : ℝ) + 1) < ε / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have h1 : 1 < (K : ℝ) * ε := (div_lt_iff₀ hε).mp hK
      linarith
    have hδ : 0 < ε / (4 * (K : ℝ)) := by positivity
    obtain ⟨L, hsort, hon, hlen⟩ := exists_goodCover t (ε / (4 * (K : ℝ))) hδ
    obtain ⟨B, hsortB, honB, hlenB⟩ := pullback_blocks t hsort hon K
    have hsort0 : SortedIn 0 1 B := by
      have h0le : (0 : ℝ) ≤ 1 / (2 * (K : ℝ) + 1) := by positivity
      cases B with
      | nil => exact zero_le_one
      | cons q rest => exact ⟨le_trans h0le hsortB.1, hsortB.2.1, hsortB.2.2⟩
    refine ⟨B, hsort0, honB, ?_⟩
    have h2K : 2 * (K : ℝ) * (1 - lenSum L) < ε / 2 := by
      have h1 : 1 - lenSum L < ε / (4 * (K : ℝ)) := by linarith
      have h2 : 2 * (K : ℝ) * (1 - lenSum L) < 2 * (K : ℝ) * (ε / (4 * (K : ℝ))) :=
        mul_lt_mul_of_pos_left h1 (by positivity)
      have h3 : 2 * (K : ℝ) * (ε / (4 * (K : ℝ))) = ε / 2 := by
        field_simp [hKR.ne']; ring
      linarith
    linarith

-- Step 3: Integral approximation by sorted cover
private lemma integral_cover_err (t : ℕ) {lo : ℝ} (hlo0 : 0 ≤ lo) :
    ∀ {L : List Piece}, SortedIn lo 1 L → OnCover t L →
      |(∫ x in lo..1, E t x) - valSum L| ≤ (t : ℝ) * ((1 - lo) - lenSum L)
  | [], hsort, _ => by
    simp only [valSum, lenSum, List.map_nil, List.sum_nil, sub_zero]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := lo) (b := 1) (f := E t)
      (C := (t : ℝ)) (fun x _ => by rw [Real.norm_eq_abs]; exact E_abs_le t x)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsort)] at h
  | p :: rest, ⟨hlo, hab, hrest⟩, hon => by
    obtain ⟨hpb1, _⟩ := sortedIn_bounds hrest
    have hsplit1 : ∫ x in lo..1, E t x = (∫ x in lo..p.a, E t x) + ∫ x in p.a..1, E t x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (E_intervalIntegrable t lo p.a) (E_intervalIntegrable t p.a 1)).symm
    have hsplit2 : ∫ x in p.a..1, E t x = (∫ x in p.a..p.b, E t x) + ∫ x in p.b..1, E t x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (E_intervalIntegrable t p.a p.b) (E_intervalIntegrable t p.b 1)).symm
    have hp_int : ∫ x in p.a..p.b, E t x = p.v * (p.b - p.a) := by
      rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have hcongr : ∫ x in Ioo p.a p.b, E t x = ∫ _ in Ioo p.a p.b, p.v :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx =>
          hon p (List.mem_cons_self ..) x hx
      rw [hcongr, MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hab.le, mul_comm]
    have hgap : |∫ x in lo..p.a, E t x| ≤ (t : ℝ) * (p.a - lo) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := lo) (b := p.a) (f := E t)
        (C := (t : ℝ)) (fun x _ => by rw [Real.norm_eq_abs]; exact E_abs_le t x)
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlo)] at h
    have ih := integral_cover_err t (by linarith) hrest
      (fun q hq => hon q (List.mem_cons_of_mem p hq))
    have heq : (∫ x in lo..1, E t x) - valSum (p :: rest) =
        (∫ x in lo..p.a, E t x) + ((∫ x in p.b..1, E t x) - valSum rest) := by
      rw [hsplit1, hsplit2, hp_int]
      simp only [valSum, List.map_cons, List.sum_cons]
      ring
    rw [heq]
    have htri := abs_add_le (∫ x in lo..p.a, E t x) ((∫ x in p.b..1, E t x) - valSum rest)
    have hlen : lenSum (p :: rest) = (p.b - p.a) + lenSum rest := rfl
    rw [hlen]
    have hmul : (t : ℝ) * ((1 - lo) - ((p.b - p.a) + lenSum rest)) =
        (t : ℝ) * (p.a - lo) + (t : ℝ) * ((1 - p.b) - lenSum rest) := by ring
    linarith

-- Step 4: Discrete grid count and approximation by sorted cover
private def gridPt (m j : ℕ) : ℝ := (2 * ((j : ℝ) + 1)) / ((2 * m + 1 : ℕ) : ℝ)

private lemma gridPt_mem (m : ℕ) {j : ℕ} (hj : j ∈ Finset.range m) :
    0 < gridPt m j ∧ gridPt m j ≤ 1 := by
  rw [Finset.mem_range] at hj
  dsimp [gridPt]
  have hN : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  constructor
  · positivity
  · rw [div_le_one hN]
    have : 2 * (j + 1) ≤ 2 * m + 1 := by omega
    exact_mod_cast this

private lemma card_grid_Ioc (m : ℕ) {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβ1 : β ≤ 1) :
    let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
    let S := (Finset.range m).filter (fun j => α < gridPt m j ∧ gridPt m j ≤ β)
    |((S.card : ℕ) : ℝ) - (β - α) * (N / 2)| ≤ 1 := by
  intro N S
  have hβ0 : 0 ≤ β := le_trans hα0 hαβ
  have hN : 0 < N := by dsimp [N]; positivity
  have hN2 : N / 2 = (m : ℝ) + 1 / 2 := by dsimp [N]; push_cast; ring
  have hfl_le : ⌊β * (N / 2)⌋₊ ≤ m := by
    have h1 : β * (N / 2) < (m : ℝ) + 1 := by nlinarith
    exact Nat.lt_succ_iff.mp (Nat.floor_lt (by positivity) |>.mpr (by exact_mod_cast h1))
  have hfl_mono : ⌊α * (N / 2)⌋₊ ≤ ⌊β * (N / 2)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hαβ (by positivity))
  have hcard : S.card = (Finset.Icc (⌊α * (N / 2)⌋₊ + 1) ⌊β * (N / 2)⌋₊).card := by
    refine Finset.card_bij (fun j _ => j + 1) ?_ ?_ ?_
    · intro j hj
      simp only [S, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hj ⊢
      obtain ⟨hjm, h1, h2⟩ := hj
      dsimp [gridPt] at h1 h2
      have h1' : α * (N / 2) < ((j + 1 : ℕ) : ℝ) := by
        have : α * N < 2 * ((j : ℝ) + 1) := (lt_div_iff₀ hN).mp h1
        push_cast; linarith
      have h2' : ((j + 1 : ℕ) : ℝ) ≤ β * (N / 2) := by
        have : 2 * ((j : ℝ) + 1) ≤ β * N := (div_le_iff₀ hN).mp h2
        push_cast; linarith
      exact ⟨Nat.succ_le_of_lt (Nat.floor_lt (by positivity) |>.mpr h1'), Nat.le_floor h2'⟩
    · intro j1 _ j2 _ h; omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      refine ⟨k - 1, ?_, by omega⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      have hk1 : 1 ≤ k := by omega
      have hkm : k - 1 < m := by omega
      have hkcast : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by exact_mod_cast (show k - 1 + 1 = k by omega)
      refine ⟨hkm, ?_, ?_⟩
      · dsimp [gridPt]
        rw [hkcast, lt_div_iff₀ hN]
        have hlt : α * (N / 2) < (k : ℝ) := by
          have := Nat.lt_floor_add_one (α * (N / 2))
          have hk' : ((⌊α * (N / 2)⌋₊ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          push_cast at hk'; linarith
        linarith
      · dsimp [gridPt]
        rw [hkcast, div_le_iff₀ hN]
        have hle : (k : ℝ) ≤ β * (N / 2) :=
          le_trans (by exact_mod_cast hk.2) (Nat.floor_le (by positivity))
        linarith
  rw [hcard, Nat.card_Icc]
  have hsub : ⌊β * (N / 2)⌋₊ + 1 - (⌊α * (N / 2)⌋₊ + 1) = ⌊β * (N / 2)⌋₊ - ⌊α * (N / 2)⌋₊ := by omega
  rw [hsub]
  have hcast : ((⌊β * (N / 2)⌋₊ - ⌊α * (N / 2)⌋₊ : ℕ) : ℝ) =
      (⌊β * (N / 2)⌋₊ : ℝ) - (⌊α * (N / 2)⌋₊ : ℝ) := Nat.cast_sub hfl_mono
  rw [hcast]
  have hα1 : (⌊α * (N / 2)⌋₊ : ℝ) ≤ α * (N / 2) := Nat.floor_le (by positivity)
  have hα2 : α * (N / 2) < (⌊α * (N / 2)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hβ1' : (⌊β * (N / 2)⌋₊ : ℝ) ≤ β * (N / 2) := Nat.floor_le (by positivity)
  have hβ2 : β * (N / 2) < (⌊β * (N / 2)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

private lemma card_grid_eq_le_one (m : ℕ) (x : ℝ) :
    ((Finset.range m).filter (fun j => gridPt m j = x)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j1 hj1 j2 hj2
  simp only [Finset.mem_filter] at hj1 hj2
  have heq : gridPt m j1 = gridPt m j2 := hj1.2.trans hj2.2.symm
  dsimp [gridPt] at heq
  have hN : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 : 2 * ((j1 : ℝ) + 1) = 2 * ((j2 : ℝ) + 1) := (div_left_inj' hN).mp heq
  have h2 : (j1 : ℝ) = (j2 : ℝ) := by linarith
  exact_mod_cast h2

private lemma discrete_cover_err (t m : ℕ) {lo : ℝ} (hlo0 : 0 ≤ lo) :
    ∀ {L : List Piece}, SortedIn lo 1 L → OnCover t L →
      let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
      let H := (Finset.range m).filter (fun j => lo < gridPt m j ∧ gridPt m j ≤ 1)
      |(∑ j ∈ H, E t (gridPt m j)) - (N / 2) * valSum L| ≤
        (t : ℝ) * (((1 - lo) - lenSum L) * (N / 2) + 4 * ((L.length : ℝ) + 1))
  | [], hsort, _ => by
    intro N H
    simp only [valSum, lenSum, List.map_nil, List.sum_nil, mul_zero, sub_zero, List.length_nil, Nat.cast_zero, zero_add]
    have hsum : |∑ j ∈ H, E t (gridPt m j)| ≤ ((H.card : ℕ) : ℝ) * (t : ℝ) := by
      calc |∑ j ∈ H, E t (gridPt m j)|
            ≤ ∑ j ∈ H, |E t (gridPt m j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ H, (t : ℝ) := Finset.sum_le_sum fun j _ => E_abs_le t _
        _ = ((H.card : ℕ) : ℝ) * (t : ℝ) := by simp
    have hcard := card_grid_Ioc m hlo0 hsort le_rfl
    rw [abs_le] at hcard
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    nlinarith
  | p :: rest, ⟨hlo, hab, hrest⟩, hon => by
    intro N H
    obtain ⟨hpb1, _⟩ := sortedIn_bounds hrest
    let H1 := (Finset.range m).filter (fun j => lo < gridPt m j ∧ gridPt m j ≤ p.a)
    let H2 := (Finset.range m).filter (fun j => p.a < gridPt m j ∧ gridPt m j < p.b)
    let H3 := (Finset.range m).filter (fun j => gridPt m j = p.b)
    let H4 := (Finset.range m).filter (fun j => p.b < gridPt m j ∧ gridPt m j ≤ 1)
    have hH23 : H2 ∪ H3 = (Finset.range m).filter (fun j => p.a < gridPt m j ∧ gridPt m j ≤ p.b) := by
      ext j
      simp only [H2, H3, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2, h3.le⟩
        · exact ⟨h1, by linarith, h2.le⟩
      · rintro ⟨h1, h2, h3⟩
        rcases lt_or_eq_of_le h3 with hlt | heq
        · exact Or.inl ⟨h1, h2, hlt⟩
        · exact Or.inr ⟨h1, heq⟩
    have hdisj23 : Disjoint H2 H3 := by
      rw [Finset.disjoint_left]
      intro j hj2 hj3
      simp only [H2, H3, Finset.mem_filter] at hj2 hj3
      linarith
    have hH : H = H1 ∪ (H2 ∪ H3) ∪ H4 := by
      ext j
      simp only [H, H1, hH23, H4, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hj, h1, h2⟩
        by_cases c1 : gridPt m j ≤ p.a
        · exact Or.inl (Or.inl ⟨hj, h1, c1⟩)
        · by_cases c2 : gridPt m j ≤ p.b
          · exact Or.inl (Or.inr ⟨hj, lt_of_not_ge c1, c2⟩)
          · exact Or.inr ⟨hj, lt_of_not_ge c2, h2⟩
      · rintro ((⟨hj, h1, h2⟩ | ⟨hj, h1, h2⟩) | ⟨hj, h1, h2⟩)
        · exact ⟨hj, h1, by linarith⟩
        · exact ⟨hj, by linarith, by linarith⟩
        · exact ⟨hj, by linarith, h2⟩
    have hdisj1_23 : Disjoint H1 (H2 ∪ H3) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj23
      rw [hH23] at hj23
      simp only [H1, Finset.mem_filter] at hj1 hj23
      linarith
    have hdisj123_4 : Disjoint (H1 ∪ (H2 ∪ H3)) H4 := by
      rw [Finset.disjoint_left]
      intro j hj123 hj4
      simp only [H1, hH23, H4, Finset.mem_union, Finset.mem_filter] at hj123 hj4
      rcases hj123 with ⟨_, _, hle⟩ | ⟨_, _, hle⟩ <;> linarith
    have hsum_split : ∑ j ∈ H, E t (gridPt m j) =
        (∑ j ∈ H1, E t (gridPt m j)) +
        (∑ j ∈ H2, E t (gridPt m j)) +
        (∑ j ∈ H3, E t (gridPt m j)) +
        (∑ j ∈ H4, E t (gridPt m j)) := by
      rw [hH, Finset.sum_union hdisj123_4, Finset.sum_union hdisj1_23, Finset.sum_union hdisj23]
      ring
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    -- Bound on H1
    have hB1 : |∑ j ∈ H1, E t (gridPt m j)| ≤ (t : ℝ) * ((p.a - lo) * (N / 2) + 1) := by
      have hs : |∑ j ∈ H1, E t (gridPt m j)| ≤ ((H1.card : ℕ) : ℝ) * (t : ℝ) := by
        calc |∑ j ∈ H1, E t (gridPt m j)|
              ≤ ∑ j ∈ H1, |E t (gridPt m j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _ ∈ H1, (t : ℝ) := Finset.sum_le_sum fun j _ => E_abs_le t _
          _ = ((H1.card : ℕ) : ℝ) * (t : ℝ) := by simp
      have hc := card_grid_Ioc m hlo0 hlo (by linarith)
      rw [abs_le] at hc
      nlinarith
    -- Bound on H2
    have hpv_abs : |p.v| ≤ (t : ℝ) := by
      have hmid : (p.a + p.b) / 2 ∈ Ioo p.a p.b := ⟨by linarith, by linarith⟩
      rw [← hon p (List.mem_cons_self ..) ((p.a + p.b) / 2) hmid]
      exact E_abs_le t _
    have hB2 : |(∑ j ∈ H2, E t (gridPt m j)) - (N / 2) * (p.v * (p.b - p.a))| ≤ (t : ℝ) * 2 := by
      have hconst : ∑ j ∈ H2, E t (gridPt m j) = ((H2.card : ℕ) : ℝ) * p.v := by
        calc ∑ j ∈ H2, E t (gridPt m j)
              = ∑ _ ∈ H2, p.v := Finset.sum_congr rfl fun j hj => by
                  simp only [H2, Finset.mem_filter] at hj
                  exact hon p (List.mem_cons_self ..) (gridPt m j) hj.2
          _ = ((H2.card : ℕ) : ℝ) * p.v := by simp
      rw [hconst]
      have heq : ((H2.card : ℕ) : ℝ) * p.v - (N / 2) * (p.v * (p.b - p.a)) =
          p.v * (((H2.card : ℕ) : ℝ) - (p.b - p.a) * (N / 2)) := by ring
      rw [heq, abs_mul]
      have hcard23 := card_grid_Ioc m (by linarith) hab.le hpb1
      dsimp only at hcard23
      rw [← hH23, Finset.card_union_of_disjoint hdisj23] at hcard23
      have hc3 : ((H3.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast card_grid_eq_le_one m p.b
      have hc3_nn : (0 : ℝ) ≤ ((H3.card : ℕ) : ℝ) := Nat.cast_nonneg _
      push_cast at hcard23
      rw [abs_le] at hcard23
      have hdiff2 : |((H2.card : ℕ) : ℝ) - (p.b - p.a) * (N / 2)| ≤ 2 := by
        have hNcast : N = 2 * (m : ℝ) + 1 := by dsimp [N]; push_cast; ring
        rw [hNcast, abs_le]; constructor <;> linarith
      exact mul_le_mul hpv_abs hdiff2 (abs_nonneg _) ht0
    -- Bound on H3
    have hB3 : |∑ j ∈ H3, E t (gridPt m j)| ≤ (t : ℝ) * 1 := by
      have hs : |∑ j ∈ H3, E t (gridPt m j)| ≤ ((H3.card : ℕ) : ℝ) * (t : ℝ) := by
        calc |∑ j ∈ H3, E t (gridPt m j)|
              ≤ ∑ j ∈ H3, |E t (gridPt m j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _ ∈ H3, (t : ℝ) := Finset.sum_le_sum fun j _ => E_abs_le t _
          _ = ((H3.card : ℕ) : ℝ) * (t : ℝ) := by simp
      have hc3 : ((H3.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast card_grid_eq_le_one m p.b
      nlinarith
    -- Bound on H4 by IH
    have ih := discrete_cover_err t m (by linarith) hrest
      (fun q hq => hon q (List.mem_cons_of_mem p hq))
    dsimp only at ih
    have hsplit_err : (∑ j ∈ H, E t (gridPt m j)) - (N / 2) * valSum (p :: rest) =
        (∑ j ∈ H1, E t (gridPt m j)) +
        ((∑ j ∈ H2, E t (gridPt m j)) - (N / 2) * (p.v * (p.b - p.a))) +
        (∑ j ∈ H3, E t (gridPt m j)) +
        ((∑ j ∈ H4, E t (gridPt m j)) - (N / 2) * valSum rest) := by
      rw [hsum_split]
      simp only [valSum, List.map_cons, List.sum_cons]
      ring
    rw [hsplit_err]
    have htri1 := abs_add_le
      ((∑ j ∈ H1, E t (gridPt m j)) +
        ((∑ j ∈ H2, E t (gridPt m j)) - (N / 2) * (p.v * (p.b - p.a))) +
        (∑ j ∈ H3, E t (gridPt m j)))
      ((∑ j ∈ H4, E t (gridPt m j)) - (N / 2) * valSum rest)
    have htri2 := abs_add_le
      ((∑ j ∈ H1, E t (gridPt m j)) +
        ((∑ j ∈ H2, E t (gridPt m j)) - (N / 2) * (p.v * (p.b - p.a))))
      (∑ j ∈ H3, E t (gridPt m j))
    have htri3 := abs_add_le
      (∑ j ∈ H1, E t (gridPt m j))
      ((∑ j ∈ H2, E t (gridPt m j)) - (N / 2) * (p.v * (p.b - p.a)))
    have hlen : lenSum (p :: rest) = (p.b - p.a) + lenSum rest := rfl
    rw [hlen, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hmul : (t : ℝ) * (((1 - lo) - ((p.b - p.a) + lenSum rest)) * (N / 2) + 4 * ((rest.length : ℝ) + 1 + 1)) =
        (t : ℝ) * ((p.a - lo) * (N / 2) + 1) + (t : ℝ) * 2 + (t : ℝ) * 1 +
        (t : ℝ) * (((1 - p.b) - lenSum rest) * (N / 2) + 4 * ((rest.length : ℝ) + 1)) := by ring
    linarith

private lemma even_sum_eq (t m : ℕ) :
    ((∑ a ∈ (Finset.Ico 1 (2 * m + 1)).filter Even, A t a (2 * m + 1) : ℤ) : ℝ) =
      ∑ j ∈ Finset.range m, E t (gridPt m j) := by
  have himg : (Finset.Ico 1 (2 * m + 1)).filter Even = (Finset.range m).image (fun j => 2 * (j + 1)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨ha1, ha2⟩, ⟨k, hk⟩⟩
      refine ⟨k - 1, ?_, ?_⟩ <;> omega
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨j + 1, by ring⟩⟩
  rw [himg, Finset.sum_image (fun _ _ _ _ h => by omega)]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hle : 2 * (j + 1) ≤ 2 * m + 1 := by omega
  rw [A_eq_E t (2 * (j + 1)) (2 * m + 1) hle (by omega)]
  dsimp [gridPt]
  congr 1
  push_cast
  ring

private lemma main_theorem :
    ∀ t : ℕ, Tendsto
      (fun m : ℕ => ((∑ a ∈ (Finset.Ico 1 (2 * m + 1)).filter Even, A t a (2 * m + 1) : ℤ) : ℝ) /
        ((2 * m + 1 : ℕ) : ℝ))
      atTop (𝓝 ((1 / 2) * (∫ x in (0 : ℝ)..1, E t x))) := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht0
  · simp [A_zero, E_zero]
  · have htpos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L, hsort, hon, hlen⟩ := exists_goodCover t (ε / (2 * (t : ℝ))) (by positivity)
    obtain ⟨M, hM⟩ := exists_nat_gt (8 * (t : ℝ) * ((L.length : ℝ) + 1) / ε)
    refine ⟨M, fun m hm => ?_⟩
    rw [Real.dist_eq, even_sum_eq t m]
    set N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
    have hNpos : 0 < N := by dsimp [N]; positivity
    have hH_eq : (Finset.range m).filter (fun j => (0 : ℝ) < gridPt m j ∧ gridPt m j ≤ 1) =
        Finset.range m := by
      ext j
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      exact gridPt_mem m
    have hdisc := discrete_cover_err t m le_rfl hsort hon
    dsimp only at hdisc
    rw [hH_eq] at hdisc
    have hint := integral_cover_err t le_rfl hsort hon
    have hdiff_split :
        (∑ j ∈ Finset.range m, E t (gridPt m j)) / N - (1 / 2) * (∫ x in (0 : ℝ)..1, E t x) =
        ((∑ j ∈ Finset.range m, E t (gridPt m j)) - (N / 2) * valSum L) / N -
        (1 / 2) * ((∫ x in (0 : ℝ)..1, E t x) - valSum L) := by
      field_simp [hNpos.ne']; ring
    rw [hdiff_split]
    have htri := abs_sub
      (((∑ j ∈ Finset.range m, E t (gridPt m j)) - (N / 2) * valSum L) / N)
      ((1 / 2) * ((∫ x in (0 : ℝ)..1, E t x) - valSum L))
    have h1 : |((∑ j ∈ Finset.range m, E t (gridPt m j)) - (N / 2) * valSum L) / N| ≤
        (t : ℝ) * ((1 - lenSum L) / 2 + 4 * ((L.length : ℝ) + 1) / N) := by
      rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
      have : (t : ℝ) * ((1 - lenSum L) / 2 + 4 * ((L.length : ℝ) + 1) / N) * N =
          (t : ℝ) * (((1 - 0) - lenSum L) * (N / 2) + 4 * ((L.length : ℝ) + 1)) := by
        field_simp [hNpos.ne']; ring
      linarith
    have h2 : |(1 / 2) * ((∫ x in (0 : ℝ)..1, E t x) - valSum L)| ≤
        (t : ℝ) * ((1 - lenSum L) / 2) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    have hgap1 : (t : ℝ) * (1 - lenSum L) < ε / 2 := by
      have : 1 - lenSum L < ε / (2 * (t : ℝ)) := by linarith
      have := mul_lt_mul_of_pos_left this htpos
      have heq : (t : ℝ) * (ε / (2 * (t : ℝ))) = ε / 2 := by field_simp [htpos.ne']
      linarith
    have hgap2 : (t : ℝ) * (4 * ((L.length : ℝ) + 1) / N) < ε / 2 := by
      have hNM : (2 * (M : ℝ) + 1) ≤ N := by
        dsimp [N]
        have : 2 * M + 1 ≤ 2 * m + 1 := by omega
        exact_mod_cast this
      have hbig : 8 * (t : ℝ) * ((L.length : ℝ) + 1) / ε < N := by
        have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        linarith
      have hmul : 8 * (t : ℝ) * ((L.length : ℝ) + 1) < N * ε := (div_lt_iff₀ hε).mp hbig
      have heq : (t : ℝ) * (4 * ((L.length : ℝ) + 1) / N) =
          (4 * (t : ℝ) * ((L.length : ℝ) + 1)) / N := by ring
      rw [heq, div_lt_div_iff₀ hNpos (by norm_num)]
      linarith
    linarith

end

end Arxiv250103234H2

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_4_4_R1.H2 :=
  Arxiv250103234H2.main_theorem
