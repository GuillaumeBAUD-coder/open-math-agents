import OMAStatements.S_mo_321567
import Mathlib

namespace OMA.P321567
open Finset OMA.S_mo_321567

section Geo
variable {p : ℕ} [Fact p.Prime]

lemma label_point (s : Dir p) (a t : ZMod p) : label s (point s a t) = a := by
  cases s <;> simp [label, point]

def coord (s : Dir p) (x : Pt p) : ZMod p := s.elim x.2 (fun _ => x.1)

def eqv (s : Dir p) : ZMod p × ZMod p ≃ Pt p where
  toFun q := point s q.1 q.2
  invFun y := (label s y, coord s y)
  left_inv q := by cases s <;> simp [label, point, coord]
  right_inv y := by cases s <;> simp [label, point, coord]

lemma sum_pt (s : Dir p) (f : Pt p → ℝ) : ∑ x, f x = ∑ a, ∑ t, f (point s a t) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (eqv s) _ _ (fun _ => rfl)).symm

lemma label_point_bij {s s' : Dir p} (h : s ≠ s') (a : ZMod p) :
    Function.Bijective (fun t => label s' (point s a t)) := by
  rw [← Finite.injective_iff_bijective]
  intro t1 t2 ht
  cases s with
  | none => cases s' with
    | none => exact absurd rfl h
    | some m' => simpa [label, point] using ht
  | some m => cases s' with
    | none => simpa [label, point] using ht
    | some m' =>
      have hm : m - m' ≠ 0 := sub_ne_zero.mpr (fun e => h (by rw [e]))
      simp only [label, point, Option.elim] at ht
      have : (m - m') * t1 = (m - m') * t2 := by linear_combination ht
      exact mul_left_cancel₀ hm this

lemma p_ne : (p : ℝ) ≠ 0 := by
  have := (Fact.out : p.Prime).pos
  positivity

lemma card_dir : (univ : Finset (Dir p)).card = p + 1 := by
  simp [Finset.card_univ, Fintype.card_option, ZMod.card]

lemma sum_line_assemble (c : ℝ) (g : Dir p → ZMod p → ℝ) (hg : centered g) (s : Dir p)
    (a : ZMod p) : ∑ t, assemble c g (point s a t) = p * (c + g s a) := by
  simp only [assemble]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, Finset.sum_comm]
  rw [Finset.sum_eq_single s]
  · simp [label_point, ZMod.card]; ring
  · intro s' _ hs'
    rw [(label_point_bij (Ne.symm hs') a).sum_comp (g s')]
    exact hg s'
  · simp

lemma lineMean_assemble (c : ℝ) (g : Dir p → ZMod p → ℝ) (hg : centered g) (s : Dir p)
    (a : ZMod p) : lineMean (assemble c g) s a = c + g s a := by
  unfold lineMean
  rw [sum_line_assemble c g hg]
  field_simp [p_ne (p := p)]

lemma mean_assemble (c : ℝ) (g : Dir p → ZMod p → ℝ) (hg : centered g) :
    mean (assemble c g) = c := by
  unfold mean
  rw [sum_pt none]
  simp_rw [sum_line_assemble c g hg]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hg none]
  simp [ZMod.card]
  field_simp [p_ne (p := p)]

lemma sum_lineMean (w : Pt p → ℝ) (s : Dir p) : ∑ a, lineMean w s a = (∑ x, w x) / p := by
  unfold lineMean
  rw [← Finset.sum_div, ← sum_pt s]

lemma line_as_filter (w : Pt p → ℝ) (s : Dir p) (x : Pt p) :
    ∑ t, w (point s (label s x) t) = ∑ y, if label s y = label s x then w y else 0 := by
  rw [sum_pt s (fun y => if label s y = label s x then w y else 0)]
  simp only [label_point]
  simp

lemma count_dirs (x y : Pt p) :
    ∑ s : Dir p, (if label s y = label s x then (1 : ℝ) else 0) = 1 + if y = x then (p : ℝ) else 0 := by
  rw [Fintype.sum_option]
  simp only [label, Option.elim]
  by_cases hyx : y = x
  · subst hyx; simp [ZMod.card]
  · by_cases h1 : y.1 = x.1
    · have h2 : y.2 ≠ x.2 := fun h2 => hyx (Prod.ext h1 h2)
      simp [h1, h2, hyx]
    · have hne : y.1 - x.1 ≠ 0 := sub_ne_zero.mpr h1
      have key : ∀ m : ZMod p, (y.2 - m * y.1 = x.2 - m * x.1) ↔ m = (y.2 - x.2) / (y.1 - x.1) := by
        intro m
        rw [eq_div_iff hne]
        constructor <;> intro h <;> linear_combination (-1 : ZMod p) * h
      simp only [key, h1, hyx]
      simp

lemma sum_lines_through (w : Pt p → ℝ) (x : Pt p) :
    ∑ s, lineMean w s (label s x) = w x + (∑ y, w y) / p := by
  unfold lineMean
  rw [← Finset.sum_div]
  simp_rw [line_as_filter w _ x]
  rw [Finset.sum_comm]
  have : ∀ y, (∑ s : Dir p, if label s y = label s x then w y else 0)
      = w y * (1 + if y = x then (p : ℝ) else 0) := by
    intro y
    rw [← count_dirs x y, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs <;> simp
  simp_rw [this, mul_add, mul_one, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq']
  simp
  field_simp [p_ne (p := p)]
  ring

theorem part1b (w : Pt p → ℝ) (c : ℝ) (g : Dir p → ZMod p → ℝ) (hg : centered g)
    (hw : w = assemble c g) :
    c = mean w ∧ (∀ s a, g s a = lineMean w s a - mean w) ∧
      (∀ k : ℕ, w ∈ admissible k ↔
        (∀ x, 0 ≤ assemble c g x) ∧ (active g).card + k ≤ p+1) := by
  subst hw
  refine ⟨(mean_assemble c g hg).symm, fun s a => ?_, fun k => ?_⟩
  · rw [lineMean_assemble c g hg, mean_assemble c g hg]; ring
  · have hev : evens (assemble c g) = univ.filter (fun s => ¬ (g s ≠ 0)) := by
      ext s
      simp only [evens, mem_filter, mem_univ, true_and, lineMean_assemble c g hg,
        mean_assemble c g hg, add_eq_left, not_not, funext_iff, Pi.zero_apply]
    have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Dir p)))
      (fun s => g s ≠ 0)
    rw [card_dir] at hc
    simp only [admissible, Set.mem_ofPred_eq, hev]
    unfold active
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      omega
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      omega

theorem part1 (w : Pt p → ℝ) :
    (∃! cg : ℝ × (Dir p → ZMod p → ℝ), centered cg.2 ∧ w = assemble cg.1 cg.2) ∧
      (∀ c g, centered g → w = assemble c g →
        c = mean w ∧ (∀ s a, g s a = lineMean w s a - mean w) ∧
        (∀ k : ℕ, w ∈ admissible k ↔
          (∀ x, 0 ≤ assemble c g x) ∧ (active g).card + k ≤ p+1)) := by
  refine ⟨?_, fun c g hg hw => part1b w c g hg hw⟩
  refine ⟨(mean w, fun s a => lineMean w s a - mean w), ⟨?_, ?_⟩, ?_⟩
  · intro s
    simp only
    rw [Finset.sum_sub_distrib, sum_lineMean]
    simp [ZMod.card, mean]
    field_simp [p_ne (p := p)]
    ring
  · funext x
    simp only [assemble]
    rw [Finset.sum_sub_distrib, sum_lines_through]
    simp [mean]
    field_simp [p_ne (p := p)]
    ring
  · rintro ⟨c, g⟩ ⟨hg, hw⟩
    obtain ⟨h1, h2, -⟩ := part1b w c g hg hw
    rw [h1]
    congr
    funext s a
    exact h2 s a


noncomputable def h0 (p : ℕ) : ZMod p → ℝ := fun a => (if a = 0 then 1 else 0) - 1 / p

noncomputable def gS {p : ℕ} (S : Finset (Dir p)) : Dir p → ZMod p → ℝ := fun s => if s ∈ S then h0 p else 0

lemma h0_sum : ∑ a, h0 p a = 0 := by
  simp only [h0]
  rw [Finset.sum_sub_distrib]
  simp [ZMod.card]

lemma h0_pos : 0 < h0 p 0 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  simp only [h0, if_true]
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

lemma h0_ge (a : ZMod p) : -1 ≤ h0 p a := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  simp only [h0]
  split_ifs <;> linarith

lemma active_eq (g : Dir p → ZMod p → ℝ) (S : Finset (Dir p))
    (h1 : ∀ s, s ∉ S → g s = 0) (h2 : ∀ s, s ∈ S → g s 0 ≠ 0) : active g = S := by
  ext s
  simp only [active, mem_filter, mem_univ, true_and]
  constructor
  · intro hs
    by_contra hn
    exact hs (h1 s hn)
  · intro hs he
    exact h2 s hs (by rw [he]; rfl)

lemma nonneg_of_ge (g : Dir p → ZMod p → ℝ) (hg : ∀ s a, -1 ≤ g s a) (x : Pt p) :
    0 ≤ assemble ((p : ℝ) + 2) g x := by
  unfold assemble
  have : ∑ s : Dir p, (-1 : ℝ) ≤ ∑ s, g s (label s x) :=
    Finset.sum_le_sum (fun s _ => hg s _)
  rw [Finset.sum_const, card_dir, nsmul_eq_mul] at this
  push_cast at this
  linarith

lemma gS_centered (S : Finset (Dir p)) : centered (gS S) := by
  intro s
  unfold gS
  split_ifs
  · exact h0_sum
  · simp

lemma gS_ge (S : Finset (Dir p)) (s : Dir p) (a : ZMod p) : -1 ≤ gS S s a := by
  unfold gS
  split_ifs
  · exact h0_ge a
  · simp

lemma gS_active (S : Finset (Dir p)) : active (gS S) = S := by
  apply active_eq
  · intro s hs; simp [gS, hs]
  · intro s hs; simp only [gS, if_pos hs]; exact h0_pos.ne'

theorem part2 (k : ℕ) (hk3 : 3 ≤ k) (hk : k ≤ p) : ¬ Convex ℝ (@admissible p _ k) := by
  intro hconv
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Dir p)))
    (n := p + 2 - k) (by rw [card_dir]; omega)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  set S1 := T.erase a
  set S2 := T.erase b
  have c1 : S1.card = p + 1 - k := by rw [Finset.card_erase_of_mem ha]; omega
  have c2 : S2.card = p + 1 - k := by rw [Finset.card_erase_of_mem hb]; omega
  have hU : S1 ∪ S2 = T := by
    ext x
    simp only [S1, S2, mem_union, mem_erase]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro hx
      by_cases hxa : x = a
      · subst hxa; exact Or.inr ⟨hab, hx⟩
      · exact Or.inl ⟨hxa, hx⟩
  have adm : ∀ S : Finset (Dir p), S.card = p + 1 - k →
      assemble ((p : ℝ) + 2) (gS S) ∈ @admissible p _ k := by
    intro S hS
    rw [((part1b _ _ _ (gS_centered S) rfl).2.2 k)]
    refine ⟨nonneg_of_ge _ (gS_ge S), ?_⟩
    rw [gS_active, hS]
    omega
  have hm := hconv (adm S1 c1) (adm S2 c2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  set gm : Dir p → ZMod p → ℝ := fun s a => (1 / 2) * (gS S1 s a + gS S2 s a)
  have hmid : (1 / 2 : ℝ) • assemble ((p : ℝ) + 2) (gS S1) + (1 / 2 : ℝ) • assemble ((p : ℝ) + 2) (gS S2)
      = assemble ((p : ℝ) + 2) gm := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, assemble, gm, mul_add,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have gm_c : centered gm := by
    intro s
    simp only [gm]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, gS_centered S1 s, gS_centered S2 s]
    simp
  have gm_a : active gm = S1 ∪ S2 := by
    apply active_eq
    · intro s hs
      rw [mem_union, not_or] at hs
      funext a
      simp [gm, gS, hs.1, hs.2]
    · intro s hs
      have hp := (h0_pos (p := p))
      simp only [gm, gS]
      rcases mem_union.mp hs with h | h
      · by_cases h' : s ∈ S2
        · simp only [if_pos h, if_pos h']; positivity
        · simp only [if_pos h, if_neg h']; simp; exact hp.ne'
      · by_cases h' : s ∈ S1
        · simp only [if_pos h, if_pos h']; positivity
        · simp only [if_pos h, if_neg h']; simp; exact hp.ne'
  rw [hmid, ((part1b _ _ _ gm_c rfl).2.2 k), gm_a, hU, hT] at hm
  omega

end Geo


theorem part3 : (∀ i : Fin 5, (univ.filter (fun j => support5 i j)).card=2) ∧
     (∀ j : Fin 5, (univ.filter (fun i => support5 i j)).card=2) ∧
     (∀ a : Fin 5, (univ.filter (fun i => support5 i (a+i))).card=2) ∧
     ¬∃ f : Fin 5 → Fin 5, Function.Injective f ∧ Function.Injective (fun i => f i-i) ∧
        ∀ i, support5 i (f i) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨f, hf, hg, hs⟩
  have key : ∀ i, f i = permA i ∨ f i = permB i := fun i => by simpa [support5] using hs i
  obtain ⟨c, hc⟩ : ∃ c : Fin 5 → Bool, f = fun i => if c i then permA i else permB i := by
    refine ⟨fun i => decide (f i = permA i), ?_⟩
    funext i
    by_cases h : f i = permA i
    · simp [h]
    · simp [h]; exact (key i).resolve_left h
  subst hc
  revert hf hg
  revert c
  decide

end OMA.P321567

theorem OMA.solution : type_of% @OMA.S_mo_321567.main := by
  refine ⟨fun p _ w => OMA.P321567.part1 w, fun p _ k h3 hk => OMA.P321567.part2 k h3 hk,
    OMA.P321567.part3⟩
