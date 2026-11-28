import OMAStatements.S_oeis_a026364

-- Credit: @RiverMint78

/-!
Give each zero weight 1 + sqrt(3) and each one weight -1. Substitution
multiplies the weight of a full word by 1 - sqrt(3). The possible initial
segments of a substituted letter preserve separate weight intervals at
positions immediately before a zero and before a one.
-/

namespace A026364Proof

open OMA.S_oeis_a026364

private def image (b : Bool) : List Bool :=
  if b then [true, false, true] else [true, true]

private theorem step_cons (b : Bool) (w : List Bool) :
    morphStep (b :: w) = image b ++ morphStep w := rfl

private theorem step_append (u v : List Bool) :
    morphStep (u ++ v) = morphStep u ++ morphStep v := by
  simp [morphStep, List.flatMap_append]

private noncomputable def r : ℝ := Real.sqrt 3

private noncomputable def decay : ℝ := 1 - r

private theorem r_sq : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem r_gt_one : 1 < r := by
  exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)

private theorem r_lt_two : r < 2 := by
  exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)

private theorem decay_neg : decay < 0 := sub_neg.mpr r_gt_one

private noncomputable def weight (b : Bool) : ℝ := if b then -1 else 1 + r

private noncomputable def score (w : List Bool) : ℝ := (w.map weight).sum

private theorem score_append (u v : List Bool) : score (u ++ v) = score u + score v := by
  simp [score]

private theorem image_score (b : Bool) : score (image b) = decay * weight b := by
  cases b <;> simp [image, score, weight, decay] <;> nlinarith [r_sq]

private theorem step_score (w : List Bool) : score (morphStep w) = decay * score w := by
  induction w with
  | nil => simp [morphStep, score]
  | cons b w ih =>
      rw [step_cons, score_append, image_score, ih]
      change decay * weight b + decay * score w = decay * (weight b + score w)
      rw [mul_add]

private def before (b : Bool) (z : ℝ) : Prop :=
  if b then -(1 + r) < z ∧ z < 2 + r else -(2 + r) < z ∧ z < 1

private theorem image_prefixes (c b : Bool) (u v : List Bool) (h : image c = u ++ b :: v) :
    (b = true ∧ score u = 0) ∨
    (c = false ∧ b = true ∧ score u = -1) ∨
    (c = true ∧ b = false ∧ score u = -1) ∨
    (c = true ∧ b = true ∧ score u = r) := by
  rcases u with _ | ⟨a, _ | ⟨d, _ | ⟨e, u⟩⟩⟩ <;>
    cases c <;> cases b <;> simp_all [image, score, weight]
  rw [← h.2]
  simp [weight]

private theorem image_preserves (c b : Bool) (u v : List Bool) (h : image c = u ++ b :: v)
    {z : ℝ} (hb : before c z) : before b (decay * z + score u) := by
  have e0 : decay * (-(2 + r)) = 1 + r := by
    unfold decay
    nlinarith [r_sq]
  have e1 : decay * (-(1 + r)) = 2 := by
    unfold decay
    nlinarith [r_sq]
  have e2 : decay * (2 + r) = -(1 + r) := by
    unfold decay
    nlinarith [r_sq]
  have e3 : decay = 1 - r := rfl
  have hr₁ := r_gt_one
  have hr₂ := r_lt_two
  rcases image_prefixes c b u v h with ⟨rfl, hs⟩ | ⟨rfl, rfl, hs⟩ |
    ⟨rfl, rfl, hs⟩ | ⟨rfl, rfl, hs⟩
  · cases c <;> rw [hs] <;> simp only [before, Bool.false_eq_true, if_false] at hb ⊢
    all_goals
      have lower := mul_lt_mul_of_neg_left hb.2 decay_neg
      have upper := mul_lt_mul_of_neg_left hb.1 decay_neg
      simp only [mul_one, e0, e1, e2] at lower upper
      rw [e3] at lower upper ⊢
      constructor <;> linarith
  all_goals
    rw [hs]
    simp only [before, Bool.false_eq_true, if_false] at hb ⊢
    have lower := mul_lt_mul_of_neg_left hb.2 decay_neg
    have upper := mul_lt_mul_of_neg_left hb.1 decay_neg
    simp only [mul_one, e0, e1, e2] at lower upper
    rw [e3] at lower upper ⊢
    constructor <;> linarith

/-- Locate a letter of the substituted word in the image of one source letter. -/
private theorem split_image (w u v : List Bool) (b : Bool)
    (h : morphStep w = u ++ b :: v) :
    ∃ p c s q t, w = p ++ c :: s ∧ image c = q ++ b :: t ∧ u = morphStep p ++ q := by
  induction w generalizing u v with
  | nil => simp [morphStep] at h
  | cons c w ih =>
      rw [step_cons] at h
      rcases List.append_eq_append_iff.mp h with ⟨rem, hu, hw⟩ | ⟨rem, hc, hr⟩
      · obtain ⟨p, d, s, q, t, hp, hd, hq⟩ := ih rem v hw
        refine ⟨c :: p, d, s, q, t, ?_, hd, ?_⟩
        · exact congrArg (List.cons c) hp
        · rw [hu, hq, step_cons, List.append_assoc]
      · cases rem with
        | nil =>
            obtain ⟨p, d, s, q, t, hp, hd, hq⟩ := ih [] v (by simpa using hr.symm)
            refine ⟨c :: p, d, s, q, t, congrArg (List.cons c) hp, hd, ?_⟩
            rw [step_cons, List.append_assoc, ← hq]
            simpa using hc.symm
        | cons e rem =>
            have he : b = e := (List.cons.inj hr).1
            subst e
            exact ⟨[], c, w, u, rem, rfl, hc, rfl⟩

private def word (m : ℕ) : List Bool := (morphStep^[m]) [true]

private theorem word_succ (m : ℕ) : word (m + 1) = morphStep (word m) :=
  Function.iterate_succ_apply' _ _ _

private theorem word_bounds (m : ℕ) (u v : List Bool) (b : Bool)
    (h : word m = u ++ b :: v) : before b (score u) := by
  induction m generalizing u v b with
  | zero =>
      change [true] = u ++ b :: v at h
      have hl := congrArg List.length h
      have hu : u = [] := List.length_eq_zero_iff.mp (by simp at hl; omega)
      subst u
      have hb : b = true := (List.cons.inj h).1.symm
      subst b
      have hr := r_gt_one
      simpa [score, before] using (show -(1 + r) < (0 : ℝ) ∧ 0 < 2 + r from
        ⟨by linarith, by linarith⟩)
  | succ m ih =>
      rw [word_succ] at h
      obtain ⟨p, c, s, q, t, hp, hc, hq⟩ := split_image (word m) u v b h
      rw [hq, score_append, step_score]
      exact image_preserves c b q t hc (ih p s c hp)

private theorem step_prefix {u v : List Bool} (h : u <+: v) :
    morphStep u <+: morphStep v := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨morphStep w, (step_append _ _).symm⟩

private theorem word_prefix_succ (m : ℕ) : word m <+: word (m + 1) := by
  induction m with
  | zero => exact ⟨[false, true], rfl⟩
  | succ m ih =>
      rw [word_succ (m + 1), word_succ m]
      exact step_prefix (by simpa only [word_succ m] using ih)

private theorem word_prefix {m n : ℕ} (h : m ≤ n) : word m <+: word n := by
  induction h with
  | refl => exact ⟨[], List.append_nil _⟩
  | step _ ih => exact ih.trans (word_prefix_succ _)

private theorem step_length (v : List Bool) : 2 * v.length ≤ (morphStep v).length := by
  induction v with
  | nil => simp
  | cons b v ih =>
      rw [step_cons, List.length_append]
      cases b <;> simp [image] <;> omega

private theorem word_length (m : ℕ) : m + 1 ≤ (word m).length := by
  induction m with
  | zero => decide
  | succ m ih =>
      have h := step_length (word m)
      rw [word_succ]
      omega

private theorem getD_prefix {u v : List Bool} (hp : u <+: v) {k : ℕ}
    (hk : k < u.length) : u.getD k true = v.getD k true := by
  simpa only [List.getElem_eq_getD true] using hp.getElem hk

private theorem word_agrees (m k : ℕ) (hk : k < (word m).length) :
    (word m).getD k true = fixedPoint k := by
  change (word m).getD k true = (word (k + 1)).getD k true
  rcases le_total m (k + 1) with h | h
  · exact getD_prefix (word_prefix h) hk
  · exact (getD_prefix (word_prefix h) (by have := word_length (k + 1); omega)).symm

private theorem word_final (m : ℕ) : ∃ u, word m = u ++ [true] := by
  induction m with
  | zero => exact ⟨[], rfl⟩
  | succ m ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨morphStep u ++ [true, false], ?_⟩
      rw [word_succ, hu, step_append, List.append_assoc]
      rfl

private abbrev zeroAt (k : ℕ) : Prop := fixedPoint k = false

private theorem zeros_infinite : (Set.ofPred zeroAt).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨u, hu⟩ := word_final (n + 2)
  let k := (morphStep u).length + 1
  have hw : word (n + 3) = (morphStep u ++ [true]) ++ false :: [true] := by
    rw [show n + 3 = (n + 2) + 1 by omega, word_succ, hu, step_append, List.append_assoc]
    rfl
  have hl : (word (n + 3)).length = k + 2 := by
    simp [hw, k]
  have hlarge := word_length (n + 3)
  have hget : (word (n + 3)).getD k true = false := by
    rw [hw, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [k])]
    simp [k]
  exact ⟨k, (word_agrees _ k (by omega)).symm.trans hget, by omega⟩

private theorem score_take (m k : ℕ) (hk : k ≤ (word m).length) :
    score ((word m).take k) = (Nat.count zeroAt k : ℝ) * (2 + r) - (k : ℝ) := by
  induction k with
  | zero => simp [score]
  | succ k ih =>
      have hlt : k < (word m).length := by omega
      have hget : (word m)[k] = fixedPoint k :=
        (List.getElem_eq_getD true).trans (word_agrees m k hlt)
      rw [List.take_succ_eq_append_getElem hlt, score_append, ih (by omega),
        hget, Nat.count_succ]
      by_cases h : zeroAt k
      · rw [if_pos h, show fixedPoint k = false from h]
        simp [score, weight, Nat.cast_add]
        ring
      · have ht : fixedPoint k = true := by
          cases he : fixedPoint k
          · exact (h he).elim
          · rfl
        rw [if_neg h, ht]
        simp [score, weight, Nat.cast_add]
        ring

end A026364Proof

open A026364Proof OMA.S_oeis_a026364 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026364.main := by
  intro n hn
  let k := Nat.nth zeroAt (n - 1)
  have hz : fixedPoint k = false := Nat.nth_mem_of_infinite zeros_infinite _
  have hcount : Nat.count zeroAt k + 1 = n := by
    rw [Nat.count_nth_of_infinite zeros_infinite (n - 1)]
    omega
  have hk : k < (word (k + 1)).length := by
    have h := word_length (k + 1)
    omega
  have hget : (word (k + 1))[k] = false := by
    exact (List.getElem_eq_getD true).trans ((word_agrees _ k hk).trans hz)
  have hsplit : word (k + 1) = (word (k + 1)).take k ++ false :: (word (k + 1)).drop (k + 1) := by
    have h := (List.take_append_drop k (word (k + 1))).symm
    rwa [List.drop_eq_getElem_cons hk, hget] at h
  have hb := word_bounds (k + 1) _ _ false hsplit
  simp only [before, Bool.false_eq_true, if_false] at hb
  rw [score_take (k + 1) k hk.le] at hb
  have hnR : (Nat.count zeroAt k : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hcount
  have ha : a n = k + 1 := rfl
  have hr := r_lt_two
  rw [ha, Nat.cast_add, Nat.cast_one, ← hnR]
  change -1 < ((Nat.count zeroAt k : ℝ) + 1) * (2 + r) - ((k : ℝ) + 1) ∧
    ((Nat.count zeroAt k : ℝ) + 1) * (2 + r) - ((k : ℝ) + 1) < 4
  constructor <;> linarith [hb.1, hb.2]
