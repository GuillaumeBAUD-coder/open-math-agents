import OMAStatements.S_oeis_a107793

-- Problem: A107793: Differences between successive indices of 1's in the ternary tribonacci sequence A305390.
-- Upstream: formal-conjectures statements/oeis-a107793.lean:0 (declaration OMA.S_oeis_a107793.main)
-- Credit: Daniel Whorlow (@draonbioetl)
-- Disproof of N. J. A. Sloane's 2018 conjecture: M and t have the same subword language
-- (every finite prefix of M occurs in t, e.g. M[0..1701] = t[329..2030]),
-- yet M satisfies M = sigma([5, 6] ++ M) while t satisfies t = sigma(t).
-- By unique desubstitution of sigma (3 marks codeword boundaries and codeword lengths
-- 4, 6, 7 are distinct), any integer shift s yields a strictly smaller shift, giving
-- a contradiction by infinite descent.

namespace OMA_A107793

open OMA.S_oeis_a107793

private def fStep (w : List ℕ) : List ℕ := w.flatMap f
private def f3Step (w : List ℕ) : List ℕ := fStep (fStep (fStep w))
private def sigmaStep (w : List ℕ) : List ℕ := w.flatMap sigma

private def phi : ℕ → List ℕ
  | 3 => [1, 2, 3]
  | 5 => [1, 2, 3, 3]
  | 6 => [1, 2, 3, 2, 3]
  | _ => []

private def tau : ℕ → List ℕ
  | 3 => [6, 5, 6, 3]
  | 5 => [6, 5, 6, 5, 6, 3]
  | 6 => [6, 5, 6, 6, 5, 6, 3]
  | _ => []

private def GoodLetter (c : ℕ) : Prop := c = 3 ∨ c = 5 ∨ c = 6

private def W' : ℕ → List ℕ
  | 0 => []
  | k + 1 => [5, 6] ++ sigmaStep (W' k ++ [3])

private lemma fStep_append (a b : List ℕ) : fStep (a ++ b) = fStep a ++ fStep b :=
  List.flatMap_append

private lemma f3Step_append (a b : List ℕ) : f3Step (a ++ b) = f3Step a ++ f3Step b := by
  simp [f3Step, fStep_append]

private lemma sigmaStep_append (a b : List ℕ) :
    sigmaStep (a ++ b) = sigmaStep a ++ sigmaStep b :=
  List.flatMap_append

private lemma S_add_three (n : ℕ) : S (n + 3) = f3Step (S n) := by
  simp [S, f3Step, fStep, Function.iterate_succ_apply']

private lemma T_succ (k : ℕ) : T (k + 1) = sigmaStep (T k) := by
  simp [T, sigmaStep, Function.iterate_succ_apply']

private lemma sigma_good {c : ℕ} (hc : GoodLetter c) :
    ∀ x ∈ sigma c, GoodLetter x := by
  rcases hc with rfl | rfl | rfl <;> intro x hx <;> simp [sigma, GoodLetter] at hx ⊢ <;> omega

private lemma sigmaStep_good {w : List ℕ} (hw : ∀ x ∈ w, GoodLetter x) :
    ∀ x ∈ sigmaStep w, GoodLetter x := by
  intro x hx
  rw [sigmaStep, List.mem_flatMap] at hx
  rcases hx with ⟨c, hc, hxc⟩
  exact sigma_good (hw c hc) x hxc

private lemma W'_good (k : ℕ) : ∀ x ∈ W' k, GoodLetter x := by
  induction k with
  | zero => intro x hx; cases hx
  | succ k ih =>
    intro x hx
    rw [W', List.mem_append] at hx
    rcases hx with hx | hx
    · simp [GoodLetter] at hx ⊢; omega
    · refine sigmaStep_good ?_ x hx
      intro y hy
      rw [List.mem_append] at hy
      rcases hy with hy | hy
      · exact ih y hy
      · simp at hy; exact Or.inl hy

private lemma T_good (k : ℕ) : ∀ x ∈ T k, GoodLetter x := by
  induction k with
  | zero =>
    intro x hx
    simp [T, GoodLetter] at hx ⊢
    omega
  | succ k ih =>
    rw [T_succ]
    exact sigmaStep_good ih

private lemma tau_conj_sigma {c : ℕ} (hc : GoodLetter c) :
    3 :: tau c = sigma c ++ [3] := by
  rcases hc with rfl | rfl | rfl <;> rfl

private lemma tau_flatMap_conj_sigma {w : List ℕ} (hw : ∀ x ∈ w, GoodLetter x) :
    3 :: w.flatMap tau = sigmaStep w ++ [3] := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    have hc : GoodLetter c := hw c (by simp)
    have hcs : ∀ x ∈ cs, GoodLetter x := fun x hx => hw x (by simp [hx])
    have ih' := ih hcs
    calc
      3 :: (c :: cs).flatMap tau
          = (3 :: tau c) ++ cs.flatMap tau := by simp [List.flatMap_cons]
      _ = (sigma c ++ [3]) ++ cs.flatMap tau := by rw [tau_conj_sigma hc]
      _ = sigma c ++ (3 :: cs.flatMap tau) := by simp [List.append_assoc]
      _ = sigma c ++ (sigmaStep cs ++ [3]) := by rw [ih']
      _ = sigmaStep (c :: cs) ++ [3] := by simp [sigmaStep, List.flatMap_cons, List.append_assoc]

private lemma f3Step_phi {c : ℕ} (hc : GoodLetter c) :
    f3Step (phi c) = (tau c).flatMap phi := by
  rcases hc with rfl | rfl | rfl <;> decide

private lemma f3Step_flatMap_phi {w : List ℕ} (hw : ∀ x ∈ w, GoodLetter x) :
    f3Step (w.flatMap phi) = (w.flatMap tau).flatMap phi := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    have hc : GoodLetter c := hw c (by simp)
    have hcs : ∀ x ∈ cs, GoodLetter x := fun x hx => hw x (by simp [hx])
    simp only [List.flatMap_cons, f3Step_append, f3Step_phi hc, ih hcs, List.flatMap_append]

private lemma f3Step_two_three :
    f3Step [2, 3] = [2, 3] ++ ([5, 6, 3] : List ℕ).flatMap phi := by
  decide

private lemma S_block (k : ℕ) :
    S (3 * (k + 1) + 1) = [2, 3] ++ (W' k ++ [3]).flatMap phi := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hidx : 3 * (k + 1 + 1) + 1 = (3 * (k + 1) + 1) + 3 := by omega
    rw [hidx, S_add_three, ih, f3Step_append, f3Step_two_three]
    have hgood : ∀ x ∈ W' k ++ [3], GoodLetter x := by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact W'_good k x hx
      · simp at hx; exact Or.inl hx
    rw [f3Step_flatMap_phi hgood, List.append_assoc, ← List.flatMap_append]
    congr 1
    have hconj := tau_flatMap_conj_sigma hgood
    have hlist : ([5, 6, 3] : List ℕ) ++ (W' k ++ [3]).flatMap tau =
        ([5, 6] ++ sigmaStep (W' k ++ [3])) ++ [3] := by
      change [5, 6] ++ (3 :: (W' k ++ [3]).flatMap tau) = _
      rw [hconj, List.append_assoc]
    rw [hlist]
    rfl

private lemma sigma_prefix_3656 {c : ℕ} (hc : GoodLetter c) :
    ([3, 6, 5, 6] : List ℕ) <+: sigma c := by
  rcases hc with rfl | rfl | rfl
  · exact ⟨[], by rfl⟩
  · exact ⟨[5, 6], by rfl⟩
  · exact ⟨[6, 5, 6], by rfl⟩

private lemma sigma_len_ge_four {c : ℕ} (hc : GoodLetter c) :
    4 ≤ (sigma c).length := by
  rcases hc with rfl | rfl | rfl <;> decide

private lemma sigmaStep_prefix_mono {a b : List ℕ} (h : a <+: b) :
    sigmaStep a <+: sigmaStep b := by
  rcases h with ⟨t, rfl⟩
  exact ⟨sigmaStep t, (sigmaStep_append a t).symm⟩

private lemma W'_strict_prefix (k : ℕ) :
    ∃ r, r ≠ [] ∧ W' (k + 1) = W' k ++ r := by
  induction k with
  | zero =>
    refine ⟨[5, 6, 3, 6, 5, 6], by simp, ?_⟩
    decide
  | succ k ih =>
    rcases ih with ⟨r, hr, hEq⟩
    cases r with
    | nil => exact absurd rfl hr
    | cons c cs =>
      have hc : GoodLetter c := by
        apply W'_good (k + 1) c
        rw [hEq]
        simp
      obtain ⟨t, ht⟩ := sigma_prefix_3656 hc
      have hsig : sigmaStep (W' (k + 1) ++ [3]) =
          sigmaStep (W' k) ++ [3, 6, 5, 6] ++ (t ++ sigmaStep cs ++ sigmaStep [3]) := by
        rw [hEq]
        simp only [sigmaStep, List.flatMap_append, List.flatMap_cons, List.append_assoc]
        rw [← ht]
        simp
      have hWk1 : W' (k + 1) = [5, 6] ++ sigmaStep (W' k) ++ [3, 6, 5, 6] := by
        simp [W', sigmaStep, sigma]
      refine ⟨t ++ sigmaStep cs ++ sigmaStep [3], ?_, ?_⟩
      · intro hnil
        have h3 : sigmaStep [3] ≠ [] := by decide
        have hlen := congrArg List.length hnil
        simp [sigmaStep, sigma] at hlen
      · rw [W', hsig, hWk1]
        simp [List.append_assoc]

private lemma W'_prefix_mono {j k : ℕ} (h : j ≤ k) : W' j <+: W' k := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rcases W'_strict_prefix _ with ⟨r, _, hr⟩
    exact ih.trans ⟨r, hr.symm⟩

private lemma W'_length_ge (k : ℕ) : k ≤ (W' k).length := by
  induction k with
  | zero => simp [W']
  | succ k ih =>
    rcases W'_strict_prefix k with ⟨r, hr, hEq⟩
    have hrpos : 1 ≤ r.length := List.length_pos_of_ne_nil hr
    rw [hEq, List.length_append]
    omega

private lemma T_prefix_succ (k : ℕ) : T k <+: T (k + 1) := by
  induction k with
  | zero =>
    exact ⟨[6, 5, 6], by decide⟩
  | succ k ih =>
    rw [T_succ, T_succ]
    exact sigmaStep_prefix_mono ih

private lemma T_prefix_mono {j k : ℕ} (h : j ≤ k) : T j <+: T k := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (T_prefix_succ _)

private lemma T_length_ge (k : ℕ) : k + 1 ≤ (T k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [T_succ]
    have hge : ∀ w : List ℕ, (∀ x ∈ w, GoodLetter x) → 4 * w.length ≤ (sigmaStep w).length := by
      intro w hw
      induction w with
      | nil => simp [sigmaStep]
      | cons c cs ihw =>
        have hc := sigma_len_ge_four (hw c (by simp))
        have hcs := ihw (fun x hx => hw x (by simp [hx]))
        simp only [sigmaStep, List.flatMap_cons, List.length_append, List.length_cons] at hcs ⊢
        omega
    have h4 := hge (T k) (T_good k)
    omega

private lemma fStep_prefix_mono {a b : List ℕ} (h : a <+: b) : fStep a <+: fStep b := by
  rcases h with ⟨t, rfl⟩
  exact ⟨fStep t, (fStep_append a t).symm⟩

private lemma f3Step_prefix_mono {a b : List ℕ} (h : a <+: b) : f3Step a <+: f3Step b :=
  fStep_prefix_mono (fStep_prefix_mono (fStep_prefix_mono h))

private lemma S_prefix_step (k : ℕ) : S (3 * k + 1) <+: S (3 * (k + 1) + 1) := by
  induction k with
  | zero => exact ⟨[3, 1, 2, 3], by decide⟩
  | succ k ih =>
    have h1 : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by omega
    have h2 : 3 * (k + 1 + 1) + 1 = (3 * (k + 1) + 1) + 3 := by omega
    rw [h1, h2, S_add_three, S_add_three]
    exact f3Step_prefix_mono ih

private lemma S_prefix_mono {j k : ℕ} (h : j ≤ k) : S (3 * j + 1) <+: S (3 * k + 1) := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (S_prefix_step _)

private lemma phi_len_ge_three {c : ℕ} (hc : GoodLetter c) : 3 ≤ (phi c).length := by
  rcases hc with rfl | rfl | rfl <;> decide

private lemma flatMap_phi_len_ge {w : List ℕ} (hw : ∀ x ∈ w, GoodLetter x) :
    3 * w.length ≤ (w.flatMap phi).length := by
  induction w with
  | nil => simp
  | cons c cs ih =>
    have hc := phi_len_ge_three (hw c (by simp))
    have hcs := ih (fun x hx => hw x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at hcs ⊢
    omega

private lemma S_length_gt (k : ℕ) : k < (S (3 * k + 1)).length := by
  cases k with
  | zero => decide
  | succ k =>
    rw [S_block k, List.length_append]
    have hgood : ∀ x ∈ W' k ++ [3], GoodLetter x := by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact W'_good k x hx
      · simp at hx; exact Or.inl hx
    have h3 := flatMap_phi_len_ge hgood
    have hW := W'_length_ge k
    simp only [List.length_append, List.length_cons, List.length_nil] at h3 ⊢
    omega

private lemma getD_of_prefix {a b : List ℕ} (h : a <+: b) {i : ℕ} (hi : i < a.length) :
    a.getD i 0 = b.getD i 0 := by
  rcases h with ⟨t, rfl⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma u_eq_getD {i k : ℕ} (hi : i < (S (3 * k + 1)).length) :
    u i = (S (3 * k + 1)).getD i 0 := by
  unfold u
  rcases le_total i k with hik | hki
  · exact getD_of_prefix (S_prefix_mono hik) (S_length_gt i)
  · exact (getD_of_prefix (S_prefix_mono hki) hi).symm

private lemma t_eq_getD {j k : ℕ} (hj : j < (T k).length) :
    t j = (T k).getD j 0 := by
  unfold t
  rcases le_total (j + 1) k with h | h
  · exact getD_of_prefix (T_prefix_mono h) (by have := T_length_ge (j + 1); omega)
  · exact (getD_of_prefix (T_prefix_mono h) hj).symm

/-- Position of the `n`-th block in `w.flatMap f`. -/
private def blockPos (F : ℕ → List ℕ) (w : List ℕ) (n : ℕ) : ℕ :=
  ((w.take n).flatMap F).length

private lemma blockPos_zero (F : ℕ → List ℕ) (w : List ℕ) : blockPos F w 0 = 0 := by
  simp [blockPos]

private lemma blockPos_succ (F : ℕ → List ℕ) (w : List ℕ) {n : ℕ} (hn : n < w.length) :
    blockPos F w (n + 1) = blockPos F w n + (F w[n]).length := by
  unfold blockPos
  rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some,
    List.flatMap_append, List.length_append, List.flatMap_singleton]

private lemma blockPos_mono (F : ℕ → List ℕ) (w : List ℕ) {a b : ℕ} (hab : a ≤ b) :
    blockPos F w a ≤ blockPos F w b := by
  unfold blockPos
  have hpre : w.take a <+: w.take b := by
    have h := List.take_prefix a (w.take b)
    rw [List.take_take, Nat.min_eq_left hab] at h
    exact h
  rcases hpre with ⟨t, ht⟩
  rw [← ht, List.flatMap_append, List.length_append]
  omega

private lemma flatMap_getD_blockPos (F : ℕ → List ℕ) (w : List ℕ) {n r : ℕ}
    (hn : n < w.length) (hr : r < (F w[n]).length) :
    (w.flatMap F).getD (blockPos F w n + r) 0 = (F w[n]).getD r 0 := by
  have hsplit : w = w.take n ++ [w[n]] ++ w.drop (n + 1) := by
    conv_lhs => rw [← List.take_append_drop n w]
    rw [List.drop_eq_getElem_cons hn]
    simp
  have hL : w.flatMap F = (w.take n).flatMap F ++ (F w[n] ++ (w.drop (n + 1)).flatMap F) := by
    have h := congrArg (fun l => l.flatMap F) hsplit
    simpa only [List.flatMap_append, List.flatMap_singleton, List.append_assoc] using h
  rw [hL, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [blockPos])]
  have hsub : blockPos F w n + r - ((w.take n).flatMap F).length = r := by
    simp [blockPos]
  rw [hsub, List.getElem?_append_left hr]

private lemma phi_getD_eq_one_iff {c r : ℕ} (hc : GoodLetter c) (hr : r < (phi c).length) :
    (phi c).getD r 0 = 1 ↔ r = 0 := by
  rcases hc with rfl | rfl | rfl
  · have : r < 3 := hr; interval_cases r <;> decide
  · have : r < 4 := hr; interval_cases r <;> decide
  · have : r < 5 := hr; interval_cases r <;> decide

private lemma exists_block_of_lt_flatMap (F : ℕ → List ℕ) (w : List ℕ) {idx : ℕ}
    (hidx : idx < (w.flatMap F).length) :
    ∃ n, ∃ hn : n < w.length, ∃ r, r < (F w[n]).length ∧ idx = blockPos F w n + r := by
  induction w generalizing idx with
  | nil => simp at hidx
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append] at hidx
    by_cases hlt : idx < (F c).length
    · refine ⟨0, by simp, idx, by simpa using hlt, ?_⟩
      simp [blockPos]
    · have hge : (F c).length ≤ idx := by omega
      have hidx' : idx - (F c).length < (cs.flatMap F).length := by omega
      obtain ⟨n, hn, r, hr, hEq⟩ := ih hidx'
      refine ⟨n + 1, by simp [hn], r, by simpa using hr, ?_⟩
      have hbp : blockPos F (c :: cs) (n + 1) = (F c).length + blockPos F cs n := by
        simp [blockPos, List.take_succ_cons, List.flatMap_cons, List.length_append]
      omega

private lemma flatMap_phi_eq_one_iff {w : List ℕ} (hw : ∀ x ∈ w, GoodLetter x)
    {idx : ℕ} (hidx : idx < (w.flatMap phi).length) :
    (w.flatMap phi).getD idx 0 = 1 ↔ ∃ n, n < w.length ∧ idx = blockPos phi w n := by
  constructor
  · intro h1
    obtain ⟨n, hn, r, hr, rfl⟩ := exists_block_of_lt_flatMap phi w hidx
    rw [flatMap_getD_blockPos phi w hn hr] at h1
    have hgn : GoodLetter w[n] := hw w[n] (List.getElem_mem hn)
    have hr0 : r = 0 := (phi_getD_eq_one_iff hgn hr).mp h1
    subst hr0
    exact ⟨n, hn, by simp⟩
  · rintro ⟨n, hn, rfl⟩
    have hgn : GoodLetter w[n] := hw w[n] (List.getElem_mem hn)
    have hr0 : 0 < (phi w[n]).length := by have := phi_len_ge_three hgn; omega
    have := flatMap_getD_blockPos phi w hn hr0
    simp only [add_zero] at this
    rw [this]
    exact (phi_getD_eq_one_iff hgn hr0).mpr rfl

private lemma blockPos_phi_strictMono {w : List ℕ} (hw : ∀ x ∈ w, GoodLetter x)
    {a b : ℕ} (hab : a < b) (hb : b ≤ w.length) :
    blockPos phi w a < blockPos phi w b := by
  have ha : a < w.length := by omega
  have hpos : 0 < (phi w[a]).length := by
    have := phi_len_ge_three (hw w[a] (List.getElem_mem ha)); omega
  have h1 : blockPos phi w a < blockPos phi w (a + 1) := by
    rw [blockPos_succ phi w ha]; omega
  exact lt_of_lt_of_le h1 (blockPos_mono phi w (by omega))

/-- The `n`-th occurrence of `1` in `u` is `2 + blockPos phi (W' k ++ [3]) n` for `n ≤ (W' k).length`. -/
private lemma nth_one_u_eq (k n : ℕ) (hn : n ≤ (W' k).length) :
    Nat.nth (fun i => u i = 1) n = 2 + blockPos phi (W' k ++ [3]) n := by
  set w := W' k ++ [3]
  have hw_good : ∀ x ∈ w, GoodLetter x := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact W'_good k x hx
    · simp at hx; exact Or.inl hx
  have hlen_w : w.length = (W' k).length + 1 := by simp [w]
  have hS : S (3 * (k + 1) + 1) = [2, 3] ++ w.flatMap phi := S_block k
  have hpos_lt : ∀ m ≤ (W' k).length, 2 + blockPos phi w m < (S (3 * (k + 1) + 1)).length := by
    intro m hm
    rw [hS, List.length_append]
    have hm' : m < w.length := by omega
    have hstep := blockPos_succ phi w hm'
    have hle : blockPos phi w (m + 1) ≤ (w.flatMap phi).length := by
      have : w.take (m + 1) <+: w := List.take_prefix _ _
      rcases this with ⟨t, ht⟩
      unfold blockPos
      conv_rhs => rw [← ht, List.flatMap_append, List.length_append]
      omega
    have hpos3 : 0 < (phi w[m]).length := by
      have := phi_len_ge_three (hw_good w[m] (List.getElem_mem hm')); omega
    simp only [List.length_cons, List.length_nil]
    omega
  have hu_iff : ∀ idx < (S (3 * (k + 1) + 1)).length,
      u idx = 1 ↔ ∃ m, m < w.length ∧ idx = 2 + blockPos phi w m := by
    intro idx hidx
    rw [u_eq_getD hidx, hS]
    by_cases h2 : idx < 2
    · interval_cases idx
      · constructor
        · intro h; simp at h
        · rintro ⟨m, _, hm⟩; omega
      · constructor
        · intro h; simp at h
        · rintro ⟨m, _, hm⟩; omega
    · have hge2 : 2 ≤ idx := by omega
      have hidx' : idx - 2 < (w.flatMap phi).length := by
        rw [hS, List.length_append] at hidx
        simp only [List.length_cons, List.length_nil] at hidx
        omega
      have hget : ([2, 3] ++ w.flatMap phi).getD idx 0 = (w.flatMap phi).getD (idx - 2) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simpa using hge2)]
        simp
      rw [hget, flatMap_phi_eq_one_iff hw_good hidx']
      constructor
      · rintro ⟨m, hm, hEq⟩; exact ⟨m, hm, by omega⟩
      · rintro ⟨m, hm, hEq⟩; exact ⟨m, hm, by omega⟩
  -- Prove that `{i | u i = 1}` is infinite so Nat.nth works nicely, or use Nat.nth_eq_iff!
  -- Actually we can prove directly that `count (u i = 1) below (2 + blockPos phi w n) = n`
  -- and `u (2 + blockPos phi w n) = 1`!
  have h_inf : Set.Infinite {i : ℕ | u i = 1} := by
    rw [Set.infinite_iff_exists_gt]
    intro B
    have hleB : B ≤ (W' B).length := W'_length_ge B
    have hSB : S (3 * (B + 1) + 1) = [2, 3] ++ (W' B ++ [3]).flatMap phi := S_block B
    have hwB_good : ∀ x ∈ W' B ++ [3], GoodLetter x := by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact W'_good B x hx
      · simp at hx; exact Or.inl hx
    have hposB : blockPos phi (W' B ++ [3]) B < ((W' B ++ [3]).flatMap phi).length := by
      have hB' : B < (W' B ++ [3]).length := by simp; omega
      have hstep := blockPos_succ phi (W' B ++ [3]) hB'
      have h3 : 0 < (phi (W' B ++ [3])[B]).length := by
        have := phi_len_ge_three (hwB_good _ (List.getElem_mem hB')); omega
      have hle' : blockPos phi (W' B ++ [3]) (B + 1) ≤ ((W' B ++ [3]).flatMap phi).length := by
        have : (W' B ++ [3]).take (B + 1) <+: W' B ++ [3] := List.take_prefix _ _
        rcases this with ⟨t, ht⟩
        unfold blockPos
        conv_rhs => rw [← ht, List.flatMap_append, List.length_append]
        omega
      omega
    have hltS : 2 + blockPos phi (W' B ++ [3]) B < (S (3 * (B + 1) + 1)).length := by
      rw [hSB, List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
    have hu1 : u (2 + blockPos phi (W' B ++ [3]) B) = 1 := by
      rw [u_eq_getD hltS, hSB]
      have hget : ([2, 3] ++ (W' B ++ [3]).flatMap phi).getD (2 + blockPos phi (W' B ++ [3]) B) 0 =
          ((W' B ++ [3]).flatMap phi).getD (blockPos phi (W' B ++ [3]) B) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp)]
        simp
      rw [hget, flatMap_phi_eq_one_iff hwB_good hposB]
      exact ⟨B, by simp; omega, rfl⟩
    have hgt : B < 2 + blockPos phi (W' B ++ [3]) B := by
      have h3B : 3 * ((W' B ++ [3]).take B).length ≤ blockPos phi (W' B ++ [3]) B := by
        apply flatMap_phi_len_ge
        intro x hx
        exact hwB_good x (List.mem_of_mem_take hx)
      have htk : ((W' B ++ [3]).take B).length = B := by
        rw [List.length_take]; simp; omega
      omega
    exact ⟨2 + blockPos phi (W' B ++ [3]) B, hu1, hgt⟩
  -- Use induction on n ≤ (W' k).length via Nat.nth_eq_sInf / Nat.count!
  -- Actually, Nat.nth_of_strictMono or Nat.count_nth is super clean!
  -- Even simpler: prove `∀ m ≤ (W' k).length, Nat.nth (fun i => u i = 1) m = 2 + blockPos phi w m`
  -- by induction on m!
  revert hn
  induction n with
  | zero =>
    intro _
    rw [Nat.nth_zero]
    apply IsLeast.csInf_eq
    refine ⟨(hu_iff _ (hpos_lt 0 (Nat.zero_le _))).mpr ⟨0, by omega, rfl⟩, ?_⟩
    intro a ha
    by_contra hlt
    push Not at hlt
    have hltS : a < (S (3 * (k + 1) + 1)).length := lt_trans hlt (hpos_lt 0 (Nat.zero_le _))
    obtain ⟨m, hm, rfl⟩ := (hu_iff a hltS).mp ha
    have h0 : blockPos phi w 0 ≤ blockPos phi w m := blockPos_mono phi w (Nat.zero_le m)
    omega
  | succ n ih =>
    intro hn
    have ihn := ih (by omega)
    rw [Nat.nth_eq_sInf]
    apply IsLeast.csInf_eq
    refine ⟨⟨(hu_iff _ (hpos_lt (n + 1) hn)).mpr ⟨n + 1, by omega, rfl⟩, ?_⟩, ?_⟩
    · intro j hj
      have hj' : j ≤ n := by omega
      have hlt_j : Nat.nth (fun i => u i = 1) j ≤ Nat.nth (fun i => u i = 1) n :=
        (Nat.nth_strictMono h_inf).monotone hj'
      rw [ihn] at hlt_j
      have hstrict := blockPos_phi_strictMono hw_good (show n < n + 1 by omega) (by omega)
      omega
    · intro a ha
      rcases ha with ⟨hau, hgt⟩
      by_contra hlt
      push Not at hlt
      have hltS : a < (S (3 * (k + 1) + 1)).length := lt_trans hlt (hpos_lt (n + 1) hn)
      obtain ⟨m, hm, rfl⟩ := (hu_iff a hltS).mp hau
      have hgt_n : 2 + blockPos phi w n < 2 + blockPos phi w m := by
        rw [← ihn]; exact hgt n (Nat.lt_succ_self n)
      have hnm : n < m := by
        by_contra hle
        push Not at hle
        have := blockPos_mono phi w hle
        omega
      have hle_m : n + 1 ≤ m := by omega
      have := blockPos_mono phi w hle_m
      omega

private lemma g_phi_len {c : ℕ} (hc : GoodLetter c) : g (phi c).length = c := by
  rcases hc with rfl | rfl | rfl <;> decide

private lemma gd_eq_W' {k n : ℕ} (hn : n < (W' k).length) :
    g (d n) = (W' k)[n] := by
  have h1 := nth_one_u_eq k n (by omega)
  have h2 := nth_one_u_eq k (n + 1) (by omega)
  have hn' : n < (W' k ++ [3]).length := by simp; omega
  have hd : d n = (phi ((W' k ++ [3])[n]'hn')).length := by
    unfold d
    rw [h1, h2, blockPos_succ phi (W' k ++ [3]) hn']
    omega
  have hget : (W' k ++ [3])[n]'hn' = (W' k)[n] :=
    List.getElem_append_left hn
  rw [hd, hget]
  exact g_phi_len (W'_good k _ (List.getElem_mem hn))

private noncomputable def M' : ℕ → ℕ
  | 0 => 5
  | 1 => 6
  | i + 2 => M i

private lemma M'_eq_W' {k n : ℕ} (hn : n < (W' k).length) :
    M' n = (W' k)[n] := by
  match n with
  | 0 =>
    have hpre : W' 1 <+: W' k := by
      cases k with
      | zero => simp [W'] at hn
      | succ k' => exact W'_prefix_mono (Nat.succ_le_succ (Nat.zero_le _))
    have hW1 : W' 1 = [5, 6, 3, 6, 5, 6] := by decide
    have h0 : (W' 1).getD 0 0 = (W' k).getD 0 0 := getD_of_prefix hpre (by rw [hW1]; simp)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn] at h0
    simp [hW1] at h0
    exact h0
  | 1 =>
    have hpre : W' 1 <+: W' k := by
      cases k with
      | zero => simp [W'] at hn
      | succ k' => exact W'_prefix_mono (Nat.succ_le_succ (Nat.zero_le _))
    have hW1 : W' 1 = [5, 6, 3, 6, 5, 6] := by decide
    have h1 : (W' 1).getD 1 0 = (W' k).getD 1 0 := getD_of_prefix hpre (by rw [hW1]; simp)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn] at h1
    simp [hW1] at h1
    exact h1
  | i + 2 =>
    exact gd_eq_W' hn

private lemma M'_good (n : ℕ) : GoodLetter (M' n) := by
  have hlt : n < (W' (n + 1)).length := by have := W'_length_ge (n + 1); omega
  rw [M'_eq_W' hlt]
  exact W'_good (n + 1) _ (List.getElem_mem hlt)

private lemma t_good (n : ℕ) : GoodLetter (t n) := by
  have hlt : n < (T n).length := T_length_ge n
  rw [t_eq_getD hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact T_good n _ (List.getElem_mem hlt)

/-- Cumulative length of `sigma` images for an infinite sequence `A : ℕ → ℕ`. -/
private def spos (A : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => spos A m + (sigma (A m)).length

private lemma spos_eq_blockPos {A : ℕ → ℕ} {w : List ℕ} {m : ℕ}
    (hm : m ≤ w.length) (hAw : ∀ i (hi : i < m), A i = w[i]'(by omega)) :
    spos A m = blockPos sigma w m := by
  induction m with
  | zero => simp [spos, blockPos]
  | succ m ih =>
    rw [spos, blockPos_succ sigma w (by omega),
      ih (by omega) (fun i hi => hAw i (by omega)), hAw m (Nat.lt_succ_self m)]

private lemma M_is_sigma_M' (m r : ℕ) (hr : r < (sigma (M' m)).length) :
    M (spos M' m + r) = (sigma (M' m)).getD r 0 := by
  set k := m + 1
  have hm : m < (W' k).length := by have := W'_length_ge k; omega
  have hm' : m < (W' k ++ [3]).length := by simp; omega
  have hAw : ∀ i (hi : i < m + 1), M' i = (W' k ++ [3])[i]'(by simp; omega) := by
    intro i hi
    have hi' : i < (W' k).length := by omega
    rw [M'_eq_W' hi', List.getElem_append_left hi']
  have hbp : spos M' m = blockPos sigma (W' k ++ [3]) m :=
    spos_eq_blockPos (by omega) (fun i hi => hAw i (by omega))
  have hm_eq : M' m = (W' k ++ [3])[m]'hm' := hAw m (Nat.lt_succ_self m)
  have hr' : r < (sigma ((W' k ++ [3])[m]'hm')).length := hm_eq ▸ hr
  have hblk := flatMap_getD_blockPos sigma (W' k ++ [3]) hm' hr'
  have hpos_lt : blockPos sigma (W' k ++ [3]) m + r < (sigmaStep (W' k ++ [3])).length := by
    have hstep := blockPos_succ sigma (W' k ++ [3]) hm'
    have hle : blockPos sigma (W' k ++ [3]) (m + 1) ≤ (sigmaStep (W' k ++ [3])).length := by
      have : (W' k ++ [3]).take (m + 1) <+: W' k ++ [3] := List.take_prefix _ _
      rcases this with ⟨u, hu⟩
      unfold blockPos sigmaStep
      conv_rhs => rw [← hu, List.flatMap_append, List.length_append]
      omega
    omega
  have hidx_lt : spos M' m + r + 2 < (W' (k + 1)).length := by
    rw [W', List.length_append, hbp]
    simp only [List.length_cons, List.length_nil]
    omega
  have hM : M (spos M' m + r) = (W' (k + 1))[spos M' m + r + 2]'hidx_lt :=
    gd_eq_W' hidx_lt
  rw [hM]
  have hget : (W' (k + 1))[spos M' m + r + 2]'hidx_lt =
      (sigmaStep (W' k ++ [3])).getD (blockPos sigma (W' k ++ [3]) m + r) 0 := by
    have hW : W' (k + 1) = [5, 6] ++ sigmaStep (W' k ++ [3]) := rfl
    have h1 : (W' (k + 1)).getD (spos M' m + r + 2) 0 = (W' (k + 1))[spos M' m + r + 2]'hidx_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt]; rfl
    rw [← h1, hW, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp)]
    simp [hbp]
  rw [hget, sigmaStep, hblk, ← hm_eq]

private lemma t_is_sigma_t (m r : ℕ) (hr : r < (sigma (t m)).length) :
    t (spos t m + r) = (sigma (t m)).getD r 0 := by
  set k := m + 1
  have hm : m < (T k).length := by have := T_length_ge k; omega
  have hAw : ∀ i (hi : i < m + 1), t i = (T k)[i]'(by omega) := by
    intro i hi
    have hi' : i < (T k).length := by omega
    rw [t_eq_getD hi', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rfl
  have hbp : spos t m = blockPos sigma (T k) m :=
    spos_eq_blockPos (by omega) (fun i hi => hAw i (by omega))
  have hm_eq : t m = (T k)[m]'hm := hAw m (Nat.lt_succ_self m)
  have hr' : r < (sigma ((T k)[m]'hm)).length := hm_eq ▸ hr
  have hblk := flatMap_getD_blockPos sigma (T k) hm hr'
  have hpos_lt : spos t m + r < (T (k + 1)).length := by
    rw [T_succ, hbp]
    have hstep := blockPos_succ sigma (T k) hm
    have hle : blockPos sigma (T k) (m + 1) ≤ (sigmaStep (T k)).length := by
      have : (T k).take (m + 1) <+: T k := List.take_prefix _ _
      rcases this with ⟨u, hu⟩
      unfold blockPos sigmaStep
      conv_rhs => rw [← hu, List.flatMap_append, List.length_append]
      omega
    omega
  rw [t_eq_getD hpos_lt, T_succ, hbp, sigmaStep, hblk, ← hm_eq]

private lemma sigma_getD_eq_three_iff {c r : ℕ} (hc : GoodLetter c) (hr : r < (sigma c).length) :
    (sigma c).getD r 0 = 3 ↔ r = 0 := by
  rcases hc with rfl | rfl | rfl
  · have : r < 4 := hr; interval_cases r <;> decide
  · have : r < 6 := hr; interval_cases r <;> decide
  · have : r < 7 := hr; interval_cases r <;> decide

private lemma sigma_len_inj {a b : ℕ} (ha : GoodLetter a) (hb : GoodLetter b)
    (hlen : (sigma a).length = (sigma b).length) : a = b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp [sigma] at hlen ⊢

private lemma spos_ge_four_mul {A : ℕ → ℕ} (hA : ∀ n, GoodLetter (A n)) (m : ℕ) :
    4 * m ≤ spos A m := by
  induction m with
  | zero => simp [spos]
  | succ m ih =>
    have h4 := sigma_len_ge_four (hA m)
    rw [spos]
    omega

private lemma exists_spos_add {A : ℕ → ℕ} (hA : ∀ n, GoodLetter (A n)) (n : ℕ) :
    ∃ m r, r < (sigma (A m)).length ∧ n = spos A m + r := by
  -- Strong induction / find largest m with spos A m ≤ n
  have h_ex : ∃ m, n < spos A m := ⟨n + 1, by have := spos_ge_four_mul hA (n + 1); omega⟩
  let m1 := Nat.find h_ex
  have hm1 : n < spos A m1 := Nat.find_spec h_ex
  have hm1_pos : 0 < m1 := by
    by_contra h0
    have : m1 = 0 := by omega
    rw [this, spos] at hm1
    omega
  have hm_le : spos A (m1 - 1) ≤ n := by
    by_contra hlt
    push Not at hlt
    exact Nat.find_min h_ex (by omega : m1 - 1 < m1) hlt
  have hsucc : spos A m1 = spos A (m1 - 1) + (sigma (A (m1 - 1))).length := by
    conv_lhs => rw [show m1 = (m1 - 1) + 1 by omega, spos]
  refine ⟨m1 - 1, n - spos A (m1 - 1), ?_, by omega⟩
  omega

private lemma eq_three_iff_exists_spos {A A' : ℕ → ℕ} (hA' : ∀ n, GoodLetter (A' n))
    (hSig : ∀ m r, r < (sigma (A' m)).length → A (spos A' m + r) = (sigma (A' m)).getD r 0)
    (n : ℕ) :
    A n = 3 ↔ ∃ m, n = spos A' m := by
  constructor
  · intro h3
    obtain ⟨m, r, hr, rfl⟩ := exists_spos_add hA' n
    rw [hSig m r hr, sigma_getD_eq_three_iff (hA' m) hr] at h3
    subst h3
    exact ⟨m, by simp⟩
  · rintro ⟨m, rfl⟩
    have hr0 : 0 < (sigma (A' m)).length := by have := sigma_len_ge_four (hA' m); omega
    have := hSig m 0 hr0
    simp only [add_zero] at this
    rw [this]
    exact (sigma_getD_eq_three_iff (hA' m) hr0).mpr rfl

private lemma desubst_shift {A A' B B' : ℕ → ℕ}
    (hA' : ∀ n, GoodLetter (A' n)) (hB' : ∀ n, GoodLetter (B' n))
    (hSigA : ∀ m r, r < (sigma (A' m)).length → A (spos A' m + r) = (sigma (A' m)).getD r 0)
    (hSigB : ∀ m r, r < (sigma (B' m)).length → B (spos B' m + r) = (sigma (B' m)).getD r 0)
    {s : ℕ} (halign : ∀ i, A i = B (i + s)) :
    ∃ q, s = spos B' q ∧ ∀ m, A' m = B' (m + q) := by
  have hA0 : A 0 = 3 := (eq_three_iff_exists_spos hA' hSigA 0).mpr ⟨0, rfl⟩
  have hBs : B s = 3 := by simpa using (halign 0).symm.trans hA0
  obtain ⟨q, hsq⟩ := (eq_three_iff_exists_spos hB' hSigB s).mp hBs
  have hstep : ∀ m, spos A' m + spos B' q = spos B' (m + q) ∧ A' m = B' (m + q) := by
    intro m
    induction m with
    | zero =>
      have hpos : spos A' 0 + spos B' q = spos B' (0 + q) := by simp [spos]
      refine ⟨hpos, ?_⟩
      -- Compare lengths (sigma (A' 0)).length and (sigma (B' q)).length
      have hlen : (sigma (A' 0)).length = (sigma (B' q)).length := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- A (sigma (A' 0)).length = 3, but B (spos B' q + (sigma (A' 0)).length) ≠ 3
          have h1 : A (spos A' 1) = 3 := (eq_three_iff_exists_spos hA' hSigA _).mpr ⟨1, rfl⟩
          have h2 : B (spos B' q + (sigma (A' 0)).length) = 3 := by
            have := halign (spos A' 1)
            rw [h1, hsq] at this
            simpa [spos, Nat.add_comm] using this.symm
          rw [hSigB q _ hlt, sigma_getD_eq_three_iff (hB' q) hlt] at h2
          have := sigma_len_ge_four (hA' 0); omega
        · have h1 : B (spos B' (q + 1)) = 3 := (eq_three_iff_exists_spos hB' hSigB _).mpr ⟨q + 1, rfl⟩
          have h2 : A (spos A' 0 + (sigma (B' q)).length) = 3 := by
            have := halign ((sigma (B' q)).length)
            rw [hsq] at this
            have h3 : (sigma (B' q)).length + spos B' q = spos B' (q + 1) := by
              rw [spos]; omega
            rw [h3, h1] at this
            simpa [spos] using this
          rw [hSigA 0 _ hgt, sigma_getD_eq_three_iff (hA' 0) hgt] at h2
          have := sigma_len_ge_four (hB' q); omega
      exact sigma_len_inj (hA' 0) (hB' (0 + q)) (by simpa using hlen)
    | succ m ih =>
      rcases ih with ⟨hpos_m, hEq_m⟩
      have hpos : spos A' (m + 1) + spos B' q = spos B' (m + 1 + q) := by
        have hmq : m + 1 + q = (m + q) + 1 := by omega
        rw [hmq, spos, spos, hEq_m]
        omega
      refine ⟨hpos, ?_⟩
      have hlen : (sigma (A' (m + 1))).length = (sigma (B' (m + 1 + q))).length := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h1 : A (spos A' (m + 2)) = 3 :=
            (eq_three_iff_exists_spos hA' hSigA _).mpr ⟨m + 2, rfl⟩
          have h2 : B (spos B' (m + 1 + q) + (sigma (A' (m + 1))).length) = 3 := by
            have := halign (spos A' (m + 2))
            rw [h1, hsq] at this
            have hsa : spos A' (m + 2) = spos A' (m + 1) + (sigma (A' (m + 1))).length := rfl
            have hadd : spos A' (m + 2) + spos B' q =
                spos B' (m + 1 + q) + (sigma (A' (m + 1))).length := by omega
            rw [hadd] at this
            exact this.symm
          rw [hSigB (m + 1 + q) _ hlt, sigma_getD_eq_three_iff (hB' (m + 1 + q)) hlt] at h2
          have := sigma_len_ge_four (hA' (m + 1)); omega
        · have h1 : B (spos B' (m + 1 + q + 1)) = 3 :=
            (eq_three_iff_exists_spos hB' hSigB _).mpr ⟨m + 1 + q + 1, rfl⟩
          have h2 : A (spos A' (m + 1) + (sigma (B' (m + 1 + q))).length) = 3 := by
            have := halign (spos A' (m + 1) + (sigma (B' (m + 1 + q))).length)
            rw [hsq] at this
            have hsb : spos B' (m + 1 + q + 1) =
                spos B' (m + 1 + q) + (sigma (B' (m + 1 + q))).length := rfl
            have hadd : spos A' (m + 1) + (sigma (B' (m + 1 + q))).length + spos B' q =
                spos B' (m + 1 + q + 1) := by omega
            rw [hadd, h1] at this
            exact this
          rw [hSigA (m + 1) _ hgt, sigma_getD_eq_three_iff (hA' (m + 1)) hgt] at h2
          have := sigma_len_ge_four (hB' (m + 1 + q)); omega
      exact sigma_len_inj (hA' (m + 1)) (hB' (m + 1 + q)) hlen
  exact ⟨q, hsq, fun m => (hstep m).2⟩

private lemma M_four_eq_five : M 4 = 5 := by
  have hlt : 6 < (W' 2).length := by decide
  have hgd := gd_eq_W' (k := 2) (n := 6) hlt
  change M 4 = (W' 2)[6]'hlt at hgd
  have hget : (W' 2).getD 6 0 = (W' 2)[6]'hlt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  have hval : (W' 2).getD 6 0 = 5 := by decide
  rw [hgd, ← hget, hval]

private lemma t_four_eq_three : t 4 = 3 := by
  have hT2 : T 2 = sigmaStep [3, 6, 5, 6] := by decide
  have hlt : 4 < (T 2).length := by rw [hT2]; decide
  rw [t_eq_getD hlt, hT2]
  decide

private lemma t_zero_eq_three : t 0 = 3 := by
  have hlt : 0 < (T 0).length := by decide
  rw [t_eq_getD hlt]
  decide

private lemma no_nonneg_shift : ∀ s : ℕ, ¬ ∀ i : ℕ, M i = t (i + s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro halign
    obtain ⟨q, hsq, hEq⟩ := desubst_shift M'_good t_good M_is_sigma_M' t_is_sigma_t halign
    by_cases hq0 : q = 0
    · subst hq0
      have hs0 : s = 0 := by simpa [spos] using hsq
      subst hs0
      have h4 := halign 4
      simp [M_four_eq_five, t_four_eq_three] at h4
    · have hq1 : 1 ≤ q := by omega
      have h4q : 4 * q ≤ s := by rw [hsq]; exact spos_ge_four_mul t_good q
      have hlt : q + 2 < s := by omega
      apply ih (q + 2) hlt
      intro i
      have := hEq (i + 2)
      simpa [M', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private lemma no_pos_neg_shift : ∀ k : ℕ, 0 < k → ¬ ∀ j : ℕ, t j = M (j + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk halign
    obtain ⟨q, hkq, hEq⟩ := desubst_shift t_good M'_good t_is_sigma_t M_is_sigma_M' halign
    have hq0 : q ≠ 0 := by
      intro h0
      subst h0
      simp [spos] at hkq
      omega
    have hq1 : q ≠ 1 := by
      intro h1
      subst h1
      have h0 := hEq 0
      simp [t_zero_eq_three, M'] at h0
    have hq2 : q ≠ 2 := by
      intro h2
      subst h2
      have h4 := hEq 4
      simp [t_four_eq_three, M', M_four_eq_five] at h4
    have hq3 : 3 ≤ q := by omega
    have h4q : 4 * q ≤ k := by rw [hkq]; exact spos_ge_four_mul M'_good q
    have hlt : q - 2 < k := by omega
    apply ih (q - 2) hlt (by omega)
    intro j
    have := hEq j
    have hidx : j + q = (j + (q - 2)) + 2 := by omega
    rw [hidx] at this
    exact this

end OMA_A107793

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a107793.main) := by
  rintro ⟨s, hs⟩
  by_cases hnonneg : 0 ≤ s
  · lift s to ℕ using hnonneg
    exact OMA_A107793.no_nonneg_shift s (fun i => hs i (i + s) (by push_cast; ring))
  · have hpos : 0 < -s := by omega
    lift (-s) to ℕ using (by omega) with k hk
    have hk_pos : 0 < k := by omega
    refine OMA_A107793.no_pos_neg_shift k hk_pos (fun j => ?_)
    have hEq := hs (j + k) j (by omega)
    exact hEq.symm
