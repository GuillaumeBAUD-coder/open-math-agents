import OMAStatements.S_oeis_a081692
import Mathlib

/-!
# OEIS A081692

Let `f = fixedWord` be the fixed point of `0 -> 01`, `1 -> 0000`, and let `L m` be the length of the
image of the prefix of length `m`. The image of every prefix is a prefix, so the ones of the word
are exactly the last letters of the images of the zeros. Writing `z n` for the (1-indexed) position
of the `n`-th zero, the `n`-th one is at position `L (z n) = 4 * z n - 2 * n`, consecutive zeros are
at distance 1 or 2, and hence `B n = L (z n)` and `A n = z n` by induction on the mex recursion.
-/

open OMA.S_oeis_a081692

namespace OMA.A081692

theorem morphStep_append (u v : List Bool) :
    morphStep (u ++ v) = morphStep u ++ morphStep v := by
  simp [morphStep]

theorem morphStep_length (w : List Bool) : 2 * w.length ≤ (morphStep w).length := by
  induction w with
  | nil => simp [morphStep]
  | cons a w ih =>
    have h : morphStep (a :: w) = morphStep [a] ++ morphStep w := by
      rw [← morphStep_append]; rfl
    rw [h, List.length_append, List.length_cons]
    have h2 : 2 ≤ (morphStep [a]).length := by cases a <;> simp [morphStep]
    omega

def W (j : ℕ) : List Bool := morphStep^[j] [false]

theorem W_succ (j : ℕ) : W (j + 1) = morphStep (W j) := by
  simp [W, Function.iterate_succ_apply']

theorem W_length (j : ℕ) : j + 1 ≤ (W j).length := by
  induction j with
  | zero => simp [W]
  | succ j ih => rw [W_succ]; have := morphStep_length (W j); omega

theorem W_prefix_succ (j : ℕ) : W j <+: W (j + 1) := by
  induction j with
  | zero => exact ⟨[true], by simp [W, morphStep]⟩
  | succ j ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨morphStep t, ?_⟩
    rw [W_succ (j + 1), ← ht, morphStep_append, ← W_succ j, ht]

theorem W_prefix {i j : ℕ} (h : i ≤ j) : W i <+: W j := by
  induction j, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j _ ih => exact ih.trans (W_prefix_succ j)

theorem fixedWord_eq (k : ℕ) : fixedWord k = (W (k + 1)).getD k false := rfl

theorem W_getD (j k : ℕ) (hk : k < (W j).length) : (W j).getD k false = fixedWord k := by
  rw [fixedWord_eq]
  have hk' : k < (W (k + 1)).length := by have := W_length (k + 1); omega
  rcases le_total j (k + 1) with h | h
  · obtain ⟨t, ht⟩ := W_prefix h
    rw [← ht, List.getD_append _ _ _ _ hk]
  · obtain ⟨t, ht⟩ := W_prefix h
    rw [← ht, List.getD_append _ _ _ _ hk']

def pre (m : ℕ) : List Bool := (List.range m).map fixedWord

theorem pre_length (m : ℕ) : (pre m).length = m := by simp [pre]

theorem prefix_pre {u : List Bool} {N : ℕ} (h : u <+: pre N) : u = pre u.length := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2
    rw [h.getElem h1]
    simp [pre]

theorem W_eq_pre (j : ℕ) : W j = pre (W j).length := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2
    have := W_getD j i h1
    rw [List.getD_eq_getElem _ _ h1] at this
    simp [pre, this]

theorem pre_add (a b : ℕ) :
    pre (a + b) = pre a ++ (List.range b).map (fun j => fixedWord (a + j)) := by
  simp [pre, List.range_add, List.map_map, Function.comp_def]

theorem pre_prefix {m N : ℕ} (h : m ≤ N) : pre m <+: pre N := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pre_add]; exact List.prefix_append _ _

def L (m : ℕ) : ℕ := (morphStep (pre m)).length

theorem morph_pre (m : ℕ) : morphStep (pre m) = pre (L m) := by
  have h1 : pre m <+: pre (W m).length := pre_prefix (by have := W_length m; omega)
  rw [← W_eq_pre] at h1
  obtain ⟨t, ht⟩ := h1
  have h2 : morphStep (pre m) <+: pre (W (m + 1)).length := by
    rw [← W_eq_pre, W_succ, ← ht, morphStep_append]; exact List.prefix_append _ _
  exact prefix_pre h2

theorem L_zero : L 0 = 0 := by simp [L, pre, morphStep]

theorem block_eq (m : ℕ) :
    (List.range (morphStep [fixedWord m]).length).map (fun j => fixedWord (L m + j))
        = morphStep [fixedWord m]
      ∧ L (m + 1) = L m + (morphStep [fixedWord m]).length := by
  have h1 : pre (m + 1) = pre m ++ [fixedWord m] := by
    rw [pre_add]; simp
  have h2 : pre (L (m + 1)) = pre (L m) ++ morphStep [fixedWord m] := by
    rw [← morph_pre, h1, morphStep_append, morph_pre]
  have h3 : L (m + 1) = L m + (morphStep [fixedWord m]).length := by
    have := congrArg List.length h2
    simpa [pre_length] using this
  refine ⟨?_, h3⟩
  rw [h3, pre_add] at h2
  exact List.append_cancel_left h2

theorem step_false {m : ℕ} (h : fixedWord m = false) :
    fixedWord (L m) = false ∧ fixedWord (L m + 1) = true ∧ L (m + 1) = L m + 2 := by
  obtain ⟨h1, h2⟩ := block_eq m
  rw [h] at h1 h2
  simp [morphStep, List.range_succ] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

theorem step_true {m : ℕ} (h : fixedWord m = true) :
    (∀ j, j < 4 → fixedWord (L m + j) = false) ∧ L (m + 1) = L m + 4 := by
  obtain ⟨h1, h2⟩ := block_eq m
  rw [h] at h1 h2
  simp [morphStep, List.range_succ] at h1 h2
  refine ⟨?_, h2⟩
  intro j hj
  interval_cases j
  · simpa using h1.1
  · exact h1.2.1
  · exact h1.2.2.1
  · exact h1.2.2.2

theorem L_start (m : ℕ) : fixedWord (L m) = false := by
  cases h : fixedWord m with
  | false => exact (step_false h).1
  | true => simpa using (step_true h).1 0 (by omega)

theorem two_mul_le_L (m : ℕ) : 2 * m ≤ L m := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases h : fixedWord m with
    | false => have := (step_false h).2.2; omega
    | true => have := (step_true h).2; omega

theorem ones_lt (m : ℕ) : ∀ y, y < L m → fixedWord y = true →
    ∃ k, k < m ∧ fixedWord k = false ∧ y = L k + 1 := by
  induction m with
  | zero => intro y hy; simp [L_zero] at hy
  | succ m ih =>
    intro y hy hf
    by_cases hlt : y < L m
    · obtain ⟨k, hk, h1, h2⟩ := ih y hlt hf
      exact ⟨k, by omega, h1, h2⟩
    · cases h : fixedWord m with
      | false =>
        obtain ⟨a, b, c⟩ := step_false h
        have hy2 : y = L m ∨ y = L m + 1 := by omega
        rcases hy2 with rfl | rfl
        · rw [a] at hf; cases hf
        · exact ⟨m, by omega, h, rfl⟩
      | true =>
        obtain ⟨a, c⟩ := step_true h
        obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ y = L m + j := ⟨y - L m, by omega, by omega⟩
        rw [a j hj] at hf; cases hf

theorem ones {y : ℕ} (hf : fixedWord y = true) : ∃ k, fixedWord k = false ∧ y = L k + 1 := by
  have h := two_mul_le_L (y + 1)
  obtain ⟨k, _, h1, h2⟩ := ones_lt (y + 1) y (by omega) hf
  exact ⟨k, h1, h2⟩

theorem no11 {y : ℕ} (hf : fixedWord y = true) : fixedWord (y + 1) = false := by
  obtain ⟨k, hk, rfl⟩ := ones hf
  have h := L_start (k + 1)
  rw [(step_false hk).2.2] at h
  exact h

/-- The predicate of the statement: `m` is a (1-indexed) position of a zero. -/
def P (m : ℕ) : Prop := 1 ≤ m ∧ fixedWord (m - 1) = false

instance : DecidablePred P := fun m => by unfold P; infer_instance

theorem P_succ (m : ℕ) : P (m + 1) ↔ fixedWord m = false := by simp [P]

theorem not_P_zero : ¬ P 0 := by simp [P]

theorem L_count (m : ℕ) : L m + 2 * Nat.count P (m + 1) = 4 * m := by
  induction m with
  | zero => simp [L_zero, Nat.count_succ, not_P_zero]
  | succ m ih =>
    rw [Nat.count_succ]
    cases h : fixedWord m with
    | false =>
      have h1 := (step_false h).2.2
      have hp : P (m + 1) := (P_succ m).2 h
      simp only [hp, if_true]; omega
    | true =>
      have h1 := (step_true h).2
      have hp : ¬ P (m + 1) := by rw [P_succ]; simp [h]
      simp only [hp, if_false]; omega

theorem P_one : P 1 := by
  have h := L_start 0
  rw [L_zero] at h
  exact (P_succ 0).2 h

theorem P_inf : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  cases h : fixedWord a with
  | false => exact ⟨a + 1, (P_succ a).2 h, by omega⟩
  | true => exact ⟨a + 2, (P_succ (a + 1)).2 (no11 h), by omega⟩

theorem nth_pos (n : ℕ) : 1 ≤ Nat.nth P n := (Nat.nth_mem_of_infinite P_inf n).1

theorem nth_zero' : Nat.nth P 0 = 1 := by
  have h := Nat.nth_count P_one
  have h0 : Nat.count P 1 = 0 := by simp [Nat.count_succ, not_P_zero]
  rwa [h0] at h

theorem nth_gap (n : ℕ) : Nat.nth P (n + 1) ≤ Nat.nth P n + 2 := by
  have hx := Nat.nth_mem_of_infinite P_inf n
  have hc := Nat.count_nth_of_infinite P_inf n
  generalize Nat.nth P n = x at hx hc ⊢
  have key : ∀ q, P q → x < q → Nat.nth P (n + 1) ≤ q := by
    intro q hq hlt
    have h1 : Nat.count P (x + 1) = n + 1 := by rw [Nat.count_succ, hc]; simp [hx]
    have h2 : n + 1 ≤ Nat.count P q := by
      rw [← h1]; exact Nat.count_monotone P (by omega)
    have h3 := Nat.nth_monotone P_inf h2
    rwa [Nat.nth_count hq] at h3
  cases h : fixedWord x with
  | false => have := key (x + 1) ((P_succ x).2 h) (by omega); omega
  | true => have := key (x + 2) ((P_succ (x + 1)).2 (no11 h)) (by omega); omega

theorem L_nth (n : ℕ) :
    L (Nat.nth P n) + 2 * (n + 1) = 4 * Nat.nth P n ∧ ¬ P (L (Nat.nth P n)) := by
  have hx := Nat.nth_mem_of_infinite P_inf n
  have hc := Nat.count_nth_of_infinite P_inf n
  generalize Nat.nth P n = x at hx hc ⊢
  have h1 : Nat.count P (x + 1) = n + 1 := by rw [Nat.count_succ, hc]; simp [hx]
  have h2 := L_count x
  rw [h1] at h2
  refine ⟨h2, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by have := hx.1; omega⟩
  have hf := (P_succ m).1 hx
  obtain ⟨a, b, c⟩ := step_false hf
  rw [c]
  intro hP
  have h3 := (P_succ (L m + 1)).1 hP
  rw [b] at h3; cases h3

theorem notP_form {y : ℕ} (hy : 1 ≤ y) (h : ¬ P y) :
    ∃ k, y = L (Nat.nth P k) ∧ Nat.nth P k < y := by
  obtain ⟨m, rfl⟩ : ∃ m, y = m + 1 := ⟨y - 1, by omega⟩
  rw [P_succ] at h
  have hf : fixedWord m = true := by simpa using h
  obtain ⟨k, hk, rfl⟩ := ones hf
  have hP : P (k + 1) := (P_succ k).2 hk
  refine ⟨Nat.count P (k + 1), ?_, ?_⟩
  · rw [Nat.nth_count hP, (step_false hk).2.2]
  · rw [Nat.nth_count hP]; have := two_mul_le_L k; omega

/-- `z n` is the position of the `n`-th zero, with `z 0 = 0`. -/
noncomputable def z (i : ℕ) : ℕ := if i = 0 then 0 else Nat.nth P (i - 1)

theorem z_zero : z 0 = 0 := by simp [z]

theorem z_succ (n : ℕ) : z (n + 1) = Nat.nth P n := by simp [z]

theorem z_lt (n : ℕ) : z n < z (n + 1) := by
  cases n with
  | zero => rw [z_zero, z_succ]; have := nth_pos 0; omega
  | succ n => rw [z_succ, z_succ]; exact Nat.nth_strictMono P_inf (by omega)

theorem z_le (n : ℕ) : z (n + 1) ≤ z n + 2 := by
  cases n with
  | zero => rw [z_zero, z_succ, nth_zero']; omega
  | succ n => rw [z_succ, z_succ]; exact nth_gap n

theorem z_mono : StrictMono z := strictMono_nat_of_lt_succ z_lt

theorem L_z (n : ℕ) : L (z n) + 2 * n = 4 * z n := by
  cases n with
  | zero => simp [z_zero, L_zero]
  | succ n => rw [z_succ]; exact (L_nth n).1

theorem L_rec (n : ℕ) :
    L (z (n + 1)) = L (z n) + (z (n + 1) - z n) * (z (n + 1) - z n + 1) := by
  have h1 := L_z n
  have h2 := L_z (n + 1)
  have h3 := z_lt n
  have h4 := z_le n
  have h5 : z (n + 1) = z n + 1 ∨ z (n + 1) = z n + 2 := by omega
  rcases h5 with h | h
  · have hd : z (n + 1) - z n = 1 := by omega
    rw [hd]; omega
  · have hd : z (n + 1) - z n = 2 := by omega
    rw [hd]; omega

theorem mex_lemma (S : Finset ℕ) (v : ℕ) (h1 : v ∉ S) (h2 : ∀ x < v, x ∈ S) :
    sInf {x : ℕ | x ∉ S} = v := by
  apply le_antisymm
  · exact Nat.sInf_le h1
  · by_contra hlt
    rw [not_le] at hlt
    have hne : {x : ℕ | x ∉ S}.Nonempty := ⟨v, h1⟩
    exact (Nat.sInf_mem hne) (h2 _ hlt)

theorem used_mem (n x : ℕ) :
    x ∈ (((List.range (n + 1)).map (fun i => (z i, L (z i)))).map Prod.fst ++
      ((List.range (n + 1)).map (fun i => (z i, L (z i)))).map Prod.snd).toFinset ↔
    ∃ i, i ≤ n ∧ (z i = x ∨ L (z i) = x) := by
  simp only [List.map_map, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    Function.comp_apply]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, by omega, Or.inl h⟩
    · exact ⟨i, by omega, Or.inr h⟩
  · rintro ⟨i, hi, h | h⟩
    · exact Or.inl ⟨i, by omega, h⟩
    · exact Or.inr ⟨i, by omega, h⟩

theorem mex_z (n : ℕ) :
    sInf {x : ℕ | x ∉ (((List.range (n + 1)).map (fun i => (z i, L (z i)))).map Prod.fst ++
      ((List.range (n + 1)).map (fun i => (z i, L (z i)))).map Prod.snd).toFinset} = z (n + 1) := by
  apply mex_lemma
  · rw [used_mem]
    rintro ⟨i, hi, h | h⟩
    · have := z_mono (show i < n + 1 by omega); omega
    · cases i with
      | zero => rw [z_zero, L_zero] at h; have := z_lt n; omega
      | succ i =>
        rw [z_succ] at h
        have h1 := (L_nth i).2
        rw [h, z_succ] at h1
        exact h1 (Nat.nth_mem_of_infinite P_inf n)
  · intro x hx
    rw [used_mem]
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · exact ⟨0, by omega, Or.inl z_zero⟩
    · by_cases hP : P x
      · have h1 : z (Nat.count P x + 1) = x := by rw [z_succ, Nat.nth_count hP]
        refine ⟨Nat.count P x + 1, ?_, Or.inl h1⟩
        have h2 : z (Nat.count P x + 1) < z (n + 1) := by omega
        have := z_mono.lt_iff_lt.1 h2; omega
      · obtain ⟨k, hk1, hk2⟩ := notP_form hpos hP
        refine ⟨k + 1, ?_, Or.inr ?_⟩
        · have h2 : z (k + 1) < z (n + 1) := by rw [z_succ]; omega
          have := z_mono.lt_iff_lt.1 h2; omega
        · rw [z_succ]; exact hk1.symm

theorem abPrefix_eq (n : ℕ) :
    abPrefix n = (List.range (n + 1)).map (fun i => (z i, L (z i))) := by
  induction n with
  | zero => simp [abPrefix, z_zero, L_zero]
  | succ n ih =>
    have hlast : (abPrefix n).getLastD (0, 0) = (z n, L (z n)) := by
      rw [ih]; simp [List.range_succ]
    have hmex : sInf {x : ℕ | x ∉ ((abPrefix n).map Prod.fst ++
        (abPrefix n).map Prod.snd).toFinset} = z (n + 1) := by
      rw [ih]; exact mex_z n
    rw [List.range_succ, List.map_append, ← ih, abPrefix]
    simp only [hlast, hmex, List.map_cons, List.map_nil, ← L_rec]

theorem aSeq_eq (n : ℕ) : aSeq n = z n := by
  unfold aSeq
  rw [abPrefix_eq]
  simp [List.range_succ]

end OMA.A081692

theorem OMA.solution : type_of% @OMA.S_oeis_a081692.main := by
  intro n hn
  rw [OMA.A081692.aSeq_eq]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [OMA.A081692.z_succ]
  rfl
