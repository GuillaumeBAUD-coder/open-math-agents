import OMAStatements.S_oeis_a334513
import Mathlib

open OMA.S_oeis_a334513

section

/- The exceptional sites through time eight are computed against an alternating uniform background. -/
open OMA.S_oeis_a334513

/-- The exceptional cells in the first nine stages, against the alternating
uniform background. Indices n-j represent negative offsets. -/
private def rule25Mask (n : ℕ) : ℕ → ℕ → Bool
  | 0, i => decide (i = 0)
  | 1, i => !decide (i = n-1 ∨ i = 0)
  | 2, i => decide (i = n-1 ∨ i = 1)
  | 3, i => !decide (i = n-2 ∨ i = n-1 ∨ i = 0 ∨ i = 1)
  | 4, i => decide (i = n-2 ∨ i = n-1 ∨ i = 0 ∨ i = 2)
  | 5, i => !decide (i = n-3 ∨ i = n-1 ∨ i = 0 ∨ i = 1 ∨ i = 2)
  | 6, i => decide (i = n-1 ∨ i = 0 ∨ i = 1 ∨ i = 3)
  | 7, i => !decide (i = n-2 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)
  | _, i => decide (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)

private lemma rule25_pred_val {n : ℕ} (i : Fin n) :
    (i.val+n-1) % n = if i.val = 0 then n-1 else i.val-1 := by
  split_ifs with h
  · rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [show i.val+n-1 = i.val-1+n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

private lemma rule25_succ_val {n : ℕ} (i : Fin n) :
    (i.val+1) % n = if i.val+1 = n then 0 else i.val+1 := by
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma rule25_mask_step {n : ℕ} (hn : 10 ≤ n) (i : Fin n)
    (t : ℕ) (ht : t < 8) :
    step 25 n (fun j => rule25Mask n t j.val) i = rule25Mask n (t+1) i.val := by
  simp only [step, rule25_pred_val, rule25_succ_val]
  have hi := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = n-1 ∨ i.val = n-2 ∨ i.val = n-3 ∨ i.val = n-4 ∨
      (5 ≤ i.val ∧ i.val + 4 < n) := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|⟨h,h'⟩ <;> interval_cases t <;>
    simp (disch := omega) only [rule25Mask, if_pos, if_neg, true_or, or_true,
      decide_eq_true, decide_eq_false] <;> decide

private lemma rule25_state_mask {n : ℕ} (hn : 10 ≤ n) (t : ℕ) (ht : t ≤ 8) (i : Fin n) :
    state 25 n t i = rule25Mask n t i.val := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [state, show state 25 n t = fun j => rule25Mask n t j.val by
      funext j
      exact ih (by omega) j]
    exact rule25_mask_step hn i t (by omega)

private lemma rule25_six {n : ℕ} (hn : 10 ≤ n) (i : Fin n) :
    state 25 n 6 i = decide (i.val = n-1 ∨ i.val = 0 ∨ i.val = 1 ∨ i.val = 3) :=
  rule25_state_mask hn 6 (by decide) i

private lemma rule25_seven {n : ℕ} (hn : 10 ≤ n) (i : Fin n) :
    state 25 n 7 i = !decide (i.val = n-2 ∨ i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3) :=
  rule25_state_mask hn 7 (by decide) i

private lemma rule25_eight {n : ℕ} (hn : 10 ≤ n) (i : Fin n) :
    state 25 n 8 i = state 25 n 6 ⟨(i.val+n-1)%n, Nat.mod_lt _ (Fin.pos i)⟩ := by
  rw [rule25_state_mask hn 8 (by decide), rule25_six hn]
  simp only [rule25Mask, decide_eq_decide, rule25_pred_val]
  split_ifs <;> omega

end

section

/- The unique isolated live cell identifies the location of the even pattern. Counting live cells distinguishes the two phases. -/
open Finset OMA.S_oeis_a334513

private lemma oma_rule_even_stabilizer {n k : ℕ} (hn : 10 ≤ n)
    (s : Fin n → Bool) (hs : ∀ i, s i = decide (i.val=n-1 ∨ i.val=0 ∨ i.val=1 ∨ i.val=3)) :
    (∀ i : Fin n, s ⟨(i.val+k)%n, Nat.mod_lt _ (by omega)⟩ = s i) ↔ n ∣ k := by
  have hpos : 0 < n := by omega
  constructor
  · intro h
    have atZero := h ⟨0, hpos⟩
    have atThree := h ⟨3, by omega⟩
    simp [hs] at atZero
    simp [hs] at atThree
    rw [Nat.dvd_iff_mod_eq_zero]
    rcases atZero with hk | hk | hk | hk
    · rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 3 < n), hk,
        show 3+(n-1) = 2+n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 2<n)] at atThree
      omega
    · exact hk
    · rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 3 < n), hk, Nat.mod_eq_of_lt (by omega : 3+1<n)] at atThree
      omega
    · rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 3 < n), hk, Nat.mod_eq_of_lt (by omega : 3+3<n)] at atThree
      omega
  · intro hk i
    congr 1
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hk, Nat.mod_eq_of_lt i.isLt]

private lemma oma_rule_count_values {n : ℕ} (U : Finset ℕ) (hU : ∀ i ∈ U, i < n) :
    (univ.filter (fun i : Fin n => i.val ∈ U)).card = U.card := by
  apply card_bij (fun i _ => i.val)
  · intro a ha
    exact (mem_filter.mp ha).2
  · intro i _ j _ h
    exact Fin.ext h
  · intro i hi
    exact ⟨⟨i,hU i hi⟩, mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩

private lemma oma_rule_phase_sizes {n : ℕ} (hn : 10 ≤ n) (s t : Fin n → Bool)
    (hs : ∀ i, s i = decide (i.val=n-1 ∨ i.val=0 ∨ i.val=1 ∨ i.val=3))
    (ht : ∀ i, t i = !decide (i.val=n-2 ∨ i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3)) :
    (univ.filter (fun i => s i = true)).card = 4 ∧
    (univ.filter (fun i => t i = true)).card = n-5 := by
  let A : Finset ℕ := {n-1,0,1,3}
  let B : Finset ℕ := {n-2,0,1,2,3}
  have bA {i : ℕ} (hi : i ∈ A) : i < n := by simp only [A, mem_insert, mem_singleton] at hi; omega
  have bB {i : ℕ} (hi : i ∈ B) : i < n := by simp only [B, mem_insert, mem_singleton] at hi; omega
  have cA : A.card = 4 := by
    change (insert (n-1) ({0,1,3} : Finset ℕ)).card = 4
    rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega)]
    decide
  have cB : B.card = 5 := by
    change (insert (n-2) ({0,1,2,3} : Finset ℕ)).card = 5
    rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega)]
    decide
  have ca := (oma_rule_count_values A (fun _ h => bA h)).trans cA
  have cb := (oma_rule_count_values B (fun _ h => bB h)).trans cB
  constructor
  · simpa [hs, A] using ca
  · have both := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (p := fun i => i.val ∈ B)
    have off : (univ.filter (fun i : Fin n => i.val ∉ B)).card = n-5 := by
      rw [cb, card_univ, Fintype.card_fin] at both
      omega
    simpa [ht, B] using off

private lemma oma_rule_phase_ne {n : ℕ} (hn : 10 ≤ n) (s t : Fin n → Bool)
    (hs : ∀ i, s i = decide (i.val=n-1 ∨ i.val=0 ∨ i.val=1 ∨ i.val=3))
    (ht : ∀ i, t i = !decide (i.val=n-2 ∨ i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3))
    (u v : Equiv.Perm (Fin n)) : (s ∘ u) ≠ (t ∘ v) := by
  obtain ⟨hA,hB⟩ := oma_rule_phase_sizes hn s t hs ht
  have cardShift (f : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
      (univ.filter (fun i => f (e i) = true)).card = (univ.filter (fun i => f i = true)).card := by
    apply card_bij (fun i _ => e i)
    · intro i hi
      simpa using hi
    · intro i _ j _ h
      exact e.injective h
    · intro i hi
      exact ⟨e.symm i, by simpa using hi, e.apply_symm_apply i⟩
  intro eqv
  have hc := congrArg (fun f : Fin n → Bool => (univ.filter fun i => f i = true).card) eqv
  change (univ.filter (fun i => s (u i) = true)).card = (univ.filter (fun i => t (v i) = true)).card at hc
  rw [cardShift, cardShift, hA, hB] at hc
  omega

private lemma oma_rule_stabilizer {n : ℕ} [NeZero n] (hn : 10 ≤ n)
    (h6 : ∀ i : Fin n, state 25 n 6 i = decide (i.val=n-1 ∨ i.val=0 ∨ i.val=1 ∨ i.val=3))
    (s : Fin n) (h : ∀ i : Fin n, state 25 n 6 (i+s) = state 25 n 6 i) : s=0 := by
  have hd := (oma_rule_even_stabilizer (k := s.val) hn (state 25 n 6) h6).mp h
  apply Fin.ext
  change s.val = 0
  exact Nat.eq_zero_of_dvd_of_lt hd s.isLt

private lemma oma_rule_no_odd_shift {n : ℕ} [NeZero n] (hn : 10 ≤ n)
    (h6 : ∀ i : Fin n, state 25 n 6 i = decide (i.val=n-1 ∨ i.val=0 ∨ i.val=1 ∨ i.val=3))
    (h7 : ∀ i : Fin n, state 25 n 7 i = !decide (i.val=n-2 ∨ i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3))
    (s : Fin n) : ¬ (∀ i : Fin n, state 25 n 7 (i+s) = state 25 n 6 i) := by
  intro h
  apply oma_rule_phase_ne hn _ _ h6 h7 (Equiv.refl _) (Equiv.addRight s)
  exact funext (fun i => (h i).symm)

end

section

/- The update commutes with cyclic translation, so the two-step shift propagates through the orbit. -/
open OMA.S_oeis_a334513 Fin.NatCast

private lemma rule25_prev {n : ℕ} [NeZero n] (hn : 10 ≤ n) (i : Fin n) :
    (⟨(i.val+n-1)%n, Nat.mod_lt _ (Fin.pos i)⟩ : Fin n) = i-1 := by
  apply Fin.ext
  simp only [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1<n)]
  congr 1
  omega

private lemma rule25_step_shift {n : ℕ} [NeZero n] (hn : 10 ≤ n)
    (x : Fin n → Bool) (s i : Fin n) :
    step 25 n (fun j => x (j+s)) i = step 25 n x (i+s) := by
  have next (j : Fin n) : (⟨(j.val+1)%n, Nat.mod_lt _ (Fin.pos j)⟩ : Fin n) = j+1 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one',Nat.mod_eq_of_lt (by omega : 1<n)]
  unfold step
  rw [rule25_prev hn i,rule25_prev hn (i+s),next i,next (i+s)]
  dsimp only
  rw [show i-1+s=(i+s)-1 by abel, show i+1+s=(i+s)+1 by abel]

private lemma rule25_large {n : ℕ} [NeZero n] (hn : 10 ≤ n)
    (eight : ∀ i : Fin n, state 25 n 8 i = state 25 n 6 (i-1))
    (stabilizer : ∀ s : Fin n, (∀ i : Fin n, state 25 n 6 (i+s) = state 25 n 6 i) → s=0)
    (different : ∀ s : Fin n, ¬ (∀ i : Fin n, state 25 n 7 (i+s) = state 25 n 6 i)) :
    a n = 2*n := by
  let x := state 25 n
  have slide (t : ℕ) : ∀ i : Fin n, x (8+t) i = x (6+t) (i-1) := by
    induction t with
    | zero => simpa [x] using eight
    | succ t ih =>
      intro i
      change step 25 n (x (8+t)) i = step 25 n (x (6+t)) (i-1)
      rw [funext ih]
      simpa only [sub_eq_add_neg] using rule25_step_shift hn (x (6+t)) (-1) i
  have evenp (k : ℕ) : ∀ i : Fin n, x (6+2*k) i = x 6 (i-(k : Fin n)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      rw [show 6+2*(k+1) = 8+2*k by omega,slide,ih,Nat.cast_succ]
      congr 1
      abel
  have oddp (k : ℕ) (i : Fin n) : x (6+(2*k+1)) i = x 7 (i-(k:Fin n)) := by
    change step 25 n (x (6+2*k)) i = step 25 n (x 6) (i-(k:Fin n))
    rw [funext (evenp k)]
    simpa only [sub_eq_add_neg] using rule25_step_shift hn (x 6) (-(k:Fin n)) i
  have selfcast : (n : Fin n) = 0 := by apply Fin.ext; simp
  have per : Function.Periodic (fun j => x (6+j)) (2*n) := by
    intro j
    induction j with
    | zero => simpa only [zero_add, add_zero,selfcast, sub_zero] using funext (evenp n)
    | succ j ih =>
      change x (6+(j+1+2*n)) = x (6+(j+1))
      rw [show 6+(j+1+2*n)=(6+(j+2*n))+1 by omega]
      exact congrArg (step 25 n) ih
  have ev : EventualPeriod 25 n (2*n) := by
    refine ⟨6,?_⟩
    intro t ht
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa only [Nat.add_assoc] using per j
  let G := {p : ℕ | 0<p ∧ EventualPeriod 25 n p}
  have mem : 2*n ∈ G := ⟨by omega, ev⟩
  rw [a,if_neg (by omega : n ≠ 0)]
  change sInf G = 2*n
  refine le_antisymm (Nat.sInf_le mem) (le_csInf ⟨_,mem⟩ ?_)
  rintro r ⟨hr,U,hU⟩
  by_contra! small
  have hu : U ≤ 6 + U*(2*n) := by nlinarith
  have p0 := per.nat_mul U 0
  have pr := per.nat_mul U r
  simp only [Nat.cast_id, zero_add, add_zero] at p0 pr
  have same : x (6+r) = x 6 := by
    calc
      _ = x (6+(r+U*(2*n))) := pr.symm
      _ = x (6+U*(2*n)+r) := by congr 1; omega
      _ = x (6+U*(2*n)) := hU _ hu
      _ = _ := p0
  let k := r/2
  have hk : k<n := by dsimp [k]; omega
  rcases (show r=2*k ∨ r=2*k+1 by dsimp [k]; omega) with h | h
  · rw [h] at same
    have hz := stabilizer (-(k:Fin n)) (fun i => by
      simpa only [← sub_eq_add_neg] using (evenp k i).symm.trans (congrFun same i))
    have z : (k : Fin n) = 0 := neg_eq_zero.mp hz
    have zval := congrArg Fin.val z
    simp [Fin.val_natCast, Nat.mod_eq_of_lt hk] at zval
    omega
  · rw [h] at same
    exact different (-(k:Fin n)) (fun i => by
      simpa only [← sub_eq_add_neg] using (oddp k i).symm.trans (congrFun same i))

end

section

/- For the nine small rings, check the transition tables and the first return to the recurrent state. -/
open OMA.S_oeis_a334513

private lemma rule25_certify {n T P : ℕ} (hn : n ≠ 0) (hp : 0 < P) (table : List ℕ)
    (h0 : ∀ i : Fin n, decide (i.val = 0) = (table.getD 0 0).testBit i.val)
    (hstep : ∀ j : Fin (T+P), ∀ i : Fin n,
      step 25 n (fun k => (table.getD j.val 0).testBit k.val) i =
        (table.getD (j.val+1) 0).testBit i.val)
    (hcycle : table.getD (T+P) 0 = table.getD T 0)
    (hmin : ∀ j : Fin P, 0 < j.val → ∃ i : Fin n,
      (table.getD (T+j.val) 0).testBit i.val ≠ (table.getD T 0).testBit i.val) :
    a n = P := by
  have tab (t : ℕ) (ht : t ≤ T+P) :
      state 25 n t = fun i => (table.getD t 0).testBit i.val := by
    induction t with
    | zero => exact funext h0
    | succ t ih =>
      change step 25 n (state 25 n t) = _
      rw [ih (by omega)]
      exact funext (hstep ⟨t, by omega⟩)
  have per : Function.Periodic (fun j => state 25 n (T+j)) P := by
    intro j
    induction j with
    | zero =>
      change state 25 n (T+(0+P)) = state 25 n (T+0)
      rw [zero_add, add_zero, tab (T+P) le_rfl, tab T (by omega), hcycle]
    | succ j ih =>
      change state 25 n (T + (j+1+P)) = state 25 n (T + (j+1))
      rw [show T+(j+1+P) = (T+(j+P))+1 by omega, show T+(j+1) = (T+j)+1 by omega]
      exact congrArg (step 25 n) ih
  have eventual : EventualPeriod 25 n P := by
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa only [Nat.add_assoc] using per s
  let good := {p : ℕ | 0 < p ∧ EventualPeriod 25 n p}
  have mem : P ∈ good := ⟨hp,eventual⟩
  rw [a, if_neg hn]
  change sInf good = P
  refine le_antisymm (Nat.sInf_le mem) ?_
  apply le_csInf ⟨P, mem⟩
  rintro r ⟨hr, U, he⟩
  by_contra! small
  have hu : U ≤ T + U*P := by nlinarith
  have h0' := per.nat_mul U 0
  have hr' := per.nat_mul U r
  simp only [Nat.cast_id, zero_add, add_zero] at h0' hr'
  have same : state 25 n (T+r) = state 25 n T := by
    calc
      _ = state 25 n (T+(r+U*P)) := hr'.symm
      _ = state 25 n (T+U*P+r) := by congr 1; omega
      _ = state 25 n (T+U*P) := he _ hu
      _ = _ := h0'
  obtain ⟨i,hi⟩ := hmin ⟨r,small⟩ hr
  apply hi
  rw [tab (T+r) (by omega), tab T (by omega)] at same
  exact congrFun same i

private lemma rule25_small_1 : a 1 = 2 := by
  apply rule25_certify (T := 0) (by decide) (by decide) [1, 0, 1] <;> decide

private lemma rule25_small_2 : a 2 = 2 := by
  apply rule25_certify (T := 1) (by decide) (by decide) [1, 0, 3, 0] <;> decide

private lemma rule25_small_3 : a 3 = 3 := by
  apply rule25_certify (T := 0) (by decide) (by decide) [1, 2, 4, 1] <;> decide

private lemma rule25_small_4 : a 4 = 2 := by
  apply rule25_certify (T := 3) (by decide) (by decide) [1, 6, 10, 0, 15, 0] <;> decide

private lemma rule25_small_5 : a 5 = 15 := by
  apply rule25_certify (T := 0) (by decide) (by decide) [1, 14, 18, 4, 25, 10, 16, 7, 9, 2, 28, 5, 8, 19, 20, 1] <;> decide

private lemma rule25_small_6 : a 6 = 15 := by
  apply rule25_certify (T := 0) (by decide) (by decide) [1, 30, 34, 12, 53, 16, 39, 40, 3, 29, 4, 57, 10, 48, 23, 1] <;> decide

private lemma rule25_small_7 : a 7 = 21 := by
  apply rule25_certify (T := 2) (by decide) (by decide) [1, 62, 66, 28, 101, 40, 67, 92, 5, 56, 75, 80, 7, 57, 10, 112, 23, 33, 14, 114, 20, 97, 46, 66] <;> decide

private lemma rule25_small_8 : a 8 = 16 := by
  apply rule25_certify (T := 4) (by decide) (by decide) [1, 126, 130, 60, 197, 88, 139, 176, 23, 97, 46, 194, 92, 133, 184, 11, 113, 22, 226, 44, 197] <;> decide

private lemma rule25_small_9 : a 9 = 9 := by
  apply rule25_certify (T := 4) (by decide) (by decide) [1, 254, 258, 124, 389, 184, 267, 368, 23, 225, 46, 450, 92, 389] <;> decide

private lemma rule25_small (n : ℕ) (hn : n < 10) :
    a n = ([0, 2, 2, 3, 2, 15, 15, 21, 16, 9] : List ℕ).getD n 0 := by
  interval_cases n
  · rfl
  · exact rule25_small_1
  · exact rule25_small_2
  · exact rule25_small_3
  · exact rule25_small_4
  · exact rule25_small_5
  · exact rule25_small_6
  · exact rule25_small_7
  · exact rule25_small_8
  · exact rule25_small_9

end

section

/- The tail law gives the recurrence and the generating function coefficient by coefficient. -/
open OMA.S_oeis_a334513 PowerSeries

private lemma rule25_recurrence (ht : ∀ n : ℕ, 10 ≤ n → a n = 2 * n) :
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 2 * a (n-1) - a (n-2) := by
  intro n hn
  rw [ht n (by omega), ht (n-1) (by omega), ht (n-2) (by omega)]
  omega

private lemma rule25_gf
    (hs : ∀ n : ℕ, n < 10 → a n = ([0,2,2,3,2,15,15,21,16,9] : List ℕ).getD n 0)
    (ht : ∀ n : ℕ, 10 ≤ n → a n = 2*n) :
    mk (fun n => (a n : ℤ)) * (1-X)^2 =
      X * (2 - 2*X + X^2 - 2*X^3 + 14*X^4 - 13*X^5 + 6*X^6 - 11*X^7 -
        2*X^8 + 18*X^9 - 9*X^10) := by
  let A := mk (fun n => (a n : ℤ))
  have lhs : A * (1-X)^2 = A - C 2 * (A * X^1) + A * X^2 := by
    norm_num [map_ofNat]
    ring
  have rhs : X * (2 - 2*X + X^2 - 2*X^3 + 14*X^4 - 13*X^5 + 6*X^6 - 11*X^7 -
      2*X^8 + 18*X^9 - 9*X^10) =
      C (2 : ℤ)*X^1 - C 2*X^2 + X^3 - C 2*X^4 + C 14*X^5 - C 13*X^6 +
        C 6*X^7 - C 11*X^8 - C 2*X^9 + C 18*X^10 - C 9*X^11 := by
    norm_num [map_ofNat]
    ring
  change A * (1-X)^2 = _
  rw [lhs, rhs]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_X_pow, coeff_C]
  by_cases big : 11 < n
  · simp (disch := omega) only [if_neg, if_pos]
    linarith [rule25_recurrence ht n big]
  · have val (k : ℕ) : a k = if k < 10 then
        ([0,2,2,3,2,15,15,21,16,9] : List ℕ).getD k 0 else 2*k := by
      split_ifs with h
      · exact hs _ h
      · exact ht _ (by omega)
    interval_cases n <;> norm_num [val, List.getD]

end

theorem OMA.solution : type_of% @OMA.S_oeis_a334513.main := by
  have tailLaw (n : ℕ) (hn : 10 ≤ n) : a n = 2*n := by
    let _ : NeZero n := ⟨by omega⟩
    apply rule25_large hn
    · intro i
      simpa only [rule25_prev hn] using rule25_eight hn i
    · exact oma_rule_stabilizer hn (rule25_six hn)
    · exact oma_rule_no_odd_shift hn (rule25_six hn) (rule25_seven hn)
  exact ⟨tailLaw, rule25_recurrence tailLaw, rule25_gf rule25_small tailLaw⟩
