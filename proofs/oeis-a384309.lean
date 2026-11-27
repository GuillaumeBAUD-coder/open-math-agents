import OMAStatements.S_oeis_a384309
import Mathlib.Tactic

namespace OMA.Counter384309
open OMA.S_oeis_a384309

abbrev val (t : ℕ) := (state t).1
abbrev visits (t : ℕ) := (state t).2
def count (n : ℕ) (d : Digit) :=
  ((Finset.range n).filter (fun i => leading (i+1) = d)).card
def incoming (c : Digit → ℕ) (d : Digit) := ∑ j, count (c j) d

lemma next_val (t : ℕ) : val (t+1) = visits t (leading (val t))+1 := rfl
lemma next_visits (t : ℕ) (d : Digit) :
    visits (t+1) d = visits t d + if d = leading (val t) then 1 else 0 := rfl

lemma count_succ (n : ℕ) (d : Digit) :
    count (n+1) d = count n d + if leading (n+1) = d then 1 else 0 := by
  by_cases h : leading (n+1) = d <;> simp [h, count, Finset.range_add_one, Finset.filter_insert, Finset.card_insert_of_notMem]

lemma count_mono (d : Digit) : Monotone (fun n => count n d) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [count_succ]
  omega

lemma count_lt_last {m n : ℕ} (h : m < n) :
    count m (leading n) < count n (leading n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have := count_mono (leading (n+1)) (show m ≤ n by omega)
  rw [count_succ]
  simp
  omega

lemma incoming_mono {c v : Digit → ℕ} (h : ∀ j, c j ≤ v j) (d : Digit) :
    incoming c d ≤ incoming v d :=
  Finset.sum_le_sum (fun j _ => count_mono d (h j))

lemma full_predecessor {c v : Digit → ℕ} (hle : ∀ j, c j ≤ v j) (j : Digit)
    (heq : incoming c (leading (v j)) = incoming v (leading (v j))) : c j = v j := by
  by_contra hne
  have hlt := count_lt_last (lt_of_le_of_ne (hle j) hne)
  have : incoming c (leading (v j)) < incoming v (leading (v j)) :=
    Finset.sum_lt_sum (fun i _ => count_mono _ (hle i)) ⟨j, Finset.mem_univ _, hlt⟩
  omega

lemma sum_visits (t : ℕ) : (∑ j, visits t j) = t := by
  induction t with
  | zero => simp [visits, state]
  | succ t ih =>
    simp only [next_visits, Finset.sum_add_distrib, ih]
    simp

/-- Each recorded visit emits one new value. Counting destinations accounts for all visits except the current one and includes the initial digit separately. -/
lemma flow (t : ℕ) (d : Digit) :
    incoming (visits t) d + (if d = 0 then 1 else 0) =
    visits t d + (if d = leading (val t) then 1 else 0) := by
  induction t with
  | zero =>
    have h : leading 1 = 0 := by decide
    simp [incoming, visits, val, state, count, h]
  | succ t ih =>
    have step : incoming (visits (t+1)) d =
        incoming (visits t) d + (if d = leading (val (t+1)) then 1 else 0) := by
      unfold incoming
      let v := if d = leading (val (t+1)) then 1 else 0
      have hs : (∑ i : Digit, if i = leading (val t) then v else 0) = v := by simp
      change _ = _ + v
      rw [← hs, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases he : i = leading (val t)
      · subst i
        simp [v, next_visits, next_val, count_succ, eq_comm]
        rfl
      · simp [next_visits, he]
    rw [step, next_visits]
    omega


lemma leading_block (k : ℕ) (d : Digit) (x : ℕ)
    (lo : (d.val+1)*10^k ≤ x) (hi : x < (d.val+2)*10^k) : leading x = d := by
  have hp : 0 < 10^k := by positivity
  have hd := d.isLt
  have low : 10^k ≤ x := by nlinarith
  have high : x < 10^(k+1) := by
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (10^k) (show d.val+2 ≤ 10 by omega)]
  have hx := Nat.log_eq_of_pow_le_of_lt_pow low high
  have hdiv : x/10^k = d.val+1 := Nat.div_eq_of_lt_le lo (by simpa [Nat.add_assoc] using hi)
  apply Fin.ext
  simp [leading, hx, hdiv, Nat.mod_eq_of_lt hd]

lemma count_block {s : ℕ} (k : ℕ) (c d : Digit)
    (h : ∀ x, s < x → x ≤ s+k → leading x = c) :
    count (s+k) d = count s d + if c = d then k else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show s+(k+1) = (s+k)+1 by omega, count_succ, h _ (by omega) (by omega),
      ih (fun x hx hy => h x hx (by omega))]
    split <;> omega

lemma decimal_count (k j : ℕ) (hj : j ≤ 9) (d : Digit) :
    count ((j+1)*10^k-1) d = count (10^k-1) d + if d.val < j then 10^k else 0 := by
  have hp : 0 < 10^k := by positivity
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < 9 := by omega
    let c : Digit := ⟨j,hj'⟩
    have hs : (j+1+1)*10^k-1 = ((j+1)*10^k-1)+10^k := by
      rw [Nat.add_mul, one_mul]
      have : 0 < (j+1)*10^k := by positivity
      omega
    rw [hs, count_block _ c d (by
      intro x hx hy
      apply leading_block k c x
      · change (j+1)*10^k ≤ x
        omega
      · change x < (j+1+1)*10^k
        omega), ih (by omega)]
    by_cases he : c = d
    · subst d
      simp [c]
    · have hne : d.val ≠ j := fun h => he (Fin.ext h.symm)
      simp [he, show (d.val < j+1) ↔ d.val < j by omega]

lemma uniform_count (k : ℕ) (d : Digit) : 9*count (10^k-1) d = 10^k-1 := by
  induction k with
  | zero => simp [count]
  | succ k ih =>
    have h := decimal_count k 9 (by decide) d
    have hd := d.isLt
    simp only [show 9+1 = 10 by decide, if_pos hd, ← pow_succ'] at h
    rw [h, pow_succ]
    have hp : 0 < 10^k := by positivity
    omega


/-- The proposed terminal counters at decimal scale D, in leading-digit order 1 through 9. -/
def cap (D : ℕ) (d : Digit) := if d = 0 then 9*D else if d = 8 then D-1 else 2*D-1

lemma sum_cap (D : ℕ) (hD : 0 < D) : (∑ d, cap D d) = 24*D-8 := by
  simp (disch := decide) [Fin.sum_univ_succ, cap]
  omega

lemma cap_first (k : ℕ) : leading (cap (10^k) 0) = 8 := by
  simp [cap]
  apply leading_block k (8 : Digit)
  · rfl
  · change 9*10^k < 10*10^k
    have : 0 < 10^k := by positivity
    omega

lemma cap_middle (k : ℕ) (j : Digit) (h0 : j ≠ 0) (h8 : j ≠ 8) :
    leading (cap (10^k) j) = 0 := by
  simp [cap, h0, h8]
  apply leading_block k (0 : Digit)
  · change 1*10^k ≤ 2*10^k-1
    have : 0 < 10^k := by positivity
    omega
  · change 2*10^k-1 < 2*10^k
    have : 0 < 10^k := by positivity
    omega

lemma cap_last (k : ℕ) (hk : 0 < k) : leading (cap (10^k) 8) = 8 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  norm_num [cap, pow_succ]
  apply leading_block k (8 : Digit)
  · change 9*10^k ≤ 10^k*10-1
    have : 0 < 10^k := by positivity
    omega
  · change 10^k*10-1 < 10*10^k
    have : 0 < 10^k := by positivity
    omega

lemma cap_flow (k : ℕ) (d : Digit) :
    incoming (cap (10^k)) d + (if d = 0 then 1 else 0) =
      cap (10^k) d + (if d = 8 then 1 else 0) := by
  let D := 10^k
  have hp : 0 < D := by dsimp [D]; positivity
  have hsum : incoming (cap D) d = count (9*D) d + 7*count (2*D-1) d + count (D-1) d := by
    simp (disch := decide) [incoming, cap, Fin.sum_univ_succ]
    omega
  have h1 : count (2*D-1) d = count (D-1) d + if d.val < 1 then D else 0 :=
    decimal_count k 1 (by decide) d
  have h8 : count (9*D-1) d = count (D-1) d + if d.val < 8 then D else 0 :=
    decimal_count k 8 (by decide) d
  have h9 : count (9*D) d = count (9*D-1) d + if (8 : Digit) = d then 1 else 0 := by
    have he : 9*D-1+1 = 9*D := by omega
    have hh := count_succ (9*D-1) d
    rw [he] at hh
    have hl : leading (9*D) = 8 := by simpa [D, cap] using cap_first k
    rwa [hl] at hh
  have hc : 9*count (D-1) d = D-1 := uniform_count k d
  change incoming (cap D) d + _ = cap D d + _
  rw [hsum, h9, h8, h1]
  by_cases h0 : d=0
  · subst d
    norm_num [cap, show (8:Digit) ≠ 0 by decide, show (0:Digit) ≠ 8 by decide] at *
    omega
  by_cases hroot : d=8
  · subst d
    norm_num [cap, show (8:Digit) ≠ 0 by decide, show (0:Digit) ≠ 8 by decide] at *
    omega
  have hne0 : d.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hne8 : d.val ≠ 8 := fun h => hroot (Fin.ext h)
  have hd := d.isLt
  simp [cap, h0, hroot, Ne.symm hroot, show ¬ d.val < 1 by omega, show d.val < 8 by omega]
  omega

/-- Once the current stack is exhausted, flow balance forces it to be digit 9. The final edge of digit 1 leads to 9, and the final edges of digits 2 through 8 lead to 1. All stacks must therefore be exhausted. -/
lemma blocked {k t : ℕ} (hle : ∀ j, visits t j ≤ cap (10^k) j)
    (hblock : visits t (leading (val t)) = cap (10^k) (leading (val t))) :
    ∀ j, visits t j = cap (10^k) j := by
  let v := cap (10^k)
  let cur := leading (val t)
  have fcur := flow t cur
  have vcur := cap_flow k cur
  have inc := incoming_mono hle cur
  change visits t cur = v cur at hblock
  change incoming (visits t) cur + _ = visits t cur + (if cur=cur then 1 else 0) at fcur
  change incoming v cur + _ = v cur + _ at vcur
  change incoming (visits t) cur ≤ incoming v cur at inc
  have hroot : cur=8 := by
    by_contra h
    simp [h] at fcur vcur
    omega
  have hrootinc : incoming (visits t) 8 = incoming v 8 := by
    rw [← hroot]
    simp [hroot] at fcur vcur hblock ⊢
    omega
  have hfirst : visits t 0 = v 0 := by
    apply full_predecessor hle
    simpa [v, cap_first] using hrootinc
  have hfirstinc : incoming (visits t) 0 = incoming v 0 := by
    have hf := flow t (0:Digit)
    have hv := cap_flow k (0:Digit)
    change incoming (visits t) 0 + _ = visits t 0 + (if (0:Digit)=cur then 1 else 0) at hf
    change incoming v 0 + _ = v 0 + _ at hv
    norm_num [hroot] at hf hv
    omega
  intro j
  by_cases h0 : j = 0
  · simpa [h0] using hfirst
  by_cases h8 : j = 8
  · simpa [h8, hroot, v] using hblock
  apply full_predecessor hle
  simpa [cap_middle k j h0 h8, v] using hfirstinc


def endTime (k : ℕ) := 24*10^k-8

lemma time_when_full (k t : ℕ) (h : ∀ j, visits t j = cap (10^k) j) :
    t = endTime k := by
  rw [← sum_visits t]
  simp_rw [h]
  exact sum_cap _ (by positivity)

/-- Before the total number of available edges has been used, the walk can take its next edge without exceeding any terminal counter. The last edge at digit 9 returns to 9. -/
lemma barrier (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : t ≤ endTime k) :
    (∀ j, visits t j ≤ cap (10^k) j) ∧
    (visits t 8 = cap (10^k) 8 → val t = cap (10^k) 8 ∧ t = endTime k) := by
  induction t with
  | zero =>
    refine ⟨fun _ => Nat.zero_le _, ?_⟩
    have hp : 10 ≤ 10^k := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 10) (show 1 ≤ k by omega)
    change 0 = 10^k-1 → _
    omega
  | succ t ih =>
    obtain ⟨hle,hroot⟩ := ih (by omega)
    have hfree : visits t (leading (val t)) < cap (10^k) (leading (val t)) := by
      apply lt_of_le_of_ne (hle _)
      intro he
      have := time_when_full k t (blocked hle he)
      omega
    have hnext : ∀ j, visits (t+1) j ≤ cap (10^k) j := by
      intro j
      rw [next_visits]
      by_cases h : j = leading (val t)
      · subst j
        simpa using hfree
      · simpa [h] using hle j
    refine ⟨hnext, ?_⟩
    intro he
    have hprev : visits t 8 ≠ cap (10^k) 8 := fun h => by
      have := (hroot h).2
      omega
    have hlead : leading (val t) = 8 := by
      by_contra hn
      apply hprev
      simpa [next_visits, Ne.symm hn] using he
    have hx : val (t+1) = cap (10^k) 8 := by
      simpa [next_val, next_visits, hlead] using he
    have hlead' : leading (val (t+1)) = 8 := hx ▸ cap_last k hk
    refine ⟨hx, time_when_full k (t+1) (blocked hnext ?_)⟩
    simpa [hlead'] using he

lemma boundary (k : ℕ) (hk : 0 < k) :
    (∀ j, visits (endTime k) j = cap (10^k) j) ∧ val (endTime k) = 10^k-1 := by
  obtain ⟨hle,hroot⟩ := barrier k hk (endTime k) le_rfl
  have hsum : (∑ j, visits (endTime k) j) = ∑ j, cap (10^k) j := by
    rw [sum_visits, sum_cap _ (by positivity)]
    rfl
  have heq (j : Digit) : visits (endTime k) j = cap (10^k) j := by
    by_contra hne
    have hlt := Finset.sum_lt_sum (fun i _ => hle i)
      ⟨j, Finset.mem_univ _, lt_of_le_of_ne (hle j) hne⟩
    omega
  exact ⟨heq, (hroot (heq 8)).1⟩

lemma visits_mono (d : Digit) : Monotone (fun t => visits t d) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [next_visits]
  omega

lemma visits_after (k : ℕ) (hk : 0 < k) {t : ℕ} (ht : endTime k ≤ t) (d : Digit) :
    10^k-1 ≤ visits t d := by
  have heq := (boundary k hk).1 d
  have hm : visits (endTime k) d ≤ visits t d := visits_mono d ht
  simp only [cap] at heq
  split_ifs at heq <;> omega


def hits (x t : ℕ) := ((Finset.range t).filter (fun i => val i = x)).card
def covered (x : ℕ) (c : Digit → ℕ) : ℕ := ∑ j, if x ≤ c j then 1 else 0

lemma hits_succ (x t : ℕ) : hits x (t+1) = hits x t + if val t = x then 1 else 0 := by
  by_cases h : val t = x <;> simp [hits, Finset.range_add_one, Finset.filter_insert, h]

/-- A stack with counter c has emitted precisely one copy of every positive integer up to c. -/
lemma tally (x : ℕ) (hx : 0 < x) (t : ℕ) :
    hits x (t+1) = covered x (visits t) + if x=1 then 1 else 0 := by
  induction t with
  | zero =>
    have hz : covered x (visits 0) = 0 := by
      simp [covered, visits, state, Nat.not_le_of_lt hx]
    rw [hits_succ, hz]
    change 0 + (if 1=x then 1 else 0) = 0 + (if x=1 then 1 else 0)
    simp [eq_comm]
  | succ t ih =>
    have hstep : covered x (visits (t+1)) =
        covered x (visits t) + (if val (t+1) = x then 1 else 0) := by
      unfold covered
      let v := if val (t+1) = x then 1 else 0
      have hs : (∑ i : Digit, if i = leading (val t) then v else 0) = v := by simp
      change _ = _ + v
      rw [← hs, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases he : i = leading (val t)
      · subst i
        simp only [next_visits, if_true, v, next_val]
        have bump (a : ℕ) : (if x ≤ a+1 then 1 else 0 : ℕ) =
            (if x ≤ a then 1 else 0) + (if a+1=x then 1 else 0) := by
          split_ifs <;> omega
        exact bump _
      · simp [next_visits, he]
    rw [hits_succ, ih, hstep]
    omega

lemma multiplicity (x : ℕ) (hx : 0 < x) :
    ∃ M, ∀ m ≥ M, hits x m = if x=1 then 10 else 9 := by
  let k := x+1
  have hpow (j : ℕ) : j < 10^j := by
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ]; omega
  refine ⟨endTime k+1, ?_⟩
  intro m hm
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hall (d : Digit) : x ≤ visits m d := by
    have ha := visits_after k (by dsimp [k]; omega) (show endTime k ≤ m by omega) d
    have hb := hpow k
    dsimp [k] at hb ha
    omega
  rw [tally x hx]
  simp [covered, hall]
  split <;> decide

lemma final_position (k : ℕ) (hk : 0 < k) :
    entry (24*10^k-7) = 10^k-1 ∧ ∀ n > 24*10^k-7, 10^k ≤ entry n := by
  have hD : 0 < 10^k := by positivity
  constructor
  · have he : (24*10^k-7)-1 = endTime k := by unfold endTime; omega
    simpa only [entry, he, val] using (boundary k hk).2
  · intro n hn
    have hm : endTime k ≤ n-2 := by unfold endTime; omega
    have hsucc : n-1 = n-2+1 := by omega
    change 10^k ≤ val (n-1)
    rw [hsucc, next_val]
    have := visits_after k hk hm (leading (val (n-2)))
    omega

end OMA.Counter384309

theorem OMA.solution : type_of% @OMA.S_oeis_a384309.main :=
  ⟨OMA.Counter384309.multiplicity, OMA.Counter384309.final_position⟩
