import OMAStatements.S_oeis_a266430
import Mathlib

/-!
# oeis-a266430: counting the 4 X n arrays

Split an array (a list of columns) into its first column and the rest. The local conditions
are a chain condition, and each lexicographic comparison of consecutive rows is decided at the first position
where the two differ, so it only adds a flag saying whether the comparison is still pending. The
numbers of valid arrays with a given first column and given pending flags satisfy a linear
recursion over the next column; their explicit polynomial closed forms are checked by induction
over the 16 possible first columns and all flag settings. Summing them gives Hardin's
polynomial, and the generating function and Barker's recurrence follow from it.

Source: OEIS A266430, https://oeis.org/A266430.
-/
namespace OMA.P_oeis_a266430

open OMA.S_oeis_a266430

abbrev R := Fin 4 → Fin 2

lemma lexle (r s : R) : toLex r ≤ toLex s ↔ (r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ (r 2 < s 2 ∨ (r 2 = s 2 ∧ r 3 ≤ s 3)))))) := by
  rw [le_iff_lt_or_eq]
  change (∃ i, (∀ j, j < i → r j = s j) ∧ r i < s i) ∨ r = s ↔ _
  rw [funext_iff]
  simp only [Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one, IsEmpty.exists_iff,
    IsEmpty.forall_iff]
  simp +decide only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, lt_self_iff_false, false_imp_iff, true_imp_iff, and_true, true_and, or_false]
  rw [le_iff_lt_or_eq (a := r 3)]
  tauto

lemma sumk (g : R → ℚ) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, ∑ y3 : Fin 2, g ![y0, y1, y2, y3] := by
  let e : Fin 2 × Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2], fun f => (f 0, f 1, f 2, f 3), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def rowOK (_r : R) : Prop := True

def adj (r s : R) : Prop := toLex r ≤ toLex s ∧ ∑ i, (r i : ℕ) ≤ ∑ i, (s i : ℕ)

/-- A decidable form of `adj`. -/
def adjE (r s : R) : Prop :=
  (r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ (r 2 < s 2 ∨ (r 2 = s 2 ∧ r 3 ≤ s 3)))))) ∧
    ∑ i, (r i : ℕ) ≤ ∑ i, (s i : ℕ)

lemma adj_iff (r s : R) : adj r s ↔ adjE r s := by unfold adj adjE; rw [lexle]

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
instance (r s : R) : Decidable (adjE r s) := by unfold adjE; infer_instance

open Classical

def Pall (l : List R) : Prop := (∀ r ∈ l, rowOK r) ∧ l.IsChain adj

def C0 (l : List R) : Prop := l.map (fun r => r 0) ≤ l.map (fun r => r 1)
def C1 (l : List R) : Prop := l.map (fun r => r 1) ≤ l.map (fun r => r 2)
def C2 (l : List R) : Prop := l.map (fun r => r 2) ≤ l.map (fun r => r 3)

lemma isSol_iff (l : List R) : IsSolution l ↔ Pall l ∧ C0 l ∧ C1 l ∧ C2 l := by
  unfold IsSolution Pall rowOK adj C0 C1 C2
  simp only [Fin.forall_fin_succ, Fin.forall_fin_one, IsEmpty.forall_iff, Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.succ_one_eq_two, Fin.castSucc_one, Fin.reduceSucc, Fin.reduceCastSucc, implies_true, true_and]
  tauto

lemma pall_cons_nil (r : R) : Pall [r] ↔ rowOK r := by
  simp [Pall]

lemma pall_cons_cons (r s : R) (m : List R) :
    Pall (r :: s :: m) ↔ rowOK r ∧ adj r s ∧ Pall (s :: m) := by
  unfold Pall
  rw [List.isChain_cons]
  simp only [List.mem_cons, forall_eq_or_imp, List.head?_cons, Option.mem_def,
    Option.some.injEq, forall_eq']
  tauto

lemma lcons (a b : Fin 2) (l m : List (Fin 2)) : a :: l ≤ b :: m ↔ a < b ∨ (a = b ∧ l ≤ m) := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  change (List.Lex (· < ·) _ _ ∨ _) ↔ (_ ∨ _ ∧ (List.Lex (· < ·) _ _ ∨ _))
  rw [List.cons_lex_cons_iff, List.cons.injEq]
  tauto

lemma c0_cons (r : R) (l : List R) : C0 (r :: l) ↔ r 0 < r 1 ∨ (r 0 = r 1 ∧ C0 l) := by
  unfold C0; simp only [List.map_cons]; exact lcons _ _ _ _

lemma c1_cons (r : R) (l : List R) : C1 (r :: l) ↔ r 1 < r 2 ∨ (r 1 = r 2 ∧ C1 l) := by
  unfold C1; simp only [List.map_cons]; exact lcons _ _ _ _

lemma c2_cons (r : R) (l : List R) : C2 (r :: l) ↔ r 2 < r 3 ∨ (r 2 = r 3 ∧ C2 l) := by
  unfold C2; simp only [List.map_cons]; exact lcons _ _ _ _

lemma c_nil0 : C0 [] := by unfold C0; simp
lemma c_nil1 : C1 [] := by unfold C1; simp
lemma c_nil2 : C2 [] := by unfold C2; simp

def LL : ℕ → Finset (List R)
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset R) ×ˢ LL n).image (fun p => p.1 :: p.2)

lemma mem_LL (n : ℕ) (l : List R) : l ∈ LL n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [LL]
  | succ n ih =>
    cases l with
    | nil => simp [LL]
    | cons x m => simp [LL, ih]

lemma card_cons (n : ℕ) (Q : List R → Prop) [DecidablePred Q] :
    ((LL (n + 1)).filter Q).card = ∑ s : R, ((LL n).filter (fun m => Q (s :: m))).card := by
  rw [LL, Finset.filter_image, Finset.card_image_of_injective _ (by
    intro p q h; simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2)]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter]

/-- The pending track comparisons. -/
def Q (b0 b1 b2 : Bool) (l : List R) : Prop := Pall l ∧ (b0 = true → C0 l) ∧ (b1 = true → C1 l) ∧ (b2 = true → C2 l)

/-- Condition on the first letter. -/
def okT (b0 b1 b2 : Bool) (r : R) : Prop := rowOK r ∧ (b0 = true → r 0 ≤ r 1) ∧ (b1 = true → r 1 ≤ r 2) ∧ (b2 = true → r 2 ≤ r 3)

instance (b0 b1 b2 : Bool) (r : R) : Decidable (okT b0 b1 b2 r) := by
  unfold okT; infer_instance

noncomputable def f (b0 b1 b2 : Bool) (n : ℕ) (r : R) : ℕ :=
  ((LL n).filter (fun l => Q b0 b1 b2 (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f true true true n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q true true true)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, Q, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma aux (b : Bool) (x y : Fin 2) (C : Prop) :
    (b = true → (x < y ∨ (x = y ∧ C))) ↔ (b = true → x ≤ y) ∧ ((b && decide (x = y)) = true → C) := by
  cases b
  · simp
  · simp only [true_imp_iff, Bool.true_and, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨h, hc⟩)
      · exact ⟨h.le, fun he => absurd he h.ne⟩
      · exact ⟨h.le, fun _ => hc⟩
    · rintro ⟨h, hc⟩
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', hc h'⟩

lemma aux1 (b : Bool) (x y : Fin 2) (C : Prop) (hC : C) :
    (b = true → (x < y ∨ (x = y ∧ C))) ↔ (b = true → x ≤ y) := by
  rw [aux]; constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun _ => hC⟩

lemma q_single (b0 b1 b2 : Bool) (r : R) : Q b0 b1 b2 [r] ↔ okT b0 b1 b2 r := by
  unfold Q okT
  rw [pall_cons_nil, c0_cons, c1_cons, c2_cons]
  have h0 := c_nil0; have h1 := c_nil1; have h2 := c_nil2
  simp only [aux1 _ _ _ _ h0, aux1 _ _ _ _ h1, aux1 _ _ _ _ h2]

lemma q_cons (b0 b1 b2 : Bool) (r s : R) (m : List R) :
    Q b0 b1 b2 (r :: s :: m) ↔ (okT b0 b1 b2 r ∧ adj r s) ∧ Q (b0 && decide (r 0 = r 1)) (b1 && decide (r 1 = r 2)) (b2 && decide (r 2 = r 3)) (s :: m) := by
  unfold Q okT
  rw [pall_cons_cons, c0_cons, c1_cons, c2_cons, aux, aux, aux]
  tauto

lemma f_zero (b0 b1 b2 : Bool) (r : R) :
    f b0 b1 b2 0 r = if okT b0 b1 b2 r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT b0 b1 b2 r
  · rw [if_pos ((q_single b0 b1 b2 r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((q_single b0 b1 b2 r).mp h')), if_neg h]; rfl

lemma f_succ (b0 b1 b2 : Bool) (n : ℕ) (r : R) :
    f b0 b1 b2 (n + 1) r = ∑ s : R, if okT b0 b1 b2 r ∧ adjE r s then
      f (b0 && decide (r 0 = r 1)) (b1 && decide (r 1 = r 2)) (b2 && decide (r 2 = r 3)) n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [q_cons, adj_iff]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

def T000 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((1 : ℚ) / 151200) * x ^ 10 + ((13 : ℚ) / 72576) * x ^ 9 + ((109 : ℚ) / 40320) * x ^ 8 + ((1291 : ℚ) / 50400) * x ^ 7 + ((2321 : ℚ) / 14400) * x ^ 6 + ((250357 : ℚ) / 362880) * x ^ 5 + ((243343 : ℚ) / 120960) * x ^ 4 + ((443837 : ℚ) / 113400) * x ^ 3 + ((81049 : ℚ) / 16800) * x ^ 2 + ((93427 : ℚ) / 27720) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((11 : ℚ) / 181440) * x ^ 9 + ((23 : ℚ) / 17280) * x ^ 8 + ((241 : ℚ) / 15120) * x ^ 7 + ((1267 : ℚ) / 10800) * x ^ 6 + ((967 : ℚ) / 1728) * x ^ 5 + ((638807 : ℚ) / 362880) * x ^ 4 + ((327689 : ℚ) / 90720) * x ^ 3 + ((33271 : ℚ) / 7200) * x ^ 2 + ((8347 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 90720) * x ^ 9 + ((1 : ℚ) / 2016) * x ^ 8 + ((13 : ℚ) / 1512) * x ^ 7 + ((19 : ℚ) / 240) * x ^ 6 + ((377 : ℚ) / 864) * x ^ 5 + ((145 : ℚ) / 96) * x ^ 4 + ((29969 : ℚ) / 9072) * x ^ 3 + ((11113 : ℚ) / 2520) * x ^ 2 + ((4097 : ℚ) / 1260) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 560) * x ^ 7 + ((37 : ℚ) / 1440) * x ^ 6 + ((47 : ℚ) / 240) * x ^ 5 + ((2507 : ℚ) / 2880) * x ^ 4 + ((139 : ℚ) / 60) * x ^ 3 + ((18163 : ℚ) / 5040) * x ^ 2 + ((209 : ℚ) / 70) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((11 : ℚ) / 5040) * x ^ 7 + ((47 : ℚ) / 1440) * x ^ 6 + ((11 : ℚ) / 45) * x ^ 5 + ((3007 : ℚ) / 2880) * x ^ 4 + ((1907 : ℚ) / 720) * x ^ 3 + ((2197 : ℚ) / 560) * x ^ 2 + ((326 : ℚ) / 105) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2520) * x ^ 7 + ((1 : ℚ) / 90) * x ^ 6 + ((43 : ℚ) / 360) * x ^ 5 + ((47 : ℚ) / 72) * x ^ 4 + ((89 : ℚ) / 45) * x ^ 3 + ((1201 : ℚ) / 360) * x ^ 2 + ((1219 : ℚ) / 420) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((7 : ℚ) / 120) * x ^ 5 + ((4 : ℚ) / 9) * x ^ 4 + ((13 : ℚ) / 8) * x ^ 3 + ((1099 : ℚ) / 360) * x ^ 2 + ((169 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((5 : ℚ) / 12) * x ^ 3 + ((35 : ℚ) / 24) * x ^ 2 + ((25 : ℚ) / 12) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 20) * x ^ 5 + ((13 : ℚ) / 36) * x ^ 4 + ((4 : ℚ) / 3) * x ^ 3 + ((949 : ℚ) / 360) * x ^ 2 + ((157 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((5 : ℚ) / 24) * x ^ 4 + (1 : ℚ) * x ^ 3 + ((55 : ℚ) / 24) * x ^ 2 + ((149 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 12) * x ^ 4 + ((2 : ℚ) / 3) * x ^ 3 + ((23 : ℚ) / 12) * x ^ 2 + ((7 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def T001 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((1 : ℚ) / 181440) * x ^ 10 + ((47 : ℚ) / 362880) * x ^ 9 + ((107 : ℚ) / 60480) * x ^ 8 + ((781 : ℚ) / 50400) * x ^ 7 + ((799 : ℚ) / 8640) * x ^ 6 + ((136579 : ℚ) / 362880) * x ^ 5 + ((196559 : ℚ) / 181440) * x ^ 4 + ((1186163 : ℚ) / 453600) * x ^ 3 + ((3853 : ℚ) / 1008) * x ^ 2 + ((41483 : ℚ) / 13860) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((11 : ℚ) / 181440) * x ^ 9 + ((23 : ℚ) / 17280) * x ^ 8 + ((241 : ℚ) / 15120) * x ^ 7 + ((1267 : ℚ) / 10800) * x ^ 6 + ((967 : ℚ) / 1728) * x ^ 5 + ((638807 : ℚ) / 362880) * x ^ 4 + ((327689 : ℚ) / 90720) * x ^ 3 + ((33271 : ℚ) / 7200) * x ^ 2 + ((8347 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 720) * x ^ 7 + ((5 : ℚ) / 288) * x ^ 6 + ((17 : ℚ) / 144) * x ^ 5 + ((1427 : ℚ) / 2880) * x ^ 4 + ((437 : ℚ) / 360) * x ^ 3 + ((2507 : ℚ) / 1008) * x ^ 2 + ((8 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 560) * x ^ 7 + ((31 : ℚ) / 1440) * x ^ 6 + ((3 : ℚ) / 20) * x ^ 5 + ((1607 : ℚ) / 2880) * x ^ 4 + ((371 : ℚ) / 240) * x ^ 3 + ((14719 : ℚ) / 5040) * x ^ 2 + ((1177 : ℚ) / 420) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2520) * x ^ 7 + ((1 : ℚ) / 90) * x ^ 6 + ((43 : ℚ) / 360) * x ^ 5 + ((47 : ℚ) / 72) * x ^ 4 + ((89 : ℚ) / 45) * x ^ 3 + ((1201 : ℚ) / 360) * x ^ 2 + ((1219 : ℚ) / 420) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 4) * x ^ 3 + ((23 : ℚ) / 24) * x ^ 2 + ((7 : ℚ) / 4) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 30) * x ^ 5 + ((17 : ℚ) / 72) * x ^ 4 + ((2 : ℚ) / 3) * x ^ 3 + ((317 : ℚ) / 180) * x ^ 2 + ((23 : ℚ) / 10) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((5 : ℚ) / 24) * x ^ 4 + (1 : ℚ) * x ^ 3 + ((55 : ℚ) / 24) * x ^ 2 + ((149 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def T010 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((11 : ℚ) / 1814400) * x ^ 10 + ((13 : ℚ) / 90720) * x ^ 9 + ((233 : ℚ) / 120960) * x ^ 8 + ((5071 : ℚ) / 302400) * x ^ 7 + ((8393 : ℚ) / 86400) * x ^ 6 + ((17873 : ℚ) / 45360) * x ^ 5 + ((428801 : ℚ) / 362880) * x ^ 4 + ((1171273 : ℚ) / 453600) * x ^ 3 + ((187451 : ℚ) / 50400) * x ^ 2 + ((83351 : ℚ) / 27720) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((1 : ℚ) / 18144) * x ^ 9 + ((25 : ℚ) / 24192) * x ^ 8 + ((331 : ℚ) / 30240) * x ^ 7 + ((401 : ℚ) / 5400) * x ^ 6 + ((1391 : ℚ) / 4320) * x ^ 5 + ((71263 : ℚ) / 72576) * x ^ 4 + ((203107 : ℚ) / 90720) * x ^ 3 + ((57839 : ℚ) / 16800) * x ^ 2 + ((7379 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 90720) * x ^ 9 + ((1 : ℚ) / 2016) * x ^ 8 + ((13 : ℚ) / 1512) * x ^ 7 + ((19 : ℚ) / 240) * x ^ 6 + ((377 : ℚ) / 864) * x ^ 5 + ((145 : ℚ) / 96) * x ^ 4 + ((29969 : ℚ) / 9072) * x ^ 3 + ((11113 : ℚ) / 2520) * x ^ 2 + ((4097 : ℚ) / 1260) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 560) * x ^ 7 + ((37 : ℚ) / 1440) * x ^ 6 + ((47 : ℚ) / 240) * x ^ 5 + ((2507 : ℚ) / 2880) * x ^ 4 + ((139 : ℚ) / 60) * x ^ 3 + ((18163 : ℚ) / 5040) * x ^ 2 + ((209 : ℚ) / 70) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 20) * x ^ 5 + ((5 : ℚ) / 18) * x ^ 4 + (1 : ℚ) * x ^ 3 + ((799 : ℚ) / 360) * x ^ 2 + ((49 : ℚ) / 20) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 4) * x ^ 3 + ((23 : ℚ) / 24) * x ^ 2 + ((7 : ℚ) / 4) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 24) * x ^ 5 + ((17 : ℚ) / 72) * x ^ 4 + ((19 : ℚ) / 24) * x ^ 3 + ((317 : ℚ) / 180) * x ^ 2 + ((13 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((1 : ℚ) / 6) * x ^ 4 + ((7 : ℚ) / 12) * x ^ 3 + ((4 : ℚ) / 3) * x ^ 2 + ((19 : ℚ) / 10) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 12) * x ^ 4 + ((2 : ℚ) / 3) * x ^ 3 + ((23 : ℚ) / 12) * x ^ 2 + ((7 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def T011 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((1 : ℚ) / 201600) * x ^ 10 + ((17 : ℚ) / 181440) * x ^ 9 + ((1 : ℚ) / 960) * x ^ 8 + ((2431 : ℚ) / 302400) * x ^ 7 + ((1159 : ℚ) / 28800) * x ^ 6 + ((5995 : ℚ) / 36288) * x ^ 5 + ((1489 : ℚ) / 3360) * x ^ 4 + ((150877 : ℚ) / 113400) * x ^ 3 + ((566 : ℚ) / 225) * x ^ 2 + ((34597 : ℚ) / 13860) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((1 : ℚ) / 18144) * x ^ 9 + ((25 : ℚ) / 24192) * x ^ 8 + ((331 : ℚ) / 30240) * x ^ 7 + ((401 : ℚ) / 5400) * x ^ 6 + ((1391 : ℚ) / 4320) * x ^ 5 + ((71263 : ℚ) / 72576) * x ^ 4 + ((203107 : ℚ) / 90720) * x ^ 3 + ((57839 : ℚ) / 16800) * x ^ 2 + ((7379 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 720) * x ^ 7 + ((5 : ℚ) / 288) * x ^ 6 + ((17 : ℚ) / 144) * x ^ 5 + ((1427 : ℚ) / 2880) * x ^ 4 + ((437 : ℚ) / 360) * x ^ 3 + ((2507 : ℚ) / 1008) * x ^ 2 + ((8 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 12) * x ^ 3 + ((11 : ℚ) / 24) * x ^ 2 + ((17 : ℚ) / 12) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 40) * x ^ 5 + ((1 : ℚ) / 9) * x ^ 4 + ((7 : ℚ) / 24) * x ^ 3 + ((319 : ℚ) / 360) * x ^ 2 + ((101 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 60) * x ^ 5 + ((1 : ℚ) / 6) * x ^ 4 + ((7 : ℚ) / 12) * x ^ 3 + ((4 : ℚ) / 3) * x ^ 2 + ((19 : ℚ) / 10) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def T100 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((1 : ℚ) / 151200) * x ^ 10 + ((61 : ℚ) / 362880) * x ^ 9 + ((31 : ℚ) / 13440) * x ^ 8 + ((2963 : ℚ) / 151200) * x ^ 7 + ((1601 : ℚ) / 14400) * x ^ 6 + ((160561 : ℚ) / 362880) * x ^ 5 + ((153631 : ℚ) / 120960) * x ^ 4 + ((148091 : ℚ) / 56700) * x ^ 3 + ((182267 : ℚ) / 50400) * x ^ 2 + ((81107 : ℚ) / 27720) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((11 : ℚ) / 181440) * x ^ 9 + ((149 : ℚ) / 120960) * x ^ 8 + ((199 : ℚ) / 15120) * x ^ 7 + ((461 : ℚ) / 5400) * x ^ 6 + ((631 : ℚ) / 1728) * x ^ 5 + ((395123 : ℚ) / 362880) * x ^ 4 + ((209501 : ℚ) / 90720) * x ^ 3 + ((167557 : ℚ) / 50400) * x ^ 2 + ((7087 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 90720) * x ^ 9 + ((1 : ℚ) / 2016) * x ^ 8 + ((59 : ℚ) / 7560) * x ^ 7 + ((1 : ℚ) / 16) * x ^ 6 + ((257 : ℚ) / 864) * x ^ 5 + ((89 : ℚ) / 96) * x ^ 4 + ((91381 : ℚ) / 45360) * x ^ 3 + ((1517 : ℚ) / 504) * x ^ 2 + ((3377 : ℚ) / 1260) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 560) * x ^ 7 + ((11 : ℚ) / 480) * x ^ 6 + ((7 : ℚ) / 48) * x ^ 5 + ((529 : ℚ) / 960) * x ^ 4 + ((7 : ℚ) / 5) * x ^ 3 + ((12227 : ℚ) / 5040) * x ^ 2 + ((103 : ℚ) / 42) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((11 : ℚ) / 5040) * x ^ 7 + ((47 : ℚ) / 1440) * x ^ 6 + ((11 : ℚ) / 45) * x ^ 5 + ((3007 : ℚ) / 2880) * x ^ 4 + ((1907 : ℚ) / 720) * x ^ 3 + ((2197 : ℚ) / 560) * x ^ 2 + ((326 : ℚ) / 105) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2520) * x ^ 7 + ((1 : ℚ) / 90) * x ^ 6 + ((43 : ℚ) / 360) * x ^ 5 + ((47 : ℚ) / 72) * x ^ 4 + ((89 : ℚ) / 45) * x ^ 3 + ((1201 : ℚ) / 360) * x ^ 2 + ((1219 : ℚ) / 420) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((7 : ℚ) / 120) * x ^ 5 + ((4 : ℚ) / 9) * x ^ 4 + ((13 : ℚ) / 8) * x ^ 3 + ((1099 : ℚ) / 360) * x ^ 2 + ((169 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((5 : ℚ) / 12) * x ^ 3 + ((35 : ℚ) / 24) * x ^ 2 + ((25 : ℚ) / 12) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + (1 : ℚ) * x ^ 2 + ((11 : ℚ) / 6) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def T101 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((1 : ℚ) / 181440) * x ^ 10 + ((43 : ℚ) / 362880) * x ^ 9 + ((89 : ℚ) / 60480) * x ^ 8 + ((1733 : ℚ) / 151200) * x ^ 7 + ((547 : ℚ) / 8640) * x ^ 6 + ((85087 : ℚ) / 362880) * x ^ 5 + ((133433 : ℚ) / 181440) * x ^ 4 + ((790843 : ℚ) / 453600) * x ^ 3 + ((13607 : ℚ) / 5040) * x ^ 2 + ((6959 : ℚ) / 2772) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((11 : ℚ) / 181440) * x ^ 9 + ((149 : ℚ) / 120960) * x ^ 8 + ((199 : ℚ) / 15120) * x ^ 7 + ((461 : ℚ) / 5400) * x ^ 6 + ((631 : ℚ) / 1728) * x ^ 5 + ((395123 : ℚ) / 362880) * x ^ 4 + ((209501 : ℚ) / 90720) * x ^ 3 + ((167557 : ℚ) / 50400) * x ^ 2 + ((7087 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 720) * x ^ 7 + ((7 : ℚ) / 480) * x ^ 6 + ((61 : ℚ) / 720) * x ^ 5 + ((289 : ℚ) / 960) * x ^ 4 + ((287 : ℚ) / 360) * x ^ 3 + ((8489 : ℚ) / 5040) * x ^ 2 + ((127 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 560) * x ^ 7 + ((31 : ℚ) / 1440) * x ^ 6 + ((3 : ℚ) / 20) * x ^ 5 + ((1607 : ℚ) / 2880) * x ^ 4 + ((371 : ℚ) / 240) * x ^ 3 + ((14719 : ℚ) / 5040) * x ^ 2 + ((1177 : ℚ) / 420) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2520) * x ^ 7 + ((1 : ℚ) / 90) * x ^ 6 + ((43 : ℚ) / 360) * x ^ 5 + ((47 : ℚ) / 72) * x ^ 4 + ((89 : ℚ) / 45) * x ^ 3 + ((1201 : ℚ) / 360) * x ^ 2 + ((1219 : ℚ) / 420) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 4) * x ^ 3 + ((23 : ℚ) / 24) * x ^ 2 + ((7 : ℚ) / 4) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((1 : ℚ) / 2) * x ^ 2 + ((4 : ℚ) / 3) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((3 : ℚ) / 2) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def T110 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((11 : ℚ) / 1814400) * x ^ 10 + ((1 : ℚ) / 7560) * x ^ 9 + ((37 : ℚ) / 24192) * x ^ 8 + ((473 : ℚ) / 43200) * x ^ 7 + ((4553 : ℚ) / 86400) * x ^ 6 + ((17581 : ℚ) / 90720) * x ^ 5 + ((42013 : ℚ) / 72576) * x ^ 4 + ((23069 : ℚ) / 16800) * x ^ 3 + ((119291 : ℚ) / 50400) * x ^ 2 + ((3197 : ℚ) / 1320) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((1 : ℚ) / 18144) * x ^ 9 + ((113 : ℚ) / 120960) * x ^ 8 + ((247 : ℚ) / 30240) * x ^ 7 + ((59 : ℚ) / 1350) * x ^ 6 + ((677 : ℚ) / 4320) * x ^ 5 + ((170591 : ℚ) / 362880) * x ^ 4 + ((101929 : ℚ) / 90720) * x ^ 3 + ((100057 : ℚ) / 50400) * x ^ 2 + ((5573 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => ((1 : ℚ) / 90720) * x ^ 9 + ((1 : ℚ) / 2016) * x ^ 8 + ((59 : ℚ) / 7560) * x ^ 7 + ((1 : ℚ) / 16) * x ^ 6 + ((257 : ℚ) / 864) * x ^ 5 + ((89 : ℚ) / 96) * x ^ 4 + ((91381 : ℚ) / 45360) * x ^ 3 + ((1517 : ℚ) / 504) * x ^ 2 + ((3377 : ℚ) / 1260) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 560) * x ^ 7 + ((11 : ℚ) / 480) * x ^ 6 + ((7 : ℚ) / 48) * x ^ 5 + ((529 : ℚ) / 960) * x ^ 4 + ((7 : ℚ) / 5) * x ^ 3 + ((12227 : ℚ) / 5040) * x ^ 2 + ((103 : ℚ) / 42) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => ((1 : ℚ) / 360) * x ^ 6 + ((1 : ℚ) / 20) * x ^ 5 + ((5 : ℚ) / 18) * x ^ 4 + (1 : ℚ) * x ^ 3 + ((799 : ℚ) / 360) * x ^ 2 + ((49 : ℚ) / 20) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 4) * x ^ 3 + ((23 : ℚ) / 24) * x ^ 2 + ((7 : ℚ) / 4) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => (1 : ℚ) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def T111 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℚ → ℚ :=
  ![![![![(fun x : ℚ => ((1 : ℚ) / 9979200) * x ^ 11 + ((1 : ℚ) / 201600) * x ^ 10 + ((1 : ℚ) / 12096) * x ^ 9 + ((1 : ℚ) / 1344) * x ^ 8 + ((1271 : ℚ) / 302400) * x ^ 7 + ((479 : ℚ) / 28800) * x ^ 6 + ((12797 : ℚ) / 181440) * x ^ 5 + ((97 : ℚ) / 504) * x ^ 4 + ((1779 : ℚ) / 2800) * x ^ 3 + ((2032 : ℚ) / 1575) * x ^ 2 + ((8269 : ℚ) / 4620) * x ^ 1 + (1 : ℚ) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 907200) * x ^ 10 + ((1 : ℚ) / 18144) * x ^ 9 + ((113 : ℚ) / 120960) * x ^ 8 + ((247 : ℚ) / 30240) * x ^ 7 + ((59 : ℚ) / 1350) * x ^ 6 + ((677 : ℚ) / 4320) * x ^ 5 + ((170591 : ℚ) / 362880) * x ^ 4 + ((101929 : ℚ) / 90720) * x ^ 3 + ((100057 : ℚ) / 50400) * x ^ 2 + ((5573 : ℚ) / 2520) * x ^ 1 + (1 : ℚ) * x ^ 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 20160) * x ^ 8 + ((1 : ℚ) / 720) * x ^ 7 + ((7 : ℚ) / 480) * x ^ 6 + ((61 : ℚ) / 720) * x ^ 5 + ((289 : ℚ) / 960) * x ^ 4 + ((287 : ℚ) / 360) * x ^ 3 + ((8489 : ℚ) / 5040) * x ^ 2 + ((127 : ℚ) / 60) * x ^ 1 + (1 : ℚ) * x ^ 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((1 : ℚ) / 12) * x ^ 3 + ((11 : ℚ) / 24) * x ^ 2 + ((17 : ℚ) / 12) * x ^ 1 + (1 : ℚ) * x ^ 0)]]], ![![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => 0)]], ![![(fun x : ℚ => 0), (fun x : ℚ => 0)], ![(fun x : ℚ => 0), (fun x : ℚ => (1 : ℚ) * x ^ 0)]]]]

def PCv (b0 b1 b2 : Bool) (i0 i1 i2 i3 : Fin 2) (t : ℚ) : ℚ :=
  (if b0 then (if b1 then (if b2 then T111 else T110) else (if b2 then T101 else T100)) else (if b1 then (if b2 then T011 else T010) else (if b2 then T001 else T000))) i0 i1 i2 i3 t

set_option maxHeartbeats 40000000 in
lemma st_000 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f false false false (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv false false false i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
lemma st_001 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f false false true (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv false false true i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
lemma st_010 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f false true false (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv false true false i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
lemma st_011 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f false true true (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv false true true i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
lemma st_100 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f true false false (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv true false false i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
lemma st_101 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f true false true (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv true false true i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
lemma st_110 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f true true false (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv true true false i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
lemma st_111 (n : ℕ) (ih : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n) : ∀ (i0 i1 i2 i3 : Fin 2),
    (f true true true (n + 1) ![i0, i1, i2, i3] : ℚ) = PCv true true true i0 i1 i2 i3 ((n + 1 : ℕ) : ℚ) := by
    intro i0 i1 i2 i3; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_two]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide only [okT, rowOK, adjE, if_true, if_false, Bool.false_and, Bool.true_and,
        Bool.and_true, Bool.and_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [PCv, T000, T001, T010, T011, T100, T101, T110, T111] <;> ring

set_option maxHeartbeats 40000000 in
theorem f_closed (n : ℕ) : ∀ b0 b1 b2 (i0 i1 i2 i3 : Fin 2), (f b0 b1 b2 n ![i0, i1, i2, i3] : ℚ) = PCv b0 b1 b2 i0 i1 i2 i3 n := by
  induction n with
  | zero =>
    intro b0 b1 b2 i0 i1 i2 i3; rw [f_zero]
    cases b0 <;> cases b1 <;> cases b2 <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;>
      simp +decide [PCv, T000, T001, T010, T011, T100, T101, T110, T111, okT, rowOK]
  | succ n ih =>
    intro b0 b1 b2; cases b0 <;> cases b1 <;> cases b2 <;> first | exact st_000 n ih | exact st_001 n ih | exact st_010 n ih | exact st_011 n ih | exact st_100 n ih | exact st_101 n ih | exact st_110 n ih | exact st_111 n ih

set_option maxHeartbeats 4000000 in
theorem a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 9979200) * (n : ℚ) ^ 11 + ((1 : ℚ) / 201600) * (n : ℚ) ^ 10 + ((1 : ℚ) / 12096) * (n : ℚ) ^ 9 + ((1 : ℚ) / 1344) * (n : ℚ) ^ 8 + ((1271 : ℚ) / 302400) * (n : ℚ) ^ 7 + ((479 : ℚ) / 28800) * (n : ℚ) ^ 6 + ((12797 : ℚ) / 181440) * (n : ℚ) ^ 5 + ((97 : ℚ) / 504) * (n : ℚ) ^ 4 + ((1779 : ℚ) / 2800) * (n : ℚ) ^ 3 + ((2032 : ℚ) / 1575) * (n : ℚ) ^ 2 + ((8269 : ℚ) / 4620) * (n : ℚ) ^ 1 + (1 : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]; push_cast
  rw [sumk]
  simp only [Fin.sum_univ_two, f_closed]
  simp [PCv, T111]
  ring

lemma av (k : ℕ) : (a (k + 1) : ℚ) = ((1 : ℚ) / 9979200) * ((k : ℚ) + 1) ^ 11 + ((1 : ℚ) / 201600) * ((k : ℚ) + 1) ^ 10 + ((1 : ℚ) / 12096) * ((k : ℚ) + 1) ^ 9 + ((1 : ℚ) / 1344) * ((k : ℚ) + 1) ^ 8 + ((1271 : ℚ) / 302400) * ((k : ℚ) + 1) ^ 7 + ((479 : ℚ) / 28800) * ((k : ℚ) + 1) ^ 6 + ((12797 : ℚ) / 181440) * ((k : ℚ) + 1) ^ 5 + ((97 : ℚ) / 504) * ((k : ℚ) + 1) ^ 4 + ((1779 : ℚ) / 2800) * ((k : ℚ) + 1) ^ 3 + ((2032 : ℚ) / 1575) * ((k : ℚ) + 1) ^ 2 + ((8269 : ℚ) / 4620) * ((k : ℚ) + 1) ^ 1 + (1 : ℚ) := by
  rw [a_closed (k + 1) (by omega)]; push_cast; ring

open PowerSeries in
theorem full :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 9979200) * n ^ 11 + (1 / 201600) * n ^ 10 + (1 / 12096) * n ^ 9 + (1 / 1344) * n ^ 8 + (1271 / 302400) * n ^ 7 + (479 / 28800) * n ^ 6 + (12797 / 181440) * n ^ 5 + (97 / 504) * n ^ 4 + (1779 / 2800) * n ^ 3 + (2032 / 1575) * n ^ 2 + (8269 / 4620) * n + 1) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 12 =
      5 - 38 * X + 162 * X ^ 2 - 396 * X ^ 3 + 679 * X ^ 4 - 833 * X ^ 5 + 737 * X ^ 6 - 471 * X ^ 7 + 213 * X ^ 8 - 65 * X ^ 9 + 12 * X ^ 10 - 1 * X ^ 11) ∧
    (∀ n > 12, (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - 1 * a (n - 12)) := by
  refine ⟨fun n hn => by rw [a_closed n hn]; ring, ?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 12 =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) + C (-12 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (66 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-220 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (495 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-792 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (924 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-792 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) + C (495 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 8) + C (-220 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 9) + C (66 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 10) + C (-12 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 11) + C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 12) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (5 - 38 * X + 162 * X ^ 2 - 396 * X ^ 3 + 679 * X ^ 4 - 833 * X ^ 5 + 737 * X ^ 6 - 471 * X ^ 7 + 213 * X ^ 8 - 65 * X ^ 9 + 12 * X ^ 10 - 1 * X ^ 11 : PowerSeries ℚ) = C (5 : ℚ) * X ^ 0 + C (-38 : ℚ) * X ^ 1 + C (162 : ℚ) * X ^ 2 + C (-396 : ℚ) * X ^ 3 + C (679 : ℚ) * X ^ 4 + C (-833 : ℚ) * X ^ 5 + C (737 : ℚ) * X ^ 6 + C (-471 : ℚ) * X ^ 7 + C (213 : ℚ) * X ^ 8 + C (-65 : ℚ) * X ^ 9 + C (12 : ℚ) * X ^ 10 + C (-1 : ℚ) * X ^ 11 by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul, pow_zero, mul_one]; ring]
    ext k
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge k 12 with h | h
    · interval_cases k <;> simp [av] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 12 := ⟨k - 12, by omega⟩
      simp only [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega, show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega, show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega, show m + 12 - 7 = m + 5 by omega, show m + 12 - 8 = m + 4 by omega, show m + 12 - 9 = m + 3 by omega, show m + 12 - 10 = m + 2 by omega, show m + 12 - 11 = m + 1 by omega, show m + 12 - 12 = m + 0 by omega, show 1 ≤ m + 12 by omega, show 2 ≤ m + 12 by omega, show 3 ≤ m + 12 by omega, show 4 ≤ m + 12 by omega, show 5 ≤ m + 12 by omega, show 6 ≤ m + 12 by omega, show 7 ≤ m + 12 by omega, show 8 ≤ m + 12 by omega, show 9 ≤ m + 12 by omega, show 10 ≤ m + 12 by omega, show 11 ≤ m + 12 by omega, show 12 ≤ m + 12 by omega, if_true, show m + 12 ≠ 0 by omega, show m + 12 ≠ 1 by omega, show m + 12 ≠ 2 by omega, show m + 12 ≠ 3 by omega, show m + 12 ≠ 4 by omega, show m + 12 ≠ 5 by omega, show m + 12 ≠ 6 by omega, show m + 12 ≠ 7 by omega, show m + 12 ≠ 8 by omega, show m + 12 ≠ 9 by omega, show m + 12 ≠ 10 by omega, show m + 12 ≠ 11 by omega, if_false, av, coeff_C]
      first | (push_cast; ring) | (simp; push_cast; ring) | simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    simp only [show m + 13 - 1 = m + 11 + 1 by omega, show m + 13 - 2 = m + 10 + 1 by omega, show m + 13 - 3 = m + 9 + 1 by omega, show m + 13 - 4 = m + 8 + 1 by omega, show m + 13 - 5 = m + 7 + 1 by omega, show m + 13 - 6 = m + 6 + 1 by omega, show m + 13 - 7 = m + 5 + 1 by omega, show m + 13 - 8 = m + 4 + 1 by omega, show m + 13 - 9 = m + 3 + 1 by omega, show m + 13 - 10 = m + 2 + 1 by omega, show m + 13 - 11 = m + 1 + 1 by omega, show m + 13 - 12 = m + 0 + 1 by omega, show m + 13 = m + 12 + 1 by omega]
    have : ((a (m + 12 + 1) : ℤ) : ℚ) = 12 * (a (m + 11 + 1) : ℚ) - 66 * (a (m + 10 + 1) : ℚ) + 220 * (a (m + 9 + 1) : ℚ) - 495 * (a (m + 8 + 1) : ℚ) + 792 * (a (m + 7 + 1) : ℚ) - 924 * (a (m + 6 + 1) : ℚ) + 792 * (a (m + 5 + 1) : ℚ) - 495 * (a (m + 4 + 1) : ℚ) + 220 * (a (m + 3 + 1) : ℚ) - 66 * (a (m + 2 + 1) : ℚ) + 12 * (a (m + 1 + 1) : ℚ) - 1 * (a (m + 0 + 1) : ℚ) := by
      push_cast; rw [av, av, av, av, av, av, av, av, av, av, av, av, av]; push_cast; ring
    exact_mod_cast this

end OMA.P_oeis_a266430

theorem OMA.solution : type_of% @OMA.S_oeis_a266430.main := OMA.P_oeis_a266430.full
