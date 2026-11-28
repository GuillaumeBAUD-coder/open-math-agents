import OMAStatements.S_mo_306162

/-!
The three-letter hand THH/HHT was suggested by usul on MathOverflow (question 306162).
Bob has two distinct words, so one is different from TTH. We follow that word alone.
The observer retains the last two tosses, the two Alice flags, and whether Bob's
word has appeared while Alice still lacks a word. The fair-coin overlap calculation
is recorded in units of 1/30. The four possible two-toss suffixes make its one-step
inequalities finite. Splitting cylinders proves the bound at every horizon.
-/

namespace PenneyThree

open MeasureTheory OMA.S_mo_306162
open scoped ENNReal

def triple (a b c : Bool) : Word 3 := ![a, b, c]
abbrev thh := triple false true true
abbrev hht := triple true true false
abbrev tth := triple false false true

def alice : Choice 3 := ⟨{thh, hht}, by decide⟩
abbrev eligible (w : Word 3) := w ≠ thh ∧ w ≠ hht ∧ w ≠ tth
noncomputable abbrev half : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹

lemma two_half : (2 : ℝ≥0∞) * half = 1 :=
  ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

lemma fair_law : ∃ μ : Measure Ω, fairCoin μ := by
  let coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
  let : IsProbabilityMeasure coin := inferInstanceAs
    (IsProbabilityMeasure (PMF.uniformOfFintype Bool).toMeasure)
  refine ⟨Measure.infinitePi (fun _ : ℕ => coin), ?_⟩
  intro s x
  change Measure.infinitePi (fun _ : ℕ => coin)
    (Set.pi (s : Set ℕ) (fun i => {x i})) = _
  rw [Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton (x i))]
  have point (b : Bool) : coin {b} = half := by
    rw [show coin = (PMF.uniformOfFintype Bool).toMeasure from rfl,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
    simp
  simp [point]

inductive Position where
  | empty
  | one (a : Bool)
  | two (a b sawTHH sawHHT won : Bool)

def success : Position → Bool
  | .two _ _ _ _ won => won
  | _ => false

def advance (w : Word 3) (s : Position) (c : Bool) : Position :=
  match s with
  | .empty => .one c
  | .one a => .two a c false false false
  | .two a b x y won =>
    let v := triple a b c
    let x' := x || decide (v = thh)
    let y' := y || decide (v = hht)
    .two b c x' y' (won || (decide (v = w) && !(x' && y')))

def run (w : Word 3) (ω : Ω) : ℕ → Position
  | 0 => .empty
  | n + 1 => advance w (run w ω n) (ω n)

def code (w : Word 3) : ℕ := 4 * (w 0).toNat + 2 * (w 1).toNat + (w 2).toNat

def capital (w : Word 3) : Position → ℕ
  | .empty => 15
  | .one a =>
    match code w with
    | 0 => 12
    | 4 | 5 => if a then 20 else 10
    | _ => 15
  | .two a b x y won =>
    if won then 30 else if x && y then 0 else
    if code w == 7 then (if y && !(a && b) then 0 else 15) else
    if x && a && b then 0 else
    match code w with
    | 0 => if a then 12 else if b then 6 else 18
    | 4 | 5 => if a then 20 else 10
    | _ => 15

lemma expand (w : Word 3) : triple (w 0) (w 1) (w 2) = w := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 1000000 in
lemma capital_step (w : Word 3) (hw : eligible w) (s : Position) :
    capital w (advance w s false) + capital w (advance w s true) ≤ 2 * capital w s := by
  have aux (a b c : Bool) (q : Position) :
      let v := triple a b c
      eligible v → capital v (advance v q false) + capital v (advance v q true) ≤ 2 * capital v q := by
    cases q with
    | empty => revert a b c; decide
    | one d => revert a b c d; decide
    | two d e x y won => revert a b c d e x y won; decide
  simpa only [expand] using (aux (w 0) (w 1) (w 2) s (by simpa only [expand] using hw))

lemma success_capital (w : Word 3) (s : Position) (h : success s = true) :
    capital w s = 30 := by
  cases s with
  | empty => contradiction
  | one _ => contradiction
  | two a b x y won => change won = true at h; simp [capital, h]

def past (p : ℕ → Prop) (n : ℕ) : Prop := ∃ i < n, p i

lemma past_succ (p : ℕ → Prop) (n : ℕ) :
    past p (n+1) ↔ past p n ∨ p n := by
  constructor
  · rintro ⟨i, hi, h⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hl | rfl
    · exact Or.inl ⟨i, hl, h⟩
    · exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, by omega, h⟩
    · exact ⟨n, by omega, h⟩

lemma window_iff (w : Word 3) (ω : Ω) (n : ℕ) :
    occurs w ω n ↔ triple (ω n) (ω (n+1)) (ω (n+2)) = w := by
  constructor
  · intro h
    funext i
    fin_cases i
    · exact h 0
    · exact h 1
    · exact h 2
  · intro h i
    have hi := congrFun h i
    fin_cases i <;> exact hi

lemma alice_by (ω : Ω) (n : ℕ) :
    choiceOccurredBy alice ω n ↔
    past (occurs thh ω) (n+1) ∧ past (occurs hht ω) (n+1) := by
  simp [alice, choiceOccurredBy, occurredBy, past]

abbrev early (w : Word 3) (ω : Ω) :=
  past (fun i => occurs w ω i ∧ ¬choiceOccurredBy alice ω i)

noncomputable def observed (w : Word 3) (ω : Ω) (n : ℕ) : Position := by
  classical
  exact .two (ω n) (ω (n+1)) (decide (past (occurs thh ω) n))
    (decide (past (occurs hht ω) n)) (decide (early w ω n))

lemma bool_or (p q : Prop) [Decidable p] [Decidable q] [Decidable (p ∨ q)] :
    decide (p ∨ q) = (decide p || decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma bool_and (p q : Prop) [Decidable p] [Decidable q] [Decidable (p ∧ q)] :
    decide (p ∧ q) = (decide p && decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma run_observed (w : Word 3) (ω : Ω) (n : ℕ) :
    run w ω (n+2) = observed w ω n := by
  classical
  induction n with
  | zero => simp [run, advance, observed, early, past]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, run, ih]
    simp only [observed, advance, early, past_succ, alice_by, window_iff,
      bool_or, bool_and, decide_not]

def event (w : Word 3) (n : ℕ) : Set Ω := {ω | success (run w ω n) = true}

lemma event_mono (w : Word 3) : Monotone (event w) := by
  apply monotone_nat_of_le_succ
  intro n ω h
  change success (advance w (run w ω n) (ω n)) = true
  change success (run w ω n) = true at h
  cases e : run w ω n with
  | empty => simp [e, success] at h
  | one _ => simp [e, success] at h
  | two a b x y won =>
    rw [e] at h
    change won = true at h
    simp [advance, success, h]

def cyl (n : ℕ) (x : Ω) : Set Ω := {ω | ∀ i < n, ω i = x i}

lemma cyl_mass {μ : Measure Ω} (hμ : fairCoin μ) (n : ℕ) (x : Ω) :
    μ (cyl n x) = half ^ n := by
  simpa [cyl] using hμ (Finset.range n) x

lemma run_agree (w : Word 3) {ω x : Ω} {n : ℕ} (h : ω ∈ cyl n x) :
    run w ω n = run w x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, run, ih (fun i hi => h i (by omega)), h n (by omega)]

lemma cylinder_bound {μ : Measure Ω} (hμ : fairCoin μ) (w : Word 3) (hw : eligible w) (m : ℕ) :
    ∀ n x, 30 * μ (cyl n x ∩ event w (n+m)) ≤ (capital w (run w x n) : ℝ≥0∞) * half^n := by
  induction m with
  | zero =>
    intro n x
    rw [Nat.add_zero]
    by_cases h : success (run w x n) = true
    · rw [success_capital w _ h]
      have hm : μ (cyl n x ∩ event w n) ≤ half^n :=
        (measure_mono Set.inter_subset_left).trans_eq (cyl_mass hμ n x)
      exact mul_le_mul_of_nonneg_left hm zero_le
    · have he : cyl n x ∩ event w n = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨hc, he⟩
        apply h
        change success (run w ω n) = true at he
        rwa [run_agree w hc] at he
      simp [he]
  | succ m ih =>
    intro n x
    let child (b : Bool) : Ω := Function.update x n b
    have same (b : Bool) : child b ∈ cyl n x := by
      intro i hi
      exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
    have nextState (b : Bool) :
        run w (child b) (n+1) = advance w (run w x n) b := by
      rw [run, run_agree w (same b)]
      simp [child]
    let children (b : Bool) := cyl (n+1) (child b) ∩ event w ((n+1)+m)
    have cover : cyl n x ∩ event w (n+(m+1)) ⊆ children false ∪ children true := by
      rintro ω ⟨hc, he⟩
      have hchild : ω ∈ children (ω n) := by
        refine ⟨?_, ?_⟩
        · intro i hi
          by_cases e : i = n
          · subst i; simp [child]
          · exact (hc i (by omega)).trans ((same (ω n)) i (by omega)).symm
        · rwa [show n+1+m = n+(m+1) by omega]
      cases e : ω n
      · exact Or.inl (e ▸ hchild)
      · exact Or.inr (e ▸ hchild)
    have splitBound := add_le_add (ih (n+1) (child false)) (ih (n+1) (child true))
    have hstep : (capital w (run w (child false) (n+1)) : ℝ≥0∞) +
        capital w (run w (child true) (n+1)) ≤ 2 * capital w (run w x n) := by
      rw [nextState, nextState]
      exact_mod_cast capital_step w hw (run w x n)
    calc
      _ ≤ 30 * (μ (children false) + μ (children true)) :=
        mul_le_mul_of_nonneg_left ((measure_mono cover).trans (measure_union_le _ _)) zero_le
      _ = 30 * μ (children false) + 30 * μ (children true) := mul_add _ _ _
      _ ≤ _ := splitBound
      _ = _ := (add_mul _ _ _).symm
      _ ≤ (2 * (capital w (run w x n) : ℝ≥0∞)) * half^(n+1) :=
        mul_le_mul_of_nonneg_right hstep zero_le
      _ = _ := by
        rw [pow_succ]
        calc
          _ = (2 * half) * ((capital w (run w x n) : ℝ≥0∞) * half^n) := by ring
          _ = _ := by rw [two_half, one_mul]

lemma finite_bound {μ : Measure Ω} (hμ : fairCoin μ) (w : Word 3) (hw : eligible w) (n : ℕ) :
    μ (event w n) ≤ half := by
  let x : Ω := fun _ => false
  have hc : cyl 0 x = Set.univ := by ext; simp [cyl]
  have h : 30 * μ (event w n) ≤ 15 := by
    simpa [hc, run, capital] using cylinder_bound hμ w hw n 0 x
  have scale : (30 : ℝ≥0∞) * half = 15 := by
    rw [show (30 : ℝ≥0∞) = 15 * 2 by norm_num, mul_assoc, two_half, mul_one]
  have cancel (a : ℝ≥0∞) : (30 : ℝ≥0∞)⁻¹ * (30 * a) = a :=
    ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)
  calc
    μ (event w n) = (30 : ℝ≥0∞)⁻¹ * (30 * μ (event w n)) := (cancel _).symm
    _ ≤ (30 : ℝ≥0∞)⁻¹ * 15 := mul_le_mul_of_nonneg_left h zero_le
    _ = half := by rw [← scale, cancel]

lemma response_word (B : Choice 3) (hd : disjointChoices alice B) :
    ∃ w ∈ B.1, eligible w := by
  have outside (w) (hw : w ∈ B.1) : w ≠ thh ∧ w ≠ hht := by
    have ha : w ∉ alice.1 := fun h =>
      (Finset.notMem_empty w) (hd ▸ Finset.mem_inter.mpr ⟨h, hw⟩)
    simpa [alice] using ha
  obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp B.2
  have hu : u ∈ B.1 := by simp [hp]
  have hv : v ∈ B.1 := by simp [hp]
  by_cases e : u = tth
  · exact ⟨v, hv, (outside v hv).1, (outside v hv).2, fun h => huv (e.trans h.symm)⟩
  · exact ⟨u, hu, (outside u hu).1, (outside u hu).2, e⟩

lemma response_bound {μ : Measure Ω} (hμ : fairCoin μ) (B : Choice 3)
    (hd : disjointChoices alice B) : BWinProbability μ alice B ≤ half := by
  obtain ⟨w, hw, hgood⟩ := response_word B hd
  have sub : {ω | BWins alice B ω} ⊆ ⋃ n, event w n := by
    rintro ω ⟨b, a, hb, ha, hba⟩
    obtain ⟨t, ht, occursAt⟩ := hb.1 w hw
    have he : early w ω (t+1) := ⟨t, by omega, occursAt, ha.2 t (by omega)⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(t+1)+2, ?_⟩
    change success (run w ω ((t+1)+2)) = true
    rw [run_observed]
    simpa [observed, success] using he
  change μ {ω | BWins alice B ω} ≤ _
  calc
    _ ≤ μ (⋃ n, event w n) := measure_mono sub
    _ = ⨆ n, μ (event w n) := (event_mono w).measure_iUnion
    _ ≤ _ := iSup_le (finite_bound hμ w hgood)

end PenneyThree

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_306162.main) := by
  intro claim
  obtain ⟨μ, fair⟩ := PenneyThree.fair_law
  obtain ⟨B, disjoint, better⟩ := claim 3 (by decide) μ fair PenneyThree.alice
  exact (not_lt_of_ge (PenneyThree.response_bound fair B disjoint)) better
