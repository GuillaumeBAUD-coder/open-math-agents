import OMAStatements.S_oeis_a002464

/-!
For each selected set of successions, cut the line of values at the
unselected edges. The resulting blocks can be ordered freely, and
each block of length at least two can be reversed independently.
Inclusion-exclusion and the signed run recurrence then give the formula.
-/

namespace Hertzsprung
open Finset OMA.S_oeis_a002464

def falseCount {n : ℕ} (w : Fin n → Bool) : ℕ :=
  (univ.filter fun i => w i = false).card

def runAt {n : ℕ} (w : Fin n → Bool) (i : Fin n) : Prop :=
  w i = true ∧ ∀ j : Fin n, j.val + 1 = i.val → w j = false

instance {n : ℕ} (w : Fin n → Bool) (i : Fin n) : Decidable (runAt w i) := by
  unfold runAt
  infer_instance

def runCount {n : ℕ} (w : Fin n → Bool) : ℕ := (univ.filter (runAt w)).card

private theorem falseCount_le {n : ℕ} (w : Fin n → Bool) : falseCount w ≤ n := by
  exact (card_filter_le _ _).trans (by simp)

private theorem card_filter_count {α : Type*} (P : α → Prop) [DecidablePred P] (s : Finset α) :
    (s.filter P).card = ∑ i ∈ s, if P i then 1 else 0 :=
  natCast_card_filter (R := ℕ) P s

private theorem falseCount_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    falseCount (Fin.cons b w) = (if b = false then 1 else 0) + falseCount w := by
  simp only [falseCount, card_filter_count, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

private theorem runAt_zero {n : ℕ} (w : Fin (n+1) → Bool) :
    runAt w 0 ↔ w 0 = true := by
  simp [runAt]

private theorem runAt_succ_zero {n : ℕ} (b : Bool) (w : Fin (n+1) → Bool) :
    runAt (Fin.cons b w) ((0 : Fin (n+1)).succ) ↔ w 0 = true ∧ b = false := by
  unfold runAt
  rw [Fin.cons_succ]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₁, h₂ 0 (by simp)⟩
  · rintro ⟨h₁,h₂⟩
    refine ⟨h₁,fun j hj => ?_⟩
    have he : j = 0 := Fin.ext (by simpa using Nat.add_right_cancel hj)
    simpa [he, Fin.cons_zero] using h₂

private theorem runAt_cons_two {n : ℕ} (b : Bool) (w : Fin (n+1) → Bool) (i : Fin n) :
    runAt (Fin.cons b w) i.succ.succ ↔ runAt w i.succ := by
  unfold runAt
  rw [Fin.cons_succ]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₁,fun j hj => by simpa using h₂ j.succ (by simp at hj ⊢; omega)⟩
  · rintro ⟨h₁,h₂⟩
    refine ⟨h₁,?_⟩
    intro j
    refine Fin.cases ?_ (fun k hk => ?_) j
    · simp
    · simpa using h₂ k (by simp at hk ⊢; omega)

private theorem runCount_cons {n : ℕ} (b : Bool) (w : Fin (n+1) → Bool) :
    runCount (Fin.cons b w) =
      (if b = true then 1 else 0) + (if w 0 = true ∧ b = false then 1 else 0) +
        ∑ i : Fin n, if runAt w i.succ then 1 else 0 := by
  simp only [runCount, card_filter_count]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [runAt_zero, Fin.cons_zero, runAt_succ_zero, runAt_cons_two, Nat.add_assoc]

private theorem runCount_split {n : ℕ} (w : Fin (n+1) → Bool) :
    runCount w = (if w 0 = true then 1 else 0) +
      ∑ i : Fin n, if runAt w i.succ then 1 else 0 := by
  simp only [runCount, card_filter_count, Fin.sum_univ_succ, runAt_zero]

private theorem runCount_cons_false {n : ℕ} (w : Fin n → Bool) :
    runCount (Fin.cons false w) = runCount w := by
  cases n
  · simp only [runCount, card_filter_count, Fin.sum_univ_succ, runAt_zero,
      Fin.cons_zero, Bool.false_eq_true, if_false, Fintype.sum_empty, add_zero]
  · rw [runCount_cons, runCount_split w]
    simp

private theorem runCount_cons_true {n : ℕ} (w : Fin (n+1) → Bool) :
    runCount (Fin.cons true w) = runCount w + if w 0 = false then 1 else 0 := by
  rw [runCount_cons, runCount_split w]
  cases w 0 <;> simp [Nat.add_comm]

private def weight {n : ℕ} (w : Fin n → Bool) : ℤ :=
  (-1)^(n - falseCount w) * 2^runCount w

private theorem weight_false {n : ℕ} (w : Fin n → Bool) :
    weight (Fin.cons false w) = weight w := by
  simp only [weight, falseCount_cons, runCount_cons_false, if_true]
  rw [show n+1 - (1+falseCount w) = n - falseCount w by omega]

private theorem weight_true {n : ℕ} (w : Fin (n+1) → Bool) :
    weight (Fin.cons true w) = -(if w 0 = false then 2 else 1) * weight w := by
  have h := falseCount_le w
  simp only [weight, falseCount_cons, runCount_cons_true, Bool.true_eq_false,
    if_false, zero_add]
  rw [show n+1+1 - falseCount w = n+1 - falseCount w + 1 by omega, pow_succ, pow_add]
  cases w 0 with
  | false => simp; ring
  | true => simp

private def slice {n : ℕ} (k : ℕ) (w : Fin n → Bool) : ℤ :=
  if falseCount w = k then weight w else 0

private def signedSum (n k : ℕ) : ℤ := ∑ w : Fin n → Bool, slice k w

private def prefFalse (n k : ℕ) : ℤ := ∑ w : Fin n → Bool, slice k (Fin.cons false w)

private theorem sum_cons {n : ℕ} (F : (Fin (n+1) → Bool) → ℤ) :
    ∑ w, F w = (∑ w : Fin n → Bool, F (Fin.cons false w)) +
      ∑ w : Fin n → Bool, F (Fin.cons true w) := by
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Bool)
  calc
    ∑ w, F w = ∑ q : Bool × (Fin n → Bool), F (e q) :=
      (Fintype.sum_equiv e (fun q => F (e q)) F (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      exact add_comm _ _

private theorem prefFalse_zero (n : ℕ) : prefFalse n 0 = 0 := by
  simp [prefFalse, slice, falseCount_cons]

private theorem prefFalse_succ (n k : ℕ) : prefFalse n (k+1) = signedSum n k := by
  simp [prefFalse, signedSum, slice, falseCount_cons, weight_false, Nat.add_comm 1]

private theorem signedSum_true_prefix (n k : ℕ) :
    (∑ w : Fin (n+1) → Bool, slice k (Fin.cons true w)) =
      -signedSum (n+1) k - prefFalse n k := by
  have h (w : Fin (n+1) → Bool) :
      slice k (Fin.cons true w) =
        -(slice k w) - if w 0 = false then slice k w else 0 := by
    simp only [slice, falseCount_cons, Bool.true_eq_false, if_false, zero_add, weight_true]
    split_ifs <;> ring
  have hc :
      (∑ w : Fin (n+1) → Bool, if w 0 = false then slice k w else 0) = prefFalse n k := by
    rw [sum_cons]
    simp [prefFalse, Fin.cons_zero]
  simp only [h, sum_sub_distrib, sum_neg_distrib, hc, signedSum]

private theorem signedSum_zero (n : ℕ) : signedSum (n+2) 0 = -signedSum (n+1) 0 := by
  conv_lhs => unfold signedSum
  rw [sum_cons]
  change prefFalse (n+1) 0 + _ = _
  rw [signedSum_true_prefix, prefFalse_zero, prefFalse_zero]
  ring

private theorem signedSum_succ (n k : ℕ) :
    signedSum (n+2) (k+1) = signedSum (n+1) k - signedSum (n+1) (k+1) - signedSum n k := by
  conv_lhs => unfold signedSum
  rw [sum_cons]
  change prefFalse (n+1) (k+1) + _ = _
  rw [signedSum_true_prefix, prefFalse_succ, prefFalse_succ]
  ring

private theorem signedSum_large {n k : ℕ} (h : n < k) : signedSum n k = 0 := by
  unfold signedSum slice
  apply sum_eq_zero
  intro w _
  rw [if_neg]
  exact (falseCount_le w).trans_lt h |>.ne

private theorem signedSum_eq_T (n k : ℕ) : signedSum n k = T n k := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero =>
    cases k with
    | zero => decide +kernel
    | succ k => rw [signedSum_large (Nat.zero_lt_succ _), T]
  | one =>
    obtain _ | _ | k := k
    · decide +kernel
    · decide +kernel
    · rw [signedSum_large (by omega),T]
  | more n hn hn' =>
    cases k with
    | zero => rw [signedSum_zero,hn',T]
    | succ k => rw [signedSum_succ,hn,hn',hn',T]

theorem signed_masks (n k : ℕ) :
    (∑ w : Fin n → Bool, if falseCount w = k then (-1:ℤ)^(n-k)*2^runCount w else 0) = T n k := by
  rw [← signedSum_eq_T]
  unfold signedSum slice weight
  apply sum_congr rfl
  intro w _
  by_cases h : falseCount w = k <;> simp [h]

end Hertzsprung

namespace Hertzsprung

private def Next (a b : ℕ) : Prop := b = a + 1 ∨ a = b + 1

private theorem path_formula {s : ℕ} (hs : 0 < s) (f : Fin s → ℕ)
    (hf : Function.Injective f) (hn : ∀ i j : Fin s, (j:ℕ) = i+1 → Next (f i) (f j)) :
    ∃ base : ℕ, ∃ rev : Bool, (rev = true → 1 < s) ∧
      ∀ j : Fin s, f j = base + (if rev then s - 1 - j else j) := by
  let j0 : Fin s := ⟨0,hs⟩
  by_cases hs' : 1 < s
  · let j1 : Fin s := ⟨1,hs'⟩
    have hwalk (d : ℤ) (hd : d = 1 ∨ d = -1) (h₁ : (f j1 : ℤ) = f j0 + d) :
        ∀ j : Fin s, (f j : ℤ) = (f j0 : ℤ) + j.val * d := by
      have aux (k : ℕ) : ∀ hk : k < s,
          (f ⟨k,hk⟩ : ℤ) = (f j0 : ℤ) + (k:ℤ)*d := by
        induction k using Nat.strong_induction_on with
        | h k ih =>
          intro hk
          rcases k with _|k
          · simp [j0]
          rcases k with _|k
          · simpa [j1] using h₁
          let x : Fin s := ⟨k,by omega⟩
          let y : Fin s := ⟨k+1,by omega⟩
          let z : Fin s := ⟨k+2,hk⟩
          have hx := ih k (by omega) x.2
          have hy := ih (k+1) (by omega) y.2
          have hne : f x ≠ f z := fun h => by
            have he := congrArg Fin.val (hf h)
            change k = k+2 at he
            omega
          have hneZ : (f x : ℤ) ≠ f z := by exact_mod_cast hne
          have hstep := hn y z rfl
          change (f x : ℤ) = _ at hx
          change (f y : ℤ) = _ at hy
          change (f z : ℤ) = _
          rcases hd with rfl | rfl <;>
            rcases hstep with hp | hp <;>
            (push_cast at hy ⊢; omega)
      exact fun j => aux j j.2
    rcases hn j0 j1 rfl with hh | hh
    · have hf' := hwalk 1 (Or.inl rfl) (by exact_mod_cast hh)
      exact ⟨f j0,false,by simp,fun j => by have h := hf' j; norm_num at h ⊢; exact_mod_cast h⟩
    · have hf' := hwalk (-1) (Or.inr rfl) (by omega)
      let jlast : Fin s := ⟨s-1,by omega⟩
      refine ⟨f jlast,true,fun _ => hs',?_⟩
      intro j
      have hlast := hf' jlast
      have hj := hf' j
      change (f jlast : ℤ) = (f j0 : ℤ) + ((s-1:ℕ):ℤ)*(-1) at hlast
      have hb := j.2
      simp only [if_true]
      omega
  · refine ⟨f j0,false,by simp,?_⟩
    intro j
    have h : j = j0 := Fin.ext (by have := j.2; change j.val = 0; omega)
    simp [h,j0]

private abbrev Turns {k : ℕ} (s : Fin k → ℕ) := {a : Fin k // 1 < s a} → Bool

private def flip {k : ℕ} {s : Fin k → ℕ} (r : Turns s) (a : Fin k) : Bool :=
  if h : 1 < s a then r ⟨a,h⟩ else false

private def orient {k : ℕ} {s : Fin k → ℕ} (r : Turns s) (a : Fin k) :
    Equiv.Perm (Fin (s a)) :=
  if flip r a then Fin.revPerm else Equiv.refl _

private theorem orient_val {k : ℕ} {s : Fin k → ℕ} (r : Turns s) (a : Fin k)
    (j : Fin (s a)) :
    ((orient r a) j : ℕ) = if flip r a then s a - 1 - j else j := by
  unfold orient
  cases flip r a <;> simp [Fin.val_rev, Nat.sub_sub, Nat.add_comm]

private def orientation {k : ℕ} {s : Fin k → ℕ} (r : Turns s) :
    Equiv.Perm ((a : Fin k) × Fin (s a)) := Equiv.sigmaCongrRight (orient r)

private def layout {k N : ℕ} {s : Fin k → ℕ} (hs : ∑ a, s a = N)
    (o : Equiv.Perm (Fin k)) : (Σ i : Fin k, Fin (s (o i))) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr ((Equiv.sum_comp o s).trans hs))

private def ordered {k N : ℕ} {s : Fin k → ℕ} (hs : ∑ a, s a = N)
    (o : Equiv.Perm (Fin k)) :
    ((a : Fin k) × Fin (s a)) ≃ Fin N :=
  (Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o).symm.trans (layout hs o)

private def arrange {k N : ℕ} {s : Fin k → ℕ} (hs : ∑ a, s a = N)
    (o : Equiv.Perm (Fin k)) (r : Turns s) :
    ((a : Fin k) × Fin (s a)) ≃ Fin N :=
  (orientation r).trans (ordered hs o)

private def offset {k : ℕ} (s : Fin k → ℕ) (o : Equiv.Perm (Fin k)) (i : Fin k) : ℕ :=
  ∑ j : Fin i.val, s (o (Fin.castLE i.isLt.le j))

private theorem layout_val {k N : ℕ} {s : Fin k → ℕ} (hs : ∑ a, s a = N)
    (o : Equiv.Perm (Fin k)) (i : Fin k) (j : Fin (s (o i))) :
    ((layout hs o) ⟨i,j⟩ : ℕ) = offset s o i + j := by
  exact finSigmaFinEquiv_apply _

private theorem arrange_val {k N : ℕ} {s : Fin k → ℕ} (hs : ∑ a, s a = N)
    (o : Equiv.Perm (Fin k)) (r : Turns s) (i : Fin k) (j : Fin (s (o i))) :
    ((arrange hs o r) ⟨o i,j⟩ : ℕ) = offset s o i + (if flip r (o i) then s (o i)-1-j else j) := by
  have he : ((Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o).symm
      ⟨o i,(orient r (o i)) j⟩) = ⟨i,(orient r (o i)) j⟩ :=
    (Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o).symm_apply_apply ⟨i,(orient r (o i)) j⟩
  change ((layout hs o) ((Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o).symm
      ⟨o i,(orient r (o i)) j⟩) : ℕ) = _
  rw [he, layout_val, orient_val]

private def Respects {k N : ℕ} {s : Fin k → ℕ} (f : ((a : Fin k) × Fin (s a)) ≃ Fin N) :
    Prop := ∀ (a : Fin k) (i j : Fin (s a)), (j:ℕ) = i+1 → Next (f ⟨a,i⟩).val (f ⟨a,j⟩).val

private noncomputable instance {k N : ℕ} {s : Fin k → ℕ} :
    DecidablePred (@Respects k N s) := Classical.decPred _

private theorem arrange_respects {k N : ℕ} {s : Fin k → ℕ} (hs : ∑ a, s a = N)
    (o : Equiv.Perm (Fin k)) (r : Turns s) : Respects (arrange hs o r) := by
  intro a
  obtain ⟨v,rfl⟩ := o.surjective a
  intro i j hj
  rw [arrange_val, arrange_val]
  cases flip r (o v)
  · simp only [Bool.false_eq_true, if_false, Next]
    omega
  · simp only [if_true, Next]
    have hi := i.2
    have hj' := j.2
    omega

end Hertzsprung
namespace Hertzsprung

private theorem offset_succ_le {k : ℕ} (s : Fin k → ℕ) (o : Equiv.Perm (Fin k))
    {i j : Fin k} (h : i < j) :
    offset s o i + s (o i) ≤ offset s o j := by
  classical
  let f : ℕ → ℕ := fun u => if hu : u < k then s (o ⟨u,hu⟩) else 0
  have eq (a : Fin k) : offset s o a = ∑ u ∈ Finset.range a.val, f u := by
    unfold offset
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro u _
    simp [f, u.2.trans a.2]
    rfl
  rw [eq i, eq j, ← show f i.val = s (o i) by simp [f, i.2], ← Finset.sum_range_succ]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

private def first {s : ℕ} (hs : 0 < s) : Fin s := ⟨0,hs⟩

private def last {s : ℕ} (hs : 0 < s) : Fin s := ⟨s-1,by omega⟩

private def startPos {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    (f : ((a : Fin k) × Fin (s a)) ≃ Fin N) (a : Fin k) : ℕ :=
  min (f ⟨a,first (hp a)⟩).val (f ⟨a,last (hp a)⟩).val

private def direction {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    (f : ((a : Fin k) × Fin (s a)) ≃ Fin N) : Turns s :=
  fun a => decide ((f ⟨a.val,last (hp a.val)⟩).val < (f ⟨a.val,first (hp a.val)⟩).val)

private theorem recover_path {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    {f : ((a : Fin k) × Fin (s a)) ≃ Fin N} (hf : Respects f) (a : Fin k)
    (j : Fin (s a)) :
    (f ⟨a,j⟩).val = startPos hp f a +
      (if flip (direction hp f) a then s a - 1 - j else j) := by
  have hi : Function.Injective (fun j : Fin (s a) => (f ⟨a,j⟩).val) := by
    intro x y hx
    have he := f.injective (Fin.ext hx)
    exact Fin.ext (by simpa using congrArg (fun z : (Σ a : Fin k, Fin (s a)) => z.2.val) he)
  obtain ⟨l,b,hb,he⟩ := path_formula (hp a) _ hi (hf a)
  have hfirst := he (first (hp a))
  have hlast := he (last (hp a))
  cases b with
  | false =>
    simp only [if_false, Bool.false_eq_true] at hfirst hlast he
    change (f ⟨a,first (hp a)⟩).val = l + 0 at hfirst
    change (f ⟨a,last (hp a)⟩).val = l + (s a - 1) at hlast
    have hflip : flip (direction hp f) a = false := by
      by_cases ha : 1 < s a
      · simp [flip,ha,direction,hfirst,hlast]
      · simp [flip,ha]
    simp [hflip,startPos,hfirst,hlast,he]
  | true =>
    have ha : 1 < s a := hb rfl
    simp only [if_true] at hfirst hlast he
    change (f ⟨a,first (hp a)⟩).val = l + (s a - 1 - 0) at hfirst
    change (f ⟨a,last (hp a)⟩).val = l + (s a - 1 - (s a - 1)) at hlast
    have hd : l < l + (s a-1) := by omega
    simp [flip,ha,direction,startPos,hfirst,hlast,hd,he, hd.le]

private theorem oriented_path {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    {f : ((a : Fin k) × Fin (s a)) ≃ Fin N} (hf : Respects f) (a : Fin k)
    (j : Fin (s a)) :
    (f (orientation (direction hp f) ⟨a,j⟩)).val = startPos hp f a + j := by
  change (f ⟨a,(orient (direction hp f) a) j⟩).val = _
  rw [recover_path hp hf, orient_val]
  cases flip (direction hp f) a <;> simp only [Bool.false_eq_true, if_false, if_true]
  have hj := j.2
  omega

private theorem startPos_injective {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    {f : ((a : Fin k) × Fin (s a)) ≃ Fin N} (hf : Respects f) :
    Function.Injective (startPos hp f) := by
  intro a b hab
  have ha := oriented_path hp hf a (first (hp a))
  have hb := oriented_path hp hf b (first (hp b))
  have h : f (orientation (direction hp f) ⟨a,first (hp a)⟩) =
      f (orientation (direction hp f) ⟨b,first (hp b)⟩) :=
    Fin.ext (by simpa [first,hab] using ha.trans (by simpa [first,hab] using hb.symm))
  exact congrArg Sigma.fst ((orientation (direction hp f)).injective (f.injective h))

private theorem disjoint_pos {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    {f : ((a : Fin k) × Fin (s a)) ≃ Fin N} (hf : Respects f)
    {a b : Fin k} (h : startPos hp f a < startPos hp f b) :
    startPos hp f a + s a ≤ startPos hp f b := by
  by_contra! hh
  let i : Fin (s a) := ⟨startPos hp f b - startPos hp f a,by omega⟩
  have ha := oriented_path hp hf a i
  have hb := oriented_path hp hf b (first (hp b))
  have he : f (orientation (direction hp f) ⟨a,i⟩) =
      f (orientation (direction hp f) ⟨b,first (hp b)⟩) := Fin.ext (by
    change _ = startPos hp f a + (startPos hp f b - startPos hp f a) at ha
    change _ = startPos hp f b + 0 at hb
    omega)
  have hne : a ≠ b := by intro he; subst b; exact (lt_irrefl _) h
  exact hne (congrArg Sigma.fst ((orientation (direction hp f)).injective (f.injective he)))

private theorem start_arrange {k N : ℕ} {s : Fin k → ℕ}
    (hp : ∀ a, 0 < s a) (hs : ∑ a, s a = N)
    (o : Equiv.Perm (Fin k)) (r : Turns s) (i : Fin k) :
    startPos hp (arrange hs o r) (o i) = offset s o i := by
  unfold startPos
  rw [arrange_val, arrange_val]
  cases flip r (o i) <;> simp [first,last]

private theorem direction_arrange {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    (hs : ∑ a, s a = N) (o : Equiv.Perm (Fin k)) (r : Turns s) :
    direction hp (arrange hs o r) = r := by
  funext a
  obtain ⟨i,hi⟩ := o.surjective a.val
  obtain ⟨a,ha⟩ := a
  change o i = a at hi
  subst a
  unfold direction
  simp only [arrange_val, flip, ha, dif_pos]
  cases r ⟨o i,ha⟩
  · simp [first,last]
  · have hp' : 0 < s (o i)-1 := by omega
    simp [first,last,hp']

private theorem arrange_injective {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    (hs : ∑ a, s a = N) :
    Function.Injective (fun data : Equiv.Perm (Fin k) × Turns s => arrange hs data.1 data.2) := by
  rintro ⟨o,r⟩ ⟨p,t⟩ he
  change arrange hs o r = arrange hs p t at he
  have hrt := congrArg (direction hp) he
  rw [direction_arrange hp, direction_arrange hp] at hrt
  subst t
  let f := arrange hs o r
  have hmonoO : StrictMono (startPos hp f ∘ o) := by
    intro i j hij
    change startPos hp f (o i) < startPos hp f (o j)
    rw [start_arrange, start_arrange]
    have hle := offset_succ_le s o hij
    have hpos := hp (o i)
    omega
  have hmonoP : StrictMono (startPos hp f ∘ p) := by
    intro i j hij
    change startPos hp f (p i) < startPos hp f (p j)
    rw [show f=arrange hs p r from he, start_arrange, start_arrange]
    have hle := offset_succ_le s p hij
    have hpos := hp (p i)
    omega
  have hc := Tuple.unique_monotone (σ := o) (τ := p) hmonoO.monotone hmonoP.monotone
  have hi := startPos_injective hp (arrange_respects hs o r)
  congr 1
  apply Equiv.ext
  intro a
  exact hi (congrFun hc a)

private theorem arrange_surjective {k N : ℕ} {s : Fin k → ℕ} (hp : ∀ a, 0 < s a)
    (hs : ∑ a, s a = N) {f : ((a : Fin k) × Fin (s a)) ≃ Fin N} (hf : Respects f) :
    ∃ o : Equiv.Perm (Fin k), ∃ r : Turns s, arrange hs o r = f := by
  let o := Tuple.sort (startPos hp f)
  let r := direction hp f
  let g := (layout hs o).symm.trans
    (((Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o).trans (orientation r)).trans f)
  have hstrict : StrictMono (startPos hp f ∘ o) :=
    (Tuple.monotone_sort _).strictMono_of_injective ((startPos_injective hp hf).comp o.injective)
  have hg (i : Fin k) (j : Fin (s (o i))) :
      (g (layout hs o ⟨i,j⟩)).val = startPos hp f (o i) + j := by
    exact (show g (layout hs o ⟨i,j⟩) = f (orientation r ⟨o i,j⟩) by simp [g]) ▸
      (oriented_path hp hf (o i) j)
  have hmono : StrictMono g := by
    intro x y hxy
    obtain ⟨⟨i,u⟩,rfl⟩ := (layout hs o).surjective x
    obtain ⟨⟨j,v⟩,rfl⟩ := (layout hs o).surjective y
    change (layout hs o ⟨i,u⟩).val < (layout hs o ⟨j,v⟩).val at hxy
    change (g (layout hs o ⟨i,u⟩)).val < (g (layout hs o ⟨j,v⟩)).val
    rw [layout_val,layout_val] at hxy
    rw [hg,hg]
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hle := disjoint_pos hp hf (hstrict hij)
      have hu := u.2
      omega
    · omega
    · have hle := offset_succ_le s o hji
      have hv := v.2
      omega
  have horient (a : (Σ a : Fin k, Fin (s a))) : orientation r (orientation r a) = a := by
    rcases a with ⟨a,j⟩
    change (@Sigma.mk (Fin k) (fun l => Fin (s l)) a (orient r a (orient r a j))) = _
    cases he : flip r a <;> simp [orient,he]
  refine ⟨o,r,?_⟩
  ext a
  obtain ⟨⟨i,j⟩, rfl⟩ := ((Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o).trans
      (orientation r)).surjective a
  have h : f (orientation r ⟨o i,j⟩) = layout hs o ⟨i,j⟩ := by
    simpa [g] using hmono.apply_eq (x := layout hs o ⟨i,j⟩)
  change ((ordered hs o) (orientation r (orientation r ⟨o i,j⟩))).val =
    (f (orientation r ⟨o i,j⟩)).val
  rw [horient, h]
  change (layout hs o ((Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o).symm
    ((Equiv.sigmaCongrLeft (β := fun a => Fin (s a)) o) ⟨i,j⟩))).val = _
  rw [Equiv.symm_apply_apply]

private theorem count_placements {k N : ℕ} {s : Fin k → ℕ}
    (hp : ∀ a, 0 < s a) (hs : ∑ a, s a = N) :
    Fintype.card {f : ((a : Fin k) × Fin (s a)) ≃ Fin N // Respects f} =
      k.factorial * 2 ^ Fintype.card {a : Fin k // 1 < s a} := by
  classical
  let G : Equiv.Perm (Fin k) × Turns s →
      {f : ((a : Fin k) × Fin (s a)) ≃ Fin N // Respects f} :=
    fun u => ⟨arrange hs u.1 u.2, arrange_respects hs u.1 u.2⟩
  have hi : Function.Injective G :=
    fun _ _ he => arrange_injective hp hs (congrArg Subtype.val he)
  have hu : Function.Surjective G := by
    intro f
    obtain ⟨o,r,h⟩ := arrange_surjective hp hs f.2
    exact ⟨(o,r),Subtype.ext h⟩
  rw [← Fintype.card_congr (Equiv.ofBijective G ⟨hi,hu⟩)]
  simp [Turns, Fintype.card_perm]

end Hertzsprung
namespace Hertzsprung

open Finset

private def cutEmb (n : ℕ) : Fin n ↪ Fin (n+2) :=
  ⟨fun i => i.succ.castSucc, fun _ _ h => Fin.succ_injective _ (Fin.castSucc_injective _ h)⟩

private def cuts {n : ℕ} (w : Fin n → Bool) : CompositionAsSet (n+1) where
  boundaries := insert 0 (insert (Fin.last (n+1))
    ((Finset.univ.filter fun i => w i = false).map (cutEmb n)))
  zero_mem := Finset.mem_insert_self _ _
  getLast_mem := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

private abbrev cutComposition {n : ℕ} (w : Fin n → Bool) := (cuts w).toComposition

private theorem cut_boundary {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    (cutEmb n i) ∈ (cutComposition w).boundaries ↔ w i = false := by
  rw [show (cutComposition w).boundaries = (cuts w).boundaries from
    (cuts w).toComposition_boundaries]
  change _ ∈ insert (0 : Fin (n+2)) (insert (Fin.last (n+1))
    ((Finset.univ.filter fun j => w j = false).map (cutEmb n))) ↔ _
  have hz : cutEmb n i ≠ 0 := by intro h; have he := congrArg Fin.val h; change i.val+1 = 0 at he; omega
  have hl : cutEmb n i ≠ Fin.last (n+1) := by
    intro h
    have he := congrArg Fin.val h
    change i.val+1 = n+1 at he
    have hi := i.2
    omega
  simp [hz,hl]

private theorem length_cut {n : ℕ} (w : Fin n → Bool) :
    (cutComposition w).length = (Finset.univ.filter fun i => w i = false).card + 1 := by
  let s : Finset (Fin (n+2)) := ((Finset.univ.filter fun i => w i = false).map (cutEmb n))
  have ha : Fin.last (n+1) ∉ s := by
    intro hl
    obtain ⟨i,_,he⟩ := Finset.mem_map.mp hl
    have he' := congrArg Fin.val he
    change i.val+1 = n+1 at he'
    have hi := i.2
    omega
  have hb : (0 : Fin (n+2)) ∉ insert (Fin.last (n+1)) s := by
    rw [Finset.mem_insert]
    rintro (he|he)
    · have he' := congrArg Fin.val he
      change 0 = n+1 at he'
      omega
    · obtain ⟨i,_,he'⟩ := Finset.mem_map.mp he
      have hh := congrArg Fin.val he'
      change i.val+1 = 0 at hh
      omega
  rw [CompositionAsSet.toComposition_length, CompositionAsSet.length]
  change (insert (0 : Fin (n+2)) (insert (Fin.last (n+1)) s)).card - 1 = _
  rw [Finset.card_insert_of_notMem hb, Finset.card_insert_of_notMem ha, Finset.card_map]
  omega

private theorem boundary_iff_start {N : ℕ} (c : Composition N) (x : Fin N) :
    x.castSucc ∈ c.boundaries ↔ x.val = c.sizeUpTo (c.index x) := by
  constructor
  · intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hx
    have he := congrArg Fin.val hi
    change c.sizeUpTo i.val = x.val at he
    have hle := c.sizeUpTo_index_le x
    have hlt := c.lt_sizeUpTo_index_succ x
    have hie : i.val ≤ (c.index x).val := by
      by_contra! hgt
      have h := c.monotone_sizeUpTo (show (c.index x).val + 1 ≤ i.val by omega)
      change c.sizeUpTo ((c.index x).val+1) ≤ c.sizeUpTo i.val at h
      change x.val < c.sizeUpTo ((c.index x).val+1) at hlt
      omega
    have hix := c.monotone_sizeUpTo hie
    omega
  · intro hx
    apply Finset.mem_map.mpr
    exact ⟨(c.index x).castSucc, Finset.mem_univ _, Fin.ext hx.symm⟩

private theorem edge_iff_same {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    w i = true ↔ (cutComposition w).index i.castSucc = (cutComposition w).index i.succ := by
  let c := cutComposition w
  have hB : w i = false ↔ i.succ.castSucc ∈ c.boundaries := (cut_boundary w i).symm
  rw [boundary_iff_start] at hB
  have hl := c.sizeUpTo_index_le i.succ
  have hh := c.lt_sizeUpTo_index_succ i.succ
  have hll := c.sizeUpTo_index_le i.castSucc
  change c.sizeUpTo (c.index i.succ).val ≤ i.val + 1 at hl
  change i.val+1 < c.sizeUpTo ((c.index i.succ).val+1) at hh
  change c.sizeUpTo (c.index i.castSucc).val ≤ i.val at hll
  constructor
  · intro hw
    have hne : i.val + 1 ≠ c.sizeUpTo (c.index i.succ).val := by
      intro he
      have hfalse := hB.mpr he
      simp [hw] at hfalse
    have hmem : i.castSucc ∈ Set.range (c.embedding (c.index i.succ)) :=
      c.mem_range_embedding_iff.mpr ⟨by change c.sizeUpTo (c.index i.succ).val ≤ i.val; omega,
        by change i.val < c.sizeUpTo ((c.index i.succ).val + 1); omega⟩
    exact (c.mem_range_embedding_iff'.mp hmem).symm
  · intro he
    change c.index i.castSucc = c.index i.succ at he
    rw [he] at hll
    cases hw : w i
    · have hh := hB.mp hw
      change i.val+1 = c.sizeUpTo (c.index i.succ).val at hh
      omega
    · rfl

private theorem edge_before_boundary {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    i.castSucc.castSucc ∈ (cutComposition w).boundaries ↔
      ∀ j : Fin n, j.val + 1 = i.val → w j = false := by
  constructor
  · intro h j hj
    have he : cutEmb n j = i.castSucc.castSucc := Fin.ext hj
    exact (cut_boundary w j).mp (he.symm ▸ h)
  · intro h
    by_cases hi : i.val = 0
    · have hzero : i.castSucc.castSucc = 0 := Fin.ext hi
      rw [hzero]
      exact (cutComposition w).toCompositionAsSet.zero_mem
    · let j : Fin n := ⟨i.val-1,by have := i.2; omega⟩
      have hj : j.val+1 = i.val := by dsimp [j]; omega
      have hj' : cutEmb n j = i.castSucc.castSucc := Fin.ext hj
      exact hj' ▸ (cut_boundary w j).mpr (h j hj)

private abbrev RunStart {n : ℕ} (w : Fin n → Bool) (i : Fin n) : Prop :=
  runAt w i

private theorem nontriv_count {n : ℕ} (w : Fin n → Bool) :
    Fintype.card {a : Fin (cutComposition w).length // 1 < (cutComposition w).blocksFun a} =
      (Finset.univ.filter (RunStart w)).card := by
  classical
  let c := cutComposition w
  have iff_run (i : Fin n) :
      RunStart w i ↔
        c.index i.castSucc = c.index i.succ ∧
        i.val = c.sizeUpTo (c.index i.castSucc) := by
    unfold RunStart
    exact and_congr (edge_iff_same w i)
      ((edge_before_boundary w i).symm.trans (boundary_iff_start c i.castSucc))
  let F (a : {a : Fin c.length // 1 < c.blocksFun a}) : Fin n :=
    ⟨c.sizeUpTo a.val,by
      have hup := c.sizeUpTo_le (a.val.val+1)
      rw [c.sizeUpTo_succ'] at hup
      have ha := a.2
      omega⟩
  have index_F (a : {a : Fin c.length // 1 < c.blocksFun a}) :
      c.index (F a).castSucc = a.val := by
    change c.index (c.embedding a.val ⟨0,by have := a.2; omega⟩) = _
    exact c.index_embedding _ _
  have hF (a : {a : Fin c.length // 1 < c.blocksFun a}) : RunStart w (F a) := by
    rw [iff_run, index_F]
    constructor
    · apply c.mem_range_embedding_iff'.mp
      apply c.mem_range_embedding_iff.mpr
      change c.sizeUpTo a.val ≤ c.sizeUpTo a.val+1 ∧
        c.sizeUpTo a.val+1 < c.sizeUpTo (a.val.val+1)
      rw [c.sizeUpTo_succ']
      have ha := a.2
      omega
    · rfl
  let G (i : {i : Fin n // RunStart w i}) : {a : Fin c.length // 1 < c.blocksFun a} :=
    ⟨c.index i.val.castSucc,by
      have hi := (iff_run i.val).mp i.2
      have hval := c.lt_sizeUpTo_index_succ i.val.succ
      rw [← hi.1] at hval
      change i.val.val+1 < c.sizeUpTo ((c.index i.val.castSucc).val+1) at hval
      rw [c.sizeUpTo_succ', ← hi.2] at hval
      omega⟩
  let e : {a : Fin c.length // 1 < c.blocksFun a} ≃ {i : Fin n // RunStart w i} :=
    ⟨fun a => ⟨F a,hF a⟩, G,
      fun a => Subtype.ext (index_F a),
      fun i => Subtype.ext (Fin.ext ((iff_run i.val).mp i.2).2.symm)⟩
  rw [Fintype.card_congr e]
  simp [Fintype.card_subtype]

end Hertzsprung
namespace Hertzsprung

open Finset

private def Hit {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) (i : Fin n) : Prop :=
  Next (σ.symm i.castSucc).val (σ.symm i.succ).val

private instance {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) : DecidablePred (Hit σ) :=
  fun i => inferInstanceAs (Decidable ((σ.symm i.succ).val = (σ.symm i.castSucc).val + 1 ∨ (σ.symm i.castSucc).val = (σ.symm i.succ).val + 1))

private def Matches {n : ℕ} (w : Fin n → Bool) (σ : Equiv.Perm (Fin (n+1))) :=
  ∀ i : Fin n, w i = true → Hit σ i

private noncomputable instance {n : ℕ} (w : Fin n → Bool) : DecidablePred (Matches w) :=
  Classical.decPred _

private theorem respects_iff_matches {n : ℕ} (w : Fin n → Bool)
    (σ : Equiv.Perm (Fin (n+1))) :
    Respects ((cutComposition w).blocksFinEquiv.trans σ.symm) ↔ Matches w σ := by
  let c := cutComposition w
  have hs (a : Fin c.length) (j : Fin (c.blocksFun a)) :
      (c.blocksFinEquiv ⟨a,j⟩).val = c.sizeUpTo a + j := rfl
  constructor
  · intro hf i hw
    have hindex := (edge_iff_same w i).mp hw
    change c.index i.castSucc = c.index i.succ at hindex
    let a := c.index i.castSucc
    let u : Fin (c.blocksFun a) := c.invEmbedding i.castSucc
    let v : Fin (c.blocksFun a) := ⟨i.succ.val-c.sizeUpTo a,by
      have h := c.lt_sizeUpTo_index_succ i.succ
      rw [← hindex] at h
      change i.succ.val < c.sizeUpTo (a.val+1) at h
      rw [c.sizeUpTo_succ'] at h
      have hlo := c.sizeUpTo_index_le i.castSucc
      change c.sizeUpTo a.val ≤ i.val at hlo
      change i.val+1 < c.sizeUpTo a.val + c.blocksFun a at h
      change i.val+1 - c.sizeUpTo a.val < c.blocksFun a
      omega⟩
    have hu : c.blocksFinEquiv ⟨a,u⟩ = i.castSucc := c.embedding_comp_inv _
    have hv : c.blocksFinEquiv ⟨a,v⟩ = i.succ := by
      apply Fin.ext
      rw [hs]
      have hlo := c.sizeUpTo_index_le i.castSucc
      change c.sizeUpTo a.val ≤ i.val at hlo
      change c.sizeUpTo a.val + (i.val+1-c.sizeUpTo a.val) = i.val+1
      omega
    have hstep : v.val = u.val+1 := by
      have hlo := c.sizeUpTo_index_le i.castSucc
      change c.sizeUpTo a.val ≤ i.val at hlo
      change (i.val+1-c.sizeUpTo a.val) = (i.val-c.sizeUpTo a.val)+1
      omega
    have hh := hf a u v hstep
    change Next (σ.symm (c.blocksFinEquiv ⟨a,u⟩)).val
      (σ.symm (c.blocksFinEquiv ⟨a,v⟩)).val at hh
    rw [hu,hv] at hh
    exact hh
  · intro hf a u v hstep
    let x := c.blocksFinEquiv ⟨a,u⟩
    let y := c.blocksFinEquiv ⟨a,v⟩
    have ha : y.val = x.val+1 := by
      dsimp only [x,y]
      rw [hs,hs,hstep]
      omega
    let i : Fin n := ⟨x.val,by have := y.2; omega⟩
    have h₁ : i.castSucc = x := rfl
    have h₂ : i.succ = y := Fin.ext ha.symm
    have same : c.index i.castSucc = c.index i.succ := by
      rw [h₁,h₂]
      exact (c.index_embedding a u).trans (c.index_embedding a v).symm
    have hh := hf i ((edge_iff_same w i).mpr same)
    unfold Hit at hh
    rw [h₁,h₂] at hh
    exact hh

private theorem count_matches {n : ℕ} (w : Fin n → Bool) :
    Fintype.card {σ : Equiv.Perm (Fin (n+1)) // Matches w σ} =
      (((Finset.univ.filter fun i => w i = false).card + 1).factorial) *
      2 ^ (Finset.univ.filter (RunStart w)).card := by
  classical
  let c := cutComposition w
  let f := c.blocksFinEquiv
  have recover (g : ((a : Fin c.length) × Fin (c.blocksFun a)) ≃ Fin (n+1)) :
      f.trans (g.symm.trans f).symm = g := by
    apply Equiv.ext
    intro x
    simp
  let e : {σ : Equiv.Perm (Fin (n+1)) // Matches w σ} ≃
      {g : ((a : Fin c.length) × Fin (c.blocksFun a)) ≃ Fin (n+1) // Respects g} :=
    { toFun := fun σ => ⟨f.trans σ.val.symm, (respects_iff_matches w σ.val).2 σ.prop⟩
      invFun := fun g => ⟨g.val.symm.trans f, (respects_iff_matches w _).1 (by
        change Respects (f.trans (g.val.symm.trans f).symm)
        rw [recover]
        exact g.prop)⟩
      left_inv := fun σ => by apply Subtype.ext; simp [f, Equiv.trans_assoc]
      right_inv := fun g => Subtype.ext (recover g.val) }
  rw [Fintype.card_congr e, count_placements (fun _ => c.one_le_blocksFun _) c.sum_blocksFun]
  rw [show Fintype.card {a : Fin c.length // 1 < c.blocksFun a} = _ from nontriv_count w,
    show c.length = _ from length_cut w]

end Hertzsprung
namespace Hertzsprung

open Finset

private def masks (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun w := univ.filter (fun i => w i = true)
  invFun s i := decide (i ∈ s)
  left_inv w := by funext i; cases hw : w i <;> simp [hw]
  right_inv s := by ext i; simp

private theorem hit_iff_index {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    (∀ i j : Fin (n+1), j.val = i.val + 1 →
      (σ j).val ≠ (σ i).val + 1 ∧ (σ i).val ≠ (σ j).val + 1) ↔
    ∀ i : Fin n, ¬ Hit σ i := by
  constructor
  · intro h i
    unfold Hit Next
    rintro (hh | hh)
    · have he := (h _ _ hh).1
      simp at he
    · have he := (h _ _ hh).2
      simp at he
  · intro h x y hxy
    constructor
    · intro he
      let i : Fin n := ⟨(σ x).val,by have := (σ y).2; omega⟩
      have hi : i.castSucc = σ x := rfl
      have hj : i.succ = σ y := Fin.ext he.symm
      apply h i
      unfold Hit Next
      rw [hi,hj]
      simpa using Or.inl hxy
    · intro he
      let i : Fin n := ⟨(σ y).val,by have := (σ x).2; omega⟩
      have hi : i.castSucc = σ y := rfl
      have hj : i.succ = σ x := Fin.ext he.symm
      apply h i
      unfold Hit Next
      rw [hi,hj]
      simpa using Or.inr hxy

private theorem cardinal_matches_eq_sum {n : ℕ} (w : Fin n → Bool) :
    (Fintype.card {σ : Equiv.Perm (Fin (n+1)) // Matches w σ} : ℤ) =
      (((univ : Finset (Fin n)).filter (fun i => w i = false)).card+1).factorial *
       (2:ℤ) ^ (univ.filter (RunStart w)).card := by
  exact_mod_cast count_matches w

private theorem inclusion {n : ℕ} :
    (OMA.S_oeis_a002464.a (n+1) : ℤ) =
      ∑ w : Fin n → Bool, (-1:ℤ) ^ (n - (univ.filter (fun i => w i = false)).card) *
        (((univ.filter (fun i => w i = false)).card+1).factorial *
          (2:ℤ) ^ (univ.filter (RunStart w)).card) := by
  classical
  let C (i : Fin n) : Finset (Equiv.Perm (Fin (n+1))) := univ.filter (fun σ => Hit σ i)
  have hA : ((univ : Finset (Fin n)).inf (fun i => (C i)ᶜ)) =
      (univ.filter fun σ : Equiv.Perm (Fin (n+1)) =>
        ∀ i j : Fin (n+1), j.val = i.val + 1 →
          (σ j).val ≠ (σ i).val + 1 ∧ (σ i).val ≠ (σ j).val + 1) := by
    ext σ
    simp [C, Finset.mem_inf, hit_iff_index]
  have hIE := Finset.inclusion_exclusion_card_inf_compl (univ : Finset (Fin n)) C
  have hp : (univ : Finset (Fin n)).powerset = univ := by ext; simp
  rw [hA,hp] at hIE
  change (OMA.S_oeis_a002464.a (n+1) : ℤ) = _ at hIE
  rw [hIE, ← (masks n).sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  change (-1:ℤ)^((univ.filter fun i => w i = true).card) *
      (((masks n w).inf C).card : ℤ) = _
  have hm : (masks n w).inf C =
      (univ.filter (Matches w) : Finset (Equiv.Perm (Fin (n+1)))) := by
    ext σ
    simp [masks,C,Matches,Finset.mem_inf]
  have hfalse : (univ.filter (fun i => w i = true)).card =
      n - (univ.filter (fun i => w i = false)).card := by
    have he : (univ.filter (fun i => w i = true)).card +
        (univ.filter (fun i => w i = false)).card = n := by
      have he := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin n))) (p := fun i => w i = true)
      simpa using he
    omega
  rw [hm,hfalse]
  have hcm : ((univ.filter (Matches w)).card : ℤ) =
      (((univ.filter (fun i => w i = false)).card+1).factorial : ℤ) *
        (2:ℤ) ^ (univ.filter (RunStart w)).card := by
    rw [← Fintype.card_subtype, cardinal_matches_eq_sum]
  rw [hcm]

end Hertzsprung
namespace Hertzsprung

open Finset OMA.S_oeis_a002464

private theorem group_weights (n : ℕ) :
    (∑ w : Fin n → Bool, (-1:ℤ) ^ (n-falseCount w) *
        (((falseCount w+1).factorial : ℤ) * 2^runCount w)) =
      ∑ k ∈ range (n+1), ((k+1).factorial : ℤ) * T n k := by
  classical
  simp only [← signed_masks n, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [sum_eq_single (falseCount w)]
  · simp only [if_true]
    ring
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact (h (mem_range.mpr (Nat.lt_succ_of_le (falseCount_le w)))).elim

private theorem main_succ (n : ℕ) :
    (a (n+1) : ℤ) =
      ∑ k ∈ Icc 1 (n+1), (k.factorial : ℤ) * T n (k-1) := by
  have he := inclusion (n := n)
  change (a (n+1) : ℤ) = (∑ w : Fin n → Bool, (-1:ℤ) ^ (n-falseCount w) *
        (((falseCount w+1).factorial : ℤ) * 2^runCount w)) at he
  rw [he, group_weights]
  refine sum_bij (fun k _ => k+1) (fun k hk => ?_) ?_ ?_ (fun k _ => by simp)
  · rw [mem_Icc]
    exact ⟨by omega, Nat.succ_le_iff.mpr (mem_range.mp hk)⟩
  · intro i _ j _ h
    omega
  · intro k hk
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hk
    exact ⟨k-1,mem_range.mpr (by omega),by omega⟩

end Hertzsprung

theorem OMA.solution : type_of% @OMA.S_oeis_a002464.main := by
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using Hertzsprung.main_succ k
