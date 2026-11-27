import OMAReductions.R_Erdos107_variants_su_bound_R1_H1_R1
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

-- Credit: @anmolspace for the finite-indexed sampling argument below.
-- Cup–cap recurrence and orientation lemmas by @Genbox, reproduced from the accepted
-- Erdos107.variants.ersz_bounds proof (PR #1086) because those lemmas are private there.
-- The underlying binomial recurrence is due to Erdős and Szekeres (1935).

open Finset
open scoped Classical

namespace OMA.SampledCupCap

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

private def turn (up : Bool) (a b c : Point) : Prop :=
  if up then 0 < orient a b c else orient a b c < 0

private def turns (up : Bool) : List Point → Prop
  | a :: b :: c :: l => turn up a b c ∧ turns up (b :: c :: l)
  | _ => True

private def IsSeq (up : Bool) (X : Finset Point) (l : List Point) : Prop :=
  (∀ p ∈ l, p ∈ X) ∧ l.Pairwise (fun p q => p.1 < q.1) ∧ turns up l

private def HasSeq (up : Bool) (X : Finset Point) (k : ℕ) : Prop :=
  ∃ l, IsSeq up X l ∧ l.length = k

private theorem isSeq_mono {up : Bool} {X Y : Finset Point} {l : List Point}
    (hl : IsSeq up X l) (hXY : X ⊆ Y) : IsSeq up Y l :=
  ⟨fun p hp => hXY (hl.1 p hp), hl.2⟩

private theorem turns_append {up : Bool} {a b c : Point} (l : List Point)
    (hl : turns up (l ++ [a, b])) (hc : turn up a b c) :
    turns up (l ++ [a, b, c]) := by
  induction l with
  | nil => simpa [turns] using hc
  | cons x l ih =>
    cases l with
    | nil =>
      have h := (show turn up x a b ∧ turns up [a, b] from hl).1
      exact ⟨h, ih (by trivial)⟩
    | cons y l =>
      cases l with
      | nil =>
        exact ⟨(show turn up x y a ∧ turns up [y, a, b] from hl).1,
          ih (show turns up [y, a, b] from hl.2)⟩
      | cons z l =>
        exact ⟨(show turn up x y z ∧ turns up ((y :: z :: l) ++ [a, b]) from hl).1,
          ih (show turns up ((y :: z :: l) ++ [a, b]) from hl.2)⟩

private theorem isSeq_append {up : Bool} {X : Finset Point} {a b c : Point} {l : List Point}
    (hl : IsSeq up X (l ++ [a, b])) (hc : c ∈ X) (hbc : b.1 < c.1) (ht : turn up a b c) :
    IsSeq up X (l ++ [a, b, c]) := by
  rw [show l ++ [a, b, c] = (l ++ [a, b]) ++ [c] by simp]
  refine ⟨?_, List.pairwise_append.2 ⟨hl.2.1, by simp, ?_⟩, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hl.1 p hp
    · simpa using (List.mem_singleton.1 hp ▸ hc)
  · intro p hp q hq
    have hqc := List.mem_singleton.1 hq
    subst q
    rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp] at hp
    rcases List.mem_append.1 hp with hp | hp
    · have hsort := hl.2.1
      rw [show l ++ [a,b] = (l ++ [a]) ++ [b] by simp] at hsort
      exact ((List.pairwise_append.1 hsort).2.2 _ hp _ (by simp)).trans hbc
    · simpa [List.mem_singleton.1 hp] using hbc
  · simpa using turns_append l hl.2.2 ht

private theorem exists_suffix_two {l : List Point} (h : 2 ≤ l.length) :
    ∃ pre a b, l = pre ++ [a, b] := by
  have hrevlen : 2 ≤ l.reverse.length := by simpa using h
  cases hr : l.reverse with
  | nil => simp [hr] at hrevlen
  | cons b r =>
    cases r with
    | nil => simp [hr] at hrevlen
    | cons a pre =>
      exact ⟨pre.reverse, a, b, by
        simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hr⟩

private def IsEnd (s : ℕ) (X : Finset Point) (p : Point) : Prop :=
  ∃ pre a, IsSeq true X (pre ++ [a, p]) ∧ pre.length = s

private theorem no_shorter_cup_outside (s : ℕ) (X : Finset Point) :
    ¬ HasSeq true {p ∈ X | ¬ IsEnd s X p} (s + 2) := by
  rintro ⟨l, hl, hlen⟩
  obtain ⟨pre, a, p, rfl⟩ := exists_suffix_two (by omega : 2 ≤ l.length)
  have hp := Finset.mem_filter.1 (hl.1 p (by simp))
  have hpre : pre.length = s := by simpa using hlen
  exact hp.2 ⟨pre, a, isSeq_mono hl (Finset.filter_subset _ _), hpre⟩

private theorem no_shorter_cap_in_ends (s t : ℕ) (X : Finset Point)
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 3)) (hd : ¬ HasSeq false X (t + 3)) :
    ¬ HasSeq false {p ∈ X | IsEnd s X p} (t + 2) := by
  rintro ⟨l, hl, hlen⟩
  cases l with
  | nil => simp at hlen
  | cons p l =>
    cases l with
    | nil => simp at hlen
    | cons q tail =>
      obtain ⟨hp, pre, a, hcup, hpre⟩ := Finset.mem_filter.1 (hl.1 p (by simp))
      have hq := (Finset.mem_filter.1 (hl.1 q (by simp))).1
      have ha := hcup.1 a (by simp)
      have hap : a.1 < p.1 :=
        (List.pairwise_cons.1 (List.pairwise_append.1 hcup.2.1).2.1).1 p (by simp)
      have hpq : p.1 < q.1 := (List.pairwise_cons.1 hl.2.1).1 q (by simp)
      by_cases hturn : 0 < orient a p q
      · apply hc
        exact ⟨pre ++ [a, p, q],
          isSeq_append hcup hq hpq (by simpa [turn] using hturn), by simp [hpre]⟩
      · apply hd
        have hneg : orient a p q < 0 :=
          lt_of_le_of_ne (le_of_not_gt hturn) (hgen a ha p hp q hq hap hpq)
        have hlX := isSeq_mono hl (Finset.filter_subset _ _)
        refine ⟨a :: p :: q :: tail,
          ⟨?_, List.pairwise_cons.2 ⟨?_, hlX.2.1⟩, ?_⟩, ?_⟩
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact ha
          · exact hlX.1 b hb
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hap
          · exact hap.trans ((List.pairwise_cons.1 hlX.2.1).1 _ hb)
        · change turn false a p q ∧ turns false (p :: q :: tail)
          exact ⟨by simpa [turn] using hneg, hlX.2.2⟩
        · simp only [List.length_cons] at hlen ⊢
          omega

private theorem hasSeq_two {X : Finset Point}
    (hx : Set.InjOn Prod.fst (X : Set Point)) (hX : 1 < X.card) (up : Bool) :
    HasSeq up X 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hX
  have hne : a.1 ≠ b.1 := fun he => hab (hx ha hb he)
  have hseq {a b : Point} (ha : a ∈ X) (hb : b ∈ X) (hab : a.1 < b.1) :
      HasSeq up X 2 := by
    refine ⟨[a, b], ⟨?_, ?_, trivial⟩, rfl⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    · simp [hab]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hseq ha hb h
  · exact hseq hb ha h

private theorem card_le_binomial (s t : ℕ) (X : Finset Point)
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 2)) (hd : ¬ HasSeq false X (t + 2)) :
    X.card ≤ (s + t).choose s := by
  induction s generalizing t X with
  | zero =>
    simpa using (le_of_not_gt fun h => hc (hasSeq_two hx h true))
  | succ s ih =>
    induction t generalizing X with
    | zero =>
      simpa using (le_of_not_gt fun h => hd (hasSeq_two hx h false))
    | succ t jt =>
      let T := X.filter (IsEnd s X)
      let U := X.filter (fun p => ¬ IsEnd s X p)
      have hTX : T ⊆ X := Finset.filter_subset _ _
      have hUX : U ⊆ X := Finset.filter_subset _ _
      have hT : T.card ≤ (s + 1 + t).choose (s + 1) := by
        apply jt T (hx.mono hTX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hTX ha) b (hTX hb) c (hTX hc) hab hbc
        · rintro ⟨l, hl, hlen⟩
          exact hc ⟨l, isSeq_mono hl hTX, hlen⟩
        · exact no_shorter_cap_in_ends s t X hgen hc hd
      have hU : U.card ≤ (s + (t + 1)).choose s := by
        apply ih (t + 1) U (hx.mono hUX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hUX ha) b (hUX hb) c (hUX hc) hab hbc
        · exact no_shorter_cup_outside s X
        · rintro ⟨l, hl, hlen⟩
          exact hd ⟨l, isSeq_mono hl hUX, hlen⟩
      have hpart : T.card + U.card = X.card :=
        Finset.card_filter_add_card_filter_not (IsEnd s X)
      have hchoose :
          ((s + 1) + (t + 1)).choose (s + 1) =
            (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega,
          Nat.choose_succ_succ', show s + (t + 1) = s + 1 + t by omega]
      rw [hchoose, ← hpart]
      exact (Nat.add_le_add hT hU).trans_eq (Nat.add_comm _ _)

private def signedOrient (up : Bool) (a b c : Point) : ℝ :=
  (if up then 1 else -1) * orient a b c

private theorem turn_iff_signed (up : Bool) (a b c : Point) :
    turn up a b c ↔ 0 < signedOrient up a b c := by
  cases up <;> simp [turn, signedOrient]

private theorem turn_quad {up : Bool} {a b c d : Point}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h₁ : turn up a b c) (h₂ : turn up b c d) :
    turn up a b d ∧ turn up a c d := by
  rw [turn_iff_signed] at h₁ h₂
  simp only [turn_iff_signed]
  have hleft :
      (c.1 - b.1) * signedOrient up a b d =
        (d.1 - b.1) * signedOrient up a b c + (b.1 - a.1) * signedOrient up b c d := by
    unfold signedOrient orient
    ring
  have hright :
      (c.1 - b.1) * signedOrient up a c d =
        (c.1 - a.1) * signedOrient up b c d + (d.1 - c.1) * signedOrient up a b c := by
    unfold signedOrient orient
    ring
  constructor
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hleft]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁) (mul_pos (sub_pos.mpr hab) h₂)
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hright]
    exact add_pos (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂) (mul_pos (sub_pos.mpr hcd) h₁)

private theorem turns_tail {up : Bool} {a : Point} {l : List Point}
    (h : turns up (a :: l)) : turns up l := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
  · trivial
  · trivial
  · exact h.2

private theorem x_lt_next {a b : Point} {l : List Point}
    (h : (a :: b :: l).Pairwise (fun p q => p.1 < q.1)) : a.1 < b.1 :=
  (List.pairwise_cons.1 h).1 b (by simp)

private theorem turns_delete {up : Bool} {p : Point} {l : List Point} (pre : List Point)
    (hs : (pre ++ p :: l).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ p :: l)) : turns up (pre ++ l) := by
  induction pre with
  | nil => exact turns_tail ht
  | cons a pre ih =>
    cases pre with
    | nil =>
      rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
      · trivial
      · trivial
      · have hs' : (a :: p :: b :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
        have ht' : turns up (a :: p :: b :: c :: l) := ht
        have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
          (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
        exact ⟨hp.2, ht'.2.2⟩
    | cons b pre =>
      cases pre with
      | nil =>
        cases l with
        | nil => trivial
        | cons c l =>
          have hs' : (a :: b :: p :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
          have ht' : turns up (a :: b :: p :: c :: l) := ht
          have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
            (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
          exact ⟨hp.1, ih hs'.tail ht'.2⟩
      | cons c pre =>
        have ht' : turns up (a :: b :: c :: (pre ++ p :: l)) := ht
        exact ⟨ht'.1, ih hs.tail ht'.2⟩

private theorem turns_sublist_append {up : Bool} {l₁ l₂ : List Point} (h : List.Sublist l₁ l₂)
    (pre : List Point) (hs : (pre ++ l₂).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ l₂)) : turns up (pre ++ l₁) := by
  induction h generalizing pre with
  | slnil => exact ht
  | cons a h ih =>
    apply ih pre
    · apply List.Pairwise.sublist _ hs
      exact (List.Sublist.refl _).append (List.Sublist.cons _ (List.Sublist.refl _))
    · exact turns_delete pre hs ht
  | cons_cons a h ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [a]) (by simpa only [List.append_assoc, List.singleton_append] using hs)
        (by simpa only [List.append_assoc, List.singleton_append] using ht)

private theorem turn_of_mem {up : Bool} {X : Finset Point} {l : List Point}
    (h : IsSeq up X l) {a b c : Point} (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) : turn up a b c := by
  let r : Point → Point → Prop := fun a b => a.1 < b.1
  let : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim⟩
  let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  have htri : [a, b, c].Pairwise r := by simp [r, hab, hbc, hab.trans hbc]
  have hsub : [a, b, c] ⊆ l := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hsublist : List.Sublist [a, b, c] l :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htri.nodup hsub) htri h.2.1
  have hh := turns_sublist_append hsublist [] h.2.1 h.2.2
  exact hh.1

/-- Sample the cup or cap in its increasing order of first coordinate. -/
theorem sample : ∀ k : ℕ, 0 < k → ∃ m : ℕ, 2 * k + 1 ≤ m ∧
    ∀ U : Finset (ℝ × ℝ), U.card = m → Set.InjOn Prod.fst (U : Set (ℝ × ℝ)) →
      (∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a.1 < b.1 → b.1 < c.1 →
        (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
      ∃ (up : Bool) (e : Fin (2 * k + 1) → ℝ × ℝ), (∀ i, e i ∈ U) ∧
        StrictMono (fun i => (e i).1) ∧ ∀ i j l, i < j → j < l →
          0 < (if up then (1 : ℝ) else -1) * (((e j).1 - (e i).1) * ((e l).2 - (e j).2) -
            ((e j).2 - (e i).2) * ((e l).1 - (e j).1)) := by
  intro k hk
  let n := 2*k+1
  let s := n-2
  have hs : s+2 = n := by dsimp [s, n]; omega
  refine ⟨n + (s+s).choose s + 1, by dsimp [n]; omega, ?_⟩
  intro U hU hx hgen
  have hseq : ∃ up : Bool, HasSeq up U n := by
    by_contra h
    have ht : ¬ HasSeq true U (s+2) := by rw [hs]; exact fun h' ↦ h ⟨true,h'⟩
    have hf : ¬ HasSeq false U (s+2) := by rw [hs]; exact fun h' ↦ h ⟨false,h'⟩
    have hbound := card_le_binomial s s U hx hgen ht hf
    omega
  obtain ⟨up, l, hl, hlen⟩ := hseq
  let e (i : Fin n) := l.get (Fin.cast hlen.symm i)
  have hm (i : Fin n) : e i ∈ l := List.get_mem _ _
  have mono : StrictMono (fun i : Fin n ↦ (e i).1) := by
    intro i j hij
    exact hl.2.1.rel_get_of_lt (a := Fin.cast hlen.symm i) (b := Fin.cast hlen.symm j) hij
  refine ⟨up, e, fun i ↦ hl.1 _ (hm i), mono, ?_⟩
  intro i j t hij hjt
  exact (turn_iff_signed up _ _ _).mp (turn_of_mem hl (hm i) (hm j) (hm t) (mono hij) (mono hjt))

end OMA.SampledCupCap

theorem OMA.solution : OMA.R_Erdos107_variants_su_bound_R1_H1_R1.H1 :=
  OMA.SampledCupCap.sample
