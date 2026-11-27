import OMAReductions.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1
import Mathlib.Tactic

/-!
# Guarding a closed neighbourhood in Cops and Robbers (`MeynielConjecture` step `H1`)
-/

namespace MeynielStepH1

open MeynielConjecture

private def putLast {V : Type*} {k : ℕ} (c : Fin k → V) (x : V) (j : Fin (k + 1)) : V :=
  if h : j.val < k then c ⟨j.val, h⟩ else x

private lemma putLast_cast {V : Type*} {k : ℕ} (c : Fin k → V) (x : V) (i : Fin k) :
    putLast c x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = c i := by
  simp [putLast, i.isLt]

private lemma putLast_last {V : Type*} {k : ℕ} (c : Fin k → V) (x : V) :
    putLast c x (Fin.last k) = x := by
  simp [putLast]

private lemma putLast_const {V : Type*} {k : ℕ} (x : V) :
    putLast (fun _ : Fin k => x) x = (fun _ : Fin (k + 1) => x) := by
  funext j
  by_cases h : j.val < k <;> simp [putLast, h]

private lemma putLast_step {V : Type*} (G : SimpleGraph V) {k : ℕ}
    {c c' : Fin k → V} (x : V) (hc : ∀ i, Step G (c i) (c' i)) :
    ∀ j : Fin (k + 1), Step G (putLast c x j) (putLast c' x j) := by
  intro j
  by_cases h : j.val < k
  · simpa [putLast, h] using hc ⟨j.val, h⟩
  · simp [putLast, h, Step]

private lemma catch_mono {V : Type*} (G : SimpleGraph V) {k m m' : ℕ} (hle : m ≤ m') :
    ∀ (c : Fin k → V) (r : V), CopsCatchWithin G k m c r → CopsCatchWithin G k m' c r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero =>
    intro c r h
    simpa using h
  | succ d ih =>
    have step1 : ∀ (n : ℕ) (c : Fin k → V) (r : V),
        CopsCatchWithin G k n c r → CopsCatchWithin G k (n + 1) c r := by
      intro n
      induction n with
      | zero =>
        intro c r h
        exact Or.inl h
      | succ n ihn =>
        rintro c r (h0 | ⟨c', hstep, hcaught | hnext⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨c', hstep, Or.inl hcaught⟩
        · exact Or.inr ⟨c', hstep, Or.inr (fun r' hr' => ihn c' r' (hnext r' hr'))⟩
    intro c r h
    rw [← Nat.add_assoc]
    exact step1 (m + d) c r (ih (Nat.le_add_right m d) c r h)

private lemma catch_of_not_avoid {V : Type*} (G : SimpleGraph V) (v : V) {k : ℕ}
    (c : Fin k → V) {r : V} (hr : ¬ (r ≠ v ∧ ¬ G.Adj v r)) :
    CopsCatchWithin G (k + 1) 1 (putLast c v) r := by
  by_cases hrv : r = v
  · subst hrv
    exact Or.inl ⟨Fin.last k, putLast_last c r⟩
  · have hadj : G.Adj v r := by tauto
    refine Or.inr ⟨putLast c r, ?_, Or.inl ⟨Fin.last k, putLast_last c r⟩⟩
    intro j
    by_cases hj : j.val < k
    · simp [putLast, hj, Step]
    · simp [putLast, hj, Step, hadj]

private def walkAt {V : Type*} {G : SimpleGraph V} {u w : V} : G.Walk u w → ℕ → V
  | .nil, _ => u
  | .cons _ _, 0 => u
  | .cons _ q, n + 1 => walkAt q n

private lemma walkAt_zero {V : Type*} {G : SimpleGraph V} {u w : V} (p : G.Walk u w) :
    walkAt p 0 = u := by
  cases p <;> rfl

private lemma walkAt_of_le {V : Type*} {G : SimpleGraph V} {u w : V} (p : G.Walk u w) :
    ∀ {n : ℕ}, p.length ≤ n → walkAt p n = w := by
  induction p with
  | nil =>
    intro n _
    rfl
  | @cons a b c _ q ih =>
    intro n hn
    cases n with
    | zero =>
      simp at hn
    | succ n =>
      simp only [SimpleGraph.Walk.length_cons, Nat.add_le_add_iff_right] at hn
      exact ih hn

private lemma walkAt_step {V : Type*} {G : SimpleGraph V} {u w : V} (p : G.Walk u w) :
    ∀ n : ℕ, Step G (walkAt p n) (walkAt p (n + 1)) := by
  induction p with
  | nil =>
    intro _
    exact Or.inl rfl
  | @cons a b c hadj q ih =>
    intro n
    cases n with
    | zero =>
      change Step G a (walkAt q 0)
      rw [walkAt_zero]
      exact Or.inr hadj
    | succ n =>
      exact ih n

private lemma induce_step_to_G {V : Type*} {G : SimpleGraph V} {s : Set V} {a b : s}
    (h : Step (G.induce s) a b) : Step G a.1 b.1 := by
  rcases h with rfl | hadj
  · exact Or.inl rfl
  · exact Or.inr hadj

theorem prove_Meyniel_H1 :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ), G.Connected →
      (∀ s : Set V, s ⊆ {u | u ≠ v ∧ ¬ G.Adj v u} → (G.induce s).Connected →
        CopsWin (G.induce s) k) →
      CopsWin G (k + 1) := by
  intro V _ G v k hG hsub
  classical
  refine ⟨fun _ => v, fun r₀ => ?_⟩
  let U : Set V := {u | u ≠ v ∧ ¬ G.Adj v u}
  by_cases hr₀ : r₀ ∈ U
  · let s : Set V := {u | ∃ hu : u ∈ U, (G.induce U).Reachable ⟨r₀, hr₀⟩ ⟨u, hu⟩}
    have hsU : s ⊆ U := fun u ⟨hu, _⟩ => hu
    have hr₀s : r₀ ∈ s := ⟨hr₀, SimpleGraph.Reachable.refl _⟩
    have hs_closed : ∀ u ∈ s, ∀ u' ∈ U, Step G u u' → u' ∈ s := by
      rintro u ⟨hu, hreach⟩ u' hu' (rfl | hadj)
      · exact ⟨hu, hreach⟩
      · have hadjU : (G.induce U).Adj ⟨u, hu⟩ ⟨u', hu'⟩ := hadj
        exact ⟨hu', hreach.trans hadjU.reachable⟩
    have walk_to_s : ∀ {x y : U}, (G.induce U).Walk x y →
        ∀ hx : x.1 ∈ s, ∃ hy : y.1 ∈ s, (G.induce s).Reachable ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
      intro x y p
      induction p with
      | nil =>
        intro hx
        exact ⟨hx, SimpleGraph.Reachable.refl _⟩
      | @cons a b c hadj q ih =>
        intro ha
        have hb : b.1 ∈ s := hs_closed a.1 ha b.1 b.2 (Or.inr hadj)
        obtain ⟨hc, hbc⟩ := ih hb
        have hab : (G.induce s).Adj ⟨a.1, ha⟩ ⟨b.1, hb⟩ := hadj
        exact ⟨hc, hab.reachable.trans hbc⟩
    have : Nonempty s := ⟨⟨r₀, hr₀s⟩⟩
    have hsc : (G.induce s).Connected := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨haU, haR⟩ := a.2
      obtain ⟨hbU, hbR⟩ := b.2
      obtain ⟨pa⟩ := haR
      obtain ⟨pb⟩ := hbR
      obtain ⟨ha', hra⟩ := walk_to_s pa hr₀s
      obtain ⟨hb', hrb⟩ := walk_to_s pb hr₀s
      have ea : (⟨a.1, ha'⟩ : s) = a := Subtype.ext rfl
      have eb : (⟨b.1, hb'⟩ : s) = b := Subtype.ext rfl
      rw [ea] at hra
      rw [eb] at hrb
      exact hra.symm.trans hrb
    obtain ⟨t₀, ht₀⟩ := hsub s hsU hsc
    let M : ℕ := (Finset.univ : Finset s).sup (fun w => Classical.choose (ht₀ w))
    have ht₀_unif : ∀ w : s, CopsCatchWithin (G.induce s) k M t₀ w := by
      intro w
      exact catch_mono (G.induce s) (Finset.le_sup (Finset.mem_univ w)) t₀ w
        (Classical.choose_spec (ht₀ w))
    have lift_catch : ∀ (m : ℕ) (c : Fin k → s) (w : s),
        CopsCatchWithin (G.induce s) k m c w →
        CopsCatchWithin G (k + 1) (m + 1) (putLast (fun i => (c i).1) v) w.1 := by
      intro m
      induction m with
      | zero =>
        rintro c w ⟨i, hi⟩
        refine Or.inl ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩
        rw [putLast_cast, hi]
      | succ m ih =>
        rintro c w (⟨i, hi⟩ | ⟨c', hstep, ⟨i, hi⟩ | hnext⟩)
        · refine Or.inl ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩
          rw [putLast_cast, hi]
        · refine Or.inr ⟨putLast (fun l => (c' l).1) v,
            putLast_step G v (fun l => induce_step_to_G (hstep l)),
            Or.inl ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩⟩
          rw [putLast_cast, hi]
        · refine Or.inr ⟨putLast (fun l => (c' l).1) v,
            putLast_step G v (fun l => induce_step_to_G (hstep l)),
            Or.inr (fun r' hr' => ?_)⟩
          by_cases hr'U : r' ∈ U
          · have hr's : r' ∈ s := hs_closed w.1 w.2 r' hr'U hr'
            have hstep_s : Step (G.induce s) w ⟨r', hr's⟩ := by
              rcases hr' with rfl | hadj
              · exact Or.inl (Subtype.ext rfl)
              · exact Or.inr hadj
            exact ih c' ⟨r', hr's⟩ (hnext ⟨r', hr's⟩ hstep_s)
          · exact catch_mono G (Nat.succ_pos m) _ r'
              (catch_of_not_avoid G v (fun l => (c' l).1) hr'U)
    have hPhase2 : ∀ w : s,
        CopsCatchWithin G (k + 1) (M + 1) (putLast (fun i => (t₀ i).1) v) w.1 :=
      fun w => lift_catch M t₀ w (ht₀_unif w)
    have hp : ∀ i : Fin k, ∃ p : G.Walk v (t₀ i).1, True :=
      fun i => let ⟨p⟩ := hG.preconnected v (t₀ i).1; ⟨p, trivial⟩
    let p : ∀ i : Fin k, G.Walk v (t₀ i).1 := fun i => Classical.choose (hp i)
    let D : ℕ := (Finset.univ : Finset (Fin k)).sup (fun i => (p i).length)
    let sched : ℕ → Fin k → V := fun n i => walkAt (p i) n
    have hsched0 : sched 0 = (fun _ => v) := funext (fun i => walkAt_zero (p i))
    have hschedD : sched D = (fun i => (t₀ i).1) :=
      funext (fun i => walkAt_of_le (p i)
        (Finset.le_sup (f := fun j : Fin k => (p j).length) (Finset.mem_univ i)))
    have hsched_step : ∀ n i, Step G (sched n i) (sched (n + 1) i) :=
      fun n i => walkAt_step (p i) n
    have walk_phase : ∀ (d : ℕ) (f : ℕ → Fin k → V),
        (∀ n i, Step G (f n i) (f (n + 1) i)) →
        (∀ w : s, CopsCatchWithin G (k + 1) (M + 1) (putLast (f d) v) w.1) →
        ∀ w : s, CopsCatchWithin G (k + 1) (d + (M + 1)) (putLast (f 0) v) w.1 := by
      intro d
      induction d with
      | zero =>
        intro f _ hbase w
        simpa using hbase w
      | succ d ih =>
        intro f hf hbase w
        rw [Nat.succ_add]
        refine Or.inr ⟨putLast (f 1) v, putLast_step G v (hf 0), Or.inr (fun r' hr' => ?_)⟩
        by_cases hr'U : r' ∈ U
        · have hr's : r' ∈ s := hs_closed w.1 w.2 r' hr'U hr'
          exact ih (fun n => f (n + 1)) (fun n i => hf (n + 1) i)
            (by simpa [Nat.add_comm d 1] using hbase) ⟨r', hr's⟩
        · exact catch_mono G (by omega : 1 ≤ d + (M + 1)) (putLast (f 1) v) r'
            (catch_of_not_avoid G v (f 1) hr'U)
    have htotal := walk_phase D sched hsched_step (by rw [hschedD]; exact hPhase2) ⟨r₀, hr₀s⟩
    rw [hsched0, putLast_const] at htotal
    exact ⟨D + (M + 1), htotal⟩
  · refine ⟨1, ?_⟩
    rw [← putLast_const (k := k) v]
    exact catch_of_not_avoid G v (fun _ => v) hr₀

end MeynielStepH1

export MeynielStepH1 (prove_Meyniel_H1)

theorem OMA.solution : OMA.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1.H1 :=
  MeynielStepH1.prove_Meyniel_H1
