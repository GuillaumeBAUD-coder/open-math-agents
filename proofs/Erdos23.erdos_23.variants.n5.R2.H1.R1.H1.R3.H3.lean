import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R3
import Mathlib.Tactic

/-!
Finite weighted-cut proof of the three-exception path step.
Parent reduction and reusable lemmas: @YOHSUKE-TAKAHASHI, PR21505.
Ancestor edge counting/reduction: @steveDOTdigital, PR4581 and PR4937.
Large independent set argument used by the parent degree lemma:
@synthrosai, notes86740,86767,86816.
The finite tables, exact certificates and graph-counting bridge below
were written independently for this step.
-/

-- NativeTables

namespace ThreeExceptions
open SimpleGraph

abbrev Near (a b : Fin 5) : Prop := b=a+1 ∨ a=b+1

abbrev Regular := Fin 5 × (Fin 3 → Bool)
abbrev Slot := Regular ⊕ Fin 3

abbrev Valid (t : Fin 3 → Fin 5) (a : Regular) : Prop :=
  (∀ x, a.2 x=true → ¬ Near a.1 (t x)) ∧
  ¬(a.2 0=true ∧ a.2 1=true) ∧ ¬(a.2 0=true ∧ a.2 2=true)

def Allowed (t : Fin 3 → Fin 5) (a b : Slot) : Prop :=
  match a,b with
  | .inl u,.inl v => Valid t u ∧ Valid t v ∧ Near u.1 v.1 ∧
      ∀ x, ¬(u.2 x=true ∧ v.2 x=true)
  | .inl u,.inr x => Valid t u ∧ u.2 x=true
  | .inr x,.inl u => Valid t u ∧ u.2 x=true
  | .inr x,.inr y => x≠y ∧ (x=0 ∨ y=0)

variable {V : Type*}

noncomputable def label (G : SimpleGraph V) (ex : Fin 3 → V) (g : V → Fin 5)
    (a : V) : Slot := by
  classical
  exact if h : ∃ x, a=ex x then .inr h.choose
    else .inl (g a, fun x => decide (G.Adj (ex x) a))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem label_exception (G : SimpleGraph V) (ex : Fin 3 → V)
    (inj : Function.Injective ex) (g : V → Fin 5) (x : Fin 3) :
    label G ex g (ex x)=.inr x := by
  classical
  have h : ∃ y, ex x=ex y := ⟨x,rfl⟩
  have hc : h.choose=x := (inj h.choose_spec).symm
  simp [label,h,hc]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem label_exception_iff (G : SimpleGraph V) (ex : Fin 3 → V)
    (inj : Function.Injective ex) (g : V → Fin 5) (a : V) (x : Fin 3) :
    label G ex g a=.inr x ↔ a=ex x := by
  classical
  constructor
  · intro hh
    by_cases h : ∃ y, a=ex y
    · have hc : h.choose=x := by simpa [label,h] using hh
      simpa [hc] using h.choose_spec
    · simp [label,h] at hh
  · rintro rfl
    exact label_exception G ex inj g x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem label_regular (G : SimpleGraph V) (ex : Fin 3 → V) (g : V → Fin 5)
    (a : V) (u : Regular) (h : label G ex g a=.inl u) :
    (¬∃ x,a=ex x) ∧ g a=u.1 ∧ ∀ x, G.Adj (ex x) a ↔ u.2 x=true := by
  classical
  by_cases hx : ∃ x,a=ex x
  · simp [label,hx] at h
  · have he : (g a,fun x => decide (G.Adj (ex x) a))=u := by
      simpa [label,hx] using h
    refine ⟨hx,congrArg Prod.fst he,?_⟩
    intro x
    have hm := congrFun (congrArg Prod.snd he) x
    rw [←hm]
    simp

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem label_valid (G : SimpleGraph V) (ex : Fin 3 → V) (g : V → Fin 5)
    (v : Fin 5 → V) (t : Fin 3 → Fin 5)
    (tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (exedge : ∀ x y, G.Adj (ex x) (ex y) ↔ x≠y ∧ (x=0 ∨ y=0))
    (single : ∀ x i, G.Adj (ex x) (v i) ↔ i=t x)
    (profile : ∀ a, (¬∃ x,a=ex x) → ∀ i, G.Adj a (v i) ↔ Near (g a) i)
    (a : V) (u : Regular) (h : label G ex g a=.inl u) : Valid t u := by
  classical
  obtain ⟨ha,hg,hm⟩ := label_regular G ex g a u h
  have edge (x : Fin 3) (hx : u.2 x=true) : G.Adj (ex x) a :=
    (hm x).mpr hx
  refine ⟨?_,?_,?_⟩
  · intro x hx hn
    have ac : G.Adj a (v (t x)) := (profile a ha _).mpr (by simpa [hg] using hn)
    exact tri _ _ _ (edge x hx) ((single x _).mpr rfl) ac
  · rintro ⟨hp,hq⟩
    exact tri _ _ _ ((exedge 0 1).mpr (by decide)) (edge 0 hp) (edge 1 hq)
  · rintro ⟨hp,hr⟩
    exact tri _ _ _ ((exedge 0 2).mpr (by decide)) (edge 0 hp) (edge 2 hr)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem label_hom (G : SimpleGraph V) (ex : Fin 3 → V)
    (inj : Function.Injective ex) (g : V → Fin 5)
    (v : Fin 5 → V) (t : Fin 3 → Fin 5)
    (tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (exedge : ∀ x y, G.Adj (ex x) (ex y) ↔ x≠y ∧ (x=0 ∨ y=0))
    (single : ∀ x i, G.Adj (ex x) (v i) ↔ i=t x)
    (profile : ∀ a, (¬∃ x,a=ex x) → ∀ i, G.Adj a (v i) ↔ Near (g a) i)
    (maps : ∀ a, (¬∃ x,a=ex x) → ∀ b, (¬∃ x,b=ex x) → G.Adj a b → Near (g a) (g b)) :
    ∀ a b, G.Adj a b → Allowed t (label G ex g a) (label G ex g b) := by
  classical
  intro a b hab
  cases ha : label G ex g a with
  | inl u =>
    have ua := label_regular G ex g a u ha
    have uv := label_valid G ex g v t tri exedge single profile a u ha
    cases hb : label G ex g b with
    | inl w =>
      have wb := label_regular G ex g b w hb
      have wv := label_valid G ex g v t tri exedge single profile b w hb
      refine ⟨uv,wv,?_,?_⟩
      · simpa [ua.2.1,wb.2.1] using maps a ua.1 b wb.1 hab
      · rintro x ⟨hu,hw⟩
        exact tri (ex x) a b ((ua.2.2 x).mpr hu) ((wb.2.2 x).mpr hw) hab
    | inr x =>
      have hb' := (label_exception_iff G ex inj g b x).mp hb
      subst b
      refine ⟨uv,?_⟩
      exact (ua.2.2 x).mp hab.symm
  | inr x =>
    have ha' := (label_exception_iff G ex inj g a x).mp ha
    subst a
    cases hb : label G ex g b with
    | inl w =>
      have wb := label_regular G ex g b w hb
      refine ⟨label_valid G ex g v t tri exedge single profile b w hb,?_⟩
      exact (wb.2.2 x).mp hab
    | inr y =>
      have hb' := (label_exception_iff G ex inj g b y).mp hb
      subst b
      exact (exedge x y).mp hab

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem near_irrefl : ∀ i : Fin 5, ¬Near i i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem near_cycle_center : ∀ a i : Fin 5, Near a (i+1) → Near a (i+4) → a=i := by
  decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycle_arithmetic : ∀ i : Fin 5, (i+4)+1=i ∧ i+1≠i+4 := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycle_regular (G : SimpleGraph V) (ex : Fin 3 → V) (v : Fin 5 → V)
    (t : Fin 3 → Fin 5) (cyc : ∀ i, G.Adj (v i) (v (i+1)))
    (single : ∀ x i, G.Adj (ex x) (v i) ↔ i=t x) :
    ∀ i, ¬∃ x, v i=ex x := by
  intro i ⟨x,hx⟩
  have left := cyc i
  have right := (cyc (i+4)).symm
  rw [(cycle_arithmetic i).1] at right
  rw [hx] at left right
  exact (cycle_arithmetic i).2 (((single x _).mp left).trans ((single x _).mp right).symm)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycle_profile (G : SimpleGraph V) (ex : Fin 3 → V) (g : V → Fin 5)
    (v : Fin 5 → V) (t : Fin 3 → Fin 5) (cyc : ∀ i, G.Adj (v i) (v (i+1)))
    (single : ∀ x i, G.Adj (ex x) (v i) ↔ i=t x)
    (profile : ∀ a, (¬∃ x,a=ex x) → ∀ i, G.Adj a (v i) ↔ Near (g a) i) :
    ∀ i, g (v i)=i := by
  intro i
  have regular := cycle_regular G ex v t cyc single i
  apply near_cycle_center
  · exact (profile _ regular _).mp (cyc i)
  · apply (profile _ regular _).mp
    have h := (cyc (i+4)).symm
    rwa [(cycle_arithmetic i).1] at h

end ThreeExceptions


namespace FiniteCutTemplate
open ThreeExceptions
def ordered {n e : ℕ} (ends : Fin e → Fin n × Fin n) (o : Fin e × Bool) : Fin n × Fin n :=
  if o.2 then ((ends o.1).2,(ends o.1).1) else ends o.1
structure Table (t : Fin 3 → Fin 5) (n e : ℕ) where
  slot : Fin n → Regular
  ends : Fin e → Fin n × Fin n
  cycle : Fin 5 → Fin n
  valid : ∀ i, Valid t (slot i)
  injective : Function.Injective slot
  covers : ∀ u : Regular, Valid t u → ∃ i, slot i=u
  ordered_inj : Function.Injective (ordered ends)
  ordered_covers : ∀ a b : Fin n,
    (Near (slot a).1 (slot b).1 ∧ ∀ x, ¬((slot a).2 x=true ∧ (slot b).2 x=true)) ↔
      ∃ o, ordered ends o=(a,b)
  cycle_spec : ∀ i, slot (cycle i)=(i,fun x => decide (i=t x))
end FiniteCutTemplate

namespace NativeCutTemplate.C011
open ThreeExceptions FiniteCutTemplate
def t : Fin 3 → Fin 5 := fun x => if x=0 then 0 else if x=1 then 1 else 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def slot (a : Fin 17) : Regular :=
  match a.val with
  | 0 => (0,fun x => (0 : ℕ).testBit x.val)
  | 1 => (0,fun x => (1 : ℕ).testBit x.val)
  | 2 => (1,fun x => (0 : ℕ).testBit x.val)
  | 3 => (1,fun x => (2 : ℕ).testBit x.val)
  | 4 => (1,fun x => (4 : ℕ).testBit x.val)
  | 5 => (1,fun x => (6 : ℕ).testBit x.val)
  | 6 => (2,fun x => (0 : ℕ).testBit x.val)
  | 7 => (2,fun x => (1 : ℕ).testBit x.val)
  | 8 => (3,fun x => (0 : ℕ).testBit x.val)
  | 9 => (3,fun x => (1 : ℕ).testBit x.val)
  | 10 => (3,fun x => (2 : ℕ).testBit x.val)
  | 11 => (3,fun x => (4 : ℕ).testBit x.val)
  | 12 => (3,fun x => (6 : ℕ).testBit x.val)
  | 13 => (4,fun x => (0 : ℕ).testBit x.val)
  | 14 => (4,fun x => (2 : ℕ).testBit x.val)
  | 15 => (4,fun x => (4 : ℕ).testBit x.val)
  | 16 => (4,fun x => (6 : ℕ).testBit x.val)
  | _ => (0,fun _ => false)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def ends (k : Fin 46) : Fin 17 × Fin 17 :=
  match k.val with
  | 0 => (2,0)
  | 1 => (2,1)
  | 2 => (3,0)
  | 3 => (3,1)
  | 4 => (4,0)
  | 5 => (4,1)
  | 6 => (5,0)
  | 7 => (5,1)
  | 8 => (6,2)
  | 9 => (6,3)
  | 10 => (6,4)
  | 11 => (6,5)
  | 12 => (7,2)
  | 13 => (7,3)
  | 14 => (7,4)
  | 15 => (7,5)
  | 16 => (8,6)
  | 17 => (8,7)
  | 18 => (9,6)
  | 19 => (10,6)
  | 20 => (10,7)
  | 21 => (11,6)
  | 22 => (11,7)
  | 23 => (12,6)
  | 24 => (12,7)
  | 25 => (13,0)
  | 26 => (13,1)
  | 27 => (13,8)
  | 28 => (13,9)
  | 29 => (13,10)
  | 30 => (13,11)
  | 31 => (13,12)
  | 32 => (14,0)
  | 33 => (14,1)
  | 34 => (14,8)
  | 35 => (14,9)
  | 36 => (14,11)
  | 37 => (15,0)
  | 38 => (15,1)
  | 39 => (15,8)
  | 40 => (15,9)
  | 41 => (15,10)
  | 42 => (16,0)
  | 43 => (16,1)
  | 44 => (16,8)
  | 45 => (16,9)
  | _ => (0,0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def cycle (i : Fin 5) : Fin 17 :=
  match i.val with
  | 0 => 1
  | 1 => 5
  | 2 => 6
  | 3 => 8
  | 4 => 13
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def table : Table t 17 46 where
  slot := slot
  ends := ends
  cycle := cycle
  valid := by decide +kernel
  injective := by decide +kernel
  covers := by decide +kernel
  ordered_inj := by decide +kernel
  ordered_covers := by decide +kernel
  cycle_spec := by decide +kernel
end NativeCutTemplate.C011

namespace NativeCutTemplate.C012
open ThreeExceptions FiniteCutTemplate
def t : Fin 3 → Fin 5 := fun x => if x=0 then 0 else if x=1 then 1 else 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def slot (a : Fin 15) : Regular :=
  match a.val with
  | 0 => (0,fun x => (0 : ℕ).testBit x.val)
  | 1 => (0,fun x => (1 : ℕ).testBit x.val)
  | 2 => (0,fun x => (4 : ℕ).testBit x.val)
  | 3 => (1,fun x => (0 : ℕ).testBit x.val)
  | 4 => (1,fun x => (2 : ℕ).testBit x.val)
  | 5 => (2,fun x => (0 : ℕ).testBit x.val)
  | 6 => (2,fun x => (1 : ℕ).testBit x.val)
  | 7 => (2,fun x => (4 : ℕ).testBit x.val)
  | 8 => (3,fun x => (0 : ℕ).testBit x.val)
  | 9 => (3,fun x => (1 : ℕ).testBit x.val)
  | 10 => (3,fun x => (2 : ℕ).testBit x.val)
  | 11 => (4,fun x => (0 : ℕ).testBit x.val)
  | 12 => (4,fun x => (2 : ℕ).testBit x.val)
  | 13 => (4,fun x => (4 : ℕ).testBit x.val)
  | 14 => (4,fun x => (6 : ℕ).testBit x.val)
  | _ => (0,fun _ => false)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def ends (k : Fin 40) : Fin 15 × Fin 15 :=
  match k.val with
  | 0 => (3,0)
  | 1 => (3,1)
  | 2 => (3,2)
  | 3 => (4,0)
  | 4 => (4,1)
  | 5 => (4,2)
  | 6 => (5,3)
  | 7 => (5,4)
  | 8 => (6,3)
  | 9 => (6,4)
  | 10 => (7,3)
  | 11 => (7,4)
  | 12 => (8,5)
  | 13 => (8,6)
  | 14 => (8,7)
  | 15 => (9,5)
  | 16 => (9,7)
  | 17 => (10,5)
  | 18 => (10,6)
  | 19 => (10,7)
  | 20 => (11,0)
  | 21 => (11,1)
  | 22 => (11,2)
  | 23 => (11,8)
  | 24 => (11,9)
  | 25 => (11,10)
  | 26 => (12,0)
  | 27 => (12,1)
  | 28 => (12,2)
  | 29 => (12,8)
  | 30 => (12,9)
  | 31 => (13,0)
  | 32 => (13,1)
  | 33 => (13,8)
  | 34 => (13,9)
  | 35 => (13,10)
  | 36 => (14,0)
  | 37 => (14,1)
  | 38 => (14,8)
  | 39 => (14,9)
  | _ => (0,0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def cycle (i : Fin 5) : Fin 15 :=
  match i.val with
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | 3 => 8
  | 4 => 11
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def table : Table t 15 40 where
  slot := slot
  ends := ends
  cycle := cycle
  valid := by decide +kernel
  injective := by decide +kernel
  covers := by decide +kernel
  ordered_inj := by decide +kernel
  ordered_covers := by decide +kernel
  cycle_spec := by decide +kernel
end NativeCutTemplate.C012

namespace NativeCutTemplate.C013
open ThreeExceptions FiniteCutTemplate
def t : Fin 3 → Fin 5 := fun x => if x=0 then 0 else if x=1 then 1 else 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def slot (a : Fin 16) : Regular :=
  match a.val with
  | 0 => (0,fun x => (0 : ℕ).testBit x.val)
  | 1 => (0,fun x => (1 : ℕ).testBit x.val)
  | 2 => (0,fun x => (4 : ℕ).testBit x.val)
  | 3 => (1,fun x => (0 : ℕ).testBit x.val)
  | 4 => (1,fun x => (2 : ℕ).testBit x.val)
  | 5 => (1,fun x => (4 : ℕ).testBit x.val)
  | 6 => (1,fun x => (6 : ℕ).testBit x.val)
  | 7 => (2,fun x => (0 : ℕ).testBit x.val)
  | 8 => (2,fun x => (1 : ℕ).testBit x.val)
  | 9 => (3,fun x => (0 : ℕ).testBit x.val)
  | 10 => (3,fun x => (1 : ℕ).testBit x.val)
  | 11 => (3,fun x => (2 : ℕ).testBit x.val)
  | 12 => (3,fun x => (4 : ℕ).testBit x.val)
  | 13 => (3,fun x => (6 : ℕ).testBit x.val)
  | 14 => (4,fun x => (0 : ℕ).testBit x.val)
  | 15 => (4,fun x => (2 : ℕ).testBit x.val)
  | _ => (0,fun _ => false)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def ends (k : Fin 41) : Fin 16 × Fin 16 :=
  match k.val with
  | 0 => (3,0)
  | 1 => (3,1)
  | 2 => (3,2)
  | 3 => (4,0)
  | 4 => (4,1)
  | 5 => (4,2)
  | 6 => (5,0)
  | 7 => (5,1)
  | 8 => (6,0)
  | 9 => (6,1)
  | 10 => (7,3)
  | 11 => (7,4)
  | 12 => (7,5)
  | 13 => (7,6)
  | 14 => (8,3)
  | 15 => (8,4)
  | 16 => (8,5)
  | 17 => (8,6)
  | 18 => (9,7)
  | 19 => (9,8)
  | 20 => (10,7)
  | 21 => (11,7)
  | 22 => (11,8)
  | 23 => (12,7)
  | 24 => (12,8)
  | 25 => (13,7)
  | 26 => (13,8)
  | 27 => (14,0)
  | 28 => (14,1)
  | 29 => (14,2)
  | 30 => (14,9)
  | 31 => (14,10)
  | 32 => (14,11)
  | 33 => (14,12)
  | 34 => (14,13)
  | 35 => (15,0)
  | 36 => (15,1)
  | 37 => (15,2)
  | 38 => (15,9)
  | 39 => (15,10)
  | 40 => (15,12)
  | _ => (0,0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def cycle (i : Fin 5) : Fin 16 :=
  match i.val with
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 14
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def table : Table t 16 41 where
  slot := slot
  ends := ends
  cycle := cycle
  valid := by decide +kernel
  injective := by decide +kernel
  covers := by decide +kernel
  ordered_inj := by decide +kernel
  ordered_covers := by decide +kernel
  cycle_spec := by decide +kernel
end NativeCutTemplate.C013

namespace NativeCutTemplate.C014
open ThreeExceptions FiniteCutTemplate
def t : Fin 3 → Fin 5 := fun x => if x=0 then 0 else if x=1 then 1 else 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def slot (a : Fin 16) : Regular :=
  match a.val with
  | 0 => (0,fun x => (0 : ℕ).testBit x.val)
  | 1 => (0,fun x => (1 : ℕ).testBit x.val)
  | 2 => (1,fun x => (0 : ℕ).testBit x.val)
  | 3 => (1,fun x => (2 : ℕ).testBit x.val)
  | 4 => (1,fun x => (4 : ℕ).testBit x.val)
  | 5 => (1,fun x => (6 : ℕ).testBit x.val)
  | 6 => (2,fun x => (0 : ℕ).testBit x.val)
  | 7 => (2,fun x => (1 : ℕ).testBit x.val)
  | 8 => (2,fun x => (4 : ℕ).testBit x.val)
  | 9 => (3,fun x => (0 : ℕ).testBit x.val)
  | 10 => (3,fun x => (1 : ℕ).testBit x.val)
  | 11 => (3,fun x => (2 : ℕ).testBit x.val)
  | 12 => (4,fun x => (0 : ℕ).testBit x.val)
  | 13 => (4,fun x => (2 : ℕ).testBit x.val)
  | 14 => (4,fun x => (4 : ℕ).testBit x.val)
  | 15 => (4,fun x => (6 : ℕ).testBit x.val)
  | _ => (0,fun _ => false)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def ends (k : Fin 44) : Fin 16 × Fin 16 :=
  match k.val with
  | 0 => (2,0)
  | 1 => (2,1)
  | 2 => (3,0)
  | 3 => (3,1)
  | 4 => (4,0)
  | 5 => (4,1)
  | 6 => (5,0)
  | 7 => (5,1)
  | 8 => (6,2)
  | 9 => (6,3)
  | 10 => (6,4)
  | 11 => (6,5)
  | 12 => (7,2)
  | 13 => (7,3)
  | 14 => (7,4)
  | 15 => (7,5)
  | 16 => (8,2)
  | 17 => (8,3)
  | 18 => (9,6)
  | 19 => (9,7)
  | 20 => (9,8)
  | 21 => (10,6)
  | 22 => (10,8)
  | 23 => (11,6)
  | 24 => (11,7)
  | 25 => (11,8)
  | 26 => (12,0)
  | 27 => (12,1)
  | 28 => (12,9)
  | 29 => (12,10)
  | 30 => (12,11)
  | 31 => (13,0)
  | 32 => (13,1)
  | 33 => (13,9)
  | 34 => (13,10)
  | 35 => (14,0)
  | 36 => (14,1)
  | 37 => (14,9)
  | 38 => (14,10)
  | 39 => (14,11)
  | 40 => (15,0)
  | 41 => (15,1)
  | 42 => (15,9)
  | 43 => (15,10)
  | _ => (0,0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def cycle (i : Fin 5) : Fin 16 :=
  match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 9
  | 4 => 14
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def table : Table t 16 44 where
  slot := slot
  ends := ends
  cycle := cycle
  valid := by decide +kernel
  injective := by decide +kernel
  covers := by decide +kernel
  ordered_inj := by decide +kernel
  ordered_covers := by decide +kernel
  cycle_spec := by decide +kernel
end NativeCutTemplate.C014

namespace NativeCutTemplate.C022
open ThreeExceptions FiniteCutTemplate
def t : Fin 3 → Fin 5 := fun x => if x=0 then 0 else if x=1 then 2 else 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def slot (a : Fin 17) : Regular :=
  match a.val with
  | 0 => (0,fun x => (0 : ℕ).testBit x.val)
  | 1 => (0,fun x => (1 : ℕ).testBit x.val)
  | 2 => (0,fun x => (2 : ℕ).testBit x.val)
  | 3 => (0,fun x => (4 : ℕ).testBit x.val)
  | 4 => (0,fun x => (6 : ℕ).testBit x.val)
  | 5 => (1,fun x => (0 : ℕ).testBit x.val)
  | 6 => (2,fun x => (0 : ℕ).testBit x.val)
  | 7 => (2,fun x => (1 : ℕ).testBit x.val)
  | 8 => (2,fun x => (2 : ℕ).testBit x.val)
  | 9 => (2,fun x => (4 : ℕ).testBit x.val)
  | 10 => (2,fun x => (6 : ℕ).testBit x.val)
  | 11 => (3,fun x => (0 : ℕ).testBit x.val)
  | 12 => (3,fun x => (1 : ℕ).testBit x.val)
  | 13 => (4,fun x => (0 : ℕ).testBit x.val)
  | 14 => (4,fun x => (2 : ℕ).testBit x.val)
  | 15 => (4,fun x => (4 : ℕ).testBit x.val)
  | 16 => (4,fun x => (6 : ℕ).testBit x.val)
  | _ => (0,fun _ => false)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def ends (k : Fin 40) : Fin 17 × Fin 17 :=
  match k.val with
  | 0 => (5,0)
  | 1 => (5,1)
  | 2 => (5,2)
  | 3 => (5,3)
  | 4 => (5,4)
  | 5 => (6,5)
  | 6 => (7,5)
  | 7 => (8,5)
  | 8 => (9,5)
  | 9 => (10,5)
  | 10 => (11,6)
  | 11 => (11,7)
  | 12 => (11,8)
  | 13 => (11,9)
  | 14 => (11,10)
  | 15 => (12,6)
  | 16 => (12,8)
  | 17 => (12,9)
  | 18 => (12,10)
  | 19 => (13,0)
  | 20 => (13,1)
  | 21 => (13,2)
  | 22 => (13,3)
  | 23 => (13,4)
  | 24 => (13,11)
  | 25 => (13,12)
  | 26 => (14,0)
  | 27 => (14,1)
  | 28 => (14,3)
  | 29 => (14,11)
  | 30 => (14,12)
  | 31 => (15,0)
  | 32 => (15,1)
  | 33 => (15,2)
  | 34 => (15,11)
  | 35 => (15,12)
  | 36 => (16,0)
  | 37 => (16,1)
  | 38 => (16,11)
  | 39 => (16,12)
  | _ => (0,0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def cycle (i : Fin 5) : Fin 17 :=
  match i.val with
  | 0 => 1
  | 1 => 5
  | 2 => 10
  | 3 => 11
  | 4 => 13
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def table : Table t 17 40 where
  slot := slot
  ends := ends
  cycle := cycle
  valid := by decide +kernel
  injective := by decide +kernel
  covers := by decide +kernel
  ordered_inj := by decide +kernel
  ordered_covers := by decide +kernel
  cycle_spec := by decide +kernel
end NativeCutTemplate.C022

namespace NativeCutTemplate.C023
open ThreeExceptions FiniteCutTemplate
def t : Fin 3 → Fin 5 := fun x => if x=0 then 0 else if x=1 then 2 else 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def slot (a : Fin 15) : Regular :=
  match a.val with
  | 0 => (0,fun x => (0 : ℕ).testBit x.val)
  | 1 => (0,fun x => (1 : ℕ).testBit x.val)
  | 2 => (0,fun x => (2 : ℕ).testBit x.val)
  | 3 => (0,fun x => (4 : ℕ).testBit x.val)
  | 4 => (0,fun x => (6 : ℕ).testBit x.val)
  | 5 => (1,fun x => (0 : ℕ).testBit x.val)
  | 6 => (1,fun x => (4 : ℕ).testBit x.val)
  | 7 => (2,fun x => (0 : ℕ).testBit x.val)
  | 8 => (2,fun x => (1 : ℕ).testBit x.val)
  | 9 => (2,fun x => (2 : ℕ).testBit x.val)
  | 10 => (3,fun x => (0 : ℕ).testBit x.val)
  | 11 => (3,fun x => (1 : ℕ).testBit x.val)
  | 12 => (3,fun x => (4 : ℕ).testBit x.val)
  | 13 => (4,fun x => (0 : ℕ).testBit x.val)
  | 14 => (4,fun x => (2 : ℕ).testBit x.val)
  | _ => (0,fun _ => false)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def ends (k : Fin 36) : Fin 15 × Fin 15 :=
  match k.val with
  | 0 => (5,0)
  | 1 => (5,1)
  | 2 => (5,2)
  | 3 => (5,3)
  | 4 => (5,4)
  | 5 => (6,0)
  | 6 => (6,1)
  | 7 => (6,2)
  | 8 => (7,5)
  | 9 => (7,6)
  | 10 => (8,5)
  | 11 => (8,6)
  | 12 => (9,5)
  | 13 => (9,6)
  | 14 => (10,7)
  | 15 => (10,8)
  | 16 => (10,9)
  | 17 => (11,7)
  | 18 => (11,9)
  | 19 => (12,7)
  | 20 => (12,8)
  | 21 => (12,9)
  | 22 => (13,0)
  | 23 => (13,1)
  | 24 => (13,2)
  | 25 => (13,3)
  | 26 => (13,4)
  | 27 => (13,10)
  | 28 => (13,11)
  | 29 => (13,12)
  | 30 => (14,0)
  | 31 => (14,1)
  | 32 => (14,3)
  | 33 => (14,10)
  | 34 => (14,11)
  | 35 => (14,12)
  | _ => (0,0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def cycle (i : Fin 5) : Fin 15 :=
  match i.val with
  | 0 => 1
  | 1 => 5
  | 2 => 9
  | 3 => 12
  | 4 => 13
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def table : Table t 15 36 where
  slot := slot
  ends := ends
  cycle := cycle
  valid := by decide +kernel
  injective := by decide +kernel
  covers := by decide +kernel
  ordered_inj := by decide +kernel
  ordered_covers := by decide +kernel
  cycle_spec := by decide +kernel
end NativeCutTemplate.C023

-- Mass

namespace FiniteMass
open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

noncomputable def mass (f : X → Y) (w : X → ℤ) (y : Y) : ℤ := by
  classical
  exact ∑ x, if f x=y then w x else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem nonneg (f : X → Y) (w : X → ℤ) (positive : ∀ x, 0  ≤  w x) (y : Y) :
    0  ≤  mass f w y := by
  classical
  unfold mass
  exact sum_nonneg fun x _ => by split <;> first | exact positive x | exact le_rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem push (f : X → Y) (w : X → ℤ) (g : Y → ℤ) :
    (∑ y, mass f w y * g y) = ∑ x, w x * g (f x) := by
  classical
  unfold mass
  simp_rw [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem total (f : X → Y) (w : X → ℤ) :
    (∑ y, mass f w y) = ∑ x, w x := by
  simpa using push f w (fun _ => 1)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem comp (f : X → Y) (g : Y → Z) (w : X → ℤ) (z : Z) :
    mass g (mass f w) z = mass (g ∘ f) w z := by
  classical
  simpa [mass, Function.comp_def, mul_ite] using push f w (fun y => if g y=z then 1 else 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem singleton (f : X → Y) (w : X → ℤ) (y : Y) (x : X)
    (fiber : ∀ a, f a=y ↔ a=x) : mass f w y = w x := by
  classical
  simp [mass, fiber]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem fst (w : X × Y → ℤ) (x : X) : mass Prod.fst w x = ∑ y, w (x,y) := by
  classical
  unfold mass
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro y _
  simp

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem row (f : X → Y) (w : X × X → ℤ) (y : Y) :
    (∑ z : Y, mass (Prod.map f f) w (y,z)) =
      mass f (fun x => ∑ z, w (x,z)) y := by
  rw [← fst]
  rw [comp]
  have h : (Prod.fst ∘ Prod.map f f) = f ∘ Prod.fst := rfl
  rw [h, ← comp]
  congr 2
  funext x
  exact fst w x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem symmetric (f : X → Y) (w : X × X → ℤ)
    (sym : ∀ a b, w (a,b)=w (b,a)) (i j : Y) :
    mass (Prod.map f f) w (i,j) = mass (Prod.map f f) w (j,i) := by
  classical
  unfold mass
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp only [Prod.map_apply, Prod.mk.injEq]
  rw [sym b a]
  simp only [and_comm]

end FiniteMass

-- MassMore

namespace FiniteMass
open Finset
variable {X Y : Type*} [Fintype X] [Fintype Y]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem mono (f : X → Y) (u v : X → ℤ) (h : ∀ x, u x  ≤  v x) (y : Y) :
    mass f u y  ≤  mass f v y := by
  classical
  unfold mass
  apply sum_le_sum
  intro x _
  by_cases hx : f x=y <;> simp [hx,h x]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem fiber_const (f : X → Y) (w : X → ℤ) (y : Y) (c : ℤ)
    (h : ∀ x, f x=y → w x=c) : mass f w y = c * mass f (fun _ => 1) y := by
  classical
  unfold mass
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : f x=y
  · simp [hx,h x hx]
  · simp [hx]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem zero_of (f : X → Y) (w : X → ℤ) (y : Y)
    (h : ∀ x, f x=y → w x=0) : mass f w y=0 := by
  rw [fiber_const f w y 0 h,zero_mul]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem hit (f : X → Y) (x : X) : 1  ≤  mass f (fun _ => 1) (f x) := by
  classical
  unfold mass
  have h := single_le_sum (s:=univ) (f:=fun a : X => if f a=f x then (1:ℤ) else 0)
    (fun a _ => by split <;> norm_num) (mem_univ x)
  simpa using h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem pair_right (f : X → Y) (w : X × X → ℤ) (i j : Y) (z : X)
    (fiber : ∀ x, f x=j ↔ x=z) :
    mass (Prod.map f f) w (i,j) = mass f (fun x => w (x,z)) i := by
  classical
  unfold mass
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  simp only [Prod.map_apply,Prod.mk.injEq,fiber]
  by_cases h : f x=i <;> simp [h]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem pair_push (f : X → Y) (w : X × X → ℤ) (F : Y → Y → ℤ) :
    (∑ i, ∑ j, mass (Prod.map f f) w (i,j)*F i j) =
      ∑ x, ∑ y, w (x,y)*F (f x) (f y) := by
  simpa only [Fintype.sum_prod_type,Prod.map_apply] using push (Prod.map f f) w (fun p => F p.1 p.2)

end FiniteMass

-- MassExtra
namespace FiniteMass
open Finset
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem mono_on (f : X → Y) (u v : X → ℤ) (y : Y)
    (h : ∀x, f x=y → u x ≤ v x) : mass f u y ≤ mass f v y := by
  unfold mass
  apply sum_le_sum
  intro x _
  by_cases hx : f x=y
  · simpa only [if_pos hx] using h x hx
  · simp [hx]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem add (f : X → Y) (u v : X → ℤ) (y : Y) :
    mass f (fun x => u x+v x) y=mass f u y+mass f v y := by
  unfold mass
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  by_cases h : f x=y <;> simp [h]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem sub (f : X → Y) (u v : X → ℤ) (y : Y) :
    mass f (fun x => u x-v x) y=mass f u y-mass f v y := by
  unfold mass
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  by_cases h : f x=y <;> simp [h]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem delta (f : X → Y) (z : X) (c : ℤ) (y : Y) :
    mass f (fun x => if x=z then c else 0) y=if f z=y then c else 0 := by
  unfold mass
  rw [sum_eq_single z]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem delta_left (f : X → Y) (w : X → ℤ) (z : X) (i j : Y) :
    mass (Prod.map f f) (fun p => if p.1=z then w p.2 else 0) (i,j)=
      if f z=i then mass f w j else 0 := by
  unfold mass
  rw [Fintype.sum_prod_type,sum_eq_single z]
  · by_cases h : f z=i
    · simp only [if_pos h]
      apply sum_congr rfl
      intro y _
      by_cases hy : f y=j <;> simp [h,hy]
    · simp [h]
  · intro x _ hx
    apply sum_eq_zero
    intro y _
    simp [hx]
  · simp

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem delta_right (f : X → Y) (w : X → ℤ) (z : X) (i j : Y) :
    mass (Prod.map f f) (fun p => if p.2=z then w p.1 else 0) (i,j)=
      if f z=j then mass f w i else 0 := by
  unfold mass
  rw [Fintype.sum_prod_type,sum_comm,sum_eq_single z]
  · by_cases h : f z=j
    · simp only [if_pos h]
      apply sum_congr rfl
      intro x _
      by_cases hx : f x=i <;> simp [h,hx]
    · simp [h]
  · intro y _ hy
    apply sum_eq_zero
    intro x _
    simp [hy]
  · simp

end FiniteMass

-- MatrixDecomp

namespace CutMatrix
open Finset

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem reindex_support {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (inj : Function.Injective f) (w : Y → ℤ)
    (support : ∀ y, (¬∃ x, f x=y) → w y=0) :
    (∑ x, w (f x)) = ∑ y, w y := by
  classical
  calc
    _ = ∑ y ∈ univ.image f, w y := (sum_image inj.injOn).symm
    _ = _ := by
      apply sum_subset (subset_univ _)
      intro y _ hy
      apply support y
      rintro ⟨x,rfl⟩
      exact hy (mem_image_of_mem f (mem_univ x))

def orient {A E : Type*} (ends : E → A × A) (o : E × Bool) : A × A :=
  if o.2 then ((ends o.1).2,(ends o.1).1) else ends o.1

variable {A E : Type*} [Fintype A] [Fintype E]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem core_sum (ends : E → A × A) (inj : Function.Injective (orient ends))
    (R F : (A ⊕ Fin 3) → (A ⊕ Fin 3) → ℤ)
    (sym : ∀ a b, R a b=R b a) (fsym : ∀ a b, F a b=F b a)
    (support : ∀ a b, (¬∃ o, orient ends o=(a,b)) → R (.inl a) (.inl b)=0) :
    (∑ a : A, ∑ b : A, R (.inl a) (.inl b)*F (.inl a) (.inl b)) =
      2 * ∑ k : E, R (.inl (ends k).1) (.inl (ends k).2)*
        F (.inl (ends k).1) (.inl (ends k).2) := by
  classical
  let w (p : A × A) := R (.inl p.1) (.inl p.2)*F (.inl p.1) (.inl p.2)
  have reindex := reindex_support (orient ends) inj w
    (fun p hp => by simp only [w,support p.1 p.2 hp,zero_mul])
  have point (k : E) : (∑ b : Bool, w (orient ends (k,b))) =
      2*(R (.inl (ends k).1) (.inl (ends k).2)*F (.inl (ends k).1) (.inl (ends k).2)) := by
    rw [Fintype.sum_bool]
    simp [w,orient]
    rw [sym (.inl (ends k).2) (.inl (ends k).1),fsym (.inl (ends k).2) (.inl (ends k).1)]
    ring
  rw [Fintype.sum_prod_type] at reindex
  simp_rw [point] at reindex
  rw [←mul_sum] at reindex
  simpa only [w,Fintype.sum_prod_type] using reindex.symm


set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem decompose (ends : E → A × A) (inj : Function.Injective (orient ends))
    (R F : (A ⊕ Fin 3) → (A ⊕ Fin 3) → ℤ) (n : A → ℤ)
    (mask : A → Fin 3 → Bool)
    (sym : ∀ a b, R a b=R b a) (fsym : ∀ a b, F a b=F b a)
    (support : ∀ a b, (¬∃ o, orient ends o=(a,b)) → R (.inl a) (.inl b)=0)
    (boundary : ∀ a x, R (.inl a) (.inr x)=if mask a x then n a else 0)
    (inner : ∀ x y, R (.inr x) (.inr y)=if x≠y ∧ (x=0 ∨ y=0) then 1 else 0) :
    (∑ a, ∑ b, R a b*F a b) = 2 *
      ((∑ k : E, R (.inl (ends k).1) (.inl (ends k).2)*F (.inl (ends k).1) (.inl (ends k).2)) +
        (∑ a : A, ∑ x : Fin 3, if mask a x then n a*F (.inl a) (.inr x) else 0) +
        F (.inr 0) (.inr 1)+F (.inr 0) (.inr 2)) := by
  classical
  have core := core_sum ends inj R F sym fsym support
  have forward : (∑ a : A, ∑ x : Fin 3, R (.inl a) (.inr x)*F (.inl a) (.inr x)) =
      ∑ a : A, ∑ x : Fin 3, if mask a x then n a*F (.inl a) (.inr x) else 0 := by
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro x _
    rw [boundary]
    by_cases h : mask a x=true <;> simp [h]
  have backward : (∑ x : Fin 3, ∑ a : A, R (.inr x) (.inl a)*F (.inr x) (.inl a)) =
      ∑ a : A, ∑ x : Fin 3, if mask a x then n a*F (.inl a) (.inr x) else 0 := by
    rw [sum_comm]
    calc
      _ = ∑ a : A, ∑ x : Fin 3, R (.inl a) (.inr x)*F (.inl a) (.inr x) := by
        apply sum_congr rfl
        intro a _
        apply sum_congr rfl
        intro x _
        rw [sym (.inr x) (.inl a),fsym (.inr x) (.inl a)]
      _ = _ := forward
  have inside : (∑ x : Fin 3, ∑ y : Fin 3, R (.inr x) (.inr y)*F (.inr x) (.inr y)) =
      2*(F (.inr 0) (.inr 1)+F (.inr 0) (.inr 2)) := by
    simp only [inner]
    norm_num [Fin.sum_univ_succ]
    simp only [show (0 : Fin 3) ≠ 2 by decide,if_false]
    rw [fsym (.inr 1) (.inr 0),fsym (.inr 2) (.inr 0)]
    ring
  simp_rw [Fintype.sum_sum_type,sum_add_distrib]
  rw [core,forward,backward,inside]
  ring

end CutMatrix

-- Compressed

namespace FiniteCutTemplate
open ThreeExceptions
variable {n e : ℕ} {t : Fin 3 → Fin 5}

def embed (T : Table t n e) : Fin n ⊕ Fin 3 → Slot := Sum.map T.slot id

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem embed_injective (T : Table t n e) : Function.Injective (embed T) := by
  intro a b h
  cases a <;> cases b <;> simp_all [embed,T.injective.eq_iff]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem embed_covers (T : Table t n e) (s : Slot)
    (h : ∀ u, s=.inl u → Valid t u) : ∃a, embed T a=s := by
  cases s with
  | inl u => obtain ⟨a,ha⟩ := T.covers u (h u rfl); exact ⟨.inl a,congrArg Sum.inl ha⟩
  | inr x => exact ⟨.inr x,rfl⟩

noncomputable def compress (T : Table t n e) (s : Slot)
    (h : ∀ u, s=.inl u → Valid t u) : Fin n ⊕ Fin 3 := (embed_covers T s h).choose

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem compress_spec (T : Table t n e) (s : Slot)
    (h : ∀ u, s=.inl u → Valid t u) : embed T (compress T s h)=s :=
  (embed_covers T s h).choose_spec

variable {V : Type*}

structure Representation (G : SimpleGraph V) (ex : Fin 3 → V) (v : Fin 5 → V)
    (T : Table t n e) where
  label : V → Fin n ⊕ Fin 3
  singleton : ∀ a x, label a=.inr x ↔ a=ex x
  hom : ∀ a b, G.Adj a b → Allowed t (embed T (label a)) (embed T (label b))
  boundary : ∀ a u, label a=.inl u → ∀ x, G.Adj a (ex x) ↔ (T.slot u).2 x=true
  cycle_label : ∀ i, label (v i)=.inl (T.cycle i)
  cycle_adj : ∀ a u, label a=.inl u → ∀ i, G.Adj a (v i) ↔ Near (T.slot u).1 i
  single : ∀ x i, G.Adj (ex x) (v i) ↔ i=t x
  exedge : ∀ x y, G.Adj (ex x) (ex y) ↔ x≠y ∧ (x=0 ∨ y=0)

noncomputable def represent (G : SimpleGraph V) (ex : Fin 3 → V)
    (inj : Function.Injective ex) (g : V → Fin 5)
    (v : Fin 5 → V) (T : Table t n e)
    (tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (exedge : ∀ x y, G.Adj (ex x) (ex y) ↔ x≠y ∧ (x=0 ∨ y=0))
    (single : ∀ x i, G.Adj (ex x) (v i) ↔ i=t x)
    (profile : ∀ a, (¬∃ x,a=ex x) → ∀ i, G.Adj a (v i) ↔ Near (g a) i)
    (maps : ∀ a, (¬∃ x,a=ex x) → ∀ b, (¬∃ x,b=ex x) → G.Adj a b → Near (g a) (g b))
    (cyc : ∀ i, G.Adj (v i) (v (i+1))) : Representation G ex v T := by
  classical
  let L (a : V) := compress T (ThreeExceptions.label G ex g a)
    (fun u hu => label_valid G ex g v t tri exedge single profile a u hu)
  have eq (a : V) : embed T (L a)=ThreeExceptions.label G ex g a := compress_spec _ _ _
  have regular (a : V) (u : Fin n) (h : L a=.inl u) :
      ThreeExceptions.label G ex g a=.inl (T.slot u) := by rw [←eq a,h]; rfl
  refine ⟨L,?_,?_,?_,?_,?_,single,exedge⟩
  · intro a x
    rw [←label_exception_iff G ex inj g a x,←eq a]
    change L a=.inr x ↔ embed T (L a)=embed T (.inr x)
    exact (embed_injective T).eq_iff.symm
  · intro a b hab
    rw [eq a,eq b]
    exact label_hom G ex inj g v t tri exedge single profile maps a b hab
  · intro a u ha x
    have hr := label_regular G ex g a (T.slot u) (regular a u ha)
    exact ⟨fun h => (hr.2.2 x).mp h.symm,fun h => ((hr.2.2 x).mpr h).symm⟩
  · intro i
    apply embed_injective T
    rw [eq,show embed T (.inl (T.cycle i))=.inl (T.slot (T.cycle i)) from rfl,T.cycle_spec]
    have hc := cycle_regular G ex v t cyc single i
    have hp := cycle_profile G ex g v t cyc single profile i
    simp only [ThreeExceptions.label,dif_neg hc,hp]
    apply congrArg Sum.inl
    apply Prod.ext
    · rfl
    · funext x
      simp only [single]
  · intro a u ha i
    have hr := label_regular G ex g a (T.slot u) (regular a u ha)
    simpa only [hr.2.1] using profile a hr.1 i

end FiniteCutTemplate

-- GraphMass

namespace GraphMass
open Finset ThreeExceptions FiniteCutTemplate
variable {V : Type*} [Fintype V] {n e : ℕ} {t : Fin 3 → Fin 5}
variable {G : SimpleGraph V} {ex : Fin 3 → V} {v : Fin 5 → V} {T : Table t n e}

noncomputable def W (G : SimpleGraph V) (p : V × V) : ℤ := by
  classical
  exact if G.Adj p.1 p.2 then 1 else 0
noncomputable def deg (G : SimpleGraph V) (a : V) : ℤ := ∑ b, W G (a,b)
noncomputable def N (S : Representation G ex v T) (a : Fin n) : ℤ :=
  FiniteMass.mass S.label (fun _ => 1) (.inl a)
noncomputable def R (S : Representation G ex v T) (a b : Fin n ⊕ Fin 3) : ℤ :=
  FiniteMass.mass (Prod.map S.label S.label) (W G) (a,b)
noncomputable def E (S : Representation G ex v T) (k : Fin e) : ℤ :=
  R S (.inl (T.ends k).1) (.inl (T.ends k).2)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem W_sym (G : SimpleGraph V) (a b : V) : W G (a,b)=W G (b,a) := by
  classical
  simp only [W,G.adj_comm]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem R_sym (S : Representation G ex v T) (a b) : R S a b=R S b a :=
  FiniteMass.symmetric S.label (W G) (W_sym G) a b

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem R_nonneg (S : Representation G ex v T) (a b) : 0 ≤ R S a b := by
  apply FiniteMass.nonneg
  intro p
  unfold W
  split <;> norm_num

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem N_nonneg (S : Representation G ex v T) (a) : 0 ≤ N S a :=
  FiniteMass.nonneg S.label (fun _ => 1) (fun _ => by norm_num) (.inl a)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem R_support (S : Representation G ex v T) (a b : Fin n)
    (h : ¬∃o, CutMatrix.orient T.ends o=(a,b)) : R S (.inl a) (.inl b)=0 := by
  apply FiniteMass.zero_of
  intro p hp
  have ha : S.label p.1=.inl a := congrArg Prod.fst hp
  have hb : S.label p.2=.inl b := congrArg Prod.snd hp
  unfold W
  split
  next hab =>
    have hh := S.hom _ _ hab
    rw [ha,hb] at hh
    have hc := (T.ordered_covers a b).mp ⟨hh.2.2.1,hh.2.2.2⟩
    exact False.elim (h hc)
  next => rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem R_boundary (S : Representation G ex v T) (a : Fin n) (x : Fin 3) :
    R S (.inl a) (.inr x)=if (T.slot a).2 x then N S a else 0 := by
  classical
  rw [R,FiniteMass.pair_right S.label (W G) (.inl a) (.inr x) (ex x) (fun y => S.singleton y x)]
  have hc : ∀y, S.label y=.inl a → W G (y,ex x)=(if (T.slot a).2 x then 1 else 0) := by
    intro y hy
    simp only [W,S.boundary y a hy x]
  rw [FiniteMass.fiber_const S.label _ (.inl a) _ hc]
  by_cases h : (T.slot a).2 x=true <;> simp [h,N]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem R_inner (S : Representation G ex v T) (x y : Fin 3) :
    R S (.inr x) (.inr y)=if x≠y ∧ (x=0∨y=0) then 1 else 0 := by
  classical
  rw [R,FiniteMass.pair_right S.label (W G) (.inr x) (.inr y) (ex y) (fun a => S.singleton a y),
    FiniteMass.singleton S.label _ (.inr x) (ex x) (fun a => S.singleton a x)]
  simp only [W,S.exedge]

noncomputable def half (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ)
    (F : (Fin n ⊕ Fin 3) → (Fin n ⊕ Fin 3) → ℤ) : ℤ :=
  (∑ k, E k*F (.inl (T.ends k).1) (.inl (T.ends k).2)) +
  (∑ a, ∑ x, if (T.slot a).2 x then N a*F (.inl a) (.inr x) else 0) +
  F (.inr 0) (.inr 1)+F (.inr 0) (.inr 2)

noncomputable def edgeCount (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) : ℤ :=
  half T N E (fun _ _ => 1)

noncomputable def regularDegree (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ)
    (a : Fin n) : ℤ := by
  classical
  exact (∑k, ((if (T.ends k).1=a then E k else 0)+(if (T.ends k).2=a then E k else 0))) +
    ∑x, if (T.slot a).2 x then N a else 0

noncomputable def exceptionDegree (T : Table t n e) (N : Fin n → ℤ) (x : Fin 3) : ℤ := by
  classical
  exact (if x=0 then 2 else 1)+(∑a, if (T.slot a).2 x then N a else 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem statistic (S : Representation G ex v T)
    (F : (Fin n ⊕ Fin 3) → (Fin n ⊕ Fin 3) → ℤ)
    (fsym : ∀a b,F a b=F b a) :
    (∑a,∑b, W G (a,b)*F (S.label a) (S.label b)) =
      2*half T (N S) (E S) F := by
  rw [←FiniteMass.pair_push S.label (W G) F]
  exact CutMatrix.decompose T.ends T.ordered_inj (R S) F (N S) (fun a => (T.slot a).2)
    (R_sym S) fsym (R_support S) (R_boundary S) (R_inner S)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem vertex_total (S : Representation G ex v T) :
    (∑a, N S a)+3=Fintype.card V := by
  classical
  have ht := FiniteMass.total S.label (fun _ => (1:ℤ))
  simp only [Fintype.sum_sum_type] at ht
  have one (x : Fin 3) : FiniteMass.mass S.label (fun _ => (1:ℤ)) (.inr x)=1 :=
    FiniteMass.singleton S.label (fun _ => 1) _ (ex x) (fun a => S.singleton a x)
  simpa only [N,one,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    Nat.cast_ofNat] using ht

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem core_row (S : Representation G ex v T) (a : Fin n) :
    (∑b : Fin n, R S (.inl a) (.inl b)) =
      ∑k, ((if (T.ends k).1=a then E S k else 0)+(if (T.ends k).2=a then E S k else 0)) := by
  classical
  let w (p : Fin n × Fin n) : ℤ := if p.1=a then R S (.inl p.1) (.inl p.2) else 0
  have h := CutMatrix.reindex_support (CutMatrix.orient T.ends) T.ordered_inj w
    (fun p hp => by simp only [w,R_support S p.1 p.2 hp,ite_self])
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at h
  have point (k : Fin e) : (∑b : Bool, w (CutMatrix.orient T.ends (k,b))) =
      (if (T.ends k).1=a then E S k else 0)+(if (T.ends k).2=a then E S k else 0) := by
    rw [Fintype.sum_bool]
    simp [w,CutMatrix.orient,E,R_sym S (.inl (T.ends k).2) (.inl (T.ends k).1),add_comm]
  simp_rw [point] at h
  simpa [w] using h.symm

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem regular_degree (S : Representation G ex v T) (a : Fin n) :
    regularDegree T (N S) (E S) a = FiniteMass.mass S.label (deg G) (.inl a) := by
  have row := FiniteMass.row S.label (W G) (.inl a)
  simp only [Fintype.sum_sum_type] at row
  change (∑ b : Fin n,R S (.inl a) (.inl b))+
    (∑x : Fin 3,R S (.inl a) (.inr x))=FiniteMass.mass S.label (deg G) (.inl a) at row
  simp_rw [R_boundary S] at row
  unfold regularDegree
  rw [←core_row S a]
  exact row

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem path_degree : ∀x : Fin 3,
    (∑y : Fin 3,if x≠y∧(x=0∨y=0) then (1:ℤ) else 0)=if x=0 then 2 else 1 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem exception_degree (S : Representation G ex v T) (x : Fin 3) :
    exceptionDegree T (N S) x=deg G (ex x) := by
  have row := FiniteMass.row S.label (W G) (.inr x)
  rw [FiniteMass.singleton S.label _ (.inr x) (ex x) (fun a => S.singleton a x)] at row
  simp only [Fintype.sum_sum_type] at row
  change (∑a:Fin n,R S (.inr x) (.inl a))+(∑y:Fin 3,R S (.inr x) (.inr y))=_ at row
  have hinner : (∑y:Fin 3,R S (.inr x) (.inr y))=if x=0 then 2 else 1 := by
    simp_rw [R_inner S]
    exact path_degree x
  rw [hinner] at row
  simpa only [exceptionDegree,R_sym S (.inr x),R_boundary S,deg,add_comm] using row

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycle_exists (S : Representation G ex v T) (i : Fin 5) : 1 ≤ N S (T.cycle i) := by
  have h := FiniteMass.hit S.label (v i)
  simpa only [S.cycle_label,N] using h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem degree_bound (S : Representation G ex v T) (C : ℤ) (h : ∀x, deg G x ≤ C) (a : Fin n) :
    regularDegree T (N S) (E S) a ≤ C*N S a := by
  rw [regular_degree S a]
  calc
    _  ≤  FiniteMass.mass S.label (fun _ => C) (.inl a) := FiniteMass.mono _ _ _ h _
    _ = _ := FiniteMass.fiber_const _ _ _ _ (fun _ _ => rfl)

end GraphMass

-- GraphStars
namespace GraphMass
open Finset ThreeExceptions FiniteCutTemplate
variable {V : Type*} [Fintype V] {n e : ℕ} {t : Fin 3 → Fin 5}
variable {G : SimpleGraph V} {ex : Fin 3 → V} {v : Fin 5 → V} {T : Table t n e}

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem edge_near (T : Table t n e) (k : Fin e) :
    Near (T.slot (T.ends k).1).1 (T.slot (T.ends k).2).1 := by
  exact ((T.ordered_covers (T.ends k).1 (T.ends k).2).mpr ⟨(k,false),rfl⟩).1

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycle_star_left (S : Representation G ex v T) (k : Fin e) (i : Fin 5)
    (ha : (T.ends k).1=T.cycle i) : N S (T.ends k).2 ≤ E S k := by
  classical
  let A := (T.ends k).1
  let B := (T.ends k).2
  have hn : Near (T.slot B).1 i := by
    have h := edge_near T k
    rw [ha,T.cycle_spec] at h
    exact h.symm
  have h := FiniteMass.mono_on (Prod.map S.label S.label)
    (fun p : V×V => if p.1=v i then (1:ℤ) else 0) (W G) (.inl A,.inl B) (by
      intro p hp
      have hy : S.label p.2=.inl B := congrArg Prod.snd hp
      by_cases hx : p.1=v i
      · have hed : G.Adj p.1 p.2 := by rw [hx]; exact ((S.cycle_adj p.2 B hy i).mpr hn).symm
        simp only [W,if_pos hed]
        simp [hx]
      · simp only [if_neg hx]
        unfold W
        split <;> norm_num)
  rw [FiniteMass.delta_left S.label (fun _ : V => 1) (v i) (.inl A) (.inl B)] at h
  simpa [S.cycle_label,←ha,A,B,N,E,R] using h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycle_star_right (S : Representation G ex v T) (k : Fin e) (j : Fin 5)
    (hb : (T.ends k).2=T.cycle j) : N S (T.ends k).1 ≤ E S k := by
  classical
  let A := (T.ends k).1
  let B := (T.ends k).2
  have hn : Near (T.slot A).1 j := by
    have h := edge_near T k
    rw [hb,T.cycle_spec] at h
    exact h
  have h := FiniteMass.mono_on (Prod.map S.label S.label)
    (fun p : V×V => if p.2=v j then (1:ℤ) else 0) (W G) (.inl A,.inl B) (by
      intro p hp
      have hx : S.label p.1=.inl A := congrArg Prod.fst hp
      by_cases hy : p.2=v j
      · have hed : G.Adj p.1 p.2 := by rw [hy]; exact (S.cycle_adj p.1 A hx j).mpr hn
        simp only [W,if_pos hed]
        simp [hy]
      · simp only [if_neg hy]
        unfold W
        split <;> norm_num)
  rw [FiniteMass.delta_right S.label (fun _ : V => 1) (v j) (.inl A) (.inl B)] at h
  simpa [S.cycle_label,←hb,A,B,N,E,R] using h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycle_star_both (S : Representation G ex v T) (k : Fin e) (i j : Fin 5)
    (ha : (T.ends k).1=T.cycle i) (hb : (T.ends k).2=T.cycle j) :
    N S (T.ends k).1+N S (T.ends k).2-1 ≤ E S k := by
  classical
  let A := (T.ends k).1
  let B := (T.ends k).2
  have hnB : Near (T.slot B).1 i := by
    have h := edge_near T k
    rw [ha,T.cycle_spec] at h
    exact h.symm
  have hnA : Near (T.slot A).1 j := by
    have h := edge_near T k
    rw [hb,T.cycle_spec] at h
    exact h
  have h := FiniteMass.mono_on (Prod.map S.label S.label)
    (fun p : V×V => (if p.1=v i then (1:ℤ) else 0)+(if p.2=v j then 1 else 0)-
      (if p.1=v i then (if p.2=v j then 1 else 0) else 0))
    (W G) (.inl A,.inl B) (by
      intro p hp
      have hx : S.label p.1=.inl A := congrArg Prod.fst hp
      have hy : S.label p.2=.inl B := congrArg Prod.snd hp
      by_cases hi : p.1=v i
      · have hed : G.Adj p.1 p.2 := by rw [hi]; exact ((S.cycle_adj p.2 B hy i).mpr hnB).symm
        simp only [W,if_pos hed]
        by_cases hj : p.2=v j <;> simp [hi,hj]
      · by_cases hj : p.2=v j
        · have hed : G.Adj p.1 p.2 := by rw [hj]; exact (S.cycle_adj p.1 A hx j).mpr hnA
          simp only [W,if_pos hed]
          simp [hi,hj]
        · simp only [if_neg hi,if_neg hj,add_zero,sub_zero]
          unfold W
          split <;> norm_num)
  rw [FiniteMass.sub,FiniteMass.add,
    FiniteMass.delta_left S.label (fun _ : V => 1) (v i) (.inl A) (.inl B),
    FiniteMass.delta_right S.label (fun _ : V => 1) (v j) (.inl A) (.inl B),
    FiniteMass.delta_left S.label (fun x : V => if x=v j then 1 else 0) (v i) (.inl A) (.inl B)] at h
  simp only [S.cycle_label,←ha,←hb,if_pos rfl,FiniteMass.delta] at h
  simpa [A,B,N,E,R,add_comm] using h

end GraphMass

-- Summary

namespace CutSummary
open Finset ThreeExceptions FiniteCutTemplate GraphMass
variable {n e : ℕ} {t : Fin 3 → Fin 5}

def properAway (T : Table t n e) (r : Fin 3) (c : Fin n ⊕ Fin 3 → Fin 5) : Prop :=
  ∀a b, Allowed t (embed T a) (embed T b) → a≠.inr r → b≠.inr r → c a≠c b

noncomputable def cutWeight (b : Fin n ⊕ Fin 3 → Bool) (a a' : Fin n ⊕ Fin 3) : ℤ := by
  classical
  exact if b a=b a' then 1 else 0
noncomputable def errorWeight (r : Fin 3) (c : Fin n ⊕ Fin 3 → Fin 5)
    (a b : Fin n ⊕ Fin 3) : ℤ := by
  classical
  exact if a≠.inr r ∧ b≠.inr r ∧ ¬Near (c a) (c b) then 1 else 0
noncomputable def rootCycle (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ)
    (i : Fin 5) : ℤ := by
  classical
  exact (∑a,if Near (T.slot a).1 i then regularDegree T N E a else 0)+
    ∑x,if i=t x then exceptionDegree T N x else 0

structure Feasible (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) (cap upper : ℤ) : Prop where
  npos : ∀a, 0 ≤ N a
  epos : ∀k, 0 ≤ E k
  vertices : ∑a,N a=22
  edgeHi : edgeCount T N E ≤ upper
  degrees : ∀a,regularDegree T N E a ≤ cap*N a
  exists_cycle : ∀i,1 ≤ N (T.cycle i)
  cycle_left : ∀k i,(T.ends k).1=T.cycle i → N (T.ends k).2 ≤ E k
  cycle_right : ∀k i,(T.ends k).2=T.cycle i → N (T.ends k).1 ≤ E k
  cycle_both : ∀k i j,(T.ends k).1=T.cycle i → (T.ends k).2=T.cycle j →
    N (T.ends k).1+N (T.ends k).2-1 ≤ E k
  cuts : ∀b,26 ≤ half T N E (cutWeight b)
  repairs : ∀r c,properAway T r c → 130 ≤ edgeCount T N E+2*half T N E (errorWeight r c)
  root : ∀i,rootCycle T N E i ≤ edgeCount T N E-26
  obstruction : 134 ≤ edgeCount T N E+exceptionDegree T N 0+exceptionDegree T N 2

end CutSummary

-- FeasibleGraph

namespace CutSummary
open scoped Classical
open Finset ThreeExceptions FiniteCutTemplate GraphMass
variable {V : Type*} [Fintype V] {n e : ℕ} {t : Fin 3 → Fin 5}
variable {G : SimpleGraph V} {ex : Fin 3 → V} {v : Fin 5 → V} {T : Table t n e}

noncomputable def cycleMask (T : Table t n e) (i : Fin 5) (s : Fin n ⊕ Fin 3) : ℤ := by
  classical
  exact match s with
  | .inl a => if Near (T.slot a).1 i then 1 else 0
  | .inr x => if i=t x then 1 else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cycleMask_spec (S : Representation G ex v T) (i : Fin 5) (a : V) :
    cycleMask T i (S.label a)=W G (v i,a) := by
  classical
  cases hl : S.label a with
  | inl u =>
    rw [W_sym G (v i) a]
    simp only [cycleMask,W,S.cycle_adj a u hl i]
  | inr x =>
    have ha := (S.singleton a x).mp hl
    subst a
    rw [W_sym G (v i) (ex x)]
    simp only [cycleMask,W,S.single]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem root_identity (S : Representation G ex v T) (i : Fin 5) :
    rootCycle T (N S) (E S) i=∑a,W G (v i,a)*deg G a := by
  classical
  have h := FiniteMass.push S.label (deg G) (cycleMask T i)
  simp_rw [cycleMask_spec S] at h
  simp only [Fintype.sum_sum_type] at h
  have anchor (x : Fin 3) : FiniteMass.mass S.label (deg G) (.inr x)=exceptionDegree T (N S) x := by
    rw [FiniteMass.singleton S.label _ (.inr x) (ex x) (fun a => S.singleton a x)]
    exact (exception_degree S x).symm
  simp only [←regular_degree S,anchor,cycleMask,mul_ite,mul_one,mul_zero] at h
  simpa only [rootCycle,mul_comm] using h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem feasible [DecidableEq V] (S : Representation G ex v T) (M cap upper : ℤ)
    (order : Fintype.card V=25)
    (count : (∑a,∑b,W G (a,b))=2*M)
    (degrees : ∀a,deg G a ≤ cap) (edgeHi : M ≤ upper)
    (bad : ∀ f : V → Bool,51 ≤ ∑a,∑b,if G.Adj a b ∧ f a=f b then (1:ℤ) else 0)
    (repair : ∀r : Fin 3,∀c : V → Fin 5,
      (∀a,a≠ex r→∀b,b≠ex r→G.Adj a b→c a≠c b) →
      130 ≤ M+(∑a,∑b,if G.Adj a b ∧ a≠ex r ∧ b≠ex r ∧ ¬Near (c a) (c b) then (1:ℤ) else 0))
    (root : ∀a,(∑b,W G (a,b)*deg G b) ≤ M-26)
    (ob : 134 ≤ M+deg G (ex 0)+deg G (ex 2)) :
    Feasible T (N S) (E S) cap upper := by
  classical
  have countEq : edgeCount T (N S) (E S)=M := by
    have h := statistic S (fun _ _ => 1) (fun _ _ => rfl)
    simp only [mul_one] at h
    change (∑a,∑b,W G (a,b))=2*edgeCount T (N S) (E S) at h
    omega
  refine ⟨N_nonneg S,fun k => R_nonneg S _ _,?_,?_,degree_bound S cap degrees,
    cycle_exists S,cycle_star_left S,cycle_star_right S,cycle_star_both S,?_,?_,?_,?_⟩
  · have h := vertex_total S
    rw [order] at h
    norm_num at h
    omega
  · simpa only [countEq] using edgeHi
  · intro b
    have hb := bad (b ∘ S.label)
    have h := statistic S (cutWeight b) (fun a a' => by simp only [cutWeight,eq_comm])
    have eq (a a' : V) : W G (a,a')*cutWeight b (S.label a) (S.label a')=
        if G.Adj a a' ∧ b (S.label a)=b (S.label a') then (1:ℤ) else 0 := by
      by_cases ha : G.Adj a a' <;> by_cases hc : b (S.label a)=b (S.label a') <;>
        simp [W,cutWeight,ha,hc]
    simp_rw [eq] at h
    simp only [Function.comp_apply] at hb
    omega
  · intro r c hp
    have proper : ∀a,a≠ex r→∀b,b≠ex r→G.Adj a b→c (S.label a)≠c (S.label b) := by
      intro a ha b hb hab
      apply hp _ _ (S.hom a b hab)
      · intro hh
        exact ha ((S.singleton a r).mp hh)
      · intro hh
        exact hb ((S.singleton b r).mp hh)
    have hr := repair r (c ∘ S.label) proper
    have h := statistic S (errorWeight r c) (fun a b => by
      simp only [errorWeight,Near,and_assoc,and_comm,and_left_comm,or_comm])
    have eq (a b : V) : W G (a,b)*errorWeight r c (S.label a) (S.label b)=
        if G.Adj a b ∧ a≠ex r ∧ b≠ex r ∧ ¬Near (c (S.label a)) (c (S.label b)) then (1:ℤ) else 0 := by
      simp only [errorWeight,W,ne_eq,S.singleton]
      split <;> simp_all
    simp_rw [eq] at h
    rw [countEq]
    simp only [Function.comp_apply] at hr
    omega
  · intro i
    rw [root_identity S i,countEq]
    exact root (v i)
  · rw [countEq,exception_degree S 0,exception_degree S 2]
    exact ob

end CutSummary

-- Canonical

namespace CutCanonical

def turn (s : Fin 10) (i : Fin 5) : Fin 5 :=
  if s.val<5 then Fin.ofNat 5 (i.val+s.val) else Fin.ofNat 5 (s.val+5-i.val)

def pair (k : Fin 6) : Fin 5 × Fin 5 :=
  match k.val with
  | 0 => (1,1)
  | 1 => (1,2)
  | 2 => (1,3)
  | 3 => (1,4)
  | 4 => (2,2)
  | _ => (2,3)

def types (k : Fin 6) : Fin 3 → Fin 5 :=
  fun x => if x=0 then 0 else if x=1 then (pair k).1 else (pair k).2

def swap (b : Bool) (x : Fin 3) : Fin 3 :=
  if b then (if x=0 then 0 else if x=1 then 2 else 1) else x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem turn_injective : ∀ s : Fin 10, Function.Injective (turn s) := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem turn_cycle : ∀ (s : Fin 10) (i : Fin 5),
    turn s (i+1)=turn s i+1 ∨ turn s i=turn s (i+1)+1 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem swap_injective : ∀ b : Bool, Function.Injective (swap b) := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem swap_path : ∀ (b : Bool) (x y : Fin 3),
    (swap b x≠swap b y ∧ (swap b x=0 ∨ swap b y=0)) ↔ (x≠y ∧ (x=0 ∨ y=0)) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem classify : ∀ t : Fin 3 → Fin 5, t 0≠t 1 → t 0≠t 2 →
    ∃ (s : Fin 10) (k : Fin 6) (b : Bool), ∀ x, turn s (types k x)=t (swap b x) := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem unique_reindex {X Y : Type*} (f : X → Y) (hf : Function.Bijective f) (P : Y → Prop) :
    (∃! x, P (f x)) ↔ ∃! y, P y := by
  constructor
  · rintro ⟨x,hx,hu⟩
    refine ⟨f x,hx,?_⟩
    intro y hy
    obtain ⟨z,rfl⟩ := hf.2 y
    exact congrArg f (hu z hy)
  · rintro ⟨y,hy,hu⟩
    obtain ⟨x,rfl⟩ := hf.2 y
    refine ⟨x,hy,?_⟩
    intro z hz
    exact hf.1 (hu (f z) hz)

end CutCanonical

-- Normalize
namespace CutCanonical
open ThreeExceptions
variable {V : Type*}

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem swap_zero : ∀b,swap b 0=0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem swap_nonzero : ∀b,swap b 2=1 ∨ swap b 2=2 := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem change_frame (G : SimpleGraph V) (ex : Fin 3 → V) (v : Fin 5 → V)
    (t : Fin 3 → Fin 5)
    (cyc : ∀i,G.Adj (v i) (v (i+1))) (dom : ∀a,∃i,G.Adj a (v i))
    (single : ∀x i,G.Adj (ex x) (v i) ↔ i=t x)
    (exedge : ∀x y,G.Adj (ex x) (ex y) ↔ x≠y ∧ (x=0∨y=0))
    (s : Fin 10) (k : Fin 6) (b : Bool)
    (eq : ∀x,turn s (types k x)=t (swap b x)) :
    (∀i,G.Adj (v (turn s i)) (v (turn s (i+1)))) ∧
    (∀a,∃i,G.Adj a (v (turn s i))) ∧
    (∀x i,G.Adj (ex (swap b x)) (v (turn s i)) ↔ i=types k x) ∧
    (∀x y,G.Adj (ex (swap b x)) (ex (swap b y)) ↔ x≠y ∧ (x=0∨y=0)) ∧
    (∀a,(∃!i,G.Adj a (v (turn s i))) ↔ ∃!i,G.Adj a (v i)) := by
  have bij : Function.Bijective (turn s) := ⟨turn_injective s,Finite.surjective_of_injective (turn_injective s)⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    rcases turn_cycle s i with h | h
    · rw [h]
      exact cyc _
    · have hh := (cyc (turn s (i+1))).symm
      rwa [←h] at hh
  · intro a
    obtain ⟨j,hj⟩ := dom a
    obtain ⟨i,rfl⟩ := bij.2 j
    exact ⟨i,hj⟩
  · intro x i
    rw [single,←eq x]
    exact (turn_injective s).eq_iff
  · intro x y
    exact (exedge _ _).trans (swap_path b x y)
  · intro a
    exact unique_reindex (turn s) bij (fun i => G.Adj a (v i))

end CutCanonical

-- DegreeCap

namespace CutDegree
open Finset

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
lemma tangent_seven (x : ℤ) : 15*x - 56  ≤  x*x := by
  by_cases h : x  ≤  7
  · have a : 0  ≤  7-x := by omega
    have b : 0  ≤  8-x := by omega
    nlinarith [mul_nonneg a b]
  · have a : 0  ≤  x-7 := by omega
    have b : 0  ≤  x-8 := by omega
    nlinarith [mul_nonneg a b]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
lemma tangent_ten (x : ℤ) : 21*x - 110  ≤  x*x := by
  by_cases h : x  ≤  10
  · have a : 0  ≤  10-x := by omega
    have b : 0  ≤  11-x := by omega
    nlinarith [mul_nonneg a b]
  · have a : 0  ≤  x-10 := by omega
    have b : 0  ≤  x-11 := by omega
    nlinarith [mul_nonneg a b]


set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem maximum_eleven (D : Fin 25 → ℤ) (W : Fin 25 → Fin 25 → ℤ) (M : ℤ)
    (sym : ∀ i j, W i j = W j i) (diag : ∀ i, W i i = 0)
    (bits : ∀ i j, W i j = 0 ∨ W i j = 1)
    (row : ∀ i, ∑ j, W i j = D i) (total : ∑ i, D i = 2*M)
    (root : ∀ i, (∑ j, W i j * D j)  ≤  M-26) (dense : 118  ≤  M) :
    ∀ i, D i  ≤  11 := by
  have col (j : Fin 25) : ∑ i, W i j = D j := by
    simpa only [sym] using row j
  have squares : (∑ i, ∑ j, W i j * D j) = ∑ j, D j * D j := by
    rw [sum_comm]
    simp_rw [← sum_mul, col]
  have upper : (∑ j, D j * D j)  ≤  25*(M-26) := by
    rw [← squares]
    calc
      _  ≤  ∑ _i : Fin 25, (M-26) := sum_le_sum fun i _ => root i
      _ = _ := by simp [nsmul_eq_mul] <;> ring
  intro i
  have point (j : Fin 25) :
      21*D j - 110 - 6*(W i j * D j) + 54*W i j +
        (if j=i then D i*D i - 21*D i + 110 else 0)  ≤  D j*D j := by
    by_cases h : j=i
    · subst j
      simp only [diag, zero_mul, mul_zero, if_true]
      linarith
    · rw [if_neg h]
      rcases bits i j with hbit | hbit
      · rw [hbit]
        simpa using tangent_ten (D j)
      · rw [hbit]
        nlinarith [tangent_seven (D j)]
  have summed := sum_le_sum (s := univ) (fun j _ => point j)
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
  have singleton : (∑ j : Fin 25, if j=i then D i*D i-21*D i+110 else 0) =
      D i*D i-21*D i+110 := by simp
  rw [singleton, total, row] at summed
  norm_num at summed
  have numeric : D i*D i + 11*M + 33*D i  ≤  1834 := by
    linarith only [summed, upper, root i]
  by_contra h
  have big : 12  ≤  D i := by omega
  have square : 144  ≤  D i*D i := by nlinarith [sq_nonneg (D i-12)]
  linarith only [numeric, dense, big, square]

end CutDegree

-- CertificatesIntLookup

namespace CertifiedLinear
open Finset


set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem contradiction {n m : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (weight : Fin m → ℤ) (v : Fin n → ℤ)
    (valid : ∀ i, ∑ j, A i j * v j  ≤  b i)
    (weight_nonneg : ∀ i, 0  ≤  weight i) (v_nonneg : ∀ j, 0  ≤  v j)
    (coeff_nonneg : ∀ j, 0  ≤  ∑ i, weight i * A i j)
    (rhs_negative : ∑ i, weight i * b i < 0) : False := by
  have bound : (∑ i, weight i * ∑ j, A i j * v j)  ≤  ∑ i, weight i * b i :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (valid i) (weight_nonneg i)
  have identity : (∑ i, weight i * ∑ j, A i j * v j) =
      ∑ j, (∑ i, weight i * A i j) * v j := by
    simp_rw [mul_sum, sum_mul, mul_assoc]
    exact sum_comm
  rw [identity] at bound
  have pos : 0  ≤  ∑ j, (∑ i, weight i * A i j) * v j :=
    sum_nonneg fun j _ => mul_nonneg (coeff_nonneg j) (v_nonneg j)
  exact (not_le_of_gt rhs_negative) (pos.trans bound)

end CertifiedLinear


namespace IndependentCutLP.C011
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def A (i : Fin 48) (j : Fin 63) : ℤ :=
  match j.val with
  | 0 => match i.val with
    | 0 => 1
    | 5 => -12
    | _ => 0
  | 1 => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => -1
    | 6 => -11
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 39 => -1
    | _ => 0
  | 2 => match i.val with
    | 0 => 1
    | 7 => -12
    | _ => 0
  | 3 => match i.val with
    | 0 => 1
    | 1 => 1
    | 8 => -11
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | _ => 0
  | 4 => match i.val with
    | 0 => 1
    | 1 => 1
    | 9 => -11
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 39 => -1
    | 44 => -1
    | 45 => -1
    | 47 => -1
    | _ => 0
  | 5 => match i.val with
    | 0 => 1
    | 1 => 2
    | 3 => -1
    | 10 => -10
    | 19 => -2
    | 20 => -2
    | 21 => -2
    | 39 => -2
    | 44 => -1
    | 45 => -2
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 6 => match i.val with
    | 0 => 1
    | 11 => -12
    | 22 => 1
    | _ => 0
  | 7 => match i.val with
    | 0 => 1
    | 1 => 1
    | 19 => -1
    | 20 => -3
    | 21 => -3
    | 33 => -1
    | 36 => -1
    | 39 => -1
    | _ => 0
  | 8 => match i.val with
    | 0 => 1
    | 4 => -1
    | 12 => -12
    | 22 => 1
    | 26 => 1
    | _ => 0
  | 9 => match i.val with
    | 0 => 1
    | 1 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 27 => 1
    | 34 => -1
    | 35 => -1
    | 37 => -1
    | 42 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 10 => match i.val with
    | 0 => 1
    | 1 => 1
    | 13 => -11
    | 19 => -1
    | 20 => -1
    | 21 => -3
    | 23 => 1
    | 28 => 1
    | 36 => -1
    | 38 => -1
    | 41 => -1
    | 43 => -1
    | 45 => -1
    | _ => 0
  | 11 => match i.val with
    | 0 => 1
    | 1 => 1
    | 14 => -11
    | 19 => -1
    | 20 => -3
    | 21 => -1
    | 24 => 1
    | 29 => 1
    | 36 => -1
    | 38 => -1
    | 40 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 12 => match i.val with
    | 0 => 1
    | 1 => 2
    | 19 => -2
    | 20 => -4
    | 21 => -4
    | 25 => 1
    | 36 => -2
    | 41 => -2
    | 44 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 13 => match i.val with
    | 0 => 1
    | 15 => -12
    | 26 => 1
    | _ => 0
  | 14 => match i.val with
    | 0 => 1
    | 1 => 1
    | 16 => -11
    | 19 => -3
    | 20 => -1
    | 21 => -1
    | 30 => 1
    | 33 => -1
    | 34 => -1
    | 35 => -1
    | 37 => -1
    | 39 => -1
    | _ => 0
  | 15 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -11
    | 19 => -3
    | 20 => -1
    | 21 => -1
    | 31 => 1
    | 33 => -1
    | 34 => -1
    | 35 => -1
    | 37 => -1
    | 39 => -1
    | _ => 0
  | 16 => match i.val with
    | 0 => 1
    | 1 => 2
    | 19 => -6
    | 20 => -2
    | 21 => -2
    | 32 => 1
    | 33 => -2
    | 34 => -2
    | 35 => -2
    | 44 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 17 => match i.val with
    | 1 => 1
    | 5 => 1
    | 7 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | _ => 0
  | 18 => match i.val with
    | 1 => 1
    | 6 => 1
    | 7 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | _ => 0
  | 19 => match i.val with
    | 1 => 1
    | 5 => 1
    | 8 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | 39 => -1
    | _ => 0
  | 20 => match i.val with
    | 1 => 1
    | 6 => 1
    | 8 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | 39 => -1
    | _ => 0
  | 21 => match i.val with
    | 1 => 1
    | 5 => 1
    | 9 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | 44 => -1
    | _ => 0
  | 22 => match i.val with
    | 1 => 1
    | 6 => 1
    | 9 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | 44 => -1
    | _ => 0
  | 23 => match i.val with
    | 1 => 1
    | 5 => 1
    | 10 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | _ => 0
  | 24 => match i.val with
    | 1 => 1
    | 6 => 1
    | 10 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 35 => -1
    | _ => 0
  | 25 => match i.val with
    | 1 => 1
    | 7 => 1
    | 11 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 41 => -1
    | _ => 0
  | 26 => match i.val with
    | 1 => 1
    | 8 => 1
    | 11 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 39 => -1
    | 41 => -1
    | _ => 0
  | 27 => match i.val with
    | 1 => 1
    | 9 => 1
    | 11 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 41 => -1
    | 44 => -1
    | _ => 0
  | 28 => match i.val with
    | 1 => 1
    | 10 => 1
    | 11 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 41 => -1
    | _ => 0
  | 29 => match i.val with
    | 1 => 1
    | 7 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | _ => 0
  | 30 => match i.val with
    | 1 => 1
    | 8 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 39 => -1
    | _ => 0
  | 31 => match i.val with
    | 1 => 1
    | 9 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 44 => -1
    | _ => 0
  | 32 => match i.val with
    | 1 => 1
    | 10 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | _ => 0
  | 33 => match i.val with
    | 1 => 1
    | 11 => 1
    | 12 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | 43 => -1
    | _ => 0
  | 34 => match i.val with
    | 1 => 1
    | 12 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 40 => -1
    | 41 => -1
    | 43 => -1
    | _ => 0
  | 35 => match i.val with
    | 1 => 1
    | 11 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 38 => -1
    | 40 => -1
    | 43 => -1
    | _ => 0
  | 36 => match i.val with
    | 1 => 1
    | 11 => 1
    | 13 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 23 => -1
    | 38 => -1
    | 39 => -1
    | 43 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 37 => match i.val with
    | 1 => 1
    | 13 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 38 => -1
    | 39 => -1
    | 41 => -1
    | 43 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 38 => match i.val with
    | 1 => 1
    | 11 => 1
    | 14 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 24 => -1
    | 38 => -1
    | 39 => -1
    | 40 => -1
    | 47 => -1
    | _ => 0
  | 39 => match i.val with
    | 1 => 1
    | 14 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 38 => -1
    | 39 => -1
    | 40 => -1
    | 41 => -1
    | 47 => -1
    | _ => 0
  | 40 => match i.val with
    | 1 => 1
    | 11 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 25 => -1
    | 39 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 41 => match i.val with
    | 1 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 39 => -1
    | 41 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 42 => match i.val with
    | 1 => 1
    | 5 => 1
    | 15 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 37 => -1
    | 42 => -1
    | _ => 0
  | 43 => match i.val with
    | 1 => 1
    | 6 => 1
    | 15 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 37 => -1
    | 42 => -1
    | _ => 0
  | 44 => match i.val with
    | 1 => 1
    | 12 => 1
    | 15 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 26 => -1
    | 38 => -1
    | 39 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 45 => match i.val with
    | 1 => 1
    | 15 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 27 => -1
    | 39 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 46 => match i.val with
    | 1 => 1
    | 13 => 1
    | 15 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 28 => -1
    | 40 => -1
    | 45 => -1
    | 47 => -1
    | _ => 0
  | 47 => match i.val with
    | 1 => 1
    | 14 => 1
    | 15 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 29 => -1
    | 43 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | _ => 0
  | 48 => match i.val with
    | 1 => 1
    | 15 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 38 => -1
    | 40 => -1
    | 43 => -1
    | _ => 0
  | 49 => match i.val with
    | 1 => 1
    | 5 => 1
    | 16 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 37 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | _ => 0
  | 50 => match i.val with
    | 1 => 1
    | 6 => 1
    | 16 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 37 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | _ => 0
  | 51 => match i.val with
    | 1 => 1
    | 12 => 1
    | 16 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 30 => -1
    | 38 => -1
    | 39 => -1
    | 42 => -1
    | 47 => -1
    | _ => 0
  | 52 => match i.val with
    | 1 => 1
    | 16 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 39 => -1
    | 42 => -1
    | 47 => -1
    | _ => 0
  | 53 => match i.val with
    | 1 => 1
    | 14 => 1
    | 16 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 54 => match i.val with
    | 1 => 1
    | 5 => 1
    | 17 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 37 => -1
    | 45 => -1
    | 47 => -1
    | _ => 0
  | 55 => match i.val with
    | 1 => 1
    | 6 => 1
    | 17 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 37 => -1
    | 45 => -1
    | 47 => -1
    | _ => 0
  | 56 => match i.val with
    | 1 => 1
    | 12 => 1
    | 17 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 31 => -1
    | 38 => -1
    | 39 => -1
    | 42 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 57 => match i.val with
    | 1 => 1
    | 17 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 39 => -1
    | 42 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 58 => match i.val with
    | 1 => 1
    | 13 => 1
    | 17 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 40 => -1
    | 42 => -1
    | _ => 0
  | 59 => match i.val with
    | 1 => 1
    | 5 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 39 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 60 => match i.val with
    | 1 => 1
    | 6 => 1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 32 => -1
    | 34 => -1
    | 39 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | _ => 0
  | 61 => match i.val with
    | 1 => 1
    | 12 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 37 => -1
    | 38 => -1
    | 42 => -1
    | _ => 0
  | 62 => match i.val with
    | 1 => 1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 37 => -1
    | 42 => -1
    | _ => 0
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def B (i : Fin 48) : ℤ :=
  match i.val with
  | 0 => 22
  | 1 => 119
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 18 => -26
  | 19 => -128
  | 20 => -128
  | 21 => -128
  | 22 => 1
  | 26 => 1
  | 33 => -24
  | 34 => -26
  | 35 => -26
  | 36 => -26
  | 37 => -26
  | 38 => -26
  | 39 => -26
  | 40 => -26
  | 41 => -26
  | 42 => -26
  | 43 => -26
  | 44 => -25
  | 45 => -24
  | 46 => -25
  | 47 => -25
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private def w (i : Fin 48) : ℤ :=
  match i.val with
  | 0 => 4380
  | 1 => 4695
  | 2 => 122
  | 3 => 3600
  | 4 => 1380
  | 5 => 365
  | 6 => 365
  | 7 => 365
  | 8 => 545
  | 9 => 515
  | 10 => 365
  | 11 => 438
  | 12 => 438
  | 13 => 66
  | 14 => 66
  | 15 => 480
  | 16 => 162
  | 17 => 162
  | 18 => 42
  | 19 => 145
  | 20 => 792
  | 21 => 792
  | 22 => 876
  | 23 => 876
  | 24 => 876
  | 25 => 1380
  | 26 => 1380
  | 27 => 1380
  | 28 => 636
  | 29 => 636
  | 30 => 744
  | 31 => 744
  | 32 => 420
  | 33 => 667
  | 34 => 887
  | 35 => 3029
  | 36 => 3331
  | 37 => 1255
  | 38 => 438
  | 39 => 180
  | 40 => 1483
  | 41 => 438
  | 42 => 1669
  | 43 => 1483
  | 44 => 150
  | 45 => 858
  | 46 => 343
  | 47 => 493
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_weights : ∀ i : Fin 48, 0  ≤  w i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_coeff : ∀ j : Fin 63, 0  ≤  ∑ i : Fin 48, w i * A i j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem negative_rhs : (∑ i : Fin 48, w i * B i) < 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (v : Fin 63 → ℤ) (positive : ∀ j, 0  ≤  v j)
    (valid : ∀ i : Fin 48, ∑ j, A i j * v j  ≤  B i) : False :=
  CertifiedLinear.contradiction A B w v valid nonneg_weights positive nonneg_coeff negative_rhs
end IndependentCutLP.C011

namespace IndependentCutLP.C012
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def A (i : Fin 47) (j : Fin 55) : ℤ :=
  match j.val with
  | 0 => match i.val with
    | 0 => 1
    | 6 => -12
    | 22 => 1
    | _ => 0
  | 1 => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => -1
    | 7 => -11
    | 17 => -1
    | 18 => -1
    | 23 => 1
    | 28 => -1
    | 31 => -1
    | 39 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 2 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 29 => -1
    | 30 => -1
    | 31 => -1
    | 34 => -1
    | 43 => -1
    | _ => 0
  | 3 => match i.val with
    | 0 => 1
    | 8 => -12
    | _ => 0
  | 4 => match i.val with
    | 0 => 1
    | 1 => 1
    | 3 => -1
    | 9 => -11
    | 17 => -1
    | 18 => -1
    | 29 => -1
    | 39 => -1
    | 45 => -1
    | _ => 0
  | 5 => match i.val with
    | 0 => 1
    | 10 => -12
    | 19 => 1
    | _ => 0
  | 6 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 29 => -1
    | 30 => -1
    | 32 => -1
    | 35 => -1
    | 39 => -1
    | _ => 0
  | 7 => match i.val with
    | 0 => 1
    | 1 => 1
    | 4 => -1
    | 11 => -11
    | 17 => -1
    | 18 => -1
    | 20 => 1
    | 28 => -1
    | 36 => -1
    | 43 => -1
    | _ => 0
  | 8 => match i.val with
    | 0 => 1
    | 5 => -1
    | 12 => -12
    | 20 => 1
    | 24 => 1
    | _ => 0
  | 9 => match i.val with
    | 0 => 1
    | 1 => 1
    | 13 => -11
    | 17 => -3
    | 18 => -3
    | 25 => 1
    | 28 => -1
    | 31 => -1
    | 36 => -1
    | 37 => -1
    | 38 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 10 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -1
    | 18 => -3
    | 21 => 1
    | 29 => -1
    | 30 => -1
    | 34 => -1
    | 41 => -1
    | _ => 0
  | 11 => match i.val with
    | 0 => 1
    | 14 => -12
    | 23 => 1
    | 24 => 1
    | _ => 0
  | 12 => match i.val with
    | 0 => 1
    | 1 => 1
    | 15 => -11
    | 17 => -3
    | 18 => -1
    | 26 => 1
    | 28 => -1
    | 31 => -1
    | 35 => -1
    | 36 => -1
    | 45 => -1
    | _ => 0
  | 13 => match i.val with
    | 0 => 1
    | 1 => 1
    | 16 => -11
    | 17 => -1
    | 18 => -1
    | 27 => 1
    | 28 => -1
    | 33 => -1
    | 36 => -1
    | 38 => -1
    | 39 => -1
    | 41 => -1
    | 42 => -1
    | 45 => -1
    | _ => 0
  | 14 => match i.val with
    | 0 => 1
    | 1 => 2
    | 17 => -4
    | 18 => -2
    | 28 => -2
    | 31 => -1
    | 32 => -1
    | 33 => -1
    | 35 => -1
    | 37 => -1
    | 38 => -1
    | 40 => -1
    | 41 => -1
    | 42 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 15 => match i.val with
    | 1 => 1
    | 6 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 28 => -1
    | 29 => -1
    | 31 => -1
    | 35 => -1
    | 44 => -1
    | _ => 0
  | 16 => match i.val with
    | 1 => 1
    | 7 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 28 => -1
    | 29 => -1
    | 31 => -1
    | 32 => -1
    | 35 => -1
    | _ => 0
  | 17 => match i.val with
    | 1 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 28 => -1
    | 29 => -1
    | 31 => -1
    | 36 => -1
    | _ => 0
  | 18 => match i.val with
    | 1 => 1
    | 6 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 28 => -1
    | 29 => -1
    | 31 => -1
    | 35 => -1
    | 44 => -1
    | _ => 0
  | 19 => match i.val with
    | 1 => 1
    | 7 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 28 => -1
    | 29 => -1
    | 31 => -1
    | 32 => -1
    | 35 => -1
    | _ => 0
  | 20 => match i.val with
    | 1 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 28 => -1
    | 29 => -1
    | 31 => -1
    | 36 => -1
    | _ => 0
  | 21 => match i.val with
    | 1 => 1
    | 8 => 1
    | 10 => 1
    | 17 => -1
    | 18 => -1
    | 30 => -1
    | 34 => -1
    | _ => 0
  | 22 => match i.val with
    | 1 => 1
    | 9 => 1
    | 10 => 1
    | 17 => -1
    | 18 => -1
    | 30 => -1
    | 34 => -1
    | _ => 0
  | 23 => match i.val with
    | 1 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 30 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 24 => match i.val with
    | 1 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 30 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 25 => match i.val with
    | 1 => 1
    | 8 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 30 => -1
    | 34 => -1
    | _ => 0
  | 26 => match i.val with
    | 1 => 1
    | 9 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 30 => -1
    | 34 => -1
    | _ => 0
  | 27 => match i.val with
    | 1 => 1
    | 10 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 33 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 28 => match i.val with
    | 1 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 33 => -1
    | 34 => -1
    | _ => 0
  | 29 => match i.val with
    | 1 => 1
    | 11 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 20 => -1
    | 33 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 30 => match i.val with
    | 1 => 1
    | 10 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 33 => -1
    | 40 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 31 => match i.val with
    | 1 => 1
    | 11 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 33 => -1
    | 40 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 32 => match i.val with
    | 1 => 1
    | 10 => 1
    | 17 => -1
    | 18 => -1
    | 39 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 33 => match i.val with
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 34 => -1
    | 39 => -1
    | _ => 0
  | 34 => match i.val with
    | 1 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 21 => -1
    | 39 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 35 => match i.val with
    | 1 => 1
    | 6 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 22 => -1
    | 32 => -1
    | 36 => -1
    | 38 => -1
    | 46 => -1
    | _ => 0
  | 36 => match i.val with
    | 1 => 1
    | 7 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 23 => -1
    | 36 => -1
    | 38 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 37 => match i.val with
    | 1 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 32 => -1
    | 35 => -1
    | 38 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 38 => match i.val with
    | 1 => 1
    | 12 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 24 => -1
    | 37 => -1
    | 39 => -1
    | 40 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 39 => match i.val with
    | 1 => 1
    | 13 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 25 => -1
    | 37 => -1
    | 39 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 40 => match i.val with
    | 1 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 33 => -1
    | 37 => -1
    | 40 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 41 => match i.val with
    | 1 => 1
    | 6 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 36 => -1
    | 39 => -1
    | 44 => -1
    | _ => 0
  | 42 => match i.val with
    | 1 => 1
    | 7 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 26 => -1
    | 32 => -1
    | 36 => -1
    | 39 => -1
    | _ => 0
  | 43 => match i.val with
    | 1 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 35 => -1
    | 39 => -1
    | _ => 0
  | 44 => match i.val with
    | 1 => 1
    | 12 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 32 => -1
    | 37 => -1
    | 38 => -1
    | 40 => -1
    | 42 => -1
    | 43 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 45 => match i.val with
    | 1 => 1
    | 13 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 32 => -1
    | 37 => -1
    | 38 => -1
    | 41 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | _ => 0
  | 46 => match i.val with
    | 1 => 1
    | 6 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 32 => -1
    | 36 => -1
    | 37 => -1
    | 40 => -1
    | 46 => -1
    | _ => 0
  | 47 => match i.val with
    | 1 => 1
    | 7 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 36 => -1
    | 37 => -1
    | 40 => -1
    | 44 => -1
    | 46 => -1
    | _ => 0
  | 48 => match i.val with
    | 1 => 1
    | 12 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 27 => -1
    | 38 => -1
    | 39 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 49 => match i.val with
    | 1 => 1
    | 13 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 38 => -1
    | 39 => -1
    | 40 => -1
    | 41 => -1
    | 45 => -1
    | _ => 0
  | 50 => match i.val with
    | 1 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 33 => -1
    | 38 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 51 => match i.val with
    | 1 => 1
    | 6 => 1
    | 17 => -1
    | 18 => -1
    | 32 => -1
    | 37 => -1
    | 38 => -1
    | 39 => -1
    | 42 => -1
    | 45 => -1
    | 46 => -1
    | _ => 0
  | 52 => match i.val with
    | 1 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 37 => -1
    | 38 => -1
    | 39 => -1
    | 42 => -1
    | 44 => -1
    | 45 => -1
    | 46 => -1
    | _ => 0
  | 53 => match i.val with
    | 1 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 36 => -1
    | 40 => -1
    | 43 => -1
    | 45 => -1
    | _ => 0
  | 54 => match i.val with
    | 1 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 36 => -1
    | 41 => -1
    | 42 => -1
    | _ => 0
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def B (i : Fin 47) : ℤ :=
  match i.val with
  | 0 => 22
  | 1 => 119
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 5 => -1
  | 17 => -128
  | 18 => -128
  | 20 => 1
  | 23 => 1
  | 24 => 1
  | 28 => -26
  | 29 => -26
  | 30 => -26
  | 31 => -25
  | 32 => -25
  | 33 => -25
  | 34 => -26
  | 35 => -25
  | 36 => -26
  | 37 => -25
  | 38 => -25
  | 39 => -26
  | 40 => -25
  | 41 => -25
  | 42 => -25
  | 43 => -26
  | 44 => -25
  | 45 => -26
  | 46 => -25
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private def w (i : Fin 47) : ℤ :=
  match i.val with
  | 0 => 1980
  | 1 => 2743
  | 2 => 92
  | 3 => 340
  | 4 => 370
  | 5 => 216
  | 6 => 198
  | 7 => 198
  | 8 => 165
  | 9 => 165
  | 10 => 198
  | 11 => 198
  | 12 => 216
  | 13 => 18
  | 14 => 234
  | 15 => 18
  | 16 => 36
  | 17 => 591
  | 18 => 337
  | 19 => 396
  | 20 => 396
  | 21 => 396
  | 22 => 396
  | 23 => 396
  | 24 => 432
  | 25 => 432
  | 26 => 118
  | 27 => 432
  | 28 => 8
  | 29 => 681
  | 30 => 1142
  | 31 => 296
  | 32 => 139
  | 33 => 995
  | 34 => 1036
  | 35 => 1054
  | 36 => 995
  | 37 => 18
  | 38 => 36
  | 39 => 779
  | 40 => 216
  | 41 => 658
  | 42 => 180
  | 43 => 640
  | 44 => 139
  | 45 => 180
  | 46 => 681
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_weights : ∀ i : Fin 47, 0  ≤  w i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_coeff : ∀ j : Fin 55, 0  ≤  ∑ i : Fin 47, w i * A i j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem negative_rhs : (∑ i : Fin 47, w i * B i) < 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (v : Fin 55 → ℤ) (positive : ∀ j, 0  ≤  v j)
    (valid : ∀ i : Fin 47, ∑ j, A i j * v j  ≤  B i) : False :=
  CertifiedLinear.contradiction A B w v valid nonneg_weights positive nonneg_coeff negative_rhs
end IndependentCutLP.C012

namespace IndependentCutLP.C013
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def A (i : Fin 41) (j : Fin 57) : ℤ :=
  match j.val with
  | 0 => match i.val with
    | 0 => 1
    | 5 => -12
    | _ => 0
  | 1 => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => -1
    | 6 => -11
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 22 => 1
    | 30 => -1
    | _ => 0
  | 2 => match i.val with
    | 0 => 1
    | 1 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -3
    | 19 => -1
    | 20 => -1
    | 29 => -1
    | 31 => -1
    | 33 => -1
    | 36 => -1
    | 37 => -1
    | 39 => -1
    | 40 => -1
    | _ => 0
  | 3 => match i.val with
    | 0 => 1
    | 7 => -12
    | 21 => 1
    | _ => 0
  | 4 => match i.val with
    | 0 => 1
    | 1 => 1
    | 3 => -1
    | 8 => -11
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 22 => 1
    | _ => 0
  | 5 => match i.val with
    | 0 => 1
    | 1 => 1
    | 9 => -11
    | 16 => -3
    | 17 => -3
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 35 => -1
    | _ => 0
  | 6 => match i.val with
    | 0 => 1
    | 1 => 2
    | 10 => -10
    | 16 => -4
    | 17 => -4
    | 18 => -2
    | 19 => -2
    | 20 => -2
    | 32 => -1
    | 33 => -2
    | 34 => -1
    | 35 => -1
    | _ => 0
  | 7 => match i.val with
    | 0 => 1
    | 11 => -12
    | 25 => 1
    | _ => 0
  | 8 => match i.val with
    | 0 => 1
    | 1 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -3
    | 32 => -1
    | 34 => -1
    | _ => 0
  | 9 => match i.val with
    | 0 => 1
    | 12 => -12
    | 23 => 1
    | 26 => 1
    | _ => 0
  | 10 => match i.val with
    | 0 => 1
    | 1 => 1
    | 16 => -1
    | 17 => -3
    | 18 => -3
    | 19 => -3
    | 20 => -1
    | 27 => 1
    | 29 => -1
    | 30 => -1
    | 31 => -1
    | 38 => -1
    | 39 => -1
    | _ => 0
  | 11 => match i.val with
    | 0 => 1
    | 1 => 1
    | 13 => -11
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -3
    | 24 => 1
    | 32 => -1
    | 34 => -1
    | 36 => -1
    | _ => 0
  | 12 => match i.val with
    | 0 => 1
    | 1 => 1
    | 4 => -1
    | 14 => -11
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 25 => 1
    | 28 => 1
    | 36 => -1
    | _ => 0
  | 13 => match i.val with
    | 0 => 1
    | 1 => 2
    | 16 => -2
    | 17 => -2
    | 18 => -2
    | 19 => -2
    | 20 => -4
    | 32 => -1
    | 34 => -1
    | 35 => -1
    | _ => 0
  | 14 => match i.val with
    | 0 => 1
    | 15 => -12
    | 28 => 1
    | _ => 0
  | 15 => match i.val with
    | 0 => 1
    | 1 => 1
    | 16 => -3
    | 17 => -1
    | 18 => -1
    | 19 => -3
    | 20 => -1
    | 29 => -1
    | 30 => -1
    | 38 => -1
    | _ => 0
  | 16 => match i.val with
    | 1 => 1
    | 5 => 1
    | 7 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 34 => -1
    | 38 => -1
    | _ => 0
  | 17 => match i.val with
    | 1 => 1
    | 6 => 1
    | 7 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 30 => -1
    | _ => 0
  | 18 => match i.val with
    | 1 => 1
    | 7 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 38 => -1
    | _ => 0
  | 19 => match i.val with
    | 1 => 1
    | 5 => 1
    | 8 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 34 => -1
    | 38 => -1
    | _ => 0
  | 20 => match i.val with
    | 1 => 1
    | 6 => 1
    | 8 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 22 => -1
    | 30 => -1
    | _ => 0
  | 21 => match i.val with
    | 1 => 1
    | 8 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 38 => -1
    | _ => 0
  | 22 => match i.val with
    | 1 => 1
    | 5 => 1
    | 9 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 38 => -1
    | _ => 0
  | 23 => match i.val with
    | 1 => 1
    | 6 => 1
    | 9 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 34 => -1
    | _ => 0
  | 24 => match i.val with
    | 1 => 1
    | 5 => 1
    | 10 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 33 => -1
    | 38 => -1
    | _ => 0
  | 25 => match i.val with
    | 1 => 1
    | 6 => 1
    | 10 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 30 => -1
    | 33 => -1
    | 34 => -1
    | _ => 0
  | 26 => match i.val with
    | 1 => 1
    | 7 => 1
    | 11 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 34 => -1
    | 36 => -1
    | _ => 0
  | 27 => match i.val with
    | 1 => 1
    | 8 => 1
    | 11 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 34 => -1
    | 36 => -1
    | _ => 0
  | 28 => match i.val with
    | 1 => 1
    | 9 => 1
    | 11 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 36 => -1
    | _ => 0
  | 29 => match i.val with
    | 1 => 1
    | 10 => 1
    | 11 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 33 => -1
    | 36 => -1
    | _ => 0
  | 30 => match i.val with
    | 1 => 1
    | 7 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 34 => -1
    | _ => 0
  | 31 => match i.val with
    | 1 => 1
    | 8 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 34 => -1
    | _ => 0
  | 32 => match i.val with
    | 1 => 1
    | 9 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | _ => 0
  | 33 => match i.val with
    | 1 => 1
    | 10 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 32 => -1
    | 33 => -1
    | _ => 0
  | 34 => match i.val with
    | 1 => 1
    | 11 => 1
    | 12 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 23 => -1
    | 33 => -1
    | 39 => -1
    | 40 => -1
    | _ => 0
  | 35 => match i.val with
    | 1 => 1
    | 12 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 33 => -1
    | 36 => -1
    | 39 => -1
    | 40 => -1
    | _ => 0
  | 36 => match i.val with
    | 1 => 1
    | 11 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 33 => -1
    | 35 => -1
    | 37 => -1
    | 40 => -1
    | _ => 0
  | 37 => match i.val with
    | 1 => 1
    | 11 => 1
    | 13 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 24 => -1
    | _ => 0
  | 38 => match i.val with
    | 1 => 1
    | 13 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 36 => -1
    | _ => 0
  | 39 => match i.val with
    | 1 => 1
    | 11 => 1
    | 14 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 25 => -1
    | 35 => -1
    | _ => 0
  | 40 => match i.val with
    | 1 => 1
    | 14 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 35 => -1
    | 36 => -1
    | _ => 0
  | 41 => match i.val with
    | 1 => 1
    | 11 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 35 => -1
    | 36 => -1
    | _ => 0
  | 42 => match i.val with
    | 1 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 35 => -1
    | _ => 0
  | 43 => match i.val with
    | 1 => 1
    | 5 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 29 => -1
    | 34 => -1
    | 37 => -1
    | 39 => -1
    | _ => 0
  | 44 => match i.val with
    | 1 => 1
    | 6 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 29 => -1
    | 37 => -1
    | 38 => -1
    | 39 => -1
    | _ => 0
  | 45 => match i.val with
    | 1 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 29 => -1
    | 37 => -1
    | 39 => -1
    | _ => 0
  | 46 => match i.val with
    | 1 => 1
    | 12 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 26 => -1
    | 31 => -1
    | 35 => -1
    | 39 => -1
    | _ => 0
  | 47 => match i.val with
    | 1 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 27 => -1
    | 31 => -1
    | 37 => -1
    | _ => 0
  | 48 => match i.val with
    | 1 => 1
    | 13 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 31 => -1
    | 33 => -1
    | 35 => -1
    | 40 => -1
    | _ => 0
  | 49 => match i.val with
    | 1 => 1
    | 14 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 28 => -1
    | 31 => -1
    | 33 => -1
    | 40 => -1
    | _ => 0
  | 50 => match i.val with
    | 1 => 1
    | 15 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 31 => -1
    | 33 => -1
    | 36 => -1
    | 40 => -1
    | _ => 0
  | 51 => match i.val with
    | 1 => 1
    | 5 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 29 => -1
    | 34 => -1
    | _ => 0
  | 52 => match i.val with
    | 1 => 1
    | 6 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 29 => -1
    | 38 => -1
    | _ => 0
  | 53 => match i.val with
    | 1 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 29 => -1
    | _ => 0
  | 54 => match i.val with
    | 1 => 1
    | 12 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 31 => -1
    | 35 => -1
    | 37 => -1
    | _ => 0
  | 55 => match i.val with
    | 1 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 31 => -1
    | 39 => -1
    | _ => 0
  | 56 => match i.val with
    | 1 => 1
    | 14 => 1
    | 16 => -1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 31 => -1
    | 33 => -1
    | 37 => -1
    | 39 => -1
    | 40 => -1
    | _ => 0
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def B (i : Fin 41) : ℤ :=
  match i.val with
  | 0 => 22
  | 1 => 119
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 16 => -128
  | 17 => -126
  | 18 => -128
  | 19 => -128
  | 20 => -128
  | 22 => 1
  | 25 => 1
  | 28 => 1
  | 29 => -26
  | 30 => -26
  | 31 => -26
  | 32 => -25
  | 33 => -26
  | 34 => -25
  | 35 => -25
  | 36 => -26
  | 37 => -26
  | 38 => -26
  | 39 => -26
  | 40 => -26
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private def w (i : Fin 41) : ℤ :=
  match i.val with
  | 0 => 15840
  | 1 => 20800
  | 2 => 3740
  | 3 => 3300
  | 4 => 4928
  | 5 => 1320
  | 6 => 1320
  | 7 => 1540
  | 8 => 1540
  | 9 => 220
  | 10 => 275
  | 11 => 1584
  | 12 => 1712
  | 13 => 176
  | 14 => 1584
  | 15 => 1584
  | 16 => 5556
  | 17 => 164
  | 18 => 5456
  | 19 => 714
  | 20 => 7150
  | 21 => 2640
  | 22 => 2640
  | 23 => 3168
  | 24 => 3520
  | 25 => 3168
  | 26 => 1536
  | 27 => 1888
  | 28 => 3168
  | 29 => 1760
  | 30 => 1980
  | 31 => 816
  | 32 => 1980
  | 33 => 55
  | 34 => 1320
  | 35 => 1760
  | 36 => 1584
  | 37 => 640
  | 38 => 1320
  | 39 => 944
  | 40 => 889
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_weights : ∀ i : Fin 41, 0  ≤  w i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_coeff : ∀ j : Fin 57, 0  ≤  ∑ i : Fin 41, w i * A i j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem negative_rhs : (∑ i : Fin 41, w i * B i) < 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (v : Fin 57 → ℤ) (positive : ∀ j, 0  ≤  v j)
    (valid : ∀ i : Fin 41, ∑ j, A i j * v j  ≤  B i) : False :=
  CertifiedLinear.contradiction A B w v valid nonneg_weights positive nonneg_coeff negative_rhs
end IndependentCutLP.C013

namespace IndependentCutLP.C014
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def A (i : Fin 48) (j : Fin 60) : ℤ :=
  match j.val with
  | 0 => match i.val with
    | 0 => 1
    | 5 => -12
    | 33 => 1
    | _ => 0
  | 1 => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => -1
    | 6 => -11
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 34 => 1
    | _ => 0
  | 2 => match i.val with
    | 0 => 1
    | 7 => -12
    | 23 => 1
    | _ => 0
  | 3 => match i.val with
    | 0 => 1
    | 1 => 1
    | 3 => -1
    | 8 => -11
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 24 => 1
    | 46 => -1
    | _ => 0
  | 4 => match i.val with
    | 0 => 1
    | 1 => 1
    | 9 => -11
    | 17 => -1
    | 18 => -3
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | 41 => -1
    | 47 => -1
    | _ => 0
  | 5 => match i.val with
    | 0 => 1
    | 1 => 2
    | 10 => -10
    | 17 => -2
    | 18 => -4
    | 19 => -2
    | 20 => -2
    | 21 => -2
    | 22 => -2
    | 40 => -1
    | 41 => -1
    | 42 => -2
    | 47 => -1
    | _ => 0
  | 6 => match i.val with
    | 0 => 1
    | 11 => -12
    | 24 => 1
    | 26 => 1
    | _ => 0
  | 7 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -3
    | 21 => -1
    | 22 => -3
    | 25 => 1
    | 27 => 1
    | 38 => -1
    | 41 => -1
    | 46 => -1
    | _ => 0
  | 8 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -3
    | 18 => -1
    | 19 => -3
    | 20 => -3
    | 21 => -1
    | 22 => -1
    | 28 => 1
    | 39 => -1
    | 44 => -1
    | 45 => -1
    | _ => 0
  | 9 => match i.val with
    | 0 => 1
    | 4 => -1
    | 12 => -12
    | 26 => 1
    | 35 => 1
    | _ => 0
  | 10 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -3
    | 22 => -1
    | 29 => 1
    | 36 => 1
    | 39 => -1
    | 40 => -1
    | 47 => -1
    | _ => 0
  | 11 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -3
    | 20 => -1
    | 21 => -3
    | 22 => -3
    | 30 => 1
    | 38 => -1
    | 43 => -1
    | 46 => -1
    | _ => 0
  | 12 => match i.val with
    | 0 => 1
    | 13 => -12
    | 31 => 1
    | 32 => 1
    | _ => 0
  | 13 => match i.val with
    | 0 => 1
    | 1 => 1
    | 14 => -11
    | 17 => -3
    | 18 => -3
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | 41 => -1
    | _ => 0
  | 14 => match i.val with
    | 0 => 1
    | 1 => 1
    | 15 => -11
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 34 => 1
    | 35 => 1
    | _ => 0
  | 15 => match i.val with
    | 0 => 1
    | 1 => 2
    | 16 => -10
    | 17 => -4
    | 18 => -4
    | 19 => -2
    | 20 => -2
    | 21 => -2
    | 22 => -2
    | 37 => 1
    | 40 => -1
    | 41 => -1
    | 47 => -1
    | _ => 0
  | 16 => match i.val with
    | 1 => 1
    | 5 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | 42 => -1
    | 46 => -1
    | _ => 0
  | 17 => match i.val with
    | 1 => 1
    | 6 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | 42 => -1
    | 46 => -1
    | _ => 0
  | 18 => match i.val with
    | 1 => 1
    | 5 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | 46 => -1
    | _ => 0
  | 19 => match i.val with
    | 1 => 1
    | 6 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | 46 => -1
    | _ => 0
  | 20 => match i.val with
    | 1 => 1
    | 5 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | _ => 0
  | 21 => match i.val with
    | 1 => 1
    | 6 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | _ => 0
  | 22 => match i.val with
    | 1 => 1
    | 5 => 1
    | 10 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | 42 => -1
    | _ => 0
  | 23 => match i.val with
    | 1 => 1
    | 6 => 1
    | 10 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 41 => -1
    | 42 => -1
    | _ => 0
  | 24 => match i.val with
    | 1 => 1
    | 7 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 23 => -1
    | 38 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 25 => match i.val with
    | 1 => 1
    | 8 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 24 => -1
    | 38 => -1
    | 43 => -1
    | _ => 0
  | 26 => match i.val with
    | 1 => 1
    | 9 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 38 => -1
    | 43 => -1
    | 46 => -1
    | _ => 0
  | 27 => match i.val with
    | 1 => 1
    | 10 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 38 => -1
    | 42 => -1
    | 43 => -1
    | 46 => -1
    | _ => 0
  | 28 => match i.val with
    | 1 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 38 => -1
    | 42 => -1
    | _ => 0
  | 29 => match i.val with
    | 1 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 25 => -1
    | 38 => -1
    | _ => 0
  | 30 => match i.val with
    | 1 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 38 => -1
    | 46 => -1
    | _ => 0
  | 31 => match i.val with
    | 1 => 1
    | 10 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 38 => -1
    | 42 => -1
    | 46 => -1
    | _ => 0
  | 32 => match i.val with
    | 1 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 38 => -1
    | 43 => -1
    | _ => 0
  | 33 => match i.val with
    | 1 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 38 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 34 => match i.val with
    | 1 => 1
    | 11 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 26 => -1
    | 42 => -1
    | 44 => -1
    | _ => 0
  | 35 => match i.val with
    | 1 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 27 => -1
    | 42 => -1
    | 43 => -1
    | 44 => -1
    | _ => 0
  | 36 => match i.val with
    | 1 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 28 => -1
    | 44 => -1
    | _ => 0
  | 37 => match i.val with
    | 1 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 29 => -1
    | 42 => -1
    | 44 => -1
    | 45 => -1
    | _ => 0
  | 38 => match i.val with
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 44 => -1
    | 45 => -1
    | _ => 0
  | 39 => match i.val with
    | 1 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 30 => -1
    | _ => 0
  | 40 => match i.val with
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 43 => -1
    | _ => 0
  | 41 => match i.val with
    | 1 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 42 => -1
    | _ => 0
  | 42 => match i.val with
    | 1 => 1
    | 5 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | 42 => -1
    | 44 => -1
    | 47 => -1
    | _ => 0
  | 43 => match i.val with
    | 1 => 1
    | 6 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 31 => -1
    | 40 => -1
    | 42 => -1
    | 44 => -1
    | 47 => -1
    | _ => 0
  | 44 => match i.val with
    | 1 => 1
    | 12 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 32 => -1
    | 39 => -1
    | 42 => -1
    | 44 => -1
    | 45 => -1
    | _ => 0
  | 45 => match i.val with
    | 1 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 39 => -1
    | 42 => -1
    | 44 => -1
    | _ => 0
  | 46 => match i.val with
    | 1 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 39 => -1
    | 45 => -1
    | _ => 0
  | 47 => match i.val with
    | 1 => 1
    | 5 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | _ => 0
  | 48 => match i.val with
    | 1 => 1
    | 6 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | _ => 0
  | 49 => match i.val with
    | 1 => 1
    | 12 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 39 => -1
    | 45 => -1
    | 47 => -1
    | _ => 0
  | 50 => match i.val with
    | 1 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 39 => -1
    | 47 => -1
    | _ => 0
  | 51 => match i.val with
    | 1 => 1
    | 5 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 33 => -1
    | 40 => -1
    | 47 => -1
    | _ => 0
  | 52 => match i.val with
    | 1 => 1
    | 6 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 34 => -1
    | 40 => -1
    | 47 => -1
    | _ => 0
  | 53 => match i.val with
    | 1 => 1
    | 12 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 35 => -1
    | 39 => -1
    | 45 => -1
    | _ => 0
  | 54 => match i.val with
    | 1 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 36 => -1
    | 39 => -1
    | _ => 0
  | 55 => match i.val with
    | 1 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 39 => -1
    | 42 => -1
    | 44 => -1
    | 45 => -1
    | _ => 0
  | 56 => match i.val with
    | 1 => 1
    | 5 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | 47 => -1
    | _ => 0
  | 57 => match i.val with
    | 1 => 1
    | 6 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 40 => -1
    | 47 => -1
    | _ => 0
  | 58 => match i.val with
    | 1 => 1
    | 12 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 37 => -1
    | 39 => -1
    | 45 => -1
    | _ => 0
  | 59 => match i.val with
    | 1 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 39 => -1
    | _ => 0
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def B (i : Fin 48) : ℤ :=
  match i.val with
  | 0 => 22
  | 1 => 119
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 17 => -128
  | 18 => -128
  | 19 => -128
  | 20 => -128
  | 21 => -128
  | 22 => -128
  | 24 => 1
  | 26 => 1
  | 34 => 1
  | 35 => 1
  | 38 => -26
  | 39 => -26
  | 40 => -25
  | 41 => -25
  | 42 => -26
  | 43 => -26
  | 44 => -26
  | 45 => -26
  | 46 => -26
  | 47 => -25
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private def w (i : Fin 48) : ℤ :=
  match i.val with
  | 0 => 715680
  | 1 => 1025715
  | 2 => 151888
  | 3 => 196488
  | 4 => 163152
  | 5 => 65827
  | 6 => 65827
  | 7 => 67494
  | 8 => 59307
  | 9 => 12183
  | 10 => 20370
  | 11 => 86061
  | 12 => 72465
  | 13 => 66420
  | 14 => 3957
  | 15 => 88203
  | 16 => 13959
  | 17 => 50244
  | 18 => 168905
  | 19 => 14327
  | 20 => 325726
  | 21 => 364000
  | 22 => 16452
  | 23 => 94248
  | 24 => 94248
  | 25 => 94248
  | 26 => 222804
  | 27 => 50682
  | 28 => 144930
  | 29 => 77874
  | 30 => 172122
  | 31 => 30678
  | 32 => 50682
  | 33 => 74244
  | 34 => 74244
  | 35 => 94248
  | 36 => 94248
  | 37 => 20004
  | 38 => 51120
  | 39 => 80016
  | 40 => 155845
  | 41 => 164071
  | 42 => 8187
  | 43 => 86061
  | 44 => 13596
  | 45 => 72465
  | 46 => 47124
  | 47 => 10002
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_weights : ∀ i : Fin 48, 0  ≤  w i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_coeff : ∀ j : Fin 60, 0  ≤  ∑ i : Fin 48, w i * A i j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem negative_rhs : (∑ i : Fin 48, w i * B i) < 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (v : Fin 60 → ℤ) (positive : ∀ j, 0  ≤  v j)
    (valid : ∀ i : Fin 48, ∑ j, A i j * v j  ≤  B i) : False :=
  CertifiedLinear.contradiction A B w v valid nonneg_weights positive nonneg_coeff negative_rhs
end IndependentCutLP.C014

namespace IndependentCutLP.C022low
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def A (i : Fin 53) (j : Fin 57) : ℤ :=
  match j.val with
  | 0 => match i.val with
    | 0 => 1
    | 3 => -12
    | 27 => 1
    | _ => 0
  | 1 => match i.val with
    | 0 => 1
    | 1 => 1
    | 4 => -11
    | 17 => -2
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 28 => 1
    | 42 => -1
    | 46 => -1
    | 48 => -1
    | 50 => -1
    | _ => 0
  | 2 => match i.val with
    | 0 => 1
    | 1 => 1
    | 5 => -11
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -3
    | 21 => -3
    | 29 => 1
    | 34 => -1
    | 39 => -1
    | 41 => -1
    | 43 => -1
    | 45 => -1
    | 47 => -1
    | 51 => -1
    | _ => 0
  | 3 => match i.val with
    | 0 => 1
    | 1 => 1
    | 6 => -11
    | 17 => -2
    | 18 => -1
    | 19 => -3
    | 20 => -1
    | 21 => -1
    | 30 => 1
    | 34 => -1
    | 39 => -1
    | 41 => -1
    | 43 => -1
    | 45 => -1
    | 49 => -1
    | 51 => -1
    | _ => 0
  | 4 => match i.val with
    | 0 => 1
    | 1 => 2
    | 17 => -3
    | 18 => -2
    | 19 => -4
    | 20 => -4
    | 21 => -4
    | 22 => 1
    | 34 => -2
    | 41 => -2
    | 43 => -2
    | 51 => -2
    | _ => 0
  | 5 => match i.val with
    | 0 => 1
    | 7 => -12
    | _ => 0
  | 6 => match i.val with
    | 0 => 1
    | 8 => -12
    | 23 => 1
    | _ => 0
  | 7 => match i.val with
    | 0 => 1
    | 1 => 1
    | 17 => -2
    | 18 => -1
    | 19 => -3
    | 20 => -1
    | 21 => -3
    | 34 => -1
    | 37 => -1
    | 39 => -1
    | 45 => -1
    | 48 => -1
    | 52 => -1
    | _ => 0
  | 8 => match i.val with
    | 0 => 1
    | 1 => 1
    | 9 => -11
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 24 => 1
    | 35 => -1
    | 41 => -1
    | 47 => -1
    | 49 => -1
    | _ => 0
  | 9 => match i.val with
    | 0 => 1
    | 1 => 1
    | 10 => -11
    | 17 => -2
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 25 => 1
    | 41 => -1
    | 46 => -1
    | 47 => -1
    | 49 => -1
    | _ => 0
  | 10 => match i.val with
    | 0 => 1
    | 1 => 2
    | 2 => -1
    | 11 => -10
    | 17 => -3
    | 18 => -2
    | 19 => -2
    | 20 => -2
    | 21 => -2
    | 26 => 1
    | 47 => -2
    | 49 => -2
    | _ => 0
  | 11 => match i.val with
    | 0 => 1
    | 12 => -12
    | 26 => 1
    | _ => 0
  | 12 => match i.val with
    | 0 => 1
    | 1 => 1
    | 13 => -11
    | 17 => -2
    | 18 => -1
    | 19 => -1
    | 20 => -3
    | 21 => -1
    | 36 => -1
    | 38 => -1
    | 46 => -1
    | 47 => -1
    | 49 => -1
    | 50 => -1
    | _ => 0
  | 13 => match i.val with
    | 0 => 1
    | 14 => -12
    | 28 => 1
    | _ => 0
  | 14 => match i.val with
    | 0 => 1
    | 1 => 1
    | 15 => -11
    | 17 => -1
    | 18 => -3
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 31 => 1
    | 35 => -1
    | 36 => -1
    | 40 => -1
    | 42 => -1
    | 44 => -1
    | 46 => -1
    | 47 => -1
    | 48 => -1
    | 50 => -1
    | _ => 0
  | 15 => match i.val with
    | 0 => 1
    | 1 => 1
    | 16 => -11
    | 17 => -2
    | 18 => -3
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 32 => 1
    | 35 => -1
    | 38 => -1
    | 40 => -1
    | 42 => -1
    | 44 => -1
    | 46 => -1
    | 48 => -1
    | 49 => -1
    | 50 => -1
    | _ => 0
  | 16 => match i.val with
    | 0 => 1
    | 1 => 2
    | 17 => -3
    | 18 => -6
    | 19 => -2
    | 20 => -2
    | 21 => -2
    | 33 => 1
    | 42 => -2
    | 44 => -2
    | 46 => -2
    | 50 => -2
    | _ => 0
  | 17 => match i.val with
    | 1 => 1
    | 3 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 37 => -1
    | 40 => -1
    | 45 => -1
    | 52 => -1
    | _ => 0
  | 18 => match i.val with
    | 1 => 1
    | 4 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 37 => -1
    | 39 => -1
    | 45 => -1
    | 52 => -1
    | _ => 0
  | 19 => match i.val with
    | 1 => 1
    | 5 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 39 => -1
    | 45 => -1
    | 49 => -1
    | _ => 0
  | 20 => match i.val with
    | 1 => 1
    | 6 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 39 => -1
    | 45 => -1
    | 47 => -1
    | _ => 0
  | 21 => match i.val with
    | 1 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 22 => -1
    | 47 => -1
    | 49 => -1
    | _ => 0
  | 22 => match i.val with
    | 1 => 1
    | 7 => 1
    | 8 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 40 => -1
    | 41 => -1
    | 46 => -1
    | 50 => -1
    | 51 => -1
    | _ => 0
  | 23 => match i.val with
    | 1 => 1
    | 7 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 42 => -1
    | 46 => -1
    | 50 => -1
    | _ => 0
  | 24 => match i.val with
    | 1 => 1
    | 7 => 1
    | 9 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 35 => -1
    | 43 => -1
    | 51 => -1
    | _ => 0
  | 25 => match i.val with
    | 1 => 1
    | 7 => 1
    | 10 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 43 => -1
    | 46 => -1
    | 51 => -1
    | _ => 0
  | 26 => match i.val with
    | 1 => 1
    | 7 => 1
    | 11 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 34 => -1
    | 41 => -1
    | 43 => -1
    | 51 => -1
    | _ => 0
  | 27 => match i.val with
    | 1 => 1
    | 8 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 23 => -1
    | 40 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 28 => match i.val with
    | 1 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 41 => -1
    | 43 => -1
    | 51 => -1
    | _ => 0
  | 29 => match i.val with
    | 1 => 1
    | 9 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 24 => -1
    | 35 => -1
    | 41 => -1
    | 42 => -1
    | 46 => -1
    | 50 => -1
    | _ => 0
  | 30 => match i.val with
    | 1 => 1
    | 10 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 25 => -1
    | 41 => -1
    | 42 => -1
    | 50 => -1
    | _ => 0
  | 31 => match i.val with
    | 1 => 1
    | 11 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 26 => -1
    | 42 => -1
    | 46 => -1
    | 50 => -1
    | _ => 0
  | 32 => match i.val with
    | 1 => 1
    | 8 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 43 => -1
    | 44 => -1
    | _ => 0
  | 33 => match i.val with
    | 1 => 1
    | 9 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 40 => -1
    | 41 => -1
    | 44 => -1
    | 46 => -1
    | 50 => -1
    | _ => 0
  | 34 => match i.val with
    | 1 => 1
    | 10 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 40 => -1
    | 41 => -1
    | 44 => -1
    | 50 => -1
    | _ => 0
  | 35 => match i.val with
    | 1 => 1
    | 11 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 40 => -1
    | 44 => -1
    | 46 => -1
    | 50 => -1
    | _ => 0
  | 36 => match i.val with
    | 1 => 1
    | 3 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 27 => -1
    | 39 => -1
    | 40 => -1
    | 47 => -1
    | 49 => -1
    | 52 => -1
    | _ => 0
  | 37 => match i.val with
    | 1 => 1
    | 4 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 28 => -1
    | 47 => -1
    | 49 => -1
    | 52 => -1
    | _ => 0
  | 38 => match i.val with
    | 1 => 1
    | 5 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 29 => -1
    | 37 => -1
    | 47 => -1
    | _ => 0
  | 39 => match i.val with
    | 1 => 1
    | 6 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 30 => -1
    | 37 => -1
    | 49 => -1
    | _ => 0
  | 40 => match i.val with
    | 1 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 37 => -1
    | 39 => -1
    | 45 => -1
    | _ => 0
  | 41 => match i.val with
    | 1 => 1
    | 12 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 36 => -1
    | 38 => -1
    | 40 => -1
    | 44 => -1
    | 48 => -1
    | 52 => -1
    | _ => 0
  | 42 => match i.val with
    | 1 => 1
    | 13 => 1
    | 14 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 38 => -1
    | 42 => -1
    | 48 => -1
    | 52 => -1
    | _ => 0
  | 43 => match i.val with
    | 1 => 1
    | 3 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 38 => -1
    | 39 => -1
    | 40 => -1
    | 47 => -1
    | _ => 0
  | 44 => match i.val with
    | 1 => 1
    | 4 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 31 => -1
    | 38 => -1
    | 47 => -1
    | _ => 0
  | 45 => match i.val with
    | 1 => 1
    | 6 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 37 => -1
    | 38 => -1
    | 52 => -1
    | _ => 0
  | 46 => match i.val with
    | 1 => 1
    | 12 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 36 => -1
    | 40 => -1
    | 44 => -1
    | 48 => -1
    | 49 => -1
    | _ => 0
  | 47 => match i.val with
    | 1 => 1
    | 13 => 1
    | 15 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 42 => -1
    | 48 => -1
    | 49 => -1
    | _ => 0
  | 48 => match i.val with
    | 1 => 1
    | 3 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 39 => -1
    | 40 => -1
    | 49 => -1
    | _ => 0
  | 49 => match i.val with
    | 1 => 1
    | 4 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 32 => -1
    | 36 => -1
    | 49 => -1
    | _ => 0
  | 50 => match i.val with
    | 1 => 1
    | 5 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 36 => -1
    | 37 => -1
    | 52 => -1
    | _ => 0
  | 51 => match i.val with
    | 1 => 1
    | 12 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 38 => -1
    | 40 => -1
    | 44 => -1
    | 47 => -1
    | 48 => -1
    | _ => 0
  | 52 => match i.val with
    | 1 => 1
    | 13 => 1
    | 16 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 38 => -1
    | 42 => -1
    | 47 => -1
    | 48 => -1
    | _ => 0
  | 53 => match i.val with
    | 1 => 1
    | 3 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 36 => -1
    | 38 => -1
    | 39 => -1
    | 48 => -1
    | _ => 0
  | 54 => match i.val with
    | 1 => 1
    | 4 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 36 => -1
    | 38 => -1
    | 40 => -1
    | 48 => -1
    | _ => 0
  | 55 => match i.val with
    | 1 => 1
    | 12 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 33 => -1
    | 44 => -1
    | 47 => -1
    | 49 => -1
    | _ => 0
  | 56 => match i.val with
    | 1 => 1
    | 13 => 1
    | 17 => -1
    | 18 => -1
    | 19 => -1
    | 20 => -1
    | 21 => -1
    | 35 => -1
    | 40 => -1
    | 42 => -1
    | 47 => -1
    | 49 => -1
    | _ => 0
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def B (i : Fin 53) : ℤ :=
  match i.val with
  | 0 => 22
  | 1 => 115
  | 2 => -1
  | 17 => -129
  | 18 => -128
  | 19 => -128
  | 20 => -126
  | 21 => -128
  | 26 => 1
  | 28 => 1
  | 34 => -26
  | 35 => -24
  | 36 => -24
  | 37 => -26
  | 38 => -24
  | 39 => -26
  | 40 => -24
  | 41 => -26
  | 42 => -26
  | 43 => -26
  | 44 => -24
  | 45 => -26
  | 46 => -26
  | 47 => -26
  | 48 => -26
  | 49 => -26
  | 50 => -26
  | 51 => -26
  | 52 => -26
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private def w (i : Fin 53) : ℤ :=
  match i.val with
  | 0 => 3214752
  | 1 => 3654892
  | 2 => 952032
  | 3 => 298056
  | 4 => 298056
  | 5 => 45553
  | 6 => 187
  | 7 => 267896
  | 8 => 307800
  | 9 => 307800
  | 10 => 307800
  | 11 => 307800
  | 12 => 319196
  | 13 => 11396
  | 14 => 322816
  | 15 => 48029
  | 16 => 2663
  | 17 => 362928
  | 18 => 781768
  | 19 => 562408
  | 20 => 220556
  | 21 => 341852
  | 22 => 549200
  | 23 => 478848
  | 24 => 252672
  | 25 => 615600
  | 26 => 615600
  | 27 => 522288
  | 28 => 659040
  | 29 => 640306
  | 30 => 549574
  | 31 => 595738
  | 32 => 505006
  | 33 => 499680
  | 34 => 256500
  | 35 => 181464
  | 36 => 606372
  | 37 => 584088
  | 38 => 606372
  | 39 => 68376
  | 40 => 68376
  | 41 => 181464
  | 42 => 42860
  | 43 => 1422292
  | 44 => 100820
  | 45 => 1055732
  | 46 => 181464
  | 47 => 529355
  | 48 => 220852
  | 49 => 574721
  | 50 => 1172452
  | 51 => 100820
  | 52 => 243136
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_weights : ∀ i : Fin 53, 0  ≤  w i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_coeff : ∀ j : Fin 57, 0  ≤  ∑ i : Fin 53, w i * A i j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem negative_rhs : (∑ i : Fin 53, w i * B i) < 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (v : Fin 57 → ℤ) (positive : ∀ j, 0  ≤  v j)
    (valid : ∀ i : Fin 53, ∑ j, A i j * v j  ≤  B i) : False :=
  CertifiedLinear.contradiction A B w v valid nonneg_weights positive nonneg_coeff negative_rhs
end IndependentCutLP.C022low

namespace IndependentCutLP.C022high
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def A (i : Fin 53) (j : Fin 57) : ℤ :=
  match j.val with
  | 0 => match i.val with
    | 0 => 1
    | 3 => -11
    | 17 => 1
    | _ => 0
  | 1 => match i.val with
    | 0 => 1
    | 1 => 1
    | 4 => -10
    | 18 => 1
    | 35 => -1
    | 41 => -1
    | 42 => -1
    | 45 => -1
    | _ => 0
  | 2 => match i.val with
    | 0 => 1
    | 1 => 1
    | 19 => 1
    | 24 => -1
    | 31 => -1
    | 32 => -1
    | 37 => -1
    | 39 => -1
    | 40 => -1
    | 46 => -1
    | 47 => -1
    | 49 => -1
    | 51 => -1
    | _ => 0
  | 3 => match i.val with
    | 0 => 1
    | 1 => 1
    | 20 => 1
    | 24 => -1
    | 25 => -1
    | 31 => -1
    | 32 => -1
    | 37 => -1
    | 39 => -1
    | 43 => -1
    | 46 => -1
    | 47 => -1
    | 48 => -1
    | 49 => -1
    | 52 => -1
    | _ => 0
  | 4 => match i.val with
    | 0 => 1
    | 1 => 2
    | 12 => 1
    | 24 => -2
    | 32 => -2
    | 34 => -1
    | 36 => -1
    | 37 => -2
    | 44 => -1
    | 46 => -2
    | 47 => -2
    | 48 => -2
    | 49 => -2
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 5 => match i.val with
    | 0 => 1
    | 5 => -11
    | _ => 0
  | 6 => match i.val with
    | 0 => 1
    | 6 => -11
    | 13 => 1
    | _ => 0
  | 7 => match i.val with
    | 0 => 1
    | 1 => 1
    | 24 => -1
    | 25 => -1
    | 28 => -1
    | 31 => -1
    | 39 => -1
    | 41 => -1
    | 42 => -1
    | 48 => -1
    | _ => 0
  | 8 => match i.val with
    | 0 => 1
    | 1 => 1
    | 7 => -10
    | 14 => 1
    | 25 => -1
    | 26 => -1
    | 29 => -1
    | 32 => -1
    | 36 => -1
    | 40 => -1
    | 43 => -1
    | 47 => -1
    | _ => 0
  | 9 => match i.val with
    | 0 => 1
    | 1 => 1
    | 8 => -10
    | 15 => 1
    | 25 => -1
    | 29 => -1
    | 32 => -1
    | 33 => -1
    | 34 => -1
    | 40 => -1
    | 43 => -1
    | 44 => -1
    | 46 => -1
    | 47 => -1
    | 50 => -1
    | _ => 0
  | 10 => match i.val with
    | 0 => 1
    | 1 => 2
    | 2 => -1
    | 9 => -9
    | 16 => 1
    | 29 => -2
    | 34 => -1
    | 36 => -1
    | 40 => -2
    | 43 => -2
    | 44 => -1
    | 47 => -2
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 11 => match i.val with
    | 0 => 1
    | 10 => -11
    | 16 => 1
    | _ => 0
  | 12 => match i.val with
    | 0 => 1
    | 1 => 1
    | 27 => -1
    | 29 => -1
    | 30 => -1
    | 34 => -1
    | 36 => -1
    | 40 => -1
    | 43 => -1
    | 44 => -1
    | 45 => -1
    | 50 => -1
    | _ => 0
  | 13 => match i.val with
    | 0 => 1
    | 11 => -11
    | 18 => 1
    | _ => 0
  | 14 => match i.val with
    | 0 => 1
    | 1 => 1
    | 21 => 1
    | 26 => -1
    | 27 => -1
    | 29 => -1
    | 33 => -1
    | 35 => -1
    | 38 => -1
    | 40 => -1
    | 42 => -1
    | 45 => -1
    | 52 => -1
    | _ => 0
  | 15 => match i.val with
    | 0 => 1
    | 1 => 1
    | 22 => 1
    | 26 => -1
    | 29 => -1
    | 30 => -1
    | 33 => -1
    | 35 => -1
    | 38 => -1
    | 42 => -1
    | 43 => -1
    | 45 => -1
    | 51 => -1
    | _ => 0
  | 16 => match i.val with
    | 0 => 1
    | 1 => 2
    | 23 => 1
    | 33 => -2
    | 34 => -1
    | 35 => -2
    | 36 => -1
    | 38 => -2
    | 44 => -1
    | 45 => -2
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 17 => match i.val with
    | 1 => 1
    | 3 => 1
    | 5 => 1
    | 25 => -1
    | 28 => -1
    | 34 => -1
    | 39 => -1
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 18 => match i.val with
    | 1 => 1
    | 4 => 1
    | 5 => 1
    | 25 => -1
    | 28 => -1
    | 31 => -1
    | 39 => -1
    | 48 => -1
    | _ => 0
  | 19 => match i.val with
    | 1 => 1
    | 5 => 1
    | 29 => -1
    | 31 => -1
    | 36 => -1
    | 39 => -1
    | 43 => -1
    | _ => 0
  | 20 => match i.val with
    | 1 => 1
    | 5 => 1
    | 25 => -1
    | 29 => -1
    | 31 => -1
    | 34 => -1
    | 39 => -1
    | 40 => -1
    | 44 => -1
    | 48 => -1
    | 50 => -1
    | _ => 0
  | 21 => match i.val with
    | 1 => 1
    | 5 => 1
    | 12 => -1
    | 29 => -1
    | 34 => -1
    | 36 => -1
    | 40 => -1
    | 43 => -1
    | 44 => -1
    | 48 => -1
    | 50 => -1
    | _ => 0
  | 22 => match i.val with
    | 1 => 1
    | 5 => 1
    | 6 => 1
    | 24 => -1
    | 32 => -1
    | 45 => -1
    | 46 => -1
    | 49 => -1
    | _ => 0
  | 23 => match i.val with
    | 1 => 1
    | 5 => 1
    | 24 => -1
    | 35 => -1
    | 45 => -1
    | _ => 0
  | 24 => match i.val with
    | 1 => 1
    | 5 => 1
    | 7 => 1
    | 24 => -1
    | 25 => -1
    | 26 => -1
    | 37 => -1
    | 46 => -1
    | 49 => -1
    | 51 => -1
    | _ => 0
  | 25 => match i.val with
    | 1 => 1
    | 5 => 1
    | 8 => 1
    | 24 => -1
    | 25 => -1
    | 33 => -1
    | 37 => -1
    | 49 => -1
    | 52 => -1
    | _ => 0
  | 26 => match i.val with
    | 1 => 1
    | 5 => 1
    | 9 => 1
    | 24 => -1
    | 32 => -1
    | 37 => -1
    | 46 => -1
    | 49 => -1
    | _ => 0
  | 27 => match i.val with
    | 1 => 1
    | 6 => 1
    | 10 => 1
    | 13 => -1
    | 35 => -1
    | 37 => -1
    | _ => 0
  | 28 => match i.val with
    | 1 => 1
    | 10 => 1
    | 32 => -1
    | 37 => -1
    | 46 => -1
    | 49 => -1
    | _ => 0
  | 29 => match i.val with
    | 1 => 1
    | 7 => 1
    | 10 => 1
    | 14 => -1
    | 25 => -1
    | 26 => -1
    | 32 => -1
    | 35 => -1
    | 45 => -1
    | 51 => -1
    | _ => 0
  | 30 => match i.val with
    | 1 => 1
    | 8 => 1
    | 10 => 1
    | 15 => -1
    | 25 => -1
    | 32 => -1
    | 33 => -1
    | 35 => -1
    | 45 => -1
    | 46 => -1
    | 52 => -1
    | _ => 0
  | 31 => match i.val with
    | 1 => 1
    | 9 => 1
    | 10 => 1
    | 16 => -1
    | 35 => -1
    | 45 => -1
    | _ => 0
  | 32 => match i.val with
    | 1 => 1
    | 6 => 1
    | 26 => -1
    | 33 => -1
    | 37 => -1
    | 38 => -1
    | 47 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 33 => match i.val with
    | 1 => 1
    | 7 => 1
    | 25 => -1
    | 32 => -1
    | 33 => -1
    | 38 => -1
    | 45 => -1
    | 47 => -1
    | 52 => -1
    | _ => 0
  | 34 => match i.val with
    | 1 => 1
    | 8 => 1
    | 25 => -1
    | 26 => -1
    | 32 => -1
    | 38 => -1
    | 45 => -1
    | 46 => -1
    | 47 => -1
    | 51 => -1
    | _ => 0
  | 35 => match i.val with
    | 1 => 1
    | 9 => 1
    | 26 => -1
    | 33 => -1
    | 38 => -1
    | 45 => -1
    | 47 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 36 => match i.val with
    | 1 => 1
    | 3 => 1
    | 11 => 1
    | 17 => -1
    | 29 => -1
    | 31 => -1
    | 36 => -1
    | 40 => -1
    | 43 => -1
    | 44 => -1
    | 48 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 37 => match i.val with
    | 1 => 1
    | 4 => 1
    | 11 => 1
    | 18 => -1
    | 29 => -1
    | 34 => -1
    | 36 => -1
    | 40 => -1
    | 43 => -1
    | 44 => -1
    | 50 => -1
    | _ => 0
  | 38 => match i.val with
    | 1 => 1
    | 11 => 1
    | 19 => -1
    | 25 => -1
    | 28 => -1
    | 34 => -1
    | 40 => -1
    | 44 => -1
    | 48 => -1
    | 50 => -1
    | _ => 0
  | 39 => match i.val with
    | 1 => 1
    | 11 => 1
    | 20 => -1
    | 28 => -1
    | 36 => -1
    | 43 => -1
    | _ => 0
  | 40 => match i.val with
    | 1 => 1
    | 11 => 1
    | 25 => -1
    | 28 => -1
    | 31 => -1
    | 39 => -1
    | _ => 0
  | 41 => match i.val with
    | 1 => 1
    | 10 => 1
    | 11 => 1
    | 26 => -1
    | 27 => -1
    | 30 => -1
    | 33 => -1
    | 38 => -1
    | 41 => -1
    | 42 => -1
    | 47 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 42 => match i.val with
    | 1 => 1
    | 11 => 1
    | 27 => -1
    | 30 => -1
    | 35 => -1
    | 41 => -1
    | 42 => -1
    | _ => 0
  | 43 => match i.val with
    | 1 => 1
    | 3 => 1
    | 29 => -1
    | 30 => -1
    | 31 => -1
    | 40 => -1
    | 41 => -1
    | 44 => -1
    | 48 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 44 => match i.val with
    | 1 => 1
    | 4 => 1
    | 21 => -1
    | 29 => -1
    | 30 => -1
    | 34 => -1
    | 40 => -1
    | 41 => -1
    | 44 => -1
    | 50 => -1
    | _ => 0
  | 45 => match i.val with
    | 1 => 1
    | 28 => -1
    | 30 => -1
    | 41 => -1
    | _ => 0
  | 46 => match i.val with
    | 1 => 1
    | 10 => 1
    | 26 => -1
    | 27 => -1
    | 33 => -1
    | 36 => -1
    | 38 => -1
    | 42 => -1
    | 43 => -1
    | 47 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 47 => match i.val with
    | 1 => 1
    | 27 => -1
    | 35 => -1
    | 36 => -1
    | 42 => -1
    | 43 => -1
    | _ => 0
  | 48 => match i.val with
    | 1 => 1
    | 3 => 1
    | 27 => -1
    | 29 => -1
    | 31 => -1
    | 34 => -1
    | 36 => -1
    | 41 => -1
    | 43 => -1
    | 48 => -1
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 49 => match i.val with
    | 1 => 1
    | 4 => 1
    | 22 => -1
    | 27 => -1
    | 29 => -1
    | 36 => -1
    | 41 => -1
    | 43 => -1
    | _ => 0
  | 50 => match i.val with
    | 1 => 1
    | 25 => -1
    | 27 => -1
    | 28 => -1
    | 41 => -1
    | 48 => -1
    | _ => 0
  | 51 => match i.val with
    | 1 => 1
    | 10 => 1
    | 26 => -1
    | 30 => -1
    | 33 => -1
    | 34 => -1
    | 38 => -1
    | 40 => -1
    | 42 => -1
    | 44 => -1
    | 47 => -1
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 52 => match i.val with
    | 1 => 1
    | 30 => -1
    | 34 => -1
    | 35 => -1
    | 40 => -1
    | 42 => -1
    | 44 => -1
    | 50 => -1
    | _ => 0
  | 53 => match i.val with
    | 1 => 1
    | 3 => 1
    | 26 => -1
    | 27 => -1
    | 30 => -1
    | 31 => -1
    | 41 => -1
    | 42 => -1
    | 44 => -1
    | 48 => -1
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 54 => match i.val with
    | 1 => 1
    | 4 => 1
    | 26 => -1
    | 27 => -1
    | 30 => -1
    | 34 => -1
    | 41 => -1
    | 42 => -1
    | 44 => -1
    | _ => 0
  | 55 => match i.val with
    | 1 => 1
    | 10 => 1
    | 23 => -1
    | 29 => -1
    | 33 => -1
    | 36 => -1
    | 38 => -1
    | 40 => -1
    | 43 => -1
    | 47 => -1
    | 50 => -1
    | 51 => -1
    | 52 => -1
    | _ => 0
  | 56 => match i.val with
    | 1 => 1
    | 26 => -1
    | 29 => -1
    | 35 => -1
    | 36 => -1
    | 40 => -1
    | 43 => -1
    | 50 => -1
    | _ => 0
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def B (i : Fin 53) : ℤ :=
  match i.val with
  | 0 => 22
  | 1 => 119
  | 2 => -1
  | 16 => 1
  | 18 => 1
  | 24 => -26
  | 25 => -26
  | 26 => -24
  | 27 => -24
  | 28 => -26
  | 29 => -26
  | 30 => -24
  | 31 => -26
  | 32 => -26
  | 33 => -24
  | 34 => -25
  | 35 => -26
  | 36 => -25
  | 37 => -26
  | 38 => -24
  | 39 => -26
  | 40 => -26
  | 41 => -26
  | 42 => -26
  | 43 => -26
  | 44 => -25
  | 45 => -26
  | 46 => -26
  | 47 => -26
  | 48 => -26
  | 49 => -26
  | 50 => -25
  | 51 => -25
  | 52 => -25
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private def w (i : Fin 53) : ℤ :=
  match i.val with
  | 0 => 9882972
  | 1 => 12469476
  | 2 => 9034716
  | 3 => 1253272
  | 4 => 609120
  | 5 => 898452
  | 6 => 1098108
  | 7 => 1204070
  | 8 => 1204070
  | 9 => 1098108
  | 10 => 1098108
  | 11 => 1233468
  | 12 => 2466936
  | 13 => 2196216
  | 14 => 442746
  | 15 => 62680
  | 16 => 2196216
  | 17 => 3903020
  | 18 => 3685176
  | 19 => 2466936
  | 20 => 2466936
  | 21 => 1218240
  | 22 => 1218240
  | 23 => 1218240
  | 24 => 898452
  | 25 => 105962
  | 26 => 609120
  | 27 => 1180487
  | 28 => 6451490
  | 29 => 1437918
  | 30 => 1560553
  | 31 => 335016
  | 32 => 876735
  | 33 => 799153
  | 34 => 609120
  | 35 => 3484956
  | 36 => 3120542
  | 37 => 8984520
  | 38 => 1743362
  | 39 => 6810476
  | 40 => 2044042
  | 41 => 4457433
  | 42 => 3019515
  | 43 => 1663976
  | 44 => 1642368
  | 45 => 8984520
  | 46 => 190033
  | 47 => 896199
  | 48 => 274104
  | 49 => 3516296
  | 50 => 108922
  | 51 => 267615
  | 52 => 267615
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_weights : ∀ i : Fin 53, 0  ≤  w i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_coeff : ∀ j : Fin 57, 0  ≤  ∑ i : Fin 53, w i * A i j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem negative_rhs : (∑ i : Fin 53, w i * B i) < 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (v : Fin 57 → ℤ) (positive : ∀ j, 0  ≤  v j)
    (valid : ∀ i : Fin 53, ∑ j, A i j * v j  ≤  B i) : False :=
  CertifiedLinear.contradiction A B w v valid nonneg_weights positive nonneg_coeff negative_rhs
end IndependentCutLP.C022high

namespace IndependentCutLP.C023
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def A (i : Fin 42) (j : Fin 51) : ℤ :=
  match j.val with
  | 0 => match i.val with
    | 0 => 1
    | 5 => -12
    | 17 => 1
    | 23 => 1
    | _ => 0
  | 1 => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => -1
    | 6 => -11
    | 18 => 1
    | 24 => 1
    | 28 => -1
    | 31 => -1
    | 32 => -1
    | _ => 0
  | 2 => match i.val with
    | 0 => 1
    | 1 => 1
    | 7 => -11
    | 27 => -1
    | 29 => -1
    | 37 => -1
    | 39 => -1
    | 41 => -1
    | _ => 0
  | 3 => match i.val with
    | 0 => 1
    | 1 => 1
    | 8 => -11
    | 30 => -1
    | 33 => -1
    | 39 => -1
    | 40 => -1
    | 41 => -1
    | _ => 0
  | 4 => match i.val with
    | 0 => 1
    | 1 => 2
    | 19 => 1
    | 25 => 1
    | 27 => -1
    | 33 => -1
    | 34 => -1
    | 35 => -1
    | 36 => -1
    | 37 => -1
    | 38 => -1
    | 40 => -1
    | _ => 0
  | 5 => match i.val with
    | 0 => 1
    | 9 => -12
    | 18 => 1
    | _ => 0
  | 6 => match i.val with
    | 0 => 1
    | 1 => 1
    | 26 => -1
    | 27 => -1
    | 31 => -1
    | 32 => -1
    | _ => 0
  | 7 => match i.val with
    | 0 => 1
    | 10 => -12
    | 21 => 1
    | _ => 0
  | 8 => match i.val with
    | 0 => 1
    | 1 => 1
    | 11 => -11
    | 29 => -1
    | 31 => -1
    | 35 => -1
    | 36 => -1
    | 37 => -1
    | 39 => -1
    | _ => 0
  | 9 => match i.val with
    | 0 => 1
    | 1 => 1
    | 3 => -1
    | 12 => -11
    | 22 => 1
    | 28 => -1
    | 30 => -1
    | 41 => -1
    | _ => 0
  | 10 => match i.val with
    | 0 => 1
    | 13 => -12
    | 20 => 1
    | _ => 0
  | 11 => match i.val with
    | 0 => 1
    | 1 => 1
    | 14 => -11
    | 28 => -1
    | 30 => -1
    | 34 => -1
    | 38 => -1
    | 40 => -1
    | 41 => -1
    | _ => 0
  | 12 => match i.val with
    | 0 => 1
    | 1 => 1
    | 4 => -1
    | 15 => -11
    | 22 => 1
    | 29 => -1
    | 31 => -1
    | 39 => -1
    | _ => 0
  | 13 => match i.val with
    | 0 => 1
    | 16 => -12
    | 24 => 1
    | _ => 0
  | 14 => match i.val with
    | 0 => 1
    | 1 => 1
    | 26 => -1
    | 28 => -1
    | 32 => -1
    | 33 => -1
    | _ => 0
  | 15 => match i.val with
    | 1 => 1
    | 5 => 1
    | 9 => 1
    | 17 => -1
    | 29 => -1
    | 38 => -1
    | 39 => -1
    | _ => 0
  | 16 => match i.val with
    | 1 => 1
    | 6 => 1
    | 9 => 1
    | 18 => -1
    | 29 => -1
    | 36 => -1
    | 39 => -1
    | _ => 0
  | 17 => match i.val with
    | 1 => 1
    | 7 => 1
    | 9 => 1
    | 29 => -1
    | 30 => -1
    | 35 => -1
    | 39 => -1
    | _ => 0
  | 18 => match i.val with
    | 1 => 1
    | 8 => 1
    | 9 => 1
    | 34 => -1
    | 36 => -1
    | 38 => -1
    | 39 => -1
    | _ => 0
  | 19 => match i.val with
    | 1 => 1
    | 9 => 1
    | 19 => -1
    | 30 => -1
    | 38 => -1
    | 41 => -1
    | _ => 0
  | 20 => match i.val with
    | 1 => 1
    | 5 => 1
    | 28 => -1
    | 35 => -1
    | 37 => -1
    | 38 => -1
    | _ => 0
  | 21 => match i.val with
    | 1 => 1
    | 6 => 1
    | 28 => -1
    | 35 => -1
    | 36 => -1
    | 37 => -1
    | _ => 0
  | 22 => match i.val with
    | 1 => 1
    | 7 => 1
    | 28 => -1
    | 30 => -1
    | 37 => -1
    | _ => 0
  | 23 => match i.val with
    | 1 => 1
    | 9 => 1
    | 10 => 1
    | 27 => -1
    | 28 => -1
    | 35 => -1
    | 37 => -1
    | _ => 0
  | 24 => match i.val with
    | 1 => 1
    | 10 => 1
    | 27 => -1
    | 29 => -1
    | 39 => -1
    | _ => 0
  | 25 => match i.val with
    | 1 => 1
    | 9 => 1
    | 11 => 1
    | 28 => -1
    | 32 => -1
    | 35 => -1
    | 37 => -1
    | _ => 0
  | 26 => match i.val with
    | 1 => 1
    | 11 => 1
    | 29 => -1
    | 32 => -1
    | 39 => -1
    | _ => 0
  | 27 => match i.val with
    | 1 => 1
    | 9 => 1
    | 12 => 1
    | 27 => -1
    | 28 => -1
    | 35 => -1
    | 37 => -1
    | _ => 0
  | 28 => match i.val with
    | 1 => 1
    | 12 => 1
    | 27 => -1
    | 29 => -1
    | 39 => -1
    | _ => 0
  | 29 => match i.val with
    | 1 => 1
    | 10 => 1
    | 13 => 1
    | 26 => -1
    | 32 => -1
    | _ => 0
  | 30 => match i.val with
    | 1 => 1
    | 11 => 1
    | 13 => 1
    | 26 => -1
    | 27 => -1
    | _ => 0
  | 31 => match i.val with
    | 1 => 1
    | 12 => 1
    | 13 => 1
    | 20 => -1
    | 26 => -1
    | 32 => -1
    | _ => 0
  | 32 => match i.val with
    | 1 => 1
    | 10 => 1
    | 14 => 1
    | 26 => -1
    | 33 => -1
    | _ => 0
  | 33 => match i.val with
    | 1 => 1
    | 12 => 1
    | 14 => 1
    | 26 => -1
    | 33 => -1
    | _ => 0
  | 34 => match i.val with
    | 1 => 1
    | 10 => 1
    | 15 => 1
    | 21 => -1
    | 26 => -1
    | 32 => -1
    | _ => 0
  | 35 => match i.val with
    | 1 => 1
    | 11 => 1
    | 15 => 1
    | 26 => -1
    | 27 => -1
    | _ => 0
  | 36 => match i.val with
    | 1 => 1
    | 12 => 1
    | 15 => 1
    | 22 => -1
    | 26 => -1
    | 32 => -1
    | _ => 0
  | 37 => match i.val with
    | 1 => 1
    | 5 => 1
    | 16 => 1
    | 23 => -1
    | 30 => -1
    | 36 => -1
    | 41 => -1
    | _ => 0
  | 38 => match i.val with
    | 1 => 1
    | 6 => 1
    | 16 => 1
    | 24 => -1
    | 30 => -1
    | 38 => -1
    | 41 => -1
    | _ => 0
  | 39 => match i.val with
    | 1 => 1
    | 7 => 1
    | 16 => 1
    | 35 => -1
    | 36 => -1
    | 38 => -1
    | 41 => -1
    | _ => 0
  | 40 => match i.val with
    | 1 => 1
    | 8 => 1
    | 16 => 1
    | 29 => -1
    | 30 => -1
    | 34 => -1
    | 41 => -1
    | _ => 0
  | 41 => match i.val with
    | 1 => 1
    | 16 => 1
    | 25 => -1
    | 29 => -1
    | 36 => -1
    | 39 => -1
    | _ => 0
  | 42 => match i.val with
    | 1 => 1
    | 13 => 1
    | 16 => 1
    | 31 => -1
    | 33 => -1
    | 34 => -1
    | 40 => -1
    | _ => 0
  | 43 => match i.val with
    | 1 => 1
    | 14 => 1
    | 16 => 1
    | 31 => -1
    | 32 => -1
    | 34 => -1
    | 40 => -1
    | _ => 0
  | 44 => match i.val with
    | 1 => 1
    | 15 => 1
    | 16 => 1
    | 31 => -1
    | 33 => -1
    | 34 => -1
    | 40 => -1
    | _ => 0
  | 45 => match i.val with
    | 1 => 1
    | 5 => 1
    | 31 => -1
    | 34 => -1
    | 36 => -1
    | 40 => -1
    | _ => 0
  | 46 => match i.val with
    | 1 => 1
    | 6 => 1
    | 31 => -1
    | 34 => -1
    | 38 => -1
    | 40 => -1
    | _ => 0
  | 47 => match i.val with
    | 1 => 1
    | 8 => 1
    | 29 => -1
    | 31 => -1
    | 40 => -1
    | _ => 0
  | 48 => match i.val with
    | 1 => 1
    | 13 => 1
    | 30 => -1
    | 33 => -1
    | 41 => -1
    | _ => 0
  | 49 => match i.val with
    | 1 => 1
    | 14 => 1
    | 30 => -1
    | 32 => -1
    | 41 => -1
    | _ => 0
  | 50 => match i.val with
    | 1 => 1
    | 15 => 1
    | 30 => -1
    | 33 => -1
    | 41 => -1
    | _ => 0
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
def B (i : Fin 42) : ℤ :=
  match i.val with
  | 0 => 22
  | 1 => 119
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 18 => 1
  | 22 => 1
  | 24 => 1
  | 26 => -24
  | 27 => -25
  | 28 => -26
  | 29 => -26
  | 30 => -26
  | 31 => -26
  | 32 => -26
  | 33 => -25
  | 34 => -25
  | 35 => -25
  | 36 => -25
  | 37 => -25
  | 38 => -25
  | 39 => -26
  | 40 => -25
  | 41 => -26
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private def w (i : Fin 42) : ℤ :=
  match i.val with
  | 0 => 3060
  | 1 => 4405
  | 2 => 1228
  | 3 => 1428
  | 4 => 1428
  | 5 => 357
  | 6 => 357
  | 7 => 51
  | 8 => 51
  | 9 => 306
  | 10 => 302
  | 11 => 20
  | 12 => 302
  | 13 => 302
  | 14 => 20
  | 15 => 302
  | 16 => 306
  | 17 => 612
  | 18 => 612
  | 19 => 255
  | 20 => 564
  | 21 => 564
  | 22 => 564
  | 23 => 612
  | 24 => 612
  | 25 => 255
  | 26 => 2503
  | 27 => 2224
  | 28 => 796
  | 29 => 1973
  | 30 => 1973
  | 31 => 796
  | 32 => 1942
  | 33 => 2224
  | 34 => 306
  | 35 => 306
  | 36 => 1973
  | 37 => 1687
  | 38 => 1973
  | 39 => 510
  | 40 => 1687
  | 41 => 510
  | _ => 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_weights : ∀ i : Fin 42, 0  ≤  w i := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem nonneg_coeff : ∀ j : Fin 51, 0  ≤  ∑ i : Fin 42, w i * A i j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem negative_rhs : (∑ i : Fin 42, w i * B i) < 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (v : Fin 51 → ℤ) (positive : ∀ j, 0  ≤  v j)
    (valid : ∀ i : Fin 42, ∑ j, A i j * v j  ≤  B i) : False :=
  CertifiedLinear.contradiction A B w v valid nonneg_weights positive nonneg_coeff negative_rhs
end IndependentCutLP.C023

-- DecideAllowed

namespace ThreeExceptions
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
instance allowedDecidable (t : Fin 3 → Fin 5) (a b : Slot) : Decidable (Allowed t a b) := by
  cases a <;> cases b <;> unfold Allowed <;> infer_instance
end ThreeExceptions

-- Affine

namespace CertifiedAffine
open Finset

inductive Form (n : ℕ) where
  | c : ℤ → Form n
  | var : Fin n → Form n
  | plus : Form n → Form n → Form n
  | scale : ℤ → Form n → Form n
  | fsum : (m : ℕ) → (Fin m → Form n) → Form n

def Form.eval {n : ℕ} (v : Fin n → ℤ) : Form n → ℤ
  | .c z => z
  | .var j => v j
  | .plus a b => a.eval v+b.eval v
  | .scale z a => z*a.eval v
  | .fsum _ f => ∑i,(f i).eval v

def Form.constant {n : ℕ} : Form n → ℤ
  | .c z => z
  | .var _ => 0
  | .plus a b => a.constant+b.constant
  | .scale z a => z*a.constant
  | .fsum _ f => ∑i,(f i).constant

def Form.coeff {n : ℕ} : Form n → Fin n → ℤ
  | .c _,_ => 0
  | .var i,j => if i=j then 1 else 0
  | .plus a b,j => a.coeff j+b.coeff j
  | .scale z a,j => z*a.coeff j
  | .fsum _ f,j => ∑i,(f i).coeff j

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem Form.sound {n : ℕ} (t : Form n) (v : Fin n → ℤ) :
    t.eval v=t.constant+∑j,t.coeff j*v j := by
  classical
  induction t with
  | c z => simp [eval,constant,coeff]
  | var i => simp [eval,constant,coeff,ite_mul]
  | plus a b ha hb =>
    simp only [eval,constant,coeff,ha,hb,add_mul,sum_add_distrib]
    ring
  | scale z a ha =>
    simp only [eval,constant,coeff,ha,mul_add,mul_sum,mul_assoc]
  | fsum m f ih =>
    simp only [eval,constant,coeff]
    simp_rw [ih]
    rw [sum_add_distrib]
    congr 1
    simp_rw [sum_mul]
    exact sum_comm

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem of_eval_le {n : ℕ} (t : Form n) (A : Fin n → ℤ) (B r : ℤ) (v : Fin n → ℤ)
    (coefficient : ∀j,t.coeff j=A j) (constant : r-t.constant=B)
    (h : t.eval v ≤ r) : (∑j,A j*v j) ≤ B := by
  rw [t.sound] at h
  simp_rw [coefficient] at h
  omega

end CertifiedAffine

-- AffineModel

namespace AffineCut
open Finset CertifiedAffine ThreeExceptions FiniteCutTemplate GraphMass CutSummary
variable {n e : ℕ} {t : Fin 3 → Fin 5}

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_plus {q : ℕ} (v : Fin q → ℤ) (a b : Form q) :
    (Form.plus a b).eval v=a.eval v+b.eval v := rfl
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_scale {q : ℕ} (v : Fin q → ℤ) (z : ℤ) (a : Form q) :
    (Form.scale z a).eval v=z*a.eval v := rfl

def flat (N : Fin n → ℤ) (E : Fin e → ℤ) (j : Fin (n+e)) : ℤ :=
  Fin.addCases (motive:=fun _ => ℤ) N E j

def nv (a : Fin n) : Form (n+e) := .var (Fin.castAdd e a)
def ev (k : Fin e) : Form (n+e) := .var (Fin.natAdd n k)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_nv (N : Fin n → ℤ) (E : Fin e → ℤ) (a : Fin n) :
    (nv (e:=e) a).eval (flat N E)=N a := by simp [nv,Form.eval,flat]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_ev (N : Fin n → ℤ) (E : Fin e → ℤ) (k : Fin e) :
    (ev (n:=n) k).eval (flat N E)=E k := by simp [ev,Form.eval,flat]

def verticesForm : Form (n+e) := .fsum n (fun a => nv a)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_vertices (N : Fin n → ℤ) (E : Fin e → ℤ) :
    (verticesForm (n:=n) (e:=e)).eval (flat N E)=∑a,N a := by
  simp only [verticesForm,Form.eval,eval_nv]

def halfForm (T : Table t n e) (F : (Fin n ⊕ Fin 3) → (Fin n ⊕ Fin 3) → ℤ) : Form (n+e) :=
  .plus (.plus
    (.fsum e (fun k => .scale (F (.inl (T.ends k).1) (.inl (T.ends k).2)) (ev k)))
    (.fsum n (fun a => .fsum 3 (fun x => if (T.slot a).2 x then
      .scale (F (.inl a) (.inr x)) (nv a) else .c 0))))
    (.c (F (.inr 0) (.inr 1)+F (.inr 0) (.inr 2)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_half (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) (F) :
    (halfForm T F).eval (flat N E)=half T N E F := by
  classical
  simp only [halfForm,Form.eval,apply_ite,eval_nv,eval_ev,half]
  simp_rw [mul_comm]
  ring

def mForm (T : Table t n e) : Form (n+e) := halfForm T (fun _ _ => 1)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_m (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) :
    (mForm T).eval (flat N E)=edgeCount T N E := eval_half T N E _

def degreeForm (T : Table t n e) (a : Fin n) : Form (n+e) :=
  .plus (.fsum e (fun k => .plus
    (if (T.ends k).1=a then ev k else .c 0)
    (if (T.ends k).2=a then ev k else .c 0)))
    (.fsum 3 (fun x => if (T.slot a).2 x then nv a else .c 0))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_degree (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) (a : Fin n) :
    (degreeForm T a).eval (flat N E)=regularDegree T N E a := by
  classical
  simp only [degreeForm,Form.eval,apply_ite,eval_nv,eval_ev,regularDegree]

def exceptionForm (T : Table t n e) (x : Fin 3) : Form (n+e) :=
  .plus (.c (if x=0 then 2 else 1))
    (.fsum n (fun a => if (T.slot a).2 x then nv a else .c 0))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_exception (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) (x : Fin 3) :
    (exceptionForm T x).eval (flat N E)=exceptionDegree T N x := by
  classical
  simp only [exceptionForm,Form.eval,apply_ite,eval_nv,exceptionDegree]

def rootForm (T : Table t n e) (i : Fin 5) : Form (n+e) :=
  .plus (.fsum n (fun a => if Near (T.slot a).1 i then degreeForm T a else .c 0))
    (.fsum 3 (fun x => if i=t x then exceptionForm T x else .c 0))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_root (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) (i : Fin 5) :
    (rootForm T i).eval (flat N E)=rootCycle T N E i := by
  classical
  simp only [rootForm,Form.eval,apply_ite,eval_degree,eval_exception,rootCycle]

def cutF (b : Fin n ⊕ Fin 3 → Bool) (a a' : Fin n ⊕ Fin 3) : ℤ :=
  if b a=b a' then 1 else 0

def errorF (r : Fin 3) (c : Fin n ⊕ Fin 3 → Fin 5) (a b : Fin n ⊕ Fin 3) : ℤ :=
  if a≠.inr r ∧ b≠.inr r ∧ ¬Near (c a) (c b) then 1 else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cutF_eq (b : Fin n ⊕ Fin 3 → Bool) : cutF b=cutWeight b := by
  funext a a'
  by_cases h : b a=b a' <;> simp [cutF,cutWeight,h]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem errorF_eq (r : Fin 3) (c : Fin n ⊕ Fin 3 → Fin 5) : errorF r c=errorWeight r c := by
  funext a b
  by_cases h : a≠.inr r ∧ b≠.inr r ∧ ¬Near (c a) (c b) <;> simp [errorF,errorWeight,h]

def cutForm (T : Table t n e) (b : Fin n ⊕ Fin 3 → Bool) : Form (n+e) := halfForm T (cutF b)
def errorForm (T : Table t n e) (r : Fin 3) (c : Fin n ⊕ Fin 3 → Fin 5) : Form (n+e) := halfForm T (errorF r c)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_cut (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) (b : Fin n ⊕ Fin 3 → Bool) :
    (cutForm T b).eval (flat N E)=half T N E (cutWeight b) := by
  simpa only [cutForm,cutF_eq] using eval_half T N E (cutF b)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem eval_error (T : Table t n e) (N : Fin n → ℤ) (E : Fin e → ℤ) (r : Fin 3) (c : Fin n ⊕ Fin 3 → Fin 5) :
    (errorForm T r c).eval (flat N E)=half T N E (errorWeight r c) := by
  simpa only [errorForm,errorF_eq] using eval_half T N E (errorF r c)

end AffineCut

-- CaseFast011

namespace FastCutCase.C011
open Finset ThreeExceptions FiniteCutTemplate GraphMass CutSummary CertifiedAffine AffineCut
abbrev T := NativeCutTemplate.C011.table
def row_0 : Form 63 := (verticesForm (n:=17) (e:=46))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_0 : ∀j,row_0.coeff j=IndependentCutLP.C011.A 0 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_0 : (22:ℤ)-row_0.constant=IndependentCutLP.C011.B 0 := by decide +kernel
def row_1 : Form 63 := (mForm T)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_1 : ∀j,row_1.coeff j=IndependentCutLP.C011.A 1 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_1 : (121:ℤ)-row_1.constant=IndependentCutLP.C011.B 1 := by decide +kernel
def row_2 : Form 63 := (.scale (-1) (nv (n:=17) (e:=46) (T.cycle 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_2 : ∀j,row_2.coeff j=IndependentCutLP.C011.A 2 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_2 : (-1:ℤ)-row_2.constant=IndependentCutLP.C011.B 2 := by decide +kernel
def row_3 : Form 63 := (.scale (-1) (nv (n:=17) (e:=46) (T.cycle 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_3 : ∀j,row_3.coeff j=IndependentCutLP.C011.A 3 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_3 : (-1:ℤ)-row_3.constant=IndependentCutLP.C011.B 3 := by decide +kernel
def row_4 : Form 63 := (.scale (-1) (nv (n:=17) (e:=46) (T.cycle 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_4 : ∀j,row_4.coeff j=IndependentCutLP.C011.A 4 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_4 : (-1:ℤ)-row_4.constant=IndependentCutLP.C011.B 4 := by decide +kernel
def row_5 : Form 63 := (.plus (degreeForm T 0) (.scale (-12) (nv (n:=17) (e:=46) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_5 : ∀j,row_5.coeff j=IndependentCutLP.C011.A 5 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_5 : (0:ℤ)-row_5.constant=IndependentCutLP.C011.B 5 := by decide +kernel
def row_6 : Form 63 := (.plus (degreeForm T 1) (.scale (-12) (nv (n:=17) (e:=46) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_6 : ∀j,row_6.coeff j=IndependentCutLP.C011.A 6 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_6 : (0:ℤ)-row_6.constant=IndependentCutLP.C011.B 6 := by decide +kernel
def row_7 : Form 63 := (.plus (degreeForm T 2) (.scale (-12) (nv (n:=17) (e:=46) 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_7 : ∀j,row_7.coeff j=IndependentCutLP.C011.A 7 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_7 : (0:ℤ)-row_7.constant=IndependentCutLP.C011.B 7 := by decide +kernel
def row_8 : Form 63 := (.plus (degreeForm T 3) (.scale (-12) (nv (n:=17) (e:=46) 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_8 : ∀j,row_8.coeff j=IndependentCutLP.C011.A 8 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_8 : (0:ℤ)-row_8.constant=IndependentCutLP.C011.B 8 := by decide +kernel
def row_9 : Form 63 := (.plus (degreeForm T 4) (.scale (-12) (nv (n:=17) (e:=46) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_9 : ∀j,row_9.coeff j=IndependentCutLP.C011.A 9 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_9 : (0:ℤ)-row_9.constant=IndependentCutLP.C011.B 9 := by decide +kernel
def row_10 : Form 63 := (.plus (degreeForm T 5) (.scale (-12) (nv (n:=17) (e:=46) 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_10 : ∀j,row_10.coeff j=IndependentCutLP.C011.A 10 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_10 : (0:ℤ)-row_10.constant=IndependentCutLP.C011.B 10 := by decide +kernel
def row_11 : Form 63 := (.plus (degreeForm T 6) (.scale (-12) (nv (n:=17) (e:=46) 6)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_11 : ∀j,row_11.coeff j=IndependentCutLP.C011.A 11 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_11 : (0:ℤ)-row_11.constant=IndependentCutLP.C011.B 11 := by decide +kernel
def row_12 : Form 63 := (.plus (degreeForm T 8) (.scale (-12) (nv (n:=17) (e:=46) 8)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_12 : ∀j,row_12.coeff j=IndependentCutLP.C011.A 12 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_12 : (0:ℤ)-row_12.constant=IndependentCutLP.C011.B 12 := by decide +kernel
def row_13 : Form 63 := (.plus (degreeForm T 10) (.scale (-12) (nv (n:=17) (e:=46) 10)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_13 : ∀j,row_13.coeff j=IndependentCutLP.C011.A 13 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_13 : (0:ℤ)-row_13.constant=IndependentCutLP.C011.B 13 := by decide +kernel
def row_14 : Form 63 := (.plus (degreeForm T 11) (.scale (-12) (nv (n:=17) (e:=46) 11)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_14 : ∀j,row_14.coeff j=IndependentCutLP.C011.A 14 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_14 : (0:ℤ)-row_14.constant=IndependentCutLP.C011.B 14 := by decide +kernel
def row_15 : Form 63 := (.plus (degreeForm T 13) (.scale (-12) (nv (n:=17) (e:=46) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_15 : ∀j,row_15.coeff j=IndependentCutLP.C011.A 15 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_15 : (0:ℤ)-row_15.constant=IndependentCutLP.C011.B 15 := by decide +kernel
def row_16 : Form 63 := (.plus (degreeForm T 14) (.scale (-12) (nv (n:=17) (e:=46) 14)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_16 : ∀j,row_16.coeff j=IndependentCutLP.C011.A 16 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_16 : (0:ℤ)-row_16.constant=IndependentCutLP.C011.B 16 := by decide +kernel
def row_17 : Form 63 := (.plus (degreeForm T 15) (.scale (-12) (nv (n:=17) (e:=46) 15)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_17 : ∀j,row_17.coeff j=IndependentCutLP.C011.A 17 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_17 : (0:ℤ)-row_17.constant=IndependentCutLP.C011.B 17 := by decide +kernel
def row_18 : Form 63 := (.plus (rootForm T 1) (.scale (-1) (mForm T)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_18 : ∀j,row_18.coeff j=IndependentCutLP.C011.A 18 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_18 : (-26:ℤ)-row_18.constant=IndependentCutLP.C011.B 18 := by decide +kernel
def colors_19 : Fin 17 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 0 else if x=1 then 2 else 2)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_19 : properAway T 0 colors_19 := by unfold properAway; decide +kernel
def row_19 : Form 63 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 0 colors_19))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_19 : ∀j,row_19.coeff j=IndependentCutLP.C011.A 19 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_19 : (-130:ℤ)-row_19.constant=IndependentCutLP.C011.B 19 := by decide +kernel
def colors_20 : Fin 17 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 4 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_20 : properAway T 1 colors_20 := by unfold properAway; decide +kernel
def row_20 : Form 63 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 1 colors_20))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_20 : ∀j,row_20.coeff j=IndependentCutLP.C011.A 20 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_20 : (-130:ℤ)-row_20.constant=IndependentCutLP.C011.B 20 := by decide +kernel
def colors_21 : Fin 17 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 4 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_21 : properAway T 2 colors_21 := by unfold properAway; decide +kernel
def row_21 : Form 63 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_21))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_21 : ∀j,row_21.coeff j=IndependentCutLP.C011.A 21 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_21 : (-130:ℤ)-row_21.constant=IndependentCutLP.C011.B 21 := by decide +kernel
def row_22 : Form 63 := (.plus (.plus (nv (n:=17) (e:=46) (T.ends 16).1) (nv (n:=17) (e:=46) (T.ends 16).2)) (.scale (-1) (ev (n:=17) (e:=46) 16)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_22 : ∀j,row_22.coeff j=IndependentCutLP.C011.A 22 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_22 : (1:ℤ)-row_22.constant=IndependentCutLP.C011.B 22 := by decide +kernel
def row_23 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 19).1) (.scale (-1) (ev (n:=17) (e:=46) 19)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_23 : ∀j,row_23.coeff j=IndependentCutLP.C011.A 23 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_23 : (0:ℤ)-row_23.constant=IndependentCutLP.C011.B 23 := by decide +kernel
def row_24 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 21).1) (.scale (-1) (ev (n:=17) (e:=46) 21)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_24 : ∀j,row_24.coeff j=IndependentCutLP.C011.A 24 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_24 : (0:ℤ)-row_24.constant=IndependentCutLP.C011.B 24 := by decide +kernel
def row_25 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 23).1) (.scale (-1) (ev (n:=17) (e:=46) 23)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_25 : ∀j,row_25.coeff j=IndependentCutLP.C011.A 25 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_25 : (0:ℤ)-row_25.constant=IndependentCutLP.C011.B 25 := by decide +kernel
def row_26 : Form 63 := (.plus (.plus (nv (n:=17) (e:=46) (T.ends 27).1) (nv (n:=17) (e:=46) (T.ends 27).2)) (.scale (-1) (ev (n:=17) (e:=46) 27)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_26 : ∀j,row_26.coeff j=IndependentCutLP.C011.A 26 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_26 : (1:ℤ)-row_26.constant=IndependentCutLP.C011.B 26 := by decide +kernel
def row_27 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 28).2) (.scale (-1) (ev (n:=17) (e:=46) 28)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_27 : ∀j,row_27.coeff j=IndependentCutLP.C011.A 27 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_27 : (0:ℤ)-row_27.constant=IndependentCutLP.C011.B 27 := by decide +kernel
def row_28 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 29).2) (.scale (-1) (ev (n:=17) (e:=46) 29)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_28 : ∀j,row_28.coeff j=IndependentCutLP.C011.A 28 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_28 : (0:ℤ)-row_28.constant=IndependentCutLP.C011.B 28 := by decide +kernel
def row_29 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 30).2) (.scale (-1) (ev (n:=17) (e:=46) 30)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_29 : ∀j,row_29.coeff j=IndependentCutLP.C011.A 29 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_29 : (0:ℤ)-row_29.constant=IndependentCutLP.C011.B 29 := by decide +kernel
def row_30 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 34).1) (.scale (-1) (ev (n:=17) (e:=46) 34)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_30 : ∀j,row_30.coeff j=IndependentCutLP.C011.A 30 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_30 : (0:ℤ)-row_30.constant=IndependentCutLP.C011.B 30 := by decide +kernel
def row_31 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 39).1) (.scale (-1) (ev (n:=17) (e:=46) 39)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_31 : ∀j,row_31.coeff j=IndependentCutLP.C011.A 31 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_31 : (0:ℤ)-row_31.constant=IndependentCutLP.C011.B 31 := by decide +kernel
def row_32 : Form 63 := (.plus (nv (n:=17) (e:=46) (T.ends 43).1) (.scale (-1) (ev (n:=17) (e:=46) 43)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_32 : ∀j,row_32.coeff j=IndependentCutLP.C011.A 32 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_32 : (0:ℤ)-row_32.constant=IndependentCutLP.C011.B 32 := by decide +kernel
def bits_33 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (1040576 : ℕ).testBit a.val) (fun x => (1040576 : ℕ).testBit (17+x.val))
def row_33 : Form 63 := (.scale (-1) (cutForm T bits_33))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_33 : ∀j,row_33.coeff j=IndependentCutLP.C011.A 33 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_33 : (-26:ℤ)-row_33.constant=IndependentCutLP.C011.B 33 := by decide +kernel
def bits_34 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (139068 : ℕ).testBit a.val) (fun x => (139068 : ℕ).testBit (17+x.val))
def row_34 : Form 63 := (.scale (-1) (cutForm T bits_34))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_34 : ∀j,row_34.coeff j=IndependentCutLP.C011.A 34 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_34 : (-26:ℤ)-row_34.constant=IndependentCutLP.C011.B 34 := by decide +kernel
def bits_35 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (909504 : ℕ).testBit a.val) (fun x => (909504 : ℕ).testBit (17+x.val))
def row_35 : Form 63 := (.scale (-1) (cutForm T bits_35))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_35 : ∀j,row_35.coeff j=IndependentCutLP.C011.A 35 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_35 : (-26:ℤ)-row_35.constant=IndependentCutLP.C011.B 35 := by decide +kernel
def bits_36 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (254204 : ℕ).testBit a.val) (fun x => (254204 : ℕ).testBit (17+x.val))
def row_36 : Form 63 := (.scale (-1) (cutForm T bits_36))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_36 : ∀j,row_36.coeff j=IndependentCutLP.C011.A 36 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_36 : (-26:ℤ)-row_36.constant=IndependentCutLP.C011.B 36 := by decide +kernel
def bits_37 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (204604 : ℕ).testBit a.val) (fun x => (204604 : ℕ).testBit (17+x.val))
def row_37 : Form 63 := (.scale (-1) (cutForm T bits_37))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_37 : ∀j,row_37.coeff j=IndependentCutLP.C011.A 37 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_37 : (-26:ℤ)-row_37.constant=IndependentCutLP.C011.B 37 := by decide +kernel
def bits_38 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (258364 : ℕ).testBit a.val) (fun x => (258364 : ℕ).testBit (17+x.val))
def row_38 : Form 63 := (.scale (-1) (cutForm T bits_38))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_38 : ∀j,row_38.coeff j=IndependentCutLP.C011.A 38 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_38 : (-26:ℤ)-row_38.constant=IndependentCutLP.C011.B 38 := by decide +kernel
def bits_39 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (844596 : ℕ).testBit a.val) (fun x => (844596 : ℕ).testBit (17+x.val))
def row_39 : Form 63 := (.scale (-1) (cutForm T bits_39))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_39 : ∀j,row_39.coeff j=IndependentCutLP.C011.A 39 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_39 : (-26:ℤ)-row_39.constant=IndependentCutLP.C011.B 39 := by decide +kernel
def bits_40 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (259132 : ℕ).testBit a.val) (fun x => (259132 : ℕ).testBit (17+x.val))
def row_40 : Form 63 := (.scale (-1) (cutForm T bits_40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_40 : ∀j,row_40.coeff j=IndependentCutLP.C011.A 40 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_40 : (-26:ℤ)-row_40.constant=IndependentCutLP.C011.B 40 := by decide +kernel
def bits_41 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (254076 : ℕ).testBit a.val) (fun x => (254076 : ℕ).testBit (17+x.val))
def row_41 : Form 63 := (.scale (-1) (cutForm T bits_41))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_41 : ∀j,row_41.coeff j=IndependentCutLP.C011.A 41 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_41 : (-26:ℤ)-row_41.constant=IndependentCutLP.C011.B 41 := by decide +kernel
def bits_42 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (253756 : ℕ).testBit a.val) (fun x => (253756 : ℕ).testBit (17+x.val))
def row_42 : Form 63 := (.scale (-1) (cutForm T bits_42))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_42 : ∀j,row_42.coeff j=IndependentCutLP.C011.A 42 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_42 : (-26:ℤ)-row_42.constant=IndependentCutLP.C011.B 42 := by decide +kernel
def bits_43 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (260156 : ℕ).testBit a.val) (fun x => (260156 : ℕ).testBit (17+x.val))
def row_43 : Form 63 := (.scale (-1) (cutForm T bits_43))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_43 : ∀j,row_43.coeff j=IndependentCutLP.C011.A 43 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_43 : (-26:ℤ)-row_43.constant=IndependentCutLP.C011.B 43 := by decide +kernel
def bits_44 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (437036 : ℕ).testBit a.val) (fun x => (437036 : ℕ).testBit (17+x.val))
def row_44 : Form 63 := (.scale (-1) (cutForm T bits_44))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_44 : ∀j,row_44.coeff j=IndependentCutLP.C011.A 44 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_44 : (-26:ℤ)-row_44.constant=IndependentCutLP.C011.B 44 := by decide +kernel
def bits_45 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (929596 : ℕ).testBit a.val) (fun x => (929596 : ℕ).testBit (17+x.val))
def row_45 : Form 63 := (.scale (-1) (cutForm T bits_45))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_45 : ∀j,row_45.coeff j=IndependentCutLP.C011.A 45 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_45 : (-26:ℤ)-row_45.constant=IndependentCutLP.C011.B 45 := by decide +kernel
def bits_46 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (437052 : ℕ).testBit a.val) (fun x => (437052 : ℕ).testBit (17+x.val))
def row_46 : Form 63 := (.scale (-1) (cutForm T bits_46))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_46 : ∀j,row_46.coeff j=IndependentCutLP.C011.A 46 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_46 : (-26:ℤ)-row_46.constant=IndependentCutLP.C011.B 46 := by decide +kernel
def bits_47 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (681788 : ℕ).testBit a.val) (fun x => (681788 : ℕ).testBit (17+x.val))
def row_47 : Form 63 := (.scale (-1) (cutForm T bits_47))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_47 : ∀j,row_47.coeff j=IndependentCutLP.C011.A 47 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_47 : (-26:ℤ)-row_47.constant=IndependentCutLP.C011.B 47 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_0 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 0 j*flat N E j) ≤ IndependentCutLP.C011.B 0 := by
  apply of_eval_le row_0 _ _ (22:ℤ) (flat N E) coeff_0 const_0
  have h := S.vertices
  simp only [row_0,eval_vertices]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_1 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 1 j*flat N E j) ≤ IndependentCutLP.C011.B 1 := by
  apply of_eval_le row_1 _ _ (121:ℤ) (flat N E) coeff_1 const_1
  have h := S.edgeHi
  simp only [row_1,eval_m]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_2 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 2 j*flat N E j) ≤ IndependentCutLP.C011.B 2 := by
  apply of_eval_le row_2 _ _ (-1:ℤ) (flat N E) coeff_2 const_2
  have h := S.exists_cycle 0
  simp only [row_2,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_3 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 3 j*flat N E j) ≤ IndependentCutLP.C011.B 3 := by
  apply of_eval_le row_3 _ _ (-1:ℤ) (flat N E) coeff_3 const_3
  have h := S.exists_cycle 1
  simp only [row_3,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_4 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 4 j*flat N E j) ≤ IndependentCutLP.C011.B 4 := by
  apply of_eval_le row_4 _ _ (-1:ℤ) (flat N E) coeff_4 const_4
  have h := S.exists_cycle 3
  simp only [row_4,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_5 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 5 j*flat N E j) ≤ IndependentCutLP.C011.B 5 := by
  apply of_eval_le row_5 _ _ (0:ℤ) (flat N E) coeff_5 const_5
  have h := S.degrees 0
  simp only [row_5,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_6 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 6 j*flat N E j) ≤ IndependentCutLP.C011.B 6 := by
  apply of_eval_le row_6 _ _ (0:ℤ) (flat N E) coeff_6 const_6
  have h := S.degrees 1
  simp only [row_6,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_7 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 7 j*flat N E j) ≤ IndependentCutLP.C011.B 7 := by
  apply of_eval_le row_7 _ _ (0:ℤ) (flat N E) coeff_7 const_7
  have h := S.degrees 2
  simp only [row_7,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_8 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 8 j*flat N E j) ≤ IndependentCutLP.C011.B 8 := by
  apply of_eval_le row_8 _ _ (0:ℤ) (flat N E) coeff_8 const_8
  have h := S.degrees 3
  simp only [row_8,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_9 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 9 j*flat N E j) ≤ IndependentCutLP.C011.B 9 := by
  apply of_eval_le row_9 _ _ (0:ℤ) (flat N E) coeff_9 const_9
  have h := S.degrees 4
  simp only [row_9,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_10 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 10 j*flat N E j) ≤ IndependentCutLP.C011.B 10 := by
  apply of_eval_le row_10 _ _ (0:ℤ) (flat N E) coeff_10 const_10
  have h := S.degrees 5
  simp only [row_10,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_11 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 11 j*flat N E j) ≤ IndependentCutLP.C011.B 11 := by
  apply of_eval_le row_11 _ _ (0:ℤ) (flat N E) coeff_11 const_11
  have h := S.degrees 6
  simp only [row_11,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_12 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 12 j*flat N E j) ≤ IndependentCutLP.C011.B 12 := by
  apply of_eval_le row_12 _ _ (0:ℤ) (flat N E) coeff_12 const_12
  have h := S.degrees 8
  simp only [row_12,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_13 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 13 j*flat N E j) ≤ IndependentCutLP.C011.B 13 := by
  apply of_eval_le row_13 _ _ (0:ℤ) (flat N E) coeff_13 const_13
  have h := S.degrees 10
  simp only [row_13,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_14 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 14 j*flat N E j) ≤ IndependentCutLP.C011.B 14 := by
  apply of_eval_le row_14 _ _ (0:ℤ) (flat N E) coeff_14 const_14
  have h := S.degrees 11
  simp only [row_14,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_15 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 15 j*flat N E j) ≤ IndependentCutLP.C011.B 15 := by
  apply of_eval_le row_15 _ _ (0:ℤ) (flat N E) coeff_15 const_15
  have h := S.degrees 13
  simp only [row_15,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_16 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 16 j*flat N E j) ≤ IndependentCutLP.C011.B 16 := by
  apply of_eval_le row_16 _ _ (0:ℤ) (flat N E) coeff_16 const_16
  have h := S.degrees 14
  simp only [row_16,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_17 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 17 j*flat N E j) ≤ IndependentCutLP.C011.B 17 := by
  apply of_eval_le row_17 _ _ (0:ℤ) (flat N E) coeff_17 const_17
  have h := S.degrees 15
  simp only [row_17,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_18 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 18 j*flat N E j) ≤ IndependentCutLP.C011.B 18 := by
  apply of_eval_le row_18 _ _ (-26:ℤ) (flat N E) coeff_18 const_18
  have h := S.root 1
  simp only [row_18,eval_plus,eval_scale,eval_m,eval_root]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_19 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 19 j*flat N E j) ≤ IndependentCutLP.C011.B 19 := by
  apply of_eval_le row_19 _ _ (-130:ℤ) (flat N E) coeff_19 const_19
  have h := S.repairs 0 colors_19 proper_19
  simp only [row_19,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_20 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 20 j*flat N E j) ≤ IndependentCutLP.C011.B 20 := by
  apply of_eval_le row_20 _ _ (-130:ℤ) (flat N E) coeff_20 const_20
  have h := S.repairs 1 colors_20 proper_20
  simp only [row_20,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_21 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 21 j*flat N E j) ≤ IndependentCutLP.C011.B 21 := by
  apply of_eval_le row_21 _ _ (-130:ℤ) (flat N E) coeff_21 const_21
  have h := S.repairs 2 colors_21 proper_21
  simp only [row_21,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_22 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 22 j*flat N E j) ≤ IndependentCutLP.C011.B 22 := by
  apply of_eval_le row_22 _ _ (1:ℤ) (flat N E) coeff_22 const_22
  have h := S.cycle_both 16 3 2 (by decide +kernel) (by decide +kernel)
  simp only [row_22,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_23 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 23 j*flat N E j) ≤ IndependentCutLP.C011.B 23 := by
  apply of_eval_le row_23 _ _ (0:ℤ) (flat N E) coeff_23 const_23
  have h := S.cycle_right 19 2 (by decide +kernel)
  simp only [row_23,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_24 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 24 j*flat N E j) ≤ IndependentCutLP.C011.B 24 := by
  apply of_eval_le row_24 _ _ (0:ℤ) (flat N E) coeff_24 const_24
  have h := S.cycle_right 21 2 (by decide +kernel)
  simp only [row_24,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_25 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 25 j*flat N E j) ≤ IndependentCutLP.C011.B 25 := by
  apply of_eval_le row_25 _ _ (0:ℤ) (flat N E) coeff_25 const_25
  have h := S.cycle_right 23 2 (by decide +kernel)
  simp only [row_25,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_26 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 26 j*flat N E j) ≤ IndependentCutLP.C011.B 26 := by
  apply of_eval_le row_26 _ _ (1:ℤ) (flat N E) coeff_26 const_26
  have h := S.cycle_both 27 4 3 (by decide +kernel) (by decide +kernel)
  simp only [row_26,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_27 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 27 j*flat N E j) ≤ IndependentCutLP.C011.B 27 := by
  apply of_eval_le row_27 _ _ (0:ℤ) (flat N E) coeff_27 const_27
  have h := S.cycle_left 28 4 (by decide +kernel)
  simp only [row_27,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_28 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 28 j*flat N E j) ≤ IndependentCutLP.C011.B 28 := by
  apply of_eval_le row_28 _ _ (0:ℤ) (flat N E) coeff_28 const_28
  have h := S.cycle_left 29 4 (by decide +kernel)
  simp only [row_28,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_29 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 29 j*flat N E j) ≤ IndependentCutLP.C011.B 29 := by
  apply of_eval_le row_29 _ _ (0:ℤ) (flat N E) coeff_29 const_29
  have h := S.cycle_left 30 4 (by decide +kernel)
  simp only [row_29,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_30 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 30 j*flat N E j) ≤ IndependentCutLP.C011.B 30 := by
  apply of_eval_le row_30 _ _ (0:ℤ) (flat N E) coeff_30 const_30
  have h := S.cycle_right 34 3 (by decide +kernel)
  simp only [row_30,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_31 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 31 j*flat N E j) ≤ IndependentCutLP.C011.B 31 := by
  apply of_eval_le row_31 _ _ (0:ℤ) (flat N E) coeff_31 const_31
  have h := S.cycle_right 39 3 (by decide +kernel)
  simp only [row_31,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_32 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 32 j*flat N E j) ≤ IndependentCutLP.C011.B 32 := by
  apply of_eval_le row_32 _ _ (0:ℤ) (flat N E) coeff_32 const_32
  have h := S.cycle_right 43 0 (by decide +kernel)
  simp only [row_32,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_33 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 33 j*flat N E j) ≤ IndependentCutLP.C011.B 33 := by
  apply of_eval_le row_33 _ _ (-26:ℤ) (flat N E) coeff_33 const_33
  have h := S.cuts bits_33
  simp only [row_33,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_34 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 34 j*flat N E j) ≤ IndependentCutLP.C011.B 34 := by
  apply of_eval_le row_34 _ _ (-26:ℤ) (flat N E) coeff_34 const_34
  have h := S.cuts bits_34
  simp only [row_34,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_35 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 35 j*flat N E j) ≤ IndependentCutLP.C011.B 35 := by
  apply of_eval_le row_35 _ _ (-26:ℤ) (flat N E) coeff_35 const_35
  have h := S.cuts bits_35
  simp only [row_35,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_36 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 36 j*flat N E j) ≤ IndependentCutLP.C011.B 36 := by
  apply of_eval_le row_36 _ _ (-26:ℤ) (flat N E) coeff_36 const_36
  have h := S.cuts bits_36
  simp only [row_36,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_37 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 37 j*flat N E j) ≤ IndependentCutLP.C011.B 37 := by
  apply of_eval_le row_37 _ _ (-26:ℤ) (flat N E) coeff_37 const_37
  have h := S.cuts bits_37
  simp only [row_37,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_38 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 38 j*flat N E j) ≤ IndependentCutLP.C011.B 38 := by
  apply of_eval_le row_38 _ _ (-26:ℤ) (flat N E) coeff_38 const_38
  have h := S.cuts bits_38
  simp only [row_38,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_39 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 39 j*flat N E j) ≤ IndependentCutLP.C011.B 39 := by
  apply of_eval_le row_39 _ _ (-26:ℤ) (flat N E) coeff_39 const_39
  have h := S.cuts bits_39
  simp only [row_39,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_40 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 40 j*flat N E j) ≤ IndependentCutLP.C011.B 40 := by
  apply of_eval_le row_40 _ _ (-26:ℤ) (flat N E) coeff_40 const_40
  have h := S.cuts bits_40
  simp only [row_40,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_41 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 41 j*flat N E j) ≤ IndependentCutLP.C011.B 41 := by
  apply of_eval_le row_41 _ _ (-26:ℤ) (flat N E) coeff_41 const_41
  have h := S.cuts bits_41
  simp only [row_41,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_42 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 42 j*flat N E j) ≤ IndependentCutLP.C011.B 42 := by
  apply of_eval_le row_42 _ _ (-26:ℤ) (flat N E) coeff_42 const_42
  have h := S.cuts bits_42
  simp only [row_42,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_43 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 43 j*flat N E j) ≤ IndependentCutLP.C011.B 43 := by
  apply of_eval_le row_43 _ _ (-26:ℤ) (flat N E) coeff_43 const_43
  have h := S.cuts bits_43
  simp only [row_43,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_44 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 44 j*flat N E j) ≤ IndependentCutLP.C011.B 44 := by
  apply of_eval_le row_44 _ _ (-26:ℤ) (flat N E) coeff_44 const_44
  have h := S.cuts bits_44
  simp only [row_44,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_45 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 45 j*flat N E j) ≤ IndependentCutLP.C011.B 45 := by
  apply of_eval_le row_45 _ _ (-26:ℤ) (flat N E) coeff_45 const_45
  have h := S.cuts bits_45
  simp only [row_45,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_46 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 46 j*flat N E j) ≤ IndependentCutLP.C011.B 46 := by
  apply of_eval_le row_46 _ _ (-26:ℤ) (flat N E) coeff_46 const_46
  have h := S.cuts bits_46
  simp only [row_46,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_47 (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C011.A 47 j*flat N E j) ≤ IndependentCutLP.C011.B 47 := by
  apply of_eval_le row_47 _ _ (-26:ℤ) (flat N E) coeff_47 const_47
  have h := S.cuts bits_47
  simp only [row_47,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (N : Fin 17 → ℤ) (E : Fin 46 → ℤ) (S : Feasible T N E 12 121) : False := by
  apply IndependentCutLP.C011.impossible (flat N E)
  · intro j
    refine Fin.addCases (m:=17) (n:=46) (fun a => ?_) (fun k => ?_) j
    · simpa [flat] using S.npos a
    · simpa [flat] using S.epos k
  · intro i
    fin_cases i
    · exact valid_0 N E S
    · exact valid_1 N E S
    · exact valid_2 N E S
    · exact valid_3 N E S
    · exact valid_4 N E S
    · exact valid_5 N E S
    · exact valid_6 N E S
    · exact valid_7 N E S
    · exact valid_8 N E S
    · exact valid_9 N E S
    · exact valid_10 N E S
    · exact valid_11 N E S
    · exact valid_12 N E S
    · exact valid_13 N E S
    · exact valid_14 N E S
    · exact valid_15 N E S
    · exact valid_16 N E S
    · exact valid_17 N E S
    · exact valid_18 N E S
    · exact valid_19 N E S
    · exact valid_20 N E S
    · exact valid_21 N E S
    · exact valid_22 N E S
    · exact valid_23 N E S
    · exact valid_24 N E S
    · exact valid_25 N E S
    · exact valid_26 N E S
    · exact valid_27 N E S
    · exact valid_28 N E S
    · exact valid_29 N E S
    · exact valid_30 N E S
    · exact valid_31 N E S
    · exact valid_32 N E S
    · exact valid_33 N E S
    · exact valid_34 N E S
    · exact valid_35 N E S
    · exact valid_36 N E S
    · exact valid_37 N E S
    · exact valid_38 N E S
    · exact valid_39 N E S
    · exact valid_40 N E S
    · exact valid_41 N E S
    · exact valid_42 N E S
    · exact valid_43 N E S
    · exact valid_44 N E S
    · exact valid_45 N E S
    · exact valid_46 N E S
    · exact valid_47 N E S
end FastCutCase.C011

-- CaseFast012

namespace FastCutCase.C012
open Finset ThreeExceptions FiniteCutTemplate GraphMass CutSummary CertifiedAffine AffineCut
abbrev T := NativeCutTemplate.C012.table
def row_0 : Form 55 := (verticesForm (n:=15) (e:=40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_0 : ∀j,row_0.coeff j=IndependentCutLP.C012.A 0 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_0 : (22:ℤ)-row_0.constant=IndependentCutLP.C012.B 0 := by decide +kernel
def row_1 : Form 55 := (mForm T)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_1 : ∀j,row_1.coeff j=IndependentCutLP.C012.A 1 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_1 : (121:ℤ)-row_1.constant=IndependentCutLP.C012.B 1 := by decide +kernel
def row_2 : Form 55 := (.scale (-1) (nv (n:=15) (e:=40) (T.cycle 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_2 : ∀j,row_2.coeff j=IndependentCutLP.C012.A 2 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_2 : (-1:ℤ)-row_2.constant=IndependentCutLP.C012.B 2 := by decide +kernel
def row_3 : Form 55 := (.scale (-1) (nv (n:=15) (e:=40) (T.cycle 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_3 : ∀j,row_3.coeff j=IndependentCutLP.C012.A 3 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_3 : (-1:ℤ)-row_3.constant=IndependentCutLP.C012.B 3 := by decide +kernel
def row_4 : Form 55 := (.scale (-1) (nv (n:=15) (e:=40) (T.cycle 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_4 : ∀j,row_4.coeff j=IndependentCutLP.C012.A 4 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_4 : (-1:ℤ)-row_4.constant=IndependentCutLP.C012.B 4 := by decide +kernel
def row_5 : Form 55 := (.scale (-1) (nv (n:=15) (e:=40) (T.cycle 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_5 : ∀j,row_5.coeff j=IndependentCutLP.C012.A 5 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_5 : (-1:ℤ)-row_5.constant=IndependentCutLP.C012.B 5 := by decide +kernel
def row_6 : Form 55 := (.plus (degreeForm T 0) (.scale (-12) (nv (n:=15) (e:=40) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_6 : ∀j,row_6.coeff j=IndependentCutLP.C012.A 6 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_6 : (0:ℤ)-row_6.constant=IndependentCutLP.C012.B 6 := by decide +kernel
def row_7 : Form 55 := (.plus (degreeForm T 1) (.scale (-12) (nv (n:=15) (e:=40) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_7 : ∀j,row_7.coeff j=IndependentCutLP.C012.A 7 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_7 : (0:ℤ)-row_7.constant=IndependentCutLP.C012.B 7 := by decide +kernel
def row_8 : Form 55 := (.plus (degreeForm T 3) (.scale (-12) (nv (n:=15) (e:=40) 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_8 : ∀j,row_8.coeff j=IndependentCutLP.C012.A 8 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_8 : (0:ℤ)-row_8.constant=IndependentCutLP.C012.B 8 := by decide +kernel
def row_9 : Form 55 := (.plus (degreeForm T 4) (.scale (-12) (nv (n:=15) (e:=40) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_9 : ∀j,row_9.coeff j=IndependentCutLP.C012.A 9 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_9 : (0:ℤ)-row_9.constant=IndependentCutLP.C012.B 9 := by decide +kernel
def row_10 : Form 55 := (.plus (degreeForm T 5) (.scale (-12) (nv (n:=15) (e:=40) 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_10 : ∀j,row_10.coeff j=IndependentCutLP.C012.A 10 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_10 : (0:ℤ)-row_10.constant=IndependentCutLP.C012.B 10 := by decide +kernel
def row_11 : Form 55 := (.plus (degreeForm T 7) (.scale (-12) (nv (n:=15) (e:=40) 7)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_11 : ∀j,row_11.coeff j=IndependentCutLP.C012.A 11 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_11 : (0:ℤ)-row_11.constant=IndependentCutLP.C012.B 11 := by decide +kernel
def row_12 : Form 55 := (.plus (degreeForm T 8) (.scale (-12) (nv (n:=15) (e:=40) 8)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_12 : ∀j,row_12.coeff j=IndependentCutLP.C012.A 12 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_12 : (0:ℤ)-row_12.constant=IndependentCutLP.C012.B 12 := by decide +kernel
def row_13 : Form 55 := (.plus (degreeForm T 9) (.scale (-12) (nv (n:=15) (e:=40) 9)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_13 : ∀j,row_13.coeff j=IndependentCutLP.C012.A 13 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_13 : (0:ℤ)-row_13.constant=IndependentCutLP.C012.B 13 := by decide +kernel
def row_14 : Form 55 := (.plus (degreeForm T 11) (.scale (-12) (nv (n:=15) (e:=40) 11)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_14 : ∀j,row_14.coeff j=IndependentCutLP.C012.A 14 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_14 : (0:ℤ)-row_14.constant=IndependentCutLP.C012.B 14 := by decide +kernel
def row_15 : Form 55 := (.plus (degreeForm T 12) (.scale (-12) (nv (n:=15) (e:=40) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_15 : ∀j,row_15.coeff j=IndependentCutLP.C012.A 15 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_15 : (0:ℤ)-row_15.constant=IndependentCutLP.C012.B 15 := by decide +kernel
def row_16 : Form 55 := (.plus (degreeForm T 13) (.scale (-12) (nv (n:=15) (e:=40) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_16 : ∀j,row_16.coeff j=IndependentCutLP.C012.A 16 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_16 : (0:ℤ)-row_16.constant=IndependentCutLP.C012.B 16 := by decide +kernel
def colors_17 : Fin 15 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 1 else if x=1 then 2 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_17 : properAway T 2 colors_17 := by unfold properAway; decide +kernel
def row_17 : Form 55 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_17))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_17 : ∀j,row_17.coeff j=IndependentCutLP.C012.A 17 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_17 : (-130:ℤ)-row_17.constant=IndependentCutLP.C012.B 17 := by decide +kernel
def colors_18 : Fin 15 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 1 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_18 : properAway T 2 colors_18 := by unfold properAway; decide +kernel
def row_18 : Form 55 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_18))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_18 : ∀j,row_18.coeff j=IndependentCutLP.C012.A 18 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_18 : (-130:ℤ)-row_18.constant=IndependentCutLP.C012.B 18 := by decide +kernel
def row_19 : Form 55 := (.plus (nv (n:=15) (e:=40) (T.ends 12).2) (.scale (-1) (ev (n:=15) (e:=40) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_19 : ∀j,row_19.coeff j=IndependentCutLP.C012.A 19 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_19 : (0:ℤ)-row_19.constant=IndependentCutLP.C012.B 19 := by decide +kernel
def row_20 : Form 55 := (.plus (.plus (nv (n:=15) (e:=40) (T.ends 14).1) (nv (n:=15) (e:=40) (T.ends 14).2)) (.scale (-1) (ev (n:=15) (e:=40) 14)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_20 : ∀j,row_20.coeff j=IndependentCutLP.C012.A 20 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_20 : (1:ℤ)-row_20.constant=IndependentCutLP.C012.B 20 := by decide +kernel
def row_21 : Form 55 := (.plus (nv (n:=15) (e:=40) (T.ends 19).1) (.scale (-1) (ev (n:=15) (e:=40) 19)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_21 : ∀j,row_21.coeff j=IndependentCutLP.C012.A 21 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_21 : (0:ℤ)-row_21.constant=IndependentCutLP.C012.B 21 := by decide +kernel
def row_22 : Form 55 := (.plus (nv (n:=15) (e:=40) (T.ends 20).2) (.scale (-1) (ev (n:=15) (e:=40) 20)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_22 : ∀j,row_22.coeff j=IndependentCutLP.C012.A 22 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_22 : (0:ℤ)-row_22.constant=IndependentCutLP.C012.B 22 := by decide +kernel
def row_23 : Form 55 := (.plus (.plus (nv (n:=15) (e:=40) (T.ends 21).1) (nv (n:=15) (e:=40) (T.ends 21).2)) (.scale (-1) (ev (n:=15) (e:=40) 21)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_23 : ∀j,row_23.coeff j=IndependentCutLP.C012.A 23 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_23 : (1:ℤ)-row_23.constant=IndependentCutLP.C012.B 23 := by decide +kernel
def row_24 : Form 55 := (.plus (.plus (nv (n:=15) (e:=40) (T.ends 23).1) (nv (n:=15) (e:=40) (T.ends 23).2)) (.scale (-1) (ev (n:=15) (e:=40) 23)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_24 : ∀j,row_24.coeff j=IndependentCutLP.C012.A 24 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_24 : (1:ℤ)-row_24.constant=IndependentCutLP.C012.B 24 := by decide +kernel
def row_25 : Form 55 := (.plus (nv (n:=15) (e:=40) (T.ends 24).2) (.scale (-1) (ev (n:=15) (e:=40) 24)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_25 : ∀j,row_25.coeff j=IndependentCutLP.C012.A 25 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_25 : (0:ℤ)-row_25.constant=IndependentCutLP.C012.B 25 := by decide +kernel
def row_26 : Form 55 := (.plus (nv (n:=15) (e:=40) (T.ends 27).1) (.scale (-1) (ev (n:=15) (e:=40) 27)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_26 : ∀j,row_26.coeff j=IndependentCutLP.C012.A 26 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_26 : (0:ℤ)-row_26.constant=IndependentCutLP.C012.B 26 := by decide +kernel
def row_27 : Form 55 := (.plus (nv (n:=15) (e:=40) (T.ends 33).1) (.scale (-1) (ev (n:=15) (e:=40) 33)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_27 : ∀j,row_27.coeff j=IndependentCutLP.C012.A 27 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_27 : (0:ℤ)-row_27.constant=IndependentCutLP.C012.B 27 := by decide +kernel
def bits_28 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (227552 : ℕ).testBit a.val) (fun x => (227552 : ℕ).testBit (15+x.val))
def row_28 : Form 55 := (.scale (-1) (cutForm T bits_28))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_28 : ∀j,row_28.coeff j=IndependentCutLP.C012.A 28 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_28 : (-26:ℤ)-row_28.constant=IndependentCutLP.C012.B 28 := by decide +kernel
def bits_29 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (63712 : ℕ).testBit a.val) (fun x => (63712 : ℕ).testBit (15+x.val))
def row_29 : Form 55 := (.scale (-1) (cutForm T bits_29))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_29 : ∀j,row_29.coeff j=IndependentCutLP.C012.A 29 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_29 : (-26:ℤ)-row_29.constant=IndependentCutLP.C012.B 29 := by decide +kernel
def bits_30 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (63736 : ℕ).testBit a.val) (fun x => (63736 : ℕ).testBit (15+x.val))
def row_30 : Form 55 := (.scale (-1) (cutForm T bits_30))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_30 : ∀j,row_30.coeff j=IndependentCutLP.C012.A 30 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_30 : (-26:ℤ)-row_30.constant=IndependentCutLP.C012.B 30 := by decide +kernel
def bits_31 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (96480 : ℕ).testBit a.val) (fun x => (96480 : ℕ).testBit (15+x.val))
def row_31 : Form 55 := (.scale (-1) (cutForm T bits_31))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_31 : ∀j,row_31.coeff j=IndependentCutLP.C012.A 31 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_31 : (-26:ℤ)-row_31.constant=IndependentCutLP.C012.B 31 := by decide +kernel
def bits_32 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (136986 : ℕ).testBit a.val) (fun x => (136986 : ℕ).testBit (15+x.val))
def row_32 : Form 55 := (.scale (-1) (cutForm T bits_32))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_32 : ∀j,row_32.coeff j=IndependentCutLP.C012.A 32 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_32 : (-26:ℤ)-row_32.constant=IndependentCutLP.C012.B 32 := by decide +kernel
def bits_33 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (195608 : ℕ).testBit a.val) (fun x => (195608 : ℕ).testBit (15+x.val))
def row_33 : Form 55 := (.scale (-1) (cutForm T bits_33))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_33 : ∀j,row_33.coeff j=IndependentCutLP.C012.A 33 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_33 : (-26:ℤ)-row_33.constant=IndependentCutLP.C012.B 33 := by decide +kernel
def bits_34 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (63672 : ℕ).testBit a.val) (fun x => (63672 : ℕ).testBit (15+x.val))
def row_34 : Form 55 := (.scale (-1) (cutForm T bits_34))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_34 : ∀j,row_34.coeff j=IndependentCutLP.C012.A 34 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_34 : (-26:ℤ)-row_34.constant=IndependentCutLP.C012.B 34 := by decide +kernel
def bits_35 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (129252 : ℕ).testBit a.val) (fun x => (129252 : ℕ).testBit (15+x.val))
def row_35 : Form 55 := (.scale (-1) (cutForm T bits_35))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_35 : ∀j,row_35.coeff j=IndependentCutLP.C012.A 35 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_35 : (-26:ℤ)-row_35.constant=IndependentCutLP.C012.B 35 := by decide +kernel
def bits_36 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (50972 : ℕ).testBit a.val) (fun x => (50972 : ℕ).testBit (15+x.val))
def row_36 : Form 55 := (.scale (-1) (cutForm T bits_36))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_36 : ∀j,row_36.coeff j=IndependentCutLP.C012.A 36 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_36 : (-26:ℤ)-row_36.constant=IndependentCutLP.C012.B 36 := by decide +kernel
def bits_37 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (171800 : ℕ).testBit a.val) (fun x => (171800 : ℕ).testBit (15+x.val))
def row_37 : Form 55 := (.scale (-1) (cutForm T bits_37))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_37 : ∀j,row_37.coeff j=IndependentCutLP.C012.A 37 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_37 : (-26:ℤ)-row_37.constant=IndependentCutLP.C012.B 37 := by decide +kernel
def bits_38 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (177944 : ℕ).testBit a.val) (fun x => (177944 : ℕ).testBit (15+x.val))
def row_38 : Form 55 := (.scale (-1) (cutForm T bits_38))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_38 : ∀j,row_38.coeff j=IndependentCutLP.C012.A 38 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_38 : (-26:ℤ)-row_38.constant=IndependentCutLP.C012.B 38 := by decide +kernel
def bits_39 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (207640 : ℕ).testBit a.val) (fun x => (207640 : ℕ).testBit (15+x.val))
def row_39 : Form 55 := (.scale (-1) (cutForm T bits_39))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_39 : ∀j,row_39.coeff j=IndependentCutLP.C012.A 39 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_39 : (-26:ℤ)-row_39.constant=IndependentCutLP.C012.B 39 := by decide +kernel
def bits_40 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (187672 : ℕ).testBit a.val) (fun x => (187672 : ℕ).testBit (15+x.val))
def row_40 : Form 55 := (.scale (-1) (cutForm T bits_40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_40 : ∀j,row_40.coeff j=IndependentCutLP.C012.A 40 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_40 : (-26:ℤ)-row_40.constant=IndependentCutLP.C012.B 40 := by decide +kernel
def bits_41 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (162392 : ℕ).testBit a.val) (fun x => (162392 : ℕ).testBit (15+x.val))
def row_41 : Form 55 := (.scale (-1) (cutForm T bits_41))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_41 : ∀j,row_41.coeff j=IndependentCutLP.C012.A 41 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_41 : (-26:ℤ)-row_41.constant=IndependentCutLP.C012.B 41 := by decide +kernel
def bits_42 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (179480 : ℕ).testBit a.val) (fun x => (179480 : ℕ).testBit (15+x.val))
def row_42 : Form 55 := (.scale (-1) (cutForm T bits_42))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_42 : ∀j,row_42.coeff j=IndependentCutLP.C012.A 42 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_42 : (-26:ℤ)-row_42.constant=IndependentCutLP.C012.B 42 := by decide +kernel
def bits_43 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (64792 : ℕ).testBit a.val) (fun x => (64792 : ℕ).testBit (15+x.val))
def row_43 : Form 55 := (.scale (-1) (cutForm T bits_43))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_43 : ∀j,row_43.coeff j=IndependentCutLP.C012.A 43 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_43 : (-26:ℤ)-row_43.constant=IndependentCutLP.C012.B 43 := by decide +kernel
def bits_44 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (92390 : ℕ).testBit a.val) (fun x => (92390 : ℕ).testBit (15+x.val))
def row_44 : Form 55 := (.scale (-1) (cutForm T bits_44))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_44 : ∀j,row_44.coeff j=IndependentCutLP.C012.A 44 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_44 : (-26:ℤ)-row_44.constant=IndependentCutLP.C012.B 44 := by decide +kernel
def bits_45 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (211544 : ℕ).testBit a.val) (fun x => (211544 : ℕ).testBit (15+x.val))
def row_45 : Form 55 := (.scale (-1) (cutForm T bits_45))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_45 : ∀j,row_45.coeff j=IndependentCutLP.C012.A 45 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_45 : (-26:ℤ)-row_45.constant=IndependentCutLP.C012.B 45 := by decide +kernel
def bits_46 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (169752 : ℕ).testBit a.val) (fun x => (169752 : ℕ).testBit (15+x.val))
def row_46 : Form 55 := (.scale (-1) (cutForm T bits_46))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_46 : ∀j,row_46.coeff j=IndependentCutLP.C012.A 46 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_46 : (-26:ℤ)-row_46.constant=IndependentCutLP.C012.B 46 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_0 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 0 j*flat N E j) ≤ IndependentCutLP.C012.B 0 := by
  apply of_eval_le row_0 _ _ (22:ℤ) (flat N E) coeff_0 const_0
  have h := S.vertices
  simp only [row_0,eval_vertices]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_1 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 1 j*flat N E j) ≤ IndependentCutLP.C012.B 1 := by
  apply of_eval_le row_1 _ _ (121:ℤ) (flat N E) coeff_1 const_1
  have h := S.edgeHi
  simp only [row_1,eval_m]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_2 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 2 j*flat N E j) ≤ IndependentCutLP.C012.B 2 := by
  apply of_eval_le row_2 _ _ (-1:ℤ) (flat N E) coeff_2 const_2
  have h := S.exists_cycle 0
  simp only [row_2,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_3 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 3 j*flat N E j) ≤ IndependentCutLP.C012.B 3 := by
  apply of_eval_le row_3 _ _ (-1:ℤ) (flat N E) coeff_3 const_3
  have h := S.exists_cycle 1
  simp only [row_3,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_4 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 4 j*flat N E j) ≤ IndependentCutLP.C012.B 4 := by
  apply of_eval_le row_4 _ _ (-1:ℤ) (flat N E) coeff_4 const_4
  have h := S.exists_cycle 2
  simp only [row_4,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_5 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 5 j*flat N E j) ≤ IndependentCutLP.C012.B 5 := by
  apply of_eval_le row_5 _ _ (-1:ℤ) (flat N E) coeff_5 const_5
  have h := S.exists_cycle 3
  simp only [row_5,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_6 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 6 j*flat N E j) ≤ IndependentCutLP.C012.B 6 := by
  apply of_eval_le row_6 _ _ (0:ℤ) (flat N E) coeff_6 const_6
  have h := S.degrees 0
  simp only [row_6,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_7 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 7 j*flat N E j) ≤ IndependentCutLP.C012.B 7 := by
  apply of_eval_le row_7 _ _ (0:ℤ) (flat N E) coeff_7 const_7
  have h := S.degrees 1
  simp only [row_7,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_8 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 8 j*flat N E j) ≤ IndependentCutLP.C012.B 8 := by
  apply of_eval_le row_8 _ _ (0:ℤ) (flat N E) coeff_8 const_8
  have h := S.degrees 3
  simp only [row_8,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_9 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 9 j*flat N E j) ≤ IndependentCutLP.C012.B 9 := by
  apply of_eval_le row_9 _ _ (0:ℤ) (flat N E) coeff_9 const_9
  have h := S.degrees 4
  simp only [row_9,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_10 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 10 j*flat N E j) ≤ IndependentCutLP.C012.B 10 := by
  apply of_eval_le row_10 _ _ (0:ℤ) (flat N E) coeff_10 const_10
  have h := S.degrees 5
  simp only [row_10,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_11 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 11 j*flat N E j) ≤ IndependentCutLP.C012.B 11 := by
  apply of_eval_le row_11 _ _ (0:ℤ) (flat N E) coeff_11 const_11
  have h := S.degrees 7
  simp only [row_11,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_12 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 12 j*flat N E j) ≤ IndependentCutLP.C012.B 12 := by
  apply of_eval_le row_12 _ _ (0:ℤ) (flat N E) coeff_12 const_12
  have h := S.degrees 8
  simp only [row_12,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_13 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 13 j*flat N E j) ≤ IndependentCutLP.C012.B 13 := by
  apply of_eval_le row_13 _ _ (0:ℤ) (flat N E) coeff_13 const_13
  have h := S.degrees 9
  simp only [row_13,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_14 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 14 j*flat N E j) ≤ IndependentCutLP.C012.B 14 := by
  apply of_eval_le row_14 _ _ (0:ℤ) (flat N E) coeff_14 const_14
  have h := S.degrees 11
  simp only [row_14,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_15 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 15 j*flat N E j) ≤ IndependentCutLP.C012.B 15 := by
  apply of_eval_le row_15 _ _ (0:ℤ) (flat N E) coeff_15 const_15
  have h := S.degrees 12
  simp only [row_15,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_16 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 16 j*flat N E j) ≤ IndependentCutLP.C012.B 16 := by
  apply of_eval_le row_16 _ _ (0:ℤ) (flat N E) coeff_16 const_16
  have h := S.degrees 13
  simp only [row_16,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_17 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 17 j*flat N E j) ≤ IndependentCutLP.C012.B 17 := by
  apply of_eval_le row_17 _ _ (-130:ℤ) (flat N E) coeff_17 const_17
  have h := S.repairs 2 colors_17 proper_17
  simp only [row_17,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_18 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 18 j*flat N E j) ≤ IndependentCutLP.C012.B 18 := by
  apply of_eval_le row_18 _ _ (-130:ℤ) (flat N E) coeff_18 const_18
  have h := S.repairs 2 colors_18 proper_18
  simp only [row_18,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_19 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 19 j*flat N E j) ≤ IndependentCutLP.C012.B 19 := by
  apply of_eval_le row_19 _ _ (0:ℤ) (flat N E) coeff_19 const_19
  have h := S.cycle_left 12 3 (by decide +kernel)
  simp only [row_19,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_20 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 20 j*flat N E j) ≤ IndependentCutLP.C012.B 20 := by
  apply of_eval_le row_20 _ _ (1:ℤ) (flat N E) coeff_20 const_20
  have h := S.cycle_both 14 3 2 (by decide +kernel) (by decide +kernel)
  simp only [row_20,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_21 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 21 j*flat N E j) ≤ IndependentCutLP.C012.B 21 := by
  apply of_eval_le row_21 _ _ (0:ℤ) (flat N E) coeff_21 const_21
  have h := S.cycle_right 19 2 (by decide +kernel)
  simp only [row_21,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_22 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 22 j*flat N E j) ≤ IndependentCutLP.C012.B 22 := by
  apply of_eval_le row_22 _ _ (0:ℤ) (flat N E) coeff_22 const_22
  have h := S.cycle_left 20 4 (by decide +kernel)
  simp only [row_22,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_23 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 23 j*flat N E j) ≤ IndependentCutLP.C012.B 23 := by
  apply of_eval_le row_23 _ _ (1:ℤ) (flat N E) coeff_23 const_23
  have h := S.cycle_both 21 4 0 (by decide +kernel) (by decide +kernel)
  simp only [row_23,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_24 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 24 j*flat N E j) ≤ IndependentCutLP.C012.B 24 := by
  apply of_eval_le row_24 _ _ (1:ℤ) (flat N E) coeff_24 const_24
  have h := S.cycle_both 23 4 3 (by decide +kernel) (by decide +kernel)
  simp only [row_24,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_25 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 25 j*flat N E j) ≤ IndependentCutLP.C012.B 25 := by
  apply of_eval_le row_25 _ _ (0:ℤ) (flat N E) coeff_25 const_25
  have h := S.cycle_left 24 4 (by decide +kernel)
  simp only [row_25,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_26 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 26 j*flat N E j) ≤ IndependentCutLP.C012.B 26 := by
  apply of_eval_le row_26 _ _ (0:ℤ) (flat N E) coeff_26 const_26
  have h := S.cycle_right 27 0 (by decide +kernel)
  simp only [row_26,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_27 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 27 j*flat N E j) ≤ IndependentCutLP.C012.B 27 := by
  apply of_eval_le row_27 _ _ (0:ℤ) (flat N E) coeff_27 const_27
  have h := S.cycle_right 33 3 (by decide +kernel)
  simp only [row_27,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_28 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 28 j*flat N E j) ≤ IndependentCutLP.C012.B 28 := by
  apply of_eval_le row_28 _ _ (-26:ℤ) (flat N E) coeff_28 const_28
  have h := S.cuts bits_28
  simp only [row_28,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_29 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 29 j*flat N E j) ≤ IndependentCutLP.C012.B 29 := by
  apply of_eval_le row_29 _ _ (-26:ℤ) (flat N E) coeff_29 const_29
  have h := S.cuts bits_29
  simp only [row_29,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_30 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 30 j*flat N E j) ≤ IndependentCutLP.C012.B 30 := by
  apply of_eval_le row_30 _ _ (-26:ℤ) (flat N E) coeff_30 const_30
  have h := S.cuts bits_30
  simp only [row_30,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_31 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 31 j*flat N E j) ≤ IndependentCutLP.C012.B 31 := by
  apply of_eval_le row_31 _ _ (-26:ℤ) (flat N E) coeff_31 const_31
  have h := S.cuts bits_31
  simp only [row_31,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_32 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 32 j*flat N E j) ≤ IndependentCutLP.C012.B 32 := by
  apply of_eval_le row_32 _ _ (-26:ℤ) (flat N E) coeff_32 const_32
  have h := S.cuts bits_32
  simp only [row_32,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_33 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 33 j*flat N E j) ≤ IndependentCutLP.C012.B 33 := by
  apply of_eval_le row_33 _ _ (-26:ℤ) (flat N E) coeff_33 const_33
  have h := S.cuts bits_33
  simp only [row_33,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_34 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 34 j*flat N E j) ≤ IndependentCutLP.C012.B 34 := by
  apply of_eval_le row_34 _ _ (-26:ℤ) (flat N E) coeff_34 const_34
  have h := S.cuts bits_34
  simp only [row_34,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_35 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 35 j*flat N E j) ≤ IndependentCutLP.C012.B 35 := by
  apply of_eval_le row_35 _ _ (-26:ℤ) (flat N E) coeff_35 const_35
  have h := S.cuts bits_35
  simp only [row_35,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_36 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 36 j*flat N E j) ≤ IndependentCutLP.C012.B 36 := by
  apply of_eval_le row_36 _ _ (-26:ℤ) (flat N E) coeff_36 const_36
  have h := S.cuts bits_36
  simp only [row_36,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_37 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 37 j*flat N E j) ≤ IndependentCutLP.C012.B 37 := by
  apply of_eval_le row_37 _ _ (-26:ℤ) (flat N E) coeff_37 const_37
  have h := S.cuts bits_37
  simp only [row_37,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_38 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 38 j*flat N E j) ≤ IndependentCutLP.C012.B 38 := by
  apply of_eval_le row_38 _ _ (-26:ℤ) (flat N E) coeff_38 const_38
  have h := S.cuts bits_38
  simp only [row_38,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_39 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 39 j*flat N E j) ≤ IndependentCutLP.C012.B 39 := by
  apply of_eval_le row_39 _ _ (-26:ℤ) (flat N E) coeff_39 const_39
  have h := S.cuts bits_39
  simp only [row_39,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_40 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 40 j*flat N E j) ≤ IndependentCutLP.C012.B 40 := by
  apply of_eval_le row_40 _ _ (-26:ℤ) (flat N E) coeff_40 const_40
  have h := S.cuts bits_40
  simp only [row_40,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_41 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 41 j*flat N E j) ≤ IndependentCutLP.C012.B 41 := by
  apply of_eval_le row_41 _ _ (-26:ℤ) (flat N E) coeff_41 const_41
  have h := S.cuts bits_41
  simp only [row_41,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_42 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 42 j*flat N E j) ≤ IndependentCutLP.C012.B 42 := by
  apply of_eval_le row_42 _ _ (-26:ℤ) (flat N E) coeff_42 const_42
  have h := S.cuts bits_42
  simp only [row_42,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_43 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 43 j*flat N E j) ≤ IndependentCutLP.C012.B 43 := by
  apply of_eval_le row_43 _ _ (-26:ℤ) (flat N E) coeff_43 const_43
  have h := S.cuts bits_43
  simp only [row_43,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_44 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 44 j*flat N E j) ≤ IndependentCutLP.C012.B 44 := by
  apply of_eval_le row_44 _ _ (-26:ℤ) (flat N E) coeff_44 const_44
  have h := S.cuts bits_44
  simp only [row_44,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_45 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 45 j*flat N E j) ≤ IndependentCutLP.C012.B 45 := by
  apply of_eval_le row_45 _ _ (-26:ℤ) (flat N E) coeff_45 const_45
  have h := S.cuts bits_45
  simp only [row_45,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_46 (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C012.A 46 j*flat N E j) ≤ IndependentCutLP.C012.B 46 := by
  apply of_eval_le row_46 _ _ (-26:ℤ) (flat N E) coeff_46 const_46
  have h := S.cuts bits_46
  simp only [row_46,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (N : Fin 15 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 121) : False := by
  apply IndependentCutLP.C012.impossible (flat N E)
  · intro j
    refine Fin.addCases (m:=15) (n:=40) (fun a => ?_) (fun k => ?_) j
    · simpa [flat] using S.npos a
    · simpa [flat] using S.epos k
  · intro i
    fin_cases i
    · exact valid_0 N E S
    · exact valid_1 N E S
    · exact valid_2 N E S
    · exact valid_3 N E S
    · exact valid_4 N E S
    · exact valid_5 N E S
    · exact valid_6 N E S
    · exact valid_7 N E S
    · exact valid_8 N E S
    · exact valid_9 N E S
    · exact valid_10 N E S
    · exact valid_11 N E S
    · exact valid_12 N E S
    · exact valid_13 N E S
    · exact valid_14 N E S
    · exact valid_15 N E S
    · exact valid_16 N E S
    · exact valid_17 N E S
    · exact valid_18 N E S
    · exact valid_19 N E S
    · exact valid_20 N E S
    · exact valid_21 N E S
    · exact valid_22 N E S
    · exact valid_23 N E S
    · exact valid_24 N E S
    · exact valid_25 N E S
    · exact valid_26 N E S
    · exact valid_27 N E S
    · exact valid_28 N E S
    · exact valid_29 N E S
    · exact valid_30 N E S
    · exact valid_31 N E S
    · exact valid_32 N E S
    · exact valid_33 N E S
    · exact valid_34 N E S
    · exact valid_35 N E S
    · exact valid_36 N E S
    · exact valid_37 N E S
    · exact valid_38 N E S
    · exact valid_39 N E S
    · exact valid_40 N E S
    · exact valid_41 N E S
    · exact valid_42 N E S
    · exact valid_43 N E S
    · exact valid_44 N E S
    · exact valid_45 N E S
    · exact valid_46 N E S
end FastCutCase.C012

-- CaseFast013

namespace FastCutCase.C013
open Finset ThreeExceptions FiniteCutTemplate GraphMass CutSummary CertifiedAffine AffineCut
abbrev T := NativeCutTemplate.C013.table
def row_0 : Form 57 := (verticesForm (n:=16) (e:=41))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_0 : ∀j,row_0.coeff j=IndependentCutLP.C013.A 0 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_0 : (22:ℤ)-row_0.constant=IndependentCutLP.C013.B 0 := by decide +kernel
def row_1 : Form 57 := (mForm T)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_1 : ∀j,row_1.coeff j=IndependentCutLP.C013.A 1 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_1 : (121:ℤ)-row_1.constant=IndependentCutLP.C013.B 1 := by decide +kernel
def row_2 : Form 57 := (.scale (-1) (nv (n:=16) (e:=41) (T.cycle 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_2 : ∀j,row_2.coeff j=IndependentCutLP.C013.A 2 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_2 : (-1:ℤ)-row_2.constant=IndependentCutLP.C013.B 2 := by decide +kernel
def row_3 : Form 57 := (.scale (-1) (nv (n:=16) (e:=41) (T.cycle 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_3 : ∀j,row_3.coeff j=IndependentCutLP.C013.A 3 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_3 : (-1:ℤ)-row_3.constant=IndependentCutLP.C013.B 3 := by decide +kernel
def row_4 : Form 57 := (.scale (-1) (nv (n:=16) (e:=41) (T.cycle 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_4 : ∀j,row_4.coeff j=IndependentCutLP.C013.A 4 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_4 : (-1:ℤ)-row_4.constant=IndependentCutLP.C013.B 4 := by decide +kernel
def row_5 : Form 57 := (.plus (degreeForm T 0) (.scale (-12) (nv (n:=16) (e:=41) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_5 : ∀j,row_5.coeff j=IndependentCutLP.C013.A 5 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_5 : (0:ℤ)-row_5.constant=IndependentCutLP.C013.B 5 := by decide +kernel
def row_6 : Form 57 := (.plus (degreeForm T 1) (.scale (-12) (nv (n:=16) (e:=41) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_6 : ∀j,row_6.coeff j=IndependentCutLP.C013.A 6 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_6 : (0:ℤ)-row_6.constant=IndependentCutLP.C013.B 6 := by decide +kernel
def row_7 : Form 57 := (.plus (degreeForm T 3) (.scale (-12) (nv (n:=16) (e:=41) 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_7 : ∀j,row_7.coeff j=IndependentCutLP.C013.A 7 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_7 : (0:ℤ)-row_7.constant=IndependentCutLP.C013.B 7 := by decide +kernel
def row_8 : Form 57 := (.plus (degreeForm T 4) (.scale (-12) (nv (n:=16) (e:=41) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_8 : ∀j,row_8.coeff j=IndependentCutLP.C013.A 8 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_8 : (0:ℤ)-row_8.constant=IndependentCutLP.C013.B 8 := by decide +kernel
def row_9 : Form 57 := (.plus (degreeForm T 5) (.scale (-12) (nv (n:=16) (e:=41) 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_9 : ∀j,row_9.coeff j=IndependentCutLP.C013.A 9 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_9 : (0:ℤ)-row_9.constant=IndependentCutLP.C013.B 9 := by decide +kernel
def row_10 : Form 57 := (.plus (degreeForm T 6) (.scale (-12) (nv (n:=16) (e:=41) 6)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_10 : ∀j,row_10.coeff j=IndependentCutLP.C013.A 10 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_10 : (0:ℤ)-row_10.constant=IndependentCutLP.C013.B 10 := by decide +kernel
def row_11 : Form 57 := (.plus (degreeForm T 7) (.scale (-12) (nv (n:=16) (e:=41) 7)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_11 : ∀j,row_11.coeff j=IndependentCutLP.C013.A 11 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_11 : (0:ℤ)-row_11.constant=IndependentCutLP.C013.B 11 := by decide +kernel
def row_12 : Form 57 := (.plus (degreeForm T 9) (.scale (-12) (nv (n:=16) (e:=41) 9)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_12 : ∀j,row_12.coeff j=IndependentCutLP.C013.A 12 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_12 : (0:ℤ)-row_12.constant=IndependentCutLP.C013.B 12 := by decide +kernel
def row_13 : Form 57 := (.plus (degreeForm T 11) (.scale (-12) (nv (n:=16) (e:=41) 11)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_13 : ∀j,row_13.coeff j=IndependentCutLP.C013.A 13 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_13 : (0:ℤ)-row_13.constant=IndependentCutLP.C013.B 13 := by decide +kernel
def row_14 : Form 57 := (.plus (degreeForm T 12) (.scale (-12) (nv (n:=16) (e:=41) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_14 : ∀j,row_14.coeff j=IndependentCutLP.C013.A 14 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_14 : (0:ℤ)-row_14.constant=IndependentCutLP.C013.B 14 := by decide +kernel
def row_15 : Form 57 := (.plus (degreeForm T 14) (.scale (-12) (nv (n:=16) (e:=41) 14)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_15 : ∀j,row_15.coeff j=IndependentCutLP.C013.A 15 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_15 : (0:ℤ)-row_15.constant=IndependentCutLP.C013.B 15 := by decide +kernel
def colors_16 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 0 else if x=1 then 2 else 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_16 : properAway T 0 colors_16 := by unfold properAway; decide +kernel
def row_16 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 0 colors_16))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_16 : ∀j,row_16.coeff j=IndependentCutLP.C013.A 16 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_16 : (-130:ℤ)-row_16.constant=IndependentCutLP.C013.B 16 := by decide +kernel
def colors_17 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 1 else if x=1 then 0 else 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_17 : properAway T 1 colors_17 := by unfold properAway; decide +kernel
def row_17 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 1 colors_17))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_17 : ∀j,row_17.coeff j=IndependentCutLP.C013.A 17 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_17 : (-130:ℤ)-row_17.constant=IndependentCutLP.C013.B 17 := by decide +kernel
def colors_18 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 1 else if x=1 then 0 else 2)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_18 : properAway T 1 colors_18 := by unfold properAway; decide +kernel
def row_18 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 1 colors_18))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_18 : ∀j,row_18.coeff j=IndependentCutLP.C013.A 18 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_18 : (-130:ℤ)-row_18.constant=IndependentCutLP.C013.B 18 := by decide +kernel
def colors_19 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 1 else if x=1 then 2 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_19 : properAway T 2 colors_19 := by unfold properAway; decide +kernel
def row_19 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_19))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_19 : ∀j,row_19.coeff j=IndependentCutLP.C013.A 19 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_19 : (-130:ℤ)-row_19.constant=IndependentCutLP.C013.B 19 := by decide +kernel
def colors_20 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 4 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_20 : properAway T 2 colors_20 := by unfold properAway; decide +kernel
def row_20 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_20))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_20 : ∀j,row_20.coeff j=IndependentCutLP.C013.A 20 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_20 : (-130:ℤ)-row_20.constant=IndependentCutLP.C013.B 20 := by decide +kernel
def row_21 : Form 57 := (.plus (nv (n:=16) (e:=41) (T.ends 1).1) (.scale (-1) (ev (n:=16) (e:=41) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_21 : ∀j,row_21.coeff j=IndependentCutLP.C013.A 21 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_21 : (0:ℤ)-row_21.constant=IndependentCutLP.C013.B 21 := by decide +kernel
def row_22 : Form 57 := (.plus (.plus (nv (n:=16) (e:=41) (T.ends 4).1) (nv (n:=16) (e:=41) (T.ends 4).2)) (.scale (-1) (ev (n:=16) (e:=41) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_22 : ∀j,row_22.coeff j=IndependentCutLP.C013.A 22 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_22 : (1:ℤ)-row_22.constant=IndependentCutLP.C013.B 22 := by decide +kernel
def row_23 : Form 57 := (.plus (nv (n:=16) (e:=41) (T.ends 18).1) (.scale (-1) (ev (n:=16) (e:=41) 18)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_23 : ∀j,row_23.coeff j=IndependentCutLP.C013.A 23 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_23 : (0:ℤ)-row_23.constant=IndependentCutLP.C013.B 23 := by decide +kernel
def row_24 : Form 57 := (.plus (nv (n:=16) (e:=41) (T.ends 21).1) (.scale (-1) (ev (n:=16) (e:=41) 21)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_24 : ∀j,row_24.coeff j=IndependentCutLP.C013.A 24 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_24 : (0:ℤ)-row_24.constant=IndependentCutLP.C013.B 24 := by decide +kernel
def row_25 : Form 57 := (.plus (.plus (nv (n:=16) (e:=41) (T.ends 23).1) (nv (n:=16) (e:=41) (T.ends 23).2)) (.scale (-1) (ev (n:=16) (e:=41) 23)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_25 : ∀j,row_25.coeff j=IndependentCutLP.C013.A 25 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_25 : (1:ℤ)-row_25.constant=IndependentCutLP.C013.B 25 := by decide +kernel
def row_26 : Form 57 := (.plus (nv (n:=16) (e:=41) (T.ends 30).2) (.scale (-1) (ev (n:=16) (e:=41) 30)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_26 : ∀j,row_26.coeff j=IndependentCutLP.C013.A 26 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_26 : (0:ℤ)-row_26.constant=IndependentCutLP.C013.B 26 := by decide +kernel
def row_27 : Form 57 := (.plus (nv (n:=16) (e:=41) (T.ends 31).2) (.scale (-1) (ev (n:=16) (e:=41) 31)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_27 : ∀j,row_27.coeff j=IndependentCutLP.C013.A 27 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_27 : (0:ℤ)-row_27.constant=IndependentCutLP.C013.B 27 := by decide +kernel
def row_28 : Form 57 := (.plus (.plus (nv (n:=16) (e:=41) (T.ends 33).1) (nv (n:=16) (e:=41) (T.ends 33).2)) (.scale (-1) (ev (n:=16) (e:=41) 33)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_28 : ∀j,row_28.coeff j=IndependentCutLP.C013.A 28 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_28 : (1:ℤ)-row_28.constant=IndependentCutLP.C013.B 28 := by decide +kernel
def bits_29 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (81528 : ℕ).testBit a.val) (fun x => (81528 : ℕ).testBit (16+x.val))
def row_29 : Form 57 := (.scale (-1) (cutForm T bits_29))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_29 : ∀j,row_29.coeff j=IndependentCutLP.C013.A 29 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_29 : (-26:ℤ)-row_29.constant=IndependentCutLP.C013.B 29 := by decide +kernel
def bits_30 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (442752 : ℕ).testBit a.val) (fun x => (442752 : ℕ).testBit (16+x.val))
def row_30 : Form 57 := (.scale (-1) (cutForm T bits_30))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_30 : ∀j,row_30.coeff j=IndependentCutLP.C013.A 30 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_30 : (-26:ℤ)-row_30.constant=IndependentCutLP.C013.B 30 := by decide +kernel
def bits_31 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (130680 : ℕ).testBit a.val) (fun x => (130680 : ℕ).testBit (16+x.val))
def row_31 : Form 57 := (.scale (-1) (cutForm T bits_31))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_31 : ∀j,row_31.coeff j=IndependentCutLP.C013.A 31 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_31 : (-26:ℤ)-row_31.constant=IndependentCutLP.C013.B 31 := by decide +kernel
def bits_32 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (377336 : ℕ).testBit a.val) (fun x => (377336 : ℕ).testBit (16+x.val))
def row_32 : Form 57 := (.scale (-1) (cutForm T bits_32))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_32 : ∀j,row_32.coeff j=IndependentCutLP.C013.A 32 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_32 : (-26:ℤ)-row_32.constant=IndependentCutLP.C013.B 32 := by decide +kernel
def bits_33 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (129080 : ℕ).testBit a.val) (fun x => (129080 : ℕ).testBit (16+x.val))
def row_33 : Form 57 := (.scale (-1) (cutForm T bits_33))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_33 : ∀j,row_33.coeff j=IndependentCutLP.C013.A 33 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_33 : (-26:ℤ)-row_33.constant=IndependentCutLP.C013.B 33 := by decide +kernel
def bits_34 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (147046 : ℕ).testBit a.val) (fun x => (147046 : ℕ).testBit (16+x.val))
def row_34 : Form 57 := (.scale (-1) (cutForm T bits_34))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_34 : ∀j,row_34.coeff j=IndependentCutLP.C013.A 34 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_34 : (-26:ℤ)-row_34.constant=IndependentCutLP.C013.B 34 := by decide +kernel
def bits_35 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (379512 : ℕ).testBit a.val) (fun x => (379512 : ℕ).testBit (16+x.val))
def row_35 : Form 57 := (.scale (-1) (cutForm T bits_35))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_35 : ∀j,row_35.coeff j=IndependentCutLP.C013.A 35 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_35 : (-26:ℤ)-row_35.constant=IndependentCutLP.C013.B 35 := by decide +kernel
def bits_36 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (123128 : ℕ).testBit a.val) (fun x => (123128 : ℕ).testBit (16+x.val))
def row_36 : Form 57 := (.scale (-1) (cutForm T bits_36))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_36 : ∀j,row_36.coeff j=IndependentCutLP.C013.A 36 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_36 : (-26:ℤ)-row_36.constant=IndependentCutLP.C013.B 36 := by decide +kernel
def bits_37 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (113272 : ℕ).testBit a.val) (fun x => (113272 : ℕ).testBit (16+x.val))
def row_37 : Form 57 := (.scale (-1) (cutForm T bits_37))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_37 : ∀j,row_37.coeff j=IndependentCutLP.C013.A 37 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_37 : (-26:ℤ)-row_37.constant=IndependentCutLP.C013.B 37 := by decide +kernel
def bits_38 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (442754 : ℕ).testBit a.val) (fun x => (442754 : ℕ).testBit (16+x.val))
def row_38 : Form 57 := (.scale (-1) (cutForm T bits_38))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_38 : ∀j,row_38.coeff j=IndependentCutLP.C013.A 38 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_38 : (-26:ℤ)-row_38.constant=IndependentCutLP.C013.B 38 := by decide +kernel
def bits_39 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (113784 : ℕ).testBit a.val) (fun x => (113784 : ℕ).testBit (16+x.val))
def row_39 : Form 57 := (.scale (-1) (cutForm T bits_39))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_39 : ∀j,row_39.coeff j=IndependentCutLP.C013.A 39 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_39 : (-26:ℤ)-row_39.constant=IndependentCutLP.C013.B 39 := by decide +kernel
def bits_40 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (129144 : ℕ).testBit a.val) (fun x => (129144 : ℕ).testBit (16+x.val))
def row_40 : Form 57 := (.scale (-1) (cutForm T bits_40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_40 : ∀j,row_40.coeff j=IndependentCutLP.C013.A 40 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_40 : (-26:ℤ)-row_40.constant=IndependentCutLP.C013.B 40 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_0 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 0 j*flat N E j) ≤ IndependentCutLP.C013.B 0 := by
  apply of_eval_le row_0 _ _ (22:ℤ) (flat N E) coeff_0 const_0
  have h := S.vertices
  simp only [row_0,eval_vertices]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_1 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 1 j*flat N E j) ≤ IndependentCutLP.C013.B 1 := by
  apply of_eval_le row_1 _ _ (121:ℤ) (flat N E) coeff_1 const_1
  have h := S.edgeHi
  simp only [row_1,eval_m]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_2 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 2 j*flat N E j) ≤ IndependentCutLP.C013.B 2 := by
  apply of_eval_le row_2 _ _ (-1:ℤ) (flat N E) coeff_2 const_2
  have h := S.exists_cycle 0
  simp only [row_2,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_3 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 3 j*flat N E j) ≤ IndependentCutLP.C013.B 3 := by
  apply of_eval_le row_3 _ _ (-1:ℤ) (flat N E) coeff_3 const_3
  have h := S.exists_cycle 1
  simp only [row_3,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_4 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 4 j*flat N E j) ≤ IndependentCutLP.C013.B 4 := by
  apply of_eval_le row_4 _ _ (-1:ℤ) (flat N E) coeff_4 const_4
  have h := S.exists_cycle 3
  simp only [row_4,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_5 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 5 j*flat N E j) ≤ IndependentCutLP.C013.B 5 := by
  apply of_eval_le row_5 _ _ (0:ℤ) (flat N E) coeff_5 const_5
  have h := S.degrees 0
  simp only [row_5,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_6 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 6 j*flat N E j) ≤ IndependentCutLP.C013.B 6 := by
  apply of_eval_le row_6 _ _ (0:ℤ) (flat N E) coeff_6 const_6
  have h := S.degrees 1
  simp only [row_6,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_7 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 7 j*flat N E j) ≤ IndependentCutLP.C013.B 7 := by
  apply of_eval_le row_7 _ _ (0:ℤ) (flat N E) coeff_7 const_7
  have h := S.degrees 3
  simp only [row_7,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_8 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 8 j*flat N E j) ≤ IndependentCutLP.C013.B 8 := by
  apply of_eval_le row_8 _ _ (0:ℤ) (flat N E) coeff_8 const_8
  have h := S.degrees 4
  simp only [row_8,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_9 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 9 j*flat N E j) ≤ IndependentCutLP.C013.B 9 := by
  apply of_eval_le row_9 _ _ (0:ℤ) (flat N E) coeff_9 const_9
  have h := S.degrees 5
  simp only [row_9,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_10 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 10 j*flat N E j) ≤ IndependentCutLP.C013.B 10 := by
  apply of_eval_le row_10 _ _ (0:ℤ) (flat N E) coeff_10 const_10
  have h := S.degrees 6
  simp only [row_10,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_11 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 11 j*flat N E j) ≤ IndependentCutLP.C013.B 11 := by
  apply of_eval_le row_11 _ _ (0:ℤ) (flat N E) coeff_11 const_11
  have h := S.degrees 7
  simp only [row_11,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_12 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 12 j*flat N E j) ≤ IndependentCutLP.C013.B 12 := by
  apply of_eval_le row_12 _ _ (0:ℤ) (flat N E) coeff_12 const_12
  have h := S.degrees 9
  simp only [row_12,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_13 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 13 j*flat N E j) ≤ IndependentCutLP.C013.B 13 := by
  apply of_eval_le row_13 _ _ (0:ℤ) (flat N E) coeff_13 const_13
  have h := S.degrees 11
  simp only [row_13,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_14 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 14 j*flat N E j) ≤ IndependentCutLP.C013.B 14 := by
  apply of_eval_le row_14 _ _ (0:ℤ) (flat N E) coeff_14 const_14
  have h := S.degrees 12
  simp only [row_14,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_15 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 15 j*flat N E j) ≤ IndependentCutLP.C013.B 15 := by
  apply of_eval_le row_15 _ _ (0:ℤ) (flat N E) coeff_15 const_15
  have h := S.degrees 14
  simp only [row_15,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_16 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 16 j*flat N E j) ≤ IndependentCutLP.C013.B 16 := by
  apply of_eval_le row_16 _ _ (-130:ℤ) (flat N E) coeff_16 const_16
  have h := S.repairs 0 colors_16 proper_16
  simp only [row_16,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_17 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 17 j*flat N E j) ≤ IndependentCutLP.C013.B 17 := by
  apply of_eval_le row_17 _ _ (-130:ℤ) (flat N E) coeff_17 const_17
  have h := S.repairs 1 colors_17 proper_17
  simp only [row_17,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_18 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 18 j*flat N E j) ≤ IndependentCutLP.C013.B 18 := by
  apply of_eval_le row_18 _ _ (-130:ℤ) (flat N E) coeff_18 const_18
  have h := S.repairs 1 colors_18 proper_18
  simp only [row_18,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_19 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 19 j*flat N E j) ≤ IndependentCutLP.C013.B 19 := by
  apply of_eval_le row_19 _ _ (-130:ℤ) (flat N E) coeff_19 const_19
  have h := S.repairs 2 colors_19 proper_19
  simp only [row_19,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_20 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 20 j*flat N E j) ≤ IndependentCutLP.C013.B 20 := by
  apply of_eval_le row_20 _ _ (-130:ℤ) (flat N E) coeff_20 const_20
  have h := S.repairs 2 colors_20 proper_20
  simp only [row_20,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_21 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 21 j*flat N E j) ≤ IndependentCutLP.C013.B 21 := by
  apply of_eval_le row_21 _ _ (0:ℤ) (flat N E) coeff_21 const_21
  have h := S.cycle_right 1 0 (by decide +kernel)
  simp only [row_21,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_22 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 22 j*flat N E j) ≤ IndependentCutLP.C013.B 22 := by
  apply of_eval_le row_22 _ _ (1:ℤ) (flat N E) coeff_22 const_22
  have h := S.cycle_both 4 1 0 (by decide +kernel) (by decide +kernel)
  simp only [row_22,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_23 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 23 j*flat N E j) ≤ IndependentCutLP.C013.B 23 := by
  apply of_eval_le row_23 _ _ (0:ℤ) (flat N E) coeff_23 const_23
  have h := S.cycle_right 18 2 (by decide +kernel)
  simp only [row_23,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_24 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 24 j*flat N E j) ≤ IndependentCutLP.C013.B 24 := by
  apply of_eval_le row_24 _ _ (0:ℤ) (flat N E) coeff_24 const_24
  have h := S.cycle_right 21 2 (by decide +kernel)
  simp only [row_24,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_25 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 25 j*flat N E j) ≤ IndependentCutLP.C013.B 25 := by
  apply of_eval_le row_25 _ _ (1:ℤ) (flat N E) coeff_25 const_25
  have h := S.cycle_both 23 3 2 (by decide +kernel) (by decide +kernel)
  simp only [row_25,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_26 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 26 j*flat N E j) ≤ IndependentCutLP.C013.B 26 := by
  apply of_eval_le row_26 _ _ (0:ℤ) (flat N E) coeff_26 const_26
  have h := S.cycle_left 30 4 (by decide +kernel)
  simp only [row_26,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_27 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 27 j*flat N E j) ≤ IndependentCutLP.C013.B 27 := by
  apply of_eval_le row_27 _ _ (0:ℤ) (flat N E) coeff_27 const_27
  have h := S.cycle_left 31 4 (by decide +kernel)
  simp only [row_27,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_28 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 28 j*flat N E j) ≤ IndependentCutLP.C013.B 28 := by
  apply of_eval_le row_28 _ _ (1:ℤ) (flat N E) coeff_28 const_28
  have h := S.cycle_both 33 4 3 (by decide +kernel) (by decide +kernel)
  simp only [row_28,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_29 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 29 j*flat N E j) ≤ IndependentCutLP.C013.B 29 := by
  apply of_eval_le row_29 _ _ (-26:ℤ) (flat N E) coeff_29 const_29
  have h := S.cuts bits_29
  simp only [row_29,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_30 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 30 j*flat N E j) ≤ IndependentCutLP.C013.B 30 := by
  apply of_eval_le row_30 _ _ (-26:ℤ) (flat N E) coeff_30 const_30
  have h := S.cuts bits_30
  simp only [row_30,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_31 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 31 j*flat N E j) ≤ IndependentCutLP.C013.B 31 := by
  apply of_eval_le row_31 _ _ (-26:ℤ) (flat N E) coeff_31 const_31
  have h := S.cuts bits_31
  simp only [row_31,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_32 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 32 j*flat N E j) ≤ IndependentCutLP.C013.B 32 := by
  apply of_eval_le row_32 _ _ (-26:ℤ) (flat N E) coeff_32 const_32
  have h := S.cuts bits_32
  simp only [row_32,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_33 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 33 j*flat N E j) ≤ IndependentCutLP.C013.B 33 := by
  apply of_eval_le row_33 _ _ (-26:ℤ) (flat N E) coeff_33 const_33
  have h := S.cuts bits_33
  simp only [row_33,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_34 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 34 j*flat N E j) ≤ IndependentCutLP.C013.B 34 := by
  apply of_eval_le row_34 _ _ (-26:ℤ) (flat N E) coeff_34 const_34
  have h := S.cuts bits_34
  simp only [row_34,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_35 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 35 j*flat N E j) ≤ IndependentCutLP.C013.B 35 := by
  apply of_eval_le row_35 _ _ (-26:ℤ) (flat N E) coeff_35 const_35
  have h := S.cuts bits_35
  simp only [row_35,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_36 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 36 j*flat N E j) ≤ IndependentCutLP.C013.B 36 := by
  apply of_eval_le row_36 _ _ (-26:ℤ) (flat N E) coeff_36 const_36
  have h := S.cuts bits_36
  simp only [row_36,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_37 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 37 j*flat N E j) ≤ IndependentCutLP.C013.B 37 := by
  apply of_eval_le row_37 _ _ (-26:ℤ) (flat N E) coeff_37 const_37
  have h := S.cuts bits_37
  simp only [row_37,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_38 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 38 j*flat N E j) ≤ IndependentCutLP.C013.B 38 := by
  apply of_eval_le row_38 _ _ (-26:ℤ) (flat N E) coeff_38 const_38
  have h := S.cuts bits_38
  simp only [row_38,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_39 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 39 j*flat N E j) ≤ IndependentCutLP.C013.B 39 := by
  apply of_eval_le row_39 _ _ (-26:ℤ) (flat N E) coeff_39 const_39
  have h := S.cuts bits_39
  simp only [row_39,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_40 (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C013.A 40 j*flat N E j) ≤ IndependentCutLP.C013.B 40 := by
  apply of_eval_le row_40 _ _ (-26:ℤ) (flat N E) coeff_40 const_40
  have h := S.cuts bits_40
  simp only [row_40,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (N : Fin 16 → ℤ) (E : Fin 41 → ℤ) (S : Feasible T N E 12 121) : False := by
  apply IndependentCutLP.C013.impossible (flat N E)
  · intro j
    refine Fin.addCases (m:=16) (n:=41) (fun a => ?_) (fun k => ?_) j
    · simpa [flat] using S.npos a
    · simpa [flat] using S.epos k
  · intro i
    fin_cases i
    · exact valid_0 N E S
    · exact valid_1 N E S
    · exact valid_2 N E S
    · exact valid_3 N E S
    · exact valid_4 N E S
    · exact valid_5 N E S
    · exact valid_6 N E S
    · exact valid_7 N E S
    · exact valid_8 N E S
    · exact valid_9 N E S
    · exact valid_10 N E S
    · exact valid_11 N E S
    · exact valid_12 N E S
    · exact valid_13 N E S
    · exact valid_14 N E S
    · exact valid_15 N E S
    · exact valid_16 N E S
    · exact valid_17 N E S
    · exact valid_18 N E S
    · exact valid_19 N E S
    · exact valid_20 N E S
    · exact valid_21 N E S
    · exact valid_22 N E S
    · exact valid_23 N E S
    · exact valid_24 N E S
    · exact valid_25 N E S
    · exact valid_26 N E S
    · exact valid_27 N E S
    · exact valid_28 N E S
    · exact valid_29 N E S
    · exact valid_30 N E S
    · exact valid_31 N E S
    · exact valid_32 N E S
    · exact valid_33 N E S
    · exact valid_34 N E S
    · exact valid_35 N E S
    · exact valid_36 N E S
    · exact valid_37 N E S
    · exact valid_38 N E S
    · exact valid_39 N E S
    · exact valid_40 N E S
end FastCutCase.C013

-- CaseFast014

namespace FastCutCase.C014
open Finset ThreeExceptions FiniteCutTemplate GraphMass CutSummary CertifiedAffine AffineCut
abbrev T := NativeCutTemplate.C014.table
def row_0 : Form 60 := (verticesForm (n:=16) (e:=44))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_0 : ∀j,row_0.coeff j=IndependentCutLP.C014.A 0 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_0 : (22:ℤ)-row_0.constant=IndependentCutLP.C014.B 0 := by decide +kernel
def row_1 : Form 60 := (mForm T)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_1 : ∀j,row_1.coeff j=IndependentCutLP.C014.A 1 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_1 : (121:ℤ)-row_1.constant=IndependentCutLP.C014.B 1 := by decide +kernel
def row_2 : Form 60 := (.scale (-1) (nv (n:=16) (e:=44) (T.cycle 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_2 : ∀j,row_2.coeff j=IndependentCutLP.C014.A 2 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_2 : (-1:ℤ)-row_2.constant=IndependentCutLP.C014.B 2 := by decide +kernel
def row_3 : Form 60 := (.scale (-1) (nv (n:=16) (e:=44) (T.cycle 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_3 : ∀j,row_3.coeff j=IndependentCutLP.C014.A 3 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_3 : (-1:ℤ)-row_3.constant=IndependentCutLP.C014.B 3 := by decide +kernel
def row_4 : Form 60 := (.scale (-1) (nv (n:=16) (e:=44) (T.cycle 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_4 : ∀j,row_4.coeff j=IndependentCutLP.C014.A 4 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_4 : (-1:ℤ)-row_4.constant=IndependentCutLP.C014.B 4 := by decide +kernel
def row_5 : Form 60 := (.plus (degreeForm T 0) (.scale (-12) (nv (n:=16) (e:=44) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_5 : ∀j,row_5.coeff j=IndependentCutLP.C014.A 5 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_5 : (0:ℤ)-row_5.constant=IndependentCutLP.C014.B 5 := by decide +kernel
def row_6 : Form 60 := (.plus (degreeForm T 1) (.scale (-12) (nv (n:=16) (e:=44) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_6 : ∀j,row_6.coeff j=IndependentCutLP.C014.A 6 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_6 : (0:ℤ)-row_6.constant=IndependentCutLP.C014.B 6 := by decide +kernel
def row_7 : Form 60 := (.plus (degreeForm T 2) (.scale (-12) (nv (n:=16) (e:=44) 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_7 : ∀j,row_7.coeff j=IndependentCutLP.C014.A 7 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_7 : (0:ℤ)-row_7.constant=IndependentCutLP.C014.B 7 := by decide +kernel
def row_8 : Form 60 := (.plus (degreeForm T 3) (.scale (-12) (nv (n:=16) (e:=44) 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_8 : ∀j,row_8.coeff j=IndependentCutLP.C014.A 8 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_8 : (0:ℤ)-row_8.constant=IndependentCutLP.C014.B 8 := by decide +kernel
def row_9 : Form 60 := (.plus (degreeForm T 4) (.scale (-12) (nv (n:=16) (e:=44) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_9 : ∀j,row_9.coeff j=IndependentCutLP.C014.A 9 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_9 : (0:ℤ)-row_9.constant=IndependentCutLP.C014.B 9 := by decide +kernel
def row_10 : Form 60 := (.plus (degreeForm T 5) (.scale (-12) (nv (n:=16) (e:=44) 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_10 : ∀j,row_10.coeff j=IndependentCutLP.C014.A 10 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_10 : (0:ℤ)-row_10.constant=IndependentCutLP.C014.B 10 := by decide +kernel
def row_11 : Form 60 := (.plus (degreeForm T 6) (.scale (-12) (nv (n:=16) (e:=44) 6)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_11 : ∀j,row_11.coeff j=IndependentCutLP.C014.A 11 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_11 : (0:ℤ)-row_11.constant=IndependentCutLP.C014.B 11 := by decide +kernel
def row_12 : Form 60 := (.plus (degreeForm T 9) (.scale (-12) (nv (n:=16) (e:=44) 9)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_12 : ∀j,row_12.coeff j=IndependentCutLP.C014.A 12 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_12 : (0:ℤ)-row_12.constant=IndependentCutLP.C014.B 12 := by decide +kernel
def row_13 : Form 60 := (.plus (degreeForm T 12) (.scale (-12) (nv (n:=16) (e:=44) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_13 : ∀j,row_13.coeff j=IndependentCutLP.C014.A 13 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_13 : (0:ℤ)-row_13.constant=IndependentCutLP.C014.B 13 := by decide +kernel
def row_14 : Form 60 := (.plus (degreeForm T 13) (.scale (-12) (nv (n:=16) (e:=44) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_14 : ∀j,row_14.coeff j=IndependentCutLP.C014.A 14 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_14 : (0:ℤ)-row_14.constant=IndependentCutLP.C014.B 14 := by decide +kernel
def row_15 : Form 60 := (.plus (degreeForm T 14) (.scale (-12) (nv (n:=16) (e:=44) 14)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_15 : ∀j,row_15.coeff j=IndependentCutLP.C014.A 15 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_15 : (0:ℤ)-row_15.constant=IndependentCutLP.C014.B 15 := by decide +kernel
def row_16 : Form 60 := (.plus (degreeForm T 15) (.scale (-12) (nv (n:=16) (e:=44) 15)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_16 : ∀j,row_16.coeff j=IndependentCutLP.C014.A 16 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_16 : (0:ℤ)-row_16.constant=IndependentCutLP.C014.B 16 := by decide +kernel
def colors_17 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 0 else if x=1 then 2 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_17 : properAway T 0 colors_17 := by unfold properAway; decide +kernel
def row_17 : Form 60 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 0 colors_17))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_17 : ∀j,row_17.coeff j=IndependentCutLP.C014.A 17 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_17 : (-130:ℤ)-row_17.constant=IndependentCutLP.C014.B 17 := by decide +kernel
def colors_18 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 0 else if x=1 then 2 else 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_18 : properAway T 0 colors_18 := by unfold properAway; decide +kernel
def row_18 : Form 60 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 0 colors_18))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_18 : ∀j,row_18.coeff j=IndependentCutLP.C014.A 18 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_18 : (-130:ℤ)-row_18.constant=IndependentCutLP.C014.B 18 := by decide +kernel
def colors_19 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 0 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_19 : properAway T 0 colors_19 := by unfold properAway; decide +kernel
def row_19 : Form 60 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 0 colors_19))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_19 : ∀j,row_19.coeff j=IndependentCutLP.C014.A 19 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_19 : (-130:ℤ)-row_19.constant=IndependentCutLP.C014.B 19 := by decide +kernel
def colors_20 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 4 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_20 : properAway T 1 colors_20 := by unfold properAway; decide +kernel
def row_20 : Form 60 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 1 colors_20))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_20 : ∀j,row_20.coeff j=IndependentCutLP.C014.A 20 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_20 : (-130:ℤ)-row_20.constant=IndependentCutLP.C014.B 20 := by decide +kernel
def colors_21 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 1 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_21 : properAway T 2 colors_21 := by unfold properAway; decide +kernel
def row_21 : Form 60 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_21))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_21 : ∀j,row_21.coeff j=IndependentCutLP.C014.A 21 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_21 : (-130:ℤ)-row_21.constant=IndependentCutLP.C014.B 21 := by decide +kernel
def colors_22 : Fin 16 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 4 else if x=1 then 0 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_22 : properAway T 2 colors_22 := by unfold properAway; decide +kernel
def row_22 : Form 60 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_22))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_22 : ∀j,row_22.coeff j=IndependentCutLP.C014.A 22 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_22 : (-130:ℤ)-row_22.constant=IndependentCutLP.C014.B 22 := by decide +kernel
def row_23 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 8).2) (.scale (-1) (ev (n:=16) (e:=44) 8)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_23 : ∀j,row_23.coeff j=IndependentCutLP.C014.A 23 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_23 : (0:ℤ)-row_23.constant=IndependentCutLP.C014.B 23 := by decide +kernel
def row_24 : Form 60 := (.plus (.plus (nv (n:=16) (e:=44) (T.ends 9).1) (nv (n:=16) (e:=44) (T.ends 9).2)) (.scale (-1) (ev (n:=16) (e:=44) 9)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_24 : ∀j,row_24.coeff j=IndependentCutLP.C014.A 24 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_24 : (1:ℤ)-row_24.constant=IndependentCutLP.C014.B 24 := by decide +kernel
def row_25 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 13).1) (.scale (-1) (ev (n:=16) (e:=44) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_25 : ∀j,row_25.coeff j=IndependentCutLP.C014.A 25 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_25 : (0:ℤ)-row_25.constant=IndependentCutLP.C014.B 25 := by decide +kernel
def row_26 : Form 60 := (.plus (.plus (nv (n:=16) (e:=44) (T.ends 18).1) (nv (n:=16) (e:=44) (T.ends 18).2)) (.scale (-1) (ev (n:=16) (e:=44) 18)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_26 : ∀j,row_26.coeff j=IndependentCutLP.C014.A 26 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_26 : (1:ℤ)-row_26.constant=IndependentCutLP.C014.B 26 := by decide +kernel
def row_27 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 19).2) (.scale (-1) (ev (n:=16) (e:=44) 19)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_27 : ∀j,row_27.coeff j=IndependentCutLP.C014.A 27 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_27 : (0:ℤ)-row_27.constant=IndependentCutLP.C014.B 27 := by decide +kernel
def row_28 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 20).2) (.scale (-1) (ev (n:=16) (e:=44) 20)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_28 : ∀j,row_28.coeff j=IndependentCutLP.C014.A 28 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_28 : (0:ℤ)-row_28.constant=IndependentCutLP.C014.B 28 := by decide +kernel
def row_29 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 21).1) (.scale (-1) (ev (n:=16) (e:=44) 21)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_29 : ∀j,row_29.coeff j=IndependentCutLP.C014.A 29 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_29 : (0:ℤ)-row_29.constant=IndependentCutLP.C014.B 29 := by decide +kernel
def row_30 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 23).1) (.scale (-1) (ev (n:=16) (e:=44) 23)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_30 : ∀j,row_30.coeff j=IndependentCutLP.C014.A 30 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_30 : (0:ℤ)-row_30.constant=IndependentCutLP.C014.B 30 := by decide +kernel
def row_31 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 27).1) (.scale (-1) (ev (n:=16) (e:=44) 27)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_31 : ∀j,row_31.coeff j=IndependentCutLP.C014.A 31 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_31 : (0:ℤ)-row_31.constant=IndependentCutLP.C014.B 31 := by decide +kernel
def row_32 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 28).1) (.scale (-1) (ev (n:=16) (e:=44) 28)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_32 : ∀j,row_32.coeff j=IndependentCutLP.C014.A 32 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_32 : (0:ℤ)-row_32.constant=IndependentCutLP.C014.B 32 := by decide +kernel
def row_33 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 35).2) (.scale (-1) (ev (n:=16) (e:=44) 35)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_33 : ∀j,row_33.coeff j=IndependentCutLP.C014.A 33 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_33 : (0:ℤ)-row_33.constant=IndependentCutLP.C014.B 33 := by decide +kernel
def row_34 : Form 60 := (.plus (.plus (nv (n:=16) (e:=44) (T.ends 36).1) (nv (n:=16) (e:=44) (T.ends 36).2)) (.scale (-1) (ev (n:=16) (e:=44) 36)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_34 : ∀j,row_34.coeff j=IndependentCutLP.C014.A 34 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_34 : (1:ℤ)-row_34.constant=IndependentCutLP.C014.B 34 := by decide +kernel
def row_35 : Form 60 := (.plus (.plus (nv (n:=16) (e:=44) (T.ends 37).1) (nv (n:=16) (e:=44) (T.ends 37).2)) (.scale (-1) (ev (n:=16) (e:=44) 37)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_35 : ∀j,row_35.coeff j=IndependentCutLP.C014.A 35 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_35 : (1:ℤ)-row_35.constant=IndependentCutLP.C014.B 35 := by decide +kernel
def row_36 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 38).2) (.scale (-1) (ev (n:=16) (e:=44) 38)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_36 : ∀j,row_36.coeff j=IndependentCutLP.C014.A 36 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_36 : (0:ℤ)-row_36.constant=IndependentCutLP.C014.B 36 := by decide +kernel
def row_37 : Form 60 := (.plus (nv (n:=16) (e:=44) (T.ends 42).1) (.scale (-1) (ev (n:=16) (e:=44) 42)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_37 : ∀j,row_37.coeff j=IndependentCutLP.C014.A 37 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_37 : (0:ℤ)-row_37.constant=IndependentCutLP.C014.B 37 := by decide +kernel
def bits_38 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (127484 : ℕ).testBit a.val) (fun x => (127484 : ℕ).testBit (16+x.val))
def row_38 : Form 60 := (.scale (-1) (cutForm T bits_38))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_38 : ∀j,row_38.coeff j=IndependentCutLP.C014.A 38 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_38 : (-26:ℤ)-row_38.constant=IndependentCutLP.C014.B 38 := by decide +kernel
def bits_39 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (130620 : ℕ).testBit a.val) (fun x => (130620 : ℕ).testBit (16+x.val))
def row_39 : Form 60 := (.scale (-1) (cutForm T bits_39))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_39 : ∀j,row_39.coeff j=IndependentCutLP.C014.A 39 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_39 : (-26:ℤ)-row_39.constant=IndependentCutLP.C014.B 39 := by decide +kernel
def bits_40 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (331324 : ℕ).testBit a.val) (fun x => (331324 : ℕ).testBit (16+x.val))
def row_40 : Form 60 := (.scale (-1) (cutForm T bits_40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_40 : ∀j,row_40.coeff j=IndependentCutLP.C014.A 40 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_40 : (-26:ℤ)-row_40.constant=IndependentCutLP.C014.B 40 := by decide +kernel
def bits_41 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (258496 : ℕ).testBit a.val) (fun x => (258496 : ℕ).testBit (16+x.val))
def row_41 : Form 60 := (.scale (-1) (cutForm T bits_41))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_41 : ∀j,row_41.coeff j=IndependentCutLP.C014.A 41 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_41 : (-26:ℤ)-row_41.constant=IndependentCutLP.C014.B 41 := by decide +kernel
def bits_42 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (125208 : ℕ).testBit a.val) (fun x => (125208 : ℕ).testBit (16+x.val))
def row_42 : Form 60 := (.scale (-1) (cutForm T bits_42))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_42 : ∀j,row_42.coeff j=IndependentCutLP.C014.A 42 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_42 : (-26:ℤ)-row_42.constant=IndependentCutLP.C014.B 42 := by decide +kernel
def bits_43 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (127356 : ℕ).testBit a.val) (fun x => (127356 : ℕ).testBit (16+x.val))
def row_43 : Form 60 := (.scale (-1) (cutForm T bits_43))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_43 : ∀j,row_43.coeff j=IndependentCutLP.C014.A 43 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_43 : (-26:ℤ)-row_43.constant=IndependentCutLP.C014.B 43 := by decide +kernel
def bits_44 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (124988 : ℕ).testBit a.val) (fun x => (124988 : ℕ).testBit (16+x.val))
def row_44 : Form 60 := (.scale (-1) (cutForm T bits_44))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_44 : ∀j,row_44.coeff j=IndependentCutLP.C014.A 44 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_44 : (-26:ℤ)-row_44.constant=IndependentCutLP.C014.B 44 := by decide +kernel
def bits_45 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (129596 : ℕ).testBit a.val) (fun x => (129596 : ℕ).testBit (16+x.val))
def row_45 : Form 60 := (.scale (-1) (cutForm T bits_45))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_45 : ∀j,row_45.coeff j=IndependentCutLP.C014.A 45 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_45 : (-26:ℤ)-row_45.constant=IndependentCutLP.C014.B 45 := by decide +kernel
def bits_46 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (127472 : ℕ).testBit a.val) (fun x => (127472 : ℕ).testBit (16+x.val))
def row_46 : Form 60 := (.scale (-1) (cutForm T bits_46))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_46 : ∀j,row_46.coeff j=IndependentCutLP.C014.A 46 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_46 : (-26:ℤ)-row_46.constant=IndependentCutLP.C014.B 46 := by decide +kernel
def bits_47 : Fin 16 ⊕ Fin 3 → Bool := Sum.elim (fun a => (339516 : ℕ).testBit a.val) (fun x => (339516 : ℕ).testBit (16+x.val))
def row_47 : Form 60 := (.scale (-1) (cutForm T bits_47))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_47 : ∀j,row_47.coeff j=IndependentCutLP.C014.A 47 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_47 : (-26:ℤ)-row_47.constant=IndependentCutLP.C014.B 47 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_0 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 0 j*flat N E j) ≤ IndependentCutLP.C014.B 0 := by
  apply of_eval_le row_0 _ _ (22:ℤ) (flat N E) coeff_0 const_0
  have h := S.vertices
  simp only [row_0,eval_vertices]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_1 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 1 j*flat N E j) ≤ IndependentCutLP.C014.B 1 := by
  apply of_eval_le row_1 _ _ (121:ℤ) (flat N E) coeff_1 const_1
  have h := S.edgeHi
  simp only [row_1,eval_m]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_2 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 2 j*flat N E j) ≤ IndependentCutLP.C014.B 2 := by
  apply of_eval_le row_2 _ _ (-1:ℤ) (flat N E) coeff_2 const_2
  have h := S.exists_cycle 0
  simp only [row_2,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_3 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 3 j*flat N E j) ≤ IndependentCutLP.C014.B 3 := by
  apply of_eval_le row_3 _ _ (-1:ℤ) (flat N E) coeff_3 const_3
  have h := S.exists_cycle 1
  simp only [row_3,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_4 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 4 j*flat N E j) ≤ IndependentCutLP.C014.B 4 := by
  apply of_eval_le row_4 _ _ (-1:ℤ) (flat N E) coeff_4 const_4
  have h := S.exists_cycle 3
  simp only [row_4,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_5 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 5 j*flat N E j) ≤ IndependentCutLP.C014.B 5 := by
  apply of_eval_le row_5 _ _ (0:ℤ) (flat N E) coeff_5 const_5
  have h := S.degrees 0
  simp only [row_5,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_6 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 6 j*flat N E j) ≤ IndependentCutLP.C014.B 6 := by
  apply of_eval_le row_6 _ _ (0:ℤ) (flat N E) coeff_6 const_6
  have h := S.degrees 1
  simp only [row_6,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_7 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 7 j*flat N E j) ≤ IndependentCutLP.C014.B 7 := by
  apply of_eval_le row_7 _ _ (0:ℤ) (flat N E) coeff_7 const_7
  have h := S.degrees 2
  simp only [row_7,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_8 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 8 j*flat N E j) ≤ IndependentCutLP.C014.B 8 := by
  apply of_eval_le row_8 _ _ (0:ℤ) (flat N E) coeff_8 const_8
  have h := S.degrees 3
  simp only [row_8,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_9 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 9 j*flat N E j) ≤ IndependentCutLP.C014.B 9 := by
  apply of_eval_le row_9 _ _ (0:ℤ) (flat N E) coeff_9 const_9
  have h := S.degrees 4
  simp only [row_9,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_10 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 10 j*flat N E j) ≤ IndependentCutLP.C014.B 10 := by
  apply of_eval_le row_10 _ _ (0:ℤ) (flat N E) coeff_10 const_10
  have h := S.degrees 5
  simp only [row_10,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_11 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 11 j*flat N E j) ≤ IndependentCutLP.C014.B 11 := by
  apply of_eval_le row_11 _ _ (0:ℤ) (flat N E) coeff_11 const_11
  have h := S.degrees 6
  simp only [row_11,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_12 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 12 j*flat N E j) ≤ IndependentCutLP.C014.B 12 := by
  apply of_eval_le row_12 _ _ (0:ℤ) (flat N E) coeff_12 const_12
  have h := S.degrees 9
  simp only [row_12,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_13 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 13 j*flat N E j) ≤ IndependentCutLP.C014.B 13 := by
  apply of_eval_le row_13 _ _ (0:ℤ) (flat N E) coeff_13 const_13
  have h := S.degrees 12
  simp only [row_13,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_14 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 14 j*flat N E j) ≤ IndependentCutLP.C014.B 14 := by
  apply of_eval_le row_14 _ _ (0:ℤ) (flat N E) coeff_14 const_14
  have h := S.degrees 13
  simp only [row_14,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_15 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 15 j*flat N E j) ≤ IndependentCutLP.C014.B 15 := by
  apply of_eval_le row_15 _ _ (0:ℤ) (flat N E) coeff_15 const_15
  have h := S.degrees 14
  simp only [row_15,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_16 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 16 j*flat N E j) ≤ IndependentCutLP.C014.B 16 := by
  apply of_eval_le row_16 _ _ (0:ℤ) (flat N E) coeff_16 const_16
  have h := S.degrees 15
  simp only [row_16,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_17 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 17 j*flat N E j) ≤ IndependentCutLP.C014.B 17 := by
  apply of_eval_le row_17 _ _ (-130:ℤ) (flat N E) coeff_17 const_17
  have h := S.repairs 0 colors_17 proper_17
  simp only [row_17,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_18 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 18 j*flat N E j) ≤ IndependentCutLP.C014.B 18 := by
  apply of_eval_le row_18 _ _ (-130:ℤ) (flat N E) coeff_18 const_18
  have h := S.repairs 0 colors_18 proper_18
  simp only [row_18,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_19 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 19 j*flat N E j) ≤ IndependentCutLP.C014.B 19 := by
  apply of_eval_le row_19 _ _ (-130:ℤ) (flat N E) coeff_19 const_19
  have h := S.repairs 0 colors_19 proper_19
  simp only [row_19,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_20 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 20 j*flat N E j) ≤ IndependentCutLP.C014.B 20 := by
  apply of_eval_le row_20 _ _ (-130:ℤ) (flat N E) coeff_20 const_20
  have h := S.repairs 1 colors_20 proper_20
  simp only [row_20,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_21 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 21 j*flat N E j) ≤ IndependentCutLP.C014.B 21 := by
  apply of_eval_le row_21 _ _ (-130:ℤ) (flat N E) coeff_21 const_21
  have h := S.repairs 2 colors_21 proper_21
  simp only [row_21,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_22 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 22 j*flat N E j) ≤ IndependentCutLP.C014.B 22 := by
  apply of_eval_le row_22 _ _ (-130:ℤ) (flat N E) coeff_22 const_22
  have h := S.repairs 2 colors_22 proper_22
  simp only [row_22,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_23 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 23 j*flat N E j) ≤ IndependentCutLP.C014.B 23 := by
  apply of_eval_le row_23 _ _ (0:ℤ) (flat N E) coeff_23 const_23
  have h := S.cycle_left 8 2 (by decide +kernel)
  simp only [row_23,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_24 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 24 j*flat N E j) ≤ IndependentCutLP.C014.B 24 := by
  apply of_eval_le row_24 _ _ (1:ℤ) (flat N E) coeff_24 const_24
  have h := S.cycle_both 9 2 1 (by decide +kernel) (by decide +kernel)
  simp only [row_24,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_25 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 25 j*flat N E j) ≤ IndependentCutLP.C014.B 25 := by
  apply of_eval_le row_25 _ _ (0:ℤ) (flat N E) coeff_25 const_25
  have h := S.cycle_right 13 1 (by decide +kernel)
  simp only [row_25,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_26 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 26 j*flat N E j) ≤ IndependentCutLP.C014.B 26 := by
  apply of_eval_le row_26 _ _ (1:ℤ) (flat N E) coeff_26 const_26
  have h := S.cycle_both 18 3 2 (by decide +kernel) (by decide +kernel)
  simp only [row_26,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_27 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 27 j*flat N E j) ≤ IndependentCutLP.C014.B 27 := by
  apply of_eval_le row_27 _ _ (0:ℤ) (flat N E) coeff_27 const_27
  have h := S.cycle_left 19 3 (by decide +kernel)
  simp only [row_27,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_28 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 28 j*flat N E j) ≤ IndependentCutLP.C014.B 28 := by
  apply of_eval_le row_28 _ _ (0:ℤ) (flat N E) coeff_28 const_28
  have h := S.cycle_left 20 3 (by decide +kernel)
  simp only [row_28,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_29 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 29 j*flat N E j) ≤ IndependentCutLP.C014.B 29 := by
  apply of_eval_le row_29 _ _ (0:ℤ) (flat N E) coeff_29 const_29
  have h := S.cycle_right 21 2 (by decide +kernel)
  simp only [row_29,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_30 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 30 j*flat N E j) ≤ IndependentCutLP.C014.B 30 := by
  apply of_eval_le row_30 _ _ (0:ℤ) (flat N E) coeff_30 const_30
  have h := S.cycle_right 23 2 (by decide +kernel)
  simp only [row_30,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_31 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 31 j*flat N E j) ≤ IndependentCutLP.C014.B 31 := by
  apply of_eval_le row_31 _ _ (0:ℤ) (flat N E) coeff_31 const_31
  have h := S.cycle_right 27 0 (by decide +kernel)
  simp only [row_31,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_32 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 32 j*flat N E j) ≤ IndependentCutLP.C014.B 32 := by
  apply of_eval_le row_32 _ _ (0:ℤ) (flat N E) coeff_32 const_32
  have h := S.cycle_right 28 3 (by decide +kernel)
  simp only [row_32,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_33 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 33 j*flat N E j) ≤ IndependentCutLP.C014.B 33 := by
  apply of_eval_le row_33 _ _ (0:ℤ) (flat N E) coeff_33 const_33
  have h := S.cycle_left 35 4 (by decide +kernel)
  simp only [row_33,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_34 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 34 j*flat N E j) ≤ IndependentCutLP.C014.B 34 := by
  apply of_eval_le row_34 _ _ (1:ℤ) (flat N E) coeff_34 const_34
  have h := S.cycle_both 36 4 0 (by decide +kernel) (by decide +kernel)
  simp only [row_34,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_35 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 35 j*flat N E j) ≤ IndependentCutLP.C014.B 35 := by
  apply of_eval_le row_35 _ _ (1:ℤ) (flat N E) coeff_35 const_35
  have h := S.cycle_both 37 4 3 (by decide +kernel) (by decide +kernel)
  simp only [row_35,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_36 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 36 j*flat N E j) ≤ IndependentCutLP.C014.B 36 := by
  apply of_eval_le row_36 _ _ (0:ℤ) (flat N E) coeff_36 const_36
  have h := S.cycle_left 38 4 (by decide +kernel)
  simp only [row_36,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_37 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 37 j*flat N E j) ≤ IndependentCutLP.C014.B 37 := by
  apply of_eval_le row_37 _ _ (0:ℤ) (flat N E) coeff_37 const_37
  have h := S.cycle_right 42 3 (by decide +kernel)
  simp only [row_37,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_38 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 38 j*flat N E j) ≤ IndependentCutLP.C014.B 38 := by
  apply of_eval_le row_38 _ _ (-26:ℤ) (flat N E) coeff_38 const_38
  have h := S.cuts bits_38
  simp only [row_38,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_39 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 39 j*flat N E j) ≤ IndependentCutLP.C014.B 39 := by
  apply of_eval_le row_39 _ _ (-26:ℤ) (flat N E) coeff_39 const_39
  have h := S.cuts bits_39
  simp only [row_39,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_40 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 40 j*flat N E j) ≤ IndependentCutLP.C014.B 40 := by
  apply of_eval_le row_40 _ _ (-26:ℤ) (flat N E) coeff_40 const_40
  have h := S.cuts bits_40
  simp only [row_40,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_41 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 41 j*flat N E j) ≤ IndependentCutLP.C014.B 41 := by
  apply of_eval_le row_41 _ _ (-26:ℤ) (flat N E) coeff_41 const_41
  have h := S.cuts bits_41
  simp only [row_41,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_42 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 42 j*flat N E j) ≤ IndependentCutLP.C014.B 42 := by
  apply of_eval_le row_42 _ _ (-26:ℤ) (flat N E) coeff_42 const_42
  have h := S.cuts bits_42
  simp only [row_42,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_43 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 43 j*flat N E j) ≤ IndependentCutLP.C014.B 43 := by
  apply of_eval_le row_43 _ _ (-26:ℤ) (flat N E) coeff_43 const_43
  have h := S.cuts bits_43
  simp only [row_43,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_44 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 44 j*flat N E j) ≤ IndependentCutLP.C014.B 44 := by
  apply of_eval_le row_44 _ _ (-26:ℤ) (flat N E) coeff_44 const_44
  have h := S.cuts bits_44
  simp only [row_44,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_45 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 45 j*flat N E j) ≤ IndependentCutLP.C014.B 45 := by
  apply of_eval_le row_45 _ _ (-26:ℤ) (flat N E) coeff_45 const_45
  have h := S.cuts bits_45
  simp only [row_45,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_46 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 46 j*flat N E j) ≤ IndependentCutLP.C014.B 46 := by
  apply of_eval_le row_46 _ _ (-26:ℤ) (flat N E) coeff_46 const_46
  have h := S.cuts bits_46
  simp only [row_46,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_47 (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C014.A 47 j*flat N E j) ≤ IndependentCutLP.C014.B 47 := by
  apply of_eval_le row_47 _ _ (-26:ℤ) (flat N E) coeff_47 const_47
  have h := S.cuts bits_47
  simp only [row_47,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (N : Fin 16 → ℤ) (E : Fin 44 → ℤ) (S : Feasible T N E 12 121) : False := by
  apply IndependentCutLP.C014.impossible (flat N E)
  · intro j
    refine Fin.addCases (m:=16) (n:=44) (fun a => ?_) (fun k => ?_) j
    · simpa [flat] using S.npos a
    · simpa [flat] using S.epos k
  · intro i
    fin_cases i
    · exact valid_0 N E S
    · exact valid_1 N E S
    · exact valid_2 N E S
    · exact valid_3 N E S
    · exact valid_4 N E S
    · exact valid_5 N E S
    · exact valid_6 N E S
    · exact valid_7 N E S
    · exact valid_8 N E S
    · exact valid_9 N E S
    · exact valid_10 N E S
    · exact valid_11 N E S
    · exact valid_12 N E S
    · exact valid_13 N E S
    · exact valid_14 N E S
    · exact valid_15 N E S
    · exact valid_16 N E S
    · exact valid_17 N E S
    · exact valid_18 N E S
    · exact valid_19 N E S
    · exact valid_20 N E S
    · exact valid_21 N E S
    · exact valid_22 N E S
    · exact valid_23 N E S
    · exact valid_24 N E S
    · exact valid_25 N E S
    · exact valid_26 N E S
    · exact valid_27 N E S
    · exact valid_28 N E S
    · exact valid_29 N E S
    · exact valid_30 N E S
    · exact valid_31 N E S
    · exact valid_32 N E S
    · exact valid_33 N E S
    · exact valid_34 N E S
    · exact valid_35 N E S
    · exact valid_36 N E S
    · exact valid_37 N E S
    · exact valid_38 N E S
    · exact valid_39 N E S
    · exact valid_40 N E S
    · exact valid_41 N E S
    · exact valid_42 N E S
    · exact valid_43 N E S
    · exact valid_44 N E S
    · exact valid_45 N E S
    · exact valid_46 N E S
    · exact valid_47 N E S
end FastCutCase.C014

-- CaseFast022low

namespace FastCutCase.C022low
open Finset ThreeExceptions FiniteCutTemplate GraphMass CutSummary CertifiedAffine AffineCut
abbrev T := NativeCutTemplate.C022.table
def row_0 : Form 57 := (verticesForm (n:=17) (e:=40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_0 : ∀j,row_0.coeff j=IndependentCutLP.C022low.A 0 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_0 : (22:ℤ)-row_0.constant=IndependentCutLP.C022low.B 0 := by decide +kernel
def row_1 : Form 57 := (mForm T)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_1 : ∀j,row_1.coeff j=IndependentCutLP.C022low.A 1 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_1 : (117:ℤ)-row_1.constant=IndependentCutLP.C022low.B 1 := by decide +kernel
def row_2 : Form 57 := (.scale (-1) (nv (n:=17) (e:=40) (T.cycle 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_2 : ∀j,row_2.coeff j=IndependentCutLP.C022low.A 2 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_2 : (-1:ℤ)-row_2.constant=IndependentCutLP.C022low.B 2 := by decide +kernel
def row_3 : Form 57 := (.plus (degreeForm T 0) (.scale (-12) (nv (n:=17) (e:=40) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_3 : ∀j,row_3.coeff j=IndependentCutLP.C022low.A 3 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_3 : (0:ℤ)-row_3.constant=IndependentCutLP.C022low.B 3 := by decide +kernel
def row_4 : Form 57 := (.plus (degreeForm T 1) (.scale (-12) (nv (n:=17) (e:=40) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_4 : ∀j,row_4.coeff j=IndependentCutLP.C022low.A 4 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_4 : (0:ℤ)-row_4.constant=IndependentCutLP.C022low.B 4 := by decide +kernel
def row_5 : Form 57 := (.plus (degreeForm T 2) (.scale (-12) (nv (n:=17) (e:=40) 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_5 : ∀j,row_5.coeff j=IndependentCutLP.C022low.A 5 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_5 : (0:ℤ)-row_5.constant=IndependentCutLP.C022low.B 5 := by decide +kernel
def row_6 : Form 57 := (.plus (degreeForm T 3) (.scale (-12) (nv (n:=17) (e:=40) 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_6 : ∀j,row_6.coeff j=IndependentCutLP.C022low.A 6 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_6 : (0:ℤ)-row_6.constant=IndependentCutLP.C022low.B 6 := by decide +kernel
def row_7 : Form 57 := (.plus (degreeForm T 5) (.scale (-12) (nv (n:=17) (e:=40) 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_7 : ∀j,row_7.coeff j=IndependentCutLP.C022low.A 7 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_7 : (0:ℤ)-row_7.constant=IndependentCutLP.C022low.B 7 := by decide +kernel
def row_8 : Form 57 := (.plus (degreeForm T 6) (.scale (-12) (nv (n:=17) (e:=40) 6)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_8 : ∀j,row_8.coeff j=IndependentCutLP.C022low.A 8 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_8 : (0:ℤ)-row_8.constant=IndependentCutLP.C022low.B 8 := by decide +kernel
def row_9 : Form 57 := (.plus (degreeForm T 8) (.scale (-12) (nv (n:=17) (e:=40) 8)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_9 : ∀j,row_9.coeff j=IndependentCutLP.C022low.A 9 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_9 : (0:ℤ)-row_9.constant=IndependentCutLP.C022low.B 9 := by decide +kernel
def row_10 : Form 57 := (.plus (degreeForm T 9) (.scale (-12) (nv (n:=17) (e:=40) 9)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_10 : ∀j,row_10.coeff j=IndependentCutLP.C022low.A 10 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_10 : (0:ℤ)-row_10.constant=IndependentCutLP.C022low.B 10 := by decide +kernel
def row_11 : Form 57 := (.plus (degreeForm T 10) (.scale (-12) (nv (n:=17) (e:=40) 10)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_11 : ∀j,row_11.coeff j=IndependentCutLP.C022low.A 11 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_11 : (0:ℤ)-row_11.constant=IndependentCutLP.C022low.B 11 := by decide +kernel
def row_12 : Form 57 := (.plus (degreeForm T 11) (.scale (-12) (nv (n:=17) (e:=40) 11)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_12 : ∀j,row_12.coeff j=IndependentCutLP.C022low.A 12 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_12 : (0:ℤ)-row_12.constant=IndependentCutLP.C022low.B 12 := by decide +kernel
def row_13 : Form 57 := (.plus (degreeForm T 12) (.scale (-12) (nv (n:=17) (e:=40) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_13 : ∀j,row_13.coeff j=IndependentCutLP.C022low.A 13 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_13 : (0:ℤ)-row_13.constant=IndependentCutLP.C022low.B 13 := by decide +kernel
def row_14 : Form 57 := (.plus (degreeForm T 13) (.scale (-12) (nv (n:=17) (e:=40) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_14 : ∀j,row_14.coeff j=IndependentCutLP.C022low.A 14 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_14 : (0:ℤ)-row_14.constant=IndependentCutLP.C022low.B 14 := by decide +kernel
def row_15 : Form 57 := (.plus (degreeForm T 14) (.scale (-12) (nv (n:=17) (e:=40) 14)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_15 : ∀j,row_15.coeff j=IndependentCutLP.C022low.A 15 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_15 : (0:ℤ)-row_15.constant=IndependentCutLP.C022low.B 15 := by decide +kernel
def row_16 : Form 57 := (.plus (degreeForm T 15) (.scale (-12) (nv (n:=17) (e:=40) 15)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_16 : ∀j,row_16.coeff j=IndependentCutLP.C022low.A 16 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_16 : (0:ℤ)-row_16.constant=IndependentCutLP.C022low.B 16 := by decide +kernel
def row_17 : Form 57 := (.scale (-1) (.plus (.plus (mForm T) (exceptionForm T 0)) (exceptionForm T 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_17 : ∀j,row_17.coeff j=IndependentCutLP.C022low.A 17 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_17 : (-134:ℤ)-row_17.constant=IndependentCutLP.C022low.B 17 := by decide +kernel
def colors_18 : Fin 17 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 0 else if x=1 then 1 else 1)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_18 : properAway T 0 colors_18 := by unfold properAway; decide +kernel
def row_18 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 0 colors_18))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_18 : ∀j,row_18.coeff j=IndependentCutLP.C022low.A 18 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_18 : (-130:ℤ)-row_18.constant=IndependentCutLP.C022low.B 18 := by decide +kernel
def colors_19 : Fin 17 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 4 else if x=1 then 0 else 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_19 : properAway T 1 colors_19 := by unfold properAway; decide +kernel
def row_19 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 1 colors_19))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_19 : ∀j,row_19.coeff j=IndependentCutLP.C022low.A 19 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_19 : (-130:ℤ)-row_19.constant=IndependentCutLP.C022low.B 19 := by decide +kernel
def colors_20 : Fin 17 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 1 else if x=1 then 3 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_20 : properAway T 2 colors_20 := by unfold properAway; decide +kernel
def row_20 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_20))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_20 : ∀j,row_20.coeff j=IndependentCutLP.C022low.A 20 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_20 : (-130:ℤ)-row_20.constant=IndependentCutLP.C022low.B 20 := by decide +kernel
def colors_21 : Fin 17 ⊕ Fin 3 → Fin 5 := Sum.elim (fun a => (T.slot a).1) (fun x => if x=0 then 4 else if x=1 then 3 else 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem proper_21 : properAway T 2 colors_21 := by unfold properAway; decide +kernel
def row_21 : Form 57 := (.scale (-1) (.plus (mForm T) (.scale (2) (errorForm T 2 colors_21))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_21 : ∀j,row_21.coeff j=IndependentCutLP.C022low.A 21 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_21 : (-130:ℤ)-row_21.constant=IndependentCutLP.C022low.B 21 := by decide +kernel
def row_22 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 4).2) (.scale (-1) (ev (n:=17) (e:=40) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_22 : ∀j,row_22.coeff j=IndependentCutLP.C022low.A 22 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_22 : (0:ℤ)-row_22.constant=IndependentCutLP.C022low.B 22 := by decide +kernel
def row_23 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 10).2) (.scale (-1) (ev (n:=17) (e:=40) 10)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_23 : ∀j,row_23.coeff j=IndependentCutLP.C022low.A 23 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_23 : (0:ℤ)-row_23.constant=IndependentCutLP.C022low.B 23 := by decide +kernel
def row_24 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 12).2) (.scale (-1) (ev (n:=17) (e:=40) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_24 : ∀j,row_24.coeff j=IndependentCutLP.C022low.A 24 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_24 : (0:ℤ)-row_24.constant=IndependentCutLP.C022low.B 24 := by decide +kernel
def row_25 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 13).2) (.scale (-1) (ev (n:=17) (e:=40) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_25 : ∀j,row_25.coeff j=IndependentCutLP.C022low.A 25 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_25 : (0:ℤ)-row_25.constant=IndependentCutLP.C022low.B 25 := by decide +kernel
def row_26 : Form 57 := (.plus (.plus (nv (n:=17) (e:=40) (T.ends 14).1) (nv (n:=17) (e:=40) (T.ends 14).2)) (.scale (-1) (ev (n:=17) (e:=40) 14)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_26 : ∀j,row_26.coeff j=IndependentCutLP.C022low.A 26 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_26 : (1:ℤ)-row_26.constant=IndependentCutLP.C022low.B 26 := by decide +kernel
def row_27 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 19).2) (.scale (-1) (ev (n:=17) (e:=40) 19)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_27 : ∀j,row_27.coeff j=IndependentCutLP.C022low.A 27 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_27 : (0:ℤ)-row_27.constant=IndependentCutLP.C022low.B 27 := by decide +kernel
def row_28 : Form 57 := (.plus (.plus (nv (n:=17) (e:=40) (T.ends 20).1) (nv (n:=17) (e:=40) (T.ends 20).2)) (.scale (-1) (ev (n:=17) (e:=40) 20)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_28 : ∀j,row_28.coeff j=IndependentCutLP.C022low.A 28 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_28 : (1:ℤ)-row_28.constant=IndependentCutLP.C022low.B 28 := by decide +kernel
def row_29 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 21).2) (.scale (-1) (ev (n:=17) (e:=40) 21)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_29 : ∀j,row_29.coeff j=IndependentCutLP.C022low.A 29 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_29 : (0:ℤ)-row_29.constant=IndependentCutLP.C022low.B 29 := by decide +kernel
def row_30 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 22).2) (.scale (-1) (ev (n:=17) (e:=40) 22)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_30 : ∀j,row_30.coeff j=IndependentCutLP.C022low.A 30 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_30 : (0:ℤ)-row_30.constant=IndependentCutLP.C022low.B 30 := by decide +kernel
def row_31 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 27).1) (.scale (-1) (ev (n:=17) (e:=40) 27)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_31 : ∀j,row_31.coeff j=IndependentCutLP.C022low.A 31 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_31 : (0:ℤ)-row_31.constant=IndependentCutLP.C022low.B 31 := by decide +kernel
def row_32 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 32).1) (.scale (-1) (ev (n:=17) (e:=40) 32)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_32 : ∀j,row_32.coeff j=IndependentCutLP.C022low.A 32 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_32 : (0:ℤ)-row_32.constant=IndependentCutLP.C022low.B 32 := by decide +kernel
def row_33 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 38).1) (.scale (-1) (ev (n:=17) (e:=40) 38)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_33 : ∀j,row_33.coeff j=IndependentCutLP.C022low.A 33 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_33 : (0:ℤ)-row_33.constant=IndependentCutLP.C022low.B 33 := by decide +kernel
def bits_34 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255968 : ℕ).testBit a.val) (fun x => (255968 : ℕ).testBit (17+x.val))
def row_34 : Form 57 := (.scale (-1) (cutForm T bits_34))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_34 : ∀j,row_34.coeff j=IndependentCutLP.C022low.A 34 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_34 : (-26:ℤ)-row_34.constant=IndependentCutLP.C022low.B 34 := by decide +kernel
def bits_35 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (977184 : ℕ).testBit a.val) (fun x => (977184 : ℕ).testBit (17+x.val))
def row_35 : Form 57 := (.scale (-1) (cutForm T bits_35))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_35 : ∀j,row_35.coeff j=IndependentCutLP.C022low.A 35 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_35 : (-26:ℤ)-row_35.constant=IndependentCutLP.C022low.B 35 := by decide +kernel
def bits_36 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (948256 : ℕ).testBit a.val) (fun x => (948256 : ℕ).testBit (17+x.val))
def row_36 : Form 57 := (.scale (-1) (cutForm T bits_36))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_36 : ∀j,row_36.coeff j=IndependentCutLP.C022low.A 36 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_36 : (-26:ℤ)-row_36.constant=IndependentCutLP.C022low.B 36 := by decide +kernel
def bits_37 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255964 : ℕ).testBit a.val) (fun x => (255964 : ℕ).testBit (17+x.val))
def row_37 : Form 57 := (.scale (-1) (cutForm T bits_37))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_37 : ∀j,row_37.coeff j=IndependentCutLP.C022low.A 37 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_37 : (-26:ℤ)-row_37.constant=IndependentCutLP.C022low.B 37 := by decide +kernel
def bits_38 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (964640 : ℕ).testBit a.val) (fun x => (964640 : ℕ).testBit (17+x.val))
def row_38 : Form 57 := (.scale (-1) (cutForm T bits_38))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_38 : ∀j,row_38.coeff j=IndependentCutLP.C022low.A 38 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_38 : (-26:ℤ)-row_38.constant=IndependentCutLP.C022low.B 38 := by decide +kernel
def bits_39 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (792622 : ℕ).testBit a.val) (fun x => (792622 : ℕ).testBit (17+x.val))
def row_39 : Form 57 := (.scale (-1) (cutForm T bits_39))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_39 : ∀j,row_39.coeff j=IndependentCutLP.C022low.A 39 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_39 : (-26:ℤ)-row_39.constant=IndependentCutLP.C022low.B 39 := by decide +kernel
def bits_40 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (71582 : ℕ).testBit a.val) (fun x => (71582 : ℕ).testBit (17+x.val))
def row_40 : Form 57 := (.scale (-1) (cutForm T bits_40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_40 : ∀j,row_40.coeff j=IndependentCutLP.C022low.A 40 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_40 : (-26:ℤ)-row_40.constant=IndependentCutLP.C022low.B 40 := by decide +kernel
def bits_41 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255072 : ℕ).testBit a.val) (fun x => (255072 : ℕ).testBit (17+x.val))
def row_41 : Form 57 := (.scale (-1) (cutForm T bits_41))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_41 : ∀j,row_41.coeff j=IndependentCutLP.C022low.A 41 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_41 : (-26:ℤ)-row_41.constant=IndependentCutLP.C022low.B 41 := by decide +kernel
def bits_42 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (913568 : ℕ).testBit a.val) (fun x => (913568 : ℕ).testBit (17+x.val))
def row_42 : Form 57 := (.scale (-1) (cutForm T bits_42))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_42 : ∀j,row_42.coeff j=IndependentCutLP.C022low.A 42 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_42 : (-26:ℤ)-row_42.constant=IndependentCutLP.C022low.B 42 := by decide +kernel
def bits_43 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255776 : ℕ).testBit a.val) (fun x => (255776 : ℕ).testBit (17+x.val))
def row_43 : Form 57 := (.scale (-1) (cutForm T bits_43))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_43 : ∀j,row_43.coeff j=IndependentCutLP.C022low.A 43 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_43 : (-26:ℤ)-row_43.constant=IndependentCutLP.C022low.B 43 := by decide +kernel
def bits_44 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (1042464 : ℕ).testBit a.val) (fun x => (1042464 : ℕ).testBit (17+x.val))
def row_44 : Form 57 := (.scale (-1) (cutForm T bits_44))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_44 : ∀j,row_44.coeff j=IndependentCutLP.C022low.A 44 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_44 : (-26:ℤ)-row_44.constant=IndependentCutLP.C022low.B 44 := by decide +kernel
def bits_45 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255952 : ℕ).testBit a.val) (fun x => (255952 : ℕ).testBit (17+x.val))
def row_45 : Form 57 := (.scale (-1) (cutForm T bits_45))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_45 : ∀j,row_45.coeff j=IndependentCutLP.C022low.A 45 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_45 : (-26:ℤ)-row_45.constant=IndependentCutLP.C022low.B 45 := by decide +kernel
def bits_46 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (910048 : ℕ).testBit a.val) (fun x => (910048 : ℕ).testBit (17+x.val))
def row_46 : Form 57 := (.scale (-1) (cutForm T bits_46))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_46 : ∀j,row_46.coeff j=IndependentCutLP.C022low.A 46 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_46 : (-26:ℤ)-row_46.constant=IndependentCutLP.C022low.B 46 := by decide +kernel
def bits_47 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (235576 : ℕ).testBit a.val) (fun x => (235576 : ℕ).testBit (17+x.val))
def row_47 : Form 57 := (.scale (-1) (cutForm T bits_47))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_47 : ∀j,row_47.coeff j=IndependentCutLP.C022low.A 47 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_47 : (-26:ℤ)-row_47.constant=IndependentCutLP.C022low.B 47 := by decide +kernel
def bits_48 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (849952 : ℕ).testBit a.val) (fun x => (849952 : ℕ).testBit (17+x.val))
def row_48 : Form 57 := (.scale (-1) (cutForm T bits_48))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_48 : ∀j,row_48.coeff j=IndependentCutLP.C022low.A 48 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_48 : (-26:ℤ)-row_48.constant=IndependentCutLP.C022low.B 48 := by decide +kernel
def bits_49 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (219188 : ℕ).testBit a.val) (fun x => (219188 : ℕ).testBit (17+x.val))
def row_49 : Form 57 := (.scale (-1) (cutForm T bits_49))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_49 : ∀j,row_49.coeff j=IndependentCutLP.C022low.A 49 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_49 : (-26:ℤ)-row_49.constant=IndependentCutLP.C022low.B 49 := by decide +kernel
def bits_50 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (909536 : ℕ).testBit a.val) (fun x => (909536 : ℕ).testBit (17+x.val))
def row_50 : Form 57 := (.scale (-1) (cutForm T bits_50))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_50 : ∀j,row_50.coeff j=IndependentCutLP.C022low.A 50 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_50 : (-26:ℤ)-row_50.constant=IndependentCutLP.C022low.B 50 := by decide +kernel
def bits_51 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255840 : ℕ).testBit a.val) (fun x => (255840 : ℕ).testBit (17+x.val))
def row_51 : Form 57 := (.scale (-1) (cutForm T bits_51))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_51 : ∀j,row_51.coeff j=IndependentCutLP.C022low.A 51 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_51 : (-26:ℤ)-row_51.constant=IndependentCutLP.C022low.B 51 := by decide +kernel
def bits_52 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (247772 : ℕ).testBit a.val) (fun x => (247772 : ℕ).testBit (17+x.val))
def row_52 : Form 57 := (.scale (-1) (cutForm T bits_52))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_52 : ∀j,row_52.coeff j=IndependentCutLP.C022low.A 52 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_52 : (-26:ℤ)-row_52.constant=IndependentCutLP.C022low.B 52 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_0 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 0 j*flat N E j) ≤ IndependentCutLP.C022low.B 0 := by
  apply of_eval_le row_0 _ _ (22:ℤ) (flat N E) coeff_0 const_0
  have h := S.vertices
  simp only [row_0,eval_vertices]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_1 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 1 j*flat N E j) ≤ IndependentCutLP.C022low.B 1 := by
  apply of_eval_le row_1 _ _ (117:ℤ) (flat N E) coeff_1 const_1
  have h := S.edgeHi
  simp only [row_1,eval_m]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_2 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 2 j*flat N E j) ≤ IndependentCutLP.C022low.B 2 := by
  apply of_eval_le row_2 _ _ (-1:ℤ) (flat N E) coeff_2 const_2
  have h := S.exists_cycle 2
  simp only [row_2,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_3 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 3 j*flat N E j) ≤ IndependentCutLP.C022low.B 3 := by
  apply of_eval_le row_3 _ _ (0:ℤ) (flat N E) coeff_3 const_3
  have h := S.degrees 0
  simp only [row_3,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_4 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 4 j*flat N E j) ≤ IndependentCutLP.C022low.B 4 := by
  apply of_eval_le row_4 _ _ (0:ℤ) (flat N E) coeff_4 const_4
  have h := S.degrees 1
  simp only [row_4,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_5 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 5 j*flat N E j) ≤ IndependentCutLP.C022low.B 5 := by
  apply of_eval_le row_5 _ _ (0:ℤ) (flat N E) coeff_5 const_5
  have h := S.degrees 2
  simp only [row_5,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_6 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 6 j*flat N E j) ≤ IndependentCutLP.C022low.B 6 := by
  apply of_eval_le row_6 _ _ (0:ℤ) (flat N E) coeff_6 const_6
  have h := S.degrees 3
  simp only [row_6,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_7 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 7 j*flat N E j) ≤ IndependentCutLP.C022low.B 7 := by
  apply of_eval_le row_7 _ _ (0:ℤ) (flat N E) coeff_7 const_7
  have h := S.degrees 5
  simp only [row_7,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_8 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 8 j*flat N E j) ≤ IndependentCutLP.C022low.B 8 := by
  apply of_eval_le row_8 _ _ (0:ℤ) (flat N E) coeff_8 const_8
  have h := S.degrees 6
  simp only [row_8,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_9 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 9 j*flat N E j) ≤ IndependentCutLP.C022low.B 9 := by
  apply of_eval_le row_9 _ _ (0:ℤ) (flat N E) coeff_9 const_9
  have h := S.degrees 8
  simp only [row_9,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_10 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 10 j*flat N E j) ≤ IndependentCutLP.C022low.B 10 := by
  apply of_eval_le row_10 _ _ (0:ℤ) (flat N E) coeff_10 const_10
  have h := S.degrees 9
  simp only [row_10,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_11 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 11 j*flat N E j) ≤ IndependentCutLP.C022low.B 11 := by
  apply of_eval_le row_11 _ _ (0:ℤ) (flat N E) coeff_11 const_11
  have h := S.degrees 10
  simp only [row_11,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_12 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 12 j*flat N E j) ≤ IndependentCutLP.C022low.B 12 := by
  apply of_eval_le row_12 _ _ (0:ℤ) (flat N E) coeff_12 const_12
  have h := S.degrees 11
  simp only [row_12,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_13 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 13 j*flat N E j) ≤ IndependentCutLP.C022low.B 13 := by
  apply of_eval_le row_13 _ _ (0:ℤ) (flat N E) coeff_13 const_13
  have h := S.degrees 12
  simp only [row_13,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_14 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 14 j*flat N E j) ≤ IndependentCutLP.C022low.B 14 := by
  apply of_eval_le row_14 _ _ (0:ℤ) (flat N E) coeff_14 const_14
  have h := S.degrees 13
  simp only [row_14,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_15 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 15 j*flat N E j) ≤ IndependentCutLP.C022low.B 15 := by
  apply of_eval_le row_15 _ _ (0:ℤ) (flat N E) coeff_15 const_15
  have h := S.degrees 14
  simp only [row_15,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_16 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 16 j*flat N E j) ≤ IndependentCutLP.C022low.B 16 := by
  apply of_eval_le row_16 _ _ (0:ℤ) (flat N E) coeff_16 const_16
  have h := S.degrees 15
  simp only [row_16,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_17 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 17 j*flat N E j) ≤ IndependentCutLP.C022low.B 17 := by
  apply of_eval_le row_17 _ _ (-134:ℤ) (flat N E) coeff_17 const_17
  have h := S.obstruction
  simp only [row_17,eval_plus,eval_scale,eval_m,eval_exception]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_18 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 18 j*flat N E j) ≤ IndependentCutLP.C022low.B 18 := by
  apply of_eval_le row_18 _ _ (-130:ℤ) (flat N E) coeff_18 const_18
  have h := S.repairs 0 colors_18 proper_18
  simp only [row_18,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_19 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 19 j*flat N E j) ≤ IndependentCutLP.C022low.B 19 := by
  apply of_eval_le row_19 _ _ (-130:ℤ) (flat N E) coeff_19 const_19
  have h := S.repairs 1 colors_19 proper_19
  simp only [row_19,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_20 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 20 j*flat N E j) ≤ IndependentCutLP.C022low.B 20 := by
  apply of_eval_le row_20 _ _ (-130:ℤ) (flat N E) coeff_20 const_20
  have h := S.repairs 2 colors_20 proper_20
  simp only [row_20,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_21 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 21 j*flat N E j) ≤ IndependentCutLP.C022low.B 21 := by
  apply of_eval_le row_21 _ _ (-130:ℤ) (flat N E) coeff_21 const_21
  have h := S.repairs 2 colors_21 proper_21
  simp only [row_21,eval_plus,eval_scale,eval_m,eval_error]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_22 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 22 j*flat N E j) ≤ IndependentCutLP.C022low.B 22 := by
  apply of_eval_le row_22 _ _ (0:ℤ) (flat N E) coeff_22 const_22
  have h := S.cycle_left 4 1 (by decide +kernel)
  simp only [row_22,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_23 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 23 j*flat N E j) ≤ IndependentCutLP.C022low.B 23 := by
  apply of_eval_le row_23 _ _ (0:ℤ) (flat N E) coeff_23 const_23
  have h := S.cycle_left 10 3 (by decide +kernel)
  simp only [row_23,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_24 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 24 j*flat N E j) ≤ IndependentCutLP.C022low.B 24 := by
  apply of_eval_le row_24 _ _ (0:ℤ) (flat N E) coeff_24 const_24
  have h := S.cycle_left 12 3 (by decide +kernel)
  simp only [row_24,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_25 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 25 j*flat N E j) ≤ IndependentCutLP.C022low.B 25 := by
  apply of_eval_le row_25 _ _ (0:ℤ) (flat N E) coeff_25 const_25
  have h := S.cycle_left 13 3 (by decide +kernel)
  simp only [row_25,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_26 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 26 j*flat N E j) ≤ IndependentCutLP.C022low.B 26 := by
  apply of_eval_le row_26 _ _ (1:ℤ) (flat N E) coeff_26 const_26
  have h := S.cycle_both 14 3 2 (by decide +kernel) (by decide +kernel)
  simp only [row_26,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_27 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 27 j*flat N E j) ≤ IndependentCutLP.C022low.B 27 := by
  apply of_eval_le row_27 _ _ (0:ℤ) (flat N E) coeff_27 const_27
  have h := S.cycle_left 19 4 (by decide +kernel)
  simp only [row_27,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_28 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 28 j*flat N E j) ≤ IndependentCutLP.C022low.B 28 := by
  apply of_eval_le row_28 _ _ (1:ℤ) (flat N E) coeff_28 const_28
  have h := S.cycle_both 20 4 0 (by decide +kernel) (by decide +kernel)
  simp only [row_28,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_29 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 29 j*flat N E j) ≤ IndependentCutLP.C022low.B 29 := by
  apply of_eval_le row_29 _ _ (0:ℤ) (flat N E) coeff_29 const_29
  have h := S.cycle_left 21 4 (by decide +kernel)
  simp only [row_29,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_30 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 30 j*flat N E j) ≤ IndependentCutLP.C022low.B 30 := by
  apply of_eval_le row_30 _ _ (0:ℤ) (flat N E) coeff_30 const_30
  have h := S.cycle_left 22 4 (by decide +kernel)
  simp only [row_30,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_31 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 31 j*flat N E j) ≤ IndependentCutLP.C022low.B 31 := by
  apply of_eval_le row_31 _ _ (0:ℤ) (flat N E) coeff_31 const_31
  have h := S.cycle_right 27 0 (by decide +kernel)
  simp only [row_31,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_32 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 32 j*flat N E j) ≤ IndependentCutLP.C022low.B 32 := by
  apply of_eval_le row_32 _ _ (0:ℤ) (flat N E) coeff_32 const_32
  have h := S.cycle_right 32 0 (by decide +kernel)
  simp only [row_32,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_33 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 33 j*flat N E j) ≤ IndependentCutLP.C022low.B 33 := by
  apply of_eval_le row_33 _ _ (0:ℤ) (flat N E) coeff_33 const_33
  have h := S.cycle_right 38 3 (by decide +kernel)
  simp only [row_33,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_34 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 34 j*flat N E j) ≤ IndependentCutLP.C022low.B 34 := by
  apply of_eval_le row_34 _ _ (-26:ℤ) (flat N E) coeff_34 const_34
  have h := S.cuts bits_34
  simp only [row_34,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_35 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 35 j*flat N E j) ≤ IndependentCutLP.C022low.B 35 := by
  apply of_eval_le row_35 _ _ (-26:ℤ) (flat N E) coeff_35 const_35
  have h := S.cuts bits_35
  simp only [row_35,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_36 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 36 j*flat N E j) ≤ IndependentCutLP.C022low.B 36 := by
  apply of_eval_le row_36 _ _ (-26:ℤ) (flat N E) coeff_36 const_36
  have h := S.cuts bits_36
  simp only [row_36,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_37 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 37 j*flat N E j) ≤ IndependentCutLP.C022low.B 37 := by
  apply of_eval_le row_37 _ _ (-26:ℤ) (flat N E) coeff_37 const_37
  have h := S.cuts bits_37
  simp only [row_37,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_38 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 38 j*flat N E j) ≤ IndependentCutLP.C022low.B 38 := by
  apply of_eval_le row_38 _ _ (-26:ℤ) (flat N E) coeff_38 const_38
  have h := S.cuts bits_38
  simp only [row_38,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_39 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 39 j*flat N E j) ≤ IndependentCutLP.C022low.B 39 := by
  apply of_eval_le row_39 _ _ (-26:ℤ) (flat N E) coeff_39 const_39
  have h := S.cuts bits_39
  simp only [row_39,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_40 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 40 j*flat N E j) ≤ IndependentCutLP.C022low.B 40 := by
  apply of_eval_le row_40 _ _ (-26:ℤ) (flat N E) coeff_40 const_40
  have h := S.cuts bits_40
  simp only [row_40,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_41 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 41 j*flat N E j) ≤ IndependentCutLP.C022low.B 41 := by
  apply of_eval_le row_41 _ _ (-26:ℤ) (flat N E) coeff_41 const_41
  have h := S.cuts bits_41
  simp only [row_41,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_42 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 42 j*flat N E j) ≤ IndependentCutLP.C022low.B 42 := by
  apply of_eval_le row_42 _ _ (-26:ℤ) (flat N E) coeff_42 const_42
  have h := S.cuts bits_42
  simp only [row_42,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_43 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 43 j*flat N E j) ≤ IndependentCutLP.C022low.B 43 := by
  apply of_eval_le row_43 _ _ (-26:ℤ) (flat N E) coeff_43 const_43
  have h := S.cuts bits_43
  simp only [row_43,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_44 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 44 j*flat N E j) ≤ IndependentCutLP.C022low.B 44 := by
  apply of_eval_le row_44 _ _ (-26:ℤ) (flat N E) coeff_44 const_44
  have h := S.cuts bits_44
  simp only [row_44,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_45 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 45 j*flat N E j) ≤ IndependentCutLP.C022low.B 45 := by
  apply of_eval_le row_45 _ _ (-26:ℤ) (flat N E) coeff_45 const_45
  have h := S.cuts bits_45
  simp only [row_45,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_46 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 46 j*flat N E j) ≤ IndependentCutLP.C022low.B 46 := by
  apply of_eval_le row_46 _ _ (-26:ℤ) (flat N E) coeff_46 const_46
  have h := S.cuts bits_46
  simp only [row_46,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_47 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 47 j*flat N E j) ≤ IndependentCutLP.C022low.B 47 := by
  apply of_eval_le row_47 _ _ (-26:ℤ) (flat N E) coeff_47 const_47
  have h := S.cuts bits_47
  simp only [row_47,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_48 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 48 j*flat N E j) ≤ IndependentCutLP.C022low.B 48 := by
  apply of_eval_le row_48 _ _ (-26:ℤ) (flat N E) coeff_48 const_48
  have h := S.cuts bits_48
  simp only [row_48,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_49 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 49 j*flat N E j) ≤ IndependentCutLP.C022low.B 49 := by
  apply of_eval_le row_49 _ _ (-26:ℤ) (flat N E) coeff_49 const_49
  have h := S.cuts bits_49
  simp only [row_49,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_50 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 50 j*flat N E j) ≤ IndependentCutLP.C022low.B 50 := by
  apply of_eval_le row_50 _ _ (-26:ℤ) (flat N E) coeff_50 const_50
  have h := S.cuts bits_50
  simp only [row_50,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_51 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 51 j*flat N E j) ≤ IndependentCutLP.C022low.B 51 := by
  apply of_eval_le row_51 _ _ (-26:ℤ) (flat N E) coeff_51 const_51
  have h := S.cuts bits_51
  simp only [row_51,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_52 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) :
    (∑j,IndependentCutLP.C022low.A 52 j*flat N E j) ≤ IndependentCutLP.C022low.B 52 := by
  apply of_eval_le row_52 _ _ (-26:ℤ) (flat N E) coeff_52 const_52
  have h := S.cuts bits_52
  simp only [row_52,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 12 117) : False := by
  apply IndependentCutLP.C022low.impossible (flat N E)
  · intro j
    refine Fin.addCases (m:=17) (n:=40) (fun a => ?_) (fun k => ?_) j
    · simpa [flat] using S.npos a
    · simpa [flat] using S.epos k
  · intro i
    fin_cases i
    · exact valid_0 N E S
    · exact valid_1 N E S
    · exact valid_2 N E S
    · exact valid_3 N E S
    · exact valid_4 N E S
    · exact valid_5 N E S
    · exact valid_6 N E S
    · exact valid_7 N E S
    · exact valid_8 N E S
    · exact valid_9 N E S
    · exact valid_10 N E S
    · exact valid_11 N E S
    · exact valid_12 N E S
    · exact valid_13 N E S
    · exact valid_14 N E S
    · exact valid_15 N E S
    · exact valid_16 N E S
    · exact valid_17 N E S
    · exact valid_18 N E S
    · exact valid_19 N E S
    · exact valid_20 N E S
    · exact valid_21 N E S
    · exact valid_22 N E S
    · exact valid_23 N E S
    · exact valid_24 N E S
    · exact valid_25 N E S
    · exact valid_26 N E S
    · exact valid_27 N E S
    · exact valid_28 N E S
    · exact valid_29 N E S
    · exact valid_30 N E S
    · exact valid_31 N E S
    · exact valid_32 N E S
    · exact valid_33 N E S
    · exact valid_34 N E S
    · exact valid_35 N E S
    · exact valid_36 N E S
    · exact valid_37 N E S
    · exact valid_38 N E S
    · exact valid_39 N E S
    · exact valid_40 N E S
    · exact valid_41 N E S
    · exact valid_42 N E S
    · exact valid_43 N E S
    · exact valid_44 N E S
    · exact valid_45 N E S
    · exact valid_46 N E S
    · exact valid_47 N E S
    · exact valid_48 N E S
    · exact valid_49 N E S
    · exact valid_50 N E S
    · exact valid_51 N E S
    · exact valid_52 N E S
end FastCutCase.C022low

-- CaseFast022high

namespace FastCutCase.C022high
open Finset ThreeExceptions FiniteCutTemplate GraphMass CutSummary CertifiedAffine AffineCut
abbrev T := NativeCutTemplate.C022.table
def row_0 : Form 57 := (verticesForm (n:=17) (e:=40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_0 : ∀j,row_0.coeff j=IndependentCutLP.C022high.A 0 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_0 : (22:ℤ)-row_0.constant=IndependentCutLP.C022high.B 0 := by decide +kernel
def row_1 : Form 57 := (mForm T)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_1 : ∀j,row_1.coeff j=IndependentCutLP.C022high.A 1 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_1 : (121:ℤ)-row_1.constant=IndependentCutLP.C022high.B 1 := by decide +kernel
def row_2 : Form 57 := (.scale (-1) (nv (n:=17) (e:=40) (T.cycle 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_2 : ∀j,row_2.coeff j=IndependentCutLP.C022high.A 2 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_2 : (-1:ℤ)-row_2.constant=IndependentCutLP.C022high.B 2 := by decide +kernel
def row_3 : Form 57 := (.plus (degreeForm T 0) (.scale (-11) (nv (n:=17) (e:=40) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_3 : ∀j,row_3.coeff j=IndependentCutLP.C022high.A 3 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_3 : (0:ℤ)-row_3.constant=IndependentCutLP.C022high.B 3 := by decide +kernel
def row_4 : Form 57 := (.plus (degreeForm T 1) (.scale (-11) (nv (n:=17) (e:=40) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_4 : ∀j,row_4.coeff j=IndependentCutLP.C022high.A 4 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_4 : (0:ℤ)-row_4.constant=IndependentCutLP.C022high.B 4 := by decide +kernel
def row_5 : Form 57 := (.plus (degreeForm T 5) (.scale (-11) (nv (n:=17) (e:=40) 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_5 : ∀j,row_5.coeff j=IndependentCutLP.C022high.A 5 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_5 : (0:ℤ)-row_5.constant=IndependentCutLP.C022high.B 5 := by decide +kernel
def row_6 : Form 57 := (.plus (degreeForm T 6) (.scale (-11) (nv (n:=17) (e:=40) 6)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_6 : ∀j,row_6.coeff j=IndependentCutLP.C022high.A 6 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_6 : (0:ℤ)-row_6.constant=IndependentCutLP.C022high.B 6 := by decide +kernel
def row_7 : Form 57 := (.plus (degreeForm T 8) (.scale (-11) (nv (n:=17) (e:=40) 8)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_7 : ∀j,row_7.coeff j=IndependentCutLP.C022high.A 7 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_7 : (0:ℤ)-row_7.constant=IndependentCutLP.C022high.B 7 := by decide +kernel
def row_8 : Form 57 := (.plus (degreeForm T 9) (.scale (-11) (nv (n:=17) (e:=40) 9)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_8 : ∀j,row_8.coeff j=IndependentCutLP.C022high.A 8 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_8 : (0:ℤ)-row_8.constant=IndependentCutLP.C022high.B 8 := by decide +kernel
def row_9 : Form 57 := (.plus (degreeForm T 10) (.scale (-11) (nv (n:=17) (e:=40) 10)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_9 : ∀j,row_9.coeff j=IndependentCutLP.C022high.A 9 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_9 : (0:ℤ)-row_9.constant=IndependentCutLP.C022high.B 9 := by decide +kernel
def row_10 : Form 57 := (.plus (degreeForm T 11) (.scale (-11) (nv (n:=17) (e:=40) 11)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_10 : ∀j,row_10.coeff j=IndependentCutLP.C022high.A 10 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_10 : (0:ℤ)-row_10.constant=IndependentCutLP.C022high.B 10 := by decide +kernel
def row_11 : Form 57 := (.plus (degreeForm T 13) (.scale (-11) (nv (n:=17) (e:=40) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_11 : ∀j,row_11.coeff j=IndependentCutLP.C022high.A 11 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_11 : (0:ℤ)-row_11.constant=IndependentCutLP.C022high.B 11 := by decide +kernel
def row_12 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 4).2) (.scale (-1) (ev (n:=17) (e:=40) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_12 : ∀j,row_12.coeff j=IndependentCutLP.C022high.A 12 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_12 : (0:ℤ)-row_12.constant=IndependentCutLP.C022high.B 12 := by decide +kernel
def row_13 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 10).2) (.scale (-1) (ev (n:=17) (e:=40) 10)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_13 : ∀j,row_13.coeff j=IndependentCutLP.C022high.A 13 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_13 : (0:ℤ)-row_13.constant=IndependentCutLP.C022high.B 13 := by decide +kernel
def row_14 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 12).2) (.scale (-1) (ev (n:=17) (e:=40) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_14 : ∀j,row_14.coeff j=IndependentCutLP.C022high.A 14 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_14 : (0:ℤ)-row_14.constant=IndependentCutLP.C022high.B 14 := by decide +kernel
def row_15 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 13).2) (.scale (-1) (ev (n:=17) (e:=40) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_15 : ∀j,row_15.coeff j=IndependentCutLP.C022high.A 15 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_15 : (0:ℤ)-row_15.constant=IndependentCutLP.C022high.B 15 := by decide +kernel
def row_16 : Form 57 := (.plus (.plus (nv (n:=17) (e:=40) (T.ends 14).1) (nv (n:=17) (e:=40) (T.ends 14).2)) (.scale (-1) (ev (n:=17) (e:=40) 14)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_16 : ∀j,row_16.coeff j=IndependentCutLP.C022high.A 16 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_16 : (1:ℤ)-row_16.constant=IndependentCutLP.C022high.B 16 := by decide +kernel
def row_17 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 19).2) (.scale (-1) (ev (n:=17) (e:=40) 19)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_17 : ∀j,row_17.coeff j=IndependentCutLP.C022high.A 17 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_17 : (0:ℤ)-row_17.constant=IndependentCutLP.C022high.B 17 := by decide +kernel
def row_18 : Form 57 := (.plus (.plus (nv (n:=17) (e:=40) (T.ends 20).1) (nv (n:=17) (e:=40) (T.ends 20).2)) (.scale (-1) (ev (n:=17) (e:=40) 20)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_18 : ∀j,row_18.coeff j=IndependentCutLP.C022high.A 18 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_18 : (1:ℤ)-row_18.constant=IndependentCutLP.C022high.B 18 := by decide +kernel
def row_19 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 21).2) (.scale (-1) (ev (n:=17) (e:=40) 21)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_19 : ∀j,row_19.coeff j=IndependentCutLP.C022high.A 19 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_19 : (0:ℤ)-row_19.constant=IndependentCutLP.C022high.B 19 := by decide +kernel
def row_20 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 22).2) (.scale (-1) (ev (n:=17) (e:=40) 22)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_20 : ∀j,row_20.coeff j=IndependentCutLP.C022high.A 20 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_20 : (0:ℤ)-row_20.constant=IndependentCutLP.C022high.B 20 := by decide +kernel
def row_21 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 27).1) (.scale (-1) (ev (n:=17) (e:=40) 27)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_21 : ∀j,row_21.coeff j=IndependentCutLP.C022high.A 21 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_21 : (0:ℤ)-row_21.constant=IndependentCutLP.C022high.B 21 := by decide +kernel
def row_22 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 32).1) (.scale (-1) (ev (n:=17) (e:=40) 32)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_22 : ∀j,row_22.coeff j=IndependentCutLP.C022high.A 22 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_22 : (0:ℤ)-row_22.constant=IndependentCutLP.C022high.B 22 := by decide +kernel
def row_23 : Form 57 := (.plus (nv (n:=17) (e:=40) (T.ends 38).1) (.scale (-1) (ev (n:=17) (e:=40) 38)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_23 : ∀j,row_23.coeff j=IndependentCutLP.C022high.A 23 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_23 : (0:ℤ)-row_23.constant=IndependentCutLP.C022high.B 23 := by decide +kernel
def bits_24 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255968 : ℕ).testBit a.val) (fun x => (255968 : ℕ).testBit (17+x.val))
def row_24 : Form 57 := (.scale (-1) (cutForm T bits_24))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_24 : ∀j,row_24.coeff j=IndependentCutLP.C022high.A 24 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_24 : (-26:ℤ)-row_24.constant=IndependentCutLP.C022high.B 24 := by decide +kernel
def bits_25 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255188 : ℕ).testBit a.val) (fun x => (255188 : ℕ).testBit (17+x.val))
def row_25 : Form 57 := (.scale (-1) (cutForm T bits_25))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_25 : ∀j,row_25.coeff j=IndependentCutLP.C022high.A 25 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_25 : (-26:ℤ)-row_25.constant=IndependentCutLP.C022high.B 25 := by decide +kernel
def bits_26 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (977184 : ℕ).testBit a.val) (fun x => (977184 : ℕ).testBit (17+x.val))
def row_26 : Form 57 := (.scale (-1) (cutForm T bits_26))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_26 : ∀j,row_26.coeff j=IndependentCutLP.C022high.A 26 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_26 : (-26:ℤ)-row_26.constant=IndependentCutLP.C022high.B 26 := by decide +kernel
def bits_27 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (948256 : ℕ).testBit a.val) (fun x => (948256 : ℕ).testBit (17+x.val))
def row_27 : Form 57 := (.scale (-1) (cutForm T bits_27))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_27 : ∀j,row_27.coeff j=IndependentCutLP.C022high.A 27 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_27 : (-26:ℤ)-row_27.constant=IndependentCutLP.C022high.B 27 := by decide +kernel
def bits_28 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255964 : ℕ).testBit a.val) (fun x => (255964 : ℕ).testBit (17+x.val))
def row_28 : Form 57 := (.scale (-1) (cutForm T bits_28))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_28 : ∀j,row_28.coeff j=IndependentCutLP.C022high.A 28 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_28 : (-26:ℤ)-row_28.constant=IndependentCutLP.C022high.B 28 := by decide +kernel
def bits_29 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (202812 : ℕ).testBit a.val) (fun x => (202812 : ℕ).testBit (17+x.val))
def row_29 : Form 57 := (.scale (-1) (cutForm T bits_29))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_29 : ∀j,row_29.coeff j=IndependentCutLP.C022high.A 29 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_29 : (-26:ℤ)-row_29.constant=IndependentCutLP.C022high.B 29 := by decide +kernel
def bits_30 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (964640 : ℕ).testBit a.val) (fun x => (964640 : ℕ).testBit (17+x.val))
def row_30 : Form 57 := (.scale (-1) (cutForm T bits_30))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_30 : ∀j,row_30.coeff j=IndependentCutLP.C022high.A 30 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_30 : (-26:ℤ)-row_30.constant=IndependentCutLP.C022high.B 30 := by decide +kernel
def bits_31 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (792622 : ℕ).testBit a.val) (fun x => (792622 : ℕ).testBit (17+x.val))
def row_31 : Form 57 := (.scale (-1) (cutForm T bits_31))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_31 : ∀j,row_31.coeff j=IndependentCutLP.C022high.A 31 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_31 : (-26:ℤ)-row_31.constant=IndependentCutLP.C022high.B 31 := by decide +kernel
def bits_32 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255072 : ℕ).testBit a.val) (fun x => (255072 : ℕ).testBit (17+x.val))
def row_32 : Form 57 := (.scale (-1) (cutForm T bits_32))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_32 : ∀j,row_32.coeff j=IndependentCutLP.C022high.A 32 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_32 : (-26:ℤ)-row_32.constant=IndependentCutLP.C022high.B 32 := by decide +kernel
def bits_33 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (1042976 : ℕ).testBit a.val) (fun x => (1042976 : ℕ).testBit (17+x.val))
def row_33 : Form 57 := (.scale (-1) (cutForm T bits_33))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_33 : ∀j,row_33.coeff j=IndependentCutLP.C022high.A 33 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_33 : (-26:ℤ)-row_33.constant=IndependentCutLP.C022high.B 33 := by decide +kernel
def bits_34 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (616390 : ℕ).testBit a.val) (fun x => (616390 : ℕ).testBit (17+x.val))
def row_34 : Form 57 := (.scale (-1) (cutForm T bits_34))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_34 : ∀j,row_34.coeff j=IndependentCutLP.C022high.A 34 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_34 : (-26:ℤ)-row_34.constant=IndependentCutLP.C022high.B 34 := by decide +kernel
def bits_35 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (913568 : ℕ).testBit a.val) (fun x => (913568 : ℕ).testBit (17+x.val))
def row_35 : Form 57 := (.scale (-1) (cutForm T bits_35))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_35 : ∀j,row_35.coeff j=IndependentCutLP.C022high.A 35 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_35 : (-26:ℤ)-row_35.constant=IndependentCutLP.C022high.B 35 := by decide +kernel
def bits_36 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (743476 : ℕ).testBit a.val) (fun x => (743476 : ℕ).testBit (17+x.val))
def row_36 : Form 57 := (.scale (-1) (cutForm T bits_36))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_36 : ∀j,row_36.coeff j=IndependentCutLP.C022high.A 36 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_36 : (-26:ℤ)-row_36.constant=IndependentCutLP.C022high.B 36 := by decide +kernel
def bits_37 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255776 : ℕ).testBit a.val) (fun x => (255776 : ℕ).testBit (17+x.val))
def row_37 : Form 57 := (.scale (-1) (cutForm T bits_37))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_37 : ∀j,row_37.coeff j=IndependentCutLP.C022high.A 37 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_37 : (-26:ℤ)-row_37.constant=IndependentCutLP.C022high.B 37 := by decide +kernel
def bits_38 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (1042464 : ℕ).testBit a.val) (fun x => (1042464 : ℕ).testBit (17+x.val))
def row_38 : Form 57 := (.scale (-1) (cutForm T bits_38))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_38 : ∀j,row_38.coeff j=IndependentCutLP.C022high.A 38 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_38 : (-26:ℤ)-row_38.constant=IndependentCutLP.C022high.B 38 := by decide +kernel
def bits_39 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255952 : ℕ).testBit a.val) (fun x => (255952 : ℕ).testBit (17+x.val))
def row_39 : Form 57 := (.scale (-1) (cutForm T bits_39))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_39 : ∀j,row_39.coeff j=IndependentCutLP.C022high.A 39 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_39 : (-26:ℤ)-row_39.constant=IndependentCutLP.C022high.B 39 := by decide +kernel
def bits_40 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (235576 : ℕ).testBit a.val) (fun x => (235576 : ℕ).testBit (17+x.val))
def row_40 : Form 57 := (.scale (-1) (cutForm T bits_40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_40 : ∀j,row_40.coeff j=IndependentCutLP.C022high.A 40 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_40 : (-26:ℤ)-row_40.constant=IndependentCutLP.C022high.B 40 := by decide +kernel
def bits_41 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (800800 : ℕ).testBit a.val) (fun x => (800800 : ℕ).testBit (17+x.val))
def row_41 : Form 57 := (.scale (-1) (cutForm T bits_41))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_41 : ∀j,row_41.coeff j=IndependentCutLP.C022high.A 41 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_41 : (-26:ℤ)-row_41.constant=IndependentCutLP.C022high.B 41 := by decide +kernel
def bits_42 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (849952 : ℕ).testBit a.val) (fun x => (849952 : ℕ).testBit (17+x.val))
def row_42 : Form 57 := (.scale (-1) (cutForm T bits_42))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_42 : ∀j,row_42.coeff j=IndependentCutLP.C022high.A 42 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_42 : (-26:ℤ)-row_42.constant=IndependentCutLP.C022high.B 42 := by decide +kernel
def bits_43 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (219188 : ℕ).testBit a.val) (fun x => (219188 : ℕ).testBit (17+x.val))
def row_43 : Form 57 := (.scale (-1) (cutForm T bits_43))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_43 : ∀j,row_43.coeff j=IndependentCutLP.C022high.A 43 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_43 : (-26:ℤ)-row_43.constant=IndependentCutLP.C022high.B 43 := by decide +kernel
def bits_44 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (432184 : ℕ).testBit a.val) (fun x => (432184 : ℕ).testBit (17+x.val))
def row_44 : Form 57 := (.scale (-1) (cutForm T bits_44))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_44 : ∀j,row_44.coeff j=IndependentCutLP.C022high.A 44 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_44 : (-26:ℤ)-row_44.constant=IndependentCutLP.C022high.B 44 := by decide +kernel
def bits_45 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (909536 : ℕ).testBit a.val) (fun x => (909536 : ℕ).testBit (17+x.val))
def row_45 : Form 57 := (.scale (-1) (cutForm T bits_45))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_45 : ∀j,row_45.coeff j=IndependentCutLP.C022high.A 45 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_45 : (-26:ℤ)-row_45.constant=IndependentCutLP.C022high.B 45 := by decide +kernel
def bits_46 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255328 : ℕ).testBit a.val) (fun x => (255328 : ℕ).testBit (17+x.val))
def row_46 : Form 57 := (.scale (-1) (cutForm T bits_46))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_46 : ∀j,row_46.coeff j=IndependentCutLP.C022high.A 46 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_46 : (-26:ℤ)-row_46.constant=IndependentCutLP.C022high.B 46 := by decide +kernel
def bits_47 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (256032 : ℕ).testBit a.val) (fun x => (256032 : ℕ).testBit (17+x.val))
def row_47 : Form 57 := (.scale (-1) (cutForm T bits_47))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_47 : ∀j,row_47.coeff j=IndependentCutLP.C022high.A 47 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_47 : (-26:ℤ)-row_47.constant=IndependentCutLP.C022high.B 47 := by decide +kernel
def bits_48 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (792634 : ℕ).testBit a.val) (fun x => (792634 : ℕ).testBit (17+x.val))
def row_48 : Form 57 := (.scale (-1) (cutForm T bits_48))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_48 : ∀j,row_48.coeff j=IndependentCutLP.C022high.A 48 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_48 : (-26:ℤ)-row_48.constant=IndependentCutLP.C022high.B 48 := by decide +kernel
def bits_49 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (255840 : ℕ).testBit a.val) (fun x => (255840 : ℕ).testBit (17+x.val))
def row_49 : Form 57 := (.scale (-1) (cutForm T bits_49))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_49 : ∀j,row_49.coeff j=IndependentCutLP.C022high.A 49 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_49 : (-26:ℤ)-row_49.constant=IndependentCutLP.C022high.B 49 := by decide +kernel
def bits_50 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (550854 : ℕ).testBit a.val) (fun x => (550854 : ℕ).testBit (17+x.val))
def row_50 : Form 57 := (.scale (-1) (cutForm T bits_50))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_50 : ∀j,row_50.coeff j=IndependentCutLP.C022high.A 50 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_50 : (-26:ℤ)-row_50.constant=IndependentCutLP.C022high.B 50 := by decide +kernel
def bits_51 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (267998 : ℕ).testBit a.val) (fun x => (267998 : ℕ).testBit (17+x.val))
def row_51 : Form 57 := (.scale (-1) (cutForm T bits_51))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_51 : ∀j,row_51.coeff j=IndependentCutLP.C022high.A 51 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_51 : (-26:ℤ)-row_51.constant=IndependentCutLP.C022high.B 51 := by decide +kernel
def bits_52 : Fin 17 ⊕ Fin 3 → Bool := Sum.elim (fun a => (529886 : ℕ).testBit a.val) (fun x => (529886 : ℕ).testBit (17+x.val))
def row_52 : Form 57 := (.scale (-1) (cutForm T bits_52))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_52 : ∀j,row_52.coeff j=IndependentCutLP.C022high.A 52 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_52 : (-26:ℤ)-row_52.constant=IndependentCutLP.C022high.B 52 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_0 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 0 j*flat N E j) ≤ IndependentCutLP.C022high.B 0 := by
  apply of_eval_le row_0 _ _ (22:ℤ) (flat N E) coeff_0 const_0
  have h := S.vertices
  simp only [row_0,eval_vertices]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_1 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 1 j*flat N E j) ≤ IndependentCutLP.C022high.B 1 := by
  apply of_eval_le row_1 _ _ (121:ℤ) (flat N E) coeff_1 const_1
  have h := S.edgeHi
  simp only [row_1,eval_m]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_2 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 2 j*flat N E j) ≤ IndependentCutLP.C022high.B 2 := by
  apply of_eval_le row_2 _ _ (-1:ℤ) (flat N E) coeff_2 const_2
  have h := S.exists_cycle 2
  simp only [row_2,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_3 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 3 j*flat N E j) ≤ IndependentCutLP.C022high.B 3 := by
  apply of_eval_le row_3 _ _ (0:ℤ) (flat N E) coeff_3 const_3
  have h := S.degrees 0
  simp only [row_3,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_4 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 4 j*flat N E j) ≤ IndependentCutLP.C022high.B 4 := by
  apply of_eval_le row_4 _ _ (0:ℤ) (flat N E) coeff_4 const_4
  have h := S.degrees 1
  simp only [row_4,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_5 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 5 j*flat N E j) ≤ IndependentCutLP.C022high.B 5 := by
  apply of_eval_le row_5 _ _ (0:ℤ) (flat N E) coeff_5 const_5
  have h := S.degrees 5
  simp only [row_5,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_6 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 6 j*flat N E j) ≤ IndependentCutLP.C022high.B 6 := by
  apply of_eval_le row_6 _ _ (0:ℤ) (flat N E) coeff_6 const_6
  have h := S.degrees 6
  simp only [row_6,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_7 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 7 j*flat N E j) ≤ IndependentCutLP.C022high.B 7 := by
  apply of_eval_le row_7 _ _ (0:ℤ) (flat N E) coeff_7 const_7
  have h := S.degrees 8
  simp only [row_7,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_8 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 8 j*flat N E j) ≤ IndependentCutLP.C022high.B 8 := by
  apply of_eval_le row_8 _ _ (0:ℤ) (flat N E) coeff_8 const_8
  have h := S.degrees 9
  simp only [row_8,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_9 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 9 j*flat N E j) ≤ IndependentCutLP.C022high.B 9 := by
  apply of_eval_le row_9 _ _ (0:ℤ) (flat N E) coeff_9 const_9
  have h := S.degrees 10
  simp only [row_9,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_10 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 10 j*flat N E j) ≤ IndependentCutLP.C022high.B 10 := by
  apply of_eval_le row_10 _ _ (0:ℤ) (flat N E) coeff_10 const_10
  have h := S.degrees 11
  simp only [row_10,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_11 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 11 j*flat N E j) ≤ IndependentCutLP.C022high.B 11 := by
  apply of_eval_le row_11 _ _ (0:ℤ) (flat N E) coeff_11 const_11
  have h := S.degrees 13
  simp only [row_11,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_12 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 12 j*flat N E j) ≤ IndependentCutLP.C022high.B 12 := by
  apply of_eval_le row_12 _ _ (0:ℤ) (flat N E) coeff_12 const_12
  have h := S.cycle_left 4 1 (by decide +kernel)
  simp only [row_12,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_13 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 13 j*flat N E j) ≤ IndependentCutLP.C022high.B 13 := by
  apply of_eval_le row_13 _ _ (0:ℤ) (flat N E) coeff_13 const_13
  have h := S.cycle_left 10 3 (by decide +kernel)
  simp only [row_13,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_14 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 14 j*flat N E j) ≤ IndependentCutLP.C022high.B 14 := by
  apply of_eval_le row_14 _ _ (0:ℤ) (flat N E) coeff_14 const_14
  have h := S.cycle_left 12 3 (by decide +kernel)
  simp only [row_14,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_15 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 15 j*flat N E j) ≤ IndependentCutLP.C022high.B 15 := by
  apply of_eval_le row_15 _ _ (0:ℤ) (flat N E) coeff_15 const_15
  have h := S.cycle_left 13 3 (by decide +kernel)
  simp only [row_15,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_16 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 16 j*flat N E j) ≤ IndependentCutLP.C022high.B 16 := by
  apply of_eval_le row_16 _ _ (1:ℤ) (flat N E) coeff_16 const_16
  have h := S.cycle_both 14 3 2 (by decide +kernel) (by decide +kernel)
  simp only [row_16,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_17 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 17 j*flat N E j) ≤ IndependentCutLP.C022high.B 17 := by
  apply of_eval_le row_17 _ _ (0:ℤ) (flat N E) coeff_17 const_17
  have h := S.cycle_left 19 4 (by decide +kernel)
  simp only [row_17,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_18 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 18 j*flat N E j) ≤ IndependentCutLP.C022high.B 18 := by
  apply of_eval_le row_18 _ _ (1:ℤ) (flat N E) coeff_18 const_18
  have h := S.cycle_both 20 4 0 (by decide +kernel) (by decide +kernel)
  simp only [row_18,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_19 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 19 j*flat N E j) ≤ IndependentCutLP.C022high.B 19 := by
  apply of_eval_le row_19 _ _ (0:ℤ) (flat N E) coeff_19 const_19
  have h := S.cycle_left 21 4 (by decide +kernel)
  simp only [row_19,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_20 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 20 j*flat N E j) ≤ IndependentCutLP.C022high.B 20 := by
  apply of_eval_le row_20 _ _ (0:ℤ) (flat N E) coeff_20 const_20
  have h := S.cycle_left 22 4 (by decide +kernel)
  simp only [row_20,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_21 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 21 j*flat N E j) ≤ IndependentCutLP.C022high.B 21 := by
  apply of_eval_le row_21 _ _ (0:ℤ) (flat N E) coeff_21 const_21
  have h := S.cycle_right 27 0 (by decide +kernel)
  simp only [row_21,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_22 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 22 j*flat N E j) ≤ IndependentCutLP.C022high.B 22 := by
  apply of_eval_le row_22 _ _ (0:ℤ) (flat N E) coeff_22 const_22
  have h := S.cycle_right 32 0 (by decide +kernel)
  simp only [row_22,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_23 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 23 j*flat N E j) ≤ IndependentCutLP.C022high.B 23 := by
  apply of_eval_le row_23 _ _ (0:ℤ) (flat N E) coeff_23 const_23
  have h := S.cycle_right 38 3 (by decide +kernel)
  simp only [row_23,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_24 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 24 j*flat N E j) ≤ IndependentCutLP.C022high.B 24 := by
  apply of_eval_le row_24 _ _ (-26:ℤ) (flat N E) coeff_24 const_24
  have h := S.cuts bits_24
  simp only [row_24,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_25 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 25 j*flat N E j) ≤ IndependentCutLP.C022high.B 25 := by
  apply of_eval_le row_25 _ _ (-26:ℤ) (flat N E) coeff_25 const_25
  have h := S.cuts bits_25
  simp only [row_25,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_26 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 26 j*flat N E j) ≤ IndependentCutLP.C022high.B 26 := by
  apply of_eval_le row_26 _ _ (-26:ℤ) (flat N E) coeff_26 const_26
  have h := S.cuts bits_26
  simp only [row_26,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_27 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 27 j*flat N E j) ≤ IndependentCutLP.C022high.B 27 := by
  apply of_eval_le row_27 _ _ (-26:ℤ) (flat N E) coeff_27 const_27
  have h := S.cuts bits_27
  simp only [row_27,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_28 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 28 j*flat N E j) ≤ IndependentCutLP.C022high.B 28 := by
  apply of_eval_le row_28 _ _ (-26:ℤ) (flat N E) coeff_28 const_28
  have h := S.cuts bits_28
  simp only [row_28,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_29 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 29 j*flat N E j) ≤ IndependentCutLP.C022high.B 29 := by
  apply of_eval_le row_29 _ _ (-26:ℤ) (flat N E) coeff_29 const_29
  have h := S.cuts bits_29
  simp only [row_29,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_30 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 30 j*flat N E j) ≤ IndependentCutLP.C022high.B 30 := by
  apply of_eval_le row_30 _ _ (-26:ℤ) (flat N E) coeff_30 const_30
  have h := S.cuts bits_30
  simp only [row_30,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_31 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 31 j*flat N E j) ≤ IndependentCutLP.C022high.B 31 := by
  apply of_eval_le row_31 _ _ (-26:ℤ) (flat N E) coeff_31 const_31
  have h := S.cuts bits_31
  simp only [row_31,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_32 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 32 j*flat N E j) ≤ IndependentCutLP.C022high.B 32 := by
  apply of_eval_le row_32 _ _ (-26:ℤ) (flat N E) coeff_32 const_32
  have h := S.cuts bits_32
  simp only [row_32,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_33 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 33 j*flat N E j) ≤ IndependentCutLP.C022high.B 33 := by
  apply of_eval_le row_33 _ _ (-26:ℤ) (flat N E) coeff_33 const_33
  have h := S.cuts bits_33
  simp only [row_33,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_34 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 34 j*flat N E j) ≤ IndependentCutLP.C022high.B 34 := by
  apply of_eval_le row_34 _ _ (-26:ℤ) (flat N E) coeff_34 const_34
  have h := S.cuts bits_34
  simp only [row_34,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_35 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 35 j*flat N E j) ≤ IndependentCutLP.C022high.B 35 := by
  apply of_eval_le row_35 _ _ (-26:ℤ) (flat N E) coeff_35 const_35
  have h := S.cuts bits_35
  simp only [row_35,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_36 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 36 j*flat N E j) ≤ IndependentCutLP.C022high.B 36 := by
  apply of_eval_le row_36 _ _ (-26:ℤ) (flat N E) coeff_36 const_36
  have h := S.cuts bits_36
  simp only [row_36,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_37 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 37 j*flat N E j) ≤ IndependentCutLP.C022high.B 37 := by
  apply of_eval_le row_37 _ _ (-26:ℤ) (flat N E) coeff_37 const_37
  have h := S.cuts bits_37
  simp only [row_37,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_38 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 38 j*flat N E j) ≤ IndependentCutLP.C022high.B 38 := by
  apply of_eval_le row_38 _ _ (-26:ℤ) (flat N E) coeff_38 const_38
  have h := S.cuts bits_38
  simp only [row_38,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_39 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 39 j*flat N E j) ≤ IndependentCutLP.C022high.B 39 := by
  apply of_eval_le row_39 _ _ (-26:ℤ) (flat N E) coeff_39 const_39
  have h := S.cuts bits_39
  simp only [row_39,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_40 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 40 j*flat N E j) ≤ IndependentCutLP.C022high.B 40 := by
  apply of_eval_le row_40 _ _ (-26:ℤ) (flat N E) coeff_40 const_40
  have h := S.cuts bits_40
  simp only [row_40,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_41 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 41 j*flat N E j) ≤ IndependentCutLP.C022high.B 41 := by
  apply of_eval_le row_41 _ _ (-26:ℤ) (flat N E) coeff_41 const_41
  have h := S.cuts bits_41
  simp only [row_41,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_42 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 42 j*flat N E j) ≤ IndependentCutLP.C022high.B 42 := by
  apply of_eval_le row_42 _ _ (-26:ℤ) (flat N E) coeff_42 const_42
  have h := S.cuts bits_42
  simp only [row_42,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_43 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 43 j*flat N E j) ≤ IndependentCutLP.C022high.B 43 := by
  apply of_eval_le row_43 _ _ (-26:ℤ) (flat N E) coeff_43 const_43
  have h := S.cuts bits_43
  simp only [row_43,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_44 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 44 j*flat N E j) ≤ IndependentCutLP.C022high.B 44 := by
  apply of_eval_le row_44 _ _ (-26:ℤ) (flat N E) coeff_44 const_44
  have h := S.cuts bits_44
  simp only [row_44,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_45 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 45 j*flat N E j) ≤ IndependentCutLP.C022high.B 45 := by
  apply of_eval_le row_45 _ _ (-26:ℤ) (flat N E) coeff_45 const_45
  have h := S.cuts bits_45
  simp only [row_45,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_46 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 46 j*flat N E j) ≤ IndependentCutLP.C022high.B 46 := by
  apply of_eval_le row_46 _ _ (-26:ℤ) (flat N E) coeff_46 const_46
  have h := S.cuts bits_46
  simp only [row_46,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_47 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 47 j*flat N E j) ≤ IndependentCutLP.C022high.B 47 := by
  apply of_eval_le row_47 _ _ (-26:ℤ) (flat N E) coeff_47 const_47
  have h := S.cuts bits_47
  simp only [row_47,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_48 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 48 j*flat N E j) ≤ IndependentCutLP.C022high.B 48 := by
  apply of_eval_le row_48 _ _ (-26:ℤ) (flat N E) coeff_48 const_48
  have h := S.cuts bits_48
  simp only [row_48,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_49 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 49 j*flat N E j) ≤ IndependentCutLP.C022high.B 49 := by
  apply of_eval_le row_49 _ _ (-26:ℤ) (flat N E) coeff_49 const_49
  have h := S.cuts bits_49
  simp only [row_49,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_50 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 50 j*flat N E j) ≤ IndependentCutLP.C022high.B 50 := by
  apply of_eval_le row_50 _ _ (-26:ℤ) (flat N E) coeff_50 const_50
  have h := S.cuts bits_50
  simp only [row_50,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_51 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 51 j*flat N E j) ≤ IndependentCutLP.C022high.B 51 := by
  apply of_eval_le row_51 _ _ (-26:ℤ) (flat N E) coeff_51 const_51
  have h := S.cuts bits_51
  simp only [row_51,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_52 (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) :
    (∑j,IndependentCutLP.C022high.A 52 j*flat N E j) ≤ IndependentCutLP.C022high.B 52 := by
  apply of_eval_le row_52 _ _ (-26:ℤ) (flat N E) coeff_52 const_52
  have h := S.cuts bits_52
  simp only [row_52,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (N : Fin 17 → ℤ) (E : Fin 40 → ℤ) (S : Feasible T N E 11 121) : False := by
  apply IndependentCutLP.C022high.impossible (flat N E)
  · intro j
    refine Fin.addCases (m:=17) (n:=40) (fun a => ?_) (fun k => ?_) j
    · simpa [flat] using S.npos a
    · simpa [flat] using S.epos k
  · intro i
    fin_cases i
    · exact valid_0 N E S
    · exact valid_1 N E S
    · exact valid_2 N E S
    · exact valid_3 N E S
    · exact valid_4 N E S
    · exact valid_5 N E S
    · exact valid_6 N E S
    · exact valid_7 N E S
    · exact valid_8 N E S
    · exact valid_9 N E S
    · exact valid_10 N E S
    · exact valid_11 N E S
    · exact valid_12 N E S
    · exact valid_13 N E S
    · exact valid_14 N E S
    · exact valid_15 N E S
    · exact valid_16 N E S
    · exact valid_17 N E S
    · exact valid_18 N E S
    · exact valid_19 N E S
    · exact valid_20 N E S
    · exact valid_21 N E S
    · exact valid_22 N E S
    · exact valid_23 N E S
    · exact valid_24 N E S
    · exact valid_25 N E S
    · exact valid_26 N E S
    · exact valid_27 N E S
    · exact valid_28 N E S
    · exact valid_29 N E S
    · exact valid_30 N E S
    · exact valid_31 N E S
    · exact valid_32 N E S
    · exact valid_33 N E S
    · exact valid_34 N E S
    · exact valid_35 N E S
    · exact valid_36 N E S
    · exact valid_37 N E S
    · exact valid_38 N E S
    · exact valid_39 N E S
    · exact valid_40 N E S
    · exact valid_41 N E S
    · exact valid_42 N E S
    · exact valid_43 N E S
    · exact valid_44 N E S
    · exact valid_45 N E S
    · exact valid_46 N E S
    · exact valid_47 N E S
    · exact valid_48 N E S
    · exact valid_49 N E S
    · exact valid_50 N E S
    · exact valid_51 N E S
    · exact valid_52 N E S
end FastCutCase.C022high

-- CaseFast023

namespace FastCutCase.C023
open Finset ThreeExceptions FiniteCutTemplate GraphMass CutSummary CertifiedAffine AffineCut
abbrev T := NativeCutTemplate.C023.table
def row_0 : Form 51 := (verticesForm (n:=15) (e:=36))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_0 : ∀j,row_0.coeff j=IndependentCutLP.C023.A 0 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_0 : (22:ℤ)-row_0.constant=IndependentCutLP.C023.B 0 := by decide +kernel
def row_1 : Form 51 := (mForm T)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_1 : ∀j,row_1.coeff j=IndependentCutLP.C023.A 1 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_1 : (121:ℤ)-row_1.constant=IndependentCutLP.C023.B 1 := by decide +kernel
def row_2 : Form 51 := (.scale (-1) (nv (n:=15) (e:=36) (T.cycle 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_2 : ∀j,row_2.coeff j=IndependentCutLP.C023.A 2 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_2 : (-1:ℤ)-row_2.constant=IndependentCutLP.C023.B 2 := by decide +kernel
def row_3 : Form 51 := (.scale (-1) (nv (n:=15) (e:=36) (T.cycle 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_3 : ∀j,row_3.coeff j=IndependentCutLP.C023.A 3 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_3 : (-1:ℤ)-row_3.constant=IndependentCutLP.C023.B 3 := by decide +kernel
def row_4 : Form 51 := (.scale (-1) (nv (n:=15) (e:=36) (T.cycle 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_4 : ∀j,row_4.coeff j=IndependentCutLP.C023.A 4 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_4 : (-1:ℤ)-row_4.constant=IndependentCutLP.C023.B 4 := by decide +kernel
def row_5 : Form 51 := (.plus (degreeForm T 0) (.scale (-12) (nv (n:=15) (e:=36) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_5 : ∀j,row_5.coeff j=IndependentCutLP.C023.A 5 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_5 : (0:ℤ)-row_5.constant=IndependentCutLP.C023.B 5 := by decide +kernel
def row_6 : Form 51 := (.plus (degreeForm T 1) (.scale (-12) (nv (n:=15) (e:=36) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_6 : ∀j,row_6.coeff j=IndependentCutLP.C023.A 6 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_6 : (0:ℤ)-row_6.constant=IndependentCutLP.C023.B 6 := by decide +kernel
def row_7 : Form 51 := (.plus (degreeForm T 2) (.scale (-12) (nv (n:=15) (e:=36) 2)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_7 : ∀j,row_7.coeff j=IndependentCutLP.C023.A 7 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_7 : (0:ℤ)-row_7.constant=IndependentCutLP.C023.B 7 := by decide +kernel
def row_8 : Form 51 := (.plus (degreeForm T 3) (.scale (-12) (nv (n:=15) (e:=36) 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_8 : ∀j,row_8.coeff j=IndependentCutLP.C023.A 8 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_8 : (0:ℤ)-row_8.constant=IndependentCutLP.C023.B 8 := by decide +kernel
def row_9 : Form 51 := (.plus (degreeForm T 5) (.scale (-12) (nv (n:=15) (e:=36) 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_9 : ∀j,row_9.coeff j=IndependentCutLP.C023.A 9 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_9 : (0:ℤ)-row_9.constant=IndependentCutLP.C023.B 9 := by decide +kernel
def row_10 : Form 51 := (.plus (degreeForm T 7) (.scale (-12) (nv (n:=15) (e:=36) 7)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_10 : ∀j,row_10.coeff j=IndependentCutLP.C023.A 10 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_10 : (0:ℤ)-row_10.constant=IndependentCutLP.C023.B 10 := by decide +kernel
def row_11 : Form 51 := (.plus (degreeForm T 8) (.scale (-12) (nv (n:=15) (e:=36) 8)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_11 : ∀j,row_11.coeff j=IndependentCutLP.C023.A 11 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_11 : (0:ℤ)-row_11.constant=IndependentCutLP.C023.B 11 := by decide +kernel
def row_12 : Form 51 := (.plus (degreeForm T 9) (.scale (-12) (nv (n:=15) (e:=36) 9)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_12 : ∀j,row_12.coeff j=IndependentCutLP.C023.A 12 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_12 : (0:ℤ)-row_12.constant=IndependentCutLP.C023.B 12 := by decide +kernel
def row_13 : Form 51 := (.plus (degreeForm T 10) (.scale (-12) (nv (n:=15) (e:=36) 10)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_13 : ∀j,row_13.coeff j=IndependentCutLP.C023.A 13 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_13 : (0:ℤ)-row_13.constant=IndependentCutLP.C023.B 13 := by decide +kernel
def row_14 : Form 51 := (.plus (degreeForm T 11) (.scale (-12) (nv (n:=15) (e:=36) 11)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_14 : ∀j,row_14.coeff j=IndependentCutLP.C023.A 14 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_14 : (0:ℤ)-row_14.constant=IndependentCutLP.C023.B 14 := by decide +kernel
def row_15 : Form 51 := (.plus (degreeForm T 12) (.scale (-12) (nv (n:=15) (e:=36) 12)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_15 : ∀j,row_15.coeff j=IndependentCutLP.C023.A 15 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_15 : (0:ℤ)-row_15.constant=IndependentCutLP.C023.B 15 := by decide +kernel
def row_16 : Form 51 := (.plus (degreeForm T 13) (.scale (-12) (nv (n:=15) (e:=36) 13)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_16 : ∀j,row_16.coeff j=IndependentCutLP.C023.A 16 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_16 : (0:ℤ)-row_16.constant=IndependentCutLP.C023.B 16 := by decide +kernel
def row_17 : Form 51 := (.plus (nv (n:=15) (e:=36) (T.ends 0).2) (.scale (-1) (ev (n:=15) (e:=36) 0)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_17 : ∀j,row_17.coeff j=IndependentCutLP.C023.A 17 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_17 : (0:ℤ)-row_17.constant=IndependentCutLP.C023.B 17 := by decide +kernel
def row_18 : Form 51 := (.plus (.plus (nv (n:=15) (e:=36) (T.ends 1).1) (nv (n:=15) (e:=36) (T.ends 1).2)) (.scale (-1) (ev (n:=15) (e:=36) 1)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_18 : ∀j,row_18.coeff j=IndependentCutLP.C023.A 18 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_18 : (1:ℤ)-row_18.constant=IndependentCutLP.C023.B 18 := by decide +kernel
def row_19 : Form 51 := (.plus (nv (n:=15) (e:=36) (T.ends 4).2) (.scale (-1) (ev (n:=15) (e:=36) 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_19 : ∀j,row_19.coeff j=IndependentCutLP.C023.A 19 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_19 : (0:ℤ)-row_19.constant=IndependentCutLP.C023.B 19 := by decide +kernel
def row_20 : Form 51 := (.plus (nv (n:=15) (e:=36) (T.ends 16).1) (.scale (-1) (ev (n:=15) (e:=36) 16)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_20 : ∀j,row_20.coeff j=IndependentCutLP.C023.A 20 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_20 : (0:ℤ)-row_20.constant=IndependentCutLP.C023.B 20 := by decide +kernel
def row_21 : Form 51 := (.plus (nv (n:=15) (e:=36) (T.ends 19).2) (.scale (-1) (ev (n:=15) (e:=36) 19)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_21 : ∀j,row_21.coeff j=IndependentCutLP.C023.A 21 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_21 : (0:ℤ)-row_21.constant=IndependentCutLP.C023.B 21 := by decide +kernel
def row_22 : Form 51 := (.plus (.plus (nv (n:=15) (e:=36) (T.ends 21).1) (nv (n:=15) (e:=36) (T.ends 21).2)) (.scale (-1) (ev (n:=15) (e:=36) 21)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_22 : ∀j,row_22.coeff j=IndependentCutLP.C023.A 22 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_22 : (1:ℤ)-row_22.constant=IndependentCutLP.C023.B 22 := by decide +kernel
def row_23 : Form 51 := (.plus (nv (n:=15) (e:=36) (T.ends 22).2) (.scale (-1) (ev (n:=15) (e:=36) 22)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_23 : ∀j,row_23.coeff j=IndependentCutLP.C023.A 23 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_23 : (0:ℤ)-row_23.constant=IndependentCutLP.C023.B 23 := by decide +kernel
def row_24 : Form 51 := (.plus (.plus (nv (n:=15) (e:=36) (T.ends 23).1) (nv (n:=15) (e:=36) (T.ends 23).2)) (.scale (-1) (ev (n:=15) (e:=36) 23)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_24 : ∀j,row_24.coeff j=IndependentCutLP.C023.A 24 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_24 : (1:ℤ)-row_24.constant=IndependentCutLP.C023.B 24 := by decide +kernel
def row_25 : Form 51 := (.plus (nv (n:=15) (e:=36) (T.ends 26).2) (.scale (-1) (ev (n:=15) (e:=36) 26)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_25 : ∀j,row_25.coeff j=IndependentCutLP.C023.A 25 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_25 : (0:ℤ)-row_25.constant=IndependentCutLP.C023.B 25 := by decide +kernel
def bits_26 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (254048 : ℕ).testBit a.val) (fun x => (254048 : ℕ).testBit (15+x.val))
def row_26 : Form 51 := (.scale (-1) (cutForm T bits_26))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_26 : ∀j,row_26.coeff j=IndependentCutLP.C023.A 26 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_26 : (-26:ℤ)-row_26.constant=IndependentCutLP.C023.B 26 := by decide +kernel
def bits_27 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (189152 : ℕ).testBit a.val) (fun x => (189152 : ℕ).testBit (15+x.val))
def row_27 : Form 51 := (.scale (-1) (cutForm T bits_27))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_27 : ∀j,row_27.coeff j=IndependentCutLP.C023.A 27 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_27 : (-26:ℤ)-row_27.constant=IndependentCutLP.C023.B 27 := by decide +kernel
def bits_28 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (222112 : ℕ).testBit a.val) (fun x => (222112 : ℕ).testBit (15+x.val))
def row_28 : Form 51 := (.scale (-1) (cutForm T bits_28))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_28 : ∀j,row_28.coeff j=IndependentCutLP.C023.A 28 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_28 : (-26:ℤ)-row_28.constant=IndependentCutLP.C023.B 28 := by decide +kernel
def bits_29 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (58328 : ℕ).testBit a.val) (fun x => (58328 : ℕ).testBit (15+x.val))
def row_29 : Form 51 := (.scale (-1) (cutForm T bits_29))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_29 : ∀j,row_29.coeff j=IndependentCutLP.C023.A 29 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_29 : (-26:ℤ)-row_29.constant=IndependentCutLP.C023.B 29 := by decide +kernel
def bits_30 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (56436 : ℕ).testBit a.val) (fun x => (56436 : ℕ).testBit (15+x.val))
def row_30 : Form 51 := (.scale (-1) (cutForm T bits_30))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_30 : ∀j,row_30.coeff j=IndependentCutLP.C023.A 30 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_30 : (-26:ℤ)-row_30.constant=IndependentCutLP.C023.B 30 := by decide +kernel
def bits_31 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (212064 : ℕ).testBit a.val) (fun x => (212064 : ℕ).testBit (15+x.val))
def row_31 : Form 51 := (.scale (-1) (cutForm T bits_31))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_31 : ∀j,row_31.coeff j=IndependentCutLP.C023.A 31 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_31 : (-26:ℤ)-row_31.constant=IndependentCutLP.C023.B 31 := by decide +kernel
def bits_32 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (223584 : ℕ).testBit a.val) (fun x => (223584 : ℕ).testBit (15+x.val))
def row_32 : Form 51 := (.scale (-1) (cutForm T bits_32))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_32 : ∀j,row_32.coeff j=IndependentCutLP.C023.A 32 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_32 : (-26:ℤ)-row_32.constant=IndependentCutLP.C023.B 32 := by decide +kernel
def bits_33 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (128096 : ℕ).testBit a.val) (fun x => (128096 : ℕ).testBit (15+x.val))
def row_33 : Form 51 := (.scale (-1) (cutForm T bits_33))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_33 : ∀j,row_33.coeff j=IndependentCutLP.C023.A 33 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_33 : (-26:ℤ)-row_33.constant=IndependentCutLP.C023.B 33 := by decide +kernel
def bits_34 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (113768 : ℕ).testBit a.val) (fun x => (113768 : ℕ).testBit (15+x.val))
def row_34 : Form 51 := (.scale (-1) (cutForm T bits_34))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_34 : ∀j,row_34.coeff j=IndependentCutLP.C023.A 34 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_34 : (-26:ℤ)-row_34.constant=IndependentCutLP.C023.B 34 := by decide +kernel
def bits_35 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (189348 : ℕ).testBit a.val) (fun x => (189348 : ℕ).testBit (15+x.val))
def row_35 : Form 51 := (.scale (-1) (cutForm T bits_35))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_35 : ∀j,row_35.coeff j=IndependentCutLP.C023.A 35 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_35 : (-26:ℤ)-row_35.constant=IndependentCutLP.C023.B 35 := by decide +kernel
def bits_36 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (72810 : ℕ).testBit a.val) (fun x => (72810 : ℕ).testBit (15+x.val))
def row_36 : Form 51 := (.scale (-1) (cutForm T bits_36))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_36 : ∀j,row_36.coeff j=IndependentCutLP.C023.A 36 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_36 : (-26:ℤ)-row_36.constant=IndependentCutLP.C023.B 36 := by decide +kernel
def bits_37 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (189344 : ℕ).testBit a.val) (fun x => (189344 : ℕ).testBit (15+x.val))
def row_37 : Form 51 := (.scale (-1) (cutForm T bits_37))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_37 : ∀j,row_37.coeff j=IndependentCutLP.C023.A 37 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_37 : (-26:ℤ)-row_37.constant=IndependentCutLP.C023.B 37 := by decide +kernel
def bits_38 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (156550 : ℕ).testBit a.val) (fun x => (156550 : ℕ).testBit (15+x.val))
def row_38 : Form 51 := (.scale (-1) (cutForm T bits_38))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_38 : ∀j,row_38.coeff j=IndependentCutLP.C023.A 38 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_38 : (-26:ℤ)-row_38.constant=IndependentCutLP.C023.B 38 := by decide +kernel
def bits_39 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (58320 : ℕ).testBit a.val) (fun x => (58320 : ℕ).testBit (15+x.val))
def row_39 : Form 51 := (.scale (-1) (cutForm T bits_39))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_39 : ∀j,row_39.coeff j=IndependentCutLP.C023.A 39 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_39 : (-26:ℤ)-row_39.constant=IndependentCutLP.C023.B 39 := by decide +kernel
def bits_40 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (113760 : ℕ).testBit a.val) (fun x => (113760 : ℕ).testBit (15+x.val))
def row_40 : Form 51 := (.scale (-1) (cutForm T bits_40))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_40 : ∀j,row_40.coeff j=IndependentCutLP.C023.A 40 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_40 : (-26:ℤ)-row_40.constant=IndependentCutLP.C023.B 40 := by decide +kernel
def bits_41 : Fin 15 ⊕ Fin 3 → Bool := Sum.elim (fun a => (56432 : ℕ).testBit a.val) (fun x => (56432 : ℕ).testBit (15+x.val))
def row_41 : Form 51 := (.scale (-1) (cutForm T bits_41))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem coeff_41 : ∀j,row_41.coeff j=IndependentCutLP.C023.A 41 j := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem const_41 : (-26:ℤ)-row_41.constant=IndependentCutLP.C023.B 41 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_0 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 0 j*flat N E j) ≤ IndependentCutLP.C023.B 0 := by
  apply of_eval_le row_0 _ _ (22:ℤ) (flat N E) coeff_0 const_0
  have h := S.vertices
  simp only [row_0,eval_vertices]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_1 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 1 j*flat N E j) ≤ IndependentCutLP.C023.B 1 := by
  apply of_eval_le row_1 _ _ (121:ℤ) (flat N E) coeff_1 const_1
  have h := S.edgeHi
  simp only [row_1,eval_m]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_2 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 2 j*flat N E j) ≤ IndependentCutLP.C023.B 2 := by
  apply of_eval_le row_2 _ _ (-1:ℤ) (flat N E) coeff_2 const_2
  have h := S.exists_cycle 0
  simp only [row_2,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_3 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 3 j*flat N E j) ≤ IndependentCutLP.C023.B 3 := by
  apply of_eval_le row_3 _ _ (-1:ℤ) (flat N E) coeff_3 const_3
  have h := S.exists_cycle 2
  simp only [row_3,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_4 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 4 j*flat N E j) ≤ IndependentCutLP.C023.B 4 := by
  apply of_eval_le row_4 _ _ (-1:ℤ) (flat N E) coeff_4 const_4
  have h := S.exists_cycle 3
  simp only [row_4,eval_scale,eval_nv]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_5 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 5 j*flat N E j) ≤ IndependentCutLP.C023.B 5 := by
  apply of_eval_le row_5 _ _ (0:ℤ) (flat N E) coeff_5 const_5
  have h := S.degrees 0
  simp only [row_5,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_6 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 6 j*flat N E j) ≤ IndependentCutLP.C023.B 6 := by
  apply of_eval_le row_6 _ _ (0:ℤ) (flat N E) coeff_6 const_6
  have h := S.degrees 1
  simp only [row_6,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_7 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 7 j*flat N E j) ≤ IndependentCutLP.C023.B 7 := by
  apply of_eval_le row_7 _ _ (0:ℤ) (flat N E) coeff_7 const_7
  have h := S.degrees 2
  simp only [row_7,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_8 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 8 j*flat N E j) ≤ IndependentCutLP.C023.B 8 := by
  apply of_eval_le row_8 _ _ (0:ℤ) (flat N E) coeff_8 const_8
  have h := S.degrees 3
  simp only [row_8,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_9 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 9 j*flat N E j) ≤ IndependentCutLP.C023.B 9 := by
  apply of_eval_le row_9 _ _ (0:ℤ) (flat N E) coeff_9 const_9
  have h := S.degrees 5
  simp only [row_9,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_10 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 10 j*flat N E j) ≤ IndependentCutLP.C023.B 10 := by
  apply of_eval_le row_10 _ _ (0:ℤ) (flat N E) coeff_10 const_10
  have h := S.degrees 7
  simp only [row_10,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_11 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 11 j*flat N E j) ≤ IndependentCutLP.C023.B 11 := by
  apply of_eval_le row_11 _ _ (0:ℤ) (flat N E) coeff_11 const_11
  have h := S.degrees 8
  simp only [row_11,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_12 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 12 j*flat N E j) ≤ IndependentCutLP.C023.B 12 := by
  apply of_eval_le row_12 _ _ (0:ℤ) (flat N E) coeff_12 const_12
  have h := S.degrees 9
  simp only [row_12,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_13 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 13 j*flat N E j) ≤ IndependentCutLP.C023.B 13 := by
  apply of_eval_le row_13 _ _ (0:ℤ) (flat N E) coeff_13 const_13
  have h := S.degrees 10
  simp only [row_13,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_14 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 14 j*flat N E j) ≤ IndependentCutLP.C023.B 14 := by
  apply of_eval_le row_14 _ _ (0:ℤ) (flat N E) coeff_14 const_14
  have h := S.degrees 11
  simp only [row_14,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_15 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 15 j*flat N E j) ≤ IndependentCutLP.C023.B 15 := by
  apply of_eval_le row_15 _ _ (0:ℤ) (flat N E) coeff_15 const_15
  have h := S.degrees 12
  simp only [row_15,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_16 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 16 j*flat N E j) ≤ IndependentCutLP.C023.B 16 := by
  apply of_eval_le row_16 _ _ (0:ℤ) (flat N E) coeff_16 const_16
  have h := S.degrees 13
  simp only [row_16,eval_plus,eval_scale,eval_nv,eval_degree]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_17 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 17 j*flat N E j) ≤ IndependentCutLP.C023.B 17 := by
  apply of_eval_le row_17 _ _ (0:ℤ) (flat N E) coeff_17 const_17
  have h := S.cycle_left 0 1 (by decide +kernel)
  simp only [row_17,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_18 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 18 j*flat N E j) ≤ IndependentCutLP.C023.B 18 := by
  apply of_eval_le row_18 _ _ (1:ℤ) (flat N E) coeff_18 const_18
  have h := S.cycle_both 1 1 0 (by decide +kernel) (by decide +kernel)
  simp only [row_18,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_19 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 19 j*flat N E j) ≤ IndependentCutLP.C023.B 19 := by
  apply of_eval_le row_19 _ _ (0:ℤ) (flat N E) coeff_19 const_19
  have h := S.cycle_left 4 1 (by decide +kernel)
  simp only [row_19,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_20 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 20 j*flat N E j) ≤ IndependentCutLP.C023.B 20 := by
  apply of_eval_le row_20 _ _ (0:ℤ) (flat N E) coeff_20 const_20
  have h := S.cycle_right 16 2 (by decide +kernel)
  simp only [row_20,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_21 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 21 j*flat N E j) ≤ IndependentCutLP.C023.B 21 := by
  apply of_eval_le row_21 _ _ (0:ℤ) (flat N E) coeff_21 const_21
  have h := S.cycle_left 19 3 (by decide +kernel)
  simp only [row_21,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_22 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 22 j*flat N E j) ≤ IndependentCutLP.C023.B 22 := by
  apply of_eval_le row_22 _ _ (1:ℤ) (flat N E) coeff_22 const_22
  have h := S.cycle_both 21 3 2 (by decide +kernel) (by decide +kernel)
  simp only [row_22,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_23 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 23 j*flat N E j) ≤ IndependentCutLP.C023.B 23 := by
  apply of_eval_le row_23 _ _ (0:ℤ) (flat N E) coeff_23 const_23
  have h := S.cycle_left 22 4 (by decide +kernel)
  simp only [row_23,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_24 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 24 j*flat N E j) ≤ IndependentCutLP.C023.B 24 := by
  apply of_eval_le row_24 _ _ (1:ℤ) (flat N E) coeff_24 const_24
  have h := S.cycle_both 23 4 0 (by decide +kernel) (by decide +kernel)
  simp only [row_24,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_25 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 25 j*flat N E j) ≤ IndependentCutLP.C023.B 25 := by
  apply of_eval_le row_25 _ _ (0:ℤ) (flat N E) coeff_25 const_25
  have h := S.cycle_left 26 4 (by decide +kernel)
  simp only [row_25,eval_plus,eval_scale,eval_nv,eval_ev]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_26 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 26 j*flat N E j) ≤ IndependentCutLP.C023.B 26 := by
  apply of_eval_le row_26 _ _ (-26:ℤ) (flat N E) coeff_26 const_26
  have h := S.cuts bits_26
  simp only [row_26,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_27 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 27 j*flat N E j) ≤ IndependentCutLP.C023.B 27 := by
  apply of_eval_le row_27 _ _ (-26:ℤ) (flat N E) coeff_27 const_27
  have h := S.cuts bits_27
  simp only [row_27,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_28 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 28 j*flat N E j) ≤ IndependentCutLP.C023.B 28 := by
  apply of_eval_le row_28 _ _ (-26:ℤ) (flat N E) coeff_28 const_28
  have h := S.cuts bits_28
  simp only [row_28,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_29 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 29 j*flat N E j) ≤ IndependentCutLP.C023.B 29 := by
  apply of_eval_le row_29 _ _ (-26:ℤ) (flat N E) coeff_29 const_29
  have h := S.cuts bits_29
  simp only [row_29,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_30 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 30 j*flat N E j) ≤ IndependentCutLP.C023.B 30 := by
  apply of_eval_le row_30 _ _ (-26:ℤ) (flat N E) coeff_30 const_30
  have h := S.cuts bits_30
  simp only [row_30,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_31 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 31 j*flat N E j) ≤ IndependentCutLP.C023.B 31 := by
  apply of_eval_le row_31 _ _ (-26:ℤ) (flat N E) coeff_31 const_31
  have h := S.cuts bits_31
  simp only [row_31,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_32 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 32 j*flat N E j) ≤ IndependentCutLP.C023.B 32 := by
  apply of_eval_le row_32 _ _ (-26:ℤ) (flat N E) coeff_32 const_32
  have h := S.cuts bits_32
  simp only [row_32,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_33 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 33 j*flat N E j) ≤ IndependentCutLP.C023.B 33 := by
  apply of_eval_le row_33 _ _ (-26:ℤ) (flat N E) coeff_33 const_33
  have h := S.cuts bits_33
  simp only [row_33,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_34 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 34 j*flat N E j) ≤ IndependentCutLP.C023.B 34 := by
  apply of_eval_le row_34 _ _ (-26:ℤ) (flat N E) coeff_34 const_34
  have h := S.cuts bits_34
  simp only [row_34,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_35 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 35 j*flat N E j) ≤ IndependentCutLP.C023.B 35 := by
  apply of_eval_le row_35 _ _ (-26:ℤ) (flat N E) coeff_35 const_35
  have h := S.cuts bits_35
  simp only [row_35,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_36 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 36 j*flat N E j) ≤ IndependentCutLP.C023.B 36 := by
  apply of_eval_le row_36 _ _ (-26:ℤ) (flat N E) coeff_36 const_36
  have h := S.cuts bits_36
  simp only [row_36,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_37 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 37 j*flat N E j) ≤ IndependentCutLP.C023.B 37 := by
  apply of_eval_le row_37 _ _ (-26:ℤ) (flat N E) coeff_37 const_37
  have h := S.cuts bits_37
  simp only [row_37,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_38 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 38 j*flat N E j) ≤ IndependentCutLP.C023.B 38 := by
  apply of_eval_le row_38 _ _ (-26:ℤ) (flat N E) coeff_38 const_38
  have h := S.cuts bits_38
  simp only [row_38,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_39 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 39 j*flat N E j) ≤ IndependentCutLP.C023.B 39 := by
  apply of_eval_le row_39 _ _ (-26:ℤ) (flat N E) coeff_39 const_39
  have h := S.cuts bits_39
  simp only [row_39,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_40 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 40 j*flat N E j) ≤ IndependentCutLP.C023.B 40 := by
  apply of_eval_le row_40 _ _ (-26:ℤ) (flat N E) coeff_40 const_40
  have h := S.cuts bits_40
  simp only [row_40,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem valid_41 (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) :
    (∑j,IndependentCutLP.C023.A 41 j*flat N E j) ≤ IndependentCutLP.C023.B 41 := by
  apply of_eval_le row_41 _ _ (-26:ℤ) (flat N E) coeff_41 const_41
  have h := S.cuts bits_41
  simp only [row_41,eval_scale,eval_cut]
  omega
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem impossible (N : Fin 15 → ℤ) (E : Fin 36 → ℤ) (S : Feasible T N E 12 121) : False := by
  apply IndependentCutLP.C023.impossible (flat N E)
  · intro j
    refine Fin.addCases (m:=15) (n:=36) (fun a => ?_) (fun k => ?_) j
    · simpa [flat] using S.npos a
    · simpa [flat] using S.epos k
  · intro i
    fin_cases i
    · exact valid_0 N E S
    · exact valid_1 N E S
    · exact valid_2 N E S
    · exact valid_3 N E S
    · exact valid_4 N E S
    · exact valid_5 N E S
    · exact valid_6 N E S
    · exact valid_7 N E S
    · exact valid_8 N E S
    · exact valid_9 N E S
    · exact valid_10 N E S
    · exact valid_11 N E S
    · exact valid_12 N E S
    · exact valid_13 N E S
    · exact valid_14 N E S
    · exact valid_15 N E S
    · exact valid_16 N E S
    · exact valid_17 N E S
    · exact valid_18 N E S
    · exact valid_19 N E S
    · exact valid_20 N E S
    · exact valid_21 N E S
    · exact valid_22 N E S
    · exact valid_23 N E S
    · exact valid_24 N E S
    · exact valid_25 N E S
    · exact valid_26 N E S
    · exact valid_27 N E S
    · exact valid_28 N E S
    · exact valid_29 N E S
    · exact valid_30 N E S
    · exact valid_31 N E S
    · exact valid_32 N E S
    · exact valid_33 N E S
    · exact valid_34 N E S
    · exact valid_35 N E S
    · exact valid_36 N E S
    · exact valid_37 N E S
    · exact valid_38 N E S
    · exact valid_39 N E S
    · exact valid_40 N E S
    · exact valid_41 N E S
end FastCutCase.C023

-- ParentFacts

namespace ErdosPathFacts
open scoped Classical
open Finset SimpleGraph ThreeExceptions GraphMass

noncomputable def nd (G : SimpleGraph (Fin 25)) (a : Fin 25) : ℕ := by
  classical
  exact ∑b,if G.Adj a b then 1 else 0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cast_degree (G : SimpleGraph (Fin 25)) (a : Fin 25) : (nd G a:ℤ)=deg G a := by
  classical
  simp [nd,deg,W]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem nd_degree (G : SimpleGraph (Fin 25)) (a : Fin 25) : nd G a=G.degree a := by
  classical
  simp [nd,←G.card_neighborFinset_eq_degree,neighborFinset_eq_filter,Finset.sum_boole]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem total (G : SimpleGraph (Fin 25)) :
    (∑a,∑b,W G (a,b))=2*(G.edgeFinset.card:ℤ) := by
  classical
  have hn : (∑a,nd G a)=2*G.edgeFinset.card := by
    simpa only [nd_degree] using G.sum_degrees_eq_twice_card_edges
  have hi : (∑a,deg G a)=2*(G.edgeFinset.card:ℤ) := by
    simp_rw [←cast_degree]
    exact_mod_cast hn
  simpa only [deg] using hi

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem maximum_twelve (G : SimpleGraph (Fin 25))
    (large : ∀a,13 ≤ G.degree a →
      ∃f:Fin 25→Bool,(∑x,∑y,if G.Adj x y∧f x=f y then (1:ℕ) else 0) ≤ 50)
    (bad : ∀f:Fin 25→Bool,50<∑a,∑b,if G.Adj a b∧f a=f b then (1:ℕ) else 0) :
    ∀a,deg G a ≤ 12 := by
  classical
  intro a
  have cap : G.degree a ≤ 12 := by
    by_contra h
    obtain ⟨f,hf⟩ := large a (by omega)
    exact (not_lt_of_ge hf) (bad f)
  rw [←cast_degree,nd_degree]
  exact_mod_cast cap

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem roots (G : SimpleGraph (Fin 25))
    (h : ∀a,2*(∑b,(if G.Adj a b then (1:ℕ) else 0)*nd G b)+51 ≤ 2*G.edgeFinset.card) :
    ∀a,(∑b,W G (a,b)*deg G b) ≤ (G.edgeFinset.card:ℤ)-26 := by
  classical
  intro a
  have hn : (∑b,(if G.Adj a b then (1:ℕ) else 0)*nd G b)+26 ≤ G.edgeFinset.card := by
    have hh := h a
    omega
  have hi : ((∑b,(if G.Adj a b then (1:ℕ) else 0)*nd G b):ℤ)+26 ≤ (G.edgeFinset.card:ℤ) := by
    exact_mod_cast hn
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,cast_degree] at hi
  change (∑b,W G (a,b)*deg G b)+26 ≤ (G.edgeFinset.card:ℤ) at hi
  omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem maximum_eleven (G : SimpleGraph (Fin 25))
    (root : ∀a,(∑b,W G (a,b)*deg G b) ≤ (G.edgeFinset.card:ℤ)-26)
    (dense : 118 ≤ G.edgeFinset.card) : ∀a,deg G a ≤ 11 := by
  classical
  apply CutDegree.maximum_eleven (deg G) (fun a b => W G (a,b)) (G.edgeFinset.card:ℤ)
  · exact W_sym G
  · intro a
    simp [W]
  · intro a b
    by_cases h : G.Adj a b <;> simp [W,h]
  · intro a
    rfl
  · simpa only [deg] using total G
  · exact root
  · exact_mod_cast dense

end ErdosPathFacts

-- CastBounds
namespace ErdosPathCasts
open scoped Classical
open Finset SimpleGraph GraphMass ErdosPathFacts

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem upper (m k : ℕ) (h : m  ≤  k) : (m:ℤ)  ≤  (k:ℤ) := by exact_mod_cast h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem cut (G : SimpleGraph (Fin 25)) (f : Fin 25 → Bool)
    (h : 50<∑a,∑b,if G.Adj a b∧f a=f b then (1:ℕ) else 0) :
    51  ≤  ∑a,∑b,if G.Adj a b∧f a=f b then (1:ℤ) else 0 := by
  have hn : 51  ≤  ∑a,∑b,if G.Adj a b∧f a=f b then (1:ℕ) else 0 := by omega
  exact_mod_cast hn

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem repair (G : SimpleGraph (Fin 25)) (m : ℕ) (r : Fin 25) (c : Fin 25 → Fin 5)
    (h : 130  ≤  m+∑a,∑z,if G.Adj a z∧a≠r∧z≠r∧¬ThreeExceptions.Near (c a) (c z) then (1:ℕ) else 0) :
    130  ≤  (m:ℤ)+(∑a,∑z,if G.Adj a z∧a≠r∧z≠r∧¬ThreeExceptions.Near (c a) (c z) then (1:ℤ) else 0) := by
  exact_mod_cast h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem obstruction (G : SimpleGraph (Fin 25)) (m : ℕ) (a b : Fin 25)
    (h : 134  ≤  m+nd G a+nd G b) : 134  ≤  (m:ℤ)+deg G a+deg G b := by
  rw [←cast_degree,←cast_degree]
  exact_mod_cast h
end ErdosPathCasts

-- Assembly

namespace ErdosPathProof
open Finset SimpleGraph ThreeExceptions FiniteCutTemplate GraphMass CutSummary ErdosPathFacts
open OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R3

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem assemble
    (case011 : ∀(N : Fin 17 → ℤ)(E : Fin 46 → ℤ),Feasible NativeCutTemplate.C011.table N E 12 121 → False)
    (case012 : ∀(N : Fin 15 → ℤ)(E : Fin 40 → ℤ),Feasible NativeCutTemplate.C012.table N E 12 121 → False)
    (case013 : ∀(N : Fin 16 → ℤ)(E : Fin 41 → ℤ),Feasible NativeCutTemplate.C013.table N E 12 121 → False)
    (case014 : ∀(N : Fin 16 → ℤ)(E : Fin 44 → ℤ),Feasible NativeCutTemplate.C014.table N E 12 121 → False)
    (case022low : ∀(N : Fin 17 → ℤ)(E : Fin 40 → ℤ),Feasible NativeCutTemplate.C022.table N E 12 117 → False)
    (case022high : ∀(N : Fin 17 → ℤ)(E : Fin 40 → ℤ),Feasible NativeCutTemplate.C022.table N E 11 121 → False)
    (case023 : ∀(N : Fin 15 → ℤ)(E : Fin 36 → ℤ),Feasible NativeCutTemplate.C023.table N E 12 121 → False)
    : OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R3.H3 := by
  classical
  intro G tri w d m _lo upper _nomap rooted _bip _edgecap _pairmap v cyc dom X repair p q r Xeq pq rp rq miss rpadj _dense obstruction
  by_contra bad0
  have bad : ∀f:Fin 25→Bool,50<∑a,∑b,if G.Adj a b∧f a=f b then (1:ℕ) else 0 := by
    simpa only [not_exists,not_le] using bad0
  have triangle (a b c) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False :=
    tri {a,b,c} (is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)
  have cov (a) (h : ∃!i,G.Adj a (v i)) : a=p ∨ a=q ∨ a=r := by
    have ha : a∈X := by simpa only [X,mem_filter,mem_univ,true_and] using h
    simpa only [Xeq,mem_insert,mem_singleton] using ha
  have other : 134  ≤  m+d p+d r := by
    have h := (triple_obstruction G tri bad v cyc dom p r q rpadj.symm
      (G.ne_of_adj pq).symm rq.symm (fun h => miss h.symm)
      (fun a ha => by rcases cov a ha with h|h|h; exact Or.inl h; exact Or.inr (Or.inr h); exact Or.inr (Or.inl h))).2.2
    simpa only [if_pos pq.symm,show 130+(4:ℕ)=134 by decide] using h
  let ex : Fin 3 → Fin 25 := ![p,q,r]
  have exinj : Function.Injective ex := by
    intro a b h
    have hpq := G.ne_of_adj pq
    fin_cases a <;> fin_cases b
    all_goals first
      | rfl
      | exact False.elim (hpq h)
      | exact False.elim (hpq h.symm)
      | exact False.elim (rp h)
      | exact False.elim (rp h.symm)
      | exact False.elim (rq h)
      | exact False.elim (rq h.symm)
  have exedge : ∀x y,G.Adj (ex x) (ex y) ↔ x≠y∧(x=0∨y=0) := by
    intro x y
    have miss' : ¬G.Adj q r := fun h => miss h.symm
    fin_cases x <;> fin_cases y <;> simp [ex,pq,pq.symm,rpadj,rpadj.symm,miss,miss'] <;> decide +kernel
  have member (x : Fin 3) : ex x∈X := by
    rw [Xeq]
    fin_cases x <;> simp [ex]
  have unique (x : Fin 3) : ∃!i,G.Adj (ex x) (v i) := by
    have h := member x
    simpa only [X,mem_filter,mem_univ,true_and] using h
  choose t ht hu using unique
  have single (x : Fin 3) (i : Fin 5) : G.Adj (ex x) (v i) ↔ i=t x :=
    ⟨fun h => hu x i h,fun h => by simpa only [h] using ht x⟩
  have t01 : t 0≠t 1 := by
    intro h
    exact triangle _ _ _ ((exedge 0 1).mpr (by decide)) (ht 0) ((single 1 _).mpr h)
  have t02 : t 0≠t 2 := by
    intro h
    exact triangle _ _ _ ((exedge 0 2).mpr (by decide)) (ht 0) ((single 2 _).mpr h)
  obtain ⟨s,k,b,heq⟩ := CutCanonical.classify t t01 t02
  obtain ⟨newcyc,newdom,newsingle,newedge,uniques⟩ :=
    CutCanonical.change_frame G ex v t cyc dom single exedge s k b heq
  let ex' : Fin 3 → Fin 25 := fun x => ex (CutCanonical.swap b x)
  let v' : Fin 5 → Fin 25 := fun i => v (CutCanonical.turn s i)
  have exinj' : Function.Injective ex' := exinj.comp (CutCanonical.swap_injective b)
  have noUnique (a) (ha : ¬∃x,a=ex' x) : ¬∃!i,G.Adj a (v' i) := by
    intro h
    have old := (uniques a).mp h
    have arange : ∃x,a=ex x := by
      rcases cov a old with hp|hq|hr
      · exact ⟨0,hp⟩
      · exact ⟨1,hq⟩
      · exact ⟨2,hr⟩
    obtain ⟨x,hx⟩ := arange
    obtain ⟨y,hy⟩ := Finite.surjective_of_injective (CutCanonical.swap_injective b) x
    apply ha
    exact ⟨y,by simpa only [ex',hy] using hx⟩
  obtain ⟨g,prof,maps⟩ := pentagon_profiles G tri v' newcyc newdom
  have profile (a) (ha : ¬∃x,a=ex' x) (i) : G.Adj a (v' i) ↔ Near (g a) i :=
    prof a (noUnique a ha) i
  have mapped (a) (ha : ¬∃x,a=ex' x) (c) (hc : ¬∃x,c=ex' x) (hac : G.Adj a c) : Near (g a) (g c) :=
    maps a (noUnique a ha) c (noUnique c hc) hac
  let M : ℤ := m
  have cap12 : ∀a,deg G a  ≤  12 := maximum_twelve G (degree_at_least_thirteen G tri) bad
  have rt : ∀a,(∑c,W G (a,c)*deg G c)  ≤  M-26 := roots G rooted
  have count : (∑a,∑c,W G (a,c))=2*M := total G
  have up : M  ≤  121 := ErdosPathCasts.upper m 121 upper
  have badInt (f : Fin 25 → Bool) : 51  ≤  ∑a,∑c,if G.Adj a c∧f a=f c then (1:ℤ) else 0 := by
    exact ErdosPathCasts.cut G f (bad f)
  have repairInt (x : Fin 3) (c : Fin 25 → Fin 5)
      (proper : ∀a,a≠ex' x→∀z,z≠ex' x→G.Adj a z→c a≠c z) :
      130  ≤  M+(∑a,∑z,if G.Adj a z∧a≠ex' x∧z≠ex' x∧¬Near (c a) (c z) then (1:ℤ) else 0) := by
    have h := repair (ex' x) (member (CutCanonical.swap b x)) c proper
    exact ErdosPathCasts.repair G m (ex' x) c h
  have ob : 134  ≤  M+deg G (ex' 0)+deg G (ex' 2) := by
    rcases CutCanonical.swap_nonzero b with h|h
    · simp only [ex',CutCanonical.swap_zero,h] 
      change 134  ≤  M+deg G p+deg G q
      exact ErdosPathCasts.obstruction G m p q obstruction
    · simp only [ex',CutCanonical.swap_zero,h]
      change 134  ≤  M+deg G p+deg G r
      exact ErdosPathCasts.obstruction G m p r other
  have models (n e : ℕ) (T : Table (CutCanonical.types k) n e) (cap hi : ℤ)
      (hc : ∀a,deg G a  ≤  cap) (hm : M  ≤  hi) :
      ∃N E,Feasible T N E cap hi := by
    let S := represent G ex' exinj' g v' T triangle newedge newsingle profile mapped newcyc
    exact ⟨N S,E S,feasible S M cap hi (by rfl) count hc hm badInt repairInt rt ob⟩
  fin_cases k
  · obtain ⟨N,E,S⟩ := models 17 46 NativeCutTemplate.C011.table 12 121 cap12 up
    exact case011 N E S
  · obtain ⟨N,E,S⟩ := models 15 40 NativeCutTemplate.C012.table 12 121 cap12 up
    exact case012 N E S
  · obtain ⟨N,E,S⟩ := models 16 41 NativeCutTemplate.C013.table 12 121 cap12 up
    exact case013 N E S
  · obtain ⟨N,E,S⟩ := models 16 44 NativeCutTemplate.C014.table 12 121 cap12 up
    exact case014 N E S
  · by_cases low : m  ≤  117
    · obtain ⟨N,E,S⟩ := models 17 40 NativeCutTemplate.C022.table 12 117 cap12 (ErdosPathCasts.upper m 117 low)
      exact case022low N E S
    · have dense : 118  ≤  G.edgeFinset.card := by omega
      obtain ⟨N,E,S⟩ := models 17 40 NativeCutTemplate.C022.table 11 121 (maximum_eleven G rt dense) up
      exact case022high N E S
  · obtain ⟨N,E,S⟩ := models 15 36 NativeCutTemplate.C023.table 12 121 cap12 up
    exact case023 N E S

end ErdosPathProof

-- MainProof

namespace ErdosPathProof
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem solution : OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R3.H3 :=
  assemble
    FastCutCase.C011.impossible
    FastCutCase.C012.impossible
    FastCutCase.C013.impossible
    FastCutCase.C014.impossible
    FastCutCase.C022low.impossible
    FastCutCase.C022high.impossible
    FastCutCase.C023.impossible
end ErdosPathProof

theorem OMA.solution : OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R3.H3 :=
  ErdosPathProof.solution
