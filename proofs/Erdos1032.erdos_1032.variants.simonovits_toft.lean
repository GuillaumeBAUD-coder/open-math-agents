import FormalConjectures.ErdosProblems.«1032»

/-! Simonovits and Toft proved the cubic-root bound for the minimum degree of
4-critical graphs (1972). The construction here uses an odd circuit split into
odd-length blocks and a further group of their starting vertices. Every proper
tricoloring uses all three colors on at least one group. Conversely a prescribed
group can be made the unique such group, with a prescribed vertex carrying its
exceptional color. Two copies joined by complete bipartite gadgets are therefore
not tricolorable. The exceptional colorings certify that deleting any gadget
edge allows three colors; these edges ensure a large degree at every vertex.
The odd-block and complete-bipartite ideas are from M. Simonovits, "On
colour-critical graphs", Studia Sci. Math. Hungar. 7 (1972). -/

namespace OMA.Toft1032

open SimpleGraph

abbrev C := Fin 3

structure Palette (X I J : Type) where
  base : SimpleGraph X
  group : I → J → X
  hits : ∀ c : base.Coloring C, ∃ i, Function.Surjective (fun j => c (group i j))
  focus : ∀ i j, ∃ c : base.Coloring C, c (group i j) = 0 ∧
    (∀ l, l ≠ j → c (group i l) ≠ 0) ∧
    ∀ k, k ≠ i → ∃ a, ∀ l, c (group k l) ≠ a

abbrev Side (X I J : Type) := X ⊕ (I × I × J)
abbrev V (X I J : Type) := Side X I J ⊕ Side X I J
variable {X I J : Type} (P : Palette X I J)

abbrev left (x : X) : V X I J := .inl (.inl x)
abbrev right (x : X) : V X I J := .inr (.inl x)
abbrev L (i k : I) (j : J) : V X I J := .inl (.inr (i,k,j))
abbrev R (i k : I) (l : J) : V X I J := .inr (.inr (i,k,l))

inductive Arrow (baseEdges : Bool) : V X I J → V X I J → Prop
  | baseL {x y} : baseEdges = true → P.base.Adj x y → Arrow baseEdges (left x) (left y)
  | baseR {x y} : baseEdges = true → P.base.Adj x y → Arrow baseEdges (right x) (right y)
  | matchL (i k j) : Arrow baseEdges (left (P.group i j)) (L i k j)
  | matchR (i k l) : Arrow baseEdges (right (P.group k l)) (R i k l)
  | cross (i k j l) : Arrow baseEdges (L i k j) (R i k l)

def graph (b : Bool) : SimpleGraph (V X I J) := SimpleGraph.fromRel (Arrow P b)

lemma arrow_adj {b x y} (h : Arrow P b x y) : (graph P b).Adj x y := by
  refine ⟨?_,Or.inl h⟩
  cases h with
  | baseL _ h => exact fun he => h.ne (Sum.inl.inj (Sum.inl.inj he))
  | baseR _ h => exact fun he => h.ne (Sum.inl.inj (Sum.inr.inj he))
  | matchL => simp
  | matchR => simp
  | cross => simp

lemma graph_mono : graph P false ≤ graph P true := by
  have aux {x y} (h : Arrow P false x y) : Arrow P true x y := by
    cases h with
    | baseL h => cases h
    | baseR h => cases h
    | matchL => constructor
    | matchR => constructor
    | cross => constructor
  intro x y h
  exact ⟨h.1,h.2.imp aux aux⟩

lemma missing_of_adjacent_ranges (f g : J → C) (h : ∀ j l, f j ≠ g l) :
    (∃ a, ∀ j, f j = a) ∨ (∃ a, ∀ l, g l = a) := by
  classical
  by_contra! hn
  obtain ⟨j0,hj0⟩ := hn.1 0
  obtain ⟨j1,hj1⟩ := hn.1 (f j0)
  obtain ⟨l0,hl0⟩ := hn.2 0
  obtain ⟨l1,hl1⟩ := hn.2 (g l0)
  have h00 := h j0 l0
  have h01 := h j0 l1
  have h10 := h j1 l0
  have h11 := h j1 l1
  exact (show ∀ a b c d : C, b ≠ a → d ≠ c → a ≠ c → a ≠ d → b ≠ c → b ≠ d → False
    by decide) _ _ _ _ hj1 hl1 h00 h01 h10 h11

lemma not_colorable : ¬(graph P true).Colorable 3 := by
  rintro ⟨c⟩
  let lc : P.base.Coloring C := Coloring.mk (fun x => c (left x))
    (fun h => c.valid (arrow_adj P (.baseL rfl h)))
  let rc : P.base.Coloring C := Coloring.mk (fun x => c (right x))
    (fun h => c.valid (arrow_adj P (.baseR rfl h)))
  obtain ⟨i,hi⟩ := P.hits lc
  obtain ⟨k,hk⟩ := P.hits rc
  rcases missing_of_adjacent_ranges (fun j => c (L i k j)) (fun l => c (R i k l))
    (fun j l => c.valid (arrow_adj P (.cross i k j l))) with ⟨a,ha⟩ | ⟨a,ha⟩
  · obtain ⟨j,hj⟩ := hi a
    exact c.valid (arrow_adj P (.matchL i k j)) (hj.trans (ha j).symm)
  · obtain ⟨l,hl⟩ := hk a
    exact c.valid (arrow_adj P (.matchR i k l)) (hl.trans (ha l).symm)

lemma exists_other (a b : C) : ∃ c : C, c ≠ a ∧ c ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

/-- One non-rainbow group suffices to extend the coloring across its complete bipartite gadget. -/
lemma ordinary (f g : J → C) (h : (∃ a, ∀ j, f j ≠ a) ∨ (∃ a, ∀ l, g l ≠ a)) :
    ∃ p q : J → C, (∀ j, f j ≠ p j) ∧ (∀ l, g l ≠ q l) ∧ ∀ j l, p j ≠ q l := by
  classical
  rcases h with ⟨a,ha⟩ | ⟨a,ha⟩
  · choose q hq using fun l => exists_other (g l) a
    exact ⟨fun _ => a,q,ha,fun l => (hq l).1.symm,fun _ l => (hq l).2.symm⟩
  · choose p hp using fun j => exists_other (f j) a
    exact ⟨p,fun _ => a,fun j => (hp j).1.symm,ha,fun j _ => (hp j).2⟩

def cutEdge (i k : I) (j l : J) (d : C) : Sym2 (V X I J) :=
  if d = 0 then s(L i k j,R i k l)
  else if d = 1 then s(left (P.group i j),L i k j)
  else s(right (P.group k l),R i k l)

def Allows (i k : I) (f g : J → C) (e : Sym2 (V X I J)) (p q : J → C) : Prop :=
  (∀ j, f j = p j → s(left (P.group i j),L i k j) = e) ∧
  (∀ l, g l = q l → s(right (P.group k l),R i k l) = e) ∧
  ∀ j l, p j = q l → s(L i k j,R i k l) = e

lemma marked (i k : I) (j l : J) (d : C) (f g : J → C)
    (hf : f j = 0) (hg : g l = 1) (hf' : ∀ t, t ≠ j → f t ≠ 0)
    (hg' : ∀ t, t ≠ l → g t ≠ 1) :
    ∃ p q, Allows P i k f g (cutEdge P i k j l d) p q := by
  classical
  let p (t : J) : C := if t = j ∧ d ≠ 1 then 2 else 0
  let q (t : J) : C := if t = l ∧ d ≠ 2 then 2 else 1
  refine ⟨p,q,?_,?_,?_⟩
  · intro t eq
    by_cases h : t = j
    · subst t
      fin_cases d <;> simp_all [p,cutEdge]
    · exact (hf' t h (by simpa [p,h] using eq)).elim
  · intro t eq
    by_cases h : t = l
    · subst t
      fin_cases d <;> simp_all [q,cutEdge]
    · exact (hg' t h (by simpa [q,h] using eq)).elim
  · intro u v eq
    by_cases hu : u = j <;> by_cases hv : v = l <;> fin_cases d <;>
      simp_all [p,q,cutEdge]

lemma cut_colorable (i k : I) (j l : J) (d : C) :
    ((graph P true).deleteEdges {cutEdge P i k j l d}).Colorable 3 := by
  classical
  obtain ⟨f, hf, hf', hfo⟩ := P.focus i j
  obtain ⟨g₀, hg₀, hg₀', hgo₀⟩ := P.focus k l
  let σ : C ≃ C := Equiv.swap 0 1
  let g : P.base.Coloring C := Coloring.mk (σ ∘ g₀) (fun h he => g₀.valid h (σ.injective he))
  have hg : g (P.group k l) = 1 := by change σ (g₀ _) = _; simp [hg₀,σ]
  have hg' (t : J) (ht : t ≠ l) : g (P.group k t) ≠ 1 := by
    intro h
    change σ (g₀ (P.group k t)) = 1 at h
    exact hg₀' t ht (σ.injective (show σ (g₀ _) = σ 0 by simpa [σ] using h))
  let e := cutEdge P i k j l d
  have extend (a b : I) : ∃ p q,
      Allows P a b (fun t => f (P.group a t)) (fun t => g (P.group b t)) e p q := by
    by_cases hb : a = i ∧ b = k
    · obtain ⟨rfl,rfl⟩ := hb
      exact marked P _ _ _ _ _ _ _ hf hg hf' hg'
    · have none : (∃ z, ∀ t, f (P.group a t) ≠ z) ∨ (∃ z, ∀ t, g (P.group b t) ≠ z) := by
        by_cases ha : a = i
        · obtain ⟨z,hz⟩ := hgo₀ b (fun h => hb ⟨ha,h⟩)
          exact Or.inr ⟨σ z,fun t h => hz t (σ.injective h)⟩
        · exact Or.inl (hfo a ha)
      obtain ⟨p,q,hl,hr,hpq⟩ := ordinary _ _ none
      exact ⟨p,q,fun t h => (hl t h).elim,fun t h => (hr t h).elim,
        fun t u h => (hpq t u h).elim⟩
  choose p q hpq using extend
  let c : V X I J → C
    | .inl (.inl x) => f x
    | .inr (.inl x) => g x
    | .inl (.inr (a,b,t)) => p a b t
    | .inr (.inr (a,b,t)) => q a b t
  have single {x y} (h : Arrow P true x y) (hc : c x = c y) : s(x,y) = e := by
    cases h with
    | baseL _ h => exact (f.valid h hc).elim
    | baseR _ h => exact (g.valid h hc).elim
    | matchL a b t => exact (hpq a b).1 t hc
    | matchR a b t => exact (hpq a b).2.1 t hc
    | cross a b t u => exact (hpq a b).2.2 t u hc
  refine ⟨Coloring.mk c (fun {x y} h hc => ?_)⟩
  obtain ⟨ha,he⟩ := SimpleGraph.deleteEdges_adj.mp h
  rcases ha.2 with h | h
  · exact he (single h hc)
  · exact he (Sym2.eq_swap.trans (single h hc.symm))

lemma forced_edges [Nonempty J] (e : Sym2 (V X I J)) (he : e ∈ (graph P false).edgeSet) :
    ((graph P true).deleteEdges {e}).Colorable 3 := by
  classical
  let j₀ : J := Classical.choice inferInstance
  have del {x y} (h : Arrow P false x y) :
      ((graph P true).deleteEdges {s(x,y)}).Colorable 3 := by
    cases h with
    | baseL h => cases h
    | baseR h => cases h
    | matchL a b t => exact cut_colorable P a b t j₀ 1
    | matchR a b u => exact cut_colorable P a b j₀ u 2
    | cross a b t u => exact cut_colorable P a b t u 0
  induction e using Sym2.inductionOn with
  | _ x y =>
    rcases (show (graph P false).Adj x y from he).2 with h | h
    · exact del h
    · rw [Sym2.eq_swap]
      exact del h

lemma degree_bound [Fintype X] [Fintype I] [Fintype J]
    (hIJ : Fintype.card J ≤ Fintype.card I) (cover : ∀ x, ∃ i j, P.group i j = x)
    (v : V X I J) :
    letI := Classical.decRel (graph P false).Adj
    Fintype.card J ≤ (graph P false).degree v := by
  classical
  rw [← card_neighborSet_eq_degree]
  rcases v with (x | ⟨i,k,j⟩) | (x | ⟨i,k,l⟩)
  · obtain ⟨i,j,rfl⟩ := cover x
    exact hIJ.trans (Fintype.card_le_of_injective
      (fun k : I => (⟨L i k j,arrow_adj P (.matchL i k j)⟩ : (graph P false).neighborSet _))
      (fun _ _ h => (Prod.mk.inj (Prod.mk.inj (Sum.inr.inj (Sum.inl.inj (congrArg Subtype.val h)))).2).1))
  · exact Fintype.card_le_of_injective
      (fun l : J => (⟨R i k l,arrow_adj P (.cross i k j l)⟩ : (graph P false).neighborSet _))
      (fun _ _ h => (Prod.mk.inj (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj (congrArg Subtype.val h)))).2).2)
  · obtain ⟨k,l,rfl⟩ := cover x
    exact hIJ.trans (Fintype.card_le_of_injective
      (fun i : I => (⟨R i k l,arrow_adj P (.matchR i k l)⟩ : (graph P false).neighborSet _))
      (fun _ _ h => (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj (congrArg Subtype.val h)))).1))
  · exact Fintype.card_le_of_injective
      (fun j : J => (⟨L i k j,(arrow_adj P (.cross i k j l)).symm⟩ : (graph P false).neighborSet _))
      (fun _ _ h => (Prod.mk.inj (Prod.mk.inj (Sum.inr.inj (Sum.inl.inj (congrArg Subtype.val h)))).2).2)

end OMA.Toft1032

namespace OMA.Toft1032

abbrev size (t : ℕ) := 2*t+3
abbrev A (t : ℕ) := Fin (size t)
abbrev Pt (t : ℕ) := A t × A t

def rotate {t} (i : A t) : A t :=
  if h : i.val+1 < size t then ⟨i.val+1,h⟩ else 0

lemma rotate_step {t} (i : A t) :
    (rotate i).val = i.val+1 ∨ (i.val+1 = size t ∧ (rotate i).val = 0) := by
  have := i.isLt
  unfold rotate
  split <;> simp_all [size]
  omega

def baseStep {t} (x y : Pt t) : Prop :=
  (x.1 = y.1 ∧ x.2.val+1 = y.2.val) ∨
    (x.2.val+1 = size t ∧ y.2.val = 0 ∧ y.1 = rotate x.1)

def baseCycle (t : ℕ) := SimpleGraph.fromRel (@baseStep t)

lemma step_adj {t} {x y : Pt t} (h : baseStep x y) : (baseCycle t).Adj x y := by
  refine ⟨?_,Or.inl h⟩
  rintro rfl
  rcases h with ⟨_,hy⟩ | ⟨he,hz,_⟩ <;> unfold size at * <;> omega

def mkColor {t} (f : Pt t → C) (h : ∀ x y, baseStep x y → f x ≠ f y) :
    (baseCycle t).Coloring C :=
  SimpleGraph.Coloring.mk f (fun a => a.2.elim (h _ _) (fun e => (h _ _ e).symm))

def atGroup {t} : Option (A t) → A t → Pt t
  | none, i => (i,0)
  | some i, j => (i,j)

lemma even_path {t} (c : A t → C) (z : C) (hz : ∀ j, c j ≠ z)
    (hs : ∀ a b : A t, a.val+1 = b.val → c a ≠ c b)
    (k : ℕ) (hk : 2*k < size t) : c ⟨2*k,hk⟩ = c 0 := by
  have rule : ∀ a b d o : C, a ≠ b → b ≠ d → a ≠ o → b ≠ o → d ≠ o → a = d := by decide
  induction k with
  | zero => rfl
  | succ k ih =>
    let a : A t := ⟨2*k,by omega⟩
    let b : A t := ⟨2*k+1,by omega⟩
    let d : A t := ⟨2*(k+1),hk⟩
    have heq := rule (c d) (c b) (c a) z (hs b d (by dsimp [b,d]; omega)).symm
      (hs a b rfl).symm (hz _) (hz _) (hz _)
    exact heq.trans (ih a.isLt)

lemma base_hits (t) (c : (baseCycle t).Coloring C) :
    ∃ i, Function.Surjective (fun j => c (atGroup i j)) := by
  classical
  by_contra! contra
  have miss (i : Option (A t)) : ∃ z, ∀ j, c (atGroup i j) ≠ z := by
    simpa [Function.Surjective] using contra i
  let last : A t := ⟨2*(t+1),by unfold size; omega⟩
  have last_eq (i : A t) : c (i,last) = c (i,0) := by
    obtain ⟨z,hz⟩ := miss (some i)
    exact even_path (fun a => c (i,a)) z hz (fun a b h => c.valid (step_adj (Or.inl ⟨rfl,h⟩)))
      (t+1) last.isLt
  have wrap (i : A t) : c (i,0) ≠ c (rotate i,0) := by
    rw [← last_eq i]
    exact c.valid (step_adj (Or.inr ⟨by simp [last,size]; omega,rfl,rfl⟩))
  obtain ⟨z,hz⟩ := miss none
  have heq := even_path (fun i => c (i,0)) z hz (fun a b h => by
    have hrot : rotate a = b := by
      have hb := b.isLt
      exact Fin.ext (by simp [rotate,h])
    exact hrot ▸ wrap a) (t+1) last.isLt
  have zero : rotate last = 0 := by simp [rotate,last,size]; omega
  exact wrap last (by rw [zero]; exact heq)

/-- Color an odd circuit, using color zero just at position r. -/
def spike (r x : ℕ) : C :=
  if x = r then 0 else if (x + (if x < r then 0 else 1)) % 2 = 0 then 1 else 2

lemma spike_zero (r x : ℕ) : spike r x = 0 ↔ x = r := by
  unfold spike
  split_ifs <;> simp_all

lemma spike_step {N r x y : ℕ} (odd : N%2=1) (rN : r<N) (_xN : x<N) (_yN : y<N)
    (hN : 1<N) (step : y=x+1 ∨ (x+1=N ∧ y=0)) : spike r x ≠ spike r y := by
  unfold spike
  split_ifs <;> first | decide | omega

def pos {t} (x : Pt t) := x.1.val * size t + x.2.val

lemma pos_lt {t} (x : Pt t) : pos x < size t * size t := by
  have h := Nat.mul_le_mul_right (size t) (Nat.succ_le_of_lt x.1.isLt)
  have hj := x.2.isLt
  unfold pos
  rw [Nat.succ_mul] at h
  omega

lemma pos_inj {t} : Function.Injective (@pos t) := by
  intro x y eq
  have hx := x.2.isLt
  have hy := y.2.isLt
  apply Prod.ext <;> apply Fin.ext
  · by_contra! h
    have ne {a b : Pt t} (ha : a.1.val < b.1.val) : pos a < pos b := by
      have := Nat.mul_le_mul_right (size t) ha
      rw [Nat.succ_mul] at this
      have := a.2.isLt
      unfold pos
      omega
    rcases lt_or_gt_of_ne h with h | h
    · exact (ne h).ne eq
    · exact (ne h).ne eq.symm
  · have hmod := congrArg (· % size t) eq
    simpa [pos,Nat.add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hmod

lemma position_step {t} {x y : Pt t} (h : baseStep x y) :
    pos y = pos x + 1 ∨ (pos x+1=size t * size t ∧ pos y=0) := by
  rcases h with ⟨hi,hj⟩ | ⟨hj,hz,hi⟩
  · left; simp only [pos,hi,← hj]; omega
  · rcases rotate_step x.1 with hr | ⟨hr,h0⟩
    · left; simp only [pos,hz,hi,hr,Nat.succ_mul]; omega
    · right; simp only [pos,hi,h0,hz,zero_mul,add_zero,and_true]
      calc x.1.val*size t + x.2.val+1 = (x.1.val+1)*size t := by rw [Nat.succ_mul]; omega
           _ = _ := by rw [hr]

def offset {t} (i a : A t) : ℕ :=
  if i.val ≤ a.val then a.val-i.val else size t+a.val-i.val

lemma offset_lt {t} (i a : A t) : offset i a < size t := by
  have := i.isLt
  have := a.isLt
  unfold offset
  split <;> omega

lemma offset_zero {t} {i a : A t} : offset i a = 0 ↔ a = i := by
  rw [Fin.ext_iff]
  have := i.isLt
  have := a.isLt
  unfold offset
  split <;> omega

lemma offset_step {t} (i a : A t) :
    offset i (rotate a) = offset i a+1 ∨ (offset i a+1 = size t ∧ offset i (rotate a)=0) := by
  have hi := i.isLt
  have ha := a.isLt
  have hb := (rotate a).isLt
  rcases rotate_step a with h | ⟨h,h0⟩ <;> unfold offset <;> split_ifs <;> omega

/-- If the prescribed vertex starts block zero, give the remaining vertices of
that block colors one and two, and color the other block starts alternately
zero and one. The group of starts then omits two. -/
def firstSpike (a b : ℕ) : C :=
  if a=0 then if b=0 then 0 else if b%2=0 then 1 else 2
  else if b%2=1 then 2 else if a%2=1 then 0 else 1

lemma firstSpike_step {m x y u v : ℕ} (odd : m % 2 = 1) (hm : 2 < m) (_hy : y < m)
    (h : (u=x ∧ v=y+1) ∨
      (v=0 ∧ y+1=m ∧ (u=x+1 ∨ (x+1=m ∧ u=0)))) :
    firstSpike x y ≠ firstSpike u v := by
  obtain ⟨rfl,rfl⟩ | ⟨rfl,hl,(rfl | ⟨he,rfl⟩)⟩ := h <;>
    unfold firstSpike <;> split_ifs <;> first | contradiction | decide | omega

lemma focus_start {t} (i : A t) : ∃ c : (baseCycle t).Coloring C,
    c (atGroup (some i) 0) = 0 ∧ (∀ l, l ≠ 0 → c (atGroup (some i) l) ≠ 0) ∧
    ∀ k, k ≠ some i → ∃ a, ∀ l, c (atGroup k l) ≠ a := by
  let f (x : Pt t) := firstSpike (offset i x.1) x.2.val
  have proper {x y : Pt t} (h : baseStep x y) : f x ≠ f y := by
    refine firstSpike_step (m := size t) (by simp [size, Nat.add_mod]) (by unfold size; omega) x.2.isLt ?_
    rcases h with ⟨hi,hj⟩ | ⟨hj,hz,hi⟩
    · exact Or.inl ⟨by rw [hi],hj.symm⟩
    · exact Or.inr ⟨hz,hj,hi ▸ offset_step i x.1⟩
  refine ⟨mkColor f (fun _ _ => proper),?_,?_,?_⟩
  · change firstSpike (offset i i) 0 = 0
    simp [firstSpike,offset]
  · intro l hl
    have h : l.val ≠ 0 := fun he => hl (Fin.ext he)
    change firstSpike (offset i i) l.val ≠ 0
    simp [firstSpike,offset,h]
    split <;> decide
  · intro k hk
    cases k with
    | none =>
      refine ⟨2,fun l => ?_⟩
      change firstSpike (offset i l) 0 ≠ 2
      simp only [firstSpike,Nat.zero_mod,if_true]
      split_ifs <;> first | contradiction | decide
    | some a =>
      have hn : offset i a ≠ 0 := fun he => hk (congrArg some (offset_zero.mp he))
      refine ⟨if offset i a%2=1 then 1 else 0,fun l => ?_⟩
      change firstSpike (offset i a) l.val ≠ _
      unfold firstSpike
      split_ifs <;> first | contradiction | decide

lemma focus_interior {t} (i j : A t) (hj : j ≠ 0) : ∃ c : (baseCycle t).Coloring C,
    c (atGroup (some i) j) = 0 ∧ (∀ l, l ≠ j → c (atGroup (some i) l) ≠ 0) ∧
    ∀ k, k ≠ some i → ∃ a, ∀ l, c (atGroup k l) ≠ a := by
  let f (x : Pt t) := spike (pos (i,j)) (pos x)
  have proper {x y : Pt t} (h : baseStep x y) : f x ≠ f y := by
    apply spike_step (N := size t * size t) _ (pos_lt _) (pos_lt _) (pos_lt _) _ (position_step h)
    · simp [size,Nat.mul_mod,Nat.add_mod]
    · unfold size; nlinarith
  have only {x : Pt t} (h : f x = 0) : x = (i,j) := pos_inj (spike_zero _ _ |>.mp h)
  refine ⟨mkColor f (fun _ _ => proper), (spike_zero _ _).mpr rfl,?_,?_⟩
  · exact fun l hl h => hl (congrArg Prod.snd (only h))
  · intro k hk
    refine ⟨0,fun l he => ?_⟩
    have eq := only (x := atGroup k l) he
    cases k with
    | none => exact hj (congrArg Prod.snd eq).symm
    | some a => exact hk (congrArg some (congrArg Prod.fst eq))

lemma focus_starts {t} (j : A t) : ∃ c : (baseCycle t).Coloring C,
    c (atGroup none j) = 0 ∧ (∀ l, l ≠ j → c (atGroup none l) ≠ 0) ∧
    ∀ k, k ≠ none → ∃ a, ∀ l, c (atGroup k l) ≠ a := by
  let b (a : A t) := spike j.val a.val
  let other (a : C) : C := if a=0 then 1 else 0
  have ne (a : C) : other a ≠ a := by unfold other; split <;> grind
  let f (x : Pt t) := if x.2.val%2=0 then b x.1 else other (b x.1)
  have proper {x y : Pt t} (h : baseStep x y) : f x ≠ f y := by
    rcases h with ⟨hi,hj⟩ | ⟨hj,hz,hi⟩
    · simp only [f,hi,← hj]
      split_ifs <;> first | exact ne _ | exact (ne _).symm | omega
    · have hpar : x.2.val%2=0 := by unfold size at hj; omega
      simp only [f,hpar,hz,Nat.zero_mod,if_true,hi]
      exact spike_step (N := size t) (by simp [size,Nat.add_mod]) j.isLt x.1.isLt
        (rotate x.1).isLt (by unfold size; omega) (rotate_step x.1)
  refine ⟨mkColor f (fun _ _ => proper),?_,?_,?_⟩
  · change spike j.val j.val = 0
    exact (spike_zero _ _).mpr rfl
  · intro l hl
    change spike j.val l.val ≠ 0
    exact fun h => hl (Fin.ext ((spike_zero _ _).mp h))
  · rintro (_ | i) hk
    · exact (hk rfl).elim
    obtain ⟨z,h₁,h₂⟩ := exists_other (b i) (other (b i))
    refine ⟨z,fun l => ?_⟩
    change (if l.val%2=0 then b i else other (b i)) ≠ z
    split <;> first | exact h₁.symm | exact h₂.symm

def palette (t : ℕ) : Palette (Pt t) (Option (A t)) (A t) where
  base := baseCycle t
  group := atGroup
  hits := base_hits t
  focus := by
    rintro (_ | i) j
    · exact focus_starts j
    by_cases h : j=0
    · subst j; exact focus_start i
    · exact focus_interior i j h

end OMA.Toft1032

/- Extract a spanning critical subgraph without losing essential edges. -/

namespace OMA.Critical1032

open SimpleGraph

open scoped Classical in
/-- An edge-minimal four-chromatic graph retains every edge whose deletion
already makes the starting graph three-colorable. A spanning supply of such
edges preserves a prescribed minimum degree through minimization. -/
theorem extract {V : Type*} [Fintype V] [Nonempty V] (G F : SimpleGraph V)
    (_hFG : F ≤ G) (m : ℕ) (hm : 0 < m) (hdeg : ∀ v, m ≤ F.degree v)
    (hG : ¬G.Colorable 3)
    (heF : ∀ e ∈ F.edgeSet, (G.deleteEdges {e}).Colorable 3) :
    ∃ H : SimpleGraph V, Erdos1032.IsKCritical H 4 ∧ m ≤ H.minDegree := by
  classical
  obtain ⟨H, hHG, hn, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun K : SimpleGraph V => ¬K.Colorable 3) G hG
  have hFH : F ≤ H := by
    intro a b hab
    by_contra h
    apply hn
    apply Colorable.mono_left _ (heF s(a,b) hab)
    intro x y hxy
    apply deleteEdges_adj.mpr
    refine ⟨hHG hxy, ?_⟩
    intro hmem
    change s(x,y) = s(a,b) at hmem
    rcases Sym2.eq_iff.mp hmem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h hxy
    · exact h hxy.symm
  have hdel : ∀ e ∈ H.edgeSet, (H.deleteEdges {e}).Colorable 3 := by
    intro e he
    by_contra hn'
    have heq := le_antisymm (H.deleteEdges_le {e}) (hmin hn' (H.deleteEdges_le {e}))
    have hd := deleteEdges_eq_self.mp heq
    exact Set.disjoint_left.mp hd he (Set.mem_singleton e)
  have neighbor (v : V) : ∃ w, H.Adj v w := by
    obtain ⟨w, hw⟩ := (F.degree_pos_iff_exists_adj v).mp (lt_of_lt_of_le hm (hdeg v))
    exact ⟨w,hFH hw⟩
  have chrom : H.chromaticNumber = 4 := by
    apply (chromaticNumber_eq_iff_colorable_not_colorable (n := 3)).mpr
    refine ⟨?_, hn⟩
    let v : V := Classical.arbitrary V
    obtain ⟨w, hvw⟩ := neighbor v
    obtain ⟨c⟩ := hdel s(v,w) hvw
    refine ⟨Coloring.mk (fun x => if x = v then Fin.last 3 else (c x).castSucc) ?_⟩
    intro x y hxy
    by_cases hx : x = v
    · have hy : y ≠ v := by grind [Adj.ne]
      simpa only [if_pos hx, if_neg hy] using (Fin.castSucc_ne_last (c y)).symm
    by_cases hy : y = v
    · simpa only [if_neg hx, if_pos hy] using Fin.castSucc_ne_last (c x)
    have hh : (H.deleteEdges {s(v,w)}).Adj x y :=
      deleteEdges_adj.mpr ⟨hxy, by simp [hx, hy]⟩
    simpa [hx, hy] using c.valid hh
  refine ⟨H, ⟨⟨chrom, ?_⟩, ?_⟩, H.le_minDegree_of_forall_le_degree m
    (fun v => (hdeg v).trans (F.degree_le_of_le hFH))⟩
  · intro v
    obtain ⟨w, hvw⟩ := neighbor v
    obtain ⟨c⟩ := hdel s(v,w) hvw
    let K := (⊤ : H.Subgraph).deleteVerts {v}
    have hc : K.coe.Colorable 3 := by
      refine ⟨Coloring.mk (fun x => c x.val) ?_⟩
      intro x y hxy
      have hx : (x : V) ≠ v := x.property.2
      have hy : (y : V) ≠ v := y.property.2
      apply c.valid
      exact deleteEdges_adj.mpr ⟨K.adj_sub hxy, by simp [hx,hy]⟩
    change K.coe.chromaticNumber < (⊤ : H.Subgraph).coe.chromaticNumber
    have horig : H.chromaticNumber ≤ (⊤ : H.Subgraph).coe.chromaticNumber :=
      chromaticNumber_mono_of_hom (Subgraph.topIso (G := H)).symm.toHom
    exact lt_of_le_of_lt hc.chromaticNumber_le (lt_of_lt_of_le (by rw [chrom]; decide) horig)
  · intro e he
    change (H.deleteEdges {e}).chromaticNumber < H.chromaticNumber
    exact lt_of_le_of_lt (hdel e he).chromaticNumber_le (by rw [chrom]; decide)

end OMA.Critical1032

namespace OMA.Toft1032

open SimpleGraph
open scoped Classical

/-- Relabel the two copies of the palette and their complete bipartite connectors;
then minimize on this labeled vertex set. -/
theorem build (t : ℕ) :
    ∃ G : SimpleGraph (Fin (2*(2*t+3)^2 + 2*((2*t+3)+1)^2*(2*t+3))),
      Erdos1032.IsKCritical G 4 ∧ 2*t+3 ≤ G.minDegree := by
  classical
  let m := size t
  let n := 2*m^2 + 2*(m+1)^2*m
  let T := V (Pt t) (Option (A t)) (A t)
  have card : Fintype.card T = n := by
    simp only [T,V,Side,Pt,A,n,Fintype.card_sum,Fintype.card_prod,Fintype.card_option,Fintype.card_fin]
    dsimp [m]
    ring
  let e : Fin n ≃ T := (Fintype.equivFinOfCardEq card).symm
  let G := (graph (palette t) true).comap e
  let F := (graph (palette t) false).comap e
  let isoG : G ≃g graph (palette t) true := Iso.comap e _
  let isoF : F ≃g graph (palette t) false := Iso.comap e _
  let : Nonempty (Fin n) := ⟨e.symm (left ((0,0) : Pt t))⟩
  refine OMA.Critical1032.extract G F (fun _ _ h => graph_mono _ h) m (by dsimp [m,size]; omega)
    (fun v => ?_) (fun hc => not_colorable (palette t) (hc.of_hom isoG.symm.toHom)) ?_
  · calc
      m ≤ (graph (palette t) false).degree (e v) := by
        have h := degree_bound (palette t) (by simp) (fun x => ⟨some x.1,x.2,rfl⟩) (e v)
        simpa only [A,m,Fintype.card_fin] using h
      _ = F.degree v := isoF.degree_eq v
  · refine Sym2.ind fun u v huv => ?_
    obtain ⟨c⟩ := forced_edges (palette t) s(e u,e v) huv
    refine ⟨Coloring.mk (fun x => c (e x)) (fun {a b} hab => c.valid (deleteEdges_adj.mpr ⟨hab.1,?_⟩))⟩
    intro he
    apply (deleteEdges_adj.mp hab).2
    change s(e a,e b) = s(e u,e v) at he
    rcases Sym2.eq_iff.mp he with h | h
    · exact Sym2.eq_iff.mpr (.inl ⟨e.injective h.1,e.injective h.2⟩)
    · exact Sym2.eq_iff.mpr (.inr ⟨e.injective h.1,e.injective h.2⟩)

end OMA.Toft1032

/- Turn the critical graph family into the required lower bound on minimum degree. -/

namespace OMA.ToftScale1032

open Filter
open scoped Classical in
theorem from_family (build : ∀ t : ℕ, let m := 2*t+3
    ∃ G : SimpleGraph (Fin (2*m^2 + 2*(m+1)^2*m)),
      Erdos1032.IsKCritical G 4 ∧ m ≤ G.minDegree) :
    type_of% @Erdos1032.erdos_1032.variants.simonovits_toft := by
  refine ⟨1/3, by norm_num, frequently_atTop.mpr ?_⟩
  intro t
  let m := 2*t+3
  let n := 2*m^2 + 2*(m+1)^2*m
  obtain ⟨G,hG,hmG⟩ := build t
  have hmt : t ≤ m := by dsimp [m]; omega
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hn : m ≤ n := by
    dsimp [n]
    nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) m]
  refine ⟨n, hmt.trans hn, G, hG, ?_⟩
  have hr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hb : (n:ℝ) ≤ (3*(m:ℝ))^3 := by
    dsimp [n]
    push_cast
    nlinarith [sq_nonneg (m:ℝ), mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (m:ℝ)),
      mul_nonneg (sub_nonneg.mpr hr) (by positivity : 0 ≤ (m:ℝ))]
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ (n:ℝ)) hb
    (by norm_num : (0:ℝ) ≤ 1/3)
  have hc : ((3*(m:ℝ))^3) ^ (1/3:ℝ) = 3*(m:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hc] at hroot
  have hdeg : (m:ℝ) ≤ G.minDegree := by exact_mod_cast hmG
  linarith

end OMA.ToftScale1032

theorem OMA.solution : type_of% @Erdos1032.erdos_1032.variants.simonovits_toft := by
  exact OMA.ToftScale1032.from_family OMA.Toft1032.build
