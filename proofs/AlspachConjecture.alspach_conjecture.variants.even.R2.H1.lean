import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_even_R2
import Mathlib.Data.Multiset.Sort

namespace AlspachSmall

private def partitionsAux (n : Nat) : Nat → Nat → Nat → List (List Nat)
  | 0, _, total => if total = 0 then [[]] else []
  | fuel + 1, lo, total =>
      if total = 0 then [[]] else
        ((List.range (n+1)).filter (fun k => decide (lo ≤ k ∧ k ≤ total))).flatMap fun k =>
          (partitionsAux n fuel k (total-k)).map (k :: ·)

/-- Nondecreasing partitions of `total` with positive parts in the interval `[lo,n]`.
The characterization below applies for `0 < lo`. -/
def partitions (n lo total : Nat) : List (List Nat) :=
  partitionsAux n total lo total

private theorem length_le_sum_of_pos {xs : List Nat} (h : ∀ k ∈ xs, 0 < k) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons k rest ih =>
    have hk := h k (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem mem_partitionsAux_iff {n fuel lo total : Nat} {xs : List Nat} (hlo : 0 < lo) :
    xs ∈ partitionsAux n fuel lo total ↔
      xs.length ≤ fuel ∧ xs.Pairwise (· ≤ ·) ∧ (∀ k ∈ xs, lo ≤ k ∧ k ≤ n) ∧ xs.sum = total := by
  induction fuel generalizing lo total xs with
  | zero =>
    cases xs with
    | nil => by_cases ht : total = 0 <;> simp_all [partitionsAux] <;> omega
    | cons k rest => by_cases ht : total = 0 <;> simp [partitionsAux, ht]
  | succ fuel ih =>
    by_cases ht : total = 0
    · subst total
      cases xs with
      | nil => simp [partitionsAux]
      | cons k rest =>
        have hk : ¬ (lo ≤ k ∧ k + rest.sum = 0) := by omega
        simp [partitionsAux, List.pairwise_cons]
        omega
    · rw [partitionsAux, if_neg ht]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_map]
      constructor
      · rintro ⟨k, ⟨hkn, hlk, hkt⟩, rest, hr, rfl⟩
        obtain ⟨hrlen, hrsort, hrbounds, hrsum⟩ := (ih (by omega : 0 < k)).mp hr
        refine ⟨by simp only [List.length_cons]; omega, List.pairwise_cons.mpr ⟨?_, hrsort⟩, ?_, ?_⟩
        · exact fun j hj => (hrbounds j hj).1
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact ⟨hlk, by omega⟩
          · exact ⟨Nat.le_trans hlk (hrbounds _ hj).1, (hrbounds _ hj).2⟩
        · simp only [List.sum_cons]
          omega
      · rintro ⟨hlen, hsort, hbounds, hsum⟩
        cases xs with
        | nil => simp_all
        | cons k rest =>
          have ⟨hlk, hkn⟩ := hbounds k (by simp)
          have ⟨hsfirst, hstail⟩ := List.pairwise_cons.mp hsort
          simp only [List.sum_cons] at hsum
          simp only [List.length_cons] at hlen
          refine ⟨k, ⟨by omega, hlk, by omega⟩, rest, ?_, rfl⟩
          apply (ih (by omega : 0 < k)).mpr
          exact ⟨by omega, hstail, fun j hj => ⟨hsfirst j hj, (hbounds j (.tail k hj)).2⟩, by omega⟩

theorem mem_partitions_iff {n lo total : Nat} {xs : List Nat} (hlo : 0 < lo) :
    xs ∈ partitions n lo total ↔
      xs.Pairwise (· ≤ ·) ∧ (∀ k ∈ xs, lo ≤ k ∧ k ≤ n) ∧ xs.sum = total := by
  rw [partitions, mem_partitionsAux_iff hlo]
  constructor
  · exact fun h => h.2
  · rintro ⟨hs, hb, hsum⟩
    refine ⟨?_, hs, hb, hsum⟩
    rw [← hsum]
    exact length_le_sum_of_pos (fun k hk => Nat.lt_of_lt_of_le hlo (hb k hk).1)

end AlspachSmall

namespace AlspachSmall.Bitmap

abbrev Code (n : Nat) := Fin n × List (Fin n)

def chain {n : Nat} (a b : Fin n) : List (Fin n) → Bool
  | [] => a.val / 2 != b.val / 2
  | x :: xs => (a.val / 2 != x.val / 2) && chain x b xs

def arcs {n : Nat} (a b : Fin n) : List (Fin n) → List (Fin n × Fin n)
  | [] => [(a, b)]
  | x :: xs => (a, x) :: arcs x b xs

def good {n : Nat} (c : Code n) : Bool :=
  chain c.1 c.1 c.2 && decide ((c.2 ++ [c.1]).Nodup) && decide (3 ≤ c.2.length + 1)

-- Nat.pair's defining formula, available here without a Mathlib import.
def key {n : Nat} (p : Fin n × Fin n) : Nat :=
  let a := min p.1.val p.2.val
  let b := max p.1.val p.2.val
  if a < b then b * b + a else a * a + a + b

def bitmap {n : Nat} : List (Fin n × Fin n) → Nat
  | [] => 0
  | p :: ps => (1 <<< key p) ||| bitmap ps

def pack {n : Nat} : List (Code n) → Option Nat
  | [] => some 0
  | c :: cs => do
    let rest ← pack cs
    let b := bitmap (arcs c.1 c.1 c.2)
    if good c && (b &&& rest == 0) then some (b ||| rest) else none

def full (n : Nat) := bitmap ((List.finRange n).flatMap fun a =>
  ((List.finRange n).filter (fun b => b.val / 2 != a.val / 2)).map (fun b => (a,b)))

def vertex {n : Nat} (hn : 0 < n) (a : Nat) : Fin n := ⟨a % n, Nat.mod_lt _ hn⟩

def code {n : Nat} (hn : 0 < n) : List Nat → Code n
  | [] => (vertex hn 0, [])
  | a :: as => (vertex hn a, as.map (vertex hn))

def Valid {n : Nat} (hn : 0 < n) (sizes : List Nat) (paths : List (List Nat)) : Prop :=
  let cs := paths.map (code hn)
  pack cs = some (full n) ∧ cs.map (fun c => c.2.length + 1) = sizes

instance {n : Nat} (hn : 0 < n) (sizes : List Nat) (paths : List (List Nat)) :
    Decidable (Valid hn sizes paths) := inferInstanceAs (Decidable (_ ∧ _))

end AlspachSmall.Bitmap

/-! Transfer the checked tables for orders six and eight to Mathlib's cycle
decomposition predicate. The walk-construction and bitmap soundness arguments
adapt Deldor14's proof for odd orders in AlspachConjecture.alspach_conjecture.R1.H1.
Here the adjacency condition omits consecutive matching pairs. -/

namespace AlspachSmall.Bitmap

open SimpleGraph AlspachConjecture

/-- The complete graph less the pairs (0,1), (2,3), … . -/
abbrev cocktail (n : Nat) : SimpleGraph (Fin n) :=
  (completeGraph Nat).comap (fun x : Fin n => x.val / 2)

/-- Identify the arithmetic adjacency model with the actual subtraction in
the upstream theorem whenever the removed matching pairs consecutive vertices. -/
theorem cocktail_eq_sdiff {n : Nat} (I : (completeGraph (Fin n)).Subgraph)
    (paired : ∀ a b : Fin n, I.Adj a b ↔ a ≠ b ∧ a.val / 2 = b.val / 2) :
    cocktail n = completeGraph (Fin n) \ I.spanningCoe := by
  ext a b
  change (a.val / 2 ≠ b.val / 2) ↔ (a ≠ b ∧ ¬ I.Adj a b)
  rw [paired]
  constructor
  · intro h
    exact ⟨fun eq => h (congrArg (fun v : Fin n => v.val / 2) eq), fun both => h both.2⟩
  · rintro ⟨hne, hnm⟩ he
    exact hnm ⟨hne, he⟩

private def trail {n : Nat} (a b : Fin n) : (l : List (Fin n)) → chain a b l = true → (cocktail n).Walk a b
  | [], h => .cons (by simpa [chain] using h) .nil
  | x::xs, h => .cons (by simpa [chain] using (Bool.and_eq_true_iff.mp h).1)
      (trail x b xs ((Bool.and_eq_true_iff.mp h).2))

private lemma trail_length {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).length=l.length+1 := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,ih]

private lemma trail_support {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).support=a::(l++[b]) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,ih]

private lemma trail_edges {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).edges=(arcs a b l).map (fun p => s(p.1,p.2)) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,arcs,ih]

private def cyc {n : Nat} (c : Code n) (h : good c=true) : Cycle (cocktail n) := by
  have facts := Bool.and_eq_true_iff.mp h
  have hface := Bool.and_eq_true_iff.mp facts.1
  refine ⟨c.1, trail c.1 c.1 c.2 hface.1, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,?_⟩⟩
  · apply (Walk.isPath_def _).mpr
    rw [Walk.support_tail_of_not_nil _ (by simp [← Walk.length_eq_zero_iff,trail_length]),trail_support]
    simpa using of_decide_eq_true hface.2
  · rw [trail_length]
    exact of_decide_eq_true facts.2

private lemma cyc_length {n : Nat} (c : Code n) (h : good c=true) :
    (cyc c h).length=c.2.length+1 := trail_length .. 

private lemma cyc_edges {n : Nat} (c : Code n) (h : good c=true) :
    (cyc c h).edges=(arcs c.1 c.1 c.2).map (fun p => s(p.1,p.2)) := trail_edges ..

private theorem key_iff {n : Nat} (p q : Fin n × Fin n) :
    key p=key q ↔ s(p.1,p.2)=s(q.1,q.2) := by
  change Nat.pair (min p.1.val p.2.val) (max p.1.val p.2.val) =
    Nat.pair (min q.1.val q.2.val) (max q.1.val q.2.val) ↔ _
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  simp only [Nat.pair_eq_pair,Sym2.eq_iff,Fin.ext_iff]
  omega

private lemma read_bitmap {n : Nat} (ps : List (Fin n × Fin n)) (q : Fin n × Fin n) :
    (bitmap ps).testBit (key q)=true ↔ s(q.1,q.2) ∈ ps.map (fun p => s(p.1,p.2)) := by
  induction ps with
  | nil => simp [bitmap]
  | cons p ps ih =>
    rw [bitmap,Nat.testBit_or,Bool.or_eq_true_iff]
    have bit : (1 <<< key p).testBit (key q) = decide (key p=key q) := by
      rw [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow]
    rw [bit, decide_eq_true_eq, key_iff,ih,List.map_cons,List.mem_cons]
    exact or_congr_left eq_comm

theorem packed {n : Nat} (cs : List (Code n)) (k : Nat) (hc : pack cs=some k) :
    ∃ C : Multiset (Cycle (cocktail n)), lengths C = ((cs.map fun c => c.2.length+1) : List Nat) ∧
      ∀ q : Fin n × Fin n, (C.filter fun c => s(q.1,q.2) ∈ c.edges).card =
        (k.testBit (key q)).toNat := by
  classical
  induction cs generalizing k with
  | nil =>
    have z : k=0 := by simpa [pack,eq_comm] using hc
    exact ⟨0,rfl,fun q => by simp [z]⟩
  | cons c cs ih =>
    cases h : pack cs with
    | none => simp [pack,h] at hc
    | some r =>
      let bits := bitmap (arcs c.1 c.1 c.2)
      have facts : (good c=true ∧ bits &&& r=0) ∧ bits ||| r=k := by
        simpa [pack,h,bits] using hc
      obtain ⟨⟨cgood,dis⟩,get'⟩ := facts
      have get := get'.symm
      obtain ⟨C,lens,count⟩ := ih r h
      refine ⟨cyc c cgood ::ₘ C,?_,?_⟩
      · simpa [lengths,cyc_length] using congrArg (Multiset.cons (c.2.length+1)) lens
      · intro q
        have mem : s(q.1,q.2) ∈ (cyc c cgood).edges ↔ bits.testBit (key q)=true := by
          rw [cyc_edges]; exact (read_bitmap _ _).symm
        have distinct := congrArg (fun m : Nat => m.testBit (key q)) dis
        rw [get,Nat.testBit_or]
        by_cases own : bits.testBit (key q)=true
        · have zero : r.testBit (key q)=false := by simpa [own] using distinct
          rw [Multiset.filter_cons_of_pos (p:=fun v : Cycle (cocktail n) => s(q.1,q.2) ∈ v.edges) C (mem.mpr own),Multiset.card_cons,count]
          simp [own,zero]
        · rw [Multiset.filter_cons_of_neg (p:=fun v : Cycle (cocktail n) => s(q.1,q.2) ∈ v.edges) C (fun e => own (mem.mp e)),count]
          simp [own]

theorem full_has {n : Nat} (a b : Fin n) (h : a.val / 2 ≠ b.val / 2) : (full n).testBit (key (a,b))=true := by
  apply (read_bitmap _ _).mpr
  apply List.mem_map.mpr
  refine ⟨(a,b), List.mem_flatMap.mpr ⟨a, by simp, ?_⟩, rfl⟩
  exact List.mem_map.mpr ⟨b,by simp [h.symm],rfl⟩


theorem from_row {n : Nat} {hn : 0 < n} {sizes : List Nat} {paths : List (List Nat)}
    (ok : Valid hn sizes paths) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧
      lengths C = (sizes : Multiset Nat) := by
  classical
  obtain ⟨C, hl, hc⟩ := packed _ _ ok.1
  refine ⟨C, ?_, hl.trans (congrArg (fun l : List Nat => (l : Multiset Nat)) ok.2)⟩
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have h : a.val / 2 ≠ b.val / 2 := (SimpleGraph.mem_edgeFinset.mp he : (cocktail n).Adj a b)
    simpa [full_has a b h] using hc (a, b)

theorem realize_order (n total : Nat) (tab : List (List Nat × List (List Nat)))
    (hn : 0 < n)
    (present : ∀ {xs : List Nat}, xs.Pairwise (· ≤ ·) → (∀ k ∈ xs, 3 ≤ k ∧ k ≤ n) →
      xs.sum = total → ∃ cs, (xs, cs) ∈ tab)
    (verified : ∀ row ∈ tab, Valid hn row.1 row.2)
    (m : Multiset Nat) (bound : ∀ k ∈ m, 3 ≤ k ∧ k ≤ n) (hsum : m.sum = total) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m := by
  let xs := m.sort (· ≤ ·)
  have eqm : (xs : Multiset Nat) = m := Multiset.sort_eq ..
  have sx : xs.sum = total := by
    convert hsum using 1
    exact congrArg Multiset.sum eqm
  have bounds (k : Nat) (hk : k ∈ xs) : 3 ≤ k ∧ k ≤ n := bound k (by simpa [xs] using hk)
  obtain ⟨paths, mem⟩ := present (Multiset.pairwise_sort ..) bounds sx
  obtain ⟨C, cover, sizes⟩ := from_row (verified (xs, paths) mem)
  exact ⟨C, cover, sizes.trans eqm⟩

end AlspachSmall.Bitmap

namespace AlspachSmall

/-- Each vertex of an even order has a unique distinct mate in its consecutive pair. -/
theorem mate_index (k i : Nat) (hi : i < k + k) :
    ∃ j : Nat, j < k + k ∧ i ≠ j ∧ i / 2 = j / 2 ∧
      ∀ z : Nat, i ≠ z → i / 2 = z / 2 → z = j := by
  by_cases hi0 : i % 2 = 0
  · refine ⟨i + 1, by omega, by omega, by omega, ?_⟩
    intro z hne hq
    omega
  · refine ⟨i - 1, by omega, by omega, by omega, ?_⟩
    intro z hne hq
    omega

end AlspachSmall

namespace AlspachSmall.Bitmap

open SimpleGraph AlspachConjecture

def consecutiveMatching (n : Nat) : (completeGraph (Fin n)).Subgraph where
  verts := Set.univ
  Adj i j := i ≠ j ∧ i.val / 2 = j.val / 2
  adj_sub := fun h => h.1
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩

theorem consecutiveMatching_perfect {n : Nat} (hn : Even n) :
    (consecutiveMatching n).IsPerfectMatching := by
  obtain ⟨k, rfl⟩ := hn
  apply Subgraph.isPerfectMatching_iff.mpr
  intro i
  obtain ⟨j, hj, hij, hq, huniq⟩ := AlspachSmall.mate_index k i.val i.isLt
  refine ⟨⟨j, hj⟩, ⟨fun h => hij (congrArg Fin.val h), hq⟩, ?_⟩
  intro z hz
  apply Fin.ext
  exact huniq z.val (fun h => hz.1 (Fin.ext h)) hz.2

theorem consecutiveMatching_complement (n : Nat) :
    cocktail n = completeGraph (Fin n) \ (consecutiveMatching n).spanningCoe :=
  cocktail_eq_sdiff _ (fun _ _ => Iff.rfl)

open Classical in
theorem choose_consecutive_matching {n : Nat} (hn : Even n) (m : Multiset Nat)
    (w : ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m := by
  refine ⟨consecutiveMatching n, consecutiveMatching_perfect hn, ?_⟩
  have transport (G H : SimpleGraph (Fin n)) [dG : DecidableRel G.Adj]
      [dH : DecidableRel H.Adj] (eq : G = H)
      (cover : ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧ lengths C = m) :
      ∃ C : Multiset (Cycle H), IsCycleDecomposition H C ∧ lengths C = m := by
    subst H
    cases Subsingleton.elim dG dH
    exact cover
  exact transport _ _ (consecutiveMatching_complement n) w

end AlspachSmall.Bitmap

namespace AlspachSmall.Bitmap

open SimpleGraph AlspachConjecture
open scoped Classical

/-- Restricted cycle decomposition on the ambient graph. The bitmask specifies
exactly the edges used. Each marked edge occurs on one cycle. -/
def Region (n mask : Nat) (m : Multiset Nat) : Prop :=
  ∃ C : Multiset (Cycle (cocktail n)), lengths C = m ∧
    ∀ q : Fin n × Fin n, (C.filter fun c => s(q.1,q.2) ∈ c.edges).card =
      (mask.testBit (key q)).toNat

abbrev ValidForMask {n : Nat} (hn : 0 < n) (mask : Nat)
    (sizes : List Nat) (paths : List (List Nat)) : Prop :=
  let cs := paths.map (code hn)
  pack cs = some mask ∧ cs.map (fun c => c.2.length + 1) = sizes

theorem region_of_row {n mask : Nat} {hn : 0 < n} {sizes : List Nat} {paths : List (List Nat)}
    (h : ValidForMask hn mask sizes paths) : Region n mask (sizes : Multiset Nat) := by
  obtain ⟨C, hl, hcounts⟩ := packed _ _ h.1
  exact ⟨C, hl.trans (congrArg (fun l : List Nat => (l : Multiset Nat)) h.2), hcounts⟩

theorem decompose_full {n : Nat} {m : Multiset Nat} (h : Region n (full n) m) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m := by
  obtain ⟨C, hl, hc⟩ := h
  refine ⟨C, ?_, hl⟩
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have hab : a.val / 2 ≠ b.val / 2 := (SimpleGraph.mem_edgeFinset.mp he : (cocktail n).Adj a b)
    simpa [full_has a b hab] using hc (a,b)

end AlspachSmall.Bitmap

namespace AlspachSmall.Bitmap

open AlspachConjecture SimpleGraph

theorem region_union {n a b : Nat} {m₁ m₂ : Multiset ℕ}
    (h₁ : Region n a m₁) (h₂ : Region n b m₂) (hd : a &&& b = 0) :
    Region n (a ||| b) (m₁ + m₂) := by
  classical
  obtain ⟨C₁, l₁, c₁⟩ := h₁
  obtain ⟨C₂, l₂, c₂⟩ := h₂
  refine ⟨C₁ + C₂, ?_, ?_⟩
  · rw [lengths, Multiset.map_add]
    exact congrArg₂ (· + ·) l₁ l₂
  · intro q
    rw [Multiset.filter_add, Multiset.card_add, c₁, c₂, Nat.testBit_or]
    have disjointBits := congrArg (fun w : Nat => w.testBit (key q)) hd
    change (a &&& b).testBit (key q) = (0 : Nat).testBit (key q) at disjointBits
    rw [Nat.testBit_and, Nat.zero_testBit] at disjointBits
    have add_or : ∀ x y : Bool, (x && y) = false → x.toNat + y.toNat = (x || y).toNat := by decide
    exact add_or _ _ disjointBits


end AlspachSmall.Bitmap

namespace AlspachSmall.Keys

def lengthKey (xs : List Nat) : Nat := (xs.map fun k => 32^(k-3)).sum

theorem lengthKey_append (xs ys : List Nat) : lengthKey (xs ++ ys) = lengthKey xs + lengthKey ys := by
  simp [lengthKey]

private def suffixKey (lo : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if lo ≤ x then 32^(x-lo) else 0) + suffixKey lo xs

private theorem initial (xs : List Nat) (h : ∀ x ∈ xs, 3 ≤ x) : suffixKey 3 xs = lengthKey xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have t := ih (fun k hk => h k (by simp [hk]))
    simp [suffixKey, hx, lengthKey, t]

private theorem suffix_step (lo : Nat) (xs : List Nat) :
    suffixKey lo xs = xs.count lo + 32 * suffixKey (lo+1) xs := by
  induction xs with
  | nil => simp [suffixKey]
  | cons x xs ih =>
    by_cases eq : x = lo
    · subst x
      simp [suffixKey, ih, show ¬ lo + 1 ≤ lo by omega]
      omega
    · by_cases more : lo + 1 ≤ x
      · have diff : x - lo = (x - (lo+1)) + 1 := by omega
        have ge : lo ≤ x := by omega
        simp [suffixKey,more,ge,List.count_cons,eq,ih,diff,Nat.pow_succ]
        omega
      · have lt : ¬ lo ≤ x := by omega
        simp [suffixKey,more,lt,List.count_cons,eq,ih]

private theorem count_bound {k : Nat} (hk : 3 ≤ k) (xs : List Nat) :
    3 * xs.count k ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x = k
    · subst x
      simp [List.count_cons]
      omega
    · simp [List.count_cons, h]
      omega

/-- Equal base-32 length keys determine a multiset of lengths. Each length is
at least three and occurs fewer than 32 times on each side. -/
theorem perm_of_key {xs ys : List Nat}
    (hx : ∀ x ∈ xs, 3 ≤ x) (hy : ∀ y ∈ ys, 3 ≤ y)
    (cx : ∀ k, 3 ≤ k → xs.count k < 32) (cy : ∀ k, 3 ≤ k → ys.count k < 32)
    (equal : lengthKey xs = lengthKey ys) : xs.Perm ys := by
  have tails (j : Nat) : suffixKey (3+j) xs = suffixKey (3+j) ys := by
    induction j with
    | zero => simpa only [Nat.add_zero,initial xs hx,initial ys hy] using equal
    | succ j ih =>
      change suffixKey ((3+j)+1) xs = suffixKey ((3+j)+1) ys
      have ax := suffix_step (3+j) xs
      have ay := suffix_step (3+j) ys
      have bx := cx (3+j) (by omega)
      have by' := cy (3+j) (by omega)
      omega
  apply List.perm_iff_count.mpr
  intro k
  by_cases ge : 3 ≤ k
  · have eq := tails (k-3)
    rw [show 3 + (k-3) = k by omega] at eq
    have ax := suffix_step k xs
    have ay := suffix_step k ys
    have bx := cx k ge
    have by' := cy k ge
    omega
  · have ax : k ∉ xs := fun hk => ge (hx _ hk)
    have ay : k ∉ ys := fun hk => ge (hy _ hk)
    simp [List.count_eq_zero_of_not_mem,ax,ay]

theorem perm_of_key_bounded {xs ys : List Nat}
    (hx : ∀ x ∈ xs, 3 ≤ x) (hy : ∀ y ∈ ys, 3 ≤ y)
    (sx : xs.sum ≤ 84) (sy : ys.sum ≤ 84)
    (equal : lengthKey xs = lengthKey ys) : xs.Perm ys :=
  perm_of_key hx hy (fun k hk => by have := count_bound hk xs; omega)
    (fun k hk => by have := count_bound hk ys; omega) equal

end AlspachSmall.Keys

namespace AlspachSmall.Packed

/-- Read four-bit vertex labels from the least significant digit first.
Digit fifteen ends a cycle. The longest supported row has 84 vertices
and at most 28 cycle separators. -/
def readDigits : Nat → Nat → List Nat → List (List Nat) → List (List Nat)
  | 0, _, _, done => done.reverse
  | fuel+1, w, cycle, done =>
    if w = 0 then done.reverse
    else if w%16 = 15 then readDigits fuel (w/16) [] (cycle.reverse :: done)
    else readDigits fuel (w/16) (w%16 :: cycle) done

def paths (w : Nat) := readDigits 113 w [] []
def sizes (w : Nat) := (paths w).map List.length
def keys (ws : List Nat) := ws.map (fun w => Keys.lengthKey (sizes w))

abbrev Tested (n : Nat) (hn : 0<n) (mask total w : Nat) : Prop :=
  let cs := (paths w).map (Bitmap.code hn)
  (Bitmap.pack cs = some mask ∧ cs.map (fun c => c.2.length+1) = sizes w) ∧
  (∀ d ∈ sizes w, 3≤d) ∧ (sizes w).sum = total

def AllTested (n : Nat) (hn : 0<n) (mask total : Nat) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, Tested n hn mask total w

instance {n : Nat} {hn : 0<n} {mask total : Nat} {ws : List Nat} :
    Decidable (AllTested n hn mask total ws) :=
  inferInstanceAs (Decidable (∀ w ∈ ws, Tested n hn mask total w))

theorem allTestedAppend {n : Nat} {hn : 0<n} {mask total : Nat} {xs ys : List Nat}
    (hx : AllTested n hn mask total xs) (hy : AllTested n hn mask total ys) :
    AllTested n hn mask total (xs ++ ys) :=
  fun w h => (List.mem_append.mp h).elim (hx w) (hy w)

end AlspachSmall.Packed

namespace AlspachSmall.Bitmap

open SimpleGraph AlspachConjecture

/-- A table can supply actual cycles of the indicated lengths for every key it lists. -/
abbrev Offers (n mask total : Nat) (ws : List Nat) :=
  ∀ {k}, k ∈ Packed.keys ws → ∃ ys : List Nat, Region n mask (ys : Multiset Nat) ∧
    Keys.lengthKey ys = k ∧ (∀ d ∈ ys, 3 ≤ d) ∧ ys.sum = total

theorem checkedOffers {n mask total : Nat} {hn : 0 < n} {ws : List Nat}
    (h : Packed.AllTested n hn mask total ws) : Offers n mask total ws := by
  intro k hk
  obtain ⟨w, hw, eq⟩ := List.mem_map.mp hk
  obtain ⟨good, low, sum⟩ := h w hw
  exact ⟨Packed.sizes w, region_of_row good, eq, low, sum⟩

theorem relabeledOffers {n a b total : Nat} {left right : List Nat}
    (given : Offers n a total left) (same : Packed.keys right = Packed.keys left)
    (move : ∀ m, Region n a m → Region n b m) : Offers n b total right := by
  intro k hk
  obtain ⟨ys,good,eq,low,sum⟩ := given (same ▸ hk)
  exact ⟨ys,move _ good,eq,low,sum⟩

/-- Either a full certificate or two complementary partial certificates give
the same actual multiset after the base-32 keys have been checked. -/
theorem region_of_offers {n a b half : Nat} {hn : 0 < n} {left right extras : List Nat}
    (disjoint : a &&& b = 0) (allEdges : a ||| b = full n) (bound : half + half ≤ 84)
    (hl : Packed.AllTested n hn a half left) (hr : Offers n b half right)
    (he : Packed.AllTested n hn (full n) (half+half) extras) (xs : List Nat)
    (hx : ∀ k ∈ xs, 3 ≤ k) (hs : xs.sum = half + half)
    (coverage : Keys.lengthKey xs ∈ Packed.keys extras ∨
      ∃ u ∈ Packed.keys left, ∃ v ∈ Packed.keys right, u + v = Keys.lengthKey xs) :
    Region n (full n) (xs : Multiset Nat) := by
  rcases coverage with direct | ⟨u,hu,v,hv,huv⟩
  · obtain ⟨ys,hy,eq,ly,sy⟩ := checkedOffers he direct
    have perm := Keys.perm_of_key_bounded ly hx (sy.le.trans bound) (hs.le.trans bound) eq
    have same : (ys : Multiset Nat) = (xs : Multiset Nat) := Quot.sound perm
    exact same ▸ hy
  · obtain ⟨ys,hy,ey,ly,sy⟩ := checkedOffers hl hu
    obtain ⟨zs,hz,ez,lz,sz⟩ := hr hv
    have lens : Keys.lengthKey (ys++zs) = Keys.lengthKey xs := by
      rw [Keys.lengthKey_append,ey,ez,huv]
    have low (k : Nat) (hk : k ∈ ys++zs) : 3 ≤ k := (List.mem_append.mp hk).elim (ly k) (lz k)
    have total : (ys++zs).sum ≤ 84 := by simpa only [List.sum_append,sy,sz] using bound
    have perm := Keys.perm_of_key_bounded low hx total (hs.le.trans bound) lens
    have same : (ys : Multiset Nat) + (zs : Multiset Nat) = (xs : Multiset Nat) := Quot.sound perm
    have merged := region_union hy hz disjoint
    simpa only [allEdges,same] using merged

theorem from_partition_offers {n a b half : Nat} {hn : 0 < n} {left right extras : List Nat}
    (disjoint : a &&& b = 0) (allEdges : a ||| b = full n) (bound : half + half ≤ 84)
    (hl : Packed.AllTested n hn a half left) (hr : Offers n b half right)
    (he : Packed.AllTested n hn (full n) (half+half) extras)
    (allKeys : ∀ xs ∈ partitions n 3 (half+half), Keys.lengthKey xs ∈ Packed.keys extras ∨
      ∃ u ∈ Packed.keys left, ∃ v ∈ Packed.keys right, u + v = Keys.lengthKey xs)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ n) (hsum : m.sum = half+half) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m := by
  let xs := m.sort (· ≤ ·)
  have eqm : (xs : Multiset Nat) = m := Multiset.sort_eq ..
  have hs : xs.sum = half+half := by
    convert hsum using 1
    exact congrArg Multiset.sum eqm
  have lim (k : Nat) (hk : k ∈ xs) : 3 ≤ k ∧ k ≤ n := hm k (by simpa [xs] using hk)
  have has := (mem_partitions_iff (by decide : 0 < 3)).2 ⟨Multiset.pairwise_sort ..,lim,hs⟩
  have R := region_of_offers disjoint allEdges bound hl hr he xs (fun k hk => (lim k hk).1) hs
    (allKeys xs has)
  exact decompose_full (eqm ▸ R)

end AlspachSmall.Bitmap

namespace AlspachSmall.Coverage
open Keys

def Covered (a b e : List Nat) (k : Nat) := k ∈ e ∨ ∃ u ∈ a, ∃ v ∈ b, u + v = k

def Split (xs : List Nat) (h : Nat) := ∃ a b : List Nat, (a ++ b).Perm xs ∧ a.sum = h

private theorem split_perm {xs ys : List Nat} {h : Nat} (q : Split xs h) (hp : xs.Perm ys) : Split ys h := by
  obtain ⟨a,b,hab,hs⟩ := q
  exact ⟨a,b,hab.trans hp,hs⟩

private theorem split_append {xs : List Nat} {h : Nat} (q : Split xs h) (ys : List Nat) : Split (xs ++ ys) h := by
  obtain ⟨a,b,hab,hs⟩ := q
  exact ⟨a,b++ys,by simpa only [List.append_assoc] using hab.append_right ys,hs⟩

def ValidState (xs : List Nat) (s : Nat) := ∀ q, s.testBit q = true → Split xs q

private theorem initial : ValidState [] 1 := by
  intro q h
  have z : q = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h
  exact ⟨[],[],by simp,by simp [z]⟩

private def step (v s : Nat) := s ||| (s <<< v)

private theorem step_sound {xs : List Nat} {s : Nat} (ok : ValidState xs s) (v : Nat) :
    ValidState (v::xs) (step v s) := by
  intro q hit
  simp only [step,Nat.testBit_or,Bool.or_eq_true_iff,Nat.testBit_shiftLeft,Bool.and_eq_true,
    decide_eq_true_eq] at hit
  rcases hit with h|⟨hv,h⟩
  · obtain ⟨a,b,hab,ha⟩ := ok _ h
    exact ⟨a,v::b,List.perm_middle.trans (hab.cons v),ha⟩
  · obtain ⟨a,b,hab,ha⟩ := ok _ h
    exact ⟨v::a,b,hab.cons v,by simp [ha]; omega⟩

def advance (v : Nat) : Nat → Nat → Nat
  | 0, s => s
  | c+1,s => step v (advance v c s)

private theorem advance_sound {xs : List Nat} {s : Nat} (ok : ValidState xs s) (v c : Nat) :
    ValidState (List.replicate c v ++ xs) (advance v c s) := by
  induction c with
  | zero => simpa [advance] using ok
  | succ c ih => simpa [advance,List.replicate_succ] using step_sound ih v

/-- Enumerate the keys for which the subset-sum bitmap has no bit at the target.
The count of the largest part is the outer loop, so the resulting keys are in increasing order. -/
def missed (target : Nat) : Nat → Nat → Nat → Nat → List Nat
  | 0, r, key, bits =>
    if r % 3 = 0 && !(advance 3 (r/3) bits).testBit target then [key + r/3] else []
  | d+1, r, key, bits =>
    if bits.testBit target then [] else
      let v := d+4
      (List.range (r/v+1)).flatMap fun c =>
        missed target d (r-c*v) (key+c*32^(v-3)) (advance v c bits)

private theorem pull (v : Nat) (xs : List Nat) :
    ∃ c ys, (List.replicate c v ++ ys).Perm xs ∧ ∀ k ∈ ys, k ∈ xs ∧ k ≠ v := by
  induction xs with
  | nil => exact ⟨0,[],by simp,by simp⟩
  | cons x xs ih =>
    obtain ⟨c,ys,hp,hs⟩ := ih
    by_cases hx : x = v
    · subst x
      exact ⟨c+1,ys,by simpa [List.replicate_succ] using hp.cons v,
        fun k hk => ⟨.tail _ (hs k hk).1,(hs k hk).2⟩⟩
    · refine ⟨c,x::ys,List.perm_middle.trans (hp.cons x),?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact ⟨by simp,hx⟩
      · exact ⟨.tail _ (hs k hk).1,(hs k hk).2⟩

private theorem psum {xs ys : List Nat} (p : xs.Perm ys) : xs.sum = ys.sum := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap a b t => simp [Nat.add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem key_perm {xs ys : List Nat} (p : xs.Perm ys) : lengthKey xs = lengthKey ys :=
  psum (p.map _)

private theorem rep_key (c v : Nat) : lengthKey (List.replicate c v) = c * 32^(v-3) := by
  simp [lengthKey, List.sum_replicate_nat]

private theorem classify (h d : Nat) (xs pre : List Nat) (s : Nat) (ok : ValidState pre s)
    (bounds : ∀ k ∈ xs, 3 ≤ k ∧ k ≤ d+3) :
    Split (pre++xs) h ∨ lengthKey (pre++xs) ∈ missed h d xs.sum (lengthKey pre) s := by
  induction d generalizing xs pre s with
  | zero =>
    have ex : xs = List.replicate xs.length 3 :=
      List.eq_replicate_iff.mpr ⟨rfl,fun k hk => by have := bounds k hk; omega⟩
    let c := xs.length
    have hx : xs = List.replicate c 3 := ex
    have sum : xs.sum = c*3 := by rw [hx, List.sum_replicate_nat]
    have hr : (pre++xs).Perm (List.replicate c 3 ++ pre) := hx ▸ List.perm_append_comm
    have val := advance_sound ok 3 c
    by_cases bit : (advance 3 c s).testBit h = true
    · exact Or.inl (split_perm (val h bit) hr.symm)
    · right
      have hk := congrArg lengthKey hx
      rw [rep_key] at hk
      simp [missed, sum, bit, lengthKey_append, hk]
  | succ d ih =>
    by_cases hit : s.testBit h = true
    · exact Or.inl (split_append (ok h hit) xs)
    · let v := d+4
      obtain ⟨c,ys,hp,hy⟩ := pull v xs
      have total : c*v + ys.sum = xs.sum := by simpa [List.sum_append,List.sum_replicate_nat] using psum hp
      have act := advance_sound ok v c
      have bounded k (hk : k ∈ ys) : 3 ≤ k ∧ k ≤ d+3 := by
        obtain ⟨hk',ne⟩ := hy k hk
        have ⟨l,u⟩ := bounds k hk'
        dsimp [v] at ne
        omega
      have perm : ((List.replicate c v ++ pre)++ys).Perm (pre++xs) := by
        have p₁ := (List.perm_append_comm (l₁ := List.replicate c v) (l₂ := pre)).append_right ys
        exact p₁.trans (by simpa only [List.append_assoc] using hp.append_left pre)
      rcases ih ys (List.replicate c v ++pre) _ act bounded with split|here
      · exact Or.inl (split_perm split perm)
      · right
        rw [missed,if_neg hit,List.mem_flatMap]
        refine ⟨c,List.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by dsimp [v]; omega : 0<v)).mpr (by omega))),?_⟩
        rw [← key_perm perm]
        have sr : xs.sum-c*v = ys.sum := by omega
        have sk : lengthKey (List.replicate c v ++ pre) = lengthKey pre + c*32^(v-3) := by
          rw [lengthKey_append,rep_key,Nat.add_comm]
        change lengthKey _ ∈ missed h d (xs.sum-c*v) (lengthKey pre+c*32^(v-3)) (advance v c s)
        simpa only [sr,sk] using here

theorem classify_all (target n : Nat) (hn : 3 ≤ n) (xs : List Nat)
    (h : ∀ k ∈ xs, 3 ≤ k ∧ k ≤ n) :
    Split xs target ∨ lengthKey xs ∈ missed target (n-3) xs.sum 0 1 := by
  have hn' : n-3+3=n := by omega
  simpa [lengthKey] using classify target (n-3) xs [] 1 initial (by simpa only [hn'] using h)

abbrev Included (xs ys : List Nat) := ∀ k ∈ xs, k ∈ ys

theorem missed_succ {h d r key bits : Nat} {dest : List Nat}
    (children : ∀ c, c < r/(d+4)+1 → Included
      (missed h d (r-c*(d+4)) (key+c*32^((d+4)-3)) (advance (d+4) c bits)) dest) :
    Included (missed h (d+1) r key bits) dest := by
  intro k hk
  rw [missed] at hk
  split at hk
  · simp at hk
  · obtain ⟨c, hc, hit⟩ := List.mem_flatMap.mp hk
    exact children c (List.mem_range.mp hc) _ hit

theorem cover_of_included {n h : Nat} (hn : 3 ≤ n) {a b e : List Nat}
    (ha : Included (missed (h+1) (n-3) h 0 1) a)
    (hb : Included (missed (h+1) (n-3) h 0 1) b)
    (he : Included (missed h (n-3) (h+h) 0 1) e)
    {xs : List Nat} (mem : xs ∈ partitions n 3 (h+h)) :
    Covered a b e (lengthKey xs) := by
  obtain ⟨_, bounds, total⟩ := (mem_partitions_iff (by decide : 0<3)).mp mem
  rcases classify_all h n hn xs bounds with ⟨u,v,p,hu⟩ | k
  · have sum := psum p
    rw [List.sum_append, total, hu] at sum
    have hv : v.sum = h := by omega
    have half {ys : List Nat} (ly : ∀ i ∈ ys, 3 ≤ i ∧ i ≤ n) (hy : ys.sum = h) :
        lengthKey ys ∈ missed (h+1) (n-3) h 0 1 := by
      rcases classify_all (h+1) n hn ys ly with ⟨w,z,hp,hw⟩ | k
      · have eq := psum hp
        rw [List.sum_append, hw, hy] at eq
        omega
      · rwa [hy] at k
    have hu' := half (fun i hi => bounds i (p.mem_iff.mp (List.mem_append_left v hi))) hu
    have hv' := half (fun i hi => bounds i (p.mem_iff.mp (List.mem_append_right u hi))) hv
    exact Or.inr ⟨_,ha _ hu',_,hb _ hv',by simpa only [lengthKey_append] using key_perm p⟩
  · exact Or.inl (he _ (total ▸ k))

theorem cover_of_missed {n h : Nat} (hn : 3 ≤ n) {a b e : List Nat}
    (ha : missed (h+1) (n-3) h 0 1 = a)
    (hb : missed (h+1) (n-3) h 0 1 = b)
    (he : missed h (n-3) (h+h) 0 1 = e)
    {xs : List Nat} (mem : xs ∈ partitions n 3 (h+h)) :
    Covered a b e (lengthKey xs) :=
  cover_of_included hn (fun _ hk => ha ▸ hk) (fun _ hk => hb ▸ hk) (fun _ hk => he ▸ hk) mem

end AlspachSmall.Coverage

namespace AlspachSmall.Bitmap
open SimpleGraph AlspachConjecture

private def tableTwo : List (List Nat × List (List Nat)) := [([],[])]
private def tableFour : List (List Nat × List (List Nat)) :=
  [([4], [[0,2,1,3]])]

theorem canonical_two (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ 2) (hs : m.sum = 0) :
    ∃ C : Multiset (Cycle (cocktail 2)), IsCycleDecomposition (cocktail 2) C ∧ lengths C = m := by
  apply realize_order 2 0 tableTwo (by decide) _ (by decide +kernel) m hm hs
  intro xs sorted bound total
  have h := (mem_partitions_iff (by decide : 0 < 3)).2 ⟨sorted,bound,total⟩
  have keys : tableTwo.map Prod.fst = partitions 2 3 0 := by decide +kernel
  rw [←keys,List.mem_map] at h
  obtain ⟨⟨_,cs⟩,hin,rfl⟩ := h
  exact ⟨cs,hin⟩

theorem canonical_four (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ 4) (hs : m.sum = 4) :
    ∃ C : Multiset (Cycle (cocktail 4)), IsCycleDecomposition (cocktail 4) C ∧ lengths C = m := by
  apply realize_order 4 4 tableFour (by decide) _ (by decide +kernel) m hm hs
  intro xs sorted bound total
  have h := (mem_partitions_iff (by decide : 0 < 3)).2 ⟨sorted,bound,total⟩
  have keys : tableFour.map Prod.fst = partitions 4 3 4 := by decide +kernel
  rw [←keys,List.mem_map] at h
  obtain ⟨⟨_,cs⟩,hin,rfl⟩ := h
  exact ⟨cs,hin⟩

end AlspachSmall.Bitmap

namespace AlspachSmall.Packed

def s6_0 : List Nat := [0xf431f521f530f420,0xf521430f531f420,0xf43521f5130f420,0xf5342f5140f3120,0xf425130f534120]

def s6 : List Nat := s6_0

def s8_0 : List Nat := [0xf743f641f531f652f721f750f630f420,0xf746150f753f652f721f630f431f420,0xf75631f7260f743f641f521f530f420,0xf7564f7362f7160f431f521f530f420,0xf75634120f6251f742f640f731f530,0xf7341560f74631f530f752f621f420,0xf637150f746530f752f621f431f420,0xf7143560f7463f5130f752f621f420,0xf472631f75643f7160f521f530f420,0xf73641f57431f72160f652f530f420,0xf75634120f6152740f642f731f530,0xf436521f7462f5731f7160f530f420,0xf73462f36521f5741f7160f530f420,0xf75643120f637251f6240f741f530,0xf6374150f7256431f7530f621f420,0xf75634120f74261f52730f640f531,0xf6374150f756431f72530f621f420,0xf637251f621750f746530f431f420,0xf65743f7352f4621f7160f5130f420,0xf75643120f63742f7251f6140f530,0xf4365721f647352f7150f6130f420,0xf7264351f73650f47521f6130f420,0xf756341f647352f72160f5130f420,0xf753462f73651f74160f52130f420,0xf53726140f75643120f74251f630,0xf75643120f6251740f637241f530,0xf5634721f6417350f7526130f420,0xf5743f7362f5241f7160f5640f3120,0xf75643120f6352f7241f6150f4730,0xf5263741f75342f7160f5640f3120,0xf725361f734260f5741f5640f3120,0xf734251f75362f74160f5640f3120,0xf62741530f75643120f7361f5240,0xf73462f75361f74250f65140f3120,0xf75643120f7425361f62730f5140,0xf75643120f725361f624150f4730,0xf7265341f6374250f751640f3120,0xf75643120f617250f63742f41530,0xf7352461f6274150f75630f43120,0xf5263741f642750f716530f43120]

def s8_1 : List Nat := [0xf637251f742650f417530f643120,0xf63714250f47261530f75643120]

def s8 : List Nat := s8_0 ++ s8_1

def s10_0 : List Nat := [0xf2741f571f381f961f397f087f509f429f852f602f340f635f486,0xf7563428f851f038f468f074f914f261f906f250f792f317f395,0xf648530f9634f704f124f193f783f816f571f208f526f972f905,0xf36219f57042f965f479f209f872f317f146f851f305f843f086,0xf7843612590f640f856f926f742f194f082f318f379f503f157,0xf85603f9743f2405f573f163f915f217f841f694f286f087f290,0xf308569721f0926f571f861f491f378f248f047f634f520f395,0xf52617849f64079f219f309f506f386f820f158f472f341f753,0xf2805916f412096f865f306f740f384f718f924f379f527f531,0xf5962f1739f4812f0657f029f749f872f146f386f531f058f403,0xf92157083f3027f6053f413f940f197f681f569f847f285f426,0xf4703569f16839f0629f579f436f173f827f814f521f024f058,0xf152743f702953f6975f817f085f930f640f683f428f149f261,0xf351246f29756f48259f609f816f319f702f085f471f340f783,0xf0468537192f706249f847f527f134f182f038f950f693f615,0xf164392708f8491305f240f690f759f174f251f862f356f378,0xf97421803f51726843f316f873f941f064f507f956f285f029,0xf0975834f6503f1273f1925f260f780f953f417f482f694f168,0xf819435f16093f3657f1795f205f803f241f269f740f864f872,0xf73042f74620f53160f8290f934f184f512f791f587f659f863,0xf9084631257f38607f5028f742f187f962f156f395f419f034,0xf273846091f031475f5179f807f681f240f258f394f635f629,0xf13964825f7126385f9560f035f870f240f186f491f729f473,0xf072465938f57961f36871f291f481f258f062f437f049f053,0xf24907835f295640f79682f139f162f036f580f715f437f481,0xf3640851f8352416f90571f260f370f956f943f874f297f218,0xf6248195f341685f064782f125f075f371f308f972f963f940,0xf2150784369f371940265f930f759f427f860f164f825f831,0xf064713f8243f6973f5127f6291f593f807f841f049f586f250,0xf12806f04372f3629f5786f4852f496f174f318f951f079f503,0xf0581934726f8256f3516f7831f142f092f649f759f084f073,0xf215049638f17856f4681f0348f274f026f952f735f907f913,0xf60952874f183704f0243f9684f580f162f536f193f729f571,0xf4260738f4031697f6815f7825f805f935f172f920f463f419,0xf81790253f36287f16072f4157f492f391f043f684f508f569,0xf8279305f709625f49513f8173f635f487f219f641f068f240,0xf925831f639482f790641f0512f168f078f472f569f375f043,0xf2963158047f56821903f2495f937f057f817f620f438f614,0xf204685139f750618243f5369f419f079f271f265f847f380,0xf1296503f78391f40861f49528f851f735f643f709f260f742]

def s10_1 : List Nat := [0xf780463f261534f29470f86914f506f390f813f258f759f712,0xf6128059734f6031842f53872f740f914f290f369f517f658,0xf183720694f04295317f75619f309f580f251f862f463f874,0xf8742639051f372841f657021f917f592f469f086f385f403,0xf158643907f5306297f947281f387f048f124f520f613f956,0xf64093182f20865194f734169f529f721f874f358f036f057,0xf02837415f9643185f9178403f752f365f924f612f079f806,0xf26847f0714f3824f1608f9137f2951f964f587f536f093f520,0xf504397812f0283f6913f5809f6270f753f492f147f651f846,0xf38056149f31706f0469f7219f3420f259f851f874f537f682,0xf4687302f971634f3825f7215f9265f085f148f960f740f913,0xf4795816f37841f39425f2651f7291f057f034f863f096f802,0xf127953f815647f40583f6173f2570f903f860f248f941f269,0xf0214839756f7152468f8072f1958f347f904f350f692f631,0xf419035872f93864752f3694f5079f804f128f620f173f561,0xf618304f93586f08759f56370f4728f924f134f521f062f971,0xf1380756492f140935f79582f4862f052f178f347f619f360,0xf826059431f7968304f92480f1739f164f758f207f563f152,0xf51904836f73412059f62931f0357f469f086f781f724f582,0xf496025138f563928f340957f4726f780f168f142f971f350,0xf28609471f3619705f739208f3851f481f403f257f642f695,0xf6382471f6527814f9621534f5048f931f086f975f037f902,0xf94162f82596f02746f38756f19342f084f158f079f305f371,0xf6348521709f72039f87562f40537f429f159f164f806f318,0xf836041275f908746f02935f71349f195f625f842f186f307,0xf50439786f0942758f28469f07352f138f951f261f741f036,0xf14809273f830652f869435f97463f126f042f750f187f591,0xf5039687f5162438f721840f64790f280f137f563f914f925,0xf2853416907f1265084739f46879f592f036f183f517f240,0xf5380472f295164f862034f790658f941f821f731f963f075,0xf9613584720f914637052f421560f871f934f862f975f038,0xf4702853169f19340562f2790364f592f806f715f837f184,0xf871936425f153847926f5730869f605f270f490f143f812,0xf065193784f25908134f75036821f794f614f269f270f385,0xf6582f1748f9314f5203f5921f0975f0724f068f916f436f738,0xf53714260f9134f8163f6874f5796f2951f408f930f270f285,0xf7264805f95140f1307f6120f8691f4792f356f825f349f783,0xf907561f695248f5143f8213f2047f6492f397f063f871f580,0xf704639f26194f38714f8274f5037f2081f513f658f906f259,0xf2834791650f695170f8037f2639f1853f490f527f846f214]

def s10_2 : List Nat := [0xf318462079f3874915f0829f6058f1736f695f430f241f752,0xf62807593f97215604f7183f4258f6478f053f413f902f916,0xf60712f91372f56802f41596f3618f0935f482f758f403f749,0xf6085214973f56430f40718f7835f1695f286f913f274f290,0xf841360597f865340f27309f2470f1839f157f694f261f825,0xf04172869f7912483f26139f3594f5746f063f581f025f708,0xf83160475f052639f172965f5943f1879f421f802f370f864,0xf2590681f3584079f265037f5741f3871f169f429f463f082,0xf2178365904f5846197203f1374f8152f943f057f629f860,0xf819305742f60952f65379f83615f9402f172f870f431f684,0xf94375082f419702f40317f65184f2785f612f690f359f863,0xf9168537f8209463f29347f06513f5269f142f084f750f871,0xf1860524f028573f179083f29407f6219f346f953f487f615,0xf3042581697f029513478f86093f8462f570f217f635f491,0xf641705f839615f863197f218406f5903f275f473f249f082,0xf5027381496f79524361f062193f8092f531f846f740f857,0xf821973064f865341720f470592f5261f904f369f183f857,0xf9184360725f8751246f3169285f0562f308f490f793f714,0xf249651730f50613847f4185270f9780f395f219f628f634,0xf12569407f82950614f90368157f7802f473f624f391f385,0xf86291305f17908f65120f36957f49352f438f278f470f146,0xf8705926f481637f09412f43582f65139f197f257f064f308,0xf735840f968243f756208f46051f90361f127f831f925f479,0xf8319506274f25618794f12864f07358f430f920f751f693,0xf657840912f469703152f43729f36059f802f835f186f417,0xf3721650948f3192685f460281f47952f751f078f340f963,0xf148705396f64903812f563172f97582f024f086f734f159,0xf356940271f5837462f8243906f15036f912f795f870f814,0xf46280731f52749036f0539216f96851f781f438f957f024,0xf3150962784f946821f637581f935607f174f024f295f380,0xf248356071f3472591f940516f630814f875f268f920f397,0xf52704618f36579124f903514f860593f487f317f269f820,0xf02874936f2158379f0913427f817526f164f956f084f530,0xf4792508f0941572f4306912f4659370f682f358f178f631,0xf1749528036f8519604273f81265397f431f864f075f290,0xf0573861492f269534781f563084271f582f907f319f640,0xf0812734f2578f5948f1465f7924f1396f1709f638f035f602,0xf319780f68571f6095f1205f2837f3925f6243f740f481f694,0xf70912f34860f53740f1794f6139f5836f7815f592f462f802,0xf2568174390f62873f0857f4279f8314f9216f350f640f195]

def s10_3 : List Nat := [0xf795826031f947836f0439f2164f0568f5192f184f270f573,0xf95068413f6912403f7153f8743f6294f8561f079f275f820,0xf356809124f51392f74850f1728f4061f6302f783f975f946,0xf56217308f907481f24687f3528f1405f6920f957f316f439,0xf2053417f7091384f04928f7518f9685f6425f261f397f630,0xf8509427f603125f814620f9382f4863f9716f735f195f470,0xf6175382049f378064219f4307f5862f1563f905f729f184,0xf41826907f30271f53861f43952f7563f8794f912f406f805,0xf3059186f093416f21749f08524f2846f5796f720f387f531,0xf596483f275194f265879f07439f0863f0614f137f218f502,0xf5082973461f60913852f75930f8741f8496f721f402f635,0xf185309472f795041638f73460f2480f9682f562f193f157,0xf0297581463f6870951f271935f8213f6942f473f084f065,0xf369281407f71658094f342591f7839f5127f053f684f206,0xf143507928f0427568f9521374f4638f7158f691f039f206,0xf97036415f26871904f6531849f9283f1206f085f275f473,0xf7908651f84075f93605f27830f19628f5213f437f461f294,0xf752091f842950f40621f72869f74658f8163f439f513f703,0xf7091435268f2806574f15836f03184f0295f946f793f217,0xf246085731f72048361f59741f92870f1968f526f934f035,0xf9486025173f691274f926180f28504f7038f143f563f759,0xf085931472f6905371f265781f03497f9251f842f640f836,0xf31628794f04185637f695384f25174f0275f068f903f192,0xf87051624f8695213f0918536f56417f9304f347f297f802,0xf827165943f521397f624053f064192f9086f037f487f185,0xf42685197f2734065f314695f178492f3816f903f820f750,0xf9427350f4817563f6851974f782140f6139f620f380f592,0xf9316402587f3728065914f5709481f2471f692f305f368,0xf8361527094f195780264f68530479f2439f128f056f317,0xf392417560f519683472f359462187f0285f480f790f163,0xf608472f17582f91465f39704f38690f73618f924f502f315,0xf7058314692f362179f02516f86591f78035f490f482f374,0xf821306597f5029473f15807f46390f41962f725f861f348,0xf39152487f65908314f16027f82635f29681f794f507f304,0xf405736129f608274f651302f14259f68439f709f835f178,0xf42785093f2038695f064928f26531f97361f751f481f470,0xf3529087f6948215f3042619f46057f18597f702f314f368,0xf53712860f487093f859413f804751f03652f426f972f916,0xf6537942f5960312f347519f850461f14827f092f863f708,0xf4615079283f8624039175f120873f47259f365f418f096]

def s10_4 : List Nat := [0xf6942037851f346075928f7408621f90527f148f391f563,0xf1973062485f41872596f21740538f75680f316f943f902,0xf028651473f943506271f58709642f93612f831f579f084,0xf9028573f163527f412683f403192f506481f479f807f695,0xf6504387921f520369147f593718f649072f284f068f351,0xf3486971250f26381947f0873156f042857f641f935f902,0xf094625317f736140829f8391506f218430f569f758f742,0xf146930287f72958043f75216384f942681f097f513f605,0xf3590418726f4751206f5829716f8694250f307f348f193,0xf913708462f68795341f7490281f7583042f251f650f693,0xf02816347f65831942f68039514f9250487f712f537f096,0xf746130f4390f2536f8796f7183f4158f9275f9421f802f650,0xf68340f73182f7590f8530f1265f9463f9716f2914f025f478,0xf0975184362f6031f6874f0824f5692f5370f9583f217f941,0xf437819052f58293f7215f0462f1684f0317f3608f695f479,0xf18029365f124309f4869f0735f7138f6472f4061f975f852,0xf4180639f7043861f1953f8215f6925f7305f0972f487f462,0xf50286943f51937f95247f4081f8307f2609f4856f631f271,0xf1473029f640521f83490f7260f5871f6318f5397f842f659,0xf643921f806942f537918f7402f1784f0513f5907f526f836,0xf9136042857f43961527f2641f5683f9084f9502f703f817,0xf305748691f370941856f1726f9287f4602f3804f512f539,0xf0218374f72841f52631f68534f0578f0956f3079f942f961,0xf842965f795382f03912f87360f1625f4713f6814f705f409,0xf3705129684f0839164f42879f6302f5813f0956f174f527,0xf147952608f30924617f12705f8357f4028f6319f658f934,0xf3507829614f573648f517426f8306f1208f9527f490f391,0xf395708421f9043687f065372f8251f4629f8305f916f741,0xf15640279f86952437f821635f3081f3948f9260f705f147,0xf58160243f9721503f2649578f9041f8470f6529f638f173,0xf516309f24756f31725f38219f37814f7920f4850f680f496,0xf6359024178f052194f93082f75843f6972f4607f183f651,0xf803592164f0741936f62579f28650f2734f8713f049f581,0xf30912465f74925860f14396f78159f2750f8362f173f408,0xf268370419f503427f521693f63174f8794f5906f851f802,0xf58342170f5648137f869740f35260f9163f5149f902f782,0xf6135928f8309715f3780419f74962f8124f7560f052f643,0xf62784139f491520f743590f792185f6371f4286f038f650,0xf7041352f8069742f921650f378620f8391f9485f157f463,0xf1574268309f2536084179f137856f3964f0594f281f720]

def s10_5 : List Nat := [0xf9207153846f528194736f4390572f0413f9785f806f216,0xf5602478319f46392750f35814907f8034f9617f628f125,0xf693720514f586124309f92631804f0657f5283f917f847,0xf53691f97803f46573f20486f95274f58290f6170f381f241,0xf5387296041f47903f56207f85246f94805f6391f128f731,0xf205784639f156273f12586f83042f14708f9435f096f791,0xf25908136f3860579f19285f47356f24870f4169f403f712,0xf52809341f970642f786304f50269f57216f9184f371f385,0xf6394175f0916437f726038f31805f47968f1592f420f582,0xf8405316972f1257386094f74620f30856f3924f817f519,0xf0436852f079648f935062f130956f15738f2478f127f149,0xf9651348270f463819257f805937f85306f7941f261f042,0xf5197360842f50729438f3574021f61782f6418f965f309,0xf956134870f536804917f1283964f03792f5062f274f581,0xf870493516f41928563f79526481f05738f2130f690f427,0xf924685f139725f482617f021496f409183f7805f365f037,0xf8025694371f59270631f904821f685742f7938f416f350,0xf048561297f095142638f068753f196473f2817f250f934,0xf1948056273f0796143f0421786f936475f3528f185f920,0xf084361297f50387496f2468190f140627f5937f531f285,0xf28736190f97056812f30427159f947526f8460f358f314,0xf461958370f9308652f5348790f9631574f7182f214f602,0xf68031279f38526419f8716342f0481537f4759f902f560,0xf1683479052f1784039265f1859427063f1469f573f208,0xf024369785f94835f03164f82906f70814f27391f517f625,0xf84170926f465312f06194f37280f97436f59381f520f578,0xf8591307f8120634f37905f24657f29615f38049f147f628,0xf3641859f684251f340628f09657f80317f20537f479f219,0xf0586379214f438251907f16203f48069f42756f953f178,0xf608351f852031f786340f756482f17429f62149f905f379,0xf5173946028f31297048f526190f43681f57803f742f965,0xf208563941f784260953f469713f81503f68291f704f275,0xf3026875941f3927406f3790524f08217f56481f961f853,0xf270436819f65874902f3841695f79305f80642f125f137,0xf27509314f02953874f79125803f36284f07156f186f946,0xf9152748036f8704926f346095f824175f21650f381f739,0xf124307869f48253906f513629f837561f17204f749f508,0xf856197302f2963481f0938715f625314f07594f724f086,0xf92465783f85963472f9730214f625091f71840f351f680,0xf94258160f1739684f9205387f5621307f74082f951f436]

def s10_6 : List Nat := [0xf9615243087f8653720914f362859471f29381f064f057,0xf9261307584f068214f938056f971520f953781f427f364,0xf421578096f8593041f291635f820734f268317f749f605,0xf37059164f72569314f426358f294038f157902f781f608,0xf29056871f9572803f2079485f435160f741963f813f426,0xf6859173f1472083f9261840f6578249f397064f053f512,0xf2956307481f8504261793f09153728f860257f469f341,0xf6902483175f582164970f419362780f306815f259f437,0xf2134687590f6514938270f3791850f6352471f804f926,0xf2936850741f609134875f18273596f6251794f083f240,0xf487052631f937240861f602834795f8530921f571f694,0xf6273195084f58693471f03578216f81492563f024f790,0xf526804713f943827516f90564873f97024185f630f291,0xf15208f3928f6312f4872f5068f9735f6475f4309f7140f196,0xf562179348f6318f2738f0253f4192f6051f4096f7495f870,0xf57431682f49651f2091f0795f3927f3085f6042f8364f187,0xf7192534f309426f6804f3721f5961f0582f0756f9783f814,0xf4196278f13758f09517f6821f3029f4352f0638f4650f497,0xf207184f309287f15834f4759f2197f6931f5263f8650f604,0xf3875612409f5843029f7069f5280f6318f7462f7153f941,0xf568079342f02137469f4951f8291f7261f8357f4058f036,0xf734960f80364f52793f59120f4290f6582f7415f1786f183,0xf5342086917f137904f85294f0647f8127f3059f2836f561,0xf057826319f8604153f74259f6129f0372f1807f6485f439,0xf12830796f50278413f08524f4639f9062f1957f5681f743,0xf702956843f403581f369751f7821f9461f5062f0839f247,0xf85240736f0281465f095316f7512f7491f3879f0843f926,0xf7043529f7426831f0287365f4169f5819f7215f8064f390,0xf85172f46391f30481f65349f73860f2974f0952f7805f612,0xf0975283164f95843f19624f07812f2749f5371f0365f608,0xf964730821f835261f65178f70639f5948f0924f0275f431,0xf38251947f3927146f97026f18406f3580f8756f4213f590,0xf72519630f734285f174862f41879f8390f5920f1356f640,0xf3847590f3581429f517802f56270f4960f3197f1682f643,0xf9478203165f3570421968f46258f5180f7341f3906f927,0xf9308742f205368f437960f956170f4126f1849f3158f752,0xf2418075936f152786043f583746f9284f1697f2190f035,0xf9430718625f72846319f5693780f0924f6120f7514f853,0xf135027846f704283915f8129730f6258f9065f3496f174,0xf562184309f36147529f19642835f7802f7049f6058f371]

def s10_7 : List Nat := [0xf178352096f68415f04758f79260f27318f9305f4912f643,0xf96140537f206831f25817f63915f08759f4926f3470f482,0xf5390618f3865970f78052f63402f91482f1742f7315f964,0xf1408526f879246f943820f72184f95713f9156f3705f306,0xf2485631970f925730814f60439f86153f7264f8712f905,0xf917583f251649f206531f826950f36814f4097f2487f037,0xf0219357846f14290386f807315f50436f5962f7182f794,0xf583417209f284653079f394086f73124f5781f5062f691,0xf8124975063f9203461f8659047f52693f8072f5841f173,0xf342817950f49613580f1902684f78360f5746f9273f251,0xf51829630f85397160f52648319f37024f7412f5786f940,0xf1627530948f5142978f640738f960521f3174f6593f208,0xf916348725f68024715f269318f921407f7503f6094f853,0xf478293160f9635127f0852649f502486f4183f5917f370,0xf25304816f05874312f6907514f173659f3928f7942f680,0xf71524083f1306879f4357209f0741285f6293f4816f569,0xf7906283415f3650842917f746953120f4930f5278f816,0xf64705183f92173f58413f62791f56087f52869f2094f430,0xf4918572f716593f09253f87026f04796f05148f8213f643,0xf951473f843607f569283f90217f85031f86240f6194f275,0xf8346509217f75314269f86394f25807f18206f0374f915,0xf246580791f052694873f75381f63951f29068f4027f134,0xf4396571208f8704195f249736f82746f53092f5061f381,0xf260958371f56394027f147803f19705f81692f2435f648,0xf295648071f9147863f5820613f05183f26904f7349f257,0xf27946851f35629074f4025931f16387f06918f7305f428,0xf6849275130f638209f185647f526193f43780f5970f421,0xf042759683f6082134f520718f629051f19784f9374f563,0xf28169530f68794152f721365f708391f42906f4058f374,0xf80462973f2419350f9607284f863095f87431f7165f521,0xf3826941f4085736f0247935f3487290f86071f9561f251,0xf5179204638f1284957306f87096531f25086f3419f247,0xf3148560729f712804359f381574620f42509f3786f619,0xf206948315f658173f916805f478293f214097f5307f246,0xf51863740f5308419f794620f125783f561728f3429f609,0xf3706481f3085926f4905283f978651f753961f2140f247,0xf2695081347f5294160387f6402853f684215f3907f197,0xf1439278065f475312096f85970362f948371f0524f816,0xf316258497f568274039f605781429f153802f7190f346,0xf3471590826f781694052f8419356f7921385f4206f703]

def s10_8 : List Nat := [0xf1827539406f12486379f08317462f1430785f2965f059,0xf570241869f627943851f05364719f0652873f2931f480,0xf917368025f51874926f84135072f79604385f4216f309,0xf0948172f14692f30524f83160f87562f39586f19735f704,0xf579302f386917f61582f70412f43187f59063f80564f492,0xf1938604752f4287309f58079f51720f64135f16348f629,0xf051964283f34812709f60295f78049f61358f75263f741,0xf7052649381f865724f378596f06143f29740f82190f513,0xf690847352f7836592f617058f28130f43912f41579f604,0xf92063874f09571648f704312f68142f50396f19735f582,0xf79612483f7058291f6490275f81530f62593f68740f413,0xf938251407f084375f160927f691203f85947f65318f624,0xf48379260f1825369f470213f508649f71658f72415f093,0xf5286470f5813906f3591240f263480f92716f15794f783,0xf2561948307f1358026974f7863405f95173f24609f218,0xf7169253840f586034279f50814736f02649f87512f139,0xf574396128f268153097f029563148f04917f05246f837,0xf41683952f405718f792158f703462f637490f69135f802,0xf5071639f5862043f182469f413729f847560f97830f215,0xf9572468031f6502839471f637092f406978f85341f251,0xf9703842651f061437829f4058127f680253f13957f496,0xf6184093572f42978051f47038659f134602f73691f825,0xf472809513f942075681f21483506f716403f78529f963,0xf0518249637f52138097f7295861f3026419f40653f478,0xf531682407f934627180f8795063f2914730f58496f152,0xf726905843f79420815f87406192f6830714f95213f563,0xf48517263f70861953f87569213f25097418f60394f042,0xf3470691f580497f217309f278650f624183f846152f539,0xf9064217835f315286970f162758f049365f914802f473,0xf2137409685f93827564f9516307f062435f084192f178,0xf852793614f280731569f4386209f753064f219504f187,0xf642738190f14752693f40297863f849512f716580f503,0xf8219346507f3085147f4816902f4068359f526317f279,0xf695137280f70216438f5841930f7186529f624753f049,0xf41369278f57903421f38052649f1702859f406537f618,0xf653074821f2951386f1405739f0258179f2780634f496,0xf25978146f40513728f7583960f1249086f4302917f635,0xf9156803742f0469578312f2536097148f7058162f934,0xf2859706314f8396150274f926573081f35217864f940,0xf8462917530f368215974f185607394f613872509f402]

def s10_9 : List Nat := [0xf4731f5043f6203f9183f8270f6590f4296f7849f5712f1586,0xf04831726f8296f5308f1578f9420f7950f4637f4193f1256,0xf0384617f29360f3504f9680f5126f7813f9741f2594f8275,0xf752641f386924f2847f3187f9407f0958f1539f6305f2061,0xf562479f93750f84063f0352f1943f8270f6129f8715f8146,0xf0786539412f483192f9726f5182f0859f7361f4057f4603,0xf092483716f7821564f4369f8026f5072f5397f1304f5819,0xf30697514f26495831f4817f6391f8256f0924f0735f7802,0xf95703f74853f97120f18729f8260f3168f9436f5046f1425,0xf7560928134f52140f80715f9461f3795f2487f3869f0263,0xf635940281f513726f97843f6914f8306f7421f0857f9250,0xf27960348f7859261f52047f1942f3641f5381f7093f5680,0xf28743519f970683f509427f0814f6371f2031f5648f6952,0xf3159620f7361925f871405f3865f4906f7439f8270f1248,0xf3659408127f9058264713f7830f4253f6920f5197f6148,0xf430586192f93120f41870f71594f7265f3796f4806f5283,0xf07249513f437128f93602f41690f8053f8791f5647f2685,0xf7405392f4859136f17096f75149f1862f3428f0652f7308,0xf8243065f180796f157209f12537f3926f4786f4138f0594,0xf2536907148f385726049f47316f1879f2951f6508f0243,0xf812795f156829f349078f396475f7361f4031f6052f4802,0xf0618372495f64875209f743129f5391f4071f6582f3086,0xf269517834f792056814f048219f9364f0316f5273f8075,0xf1405392687f0615943f9024836f7319f5746f2807f8521,0xf602918573f46159708f2174965f3041f8627f3905f3824,0xf06827915f25648370f17853426f4957f1392f0814f0963,0xf80946537f03127f83405f16284f63918f7159f2475f6920,0xf2173965f605974f58041f35724f26309f9481f8613f7820,0xf286397f095387f657349f24719f03162f5812f5041f4608,0xf3480962157f41920786f42597f06135f7182f0394f5638,0xf472618059f642531709f51978f30214f9283f4068f6375,0xf4792516830f8756412f071396f42053f7263f9085f9184,0xf028653917f49627503f425806f37816f4138f5921f7409,0xf857914302f5071869f1378065f53612f4627f0924f8394,0xf27483590f15708639f1430582f60492f7169f4256f1873,0xf6021859374f251704f841350f657283f9430f9687f2619,0xf562903147f4935870f812064f519680f6173f8243f9527,0xf37021865f05791483f608243f529478f5931f6271f0469,0xf12978356f5241739f8430751f509468f2806f3196f4027,0xf1793426f0784156f8375046f9130274f3596f8290f5812]

def s10_10 : List Nat := [0xf3579604281f2739058641f43871659f2915f0847f2630,0xf7569481203f462508317f270685934f9782f1635f0914,0xf7435621f58631f05246f78095f07384f72039f1694f2819,0xf817430f720463f86293f56907f51428f21605f9531f8794,0xf3564179280f7819052f69402f86374f51607f4312f3958,0xf837126905f31684275f95147f65294f30819f0634f2870,0xf4190725368f374951f750469f02178f42603f9382f5618,0xf537469281f0219384f906524f75031f08597f7862f3416,0xf86097425f75692830f872134f35917f62041f8051f6394,0xf79241863f5120783f5617280f04396f84625f3190f5947,0xf179425083f075926f820396f584091f53746f1634f8127,0xf94150682f2081795f587396f721904f83624f3164f0753,0xf4953618f4029173f5687241f574690f25831f0793f6082,0xf1879426053f4837520916f1743085f72140f6395f2869,0xf5284970631f471209583f19356278f69241f5037f6804,0xf420635197f348596271f078652149f18046f8293f7305,0xf27856930f160947f359184f297051f526837f6314f2804,0xf6915348f6590241f128047f263975f294607f3781f5038,0xf0627384159f3640758129f302561f243508f4719f8697,0xf8256319407f647908512f8172053f695730f4293f4168,0xf4605937281f49621380f78435291f097563f4207f8516,0xf609784125f726934081f74928615f246370f0583f1953,0xf5271360849f93785042f0216479f3826570f3514f6918,0xf034871596f391402756f8509731f4708352f2168f4926,0xf697180243f85741392f62194078f0516483f3725f0659,0xf83752190f74318650f71649582f97841536f2604f9302,0xf864197f50396f04836f51708f27590f42137f43529f2618,0xf1805739426f859136f07483f25178f96027f14092f5346,0xf205863147f8096157f35607f42830f43918f25946f2971,0xf84271365f07341869f02975f26495f80612f04783f1935,0xf486519072f920346f750839f78253f41859f17406f1263,0xf64830791f1350827f185602f90415f69378f49263f7524,0xf0391425f3169785f9283604f84751f68095f26437f2071,0xf52460817f879215f627405f631948f95370f39614f0382,0xf6290843f5861249f502837f187253f46917f06514f9307,0xf9257086413f3582409617f384956f50621f74302f8197,0xf7960351842f940875261f4365821f39071f68374f0295,0xf1795386042f47580269f07846315f56182f90341f9372,0xf061587293f209471836f59731480f42570f19682f6435,0xf5680742f169584f319750f281736f783512f64390f9204]

def s10_11 : List Nat := [0xf8095721643f850624917f402537f369281f15684f0397,0xf6294130758f72195638f9374280f846051f40253f9716,0xf435807261f425906387f3056491f869371f79215f8204,0xf526908713f91428573f94072165f602974f15038f8436,0xf7061924358f0573814f9036284f0213968f74651f2795,0xf421509736f78430695f9402713f0829147f16258f5683,0xf84791206f37518294f62593071f2785314f69083f0465,0xf368207f192657f406127f438052f318490f514693f9587,0xf0748391256f43095726f928516f794053f142087f1863,0xf092613874f591428630f120648f534972f156937f5708,0xf7180536249f0614392f3158740f683709f846572f5219,0xf914860735f36158724f4650817f903126f382049f9257,0xf59743820f36072481f26403785f716935f086519f4129,0xf421657308f1526078f3179405f3685914f964720f2938,0xf31975264f58127369f9386074f5178290f165304f2480,0xf6520937841f9426350817f2746038591f157043f8296,0xf57064281f5043916f2179530f2783149f6258473f8690,0xf7425938061f6275031849f158297364f7865340f2091,0xf6817352409f2748506139f26308791f34657028f9415,0xf0839756142f095273186f304921785f70519634f4628,0xf517068349f205874631f809357261f379652840f2419,0xf79265f64859f13086f34906f12539f70283f17405f87241,0xf9305874621f34816f02514f70831f95724f56973f68290,0xf619437285f796318f35268f04293f07146f50847f51209,0xf62490538f4630257f82715f87921f07348f69140f31659,0xf92840736f609174f386149f81597f25034f56213f80275,0xf0294318f7504839f647285f42691f51709f68730f52163,0xf7831642950f2740851936f60375f28435f17968f49021,0xf4293850f368720f473128f691435f25906f75180f17946,0xf7839651420f862943750f472530f63190f12846f79581,0xf5680294731f28795041f7584391f60381f64253f09627,0xf204165378f031925746f8051263f79681f43958f07249,0xf507384612f17902658f06913478f41530f29368f57249,0xf243871f375281f027493f685092f046597f69153f60841,0xf1849725036f35708641f265839f174069f02159f37824,0xf170283465f847590361f853726f529780f91406f24931,0xf5214807963f1839426f3478291f720465f95860f17305,0xf647039152f29578140f7908342f605849f63128f71653,0xf65912403f14738605f64317082f753902f48529f97816,0xf352196487f0627138f5740286f1850794f59361f09243]

def s10_12 : List Nat := [0xf28160374f59126870f6480293f5790438f15694f71352,0xf8643529071f9150362847f0493875612f31427f58069,0xf9270513864f7369524f809162f358714f065793f12048,0xf639250741f28791534f712683f594608f209657f13048,0xf873649025f9380417f0591843f356821f074296f57261,0xf86935042f51834607f1726309f587412f731659f20849,0xf38469120f8735240f6274150f5792816f685943f17093,0xf3942618057f2834651907f869253047f714859f63120,0xf8534126f0948752f1647938f5630719f7240513f82960,0xf8513694207f5382971460f16590372f5740862f81934,0xf9350684172f659430782f420963157f9738521f80461,0xf0314758269f127860539f18407925f42083716f63495,0xf163825079f264817530f586927341f39087421f06594,0xf1278069534f839471f630284f097524f165073f915862,0xf924073851f6534718f803614f931264f972506f578209,0xf83462507f08517963f394275f160473f914820f812956,0xf42971358f4093786f7594302f912836f062518f470561,0xf8279156f0814395f0647312f9617830f842635f704925,0xf9578064312f0369147285f86249351f702561f483790,0xf4190725386f824736950f348517920f126578f139406,0xf7250964183f6207439158f2875304f0617948f659213,0xf6042978351f705936841f34620857f3096521f819472,0xf706419258f173690428f657493021f6279538f431508,0xf1702569384f30957264f47863150f24973581f806192,0xf570824361f049537862f92503817f90658413f746912,0xf6578309412f064829135f3618527f4796802f5934071,0xf1462097835f70396524f80637195f4316829f4812750,0xf172609385f965087412f42531970f5948637f4618203,0xf385260741f16930428f75368491f73465029f8721590,0xf64957380f21970534f68715293f62031485f74096182,0xf8517963402f9564273081f9350786214f5748316092]

def s10 : List Nat := s10_0 ++ s10_1 ++ s10_2 ++ s10_3 ++ s10_4 ++ s10_5 ++ s10_6 ++ s10_7 ++ s10_8 ++ s10_9 ++ s10_10 ++ s10_11 ++ s10_12

end AlspachSmall.Packed

namespace AlspachSmall.Packed

def a12Mask : Nat := 0x672003e4000ac0081003003301a0a0020

def a12_0 : List Nat := [0xfb80fa78f437f560f5b3f94bf2a5f69af192f146,0xf4921f6a91f4b96f5a2f87afb08f650f35bf734,0xfa652f0b96f8a50fb378f435bf9a74f921f461,0xf560b3f5b80fa78f437f94bfa25f192f614f96a,0xfa9437f4b87f069bf5a80f652af5b3f129f641,0xf49b37f41653fb508f60b4fa78f2a5f9a6f192,0xfa5612f4b873f9b52f3b05fa608f4196f7a94,0xf06a78fb35a8f14652f92af473fb05f9b4f619,0xfb5608f49b37f4350bf29a5f1964f6a21fa87,0xf4b5a7f9160bf25341f6508afb873f964fa92,0xfa5612f9b341f94b52f647a9f06a8bf80537,0xf460521f961fb80fa78f437fb53f94bfa29f6a5,0xf8b9a50f56a2f4961f0b46f912f734f35bf7a8,0xfa21478f5b80f64b0f943bf6a91f5a73f9652,0xf47a253fa5608fb378f96af146f9b4fb50f129,0xfb5a608f529b0f4b37f912af6941f4653f7a8,0xfb94780fa73b8fa9125f435bf6a29f560f614,0xfb92508f165a2f694b0f19a64f473fb53fa87,0xfa25087f5b473f643b0f619a5fb8a69f9412,0xf46a537f4125b3fb08fa78f605f94bf92af916,0xf608734fb056a8f6921f4b91f47a9fa52f5b3,0xf506492f147356f69b5afa912fb80fa78fb34,0xf537a60f92143bf74b08fa25b8f69a5f1649,0xfa53b87f64192af0b9a8f5694bf60521f437,0xfa65378f4605a7f2143b5fb08f9b4f9a2f169,0xfa96087f29416afb05219fb5a8f3b47f5346,0xfb49650f37419bf612534f6a780fb5a8f92a,0xf3b9a87f4165a7f5b4960f46a253fb08f291,0xf614b80fa96478f92a534fb05219f37a65b,0xf0b46a78f9216f8a9bf560f437f5b3f2a5f914,0xf0b9a746fa652f4961f5a80f35b4f873bf921,0xf49b52a7f35a87fb08f69af129f461f4b3f605,0xf92a8064fb9143fb478fa537f6521f05bf9a6,0xf3529a87fb9608f412a7f4619fb43f5b0f5a6,0xf619a250fb5a73f4b087f96a8bf4921f4356,0xf3b46a87f5a960f5349bf12a74f52916f0b8,0xf8b49a50f560b92f6a21f4691f78af347fb35,0xf4612a8bfa5b087f529b3f437f650f9a6f491,0xf5b06492f74356af4b961f9a21f8a50f378b,0xf43b0691f64b521fa8056fb8749f37a5f9a2]

def a12_1 : List Nat := [0xf6412a80f435b87fb05a73f6925fa916fb94,0xfb052143fa619b5f694b80f46537fa87f2a9,0xf60873b4f534192fb5a749fa650b8f69a21,0xf4b52a61f08b9a56f350bf921f964f734fa78,0xf65349b0fa925b37f4b87fa508f1964f16a2,0xfa216087fb9146a8f9a5b4f50b3f2965f473,0xfa650b47f25b8061fa5378fb9643f914f92a,0xf78a69b3f129a746f6534b0f5b80fa25f941,0xfb921478f56194b3f69a250fb5a80f6437a,0xf6478a21fa529437f653b9af0b4196f08b5,0xfa65b087f614b350f9b8a521f437f964fa92,0xf5b8a692f349b087f053b416f5647afa912,0xfb473508f965a214fb06a925f4619b3fa87,0xf9b41652af5a60fb80fa78f3b5f473f946f219,0xf46508a73fb478f69b0f2a61f29a5f5b3f914,0xf7a692508f165a2fb9a8f4b06f3b5f437f491,0xf4608b537f569b0f16a94fa78f4b3f2a5f912,0xf943b8a52f53780f9b47af6a21f9641f5b06,0xf4780b921f52a60fb3465f8a94bf35a7f691,0xf49216537f460b91fb805fa52fa78f69af3b4,0xfa5069b87f52a80bf4b37f5643f916af9214,0xf069478a5fb52a73f9a612f4653fb914fb80,0xfa64b5378f96143bfa2947fa5219fb80f650,0xf5649b873f4160b3fa25b47fa805f9a6f912,0xf560b8a73f4619b3f4b5087f9a214f5296a,0xf8a94b537f0619b8f5643b0f7a5214fa296,0xfa2506437f478a561f912fb35f9b4f96af0b8,0xf6052a741fa694b08f8b37f5346f9b5af912,0xfa2941608fa650b87f5219afb964f473f35b,0xf29a64b05f12a8069fb5a73f49b87f56143,0xf2169a8b5fb35a780f92a641f473f650f9b4,0xf65a74b80f125b964f49a873f6a291f50b3,0xf961435a2fb460873f9a6521f49b8a7f05b,0xf805a6437fb491253f692a741fb9a8f65b0,0xf612a94b0f653b914f8b5296afa5087f437,0xf435b06a9f8b374650f6921f4b91fa52fa78,0xfa8b34612f9b087a52f4b537f491f6a9f506,0xf8b347a50fb49a8735f46521f9b061fa692,0xf69435a21fb9250873f4b8a91fb065f647a,0xfb3741960fa9216435f56a780fb52a8f4b9]

def a12_2 : List Nat := [0xfb412a608f50b91643f4965b37f25a9fa87,0xf08b469a5f60b9478afa735612f925b341,0xfa2564378fb4129a53f06a749b5fb80f619,0xf94b56a21f9b087a52f43b8a961f053746,0xf64735b921fa87f4b3f914f0b8f5a2f6a9f605,0xf60b374921f9b41f508bf5643fa87fa96fa52,0xf496125a87f346a7f4b91fb08fa92f5b3f560,0xf5b08a9612fa2947f4b91f73b8f6a50f3564,0xfb05649a73f43521fb92a5f8a60f874bf916,0xf652a914b0f508b3fb96a5f12946f437fa87,0xf9b53746a2f69a521f056f8a7f491fb08fb34,0xf4160b9253f56a780f4b37fb5a8f9a21f649,0xf8b437a560f50b9a2fa6478f9412f691fb35,0xf534b06912f647805fa5b92f8a73bf16a94,0xfb8a291653fa96087f5a6412f473fb50fb94,0xf478b9a561f506492fb08a73f96a21fb435,0xfb05619473fb9a608f53412afb52964fa78,0xf9165b87a2f5a96412f0b35f08a6f473f9b4,0xf46a735b91f478a529fa9612fb43f08bf605,0xf805a96147fa294b37fa8b06f5b912f5643,0xfb53741960f6508a21fb46a78f9a52f49b3,0xfa64925b37f419b087fa534b8f69a21f506,0xf52147a69bf8a50b37fb491608f6435f2a9,0xfb92564780fa5b3412f916a8b4f35069a7,0xf96537412af43b52916f5a60fb80fa78fb49,0xfb94608a73fb5a61478f534b0f2a91f6925,0xfb437a5219fb0561478fa9608fa2946fb53,0xf921437a5bfa8749652f64b350f916afb08,0xf608a9b341fa78b4912f5374692f56af05b,0xf416a50b87f3b5692a7f435219bfa94608,0xf473b56921f9b052a61fa5346087fa94b8,0xfa53416087f6473b8a25fb50f921f9b4fa69,0xf5216943b0fa29146537f6a80fb478fb5a9,0xfb469a5378f129b347a6f52a80fb560f419,0xf6437a29b0f52169a8b3f4b5087f914f65a,0xf9605b3741fb4356a780fa94612fb925a8,0xfb08a96473f0619b87a5fa653492f4b521,0xfb34652a78f94b08a612f19605374fb5a9,0xf5087a6912fb561492a8f37460b9a5fb43,0xfb352146a78fa508f065bf473f9b4f961f2a9]

def a12_3 : List Nat := [0xf50b87a2143f4b37fa608f925bf9461f9a56,0xf5374608b92f69a21f491f5a6fb50f8a7fb43,0xf5214b9a780fb0653f8a5bf9164f2a69f473,0xfa5346129b8fa6087fa9652fb473f5b0f194,0xf14780569a2fa5b37f49253fb4619fb8a60,0xf537a291460f496a87fb5a9f5612fb08f3b4,0xf9653b87a21f0529a6fb5a80f473f641f49b,0xf560b87a912f43b961fb4735fa6492f5a80,0xf6921437a50f49b087f52a8b3fb564fa619,0xfa53780b946f4b5691f47a8b3f60521fa92,0xf5a78b94160fa964b08f256af347f5b3f921,0xf419608b5a7f8a94b37f0529bf612af6435,0xfa521469b87f5b49a80fb0653f16a29f473,0xfa2506914b8f6129b34f5b0873f49a7f56a,0xf5649b08a73f4125b87fa291605f96afb34,0xf6947a253b0f9b80561fa5b4378f46a921,0xf652a8749b0f4b805a73fb53f614f921f69a,0xf92a5b80641fa8734b96f6521fa947f50b3,0xf419250b873fa9b35608f47a5bf2a61f649,0xfb947352a60f5a964b80f4165b3f129fa78,0xf291650b47af69a53b80fa64378f25b941,0xf5a2169b873f47a8065bf943b052fa9146,0xf43b508a291fb9a65378f496125a7fb064,0xfa29b065347f50873b412f9a61f5a8bf649,0xf9b356147a2fa52194378fb4605fb80f6a9,0xfa564378b92f8a914b350f5b0612f96a74,0xfa734165b92fa52196478fb49a608f53b0,0xf56914b8a73f46a9b5087f612943b0f25a,0xf650b478a21fb91437a608fa529f964f53b,0xfa943560b87f41296a5b37f52a80f64b91,0xf9460b378a2fb805347a69f4b5a91f6521,0xf506a78b912f469a80b537f5a29416fb43,0xfa65219b437f5a964780b3f2941605b8a,0xf6a921473b50f6435fb08fa52f8a7f49bf619,0xfb3529416a78fa508f64b0f19a2f69b5f473,0xf529147a80b3f4b873f9a5bfa612f650f964,0xf43b50619a87f52a73f96412f65afb94fb80,0xf05b912a6478fa53b8f9437afb0614f6529,0xfb9412537a60f564780fb8a5f961fa29fb43,0xfa806419b537f5a94b0f8b347f256af2169]

def a12_4 : List Nat := [0xf7a53b914608f52a8b0f6a921fb4965f437,0xf06a219435b8fb9a873fa74b05f5692f416,0xfb5064129a78fb08a253f473f65af9b4f961,0xfa21608b9437f65b478af5a92fb053f1469,0xfb087a291643f4960537f5214bfb8a9fa56,0xf7a619435b08f214b8a9fb96473f560f5a2,0xf735a9214b08f569b8a2f6a7491f643b50,0xf64925a73b80f4169a87f2a65b91fb0534,0xfa219b534608f50b47a92fb873f1694f6a5,0xf5064129a8b3f6a780b91f965b4f437fa52,0xf9a6053b8741fa5216437fb92a80f694b5,0xf8a61250b347f56492a73fb806914fb9a5,0xf41296a80b37f5a78b943f5b4619a2f650,0xfa8065374912fb87a69250f9b5af416fb34,0xfb5296147a80f506a219b3f8b437f5a946,0xf564b912a780f4735b8a61f06943bf9a52,0xf529b416a780f5a21960b3f465b8a9f473,0xf412a960b537f5291643b80fa87fa65fb94,0xf8b506a92147f256194b08af469b3fa537,0xfa9b87346052f9653b08a74f4b5a61f921,0xf34b52169a87fb9147a6508f460b35a29,0xfb052946a873f435b80612a7f9b41f569a,0xfa9250614b87fa80b3564912fa5b96f473,0xfa8b96537412f061943b5a78f46a9250b,0xf6147352a9b80fb50f43bfa65f78af912f469,0xf4352169b08a7f3b87f564bfa506f941f92a,0xf6129b8a74350f80b37f465bfa52f914f9a6,0xf608b37a52941f46a87f534b0fa912f65b9,0xfb912a8056473fa5b87f94352fb0614f6a9,0xf53b416087a92fa8b912f5b0f6a5f496f743,0xf80529a614b37f947a21fb960f5346fb8a5,0xf80b416a92537fa74912fb9643fa8b5f506,0xf50b8a9216473fa56087f25b96af4b3f941,0xf6508a73b4921f9a5341f69b52af7460b8,0xf5378b06a9412f91647a2f5a80f65b9f4b3,0xf91460b8a7352fb947805f65a21f6a9fb34,0xf612a9478b350f734196af9b4652fb5a80,0xf5b37806419a2fb947a50f534b8a6f9612,0xf6a921478b350fb9437a80f564bf5a2f619,0xfa734619b8052f4b356921f6a5b0fa8749]

def a12_5 : List Nat := [0xf492a735b8061f50b3478af56a912f64b9,0xf5b8064912a73f78a529b4fb056143fa69,0xfa29b35061478f437a9125bfb80f65af946,0xf52916a743b80f35b412a87f9465af60b9,0xfb47352169a80fb92a50643f8b56a7f194,0xf160b53478a92f52a649b80fb37a56914,0xf96a87350b412fb347a25608fb9a5f4619,0xf4350b9216a87fa914608b37fb5694f52a,0xfb91253478a60fa946508b37f614b5a29,0xf43780b96a521f5061947a8b3f5b46fa29,0xf437a8069b521fb35a2916478f50b49a6,0xf50b8a2196473f6143b529a780f65af94b,0xf64378a50b921fa7419608b352f6a94b5]

def a12 := a12_0 ++ a12_1 ++ a12_2 ++ a12_3 ++ a12_4 ++ a12_5

def b12Mask : Nat := 0x18c0001b00152007e004e00c004050610

def b12_0 : List Nat := [0xf26bf386f17bf579f815f248f027fa31f04af309,0xf3159f8275f81a4f079f1b7f26bf402f3a0f386,0xf82b6f3026f7042fa390f8513f1a48f17bf579,0xf842b6f3826f17bf518f072f957f3a1f04af903,0xf2486bf3026f8172f3958fb157f0a4f790f1a3,0xf38179f84a15f7095f631bf2b7f03af286f024,0xf1a075f182b7f3859f0279f3a40f8624f6b13,0xf317b6f2481bf583a1f093f04af720f795f268,0xf3071af95840f13975f20a4fb627f281bf863,0xf70395f17285f02b79f63842f1b68fa04f3a1,0xf82795f1a075fb6317f04a39f26830f1842b,0xf836b24f04af13af71bf903f581f270f795f826,0xf3951b6f2486f7185f2038f709fa04f13af27b,0xf31790af81a4f2704f2630fb157f682bf9385,0xf381b26f857b6f9715f428f027fa31f093f0a4,0xf0a31b7f72409f8395f286bfa184f3026f175,0xf75826bf1842bf304a1f1795f0a39f072f368,0xf1a386bf27136f93075f2097bf581f04af428,0xf15726bf1384af07b24f82036f95817f093a,0xf3a0486f13824af2b6f71bf702f903f581f975,0xf5790a1f84a395f3186f2038f4270f26bf71b,0xfa36840f2831a4f70395f7209f185fb26fb71,0xf2630a4f1b6827f84095f13975f7b20f83a1,0xf7b1859f275136f1703af28390f2b684f0a4,0xf17204af51b639f862b75f824f30af790f831,0xf27036bf81a402f31790af8426f157bf3859,0xf863904f751820f831795f2b1a4f726bf30a,0xf3a42b6f720a1bf079384f581309f826f751,0xf726395f0a3179f0481b7f824a15fb68302,0xf8275904f024af7930f31af863fb62f1b7f581,0xf97584a0f286bf3026f7042f3159f83a1f17b,0xf362851af2486bf0a4f318f71bf795f039f072,0xf1a3027bf842b6f3826f1758f3159f0a4f970,0xf240936bf70a1bf71302f83a4f759f185f286,0xf1362795f82403f71b20fb7586f0a39f81a4,0xf427183af7931bf0a159f03682f70485f2b6,0xf07b1584f381726f82b6f0a42f3a1f957f039,0xf1b6390af0713a4f84203f826f72bf579f518,0xf13a4097f0a1593f381b6f207bf8426f5728,0xf5826b79fb20751f1724af81304f390af638]

def b12_1 : List Nat := [0xf4a186b2f170285fb13627f3048f90a3f759,0xf0368279fa02483f07b1a4f31759f815f6b2,0xf2b70486f209758f30a159f1724a3f1836b,0xf402b71af627031bf0a39f795f815f824f683,0xf27593a4f0485179f031af8263fb186f2b70,0xf158204af7b68130f26384f3a09f271bf795,0xf5813627fb159386f3071af97b20f0a4f284,0xf1a426b7f84031b2f3a0759f7209f815f863,0xf263951bf82790a1f71386bf024a3f48570,0xf02b751af8270936f2481b6f583179f03a4,0xfa42b683f0a17284fb702631f759f185f309,0xf0728139f204857bf830a426fa36b1f1795,0xf420971af36b2840fb726831f3a0759f815,0xf631b7958f183af04af284f093f715f26bf072,0xf1a382095f7039f2684f1758f1b63f40afb27,0xf27586304f1a028f83a4f5139fb62f71bf907,0xf1b68204af48362f13958f72bf03af715f907,0xf1397b628f83a15f36840f0759f024afb172,0xf2071a36bf0384af1857bf97240f9315f268,0xf72684a1bf3182b6f3958f042f03af715f790,0xf362b1590f86b704f024af7139f8572f83a1,0xf31b6820afb26307f04279f3859f81a4f715,0xf7130286bf936270f3851af2b184f0a4f975,0xf395172b6f18203af7b1385f2684f04af790,0xf84071a36f13026bf790a42f7582bf39518,0xf70395182f20a17bf83a426f048579f136b,0xf81a03975f09513a4f270f683f248fb71f2b6,0xf3685704af902b183f1795f031afb627f284,0xf813042b6f072851af09362f83a4f71bf759,0xf09317584f2b683a4f7951bf07263f81a02,0xf7b683095f72b1a39f620713f815f428f04a,0xf81309724f951b683f36204afb7582f170a,0xf7b263859f4203a18f139075f8271b6f0a4,0xf7182b639fa0427b1fa486203f7095f8315,0xf07284a39f638517bf8130426f1b20af795,0xf2b713684f203951b6f183af7285f0a4f907,0xf07b281a4f85139024f726b1f386f03af975,0xf03182759fb7048362f1793af1586bf20a4,0xf2684031bfa4207951f71836bf5728f90a3,0xf830957b6f1a39702bf248136f85172f40a]

def b12_2 : List Nat := [0xf207951b6f24036857f284a17bf390af831,0xf39572b1afb7902836f85170a4f2681304,0xf26307184f27b68590f839751b2f0a4f31a,0xf7582031bf81590726f483971a0f24a36b,0xf3a15842b6f0a4f286f138f795f71bf093f720,0xf02836b759f7039f2684fb172f185fa40f1a3,0xf2683a407bf1720af136bf842f597f851f039,0xf18590263af830a4f2704f1793f6b28fb751,0xfb20751836f3904af72859f2684f130af7b1,0xf1b628590af203a4f79315f18407f7b2f683,0xf302795186f839075f2b6f1b7f428fa31f4a0,0xf30284a179f6240a3f7095f8315f6b18fb72,0xfa18407b63f72b139f03859f20a4f175f826,0xf857b63904f827951f2b1a4f3170af68302,0xf3a1702486f82b795f1b6275f039f0a4f138,0xf702b1a385f0a4863f71826bf90427f3159,0xf851703a42f3902b6f81b726f13840af759,0xf857042b63f7203159f0a39f184af682f71b,0xf36b20751af38597b1f81724f0a4f862f093,0xf3951a0728f204a36bf7581bf90317f8624,0xf315904286f4a07938f03a1b2f726bf8175,0xf0a3684279f204a1b6f8517b2f70395f831,0xf186b24075f8362795fa130284f0a39f1b7,0xf71a486209f39582b6f3a07b18f4031572,0xf0724a1839f8631b795f2048f2b6f751fa03,0xf04863a172f0a426b79f70395f8315f182b,0xf20957b184f038271a4f63158f3a079fb62,0xf0486b1a39f70362815f831795f20a4f27b,0xf72036b159f81a39075f7b24831f4a0f268,0xf5709386b1f81a36204f031724afb28597,0xf3159072b6f81793a42f57b1a038f84026,0xf284a097b6f17593042bf027f815f386fa31,0xf390a482b6f713026859f0724f157bfa381,0xf72b186395f3a4097158f207b6fa130f842,0xf857b203a4f936b17240f1a0795f862f831,0xf17b684095f13970a42bf726385fa18203,0xf1724a3095f836b1a075fb281397f86204,0xf27b6831a4f09518263af1758402bf7930,0xf172093685f031a482b7f240a381b6f795,0xf27590a486bf3628f0397f185f17bf3a1f042]

def b12_3 : List Nat := [0xf7b1583a042f82b6f3026f184af9713f9570,0xf7b1a042859f3a481f715f207f309f638f6b2,0xf36b1a40759f2817bf8315f2097f6842fa03,0xfa175902483f1397bf30726f82b6fa40f815,0xf04271a3859f70315f36b79f284a0f2681b,0xf63a097581bf17b24af0384f1593f286f072,0xf3681b7240af317028f1a485f759f2b6f390,0xf4097581362f17286bfa3951f0a483f702b,0xf8624079315f02b759f1a036bf1827f384a,0xf20793851a4f840a36f957130f1827bf2b6,0xf2b63851704f720a31bf184af975f628f903,0xf93627581a0f82031b6f7042bf83a4f5179,0xf7b1a486395f83a0715f27904f20318f2b6,0xf8207951b63f2713904f7b2685f81a4f30a,0xf3951a482b6f0386279f075813af420f1b7,0xf138624097bfa175820f3a48159f3072b6,0xf30971b2486f3826b759f185fa13f072f40a,0xf1362840975f7039586bf2b17fa024f1a38,0xf3824a071b6f97581a30f20486f1593f7b2,0xf7b62813a09f1b270395f7584a1f204f386,0xf831a097b26f36b1584af720395f042817,0xf0975136b24f1728593af81b7026f830a4,0xf2793a481b6f86317095fa042b751f3028,0xf263851b790f86b275931f03a4f170af842,0xf2b15790384f39586b71af18263f0a4f270,0xf71a4820395f1862b70a3f836b15f90427,0xf826b713904f1a368572bf3815970f024a,0xf1a386b2075f8427b1395f30971826fa40,0xf3a15970286f390a427581f0384f26bf17b,0xf203a4817b6f2b1a075938f31586f42790,0xf3840a1b279f36b715824af318620f7095,0xf85793a1b24f036b728159f3862071f04a,0xf27138590a4f3a1b682079fb751840362,0xf039571b624af8402f72bf31af836f097f581,0xf30a427b1586f183af9075f4820f1793f26b,0xf368420a1b79f07159f8275f3a40f6b2f318,0xf036842b7159f281b6f79385fa31f072f4a0,0xf85904a172b6f3970af28136f24830f51b7,0xf0a42b638159f204857f7039f71bf826f31a,0xf3a42b681709f840275f1b795f8362f1a03]

def b12_4 : List Nat := [0xf318597b240af1b684af39028f72630f751,0xf1b27590384af70426bf820a36f3179f518,0xf8597b13a024f07281a4f390f683f6b2f751,0xf263a1b75904f81720a4f3079f682bf3158,0xf362b790481af8593072f831b6f024af157,0xf703a1b26859f093184afb72836f204f751,0xf3184a0957b6f304271af862b15f283970,0xf275903a481bf3862079f0a15824f317b6,0xf3a4028517b6f9381b275f031af4862f790,0xf390a4815726f2079586bf82403f17bf31a,0xf03824a1b759f8620a315f27936bf04817,0xf3951b62704af483097b2f820a136f8175,0xf186b240a395f79026385f7031a482fb71,0xf31b6859704af26390a184f2830f27bf571,0xf5793a1b2048f2638170a4f827b6f15903,0xf3a1b7268409f8136b2075f03824af1795,0xf724a309581bf9751a0483f8207136f2b6,0xf1a42036857bf93a0482715f2b6f138f097,0xf0a4263851b7f27903a186bf57139f4820,0xf097b62831a4f7159368420f27581bf30a,0xf863951720a4f3857042b1af7b6281309,0xf863902751a4f0a38597b624f1703fb281,0xf7185903a42bf0a157936284f1386bf270,0xf0793851b24af571a3628409f6813027b,0xf30a4826b1759f815f368f204f790f27bf1a3,0xf18420957b63af7039f8315f71b2f0a4f268,0xf3957b204a186f271b6f3158f824f079fa30,0xf3a409581b726f1a075f38420f82b6f3179,0xf04285936b71af3184af02683f72b15f790,0xf8204a1b75936f158427f2b6f079f3a0f138,0xf7b1a40263859f157248f82b6f3071f3a09,0xf24093a17586bf8270a4f7b159f3620f318,0xf85972b631a04f2093a4f183075f862f17b,0xf7b68240a3159f8571a4f263907f381b20,0xf84a1759302b6f097b13af2704f8362f185,0xf2684a309571bf072831af397b6f042f581,0xf268579304a1bf31827b6f83a024f07159,0xf824a075931b6f158403af362b718f7902,0xf3a1586b72409f1b284a07f3026f759f813,0xf824a390751b6f7b263859f03184fa1720]

def b12_5 : List Nat := [0xf38426b71590af027931a4f758630f81b2,0xf7b1586240a39f036b2759f170284af183,0xf840a136b2795f38157024af682f093f1b7,0xf86b2095713a4f04263851af27b18f3079,0xf0271b68593a4f0a1362b79f518307f824,0xf0426b179583af8270931a4fb75186302,0xf81a409362b75f2486b13a07f1795f3820,0xf0a482631b759f2b6851a307f38179f024,0xf862b1a403975f24817b63a0f13827095,0xf204a1586397bf183a095726bf1703f482,0xf8513a097b624f3681a402759f283071b,0xf1795824a036bf04862b751a39f270f318,0xf7b62481a0395f863a40972b15f713820]

def b12 := b12_0 ++ b12_1 ++ b12_2 ++ b12_3 ++ b12_4 ++ b12_5

def e12Mask : Nat := 0x7fe003ff001fe00ff007e03f01e0f0630

def e12_0 : List Nat := [0xf0396f8a63f1286fb426f5046fa584fb708f7a18fb3a0f9520f9b2af175bf7492f3415f3791,0xf36875f9156f0b85f24b5fa2b6f729bf371bf4026f1482f0316fa081fa438f9074f793afa95,0xfa8703b6fa41b0f204bf9680f5160f5346f2136f948bf7a24f725bf9182f5a38f971af3957,0xf804b1a5fb371950f2435b81fa027b68f62b907af60314f69751f2a365f87493fa9284,0xf0a25349f0641875fb269307f29b0837f1b42863f12048b6f479af3b5af658af17af195,0xf147b259f0631a75f6208b15f4a8730bf816a243f7128640fa0935f6b3a9f485b9f729,0xf5a936b0f17a8625f7319065f2a30469fa143870f2816a47f4802b9f124bf358bf795b,0xf2b59371f80426b7f5a64790f5631827f352a194f1583a96fb14a70f30a84bf92068b,0xf685a93bf83a175bf1256a79f6048159f302a461f3427805f6370a82f2b09f41b9f74b,0xf062538afb059182f6429758fb9a6348f3a15b69fa413b72f1b47a56f37120f708f490,0xf3b28790f507438bf1408a7bfa529184f531a268f16a9572f173a065f496b02f4639b,0xfa362718f94b831af405396af03b975af4219073f85b1647f5206841fb082956fb2a7,0xf56a0913bf60b1f286bf4a8bf759bf3796f4026f3580f7150fa925f4839f7a18f2147f243a,0xf7864b2a1f3a418f3421f0b84f50a8f0728f65b1f9251f6302f9b60f357bf95a6fa739f974,0xf485b0927f94350a7f87b20f4170f3a57f6130f8193f68b3f24a8f69b4f651bfa259f621a,0xf956b712afb24a638fb4720a3f5708162f5b9037af31a829f06841bf915046f435879,0xf43a927b6f8524706f8026957f39b16a5f8b417a2f973b0a4fb21365f1a8405f19038,0xf7b309581f4b9a128f647a20bf5a4062bf392750af9416537f6915243f138bf708f6a8,0xf62b7a419f2059481f56a8392f731a082f5368b9afb609743f164b587f03a24fb1570,0xf12793b65f95b0716fa2b1346f49b78a1f47a058bf5204a37f24835a9f036819f2806,0xf1970638afb952a64f518b69af314920af085b739f28430b1f56872b3f1624057f4a7,0xf61b38405f97814a36f7513f9a71f25a1fb435f0293f8b95f0749f2a64f860af2b08f726b,0xf16438702fb8041563f1973af490af27a9f528af6059fb039fb742f5317f84b1f5b68f62a,0xf09641735f203a9b47fa482570f68513fb340f6180f2194f8793fa1b7f5b29f65a2fa6b8,0xf5692b347f3a851497f36024b91f4a70fb127f8617fa081f8264fb038f5093fa259f6a5b,0xf3a47b850f28391a57fb1629435f51709f6a25f4b21f8731f63b9f046bf068af8420f9a7,0xfb04682a7f3a621580f9256b413f8175063fa0735f9b20f91b5fa961f843bf478af4279,0xfa726b395f304b1786f918a370bf4a096138f5743f1285f6025fb805f97b2fa642f1a94,0xf30a42819f846271a3f569b1473f579a8b21fb6043fb594f0529f087bfa586f02a7f613,0xf6b341782f18b02973f51a39647fa8356049f4a72bf5907bf68503f25a61fa2480f9b1,0xf2873b594f6b853a14f638a5702f160527b9f1740a92f90b13f3084fb2a4f697af6815,0xf1b34a975f41693028f17b86049f0b264738f72136b90f4b52f8a35f92a5f0a65f781a,0xf8b571364f97a1b086f9b430251f2a358741f5942738af507b6f406af2816f293bfa90,0xf2b348a57f247b0938f0a1564b8f92a4136bf403a6219f97185f69a78f02537f061b5,0xf358a49b0f0297a5b8f6125937bf564072a1f574263a0f419683bf31784f2b18fa609,0xf72b58140fb7a39120fa9b48650f3874a1b6fa8b31792f3516280f46a52f73495f906,0xf5603924af6375190af2b64853af431b8259fb7186204f072169b5f879af147afb083,0xfb0752914f0a831594fb2a65871f03b96182fb5a73906f8053a97bf86274fa124f436,0xf0614a8b2f6308791bf46a9370bf842a3596f405a7183f7251a094fb312657f829b5,0xf1a950b42f04736a52f9b5680a4f192a7834f3b69718afb2703158f9061b753f6284]

def e12_1 : List Nat := [0xfb6531a829f4173f6974f2194fa684fb261f5781f0936f50a9f583afb725f07a2f03b8fb04,0xf2569b48a1f079431bf6b28f57b8f3a5bf9035f1605f4780f1738f6a93f2a46f27a0f4291,0xf17a382659f90841b2af875af186afb358f6051fb925f3021f74b0f736bf4972f4396f40a,0xf3946a170bf4305187bf8a5b920f128bf652bf7385f9635fa413f6248f9061fa740f972a,0xf92b65a317f615b9472fa46803b7f0287f8a63f9506f4093f2485f19a2fb1a0fb814f357,0xf4b972a306f3586b709f1a8b5049f6951243f4137f80b3f29a0fa784f526af1756f82b1,0xf83417a265f4861502bf379604a1f2703a649f759bf125bf0a8bf39a5f0918f7428fb63,0xf937a8b416f0463b597fb6038249f4a1b2508f8719a65f2a09f2186f3574f027bfa513,0xf296047358f0b93a572fb81a0943f807915b4f503178a9f1256f4a26fb7a6fb142f863,0xfa8b241690f5b3874a9fb0643a79f18507b63f086571b4fa519302f6a12f8492f7352,0xf63804257af20a34158f62a17b30f691b2735fb4681390f9216b874f9b5af7950f48a,0xfa391468b2f4056b729f1736a025fa79b3581fa43870b5f09a84b13f1247596f8062,0xf617953b8af74b06283f021a9b63fa2570493f842965a0f851b7a46f5b278190f431,0xfb78639042f69b3807a4f49a52613f741956a3f7206b815fb48a2971f128530afb05,0xf61579b382f1b408a653f6905871a3f14302f937a2f918b5f6847bf60a94f5a42fb072,0xf974b85362f5a1b93782f034a7195bf27b6180af413b2f07512f64905f6a840f869a3,0xf87205b69af51b862497f36184092bf346082a59f19b7af0b417f530a6f25831f73a4,0xfa1b724863f178526b43f47a20b516fb8a570412f508193fa0659f28309f973bf4a69,0xf9a4831720f61b3492a5fa637419b8fb793a1264f42587a0f6075b28fb69530f1508,0xf63b270418f42157b038fb47a29508fb931a4625f9a028561f34906af378a5f96b17,0xf5126b903af437a182b0f068794a25f07429638af8531b720f4617593bf9a65b841,0xf46352b097f961758a42fa7b948065f130a628b5f1b6834072fa2059f1a3b4f91873,0xf57a1362b8f06b94a218f461b07928f9147350a6f2715a3904f52034bf659a8f387b,0xf804b2735af34850961afb38712495f682031b74f360b81529f9b62a41f079af657a,0xf641b90872fb248a9716f5192a360bf39470a521fa40283756f534b7a18f305968b,0xfa17b48593f53708641bf6092a478bf0a6152834f962057a81f2b0365a97f94213b,0xfb8153a0274f634a91bf4265839f25b0731f5792b30f87b95a2f8046f17a6f8a14f096,0xfa819734b50f07a693bfa514603f52b7163f1b80942f8574a13f829b6f59a26f04872,0xf8b39150426f17356b2fa825963f0b4a792f83147b5f09a6487f180349bfa572fa160,0xfb96408a517f835b241fa94b821f056a73bf85920a4f2639075f2a30687f97431f61b,0xf620b83a179f356b1470fa750492f3b580a9fb24a609f8134b72f6378a51f9125f648,0xf63a91840b2fa0941528fb837924f746a508f3b172a4f7b6531af5b93068f9570216,0xf7a36b48502f608b7925f8715a962f1935b2a6f4759b31af40a86f30b18f34907f124,0xfa427860953fb0251a83f375849a0f62971b5af46319b80f2b439618f6b705f47a21,0xfb071364958f03486975f192a4065f274b6a08f3a902418f1a739b26f78a521bf35b,0xfa358702416f493752b60fa138b4695f684719b5f0a79263bfa8215034f7b1809a2,0xf13024759b8f7a6584093fa4162b705f286b49a15fa0b53f38064f963b1f72a8f9217,0xf5724691a80f436258b09fa61b95384f92a3156b7f6812b470f73028fa7140f39a5b,0xfa2406b5379f930512786f9174a5280fb92643a81f8b07a165f2b4136a0f4957b38,0xf97a4213850f064827b53f3a69b1874f3b862a917f8a16392b0f41520f6b495fa075]

def e12_2 : List Nat := [0xf473815092af7b3586402fb61a57039fb41780a65f3a7960b84fa91b28f6312f4952,0xf9253874a16f059b31462fb79428a06f73a5840b1fa9308b572f218634bfa709156,0xf97126a380bf564702a1bf925730481f0a42b3596fa728b4905f851436b7f39a861,0xf0a4861b257f2490b3a56f360512874fb935802a6f92731a8b5fa7b403819f96417,0xf7935a2b081f4950738b12f628a043f157b4a9f684725bf6587a14f9b30fa613f6920,0xf126b497085f65b3a17209f24a9305f1b74829fa7360b2f41386a0f4357816fa59b8,0xf140a756928f8360b2a597f3027b519f3526471f08a9437f48b3a12fb168509fa4b6,0xf843a590b16f302a4758b6f4213b796fb29a8705f39b41728f1940a735f081a6f256,0xf3a87b12059f0a462573b8f47903681f271a9b04f82b51694f3856a291f35a706b4,0xf259a468b71f34b1a62057f047a58139f9153a87f65b941f270384f6b0a29f063b28,0xfb316528047f07358a29b6f9627514b0f871b5a46f342059a6f38b2197afa184930,0xf6a20b37591f8569247a03f7804935a1f86079a34bf62b90513f846b721f4a825b1,0xf3a92486b17f9520b346a7f90a18b536f3804a2b91f7856214bf93061574fa82705,0xfb379a02856f4805921b7af940b25713f4b9683072f87460915bf8143af62a1f35a6,0xf8307295b16f578214b936f73a94026bf48a791352f058b3471af4a51806f90b2a6,0xfb624905173f1480a25b93f38a579204f8596a12b7f9a3560b81fb16827a4f74630,0xf60725a8314f7b569a0284f3a421750bf862a19430fb16378592f93518b6a7f904b,0xf29b4a685307f87b34f7405f2164f1a94f1597fa837fa093f6913fb081f265afb825f2b60,0xf682b9053174f40a751fb81207f365a80f4b6a38f693b0f5261bf4a973f59278f2a194,0xf746093b1a25fb716305fb8720a6f819437af0482b97f0b42138fa415f3a95f586f926,0xfb25a9618370f5902643f928a06bf5197240f871a65bf7a21485f1b7493f6308fb4a3,0xf3a2b1560847f0958142f64b8792fa7b3968f0436a17f9b035a4f50a916bf1382f527,0xf2053168b4a7f87b596af3b91257f2a9746bf043651bf0392817fa149083f62485a0,0xf0b726159348f36a124b8f5a928f4a86f7918f5096fb206f53a2f73b5f1703f941bfa047,0xf628a30579b1f4a273580f74931a0fb4295a7f8b6a917f514683bf1843652f02bf690,0xf4b5a0827169f92638b07f21b7530f15904a3f4681a93f658419bf42506a7fa873b2,0xf37a9b856240f0b52781af4153b708f6195af8a43f12a3fb682f471bf9057f6920f4936,0xf30b65287a19f502163a9f80647351f4a83b570f2a096fb729f4179f48b2f431bf85a6,0xf296315a74b0f8b34a061f4052b938f5907b6a8f62178f27308f53a97f41b56f2a194,0xf952738a46b0f912b8536fa93b4751fa287b943fa7924865f5b170f26a0f1306f4180,0xf13527960b8af037a2649f85041293f6b287195f07b16842f081574af4b5a3fb9a63,0xf0619b4825a3fa81b6357f2907856af40b51739f08b24695f3b741268f9720af431a,0xf81a0596b247f649317258f2a79f0b19fb5a9f384af628af0412f5361f0756fb437f803b,0xf142a0693578f309a7b584f794a82b0f638bf6208f5640f13a6f74b3f1527f9b12f95a1,0xf7b815246039f2736b50a9f53861a49f14802a69f409bf2856f7a34f75a8f1b07f12b3,0xf9584730b162f609b2718af207a3968fb642a978f125349f51a4b7f50413bf6380a5,0xf7483b26150afa4308b579f870b92a5f90468125f206391a8f56a3fb496f1724f137b,0xf25b4073a196fa793b6158f9b284635f031724a6fb8092147fb18349a0f8756f02a5,0xf30915684b2af96a718b02f625739a0f46b78350f79b14280f13b5a472f4958a163,0xf84059317b62f253b0a864f8091a574bf34158706f816a9203f973a2b56f1b94a72]

def e12_3 : List Nat := [0xfa5603782419f6a0275b94f6b2a15348f3a4096258f79218b4f59361b0f08a7f13b7,0xfb902a574638f706825319fa162940b7f95b1430a6fa4805173f39a812bf724b658,0xf03816527b9af02a4873b6f5b4907128f192b04753f1a34268bf415a7936f80596a,0xf0296a17483bf50461372bf4a068791bf75281436bfa94265807f8a39bf3590f2a51,0xf3046a9527b1fb8a126943f7142850a3f29b06815af802b61974f87a4b53f570936,0xfb20475a8693fb4352a081f6278419a3f7b09564a1f794285b60f9b830512f6a731,0xf62a471b5039fb465a1920f0752b8349f5806137b9f3a721486bf81536a042f879a,0xf7a2b3815049f68a1b47392f1306b9f580a69f52163af5b7146f9a420f87534fb0728,0xf8026b51a397f17568a9b24f8361294f2590b37fa691850f2a531b8f7460fa7b4f340,0xf483657120a9f1b4a306879fb907a25f3504269fb615a80f73418b2f47b31a6f9582,0xf0b5869a1274f2a81795034f64837b90fb87a493f56b2807f25316a0f63a5192f14b,0xf06a3795b812fb69a740831f1642b705f539b4826f86309175f78a52fa1492fa0b34,0xf2490735a1b6f6413a802b9f7b850639f47215b30f1829a756f71952a48fa6834b0,0xf28640b35917f6a8743025bf36905a2481f3a08b7f0614a7f21a94bf839265fb9751,0xf94a30861b72f7364b25a09f156207a9b3f148b6a2f839571af5b06918f8247f4053,0xf26b953a4178fa0347b2185f938b1a7024f4b372906f79680b5f319a256f048a615,0xf1b80592a743f61a830975bf27b9140a65fa3b02815f70694853f217864bfa42639,0xfb7a52148039fa0691b8274f2b61a35709f5b046879f2651738afb3185024fa6349,0xf0b64a395127f574b29618a0f37a204fb91a68fa97b35f84903f85260f87142f365b1,0xf9274b053a81fa4208695731f5146b2f609a71fa58362f03b56af49b78f79340f821b,0xf7a83492b651f03b95748162f5369a12f724a39f860a2f1b873f085b7f4b091f6a504,0xf346051782a9fa586147b903f5297a63f21a4b57f8426b0af04918b2f0837fb13f596,0xf02b3658479af1530687a4b9f28b1a59f71240b5f6438072f137b694f093a25f618a,0xf2836159a704f96843a1b720f0b53918fa852130f749b2a5f78b4629f3b6a417f650,0xf5b729164380fa2586390741fa71842b35f60b975f628b49f04a873f021b6af3a951,0xf485b7036a12f3a4928b6057f347952a81f783b09651f4627a91f39b40a5f0861b2,0xfb6257391480fb2a30517468f069b58312f356a9427bfa16340795f7a0928fa4b18,0xf563a41297b0f968135742a0f78a5b9302f438259170f1a73b6485f4b806a9f162b,0xf20b7485a691f8609b42a357f95b618a037f0514a7f43b1a9f8b2563f72931f46280,0xf9482a063517fa6219b43805f7b18a46930fb86140f73a924f7856b2f1a75b3f0259,0xf31259b7a086f3a2850b1749fa843579061f918b5a6fb29a46f41562f03872f3704b,0xfa392b618704f85791306a24f8690a7253bf056347bf4621a5bfa837159f9b14f082,0xfa7b63851492fa6825743b91f93a8b12056f95b460afb248790f3726180f7135a40,0xf03865b9a724f135a4608b29fa690734852f5947b621a0f163975f814b3af71b028,0xf0a281b79536f275048b93a1fb490378a56f4385b029a7fa42b316f807146f25196,0xfa825097b164fb5a60387192f6b93518402f7a9568b342f47580a1f94b0736f3a21,0xfa643b781905f72b539a8061f7a40b926385f152f4b1f3a1f965f86bf749f284f0a2f037,0xf15092a64b73f20a971486b5f72b081a4965f934285f5a3fb83f063f19bf126f704f8a7,0xf28190b6534af95124b3786af629308b5741f84063afb25831fa71f50af946f702fb97,0xf2a738b59416f4b187925063fa09b2748651f5a40b7f64208af28531fa96b3f07193]

def e12_4 : List Nat := [0xf2580374a91bf06871a3b492f59318a26b70f35b904f6a0b84f382796f241f75af651,0xf2b386049517f93564821a07f6a9b8142503fa58743f61920bf62a809fb4a75fb137,0xf4830b17a629f460739b512af69578a042b3f3527b4f180974f8b6502f1685a9f1a3,0xf758a41b3620f784b03516a2f1a7346095b8f2b680a5f49650f21938f79a31f9247b,0xf746258b0391f84953a207b6f87a43b92150f5b27906f9a0416fb1824f8375afa631,0xf13b6204857af15378a09642f807b94165a3f29a6347f8603952fb2a4fb05f18bf179,0xf817a6039524fb74692a5831f9163b2078a4fa34b821f75b0862f56b973f1504fa09,0xf68704b21395f026481973b5f38b7a609415f4a96b17f243a0b9f82a1630f5a8f725,0xfa6421739b58f02b87a96513fa57b1862904f614953bfa250743fa197280f84b063,0xfa864b039215f347918b6025f73842b90561f41a269580f7b5fa70f827fa94f31bfa36,0xf60b349257a8f1950246b783f36584a9b217f74b51a082f416970f1b8fa35f903fa26,0xf7596a04b812f73865b0914af79428053b61f3a851b264f9b702af931a52f630f487,0xf5817b49630af7908b5264a3f568a92b0741f391a78204f21b384f59b613f7506a2,0xf78062951b43fb7219a04658fa82416b5097f170b2a538f02574a3f49b368f96a13,0xf4a7869521b3f9b7502a8413f562b4079a18f715a6b803f190b536fa382460f2749,0xf9a42b618035f1579026834bf92a1704658bfb05a74963f84125b73af827f06af913,0xf029b463a817f569403b127af435826b791af9578316a0f4739a2b08f8b506f1524,0xf591a370b428f948357b1620f5b64a930812f3692b8741f068a79b34f7150a2fa56,0xf62b17504a39f568b743021af24159b60837f978a25361fb07a94813fb46a09285,0xf9a58034b127f137428b9605f683902b714af3b61a70495f63a0b5f481926fa8752,0xf26085b9734af7b8a5396120f83a749152b6f756a0b3142fa1b4829f6403f950f178,0xf956a48b2731f0b615793428f7b3850a2941f74b12063a8f904625bf869a1f035a7,0xf03b58a62719f64a2507b813f6b1295a0478fb2806537a9f8397514f943a16f0b42,0xf413905a8b62f6359b17482af30b46927a18f6079a3b521f3785194f756802bf04a,0xfa814697b530f87a605129b4f027583b61a9f708b263194f2a59371b04f8256f4a3,0xfb3a94612708f7b4296a5381f147a26305b9f9758431b60fa40b259378f0a15682,0xf180953a2647f579b6a83420f4a5b2786930f137b065829af1b36f70af48bf125f914,0xf2a8153b6094f75b869a0312f74192b0583af9b170843625f7b4028f1a56f46af937,0xfa78b1924356f90852a4637bf759403a8621f5a938472061fb50796f4182bf0a13b,0xf087b143a952f2739b8516a4f697a03812b4f635b07192a8f906284f1a56b3f4057,0xf507b1a63492f09317584b26f5a3786b0419fb83021564a9f182a796f8a0f247f3b5,0xfb1564739a28fb4a05279136f9240b587a16fb3a57094812f53417b9f38a60f6208,0xf0a1357428b6f1480b3a6925f4637209a81bf349705a2168f304a719f562b78f9b5,0xf630b718a294f3748021b5a9f38279516b4af609b875341af56913b240f2586fa07,0xf915b8607a34f124759a8036f509b38271a6fb2973185a04fb14a25396f87b0264,0xf1856b209a47f3a521b94807f5927b3640a1f342a87960b5f14b83057a6f862f319,0xf826914a73b0f9278a64b530f483975612a0f9524718b63af943158602bfa1b705,0xfa4038217b65f9053b1a2487f4720a618b93f062b49158a7f3a925b08641f59637,0xf5b863027a149f1b39f26b9f7469f05a9f240bf784bf38a4f1573f1607f82a0f2581f56a3,0xf904b7281a653f73a41f5138f0643f2961f95b1f2086fa749f70b9f8a57fa250f8b24fb63]

def e12_5 : List Nat := [0xf491a86b02573f4a70638fa5b39f8130fb278f5928fa642f1562f9b16f4b71f9047f0a35,0xf60b5781492a3f9b35a17f0a68593f4261b83fa827469f137b2f90251f04b65f4807a,0xf91b65382407af39b871af2750641f20b4736fa592b34f52a097bf496a8f03168f581,0xf65374b8291a0f4a95830f7249680f312a579f63415b2fa8716b3f846a7b1f9b0f250,0xf9a3b27581406fb92a056f830795af71b024af9125b80f461537bf6287493f13486a,0xf5127438b609af19b570a4f246af781af308afb371f6531f94b7f250bf8695f6293f8204,0xfa4731502b869f279381b4f49b60f5b09f2a19f357bf8a30f1287f4658f6341fa526fa70,0xf7b805346921af281b065af7316a85f2b915f94b5f386bf7241f7048f3026fa390f9a47,0xf24159306a8b7f58162a73f63b0978f13a9b47fb128346f2b50a19f570496f8025a4,0xf407258b36a19f84395b71fb928614f3a790b1f69a502bfa083564f873062af12475,0xf503b91642a78f6975b483f2094a1b6f718bf2568f06a8f270bf3147f9512f3a04f39a5,0xf28a7b9405631f0a25b193f970b41a5f74815f46a3f7853f6271f602bf9086fa924f83b,0xf6803b1975a24f85931a07f156b94a7f12835b4f7348bf0274f69a3f0625fa618fb092,0xf843b26519a70fb58a1420f37b1286af9b816403fa290f475af5972f3605f8317f6b49,0xfa78359b02146f36b5849af79042513f168b4729f62b39f0a43fa182f05a8f7560f7b1,0xfa026841b7935f72a69b80f5b217a90f4b637529f8591603f51a46f043bf4782fa318,0xf49356b0a1827fb3708514f97b8a205fa5b24687f31926048f1257f36a4fa903f61b9,0xf0478b5126a93f3b209164f81a53706fb4283a71f084a257bf14963f56b9f8a05f729,0xf0731b24a6958f9025178af0b81975af16043b7af364129b5f394b650f3862af4728,0xf3426809b15a7f5917b360f8720a6b5f8a49312bf48352a16f3a928140f9756f4b07,0xf35b24197a068f6958137bf6349a871fa2748051fa39b0756f28b304a5fb4621f209,0xf4026b839571af47850a63f842b7906f318a9b07f29615308fa25641b3fa5b49127,0xfa562190b8743f185b49603f7083f5163f2a05f7295fa179f42b1f6a7bf8402f864af9b3,0xf756b91482a03f153402978f9a724b0f807bf6250f13b2f1a5bf9685f4617f3a49fa638,0xfb208739561a4f694257183f13a8274f509b843f03b64f5b068f7a51bf92a07f9a621,0xfa2b794150638f5b4319a72f84071b92f620af1a42f6574f8b61f093bf8730f6859f53a,0xfa50487b16293fb972a4683fa80b5947f51734b2f0753f6913f658bf2418f09a6fa021,0xf27835640a9b1f70b863429f59371a82f80962a31f6a51fb602f7b4af5748f5b30f491,0xf4b359127a086fb294071a6f15839026f4a573182f2a96305f60b5f47b1fa843f978b,0xf72508b3a1469f473156a09f16b287a9fb5a26817f0634a857f20b9f4830f421bf593,0xf04172a69b853f70918a463f4921a783f5680b247f15b48206fa31b625f97b3f50a9,0xf4213a596870bf6a920471bf9160852bf62a14903f4a728156f50a84397f738bf53b,0xfb2596348a170f41279b380fa0578192f265b7a90f3a51b647f316a4b85f6824930,0xf5b418a927360f0b34691a78f35a2b68f970a31bf2409561f4a62039fb7528f47158,0xf0412a87b6539f97203185a4fb4736a9f25b3869fa750643f0842b17f8b0a162f591,0xf7a640921583bf720869b1a3fa943560b2f6170a8bf1930578f5b482f31426f95a47,0xf362074b8519afa2b7149608f21b03865a7f52816a0f37924a1fb359046f39b5784,0xf56421780a39bf1628307a94f51a847b029f34b25a697f0913b86f27504af81b635,0xf43b06592a178fa02b461538fb14075a396f6a4790528f03627b8f137a942f185b9,0xfa18704b29365f7913508a26bf469b1f348bf520bfa603f7283f5168f7421fa094f7a95]

def e12_6 : List Nat := [0xf8690b53a4721f851730a64b2f06b952f4078a2f9a562f7b805f931a7f19436fb1483,0xf360a9741b258f4b96175a302f6870492afb5648fa128f0518f3195f37a4fb093fb627,0xf52b683a41970f6035a8217b9f92473b15fa9461802f0b87af2657fa136f0439fb584,0xf0613574b928af4038b56a972f7052b681f7802a463f490b7a58fa3951f143bf9621,0xf4187563b902af916048b2735fa0b46258f9a15b742f6943071bf31286a79f3805a,0xf2a947038b516f96408a73b25f5872914a6f135af0b75f093af6820f1842fb436f79b1,0xf46250a1b3879f95b43a60281fa741586b2f630b8421f927bf5317f0937fa408fa965,0xf6a758b309421fa974b265081f06384a527fb0a28731f68a39204f1435f9b71f695b,0xf578b90624a31fb02834795a1f94037a812f4193652bf6a27053bf08469af8617b5,0xf537046a91b28fa27b4150968f162943b5af75602481fb9521308f936b0a47fa387,0xf65092a87b143f8b53a491602f695a037248f157462f081a6bf83b25fb9704f9317a,0xf425a6179083bf914a2b75863f781b602953f269b8407a1f643a05f94728afb0315,0xfb1a049738652f2784390b5a6f7b364a29150f716b95f28530f8a960f413a7f4b812,0xf6a274b381509f956b1a70843f79b064125a3f5368b7f29a85bf28716f40319fa420,0xf349b02685a71f59a3b706481f08b697352a4f305614b28f12478af9275b1f90a63,0xf50647a9b3812f493578b2a61f431a8697b02fa0917284b5fb15926f80365f704a3,0xf750613b8a249f36817b4a529f5b6284703a1f53804127a9f6a0b19f856437f2b90,0xfb4a358716920f42709b51836f1259a08473bf682b7a1305f8a5793406bf2a6f914,0xf58604279a3b1f13625078b49fa4657390b28f614802a7b9f5b6a038129f53471a,0xf4a17b0382956f491357a206bf8143b2709a5f874250a369bf5b1f68af216f840f379,0xf0b4872a91635f8062b13495af6903b58174af204156837b9f793a0f521a7f8246b,0xf0397248a5b16f2b36591a470f3a0b4962517f8146a7b9053f280431f8b6fa92f857,0xf492b83a15706f17862a4059bfa8419730256f539a081247bf0b3169f5a728f436b,0xf7a80b6149253fa285197b460f4709a31b562f75963402b81f786a12f48305af39b,0xf869314b7a502f791b34a0625fb63512a8740f9465b81a370f724859a61fb92f038,0xfa25394860b17f4a503628197f21a0834b657f8b51692073af413b78590f42b9a6,0xf04b3618a7259f56483a91b20f7308b96a421fa29435786b0f1a58260793fb7415,0xf28094156a37bf0592a48136bf1683025a74bf8a06917243bf64078539a12fb975,0xf60814a273b95fa504297831b6f2b46f8216f5b02f9036f748bfa170fa857f9a34f5193,0xf72b68a195340f4a658b093712f9a752fa062f3b50f13a5f6483f9416f7b18fb479f820,0xf4380729b165afb7140a682593f78b0519f2649af37a1f853af0963f2481fb602f75b4,0xfa5b408263917f1b0652479a83f509b273f492a3f84157f6958bfa6120f1864af3b70,0xf0825719a4b63fb3874612a059f1b73a85f041a697f6813490f56293f48b02f7a5b2,0xf0a465378192bf0283b16a5947f90431a7f8b50624fa396852fa8036b9f127b4f571,0xf8a61205b7943fb82964157a03f7804b9a3f9365f1a53f2485f1b68f260bf72a4f7190,0xf58694071a3b2fa75b84316092f159b4782f46b72f5026f081bf35a6fa830fa914f739,0xf2496b3a17805f04a92b861357f27439b51f14b7958f028a6f62a5f091bf30a7f8463,0xfa75083b16924f3418a95b6207fb90a5287f6851274fa179356f3048b2af63194b0,0xf84930a72b156f43a590826b71fa1204b38f9a46135bf7918f50b8f692af7425f7063,0xf8072935a61b4f587b2149a360f68a13b04f309b62a4f7a024f528bf1975f7183f596]

def e12_7 : List Nat := [0xf9b65a4317820f68a1925307b4fb0849a21f758163b2f74150a3f395b8f2604fa697,0xf7b1952834a60fa96b35127480f87a5614bf7362a185f3179468af0b24f3920f5b90,0xf4a975062183bf084725396a1bf65137a8bf0291643af03682417f7859bfa2b5f094,0xf9b7826341a50f58a2b4079316f84215b60f71b3a952f730b8194f8357a46f920a6,0xf47a8056193b2f4b68302579a1f8b170a62f53a29481fb0469587f0634a5b9f1273,0xf4a6b83195207f1842a3b50697fa5804b937f5687f1635f29a8f4126f9034fa1b0fb27,0xf5724069b183af9085634b217af946a13b02f3915b70f50a2f874af8b62f4861f5379,0xf4709b25a3681fa75b31694280f17b048359f4b6a973f20587f1a465f2a8b1f29306,0xf356a0b418297f596b3178a240f3064752b9f8349a5bf27a3680f907b1f51a48f261,0xf79b624831a50fb0347a951682f496372580f9064a812fb578f14b7f53a6f391bfa20,0xf2a9431b57860f596408a73b21f9716358b0f7b925a30f50a1426f9381fb4a6f8274,0xf38705b16249af73184b956a02f1297b035af9347a860f3b25196f5714a28f46b80,0xfa938506174b2f5b946a187302f4a8091b72f36b07a51f8629753bf4821f43a0f695,0xf821b3a496057f9a165b830247f84b9526a0fa85140b7f2b643907f291735af3681,0xf642b05a81793f804b962a1537f8b74a6192f07a94312f5b683a09f1b306584f257,0xf804a137b5926f70a691b48352f516479b03af9341750fa7812f49a82f563b8fb206,0xf7246083b951af14785a20b693f90735b126af91863a4f7b82561f792b405fa0348,0xf06958a27b314f250b936a4871fb5a9243081fb28357a16f268b470f46519f790a3,0xf35a2b7091468f29b0a1847365f169428a3b5f31b4a7260f78b6a95f3402179f508,0xf69752413b8a0fa1507b482936f046853a72bfa203817495f7809a43f265b1fb619,0xf4368a50297b1f318b07a65249fa378264b59f2751a4083bf84712a035f916bf096,0xf57a1b4096382f8512b649730af8065924a31f53916847b0f07143b5a2f78b9a62,0xf627513b0849af18609537a2b4f1b82507963af0a564f38a4f7124f9203fb916fb785,0xf79134a6b8520f78621b35a904f651a08427b9f49361f05b46f382b0fa3718f7592a,0xf75b3094a6182fb79a85024631f1734086b92af415962b8f35219f70b4f7a38fa560,0xf5b1724839a60fb43a02578619f0853126b7a4fa2903b81fb28a5970f49651f7364,0xf4753b2169a80f25b0934a7186f05a29148736fa38207b46f156bf9b85f7249f1a03,0xfb6a792403851f390a825b7461fb9a36570214f1a4359687f2a508b37f8194f2b06,0xf3562078b19a4fa7b931852406f71a295086b4f963a51284f8a0972b3f730b5f146,0xfb3a742691580f20418b9736a5f9568217b4a0fa84316b29f1b53072af06493875,0xf4b7a93158206f94863a1275b0f296b17038a5f261953b80af04a65f479b2f43781,0xf283b150946a7f842a170b6395f06125b479a3fb291408657f620a4318b9fa8735,0xfa5063b917842f31b6952047a8fa3908214b56f530b79a4618f72943fa0751f68b2,0xf20371658b9a4f3b1860a25794f39270b5a648fb40596213a7f9082b6351f78a14,0xf92b304a16875f794b13a08562fb53820647a9f48b63917052fb096a51437f12a8,0xf219b3584a706f30a925b86417f0b75a281639f513a8024b69f056a1b27834f749,0xf16b20a947358f7519634b08a2f6590483a7b12f4a52f6a14f8706f9b82f3b50f9713,0xfa4b273850691f46820b3a9517f9b814036a257f490a8f5b7af2934f1b62f6135f807,0xf3b097a285146f50319b724a86f359a621b8074fb6184f25739f0a5b2f71a38f9604,0xf2507b916a384f6874b20351a9f63495712a8b0f813b5a0f7904af2739f46b1f6285]

def e12_8 : List Nat := [0xf13057a968b42f2804793a51b6f2560a87143b9f73584a2f91a64f07b59f3816f20b,0xf9b278a506134f12597b08463af0a658b374192f3862a90f157a428f5b693f1b407,0xf6075b28a4931f958b720346a1f873b65a09241f53a71b0f4862a9bf9740836f215,0xf0a142b973856f17a46903b825f075a9312684bf7492a36bf195bf8a61f7208f5340,0xf46b192a85307f4b96a0837251f9a56048213b7fa750b861f2b590f4362fa493f781,0xf70368b214a95f2843a791b605fa5809b317426f02935164fa0b7381f4b569f8a27,0xf6153b094a782f931486a05b27f529640738b1af03a24718fb9120634f57b6f859a,0xf60a29487b531f9b85703a6241f7963805a4b21f564390b1f73b68204f9527afa81,0xf17b9a8243056f948b5a126073f1804a3b69275f6a253874f90b13685f4197a02b,0xf702653b8a914f508713a6b942f73869215a04bfb034a7285fa1b2f4618f9360f597,0xf8197b264a530f0483a72165b9f1a920b863475f37142596bf394b1f078a6fa2850,0xf8412b63957a0fb92a85074613f651837b0249af71b4a5309f6043a19f825bf8627,0xfa486b1730295f6081a9342b75f8796314b0a25f7216a8b90f83a7462f50491fb35,0xf2153a9b78406f7a20b4395681f5a41372b6908f30a647928f63b52491fa8b1f075,0xf58291a4b7063f51809b6a3427f25b038649a71f3162a0487f59741b20f693b8a5,0xf7046b352a819f302174a965b8fa3148750b926f90682b7a15f4361bf39427f85a0,0xf17b49a582603f3b640972a815f1b0837596a42f86341a702bf56193a0f9b52f748,0xf1829a03b4756f713a6b524908f48a73950b126fb91534a207f72b8369f041a586,0xf75281b46a903f635027b8a149f13842b560a79f0b621785a4f470861593fb92a3,0xf2043a96175b8f06524b978a13f50b3746a2918f4a72b15368f0a594126b7f8390,0xf3059b8247a16f73841b096a52f97185b6043a2f5319a087b26f57021f493bfa468,0xf1978b534260af516849037b2afb38a71295640fb47250813a9f57028fb6a41f396,0xf6a520341b879f495718360b2af391280a7b465f58613b92470fa3726b51f09a84,0xf092758a1634bfa78b14935062f7b3120a59684fb28197304a6f17083a9b5f5642,0xf5b2790834a61f1a03b9685247f604829135a7bf759418b0263f078a21b465f9a3,0xfa1304875b269f734a825619b0fb12908536a74f60a39518b724f9417fb683fa205,0xf078b12635a94fa469b5027183f8652a0913b74fb2803957a614f29734f158af0b6,0xf302a7965b184f2b91a3570468f90b6274a8315f63b871429a50f0a61258f7394b,0xf8194a2b36570f417826a395b0fa869734b1250f20358b7461a9f7248315af09b6,0xf09178a6534b2f7259b3a06814f94057a138b62f5b128463079af16937b085f4a2,0xf034b8a179562f6083947a5b21fa253b0781964f409b6a315728f058637b1429a]

def e12 := e12_0 ++ e12_1 ++ e12_2 ++ e12_3 ++ e12_4 ++ e12_5 ++ e12_6 ++ e12_7 ++ e12_8

def a14Mask : Nat := 0x72a000c960001b800313000e4004d001603801e000220

def a14_0 : List Nat := [0xf965fd82f863fc71fb64fa80fd94fd70fa91fca4fcb2f521fb73f530,0xf7cb3f1c25f712bf956f4b6f836f035fd07fa4cf8a0fd82f9d4f9a1,0xf4bcaf53b6f712bfc152fd059f7d4cfd28f368fa08f19af946f037,0xf5371f9521f6305fb283fd4c2f08d7fa9d0f496bfa864fc1afb7c,0xf17c25f2bc1fa4cf9a1f80afd82f638f4d9f659fb64f305f7d0f73b,0xf91c25f68a9fb712f3bc7fa150fd49fd28f038f70df635f4b6f4ac,0xf53bc1f8250fc7b2fd912f30d7f1a07f4a8df94caf638f659f64b,0xfb37d2f68a03f5283f5170fc12fd08f49df965fa19f4b6fca4f7cb,0xf253bcf837d2fc1a4f70acf712bf968af3650fb64fd94f591f0d8,0xfa82c4f36508fb496f8d46f1a95fd219f3b25f7d03f71cbf07ca,0xf2837bfa4680fd2ca8fcb4f63bf503fd07f1c7f512f956f91af9d4,0xf2bca8f0521af356b7fd869f4d2cfb364fa49f159f308f7c1f7d0,0xf46359fa07d9f4a86bf9651f2805fd830f4c2dfb712fbc73fca1,0xfd7128f369a8f0352df70a1cf5086f4b6fd94fcb2f7b3f195fac4,0xf17cb2f491acf637b4f3596bf51c2fa4d9f0a83f0568fd82f70d,0xf512b6f0a825f719d0fb4c73f7bc2df468df3596f038fa49fa1c,0xf2d0a8fca4b2f73bc1f46b7cf8307df68053f512f91afd94f569,0xf15649fd96b4fa8059f03bcaf2d07bf68d73fc4a1f7c21f8352,0xf6bc73f864b3f2d07bfa4d80f952c4f51a96f128acf917df305,0xf864b73fd94fac4f569f1a9f3b6f08af2d8f053f70df2cbf152f71c,0xfb28a46fc70af1c25f217df956f386fd08f530f7b3fc4bfd94f1a9,0xf917c4afb21cf50a1f28acfd952fb386f7d4bf649f365f0d8f730,0xf153bc7f637bf0a83fd807f4d2bf59d0f2568f1ac2f964af94c1,0xfd4b359f8650af37b6f964f1a9fca4f083f215fd70f2d8fc17fbc2,0xf21a9d8f630a8f7380fd250fb653fb4d7f946f195fc71fcb2f4ac,0xf259ac1f7b651f491af3705fd869f4b36fc7d4f80d2f8a03f2cb,0xf19d28af0738df3b680f059afb7d4fc4af649fc17f2bcf563f215,0xf9acb71fa8251fd7c12fb4c2f0d4af6594f8073f8d96f63bf035,0xfa836bcfd2c49f4d82bf680a4f71cf3b7f503f512f91af596f0d7,0xfd0a159fa8219fd2508fca4b2f53b6f71cbfc4d7f386f496f073,0xf5086b2f82173fcb4d2f7b30dfa4c70fa9d8f653f195f496fac1,0xf7c4d80f64b38f369a0f517d9f7356bfb21cfa82cf50d2f91a4,0xfb64d03f63705f1a495f12ca9fb71c4fd7cb2fd968f3528f8a0,0xf3b21c7fa052cf68d7bf08a17f382d0f53691f4d956f4bcf94a,0xfd7c128f152d07f368fa08f49dfbc2f3b7f503f965fa91f4caf46b,0xf468a0df94bc2dfd807f2b38f7b63fac4f350f19af71cf512f695,0xfa4cb30f649a83f2d08f5370fd7b4f652bf9d86f12c7f1caf159,0xfa4c170f2ca86bf80d73f64b3f305fcb7f2d8f9d4f91af569f251,0xfd21950f7b38a0fc28d7f8036f5173f56b2f9a4dfca1f4bcf946,0xf9d4b21f8307d2f8a156f37c25f0a95fb71cfc4afd80f63bf469]

def a14_1 : List Nat := [0xf64c128f6952cbfd7b38fa9d08f4b2dfa194f5036fc70af1735,0xf5649a1f283695fd2c19fb3712fb4d86fca4f07df053f08afcb7,0xf564c21f9a82b6f30d86f17b49f70a4df59d2f3508fbc73fca1,0xf8d4cb6f051a83fd0719f2b465f21c7df280acf9635fa49f37b,0xf1c7365f64d708f528d9f0a835fb2d03f17bc2f9a4b6fca194,0xfb49683f7d9563f4d07b6f503f125fa80fc17fa91f28dfcb2f4ca,0xf21ac4df9652c1f9d8a05f3517f8630f382bfcb7fd07f49af6b4,0xf071968f594b36fc12537fd4a9fbc46f2d7bfa051f8d03fac28,0xf17bc4af73b21cfd83052f9680afca82f64bf591fd94f7d0f563,0xf82cb4df368ac7fa03b69f07b2dfd719fa4c1f6594f3805f512,0xf9d8071f5682d0fca4952fa0351f69a83f21cbf7d4cf46bf73b,0xfb4d807f94c12df3b6825fd7150f30ac7fa4638fa91f659fb2c,0xf9ac2d4f1507bcf837d0afa17c4f9568df25308f2196bf364b,0xf194b7cf0a8217f52d9a1f64d73bf659fbc2f305f4acf8d0f863,0xfd94b38f564d73fb70a96fc4a12bf8ac2f0368f52d0f1c7f159,0xf071963f537cb6f280d7bfa059d8f3b468fc2d4f125fa49fca1,0xf70a94cf82d91af51cb69f71253bfa4b2cfd0564f3086f738d,0xf1cb465f71a83bf912d4af4c70d9f2b695f8d736f0ac28f350,0xfd71cb2f80d4c2f950a8df653b49f7b64acf125fa91f370f638,0xf837cb2f64a059f80d71af356b70fd863b4f1c25f9d21f49ac,0xfa15968fc1283bfd80ac2f9a4d71fc49d07f37b46f2b65f053,0xf305968f7bc4d0f7c1a9df4912cafb25364f56b371fa80f2d8,0xfd08ac2f1c730afb2864cf56b712f963b4afd49507f8d9153,0xf0d49a15f17d9f3b25f956f28dfc12f368f703fa08fbc7f4b6fa4c,0xf17b30d9f5370fc4d7f159afcb4af256bf8a0f683f28df496f1c2,0xfcb3659af64d8f2538fc1a4f96b4f7d03f7b2cf19d2f7051f0a8,0xf49d80acf4d28afb2cf17cfa19f569f512f70df3b7f6b4f386f053,0xf4d71a86f65083fb253fa9d0f4b69f037f195fc21fd82fcb7f4ac,0xf38d4b25fc7082fac49f12d9f68a4f037df1a05f7bc1f965f3b6,0xf912b705fa9651f3bc25f30d7fc71f4d9f8a0f683f28df4acf4b6,0xf4b2519afac2d0f38650f708dfa128f9635fcb64f4d9fc71f37b,0xf496537bfbc712fd8307f4d286f51c2fd059f63bfa4cf9a1fa80,0xf159a4c2fb38acf07c1af352b7f9d71f6b49fd082f68d4f6503,0xf03512b7fa1950f6bc25f8a9d2f37d4bf8d0fc71f4acf694f638,0xfd8a12c4f70a4bfd9517f05638f0d253f3bc7f682bf9ac1f469,0xf538acb2fb4a07fd9637f864d2f951c4f3b650f217cf0d8f1a9,0xf94c1a05f15307f96521fd28a9f864d0f7b38dfb4ac2fbc736,0xf4d8653bf50a9d2f736bfa128fcb2f083f946fac4f7d0f17cf591,0xf86352d0fa8d950f2b38f1965fca12fcb71f4c7df703f49af46b,0xf682d705f19538af9630af215fbc2f7c1f4acf0d8f4b6f37bf4d9]

def a14_2 : List Nat := [0xf51c2b30f2d70a8f56b73fca17f4a9df9125f8d0f368f496fc4b,0xf468351cf37196bfcb49af2c7bf08d7fa821fd0a4f5630f952d,0xf4a073bcf7b2ca1f2d7c1f83052f869af195fd08f4d9f64bf653,0xf71c4d2bfcb4912f53082f51a86fa964fd059fc70af738df63b,0xf38a194bf2d4acbf9d7b6f637c4f07153f50a9f8256f80df21c,0xf96821a4fd2b638fc7d4bf0ac17f4652cfa9d08f73bf503f195,0xf512ca46f4d917bf736bcf0a8d7f69508f52d03f1a94cf82b3,0xfb7c4912fd4a869f173bcaf50a9f52c1f64bf8d2f308f7d0f563,0xfd91c4b7f2156bcf638a49f1ac7f253bf0a95f82d0f8d46f370,0xf7386b2dfb369d4f82170dfc4652fc7bfa1cf591fa49f08af350,0xf53b7082fd95037f2b638dfa94d0f6915fca17f4a86fc12fb4c,0xf8d4a196f64952bf2150acfc73b4fd28a9fc17bf038f356f70d,0xf7b2d9a0f059683fac4d08f217d8f36bc7f653b4f4a19fc152,0xf8a4c730f1c2d07fb350acfd4b28f59a12f69d7bf49156f683,0xf4d7b2cafd821a9f736bc1fb4c703f8356f0d25f591f649f0a8,0xf03694b7f50ac73f8a46b3f59d086fd71c4f2cbf19af215f28d,0xf651cb28f4a17b6f4d08a9f703b4cfca052f9d21f3695fd837,0xfb71a94cf528691fa08364fc70d8af3056bf7d953fd4b2f12c,0xf9d07c25f8364a0fb28d73fa17b68fbc12d4f6915fac49f305,0xfd219537fb38a07fa9d051f4cb68df630825f4b2caf1c7f964,0xfd2c7150f6b70a4f80369afd4b259f8d7356fb3821cf94ca1,0xfa173650f91c2b35f69a8f215f8d2f083fd70f4caf4d9fb7cf6b4,0xf52bc173f69a07b3f0d83f5086fa128fc2d7f46bf951f4d9fc4a,0xf6b250a9fd956380f7b30fca4bf128af1c49f1735fd864fd7c2,0xf17d0a95f1a82b49f2d805f6b35f469df836fc21fc7bf4acf730,0xfd835917fb256803fc1507f36b7fa821fd9a0fc4d2f4acbf496,0xf50d9682f4c1a07dfd8ac2fbc712f94afb64f380f591f37bf653,0xfd259ac4f1c738d9f80a46f0d715f94b6f128afb307f653fbc2,0xf7d4c2b3f9a1c7b4f4acb6f21708f52d91f8d0af386f956f035,0xf56308d9f83512b6f1964af0d49af173bcf2507df28acfb7c4,0xf69d2c15f9a86b21fb7083f1a037f59463fd4ac7f528d0fbc4,0xf468a03bf950d736f807153f6b25f7cbf2d8fc12fa4cf94df1a9,0xf37b4c25f82bc1a0fca9507f2d71f038df6519f64a8f94df36b,0xfd7386b4facb30d8f2d9a08f507c2f1c4af217bf563f964f915,0xfd968037fa0d8219f49507bf4652df8351afcb2f36bfac4f17c,0xf7156803f5364b70f21a83bf9acb6f28d95fd4a0fc491fc7d2,0xf21ac4d8f736b250f519a46f69d08fc17d2f53b49fa038fbc7,0xf217d865f94ca82df0d4a15fa07c19f5963f380fb46fb2cf73b,0xfd4a9512f08d9635f1cb649fa83b4cf2c7bf5682f7d03f071a,0xf2b4d865fa46bc28f150837fd219a0f4c7d9fb307f6953fca1]

def a14_3 : List Nat := [0xf507ca12fb4d71c2f4a86bcf0a9638f94651fd0359f82df3b7,0xf2d4b705f80d9ac2f0a4653f951a86fc4912bf8d73fb63fc17,0xf71c253bfa837c49f0a468df912b4dfbca156f807d2f36950,0xf7bc4d91f28a496bf530d86f70512dfac7380f2c1a95f364b,0xfca9652bf8a19536fc7150a4fb64f73bfd49f2c1f0d7f82df803,0xfd94ac70f7d4cb63f4b71a96f3b25f0865fa038f195f21cf28d,0xf4c7b259fc28a071f3bca4d7f651a9f19d2f80df368f64bf305,0xf64a19d8fca80d71f07b259af12835f3650fbc73fb496f4d2c,0xf4a8d03bf864c7d2fa156380f12cb7f6952bf0537fac19f9d4,0xfac46519f521cb69fa4d2c71fd7b49f38d05f2863bf037f08a,0xfb73652cf1594d07f2b38691f1c7d9afac4f80af530fd28fb64,0xf280d735f1c7b305f8a4cb63fc2b49af1a07f2d91f8d46f695,0xf96b2c4df8250736f912d0a4f7d8acbf3564bf1a95f17cf083,0xf36b2507f4682d7bf9ac2156fc1a03bf38d95fd4a80f917c4,0xfd0591a4f8d2c153f7128a9df25694bf80ac46f63bfc7bf370,0xf96b7c2df38d4a07f364ca80fb21a94f3bc195f17d05f2568,0xf9a0d2b6f51cb7d9f17052cafb4a803f7c4d83f912864f635,0xf6350d28fa1c2b30f194b652f738a951f807df469dfca4fb7c,0xf4ca8056fd491528fa17b2d0fcb4a9d7f596b3f730f683f12c,0xf652b7d8fcb630d2f9173b46f4c70a9df8ac12f594a1f3805,0xf564ac19f036821af7b4c253f7cb694dfd2b380fa8d9f7051,0xf1c7b49afb28364cf65307d8f371596bf50d912fc2d4af80a,0xfca19637f8d4b653f259a4cbf17d2805f68a0d94f07b3f2c1,0xfd736912fbca9d46f8a4b30df253807bfc1a0594f86517c2,0xfb7d05683f6953f073f1c7f4b6f2cbfa80f215fd28f94dfac4f91a,0xf382b4650fd968f4c2df1537f9125f0a8fd70f3b6fc7bfa94fa1c,0xf517c4683f0365f94b6f2d95f08d7fac19f0a4dfa128f7b3f2cb,0xfa0594d28f3b465f37b6f9d86fc2bf083f1a9f7d0fc4af17cf512,0xf46b2c159fa0569fd219f3086f7ca1f3825f4a8dfd70fb37fb4c,0xfa0d7c469f70591fa86b4f380fd49fb37f536f28df125fca1fb2c,0xf637cb4d8f30d28f96b7df5946f5170fb253f08af1a9fca4fc21,0xf682b70a9fbc463f94b65fd4a8f17caf3508f37d0f152cf12d9,0xf694a8d73f3507bfd2ca0f4d956f2b68f1c7f083f512fa91fb4c,0xfbc28a056f1c469f37086f53b21fd952fb7d4f038dfa17cfa49,0xf46b70d9af51280f694d8fc2591f3b2d7f038afc71af4bcf635,0xfd863b4a0f7ca80f2d738f156b7f9521af9d4c1f053fbc2f946,0xfc7b21a94fd2ca4f07d8af683b4f691cbf359d0f65173f5082,0xf4ac7156bf49521cfd964fbc2f035f37bf8d2f836fa08f0d7fa19,0xfd82591a0f1c2b35f3807f5630fd712f69a8f49dfb46fc4afb7c,0xf19463052f4ca82bf6b35f71cbf2d7cf8073fd4a0f9a15f69d8]

def a14_4 : List Nat := [0xfb4ca0712f2c1a8df37d08f4a9df6528f530f951f649fb36f7bc,0xf6bc4a173f128d95f0d4b7f253bf8056fc7d2fa830f9ac1f964,0xf0d2b371afb708acf1c4a9f28d7cf638f521f49df530f695fb46,0xf5968acb2f4651a9f4c19dfa4b70f7d83f82d0fc217f305fb63,0xf94ca037dfd07b64f8d256f12805fa4b38f9536fcb2f17cf19a,0xf86517d03f4a953bf28acbf07c1af2c491fd8052fb736fd469,0xf15694cb2f4d283bf7036bfca952fa0864f9d8a1fd0537f71c,0xf3719564bf4d86bcfd28369f2c7bf1acfa94f0d7f0a8f512f530,0xf7d9ac250f219568f463b2dfa038f4b69f1735f1c4afd08fc7b,0xfa19d2538f37b4a0fcb64d7f2863bf1705f9ac4f8d0f659f12c,0xf12803695fd917b2fbc4d83fc7352f0568afac1f4a9f6b4f0d7,0xf691530d8f837d4af1c280af7cb21fb6507f9ac4f2d95f63b4,0xf8217c49afb708d4f3bc2d7fa1964f50ac1f0359df56b2f386,0xf0ac28635f719d83f07c1a8fd4cb30fb2d7f94af64bf569f512,0xf680a4c2bf8d4b73f0d7cb3f52d946f5963fa128f7150f1ca9,0xfcb68a0d4f9d821af517b46f2b3705f194acf5369f7d2cf308,0xf96382bcaf30a4c7f659d08f2d4915f53b70f1a8d7f4b6fc12,0xf1c2d968af250d7bf70a94cf821730f538d46f4acbfb63f159,0xfa0564d2cfbc4a12f94b7c1f86b37df528369f53071f8a9d0,0xf869a07c2fa49521fcb2d91f4d08acf37b650f538d71f463b,0xf2517386bfa463b7cf2c1f4bcfd94f956f035f0d7fa91f8a0fd82,0xfc2173b4af1c4d28afd0a9f08d7f56b2f591f7bcf649f305f638,0xf3bc70865f4917d2bf9a05fd830f6b73f4d96fc4a1f2ca8f512,0xf173056bcf4d9ac7bf1a4c2fb253f8d2f915f08af638f649f7d0,0xf69d21705f6803594fbc7d4f251cf37b6f8a0dfb382fa4cf1a9,0xfa96512c4f7b638d0f2d468f4952bfbc73f19d7f350fa80fac1,0xfa0d821c4fb37ca94f652d4f69d7bf8071afbc2f159f305f368,0xfca12d96bfc7d0a91fa4b28f7153bf4952cf3807f6305fd468,0xfacb38051fb6491c2f71253fa07c4f9568af369d0f4d7bfd82,0xfa864b730f7d25380f0d8215f6b3fcb2f956f1c7fa4cf94dfa19,0xf64b25308f7bc1a8df82d073f12c7f59a0f9651f6b3f4acfd49,0xf4951a836f2196805fb4d703f7356bfd0a9fca4f2d8fc17fcb2,0xf1ca086b2fd705369f519a82f71a4bf73bcf4d2cf9564f8d03,0xf1a0d7b25fcb3708af5364a9f9128df83056f6b49fc2d4fc71,0xf968051c4f56b4a82f91ac2df4638dfb2173f530a9f0d7fc7b,0xf8d0ac4b2fcb719d2fa837c1f64d708f512f94af63bf530f569,0xfa830521cf680d9a4f4d7c2bf3594cbf1569f37b6fa071f2d8,0xf80519463f96b7c2df07128df30a4d7f68a95f53b2fcb4fa1c,0xfb371a496f3059d46f08652dfa83519f7bca0fc4b21f7d82c,0xf4a195086f369ac15f56b7c2f703b21fd738a0f4bcfd49fd28]

def a14_5 : List Nat := [0xfb7d05683f4d9acb6f082c73f194a07f251a8df21c4bf3596,0xfcb70d491f6b37125f80a463f9d8a15fc4b2d7f869ac2f053,0xfa4630d71f1cb68d2f70519acfb4c2f5382f965f80af3b7f49d,0xf9a4cb38df9173086fb2c1536fca07f52d0fb4d7f5649f8a12,0xf968352c1f07d82b3f9a12d05f17365fa08f4b6fc7bf4caf49d,0xfd9a46528f0a12c4dfc70368afb37d2f0538fbc17f694bf159,0xf7d4a8051fb65307cf637b259f2194cfb4683f0d9afa1cf8d2,0xf912568d4fb69a0d2f364ca80fc7382f507d9fb7153f1cb4a,0xf4c1a0d86fd4b3052fd963807f6537cbfb712fca82f9a4f591,0xfbc705283f69ac173f7d0a12bfa4c2d8f86530f4b6fd94f915,0xfb2507364f2d4917cf21530a8fb659acfd83b7f80d96f1c4a,0xfd08a96b2fa4d7b30fbca1564f507382f95368df2c71f1c49,0xf4682b30af9651c2dfd7b6380fa8d491fac7059f73521fbc4,0xf28a07b4df6503bc4f95371caf2c7d96bf194af863f08df215,0xf19d28a07f380564bf9a4d035f968d7c4fc152bfb736f1ac2,0xf807b4a96fb2c7d46f37194cbf8259d03fa051cf12d8af536,0xf25037ca1fb4a91c2f68d4953f170d965fd7b382f46bcf80a,0xf719d82cbf3651ca8f0d4a968f2b350a1f7c4952df4b6f037,0xf82cb369df491a07cf4d051caf6b2d738f17b4652f5308a9,0xf2d96b308f537b4ca0f4d8af5946f368f70df1a9f125fc71f2bc,0xf56370a91fb694c2d7f28a1fb4acf53b2fd864f0d95fc71f308,0xf5286b730fd9ac2b38f1a4d2f70df1c7f80af653f4cbf915f964,0xf659d21a4f152b70a9f968d4f82caf0538f730dfbc4f3b6f7c1,0xf637d21c4fcb38d917fb4d07f52ca1f86b2fa94f0a8f530f569,0xf8659a4c2f7b364d91fcb21af7351cf038afb694fd052fd807,0xf4659ac7bf369d4a05f2b37dfcb682f08a17f491cfd038f512,0xf38d2c4b6f95308a4df7ca0df173bcf52b70f51286f694f19a,0xfd82564b7fc4d0596bf07c2b3f5173f9d21f863fa1cfa08f9a4,0xf4d2863bcfb4a83052f96b7c1fc21af5371f4956fd708fa0d9,0xfa0719638fc2b659a4f0d9468f7cb4df2d8f3b7f1caf521f053,0xf51c468a9facb280d4f5037c2f83b7dfb496fd219f071af356,0xfa194b370f517bca83f4c7d9afd46b2f630d8f8250f1c2f965,0xf1cb28365f96807d21f71a053fb4d03fa49d8fc259af46b7c,0xfa8073651fb7d49503fb64ac2fd0a968f5283f19d2fc71fb4c,0xf305694c7fb4d251acf864a9df195382f1c2b7fd07f8a0f63b,0xfd07c1a82f7b69a08df4c219df538649f36517fb3052f4bca,0xf82507c46f94a1cb35fb21736fd08ac2fd9a038f6519f4b7d,0xf4a071cb6f7d80594bf530d96fa12d4cf2519a8fb2c73f836,0xf2519468dfa12cb659fb4d9637f2b38f08af350f7d0fc17fa4c,0xfa952b730f1c7d4b69f8d94cb3f8a46f0d28f1705fac21f635]

def a14_6 : List Nat := [0xf50a17d82fd96b7380f703b21cf68a94f4bcafd2c4f519f563,0xfd4b38a07f563082d9f52b68d0fc217bf37c15fc4af19af694,0xf2b4c1965fa946bc21f2d7b368f15037f59d83fd4a80fca07,0xf0735649df3bc12596f19a86b7fc2b4d7f0a15fac4f803fd82,0xf352b7d86f94d08215f0569a17f37ca4bfc19d2f4cb6fa830,0xf2b65308dfa12c7b49f7364d91fa4c150f95286fa83bcf07d,0xf71acb64dfb49651c7fb2c4a03f253708f1950d2fa9d8f683,0xf963b7ca1fc4680371fd28a059f38d4b65f49afb2cf521f07d,0xfc7d0564af9682b351f4bc21a9fd8071c4f637bfa038f9d25,0xf80537cb6fd8259630fb38a4d2fac4b7d9f19465f1a07f2c1,0xf0736bc4af6830d7b4fd9a17c2f4d8ac19f3b2805f965f215,0xfac7082d4fa836b219f650a1c4f35968d0f7d94b3f2cb715,0xfc12507b4fc730d82bfd953b64f17d2ca9f3651a08fa4968,0xf94d2b7c1f03bc28d7f350d9a17f512f64bf683fa4cfa80f695,0xf250d46bcfa194b280f512d9a86f3b70f8d73f5963fc17f4ac,0xfb63594d2fac4650d9fa17d83b4f86912f2c15f7bcf037f8a0,0xf869d2b30f8d7c4b63fa1cb70d4f0a825f219acf9465f3715,0xf37159a08f50d7ca82f307bc465f68d49fd2c19fa4b21fb36,0xf5912d7b6f05283b4df351ac496f864a9dfcb2f08af703f71c,0xf94c21735f9d83b7c1f82b4d70af6bca15f052df64a9f3680,0xf82cb719df2508ac7df15683b4cfb69a12f53649fd4a0f307,0xf7386b250fa94bc280f1a8d7b35f59d036f1964d2fca4fc17,0xfb4d259acf638d91c4f6b730a49f80d71af2b3568f1507c2,0xfa864b7c1fd0a49638f03bca9d7f17356b2f2c4df8052f915,0xf9528a4c1fd4b69ac2fd7305649f0a12bc7f53b71f836f8d0,0xf0d4c719af7351cb2df3b469508f82ca49df12568af036b7,0xf28d9a1cbf4c25173bf695307d4f638ac7bfd0a4912f8650,0xfc1a83052f49568d0af7ca91280f3517d2b6f64d9fb4cf73b,0xf952cb7d4f6b2d8305fa1c73680f28a4b351f9170df4ca96,0xf71a49d2bfc738a0d4f8695307df15082ca9fbc1256f364b,0xfd863bc70f2d9a1538f1ca052b7f4b65912cfa4d7308f964,0xf719d4c2b3f863f053fd82f70dfa80f152fca1fbc7f49af659f64b,0xfb7305691cf12c7fa951fb352fd07f8a0f4acf4d9f28df6b4f683,0xfca1703594f6915fd8a9f2bc1f4d0af7c2df0825f6b4f3b7f863,0xf49170a82dfd7ca9f4c1af3b7f659fb64f2cbf521f386f0d8f350,0xf6508ac219f951a4f0d9af3825f4d86fb7d2f730fb63fc17fc4b,0xf70a82d951fb4d7cfc491fac21f469af038dfb352f6508fb736,0xf2d80acb35f51730f2836bfc4b7f68a4f965f7d0f49df21cf1a9,0xf6b21a0d73f194c7f8a950f307bf4acbf251cf69d4f8356f82d,0xf3bc2159a0f508d2f68a19fb7382f70df49df635fc71f46bfc4a]

def a14_7 : List Nat := [0xf380d7cb25fca864f51736fd91a4fb496f50a9fb703f2c1f8d2,0xf1ca8d4637f250a1fb69d2fc7082f3b7d0f5683f4bcf9a4f195,0xf38d07ca4bfd4cb7f68a94f19537f0821afb69d2f251cf0365,0xfa950d2bc1f37b65f4a03bf8d963f8ac70f864c2f194d7f125,0xf9d4ca8365fa4b680f521f035f7b3fb2cf71cf0d7f8d2f946f9a1,0xf0712d4653f82bc7df950df1c25f694bfb37fa80f683f4acf91a,0xf4ca835196fcb49a1f217cfd0a4fd259f86b2f3056fd708fb37,0xf05382d71afd9a864f2b4acf194cfc7bf63bf596f215f073f0d8,0xfa4b682170f63b259f15649f4c2df9a8df037df8053fc1afb7c,0xf805912cb3f4d2b7cf69a03f4a8d9f7351f6825fac1f64bfd70,0xf2d964b705f21a86bf3bc17fd49a0f28d7cf653f083f951fca4,0xf4b70d8659f150369f21c7df38a17f2ca08fbc46fa9d4f2b35,0xf6b2d8ac19f073b4af4c7d9f217bcf53682f0d465f59a1f803,0xf28659a07df19d4b7f38a4c7f694f0d8fb36f1caf251f035fb2c,0xfb4c251736f564a19f2d7bc1fa869f07caf382bfd49f08df530,0xf2c7d46b38fd21950f8694a0f517b2fd8a9f703fbc4f563fc1a,0xfc1a9536b7f52b370f17d082f8649dfc4d2f6915fa830fcb4a,0xf0719a4b2df568d49f3521c7f6b7d9fcb364f0a15fca82f830,0xf69a1c2538f650ac4f9d28a4f70d4bf37d80fcb217fb36f195,0xf86537d94af46912cf59a071f0d4b25f1acfb7cf8d2f380f63b,0xf4c19a07b6f53b496f2517cbf3082d7fd059f2ca1fd8a4f836,0xf0a12cb738f507d82fca9517f4a869df0d2b3f91c4f64bf536,0xfa46351280f07cb2dfac49d8f9a1c25f56830f73b4dfb7196,0xfc7b64a052f38d215f8ac4b2f637d08f3bc170f9d4f19af596,0xfd7350a864f2596bcfd071a9f308d2bf836512fac194fb4c7,0xf17d286359fd9ac70f3bc150f496b2cf38d4b7f521a46f80a,0xf917cb350df82c1a4dfb7d2fa94cf521f695f64bf836f037fa80,0xf1965380d7f68d4c73f307bf21cbfa051f952df2ca8f4b6fa49,0xf864b25073f803517dfa0d28fb63f956fc12fc7bf4acf9d4fa19,0xf96bc70835fd2b4630fa94d8f8256f719df1a05f73bfc4afc12,0xfc253869a1fb217036f7d94cfd0564fb4acf195f8d2f0a8f73b,0xf915370a86fd463082fcb4a1fd83b7f12c7f56b2fd950fa94c,0xf15380d7c2f7056bc1f194caf630a9f82b4af52d9f864df7b3,0xf2b37c159df8a0564df28035f19ac2f4cb69fa4b71f7d0f386,0xfc2d8a194bf4d9a086f038215f2b35f7b63f965f7d0fc71fac4,0xfd94c12b30f4682c7dfa8d259f1a07f8350f9651f6b73f4bca,0xf9a1cb7d25f9650371f8a07c2f2b351f4d9f46bfac4f836fd80,0xf7bca4d283f9468035f91c4b6f3652bf1a05fa8d9f12c7fd70,0xf94d086351fa073bc4f38a950fd82b7f9652df21acf17cf64b,0xf7d4956bc1fc469152f8a03b2f12d9afb7ca4f38d07f63508]

def a14_8 : List Nat := [0xfcb2569d0af194a82cfd73864fd80712f7b4cf159af305fb63,0xfd80712b69fc4b37d2f64a825f194d0afca951f035f836fb7c,0xf9a8073b46f35194a0f259d7bf05638df1c4d2fcb682fa17c,0xfac2507d94f28a1c4bf9517b6f4d8356f19a0d2f0368f7cb3,0xf96bc25071fb4a1c73f530d21f9a0865f8ac463f28d7bf94d,0xf3708a964bf2b659d8f17d2c49f4a0df386f512fcb7fa1cf053,0xf308659d7bf4d2507cf38d0a96fbc12fa82cf91a4f3715f64b,0xf2cb370865f6b7ca03f7d964c1f538d0fa128f4b2df195fa49,0xfc7195382bfd08a152f4b7d9acf4650af68d49f12cf307fb36,0xfca4b350d2f6308259fb217386f15649fc4d7bf0a1c7f8d9a,0xfac70594d8f7d96821fa0d2c19f5364a1f6b25f308fb37f4bc,0xf568a4cb30f351c7b6f17382cafb25964f4912df7d80f9a0d,0xfa1537c4d0f08d7b25f682d94bf1cb307f638a4f912caf956,0xf51a9d07b6f2ca8305fd4cb217f80a496f537c19f463bfd82,0xfd9173b4a0f512b630f807d49af864c253fca1f569f8d2fbc7,0xfbc7128364f86b2c1af53708d2fb7d9503fd4a0f94caf5691,0xf12594a807f4d0ac2bf63051c4f965382dfd86b7fbc73fa91,0xf508d96b21f730a94cfd719564fb352d07f28a4bcf1caf386,0xf7d21c4a80f7b35691f94bca15f250d46bfa038d9f682c73,0xfd251ac738f2b364c1f0d49653fb4a082cf8a9d7b6f95071,0xf12d05638af9682530af7d80fa4cfb73fbc2f195fc17f49df6b4,0xfd052194c7fa0869d2cfbc17fa951fb382fa4d8f073f6b4f365,0xf569a12b73f7052c49df4d286fd0a8fca4bf380f6b3f1c7f159,0xf80a17b463f03b68a4dfd8259f5196f4ca9f3705f2c7df1cb2,0xf37c49d865f0a963b25fb712cf4d28af1acf591f0d7f803fb46,0xfc712d863bf2b730a95f51946fd4b69f8053fa4c1f28acf70d,0xf2b49a1508f4a8d9536fc4d0af12569f71c2dfb386f703fbc7,0xf82b69a4d0f512ca836f537d2f9468dfb71c4f0a195f703bc,0xf12837b695f649d8a05f2d4b35f3086fc2bf1a9fca4f7d0fc71,0xf68352d0a9fb7159d46f28a491fc2b4f3056fc73bf708dfc1a,0xfb7352d8acf4d917c2bf03869af21508f1c4af9465f6b3fd70,0xf350acb4d8f7b64c19df1a82c7f37086f2b30df596fa94f215,0xfbca821536f386591a0fc17d94f0d4b7f2508df2c73bfa964,0xfa4c251738f0ac19d28f4b368df69a12bf9564f7d0f530fbc7,0xf694c1a805f864a952dfd03517f2b4d91fc283bf7ca0f37b6,0xfbc7153082fca0d86b4f63b705f9d738afd4952fa4691f2c1,0xf05649ac73fc4a836b2f128695f3b4d25fd91cb7f170af08d,0xf96b2508a4f12cb4d9afa03864cfd28f519f356f7b3f71cf0d7,0xf371c2d94bf68251acbf9507b21fd4c7fa469f8a0df635f803,0xfd4ca91280f68a152d9f50a4b73f307d8f6594fb63fc17fbc2]

def a14_9 : List Nat := [0xf4d286b71cf8d7cb49afd912ca0f69503f1a465f7380fb253,0xf91c280d4af63071594fc73521afb38d2f650a8f7d96bfb4c,0xf195307b2cf569d71a0fd08acb4f7c46b3f9a4f215f8d2f638,0xf0d91ac463f9a07b256f28d4bc1f594a80f7153fb683f7c2d,0xfa863b2c71f07b4d283f7d91253facb694f64c15fa950f08d,0xf2d730864cf953b70a4f9d4bc71f69a82bf83650dfac1f251,0xfc7d9a803bf4ca07359f1c2864af25196bfd4b712f05638d,0xf0ac173b2df8a46307df21956bcf51a9682f5083fc7b4f4d9,0xf6b70d8215f173508a9fc4b30a1fb259d7cfc2d4af638f946,0xf71594d8acf63b2d708f4a0382cfd9a1250f6537b4fb691c,0xf2cb68a94df7364c12bfb4a0d83f5691703fa159d7cf5082,0xf3807152b6f8ac1964df1286594afd9a0f7d2cfbc4f305f3b7,0xf7b68052c1f738a94bcf0a19d463f2153bfca4f569fd70f8d2,0xf4652d917cf4d037bcafb4963512f28a1cf059af807dfb386,0xfc4d21a807f9a0d7b46fca49d82bf05683fc2591f5173fb63,0xf08d4ac195f7c4b38a1fd9a07bc2f821536f52b6f30d7f946,0xf30d8a94cbf917b4635f837c2d96f082b65fa4d70f251fca1,0xf35082196bfb2568a4cf951a038dfc170d2fa94d7cf364b7,0xf51c4d7082fac712b64fd8a94bc2f30a1968fd950f536f3b7,0xf863bca952f7c21530df37b691a8f564c170fd2b49fa08d4,0xf9d80564a1f4d7b38acf8630a952f21537cbf0d2c17f6b49,0xf382b650d7f4b70a869f46352c1afd217ca9f8d4cb30f519,0xf68d217c49f508364d9fbc2530a4fb28ac156fa19f70df37b,0xfd21503864f1a4b3569f0d71c28af952b708df7cb63fca94,0xf2d7b38a05f30d49156f86b2ca9df5371a469fc70821fbc4,0xf9a864bc71f0596b2c4af215fac1f356fd49f37bfd82f038fd70,0xf1acb69d82f468371c2bf50d2f703bf4d7cf536f915fa80f49a,0xf9d7153bcaf952d864c1fa4d0f821af0738fb694f7c2bf0563,0xf5217368a9fc7083b651fd91a0fd4b7f4caf530f964f28df2bc,0xfc17b2568af07cb35128f50369f4c2df837df0a9df1a49f6b4,0xfd25370a19f7d4cb3051f59a46f821cafb496f2c7bf8d0f683,0xf7d8691c4bf7150d94acf2d46bf59a12f83bc2f08af307f653,0xf50a964d21f6bc708d95fc491af7b2c1f86352fb38a4f37d0,0xf952c4b371fa80512b69f864a03f653fd94fc1af7d0f82df7bc,0xf9a4c71536f507d2cb46f68037bf82b3f9521f0d8afa1cf4d9,0xf283bc1705f7b219d863fd03594f1569afd2c7f8a0f4cafb46,0xf683b4a159f6bc708a94f28d4c1f0d2caf7352bf9d71f3056,0xf49d71a82cf512d864a9fac7380fc196bf7052bf4d03bf563,0xf7359a8d2bf4a196382cf803b46fca056bf125fd70fc17fd49,0xfb7364d9acf0594b68d7f03b28afd25380f12c7fa4c1f6519]

def a14_10 : List Nat := [0xf49a12c7b6f4bc170a8dfb2d953f196825f7380df6503f4ca,0xf8a46591c2f369a0d715f7cb250fa12d4cf8d94b6f380fb73,0xf52cb70369f50a4b37c1fa912d8f08649df4ca17df6b2835,0xf1a94c2d05f7c125964df38d9170fcb4af82b6f8a0f3b7f653,0xfb7d9ac283f0d864a1c7f4d2b659f19637f503f152fc4bf0a8,0xfd08a156b2fc7b4d950af1703bc2f37d86f3825f469af4c19,0xfb69a82d07f49d80a12bfbca4683f15037f2c195f4d7cf635,0xfacb495038fa46b35170f0821c4df637b25fd7c2f869df91a,0xf2d7cb6491f382569d4bf4a07b2cf86371af51ca9f035f08d,0xf217b68d4cf0d2b49a83f2807d95fb364acf9650a1fc1537,0xfc7d4a863bfc491508d2f82b6953f64b7125fa0d9f073fca1,0xfc1a8053b7f6830ac215f8d4a952f7364b2df0719dfcb694,0xf9507cb38afc496530d2fac15280f9d864a1fb4d712f736b,0xf7d25683bcf4a0d82c19fb71ac46f2159d4bf9a80736f053,0xf4a12b38d9f86307d4c2f7bca9653f0d25f159f8a0f6b4f71c,0xfac17d8364f95307b2d4fb68a12c4f9a0dfcb37f5082f6519,0xf6b4d21ca9f2c4a08635fb3071a82f46519fd950f738dfbc7,0xf0a86bc495f38d07ca46f803517b2fd9652f4d73bf21cfa91,0xf6b7ca8d94f368250d4bf3512d708f719a03f4a1cf2bcf965,0xfa8056bc19f364a17c2bfd94b7352f159682f0d4cafd7038,0xf9a4d08256f912d8acb4f07c2b683fd953b7f64c173f50a1,0xf382b691a0f2ca953b7dfa4d07368fd805649f1c7fc4bf125,0xfd9a170382fd0596b4a8f94d7b351f73680acf4652cf2bc1,0xf2d80536bcf7b21569d0fd7382594fb30a864fc719a4fc1a,0xf9ac4b2d86f9125307d4f37c28a46fb659d083f17bcfa150,0xf953b280a1f52d94ca86f7b64d830f69a4bc73f7d051fc21,0xf1a4d837bcf15364b2d7f250ac491fd9682c70f56b308a9,0xf70d91c283f2d864ac71fb7d49a152f659f035fb63fa80f4cb,0xfc7b35194afc173652b4f86bc2d703f8a12f950af64d9f0d8,0xfb30d8a4c7f17d95680af4b637052df38215f19acf2cbf694,0xf651a4b2d9f1cb37d8a9f25380ac71f0594df7b630f682c4,0xfb6594ac17fa0d468351fb369a8052fd912c7f730f28dfc4b,0xf649d7052bf3b4d80ac7f196538a4cf8630d2fb712cf159a,0xf1c7d4a835f94b3052caf07b69d21af659173f682bc4fd80,0xf807194bcafc259d0364fc7b356821fa96b2d4f150af37d8,0xf8a91703b2f37b4659d8f51c7d4963fd2cb680f1a052fca4,0xf059a12d83fd07152c49f280ac7d4bf537bc196f8a46f3b6,0xf6b7350d94f17c2b3869fa8d703651fca082d4bfc4a9521,0xf2d836b491f59a082c71f653b7d4a8f4cb250d96fac1f037,0xfbc7196503f46b259a1cfd70863512fa837b49d0fa4d82c]

def a14_11 : List Nat := [0xfc4d7b3569af194af50d9f2d8f368f0a8f703fb64f215fcb2f71c,0xf4917056bcafc4b7f253bfd964f30d7f1a95f80af863f2c1f82d,0xf83651a4c70f0d73fb253fa950f1cb7f9d21f496bf8ac2f864d,0xf9d4b6521caf4a17cfb2cf37bf0d7f591f694f82df836f035f8a0,0xf94a0836b71f864b2f73bcf4d2cf9d8af1acf512f0d7f503f659,0xf28a4b7351cfcb2d7fd038f6508f9125f70a1f94caf64d9f63b,0xfa08651c7d9f738a1f0d4b7f2195f469f3b6f28df350fca4fcb2,0xf71536bc28df03b2df64a05f7083f5912fa869fc7b4fd94fca1,0xf917b65380dfd7368fb2503f4a82dfca07fa951f1c2f4cbf496,0xfa9638d7c21f73bc1f0a82df652b4f7b680f951f4acf053f4d9,0xf2c7b4951a8f170a9fb2563f46bcafc4d21fd968f3508fd037,0xf308a465917f1c70af2d7bcfd96b4f528d0f2b351f94caf386,0xf6bca082194f51a9d2f4a8dfb2c4f73bf7c1f07df659f350f836,0xf94c7350a86f25630dfd9a4f12caf7bc1fd807f382bf4b6f519,0xf9a1c7b6835f46503bf91736f2cbf215fd82f0a8f4cafd70fd94,0xfc194b650d2fa8d730f07128f53b2f9a15f9d46f7cbf638f4ca,0xf9d28635071fa94651fd7ca4f96b25f038afbc4f21cf73bfd80,0xf6b219a07d8f94ac15f71a83fcb352f0d28f5630fc4b7f4d96,0xf80d94c251af7c19a0f68359f6b7d4f3b217f3650fb4acf2d8,0xfb49170d863f9d7cb6f530a9f8a150f2564df2b738fc21f4ca,0xf4ac2b680d9f38a965f7d4630fa051f9125fc71fbc4f7b3f8d2,0xf6bc2159d03f8d7352fa07b38fca17fd4b2f964af91c4f6508,0xf968a12d735f03b715fc70a91f28365f4b6fcb2fd08f94df4ac,0xf2d4a863b7cfd03719f56b4c1f2bca1f5283fa059fd708f964,0xf307d25946bf7ca053fa17bc4fa80d9f2b4d8f1569f836f1c2,0xf96b7d21ac4fa830d4fc1563bf64b28f9508dfc7352f719a0,0xf0564acb2d7f49a17cfd036b4f538219f869dfc251fb37fa80,0xf9a46bc7305f94b351f2b7d4cf8d9652f70d21fca1f8a0f368,0xfcb7083521af69a4b3f6b2d95fa864d0fd7c28f15037f94c1,0xf37b2194a08fac1528f63b4d8f95071af6530d9fcb64f7d2c,0xf7d80a964b3f12d035fa17b68fc49507f1ca4d9f38256fbc2,0xf17d2b4a805f64ca0d8f8352f730f965f1c2fb63fbc7f94df19a,0xf12d4a803bcf0ac28d7f4b7cf652bf59d0f1537f638f91af694,0xf6bc2537d49f70a864bf512d9f6305fb382fa91f80dfc4af17c,0xf630d2bca94f28a4b7cfd4c17f968df3807f56b3f51a0f2591,0xf7d0821c4b3fa0719d8fac251f46b2df638f530fb7cf94af596,0xf659d4ac283fd8052b7f03bc7fa12d0f7153f91c4f69a8f64b,0xfa037d46b21f28a917cf51c49fb3507fd2569fca4bf8d0f368,0xf50a12b4d86f94a83b6f37c46f52803fc159af719d0fd7bc2,0xf73b64ac251f8694c1afd4b219f50a9f356fd82f07dfc7bf308]

def a14_12 : List Nat := [0xf1a4b3528d9fcb64d21f0a837df4ca9f0715f0368f2b7cf695,0xf350d94c7b6fa083b2cf17d4bcf651a8f469af5219f037f82d,0xfd4c1a95638f37ca86bfa0d7b4f12807f52d91fc2bf469f035,0xfa83052b719f821c4d0fac2d70fb637cf4a156f3594bf69d8,0xfd94c712b30fa4bc250fd7b682fa964d8f3708f536f1acf519,0xf2ca94d8051fbc70a82fa46591f369d25f7b4c1f730df86b3,0xf2b4ca0d915fd8a9507f8217b3f4d2c1af80356fbc736f496,0xf4d0536bca9f170a8d9f37d280f15964af3b2568fb4c7fc21,0xf64a0d2537bf2ca863bf1507d82f4cbf9d4f380f956f1c7f91a,0xf152ca963b7fb650d94fa195370f864afc7d4f2bc1f28df308,0xf517b2c4680f3b69d70fcb4d837f28a0df2591f563f1acf9a4,0xfa19536b2d4fd7c4b30fc21569af50a82f649d8f3708fb71c,0xfd286b71594f9d80ac1f3564bc7fc21a4f638a9f3b250f70d,0xf64b2517d83f286b70df537c4a0facb308f91af956f94dfc21,0xfd2807bca49f503b691f7364b21f59a1c2f8653fd0a8f4c7d,0xf1968d2507cf49d71acf0a4b738f159a82f0364df3b65fb2c,0xf1a94c25637fd96bc12f053864afb4d703fca82b7fd08f951,0xf49a12503bcf807364afb7c28d4fd71ca0fd956b2f915386,0xf59d2c4b680f630d719fca07b21f4651a8df37cbf5382f49a,0xf30d2b4a1c7f5638ac2f96b350af70864cbf17d82f915f9d4,0xf9507c46821fa4b2d71f630ac15f9d837b6f08a94dfcb352,0xfbc2507d863fb6594d2f469ac7bf380d915f4c1730afa128,0xf1250a96b7cf8a173b46f356f951f2cbf4cafd94f083fd28f0d7,0xf512ca07d46fa8037bc4fb694fd950f2b35f836f17cf19af28d,0xfa4b3086519fb649d052f3596f7d83fa128fcb71fac70fc2d4,0xf56b28d4ac1f3b469a17f52c49f2d91f836f035f7cbf0a8f70d,0xf7bc46359a1fb38d9152fd4a82fb694f0865f70acf37d0fc21,0xf56bc283719f63b251c4f2d0a1fca807f4b7df869df94af530,0xf59a4bc1703f7c2d96b3fd82b7f1ac49fd4650f386f512f08a,0xf250d8ac491f735682c1f3b708fa4630fb69d4f2d7cbfa951,0xf95308a4c7dfa056b71cf073b4dfcb2fd82f512f683f91af964,0xfd8217bc469f4b68ac2df3651c7f352bf94a1fa059f0d7f083,0xfc7b3649512fa8352bc4f682d4bf650a9f9d71f1acf073f8d0,0xf4637c1259af91703b4df51a8d0f82ca0fcb694f8356fd2b7,0xfb69ac280d4f38d7052bf4c12d9fa1568f35917f30a46fc7b,0xfbc71250d86f369a1c28f4b7356fd703b2fa08f4acf951f4d9,0xf9d08a46b71fa0594c21f307c15f369acbf6825fb4d2f38d7,0xf9a8d463071f0d21a495f1c4b25f9d7386f80ac2f56b3f7cb,0xfd9a07bc152f821a4c7df8694d0fb38ac2f736591f350f6b4,0xf64b2c19d08f2d4a9538f730a8df51ac70f17b652fb3694c]

def a14_13 : List Nat := [0xfd0a86b21c7f59d4cb70f371ac25f64b3f1965f803f82df4a9,0xf2b68a94c71f051cb4d7f0d952cafa1964f37bf830f563fd28,0xfb6835912c4f8d49ac70f64a82d9f3b256f150af7bc1fd037,0xfacb2864950fa96352d8fc4b3807fb7156f4d91afd730f1c2,0xf2d4a96351cf80521946f28d956bf1acb37fc4b7f38a0f0d7,0xf0521a968d7fcb465382f9d4ac15f036b2dfc4917f8a0f73b,0xf521a8d4cb3fd2b49507f380d917fac7b69fc15682f364a0,0xf3b650d4ca8fc17d9682fb4a08d2f53649a1f2591f7bcf703,0xf6b351c2d94fa4d08371f63059a8fc4b28d7f7bca0f91256,0xf4c215380d9fc1952d4bf4ac7d86f1a96b37f2b70a8f5036,0xf528ac73b46f9a0d2cb6f7d4c12bf519d803f70594a1f836,0xf2c4a056b38f6352d708f712b4d03f8d9afcb7f1caf915f694,0xf86b7d49152fa96530d8fd2c4a059fb364f0738f1cb2fa17c,0xf3807d21c4bf86b7194afcb28d037f0ac25f59a1f64d9f563,0xf835691acb2f08d2c495fd46370a9fa4b68f7d03bf152f17c,0xfcb7d4a9521f5630ac71fb38694c2f82d91af7350f80df6b4,0xf86b215370df69acb305f4c1a0836f917c25fa4d28fb49d7,0xf69a82d7153f7cb65083f19d07b2cf30ac4bf12594afd864,0xfd9683b21a0fc7b6519afc2594d71f807364af530f2d8fcb4,0xfd086b21a94f659d82c4f9152d736f53bc170fb7ca4f830a,0xf94d086b2cafd7c46528f0712d963f738a1cbf053b4af951,0xf94b256370af508a46b3f82159d03fa1968d2cfc17bfd7c4,0xf9d71cb2864f8ac4b350f659a4d83f9152c7b6fd0a12f370,0xf2b7d803691fca4d073bf2c1a059df4b6538a9f864c7152,0xfc4a05368d2fc173b4d9af28a1fb652f946f195f038f7cbf70d,0xf7d083b49acf4630a17bcf52c1f2d91f86b2fd8a4f5370f569,0xfa0836594c1fd917ca864fb69a4f2bcf521f73bf053fd28fd70,0xf4ca156382df96bc7308df4b719fa950f4a86f352bfd70f2c1,0xf19d4cb6807f6950d2b73f82c7df653b4fa038fa49f1caf512,0xf0a4b2c1537f7d49521acfb364cf03865f6917bf80d2fa9d8,0xfacb2d95170f4b3052c1af7d083f4968df8a912fb7c46f635,0xf9170a4c286fd4951a837fd9ac12f63b4f52b6fc7bf0d8f530,0xf152b469a07f912c4a865f82d730fd8350fb36fc1af9d4fcb7,0xfb491a8d036fa086953bcfc73821f564c2f1705fd4a9fb7d2,0xfac46512d80f2c196b705fd49a17f59d03f4a82bfbc73f386,0xf6b21a4c735f9a07d2c15fcb368af4d917bf5280f38d0f694,0xf652d73bc49f63591a4d8fc2830af7b2150fa9d08fb64fc71,0xfac12d7b350f64bc28073fd9a830f9568d4fb25196f1a4c7,0xf2863b7c4a1fa9d8356bcfc250d71fd4b2f951f694f037f8a0,0xfca17b28694f8a0d4b653f59a4630f7d80fbc73f12d9fc251]

def a14_14 : List Nat := [0xfd2594cb730f1ac708635fd4650a8f96b4af2b38f917df2c1,0xf8d2b65371af8630d4bc2f05964caf1c7d9fb7083f9a4f251,0xf46382b7d9afb35680d4cf0ac7125fa8d2c1f94b6f519f073,0xfb2ca469517f4d056b37cfa12d708f8d9a03f52863f4bc19,0xfd0837c2194f59ac17d82f569d2b3f64b703fa86bc4f051a,0xfd705369ac4fbc1a830d2f086594afd82c719fb64f125fb73,0xfd2b4ca8370f659d712cbf051c7b3fa194d80f68253f64a9,0xfc1537d2864fa125630d8fca917b2f69507cbfa083b4fd94,0xf2d4ac7b651fc28359d71f052b368af9a1f4bcf0d8f946f703,0xfc250719d8af7c49a086bfd28351a4fb463f21cbf30d7f596,0xf4b25691a8dfa9d7cb680f159463b7f82d03f5370fc21fc4a,0xf30512d8a96f682b71ca4f1a07c4d9fb652cf380d7f94b35,0xf280a1736bcfd7b38a912f64ac70d8f251c4bf956f9d4f350,0xf9d8a4cb635f21c73864bf2ca17d08f9152d4f0569af07b3,0xfd94b286307f2c73569a1fbc4d2517f0ac195f83b64afd80,0xf15308d9a4cf7cb4d21a0f7d059683f364917bf8ac2f56b2,0xfd864bc1259fb2d4a9637fc491538af82c71a0f6b305f7d0,0xf512b64d703f0a9d28365f968a1c25f73bca491fc4b7fd80,0xfc1530a8d94f71963b4d0fca4682d7f21a956bcf052b738,0xf2b691530d8f8a17d9463f52d4c7086fa950fcb4af73bf1c2,0xf3869d0ac7bfd71a946b2f9508d4bc1f28a4cf512f365f730,0xfb368a491c2fac4b73569fd8307cb64f80512fa0d71f952d,0xf7d963bc4a1f7b6512d83fc19a864b2f94d035f8052f0ac7,0xf2563b4d0a1f1ca837b69f153082bc7f864c2df7d950f4a9,0xf03869ac17df64d8a153bf9d2807365f91250a4fb2c7f4bc,0xf594b2d8371f7c1a8630df219650a4cf6bca9d4f7b35280,0xf50a4963bc2fa17382b4cf07d9a8653f1c7b64d2f0d8f519,0xf7d46528acbf37194a086f0d2b351c7f9a12c4b6fd95038,0xf517380d496f82b30a19df68a4bc253f59ac46b70fc12d7,0xf682d4ac719f4cb25638d9f159afb46f08af37bf035f70df1c2,0xf7d05912cb3f2d8a94b715fac70f469df1c4af86b2f038f653,0xfb70352d8a4fd956b371a0f15082fc19af4d7cfcb2f649f863,0xfa9528d7b30f6b4d91c738f0d217f8a150f653f469fc2bfc4a,0xf2bc71a8d95f49ac280d7bf64a03f21c4df3705fb683f9156,0xf59d2ca8370f253691a0d8fbc712f86b30f4651cfb4d7fa94,0xf71ca968053fd2564c7b38f0a4b63f28a1f195fd49f2bcf07d,0xf83519d2ca0f9a1cb36825f564c70f730df12b7f4d8af4b69,0xfbc46950382f8653b4ac70f94d0a1fc17d2f6b73f9a8df512,0xf69d821ca03f5194c2b680f59a4b3f1a837f4d256f07dfcb7,0xf64a952d038f8d912b370af496b7dfc15082fca17f653fc4b]

def a14_15 : List Nat := [0xf0594a1c28df538a9d2b71fcb680af3b4d70f7364cf52196,0xf1a8350d2b7f6519a07d4bf69d803f4952cafc46821fb37c,0xf68a4d2507bf17d9a0382cf73b21acfc4bfd80f591f653f964,0xf30d865912bf7369a8251cfc2d7b64fa4bcfa071f8350f49d,0xf56307128d9f52d73b68a1fa0d4c19f7b4acf5380f694f2bc,0xf8d7364bc12f694ac2517bfa9d2b38f08653f0a195f0d4c7,0xf51c2807b63f38d4ac712bfd0a8652f3059d7f496f9a1fc4b,0xf2c49a80371fa4b6382d70f91acb35f2b7c15f0568df64d9,0xf4bc2d8630af17c4d083b2f49537b6f9d7056f28ac15fa19,0xf3b64a95280f1ac70d94b2f517d8a0f3691cb7fc4d2f6538,0xfcb4d821507f649530ac2bf68a4c19f52d0836fd71a9fb37,0xf9a4cb7d036f351a08d2c7fa865071cf9125f2b38f49dfb46,0xfd2c1a964b7f5173b68d49fbc70d912f52830fac4f80af563,0xfd803b251a9fd28371c4a0f64912ca8fb7056fd7cb4f3596,0xf6b2538a1c4f96370d82caf30a4d7cbf7b4951f6508f2d91,0xf730d496b2cf7128650a4bf807d259af91538df463bcf1ac,0xf952ca807d4fd0a9153682f4a12b37cf0569d83f71cbf6b4,0xf9a1c2d7036f95280d4c71f56837b21f3b64a05f9d8acb4,0xfa8371cb4d0f7d91ac463bfb65308d2fc7059682f152fa49,0xfa9d71c4680f3b4a152c70fbca82196fb2d49537f638d05,0xf80d4cb7152f7c1a05638df68ac2b359f19d2f46bf94af307,0xfb4ac70d963f2d8a1946bcf128037d4cf52b71f6538f9a05,0xf95217364caf4bc7d03519f2c1a4d968fd2b38f507b6fa80,0xf6351c70a4bf28305649a1fd952bca80f968d71fc2d4fb73,0xf2d70594ca1f2864d03715fd8356b4a9f7b3691cfcb2f8a0,0xf6807cb4915f7d0ac2536bf2d964a83bf1a95037f21c4d8,0xf036bc152d8f4ca056917df37c21a468fd9a82b70fb4953,0xf37ca0d2b65f51c28d4b70f1a8364952fbc4a96803f917d,0xfd05682bc19f4d2c70a159f5369a8d712f4cafb64f3b7f803,0xf382b7ca4d0f12cb649537f91c4b3652df708df51a0f8a96,0xf0d864ac195fb69a082d4cfb49d738a12f2c715f703bf536,0xf6350a1cb49f712b30864cfb738a4d256f82ca9df519f07d,0xf82b7ca9463f4a08d912cbf4d05968a1cf352d70f156b37,0xf364d2c7195fb4ac125086f370a94cb28f569d8a1fb30d7,0xf4ca956370df1a03864b2cf6b71528a49f8053bc7dfd219,0xf468a12c70df0a9152b7d8f30596b4c17fd283bca49f653,0xf7368a0512cbfb352fd82f083f46bf956f7d0f1c7f49dfa4cf19a,0xf80ac19d2563fa4d8f1a95fc217f86b2f70df350fb73fb4cf649,0xf7b649a1c250f3680fb283fa0d8f7153f9d21fc4d7fca4bf956,0xf3712d9a0865f82503fb7c2f4d8af915fca1f07df4bcf6b3f649]

def a14_16 : List Nat := [0xfb64952d8073f12835f0563f9a86fd4a0f17d9fc4b7fcb2f1ca,0xf6b2c7194a08f38d46f9a82df70df1caf530f569f521fb37fc4b,0xf80d7ca12b36f6b4a9fc2564f3705fb71cf830afd49f159f8d2,0xf7d2ca80596bfd94a0f82b4df63bc4f3568f152f703f19af1c7,0xf2c73b651a8dfca964f17b49f507d9fa0d4f8036f2835fc12b,0xfa8d21946b30fa951cfd0869f25638f7d4a1fc7b2f5370f4cb,0xf94b6538ac71f05963f2bc15f2d9a1f8d4c2fa0864f73bfd07,0xf2d946b73508f63b4d8f0a83fc2bf956f70df152fca4f17cf1a9,0xf19a4d2b6807f03bc1afc28af59d0f7b4cf37d8f649f536f251,0xfc735912d864f2569a8f7b49dfd0a4f1507fca1f830fb36fbc2,0xfd2b36807c19f652ca9f0594af3715f8a12fb4d7f6bc4fd038,0xf173650a8d4cf64ac2bf3594bf9d286fc7bf0d7f830f1a9f512,0xf7364bc2519dfc12d0afa4c71f9a8d4fb682f307bf3805f569,0xfb7d49530ac2f837056f8a9d2f6bc19f17c4af364bf152fd80,0xf9d864b21735f25630dfa9150fbc496f7ca4df807b3fa1c28,0xf9a8d05364c1f71a4b3fc2d70af6b28f251fb7cf94df830f695,0xf03bc259a4d7fa1564cf82b496f9d21f0835fb637f0d8afc71,0xfd82c17b3594fb2d9acf08a125f4c70af6519f37d0f6b4f683,0xfd94b3071568f36bc28f0d4695f7d21cf52b73f9a1f08afc4a,0xf3bc21a468d0f49651cf4b719df9508af2d735f6b283f7ca0,0xfd05217b3864fa82bc4fc2d9a1f0ac7d8f6b49f356f915f307,0xf837c2b69a4df256308f3b7d05f68acb4f159d2fa170fc491,0xf12b30a964c7f59d863fc28a4bf25194df37d08fb6507f1ca,0xf5649ac12b30f2536bcf708a4cf1a0d95f837196fb7d4fd82,0xfca9156837b2f9521a4dfd28f70df0a8f350fc71f649fb4cfb63,0xf21a49650d7cf8d9ac46fb71cf2835fd2b4f307f591f3b6f0a8,0xf46b382d7ca9f59d8a12f6915f3705fcb71f0368fc4b2f0d4a,0xf7152d94ca83fd703b28f53680fa4d0f1c2f91afb64f695fcb7,0xf2b4d8630a15f7d94a83f07b35f4cb6f82d0fc217fa91cf965,0xfca86519d4b2fb712d83f82530f6bc73f4a1cf950af0d7f649,0xf0a82c7d4963f5086b73f19d07fa4659f3b2d8fcb4f125fca1,0xf4bc7d91530af0d463b7fa8d2cf94c1af6b259f73821f6805,0xf128d0594ac7f703569df4c152dfbc2f3b7f863fa19f8a0fb46,0xf1ca86b370d9f46352cbf9651a4fd7c4f0a95f217bf803f2d8,0xfc71a9d4b682f8d2b703f1cb365f7d053f9125f496fa4cfa08,0xf4ac2d70536bf8a1cb73f7c4651f2803bf694d8f1952f9a0d,0xfd052b3864a9f07c4d28facb7d8f351a0f36917f56b49f1c2,0xfb4ca0d71283f68052d4fb691c2f51a8d9f9a4f7bcf356f307,0xf9d730521c46fbca4956fd863b4f8a9153f280df70a1f7b2c,0xf69d73b4c1a8f638d215f7194d0fac7b64f28035f59a0fcb2]

def a14_17 : List Nat := [0xf95370ac2d86f7c1564bf28a4cbf94d71af05219df3b6f830,0xf73b2d8691acf159d7bcf4a056bf038217f4c2536f4d08a9,0xf521a9d46830fa07b694f17d08acfcb37f2c4bf563f951f82d,0xf8d4bca12596fb2c1946f0a4c715fd28a9f653f73bf07df830,0xfd73521a8649fcb28051f9563b71fa4b69fc4d2f038dfac70,0xfa825917c4d0f9d73564fc21507bfa4b69f8d2b3f8036fca1,0xfd7351a086b2f128d07cfa83b719fd952c4fbca4f0563f694,0xf83051a94cb6fa46912cfb3659d2f8d7352fd07b4f7c1f8a0,0xf649a0821cb3f15038d7f2b7359df6b4a19fac2568fd4c70,0xfd07c49a1528f4d712caf9637b2df591cb46fb683fa08f530,0xf1c735682d0af03b6915fd8364a9fca807d4fb2594f17bc2,0xf2b68a49507df915638dfb71a964fca03521fc280d4fb37c,0xfa1507b49d2cf35964d7f630d825f80a4cb6f9a83b21f17c,0xf6bca128d705fd4a91530fd259fc2b4f694f71cf8a0f386f3b7,0xf0368a491c25f12807b35fac71f9d0afd738fb4d2fc46bf695,0xf4b350d7c21af9ac46b71fc152bfd94f82df695f80af386f730,0xf0a9517bc283f708d94b3f2196bfa468fd4c7fd250f653fc1a,0xfd9a830517c4f70a4912bfc286bf7d253f63b4fac1f569f0d8,0xf07d951a4b28f364d217bf6bc19f50d86f352c7fac49f38a0,0xf1ca4d96b705f64b38a95f2d735f194c7f80a12fd8630f2bc,0xf8ac4d915630f1a0596b7f468d2bfc73bf5283f0d7f49afc21,0xf830564ca17df2863b70df537c12fb4a96fd49f2cbf08af195,0xf369d80a1c25f738a4651f5912d0f4bca9fb682f703bf7d4c,0xf6bc49512d83fd4a053b7f1a82c7f64b25f9680df19acf073,0xf256837d0a1cf951708a4fcb28d4f7ca96bfb364f2d91f530,0xf71c4a03652bf28acb69df1537c2f7d4950f3b468f8d0f9a1,0xf8d7b64c2150f8a1cb256fb370d4fca4917f2d9538fa9630,0xf68359d7c2b4f1250d49af36bc170f1965fa08f4caf2d8f3b7,0xf9682503b7c1f12d70835f36bca17f9465fa0d9fa4d8fb2c4,0xfd49a1537b28f3bc12d08f4a8652cf69503fac70f719df46b,0xf217368d0a95fb69d7083fa1c7b28f64915f4ac2df503fbc4,0xf7bca1953680fb64a0382fd8a9650f4c173bf7d2cfd49f251,0xf91563b7d08afb4d2537cf3864950f69d82bfa4c21f170ac,0xf5368a194b70fc465173bf7c1280df830a4df6b2ca9f52d9,0xf259d8a071cbfc28650d7fa912d4cf694a153f7b3f64bf380,0xfb4d056821acf1c259637f80a9153f4a8d2b6fd94c7f07b3,0xf52cb469d083fd2b659a8f2863b71f94ca051f7d4a1cf037,0xf153649a80d7f683b4d95f1a052b69fc21fc7bf2d8f073fa4c,0xf3b2519a4d07f1c4682d7f94b6508df1ac2f5369fa038fb7c,0xf0d82cb64a17f4b352d7cfb21ca837f9a036f6805f951f9d4]

def a14_18 : List Nat := [0xf569a1c7d4b2f491738acf359d807bf86bc2f30a46fd2150,0xfd49a80536b7f9d83b465f2d0a1968f7152bcf037fca4fc12,0xf2bc17380d95f3b4ca056fb7035196fd21a94fc28d7f8a46,0xf6825370a4d9f7b2d8ac1fb6380d7cf4c21a9fb46503f915,0xf2b730a91568fd083b4c7f071cb635f2594a8df964dfca12,0xf569a0d4bc21f8d7053b6f3719d280fc4952b7f38a46f1ca,0xf530a8d96bc1f4682b70df38052c4bf594ac736f2d71f1a9,0xf59d217ca4b3f7d869a03f1564c28af91cb70d4f0836b25,0xf5364a08d2c1f7ca830521fb682f9a1f965fb4cf73bfd70f9d4,0xf96b4c15038af0864952b7f73bcf21acf7d91fd0a4f563f28d,0xf15038d96bc2f071a4682dfb4952fc19af7d4cf536fa08f7b3,0xf650d9a12bc4fd7b4a8352fca082f694d8f159f36bf7c1f370,0xf3649d2cb708fac19528d0fb4a12f503b6f68a9f1735fc7d4,0xf682d4ac1953fd08a12c49f2517bf307cbf9a056fd837fb64,0xf69a08d217c4fb7d9538a4f5194d0f2568f307fcb2f6b3f1ca,0xf6bca8307194fd73b21568f82c1a0fd250f9536f4b7cfa9d4,0xf70a1c4d956bfa46305219f38694bfd7ca8f1735f82d0fc2b,0xf517364a9d80f95382b7d4fa86b30fc2d07f19652fca1fb4c,0xf64d07ca952bfb4c215037fa83bc1f80a496f9d71f635f2d8,0xfb371ca80d94f36912c4d8f7b682df507cb2f51a46fa9530,0xfd803b2ca964f1a49536bcf837156fd05219f70a82df7c4b,0xf2d7b46530acf2869507cbf371c4a8f8d0f125f49df1a9f36b,0xf4638d25071cf803b7d912fac73568fa4d0f951af6b49fc2b,0xf694ac152d08fb6507d4c2f0a8d953f17382fb463f1a9fbc7,0xf156307b4ca9f3596bc128fa0d9468f7d4a1f3b2c7f8d250,0xf2b73691ca05f17c283b65fd21a864f308d95f4a9f4cbf7d0,0xf1537d8a96b2f4659d071af382d4cbf94b7c1f50ac2f8036,0xf0d4c2b38a95f037d94bcafb7c1a46f915286f80712df653,0xf837b694a12df30a917c25f8ac4d70f682bc15fd059f4b36,0xfb64a9d7382cf4c1530d2bfac70521f917b365f68d49fa08,0xfd91537cb4a8f7d052c46bf12d49a07fb382f6803f956f1ca,0xfa4b2c735680f2d4c17b38f95036bcaf19d8af215f7d0f469,0xf951703b68a4fc19a0d837fc2805364fa12bcf652d9fd4b7,0xf30869a17c2bf7d8a0536bf70d91283f4d251cfcb4af4659,0xf7d251c4a863f53082c719f0a96b38df46507bfcb21af94d,0xf3691a8d2c70f4653b217df837b4ca0f286bc15f59d0fa49,0xf2d9650a1c4bfb7ca95386f912807d4f364a8d0f7152cb3,0xf5128d703b69f864b2d91af9ac250d4f4cb7380af356f7c1,0xf3564bc28d70f694d0ac7bf50863719fb38a4c12fa152d9,0xf082c159a4b3f50a837cb2f17b68d4cafd219f7d0f635f469]

def a14_19 : List Nat := [0xfb71503694acfb4c19a0d2f59d708a12f837c2fd864f53b6,0xf682d073bc15f5217b4a83f91ac7d805fc46b2f9630af9d4,0xfb2d8694ca07fd051c2837fd9a803b64fb4a17cf9521f635,0xf350d94682c7fc4b703691f59a4d83b6f2d71acbf521f80a,0xfd0a86b71952fa1cb28364fa9d703b4cf08d4965f537c21,0xf2b70a9d4638f0d8ac2195f371a49680f53b4c7d2fcb651,0xfd4b2591a837f5082c7b36f9ac170d86fd94a03512f6bc4,0xf6951a0d7b38f4ca805219dfd82fbc2f71cf46bf365f49af037,0xf4c71a8d2596f5194bca086f3b28fd4a9fb736f035fc12fd07,0xf9d28a4c1736f156b380ac2fb2594fd468f70df530f9a1fb7c,0xfc7196530a4bf2b3807d9a1fc4951f6b73f28acf2d05f64d8,0xf94a80d2c736fc125038d7bf4b356fa9d4cf82b6fa071f159,0xfc2b371a0d94f307d4ac196f51286f8a950fd2538f64bf7bc,0xf950ac1286b4f2517b38a4df964c7dfd80f037f653fa19fc2b,0xfca9d8256307f83517d0a46f591a80f4c2dfbc12f4b69fb73,0xf50a912c4d73fb649d8a1c7f7152d0fb3082fca4bf638f965,0xfa0863bc17d4f5964b2d830f94c70dfa8219f56b73fac251,0xf8a037d96512f64ca17052bfd2c7b4fb3591cf836f80df9a4,0xf5964bc71280fca491568d2f8a0d73f4c1a9df36b25f703b,0xf9d4a07c2b35f4b6830d719f82569af508d21f7364cbf1ca,0xf17368a94b25f4ca12807b6fd83bc19fd7c2fd4a0f053f695,0xf38ac712d965fd7b68250a4f1594b2cf63bc4f073f91af0d8,0xf05128a94bc7fd2b3680ac4f2c17b65fd9537fa4691fd038,0xf83594a17cb2f56b4d08ac1fd7364c2f0a9125f03b7f69d8,0xf82d07b35946f8d4cb21963f37d9a80fa4b650f17c25fc1a,0xfc7b256308a4f70acb49d21f537d469f82c150df86b3f19a,0xfacb7d250869f1a0d4c73b2f4b6538af1c28d95f7194630,0xfc2d9a0356b7f5073694cb2fd4b38217f8a46f159f8d0fac1,0xf08d9651cb73f36b4d059a8f0a4682d7fac491fc217f352b,0xfa82c46b30d9f4b7368d219fc708352bf71a4dfa051cf569,0xf2d7c4a03b68fd835217b49fca805691fd07364fa159fcb2,0xf3bc4a0d8695f637d91a82bf07b4d215f4652ca9f71cf038,0xf52b37c1a869f07bca9d283f2c4a0d71f6508d4bf635194,0xfd73521a86b4f05649d2cb3f95170836fb7ca0d82f9a4c1,0xf94b63071c2df468253bc7dfa837b2150f8d0fac4f9a1f956,0xfc21a038d94bfd0825963b7f6b2d4c735f0715fa468f19ac,0xf9d082cb651af8d2b7c4a03f68ac17053fb4d73f9521f496,0xf64a912d07b3f56b4c7d8a1f2bca05968f352c17f083fd94,0xfd25173b4a08f68a1cb7d03f564d9ac70f953821f4c2b69,0xf73649a0512bfd7cb308652f70d82c4a1f538ac19fd96b4]

def a14_20 : List Nat := [0xf952cb38071af2b7350ac4df91c7d0364f5128a4b6fd869,0xf968d0acb251fa4b7053821fd2c495637fb308a9d46f7c1,0xfbc4a08369d2f9530d46821fb6507d8a94f1ac7f251cfb73,0xf49a12c7350dfac4b7d9638f564a071cb2f03b68f2d8f951,0xfd21ac7b4630f94a0568d71f37082c4d95f96b38af152bc,0xfa836952d71cf0a94b28653fb708d91a46f4d0512cfb37c,0xfcb65307d21af2c159d4a08fb250d83694fa917c468f37b,0xfd4965280a17fca9d2b63507f864af0d83f7b3f195fc4bf2c1,0xfd251964b380f7d8a12c4953fca07f5630f2b68f9a4dfb71c,0xf17d03b2564af80537c4b69afb70acf9d4f863f2d8f1c2f195,0xf59a128d4b70fc7152b3694af1c2d9fd730f6835fc46bf0a8,0xfc71a83056b2fc128d0a953bf36807f9d251f4d7bf4caf469,0xf9650d28acb4f59d830a17c2f4c19af73680fb7d46f512b3,0xf2bca837d491f03568d2c4b7f51a0d9f469af5280fc71fb63,0xf368a052c4d7f82d94ac1530fd83b70fc712bf46bf956f9a1,0xf2c4d7b38a91fcb2805964a1f4b68d9f37156f0d253f7ca0,0xf2d0a4b71568f6b2c491a803fc7d83bf1259acf0537f964d,0xfd82b73691a4fa9512d7cb38f0ac49df7052c1f03568f46b,0xf4d7b2c1538af917c4b36805fcb6521af0a9df8d2f964f703,0xf6b2c4a8d035f4d7cb380a19f1ca9682f7364bfd259f0715,0xfac468d07351fcb30569a4d7f217b495fc2d91f836b2f80a,0xf1cb2837d0a9f508d2ca17b3f8a4d956f307c46fb496f215,0xf650d7c12b49f2cb38a4d915fca95364f80a17b6f370fd28,0xf07c251a869df0acb3649128f2d71c4bfa9538d4f73056b,0xfc1708d4b652f0a82153bc7df9d2b7305f638fa4cf964fa91,0xf2d71a083b65f21c730d864bf491507bcf6359fd4a9f8ac2,0xf3691a4c2507f8a9517d46b2f7b49d21cfbca03f8356f08d,0xf7d0ac215963f3b68d91c705fa82d4b71fbc4652f308f9a4,0xf1a952d8307cf153b694a082f19d05637fca864bf2b7d4c,0xf59a071c46b3fd4ac7b21569fa194bc28f52d7380fd8630,0xf36594cb2807fa8d46b71250fa9d0351cf38691a4bfd7c2,0xf8694b25037dfca83b719564f1536bc70af4a9df280df2c1,0xf64b719d8305f280ac73b695f3512d4a86fc49a1fd70fb2c,0xfd071964bca8f536b7c1a4d9fc49a037d2f25683bf05128,0xf4acb7125086f9538d4c70a1f51c2d94b6fb369a82f730d,0xf7d86305912bfac7382564d9fcb4a170d2f53b694c1fa08,0xf7b4c12d9a03f286594a17cbf8ac251964df5083fb63f7d0,0xfc12596b7d4af864cb35071af2d0365194bf80a9df37c28,0xfc7b286530d4fd7150836bc2f073b49521af4a8d96fc19a,0xf4ca12b37d96f4a0d825917bfc2d49a8051f07cb653f368]

def a14_21 : List Nat := [0xf2b4a95630d8fca0719d253bf8694d7c150fc46b738a12,0xf70a94b6512df952863bca4df4c2b738a196f8d0f053f7c1,0xfd96b7128ac4f2d07359a1cbfd80a49152c7fb3864f0563,0xfd869a1503b2f70d4912536bfca0837d9564fc28a4bfc17,0xf17bc4630d95fb2c19a837d4f3b6821ac705f0a49652d8,0xf68a05371c2b4f4cafd94f7bcf63bfd07f91af596f28df215f803,0xf519a86b2d730fa170f2538f64b3f80dfcb7f4caf21cf695fd94,0xf1cb259d0864af830af7b4df94caf5370f9156f17c2f2d8f36b,0xfa173564b2d80f83052fa968f7d0fb63fc12f915f49dfcb7fca4,0xf8d2ca0735196f4cb7df63b4f256bf1a82f50d9f9a4f803fc17,0xf683b7d4c1259fd9a80f37ca0f194af5170f653fb2cfd82fb46,0xf80351c7d2b4afb382cf564d0fa94cf68d9f5219f70a1f37b6,0xfb2d94ac17086f538a0f2c7d8f364d0f91af569fbc4f73bf251,0xf2d94a07b351cf64d05f8037dfb6382f9125f68a9fc71af4bc,0xfd7152cb680a4fc73b4fd2b70f8d963f128a9f5649f305fc1a,0xf730821acb64df38d25f68a95f0d915f7b2c1f7c4a0f694b3,0xf4b2568371a0df07d9a8f350f915fcb7f4caf2c1f63bf946f28d,0xfc19d4b286507f536bc2fa0d8f12d7f9a15fa4cf964f73bf083,0xf0352c71a869df64d215f708dfa950f4c19fcb4afb382f36b7,0xfa968d253b4c1f4ac7b6f38217f0563f915fbc2f0a8fd94fd70,0xf7b695382ca0df9d2564fc12b4f8a4df7051f3680fbc73f1a9,0xfac71964b2538f70594df12c4afcb651f9a0df3680f8d2f3b7,0xf7359a0864c21f94b251fd28a4f650d9f307d8fca1f7bcf36b,0xf86503b4a912dfc7152bf7d96bf49536fac4d0fa1c28f3807,0xf86b71c4d059af7ca4b3f07d91af28df2cbf308f649f563f512,0xf70acb6538d21f682b49f308a46fc251f4d7cf950dfa19fb37,0xf2cb4a1703568f3694d8f1c46b2fc7d9af52d0f80afb73f915,0xf0d83bc46591af1537c2f1ca4d7fd9a82f507b2f694bf3086,0xf2d7cb3864a15fa91280f4b6359f50d96fca8d4fb71c2f370,0xf564b2c738a19fb69a4cf36807bf17d0acfd49f521f530f2d8,0xf49d8a12c7b36f9a0356fd71952f0d4c15f286bf7083fb4ac,0xfc21530d4a96bf82b463fca0594f1a807cf2d865f719df7b3,0xfc4b2d9a15037f1963b7fcb6521f8d4ac2f946835f07df8a0,0xfca9152d036b4f594683f712cb3f08d965f70a82bfa4d7c1,0xf7ca4b2196503f53b71c2fa951f6bc4fd82fd49f07df80af863,0xf96538ac4d071f8d94a12f7b2dfc152fb37cf0863fa059f64b,0xf0a836b2d91c7f649ac28fd4a17f73bf80df503f512f569f4bc,0xf3b468219ac70f517d496f38a05f259dfb637f4c1af80dfc2b,0xf59a46bc12830f153b4caf71963f8652df2b7cf0d7f8a0fd94,0xf917d4a86bc25f964b28df56380fa12d0f7c153f7b30fca94]

def a14_22 : List Nat := [0xfb708d2c49653f9d46b25f71503f8a912fac7d0fbc1a4f386,0xf4ca19652830df7c2d863fd7b359fb21cf7051fa49f08af64b,0xfb4a9d07c1253f71acb63fd7b2c4f86503f946f8a0f591f8d2,0xfd80a4953b2c7f1cb4637f68307bfd9ac4f5196f250dfa128,0xf0a4c7d956b38fd8694b2f9a82c1f7bca1f30d46f0735f251,0xf3507d49682cbfd083652fb21c46f730a4bf1ac7fd9a8f519,0xf64a07b382c15f12b69d7f0352d8f68ac73f4950dfbc4f1a9,0xf2d730a46bc15f8a9d053f49568df917b36fb4ca12f7c280,0xf946b3715082df0d8acb7fa0352b4fc4d7f21cf368f956fa91,0xf07d9a4b63825fd8a1530fca08691f6495fc2d4fb712f7cb3,0xf1730ac4d96b2f2c7b4a8f3bc1946fd8352f0865f9a15fd07,0xf3508a49d71cbf8d4b256f382c7b6fca964f1a0d2f073f519,0xf08364c259a17fc12d73bf4a0d86bfa82b7cf9651f035f4d9,0xf7c4b21a9680dfd2530a8f5946b70fd91ca4fc283bf71563,0xfa4b65280d91cf1a8d7b2f830a946f3bc705f963715f2d4c,0xf9a4682d73bc1f2b7ca15fd4c2170f36b49d8f350f695f8a0,0xfb7c1950a82d4f96b2c4afb3521acf30d7156f9d864f8073,0xfcb2569a4d807f19d7382fa863b71f3594ca0fc150d2f6b4,0xf91a083b7c465f6b4ac173f9a86f125f305fd28fd07f2cbf4d9,0xf3bc469d0a825f7b65912cf4d2bf8036f37d8f1507fa49fca1,0xf3b4d28a91c70f52b69d73fc217bf5946f0a15f863f08dfca4,0xfb37d964ac152f1708d4c2fa0d28f594b6f368fa19f530f7cb,0xf630a9517b2d4fd0538a49fc73b4fc196bf2ca1f8256f8d70,0xf5371286bc4d0f07ca1963f4659afd2b49fd7b38fc152f80a,0xfb2c1a80d4956f382d7196f9d864afc70af521f035fbc4fb73,0xf0d7c28a964b3f94d80ac1f4a12bcf637bf0517f3568f59d2,0xf7c153b64d280f52ca9630f1a8659f0d94af17b2f7d83fbc4,0xfbc70d4682153fb6952c17f650a83f7d803f49d2bfa91fca4,0xf59a46b7c2d80f8ac17d03f3b2196f51a073f8256f4cbf9d4,0xf17b694d0382cf7d952b4cfcb364af086537f150a9fa8d21,0xf5638a12c7b49fd051c469fa03719f253b68fbca4d2f8d70,0xf28d4917356bcfc469d2b7f59a4b30fd07f8a0f1caf368f251,0xf0351a9682c4df6591ca83f94a052df3bc7f217bf08d7f64b,0xf7c4b2569a830f1cb7d082f468d2caf0a195f1537f49df36b,0xfa0d83517bc49f2b4d7365f59d2c70f086b3f1a469f8ac12,0xf9650d4c7b38af736b4ac1f94680a1f307d95f521f8d2fbc2,0xf156830a9d2bcf528d4963f7b64a80f05917df37c4bfa12c,0xf5369d4a82170f591acb46f0d2c49afd73b68f152b7cf083,0xf71c4b68d9503f63528a94fb21a4d7f2cb380dfca07f9651,0xf96538d21acb4f7150a463f2b7c195f2c4d9a8f086b3f7d0]

def a14_23 : List Nat := [0xfd9682cb370a4f4b6591acf3508a946fd038fb2d7f71cf152,0xf7c4b28a19650fd8637159fbca0d253fd46b7f038f2c1f9a4,0xf12538d4cb70af9a86b37dfc2b46517f94ac1f96305f082d,0xfc19d8a0736b4f712803bcf538694d0f52ca46f2b7df1a95,0xf491a8073652df69d8217bf9a468305f153b4cfac7d0fb2c,0xf52d4680a9173f6b7d9503f694ac215fa1c70d8f82b3f4cb,0xf9a8350d46bc1f2ca03715f28d7b4a1f7c49680f2b3659d,0xf512d708acb49f9d8364a1f69a03528f4c2b650df7c1fb37,0xf4659a1c7083bf4cb2869dfa053712cf152d8a49fb7d036,0xf56837b4d0a12f8ac469d70fc17f2d8f94af591fb2cf350f63b,0xf68307159ac4bf91a052b7df4d8af37cbf80d2f2c1f653f496,0xfc25917b3680afd7c4a8350f69a15fb21cfd82f4d9f073f46b,0xf70a4cb638d21f7350d91acf803b2f51c2f9465f8a96f4b7d,0xfd07156b49ac2f03bc4a195f1c7b2f637d8f3528f9d46f8a0,0xf682b30ac1594fd738a96b4f1a4c2fd0719f8052df536fcb7,0xfa0715638d2bcf95280d7c4fa4d968f1c2f305fb37f64bfa19,0xfd91a4bc28037f7b21564d0f8a052df683bf9635f9ac4fc71,0xf1964b7d2530af5173b28d9fca836bfc70d4f8650fa94f1c2,0xfb30517c28d94fca86912d4fcb70a1f64a95f0837dfb2536,0xf38d0a91c7b25f3bc215086fb4d956fa82d71f694f4caf307,0xf1ca94b703825f7c2b3568dfa4d950f8a12d0f73691f6bc4,0xf536b70d8ac19fcb37d9682f94d21af50a4b2fc71564f083,0xf5694a128d730f9a807bc15fca0d917fc2d4f53b2f368fb46,0xf703b2d9468a1fb69ac2837fc7d0591f4a08df4cbf536f512,0xf8ac2d4651730f7c12b38d0f9d7b4a1f86352fcb694fa059,0xf3569128acb70fb680517c2f2d0a495fa9d4c1f37d8f4b36,0xf80a952bc1736fd912ca830fd7051a4fb35694fc7b64fd82,0xfc173b2564d9af2c4a8350dfa159630fb682194fd708fb7c,0xf056bc4d9a837f821a03b7df4680d2bf91c2536fa49517c,0xfd8a91c7352b4f0d95682cafcb7d21a4f7051f496f36bf083,0xfca053b712864fd2b651a80fbc703694f2c195f9a4df8d73,0xf7c1a4b695283f4ca03519dfd2b36508f68a94f12cb7f7d0,0xfd4c2150836b7f2bc19a865f4695370afd94b30f1ac7f28d,0xf96b4a82d7c15f1738d0ac2fc468053bf7b25630f91af49d,0xfcb3652807194f7c12b4a03fb7d2ca96f8350d46f9d8a15,0xf380564a17c2bf7d91528a0fc4b6359afcb730d21f968d4,0xf82d7cb495630f46b250a8df170d96835f37bfac4f1a9fc21,0xfd2bca4915680f7b69d8350fa0371c259fb463fd7c4f128a,0xf9468a1cb352df96507b2caf12836b4c7f7308dfd0a4f951,0xfa86b4d2507c1f4a08d73bcf19d0382b7f9ac215f649f635]

def a14_24 : List Nat := [0xfa4d7351286bcf5083b7c46f9d0a1c2b4f196307fd259a8,0xf356b217ca9d8f59682cb30f2d7364c15f7b491a0fd08a4,0xf3b2d71564a08fcb7368d91f307c4b695fca94d052f821a,0xfb3564a9d807cfa0d736b4cf968a152d4fb71950382fc12,0xfca128d95037bf53b2d07196fc152f7d4cfb46f386fa80f49a,0xf28351a0d946bf4a8695217bfcb37f0563fca91fd708fd4c2,0xf7d053864a12bfca96528d4bf4c2d9f36bf915f703f8a0f71c,0xfa083569d7b4cf6371950d2bf703bcf52c1f8a12f468df4a9,0xf0a95283b64d7fb730d8a12cf49d2bf50863f9651fc71f4ac,0xf1946b2d038acf28d9650a4cf4bc7df63708f59a12f7b351,0xf4d9563b7082cfb2d0a4691cf4b68a9f71acf7d83f521f350,0xfac153b682d94f4638d7052bfc4d037f7bc21f956fa19f08a,0xfd951a46807b2f9128d03bcaf637c25f0a835f4c17df94b6,0xf9528d7036b4af2d91a0564cf538ac1f49680df73bcf2b71,0xf46b7380521caf1a07c2b369f5682d9f17d035f4d8a9f4cb,0xf659a4c2d7038fa0d917cb28f08d4635f694bf125fb73fca1,0xf07d9a1564b38f49173052bcf1286b7cfa8d2cfa4d0f5963,0xf96503b2c1a4df946b70d835f80ac736f517d2f9128afbc4,0xfa1283bc49650fb2c1536807f037ca8dfa4d719f52d9f4b6,0xf9d28a07bc465f0386b2517df053b4d8f7ca4963f12cfa19,0xf7d8364a052c1fb6915370d4f8659a12f803b7caf9d2bc4,0xf4b28a173059df91c2d08356f64ca07d8f521fb7cf3b6fa94,0xf536bc7d8a491fd469ac1730f2c4b70a1f52d9f83b2f6508,0xf4ca08369152df9d07b6821afa8d7c2b4f173bcf6594f503,0xf65219a4c70d8f64d7150a83f2b695308f49d2cbf73bf1ac,0xf96803b2d7ca1f4bc15638a9f46b7359df128d07f52c4a0,0xf9680d71a4c25fd219acb364fa8d94b70f82b6503f37c15,0xf3680d91ac4b7fb2594d8a03f2c170538f6bc7d215f9a46,0xf9a4b382d07c1f3517d4c2b6f037bca125f4956fd869fa08,0xf64b7d9ac2508f0d4956b28af4a12d83bcf35196f730fc71,0xfc2d8a946503bf9680d4ac15fc4b638217fa07d91f352b7,0xf12596803b4acfb2c738d056fd4cb70a82f649a153f7d91,0xf4b736950821cfa8d03b2c71f0acb652d7f4d915386fa49,0xfc12b64d7038af652c7b4a08f9d05173bc4f9536f91afd28,0xfa4c7b3691528f2d95370a1cf56b217d830f864d0fcb49a,0xf519d70ac4682f37bc12d496f2c71a8056bf4b359afd830,0xf7b4d963082c1fb3512d8a46f568370acb2f594c7d0f9a1,0xf2d4b308659acfd82bc73519f0a8364c17dfb694a12507,0xf52c17d4a8369f86512bc49d0f0ac7f035fb73f19afd28f4b6,0xfd80a96537cb4f7b28a463051fca12f491cf83b6f2d95fd70]

def a14_25 : List Nat := [0xf71cb4a869503f64d9a07c215f491acf3825f2b7dfd80fb63,0xfd825073bca94f517d2c4a803f7c12bf9d0a1f6b4f638f596,0xf3821a9650d4bfd25364a0719f68acbf4951cfd7308f2b7c,0xf4d2bc71a0596f637b4ac19d8f9a82c4f53b6f0d7f521f803,0xf2b7ca463519df8a96521c4b3f594d80fb682cfd730fa170,0xfb368219d07c4f0a17b2d4695fa8352cf1cb65f7d803f49a,0xf96b4d80ac715f73bc1a8649df2c4a91f382b70fd052f365,0xfb4c7d259a836f217b350a4d8f5680d91f496fc2bf730f1ca,0xf30d82b71ca46fb4952d70a86fa12c4d9f1965f3805fc73b,0xfb350ac712864f1cb25630d4afd8a94c2f7b69df7083f915,0xfc4d03596b21af2cb3649d705f15680a9f37b4a8f71cfd82,0xf69d4ca83512bfd0a4bc73652f94682c1f08d7b3f1a9507,0xf682173059d4bfa1c2d083569fb364ac7f25194cbfd70a8,0xf8d7152cb4630f69a1c4d2835f4a86b219f70acfd950f7b3,0xf0863bc1594d7f69d8ac21735f4c7b2d0af50382f1a9f4b6,0xfb70519ac2d86f569d4c173b2f80d7cb4af21a038f59463,0xfa07bc1963528fd9564a12b30fd80517c2fd4b6837f4ca9,0xfb2d805917c46f52ca4b30d96f128a07bcf351a94d7f368,0xf8352bc4d9170fa46b37c2150f6594b7d03f8a96f28dfa1c,0xf495368d71c2bf519d46b7382fc4a96503bfac708f1a0d2,0xf6b7c4d219a83fb2594a17d03f80ac1569dfc2864bf5370,0xfbc250d8a4637fa15382b694cf2d4b30a91f59d7086fc17,0xf537c2b4680a1f71c4a82503bf9acb638d21fd70f94df965,0xfa1259d7b4680f9a82c4d03b6fcb2d836507fac194f7153,0xfb637ca80d952f4d2c17b3056f4a07d83519f96821afbc4,0xfcb7369d2508afc17d0a956b4f703864912cf82b351a4d,0xf2b735680d4acfc4b69a83071f28d7cb36491f051af59d2,0xfc1a0d86537b4fd9128acb307fc71508364d2f52b69f4a9,0xf8d9a071c4b36facb28351964f12c7d49508af730d256b,0xf95371a082c4dfb305691ca8d2f215f70df4a9fb64f863f7cb,0xfcb650382d917fb4c2159a8637fd708f4a0df352bf1acf469,0xf96b3508217d4fc1a9d2568307f7b463fa0d8f915fc2bfca4,0xf9152b364d08af94b712d83056fb682cf9537df1a4cf07ca,0xf63082591ac4bf51c2d70a4683f2173bf94d8afd9650fb7c,0xfd7ca830564b2fb73528691a4cf9a0715f1c2fd08fb36f94d,0xf468037d9521af638d0517bc49f91c28afca07fb4d2f653b,0xf5682b30d4a91f7b46359d21a0fc2508af96bc4f738dfc17,0xf64cb7d0a8259fb638071ac2d4f19d865fb21c73f305fa49,0xf4c1a8052d96bf912ca468d035f17b365f82bc73fa07d49,0xf12c7d4a05369fb4ca152d0386f7082bc1f4956fa8d9f73b]

def a14_26 : List Nat := [0xf359d7c1a086bfc4650d83719af96307b4f2d4a8fcb2f512,0xfa4d073596b28f63052d9ac7b4f83bc156f0a17d8f2c491,0xf64bc7d059a83fd4c2b70a1968f6b30825fd94ac12f7153,0xf03bc259d864af694d2150837bf8a17c4b2f9ac1f653fd70,0xf0d7b3864c21af8d9170352b4af82d49650f59ac1fb637c,0xf9a05637c12d4f17d82bca4695f386b4c25f0d91a8f7b30,0xf5649d0837b21f86307c4a952dfa053bc28f7d4b691fc1a,0xfca08219536b7f4d8a1c2b3056f3869d2517fd70f49afcb4,0xf83715964d2cafb25368d7c194f4cb30821af6b705fd9a0,0xf70a953682b4dfb7380521a496f9d8ac4651f2d03bcfc71,0xf6382150a4c7bf952c1a8d73b4f0719d4653f0869acb2d,0xfac170386b2d9f94a80d736521f64d82cb359f051af7c4b,0xf5637b4c1a9d0f19528acb64d7fc70a4968d2f153b2f380,0xf64d912bc7038fa17b36950d2cfa08d7356b4f49a8251c,0xfbc4d0a965382fd917ca4b6308fa8649507d21f251cf73b,0xfca864b30d217f96b7d4a052c1f51a94cb2836f59d8073,0xfcb735219d864fa0d7c1596b28fd4b365071ac2f038f94a,0xf517c2b49a836fca4d0537b691f2864cb307d95f08d21a,0xfc4d7152b3869af4a19f50d9fc21f08afb64f7bcf2d8f370f356,0xf730d21568ac4bf9d46f8352f708df94a1fa950f36bfc2bf1c7,0xf2c4d91a80537bfca03bf4b6fd70f17cf863f956f9a4f251f28d,0xf6b71ca4d28359f4c7d9f0a8df6508f364bf1a9f521fb2cf037,0xf9d28073bca465f36b25f0d83f7d4bf17c2f1a05f9a86f94c1,0xfc253b649a08d7fd4a82f9150df217bf037f683f1cafb4cf596,0xf1950a468d7cb2f83652fa80d9fc4d2fb694f307bf7153f1ac,0xfd4ca037125968fd28a9f36508f1cb35fa491fb2c7f07dfb64,0xf7d956b4ac1283f53b71f0d863f2c705f4cb2dfa91f08af946,0xf82c19a4d70356f3b496f2517bfa837cf059d8f0a12dfbc46,0xf7b350d4a8691cf5637d9fa94cf1a07f2bcf64bf28df083f152,0xf80acb2537194df159d2cfb4c7f3650fa821fb683f469af07d,0xf569d4b371a082fa8d2bcf46b7cf1c2f591f386f0d7fa49f530,0xf059683bc1a4d7f94630df219acfc7b4f5371f2b65f80af8d2,0xf712d94b6530acf8d4cb2f8364af08695f2c15fa91f70dfb73,0xfb2d91c4a80536f7b4651fa9521fd8694f3bc28f70acf7d03,0xf7c28d9a4b3051fb21a86f91c46fd2594f0837df0acb7f653,0xf1736b2c4d8a95f49653bf830a46f0825fd219f7cbfd07fa1c,0xf56b712ca4d830fa9d7c1f0d2b37f86352f0a8f496f915fc4b,0xf351ca4b2d7086fd9a128f2c4d05f6b719f5649f038af73bc,0xf2d4c1a953086bf46517bf821963fca052fd94a8fb37cf0d7,0xf9653bc21708d4f0ac195f2d9a15f82b64af37d0fb7c4f638]

def a14_27 : List Nat := [0xf528036b7d49a1fd05912f3b4a07f9d8356fa864cf2cbf71c,0xf170569a8d4b2cf3086b7f359128f1a0d25f364acbfd94c7,0xf170568ac2b4d9f0a9537df4c1af215fb7cf830fd28f63bf964,0xfca0563b7128d4f1530d7cf9d25f8073fa468fb496fcb2f19a,0xf8219564bca07dfd0536b2fa17c4f251cf8a96f94df308f73b,0xf0d71c4b69a835f3b21a46fd2568fac280f49df951fc7bf073,0xfc4a19d708352bfc730d21f8d496f517b6f3b46fa950fca82,0xfd946bc21a0738f369a825fb30d2f4b7caf7d4c1f6508f915,0xf21cb38a07d965f6371594f86b7c2fb2d4fca4f053f9a1fd80,0xfc705694b3821afc19a0d2fd7b259f8a4dfb64cf5371f6803,0xf730d9a4b682c1f91a8056f38d4cbf49536fc70afd7b2f215,0xf071c4638a952df4d7cb69f0a1568f128d9fa4b2cf350fb73,0xf94a8356bc170df964b215f7ca08df528630fd4c2f7b3fa91,0xfd2b69538a1c70f4d9a03bf194cb7f52ca46fd7368f51280,0xf70d4b3568ac21f9463051f9d7cb6f8259a0fb2d837fa4c1,0xf5694a80371cb2fac7b350f2c4d9a1fd07f46bf836f915f2d8,0xf4d7156b382ca9f52d0a19f8d96370fb4c7fbc12fa468f305,0xfc49d70a15683bf7b4d253f0364a95f196b2fca82f17cf8d0,0xf2c159a8364d7bfd807352facb49d0fb6503f17c4af21968,0xf6bc219a4d0738f4ca17d9f564b7c1f5963b2f8a0f2d8f305,0xf568073b2d94a1fb69521cf4b7d82cf0d4635f9ac71f8a03,0xf73b68250ac19df71a9530fc215694f4b2d8af08364dfc7b,0xfca9d217083564fa4bc730f3694d7bf591a8d0f286bf2c15,0xfa9152b4c738d0f307d465f2c1a49df7bca821f96805fb63,0xfd4a917c2b6538fd9503682f8a0fc1af521fb4cf70dfb73f946,0xf053712d94bca8fb28d0a46fb703f7c4df2c15f659f386f1a9,0xf2d91ca863507bfa17c28d0f37d4bfcb64f803f9a4f569f512,0xf3715082ca946bf2596307bfbc7d4fd912f8356fa1c4f0a8d,0xfcb49682d0371af56b708d9f150a9f8364afc4d7f3b25f1c2,0xfd82b637c1a059fac4d2519fbc217fb38a4f08653f649f70d,0xf8ac21964d07b3f1a037d95f86b250f365fc17f4a9f8d2fbc4,0xf03b46512d9ac7fbc250a17f8a4d73f6359fc491f82b6fd80,0xfa071cb46528d9f2d7ca86bf4d0519f21a4cf6953f380fb73,0xf8d4cb691a0352f56380d21f71c2b3f49a86f7d950f4ac7b,0xf7352b680d9a1cf3b7d4650f12ca07f38a496f4cbf915f82d,0xf07152bc4d9a83fb7350d86f594b36f821ca0f91a46fc2d7,0xf5946b38a1c7d0fcb2869d4fd21708f37b4a0f52ca91f635,0xf70d9a82b3651cf86b71950f2d4a035f12caf837df4cbf964,0xfb69a1738250d4f12b7d94cfd864ac2fcb307f08af519f536,0xf86b495037c21af8d7bc4a0f71ca9d0f53691fd2564f283b]

def a14_28 : List Nat := [0xf1cb4638a9d705f80a49652fd86b730fb35912fc2d4f17ca,0xfd9651ac2b3708f52d49a03f21cb4a8f7d0591fc46b7f386,0xfa917c4d82b350fd07bc159f38ac2d7fb6521a4f8630f649,0xf2837b69d0ac15f7059a12df94b2c71f308d465f68a4cb3,0xf569d4a1c2b370f64917d28f59ac7b63f0a83fd08fcb4f512,0xf6b3512d708a94f8d036952f68371a05f19d4cf4bcaf7b2c,0xf65037d94acb28fc4d08351f6952c7b4fa12d8f19a07fb63,0xf0d4acb2837195f9d251c46fa12c7b49f8d7036f6b35f8a0,0xf380a96b4c7d25f82c1950df64acb715fa12b368f4d9f037,0xf1a038d2b6594cf37150d96f91253b4afd4682c7f7bca80,0xf73594680a12bcf8d9156b3f0369ac4dfb4a82507f2c17d,0xfc70536b2d491af217d0a468f9a8dfc152f308fb37f659fcb4,0xfc4a15082d736bf7b49568a0f253bf17c2f0d83f9d46fc19a,0xfb469d0ac17382f56807d4c2fa12d8f94af519f350fbc7f3b6,0xf17c49d8a053b2fc2d036951f64d7bf6825fb4acf3708f19a,0xf38d96b251ac70f821c4d056fb7d2cf91735fb463fa94f80a,0xfd9503712b68a4f3b7d0a156fca964f7082cfb491cf8d253,0xfcb64a037d2591f15082b4caf70d83bf8a96f217cfd49f365,0xf0d73b46521ca8fd869a17b2f382cb6f0a4c7f9d4f503f951,0xf7d053bc4968a1f9a4638d21f56b4d9fb7082fc730af1c25,0xfa0719d8356b4cf2b7d4951cf052863f08a12df3bc7f64a9,0xf0368251c7b49af8ac2d9650fb38d4cf46b21af37195fd07,0xfd83b70ac49652f7c280d9a1f637d4a8f2bc1f519f305f4b6,0xf508a49d71cb36f1968d07c2fac4b730fd46b2f5382fa951,0xfa12d7cb469530f0d86b3715f25638acf1c4a9f07b28f49d,0xfa0863512b7d94fac1730569f8d07cb3f591a82fd2c4f6b4,0xfb4c28d0356917f0a864d215fb37d952f36bc708fa1cf9a4,0xf4d0537bc21a86fc7d25194af28d956bfc4b3071fa08369,0xfa03519d82cb64f1708a94d2f4c7d052bf37bfa1cf695f683,0xfd9153b7c280a4f71a94b2d0f5968ac12f5630fd837f64cb,0xfc25917d80a46bf0d21ac4b3f369a82b7f07c15f5683f49d,0xf30d4a952c7b68f9651ca07df8053b21af194637fd28f4cb,0xf7ca830d49652bfd864a1507f5912c4b3f6bc173fd9a082,0xfb359d0864a12cfb28a94c17f25196b4dfc7d830af56370,0xf153694d708ac2fb38d0a1c4f5682b730f19a46bc7f9d25,0xfb68a12594c703f64b283519fc2d73650afd9a4fcb71fd80,0xfa83715964c2d0f2803b7ca1f9d7052bc1f6b4d8f4a9f365,0xfc7b4a0d836912f4cb28659df53b649ac1f8a1730f052d7,0xf86371ca4b250dfc7b695382fbc4651a03f708a94df19d2,0xf1cb3705694d8afd7c2b6380f9d217b4caf64a03528f915]

def a14_29 : List Nat := [0xf21a083569d7bcfa94d052b68fb463f28df159f730fc71f4ca,0xf594d8a0736bc2f7d03b28651f2d91f5380fa469fb4c7fca1,0xfc4d21968a0537f5638d94ac2f3082bf7bc1f59a1f46bfd70,0xfa94c28d7b6350fbca19680d2f4a83bf9564df71cf521f037,0xf4ca9152b7d086fd8a071cb49f2c738fb6503f4d21af5963,0xfa4683059d712cfc15694d07bf36b4c7f52b3fa19f8d2f8a0,0xfa17b30d4c2569f95364bca8df0a4915fd7c12f86b2f8073,0xf21c73b64a9d05f4ca0863519f8a17b2f8d703fbc2d4f956,0xfbc2d951a46307fca94d86537f71250dfb4c196f382bf80a,0xf3b7d0564ca128fd86359a4b2f196bc25f08af94df71cf307,0xf8a12b496537d0fc28d4a917bf463051cf70acf9d25fb386,0xf8a12d7b305946f9a0d4cb651f3708d96fac2b4f8352f7c1,0xf9503bc4d71286f2d07b4ac15f46538d9f6b2c73fa08fa91,0xf46b308d9521acf3694a82d05fb70a91cf4d7c2bf386517,0xf59a82c7d46b30f4b7368d91afca08351f2bc4965fd2170,0xfb691a8370d2c4fd463082159fac7d8650fb253f1cb7f4a9,0xf95371c4a082b6fb7c2d8a194f63bca9d4f83056f0d7f521,0xf4952d7bca0386f28d9635071fc19a80d4f6b4a15f7c2b3,0xf7b3682c1a4950f69ac7d4b25f1738a0d2f519d803fb64c,0xf0386b2194ac7df5073b469d2f1c4d8a95fc280a17bf365,0xf382159acb4d07fc17d9680a4f256491a8df7b2cf350f36b,0xf9ac28d46b7305f563b2d70a1fa83521cb4f4917cfd9680,0xf8d071ac4956b3f80a91537b2f1cb463052fa869d4fd2c7,0xf5682d491ac7b3f52b638d9a0f8a4c217d0f4bc1596f307,0xfb2c468d719503f8a1cb4d073fac7b69d280f563f4a9f125,0xf8a156b2c49d03fbc12d70863f4d8250ac7bf73591f69a4,0xfac28650d73b49f38d2bc1a46f25307c4d91f517b69fa08,0xfa830d496bc251f9170864b2dfd7350ac128f659a4c7b3,0xfd8a4b69521c70fac4682d7150f830fb37f9a1f9d4f2bcf365,0xf63bc7128a0594fc2d968351a4f7d4bfca91f6b25f037fd80,0xfd70a195382bc4fd2ca8036b49f8650dfa964f7b3f1c7f125,0xf350a8d2c196b7f49512b3807cf9d71af64d03f4acbf5286,0xf128637b4950acfa8307d46519fc71a4f2cb35f2d96bfd08,0xf6b4a07351c2d8f8ac4630d712f052b38f7cbf956f9d4f91a,0xf7c4a156b3082df8370ac21946f2b4d05f9536f71cbf8a9d,0xfb730d9a152864fb3694a07d2cf56b219fa8d4cf8053fc71,0xfb65370a19d4c2f0d7159a4b38fd8ac12f630528f946f7cb,0xfd9ac1528364b7f3712d08a495fc2b307fa05691f8d4cb6,0xf52c17b4d869a0fd7ca153b280f94a8365f219df4cb6f307,0xf35071ca968d4bf80a4956b7d2f19d038af37c46f125fcb2]

def a14_30 : List Nat := [0xf2517d4b3680acf64a82bc70d9f2d83591f56b730fc1a94,0xf0d7ca86b49153f7bc1a469d83f082b365f2170a95f2d4c,0xf73b68250d49a1f2d8a46351cbf9d7b4c21fa07cf038f659,0xf6bc217059a4d8fca1563b49d7fa0d2b738f25308f691c4,0xf082517d4acb63f1a0537b2c49f3b4659a8f7c12d0f8d96,0xfb6350a8217d94f38659a1c2d0f69152bc4f708d4acfb37,0xf1c7359680a4d2f71a9d82503bf365194ca8fb64fc2bf07d,0xfa056b4c7d9128f70d469a1cb3f2ca49517bf52d83f3680,0xf9d86b2c15370afb7ca12830d4fa80563bc4f52d719f649,0xf51c280d9a4b36f86b21ac7053fa8d491730f7bc46952d,0xfb4d7c21a95386f7b3082d9651f507364acb2fc194fa8d0,0xf3708d215694cbfb638a0d91c7f2864d71a95fca4b2f503,0xfb7086352d4a1cf59a03b64c71f9d738ac2b4fd8219650,0xfa0382b7c15649fac4d0521968f2cb4a17359df8d70f3b6,0xf152c7d03b468af0ac19d28365fd4a96b21708fc49537b,0xf1730d94682bcaf8369a4b7052df56b3fc7d4f80af12cf591,0xfc71a95386b4d2fa8d91cb25630f15082f7b3f0d7f496f4ca,0xf69a837d4b2c15f217ca49d8635f0a195fb703fbc46f2d08,0xfa83b649507d21f5308d9a4b2c1f73691f0ac4df5682f7cb,0xfd2bc15694a037f0d4c7b368a95f1708d9f3825f12caf64b,0xf4a0386bc7d259f73b2c469d051f8d4b70f9a821fac1f563,0xf4912d0537ca86f8307d9a1c4b2f517b69f2cb365fa4d80,0xf964d7bc21a805f071538d2b4caf91c730df6825f49af63b,0xf825194cb37d0afd21ac70356b4f68059a4f38d96fb2c17,0xf08d2c19637b4af9a82bc70564dfd712530fa1594cf3b68,0xfd71a83052cb69fb215368d07c4fa94d280f6591ca4f7b3,0xf503b71c4d2869f4b6537ca80d9fa07d8364f19af2bcf152,0xf4a80d2596b71cf5307d91ac286f2150a94bfd8364f3bc7,0xf7b659d4c12803f0d836917cb25f3b468a15f0ac2d7fa49,0xfbca8250371964fb356807d94c2fd836b7c12fa0d4fa159,0xf12ca94d056b37fa463591c7b28f69d251a08f38d70fbc4,0xfc1a9468d73052f2196b7c4a80df63bca0715f8359d4b2,0xf4a08d2c19537bf507cb38a9d46fac49630d71fb682f152,0xf4a83bc7052196fc286b49d7351f3659ac4d80fa0d2b71,0xfb64d703591ac2f94bc71250a86f9a4c156380df2d8fb37,0xf9a830564b7d21f52b68071c4d9f63bc28d0a49f351ac7,0xfac219463507d8f8651a0d2bc73f3b71c4d95280f4b69a,0xf3708a4d91c256f9683b217d0ac4f59a1f6b4f28df7bcf305,0xf36bc12d4a9507fca17d94680352f9651fb4c7f8d0af3b28,0xf59a82c1730d46f5194acb2d7083fa1250f68d9f7c4bfb36]

def a14_31 : List Nat := [0xf50a912b7c4d83f251730d9468acf4a1cbf807d2f63bf965,0xfa1569d082c7b4fa053864d712bcfd259a8fc491f307f36b,0xfbc1705694d283f35912b68ac7d0fa152c4f7b463fd9a08,0xfd219ac70536b4f51c2b37d08649fd82569fc4a17bf30a8,0xfc28370d4b651afc4a863b259d71f0a912d8f7bcf530f649,0xfb4c1730569d82f1a4d0836bc259f53b7d21f8a946fc70a,0xf28a95364c170df650a194b2c738f96b308dfacb7d4f215,0xf4bc12d7368059f8d03b71a964c2f538a4d91f56b2fc70a,0xf5071a86bc49d2fb21ca965380d7f364d82c7f3b4a0f195,0xf37cb64a1952d8f4b3568ac2170df9a082b7df4c150369,0xfc2b70538a19d4fd0acb49568217fc152d8037f4a96f63b,0xfd803719652ca4fd21c7053b68a9f7d0a1594bf2bc4638,0xf5370d94c21a86f5036b4ac17d82fa083b2d469fbc7f591,0xf5630d9a4b7c21fb64ca08259173f694d2bc1a8fd83507,0xf2d71a94b36805f9564c2b738a0df5307ca4d821fcb691,0xf807cb64a159d2f53b4d71968ac2fd0a94c12b738f5036,0xf53b4d7c2869a1fcb6491250738afa03659d2b71c4fd80,0xfc2b386950d71a4fc19af8a0f521f635f730fd28f4d9fb64fb7c,0xf307c2b649d8a15f0825fac19fd712f4d0af956f4bcf3b7f836,0xfd9a80564cb3712f0ac7f251cf94a1f6359f86b2fd7b4fd038,0xfd9568a0371c2b4f4a196f4ca9f8350fb7cf0d7f28df512f36b,0xf9a0863b7c152d4f8a4b2f12caf46bcf7d91f30d8f7350f569,0xf21ac4b69d70835f650d4f8630af94af2d8fcb2f71cf73bf951,0xf80a9152bc7364df2170df94b7df86b3fa4c1fa82cf350f596,0xf150d94ca82b637f7cb4df8d253fa4680f03b7f91af596fc21,0xf08a4c12b3569d7f86bc2f37ca0f4d836f7194bf2d05fa951,0xf308d9a4b7c2156f91ac4f68259fd2b64f173bcf0538af07d,0xf256837b4ca0d91f807d4afa951f469fb36fc2bf530f8d2f7c1,0xf038d4a12c7b695f94cb2dfac19f63b4f5371f8256f7d0f8a0,0xf4c715380a9d2b6fcb4a82f4d869f5912f3650f70dfca1fb73,0xfd2b38a071c4659f4d7369f4b7caf682cbfa91f503f251fd80,0xfd07351946b2ca8f4b369af05683f21a08f7bc1fd259f7d4c,0xf912cb705368a4df51a082f3b2d8f6594bfac469f7d03f71c,0xf0a94d8637bc125fd2b359fc28a17f9651f4b6f803f70df4ca,0xf6350acb49d7128f8a952df46b30df3708fb2c7f9156f4a1c,0xfbc4d28a0735196f950864f7d9a4bf2b365fd830fa17cfc12,0xfca9d08652173b4f49530af638a19fd7b64f7c150f28df2cb,0xfbc71952d038a46f80569df215368fa94d70fc4b2fb37fa1c,0xf4bc2537d80a196f17b305fc49d21fd4ac70f8659af36b28,0xf0564c19a82b37df07b638f1a4bc7f352ca0f1594d2f69d8]

def a14_32 : List Nat := [0xfb371ac4d965082fd2530a8f49af7d0f683f195fc21fb7cfb46,0xf5637bc49a12d80f69d7038f52b3fa82cf4d0afb46f159fc71,0xf71c46b359d28a0f508d496fb7ca4f7d03f386f125fa91fc2b,0xf1280ac7b3564d9f36bc170fa8694f2c4bfd052f9a15f8d73,0xf25968a03b4d71cfb637082f0538dfa4651f12d9fa94cfcb7,0xf4bc12d8370569afb2864d7fc491af530d9f7c251f08afb36,0xf28a0d4965371cbf9507c2df7d864bf3b6f083f152fa4cfa91,0xf03bc7d4a869125f51c2b46f382d95f37b6fac49f170af0d8,0xf1c738a964b2d05f917d825fb680acf4a12cf7b30fd94f536,0xfac12d86b370594f1964bc7fb7d4c2f08a9df52836fa1530,0xf2d8ac46915037bfc71253bfb4a956f1a082cfd70fd49f368,0xf8a159d2b64c730fd0ac217f94d836fc19a4bf07b35f2865,0xfb694ca17d28053fd4bc219f638a95f8d0a46f7c152bf370,0xfb21ca94d705683fc4a1952f69d8a03f3517f0d28fb7cf6b4,0xfd7cb3051964a82fa956b2cf370a125fc4b71f8d0f94df863,0xf12bc70d835964af52d9a80f630ac28f17b65f7d4b3f491c,0xf64d9a80512c73bfb2d0ac4f3568d70f259638f71cbf194a,0xf2c1a836b49507df3b719a0fcb21537f569d82f680d4fca4,0xfb38d0a17c46952f12cb735f07d4b63f9d28ac1f6508fa94,0xfca94d21507386bf4c2b30af65917b4fd7c1a80f28d9635,0xf53b69d4ca80712f7c150a4bf730df4659fc2bf8d2f9a1f368,0xfa4637d2bc19508f6b4d0a15f3528f69d8fc712fb703fa94c,0xf3507c19d4a82b6fca9568d2fa17d0f469fbc4f038f125f37b,0xf6b71c250a49d83f91acb465f12b35fd082f4d7cf69a8f703,0xf49d71acb250386fa8d4b659f15369fc70a4f280df7b3f2c1,0xfd07cb21a495638f37d4b680f528a0fc2d9af1c469f7153b,0xf1ca964d28053b7f8d94a156f36b2c7f30a8f1259f7d0f4cb,0xfd7c2b683051a94f08a4659df125369fca071fb4cf37bf8d2,0xfb2d835964a071cf7b6821acf52c491f37d4bf8a9d0f0365,0xf3591c28a4d07b6f38d9a150f9652b4fca0864fd712f7cb3,0xf64a8d705912cb3fd9651ca0f4d286bf1a94c7f7b253f038,0xf6b7380d2591ca4f17c2b30af1507d82fa869fd94fcb4f356,0xfa9173052cb68d4f7d08a12bf9d283b4f1c465fc70af3596,0xf917c2503b64a8df694cb738f2b4d708f1a0d2fa951cf536,0xfb352c1a8649d07f05196b28fa4d837cf659a03f217dfbc4,0xf28d496bca17305f219a4b7df9d07c15fb2c4683f563f80a,0xfc7350d8a1946b2fca0863b4f569a4d2f51cb7d9f128307,0xfa82517c4d96b30f73864950fb7d21ca4f80dfbc2f19af356,0xf8036bc71259a4df4c1a0d2bf683b7d94f1569f7350f82ca,0xf8217cb4d9a0563f691a4c2bfca864951f52d73fb703f80d]

def a14_33 : List Nat := [0xf950a4c7d863b21f8a1c2530f96517bcaf382d07f4b6f94d,0xfc7350a912d86b4facb25694f9d082c15f6307d4f1a83b7,0xf7ca49638d0512bf037d91a8fc170a952f82d4cb6f653b4,0xf21c7b4a038d965fd28a9537f6b2c4d08fbca19463f0715,0xf836591a07cb4d2f7d9a86b21fc251f4caf3b7f649f0d8f503,0xf082d4ca917b653f594a837c2f0a15fcb21f64b3fd968f0d7,0xfa946517cb2d038f9d86b4ca1fa07d4f3596f8052f2c1fb73,0xfd2cb71a0835694f1c70d9a82f3052bf368d7f591f4cafb64,0xf652b307c4d91a8fc17b4a082f2150df96bcaf64953f38d7,0xf537d08649a1cb2f50a8d4b71f382c70fd912f63bfa4cf659,0xfc17b46382d059af3512c4d70f0a49d8f8691afb256fb37c,0xf7053682bc19a4df4951a03b6f712c4bf2d965fca837f80d,0xf9d0537b64c28a1f1563b4a07f968d25fc7d49afc12bf830,0xfa17c259d4b6380f568a912b3fc150d7bf703fd28f4acf469,0xf950364cb7d28a1f38d4ac12bf7c25680f7153f9a0df6b49,0xf38d07b21c4a965fca173b682f1503649fb4d7cf2d95fa08,0xf08d49653b2ca17f3059a46b7f8a0d912f7d251cf836f4cb,0xf7ca86b30594d21f96537d80af19d07bcf4a152bf8364c2,0xfd215370a86bc49f03b7ca965f2b4a195f7d082c1f4d836,0xf70acb65194d283fa863052c1f9d712b35fa469fc4b7f80d,0xfa194c2d8653b70f59a8217d0fd9637ca4fbc152f380f64b,0xfd71a82cb649530f512b4a086f7b38d250fc7369afd91c4,0xf38a0d491c256b7f28d7cb4a1f3b2d9680fca95364f5071,0xf2530a8d964b7c1f70863bc2dfca1950d4f7382b651fa94,0xf50d73bc4968a12f71ca4b630f9d465380af7c2bf2d8f915,0xf0591c2d8637b4afd9a83b217f564d07ca1f28035f96bc4,0xf2c7d08356b49a1fa073b2d4cf950364a8df869152fb71c,0xf3bc71964a82d05f80a12c4b6fd9ac15638f7d4952bf370,0xf5037b468d2ca19f65382bc4a9f9d4f07df0a8f17cf3b6f152,0xf056b7d2194ca83f86370a4bc2f53b2f9a15fd964f17cfd80,0xf21ca8035694d7bf1a46b37059f2c715fd0a9fc4bf836fd28,0xf7c152d0a94b683fbca8d71953f2b708f4c21af5630f9d46,0xfd8052b4ac17369fb7c4d21a86f15649fa0359f83bc2f07d,0xf73b65280d91a4cf70a9512d4bf1ca8d7fc2bf350f694f368,0xf96530d4c17b28af8d70512cb6fc7380af64b3f194af952d,0xf082cb46537d91af7b6830d21cf5963b2f4ca8df1705f94a,0xf2d0a94bc715368fc2196508d4fa83b64f9d7b25f073fc1a,0xf6352d9a8071c4bf3b7d8651a0fcb2837f94ac21fd46950,0xfd2bc491a805637fac125968d0fc283517f7b30f4d9af6b4,0xfacb652d4917308fa05963b7c4f51a9d83f4b286f1c2f7d0]

def a14_34 : List Nat := [0xfb4c71a956308d2f694d73bca8fc19d052f7b64a0f38215,0xfd864cb21a95307f0a4d96b715f1c73b49f25638acf0d28,0xf4691c7b352d80af150d738ac2f9563071af6b28f4d9fcb4,0xf0519637d82b4cafc17b68a952f380d9465f4d21afb307c,0xf6837d0ac2b4915fa170536bc4f7b30821cf2d8a95fd964,0xfb2830d7c4a9156f071ca8d495f80a12536fcb469d2fb37,0xf508acb4d736912fb2c4659d03fb70a15386f2d8fa49f17c,0xf7ca9152b4d8630fc28a495371f83b7d9650f12d0af4cb6,0xfd4a96503b71c28f9d2b4c7351f12594638afbca086f0d7,0xf0d9564b37ca128f0a9638d715fc2b68a491f70352d4cb,0xfa07bc4d2835691f7305946b21f680d7ca4b3f2c15fd9a8,0xf70d9564a821cb3fa94c2b6350f1968d4b7caf7d251f803,0xf64d2ca83b70519f30a4bc7d86fa1735280d9f6594c12b,0xf6371c2b4a08d95fac7b382d491f64cbf9a86f350f125f7d0,0xfca17b350d49682fbc4a95638d2fd7c19f152f073f80af64b,0xf508d2c46b371a9f3691528ac70f7b49df4a0df8356f1cb2,0xfd94cb653708a12fb28369150d7fca952f03b4af4d86f71c,0xf7b36591a082d4cfbca4968d712f038a9dfc251f3705fb46,0xfb4ca80537d2196f07b38259a4df51a036f8d946fc2bfc71,0xf0a1c46b28359d7f9652d803b4af368ac7f0d4915f2cb71,0xf4cb2d8a0371569f9ac28053b7df0d4a1c7f1259f64bf386,0xf1c2596b7380d4af4c712d9a03bf5368d70fbca82f94651,0xf49517ca80d2b36fd91c25307b4f128650af69a4cbf37d8,0xf7364bc2519a8d0f95386b21a4dfca05694f82d7b30f17c,0xfcb682d703594a1f7c2b4638d91fc4d0569af215f7b3fa80,0xfa46bc17d952830f21a8073694df9153b4caf50d86fb2c7,0xf1c4a053682b7d9f651acb30d49fc708a952f21738df6b4,0xf1703b468d2ca95f8a0d912b653f3694a1cb7f4c7df0825,0xfd7c251a083b694f1ca46530d82f2b7368a9df19507fc4b,0xf368a9d2b4c7150f91ac2538d46f594a0d7b6f3bc12807,0xfa94638d07152bcf30596821c7bfa4b6537d91f4d2cf08a,0xf2bc469d70a1538fc719a4b3652f495037b68df1ca80d2,0xfd7083b21564ca9f7cb4d0a1963f71c2594a86bf035fd28,0xfb4a95368d07c12f837d25694caf2cb64d91508fa03b71,0xfc19a056382b7d4f359d2c71a86bfacb4f694f251f037f8d0,0xfa9536b7d4c1280f071564b2ca83f73bcfd968f491afd250,0xf86591a4cb2d073f94d8a03517b6f9ac7dfb364f8250fc21,0xfd7152c4b30a869f59a12d46bc70f37b28f4ac19f80df365,0xf1c4650a9d7b382f71952d4a8630f1ac735fb694fd08fc2b,0xf6bc4a9512d7083f2c71a03b49d8f68ac19f7352bf0564d]

def a14_35 : List Nat := [0xf69a80351c7d2b4f5286b70ac4d9f73bc21f650d83f491a,0xf52c1a9d4683b70f17d03694acb2f537c4b6f8a0f951f82d,0xfa08d7b6352c491fc705683b4d21f37159d0f8acb2fa469,0xf1c2d7b4a038695fd8a91256bc70f64ca173f3b2805fd49,0xf49517c2d0a836bf2b73568d4ca1f03bc19d7f0825f9a46,0xfc7d4a91563082bfd253b71ac469fa86b4950f70d83fc21,0xf3807d9a46521cbfd0591ac286b4f37b2d8a0f63517c49,0xf5217cb64d830a9fa4c2b7d05368fd28073b49f6915f1ca,0xfac2837d05196b4f8d4953b7c1a0f4cb217036fa9d2568,0xfb659a1c28037d4fa469170d2b38fca05368d94f7cbf251,0xfd07c1a4952b638f28a9d71503bcfb4d2196537fc4680a,0xf37d0864b2ca915f6bc71a038d95f94c12507b36fd28a4,0xf17364bca9d8052f4a03b286951cf56b70d491a83f2d7c,0xfac4691503b7d28f259d4b68370a1f4a9f08dfcb2f356f71c,0xf4a9125370d86bcfd2ca8036594b7f051af82b3f469df1c7,0xf538a07d21cb469f4c2b730d8651afac719f2508fb36f4d9,0xfca49d0386b7152f082bc195364d7fa0569f4b37cf8a12d,0xf538a1946bc70d2f503682b4a9d71f4d80acfc12fb37f659,0xf950a1c28d7b364fd0837cb2569a4f4ca86bf17035f912d,0xf50a964b738d2c1f9d4cb6308a125f7194acf2b3568f07d,0xf64d2507b38ac19f6bc7128d0a495f1a9d735f8630fb4c2,0xf9465380d7b21caf369d25071a4cbfa82c730f4b68df195,0xf0d49651a82bc73f86b7d2c19a053f8071259df4b36fac4,0xfbc4a968d215073fac7d95364b280f94d038a1f52c17b6,0xf0596b28d4ac173f9d2c7b46380a1fcb3568a94f7d0f512,0xfca94b280d73651fd8352cb70a469f503b68a19fd217c4,0xfb2d70836519ac4f52c1a4d037b69fcb350a8217f8d946,0xfcb7038652d49a1f7d80ac21964b3f8a4c71536b2f9d05,0xf53649d80ac7b21fa950386b4d2c1f4a82569173bcfd70,0xf4cb2d80736951afc2194d7b30568afd9a0f3528f1c7fb64,0xfa053682d94cb71fa9152b64d8037cfa83b4f12cf659fd07,0xfb37d0a865194c2f4a9507c12d836bf71acbf53082fd469,0xf1ac7b2805364d9fa4cb30712d8659f837d0af4b69f52c1,0xf69a4d821cb7053f4b2591ac7d0386f7156b3f49d2cfa08,0xf864c152b370d9af0acb7128d49635f591a4b6fc7d2f380,0xf1530d8a964b7c2f1ac4d7082b3659fa49d250f7386bc1,0xf8251c73b4d0a96fc46b7d2195038af71a49d80f2bcf365,0xf1ca8037d256b49f286350a9d4cb71fc2b38d07fa15964,0xf64c2d951a07b38f173569a4d082bcf036b49125fc7d8a,0xf5912bca0864d73f5170d83b69a4c2f28a1c7b49df3650]

def a14_36 : List Nat := [0xf2837d49a056bc1f530d8a1964b7c2f5170863b2d9f4ca,0xf864d703519acb2f652c1a49d0837bf5963b4c712d8a0]

def a14 := a14_0 ++ a14_1 ++ a14_2 ++ a14_3 ++ a14_4 ++ a14_5 ++ a14_6 ++ a14_7 ++ a14_8 ++ a14_9 ++ a14_10 ++ a14_11 ++ a14_12 ++ a14_13 ++ a14_14 ++ a14_15 ++ a14_16 ++ a14_17 ++ a14_18 ++ a14_19 ++ a14_20 ++ a14_21 ++ a14_22 ++ a14_23 ++ a14_24 ++ a14_25 ++ a14_26 ++ a14_27 ++ a14_28 ++ a14_29 ++ a14_30 ++ a14_31 ++ a14_32 ++ a14_33 ++ a14_34 ++ a14_35 ++ a14_36

def b14Mask : Nat := 0x18d4000369000646000ec0011a00b200680070000f0410

def e14Mask : Nat := 0x1ffe000fff0007fe003ff001fe00ff007e03f01e0f0630

def e14_0 : List Nat := [0xf618af9d1af3491f2741fc371fb851f60a3f564af2c7afd6cafb026f8296fdb42f5cb2f80c4f07d4f978cf53b7f30d8f9b50f3d59,0xfc9a50f37a0f9570fd620f8c60f3ca6f2d3af49daf158af865dfcb35fb725f4796f12b6f71bdf84c7f819bf3928f4d13fc142f4b0,0xf17095fd2475f86c25f3bc05f4027cf9731cfd62b7fa4b87f91d82fa6412fd0a84f1a308f9ad34f960bdf1639bf5b6fac5f38c,0xf63c0bfa2d30fd8560f4c780f95d70fa62c5f37125f19275f46182fa34b7f9ca47f9ad13f849b3f1c6d4fbc8a1f69db8f205b,0xfda1bc8f496b8f3c168f06418fd09c6f25ca6f34b56f2704cf7420cfd93a4f5130afbd350fb2173f9b7d1f9a2d5fa758f9287,0xf5c8d29fd6c19f05bc9f78269f413a9f36b2cfa157cf0da4cf5a03df481bdf7a61df70421f8652af8b735f4b083f06472f93b,0xf94cb2a7f84a17f2d74f13b4f6a34f09d4fb627f5d37fc607f0863f50d6f1596fb0adfc920f8c1df819af25b1f38b9fc582f53ca,0xf0b9c4156fd637f85b6f1bc6f2946fad96f0759f3179fac19f24a1f80d1fd8a5f250af30c5f2840f7c3af278cfb4d2f3b74fdb83,0xfd172a564f8b9a4f4b0cf3a04f7c94f2c14f73caf528cf158afd96afb195f6d21f3081f07b2fd53bf0975f3629f8d06f3d78f6bc,0xf4d903b82f8a265f1275af9bc25f9c5b2f13605f3c7d5fad8c0f49380f471d3f6c4bdf6841bfac164f7a918f6a379f0d2f70b,0xfc125da07f9416d7f47186f3d287fa9027fbd857f4b91df0b69dfc8429f34a59fc2604fa31b2f536a1fcb38af0c5b8f03c65,0xf271a3c06fcb39d12f46920f5742fb4a2f8bd2fca94f8c14fd634f786cf519cfa816f50b6f35b1f709bf7d59f80a5f3da7f30d8,0xf265084daf31bd290afa9bcf875af634af791af5149f37d9fc469fb074f2c04fb617f21c7f86d1fc306f28d0f58b2f5b3dfc538,0xf8da20417f0c3156a7f16972f57d2f4637fc426f09d6fb586f91c2fb182fa4d1f39bdf530df9a34f5ac9f8b0afc805fb384fbc7,0xf9180537dfb613485df4128df20b1dfa470dfc7951fa2b71f56a87f240a7f629b8fc4b52fc903bfc83a5f960c3f9ac64f36d,0xf65b24c0df92ac830bf85972dbf126cbfd4b3fa09df5c7df168df706bfa496f3746f8a57f13a7f1c9af1439f0284f0518fc352,0xf70483d61f5d08b791fd74b3a68f81acf46c1f39d1f26b1f2c4dfa5bdf27cbf0a9bf28a4f5378f52a7f9c34f0563f9602f90c5,0xf02adb174f3865d0a4fc3b291d4f4b728f9614fc512f59d2f7a6df378df0cb6f31c6f8ca1f907cf5397fb8a9f05a3f085bf624,0xfcb2d9638fa143db09f84d15a3bf85930f705c9f4a7b9f16a29f57c13fc6273f6821bf7da81f40d87fc420af560c2f5d64b,0xf5042c781f27a9db41f6ad358bcf5a48c92f3c571f8a16f94c1fd2b1f03acf062af0d82f3908f79b0f6b59f64d5f736dfb743,0xf96081b42f86b52714fdb831564f7c8a5034fa904f5c49fd285fd378f7935fc9b3f16d9fa263fa1c6fd021fb0c2fa7bcf70ad,0xf6a04835df25147da8f24b7ca39fbc271d46f8d950fc368fb918fc9a5fb065fc096f4379f1b26fa1c4f207af3bd0fd213f785,0xf580c1937f42c6d071f403d2b87f9bda0527f26bc7a1fac815f495cf369cf3861fb7d1f60b5f4a3bfd435f8a64f9a20f9d82,0xf7c3859adf0b2c43d5f78bc6915f630c8a25fdb160429f5b93fc1a5f97acf4d09fb6a3f470af714bf2137f86d1f208df2648,0xf5138b702f7c6d0821fd860b5a7f975843b6f4c590a87f642b1fc372f9ad2f3056f4ac0fd935f19c8f1d3af4bc1f94dbfa62,0xf9b61d380f7963a2d8f71530d9af4b73c956f4913b2c7fa50268cfcb840f2758f14a8f1c6afdb0af7d60f4c5df2934f25b1,0xf2d5071b4fc490d152f6834a912fa87953b2f7b60c582fb9c65748f0392f8140fadb0fc7d8fca5bf3a1cf6d31fa637fd469,0xf02ad8b17f80c295a1f58a04261f5cb03782f53c7a90dfb349d657f368c1f4791fbd72f3d48f6b50f96a3fc4b9f46caf2d1,0xfa125c4b6f43c8b726f859d7ac6fa5093d42f81b073a4f35178ad0f9402d56f19a06fd63bfcb29f082cf75b9f147cf38d1,0xf4127865cfb940251cf0713d48cf82a0695dfb26397adf81a34b75f37461b08f9d6cfa53cf7d2cf091dfa429f3b50f6b8a,0xf519c38a0f8d5c6b30fd784a160fa963571cf31da2647fb8659d21fb43925a7f42790f7c20f418cf3d6af5b28f49bdfb0c,0xf74d065a2f0814c352fb790a482fc507a862fc9630b17f49a3b6c0f34bca619fb95731df29da1f642df8b5df387dfc158,0xf4351d0bcf7a0283b1f946a85c1f52693d40f56c2d87bf3a57248cf4a95d637fc9b612af413092bf80c7da1fd97068b,0xfc5bd6379f02a7581bf52bc8439f62803da9f14b8d053f642d1ca8f165a40c2f06c4d51af9b71f4927f09d7f83c7fa6b3,0xf85ad312bf0783a25bf90d715cbf94c80375f0ca41935fa69742c1fa06843c7f9a82046cf7261bf3b6f4dbf9d2f81df65d,0xf30b9172cf702d13bcf638a1b50f6d592841f5a74b681f3587db24f79d3a265f8b7396adf9a08cf04acf521cfd490f64c,0xf0d2b4386fbda95036fc2a8b5d6f7b3d4825f9c47a08df79024a1dfc049273afc8139b07f564178f215a6f961fc35fbc1,0xfb53840d1f79d2a18bf946a8c3bf617c09adf314a057df3621c47af96802c51f4306c952f6b4d85f07392bfacbd5f287,0xf40c71a86f39c56081f53a0b8c1f42d95a61f4b637a28f20743bc6fc294ad03fac4d72b9f78d6905fdb521fb791fd385,0xf529bc730f8a1749c3fd841c093f619a72b3f60d28b5cf64b1875af21569db0f5d426b79fd704a31f580ac43fd68c2a]

def e14_1 : List Nat := [0xf478350bcf612c793bf608c1943f5a18b46cfa962d840fd9b17520f5db27a41f24d6a859fd7b5682afac3f073fd13f90c,0xf9a461785fd5741bcaf2b7d963af024c3b97f2db68137fc560b821f290d48c6f52c9304bf508d3491f5a83f0c7af6d1a,0xf136025bdf07261a3df9712c65df91ca2b46f415c0b92f809c73b1f8a5034cbf478359a0f8c394a75f6b7d8f84d2fa6d,0xf47db0863f40a8b39df24695cadf792c1a4bf126a7c49f87530614f507281b6f3c9a2517fb20c83a5f09bc6df5d8f13d,0xf61c7d58af37564ad8f92c3b406f21d087b6f2039bd48f2519c43df59ac0713fb2497a5cf2a05b147fa18c63fd90b86,0xf2b687dacfb970362df8b375c9df617c4a0df41528cb7fa6908127f1384206cfa340b592f19a8564bfd1a50c3f4935d,0xf87534b1cf2d1a7cb8f0b259618fa46c3d58f42ca30d8f90417d63f7b9da213f5079c4dbf0a62915cf5602749afb683,0xf935cb7a82f4372f57c2fd5b2f0462f1947f8597f03d7f6815f09a5fd069fc3b9fbd80fc4a0f6cadf148cf1b4df36b8f6a31f1a2,0xf5d6941b80fa0271fd03a7fc4607f51d37f8c047f916b7f92cb0f8a6c1f35a21f5b4acf34d9cf86524f9b285f38da9f362db,0xf64185b730f35048cf1db65f2d9c5f968d5f70a6df3bc0dfa8b4df9280bf1ac2bf31978f9a420f3a749f126c7f1c436fa275,0xf5bd0684c2fc7ad926f7165fa2b6f97d6f3b46f3cb7f4127f0287f43d2f91d4f05a4f8c5df1a0cf93acf809afb830f1853f1b95,0xf9c083d61bf7862b4c5fd0b7f91c7f4a27f3607f8b6af9ac6f5946f2409f35d9f1d84f3bd4f20adf5a30f58cbf12c3f5182fa17,0xf94b2c60d1f21a63504f9c80346f8416fb026fda56f92a0f71c0f73a4fd3c4f7bcaf597cf8d9afb139f85b3f87dbf2518f5d27,0xf379a1b4d0fc59b720af53bd2a86fc807fb6c0f6490f5840f924cf3619f25a6f3da4f1574f317af81d7f8b5df2c38f12bcfd69,0xfd358b6074fa037c418f2bc179a6f2516940f6d24fb7a4f8634fc056f5c27fd087f91b0fad8cf3928fa312fd5a1f9db5f3c9b,0xf9bd752481f74126b03f0cb1da46f872b40d6f9d3af5693f1a63fb5c3f8c43f7a51f807bf95d4f2a8df92c7fa09cf2058f1c6,0xfb4a21570dfb5d3a840f8206b14df80cb9246f52d97a0f69adf165afc26af7c1df38c6f3490f78b2fc374f13b7f5918f5c93,0xf5cb6a7d80f1a437268fc97153a8f0ac12957fb4613da5f8402f3658f42c7f3b0cf6d4cf9b14f9306fd091f25dbfd2a9fb78,0xfc58d91b36f3a097d61f071d52b6f30c495adf39b87215f8a14756f296af4d26fb50dfc7a9fc281f3cb7f4083f48cafb420,0xf4b6190372f14a07b92fa956c802fd8b15360f34871d2bf7a183c25f5c40fda5bf3ac1f6a82f6d58f94d3f7964f9c7dfcb0,0xf534026c91fad5c2b60f37d69a50f3bc8a416f495b87a6f7ca31d85f86521b0fbd09f71c0f427bf82a1f3c48fd392f79d4,0xf38b572c40fdb08c917fa0d29437f590c68a2f58d3a460f31ad569bf481b702f16b4782fc79362bf15ca6d4f1d9a53c,0xf9d8b71204fc0724368fc6d75814fb92835d4fa16b5978fca50db37f26ad39c5f6480f1965fa309fcb13f2d1cfb2a0fa74,0xfcb39a6217f52b1c6d7fca035bd2fc8496150f3da4c9b6f831a5d4bf8d195c3af340d927f2a70f8147fb097f8642f8560,0xfdb5847260f3c9da714f5d296ac1f75a8bc09fb42c83a9f256b780afd82b37c4f20394a1f86d3591fb05c631f61d704,0xf3a2db8c40f7584a920f741c26daf73591b28f364b7218f5c9b3d42f9615bc34f65d9317cf86a0fd790f5ac0f1d8afb60,0xf261d8b590f5840c9d2f4d0a39b2f605a8749f6ac5db18f756b4130f3d64c715fa436cb7dfa1973c2f8c12f7a92fb380,0xf93d1a4852f64d218bcfac803742f4bd65a0cf35d96a7cf70619a82f349b57dafb38d0417f7863159f09c1b2f50b62c,0xfa5b30c917fbc6d9257f846902c7fd428ca93fa1d2b053f4b8a651cfbd860a41fb940da26f0836127f43185d7f973c5,0xfdb0a73918f4d1cb258f0534c978f1b7290c3f46570d3bfad5b9603f142a59d6f49ac7120f47d2c51afc836fa6b8f826,0xf8603c5174f82796d4bfa26b31d7f6520ad34f19504a36fc14938a6f8cbd09a1fca5d29b0f12c9d85bfc7b24f087f537,0xf2a8b073c5fd029bc15f40a3869cf61da5780f346a7db5f6d312485f491b728df6c814a93fac26b471f3b2d90f97c05,0xf912a78d4bfc0248317f90826b14fdac36592f5b8a0d1cf69703a18f9a6053bcf4a5d37b0f6157d934f58c6db2fc472,0xf03a87cb29f4d362ac9fd2c48b39f164720b9f6d7140a9f31a50db7f0c8256a7fd538124afb1586c34fb608d1c5f795,0xf583a2491df4c2b97516fd31c69f906d2f73b0df481adfb568df36259fa87c9fa41b6f7b821f035c8f027a5fca04bfc3470,0xf38d5ac126fbc90da356f084d392a6f73b2c8159f7a0c5b82df47c6852fd134b96fa870bd9f04a1b72f7503c41f9164,0xf3b69752c1f802d5617bfda826c40bf4d63c0592f3468d0ac7fd391584a7f1bc94f4709bf2a5bf1872fa306f538cf1d9a,0xfbc5d12a40f950c472b1f6079d43c1f62d039ca5fc7db46928f9b73a6c24f3b68571f3d8a025f9ad6380f487a1f8b51,0xf48b795316fd8527143bfc94b120d5fa9b0624c7f6ad1938cbfa403d96c1fd65ac074f182b5f3c2d7f8057fa092f8a36,0xf7951860bcfa52b74809f4d7a169c0f3db1246c5f413ca2d8bf91d6283a4f4305b92cf3b658c17fa8720fa639dfd570]

def e14_2 : List Nat := [0xfa035db721f9d3a871cbf6c931428bfd846a57c2f5081d4362f04c56837df706158ca4f902b1f3c0bf495bf7a29f6da9,0xf359a46db0f7d4b56390f8c7912ad5f1a3b86925f73182ca6bf83c1d247af16c9d3487f62bc0fa5720f5c40f149bf8d0,0xf296a81705fca1358b62f4c3095d12f940dbc87afc61483d97f9b1c56d43fc0864b519f8d73602fda572f47b3af0b2a,0xf842a60d9cf15038a74cfb39725d68f1340b2958fd37b41a02fa3571b964f7da5b6190fbd1280cf78d49acf365cfc62,0xfa7584120cf625c18b0afb9d64c872f63b51d79cf6bda43908fd06591b74f03d5a9617f4bc7382fd8a13c2f94053a2,0xf7c58641a2f1dac38752fdb6539a04f7a318d5b4f637bc195af1b3d79605f6170c8b9dfc94a8026f24309f84c2fb0d2,0xf0c2d48536fa16293b8cf5d042871cfb13a07564f9086b7d14f915ad830bf5218a73d9fdb502796fa43c6fb2a9cf7c4,0xf7203a16c8f58b2463d7fa95d21b47f94da6283cf4318065acf91486b0a2f04a8d69b5f5cb39071fbd1c2537fd97c0,0xfd803146caf2561d0c8af62173b50af9d42b8751fb607934c1f2d7b4853cf6920bc5d3f827409bd6f94a5fc7a9f381a,0xf07c68a4b9f7d5a62149f3165c872af03d8b751af960d285b1fd63502481f92bc3804dfb0c259346fdb37af4c17fa9c,0xf1c9748d0bfa72435190fd5b731ac4fa529d3614f26ad17830f956d218a3f6c758b2a9f07db682c5f49b3c80f60cb4,0xfa30215cb7f3d4a52807fd65831c27fc86a94b57fd1ac926b8f409d2b16cf436950da2f60bd53914f9b3c0a87f1847,0xfdb8142963f5c2619438f7c93b2d48fc4a097128fa3156c0d8fa9b50273cfb035d7a1cfd1b746a59f04b6da257f068,0xf60bd594382f53d96f18c36fac586fd2bc6f425b6f02a15f7c9a5f1d4c2f0791cf7a392f084b9f73041f7d8a4fb13fa0df7b8,0xf14860c3795f65d7af4d357fc7285f08d25fbca87f12b07f134c8fb1638f94203f6b9c2f96da2fd904bf1a46cf0d19afb3a5,0xf26b39c087af13728af6835afc709afd8bc3f41c63f4718cf57b2cf946d7f50d48f251b4f29560fd9612f91d5bf03a4fbda0,0xf9d0574c36bf4a651bf90846f1d304f35bd4f7a85dfc0a95f2bca5f178c9f7b839f0613bfad273f21c70f6c28df81a26f294,0xf091628db7af70496ca8f1a68cf20d9af3d24af7581dfb8306f5b136f43c08fb9350f714b3f2c951f274c5f297cbf5daf46d,0xf3c605b2917f78b9a204f94a0c7f56d07fb46a7f25ad7f139caf8143afb1690fd4c59f8d530f2d384f1c285fbc863f621db,0xfa9b2485c31f3527b1c9f8ad0215bf6ca3bfd90cbf4a50bf65d2af74195f694c2f71829f8037cfd6387f4d860f43d16f70a,0xfb4c9183a5df412c7a0df134926adf7b65042df368d9f03d69f528a9fb5379fc58b3f70615fc1a46fbc871f20847f2ac0b,0xf8256c9adb4fb75d4a302f18342fc58a2f941d2f7d962f09bc4f7c164f395acf0a78cf63b1af15379fd0713f086b5fd60b8,0xf8b479a2563f40719c68afc16487f4ca03fd58c3f1d6a3f72953fb0d93f157daf062c5fb1496f218d4fbc02df9b280f7b5a,0xf6128bc9375fa152407c6f9271ca4d0fb74c50f4685bf3026bf9ad2bfd631bf08d96fd3495fa0c35f87914fa2c83fd7a81,0xf85d9c634a7f60c739152fb94d13a02f4218b6d70f4c82a571bf95ca61472f3c1a9648dfb503fb790f8ad0fc2dbf6538,0xf56d4a172c9fd347b9a52fb8c14269df835792b1df3b06a7c51f0c3a284b5fcb640378af094c685df07daf3619f8021,0xf8a19074652f9c8b5027afd2cb1695af084d93b6af3875d06caf1d7b94035f0c73d814bf86db24c5f971c34a2f1362,0xfac8d179b63f8bc240593f613d7a9c5f125ad094cf18702b4d9f2a0b75869f1a84726d5f2db14a608f46c3f0c73f5b3,0xf0d83c41972fa87b16392f4b21d5c69f4350c7d62fb9a51c84dfb6857a09cfb06473a18f56a40713bf803dac2f259d,0xfd159c0a462fd94185720f5d87963c2fadbc60482f703b6a8c1f5b93861acfb437d6508fd35a90b74f13a7c429fb21,0xfc8371b240afcb72158603f08a3bfd4a20f9b482f6c25bfd9a62f1c978f41a5cfd357afd5647f31694f936d1f7c0f950fdb8,0xf0a9d3b1687f90258d4736fb92d6f5d126fa3c46fb840df7c2adfc5930f5a7b0f14b27f5bc97f138acf19428f351a4f6c80,0xfa781240c65fda034c9725f1608c5fc175bfd6b70f9bd20f483c7fa3b2cfd1937f4d31bfa8641f9a28df926a4f8b05f9635,0xf6cbd281493f4a8b7061c3f05312af8d903f742b3f5d048fb4c80fc7920f627d4f569c2f6b578f1b9a7fa51d6f5ca19fda3,0xf34bd172056f31b0c9d247f7a4d6218fbc648f307d8fc75a8f9a3b7f9b5d3fa290dfc16b2f496a0fc591af4153cf285f068,0xf70d39c158bf492b16d7c3f6904d213f5b384afa9d53f06273f7ad19f80cbdf5c6b9f4ca0bf24650f1a874f28175f2c86a,0xfc74b926a50f5c24a3916bfd8563b7af812d640af72a95f37025fd0315f860b2fc8b1af9c480fd71cbf9d3c6f83497f4d1,0xfc5a028493bfa72b59643cf8c4170b6f403d297bf56db87c0f6c190fd4a80f12c9bf73524fa3162fad836fd1857f15d9a,0xfa0468b7c91f25c036a9b1fca26bd751f53148fd6081f79561f9d8c6f3ad09f4a829f74d38f72d5af34b07fb24c3fbc205,0xf49a035c2bdfca25196083f1c4270b3df4a5617f5b18df2850df6379df6c7b8f409c8fb620cf4129bf3a759f1a643f7da8]

def e14_3 : List Nat := [0xf95d683bc12f4c5b1a02d3f5a6b947d1f80913ac2bf87c04dfa24bdf0b79df358a9f7284afc6418f3069cf61752f56370,0xf063859172cf79431d625cf287b61ad9f4705ac68bf214c3a75bf37d80a469f03518a24dfd3bc9a65f1c8402dbf09b,0xfbc07d85a62f1409bd5ca2f5193846d2f87b059a42f608b31c49f3d97561a0fb18a7c635f71d4b68c3f743ad02f9c2,0xf30b5c7d46af07928b6c35f248da71906f39a0df49c80f27bc0f52db9f1375dfa4785f1c2a8f1b4caf43b21f156f836f9d6,0xf0d271b534af7c046b391afc8b2605d74f49a61f836d4fcb796f028dbf5ca86f3da2cf1809cf5873af75130f521d9f29b4,0xf650a384129fc49d0825a1fb3027c5168f43d58afa7819fc8d2af624dafb6c04fb713cf90753f7db59f0b1d6fb9c2f7364,0xf940283d5caf648cb3190afb7086d2c34fdb518af4173af7421afd79c4f53927f69503fb8562fd1c78f0b16cf06b9dfa52,0xfc5b1da0396f2a6d78153bf8ac92614dbf0b971c36f720cbf5d286f38c21f5a342f758d3f907a1f9504afd0849f64bf47c,0xf2c85d63179f268b40c53df4c380521b6f6a570b39fa37c90fb94a7f561a9fdbc19fd06caf8d72af4d187f42b51f43028,0xfd9c73a8052f0cad749182f35790a168cfb872a65cfc4d830b2f129b7f51c6bf4263bf4a958fd07a5f64139f06d34fd1b,0xf29d4a5bc86f153d7a6408f71c52b0da8fd630c7b8f148205dbf3ca27958f69075f39b47f6c43bf9a124f160a3f19c2d,0xf3604cb1ad8fc0814bd93af49b6d1730af7d319582af9278af5b86afc5348fc20b3f7052bfd5690f79c15f64d21f247c6,0xfb19c3a6204f417c80a253fa5972d4c18f37d15c069fd9b286fb316cf587b6fd8b03f570dbf9ad50fa1247fc294af8463,0xfb05d612483f2a134b790df5b1d49c627fc0a917463fca5140692fb2073df53a82f9d785fc7ad8f6bc18f039b8f65c4a,0xf716c3b9a58fc12d74036bfc8d09624a7f370b52c48f9da34b157fd46a1927bf20659ca8bf35086d149fc5d3182a0,0xf952178a463fa6b51d9283fc962d8b1a5fd581c2749afc3420f7b3d0facb90f75613fd7a2bfc6d48f97c41fb04f350f860,0xfa28b463059f0a3847c519fc43db52179fd61acb3785f41d29fd80b9f726a5fc6b13f860c1f20d7bf4da70f4a8c2f3965,0xf20b714953df58c269b47dfc4608a315bf2a90c65784fc50a43f0361df4079df3812bfc7391f286a7fac925fb6d8f1adb,0xf874136ad2bf69ac381d7bfc4827506dbf4d021739c6f8c29b0fb1a03f5624bfd5168f534a2fa7c58fa59d3f970c1f940,0xf68d09742bcfd460b39ac7f35d261b4a7f9c2158036bf83496dbfa31d956fa140c3df82a05c4f25a8c19f57bf207f187,0xf637d049215f38624c5a1df3c082a9bd4f93ac7b816df0ad58c2f6b5907afb419752f6cb1784f1c960b3f74a8d2f305,0xf5307941b8cf17d364b2acf2840d95b37f68a4315290f7a08d24cf65dbcf75ad4f850b7f19b6df69a12f816a3fc93f20c,0xf6d49c2851afca264b0378f3a92d04c68f0c72b3914afcb748165f2069d5fd8b5af057a8f3d795fbd136f1b907f21c34,0xf358042c6daf7d219c0b84f5617938dbcf0d5296b137f57b9462af028c3d4af9d1caf1436afb27c4f50681f03b59f78a,0xf1b586d70a2f134d8a7b06fd02c38179af08bd1c7429f19b48c65fd9ca6305fbc41a396f3b275fa4625f940c5f782d3,0xf815bda0972fd578bca612f0591c4d8a7f0d1a49c56bfb17c069a3f85263fc2b93f7b413f02a53fd6843f47d92f6408c,0xf7bc4d52183f0724691c8bf4092c56871fa84795026cf0d2851b93f80c7adf635a1f49d13fb57d3f6a2bdfb60a4f9c3a,0xf906d5ca824fb053da2974fc159a03b78fc3721a56b9fa7c486913f4db2081f07d9364fa625834fb16c2d8f75bc0d1,0xf8d31b64902fd6c83a15b2f72c4da653bf7a48591c30f14780ac5df5a9634217f739c0df9250bf4068bfc79dbf162a8,0xf9b7d1a43c0f25bc1463a7f0d86531924f5d2b39c870f58497c20afb082615c4f8ac603db1f8b6ad9573f12a96d47,0xf836bd75ca2f874a165b9df7184bc395af1b852c9734fc7b3512694f60b24f9a802f72d40fc13d0f5d190f3a0f6adfc86,0xf7c5b6d1a09f470ca283b1fa8d7195306f92da40b786fa50d39b427f948bcf2564cf8026cf57318fd512bfa34d9f361c,0xf52b3ac84d0f28d371b4a0fa68315972dfa9124c6578fc261a53947f341d5cf9630cf7d640f7a29bf581cbfb806f9db0,0xf92706b53caf4c03197b2af4bc7596d82fd371568c9bf46c5081d93fa61487fc2da1f0b83afb3621f04d52fd0947f58a,0xfc740d581b3f2c08a9b57dfb2870ac96df26097b84a5fa194c6b027f71d4683f29d8c51fa61cb42f9563f053fad3f413,0xfc6a043d9b7fd603a85c97f9135ac4d86f942b380c15f2148bc390dfa46b507f5db1637f92c81daf02874bf1a27f256,0xf148c073d5af062d158b3af9a472c6b05f4b7ac129d0f428dbc9316fa6835b2f7d69025fc780365f81794daf4c3fb19,0xf06a479c1d5f0a13b94268f6c07ad3841f6d03c4b2a9f36402d7bcaf9172c85f9375a82fdb15c78f34d90b5f1256b8,0xfb12ac3570df431a5c6b7df14973b586df091c478b25f80a4b9c271f0c7a9516f5693df026a3f82463fb048cfd92fa8d,0xfa3d609147cfb0c938d2a7f716ad052c3f134b86597dfcb51a84036fa5780269f5812bdf46b9dfa4270f5c1b3f8c492]

def e14_4 : List Nat := [0xfa08c3db426f643b9528d0f1b756c4da2fa73850bc19fa135b8407cf03697d2cfb6d5a392f94720f15c9dfa8714f186,0xf68c74b2da1fa736bc19d4f839b7d025afd53b841296f40bd1785c2f309ca264f150728d3f081b594cf9756af06c3a,0xf597c4a218bf264b35a917f657a0c38d1fa82096d473f0586ac9d24f6c87039bf0da1c52bf5d360841fc29431bfdb7,0xf73091b84adf07b2d1c538f7ac60b4218fa5b6974c20f9d341657cbfb3c04628dfd58a6fc9368f4950df13a27fa9251,0xf75db1496acf60295b4d71f8b270d64a5f879da3b624f819b730a2df283d1a9c5f047a8cf056cbf2134cf68093f351c,0xfc7b40d2568fdb1973ca28f5746a12c9bf9243a50716f0c5139da72f63d149580f1c62b38f4cb6d78f035d4a9fa0b8,0xf9206ca4185f796da13c42f86b37c5a94f9163a7508cf0a651b8d39f64b9d0712fa87bc04d2f52830bfc1db2f35d74,0xfd2853974b1fd0a6812cb3f78d4a50261f70349b6c52f3ac9d608b7fc465bda91f90c38a7d5f40b29631f57c842a1,0xf139ca5db74f3c4d078a25f3048bc26adfa94386b120f3b28c7164afd75609b42f81d637295fd805c1a79f0c6915b,0xf268b3a0d59f25bc948d30fca64391db0f6d7a8c1b40f14a2d9b783f7c4da12b69f9085af73c50f2c618f653f175f247,0xf4c3b8d057af0862b491d7fa065b1c24df041a5928cbf6c5183a209f30ca648521fc9d37f16347f2d6b7f539bdf978a,0xf5371d69482f02d4a31b78f9d8a740612f4b0ca59362fa1c9b3d570f14c7db56a9fad0972f6c518f46bc3f8c2bf3058,0xf3a249bc7d1f8a7215db4cf1b0384a69cf0468d917b5f81a063d475f416b80da93f5370c2f3c62bf956d2f09782fa5c,0xf65d74ac928f7c159a84d2fd3c62b8049f7905b124c8f39bd0c2a58f37b0ad6914fb46035cf5702fa317f18df61afb36,0xfa8159bc247f0b6293d5c7f856130ca2bf190a4d6c3bf468d9a521cf084963a1d2fdb43827f417350f9c87fad06fb75,0xfc427a59bd8f5361cb029dfc3a8460512fb4a0c79185f13b69ac574f6a1b80739cf86da2b7f094382df304df1d7f652,0xfc7b68a90d3fac925741b3fc5a46d78b2fa058c17942fd4c0b56a19f407ad516cbf59bd283f4812693f80631df2730,0xf394c7ad26bf8290b71d34f19a308c5d4f73658d9c04f961a5702cbf79513860a2f8b1c64afa6db53cf052187df2b4,0xfdb160942a5f921d87ca05f8b9346271af84b0791c63f7d02c4186bfc96d280473f6a4d30c5f852bcf3a75bf135f9da,0xfcb9068a574f82c6a3bd07f056d431c8bf37b2a15d80f19c3648527f9ad26b4183fa429d35cf7d120cf497a0f5961b,0xf5a1708493cfd8573b4c2af74d52b963af1953d7b064f2d0cb83156f297c81db50fa09d6b1cfc6124a9f86af034f782,0xf7b1802594afcb2163d857fb50c29ad48fa624b031c8fd51ac3b906f2d19c5340af83a56c47f0db6827f396417fd97,0xf61a9db8243f7a504196d3f786cb09251fc264708ad5f8497ca6b2df27b9c8560afd4b38120f95b1c4a3f57d13fc30,0xf659bc78243f3a960b14c8f5d8b2730acf09d71a2648f7bd1935204f213b6a570df158ad3c6fd492c186f05b4a79c,0xf2a03bc1d87f1b429d3507f93147c826bf59c6d43a12f4a5816973cf6384915d7af468adb5c0f9ac20fd08b2f657b0,0xf8ca920735df24158bc96af7219b06c3df16280c75bdfc403187952f905c17b483f2b368a74df1b643af65a0df94ad,0xf31ca70b49df460c938b1dfa2b968c740fa3784c5129f5a62cb3418fa17b6c3524fb5916302dfa82790df6d75f08d5,0xf268d43c179fd0539c6b42fb085d73ac2fbd38190475fa63b84c59df314a7cb960f49a207b16f51a0c872f8a56d12,0xfb58031d749f273bd8a619facb6402159f1c25a36d4bf60538b2a7cf24a186570df3c0ad9714f82693d5c4f0b78c9,0xf6095217bc3fb91a687243fac28b61473fc0d75a92b1fa0b56d4c97fc62adb4807f5c8a469d20f9403f5d81f538fd13,0xf9781d2a046f14b507a8d6fb0d7134956fc51a47b390f537248cbdafc12b9d3857f4ca91b825df86a30f026fc36f9c2,0xf7d39c84a65f0c62b83147f536d4b1c28fda3c592718f1d52a9bc46f2d0b51a794fc7bd91205afa0378fb6043f6908,0xf8c0a6b3427fd526c31708fca3d485612fb475a1c968fd73095bc46f79adb0415cf7a49350d1bfa83602f1928fb9d2,0xf1d25a03b97fda958b21c7fbc2a38d057f1b604ac928f13946d5c8af0b53619d42f415690c3dbf34c6a7f26807f487,0xf70968b1a4cf857264d19cfb5d039421cf53a7db4182fb6047138d2f63da97b051fd65a0873b9fc02a843f592cf6ac,0xf03d4a82165fca7951d836f4c187bd5a6f840a2b37d6fc852d941a3f9c274b80daf70bc534291fc75b960f26b1390,0xf35021d97c4f51ca9b3847f6b2c085d71fad6270b8c5fa3d46c91b7fa2963cbd81f8a4b5930d2f68731425f06af490,0xf50d26a7b39fdb207c34a9f4b083125d7f5729c648d3f4c85b6d190f60a8b142c5fad49bc1682f0ca51873fa36971,0xf1c3a620958f47a0835d61fc0d4b27965f2c9d736405fc8da249b06fcb7193d284fb307ca921df5786b134afa8b51,0xf3a1c9b8504fac078d4935f2d5917c380f2a963b184cf62137ad0bcfd72b514603f79d6b4a825f16a09247bdf65c8]

def e14_5 : List Nat := [0xf8139bca7264f86143f24c1fb471fd9a4f0694fa091f5bd1fc379f5829fd0c8f75a8fb308fd6b7fc207f52b0fa3d2f5c63fd56a,0xf342087d1b96f56d82f47b86f1a726f097c6f31957fc4b21f50c81f9a5c2fdb0a2f38ad0f3584afd3c94f9d5b3facb6f0417,0xf72d90643c8af62a5cfd856af4079af3b50af849c0fdbc20f369b0f75d4cf3516dfb4186f28395f731b8f7d124fb2917f1ca,0xf1ad6bc84072f74356029f90526f3c46f17c6f83a6fd137fdb03f91b3fa9c0f82d0f5a2cfb942f58d9f4b5df14acf7815fa7b8,0xf74ca36d29b5fbc524683f70c6bfd582bf4d78bf1430bfa0d84f9a504f17a65f9c735f91c27f8ad3cf12693f061a2f9d180,0xf9c2b15d8360fc5917840f8a61d750fb5a70fa0d4f2d30f6cadfb79df2465f3c85f41c7fb34cf96b4f2186fa931f2a37fb928,0xfd42b0ac8573fb84706a3f14b69503f917d0c64f5a1c3fc934f8263fa804f2d90f1d86f5bd6f7218fa25dfbc51f9a7bfc792,0xf630dbc51a82f402b1856fc97a53d2fda34b095f0786d9b5f39a21f4961f7291fd7c1f5742f8c4dfa084f60caf3b6cf738b,0xf9d03b6c4a27f5d468713fd38ca751f091cb437f265c0841f40b293c7f1b7d8fa061f942cf5820fa9b8f6a59fad63f5bd2,0xf9582b16a07df431c9208f35da2406f479a5c26f7391d052f3a157c4dfac309417f2186df78dbfa4b8f3bc8f569bf0c6b,0xfa7820db941cfc3916b74f2d73581bf0c256a8bf3da1705bf9d836c57f95a4d68cf34609a21fbc724f15df048f296f03a,0xf5c78bd62913f42bc9d17f5a6c4821f381b652cfa075d861f0963d2a8f934da7b5f9b3a40d7fa941cf058cf0372f4b06,0xf42b9786a1d0f84a09d73fc92a7460fc814d69af58bc6349fc2d561b3fc17526b4fc7bd8215fa5b03df53a80f270f139,0xf028bd3a4615f7c9a2135fd4170c69fb2d78a19f485c36b7fa08c1b37fa5d8624cf1da60438f03956df0b5279f4bc29,0xfc7bd1952a36fd0687539f4817a6b9f3085cb27f41b3c2d7f4a8d650bf4d5b8c16fa512043df2831a0c4f926fac9f079,0xf3d49a7c0851f184c5927fcb3569d1fa8d57061f283c90b5fac864305f736da4b8f0a2c6b7df4026a397fdb142fb912,0xf08c497a65d3f93a02db1f5a1684b3fc2b69043f0c75b826fc9517246fa850d7b9fcad1470bf52a4d81cf136d92f783,0xf92178cb056af802ad6b43f374af097af528af13cafdb27f59b7fc407f46c2fd362fd860fc530f1d96f149cfb193f8b51f84d5,0xf318a7b295d0f9ca582637fc0487f41d27f53a17f6512af9164afb42c1f09b52fc8605fb6d80f34db8f396cbf94c3df0ad7,0xf0db13ca2468f27c9163b8f217d839bf87b5fa418fc048f6c4bf02cbf5d1cf50a1f9ad4f7a34f596af9260f52d6f7530fd379,0xfa86b92d134cf0485197b2f3a721b8cf69ad3875f2c95f7d5cf641cf05bcf36a5fa162f0bd6f7081f473bf0d93fd428fa490,0xf8a62b34d90cfd8b5a0293f56b08491f6059cb41f86c527b1fd731fa971f2ac1f3075f42c7fa387f364cfd582fdb96fa40d,0xf1703965d2b8f1ac43d059fd840cb5af75c1d42af783b649cf5137db08f16a4f920af3c8af682cfb974fd609f2635f127b,0xf15b3c62d4a9f65d907a38f27816b95fb04c5a1df0a842b7df8c20534bf582ac037f4796fc129f4139fad36f08d6f7cb1,0xf859b0d16a37fc083b26d5f947ca53df2ad79cb5f18403965f21c368a9f4d2c8b13fbd8241a7f0275f1709f64a0f4b6c,0xfdb026579c81fb64d8a513f07196a35f342b1a90f78216c0afd7c3952afd049b863f84b5d273fd6085c29fc14afbc47,0xf051c7a49b62f53ac8d746f825d1406f1875b4d6fc0d2b384fa930bc58f0795a1b8f91273da0f3c29db71fa6342f9c6,0xfb4639502a18fc53d42961f1d6c2783f085b17c3fb9a62843fa8c40d73fda512b68f90acb741f9d5607a4fc9752db0,0xf2d580b6c931f3a614978bf8d03c5291f04d69f57bd9fa82b9f4265bfc4a1bfad715fc83d1f63748f05346f7a2c0fc720a,0xfd136bc50a87f7b9580d6cfb51839c20f3a74c1690f821a53b46f9a48b1752f6a243d5f4973c8dfac062bdf270419d,0xf29b6a58d430f4819ac3d6f5b82407c6f5397b1da2fbd951c472fb0a8c9413f5d087a4bcf9683750f2d71a36f12c06,0xfd261b04ca59fa758bc219f6c1a4b379f24d386a09f64135d02bf81d605274fc036517d8fb708a3c9fdb5c782af493,0xf9c3142ad805f61a079b4df1c5b8349df7a40296bdf357bc2190fa687c0b39f158c6472bfac4817365fd0625f3a82d,0xfc5a1738d0b9fdb2148609f8a42c03d1fca6b79431f0829a7cb4fc653a0274f2693b85dafd25078c36f64d75b1f951,0xf4a2bc3518d0f864b31d920fa5830f52db0f1c482fc9742f73ac8fb7da8f56a7cf95b1af6d39bf49163f175d4f0c69f7260,0xf2875c9140adf08b3c1a25df56b21f6a7b1f8d471f6427df94cbdf348c7f96c07fa362cf09a86f5b938f59203fb05a4f1d3,0xf8a2614b93c7f185da6c407f50d8b31af360caf4280af96d7af47b68f379c8f2db57f52946fd9534f1c209fb215cf3d1b0,0xf6ac50b79384f75ad1928b4fd68a1b942f137a4fd9c34f5d3a9f06b2af07269f53612fc7856f18cb5fd803bf17d0cfc204,0xfbd312856094fa72051b648fb52407c18f9cb7361d5fc5783fd26c8f03a68fa0b35fd74c0f9ac2bf9d4a2f91ad6f39714,0xf8bc4709d253f37bda56194fa9b51c6d3f978d0c2b3f6927c504bf14ac9580bf8421a063cf1d7a86203f57182a64d]

def e14_6 : List Nat := [0xf63a2b4078c1f37b81d29acf6c025713d9f5d493fcb159f74a19f48621fd7246fc2834fa7c56f8d0a5f80bdaf06b9f05b3,0xfa7d8b20c935f4d3c170682fa87b41309dfdb192fc79a2f6d512f04a1df4c837f65081f59648f36b94fbc6a0fc5b3af752,0xf49a3b127c6df08bc5a2d96f857ac04b26fc87365d1f7da61f429b6f514c2f3819cf03d82f348a1f0b74af590dbf50793,0xfa47d63c08b2f829506c4bdf5831da7c26fb5d469127f9302df57042f9a6b0f1ca86f1435af79cb3f15c87f81b94f0a3d,0xf78a93c614d5f043195b86dfa1b94c2603f90bc5271dfa63b28c7df18d35fb642df92056fa7385fca479f07b48f2a0c1,0xf2a4b7865c91f730cb825d4fc8d2b163a7f6431d7029f539bda041f271a50d94fc26a97584fb381c6095f08ac3d6b,0xf3b85726ac94f50c248a7b1f1a2956bd38f96071c5d2bf08d4bf9d740f25378fbc3a5f936c7f0d613f20ad1f19a4f68c4,0xf439bd7a8521f7bc1d50283f036c94718bf248d9a65c7f5b197f692c8f0a359fad315fc06b3fac461f2a4d6fb40d2f087,0xf4bc69a08531fac0b952183fb64782c5a1fd6048a275bfb715d863f7c903fda793f4d1c3f6a491f8b24cf029d7fd0562,0xf03a9c62b478f82495a7c1bf6ad9734c81f72ca8d0b65f936025b71f486d1fa0531fcb385f964a2f04d3cf9bd70f2d51,0xf281a73b4609fc59b61d703f91bc08475af2b586c794afd51c96a83f520dac413fd2439fa0563fb8d40f78c21fd627b,0xf49687da5b03fa1736c05d2f842190a7b3f0751829ac4f520d3cb16f1db93a62cf5c806b413f8a4d972bf47c958d6,0xf46c082d1973f0ac14b9526fc815db3029f04cb2ad835f36d90b17afc586a4d07f31249a57df2c3965b87fb61a847,0xf84a9d61b503fa85c27d431f6ad3b08c75f2ac4bd1968fc920a3746bf9b7a5f712b8f0942df0c397fc6041fd815f2635,0xf8b0da47c392fc597d2b63af03178a64c2f438dbc1962f51d6c849a7f53b72fd9073f04b9cf5b14df5860af05618f21a,0xf8530a19d647fb027ad5614f96b3d1705af26cb739518fc360db2579f9b8c13a4fc04d7f2a684f38ac4f92d80fc21b5,0xf5249c60b73dfd193bc20a8fa728c4bd09f16570c34a2f1a6d48305cf7ca5b692df1462bf53ad9f18047f31586f879b,0xf913c87a4205f085621b49af7396b2d0c4fb836d572acf35160b928df6c5adb714f7c25b340fd9c1a684f3097d18a,0xfa061bc347d5f8390b2d17af1c25873b9af642970815bf19536c8402f8b75cad62f3a27c94bdf4d86af0569df4130c,0xf82b065a93c4f158d2c7a3bfd791864205f16d4709c8af49d1c6b780f695214bd3f7138bca62f375b92a0f4ad0c53,0xf6a75b4d918cfb6502834adf7495cb3d60f641d7b92a3f71c4869a52f42b873ca0fc9312d580f97c261530fd0b1a8,0xf513d8a2cb70fb5ac8174d0f39d5c78b20f6529b1c37df361279584bf6c91a75342fc4960f82da0f146bdfa904f386a,0xf716ac94d0b3f03925c86d7f81b2a043d5f0c3a915642fad148bc605f4c136b908af2c7a1f4bd27f83597f69d82f5b7,0xf9285c73461bf4d21c9a75bfc3da091726f935d742a86f83a51d0497f48d952c031fcbd6508fa18b706f3b6f20bfca4,0xfd7492b8c136f5b4a73d026f2db90a15c4f3a21d587b0fd9183c725af82c953b14df068a975fbc04396f164807fca6,0xf5d94b21736af3c61d25b7af281cb93574f3865920b14f5c7d806b31f726d3058c9fadb870c2f9048afd4ca0f1964a,0xfcb61a3d5927fd1463975a2f038d496ac2fad9065b8c4f847b91350af6c370851bdfd0b34217fb40c1862fa7825c9,0xf148b63c7509f283b1ad069f5217a04d68f1cb73a4208f0c4b5d2613f5a6c2b07d1f3978ac564fbd8c9f472a9f53d9,0xf1274c8a5036f41c3b58269f02a35d7819fb86073d429fad834b6c79f1a640b752dfb2ca7139df9c0d65fa480fc51b,0xfca7158063b9f5c278a6b19fd40b261375fcb497da386f1d39028c4af129d03c748f342d8b705f25bd69af41c0a56,0xf471d5a8c9b2fb856a3c14df7a2935046df0b15c4863df2180a4957cf1a907825b3fb7269d834f19730cb6fac602d,0xf09a78215b36f4931db7508fb69d5c2471fcb8d7352a6fad27c30b95f0c92b4a83df468ca0791fa34026581fc4d61,0xf12a83c0d756f4db3a50726f7bc60952daf48c1d97302fc78b51a492f80b19c435df58139b40acf82b6f6a9f3d6f417,0xf142930d7a65f91a2638c75fd2096b43a5fd94068b713fb21d6c48a0f1879bcad46f8db1c9a472fb3c25f085cf7350,0xf14b25d8ac03f70b62a4c83fc1275b9d43f09648b71adf7c2491580af74059c682df18792065cbf6d35afbd163f9a3,0xf734a1c8d6b2f87b120a935fca295d08b3f1609b52d38f684d1970c2fc46a31750bfc9630415a7fd9428af74bdfc56,0xfd18ac053927f9a34c6db07f8c306142a7f5d26a4831cf6b528049d3f68b195a0d4fc9658da12bf3b902c7f7b4f157,0xfc1905b73862f34db1a9756f8d6152403bf0d3ac8274bf9485da70c6f80a213c9d7f81d2935c4afa59b206fc7146b,0xf56804b29cadf972a4c6d30f59a61c7820fc2157b9360fa34d258170f48c5bd1962fb8a137d946f47a53cb1f83b0d,0xf539b804a7c2fb50c168472f9ad13b4c62fd837965a12fd951bca643f0bd5c9178af941857b6d0f824d7063cfa302]

def e14_7 : List Nat := [0xf182504a7cb3f9c6b073d24f59db1a2603f8b5720d6a3f9ad5c87163f0864b2915af97d41ca856f09b748d12cf4c3,0xf6b29cad0378fa5b70694d38f3c6a25dbf915642cbf179a435cf720a314cf7409d61af263957d1fc0b18f28df4b8f508,0xf3c2da619408f9b57d6c4130f4b206873f2a8b7469f2158d3b6fa1bc7253fac9d4817f5d1c824af9a0563f795c0fdb0,0xf914c0658a72fc3b78649021fd83157c2fd0a26b81fad9c6371fb25a3961fd359bca6f7d50b4a9f8074db5cf403f824,0xf18d95370b46f5803947b6d1f7a5bc631f421c0d3afdb8c340af609c2b1af4872965cf914d528afd79b3862f7502ac,0xf63590cbd874f608257c13adfb3415a9d7f3ca1b05df2b856a0dfc27396b5f216c948af83024b91f079268c4f1d4a7,0xf51846cadb72f3a075b96d8cf85c92a716f93b0d4c21f34062d7c1fb8a63d1fa530941f780cb24fb65d9a4f5973820,0xfa135d7bc046fac21d083749fbd2960785f209c4d368f193a724b6fda417c3b8f2b159d6fa0b9752fc184305fc65a8,0xfb5c34d1a078f9ca7d046312f6503972a8fc6941b358f4a602d518f7bc428095f9ad61c74bf8db25a3f0c26bf9d371,0xf7290356a84cfad251b86394f85cbd4217f1c60579b4f195ac83b6fd13a082c9fd3c0b2a18fa962047f37b5d64f07d,0xfac582d93b74f7ad124638bcf68a051b9cf25bd6978cfa53708419f0b6a3d759fd43062718fb40d561a2f0294cf31c,0xf35da0b24c78f946bc30d752f813bd9726f1c0284a37f1d4b596c2f615ca908df8b7a19365f8c9b1406af4705a2d3,0xf0c56db97142fa9081374bc2f46ca5b3d78fa34c85296f530b28619fda8b60512fa407c38d1f7a0d9362f4d57b1c9,0xf5b86403a971fc7da6b05941f27a061834dfb908753d1f91a2c8473fc024bd963f0d5ca82b7fa58d629c4f256cb31,0xf9d256b831a4f82b1c7d5364f8c093b5a627fc57b42f916c37fbd80acf150b92f8596d1fda8603f3a204fc9a74fd0714,0xfc056b4a7812f9d02a534c71f69258ac3740f1d2b03af36d7bc1f5c8093bfda97283f570a6c9fd51bf948bf6241fd864,0xfdb14c658a20fc296a435180f13b8ca75946f17b63c52f05a3824fb268da0f739b5d2f487c91dfbc1a974f9d30f7d60,0xf5d7048b29a6fd639c21780af34259168db7f6b974a30f851b3c7af5b0ca27fc53814bfd264c13f20d96c8f094d1a5,0xfd408c159273f5a0268d97c3fac94852b71df16d78a43fa2d56c03fbc247a18f905c4b6af9b570641fb1283f963fdb0,0xf94a51bd8026f6a853427cb0f97b3684d50af371d0928fca2b4078fc6b52130fa19d74c3f6da75c14f9b8165fc93d2,0xf36c409d5a81fbda94708c51fd69b872a3c1f4b37ac91f7d3860a1f48257b6af530bc2d8f4297c056f934d02b5f612,0xfc304a8b1659f4135c270db9f05d1a7c6839fa9d8cb4625f7b2d69f7da3b5f02436bfa21c06f0874caf4d3718f58291,0xfc4a8352db91fa3cb7d65841f3d8602974b1f2c87590a63bf2ad051f930b5df62708bf49a5c0f6ca734f9c716f824d1,0xf6139ac725b4fd584a170b36fb8d120375a6f38a05147b2df28195cf809b1cf65349cf042a3cf7d0629fda7869f4dbc,0xfb473d26a580fb34150da2c6fca35249bd70f9a48275cb13f20a7c8bfc16403f879063fd17b56f91a86f29d81f5d4c9,0xf7c6594da1b2f435b90c1786f1504c93a7b6f1975c3b0a48fa58bd12f96a8d52f708ca9df6382f4bc2f306df3741f02d,0xf1a3c9d08526f1b57ca8d209f1742a6c03d5f79a064cb81df35adb96f68412c5f39278c1f382b7a4f0495fb4d6f73b0,0xf039a26d741cf9164b75082cf40da8b9217cfdb3496025a1f81b6c3df51372bcf5b097a6f785d4a0f8359d24f63ac8,0xfbc7d2a16850f9b436271dacf3db125a4879f753a814d92bfd51c4730fc8d6a70f82c59a0f5b83196f9420f3b6cf046,0xf4c957a6d8b1f9d2b04387caf8cb42973605f9b3d47286c0f912a3c56f70ad531f80d7b51fc2648a1f493025afbd16,0xf048365ca17df2034c6a57b1fa93728c0b64f8a2c79b3506fa781529df261c958df6908b5df3a0741df3cb2491fdb4,0xf70b84dac621f2a36815b940f957bd8a4c31f2d7a06935cbfd1472503fc0873b61f290d5834fa64b1f56d9afc82f9c7,0xfa314b502968fd5872a94603fb07a16d4c93fd280436c159f6537b2caf8b621d7cf48db1752f19bc38f74a09fc5ad0,0xf30bd49a5127f8b6a13c47d2f048693b2c57fc061d85b429f83ad5917f9d3650a7f41b90253f80d62ac1f6c8a4fc7b,0xfc5d62a08317fb4ad8709516fc0d925b36a1f821d3cb9a56fa374196cf49c27b06f8a75024cf81b2d435fbd793048,0xfc2731bd0468f7a5b0c61948f1cb426d5708fa09c517d2b6f928d1a47b3fd38b9af85603af502143fc4d963f52ac79,0xf6b15c7290daf7d8c965b31afb826071c359f0c216db7385fb25d36ca04fcb08794f302d4af1d9a24f681934f475a8,0xfd8127c0439bf2605c8a974bf928371a0d6cf6a209135d48f495a3078b6f0851c3bfd14c257fb165f7acbfda42f69d3,0xf52b64da3097f8b0c17d5a63fc49b1a0d658f6814a9dbc50f6c913b7a82f9615b473f5348029f1d87042fac72fd3c2,0xfc156082db79f0ca491378b5f46c27a30d18f61b93c7042afa0214cb685f3574d92bfc8d71a95fa83625df6d34b09]

def e14_8 : List Nat := [0xf0946cb3a517fa95d6082c37f6520341c8d9f1935c0b862af831b4ac927f0d2b97c4f8adb6124f36a0581dfd47f5b7,0xf75d6312a408fb0918c7d243fc417bda9620f1d8297ac64bf2b9c160735f0d938b5afcb6851a3fc274d305f948a65,0xf875d9631c04fbd7158a0643fd28c39b4a50fbcad6147295fc91803a7b26f6b12c5fd1a683f4c79a2fd8b094f20735,0xf6c573d14029fbd530ca8479f1a90658d43cf6b594283a7df178052a4b39f70bc9d2f2b7cf864cf615af6312f18bfad0,0xfb4975a8c3d2f0d5936841caf1b0c53478d6f4cb5037a196fb904ad71583f06a9c72fbd1826f52c6f13a2f9d42fb708,0xfb14c87905d2fc7a486bd952f3c918d465b7f51cb8a03947f43d6c085a9bfb3a6920fad7062f172836f40d12f531ac,0xfb4680ca915df47052b1c3a8f3d496a2c5b8f7da4209c635f7b92d60a14cf3179d04f65a781fcb3958fb62730f21d8,0xf126a49d5cb8f716bd43c9a2fda386951c42fd35ac790641f048d75b936cf192087bfc8a13b2f0a73f074bfd650f528,0xfa2d47091cb8f2085c6b49d7f39b0a146257f24035a96d1bfa4c9215d063fbda7183f4316ac8f3c28df65978fb50c7,0xfc306d82a914fa53b792d1c8fb056ad93172f516cb90a378f7a1b5c963d0f126bd48fac20864f95d7c04f34b8f7524,0xf792b31658caf960b7d34825f078d493c215fbc738091d64fc172036b9d5f0c9ad24f4c68b1af357418afdb5a0f62a,0xfb851d9ca427f4618a39b5d0fb3194d6a280f35cb692148df1c834b2659af0a52c479f860c7f1bda7f502d7f307fc36,0xf9028b5346d1fa4978031652fc1b7d506392f75ca0b4d962f074cb6a958df8a7c9bd3fda5142fb3712fa3c81f0c684,0xfd9074ac3b56fb97c48da520fd19c534b780f93851cb27d4f3759a8c21bdf5d28b630f0c6a314f62a0f9246f816f7a1,0xf3ad5b19264cf8bd65c21704f52b387a06c1f827c053d9b6f5a2d8c930b7f081acb4df2097314f7d16a4f9634fa859,0xf1d0584b36caf16b97d25c04f7bc130629d5fdb8390217c4f9c3d68270b1fd815647af8735b2af08c243afa496f59a,0xf13b9ac4d287fa290375cb14f6b21d580a39f7c26815ad0bf61a8d35270cf65b8347df0591c84f6a79db4f2063c94,0xf2068347ac5dfb1642a3c80df6a0bc12794df2c4a8750936f52b841a9c03f956b318dfa5b4071df96c7bf92851f37d,0xfc4d07a26193f04386bc1da9f7d31b4a506cfb725641a803f8d5796a0b24f8736d95cf82db9471f92153acf20cf58b,0xfc5bd1684279fc34b6071928fc625da730b1f504a2b9d381f63a8d209574fc0a69312f356d087bfb85a14cfa94d7c,0xf65087d319caf859bc4d02a3f28406c1adb5fd692741b0c8f49a703b2d16fb62175a8f97342c5dfa093c7b4f68153,0xf49c81d36a50fb1c4382ad56fa742b9d853cf72139a084bdf14a8703b529f7c20b86159fd0c6f2d46fb75cf371af096,0xfc379ad480b2f1b7ca46829df8c14395706df1a30cb58742f17a5c694b38f726a04c9bdfa8b63d2f0d52f1653f0915,0xf437156d2c8af7a3b04c6812f6a14d9587c3f6205a974bc1fb69428da0c5f319ca25708f092b7d3f9b1d53f0db846,0xfa2c7db68135f7a04961b285f26a870c9d14f8b03792da1cf6d83a9b7120f915084ac63fb4725c3f90d4cb5f65d34,0xf1d24a9730c5fd486391b27afb43d6c80217f3bd816294caf0d96b82c314f38a647cb95f1c90652afa0b5fd705f875,0xf4630512a8d7fd09286b1ca5fb7a9185c06df072bc9d413afb934c780265f3b84a1d257f59716ad3f42c69fb04fc38,0xf48b1a56c09df726a385b049f2517b64cad8f031d5c74b2af42cb3507d61f7a8c1960d3fbd208639f218759fc34a9,0xf1439d0bc8a2f485b7d31602f5a3796c4bd2f6804a17c59bf8d6a9470351f3c0564da78f28b190acf75d1c92f63b2,0xfc29ad70b185f3b4ac8d6275f17342b9c60df964c12038a7f41a28b63c09f6a3d487cb5f931680a5f047bd915f2d5,0xfb8da4906521f3a04168c2d9f7b2035d1c6af824bd7c315af785c0b34d62fb63d057184cf7469fca19f7380f95bf2a9,0xf21d06a783b9fc537d841a26fa9c8570243df2c7b0918a4df0a5931c4728f25179403acbfd968bf5b16df3c056f46b,0xf91628d734b0fb5ad3064279f3c874a2051bfc58407a31d2f9d41c08a635fc49386d0a17f57bc92f18b2f65dbf6ca9,0xf6b38a417029f521c7da9463fc24b95061d3f875bc6d2a04fb7a1865d9c0fc5a628b1974f3ac809f158d03f4db273,0xf96b4037d2c1f27b095683d1f257c80a9d46fac029358bd6fc3b942a78d5f079cb2843adf74c6051fa814fb5a1f361,0xf57024ca863bf485c219a60bf5d0c9341872f94ad6135082f59d746c30a1f65a7c83d409f62a379bf2d17bfb8df1cb,0xfd3a8702c6b5fa1cb3094d25fc7d804a9135fac4821736d0f1b7429c06adf26143c8b97af72b4685f9db056f18395,0xf431c52b7da0fd4756218c03f8241905db63f06d2a1b84c7f20d9b5a8617fc2951d80b46f69cb37af58794a3f9ac3,0xfc4b075d9a83f72dac684193f82c516b794df78c924a5b1df26509b81c7af469580cb217fa13520d6f3a06f430fbd3,0xf7851a9b40c3fa2bd6170843f062495bca83fd920b741c5af728c4691d0afb86c7905d21f7d813b65f2c935fd4a63]

def e14_9 : List Nat := [0xfca14d637059f4a539bd2817fd840926c1b7f4602c38b5d9f861da0b3425f2a6b4c80d31f30c5697af9a8751f2bc7,0xf79538a4db61fd03b82a6c51fc263487d9a1f27ca5680931f407ad3cb296f7b5d8c420a3fb06d2581f574b9c0f419,0xf820c7a1d3b4fc30d86129a4fdb80a356c24f6278c15d934fb19c5706da2fb90581736acf31497d25a8f0b74f6b59,0xfd904713cb28fc59b61ad078f4db56c92a08f0c4a539627bf4219a6d503bf36497ac251dfb1437d2068f57c18f8a3,0xf49a356c7208fb7a14d5c392fcb1875a6342f13db46058a2f1c8d073b695fca4791d68b0fad71625b90f4c9d2830,0xfc681b4a9352fd5719c806b2f48b7a1c3d62fac47305bd12f3a59640d7cbf94d85136a07f1438ad90c56f0b92f782,0xf429b51c3a8dfb60391da2c8f497b36d0821f37462d590b1f7d35a04bc61f25834c96a70fc72bd9a4865f05781ac,0xfa8603d17c2b4f0b1af5821f3781fc961f4091fc508fd6c0f2970fd538fb648f3b56fa726fda52f9b75fd4cbf49d7fa93cf243a,0xf52b0c93687a1f2d13afb691f7061f4ac1f8c6af0d9af53daf4bd6f5c26f7b92f4902f7d59f804df3750f43c7fb583fc48bf812,0xfd26cb87031a5fb365ca0fd4180f51c3f27b5f8375f9205fd8a3f4c93f860cf2a7cf4690f4b28f1942fad74f9d6afb61df179b,0xf02a8416397dbfa086d319f2b96f5129fd409fca49f70d1fc7a1fb781f56adf852df305afcb60f42c6f7382fc5b8f3475f4c3b,0xf09126ad47b53f793d28c1f3c51bf8731fa483fa241fd861f0cb4f9ac4f05a8f5db8f0d7af6c9df257cf6b95f2b07f6920f643,0xfc7a40b358196fb4862da1fac297b6f49bd6f0617f3c56f28cbf5a8bf0278fd038f41d7f5d37f9c4df051cf2431f9a25fa093,0xf5d7924a138b6fbd86a740f157cb9d6f0648f3a96f28c6f72a8f5918fb217f3507fd25afc902f4d39fc30afc4b5f1c0df1b34,0xf92da83c0b564f17c582a3f24308d51fa93d6f41caf075af1b7af9bd1f2b35f9d05f487dfc4b8f6973f06c9f2740f2cb6f681,0xfad836290c514f56a91b48f8cb20746f7c25349fd2406fd961f3059fb6c9fd3c4fa71cf87d0fb5a0f7bd5f3127fa8b3f281a,0xf2d31605c47b9f73ac1b49f3b526819f24ad0c6bf90bcf6359fd7a9f85dbf07c3f8d43f278cf156dfa846f1204f5a17fa082,0xf07bd36482c5afd6c9714af2b93506afc81d759af74d8af049df215df0c19fb861f2569fb026f3780f4c72fb43cf83b5fa31,0xf0247a85cb963f719a6d35fc6b412d7f4c265a09fc059da3fc1a29f5b31f8793f4073f28b7fdb25f84acf61d4f80b1f068d,0xf9b682750cad1fdbc42a07f6c37a4b0f938402c7f14690d87f43b7fd594f3180f21c9fa3d9f652df61b2f58a1fb5c8fa635,0xfb4d370a5c621fd9b04831f8ad0c2b7f5208b6d7f8695d2acf539c1f7164f8291fcb34f2794fa7c3f6503f6a90fd85bfa14,0xf0bd7c15a4369f2ca1b56df9746a8b3fa2578049fb26830a7f429c061f3c84df918df071dfa35df2731f4b6cfb95cf2058,0xf680b29a375d1fad8b9431f7a50c14df0956482dfc218a635f79c83062f91bdf6b3df524bfc47bf02a4f8715fc693fca07,0xfa782b16905c3f6c79a1d3fb4170293f519b8ad7f4ca560d9f6a0bc248f04d83f5213fbd27fc081f58c9fb6d5f4a26f743,0xf69c7520ad81bf97d364a1f5db8a271f350b94d1f29d0c65bfc5809a62f6078c41fbc124f3b74f286df3840fa395f7ac3,0xfb83d97c64a50f34b75c90f92653bc4f81b93724f159a3c87f1a86bd2cf612b58daf82a0f5d02f4d60f7ac0f1d74f6319,0xf20a34db16c97f70cb528af4a5c3908fd7569240f312d64b0f17c26a94fd1ca2b63f374c8f6058f19d8f53b9f5da1f8b7,0xfb518a74c0d36f725d4a61f9b1a53c6f02cad946f857b391df0438c795f842a9cb0f4b29031f5c126f87d6f0a37fb82d,0xf21b35647d8a9fc02a69b5f871da4b6f81c9d42bf0d3c827bf50794162f57a1306df915a0483fc2dbf34c6fa37cf9085,0xf43087c159a2bfd5b648c3f126a058bf4a79d6c0f6173a820f5ad41863f1d2574caf49138d72f293bcf709bf9c56f0db,0xf43960b8251dafa0d473bcf7248c05afc56db214f97085b61f3c2d7590f835d9c71fb9263d87f204b13af86c1af946a,0xfd3052a641c79f34d729bcf0749a1bdf8136d5a7f2408591dfc2b48609fb5c82173f0c4a8b62f7b0ac615f83adf6539,0xf37941605da8bf57db93c2f04c7a192fd3865b72f1d69c0b2f53471b6cf1580d4bcf09a36487f130a59d8f6ac82f4a2,0xf462571b8c039f609b7a38fa9db4780fd592c6b0f73bc5169f207d8a5bf185043c9f27c1da48f31a24d65f4ca63d21,0xfb2d63a59c480f150c73db9fd049fa139f7869f6b30f7da0f5d83fc143f1b4df725bfc28bfac58f16c8f7a65f264af7124f209,0xfd8c392a460b5fda3b851c0f7596d1bf2bc5f47dbf9a6bf0365f38a5f49d3f204df1a73fc70af8190fc279f416cf2871f8426,0xf2b1d943756c8f1c4830529f62d7c514fda24f0bc2fa361f8b31f59c3f96d3fa40cfb974f08a9fa0d5f786afbd85f6b70f712,0xf862b730a14d5f2796a4cb1f74b8d391fd6409c1fc315f8c61f53b6f0836fa243f9a84f2d78f0ca7f52c7f0b92f5bd9fa50d,0xf8a5c04d7b962fd3a249178f3c250b48f07c461b8f1ac8f1da4f3574f037af9d27f906af2bd0f5b6dfcb36f1c95f2931f568,0xf43178a52c06bf056c1a93bf92b7d85cf49d2168cfa62083cf97cbfd196f4736f5309fd0a3f4270fad57f482afb14df15b8]

def e14_10 : List Nat := [0xfc61574a9d30bf1d59b72a8f37064b58f2d0a136bf349c521bf7c48f6ac8f0428fd714f65adf92c1f3c05f93a7f2690fb8d,0xf83da594bc207f7b80ac314f1c0d6537fa1b03697fa81529b3f24a6b57f9d7cf4093f6c50f864cf2d16f85d4f2a91f28db,0xfb4056d387ac2fd712a6308f0279c586f948bd152f9075bc46fb95d0a16f28c6fa918f34a5fa39dfc1b0f3c7bf4731f4d2,0xfa4365c187d09fa1b2d860cf6a312049f246c80b9fc27058b4f1d5a03c7f57a8419fbd93f7bc9fd374f8253f16b5fa26d,0xf69b0c13da274f84bca0973f3402b68cfd7a16524f15db78a4f5a9d281bf30d12c6af7591f3629f507cfd806f853bf49c,0xf80d57c639b1af2703415a9f190a25b7f4c1db6a7f38b240caf8265cb37fd3c20594fda48c97f460bf68d9f1853f2d61,0xf194287356b0afd0748a962fd5bc3179f3a41c509fb18d30c9fbd46a512fd758b361f4b7ad683f6c80f2c40fa27cf259,0xf50d3847c2169f175a62b39fb46d5829f02d41a36f53724a86f1d78bc03fad81c5b7fc40b152afdb6c349f809cfa079,0xf42db73a05169fa197c0b3df1825d6a4f8570d934fca5b1304f278653c1fc8362095fa9c2b8d7fa806cb92f71d4fb46,0xfb5280961da73f1ac384d27f6d85c412fc7b9d302fa5940db2f56a9c87df1b68a475f318bc60af0c19364bf5079243,0xfc52d73b06914f9da186504fc39a5bd08f2c7a3d158f612ac095df271b9c6a0f6bc135792f307b4f638d4f478af2b84,0xf13a7905d8c24fa618270b4f5a1b936c7f021d9a864fc52b30691fc380adb59f4d0ca2658fd7bc492f3d6b874f3517,0xf7129465c8a3bfa70c3d4b6f9043872dbf52037d9cbfc16824a57fc48513962f9ac635081f59741a0df0b1d6f2ad8b,0xf3d257c0a849bf4a906d8cbf835c2740bf785a3142bf6a1739205fcad469703f6821d9c43fc180d7a26f916b5fbd51,0xf415cb0926a8dfa5b7483d1f72c4b3685f9d56b87a4f203c81964f0d7ca9534f0c61bda25f280a3179bfc93706d21,0xf8c50a97d6312fbd834c16a5fa4d359602f157ad2409fc03a1b652f41870bc39f84b37c9d0f46ca85d17fb729fb862,0xfc7a053b21648fb9628703d4f38147b5c6fad9527134f9ca375604f9a51bd0c3f92cb085d7fd2091a8b6f86a24c1d,0xfac5d791b4062f1d2569b378f6a9051c47bf2c70bda38fa7536c9d8f4271a08c3f930d614a5f584d312bf64920cb8,0xfd697531ac8b0fa786421c05fa07bd48256f203c59416f60817da2cf39158d2b6f3d5b47c9af729d1bc43f9b38a40,0xf2a430d7961cbf7402c9a853bf13c0bf08b5f924bfd86bf6490f73a0f1839f52d9fda63f6c82f1a72f7148f57cafd651fc4d5,0xfc2653b7d0a19f0486a275d3cfdb8c7152f82973f31c6f4b03f95a3fad87f4907f5ca8f4d9af1208fb605f4cb2f6d14f61b9,0xfa469c780b2d5fd8c24b793a0f415c06b9f8a629075f27d65f95b1f3405f3820fa1d9f17a2f3d47fcbdafc684f13b8f63c1,0xfc736d41a5829fd174b30a6c2f4c83502afa95d7b13fcb2570d3f91643f8724f9604fad97f81caf0b5cf6215fbd86f09b8,0xfacb4617d0259f948c5a30621f74c2b6d9f758a240cfb0a15687fa418d507fd1c92fb809f6c39f7382f31b5f3bd4f3da6,0xf42871c6a39b0f2cb6490375af1bda0725fca9d3b20f41368c7bf9126d83cfd74a1692f97a85f435cfb805f60d5fd184,0xf5692d3874cb1fd06a1c24395f09d8b735f704b68c9f17280a49f641db03cf1263ad48fd613b2a7f58ac7f20c5fb9a5,0xf130a857d2b96f536b718049af1bc24659f3c0db529fd4c12709fc682ad15f8b341a7cf4a605d87f26d384b0f73ac9,0xfa1690d84b573f3c729a86bd5fb06d2a478f0283f5a08f15c8f4250fc170f9365fcb26f14c2f97acfd9b7fd46af3194fb1d3,0xf6137d0bc925af4bd269183c7f4685b307afc248d356f0c8af9780f4150f2b60fc175f94d5fa34cf27b8f9a1bfda21fd936,0xf74816c02db3af3179a8b2504f603c49158f35a1cb08f928756a0fd5c8fd370f6d93fb695fb7c9f2ad7f4d1bf24acf4126,0xf63d9b512c7a0f1a6839270b4f9c03a2bd4f340d6b87fc8da9526f1bc35d79f1c46f2084fa574f5690fd182fca85fb317,0xf6d059c34b12afb27d41308a9fc0978361af8c73d924f52068193fb85c2d17f5d826bc1fadb3f740af564afc694fb570,0xf79b8d514306cf684ad31bc09fc2db50a81f25c947d1fa7364d91f08c4b26dfa59283b6f2407853af7561f3ca9f20b7,0xfda2905734cb6f8130b46a72cf2d841a0c6f42871960f5b793a86fd5ac9b20f521b3d7cf9538bd4afd1580749f3c16,0xf52d47ac19b63f248c30d9657f07b583d6cf13460b8d5f8a2bc7d16f28714a09cf9adb40812fa1b394c5f026a3795,0xf03941b57c82af4a9c20d37b8fa62479138fdb43c617af508d1cb63fc07d6951af6409d5278fc4d29b065f185a3b2,0xf2d937ac0b468f305b74129a8fbd36027c851f7d0a69b81f091c526d8f613cb2495fb3a4079c6f84d1a57f534c2ad,0xf174bc25a369df3b16507a94dfac6029b837df0d5127934fb0c14a86df87591a264f3c5b6a081f9c7b28530fc8d24,0xf36a1b492d758f148a9c6bd02fc53ad1709b2f9d6430a51c7f52618bfa73c42f3950cbf965d31fb7860fd4728fca408,0xf21594d3b086cf38d1c7b5624f9b146305a82f7d531a06b84fc09db25f72a39c8f402dacbf796a4c3fd07a916f7581]

def e14_11 : List Nat := [0xf07b42a85163cf640821cbd39fa0d25b19734f72b831d5c94f3ac29d4175f7da18cfa50687f09a6b3f9b0265f6d84c,0xfa741db92560cf586a93120b7f96184b5ad27f591a8042b6dfb8362a49051f78c30df46c9d3fb3a07cf5c173f28d4c,0xf07d9c152648bf8024cbd531af5794d2b6c0af9b165c738daf293d14b58caf6d034af6817a3fc287b3f047219f0695,0xfc72a91b60485f9db0751638cf4a092b5d31cf3b7a124d650f9b820da6435f68173acf08a52cfb493cfd8741f697d2,0xfb065d971a2c3f6c58b739124f7db52630c94f75a3d09b618f92d6a07cb15f0538ad4f1d82b43f968027af1c84fca4,0xfd695bc28a374fc84613bd07af49756a1b03cfa5c19d20834f24b7186390af0c7d514f6b8729cfda9b258f53d1260,0xf5ac7849b03d2f9683bd02c17f42859c31a7df5da372b6091fcb80574a926f639d8c0a21f65341dfb46a81fc407b5,0xf9b1638527ca0fd7a8493b560f26c953d1478fdb21964a3c5fc42d9731a6bf51c29ad8b0f57b402af34d680f718c0,0xfc3847509bda2f0a39c8156b2f0794c5d1368f3716c0b5a4dfa7bc1460359f6a1b34278df58b40d2f9d7ca82f1962,0xf265b90d7c341f06ac92d8174f8ad3950c427fb0831649d5cf5379a4d6b28f1963025a7bdf8b3a2cf684b1cf1a075,0xf29d5c3a860b4fd70cb2a9648f09ca415b628f50da61347c8fc256d397a04f5a1c63027b9f94db381f71b8f357f1d2,0xfd3a5820b1479fd1a26409375fad6b2708c19f436cb8a7129f86a4c503bd7f3560ac2d481f169b425fc7b59f0c38d,0xf183b592dac07f563a90db748f7d4391c6208f1b2c3d96a75f60379cb4a1df7216b940a5cfc4135d8fa250b8f6428,0xf463d5a91bc87fc657d039b8af15206db3497fa41c058d2b6f3590812c4dafb04829d13c5f073861afc9624b7fa27,0xf5064c39b7218f4792b16c0a8f041563bd2c8fd359c70b4a6f5ca249031d7f91cb520d43af9d5a1738b6fda78f268,0xf4db8097a2536f043781b65acf9306172b48af947c21ad586f2d1c59b70a6f38d6c92415bfd028c4a319fd3cb057,0xf634958d07a12f16a3920b475f6c52db819a4f879d305bc24fa068c17b35df8a2b6d73c90fb965ac72831fc04fd14,0xf62d950a87143fd06ac24b813f5b6d7490382f9207a156cb3f40bd537c916fb21c4ad8579f4d1b72a5c08f8c3a96,0xf175d026c4b3afb035972ac14dfa81df863df256df9c7df0837fc213f9a43fb5a7f4287f690afb192fb649f8c04fc58bf6051,0xfa94b1d26c073f836d5b24ac97fad917f28c7f5147f084df358df13b8f65a8fc2a1f6921f0b6af0346fcb93f504cf0952fb7d,0xf42ca6379d581fd8394b26571af916870afd48a7fb047fc027fc3a4f6b34f592afd082fb1c8f5312fd603fcb96f509cfb51d,0xf24c1da9637b8f9564a30712bdf97841a0f385a274f5186ac2fb5c3916fb9c7531f3d8cbf2604df50c6df7a80df294b0,0xf62c4b9ad1530f2a34178d95c0f93c8bd50fb740f3807fa6d0f463df1cb3f297df1a5bf612bf8691fc756f8425fca49f27a8,0xfd964b30ac872f7385db14a609fa1539207f50d3af2b9af5c49f86dafbc65f2175fc263f4082fb7c0f816bfd847f431dfc19,0xf9c57d830462bfa942d5318c07f608b1725f6874a0bf51c4bf397bfc637fd3cbfa12cfa843fd914fda61f096df5029f82a5,0xf9a21740b35d6f5ac27d061b49f7c18d25bfc924da75f6315f8305fb862f0782f3d97f19bdf43a1fc46bfa8c6f80a4f3c09,0xf3027ca5b148dfb6a197408352f9da2c650f64928bd0f5d70cf126dfb7a0f8c96f3716f5187f9a85f3cb9f4a3bfc431f42d,0xf804c29db6371f460c95d8b721fd4b97851fa482b569f705391cf5a38cf1acbf613cf2a75f0349fad68fd247f0a62f0d3b,0xf7852a91b4c63fb96182743ca5f831a7590f6d3b8c50fb65124d0f920cf4a30f7da0f9d53fbc1df268df7c2bf9417f46a8,0xf3bc875a62941f809ac5b643d2f95d03a81f6d837b05fc35869b4f7251df0c17f6021fb2a1f47c2f9da7f48bdf936cf40a,0xfb278a0c594d6f5247b931cad8f7192db80f57c9a143fc4a7d15bfa261b05f973a6f60d5fc386f4b36f9d30f4820f2c81,0xf6dbca3402579f72a0b38c6591f61294703fd3150c24f1b9ad864f58a6093cfb7c4f81a4fc9d1f5a73fd2b5f80d7f26b8,0xfd9075b3ac624f960bc8253da7f5a492081f9b8650a1fd7846a21fc937bd04f7c341fc031fb274f5d2cf8d63f859afb16,0xf81db5926a0c3f17b6c42a50d3f068a912bf8d4bc270fd561a487f69415cadf9d28c73f57902f6304fa743f58b3fc1b9,0xf564c8d7190a2f03741d5a9c28f5162b7a8f70249d68f96b134d2f0dac53b4f3950bc6af81a4f3db8f1c72f5b97f3c06,0xfd287194c3650fd92475ac81b6fb26137a0f27958b30fda2539b7fa83d4bc9fd5c21a48f43a60f8690f41c6f51dbf0c7,0xfd40721539ca6f7d2058cb69a3f8431a562f7b9d814cfb0d19478fb57a0924fdb17952af4a80c16fb2c63fd5c3f8603,0xf7c609b3a58d1f3d29a7b8405cf8721c96afb0752c46f5930cb26fac834b51f2497da08fd5374a20f3681fd416f9db1,0xf5b246971d0cafd47b638c1509f81b943a2fd8bc591af3786d2c9f314857dbfc65d3027f61253c40f80b4af6a92f70a,0xf048395c16b72f0bc864917a53fa25d8b43f7da80c24f9637582df970d15b2fb3ca906dfc9b1a056fd4a6213f4c781]

def e14_12 : List Nat := [0xf1350ac97462df28b14d395c07fdb57a420f690817dafb6d83c40f3bc25160f9a21c65dfa584b291f349b7c8af8736,0xf6ad4b39278c0f3a718d56b240fa43c1d790fb507fd9b0f12dbf613dfc58bfc637f4157fac91f5a83f4968fa259fc462f280,0xf156a7830c4b9fc90271a86db5f9ad8b3524f7d2b0a5f4d58f0d95f361dfc73af264af1408fc128fc692fb706f3974fb13c,0xfc35b2684d917f2a7b460385d1f9527d6c40fc2d07931f50b1f6a41f9c02f8742f3694fbc56fa08cfb3d8f9adbf375afa18,0xf80dbc653471af24c059b138daf21c85a9d7f2c7814a6f79160a3f5ca7fb307fd251f963cfb6d5f493df2b09f8b46f8402,0xfdb847a612c05f86c42d19b3a5f60357cb49fb02ad465f7092836bf1b25fd726f340df18a4f879df1c37fa139fa08cf95c,0xf4860da75392bf7d6a2085c413f9c12db870f72815a3bf561943cbf63d8c0bfb1d9f405dfa830fac71f246cf9625f79a4,0xfac0435691d82f6c9508a3d412f9068c5247f1b2c4857fa516bd94fb931a6d5fda72f30d7f83c7f9a02fbc18fb364fb07,0xf6ad2b9431508fa1d4b60795c3fcbd375842f78a56192fa7140c82fd93647b8fd69a4c7f3025f6c12fb381f0d5bfac90,0xfcb579021d8a4f0ac85136927df8165da734f35c2a19df8062b3c7f68b03a9cfa52839b6fbd64f1b74f9504fc071f2d4,0xfd2a47b19c863fb509731d842cf8346d7251f6b9a8021fb3a04928fb26930d4fd957a60bf0785a1cf6c35f417cf5dac,0xf156430c8bd7af9ad837cb6240fc6a8274b3fa075c193f2d961350fb785d360f95b2a417f25ac49b1f84d0f1d68fc92,0xf70436a9db285fd61a8739c420fc3b814960fd7a0b468fd27915a4f26b531daf9bc25d30f12956c7bf3ac1748f05c8,0xfb9c7403d5a12fd483c17a605bfa8b36d142f9d287b13f0734bc62f564a90c2fc580b694fad861953f0d7518caf297,0xf84a5719d6cb3f8d0349526a1cf0a7d2c418bf312b9c7f05368acf96b5da3f42907bdf74b1602f51d3cf80465f2879a,0xf1c29d748a0b3f782a96c51d03f41adb958c0f4a7b18d3c9fc43902bf75683acf6d24b5af7063521fd508b64f72619,0xf4bd615028a37f638b0d4c2175f2bc304a91d5fa7b35f695bfc085f941bf8d34f2a64f9c13f8ca1f7c68f2906f72d9fd70a,0xfd2c13487b6a0f17da950b26c4f827c5a491dbf1803a24bf869caf57a1f6521f0792f3647fd406fc390fb3d9f8d53fc85b,0xf5b178d603ac2f1958cb43d07af416c7509ad2fd1c0a629f51397d4af8472afb837f2081f6b28f53bdf940bfc965f463c,0xfdb8634091a57f358a0217c96bfca2d9b41605f64d8c2b5f07824c1df93180c62f1527bfc30bf9ad5f3a6df4738f97a4,0xfa6153c09d724f28c17b3950d6f9c2da1b5736fb2a08d34fc568140bf3a85d120f925a7831f706c4fb64df9b84fc79a,0xfd421b68c3a79fac4957d60b38f0846c271db9fa187c920f5628d391f1c0734a6fbc503147fb852ad04fa5369f2d5b,0xf859c426a17b3f4b80d2a57913fd92c6b18403f14a78d65cf360cf5b93fac73f28cbfa968f4d16f7094fd527f0adbf1205,0xf196b5a80d724fc2970b1d834af4b357a90618fc4da30286f378c51a6fb958fd265f2a05fc740f9d64f3cbdf1c93f7b21,0xf2b56c0d3a781fd97052c3b468f72a1583490bf6b80a59c1fd48ca631fd693028af71bcf4a91fd29bf4062f5d73f4c57,0xf380adb152496fb2a8d795c604fd28c47a9031fd465b07c3fca419350f6d02785af9c16b75df73a1fb843f2681fcb92,0xf342569cb7a80f16ca53d2948bfc2bda463870f958d14b60f4719d6a0f79315c4dfc8621a37fb9a281c3fd5b0f2750,0xf0d6935a7481bf073c4d58261af872c59db430f06b38ac12f97d13640fc9417b50f92d3a651f86cb24adf7c8b9a25,0xf039628b7d41af8421b5709c6df3a7185640dbf38025ac7491fc0536b4a872f51c43df29a61df2b9daf68cb0f3795c,0xfca4905173d26f1c2a6b57d839f9560813cb42fda821b970c4f7bd9c863a52fa0b3587469f16d034f5d1a7cf8b204,0xf6c1d739b82a0fa52db71963c8f70b586da134f2ca46b35780fd9c516a72b4f9a3d5621bc7f183094fc0d84f59240,0xf84b693a17c20f4630a785d9c1fb0492651d3cf7b16c538da2f47319506a82f9a4c86db570f25ac0dfb97d43f18b2,0xfc8a0d5b93421f051ad6379c4bf275c690318bf9580ca3d261f29a5607483cf53b68d7a402fa287cbd146f71bf4d9,0xf12d43ac56b79fad5b8142c709f2a750c4869bfc31a8d02649fa6d1cb38725f8c63d71b4a0f35829db047f160395,0xfa8b207c1d594f29ca038d61b7f9146c2d75b3fa360d4b9782f4850c3d9a62fb69043517adf4cb0865a137f8c521,0xf3c9b875da460f37142bd85c09fca081925b7d4f8a94f36b4f0274f9d07f6a59f53b0f16cbfa1c7f6d15f2a31f2c86f82d3,0xf4209b865c317f351ca94bd706fd348a6cb5291f81640f26b1fd8c4fd596f3ad9f0b2df783bf2a58f79c2f0a7cf7305fa41,0xf319752ac4680fc347128bd659fb3a48c5d1627f3da02b6f78d90f0b96fc7d0f5140f2d49fa739f8a53fc1a6fbc24f1b58,0xfb6405c2d31a8fd57a26cb3418fad60b297c153f387b120f659a0c3fd728091f524d9caf96173f8c4a6f4bd07f9485b,0xfb95837a62c1dfa8709156cb3df06971a35b28cfd936405f681420dfa9c7b84f2ac308df275a0b1fb6134fc5294f7d4]

def e14_13 : List Nat := [0xf184205c7b9a3f74ac16809db3f25917da8364bfc96b5d40f5a03f78b0f62d0fc21bf41d3f93c4f6d8cf5728fa651f92a7,0xf5c403d691a28f159b2d073a68fa0b5d9427c38f052c64b8fcbd78f14adf3174f79caf935af0629fb657f61b3f1c02f4d8,0xfa9304d75cb12f7156d02b4ca3f9c27a058b641fd87b9631f4a1c352f86074f80b3fd943f6c81f5adbf97c0f28a6fd592,0xf8640a13c5bd7f0794a38516bcf372ac9056d14fd96c12b4f9b84c7af306a81bf53d2917f5d82639fc25ad08f20b74,0xfa17b46d2c583f948b2651dac3f61c782a904d3f7d529c43fa6b57214fb053f8130f0742f97a5fbd91fc69bf0c86fd0a8,0xf26d0a87935b4f169ac52d3708f571d906c2a38f8c720b14f0c1a5d74fa68d4fb64cfda7bf943bf5630f9215f3c91f28b,0xf3a6b90d27c41fa460c97b53d1f9ad7384bc261f50bd9287f4930ac6df25968b1f74081fc851fa5d8f63c5f2a70f243b,0xf138a49250bc7f9d4812b53c0af043db9c16582fc26d195af08b4c639fc8603b15f37daf6b7af9647f2d87f0d57f142a,0xf265a31748d90f034ad2b78c16f05b1d46c728af53b94ca1f9385c241f63c9a70bf6812afbd04fbc08fd375f697df952,0xf185726d094cbfa71c38b59d40f8da2b705639cf28a6135dfc78069a5f12c68479f641529bf0ca4bf37dbf3024fd3a1,0xfd658a2bc4970f7528d9b41a6cf1bd3a72c5968f740b61c8f29a5d136f4d73b512fac917b84f083cf3460f5390fad20,0xf2ac80d6317b4f358b91d2c6a7f3970c12b568df605da184fbd9275a0f82695c3af09cb6152f03b14fc7d4f3874fa94,0xfc7a52bd30849f8b7091d64c35fa924d8716b5cf21397568fd26a40b9fa0d73b41fad502743f06951bcf6381cf2a8c,0xf18703b56c2a9f5861ca024d39fc5d2b146a380f28a50bc9f6317c8b9f4c3726d8f1a7b4352f4751db60f90d7f4ad9,0xfc0518bd73a49f5d2bc8071643f874ca125b06dfa68304d9f5a841369f726c3d09f7b65c20af57c1b428f2ad19f93b,0xf08c342a71d59f604d7b1852caf0d8274b5139cfa0b964c5f87c6d9a4fb653d21cf97038614f3a8b2057fbda19263,0xfb129c04a58d7f820513c4b69af627081d59b3af52a190347fdb0af64d0f8c14f6371f2d94f3879fb5c2f653dfcb86fca7,0xf271db63ac804fd586129a0c74fc51a20d39b84fb25a73c14f97534a6f5649f87daf05b7f1309f83b1f6cb0fd826f9c2d,0xf8b4c09217d5af6cad42b38075f3a26db794185f602d91c7af472c50af1d37825fa95b1f0348dfb9640f6bc31f68c93,0xf2968ad15703cf4261b837d509fa5bd02874136f4a06d97bcf564819acf6b0cf859cf34b9f4d80f27a1f3a2bfd253fc17,0xfc7b4d625a139f284cb37561daf743c51206bd8fc81b5d03af7a638b29fc07d246fd359f0869f14a9fb049f850afc271,0xf4b52178a93d0f6b7351d84c29fa2b8c056d741f5d27c6819f4613a079fad436085f90bdfc1b9fac57f2830f26a4f3cb,0xfbc59736ad840fa193b472086cf26db9a058714fa318b2c94fc465d290f75b1d38cf9612a7df153cf0d43fa825f6b70,0xfa217d958046cf68c7b413a529fdb287a491630f90a183d4cfc3972d65f1c062435f8ad1b374fb8d5fb02cfb6a9f057,0xfc8307196a4d5f3615724cb80dfb29a13c04786f1c7b5346df956218adfac60bd25f4b379c28f7a2058df390af1b94,0xfb925368704a1f50248db6c371fa8b7c0d39562f4d27a9081f60b2ca31f5746a038fb5d69c43f7da5cb49fc821f91d,0xf60a285b4c13df8c30427591bdf39c7184a652bf7d16490cbfc6b805d2f43a7029df1ac53862f9a514736fa879b0d,0xf642153c8b0d9fb31607a5284dfc14a9b2d5830f75681b4392f940acb5f71d3a6bfd809736fa874c91f26c50fad7c2,0xfc25db1486097f5b2930d1c6a8f0b9c35a18d62fb6159d3a0cf6571943fb312a47fad4b827f08c42d7f05ca964f873,0xfb21594c7da36f873056a2419dfc174a935208bf27b906843df29ca1b046f6c83bd1f0a85b4df975d6fc2813fc07a5,0xf8a4b3d729651f58c16204739bf82c9a1db7053fb6ac597130f091bc78d5afa2d4c63f08b2146fd0c3486f9da7524,0xf4bc319570d2af2468a1d7c509f15206d4ca387f0a749db653f58da96140bf6279b3d5af7b80c93f34821c6f2c81b,0xf3971ad28064cfb152c68a74d0f5627d83bc14af573d6a92b40f9d184f078cf3a20f9ca0f1342f6b91fb5c7f85dbf6359,0xf5a691b7c4203f140d5ca78b93f12860c975b4dfcbd629a0583f90734a8df8c6b0f2d3bf61a3f27daf4718f5946f52c1,0xfb2d71c964350f7b924086da3cf830a2749db6cfac4d3b19065fd126a975f18b4a736fc0285fbc25f1395f8a14f8d07,0xf18da50b469c3f2a3d0c5849b6f734c8b5d2190f0351db29a86f4d6c1780fac728361fbc259741f7d93bf57a6f420a,0xf791d82cb3a40f8b4d215c7396fa81c63d9b725f8ca94261b05f90c47d65f831adb20fd57146a0f43c92a78fb5306,0xfd431c96507b8fc371940b5d68f0db624a35c79f57d16ca9208f641b938a0f82b4f7a18f2a51f2d95f36adfc274fc03b,0xfa2851bd360c4f253b74d90816f502137da94bcf1756b83ca04f246d87a1cf8a6c7034f9c86f92d1fb5d0f972bf593a,0xf87bc2165349df25a1b48c7036fb50c9a271d46fa7513c42b86fda806c593f1473b0acfa4029183f7d69fd285fd09b]

def e14_14 : List Nat := [0xfc421935a0b86fb259ac831d04fdb3096a82c15fad360584927f8d4a265b7f4716b9c3fd97cb146f3a180c57f02d7,0xf721a36485b09f7c8b2514ad60f19a783c5d4b6f7d2c6a80493fdb742681ca0fd34cb175a28f9c03bf20569f9d135,0xf0d2c613b8a57f03625b7a948cfa3d140297856f1c905da2738fb08d6435912fd71a06b4c39f47c51b9682f4dbca,0xf684d021357cbf5a62c493d718f1ca72430695bf7419d805c3bf70ad29b46c8f3a90bd16528f1a40c9736d5fb8a2,0xf14a0d2c78359fb3d84ca96125f57d931b026a8fb908156c37adf74d1f605dfc5a1f243af0463fc970fb827fb492fcb68,0xfc0d7486931a5f1804b79ac26dfa8712b3c9460f73a6c8bd4290f27530f9d25f83d5f6b15fa4c7fda28f1634fcb91fb05,0xfd2473ac691b0f52cb8d6314a0f5b94d3c08a26f7d1284035c9af1793b46f27590f06b7f29dbf85a6f51adfc781f834c,0xfbd83641ca250fa39715b6c2d4f27c9b81a6534f8613c5d92b7af73da960f87490f485a0fc4b30f591d7f8cb12f26d0,0xfbc53168ad042f6d9487a15b30f57d8b6914ca2f74d1c836a59bf72db4a0fc2971b0f93c6280f18502fc73a9fd3465,0xf17a20c34865df5a19624d7308fd359a0b64128f940d2b7516a3f6c9b183f29074acf5bda87cf506d972fb8c13f4bc,0xfca48362d059bf35a0c12468dbf8a143c57d90bf2a31d6c40785f4d56a97bf5b61f72b1f9281f9306f7ad3f2c80f7c94,0xf2d56b708c91af53a68d7140b9f384c6972b5adf362150a947cbf3781bd60f4ac1df58a7f24b8f25c0f1346f392cf9d0,0xf03714b258a9cf508d3a216479f4d207ac51869fad1c27840635f19265d0bfcb390a6f7b83cf6d9bfd75bf4a13f28c4,0xf87360b5d9ac4f1b3928d6a5c7f2d3a095618b7f3cb962150da8fc24a7531f9c80341fd7402a1fb6c0794fdb25864,0xfa21307b84c5df6b1c8a392d75f8740d69b3ca5f6a0c28179db4f38d41905f72b51a43f61d3f2495f9c7af06cbf6208,0xfb347cad15690fc8d3a25b1406f2d5039a6871cf2946358bd7a0f7b9d48a5f1a426d08f5913cf970cf2837f6b21fb4c,0xfa956c7184203fb7d2c4960531fcadb26870439fbc580a273d46f3b9d8216fc38a5291f5d097a1fd6a41f4b57fc0b8,0xf2a05d37869bcfd4859ca3602bf7429ad15c38bf72531c64a809f491b62d0f56a7d93bf14307c82fb4c0f816df175a,0xfb79251cad840fc4126a87db50fd69b173c85a2f6475d3b81a9cf7c2863a0fbc594a72f56b4d913f43902f61d0f803,0xf0db869ca3725fc8317420b9d6fb21a57d49306f41b7c58092a6f82c0a43dfb4879163f7a95bc40fa81c35dfd2651,0xf81496c03ad25f20d1a6479b5cfd9086b4a7c35f7d4cb06138a2f21c9a056fc824075af1b784395f2b8d3719f3bd6,0xf071b9c5a38d2f91c7d5b036a2f06d374b8ca95fd0a8796413cbf49da7b612f2857fb352f6815f4a1df4c08f9340fc62,0xf43b96057da1cfc84d530a2916fd079cb582631f209d3ca6b781fb2d649a71f8374156f80bdf42c0fa4b8f593af5c72,0xf4d9cb3a62071fa756042d83c1fd72a59430b61f86d0ac2539b4f9081b7c46fa478519f31297fc5d36f8adb2fb8c05,0xf9d6b05134a8cf561ca08d793bf21db837096a5f184260da759bf2c635874bf0492d5cf2864d30f41a3cf9a271fcb7,0xf94a360d5782bfc5bd31274086f5a971d20c346fdac839142507f1b48d6a7cf692a0b81fc26bf58a1f9530fc9d4f37b,0xf5b3491d260c7fb2a51369078cf4817b652039dfb8273a164059f14a80bd6cf29ad835cfa685d3cf479cfb421f0d7a,0xf4c028a6537bdf58346907c1adf1579c6842a0bf78c25914063af93174b50df61803d72f9acb8d2fc5a49b3f6b21d,0xf07c8d9651b34fa73c6d5b8209f816350c27bdafd71cb6a30852f7860b2a19f5a462139f83d0ac94fb924f75c4fd41,0xfa640db7c5819f7a8b593d26c0fa257d86143b0f605138729d4bf7356dac24f4a1c9b28f5d17963afbc49021f3c80,0xf15862bc9ad03fc697db8214a3f6b07c8a5291df871a609b5c24f618d2a743f204953b7f80c46573f50ac1b4dfd39,0xfda63c0b18495fa134708b69c5f387d162b4ca0f21c79b3a86d4f17204a9db5f75392cbf8d052f64190f37a2df6c85,0xfbc9d25a81603f6bd024978c53fa65b4d1c2809f85140ca7b26df469b057213fc3d70a4f95da173f291b83afc7486,0xf12758c4a36dbf94da152c0837fa2640319b5c7f59d2b60ac143f17b3c92486f6a8b47d39f6cb09a5fd5078f20d18,0xf4286c1a5bd03f2c7d5049a361f79b6d4a025c3fa759c0b8462dfb2a69078c4f47bca8391fb180653f729d851fd13,0xf287c503ad416fb7a91c2063d5fb6ac04812d93fb908572a1d6cf7965a0b8c3f468d071b29f24a8315f9534cfbd74,0xf1c4285a3790bf36c9512da47bf2a61387c5d9bf2c39608d4175f620d18ca94f07291a86d3f350a7db84fbc04f65b,0xfc584d72b061af3c862db5790af8024b739c15af6c78b9d3052af95d1bc07a4f47183b692cf82135640df436da91,0xf12d839b064c7f31da5042b687fd48c209a1657f41bd03529ca7f2697b581c0af4bc59f2807f5d91f36a4f3a8bf3c6d,0xfb875c260d1a4f5b20ca349681f6a213bd807c4f7a583d29cb04f7b6d5039142f53c82f9b165f736c1fd9a84fda097]

def e14_15 : List Nat := [0xf5acb63784921f7938c5da062bf3d2746a8590bfd4c965703a28f619b805243cf35bd02c1f0c714fa4b1fd681fa9d7,0xfd7c1b58492a3f1db4c596028af90c6d2b8715afb65d8c912740f8146a0d9753f624dacb3f168052c3f34a70f9b73,0xf03a59d4c286bfca048b13d529fb7836a20915cf173c0db9658af7a46c812b39f9ad805724f35b4f1c74f6d70f1d26,0xfb17083962ca5f7a2d9184b305f28b73d1c40a9f431206bc78daf856d42b9c3af0bd74168cf1a649725f6c53fd095,0xfd819024c3a56fa921c0873bd4f86ad725cb134fa7c839d150b2f703d261495bfc28a17536fca0d58b9f79604fb64,0xf4d15c26a9073f524bcad79613f5a849c0271bdf7c81a29b6405fa03856d91c4fd2b7806c3f395b0d86fa74128b3,0xf3612c0b8a94df469175203ac8f1b4356a09728f1a7b604295c3f3b26d7c1508f14739b5a2df0785df9c68dfa4cbd,0xf126ca58b94d7f92bc83615047fc3db42a81957f30a9d1c52864f0873b56a4c2fa3148d6907fb1ad539c06fb0d27,0xf6c129403d57af3507b18a9624fd793152086b4f82d90b5c3a17f3659b8da2c7f19ca583bd06fcb274f8c0a4f6d14,0xf5a6c21b39478f06b9d41357acf64b51a3d7208f2b0734ad5916fd17905283cbf18d29a0365cf96d042a8cf4c7b8,0xf15942b68d7a3f9a85d4c12073fb971a5c06483fb529d16c8740f09c281bda43f27cb419650af357b80d6acfd263,0xf9c38ad5041b7f815964c2d037f6ca0248b53d1f365c0b9a28d4fd62b391c857f06bd925a317fcb49086a127f4a7,0xfc56128b74ad3fc1360a2bd497f1527d84b693af1d6c9b587024f17305d9268cbfa957f64caf835afb043fd0c2f8190,0xfc69208d35a14f9db073a25164fa7d1b3c26504f06dac795b813fa0d21785c9b6f57b4df3684f8cb2fa938f0c19f274,0xfd4085b613c29fb1527d38c6a9fc4bda5370219f8241ac56d0b7fd50c7184a3b2f39064f7a269fb8d1cf30a86f7594,0xfa3647d2bc508fa7093c4826b5f30c87219da65f1a0d69c24b38f134db02a97c6f4068d59f8529bf14acf173df57b1,0xf37bd95ac2148f3c72d81b06a4fa25193bc807df97a031c5628bfa920c63d1758f961a350f86d47f0d5b4f2b64f9c4,0xfda28056c13b4f570d9a48c36bf51930c27d86af3461785c902df49537ca81260fa741b83f796d52bfdb0a1f924cb,0xf5bd0a287931cf37a81492d6c0f6a358c91b420fb27159ad4c38f169d3bca4752f7c26480f5d86340f5a1d7b6fb90,0xfb70c9126da43fb20d579481acf4db51692a780f95827d1c4b6af1b8c5609d247fb937c250f530af86c3f1463fd8a3,0xf24950d16b38cf47b09d86a21cf587139ad2b46f5d348a1b9207f19730a4db528f27a51406fca369f7d6cf08bcf53c,0xf38614b0597daf70c31d8b246af1c84d372096bf718049d635cbf782d519306c4fc9b34a52f65bd0a2f857caf129a,0xf241ca7d85930f849bc5736da1fd5b4a60c3829f356b8c472a0df52d46c7b3a80f0431b269fbd15a970f2c91f6871,0xf2d7cb9064815f031b24da8695f394120a7bd8cf29a3716d04b8f072c9d1a436bfa26c1975fd380ca65f74c58fb35,0xf34d59b7c281af94c60b58372af8479d6bc135af7d8b30462915f178c36902db4f056ac93df07ad125cf42b1680a,0xf8c6357b4219af6d209b3c4a58f73849d061bc2fd81a26b5c703f0a64d782951cf7408bd569fa39cf7ad1f250bf143,0xfa6834db59c07fd819263a0b47f3b9a24851d6cf694a52d308b1f93502b64c8adf56041287cfc2731facb71f90d57,0xfcb8304215d69fb7261da5c084f319a8d06b52cf87a209bd356cfa1b05829d736fd2b3a07c4f4397186f5947fac14,0xf472630d9c1b8f65294d371a08f1502b4a6c793f2461da9075bcf0c412a596d7bf7a3406bd8f19b3ca8fd28c5f538,0xf60db471952c8f1ca90534d826f2a8140b75d39fd15c3b807249f30c485b21ad7fd20a38796f31b9c7a6f4a56fc6b,0xfc850734b2691fcbd4a5720639f42ac0d783b56f0a3c5d148b79f4c7a8d3521b0f5186c2da9fd9280316f749b6a1,0xfdac297508413f9a18270c4d53f8a7d25c94603f658c74a20b19f6c178d0a5b42fa6bd159043f12b36f68b9df7bc3,0xf15ad2b64387cf25b1d039684cf8b47d95602acf1926357bd8a4f3d6a9721850bf5d4280716cf37a049cf09bcfa31,0xf6d9c408753b1f3a0c814265b9f7db836ac2519f7120d4bc685afb05c1372d846f5d1a82b709f34a2960fad3c749,0xfda08b9c72634f568d97b2a1c0fa6b40d713c58f1d207596ca38f73bc425d619af7493db5128f9035a48c2f1460b,0xf4b693d8c571af9c435a2607dbf59a3c164027bf7c6849215d03f2c058197a6d4f25631dacb8f741b2d90a8f083b,0xf9c15a783b24df561d7c8493a2f36a4cb17028df8b912ca05346f9a81472603c5fa1375b40c6dfdb692f085df97b0,0xf638b47d921c0f948cad3b5720f7861a534c9b0f6bd4258a713cf1b793a28d564f815962bc730fd2c50fa91d6f0a4,0xf40d8273a5b91f79a8c216035df9c7852a46b1df0924c3817a65f9470862bca13f6348bda0c59f6c157b4dfb02d3,0xfb0da38241597fa5c6db480319fc120439d578af0c4718b3526af64d85073c2b1fcb563d72a49f68c7a1d29fb609]

def e14_16 : List Nat := [0xf0964c1a3875bf79168d3c524bf15a49c6027dbfa9534170c2d6f0d581392ac74f7ad9b280563f4d126b30a8fcb8,0xfc4706ad93582f71a0d842b9c3f7836ca51b02df86d4b72a9130f4a8bd5c16290f3bc81256497af57c0f43d1f96b5,0xf9a2d1657b403fac9b12487063f7d962c180a43fb6c8274da590f291468a7cbd0f71a6d8b25c49fc05d3f5831fb35,0xfd3465a2071b9f780a9361d425fda82730bc415f86ac12d047b5fc7a318db4960f84a197d62b3cf6b8359cf905c2,0xf0b7c19462a3dfb97d852036c4fbc2907518a6df50ca12b6839df96048b5a713cf80a9561b3427f735c82d4f41da,0xf7c0b863425daf9064a8372db5fa047d1629c53f570284c1b96af8794d3cb2150fa17b30d658c2f14b6ca9d8f139,0xf50281cb7d4a6f07ad2b39684cf31d95a06b478f34152a97c6d0f375b09162c8dfb129408a3c5dfb9ca17246358,0xfc0b62a39d5874f2904fac94f1c84fd364f503cf7a53f1d83f2d6cf75bcf2065f1695fa186f0da8f72bdf970afb917f1b82fb43,0xf719d40653a82cfac9b1fd3bc1f6293cf0a25cf6149afd695af78b09f5b431f2db64f80721f0d7b2f36857f5038df84cf74a,0xf37195d6bc4a80f29a538f81206f7a058fb3948fc63d8f4d2a3fc5613fbda15fc746af26975f2b09cf1b40cf7d142fb9d07,0xfc6249db38a051f56147d8fb286f3046fa906f92d6f3784fcad4fb5a4f135df0c3df91a3f702afb180f7521fc7b8fc59bf72c9,0xf4b205c7138d6af82a0c1bf962c3a1f81495dafc857d29f7093468fa9b615f79dbcaf2480d1f356c4df730b52f047b36,0xf7ca2b1d506349fa3b874c9f3cb9fd469f5c09f8d2cf1a6cf6142f5731f8271f0b52f0db4f6d7bfa584f8356f0ad3f8a70f219,0xf4a30c271b685dfac7d8215f0931dfb563df97a6df8061af9c50afb4920f42570fb8c62f34695fb7819f4cb38f3741cf2da,0xf9b2a35d48170cfb7d28065fbc130d6f85c6f4c26f9416fa936f873cfa57cf2905f1d95f7219f40a7fb8a1fb420f3bd8f34ad,0xfca27b043916d8f82b59da1f179c3a8bf5078f4968f2c09fa6b9f64a0f5c7afd120f5247f35d7fd362fc156f4b31fd4cbf038,0xf34d021a86c59bf5870a2c1f3842d6bcfc4b19f7408cfa730cf9a614f605a4fb2790fd813afbd928fd5b71f35269fd7563,0xf7a685d93cb241fd2a48c6bfa94c2638f04d318bf078df0528f196df7cadf1b46f3b74f5c06f921cf53a1f095af975bf0273,0xf164852db037caf7514083af0d97bc5af2c4d5b8af68dafb174f3b24f6c9bf028cf1d78f0927f653df193cf2631f0596fa94,0xf21640d3bc97a5fc378b1a4fb07d6934fa95c8603f3502d41f8a63f7584f2b94f8d90f1829fc2a0f6c72fd1caf5b71f65db,0xf790621b5c3a4df6a513824fc695da14f78c056d1f39d2a816fbd04f8b94fca91f358df2bc9f7c25f027af07b3f680bf734,0xfdb873c25a0419f34d0cb29f536217c9fd6c18a72fa157b082fac48d79fb961f0249f3ad1f5b3df568cf0583f6470fb4a6,0xf8c57b2d41a963fa3d68025f6b8130d5f43c60b58f091b4735f2ad87049f9cb3f1795f7c1df26a8fc4a0f4216fca72f9db,0xfa391c562bd847f7c05346bf83c9b0a6fc492d306fa9d7158cf0d5972a8fad69075f1b36f1873f24bcf528bf4120f4d1a,0xf0b537816c249af59126d3afb3c7d029f72514809fd8ac0471fc4d57b28fa2dbc507f96adfc139f8603fb856fa4b1f463,0xf61592a784b0c3f0a42d813f526cb1d3f74c5d682fc941a602fca8bd091f5ad46b70fd712b39f3a97f8043f57c8fb965,0xf937240d58c61bf3475a81cf0592db4cf3d1a26b5f6d809415f384da60bf69d703a4f87a02136fc7bf52cfa9cf82bf791,0xf8c7d21b9350a4fca165d80f475963d0f194c68a5f8bd972c5f287341c9f1da264b7f4d6a3cb2f6b30f25b0f9a70f381,0xf42a03d1c9b658f62134ac8fa94072c3fd920b41af5c6d71b2f7350964cfd0639574fa5db7916f15bc08f28df7a8f3b8,0xfc09127a64b853f349da081f257836d0f5b168a3df951c8403f1db9605af7d2a9cb0f2b65c479f2ca4d8f417c62f7b3,0xf7469c3a20b8d5f5638c219f70d435c1f8526b4a1f03786cb5f0c72b3d6fda84097bfa08249d7fd29ac41f6a51fb931,0xf3b582a461d0c7f48b0963df243807bdf9c5a306df21ca9b40f6bc291a8f7139526af156c472bf53c81497fda05f78d,0xf94d786b3c25a0f59120bd6f71c5b260f80437a61f475da831fa9b4c051f92853a46f8ca2d97bf248d39c7fd036cb1,0xf351db864a29c0f0d8721cb9f5da6b082fb794d602f507438c6f7a841b3df37ca1859fb5713a04f62c5a91fd24c369,0xfc60bd4a857319f5396dac8bfb63802d1f2a9b47d8f5129703df0487a59df417c56a3f18642c0af261c4905fc3bf72b,0xfa96b27531c0d8fa3795b140fc87db349fd5162c74fa5c380b4f28b9dac4f20586d39f71d2a630fcb7a1256f190648,0xfb08d294157a63f5b96483adf12c397db8f406b7c19df4bc9a0713f03d1a82f786d053fc61b258f265ca47f42a590c,0xf27351a4c86b90f3a2c5047bf8a941b2d5f8da03964bf870d91624f92813d6a7f0b59cf1d43cfd7cbf65acf2175f3806,0xf05a8d46921bc7f93bd2c061fb9a780d65fb483d9027fc6258b049fb630a4c82f597431cf86ad751fd53a241f371ac,0xf1c706adb38529fb8c5d13a0f6d415b93cf86357d2a1f69a873d05f308d97264f617a594bf482bcf7421bfc209fa40c]

def e14_17 : List Nat := [0xf6d5290b3c4a78f7b956a834f027d81bc6f5ca0d312bfd1c7085a2f9140573adf24b8c036f1a9c2846fd496bf93517,0xf4bc1d27390568f187c4db92fa25c6d3b1f3ca9d7b61f03695b82cf8a351479cf75d083491f0642bf0a62fa704fad85,0xfc43d817b905a2fc142d608af51bd7a048f6375d02bcf1a3b49652f39a4d16b5fd9130746af3c978f5927cfb0c8f826,0xf6072d943a158bfc75b46d82f937bc5a42f31697d40bfad536874cf038a2591dfc650a7148f9c0812bf1c3dbf9026a,0xf4c531690d2b8af58143a7dbf64283791af0ca51d478f057b6da94f0b3d9c126fb952c3071fd56cb48fc729368f02a,0xf4952bda170638f2acb58d37f86b9312c7f509a82d1cfd561804a7fa69d42035fa0d6291b3f0c97514bf74c8bf643c,0xfc3ad6129b0758fb40d38251f7cb649a53f478a2c963f0a172d568fdb5c06a48f7b24d91caf9026c41d7f3b81f9503,0xfb3057a691428dfac684d251f8ad60b735fc470a29b5f3c0972b4af871cb6340f21839c7d0f1b8c2649df5613df9a5,0xfbd469a021c853f7ac61d259fa3748b651f7d34260b1f82c9b7041f27c086a4bf94c5ad830f5d6392a87f0d913cb5,0xf692d0c71b4a35fd7a93061c5fc9518fbd375f241a5f20b91fdac31f6d94cf8364df407b3f82a6bf8790af72684f058f2bc,0xf6a091435d8b2cfc42d9a3b70f3084bdf9460bf1a8cbf5716bfda204f79ca4f5687af596d0f1c37df25136f7285cf39218,0xf61a4b03879c2df5093a81b7cf735d849af624d3f6ac34f068c4f9d0c6f582b6fb521cfbda08f159b3f927d1f2a570f174,0xf425d807a6b1c3f48b93d12c0fb3718c90fac578314f69a03f59d60f27bd0f564cbf2d74bfa194df26c79f5a861f582a3,0xf31b2c406859d7f70da963b52f74b83ac05f1c7a02435f87bd3092af97146280bf948d216c3fa4d5fcb65f1d6af9c81,0xf759613a4c280df971ad3520bf86a509d41fb3047c8d5f7bc6248a0f72d1c56b8fca2158360f3c91bd64f92b4f39a7,0xf9152a6d438c7bf2d0a79c64bf9508421b6f81a56203bf8d9274135fc168a3704fca93d1782fc360bd75fc094ad5b,0xfa1b587c9604d3f63bd0795acf42a6d9153f720c48613f5d1cb8290fb62c57a49fd7412b08afd817b4652f9a03f8c3,0xf0c2b3a578694df9c6b834027f50bc1ad28fa061d5248f9d317b4a2fc7356a908f3c4159bd6fac5b19307f18d7462,0xfa534c0291d687f31279d0b6afc6593d7b1afa8169f40371f05836fb48c3fcbd57f2809cf4da07f25b8df4a2b9f5c1f426,0xf9d02b7438a61cf79042815acf4d529a178cf591d3cf0ad6cfb572cf3bd7af8b12df30641f4962af39b07f6584bf63508,0xf4960c372bd5a8f9b17082635fda0b614c57f47ac1852f6a978fd92c6f43156f8d19cf305b8f3b409fa3d21f0d4a2fbc7,0xf5c9d361a8b042fb53c4a9217f65d2b93814f582c6a37fb68c0951fd4807f31c74f91d87fad027f605a2f03bcafd694b,0xf2408d37ac516bf475d6829cbfa972d18c05f206a384195f3569bf1307bfa2178fc1ad7f9d4a0f643c2f6394cf85bfd0b,0xf9684d30c71a52f72460a3c19f81375bd04cf1d74a28056f1b2c95fd6ca9fb635cf87ad5f8d26afb3907fb8349fb4120,0xf1dac93b720864f7a94381b6dfc05612479bf58a0713c2bf29d5c78f51c6a37fd2604c8fa196352f3d4a590f4b8f0db,0xf16d82b594ac07f3d7c268a04f6b79da3125f15a72963bdfb81c930f753c648f5d09bc8f6a14c50fb19a2d4f473802,0xf8b1720653c94df0cb96a742dfc7b0934a21fb5a9264803fd3ac2815fb41adf9507df38791f58637fc52b6fa8c40f61d,0xf8d397c041526afb90d4c85a3f71b5cad283f7a2c94bd68f13cb074af8b206534fa9630f81950f275d9f61d7bfc1246,0xfda2b791865c30f61c74a9d50f75849c63a0f9253d78bc0f4317ac26dbf4c820fb5a80f1b695fd2738f1246af3b9f14d,0xf0a3961c7584dbf8c2d715a6bf37405da281fc09425387bfa43d02795cfb46291fb21d9fa9c41f3c65bf08d63fa7068,0xf062973a84b15df5c146d3902fb6c349a1d7fc8619b0ad4fcb5318d96afc705a42f58b3047f380c956fa782f2bdf172,0xfca31bd0528479fb406c78a93f2b6d51730cf5bc4127d83f20b857a1d4f192d346f081c369f5c86ad9fb70a49f5a26,0xfd485a6172bc30fb931a2d746fc8b379d125f9243a87c15fa9c283db14fd802635fb4ca750fad65b70f49186c0f960,0xf968b30d427ca5f219b5c6a08fc4136029a8fc1a4625d93fa2c04bd653f16b09478f48573f1d705f7b2daf9cb17fd38,0xf705c483d1a692f62578b419df20b1374a5df3bc9421806f3a7c82b904fbd0c3956fc15b79a2f7d861fac64df530a8,0xf6493d7b028c15f53ad81b607f86d92a0c4bf85c736a904f719526c308f9c21a4dbf5a83472df3bca7961fd142b50,0xf138d94b5c6a07fa21c953b87f364cad0b97f4a391b6057fa5d1684309fcbd658a140fc82b7f4d3c2f08152fd72f692,0xf047c92b5d681af3db7a5946cf58736a41bcf538b912607fd4b3169052f439d156b08fc42a30f179acf8d72cf820da,0xf697bd40a1853cf05627d34bcfa6b52d0937f2a5d860b14f63b82159adf2038a4619bf2ca31d9f571cf0847f4c9f87c,0xf913ac48b062d5f216873405cf742809b63cf51b79da038f2b465a18d0f5b396d14a2fcbd3571f94d70cf8a6cfa927]

def e14_18 : List Nat := [0xf41d279cb658a0f6a217db350f8d369b1c20fc47391a5d0fc529d684b7f283a94615bfb87ac30f24318c6f7095fd4a,0xf134d5097a26c8fb41a5c3928fdb3a952048fc75b61d94af1bc47063d2f9c17d6530bfad0c278f85196a0f37b2468,0xf729a4180db65cfc1d25a8b43f69512b038cf586a3d791bfd537824609f62ad840713f74d61a05f493bcf9b7acf02c,0xf09bc278a36d15f68425c371af0c8b592da4fdb3807a265fd8216930b7fd319ac6b20fd975a064f5347c18f9c4fb14,0xf215b6d9c38a74f8d4cb072a1fb20935dac1fd7804925a3f2c846059bdfc0a4b75826f0d17c563f9a68b31f697341,0xf1468cb3d59a27fd6318504a7f08d915b247f2d1a0b83c5f4db62903a8fb43960dac1f735612c9f02875a6cfc7b94,0xf4d85c6b2091a7f051c7b492dfb83a41795dfbc031826a9f64c8075b39f8a56042c37f34861b0a25fd9caf127df36d,0xf3dac8657b9041f7db0583691fa4726b59d1fa5370c2946fd6082a34c5f0a79c3b8d2fd4bc78a930f24815fb12fc61,0xf84a9c372db506f097b3461a2f52ca308b96fd785a0b126fc8d074192bfc17a835d40f4c7593d182fb49da6f6c513,0xfd695b81743a20fdb6a082c73f4d831c9a70f4b36519da8f24c5039b7df41a526cb09fa461b2753cf5d12978f60c8,0xf608251ac7b349f7392b6d504f78c362d1b9fc075b4a819f683d4c27a5f0db85c16a3fcb0217d846f53142a09fad9,0xf173809bc524d6f8470392adb6fc346fa563f27a6f9506f1b53fd8b3f0a4bf2d7bf1975f81d5f0c9df2c40f1a94fc78af21c8,0xf46cb28d903751f69431708c5bf06274fb97c4fa58b7fd2487fa21d4f3a618fa0568fd0b36fc3520f9a1c2fd391bf9cad5,0xf917da83b205c6f9b6a75d4213f4b1ca0d3f0356f8c36f72a3f4926fd816fa9d1fb52df87c2f415af9085fcb79f0c47f40b8,0xf25349c7ad0b68f24db791a380f1706c8b2fd3c46578fd137f4a27f95d2f639dfc162fbc03fa096fa5b9f184bf1504fca85,0xf6b9d41275c03afc17b0965d24f5b3608c2f97d68502fb8ac9462f1bc6f387cfa182f43d8f40dbfa470f35a7f1593fa91d,0xf4a5db09286371fc069b7d438af81620a9df2704c3daf19cb2d03f512c748bf1b6af357af94b3fc6d1f5246f508cf5879,0xf831b49605ca27f6a90c342815fd58bc216f9147035bf93d7a025f7c92d1a5f71c4d8a3f63b2fbd97f846cf04adf0b68,0xf4736d290b81acf9a40865213cf4b975a06f3d859170fd48a7b20fd93b6a27f3ad51428f69435bd1f7c8f26cf50cfb1c,0xf6574b081ca93df4d52c790a68f3b6149d8f0c8517adf27bc431df203691a8f421b9c60f2b5c3a46f87dbf3507f92a5,0xf2a5b0c94378d1fca4d31906b2f8a3964b1fc3520841fc5d7b826fc79b3058f4729adbcf240a759dfd071a6f516f863,0xf92a8bd30751c6f0b1728c39d6f16a4c208f5c97b312fad785b91fd59436b2f483a9056f40a537cbf8d1426fca74d0,0xfac43081792b5df84a391c2d65fb8a0624df3614728df0c86a51df31b05c78f3c9b7a25f0946cb37f96b4021af57d9,0xfb06a593c47d12f3b82571a0d4f1c0273684f8acbd640f5d96c830fb78da426fc91653a7f15b9a2d3f581b492cf907,0xfd65ac97281340fbc57da48096fb852a936c0fc3a07f47a8cf1786afbd837f15d2cfb2053f64d30f914b5f9d124f1629b,0xf3d19b8c65a047f26d5c4187a9f961c72b4a3f6a80c2497bf07da2f53b17fcb51af38d9cf052dbf06859f4630df82134,0xf56db83419a72cf368c4d75921fb7ca069351fa81c6403b5f028d9b4a37f1625df09785fa2471f0c948fd2b6afd0bc3,0xf3a269c784b0d1f68c2bd37514fda590cb124f8a1729405dfb607d91835fac16397b80f6582df03c52f47a6cf3b9a4,0xfb596a7304d82cf3687524b1acfd0c465a381f207bda4931f80a9d6b274fd3b8a26097f92d517cf0b91435f5c8f16c,0xf21cbda7438056f8420619375bf9d25ac0786f1d092b7c85f72a0b3d4c9f17d82c304af5d64b13f8a6b941fc59a36,0xf2978cb305614af742c59db80af136285d4c9fb20c6d7349f704b521a3cf648ac157b0f1b6835ad27f3d09f96afd18,0xf2c1b809ad5634fb913a5706d2f6b0a1283d4f78c05bd962f37bc5841d0f3c617d8a4bf5186ac4793f9c7a2f59402,0xfca7b408d93126f3c186b2094af85c71d369af1478b95306fd2c9705b1af5d4c837291f0d752843bcfa56db0f42a6,0xfa290584b3d7c6fc91786b52d4f41c5369ad0f27bca308d1fbd97062c81f74a0b28395f9b8a73c024f31a5d64f651,0xfa24d7165c09b8f731580d6a9cfa029183dbcf530b4c82d9f6b793a41c2f47a52b3c69f605d127843f75b1ad8640,0xfcbd5216a90743f1b738a2d0c5f591362784a0f46c1803bf68b5ac40f97da356bf7a1d4285f7c8d3941f20bf9d6fc29,0xf8b6a352d1974cf2a564b7380cf3d69204875cf627095bcf14a850d7f3124d860f1ad93b28f5db94361fa9c1b0f7ca,0xfd3709a5b81264f6a7243915c0f417c92d563af9578d02b4f0584c61bfadb69740f3ca86d9bfc2831d7bfc1a25308,0xf15c79264a0db8f2b58d14036cf83cb9471650fd2a7069c435fc13d7520fa127b395f9a3784b1fd90b6824fa8cf6da,0xf180c74b39da65f3d685b2c49af3026bd7a148f7506431ca28f12904d8bfa0b95d24f19c5370dfa8c61725f7bc369]

def e14_19 : List Nat := [0xfa70d829c314b5fd9a18730c25f90a6bd4c715f34961c802dafb127938406cfb2a850f75368bf64ac5f6d742fb91d3,0xf90dbc51826a37f1d24a8563b7fb29416dac08f9d3520b6c1afb469312c8d5fc4860a57f83c95047f034d7f2a7f91b,0xf6d94ca852b031fa17c8d05964f43a790c651df5b683c1207dfb75c92a6081f2cb3da04f28b9a536fbd2784f19374,0xf25a3db4781c90f830b697c512fc04637a95b2fd506c842a17f4d6580acb39f7b9162d0fd1435729fb8da4c31fa86,0xfd59bc173a0624fbd2079386c4f7d136b2905cf21ad0c3b875fb72a803d691f7a9c285614fb046a5f9d8ca4f35184,0xf6c4d350a7b821f9dac3680274fbc243871560fd5a148c0926fb58193a2d04fd130752b6a8fa964fb37dfc795f9b1c,0xf74b09da61c385f5a0263197cbf8405692ca17fa864c952d07fa4d1280c539fa306c8d5142fd349bf6d73bf18bf27b,0xf71829a6c0d43bfa5b8361d2c4f85731ca0b24fc7a8026591bf8703c52ad96f21a3509c8d7fbd3974f06b94f15d64,0xf637c49d12a8b0f1b7d3846529fb4d8750c269f4180db5c6a7f6bc8204315df6853b24a071f03c1a9fd2793af59ca,0xf63728da04b1c5f9c260db71a5f18bca9642d5f8097c6d412af6139b0c874af94386b207d1f84c3d925f05b3fa753,0xfa6531c084bd92f6c820a573b9f47d3618b259f87219ad40b6f5b7143c90d8f50793a4cb1dfd2ca8306f5c7a1f462,0xf468c293b07a51fc317d695b8afad02b487563f52a0974c1d8f9a16053427cf9db7304a621fc5d381b6f94d280cb,0xf04d2738c1a956f3a250c718d6f9b07d5c3416fa82b753d94cf920847a5b13fda09785124bf8b30d19c26fbc6f4a6,0xf04195263c87dafbd4ca350728f12d69385a4bf37cb61a8024f6c0b9751d84f56a71c9d03bf13d5c29068f9a2b74,0xfb9a7138d6425cf8c607593da4f3650281b7d4f0d962b3ac74fc15a0872db4f612c9035b8af973c0b685d1f92a14,0xfa9c04b73d1865f34978c1a20b5fc5d2f7152f9d85fc4d7fa847fa314f6924fb391f08b9f3628fca03f60daf6b21fbd6cf075,0xf728db519a46c0fd5978b3ca620f2c18604f3908fad30f56b0f92d6f1a36f4713f7a53f852af49c8fb412fd7c4fb75cf1b9d,0xf1b9d3ca247506f135d7a9086b4f04a528dfc630791f64c5b02fa3bc856fa8349c0fad2951f2784d1f6937bdfc2b817,0xfb8a34d79c6021f3947cb250a61fd8653b71fa5c1f9641fd095f70b5f2da7f8c37f4a9bf63dbf24caf8403f29d6f82c0f851,0xf31b5d287a60c9f0bd364c85219fbc1d0359f2075a3cf97caf615cf6805f42a0f6d92f73b2f4183f4b69f8d7bf48adf71a4,0xfa8b2947d15603f028c37b46195f69d3b57cf80417a63f435cf9c13fa12cf86b1fd09bf25d6fa970f84a5f2d87fad42f0bc,0xfb34a72d950c16f257c638b0a14f48079b26f73d49a21f913a602f5396fd186fc309fdb40fca82fc874f51bcfd5b7fa58d,0xf4ad97082bc561fac0d857b4963f50391d6af6c4371a0f24d7a8b1fb5d3f8153f2095f46b0f29bdf8c74f7268fa2c9fc13,0xf70341a9c865dbf971b42c6d083f12b059d3fc5820a63f47261dacfb3a8d75fc09bf648bf7c18f2a4df9406f5a73f2915,0xf3b9786a20c5d1f2b03d8c647a9f609c427df5693408af738b612cf26357b18fda19f4a0dfb52df5849f7150f1cb4f3ca,0xf56349721cadb0f06473d852b9cf04c861d7fa1bc6287f29a80d5cfb6930248fa3817b4f53c7f513bfa590fd6a2fd914,0xf64b1a9027358cf9712c40b8d56fd62a8741f5b928361fda07c524fd75a3cb2f7bd059cafc081f4a68fb306fd943f391,0xf14c269bd7835af4d65c3791820fa4b58d90f08cb7495f306c172bf2a3d5164f257c931df129a70bf6a8bf4368fdac0,0xf7483bd6a12c90f9a30c7d514b2f8720a431f6b1d3942f5968b0d2fc3564d9bf1c506379f716c4085fb5a7fd82afc8a,0xf6412c80b7d539f6da8315247c0f5849d2a0f6b19287af40db3c9afb5630279fbc4d8162f68b43d1cfca17095f375a,0xf1a968c3bd4025fd30b49c62185fa659bc24f3928d7a5f06d137c5f1478a0d9f0846b179fc43ad270f38b2ac16f75b,0xf907468cad3b15fa48539cbd627fd178029a5f40a13796cf38b942a60f34b2d918afd7b63c214fb0c75f28d05f1c56,0xf40872a6db91c3f2b137c5ad486fca38d7096f518c492d3f5b824a716f579d021a8fc25d147b0f59cb630fb460a93,0xfc1824d60b9a53fc625bd83a470f1730d58a2fb78631502f48c592da0f4c75619d3f796b41ac2fbc946a7d1f908b3,0xf028491da3756bf3c960425817bf1395a26d4bf09216acbdf5c6478a9bf7a4c083d9f341507c86fc27d530a1f2b8d,0xf1c3d257b694a8f62c7841305bdfb1972a0d538fd8c9f73adf421df5a71f0b47f6ca1f936af4cb3f0864f5c06f902bf8295,0xfacb068394217df9a8056c374b1fb95a728c41dfb69c0358fd815fa2c1f3d61f7b5cf2975f0487f263bf43a6f09d2fa0d4,0xfb2c9a84635071fb69d3042a587fa18625db390f831d7592fc8b51973fc065fd208f1c72f4a61fcad6f4cb9f47a3f0b4d,0xf074a38c562b9df6c0a51928b3dfc302495b6a7f17bca8d2f573169adf25064c97fd487f14bdf8536fc1a2f9043f081b,0xfa31526d487cb9f70c1b392a564fa6143c27d08fd8c6305bf712d538bfc40ad375f4a1d9602f90b4f286bf9185f97ac]

def e14_20 : List Nat := [0xf35ca8169472bdf83651a0bc92df934c0628b5afd7b4a305f71d48c25f12a79b3cfd0241b6af6407319df8095f6c78,0xf0841a5bc9372dfc6a2078b1594f813b065247df62c04ad1f9d64b712f35869bd4fc5d3a091f79ac8305fc7a82b63,0xf9a138b460d527f48037bca26d9fc021953ad47fbd8a75c3429f7041b36c82df150b2c4a687fa5690fc1d39f6185b,0xf05821743a69cbf30a572d8b941f681c73520dbf5924ca87d16f2c809a7b5d6f519da2b483cf0793b1a46cf4d360,0xfd73814b9c250af7bd3021a6c85f6349d1b2a70f4c3a8d695b0f28bca97164df3915a42786bf1356290847cf5d0c,0xf7b368c0a124d5f691382047cb5f0871c64a3d25f9d85f39a5fc415f6a81fb948fb6d1f2706fb034fda2bf97d0f3ca7f92c,0xf0d216a5b9487cf1c9608ad72b4fd1b70a2c3864f8b34a95f4c57f3715f63d5f0425f93a7f0913fb620f8d92fc81afd6cb,0xfb5871d203a46cf284b31ca65d7fc4d35a0b1862f38b29d6fa790c8df16043c9fa25c739f8a12470fd0596bf4157b9,0xf26931c4b5ad08f97a0248c53d1fdb9c2781a405f752d6cb1f5641f6a21f90b2f8a95f730cfd749fb607f8b36fd834f3ca,0xf394d5c08a27b1fa9c128370db6f3b02578ca416fd95864b2f09b81d6f5196fc426fc35bfa305f792cfa740f7da1f3d84,0xf9a74b1605d8c3f0a485b2d96c7f25c0d38b6a19f375ac186fda359cb7f1497f208af6d15f4c26f03b9f4312f04dbf278,0xf21836c5b094a7f8b46ac31579df392a84c05617f1bc82069f043b6258f59c786df074dfb2d7fa9bdf1a3df42c1f0a53,0xf5082d37a6c419fcb04d16279a3f09c7b1a5d843f6d70a213f42968c17f52064a81f8753fdb49fc0daf5b2cf6b85f3b9,0xf4bd753180a96cf41d6a38507c2fa8c174930b5df156bc092fd82b3460f19d3c526f372a486fd402f95acf7b1af978b,0xfc9d468217b503fb15804a36279f48ca70913db2f187d20b6fa60d8392f56da94b3fcb8a5d14f52c7fc1a0fc596f437,0xfd8a71c304b629f48b093561d72fb7c9a6802513f95c6db21f874a50c2fad4185bcf75d0a1b9f0738c46fd3a2f3496,0xf17a5d0bc93648f853d92c1a04bf94a627d130c5f8d2b1573f9ac7825bf6502a3c8f09614da8f219706c4f3b74f6db,0xf309cbd47a5621f4058ac73b2d1fd5c4a369b078fc0a29461f7b520819f593c8271f483da6c2fb60d7534f9d68b1a,0xf8a317942c6b05f539026adbc81f807d5b912ac3fc0d86437a95fd652f74a5f160af4b30fd963f4c1dfb841f7b28f7c92,0xfd90752683cb14f58db940c21a6f79502b81da34fd28c615a730fc5369a24f0a46f80b4fc78afd7b6f9172f3d5bf9c13,0xfd72160594c8a3fd24715a0c3b9f6a4830d1c92bf9634db782a1f09a731b4f5d8b0793fcb57f6cadf8641f5c26f5802,0xf08d6c9147b35af2184b503d9a7f409b68375c1afbc4d0295178f2643c7d5fb2c07961fb063942df8ca2f658af31da,0xfa6134c8207b9df59ac041d6873f42a517c3b608f8a7d036c91bfbc12583dfd2790a18f5c293a4df50b26947f65b4,0xf628ac0d1435b9f064db2a18597fc24a0836b7d5fb3c8d947521fa3784bc6509f4c7ad3168b0fc9302d6a51f2917,0xf534d786bc9120fca629bd83041fc39da18247b5fa372d580c69f1752a0b463df9513b8a4c70f1b2c8497a56f06d,0xf52408c61d7b3af56ad0c973841fb47ac1306859f07c36218d94af3509f6b19f871af2cb8f5d4cf2b57fd346f2db0f29a,0xf285a7c69340b1f8d3642b79ac1f61a2c873b95df527068bc3a41f35c0d71f291df4c9dfb6adf0849fa038fb574f0265,0xfc9d4b30a17582f25c06143a8b9f740bd8c359a2f4836c1b2d07af687dacbf5b7946af39124c7f1d56208fd690513,0xf250a6139dbc48f04b65d3719a8fc12b07594368fb14d6097ca35f15c62038f58dafc9b3f2d0cfa7d1f2a47f6429fb78,0xf27d913856b4acf73bd8c0a2641fd24051b879a3f47b06a82935dfa12b96c7f430da5cf361cf95bcf86d1f0752f4809,0xf9d7851cb4a263f7b3ca8290614fb1d534c70a96fd6c9127a5b83fa642c813f9568da17f5037f20c5fb049f80d4fd2b,0xf9d6183a02cb47fb1d094c7a852f3b05d86a9214f8b630c951ad2f875c62a4f5b917246f31c8069fd704f3db7f5ac3,0xf18c7a5b6d9042f039c2a48b156f7d580a316492f91d43c6a8705fcb968375fb74c1ad3fb0ca9714f5362fbd02f8d2,0xfb60a3c827419df371c9625b8adf3bc0865a1249f35187b02ac46fb4d057a9f7c6d8409f16a4307df2b1385cf592d,0xfc573d4b08621af390248cb7a65f97406c15da2bfa9461d27c385f30d925b6f918bd705fc28714a0f3a8d69c4f13b,0xfd4c30287b69a1f1c83b560d749f504b937c2a81f24168d95ac07f346d58b2971fa357f0a48fd36afcb09f625cfbd21,0xf6921c384a05dbf13ad8609427bf7c2d463b8591f6ac430782b51fc9b0d375a18f479356d1fa7d9f02a8fc04bf5c62,0xf4918a273b6d5cf52dac30748b1fa6579c0834d1fbc8d7a504639f4bd095317c2f4a92b061f869d3a02fc621fb587,0xfd7a046c8b9251f028574961b3cf2b50dac93681f9708d42cb6a1f3726d5a90b4fa87135c4f483db7c1f30659d2a,0xf204653ad9b1c8fc783d41625b0f5a60d2137948f15092ac34bd8f7b30a869c42f9a4708bc63fd7a195c2b6f571d]

def e14_21 : List Nat := [0xfd43b917a620c5f1a2d356079c8f7cb214086d95fa49250d1b638fb724c390ad8f130bd7469acfa3782c615f4b58,0xf970ca6b835d14f64213cb5a7d0f751c628da934f6d37c581b029f809b71652c4f872db30591afb2a368c9d4fa40,0xfb1a6c284d5903f72b8dac49350fc7342a9d16b0fa5c864179bd0f6d7a3129cb40f0852f183cf62d3fa874f1965f57b,0xfa6b3d081924c5f1b48a79c2605f720c8341d695f6409a21c3785fac71394d82b0f307b9d5f25bdf6cb8fa47df361a,0xf0bd9a7c652483fb5ac87d46293f53408d172cb9f96812a3750c4f163c58b2d079f41c906b7f1a4bf8a02fd315f6ad,0xf1740a92bc3d56f3572dac14806f4d785c20913bfa421d9507c83f528d034c97a1f26c0b18af739468bf5a6bfdb96,0xf3056b48c9da17fd2c1970638b5f46d87b3a0251f53126ca74908f2bd0c75934a8fd72a69b1fc3d429a5f40bcf681,0xf8c2147bda0693fa48b251790d3f7c04685a19b3f4295087a61bcfa94b02657d18fd431c6b5f0728d9c3f5ca2d63,0xfcbd3a79625804f34b2cad86059fa638149b7d20f2a487c6135d9fc1a56d4270b8f21b30c9a8f5c3746bf1d09f715,0xf3c17a852db694fc2706a59b3d4fbc90da128657fb038c51d64a2f804b19ac635df81397c024f926147df8b50a37,0xf2d34817acb960fb8a194d63507f2b641da908c7fb3165a28d9c0f2957db4a683cf9785c62403fc15d0a374f25b1,0xfa835cb07294d6f0518247c3a96fb80431a7d526f0d8c19375b4afbd30214c9587f1b2c09da56f3b971d2ac6f648,0xfca6378b150924fa86bd435c720f1a269bc30d58f3d6c19704a5bf413ad759c806f617b4839d25fd128fc0b2f49a7,0xf50c7b2a1638d9f0b5781c392d6f69c58b314a72f490d53712cb6f6803d19ac425fdb43a6c8207f5a0479b1f48ad,0xf5082cb69d3741fb124a53c8d07f5da2b30681c7fd195b4620a87fb85c4d6a1390f483ac652db9f04361729cfa97,0xfb8730924d5ac6f5c971bd386a2fd81cb439a706fc0472d1a85b3f19480b2c7da3f4c82157b9d0af5369f2056f416,0xf2bca96075d814fd9b473a2c651fdb71a80c5294fc13620d785a4fb038c97a6d21fda095b6827c3f6405391f8b34,0xf0381495cbd627f0b3785a46c1dfd43c97b21a65f82a3905b4c7dfac206319b847f53da9240c861f752d96b1f80a,0xf61438c592bda0fb479a53021c6f40519c7d28a6f8709b3d524a1fc48d9365b7a2f0b1d4968573cfd08bca31726,0xf38460b7251a9df021639b8a5c7dfb4096f5d629fc0379f81b56fc17a6f34ad1fc42dbf708d4f3ac2bf850a2fc3578f419,0xfa03db158c9642fa19b2d40c3786f20793b6f57da4b0f214c5d9f3a52cb8f084956fa81d09f82716df31ca74f536c7b,0xf26d1ca5087439fd94a85b1360c7f24b3c97f5d2a173f18d3a65fb0d4612f0386bdafa96c57f028cb7f40952cfb8419,0xf41a50b29637c8f3b9406512da78f30a6d724fb4c28f5d902fac162f3974af8d19af6cbd4fb7186f580c9f53d07fb13c5,0xf1d83460b29ca7fc59b6d0a31248f286903daf9a1b587f36a49dbf418a57f35d4b7fc402d7f08bc27f5261c0f156c39,0xf3a862490b57c1f4a173850d92b6f2c34b7d81f82047ad3bf52a978c03f7084c95d2fac516f39bc6f0a56fd196f4db1,0xfa24c85039b1d6fa90b81c62574df51406872df4b7a08356f95a843cb2fb5c0794a3f731ac28df0219df7c961fb63d,0xf264c87b50a391f372408b69ac51f3b286579df81b47092df416a83c0df203485a7cf360b94a25f6c95df7da1fcbd1,0xf19d7a286034bcf6b24c387950d1f71ad25c8bf93a4d651bf812c94635f409a62731f470296ca8f0c75bf80a5df3bd,0xf2ad841695c307f3624c1b0d58a7f647bc0a35f283d71940fd139a52b4f8c215bd90fb6d29ca18f9b34a6c7f87506,0xfd60b8527a14c9f3d79b1c2084a5fdb57469a8f13ad56249f0a2d16c59fb68c03712f34d07bca6f1504b3c78f3829,0xfd9c0a1568b243f7d8c496250b13f8127c6a5b3f64bc3f02c53f178acf4ad58f04d28f957a2f1db74f0916df6b970f9a3,0xf3d6420915a7bcf6c9bda1847530f795d413680f8d92a40cfb38a0f587d0f25c1dfb4965fca934f726a3f216b8f17c2b,0xfd3a1402b57c69f3609ad815c427f4782a05d1bf831295a6bfa49c85617f2c086d435f62d03ca84fb07df93b7fc19b,0xf41d69a3b078c2f90cb4635a7d81fa29d0847b1f59b8a4371f97c658204fc5bda6839f5d3ca0627f31c4d250f6b21,0xfa07593b1d624cf5c7ad34812b96fb79d4058a6f37d82a906f472513c86f80b5a4917fd029cb835fa14bd2c03fc61,0xf42906ac78b3d1f82d9a4b05c316f2ad6953840fdb749185a0fa8c63fb5126f52c46f70cb2f9371cf4d803f7a1b9fd75,0xf97204b5c386adf9285341a7c60bfcb170948d2f6b31d0ac42f8bd4a21f37b256df8a91647f59630c1f3a508c9f57d,0xfca7346951db28f029da14c3b657f47185d6a90fb0635c72a8f39b7d248f6c978f0a4d8f1cb49f25b16f0d3a5f12c03,0xf9086ad2b7c134f2cb9640a785d1f6b3920d841f3628b51ac0f3c652a81bdfc57d9fa4279f50719f38c47fb06d4f3a5,0xf70d84a219c56bf960a72d4c815bf826173cb40f420c78adb3f529a147d68fc63d1b2f53a6490f9d5ac13f0b83f597]

def e14_22 : List Nat := [0xf3b5627ad18490f6d871952ca34bf0c3751a29bf14a6c5807bfd536024c8bfa869d05f3d7cb28f46139a0f12d479c,0xfc7a216bd85903f805c2d9a63b71fc687315da4f5b8ac96d07f1938cb265af253a0649f0b974fb1d34f827d4f1c024,0xf924ad15680cb7f4c5270a319db6f96217ac8d4f1b3c6d758af743d5b061cf50d2b41873f382c9fb8409f6302af59a,0xfbc9270a684d31f243b578d9160cf25a940b6d1fb82d053964f2b7da80956f385db97a20f74a36c1f15caf814cf37c,0xfc712a53b906d8fad4319c072568fcb803615d2f7d04b629a3fc14a0b5796fca7bd95024fa6483d1f7493c58f281b,0xf29db8a0461357f5a48d2c1b6039f4d50912ac7f15b26c9ad7f5281d0b436f085cb3a142f86d3c497f7a69bf0c837,0xfd15a48c930b72f0a94c173b528dfca13db2086f3812a709d6f1bc34d7926f5c0419b8a3fb6ad5874fc750642f965,0xfd06384b197ac5f46290cb78d3a1fd6c9a05312fdb57c20861f934c182a65fb8a4037d96fad470b3c85f2715f42b9,0xfa295c80db3147f178a5349d2c0bf6521c9738bf28d1506a9bf420ad586cbf6391ac4072f6184d7c309fa3d64f7b5,0xf87ad564b092c1f07512bd436ac8fc9b61d8a47f586c31a27bfd04253a917f03d628495af5c41b39d20f37960cb8,0xf80cb194a3d572f9687413b05ac2f539c406ad71f6420a1cf370d216fb6583c7f95c8430fb9a81d4f5b8d62fbd97a2,0xf6ad49b7081c52f403c6d78b29a1f4720acb39d8f24a860c95df3790db165af34b6917c85f1382a75f21d364cfb05,0xfd8c06a472b519f502a71db43869f708ac62531bf640d2c378bfa184c56d30f79ad58241cf63a57d4921fb390fcb9,0xfd1308a4b95c26fa129075bc8d46f78350ac1b24fb614c97a58f06819d7c34f3b715d02a9fadb0c65273f63d2849,0xfc750638b2a9d4f5bda62743c908f071d653bc84fa142d0c5937f52c169b0a3dfc6b4920315af2197d8f64a8f1b78,0xf519ad7b83c620fca61b25d87430f82c597a41d0f1368c4d9b5afc12db485739fd642a817cb3f9270a356fb60f490,0xfd7840ca91b256fd3bc2859607a1fad43921c680f5bd26a3c741f209c8d57b4af42738b9d05cf7130b649f5a8163,0xfdb29714a8c036fb02a6874d9531f60437c5da12f3ac24b5690df8570a91cb64fb39c615a7d8f7b94c38052f82d1,0xf804c12b7d39a6fc346915a8d072fad26574b903f5b81420ca73f16d52a49c83fd95c60b1784fa058297cbd1fb63,0xf3db0c7a129485fad651c4b90738f2d574a08693cf72630d8fb5a6402f613bc50f143ac6bfd18259f17b8c9fa24d79,0xf18306275d4cb9fb5317a6429c8df8b3749ac56d0f3d12c79fb1c3687f40b6958f2a416c0fb43a152f0a82d9fa507d,0xf25a439bc6d780f6047c83b1a2d5f18bda3705c49fd3c158a9f96b0357f2864d17f248d09fca7b59f62b413f12c0a6,0xfd4b20a6c83917fb04c73158d269f81a97bd60524fd1b687490f27a3bc5d9f03c2a8b57f41280ca53f59c16f3da46,0xf3864152a0c7dbf70316c5a9d428f7b563d804912f09537ac1d2f8cb296ad5f2c439b0d6f71b48a3c9f18b60574a,0xf9a21b3d04c586fb91a60c725d84fa59c1478b203f49d73cb0516f7926381fd4a0931f56c8243f75bda80f6d2ca7b,0xf3c59612a0784df79a38c065b241f037ac49b158df53b81ad6472f7bc26a8091df50286c134bdf0b639c75a4fd29,0xf08a6493c17d52f03b78569d421af2b0438d19ca7fc8479b63a2d0fb5709a4fc295137fc5ad614f5068bd3fb1826c,0xfb407a931256d8f24ad173bc5068fc47519db03a8f649ca53d02b1f5b726c08fc7d4381fa097841f63c29bf5d2a69,0xf4957ad831b620f35184bd697c2af641ac5d703b8fd17243c6a9b0f7b21905a4c8f63d9285bc0f1652d4739cf80a,0xf1d68359b74a2cf570846c392bdaf6217a8cb5d09fa94c03d27816f560a137d428f14025c79d8bfc9150b43afb36,0xfd12a43879cb06f58690c3a142bdf5739dac62840f52c47b6a08d3fa9561c8b3027fc51b92d7f64d0713f94b5a81,0xfb0c8d73a19462fac6d574138b90f482d96a7cb50f35c29a8061bdf7951da4c3b68f634d072185f4b71c9302fa25,0xf81395da0cb746f9c30d87526b1afa8c43b217d65f96350bd2ac14f190284b5c73df708b9d42c6af061583a4f972,0xf3bc5814a2709df863192db5047cf8a659b7d42c0f3512648d0ac9f578b6034c1adf379a52b1d6cf0b49617a382,0xf2d1b39048a5c6f174c80b29d6a3f78db6419ca03f563d7bc02a18f69b5d43827c1f59a7068b42c3f750da49f215,0xf2c7813569d40af529a160b47d38fca5034127b86f971bd820c3a4f51d62b93708cfad2463bc1957f6a84c90d5b,0xfbc847291d6a35fc1b9438d0a756fc0285a17b4693f36251fb8073fda403fc7905fd4c95f2a814f612b0fdb687f2d9ac,0xf7c513480a96dbf9216b873a50d4f95d3cb027a681f3062c1bf9cad75bf4256c07f1d82b4f7904a1f2a839df8c4635,0xfc68d5b4092a71f385c2d1470b69fda3127bc46059fc365a19f4d02b8af0c7d348fdb37526f428ca9f530a61f9b187,0xf41973c05d628af863ad94bc2157f1a53b69248d07fb085ca7f438c1d7fb590318f9b2560afdb16402f2a6c7f4c93d]

def e14_23 : List Nat := [0xfbc418395d20a6f7968a1b4d3c25f03b7d8249c615f7485ca3f91c807af0c71364f2b906d1f78b0d92f265bdaf4a53,0xfd61538b27c09afc3420d7186b5af84d213b795c6af852c9370f149d50af3047af29b4afcb064f1bd8cf1963df82657,0xf83a56c097412bf2ad04b5913786fb934c2d581a07f16a9d30bfc72508af6d8420fc36928f46bd7afc51d49f71cb35,0xf75a3c8d21490bf43db1529a87c0fd731a2c59b480fc185026af746930af1d5b836fd6bc4af82b356fd91724fc9706,0xf81d650c72934bf6b7d902c35a84f0b28c4d596173fb19752a63fa38607f41a087fd31240fd85c62fb9ac15fadbc94,0xf0241d93658ca7f4bc05d2918a37f1594a60b3c287f384da27b1fc430db257f8b53df9a16bfc5a09f697df6804f6c12,0xf25d8073a61b9cf8c49a15bd0263fb057482d3196cf64a03c795f8b390c1dafca29d435f68140f72b6df7b421fa785,0xf839d5704b62c1f051b3ac64d829fd79c0b8a65341fad302bc74f36d2a178cf725bd0613fa59b7f9680af2491fc584,0xfb0c48d715a293f7049b8c5261a3fbc1850ad24796f82bd57a46fc95b1278afc209d14b7f19a603f53c6fd436f80d3,0xf081a9db374652f84a627d1c3095f9704da5c28613f7a35d2b41fbc83d0691f6d8b0c943f87c42af9b7512fac6b50,0xf4c1738b5d2a90f49b1a8756c30df29d613b7ac580f748193dbcf1286a597df514a36270f69c8da0bf2460cf352b4,0xf97560d382c4a1f07d81cb4625a9fc6d40a8b37159f68c0b29d1f6a27c35b9f58436b7acfa308742df205db1f9314,0xfc6d521b0a4739fc09a563d27184f1cb3ad9702864f2a85c30d4f6bd87a150f162957c83fa691d7b2cf9b534f08b4,0xf15a7b2648d90cfb81697205d3c4f41a2c75b6830df9c56a0bd1fb9374ad6cf3b1295806fa3524078cf7d28a9431,0xf8317c4a0db695f2709c5d3a684bf6d782194305acfc29a1573b8f5b793f24065fd20b9f180cbf4d8a7f261daf3c146,0xfca42d503871b6f6914da5c372b0f158a029c7d643f07a368db4cf53d047bf9081cb3f9d12c8bf62579a1f956a284,0xfc491d3b05a782f9d4a6c0817b25fb8a93c7d56204f70a138db64f869c5124f3ad0614f372d6f5b1c8fcb92af79035,0xf43a281650c7b9f9786d3c51420afca719253b8d46fdb6a573840fb036958a4fd74c2b139fd1cb5f2706f8c90f21ad,0xf3719bd2a80c65fb78d963ca0421f4397ad1620bc8f3b4d5072c1f2864a9c75f06b2947d3f90d6a385f4c5a1f8b51,0xf8506d92bc173af7b816394a2d0cfa6251bd834c90fb97082ca13f0421956c3fb68c5a720f48753da96fd741f5d4b,0xfa38c0b79d2615f5c6873124a90df2a843965bd71cfd19cb8206af1b947c308f4d3b257a1f3592704b6f58d64ca0,0xf1cb24d6a87093f5c8d712a340b6f81b4c9275a0d3f52d9a416c3fa19b30682cf79463f50269f80c74fd5b7afbd158,0xf394d6c8a12705f7964a0bd2c315fb47d3a618290cf20634c195af7140865b9cf3b248d0fa78b1d9f37b6258fd5ca,0xfa95c603d2b478f37b6d52a14908fa69240b357d1cf50261bd4c8f5b9da71346f970d812cf3684a0cf7cb82f915a3,0xfb19d07c2534a6f39b247d581c06fc3b087a512946f6504cb73d8f2db8417590f79c5b4d1a2fad628f13a96f0ac83,0xf1d046573b9c82f6a14c35d8b079f16847b50ca3d9f7cbda58392fb6317a95c2fd6c1b43087f8152d4af062af4902,0xf527d9bc40a638f64b7a2159c30df4935b07162ca8f8750c1adb6f2973d5a418f2b31906c8df47c569a3f8024d1b,0xf8bd4a203c1956fc716b0438a5d9fad18746352c09fc570d8296afb31a062485fd3a721b4c6f937bc80514fb2d79,0xf5b2a4d96c1370fbd591830ac247fd8c3409a1b627f025a39c7846f5368217fd65cb92f80b3d15fc4b8ad0f16a794,0xf7083594ad26cbfca036915d4287f4c37125a9d068f65740b92c81f85c1a7dbf279c05bf902a643f6b413dfa8d1b3,0xfb63c42591da07f4b835d2c06a97f3d8c15b09264af139bd756ca8f6d482a73b1f58694302bcf1a50872f40d9c71,0xf85bc26a1304d7fb81956c0da273fa06b9428d1c35f21bd963a705f38ac975d64f74b2d3908cf684a920b71f14c5,0xf743db5c8a6091f64b287a3c950df307b184c652a9fb0a15d7c249f83614a5729df40869731dfcb62daf20c1f358b,0xfd683502417bc9fda0b3491c7825f130d8ca4729b5fdb265c07a93fb84c21d75a6f1b4d2a806fc3a18596f364097,0xf052a8c79d3b64fb715c360284a9f734d185a62c90f7495b0d613af2da19680cb4f1ca03927dbf12b8756c4f35d8,0xf95c17a62b384df9180a3c2d56b7fa28bc6349051df872031ac46df416925b0c8af860421b9c75f0d37f4bd7f5a93,0xf9752bc4a3160df9415c62d7b80af09127c8a5d46bf1ac0283596df93c2485071bf3047a29c18df36adb4f873b56,0xf5197283d0b4acf0618439bd752cfd530a6c87b149f5b64c1da709f3b8d269a17cf374d65a8021f3a240586fbc92,0xfac14970b2d358f37ad8b6152c09f3a20d75b91864fd9a087b126c4fb42965cf83bd172f1306d5af95048cf36a47c,0xfc0642a85db971f6a4829d0b3c51fd8b6950a372c4f9a7036c812b4fa562091f34086d1f7bcad38f7d2539cf475b1]

def e14_24 : List Nat := [0xf1248d6a05b9c3f60839db4ac172f51d364c7b09a8f037965cb81a2f74d2953afd7825fc86b2f43b19fad075f40c61,0xf263a91b4c750dfb6ac049728153f569c8b7d1420af3c52b09d68a7f648d5930fa17083df1c2a43f6cb921f785bd4,0xf9a875302cbd46fb2a3c09471d58f159ca7b40d382fb08c73419d26fda506c18fd725b16f1a079b3f392486fa4c56,0xf70694d2a1b3c8f25ad346b90817f5386a912cb047fc50a829736d1fac03148d7f15b7c6fb20d58f9db4a3f4c9562,0xfb06a913d47c52f279c3b4a80d16f28b93657a0c14f296bc48153adf7834095bdf507b1ac6df68d94f2a58cf71203,0xfb97862da34051fd4b25ca691703f631d95a2cb084f7283941c0d5bf216b357c4fd7a90658bfc920a18d6f4a8c37,0xfb246091d573a8f2da4b970c5368f31b6c29587d40f8ca216947b3df7183c9a562f439d6a08f25bd0fbc150f4c7a1,0xfc026a943b87d5fb17c4a09352d6f9650dbca37412f06c91da5b728f4b9751368df1c307a248fc2b0461a8f583d9,0xf0317d6ca84b95f6a9cbd0287341f68d247a5c3b09f39d18527b60af407c1b5629fb2ad364c08f57912c83fa4d51,0xfb748c19350d26f7ca95d4306812f8d751490a36c2fd925c4a8371bfc978561ad3bfc31d69b0fa6402b5fa708b42,0xf4d5c8a73b9260f134a5028db7c9f870ad21bc3694f7d64b2a1c095fac4165b8039f7186b0d3524f583a6c279d1,0xfc140d8a3b2657fbd315c2069a47fc4d6b5a128093f052d19b86a73f4b1635d9c078f2718349fdac8597fa246cb0,0xf639d184a7c052f80a61b29c5743f6b4970d2a851cfb72c860419a3f1782095bd4c3f35a1246dfcb037daf8d569b,0xfb304d26a58197fd59b206138c47fd8439651b0c2af9a08b6d1275cf5bc14a378290fac649d071fc368a7f253db4,0xfd7429b0a3c518f9a605db372c41f25b7034da8c96f2d0ca578b461fcb2a71394086f2097c1d6358f1b659d384a,0xf7a1bc92056384fb2ac68d409537f39128a4b06d5cf08579d24c16af0da3146b8c27f9430c71db526fd3b9a5187,0xf8bc07da253961f2d1a734b6085cfdb03c427159a8f4d0a5b3129c78f3ac86f574a6f283d6f9d504fc641f91b7f09b2,0xfb1d9072a6c438fbd5619c2487a0f6297d04a15bc8f941c7b602d35af173c058f8da30f25ca8f96475fb36d4f9312b,0xf9b30a247d5816f8379ca412b506f1780b4c3ad925fc2d1340759a8bf20c8d46fc194827fdb7a56f5c63fb1a6f3d09,0xfa3590b4c2681dfa736d50248bc9fb30d8721c5a46fb14d2560a83c7f43db970f5b2ac08fd75139f6a1749f28c619,0xf1853d7940ac62f0c574b319d8a2fd5b0684a1c392f178c4db6a3095fc9ad072f169b834f1d637cbf564280fb7a52,0xf2ad73b0964851f72d5638bca941f39528c4db7061fd0a3c2975b681fb420c91fd8a62b9f7403d6cf80534a7f5c1a,0xfbd65092a48317f0d2b681ca3497fb02c4d3587a91fad128c59b4730f7d9c0615fc3627fa8041f46a52f396cbf8b5d,0xf594a30c7b61d2f7435cbd681a92f0a26c38714b5df19b85607dac42f402b369dfc28d39f805a64f1b0975fa731c8,0xf35b20a168d479f14adb83c62507fc4928a36b0d15f342d9b1ca6087f3d640c81f03bc219f6572a9fb485d7f95a7c,0xf9182bc306d475f615c4b83d9a02fbd8794135a6c0f29643b58ac17dfa37256b1f7084a2cf5da7b90f0d124f368c9,0xf7530a16c28d94fa73960bc5d124f1720c8b59a6d3f509ca3687d2b1f807b625af583bd46f0da29b4f8197c4f1c34,0xf902d684371cb5fb351da26c4078fa74b163d92805f9b21a4603c8d7f7c0b69385f25db7fa94d0f2419cfca65f18a3,0xf4ad81c9370b52fd4b85c6a17209fcb649782d150af3412a9bd657c8fc2695a840f35d74cfd3160f6308f2b19f7a3b,0xf6c13b09d8527afd3c280a561947f5c42a1db97063fb751296da8c04f784d039acf81b643f59cb20fb5d268fa4173,0xf620c358a79b1df709634d28c1a5f8bd742ac91603f86a94cb7213d0fad92c7814f15640b37f25c6bfd84b5f93a05,0xf9bd065c74812af53d28c0971b6af026d9387b51c4f68d13057294bcf08b3695d7f73c9164af85241af0b2caf34da,0xfb2940a1d736c8f2d8157a30b64cf7248613bda90cf352806a417b9df1974d05bcf395d621b4fa569cf2078af385c,0xf9a43156c802d7f93c047bd5a821f873a0d695b241fbc49275386ad1f258b6307af4d3b9c506f09d84bf261cf71ac,0xfa5b908c3741d6f61534970ac28bf03d917a2586cbf21a38469c750df724063bd8fb18a4c5d7f5620c139f29ad4b,0xf5b0c12a87943df52047d96b38cafa182db7c46590f705c91d4a68b2f06351b48df926175803f142cb9a73f6c3ad,0xf6c9b781d530a4fcb804d917526af05b2841c3da97f36d0b1a859274fb490c2a38dfc42d7f315a7f6120f568cf693b,0xf79c051d4862b3f1bca65d870249f9a0d2c41758b6f16da47c529b08f8c12a7bd93fd728a13f95a30f64b53fc6043,0xf718b69350a4d2f6d92a5738c1b0fc24bd7951a680f5849b3da7c612f209ca341d8fd5b2640f78a9130fc365fcb74,0xf05a1db4936872f419658d0a73b2f84a607d35bc92fd6431c0b8a975f3c8047b9daf095c6183f2c715fac4d2f6b12]

def e14_25 : List Nat := [0xf9746ad8b03152f1d9365b72c804f617d2438a59bcfc573d6812b49afdb62a7c350f70691a48f20c4d58fa3b1c90,0xf95b217c0a436df402c938b6a51dfb7a8c56294130f9b3507284ca16f3db187906cf52a91cb47f42d86f580dfa37d,0xf21a50c8d79b46f82b37c40da965f2a63c908174d5f39d60bc1427a8f1db75302c6f70ac591b8f86b513a4fd3492,0xf5b3c4087d96a1f7adb9c8302564f5362a8d17cb09f9ac60d31b2857f92c5d6b734f5a4b861c0f93a072d41f2184,0xfa7c48295163d0fd8c975a1b3064f1c2587340bda9f2d5ca41386b70fb50c627d94f81d653cb90f3a69f2471f2b8a,0xf7b653841a0c9df587263d1bca90fa347c60b512d8f286ad4913c570f397a25db40fa59b371c24f296d08bfc4618,0xf4d3a27c8b5160fd5cb4638291a0f659adb7342c18f9d8a53174c62bfa697580b3cf21b6d78490f52d14a70f9c03,0xf02c1d69b358a7f93c652804da17f9468c05bd213af14275cb6309d8f159ca60d74bf0b83d5afb784a2f9162f34c7,0xfa96b874d02513f2a1738605c9dbfca563d7b49082f79b146c035d8af43bc8572d6af91da0b5fc481293f62407c1,0xf31b8a790c2d64f7d038cb96a124f4c1620758d93bfb052a3d49c786f591da48273cfac635180f5b71406f92bd5a,0xf0613852bda749f687b912c4305afcb14829a07365fc3d20b46971a8f7c18d62a3b5f1d08b6c95f9d53f04acf4d72,0xfb062ad1847539f7a6d950824c3bf49c12073d8a56f52ca4b830d791fdbc6341a092f96872b13af5c716bf4d58c0,0xfa73c29b568d40fb635da48c1902f159c7430db8a6fa1d279380b4c5f149d6c07528fa3b785062facb12469f713d,0xfc57db192643a8f7ac2b940635d8f6da14b379520cf5130a9d274cb6f3c71d4a5b08fb70d39c168f5096a28f2481,0xfb920a6c74d185fb3d27916804acf8d517093a246bfd94821a7b0356f9adb1c43605f962b4137d0cf3c25a8f875c,0xf370c5b4628d9af934dacb718065f741529c6b3d0af57961c42db038f35a1b2c87d6fb913c7204a8f486a21d509,0xf56acb312948d0f6c2d79a4358b1fa3d9680b42751f460937c825bd1f7819b6da5c30f471c0fd59c4fa7b20fa8362,0xf17a35840bc6d2fbda5c80793142f9b5d437ca0681f6150d74c9a83bf03c1d96a4b72f563d829fa1b8752fc09462,0xf7c48a06b53d29fb04681ac527d9f7a508d4126c3bfa63024758cb1df5db4a2871c09f34916d07f569a31f8b2c93,0xfd857430cb1a26f38ac7d219b406fa92480b731c5df94a05b8172c3df3bd1468c907af782b6a59fc4d0256f15396,0xf3c029a4615d78f031d652a7b4c8fb14d26390ac58fa17c248d3b605f97340dbc18a6fc9570b286f9b53adf27491,0xf0746b35219d8cf1a69b40873d5cf17209563adb84f497b1305a86d2f9c60a4d75182f61d0b583c2fc7a2bf439ac,0xfa3c7b9412d586f38b027d4651a9fb1924306c87adfd31c4b28a5096fcb6253748d0af071d95c2a4f9c08163b57,0xf1c78509426d3bf169a2b57d08c4f5918ad27b036cfa3568d4b9c071f5acb84602931f5db6a0473c2fd97a43821,0xf6bc90738a1d42f59a61b30c47d2f81297b56d34a0f935db2ac87146f194b85063a7cfb9da513c2840f5c68d027,0xf0c139d2b56874f3a94b162507d8fb06c351428a79f18b73d64c2a09fc58036bd4a129fd1720fac75dfb348cf6a59,0xf1b05c73d84a69f7081d625ac3b4f0db82a756439cf02d7b68531a94f2b5da8309716cfc87241fb9d4cf1592fa360,0xf9027cbd1a3856fda28b15940c63fd7ac914805b26f134b70d8c29a6f0a812d974c3b6f4253786fb930fc571fd4a5,0xf30814d75a6bc9f7861c3bd92a04f20d36915b7a8cf73821b95064acf079a31d26584bf2b8d6c4f53490cfd5271a,0xf9a062b738c5d1f5a703b9d4c281fb47592a680d31f427da356c90b8fb58a46397c02df78d6bc1f2504961fa143c,0xf08374c59b261df71a2cb058436df41b8a690c725df97b40a3c15682fca75b64203918f8706c9adf94a53df13bd2,0xf6d07152b839c4f0a62731d5cb94f2a9536b180c74f91a7b02c3d856fda5b309786c12fc829db4af16057d4f3a84,0xf49b62715d0a8cf042da73b8695cf28063a419db75fa64b2c97d1305f438d6129acb07fa2093d481f87c35f1b56c,0xf836412ad0b795f927d6a51308c4f86c9b2d1a7534f81b65c73d9a02fb52617093ca8dfd50691c24fcb8740fa3b4,0xf8b70a3165d2c4f08a96d435712bfd04a62781c95bf025a7941d368cfd73064285ca19f15092ad83bf93c6bfb47c,0xfc7805b6a93d14fcb1a8279d6435fa360b218c9475f2a73091c68db4f3169b840ad52cfd4ac029517f07b38562d,0xf170952d4b68c3f69b12c4ad0853fd1a5b0629c783f9ac028157bd64fa8d9740561cb2fb8427d5c6a3fa730f9143,0xf71c5286a93d40f81279cad53b64fb836c29051a74f034a58d2619bcf873a241bd9560f5b20a8c31d7f4c7b0d69,0xfd302ca68b1795fa46b72d0c1835f1248c9b06da75fbd4907c613a85f4c3b269a1d780f74bc50a28d93f1436529,0xf24817d35a0bc9fad5213c8694b7f85c436a1d0972f9a30c6db87415f0839b1ca2d465fd916b37c204a8f6075b2]

def e14_26 : List Nat := [0xf6a3d8140759c2bfadb12f780d2f97a82f4bc02f51362fc17b8f3c60bf5869bf4c738f5d9acf4a1d7f6d491f35a09f65034,0xf6c3957ad21408bf83acb7f2653bf49c5bfd920bf15a09f648a9fd1685f27d05fc4307fc2a60f36d47f8c13dfa4281f179b,0xf4b38c260a195d7f187ad6b5f9a2508dbf2046c58bf96a437c0f53c9d286f7294ca30fd48a5793f1d0b7fc1bf361f241,0xfd0ac752816349bf31c56970f62b8a590f1da78c39fd74cb6a9f1a4d5837f4b512d68fb146c2a3f7b0c92f8d350f402,0xf0c8d9a34b71625fb0d215c9f82a06d5bf9204a785f64180975f7c1b6384f68a1d3bcf07da6913f73c4db2fca53942,0xfb96ad1258430c7f35cb1807f31562a78fd86174b3f9c8b20a3fa46b5728fd5ac190bfd792c406f42d059a1f6c3fd49,0xfa907b1c835d246fcb04a569f12c308d6fa849250cf743b815cf13a795b4fd7860a2bf28571d36fda193720fb9d4c6,0xfc86425b7a1d930f19cad3407fd08372f9b187fc2bd7f56d47f5a48df2a0b8f513a8f6c49af1c3b4f69021f62953f5cb60,0xfc4835d6b902a17f97268b051f475a0c13f693d7081f582406cbfdb29c3a8f6ac52d94f1b37a4df2c87b41fda95630,0xf0a86b1d43592c7f3c9bd0217fb069748cfd724a618f5c03a2b7f65b3194cf83d5264bf82d639a5f87ac140f51ad90,0xf492ca607bd8351f86950c13bf2d4c90a5fb619a8c5fd71a2485fd6c7304af21d3cb46f0b18279df439b2087f7a365,0xf29ad374185c0b6f2175dbc90f35972c1d0f3a528c4d9f7c31b8a2df42b51a783f48619fb369fca46f50a6fd806f7b40,0xfb6082719a3c4d5f49cb851a6f1b2d84ac6fc1d734b95f7b30c218af47920bd31f369da25f8c70426f093875af0d65,0xf5ad39c814b7206f150d6847af91285c37dfc462d5907f8b52ca94dfa30c6b924f69780431f53b17fcbd1f0a2bfa638,0xf6a49c15d02b783f8c0742931f06b5a2c73f6db48a05cfda7125964f162857d9bfd8b09ac3f56804cb3f91d27f341a,0xf814d95a73b0c26f08a9725c6fd1cb83475fa4036928cfd20a39b58f90da6513cfb2a17053dfc487f1249fb164fb7d6,0xf3a8c609d425b71fd1c4b9627f3d6b0c584f3cbd59216f570a9c286f30815ac79f873502a1bf83b2df6a74f0da4f194,0xf596ac04b2187d3fc608a1372fcb5da2483f56820974afb85c71d26fc94150bd8f9d4c1b752f46d0a93fb9163f07a3,0xfa86b215c39d740fc024163dbf946c2a31bf92871d560f7c8196ad2f437ac958df79a1c4835fd625a4b0f3b80f705b,0xf043ca6d95271b8fd7a96c058f13ad20978f41c937b5af1a0b2c749f6b4d03512f3bc57061df9bd56382fc42a8f468,0xf5a730db618c492f28da6c341f9d704263af0b75391d2fb4a805c79f865b13d47fb85d60a1cf71590ca2fb38469c2,0xf0c4269178adb53f09d148b75f20643a7d5f13d8c2a65f0b186c74af2936b4d08f721acb940fd2b379c16f3c58fa95,0xf1d42806a573b9cf907b53c84f8acb26395f218db405cf72519ad0cf7a2d6b038fd569714a3f920a1647df134c68b,0xfc1658b94d3027af91b7340d6af4180af2c3a1f5368af259dafb5713f97c83fdb051fc47d5f06287f4b2d8f6c924f90cb6,0xfa4d75281c09b63f5ca8d62971f1bd384f7a613f965a1f20ad1f9c42af705d2f34b59f87b35f68c74f08bc3f0b2c6f049d,0xf8b57d24a6c0913f47a52c8d9bf18493702bfa16b03f5c7b3fd59cbf69785fa0829f60da8f1ca27f63412f4c3d6f4d150,0xf958b7260a4c1d3fc0d2a84136fb69d82ca34fc3568f74038f1b508f709b3f25db0fc942bf17a92f61ad4f5c791f5a6d7,0xf2da1c5b9347806f836cb4179af2c857d913af4907caf56b7af24d37f84c96f1b046f28159fd8b21f3520cf305dbfd0a6,0xfc2d19a0374b568fb75c4d36a2f1c0b397da5f705d6b1acf9bd025f853cbf6129cf8469df09426f81340fa8714f3a728,0xfc207b19a84d653f857db0c936f27c15d38b4f25971308cbfa3b5cf064a5fd216af2690af7341afb94c6f78d04f9281d,0xf75c82a4bd31609f26408a519bfd58b03ac29fd653c741a0f37d496f9c6b3f507a9f8d243fc1784f21bc0f681dafb725,0xf4a1d268c57039bfd4251b8379fd31640c785fdb3481c6a0f82cb71960fa8d749f6590bf214c9f05a72fa35b2fdac36,0xf8d690a3571c4b2fd12473bc80f634ac5927bf5649d7c381f6a7052c931f02a8bf5d41bf91adbf062d3fc6840fa9785,0xf83721605cadb94f395264780bf6d2b415709f1c63a28b79f9a713568c2fc9d043fa5d30fa18d4f7cb1df6a85bfc420,0xf3149ac56820b7df621c795d04fc370a2d819f4da751690cf6c253a871dfb4305a1f8392b60f3b584a6fbd9f427fb8c,0xf9a4b63570c8d21f08b5d461c3fbc7d950283fd625a1487bfc247ad0685fd156c93f6a0b279f4ca81b9fa29043f713,0xf2c085b374ad691f9a2b83c614fbd815c9364fb953062d4cf025ac7b134f657248c1af90d782f0a86bfd3a71f705d9,0xfc69135b04d82a7f3b4a578c9df3a0865d2b7fd1a60c438bfc18ad62503f6bc27d093fac51479fb170249f5846129,0xf30a21d4c69b785f192c7438b5fac3b416275f4607a39db2fd7904a8136f9ad371b084f9cb65fd20c5f28d05f86a1c,0xfb390268d1c5a74fd3cb84950af2b9ca4d708f2736bd041afc031529d64fd560b197c2f61243af57183fc69a8f7b58]

def e14_27 : List Nat := [0xf041d8256c9b3a7f0a6d5931b2fa530c84692f61a850dbc2f4b091863cafb6083d94c5f512d437f9ad7fc17fb87f427,0xf09ad64c371b852f8d5c96a724fd3b5921804f6cb93057d2fa351db068cf365a870d91f614382bf97c0a4fa1c2fb47,0xfc4360bda259781fb9a082d147fc053d84a17f69c302b85dfc56a83b192f94b5ac8613f5124d07f26409d7f3a7fcb6,0xf6c1b9048275da3f5b0a7869c3fd261a8c593fb4d0792183fd64c052b71fa5602cb8d9f94ac731f742a6bdf034158,0xfa1704cbd652839f18ac69430df748b1620c9f15c2d736b9f758c3da412fc13a5b4687f0a2b359d8f4d5092f6a7b0,0xfd064ca3825791bf8156ad90cbf692d43705bf4a9c8d6217fc149358a27f1a5d3c2486f87b95c630f31d7a0bf2b40,0xfd638c750a241b9f2bd34c6179f8d127a3904f08591ac2d7f3b60c15287f3c5b026a81fcb86530da9fa5d4f964f7b4,0xf36d870524cb91af9402a815c6f4713b0d59afd7b841265afd2c09346b1f8275bd9c30fd358c792b4f160acf837a6,0xf5840a73bd21c96f4b0638cad7f3c5b70864df52a3197c0df502c439a87f2bc6a59418fb90351a426f716d92f1b8d,0xfc9b0ad41368572f9a71c42b3df73a8b4091df846bca250df065a43c782f96180c5b74f038c6a1597f1bd5392f26d,0xf756c0a8b34921df9c50da36b1f837ca9b26df417a253d96fc4a1827093f5168024b79f0b584d2c13f406a5dbc87,0xf795ad81b30246cfa4875bd62c0fb8c90f52a68fa7128fd19b2f9d472fca14bf60d7bf5d370f3c49af1635cf31569f3804,0xf92687b34c15a0dfd8c52a791b4f813d7c60f5941ac36fa842bd16f9c035746f85bc2073f9b82da40fd6b05f9a3f217,0xf4b71c38d62590af530c481bd7af8c913b50f63a97cb0f642158acf1a692734f8b2d1657f682ad39bf402c5df9470d,0xf873d12acb40596f3471c26ad80f6c97d531f94a728c3fa0b91583f429db8a1f0c7b25a9f46d2075cfd481b560fb36,0xf79d2a640b58c13fa9283d4c6b1f56027cb41f0d193f78421f69081f3c594fa3b74f57d63fca8b9fdb268fa705df52c0a,0xf5b174d8ac69203f72d9b04a183f915a7c2b4fda268597bf56a931c07fc3d521648f4c50a36d1f608243bfc90d78b,0xf5062971c34bda8fd96480c5a27fd4120a3b5f83940b1d2fc687b9a42f709136ac4fd618c9530f651a73d8bf257cb,0xf5a07c864d3b921fc1b74a2d509f8142b0c36df37ac5fbc625f8a965f6bd1af349daf30d79f84c27f80613f4028bf7591,0xf79634d05b82ca1f731bc62049dfc3924b0751f5c7b9083df19a64fd2561f8da21fb6872f03bd6fa74c0fa4853fc8a59,0xf9d642a8b3170c5f0875214b6adf3db9658ca4f1b50a7268dfd4c35f163a5f9381af2b048fc947bfc6091f37c20f792d,0xfa95307b64d8c21f4a31d287c90f50b86c1427f6083da5b92fc4b25d973f02a7df6acbdf58a0cf1743bf65193f49618,0xf3b684d0721c59af85d9b24c36afa28d17b534f875690a1bcf05a7916d38f7462cf049c6f51392f0cad2fdb037f18b4,0xf46158d0a2c9b37f26d413c0795f3a8b5c7196f4a5d182b6cf039421b7a6f78ca92d35f84056f4b083fda1cbf9d720,0xf796a24d81bc350f64b315927a0f485d6c719afd3749b025af65c12bd043f75b8614c2df1d93afc8309f26b78f08ac,0xf5d643cb09187a2f8a93d74c61bf04b2d15c97fc1306bd857f28356a4d0cf086273b9dafa5b712963fac841f42059,0xf0619d85b247ac3fc7381b0a964fbd70c92534f1a5087b3d4f2da86bc590f28b971d56afa31c26d04f948c63f7512,0xf7d4a6821b95c03f43a9c607bd2f1c79385b46f5a8bc271d6f31578da0b6f2ac4805d3bf53c81a7402f692f149f0d9,0xf4d91528a7036bcf72b13a5d648f961247db8cf39a6c2041dfa05b3c1792f0c57381a49f43580dac7bf0b956f68d2,0xf03a1c75296db84f5a427193c0bfd3bc50a947f802d41b6a7f215dac864bfd826134c90f536c2a81d9f065837f97b,0xf5138ca720946bdf3b7d256914cf581c2b40d3fd6a9374821f6079da5cb1f62a034d87cf805b924a36fa8b0c9571,0xf5a6d1b8c374920f3860c79524df96c4a17580dfc18a365bf340ad26bf9c28d70bf30912ac5f316487a9f415dbf7b2,0xf514bca6287093dfd927b03c564fa348c061795fc6352da4f8b2a7405fb6d19c75f831c2496f08db9a12f81b37d0a,0xf208356ac1b974df46cb8d0392af34b51d78c96f160b7a582f3a14905c7f0a913b2c4fadb6248fd957186f3c0725d,0xf1ad43968c7520bfa80916472b3f218d9a5c406f5831d79c6f2873c150afb953d2417f8492c0d5bf307acb6f4bd6a,0xf82716c3b0a594dfb120d96ac74f09c863db7a4f1a8075264f30cb65184f538792d60f137da9b5cfb2a391d58f42c,0xf462d307a8b5c19f5d72840b3c9f3524a0618d9fb20c8573ad4f8741b90fa634c29f1acb683f6c79f15a2f1db7f6d05,0xf0bc81536974ad2f346d85291c0f4826a739b5cfac7b16094d5f0759c21df687db3cfb42a056f8b27140fa3d9f1a83,0xf1643c509b8a72df6b14a5730d9f170bc9426daf91206ca3847f3d592c4bf40c782bdf5368d7bfa08c156f852a931,0xf7863bda1492c05f8d4213796caf938b5c1702af5903cb27d18f61b482d0f647b9d52f56d34c91f6b04af7c80af5a3]

def e14_28 : List Nat := [0xf3a9c862041b5d7f6c2748539d0fbc5638d12a7fa8096db251cfc3d49570f1a503b97f46a0b813fad2916b4f824c7,0xf37208ad5cb1964f3b56a9482c1f703629b4d8cf1687952bd04f7d6b0c385af1a39c605fc471d90af53d218b7f24a,0xfbd364908a2571cfb435dac9160f2d841b695a7fd92138b56a4f26d185c3a9bf2c68730f51a0fd740fb397f28c4f70c,0xf46d3c2a8190b57f265084bca39fa1496b7c035fd24c1360a78f1b3704ad9c6f6a97158fb95d438f8c52f20d7f12bd,0xf1802c74a39bd65fa509d341726f38d7a21cb06fa1b735d429cf13b497528adfb2d0c86fc40a916f3c5b870f48596,0xf5247c1b369a08df06a271d48b9f703461ac2d9f4c38620b7daf4b6c0d37821f0492bd65fc8a75f813a5fbc915f953,0xf2c7563b09a841dfca405962718f1ad86c07342fa531c97b6d0f3a61bd94c58fd3064b87fb5d47a2f9152f93cbf820,0xfc2634197a8b0d5f85b73ad9612f87094a56d31f7ca68d4b951f3847db60a9cf40572d1cfa1bc802f46c0392fb352,0xf342db80756a1c9f0d378c4a59bfc0ad9641527f05d192c3a84f97d6c58302af6094b712fca74d86bf2b318f5361b,0xf021a4bd968735cfa948d563bc7f3815a27b9c4f6b05917d28af4d1603975b2f146290acf3ad0852cf6d31b8cf470,0xf2c36d1b590847af6b713d9ac02f12873b04a69f460753a8b29f18527da034cf38d05a16c9fc79bf5c86f42dbf15d4,0xfd95bc728134a06f5624c1d0738f2da1b968750f7a2539408bdf7903b48ca61fd36c0b2915f412c3a8df9a5cf6b74,0xf061a7c9b852d43f917d3b4280af7490ca518dbf269570d1c8af56d972140bcfb1384ad502f92c46b53f786c3f6a3,0xfc85bda79034126f3d6bc04815af17d29c4638afd427c31b950fb8d19375ca2f9d56a02874f96807b4af1c253b06,0xfa7053864db12c9f02a5d6bc849fc73618da4b5f82d1ac3047bf3a6241c087df17258a06c43f9651f3b29fd0b9f795,0xf561c380bd274a9f914d0378bc6fd17b428c906fb3da7c21846f075d9b1a34cf02b51397d8af35ca6f862a5f92504,0xf02b83da179564cf43c8d1509a7f2c5d961b48af94031287b6cfb5a6392d07cf0857d419b3afca42681f7253fbd60,0xfd4b3c71a680952f249db57a31cf05183d79ca2f30a46d5cb19f36c047b8da5f07348a9b61df78560b2f4128cf962,0xf69c31275d4a0b8fc1d8a3609b4f8c7da1b2504f926d037a581f5c2a6bd3971f43b56c082d9fcb78359af2470f416,0xf4b7c925d6a0831f9a584c27361f35712a40b69fac51b8d0743fb97da8620c3fbd4281c6095f1d2bc87af9d30564,0xfb2130a58c6d947f1b63728dac5fc0614259a83f5dbc7a68093f48b50d2c91af8756920b4c1f462a3b971df7043d,0xf5bc47921830da6f508c17a3942fc0a15d43b82fd631b9c5702fbd968a53c72f8d37b604195f784b09ac61df62a4,0xfca51487309bd62f940635b7218afd86934a20f74b65c3adf80c752b13fa64d58c17fc428b0a16fcb3d9fd192f7059,0xf92c0adb7843651f718b52046a93f805c13a72f47d5a8612fd8590bc41f38c96d075f06ca4b9d3f3c794d2bfa1b62,0xf8b2641d30ac975f7168c5390b4df87056c3bdfd5a842960f27495136df20c1a37b5f4ad9bc283fa7c4081b6f2a91,0xfd13578c9b60a42f394d8a621c50f27b40d63815f41a568079d3fac02b8473f5bc619a28f964c7adb0fb3c295d71,0xf80d7c4953a62b1fac9d130b8427f8c04d5a1692f719b50a2c64f93b7021c58af3687514f6d83790fcb652d3fbda4,0xfac7d5b18430962f58c9b73a6d42fb46079a13d2f95a4c617802fc56b0da8391f9db86350a74f0c28d14f7512fc3b,0xf5da9b24781603cf127a3b058d4cf0a82915b6d7f538bc264097f02d341a569cf86a25931bd0f4ac637bf849d17c,0xfd4a30c27916b85f3b9d6207c1a8f68da9c41b25f96317480ac5fa64392d7815f2a73dbc6094fd128c357b0f504b,0xf4bc829715a036dfc9d508b1627af2a6481390dbfb5941c37d20f753a8d12c40f5c7b3869a42f658743da19bfc06,0xf25d4817b3096acf5b1497a28c36fc159a38d074bfdb216c9f3d68b91f78a4392f0246bf0ad26f5c408f50c73f1d75a,0xf2619db4c3a0785f536ca7421d0bf15a2804d39cbf05729b34a6fb20c846fd6817c2f7d56903f8a97bfda138f95c14,0xf5c7da20834b961f6d24175ac03bf0b2879c35d4afc13d9a6504f90d1258b74f7a18460f273a8c6f8db1936fbc295,0xf6c4375db280a19fd0c56a74b129f8b614da9307cf8d72c94a531f46879b3c152f62d17b048a3fbca206d385f059,0xf0b4721538d6ac9fa41b6397c582fd4c173a068b2f5a1db7802496f07d316cf46259b3f8c291fb503cfa9d57f840da,0xf61782a4c5bd390f3b6927c81d04fc9a85d62b473fb7915a6c24d8f59da130f6841ca3f1b94652f83570fa7d20fb0c,0xf57916b02d384caf065bc3ad8129f49536d17c80af4b2c68a1370df62741bd9fb7d5039f58240c1f87a643bf25c9a,0xf07b3846c21da59f9d426b0518c3f2853db406a19fd8b17ac52036fc475613a9fb97d5f68a49f1c734f0d2bcfa0872,0xfa9b87046315c2dfbd49173ca206f50b7a124839df95280c6a3b47f57c18a03d6fbc85341fb29c4a5f7268df0961d]

def e14_29 : List Nat := [0xf6d2a0874c1b593f86ac5d0279b3f5ad7196042c3f7a851d94bc03f16b29c84d3f7b8126cf509a146fdb07528f3a4,0xf0592b18d734c6af51ad2c9708b6f6193c7b4a852f360d94827acbfd571c09a24f874120b96fd3046fc5a38f135bd,0xfdb2619c804375af3a9658420c1bf0bc59413d7a6f39b47ca18d05f36c279d5b8fa03c4d2178f7b68290fa46d152,0xf3ca8697514d20bfd83916c47b5af80a92c5d634bf9530cb21a784f70d31b9c82fd1c73a6509fbd7185246f062a4,0xfd85170c964a3b2fa821934cb56df08635c241a79f73ca250618b4fd78c62940b1f203d59a6b7f4831c75a0dfd9b,0xfb8d5c204639a17f96c130b287a4f380a59d61bc7f0dac35b68129f9c4bd26a857fd3b91560c84fd143a2507f742,0xfb53a29781d46c0fa574cb286d30f261a843b9d50fb4a65937c12dfc249ad851b63f725c960f13809f417d0fb8ca7,0xf84b9dac5127306f1793a4d20cb6fd58047c29136f7d34c82a1b50f57a0d8b3c142f6538a94f590b26afdb781fc96,0xf8463b95d21c7a0f42690ca8d15bf82a19756c40bfa61b278c39d4f86bc29ad7135f6d381470fa50db73f20349c5,0xf4ca8396d057b12f0b48c3197d52fd40a2c16b359f1dbc56a90734f29c03da1785bf827c63a51f8649bf62d80fa74,0xf65b14c7d029a83f6a7342b85c9df5307462ac81df784a3196c052f804bc3975a16fb0951c2d3f7b94d821fa06bd,0xf6531c24b90a87df12b34695ac8dfa375b084162df03c51b6a2974fb8520c639a17fbc91827a4df507c49df683d0,0xf1782b64d50a3c9f0b31d8c47259f07bda5c63812f608a1b49d735fd39b861c7a40f4857962c03fd6acb5142fa92,0xfc7538b9da16204f306b2d584197f1829a5c63db7f05b34a2c1d69f0d8a312564bcfa68c3951b07fac942780fd74,0xf21473bc80a9d65f60b2d8157ac4f9438b702a5c6f913a6bd482c0f1da40593c786f9b5d036271cf97d358a1b42,0xf1d0ac25b374869fa75c34d602b8fb61a403d297cfa94c17805362f183adb095642fb4139c6a58d7f70c82f5d9b1,0xfb7059a38c4612df2879da6cb435fac02491b8d65fc2a0417396b5fc3b2906847a1f08a4d3627c9bf7d03185f15d,0xf8d1a5bc4362790fc7b964a05831f7a2c60415d93f194b82d75ca6f871b03d4259af8470c356db21fd029c86b3a,0xf05c62749a13d8bf2957340d681caf97c084bf20a851bf78214daf4a6bc2f3a5d7bf5691dbf639071f3064c8f253c9d,0xfb431c6092d8a75fb251a3c087d69f0714a9d5fcb81d479f46b37219fb0da2861f7c2403dbf483620acf395fc85fa65,0xf2c9d6438a507b1f084a6975b2d13fd7281a94fcb685174f6c7a2591f35da0b87f9063c8dbfc56293d0fa3b41cf024,0xf3c6a94b05172d8f687c043db1295f364280d91f7581a390fad48b730fc1d5b2a8fbc416253f9ca47d6bf20697a5c,0xf9da6807c251b34f1cb830657a42df19ca028d7fb6c4093a2f96d0c5312fb5d3c8164f9a587f3627fbd47f148afb950,0xf02b38714c96d5af972d0c1856b43f1d7a48b03f4da36cb70fc352a1947f12c86a95bfdb90573f806429df5ca8261,0xf0524d1a739c8b6f302cb481695adf574a680bdfca09b3827f1463a2d87fb53c04921f9134c58afb26d7f79d0fc156,0xf521b938dac4607f8bc34a150d927f56a80247cf30c86b5a7f96c1d4b0afd35840916f817db3a2f631495d2f7b2c9,0xf1ad509c4b62837f9d1ca6342078bf31846c2bdf9a358d472f0a7b3c56df8c0b5914af7cb168049fa512f57d2f9603,0xf1d7065acb43829f0a63741852b9df057a12649fc0b3168d5fb84d3c715fc203a87b6f2a408c1bdfc4279fa96df539,0xf8d9073a524b16cf8036b95d21ca7f3c50a4791fd60b7148af2934cb586f3572c0db8fc7d3b2049f81569a2f4d1a6,0xfd82bc5074a9613f1b6a0d42953c8f837d19b46fa78512d93fa2c975b08f27140ca56f5da1c4902f06c7b843fdb36,0xf341c965d8b0a27f205c74bd683a1fc3187925afd35b60c82f6ad195803fb75164a93f2b170d4c6f9d7a842cbf904,0xf240d61b9c3785afdb63a08492571f9d4351a8b7fc13956ad74f06812d3bc7f627a914fc8d5b4af0382c69f0c5f2b0,0xfc07d4965b3a821f6a0259cbd1384fd04a91b735f1a7c3906b4f18dac62975fc472b85f863d9b0f8c2d617f0342a5,0xf081a2d57c63b94f348db5ca61970f871b4a062cf8a96d0c472f37da5146bcf8b7a31d956f39c124df50b2f902f583,0xf9503417d2cb86af1836920bd5c7af3524c6b78afd4b9312756f8490c3d1b2f37408d915bf58c160afd079caf462a,0xf73649125da08bcf935168d2ca70bfb26d3875c1fa9d74206c3f90db582a4cf7b40596a81f41a56b3f0c84d13f927,0xf3825d0b9a61c47f39d75b62481a0f4ac3156d8bf9412adb70cf7a3d19205cf78536904d2f5a8643b179f608cfb2c,0xf13825cb7d049a6f75b18d6903ca2fc847a59b21fa420685d91fc4b3780562f79c0b63ad1fc70a8bd346f2d41539,0xfc3129657db480afb3704a1d825c9fb50d2c79346f720b863af24c6d58afd309416af4783519df18c062b7fa95fbc1,0xfd0a84319c6527bf8ca14b607d593f2a73d9051bcfc30b2871f6a429753fc08d1647f8b5a9621f6d204c58f94da3b]

def e14_30 : List Nat := [0xf68a04c27351d9bf7058da19426cbfd5c3087964bfb1829a4d60fc75a216348f9317d0ca65fa3d209c147f38bf52b,0xf0d5c1829b64a37f0b2d834ca1569f48b30c7916df7bc60a9d35f136a2047dbf9c2508ad14fc395a71268f58724b,0xfd509a2c8634b17f593164ac0db87f819cb652073f5c792d1a608fa03d4827fa512b9d8f6940b3adfb7426c35f1c4,0xfa34c056821db79fbca5d48196073f2641a8d03c9f780b516ad2cfb8520a7d631f8c5749d3fa271c6b4fb2409f539,0xf43528706db1ca9f514ad7c9683b0f42175d0a3c6f74cb2d18039f27b4d31a5c0f85b61904f6a2c8d95f2637a8b9,0xf61a30d587cb924f95a713b4d280cfbd94735c260f8c1b704a63df96c38b51da0f4ca21865793f72b6df148a9f250,0xf912a4750bd8c36f907d15b6a82c4f81ca9730246fb29c06d5384f59d0a3b1726f8b931a52d40f3416c7adfc587b,0xf94ac6218370b5df7b150d843a692f35687c0419bf7d3642a09c5f825a71306bcf1a8b2d4793cf20859adb4cf6d1,0xf26ad37190c4b58f30521d7bca946f3a15608bd479fc2b6d57fc314029f34a8c1bf786c5af183596f0d8427f9b0a2d,0xfb509c87d42a163fb86219a5d3c74fb649da703152fd84027596fa82934c56f806cb9735fdb714a0c2fac183f0b1d,0xfbd38ac02491657fc6d17928b5a34f4d853b69c2a1f804a739b1f0bc786213f259ad064bf72d905c84f63c15d70a,0xf0db1a56429c837f86c415da203b7fd62b4ac75391f6b528d31c0a9f48b09d7f06a8594f1805c36f9bc217fa34d27,0xf56c7a938021d4bf1a0b3429c8d57f3db879164c2af3c52b14906d7f9da681530cbf96b74a82d05fc136270485a,0xf80ad2b137469c5f0b5d7a26c3849f14c78630259df0793b8a6512cf3a91728db405fb75a18cf160d4acf9243d6b,0xfbcad6938704125f7268a31594b0cf1c5d2a7b8036f6a174c8d092bfb9a58206c34dfd9c246573b1f9184a053d7,0xf490715bd28c6a3f2ca46058391b7f7a20d65cb314f37c9d1a862b0fb9253da04816fc124b8d75963fa9780c4d5,0xf85db1c273964a0f12d8a9c407b65f5ad7c8b260319f5c36a20f4179b53fca3d90f16cb0df4b386df8247a1f578492,0xf257adb1c486390f83a9512c64d07f2b6ac8503d917f7340c5bf56d14b3f42a18b9f9613c7fb0829cfd5a062fd8a47,0xf061a2b7593d4c8f8a9d1702c635bf4b90ca5681372f628347adf51bc78fd05297fdb6912f48d5c9f30a41cf640b3a,0xfd642831a09c75bf05c84719a3d2bf4da59b1c27360fa70cb61d8f20394ca65fc629d7b43f53b81fd085f6978f2a41,0xf620537ad84bc91fa568c2d479031fb64c18293a075f9a41587bdfc63b08a27fca6049b83f1b2596d7f3421df0c5d,0xf92074c853bd6a1f7b842c690d5a3f6b950a7d281c3fd38ac7941f5271680bcf51264ad87fa2b5604d9f31b4f0c93,0xf95cb41a387206df2b35640ad791cf490bd857312acf8b615d39cf2d47c05a6f29a4807b5f71d03428af81b96f3c6,0xf971846bc2d03a5fadb194708625cf4b7d1c836a290fa82431650f2b935d6c0f14c7a9d85fb8721a4d3f69c375b0,0xfb46508da12c397f514c9a203bd68fa0b1d7349526cfa870d91cb6f471692d5c8f27c09b8f3a5b24df3604a75f381,0xfb14c58da796302fd9150a27b3486fd4b560817c392f38b04a57d1f3acb9470d5fc873db6a90f8a1c642fc952f612,0xfd4752b3168c90afd142a796cb805f06d9537b18ac2fa40382d719f3a651c0b49f21a5870d36f27c46b9fd843c5b,0xf31d7046c82b5a9fb852c947ad603fb0d841275c369f0268a4c195f379d561bcaf1783d24b6af1534db7c08f90a2,0xf2b563914d87ca0f52cb481d7a690f79c1640da538bf72a4c3b6085f49bd307f2d9a134f15d6c0bf268c59f173a82,0xf7264b950c8d3a1f35c6a087bd294fb2a970d1c3865fac904851b6df169d7528a4fd4203bc7a5fc47360b812f319,0xf2a36174d908cb5f130469b82d5caf9506bd73c214af1d6c42b7a85f70d86293b1cf7849c0ad35f19720b438f65a,0xf8b09714c265d3afcb30a58d12746f50d493c87a2b1f359ad6b7084fa19c5bd2836f024ac137d96f257c04b9f186,0xf416b95378dac02f5b0697c12a438fd1b3628c475a0f081a6db2c39f4651729d3a8f91304bc5d7af86c94d2507b,0xfa0d639cb715248fc7d8b59643a20fd5031b2c87a94f6c53d1270b4af8574c16f81ad973f041926fb3ca56fdb9082,0xf53149b0ac7d682f7b8c650219d4af0db5c26a93718f8724b69c15a3f16075daf0c36479f304cb1dfa843b2fd2958,0xf6c9257418bda30f8d16a537094c2fa7139b68c5d04f7b1ca0243d69f850cb2d4f780b3cf51264bf59a836fa19d72,0xf8c13b950d7264af430c97521b6d8f5c3adb7192406f582d947ca163f70b415d38fb2a6c4d18f37a5bc209f0a968,0xfc4b60a2597d831f18475b0d6ac92f58c039d264a71fdb7368a5c204fda3490728b1f6cb2419fa1653b9f3d5087c,0xf5721849cb60d3afb1503c6a742d8fadb7968534c02f3b2591d4a807fb9d78c261a0f31c5d640928f14b5639ac7,0xf71bc8a265394d0f27c5d6a3419b0f52d184a7b6c90fd874c360a12bf83164b579ac2f58b37d9fad30c15f086924]

def e14_31 : List Nat := [0xf6a820c7bd59314f6871c524ad9b0fd4c380a5b2691fac851b6d2749fb40d812c9753f348bc61af73092af3d7056,0xfd41293a06c785bf9b8c16a720d35f731804b69a52dfd150b384ac26f24657bc3091af174c9da82bf368d5c0794,0xf072495d1a8cb63f9a08261bd74c3fc7b0485192da6f2a50c9b86d31f0d81c57a43b2fac25b469783f609d41735,0xf7d6429ca081b35f1a28c0b743956f0d13a9784b5c6fad94152cb836fc4d8a719b203f704a586bd21cf3d509627,0xfdb259381c460a7f2c36b8a50d491fad3480926c7b1f2786d53a9bc04f4730b51f69d175f3b4a61fc82079fac58d2,0xf6cb2a781d90534f028b6da3c5914fd5126a9c7b384f694ca0b5713d8f065a1bdf61c0793f7d29b4fc80372f4258a,0xfb7ca92518364d0fb427305a68d9cf1d34a795b6c02f691a2c8b35740fb13a07df84c56dafd587162f82b90f93c14,0xfb1c3079a62485df3a40d8729bc56fb743802591ad6f9d137a2b860c4fac814b5f2d39c71f82c690af7d4615f0b35,0xf6308db7c2941a5fc64d970b21385f8a62d05bc3917f9681b4720ca35fd5284a73fc906b8fda24c1f43b9a0f516d7,0xfcb7a4693821d50f29185ca3074b6f4865ad371c9b2fa8d9725b314c6f2c87d61b0f63490fdb804fa2d0f53c7f951a,0xf21db3c097485a6f39cb0d751a246f5b9137ac804d6f8b43a9d205c71f92b70a416f2c495387f8d306f528adf1b6c,0xf380ac712d6594bf7d43c5a9618b2fa379d58260b14f870cb91d36a24fd8a751c6bfd09c2531af047b5f4c86f3920,0xf492516ca7d8b03f093bd5c8a1246f279a5bc1486d0f26591b780c3daf58369d4a0f73182b9c4fb40753a6fd2c71,0xf0da16b84c29753f9b2805c1d4a36f8c3b074219a6df0ca25641bd739fd38627c95fb7813406cf2d94b58a0fa517,0xf7d8043bc652a19fb1429387c0da6fa9073d1c5b284f27ac49bd58130f7b0a8c9d61f69512d4f2c3a506f8b47536,0xfc260943d185a7bf7038a6c5db219f659208b1a4c73f47152d69ca3b0fb64278c135fb4d750c39f8416fd0a9fda28,0xf150d68c4a93b72f841975bda2c60fc90b1a37d4265f8163c7a5d9402f47831d29b6f3596a0cb4fd8ac1703f852b,0xf63db71425c80a9f726c1a30485b9f5d820cb46a731f83b0d4ac21657f392b681da5f8b194c7d2afc347059f609d,0xf47156a29c3db80fc87b0a94d2135f42038ac79b6d1fd7a4391bc2860f8461c073b25f7263ad5f096c4b5f9d81a5,0xf5b2643870c1a9dfd152a3b6c9408f7350a419bc82df4c7a8bd395612f4729063c5adfb0317584fac20d6f7b1869,0xf6b385027d1ca49fc0d362b7a9514fb8c2a6134d579f4b0ad65c37812fd847c603a19f9cb1708253f2db5a86409,0xf36571b2a8c49d0f53bc14869027af39c7d521a64b8f42d8597316c0af2805ca3d6b9f4d15b7062c3fa918740bd,0xfad9b873460521cfbc8d631a75924f6280a5db1793cf683a4d072b519fc7b03d1849a2f7d209c4f165c04f6a853b,0xf9420cb6537a8d1f4da9b5c172836f2c390784bd5a6fc92d7b85031a4fd6ca340b2159f860d3b1f257c80af97416,0xfda1784c925603bfb5794a2d3c816fcb46280d5319afc51d968340a72f8d70c142b93af736a590bf2058b1f4d6c7,0xfb1c24968d307a5f875c9d0b43a61f47bda2193c650f2bc71d63584a0fc4d738a15290f8062d59acf46b31f8b972,0xf50b29c87d643a1f8b60497a5c31df4d08a2c639b71f95b4ad38621c0f7482dbca9653f24c7581b30f5270a619d,0xf8742903d5a6c1bfc71adb5360284fcb2d64957a318f9b04a2c561d73f3ca9158d07b4fd9c083b6214f50a86972,0xf9c72b8a0314d56f0c5739a4821d6fc43b785209da1f0b4638ca2d795f7086bd3c2491f8d047a35bc61f6a51b92,0xfc5bd4293a06817fd9b8c2075a146f503b491d872a6f15d3cb7904826f0b695837ac12dfb2531f9a80cfc436fad74,0xf27590ad81b63c4f3a86125bc7d94fb3840d51a9c62f5a70c14bd3928f0b731964d2ac8f471d6af78b9f0653f05c2,0xf7d6ca0953b2481f4a3d827065bc1fda63879150c4bfa5861b0d439c7f9a208c5d13746f621a8bf257b9df2c3049,0xfb390d47c65a218f2915cb0736d84fad2587b6943c0f6ac957d314b20f682c179db53a4f27a9b16fa1d508f04c83,0xf86b1ca3d792504f5a028d471396cf9158a6d072b3cf214357a9db806fd1a2c490387b5f8164b0cf73659bcf4ad2,0xf43a9cb0586271df7c135b92a6d84f2c4a09187d56bf7369da8c0251bf7940d38216c5afa142db3cf8064bf95703,0xfbc80a7512d4369f6b4c719d38250f2953ad1c0b846fd0279413b5a86f7db16a4039c58f5d81a2c6f73ca90fb742,0xf8213b0d74c9a56fd637590a41c8bf2517cad48069bf5d3920c6b7a18f91b43a2c5078df1d24038a6f49726fcb53,0xf026b3d157a8c94f90da381b74c56f4b806d5972c31fbc036a917824df35a0b21c648d9fa29b50734fd25861ac7,0xf6a7438dbc59021f4c8063d29715af37d69b2a14850fb5d931827c640f3a9c1d426b875f2c3b70a865fdac0f4b19,0xf72c9b4d816a305f8b3947c156d20f831b607d95ca4f8cb791263d0a5f8a73c0bd14692fc6871ad524fb53409a2]

def e14_32 : List Nat := [0xfb162703ad59c84f50d7914a68bc3f064db21a5c738f1d6924c0b57a8fd2ca0471563b9f31c6b782a94f0258d39,0xfc712d603485a9bf024c6a78d395bf862974a0d1c3bf2c08a1649d57bf2563814d709caf728c504b6913f351bda,0xf8a4930d2c7b561f57a3420c86b9dfb850ac31296d4fc52ad783b1904f51d807362bc9af972841c60bd35f71a64,0xfd7a86921b53c04f18264adbc75093f0a58b3f34708f6b973fd19a3fca278f4c6d8f152b7f0614bf5c1a6f95d24f02c9d,0xf849305b1c26da7fc685a3d2140b97f74a8c92bf538d19a2f0d46acb8fbd7165c4f5963c0a1f09d573b6f81342f027,0xf5b7c0d48a39216f471c285a09bd36f68b13570f25d830b6fcb2da408f5c349720f9a6d7815fca241d96f19c4b37a,0xf29c5a07d1463b8f8a2d31597b06c4fa1bd87526f374d5618f9bca40d6f9a720534f917c03adf3c2b5809f1c86b42,0xfc5b71d29a80364f915d726ca38b40fa570db9c2f8d396a1bcf481c356daf9d413b685f52b0f6120f4782fc7a0f3497,0xf612d43b85a7c90f795286b413dac0f0a8c1d69bf24a365bd0fc46a9d753f2c5d8471af50837291f4930f1b78f2bc6,0xf06b43581a2c79df5127a830bd46c9f478629b1cf41d80a369fd2b840716f573bc824af5cad3902f56a913c0fd7b5,0xf149d3b8c06a752f48190b2ad7c356fb9742d5a1f83a4072c5f0a82634b5fcb68d029af6db78039cf5961fd4c1f731,0xfb5a036c2d81794fa41bc39586d702f153748062f0913a8b64f7a9c05d38f75c16ad0bf1ac72569df8c4db92f3b24,0xf1c92b650437a8df9a21487c0b5d63fa1694203dfa095c6813f27b3c85a6fc2d071b4afb8251974cf538064d7fd9b,0xfc0859d3a4627b1f12b04d6973c8a5f7168b5c42afb65dacf350a6f9281af0d7c6f9302cf78d25f49138fbd143f74b90,0xfd19a74c283b065f487352ac16b9d0fa3cbd64120f8b2496ad7cfd30758fb1805fc9715fa4395fc6290f7b4d2f368a1,0xf1b9c2a06375d84f69d4703bca1528fa72b61d0c8f35b819ad7cf64b713a592f4c5802fd6c12f390bdf4056af97834,0xf190d346c28b5a7f80726594b3ad1cf38db9c0a41f84d516379af7d9603cb18fb04c5392d6f7ca124f2586afb7502,0xf8c9d6a74b20315f918a462c7b50d3fbd1c069273fb942a07d56f09ac4d821bf041ad25978f57168bcf35af843f6c3,0xfb3417c69058a2dfca70d953861b42f0b8c3a4d12f1a5bc94803f15da60c478f7b640a91c5f2793d65f37d826fb92,0xf81426db7539ac0fb204365a1d87c9f17258ad96cfd3795b84a2f47a0b6138cf5d03b46821f1bc507d49f3c2906a,0xf26b14390a8d5c7f96185b7042ad3cfc17d63a59bf519208c473f257a49db31fd0b46879a1f056ac2d483fc60f2b8,0xf37920d1cb48a65f814c3d5b7a9062f05c9163a24fb934680a52fdac2178b69f8d6c703b15fc0bd74a138f4d2759,0xfd8736520bca491fa958470c62db31f6ad534092b8fc2179fb14c7f5b61cf83051f80a3cfa8275f46d9bf3d069fd42a7,0xf1b04d69a782c53f2650d791c83b4afb72d158039cf4ca57368fc61a0743f0c712946f8b209d3af59bd8142fb5da6,0xf253c40918b6d7af2d5a1c64379b08f7158a03d92cf48c5b1d02f94b70cf638750f62b395fd86acbf1274a3fda9614,0xfc5278a39d60b14f6379248ca05bd1fb382a5746c9fd80c19a43f5d094b713fa702b8651f4d7c30f269581fc2da6b,0xfc5a6bd20387914fd4a0736cb92815fb1a7c346258f27486093bfa80d94213fc04b53da2f7d1c9650bfa95716d8c,0xf8a50643bc97d12f856a7b42c13d90f370b694152afb8d2617c35fa0291f4db9afc86daf30c59fd5740f872b1f6c483,0xfd3187ac0b56429f91b85c2a347d60f72da0863c9bf026a8c4937f3596c140dbf4d128f5a4b2f1579af16bc7f38d50,0xf0b5c14738d629af806b34c21a59d7f463cb85790df7bda396150f84a7c025d1f04b9c8a653f72d31fca286f2491b,0xf12083d7469bca5fda906184c53b72fa05b1492c87fa8b624d071f30b286d1c7f579c6a34bdf5913c04a2f5639d8,0xfa964cb5d072831f208ad41b795c36fc7568d12b09fc05a48bd91f7340ac2581f74b392d6c8f306b942a7df53a61,0xf3d024c857b9a16f4db3c7a2518096f83a0b471956f5da8431c92bf21b6c037f5cb8d140fc287935af07d26fa49d6,0xf93a16d5827cb40fa9c4217056b3d8fc31b8629da0f418c5bd736af96087a2d4f30b259748fc19b75346fd15ac20,0xf7b265c4a3d1809f74b8a20c639d51fad4259603b1fb0a619c857df9a78d05314fb6482ca5fd21c7386f43cb9270,0xfa13d48b65c9270f35d64ca7b28190f49d85a3b120f7d2c3806a41fc0bda257396f74b59a8fd150f68c1f2634fbc79,0xfc2708643d9a51bf84a7c956d1302bfb73812d04c6f5db396a178cf9b58ad74260f9752a361fc14b0fa053cf4d829,0xf147ad09b28653cf9d8042716b3a5cf19a6d3057cbf85b702a496cf793460a125df87362951f2d138acfb0c4fd48b,0xf395270d84c6b1af135bd264ac9087f573b068a92cf024b91c36d5f0c82b796143fd7cb812af049d385af651d47a,0xf7b0956c24d81a3fd351cb86470a29f7d5c40628a9f4b50d63c871f257c084a6bdf9ca583b216fda720391f9431b]

def e14_33 : List Nat := [0xf509a263b1d8c47f186da520bc7349f5c38714a069fb56a82c1304f5846b7d21a3f6ca72b80d51f079cf24d9fbd39,0xf50db92ac714386f6b1572d94c803afc04b5a8d731fd397846cb0af6253c91d470f5d63b7a182cf16958b2f9024a,0xf9642b3c5081ad7fa0db58349261c7f902a3517b6cf06573d8a4bcf28b0314d9a5f2d1b9368407f2195d6acfc478,0xf1296b4ad0c7583f6d1b087a249c35fd2c1a504793bf62b5d3a81f417b82036fcb91527d8f9d4370ac5f09a6fc486,0xf1942578bd6a03cf7b1a265d9c8043fda3b9206c514f0b638a71df5864a90cbf8d2705961f7482ca539f3d7c4b21,0xf153c79bd4026a8fc5a378d2b41960f8cad7b652430f64cb572a938f9470d31c2f50a128fb17a48f95d16cfb36d90,0xf846db03ca75921f2715c490da38b6f1a05d3968cb4f2c785316a4df347d9b206f73b1c9a80f7b5a28d19f56c042,0xfa2cb049d358617f7ca306951b4d82fb78465c1a902f2418b97da05fdb574a6c392fc9126b380fa5d0734c8fd631,0xf9741a083bc25d6fb7d1c58a263940f9ac4278650dbf13c6b84da57f302816a7c95fd291b4370c8f9d3a460f12b5,0xf7a5186c309b4d2f69c178d5b340a2f48ac0752b639f2cb0d9a6531fdb14297c806f8374ad19502f8b7d3a164c5,0xf35bda196c87024f47b9a6250c3d18fa294036d8bc7f5c4b13a8609df85714d0f3b2d7f93827f65a0bf61ca4fc9512,0xf56841b7ac203d9fa26b4d087135c9f75d18a0c3469fc4a15bd60738fc639058d21f16ad729fb9428fb3a52f7cb04,0xfa9b35d84c62071fd29c3a57b80416f865c127d930af0bd47963852cf2b194378caf05b642813dfad15906f4bc7a,0xfd0574c316a928bf1873d942065acbfa725b4d69c80f04ad15c26397f2d71a3586bf348d591c7bf0c6412a83f9b0,0xf735c902461b8daf5062d9b3c7148af4c18307d659af5db634082197f6c0a1d47b29f58cb0d3a2f872ca6fb51394,0xfd2acb487195603f9240a358d1c7b6f73b14d026c8af0743c218b5d9f08361adb9c5f682b0c4975af31527d64a9,0xf4b13ca659d2708f3b052c6d49a178f147d0c9b5826f8b60a421537cf964302a81d57fa5cb7fd392bfc4091f8da36,0xf093715cb84da62fc406b1953a78d2f75861db3c0a4f6c8a9b07d314f69d0381ac7b5fb436d52f1c942fa5082f927,0xf5d63784b92a0c1f27c4a685b039d1f83cbd7425691fd8c2057a1b34f2b807953dac6fa82d09c5f049a316f7b641,0xf9d17ca4260b385f3749682b5da0c1f6c3905a2db41fcb87a6d40352f3a9b70d8c564fb63d72081f84c9751af219,0xfc615829a3b4d07f1c30b7462d8a59f906d781352a4fad571b9c0836fc20a143db865f5b6937ac40f21d97f42bc8,0xfd71a39c04826b5f0618cb7a243d95fa46d19b87c25f74ca92db0315f270ad49683b1f856c14b20df908a637f3c5,0xfd17b35ac842906f9c168372b4ad05f52a087c439bdf7964d2c51a30f8d7a9413620bf0c6a81b574f3d912856bc,0xf68d2049b35c7a1f9703cad48b5621f0d64a928571cf8052a34b69d1f8a0b27d59c63f906a51bc473fd3142c87b,0xf4a50912db386c7f043d6182ac579bf806a72c39d5bfc0ad8465137bf8a924c1d7035f20d49c871a36f2596bf1b4,0xf31b02da648759cfc42a73d96b8150fa1db72c85340fd8a39b216c70f8629714d5b30f47d63825c19afacb49065,0xf24ca60d795318bf1bd372c085a496f705628a3c1d4bfd9cb036f6b9048f3b5c64f9a7c83f12d874fa2915df17520a,0xfd28a539c064b71fcb37d04a956812fc69431b8d5207fa38742b0f5b903da7fc8051a63f4db61c58fca26d914f972,0xf8b65a9d12c0437f3c5972648da1b0f63d52a4b7081cf3bca0d475f90682d7c4f16db9c8a7f2b50f9142f3158f396a,0xfd95827a1340c6bfda0b49217368c5f2b3d6097c14a5f74208a3cbfd84ca9162f18703964dfa2c9b156f38b5f0d75,0xf96ac812d04735bf7a28b0c1943d65f385adb729c461f078d93c26f71a48025cf903b241d7fcb159a36f4d50a86b,0xf25a3740d69cb18fc4d853607b92a1fd395726b08a41f465c2b319f09a7c38b5f4bd716a02f879dac034f2d51fc86,0xfd87c9351a6240bf2d746ca3b19508f943d1270c8a5bf84bc29061f37b20ad68f17569a4c3f5c14d97a2f85d036b,0xf90374b816ad52cf8c5a40d36912b7f93a84c62d150bf75b14380caf792a06dbcf24958d70f1c3b6827fa13564d9,0xf41752936d0acb8fd813c5094b627af3b79d5a2460c8f3a9c1b087df4c2035691afc704d2b516f59bd128f68af734,0xf3d19a2b57486c0fda6b704935c218f6924c7a831bd0f78b0264ac1fbc9736d514f90a1658c3bf5a34d72f59d280,0xf62819350dbc7a4fc3b6a85209d714fd2a1b03865974f8706d1ca34fb75c63da04fc2169a5b80fd51372b9c8f924,0xf56c74028a39db1f21750a638d49bcf0d62a735841c9f3d725ac0861f4b79603cf8c592b07f5d19a43bf81ad246b,0xfc094d1a6852b37f20b53d6487ac91f9b615d72804c3f07bc2695a83fa36c8b42d9f14792a065cf1bda43f750d81,0xf3795adb4860c21f850b2ac347d961fc4153a6d09287fc63d25b70a1fcb394d80265f5724a91dfb9c83046fb8a71]

def e14_34 : List Nat := [0xf41d8a53c6b7902f60a49c8371bd52f95c08612ad34bf0b82d47ca15fd04c2b39187fa6485bc1307f96572f36d9a,0xf15863c420bda79f294305b18d6ac7f08a5c612b9374fb7d062a1384f1c825d3a907f9653bc0a41dfb64d2c9578,0xfd80697cb2435a1fb41c28657a903df8b0471639d52af46ad0783b129f8ca0591f5b6d48f3a4c51f27b9c6fd73c02,0xf21b8697d53ac40fa52748c9d3b061f43c28057a9b6dfb4956c7830adfc58d2a631f1937b24a8f26415bc09f71d0,0xf908d47ac52b316f30b15872c9da46f9a60537c82d14f975d6b8420a1f621c43d07b5fc683a29b40fbc395a817d,0xfda824097c1536bf39d25ac6480b71f572a43c968d1bf56a702914bc8fa37d4950621fb9a0d5c4783f03d618b2c,0xfc81642a97d503bf08d39b6214c75af528ad0473691bf729d1c653a4bfc5902d6a7843f138b2caf068517fc94db0,0xf7b61ad84035c92f78ac265db41390fb12857a36c4d9f952bc7381d06fa9715b8c3420f91c0b3d6a4fd2a508647,0xfd7094b58c36a21fb052416ca8d937f746819c203d5af8265cbd04317fb951c4806da3f538b69a4d27f1b297c0a,0xf4ac791b36d5082f17b6a835c490d2f3c6872a59d4b0f5731840c9b26f0641a7db58c2f1cb8d3470a96f93ad152,0xf314c062b7d859af0a1d29c378b564f12ca63b4d9057f8420397c16bdafa5d694f186cb9f08c51bf38270df52a743,0xf152c748b3a0d96f0839b71ad264c5fca8d36b072419f4bd1c6035782afa794d56f8c09a5f3186d7f02bc34f21b59,0xf631b72c09584adf81d9b534c6a702f429a06bc5173dfa5d78c93b4621f57ca30bd2f83c19740dfb8a2f6149f6508,0xf1b9586027c43dafa40cb7938d2165f9053a71d46b82f2b0a819c5d736fd6a2c875bfa9d03b41cf496c3152f0748,0xf6c852a31d074b9f7b8143ca6d5029f273651a9480bcf4c7862bda5390f38a4d95c0f7d82461b5fa06b3d217f1c9,0xf1b08759c6d243afca82bd07493165f046bc8192a7d5f263b58da4c790f9a6035217bf3869d1c27f0c3d415af8b4,0xf3c1a95786d420bf4a3d82c79605b1f7b29cad516380f0c58134b6a7d9f739bc640d1f5621948a03f2db8c47f25a,0xf605b97ac43d128f572b831a0d46c9f08a6d53b1742cf851407c3a96bdfb78c192da4f3625cb09d7f165a203948,0xf4a71bc269d0538f463db8c9a12570f685b97d2413cafb06d594c18273f20c7b4d165af2915c6bfda3908f3478a0,0xfdbc1583a694702f93c68da175b240f130c5d4629b78fc84a9d0b35612f7a59c41b63df8250ac734bf6d1972a80,0xf496b5d83a072c1fb30264c75a819df9bc6134052ad7fd421a7b8c0653f71d09a63c58f7486d2b1593fa4b0829c,0xf5db4916c03a782f3d926b1ac85074f860ad4271359bf5b7d08364c12afd2b0415c79a8f184a6df9c3756fc2093b,0xf46c92d37058a1bfca4062759d138bfb5a6d82179430f61c52480d7a39f5368147c20adf519a2b6fd4c87bf0c3b9,0xfd7a39bc8246150fd56ca17290348bf140638d2a9c5bf2c74a6d319580f3578ad49621cf681d973bf70c4bfa52b0,0xf83429615c07bdafb872506ac3d149f9d64c7a30b285fb481c90a2d573f1974d08cb653f639a5b12cf86204a17d,0xfa9b0c26d784351fc3720a59db8641f394a825cb60d1f4d297b563ac80f8d57c4216903f9c6ad3b471fa2b18507,0xfb1d2c590378a46f38da562197c0b4fdb58c92a36074f0a9b7d513c682facb3d9425081f53961c48b27f0d6a714,0xf9bc08da3614275fdb2815c9a06437f8b56a2d4c1397f85d3b1ac20496f8c6d9035217afd1926b483c70fa47b05,0xf84a930c57d126bfb73495a8c20d61f51c64db97a382fa65bc9d804271f096358147ca2bf3d291f6078fda05f3c4b,0xf316b8ac49025d7f865b914a2d3c07f8150a729d63bcfc935a60842bd1f9a30b4d826c57f40da17f596438f1b7c2,0xf3b2708da9c4156f92c5d1a68b4730f87d0a46c19352f43d961b58a7c0fb95713ac842d6fbc38120f05a26fbd497,0xfd30649725cb81af56db3ac2487091fa5b08369d4c17fd02a47c935861f0c8d59a62b734f0a82d75f6c314bf29b1,0xf2537c1a08496dbf5da39268c4b170fa51d2043c9b87f246bc0318a957f1285b3d4ac609f9d836147f6a2c5f7b0d,0xf850917ca243db6fb9382d74a0c615f7948b1c560da3fc314b25a708d9f1203b75d64c8af1d40bc278f6953f29a6,0xf4d50b16a79c382f317294ac0685bdf62d951403b87cfa0912bc47356df81c2075a936b4f7b9643a8dfa25c80d1,0xfbda865c7092413f481b2d60573ac9f6b7408c21a539f1d0cb462a7859fd5b0271c4a638fb82516c3d9f4d79a03,0xf6d1582794a30bcfb1a95c0873d426f652d831ca09b4fd063914c2a75bf9c86ad5340712f7d9618a502bfc3b847,0xf9b8d21a0c65734fad60352481b79cf5a729631c4d08f2bd7409516a3cf64a9d1705b382fa20b4193d5c8fbc786,0xf079d81c46a253bf9ad157483026cbf4b29c860d371af41b8095c72d63f8249613ca05d7f04db658a3912cfa5b7]

def e14 := e14_0 ++ e14_1 ++ e14_2 ++ e14_3 ++ e14_4 ++ e14_5 ++ e14_6 ++ e14_7 ++ e14_8 ++ e14_9 ++ e14_10 ++ e14_11 ++ e14_12 ++ e14_13 ++ e14_14 ++ e14_15 ++ e14_16 ++ e14_17 ++ e14_18 ++ e14_19 ++ e14_20 ++ e14_21 ++ e14_22 ++ e14_23 ++ e14_24 ++ e14_25 ++ e14_26 ++ e14_27 ++ e14_28 ++ e14_29 ++ e14_30 ++ e14_31 ++ e14_32 ++ e14_33 ++ e14_34

end AlspachSmall.Packed


namespace AlspachSmall.Packed.Fast
open Bitmap

private def edge (x y : Nat) : Nat :=
  1 <<< (if x < y then y*y+x else x*x+y)

private theorem edge_eq {n : Nat} {x y : Fin n} (diff : x.val/2 ≠ y.val/2) :
    edge x.val y.val = 1 <<< key (x,y) := by
  have ne : x.val ≠ y.val := fun h => diff (h ▸ rfl)
  by_cases h : x.val < y.val
  · simp [edge,key,h,Nat.min_eq_left (Nat.le_of_lt h),Nat.max_eq_right (Nat.le_of_lt h)]
  · have lt : y.val < x.val := by omega
    simp [edge,key,h,lt,Nat.min_eq_right (Nat.le_of_lt lt),Nat.max_eq_left (Nat.le_of_lt lt)]

private def bit (x : Nat) := 1 <<< x

private theorem bit_self (x : Nat) : (bit x).testBit x=true := by
  simp [bit,Nat.shiftLeft_eq]

/-- A cycle suffix returns its seen vertices, its edges, and the number of vertices
including the start. Each edge is computed when its second endpoint becomes known. -/
private def cycleTail (n start prev : Nat) : List Nat → Option (Nat × Nat × Nat)
  | [] => if prev/2 = start/2 then none else some (bit start,edge prev start,1)
  | x::xs =>
    if n ≤ x ∨ prev/2 = x/2 then none else
      match cycleTail n start x xs with
      | none => none
      | some (seen,mask,len) =>
        if seen.testBit x then none
        else some (bit x ||| seen,edge prev x ||| mask,len+1)

private theorem cycleTail_sound {n : Nat} (hn : 0<n) (a p : Fin n) (xs : List Nat)
    {seen mask len : Nat} (ok : cycleTail n a.val p.val xs=some (seen,mask,len)) :
    chain p a (xs.map (vertex hn))=true ∧
    ((xs.map (vertex hn))++[a]).Nodup ∧
    (∀ v∈(xs.map (vertex hn))++[a], seen.testBit v.val=true) ∧
    bitmap (arcs p a (xs.map (vertex hn)))=mask ∧ len=xs.length+1 := by
  induction xs generalizing p seen mask len with
  | nil =>
    rw [cycleTail] at ok
    split at ok <;> rename_i h
    · contradiction
    · cases ok
      exact ⟨by simpa [chain] using h,by simp,by simpa using bit_self a.val,
        by simp [arcs,bitmap,edge_eq h],rfl⟩
  | cons x xs ih =>
    rw [cycleTail] at ok
    split at ok <;> rename_i cond
    · contradiction
    · have xb : x<n := by omega
      have ne : p.val/2 ≠ x/2 := fun e => cond (Or.inr e)
      let v : Fin n := vertex hn x
      have xv : v.val=x := Nat.mod_eq_of_lt xb
      cases z : cycleTail n a.val x xs with
      | none => simp [z] at ok
      | some t =>
        obtain ⟨s,m,l⟩ := t
        simp only [z] at ok
        split at ok <;> rename_i seenX
        · contradiction
        · cases ok
          have tail := ih v (seen:=s) (mask:=m) (len:=l) (by simpa only [xv] using z)
          obtain ⟨hc,nd,bits,ar,leng⟩ := tail
          have ndv : v ∉ xs.map (vertex hn)++[a] := fun h => seenX (xv ▸ bits v h)
          have neigh : p.val/2 ≠ v.val/2 := by simpa only [xv] using ne
          change chain p a (v::_)=true ∧ (v::(_++[a])).Nodup ∧
            (∀ q∈v::(xs.map (vertex hn)++[a]), (bit x ||| s).testBit q.val=true) ∧
            bitmap (arcs p a (v::_))=edge p.val x ||| m ∧ _
          refine ⟨by simp [chain,neigh,hc],List.nodup_cons.mpr ⟨ndv,nd⟩,?_,?_,by simp [leng]⟩
          · intro q hq
            rcases List.mem_cons.mp hq with rfl|hit
            · simp only [Nat.testBit_or,xv,bit_self,Bool.true_or]
            · simp only [Nat.testBit_or,bits q hit,Bool.or_true]
          · simp only [arcs,bitmap,ar]
            rw [←xv,edge_eq neigh]

private def rows (n : Nat) : List (List Nat) → Option (Nat × Nat)
  | [] => some (0,0)
  | []::_ => none
  | (a::xs)::ps =>
    if n≤a then none else
      match cycleTail n a a xs with
      | none => none
      | some (_,mask,len) =>
        if len<3 then none else
          match rows n ps with
          | none => none
          | some (rest,total) =>
            if mask &&& rest = 0 then some (mask ||| rest,len+total) else none

def test (n mask total word : Nat) : Bool := rows n (paths word) == some (mask,total)

private theorem rows_sound {n : Nat} (hn : 0<n) (ps : List (List Nat)) {mask total : Nat}
    (ok : rows n ps=some (mask,total)) :
    let cs := ps.map (code hn)
    (pack cs=some mask ∧ cs.map (fun c => c.2.length+1)=ps.map List.length) ∧
      (∀ d∈ps.map List.length, 3≤d) ∧ (ps.map List.length).sum=total := by
  induction ps generalizing mask total with
  | nil => cases ok; simp [pack]
  | cons p ps ih =>
    cases p with
    | nil => contradiction
    | cons a xs =>
      rw [rows] at ok
      split at ok <;>rename_i cond
      · contradiction
      · have ab : a<n := by omega
        have av : (vertex hn a).val=a := Nat.mod_eq_of_lt ab
        cases htail : cycleTail n a a xs with
        | none => simp [htail] at ok
        | some t =>
          obtain ⟨s,m,k⟩ := t
          simp only [htail] at ok
          split at ok <;>rename_i len
          · contradiction
          · cases hrest : rows n ps with
            | none => simp [hrest] at ok
            | some v =>
              obtain ⟨r,l⟩ := v
              simp only [hrest] at ok
              split at ok <;>rename_i disj
              · cases ok
                obtain ⟨hc,nd,_,hm,kl⟩ := cycleTail_sound hn (vertex hn a) (vertex hn a) xs
                  (seen:=s) (mask:=m) (len:=k) (by simpa only [av] using htail)
                obtain ⟨⟨pk,sizes⟩,low,sum⟩ := ih hrest
                simp only [List.map_cons,code,List.length_cons,List.length_map]
                have good' : good (code hn (a::xs))=true := by
                  simp only [good,code,hc,nd,decide_true,List.length_map,
                    Bool.true_and,decide_eq_true_eq]
                  omega
                refine ⟨⟨?_,by simp [sizes]⟩,?_,?_⟩
                · change good (vertex hn a,xs.map (vertex hn))=true at good'
                  simp [pack,pk,good',hm,disj]
                · intro d hd
                  rcases List.mem_cons.mp hd with rfl|h
                  · omega
                  · exact low _ h
                · simp [sum,kl]
              · contradiction

theorem sound {n mask total w : Nat} (hn : 0<n) (h : test n mask total w=true) :
    Tested n hn mask total w :=
  rows_sound hn (paths w) (eq_of_beq h)

theorem all_sound {n mask total : Nat} (hn : 0<n) {ws : List Nat}
    (h : ws.all (test n mask total)=true) : AllTested n hn mask total ws :=
  fun w hw => sound hn (List.all_eq_true.mp h w hw)

end AlspachSmall.Packed.Fast

namespace AlspachSmall.Coverage
open Packed

private theorem includeSlice {xs ws : List Nat} {i len : Nat}
    (e : xs = keys ((ws.drop i).take len)) : Included xs (keys ws) := by
  intro k hk
  rw [e] at hk
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hk
  exact List.mem_map.mpr ⟨w, List.mem_of_mem_drop (List.mem_of_mem_take hw), rfl⟩

/-- Verified cycle tables and coverage for every admissible length multiset. -/
private structure TablesVerified : Prop where
  s6Good : AllTested 6 (by decide) (Bitmap.full 6) 12 s6
  s6Keys : s6.map sizes = partitions 6 3 12
  s8Good : AllTested 8 (by decide) (Bitmap.full 8) 24 s8
  s8Keys : s8.map sizes = partitions 8 3 24
  s10Good : AllTested 10 (by decide) (Bitmap.full 10) 40 s10
  s10Keys : s10.map sizes = partitions 10 3 40
  a12Good : AllTested 12 (by decide) a12Mask 30 a12
  b12Good : AllTested 12 (by decide) b12Mask 30 b12
  e12Good : AllTested 12 (by decide) e12Mask 60 e12
  a14Good : AllTested 14 (by decide) a14Mask 42 a14
  e14Good : AllTested 14 (by decide) e14Mask 84 e14
  cover12 : ∀ xs ∈ partitions 12 3 60,
    Covered (keys a12) (keys b12) (keys e12) (Keys.lengthKey xs)
  symmetricCover14 : ∀ xs ∈ partitions 14 3 84,
    Covered (keys a14) (keys a14) (keys e14) (Keys.lengthKey xs)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000000 in
private theorem verifyTables : TablesVerified := by
  constructor
  · exact (Fast.all_sound (by decide) (by decide +kernel))
  · decide +kernel
  · exact allTestedAppend (ys := s8_1) ((Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))
  · decide +kernel
  · exact allTestedAppend (ys := s10_12) (allTestedAppend (ys := s10_11) (allTestedAppend (ys := s10_10) (allTestedAppend (ys := s10_9) (allTestedAppend (ys := s10_8) (allTestedAppend (ys := s10_7) (allTestedAppend (ys := s10_6) (allTestedAppend (ys := s10_5) (allTestedAppend (ys := s10_4) (allTestedAppend (ys := s10_3) (allTestedAppend (ys := s10_2) (allTestedAppend (ys := s10_1) ((Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))
  · decide +kernel
  · exact allTestedAppend (ys := a12_5) (allTestedAppend (ys := a12_4) (allTestedAppend (ys := a12_3) (allTestedAppend (ys := a12_2) (allTestedAppend (ys := a12_1) ((Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))
  · exact allTestedAppend (ys := b12_5) (allTestedAppend (ys := b12_4) (allTestedAppend (ys := b12_3) (allTestedAppend (ys := b12_2) (allTestedAppend (ys := b12_1) ((Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))
  · exact allTestedAppend (ys := e12_8) (allTestedAppend (ys := e12_7) (allTestedAppend (ys := e12_6) (allTestedAppend (ys := e12_5) (allTestedAppend (ys := e12_4) (allTestedAppend (ys := e12_3) (allTestedAppend (ys := e12_2) (allTestedAppend (ys := e12_1) ((Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))
  · exact allTestedAppend (ys := a14_36) (allTestedAppend (ys := a14_35) (allTestedAppend (ys := a14_34) (allTestedAppend (ys := a14_33) (allTestedAppend (ys := a14_32) (allTestedAppend (ys := a14_31) (allTestedAppend (ys := a14_30) (allTestedAppend (ys := a14_29) (allTestedAppend (ys := a14_28) (allTestedAppend (ys := a14_27) (allTestedAppend (ys := a14_26) (allTestedAppend (ys := a14_25) (allTestedAppend (ys := a14_24) (allTestedAppend (ys := a14_23) (allTestedAppend (ys := a14_22) (allTestedAppend (ys := a14_21) (allTestedAppend (ys := a14_20) (allTestedAppend (ys := a14_19) (allTestedAppend (ys := a14_18) (allTestedAppend (ys := a14_17) (allTestedAppend (ys := a14_16) (allTestedAppend (ys := a14_15) (allTestedAppend (ys := a14_14) (allTestedAppend (ys := a14_13) (allTestedAppend (ys := a14_12) (allTestedAppend (ys := a14_11) (allTestedAppend (ys := a14_10) (allTestedAppend (ys := a14_9) (allTestedAppend (ys := a14_8) (allTestedAppend (ys := a14_7) (allTestedAppend (ys := a14_6) (allTestedAppend (ys := a14_5) (allTestedAppend (ys := a14_4) (allTestedAppend (ys := a14_3) (allTestedAppend (ys := a14_2) (allTestedAppend (ys := a14_1) ((Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))
  · exact allTestedAppend (ys := e14_34) (allTestedAppend (ys := e14_33) (allTestedAppend (ys := e14_32) (allTestedAppend (ys := e14_31) (allTestedAppend (ys := e14_30) (allTestedAppend (ys := e14_29) (allTestedAppend (ys := e14_28) (allTestedAppend (ys := e14_27) (allTestedAppend (ys := e14_26) (allTestedAppend (ys := e14_25) (allTestedAppend (ys := e14_24) (allTestedAppend (ys := e14_23) (allTestedAppend (ys := e14_22) (allTestedAppend (ys := e14_21) (allTestedAppend (ys := e14_20) (allTestedAppend (ys := e14_19) (allTestedAppend (ys := e14_18) (allTestedAppend (ys := e14_17) (allTestedAppend (ys := e14_16) (allTestedAppend (ys := e14_15) (allTestedAppend (ys := e14_14) (allTestedAppend (ys := e14_13) (allTestedAppend (ys := e14_12) (allTestedAppend (ys := e14_11) (allTestedAppend (ys := e14_10) (allTestedAppend (ys := e14_9) (allTestedAppend (ys := e14_8) (allTestedAppend (ys := e14_7) (allTestedAppend (ys := e14_6) (allTestedAppend (ys := e14_5) (allTestedAppend (ys := e14_4) (allTestedAppend (ys := e14_3) (allTestedAppend (ys := e14_2) (allTestedAppend (ys := e14_1) ((Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))) (Fast.all_sound (by decide) (by decide +kernel))
  · have halfA : missed 31 9 30 0 1 = keys a12 := by decide +kernel
    have halfB : missed 31 9 30 0 1 = keys b12 := by decide +kernel
    have exc : missed 30 9 60 0 1 = keys e12 := by decide +kernel
    exact fun _ hx => cover_of_missed (n:=12) (h:=30) (by decide) halfA halfB exc hx
  · have cover_a14_0_0_0_0_0_0_0 : Included (missed 43 4 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 7 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=0) (len:=63)
        decide +kernel
      · apply includeSlice (i:=63) (len:=38)
        decide +kernel
      · apply includeSlice (i:=101) (len:=23)
        decide +kernel
      · apply includeSlice (i:=124) (len:=13)
        decide +kernel
      · apply includeSlice (i:=137) (len:=5)
        decide +kernel
      · apply includeSlice (i:=142) (len:=1)
        decide +kernel
      · apply includeSlice (i:=143) (len:=1)
        decide +kernel
    have cover_a14_0_0_0_0_0_0 : Included (missed 43 5 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0_0_0_0_0
      · apply includeSlice (i:=144) (len:=75)
        decide +kernel
      · apply includeSlice (i:=219) (len:=34)
        decide +kernel
      · apply includeSlice (i:=253) (len:=14)
        decide +kernel
      · apply includeSlice (i:=267) (len:=4)
        decide +kernel
      · apply includeSlice (i:=271) (len:=0)
        decide +kernel
    have cover_a14_0_0_0_0_0_1 : Included (missed 43 5 33 1073741824 513) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=271) (len:=69)
        decide +kernel
      · apply includeSlice (i:=340) (len:=31)
        decide +kernel
      · apply includeSlice (i:=371) (len:=11)
        decide +kernel
      · apply includeSlice (i:=382) (len:=3)
        decide +kernel
      · apply includeSlice (i:=385) (len:=0)
        decide +kernel
    have cover_a14_0_0_0_0_0 : Included (missed 43 6 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0_0_0_0
      · exact cover_a14_0_0_0_0_0_1
      · apply includeSlice (i:=385) (len:=42)
        decide +kernel
      · apply includeSlice (i:=427) (len:=11)
        decide +kernel
      · apply includeSlice (i:=438) (len:=2)
        decide +kernel
    have cover_a14_0_0_0_0_1_0 : Included (missed 43 5 32 34359738368 1025) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=440) (len:=62)
        decide +kernel
      · apply includeSlice (i:=502) (len:=29)
        decide +kernel
      · apply includeSlice (i:=531) (len:=10)
        decide +kernel
      · apply includeSlice (i:=541) (len:=2)
        decide +kernel
      · apply includeSlice (i:=543) (len:=1)
        decide +kernel
    have cover_a14_0_0_0_0_1 : Included (missed 43 6 32 34359738368 1025) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0_0_1_0
      · apply includeSlice (i:=544) (len:=35)
        decide +kernel
      · apply includeSlice (i:=579) (len:=9)
        decide +kernel
      · apply includeSlice (i:=588) (len:=1)
        decide +kernel
    have cover_a14_0_0_0_0 : Included (missed 43 7 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0_0_0
      · exact cover_a14_0_0_0_0_1
      · apply includeSlice (i:=589) (len:=39)
        decide +kernel
      · apply includeSlice (i:=628) (len:=8)
        decide +kernel
      · apply includeSlice (i:=636) (len:=0)
        decide +kernel
    have cover_a14_0_0_0_1_0_0 : Included (missed 43 5 31 1099511627776 2049) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · apply includeSlice (i:=636) (len:=57)
        decide +kernel
      · apply includeSlice (i:=693) (len:=24)
        decide +kernel
      · apply includeSlice (i:=717) (len:=9)
        decide +kernel
      · apply includeSlice (i:=726) (len:=2)
        decide +kernel
    have cover_a14_0_0_0_1_0 : Included (missed 43 6 31 1099511627776 2049) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0_1_0_0
      · apply includeSlice (i:=728) (len:=31)
        decide +kernel
      · apply includeSlice (i:=759) (len:=7)
        decide +kernel
      · apply includeSlice (i:=766) (len:=1)
        decide +kernel
    have cover_a14_0_0_0_1 : Included (missed 43 7 31 1099511627776 2049) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0_1_0
      · apply includeSlice (i:=767) (len:=35)
        decide +kernel
      · apply includeSlice (i:=802) (len:=5)
        decide +kernel
      · apply includeSlice (i:=807) (len:=0)
        decide +kernel
    have cover_a14_0_0_0 : Included (missed 43 8 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0_0
      · exact cover_a14_0_0_0_1
      · apply includeSlice (i:=807) (len:=34)
        decide +kernel
      · apply includeSlice (i:=841) (len:=4)
        decide +kernel
    have cover_a14_0_0_1_0_0 : Included (missed 43 6 30 35184372088832 4097) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · apply includeSlice (i:=845) (len:=84)
        decide +kernel
      · apply includeSlice (i:=929) (len:=27)
        decide +kernel
      · apply includeSlice (i:=956) (len:=7)
        decide +kernel
      · apply includeSlice (i:=963) (len:=1)
        decide +kernel
    have cover_a14_0_0_1_0 : Included (missed 43 7 30 35184372088832 4097) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_1_0_0
      · apply includeSlice (i:=964) (len:=29)
        decide +kernel
      · apply includeSlice (i:=993) (len:=4)
        decide +kernel
      · apply includeSlice (i:=997) (len:=1)
        decide +kernel
    have cover_a14_0_0_1 : Included (missed 43 8 30 35184372088832 4097) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_0_0_1_0
      · apply includeSlice (i:=998) (len:=28)
        decide +kernel
      · apply includeSlice (i:=1026) (len:=3)
        decide +kernel
    have cover_a14_0_0 : Included (missed 43 9 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0_0_0
      · exact cover_a14_0_0_1
      · apply includeSlice (i:=1029) (len:=27)
        decide +kernel
      · apply includeSlice (i:=1056) (len:=2)
        decide +kernel
    have cover_a14_0_1_0_0_0 : Included (missed 43 6 29 1125899906842624 8193) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · apply includeSlice (i:=1058) (len:=73)
        decide +kernel
      · apply includeSlice (i:=1131) (len:=24)
        decide +kernel
      · apply includeSlice (i:=1155) (len:=5)
        decide +kernel
      · apply includeSlice (i:=1160) (len:=0)
        decide +kernel
    have cover_a14_0_1_0_0 : Included (missed 43 7 29 1125899906842624 8193) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_0_1_0_0_0
      · apply includeSlice (i:=1160) (len:=24)
        decide +kernel
      · apply includeSlice (i:=1184) (len:=4)
        decide +kernel
    have cover_a14_0_1_0 : Included (missed 43 8 29 1125899906842624 8193) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_0_1_0_0
      · apply includeSlice (i:=1188) (len:=25)
        decide +kernel
      · apply includeSlice (i:=1213) (len:=2)
        decide +kernel
    have cover_a14_0_1 : Included (missed 43 9 29 1125899906842624 8193) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_0_1_0
      · apply includeSlice (i:=1215) (len:=21)
        decide +kernel
      · apply includeSlice (i:=1236) (len:=1)
        decide +kernel
    have cover_a14_0 : Included (missed 43 10 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0_0
      · exact cover_a14_0_1
      · apply includeSlice (i:=1237) (len:=19)
        decide +kernel
      · apply includeSlice (i:=1256) (len:=1)
        decide +kernel
    have cover_a14_1_0_0_0_0 : Included (missed 43 6 28 36028797018963968 16385) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · apply includeSlice (i:=1257) (len:=67)
        decide +kernel
      · apply includeSlice (i:=1324) (len:=20)
        decide +kernel
      · apply includeSlice (i:=1344) (len:=4)
        decide +kernel
      · apply includeSlice (i:=1348) (len:=0)
        decide +kernel
    have cover_a14_1_0_0_0 : Included (missed 43 7 28 36028797018963968 16385) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_1_0_0_0_0
      · apply includeSlice (i:=1348) (len:=22)
        decide +kernel
      · apply includeSlice (i:=1370) (len:=3)
        decide +kernel
    have cover_a14_1_0_0 : Included (missed 43 8 28 36028797018963968 16385) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_1_0_0_0
      · apply includeSlice (i:=1373) (len:=19)
        decide +kernel
      · apply includeSlice (i:=1392) (len:=2)
        decide +kernel
    have cover_a14_1_0 : Included (missed 43 9 28 36028797018963968 16385) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_1_0_0
      · apply includeSlice (i:=1394) (len:=18)
        decide +kernel
      · apply includeSlice (i:=1412) (len:=1)
        decide +kernel
    have cover_a14_1 : Included (missed 43 10 28 36028797018963968 16385) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 3 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 := by omega
      rcases opts with rfl | rfl | rfl
      · exact cover_a14_1_0
      · apply includeSlice (i:=1413) (len:=16)
        decide +kernel
      · apply includeSlice (i:=1429) (len:=0)
        decide +kernel
    have cover_a14 : Included (missed 43 11 42 0 1) (keys a14) := by
      apply missed_succ
      intro c hc
      have hb : c < 4 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases opts with rfl | rfl | rfl | rfl
      · exact cover_a14_0
      · exact cover_a14_1
      · apply includeSlice (i:=1429) (len:=12)
        decide +kernel
      · apply includeSlice (i:=1441) (len:=1)
        decide +kernel
    have cover_e14_0_0_0_0_0_0 : Included (missed 42 5 84 0 1) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 11 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=0) (len:=7)
        decide +kernel
      · apply includeSlice (i:=7) (len:=5)
        decide +kernel
      · apply includeSlice (i:=12) (len:=4)
        decide +kernel
      · apply includeSlice (i:=16) (len:=4)
        decide +kernel
      · apply includeSlice (i:=20) (len:=3)
        decide +kernel
      · apply includeSlice (i:=23) (len:=3)
        decide +kernel
      · apply includeSlice (i:=26) (len:=3)
        decide +kernel
      · apply includeSlice (i:=29) (len:=4)
        decide +kernel
      · apply includeSlice (i:=33) (len:=7)
        decide +kernel
      · apply includeSlice (i:=40) (len:=6)
        decide +kernel
      · apply includeSlice (i:=46) (len:=1)
        decide +kernel
    have cover_e14_0_0_0_0_0_1 : Included (missed 42 5 75 1073741824 513) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 10 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=47) (len:=4)
        decide +kernel
      · apply includeSlice (i:=51) (len:=2)
        decide +kernel
      · apply includeSlice (i:=53) (len:=2)
        decide +kernel
      · apply includeSlice (i:=55) (len:=2)
        decide +kernel
      · apply includeSlice (i:=57) (len:=2)
        decide +kernel
      · apply includeSlice (i:=59) (len:=3)
        decide +kernel
      · apply includeSlice (i:=62) (len:=3)
        decide +kernel
      · apply includeSlice (i:=65) (len:=4)
        decide +kernel
      · apply includeSlice (i:=69) (len:=4)
        decide +kernel
      · apply includeSlice (i:=73) (len:=1)
        decide +kernel
    have cover_e14_0_0_0_0_0 : Included (missed 42 6 84 0 1) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 10 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0_0_0_0_0
      · exact cover_e14_0_0_0_0_0_1
      · apply includeSlice (i:=74) (len:=1)
        decide +kernel
      · apply includeSlice (i:=75) (len:=0)
        decide +kernel
      · apply includeSlice (i:=75) (len:=0)
        decide +kernel
      · apply includeSlice (i:=75) (len:=1)
        decide +kernel
      · apply includeSlice (i:=76) (len:=4)
        decide +kernel
      · apply includeSlice (i:=80) (len:=8)
        decide +kernel
      · apply includeSlice (i:=88) (len:=4)
        decide +kernel
      · apply includeSlice (i:=92) (len:=1)
        decide +kernel
    have cover_e14_0_0_0_0_1 : Included (missed 42 6 74 34359738368 1025) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 9 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=93) (len:=8)
        decide +kernel
      · apply includeSlice (i:=101) (len:=2)
        decide +kernel
      · apply includeSlice (i:=103) (len:=1)
        decide +kernel
      · apply includeSlice (i:=104) (len:=0)
        decide +kernel
      · apply includeSlice (i:=104) (len:=0)
        decide +kernel
      · apply includeSlice (i:=104) (len:=0)
        decide +kernel
      · apply includeSlice (i:=104) (len:=3)
        decide +kernel
      · apply includeSlice (i:=107) (len:=3)
        decide +kernel
      · apply includeSlice (i:=110) (len:=0)
        decide +kernel
    have cover_e14_0_0_0_0 : Included (missed 42 7 84 0 1) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 9 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0_0_0_0
      · exact cover_e14_0_0_0_0_1
      · apply includeSlice (i:=110) (len:=13)
        decide +kernel
      · apply includeSlice (i:=123) (len:=12)
        decide +kernel
      · apply includeSlice (i:=135) (len:=15)
        decide +kernel
      · apply includeSlice (i:=150) (len:=19)
        decide +kernel
      · apply includeSlice (i:=169) (len:=20)
        decide +kernel
      · apply includeSlice (i:=189) (len:=10)
        decide +kernel
      · apply includeSlice (i:=199) (len:=1)
        decide +kernel
    have cover_e14_0_0_0_1_0 : Included (missed 42 6 73 1099511627776 2049) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 9 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=200) (len:=17)
        decide +kernel
      · apply includeSlice (i:=217) (len:=11)
        decide +kernel
      · apply includeSlice (i:=228) (len:=1)
        decide +kernel
      · apply includeSlice (i:=229) (len:=0)
        decide +kernel
      · apply includeSlice (i:=229) (len:=0)
        decide +kernel
      · apply includeSlice (i:=229) (len:=1)
        decide +kernel
      · apply includeSlice (i:=230) (len:=2)
        decide +kernel
      · apply includeSlice (i:=232) (len:=2)
        decide +kernel
      · apply includeSlice (i:=234) (len:=0)
        decide +kernel
    have cover_e14_0_0_0_1 : Included (missed 42 7 73 1099511627776 2049) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0_0_1_0
      · apply includeSlice (i:=234) (len:=6)
        decide +kernel
      · apply includeSlice (i:=240) (len:=6)
        decide +kernel
      · apply includeSlice (i:=246) (len:=7)
        decide +kernel
      · apply includeSlice (i:=253) (len:=8)
        decide +kernel
      · apply includeSlice (i:=261) (len:=11)
        decide +kernel
      · apply includeSlice (i:=272) (len:=8)
        decide +kernel
      · apply includeSlice (i:=280) (len:=1)
        decide +kernel
    have cover_e14_0_0_0_2 : Included (missed 42 7 62 2199023255552 4196353) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 7 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=281) (len:=11)
        decide +kernel
      · apply includeSlice (i:=292) (len:=2)
        decide +kernel
      · apply includeSlice (i:=294) (len:=0)
        decide +kernel
      · apply includeSlice (i:=294) (len:=0)
        decide +kernel
      · apply includeSlice (i:=294) (len:=0)
        decide +kernel
      · apply includeSlice (i:=294) (len:=0)
        decide +kernel
      · apply includeSlice (i:=294) (len:=0)
        decide +kernel
    have cover_e14_0_0_0 : Included (missed 42 8 84 0 1) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0_0_0
      · exact cover_e14_0_0_0_1
      · exact cover_e14_0_0_0_2
      · apply includeSlice (i:=294) (len:=8)
        decide +kernel
      · apply includeSlice (i:=302) (len:=20)
        decide +kernel
      · apply includeSlice (i:=322) (len:=28)
        decide +kernel
      · apply includeSlice (i:=350) (len:=15)
        decide +kernel
      · apply includeSlice (i:=365) (len:=2)
        decide +kernel
    have cover_e14_0_0_1_0_0 : Included (missed 42 6 72 35184372088832 4097) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 9 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=367) (len:=27)
        decide +kernel
      · apply includeSlice (i:=394) (len:=16)
        decide +kernel
      · apply includeSlice (i:=410) (len:=0)
        decide +kernel
      · apply includeSlice (i:=410) (len:=0)
        decide +kernel
      · apply includeSlice (i:=410) (len:=0)
        decide +kernel
      · apply includeSlice (i:=410) (len:=0)
        decide +kernel
      · apply includeSlice (i:=410) (len:=3)
        decide +kernel
      · apply includeSlice (i:=413) (len:=1)
        decide +kernel
      · apply includeSlice (i:=414) (len:=1)
        decide +kernel
    have cover_e14_0_0_1_0 : Included (missed 42 7 72 35184372088832 4097) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0_1_0_0
      · apply includeSlice (i:=415) (len:=2)
        decide +kernel
      · apply includeSlice (i:=417) (len:=2)
        decide +kernel
      · apply includeSlice (i:=419) (len:=0)
        decide +kernel
      · apply includeSlice (i:=419) (len:=0)
        decide +kernel
      · apply includeSlice (i:=419) (len:=0)
        decide +kernel
      · apply includeSlice (i:=419) (len:=0)
        decide +kernel
      · apply includeSlice (i:=419) (len:=0)
        decide +kernel
    have cover_e14_0_0_1 : Included (missed 42 8 72 35184372088832 4097) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 7 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0_1_0
      · apply includeSlice (i:=419) (len:=17)
        decide +kernel
      · apply includeSlice (i:=436) (len:=2)
        decide +kernel
      · apply includeSlice (i:=438) (len:=3)
        decide +kernel
      · apply includeSlice (i:=441) (len:=8)
        decide +kernel
      · apply includeSlice (i:=449) (len:=7)
        decide +kernel
      · apply includeSlice (i:=456) (len:=2)
        decide +kernel
    have cover_e14_0_0_2 : Included (missed 42 8 60 70368744177664 16781313) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=458) (len:=38)
        decide +kernel
      · apply includeSlice (i:=496) (len:=12)
        decide +kernel
      · apply includeSlice (i:=508) (len:=0)
        decide +kernel
      · apply includeSlice (i:=508) (len:=2)
        decide +kernel
      · apply includeSlice (i:=510) (len:=4)
        decide +kernel
      · apply includeSlice (i:=514) (len:=1)
        decide +kernel
    have cover_e14_0_0 : Included (missed 42 9 84 0 1) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0_0
      · exact cover_e14_0_0_1
      · exact cover_e14_0_0_2
      · apply includeSlice (i:=515) (len:=49)
        decide +kernel
      · apply includeSlice (i:=564) (len:=48)
        decide +kernel
      · apply includeSlice (i:=612) (len:=29)
        decide +kernel
      · apply includeSlice (i:=641) (len:=5)
        decide +kernel
      · apply includeSlice (i:=646) (len:=1)
        decide +kernel
    have cover_e14_0_1_0_0_0 : Included (missed 42 6 71 1125899906842624 8193) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=647) (len:=26)
        decide +kernel
      · apply includeSlice (i:=673) (len:=3)
        decide +kernel
      · apply includeSlice (i:=676) (len:=0)
        decide +kernel
      · apply includeSlice (i:=676) (len:=0)
        decide +kernel
      · apply includeSlice (i:=676) (len:=1)
        decide +kernel
      · apply includeSlice (i:=677) (len:=4)
        decide +kernel
      · apply includeSlice (i:=681) (len:=5)
        decide +kernel
      · apply includeSlice (i:=686) (len:=3)
        decide +kernel
    have cover_e14_0_1_0_0 : Included (missed 42 7 71 1125899906842624 8193) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_1_0_0_0
      · apply includeSlice (i:=689) (len:=9)
        decide +kernel
      · apply includeSlice (i:=698) (len:=4)
        decide +kernel
      · apply includeSlice (i:=702) (len:=6)
        decide +kernel
      · apply includeSlice (i:=708) (len:=8)
        decide +kernel
      · apply includeSlice (i:=716) (len:=10)
        decide +kernel
      · apply includeSlice (i:=726) (len:=5)
        decide +kernel
      · apply includeSlice (i:=731) (len:=0)
        decide +kernel
    have cover_e14_0_1_0 : Included (missed 42 8 71 1125899906842624 8193) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 7 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_1_0_0
      · apply includeSlice (i:=731) (len:=24)
        decide +kernel
      · apply includeSlice (i:=755) (len:=3)
        decide +kernel
      · apply includeSlice (i:=758) (len:=2)
        decide +kernel
      · apply includeSlice (i:=760) (len:=5)
        decide +kernel
      · apply includeSlice (i:=765) (len:=9)
        decide +kernel
      · apply includeSlice (i:=774) (len:=1)
        decide +kernel
    have cover_e14_0_1_1 : Included (missed 42 8 59 1161084278931456 33566721) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=775) (len:=20)
        decide +kernel
      · apply includeSlice (i:=795) (len:=7)
        decide +kernel
      · apply includeSlice (i:=802) (len:=0)
        decide +kernel
      · apply includeSlice (i:=802) (len:=0)
        decide +kernel
      · apply includeSlice (i:=802) (len:=2)
        decide +kernel
      · apply includeSlice (i:=804) (len:=1)
        decide +kernel
    have cover_e14_0_1 : Included (missed 42 9 71 1125899906842624 8193) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_1_0
      · exact cover_e14_0_1_1
      · apply includeSlice (i:=805) (len:=20)
        decide +kernel
      · apply includeSlice (i:=825) (len:=17)
        decide +kernel
      · apply includeSlice (i:=842) (len:=13)
        decide +kernel
      · apply includeSlice (i:=855) (len:=4)
        decide +kernel
    have cover_e14_0_2_0 : Included (missed 42 8 58 2251799813685248 67117057) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=859) (len:=31)
        decide +kernel
      · apply includeSlice (i:=890) (len:=4)
        decide +kernel
      · apply includeSlice (i:=894) (len:=0)
        decide +kernel
      · apply includeSlice (i:=894) (len:=0)
        decide +kernel
      · apply includeSlice (i:=894) (len:=4)
        decide +kernel
      · apply includeSlice (i:=898) (len:=1)
        decide +kernel
    have cover_e14_0_2 : Included (missed 42 9 58 2251799813685248 67117057) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_2_0
      · apply includeSlice (i:=899) (len:=7)
        decide +kernel
      · apply includeSlice (i:=906) (len:=4)
        decide +kernel
      · apply includeSlice (i:=910) (len:=4)
        decide +kernel
      · apply includeSlice (i:=914) (len:=2)
        decide +kernel
    have cover_e14_0 : Included (missed 42 10 84 0 1) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 7 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0_0
      · exact cover_e14_0_1
      · exact cover_e14_0_2
      · apply includeSlice (i:=916) (len:=60)
        decide +kernel
      · apply includeSlice (i:=976) (len:=49)
        decide +kernel
      · apply includeSlice (i:=1025) (len:=14)
        decide +kernel
      · apply includeSlice (i:=1039) (len:=1)
        decide +kernel
    have cover_e14_1_0_0_0_0 : Included (missed 42 6 70 36028797018963968 16385) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=1040) (len:=7)
        decide +kernel
      · apply includeSlice (i:=1047) (len:=4)
        decide +kernel
      · apply includeSlice (i:=1051) (len:=0)
        decide +kernel
      · apply includeSlice (i:=1051) (len:=0)
        decide +kernel
      · apply includeSlice (i:=1051) (len:=0)
        decide +kernel
      · apply includeSlice (i:=1051) (len:=4)
        decide +kernel
      · apply includeSlice (i:=1055) (len:=6)
        decide +kernel
      · apply includeSlice (i:=1061) (len:=2)
        decide +kernel
    have cover_e14_1_0_0_0 : Included (missed 42 7 70 36028797018963968 16385) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 8 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_1_0_0_0_0
      · apply includeSlice (i:=1063) (len:=3)
        decide +kernel
      · apply includeSlice (i:=1066) (len:=3)
        decide +kernel
      · apply includeSlice (i:=1069) (len:=3)
        decide +kernel
      · apply includeSlice (i:=1072) (len:=6)
        decide +kernel
      · apply includeSlice (i:=1078) (len:=8)
        decide +kernel
      · apply includeSlice (i:=1086) (len:=4)
        decide +kernel
      · apply includeSlice (i:=1090) (len:=1)
        decide +kernel
    have cover_e14_1_0_0 : Included (missed 42 8 70 36028797018963968 16385) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 7 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_1_0_0_0
      · apply includeSlice (i:=1091) (len:=20)
        decide +kernel
      · apply includeSlice (i:=1111) (len:=5)
        decide +kernel
      · apply includeSlice (i:=1116) (len:=6)
        decide +kernel
      · apply includeSlice (i:=1122) (len:=12)
        decide +kernel
      · apply includeSlice (i:=1134) (len:=7)
        decide +kernel
      · apply includeSlice (i:=1141) (len:=1)
        decide +kernel
    have cover_e14_1_0 : Included (missed 42 9 70 36028797018963968 16385) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_1_0_0
      · apply includeSlice (i:=1142) (len:=9)
        decide +kernel
      · apply includeSlice (i:=1151) (len:=4)
        decide +kernel
      · apply includeSlice (i:=1155) (len:=11)
        decide +kernel
      · apply includeSlice (i:=1166) (len:=9)
        decide +kernel
      · apply includeSlice (i:=1175) (len:=3)
        decide +kernel
    have cover_e14_1_1_0 : Included (missed 42 8 57 37154696925806592 134242305) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=1178) (len:=20)
        decide +kernel
      · apply includeSlice (i:=1198) (len:=4)
        decide +kernel
      · apply includeSlice (i:=1202) (len:=1)
        decide +kernel
      · apply includeSlice (i:=1203) (len:=2)
        decide +kernel
      · apply includeSlice (i:=1205) (len:=3)
        decide +kernel
      · apply includeSlice (i:=1208) (len:=0)
        decide +kernel
    have cover_e14_1_1 : Included (missed 42 9 57 37154696925806592 134242305) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_1_1_0
      · apply includeSlice (i:=1208) (len:=3)
        decide +kernel
      · apply includeSlice (i:=1211) (len:=2)
        decide +kernel
      · apply includeSlice (i:=1213) (len:=2)
        decide +kernel
      · apply includeSlice (i:=1215) (len:=1)
        decide +kernel
    have cover_e14_1 : Included (missed 42 10 70 36028797018963968 16385) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_1_0
      · exact cover_e14_1_1
      · apply includeSlice (i:=1216) (len:=28)
        decide +kernel
      · apply includeSlice (i:=1244) (len:=25)
        decide +kernel
      · apply includeSlice (i:=1269) (len:=13)
        decide +kernel
      · apply includeSlice (i:=1282) (len:=1)
        decide +kernel
    have cover_e14_2_0_0 : Included (missed 42 8 56 72057594037927936 268451841) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 6 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl
      · apply includeSlice (i:=1283) (len:=19)
        decide +kernel
      · apply includeSlice (i:=1302) (len:=10)
        decide +kernel
      · apply includeSlice (i:=1312) (len:=3)
        decide +kernel
      · apply includeSlice (i:=1315) (len:=5)
        decide +kernel
      · apply includeSlice (i:=1320) (len:=3)
        decide +kernel
      · apply includeSlice (i:=1323) (len:=0)
        decide +kernel
    have cover_e14_2_0 : Included (missed 42 9 56 72057594037927936 268451841) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_2_0_0
      · apply includeSlice (i:=1323) (len:=7)
        decide +kernel
      · apply includeSlice (i:=1330) (len:=6)
        decide +kernel
      · apply includeSlice (i:=1336) (len:=8)
        decide +kernel
      · apply includeSlice (i:=1344) (len:=2)
        decide +kernel
    have cover_e14_2 : Included (missed 42 10 56 72057594037927936 268451841) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 5 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_2_0
      · apply includeSlice (i:=1346) (len:=24)
        decide +kernel
      · apply includeSlice (i:=1370) (len:=18)
        decide +kernel
      · apply includeSlice (i:=1388) (len:=10)
        decide +kernel
      · apply includeSlice (i:=1398) (len:=1)
        decide +kernel
    have cover_e14 : Included (missed 42 11 84 0 1) (keys e14) := by
      apply missed_succ
      intro c hc
      have hb : c < 7 := hc
      have opts : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
      rcases opts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover_e14_0
      · exact cover_e14_1
      · exact cover_e14_2
      · apply includeSlice (i:=1399) (len:=0)
        decide +kernel
      · apply includeSlice (i:=1399) (len:=0)
        decide +kernel
      · apply includeSlice (i:=1399) (len:=0)
        decide +kernel
      · apply includeSlice (i:=1399) (len:=0)
        decide +kernel
    exact fun _ hx => cover_of_included (n:=14) (h:=42) (by decide) cover_a14 cover_a14 cover_e14 hx

end AlspachSmall.Coverage

namespace AlspachSmall.Packed
open Packed

theorem s6Good : AllTested 6 (by decide) (Bitmap.full 6) 12 s6 := Coverage.verifyTables.s6Good

theorem s6Keys : s6.map sizes = partitions 6 3 12 := Coverage.verifyTables.s6Keys

theorem s8Good : AllTested 8 (by decide) (Bitmap.full 8) 24 s8 := Coverage.verifyTables.s8Good

theorem s8Keys : s8.map sizes = partitions 8 3 24 := Coverage.verifyTables.s8Keys

theorem s10Good : AllTested 10 (by decide) (Bitmap.full 10) 40 s10 := Coverage.verifyTables.s10Good

theorem s10Keys : s10.map sizes = partitions 10 3 40 := Coverage.verifyTables.s10Keys

theorem a12Good : AllTested 12 (by decide) a12Mask 30 a12 := Coverage.verifyTables.a12Good

theorem b12Good : AllTested 12 (by decide) b12Mask 30 b12 := Coverage.verifyTables.b12Good

theorem e12Good : AllTested 12 (by decide) e12Mask 60 e12 := Coverage.verifyTables.e12Good

theorem a14Good : AllTested 14 (by decide) a14Mask 42 a14 := Coverage.verifyTables.a14Good

theorem e14Good : AllTested 14 (by decide) e14Mask 84 e14 := Coverage.verifyTables.e14Good

end AlspachSmall.Packed

namespace AlspachSmall.Coverage
open Packed

theorem cover12 : ∀ xs ∈ partitions 12 3 60,
    Covered (keys a12) (keys b12) (keys e12) (Keys.lengthKey xs) := Coverage.verifyTables.cover12

theorem symmetricCover14 : ∀ xs ∈ partitions 14 3 84,
    Covered (keys a14) (keys a14) (keys e14) (Keys.lengthKey xs) := Coverage.verifyTables.symmetricCover14

end AlspachSmall.Coverage

namespace AlspachSmall.Bitmap
open SimpleGraph AlspachConjecture Packed
open scoped Classical

theorem canonical_packed {n total : Nat} {hn : 0 < n} {ws : List Nat}
    (valid : AllTested n hn (full n) total ws)
    (allParts : ws.map sizes = partitions n 3 total)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ n) (hs : m.sum = total) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m := by
  let xs := m.sort (· ≤ ·)
  have eqm : (xs : Multiset Nat) = m := Multiset.sort_eq ..
  have sum : xs.sum = total := by
    convert hs using 1
    exact congrArg Multiset.sum eqm
  have bounds (k : Nat) (hk : k ∈ xs) : 3 ≤ k ∧ k ≤ n := hm k (by simpa [xs] using hk)
  have mem := (mem_partitions_iff (by decide : 0 < 3)).2 ⟨Multiset.pairwise_sort ..,bounds,sum⟩
  rw [← allParts, List.mem_map] at mem
  obtain ⟨w, hw, heq⟩ := mem
  obtain ⟨C, cover, lengthsEq⟩ := from_row (hn := hn) (sizes := sizes w) (paths := paths w) (valid w hw).1
  exact ⟨C, cover, lengthsEq.trans ((congrArg (fun l : List Nat => (l : Multiset Nat)) heq).trans eqm)⟩


end AlspachSmall.Bitmap

namespace AlspachSmall.Bitmap
open SimpleGraph AlspachConjecture Packed
open scoped Classical

theorem compact_through_ten (n : Nat) (hn : Even n) (positive : 0 < n) (small : n ≤ 10)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ n) (hs : m.sum = n.choose 2 - n / 2) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m := by
  obtain ⟨k,hk⟩ := hn
  have hcase : n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl
  · exact canonical_two m hm hs
  · exact canonical_four m hm hs
  · exact canonical_packed s6Good s6Keys m hm hs
  · exact canonical_packed s8Good s8Keys m hm hs
  · exact canonical_packed s10Good s10Keys m hm hs

end AlspachSmall.Bitmap

namespace AlspachSmall.Bitmap

open SimpleGraph AlspachConjecture
open scoped Classical

theorem canonical_through_fourteen_of_large
    (twelve : ∀ (m : Multiset Nat), (∀ k ∈ m, 3 ≤ k ∧ k ≤ 12) → m.sum = 60 →
      ∃ C : Multiset (Cycle (cocktail 12)), IsCycleDecomposition (cocktail 12) C ∧ lengths C = m)
    (fourteen : ∀ (m : Multiset Nat), (∀ k ∈ m, 3 ≤ k ∧ k ≤ 14) → m.sum = 84 →
      ∃ C : Multiset (Cycle (cocktail 14)), IsCycleDecomposition (cocktail 14) C ∧ lengths C = m)
    (n : Nat) (hn : Even n) (positive : 0 < n) (bound : n ≤ 14)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ n)
    (hs : m.sum = n.choose 2 - n / 2) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m := by
  obtain ⟨k,hk⟩ := hn
  have cases : n ≤ 10 ∨ n = 12 ∨ n = 14 := by omega
  rcases cases with base | rfl | rfl
  · exact compact_through_ten n ⟨k,hk⟩ positive base m hm hs
  · exact twelve m hm hs
  · exact fourteen m hm hs

end AlspachSmall.Bitmap
namespace AlspachSmall.Bitmap
open SimpleGraph AlspachConjecture Packed
open scoped Classical

theorem canonical_12_of_keys
    (cover : ∀ xs ∈ partitions 12 3 60, Keys.lengthKey xs ∈ keys e12 ∨
      ∃ u ∈ keys a12, ∃ v ∈ keys b12, u + v = Keys.lengthKey xs)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ 12) (hs : m.sum = 60) :
    ∃ C : Multiset (Cycle (cocktail 12)), IsCycleDecomposition (cocktail 12) C ∧ lengths C = m := by
  have eEq : e12Mask = full 12 := by decide +kernel
  exact from_partition_offers (n := 12) (hn := by decide) (a := a12Mask) (b := b12Mask)
    (half := 30) (by decide +kernel) (by decide +kernel) (by decide)
    a12Good (checkedOffers b12Good) (eEq ▸ e12Good) cover m hm hs

end AlspachSmall.Bitmap
namespace AlspachSmall.Bitmap
open SimpleGraph AlspachConjecture Packed
open scoped Classical

/-- Regions are carried along graph isomorphisms by mapping the cycle walks.
The transport of walk edges follows the approach of the parent reduction's
`iso_decomposition`. -/
theorem regionIso {n : Nat} {a b : Nat} (f : cocktail n ≃g cocktail n)
    (bits : ∀ x y : Fin n, a.testBit (key (x,y)) = b.testBit (key (f x,f y)))
    {m : Multiset Nat} (h : Region n a m) : Region n b m := by
  classical
  obtain ⟨cs, hlen, hcount⟩ := h
  let move (c : Cycle (cocktail n)) : Cycle (cocktail n) :=
    ⟨f c.base, c.walk.map f.toHom, c.isCycle.map f.injective⟩
  have mem (c : Cycle (cocktail n)) (x y : Fin n) :
      s(f x, f y) ∈ (move c).edges ↔ s(x,y) ∈ c.edges := by
    change s(f x, f y) ∈ (c.walk.map f.toHom).edges ↔ _
    rw [Walk.edges_map]
    change Sym2.map f s(x,y) ∈ List.map (Sym2.map f) c.edges ↔ s(x,y) ∈ c.edges
    exact List.mem_map_of_injective (Sym2.map.injective f.injective)
  refine ⟨cs.map move, ?_, ?_⟩
  · have len (c : Cycle (cocktail n)) : (move c).length = c.length := Walk.length_map _ _
    simpa [lengths, Multiset.map_map, Function.comp_def, len] using hlen
  · rintro ⟨x,y⟩
    obtain ⟨u,rfl⟩ := f.surjective x
    obtain ⟨v,rfl⟩ := f.surjective y
    rw [Multiset.filter_map, Multiset.card_map, ← bits]
    simpa [Function.comp_def, mem] using hcount (u,v)

def flip14Vertex (x : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (if x.val < 2 then x.val else x.val ^^^ 1)

private theorem flip14Inv : ∀ x, flip14Vertex (flip14Vertex x) = x := by decide +kernel

private theorem flip14Adj : ∀ x y : Fin 14,
    (flip14Vertex x).val / 2 ≠ (flip14Vertex y).val / 2 ↔ x.val / 2 ≠ y.val / 2 := by decide +kernel

def flip14Iso : cocktail 14 ≃g cocktail 14 where
  toFun := flip14Vertex
  invFun := flip14Vertex
  left_inv := flip14Inv
  right_inv := flip14Inv
  map_rel_iff' := flip14Adj _ _

private theorem flip14Bits : ∀ x y : Fin 14,
    a14Mask.testBit (key (x,y)) = b14Mask.testBit (key (flip14Vertex x, flip14Vertex y)) := by
  decide +kernel

theorem flip14Region {m : Multiset Nat} (h : Region 14 a14Mask m) : Region 14 b14Mask m :=
  regionIso flip14Iso flip14Bits h


end AlspachSmall.Bitmap
namespace AlspachSmall.Bitmap
open SimpleGraph AlspachConjecture Packed
open scoped Classical

theorem canonical_14_of_symmetric_keys
    (cover : ∀ xs ∈ partitions 14 3 84, Keys.lengthKey xs ∈ keys e14 ∨
      ∃ u ∈ keys a14, ∃ v ∈ keys a14, u + v = Keys.lengthKey xs)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ 14) (hs : m.sum = 84) :
    ∃ C : Multiset (Cycle (cocktail 14)), IsCycleDecomposition (cocktail 14) C ∧ lengths C = m := by
  have eEq : e14Mask = full 14 := by decide +kernel
  exact from_partition_offers (n := 14) (hn := by decide) (a := a14Mask) (b := b14Mask)
    (half := 42) (by decide +kernel) (by decide +kernel) (by decide)
    a14Good (relabeledOffers (right := a14) (checkedOffers a14Good) rfl (fun _ h => flip14Region h)) (eEq ▸ e14Good) cover m hm hs

end AlspachSmall.Bitmap

namespace AlspachSmall.Bitmap
open SimpleGraph AlspachConjecture
open scoped Classical

theorem canonical_through_fourteen (n : Nat) (hn : Even n) (positive : 0 < n) (bound : n ≤ 14)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ n)
    (hs : m.sum = n.choose 2 - n / 2) :
    ∃ C : Multiset (Cycle (cocktail n)), IsCycleDecomposition (cocktail n) C ∧ lengths C = m :=
  canonical_through_fourteen_of_large (canonical_12_of_keys Coverage.cover12)
    (canonical_14_of_symmetric_keys Coverage.symmetricCover14) n hn positive bound m hm hs

theorem choice_through_fourteen (n : Nat) (hn : Even n) (positive : 0 < n) (bound : n ≤ 14)
    (m : Multiset Nat) (hm : ∀ k ∈ m, 3 ≤ k ∧ k ≤ n)
    (hs : m.sum = n.choose 2 - n / 2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m :=
  choose_consecutive_matching hn m (canonical_through_fourteen n hn positive bound m hm hs)

end AlspachSmall.Bitmap

theorem OMA.solution : OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.H1 :=
  AlspachSmall.Bitmap.choice_through_fourteen
