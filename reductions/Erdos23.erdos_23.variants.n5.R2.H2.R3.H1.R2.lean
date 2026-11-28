import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H2_R3
import Mathlib
/-! Erdős 23, order-22 maximal extremizers with ten open-neighborhood classes.
The finite classification grows spanning subgraphs from order one through ten.
Each extension includes a kernel-checked relabeling. Only two order-ten
representatives have distinct neighborhoods. Both have weighted cuts of cost
at most sixteen at total mass 22. The graph6 witness at cost seventeen and
the fiber-counting argument are adapted from PRs #32841 and #36975. -/
namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3_H1_R2
open Finset SimpleGraph
open scoped Classical

/-- The order-22 upper bound for maximal extremizers with at most nine classes. -/
def H1 : Prop := ∀ G : SimpleGraph (Fin 22), Maximal (fun K : SimpleGraph (Fin 22) => K.CliqueFree 3) G →
  let loss (K : SimpleGraph (Fin 22)) (c : Fin 22 → Bool) :=
    ∑ i,∑ j,if K.Adj i j ∧ c i=c j then (1:ℕ) else 0
  let best (K : SimpleGraph (Fin 22)) := (univ.image (loss K)).min' (univ_nonempty.image _)
  (∀ K : SimpleGraph (Fin 22), K.CliqueFree 3 → best K ≤ best G) →
  (univ.image (fun i => G.neighborFinset i)).card ≤ 9 →
  ∃ c : Fin 22 → Bool, (∑ i,∑ j,if G.Adj i j ∧ c i=c j then (1:ℕ) else 0) ≤ 34

/-- The order-22 upper bound for maximal extremizers with at least eleven classes. -/
def H2 : Prop := ∀ G : SimpleGraph (Fin 22), Maximal (fun K : SimpleGraph (Fin 22) => K.CliqueFree 3) G →
  let loss (K : SimpleGraph (Fin 22)) (c : Fin 22 → Bool) :=
    ∑ i,∑ j,if K.Adj i j ∧ c i=c j then (1:ℕ) else 0
  let best (K : SimpleGraph (Fin 22)) := (univ.image (loss K)).min' (univ_nonempty.image _)
  (∀ K : SimpleGraph (Fin 22), K.CliqueFree 3 → best K ≤ best G) →
  11 ≤ (univ.image (fun i => G.neighborFinset i)).card →
  ∃ c : Fin 22 → Bool, (∑ i,∑ j,if G.Adj i j ∧ c i=c j then (1:ℕ) else 0) ≤ 34

section TenClasses

private lemma pack_bits {n : ℕ} (f : Fin n → Bool) :
    ∃ k : Fin (2^n),∀ i,k.val.testBit i.val=f i := by
  induction n with
  | zero => exact ⟨0,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨k,hk⟩ := ih (fun i => f i.succ)
    have bound : Nat.bit (f 0) k.val < 2^(n+1) := by
      have h := k.isLt
      cases val : f 0 <;> simp [Nat.bit,pow_succ] <;> omega
    refine ⟨⟨_,bound⟩,Fin.cases ?_ (fun i => ?_)⟩
    · exact Nat.testBit_bit_zero _ _
    · exact (Nat.testBit_bit_succ _ _ _).trans (hk i)

/-- Insert a new vertex after embedding the first n vertices in a representative.
Delete all old edges inside the new neighborhood, then use the certified
embedding of this extension. Triangle-freeness protects every original edge. -/
lemma grow_catalog {n a b : ℕ} (base : Fin a → ℕ → ℕ → Bool) (next : Fin b → ℕ → ℕ → Bool)
    (old : ∀ G : SimpleGraph (Fin n),G.CliqueFree 3 →
    ∃ k : Fin a,∃ f : Equiv.Perm (Fin n),∀ i j,G.Adj i j → base k (f i).val (f j).val=true) :
  let ext (k) (m : Fin (2^n)) (i j : ℕ) :=
    if i=n then decide (j<n) && m.val.testBit j else if j=n then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  (∀ k m,∃ t : Fin b,∃ h : Equiv.Perm (Fin (n+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true) →
  ∀ G : SimpleGraph (Fin (n+1)),G.CliqueFree 3 →
    ∃ k : Fin b,∃ f : Equiv.Perm (Fin (n+1)),∀ i j,G.Adj i j → next k (f i).val (f j).val=true := by
  intro ext certified G tri
  let R := G.comap (Fin.castSucc : Fin n → Fin (n+1))
  have clean : R.CliqueFree 3 := by
    intro s h
    obtain ⟨i,j,k,ij,ik,jk,_⟩ := is3Clique_iff.mp h
    exact tri _ (is3Clique_triple_iff.mpr
      ⟨show G.Adj i.castSucc j.castSucc from ij,show G.Adj i.castSucc k.castSucc from ik,
       show G.Adj j.castSucc k.castSucc from jk⟩)
  obtain ⟨k,f,hf⟩ := old R clean
  let last := Fin.last n
  obtain ⟨m,hm⟩ := pack_bits (fun i : Fin n => decide (G.Adj (f.symm i).castSucc last))
  have bit (i : Fin n) : m.val.testBit (f i).val = decide (G.Adj i.castSucc last) := by
    simpa only [Equiv.symm_apply_apply] using hm (f i)
  obtain ⟨t,h,map⟩ := certified k m
  let up (e : Equiv.Perm (Fin n)) : Fin (n+1) → Fin (n+1) :=
    Fin.lastCases last (fun i => (e i).castSucc)
  have cancel (e : Equiv.Perm (Fin n)) (i : Fin (n+1)) : up e.symm (up e i)=i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [up,last]
  let e : Equiv.Perm (Fin (n+1)) := ⟨up f,up f.symm,cancel f,fun i => by simpa only [Equiv.symm_symm] using cancel f.symm i⟩
  refine ⟨t,e.trans h,?_⟩
  intro i j edge
  apply map
  change ext k m (up f i).val (up f j).val=true
  revert edge
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j =>
      intro adj
      simpa [up,last,ext,bit,(f j).isLt] using (show G.Adj j.castSucc (Fin.last n) from adj.symm)
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      intro adj
      simpa [up,last,ext,bit,ne_of_lt (f i).isLt] using adj
    | cast j =>
      intro adj
      have sep : ¬ (G.Adj i.castSucc last ∧ G.Adj j.castSucc last) :=
        fun h => tri _ (is3Clique_triple_iff.mpr ⟨adj,h.1,h.2⟩)
      have elem := hf i j (show R.Adj i j from adj)
      by_cases hi : G.Adj i.castSucc last
      · have hj : ¬G.Adj j.castSucc last := fun h => sep ⟨hi,h⟩
        simp [up,ext,ne_of_lt (f i).isLt,ne_of_lt (f j).isLt,bit,elem,hj]
      · simp [up,ext,ne_of_lt (f i).isLt,ne_of_lt (f j).isLt,bit,elem,hi]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_1 :
  let base (k : Fin 1) (i j : ℕ) := (0x0 : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 1) (i j : ℕ) := (0x402 : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^1)) (i j : ℕ) :=
    if i=1 then decide (j<1) && m.val.testBit j else if j=1 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 1,∃ h : Equiv.Perm (Fin (1+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 1 → Fin 1 → ℕ := ![
    ![
      0x400200]]
  let code (k : Fin 1) (m : Fin (2^1)) :=
    (blocks k (Fin.ofNat 1 (m.val/2))) >>> (13*(m.val%2))
  let choice (k m) := Fin.ofNat 1 ((code k m)%32)
  let lab (k m) (i : Fin 2) := Fin.ofNat 2 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 2,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 2) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_2 :
  let base (k : Fin 1) (i j : ℕ) := (0x402 : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 1) (i j : ℕ) := (0x100406 : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^2)) (i j : ℕ) :=
    if i=2 then decide (j<2) && m.val.testBit j else if j=2 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 1,∃ h : Equiv.Perm (Fin (2+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 1 → Fin 1 → ℕ := ![
    ![
      0x2101008084004200]]
  let code (k : Fin 1) (m : Fin (2^2)) :=
    (blocks k (Fin.ofNat 1 (m.val/4))) >>> (17*(m.val%4))
  let choice (k m) := Fin.ofNat 1 ((code k m)%32)
  let lab (k m) (i : Fin 3) := Fin.ofNat 3 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 3,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 3) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_3 :
  let base (k : Fin 1) (i j : ℕ) := (0x100406 : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 2) (i j : ℕ) := (0x180902406000000000000000004010040e : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^3)) (i j : ℕ) :=
    if i=3 then decide (j<3) && m.val.testBit j else if j=3 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 2,∃ h : Equiv.Perm (Fin (3+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 1 → Fin 1 → ℕ := ![
    ![
      0x32101908048c4026420121300990804c840064200]]
  let code (k : Fin 1) (m : Fin (2^3)) :=
    (blocks k (Fin.ofNat 1 (m.val/8))) >>> (21*(m.val%8))
  let choice (k m) := Fin.ofNat 2 ((code k m)%32)
  let lab (k m) (i : Fin 4) := Fin.ofNat 4 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 4,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 4) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_4 :
  let base (k : Fin 2) (i j : ℕ) := (0x180902406000000000000000004010040e : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 3) (i j : ℕ) := (0x3018090601400000000000000e044110440e000000000000001004010041e : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^4)) (i j : ℕ) :=
    if i=4 then decide (j<4) && m.val.testBit j else if j=4 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 3,∃ h : Equiv.Perm (Fin (4+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 2 → Fin 1 → ℕ := ![
    ![
      0x4321021908050c8042864201430210a190804d08402864201403210a190804c90402864201321400a1908050c8400864200],
    ![
      0x4321021908050c804226840243021098a1008d0840268420140321099200850c48046480214321011920084d08402684201]]
  let code (k : Fin 2) (m : Fin (2^4)) :=
    (blocks k (Fin.ofNat 1 (m.val/16))) >>> (25*(m.val%16))
  let choice (k m) := Fin.ofNat 3 ((code k m)%32)
  let lab (k m) (i : Fin 5) := Fin.ofNat 5 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 5,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 5) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_5 :
  let base (k : Fin 3) (i j : ℕ) := (0x3018090601400000000000000e044110440e000000000000001004010041e : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 4) (i j : ℕ) := (0xc0e044110c02c000000000001c0701c380e038000000000007821084210841e000000000000401004010043e : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^5)) (i j : ℕ) :=
    if i=5 then decide (j<5) && m.val.testBit j else if j=5 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 4,∃ h : Equiv.Perm (Fin (5+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 3 → Fin 2 → ℕ := ![
    ![
      0x5043210aa1908055084c04a86420154231012a1908050d48402a86420154321012a1908050c94402a8642014321500aa19080550c8400a864200,
      0x5432102a19080550c8042a8642015430210aa1908054850c04a8642015403210aa1908054904c04a86420152431012a19080514c8402a864201],
    ![
      0x504321090aa180900c944642a8602403521190aa1809504c80642a8602405321190aa180950c480642a8602543210190aa180914c84028a64201,
      0x5432102a19080550c80428264a035430210a09a900d4850c0428a64035403210a0a9900d4904c04286a40352431010a19280d14c84028a64201],
    ![
      0x5043210a299080d14c80464a8620254231012a118808d5084066a8420354321011a92008d50c84046a480233215401990aa00cc855006642a803,
      0x5432102a19080550c80424a862025430210a18a900d4850c04680a4235403210928a18090d4408668a02434350121928a18094850c0468a0243]]
  let code (k : Fin 3) (m : Fin (2^5)) :=
    (blocks k (Fin.ofNat 2 (m.val/16))) >>> (29*(m.val%16))
  let choice (k m) := Fin.ofNat 4 ((code k m)%32)
  let lab (k m) (i : Fin 6) := Fin.ofNat 6 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 6,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 6) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_6 :
  let base (k : Fin 4) (i j : ℕ) := (0xc0e044110c02c000000000001c0701c380e038000000000007821084210841e000000000000401004010043e : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 6) (i j : ℕ) := (0x901c07118380e0700000000007078210846018058000000000307821084211805c000000000701c0701c781e078000000003e10441104411043e000000000100401004010047e : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^6)) (i j : ℕ) :=
    if i=6 then decide (j<6) && m.val.testBit j else if j=6 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 6,∃ h : Equiv.Perm (Fin (6+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 4 → Fin 4 → ℕ := ![
    ![
      0x2106543132a19080595084c04ca8642016542310132a19080550d88402ca8642016543210132a19080550c98402ca86420154321600b2a190805950c8400ca864200,
      0x60543210b2a190804859500c4ca8642012165043132a19080594850c04ca8642012160543132a19080594904c04ca8642016524310132a190805518c8402ca864201,
      0x65043210b2a190804985500c4ca8642012615043132a19080589450c04ca8642012610543132a19080589504c04ca8642016254310132a190805590c8402ca864201,
      0x654321032a190805950c8042ca86420165430210b2a190804995040c4ca86420165403210b2a190804994500c4ca8642012651043132a19080588550c04ca864201],
    ![
      0x5064321190b2a180995084c0842ca86026542310210b2a18099504c80642ca86026543210210b2a1809950c480642ca86026543210190b2a1809590c8402ac864201,
      0x6054321090b2a1809410c984642ca86025043621190b2a180994850c0842ca86025046321190b2a180994904c0842ca86026524310210b2a18099450c80642ca8602,
      0x65043210a8b21900c985500c4c08426a426150431302118a9189450c042a8c640326105431302190a9189504c042a86c403625431010aa19300d590c8402ac864201,
      0x654321032a190805950c8042a2864c0365430210a8a1b100c995040c4c04286a465403210a8a31900c994500c4c04826a426510431301218a9188550c042ac86403],
    ![
      0x210654311aa310814d518804aca86042535460212b2a190095950c840ac420a8626543210132a190809950c8404ca8642026543210132a190809950c8404ca864202,
      0x60543210ab2190811590c80486042ca85564302121810ab214c085518ac420a862216054311ab210814d590804aca68042535640212b29a1009594d0840ac420a862,
      0x65043210aa3190811518c80486402ca85546302121900ab214c805518ac420a862261054311b2a10814d950804ac6a8042536540212b1aa100958d50840ac420a862,
      0x654321032a190805950c80424ca8620265430210932a09808995040c4c420a86265403210aa1b1081150d880486420ca855436021219082b214c841518ac420a862],
    ![
      0x21065431130aa1814841950c44c2a860554326102930aa181550c9840a4c2a860554362102930aa181550d8840a4c2a86054362105221b1082910d88414886c420a4,
      0x60543210ab219080d590c80464ca86202216504311a932081558850c0a4a68c205216054311a923081558904c0a4a6c820565243101329218809194c84068ca64203,
      0x65043210930aa1809518840c8460a8c2554620132130aa1808c819504a460a8c2554602132130aa1808c815904a460a8c2532054612930aa180988550c04460a8c25,
      0x654321032a190805950c80424ca8620265430210aa09b100c995040c44a68c20565403210aa0b1900c994500c44a6c820526510431310218a9188550c044ca86204]]
  let code (k : Fin 4) (m : Fin (2^6)) :=
    (blocks k (Fin.ofNat 4 (m.val/16))) >>> (33*(m.val%16))
  let choice (k m) := Fin.ofNat 6 ((code k m)%32)
  let lab (k m) (i : Fin 7) := Fin.ofNat 7 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 7,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by
    intro k
    fin_cases k <;> decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 7) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_7 :
  let base (k : Fin 6) (i j : ℕ) := (0x901c07118380e0700000000007078210846018058000000000307821084211805c000000000701c0701c781e078000000003e10441104411043e000000000100401004010047e : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 10) (i j : ℕ) := (0xa8072502321468340580000006c0701c8421078380e0000000640701c86218781e0e0000000240701c07218781e0f00000001c3e10441104c0300b80000000c3e1044110441300bc0000003c0f03c0f3c0f03c0f00000001c0701c0701cf83e0f8000001f88120481204812047e00000004010040100401004fe : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^7)) (i j : ℕ) :=
    if i=7 then decide (j<7) && m.val.testBit j else if j=7 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 10,∃ h : Equiv.Perm (Fin (7+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 6 → Fin 8 → ℕ := ![
    ![
      0x765432101bb2a190805d95084c04eca8642017654231013b2a190805950dc8402eca8642017654321013b2a190805950c9c402eca864201654321700bb2a190805d950c8400eca864200,
      0x2107654313b2a190805d94c85006eca864201765324101bb2a190805d94850c04eca864201765342101bb2a190805d94904c04eca8642017652431013b2a190805951cc8402eca864201,
      0x2170654313b2a190805d8d485006eca864201763524101bb2a190805d89450c04eca864201763542101bb2a190805d89504c04eca8642017625431013b2a19080595d0c8402eca864201,
      0x706543210bb2a19080485d9500c4eca8642012176504313b2a190805d8c855006eca8642012176054313b2a190805d8c945006eca864201763254101bb2a190805d88550c04eca864201,
      0x2710654313b2a190805cd9485006eca864201736524101bb2a190805c99450c04eca864201736542101bb2a190805c99504c04eca8642017265431013b2a1908059d50c8402eca864201,
      0x760543210bb2a1908049c59500c4eca8642012716504313b2a190805cd8855006eca8642012716054313b2a190805cd8945006eca864201736254101bb2a190805c98550c04eca864201,
      0x765043210bb2a1908049d85500c4eca8642012761504313b2a190805cc9855006eca8642012761054313b2a190805cc9945006eca864201732654101bb2a190805c85950c04eca864201,
      0x765432103b2a190805d950c8042eca864201765430210bb2a1908049d95040c4eca864201765403210bb2a1908049d94500c4eca8642012765104313b2a190805cc8595006eca864201],
    ![
      0x6215437290bb2a1809d95084c0a42eca860276542310290bb2a1809d9504c80842eca860276543210290bb2a1809d950c480842eca860276543210210bb2a18099d50c8402cea864201,
      0x60754321210bb2a180818950c5ca42eca860206254137290bb2a1809d94850c0a42eca860206251437290bb2a1809d94904c0a42eca860276524310290bb2a1809d9450c80842eca8602,
      0x60574321210bb2a180819490c5ca42eca860206524137290bb2a1809d89450c0a42eca860206521437290bb2a1809d89504c0a42eca860276254310290bb2a1809d8550c80842eca8602,
      0x70654321090bb2a18098150c9c4842eca860260543721210bb2a18081950c85ca42eca860260547321210bb2a180819508c5ca42eca860206542137290bb2a1809d88550c0a42eca8602,
      0x2710654310390aa1b15cd9485006e0a8426c5736524101b82a118b15c99450c042ca8e6404736542101b82a190b15c99504c042ca86e4047265431010b2a1938119d50c8402cea864201,
      0x760543210b0baa190109c59500c40e4a862c52716504310392a09b15cd8855006e0a4286c527160543103928a1b15cd8945006e0a4826c5736254101b829218b15c98550c042cae86404,
      0x765043210b0aba190109d85500c40ea4862c527615043103a9209b15cc9855006e04a286c527610543103a90a1b15cc9945006e04a826c5732654101b812a18b15c85950c042cea86404,
      0x765432103b2a190805d950c8042c2a864e04765430210b0aa1b90109d95040c40ea8642c5765403210b0aa3990109d94500c40ea8462c527651043103aa109b15cc8595006e042a86c5],
    ![
      0x7654321019b2a390818d951c804ceca8604263654702133b2a190099d950c840c6eca842037654321013b2a190809d950c8404eca8642027654321013b2a190809d950c8404eca864202,
      0x2107654313b2a188121d950c4810eca8604277654321043b2a19009dd950c840e6eca842037653421019b2ba10818d95d0804ceca6804263657402133b29a10099d94d0840c6eca84203,
      0x2170654313b22988121d914c4810ec8a604277645321043b2299009dd914c840e6eca842037635421019b3aa10818d9d50804cec6a804263675402133b1aa10099d8d50840c6eca84203,
      0x706543210b3aa1908159d50c804a06ca8e42667543021281b2a138980d95085cc6eca842032176054313b21a88121d90d44810ec86a04277643521043b21a9009dd90d4840e6eca84203,
      0x2710654313a32988121d194c4810e8ca604277465321043a3299009dd194c840e6eca842037365421019bb2a10818dd950804ce6ca8042637654021339b2a10099cd950840c6eca84203,
      0x760543210b2ba19081595d0c804a0c6a8e426657430212831aa1389818d5085cc6eca842032716054313a31a88121d18d44810e8c6a04277463521043a31a9009dd18d4840e6eca84203,
      0x765043210b2a3990815951cc804a0ca68e4266547302128329a13898194d085cc6eca842032761054313a1b288121d0d944810e86ca04277436521043a1b29009dd0d94840e6eca84203,
      0x765432103b2a190805d950c80424eca8620276543021093b2a098089d95040c46eca84203765403210b2a1b90815950dc804a0ca86e426654370212832a1938981950c85cc6eca84203],
    ![
      0x210765433138b2a1818841d950cc4e2ca8606657413024138b2a181995d04c0904e2ca8606657431024138b2a181995d0c40904e2ca86062105437629082a1bb1484150dd8a420a86ec5,
      0x210765431138b2a1818841d950c44e2ca8606210657433138b2a181884195d0cc4e2ca8606210675433138b2a18188419d50cc4e2ca8606657143024138b2a181995c50c0904e2ca8606,
      0x2170654313b0aa181209d85500cc4c6ea82067635241019b12ba08199c9450c0c2ce8a60487635421019b12a388199c9504c0c2ce86a0487625431013b12a188095d90c8408aec864204,
      0x706543210b3aa1908119d50c80484eca862022176504313b0a1a81209d95040cc4c6a8e2062176054313b0a2981209d94500cc4c6ae82067632541019b13aa08199c8550c0c2cea86048,
      0x620754312938b2a1809c4990d410460ca8e26712645304138b2a1808c819d504c460ca8e26712654304138b2a1808c8195d04c460ca8e26320654713138b2a1809c85950c04460ca8e26,
      0x760543210938b2a180988150dc4a460ca8e26620547312938b2a1809c490d9410460ca8e26620574312938b2a1809c4918d410460ca8e26712465304138b2a1808c81d9504c460ca8e26,
      0x765043210b28ba190109d85500c44c6ea820627615043102b9209b15cc98550062ce8a604827610543102b90a1b15cc99450062ce86a048732654101b902a18b15c85950c044eca86205,
      0x765432103b2a190805d950c80424eca86202765430210b28a1b90109d95040c44c6a8e206765403210b28a3990109d94500c44c6ae820627651043102ba109b15cc85950062cea86048],
    ![
      0x210765433138b2a181c841d950cc4e2ca8607210765433138b2a181c841d950cc4e2ca860765743102432ba18812195d0c4090cae86204865743102432ba18812195d0c4090cae862048,
      0x210765431138b2a181c841d950c44e2ca8607210765431138b2a181c841d950c44e2ca8607210675433138b2a181c8419d50cc4e2ca8607210675433138b2a181c8419d50cc4e2ca8607,
      0x2170654310130baa1989d85500ceeca862409276150433bb2a1908259c9450c0ec40e2a866763542101bb1aa1080d8c1509c4cc60a84e266305472133182a390995d90c840aaec864205,
      0x706543210b3aa1908159d50c804a06ca8e42667543021281b2a138980d95085cc6eca8420321760543101338aa1989d94500ceace864209276510433ab3a1890259c8550c0ec402ea866,
      0x620754312938b2a1809c4990d410460ca8e2671264530411832ba098c819d504c2e4ca8608712654304138b2a1808c8195d04c460ca8e2632065471311832ba099c85950c042e4ca8608,
      0x760543210938b2a180988150dc4a460ca8e2662054731291832ba099c490d94102e4ca8608620574312938b2a1809c4918d410460ca8e2671246530411832ba098c81d9504c2e4ca8608,
      0x765043210b28ba190109d85500c44c6ea8206276150431131ba8a019cc9855006c40e2a86627610543102b90a1b15cc99450062ce86a0487326541018b3a182921c85950c04a0c4286e5,
      0x765432103b2a190805d950c80424eca8620276543021093b2a098089d95040c46eca84203765403210b28a3990109d94500c44c6ae8206276510431131ab8a019cc8595006c402ea866],
    ![
      0x765432101bb2a19080d0d95c804e86cae4027436570213a1b2b8109d0d95c409086cae204867543210333aa1908199d50c840ccea86420667543210333aa1908199d50c840ccea864206,
      0x210765431010bb2a19885d9500cee8c6a2409217650433ba31a9082595c850c0ece420a866271605433133a8a181d90c549c12468cea20964315720491a338a82595c850c0ece420a866,
      0x2170654310138b2a198859d500cea68ce4209216750433ba1b290825949c50c0ece420a866276105433132b8a181d904d49c1228c6ae4096413572048a31a93825949c50c0ece420a866,
      0x706543210b3aa09901085d9500c44eca6820621765043113b298a019d8c855006ce420a86667540321213b28a18080994dc50c48cae60270265317431232b8189dd8c855006ce420a866,
      0x2710654313a32988121d194c4810e8ca604277465321043a3299009dd194c840e6eca84203736542101a3b299081dcd95084068eca64207736542101a3b299081dcd95084068eca64207,
      0x760543210b2ba19081595d0c804a0c6a8e426657430212831aa1389818d5085cc6eca84203271605431133a8a181c189c54d0c468cea20906271354311a338a825d080594ce8e420ca67,
      0x765043210b2a3990815951cc804a0ca68e4266547302128329a13898194d085cc6eca84203276105431132b8a181c19c854d0c28c6ae4090672135430a31a93825d008594ce8e420ca67,
      0x765432103b2a190805d950c80424eca8620276543021093b2a098089d95040c46eca8420376540321093b28a18098951c40ca48cae60276254701329232b8189c1d94c850c8e420ca67]]
  let code (k : Fin 6) (m : Fin (2^7)) :=
    (blocks k (Fin.ofNat 8 (m.val/16))) >>> (37*(m.val%16))
  let choice (k m) := Fin.ofNat 10 ((code k m)%32)
  let lab (k m) (i : Fin 8) := Fin.ofNat 8 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 8,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by
    intro k
    fin_cases k <;> decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 8) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_8 :
  let base (k : Fin 10) (i j : ℕ) := (0xa8072502321468340580000006c0701c8421078380e0000000640701c86218781e0e0000000240701c07218781e0f00000001c3e10441104c0300b80000000c3e1044110441300bc0000003c0f03c0f3c0f03c0f00000001c0701c0701cf83e0f8000001f88120481204812047e00000004010040100401004fe : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 16) (i j : ℕ) := (0x2a064074148661078540e00004a01d3410c43414c86c0b80003303c0f4310c3c0f0701c00001303c0f03d0c3c0f0781e00001103c0f03d0e3c0f03c1e00003b01c0741104410f8701c00001b01c0701d04410f8781e00001901c0701d06418f83e1e00000901c0701c07418f83e1f00000f1f881204816018060170000071f881204812058060178000031f88120481204816017c0000f03c0f03c0f7c1f07c1f00000701c0701c0701df87e1f8000fe405014050140501404fe00001004010040100401005fe : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^8)) (i j : ℕ) :=
    if i=8 then decide (j<8) && m.val.testBit j else if j=8 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 16,∃ h : Equiv.Perm (Fin (8+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 10 → Fin 16 → ℕ := ![
    ![
      0x8765432101c3b2a1908061d95084c050eca864201876542310143b2a190805d950e084030eca864201876543210143b2a190805d950ca04030eca8642017654321800c3b2a1908061d950c84010eca864200,
      0x3210876541c3b2a1908061d94c850070eca8642018765324101c3b2a1908061d94850c050eca8642018765342101c3b2a1908061d94904c050eca864201876524310143b2a190805d9520c84030eca864201,
      0x3218076541c3b2a1908061d8d4850070eca8642018763524101c3b2a1908061d89450c050eca8642018763542101c3b2a1908061d89504c050eca864201876254310143b2a190805d9610c84030eca864201,
      0x210876543143b2a190804c861d941070eca8642013218760541c3b2a1908061d8c8550070eca8642013218706541c3b2a1908061d8c9450070eca8642018763254101c3b2a1908061d88550c050eca864201,
      0x3281076541c3b2a1908061cd94850070eca8642018736524101c3b2a1908061c99450c050eca8642018736542101c3b2a1908061c99504c050eca864201872654310143b2a190805da150c84030eca864201,
      0x218076543143b2a190804ca05d941070eca8642013281760541c3b2a1908061cd88550070eca8642013281706541c3b2a1908061cd89450070eca8642018736254101c3b2a1908061c98550c050eca864201,
      0x218706543143b2a190804ca1c5941070eca8642013287160541c3b2a1908061cc98550070eca8642013287106541c3b2a1908061cc99450070eca8642018732654101c3b2a1908061c85950c050eca864201,
      0x8076543210c3b2a190804861d9500c50eca864201218765043143b2a190804ca1d9441070eca864201218760543143b2a190804ca1d8541070eca8642013287610541c3b2a1908061cc85950070eca864201,
      0x3821076541c3b2a1908060dd94850070eca8642018376524101c3b2a19080609d9450c050eca8642018376542101c3b2a19080609d9504c050eca864201827654310143b2a190805e1950c84030eca864201,
      0x281076543143b2a190804e085d941070eca8642013821760541c3b2a1908060dd88550070eca8642013821706541c3b2a1908060dd89450070eca8642018376254101c3b2a19080609d8550c050eca864201,
      0x281706543143b2a190804e09c5941070eca8642013827160541c3b2a1908060dc98550070eca8642013827106541c3b2a1908060dc99450070eca8642018372654101c3b2a19080609c5950c050eca864201,
      0x8706543210c3b2a190804a05d9500c50eca864201281765043143b2a190804e09d9441070eca864201281760543143b2a190804e09d8541070eca8642013827610541c3b2a1908060dc85950070eca864201,
      0x287106543143b2a190804e1c85941070eca8642013872160541c3b2a1908060c9d8550070eca8642013872106541c3b2a1908060c9d9450070eca8642018327654101c3b2a190806085d950c050eca864201,
      0x8760543210c3b2a190804a1c59500c50eca864201287165043143b2a190804e1c99441070eca864201287160543143b2a190804e1c98541070eca8642013872610541c3b2a1908060c9c5950070eca864201,
      0x8765043210c3b2a190804a1d85500c50eca864201287615043143b2a190804e1d89441070eca864201287610543143b2a190804e1d88541070eca8642013876210541c3b2a1908060c85d950070eca864201,
      0x87654321043b2a1908061d950c80430eca8642018765430210c3b2a190804a1d95040c50eca8642018765403210c3b2a190804a1d94500c50eca864201287651043143b2a190804e1d94841070eca864201],
    ![
      0x876543210310c3b2a180a1d95084c0a430eca8602876542310290c3b2a180a1d9504c808430eca8602876543210290c3b2a180a1d950c4808430eca8602876543210210c3b2a1809e1950c8402f0ca864201,
      0x72165438290c3b2a180a1d94c8500c430eca8602876532410310c3b2a180a1d94850c0a430eca8602876534210310c3b2a180a1d94904c0a430eca8602876524310290c3b2a180a1d9450c808430eca8602,
      0x72615438290c3b2a180a1d8d48500c430eca8602876352410310c3b2a180a1d89450c0a430eca8602876354210310c3b2a180a1d89504c0a430eca8602876254310290c3b2a180a1d8550c808430eca8602,
      0x708654321210c3b2a18081c9950c60a430eca8602072654138290c3b2a180a1d8c85500c430eca8602072651438290c3b2a180a1d8c94500c430eca8602876325410310c3b2a180a1d88550c0a430eca8602,
      0x76215438290c3b2a180a1cd948500c430eca8602873652410310c3b2a180a1c99450c0a430eca8602873654210310c3b2a180a1c99504c0a430eca8602872654310290c3b2a180a1c5950c808430eca8602,
      0x706854321210c3b2a18081d8950c60a430eca8602076254138290c3b2a180a1cd885500c430eca8602076251438290c3b2a180a1cd894500c430eca8602873625410310c3b2a180a1c98550c0a430eca8602,
      0x706584321210c3b2a18081d9490c60a430eca8602076524138290c3b2a180a1cc985500c430eca8602076521438290c3b2a180a1cc994500c430eca8602873265410310c3b2a180a1c85950c0a430eca8602,
      0x807654321090c3b2a1809c1950ca048430eca8602706543821210c3b2a18081d950c860a430eca8602706548321210c3b2a18081d9508c60a430eca8602076542138290c3b2a180a1cc859500c430eca8602,
      0x3821076541c032a190b9a0dd948500700ca8426e58376524101c032a118b9609d9450c042eca9064048376542101c032a190b9609d9504c042eca87040482765431010bb2a194011e1950c8402f0ca864201,
      0x28107654310410b2a1b94e085d9410700ca6428e63821760541c0329920b9a0dd885500700ca4286e53821706541c0329a10b9a0dd894500700ca4826e58376254101c0329218b9609d8550c042ecb086404,
      0x281706543104130aa1b94e09c59410700c6a428e63827160541c031a920b9a0dc985500700c4a286e53827106541c031aa10b9a0dc994500700c4a826e58372654101c0312a18b9609c5950c042ed0a86404,
      0x8706543210b8c32a19010a05d9500c4104ca862e5281765043104132a09b94e09d94410700c642a8e62817605431041328a1b94e09d85410700c64a28e63827610541c03192a0b9a0dc859500700c42a86e5,
      0x287106543104310aa1b94e1c8594107006ca428e63872160541c01b2920b9a0c9d855007004ca286e53872106541c01b2a10b9a0c9d945007004ca826e58327654101c0132a18b96085d950c042f0ca86404,
      0x8760543210b8b42a19010a1c59500c410c4a862e5287165043104312a09b94e1c9944107006c42a8e62871605431043128a1b94e1c9854107006c4a28e63872610541c01b12a0b9a0c9c595007004c2a86e5,
      0x8765043210b8b2c219010a1d85500c410ca4862e5287615043104329209b94e1d89441070064c2a8e62876105431043290a1b94e1d88541070064ca28e63876210541c01932a0b9a0c85d950070042ca86e5,
      0x87654321043b2a1908061d950c8042e2ca8650048765430210b8b2a1c1010a1d95040c410ca8642e58765403210b8b2a419010a1d94500c410ca8462e528765104310432a109b94e1d948410700642ca8e6],
    ![
      0x87654321019bb2a41081cdd9520804f0eca8604273765480213c3b2a19009e1d950c840e70eca84203876543210143b2a19080a1d950c84050eca864202876543210143b2a19080a1d950c84050eca864202,
      0x3210876541c3b2a1881261d950c48130eca8604288765432104c3b2a1900a21d950c841070eca8420387653421019bb2c21081cdd9610804f0eca6804273765840213c3b29a1009e1d94d0840e70eca84203,
      0x3218076541c3b229881261d914c48130ec8a604288764532104c3b229900a21d914c841070eca8420387635421019bb42a1081cdda150804f0ec6a804273768540213c3b1aa1009e1d8d50840e70eca84203,
      0x210876543143b2a18812a1d950c4814086ecb04288765432105021bb2940a010dd94861070eca842033218706541c3b21a881261d90d448130ec86a04288764352104c3b21a900a21d90d4841070eca84203,
      0x3281076541c3a329881261d194c48130e8ca604288746532104c3a329900a21d194c841070eca8420387365421019bc32a1081cde1950804f0e6ca804273786540213c39b2a1009e1cd950840e70eca84203,
      0x218076543143ab218812a1d590c481408e6cb042887564321050239b2940a011cd94861070eca842033281706541c3a31a881261d18d448130e8c6a04288746352104c3a31a900a21d18d4841070eca84203,
      0x218706543143aa318812a1d518c481408ec6b04288754632105023b1a940a011d8d4861070eca842033287106541c3a1b2881261d0d9448130e86ca04288743652104c3a1b2900a21d0d94841070eca84203,
      0x8076543210bc32a190815e1950c804a06eca90427786543021281bb2a1409c0dd950860e70eca84203218760543143aa1b0812a1d50d8481408eca704288754362105023b29940a011d94c861070eca84203,
      0x3821076541c23b298812611d94c481308eca604288476532104c23b29900a211d94c841070eca8420383765421019c3b2a1081ce1d950804f06eca804273876540213c1bb2a1009e0dd950840e70eca84203,
      0x281076543142bb218812a15d90c48140e86cb0428857643210503a1b2940a01d0d94861070eca842033821706541c23b1a8812611d8d4481308ec6a04288476352104c23b1a900a211d8d4841070eca84203,
      0x281706543142ba318812a15d18c48140e8c6b0428857463210503a31a940a01d18d4861070eca842033827106541c239b28812611cd94481308e6ca04288473652104c239b2900a211cd94841070eca84203,
      0x8706543210bb42a190815da150c804a0e6ca904277685430212839b2a1409c1cd950860e70eca84203281760543142ba1b0812a15d0d848140e8ca70428857436210503a329940a01d194c861070eca84203,
      0x287106543142a3b18812a151d8c48140ec86b0428854763210503b21a940a01d90d4861070eca842033872106541c21bb28812610dd944813086eca04288437652104c21bb2900a210dd94841070eca84203,
      0x8760543210bb2c2190815d9610c804a0ec6a90427765843021283b1aa1409c1d8d50860e70eca84203287160543142a39b0812a151cd848140ec8a70428854736210503b229940a01d914c861070eca84203,
      0x8765043210bb2a4190815d9520c804a0eca690427765483021283b29a1409c1d94d0860e70eca84203287610543142a1bb0812a150dd848140eca870428854376210503b2a1940a01d950c861070eca84203,
      0x87654321043b2a1908061d950c804250eca862028765430210943b2a09808a1d95040c470eca842038765403210bb2a1c10815d950e0804a0eca870427765438021283b2a19409c1d950c860e70eca84203],
    ![
      0x8765432101c3b2a19080e1d950c84070eca8642038765432101c3b2a19080e1d950c84070eca8642038765432101c3b2a19080e1d950c84070eca8642038765432101c3b2a19080e1d950c84070eca864203,
      0x3210876541a3b2c19082d1d960c80570eca82064c4765830215c3b2a0981321d9504c8190eca80642b4765803215c3b2a1881321d950c48190eca86042b876543210643b2a1900ae1d950c841706420eca83,
      0x3218076541a3b4299082d1da14c80570ec8a2064c4768530215c3b228981321d9144c8190ec8a0642b4768503215c3b229881321d914c48190ec8a6042b876453210643b229900ae1d914c841706420eca83,
      0x210876543110821bb2c248410dda1530eca82064d2104378654c3b2a0981361d9504c81b064208ecac2104387654c3b2a1881361d950c481b06420e8cac8765432106c19083b22b20c841d951906420eca83,
      0x3281076541a3c3299082d1e194c80570e8ca2064c4786530215c3a328981321d1944c8190e8ca0642b4786503215c3a329881321d194c48190e8ca6042b874653210643a329900ae1d194c841706420eca83,
      0x218076543110a01bb2c248500dda1530eac82064d2140378654c3ab20981361d5904c81b062408ecac2140387654c3ab21881361d590c481b06240e8cac8756432106c18903b22b20c481d951906420eca83,
      0x218706543110a183b2c24850c1da1530ea8c2064d2143078654c3aa30981361d5184c81b062048ecac2143087654c3aa31881361d518c481b06204e8cac8754632106c18813b22b20c409d951906420eca83,
      0x8076543210bc32a190819e1950c804c50eca862097865430213143b2a09824a1d95040d2806430ecab7865403213143b28a1824a1d94500d280642f0cab2876510434a0190bb42ad00c85d961706420eca83,
      0x3821076541a43b299082d21d94c805708eca2064c4876530215c23b289813211d944c81908eca0642b4876503215c23b298813211d94c481908eca6042b8476532106423b29900ae11d94c841706420eca83,
      0x281076543112081bb2c249040dda1530aec82064d2410378654c2bb209813615d904c81b026408ecac2410387654c2bb218813615d90c481b02640e8cac8576432106c09903b22b204c81d951906420eca83,
      0x2817065431120983b2c24904c1da1530ae8c2064d2413078654c2ba309813615d184c81b026048ecac2413087654c2ba318813615d18c481b02604e8cac8574632106c09813b22b204c09d951906420eca83,
      0x8706543210bb42a190819da150c804c4f0ca86209768543021313c32a098249e195040d2860430ecab768540321313c328a18249e194500d286042f0cab2786510434a1810bb42ad0c085d961706420eca83,
      0x2871065431121883b2c2490c41da1530a8ec2064d2431078654c2a3b098136151d84c81b020648ecac2431087654c2a3b188136151d8c481b02064e8cac8547632106c08193b22b2040c9d951906420eca83,
      0x8760543210bb2c2190819d9610c804c4ed0a86209765843021313b42a098249da15040d2864030ecab765840321313b428a18249da14500d286402f0cab2768510434a1900bb42ad0c805d961706420eca83,
      0x8765043210bb2a4190819d9520c804c4ecb086209765483021313b2c2098249d961040d2864210ecab765480321313b2c0a18249d960500d286420f0cab2765810434a19083b42ad0c841d961706420eca83,
      0x87654321043b2a1908061d950c804250eca862028765430210943b2a09808a1d95040c470eca842038765403210943b28a1808a1d94500c470eca4820328765104311c3b290a00ce1d948410706420eca83],
    ![
      0x1024376584940bb2a181c4090dd9612502eca86077685413025140bb2a181dda1504c094502eca86077685431025140bb2a181dda150c4094502eca8607210654387290832a1c394841950e1ca420ca870e5,
      0x2108765433940bb2a181c8421d950ce502eca86071024763584940bb2a181c4091d8d612502eca86071024736584940bb2a181c4091cd9612502eca86077685143025140bb2a181dda1450c094502eca8607,
      0x2107865433940bb2a181c841e1950ce502eca86071027463584940bb2a181c409d18d612502eca86071027436584940bb2a181c409d0d9612502eca86077681543025140bb2a181dda0550c094502eca8607,
      0x2108765431140bb2a181c8421d950c4502eca86072107658433940bb2a181c841d9610ce502eca86072107685433940bb2a181c841da150ce502eca86071027643584940bb2a181c409d90d612502eca8607,
      0x3281076541c38b2a18125e0d94850162f086ca04987365241019b932c2081de099450c0e2f0a8c604a87365421019b932a4081de099504c0e2f0a86c04a872654310143932a18809a1d50c8408d0ea864204,
      0x2180765431438b2a18128a1c59500ce4e70ca82073281760541c38b21a8125e0d88550162f08ca60493281706541c38b2298125e0d89450162f08c6a04987362541019b9342a081de098550c0e2f0ac8604a,
      0x2187065431438ab218128a1d85500ce4e6d0a82073287160541c38a31a8125e0c98550162f0c8a60493287106541c38a3298125e0c99450162f0c86a04987326541019b9432a081de085950c0e2f0ca8604a,
      0x8076543210bc32a190811e1950c804850eca862022187650431438aa1b0128a1d95040ce4e6ca902072187605431438aa318128a1d94500ce4e6cb082073287610541c38a1b28125e0c85950162f0ca86049,
      0x8127654305140bb2a180a049d90d412460eca90278127645304940bb2a1808c81da1504e460eca90278127654304940bb2a1808c81d96104e460eca90273207654813940bb2a180a085d950c04460eca9027,
      0x7208654312940bb2a180a049d50d814460eca90278127546305140bb2a180a049d0d9412460eca90278127564305140bb2a180a049d18d412460eca90278127465304940bb2a1808c81e19504e460eca9027,
      0x7206854312940bb2a180a0495d0d814460eca90278125746305140bb2a180a0491cd9412460eca90278125764305140bb2a180a0491d8d412460eca90278124765304940bb2a1808c821d9504e460eca9027,
      0x8706543210940bb2a1809c81950e04a460eca90277206548312940bb2a180a04950dd814460eca90277206584312940bb2a180a04951cd814460eca90278125476305140bb2a180a0490dd9412460eca9027,
      0x287106543103410aa1b94e1c85941062f086ca0493872160541c1832920b9a0c9d8550062f0a8c604a3872106541c1832a10b9a0c9d9450062f0a86c04a8327654101c1032a18b96085d950c0450eca86205,
      0x8760543210bb0c2a19010a1c59500c44e70ca8207287165043103412a09b94e1c99441062f08ca60492871605431034128a1b94e1c98541062f08c6a0493872610541c18312a0b9a0c9c5950062f0ac8604a,
      0x8765043210bb0ac219010a1d85500c44e6d0a8207287615043103429209b94e1d89441062f0c8a60492876105431034290a1b94e1d88541062f0c86a0493876210541c18132a0b9a0c85d950062f0ca8604a,
      0x87654321043b2a1908061d950c804250eca862028765430210bb0aa1c1010a1d95040c44e6ca902078765403210bb0aa419010a1d94500c44e6cb0820728765104310342a109b94e1d94841062f0ca86049],
    ![
      0x1024376584940bb2a18204090dd9612502eca86081024376584940bb2a18204090dd9612502eca860876854310253b42a188129da150c4094ed0a86204a76854310253b42a188129da150c4094ed0a86204a,
      0x2108765433940bb2a18208421d950ce502eca86082108765433940bb2a18208421d950ce502eca86081024736584940bb2a18204091cd9612502eca86081024736584940bb2a18204091cd9612502eca8608,
      0x2107865433940bb2a1820841e1950ce502eca86082107865433940bb2a1820841e1950ce502eca86081027436584940bb2a1820409d0d9612502eca86081027436584940bb2a1820409d0d9612502eca8608,
      0x2108765431140bb2a18208421d950c4502eca86082108765431140bb2a18208421d950c4502eca86082107685433940bb2a1820841da150ce502eca86082107685433940bb2a1820841da150ce502eca8608,
      0x3281076541a39b2c1082de0d94850190eca86240e783652410643b2a190839e099450c10e24860cb098736542101c39b2a1080dcc1950a04ee60ca850277306548213b9832a4109da1d50c840ad0ea864205,
      0x218076543110b821b2c24a1c59500d0cf06a8420e287165043433c1aa09038e1c99441186e90ca420b3281706541a39b429082de0d89450190eca68240e783625410643b29a10839e098550c10e24806cb09,
      0x218706543110ba01b2c24a1d85500d0cf0a68420e287615043433c29a09038e1d89441186e8d0a420b3287106541a39c329082de0c99450190ec6a8240e783265410643b1aa10839e085950c10e24086cb09,
      0x8076543210bc32a190815e1950c804a06eca90427786543021281bb2a1409c0dd950860e70eca84203218760543110ba1832c24a1d94500d0cf0a86420e287651043433c2a189038e1d94841186e8cb0420b,
      0x8127654305140bb2a180a049d90d412460eca902781276453049183b2c209cc81da1504e304eca86098127654304940bb2a1808c81d96104e460eca902732076548139183b2c209e085d950c04304eca8609,
      0x7208654312940bb2a180a049d50d814460eca902781275463051183b2c209e049d0d9412304eca86098127564305140bb2a180a049d18d412460eca902781274653049183b2c209cc81e19504e304eca8609,
      0x7206854312940bb2a180a0495d0d814460eca902781257463051183b2c209e0491cd9412304eca86098125764305140bb2a180a0491d8d412460eca902781247653049183b2c209cc821d9504e304eca8609,
      0x8706543210940bb2a1809c81950e04a460eca902772065483129183b2c209e04950dd814304eca86097206584312940bb2a180a04951cd814460eca902781254763051183b2c209e0490dd9412304eca8609,
      0x287106543103410aa1b94e1c85941062f086ca04938721605418bc21b029260c9d855006e24860cb093872106541c1832a10b9a0c9d9450062f0a86c04a83276541018bc2a18312a085d950c0470eca84206,
      0x8760543210bb0c2a19010a1c59500c44e70ca82072871650431139c328a01ce1c99441066e90ca420b2871605431034128a1b94e1c98541062f08c6a04938726105418bc231829260c9c595006e24806cb09,
      0x8765043210bb0ac219010a1d85500c44e6d0a82072876150431139b428a01ce1d89441066e8d0a420b2876105431034290a1b94e1d88541062f0c86a04938762105418bc321829260c85d95006e24086cb09,
      0x87654321043b2a1908061d950c804250eca862028765430210943b2a09808a1d95040c470eca842038765403210bb0aa419010a1d94500c44e6cb082072876510431139b2c0a01ce1d94841066e8cb0420b],
    ![
      0x8765432101c3b2a19080d0dd960805086ecb04028437658021421bb2c010a10dd960409286ecb020497865432103bc32a19081de1950c840ef0ca8642077865432103bc32a19081de1950c840ef0ca864207,
      0x3210876541a3b2c19082dd95040e09a50a8e6c02e76541083269baa41300b95040c9da1a70eca8420b7865342105b8aa0319435cd50a0581c46a8f0c20e735428610711aa3c0b0395040c9da1a70eca8420b,
      0x3218076541a3b4299082dd94500e09a50ae86c02e76514083269bac21300b9504c09da1a70eca8420b78635421059a8a013b435cd4920581c46ae90c20e735248610711aba40b039504c09da1a70eca8420b,
      0x210876543110821bb2c24861d9500d0c6ea90420e218765043431baa409038ca1d94411870eca8420b281760543393c328a182184d51c821cd0ea86402e6135470287343aa1810b8ca1d94411870eca8420b,
      0x3281076541a3c3299082dd85500e09a50ea86c02e76154083269bc2a1300b950c409da1a70eca8420b78365421059aa0813b435cc9520581c46ea90c20e732548610711baa40b03950c409da1a70eca8420b,
      0x218076543110a01bb2c2485e19500d0c6ae90420e217865043431aba409038c9e194411870eca8420b287160543393b428a1821854d1c821cd0ae86402e6153470287342ba1810b8c9e194411870eca8420b,
      0x218706543110a183b2c2485da1500d0c6a8f0420e217685043431aa3c09038c9da14411870eca8420b287610543393b2c0a18218550dc821cd0a8e6402e6154370287342a39810b8c9da14411870eca8420b,
      0x8076543210bc32a099010861d9500c450eca682072187650431143b298a01cca1d94410670eca8420b7865403212143b28a180809d94e050e48ecb060280276531843923b2c018a0ca1d94410670eca8420b,
      0x3821076541c23b298812611d94c481308eca604288476532104c23b29900a211d94c841070eca842038376542101a43b29908220dd950840690eca642088376542101a43b29908220dd950840690eca64208,
      0x281076543142bb218812a15d90c48140e86cb0428857643210503a1b2940a01d0d94861070eca842033821706541b8aa03194350dda14805646a8f0c20e437685021591aa3c0b03a05d914c81830eca8640c,
      0x281706543142ba318812a15d18c48140e8c6b0428857463210503a31a940a01d18d4861070eca8420338271065419a8a013b4350de194805646ae90c20e437865021591aba40b03a05d194c81830eca8640c,
      0x8706543210bb42a190815da150c804a0e6ca904277685430212839b2a1409c1cd950860e70eca84203281760543113c328a18209c50c1a152d0ea86402e2714308654b43aa1810ba05d518c81a30eca8640c,
      0x287106543142a3b18812a151d8c48140ec86b0428854763210503b21a940a01d90d4861070eca8420338721065419aa0813b4350e1d94805646ea90c20e438765021591baa40b03a051d94c81830eca8640c,
      0x8760543210bb2c2190815d9610c804a0ec6a90427765843021283b1aa1409c1d8d50860e70eca84203287160543113b428a18209d04c1a152d0ae86402e2741308654b42ba1810ba055d18c81a30eca8640c,
      0x8765043210bb2a4190815d9520c804a0eca690427765483021283b29a1409c1d94d0860e70eca84203287610543113b2c0a18209d0c41a152d0a8e6402e2743108654b42a39810ba0551d8c81a30eca8640c,
      0x87654321043b2a1908061d950c804250eca862028765430210943b2a09808a1d95040c470eca842038765403210943b28a1809c9952040ca48ecb060287265480132923b2c018a021d94c850e30eca8640c],
    ![
      0x78654132063c32a099031cd5208581ce6a9042c0e735482610739aa41308395040c9da1aa82064ed0d78654321043c32a190821e1950c8410f0ca86420878654321043c32a190821e1950c8410f0ca864208,
      0x3210876541990843b2a0dd95040e09aeca820704d7654108326bb2a08419355040c9da1aa82064ed0d78651432063c328a19031cd50a0581ce6a8502c0e735428610739aa14308395040c9da1aa82064ed0d,
      0x281704653409b3842a13984d5d0821d0eca86240f613574028743b2a19083cca1d944118f06420ca8c382710654639c13288230d9e150049d0ce6a8204e36785410274339aa00938ca1d944118f06420ca8c,
      0x2108765431010c3b2a19c861d9500d02c6ea9004e21876504340b1baa04138ca1d944118f06420ca8c281740653409b3c02a13984d51c821d0eca68240f613547028743b29a1083cca1d944118f06420ca8c,
      0x287104653409bb042a139854dd0821d0eac86240f615374028743ab219083cc9e1944118f06420ca8c387210654639943288230da1d50049d0c6ea8204e3687541027431baa00938c9e1944118f06420ca8c,
      0x21807654310140bb2a19c85e19500d02ce6a9004e21786504340b39aa04138c9e1944118f06420ca8c287140653409bb402a139854d1c821d0eac68240f615347028743ab1a1083cc9e1944118f06420ca8c,
      0x786502431281bb142a09c09d8d6050e26a850ec0e027635184389aa1433838ca1d944106f06420ca8c03762154839c3b10aa00c09d90e05506ea820d04d02764318541baa0843134ca1d944106f06420ca8c,
      0x8076543210bc3290a1814861d9500c450ec86a2082187650431143b218a820ca1d944106f06420ca8c786520431281bb412a09c09d94e050e26a904ec0e027653184389aa4133838ca1d944106f06420ca8c,
      0x3821076541b8aa30194350dd960805646a90ec20e437658021591aa438b03a05d950c81830ec8a640c8376542101b821b290c220dd9508406e086ca43088376542101b821b290c220dd9508406e086ca4308,
      0x281076543142bb218812a15d90c48140e86cb0428857643210503a1b2940a01d0d94861070eca842033821706541b8aa03194350dda14805646a8f0c20e437685021591aa3c0b03a05d914c81830eca8640c,
      0x281706543113c30aa18209c500da152d0ea68402e2714038654b43a9a010ba05d590c81a30ec8a640c3827106541b9c132882310de19480570ce6a8204e4378650215c339aa0093a05d194c81830eca8640d,
      0x8706543210bb42a190815da150c804a0e6ca904277685430212839b2a1409c1cd950860e70eca84203281760543113c328a18209c50c1a152d0ea86402e2714308654b43aa1810ba05d518c81a30eca8640c,
      0x287106543113b40aa18209d040da152d0ae68402e2741038654b42b9a010ba055d90c81a30ec8a640c3872106541b99432882310e1d9480570c6ea8204e4387650215c31baa0093a051d94c81830eca8640d,
      0x8760543210bb2c2190815d9610c804a0ec6a90427765843021283b1aa1409c1d8d50860e70eca84203287160543113b428a18209d04c1a152d0ae86402e2741308654b42ba1810ba055d18c81a30eca8640c,
      0x8765043210943b0aa1809c9961040ca48ed0a60287265840132923b42818a021d8d4850e30ec8a640c28761054311c3b10aa00e0551d808d46ea820d04d81547620351baa084313421d90c855030eca8640d,
      0x87654321043b2a1908061d950c804250eca862028765430210943b2a09808a1d95040c470eca842038765403210943b28a1809c9952040ca48ecb060287265480132923b2c018a021d94c850e30eca8640c],
    ![
      0x7465830215ba32c1810add1960c0856e8cb06042b7654108326bb2a0841935d950420c9aeca821064d7865432104bc32a190825e1950c8412f0ca8642097865432104bc32a190825e1950c8412f0ca864209,
      0x3210876541990843b2a0cc8421d950664210eca837654108326bb2a0841935d950420c9aeca821064d7465380215ba329c010add194e00856e8ca70042b7654108326bb2a0841935d950420c9aeca821064d,
      0x2014873654030992ba438184c95e11c62c0f04a8e21876504340b1baa0413858dd500a1c70eca8420d7863542106bb18aa01439d8c550209ce502ca086821876504340b1baa0413858dd500a1c70eca8420d,
      0x2108765431010c3b2a19c0861d94d0e0430eca86821876504340b1baa0413858dd500a1c70eca8420d20147836540309a93a438184d49e11c62c10e4a8e21876504340b1baa0413858dd500a1c70eca8420d,
      0x2041873654031892ba43818c495e11c42c10e6a8e21786504340b39aa0413859cd500a1c70eca8420d7836542106bb09aa01439d84d50209ce430ca086821786504340b39aa0413859cd500a1c70eca8420d,
      0x21807654310140bb2a19c0a05d94d0e0502eca86821786504340b39aa0413859cd500a1c70eca8420d20417836540318a93a43818c549e11c42c0f06a8e21786504340b39aa0413859cd500a1c70eca8420d,
      0x7865034213143b0a29824a1d85140d28064f02cab21876504311021bb0ac20810dd8615070eca8420d2876105434a0193b0c2ad00c9d856170642ec0a8321876504311021bb0ac20810dd8615070eca8420d,
      0x8076543210bc329920819e194c9004c50ec86a20921876504311021bb0ac20810dd8615070eca8420d7865304213143b20a9824a1d90540d280650e2cab21876504311021bb0ac20810dd8615070eca8420d,
      0x3821076541b8aa3019435c55180e09a2ea80d064d437658021591aa438b038c951e0581c68ed0a042b8376542101b821b290c21c10d94a050b0ec86420a8376542101b821b290c21c10d94a050b0ec86420a,
      0x281076543142bb218812a15d90c48140e86cb0428857643210503a1b2940a01d0d94861070eca842033821706541b8aa0319435c55018e09a2ea8c1064d437685021591aa3c0b038c9521c581c68ecb0042b,
      0x281706543113c30aa18209e185500d06f0c4a820c2714038654b43a9a010b9a1d4d0049c68ed0a042b3827106541b9c13288231ce09945018e502ca08684378650215c339aa0093a19cd50085ce420870ca9,
      0x8706543210bb42a190815da150c804a0e6ca904277685430212839b2a1409c1cd950860e70eca84203281760543113c328a18209e194500d06f0ca4820c2714308654b43aa1810b9a1d50c049c68ecb0042b,
      0x287106543113b40aa18209da05500d06ed04a820c2741038654b42b9a010b9a15cd0049c68ed0a042b3872106541b9943288231cca1945018e430ca08684387650215c31baa0093a18dd50085ce420870ca9,
      0x8760543210bb2c2190815d9610c804a0ec6a90427765843021283b1aa1409c1d8d50860e70eca84203287160543113b428a18209da14500d06ed0a4820c2741308654b42ba1810b9a15d0c049c68ecb0042b,
      0x8765043210943b0aa1808a1d85500c470ec4a8203716584032211bb428209c8dda14050e68ed0a042b28761054311c3b10aa00ce1d88541070642ec0a8308652174328c3b219282461d90c8152e420870ca9,
      0x87654321043b2a1908061d950c804250eca862028765430210943b2a09808a1d95040c470eca842038765403210943b28a1808a1d94500c470eca48203716548032211bb2c0209c8dd960050e68ecb0042b],
    ![
      0x312807465621b42b8903cc4a01d195886d0ae240f76835241062a18bb40139da0d490418a862ed004e534278601729a13c300b94d09e1805ca684f0c02e534278601729a13c300b94d09e1805ca684f0c02e,
      0x28107463541438b2a183c4d81e1491ca2ec50086f63105278472b38c1201be19c94500dea624c0f08e38217064562431ba9083dce18945018a268ce104e38217064562431ba9083dce18945018a268ce104e,
      0x3218076541881b9432a30c8601d9506206e50ca8c76835241062a18bb40139da0d490418a862ed004e78615430263c30aa18131e18550c098f0c2a8604c58764321072c3b219083961d90c841cb0ec86420e,
      0x210876543110c3b2a1820085e194d0e2c6ae9040e21876504341943b28a03058d5d00a1cf06240c8ac2814706354309aa3940384da1c1491d0ec6a8204f61354708271943b28a031e18d14841ef06240c8ac,
      0x273168543b1a83c210ba1d4d85081a70e2c8a04c3287160541bb18c1282304e1c981158a624c0f08e13526078474229339883cdd86094118e26c500a8c31762805463b18c12823152099cc41ea624c0f08e,
      0x7860524132943832298a00dc9a1450e70e2c8a04c027386154398bc23029304d49e1811ca624c0f08e0372615843892b21c3838e1c9854106e26c500a8c835716240698bc23029305e0d890158a624c0f08e,
      0x218706543110ba4329820851c18e152c6a4f0802e3287160541bb18c1282304e1c981158aec062850e28741063540b42813a1b99d48c5021d08a2ce640f31762805463b18c12823152099cc41eaec062850e,
      0x807654321090c3b2a1809e1894500ca50e8c6a02821876504311943b28a00ca1d18c4150f06240c8ac7862504132813b29c209c0de189450e24ae870c0e02765314839943b28a00c4d610981dcf06240c8ac,
      0x24180736543298ba4103994c5d2009c6f04ca820c186307254739b42a0813dcda150481ee270048cac716845032638b4228193159e0d0481cacf068240e716845032638b4228193159e0d0481cacf068240e,
      0x281076543113c0b2a18209e059500d06f04ca820c07216835438a9b239403854d91c821ce270048cac38217065418b984132a31ce18945018a268ce104e38217065418b984132a31ce18945018a268ce104e,
      0x2817065431120b81b2c24905c0da1530ae2c8064d278615043432bc1a0903995e0d0409c2ed08a064c38271065419c138832a0c60dc819158306e40c8ac17380246560b9c01232b0dda150409e6ed0a8204f,
      0x8706543210bb42a190815da150c804a0e6ca904277685430212839b2a1409c1cd950860e70eca842032817605431138a1832c249e194500d0d0ea86420e2714308654c0baa318135a1d50c049c30eca8604c,
      0x726805143283b11aa409c1d88d5060e70e4ca820308732615438ba91a340385d48d1821ce270048cac24780136540ac310239b8dd86094118e26c500a8c625713048740aa3b1183d4a11d84c1ea0ce26490e,
      0x87605432109438b2a1808a1c59500c470e4ca82037268150432923c1b028a091e0d80550e270048cac28716054311238b41a820e1c9854106e26c500a8c2741608354b129c3820b85e0d890158a0ce26490e,
      0x8765043210bb294218815d94a10c04a0ed06a8427287615043113b242898209d921440d02ed08a064c287610543103c310aa19c9d920540d02af06c804e24761805340c3ab1821389591e040dec0430e8a6f,
      0x87654321043b2a1908061d950c804250eca862028765430210943b2a09808a1d95040c470eca842038765403210b932a409814a1d94500c448ecb062087265480312843b299209c91d96004d030eca8604c]]
  let code (k : Fin 10) (m : Fin (2^8)) :=
    (blocks k (Fin.ofNat 16 (m.val/16))) >>> (41*(m.val%16))
  let choice (k m) := Fin.ofNat 16 ((code k m)%32)
  let lab (k m) (i : Fin 9) := Fin.ofNat 9 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 9,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by
    intro k
    fin_cases k <;> decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 9) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 100000000 in
lemma extensions_9 :
  let base (k : Fin 16) (i j : ℕ) := (0x2a064074148661078540e00004a01d3410c43414c86c0b80003303c0f4310c3c0f0701c00001303c0f03d0c3c0f0781e00001103c0f03d0e3c0f03c1e00003b01c0741104410f8701c00001b01c0701d04410f8781e00001901c0701d06418f83e1e00000901c0701c07418f83e1f00000f1f881204816018060170000071f881204812058060178000031f88120481204816017c0000f03c0f03c0f7c1f07c1f00000701c0701c0701df87e1f8000fe405014050140501404fe00001004010040100401005fe : ℕ).testBit (100*k.val+10*i+j)
  let next (k : Fin 31) (i j : ℕ) := (0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*k.val+10*i+j)
  let ext (k) (m : Fin (2^9)) (i j : ℕ) :=
    if i=9 then decide (j<9) && m.val.testBit j else if j=9 then m.val.testBit i
    else base k i j && !(m.val.testBit i && m.val.testBit j)
  ∀ k m,∃ t : Fin 31,∃ h : Equiv.Perm (Fin (9+1)),∀ i j,
    ext k m i.val j.val=true → next t (h i).val (h j).val=true := by
  intro base next ext
  let blocks : Fin 16 → Fin 32 → ℕ := ![
    ![
      0x98765432101cc3b2a19080661d95084c0530eca864201987654231014c3b2a1908061d950e4840330eca864201987654321014c3b2a1908061d950ca440330eca86420187654321900cc3b2a19080661d950c840130eca864200,
      0x987654321024c3b2a19080661d94c8500730eca86420198765324101cc3b2a19080661d94850c0530eca86420198765342101cc3b2a19080661d94904c0530eca864201987652431014c3b2a1908061d9524c840330eca864201,
      0x987645321024c3b2a19080661d8d48500730eca86420198763524101cc3b2a19080661d89450c0530eca86420198763542101cc3b2a19080661d89504c0530eca864201987625431014c3b2a1908061d9650c840330eca864201,
      0x32109876541cc3b2a19080661d90c8540930eca864201987643251024c3b2a19080661d8c85500730eca864201987643521024c3b2a19080661d8c94500730eca86420198763254101cc3b2a19080661d88550c0530eca864201,
      0x987465321024c3b2a19080661cd948500730eca86420198736524101cc3b2a19080661c99450c0530eca86420198736542101cc3b2a19080661c99504c0530eca864201987265431014c3b2a1908061da550c840330eca864201,
      0x32190876541cc3b2a19080661d18c8540930eca864201987463251024c3b2a19080661cd885500730eca864201987463521024c3b2a19080661cd894500730eca86420198736254101cc3b2a19080661c98550c0530eca864201,
      0x32198076541cc3b2a19080661d0d88540930eca864201987436251024c3b2a19080661cc985500730eca864201987436521024c3b2a19080661cc994500730eca86420198732654101cc3b2a19080661c85950c0530eca864201,
      0x210987654314c3b2a190804c8661d9410730eca86420132198760541cc3b2a19080661d0c85940930eca86420132198706541cc3b2a19080661d0c98540930eca864201987432651024c3b2a19080661cc859500730eca864201,
      0x984765321024c3b2a19080660dd948500730eca86420198376524101cc3b2a190806609d9450c0530eca86420198376542101cc3b2a190806609d9504c0530eca864201982765431014c3b2a1908061e5950c840330eca864201,
      0x32910876541cc3b2a190806611d8c8540930eca864201984763251024c3b2a19080660dd885500730eca864201984763521024c3b2a19080660dd894500730eca86420198376254101cc3b2a190806609d8550c0530eca864201,
      0x32918076541cc3b2a190806611cd88540930eca864201984736251024c3b2a19080660dc985500730eca864201984736521024c3b2a19080660dc994500730eca86420198372654101cc3b2a190806609c5950c0530eca864201,
      0x219087654314c3b2a190804ca461d9410730eca86420132918760541cc3b2a190806611cc85940930eca86420132918706541cc3b2a190806611cc98540930eca864201984732651024c3b2a19080660dc859500730eca864201,
      0x32981076541cc3b2a190806610dd88540930eca864201984376251024c3b2a19080660c9d85500730eca864201984376521024c3b2a19080660c9d94500730eca86420198327654101cc3b2a1908066085d950c0530eca864201,
      0x219807654314c3b2a190804ca605d9410730eca86420132981760541cc3b2a190806610dc85940930eca86420132981706541cc3b2a190806610dc98540930eca864201984372651024c3b2a19080660c9c59500730eca864201,
      0x219870654314c3b2a190804ca61c59410730eca86420132987160541cc3b2a190806610c9c5940930eca86420132987106541cc3b2a190806610c9d8540930eca864201984327651024c3b2a19080660c85d9500730eca864201,
      0x90876543210cc3b2a1908048661d9500c530eca864201219876504314c3b2a190804ca61d94410730eca864201219876054314c3b2a190804ca61d85410730eca86420132987610541cc3b2a190806610c85d940930eca864201,
      0x948765321024c3b2a1908064e1d948500730eca86420193876524101cc3b2a1908064a1d9450c0530eca86420193876542101cc3b2a1908064a1d9504c0530eca864201928765431014c3b2a19080625d950c840330eca864201,
      0x39210876541cc3b2a190806521d8c8540930eca864201948763251024c3b2a1908064e1d885500730eca864201948763521024c3b2a1908064e1d894500730eca86420193876254101cc3b2a1908064a1d8550c0530eca864201,
      0x39218076541cc3b2a190806521cd88540930eca864201948736251024c3b2a1908064e1c985500730eca864201948736521024c3b2a1908064e1c994500730eca86420193872654101cc3b2a1908064a1c5950c0530eca864201,
      0x291087654314c3b2a190804e4861d9410730eca86420139218760541cc3b2a190806521cc85940930eca86420139218706541cc3b2a190806521cc98540930eca864201948732651024c3b2a1908064e1c859500730eca864201,
      0x39281076541cc3b2a190806520dd88540930eca864201948376251024c3b2a1908064e09d85500730eca864201948376521024c3b2a1908064e09d94500730eca86420193827654101cc3b2a1908064a05d950c0530eca864201,
      0x291807654314c3b2a190804e4a05d9410730eca86420139281760541cc3b2a190806520dc85940930eca86420139281706541cc3b2a190806520dc98540930eca864201948372651024c3b2a1908064e09c59500730eca864201,
      0x291870654314c3b2a190804e4a1c59410730eca86420139287160541cc3b2a190806520c9c5940930eca86420139287106541cc3b2a190806520c9d8540930eca864201948327651024c3b2a1908064e085d9500730eca864201,
      0x98076543210cc3b2a190804a461d9500c530eca864201291876504314c3b2a190804e4a1d94410730eca864201291876054314c3b2a190804e4a1d85410730eca86420139287610541cc3b2a190806520c85d940930eca864201,
      0x39821076541cc3b2a19080650e1d88540930eca864201943876251024c3b2a1908064ca1d85500730eca864201943876521024c3b2a1908064ca1d94500730eca86420193287654101cc3b2a1908064861d950c0530eca864201,
      0x298107654314c3b2a190804e6085d9410730eca86420139821760541cc3b2a19080650e1c85940930eca86420139821706541cc3b2a19080650e1c98540930eca864201943872651024c3b2a1908064ca1c59500730eca864201,
      0x298170654314c3b2a190804e609c59410730eca86420139827160541cc3b2a19080650e09c5940930eca86420139827106541cc3b2a19080650e09d8540930eca864201943827651024c3b2a1908064ca05d9500730eca864201,
      0x98706543210cc3b2a190804a605d9500c530eca864201298176504314c3b2a190804e609d94410730eca864201298176054314c3b2a190804e609d85410730eca86420139827610541cc3b2a19080650e085d940930eca864201,
      0x298710654314c3b2a190804e61c859410730eca86420139872160541cc3b2a19080650ca1c5940930eca86420139872106541cc3b2a19080650ca1d8540930eca864201943287651024c3b2a1908064c861d9500730eca864201,
      0x98760543210cc3b2a190804a61c59500c530eca864201298716504314c3b2a190804e61c994410730eca864201298716054314c3b2a190804e61c985410730eca86420139872610541cc3b2a19080650ca05d940930eca864201,
      0x98765043210cc3b2a190804a61d85500c530eca864201298761504314c3b2a190804e61d894410730eca864201298761054314c3b2a190804e61d885410730eca86420139876210541cc3b2a19080650c861d940930eca864201,
      0x98765432104c3b2a19080661d950c804330eca86420198765430210cc3b2a190804a61d95040c530eca86420198765403210cc3b2a190804a61d94500c530eca864201298765104314c3b2a190804e61d948410730eca864201],
    ![
      0x9876543210390cc3b2a180a61d95084c0c4330eca86029876542310310cc3b2a180a61d9504c80a4330eca86029876543210310cc3b2a180a61d950c480a4330eca86029876543210290cc3b2a180a25d950c840312eca864201,
      0x832176549390cc3b2a180a61d94c8500e4330eca86029876532410390cc3b2a180a61d94850c0c4330eca86029876534210390cc3b2a180a61d94904c0c4330eca86029876524310310cc3b2a180a61d9450c80a4330eca8602,
      0x832716549390cc3b2a180a61d8d48500e4330eca86029876352410390cc3b2a180a61d89450c0c4330eca86029876354210390cc3b2a180a61d89504c0c4330eca86029876254310310cc3b2a180a61d8550c80a4330eca8602,
      0x821765439310cc3b2a180820c9d95064e4330eca86020832765149390cc3b2a180a61d8c85500e4330eca86020832761549390cc3b2a180a61d8c94500e4330eca86029876325410390cc3b2a180a61d88550c0c4330eca8602,
      0x837216549390cc3b2a180a61cd948500e4330eca86029873652410390cc3b2a180a61c99450c0c4330eca86029873654210390cc3b2a180a61c99504c0c4330eca86029872654310310cc3b2a180a61c5950c80a4330eca8602,
      0x827165439310cc3b2a180820dc995064e4330eca86020837265149390cc3b2a180a61cd885500e4330eca86020837261549390cc3b2a180a61cd894500e4330eca86029873625410390cc3b2a180a61c98550c0c4330eca8602,
      0x827615439310cc3b2a180820dd895064e4330eca86020837625149390cc3b2a180a61cc985500e4330eca86020837621549390cc3b2a180a61cc994500e4330eca86029873265410390cc3b2a180a61c85950c0c4330eca8602,
      0x8097654321290cc3b2a1808209d950c64c4330eca86020827654139310cc3b2a180820dd950864e4330eca86020827651439310cc3b2a180820dd949064e4330eca86020837652149390cc3b2a180a61cc859500e4330eca8602,
      0x873216549390cc3b2a180a60dd948500e4330eca86029837652410390cc3b2a180a609d9450c0c4330eca86029837654210390cc3b2a180a609d9504c0c4330eca86029827654310310cc3b2a180a605d950c80a4330eca8602,
      0x872165439310cc3b2a180821cc995064e4330eca86020873265149390cc3b2a180a60dd885500e4330eca86020873261549390cc3b2a180a60dd894500e4330eca86029837625410390cc3b2a180a609d8550c0c4330eca8602,
      0x872615439310cc3b2a180821cd895064e4330eca86020873625149390cc3b2a180a60dc985500e4330eca86020873621549390cc3b2a180a60dc994500e4330eca86029837265410390cc3b2a180a609c5950c0c4330eca8602,
      0x8079654321290cc3b2a180821c9950c64c4330eca86020872654139310cc3b2a180821cd950864e4330eca86020872651439310cc3b2a180821cd949064e4330eca86020873652149390cc3b2a180a60dc859500e4330eca8602,
      0x876215439310cc3b2a180821d8c95064e4330eca86020876325149390cc3b2a180a60c9d85500e4330eca86020876321549390cc3b2a180a60c9d94500e4330eca86029832765410390cc3b2a180a6085d950c0c4330eca8602,
      0x8076954321290cc3b2a180821d8950c64c4330eca86020876254139310cc3b2a180821d8d50864e4330eca86020876251439310cc3b2a180821d8d49064e4330eca86020876352149390cc3b2a180a60c9c59500e4330eca8602,
      0x8076594321290cc3b2a180821d9490c64c4330eca86020876524139310cc3b2a180821d94d0864e4330eca86020876521439310cc3b2a180821d94c9064e4330eca86020876532149390cc3b2a180a60c85d9500e4330eca8602,
      0x9087654321090cc3b2a180a01d950ca44a4330eca86028076543921290cc3b2a180821d950c864c4330eca86028076549321290cc3b2a180821d9508c64c4330eca86020876542139310cc3b2a180821d950c864e4330eca8602,
      0x94876532102483b2a190c1e4e1d948500720eca84270693876524101c83b2a118c1a4a1d9450c0430eca92640593876542101c83b2a190c1a4a1d9504c0430eca872405928765431010c3b2a19481625d950c840312eca864201,
      0x3921087654184990bb2a41e521d8c8540920eca64290794876325102483b29920c1e4e1d885500720eca42870694876352102483b29a10c1e4e1d894500720eca48270693876254101c83b29218c1a4a1d8550c0430ecb286405,
      0x39218076541849938b2a41e521cd88540920ec6a4290794873625102483b1a920c1e4e1c985500720ec4a2870694873652102483b1aa10c1e4e1c994500720ec4a8270693872654101c83b12a18c1a4a1c5950c0430ed2a86405,
      0x291087654310490bb2a1c18e4861d941061264eca83073921876054184993b28a41e521cc85940920ec642a9073921870654184993b0aa41e521cc98540920ec64a290794873265102483b192a0c1e4e1c859500720ec42a8706,
      0x39281076541849b90b2a41e520dd88540920e6ca42907948376251024839b2920c1e4e09d85500720e4ca28706948376521024839b2a10c1e4e09d94500720e4ca8270693827654101c83932a18c1a4a05d950c0430f2ca86405,
      0x2918076543104938b2a1c18e4a05d94106126e4ca830739281760541849b9328a41e520dc85940920e6c42a90739281706541849b930aa41e520dc98540920e6c4a2907948372651024839b12a0c1e4e09c59500720e4c2a8706,
      0x291870654310493b0aa1c18e4a1c594106126ec4a830739287160541849bb128a41e520c9c5940920e64c2a90739287106541849bb10aa41e520c9d8540920e64ca2907948327651024839932a0c1e4e085d9500720e42ca8706,
      0x98076543210c0cbb2a19014a461d9500c4124eca86306291876504310493b2a09c18e4a1d944106126eca84307291876054310493b28a1c18e4a1d854106126eca4830739287610541849bb290a41e520c85d940920e642ca907,
      0x3982107654184b990b2a41e50e1d885409206eca4290794387625102481bb2920c1e4ca1d855007204eca2870694387652102481bb2a10c1e4ca1d945007204eca8270693287654101c813b2a18c1a4861d950c04312eca86405,
      0x2981076543104b90b2a1c18e6085d9410612e64ca83073982176054184b99328a41e50e1c859409206ec42a9073982170654184b9930aa41e50e1c985409206ec4a290794387265102481bb12a0c1e4ca1c595007204ec2a8706,
      0x2981706543104b930aa1c18e609c59410612e6c4a83073982716054184b9b128a41e50e09c59409206e4c2a9073982710654184b9b10aa41e50e09d85409206e4ca290794382765102481b932a0c1e4ca05d95007204e2ca8706,
      0x98706543210c0bcb2a19014a605d9500c412e4ca863062981765043104b932a09c18e609d94410612e6ca843072981760543104b9328a1c18e609d85410612e6ca483073982761054184b9b290a41e50e085d9409206e42ca907,
      0x2987106543104bb10aa1c18e61c859410612ec64a83073987216054184bb1928a41e50ca1c594092064ec2a9073987210654184bb190aa41e50ca1d854092064eca29079432876510248193b2a0c1e4c861d950072042eca8706,
      0x98760543210c0bb4aa19014a61c59500c412ec4a863062987165043104bb12a09c18e61c994410612ec6a843072987160543104bb128a1c18e61c985410612ec6a483073987261054184bb1a90a41e50ca05d94092064e2ca907,
      0x98765043210c0bb2ca19014a61d85500c412eca4863062987615043104bb29209c18e61d894410612eca6843072987610543104bb290a1c18e61d885410612eca6483073987621054184bb2990a41e50c861d940920642eca907,
      0x98765432104c3b2a19080661d950c804302eca86520598765430210c0bb2a1c9014a61d95040c412eca86430698765403210c0bb2a499014a61d94500c412eca8463062987651043104bb2a109c18e61d948410612eca864307],
    ![
      0x987654321019c3b2a490820e1d9524805130eca860428387654902144c3b2a1900a261d950c8410730eca84203987654321014c3b2a19080a61d950c840530eca864202987654321014c3b2a19080a61d950c840530eca864202,
      0x987654321024c3b2a18812a61d950c481530eca860429987654321054c3b2a1900a661d950c8412730eca84203987653421019c3b2ca10820e1d9650805130eca680428387659402144c3b29a100a261d94d08410730eca84203,
      0x987645321024c3b2298812a61d914c481530ec8a60429987645321054c3b229900a661d914c8412730eca84203987635421019c3b4aa10820e1da550805130ec6a80428387695402144c3b1aa100a261d8d508410730eca84203,
      0x32109876541cc3b2a18813261d950c481930eca86042b987654321064c3b2a1900ae61d950c8416730eca84203987643521024c3b21a8812a61d90d4481530ec86a0429987643521054c3b21a900a661d90d48412730eca84203,
      0x987465321024c3a3298812a61d194c481530e8ca60429987465321054c3a329900a661d194c8412730eca84203987365421019c3cb2a10820e1e5950805130e6ca80428387965402144c39b2a100a261cd9508410730eca84203,
      0x32190876541cc3ab218813261d590c481930eac86042b987564321064c3ab21900ae61d590c8416730eca84203987463521024c3a31a8812a61d18d4481530e8c6a0429987463521054c3a31a900a661d18d48412730eca84203,
      0x32198076541cc3aa318813261d518c481930ea8c6042b987546321064c3aa31900ae61d518c8416730eca84203987436521024c3a1b28812a61d0d94481530e86ca0429987436521054c3a1b2900a661d0d948412730eca84203,
      0x210987654314c3b2a18813661d950c481a0870ecb242998765432106821c3b2948a410e1d948652730eca8420332198706541cc3aa1b0813261d50d8481930ea86c042b987543621064c3aa1b100ae61d50d88416730eca84203,
      0x984765321024c23b298812a611d94c4815308eca60429984765321054c23b29900a6611d94c8412730eca84203983765421019c4bb2a10820e25d9508051306eca80428389765402144c1bb2a100a260dd9508410730eca84203,
      0x32910876541cc2bb2188132615d90c481930aec86042b985764321064c2bb21900ae615d90c8416730eca84203984763521024c23b1a8812a611d8d44815308ec6a0429984763521054c23b1a900a6611d8d48412730eca84203,
      0x32918076541cc2ba3188132615d18c481930ae8c6042b985746321064c2ba31900ae615d18c8416730eca84203984736521024c239b28812a611cd944815308e6ca0429984736521054c239b2900a6611cd948412730eca84203,
      0x219087654314c33aa188136619d50c481a0906ecb2429986754321068241bb2948a4120dd948652730eca8420332918706541cc2ba1b08132615d0d8481930ae86c042b985743621064c2ba1b100ae615d0d88416730eca84203,
      0x32981076541cc2a3b1881326151d8c481930a8ec6042b985476321064c2a3b1900ae6151d8c8416730eca84203984376521024c21bb28812a610dd9448153086eca0429984376521054c21bb2900a6610dd948412730eca84203,
      0x219807654314c32ba1881366195d0c481a090e6cb24299865743210682439b2948a4121cd948652730eca8420332981706541cc2a39b081326151cd8481930a8e6c042b985473621064c2a39b100ae6151cd88416730eca84203,
      0x219870654314c32a398813661951cc481a090ec6b2429986547321068243b1a948a4121d8d48652730eca8420332987106541cc2a1bb081326150dd8481930a86ec042b985437621064c2a1bb100ae6150dd88416730eca84203,
      0x90876543210c4bb2a19081a25d950c804c070eca924288976543021301c3b2a148a00e1d9508650730eca84203219876054314c32a1b8813661950dc481a090eca72429986543721068243b29948a4121d94c8652730eca84203,
      0x948765321024a43b298812a521d94c4815290eca60429948765321054a43b29900a6521d94c8412730eca84203938765421019cc3b2a10820e61d9508051270eca804283987654021449c3b2a100a24e1d9508410730eca84203,
      0x39210876541cac3b2188132561d90c48192b0ec86042b958764321064ac3b21900ae561d90c8416730eca84203948763521024a43b1a8812a521d8d44815290ec6a0429948763521054a43b1a900a6521d8d48412730eca84203,
      0x39218076541cac3a3188132561d18c48192b0e8c6042b958746321064ac3a31900ae561d18c8416730eca84203948736521024a439b28812a521cd944815290e6ca0429948736521054a439b2900a6521cd948412730eca84203,
      0x291087654314b43aa1881365a1d50c481a1086ecb2429968754321068421bb2948a4210dd948652730eca8420339218706541cac3a1b08132561d0d848192b0e86c042b958743621064ac3a1b100ae561d0d88416730eca84203,
      0x39281076541cac23b1881325611d8c48192b08ec6042b958476321064ac23b1900ae5611d8c8416730eca84203948376521024a41bb28812a520dd9448152906eca0429948376521054a41bb2900a6520dd948412730eca84203,
      0x291807654314b42ba1881365a15d0c481a108e6cb24299685743210684239b2948a4211cd948652730eca8420339281706541cac239b081325611cd848192b08e6c042b958473621064ac239b100ae5611cd88416730eca84203,
      0x291870654314b42a39881365a151cc481a108ec6b2429968547321068423b1a948a4211d8d48652730eca8420339287106541cac21bb081325610dd848192b086ec042b958437621064ac21bb100ae5610dd88416730eca84203,
      0x98076543210c3cb2a19081a1e5950c804c106eca9242887965430213041bb2a148a020dd9508650730eca84203291876054314b42a1b881365a150dc481a108eca72429968543721068423b29948a4211d94c8652730eca84203,
      0x39821076541caa43b1881325521d8c48192a90ec6042b954876321064aa43b1900ae5521d8c8416730eca84203943876521024a1c3b28812a50e1d9448152870eca0429943876521054a1c3b2900a650e1d948412730eca84203,
      0x298107654314b2c3a1881365961d0c481a10e86cb242996587432106843a1b2948a421d0d948652730eca8420339821706541caa439b081325521cd848192a90e6c042b954873621064aa439b100ae5521cd88416730eca84203,
      0x298170654314b2c2398813659611cc481a10e8c6b242996584732106843a31a948a421d18d48652730eca8420339827106541caa41bb081325520dd848192a906ec042b954837621064aa41bb100ae5520dd88416730eca84203,
      0x98706543210c3b4aa19081a1da550c804c10e6ca92428876954302130439b2a148a021cd9508650730eca84203298176054314b2c21b8813659610dc481a10e8ca7242996584372106843a329948a421d194c8652730eca84203,
      0x298710654314b2a4398813659521cc481a10ec86b242996548732106843b21a948a421d90d48652730eca8420339872106541caa1c3b08132550e1d848192a870ec042b954387621064aa1c3b100ae550e1d88416730eca84203,
      0x98760543210c3b2ca19081a1d9650c804c10ec6a9242887659430213043b1aa148a021d8d508650730eca84203298716054314b2a41b8813659520dc481a10ec8a7242996548372106843b229948a421d914c8652730eca84203,
      0x98765043210c3b2a499081a1d9524c804c10eca69242887654930213043b29a148a021d94d08650730eca84203298761054314b2a1c3881365950e1c481a10eca87242996543872106843b2a1948a421d950c8652730eca84203,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca8420398765403210c3b2a1c9081a1d950e4804c10eca87242887654390213043b2a1948a021d950c8650730eca84203],
    ![
      0x98765432101cc3b2a19080e61d950c840730eca86420398765432101cc3b2a19080e61d950c840730eca86420398765432101cc3b2a19080e61d950c840730eca86420398765432101cc3b2a19080e61d950c840730eca864203,
      0x98765432102243b2c99083921d964c805d30eca82064f487659302174c3b2a09813e61d9504c81f30eca80642e487659032174c3b2a18813e61d950c481f30eca86042e98765432107cc3b2a1900ba61d950c841c930eca64204,
      0x98764532102243b4a99083921da54c805d30ec8a2064f487695302174c3b2289813e61d9144c81f30ec8a0642e487695032174c3b2298813e61d914c481f30ec8a6042e98764532107cc3b229900ba61d914c841c930eca64204,
      0x32109876541cc3b2a1081ca61d95084c2530eca820651987654231094c3b2a09814661d9504c82330eca806430987654321094c3b2a18814661d950c482330eca86043098765432108cc3b2a1900c261d950c8420930eca64204,
      0x98746532102243cb299083921e594c805d30e8ca2064f487965302174c3a3289813e61d1944c81f30e8ca0642e487965032174c3a3298813e61d194c481f30e8ca6042e98746532107cc3a329900ba61d194c841c930eca64204,
      0x32190876541cc3ab21081ca61d59084c2530eac820651987564231094c3ab209814661d5904c82330eac806430987564321094c3ab218814661d590c482330eac86043098756432108cc3ab21900c261d590c8420930eca64204,
      0x32198076541cc3aa31081ca61d51884c2530ea8c20651987546231094c3aa309814661d5184c82330ea8c06430987546321094c3aa318814661d518c482330ea8c6043098754632108cc3aa31900c261d518c8420930eca64204,
      0x210987654311082a1c3b4b084150e1e59930eca820653210543897664c3b2a09814e61d9504c8260a90ed26430210543987664c3b2a18814e61d950c48260a90ec724309876543210982a43b1948c01521d8c8660930eca64204,
      0x98476532102244bb2990839225d94c805d308eca2064f489765302174c23b289813e611d944c81f308eca0642e489765032174c23b298813e611d94c481f308eca6042e98476532107cc23b29900ba611d94c841c930eca64204,
      0x32910876541cc2bb21081ca615d9084c2530aec820651985764231094c2bb2098146615d904c82330aec806430985764321094c2bb2188146615d90c482330aec86043098576432108cc2bb21900c2615d90c8420930eca64204,
      0x32918076541cc2ba31081ca615d1884c2530ae8c20651985746231094c2ba3098146615d184c82330ae8c06430985746321094c2ba3188146615d18c482330ae8c6043098574632108cc2ba31900c2615d18c8420930eca64204,
      0x2190876543110a821c3b4b085410e1e59930cea820653215043897664c33aa09814e619d504c8260b08ed26430215043987664c33aa18814e619d50c48260b08ec724309867543210982c23b1948c01611d8c8660930eca64204,
      0x32981076541cc2a3b1081ca6151d884c2530a8ec20651985476231094c2a3b0981466151d84c82330a8ec06430985476321094c2a3b1881466151d8c482330a8ec6043098547632108cc2a3b1900c26151d8c8420930eca64204,
      0x2198076543110aa01c3b4b085500e1e59930cae820653215403897664c32ba09814e6195d04c8260b0e8d26430215403987664c32ba18814e6195d0c48260b0e8c724309865743210982c3a31948c0161d18c8660930eca64204,
      0x2198706543110aa1843b4b08550c21e59930ca8e20653215430897664c32a389814e61951c4c8260b0ec926430215430987664c32a398814e61951cc48260b0ec8724309865473210982c3b21948c0161d90c8660930eca64204,
      0x90876543210c4bb2a19081e25d950c804e530eca8620a8976543021394c3b2a09828a61d95040d4090ecb2642e8976540321394c3b28a1828a61d94500d4090eca7242e298765104350243b29948b8121d94c865c930eca64204,
      0x9487653210224c3b2990839261d94c805d290eca2064f498765302174a43b289813e521d944c81f290eca0642e498765032174a43b298813e521d94c481f290eca6042e94876532107ca43b29900ba521d94c841c930eca64204,
      0x39210876541cac3b21081ca561d9084c252b0ec820651958764231094ac3b2098146561d904c8232b0ec806430958764321094ac3b2188146561d90c48232b0ec86043095876432108cac3b21900c2561d90c8420930eca64204,
      0x39218076541cac3a31081ca561d1884c252b0e8c20651958746231094ac3a3098146561d184c8232b0e8c06430958746321094ac3a3188146561d18c48232b0e8c6043095874632108cac3a31900c2561d18c8420930eca64204,
      0x29108765431128821c3b4b094410e1e5992d0ea820653251043897664b43aa09814e5a1d504c82610a8ed26430251043987664b43aa18814e5a1d50c482610a8ec7243096875432109842a3b1948c02151d8c8660930eca64204,
      0x39281076541cac23b1081ca5611d884c252b08ec20651958476231094ac23b0981465611d84c8232b08ec06430958476321094ac23b1881465611d8c48232b08ec6043095847632108cac23b1900c25611d8c8420930eca64204,
      0x29180765431128a01c3b4b094500e1e5992d0ae820653251403897664b42ba09814e5a15d04c82610ae8d26430251403987664b42ba18814e5a15d0c482610ae8c7243096857432109842ba31948c0215d18c8660930eca64204,
      0x29187065431128a1843b4b09450c21e5992d0a8e20653251430897664b42a389814e5a151c4c82610aec926430251430987664b42a398814e5a151cc482610aec87243096854732109842bb21948c0215d90c8660930eca64204,
      0x98076543210c3cb2a19081e1e5950c804e512eca8620a87965430213944bb2a09828a25d95040d4108ecb2642e87965403213944bb28a1828a25d94500d4108eca7242e289765104350423b29948b8211d94c865c930eca64204,
      0x39821076541caa43b1081ca5521d884c252a90ec20651954876231094aa43b0981465521d84c8232a90ec06430954876321094aa43b1881465521d8c48232a90ec6043095487632108caa43b1900c25521d8c8420930eca64204,
      0x2981076543112a081c3b4b095040e1e5992cb0e820653254103897664b2c3a09814e5961d04c82610ea8d26430254103987664b2c3a18814e5961d0c482610ea8c7243096587432109843aa31948c021d518c8660930eca64204,
      0x2981706543112a09843b4b09504c21e5992cb08e20653254130897664b2c2389814e59611c4c82610eac926430254130987664b2c2398814e59611cc482610eac87243096584732109843ab21948c021d590c8660930eca64204,
      0x98706543210c3b4aa19081e1da550c804e50f2ca8620a87695430213943cb2a09828a1e595040d410e8cb2642e87695403213943cb28a1828a1e594500d410e8ca7242e28796510435043a329948b821d194c865c930eca64204,
      0x2987106543112a18843b4b0950c421e5992ca90e20653254310897664b2a4389814e59521c4c82610eca926430254310987664b2a4398814e59521cc482610eca87243096548732109843b2a1948c021d950c8660930eca64204,
      0x98760543210c3b2ca19081e1d9650c804e50ed2a8620a87659430213943b4aa09828a1da55040d410ec8b2642e87659403213943b4a8a1828a1da54500d410ec8a7242e28769510435043b229948b821d914c865c930eca64204,
      0x98765043210c3b2a499081e1d9524c804e50ecb28620a87654930213943b2ca09828a1d965040d410eca92642e87654903213943b2c8a1828a1d964500d410eca87242e28765910435043b2a1948b821d950c865c930eca64204,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca48203298765104311cc3b290a00ce61d9484106930eca64204],
    ![
      0x10254387696148c3b2a182040950e1da585230eca860887965413026948c3b2a18221e59504c09a5230eca860887965431026948c3b2a18221e5950c409a5230eca8608210765439831083b2a1cc18841d950e60c420eca87306,
      0x10243876595148c3b2a18204090e1d96545230eca860810254873696148c3b2a1820409521cda585230eca860810254837696148c3b2a1820409520dda585230eca860887965143026948c3b2a18221e59450c09a5230eca8608,
      0x10248376595148c3b2a182040920dd96545230eca860810258473696148c3b2a1820409611cda585230eca860810258437696148c3b2a1820409610dda585230eca860887961543026948c3b2a18221e58550c09a5230eca8608,
      0x21098765434148c3b2a182084261d950d05230eca860810248763595148c3b2a182040921d8d6545230eca860810248736595148c3b2a182040921cd96545230eca860810258743696148c3b2a182040961d0da585230eca8608,
      0x10284376595148c3b2a182040a10dd96545230eca860810285473696148c3b2a182040a151cda585230eca860810285437696148c3b2a182040a150dda585230eca860887916543026948c3b2a18221e45950c09a5230eca8608,
      0x21089765434148c3b2a182084225d950d05230eca860810284763595148c3b2a182040a11d8d6545230eca860810284736595148c3b2a182040a11cd96545230eca860810285743696148c3b2a182040a15d0da585230eca8608,
      0x21087965434148c3b2a18208421e5950d05230eca860810287463595148c3b2a182040a1d18d6545230eca860810287436595148c3b2a182040a1d0d96545230eca860810287543696148c3b2a182040a1d50da585230eca8608,
      0x21098765431148c3b2a182084261d950c45230eca860821087659434148c3b2a18208421d9650d05230eca860821087695434148c3b2a18208421da550d05230eca860810287643595148c3b2a182040a1d90d6545230eca8608,
      0x984765321024c0bb2a1812a24dd948501c312a86ec04c983765241019c13b2ca0822249d9450c10312ca8e604d983765421019c13b2a48822249d9504c10312ca86e04d982765431014c13b2a18809e61950c840af30ca864205,
      0x32910876541cc0bb2a18130e6085d9411c31286eca04a984763251024c0bb21a812a24dd885501c312a8ec604c984763521024c0bb229812a24dd894501c312a8e6c04c983762541019c13b4aa0822249d8550c10312cae8604d,
      0x32918076541cc0bab218130e609c59411c3128e6ca04a984736251024c0ba31a812a24dc985501c312ae8c604c984736521024c0ba329812a24dc994501c312ae86c04c983726541019c13cb2a0822249c5950c10312cea8604d,
      0x219087654314c0bb2a18134a605d9500d05072eca820832918760541cc0baa1b0130e609d94411c3128eca604a32918706541cc0baa318130e609d85411c3128ec6a04a984732651024c0ba1b2812a24dc859501c312aec8604c,
      0x32981076541cc0abb218130e61c859411c312e86ca04a984376251024c0a3b1a812a24c9d85501c312ea8c604c984376521024c0a3b29812a24c9d94501c312ea86c04c983276541019c14bb2a08222485d950c10312eca8604d,
      0x219807654314c0b3aa18134a61c59500d0506f2ca820832981760541cc0aba1b0130e61c994411c312e8ca604a32981706541cc0aba318130e61c985411c312e8c6a04a984372651024c0a39b2812a24c9c59501c312eac8604c,
      0x219870654314c0b2ba18134a61d85500d0506ed2a820832987160541cc0aa39b0130e61d894411c312ec8a604a32987106541cc0aa3b18130e61d885411c312ec86a04a984327651024c0a1bb2812a24c85d9501c312eca8604c,
      0x90876543210c4bb2a19081625d950c804a530eca86202219876504314c0b2a1b8134a61d95040d0506eca92208219876054314c0b2a398134a61d94500d0506ecb2820832987610541cc0aa1bb0130e61d948411c312eca8604a,
      0x91287654306148c3b2a180a44a1d90d4144610eca922891287645305148c3b2a1808c821da550504610eca922891287654305148c3b2a1808c821d9650504610eca922832087654914148c3b2a180a4861d950c044610eca9228,
      0x91287654306948c3b2a180a44a1d50d8184610eca922891287546306148c3b2a180a44a1d0d94144610eca922891287564306148c3b2a180a44a1d18d4144610eca922891287465305148c3b2a1808c821e5950504610eca9228,
      0x91286754306948c3b2a180a44a15d0d8184610eca922891285746306148c3b2a180a44a11cd94144610eca922891285764306148c3b2a180a44a11d8d4144610eca922891284765305148c3b2a1808c8225d950504610eca9228,
      0x82097654313148c3b2a180a44a1950dc1a4610eca922891286547306948c3b2a180a44a150dd8184610eca922891286574306948c3b2a180a44a151cd8184610eca922891285476306148c3b2a180a44a10dd94144610eca9228,
      0x91268754306948c3b2a180a44961d0d8184610eca922891258746306148c3b2a180a44921cd94144610eca922891258764306148c3b2a180a44921d8d4144610eca922891248765305148c3b2a1808c8261d950504610eca9228,
      0x82079654313148c3b2a180a449a150dc1a4610eca922891268547306948c3b2a180a449610dd8184610eca922891268574306948c3b2a180a449611cd8184610eca922891258476306148c3b2a180a44920dd94144610eca9228,
      0x82076954313148c3b2a180a4499610dc1a4610eca922891265847306948c3b2a180a449520dd8184610eca922891265874306948c3b2a180a449521cd8184610eca922891254876306148c3b2a180a4490e1d94144610eca9228,
      0x98076543210948c3b2a180a081d950e44c4610eca922882076549313148c3b2a180a449950e1c1a4610eca922882076594313148c3b2a180a4499520dc1a4610eca922891265487306948c3b2a180a44950e1d8184610eca9228,
      0x3982107654183c990b2a41e50e1d885408312a86ec04c943876251024983b2920c1e4ca1d855006312ca8e604d943876521024983b2a10c1e4ca1d945006312ca86e04d93287654101c903b2a18c1a4861d950c04530eca86206,
      0x2981076543103c90b2a1c18e6085d9410631286eca04a3982176054183c99328a41e50e1c859408312a8ec604c3982170654183c9930aa41e50e1c985408312a8e6c04c943872651024983b12a0c1e4ca1c595006312cae8604d,
      0x2981706543103c930aa1c18e609c5941063128e6ca04a3982716054183c9b128a41e50e09c59408312ae8c604c3982710654183c9b10aa41e50e09d85408312ae86c04c943827651024983932a0c1e4ca05d95006312cea8604d,
      0x98706543210c38cb2a19014a605d9500c45072eca82082981765043103c932a09c18e609d9441063128eca604a2981760543103c9328a1c18e609d8541063128ec6a04a3982761054183c9b290a41e50e085d9408312aec8604c,
      0x2987106543103cb10aa1c18e61c8594106312e86ca04a3987216054183cb1928a41e50ca1c59408312ea8c604c3987210654183cb190aa41e50ca1d85408312ea86c04c9432876510249813b2a0c1e4c861d95006312eca8604d,
      0x98760543210c38b4aa19014a61c59500c4506f2ca82082987165043103cb12a09c18e61c9944106312e8ca604a2987160543103cb128a1c18e61c9854106312e8c6a04a3987261054183cb1a90a41e50ca05d9408312eac8604c,
      0x98765043210c38b2ca19014a61d85500c4506ed2a82082987615043103cb29209c18e61d8944106312ec8a604a2987610543103cb290a1c18e61d8854106312ec86a04a3987621054183cb2990a41e50c861d9408312eca8604c,
      0x98765432104c3b2a19080661d950c8042530eca8620298765430210c38b2a1c9014a61d95040c4506eca9220898765403210c38b2a499014a61d94500c4506ecb282082987651043103cb2a109c18e61d9484106312eca8604a],
    ![
      0x10254387696148c3b2a182440950e1da585230eca860910254387696148c3b2a182440950e1da585230eca860987965431026c3cb2a1881361e5950c409b0f2ca86204d87965431026c3cb2a1881361e5950c409b0f2ca86204d,
      0x10243876595148c3b2a18244090e1d96545230eca860910243876595148c3b2a18244090e1d96545230eca860910254837696148c3b2a1824409520dda585230eca860910254837696148c3b2a1824409520dda585230eca8609,
      0x10248376595148c3b2a182440920dd96545230eca860910248376595148c3b2a182440920dd96545230eca860910258437696148c3b2a1824409610dda585230eca860910258437696148c3b2a1824409610dda585230eca8609,
      0x21098765434148c3b2a182484261d950d05230eca860921098765434148c3b2a182484261d950d05230eca860910248736595148c3b2a182440921cd96545230eca860910248736595148c3b2a182440921cd96545230eca8609,
      0x10284376595148c3b2a182440a10dd96545230eca860910284376595148c3b2a182440a10dd96545230eca860910285437696148c3b2a182440a150dda585230eca860910285437696148c3b2a182440a150dda585230eca8609,
      0x21089765434148c3b2a182484225d950d05230eca860921089765434148c3b2a182484225d950d05230eca860910284736595148c3b2a182440a11cd96545230eca860910284736595148c3b2a182440a11cd96545230eca8609,
      0x21087965434148c3b2a18248421e5950d05230eca860921087965434148c3b2a18248421e5950d05230eca860910287436595148c3b2a182440a1d0d96545230eca860910287436595148c3b2a182440a1d0d96545230eca8609,
      0x21098765431148c3b2a182484261d950c45230eca860921098765431148c3b2a182484261d950c45230eca860921087695434148c3b2a18248421da550d05230eca860921087695434148c3b2a18248421da550d05230eca8609,
      0x98476532102241bb2c9083a24dd948501f30eca86241489376524107cc3b2a190852249d9450c13024a860ed2c98376542101cc1bb2a1080e0c1d950a451060eca85228830765492144183b2a490a1e61950c840cf30ca864206,
      0x32910876541cc13b2a081c8e6085d94120f1286ca4215398217605484c3b2a19085624dd8855020512a8ec207298476352102241bb4a9083a24dd894501f30eca68241489376254107cc3b29a10852249d8550c13024a806ed2c,
      0x32918076541cc13ab2081c8e609c594120f128c6a4215398271605484c3b2299085624dc9855020512ae8c207298473652102241bcb29083a24dc994501f30ec6a8241489372654107cc3b1aa10852249c5950c13024a086ed2c,
      0x2190876543110c02a1bb4b0a605d9500d2f126ca8421429817650434bc49b2a09050e609d94411e7092eca420e32918706541cc13aa3081c8e609d854120f128ca64215398276105484c3b21a9085624dc8595020512aec82072,
      0x32981076541cc12bb2081c8e61c8594120f12c86a4215398721605484c3a3299085624c9d855020512ea8c207298437652102241cbb29083a24c9d94501f30e6ca8241489327654107cc39b2a108522485d950c130240a86ed2c,
      0x2198076543110c2821bb4b0a61c59500d2f12c6a8421429871650434bc4b1aa09050e61c994411e708f2ca420e32981706541cc12ba3081c8e61c9854120f12c8a64215398726105484c3a31a9085624c9c595020512eac82072,
      0x2198706543110c2a01bb4b0a61d85500d2f12ca68421429876150434bc4b29a09050e61d894411e708ed2a420e32987106541cc12a3b081c8e61d8854120f12ca864215398762105484c3a1b29085624c85d95020512eca82072,
      0x90876543210c4bb2a19081a25d950c804c070eca924288976543021301c3b2a148a00e1d9508650730eca842032198760543110c2a183b4b0a61d94500d2f12ca86421429876510434bc4b2a189050e61d948411e708ecb2420e,
      0x91287654306148c3b2a180a44a1d90d4144610eca92289128764530511843b2ca0a0c821da550503250eca860a91287654305148c3b2a1808c821d9650504610eca92283208765491411843b2ca0a24861d950c043250eca860a,
      0x91287654306948c3b2a180a44a1d50d8184610eca92289128754630611843b2ca0a244a1d0d94143250eca860a91287564306148c3b2a180a44a1d18d4144610eca92289128746530511843b2ca0a0c821e5950503250eca860a,
      0x91286754306948c3b2a180a44a15d0d8184610eca92289128574630611843b2ca0a244a11cd94143250eca860a91285764306148c3b2a180a44a11d8d4144610eca92289128476530511843b2ca0a0c8225d950503250eca860a,
      0x82097654313148c3b2a180a44a1950dc1a4610eca92289128654730691843b2ca0a244a150dd8183250eca860a91286574306948c3b2a180a44a151cd8184610eca92289128547630611843b2ca0a244a10dd94143250eca860a,
      0x91268754306948c3b2a180a44961d0d8184610eca92289125874630611843b2ca0a244921cd94143250eca860a91258764306148c3b2a180a44921d8d4144610eca92289124876530511843b2ca0a0c8261d950503250eca860a,
      0x82079654313148c3b2a180a449a150dc1a4610eca92289126854730691843b2ca0a2449610dd8183250eca860a91268574306948c3b2a180a449611cd8184610eca92289125847630611843b2ca0a244920dd94143250eca860a,
      0x82076954313148c3b2a180a4499610dc1a4610eca92289126584730691843b2ca0a2449520dd8183250eca860a91265874306948c3b2a180a449521cd8184610eca92289125487630611843b2ca0a24490e1d94143250eca860a,
      0x98076543210948c3b2a180a081d950e44c4610eca92288207654931311843b2ca0a2449950e1c1a3250eca860a82076594313148c3b2a180a4499520dc1a4610eca92289126548730691843b2ca0a244950e1d8183250eca860a,
      0x3982107654183c990b2a41e50e1d885408312a86ec04c943876251020c4aa1b831324ca1d855007024a860ed2c943876521024983b2a10c1e4ca1d945006312ca86e04d932876541018c4b2a1839364861d950c04730eca84207,
      0x2981076543103c90b2a1c18e6085d9410631286eca04a398217605418c4a1bb0292a50e1c859408512a8ec20723982170654183c9930aa41e50e1c985408312a8e6c04c943872651020c4aa39831324ca1c595007024a806ed2c,
      0x2981706543103c930aa1c18e609c5941063128e6ca04a398271605418c4a39b0292a50e09c59408512ae8c20723982710654183c9b10aa41e50e09d85408312ae86c04c943827651020c4aba1831324ca05d95007024a086ed2c,
      0x98706543210c38cb2a19014a605d9500c45072eca820829817650431141cbb28a020e609d9441067092eca420e2981760543103c9328a1c18e609d8541063128ec6a04a398276105418c4a3b18292a50e085d9408512aec82072,
      0x2987106543103cb10aa1c18e61c8594106312e86ca04a398721605418c4ba1b0292a50ca1c59408512ea8c20723987210654183cb190aa41e50ca1d85408312ea86c04c943287651020c4baa1831324c861d950070240a86ed2c,
      0x98760543210c38b4aa19014a61c59500c4506f2ca820829871650431141bcb28a020e61c9944106708f2ca420e2987160543103cb128a1c18e61c9854106312e8c6a04a398726105418c4ba318292a50ca05d9408512eac82072,
      0x98765043210c38b2ca19014a61d85500c4506ed2a820829876150431141bb4a8a020e61d8944106708ed2a420e2987610543103cb290a1c18e61d8854106312ec86a04a398762105418c4bb218292a50c861d9408512eca82072,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca8420398765403210c38b2a499014a61d94500c4506ecb2820829876510431141bb2c8a020e61d9484106708ecb2420e],
    ![
      0x102543876960812a1c3b4b040950e1da58204a870ed2c102543876960812a1c3b4b040950e1da58204a870ed2c102543876960812a1c3b4b040950e1da58204a870ed2c102543876960812a1c3b4b040950e1da58204a870ed2c,
      0x10243876595148c3b2a182c4090e1d96545230eca860b10243876595148c3b2a182c4090e1d96545230eca860b10243876595148c3b2a182c4090e1d96545230eca860b10243876595148c3b2a182c4090e1d96545230eca860b,
      0x10248376595148c3b2a182c40920dd96545230eca860b10248376595148c3b2a182c40920dd96545230eca860b10248376595148c3b2a182c40920dd96545230eca860b10248376595148c3b2a182c40920dd96545230eca860b,
      0x21098765434148c3b2a182c84261d950d05230eca860b21098765434148c3b2a182c84261d950d05230eca860b21098765434148c3b2a182c84261d950d05230eca860b21098765434148c3b2a182c84261d950d05230eca860b,
      0x10284376595148c3b2a182c40a10dd96545230eca860b10284376595148c3b2a182c40a10dd96545230eca860b10284376595148c3b2a182c40a10dd96545230eca860b10284376595148c3b2a182c40a10dd96545230eca860b,
      0x21089765434148c3b2a182c84225d950d05230eca860b21089765434148c3b2a182c84225d950d05230eca860b21089765434148c3b2a182c84225d950d05230eca860b21089765434148c3b2a182c84225d950d05230eca860b,
      0x21087965434148c3b2a182c8421e5950d05230eca860b21087965434148c3b2a182c8421e5950d05230eca860b21087965434148c3b2a182c8421e5950d05230eca860b21087965434148c3b2a182c8421e5950d05230eca860b,
      0x21098765431148c3b2a182c84261d950c45230eca860b21098765431148c3b2a182c84261d950c45230eca860b21098765431148c3b2a182c84261d950c45230eca860b21098765431148c3b2a182c84261d950c45230eca860b,
      0x984765321024c23b2990812101d94ca45d080eca6522e840765392174203b29c90ba249d9450c15124eca2860a840765932174203b2c990ba249d9504c15124eca8260a892765431054493b2a18829e61950c840ef30ca864207,
      0x3291087654181c10cbb2a38c148521e5a130eca842616305214897684c3b2a11885a24dd8855023120ca4286f5305214987684c3b2a19085a24dd8945023120ca4826f589376254108c48329218bd6249d8550c17024860ecb2a,
      0x3291807654181c148bb2a38c149061e5a130ec8a42616305241897684c3b2291885a24dc9855023120c4a286f5305241987684c3b2299085a24dc9945023120c4a826f589372654108c48312a18bd6249c5950c17024806ecb2a,
      0x2190876543110c021bb2ca8a605d9500d61304ca862f52981765043584c132a09bd4e609d944122f128ca642162981760543584c1328a1bd4e609d854122f128ca4621639827610548bc4a3290985940d0861da61061242eca8e,
      0x3298107654181c490bb2a38c150861e5a130e8ca42616305421897684c3a3291885a24c9d8550231204ca286f5305421987684c3a3299085a24c9d9450231204ca826f589327654108c48132a18bd62485d950c17024086ecb2a,
      0x2198076543110c201bb2ca8a61c59500d6130c4a862f52987165043584c312a09bd4e61c9944122f12c8a642162987160543584c3128a1bd4e61c9854122f12c8a4621639872610548bc4b2290985940c9061da61060522eca8e,
      0x2198706543110c2183b2ca8a61d85500d6130ca4862f52987615043584c329209bd4e61d8944122f12ca8642162987610543584c3290a1bd4e61d8854122f12ca84621639876210548bc4b2a10985940c8521da61060432eca8e,
      0x90876543210c4bb2a19081e25d950c804e530eca8620a8976543021394c3b2a09828a61d95040d4090ecb2642e8976540321394c3b28a1828a61d94500d4090eca7242e298765104350243b29948b8121d94c865c930eca64204,
      0x91287654306148c3b2a180a44a1d90d4144610eca92289128764530511843b2ca0a0c821da550503250eca860a9128765430511843b4aa0a0c821d9650503250ec8a60a320876549140c943b21a82a4861d950c043250eca860c,
      0x91287654306948c3b2a180a44a1d50d8184610eca92289128754630611843b2ca0a244a1d0d94143250eca860a9128756430611843b4aa0a244a1d18d4143250ec8a60a912874653050c943b21a828c821e5950503250eca860c,
      0x91286754306948c3b2a180a44a15d0d8184610eca92289128574630611843b2ca0a244a11cd94143250eca860a9128576430611843b4aa0a244a11d8d4143250ec8a60a912847653050c943b21a828c8225d950503250eca860c,
      0x82097654313148c3b2a180a44a1950dc1a4610eca92289128654730691843b2ca0a244a150dd8183250eca860a9128657430691843b4aa0a244a151cd8183250ec8a60a912854763060c943b21a82a44a10dd94143250eca860c,
      0x91268754306948c3b2a180a44961d0d8184610eca92289125874630611843b2ca0a244921cd94143250eca860a9125876430611843b4aa0a244921d8d4143250ec8a60a912487653050c943b21a828c8261d950503250eca860c,
      0x82079654313148c3b2a180a449a150dc1a4610eca92289126854730691843b2ca0a2449610dd8183250eca860a9126857430691843b4aa0a2449611cd8183250ec8a60a912584763060c943b21a82a44920dd94143250eca860c,
      0x82076954313148c3b2a180a4499610dc1a4610eca92289126584730691843b2ca0a2449520dd8183250eca860a9126587430691843b4aa0a2449521cd8183250ec8a60a912548763060c943b21a82a4490e1d94143250eca860c,
      0x98076543210948c3b2a180a081d950e44c4610eca92288207654931311843b2ca0a2449950e1c1a3250eca860a8207659431311843b4aa0a24499520dc1a3250ec8a60a912654873068c943b21a82a44950e1d8183250eca860c,
      0x3982107654183c990b2a41e50e1d885408312a86ec04c943876251020c4aa1b831324ca1d855007024a860ed2c943876521020c4aa183b1324ca1d945007024a86e0d2c93287654101c092a1bb04b24861d950c04e10642ca927,
      0x2981076543103c90b2a1c18e6085d9410631286eca04a398217605418c4a1bb0292a50e1c859408512a8ec2072398217065418c4a1b83292a50e1c985408512a8e2c07294387265102144aa38831ca4ca1c595007024860ecb2a,
      0x2981706543103c930aa1c18e609c5941063128e6ca04a398271605418c4a39b0292a50e09c59408512ae8c2072398271065418c4a3983292a50e09d85408512ae82c07294382765102144aba0831ca4ca05d95007024806ecb2a,
      0x98706543210c38cb2a19014a605d9500c45072eca820829817650431141cbb28a020e609d9441067092eca420e29817605431141cbb0aa020e609d8541067092ec4a20e398276105419c24bb10a83a50e085d9409061242eca8e,
      0x2987106543103cb10aa1c18e61c8594106312e86ca04a398721605418c4ba1b0292a50ca1c59408512ea8c2072398721065418c4ba183292a50ca1d85408512ea82c07294328765102144baa0831ca4c861d95007024086ecb2a,
      0x98760543210c38b4aa19014a61c59500c4506f2ca820829871650431141bcb28a020e61c9944106708f2ca420e29871605431141bcb0aa020e61c9854106708f2c4a20e398726105419c23cb10a83a50ca05d9409060522eca8e,
      0x98765043210c38b2ca19014a61d85500c4506ed2a820829876150431141bb4a8a020e61d8944106708ed2a420e29876105431141bb48aa020e61d8854106708ed24a20e398762105419c23b490a83a50c861d9409060432eca8e,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca48203298765104311cc3b290a00ce61d9484106930eca64204],
    ![
      0x98765432101cc3b2a19080d0e1d9648052870ecb2402943876590214a1c3b2c810a50e1d9644094870ecb2204a8976543210444bb2a19082225d950c841112eca8642088976543210444bb2a19082225d950c841112eca864208,
      0x98765432102243b2c99083a1d95040e4a652ca906e034876541093299c32a49380d0419521cca66730eca8420e8976534210740b2a03994ce0d950a45c2846ca912e2148365429710a11b2a448b850419521cca66730eca8420e,
      0x98764532102243b4a99083a1d94500e4a652cb086e034876514093299c32ca1380d0419611cca66730eca8420e8976354210740b2823994ce0d949245c2846cb092e2148365249710a11b2c248b850419611cca66730eca8420e,
      0x32109876541cc3b2a1081c8c84195225e630a8ec72417321065498798c2a3b19485c41521d8ca62730eca8420e392187065471b082a143cce49950e041eb30eca8624179265438017acc3b2a19085c41521d8ca62730eca8420e,
      0x98746532102243cb299083a1d85500e4a652d0a86e034876154093299c34aa1380d041a151cca66730eca8420e8973654210740b02a3994ce0d895245c2846d0a92e2148362549710a11b42a48b85041a151cca66730eca8420e,
      0x32190876541cc3ab21081c8c85815225e630ae8c72417321605498798c2ba319485c41611d8ca62730eca8420e392817065471b0a82143cce49914e041eb30eac8624179264538017acc3ab219085c41611d8ca62730eca8420e,
      0x32198076541cc3aa31081c8c85941225e630aec872417321650498798c2bb219485c4161d18ca62730eca8420e392871065471b0aa0143cce4990d6041eb30ea8c624179264358017acc3aa319085c4161d18ca62730eca8420e,
      0x210987654311082a1c3b4b08661d9500d2e70ca92421421987650434b9c32a489050ca61d94411e730eca8420e29187605434144bb28a1825c4d95208268f30ca8640347136548029a3cc32a1810d0ca61d94411e730eca8420e,
      0x98476532102244bb299083a1c59500e4a6530ca86e034871654093299c4b2a1380d0421951cca66730eca8420e8937654210740832a3994ce0c995245c28470ca92e2148326549710a11c32a48b850421951cca66730eca8420e,
      0x32910876541cc2bb21081c8c98415225e630ea8c72417326105498798c3aa319485c42151d8ca62730eca8420e398217065471b2882143cce49194e041eb30aec8624179246538017acc2bb219085c42151d8ca62730eca8420e,
      0x32918076541cc2ba31081c8c98541225e630eac872417326150498798c3ab219485c4215d18ca62730eca8420e398271065471b28a0143cce4918d6041eb30ae8c624179246358017acc2ba319085c4215d18ca62730eca8420e,
      0x2190876543110a821c3b4b08625d9500d2e6d0a92421421897650434b9b42a489050ca25d94411e730eca8420e29817605434143cb28a1825c58d5208268f2d0a8640347163548029a3cb42a1810d0ca25d94411e730eca8420e,
      0x32981076541cc2a3b1081c8c99441225e630eca872417326510498798c3b2a19485c421d518ca62730eca8420e398721065471b2a08143cce490d96041eb30a8ec624179243658017acc2a3b19085c421d518ca62730eca8420e,
      0x2198076543110aa01c3b4b0861e59500d2e6cb092421421879650434b9b2c2489050ca1e594411e730eca8420e29871605434143b4a8a1825c594d208268f2cb08640347165348029a3cb2c21810d0ca1e594411e730eca8420e,
      0x2198706543110aa1843b4b0861da5500d2e6ca912421421876950434b9b2a4489050ca1da54411e730eca8420e29876105434143b2c8a1825c5950e08268f2ca90640347165438029a3cb2a41810d0ca1da54411e730eca8420e,
      0x90876543210c4bb2a0990148661d9500c4530eca682082198765043114c3b298a020ca61d944106730eca8420e8976540321294c3b28a18080a1d94e4510490ecb26029028765319441243b2c818a4ca61d944106730eca8420e,
      0x948765321024a43b298812a521d94c4815290eca60429948765321054a43b29900a6521d94c8412730eca8420393876542101a4c3b29908264e1d9508406930eca6420993876542101a4c3b29908264e1d9508406930eca64209,
      0x39210876541cac3b2188132561d90c48192b0ec86042b958764321064ac3b21900ae561d90c8416730eca842039487635210240b2a03994cd0e1da54805c46ca912e2144387695021711b2a448b852461d914c81e330eca8640f,
      0x39218076541cac3a3188132561d18c48192b0e8c6042b958746321064ac3a31900ae561d18c8416730eca842039487365210240b2823994cd0e1e594805c46cb092e2144387965021711b2c248b852461d194c81e330eca8640f,
      0x291087654314b43aa1881365a1d50c481a1086ecb2429968754321068421bb2948a4210dd948652730eca84203392187065419b082a143cce4a1d5184c2530eca862417928754631094c3b2a19085e461d518c822330eca8640f,
      0x39281076541cac23b1881325611d8c48192b08ec6042b958476321064ac23b1900ae5611d8c8416730eca842039483765210240b02a3994cd0e25d94805c46d0a92e2144389765021711b42a48b8524611d94c81e330eca8640f,
      0x291807654314b42ba1881365a15d0c481a108e6cb24299685743210684239b2948a4211cd948652730eca84203392817065419b0a82143cce4a15d184c2530eac862417928574631094c3ab219085e4615d18c822330eca8640f,
      0x291870654314b42a39881365a151cc481a108ec6b2429968547321068423b1a948a4211d8d48652730eca84203392871065419b0aa0143cce4a151d84c2530ea8c62417928547631094c3aa319085e46151d8c822330eca8640f,
      0x98076543210c3cb2a19081a1e5950c804c106eca9242887965430213041bb2a148a020dd9508650730eca8420329187605431144bb28a1824a0550c1e598f30ca864034281543097663cc32a1810d2461951cc826330eca8640f,
      0x39821076541caa43b1881325521d8c48192a90ec6042b954876321064aa43b1900ae5521d8c8416730eca842039438765210240832a3994cd0e61d94805c470ca92e2144398765021711c32a48b8524521d94c81e330eca8640f,
      0x298107654314b2c3a1881365961d0c481a10e86cb242996587432106843a1b2948a421d0d948652730eca84203398217065419b2882143cce4961d184c2530aec862417925874631094c2bb219085e4561d18c822330eca8640f,
      0x298170654314b2c2398813659611cc481a10e8c6b242996584732106843a31a948a421d18d48652730eca84203398271065419b28a0143cce49611d84c2530ae8c62417925847631094c2ba319085e45611d8c822330eca8640f,
      0x98706543210c3b4aa19081a1da550c804c10e6ca92428876954302130439b2a148a021cd9508650730eca8420329817605431143cb28a1824a1450c1e598f2d0a864034285143097663cb42a1810d245a151cc826330eca8640f,
      0x298710654314b2a4398813659521cc481a10ec86b242996548732106843b21a948a421d90d48652730eca84203398721065419b2a08143cce49521d84c2530a8ec62417925487631094c2a3b19085e45521d8c822330eca8640f,
      0x98760543210c3b2ca19081a1d9650c804c10ec6a9242887659430213043b1aa148a021d8d508650730eca8420329871605431143b4a8a1824a1504c1e598f2cb0864034285413097663cb2c21810d2459611cc826330eca8640f,
      0x98765043210c3b2a499081a1d9524c804c10eca69242887654930213043b29a148a021d94d08650730eca8420329876105431143b2c8a1824a150c41e598f2ca9064034285431097663cb2a41810d2459521cc826330eca8640f,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a180a09d952440cc490ecb26029827654901331243b2c818a4261d94c8510330eca8640f],
    ![
      0x89765413207c4bb2a09903e0d952485c2906ca9242e148365492710a41b2a4938850419521cca6620ca90e653389765432104c4bb2a19082625d950c841312eca86420989765432104c4bb2a19082625d950c841312eca864209,
      0x987654321024c3b2a1908121d95040e4a70eca820725387654109329c3b2a084994c419521cca6620ca90e653389765143207c4bb28a1903e0d950a45c2906ca8522e148365429710a41b2a14b8850419521cca6620ca90e6533,
      0x392180576484c3b2a190866499520c41eb30eca8624189265483017acc3b2a19086041521d8ca62730eca842108976354210840aa03b194c4e5da150806f12ec6a804373976854021bc4bb1aa100dc41521d8ca62730eca84210,
      0x321098765418190cc3b2a38c84195225e652cb086e0353210654987994b2c21838d441521d8ca62730eca84210392185076484c3b29a1086649950e041eb30eca6824189265438017acc3b29a1086041521d8ca62730eca84210,
      0x392810576484c3ab2190866499160c41eb30eac8624189264583017acc3ab219086041611d8ca62730eca842108973654210840a823b194c4e5e1950806f12e6ca804373978654021bc4b9b2a100dc41611d8ca62730eca84210,
      0x3219087654181948c3b2a38c85815225e652d0a86e0353216054987994b42a1838d441611d8ca62730eca84210392815076484c3ab1a1086649914e041eb30eac6824189264538017acc3ab1a1086041611d8ca62730eca84210,
      0x2918704653481cbb142a0ddc4d9610826830aec6924187136584029a0c2bb1a14860ca61d94411e730eca84210392871065479c4bb10aa0404a1d95240eef30ca8640359035476218bbcc32a1810d4ca61d94411e730eca84210,
      0x2109876543110821c3b2ca88661d9500d2126eca9043721987650434849bb2a140dcca61d94411e730eca842102918740653481cbb412a0ddc4d9520826830aec8724187136548029a0c2bb2194860ca61d94411e730eca84210,
      0x398210576484c2bb2190866491960c41eb30aec8624189246583017acc2bb219086042151d8ca62730eca84210893765421084082a3b194c4e61d950806f126eca804373987654021bc49bb2a100dc42151d8ca62730eca84210,
      0x3291087654181c90c3b2a38c98415225e6530ca86e0353261054987994c32a1838d442151d8ca62730eca84210398215076484c2bb1a1086649194e041eb30aec6824189246538017acc2bb1a1086042151d8ca62730eca84210,
      0x2981704653481bcb142a0ddc58d610826830eac6924187163584029a0c3ab1a14860ca25d94411e730eca84210398271065479c3cb10aa04049e195240eef2d0a8640359053476218bbcb42a1810d4ca25d94411e730eca84210,
      0x2190876543110a01c3b2ca88625d9500d212e6ca904372189765043484b9b2a140dcca25d94411e730eca842102981740653481bcb412a0ddc58d520826830eac8724187163548029a0c3ab2194860ca25d94411e730eca84210,
      0x2987104653481bb4942a0ddc594e10826830eca6924187165384029a0c3b29a14860ca1e594411e730eca84210398721065479c3b490aa04049da15240eef2cb08640359054376218bbcb2c21810d4ca1e594411e730eca84210,
      0x2198076543110a1843b2ca8861e59500d212ec6a904372187965043484bb1aa140dcca1e594411e730eca842102987140653481bb4c12a0ddc594d20826830eca8724187165348029a0c3b2a194860ca1e594411e730eca84210,
      0x8976502431301c3b14aa0a00a1d8d6451026ca8530e140287635194409b2a14bc050ca61d944106730eca84210038762154941cc3b10aa00c0a1d90e455270ca820f253028764319549c32a084b94cca61d944106730eca84210,
      0x90876543210c4bb290a18188661d9500c4530ec86a2092198765043114c3b218a824ca61d944106730eca842108976520431301c3b492a0a00a1d94e451026ca9250e140287653194409b2a493c050ca61d944106730eca84210,
      0x9487653210240b2a38194cd0e1d964805c46ca930e2144387659021711b2a4c0b852461d950c81e330ec8a640f93876542101acc3b219082e4e1d9508406b30ec86420b93876542101acc3b219082e4e1d9508406b30ec86420b,
      0x39210876541cac3b2188132561d90c48192b0ec86042b958764321064ac3b21900ae561d90c8416730eca842039487635210240b2a03994cd0e1da54805c46ca912e2144387695021711b2a448b852461d914c81e330eca8640f,
      0x392180765419b0829243cce4a1d5904c2530eca682417928756431094c3b29a1085e461d590c822330ec8a640f9487365210240aa03b194c50e1e594805d12ec6a804374387965021744bb1aa100de461d194c81e330eca86411,
      0x291087654314b43aa1881365a1d50c481a1086ecb2429968754321068421bb2948a4210dd948652730eca84203392187065419b082a143cce4a1d5184c2530eca862417928754631094c3b2a19085e461d518c822330eca8640f,
      0x392810765419b0a81243cce4a15d904c2530eac682417928576431094c3ab1a1085e4615d90c822330ec8a640f9483765210240a823b194c50e25d94805d12e6ca804374389765021744b9b2a100de4611d94c81e330eca86411,
      0x291807654314b42ba1881365a15d0c481a108e6cb24299685743210684239b2948a4211cd948652730eca84203392817065419b0a82143cce4a15d184c2530eac862417928574631094c3ab219085e4615d18c822330eca8640f,
      0x29187065431144bb0aa1824a05500de598f30ca684034281540397663cc329a010d246195d0c826330ec8a640f392871065419c4bb10aa0424a151d84c24f30ca864035928547631093cc32a1810d646151d8c822330eca86411,
      0x98076543210c3cb2a19081a1e5950c804c106eca9242887965430213041bb2a148a020dd9508650730eca8420329187605431144bb28a1824a0550c1e598f30ca864034281543097663cc32a1810d2461951cc826330eca8640f,
      0x398210765419b2881243cce4961d904c2530aec682417925876431094c2bb1a1085e4561d90c822330ec8a640f943876521024082a3b194c50e61d94805d126eca8043743987650217449bb2a100de4521d94c81e330eca86411,
      0x298107654314b2c3a1881365961d0c481a10e86cb242996587432106843a1b2948a421d0d948652730eca84203398217065419b2882143cce4961d184c2530aec862417925874631094c2bb219085e4561d18c822330eca8640f,
      0x29817065431143cb0aa1824a14500de598f2d0a684034285140397663cb429a010d245a15d0c826330ec8a640f398271065419c3cb10aa04249611d84c24f2d0a864035925847631093cb42a1810d645611d8c822330eca86411,
      0x98706543210c3b4aa19081a1da550c804c10e6ca92428876954302130439b2a148a021cd9508650730eca8420329817605431143cb28a1824a1450c1e598f2d0a864034285143097663cb42a1810d245a151cc826330eca8640f,
      0x29871065431143b48aa1824a15040de598f2cb0684034285410397663cb2c1a010d245961d0c826330ec8a640f398721065419c3b490aa04249521d84c24f2cb0864035925487631093cb2c21810d645521d8c822330eca86411,
      0x98760543210c3b2ca19081a1d9650c804c10ec6a9242887659430213043b1aa148a021d8d508650730eca8420329871605431143b4a8a1824a1504c1e598f2cb0864034285413097663cb2c21810d2459611cc826330eca8640f,
      0x9876504321094c3b0aa180a09d965040cc490ed2a6029827659401331243b4a818a4261d8d48510330ec8a640f298761054311cc3b10aa00e459521c08da70ca820f253916548720369c32a084b94c261d90c8552330eca86411,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a180a09d952440cc490ecb26029827654901331243b2c818a4261d94c8510330eca8640f],
    ![
      0x84765930217423b2c9810ba11d964c085d08ecb26042e87654109329c3b2a084994e1d950424ca70eca82126538976543210544bb2a19082a25d950c841512eca86420a8976543210544bb2a19082a25d950c841512eca86420a,
      0x987654321024c3b2a19081261d950c840930eca86420487654109329c3b2a084994e1d950424ca70eca821265384765390217423b29c810ba11d94e4085d08eca72042e87654109329c3b2a084994e1d950424ca70eca8212653,
      0x302159847684c32a193885a61950c9c06d12ec8a604393210654987994b2c21838d4a59610c05ea730eca8421189763542108c4b292180bd6259490c1c6ac6204a930f33210654987994b2c21838d4a59610c05ea730eca84211,
      0x321098765418190cc3b2a380c8661d915c064330eca903210654987994b2c21838d4a59610c05ea730eca84211302158947684c32a11b885a619508dc06d12ec86a04393210654987994b2c21838d4a59610c05ea730eca84211,
      0x302519847684c322993885a61914c9c06d12e8ca604393216054987994b42a1838d4a5a150c05ea730eca8421189736542108c4b12a180bd6258950c1c6ac6240a930f33216054987994b42a1838d4a5a150c05ea730eca84211,
      0x3219087654181948c3b2a380ca461d915c065230eca903216054987994b42a1838d4a5a150c05ea730eca84211302518947684c32291b885a619148dc06d12e8c6a04393216054987994b42a1838d4a5a150c05ea730eca84211,
      0x29187056435849328a41bd424994521cea8604330aed921987650434849bb2a140dc24dd950862e730eca8421139287106548bc23290c9859e11948640ed07242ec0a9021987650434849bb2a140dc24dd950862e730eca84211,
      0x2109876543110821c3b2ca88410e1da55526420ca90f321987650434849bb2a140dc24dd950862e730eca842112918750643584932a0c1bd424995061cea8604312aed921987650434849bb2a140dc24dd950862e730eca84211,
      0x305219847684c232993885a61194c9c06d128eca604393261054987994c32a1838d4a61950c05ea730eca8421189376542108c4932a180bd6249950c1c6ac6420a930f33261054987994c32a1838d4a61950c05ea730eca84211,
      0x3291087654181c90c3b2a380e4861d915c072430eca903261054987994c32a1838d4a61950c05ea730eca84211305218947684c23291b885a611948dc06d128ec6a04393261054987994c32a1838d4a61950c05ea730eca84211,
      0x2981705643584b128a41bd425894521cea8640330aed92189765043484b9b2a140dc25cd950862e730eca8421139827106548bc32290c9859e19148640ed06522ec0a902189765043484b9b2a140dc25cd950862e730eca84211,
      0x2190876543110a01c3b2ca88500e1da55526240ca90f32189765043484b9b2a140dc25cd950862e730eca842112981750643584b12a0c1bd425895061cea8640312aed92189765043484b9b2a140dc25cd950862e730eca84211,
      0x2987105643584b290a41bd425948521cea8642130aed92187965043484bb1aa140dc25d8d50862e730eca8421139872106548bc32a10c9859e19508640ed06432ec0a902187965043484bb1aa140dc25d8d50862e730eca84211,
      0x2198076543110a1843b2ca8850c21da55526204ca90f32187965043484bb1aa140dc25d8d50862e730eca842112987150643584b2920c1bd425949061cea8642112aed92187965043484bb1aa140dc25d8d50862e730eca84211,
      0x8976503421394c3b0a29828a61d85140d4090ec72a42e2198765043114c3b2a0982ca61d95040d6730eca84211298761054350243b192c8b8121d8c9465c930ec64a2042198765043114c3b2a0982ca61d95040d6730eca84211,
      0x90876543210c4bb2992081e25d94c9004e530ec86a20a2198765043114c3b2a0982ca61d95040d6730eca842118976530421394c3b20a9828a61d90540d4090ed26a42e2198765043114c3b2a0982ca61d95040d6730eca84211,
      0x9487653210240b2a38194ce05951c0e4a630ca80f26534387659021711b2a4c0b850c9952245c28690ed2a042e93876542101acc3b219082d661d90c8056b30ec86420c93876542101acc3b219082d661d90c8056b30ec86420c,
      0x39210876541cac3b2188132561d90c48192b0ec86042b958764321064ac3b21900ae561d90c8416730eca842039487635210240b2a03994ce059501ce4a630ca8e126534387695021711b2a448b850c9952605c28690ecb2042e,
      0x392180765419b0829243cccd84149225e630a8e0d2651928756431094c3b29a1085e61d94d0806e690ed2a042e9487365210240aa03b194c605501d8e4a2c6204a930f34387965021744bb1aa100de25d8d50842e530eca86212,
      0x291087654314b43aa1881365a1d50c481a1086ecb2429968754321068421bb2948a4210dd948652730eca84203392187065419b082a143cccd84150a25e630a8ec12651928754631094c3b2a19085e61d950c806e690ecb2042e,
      0x392810765419b0a81243cccd85409225e630ae80d2651928576431094c3ab1a1085e61d58d0806e690ed2a042e9483765210240a823b194c605411d8e4a2c6240a930f34389765021744b9b2a100de25cd950842e530eca86212,
      0x291807654314b42ba1881365a15d0c481a108e6cb24299685743210684239b2948a4211cd948652730eca84203392817065419b0a82143cccd85410a25e630ae8c12651928574631094c3ab219085e61d590c806e690ecb2042e,
      0x29187065431144bb0aa1824a25d85500d2712ec4a820f281540397663cc329a010d1e6194d004a8690ed2a042e392871065419c4bb10aa040e25d885412107242ec0a90928547631093cc32a1810d65e10d94086a530eca86212,
      0x98076543210c3cb2a19081a1e5950c804c106eca9242887965430213041bb2a148a020dd9508650730eca8420329187605431144bb28a1824a25d94500d2712eca4820f281543097663cc32a1810d1e61950c04a8690ecb2042e,
      0x398210765419b2881243cccd94409225e630ea80d2651925876431094c2bb1a1085e615d8d0806e690ed2a042e943876521024082a3b194c604151d8e4a2c6420a930f343987650217449bb2a100de24dd950842e530eca86212,
      0x298107654314b2c3a1881365961d0c481a10e86cb242996587432106843a1b2948a421d0d948652730eca84203398217065419b2882143cccd94410a25e630ea8c12651925874631094c2bb219085e615d90c806e690ecb2042e,
      0x29817065431143cb0aa1824a1e585500d270f2c4a820f285140397663cb429a010d1e5a14d004a8690ed2a042e398271065419c3cb10aa040e1e5885412106522ec0a90925847631093cb42a1810d65d20d94086a530eca86212,
      0x98706543210c3b4aa19081a1da550c804c10e6ca92428876954302130439b2a148a021cd9508650730eca8420329817605431143cb28a1824a1e594500d270f2ca4820f285143097663cb42a1810d1e5a150c04a8690ecb2042e,
      0x29871065431143b48aa1824a1da45500d270ed24a820f285410397663cb2c1a010d1e5960d004a8690ed2a042e398721065419c3b490aa040e1da485412106432ec0a90925487631093cb2c21810d65d0e194086a530eca86212,
      0x98760543210c3b2ca19081a1d9650c804c10ec6a9242887659430213043b1aa148a021d8d508650730eca8420329871605431143b4a8a1824a1da54500d270ed2a4820f285413097663cb2c21810d1e59610c04a8690ecb2042e,
      0x9876504321094c3b0aa1808a61d85500c4730ec4a82038176594032291c3b4a820a08e1da540510690ed2a042e298761054311cc3b10aa00ce61d8854106930ec64a204097652184330cc3b2192828661d90c8154530eca86212,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca482038176549032291c3b2c820a08e1d9640510690ecb2042e],
    ![
      0x8976542310944bb2a11884a25d9508c42512eca84621232106549879990832a4c3ccc84195261e66420ca930f38976543210644bb2a19083225d950c841912eca86420c8976543210644bb2a19083225d950c841912eca86420c,
      0x302198746571810cc3a32b8c08661d195c604330e8cae32106549879990832a4c3ccc84195261e66420ca930f38976524310944bb2921884a25d9490c42512eca48621232106549879990832a4c3ccc84195261e66420ca930f3,
      0x302189746571810c4ba32b8c08625d195c604312e8cae32106549879990832a4c3ccc84195261e66420ca930f38976254310944bb12a1884a25d8950c42512ec4a8621232106549879990832a4c3ccc84195261e66420ca930f3,
      0x3210987654199084c3b2a0cc84261d9506642130eca8332106549879990832a4c3ccc84195261e66420ca930f3302187946571810c3ca32b8c0861e5195c60430f28cae32106549879990832a4c3ccc84195261e66420ca930f3,
      0x39281067549c810b2a39c564085951e0ea6124ed02a97219876504348b9c32a049505ce19500a68730eca8421389736542109c398b2a014d21cc595024a90522eca0869219876504348b9c32a049505ce19500a68730eca84213,
      0x201498736548389932c24d01c4c996252924026a90ed7219876504348b9c32a049505ce19500a68730eca8421339281607549c810b22b9c564085915e0ea6124f0c2a97219876504348b9c32a049505ce19500a68730eca84213,
      0x201489736548389b12c24d01c4d89625292402a690ed7219876504348b9c32a049505ce19500a68730eca8421339286107549c810a32b9c564085195e0ea61250ec2a97219876504348b9c32a049505ce19500a68730eca84213,
      0x21098765431010cc3b2a1a008661d94d1004330eca869219876504348b9c32a049505ce19500a68730eca84213201487936548389b29424d01c4d94a25292402a870ed7219876504348b9c32a049505ce19500a68730eca84213,
      0x39821067549c80932a39c564049951e0ea6052ed02a97218976504348bc1b2a049505e0d9500a68730eca8421389376542109c389b2a014d21c4d95024a90432eca0869218976504348bc1b2a049505e0d9500a68730eca84213,
      0x204198736548398932c24d01cc4996252924206a90ed7218976504348bc1b2a049505e0d9500a68730eca8421339821607549c809322b9c564049915e0ea6052f0c2a97218976504348bc1b2a049505e0d9500a68730eca84213,
      0x204189736548398b12c24d01cc589625292420a690ed7218976504348bc1b2a049505e0d9500a68730eca8421339826107549c809232b9c564049195e0ea60530ec2a97218976504348bc1b2a049505e0d9500a68730eca84213,
      0x219087654310148c3b2a1a00a461d94d1005230eca869218976504348bc1b2a049505e0d9500a68730eca84213204187936548398b29424d01cc594a25292420a870ed7218976504348bc1b2a049505e0d9500a68730eca84213,
      0x298710564364990c3a8234a4c861d4192480650f22cae219876504311021c3b0aca4810e1d86552730eca8421393218760549201943b0cab900ca1d8565d26430ec0a83219876504311021c3b0aca4810e1d86552730eca84213,
      0x8032976154394c38aa31830a61c55180d926430a80ed2219876504311021c3b0aca4810e1d86552730eca84213298715064364990c2b8234a4c8615c1924806512e2cae219876504311021c3b0aca4810e1d86552730eca84213,
      0x8032796154394c3a8a31830a61d45180d92642b080ed2219876504311021c3b0aca4810e1d86552730eca84213298751064364990ac38234a4c8561c1924806530e2cae219876504311021c3b0aca4810e1d86552730eca84213,
      0x90876543210c0193b28a49e00c9d94650e530ea86c20c219876504311021c3b0aca4810e1d86552730eca842138032769154394c3aa0b1830a61d50580d92642a900ed2219876504311021c3b0aca4810e1d86552730eca84213,
      0x9487653210240aa3b0194c60551d80e4a2c620a8530f34387659021744bb2a1900de25d950c842e530ea8c621293876542101c021bb290ca6010dd94a452d30ea86420d93876542101c021bb290ca6010dd94a452d30ea86420d,
      0x392108765419b0812a43cccd84095225e630a80ed2651928765431094c3b1aa1085e61d8d50806e690f2ca042e9487635210240aa383194c60551c18e4a2c620a4930f34387695021744bb29a100de25d94d0842e530eac86212,
      0x392180765419b0829243cccd84149225e630a8e0d2651928756431094c3b29a1085e61d94d0806e690ed2a042e9487365210240aa03b194c605501d8e4a2c6204a930f34387965021744bb1aa100de25d8d50842e530eca86212,
      0x291087654314b43aa1881365a1d50c481a1086ecb2429968754321068421bb2948a4210dd948652730eca84203392187065419b082a143cccd84150a25e630a8ec12651928754631094c3b2a19085e61d950c806e690ecb2042e,
      0x392810765419c4b90b2a040e25c85941210724ec20a90928576431093cc321a810d65e1194c086a530ea8c62129483765210241c93b28823e0e49d94501f0522eca0869438976502174bc1b2a009525e0d95008690420a872ecc,
      0x29180765431144b8b2a1824a25c59500d2712e4ca820f281504397663cc31aa010d1e618d5004a8690f2ca042e392817065419c4b930aa040e25c98541210724e2c0a90928574631093cc3229810d65e118d4086a530eac86212,
      0x29187065431144bb0aa1824a25d85500d2712ec4a820f281540397663cc329a010d1e6194d004a8690ed2a042e392871065419c4bb10aa040e25d885412107242ec0a90928547631093cc32a1810d65e10d94086a530eca86212,
      0x98076543210c3cb2a19081a1e5950c804c106eca9242887965430213041bb2a148a020dd9508650730eca8420329187605431144bb28a1824a25d94500d2712eca4820f281543097663cc32a1810d1e61950c04a8690ecb2042e,
      0x398210765419c3c90b2a040e1e485941210652ec20a90925876431093cb421a810d65d2194c086a530ea8c6212943876521024194bb28823e0ca5d94501f0432eca0869439876502174b9c32a009525ce195008690420a872ecc,
      0x29810765431143c8b2a1824a1e459500d270f24ca820f285104397663cb41aa010d1e5a0d5004a8690f2ca042e398217065419c3c930aa040e1e498541210652e2c0a90925874631093cb4229810d65d218d4086a530eac86212,
      0x29817065431143cb0aa1824a1e585500d270f2c4a820f285140397663cb429a010d1e5a14d004a8690ed2a042e398271065419c3cb10aa040e1e5885412106522ec0a90925847631093cb42a1810d65d20d94086a530eca86212,
      0x98706543210c3b4aa19081a1da550c804c10e6ca92428876954302130439b2a148a021cd9508650730eca8420329817605431143cb28a1824a1e594500d270f2ca4820f285143097663cb42a1810d1e5a150c04a8690ecb2042e,
      0x298710654311cc390b2a00ce61c8594106930e64ca204097621584330cc3a1b12828661d0d88154530ea8c621239872106541a4c3990b281250ca1d8540926430ec0a83097632185438cc3aa193030661d50c81990420a872ecc,
      0x9876054321094c38b2a1808a61c59500c4730e4ca82038176954032291c3cb2820a08e1e5940510690f2ca042e298716054311cc3930aa00ce61c9854106930e6c4a204097625184330cc3a3192828661d18c8154530eac86212,
      0x9876504321094c3b0aa1808a61d85500c4730ec4a82038176594032291c3b4a820a08e1da540510690ed2a042e298761054311cc3b10aa00ce61d8854106930ec64a204097652184330cc3b2192828661d90c8154530eca86212,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca482038176549032291c3b2c820a08e1d9640510690ecb2042e],
    ![
      0x8976543210744bb2a19083a25d950c841d12eca86420e8976543210744bb2a19083a25d950c841d12eca86420e8976543210744bb2a19083a25d950c841d12eca86420e8976543210744bb2a19083a25d950c841d12eca86420e,
      0x987654321024c3b2a190811521da4c8060a90ed264030548769302182a43b49810c1521da4c40a2a90ed262051548769032182a43b48190c1521da44c0a2a90ed22605154876910328aa43b4881945521da4840e4a90ed242072,
      0x392180765471a882143b4c61194e485c2c1042a6ed2998465392710b0410a9bcb26615d924c843286cb30042f68465397210b0410a9cbb26615d9248c43286cb30402f68576492130ca1b2cc1083d95040ca1da63126420eca8e,
      0x321098765418190cc3b2a38c841521e5a292ed0a4207932105489768a4bb429009e661d9504c8350a42608ed3932105498768a4bb428109e661d950c48350a4260e8d399876543210d4290983b24e55040ca1da63126420eca8e,
      0x392810765471a8a0143b4c6118d6485c2c104a26ed2998463592710b041289bcb26615d1a4c843286d2b0042f68463597210b041289cbb26615d1a48c43286d2b0402f68574692130ca1b4ac1083d9504c0a1da63126420eca8e,
      0x3219087654181948c3b2a38c854121e5a292f0ca4207932150489768a4bc329009e661d5904c8350a46208ed3932150498768a4bc328109e661d590c48350a4620e8d399875643210d4291883b24e5504c0a1da63126420eca8e,
      0x29187065434144bb0aa182c0499650de2a112ca486e350126594738a844b292398d524084e1d972112ec8a42790126597438a844b293a18d524084de1972112ec84a2794902137685c844bb210a9e5500c861da61126420eca8e,
      0x2109876543110821c3b2ca88661d9500d6052cb0862f521987650435814b2c209bd4ca61d944122e90cb26421621987605435814b2c0a1bd4ca61d854122e90cb24621632987610548ba432c909859500c861da61126420eca8e,
      0x398210765471aa08143b4c610d96485c2c10a426ed2998436592710b042909bcb266151da4c8432872cb0042f68436597210b042909cbb266151da48c432872cb0402f68547692130ca1cb2c1083d950c40a1da63126420eca8e,
      0x3291087654181c90c3b2a38c944121e5a2930eca4207932510489768a4c3b29009e6615d904c8350a64208ed3932510498768a4c3b28109e6615d90c48350a6420e8d399857643210d4299083b24e550c40a1da63126420eca8e,
      0x29817065434143cb0aa182c0589650de2a10d2a486e350162594738a8434a92398d524804e1d97210f2c8a42790162597438a8434a93a18d524804de197210f2c84a2794920137685c843cb210a9e550c0861da61126420eca8e,
      0x2190876543110a01c3b2ca88625d9500d604d2b0862f5218976504358134ac209bd4ca25d944122e8d0b264216218976054358134ac0a1bd4ca25d854122e8d0b24621632897610548ba342c90985950c0861da61126420eca8e,
      0x29871065434143b48aa182c0594a50de2a10cb2486e350165294738a8432c92398d524840e1d97210ed28a42790165297438a8432c93a18d524840de197210ed284a2794921037685c843b4a10a9e550c8061da61126420eca8e,
      0x2198076543110a1843b2ca8861e59500d604cb30862f5218796504358132cc209bd4ca1e5944122e8cb1264216218796054358132cc0a1bd4ca1e5854122e8cb124621632879610548ba32c490985950c8061da61126420eca8e,
      0x8976504321294c3b0aa1808861da50c1544b0ed28602b2187694035512c3b4a018ac0e1d924855c6b0ed2820512187690435512c3b48218ac0e1d90a455c6b0ed228051038764219571ac3b4882146610c85d9409126420eca8e,
      0x90876543210c4bb28a190148661d9500c4530ec6a82082198765043114c3b1a8a020ca61d944106730ec8a420e2198760543114c3b18aa020ca61d854106730ec84a20e329876105419cc3b210a83a610c85d9409126420eca8e,
      0x948765321022cc3b2190842521d94c8408b30ec864210948765321022cc3b2190842521d94c8408b30ec864210948765321022cc3b2190842521d94c8408b30ec864210948765321022cc3b2190842521d94c8408b30ec864210,
      0x39210876541cac3b21081ca561d9084c252b0ec820651958764231094ac3b2098146561d904c8232b0ec806430958764321094ac3b2188146561d90c48232b0ec86043095876432108cac3b21900c2561d90c8420930eca64204,
      0x392180765419a882143b4c420ca45d915c1042a6ed299083291746570410a9bcb26420ca45d51a086cb30042f6083291476570410a9cbb26420ca455d1a086cb30402f60832915476821b2cc1083da54c8061d920b264210ec90,
      0x29108765431128821c3b4b094410e1e5992d0ea820653251043897664b43aa09814e5a1d504c82610a8ed26430251043987664b43aa18814e5a1d50c482610a8ec7243096875432109842a3b1948c02151d8c8660930eca64204,
      0x392810765419a8a0143b4c420e485d915c104a26ed29908392174657041289bcb26420e485d51a086d2b0042f608392147657041289cbb26420e4855d1a086d2b0402f60839215476821b4ac1083da54c0861d920b264210ec90,
      0x29180765431128a01c3b4b094500e1e5992d0ae820653251403897664b42ba09814e5a15d04c82610ae8d26430251403987664b42ba18814e5a15d0c482610ae8c7243096857432109842ba31948c0215d18c8660930eca64204,
      0x29187065431144bb0aa182ca050c1da554112ca486e3528143079655044b292398d658c40961d26112ec8a427928143097655044b293a18d658c40a15d26112ec84a27996310287549844bb210a9e654c40a1d922b264210ec90,
      0x98076543210c3cb2a19081e1e5950c804e512eca8620a87965430213944bb2a09828a25d95040d4108ecb2642e87965403213944bb28a1828a25d94500d4108eca7242e289765104350423b29948b8211d94c865c930eca64204,
      0x398210765419aa08143b4c4224c85d915c10a426ed29908932174657042909bcb264224c85d51a0872cb0042f608932147657042909cbb264224c855d1a0872cb0402f60893215476821cb2c1083da540c861d920b264210ec90,
      0x2981076543112a081c3b4b095040e1e5992cb0e820653254103897664b2c3a09814e5961d04c82610ea8d26430254103987664b2c3a18814e5961d0c482610ea8c7243096587432109843aa31948c021d518c8660930eca64204,
      0x29817065431143cb0aa182ca104c1da55410d2a486e35284130796550434a92398d6584c0961d2610f2c8a4279284130976550434a93a18d6584c0a15d2610f2c84a27996130287549843cb210a9e6544c0a1d922b264210ec90,
      0x98706543210c3b4aa19081e1da550c804e50f2ca8620a87695430213943cb2a09828a1e595040d410e8cb2642e87695403213943cb28a1828a1e594500d410e8ca7242e28796510435043a329948b821d194c865c930eca64204,
      0x29871065431143b48aa182ca10c41da55410cb2486e35284310796550432c92398d65840c961d2610ed28a4279284310976550432c93a18d65840ca15d2610ed284a27996103287549843b4a10a9e65440ca1d922b264210ec90,
      0x98760543210c3b2ca19081e1d9650c804e50ed2a8620a87659430213943b4aa09828a1da55040d410ec8b2642e87659403213943b4a8a1828a1da54500d410ec8a7242e28769510435043b229948b821d914c865c930eca64204,
      0x9876504321094c3b0aa180a0dd9648410e4b0ed28602b8376592014392c3b4a018ac921da4c41546b0ed2820518376590214392c3b48218ac921da44c1546b0ed228051248769103551ac3b4882144261d90c855cb264210ec90,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca48203298765104311cc3b290a00ce61d9484106930eca64204],
    ![
      0x89765432107c4bb2a19083e25d950c841f12eca86420f89765432107c4bb2a19083e25d950c841f12eca86420f89765432107c4bb2a19083e25d950c841f12eca86420f89765432107c4bb2a19083e25d950c841f12eca86420f,
      0x987654321024c3b2a19081261d950c840930eca864204548769302182a43b49810c1521da4c0860a90ed260430548769032182a43b48190c1521da40c860a90ed20643054876910328aa43b4881945521da440ca2a90ed220651,
      0x392180765484c3b2a10986661d950840f26f30c4a821a3021859476cac3b4a19086e61d9508c43700426a92ed93021854976cac3b4a11886e61d950c843700426b28ed99876543210d4290983b24e61484c1da533126420eca90,
      0x321098765418190cc3b2a380c8661d915c064330eca9032105489768a4bb429009e525da1480c7290cb260e43632105498768a4bb428109e525da1408c7290cb26e04369876543210d4290983b24e61484c1da533126420eca90,
      0x392810765484c3ab210986661d590840f2b2f0c86421a3028159476cac3cb219086e61d5908c43700462a92ed93028154976cac3cb211886e61d590c843700462b28ed99875643210d4291883b24e6148c41da533126420eca90,
      0x3219087654181948c3b2a380ca461d915c065230eca9032150489768a4bc329009e525e19480c7290d2a60e43632150498768a4bc328109e525e19408c7290d2a6e04369875643210d4291883b24e6148c41da533126420eca90,
      0x2918706543481cbb12a40dc0e5d895062e712ec4a82110297638154bcc3b2a1180f261d9508c438f30ca8604360297631854bcc3b2a1900f261d950c8438f30ca80643632987610548ba432c909859d21964840ed126420eca90,
      0x2109876543110821c3b2ca88410e1da55526420ca90f321987650435814b2c209bd40a596105cea092ed0a643921987605435814b2c0a1bd40a596051cea092ed06a43932987610548ba432c909859d21964840ed126420eca90,
      0x398210765484c2bb2109866615d90840f2b30ec86421a3082159476cac4bb219086e615d908c43700642a92ed93082154976cac4bb211886e615d90c843700642b28ed99857643210d4299083b24e614c841da533126420eca90,
      0x3291087654181c90c3b2a380e4861d915c072430eca9032510489768a4c3b29009e5261d9480c72912ca60e43632510498768a4c3b28109e5261d9408c72912ca6e04369857643210d4299083b24e614c841da533126420eca90,
      0x2981706543481bcb12a40dc0de5895062e70f2c4a82110279638154bcc33aa1180f2619d508c438f2d0a8604360279631854bcc33aa1900f2619d50c8438f2d0a80643632897610548ba342c909859d1a164840ed126420eca90,
      0x2190876543110a01c3b2ca88500e1da55526240ca90f3218976504358134ac209bd409a56105cea08f2d0a6439218976054358134ac0a1bd409a56051cea08f2d06a43932897610548ba342c909859d1a164840ed126420eca90,
      0x2987106543481bb492a40dc0dda495062e70ed24a82110276938154bcc32ba1180f26195d08c438f2cb08604360276931854bcc32ba1900f26195d0c8438f2cb080643632879610548ba32c4909859d19624840ed126420eca90,
      0x2198076543110a1843b2ca8850c21da55526204ca90f3218796504358132cc209bd409966105cea08ed30a6439218796054358132cc0a1bd409966051cea08ed306a43932879610548ba32c4909859d19624840ed126420eca90,
      0x8976504321301c3b12a48a00e1d8950650730ec4a82030287639154409b2a143c8504d950a1c2686b0ed2804300287631954409b2a13c48504d9509e02686b0ed208430329876105419cc3b290a040e61d9484121126420eca90,
      0x90876543210c4bb2921881a25d9490c04c070ed2a84282198765043114c3b2289824a61d91440d2730ec8a420f2198760543114c3b20a9824a61d90540d2730ec84a20f329876105419cc3b290a040e61d9484121126420eca90,
      0x948765321022cc3b2190841661d90c8060b30ec864211948765321022cc3b2190841661d90c8060b30ec864211948765321022cc3b2190841661d90c8060b30ec864211948765321022cc3b2190841661d90c8060b30ec864211,
      0x39210876541cac3b21081ca561d9084c252b0ec820651958764231094ac3b2098146561d904c8232b0ec806430958764321094ac3b2188146561d90c48232b0ec86043095876432108cac3b21900c2561d90c8420930eca64204,
      0x392180765419a882143b4c4d4410a1e5a26f30c4a821a083291746570410a9bcb26420854de51b300426a92ed9083291476570410a9cbb26420854e5d1b300426b28ed90832915476821b2cc1083d90d966085c2d006432a8ed0,
      0x29108765431128821c3b4b094410e1e5992d0ea820653251043897664b43aa09814e5a1d504c82610a8ed26430251043987664b43aa18814e5a1d50c482610a8ec7243096875432109842a3b1948c02151d8c8660930eca64204,
      0x392810765419a8a0143b4c4d4500a1e5a2b2f0c86421a08392174657041289bcb26420944de51b300462a92ed908392147657041289cbb26420944e5d1b300462b28ed90839215476821b4ac1083d90da56085c2d006432a8ed0,
      0x29180765431128a01c3b4b094500e1e5992d0ae820653251403897664b42ba09814e5a15d04c82610ae8d26430251403987664b42ba18814e5a15d0c482610ae8c7243096857432109842ba31948c0215d18c8660930eca64204,
      0x29187065431144bb0aa182ca25d85500d6712ec4a821128143079655044b292398d42259491c4eaf30ca86043628143097655044b293a18d4225949d04eaf30ca80643696310287549844bb210a9e4225d9084d73006432a8ed0,
      0x98076543210c3cb2a19081e1e5950c804e512eca8620a87965430213944bb2a09828a25d95040d4108ecb2642e87965403213944bb28a1828a25d94500d4108eca7242e289765104350423b29948b8211d94c865c930eca64204,
      0x398210765419aa08143b4c4d5040a1e5a2b30ec86421a08932174657042909bcb26421484de51b300642a92ed908932147657042909cbb26421484e5d1b300642b28ed90893215476821cb2c1083d90e596085c2d006432a8ed0,
      0x2981076543112a081c3b4b095040e1e5992cb0e820653254103897664b2c3a09814e5961d04c82610ea8d26430254103987664b2c3a18814e5961d0c482610ea8c7243096587432109843aa31948c021d518c8660930eca64204,
      0x29817065431143cb0aa182ca1e585500d670f2c4a8211284130796550434a92398d421a5491c4eaf2d0a860436284130976550434a93a18d421a549d04eaf2d0a80643696130287549843cb210a9e421e59084d73006432a8ed0,
      0x98706543210c3b4aa19081e1da550c804e50f2ca8620a87695430213943cb2a09828a1e595040d410e8cb2642e87695403213943cb28a1828a1e594500d410e8ca7242e28796510435043a329948b821d194c865c930eca64204,
      0x29871065431143b48aa182ca1da45500d670ed24a8211284310796550432c92398d42196491c4eaf2cb0860436284310976550432c93a18d4219649d04eaf2cb080643696103287549843b4a10a9e421da5084d73006432a8ed0,
      0x98760543210c3b2ca19081e1d9650c804e50ed2a8620a87659430213943b4aa09828a1da55040d410ec8b2642e87659403213943b4a8a1828a1da54500d410ec8a7242e28769510435043b229948b821d914c865c930eca64204,
      0x9876504321094c3b0aa1808a61d85500c4730ec4a8203827659104331243b49828a4921da4c05526b0ed280430827659014331243b481a8a4921da40c5526b0ed208430098763215440cc3b219283c661d90c815f006432a8ed0,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca48203298765104311cc3b290a00ce61d9484106930eca64204],
    ![
      0x89765432108c4bb2a19084625d950c842312eca86421189765432108c4bb2a19084625d950c842312eca86421189765432108c4bb2a19084625d950c842312eca86421189765432108c4bb2a19084625d950c842312eca864211,
      0x302198547681810cc2a3b40c0866151da0604330a8ed09476853021cca3b429810e651da14c087328ed0a604399476850321cca3b428190e651da140c87328ed0a064399876543210d4c3b2a19086a61d950c843530eca86421a,
      0x302189547681810c4aa3b40c0862551da0604312a8ed03021859476c9810c2ca3b64c0861651db260430b28ed93021854976c9810c2a4bb64c0861525db260430a92ed99876543210d4c3b2a19086a61d950c843530eca86421a,
      0x3210987654199084c3b2a0cc84261d9506642130eca833210548976899082a44bb44c8415225da26420a912ed13210549876899082a4c3b44c8415261da26420a930ed19876543210d4c3b2a19086a61d950c843530eca86421a,
      0x392810765489a0490bb42e6410dd8861730724ec20a912098657143aa4bc3298907125e194c40b90124ca2e8752098651743ac4ba3298817225d194c48390124cae2875329876105489824bb10c2e6500c85da173126420eca91,
      0x2918057643594818abb245ca40c55da12e2412f0ca8750297368154bcc3b2a1180f661d9508c43b1262408ecbc0297361854bcc3b2a1900f661d950c843b126240e8cbc329876105489824bb10c2e6500c85da173126420eca91,
      0x291850764359481a8bb245ca40d45da12e24130eca8750297638154bcc3b229180f661d9148c43b1262048ecbc0297631854bcc3b229900f661d914c843b126204e8cbc329876105489824bb10c2e6500c85da173126420eca91,
      0x21098765431010cc3b2a1a008661d94d1004330eca869219876504359049bb28a45c824dd94612e2052cb0e875219876054359049bb0aa45c824dd85612e2052caf0875329876105489824bb10c2e6500c85da173126420eca91,
      0x398210765489a4810bb42e640d1d8861730652ec20a912089657143aa4c3b2989071261d94c40b90052ca2e8752089651743ac4a3b2988172251d94c48390052cae287532897610548984a3b10c2e650c085da173126420eca91,
      0x2981057643594980abb245ca4c055da12e2520f0ca8750279368154bcc33aa1180f6619d508c43b1226408ecbc0279361854bcc33aa1900f6619d50c843b122640e8cbc32897610548984a3b10c2e650c085da173126420eca91,
      0x29815076435949828bb245ca4c145da12e25210eca8750279638154bcc33a29180f6619d148c43b1226048ecbc0279631854bcc33a29900f6619d14c843b122604e8cbc32897610548984a3b10c2e650c085da173126420eca91,
      0x219087654310148c3b2a1a00a461d94d1005230eca86921897650435901cbb28a45c80e5d94612e2124cb0e87521897605435901cbb0aa45c80e5d85612e2124caf087532897610548984a3b10c2e650c085da173126420eca91,
      0x2987106543502439932c8b8121cc99465c930e64ca204028743916548932a1c843d449950e41e2b0620a852ed1028743196548932a184c3d449950c25e2b0620a924ed132987610541982a4390b4c0c1521c865a1126420eca91,
      0x8976035421394c38a329828a61c51940d4090e72ca42e0287369154414bb429820dca5da14c052f20430a68ed90287361954414bb4281a0dca5da140c52f20430a86ed932987610541982a4390b4c0c1521c865a1126420eca91,
      0x8976305421394c3a0b29828a61d05940d4090f26ca42e0287639154414bb2c1820dca5d960c052e68ed0b204390287631954414bb2c01a0dca5d9600c52e68ed0a1243932987610541982a4390b4c0c1521c865a1126420eca91,
      0x90876543210c4bb192a081e25d8c95004e530e86ca20a2198765043114c3aa30982ca61d51840d6730ea8c42112198760543114c3aa0b182ca61d50580d6730ea84c21132987610541982a4390b4c0c1521c865a1126420eca91,
      0x94876532102402a3b190cc20151d8ca460d30ea86421394876532102402a3b190cc20151d8ca460d30ea86421394876532102402a3b190cc20151d8ca460d30ea86421394876532102402a3b190cc20151d8ca460d30ea864213,
      0x392108765419a881243b4c4d440921e5a26f304ca821a0832197465704109abcb2642084d5e51b30042a692ed90832194765704109acbb2642084d65d1b30042a728ed90832195476821b2c49083d90d962485c2d006522a8ed0,
      0x392180765419a882143b4c4d4410a1e5a26f30c4a821a083291746570410a9bcb26420854de51b300426a92ed9083291476570410a9cbb26420854e5d1b300426b28ed90832915476821b2cc1083d90d966085c2d006432a8ed0,
      0x29108765431128821c3b4b094410e1e5992d0ea820653251043897664b43aa09814e5a1d504c82610a8ed26430251043987664b43aa18814e5a1d50c482610a8ec7243096875432109842a3b1948c02151d8c8660930eca64204,
      0x392810765419a8210c3b4c0d410861e5a10724ec20a91083921746574bc2329009da5e119480c6d0124ca2e875083921476574bc2328109da5e119408c6d0124cae287508392154768404a3b109ae60251d8854f2d264210ea93,
      0x29180765431144b8b2a182ca25c59500d6712e4ca821128140379655044b12a398d42258951c4eaf30c8a6043628140397655044b12ba18d4225895d04eaf30c8a0643696312087549844ba310a9e4225d1884d73006522a8ed0,
      0x29187065431144bb0aa182ca25d85500d6712ec4a821128143079655044b292398d42259491c4eaf30ca86043628143097655044b293a18d4225949d04eaf30ca80643696310287549844bb210a9e4225d9084d73006432a8ed0,
      0x98076543210c3cb2a19081e1e5950c804e512eca8620a87965430213944bb2a09828a25d95040d4108ecb2642e87965403213944bb28a1828a25d94500d4108eca7242e289765104350423b29948b8211d94c865c930eca64204,
      0x398210765419aa010c3b4c0d500861e5a10652ec20a91089321746574ba4329009da5d219480c6d0052ca2e875089321476574ba4328109da5d219408c6d0052cae2875089321547684024bb109ae60125d8854f2d264210ea93,
      0x29810765431143c8b2a182ca1e459500d670f24ca821128410379655043492a398d421a4951c4eaf2d08a6043628410397655043492ba18d421a495d04eaf2d08a0643696132087549843ca310a9e421e51884d73006522a8ed0,
      0x29817065431143cb0aa182ca1e585500d670f2c4a8211284130796550434a92398d421a5491c4eaf2d0a860436284130976550434a93a18d421a549d04eaf2d0a80643696130287549843cb210a9e421e59084d73006432a8ed0,
      0x98706543210c3b4aa19081e1da550c804e50f2ca8620a87695430213943cb2a09828a1e595040d410e8cb2642e87695403213943cb28a1828a1e594500d410e8ca7242e28796510435043a329948b821d194c865c930eca64204,
      0x298710654311cc390b2a00ce61c8594106930e64ca204916587024369c32883ca14ce19441e49270620a852ed1916587204369c32884ba14ce194425c9270620a924ed1098743216548cc3aa193044661d50c81a2d264210ea93,
      0x9876054321094c38b2a1808a61c59500c4730e4ca8203827695104331243cb1828a4921e58c05526b0f2c80430827695014331243cb01a8a4921e580c5526b0f2c08430098736215440cc3a319283c661d18c815f006522a8ed0,
      0x9876504321094c3b0aa1808a61d85500c4730ec4a8203827659104331243b49828a4921da4c05526b0ed280430827659014331243b481a8a4921da40c5526b0ed208430098763215440cc3b219283c661d90c815f006432a8ed0,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca48203298765104311cc3b290a00ce61d9484106930eca64204],
    ![
      0x584076392181a28bb4490616101d8e486068a2ed1241887936524107aa183b4c10de1e4d949041ea860ed304375341768920ba9a0bb44905d4d05da2482ea682ed124175341768920ba9a0bb44905d4d05da2482ea682ed12417,
      0x31290584768bb2ca0091c751e41a094c724b06ed2821b3204189576c882ca33941f65e0d94904365120ec8a6392810573649cb12380a9cc75ca25458d0325302eca86192810573649cb12380a9cc75ca25458d0325302eca8619,
      0x31295084768bb2c82091c751e421894c724b06ed2821b3204819576c882cb23941f65e0d58904365120ec8a6392810753649cb1238829cc75ca24558d0325302eca86192810753649cb1238829cc75ca24558d0325302eca8619,
      0x2910874635494c0bb2a18600e49da1452e4b06ed2821b7310652894a1944b2b820f05609da4c1305120ec8a639392187064579c10b283a4f0e249d8541205302eca8619392187064579c10b283a4f0e249d8541205302eca8619,
      0x987465321022a41bb49084261d194c8408a906ed2421087936524107aa183b4c10de1e4d949041ea860ed3043789716543027c4b8b2a1813e25c5950c09f12e2ca8604f6987543210a34c3aa190851a61d50c8428d30ea864214,
      0x32190876541990c02a3b4c40ca065d915c92e4d0a26193298176054810c4abb1a0665e0994500f2f040a26c9393925180746818138c2cb26661cd9508072b0e2d28605b7982615430c90c4abb1a065580d085e63af040a26c939,
      0x32198076541990c2823b4c40ca245d915c92e50ca26193298716054810c4bab1a0665e0958500f2f0402a6c939392581074681813c0acb26661cd5908072b0e32c8605b7982165430c90c4bab1a065580c905e63af0402a6c939,
      0x2109876543110cc3b2a182484210dda554430ea8c721721987650434994c3b28a03c24d5d90862e730aec8403029148706354b89b2a4148500e61d89452e30a8ec720587136548092a194c3b28a03c2515d8c8630730aec84030,
      0x384217965749a93b42085e614dd8508227302ec8a04f984376251024389aa0314c5624dd8900605120ec8a6399820764531cca293b41886061cd5018a626b04ed28210853276941084389aa0314c55249da0c4305120ec8a639,
      0x2189047365539b042ca10d2618dd4508267302ec8a04f038429716574b90428b1a640a2455cd1b25120ec8a6392879150436b89b92b424860e1c6589411e6b04ed282104723980615ccb90428b1a649e4618d41365120ec8a639,
      0x2189407365539b02c4a10d2618d5c508267302ec8a04f03849271657193a42b0c8640a2545cd1b25120ec8a6392879510436b89b932c24860e1c5a49411e6b04ed282104723890615c993a42b0c8649e45a0d41365120ec8a639,
      0x8970652413314c03b2298a40e09da545107302ec8a04f2189437065518c4aa383144a1e550c41ae5120ec8a639038276159440933aa1cc050e609d8541066b04ed282109813652704998c4aa383144624dd89015e5120ec8a639,
      0x329810765419934082a3cce6149d850c2526a2ed08417984376251024389aa0314c5624dd8900609120ca462f539852107468184390acb2666105948c1eb28a2ed06418853276941084389aa0314c55249da0c4309120ca462f5,
      0x2198076543110c24bb29824856011ce598e6c50b28034329817605419942cbb0a040c56011ca5a2f040a26c93929841706354813acb1c20dde188d45026826f2ad08418318726905479942cbb0a040c19c9606538f040a26c939,
      0x2198706543110c23cb29824856101ce598e6c4b128034329871605419942bcb0a040c56101ca5a2f0402a6c93929847106354813ab49c20dde1894c5026826f2cb08418318762905479942bcb0a040c19d4a06538f0402a6c939,
      0x9087654321090cc3b2a180a25c994500cc5308ec6a02921987650431194c3b28a00ca611d8c4152730aec84030897265041330143b29ca0a00e25d89451024d0a872e1402876531494194c3b28a00c4da5509c228730aec84030,
      0x352910847688bc12a31c85e54c1d92086e7124eca820f3804219576cc228bb1c81621145d8e483070a0ec9243081795460328c0bcaa301945261d94c842a930eca6421581795460328c0bcaa301945261d94c842a930eca64215,
      0x25190483765bb18c2a49051d8c615240a87124eca820f2509143876b8398a32cc1601cc51964a3070a0ec9243038209716548493a42b09865ca25458d0325302eca861938209716548493a42b09865ca25458d0325302eca8619,
      0x25194083765bb18ac249051d8c561240a87124eca820f2509413876b8398b22cc1601cc59164a3070a0ec92430382079165481b90428b4a65ca24558d0325302eca8619382079165481b90428b4a65ca24558d0325302eca8619,
      0x291087654311448bb2a1824a245d9500d27124eca820f082176935440b1baa41485058dd520826870a0ec92430392187065419c092a03b4c4e249d8541205302eca8619392187065419c092a03b4c4e249d8541205302eca8619,
      0x39281076541cac13b2081ca5609d904c252b02ec80651389721605484a43b2990856521d94c806a30f2a8c0651948376521024a41bb290811660dd908060b306ec840308350764921841a83b2490c12145d8e40b090a2ec72058,
      0x29180765431128c021bb4b0946010de5992d02ea8065328971650434bb449aa09051da24d5040a830f28ca064f39281706541841b948b2a38d460109e5a2104e2a6c9393815240976883941a8a34e5c50941a60fa30eb2c8605b,
      0x29187065431128c201bb4b0946100de5992d02ae8065328976150434bb44a9a09051da254d040a830f2c8a064f39287106541841bc90b2a38d461009e5a2104ea26c939381542097688394298a34e5c50815a60fa30ead28605b,
      0x98076543210c3cb2a19081a1e5950c804c106eca9242887965430213041bb2a148a020dd9508650730eca8420329187605431140aa183b4b0a25d94500d2f30ca8642142815430976648c32a39814de61950c04a8330eca8604f,
      0x24891073655043921b2c8a421c90d946527304eca8203098432716571420b29cb854a10594e41ea70a0ec9243035891024768924032c9b8d461cd5018a626b04ed282109420653817b4201b2938cf01e0d9490678530eca86216,
      0x8379026154384391b2a48a021c8d9506507304eca82032489137065512bcc230985c95e611840ee70a0ec924302589041376582b91b4a40dce1c6589411e6b04ed282100469132758acb01aa0b94749e4618d4136530eca86216,
      0x83792061543843931aa48a021c98d506507304eca82032489317065512bca430985c95e521840ee70a0ec924302589401376582b931ca40dce1c5a49411e6b04ed282100469312758acb01a28b94749e45a0d4136530eca86216,
      0x9870654321094c0bb2a1808a605d9500c47304eca82038379216054392c4a1b830ac96250dc059670a0ec92430298176054311240bb49a824e609d8541066b04ed282102841760935511a8bb44a05c624dd89015e530eca86216,
      0x298710654314b28c3a1813659461d0c81a10f286ca429398721605419b2c08213cccd960410a5e630f2a8c065139872106541844b990b2a38d96040925e6490ecb26035358721906481cc390a83265c08d961247848f2cb0063c,
      0x98760543210c3b14aa1881a1d8a550c04c10f26ca842829871650431143a4b289824a1d259440d230f28ca064f29871605431142389832ca8a1d258540d20af06d2843724871690534843acb1920dc95d21a440f030eb2c8605b,
      0x98765043210c3b12ca1881a1d89650c04c10f2c6a842829876150431143a34a89824a1d1a5440d230f2c8a064f29876105431142398832ca8a1d1a4540d20af0c72843724876190534843ab49920dc95d1a2440f030ead28605b,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca8420398765403210c13b2a489818a61d94500c4490ecb262098276549031304c3b29920a0921d96404d2330eca8604f],
    ![
      0x7586941230dbac34a09186dd61a5048c36eb0d282461b4650123798ea328091bcc75194048de63a8ca0246f31d7986543210c3cc32a190861e61950c8430f30ca8642187986543210c3cc32a190861e61950c8430f30ca864218,
      0x392108574681c90842ba34191625c08c6cc8b12e046367968521430cbcb4290a1865a1480c5d278d0a4062e93c6485923701b3242c91b80d9ce618945036e730c4a281b7968521430cbcb4290a1865a1480c5d278d0a4062e93c,
      0x3291805764832a43c8109d8ca46015d920ca90f2042767698251403cb2c1180bca71da6094500f2cb04602f29c6845293710b3c9c1328826da114a4dc42cf2704ca209b7698251403cb2c1180bca71da6094500f2cb04602f29c,
      0x3210987654188194c3b2a3c4c0a25d915e024712eca9b3219876054832c2390c81d9a1509c64c2cf306420ca9b310287946578811c3cab26c480de2551b730eca86421e3219876054832c2390c81d9a1509c64c2cf306420ca9b,
      0x2987103654c18cbc12a306ce45ca1501b632eca69041e3127896054d90a329cbc0599148c4225ecf306420ca9b3987210654d923298844bd989054e5e02ce24712c0a9b3127896054d90a329cbc0599148c4225ecf306420ca9b,
      0x2918074635480934a41abd4e4a05d1815e32704eac09b31289760547994c3aa0b0419148c4225ecf306420ca9b0397251684bc8aa394031f4e25c94185204c90f20a27631289760547994c3aa0b0419148c4225ecf306420ca9b,
      0x21987046534994c38a3283c0859260dd6a2730e4ac81b3218796045790a329cbc058e4a15d041a0f306420ca9b0937521648b9cc3a90320c254509e00dba48d12e0a6363218796045790a329cbc058e4a15d041a0f306420ca9b,
      0x2109876543110cc3a1b2824a4611cd8152530ea86c21832198760541994c3aa0b040e4a15d041a0f306420ca9b2104879365510c2b9ca305ca054de501ae4b0f282c61b32198760541994c3aa0b040e4a15d041a0f306420ca9b,
      0x398201574683c942b081a64e608055d1a0f250ac206998426953701b10cc3ab021e6109a54dc06c4330eac0879893756420183c821b290c6224dd5908060f2086ca4318893756420183c821b290c6224dd5908060f2086ca4318,
      0x29810746354b8b1c2a148500de49a1452e30ea6c920587163854092a1944bb28a03c25d0d948630730eac84030398217064579c31028ba4f0e1e4985412052f0ac286194029786351c91cc3b28a06e4861d5810f2490d2a6e036,
      0x329180765419944b8b2a040ca4601d95066512e2ca8103281504976890cc3ab021e4ca054125da24330eac0879398251074683c9c1328826ce609441d1a0f2704ca209b8426359701b00caba31c1761098d65c06c032ae8c705d,
      0x2190876543110c4bb2a182485020dda55442b0e8c7217218976504349944bb28a03c25cd590862e730eac840302981470635494bc2b0a18600de6189452e4af12c6821b0142659783a91cc3b28a06e441591ce0ba490d2a6e036,
      0x2987014635498c3c932283c0d5ca6105ae24f126ca81b0146925783a992c3cb020c25580c49e13a4f30c8a063639871206457923298844bd8e15ca4501a0e24712c0a9b4028796351cbc810c2a1b64de6094501b2d126240e8bc,
      0x8976052413301439b2ca0a00e1c9a5451024ca6912e1402873651494194c3b28a00c4d94925c228730eac840300387261594409329a3cc050e61c98541066b0f2c482109316857240989cc3b21283ce1d450249a2490d2a6e036,
      0x21987065431194c38b2a00c8611c1964d42712e4ca80f21487960354992c3cb020c0261d4d085ae4f30c8a0636298741063549cc3a90320c00d5e24905ae48d12e0a6367126538094a3c810c2a1b64625d14c81b0d126240e8bc,
      0x9087654321090cc3b2a180a25d894500cc530e8c6a02921987650431194c3b28a00ca61d18c4152730eac840308976250413314c3a30298a40e1e5894510730e8c2a04f0298763154409cc3b21283c4e1a549c128490d2a6e036,
      0x389210576481c49082bb241ca6194410f2e530ca208798246593710b41232c9b8858a4615d80d325230aec06998397654210841cbb2a10841c6158d0a430e30ac6852188397654210841cbb2a10841c6158d0a430e30ac685218,
      0x392108765419c90843b2a0ce0a45d9412070522eca090382105497689c1082a4bb44a4615d80d325230aec0699389215076481c490a83b241ce618945036e730c4a281b8246539710b412329cb885824551d8ca3a122a8ec651d,
      0x28917046534839cb142a0ddd84d61082682f0ac6924187613584029a0bc2b1a14860e0a5d94411e712eca84210389271065479c3cb10aa040da09405e5384f30ca280794209876315cc90c2bb01a64a4e1d944136508cb26e216,
      0x2910876543112081c3b2ca8a065d9500d20f26ca904372819765043483c9b2a140dce0a5d94411e712eca8421028917406534839cb412a0dc9e6194500f06f30ca4821b0412659738ac80aa3399474a4e1d944136508cb26e216,
      0x28971046534829bc94230dce05ca59015e2e5072ca09b0416295738acb280993a474d4a25d8052052f08ca0276389721065479ac3c90a304189054e5e02ce24712c0a9b4208976315c9cbc290a3065c24a05518f2d306420ea9c,
      0x29180765431140a03b29ca8e4a05d9410630724eca08f24189760534844b9aa130dcd4a25d8052052f08ca027628971406534829bcc1230dce25c94185204c90f20a2767216358049a0cc3aa193061c24a05518f2d306420ea9c,
      0x87965024313041bb14aa0a0209d8d645102c6a8530e14082763519440b1aa14bc050e4a1d944106712eca84210083762154941cc3b10aa00c58950de422870aed248030913658720499c3aa084b14464e1d90815e508cb26e216,
      0x98076543210c3cb290a1818a461d9500c4512ec86a20929187650431144bb218a824e4a1d944106712eca8421087965204313041bb492a0a0a25d90144d2712ec82a40f092876315440c1b2c93a05064e1d90815e508cb26e216,
      0x398210765419c288123b4c4d604811e5a26ca0248f31d0873219465703c109acb26421c8c5651b22b0f28c461b943876521024182a3b10cc200d5d18a460e2068ac5318943876521024182a3b10cc200d5d18a460e2068ac5318,
      0x298107654311428821bb4b0a1e459500d2f2d06a842142851043976648b43aa1814de5a0d5004a8330e8ca604f398217065419c288213b4c4e1e4985412052f0ac286190873291465703c10a9cb2664861d5810f2492f0ca0279,
      0x29817065431143cb0aa1824960500de598ed30a684034258140397663b4c29a010d258615d0c826312ec8a640f398271065419c3cb10aa040d605009e5a24f30ca2807908739214657490c2bb01a6421c944e51b2528ed0a0639,
      0x98706543210c3b4aa19081a1da550c804c10e6ca92428876954302130439b2a148a021cd9508650730eca8420329817605431143cb28a1824a1e594500d270f2ca4820f2871430965513b42a0c985c9da150640ee6a90ed20430,
      0x298710654311243c8b1a824a11c658c15248af12c62182874103965511bac0a4b05c9cd461241ae2b0f28c461b398721065419ac3c90a3040e15ca4501a0e24712c0a9b087932146571cbc290a3064de6094501b2130eca8643d,
      0x98760543210c13b4aa09818a61c59500c4490f2ca62098276954031304c39b2920a0921e59404d2330e8ca604f298716054311243cb09a824e61c98541066b0f2c4821028751409366394b429820d0e1d450249a2492f0ca0279,
      0x9876504321094c3b0aa180a1c9965040cc508ed2a6029872659401331423b4a818a4225d8d48510312ec8a640f298761054311cc3b10aa00ca11da44c15270aed248030287541096361c3aa084b145e49960c0528528ed0a0639,
      0x98765432104c3b2a19080661d950c8042530eca862029876543021094c3b2a09808a61d95040c4730eca842039876540321094c3b28a1808a61d94500c4730eca4820382176590433121c3b4828a490e1da405526a90ed20430]]
  let code (k : Fin 16) (m : Fin (2^9)) :=
    (blocks k (Fin.ofNat 32 (m.val/16))) >>> (45*(m.val%16))
  let choice (k m) := Fin.ofNat 31 ((code k m)%32)
  let lab (k m) (i : Fin 10) := Fin.ofNat 10 (((code k m) >>> (5+4*i.val))%16)
  have ok : ∀ k m,∀ i j : Fin 10,
      ((decide (i=j) || decide (lab k m i≠lab k m j)) &&
       (!ext k m i.val j.val || next (choice k m) (lab k m i).val (lab k m j).val))=true := by
    intro k
    fin_cases k <;> decide +kernel
  intro k m
  have inj : Function.Injective (lab k m) := by
    intro i j eq
    have ck := ok k m i j
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ck
    exact ck.1.resolve_right (fun bad => bad eq)
  have hom (i j : Fin 10) (edge : ext k m i.val j.val=true) :
      next (choice k m) (lab k m i).val (lab k m j).val=true := by
    have ck := ok k m i j
    simp only [Bool.and_eq_true] at ck
    simpa only [edge,Bool.not_true,Bool.false_or] using ck.2
  have bj : Function.Bijective (lab k m) := ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  let e := Equiv.ofBijective (lab k m) bj
  refine ⟨choice k m,e,fun i j h => ?_⟩
  calc
    next (choice k m) (e i).val (e j).val = next (choice k m) (lab k m i).val (lab k m j).val := rfl
    _ = true := hom i j h

/-- Every triangle-free graph of order ten embeds as a spanning subgraph of a listed representative. -/
lemma cover_ten :
  let adj (k : Fin 31) (i j : ℕ) := (0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*k.val+10*i+j)
  ∀ G : SimpleGraph (Fin 10),G.CliqueFree 3 →
    ∃ k : Fin 31,∃ f : Equiv.Perm (Fin 10),∀ i j,G.Adj i j → adj k (f i).val (f j).val=true := by
  intro adj
  let g1 (k : Fin 1) (i j : ℕ) := (0x0 : ℕ).testBit (100*k.val+10*i+j)
  let g2 (k : Fin 1) (i j : ℕ) := (0x402 : ℕ).testBit (100*k.val+10*i+j)
  let g3 (k : Fin 1) (i j : ℕ) := (0x100406 : ℕ).testBit (100*k.val+10*i+j)
  let g4 (k : Fin 2) (i j : ℕ) := (0x180902406000000000000000004010040e : ℕ).testBit (100*k.val+10*i+j)
  let g5 (k : Fin 3) (i j : ℕ) := (0x3018090601400000000000000e044110440e000000000000001004010041e : ℕ).testBit (100*k.val+10*i+j)
  let g6 (k : Fin 4) (i j : ℕ) := (0xc0e044110c02c000000000001c0701c380e038000000000007821084210841e000000000000401004010043e : ℕ).testBit (100*k.val+10*i+j)
  let g7 (k : Fin 6) (i j : ℕ) := (0x901c07118380e0700000000007078210846018058000000000307821084211805c000000000701c0701c781e078000000003e10441104411043e000000000100401004010047e : ℕ).testBit (100*k.val+10*i+j)
  let g8 (k : Fin 10) (i j : ℕ) := (0xa8072502321468340580000006c0701c8421078380e0000000640701c86218781e0e0000000240701c07218781e0f00000001c3e10441104c0300b80000000c3e1044110441300bc0000003c0f03c0f3c0f03c0f00000001c0701c0701cf83e0f8000001f88120481204812047e00000004010040100401004fe : ℕ).testBit (100*k.val+10*i+j)
  let g9 (k : Fin 16) (i j : ℕ) := (0x2a064074148661078540e00004a01d3410c43414c86c0b80003303c0f4310c3c0f0701c00001303c0f03d0c3c0f0781e00001103c0f03d0e3c0f03c1e00003b01c0741104410f8701c00001b01c0701d04410f8781e00001901c0701d06418f83e1e00000901c0701c07418f83e1f00000f1f881204816018060170000071f881204812058060178000031f88120481204816017c0000f03c0f03c0f7c1f07c1f00000701c0701c0701df87e1f8000fe405014050140501404fe00001004010040100401005fe : ℕ).testBit (100*k.val+10*i+j)
  let g10 (k : Fin 31) (i j : ℕ) := (0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*k.val+10*i+j)
  have h1 : ∀ G : SimpleGraph (Fin 1),G.CliqueFree 3 →
    ∃ k : Fin 1,∃ f : Equiv.Perm (Fin 1),∀ i j,G.Adj i j → g1 k (f i).val (f j).val=true := by
    intro G _
    exact ⟨0,Equiv.refl _,fun i j h => False.elim (h.ne (Subsingleton.elim i j))⟩
  have h2 := grow_catalog g1 g2 h1 extensions_1
  have h3 := grow_catalog g2 g3 h2 extensions_2
  have h4 := grow_catalog g3 g4 h3 extensions_3
  have h5 := grow_catalog g4 g5 h4 extensions_4
  have h6 := grow_catalog g5 g6 h5 extensions_5
  have h7 := grow_catalog g6 g7 h6 extensions_6
  have h8 := grow_catalog g7 g8 h7 extensions_7
  have h9 := grow_catalog g8 g9 h8 extensions_8
  have h10 := grow_catalog g9 g10 h9 extensions_9
  exact h10

/-- Number the open neighborhoods of G and lift its quotient to a catalogue representative. -/
lemma realize_ten (G : SimpleGraph (Fin 22)) (tri : G.CliqueFree 3)
    (size : (univ.image (fun i => G.neighborFinset i)).card=10) :
  let adj (k : Fin 31) (i j : ℕ) := (0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*k.val+10*i+j)
  ∃ k,∃ f : Fin 22 → Fin 10,Function.Surjective f ∧
    (∀ i j,G.neighborFinset i=G.neighborFinset j → f i=f j) ∧
    (∀ i j,G.Adj i j → adj k (f i).val (f j).val=true) := by
  intro adj
  let S := univ.image (fun i => G.neighborFinset i)
  let e : S ≃ Fin 10 := Fintype.equivFinOfCardEq ((Fintype.card_coe S).trans size)
  let q (i : Fin 22) := e ⟨G.neighborFinset i,mem_image_of_mem _ (mem_univ i)⟩
  have onto : Function.Surjective q := by
    intro a
    obtain ⟨v,_,hv⟩ := mem_image.mp (e.symm a).property
    refine ⟨v,?_⟩
    change e _=a
    rw [←e.apply_symm_apply a]
    exact congrArg e (Subtype.ext hv)
  let g := Function.invFun q
  have same (i) : G.neighborFinset (g (q i))=G.neighborFinset i :=
    congrArg Subtype.val (e.injective (show q (g (q i))=q i from Function.apply_invFun_apply))
  have rep (i j) : G.Adj (g (q i)) j ↔ G.Adj i j := by
    simpa only [G.mem_neighborFinset] using
      (show j∈G.neighborFinset (g (q i)) ↔ j∈G.neighborFinset i by rw [same])
  let Q := G.comap g
  have clean : Q.CliqueFree 3 := by
    intro s h
    obtain ⟨i,j,k,ij,ik,jk,_⟩ := is3Clique_iff.mp h
    exact tri _ (is3Clique_triple_iff.mpr
      ⟨show G.Adj (g i) (g j) from ij,show G.Adj (g i) (g k) from ik,show G.Adj (g j) (g k) from jk⟩)
  obtain ⟨k,h,hom⟩ := cover_ten Q clean
  refine ⟨k,h ∘ q,h.surjective.comp onto,fun i j eq => congrArg h (congrArg e (Subtype.ext eq)),?_⟩
  intro i j edge
  exact hom _ _ (show Q.Adj (q i) (q j) from (rep i _).2 ((rep j i).2 edge.symm).symm)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Edge maximality makes every template edge between two fibers present.
Equal template rows would then identify two distinct neighborhood classes. -/
lemma two_templates (G : SimpleGraph (Fin 22))
    (sat : Maximal (fun K : SimpleGraph (Fin 22) => K.CliqueFree 3) G)
    (size : (univ.image (fun i => G.neighborFinset i)).card=10) :
  let adj (k : Fin 31) (i j : ℕ) := (0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*k.val+10*i+j)
  ∃ k : Fin 31,(k=29 ∨ k=30) ∧ ∃ f : Fin 22 → Fin 10,Function.Surjective f ∧
    ∀ i j,G.Adj i j ↔ adj k (f i).val (f j).val=true := by
  intro adj
  obtain ⟨k,f,onto,ident,hom⟩ := realize_ten G sat.1 size
  have sym : ∀ k,∀ i j : Fin 10,adj k i.val j.val=adj k j.val i.val := by decide +kernel
  have diag : ∀ k,∀ i : Fin 10,adj k i.val i.val=false := by decide +kernel
  have triangles : ∀ k,∀ i j h : Fin 10,
      (adj k i.val j.val && adj k i.val h.val && adj k j.val h.val)=false := by decide +kernel
  let K : SimpleGraph (Fin 22) := {
    Adj := fun i j => adj k (f i).val (f j).val=true
    symm := ⟨fun i j he => (sym k _ _).symm.trans he⟩
    loopless := ⟨fun i he => Bool.noConfusion ((diag k _).symm.trans he)⟩ }
  have clean : K.CliqueFree 3 := by
    intro s h
    obtain ⟨i,j,l,ij,il,jl,_⟩ := is3Clique_iff.mp h
    have impossible := triangles k (f i) (f j) (f l)
    change adj k (f i).val (f j).val=true at ij
    change adj k (f i).val (f l).val=true at il
    change adj k (f j).val (f l).val=true at jl
    rw [ij,il,jl] at impossible
    exact Bool.noConfusion impossible
  have sub : G ≤ K := fun i j h => hom i j h
  have eq : K=G := le_antisymm (sat.2 clean sub) sub
  have refl (i j) : G.Adj i j ↔ adj k (f i).val (f j).val=true := by rw [←eq]
  refine ⟨k,?_,f,onto,refl⟩
  let twins : Fin 31 → Fin 10 × Fin 10 := ![(1,2),(0,9),(0,1),(0,1),(0,1),(2,3),(1,2),(1,2),(1,2),(1,2),(0,1),(1,2),(0,1),(0,1),(1,2),(0,1),(1,2),(0,1),(0,1),(0,1),(4,5),(3,4),(1,2),(4,5),(6,7),(1,2),(0,1),(6,7),(5,6),(0,0),(0,0)]
  have cert : ∀ k : Fin 31,k≠29 → k≠30 → (twins k).1≠(twins k).2 ∧
      ∀ j : Fin 10,adj k (twins k).1.val j.val=adj k (twins k).2.val j.val := by decide +kernel
  by_contra! other
  obtain ⟨ne,rows⟩ := cert k other.1 other.2
  obtain ⟨i,hi⟩ := onto (twins k).1
  obtain ⟨j,hj⟩ := onto (twins k).2
  have twin : G.neighborFinset i=G.neighborFinset j := by
    ext v
    simp only [G.mem_neighborFinset,refl,hi,hj,rows]
  exact ne (hi.symm.trans ((ident i j twin).trans hj))

lemma search_boxes (x : Fin 10 → ℕ) (P : Prop)
    (leaf : ℕ → (Fin 10 → ℕ) → (Fin 10 → ℕ) → Bool)
    (valid : ∀ s lo hi, (∀ i,lo i ≤ x i) → (∀ i,x i ≤ hi i) → leaf s lo hi=true → P) :
    let run (t : BinaryTree ℕ) := BinaryTree.rec (motive:=fun _ => (Fin 10 → ℕ) → (Fin 10 → ℕ) → Bool)
      (fun _ _ => false) (fun s _ _ l r lo hi =>
        if s<512 then leaf s lo hi else
          l lo (Function.update hi (Fin.ofNat 10 ((s-512)%10)) ((s-512)/10)) &&
          r (Function.update lo (Fin.ofNat 10 ((s-512)%10)) ((s-512)/10+1)) hi) t
    ∀ t lo hi, (∀ i,lo i ≤ x i) → (∀ i,x i ≤ hi i) → run t lo hi=true → P := by
  intro run t
  induction t with
  | nil => simp [run]
  | node s l r hl hr =>
    intro lo hi low high h
    by_cases tip : s<512
    · exact valid s lo hi low high (by simpa only [run,BinaryTree.rec,tip,if_true] using h)
    let k := Fin.ofNat 10 ((s-512)%10)
    change (if s<512 then _ else _ && _)=true at h
    rw [if_neg tip,Bool.and_eq_true] at h
    by_cases side : x k ≤ (s-512)/10
    · apply hl lo _ low _ h.1
      intro i
      by_cases eq : i=k
      · subst i; simpa [k] using side
      · rw [Function.update_of_ne eq]; exact high i
    · apply hr _ hi _ high h.2
      intro i
      by_cases eq : i=k
      · subst i; simpa [k] using (show (s-512)/10+1 ≤ x k by omega)
      · rw [Function.update_of_ne eq]; exact low i

lemma tighten (x lo hi : Fin 10 → ℕ) (mass : ∑ i,x i=22)
    (low : ∀ i,lo i≤x i) (high : ∀ i,x i≤hi i) (i : Fin 10) :
    max (lo i) (22+hi i-(∑ j,hi j)) ≤ x i ∧
    x i ≤ min (hi i) (22+lo i-(∑ j,lo j)) := by
  have sl := sum_erase_add univ lo (mem_univ i)
  have sh := sum_erase_add univ hi (mem_univ i)
  have sx := sum_erase_add univ x (mem_univ i)
  have al := sum_le_sum (s:=univ.erase i) (fun j _ => low j)
  have au := sum_le_sum (s:=univ.erase i) (fun j _ => high j)
  exact ⟨max_le (low i) (by omega),le_min (high i) (by omega)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- The ten fibers are nonempty. Split codes encode a coordinate and a threshold.
At a nonempty leaf the ten-bit cut costs at most sixteen on the full box. -/
lemma weights_29 :
  let E : Finset (Fin 10 × Fin 10) := {(0,7),(0,8),(0,9),(1,6),(1,7),(1,8),(2,5),(2,7),(2,9),(3,4),(3,5),(3,6),(3,7),(4,8),(4,9),(5,8),(6,9)}
  let cost (x : Fin 10 → ℕ) (m : ℕ) := ∑ e∈E,
    if m.testBit e.1.val=m.testBit e.2.val then x e.1*x e.2 else 0
  ∀ x : Fin 10 → ℕ, (∀ i,1 ≤ x i) → (∑ i,x i)=22 → ∃ m,cost x m≤16 := by
  intro E cost x positive mass
  let leaf (s : ℕ) (lo hi : Fin 10 → ℕ) :=
    let sl := ∑ i,lo i
    let sh := ∑ i,hi i
    let h (i : Fin 10) := min (hi i) (22+lo i-sl)
    if s=511 then decide (22<sl ∨ sh<22) else decide (cost h s≤16)
  have valid s lo hi (low : ∀ i,lo i≤x i) (high : ∀ i,x i≤hi i) (check : leaf s lo hi=true) :
      ∃ m,cost x m≤16 := by
    by_cases empty : s=511
    · have bad : 22<(∑ i,lo i) ∨ (∑ i,hi i)<22 := of_decide_eq_true (by simpa only [leaf,empty,if_true] using check)
      have a := sum_le_sum (s:=univ) (fun i _ => low i)
      have b := sum_le_sum (s:=univ) (fun i _ => high i)
      omega
    · refine ⟨s,le_trans ?_ (of_decide_eq_true (by simpa only [leaf,empty,if_false] using check))⟩
      apply sum_le_sum; intro e _
      split
      · exact Nat.mul_le_mul (tighten x lo hi mass low high e.1).2 (tighten x lo hi mass low high e.2).2
      · exact le_rfl
  have cap (i : Fin 10) : x i≤13 := by
    have h := sum_erase_add univ x (mem_univ i)
    have low := sum_le_sum (s:=univ.erase i) (f:=fun _ => 1) (g:=x) (fun a _ => positive a)
    have size : (univ.erase i).card=9 := by simp
    simp only [sum_const,size,smul_eq_mul,mul_one] at low
    omega
  let readBlock (code : ℕ) := Nat.rec (motive := fun _ => ℕ → List (BinaryTree ℕ) → BinaryTree ℕ)
    (fun _ stk => stk.headD .nil)
    (fun _ step data stk => if data=0 then stk.headD .nil else
      let s := data%1024-1
      if s<512 then step (data >>> 10) (BinaryTree.node s .nil .nil :: stk)
      else match stk with
        | left :: right :: tail => step (data >>> 10) (BinaryTree.node s left right :: tail)
        | _ => .nil) 95 code []
  let branch := @BinaryTree.node ℕ
  let box (lo hi : Fin 10 → ℕ) :=
    (∀ i,lo i≤x i) → (∀ i,x i≤hi i) → ∃ m,cost x m≤16
  have divideBox (lo hi : Fin 10 → ℕ) (i : Fin 10) (k : ℕ)
      (left : box lo (Function.update hi i k))
      (right : box (Function.update lo i (k+1)) hi) : box lo hi := by
    intro low high
    by_cases h : x i≤k
    · apply left low
      intro a
      by_cases eq : a=i
      · subst a; simpa using h
      · rw [Function.update_of_ne eq]; exact high a
    · apply right _ high
      intro a
      by_cases eq : a=i
      · subst a; simpa using (show k+1≤x i by omega)
      · rw [Function.update_of_ne eq]; exact low a
  have done : box (fun _ => 1) (fun _ => 13) := by
    refine divideBox _ _ 3 7 ?_ ?_
    · refine divideBox _ _ 8 7 ?_ ?_
      · refine divideBox _ _ 9 7 ?_ ?_
        · refine divideBox _ _ 7 7 ?_ ?_
          · refine divideBox _ _ 8 4 ?_ ?_
            · refine divideBox _ _ 9 4 ?_ ?_
              · refine divideBox _ _ 3 4 ?_ ?_
                · refine divideBox _ _ 7 4 ?_ ?_
                  · refine divideBox _ _ 9 2 ?_ ?_
                    · refine divideBox _ _ 8 2 ?_ ?_
                      · refine divideBox _ _ 7 2 ?_ ?_
                        · refine divideBox _ _ 3 2 ?_ ?_
                          · refine divideBox _ _ 0 7 ?_ ?_
                            · refine divideBox _ _ 4 7 ?_ ?_
                              · refine divideBox _ _ 2 7 ?_ ?_
                                · refine divideBox _ _ 5 7 ?_ ?_
                                  · refine divideBox _ _ 1 7 ?_ ?_
                                    · intro low high
                                      apply search_boxes x _ leaf valid (branch 588 (branch 557 (branch 558 (branch 556 (branch 553 (branch 552
                                        (branch 554 (branch 533 (readBlock
                                        0x2173ca1a86c20854f2864208502083820848f284c561e2153ca1b8642084c20850f283820848f2082198502084c2083a123ca0c83d4e08020848f2082143ca13838203c8f2)
                                        (branch 534 (readBlock
                                        0x21b86820854f28642084c2083820848f2850341e2153ca1a864208502084cf2848f2838200821984c208502083a123ca0d83dd508020848f2082133ca14838203c8f2)
                                        (readBlock
                                        0x21a86c208642085614082133ca12838208420b754203ca0e080208502084e123c8200821b8642085613082143ca12838208460b538203ca0e0802084c20852123c820082198561308214082128394e83e0b538203ca0e82e0f538200802084c208502008213850f23ca143c8f2)))
                                        (branch 538 (readBlock 0x21a082190821685614442130820e082128454e3c91084c20852123c8200821308214848f208020)
                                        (readBlock
                                        0x21a85a1908215850f2838208485684c56162140820e08056864208502084a13158200821686615851108394e84c2084a0f538f244214082130814e85213440f283a130814e3ca1484c20082128394e08020)))
                                        (readBlock
                                        0x22b86a1b0821685c78864208502084876162190821408213848f20802086e17858788642084c20848740e2190821308214848f20802085a1783a1308214082121ca0d1e0788661308214082123c87884e14080761d21484c20082130802084e1408020850200821a86c20850200821308020))
                                        (branch 554 (branch 552 (branch 537 (readBlock
                                        0x21b0821908217856137c6140820e08212841d53c9d58502084e123c8200821408213848f208020) (readBlock
                                        0x21b85e190821584cf28382084834850340e2130820e080348642084c2084a140d020082178661584df1839d58502084a0f754f27561308214081d584e147c4f283a14081d53ca138502008212839d508020))
                                        (readBlock 0x21b8682084c200821408020)) (readBlock 0x21a86c20850200821308020))) (branch 553 (branch 554 (branch
                                        552 (readBlock
                                        0x21685cf286a1b1e2153ca143ca0e16076854f2850f284e0e080f21e21786e1a1e2153ca133ca0e0e074854f284cf28520e080f21e21a86e1284cf2850f283818840781e21584cf2850f2838201e2138502016038852133c8f284cf208213850f23ca143c820)
                                        (readBlock 0x21785a1b1e2121d87886e0e0e0780e21a86e0e1607815858)) (readBlock
                                        0x21a86e16162148481884cf20621284c581605885216838203c8208385815a1484cf23ca13838203c858)) (readBlock
                                        0x22186e1a87e13848f2851f185c38062120e20e0e0380e21385e0e080f20820e0e03484e143c8f28520e080f20e213850f206018)))
                                        (branch 553 (branch 554 (branch 552 (branch 556 (branch 534 (readBlock
                                        0x2163ca153ca1a866147c6133ca123ca0e835d5081d584cf28520e080f23ca133ca14838203c8f2) (readBlock
                                        0x21686a153ca1985020848f28385684c561da143ca123c856854f2850f283a13158f23ca1a85619851f1849d584cf283a0b75420756143ca133c9d5852137c42084a133c9d50821484cf23ca0e849d53c8f2))
                                        (readBlock 0x21685cf2850f23ca133c8f2)) (readBlock
                                        0x21685e1a1da148387284c201ca0e84c761d8768521a848f2080208487615a1484c2008213848f208076)) (readBlock
                                        0x21f88e1686a1483820848f284c200820e15a1215a1315856852133c8f283a135595655a1484c200821284d5655956850f215a1408056))
                                        (readBlock 0x22187e2386a147c61385df17c61985617755d5755d584e147c4f2839d5756133c820850203ca14081d5))) (branch
                                        558 (branch 554 (branch 553 (branch 552 (branch 556 (branch 533 (readBlock
                                        0x2173ca153ca1b86613442143ca123ca0e8314e08110850f284e0e080f23ca143ca13838203c8f2) (readBlock
                                        0x21786e153ca1984c20848f283834850341d2133ca123c834854f284cf283a140d0f23ca1b8561984d108494e850f283a0b53820442133ca143c94e84e144402084a143c94e08213850f23ca0e8494e3c8f2))
                                        (readBlock 0x217858f284cf23ca143c8f2)) (readBlock
                                        0x21785a1b1d21383872850201ca0e850741d07484e1b848f208020848740d2138502008214848f208074)) (readBlock
                                        0x21f88e1b85e1383820848f2850200820e0d2120d2140d03484e140802084a14735cd73613850f23ca0e851cd735cd84cf20d21308034))
                                        (readBlock 0x22087e2386e13442148591044219856164414e5394e85213440f28394e442143c82084c203ca130814e)) (readBlock
                                        0x2208861f88e173ca163c8f23ca0e84cf21c8f2850f253a133c9d5))) (readBlock
                                        0x22187e2488e2085cf2850f2858f27561385cf2755d5858f23ca173c8f2852137c5f11da1486a137c4f23ca123c856)) _ _ low high
                                      decide +kernel
                                    · intro low high
                                      apply search_boxes x _ leaf valid (readBlock
                                        0x22488e2187e258682084c2086c207561486820755d586c200821a0802084e147c5f10e21385e147c4200820e08034) _ _ low high
                                      decide +kernel
                                  · intro low high
                                    apply search_boxes x _ leaf valid (readBlock
                                      0x22087e2588e21858f284cf285cf253a14858f24411085cf23ca163c8f284e14441101d21386e14440f23ca123c834) _ _ low high
                                    decide +kernel
                                · intro low high
                                  apply search_boxes x _ leaf valid (readBlock
                                    0x22588e2087e2486c20850208682053a1386c2044110868200821b0802085213441101621485a13440200820e08056) _ _ low high
                                  decide +kernel
                              · intro low high
                                apply search_boxes x _ leaf valid (readBlock
                                  0x2208861f89225858f285cf21e2163c8f285cf23ca12858f20e078852163c8181621385cf206038) _ _ low high
                                decide +kernel
                            · intro low high
                              apply search_boxes x _ leaf valid (readBlock
                                0x22489623886208682086c200821b08020868200820e868201d0788521a080721da1386c201c874) _ _ low high
                              decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 577 (branch 576 (branch 578 (branch 573 (branch 572 (branch 574 (branch 548
                              (branch 547 (branch 546 (branch 542 (branch 544 (branch 543 (readBlock
                              0x21a8661b082153ca123ca14042163ca173c82086e123ca153ca163ca173ca133c820848f2854f2858f23ca1b866153ca123ca13042173ca163c820848f2854f285cf23ca19854f285cf2858f2042173ca163c8f2)
                              (branch 537 (readBlock
                              0x21986c2084c108501084a1585df1841d50821008020856177c4200821b84a133ca1404217856111e210754f2844781e2111e07884c108501085e158461008222080f2841f13c8780821385010848f23ca12850103ca147c4f2)
                              (readBlock
                              0x21b86613042128501085e158442083c203ca111e020844200821785614042110820f080f285010082140402084c1084a14844343c8f2850f23ca1984c1084a14040f2851f13ca133c8f2)))
                              (branch 543 (branch 538 (readBlock
                              0x219868208501084c1084a15859108454e082110802085616440200821a84a143ca1304216856101e211440f2840781e2101e0788501084c1085a158421108222080f2845103c8780821484c10848f23ca1284c103ca13440f2)
                              (readBlock
                              0x21a866140421284c1085a158402083c203ca101e020840200821685613042100820f080f284c1008213040208501084a13840563c8f284cf23ca198501084a13040f284d103ca143c8f2))
                              (readBlock 0x21b8661a0821304212850100802086a1284c10850101e213040203ca1a866140421284c10080203c810))) (branch 544 (branch
                              543 (readBlock
                              0x21a86e121e21908214042130421685c781e07884a161e2143ca133c8f286614042130421685e3384020888203c878080208501084cf21e21b84a171e2133ca143c8f286613042140421785a3384420888203c8780802084c10850f21e212850f284cf23ca1984c10850101e0f2)
                              (readBlock 0x21b86a190821284c10850101e213040788661304212850101e0203ca1a8661404213040203c810)) (readBlock
                              0x22086a1b8642084a140421304078850101e2198501084a1304078080f286e1984c1085010080f204020))) (branch 543 (readBlock
                              0x22187e163ca173ca123ca133c8f284a1a8587886c783ca1b85c783c8f286a1b852130421685c781e07884e17858781e0781e2133c878850f21e21f852163ca133c8f286a1286e138405885a353c8583ca16840783c8783ca1b84e1585a353c8581e078842111e0783c8f2848f23ca12850f21e010)
                              (readBlock
                              0x22187e1385cf2850f23ca1b84a1a852110e2178d0f20e0f285e111e0f21e0f286a14856178d0f20e0781e211840781e0f23ca123c8f284a133c8780421284e143c8781e0f2)))
                              (branch 546 (branch 542 (readBlock
                              0x2208861b854f285cf284cf2858f2082163ca173c8f286e1984d1085616442144414e851104421484d103ca13440f285213440f284d103ca2184e1b85010864103ca143c8f286e128661784474856143c8f23ca11850f2538f23ca1985e1584634850f283c203c820850f23c820080f2848f23ca130414e)
                              (readBlock 0x2208861386e1404219040f2850103ca1b84a173c8f285e16852198ccf21d0748460d1d0201e020082123c8f284c103ca1304074))
                              (readBlock 0x2218821f85cf2858f23ca123c8f284cf21d2143c8f2))) (branch 547 (branch 546 (branch 542 (readBlock
                              0x2218821a854f2858f2850f285cf2082173ca163c8f286a19851f1856177c6137c5d584df175613851f13ca147c4f284e147c4f2851f13ca208521a84c10864103ca133c8f286a128661684076856133c8f23ca1084cf2754f23ca1985a158423584cf283c203c82084cf23c820080f2848f23ca14041d5)
                              (readBlock 0x2218821486a1304219040f284c103ca1a84a163c8f285a1784e198ccf21d8768420c1d8201e020082123c8f2850103ca1404076))
                              (readBlock 0x2208861f858f285cf23ca123c8f2850f21da133c8f2)) (readBlock
                              0x2208861f88e173ca163c8f23ca123c8f2850f23ca133c8f2))) (readBlock
                              0x22588e248821f86e1986820850104421484c104421284d10161108661a8501084a1008110081104402008110851101621404056)) (readBlock
                              0x224896238822186a1b84878864201e212850101e2140402086e1284c101e213040201c8200807884876042121d010)) (readBlock
                              0x22488e258861f86a1986c2084c107c613850107c612851f10e1f18661b84c1084a11081f1081f17c420081f184df10e21304034)) (readBlock
                              0x2248861f8822386a153ca173c8f285cf23c8f27c6123c9f1850f21d8f2)) (readBlock
                              0x2208861f89225858f285cf23c8f23c878850f21e2133c878)) (readBlock
                              0x2258821f8862386e153ca163c8f2858f23c8f2442123c91084cf21d0f2)) _ _ low high
                            decide +kernel
                        · refine divideBox _ _ 3 2 ?_ ?_
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 573 (branch 572 (branch 574 (branch 577 (branch 576 (branch 578 (branch 543
                              (branch 544 (branch 542 (branch 546 (branch 548 (branch 547 (readBlock
                              0x216856173ca190820e082143c61a0821b080f285e0e082190821a0821b082130807883820864208682008217856190820e082133c61b0821a080f2838208642086c2008215864208682086c203c61b0821a08020)
                              (branch 533 (readBlock
                              0x21585cf284cf1850f183a1986d108314e3ca0c3c8208661b440f23ca1783a13082143c61b8660d1e20c44020834781e20d1e07884cf1850f186e198360c1e2261e02083110080781e213850f1838200820e850f10821444020)
                              (readBlock
                              0x217856133c60e850f186e198347882cf20820d1e020834f23ca1b866143c60d3ca0b3c820850f13ca143c4f284cf183a148343408020850200821584cf183a143c420851100821308020)))
                              (branch 547 (branch 534 (readBlock
                              0x215858f2850f184cf183a19869f1835d53ca0d3c8208661a7c4f23ca1683a14082133c61a8660c1e20d75420830781e20c1e078850f184cf186a198320d1e2261e020835f1080781e21484cf1838200820e84cf1082137c420)
                              (readBlock
                              0x216856143c60e84cf186a198307882cf20820c1e020830f23ca1a866133c60c3ca0b3c82084cf13ca133c4f2850f183a13830560802084c2008215850f183a133c42084df10821408020))
                              (readBlock 0x216856173ca143c60e84cf13c8f285e0e84cf1850f11e2133c4f208217856133c60e850f13c8f2080f1))) (branch 547 (branch
                              548 (readBlock
                              0x21785a0e1e2153ca133c6143c61a86c781e07883a1b082130821408020856133c6143c61b86a378347889878080783c8f284cf1850201e21683a1a082140821308020856143c6133c61a86e378307889878080783c8f2850f184c201e20e84c20850200821584cf1850f108020)
                              (readBlock 0x21685e153ca0e850f184cf11e2143c478856143c60e84cf11e0f208217856133c6143c4f2080f1)) (readBlock
                              0x22585e16854f283a133c6143c47884cf11e21584cf183a143c4783c82085a15850f184cf13c8203c4f2))) (branch 547 (readBlock
                              0x22588e1a0821b0820e082130802083a1786c208587808216868200802085a17852133c61a86c781e07884e1b868781e0781e21308078850201e2238521a082130802085a0e85e138307686a39080760821a83078080780821784e1986a3908076080788320d1e02008020838200820e850201e0f1)
                              (readBlock
                              0x22588e1386c20850200821783a168520d1d21b8e0201d02086e0d1e0201e02085a148661b8e0201d0201e20d83078080200820e0802083a13080783c60e84e14080781e020)))
                              (branch 542 (branch 546 (readBlock
                              0x2258921686420868208502086c200821b0821a0802085a15851108661b442134414e84d104421385110082144402084e144402085110082248521684cf1854f1082130802085a0e8561a8305886613080200820c84c20538200821586a198323984c2082cf2080f284c20080f23c82083820082143c54e)
                              (readBlock 0x2258921485a133c6153c42084cf10821683a1a0802086a1b84e158dc201605883210160f2080f23ca0e08020850f1082143c458))
                              (readBlock 0x224896238682086c200820e08020850201621308020))) (branch 544 (branch 542 (branch 546 (readBlock
                              0x224896178642086c2084c20868200821a0821b0802085e1584df18661a7c6147c5d5851f17561484df1082137c420852137c42084df10822584e17850f1854f1082140802085e0e8561b8343886614080200820d85020754200821586e19836388502082cf2080f285020080f23c82083820082133c5d5)
                              (readBlock 0x2248961385e143c6153c420850f10821783a1b0802086e1a852158dc200e038836110e0f2080f23ca0e0802084cf1082133c438))
                              (readBlock 0x2258922386c20868200820e0802084c200e21408020)) (readBlock
                              0x2248962387e1b0821a080200820e08020850200821308020))) (readBlock
                              0x22187e208922385e15858f2850f17c61484cf17c60e84df11d9f185616850f183a0c3c9f13c9f17c4f23c9f1851f11da143c456)) (readBlock
                              0x2208861f8922585a1783878854f21e20e850f11e2143c47885e0e84cf11e2133c478060f23c878838583c60e0e0f1)) (readBlock
                              0x22087e218962385a1585cf284cf144213850f14420e851101d1108561784cf183a0d3c9103c910440f23c91084d101d2133c434)) (readBlock
                              0x220896238921f85a190821b0802086c20080204420e081108502016020)) (readBlock
                              0x22489623886208682086c200802008078850201e21308078)) (readBlock
                              0x221892238961f85e190821a0802086820080207c60e081f184c200e020)) _ _ low high
                            decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 563 (branch 562 (branch 564 (branch 567 (branch 566 (branch 568 (branch 542
                              (branch 544 (branch 543 (branch 546 (branch 548 (branch 547 (branch 532 (branch 536 (readBlock
                              0x21a85df186c2085a14042130420b3ca0f080208501084c100821686d1085cf2850f184cf13ca1b85e13042140420b3ca0f0802084c10850100821784cf1850f13c810)
                              (readBlock
                              0x217858f284cf186a1b850f182cf2898f2082143c4f2850f13ca16850f186e1a84cf182cf2898f2082133c4f284cf13ca1b86a1304214040203c4f1))
                              (branch 536 (readBlock
                              0x21a86c208501085e1684c1083c20888203ca130402084c100821b84c1085a178501083c20888203ca1404020850100821685e1304214040f204010)
                              (readBlock
                              0x21785a1b86a14042130422688a10082110807884211080f23ca228320d1e0200802084cf1850f11e21a850f184cf11e0f184cf18501008216850f184c1008010)))
                              (readBlock
                              0x21585a173ca143c61986d103c8f285e133c61986e143c60b3c8203c8f284d104421685e133c61986e144420c440203c8f284d104421344020))
                              (readBlock
                              0x22485617858f284cf18661a7c4f23ca16850f18661a84cf182cf2080f23ca147c5f185e16850f18661a84df1835f1080f23ca147c5f1851f10821585a173c8f13c4f1))
                              (readBlock
                              0x2258921585a173ca143c6133c60b3c87885e133c6143c60b3c87884cf13ca1685e133c6143c62688a0c1e0783c878850f11e2133c4788561685cf23c4f13c61585e163c8f13c4f1))
                              (readBlock
                              0x223892258661a86c2085010856177c4200821b84c10856178501083c203c820082137c5f186a1b84c1085617851f1841f13c820082137c5f184df13ca1585e137c5f17c5f184e14040108520b3c42008213850f13c61489a22841f13c8f23c4f2))
                              (readBlock
                              0x22088e258921986e1a0821304215859100802086a140421585a130420f080f208020851104421b86a140421585a1344211440f2080208511044214440f28561685110441104421484c100421382cf108020852133c4f184e2688a11440f23c8f13ca1986e1a0801004010))
                              (branch 546 (readBlock
                              0x224896218821986e1a08213042140420f0807886a14042130420f0807884c100821b86a13042140422289a11080780807884c101e214040788661a86c20040100421986e1a0801004010852130401084e2289a0d7c4200801008213850100421488a26831100802004020)
                              (readBlock 0x2138501088a26844781e0781e21488a26830781e0781e078))) (readBlock 0x21585e163c9f1850f13ca147c5f1)) (readBlock
                              0x217856163ca133c4f284e143c4781e2143c4f2)) (readBlock 0x21585a173c91084cf13ca1344110)) (readBlock
                              0x21986e1a08110850100821444110)) (readBlock 0x21b8661a082130402084e14040781e21404020)) (readBlock
                              0x21986a1b081f184c10082137c5f1)) _ _ low high
                            decide +kernel
                      · refine divideBox _ _ 5 6 ?_ ?_
                        · refine divideBox _ _ 4 6 ?_ ?_
                          · refine divideBox _ _ 6 6 ?_ ?_
                            · refine divideBox _ _ 7 2 ?_ ?_
                              · refine divideBox _ _ 1 6 ?_ ?_
                                · refine divideBox _ _ 0 6 ?_ ?_
                                  · refine divideBox _ _ 2 6 ?_ ?_
                                    · refine divideBox _ _ 3 2 ?_ ?_
                                      · refine divideBox _ _ 5 3 ?_ ?_
                                        · refine divideBox _ _ 1 3 ?_ ?_
                                          · refine divideBox _ _ 6 3 ?_ ?_
                                            · intro low high
                                              apply search_boxes x _ leaf valid (branch 544 (branch 542 (branch 546 (branch 537 (readBlock
                                                0x2161e21b1e2198561783840850208487883c208402082e0d1e0f21e21408212839c58402083dd57560e082100802085e140820e102121e210080208502084a0e080200821585e0e1e214848788402089c201e2121e2101e0f28520e082125342083a121e0201e21783878852121e0201e020)
                                                (branch 533 (readBlock
                                                0x2171e2158661b848f4850f28387882cf2830f283e111e020082143ca0e8494d8307882d4e53a123ca0c3c8f286e143ca123d20e1e20c3c8f2850f283a121e0f23ca1986e121e21483878830f289c200820e1e20c1e020852123ca0e714f284a0e1e0f21e21b848788520e1e0f21e0f2)
                                                (branch 534 (readBlock
                                                0x21b1e2158660e851c5849cd8347882dc575612851cd83dd582d4d3ca1489cf283dc53ca0b83dd53c8f283a140e2121e0f2852121d0f23ca1983a140e2121e040852121d0201e034)
                                                (readBlock
                                                0x21b8661584a145360e736111e20f5354e83a147360b53a0f71420852270820b5342083e0b538200821285074838780821483838080208561285074838783d214838383c8200d2158660e851c5849cd53a128514d53820535c5))))
                                                (readBlock
                                                0x21685c7886878852123ca153c8788561b848f4838783c8f21e21786c7883a140e21a1e0f286a121e21489cf21e0f23ca1b86878852121d0381e214838383c820))
                                                (readBlock
                                                0x22386a1b1e2161e21483820864200821985e0e102121e0200807886e171e2128507485878082168387885227080780802085e161e214838381d078852121d0201e21a86c78858780e21685c781d034))
                                                (branch 546 (branch 542 (branch 537 (branch 533 (readBlock
                                                0x2198561b0821408212840208394d83c20830783ca0e082100820c82cf20802086c208502084a100820e080788402008215852125361b0820e0820c3c82086e1284078838208d47853a100820e0820c1e02084a101e20e83078538f283a10080781e21484a1b3d0f2838200821b84a101e0788407808078)
                                                (readBlock
                                                0x21986c2085612850208402083820756140820e08020850200821b84a140821584020838201e020856140820e08020082148494d08020))
                                                (branch 533 (branch 532 (readBlock
                                                0x21986e14536125360e82d4e8314e89c200820b53a0c83d4e53820852125360e5360c3c8f284a0e5360f534f283a0c82d4e5394e3ca148494d86e0e5360c3c8f23ca1b84a0e5360b534f483a0c82d4e080203c8f2)
                                                (readBlock
                                                0x219852125361b83820830f20802086e1283a270820f534f483e27080f43d20e89c20080203ca14848f4080f4))
                                                (readBlock
                                                0x2198561b84a145360e5360f5354e8520e082270814d83a0b53820082128514d5382084a1453420082128514d53820)))
                                                (readBlock
                                                0x21a86e1008219082121e0208521285a19080780802084a101e0781e21484a1686e19838201d0743c820838200821283a270807808020))
                                                (readBlock
                                                0x21f86a168521286cf483a15534783ca1583a1b0802086e0c3ca101e0f23ca0e0807883a101621b1607884a1b840781e078840781e21484a1b838183d020838201e212840780802085216856123ca0e830f23c8f23d0b484a0e89e0c3c8f43d0f43ca121e078)))
                                                _ _ low high
                                              decide +kernel
                                            · intro low high
                                              apply search_boxes x _ leaf valid (branch 544 (branch 542 (branch 546 (branch 533 (branch 537 (readBlock
                                                0x215866173ca143ca0e83078849c582cf284078082123ca0c3ca1083c203c8f285cf2850f283a0c1e2123c878830f21e2198520e716173ca123ca100802085e0e83078848f28e4787560c1e2123ca101e07883a0c1e212840787542084a0c1e0201e21483a1710020848f23ca1783a0c1e078830781e078)
                                                (readBlock
                                                0x21585cf28660e850f2830f2848f253a143ca123c8f2850f23ca1783a143ca1983078848f21e078866143ca123c8783ca14839c53c8f2))
                                                (branch 537 (branch 536 (readBlock
                                                0x21585e147160e7161283dd5841d589cf23ca0f7561082dd5754f28520e71612716100802083a127160b7142084a1083dd5755d508214839c585e1271610080200821783a127160f7144084a1083dd53c8f208020)
                                                (readBlock
                                                0x2158520e71617848f2840203c82085e0e84a273ca0b7144082e273c8401021289cf21e0f2082148384008040))
                                                (readBlock
                                                0x2158661783a14716127160b715d5852123ca273c9c584a0f754f23ca0e851c5754f283a14714f23ca0e851c5754f2)))
                                                (readBlock
                                                0x21685e0c3ca153ca0e1e0f28520e86a153c8783c8f283a0c1e0781e21483a1a85e15848f20e038080f2848f23ca0e84a273c8783c8f2))
                                                (readBlock
                                                0x22385a1a8520e85c4084a19714780821984a173c8f285e100820c1e020082123c87884a0c1da171d82083a17830781e078830780821483a1784872100f2848f21e20e830781e0788521a8660e0821284020080201003c83a1289e1008040100400820e1e078))
                                                (branch 542 (branch 546 (branch 533 (branch 537 (readBlock
                                                0x2148561983820848f284020830f20820e8494d082123c8f286612839c53ca0e080201e2158661283a0c15a1015a0b535d58420c1da0f75478830f27560e832101620b538788402053a0c840783c82083a12830781e0781e21283a10080781e078)
                                                (readBlock 0x2148560e8494d830f23ca123c8f23ca0e84a0b534f2538f2)) (readBlock
                                                0x21a8521984a0e7161008020838200802084a0e83dc5081d50814d)) (readBlock 0x21483a123c8f23c878)) (readBlock
                                                0x21484a0e0802008078))) _ _ low high
                                              decide +kernel
                                          · intro low high
                                            apply search_boxes x _ leaf valid (branch 548 (branch 544 (branch 546 (branch 542 (branch 537 (readBlock
                                              0x21b8642085c38848388502083838082198502085e158384084a0f756100820b755d583c20840207560e1021283c200802085612839c583dd50820e08020082148382084a170e02084020082178383884a10080f208020)
                                              (branch 538 (readBlock
                                              0x217866158383884838850388443883e0d0e0201e20e0e2120e2140e0788383884838850381e21984a15851cd839cd8443853a140d0208560e851cd8443808214844380802008212850340e020)
                                              (readBlock
                                              0x21985e1583a14716127360d0e1d584a147360f754f28520f714f27560e850380e1d584a14735d57160e850380e034)))
                                              (readBlock 0x21b86a19082140803885e0e0e2140e0780d21a85219080388384008034)) (readBlock
                                              0x21f86e1a8383885c38848380e21783838848380e03486a0e850380e21484838080780d038)) (readBlock
                                              0x22387e1a86e19082128502084020082140802086612850208382008214080200821b84a19856145360e7354e7354d8520e080200814d082128520e080380e020))
                                              (readBlock
                                              0x22387e2186a198520e71617855c584020756127142085617839c583dd584a10755d57560e849c5081d583a12714407561483a171002084a10080f20820e84a2782dd510040101d58661585e0e851c5849c575614849c5755d5715c57361484a0e71420081d58520e100201020e850380e0f2))
                                              _ _ low high
                                            decide +kernel
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 543 (branch 544 (branch 548 (branch 542 (branch 546 (branch 533
                                            (readBlock
                                            0x217854f286c7483874850f2848741e215850f286e19848f483a0b53a0c3ca0f5394e82cf2830f253a123d20e82cf23c8f28660e8494d82d4e3ca123c8f23ca14848f283a1b1d0f2830f20821b8487483a0c3c8203c8f2)
                                            (branch 534 (readBlock
                                            0x21b856198487483874850748347482e111d0f21e2121d20e1d2141d0788487483874850741e21583a19851cd849cd83474756140d0f286612851cd834743ca14834743c8f23ca0e850341d0f2)
                                            (readBlock
                                            0x21586e1984a145360e736111d14e83a147360b538208520b5342053a12850741d14e83a147354e53612850741d034)))
                                            (readBlock 0x21785a153ca143c87486e121d2141d0780d216852153c874848f43c834)) (readBlock
                                            0x22385e168487486c74838741d21b84874838741d03485a12850741d214838743c8200d074)) (readBlock
                                            0x21f88e1685e153ca0e850f2830f23ca143c8f28560e850f2848f23ca143c8f23ca1783a158661471612735d5735c5852123c8f23c94d3ca0e852123c8741d0f2))
                                            (readBlock
                                            0x21f88e2585a15852125361b8654d830f253a0e534f28661b8494d82d4e83a0c5394e53a128394d3c94e84a0e534f453a1484a1b3d0f283a0c3c8203ca1283a2783d4e3d0f43d14e8561986e128514d8394d53a148394d5394e5354d7361483a12534f23c94e852123d0f23d212850741d020))
                                            (readBlock
                                            0x2218961f88e1b85e0e0d2120d2198560d0d2140d1cd0d03484a140d20e7354e83a14735cd53a1783a140d212735d584a14735cd755cd838340d2120d03483a14715d5756128514d5394e))
                                            _ _ low high
                                          decide +kernel
                                      · refine divideBox _ _ 5 3 ?_ ?_
                                        · refine divideBox _ _ 6 3 ?_ ?_
                                          · intro low high
                                            apply search_boxes x _ leaf valid (branch 546 (branch 543 (branch 542 (branch 544 (branch 533 (branch 537
                                              (branch 536 (readBlock
                                              0x21586e171e2121e2143ca101e20f0820c3ca0b3c82085cf284878850f28420f0820c1e0f2830f23ca1b8487885c78852100820f0820c3c8208407883c201e2121e217850f2830f2840781e2148402008020)
                                              (readBlock 0x21586e171e2121e2143ca0c3ca101e07885cf284878850f23ca1b8487885c788520c3c8781e2121e2143c878))
                                              (readBlock
                                              0x21586e173ca19848f4850f2830f282cf2082123d2143c8f285cf2866123ca143c8f23ca1b85e123d219850f2830f2844781e2143c878866123d214830f2080203d217848f2850f23c8f2))
                                              (branch 537 (branch 536 (branch 538 (readBlock
                                              0x2158487885e0f08210082111e2148882089cf23ca0b888783c878840208520f082113d02083c20082121e217852100820f082111e0208402083c201e2148402008020)
                                              (readBlock
                                              0x21584a17850f28407883e0b756273c87889cf21e2148402083c203ca101e1d585e148402083c2089cf23ca1083c2082e273c9d50820f82e0d3c820080f2852100802008212852100820f080f2840781e2148402008020))
                                              (readBlock
                                              0x21b8487885617852111e2101e2221e0f284478840783ca14842111e0203c878852101e0781e21584a17850f2840783c8f285210888203c8f23c878))
                                              (readBlock
                                              0x21b8661585e123d21182cf4850f483e0d1e0201e21488a273ca0f82cf21e07889cf23ca0f82e0d3c8f21e0f284a143d2113d14e852113d0200821285c781d214846221e0200807885617848f4852113d0f21e0f41d2198561784a143ca0f82e22834783c8f23c8f2852273c8f23c8f23c8f2)))
                                              (branch 537 (branch 536 (branch 538 (readBlock
                                              0x21285616850f48407883c208454d830f41e214840208454d3d2100821183c2053820852163d2100802085a101e20f080780821585a1484020830f283c2082cf2082100820f0821182d4e080f2852100820f080208402008216852100820f080208402008020)
                                              (readBlock 0x21685614848f284020830f2082128407883e0c3c8203ca1083c201e0f284a143c87808212852100802008020))
                                              (readBlock
                                              0x21b84a14858f43d216856101e2111e0f21e07885a158520c3ca10844783c8f28420c1e0783c87808214848f23c878))
                                              (readBlock
                                              0x21986e1585a14848f4830f282cf20821283e115360b534f2844f43ca0f82e0c4414e4411084a143d14e08212850f43d020852123c8f23ca14848f43c8f4)))
                                              (branch 544 (readBlock
                                              0x21a86e121e21985a171e2101e21483c200802085e148402083c201e210080200821685c781e0788661285878852100802008216852100820f08078840781e020848781e21b84a171e2141d0f48661785a1488878830781e2111e0781e0201e2121e078)
                                              (readBlock 0x21a8661b84a14840203d2101e02084020080201e0f4))) (branch 542 (branch 544 (branch 537 (branch
                                              536 (branch 538 (readBlock
                                              0x212856111e2100821783c20852220e2270807889e22080781e21483c200802084478852100820f08078840200821585e0f0821008211852220e22708078888781e214888207c4208402083c20082178402083c201e020)
                                              (readBlock
                                              0x21584a1083c208502089dd57561483c2088a27081d53ca0f82dd5754f285e0f84020850207561085020755f108212852100802008020))
                                              (readBlock
                                              0x21b84a111e21484215888381e078888381e2101e07885617846101e214888381e07885210888207c4f21e0201e21285210888203c8f23c9f1))
                                              (readBlock
                                              0x21b866128561185c788507453a17852220d20f89c201d0f283e0b889cd1e0781e14d844781d2178561183e0d888381e20b88a147342008020852220e0781e20f8522289c20755f1080f20802084a111e0741e2128522283e27081d53c8f23c9f1))
                                              (readBlock 0x21a8661b84a14840208454d082100802084020080201e14d)) (readBlock
                                              0x21b86a1984a148402084478082111e0208521008020080781d020))) (readBlock
                                              0x2208861f85a17848f2854f286e1a1e0781e21286cf41e21586e143ca0c3c8783c87886e1285c781e2178561a852111e2221e0f2844781e0781e07884a143c8f23ca1285a171e0781e07886a168521286cf43ca0c3c87884a101e0f41e0783d21b84a1a84478852220e0781e07484614888381e0781e0f2))
                                              _ _ low high
                                            decide +kernel
                                          · intro low high
                                            apply search_boxes x _ leaf valid (branch 546 (branch 543 (branch 542 (branch 544 (branch 533 (readBlock
                                              0x21a8561985cf2850f2848f2830f2082173ca123c8f286617848f2850f2830f208212850f21e020848f23ca1585cf2850f23ca123c8f2)
                                              (readBlock
                                              0x21a8661585e14841f183df1848f23ca128420f756273c9d583e0b754f23ca1083dd53c8f28521083c20080207561484a1083c2008020081d584a143c8f23ca12850f23c8f2))
                                              (readBlock 0x21a85a1985215848f28420f080f23c82084a1083078754f23c8f2080f2)) (readBlock
                                              0x21686a1285219830f23c878830781e2148420f080781e0783c820)) (readBlock
                                              0x21a8661585e0f841d5851f175610851f1754f2080203c8f2)) (readBlock 0x21685e153c8f23c8f2)) _ _ low high
                                            decide +kernel
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 543 (branch 544 (readBlock
                                            0x22587e2385a1585cf286e143ca19848f4830f2538f4848f23ca1786e123d219850f2830f21e0f2848f23ca123d0f286e1585e123d2198460b3d2143d0788520b3c8f23c8f284a143d14e53a121d07484a143c8f23ca1685e153c8743d07484a1b85c743d0f28520c3c8741e21685e153c8f23c8f2)
                                            (readBlock 0x2168561486e123d20c3c9103ca12844f43c9103d14d)) (readBlock
                                            0x21b84a1784474852220d0f21d14d8460d888743c94e3c8f2)) _ _ low high
                                          decide +kernel
                                    · intro low high
                                      apply search_boxes x _ leaf valid (readBlock
                                        0x2188922088e1f8961a85a198561b0821408212840205385886c200821485612534201621284058160588661b08020082168561986e14536125354e5354d5354d852128394d08020160208521253458160208514d53a1a8661b84a148590d082100814e8521008110080204350d)
                                        _ _ low high
                                      decide +kernel
                                  · intro low high
                                    apply search_boxes x _ leaf valid (readBlock
                                      0x218892258862086a1b1e2161e04086e171e0741d02008214838401e0781d21a86e121e0781e074) _ _ low high
                                    decide +kernel
                                · intro low high
                                  apply search_boxes x _ leaf valid (readBlock
                                    0x218892238962187e1a8661b082140820e101d586e170e0380e21b85e1983838848380e034735c508020851c575438838340d21a8661b84a110e20f0802083c20081d50e034)
                                    _ _ low high
                                  decide +kernel
                              · refine divideBox _ _ 1 5 ?_ ?_
                                · refine divideBox _ _ 0 5 ?_ ?_
                                  · refine divideBox _ _ 2 5 ?_ ?_
                                    · refine divideBox _ _ 3 2 ?_ ?_
                                      · refine divideBox _ _ 5 3 ?_ ?_
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 543 (branch 546 (branch 548 (branch 544 (branch 542 (branch 537
                                            (branch 533 (branch 532 (readBlock
                                            0x21985e1b0820e1e2140820c1e20b3ca100820f0807886c2083820850208320b3ca100802084020082178387886c788520c3ca0b3ca10080f28307882cf21e20e1e21b85020840208307808214830f208078)
                                            (readBlock 0x21985e1b0820e1e214082100820c1e02086c208382085020082178387886c7885210080781e20e1e21408078))
                                            (readBlock
                                            0x21985e1b0821583840850208402083c203ca0e102140802086c208560e08214080200821786e0e102158502084020834781e214080788560e10214840203c8f21021b838208502008020))
                                            (branch 533 (branch 532 (branch 534 (readBlock
                                            0x2198387886e0b3ca0c1e20d1e2148987889c200820f8987808078830f28520b3ca0d1002082cf23ca0e1e21b8520c3ca0b3ca0d1e0788307882cf21e214830f23c8f2)
                                            (readBlock
                                            0x21983a1b850208307882e0f53a270807889c201e214830f282cf20820c1e14e86e14830f282cf289c200820c82cf283e270814e0820b83e1108020080208520c3c8f23ca0e8520c3ca0b3c8208307808214830f23c8f2))
                                            (readBlock
                                            0x217838788661b8520d1e20c1e2261e0208347883078082148320d1e020080788520c1e0781e21983a1b8502083078080208520c898f20802008020))
                                            (readBlock
                                            0x2178561986e0e1020d83c408504082e111e0f21e21489a270820b83c201e02089c200820b83e11080200802083a141020d101d58520d100203ca0e86c780e214836261e0783c8788661b838408520d100201e0400e2158661b83a140820b83e2684420080200802085227080200802008020)))
                                            (readBlock
                                            0x21a86e190820e082178587808020866178384085a1408210080780820e08020838781e21783a1b1e07885a1986e1483478898780820d1e0201e0780820e8502008020))
                                            (branch 542 (branch 537 (readBlock
                                            0x2168661586c208502083820840200821b0820e080208561b8382085020840200820e850201e0f2838200821986c20850200820e08020)
                                            (readBlock
                                            0x2168561986e0e850208320b53a270814e82e0f53820082148311082d100820c82d10080208520c82cf20802053a1483a0c82cf2080203c94e83a14080200820e8502008020))
                                            (readBlock 0x21a86e190802008020))) (branch 542 (branch 544 (branch 533 (branch 532 (branch 534 (readBlock
                                            0x20e8661a850408307882cf2835c58404008214830f2835c51020c1e20d82cf2754f28521a1020c3c8f286a0c1e20b3c8783ca1986a14830f28402082cf283c203ca0c3ca0b3ca0d83dd53c8208520c3ca0b3c8f2830f23ca1a8520c3ca0b3c820830f23c8f2)
                                            (readBlock 0x21a8661483820830f2840200820e8307882e10080200820c82cf20802083a14080783ca0e8520c3c8f23c8f2))
                                            (readBlock
                                            0x21783a14868401021a8660c1e20d1e0201e07886a19852100820c8347808020832101e078080781e2148382008078))
                                            (readBlock
                                            0x21585e1986a14838408402083c203ca0e82e0d7160f71420834400820b83e107c5d5755d583a14101d53ca0e85040100208520e08020082148384008040))
                                            (readBlock 0x21686a1585219838208320b3c8200802083a0c8407853820080203c820)) (readBlock
                                            0x21686a1483a1710020840200820e83078100781e040))) (branch 548 (branch 544 (readBlock
                                            0x21f85a17838788561a86c78830788520b3c8783ca1b8520c3ca0b3c878830781e0f286a1b1e0781e21583a1a1e214830783c8f286a14830f282cf21e20c1e0783ca0e1e07885e0e86c78850381021586e1a852261e21008078834781e0783c878838780820e86a1b1e0781e078)
                                            (readBlock 0x21686a0e85215832101e0200802084020082148320b3c878080783c820)) (readBlock
                                            0x2168561783a14830f21020c1e0f2830f23c8f21e040))) (branch 546 (branch 548 (readBlock
                                            0x22187e1a8661b082178560e1021408210081d5838400820e0802086e17838408561408210080780820e0802083840082178661b838408560d83c40850401e21483c20080200820e85040755d5838380e20e850200802086a1b864200e0400e21a86e190802008020)
                                            (readBlock 0x21a8661485e0e10210081d50820e83440081d5101c5)) (readBlock 0x20e85e1b0e04008214840200e078))) _
                                            _ low high
                                          decide +kernel
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 543 (branch 544 (branch 542 (branch 546 (branch 548 (branch 533
                                            (branch 532 (branch 534 (readBlock
                                            0x20e8660d1e20c3ca1b82cf2852261d2273c87889e263c8781e21482cf23c8f2834788520c3ca0b3c878830781e21986e0b3ca0c3ca0d852261d2273c878898781e214898f244020830f282cf23ca1b830f282cf21e0f2)
                                            (readBlock
                                            0x21983a0c82cf2850f289d4e53a1482cf289a273c94e0820b83d4e5382086e0b830f2850f24420c850f2441103ca0e8520c3c8f23c8f2))
                                            (readBlock
                                            0x21783a0d1e21483219898741e078898740820c1e0788661b8360c1e214898741e0788520c898f2440201e0781e20e8520c898f20802008110))
                                            (readBlock
                                            0x2178560e8660d86c78850387561b852260d20b89cf20e02082e0f899cd080781e1c5834780e21b8660d82e11898741e20f89a14734f23c8f2852261d0201e20b8522689cf253910080201e0f283a0d1e0381e20e8522682e273c94e0802008110))
                                            (readBlock 0x2168561783a14830f2835c53ca0c3c8f2830f23c8f21e1c5)) (readBlock
                                            0x21785a1583a14830f2834783ca0d1e0f28520c3c8f23c8780e0f2)) (readBlock
                                            0x21785a0e83478852261d0781e20d852261d0781e0200e020)) (readBlock
                                            0x2168561986e0b831108511053a0c85110538203c8f208020)) (readBlock
                                            0x21783a1586e0d0e2148983408038714388361189838081d508020)) _ _ low high
                                          decide +kernel
                                      · intro low high
                                        apply search_boxes x _ leaf valid (branch 547 (branch 546 (branch 548 (branch 543 (branch 542 (branch 544
                                          (branch 533 (branch 532 (branch 536 (branch 537 (readBlock
                                          0x21b85e0b3ca0f0820c3ca100821489c20898f208226846221e0f23c82083c20852100820c3ca0b3c82082e0c3ca1008020840200821782cf28520c3ca100820f080f283e100820c3c8f2830f23ca14830f2840200820b830f208020)
                                          (readBlock
                                          0x21786e0b3ca0c3ca1489cf2898f20820f8462689c201e0203c87882cf2830f23ca1b82e0c3ca143c910832143c910080f2))
                                          (readBlock
                                          0x21a85e1b82cf2830f2852263ca22840203c8f289a10888783c8780820c3ca0b3c8f286e14830f282cf20820b830f2080783ca1786e0b3ca0c3c8f23c8f2))
                                          (branch 537 (readBlock
                                          0x21986e1783c20840208522208226830f20802088a0c89878080783ca100820f0802085e148402083c203ca0f840201e0780821786e1488a1008226830781e07889a0c3c87808226832221e0781e0201e020)
                                          (readBlock 0x21985e1b8520c898f288a27440200822688a2783c201e0780802083e0c88a0d89878080203c8201e0f208078)))
                                          (branch 537 (readBlock
                                          0x2198561b85e0f082100821489c20888203ca0b8362289cf21e0f20802083c20840200821783e1008214081f184214081f13c82086e1783c2084020080200821586e17852108882089a277c4783ca2289a2782cf21e0783c8f282e1089a11888783c8f2080781e0203c820)
                                          (readBlock
                                          0x2158661786e0f82e1189a0d8887889cf23ca270802089c200820d88a273c8f23c8208462689c201e0200820b8362289cf21e0f23c8783c8203c820)))
                                          (readBlock
                                          0x21a866168561b8520c442100820b4402083c2084020442148320b3c82008020852100802008210080208520c82cf208020082148311044110))
                                          (readBlock
                                          0x21a8661786e168402083c2085222080201e210080208521008020082100802085222840201e0781e21488a2689e0f080781e02008078))
                                          (readBlock
                                          0x21a866178561b83c208402085222081f10820f840207c5f183c20082100802084214888207c4201e20f89e140802008020))
                                          (readBlock
                                          0x2168561786a19852107c60c3ca0f7c4f282cf2830f27c614830f23c8f2830f23ca148420f080f23c8f28521083c200802008214841f17c5f1))
                                          (readBlock
                                          0x2168561786e0c3ca0b3ca14898f21e078830f23ca14830f23c8f28522688a0c1e0783c8781e21489a22846101e0f23c8f23c878))
                                          (readBlock
                                          0x2168561786e1982cf2830f2852263c9103ca0b3c8f2830f23ca0b830f24411089a148321f3c8781e0784422782e0d88a1189a0f880f2080f23c8f23c8f208078))
                                          _ _ low high
                                        decide +kernel
                                    · intro low high
                                      apply search_boxes x _ leaf valid (readBlock 0x21886a168661b082140802083820080208520c4402053a148311008020) _ _
                                        low high
                                      decide +kernel
                                  · intro low high
                                    apply search_boxes x _ leaf valid (readBlock 0x21886a1b864201e20e1e020838781e21008020) _ _ low high
                                    decide +kernel
                                · intro low high
                                  apply search_boxes x _ leaf valid (readBlock 0x21886a1985e1b08214080400820e0e02083a0d0e0200820f08020) _ _ low high
                                  decide +kernel
                            · intro low high
                              apply search_boxes x _ leaf valid (branch 535 (readBlock
                                0x21c8822487e238861686a15866173ca143ca0e830f27547685cf23ca148660e714f21da0e830761d876856173c8f23ca1a8661585e147160e715d5715c5715c58520e849c53c8f21d8f28520e714761d8f2851c5756168561783a14869c13ca0c1e1d58520c3c9f13c8f2705c1)
                                (readBlock 0x21c85a1a8561985cf23c8f23c8f2754f2)) _ _ low high
                              decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (readBlock
                              0x21c86220886258921685c78868783d21786c780e0383c8f2852123d0781e03885a17848f21e0f41e21885a17838781e0780e0f2) _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (readBlock
                            0x21c8622087e218962385a1585cf2850f2848f453a1786c741d07485e1b856121d20e1d0740d1cd534f23ca145354e1d2120d03485a1586e173c8f43c8741d21885a1585e0e8347482cf23ca0b3c8f2440740d0f2)
                            _ _ low high
                          decide +kernel
                    · refine divideBox _ _ 8 2 ?_ ?_
                      · refine divideBox _ _ 2 6 ?_ ?_
                        · refine divideBox _ _ 0 6 ?_ ?_
                          · refine divideBox _ _ 1 6 ?_ ?_
                            · refine divideBox _ _ 3 2 ?_ ?_
                              · refine divideBox _ _ 6 6 ?_ ?_
                                · refine divideBox _ _ 4 6 ?_ ?_
                                  · refine divideBox _ _ 5 6 ?_ ?_
                                    · refine divideBox _ _ 7 2 ?_ ?_
                                      · refine divideBox _ _ 6 3 ?_ ?_
                                        · refine divideBox _ _ 2 3 ?_ ?_
                                          · refine divideBox _ _ 5 3 ?_ ?_
                                            · intro low high
                                              apply search_boxes x _ leaf valid (branch 543 (branch 546 (branch 542 (branch 538 (readBlock
                                                0x2171e21a1e219856168386084c208487883c208442082e0c1e0f21e21308212839568442083d4e53a0e082110802085a130820e182121e2110802084c2084a0e080200821585a0e1e21384878844208a0201e2121e2111e0f284e0e082125582083a121e0201e2168387884e121e0201e020)
                                                (branch 534 (readBlock
                                                0x2161e2158661a848f684cf28387882cf2834f283e101e020082133ca0e849568347882dd5756123ca0d3c8f286a133ca123da0e1e20d3c8f284cf283a121e0f23ca1986a121e21383878834f28a0200820e1e20d1e02084e123ca0e558f284a0e1e0f21e21a8487884e0e1e0f21e0f2)
                                                (branch 533 (readBlock
                                                0x21a1e2158660e84d56849568307882d5653a1284d5683d4e82d563ca138a0f283d5e3ca0b83d4e3c8f283a13162121e0f284e121d8f23ca1983a13162121e06084e121d8201e056)
                                                (readBlock
                                                0x21a8661584a1355a0e55a101e20f559d583a1355a0b7560f5582084e280820b7582083e0b754200821284c76838780821383858080208561284c76838783da13838583c82015a158660e84d568495653a1284d565382055956))))
                                                (readBlock
                                                0x21b8687885c7884e0e0821908020866168386084878080201e21a8587884a131da171e02085e0e1e2138a0201e0200821685c7884e0e160761e2138487608078))
                                                (readBlock
                                                0x21f85e161e21b1e213848f2854f21e21586a123da0e1e0f23c87885a1a1e20e84c5886c783ca1b8487884e283c8783c8f286a1b1e213848761607884e0e160f2082178587886c781da1b8687816056))
                                                (branch 546 (branch 542 (branch 538 (branch 534 (readBlock
                                                0x2198561a082130821284420839d683c20834783ca0e082110820d82cf2080208682084c2084a110820e08078844200821584e1275a1a0820e0820d3c82086a1284478838208d078756110820e0820d1e02084a111e20e83478754f283a11080781e21384a1a3d8f2838200821a84a111e0788447808078)
                                                (readBlock
                                                0x219868208561284c20844208382053a130820e0802084c200821a84a130821584420838201e020856130820e0802008213849d608020))
                                                (branch 534 (branch 532 (readBlock
                                                0x21986a1375a1275a0e82dd5835d58a0200820b7560d83dd57542084e1275a0e75a0d3c8f284a0e75a0f758f283a0d82dd5755d53ca13849d686a0e75a0d3c8f23ca1a84a0e75a0b758f683a0d82dd5080203c8f2)
                                                (readBlock
                                                0x21984e1275a1a83820834f20802086a1283a280820f758f683e28080f63da0e8a020080203ca13848f6080f6))
                                                (readBlock
                                                0x2198561a84a1375a0e75a0f759d584e0e08228081d683a0b754200821284dd67542084a13758200821284dd675420)))
                                                (readBlock
                                                0x21b86a1108219082121e02084e1285e19080780802084a111e0781e21384a1786a19838201d8763c820838200821283a280807808020))
                                                (readBlock
                                                0x21f86e1784e12868f683a15758783ca1583a1a0802086a0d3ca111e0f23ca0e0807883a110e21a0e07884a1a844781e078844781e21384a1a838183d820838201e212844780802084e17856123ca0e834f23c8f23d8d684a0e8a20d3c8f63d8f63ca121e078)))
                                                _ _ low high
                                              decide +kernel
                                            · intro low high
                                              apply search_boxes x _ leaf valid (branch 543 (branch 542 (branch 546 (branch 534 (branch 538 (readBlock
                                                0x215866163ca133ca0e834788495e82cf284478082123ca0d3ca1183c203c8f2858f284cf283a0d1e2123c878834f21e21984e0e57a163ca123ca110802085a0e83478848f28e07853a0d1e2123ca111e07883a0d1e212844785382084a0d1e0201e21383a1618020848f23ca1683a0d1e078834781e078)
                                                (readBlock
                                                0x215858f28660e84cf2834f2848f2756133ca123c8f284cf23ca1683a133ca1983478848f21e078866133ca123c8783ca138395e3c8f2))
                                                (branch 538 (branch 536 (readBlock
                                                0x21585a1357a0e57a1283d4e8454e8a0f23ca0f53a1182d4e538f284e0e57a1257a110802083a1257a0b5782084a1183d4e5394e082138395e85a1257a11080200821683a1257a0f5786084a1183d4e3c8f208020)
                                                (readBlock
                                                0x21584e0e57a16848f2844203c82085a0e84a283ca0b5786082e283c860182128a0f21e0f2082138386008060))
                                                (readBlock
                                                0x2158661683a1357a1257a0b5794e84e123ca283c95e84a0f538f23ca0e84d5e538f283a13578f23ca0e84d5e538f2)))
                                                (readBlock
                                                0x21785a0d3ca153ca0e1e0f284e0e86e153c8783c8f283a0d1e0781e21383a1b85a15848f216058080f2848f23ca0e84a283c8783c8f2))
                                                (readBlock
                                                0x22385e1b84e0e8586084a19578780821984a163c8f285a110820d1e020082123c87884a0d1d2161d02083a16834781e078834780821383a1684872180f2848f21e20e834781e07884e1b8660e0821284420080201805e83a128a21108060180600820e1e078))
                                                (branch 542 (branch 546 (branch 538 (branch 534 (readBlock
                                                0x2138561983820848f2834f2844200820e849d6082123c8f2866128395e3ca0e080201e2158660e84a110d20d0d20b7594e836110e20b7547884420756128460d1d20f53878834f253a0d844783c82083a12834781e0781e21283a11080781e078)
                                                (readBlock 0x213866128395e844200820e080200821283a0f5782053820)) (readBlock
                                                0x21784e1583a1275a0d3c8f2848f23c8f283a1282dd63c9d53c95e)) (readBlock 0x21383a123c8f23c878)) (readBlock
                                                0x21384a0e0802008078))) _ _ low high
                                              decide +kernel
                                          · intro low high
                                            apply search_boxes x _ leaf valid (branch 547 (branch 543 (branch 546 (branch 542 (branch 538 (readBlock
                                              0x21a86420858588485884c20838580821984c2085a158386084a0f53a110820b5394e83c208442053a0e1821283c2008020856128395683d4e0820e08020082138382084a161602084420082168385884a11080f208020)
                                              (branch 537 (readBlock
                                              0x21686615838588485884c588405883e0c160201e20e162121621316078838588485884c581e21984a1584d56839568405875613158208560e84d56840580821384058080200821284c5616020)
                                              (readBlock
                                              0x21985a1583a1355a1255a0c1614e84a1355a0f538f284e0f578f253a0e84c581614e84a135594e57a0e84c5816056)))
                                              (readBlock 0x21a86e19082130805885a0e162131607815a1b84e19080588386008056)) (readBlock
                                              0x21f86a1b8385885858848581621683858848581605686e0e84c5816213848580807815858)) (readBlock
                                              0x22387e1b86a190821284c208442008213080208661284c208382008213080200821a84a198561355a0e559d55595684e0e08020081560821284e0e0805816020))
                                              (readBlock
                                              0x22387e2086e1984e0e57a168555e8442053a1257820856168395e83d4e84a115394e53a0e8495e0814e83a125786053a1383a161802084a11080f20820e84a2882d4e180601814e8661585a0e84d5e8495e53a138495e5394e5795e55a1384a0e578200814e84e0e180201820e84c58160f2))
                                              _ _ low high
                                            decide +kernel
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 544 (branch 543 (branch 547 (branch 542 (branch 546 (branch 534
                                            (readBlock
                                            0x216854f2868768387684cf2848761e21584cf286a19848f683a0b7560d3ca0f755d582cf2834f2756123da0e82cf23c8f28660e8495682dd53ca123c8f23ca13848f283a1a1d8f2834f20821a8487683a0d3c8203c8f2)
                                            (branch 533 (readBlock
                                            0x21a85619848768387684c768307682e101d8f21e2121da0e1da131d878848768387684c761e21583a1984d56849568307653a13158f28661284d56830763ca13830763c8f23ca0e84c561d8f2)
                                            (readBlock
                                            0x21586a1984a1355a0e55a101d9d583a1355a0b7542084e0b758207561284c761d9d583a13559d575a1284c761d856)))
                                            (readBlock 0x21685e153ca133c87686a121da131d87815a1784e153c876848f63c856)) (readBlock
                                            0x22385a178487686876838761da1a84876838761d85685e1284c761da13838763c82015876)) (readBlock
                                            0x21f88e1785a153ca0e84cf2834f23ca133c8f28560e84cf2848f23ca133c8f23ca1683a158661355a125594e5595684e123c8f23c9563ca0e84e123c8761d8f2))
                                            (readBlock
                                            0x21f88e2485e1584e1275a1a865d6834f27560e758f28661a849d682dd583a0d755d575612839d63c9d584a0e758f67561384a1a3d8f283a0d3c8203ca1283a2883dd53d8f63d9d58561986a1284dd6839d675613839d6755d5759d655a1383a12758f23c9d584e123d8f23da1284c761d820))
                                            (readBlock
                                            0x2208922387e1a85a0e15a1215a158661015a13159561585684a1315a0e559d583a13559567561683a1315a125594e84a1355956539568485615a0e1585683a135594e53a1284d56755d5))
                                            _ _ low high
                                          decide +kernel
                                      · refine divideBox _ _ 2 3 ?_ ?_
                                        · refine divideBox _ _ 1 3 ?_ ?_
                                          · intro low high
                                            apply search_boxes x _ leaf valid (branch 542 (branch 548 (branch 546 (branch 547 (branch 538 (branch 534
                                              (branch 532 (readBlock
                                              0x21985a1a0820e1e2130820d1e20b3ca110820f08078868208382084c208360b3ca11080208442008216838788687884e0d3ca0b3ca11080f28347882cf21e20e1e21a84c20844208347808213834f208078)
                                              (readBlock 0x21985a1a0820e1e213082110820d1e020868208382084c2008216838788687884e11080781e20e1e21308078))
                                              (readBlock
                                              0x21985a1a082158386084c208442083c203ca0e1821308020868208560e08213080200821686a0e1821584c2084420830781e213080788560e18213844203c8f21821a8382084c2008020))
                                              (branch 534 (branch 532 (branch 533 (readBlock
                                              0x2198387886a0b3ca0d1e20c1e213898788a0200820f8987808078834f284e0b3ca0c1802082cf23ca0e1e21a84e0d3ca0b3ca0c1e0788347882cf21e213834f23c8f2)
                                              (readBlock
                                              0x21983a1a84c208347882e0f75628080788a0201e213834f282cf20820d1e1d586a13834f282cf28a0200820d82cf283e28081d50820b83e10080200802084e0d3c8f23ca0e84e0d3ca0b3c8208347808213834f23c8f2))
                                              (readBlock
                                              0x216838788661a84e0c1e20d1e2261e0208307883478082138360c1e0200807884e0d1e0781e21983a1a84c20834780802084e0d898f20802008020))
                                              (readBlock
                                              0x2168561986a0e1820c83c6084c6082e101e0f21e21389a280820b83c201e0208a0200820b83e10080200802083a131820c1814e84e0c180203ca0e8687816213832261e0783c8788661a8386084e0c180201e060162158661a83a130820b83e2684020080200802084e28080200802008020)))
                                              (branch 534 (branch 532 (branch 533 (readBlock
                                              0x20e8661b84c608347882cf28315e8446008213834f28315e1820d1e20c82cf2538f284e1b1820d3c8f286e0d1e20b3c8783ca1986e13834f28442082cf283c203ca0d3ca0b3ca0c83d4e3c82084e0d3ca0b3c8f2834f23ca1b84e0d3ca0b3c820834f23c8f2)
                                              (readBlock 0x21b8661383820834f2844200820e8347882e11080200820d82cf20802083a13080783ca0e84e0d3c8f23c8f2))
                                              (readBlock
                                              0x21683a1386c601821b8660d1e20c1e0201e07886e1984e110820d8307808020836111e078080781e2138382008078))
                                              (readBlock
                                              0x21585a1986e13838608442083c203ca0e82e0c57a0f57820830600820b83e114414e4411083a131814e3ca0e84c601802084e0e08020082138386008060)))
                                              (branch 547 (readBlock
                                              0x21785a0e1e21586e1a1e20d1e21382cf21e0f286a13834f282cf21e20d1e0783ca1b868781e0788560e86c7884e0d1e0f23ca1b84e0d3ca0b3c878834781e0f2838781e21683a1a1e213160608561a86e1389878844201e20c1e0781e0f21e20e1e020)
                                              (readBlock 0x2178561683a13834f21820d1e0f2834f23c8f21e060))) (branch 546 (branch 547 (branch 534 (branch
                                              532 (branch 533 (readBlock
                                              0x20e8660c1e20d3ca1a82cf284e261da283c8788a2263c8781e21382cf23c8f28307884e0d3ca0b3c878834781e21986a0b3ca0d3ca0c84e261da283c878898781e213898f27c420834f282cf23ca1a834f282cf21e0f2)
                                              (readBlock
                                              0x21983a0d82cf284cf28a1d57561382cf289a283c9d50820b83dd57542086a0b834f284cf27560d84cf2755f13ca0e84e0d3c8f23c8f2))
                                              (readBlock
                                              0x21683a0c1e21383619898761e078898760820d1e0788661a8320d1e213898761e07884e0d898f27c4201e0781e20e84e0d898f208020081f1))
                                              (readBlock
                                              0x2168560e8660c8687884c5853a1a84e2615a0b8a0f21602082e0f89956080781e15e830781621a8660c82e10898761e20f89a13558f23c8f284e261d8201e20b84e268a0f2755f1080201e0f283a0c1e0581e20e84e2682e283c9d508020081f1))
                                              (readBlock 0x2178561683a13834f28315e3ca0d3c8f2834f23c8f21e15e)) (readBlock
                                              0x21685e1583a13834f2830783ca0c1e0f284e0d3c8f23c878160f2))) (readBlock
                                              0x2258922386e1a838208642085a171e0200820e858600821985a1308211080780807885a0e868781e21a8661784e0c1e2261e02083078080201e07883a13080200820e86e1a1e0781e07885e1b84e0e85860082110802083a0d1e0601e0781821683a178307884e261d8781e05883213898761e07808020))
                                              _ _ low high
                                            decide +kernel
                                          · intro low high
                                            apply search_boxes x _ leaf valid (branch 542 (branch 548 (branch 546 (branch 547 (branch 538 (readBlock
                                              0x217866158682084c2083820844200821a0820e080208561a8382084c20844200820e84c201e0f283820082198682084c200820e08020)
                                              (readBlock
                                              0x2178561986a13835f182df1838200820e8360b75628081d582e0f754200820d82dd50802084e0d82cf2080207561383a0d82cf2080203c9d583a13080200820e84c2008020))
                                              (readBlock 0x21786e1584e19838208360b3c8200802083a0d8447875420080203c820)) (readBlock
                                              0x21b85e0e84e15844200802084420082138360b3c87808078080f2)) (readBlock
                                              0x2178561986a0b835d584df17560d84df1754203c8f208020)) (readBlock 0x21b86a190802008020)) _ _ low high
                                            decide +kernel
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 548 (branch 547 (readBlock
                                            0x22088e1f86e198682085a1308215838608442053860838200821a85a0e1821584c20844201e020838200820e1802085a1986a0e182158320f182131807884e0f080200802083a131814e53a0e1605883a13080200821b86a19080581805883a16868581802084e11080581e21b86a190802008020)
                                            (readBlock 0x21b8661385a0e18211081100820e83060081101815e)) (readBlock
                                            0x21683a1a8305884e26158201615e83210898580814e08020)) _ _ low high
                                          decide +kernel
                                    · intro low high
                                      apply search_boxes x _ leaf valid (readBlock
                                        0x21c8862587e238821786e15866163ca133ca0e834f253874858f23ca138660e578f21d20e834741d074856163c8f23ca1b8661585a1357a0e5794e5795e5795e84e0e8495e3c8f21d0f284e0e578741d0f284d5e53a178561683a1386d603ca0d1e14e84e0d3c9103c8f258160)
                                        _ _ low high
                                      decide +kernel
                                  · intro low high
                                    apply search_boxes x _ leaf valid (readBlock
                                      0x21c886208922585e161e21b1e0f685a1a1e058160f23ca13848f61e0781621785a0e1e0781e058) _ _ low high
                                    decide +kernel
                                · intro low high
                                  apply search_boxes x _ leaf valid (readBlock
                                    0x21c8861f8822488e17856163ca133ca123d9d585a1a1d8761da1686a1584876838761d856559563c8f284dd6754768485615a178561683a0c1da0b3c8f282cf23c9d51d856)
                                    _ _ low high
                                  decide +kernel
                              · refine divideBox _ _ 6 5 ?_ ?_
                                · refine divideBox _ _ 4 5 ?_ ?_
                                  · refine divideBox _ _ 5 5 ?_ ?_
                                    · refine divideBox _ _ 7 2 ?_ ?_
                                      · refine divideBox _ _ 2 3 ?_ ?_
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 548 (branch 542 (branch 543 (branch 547 (branch 546 (branch 534
                                            (branch 538 (branch 536 (readBlock
                                            0x21586a161e2121e2133ca111e20f0820d3ca0b3c820858f28487884cf28460f0820d1e0f2834f23ca1a848788587884e110820f0820d3c8208447883c201e2121e21684cf2834f2844781e2138442008020)
                                            (readBlock 0x21586a161e2121e2133ca0d3ca111e078858f28487884cf23ca1a848788587884e0d3c8781e2121e2133c878))
                                            (readBlock
                                            0x21586a163ca19848f684cf2834f282cf2082123da133c8f2858f2866123ca133c8f23ca1a85a123da1984cf2834f2840781e2133c878866123da13834f2080203da16848f284cf23c8f2))
                                            (branch 538 (branch 536 (branch 537 (readBlock
                                            0x2158487885a0f08211082101e213888208a0f23ca0b888783c8788442084e0f082103d82083c20082121e21684e110820f082101e0208442083c201e2138442008020)
                                            (readBlock
                                            0x21584a1684cf28447883e0b53a283c8788a0f21e2138442083c203ca111e14e85a138442083c208a0f23ca1183c2082e283c94e0820f82e0c3c820080f284e11080200821284e110820f080f2844781e2138442008020))
                                            (readBlock
                                            0x21a848788561684e101e2111e2221e0f284078844783ca13846101e0203c87884e111e0781e21584a1684cf2844783c8f284e11888203c8f23c878))
                                            (readBlock
                                            0x21a8661585a123da1082cf684cf683e0c1e0201e21388a283ca0f82cf21e0788a0f23ca0f82e0c3c8f21e0f284a133da103d9d584e103d82008212858781da13842221e0200807885616848f684e103d8f21e0f61da198561684a133ca0f82e22830783c8f23c8f284e283c8f23c8f23c8f2)))
                                            (readBlock
                                            0x21785a153ca123ca1a86c781e0788561a848f686e133ca0d3c8783ca121e0f2848781e21a84a161e07886e1585a1384078888783ca101e0781e0781e21284cf23c8f2))
                                            (branch 546 (branch 534 (readBlock
                                            0x21b85619858f284cf2848f2834f2082163ca123c8f286616848f284cf2834f20821284cf21e020848f23ca15858f284cf23ca123c8f2)
                                            (readBlock
                                            0x21b8661585a1284cf28460f53a283c94e83e0b538f23ca138451083d103ca1183d103c8f284e1183c200802053a1384a1183c20080200814e84a133c8f23ca1284cf23c8f2))
                                            (readBlock 0x21785a153c8f23c8f2))) (branch 546 (branch 547 (branch 538 (branch 536 (branch 537 (readBlock
                                            0x2128561784cf68447883c20841d6834f61e21384420841d63da110821083c207542084e173da110802085e111e20f080780821585e1384420834f283c2082cf2082110820f0821082dd5080f284e110820f08020844200821784e110820f080208442008020)
                                            (readBlock 0x21785613848f284420834f2082128447883e0d3c8203ca1183c201e0f284a133c8780821284e110802008020))
                                            (readBlock
                                            0x21a84a1385cf63da17856111e2101e0f21e07885e1584e0d3ca11840783c8f28460d1e0783c87808213848f23c878))
                                            (readBlock
                                            0x21986a1585e13848f6834f282cf20821283e1075a0b758f2840f63ca0f82e0d7c5d5755d584a133d9d50821284cf63d82084e123c8f23ca13848f63c8f6))
                                            (readBlock 0x21b85e1984e15848f28460f080f23c82084a1183478538f23c8f2080f2)) (readBlock
                                            0x21b85e1384a1a3d8f2834f21e212844783d8781e0f6))) (branch 543 (branch 547 (readBlock
                                            0x22386e1a8487886617858788447884e0f080200821684e110820f08078844200802085e161e0781e21984a171e213844200802085e138442083c201e2111e078082121e07886a128587884c763da1985a1784e221e20d1e078840781e07808078848781e21285e161e0781e078)
                                            (readBlock 0x21b85e1284e198460d1e0f23c878834781e2138460f080781e078080f2)) (readBlock
                                            0x21b8661a84a13844203da111e02084420080201e0f6))) (branch 542 (branch 543 (readBlock
                                            0x22488e17856163ca1a866123da133ca0d3c9d5848f63ca123c8f285a1a848f6866133ca0d3c8783ca123c8f2848f63ca1a85616848f68661082cf684cf61e21382cf23c8f23ca1284cf6755d5848761da1284cf23c8f285e16854f21d8f61da1785a153c8f23c8f2)
                                            (readBlock 0x2178561386a123da0d3c9d53ca12840f63c9d53d9d6)) (readBlock 0x21286a161d8f63ca13834f21d878))) _
                                            _ low high
                                          decide +kernel
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 548 (branch 547 (branch 546 (branch 542 (branch 543 (branch 538
                                            (branch 536 (branch 537 (readBlock
                                            0x212856101e2110821683c2084e2216228080788a222080781e21383c20080208407884e110820f08078844200821585a0f082110821084e221622808078888781e21388820440208442083c20082168442083c201e020)
                                            (readBlock
                                            0x21584a1183c2084c208a14e53a1383c2088a280814e3ca0f82d4e538f285a0f8442084c204421184c20441100821284e110802008020))
                                            (readBlock
                                            0x21a84a101e21384615888581e078888581e2111e07885616842111e213888581e07884e1188820440f21e0201e21284e11888203c8f23c910))
                                            (readBlock
                                            0x21a86612856108587884c767561684e2215a0f8a0201d8f283e0b889561e0781e1d6840781da168561083e0c888581e20b88a13558200802084e22160781e20f84e228a02053910080f20802084a101e0761e21284e2283e280814e3c8f23c910))
                                            (readBlock 0x21b8661a84a1384420841d6082110802084420080201e1d6)) (readBlock
                                            0x21a86e1984a138442084078082101e02084e1108020080781d820)) (readBlock
                                            0x21a86e128407884e22160781e21084e22160781e0781d8f2)) (readBlock
                                            0x21b8661585a0f8451084d1053a1184d10538f2080203c8f2)) (readBlock
                                            0x21a84a1985a101da13888563c876758768420c888763c9d53c8f2)) _ _ low high
                                          decide +kernel
                                      · intro low high
                                        apply search_boxes x _ leaf valid (branch 544 (branch 542 (branch 543 (branch 548 (branch 546 (branch 547
                                          (branch 534 (branch 532 (branch 536 (branch 538 (readBlock
                                          0x21686a0b3ca0f0820d3ca11082138a020888203ca26842221e0f23c82082cf284e0d3ca110820f080f283e110820d3c8f2834f23ca1a83c2084e110820d3ca0b3c82082e0d3ca11080208442008213834f2844200820f844203c8f2)
                                          (readBlock
                                          0x21686a0b3ca0d3ca138a0f2898f20820f842268a0201e0203c87882cf2834f23ca1a82e0d3ca133c9f1836133c9f1080f2))
                                          (readBlock
                                          0x21b85a1a82cf2834f284e263ca22844203c8f289a11888783c8780820d3ca0b3c8f286a13834f282cf20820b834f2080783ca1686a0b3ca0d3c8f23c8f2))
                                          (branch 538 (readBlock
                                          0x21986a1683c208442084e2208226834f20802088a0d89878080783ca110820f0802085a138442083c203ca0f844201e0780821686a1389a0d3ca22844201e07888a110807808226836221e0781e0201e020)
                                          (readBlock 0x21985a1a84e0d898f288a287c4200822688a2883c201e0780802083e0d88a0c89878080203c8201e0f208078)))
                                          (branch 538 (readBlock
                                          0x2198561a85a0f08211082138a020888203ca0b832228a0f21e0f20802083c20844200821683e11082130811084613081103c82086a1683c2084420080200821586a1684e118882089a28440783ca2289a2882cf21e0783c8f282e1189a10888783c8f2080781e0203c820)
                                          (readBlock
                                          0x2158661a85a0b83e0c88a10898788a020082283c8f28a0f23ca1089a280802008020832228a0f21e0f23ca0f842268a0201e02008078080f23c820)))
                                          (readBlock
                                          0x2178561b8661684e114420d3ca0f440f282cf2834f2442138460f080f23c8f284e0d3c8f23ca0d3c8f284e1183c2008020082138451044110))
                                          (readBlock
                                          0x2178561a85a1b834f282cf284e263c8781e20d3c8f284e0d3c8f23ca0d3c8f284e26834f21e0781e21389a228a20b3c8781e0f23c878))
                                          (readBlock
                                          0x2178561a8661682cf2834f284e263c9f13ca0b834f27c5f182cf23ca0d3c8f283613898f27c4781e20b8a2133c8f21e020))
                                          (readBlock
                                          0x21b8661a85e1584e0d7c6110820b7c42083c20844207c613844200802084420082138360b3c8200802084e0d82cf20802008213835f17c5f1))
                                          (readBlock
                                          0x21b8661a85a110820f0821388820080788442008213844200802084e2289a111e078080781e21388a268320d1e0200802008078))
                                          (readBlock
                                          0x21b8661a85a1583c208442084e22081100820f08020844200820f844204411088a1384623080781e0204422883e1089a0c88a0b8942008020080200802008020))
                                          _ _ low high
                                        decide +kernel
                                    · intro low high
                                      apply search_boxes x _ leaf valid (readBlock 0x21c85e1b856163ca133c8f2848f23c8f284e11440f253a13845103c8f2) _ _
                                        low high
                                      decide +kernel
                                  · intro low high
                                    apply search_boxes x _ leaf valid (readBlock 0x21c85e16854f21e2121e0f2848781e20d3c8f2) _ _ low high
                                    decide +kernel
                                · intro low high
                                  apply search_boxes x _ leaf valid (readBlock 0x21c85e1586a163ca133c8f63ca121d8f284a101d8f23ca0b3c8f2) _ _ low high
                                  decide +kernel
                            · intro low high
                              apply search_boxes x _ leaf valid (branch 539 (readBlock
                                0x2188962188e1f8921b85e198561a08213082128442075438868200821385612758200e212844380e0388661a08020082178561986a1375a12759d5759d6759d684e12839d6080200e02084e12758380e02084dd67561b8661a84a1385df608211081d584e11081f1080207d9f6)
                                (readBlock 0x21886e178661586820080200802075420)) _ _ low high
                              decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (readBlock
                              0x21887225892208861b8687885c781821a858781d8760802084e0e180781e07686e1a83820080601e21c86e1a848781e0781d820) _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (readBlock
                            0x2188722588e248821f86e198682084c208386053a1a858581605886a168660e16212160581595655820082135794e1620e1585686e1985a1a08060080581621c86e1986a128405883c200820f080204405815820)
                            _ _ low high
                          decide +kernel
                      · refine divideBox _ _ 1 5 ?_ ?_
                        · refine divideBox _ _ 2 5 ?_ ?_
                          · refine divideBox _ _ 0 5 ?_ ?_
                            · refine divideBox _ _ 5 5 ?_ ?_
                              · refine divideBox _ _ 4 5 ?_ ?_
                                · refine divideBox _ _ 6 5 ?_ ?_
                                  · refine divideBox _ _ 3 2 ?_ ?_
                                    · refine divideBox _ _ 7 2 ?_ ?_
                                      · intro low high
                                        apply search_boxes x _ leaf valid (branch 548 (branch 547 (branch 543 (branch 544 (branch 546 (branch 542
                                          (branch 538 (readBlock
                                          0x21a1e2171e21985616838788487882e0f53a0c1e07883e111e0781e21283e0b53a111e14e8447853a0e82e0f538200802085a121e20e1e020082168560e1e2121e0781e078)
                                          (branch 534 (readBlock
                                          0x2161e2158661a838788487882e0f7560d1e07883e101e0781e20e82e0f7560d1e1d5834787561283e0b754783c8f286a0e1e2121e0781e21a866121e20e1e0201e078)
                                          (readBlock
                                          0x21a858788661584a0f82dd584078756101e1d583a0b83dd508020080201e2168561983a0b83d4e8307853a0c1e14e84a0f82d4e1e0f23c8781e14e)))
                                          (readBlock 0x21a86c7885878848781e21b85c78848781e078)) (readBlock
                                          0x21f85a171e21a1e20e1e07885e1b1e20e1e0781e21685c781e078)) (branch 546 (branch 542 (branch 537 (branch 538
                                          (readBlock
                                          0x2198561684078848788387883e0b53a1108020844201e2128407883e0b53a110802084478082101e20e844200802085a101e2121e20e1e0208407808216856101e2121e20e1e078840781e2101e020)
                                          (readBlock
                                          0x2168661584a101e20f82d4e83a0c1e14e1e20e82e0c1e14e1e0788407883a0c1e14e53a101e078840781e2128407853820))
                                          (readBlock
                                          0x2198561b85a1283e0b53a0e53a115394e83a0b53a278a14e1807882e115394e1e20f82d4e83a0c5382053a0e82e0c538201814e84a0f82d4e0814e0820e84a0f82d4e5394e5394e84a0f83a2718078080601820e84a278a20b538781e07818078))
                                          (readBlock 0x21a86e1985a101e2121e060080781e060)) (readBlock 0x21a85a1b84078838781e0781e078))) (branch 544
                                          (branch 546 (branch 542 (branch 538 (branch 537 (readBlock
                                          0x2198561784478848788387883e0b7561008020840201e2128447883e0b756100802084078082111e20e840200802085e111e2121e20e1e0208447808217856111e2121e20e1e078844781e2111e020)
                                          (readBlock
                                          0x2178661584a111e20f82dd583a0d1e1d51e20e82e0d1e1d51e0788447883a0d1e1d5756111e078844781e2128447853820))
                                          (readBlock
                                          0x2198561a85e1283e0b7560e75610755d583a0b7562889dd51007882e10755d51e20f82dd583a0d754207560e82e0d75420101d584a0f82dd5081d50820e84a0f82dd5755d5755d584a0f83a2810078080401020e84a2889e0b754781e07810078))
                                          (readBlock 0x21b86a1985e111e2121e040080781e040)) (readBlock 0x21b85e1a84478838781e0781e078)) (readBlock
                                          0x21a86e1985612844208402053a1008020080207554e))) (branch 544 (branch 543 (branch 542 (branch 546 (branch 534
                                          (branch 533 (readBlock
                                          0x2158661b83478838788487882e0f53a0c3c878830781e20e8347882e0f53a0c3c8f2830783ca0d1e212830f23c8f286e0d1e20e1e2121e0f2834783ca1b8660d1e20e1e2121e078834781e20d1e078)
                                          (readBlock
                                          0x21b8561983a0d1e20b83d4e84a111e14e1e21283e111e14e1e0788347884a111e14e53a0d1e078834781e20e83478538f2))
                                          (readBlock
                                          0x2158661686e0e82e0f53a1253a0c5394e84a0f53a2889d4e3d07883e0c5394e1e20b83d4e84a11538f253a1283e11538f23d14e83a0b83d4e3c94e3ca1283a0b83d4e5394e5394e83a0b84a283d0783c8f43d21283a2889e0f538781e0783d078))
                                          (readBlock 0x21785a1586e0d1e20e1e0f43c8781e0f4)) (readBlock 0x21786e1683478848781e0781e078)) (readBlock
                                          0x21786e198560e836111e2121e1d584a111e1cd736128460d1e14e734781e0787554e)) (readBlock
                                          0x2158661686e0f82d4e84a0e5394e53a0b83a125394e5394e5394e5394e))) (branch 543 (branch 544 (branch 547 (branch
                                          542 (branch 546 (branch 533 (branch 534 (readBlock
                                          0x2158661a83078838788487882e0f7560d3c878834781e20e8307882e0f7560d3c8f2834783ca0c1e212834f23c8f286a0c1e20e1e2121e0f2830783ca1a8660c1e20e1e2121e078830781e20c1e078)
                                          (readBlock
                                          0x21a8561983a0c1e20b83dd584a101e1d51e21283e101e1d51e0788307884a101e1d57560c1e078830781e20e83078538f2))
                                          (readBlock
                                          0x2158661786a0e82e0f756127560d755d584a0f756278a1d53d87883e0d755d51e20b83dd584a10754f27561283e10754f23d9d583a0b83dd53c9d53ca1283a0b83dd5755d5755d583a0b84a273d8783c8f63da1283a278a20f754781e0783d878))
                                          (readBlock 0x21685e1586a0c1e20e1e0f63c8781e0f6)) (readBlock 0x21686a1783078848781e0781e078)) (readBlock
                                          0x21685e158660e834f2830f253a0c3c8f23c878539d5)) (readBlock
                                          0x21686a15866128420c1e20e1e1d583a0c1e15655a0e832101e14e558781e078539d5)) (readBlock
                                          0x2158661786a0b83dd583a12755d57560f84a0e755d5755d5755d5755d5))) _ _ low high
                                        decide +kernel
                                      · intro low high
                                        apply search_boxes x _ leaf valid (branch 543 (branch 544 (branch 542 (branch 546 (branch 547 (branch 548
                                          (branch 533 (branch 534 (readBlock
                                          0x2158661a86c78838788307882e0d1e20f840783c878834780821b838788347882e0c1e20f844783c878830780820e1e20b834f23c87886e1a1e20e1e20d1e0f286a0e1e20c1e0f21e21a86c788660e1e20c1e0781e21b8660e1e20d1e0781e078)
                                          (readBlock
                                          0x2158661a86e0e1e2101e20f82e0c1e21108020844200820c1e020838788320b83e101e0781e0780821b83a0c1e20b83e111e14e0802082e0c83d4e538200814e86a1b83878840781e0781e21a86e198387884078080781e060))
                                          (readBlock
                                          0x2178561986e1a838788447883e0b83478840200821008020834780820e1e20d82e0f844781e0781e02086a0e8347882e0f84078754200820b8360f755d5080207561b86a0e1e2111e0781e07886e1a8660e1e2111e0201e078102158661a86e0e1e210080200802008020))
                                          (readBlock
                                          0x216856178661a83a0c1e20b8347883e101e1d51e20d1e0788320b3ca0d1e07882e0d3c9d57560e830783c8f283a0c1e0783ca0e830781e07883a0c1e0781e20e82e0d83dd5755d5755d5))
                                          (readBlock
                                          0x21b85e1585a1983a0d1e20b8307883e111e14e1e20c1e0788360b3ca0c1e07882e0c3c94e53a0e834781e0f283a0d1e0781e20e834781e07883a0b8320f5394e5394e53a0e8360c1e0f23c8f2))
                                          (readBlock 0x21a86e1685c78838781e20e1e078838783ca0e1e0f2)) (readBlock
                                          0x21a86e1985e161e20e1e0208387808078838781e20e1e078)) (readBlock
                                          0x21a86e1985616838608402083e110814e0821008020840201820e840781807883a0c84078538201e20e82e0c83d4e180201814e))
                                          (readBlock
                                          0x21786e1a86615838408442083e10081d5082110804083a111e0401e20e836111e1d50807883a0b8360f75440080407561108020))
                                          _ _ low high
                                        decide +kernel
                                    · intro low high
                                      apply search_boxes x _ leaf valid (branch 539 (branch 547 (branch 548 (branch 546 (branch 542 (branch 543
                                        (branch 544 (branch 538 (branch 537 (readBlock
                                        0x2198561685c78848788407883e110820b8307808078844781e217848788447883e100820b8347808078840781e2121e20f840200802085a171e2121e2101e02085e121e2111e0200821685c78856121e2101e0781e217856121e2111e0781e078)
                                        (readBlock
                                        0x2198561785a121e20d1e20b83e111e20c3c8f2830f21e2111e0f2848788460f82e0d1e0201e0783ca1684a111e20f82e0c1e14e1e0f283e1182d4e538f23c94e85e1684878834781e0781e21785a1584878834783c8781e0f4))
                                        (readBlock
                                        0x21a8661585a17848788307882e0f84078834f23ca0d3c878840783ca121e21083e0b83078080781e0f285e128407883e0b83478754783ca0f8420b755d53c8f27561685e121e20c1e0781e07885a17856121e20c1e0f21e0783da198561685e121e20c3c8f23c8f21e0f2))
                                        (readBlock
                                        0x21a8661b8561684a101e20f8442082e0c1e14e1e2111e0788420f082111e07883e110814e53a12840780802084a101e02008212840781e07884a101e0781e21283e1182d4e5394e5394e))
                                        (readBlock
                                        0x21786e1986a1584a111e20f8402082e0d1e1d51e2101e0788460f082101e07883e10081d575612844780802084a111e0781e212844781e07884a0f8420b755d5755d575612846101e02008020))
                                        (readBlock 0x21685e1b86878848781e2121e07884878082121e020)) (readBlock
                                        0x21685e1586a1b1e2121e0f2848783c878848781e2121e078)) (readBlock
                                        0x21685e158661a848f6830f282e0d3c9d53ca0c3c8f2830f23da12830783d87884a1083078754781e21283e1082dd53d8f23d9d5))
                                        (readBlock
                                        0x21b85e1685619848f4834f282e0c3c94e3ca0d3c8f484a0d1e0f41e2128460d1e14e1e07884a0f8460b538f43c8f453a0d3c8f2))
                                        (branch 543 (branch 544 (branch 542 (branch 546 (branch 547 (branch 548 (branch 532 (branch 536 (branch 534
                                        (branch 533 (readBlock
                                        0x21a86e0b83e0c3ca0d3ca100821108020830f2834f284211080200820f84420840208320d3c82008210844208320d3c8781e20c834f21e07882e0d3ca0c3c82083e108360c3c8201e0f23ca1b82e0c3ca0d3c82083e118320d3c8201e0f23c8f2)
                                        (readBlock 0x21b86a0f84020844200820b83610844200807808020081d5)) (readBlock
                                        0x21a86e1683e11082100802082e0c84610080201e0200802008110)) (readBlock
                                        0x21685e1b86a0b830f2834f21e20c834f21e0783c8f21e078)) (readBlock
                                        0x21986a1b85e1683e10082110807884211080781e020080781e078)) (readBlock 0x20b834f23c8f2)) (readBlock
                                        0x20b830f23c8f2)) (readBlock 0x20b830f21e078)) (readBlock 0x20f8402008078)) (readBlock 0x20f8442008020))
                                        (readBlock 0x20f8402008020))) _ _ low high
                                      decide +kernel
                                  · intro low high
                                    apply search_boxes x _ leaf valid (readBlock
                                      0x2188721685e1586a198307683a0b83dd5834f21da121d9d582e0f754f63da0c1d8f683a0c3c8f23ca0c1d87683a0c1d9d51da0b83dd5755d583a0c1e1d53ca0c3c8f6)
                                      _ _ low high
                                    decide +kernel
                                · intro low high
                                  apply search_boxes x _ leaf valid (readBlock 0x21c8621685e1a1e0781e0781e078) _ _ low high
                                  decide +kernel
                              · intro low high
                                apply search_boxes x _ leaf valid (readBlock
                                  0x2188721785a1586e198347483a0b83d4e830f21d2121d14e82e0f538f43d20d1d0f483a0d3c8f23ca0d1d07483a0d1d14e1d20b83d4e5394e83a0d1e14e3ca0d3c8f4)
                                  _ _ low high
                                decide +kernel
                            · intro low high
                              apply search_boxes x _ leaf valid (readBlock 0x2188721a86e161e0781e0781e078) _ _ low high
                              decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (readBlock
                              0x21c8621a86e1985a158405884a0f82d4e844201620e1614e83e0b53860182101606084a1008020082101605884a101614e1620f82d4e5394e84a101e14e0821008060)
                              _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (readBlock
                            0x21c8621b86a1985e158443884a0f82dd5840200e20e0e1d583e0b75440102110e04084a1108020082110e03884a110e1d50e20f82dd5755d584a111e1d50821108040)
                            _ _ low high
                          decide +kernel
                  · refine divideBox _ _ 1 5 ?_ ?_
                    · refine divideBox _ _ 2 5 ?_ ?_
                      · refine divideBox _ _ 0 5 ?_ ?_
                        · refine divideBox _ _ 3 2 ?_ ?_
                          · refine divideBox _ _ 8 2 ?_ ?_
                            · intro low high
                              apply search_boxes x _ leaf valid (branch 541 (branch 567 (branch 566 (branch 568 (branch 543 (branch 544 (branch 542
                                (branch 546 (branch 547 (readBlock
                                0x22585a1585cf18642083820850f186c203c60e082190821784c20850200802085e15864208382084cf1868203c60e0821908020864208560e0802008217856163c6143c60e84cf1081f185a0e8502084cf1082143c6137c4208502008216856143c60e86a19080f13c6133c420850200821408020)
                                (readBlock
                                0x22585a1585cf184cf183a143c4204421783a13082143c42084cf185110082130802085e1584cf183a1b864203c4f1850f1082130802084c2008216856173c4f13c4f1))
                                (readBlock
                                0x2258920e85a17854f184c20850200821a0802085e1b0802008216856173c6143c6133c42085e133c6143c42044217856133c6143c4207c4f185e15858f13c4f13c616856173c4f13c4f1))
                                (readBlock 0x223892258382086c20868200821484c200820e0802084e1408020838200820e85a1a080200821308020)) (readBlock
                                0x21f88e25892168642086c200821b0802085a13851104411008216852133c420838200802085a0e868203c6143c4200821a08020)) (readBlock
                                0x22187e238922585e190821a080208682008217852137c5f17c42085e13850f10820e080200821783a1b080f184cf10802086c200821b08020))
                                (readBlock 0x217856163c5f1851f17c6143c4f1)) (readBlock 0x21785a153c60e1e0f1838203c60e080f1)) (readBlock
                                0x216856173c51084d10442133c4f1)) (branch 558 (branch 556 (branch 557 (branch 543 (branch 544 (branch 542 (branch 538
                                (branch 536 (readBlock
                                0x21a08216856178386084c208360b3c60c83c600802082e0c3c8200820e182130811085e0e1821308020182178560e84c2083478082130802008020)
                                (readBlock
                                0x21a8382085a178564484e0d3c60b3c611080208360b3ca0c1e02082e0c3c82008213834f1080f184e110802008213844200802084e0d82cf1080200821783a16856131820d1e0601802084e0d3c4f13c860))
                                (branch 536 (branch 533 (branch 534 (readBlock
                                0x21586a0e830608360b3c6441e0209120b84cf183e283c46008213180200824482e0d3ca0c3ca133c4208360c84cf183e283c4601e2133c4208320f84c60080200820b834f13c5f183a0c8347884c603ca0d82cf2080f18360b3c8f13c60e8306084c600820c836138a0f11802008020)
                                (readBlock 0x21583a0c18213180208320b83e283c4600802008060)) (readBlock
                                0x2178560e8360b3c6137c42082e133c4200820d82cf27c5f108020)) (readBlock
                                0x2178561683a0c868783c60d1e0f18360b3c8f13c4f11e058))) (readBlock 0x21b8661a0820e18020838780820e8307808020)) (readBlock
                                0x21b8661a0821308060838600820e8306008020)) (readBlock 0x21b8661a0821308020838200820d82df108020)) (readBlock
                                0x2178561683a1386c603c60d1e15084e11080f13c82018160)) (readBlock 0x20e85a1786e1a1e0f13c45808213834f13c4f2)) (readBlock
                                0x2178561683a0c8660d82cf11e0783c60d82cf27c5f182e0d3c8f17c5f11e058))) _ _ low high
                              decide +kernel
                            · intro low high
                              apply search_boxes x _ leaf valid (branch 541 (branch 557 (branch 556 (branch 558 (branch 544 (branch 543 (branch 542
                                (branch 537 (branch 536 (readBlock
                                0x21b082178561683840850208320b3c60d83c400802082e0d3c8200820e10214081f185a0e1021408020102168560e8502083078082140802008020)
                                (readBlock
                                0x21b8382085e16856448520c3c60b3c610080208320b3ca0d1e02082e0d3c82008214830f1080f185210080200821484020080208520c82cf1080200821683a17856141020c1e040100208520c3c4f13c840))
                                (branch 536 (branch 534 (branch 533 (readBlock
                                0x21586e0e834408320b3c6441e0209120b850f183e273c44008214100200824482e0c3ca0d3ca143c4208320d850f183e273c4401e2143c4208360f85040080200820b830f13c51083a0d83078850403ca0c82cf2080f18320b3c8f13c60e83440850400820d8321489cf11002008020)
                                (readBlock 0x21583a0d10214100208360b83e273c4400802008040)) (readBlock
                                0x2168560e8320b3c6144402082e143c4200820c82cf24411008020)) (readBlock
                                0x2168561783a0d86c783c60c1e0f18320b3c8f13c4f11e038))) (readBlock 0x21a8661b0820e10020838780820e8347808020)) (readBlock
                                0x21a8661b0821408040838400820e8344008020)) (readBlock 0x21a8661b0821408020838200820c82d1008020)) (readBlock
                                0x2168561783a14868403c60c1e1d185210080f13c820101c1)) (readBlock 0x20e85e1686a1b1e0f13c43808214830f13c4f2)) (readBlock
                                0x2168561783a0d8660c82cf11e0783c60c82cf24411082e0c3c8f1441101e038)) (branch 543 (branch 544 (branch 542 (branch 546
                                (branch 547 (branch 548 (branch 533 (readBlock
                                0x2178561986e1a8388083e11082100820b83440080209120b8320d3ca101802083611100200820c83478080200820e834781e20b8360c3c8204402086a0e830781e20b8320d3c8207c4201e20e86a1b1e0781e20d82e0c3c8200802083a1a86c781e07884020082158661a86e0e18210080201815018060)
                                (readBlock 0x2178561986e1a8384084420080407444010020)) (readBlock 0x20e83078744f2)) (readBlock 0x20e83478540f2))
                                (readBlock 0x20e1e0f2)) (readBlock 0x20e1e020)) (readBlock 0x20e18020)) (readBlock 0x20e10020))) _ _ low high
                              decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 540 (branch 541 (branch 556 (branch 557 (branch 558 (branch 542 (readBlock
                              0x2218821986a1b082140421585df184cf1082137c42086e130421585910850f108214440208561784cf13c4f10421585a173c6143c6133c4f185e133c6143c4f104213850f13c6143c4208661a86c207c6130402084df17c61986e1a08110850100821444110)
                              (readBlock 0x21986a1b082140402084c10082138501008020)) (readBlock 0x21585e143c4f13c5f1)) (readBlock
                              0x21585a133c4f13c510)) (readBlock 0x21585a173c4f13c4f1)) (branch 548 (branch 546 (branch 543 (branch 542 (branch 544
                              (branch 547 (branch 536 (readBlock
                              0x21b8561785a1a83c2082e0d3c64484cf1844203c820912110820d84cf1080200820b834f183e11080f13c60f844200802086a0f0820b834f2080200821686a0f08211080204402085e1a85a0f0821108020080200821585e1686a0b834f183e0c3c9f13c60d84cf17c4203c5f108020)
                              (readBlock 0x21585e1b85a1a82e0d3c6133c4f2836133c420080f13c4f108020)) (readBlock 0x213845103c4f2)) (readBlock
                              0x20f08020)) (readBlock 0x20f08020)) (readBlock 0x20f081f1)) (readBlock 0x20b834f23c4f1)) (readBlock 0x20b834f23c5f1)))
                              (branch 541 (branch 547 (branch 546 (branch 544 (branch 542 (branch 543 (branch 548 (branch 536 (readBlock
                              0x21a8561685e1b83c2082e0c3c644850f1840203c820912100820c850f1080200820b830f183e10080f13c60f840200802086e0f0820b830f2080200821786e0f08210080207c42085a1b85e0f0821008020080200821585a1786e0b830f183e0d3c9103c60c850f1440203c51008020)
                              (readBlock 0x21585a1a85e1b82e0c3c6143c4f2832143c420080f13c4f108020)) (readBlock 0x214841f13c4f2)) (readBlock
                              0x20f08020)) (readBlock 0x20f08020)) (readBlock 0x20f08110)) (readBlock 0x20b830f23c4f1)) (readBlock 0x20b830f23c510))
                              (readBlock 0x2198561685e1a86e0f82e0c84420834f20820d8402008020840200820b8320d3c820080203c8f208020080f2))) _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (readBlock 0x2188761e86a1b080200802008020) _ _ low high
                          decide +kernel
                      · intro low high
                        apply search_boxes x _ leaf valid (readBlock 0x21e8761885a1986c20080200802008020) _ _ low high
                        decide +kernel
                    · intro low high
                      apply search_boxes x _ leaf valid (readBlock 0x21d87a1885e1986820080200802008020) _ _ low high
                      decide +kernel
                · refine divideBox _ _ 7 4 ?_ ?_
                  · refine divideBox _ _ 5 5 ?_ ?_
                    · refine divideBox _ _ 6 5 ?_ ?_
                      · refine divideBox _ _ 4 5 ?_ ?_
                        · refine divideBox _ _ 7 2 ?_ ?_
                          · refine divideBox _ _ 9 2 ?_ ?_
                            · intro low high
                              apply search_boxes x _ leaf valid (branch 540 (branch 563 (branch 562 (branch 564 (branch 547 (branch 548 (branch 546
                                (branch 542 (branch 543 (readBlock
                                0x22186a1986c10854f2848f28501085cf2042123ca153ca1b84cf2850f23c8f286e19854f2848f284c10858f2042123ca153c8f2854f2866123c8f23ca1b8661a042140421284c103c91086a12850f284c103ca1404213440f2850f23ca1a866140421285a153c81004213040f2850f23ca143c8f2)
                                (readBlock
                                0x22186a1986c1084c1084a14040f27c61b84a133ca14040f284c10851f13ca133c8f286e1984c1084a17854f204010850103ca133c8f284cf23ca1a8661b0401004010))
                                (readBlock
                                0x2208861286a1b8641084cf2850f23ca163c8f286e173c8f23ca1a8661b0421404213040f286e1304214040787c61b8661304214040f24401086a1986c10040100421b8661a0401004010))
                                (readBlock 0x21f88221848f2858f285cf23ca1484cf23ca123c8f284e143c8f2848f23ca1286a163c8f23ca143c8f2)) (readBlock
                                0x22387e218821a854f285cf23ca173c8f286a13851f17c5f13ca1a85213040f2848f23c8f286a12858f204214040f23ca163c8f2)) (readBlock
                                0x22588e1f8822186e153ca163c8f2858f23ca1b8521344110440f286e13850103ca123c8f23ca1b84a173c81084c103c8f285cf23ca163c8f2))
                                (readBlock 0x21b8661a04110851104421404010)) (readBlock 0x21b86a19042121e010848f2042123c810)) (readBlock
                                0x21a8661b041f184df17c61304010)) (branch 553 (branch 552 (branch 554 (branch 548 (branch 547 (branch 546 (branch 533
                                (branch 532 (readBlock
                                0x2173ca1b8661a848f4850f28420f0421182cf43c8f283e11080f23ca123d2143c91086a123d2143c8f23d21a86612850f2840783ca143c8f23c8f2)
                                (readBlock
                                0x217848f286e1a86640852100420f0420c3c8f28420f082111e0f283e11080f23ca14840103c8108520c3c8783ca14830f23c8f28521083c103c8f23ca1a84a1b866143d2101e0f43d0f28521004010080f4))
                                (branch 532 (branch 538 (branch 537 (readBlock
                                0x21985e12844f48420f042401e0f29020f8501082e27040f41e2143d0f23ca4083e100821108214040f2842118501082e27040f41e214040f28460b850f43c8f23ca0f84010041f184a1184078850f40821083c203c8108420f0801004212844f4850f41e2118421489c103d0f23c8f2)
                                (readBlock 0x21984a113d2143d0f28460f82e27040f43c8f23c8f4)) (readBlock
                                0x21a866128420f042147c4f283e14040f23ca1083c207c5f13c8f2)) (readBlock
                                0x21a8661b84a1185c78042101e0108420f08010040101e074))) (readBlock 0x216856173ca123d0f2848783ca12844783c8f2)) (readBlock
                                0x216856173ca143c8f4848f43ca12844f43c8f2)) (readBlock 0x216856173ca143c8f2848f23ca1083df13c8f2)) (readBlock
                                0x21a8661b84a14858f4042101e10e8520c3c810080f23d10d)) (readBlock 0x21286e1a85a171e010040741e2148401004020)) (readBlock
                                0x21a8661b84a118561083c101e0780421083c207c5f183e10080107c5f11e074))) _ _ low high
                              decide +kernel
                            · intro low high
                              apply search_boxes x _ leaf valid (branch 540 (branch 554 (branch 552 (branch 553 (branch 547 (branch 548 (branch 546
                                (branch 534 (branch 532 (readBlock
                                0x2163ca1a8661b848f684cf28460f0421082cf63c8f283e10080f23ca123da133c9f186e123da133c8f23da1b8661284cf2844783ca133c8f23c8f2)
                                (readBlock
                                0x216848f286a1b8664084e110420f0420d3c8f28460f082101e0f283e10080f23ca13844103c81084e0d3c8783ca13834f23c8f284e1183c103c8f23ca1b84a1a866133da111e0f63d8f284e1104010080f6))
                                (branch 532 (branch 537 (branch 538 (readBlock
                                0x21985a12840f68460f042401e0f29020f84c1082e28040f61e2133d8f23ca4083e110821008213040f28461084c1082e28040f61e213040f28420b84cf63c8f23ca0f844100411084a108447884cf60821183c203c8108460f0801004212840f684cf61e210846138a0103d8f23c8f2)
                                (readBlock 0x21984a103da133d8f28420f82e28040f63c8f23c8f6)) (readBlock
                                0x21b866128460f04213440f283e13040f23ca1183c20441103c8f2)) (readBlock
                                0x21b8661a84a1085878042111e0108460f08010040101e076))) (readBlock 0x217856163ca123d8f2848783ca12840783c8f2)) (readBlock
                                0x217856163ca133c8f6848f63ca12840f63c8f2)) (readBlock 0x217856163ca133c8f2848f23ca1183d103c8f2)) (readBlock
                                0x21b8661a84a1385cf6042111e1f584e0d3c810080f23d9f6)) (readBlock 0x21286a1b85e161e010040761e2138441004020)) (readBlock
                                0x21b8661a84a108561183c101e0780421183c204411083e1108010441101e076)) (branch 547 (branch 548 (branch 546 (branch 542
                                (branch 543 (branch 544 (branch 537 (readBlock
                                0x21b8661585a17848f882e0c3ca0d3ca0f840f6080789020f842110820c3d8f28460d3d0f23ca11840783c8f23ca12840781e20f84211080204407885e12844781e20f84610080207c4780821285a171e0781e21183e10080f21e0f284a1685c781e078834f23ca198561685e123da0c3c8f23d9f53d8f6)
                                (readBlock 0x21b8661585e16848f4834f23c8f4438f43d0f2)) (readBlock 0x2128407843820)) (readBlock 0x212844787d420))
                                (readBlock 0x2121e020)) (readBlock 0x2121e0f2)) (readBlock 0x2123d8f2)) (readBlock 0x2123d0f2))) _ _ low high
                              decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 541 (branch 540 (branch 552 (branch 554 (branch 553 (branch 546 (readBlock
                              0x2248961585a173ca143c61986d1084c103ca13440f285e133c619869f1850103ca147c4f28661b84c10040100421986a1b04214042130401086e1304214040100421484c1004213040f285617858f27c6143c4f2851f17c61585a173c91084cf13ca1344110)
                              (readBlock 0x21585e163ca133c4f2850f13ca13850f13c8f2)) (readBlock 0x21986a1304010041f1)) (readBlock
                              0x21986e140401004110)) (readBlock 0x21986e1a0401004010)) (branch 543 (branch 542 (branch 548 (branch 546 (branch 547
                              (branch 544 (branch 532 (readBlock
                              0x2168661a86e1782cf283e100424085010830f2080f29020c3ca10850103c8f23ca0f8401082e0c3c8100420b830f23c8f285e0b3ca0f840203c8f23ca1b85e0b3ca0c3c8f2440f286a1786e0b3ca0c3c8f23c8f23ca1986a1b85e0f8401082e11081f104210850107c4f2041f13c8f2)
                              (readBlock 0x21986a1686e1783e10042140402084214040f23c810040103c8f2)) (readBlock 0x2148311004020)) (readBlock
                              0x20b3c8f2)) (readBlock 0x20b3c8f2)) (readBlock 0x20b3c9f1)) (readBlock 0x20f8402004010)) (readBlock 0x20f84020041f1)))
                              (branch 540 (branch 544 (branch 542 (branch 547 (branch 546 (branch 548 (branch 543 (branch 532 (readBlock
                              0x2178661b86a1682cf283e110424084c10834f2080f29020d3ca1184c103c8f23ca0f8441082e0d3c8100420b834f23c8f285a0b3ca0f844203c8f23ca1a85a0b3ca0d3c8f27c4f286e1686a0b3ca0d3c8f23c8f23ca1986e1a85a0f8441082e10081100421184c10440f2041103c8f2)
                              (readBlock 0x21986e1786a1683e11042130402084613040f23c810040103c8f2)) (readBlock 0x213835f104020)) (readBlock
                              0x20b3c8f2)) (readBlock 0x20b3c8f2)) (readBlock 0x20b3c910)) (readBlock 0x20f8442004010)) (readBlock 0x20f8442004110))
                              (readBlock 0x2158661b86a1685e0b83e10834f2844203ca11830f23c8f2830f23ca0f84211080f23c8f2080203c8f23c820))) _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (readBlock 0x21c8761e85a173c8f23c8f23c8f2) _ _ low high
                          decide +kernel
                      · intro low high
                        apply search_boxes x _ leaf valid (readBlock 0x21e8761c86a1585cf23c8f23c8f23c8f2) _ _ low high
                        decide +kernel
                    · intro low high
                      apply search_boxes x _ leaf valid (readBlock 0x21d87a1c86e15858f23c8f23c8f23c8f2) _ _ low high
                      decide +kernel
                  · intro low high
                    apply search_boxes x _ leaf valid (readBlock
                      0x21e8762387e24886258821586613042140421a85df1040f184cf13c61984c1004010040f1040f1040f1856168661a85e1b82e0c3c60f84020040f183e1008010040f1040f13c4100421d8661b8561785a1a82e0d3c60f84420040f183e1108010040f104010040f13c420)
                      _ _ low high
                    decide +kernel
              · refine divideBox _ _ 7 4 ?_ ?_
                · refine divideBox _ _ 3 4 ?_ ?_
                  · refine divideBox _ _ 2 5 ?_ ?_
                    · refine divideBox _ _ 6 5 ?_ ?_
                      · refine divideBox _ _ 8 2 ?_ ?_
                        · refine divideBox _ _ 3 2 ?_ ?_
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 563 (branch 567 (branch 539 (branch 562 (branch 566 (branch 548 (branch 547
                              (branch 543 (branch 544 (branch 546 (branch 542 (branch 534 (readBlock
                              0x2161e21b1e21586a19848f684cf68387882cf63da123da133d8f686613848f6839563ca0e84956758f63da1a8487884e0e1e0f61e076)
                              (readBlock
                              0x21b86878866168560e18213182121e20f180608386084c601821584e0e182125582084a0e5595e1806085a0e1e213848781807816216868788661583a1355a125595e84a13559565785615a1a8561984a1355a0e559d683a13559567585615956))
                              (readBlock 0x21b8687885c7884c6018216868781e2121e078)) (readBlock
                              0x21f85e161e21b1e2133d8f686a161e078838781e217858781e058)) (readBlock
                              0x22387e1b86a198585885612162111820e1602084858182161621216058866168560e182131821283d5e1815e84c6018213838605795e838581621a85a198385885612162131607815a0e1605684a135595655a0e84d565595686e1a858581606015a1a86e161605815858))
                              (branch 544 (branch 542 (branch 546 (branch 538 (branch 534 (readBlock
                              0x2198561a848788447884dd691a0e1e20b7587875a13849d684420839d63ca1284478839d675a111e1d686a111e2121e213838200807884e123d8201e21586a13848f684478839d63da121e2111e07884e123d8781e2111e0f6)
                              (readBlock 0x21986a1584a1375a111e20f759d68442084e0e081d6082110815684a137595e0821284dd61e058)) (readBlock
                              0x2178561986a1275a1375a0b759d684e12759d675a13848f63d8f684a133d8f63da1284dd6759d6)) (readBlock
                              0x21b85e13848f6838781e2121e078160f6)) (readBlock 0x21b86a111e2121e0781e076)) (readBlock
                              0x21b86a198442084a13559560805857956))) (branch 544 (branch 543 (branch 546 (branch 542 (branch 534 (branch 538
                              (readBlock
                              0x21586616838788347884d5e91a121e20f5787857a138395e834f28495e0820e834788495e57a0d1e15e85a0d1e20e1e213848781e07884e0e180781e21985a1383860834788495e1820e1e20d1e07884e0e180781e20d1e060)
                              (readBlock 0x21585a1983a1357a0d1e20b5795e8347884e123c95e1e20d3c95683a13579d63ca0e84d5e1e076)) (readBlock
                              0x21b8661585a0e57a1357a0f5795e84e0e5795e57a13838601806083a13180601820e84d5e5795e)) (readBlock
                              0x21786e1383860848781e20e1e0781d860)) (readBlock 0x21785a0d1e20e1e0781e058)) (readBlock
                              0x21786e158661383a1257a0d3c82084a11080f20820e84a0d1e15e1e0781e0787595e)) (readBlock
                              0x21b8661584e0e5795e8395e578601815e))) (branch 544 (branch 543 (branch 547 (readBlock
                              0x21f88e1785a15868768660e1da0d3da121d8f2838763da1a1da0e1d8768561a866123da133da0e82dd63d9d684cf63da13848f6759d6848761da1686a15848768660e1da131d87815a121d85683a135595655a1284d565595685e16868761d8f615a1685e1a1d87615876)
                              (readBlock 0x21785a15834f283a13559563c87675956)) (readBlock 0x2178561984e12759d6849d6758f63d9d6)) (readBlock
                              0x21686a0e15a121585655956))) (readBlock 0x21785a1a1e0781e078)) (readBlock 0x21b86a161e0781e078)) (branch 548 (branch 556
                              (branch 552 (branch 544 (branch 543 (branch 547 (branch 532 (branch 536 (readBlock
                              0x21b85e1683878868788347884c608446057a1a83878844608347884c600820e1e211180f285a1a1820e182131806086a0e18211180201821785a0e1e21a830788347882e0f84c601e0f61e20d82cf21e15e83a1a8347884c601e0f282e0d3c9d63da1683a1a1815e8320f180781e058)
                              (readBlock 0x21785a0e1e21b86878834781820d1e07886e0e1e213834781e0783da1683a1b1805884e11180781e058)) (readBlock
                              0x21986e168686085e0e1e213180781821a84460838780806085a1783878830781e0581e21b85e0e1e07816078)) (readBlock
                              0x21585e1986e1683a131820d1e20b8315e180608360b3ca133c87884e111815e57a0e84c601e02083a13180783ca0e84c601e0f283a131815e5820e84c601e060))
                              (readBlock
                              0x21b8661a856178442083a4684c2083478081d684e0d82cf2080207561108020844200821383a11081d60807883a111e0f61e20b836133c9d5759d6))
                              (readBlock 0x21686a1986c60838601620e16058838601821108060)) (readBlock 0x21b86a16838601e06018078)) (readBlock
                              0x21785a0e1e0781e058)) (readBlock
                              0x21685e1586a1983a0c1e20b834f684e26558781e20d1e0788320d1e20b83e101e0781e07882e0d3c8f63da0e830783d8f683a0c83478578f23ca0e830781e07883a0c161561e20b836133c9d5758f6)))
                              (readBlock 0x21c85e1b8561985a0d3ca0e57a135795e84e0e578f257a0d3c95e84e0e578781e20e84d5e3c8f284d5e57a0e84d6057960))
                              (readBlock 0x21c86e178661586a110821275a13759d684e127582075a11081d684e12758201e21284dd60802084dd675a11081d6)) _ _ low
                              high
                            decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 539 (branch 557 (branch 553 (branch 544 (branch 552 (branch 556 (branch 548
                              (branch 537 (branch 533 (readBlock
                              0x21585cf68661b84878840788447883e0b84cf61e0601e2123da1082cf61e078848f6840781e21986e171e2121e2111e07885e121e213834f61e0781da17848781e078)
                              (readBlock
                              0x2158661b85e121e2111e2133da0f82e0d3d9d61e0f684a111e2133d9d68460f0802075a17848f684cf63d9d685e1b8487884cf61e0f61e21b8661285c78082111e0f61e0f6))
                              (branch 536 (readBlock
                              0x21b8561785a0d3da121e24684e1183c20888603ca0f82cf21e0f28460f82d4e1e0781e06084a133da111e0f684e0d3c8201e2128460f84d5e53a13888601e07883e138895e3d8781e20f846130814e5786085e12858781e20d1e0601821785616834f6848f63c8f61d876)
                              (readBlock 0x21786e15834f6848781e0783d878))) (readBlock 0x21a85a1585cf6848f61da121d876848f63da0d3c8f6)) (readBlock
                              0x21785a1a848f61e0f63d878)) (readBlock 0x21b86a121e0781e076)) (readBlock
                              0x21a86e1985a1584a101e20f8446084e22558781e2111e078842111e20f82e0c1e0201e07883e110806018212840781806084a10844787582008212840781e07884a101d9561e20f846130814e57860))
                              (readBlock 0x21b8661a8561784a137da111e1d684e11081f608020080f63d9f6)) (readBlock
                              0x21786e198560d858f23ca1284cf25395e1e0f23c95e)) (branch 544 (branch 548 (branch 542 (branch 546 (branch 543 (branch 547
                              (branch 534 (branch 532 (branch 538 (branch 536 (readBlock
                              0x21a85a0b834f683e11182468321018222180f2842263d8200806091a1184c20840201e213898f63c8781820f8446091a0d84cf2830f21e21388860080783da0d91a133ca11888603d8781e21184c201e0788460f082130802083e0b834f2080f63da168360b3ca133c87882e0f844203c86018020)
                              (readBlock 0x21686a0d82cf684cf21e20b84e263d8601e0783c8f6)) (readBlock
                              0x21985a1a82e0d3da0f842263d8f23c8f6836133c8f61e0f23d8f6)) (readBlock
                              0x21b8661a85a1183c6084c201e20f84e22180f61e078080601e078)) (readBlock
                              0x21b8661586a1683e111820b83222180200806084613080601e020180601e078)) (readBlock 0x20d82cf218160)) (readBlock
                              0x21183c203d9f6)) (readBlock 0x20d82cf21e078)) (readBlock 0x21183c201e078)) (readBlock 0x20b834f23d8f6)) (readBlock
                              0x20f8442018060))) _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (branch 553 (branch 557 (branch 535 (branch 548 (branch 544 (branch 539 (branch 533
                            (readBlock
                            0x21a1e21787e238561986c7883478838781e21b1e07886c781e0781e2158661b91a0e82e0f57a1289d5e1e07883e1289d5e1e0781e20f82e125394e1e078579561e078)
                            (readBlock
                            0x21a86e2387e19856171e2111e2121e07885c781e2171e0781e0788661585e4684a0f82dd683a27758781e20b83a27758781e07882e0f839d5754781e1d6558781e21b85e15866111e20d1e15e1e078579d6))
                            (readBlock
                            0x21f88e1686a1b85c78866158387884078180601e2178561983878830781e0781e07885e158661b83878834781e0781e07857a1b85e158661a84478838781e0781e078181d51e078))
                            (readBlock 0x21c86a168661586e101e2121e20e1e0608407855a101e060840781e212840781806083e0b8395e538601820e18060)) (readBlock
                            0x21c85a1a85e158660c1e20e1e2121e0f6830783da0c1e07883a0c1e1561e20e830783d8f682e0f849d6754f63da0e830781e0f6)) (branch 539
                            (readBlock
                            0x2218962387e1a85a1786c788561984878830783d8f61e21b8661584878840781e0781e07886e198561784878844781e0781e07875a1786e198561683478848781e0781e0783d94e1e078848f63da12840781e060)
                            (readBlock 0x21585e1986e1686a0f82e0d830f684610080783da11840201807884610080781e20b8360c3c8781e0783c8203d8f618060)))
                            (readBlock 0x2178621c856168661b8347883a0b83d5e1e078538781e0781e0783d15e)) (readBlock
                            0x21b872188661a856178447884a0f82dd61e078754201e0781e078101d6)) _ _ low high
                          decide +kernel
                      · intro low high
                        apply search_boxes x _ leaf valid (readBlock 0x21c8761885e168561a1da0e84d561d8f61da133d9d684876158f6830763da0e830763d8f6) _ _
                          low high
                        decide +kernel
                    · intro low high
                      apply search_boxes x _ leaf valid (readBlock 0x2188761c86e1a866161621284d5616060162131815e838581586084058182128405818060) _ _
                        low high
                      decide +kernel
                  · intro low high
                    apply search_boxes x _ leaf valid (branch 539 (readBlock
                      0x2248762187e2085e2588e1586a123da163da0d3d82086e19848f6834f6440f63da1a848f6834f6080f63d8f686a1286e19856103d8f61e0f63da1083e11080f63d8204421284cf67d9f68487808212840780802085e168561a848f6834f63d8f81e0781e20d3c8f2)
                      (readBlock 0x21585e1d8661b86a1682e0d3da0f844203d8f683e11080f63d8f63c8f63d8f608020)) _ _ low high
                    decide +kernel
                · intro low high
                  apply search_boxes x _ leaf valid (branch 545 (branch 548 (branch 540 (readBlock
                    0x218882238921b8861f866168386086860844603ca178560e18211181f11806085a0e18211180f2180601821683a17856198306018078180608320b834f2180603c9d583a13181605820e1e0f2844200821b866168561786a111820f82e0d3c860180f218060180203c8f2)
                    (readBlock 0x21886e1a866168386084460180801e0781e060)) (readBlock 0x20e830783c8f2)) (readBlock 0x20f844203c8f2)) _ _ low high
                  decide +kernel
            · refine divideBox _ _ 9 4 ?_ ?_
              · refine divideBox _ _ 3 4 ?_ ?_
                · refine divideBox _ _ 7 4 ?_ ?_
                  · refine divideBox _ _ 1 5 ?_ ?_
                    · refine divideBox _ _ 5 5 ?_ ?_
                      · refine divideBox _ _ 9 2 ?_ ?_
                        · refine divideBox _ _ 7 2 ?_ ?_
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 568 (branch 564 (branch 535 (branch 562 (branch 566 (branch 543 (branch 544
                              (branch 548 (branch 547 (branch 542 (branch 546 (branch 533 (readBlock
                              0x2171e21a1e21586e19848f4850f48387882cf43d2123d2143d0f486614848f48394d3ca0e8494d534f43d21b848788520e1e0f41e074)
                              (readBlock
                              0x21a86c78866178560e10214102121e20f100408384085040102158520e102125342084a0e715c51004085e0e1e21484878100780e21786c788661583a1471612735c584a14735c5714340d21b8561984a145360e7354d83a147354d534340d14d))
                              (readBlock 0x21685c7886878850f43d21b85c781e20e1e078)) (readBlock
                              0x22386a1b1e2161e2141004085e1b1e078848781e21685c781e038)) (readBlock
                              0x21f88e1685e1586c748660e1d20c3d2121d0f2838743d21b1d20e1d0748561b866123d2143d20e82d4d3d14d850f43d214848f45354d848741d21786e15848748660e1d2141d0780d2121d03483a14735cd736128514d5354d85a1786c741d0f40d21785a1b1d0740d074))
                              (branch 547 (branch 546 (branch 542 (branch 533 (branch 537 (readBlock
                              0x215866178387883078851c5916121e20f7147871614839c5830f2849c50820e83078849c57160c1e1c585e0c1e20e1e214848781e0788520e100781e21985e148384083078849c51020e1e20c1e0788520e100781e20c1e040)
                              (readBlock 0x21585e1983a147160c1e20b715c583078852123c9c51e20c3c9cd83a147154d3ca0e851c51e074)) (readBlock
                              0x21a8661585e0e716147160f715c58520e715c571614838401004083a14100401020e851c5715c5)) (readBlock
                              0x21686a1483840848781e20e1e0781d040)) (readBlock 0x21685e0c1e20e1e0781e038)) (readBlock
                              0x21685e15830f283a14715c53c874535c5))) (branch 547 (branch 548 (branch 542 (branch 546 (branch 537 (branch 533
                              (readBlock
                              0x2198561b84878840788514d9160e1e20b53478536148494d840208394d3ca12840788394d536101e14d86e101e2121e2148382008078852123d0201e21586e14848f4840788394d3d2121e2101e078852123d0781e2101e0f4)
                              (readBlock 0x21986e1584a14536101e20f5354d840208520e0814d08210081cd84a14535c5082128514d1e038)) (readBlock
                              0x2168561986e12536145360b5354d852125354d53614848f43d0f484a143d0f43d2128514d5354d)) (readBlock
                              0x21a85a14848f4838781e2121e0780e0f4)) (readBlock 0x21a86e101e2121e0781e074)) (readBlock
                              0x21686a158661483a125360c3c82084a10080f20820e84a0c1e1c51e0781e078535c5)) (readBlock
                              0x21685619852125354d8494d534f43d14d))) (branch 547 (branch 548 (branch 544 (readBlock
                              0x22387e1a86e1985c38856120e2101020e0e02084838102170e2120e038866178560e102141021283dc5101c5850401021483840715c5838380e21b85e1983838856120e2140e0780d20e0e03484a14735cd7360e851c5715c586a1b85c380e0400d21b86a170e0380d038)
                              (readBlock 0x21a86e198402084a145354d080387154d)) (readBlock 0x21a866158520e715c5839c571440101c5)) (readBlock
                              0x21b85e120d20e0d034735cd))) (readBlock 0x21685e1b1e0781e078)) (readBlock 0x21a86e171e0781e078)) (branch 543 (branch 552
                              (branch 556 (branch 547 (branch 548 (branch 544 (branch 536 (branch 532 (readBlock
                              0x21686a1b8487885c7884078850f4830f45361784878830f484078850f41e2121e20c3d02086e173d2123d2143d0f485e123d20c3d0f23d21a86e121e217844788407883e0b850f41e0401e21083c200814d84a1784078850f41e02083e10081c51021b84a173d14d8460b3d0781e074)
                              (readBlock 0x21a86e121e21685c78840783d2101e07885a121e214840781e0781021b84a163d0748520c3d0781e074)) (readBlock
                              0x21585a1b85cf486a121e2143d0783d217830f4848781e0f486e1a84878844781e0741e21686a121e0781d078)) (readBlock
                              0x21986a1585a1b84a143d2101e20f8454d3d0f48420f08214080788520c3d14d53612850f41e02084a143d02008212850f41e02084a143d14d43612850f41e0f4))
                              (readBlock
                              0x216856178661a830f284a45850f2840781e1c58521083c203c8f27560c3c8f2830f21e21484a0c3c9c53c87884a0c1e0401e20f84214081d5715c5))
                              (readBlock 0x21b85e15858f4848f41d2121d074848f43d20c3c8f4)) (readBlock 0x21685e1b848f41e0f43d078)) (readBlock
                              0x21a86e121e0781e074)) (readBlock
                              0x21b86a1985e1584a111e20f8404085222714781e2101e078846101e20f82e0d1e0201e07883e100804010212844781004084a11840785342008212844781e07884a111d1cd1e20f84214081d571440)))
                              (readBlock 0x21886a168661586e1008212536145354d8521253420536100814d85212534201e2128514d080208514d536128510d5350d))
                              (readBlock 0x21885a1a8561985e0c3ca0e71614715c58520e714f27160c3c9c58520e714781e20e851c53c8f2851c57160c3c9c5)) _ _ low
                              high
                            decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 535 (branch 554 (branch 558 (branch 547 (branch 556 (branch 552 (branch 543
                              (branch 534 (branch 538 (readBlock
                              0x219868408561683878834788307882e0f850401e0f41e20e1020d83c401e07883840834781e21585a1a1e20e1e20c1e07886a0e1e214840401e0780e21a838781e078)
                              (readBlock
                              0x2198561686a0e1e20c1e2141020b83e10101c51e04083a0c1e214101c58320b3c8787161a8384085040101c586a1683878850401e0401e2168560e868781e20c1e0401e040))
                              (branch 532 (readBlock
                              0x2168661a86e101020e1e2458520c82cf2898f40820b83c201e0208320b83d4e1e078080f483a141020c1e04085210080f21e20e8320b8514d53a14898f41e07882e148994d100781e20b832143c94e534f486a0e86c781e2101e0f43d21a8661b8404083840080400e038)
                              (readBlock 0x21a85a1984040838780807810078))) (readBlock 0x21786e1986840838400e20e0e038838401021008040)) (readBlock
                              0x21a86e17838401e04010078)) (readBlock 0x21685e0e1e0781e038)) (readBlock
                              0x21785a1586e1983a0d1e20b830f485226534781e20c1e0788360c1e20b83e111e0781e07882e0c3c8f43d20e834783d0f483a0d83078714f23ca0e834781e07883a0d0e1cd1e20b832143c94e534f4))
                              (readBlock 0x216856178661a83a147060c1e1c58520c3c9c13c8f21e040101c1)) (readBlock
                              0x21a85a158661086c200820e850205394d080200814d)) (branch 543 (branch 547 (branch 546 (branch 542 (branch 544 (branch 548
                              (branch 533 (branch 532 (branch 537 (branch 536 (readBlock
                              0x21786e0f8404082e0c3d2458361110222100f2846263d020080409160c850f2834f21e21488840080783d20b830f49161085020844201e214898f43c8781020c916143ca10888403d0781e210850201e0788320b3ca143c87882e0f840203c8401021b8420f082140802083e0b830f2080f43d020)
                              (readBlock 0x21786e0c82cf4850f21e20b852263d0401e0783c8f4)) (readBlock
                              0x21985e1b82e0c3d20f846263d0f23c8f4832143c8f41e0f23d0f4)) (readBlock
                              0x21a8661b85e1083c40850201e20f85222100f41e078080401e078)) (readBlock
                              0x21a8661586e1783e101020b83622100200804084214080401e020100401e078)) (readBlock 0x20c82cf2101c1)) (readBlock
                              0x21083c203d10d)) (readBlock 0x21083c201e078)) (readBlock 0x20c82cf21e078)) (readBlock 0x20b830f23d0f4)) (readBlock
                              0x20f8402010040))) _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (branch 554 (branch 558 (branch 535 (branch 547 (branch 543 (branch 539 (branch 534
                            (readBlock
                            0x21b1e21687e23856198687883078838781e21a1e078868781e0781e2158661a9160e82e0f716128a1c51e07883e128a1c51e0781e20f82e12755d51e078715c51e078)
                            (readBlock
                            0x21b86a2387e19856161e2101e2121e078858781e2161e0781e0788661585a4584a0f82d4d83a28534781e20b83a28534781e07882e0f8394e538781e14d534781e21a85a198560c1e2101e14d1e0787154d))
                            (readBlock
                            0x21f88e1786e1a85878866158387884478100401e2168561983878834781e0781e07885a158661a83878830781e0781e0787161a85a158661b84078838781e0781e0781014e1e078))
                            (readBlock 0x21c86e178661586a111e2121e20e1e04084478736111e040844781e212844781004083e0b839c5754401020e10040)) (readBlock
                            0x21c85e1b85a158660d1e20e1e2121e0f4834783d20d1e07883a0d1e1cd1e20e834783d0f482e0f8494d538f43d20e834781e0f4)) (branch 539
                            (readBlock
                            0x2208922387e1b85e16868788561984878834783d0f41e21a8661584878844781e0781e07886a198561684878840781e0781e0785361686a198561783078848781e0781e0783d1d51e078848f43d212844781e040)
                            (readBlock 0x21585a1986a1786e0b83e0c834f484211080783d21084420100788320d3c8781e20f84211080781e0783c8203d0f410040)))
                            (readBlock 0x2168621c856178661a8307883a0b83dc51e078754781e0781e0783d9c5)) (readBlock
                            0x21a872188661b856168407884a0f82d4d1e078538201e0781e0781814d)) _ _ low high
                          decide +kernel
                      · intro low high
                        apply search_boxes x _ leaf valid (readBlock 0x21c87a1885a178561b1d20e851cd1d0f41d2143d14d848740d0f4834743d20e834743d0f4) _ _
                          low high
                        decide +kernel
                    · intro low high
                      apply search_boxes x _ leaf valid (readBlock 0x21887a1c86a1b866170e212851cd0e0400e214101c5838380d04084438102128443810040) _ _
                        low high
                      decide +kernel
                  · intro low high
                    apply search_boxes x _ leaf valid (branch 535 (readBlock
                      0x22187a2488e2586a2087e1985e0e1021b10210100f285a158384084040440401021783840840403c8401004085e0e85a158660d100401e0401020d82e0c3c840100f24420e85040705c1838783ca0e834783c8f286a1b866178384084040100801e0781e21008020)
                      (readBlock 0x21986a1e8561685e1b83e101020b830f21004082e0c3c8401004008040100403c8f2)) _ _ low high
                    decide +kernel
                · intro low high
                  apply search_boxes x _ leaf valid (branch 549 (branch 543 (branch 541 (readBlock
                    0x21c8961f88616892238561b848f485cf4830f40821a866123d20c3d1f13d0f486e123d20c3d0203d0f43d21b84a1a86615844f43d0783d0f48460f840203d0f4081d584a143d10d436121e020830f23ca168561b8661a85e0c3d20b83e10080f43d0203d0f43d0f208020)
                    (readBlock 0x21c85a178561b848f4830f43d0f81e0781e0f4)) (readBlock 0x2128447808020)) (readBlock 0x20b830f208020)) _ _ low high
                  decide +kernel
              · intro low high
                apply search_boxes x _ leaf valid (readBlock
                  0x22289a21882258921887e2385a1787078868781e21a870781e07885e1b870781e0781e0781e21c86a1b858781e0781e078834781e20c1e078844781e2101e07883878202121e0f8)
                  _ _ low high
                decide +kernel
          · intro low high
            apply search_boxes x _ leaf valid (branch 545 (branch 550 (branch 551 (branch 543 (readBlock
              0x21f8861888e248961d87a190821308216838200802086e1908020838203c61e86a1908020838203c42087a1d852133c4f13c5c13c61d87a13850f13c4f1580f18761e83a1685e1308020080203c4601021d87a1986e1a080f13c4f1080208621d87a190802018020042188761e868200806010010)
              (readBlock 0x21887a1d864200804008010)) (readBlock 0x21886e1d8661683860180201808018020)) (readBlock 0x21886a1e8661783840100201008010020))
              (readBlock 0x21d87a198561404010040f108020)) _ _ low high
            decide +kernel
        · intro low high
          apply search_boxes x _ leaf valid (branch 545 (branch 550 (branch 549 (branch 548 (branch 547 (readBlock
            0x220886188721d86a161e21b1e2123d9d685a171e20e1815e1e216868781e0788761686a1b1e0781e0781e21c8761a85a171e0781e0781e20d1e0608621d8721a86e16160581595e180781e21c8761b862178561986a111e2121e1d6758781e0587d9d61e060)
            (readBlock 0x218876178721b8661585a0d1e20e1e15e578781e0765815e1e0f6)) (readBlock 0x21c8761885a17868761d856758f61e078)) (readBlock
            0x21886e1d85a0e18060180801e060)) (readBlock 0x21c86a16860781e0781e078)) (readBlock 0x21c85e1d86a123d8f63d8f81e0f6)) _ _ low high
          decide +kernel
      · intro low high
        apply search_boxes x _ leaf valid (branch 545 (branch 551 (branch 549 (branch 543 (branch 544 (readBlock
          0x2258921c8621e86e171e21a1e2123d14d85e161e20e101c51e21786c781e07887a1b85e161e0781e0781e21887a1786e1a1e0781e0781e20c1e0408721e8621785a1b1d0740d14d3d0781e21887a168721a8661585e0c1e20e1e1c5714781e074705c51e0f4)
          (readBlock 0x21c87a1a862168561986e101e2121e14d534781e0384354d1e040)) (readBlock 0x21887a1c86e1a85c380e034714401e078)) (readBlock
          0x21886a1e85e0e10040100801e040)) (readBlock 0x21885e1b870781e0781e078)) (readBlock 0x21c85a1e86e123d0f43d0f81e0f4)) _ _ low high
        decide +kernel
    · intro low high
      apply search_boxes x _ leaf valid (branch 549 (branch 550 (branch 551 (branch 548 (readBlock
        0x2238921c87e208861d87a153ca133ca1a848f23c8f285e153c8f2848f20421e85a153c8f2848f2040f287a1d85213040100410d0421d87a1385010040107d81087a1d84a1a86e133c8f23c8f2040f43da1d87a1585e163c810040103c8f28721e876153c8f23d0f23c61c8761e858f23c8f63d0f1)
        (readBlock 0x21c8761e854f23c8f63c8f1)) (readBlock 0x21c85e1d8561a848f63d8f23d8f83d8f2)) (readBlock 0x21c85a1e8561b848f43d0f23d0f83d0f2))
        (readBlock 0x21d87a1586613040103c4103c8f2)) _ _ low high
      decide +kernel
  exact done positive cap

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- The ten fibers are nonempty. Split codes encode a coordinate and a threshold.
At a nonempty leaf the ten-bit cut costs at most sixteen on the full box. -/
lemma weights_30 :
  let E : Finset (Fin 10 × Fin 10) := {(0,5),(0,6),(0,7),(1,4),(1,6),(1,8),(2,3),(2,6),(2,9),(3,7),(3,8),(4,7),(4,9),(5,8),(5,9)}
  let cost (x : Fin 10 → ℕ) (m : ℕ) := ∑ e∈E,
    if m.testBit e.1.val=m.testBit e.2.val then x e.1*x e.2 else 0
  ∀ x : Fin 10 → ℕ, (∀ i,1 ≤ x i) → (∑ i,x i)=22 → ∃ m,cost x m≤16 := by
  intro E cost x positive mass
  let leaf (s : ℕ) (lo hi : Fin 10 → ℕ) :=
    let sl := ∑ i,lo i
    let sh := ∑ i,hi i
    let h (i : Fin 10) := min (hi i) (22+lo i-sl)
    if s=511 then decide (22<sl ∨ sh<22) else decide (cost h s≤16)
  have valid s lo hi (low : ∀ i,lo i≤x i) (high : ∀ i,x i≤hi i) (check : leaf s lo hi=true) :
      ∃ m,cost x m≤16 := by
    by_cases empty : s=511
    · have bad : 22<(∑ i,lo i) ∨ (∑ i,hi i)<22 := of_decide_eq_true (by simpa only [leaf,empty,if_true] using check)
      have a := sum_le_sum (s:=univ) (fun i _ => low i)
      have b := sum_le_sum (s:=univ) (fun i _ => high i)
      omega
    · refine ⟨s,le_trans ?_ (of_decide_eq_true (by simpa only [leaf,empty,if_false] using check))⟩
      apply sum_le_sum; intro e _
      split
      · exact Nat.mul_le_mul (tighten x lo hi mass low high e.1).2 (tighten x lo hi mass low high e.2).2
      · exact le_rfl
  have cap (i : Fin 10) : x i≤13 := by
    have h := sum_erase_add univ x (mem_univ i)
    have low := sum_le_sum (s:=univ.erase i) (f:=fun _ => 1) (g:=x) (fun a _ => positive a)
    have size : (univ.erase i).card=9 := by simp
    simp only [sum_const,size,smul_eq_mul,mul_one] at low
    omega
  let readBlock (code : ℕ) := Nat.rec (motive := fun _ => ℕ → List (BinaryTree ℕ) → BinaryTree ℕ)
    (fun _ stk => stk.headD .nil)
    (fun _ step data stk => if data=0 then stk.headD .nil else
      let s := data%1024-1
      if s<512 then step (data >>> 10) (BinaryTree.node s .nil .nil :: stk)
      else match stk with
        | left :: right :: tail => step (data >>> 10) (BinaryTree.node s left right :: tail)
        | _ => .nil) 95 code []
  let branch := @BinaryTree.node ℕ
  let box (lo hi : Fin 10 → ℕ) :=
    (∀ i,lo i≤x i) → (∀ i,x i≤hi i) → ∃ m,cost x m≤16
  have divideBox (lo hi : Fin 10 → ℕ) (i : Fin 10) (k : ℕ)
      (left : box lo (Function.update hi i k))
      (right : box (Function.update lo i (k+1)) hi) : box lo hi := by
    intro low high
    by_cases h : x i≤k
    · apply left low
      intro a
      by_cases eq : a=i
      · subst a; simpa using h
      · rw [Function.update_of_ne eq]; exact high a
    · apply right _ high
      intro a
      by_cases eq : a=i
      · subst a; simpa using (show k+1≤x i by omega)
      · rw [Function.update_of_ne eq]; exact low a
  have done : box (fun _ => 1) (fun _ => 13) := by
    refine divideBox _ _ 0 7 ?_ ?_
    · refine divideBox _ _ 8 7 ?_ ?_
      · refine divideBox _ _ 9 7 ?_ ?_
        · refine divideBox _ _ 1 7 ?_ ?_
          · refine divideBox _ _ 2 7 ?_ ?_
            · refine divideBox _ _ 7 7 ?_ ?_
              · refine divideBox _ _ 4 7 ?_ ?_
                · refine divideBox _ _ 6 7 ?_ ?_
                  · refine divideBox _ _ 5 7 ?_ ?_
                    · refine divideBox _ _ 3 7 ?_ ?_
                      · refine divideBox _ _ 0 4 ?_ ?_
                        · refine divideBox _ _ 8 4 ?_ ?_
                          · refine divideBox _ _ 9 4 ?_ ?_
                            · refine divideBox _ _ 7 4 ?_ ?_
                              · refine divideBox _ _ 1 4 ?_ ?_
                                · refine divideBox _ _ 2 4 ?_ ?_
                                  · refine divideBox _ _ 3 4 ?_ ?_
                                    · refine divideBox _ _ 6 4 ?_ ?_
                                      · refine divideBox _ _ 5 4 ?_ ?_
                                        · refine divideBox _ _ 4 4 ?_ ?_
                                          · refine divideBox _ _ 0 2 ?_ ?_
                                            · refine divideBox _ _ 1 2 ?_ ?_
                                              · intro low high
                                                apply search_boxes x _ leaf valid (branch 534 (branch 536 (readBlock
                                                  0x2181021a1021d870798787986e0b1020d1021329e0f29c4082c408344029e1c8787986e0d1020c1e60b1021283c3f7d5f583440830791021e86e0b1020c1e60d1021483c3c29ca782c40830791021b82c408344010040)
                                                  (branch 537 (readBlock
                                                  0x2181021c874798787986e0c1020d1021045a1245840830408344045a1d8787986e0d1020b1e60c102138403e7d5f58344082c791021e86e0c1020b1e60d102148403c459168304082c791021b830408344010040)
                                                  (readBlock
                                                  0x21e87479870798621b850a782c4083040838a71020b1020c100a786e0b1e60c1e4791e61c874798621b8304082c408347984a0e0fd1645a0c1020b1007986e0d1e60c1e4791e61d8621b82c40834798304083a130f8a729e0b1020c1007986e0d1e60b1e4791e61886e0b1020c1004010040)))
                                                  (branch 535 (branch 541 (readBlock
                                                  0x2198684086ca7874a78720b1020e102141e60c1e44082c40838401e61a86d16871168760e1020c102141e60b1e44083040838401e61c86d168747983079850791021d86ca78507982c791021b850a7838a710040)
                                                  (branch 536 (readBlock
                                                  0x21a1021b874a78720e1020b1020f29e118303f459168384083ca71021d8720b1020e1020f29e0c84c381e47982c4083ca71021c8384082c4010040)
                                                  (branch 537 (readBlock
                                                  0x21b871168760e1020c1021045a0b8443e29ca7838408304045a1c8760c1020e1021045a0b848381e47983040841161021d838408304010040)
                                                  (readBlock
                                                  0x21b8721d83a0b1020c102111f61284c75458a782e0c102134da12845351e4a7832122de13844b51e516846137d5f57d60c8384082c4045a0e82c40459168760b838408304029e0e8304029ca71021d8720b83040838401e60c838401e47910040))))
                                                  (branch 541 (branch 540 (readBlock
                                                  0x21c1e61986ca786a0b1e61329e141e60c83d881004082c798507929e1b86a141e61329e0b1e60c8447a459168507982c7929e1a8507982c791e479)
                                                  (branch 539 (readBlock
                                                  0x21a86d168660c1e61245a141e60b841881004083079849161e61b866141e60c1e61245a0b8447b29ca7850798307945a1985079830791e479)
                                                  (readBlock
                                                  0x21b8661a8460f7d6107d6140f20b8307c29d1682e0c1e6141e60f6584083e107d60c85186100a78520c1e5161020b850798307929e148307929ca786a0c8507982c7945a1482c79459161e61a8660b83079850791020c85079100401e479)))
                                                  (branch 539 (branch 540 (branch 536 (readBlock
                                                  0x21a86df58321045a1245a0b6d60f84db71007984a1045a130e20b83cb81e5f584e0f29e0b29df582e0f29c401021b84ca783ca7845f582e122dc791e60b84ca783ca71e61383ca71e479)
                                                  (readBlock
                                                  0x21a86e1245a1045a117d60c84d361e4798321245a104587984a10458791e61b84e127d6117d47984a117d4791e479))
                                                  (readBlock
                                                  0x21a86e1984116845f5849168320f658401021245a10459168660c841168491610210849161004045a1986e0b83221888408a0796d62884a24658b729cb783e228844029df545a0f84627888a77d5161e51610079))
                                                  (readBlock
                                                  0x21d8661b86a0f29e117d61329e1082da71004084ca783ca729e1a82e0f29e1329c4083e1329c40100a786e1a84e0b8a2211e62329d3688e11899b50f8400fa1188e267d43e458408320b886221007a45916458791021a8661b83e107d6117d440842117d4401004010040)))))
                                                  _ _ low high
                                                decide +kernel
                                              · intro low high
                                                apply search_boxes x _ leaf valid (branch 534 (branch 536 (branch 540 (readBlock
                                                  0x2188684086ca7878a78720b1020f102131e60d1e44082c4083c401e61a86df5871f587a0b1e6131e60f1020d100408344083c401e61b871f5878a784ca783ca71021e8707984c7982c791021c8347984c7910040)
                                                  (branch 537 (readBlock
                                                  0x2181021b871f587a0f1020d102107d60b8443c29ca783c40834407d61c87a0d1020f102107d60b848301e47983440841f51021e83c408344010040)
                                                  (branch 535 (readBlock
                                                  0x21b878a78720f1020b1020e29e118343f7d5f583c4082c4029e1e8720b1020e29e0f10214834301e47982c40838a71021c82c4083c4010040)
                                                  (readBlock
                                                  0x21b8721e82e0d1020f1021475611849d629c798360f102122be11850ab7d47983e111ee128506b7d4a7846124591645a0d83c4082c407d60f82c407d5f587a0b83c408344029e0f8344029ca71021e8720d82c4083c401e60b83c401e47910040))))
                                                  (branch 540 (branch 541 (readBlock
                                                  0x21c1e61b860a786a131e60b1e61429e0d8447a7d5f584c7982c7929e1886a0b1e6131e61429e0d8395a1004082c7984c7929e1a84c7982c791e479)
                                                  (branch 539 (readBlock
                                                  0x21a86df58620d1e6127d6131e60b841751004083479849f51e61b862131e60d1e6127d60b8447d29ca784c79849f51e61884c79834791e479)
                                                  (readBlock
                                                  0x21b8621a83a1045a1145a0b5d60d84d7d100a78421145a0d56a0b84d7a101f584e0b1e60d1e4a782e0d1e4a77d60b84c798347929e138347929ca786a0d84c7982c797d61382c797d5f51e61886a0d82c7984c791020b84c79100401e479)))
                                                  (branch 539 (branch 541 (branch 537 (readBlock
                                                  0x21886d1682e1429e0e29e0d55a12841551e440836107d6127d60e851521007984a107d6140c1168520e29d161021b84916841f58451683614558791e60d849f5841f51e612841f51e479)
                                                  (readBlock
                                                  0x21886e1429e0e29e1145a0b848af1e47982e1429e0e29c798520e29c791e61b8521245a114587984a11458791e479))
                                                  (readBlock
                                                  0x21a86e1884116849f5845168360e55840102127d6107d5f58620d841f5849f510210849f5100407d61886e0d84a2788079891f52be2082e230fd56458af82e2088c401f4a729e0b83a238804029d164591610079))
                                                  (readBlock
                                                  0x21e8621b86a0e29e1429e1145a0b8415610040850a7838a729e1a82e0e29e1429c4083a1429c40100a786a1b8421189a237d6224587a88a1489d5a0f0400f20d88e201015a1e4798461488a26458a71e4401e4401e61a8621b83a1045a114584084211458401004010040))))
                                                  (branch 535 (branch 536 (branch 537 (readBlock
                                                  0x21b874a7878a78720e1020f1021045a11458408384083c4045a1d878a78720f1020b29e0e10213840387d5f583c4082ca71021e8720e1020b29e0f1021484030459168384082ca71021c8384083c4010040)
                                                  (readBlock 0x21e874a786ca78720b29e0e29ca729e1b874a78720e29e0f29ca729e1d8720f29e0b29ca729c40))
                                                  (branch 541 (readBlock
                                                  0x21b874a786a1c45a0e29e11458a78721429e11458a729e1d8721a8507982ca784c7983a122a11645a141e60b29c7986a1429e0b29ca729e1a8720e850a782ca745a1482ca74591629ca7)
                                                  (readBlock
                                                  0x21a86e1c8761145a1045a127d60e84d3629ca7845168411645a1d83a1145a10458a784610458a729d168721d82e138a2211e62329d3688612895750e0400e20e88e20100a84591683a1088223101167d4797d4401021b8761c84e117d6127d4a7846127d4a729ca729c79)))
                                                  (branch 536 (branch 540 (readBlock
                                                  0x21b878a786a1c7d60f29e1329df58721329e117d4a729e1e8721a84c7982ca78507983e122a1f57d6131e60b29c7986a1329e0b29ca729e1a8720f84ca782ca77d61382ca77d5f529ca7)
                                                  (readBlock
                                                  0x21b87a1a8721145a107d61245a0f8519629ca783e117d6107d4a7846107d4a729e1c8521145a12458a784612458a729ca786a1c845f5841f57d5f529e1a8721e842128962045a217d4a88821489d880c0400c20f886221018829c7982e1489e201e4a70c0401e44010079))
                                                  (readBlock
                                                  0x21d87a1b8721a84c798451685079849161e6131e6141e51686a1329e1429ca729e1c86a131e6141e4791e47986e1c86a127d6117d5f57d4a71e61e86e1c86a1145a1245916458a71e516))))
                                                  _ _ low high
                                                decide +kernel
                                            · refine divideBox _ _ 1 2 ?_ ?_
                                              · intro low high
                                                apply search_boxes x _ leaf valid (branch 534 (branch 537 (branch 539 (readBlock
                                                  0x2188644086d1687916876101020d1e6121e60c1004083040840401e61986df5875f587a0c1e610102121e60d1004083440840401e61b875f58791684916841161021e8747984879830791021d834798487910040)
                                                  (branch 536 (readBlock
                                                  0x2181021b875f587a101020d1020f7d60c8443c4591684040834407d61d87a0d1020f7d6101020c84c201e4798344083df51021e834408404010040)
                                                  (branch 535 (readBlock
                                                  0x21b87916876101020c1020e45a118343e7d5f5840408304045a1e8760c102101020e45a14834201e47983040839161021d830408404010040)
                                                  (readBlock
                                                  0x21b8761e8320d10210102147961184de745879836101021347a118511a7d479842111ea138505a7d51684e1129ca729e0d84040830407d610830407d5f587a0c840408344045a1083440459161021d87a0d83040840401e60c840401e47910040))))
                                                  (branch 539 (branch 540 (readBlock
                                                  0x21e1e61986df58620d1e6121e6137d60f830f51004083479848797d61b862121e60d1e6137d60c8447d459168487984df51e61884879834791e479)
                                                  (branch 541 (readBlock
                                                  0x21886d168660c1e61445a121e60d838eb10040830798487945a1b866121e61445a0c1e6118347b7d5f584879851161e61984879830791e479)
                                                  (readBlock
                                                  0x21b862198360c1e6121e60f3ae0e844ef101f5832121e60e3d60f844f71011683a0f29e1129d1683e1129df545a0c848798347945a1283479459168660d84879830797d612830797d5f51e6188660c83479848791020d84879100401e479)))
                                                  (branch 535 (branch 536 (branch 538 (readBlock
                                                  0x21e874a7838a7844a78511683e0c39c401021d83ca7844a784df583a0d39c401020e83ca7844a71020f844a710040)
                                                  (readBlock
                                                  0x21d87a1383df5835f58502083a0c480a71e61483916831168360f7847929e0d83df5830e71020c83916100408360f7d6137d44083e137d4401021e8320e45a144584083a144584010040))
                                                  (readBlock
                                                  0x21e86e1d850a783916844a78321339c791e61445a0e459168760c85116839161e614839161e47945a1b8760d8321f890408987939e2483a28478f57d4e784e2687c797d4a729e0c83a2487c40458a729ca710040))
                                                  (readBlock
                                                  0x21d87a1986e1329e0f7d61129e0d850e71e479836137d60f7d47984e0f7d4791e61b84e1429e1129c798521129c791e4798661b84df583df57d5f51e61986e1e83e1189e247d62229c7b88a14898eb0f0400f20d8921f100eb1e4798461488a2729d161e4401e44010079))))
                                                  (branch 535 (branch 537 (branch 536 (readBlock
                                                  0x21b8791687116876101021129e0e1020f29c40838408404029e1c87916876101020c45a0e1020f848387d5f5840408384045a1e8760e102101020c45a1483c2029ca783840831161021d838408404010040)
                                                  (readBlock 0x21e8711686d168760c45a0e4591645a1b871168761045a0e4591645a1c8761045a0c4591645840))
                                                  (branch 541 (readBlock
                                                  0x21b871168661d29e0e29e1129d168761429e1129d1645a1c8761985079831168487983a133e4a729e141e60c458798661445a0c4591645a198760e851168311629e148311629ca745916)
                                                  (readBlock
                                                  0x21986e1d8721129e0f29e137d60e848b745916844a783ca729e1c83a1129e0f29d168460f29d16458a78721d84a0c8a2211e624458b788613894f50e0400e213886257d43829c4083a0c8921f100f529ca729c401021b8721d84a117d6137d516846137d5164591629c79)))
                                                  (branch 537 (branch 539 (readBlock
                                                  0x21e86d168761984879831168507984e10461f57d6121e60c458798661245a0c4591645a1b8661d7d61045a117d5168761245a10459f545a198761084916831167d612831167d5f545916)
                                                  (readBlock
                                                  0x21e86e198761129e0f7d61329e10851a745916842117d60f7d5168460f7d51645a1d8521129e1329d168461329d16459168661d83e138961f29e217d51887e148998808040082108862210188458798321489a1f1e516080401e4401e61986e1d845f583df57d5f510116))
                                                  (readBlock
                                                  0x21c87a1b87619844a78507984ca7848791e6121e6141e4a78661245a144591645a1d866121e6141e4791e47986e1d866117d6137d5f57d5161e61e86e1d8661129e1329ca729ca71e4a7))))
                                                  _ _ low high
                                                decide +kernel
                                              · intro low high
                                                apply search_boxes x _ leaf valid (branch 534 (branch 536 (branch 537 (branch 535 (readBlock
                                                  0x21b871f5875f587a0e29e1129e0f102101004083c408404029e1c875f587a101020d7d60f1020e84830459168404083c407d61d87a0f102101020d7d6138382029ca783c40840407d61e83c408404010040)
                                                  (readBlock 0x21b871f5875f587a107d60f7d5f57d61c875f587a107d60d7d5f57d61d87a0f7d60d7d5f57d440))
                                                  (branch 540 (readBlock
                                                  0x21c86df587a1884c79835f58487983e143e4a729e131e6121e5f5862137d60d7d5f57d61b8621e29e0f29e1129df587a1329e1129df57d61887a0f84df5835f529e13835f529ca77d5f5)
                                                  (readBlock
                                                  0x21886e1e8721129e0e29e1445a0f848af7d5f5844a7838a729e1c83e1129e0e29df58460e29df57d4a78721e8361289e201e6247d4af88214894eb0c0400c20f8921f100eb29ca785212882254583029ca7100401021b8721e84a1145a14459f584614459f57d5f529c79)))
                                                  (branch 537 (branch 539 (readBlock
                                                  0x21b875f58621e45a1045a127d51687a1245a107d5167d61d87a188487984c79835f5842145e51645a121e6131e5f5862127d60d7d5f57d61887a10849f5835f545a12835f5459167d5f5)
                                                  (readBlock
                                                  0x21d86e1887a1129e0e45a1429e138411e7d5f58421145a0e459f58460e459f57d61e84e1129e1429df58461429df57d5f587a188361088e20102267d55a89a1387d794791647a1389a1f1e51e29ca783a148961f29d16080401e4791021886e1e84516839164591610116))
                                                  (readBlock
                                                  0x21c8761b87a18844a784c79850a7848791e6121e6131e4a7862127d6137d5f57d61e862121e6131e4791e47986e1e8621145a1445916459161e61d86e1e8621129e1429ca729ca71e4a7)))
                                                  (branch 535 (branch 536 (branch 537 (branch 538 (readBlock
                                                  0x21c875f58791684516841161021d878a783ca7844a71021e844a7838a710040) (readBlock
                                                  0x21c8761e83a0f10210102147c61284df9458a783e1010213462148490829df5842122a213850887d51684a141e4791e60f84040838407d610838407d5f587a0e8404083c4045a1083c40459161021d87a0e83c408404029e0f8404029ca710040))
                                                  (readBlock
                                                  0x21b87a1d29e1c844a7838a7458a78761c844a783ca77d4a729e1d87a1c84e141e6121e4a7852121e4a729ca729ca7))
                                                  (readBlock
                                                  0x21a86e1e871168761129e0e458a745a1c8761145a10459f5459168721e876128507984c7945a1484c79459164591629e1b87a1c8761129e1429c79458a77d479))
                                                  (readBlock
                                                  0x21986a1b8721d7d61e84516841f5459f58761e844a783df529df57d61c8761e84a131e6141e5f584e141e5f57d5f5458a786e1d8721e844a784ca71e5f529d161e61b8721d87a1a84516849161e4797d51629c79)))
                                                  _ _ low high
                                                decide +kernel
                                          · intro low high
                                            apply search_boxes x _ leaf valid (branch 539 (branch 541 (branch 533 (readBlock
                                              0x2158747985c798621a45a1b4587986a1b458791e61a8611686d1685e1d1e4791e617874798621b458791e61b861161e479)
                                              (branch 538 (readBlock
                                              0x21d85e151e61a86116849f584c7945a121e614458798621a45a15850a784c7945916856141e6124587945a18869168561445a12845165595645a1a85e1245a14845165595645956)
                                              (readBlock
                                              0x21d85e151e61a84879852131e5795e479856188507984a131e5795e4795e61585e1886a1285151835755d61482d5a569565495556571)))
                                              (branch 533 (branch 537 (readBlock
                                              0x2178621b45a158747983040841161e60c45a121e4798561d1e60c1e6124587986e1d849f583479459161e61886d168560c45a12841164d93645a1b8761245a0c841164d93645936)
                                              (readBlock
                                              0x2178561d1e6188307984a0d1e47d1f4798761b848798320d1e47d1f4791f61886e1d8561283035845754da0c82c3e0f83e1d43d0d935))
                                              (readBlock
                                              0x21d85e1586a1b8617584975834791e61883479849755e47986e1884c79849751f4791e61a86e127d610459165d47d86e1a8621584516849754d9164d9754da1a86e1885e15841168497555916459565d47d)))
                                              (branch 541 (branch 533 (branch 535 (readBlock
                                              0x21586a1b45a17874798304082c7945a0c45a141e479876171e61b850a782c794587985e0c1e6144587945a1a86d1685e0c45a14839164791e45a1b8761445a0c839164791e4591e)
                                              (readBlock
                                              0x21585e1d1e61a830798520b1e47a1e8798761b850798320b1e47a1e8791ea178761b86a148301a8455a47a0c8343e0f83e4681e0e85a))
                                              (readBlock
                                              0x215876178621b8695a8515a82c791e61a82c798515a5e47986e1a84c798515a1e8791e61886e1429e0e459165687a8621b86a17839168515a559165595a1ea1b8621a87617845168515a479164591e5691e))
                                              (readBlock
                                              0x216856178761886a1b0fa0c0fa0b1e47986e0b1e60c0f87d1e61a86e0d1e60c0f87a1e4798621a83040841164583e0fa1886a1b8760e45a0c0f9364583e0f83e86a1886e178761045a0c0f91e459160f83e0fa1a8621b85e158760b8347984c7945a0e841160f83e5591e4d9791e87d)))
                                              _ _ low high
                                            decide +kernel
                                        · intro low high
                                          apply search_boxes x _ leaf valid (branch 556 (branch 532 (branch 540 (branch 541 (readBlock
                                            0x2168707985c798621929e1b29c798661b29c791e617870798661829e1b29c798621b29c791e61886ca7864a71e61b864a71e479)
                                            (branch 536 (readBlock
                                            0x21785a1c1e61886ca782c4083ca71e60b1e61329c798621b29e0b29e131e47986e1c84df58347929ca71e61886ca785a0b29e1383ca72dcb729e1b8721329e0b83ca72dcb729cb7)
                                            (readBlock
                                            0x21785a1c1e61882c7984e0d1e47d1f4798721b84c7982e0d1e47d1f4791f61c85a1b8620b84c358303f0fe13844f52dc3f2d4371d43d)))
                                            (branch 541 (branch 533 (readBlock
                                            0x21885e1c1e61986ca782c408307929e0b1e61429c798661b29e0b29e141e4798721b851168307929c7929e17870798660b1e614830791ec7b1e61c86e141e60b830791ec7b1e47b)
                                            (readBlock
                                            0x2188661b29e1782ca78520e29caf2bca786e1c850a782e0e29caf2bca72be1c85e1b8660b8502b8343f0fe14844eb2bc3f2ac2f1ac3b))
                                            (readBlock
                                            0x21685e1c8621986c3f82c3f830791e61b8307982c3f1f4798661b8347982c3f1ec791e6188660b1020e29ca70fc3f8621986e1c838a782c3f2dca70fc3f0fe198621b85e1c83ca782c3f2bca729c3f0fc3f)))
                                            (branch 540 (branch 541 (branch 539 (readBlock
                                            0x21b85a171e618864a785116844a71e6141e61329c7985e19860a784df5844a71e6131e61429c798661829ca729e1685c79862141e613848793e4f91e617866131e614848793e4f91e4f9)
                                            (readBlock
                                            0x21b8621929e16850a784e1129ce739ca78661784ca78521129ce739ca739e1685e1886613850e1834f53d614830eb3ace738ce53a4f1))
                                            (readBlock
                                            0x21b8661885e1c858f584cf5844a729e1683ca784cf539ca787216844a784cf52dca729e17872137d60d1e47939cb78721785a188487984cf51f4791f4f51f61787216866188347984cf53e4791e4f53d4b7))
                                            (readBlock
                                            0x21e86e1886616872173ae143ae1129ca785e0e29e143ace729e1c85e1129e143acaf29ca785a1c85116830791e4e72be1c85a17866121e6143ac7b1e47b3ac7b85a1c85e188660c1e6143acf91e4793aceb2be1785a1c86e198620c848798347929e0d8487929ca71ec7d3e4e72bcb7)))
                                            (readBlock
                                            0x21e872168561d1e6171e479876171e4791e61d856171e4791e4af8561d85a171e4791e47939e1585a178761c1e47d1f4351f47d))
                                            _ _ low high
                                          decide +kernel
                                      · intro low high
                                        apply search_boxes x _ leaf valid (branch 556 (branch 557 (branch 532 (branch 534 (branch 533 (readBlock
                                          0x218864408684087a1d1e61c1e4408721d1e44010219868408761c1e61e1e4408721e1e4401021c87479878791021d8787910040)
                                          (branch 540 (readBlock
                                          0x2198721e1e61a86040835f583c401e60d1e60b100408621a1021e82ca783c401e44086a0d1020b1e4401e61e870798620b1e60d84c795e5791e61c86a0d1e60b84c795e5791e579)
                                          (readBlock
                                          0x2198621a1021e82c408360f100300c04086a1c8344082e0f100300c0400c21c87a1886a0d82d51841f10c20b850a82a0302c1d15c559)))
                                          (branch 533 (branch 535 (readBlock
                                          0x21e86a191021c8747983116838401e60c1020b1e4408761c1e61982ca7838401e4798720c1e60b1004010219868408760b1020c838400e0381021a8720c1020b838400e03810038)
                                          (readBlock
                                          0x21e8721d1e61a8307982e141e588620798761982c79832141e588620796221a8661c8760c82db8849184620b83ca80e038661a84e0b8))
                                          (readBlock
                                          0x2188661a8761e870a882ca8838401021c83c4082ca80e04087a1c8384082ca80c0401021d87a0b29e131e4790e03087a1d8721a8507982ca85e4792a0a80e21d87a1c8661a84c7982ca8620791e4a82a030)))
                                          (branch 533 (branch 534 (branch 539 (readBlock
                                          0x21a862191021e8747983116840401e60c1020d1e4408661d87879835f5840401e60d1020c1e4408761e1e4791e61d878798660d1e60c848793e4f91e61e8620c1e60d848793e4f91e4f9)
                                          (readBlock
                                          0x21a862191021e830408361010020080408661d834408321010020080400821d87a188660c834e1839180820d83df108020481e13c4e9))
                                          (readBlock
                                          0x21a862198721e8751883118838401021d84040831180e04087a1d8384083118080401021c87a0c45a121e4790e0208721e87619848798311862079461180821e8721d8621985079831183e4791e4f946038))
                                          (readBlock
                                          0x2178661a8621c8761e7c60d7c60f1004087a101020d7c4301021d87a0f1020d7c420100408721d835f584c791e4300821d8721e862131e60d7c4f91e4f97c4308721d87a1a862121e60d7c5791e4795e5f10821d8721e8621986a148487984c791020f838400e0383e5796203808030)))
                                          (readBlock
                                          0x2158761e85a171e61c1e47985e1c1e4791e61785a1c1e4401e43885a1787a1c1e440100790c21687a1c85e1d1e4f93e4e13e4f9))
                                          (readBlock
                                          0x2168921c85e1587879874791021e874791e47987a15874791e4790e21585e1e87479100401e4201e61e8561d85e1c1e5795e5515e579))
                                          _ _ low high
                                        decide +kernel
                                    · intro low high
                                      apply search_boxes x _ leaf valid (branch 556 (branch 558 (branch 557 (branch 534 (branch 539 (branch 540
                                        (readBlock
                                        0x216878798547986a197d61b7d4798661b7d4791e615878798661b7d61a7d47986a1b7d4791e619869f586df51e61b869f51e479)
                                        (branch 537 (readBlock
                                        0x2168661b7d6158787983440841f51e60d7d6121e4798561e1e60d1e6127d47986e1e84916830797d5f51e61986df58560d7d612841f5755d57d61b87a127d60d841f5755d57d5d5)
                                        (readBlock
                                        0x2168561e1e6198347984a0c1e47b1ec7987a1b848798360c1e47b1ec791ee1e8561b8660d8482b83c3c0f212845966583c7582c1ac3b)))
                                        (branch 540 (branch 532 (readBlock
                                        0x21986a1b7d616878798344083df51e60d7d6131e47985a1e1e60d1e6137d47986e1e84ca783df51e5f51e6168787986a0d1e61382c791e87a1e61e86e131e60d82c791e87a1e47a)
                                        (readBlock
                                        0x21986e1a7d61e84df58360f7d5e5795f586a16835f584e0f7d5e5795f57961b86a1e85a0d84c1a8303c0f213851a71e83c1683a79c1c))
                                        (readBlock
                                        0x21585a1e86a1986c3c8343c82c791e61b830798343c1e8798661b82c798343c1ec791e61986a0d1020f7d5f50f03c8661a86e1e83df58343c755f50f03c0f21a8661b85a1e841f58343c795f57d43c0f03c)))
                                        (branch 539 (branch 540 (branch 538 (readBlock
                                        0x21e856161e619869f584ca7845f51e6131e6127d47985a1a865f584916850797d6121e6137d47986a197d5f57d619869f5856137d612845f56d5b57d61a85a127d613845f56d5b57d5b5)
                                        (readBlock
                                        0x21e85a151e61a8487984e141e588620798561984c7984a141e588620796221585a1986a13849b882da76221283196621886ddb66a198))
                                        (readBlock
                                        0x21e85a1586a1b8659684996830791e61983079849966207986e1985079849961ec791e61a86e1245a107d5f56207b86e1a86615845f584996755f5659966221a86e1985a15841f5849966d5f57d5966587b))
                                        (readBlock
                                        0x21d8561e85a1986e1a69e1369e0b1e47986a0b1e61369d881e61b86a141e61369c7a1e4798661b84ca783df57d5881ea1986e1a85a0f7d61369db57d5a769c7a86e1986a1e85a117d61369de57d5f569da76221e8561686e1a8660c82c79850797d60f841f50f03c1e87b621d5795b5)))
                                        (readBlock
                                        0x21d8561e872171e6161e47985e161e4791e617872161e4791e4b78721787a161e4791e47939e178561687a1c1e47b1ec2b1ec7b))
                                        (readBlock
                                        0x2178921c85a1d85479878791e615878791007987615878791e4790c21585a1d87879100401e4201e61d8561e85a1c1e588621b862188))
                                        (readBlock
                                        0x21c8922585a1e876171e6151e47985e151e4791e617876151e4791e5368761787a151e4791e479558791e61785a1587a1d1e47a1e81a1e87a))
                                        _ _ low high
                                      decide +kernel
                                  · intro low high
                                    apply search_boxes x _ leaf valid (branch 558 (branch 555 (branch 556 (branch 557 (branch 535 (branch 541 (branch
                                      538 (readBlock
                                      0x215874a7864a785a1a45a1c458a786a1c458a729e1a87116859168661d29ca729e19874a785a1c458a729e1c8591629ca7) (branch
                                      532 (readBlock
                                      0x21686a1c45a19874a78384082ca745a0e45a1429ca78661d29e0e29e14458a78761c8507982ca7458a745a19874a786a0e29e1482ca72a0a829e1d8721429e0e82ca72a0a829ca8)
                                      (readBlock
                                      0x21686a1c45a19839168520c45918461168721d8511683a0c4591846116462198761c86a1483808849884620e83c380e038420180a088)))
                                      (branch 538 (branch 536 (readBlock
                                      0x21a85a1c45a15874a7838408411629e0e45a1129ca78561d29e0e29e11458a78721d845f58411629d1629e15874a785a0e29e1183ca72dcb729e1d8721129e0e83ca72dcb729cb7)
                                      (readBlock
                                      0x21a85a1c45a158391684610459364d9168721d8451683a10459364d9164da158761c85a0e8443582c380e211849b54d8384d4360dcb5))
                                      (readBlock
                                      0x2198561d85a1a870388383883ca729e1c82ca7838382dca786a1c83ca7838382a0a729e1686a0e10210459160e03886a168721d8411683838461160e0380e21686a1c8561d83116838384d916458380e038)))
                                      (branch 538 (branch 541 (branch 539 (readBlock
                                      0x21d8661529e1a85916845f58491629e1129e14458a78561686916850798491629e1429e11458a786a164591645a1a859168661145a14849166599645a168561445a11849166599645996)
                                      (readBlock
                                      0x21d8561929e16850a78461329da769ca78661a844a78521329da769ca769e198561686a148458582d8862211841b5659886199569587))
                                      (readBlock
                                      0x21a8721687619855b5845b58491645a1584916845b54d9168661584116845b56591645a1d866117d61329ca74d9968661d8561683ca7845b569ca769db54da1d866158721684ca7845b52dca729cb76d4b7))
                                      (readBlock
                                      0x21e8561d866168721a622146220b29ca786a0b29e14621a729e1c86a1329e14620a829ca7872168507983116458a8622168721a8660c45a146219645988620a88721686a1d8661245a14621184591646188462198561d86a168720b83ca784ca745a0c849164603869ca82dd9646136)))
                                      (readBlock
                                      0x21e8561d8621b29e1929c7986e1929c791e61886e1929ca729c7b86e188761929ca729ca73e615862198761b29cb72dc352dcb7))
                                      (readBlock
                                      0x21e85a1c8921886d16869161e61b869161e479851160d61886e1a458a74587a86e188721a458a729d162a2168621a86e1c459364d8354d936))
                                      (branch 541 (readBlock
                                      0x21c8761b89223856168661a6221369e146219686a1265a14621a71e61986a1369e117d58829d8886a168661265a117d588459f5622141e5b584ca765a168561986988621886218886e1686a158659665996659966221b8761586616869a769da769da761588)
                                      (readBlock 0x21c8761b8661a85a156d5b56d5b56d5b8659a7))) (branch 545 (branch 541 (readBlock
                                      0x21685623892188761c8661a0e20b2a2146203886a0c46214620381e61986a0e0e20b29d1829c3886a198720c4620e100a8101160e21c8761986988621886218882ca74620c458a88621a8721987518461184611846218856198761a870a82a0a82a0a8020a8)
                                      (readBlock 0x21585a1886a198721d0e0380e0380e1b80e038)) (readBlock 0x188))) _ _ low high
                                    decide +kernel
                                · intro low high
                                  apply search_boxes x _ leaf valid (branch 554 (branch 558 (branch 556 (branch 555 (branch 557 (branch 538 (branch
                                    536 (branch 540 (readBlock
                                    0x215860a7878a785e1a7d61c7d4a786a1c7d4a729e18878a786a1c7d6177d4a7872177d4a729e1a871f585df529e1c85df529ca7) (branch
                                    535 (readBlock
                                    0x21a85e1c7d615878a783c40841f529e0f7d61129ca78561e29e0f29e117d4a78721e84516838a77d5f529e15878a785e0f29e11838a72bcaf29e1e8721129e0f838a72bcaf29caf)
                                    (readBlock
                                    0x21a85e1c7d61583df5846107d5d5755f58721e845f583e107d5d5755f57561e8561c85e1183c2b851562be0f82c300c0307582c2ac2f)))
                                    (branch 540 (branch 541 (readBlock
                                    0x21c8561829e17869f584c79849f529e1329e117d4a785e1a7d6137d61129ca78621a84516849f529ca77d618854a786a1129e13850a75695a29e1585e1329e11850a75695a29d5a)
                                    (readBlock
                                    0x21c85e1a7d61584df5846127d5755d5f586a18845f584e127d5755d5f55d6158621786a138457e82d7956a1183956559565f5765e95e))
                                    (readBlock
                                    0x21887a1586a1c85d5684556850a729e17838a784556568a787217850a7845562bca729e1c86a1145a127d5f52bd5686a1c85e15841f5845565d5f5559562be1c86a1787a15849f584556755f57d55655956)))
                                    (branch 540 (branch 536 (branch 534 (readBlock
                                    0x2158621e29e1a871f583c4082ca77d60f29e137d4a786a1c7d60f7d61329ca78721e84c7982ca77d5f529e1a871f58620f7d613835f57c5f17d61c87a137d60f835f57c5f17d5f1)
                                    (readBlock
                                    0x2158621e29e1a83ca784e0b29ca82a0a787a1c84ca783e0b29ca82a0a72a21c86a1e8621383c08851792a20f838300c030220287e410))
                                    (readBlock
                                    0x21587a1885e1c8697984d7982ca729e1a82ca784d79568a78721a850a784d792a0a729e17872131e60d7d5f5568a885e1c86a18835f584d795d5f55d5792a21c85e1a87a18849f584d797c5f57d5795e55a))
                                    (readBlock
                                    0x2198561887a1786a1c0c20f0c20b29ca78720b29e0f0c0af29e1a8720e29e0f0c0a829ca785e1a83c40841f57d4300c21786a1c87a0d7d60f0c1d57d4300c03086a178721887a107d60f0c1f17d5f50c0300c21a85e1c8621587a12841f5835f529e0d841f529ca75d5f17555a2a0af)))
                                    (readBlock
                                    0x21d8561e8661b29e1829c7986e1829c791e61986e1829ca729c7d86e1987a1829ca729ca73e6158661887a1b29caf2bc2b2bcaf))
                                    (readBlock
                                    0x21d86e1989217871f5869f529e1c869f529ca784df50ae1c85e1a7d4797d47a85e1c8661a7d4791e5f52a2178661a86e1c7d5d57542b755d5))
                                    (branch 540 (readBlock
                                    0x21c87a1b89222856178621a55a135e6145695686a135e6125d5561e61886a1155a1429d7529d5686a178621155a127d55a7d51655a127d55a84c7955a1585e1a861795e5795e57986e1786a15861755d5755d5755d61b87a188561a85d5a5695a5695a5f95a)
                                    (readBlock 0x21e8721b8621a8561755956559565595155956))) (branch 546 (branch 540 (readBlock
                                    0x217856228921987a1c8621a0c2135e60b2a03086a0d7c6135e4301e61886a0b2a20f1017929c3086a188720d7c60f100a8101f50c21c87a18869795e5795e57984c790c2131e4308661c86a18879f17c5f17c5f15e6198561887a1a870a82a0a82a0a8020a8)
                                    (readBlock 0x21585e198621a8721e0c0300c0300c1510c030)) (readBlock 0x179))) (readBlock
                                    0x22588a238921d87a1586ca7864a72a21b8621929ca729c0886e198621529ca729d362a21b8621e8661529ca729ca7658a829e11458a7845f529ca8))
                                    _ _ low high
                                  decide +kernel
                              · intro low high
                                apply search_boxes x _ leaf valid (branch 558 (branch 555 (branch 556 (branch 554 (branch 557 (branch 553 (branch 532
                                  (branch 535 (branch 536 (readBlock
                                  0x21685c408684087a1d29e1b29c4086e1d29c4010217868408761b29e1e29c4086e1e29c401021d86ca7878a71021b878a710040) (branch
                                  533 (readBlock
                                  0x21e86a171021b874a7839168304029e0e1020b29c4086e1d29e0e29e0b100408761782c798304029ca710217868408760b1020e830400f83e1021a86e0e1020b830400f83e1003e)
                                  (readBlock
                                  0x21e86e1d29e1a838a782e1429d5a568a78761782ca783a1429d5a568a756a1786a1b8760b8397e8347a0fa0e8411e0f83e5797a1f93e)))
                                  (branch 536 (branch 540 (readBlock
                                  0x21786e1e29e1a8584083df58344029e0f29e0b1004085a1a1021e82c798344029c4087a0b29e0f100401021e86ca785a0b29e0f84ca769da729e1b86a0f29e0b84ca769da729da7)
                                  (readBlock
                                  0x21785a1a1021e82c4083e0d1003c0f04086a1b83c4082e0d1003c0f0400f21e86e1686a0b83d858507a1ea0f841e50f03c1f1c561da5))
                                  (readBlock
                                  0x21685e1a8761e86c7a82c7a834401021b8344082c7a0f84087a1b8304082c7a0f0401021d87a0b1e61329ca70f83c87a1d86e1a850a782c7a69ca71e87a0fa1d87a1b85e1a84ca782c7a568a729c7a1e83c)))
                                  (branch 535 (branch 536 (branch 538 (readBlock
                                  0x21a85e161021d878a783df58404029e0f1020e29c4085a1e874a7839168404029e0e1020f29c408761e29ca729e1d878a785e0f29e0e844a739ce729e1e85a0e29e0f844a739ce729ce7)
                                  (readBlock
                                  0x21a85a171021e8384083e10100200804085e1d83c4083a1010020080400821e8761685e0e83ce18511e39e0f835e508020481e138ce5))
                                  (readBlock
                                  0x21a85a1786e1e8751e8391e830401021d840408391e0f84087a1d830408391e080401021b87a0e45a1129ca70f82086e1e87617844a78391e568a74791e0821e86e1d85a17850a78391e39ca729ce74783e))
                                  (readBlock
                                  0x21985e1a85a1b8761e7960f7960d1004087a101020f7943c1021d87a0d1020f794201004086e1d83df5844a729c3c0821d86e1e85a1329e0f794e729ce77943c86e1d87a1a85a1129e0f795a729ca769de50821685e1a87a1b87610830408344029e13850a70f83c0f0200f8e769d5a)))
                                  (readBlock
                                  0x2198561886e1d29e1e29c408761e29c401021d86e1e29ca729c3c86e1d8621e29ca729ca70821886e1e8561d29d5a5697e5695a))
                                  (readBlock
                                  0x2158821e8621d864a786ca71e61986ca7100a78761986ca71e4790f2198621d86ca71004029c3e29e1887a1b8661d29ce739ce139ce7))
                                  (readBlock
                                  0x2188922087a1b8561929e1d29ca78661d29ca729e158661d29c4029c208661586e1d29c40100a70f8a729e1e8561d8661b29da769d8569da7))
                                  (branch 543 (branch 541 (readBlock
                                  0x218856248861686e1d85e1a0fa0b1ea145683e86a0e47a145683e29e1a85e0c0fa0e4587a4583e85e1a8760c0fa0b1e51e100790fa1b876178695a5695a5695a839161ea1429c3e85a1a86e178751e4791e4791e47a16856178761b8687a1e87a1e87a0687a)
                                  (readBlock 0x2158621685e1a86e1d0f83e0f83e0f97e0f83e)) (readBlock 0x15a))) (branch 546 (branch 544 (branch 540
                                  (readBlock
                                  0x2158821e8921b8661785a1a0f21369e0b1e83c86a0f7961369c3c29e16869a769da785e168687a1e87a1ea178661686a0b1ea0d101a71e43c1e9a784ca70f2178661a85a1b83de5834401e8407d43c1e9a784ca70f2178661b86a16879e5795e5795e5069a7)
                                  (readBlock 0x2158661786a1686e1e0f03c0f03c0f1850f03c)) (readBlock 0x1a7)) (readBlock 0x7a))) (readBlock
                                  0x2208861588a238921d87a1685e19102181004086219100406221786618100405684085e1985840100401021686219100401004082c403860b1e44082c79102168621a85e1910020080e10802082ca71020b29c40))
                                  _ _ low high
                                decide +kernel
                            · intro low high
                              apply search_boxes x _ leaf valid (branch 554 (branch 556 (branch 553 (branch 557 (branch 555 (branch 558 (branch 559
                                (branch 536 (branch 534 (branch 537 (readBlock
                                0x21585840860408761b7d61c7d44086e1c7d4401021b871f5875f586216100401021d871f585a1810040102168604010040) (branch 532
                                (readBlock
                                0x21d86e1c7d6188584083ca782c407d60f7d60d1004087216860408347982c407d60d7d60f1004085a181004010216860408720d1020f82c400fc3f1021886e0f1020d82c400fc3f1003f)
                                (readBlock
                                0x21d86e1c7d61883df5836137d4f53d5f587216835f583e137d4f53d5f53d61b8721885a0d83cff8487d1f60f838b70fc3f2fc7f3dcfd)))
                                (branch 537 (branch 535 (readBlock
                                0x21b856161021d871f583ca7845f51020f102107d44085a1c875f584116838407d6101020f7d4408721d7d5f57d615858408760f10210838400e03810216872101020f838400e03810038)
                                (readBlock
                                0x21b8761c7d61583df5842117d5b56d5f587216841f583e117d5b56d5f56d61585a1c8760f841b884cb72de10831360e0386d9b72e138))
                                (readBlock
                                0x2188561686e1d870b783cb782c401021c8384083cb70fc408761c82c4083cb70e0401021b8760f29e117d5f50fc3886e1d87216845f583cb73d5f52dcb70e21d86e1c8561684df583cb76d5f57d4b72dc3f)))
                                (branch 537 (branch 534 (branch 533 (readBlock
                                0x21c856181021d86df583479830407d60d102107d4408621b875f584116830407d6101020d7d44086e1d7d5f57d615860408760d10210830400f83e1021886e101020d830400f83e1003e)
                                (readBlock
                                0x21c86e1d7d618841f5836127d5755d5f587615835f5842127d5755d5f55d61d86e158620d8417e82c7d0fa10839360f83e1f93e5f576))
                                (readBlock
                                0x2168621586e1c8753684136830401021d83840841360f8408721d83040841360e0401021b8721045a127d5f50f8388721b87615849f5841366d5f54d9360fa1b8721d86215845f5841365d5f57d5364d838))
                                (readBlock
                                0x217856168621d8721b1f60d1f60b1004086e0b1020d1f43e1021c86e0c1020d1f43f100408721d83479849f57d43f0fa1d8721b862137d60d1f5757d47d1f43f8721d86e16862127d60d1f4f57d5f51f47d0fa1585a1886e1c87613845f5849f510211849f5100400fc3e0e1b55d4f5)))
                                (readBlock 0x2198621585e1a102161004086a16100401021a85e1610040100e785e1a85616100401004069e1a86216856171003e0f97e0f83e))
                                (readBlock
                                0x21789a1686a1586440860401021986040100408561986040100403d61986a15860401004010175102198561885a1a100380e1b80e038))
                                (readBlock
                                0x22685e1d89619869f58721b7d4797d61c86a1b7d4791e43e835f56e21a8661c86df5100407d43f86a1c86e1d865f56d5b56e1b56d60d101f5))
                                (branch 545 (branch 532 (readBlock
                                0x21985e1d8962685a1886e1c0fe0b0fe0f2dc7d8720b0fe0d1f4b71021c86e0d1f6133d43f1e43f86e1c8620f2de137d43f7d4a70fe0b100f582c403d61885a1b8703f0fc3f0fc3f8761886e16870b72dcb72dcb70fe1d85e168721886c7d1f47d1f47d0d43f)
                                (readBlock 0x2178661d8721b85a183d4f53d4f53d4ff1f4b7)) (readBlock 0x2137d43f))) (readBlock
                                0x2248961988a2685e1d8561a7d61b7d5f5869f57d61a86e1c7d4401003f86e1d86a1c7d4a729df50e20f7d57e7d61d85e1c86e1a7d5755d57e5d57583c407d60f29df5))
                                (branch 543 (branch 549 (branch 547 (branch 534 (readBlock
                                0x22588a1d8561c85a1a8621b0fa0c0fa0d1f53686e0d1f6125d43e1e61886c7d1f47d86a1b861755d5751f61686a1886c3e0f83e0f97e8721a85a1b862104da127d43e7d43e5d47d0fa1686a1c8621586e0c0fa104587d101160f83e1f575834794da0c10175)
                                (readBlock 0x2168721a86e188561d4d9364d9364d8350f936)) (readBlock 0x7d)) (readBlock 0x3e)) (readBlock 0x175))) (branch
                                546 (branch 545 (branch 548 (branch 547 (branch 543 (readBlock
                                0x22686a1886e198561d872160e20f2de116d43885a0e0e20f2dd3629e168720e0e210458b71003887216876104da117d438459f50e2168721d855364d9364d936866168561d870380e0380e0380e21986e1c87615859b56d5b56d5b56e1368661b862158761c858b72dcb72dcb72dc380d60e101b5)
                                (readBlock 0x2117d438)) (readBlock 0xb7)) (readBlock 0x38)) (readBlock 0x1b5)) (readBlock 0x136))) _ _ low high
                              decide +kernel
                          · intro low high
                            apply search_boxes x _ leaf valid (branch 561 (branch 553 (branch 555 (branch 556 (branch 554 (branch 557 (branch 558
                              (branch 559 (branch 533 (branch 535 (branch 537 (readBlock
                              0x21585c408644087a1b45a1c4584086e1c458401021b871168791686617100401021e8711685e1910040102178644010040) (branch 532
                              (readBlock
                              0x21e866171021b87116838a782c4045a0e1020c4584086e1c45a0e45a0c1004085e1c8307982c404584045a17864408720c1020e82c400fc3f1021986e0e1020c82c400fc3f1003f)
                              (readBlock
                              0x21e86e1c45a198391683214458eb3ad16872178311683a14458eb3ad163ae178661b8720c838ff8347b0fe0e83caf0fc3f3bcfb1fcbf)))
                              (branch 537 (branch 539 (readBlock
                              0x217856191021e86d16830798344045a0c10210458408661b87916841f58344045a101020c4584086e1e4591645a1e86d168560c45a10849166599645a1b8661045a0c849166599645996)
                              (readBlock
                              0x217856191021e830408420d1003c0f0408661b840408320d1003c0f0400f2158661b87a0c841858507b1ee1083dd50f03c655861f1c5))
                              (readBlock
                              0x21585e198721e86c7b8307b82c401021b834408307b0fc4087a1b82c408307b0f0401021c87a0c1e612459160fc3c87a1c86e19851168307b659161ec7b0fe1c87a1b85e19849168307b3ad164587b1ec3c)))
                              (branch 535 (branch 537 (branch 538 (readBlock
                              0x219856171021e87116838a7845161020e102104584085e1c87916841f583c4045a101020e458408721e4591645a1e871168560e45a10845165595645a1c85e1045a0e845165595645956)
                              (readBlock
                              0x219856171021e838408420f100300c04085e1c8404083a0f100300c0400c21e8721585e0e84151850af2be10835d50c0302c1d154955))
                              (readBlock
                              0x2198561786e1e870af838af82c401021c83c40838af0fc4087a1c82c40838af0c0401021b87a0e29e14459160fc3086e1e8721784516838af3ad162bcaf0c21e86e1c8561785116838af55916458af2bc3f))
                              (readBlock
                              0x21a866178561b8721e756107560d1004087a0f102107543c1021c87a0d10210754301004086e1c841f5845164583c0c21b8721e8561145a107559645996754308721b87a178561245a107555645916559d50f21585e198721b87a0d83c4082c4045a11851160fc300fc300f156658eb)))
                              (readBlock 0x2188661585a1a102171004086a17100401021a85a1710040100e785a1a85617100401004055a1585a178661a1003c0f1850f03c))
                              (readBlock
                              0x21689a1786a1885440864401021586440100408561886440100403ae1886a158644010040101881021786a1985618100300c1510c030)) (branch
                              532 (readBlock
                              0x2168621e8962685e1986e1c0fe0b0fe0e2bc7b8720b0fe0c1ecaf1021c86e0c1ee144583f1e43f86e1c8660e2be144583f458a70fe0b100eb82c403ae1985e1b8703f0fc3f0fc3f87a1c85e1986c7b1ec7b1ec7b0fe1e8621986e17870af2bcaf2bcaf0ac3f)
                              (readBlock 0x2168621e8721b85e193aceb3aceb3acff1ecaf))) (readBlock
                              0x2248961885a2687a158661b45a1a459168691645a1a4591686a1b87116100400fe0e4598586e1e86a1c458a729d160c21e85a1c86a1b4599665985659968384045a0e29d16))
                              (readBlock
                              0x22489a16886258621e8561c45a1a459168691645a1a8721b458401003f8721e86a1b458791e5160f20c4595145a1887a1b86a1c4595655951559568304045a0c1e516))
                              (branch 544 (branch 549 (branch 547 (branch 533 (readBlock
                              0x22588e1587a1c85e1a86e190f21265a0c1ec3c8660d0f20c1ed961e61986c7b1ec7b86a1b86596659961ee1786a1986c3c0f03c0f18585e1a8721986e0d0f2107d47b1003c0f07b65a1c86a1786e1987a1265a107d43c7d5160f1961ec3c830797560c1e5d5)
                              (readBlock 0x2178721a86e198561e755d5755d57542b0f196)) (readBlock 0x7b)) (readBlock 0x3c)) (readBlock 0x196))) (branch
                              545 (branch 546 (branch 548 (branch 547 (branch 544 (readBlock
                              0x22686a1986e188561e85e1c0c20f0c20e2bd568721155a0e2bc3029e178720f0c2107d4af100308721787a1075611458307d5160c2178721e855d5755d5755d5862178561e870300c0300c0300c21886e1c87a1585d565595655956545568621b8661587a17870af2bcaf2bcaf2bc300ae0e29dd5)
                              (readBlock 0x20e29dd5)) (readBlock 0xaf)) (readBlock 0x30)) (readBlock 0x156)) (readBlock 0x1d5))) (readBlock
                              0x22488222886238562589a1a85a18102171019685e19101561021785a181003f0fc3f1004086a16862178644010040100403fe104584084116102107d440841f51003f))
                              _ _ low high
                            decide +kernel
                        · intro low high
                          apply search_boxes x _ leaf valid (branch 553 (branch 555 (branch 557 (branch 554 (branch 556 (branch 558 (branch 559
                            (branch 560 (branch 561 (branch 538 (branch 537 (branch 539 (readBlock
                            0x21887916859168661d7d6177d51685e1d7d51645a19875f585df585a1e4591645a168791685e1d7d51645a1d85df545916) (branch 536
                            (readBlock
                            0x21885e1d7d6168791684040839167d6107d6114591687a1645a1d844a7839167d51685a1045a117d5167d617875f585a107d61183df5795e57d61d87a117d61083df5795e57d5e5)
                            (readBlock
                            0x21885a1e45a17841168460e4591e4791687a1d845168420e4591e4791647a1e85a1d85e118401a850e739e10830200802079c1c4681e))) (branch
                            539 (branch 540 (readBlock
                            0x21e85a1845a17865f58487984df545a1245a117d51685e197d6127d6114591686219844a784df5459167d61985df5862117d61284df53d4f57d61785a127d61184df53d4f57d4f5)
                            (readBlock
                            0x21e85a1845a178491684614458eb3ad16862198451684a14458eb3ad163ae168621985e12844ff834f93d61183ce739ce73dcfd3ecef))
                            (readBlock
                            0x219876178621e858e7844e784df57d61683df5844e73d5f587a1684df5844e7795f57d61e8621129e144591639ce78621e85a1783916844e73ad1639ce739e1e862168761785116844e747916458e739ce7)))
                            (branch 539 (branch 537 (branch 534 (readBlock
                            0x2168621e45a19875f584040831167d61045a127d5168661d7d6107d612459168761e84879831167d5f545a19875f5862107d612835f57c5f17d61d87a127d610835f57c5f17d5f1)
                            (readBlock
                            0x2168621e45a198411684a0c459184611687a1d849168420c45918461164621d8661e862128400884cf93e6108382008020420187e410))
                            (readBlock
                            0x21687a1885e1d864f9848f98511645a1983116848f93ad168761985116848f94611645a1d85e121e6137d5f53e4eb85e1d86618835f5848f93d5f53d4f93d61d85e1987a1884df5848f97c5f57d4f93e4eb))
                            (readBlock
                            0x21a85a1887a178661d082100820e459168760c45a100811e45a198760e45a10081184591685e1984040835f57d420082178661d87a0d7d610081e57d42008020866178761887a0f7d610081f17d5f508020082168621e85e198760f835f584df545a0c83916080203ad1e460f5795f1)))
                            (readBlock 0x21a85e1986e1c7d61d7d4408721d7d4401021c86e1d7d5167d43e86e1c8661d7d516459f50e21c85e1d8661b7d4f53d4ff3d4f5))
                            (readBlock
                            0x21a85a188a21b87116879161021c8791610040841163fe1c86e1e459164583c86e1c8621e45916459160c21b8621e87216458eb3acff3aceb))
                            (branch 537 (readBlock
                            0x2198621b89e2885a178761e082100820f794e787a0e47a10080e71021e8761139e0e45820458208761787a0f7961129c207d4a70820f7d51e8404039e1685e1d87820080200802086e1d85e1e859e5795e5795e50821b8621e85a1d85d1e4791e4791e06820)
                            (readBlock 0x2188661b8761e85a1739ce739ce739ce139ce7))) (branch 549 (branch 537 (readBlock
                            0x21685e278a21c862198761e082100820d7c4f987a100820c460f91021e876123e60c45820458208761987a123e60d7d4207d479082188661d878200802008020835f546210100f98721887a1d8651846118461180821c85e198761e861f17c5f17c5f102020)
                            (readBlock 0x21685e1c8761e862193e4f93e4f93e4e13e4f9)) (readBlock 0x20))) (readBlock
                            0x2268962889e1686a18871168791647a1c87a1b458794581a8721e86e18458791e47d47a1c86e1a87a1845916459165e51e45a127d516848794591e))
                            (readBlock
                            0x22589a2889e238621a86e1645a1c87916458a78721e85916021184621b87a1c8591629ca72dd1886e1c86a1e8591645916459a74611645a117d516844a745918))
                            (branch 551 (branch 549 (branch 548 (branch 550 (branch 544 (readBlock
                            0x2238761b8721e8621685e1939e123e6143ace78661139e143acf545a1985e1139e137d4eb29ce785e16866123e6137d4e71e5f539e1786616860f53d4f53d4f587a188661685ce739ce739ce739e1e8721685e18864f93e4f93e4f9384f586e1c87a1686217864eb3aceb3aceb3fce73ae14458f5)
                            (readBlock 0x214458f5)) (readBlock 0xeb)) (readBlock 0xf9)) (readBlock 0xe7)) (readBlock 0xf5))) (readBlock
                            0x226886248962788e288721685e1a86df5875f57d61d86df51e47b86a1b875f5459187d61b876177d5f57d5f585e1a86e1d865f5069e5795e5795f5849f506a12459f5848797d6121e5f5849167d5e5))
                            (readBlock
                            0x22589e2389a248862888a1b8721a875f5865f545a1d865f57d4af87619869f529d1e7d61986a1c876177d4087c5f17c5f17d5f5845f50221129df5844a77d611459f5845167d5f1))
                            _ _ low high
                          decide +kernel
                      · intro low high
                        apply search_boxes x _ leaf valid (branch 544 (branch 550 (branch 549 (readBlock
                          0x2238922587e208a21c87617865f586df51e61b87a151e5f57d47985e1686a151e5f51e5f51e61d85e15866161e5f51e5f51e47985e1c8761a7d5f57d5f56d61d85e1c86df57d5f57d5d5872178761b7d5f57d5f5796178721d854791e4791e5888761c85e1e1e4791e4791ee1c87617858791e4791e47a)
                          (readBlock 0x217876198561a86e168783c7d5f51e4797947a0f1a7)) (readBlock 0x21c85e1a85a1587a1b8643c1e4797d5f57547b6583c))
                          (readBlock 0x21d8721b87a1585a19869881e4797d5f56d58869d96)) _ _ low high
                        decide +kernel
                    · intro low high
                      apply search_boxes x _ leaf valid (branch 542 (branch 550 (branch 551 (readBlock
                        0x2218822688a23896158761e85c798587929e17866161e4a71e4a787a168621c1e4a71e4a71e61d87a1b872171e4a729c791e4798561d87a161e4791e4793e61e87615870791e4791e47d8761e8561c1e4791e4791ee158761e860a729ca729ce78761587a1b29ca729ca72be1e8761586ca729ca729cb7)
                        (readBlock 0x21d856178661c85a1886c3f1e47929ca71f4b73d43f)) (readBlock 0x21e856168621c85e1986c3f1e47929ca71ecaf3ac3f))
                        (readBlock 0x21d87a1b8721685e18864e71e47929ca739cf93d4eb)) _ _ low high
                      decide +kernel
                  · intro low high
                    apply search_boxes x _ leaf valid (branch 542 (branch 543 (branch 544 (readBlock
                      0x22488a238a22789a1785a1587079864401021c86a18100791e4408561d8661a100791e4401021585a1e86219100791e440100408561785a1810040100400821685e1586040100401003085e1585a1a10040100400e21685617870791e4791e57985e1585a1c1e4791e4796221585a17874791e4791e4f9)
                      (readBlock 0x21585a1e8621986a1d87038100401e479620382a118)) (readBlock 0x21585e1d8661886a1c87830100401e4795e4302a1f1)) (readBlock
                      0x21685e1c86a188661e87420100401e4793e420461f1)) _ _ low high
                    decide +kernel
                · intro low high
                  apply search_boxes x _ leaf valid (branch 543 (branch 551 (branch 549 (readBlock
                    0x22588a2489e1f886168721e86116854791e61786a151e5161e51687a158621d1e5161e5161e61e8721b876171e516458791e47987a168721b45916459164da1c87a1686d16459164591e85a1c87a1a459164591655a1e87216874791e4791e47d8721687a171e4791e4791ea1687a1c854791e4791e579)
                    (readBlock 0x21687a188561a86e1d85c3e459161e4794787a0f95a)) (readBlock 0x21c85a1a85e1886e158743e459161e4794d87d5d43e)) (readBlock
                    0x21c87a1d86e1585e18869561e479459165e5565d55a)) _ _ low high
                  decide +kernel
              · intro low high
                apply search_boxes x _ leaf valid (branch 542 (branch 545 (branch 546 (readBlock
                  0x220886248a22589e198621586ca7874a71021a86e16100a7100a7856178761a100a7100a7102158621687a17100a7100a710040862198561a10040100400f2158621985c401004010020866158621a10040100400fa1586219874a729ca729ce7862158661b29ca729ca769e198621586ca729ca729d5a)
                  (readBlock 0x2158621e85a1786a1d86c3e1004029ca75683e1e91e)) (readBlock 0x2158661d85e1686a1b8783c1004029ca769c3c1e9e5)) (readBlock
                  0x2188661b86a1785a1e874201004029ca739c20479e5)) _ _ low high
                decide +kernel
            · intro low high
              apply search_boxes x _ leaf valid (branch 551 (branch 548 (branch 545 (readBlock
                0x2268822489e1f88e1e86e1885916854a729e1c8761929d16458a7862168561c458a7458a729e1886e1986a1529d1629d1629ca787a1886e1c45916459164da1b87a188711645916459188621b87a1a459164591665a1e86e18874a729ca729cb786e1887a1929ca729ca72a21887a1b864a729ca729da7)
                (readBlock 0x21b87a1c87615866168698829ca745916659a76d588)) (readBlock 0x21887a16856198761c8683829ca745916460a80e188)) (readBlock
                0x21b8621a8661687215874384591629ca74d8b76d438)) _ _ low high
              decide +kernel
          · intro low high
            apply search_boxes x _ leaf valid (branch 550 (branch 546 (branch 548 (readBlock
              0x2218922687e228a21986e1d854a7871f529e1886a1529df529df58761585e1829df529df529e1b8761c87a1529df57d4a729ca78661b8761a7d5f57d5f55d61d8661b871f57d5f57d5d586e198761c7d5f57d5f57c6198761b860a729ca729d5a8761986e1e29ca729ca72be1b87619878a729ca729ca8)
              (readBlock 0x219876178561a8721e860307d5f529ca77c4a80c179)) (readBlock 0x21b8761e87215862178695629ca77d5f55697555979)) (readBlock
              0x21b8661a8621587a1c85c3029ca77d5f5754af55830)) _ _ low high
            decide +kernel
        · intro low high
          apply search_boxes x _ leaf valid (branch 544 (branch 547 (branch 546 (readBlock
            0x22589e2687e2088a178661a85440858407d61d85616101f57d44086a1c85a15101f57d4401021986a1b86215101f57d4401004085e1986a1d7d5f57d5f56d61985e1a875f57d5f57d57586a178661c7d5f57d5f53d61985e1a85440100401003e86a178661610040100400fe178661a858401004010038)
            (readBlock 0x21786a1c85a158621b8743e100407d5f55d43e1f536)) (readBlock 0x21786615876168621b8703f100407d5f50fcf51f4b7)) (readBlock
            0x21986a1b862168561c87438100407d5f56d4382dd36)) _ _ low high
          decide +kernel
      · intro low high
        apply search_boxes x _ leaf valid (branch 547 (branch 545 (branch 543 (readBlock
          0x22187e238a2268961a85a1886d16871161021c85e1510116458408621986e151011610116102168621e8561b45840458401004085a1a8621710040100400c21886a1686440100401003c86a168621910040100400fe168621a87916459164595686a168621c45916459163ae1885a1a879164591645996)
          (readBlock 0x21886a1b8661585e1c878301004045916558302bdd5)) (readBlock 0x21686a1c85e198561b8783c10040459166583c1edd5)) (readBlock
          0x2168621587a178661b8703f10040459160fceb1ecaf)) _ _ low high
        decide +kernel
    · intro low high
      apply search_boxes x _ leaf valid (branch 547 (branch 548 (branch 549 (readBlock
        0x228882228862389e1a86e1c85916879167d61886616459f5459f58721685e18459f5459f545a1b8721d87a16459f57d5164591686a1c86e1645916459163ae1c86a1b87916459164591e86e1c86a1e45916459164621c86a1b875f57d5f57d5e586e1a8721d7d5f57d5f57c61a86e1c85df57d5f57d4f5)
        (readBlock 0x21a86e188661687a1787420459167d5f5479e5080e7)) (readBlock 0x21a8721685e1d86618878207d5f545916461f1080f9)) (readBlock
        0x21b8721d87a1686217864e7459167d5f53d4eb39cf9)) _ _ low high
      decide +kernel
  exact done positive cap

/-- A cut constant on the fibers charges at most the product of the two
fiber sizes for each monochromatic template edge, in each orientation. -/
private lemma fiber_cut {V : Type*} [DecidableEq V] (W : Finset V) (G : SimpleGraph V)
    (f : V → Fin 10) (E : Finset (Fin 10 × Fin 10))
    (hom : ∀ i ∈ W, ∀ j ∈ W, G.Adj i j → (f i,f j)∈E ∨ (f j,f i)∈E)
    (m : ℕ) :
    let w (a : Fin 10) := (W.filter (fun i => f i=a)).card
    (∑ i∈W,∑ j∈W,if G.Adj i j ∧ m.testBit (f i).val=m.testBit (f j).val then (1:ℕ) else 0)
      ≤ 2*(∑ e ∈ E, if m.testBit e.1.val=m.testBit e.2.val then w e.1*w e.2 else 0) := by
  classical
  intro w
  let rect (e : Fin 10 × Fin 10) (i j : V) := if f i=e.1 ∧ f j=e.2 then (1:ℕ) else 0
  let M := E.filter (fun e => m.testBit e.1.val=m.testBit e.2.val)
  have side (e) : (∑ i∈W, ∑ j∈W,rect e i j)=w e.1*w e.2 := by
    have row (i) : (∑ j∈W,rect e i j)=if f i=e.1 then w e.2 else 0 := by
      by_cases h : f i=e.1 <;> simp only [rect,h,true_and,false_and,if_true,if_false,sum_const_zero,w,card_filter]
    simp_rw [row]
    rw [←sum_filter]
    simp [w]
  have point (i) (hi : i∈W) (j) (hj : j∈W) :
      (if G.Adj i j ∧ m.testBit (f i).val=m.testBit (f j).val then 1 else 0) ≤
        ∑ e∈M,(rect e i j+rect e j i) := by
    split
    · rename_i h
      rcases hom i hi j hj h.1 with hE|hE
      · have he : (f i,f j)∈M := mem_filter.mpr ⟨hE,h.2⟩
        apply le_trans _ (single_le_sum (f:=fun e => rect e i j+rect e j i) (fun _ _ => Nat.zero_le _) he)
        simp [rect]
      · have he : (f j,f i)∈M := mem_filter.mpr ⟨hE,h.2.symm⟩
        apply le_trans _ (single_le_sum (f:=fun e => rect e i j+rect e j i) (fun _ _ => Nat.zero_le _) he)
        simp [rect]
    · exact Nat.zero_le _
  calc
    _ ≤ ∑ i∈W, ∑ j∈W, ∑ e∈M,(rect e i j+rect e j i) :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => point i hi j hj
    _ = ∑ e∈M, ∑ i∈W, ∑ j∈W,(rect e i j+rect e j i) := by
      calc
        _ = ∑ i∈W, ∑ e∈M, ∑ j∈W,(rect e i j+rect e j i) := sum_congr rfl fun _ _ => sum_comm
        _ = _ := sum_comm
    _ = ∑ e∈M, 2*(w e.1*w e.2) := by
      apply sum_congr rfl; intro e _
      simp only [sum_add_distrib]
      rw [sum_comm (f:=fun i j => rect e j i),side]; omega
    _ = _ := by rw [←mul_sum]; simp only [M,sum_filter]

private lemma fiber_mass {V : Type*} (W : Finset V) (f : V → Fin 10) :
    (∑ a,(W.filter (fun i => f i=a)).card)=W.card :=
  (card_eq_sum_card_fiberwise (t:=univ) (f:=f) (fun _ _ => mem_univ _)).symm

/-- A class-constant cut on either of the two representatives loses at most
sixteen undirected edges after replacing its vertices by ten nonempty fibers. -/
lemma ten_class_cut (G : SimpleGraph (Fin 22))
    (sat : Maximal (fun K : SimpleGraph (Fin 22) => K.CliqueFree 3) G) (size : (univ.image (fun i => G.neighborFinset i)).card=10) :
  ∃ c : Fin 22 → Bool, (∑ i,∑ j,if G.Adj i j ∧ c i=c j then (1:ℕ) else 0) ≤ 32 := by
  obtain ⟨k,classes,f,onto,edge⟩ := two_templates G sat size
  let x (a : Fin 10) := (univ.filter (fun i => f i=a)).card
  have positive (a) : 1≤x a := by
    obtain ⟨i,hi⟩ := onto a
    exact card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  have mass : ∑ a,x a=22 := (fiber_mass univ f).trans (by simp)
  rcases classes with rfl|rfl
  · let E : Finset (Fin 10 × Fin 10) := {(0,7),(0,8),(0,9),(1,6),(1,7),(1,8),(2,5),(2,7),(2,9),(3,4),(3,5),(3,6),(3,7),(4,8),(4,9),(5,8),(6,9)}
    let link (a b : Fin 10) := (0x1543303e0a433083c2a070380 : ℕ).testBit (10*a.val+b.val)
    have decode : ∀ a b,(!link a b || (decide ((a,b)∈E) || decide ((b,a)∈E)))=true := by decide +kernel
    have align : ∀ a b : Fin 10,(0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*29+10*a.val+b.val)=link a b := by decide +kernel
    have hom (i j) (h : G.Adj i j) : (f i,f j)∈E ∨ (f j,f i)∈E := by
      have he := (edge i j).1 h
      change (0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*29+10*(f i).val+(f j).val)=true at he
      rw [align] at he
      simpa only [he,Bool.not_true,Bool.false_or,Bool.or_eq_true,decide_eq_true_eq] using decode (f i) (f j)
    obtain ⟨m,hm⟩ := weights_29 x positive mass
    have bound := fiber_cut univ G f E (fun i _ j _ => hom i j) m
    exact ⟨fun i => m.testBit (f i).val,bound.trans (Nat.mul_le_mul_left 2 hm)⟩
  · let E : Finset (Fin 10 × Fin 10) := {(0,5),(0,6),(0,7),(1,4),(1,6),(1,8),(2,3),(2,6),(2,9),(3,7),(3,8),(4,7),(4,9),(5,8),(5,9)}
    let link (a b : Fin 10) := (0xd02a06407c068261248540e0 : ℕ).testBit (10*a.val+b.val)
    have decode : ∀ a b,(!link a b || (decide ((a,b)∈E) || decide ((b,a)∈E)))=true := by decide +kernel
    have align : ∀ a b : Fin 10,(0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*30+10*a.val+b.val)=link a b := by decide +kernel
    have hom (i j) (h : G.Adj i j) : (f i,f j)∈E ∨ (f j,f i)∈E := by
      have he := (edge i j).1 h
      change (0xd02a06407c068261248540e01543303e0a433083c2a0703801941303e0a8290c3c290783800941303c0f8290c3c2d0783c00cc3303c0fc330c3c0f0f03c00b81903c0f84526f02d0b41e00a81901c0781506c10f8b41e04ca0901c0781605418f8b21f02580f9a08721e0964360d8170268079908320e0581598d8178228079d08320c8381588dc1781cc0f03e0c8320c7c1f0e03800dc0f03c0f822087c3c0f03c00cc0f03c0f8320c7c1f0f03c00c40f03c0f83a0e7c1f07c3c004c0f03c0f03e0c7c1f0f83e00440f03c0f03e0e7c1f07c3e01ec0701e0481204811f8e03800ec0701c0781204811f8f03c00e40701c0781a06819f87e3c006c0701c0701e04811f8f83e00640701c0701e06819f87e3e00240701c0701c07819f87e3f003cfe4050140501c0300c02f001cfe405014050140700c02f800cfe405014050140501c02fc07c1f07c1f07fe0f83e0f83e003c0f03c0f03c0ffc3f0fc3f001c0701c0701c0701ff8fe3f87fa01806018060180601805fe00401004010040100401007fe : ℕ).testBit (100*30+10*(f i).val+(f j).val)=true at he
      rw [align] at he
      simpa only [he,Bool.not_true,Bool.false_or,Bool.or_eq_true,decide_eq_true_eq] using decode (f i) (f j)
    obtain ⟨m,hm⟩ := weights_30 x positive mass
    have bound := fiber_cut univ G f E (fun i _ j _ => hom i j) m
    exact ⟨fun i => m.testBit (f i).val,bound.trans (Nat.mul_le_mul_left 2 hm)⟩

/-- In each pentagon choose a monochromatic edge. Charge its weight to that
edge. A verified per-edge capacity converts the total charge into a cut bound. -/
private lemma charge_cycles {n : ℕ} (adj : Fin 22 → Fin 22 → Bool)
    (v : Fin n → Fin 5 → Fin 22) (w : Fin n → ℕ)
    (mark : Fin n → Fin 22 → Fin 22 → Bool) (D : ℕ)
    (cycle : ∀ t a, let i := min (v t a) (v t (a+1)); let j := max (v t a) (v t (a+1))
      i<j ∧ adj i j=true ∧ mark t i j=true)
    (capacity : ∀ i j, i<j → adj i j=true → (∑ t,if mark t i j then w t else 0) ≤ D)
    (heavy : 16*D < ∑ t,w t) (c : Fin 22 → Bool) :
    17 ≤ ∑ i,∑ j,if i<j ∧ adj i j=true ∧ c i=c j then (1:ℕ) else 0 := by
  let bad := (univ : Finset (Fin 22 × Fin 22)).filter
    (fun e => e.1<e.2 ∧ adj e.1 e.2=true ∧ c e.1=c e.2)
  have odd : ∀ b : Fin 5 → Bool, ∃ a,b a=b (a+1) := by decide +kernel
  have paid (t) : w t ≤ ∑ e∈bad,if mark t e.1 e.2 then w t else 0 := by
    obtain ⟨a,ha⟩ := odd (fun j => c (v t j))
    let i := min (v t a) (v t (a+1))
    let j := max (v t a) (v t (a+1))
    obtain ⟨lt,edge,used⟩ := cycle t a
    have eq : c i=c j := by
      rcases le_total (v t a) (v t (a+1)) with h|h
      · simpa only [i,j,min_eq_left h,max_eq_right h] using ha
      · simpa only [i,j,min_eq_right h,max_eq_left h] using ha.symm
    have he : (i,j)∈bad := mem_filter.mpr ⟨mem_univ _,lt,edge,eq⟩
    have h := single_le_sum (f:=fun e : Fin 22 × Fin 22 => if mark t e.1 e.2 then w t else 0)
      (fun _ _ => Nat.zero_le _) he
    simpa only [show mark t i j=true from used,if_true] using h
  have bound : (∑ t,w t) ≤ bad.card*D := by
    calc
      _ ≤ ∑ t,∑ e∈bad,if mark t e.1 e.2 then w t else 0 := sum_le_sum fun t _ => paid t
      _ = ∑ e∈bad,∑ t,if mark t e.1 e.2 then w t else 0 := sum_comm
      _ ≤ ∑ _e∈bad,D := sum_le_sum fun e he => capacity _ _ (mem_filter.mp he).2.1 (mem_filter.mp he).2.2.1
      _ = _ := by simp
  have h : 17 ≤ bad.card := by
    by_contra! small
    have := Nat.mul_le_mul_right D (show bad.card≤16 by omega)
    omega
  simpa only [bad,card_filter,Fintype.sum_prod_type] using h

set_option maxRecDepth 30000 in
set_option maxHeartbeats 40000000 in
/-- McKay record 198 has bipartization number seventeen. -/
lemma witness_minimum :
  let rows : Fin 1 → ℕ := ![0x941d3a2a00e0701c5285282941a0e341c341c0521fd23f0290fca47e00]
  let bit (word : ℕ) (i j : Fin 22) :=
    let hi := max i.val j.val
    let pos := hi*(hi-1)/2+min i.val j.val
    decide (i≠j) && word.testBit (233-pos)
  ∀ k : Fin 1, IsLeast (Set.range (fun c : Fin 22 → Bool =>
    ∑ i,∑ j,if i<j ∧ bit (rows k) i j=true ∧ c i=c j then (1:ℕ) else 0)) 17 := by
  intro rows bit
  let masks : Fin 1 → ℕ := ![0x2bf0d4]
  have cuts : ∀ k : Fin 1, (∑ i : Fin 22,∑ j : Fin 22, if i<j ∧ bit (rows k) i j=true ∧
      (masks k).testBit i.val=(masks k).testBit j.val then (1:ℕ) else 0)=17 := by decide +kernel
  let weightWords : Fin 1 → ℕ := ![0x11a106062a0c08b02201071840481123428f0c40481023820606042042e204850438b0110043160204301103880f24103840224684140430e]
  let w (k : Fin 1) (t : Fin 65) := ((weightWords k) >>> (7*t.val))%128
  let vertices : Fin 1 → Fin 65 → ℕ := ![![0x7a08c0,0x11a08c0,0xfa30c0,0x10a34c0,0x860ce0,0x15148e0,0x1190900,0x1009100,0xfa1100,0xf1b100,0x1093900,0x156c9e0,0x1375200,0x1364a20,0xf52041,0x105a041,0xf4cc41,0x1154c41,0x74d441,0xd31481,0xc328e1,0xd42ce1,0xc9ace1,0xf59981,0x11599a1,0x1054da1,0x11599c1,0xf54dc1,0xf5cdc1,0x115d5c1,0x1554062,0x135c062,0x12214c2,0x12824c2,0x147a8c2,0x1549e82,0x1559e82,0xda10a3,0x11498a3,0x7598a3,0x115cca3,0x7554a3,0xcaace3,0xf599a3,0x11521a3,0xf4cda3,0xf4a1c3,0x8718a4,0x1264ca4,0x12654a4,0x123a504,0xda3d26,0xea4546,0x1262127,0x1474d27,0xe94148,0xca3d68,0xc94568,0xe94568,0x1574a09,0x1565209,0x1365229,0x136d229,0x156c9ea,0x1574a2a]]
  let v (k : Fin 1) (t : Fin 65) (a : Fin 5) : Fin 22 :=
    Fin.ofNat 22 (((vertices k t) >>> (5*a.val))%32)
  let marked : Fin 1 → Fin 65 → ℕ := ![![0x5100000000000000000000000000000000000000000021000000000,0x5000000000000000000000000000002000000000000020004000000,0x4000000000000020000000100000000000000000000000090000000,0x4000000000000000020000000020000000000000000000048000000,0x122000000000108000000000000000000000000000000000000000,0x100000000000000000000000000000000042000000000000a00000,0x2800000000000000000000000002000040008000000000000000,0x400002200000000000000000000030000000000000000000000000000,0x2200000000000000000100000000000000000000008010000000,0x2000000000108000000120000000000000000000000000000000,0x2000000000000000004000020000000000050000000000000000,0x1000000000000000a0000000000800400,0x20000000000004001000028000000,0x200000010c004000000000000,0x8000000800001000000000000080400000000000000000000000000000,0x8000000800000004000000000000010040000000000000000000000000,0x8000000000000000000000000080800000000000001020000000000000,0x8000000000000000000000000000000001008000001010000000000000,0x8000080000400000000000000000000000000000000000000000204000,0x408200000000000000420000000000000000000000000000000000000,0x80000006000420000000000000000000000000000000000000000,0x8000000000c000408000000000000000000000000000000000000,0x8000000000840000000000000000000000000000c000000000000,0x10420000000080200000000000000000000000000000,0x10000420000000000001004000000000000000000000,0x400000000010080000000000012000000000000,0x10000000210000000001004000000000000000000000,0x200080400000000000000011000000000000,0x200080200000000000000009000000000000,0x200000000001004000000000000000001200,0x1000000000000000000000000000004080000000000000000000202000,0x1000000000000000000000000000004040000000001008000000000000,0x9200000000000000000000000000000000050000000000000000000,0x1000000800000000000000000000100000040010000000000000000,0x1000000004000000000000000400000000000000000020010000000,0x400000000000000000000000000000000000021000204000,0x8000000000000000000000000000000021000201000,0x18000000000000000100000000000000000000000000008040000000,0x10200000800000000000000000000000410000000000000000000000,0x10220000000018000000000000000000000000000000000000000000,0x10000000000000000000000000000000404000000208000000000000,0x10020000002000000000000000000000000000000000000000042000,0x20000000008100000000000000000000000000000000000001800,0x10000120000020200000000000000000000000000000,0x1000000108000000000000408000000000000000000000,0x100000020800000000000000022000000000000,0x200000000000084020800000000000000000000000000000,0x8200200000000000000014000000000000000000000000000000000,0x8000000000000000000000000000000000010100204000000000000,0x8000000000000000000000000000000000010100000000000040800,0x200600000000000000000000000000012000000000000000000,0x800000000020000000800000000000000000000050000000,0x4000000000010000000000008000000000000024000000,0x600000008000000000000000000002100000000000000000,0x400000000000000000000000000000000021001020000000,0x1000000000004000000080000000050000000000000000,0x4008000000000200000000000000000000090000000,0x4008000000000000000004000108000000000000000,0x4000000004000000000004000048000000000000000,0x100000000050000000000004200,0x100000000000000000088004800,0x10000000024000084000000,0x10000000022000044000000,0x4000000000000a0000000000002400,0x8000048000000000002200]]
  let D : Fin 1 → ℕ := ![0x20]
  have cycle : ∀ k t a, let i := min (v k t a) (v k t (a+1)); let j := max (v k t a) (v k t (a+1))
      i<j ∧ bit (rows k) i j=true ∧ bit (marked k t) i j=true := by decide +kernel
  have capacity : ∀ k i j, i<j → bit (rows k) i j=true →
      (∑ t,if bit (marked k t) i j then w k t else 0) ≤ D k := by decide +kernel
  have heavy : ∀ k, 16*D k < ∑ t,w k t := by decide +kernel
  intro k
  refine ⟨⟨fun i => (masks k).testBit i.val,cuts k⟩,?_⟩
  rintro _ ⟨c,rfl⟩
  exact charge_cycles (bit (rows k)) (v k) (w k) (fun t => bit (marked k t)) (D k)
    (cycle k) (capacity k) (heavy k) c
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Record 198 is maximal triangle-free. -/
lemma witness_maximal :
  let rows : Fin 1 → ℕ := ![0x941d3a2a00e0701c5285282941a0e341c341c0521fd23f0290fca47e00]
  let bit (word : ℕ) (i j : Fin 22) :=
    let hi := max i.val j.val
    let pos := hi*(hi-1)/2+min i.val j.val
    decide (i≠j) && word.testBit (233-pos)
  ∀ k : Fin 1,∃ B : SimpleGraph (Fin 22),
    (∀ i j,B.Adj i j ↔ bit (rows k) i j=true) ∧
    Maximal (fun T : SimpleGraph (Fin 22) => T.CliqueFree 3) B := by
  intro rows bit
  have sym : ∀ k i j,bit (rows k) i j=bit (rows k) j i := by decide +kernel
  have diag : ∀ k i,bit (rows k) i i=false := by decide +kernel
  have triangles : ∀ k i j v,bit (rows k) i j=true → bit (rows k) i v=true →
      bit (rows k) j v=false := by decide +kernel
  have saturated : ∀ k i j,i≠j → bit (rows k) i j=false →
      ∃ v,bit (rows k) i v=true ∧ bit (rows k) j v=true := by decide +kernel
  intro k
  let B : SimpleGraph (Fin 22) := {
    Adj := fun i j => bit (rows k) i j=true
    symm := ⟨fun i j h => (sym k i j).symm.trans h⟩
    loopless := ⟨fun i h => Bool.noConfusion ((diag k i).symm.trans h)⟩ }
  refine ⟨B,fun _ _ => Iff.rfl,?_,?_⟩
  · rintro s h
    obtain ⟨a,b,c,ab,ac,bc,_⟩ := is3Clique_iff.mp h
    exact Bool.noConfusion ((triangles k _ _ _ ab ac).symm.trans bc)
  · intro T cf sub i j adj
    by_contra absent
    change ¬bit (rows k) i j=true at absent
    obtain ⟨v,iv,jv⟩ := saturated k i j adj.ne (by simpa using absent)
    exact cf _ (is3Clique_triple_iff.mpr ⟨adj,sub (show B.Adj i v from iv),sub (show B.Adj j v from jv)⟩)

private lemma twice_loss {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Bool) :
    (∑ i,∑ j,if G.Adj i j ∧ c i=c j then (1:ℕ) else 0) =
    2*(∑ i,∑ j,if i<j ∧ G.Adj i j ∧ c i=c j then (1:ℕ) else 0) := by
  let h (i j : Fin n) := if i<j ∧ G.Adj i j ∧ c i=c j then (1:ℕ) else 0
  have split (i j) : (if G.Adj i j ∧ c i=c j then (1:ℕ) else 0) = h i j+h j i := by
    rcases lt_trichotomy i j with l|rfl|l
    · simp [h,l,not_lt_of_gt l]
    · simp [h]
    · simp [h,l,not_lt_of_gt l,G.adj_comm i j,eq_comm (a:=c i) (b:=c j)]
  calc
    _ = ∑ i, ∑ j, (h i j+h j i) := sum_congr rfl fun i _ => sum_congr rfl fun j _ => split i j
    _ = _ := by
      simp only [sum_add_distrib]
      rw [sum_comm (f:=fun i j => h j i)]
      change _ + _ = 2*(∑ i,∑ j,h i j)
      omega

/-- A maximal triangle-free order-22 global extremizer cannot have exactly
ten distinct open neighborhoods. No assumption on a map to nine vertices is needed. -/
lemma extremizer_not_ten (G : SimpleGraph (Fin 22))
    (sat : Maximal (fun K : SimpleGraph (Fin 22) => K.CliqueFree 3) G) :
  let loss (K : SimpleGraph (Fin 22)) (c : Fin 22 → Bool) :=
    ∑ i,∑ j,if K.Adj i j ∧ c i=c j then (1:ℕ) else 0
  let best (K : SimpleGraph (Fin 22)) := (univ.image (loss K)).min' (univ_nonempty.image _)
  (∀ K : SimpleGraph (Fin 22), K.CliqueFree 3 → best K ≤ best G) →
  (univ.image (fun i => G.neighborFinset i)).card≠10 := by
  intro loss best extreme size
  obtain ⟨c,hc⟩ := ten_class_cut G sat size
  obtain ⟨B,decodeB,maxB⟩ := witness_maximal 0
  have attained : ∃ c,loss B c=best B := by
    simpa only [mem_image,mem_univ,true_and] using (min'_mem (univ.image (loss B)) (univ_nonempty.image _))
  obtain ⟨b,hb⟩ := attained
  have floor : 34 ≤ best B := by
    rw [←hb]
    have low := (witness_minimum 0).2 (Set.mem_range_self b)
    have dbl := twice_loss B b
    have lb : 17 ≤ ∑ i,∑ j,if i<j ∧ B.Adj i j ∧ b i=b j then (1:ℕ) else 0 := by
      simpa only [decodeB] using low
    change 34 ≤ ∑ i,∑ j,if B.Adj i j ∧ b i=b j then (1:ℕ) else 0
    omega
  have high : 34 ≤ loss G c :=
    (floor.trans (extreme B maxB.1)).trans (min'_le _ _ (mem_image_of_mem _ (mem_univ c)))
  change loss G c ≤ 32 at hc
  omega

end TenClasses

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3.H1 := by
  classical
  intro family remaining G tri
  let loss (K : SimpleGraph (Fin 22)) (c : Fin 22 → Bool) :=
    ∑ i,∑ j,if K.Adj i j ∧ c i=c j then (1:ℕ) else 0
  let best (K : SimpleGraph (Fin 22)) := (univ.image (loss K)).min' (univ_nonempty.image _)
  let U := {T : SimpleGraph (Fin 22) // T.CliqueFree 3}
  let _ : Fintype U := Fintype.ofFinite U
  obtain ⟨m,_,maxM⟩ := exists_max_image (univ : Finset U) (fun a : U => best a.val)
    ⟨⟨G,tri⟩,mem_univ _⟩
  let M := m.val
  obtain ⟨K,sub,sat⟩ := Finite.exists_le_maximal (p:=fun T : SimpleGraph (Fin 22) => T.CliqueFree 3)
    (show M.CliqueFree 3 from m.property)
  have attained (T : SimpleGraph (Fin 22)) : ∃ c,loss T c=best T := by
    simpa only [mem_image,mem_univ,true_and] using (min'_mem (univ.image (loss T)) (univ_nonempty.image _))
  obtain ⟨k,hk⟩ := attained K
  have monotone : best M ≤ best K := by
    rw [←hk]
    apply (min'_le _ _ (mem_image_of_mem (loss M) (mem_univ k))).trans
    apply sum_le_sum; intro i _
    apply sum_le_sum; intro j _
    by_cases h : M.Adj i j ∧ k i=k j
    · simp [h.1,show K.Adj i j from sub h.1,h.2]
    · simp [h]
  have global (T : SimpleGraph (Fin 22)) (h : T.CliqueFree 3) : best T ≤ best K :=
    (maxM ⟨T,h⟩ (mem_univ _)).trans monotone
  obtain ⟨c,hc⟩ : ∃ c,loss K c≤34 := by
    by_cases small : (univ.image (fun i => K.neighborFinset i)).card ≤ 9
    · exact family K sat global small
    · have excluded := extremizer_not_ten K sat global
      exact remaining K sat global (by omega)
  obtain ⟨d,hd⟩ := attained G
  exact ⟨d,hd.le.trans ((global G tri).trans
    ((min'_le _ _ (mem_image_of_mem (loss K) (mem_univ c))).trans hc))⟩

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3_H1_R2
