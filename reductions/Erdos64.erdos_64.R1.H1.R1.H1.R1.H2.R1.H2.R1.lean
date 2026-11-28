import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1
import Mathlib

/-!
# Power-of-two cycles in abelian covers with eleven quotient coordinates

The three matching edges over the cyclic quotient either have three distinct
shifts or have a repeated shift. In the first case, short quotient cycles and
closed traversals of theta graphs give incompatible voltage conditions if all
4-, 8-, 16-, and 32-cycles are absent. In the second case, two consecutive
pairs of parallel matchings give a ladder; the remaining equal-increment case
uses the local commutation result from the parent matching reduction.

A point stabilizer contained in the abelian kernel gives the fiber coordinates
even when that stabilizer is nonnormal in the generated permutation group.
The two remaining steps treat groups without such a kernel and actions where
every stabilizer projects onto the quotient. This extends the regular-action
argument of PR 7828 and the matching reductions in PRs 592, 5246 and 5820.
-/

namespace NonfreeEleven
open SimpleGraph

/-- A closed template in the base graph lifts to a simple cycle when every edge discrepancy
vanishes in the deck group and repeated base vertices have different deck coordinates. -/
theorem template {V X L Q K : Type*} [AddCommGroup V] [AddCommGroup L]
    {n : ℕ} (G : SimpleGraph X) (ι : (Q × V) ↪ X) (F : L →+ V)
    (tail head : K → Q) (weight : K → L)
    (edges : ∀ (k : K) (g : V), G.Adj (ι (tail k,g)) (ι (head k,g+F (weight k))))
    (base : Fin (n+2) → Q) (level : Fin (n+2) → L) (label : Fin (n+2) → K)
    (cancel : L) (vanish : F cancel = 0) (forbidden : List L)
    (nonzero : ∀ a ∈ forbidden, F a ≠ 0)
    (separate : ∀ i j, i ≠ j → base i = base j → level i - level j ∈ forbidden)
    (walk : ∀ i, let j := i+1; let k := label i
      (base i=tail k ∧ base j=head k ∧
        level j-level i-weight k ∈ ([0,cancel,-cancel] : List L)) ∨
      (base j=tail k ∧ base i=head k ∧
        level i-level j-weight k ∈ ([0,cancel,-cancel] : List L))) :
    cycleGraph (n+2) ⊑ G := by
  let f (i : Fin (n+2)) := ι (base i,F (level i))
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    have pair := ι.injective eq
    have same : base i=base j := congrArg Prod.fst pair
    have h : F (level i) = F (level j) := congrArg Prod.snd pair
    exact nonzero _ (separate _ _ ne same) (by rw [map_sub,h,sub_self])
  have oriented (i j : Fin (n+2)) (k : K) (t : base i=tail k) (u : base j=head k)
      (h : level j-level i-weight k ∈ ([0,cancel,-cancel] : List L)) : G.Adj (f i) (f j) := by
    have hh : F (level j-level i-weight k)=0 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h|h
      · rw [h,map_zero]
      · rw [h,vanish]
      · rw [h,map_neg,vanish,neg_zero]
    rw [map_sub,map_sub] at hh
    have e : F (level j)=F (level i)+F (weight k) := by abel_nf at hh ⊢; linear_combination (norm := abel) hh
    change G.Adj (ι (base i,F (level i))) (ι (base j,F (level j)))
    rw [t,u,e]
    exact edges _ _
  have step (i : Fin (n+2)) : G.Adj (f i) (f (i+1)) := by
    rcases walk i with ⟨t,u,h⟩|⟨t,u,h⟩
    · exact oriented _ _ _ t u h
    · exact (oriented _ _ _ t u h).symm
  refine ⟨⟨⟨f,?_⟩,inj⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with e|e
  · have h : i=j+1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp e)
    rw [h]; exact (step _).symm
  · have h : j=i+1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp e)
    rw [h]; exact step _

private theorem incompatible2 (p1 p2 p3 p4 p5 p6 p7 : Prop)
    (h0 : ¬p1 ∨ ¬p7)
    (h1 : ¬p3 ∨ ¬p2 ∨ p1)
    (h2 : ¬p1 ∨ ¬p6)
    (h3 : p3 ∨ p6)
    (h4 : p2 ∨ p4)
    (h5 : ¬p4 ∨ ¬p7)
    (h6 : p6 ∨ p7)
    (h7 : ¬p5 ∨ ¬p4 ∨ p1)
    (h8 : p5 ∨ p7)
    (h9 : ¬p2 ∨ ¬p6)
    : False := by tauto

set_option maxHeartbeats 8000000 in
private theorem cover2 {V X : Type*} [AddCommGroup V]
    (w : Fin 11 → Fin 3 → V) (G : SimpleGraph X) (ι : (Bool × Fin 11 × V) ↪ X)
    (edge : ∀ (i : Fin 11) (k : Fin 3) (g : V),
      G.Adj (ι (false,i,g)) (ι (true,i+(![0,1,2] : Fin 3 → Fin 11) k,g+w i k))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  let fiber : ((Bool × Fin 11) × V) ↪ X := (Equiv.prodAssoc Bool (Fin 11) V).toEmbedding.trans ι
  let idx : Fin 33 → Fin 11 := ![0,0,0,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5,6,6,6,7,7,7,8,8,8,9,9,9,10,10,10]
  let color : Fin 33 → Fin 3 := ![0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2]
  let tail (k : Fin 33) := (false,idx k)
  let head (k : Fin 33) := (true,idx k+(![0,1,2] : Fin 3 → Fin 11) (color k))
  let wt (k l : Fin 33) : ℤ := if k=l then 1 else 0
  let F : (Fin 33 → ℤ) →+ V := {
    toFun z := ∑ i, z i • w (idx i) (color i)
    map_zero' := by simp
    map_add' := by intro x y; simp [Pi.add_apply,add_zsmul,Finset.sum_add_distrib] }
  have edge' (k : Fin 33) (g : V) :
      G.Adj (fiber (tail k,g)) (fiber (head k,g+F (wt k))) := by
    have basis : F (wt k)=w (idx k) (color k) := by
      change (∑ j, (if k=j then (1:ℤ) else 0) • w (idx j) (color j)) = _
      simp [ite_smul]
    rw [basis]
    exact edge _ _ _
  let val (c : ℕ × ℕ) (i : Fin 33) : ℤ :=
    (if c.1.testBit i.val then 1 else 0) - (if c.2.testBit i.val then 1 else 0)
  by_contra absent
  have no4 : ¬cycleGraph 4 ⊑ G := fun h => absent (.inl h)
  have no8 : ¬cycleGraph 8 ⊑ G := fun h => absent (.inr (.inl h))
  have no16 : ¬cycleGraph 16 ⊑ G := fun h => absent (.inr (.inr (.inl h)))
  have no32 : ¬cycleGraph 32 ⊑ G := fun h => absent (.inr (.inr (.inr h)))
  let v0 := val (140,98)
  let v1 := val (608307332,287343169)
  let v2 := val (608307234,287343113)
  let v3 := val (612501636,304120385)
  let v4 := val (612501538,304120329)
  let v5 := val (4903274528,2434826760)
  let v6 := val (4907468832,2451603976)
  let v7 := val (4907468932,2451604034)
  have short_v7 : F v7 ≠ 0 := by
    intro eq
    apply no16
    let base : Fin 16 → Bool × Fin 11 := ![(false,0),(true,1),(false,10),(true,0),(false,9),(true,10),(false,8),(true,9),(false,7),(true,7),(false,5),(true,5),(false,3),(true,3),(false,2),(true,2)]
    let codes : Fin 16 → ℕ × ℕ := ![(0,0),(2,0),(2,4294967296),(2147483650,4294967296),(2147483650,4831838208),(2415919106,4831838208),(2415919106,4898947072),(2449473538,4898947072),(2449473538,4907335680),(2451570690,4907335680),(2451570690,4907466752),(2451603458,4907466752),(2451603458,4907468800),(2451603970,4907468800),(2451603970,4907468928),(2451604034,4907468928)]
    let labels : Fin 16 → Fin 33 := ![1,32,31,29,28,26,25,23,21,17,15,11,9,7,6,2]
    apply template (n:=14) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v7 eq []
    · simp
    · dsimp only [base,codes,val,v7]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v7]
      decide
  have identity0 : v7=v0 + v6 := by
    dsimp only [v7,v0,v6,val]
    decide
  have h0 : ¬F v0=0 ∨ ¬F v6=0 := by
    by_contra! bad
    apply short_v7
    rw [identity0]
    simp [bad.1,bad.2]
  have identity1 : v0=-v2 + v1 := by
    dsimp only [v0,v2,v1,val]
    decide
  have h1 : ¬F v2=0 ∨ ¬F v1=0 ∨ F v0=0 := by
    by_contra! bad
    apply bad.2.2
    rw [identity1]
    simp [bad.1,bad.2.1]
  let v8 := val (4903274628,2434826818)
  have short_v8 : F v8 ≠ 0 := by
    intro eq
    apply no16
    let base : Fin 16 → Bool × Fin 11 := ![(false,0),(true,1),(false,10),(true,0),(false,9),(true,10),(false,8),(true,8),(false,7),(true,7),(false,5),(true,5),(false,3),(true,3),(false,2),(true,2)]
    let codes : Fin 16 → ℕ × ℕ := ![(0,0),(2,0),(2,4294967296),(2147483650,4294967296),(2147483650,4831838208),(2415919106,4831838208),(2415919106,4898947072),(2432696322,4898947072),(2432696322,4903141376),(2434793474,4903141376),(2434793474,4903272448),(2434826242,4903272448),(2434826242,4903274496),(2434826754,4903274496),(2434826754,4903274624),(2434826818,4903274624)]
    let labels : Fin 16 → Fin 33 := ![1,32,31,29,28,26,24,22,21,17,15,11,9,7,6,2]
    apply template (n:=14) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v8 eq []
    · simp
    · dsimp only [base,codes,val,v8]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v8]
      decide
  have identity2 : v8=v0 + v5 := by
    dsimp only [v8,v0,v5,val]
    decide
  have h2 : ¬F v0=0 ∨ ¬F v5=0 := by
    by_contra! bad
    apply short_v8
    rw [identity2]
    simp [bad.1,bad.2]
  let v9 := val (2147483650,4294967297)
  have short_v9 : F v9 ≠ 0 := by
    intro eq
    apply no4
    let base : Fin 4 → Bool × Fin 11 := ![(false,0),(true,0),(false,10),(true,1)]
    let codes : Fin 4 → ℕ × ℕ := ![(0,0),(1,0),(1,2147483648),(4294967297,2147483648)]
    let labels : Fin 4 → Fin 33 := ![0,31,32,1]
    apply template (n:=2) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v9 eq []
    · simp
    · dsimp only [base,codes,val,v9]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v9]
      decide
  have theta3 : F v9=0 ∨ F v2=0 ∨ F v5=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(true,0),(false,0),(true,1),(false,10),(true,0),(false,9),(true,10),(false,8),(true,8),(false,7),(true,7),(false,5),(true,5),(false,3),(true,3),(false,1),(true,1),(false,0),(true,0),(false,10),(true,1),(false,1),(true,3),(false,3),(true,5),(false,5),(true,7),(false,7),(true,8),(false,8),(true,10),(false,9)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(0,1),(2,1),(2,4294967297),(2147483650,4294967297),(2147483650,4831838209),(2415919106,4831838209),(2415919106,4898947073),(2432696322,4898947073),(2432696322,4903141377),(2434793474,4903141377),(2434793474,4903272449),(2434826242,4903272449),(2434826242,4903274497),(2434826754,4903274497),(2434826754,4903274529),(2434826762,4903274529),(2434826760,4903274529),(2434826760,4903274528),(287343112,4903274528),(287343112,608307232),(287343104,608307232),(287343104,608307200),(287342592,608307200),(287342592,608305152),(287309824,608305152),(287309824,608174080),(285212672,608174080),(285212672,603979776),(268435456,603979776),(268435456,536870912),(0,536870912)]
    let labels : Fin 32 → Fin 33 := ![0,1,32,31,29,28,26,24,22,21,17,15,11,9,5,3,1,0,31,32,3,5,9,11,15,17,21,22,24,26,28,29]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v9,-v9,v2,-v2,v5,-v5]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v9,v2,v5]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v9,v2,v5]
      decide
  have h3 : F v2=0 ∨ F v5=0 := by
    rcases theta3 with h|h|h
    · exact (short_v9 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  let v10 := val (25165824,37748736)
  have short_v10 : F v10 ≠ 0 := by
    intro eq
    apply no4
    let base : Fin 4 → Bool × Fin 11 := ![(false,7),(true,8),(false,8),(true,9)]
    let codes : Fin 4 → ℕ × ℕ := ![(0,0),(4194304,0),(4194304,16777216),(37748736,16777216)]
    let labels : Fin 4 → Fin 33 := ![22,24,25,23]
    apply template (n:=2) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v10 eq []
    · simp
    · dsimp only [base,codes,val,v10]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v10]
      decide
  have theta4 : F v10=0 ∨ F v1=0 ∨ F v3=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(false,7),(true,8),(false,8),(true,9),(false,7),(true,7),(false,5),(true,5),(false,3),(true,3),(false,2),(true,2),(false,0),(true,0),(false,9),(true,10),(false,8),(true,8),(false,7),(true,9),(false,8),(true,10),(false,9),(true,0),(false,0),(true,2),(false,2),(true,3),(false,3),(true,5),(false,5),(true,7)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(4194304,0),(4194304,16777216),(37748736,16777216),(37748736,25165824),(39845888,25165824),(39845888,25296896),(39878656,25296896),(39878656,25298944),(39879168,25298944),(39879168,25299072),(39879232,25299072),(39879232,25299076),(39879233,25299076),(39879233,562169988),(308314689,562169988),(308314689,629278852),(308314689,612501636),(304120385,612501636),(304120385,604113028),(270565953,604113028),(270565953,537004164),(2130497,537004164),(2130497,133252),(2130496,133252),(2130496,133248),(2130432,133248),(2130432,133120),(2129920,133120),(2129920,131072),(2097152,131072),(2097152,0)]
    let labels : Fin 32 → Fin 33 := ![22,24,25,23,21,17,15,11,9,7,6,2,0,29,28,26,24,22,23,25,26,28,29,0,2,6,7,9,11,15,17,21]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v10,-v10,v1,-v1,v3,-v3]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v10,v1,v3]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v10,v1,v3]
      decide
  have h4 : F v1=0 ∨ F v3=0 := by
    rcases theta4 with h|h|h
    · exact (short_v10 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  let v11 := val (2147483788,4294967393)
  have short_v11 : F v11 ≠ 0 := by
    intro eq
    apply no8
    let base : Fin 8 → Bool × Fin 11 := ![(false,0),(true,0),(false,10),(true,1),(false,1),(true,3),(false,2),(true,2)]
    let codes : Fin 8 → ℕ × ℕ := ![(0,0),(1,0),(1,2147483648),(4294967297,2147483648),(4294967297,2147483656),(4294967329,2147483656),(4294967329,2147483784),(4294967393,2147483784)]
    let labels : Fin 8 → Fin 33 := ![0,31,32,3,5,7,6,2]
    apply template (n:=6) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v11 eq []
    · simp
    · dsimp only [base,codes,val,v11]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v11]
      decide
  have identity5 : v11=v3 + -v6 := by
    dsimp only [v11,v3,v6,val]
    decide
  have h5 : ¬F v3=0 ∨ ¬F v6=0 := by
    by_contra! bad
    apply short_v11
    rw [identity5]
    simp [bad.1,bad.2]
  have theta6 : F v10=0 ∨ F v5=0 ∨ F v6=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(false,7),(true,8),(false,8),(true,9),(false,7),(true,7),(false,5),(true,5),(false,3),(true,3),(false,1),(true,1),(false,10),(true,0),(false,9),(true,10),(false,8),(true,8),(false,7),(true,9),(false,8),(true,10),(false,9),(true,0),(false,10),(true,1),(false,1),(true,3),(false,3),(true,5),(false,5),(true,7)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(4194304,0),(4194304,16777216),(37748736,16777216),(37748736,25165824),(39845888,25165824),(39845888,25296896),(39878656,25296896),(39878656,25298944),(39879168,25298944),(39879168,25298976),(39879176,25298976),(39879176,4320266272),(2187362824,4320266272),(2187362824,4857137184),(2455798280,4857137184),(2455798280,4924246048),(2455798280,4907468832),(2451603976,4907468832),(2451603976,4899080224),(2418049544,4899080224),(2418049544,4831971360),(2149614088,4831971360),(2149614088,4295100448),(2130440,4295100448),(2130440,133152),(2130432,133152),(2130432,133120),(2129920,133120),(2129920,131072),(2097152,131072),(2097152,0)]
    let labels : Fin 32 → Fin 33 := ![22,24,25,23,21,17,15,11,9,5,3,32,31,29,28,26,24,22,23,25,26,28,29,31,32,3,5,9,11,15,17,21]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v10,-v10,v5,-v5,v6,-v6]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v10,v5,v6]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v10,v5,v6]
      decide
  have h6 : F v5=0 ∨ F v6=0 := by
    rcases theta6 with h|h|h
    · exact (short_v10 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  have identity7 : v0=-v4 + v3 := by
    dsimp only [v0,v4,v3,val]
    decide
  have h7 : ¬F v4=0 ∨ ¬F v3=0 ∨ F v0=0 := by
    by_contra! bad
    apply bad.2.2
    rw [identity7]
    simp [bad.1,bad.2.1]
  have theta8 : F v9=0 ∨ F v4=0 ∨ F v6=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(true,0),(false,0),(true,1),(false,10),(true,0),(false,9),(true,10),(false,8),(true,9),(false,7),(true,7),(false,5),(true,5),(false,3),(true,3),(false,1),(true,1),(false,0),(true,0),(false,10),(true,1),(false,1),(true,3),(false,3),(true,5),(false,5),(true,7),(false,7),(true,9),(false,8),(true,10),(false,9)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(0,1),(2,1),(2,4294967297),(2147483650,4294967297),(2147483650,4831838209),(2415919106,4831838209),(2415919106,4898947073),(2449473538,4898947073),(2449473538,4907335681),(2451570690,4907335681),(2451570690,4907466753),(2451603458,4907466753),(2451603458,4907468801),(2451603970,4907468801),(2451603970,4907468833),(2451603978,4907468833),(2451603976,4907468833),(2451603976,4907468832),(304120328,4907468832),(304120328,612501536),(304120320,612501536),(304120320,612501504),(304119808,612501504),(304119808,612499456),(304087040,612499456),(304087040,612368384),(301989888,612368384),(301989888,603979776),(268435456,603979776),(268435456,536870912),(0,536870912)]
    let labels : Fin 32 → Fin 33 := ![0,1,32,31,29,28,26,25,23,21,17,15,11,9,5,3,1,0,31,32,3,5,9,11,15,17,21,23,25,26,28,29]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v9,-v9,v4,-v4,v6,-v6]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v9,v4,v6]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v9,v4,v6]
      decide
  have h8 : F v4=0 ∨ F v6=0 := by
    rcases theta8 with h|h|h
    · exact (short_v9 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  have identity9 : v11=v1 + -v5 := by
    dsimp only [v11,v1,v5,val]
    decide
  have h9 : ¬F v1=0 ∨ ¬F v5=0 := by
    by_contra! bad
    apply short_v11
    rw [identity9]
    simp [bad.1,bad.2]
  exact incompatible2 (F v0=0) (F v1=0) (F v2=0) (F v3=0) (F v4=0) (F v5=0) (F v6=0) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

private theorem incompatible3 (p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop)
    (h0 : ¬p2 ∨ ¬p8)
    (h1 : ¬p5 ∨ ¬p9)
    (h2 : p8 ∨ p9)
    (h3 : ¬p1 ∨ ¬p9)
    (h4 : p1 ∨ p5 ∨ p6)
    (h5 : p5 ∨ p7)
    (h6 : ¬p3 ∨ ¬p4)
    (h7 : p2 ∨ p3)
    (h8 : ¬p6 ∨ ¬p7)
    (h9 : p4 ∨ p9)
    : False := by tauto

set_option maxHeartbeats 8000000 in
private theorem cover3 {V X : Type*} [AddCommGroup V]
    (w : Fin 11 → Fin 3 → V) (G : SimpleGraph X) (ι : (Bool × Fin 11 × V) ↪ X)
    (edge : ∀ (i : Fin 11) (k : Fin 3) (g : V),
      G.Adj (ι (false,i,g)) (ι (true,i+(![0,1,3] : Fin 3 → Fin 11) k,g+w i k))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  let fiber : ((Bool × Fin 11) × V) ↪ X := (Equiv.prodAssoc Bool (Fin 11) V).toEmbedding.trans ι
  let idx : Fin 33 → Fin 11 := ![0,0,0,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5,6,6,6,7,7,7,8,8,8,9,9,9,10,10,10]
  let color : Fin 33 → Fin 3 := ![0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2]
  let tail (k : Fin 33) := (false,idx k)
  let head (k : Fin 33) := (true,idx k+(![0,1,3] : Fin 3 → Fin 11) (color k))
  let wt (k l : Fin 33) : ℤ := if k=l then 1 else 0
  let F : (Fin 33 → ℤ) →+ V := {
    toFun z := ∑ i, z i • w (idx i) (color i)
    map_zero' := by simp
    map_add' := by intro x y; simp [Pi.add_apply,add_zsmul,Finset.sum_add_distrib] }
  have edge' (k : Fin 33) (g : V) :
      G.Adj (fiber (tail k,g)) (fiber (head k,g+F (wt k))) := by
    have basis : F (wt k)=w (idx k) (color k) := by
      change (∑ j, (if k=j then (1:ℤ) else 0) • w (idx j) (color j)) = _
      simp [ite_smul]
    rw [basis]
    exact edge _ _ _
  let val (c : ℕ × ℕ) (i : Fin 33) : ℤ :=
    (if c.1.testBit i.val then 1 else 0) - (if c.2.testBit i.val then 1 else 0)
  by_contra absent
  have no4 : ¬cycleGraph 4 ⊑ G := fun h => absent (.inl h)
  have no8 : ¬cycleGraph 8 ⊑ G := fun h => absent (.inr (.inl h))
  have no16 : ¬cycleGraph 16 ⊑ G := fun h => absent (.inr (.inr (.inl h)))
  have no32 : ¬cycleGraph 32 ⊑ G := fun h => absent (.inr (.inr (.inr h)))
  let v0 := val (33947648,17891328)
  let v1 := val (271587328,142885888)
  let v2 := val (205800450,556800001)
  let v3 := val (545392644,272695810)
  let v4 := val (1143996434,4337434633)
  let v5 := val (1143341074,4320722953)
  let v6 := val (4303882252,1076101650)
  let v7 := val (4362209312,2164327440)
  let v8 := val (2420179986,4840359969)
  let v9 := val (4505092128,2435911696)
  have short_v9 : F v9 ≠ 0 := by
    intro eq
    apply no16
    let base : Fin 16 → Bool × Fin 11 := ![(false,1),(true,2),(false,10),(true,0),(false,8),(true,8),(false,5),(true,6),(false,6),(true,9),(false,9),(true,10),(false,7),(true,7),(false,4),(true,4)]
    let codes : Fin 16 → ℕ × ℕ := ![(0,0),(16,0),(16,4294967296),(2147483664,4294967296),(2147483664,4362076160),(2164260880,4362076160),(2164260880,4362207232),(2164326416,4362207232),(2164326416,4362469376),(2165374992,4362469376),(2165374992,4496687104),(2433810448,4496687104),(2433810448,4505075712),(2435907600,4505075712),(2435907600,4505092096),(2435911696,4505092096)]
    let labels : Fin 16 → Fin 33 := ![4,32,31,26,24,17,16,18,20,27,28,23,21,14,12,5]
    apply template (n:=14) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v9 eq []
    · simp
    · dsimp only [base,codes,val,v9]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v9]
      decide
  have identity0 : v9=-v1 + v7 := by
    dsimp only [v9,v1,v7,val]
    decide
  have h0 : ¬F v1=0 ∨ ¬F v7=0 := by
    by_contra! bad
    apply short_v9
    rw [identity0]
    simp [bad.1,bad.2]
  let v10 := val (1681000480,2454258696)
  have short_v10 : F v10 ≠ 0 := by
    intro eq
    apply no16
    let base : Fin 16 → Bool × Fin 11 := ![(false,1),(true,1),(false,9),(true,10),(false,10),(true,0),(false,8),(true,9),(false,6),(true,7),(false,7),(true,8),(false,5),(true,6),(false,3),(true,4)]
    let codes : Fin 16 → ℕ × ℕ := ![(0,0),(8,0),(8,536870912),(268435464,536870912),(268435464,1610612736),(2415919112,1610612736),(2415919112,1677721600),(2449473544,1677721600),(2449473544,1678770176),(2449997832,1678770176),(2449997832,1680867328),(2454192136,1680867328),(2454192136,1680998400),(2454257672,1680998400),(2454257672,1681000448),(2454258696,1681000448)]
    let labels : Fin 16 → Fin 33 := ![3,29,28,30,31,26,25,20,19,21,22,17,16,11,10,5]
    apply template (n:=14) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v10 eq []
    · simp
    · dsimp only [base,codes,val,v10]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v10]
      decide
  have identity1 : v10=v4 + -v8 := by
    dsimp only [v10,v4,v8,val]
    decide
  have h1 : ¬F v4=0 ∨ ¬F v8=0 := by
    by_contra! bad
    apply short_v10
    rw [identity1]
    simp [bad.1,bad.2]
  let v11 := val (339738626,562036737)
  have short_v11 : F v11 ≠ 0 := by
    intro eq
    apply no8
    let base : Fin 8 → Bool × Fin 11 := ![(false,0),(true,0),(false,8),(true,8),(false,7),(true,10),(false,9),(true,1)]
    let codes : Fin 8 → ℕ × ℕ := ![(0,0),(1,0),(1,67108864),(16777217,67108864),(16777217,71303168),(25165825,71303168),(25165825,339738624),(562036737,339738624)]
    let labels : Fin 8 → Fin 33 := ![0,26,24,22,23,28,29,1]
    apply template (n:=6) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v11 eq []
    · simp
    · dsimp only [base,codes,val,v11]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v11]
      decide
  have theta2 : F v11=0 ∨ F v7=0 ∨ F v8=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(true,0),(false,8),(true,8),(false,7),(true,10),(false,9),(true,1),(false,0),(true,0),(false,10),(true,2),(false,1),(true,4),(false,3),(true,6),(false,5),(true,8),(false,8),(true,0),(false,0),(true,1),(false,9),(true,10),(false,7),(true,8),(false,5),(true,6),(false,3),(true,4),(false,1),(true,2),(false,10)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(0,67108864),(16777216,67108864),(16777216,71303168),(25165824,71303168),(25165824,339738624),(562036736,339738624),(562036736,339738626),(562036737,339738626),(562036737,2487222274),(4857004033,2487222274),(4857004033,2487222290),(4857004065,2487222290),(4857004065,2487223314),(4857006113,2487223314),(4857006113,2487288850),(4857137185,2487288850),(4840359969,2487288850),(4840359969,2420179986),(4840359968,2420179986),(4840359968,2420179984),(4303489056,2420179984),(4303489056,2151744528),(4295100448,2151744528),(4295100448,2147550224),(4294969376,2147550224),(4294969376,2147484688),(4294967328,2147484688),(4294967328,2147483664),(4294967296,2147483664),(4294967296,2147483648),(0,2147483648)]
    let labels : Fin 32 → Fin 33 := ![26,24,22,23,28,29,1,0,31,32,4,5,10,11,16,17,24,26,0,1,29,28,23,22,17,16,11,10,5,4,32,31]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v11,-v11,v7,-v7,v8,-v8]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v11,v7,v8]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v11,v7,v8]
      decide
  have h2 : F v7=0 ∨ F v8=0 := by
    rcases theta2 with h|h|h
    · exact (short_v11 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  let v12 := val (2453931026,4858054689)
  have short_v12 : F v12 ≠ 0 := by
    intro eq
    apply no16
    let base : Fin 16 → Bool × Fin 11 := ![(false,0),(true,0),(false,10),(true,2),(false,1),(true,4),(false,3),(true,6),(false,6),(true,9),(false,8),(true,8),(false,7),(true,10),(false,9),(true,1)]
    let codes : Fin 16 → ℕ × ℕ := ![(0,0),(1,0),(1,2147483648),(4294967297,2147483648),(4294967297,2147483664),(4294967329,2147483664),(4294967329,2147484688),(4294969377,2147484688),(4294969377,2147746832),(4296017953,2147746832),(4296017953,2181301264),(4312795169,2181301264),(4312795169,2185495568),(4321183777,2185495568),(4321183777,2453931024),(4858054689,2453931024)]
    let labels : Fin 16 → Fin 33 := ![0,31,32,4,5,10,11,18,20,25,24,22,23,28,29,1]
    apply template (n:=14) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v12 eq []
    · simp
    · dsimp only [base,codes,val,v12]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v12]
      decide
  have identity3 : v12=v0 + v8 := by
    dsimp only [v12,v0,v8,val]
    decide
  have h3 : ¬F v0=0 ∨ ¬F v8=0 := by
    by_contra! bad
    apply short_v12
    rw [identity3]
    simp [bad.1,bad.2]
  have theta4 : F v0=0 ∨ F v4=0 ∨ F v5=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(false,6),(true,9),(false,8),(true,8),(false,5),(true,6),(false,6),(true,7),(false,7),(true,10),(false,10),(true,2),(false,1),(true,1),(false,0),(true,0),(false,8),(true,9),(false,6),(true,6),(false,5),(true,8),(false,8),(true,0),(false,0),(true,1),(false,1),(true,2),(false,10),(true,10),(false,7),(true,7)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(1048576,0),(1048576,33554432),(17825792,33554432),(17825792,33685504),(17891328,33685504),(17891328,33947648),(18415616,33947648),(18415616,36044800),(26804224,36044800),(26804224,1109786624),(4321771520,1109786624),(4321771520,1109786640),(4321771528,1109786640),(4321771528,1109786642),(4321771529,1109786642),(4321771529,1176895506),(4321771529,1143341074),(4320722953,1143341074),(4320722953,1143078930),(4320657417,1143078930),(4320657417,1142947858),(4303880201,1142947858),(4303880201,1075838994),(4303880200,1075838994),(4303880200,1075838992),(4303880192,1075838992),(4303880192,1075838976),(8912896,1075838976),(8912896,2097152),(524288,2097152),(524288,0)]
    let labels : Fin 32 → Fin 33 := ![20,25,24,17,16,18,19,21,23,30,32,4,3,1,0,26,25,20,18,16,17,24,26,0,1,3,4,32,30,23,21,19]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v0,-v0,v4,-v4,v5,-v5]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v0,v4,v5]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v0,v4,v5]
      decide
  have h4 : F v0=0 ∨ F v4=0 ∨ F v5=0 := by
    rcases theta4 with h|h|h
    · exact (Or.inl h)
    · exact (Or.inr (Or.inl h))
    · exact (Or.inr (Or.inr h))
  let v13 := val (68159492,33817089)
  have short_v13 : F v13 ≠ 0 := by
    intro eq
    apply no8
    let base : Fin 8 → Bool × Fin 11 := ![(false,0),(true,0),(false,8),(true,9),(false,6),(true,6),(false,3),(true,3)]
    let codes : Fin 8 → ℕ × ℕ := ![(0,0),(1,0),(1,67108864),(33554433,67108864),(33554433,68157440),(33816577,68157440),(33816577,68159488),(33817089,68159488)]
    let labels : Fin 8 → Fin 33 := ![0,26,25,20,18,11,9,2]
    apply template (n:=6) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v13 eq []
    · simp
    · dsimp only [base,codes,val,v13]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v13]
      decide
  have theta5 : F v13=0 ∨ F v4=0 ∨ F v6=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(false,0),(true,0),(false,8),(true,9),(false,6),(true,6),(false,3),(true,3),(false,0),(true,1),(false,1),(true,2),(false,10),(true,10),(false,7),(true,7),(false,6),(true,9),(false,8),(true,0),(false,0),(true,3),(false,3),(true,6),(false,6),(true,7),(false,7),(true,10),(false,10),(true,2),(false,1),(true,1)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(1,0),(1,67108864),(33554433,67108864),(33554433,68157440),(33816577,68157440),(33816577,68159488),(33817089,68159488),(33817089,68159492),(33817091,68159492),(33817091,68159500),(33817107,68159500),(33817107,4363126796),(1107558931,4363126796),(1107558931,4371515404),(1109656083,4371515404),(1109656083,4372039692),(1109656083,4370991116),(1076101651,4370991116),(1076101651,4303882252),(1076101650,4303882252),(1076101650,4303882248),(1076101138,4303882248),(1076101138,4303880200),(1075838994,4303880200),(1075838994,4303355912),(1073741842,4303355912),(1073741842,4294967304),(18,4294967304),(18,8),(2,8),(2,0)]
    let labels : Fin 32 → Fin 33 := ![0,26,25,20,18,11,9,2,1,3,4,32,30,23,21,19,20,25,26,0,2,9,11,18,19,21,23,30,32,4,3,1]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v13,-v13,v4,-v4,v6,-v6]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v13,v4,v6]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v13,v4,v6]
      decide
  have h5 : F v4=0 ∨ F v6=0 := by
    rcases theta5 with h|h|h
    · exact (short_v13 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  let v14 := val (210125828,288428545)
  have short_v14 : F v14 ≠ 0 := by
    intro eq
    apply no16
    let base : Fin 16 → Bool × Fin 11 := ![(false,0),(true,0),(false,8),(true,8),(false,5),(true,6),(false,6),(true,9),(false,9),(true,10),(false,7),(true,7),(false,4),(true,4),(false,3),(true,3)]
    let codes : Fin 16 → ℕ × ℕ := ![(0,0),(1,0),(1,67108864),(16777217,67108864),(16777217,67239936),(16842753,67239936),(16842753,67502080),(17891329,67502080),(17891329,201719808),(286326785,201719808),(286326785,210108416),(288423937,210108416),(288423937,210124800),(288428033,210124800),(288428033,210125824),(288428545,210125824)]
    let labels : Fin 16 → Fin 33 := ![0,26,24,17,16,18,20,27,28,23,21,14,12,10,9,2]
    apply template (n:=14) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v14 eq []
    · simp
    · dsimp only [base,codes,val,v14]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v14]
      decide
  have identity6 : v14=v2 + v3 := by
    dsimp only [v14,v2,v3,val]
    decide
  have h6 : ¬F v2=0 ∨ ¬F v3=0 := by
    by_contra! bad
    apply short_v14
    rw [identity6]
    simp [bad.1,bad.2]
  have theta7 : F v11=0 ∨ F v1=0 ∨ F v2=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(false,7),(true,10),(false,9),(true,1),(false,0),(true,0),(false,8),(true,8),(false,7),(true,7),(false,4),(true,4),(false,3),(true,6),(false,6),(true,9),(false,9),(true,10),(false,7),(true,8),(false,8),(true,0),(false,0),(true,1),(false,9),(true,9),(false,6),(true,6),(false,3),(true,4),(false,4),(true,7)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(8388608,0),(8388608,268435456),(545259520,268435456),(545259520,268435458),(545259521,268435458),(545259521,335544322),(562036737,335544322),(562036737,339738626),(564133889,339738626),(564133889,339755010),(564137985,339755010),(564137985,339756034),(564140033,339756034),(564140033,340018178),(565188609,340018178),(565188609,474235906),(565188609,205800450),(556800001,205800450),(556800001,201606146),(540022785,201606146),(540022785,134497282),(540022784,134497282),(540022784,134497280),(3151872,134497280),(3151872,279552),(2103296,279552),(2103296,17408),(2101248,17408),(2101248,16384),(2097152,16384),(2097152,0)]
    let labels : Fin 32 → Fin 33 := ![23,28,29,1,0,26,24,22,21,14,12,10,11,18,20,27,28,23,22,24,26,0,1,29,27,20,18,11,10,12,14,21]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v11,-v11,v1,-v1,v2,-v2]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v11,v1,v2]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v11,v1,v2]
      decide
  have h7 : F v1=0 ∨ F v2=0 := by
    rcases theta7 with h|h|h
    · exact (short_v11 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  let v15 := val (67241988,16843265)
  have short_v15 : F v15 ≠ 0 := by
    intro eq
    apply no8
    let base : Fin 8 → Bool × Fin 11 := ![(false,0),(true,0),(false,8),(true,8),(false,5),(true,6),(false,3),(true,3)]
    let codes : Fin 8 → ℕ × ℕ := ![(0,0),(1,0),(1,67108864),(16777217,67108864),(16777217,67239936),(16842753,67239936),(16842753,67241984),(16843265,67241984)]
    let labels : Fin 8 → Fin 33 := ![0,26,24,17,16,11,9,2]
    apply template (n:=6) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v15 eq []
    · simp
    · dsimp only [base,codes,val,v15]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v15]
      decide
  have identity8 : v15=v5 + v6 := by
    dsimp only [v15,v5,v6,val]
    decide
  have h8 : ¬F v5=0 ∨ ¬F v6=0 := by
    by_contra! bad
    apply short_v15
    rw [identity8]
    simp [bad.1,bad.2]
  let v16 := val (2147484692,4294967841)
  have short_v16 : F v16 ≠ 0 := by
    intro eq
    apply no8
    let base : Fin 8 → Bool × Fin 11 := ![(false,0),(true,0),(false,10),(true,2),(false,1),(true,4),(false,3),(true,3)]
    let codes : Fin 8 → ℕ × ℕ := ![(0,0),(1,0),(1,2147483648),(4294967297,2147483648),(4294967297,2147483664),(4294967329,2147483664),(4294967329,2147484688),(4294967841,2147484688)]
    let labels : Fin 8 → Fin 33 := ![0,31,32,4,5,10,9,2]
    apply template (n:=6) G fiber F tail head wt edge' base (fun i => val (codes i)) labels v16 eq []
    · simp
    · dsimp only [base,codes,val,v16]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v16]
      decide
  have theta9 : F v16=0 ∨ F v3=0 ∨ F v8=0 := by
    by_contra! eq
    apply no32
    let base : Fin 32 → Bool × Fin 11 := ![(false,0),(true,3),(false,3),(true,4),(false,1),(true,2),(false,10),(true,0),(false,0),(true,1),(false,9),(true,10),(false,7),(true,8),(false,5),(true,6),(false,3),(true,3),(false,0),(true,0),(false,10),(true,2),(false,1),(true,4),(false,3),(true,6),(false,5),(true,8),(false,7),(true,10),(false,9),(true,1)]
    let codes : Fin 32 → ℕ × ℕ := ![(0,0),(4,0),(4,512),(1028,512),(1028,544),(1044,544),(1044,4294967840),(2147484692,4294967840),(2147484692,4294967841),(2147484694,4294967841),(2147484694,4831838753),(2415920150,4831838753),(2415920150,4840227361),(2420114454,4840227361),(2420114454,4840358433),(2420179990,4840358433),(2420179990,4840360481),(2420179990,4840359969),(2420179986,4840359969),(2420179986,4840359968),(272696338,4840359968),(272696338,545392672),(272696322,545392672),(272696322,545392640),(272695298,545392640),(272695298,545390592),(272629762,545390592),(272629762,545259520),(268435458,545259520),(268435458,536870912),(2,536870912),(2,0)]
    let labels : Fin 32 → Fin 33 := ![2,9,10,5,4,32,31,0,1,29,28,23,22,17,16,11,9,2,0,31,32,4,5,10,11,16,17,22,23,28,29,1]
    apply template (n:=30) G fiber F tail head wt edge' base (fun i => val (codes i)) labels 0 (by simp) [v16,-v16,v3,-v3,v8,-v8]
    · intro z mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact eq.1
      · simpa only [map_neg,neg_ne_zero] using eq.1
      · exact eq.2.1
      · simpa only [map_neg,neg_ne_zero] using eq.2.1
      · exact eq.2.2
      · simpa only [map_neg,neg_ne_zero] using eq.2.2
    · dsimp only [base,codes,val,v16,v3,v8]
      decide
    · dsimp only [base,codes,labels,tail,head,wt,idx,color,val,v16,v3,v8]
      decide
  have h9 : F v3=0 ∨ F v8=0 := by
    rcases theta9 with h|h|h
    · exact (short_v16 h).elim
    · exact (Or.inl h)
    · exact (Or.inr h)
  exact incompatible3 (F v0=0) (F v1=0) (F v2=0) (F v3=0) (F v4=0) (F v5=0) (F v6=0) (F v7=0) (F v8=0) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

/-- Every abelian voltage cover of the two normalized index-eleven quotient graphs contains a short power-of-two cycle. -/
theorem abelian_cover {V X : Type*} [AddCommGroup V] (d : Fin 11) (hd : d=2 ∨ d=3)
    (w : Fin 11 → Fin 3 → V) (G : SimpleGraph X) (ι : (Bool × Fin 11 × V) ↪ X)
    (edge : ∀ (i : Fin 11) (k : Fin 3) (g : V),
      G.Adj (ι (false,i,g)) (ι (true,i+(![0,1,d] : Fin 3 → Fin 11) k,g+w i k))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  rcases hd with rfl|rfl
  · exact cover2 w G ι edge
  · exact cover3 w G ι edge

end NonfreeEleven

namespace NonfreeEleven
open SimpleGraph

private theorem ladder_walk {V T X : Type*} [AddCommGroup V] (a b : V)
    (G : SimpleGraph X) (ι : (Bool × Bool × V) ↪ X)
    (id : ∀ r g,G.Adj (ι (false,r,g)) (ι (true,r,g)))
    (rung : ∀ g,G.Adj (ι (false,false,g)) (ι (true,true,g)))
    (top : ∀ g,G.Adj (ι (false,false,g)) (ι (true,false,g+a)))
    (bottom : ∀ g,G.Adj (ι (false,true,g)) (ι (true,true,g+b)))
    (v : T → V) (inj : Function.Injective v) (L U : T → T → Prop)
    (low : ∀ i j,L i j → v j=v i+a) (high : ∀ i j,U i j → v j=v i+b)
    {n : ℕ} (p : Fin n → Bool × Bool × T) (distinct : Function.Injective p) :
    let forward (z w : Bool × Bool × T) : Prop :=
      z.1=false ∧ w.1=true ∧ (z.2=w.2 ∨ (z.2.1=false ∧ w.2.1=true ∧ z.2.2=w.2.2) ∨
        (z.2.1=false ∧ w.2.1=false ∧ L z.2.2 w.2.2) ∨ (z.2.1=true ∧ w.2.1=true ∧ U z.2.2 w.2.2))
    (∀ i j,(cycleGraph n).Adj i j → forward (p i) (p j) ∨ forward (p j) (p i)) →
    cycleGraph n ⊑ G := by
  intro forward edges
  let f := ((Function.Embedding.refl Bool).prodMap ((Function.Embedding.refl Bool).prodMap ⟨v,inj⟩)).trans ι
  have oriented (z w : Bool × Bool × T) (e : forward z w) : G.Adj (f z) (f w) := by
    obtain ⟨s,r,i⟩ := z
    obtain ⟨t,q,j⟩ := w
    obtain ⟨rfl,rfl,eq|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,hl⟩|⟨rfl,rfl,hu⟩⟩ := e
    · change (r,i)=(q,j) at eq
      cases eq
      exact id _ _
    · exact rung _
    · change G.Adj (ι (false,false,v i)) (ι (true,false,v j))
      rw [low _ _ hl]; exact top _
    · change G.Adj (ι (false,true,v i)) (ι (true,true,v j))
      rw [high _ _ hu]; exact bottom _
  exact ⟨⟨⟨fun i => f (p i),fun {i j} h => (edges i j h).elim (oriented _ _) (fun e => (oriented _ _ e).symm)⟩,
    f.injective.comp distinct⟩⟩

private theorem ladder {V X : Type*} [AddCommGroup V] (a b : V) (a0 : a ≠ 0) (b0 : b ≠ 0)
    (G : SimpleGraph X) (ι : (Bool × Bool × V) ↪ X)
    (id : ∀ r g,G.Adj (ι (false,r,g)) (ι (true,r,g)))
    (rung : ∀ g,G.Adj (ι (false,false,g)) (ι (true,true,g)))
    (top : ∀ g,G.Adj (ι (false,false,g)) (ι (true,false,g+a)))
    (bottom : ∀ g,G.Adj (ι (false,true,g)) (ι (true,true,g+b)))
    (distinct : a≠b ∧ a≠ -b) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  by_cases b2 : b+b=0
  · left
    let v : Bool → V := fun i => if i then b else 0
    have vi : Function.Injective v := by
      intro i j eq; cases i <;> cases j <;> simp_all [v]
    let p : Fin 4 → Bool × Bool × Bool := ![(false,true,false),(true,true,false),(false,true,true),(true,true,true)]
    have high (i j : Bool) (e : i≠j) : v j=v i+b := by cases i <;> cases j <;> simp_all [v]
    apply ladder_walk a b G ι id rung top bottom v vi (fun _ _ => False) (fun i j => i≠j)
      (fun _ _ e => e.elim) high p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]; decide
    · dsimp only [p]; decide
  let t : Fin 3 → V := ![0,b,b+b]
  have ti : Function.Injective t := by
    have notEqual : b+b≠b := by simpa using b0
    intro i j eq
    fin_cases i <;> fin_cases j <;> first | rfl | exact (b0 eq).elim | exact (b0 eq.symm).elim | exact (b2 eq).elim | exact (b2 eq.symm).elim | exact (notEqual eq).elim | exact (notEqual eq.symm).elim
  let adj (i j : Fin 3) := (i=0 ∧ j=1) ∨ (i=1 ∧ j=2)
  have up (i j : Fin 3) (e : adj i j) : t j=t i+b := by
    rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (zero_add b).symm
    · rfl
  by_cases plus : a=b+b
  · right; left
    let L (i j : Fin 3) := i=0 ∧ j=2
    have low (i j : Fin 3) (e : L i j) : t j=t i+a := by
      obtain ⟨rfl,rfl⟩ := e; change b+b=0+a; simp [plus]
    let p : Fin 8 → Bool × Bool × Fin 3 := ![(false,false,0),(true,false,2),(false,false,2),(true,true,2),
      (false,true,1),(true,true,1),(false,true,0),(true,true,0)]
    apply ladder_walk a b G ι id rung top bottom t ti L adj low up p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]; decide
    · dsimp only [p,L,adj]; decide
  by_cases minus : a= -(b+b)
  · right; left
    let L (i j : Fin 3) := i=2 ∧ j=0
    have low (i j : Fin 3) (e : L i j) : t j=t i+a := by
      obtain ⟨rfl,rfl⟩ := e; change 0=b+b+a; simp [minus]
    let p : Fin 8 → Bool × Bool × Fin 3 := ![(false,false,2),(true,false,0),(false,false,0),(true,true,0),
      (false,true,0),(true,true,1),(false,true,1),(true,true,2)]
    apply ladder_walk a b G ι id rung top bottom t ti L adj low up p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]; decide
    · dsimp only [p,L,adj]; decide
  right;right
  have dj (i j : Fin 3) : t i ≠ a+t j := by
    intro eq
    fin_cases i <;> fin_cases j <;> dsimp [t] at eq
    all_goals first
      | solve | apply a0; linear_combination (norm := abel) -eq
      | solve | apply distinct.1; linear_combination (norm := abel) -eq
      | solve | apply distinct.2; linear_combination (norm := abel) -eq
      | solve | apply plus; linear_combination (norm := abel) -eq
      | solve | apply minus; linear_combination (norm := abel) -eq
  let v (z : Bool × Fin 3) := if z.1 then a+t z.2 else t z.2
  have vi : Function.Injective v := by
    rintro ⟨r,i⟩ ⟨s,j⟩ eq
    cases r <;> cases s
    · exact Prod.ext rfl (ti eq)
    · exact (dj _ _ eq).elim
    · exact (dj _ _ eq.symm).elim
    · exact Prod.ext rfl (ti (add_left_cancel eq))
  let L (z w : Bool × Fin 3) := z.1=false ∧ w.1=true ∧ z.2=w.2
  let U (z w : Bool × Fin 3) := z.1=w.1 ∧ adj z.2 w.2
  have low (i j : Bool × Fin 3) (e : L i j) : v j=v i+a := by
    obtain ⟨r,k⟩ := i; obtain ⟨s,l⟩ := j
    obtain ⟨rfl,rfl,rfl⟩ := e; exact add_comm _ _
  have high (i j : Bool × Fin 3) (e : U i j) : v j=v i+b := by
    obtain ⟨r,k⟩ := i; obtain ⟨s,l⟩ := j
    obtain ⟨rfl,h⟩ := e; cases r <;> simp [v,up k l h,add_assoc]
  let p : Fin 16 → Bool × Bool × Bool × Fin 3 := ![
    (false,false,false,0),(true,false,true,0),(false,false,true,0),(true,true,true,0),
    (false,true,true,0),(true,true,true,1),(false,true,true,1),(true,true,true,2),
    (false,false,true,2),(true,false,true,2),(false,false,false,2),(true,true,false,2),
    (false,true,false,1),(true,true,false,1),(false,true,false,0),(true,true,false,0)]
  apply ladder_walk a b G ι id rung top bottom v vi L U low high p
  · change ∀ i j,p i=p j → i=j
    dsimp only [p]; decide
  · dsimp only [p,L,U,adj]; decide

/-- Two separated parallel shifts and one advancing shift suffice for a 4-, 8- or 16-cycle. -/
theorem parallel_cover {V X : Type*} [AddCommGroup V] (w : Fin 11 → Fin 3 → V)
    (sep : ∀ i,w i 0≠w i 1) (G : SimpleGraph X) (ι : (Bool × Fin 11 × V) ↪ X)
    (edge : ∀ (i : Fin 11) (k : Fin 3) (g : V),
      G.Adj (ι (false,i,g)) (ι (true,i+(![0,0,1] : Fin 3 → Fin 11) k,g+w i k))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let x (i : Fin 11) := w i 1-w i 0
  have nz (i : Fin 11) : x i ≠ 0 := sub_ne_zero.mpr (sep i).symm
  have next : ∀ i : Fin 11,i+1≠i := by decide
  by_cases pair : ∃ i,x i ≠ x (i+1) ∧ x i ≠ -x (i+1)
  · obtain ⟨i,different⟩ := pair
    let row (r : Bool) : Fin 11 := if r then i+1 else i
    have ri : Function.Injective row := by
      intro s t eq
      cases s <;> cases t <;> first | rfl | exact (next i eq).elim | exact (next i eq.symm).elim
    let c := w i 2-w (i+1) 0
    let e : (Bool × Bool × V) ↪ X := {
      toFun z := ι (z.1,row z.2.1,z.2.2+(if z.2.1 then c else 0)+(if z.1 then w (row z.2.1) 0 else 0))
      inj' := by
        rintro ⟨s,r,u⟩ ⟨t,j,v⟩ eq
        have h := ι.injective eq
        have side : s=t := congrArg Prod.fst h
        have layer : row r=row j := congrArg (fun z : Bool × Fin 11 × V => z.2.1) h
        have rj := ri layer
        subst t; subst j
        have hv := congrArg (fun z : Bool × Fin 11 × V => z.2.2) h
        exact Prod.ext rfl (Prod.ext rfl (add_right_cancel (add_right_cancel hv))) }
    apply ladder (x i) (x (i+1)) (nz _) (nz _) G e _ _ _ _ different
    · intro r g
      cases r
      · simpa [e,row] using edge i 0 g
      · simpa [e,row] using edge (i+1) 0 (g+c)
    · intro g
      simpa [e,row,c,sub_eq_add_neg,add_assoc] using edge i 2 g
    · intro g
      simpa [e,row,x,sub_eq_add_neg,add_assoc] using edge i 1 g
    · intro g
      simpa [e,row,x,sub_eq_add_neg,add_assoc,add_left_comm,add_comm] using edge (i+1) 1 (g+c)
  let a := x 0
  have adj (i : Fin 11) : x i=x (i+1) ∨ x i= -x (i+1) := by
    by_contra! h
    exact pair ⟨i,h⟩
  have sign (i : Fin 11) : x i=a ∨ x i= -a := by
    induction i using Fin.induction with
    | zero => exact Or.inl rfl
    | succ i ih =>
      have h := adj i.castSucc
      have ix : (i.castSucc + 1 : Fin 11)=i.succ := by fin_cases i <;> decide
      rw [ix] at h
      rcases ih with t|t <;> rcases h with h|h
      · exact Or.inl (h.symm.trans t)
      · exact Or.inr (by rw [←t,h,neg_neg])
      · exact Or.inr (h.symm.trans t)
      · exact Or.inl (by simpa using (congrArg Neg.neg (h.symm.trans t)))
  let r (i : Fin 11) := if x i=a then w i 0 else w i 1
  let j : (Bool × Fin 11 × V) ↪ X := {
    toFun z := ι (z.1,z.2.1,z.2.2+(if z.1 then r z.2.1 else 0))
    inj' := by
      rintro ⟨s,i,u⟩ ⟨t,k,v⟩ eq
      have z := ι.injective eq
      have side : s=t := congrArg Prod.fst z
      have row : i=k := congrArg (fun q : Bool × Fin 11 × V => q.2.1) z
      subst t; subst k
      exact Prod.ext rfl (Prod.ext rfl (add_right_cancel (congrArg (fun q : Bool × Fin 11 × V => q.2.2) z))) }
  let p : Equiv.Perm (Fin 11 × V) := {
    toFun z := (z.1,z.2+a)
    invFun z := (z.1,z.2-a)
    left_inv z := by simp
    right_inv z := by simp }
  let t (i : Fin 11) := w i 2-r (i+1)
  let q : Equiv.Perm (Fin 11 × V) := {
    toFun z := (z.1+1,z.2+t z.1)
    invFun z := (z.1-1,z.2-t (z.1-1))
    left_inv z := by simp
    right_inv z := by simp }
  have separated (z : Fin 11 × V) : p z≠z ∧ q z≠z ∧ p z≠q z := by
    refine ⟨?_,fun h => next _ (congrArg Prod.fst h),fun h => next _ (congrArg Prod.fst h).symm⟩
    intro h
    have e : z.2+a=z.2 := congrArg Prod.snd h
    exact nz 0 (by simpa using e)
  have idE (z : Fin 11 × V) : (G.comap j).Adj (false,z) (true,z) := by
    obtain ⟨i,g⟩ := z
    by_cases h : x i=a
    · simpa [j,r,h] using edge i 0 g
    · simpa [j,r,h] using edge i 1 g
  have pE (z : Fin 11 × V) : (G.comap j).Adj (false,z) (true,p z) := by
    obtain ⟨i,g⟩ := z
    change G.Adj (ι (false,i,g+0)) (ι (true,i,g+a+r i))
    by_cases h : x i=a
    · have eq : g+a+r i=g+w i 1 := by
        rw [show r i=w i 0 by simp [r,h],←h]
        simp [x,sub_eq_add_neg,add_assoc]
      simpa [eq] using edge i 1 g
    · have e := (sign i).resolve_left h
      have eq : g+a+r i=g+w i 0 := by
        rw [show r i=w i 1 by simp [r,h]]
        change w i 1 - w i 0= -a at e
        linear_combination (norm := abel) e
      simpa [eq] using edge i 0 g
  have qE (z : Fin 11 × V) : (G.comap j).Adj (false,z) (true,q z) := by
    obtain ⟨i,g⟩ := z
    change G.Adj (ι (false,i,g+0)) (ι (true,i+1,g+t i+r (i+1)))
    simpa [t,sub_eq_add_neg,add_assoc] using edge i 2 g
  have comm (z : Fin 11 × V) : p (q z)=q (p z) := by
    exact Prod.ext rfl (show z.2+t z.1+a=z.2+a+t z.1 by abel)
  have hit := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0
    (G.comap j) p q separated idE pE qE (0,0) (comm _) (comm _) (comm _) (comm _)
  have down : G.comap j ⊑ G := ⟨(SimpleGraph.Embedding.comap j G).toCopy⟩
  rcases hit with h|h|h
  · exact .inl (h.trans down)
  · exact .inr (.inl (h.trans down))
  · exact .inr (.inr (h.trans down))

end NonfreeEleven

universe u
namespace NonfreeEleven
open SimpleGraph
/-- Left coset fibers along a normal abelian kernel. The stabilizer may be
nonnormal in the acting group; normality inside the abelian kernel suffices. -/
theorem coordinate_bridge {A : Type u} {X Q : Type*} [Group A] [Group Q] [MulAction A X]
    (f : A →* Q) (comm : ∀ a b : f.ker, a*b=b*a) (x : X)
    (stab : ∀ a : A, a • x=x → f a=1)
    (r : Bool → Fin 11 → A) (sep : ∀ b, Function.Injective (fun i => f (r b i)))
    (shift : Fin 3 → A) (δ : Fin 3 → Fin 11)
    (matchQ : ∀ i k, f (shift k * r false i)=f (r true (i+δ k)))
    (G : SimpleGraph (Bool × X))
    (adj : ∀ k y, G.Adj (false,y) (true,shift k • y)) :
    ∃ (V : Type u) (_ : AddCommGroup V) (w : Fin 11 → Fin 3 → V)
      (ι : (Bool × Fin 11 × V) ↪ (Bool × X)),
      (∀ i k g, G.Adj (ι (false,i,g)) (ι (true,i+δ k,g+w i k))) ∧
      (∀ i k l, δ k=δ l → (∀ y : X,shift k • y ≠ shift l • y) → w i k ≠ w i l) := by
  classical
  let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := comm }
  let H := MulAction.stabilizer f.ker x
  let D := f.ker ⧸ H
  let point (g : D) : X := MulAction.ofQuotientStabilizer f.ker x g
  have pinj : Function.Injective point := MulAction.injective_ofQuotientStabilizer f.ker x
  let h (i : Fin 11) (k : Fin 3) : f.ker := ⟨(r true (i+δ k))⁻¹*(shift k*r false i),by
    change f _ = 1
    rw [map_mul,map_inv,matchQ,inv_mul_cancel]⟩
  let w (i : Fin 11) (k : Fin 3) : Additive D := Additive.ofMul (QuotientGroup.mk (h i k))
  let v (b : Bool) (i : Fin 11) (g : D) := r b i • point g
  have distinct (b : Bool) {i j : Fin 11} {g g' : D} (same : v b i g=v b j g') : i=j := by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective H g
    obtain ⟨a',ha'⟩ := QuotientGroup.mk'_surjective H g'
    subst g; subst g'
    change r b i • ((a : A) • x)=r b j • ((a' : A) • x) at same
    rw [smul_smul,smul_smul] at same
    have fixed : ((r b j*(a':A))⁻¹*(r b i*(a:A))) • x=x := by
      rw [mul_smul,same,inv_smul_smul]
    have he := stab _ fixed
    have fa : f (a:A)=1 := a.property
    have fb : f (a':A)=1 := a'.property
    simp only [map_mul,map_inv,fa,fb,mul_one,inv_mul_eq_one] at he
    exact sep b he.symm
  let embed : (Bool × Fin 11 × Additive D) ↪ (Bool × X) := {
    toFun z := (z.1,v z.1 z.2.1 z.2.2.toMul)
    inj' := by
      rintro ⟨b,i,g⟩ ⟨c,j,g'⟩ eq
      obtain rfl : b=c := congrArg Prod.fst eq
      have h' : v b i g.toMul=v b j g'.toMul := congrArg Prod.snd eq
      obtain rfl : i=j := distinct b h'
      have hv : point g.toMul=point g'.toMul := (MulAction.injective (r b i)) h'
      have hg : g=g' := congrArg Additive.ofMul (pinj hv)
      cases hg
      rfl }
  have transport (i : Fin 11) (k : Fin 3) (g : Additive D) :
      shift k • v false i g.toMul = v true (i+δ k) (g+w i k).toMul := by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective H g.toMul
    change shift k • (r false i • point g.toMul) =
      r true (i+δ k) • point (g.toMul*QuotientGroup.mk (h i k))
    rw [← ha]
    change shift k • (r false i • ((a:A) • x)) =
      r true (i+δ k) • point ((QuotientGroup.mk' H a)*(QuotientGroup.mk' H (h i k)))
    rw [← map_mul]
    change shift k • (r false i • ((a:A) • x)) =
      r true (i+δ k) • (((a*(h i k):f.ker):A) • x)
    rw [comm a (h i k),Subgroup.coe_mul,smul_smul,smul_smul]
    simp [h,mul_smul]
  refine ⟨Additive D,inferInstance,w,embed,?_,?_⟩
  · intro i k g
    change G.Adj (false,v false i g.toMul) (true,v true (i+δ k) (g+w i k).toMul)
    rw [←transport]; exact adj _ _
  · intro i k l same separate eq
    apply separate (v false i (0 : Additive D).toMul)
    rw [transport i k 0,transport i l 0,same,eq]
end NonfreeEleven
namespace NonfreeEleven
open SimpleGraph
/-- Put any three distinct quotient labels into one of the two normalized
eleven-point patterns and apply the orbit-coordinate argument. -/
theorem normalize_orbit {A : Type u} {X : Type*} [Group A] [MulAction A X]
    (f : A →* Multiplicative (ZMod 11)) (onto : Function.Surjective f)
    (comm : ∀ a b : f.ker, a*b=b*a) (x : X)
    (stab : ∀ a : A, a • x=x → f a=1)
    (a b : A) (fa : f a ≠ 1) (fb : f b ≠ 1) (fab : f a ≠ f b)
    (G : SimpleGraph (Bool × X)) (h0 : ∀ y, G.Adj (false,y) (true,y))
    (ha : ∀ y,G.Adj (false,y) (true,a • y))
    (hb : ∀ y,G.Adj (false,y) (true,b • y)) :
    ∃ (d : Fin 11), (d=2 ∨ d=3) ∧
      ∃ (V : Type u) (_ : AddCommGroup V) (w : Fin 11 → Fin 3 → V)
        (ι : (Bool × Fin 11 × V) ↪ (Bool × X)),
        ∀ i k g, G.Adj (ι (false,i,g)) (ι (true,i+(![0,1,d] : Fin 3 → Fin 11) k,g+w i k)) := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let ax := (f a).toAdd
  let bx := (f b).toAdd
  have n1 : ax ≠ 0 := fa
  have n2 : bx ≠ 0 := fb
  have n3 : ax ≠ bx := fab
  have classif : ∀ x y : ZMod 11, x ≠ 0 → y ≠ 0 → x ≠ y →
      ∃ i j k : Fin 3,
        let t : Fin 3 → ZMod 11 := ![0,x,y]
        t i ≠ t j ∧ (t k - t i = 2*(t j-t i) ∨ t k - t i = 3*(t j-t i)) := by decide
  obtain ⟨i,j,k,neq,hd⟩ := classif ax bx n1 n2 n3
  let T : Fin 3 → ZMod 11 := ![0,ax,bx]
  let S : Fin 3 → A := ![1,a,b]
  have valT (l : Fin 3) : (f (S l)).toAdd=T l := by
    fin_cases l <;> simp [S,T,ax,bx]
  let v := T j-T i
  have nv : v≠0 := sub_ne_zero.mpr (Ne.symm neq)
  obtain ⟨d,ds,dt⟩ : ∃ d : Fin 11, (d=2 ∨ d=3) ∧ T k-T i=(show ZMod 11 from d)*v := by
    rcases hd with h|h
    · exact ⟨2,Or.inl rfl,h⟩
    · exact ⟨3,Or.inr rfl,h⟩
  let order : Fin 3 → Fin 3 := ![i,j,k]
  let label : Fin 3 → Fin 11 := ![0,1,d]
  have norm (l : Fin 3) : T (order l) = T i+(show ZMod 11 from label l)*v := by
    fin_cases l
    · change T i=T i+(0 : ZMod 11)*v
      ring
    · change T j=T i+(1 : ZMod 11)*(T j-T i)
      ring
    · change T k=T i+(show ZMod 11 from d)*v
      linear_combination dt
  choose lift spec using onto
  let qcoord (b' : Bool) (l : Fin 11) : ZMod 11 := (show ZMod 11 from l)*v+(if b' then T i else 0)
  let r (b' : Bool) (l : Fin 11) : A := lift (Multiplicative.ofAdd (qcoord b' l))
  have hr (b' : Bool) (l : Fin 11) : (f (r b' l)).toAdd=qcoord b' l :=
    congrArg Multiplicative.toAdd (spec _)
  have sep (b' : Bool) : Function.Injective (fun l => f (r b' l)) := by
    intro m n hh
    have eq := congrArg Multiplicative.toAdd hh
    change (f (r b' m)).toAdd=(f (r b' n)).toAdd at eq
    rw [hr,hr] at eq
    change (show ZMod 11 from m)*v+(if b' then T i else 0)=(show ZMod 11 from n)*v+(if b' then T i else 0) at eq
    have hmn : (show ZMod 11 from m)=(show ZMod 11 from n) := mul_right_cancel₀ nv (add_right_cancel eq)
    exact hmn
  have mat (l : Fin 11) (z : Fin 3) : f (S (order z) * r false l)=f (r true (l+label z)) := by
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    change (f (S (order z))).toAdd+(f (r false l)).toAdd=(f (r true (l+label z))).toAdd
    rw [valT,norm,hr,hr]
    change T i+(show ZMod 11 from label z)*v+((show ZMod 11 from l)*v+0)=((show ZMod 11 from l)+(show ZMod 11 from label z))*v+T i
    ring
  have edges (z : Fin 3) (y : X) : G.Adj (false,y) (true,S (order z) • y) := by
    generalize order z=l
    fin_cases l <;> simp [S,h0,ha,hb]
  obtain ⟨V,inst,w,j,e,_⟩ := coordinate_bridge f comm x stab r sep (fun l=>S (order l)) label mat G edges
  exact ⟨d,ds,V,inst,w,j,e⟩

/-- Translation of the right quotient labels and scaling by the difference of the two
distinct classes put the coincident pair in positions zero and one. -/
private theorem coincident_ordered {A : Type u} {X : Type*} [Group A] [MulAction A X]
    (f : A →* Multiplicative (ZMod 11)) (onto : Function.Surjective f)
    (comm : ∀ a b : f.ker, a*b=b*a) (x : X) (stab : ∀ a : A,a • x=x → f a=1)
    (s t u : A) (same : f s=f t) (diff : f u≠f s)
    (separated : ∀ y : X,s • y≠t • y) (G : SimpleGraph (Bool × X))
    (hs : ∀ y,G.Adj (false,y) (true,s • y)) (ht : ∀ y,G.Adj (false,y) (true,t • y))
    (hu : ∀ y,G.Adj (false,y) (true,u • y)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let b := (f s).toAdd
  let a := (f u).toAdd-b
  have nz : a≠0 := sub_ne_zero.mpr (fun e => diff (Multiplicative.toAdd.injective e))
  let S : Fin 3 → A := ![s,t,u]
  let δ : Fin 3 → Fin 11 := ![0,0,1]
  have norm (k : Fin 3) : (f (S k)).toAdd=b+(show ZMod 11 from δ k)*a := by
    fin_cases k
    · change (f s).toAdd=(f s).toAdd+0*a; ring
    · change (f t).toAdd=(f s).toAdd+0*a; rw [same]; ring
    · change (f u).toAdd=(f s).toAdd+1*((f u).toAdd-(f s).toAdd); ring
  choose lift spec using onto
  let pos (side : Bool) (j : Fin 11) : ZMod 11 := (show ZMod 11 from j)*a+(if side then b else 0)
  let r (side : Bool) (j : Fin 11) : A := lift (Multiplicative.ofAdd (pos side j))
  have hr (side : Bool) (j : Fin 11) : (f (r side j)).toAdd=pos side j :=
    congrArg Multiplicative.toAdd (spec _)
  have ri (side : Bool) : Function.Injective (fun j => f (r side j)) := by
    intro i j eq
    have eq' := congrArg Multiplicative.toAdd eq
    change (f (r side i)).toAdd=(f (r side j)).toAdd at eq'
    rw [hr,hr] at eq'
    change (show ZMod 11 from i)*a+(if side then b else 0)=(show ZMod 11 from j)*a+(if side then b else 0) at eq'
    have hij : (show ZMod 11 from i)=(show ZMod 11 from j) := mul_right_cancel₀ nz (add_right_cancel eq')
    exact hij
  have align (j : Fin 11) (k : Fin 3) : f (S k*r false j)=f (r true (j+δ k)) := by
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    change (f (S k)).toAdd+(f (r false j)).toAdd=(f (r true (j+δ k))).toAdd
    rw [norm,hr,hr]
    change b+(show ZMod 11 from δ k)*a+((show ZMod 11 from j)*a+0)=((show ZMod 11 from j)+(show ZMod 11 from δ k))*a+b
    ring
  have edges (k : Fin 3) (y : X) : G.Adj (false,y) (true,S k • y) := by
    fin_cases k <;> first | exact hs y | exact ht y | exact hu y
  obtain ⟨V,inst,w,j,e,apart⟩ := coordinate_bridge f comm x stab r ri S δ align G edges
  exact parallel_cover w (fun i => apart i 0 1 rfl separated) G j e

/-- If a point stabilizer lies in the abelian kernel of an index-eleven quotient, every
separated triple of matching permutations with nonconstant quotient image has a simple
4-, 8-, 16-, or 32-cycle. -/
theorem index_eleven_orbit {A : Type u} {X : Type*} [Group A] [MulAction A X]
    (f : A →* Multiplicative (ZMod 11)) (onto : Function.Surjective f)
    (comm : ∀ g h : f.ker,g*h=h*g) (x : X)
    (stab : ∀ g : A,g • x=x → f g=1) (a b : A) (moving : f a≠1 ∨ f b≠1)
    (separated : ∀ y : X,a • y≠y ∧ b • y≠y ∧ a • y≠b • y)
    (G : SimpleGraph (Bool × X)) (h0 : ∀ y,G.Adj (false,y) (true,y))
    (ha : ∀ y,G.Adj (false,y) (true,a • y)) (hb : ∀ y,G.Adj (false,y) (true,b • y)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  have oneE (y : X) : G.Adj (false,y) (true,(1:A) • y) := by simpa using h0 y
  have includeShort (h : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) :
      cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G :=
    h.imp id (fun r => r.imp id Or.inl)
  by_cases ea : f a=1
  · have eb : f b≠1 := moving.resolve_left (not_not_intro ea)
    apply includeShort
    apply coincident_ordered f onto comm x stab 1 a b ((map_one f).trans ea.symm)
      (fun e => eb (e.trans (map_one f))) _ G oneE ha hb
    intro y
    simpa using (separated y).1.symm
  by_cases eb : f b=1
  · apply includeShort
    apply coincident_ordered f onto comm x stab 1 b a ((map_one f).trans eb.symm)
      (fun e => ea (e.trans (map_one f))) _ G oneE hb ha
    intro y
    simpa using (separated y).2.1.symm
  by_cases eq : f a=f b
  · apply includeShort
    exact coincident_ordered f onto comm x stab a b 1 eq
      (fun e => ea (e.symm.trans (map_one f))) (fun y => (separated y).2.2) G ha hb oneE
  obtain ⟨d,hd,V,inst,w,j,e⟩ := normalize_orbit f onto comm x stab a b ea eb eq G h0 ha hb
  exact abelian_cover d hd w G j e

end NonfreeEleven

open scoped commutatorElement
open SimpleGraph
namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1

/-- The generated matching group has no abelian normal subgroup of index eleven. -/
def H1 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ¬ (Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆) →
    (∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ ∃ x : X, g x=x) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N.index ≠ 11) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))

/-- Every point stabilizer maps onto the cyclic quotient of order eleven. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ¬ (Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆) →
    (∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ ∃ x : X, g x=x) →
    ∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N.index = 11 →
    (∀ x : X, ∃ g : Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g • x=x ∧ g ∉ N) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1.H2 := by
  intro absent residual X _ _ p q sep density central fixed
  classical
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  by_cases none : ∀ N : Subgroup K, N.Normal → IsMulCommutative N → N.index ≠ 11
  · exact absent X p q sep density central fixed none
  push Not at none
  obtain ⟨N,normal,comm,idx⟩ := none
  by_cases escaped : ∀ x : X, ∃ g : K, g • x=x ∧ g ∉ N
  · exact residual X p q sep density central fixed N normal comm idx escaped
  push Not at escaped
  obtain ⟨x,contained⟩ := escaped
  have card : Nat.card (K ⧸ N)=11 := N.index_eq_card.symm.trans idx
  have zcard : Nat.card (Multiplicative (ZMod 11))=11 := by change Nat.card (ZMod 11)=11; simp
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let e := mulEquivOfPrimeCardEq card zcard
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have onto : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have ker : f.ker=N := (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have abelian (g h : f.ker) : g*h=h*g := by
    have hg : (g : K) ∈ N := ker ▸ g.property
    have hh : (h : K) ∈ N := ker ▸ h.property
    apply Subtype.ext
    exact congrArg (fun z : N => (z:K)) (comm.is_comm.comm (⟨g,hg⟩ : N) (⟨h,hh⟩ : N))
  have stab (g : K) (hg : g • x=x) : f g=1 := by
    change g ∈ f.ker
    rw [ker]
    exact contained g hg
  let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
  have gen : Subgroup.closure ({a,b} : Set K)=⊤ := by
    apply Subgroup.map_injective (f := K.subtype) Subtype.coe_injective
    rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,Subgroup.subtype_range,Set.image_pair]
    rfl
  have moving : f a≠1 ∨ f b≠1 := by
    by_contra! trivial
    have hle : Subgroup.closure ({a,b} : Set K) ≤ f.ker :=
      (Subgroup.closure_le f.ker).mpr (by
        intro c hc
        rcases hc with h|h
        · exact h ▸ trivial.1
        · exact (Set.mem_singleton_iff.mp h) ▸ trivial.2)
    rw [gen,ker] at hle
    have nt : N=⊤ := top_unique hle
    rw [nt,Subgroup.index_top] at idx
    contradiction
  let G := SimpleGraph.fromRel (fun u v : Bool × X =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))
  obtain h|h|h|h := NonfreeEleven.index_eleven_orbit f onto abelian x stab a b moving sep G
    (fun y => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩)
    (fun y => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩)
    (fun y => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩)
  · exact ⟨2,by decide,h⟩
  · exact ⟨3,by decide,h⟩
  · exact ⟨4,by decide,h⟩
  · exact ⟨5,by decide,h⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1
