import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R3
import Mathlib

/-!
# From 103 compatible ten-cell partial transversals to 157 lines

Adjoin the three omitted coordinate labels to each transversal. Add three triangle
sides and the other eleven lines through each triangle vertex. These 139 lines
have size thirteen and meet pairwise exactly once. The 139-line completion theorem
keeps those lines and gives 157 in all.

The first order-twelve reduction is by @ian139 (open-math-agents PR 3312).
The 140–142 extension proof is by @seanm27lol and collaborators, from
seanm27lol/left-to-solve-research commit 4100242ec70236d9ba325564392f6c75f363acb8.
Its MIT notice is included with their source. The remaining completion and
triangle proofs are from the accompanying order-twelve research project.
The prior extension statements are displayed in full for this standalone proof.
-/

/- Component Erdos723.Completion. -/
section

/-
# Extending partial projective planes of order 12

This proves the one-line extension hypothesis in Left to Solve's first order-12
reduction. The input is a family of 143 to 156 lines on 157 points. Each line
has 13 points and distinct lines meet exactly once. The proof uses the two
incidence moments and counts common uncovered neighbors in the boundary case.
-/

namespace Order12

abbrev Pt := Fin 157
abbrev Blocks := Finset (Finset Pt)

def Good (S : Blocks) : Prop :=
  (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

def through (S : Blocks) (p : Pt) : Blocks := S.filter (p ∈ ·)

def holes (S : Blocks) (p : Pt) : Finset Pt := by
  classical exact Finset.univ.filter (fun q => q ≠ p ∧ ¬ ∃ b ∈ S, p ∈ b ∧ q ∈ b)

@[simp] lemma mem_through {S : Blocks} {b : Finset Pt} {p : Pt} :
    b ∈ through S p ↔ b ∈ S ∧ p ∈ b := by simp [through]

@[simp] lemma mem_holes {S : Blocks} {p q : Pt} :
    q ∈ holes S p ↔ q ≠ p ∧ ¬ ∃ b ∈ S, p ∈ b ∧ q ∈ b := by classical simp [holes]

lemma holes_symm (S : Blocks) (p q : Pt) : q ∈ holes S p ↔ p ∈ holes S q := by
  simp only [mem_holes]
  constructor <;> rintro ⟨hne, h⟩ <;> refine ⟨hne.symm, ?_⟩ <;>
    rintro ⟨b, hb, hp, hq⟩ <;> exact h ⟨b, hb, hq, hp⟩

/-- Distinct lines through a point have disjoint sets of remaining points. -/
lemma pencil_disjoint (S : Blocks) (h : Good S) (p : Pt) :
    (↑(through S p) : Set (Finset Pt)).PairwiseDisjoint (fun b => b.erase p) := by
  intro b hb c hc hbc
  obtain ⟨hbs, hpb⟩ := mem_through.mp hb
  obtain ⟨hcs, hpc⟩ := mem_through.mp hc
  refine Finset.disjoint_left.mpr ?_
  intro x hxb hxc
  exact (Finset.mem_erase.mp hxb).1 ((h.2 b hbs c hcs hbc).unique
    ⟨(Finset.mem_erase.mp hxb).2, (Finset.mem_erase.mp hxc).2⟩ ⟨hpb, hpc⟩)

lemma holes_card (S : Blocks) (h : Good S) (p : Pt) :
    (holes S p).card + 12 * (through S p).card = 156 := by
  classical
  let A := (through S p).biUnion (fun b => b.erase p)
  have outside : holes S p = Finset.univ.erase p \ A := by
    ext q
    simp only [mem_holes, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
      A, Finset.mem_biUnion, mem_through]
    constructor
    · rintro ⟨hn, hm⟩
      exact ⟨hn, fun ⟨b, hb, _, hq⟩ => hm ⟨b, hb.1, hb.2, hq⟩⟩
    · rintro ⟨hn, hm⟩
      exact ⟨hn, fun ⟨b, hb, hp, hq⟩ => hm ⟨b, ⟨hb, hp⟩, hn, hq⟩⟩
  have sub : A ⊆ Finset.univ.erase p := by
    intro q hq
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1, Finset.mem_univ q⟩
  have size : A.card = (through S p).card * 12 := by
    change ((through S p).biUnion _).card = _
    rw [Finset.card_biUnion (pencil_disjoint S h p)]
    calc
      ∑ b ∈ through S p, (b.erase p).card = ∑ _ ∈ through S p, 12 := by
        apply Finset.sum_congr rfl
        intro b hb
        obtain ⟨hbs, hpb⟩ := mem_through.mp hb
        rw [Finset.card_erase_of_mem hpb, h.1 b hbs]
      _ = _ := by simp
  rw [outside, Nat.mul_comm, ← size, Finset.card_sdiff_add_card_eq_card sub]
  simp

lemma degree_le (S : Blocks) (h : Good S) (p : Pt) : (through S p).card ≤ 13 := by
  have := holes_card S h p
  omega

/-- Count weighted incidences on a set of points, first by point and then by line. -/
lemma sum_through_weights (S : Blocks) (T : Finset Pt) (w : Pt → ℤ) :
    ∑ p ∈ T, ((through S p).card : ℤ) * w p = ∑ b ∈ S, ∑ p ∈ T ∩ b, w p := by
  classical
  calc
    _ = ∑ p ∈ T, ∑ b ∈ S, if p ∈ b then w p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter]
      simp [through]
    _ = ∑ b ∈ S, ∑ p ∈ T, if p ∈ b then w p else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]

/-- A line sees itself thirteen times and every other line once. -/
lemma sum_degree_on_block (S : Blocks) (h : Good S) {b : Finset Pt} (hb : b ∈ S) :
    ∑ p ∈ b, ((through S p).card : ℤ) = (S.card : ℤ) + 12 := by
  classical
  calc
    _ = ∑ c ∈ S, ((b ∩ c).card : ℤ) := by simpa using sum_through_weights S b (fun _ => 1)
    _ = ∑ c ∈ S, ((1 : ℤ) + if c = b then 12 else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases e : c = b
      · subst c
        simp [h.1 b hb]
      · have hbc : (b ∩ c).card = 1 := by
          apply Finset.card_eq_one_iff_existsUnique.mpr
          simpa using h.2 b hb c hc (Ne.symm e)
        simp [e, hbc]
    _ = _ := by simp [Finset.sum_add_distrib, hb]

/-- The two incidence moments force a degree-twelve point except in the boundary case. -/
theorem deficiencyCases (S : Blocks) (h : Good S) (lower : 143 ≤ S.card) (upper : S.card < 157) :
    (∃ p, (through S p).card = 12) ∨
      (S.card = 143 ∧ (∃ p, (through S p).card = 11) ∧
        ∀ p, (through S p).card = 11 ∨ (through S p).card = 13) := by
  classical
  by_cases twelve : ∃ p, (through S p).card = 12
  · exact Or.inl twelve
  right
  let r (p : Pt) : ℤ := (through S p).card
  have moment_one : ∑ p, r p = 13 * (S.card : ℤ) := by
    calc
      _ = ∑ b ∈ S, (b.card : ℤ) := by
        simpa [r] using sum_through_weights S Finset.univ (fun _ => 1)
      _ = ∑ _b ∈ S, (13 : ℤ) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact_mod_cast h.1 b hb
      _ = _ := by simp [mul_comm]
  have moment_two : ∑ p, r p * r p = (S.card : ℤ) * ((S.card : ℤ) + 12) := by
    calc
      _ = ∑ b ∈ S, ∑ p ∈ b, r p := by simpa [r] using sum_through_weights S Finset.univ r
      _ = ∑ _b ∈ S, ((S.card : ℤ) + 12) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact sum_degree_on_block S h hb
      _ = _ := by simp
  let g (p : Pt) := (13 - r p) * (11 - r p)
  have nonneg (p : Pt) : 0 ≤ g p := by
    have deg := degree_le S h p
    have ne : (through S p).card ≠ 12 := fun hp => twelve ⟨p, hp⟩
    by_cases high : (through S p).card = 13
    · simp [g, r, high]
    · have low : r p ≤ 11 := by dsimp [r]; omega
      exact mul_nonneg (by omega) (by omega)
  have total : ∑ p, g p = ((S.card : ℤ) - 143) * ((S.card : ℤ) - 157) := by
    calc
      _ = ∑ p, (r p * r p - 24 * r p + 143) := by
        apply Finset.sum_congr rfl
        intro p _
        dsimp [g]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, moment_one, moment_two]
        simp [Pt]
        ring
  have zero : ∑ p, g p = 0 := by
    have pos := Finset.sum_nonneg (s := Finset.univ) (fun p _ => nonneg p)
    have neg : ((S.card : ℤ) - 143) * ((S.card : ℤ) - 157) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    omega
  rw [zero] at total
  have count : S.card = 143 := by
    rcases mul_eq_zero.mp total.symm with h | h <;> omega
  have roots (p : Pt) : (through S p).card = 11 ∨ (through S p).card = 13 := by
    have gp := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => nonneg q).mp zero p (Finset.mem_univ p)
    rcases mul_eq_zero.mp gp with h | h <;> dsimp [r] at h <;> omega
  refine ⟨count, ?_, roots⟩
  by_contra! none
  have all_high (p : Pt) : r p = 13 := by
    dsimp [r]
    exact_mod_cast (roots p).resolve_left (none p)
  simp [all_high, count, Pt] at moment_one

/-- The lines through a point partition the covered portion of any set missing that point. -/
lemma holePartition (S : Blocks) (h : Good S) {p : Pt} (X : Finset Pt) (miss : p ∉ X) :
    (X ∩ holes S p).card + ∑ b ∈ through S p, (b ∩ X).card = X.card := by
  classical
  have disj : ((through S p : Blocks) : Set (Finset Pt)).PairwiseDisjoint (fun b => b ∩ X) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro x hxb hxc
    obtain ⟨hbS, hpb⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcS, hpc⟩ := Finset.mem_filter.mp hc
    obtain ⟨hxb, hxX⟩ := Finset.mem_inter.mp hxb
    obtain ⟨hxc, _⟩ := Finset.mem_inter.mp hxc
    have he : x = p := (h.2 b hbS c hcS hbc).unique ⟨hxb, hxc⟩ ⟨hpb, hpc⟩
    exact miss (he ▸ hxX)
  have part : X \ holes S p = (through S p).biUnion (fun b => b ∩ X) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, mem_through, Finset.mem_inter, mem_holes]
    constructor
    · rintro ⟨hx, hn⟩
      have ne : x ≠ p := by rintro rfl; exact miss hx
      by_contra hm
      exact hn ⟨ne, fun ⟨b, hb, hpb, hxb⟩ => hm ⟨b, ⟨hb, hpb⟩, hxb, hx⟩⟩
    · rintro ⟨b, ⟨hb, hpb⟩, hxb, hx⟩
      exact ⟨hx, fun hh => hh.2 ⟨b, hb, hpb, hxb⟩⟩
  rw [← Finset.card_biUnion disj, ← part, Finset.card_sdiff, Finset.inter_comm (holes S p) X]
  have bound : (X ∩ holes S p).card ≤ X.card := Finset.card_le_card Finset.inter_subset_left
  omega

/-- Every line through an off-block point covers a different point of the block. -/
lemma blockHoles (S : Blocks) (h : Good S) {p : Pt} {b : Finset Pt}
    (hb : b ∈ S) (miss : p ∉ b) : (b ∩ holes S p).card + (through S p).card = 13 := by
  classical
  have one : ∀ c ∈ through S p, (c ∩ b).card = 1 := by
    intro c hc
    obtain ⟨hcS, hpc⟩ := Finset.mem_filter.mp hc
    have ne : c ≠ b := by rintro rfl; exact miss hpc
    obtain ⟨x, hx, hu⟩ := h.2 c hcS b hb ne
    have sing : c ∩ b = {x} := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_singleton]
      exact ⟨fun hy => hu _ hy, fun e => e ▸ hx⟩
    simp [sing]
  have n := holePartition S h b miss
  rw [Finset.sum_const_nat one, Nat.mul_one, h.1 _ hb] at n
  exact n

theorem holes_meet_adj (S : Blocks) (h : Good S) {p q : Pt}
    (hp : (through S p).card = 11) (hq : (through S q).card = 11) (adj : q ∈ holes S p) :
    ((holes S p) ∩ (holes S q)).card = 12 := by
  classical
  have cnt := holePartition S h ((holes S p).erase q) (Finset.notMem_erase q _)
  have one : ∀ b ∈ through S q, (b ∩ (holes S p).erase q).card = 1 := by
    intro b hb
    obtain ⟨hbS, hqb⟩ := Finset.mem_filter.mp hb
    have miss : p ∉ b := fun hpb => (mem_holes.mp adj).2 ⟨b, hbS, hpb, hqb⟩
    have n := blockHoles S h hbS miss
    rw [Finset.inter_erase, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hqb, adj⟩)]
    omega
  have same : (holes S p).erase q ∩ holes S q = holes S p ∩ holes S q := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    exact ⟨fun ⟨⟨_, a⟩, b⟩ => ⟨a, b⟩,
      fun ⟨a, b⟩ => ⟨⟨(mem_holes.mp b).1, a⟩, b⟩⟩
  rw [same, Finset.sum_const_nat one, Nat.mul_one, Finset.card_erase_of_mem adj] at cnt
  have size := holes_card S h p
  omega

theorem holes_meet_nonadj (S : Blocks) (h : Good S) {p q : Pt}
    (hp : (through S p).card = 11) (hq : (through S q).card = 11)
    (ne : p ≠ q) (na : q ∉ holes S p) : ((holes S p) ∩ (holes S q)).card = 4 := by
  classical
  have col : ∃ b ∈ S, p ∈ b ∧ q ∈ b := by
    by_contra no
    exact na (mem_holes.mpr ⟨ne.symm, no⟩)
  obtain ⟨line, hl, hpl, hql⟩ := col
  have pencil : line ∈ through S q := Finset.mem_filter.mpr ⟨hl, hql⟩
  have zero : (line ∩ holes S p).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx, hx'⟩ := Finset.mem_inter.mp hx
    exact (mem_holes.mp hx').2 ⟨line, hl, hpl, hx⟩
  have two : ∀ b ∈ (through S q).erase line, (b ∩ holes S p).card = 2 := by
    intro b hb
    obtain ⟨diff, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨hbS, hqb⟩ := Finset.mem_filter.mp hb
    have miss : p ∉ b := fun hpb => ne ((h.2 b hbS line hl diff).unique ⟨hpb, hpl⟩ ⟨hqb, hql⟩)
    have n := blockHoles S h hbS miss
    omega
  have cnt := holePartition S h (holes S p) na
  have sumErase := Finset.sum_erase_add (through S q) (fun b => (b ∩ holes S p).card) pencil
  rw [Finset.sum_const_nat two, Finset.card_erase_of_mem pencil, hq, zero] at sumErase
  have size := holes_card S h p
  omega

theorem localClique (V : Finset (Fin 157)) (N : Fin 157 → Finset (Fin 157))
    (nV : V.card = 24) (inV : ∀ x ∈ V, N x ⊆ V)
    (reg : ∀ x ∈ V, (N x).card = 12) (noLoops : ∀ x ∈ V, x ∉ N x)
    (symm : ∀ x ∈ V, ∀ y ∈ V, y ∈ N x ↔ x ∈ N y)
    (low : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → y ∉ N x → ((N x) ∩ (N y)).card ≤ 3) :
    ∃ C : Finset (Fin 157), C ⊆ V ∧ C.card = 12 ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → y ∈ N x := by
  classical
  -- Three pairwise nonadjacent vertices would have at least 27 neighbors between them.
  have noTriple (x y z : Fin 157) (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hny : y ∉ N x) (hnz : z ∉ N x) (hnzy : z ∉ N y) : False := by
    have hab := Finset.card_union_add_card_inter (N x) (N y)
    have habc := Finset.card_union_add_card_inter (N x ∪ N y) (N z)
    have hsub : (N x ∪ N y) ∩ N z ⊆ (N x ∩ N z) ∪ (N y ∩ N z) := by
      intro p hp
      simp only [Finset.mem_union, Finset.mem_inter] at hp ⊢
      tauto
    have hcross := (Finset.card_le_card hsub).trans
      (Finset.card_union_le (N x ∩ N z) (N y ∩ N z))
    have htotal := Finset.card_le_card
      (Finset.union_subset (Finset.union_subset (inV x hx) (inV y hy)) (inV z hz))
    have h₁ := low x hx y hy hxy hny
    have h₂ := low x hx z hz hxz hnz
    have h₃ := low y hy z hz hyz hnzy
    rw [reg x hx, reg y hy] at hab
    rw [reg z hz] at habc
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < V.card by omega)
  -- The eleven nonneighbors of a form a clique.
  let S := V \ insert a (N a)
  have subS : S ⊆ V := Finset.sdiff_subset
  have sizeS : S.card = 11 := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.insert_subset ha (inV a ha)),
      Finset.card_insert_of_notMem (noLoops a ha), reg a ha, nV]
  have apart {x : Fin 157} (hx : x ∈ S) : x ≠ a ∧ x ∉ N a := by
    simpa only [Finset.mem_insert, not_or] using (Finset.mem_sdiff.mp hx).2
  have cliqueS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → y ∈ N x := by
    intro x hx y hy hxy
    by_contra hny
    exact noTriple a x y ha (subS hx) (subS hy) (apart hx).1.symm
      (apart hy).1.symm hxy (apart hx).2 (apart hy).2 hny
  let O := V \ S
  have subO : O ⊆ V := Finset.sdiff_subset
  have distinct {x c : Fin 157} (hx : x ∈ O) (hc : c ∈ S) : x ≠ c :=
    fun he => (Finset.mem_sdiff.mp hx).2 (he ▸ hc)
  by_cases extend : ∃ w ∈ O, S ⊆ N w
  · obtain ⟨w, hw, hall⟩ := extend
    have hwS := (Finset.mem_sdiff.mp hw).2
    refine ⟨insert w S, Finset.insert_subset (subO hw) subS, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hwS, sizeS]
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with he | hxs
      · subst x
        rcases Finset.mem_insert.mp hy with he | hys
        · exact (hxy he.symm).elim
        · exact hall hys
      · rcases Finset.mem_insert.mp hy with he | hys
        · subst y
          exact (symm x (subS hxs) w (subO hw)).2 (hall hxs)
        · exact cliqueS x hxs y hys hxy
  · -- If S cannot be extended, each outsider has at most three neighbors in S.
    have few (w : Fin 157) (hw : w ∈ O) : (N w ∩ S).card ≤ 3 := by
      obtain ⟨c, hc, hcw⟩ := Finset.not_subset.mp (fun h => extend ⟨w, hw, h⟩)
      apply (Finset.card_le_card ?_).trans (low w (subO hw) c (subS hc) (distinct hw hc) hcw)
      intro p hp
      obtain ⟨hpw, hps⟩ := Finset.mem_inter.mp hp
      exact Finset.mem_inter.mpr ⟨hpw, cliqueS c hc p hps (by rintro rfl; exact hcw hpw)⟩
    -- Each pair of outsiders has a common nonneighbor in S, so the outsiders form a clique.
    have cliqueO : ∀ x ∈ O, ∀ y ∈ O, x ≠ y → y ∈ N x := by
      intro x hx y hy hxy
      by_contra hny
      have hb := Finset.card_union_le (N x ∩ S) (N y ∩ S)
      have fx := few x hx
      have fy := few y hy
      obtain ⟨c, hc, hmiss⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show ((N x ∩ S) ∪ (N y ∩ S)).card < S.card by omega)
      apply noTriple x y c (subO hx) (subO hy) (subS hc) hxy
        (distinct hx hc) (distinct hy hc) hny
      · exact fun h => hmiss (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hc⟩))
      · exact fun h => hmiss (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, hc⟩))
    have sizeO : O.card = 13 := by
      dsimp [O]
      rw [Finset.card_sdiff_of_subset subS, nV, sizeS]
    obtain ⟨C, hC, hc⟩ := Finset.exists_subset_card_eq (show 12 ≤ O.card by omega)
    exact ⟨C, hC.trans subO, hc, fun x hx y hy => cliqueO x (hC hx) y (hC hy)⟩

/-- In the exceptional case the uncovered partners of one point contain twelve
mutually uncovered points. Together they are a candidate line. -/
lemma exceptionalBlock (S : Blocks) (h : Good S) (p : Pt) (hp : (through S p).card = 11)
    (degrees : ∀ x, (through S x).card = 11 ∨ (through S x).card = 13) :
    ∃ B : Finset Pt, B.card = 13 ∧ (∀ x ∈ B, (through S x).card = 11) ∧
      ∀ x ∈ B, ∀ y ∈ B, x ≠ y → y ∈ holes S x := by
  classical
  let V := holes S p
  let N (x : Pt) := V ∩ holes S x
  have loop (x : Pt) : x ∉ holes S x := fun hx => (mem_holes.mp hx).1 rfl
  have nbdeg (x : Pt) (hx : x ∈ V) : (through S x).card = 11 := by
    rcases degrees x with hx' | hx'
    · exact hx'
    · have count := holes_card S h x
      have pos := Finset.card_pos.mpr ⟨p, (holes_symm S p x).mp hx⟩
      omega
  have vsize : V.card = 24 := by
    have := holes_card S h p
    dsimp [V]; omega
  have reg (x : Pt) (hx : x ∈ V) : (N x).card = 12 :=
    holes_meet_adj S h hp (nbdeg x hx) hx
  have sym (x : Pt) (hx : x ∈ V) (y : Pt) (hy : y ∈ V) : y ∈ N x ↔ x ∈ N y := by
    simp only [N, Finset.mem_inter, hx, hy, true_and]
    exact holes_symm S x y
  have low (x : Pt) (hx : x ∈ V) (y : Pt) (hy : y ∈ V) (ne : x ≠ y) (na : y ∉ N x) :
      ((N x) ∩ (N y)).card ≤ 3 := by
    have counts := holes_meet_nonadj S h (nbdeg x hx) (nbdeg y hy) ne
      (fun hyx => na (Finset.mem_inter.mpr ⟨hy, hyx⟩))
    have base : p ∈ holes S x ∩ holes S y := Finset.mem_inter.mpr
      ⟨(holes_symm S p x).mp hx, (holes_symm S p y).mp hy⟩
    have sub : N x ∩ N y ⊆ (holes S x ∩ holes S y).erase p := by
      intro z hz
      obtain ⟨hzx, hzy⟩ := Finset.mem_inter.mp hz
      obtain ⟨hv, hxz⟩ := Finset.mem_inter.mp hzx
      exact Finset.mem_erase.mpr ⟨(mem_holes.mp hv).1,
        Finset.mem_inter.mpr ⟨hxz, (Finset.mem_inter.mp hzy).2⟩⟩
    have bound := Finset.card_le_card sub
    rw [Finset.card_erase_of_mem base, counts] at bound
    exact bound
  obtain ⟨C, hCV, size, clique⟩ := localClique V N vsize
    (fun _ _ => Finset.inter_subset_left) reg
    (fun x _ hx => loop x (Finset.mem_inter.mp hx).2) sym low
  have missing : p ∉ C := fun hx => loop p (hCV hx)
  refine ⟨insert p C, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem missing, size]
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp
    · exact nbdeg x (hCV hx)
  · intro x hx y hy diff
    rcases Finset.mem_insert.mp hx with ex | hxc
    · subst x
      rcases Finset.mem_insert.mp hy with ey | hyc
      · exact (diff ey.symm).elim
      · exact hCV hyc
    · rcases Finset.mem_insert.mp hy with ey | hyc
      · subst y
        exact (holes_symm S p x).mp (hCV hxc)
      · exact (Finset.mem_inter.mp (clique x hxc y hyc diff)).2

def Ext (S : Blocks) : Prop :=
  ∃ T : Blocks, S ⊆ T ∧ T.card = S.card + 1 ∧ Good T

/-- A new block meeting each old block once extends the partial plane. -/
lemma extendWithBlock (S : Blocks) (h : Good S) (B : Finset Pt) (size : B.card = 13)
    (meets : ∀ b ∈ S, (B ∩ b).card = 1) : Ext S := by
  classical
  have fresh : B ∉ S := by
    intro old
    have one := meets B old
    simp [size] at one
  have uniquePt {b c : Finset Pt} (one : (b ∩ c).card = 1) : ∃! x, x ∈ b ∧ x ∈ c := by
    obtain ⟨x, singleton⟩ := Finset.card_eq_one.mp one
    refine ⟨x, Finset.mem_inter.mp ?_, ?_⟩
    · simp [singleton]
    · intro y hy
      have iy : y ∈ b ∩ c := Finset.mem_inter.mpr hy
      simpa only [singleton, Finset.mem_singleton] using iy
  refine ⟨insert B S, Finset.subset_insert _ _, by simp [fresh], ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact size
    · exact h.1 _ hb
  · intro b hb c hc ne
    rcases Finset.mem_insert.mp hb with rfl | oldB
    · have old : c ∈ S := (Finset.mem_insert.mp hc).resolve_left ne.symm
      exact uniquePt (meets _ old)
    · rcases Finset.mem_insert.mp hc with rfl | oldC
      · apply uniquePt
        simpa only [Finset.inter_comm b] using meets b oldB
      · exact h.2 b oldB c oldC ne

theorem degree12_extend (S : Blocks) (h : Good S) {p : Pt} (hp : (through S p).card = 12) :
    Ext S := by
  classical
  have off : p ∉ holes S p := fun e => (mem_holes.mp e).1 rfl
  apply extendWithBlock S h (insert p (holes S p))
  · rw [Finset.card_insert_of_notMem off]
    have size := holes_card S h p
    omega
  · intro b hb
    by_cases incident : p ∈ b
    · apply Finset.card_eq_one.mpr
      refine ⟨p, ?_⟩
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hxb⟩
        exact hx.resolve_right (fun hh => (mem_holes.mp hh).2 ⟨b, hb, incident, hxb⟩)
      · rintro rfl
        exact ⟨Or.inl rfl, incident⟩
    · have same : insert p (holes S p) ∩ b = b ∩ holes S p := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hxb⟩
          exact ⟨hxb, hx.resolve_left (fun e => incident (e ▸ hxb))⟩
        · rintro ⟨hxb, hh⟩
          exact ⟨Or.inr hh, hxb⟩
      rw [same]
      have count := blockHoles S h hb incident
      omega

/-- Thirteen pairwise uncovered points of degree eleven meet all 143 blocks exactly once. -/
theorem clique_extend (S : Blocks) (h : Good S) (size : S.card = 143) (B : Finset Pt)
    (hB : B.card = 13) (deg : ∀ p ∈ B, (through S p).card = 11)
    (pairs : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → q ∈ holes S p) : Ext S := by
  classical
  have disj : (↑B : Set Pt).PairwiseDisjoint (through S) := by
    intro p hp q hq ne
    apply Finset.disjoint_left.mpr
    intro b bp bq
    obtain ⟨hb, hpb⟩ := mem_through.mp bp
    exact (mem_holes.mp (pairs p hp q hq ne)).2 ⟨b, hb, hpb, (mem_through.mp bq).2⟩
  have count : (B.biUnion (through S)).card = 143 := by
    rw [Finset.card_biUnion disj, Finset.sum_const_nat deg, hB]
  have sub : B.biUnion (through S) ⊆ S := by
    intro b hb
    obtain ⟨_, _, pencil⟩ := Finset.mem_biUnion.mp hb
    exact (mem_through.mp pencil).1
  have cover : B.biUnion (through S) = S :=
    Finset.eq_of_subset_of_card_le sub (by omega)
  apply extendWithBlock S h B hB
  intro b hb
  have mem : b ∈ B.biUnion (through S) := by rw [cover]; exact hb
  obtain ⟨p, hp, pencil⟩ := Finset.mem_biUnion.mp mem
  have hpb := (mem_through.mp pencil).2
  apply Finset.card_eq_one.mpr
  refine ⟨p, ?_⟩
  ext q
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hqb⟩
    by_contra ne
    exact (mem_holes.mp (pairs p hp q hq (Ne.symm ne))).2 ⟨b, hb, hpb, hqb⟩
  · rintro rfl
    exact ⟨hp, hpb⟩

/-- Every admissible partial plane with at least 143 lines can grow by one line. -/
theorem one_line_extension : 
  ∀ S : Finset (Finset (Fin 157)), 143 ≤ S.card → S.card < 157 →
    (∀ b ∈ S, b.card = 13) → (∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧
      (∀ b ∈ T, b.card = 13) ∧ ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c := by
  intro S lower upper sizes meets
  have h : Good S := ⟨sizes, meets⟩
  rcases deficiencyCases S h lower upper with ⟨p, hp⟩ | ⟨size, ⟨p, hp⟩, degrees⟩
  · exact degree12_extend S h hp
  · obtain ⟨B, hB, deg, pairs⟩ := exceptionalBlock S h p hp degrees
    exact clique_extend S h size B hB deg pairs

end Order12

end

/- Component Erdos723.Deficit139. -/
section

/-
Count the lines missing through each point of a partial plane. These identities
give bounds on the possible degrees when 139 lines are present.
-/

namespace Order12

def deficit (S : Blocks) (p : Pt) : ℤ := 13 - (through S p).card

/-- Sum the excess over two at the uncovered neighbors of a point. -/
theorem deficit_holes_sum (S : Blocks) (h : Good S) (p : Pt) :
    ∑ q ∈ holes S p, (deficit S q - 2) =
      deficit S p * (145 - (S.card : ℤ) - deficit S p) := by
  classical
  have sumDeg : ∑ q ∈ holes S p, ((through S q).card : ℤ) =
      ((S.card : ℤ) - (through S p).card) * deficit S p := by
    calc
      _ = ∑ b ∈ S, ((holes S p ∩ b).card : ℤ) := by
        simpa using sum_through_weights S (holes S p) (fun _ => 1)
      _ = ∑ b ∈ S, (deficit S p - if p ∈ b then deficit S p else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases onBlock : p ∈ b
        · have empty : holes S p ∩ b = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro q hq
            obtain ⟨hqH, hqb⟩ := Finset.mem_inter.mp hq
            exact (mem_holes.mp hqH).2 ⟨b, hb, onBlock, hqb⟩
          simp [empty, onBlock]
        · have off := blockHoles S h hb onBlock
          rw [Finset.inter_comm]
          simp only [onBlock, if_false, sub_zero, deficit]
          omega
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        change _ - ((through S p).card : ℤ) * deficit S p = _
        ring
  have size : ((holes S p).card : ℤ) = 12 * deficit S p := by
    have count := holes_card S h p
    dsimp [deficit]
    omega
  calc
    _ = ∑ q ∈ holes S p, (11 - ((through S q).card : ℤ)) := by
      apply Finset.sum_congr rfl
      intro q _
      dsimp [deficit]
      ring
    _ = ((holes S p).card : ℤ) * 11 - ((S.card : ℤ) - (through S p).card) * deficit S p := by
      rw [Finset.sum_sub_distrib, sumDeg]
      simp
    _ = _ := by rw [size]; unfold deficit; ring

/-- For 139 old lines, the absence of deficit one bounds all deficits by six. -/
theorem deficit139_bound (S : Blocks) (h : Good S) (n : S.card = 139)
    (noOne : ∀ q, (through S q).card ≠ 12) (p : Pt) :
    0 ≤ deficit S p ∧ deficit S p ≤ 6 := by
  classical
  have nonneg : 0 ≤ ∑ q ∈ holes S p, (deficit S q - 2) := by
    apply Finset.sum_nonneg
    intro q hq
    have ne := noOne q
    have pos : 0 < (holes S q).card := Finset.card_pos.mpr ⟨p, (holes_symm S p q).mp hq⟩
    have covered := holes_card S h q
    unfold deficit
    omega
  rw [deficit_holes_sum S h p, n] at nonneg
  norm_num at nonneg
  constructor
  · have deg := degree_le S h p
    unfold deficit
    omega
  · by_contra! high
    exact (not_lt_of_ge nonneg) (mul_neg_of_pos_of_neg (by omega) (by omega))

/-- The two total deficit moments at size 139. -/
theorem deficit139_moments (S : Blocks) (h : Good S) (n : S.card = 139) :
    (∑ p, deficit S p) = 234 ∧ (∑ p, deficit S p * (deficit S p - 2)) = 72 := by
  classical
  let r (p : Pt) : ℤ := (through S p).card
  have one : ∑ p, r p = 1807 := by
    calc
      _ = ∑ b ∈ S, (b.card : ℤ) := by
        simpa [r] using sum_through_weights S Finset.univ (fun _ => 1)
      _ = ∑ _ ∈ S, (13 : ℤ) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact_mod_cast h.1 b hb
      _ = _ := by simp [n]
  have two : ∑ p, r p * r p = 20989 := by
    calc
      _ = ∑ b ∈ S, ∑ p ∈ b, r p := by
        simpa [r] using sum_through_weights S Finset.univ r
      _ = ∑ _ ∈ S, (151 : ℤ) := by
        apply Finset.sum_congr rfl
        intro b hb
        simpa [n, r] using sum_degree_on_block S h hb
      _ = _ := by simp [n]
  constructor
  · change (∑ p, (13 - r p)) = 234
    rw [Finset.sum_sub_distrib, one]
    norm_num [Pt]
  · calc
      _ = ∑ p, (r p * r p - 24 * r p + 143) := by
        apply Finset.sum_congr rfl
        intro p _
        change (13 - r p) * (13 - r p - 2) = _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, one, two]
        norm_num [Pt]

end Order12

end

/- Component Erdos723.Local139.Graph. -/
section

namespace Order12.Local139

variable {α : Type*}

/-- The collinearity graph restricted to the light gap neighbors of a light point
has these bounds. Adjacency here means collinearity on an old line. -/
structure GraphBounds (V : Finset α) (N : α → Finset α) : Prop where
  size : 16 ≤ V.card
  closed : ∀ x ∈ V, N x ⊆ V
  loopless : ∀ x ∈ V, x ∉ N x
  symm : ∀ x ∈ V, ∀ y ∈ V, y ∈ N x → x ∈ N y
  triangles : ∀ x ∈ V, ∀ y ∈ N x, Disjoint (N x) (N y)
  minDegree : ∀ x ∈ V, 3 ≤ (N x).card
  edgeSum : ∀ x ∈ V, ∀ y ∈ N x, V.card ≤ (N x).card + (N y).card + 3

/-- The five-cycle degree sum argument excludes even a closed five-step walk. -/
lemma no_five {V : Finset α} {N : α → Finset α} (G : GraphBounds V N)
    {a b c d e : α} (ha : a ∈ V) (ab : b ∈ N a) (bc : c ∈ N b)
    (cd : d ∈ N c) (de : e ∈ N d) (ea : a ∈ N e) : False := by
  classical
  have hb := G.closed a ha ab
  have hc := G.closed b hb bc
  have hd := G.closed c hc cd
  have he := G.closed d hd de
  let ind (x z : α) : ℕ := if z ∈ N x then 1 else 0
  have each {x y : α} (hx : x ∈ V) (hxy : y ∈ N x) (z : α) :
      ind x z + ind y z ≤ 1 := by
    by_cases hzx : z ∈ N x
    · have hzy := Finset.disjoint_left.mp (G.triangles x hx y hxy) hzx
      simp [ind, hzx, hzy]
    · by_cases hzy : z ∈ N y <;> simp [ind, hzx, hzy]
  have total {x : α} (hx : x ∈ V) : ∑ z ∈ V, ind x z = (N x).card := by
    exact (Finset.card_eq_sum_ite (G.closed x hx)).symm
  have pointwise (z : α) (_ : z ∈ V) :
      ind a z + ind b z + ind c z + ind d z + ind e z ≤ 2 := by
    have h1 := each ha ab z
    have h2 := each hb bc z
    have h3 := each hc cd z
    have h4 := each hd de z
    have h5 := each he ea z
    omega
  have bound := Finset.sum_le_sum pointwise
  simp only [Finset.sum_add_distrib, total ha, total hb, total hc, total hd, total he,
    Finset.sum_const, smul_eq_mul] at bound
  have h1 := G.edgeSum a ha b ab
  have h2 := G.edgeSum b hb c bc
  have h3 := G.edgeSum c hc d cd
  have h4 := G.edgeSum d hd e de
  have h5 := G.edgeSum e he a ea
  have size := G.size
  omega

/-- The two disjoint color classes cover the local points. In the gap graph they
are cliques. Cross-class gap edges are allowed. -/
theorem two_sides [DecidableEq α] {V : Finset α} {N : α → Finset α} (G : GraphBounds V N) :
    ∃ A B : Finset α, Disjoint A B ∧ A ∪ B = V ∧
      (∀ x ∈ A, ∀ y ∈ A, y ∉ N x) ∧ (∀ x ∈ B, ∀ y ∈ B, y ∉ N x) := by
  classical
  have size := G.size
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < V.card by omega)
  have da := G.minDegree a ha
  obtain ⟨b, ab⟩ := Finset.card_pos.mp (show 0 < (N a).card by omega)
  have hb := G.closed a ha ab
  have ba := G.symm a ha b hb ab
  let twostep (x : α) := V.filter (fun z => ∃ y ∈ N x, z ∈ N y)
  have two_mem {x z : α} : z ∈ twostep x ↔ z ∈ V ∧ ∃ y ∈ N x, z ∈ N y :=
    Finset.mem_filter
  have independent (x : α) (hx : x ∈ V) :
      ∀ y ∈ twostep x, ∀ z ∈ twostep x, z ∉ N y := by
    intro y hy z hz yz
    obtain ⟨hyV, u, xu, uy⟩ := two_mem.mp hy
    obtain ⟨hzV, w, xw, wz⟩ := two_mem.mp hz
    have hw := G.closed x hx xw
    exact no_five G hx xu uy yz (G.symm w hw z hzV wz) (G.symm x hx w hw xw)
  refine ⟨twostep a, twostep b, ?_, ?_, independent a ha, independent b hb⟩
  · apply Finset.disjoint_left.mpr
    intro x ax bx
    obtain ⟨hx, u, au, ux⟩ := two_mem.mp ax
    obtain ⟨_, w, bw, wx⟩ := two_mem.mp bx
    have hw := G.closed b hb bw
    exact no_five G ha au ux (G.symm w hw x hx wx) (G.symm b hb w hw bw) ba
  · let R := V \ (N a ∪ N b)
    have sub : N a ∪ N b ⊆ V := Finset.union_subset (G.closed a ha) (G.closed b hb)
    have count : R.card ≤ 3 := by
      have hcard := Finset.card_sdiff_add_card_eq_card sub
      rw [Finset.card_union_of_disjoint (G.triangles a ha b ab)] at hcard
      have edge := G.edgeSum a ha b ab
      change (V \ (N a ∪ N b)).card ≤ 3
      omega
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with h | h <;> exact (two_mem.mp h).1
    · intro hx
      by_cases ax : x ∈ N a
      · exact Finset.mem_union.mpr (Or.inr (two_mem.mpr ⟨hx, a, ba, ax⟩))
      by_cases bx : x ∈ N b
      · exact Finset.mem_union.mpr (Or.inl (two_mem.mpr ⟨hx, b, ab, bx⟩))
      have xr : x ∈ R := Finset.mem_sdiff.mpr ⟨hx, fun hh => (Finset.mem_union.mp hh).elim ax bx⟩
      by_contra none
      have small : N x ⊆ R.erase x := by
        intro y xy
        have hy := G.closed x hx xy
        have yx := G.symm x hx y hy xy
        refine Finset.mem_erase.mpr ⟨fun e => G.loopless x hx (e ▸ xy), ?_⟩
        apply Finset.mem_sdiff.mpr
        refine ⟨hy, ?_⟩
        intro h
        rcases Finset.mem_union.mp h with ay | by'
        · exact none (Finset.mem_union.mpr (Or.inl (two_mem.mpr ⟨hx, y, ay, yx⟩)))
        · exact none (Finset.mem_union.mpr (Or.inr (two_mem.mpr ⟨hx, y, by', yx⟩)))
      have le := Finset.card_le_card small
      rw [Finset.card_erase_of_mem xr] at le
      have degree := G.minDegree x hx
      omega

end Order12.Local139

end

/- Component Erdos723.Local139.Incidence. -/
section

/- The local collinearity graph at a deficit-two point of a 139-line partial plane. -/

namespace Order12.Local139

/-- Light points among the gap neighbors of p. -/
def lights (S : Blocks) (p : Pt) : Finset Pt :=
  (holes S p).filter (fun y => (through S y).card = 11)

@[simp] lemma mem_lights {S : Blocks} {p q : Pt} :
    q ∈ lights S p ↔ q ∈ holes S p ∧ (through S q).card = 11 := Finset.mem_filter

/-- The collinearity neighborhood of y in L excludes y itself. -/
def oldNeighbors (S : Blocks) (L : Finset Pt) (y : Pt) : Finset Pt :=
  L \ insert y (holes S y)

@[simp] lemma mem_oldNeighbors {S : Blocks} {L : Finset Pt} {x y : Pt} :
    y ∈ oldNeighbors S L x ↔ y ∈ L ∧ y ≠ x ∧ y ∉ holes S x := by
  simp only [oldNeighbors, Finset.mem_sdiff, Finset.mem_insert, not_or]

lemma crowded {X A B C : Finset Pt} (n : X.card = 24) (hA : A ⊆ X) (hB : B ⊆ X) (hC : C ⊆ X)
    (sA : A.card = 12) (sB : B.card = 12) (sC : C.card = 12)
    (ab : (A ∩ B).card ≤ 3) (ac : (A ∩ C).card ≤ 3) (bc : (B ∩ C).card ≤ 3) : False := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A ∪ B) C
  have h3 := Finset.card_le_card (Finset.union_subset (Finset.union_subset hA hB) hC)
  have h4 := Finset.card_union_le (A ∩ C) (B ∩ C)
  rw [Finset.union_inter_distrib_right] at h2
  omega

/-- At most eight gap neighbors of a light point can be heavy. -/
lemma enough_lights (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) {p : Pt} (hp : (through S p).card = 11) :
    16 ≤ (lights S p).card := by
  classical
  let U := holes S p
  let L := lights S p
  have hu : U.card = 24 := by have := holes_card S h p; change (holes S p).card = 24; omega
  have extra := deficit_holes_sum S h p
  rw [size] at extra
  have dp : deficit S p = 2 := by unfold deficit; rw [hp]; decide
  rw [dp] at extra
  have ex8 : (∑ q ∈ U, (deficit S q - 2)) = 8 := extra.trans (by norm_num)
  have count : ((U \ L).card : ℤ) = ∑ y ∈ U, if y ∈ U \ L then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr Finset.sdiff_subset]
  have le : ((U \ L).card : ℤ) ≤ 8 := by
    rw [count, ← ex8]
    apply Finset.sum_le_sum
    intro y hy
    have pos := Finset.card_pos.mpr ⟨p, (holes_symm S p y).mp hy⟩
    have bound := holes_card S h y
    have n := noOne y
    by_cases hm : y ∈ U \ L
    · have notLight : (through S y).card ≠ 11 := fun e =>
        (Finset.mem_sdiff.mp hm).2 (mem_lights.mpr ⟨hy,e⟩)
      simp only [hm, if_true, deficit]
      omega
    · simp only [hm, if_false, deficit]
      omega
  have combined := Finset.card_sdiff_add_card_eq_card (show L ⊆ U from Finset.filter_subset _ _)
  change 16 ≤ L.card
  omega

/-- Incidence axioms give all finite graph hypotheses in the 139-line case. -/
theorem incidence_bounds (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) {p : Pt} (hp : (through S p).card = 11) :
    GraphBounds (lights S p) (oldNeighbors S (lights S p)) := by
  classical
  let U := holes S p
  let L := lights S p
  let N := oldNeighbors S L
  let K (x : Pt) := U ∩ holes S x
  have sizeL : 16 ≤ L.card := enough_lights S h size noOne hp
  have sizeU : U.card = 24 := by have := holes_card S h p; change (holes S p).card = 24; omega
  have sub (x : Pt) : N x ⊆ L := Finset.sdiff_subset
  have sym {x y : Pt} (hx : x ∈ L) (hy : y ∈ L) (xy : y ∈ N x) : x ∈ N y := by
    obtain ⟨_, ne, apart⟩ := mem_oldNeighbors.mp xy
    exact mem_oldNeighbors.mpr ⟨hx, ne.symm, fun h => apart ((holes_symm S x y).mpr h)⟩
  have twelve (x : Pt) (hx : x ∈ L) : (K x).card = 12 :=
    holes_meet_adj S h hp (mem_lights.mp hx).2 (mem_lights.mp hx).1
  have three {x y : Pt} (hx : x ∈ L) (xy : y ∈ N x) : (K x ∩ K y).card ≤ 3 := by
    obtain ⟨hy, ne, apart⟩ := mem_oldNeighbors.mp xy
    have four := holes_meet_nonadj S h (mem_lights.mp hx).2 (mem_lights.mp hy).2 ne.symm apart
    have base : p ∈ holes S x ∩ holes S y := Finset.mem_inter.mpr
      ⟨(holes_symm S p x).mp (mem_lights.mp hx).1, (holes_symm S p y).mp (mem_lights.mp hy).1⟩
    have inc : K x ∩ K y ⊆ (holes S x ∩ holes S y).erase p := by
      intro z hz
      obtain ⟨hzx, hzy⟩ := Finset.mem_inter.mp hz
      obtain ⟨hzp, hxz⟩ := Finset.mem_inter.mp hzx
      exact Finset.mem_erase.mpr ⟨(mem_holes.mp hzp).1,
        Finset.mem_inter.mpr ⟨hxz,(Finset.mem_inter.mp hzy).2⟩⟩
    have le := Finset.card_le_card inc
    rw [Finset.card_erase_of_mem base, four] at le
    exact le
  refine ⟨sizeL, (fun x _ => sub x), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x _ e => (mem_oldNeighbors.mp e).2.1 rfl
  · exact fun _ hx _ hy hxy => sym hx hy hxy
  · intro x hx y xy
    apply Finset.disjoint_left.mpr
    intro z xz yz
    have hy := sub x xy
    have hz := sub x xz
    exact crowded sizeU Finset.inter_subset_left Finset.inter_subset_left Finset.inter_subset_left
      (twelve x hx) (twelve y hy) (twelve z hz) (three hx xy) (three hx xz) (three hy yz)
  · intro x hx
    have inc : L \ N x ⊆ insert x (K x) := by
      intro z hz
      obtain ⟨hL, missing⟩ := Finset.mem_sdiff.mp hz
      by_cases e : z = x
      · exact Finset.mem_insert.mpr (Or.inl e)
      · by_cases gap : z ∈ holes S x
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mpr ⟨(mem_lights.mp hL).1, gap⟩))
        · exact (missing (mem_oldNeighbors.mpr ⟨hL, e, gap⟩)).elim
    have bound := Finset.card_le_card inc
    have single := Finset.card_insert_le x (K x)
    have union := Finset.card_sdiff_add_card_eq_card (sub x)
    have k := twelve x hx
    change 3 ≤ (N x).card
    omega
  · intro x hx y xy
    have hy := sub x xy
    have yx := sym hx hy xy
    have inc : L \ (N x ∪ N y) ⊆ K x ∩ K y := by
      intro z hz
      obtain ⟨hL, miss⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨nx, ny⟩ := not_or.mp (fun hh => miss (Finset.mem_union.mpr hh))
      have sx : z ≠ x := fun e => ny (e ▸ yx)
      have sy : z ≠ y := fun e => nx (e ▸ xy)
      have zx : z ∈ holes S x := by by_contra absent; exact nx (mem_oldNeighbors.mpr ⟨hL,sx,absent⟩)
      have zy : z ∈ holes S y := by by_contra absent; exact ny (mem_oldNeighbors.mpr ⟨hL,sy,absent⟩)
      have zu := (mem_lights.mp hL).1
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨zu,zx⟩,Finset.mem_inter.mpr ⟨zu,zy⟩⟩
    have bound := (Finset.card_le_card inc).trans (three hx xy)
    have total := Finset.card_sdiff_add_card_eq_card (Finset.union_subset (sub x) (sub y))
    have plus := Finset.card_union_le (N x) (N y)
    change L.card ≤ (N x).card + (N y).card + 3
    omega

end Order12.Local139

end

/- Component Erdos723.Local139.Sides. -/
section

/- The two gap cliques at a light point each have 5–11 vertices before adding the central point.
Each vertex has at most three gap neighbors in the opposite clique. -/

namespace Order12.Local139

def gapClique (S : Blocks) (C : Finset Pt) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → y ∈ holes S x

lemma degree_eleven_bound (S : Blocks) (C : Finset Pt) (gap : gapClique S C)
    (degree : ∀ x ∈ C, (through S x).card = 11) : C.card * 11 ≤ S.card := by
  classical
  have disj : (↑C : Set Pt).PairwiseDisjoint (through S) := by
    intro x hx y hy ne
    apply Finset.disjoint_left.mpr
    intro b hbx hby
    obtain ⟨hb, onx⟩ := mem_through.mp hbx
    exact (mem_holes.mp (gap x hx y hy ne)).2 ⟨b, hb, onx, (mem_through.mp hby).2⟩
  have sub : C.biUnion (through S) ⊆ S := by
    intro b hb
    obtain ⟨_, _, pencil⟩ := Finset.mem_biUnion.mp hb
    exact (mem_through.mp pencil).1
  have bound := Finset.card_le_card sub
  rwa [Finset.card_biUnion disj, Finset.sum_const_nat degree] at bound

/-- A local old-line independent set becomes a gap clique after the center is added. -/
lemma add_center (S : Blocks) (p : Pt) (C : Finset Pt)
    (sub : C ⊆ lights S p)
    (indep : ∀ x ∈ C, ∀ y ∈ C, y ∉ oldNeighbors S (lights S p) x) :
    gapClique S (insert p C) := by
  intro x hx y hy ne
  rcases Finset.mem_insert.mp hx with rfl | inX
  · have old := (Finset.mem_insert.mp hy).resolve_left ne.symm
    exact (mem_lights.mp (sub old)).1
  rcases Finset.mem_insert.mp hy with rfl | inY
  · exact (holes_symm S y x).mp (mem_lights.mp (sub inX)).1
  by_contra apart
  exact indep x inX y inY (mem_oldNeighbors.mpr ⟨sub inY, ne.symm, apart⟩)

/-- Local light neighbors split into two disjoint sets of size 5–11. Each set together
with p is a gap clique, and at most three cross-gap neighbors occur per vertex. -/
theorem local_partition (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) {p : Pt} (hp : (through S p).card = 11) :
    ∃ A B : Finset Pt, Disjoint A B ∧ A ∪ B = lights S p ∧
      5 ≤ A.card ∧ A.card ≤ 11 ∧ 5 ≤ B.card ∧ B.card ≤ 11 ∧
      gapClique S (insert p A) ∧ gapClique S (insert p B) ∧
      (∀ x ∈ A, (B ∩ holes S x).card ≤ 3) ∧ (∀ x ∈ B, (A ∩ holes S x).card ≤ 3) := by
  classical
  let L := lights S p
  let N := oldNeighbors S L
  have G : GraphBounds L N := incidence_bounds S h size noOne hp
  obtain ⟨A, B, sep, whole, indepA, indepB⟩ := two_sides G
  have hA : A ⊆ L := whole ▸ Finset.subset_union_left
  have hB : B ⊆ L := whole ▸ Finset.subset_union_right
  have cliqueA := add_center S p A hA indepA
  have cliqueB := add_center S p B hB indepB
  have cap (C : Finset Pt) (incl : C ⊆ L) (clique : gapClique S (insert p C)) : C.card ≤ 11 := by
    have degree : ∀ x ∈ insert p C, (through S x).card = 11 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · exact (mem_lights.mp (incl hx)).2
    have outside : p ∉ C := fun hc => (mem_holes.mp (mem_lights.mp (incl hc)).1).1 rfl
    have count := degree_eleven_bound S (insert p C) clique degree
    rw [Finset.card_insert_of_notMem outside, size] at count
    omega
  have upperA := cap A hA cliqueA
  have upperB := cap B hB cliqueB
  have card := Finset.card_union_of_disjoint sep
  rw [whole] at card
  have lower := G.size
  have cross (X Y : Finset Pt) (xSub : X ⊆ L) (ySub : Y ⊆ L)
      (cover : X ∪ Y = L) (separate : Disjoint X Y)
      (ix : ∀ x ∈ X, ∀ y ∈ X, y ∉ N x) (iy : ∀ x ∈ Y, ∀ y ∈ Y, y ∉ N x)
      (x : Pt) (hx : x ∈ X) : (Y ∩ holes S x).card ≤ 3 := by
    have degree := G.minDegree x (xSub hx)
    obtain ⟨y, xy⟩ := Finset.card_pos.mp (show 0 < (N x).card by omega)
    have localY := G.closed x (xSub hx) xy
    have nh (c : Pt) (hc : c ∈ X) : N c ⊆ Y := by
      intro z cz
      have hz := G.closed c (xSub hc) cz
      rw [← cover] at hz
      exact (Finset.mem_union.mp hz).resolve_left (fun hh => ix c hc z hh cz)
    have hy := nh x hx xy
    have ns : N y ⊆ X := by
      intro z yz
      have hz := G.closed y (ySub hy) yz
      rw [← cover] at hz
      exact (Finset.mem_union.mp hz).resolve_right (fun hh => iy y hy z hh yz)
    have near := G.edgeSum x (xSub hx) y xy
    have small := Finset.card_le_card ns
    have both := Finset.card_union_of_disjoint separate
    rw [cover] at both
    have uncleared : Y ∩ holes S x ⊆ Y \ N x := by
      intro z hz
      obtain ⟨inY, gap⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_sdiff.mpr ⟨inY, fun nz => (mem_oldNeighbors.mp nz).2.2 gap⟩
    have diff := Finset.card_sdiff_add_card_eq_card (nh x hx)
    have le := Finset.card_le_card uncleared
    omega
  exact ⟨A,B,sep,whole,by omega,upperA,by omega,upperB,cliqueA,cliqueB,
    cross A B hA hB whole sep indepA indepB,
    cross B A hB hA (by rw [Finset.union_comm, whole]) sep.symm indepB indepA⟩

end Order12.Local139

end

/- Component Erdos723.Gram139. -/
section

/-
# The missing incidence Gram matrix

For a partial plane of order 12, subtract the old incidence Gram matrix
from the full design Gram matrix. An explicit right inverse for the old
incidence matrix identifies the resulting rank and proves positivity.
-/

namespace Order12.Gram139

open Matrix
open scoped Matrix

def ones (ι κ : Type*) : Matrix ι κ ℝ := Matrix.of (fun _ _ => 1)

def incidence (S : Blocks) : Matrix S Pt ℝ :=
  Matrix.of (fun b p => if p ∈ b.val then 1 else 0)

def design (ι : Type*) [DecidableEq ι] : Matrix ι ι ℝ :=
  (12 : ℝ) • 1 + ones ι ι

noncomputable def gap (S : Blocks) : Matrix Pt Pt ℝ :=
  design Pt - (incidence S)ᵀ * incidence S

lemma ones_transpose (ι κ : Type*) : (ones ι κ)ᵀ = ones κ ι := rfl

lemma ones_mul (ι κ ν : Type*) [Fintype κ] :
    ones ι κ * ones κ ν = (Fintype.card κ : ℝ) • ones ι ν := by
  ext x y
  simp [Matrix.mul_apply, ones]

lemma incidence_row_gram (S : Blocks) (h : Good S) :
    incidence S * (incidence S)ᵀ = design S := by
  classical
  ext b c
  have count : (incidence S * (incidence S)ᵀ) b c = ((b.val ∩ c.val).card : ℝ) := by
    rw [Matrix.mul_apply]
    calc
      _ = ∑ p : Pt, (if p ∈ b.val ∩ c.val then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hb : p ∈ b.val <;> by_cases hc : p ∈ c.val <;>
          simp [incidence, Matrix.transpose_apply, hb, hc]
      _ = _ := by rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]; simp
  rw [count]
  by_cases e : b = c
  · subst c
    norm_num [h.1 b b.property, design, ones]
  · have ne : b.val ≠ c.val := fun eq => e (Subtype.ext eq)
    have one : (b.val ∩ c.val).card = 1 := Finset.card_eq_one_iff_existsUnique.mpr (by
      simpa using h.2 b b.property c c.property ne)
    simp [one, design, ones, e]

lemma incidence_mul_ones (S : Blocks) (h : Good S) (κ : Type*) :
    incidence S * ones Pt κ = (13 : ℝ) • ones S κ := by
  ext b i
  change (∑ p : Pt, (if p ∈ b.val then (1 : ℝ) else 0) * 1) = 13 * 1
  simp only [mul_one]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  simp [h.1 b b.property]

lemma ones_mul_incidence_transpose (S : Blocks) (h : Good S) (κ : Type*) :
    ones κ Pt * (incidence S)ᵀ = (13 : ℝ) • ones κ S := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_smul, ones_transpose]
    using congrArg Matrix.transpose (incidence_mul_ones S h κ)

lemma column_total (S : Blocks) (κ : Type*) (p : Pt) (i : κ) :
    ((incidence S)ᵀ * ones S κ) p i = ((through S p).card : ℝ) := by
  classical
  change (∑ b : S, (if p ∈ b.val then (1 : ℝ) else 0) * 1) = _
  simp only [mul_one, Finset.sum_coe_sort S (fun b => if p ∈ b then (1 : ℝ) else 0)]
  rw [← Finset.sum_filter]
  simp [through]

/-- Multiply by the old incidence transpose. Each output column is the deficit vector. -/
theorem gap_mul_incidence_transpose (S : Blocks) (h : Good S) :
    gap S * (incidence S)ᵀ = Matrix.of (fun p _ => (deficit S p : ℝ)) := by
  unfold gap
  rw [Matrix.sub_mul, Matrix.mul_assoc, incidence_row_gram S h]
  unfold design
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, ones_mul_incidence_transpose S h,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  ext p b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, column_total]
  change 12 * _ + 13 * 1 - (12 * _ + _) = _
  push_cast [deficit]
  ring

/-- Multiplication by an all-ones column gives thirteen times the deficit. -/
theorem gap_mul_ones (S : Blocks) (h : Good S) (κ : Type*) :
    gap S * ones Pt κ = Matrix.of (fun p _ => 13 * (deficit S p : ℝ)) := by
  unfold gap design
  rw [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, ones_mul,
    Matrix.mul_assoc, incidence_mul_ones S h, Matrix.mul_smul]
  ext p i
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, column_total]
  change 12 * 1 + (Fintype.card (Fin 157) : ℝ) * 1 - 13 * _ = _
  rw [Fintype.card_fin]
  push_cast [deficit]
  ring

private lemma design_transpose (ι : Type*) [DecidableEq ι] : (design ι)ᵀ = design ι := by
  simp only [design, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    ones_transpose]

private lemma gap_transpose (S : Blocks) : (gap S)ᵀ = gap S := by
  simp only [gap, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    design_transpose]

/-- The full design matrix is positive definite on any finite index set. -/
lemma design_posDef (ι : Type*) [DecidableEq ι] [Fintype ι] : (design ι).PosDef := by
  have gram := Matrix.posSemidef_conjTranspose_mul_self (ones Unit ι)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ones_transpose, ones_mul] at gram
  have j : (ones ι ι).PosSemidef := by simpa using gram
  exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 12)).add_posSemidef j

private noncomputable def rightInv (S : Blocks) : Matrix Pt S ℝ :=
  (1/12 : ℝ) • (incidence S)ᵀ - (1/156 : ℝ) • ones Pt S

private lemma mul_rightInv (S : Blocks) (h : Good S) :
    incidence S * rightInv S = 1 := by
  unfold rightInv
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, incidence_row_gram S h,
    incidence_mul_ones S h]
  unfold design
  module

private lemma design_rightInv (S : Blocks) (h : Good S) :
    design Pt * rightInv S = (incidence S)ᵀ := by
  unfold rightInv
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
  unfold design
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.one_mul, ones_mul_incidence_transpose S h, ones_mul]
  change _ - (1/156 : ℝ) • (12 • ones Pt S + ((157 : ℕ) : ℝ) • ones Pt S) = _
  module

/-- The gap Gram matrix is positive semidefinite; its rank is the number of missing lines. -/
theorem gap_psd_and_rank (S : Blocks) (h : Good S) :
    (gap S).PosSemidef ∧ (gap S).rank + S.card = 157 := by
  classical
  let A := incidence S
  let R := rightInv S
  let P : Matrix Pt Pt ℝ := 1 - R * A
  have ar : A * R = 1 := mul_rightInv S h
  have ap : A * P = 0 := by
    dsimp only [P]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ar, Matrix.one_mul, sub_self]
  have mp : design Pt * P = gap S := by
    dsimp only [P]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, design_rightInv S h]
    rfl
  have ptm : Pᵀ * design Pt = gap S := by
    simpa only [Matrix.transpose_mul, design_transpose, gap_transpose] using
      congrArg Matrix.transpose mp
  have kp : gap S * P = gap S := by
    change (design Pt - Aᵀ * A) * P = _
    rw [Matrix.sub_mul, Matrix.mul_assoc, ap, Matrix.mul_zero, sub_zero, mp]
  constructor
  · have gram := (design_posDef Pt).posSemidef.conjTranspose_mul_mul_same P
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, ptm, kp] at gram
  · have surj : Function.Surjective A.mulVecLin := by
      intro v
      refine ⟨R *ᵥ v, ?_⟩
      change A *ᵥ (R *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, ar, Matrix.one_mulVec]
    have dimA : A.rank = S.card := by
      rw [Matrix.rank, LinearMap.range_eq_top.mpr surj, finrank_top, Module.finrank_pi]
      exact Fintype.card_coe S
    have rangeP : LinearMap.range P.mulVecLin = LinearMap.ker A.mulVecLin := by
      apply le_antisymm
      · rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, ap, Matrix.mulVecLin_zero]
      · intro v hv
        refine ⟨v, ?_⟩
        change (1 - R * A) *ᵥ v = v
        change A *ᵥ v = 0 at hv
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv,
          Matrix.mulVec_zero, sub_zero]
    have dims := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [← rangeP] at dims
    change A.rank + P.rank = _ at dims
    rw [Module.finrank_pi, Fintype.card_fin, dimA] at dims
    rw [← mp, Matrix.rank_mul_eq_right_of_isUnit_det (design Pt) P
      ((design Pt).isUnit_iff_isUnit_det.mp (design_posDef Pt).isUnit)]
    omega

theorem gap139 (S : Blocks) (h : Good S) (n : S.card = 139) :
    (gap S).PosSemidef ∧ (gap S).rank = 18 := by
  obtain ⟨psd, dim⟩ := gap_psd_and_rank S h
  exact ⟨psd, by omega⟩

/-- The diagonal entries are the deficits. Off-diagonal entries indicate uncovered pairs. -/
theorem gap_entry (S : Blocks) (h : Good S) (p q : Pt) :
    gap S p q = if p = q then (deficit S p : ℝ) else if q ∈ holes S p then 1 else 0 := by
  classical
  let C := S.filter (fun b => p ∈ b ∧ q ∈ b)
  have dot : ((incidence S)ᵀ * incidence S) p q = (C.card : ℝ) := by
    rw [Matrix.mul_apply]
    change (∑ b : S, (if p ∈ b.val then (1 : ℝ) else 0) *
      (if q ∈ b.val then (1 : ℝ) else 0)) = _
    rw [Finset.sum_coe_sort S
      (fun b => (if p ∈ b then (1 : ℝ) else 0) * (if q ∈ b then 1 else 0))]
    calc
      _ = ∑ b ∈ S, (if p ∈ b ∧ q ∈ b then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hp : p ∈ b <;> by_cases hq : q ∈ b <;> simp [hp, hq]
      _ = _ := by rw [← Finset.sum_filter]; simp [C]
  by_cases eq : p = q
  · subst q
    have eqC : C = through S p := by ext; simp [C, through]
    simp only [gap, Matrix.sub_apply, design, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, dot, eqC, if_true]
    change 12 + 1 - ((through S p).card : ℝ) = _
    push_cast [deficit]
    ring
  · have selfZero : (1 : Matrix Pt Pt ℝ) p q = 0 := by simp [eq]
    simp only [gap, Matrix.sub_apply, design, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      selfZero, mul_zero, zero_add, dot, eq, if_false]
    change 1 - (C.card : ℝ) = _
    by_cases adj : q ∈ holes S p
    · have empty : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro b hb
        obtain ⟨hb, hp, hq⟩ := Finset.mem_filter.mp hb
        exact (mem_holes.mp adj).2 ⟨b, hb, hp, hq⟩)
      simp only [adj, if_true, empty, Finset.card_empty, Nat.cast_zero, sub_zero]
    · have ex : ∃ b ∈ S, p ∈ b ∧ q ∈ b := by
        by_contra no
        exact adj (mem_holes.mpr ⟨Ne.symm eq, no⟩)
      obtain ⟨b, hb, hp, hq⟩ := ex
      have single : C = {b} := by
        ext c
        simp only [C, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hc, hcp, hcq⟩
          by_contra ne
          exact eq ((h.2 c hc b hb ne).unique ⟨hcp, hp⟩ ⟨hcq, hq⟩)
        · rintro rfl
          exact ⟨hb, hp, hq⟩
      simp only [adj, if_false, single, Finset.card_singleton, Nat.cast_one, sub_self]

/-- Spectral coordinates for a positive semidefinite matrix need only its nonzero eigenvalues. -/
private theorem ranked_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (psd : M.PosSemidef) (s : ℕ) (rk : M.rank = s) :
    ∃ V : Matrix (Fin s) ι ℝ, Vᵀ * V = M ∧ V.rank = s := by
  classical
  let E := psd.isHermitian.eigenvalues
  let U : Matrix ι ι ℝ := psd.isHermitian.eigenvectorUnitary
  let I := {j : ι // E j ≠ 0}
  let e : Fin s ≃ I := (Fintype.equivFinOfCardEq (show Fintype.card I = s from
    psd.isHermitian.rank_eq_card_non_zero_eigs.symm.trans rk)).symm
  let V : Matrix (Fin s) ι ℝ := Matrix.of (fun i p => Real.sqrt (E (e i)) * U p (e i))
  have spec : M = U * Matrix.diagonal E * Uᵀ := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp]
      using psd.isHermitian.spectral_theorem
  have fac : Vᵀ * V = M := by
    ext p q
    let term (j : ι) := U p j * E j * U q j
    calc
      _ = ∑ i : Fin s, term (e i) := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [term, V]
        calc
          _ = (Real.sqrt (E (e i)) * Real.sqrt (E (e i))) * (U p (e i) * U q (e i)) := by ring
          _ = _ := by rw [Real.mul_self_sqrt (psd.eigenvalues_nonneg _)]; ring
      _ = ∑ j : I, term j := e.sum_comp (fun j : I => term j)
      _ = ∑ j : ι, term j := by
        have split := Fintype.sum_subtype_add_sum_subtype (fun j : ι => E j ≠ 0) term
        have vanish : ∑ j : {i : ι // ¬ E i ≠ 0}, term j = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          simp only [term, not_ne_iff.mp j.property, mul_zero, zero_mul]
        rw [vanish, add_zero] at split
        exact split
      _ = (U * Matrix.diagonal E * Uᵀ) p q := by
        rw [Matrix.mul_apply]
        simp only [term, Matrix.mul_diagonal, Matrix.transpose_apply]
      _ = M p q := congrArg (fun T : Matrix ι ι ℝ => T p q) spec.symm
  have rankV := Matrix.rank_transpose_mul_self V
  rw [fac, rk] at rankV
  exact ⟨V, fac, rankV.symm⟩

/-- For 139 lines, the gap data are exactly the Gram matrix of 157 vectors spanning ℝ¹⁸. -/
theorem gap139_factor (S : Blocks) (h : Good S) (n : S.card = 139) :
    ∃ V : Matrix (Fin 18) Pt ℝ, Vᵀ * V = gap S ∧ V.rank = 18 :=
  ranked_factor (gap S) (gap139 S h n).1 18 (gap139 S h n).2

end Order12.Gram139

end

/- Component Erdos723.Local139.Projection. -/
section

/-
# A light point outside a large light clique

Use positivity of the gap Gram matrix on the clique and one outside point.
The resulting quadratic inequality rules out three and four neighbors
when the clique has at least nine points.
-/

namespace Order12.Gram139

open Matrix
open scoped Matrix

private theorem clique_inequality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Option ι) (Option ι) ℝ) (pos : Q.PosSemidef)
    (g : ι → ℝ) (squares : ∀ i, g i * g i = g i)
    (nn : Q none none = 2) (ns : ∀ i, Q none (some i) = g i)
    (sn : ∀ i, Q (some i) none = g i)
    (ss : ∀ i j, Q (some i) (some j) = 1 + if i = j then 1 else 0) :
    0 ≤ (2 - ∑ i, g i) * ((Fintype.card ι : ℝ) + 1) + (∑ i, g i) ^ 2 := by
  classical
  let s := ∑ i, g i
  let r := (Fintype.card ι : ℝ) + 1
  let z : Option ι → ℝ := fun i => i.elim r (fun j => s - r * g j)
  have sumZ : ∑ j, (s - r * g j) = -s := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    change (Fintype.card ι : ℝ) * s - ((Fintype.card ι : ℝ) + 1) * s = -s
    ring
  have sumGZ : ∑ j, g j * (s - r * g j) = s * s - r * s := by
    calc
      _ = ∑ j, (g j * s - r * g j) := by
        apply Finset.sum_congr rfl
        intro j _
        linear_combination -r * squares j
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  have az (i : ι) : (Q *ᵥ z) (some i) = 0 := by
    change (∑ v, Q (some i) v * z v) = 0
    rw [Fintype.sum_option, sn]
    change g i * r + ∑ j, Q (some i) (some j) * (s - r * g j) = 0
    have split : ∑ j, Q (some i) (some j) * (s - r * g j) =
        (∑ j, (s - r * g j)) + (s - r * g i) := by
      calc
        _ = ∑ j, ((s - r * g j) + if i = j then s - r * g j else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [ss]
          by_cases e : i = j
          · simp only [e, if_true]; ring
          · simp [e]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    rw [split, sumZ]
    ring
  have aw : (Q *ᵥ z) none = 2 * r + (s * s - r * s) := by
    change (∑ v, Q none v * z v) = _
    rw [Fintype.sum_option, nn]
    change 2 * r + ∑ j, Q none (some j) * (s - r * g j) = _
    simp only [ns, sumGZ]
  have nonneg := pos.dotProduct_mulVec_nonneg z
  change 0 ≤ ∑ v, star z v * (Q *ᵥ z) v at nonneg
  rw [Fintype.sum_option, aw] at nonneg
  simp only [Pi.star_apply, star_trivial, az, mul_zero, Finset.sum_const_zero, add_zero] at nonneg
  change 0 ≤ r * (2 * r + (s * s - r * s)) at nonneg
  have rp : 0 < r := by dsimp [r]; positivity
  change 0 ≤ (2-s)*r+s^2
  by_contra! neg
  have bad : 2 * r + (s*s-r*s) < 0 := by linarith only [neg]
  exact (not_lt_of_ge nonneg) (mul_neg_of_pos_of_neg rp bad)

/-- A light point outside a light clique of size at least nine has at most two
neighbors there if it misses a clique member. -/
theorem outside_large_light_clique (S : Blocks) (h : Good S) (C : Finset Pt)
    (large : 9 ≤ C.card)
    (clique : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → v ∈ holes S u)
    (lights : ∀ u ∈ C, (through S u).card = 11)
    (w : Pt) (outside : w ∉ C) (light : (through S w).card = 11)
    (miss : ¬ C ⊆ holes S w) : (C ∩ holes S w).card ≤ 2 := by
  classical
  obtain ⟨v, hv, hvw⟩ := Finset.not_subset.mp miss
  have ne : w ≠ v := fun e => outside (e ▸ hv)
  have sub : C ∩ holes S w ⊆ holes S w ∩ holes S v := by
    intro p hp
    obtain ⟨hpc, hpw⟩ := Finset.mem_inter.mp hp
    exact Finset.mem_inter.mpr ⟨hpw, clique v hv p hpc (fun e => hvw (e ▸ hpw))⟩
  have upper := Finset.card_le_card sub
  rw [holes_meet_nonadj S h light (lights v hv) ne hvw] at upper
  let f : Option C → Pt := fun i => i.elim w Subtype.val
  let Q := (gap S).submatrix f f
  let g : C → ℝ := fun i => if i.val ∈ holes S w then 1 else 0
  have pos : Q.PosSemidef := (gap_psd_and_rank S h).1.submatrix f
  have squares (i : C) : g i * g i = g i := by
    unfold g
    split <;> norm_num
  have nn : Q none none = 2 := by
    change gap S w w = 2
    rw [gap_entry S h]
    norm_num [deficit, light]
  have wn (i : C) : w ≠ i.val := fun e => outside (e ▸ i.property)
  have ns (i : C) : Q none (some i) = g i := by
    change gap S w i.val = _
    rw [gap_entry S h, if_neg (wn i)]
  have sn (i : C) : Q (some i) none = g i := by
    change gap S i.val w = _
    rw [gap_entry S h, if_neg (wn i).symm]
    simp only [g, ← holes_symm S w i.val]
  have ss (i j : C) : Q (some i) (some j) = 1 + if i = j then 1 else 0 := by
    change gap S i.val j.val = _
    rw [gap_entry S h]
    by_cases e : i = j
    · subst j
      norm_num [deficit, lights i i.property]
    · have diff : i.val ≠ j.val := fun eq => e (Subtype.ext eq)
      simp only [diff, e, if_false, clique i i.property j j.property diff, if_true, add_zero]
  have cnt : ∑ i, g i = ((C ∩ holes S w).card : ℝ) := by
    unfold g
    rw [Finset.sum_coe_sort C (fun q => if q ∈ holes S w then (1 : ℝ) else 0),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter]
    simp
  have cert := clique_inequality Q pos g squares nn ns sn ss
  rw [cnt, Fintype.card_coe] at cert
  have kl : (9 : ℝ) ≤ C.card := by exact_mod_cast large
  by_contra! low
  have cases : (C ∩ holes S w).card = 3 ∨ (C ∩ holes S w).card = 4 := by omega
  rcases cases with e | e <;> rw [e] at cert <;> norm_num at cert <;> linarith

end Order12.Gram139

end

/- Component Erdos723.Local139.Cliques. -/
section

/- The maximal light cliques of size at least six are exactly the two local
sides through each of their points. -/

namespace Order12.Local139

def Light (S : Blocks) (x : Pt) : Prop := (through S x).card = 11

structure Canonical (S : Blocks) (C : Finset Pt) : Prop where
  size : 6 ≤ C.card
  light : ∀ x ∈ C, Light S x
  gaps : gapClique S C
  maximal : ∀ y, Light S y → y ∉ C → ¬ C ⊆ holes S y

def LargeBound (S : Blocks) : Prop :=
  ∀ C : Finset Pt, 9 ≤ C.card → gapClique S C → (∀ x ∈ C, Light S x) →
    ∀ y, Light S y → y ∉ C → ¬ C ⊆ holes S y → (C ∩ holes S y).card ≤ 2

theorem large_bound (S : Blocks) (h : Good S) : LargeBound S := by
  intro C large clique lights w light outside miss
  exact Gram139.outside_large_light_clique S h C large clique lights w outside light miss

structure Chart (S : Blocks) (p : Pt) where
  a : Finset Pt
  b : Finset Pt
  apart : Disjoint a b
  cover : a ∪ b = lights S p
  fiveA : 5 ≤ a.card
  fiveB : 5 ≤ b.card
  cliqueA : gapClique S (insert p a)
  cliqueB : gapClique S (insert p b)
  crossA : ∀ x ∈ a, (b ∩ holes S x).card ≤ 3
  crossB : ∀ x ∈ b, (a ∩ holes S x).card ≤ 3

lemma chart_exists (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) {p : Pt} (hp : Light S p) : Nonempty (Chart S p) := by
  obtain ⟨a,b,d,e,la,_,lb,_,ca,cb,xa,xb⟩ := local_partition S h size noOne hp
  exact ⟨⟨a,b,d,e,la,lb,ca,cb,xa,xb⟩⟩

namespace Chart

variable {S : Blocks} {p : Pt}

def swap (t : Chart S p) : Chart S p :=
  ⟨t.b,t.a,t.apart.symm,by rw [Finset.union_comm,t.cover],t.fiveB,t.fiveA,
    t.cliqueB,t.cliqueA,t.crossB,t.crossA⟩

lemma a_sub (t : Chart S p) : t.a ⊆ lights S p := t.cover ▸ Finset.subset_union_left

lemma center_off (t : Chart S p) : p ∉ t.a := fun hp =>
  (mem_holes.mp (mem_lights.mp (t.a_sub hp)).1).1 rfl

lemma side_canonical (t : Chart S p) (hp : Light S p) : Canonical S (insert p t.a) := by
  refine ⟨?_, ?_, t.cliqueA, ?_⟩
  · rw [Finset.card_insert_of_notMem t.center_off]
    have := t.fiveA
    omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | old
    · exact hp
    · exact (mem_lights.mp (t.a_sub old)).2
  · intro y ly outside sees
    have yp := (holes_symm S p y).mpr (sees (Finset.mem_insert_self _ _))
    have near : y ∈ lights S p := mem_lights.mpr ⟨yp,ly⟩
    rw [← t.cover] at near
    have yb := (Finset.mem_union.mp near).resolve_left fun a => outside (Finset.mem_insert_of_mem a)
    have sub : t.a ⊆ t.a ∩ holes S y := fun x hx =>
      Finset.mem_inter.mpr ⟨hx,sees (Finset.mem_insert_of_mem hx)⟩
    have le := (Finset.card_le_card sub).trans (t.crossB y yb)
    have := t.fiveA
    omega

/-- A clique of at least six through the center cannot use both sides. -/
lemma no_mixed (t : Chart S p) (hp : Light S p) (large : LargeBound S)
    (big : 8 ≤ t.a.card) {D : Finset Pt} (nD : 6 ≤ D.card) (cl : gapClique S D)
    (lightD : ∀ w ∈ D, Light S w) (pd : p ∈ D) :
    D ⊆ insert p t.a ∨ D ⊆ insert p t.b := by
  by_contra! neither
  obtain ⟨w, wd, outside⟩ := Finset.not_subset.mp neither.1
  obtain ⟨z, zd, beyond⟩ := Finset.not_subset.mp neither.2
  have locate {x : Pt} (xd : x ∈ D) (xp : x ≠ p) : x ∈ t.a ∪ t.b := by
    rw [t.cover]
    exact mem_lights.mpr ⟨cl p pd x xd xp.symm,lightD x xd⟩
  have zz : z ≠ p ∧ z ∉ t.b := by simpa only [Finset.mem_insert, not_or] using beyond
  have za := (Finset.mem_union.mp (locate zd zz.1)).resolve_right zz.2
  let C := insert p t.a
  have canon := t.side_canonical hp
  have cardC : 9 ≤ C.card := by
    change 9 ≤ (insert p t.a).card
    rw [Finset.card_insert_of_notMem t.center_off]
    omega
  have cut := large C cardC canon.gaps canon.light w (lightD w wd) outside
    (canon.maximal w (lightD w wd) outside)
  have small : D ∩ C ⊆ C ∩ holes S w := by
    intro x hx
    obtain ⟨xd, xc⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨xc,cl w wd x xd (fun e => outside (e ▸ xc))⟩
  have other : D \ C ⊆ t.b ∩ holes S z := by
    intro x hx
    obtain ⟨xd, xn⟩ := Finset.mem_sdiff.mp hx
    have miss : x ≠ p ∧ x ∉ t.a := by simpa only [C,Finset.mem_insert,not_or] using xn
    have xb := (Finset.mem_union.mp (locate xd miss.1)).resolve_left miss.2
    have nz : z ≠ x := fun e => miss.2 (e ▸ za)
    exact Finset.mem_inter.mpr ⟨xb,cl z zd x xd nz⟩
  have le1 := (Finset.card_le_card small).trans cut
  have le2 := (Finset.card_le_card other).trans (t.crossA z za)
  have total := Finset.card_sdiff_add_card_inter D C
  omega

lemma canonical_eq (t : Chart S p) (hp : Light S p) (large : LargeBound S)
    (enough : 16 ≤ (lights S p).card) {D : Finset Pt} (can : Canonical S D) (pd : p ∈ D) :
    D = insert p t.a ∨ D = insert p t.b := by
  have card := Finset.card_union_of_disjoint t.apart
  rw [t.cover] at card
  have cmp : D ⊆ insert p t.a ∨ D ⊆ insert p t.b := by
    by_cases first : 8 ≤ t.a.card
    · exact t.no_mixed hp large first can.size can.gaps can.light pd
    · exact (t.swap.no_mixed hp large (by change 8 ≤ t.b.card; omega) can.size can.gaps can.light pd).symm
  have equal {C : Finset Pt} (sub : D ⊆ C) (cc : Canonical S C) : D = C := by
    apply Finset.Subset.antisymm sub
    intro y yc
    by_contra outside
    apply can.maximal y (cc.light y yc) outside
    intro x xd
    exact cc.gaps y yc x (sub xd) (fun eq => outside (eq ▸ xd))
  exact cmp.imp (fun h => equal h (t.side_canonical hp)) (fun h => equal h (t.swap.side_canonical hp))

end Chart

/-- The two endpoints of the edge represented by p, as a pair of cliques.
Their union contains every light neighbor, and their intersection is just p. -/
theorem endpoints (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12)
    {p : Pt} (hp : Light S p) :
    ∃ C D : Finset Pt, Canonical S C ∧ Canonical S D ∧ C ≠ D ∧
      C ∩ D = {p} ∧ C ∪ D = insert p (lights S p) ∧
      ∀ E, Canonical S E → p ∈ E → E = C ∨ E = D := by
  obtain ⟨t⟩ := chart_exists S h size noOne hp
  refine ⟨insert p t.a,insert p t.b,t.side_canonical hp,t.swap.side_canonical hp,?_,?_,?_,
    fun E ce pe => t.canonical_eq hp (large_bound S h) (enough_lights S h size noOne hp) ce pe⟩
  · have pos : 0 < t.a.card := lt_of_lt_of_le (by decide : 0 < 5) t.fiveA
    obtain ⟨x,xa⟩ := Finset.card_pos.mp pos
    intro eq
    have xc : x ∈ insert p t.b := eq ▸ Finset.mem_insert_of_mem xa
    rcases Finset.mem_insert.mp xc with xp | xb
    · exact t.center_off (xp ▸ xa)
    · exact Finset.disjoint_left.mp t.apart xa xb
  · ext x
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨ha,hb⟩
      by_contra ne
      exact Finset.disjoint_left.mp t.apart (ha.resolve_left ne) (hb.resolve_left ne)
    · exact fun e => ⟨Or.inl e,Or.inl e⟩
  · ext x
    rw [← t.cover]
    simp only [Finset.mem_union,Finset.mem_insert]
    tauto

/-- Distinct light vertices are gap-adjacent exactly when their edges have a
common endpoint, and the common endpoint is unique. -/
theorem shared_endpoint (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12)
    {p q : Pt} (hp : Light S p) (hq : Light S q) (ne : p ≠ q) :
    q ∈ holes S p ↔ ∃! C : Finset Pt, Canonical S C ∧ p ∈ C ∧ q ∈ C := by
  constructor
  · intro gap
    obtain ⟨a,b,ca,cb,_,meet,union,through⟩ := endpoints S h size noOne hp
    have both : p ∈ a ∩ b := by rw [meet]; exact Finset.mem_singleton_self _
    have some : q ∈ a ∪ b := by rw [union]; exact Finset.mem_insert_of_mem (mem_lights.mpr ⟨gap,hq⟩)
    have noPair : ¬ (q ∈ a ∧ q ∈ b) := by
      intro pair
      have m := Finset.mem_inter.mpr pair
      rw [meet,Finset.mem_singleton] at m
      exact ne m.symm
    obtain ⟨pa,pb⟩ := Finset.mem_inter.mp both
    rcases Finset.mem_union.mp some with qa | qb
    · refine ⟨a,⟨ca,pa,qa⟩,?_⟩
      rintro C ⟨cc,pc,qc⟩
      exact (through C cc pc).resolve_right (fun e => noPair ⟨qa,e ▸ qc⟩)
    · refine ⟨b,⟨cb,pb,qb⟩,?_⟩
      rintro C ⟨cc,pc,qc⟩
      exact (through C cc pc).resolve_left (fun e => noPair ⟨e ▸ qc,qb⟩)
  · rintro ⟨C,⟨cc,pc,qc⟩,_⟩
    exact cc.gaps p pc q qc ne

end Order12.Local139

end

/- Component Erdos723.Local139.LineGraph. -/
section

/- Realize the light gap graph as the line graph of the graph of maximal cliques. -/

namespace Order12.Local139

abbrev LightPoint (S : Blocks) := {x : Pt // Light S x}
abbrev CliqueVertex (S : Blocks) := {C : Finset Pt // Canonical S C}

def lightGraph (S : Blocks) : SimpleGraph (LightPoint S) where
  Adj x y := y.val ∈ holes S x.val
  symm := ⟨fun x y => (holes_symm S x.val y.val).mp⟩
  loopless := ⟨fun _ h => (mem_holes.mp h).1 rfl⟩

def cliqueGraph (S : Blocks) : SimpleGraph (CliqueVertex S) where
  Adj a b := a ≠ b ∧ ∃ p, p ∈ a.val ∧ p ∈ b.val
  symm := ⟨fun _ _ ⟨ne,p,a,b⟩ => ⟨ne.symm,p,b,a⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Each light point gives exactly the edge joining its two canonical cliques. -/
theorem edge_realization (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) :
    ∃ f : LightPoint S ≃ (cliqueGraph S).edgeSet,
      ∀ x (C : CliqueVertex S), C ∈ (f x : Sym2 (CliqueVertex S)) ↔ x.val ∈ C.val := by
  classical
  have one (x : LightPoint S) : ∃ e : (cliqueGraph S).edgeSet,
      ∀ C : CliqueVertex S, C ∈ (e : Sym2 (CliqueVertex S)) ↔ x.val ∈ C.val := by
    obtain ⟨C,D,c,d,ne,inter,_,locate⟩ := endpoints S h size noOne x.property
    have both : x.val ∈ C ∩ D := by rw [inter]; exact Finset.mem_singleton_self _
    obtain ⟨xc,xd⟩ := Finset.mem_inter.mp both
    let a : CliqueVertex S := ⟨C,c⟩
    let b : CliqueVertex S := ⟨D,d⟩
    have edge : (cliqueGraph S).Adj a b := ⟨fun e => ne (congrArg Subtype.val e),x.val,xc,xd⟩
    refine ⟨⟨s(a,b),(cliqueGraph S).mem_edgeSet.mpr edge⟩,?_⟩
    intro E
    change E ∈ s(a,b) ↔ x.val ∈ E.val
    rw [Sym2.mem_iff]
    constructor
    · rintro (rfl | rfl)
      · exact xc
      · exact xd
    · intro xe
      exact (locate E.val E.property xe).imp (fun e => Subtype.ext e) (fun e => Subtype.ext e)
  choose f mem using one
  have inj : Function.Injective f := by
    intro x y eq
    obtain ⟨C,D,c,d,_,inter,_,_⟩ := endpoints S h size noOne x.property
    have both : x.val ∈ C ∩ D := by rw [inter]; exact Finset.mem_singleton_self _
    have pass (v : CliqueVertex S) (on : x.val ∈ v.val) : y.val ∈ v.val := by
      apply (mem y v).mp
      rw [← eq]
      exact (mem x v).mpr on
    have bothY := Finset.mem_inter.mpr ⟨pass ⟨C,c⟩ (Finset.mem_inter.mp both).1,
      pass ⟨D,d⟩ (Finset.mem_inter.mp both).2⟩
    rw [inter,Finset.mem_singleton] at bothY
    exact Subtype.ext bothY.symm
  have surj : Function.Surjective f := by
    rintro ⟨e,edge⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      obtain ⟨diff,p,pa,pb⟩ := (cliqueGraph S).mem_edgeSet.mp edge
      let x : LightPoint S := ⟨p,a.property.light p pa⟩
      refine ⟨x,Subtype.ext ((Sym2.mem_and_mem_iff diff).mp ?_)⟩
      exact ⟨(mem x a).mpr pa, (mem x b).mpr pb⟩
  exact ⟨Equiv.ofBijective f ⟨inj,surj⟩,mem⟩

/-- The degree of a vertex of the reconstructed graph equals its clique size. -/
theorem degree_is_size (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (C : CliqueVertex S) :
    Nat.card ((cliqueGraph S).neighborSet C) = C.val.card := by
  obtain ⟨f,mem⟩ := edge_realization S h size noOne
  let send (u : C.val) : LightPoint S := ⟨u.val,C.property.light u.val u.property⟩
  let g (u : C.val) : (cliqueGraph S).incidenceSet C :=
    ⟨(f (send u)).val,(f (send u)).property,(mem (send u) C).mpr u.property⟩
  have inj : Function.Injective g := by
    intro x y e
    have eq : f (send x) = f (send y) := Subtype.ext
      (congrArg (fun z : (cliqueGraph S).incidenceSet C => z.val) e)
    exact Subtype.ext (congrArg (fun z : LightPoint S => z.val) (f.injective eq))
  have surj : Function.Surjective g := by
    intro edge
    let e : (cliqueGraph S).edgeSet := ⟨edge.val,edge.property.1⟩
    obtain ⟨x,hx⟩ := f.surjective e
    have onEdge : C ∈ (f x : Sym2 (CliqueVertex S)) := by
      rw [hx]; exact edge.property.2
    let u : C.val := ⟨x.val,(mem x C).mp onEdge⟩
    refine ⟨u,Subtype.ext ?_⟩
    exact congrArg (fun z : (cliqueGraph S).edgeSet => z.val) hx
  let eq := (Equiv.ofBijective g ⟨inj,surj⟩).trans ((cliqueGraph S).incidenceSetEquivNeighborSet C)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using (Nat.card_congr eq).symm

/-- The endpoints of the edge for x have total degree two more than its number of light gap neighbors. -/
theorem endpoint_degree_sum (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (x : LightPoint S)
    (C D : CliqueVertex S) (ne : C ≠ D) (cx : x.val ∈ C.val) (dx : x.val ∈ D.val) :
    Nat.card ((cliqueGraph S).neighborSet C) + Nat.card ((cliqueGraph S).neighborSet D) =
      (lights S x.val).card + 2 := by
  obtain ⟨A,B,_,_,_,inter,union,locate⟩ := endpoints S h size noOne x.property
  have noLoop : x.val ∉ lights S x.val := fun m => (mem_holes.mp (mem_lights.mp m).1).1 rfl
  have total := Finset.card_union_add_card_inter A B
  rw [union,inter,Finset.card_insert_of_notMem noLoop,Finset.card_singleton] at total
  rw [degree_is_size S h size noOne C, degree_is_size S h size noOne D]
  rcases locate C.val C.property cx with c | c <;> rcases locate D.val D.property dx with d | d
  · exact (ne (Subtype.ext (c.trans d.symm))).elim
  · rw [c,d]; omega
  · rw [c,d]; omega
  · exact (ne (Subtype.ext (c.trans d.symm))).elim

theorem degree_bounds (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (C : CliqueVertex S) :
    6 ≤ Nat.card ((cliqueGraph S).neighborSet C) ∧ Nat.card ((cliqueGraph S).neighborSet C) ≤ 12 := by
  rw [degree_is_size S h size noOne C]
  have bound := degree_eleven_bound S C.val C.property.gaps C.property.light
  rw [size] at bound
  exact ⟨C.property.size,by omega⟩

theorem light_lineGraph (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) :
    Nonempty (lightGraph S ≃g (cliqueGraph S).lineGraph) := by
  obtain ⟨f,mem⟩ := edge_realization S h size noOne
  refine ⟨{ toEquiv := f, map_rel_iff' := ?_ }⟩
  intro x y
  change (cliqueGraph S).lineGraph.Adj (f x) (f y) ↔ y.val ∈ holes S x.val
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨diff,C,xc,yc⟩
    exact C.property.gaps x.val ((mem x C).mp xc) y.val ((mem y C).mp yc)
      (fun eq => diff (congrArg f (Subtype.ext eq)))
  · intro gap
    have ne := (mem_holes.mp gap).1.symm
    obtain ⟨C,⟨cc,xc,yc⟩,_⟩ :=
      (shared_endpoint S h size noOne x.property y.property ne).mp gap
    exact ⟨fun eq => ne (congrArg Subtype.val (f.injective eq)),⟨C,cc⟩,
      (mem x ⟨C,cc⟩).mpr xc,(mem y ⟨C,cc⟩).mpr yc⟩

end Order12.Local139

end

/- Component Erdos723.Profiles139. -/
section

/-
# Heavy deficit counts at 139 lines

Count points of each deficit in a subset. On a line the deficit sum is
even, so each line through an odd-deficit point contains another such point.
-/

namespace Order12.Profile139

structure Family where
  S : Blocks
  good : Good S
  size : S.card = 139
  noOne : ∀ p, (through S p).card ≠ 12

namespace Family

abbrev t (D : Family) := deficit D.S

def level (D : Family) (k : ℤ) : Finset Pt := Finset.univ.filter (fun p => D.t p = k)

@[simp] lemma mem_level {D : Family} {p : Pt} {k : ℤ} :
    p ∈ D.level k ↔ D.t p = k := by simp [level]

def m (D : Family) (X : Finset Pt) (k : ℤ) : ℤ := (X ∩ D.level k).card
abbrev n (D : Family) (k : ℤ) : ℤ := D.m Finset.univ k
abbrev nb (D : Family) (p : Pt) (k : ℤ) : ℤ := D.m (holes D.S p) k

@[simp] lemma n_eq (D : Family) (k : ℤ) : D.n k = (D.level k).card := by simp [n, m]

lemma nonneg (D : Family) (X : Finset Pt) (k : ℤ) : 0 ≤ D.m X k := Int.natCast_nonneg _

lemma bound (D : Family) (p : Pt) :
    D.t p = 0 ∨ D.t p = 2 ∨ D.t p = 3 ∨ D.t p = 4 ∨ D.t p = 5 ∨ D.t p = 6 := by
  obtain ⟨lo, hi⟩ := deficit139_bound D.S D.good D.size D.noOne p
  have ne := D.noOne p
  unfold t deficit at *
  omega

/-- Evaluate a sum over the six possible deficits. -/
lemma sum_by_level (D : Family) (X : Finset Pt) (f : ℤ → ℤ) :
    ∑ p ∈ X, f (D.t p) = D.m X 0 * f 0 + D.m X 2 * f 2 + D.m X 3 * f 3 +
      D.m X 4 * f 4 + D.m X 5 * f 5 + D.m X 6 * f 6 := by
  classical
  let term (k : ℤ) (p : Pt) := if D.t p = k then f k else 0
  have tot (k : ℤ) : ∑ p ∈ X, term k p = D.m X k * f k := by
    dsimp [term, m]
    rw [← Finset.sum_filter]
    have eq : X.filter (fun p => D.t p = k) = X ∩ D.level k := by ext; simp
    simp [eq]
  calc
    _ = ∑ p ∈ X, (term 0 p + term 2 p + term 3 p + term 4 p + term 5 p + term 6 p) := by
      apply Finset.sum_congr rfl
      intro p _
      rcases D.bound p with e | e | e | e | e | e <;> norm_num [term, e]
    _ = _ := by simp only [Finset.sum_add_distrib, tot]

def odds (D : Family) : Finset Pt := Finset.univ.filter (fun p => D.t p = 3 ∨ D.t p = 5)

@[simp] lemma mem_odds {D : Family} {p : Pt} : p ∈ D.odds ↔ D.t p = 3 ∨ D.t p = 5 := by
  simp [odds]

lemma odds_count (D : Family) (X : Finset Pt) :
    ((X ∩ D.odds).card : ℤ) = D.m X 3 + D.m X 5 := by
  have eq : X.filter (fun p => D.t p = 3 ∨ D.t p = 5) = X ∩ D.odds := by ext; simp
  have a := D.sum_by_level X (fun z => if z = 3 ∨ z = 5 then (1 : ℤ) else 0)
  norm_num [← Finset.sum_filter, eq] at a
  exact a

lemma global_moments (D : Family) :
    2 * D.n 2 + 3 * D.n 3 + 4 * D.n 4 + 5 * D.n 5 + 6 * D.n 6 = 234 ∧
    3 * D.n 3 + 8 * D.n 4 + 15 * D.n 5 + 24 * D.n 6 = 72 := by
  have e := deficit139_moments D.S D.good D.size
  have a := D.sum_by_level Finset.univ id
  have b := D.sum_by_level Finset.univ (fun z => z * (z - 2))
  change (∑ p, D.t p) = 234 ∧ (∑ p, D.t p * (D.t p - 2)) = 72 at e
  rw [show (∑ p, id (D.t p)) = 234 from e.1] at a
  rw [e.2] at b
  norm_num at a b
  simp only [n_eq]
  omega

lemma odd_block_even (D : Family) {b : Finset Pt} (hb : b ∈ D.S) :
    ((b ∩ D.odds).card : ℤ) % 2 = 0 := by
  have deg := sum_degree_on_block D.S D.good hb
  have defsum : ∑ p ∈ b, D.t p = 18 := by
    dsimp [t, deficit]
    rw [Finset.sum_sub_distrib, deg]
    simp [D.good.1 b hb, D.size]
  have a := D.sum_by_level b id
  change (∑ p ∈ b, D.t p) = _ at a
  rw [defsum] at a
  norm_num at a
  rw [D.odds_count]
  omega

lemma block_ge_two (D : Family) {p : Pt} (hp : p ∈ D.odds)
    {b : Finset Pt} (hb : b ∈ through D.S p) : 2 ≤ ((b ∩ D.odds).card : ℤ) := by
  have hm := mem_through.mp hb
  have card := Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hm.2, hp⟩⟩
  have even := D.odd_block_even hm.1
  omega

/-- Total excess of the odd counts on lines through an odd point. -/
lemma odd_slack (D : Family) {p : Pt} (hp : p ∈ D.odds) :
    ∑ b ∈ through D.S p, (((b ∩ D.odds).card : ℤ) - 2) =
      D.n 3 + D.n 5 - 1 - (D.nb p 3 + D.nb p 5) - (through D.S p).card := by
  classical
  let O := D.odds
  have part := holePartition D.S D.good (O.erase p) (Finset.notMem_erase p O)
  have self : p ∉ holes D.S p := fun h => (mem_holes.mp h).1 rfl
  have eqH : O.erase p ∩ holes D.S p = holes D.S p ∩ O := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_erase]
    exact ⟨fun ⟨⟨_, a⟩, b⟩ => ⟨b, a⟩, fun ⟨b, a⟩ => ⟨⟨fun e => self (e ▸ b), a⟩, b⟩⟩
  have sumErase : ∑ b ∈ through D.S p, ((b ∩ O.erase p).card : ℤ) =
      ∑ b ∈ through D.S p, (((b ∩ D.odds).card : ℤ) - 1) := by
    apply Finset.sum_congr rfl
    intro b hb
    have mem : p ∈ b ∩ O := Finset.mem_inter.mpr ⟨(mem_through.mp hb).2, hp⟩
    rw [Finset.inter_erase, Finset.card_erase_of_mem mem]
    have pos := Finset.card_pos.mpr ⟨p, mem⟩
    change (((b ∩ O).card - 1 : ℕ) : ℤ) = ((b ∩ O).card : ℤ) - 1
    rw [Nat.cast_sub (by omega : 1 ≤ (b ∩ O).card), Nat.cast_one]
  rw [eqH, Finset.card_erase_of_mem hp] at part
  have pz := congrArg (fun v : ℕ => (v : ℤ)) part
  push_cast at pz
  rw [sumErase] at pz
  have op := Finset.card_pos.mpr ⟨p, hp⟩
  have oCount : (D.odds.card : ℤ) = D.n 3 + D.n 5 := by
    have c := D.odds_count Finset.univ
    simpa only [Finset.univ_inter] using c
  have hn := D.odds_count (holes D.S p)
  dsimp [O] at pz
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at pz ⊢
  unfold nb
  omega

lemma odd_bound (D : Family) {p : Pt} (hp : p ∈ D.odds) :
    D.nb p 3 + D.nb p 5 + 14 - D.t p ≤ D.n 3 + D.n 5 := by
  have nonneg := Finset.sum_nonneg (s := through D.S p)
    (fun b hb => sub_nonneg.mpr (D.block_ge_two hp hb))
  rw [D.odd_slack hp] at nonneg
  unfold t deficit
  omega

end Family
end Order12.Profile139

namespace Order12.Profile139.Family

lemma point_of_pos (D : Family) {k : ℤ} (hk : 0 < D.n k) : ∃ p, D.t p = k := by
  rw [D.n_eq] at hk
  have pos : 0 < (D.level k).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp pos
  exact ⟨p, mem_level.mp hp⟩

lemma nb_le (D : Family) (p : Pt) (k : ℤ) : D.nb p k ≤ D.n k := by
  rw [D.n_eq]
  unfold nb m
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right :
    holes D.S p ∩ D.level k ⊆ D.level k)

lemma nb_lt_own (D : Family) (p : Pt) {k : ℤ} (hp : D.t p = k) : D.nb p k < D.n k := by
  have sub : holes D.S p ∩ D.level k ⊆ (D.level k).erase p := by
    intro x hx
    obtain ⟨hn, hk⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_erase.mpr ⟨(mem_holes.mp hn).1, hk⟩
  have hi := Finset.card_le_card sub
  have here := mem_level.mpr hp
  rw [Finset.card_erase_of_mem here] at hi
  have pos := Finset.card_pos.mpr ⟨p, here⟩
  rw [D.n_eq]
  unfold nb m
  omega

lemma hole_lower (D : Family) {p q : Pt} (hq : q ∈ holes D.S p) : 2 ≤ D.t q := by
  have no := D.noOne q
  have pos : 0 < (holes D.S q).card := Finset.card_pos.mpr ⟨p, (holes_symm D.S p q).mp hq⟩
  have covered := holes_card D.S D.good q
  unfold t deficit
  omega

lemma no_six_neighbor (D : Family) {p q : Pt} (hq : q ∈ holes D.S p)
    (hsix : D.t q = 6) : D.t p = 2 := by
  have sum := deficit_holes_sum D.S D.good q
  change (∑ x ∈ holes D.S q, (D.t x - 2)) = D.t q * _ at sum
  rw [hsix, D.size] at sum
  change _ = (6 : ℤ) * (145 - 139 - D.t q) at sum
  rw [hsix] at sum
  change (∑ x ∈ holes D.S q, (D.t x - 2)) = 0 at sum
  have nonneg := fun x (hx : x ∈ holes D.S q) => sub_nonneg.mpr (D.hole_lower hx)
  have zero := (Finset.sum_eq_zero_iff_of_nonneg nonneg).mp sum p ((holes_symm D.S p q).mp hq)
  omega

lemma nb_eq_zero (D : Family) {p : Pt} {k : ℤ} (ha : ∀ q ∈ holes D.S p, D.t q ≠ k) :
    D.nb p k = 0 := by
  have empty : holes D.S p ∩ D.level k = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨hq, hk⟩ := Finset.mem_inter.mp hq
    exact ha q hq (mem_level.mp hk)
  simp [nb, m, empty]

lemma heavy_sum (D : Family) {p : Pt} (hp : 3 ≤ D.t p) :
    D.nb p 3 + 2 * D.nb p 4 + 3 * D.nb p 5 = D.t p * (6 - D.t p) := by
  have zero : D.nb p 0 = 0 := D.nb_eq_zero (fun _ hq => by have := D.hole_lower hq; omega)
  have six : D.nb p 6 = 0 := D.nb_eq_zero
    (fun _ hq h6 => by have := D.no_six_neighbor hq h6; omega)
  have sum := deficit_holes_sum D.S D.good p
  change (∑ x ∈ holes D.S p, (D.t x - 2)) = D.t p * (145 - (D.S.card : ℤ) - D.t p) at sum
  rw [D.size] at sum
  change (∑ x ∈ holes D.S p, (D.t x - 2)) = D.t p * (6 - D.t p) at sum
  have byLev := D.sum_by_level (holes D.S p) (fun x => x - 2)
  rw [sum] at byLev
  unfold nb at *
  rw [zero, six] at byLev
  norm_num at byLev
  linarith only [byLev]

lemma sum_nb_swap (D : Family) (i j : ℤ) :
    ∑ p ∈ D.level i, D.nb p j = ∑ q ∈ D.level j, D.nb q i := by
  classical
  have count (p : Pt) (k : ℤ) :
      D.nb p k = ∑ q ∈ D.level k, (if q ∈ holes D.S p then (1 : ℤ) else 0) := by
    rw [← Finset.sum_filter]
    have filterEq : (D.level k).filter (fun q => q ∈ holes D.S p) = holes D.S p ∩ D.level k := by
      ext
      simp only [Finset.mem_filter, Finset.mem_inter, and_comm]
    rw [filterEq, Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  calc
    _ = ∑ p ∈ D.level i, ∑ q ∈ D.level j, (if q ∈ holes D.S p then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl; intro p _; exact count p j
    _ = ∑ q ∈ D.level j, ∑ p ∈ D.level i, (if q ∈ holes D.S p then (1 : ℤ) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [count]
      apply Finset.sum_congr rfl
      intro p _
      by_cases ha : q ∈ holes D.S p
      · have hb := (holes_symm D.S p q).mp ha
        simp only [ha, hb, if_true]
      · have hb := (holes_symm D.S p q).not.mp ha
        simp only [ha, hb, if_false]

/-- Gap incidences from threes to fours and fives exhaust their joint capacities. -/
lemma odd_capacity (D : Family) :
    D.n 3 * (20 - (D.n 3 + D.n 5)) ≤ 16 * D.n 4 + 10 * D.n 5 := by
  have pointwise (p : Pt) (hp : p ∈ D.level 3) :
      20 - (D.n 3 + D.n 5) ≤ 2 * (D.nb p 4 + D.nb p 5) := by
    have ht := mem_level.mp hp
    have budget := D.odd_bound (mem_odds.mpr (Or.inl ht))
    have inc := D.heavy_sum (by omega : 3 ≤ D.t p)
    rw [ht] at budget inc
    omega
  have upper (k : ℤ) (hk : 3 ≤ k) :
      ∑ q ∈ D.level k, D.nb q 3 ≤ D.n k * (k * (6-k)) := by
    calc
      _ ≤ ∑ _ ∈ D.level k, k * (6-k) := by
        apply Finset.sum_le_sum
        intro q hq
        have ht := mem_level.mp hq
        have inc := D.heavy_sum (by omega : 3 ≤ D.t q)
        have n4 := D.nonneg (holes D.S q) 4
        have n5 := D.nonneg (holes D.S q) 5
        rw [ht] at inc
        unfold nb at *
        omega
      _ = _ := by simp
  have weighted := Finset.sum_le_sum pointwise
  rw [← Finset.mul_sum, Finset.sum_add_distrib, D.sum_nb_swap 3 4, D.sum_nb_swap 3 5] at weighted
  have four := upper 4 (by decide)
  have five := upper 5 (by decide)
  norm_num at four five
  rw [Finset.sum_const, nsmul_eq_mul, ← D.n_eq] at weighted
  simp only [D.n_eq] at *
  linarith only [weighted, four, five]

end Order12.Profile139.Family
namespace Order12.Profile139.Family

private lemma no_three_fours (D : Family) (a : D.n 3 = 0) (b : D.n 4 = 3)
    (c : D.n 5 = 0) : False := by
  obtain ⟨p, hp⟩ := D.point_of_pos (by omega : 0 < D.n 4)
  have eq := D.heavy_sum (by omega : 3 ≤ D.t p)
  rw [hp] at eq
  have i := D.nb_le p 3
  have j := D.nb_lt_own p hp
  have k := D.nb_le p 5
  omega

/-- If the five is unique, each odd line through it contains exactly one of the threes. -/
private lemma no_nineteen_threes (D : Family) (a : D.n 3 = 19) (b : D.n 4 = 0)
    (c : D.n 5 = 1) : False := by
  classical
  obtain ⟨z, hz⟩ := D.point_of_pos (by omega : 0 < D.n 5)
  have zOdd := mem_odds.mpr (Or.inr hz)
  have unique {x : Pt} (hx : D.t x = 5) : x = z := by
    have n5 := c
    rw [D.n_eq] at n5
    have small : (D.level 5).card ≤ 1 := by omega
    exact Finset.card_le_one.mp small x (mem_level.mpr hx) z (mem_level.mpr hz)
  have noFours (p : Pt) : D.nb p 4 = 0 := by
    have le := D.nb_le p 4
    have nonneg : 0 ≤ D.nb p 4 := D.nonneg _ _
    omega
  have everyBlock (l : Finset Pt) (hl : l ∈ through D.S z) :
      ((l ∩ D.odds).card : ℤ) - 2 = 0 := by
    have two := D.block_ge_two zOdd hl
    obtain ⟨x, hx, ne⟩ := Finset.exists_mem_ne (show 1 < (l ∩ D.odds).card by omega) z
    obtain ⟨hxl, hxO⟩ := Finset.mem_inter.mp hx
    have hx : D.t x = 3 := (mem_odds.mp hxO).resolve_right (fun ht => ne (unique ht))
    have nb5 : D.nb x 5 = 0 := D.nb_eq_zero (by
      intro y hy hy5
      have yz := unique hy5
      subst y
      exact (mem_holes.mp hy).2 ⟨l, (mem_through.mp hl).1, hxl, (mem_through.mp hl).2⟩)
    have eq := D.heavy_sum (by omega : 3 ≤ D.t x)
    rw [hx, noFours, nb5] at eq
    have degree : ((through D.S x).card : ℤ) = 10 := by unfold t deficit at hx; omega
    have zero := D.odd_slack hxO
    rw [a, c, degree, nb5] at zero
    have nb3 : D.nb x 3 = 9 := by omega
    rw [nb3] at zero
    change (∑ l ∈ through D.S x, (((l ∩ D.odds).card : ℤ) - 2)) = 0 at zero
    have nonneg := fun m (hm : m ∈ through D.S x) => sub_nonneg.mpr (D.block_ge_two hxO hm)
    exact (Finset.sum_eq_zero_iff_of_nonneg nonneg).mp zero l (mem_through.mpr ⟨(mem_through.mp hl).1, hxl⟩)
  have atZ := D.heavy_sum (by omega : 3 ≤ D.t z)
  have nb5 : D.nb z 5 = 0 := by
    have small := D.nb_lt_own z hz
    have nonneg : 0 ≤ D.nb z 5 := D.nonneg _ _
    omega
  rw [hz, noFours, nb5] at atZ
  have degree : ((through D.S z).card : ℤ) = 8 := by unfold t deficit at hz; omega
  have slack := D.odd_slack zOdd
  rw [Finset.sum_eq_zero everyBlock, nb5] at slack
  omega

private theorem integer_profiles (a b c d : ℤ)
    (an : 0 ≤ a) (bn : 0 ≤ b) (cn : 0 ≤ c) (dn : 0 ≤ d)
    (total : 3*a + 8*b + 15*c + 24*d = 72)
    (aPos : 0 < a → 11 ≤ a+c) (cPos : 0 < c → 9 ≤ a+c)
    (cap : a * (20-(a+c)) ≤ 16*b + 10*c)
    (not3 : a=0 → b=3 → c=0 → False)
    (not19 : a=19 → b=0 → c=1 → False) :
    (a=0 ∧ b=0 ∧ c=0 ∧ d=3) ∨ (a=0 ∧ b=6 ∧ c=0 ∧ d=1) ∨
    (a=0 ∧ b=9 ∧ c=0 ∧ d=0) ∨ (a=24 ∧ b=0 ∧ c=0 ∧ d=0) := by
  have divisible : (a+c) % 4 = 0 := by omega
  have options : a+c=0 ∨ a+c=12 ∨ a+c=16 ∨ a+c=20 ∨ a+c=24 := by omega
  rcases options with e | e | e | e | e
  · have ne : b ≠ 3 := fun hb => not3 (by omega) hb (by omega)
    omega
  · rw [e] at cap
    omega
  · rw [e] at cap
    omega
  · have cost : 12*c + 8*b + 24*d = 12 := by omega
    have one : c = 1 := by omega
    exact (not19 (by omega) (by omega) one).elim
  · omega

/-- The four possible heavy deficit profiles before the 140th line is added. -/
theorem heavy_profiles (D : Family) :
    (D.n 3=0 ∧ D.n 4=0 ∧ D.n 5=0 ∧ D.n 6=3) ∨
    (D.n 3=0 ∧ D.n 4=6 ∧ D.n 5=0 ∧ D.n 6=1) ∨
    (D.n 3=0 ∧ D.n 4=9 ∧ D.n 5=0 ∧ D.n 6=0) ∨
    (D.n 3=24 ∧ D.n 4=0 ∧ D.n 5=0 ∧ D.n 6=0) := by
  apply integer_profiles (D.n 3) (D.n 4) (D.n 5) (D.n 6)
    (D.nonneg _ _) (D.nonneg _ _) (D.nonneg _ _) (D.nonneg _ _)
    D.global_moments.2 ?_ ?_ D.odd_capacity (no_three_fours D) (no_nineteen_threes D)
  · intro pos
    obtain ⟨p, hp⟩ := D.point_of_pos pos
    have z := D.odd_bound (mem_odds.mpr (Or.inl hp))
    have z3 : 0 ≤ D.nb p 3 := D.nonneg _ _
    have z5 : 0 ≤ D.nb p 5 := D.nonneg _ _
    omega
  · intro pos
    obtain ⟨p, hp⟩ := D.point_of_pos pos
    have z := D.odd_bound (mem_odds.mpr (Or.inr hp))
    have z3 : 0 ≤ D.nb p 3 := D.nonneg _ _
    have z5 : 0 ≤ D.nb p 5 := D.nonneg _ _
    omega

/-- Include the full points and the light (deficit-two) points in the four profiles. -/
theorem all_profiles (D : Family) :
    let counts := (D.n 0, D.n 2, D.n 3, D.n 4, D.n 5, D.n 6)
    counts = (46, 108, 0, 0, 0, 3) ∨ counts = (48, 102, 0, 6, 0, 1) ∨
      counts = (49, 99, 0, 9, 0, 0) ∨ counts = (52, 81, 24, 0, 0, 0) := by
  have number : D.n 0 + D.n 2 + D.n 3 + D.n 4 + D.n 5 + D.n 6 = 157 := by
    have coeff := D.sum_by_level Finset.univ (fun _ => (1 : ℤ))
    norm_num [Pt] at coeff
    simp only [n_eq]
    omega
  have incidence := D.global_moments.1
  dsimp only
  simp only [Prod.mk.injEq]
  rcases D.heavy_profiles with hs | hs | hs | hs <;>
    obtain ⟨h3, h4, h5, h6⟩ := hs <;> omega

end Order12.Profile139.Family

end

/- Component Erdos723.Local139.ThreeSixes. -/
section

/- The three deficit-six points force a twelve-regular graph on eighteen vertices. -/

namespace Order12.Local139

open Profile139

theorem light_iff_deficit_two {D : Family} {p : Pt} : Light D.S p ↔ D.t p = 2 := by
  unfold Light Profile139.Family.t deficit
  omega

/-- The geometric count of light points is the edge count used by the graph model. -/
theorem card_light_as_level (D : Family) : (Nat.card (LightPoint D.S) : ℤ) = D.n 2 := by
  let f : LightPoint D.S ≃ D.level 2 := Equiv.subtypeEquivRight fun _ =>
    light_iff_deficit_two.trans Family.mem_level.symm
  rw [Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_coe, D.n_eq]

/-- In the three-sixes profile each light point has twenty-two light neighbors
and two deficit-six neighbors among its twenty-four uncovered neighbors. -/
theorem three_sixes_neighbors (D : Family) (six : D.n 6 = 3) {p : Pt} (hp : Light D.S p) :
    (lights D.S p).card = 22 ∧ D.nb p 6 = 2 := by
  have profiles := D.all_profiles
  dsimp only at profiles
  simp only [Prod.mk.injEq] at profiles
  have n0 : D.nb p 0 = 0 := D.nb_eq_zero (fun _ hq => by have := D.hole_lower hq; omega)
  have zero (k : ℤ) (hk : D.n k = 0) : D.nb p k = 0 := by
    have := D.nb_le p k
    have : 0 ≤ D.nb p k := D.nonneg _ _
    omega
  have h3 := zero 3 (by omega)
  have h4 := zero 4 (by omega)
  have h5 := zero 5 (by omega)
  have hc := holes_card D.S D.good p
  have hn : (holes D.S p).card = 24 := by dsimp [Light] at hp; omega
  have ht := light_iff_deficit_two.mp hp
  have extra := deficit_holes_sum D.S D.good p
  change (∑ q ∈ holes D.S p, (D.t q-2)) = D.t p * (145 -(D.S.card : ℤ)-D.t p) at extra
  rw [D.size,ht] at extra
  have sums := D.sum_by_level (holes D.S p) (fun z => z-2)
  rw [extra] at sums
  have count := D.sum_by_level (holes D.S p) (fun _ => (1 : ℤ))
  unfold Family.nb at n0 h3 h4 h5 ⊢
  rw [n0,h3,h4,h5] at sums count
  norm_num [hn] at sums count
  have same : lights D.S p = holes D.S p ∩ D.level 2 := by
    ext q
    simp only [mem_lights, Finset.mem_inter, Family.mem_level]
    exact and_congr_right fun _ => light_iff_deficit_two
  rw [same]
  unfold Family.m at sums count ⊢
  omega

/-- The usual degree sum for the clique graph, expressed through the number of light points. -/
theorem clique_degree_count (D : Family) (d : ℕ)
    (regular : ∀ C : CliqueVertex D.S, Nat.card ((cliqueGraph D.S).neighborSet C) = d) :
    Nat.card (CliqueVertex D.S) * d = 2 * Nat.card (LightPoint D.S) := by
  classical
  obtain ⟨f,_⟩ := edge_realization D.S D.good D.size D.noOne
  have degrees (C : CliqueVertex D.S) : (cliqueGraph D.S).degree C = d := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact regular C
  have sum := (cliqueGraph D.S).sum_degrees_eq_twice_card_edges
  simp only [degrees, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    SimpleGraph.edgeFinset_card] at sum
  rw [Nat.card_congr f, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact sum

/-- In the graph reconstructed from the three-sixes profile, every vertex has
twelve neighbors, the graph has 108 edges, and its vertex set has size eighteen. -/
theorem three_sixes_graph (D : Family) (six : D.n 6 = 3) :
    (∀ C : CliqueVertex D.S, Nat.card ((cliqueGraph D.S).neighborSet C) = 12) ∧
    Nat.card (cliqueGraph D.S).edgeSet = 108 ∧ Nat.card (CliqueVertex D.S) = 18 := by
  have regular (C : CliqueVertex D.S) : Nat.card ((cliqueGraph D.S).neighborSet C) = 12 := by
    have c := degree_bounds D.S D.good D.size D.noOne C
    have pos : 0 < Nat.card ((cliqueGraph D.S).neighborSet C) := by omega
    obtain ⟨⟨B,adj⟩⟩ := (Nat.card_pos_iff.mp pos).1
    obtain ⟨ne,x,cx,bx⟩ := (cliqueGraph D.S).mem_neighborSet C B |>.mp adj
    let point : LightPoint D.S := ⟨x,C.property.light x cx⟩
    have eq := endpoint_degree_sum D.S D.good D.size D.noOne point C B ne cx bx
    have light := (three_sixes_neighbors D six point.property).1
    have b := degree_bounds D.S D.good D.size D.noOne B
    rw [light] at eq
    omega
  have profiles := D.all_profiles
  dsimp only at profiles
  simp only [Prod.mk.injEq] at profiles
  have light := card_light_as_level D
  have count : Nat.card (LightPoint D.S) = 108 := by omega
  have handshake := clique_degree_count D 12 regular
  obtain ⟨f,_⟩ := edge_realization D.S D.good D.size D.noOne
  exact ⟨regular,(Nat.card_congr f).symm.trans count,by omega⟩

end Order12.Local139

end

/- Component Erdos723.Local139.ProfileDegrees. -/
section

/- The gap-neighbor counts for the other three deficit profiles. -/

namespace Order12.Local139

open Profile139
open scoped Classical

private theorem light_budget (D : Family) {p : Pt} (hp : Light D.S p) :
    ((lights D.S p).card : ℤ) + D.nb p 3 + D.nb p 4 + D.nb p 5 + D.nb p 6 = 24 ∧
    D.nb p 3 + 2 * D.nb p 4 + 3 * D.nb p 5 + 4 * D.nb p 6 = 8 := by
  have n0 : D.nb p 0 = 0 := D.nb_eq_zero (fun _ hq => by have := D.hole_lower hq; omega)
  have hc := holes_card D.S D.good p
  have hn : (holes D.S p).card = 24 := by dsimp [Light] at hp; omega
  have ht := light_iff_deficit_two.mp hp
  have extra := deficit_holes_sum D.S D.good p
  change (∑ q ∈ holes D.S p, (D.t q-2)) = D.t p * (145 -(D.S.card : ℤ)-D.t p) at extra
  rw [D.size,ht] at extra
  have sums := D.sum_by_level (holes D.S p) (fun z => z-2)
  rw [extra] at sums
  have count := D.sum_by_level (holes D.S p) (fun _ => (1 : ℤ))
  unfold Family.nb at n0 ⊢
  rw [n0] at sums count
  norm_num [hn] at sums count
  have same : lights D.S p = holes D.S p ∩ D.level 2 := by
    ext q
    simp only [mem_lights, Finset.mem_inter, Family.mem_level]
    exact and_congr_right fun _ => light_iff_deficit_two
  rw [same]
  unfold Family.m at sums count ⊢
  omega

private theorem none_at (D : Family) (p : Pt) (k : ℤ) (hk : D.n k = 0) : D.nb p k = 0 := by
  have := D.nb_le p k
  have : 0 ≤ D.nb p k := D.nonneg _ _
  omega

theorem nine_fours_counts (D : Family) (profile : D.n 4 = 9) :
    Nat.card (LightPoint D.S) = 99 ∧ ∀ p : LightPoint D.S, (lights D.S p.val).card = 20 := by
  have options := D.all_profiles
  dsimp only at options
  simp only [Prod.mk.injEq] at options
  have := card_light_as_level D
  refine ⟨by omega, fun p => ?_⟩
  have b := light_budget D p.property
  have := none_at D p.val 3 (by omega)
  have := none_at D p.val 5 (by omega)
  have := none_at D p.val 6 (by omega)
  omega

theorem all_threes_counts (D : Family) (profile : D.n 3 = 24) :
    Nat.card (LightPoint D.S) = 81 ∧ ∀ p : LightPoint D.S, (lights D.S p.val).card = 16 := by
  have options := D.all_profiles
  dsimp only at options
  simp only [Prod.mk.injEq] at options
  have := card_light_as_level D
  refine ⟨by omega, fun p => ?_⟩
  have b := light_budget D p.property
  have := none_at D p.val 4 (by omega)
  have := none_at D p.val 5 (by omega)
  have := none_at D p.val 6 (by omega)
  omega

theorem mixed_counts (D : Family) (profile : D.n 6 = 1) :
    Nat.card (LightPoint D.S) = 102 ∧ ∃ z : Pt, D.t z = 6 ∧
    (Finset.univ.filter (fun p : LightPoint D.S => p.val ∈ holes D.S z)).card = 72 ∧
    ∀ p : LightPoint D.S, (lights D.S p.val).card = if p.val ∈ holes D.S z then 21 else 20 := by
  classical
  have options := D.all_profiles
  dsimp only at options
  simp only [Prod.mk.injEq] at options
  have := card_light_as_level D
  have six : (D.level 6).card = 1 := by rw [D.n_eq] at profile; omega
  obtain ⟨z,setSix⟩ := Finset.card_eq_one.mp six
  have hz : D.t z = 6 := Family.mem_level.mp (by rw [setSix]; simp)
  have rz : (through D.S z).card = 7 := by unfold Family.t deficit at hz; omega
  have sz : (holes D.S z).card = 72 := by have := holes_card D.S D.good z; omega
  refine ⟨by omega,z,hz,?_,fun p => ?_⟩
  · rw [← sz]
    apply Finset.card_bij (fun p _ => p.val)
    · exact fun _ h => (Finset.mem_filter.mp h).2
    · exact fun _ _ _ _ h => Subtype.ext h
    · intro x hx
      let p : LightPoint D.S := ⟨x,light_iff_deficit_two.mpr
        (D.no_six_neighbor ((holes_symm D.S z x).mp hx) hz)⟩
      exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩
  · have b := light_budget D p.property
    have := none_at D p.val 3 (by omega)
    have := none_at D p.val 5 (by omega)
    have h6 : D.nb p.val 6 = if p.val ∈ holes D.S z then 1 else 0 := by
      change ((holes D.S p.val ∩ D.level 6).card : ℤ) = _
      rw [setSix]
      by_cases h : p.val ∈ holes D.S z
      · rw [Finset.inter_singleton_of_mem ((holes_symm D.S z p.val).mp h),if_pos h]
        norm_num
      · rw [Finset.inter_singleton_of_notMem ((holes_symm D.S z p.val).not.mp h),if_neg h]
        norm_num
    split <;> rename_i h <;> simp [h] at h6 <;> omega

end Order12.Local139

end

/- Component Erdos723.Local139.EndpointDegrees. -/
section

/- Count the endpoints of the light edges with any prescribed vertex degree. -/

namespace Order12.Local139

open Profile139
open scoped Classical

noncomputable abbrev deg (D : Family) (v : CliqueVertex D.S) := (cliqueGraph D.S).degree v

theorem deg_eq_card (D : Family) (v : CliqueVertex D.S) : deg D v = v.val.card := by
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using
    degree_is_size D.S D.good D.size D.noOne v

theorem degree_limits (D : Family) (v : CliqueVertex D.S) : 6 ≤ deg D v ∧ deg D v ≤ 12 := by
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using
    degree_bounds D.S D.good D.size D.noOne v

theorem degree_total (D : Family) : ∑ v, deg D v = 2 * Nat.card (LightPoint D.S) := by
  classical
  obtain ⟨f,_⟩ := edge_realization D.S D.good D.size D.noOne
  rw [Nat.card_congr f,Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card]
  exact (cliqueGraph D.S).sum_degrees_eq_twice_card_edges

theorem has_adjacent (D : Family) (u : CliqueVertex D.S) : ∃ v, (cliqueGraph D.S).Adj u v := by
  obtain ⟨v,hv⟩ := Finset.card_pos.mp
    (show 0 < ((cliqueGraph D.S).neighborFinset u).card from (by have := (degree_limits D u).1; change 0 < deg D u; omega))
  exact ⟨v,((cliqueGraph D.S).mem_neighborFinset u v).mp hv⟩

theorem adjacent_sum (D : Family) {u v : CliqueVertex D.S} (h : (cliqueGraph D.S).Adj u v) :
    ∃ p : LightPoint D.S, deg D u + deg D v = (lights D.S p.val).card + 2 := by
  obtain ⟨ne,p,up,vp⟩ := h
  let e : LightPoint D.S := ⟨p,u.property.light p up⟩
  refine ⟨e,?_⟩
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using
    endpoint_degree_sum D.S D.good D.size D.noOne e u v ne up vp

/-- Each light edge has two distinct labeled ends. -/
structure DegreeEnds (D : Family) where
  a : LightPoint D.S → CliqueVertex D.S
  b : LightPoint D.S → CliqueVertex D.S
  distinct : ∀ p, a p ≠ b p
  through : ∀ p v, p.val ∈ v.val ↔ v = a p ∨ v = b p
  sum : ∀ p, deg D (a p) + deg D (b p) = (lights D.S p.val).card + 2

theorem exists_degree_ends (D : Family) : Nonempty (DegreeEnds D) := by
  have one (p : LightPoint D.S) : ∃ u v : CliqueVertex D.S, u ≠ v ∧
      (∀ w : CliqueVertex D.S, p.val ∈ w.val ↔ w=u ∨ w=v) ∧
      deg D u + deg D v = (lights D.S p.val).card+2 := by
    obtain ⟨A,B,ca,cb,ne,inter,_,whereAt⟩ := endpoints D.S D.good D.size D.noOne p.property
    let a : CliqueVertex D.S := ⟨A,ca⟩
    let b : CliqueVertex D.S := ⟨B,cb⟩
    have diff : a ≠ b := fun eq => ne (congrArg Subtype.val eq)
    have both : p.val ∈ A ∩ B := by rw [inter]; simp
    obtain ⟨ap,bp⟩ := Finset.mem_inter.mp both
    refine ⟨a,b,diff,fun w => ⟨fun on => (whereAt w.val w.property on).imp
      (fun h => Subtype.ext h) (fun h => Subtype.ext h), fun h =>
      h.elim (fun e => e ▸ ap) (fun e => e ▸ bp)⟩,?_⟩
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using
      endpoint_degree_sum D.S D.good D.size D.noOne p a b diff ap bp
  choose a b ne mem sum using one
  exact ⟨⟨a,b,ne,mem,sum⟩⟩

noncomputable def degreeLevel (D : Family) (k : ℕ) : Finset (CliqueVertex D.S) :=
  Finset.univ.filter (fun v => deg D v = k)

noncomputable def endsOfDegree {D : Family} (E : DegreeEnds D) (p : LightPoint D.S) (k : ℕ) : ℕ :=
  (if deg D (E.a p) = k then 1 else 0) + if deg D (E.b p) = k then 1 else 0

/-- Count incidences with the degree-k vertices, once by edge and once by vertex. -/
theorem sum_ends_of_degree {D : Family} (E : DegreeEnds D) (k : ℕ) :
    ∑ p, endsOfDegree E p k = k * (degreeLevel D k).card := by
  classical
  let V := degreeLevel D k
  have fiber (v : CliqueVertex D.S) : (Finset.univ.filter (fun p : LightPoint D.S => p.val ∈ v.val)).card = deg D v := by
    rw [deg_eq_card]
    apply Finset.card_bij (fun p _ => p.val)
    · exact fun p h => (Finset.mem_filter.mp h).2
    · exact fun _ _ _ _ eq => Subtype.ext eq
    · intro p hp
      exact ⟨⟨p,v.property.light p hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,rfl⟩
  have edge (p : LightPoint D.S) : endsOfDegree E p k = ∑ v ∈ V, if p.val ∈ v.val then 1 else 0 := by
    have split (v : CliqueVertex D.S) : (if p.val ∈ v.val then 1 else 0) =
        (if v = E.a p then 1 else 0) + (if v = E.b p then 1 else 0) := by
      simp only [E.through]
      by_cases a : v = E.a p
      · subst v
        simp [E.distinct p]
      · by_cases b : v = E.b p
        · subst v
          simp [(E.distinct p).symm]
        · simp [a,b]
    simp only [split,Finset.sum_add_distrib,Finset.sum_ite_eq',endsOfDegree,V,degreeLevel,Finset.mem_filter,
      Finset.mem_univ,true_and]
  calc
    _ = ∑ p : LightPoint D.S, ∑ v ∈ V, if p.val ∈ v.val then 1 else 0 := Finset.sum_congr rfl (fun p _ => edge p)
    _ = ∑ v ∈ V, ∑ p : LightPoint D.S, if p.val ∈ v.val then 1 else 0 := Finset.sum_comm
    _ = ∑ v ∈ V, deg D v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_boole]
      exact fiber v
    _ = _ := by
      rw [Finset.sum_const_nat (show ∀ v ∈ V, deg D v = k from fun _ h => (Finset.mem_filter.mp h).2),Nat.mul_comm]

end Order12.Local139

end

/- Component Erdos723.Local139.DenseDegrees. -/
section

/- Vertex counts in the uniform and mixed deficit-four profiles. -/

namespace Order12.Local139

open Profile139
open scoped Classical

theorem nine_fours_graph (D : Family) (profile : D.n 4 = 9) :
    (∀ v, deg D v = 11) ∧ Nat.card (CliqueVertex D.S) = 18 := by
  classical
  obtain ⟨lights,localCount⟩ := nine_fours_counts D profile
  obtain ⟨E⟩ := exists_degree_ends D
  have pair {u v} (uv : (cliqueGraph D.S).Adj u v) : deg D u + deg D v = 22 := by
    obtain ⟨p,eq⟩ := adjacent_sum D uv
    rw [localCount] at eq
    exact eq
  have limit (u : CliqueVertex D.S) : 10 ≤ deg D u ∧ deg D u ≤ 12 := by
    obtain ⟨v,h⟩ := has_adjacent D u
    have := pair h
    have := degree_limits D u
    have := degree_limits D v
    omega
  have tenBound : 10 * (degreeLevel D 10).card ≤ 99 := by
    have one (p : LightPoint D.S) : endsOfDegree E p 10 ≤ 1 := by
      have eq := E.sum p
      rw [localCount] at eq
      unfold endsOfDegree
      split_ifs <;> omega
    have compare := Finset.sum_le_sum (s := Finset.univ) (fun p _ => one p)
    rw [sum_ends_of_degree] at compare
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,← Nat.card_eq_fintype_card,lights] using compare
  have notTen (u : CliqueVertex D.S) : deg D u ≠ 10 := by
    intro ten
    obtain ⟨v,h⟩ := has_adjacent D u
    have ev := pair h
    have twelve : deg D v = 12 := by omega
    have sub : (cliqueGraph D.S).neighborFinset v ⊆ degreeLevel D 10 := by
      intro w hw
      have e := pair (((cliqueGraph D.S).mem_neighborFinset v w).mp hw)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    have many := Finset.card_le_card sub
    change deg D v ≤ _ at many
    omega
  have regular (u : CliqueVertex D.S) : deg D u = 11 := by
    obtain ⟨v,h⟩ := has_adjacent D u
    have := pair h
    have := limit u
    have := limit v
    have := notTen u
    have := notTen v
    omega
  have tot := clique_degree_count D 11 (fun C => by
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using regular C)
  exact ⟨regular,by omega⟩

private lemma mixed_edge_counts (a b m : ℕ) (la : 10 ≤ a) (ua : a ≤ 12)
    (lb : 10 ≤ b) (ub : b ≤ 12) (m1 : m ≤ 1) (sum : a+b = 22+m) :
    ((if a=12 then 1 else 0) + (if b=12 then 1 else 0) =
      (if a=10 then 1 else 0) + (if b=10 then 1 else 0) + m) ∧
    ((if a=10 then 1 else 0) + (if b=10 then 1 else 0) + m ≤ 1) := by
  split_ifs <;> omega

theorem mixed_graph (D : Family) (profile : D.n 6 = 1) :
    (∀ v, deg D v = 11 ∨ deg D v = 12) ∧ (degreeLevel D 11).card = 12 ∧
    (degreeLevel D 12).card = 6 ∧ Nat.card (CliqueVertex D.S) = 18 := by
  classical
  obtain ⟨lights,z,_,number,localCount⟩ := mixed_counts D profile
  obtain ⟨E⟩ := exists_degree_ends D
  let flag (p : LightPoint D.S) : ℕ := if p.val ∈ holes D.S z then 1 else 0
  have flagCount : ∑ p, flag p = 72 := by
    unfold flag
    rw [Finset.sum_boole]
    exact number
  have limit (u : CliqueVertex D.S) : 10 ≤ deg D u ∧ deg D u ≤ 12 := by
    obtain ⟨v,h⟩ := has_adjacent D u
    obtain ⟨p,eq⟩ := adjacent_sum D h
    rw [localCount] at eq
    have := degree_limits D u
    have := degree_limits D v
    split at eq <;> omega
  have b (p : LightPoint D.S) : endsOfDegree E p 12 = endsOfDegree E p 10 + flag p ∧
      endsOfDegree E p 10 + flag p ≤ 1 := by
    apply mixed_edge_counts _ _ _ (limit _).1 (limit _).2 (limit _).1 (limit _).2
    · dsimp [flag]; split <;> decide
    · have eq := E.sum p
      rw [localCount] at eq
      dsimp [flag]
      by_cases h : p.val ∈ holes D.S z <;> simp [h] at eq ⊢ <;> omega
  have balance := Finset.sum_congr (s₁ := Finset.univ) rfl (fun p _ => (b p).1)
  rw [Finset.sum_add_distrib,flagCount,sum_ends_of_degree,sum_ends_of_degree] at balance
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun p _ => (b p).2)
  rw [Finset.sum_add_distrib,flagCount,sum_ends_of_degree] at bound
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,← Nat.card_eq_fintype_card,lights] at bound
  have ten : (degreeLevel D 10).card = 0 := by omega
  have twelve : (degreeLevel D 12).card = 6 := by omega
  have every (v : CliqueVertex D.S) : deg D v = 11 ∨ deg D v = 12 := by
    have no : deg D v ≠ 10 := by
      intro h
      have pos := Finset.card_pos.mpr (show (degreeLevel D 10).Nonempty from
        ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)
      omega
    have := limit v
    omega
  have total := degree_total D
  rw [lights] at total
  have eq (v : CliqueVertex D.S) : deg D v = 11 + (if deg D v = 12 then 1 else 0) := by
    rcases every v with e | e <;> rw [e] <;> decide
  have splitSum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => eq v)
  rw [Finset.sum_add_distrib,Finset.sum_boole] at splitSum
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at splitSum
  change _ = Fintype.card (CliqueVertex D.S)*11+(degreeLevel D 12).card at splitSum
  have cardV : Fintype.card (CliqueVertex D.S) = 18 := by
    rw [total,twelve] at splitSum
    omega
  have totalLevels : (degreeLevel D 11).card + (degreeLevel D 12).card = Fintype.card (CliqueVertex D.S) := by
    let indicator (k : ℕ) (v : CliqueVertex D.S) : ℕ := if deg D v=k then 1 else 0
    have one (v : CliqueVertex D.S) : indicator 11 v + indicator 12 v = 1 := by
      rcases every v with e | e <;> simp [indicator,e]
    have count := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => one v)
    unfold indicator at count
    rw [Finset.sum_add_distrib, Finset.sum_boole,Finset.sum_boole] at count
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Nat.cast_id,degreeLevel] using count
  refine ⟨every,?_,twelve,?_⟩
  · rw [twelve,cardV] at totalLevels
    omega
  · exact Nat.card_eq_fintype_card.trans cardV

end Order12.Local139

end

/- Component Erdos723.Local139.ThreeDegrees. -/
section

/- The graph of the twenty-four deficit-three points is regular and connected. -/

namespace Order12.Local139

open Profile139
open scoped Classical

private lemma product_bound {a b : ℕ} (la : 6 ≤ a) (ua : a ≤ 12) (s : a+b=18) : 144 ≤ a*b+b*a := by
  have lb : 6 ≤ b := by omega
  have ub : b ≤ 12 := by omega
  interval_cases a <;> interval_cases b <;> omega

private lemma only_dividing {a : ℕ} (la : 6 ≤ a) (ua : a ≤ 12) (div : a ∣ 81) : a = 9 := by
  interval_cases a <;> norm_num at *

private theorem connected_on_eighteen (D : Family) (order : Nat.card (CliqueVertex D.S) = 18)
    (lo : ∀ u, 9 ≤ deg D u) : (cliqueGraph D.S).Connected := by
  classical
  let G := cliqueGraph D.S
  have n : Fintype.card (CliqueVertex D.S) = 18 := Nat.card_eq_fintype_card.symm.trans order
  let : Nonempty (CliqueVertex D.S) := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card (CliqueVertex D.S))).1
  refine ⟨?_⟩
  intro u v
  by_cases same : u = v
  · exact same ▸ SimpleGraph.Reachable.refl _
  by_cases edge : G.Adj u v
  · exact edge.reachable
  let N := fun w => G.neighborFinset w
  have off : u ∉ N u ∪ N v := by
    intro h
    rcases Finset.mem_union.mp h with e|e
    · exact G.notMem_neighborFinset_self _ e
    · exact edge (((G.mem_neighborFinset v u).mp e).symm)
  have upper := Finset.card_le_univ (insert u (N u ∪ N v))
  rw [Finset.card_insert_of_notMem off,n] at upper
  have total := Finset.card_union_add_card_inter (N u) (N v)
  have du : 9 ≤ (N u).card := lo u
  have dv : 9 ≤ (N v).card := lo v
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (show 0 < (N u ∩ N v).card by omega)
  obtain ⟨uw,vw⟩ := Finset.mem_inter.mp hw
  exact (((G.mem_neighborFinset u w).mp uw).reachable).trans (((G.mem_neighborFinset v w).mp vw).reachable.symm)

/-- All 81 light edges have endpoint degree sum eighteen. An unequal pair
would exhaust the edge budget and force each of its two degrees to divide 81. -/
theorem all_threes_graph (D : Family) (profile : D.n 3 = 24) :
    (∀ v, deg D v = 9) ∧ Nat.card (CliqueVertex D.S) = 18 ∧ (cliqueGraph D.S).Connected := by
  classical
  obtain ⟨lights,localCount⟩ := all_threes_counts D profile
  obtain ⟨E⟩ := exists_degree_ends D
  have pair {u v} (uv : (cliqueGraph D.S).Adj u v) : deg D u + deg D v = 18 := by
    obtain ⟨p,eq⟩ := adjacent_sum D uv
    rw [localCount] at eq
    exact eq
  have edgePair (p : LightPoint D.S) : deg D (E.a p) + deg D (E.b p) = 18 := by
    have eq := E.sum p
    rw [localCount] at eq
    exact eq
  have total := degree_total D
  rw [lights] at total
  let G := cliqueGraph D.S
  have regular (u : CliqueVertex D.S) : deg D u = 9 := by
    by_contra distinct
    obtain ⟨v,uv⟩ := has_adjacent D u
    let a := deg D u
    let b := deg D v
    have sum : a+b=18 := pair uv
    have ne : a ≠ b := by change deg D u + deg D v = 18 at sum; dsimp [a,b]; omega
    let A := degreeLevel D a
    let B := degreeLevel D b
    let R := Finset.univ \ (A ∪ B)
    have memA (w : CliqueVertex D.S) : w ∈ A ↔ deg D w=a := by simp [A,degreeLevel]
    have memB (w : CliqueVertex D.S) : w ∈ B ↔ deg D w=b := by simp [B,degreeLevel]
    have memR (w : CliqueVertex D.S) : w ∈ R ↔ deg D w≠a ∧ deg D w≠b := by simp [R,memA,memB]
    have subA : G.neighborFinset v ⊆ A := by
      intro w hw
      have z := pair ((G.mem_neighborFinset v w).mp hw)
      change b+deg D w=18 at z
      exact (memA w).mpr (by omega)
    have subB : G.neighborFinset u ⊆ B := by
      intro w hw
      have z := pair ((G.mem_neighborFinset u w).mp hw)
      change a+deg D w=18 at z
      exact (memB w).mpr (by omega)
    have manyA : b ≤ A.card := Finset.card_le_card subA
    have manyB : a ≤ B.card := Finset.card_le_card subB
    have disj : Disjoint A B := Finset.disjoint_left.mpr (fun w wa wb => ne (((memA w).mp wa).symm.trans ((memB w).mp wb)))
    have split := Finset.sum_sdiff (f := deg D) (Finset.subset_univ (A ∪ B))
    change (∑ w ∈ R, deg D w) + (∑ w ∈ A ∪ B, deg D w) = _ at split
    rw [Finset.sum_union disj,
      Finset.sum_const_nat (show ∀ w ∈ A, deg D w = a from fun w h => (memA w).mp h),
      Finset.sum_const_nat (show ∀ w ∈ B, deg D w = b from fun w h => (memB w).mp h),total] at split
    have ma := Nat.mul_le_mul_right a manyA
    have mb := Nat.mul_le_mul_right b manyB
    have mid : 144 ≤ a*b+b*a := product_bound (degree_limits D u).1 (degree_limits D u).2 sum
    have remaining : (∑ w ∈ R, deg D w) ≤ 18 := by omega
    have classified (w : CliqueVertex D.S) : deg D w = a ∨ deg D w = b := by
      by_contra! other
      have sub : G.neighborFinset w ⊆ R := by
        intro t ht
        have eq := pair ((G.mem_neighborFinset w t).mp ht)
        exact (memR t).mpr ⟨by omega,by omega⟩
      have big : deg D w ≤ R.card := Finset.card_le_card sub
      have low := Finset.sum_le_sum (s := R) (fun t _ => (degree_limits D t).1)
      simp only [Finset.sum_const,smul_eq_mul] at low
      have := (degree_limits D w).1
      omega
    have once (p : LightPoint D.S) : endsOfDegree E p a = 1 := by
      have eq := edgePair p
      rcases classified (E.a p) with i|i <;> rcases classified (E.b p) with j|j <;>
        unfold endsOfDegree <;> rw [i,j] <;> split_ifs <;> omega
    have hits := sum_ends_of_degree E a
    rw [Finset.sum_const_nat (fun p _ => once p),Nat.mul_one,Finset.card_univ,← Nat.card_eq_fintype_card,lights] at hits
    have div : a ∣ 81 := ⟨_,hits⟩
    have la : 6 ≤ a := (degree_limits D u).1
    have ua : a ≤ 12 := (degree_limits D u).2
    have only := only_dividing la ua div
    exact distinct only
  have tot := clique_degree_count D 9 (fun C => by
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using regular C)
  have order : Nat.card (CliqueVertex D.S) = 18 := by omega
  exact ⟨regular,order,connected_on_eighteen D order (fun v => (regular v).ge)⟩

end Order12.Local139

end

/- Component Erdos723.Local139.GramTransport. -/
section

/- Real finite-dimensional Gram representations can be aligned on a prescribed
subfamily, including when that subfamily spans a proper subspace. -/

namespace Order12.GramTransport

open scoped InnerProductSpace Matrix

/-- Two real vector families with the same Gram products can be carried to
each other by one orthogonal transformation of the ambient space. -/
theorem isometry_of_gram {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u v : I → E) (same : ∀ i j, ⟪u i, u j⟫_ℝ = ⟪v i, v j⟫_ℝ) :
    ∃ T : E ≃ₗᵢ[ℝ] E, ∀ i, T (u i) = v i := by
  classical
  let A := Finsupp.linearCombination ℝ u
  let B := Finsupp.linearCombination ℝ v
  have norms (c : I →₀ ℝ) : ‖A c‖ = ‖B c‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [← real_inner_self_eq_norm_sq, A, B, Finsupp.linearCombination_apply,
      Finsupp.sum, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, same]
  have ker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    change A c = 0 at hc
    change B c = 0
    exact norm_eq_zero.mp ((norms c).symm.trans (by rw [hc, norm_zero]))
  let f := ((LinearMap.ker A).liftQ B ker).comp A.quotKerEquivRange.symm.toLinearMap
  have image (c : I →₀ ℝ) : f (A.rangeRestrict c) = B c := by
    change (LinearMap.ker A).liftQ B ker (A.quotKerEquivRange.symm ⟨A c, _⟩) = B c
    rw [A.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range A →ₗᵢ[ℝ] E := {
    toLinearMap := f
    norm_map' := by
      intro x
      obtain ⟨c, rfl⟩ := A.surjective_rangeRestrict x
      rw [image]
      exact (norms c).symm }
  let T := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective (f := L.extend.toLinearMap) L.extend.injective)
  refine ⟨T, fun i => ?_⟩
  let c := Finsupp.single i (1 : ℝ)
  have uc : A c = u i := by simp [A, c]
  have vc : B c = v i := by simp [B, c]
  change L.extend (u i) = v i
  rw [← uc, ← vc, ← image c]
  exact L.extend_apply (A.rangeRestrict c)

abbrev column {R P : Type*} [Fintype R] (A : Matrix R P ℝ) (p : P) : EuclideanSpace ℝ R :=
  WithLp.toLp 2 (fun r => A r p)

theorem inner_columns {R P : Type*} [Fintype R] (A : Matrix R P ℝ) (p q : P) :
    ⟪column A p, column A q⟫_ℝ = (Aᵀ * A) p q := by
  simp [column, EuclideanSpace.inner_toLp_toLp, dotProduct, Matrix.mul_apply, mul_comm]

/-- A partial Gram model on indicated columns can be imposed on the entire
matrix while retaining every pairwise product. The row coordinates of both
models have the same type. -/
theorem align_columns {R P I : Type*} [Fintype R] (A : Matrix R P ℝ) (p : I → P)
    (B : Matrix R I ℝ) (same : ∀ i j, (Aᵀ * A) (p i) (p j) = (Bᵀ * B) i j) :
    ∃ W : Matrix R P ℝ, Wᵀ * W = Aᵀ * A ∧ ∀ r i, W r (p i) = B r i := by
  obtain ⟨T, maps⟩ := isometry_of_gram (fun i => column A (p i)) (column B)
    (fun i j => by simpa only [inner_columns] using same i j)
  let W : Matrix R P ℝ := Matrix.of fun r x => T (column A x) r
  have columns (x : P) : column W x = T (column A x) := rfl
  refine ⟨W, ?_, fun r i => congrArg (fun a : EuclideanSpace ℝ R => a r) (maps i)⟩
  ext x y
  rw [← inner_columns, ← inner_columns, columns, columns, T.inner_map_map]

end Order12.GramTransport

end

/- Component Erdos723.Local139.LightCoordinates. -/
section

/- In the coordinates indexed by the eighteen canonical cliques, each light
point is the sum of the unit vectors at the endpoints of its edge. -/

namespace Order12.Local139

open scoped Matrix
open Finset
open scoped Classical

def edgeCoordinates (S : Blocks) : Matrix (CliqueVertex S) (LightPoint S) ℝ :=
  Matrix.of fun C p => if p.val ∈ C.val then 1 else 0

private theorem two_cliques (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (p : LightPoint S) :
    (univ.filter fun C : CliqueVertex S => p.val ∈ C.val).card = 2 := by
  classical
  obtain ⟨C,D,c,d,ne,meet,_,classify⟩ := endpoints S h size noOne p.property
  let a : CliqueVertex S := ⟨C,c⟩
  let b : CliqueVertex S := ⟨D,d⟩
  have both : p.val ∈ C ∩ D := by rw [meet]; simp
  obtain ⟨ac,bc⟩ := mem_inter.mp both
  have eq : univ.filter (fun E : CliqueVertex S => p.val ∈ E.val) = {a,b} := by
    ext E
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact ⟨fun hit => (classify E.val E.property hit).imp
      (fun e => Subtype.ext e) (fun e => Subtype.ext e),
      fun e => e.elim (fun v => v ▸ ac) (fun v => v ▸ bc)⟩
  rw [eq, card_pair (show a ≠ b from fun e => ne (congrArg Subtype.val e))]

/-- The raw endpoint indicator vectors already have the light block of the
required Gram matrix, for every one of the four deficit profiles. -/
theorem edgeCoordinates_gram (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (p q : LightPoint S) :
    ((edgeCoordinates S)ᵀ * edgeCoordinates S) p q = Gram139.gap S p.val q.val := by
  classical
  let F := univ.filter (fun C : CliqueVertex S => p.val ∈ C.val ∧ q.val ∈ C.val)
  have count : ((edgeCoordinates S)ᵀ * edgeCoordinates S) p q = (F.card : ℝ) := by
    rw [Matrix.mul_apply]
    change (∑ C : CliqueVertex S, (if p.val ∈ C.val then (1 : ℝ) else 0) *
      (if q.val ∈ C.val then (1 : ℝ) else 0)) = _
    calc
      _ = ∑ C : CliqueVertex S, if p.val ∈ C.val ∧ q.val ∈ C.val then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro C _
        by_cases u : p.val ∈ C.val <;> by_cases v : q.val ∈ C.val <;> simp [u,v]
      _ = _ := sum_boole (fun C : CliqueVertex S => p.val ∈ C.val ∧ q.val ∈ C.val) univ
  rw [count, Gram139.gap_entry S h]
  by_cases equal : p.val = q.val
  · have same : p = q := Subtype.ext equal
    subst q
    have two : F.card = 2 := by simpa [F] using two_cliques S h size noOne p
    have light : (through S p.val).card = 11 := p.property
    have d : deficit S p.val = 2 := by unfold deficit; rw [light]; norm_num
    simp [two, d]
  rw [if_neg equal]
  by_cases uncovered : q.val ∈ holes S p.val
  · obtain ⟨C,⟨c,pc,qc⟩,unique⟩ := (shared_endpoint S h size noOne p.property q.property equal).mp uncovered
    let vertex : CliqueVertex S := ⟨C,c⟩
    have eq : F = {vertex} := by
      ext E
      simp only [F, mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun both => Subtype.ext (unique E.val ⟨E.property,both⟩),
        fun e => e ▸ ⟨pc,qc⟩⟩
    simp [eq, uncovered]
  · have empty : F = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro E he
      have both := (mem_filter.mp he).2
      exact uncovered (E.property.gaps p.val both.1 q.val both.2 equal)
    simp [empty, uncovered]

/-- Any full Gram factor can be written on the eighteen clique coordinates
with every light column equal to its endpoint vector. -/
theorem clique_coordinates (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (count : Nat.card (CliqueVertex S) = 18) :
    ∃ W : Matrix (CliqueVertex S) Pt ℝ, Wᵀ * W = Gram139.gap S ∧ W.rank = 18 ∧
      ∀ C (p : LightPoint S), W C p.val = if p.val ∈ C.val then 1 else 0 := by
  classical
  obtain ⟨V, vg, _⟩ := Gram139.gap139_factor S h size
  let e : CliqueVertex S ≃ Fin 18 := Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using count)
  let A : Matrix (CliqueVertex S) Pt ℝ := V.submatrix e id
  have ag : Aᵀ * A = Gram139.gap S := by
    change Vᵀ.submatrix id e * V.submatrix e id = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, vg]
  obtain ⟨W, wg, columns⟩ := GramTransport.align_columns A Subtype.val (edgeCoordinates S)
    (fun i j => by rw [ag, edgeCoordinates_gram S h size noOne])
  rw [ag] at wg
  have rk := Matrix.rank_transpose_mul_self W
  rw [wg, (Gram139.gap139 S h size).2] at rk
  exact ⟨W,wg,rk.symm,columns⟩

/-- Each point has squared norm equal to its deficit in these coordinates. -/
theorem coordinate_squares (S : Blocks) (h : Good S) (W : Matrix (CliqueVertex S) Pt ℝ)
    (wg : Wᵀ * W = Gram139.gap S) (x : Pt) :
    ∑ C, (W C x) ^ 2 = (deficit S x : ℝ) := by
  have eq := congrArg (fun A : Matrix Pt Pt ℝ => A x x) wg
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← sq, Gram139.gap_entry S h, if_true] using eq

/-- The sum of the two coordinates at the endpoints of a light edge is the
corresponding gap entry for every point. -/
theorem coordinate_edge_sum (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (W : Matrix (CliqueVertex S) Pt ℝ)
    (wg : Wᵀ * W = Gram139.gap S)
    (light : ∀ C (p : LightPoint S), W C p.val = if p.val ∈ C.val then 1 else 0)
    (C D : CliqueVertex S) (ne : C ≠ D) (p : LightPoint S) (pc : p.val ∈ C.val)
    (pd : p.val ∈ D.val) (x : Pt) :
    W C x + W D x = Gram139.gap S x p.val := by
  classical
  let F := univ.filter (fun E : CliqueVertex S => p.val ∈ E.val)
  have pair : {C,D} = F := by
    apply eq_of_subset_of_card_le
    · intro E he
      rcases mem_insert.mp he with rfl | he
      · exact mem_filter.mpr ⟨mem_univ _,pc⟩
      · have same : E = D := mem_singleton.mp he
        exact mem_filter.mpr ⟨mem_univ _,same ▸ pd⟩
    · rw [card_pair ne, show F.card = 2 from two_cliques S h size noOne p]
  calc
    W C x + W D x = ∑ E ∈ ({C,D} : Finset (CliqueVertex S)), W E x := by
      rw [sum_pair ne]
    _ = ∑ E : CliqueVertex S, W E x * W E p.val := by
      rw [pair]
      simp only [F, sum_filter]
      apply sum_congr rfl
      intro E _
      rw [light]
      by_cases hit : p.val ∈ E.val <;> simp [hit]
    _ = (Wᵀ * W) x p.val := by rw [Matrix.mul_apply]; rfl
    _ = Gram139.gap S x p.val := by rw [wg]

end Order12.Local139

end

/- Component Erdos723.BinaryCompletion139. -/
section

/-
# Recovering all missing lines from a binary Gram factor

Stack the supplied 18 rows under the 139 old rows. The column Gram matrix
of this square binary incidence matrix forces the identical row Gram matrix,
so its row supports give the entire projective incidence structure.
-/

namespace Order12.Gram139

open Matrix
open scoped Matrix

private lemma binary_row_gram {I : Type} [DecidableEq I] [Fintype I]
    (cardI : Fintype.card I = 157) (W : Matrix I Pt ℝ)
    (bits : ∀ i p, W i p = 0 ∨ W i p = 1)
    (gram : Wᵀ * W = design Pt) : W * Wᵀ = design I := by
  classical
  have rankW := Matrix.rank_transpose_mul_self W
  rw [gram, Matrix.rank_of_isUnit (design Pt) (design_posDef Pt).isUnit, Fintype.card_fin] at rankW
  have inj : Function.Injective Wᵀ.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have dim := LinearMap.finrank_range_add_finrank_ker Wᵀ.mulVecLin
    change Wᵀ.rank + _ = _ at dim
    rw [Matrix.rank_transpose, ← rankW, Module.finrank_pi, cardI] at dim
    omega
  have cancel {κ : Type} (X Y : Matrix I κ ℝ) (h : Wᵀ * X = Wᵀ * Y) : X = Y := by
    ext i j
    have eq : Wᵀ.mulVecLin (X.col j) = Wᵀ.mulVecLin (Y.col j) := congrArg (fun T => T.col j) h
    exact congrFun (inj eq) i
  have columns (κ : Type) : Wᵀ * ones I κ = (13 : ℝ) • ones Pt κ := by
    ext p j
    have diag : (Wᵀ * W) p p = 13 := by rw [gram]; norm_num [design, ones]
    calc
      _ = ∑ i, W i p := by simp [Matrix.mul_apply, ones]
      _ = (Wᵀ * W) p p := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        rcases bits i p with h | h <;> simp [Matrix.transpose_apply, h]
      _ = _ := by rw [diag]; simp [ones]
  have rows (κ : Type) : W * ones Pt κ = (13 : ℝ) • ones I κ := by
    apply cancel
    rw [← Matrix.mul_assoc, gram, Matrix.mul_smul, columns]
    unfold design
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, ones_mul, Fintype.card_fin]
    module
  have trans : ones Pt Pt * Wᵀ = (13 : ℝ) • ones Pt I := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, ones_transpose] using
      congrArg Matrix.transpose (rows Pt)
  apply cancel
  rw [← Matrix.mul_assoc, gram]
  unfold design
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, trans, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_one, columns]

/-- Eighteen binary rows with the prescribed Gram matrix complete all 139 old lines. -/
theorem binary_factor_full (S : Blocks) (n : S.card = 139) (V : Matrix (Fin 18) Pt ℝ)
    (binary : ∀ i p, V i p = 0 ∨ V i p = 1) (factor : Vᵀ * V = gap S) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 157 ∧ Good T := by
  classical
  let I := S ⊕ Fin 18
  let W : Matrix I Pt ℝ := Matrix.of (fun i => Sum.elim (incidence S) V i)
  have cardI : Fintype.card I = 157 := by simp [I, n]
  have bits (i : I) (p : Pt) : W i p = 0 ∨ W i p = 1 := by
    cases i with
    | inl b =>
      change (if p ∈ b.val then (1 : ℝ) else 0) = 0 ∨ (if p ∈ b.val then (1 : ℝ) else 0) = 1
      split <;> norm_num
    | inr j => exact binary j p
  have stack : Wᵀ * W = (incidence S)ᵀ * incidence S + Vᵀ * V := by
    ext p q
    change (∑ i : I, W i p * W i q) = _
    rw [Fintype.sum_sum_type]
    rfl
  have rowGram := binary_row_gram cardI W bits (by rw [stack, factor, gap]; abel)
  let L (i : I) := Finset.univ.filter (fun p => W i p = 1)
  have bitRow (i : I) (p : Pt) : W i p = if p ∈ L i then 1 else 0 := by
    rcases bits i p with h | h <;> simp [L, h]
  have dot (i j : I) : (W * Wᵀ) i j = ((L i ∩ L j).card : ℝ) := by
    rw [Matrix.mul_apply]
    calc
      _ = ∑ p : Pt, (if p ∈ L i ∩ L j then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [Matrix.transpose_apply, bitRow, Finset.mem_inter]
        by_cases hi : p ∈ L i <;> by_cases hj : p ∈ L j <;> simp [hi, hj]
      _ = _ := by rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]; simp
  have size (i : I) : (L i).card = 13 := by
    have count := dot i i
    rw [rowGram, Finset.inter_self] at count
    norm_num [design, ones] at count
    exact_mod_cast count.symm
  have meet {i j : I} (ne : i ≠ j) : (L i ∩ L j).card = 1 := by
    have count := dot i j
    rw [rowGram] at count
    norm_num [design, ones, ne] at count
    exact_mod_cast count.symm
  have inj : Function.Injective L := by
    intro i j eq
    by_contra ne
    have count := meet ne
    rw [eq, Finset.inter_self, size] at count
    omega
  let T := Finset.univ.image L
  refine ⟨T, ?_, ?_, ?_⟩
  · intro b hb
    let i : I := Sum.inl (⟨b, hb⟩ : S)
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    ext p
    change (p ∈ Finset.univ.filter (fun q => (if q ∈ b then (1 : ℝ) else 0) = 1)) ↔ p ∈ b
    by_cases hp : p ∈ b <;> simp [hp]
  · dsimp only [T]
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ, cardI]
  · constructor
    · intro b hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      exact size i
    · intro b hb c hc ne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
      have count := meet (show i ≠ j from fun he => ne (congrArg L he))
      simpa only [Finset.mem_inter] using Finset.card_eq_one_iff_existsUnique.mp count

/-- In particular a binary factor yields the next single-line extension in the reduction. -/
theorem binary_factor_next (S : Blocks) (n : S.card = 139) (V : Matrix (Fin 18) Pt ℝ)
    (binary : ∀ i p, V i p = 0 ∨ V i p = 1) (factor : Vᵀ * V = gap S) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 140 ∧ Good T := by
  classical
  obtain ⟨F, sub, size, good⟩ := binary_factor_full S n V binary factor
  obtain ⟨b, hbF, hbS⟩ := Finset.exists_mem_notMem_of_card_lt_card (show S.card < F.card by omega)
  have hin : insert b S ⊆ F := Finset.insert_subset hbF sub
  exact ⟨insert b S, Finset.subset_insert _ _, by rw [Finset.card_insert_of_notMem hbS, n],
    fun c hc => good.1 c (hin hc), fun c hc d hd => good.2 c (hin hc) d (hin hd)⟩

end Order12.Gram139

end

/- Component Erdos723.Local139.BinaryCoordinates. -/
section

/- Binary coordinates for a vector whose sums on the edges of a graph are zero or one. -/

namespace Order12.BinaryCoordinates

variable {V : Type*} {H : SimpleGraph V}

private lemma compare_via_neighbor (c : V → ℝ)
    (edges : ∀ {a b}, H.Adj a b → c a + c b = 0 ∨ c a + c b = 1)
    (common : ∀ a b, ∃ k, H.Adj a k ∧ H.Adj b k) (a b : V) :
    c a - c b = -1 ∨ c a = c b ∨ c a - c b = 1 := by
  obtain ⟨k, ha, hb⟩ := common a b
  rcases edges ha with ha | ha <;> rcases edges hb with hb | hb <;>
    first | (left; linarith) | (right; left; linarith) | (right; right; linarith)

/-- On eighteen vertices with a common neighbor for each pair, a real vector of
integral squared norm whose edge sums attain both zero and one is binary. -/
theorem dense_binary [Fintype V] (card : Fintype.card V = 18) (c : V → ℝ)
    (common : ∀ a b, ∃ k, H.Adj a k ∧ H.Adj b k)
    (edges : ∀ {a b}, H.Adj a b → c a + c b = 0 ∨ c a + c b = 1)
    (zero : ∃ a b, H.Adj a b ∧ c a + c b = 0)
    (one : ∃ a b, H.Adj a b ∧ c a + c b = 1)
    (norm : ∃ n : ℤ, ∑ x, (c x)^2 = (n : ℝ)) :
    ∀ x, c x = 0 ∨ c x = 1 := by
  obtain ⟨a,b,_,hab⟩ := zero
  obtain ⟨s,t,_,hst⟩ := one
  have step := compare_via_neighbor c edges common
  by_cases hz : c a = 0
  · have vals (x : V) : c x = -1 ∨ c x = 0 ∨ c x = 1 := by
      simpa [hz] using step x a
    have existsOne : c s = 1 ∨ c t = 1 := by
      rcases vals s with h | h | h <;> rcases vals t with k | k | k <;>
        first | (left; linarith) | (right; linarith)
    obtain ⟨u, hu⟩ : ∃ u, c u = 1 := existsOne.elim (fun h => ⟨s,h⟩) (fun h => ⟨t,h⟩)
    intro x
    rcases vals x with hx | hx | hx
    · rcases step x u with h | h | h <;> linarith
    · exact Or.inl hx
    · exact Or.inr hx
  · have signs : c a = 1/2 ∨ c a = -(1/2) := by
      rcases step a b with h | h | h <;>
        first | (left; linarith) | (right; linarith) | (exfalso; apply hz; linarith)
    have square (x : V) : (c x)^2 = 1/4 := by
      have hx : c x = 1/2 ∨ c x = -(1/2) := by
        rcases signs with h | h <;> rcases step x a with i | i | i <;>
          rcases step x b with j | j | j <;>
          first | (left; linarith) | (right; linarith)
      rcases hx with h | h <;> rw [h] <;> norm_num
    obtain ⟨n,hn⟩ := norm
    simp_rw [square] at hn
    simp [card] at hn
    exfalso
    have impossible : 18 = 4 * n := by exact_mod_cast (show (18:ℝ) = 4*(n:ℝ) by linarith)
    omega

private lemma constant_edge_sums (c : V → ℝ) (k : ℝ)
    (common : ∀ a b, ∃ u, H.Adj a u ∧ H.Adj b u)
    (rows : ∀ {a b}, H.Adj a b → c a + c b = k) :
    ∀ a, 2*c a = k := by
  have same (a b : V) : c a = c b := by
    obtain ⟨u,ha,hb⟩ := common a b
    linarith [rows ha, rows hb]
  intro a
  obtain ⟨u,ha,_⟩ := common a a
  linarith [rows ha,same a u]

/-- The existence of edges realizing both sums need not be supplied. The
all-zero case is already binary, and a constant sum one has nonintegral norm. -/
theorem common_neighbor_binary [Fintype V] (card : Fintype.card V = 18) (c : V → ℝ)
    (common : ∀ a b, ∃ k, H.Adj a k ∧ H.Adj b k)
    (edges : ∀ {a b}, H.Adj a b → c a + c b = 0 ∨ c a + c b = 1)
    (norm : ∃ n : ℤ, ∑ x, (c x)^2 = (n : ℝ)) :
    ∀ x, c x = 0 ∨ c x = 1 := by
  by_cases z : ∃ a b, H.Adj a b ∧ c a + c b = 0
  · by_cases o : ∃ a b, H.Adj a b ∧ c a + c b = 1
    · exact dense_binary card c common edges z o norm
    · have ez {a b : V} (h : H.Adj a b) : c a + c b = 0 :=
        (edges h).resolve_right (fun e => o ⟨a,b,h,e⟩)
      intro x
      exact Or.inl (by linarith [constant_edge_sums c 0 common ez x])
  · have eo {a b : V} (h : H.Adj a b) : c a + c b = 1 :=
      (edges h).resolve_left (fun e => z ⟨a,b,h,e⟩)
    have half (v : V) : c v = 1/2 := by linarith [constant_edge_sums c 1 common eo v]
    obtain ⟨n,hn⟩ := norm
    simp_rw [half] at hn
    simp [card] at hn
    exfalso
    have impossible : 18 = 4 * n := by exact_mod_cast (show (18:ℝ) = 4*(n:ℝ) by linarith)
    omega

/-- A degree lower bound of ten on eighteen vertices gives the shared-neighbor
hypothesis, so it suffices for both the degree-eleven and mixed-degree profiles. -/
theorem high_degree_binary [Fintype V] [DecidableRel H.Adj] (card : Fintype.card V = 18)
    (degree : ∀ v, 10 ≤ H.degree v) (c : V → ℝ)
    (edges : ∀ {a b}, H.Adj a b → c a + c b = 0 ∨ c a + c b = 1)
    (norm : ∃ n : ℤ, ∑ x, (c x)^2 = (n : ℝ)) :
    ∀ x, c x = 0 ∨ c x = 1 := by
  classical
  apply common_neighbor_binary card c _ edges norm
  intro a b
  have bound := Finset.card_le_univ (H.neighborFinset a ∪ H.neighborFinset b)
  have count := Finset.card_union_add_card_inter (H.neighborFinset a) (H.neighborFinset b)
  rw [card] at bound
  have ha := degree a
  have hb := degree b
  rw [← H.card_neighborFinset_eq_degree a] at ha
  rw [← H.card_neighborFinset_eq_degree b] at hb
  obtain ⟨v,hv⟩ := Finset.card_pos.mp
    (show 0 < (H.neighborFinset a ∩ H.neighborFinset b).card by omega)
  obtain ⟨va,vb⟩ := Finset.mem_inter.mp hv
  exact ⟨v,(H.mem_neighborFinset a v).mp va,(H.mem_neighborFinset b v).mp vb⟩

private def Integral (x : ℝ) : Prop := ∃ k : ℤ, x = (k : ℝ)

private lemma integral_along (f : V → ℝ)
    (edges : ∀ {a b}, H.Adj a b → Integral (f a + f b)) {a b : V}
    (w : H.Walk a b) (last : Integral (f b)) : Integral (f a) := by
  induction w with
  | nil => exact last
  | cons e w ih =>
    obtain ⟨k,hk⟩ := edges e
    obtain ⟨m,hm⟩ := ih last
    exact ⟨k-m,by push_cast; linarith⟩

private lemma alternating_walk (f : V → ℝ)
    (edges : ∀ {a b}, H.Adj a b → Integral (f a + f b))
    {a b : V} (w : H.Walk a b) :
    Integral (f a - (-1 : ℝ)^w.length * f b) := by
  induction w with
  | nil => exact ⟨0,by simp⟩
  | cons e w ih =>
    obtain ⟨k,hk⟩ := edges e
    obtain ⟨m,hm⟩ := ih
    refine ⟨k-m,?_⟩
    rw [SimpleGraph.Walk.length_cons, pow_succ]
    push_cast
    linarith

/-- On a connected non-bipartite graph an integral edge sum makes twice each
vertex value integral. -/
private theorem doubled_integral (f : V → ℝ) (connected : H.Connected)
    (nonbip : ¬ H.Colorable 2) (edges : ∀ {a b}, H.Adj a b → Integral (f a + f b)) :
    ∀ x, Integral (2 * f x) := by
  have loop : ∃ a, ∃ w : H.Walk a a, ¬ Even w.length := by
    by_contra! h
    exact nonbip (SimpleGraph.two_colorable_iff_forall_loop_even.mpr h)
  obtain ⟨a,w,hw⟩ := loop
  obtain ⟨k,hk⟩ := alternating_walk f edges w
  rw [(Nat.not_even_iff_odd.mp hw).neg_one_pow] at hk
  have root : Integral (2*f a) := ⟨k, by linarith⟩
  have evenEdge {u v : V} (h : H.Adj u v) : Integral (2*f u + 2*f v) := by
    obtain ⟨i,hi⟩ := edges h
    exact ⟨2*i,by push_cast; linarith⟩
  exact fun x => integral_along (fun v => 2*f v) evenEdge (connected x a).some root

private lemma integral_of_norm_three [Fintype V] (card : Fintype.card V = 18) (c : V → ℝ)
    (connected : H.Connected) (nonbip : ¬ H.Colorable 2)
    (edges : ∀ {a b}, H.Adj a b → c a + c b = 0 ∨ c a + c b = 1)
    (norm : ∑ x, (c x)^2 = 3) : ∀ x, Integral (c x) := by
  classical
  have whole {u v : V} (h : H.Adj u v) : Integral (c u + c v) := by
    rcases edges h with h | h
    · exact ⟨0,by simpa using h⟩
    · exact ⟨1,by simpa using h⟩
  have small : ∃ p, (c p)^2 < 1/4 := by
    by_contra! h
    have total := Finset.sum_le_sum (s := Finset.univ) (fun x (_ : x ∈ Finset.univ) => h x)
    simp [card,norm] at total
    norm_num at total
  obtain ⟨p,hp⟩ := small
  obtain ⟨k,hk⟩ := doubled_integral c connected nonbip whole p
  have hkl : (-1:ℝ) < (k:ℝ) := by nlinarith [sq_nonneg (c p + 1/2)]
  have hku : (k:ℝ) < 1 := by nlinarith [sq_nonneg (c p - 1/2)]
  have kl : (-1:ℤ) < k := by exact_mod_cast hkl
  have ku : k < 1 := by exact_mod_cast hku
  have kz : k = 0 := by omega
  have ip : Integral (c p) := ⟨0,by simpa [kz] using hk⟩
  exact fun x => integral_along c whole (connected x p).some ip

/-- Norm three and coordinate sum three force binary coordinates on eighteen vertices
of a connected non-bipartite graph with binary edge sums. -/
theorem norm_three_binary [Fintype V] (card : Fintype.card V = 18) (c : V → ℝ)
    (connected : H.Connected) (nonbip : ¬ H.Colorable 2)
    (edges : ∀ {a b}, H.Adj a b → c a + c b = 0 ∨ c a + c b = 1)
    (norm : ∑ x, (c x)^2 = 3) (sum : ∑ x, c x = 3) :
    ∀ x, c x = 0 ∨ c x = 1 := by
  classical
  have ints := integral_of_norm_three card c connected nonbip edges norm
  have pos (x : V) : 0 ≤ (c x)^2-c x := by
    obtain ⟨m,hm⟩ := ints x
    by_cases nonpos : m ≤ 0
    · have a : (m:ℝ) ≤ 0 := by exact_mod_cast nonpos
      nlinarith [sq_nonneg (c x)]
    · have a : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
      have b := mul_nonneg (show 0 ≤ c x by linarith) (show 0 ≤ c x - 1 by linarith)
      linarith
  intro x
  have s : ∑ x, ((c x)^2-c x) = 0 := by rw [Finset.sum_sub_distrib,norm,sum]; norm_num
  have term := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => pos y)).mp s x (Finset.mem_univ _)
  rcases mul_eq_zero.mp (show c x*(c x-1)=0 by nlinarith) with e | e
  · exact Or.inl e
  · exact Or.inr (by linarith)

/-- With a minimum degree of three, no supplied coordinate-sum identity is needed.
If an integral coordinate is negative, its three neighbors must all be positive,
and the four squared coordinates already exceed the available norm. -/
theorem norm_three_of_degree [Fintype V] [DecidableRel H.Adj] (card : Fintype.card V = 18)
    (degree : ∀ v, 3 ≤ H.degree v) (c : V → ℝ) (connected : H.Connected)
    (nonbip : ¬ H.Colorable 2)
    (edges : ∀ {a b}, H.Adj a b → c a + c b = 0 ∨ c a + c b = 1)
    (norm : ∑ x, (c x)^2 = 3) : ∀ x, c x = 0 ∨ c x = 1 := by
  classical
  have ints := integral_of_norm_three card c connected nonbip edges norm
  have vals (x : V) : c x = -1 ∨ c x = 0 ∨ c x = 1 := by
    have bound : (c x)^2 ≤ 3 := norm ▸
      (Finset.single_le_sum (fun y (_ : y ∈ Finset.univ) => sq_nonneg (c y)) (Finset.mem_univ x))
    have absBound := abs_lt_of_sq_lt_sq' (a := c x) (b := (2:ℝ)) (by linarith) (by norm_num)
    obtain ⟨m,hm⟩ := ints x
    rw [hm] at absBound
    have low : -(2:ℤ) < m := by exact_mod_cast absBound.1
    have high : m < 2 := by exact_mod_cast absBound.2
    interval_cases m <;> norm_num at hm <;> simp [hm]
  intro x
  rcases vals x with neg | h | h
  · exfalso
    have around (u : V) (hu : u ∈ insert x (H.neighborFinset x)) : (c u)^2 = 1 := by
      rcases Finset.mem_insert.mp hu with rfl | hmem
      · norm_num [neg]
      · have e := edges ((H.mem_neighborFinset x u).mp hmem)
        have hu : c u = 1 := by
          rcases vals u with v | v | v <;> rcases e with e | e <;> linarith
        norm_num [hu]
    have cap := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u => (c u)^2)
      (Finset.subset_univ (insert x (H.neighborFinset x))) (fun i _ _ => sq_nonneg _)
    rw [norm] at cap
    have setCard : (insert x (H.neighborFinset x)).card = H.degree x + 1 := by simp
    have count : ∑ u ∈ insert x (H.neighborFinset x), (c u)^2 =
        ((H.degree x : ℝ) + 1) := by
      rw [Finset.sum_congr rfl around]
      simp [setCard]
    rw [count] at cap
    have d : (3:ℝ) ≤ H.degree x := by exact_mod_cast degree x
    linarith
  · exact Or.inl h
  · exact Or.inr h

end Order12.BinaryCoordinates

end

/- Component Erdos723.Local139.CoordinateExtension. -/
section

/- Completion of actual 139-line families from bounds on their clique graph. -/

namespace Order12.Local139

open scoped Matrix
open scoped Classical

private theorem complete_from_columns (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (count : Nat.card (CliqueVertex S) = 18)
    (binaryCheck : ∀ x, ¬ Light S x → ∀ c : CliqueVertex S → ℝ,
      (∀ {C D}, (cliqueGraph S).Adj C D → c C + c D = 0 ∨ c C + c D = 1) →
      (∑ C, (c C)^2) = (deficit S x : ℝ) → ∀ C, c C = 0 ∨ c C = 1) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 157 ∧ Good T := by
  classical
  obtain ⟨W, wg, _, columns⟩ := clique_coordinates S h size noOne count
  have bits (C : CliqueVertex S) (x : Pt) : W C x = 0 ∨ W C x = 1 := by
    by_cases lx : Light S x
    · have e : W C x = if x ∈ C.val then 1 else 0 := columns C ⟨x,lx⟩
      rw [e]
      split <;> simp
    apply binaryCheck x lx (fun E => W E x) _ (coordinate_squares S h W wg x) C
    intro A B adj
    obtain ⟨ne,p,ap,bp⟩ := adj
    have lp := A.property.light p ap
    have diff : x ≠ p := fun e => lx (e ▸ lp)
    have es := coordinate_edge_sum S h size noOne W wg columns A B ne ⟨p,lp⟩ ap bp x
    rw [Gram139.gap_entry S h, if_neg diff] at es
    by_cases yes : p ∈ holes S x
    · exact Or.inr (by simpa only [if_pos yes] using es)
    · exact Or.inl (by simpa only [if_neg yes] using es)
  let e : Fin 18 ≃ CliqueVertex S := Fintype.equivOfCardEq (by
    simpa [Nat.card_eq_fintype_card] using count.symm)
  let V : Matrix (Fin 18) Pt ℝ := W.submatrix e id
  apply Gram139.binary_factor_full S size V (fun i x => bits (e i) x)
  change Wᵀ.submatrix id e * W.submatrix e id = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, wg]

/-- Eighteen clique vertices and minimum degree ten imply completion to all
157 lines. This includes both dense profiles once their degrees are known. -/
theorem dense_clique_completion (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (count : Nat.card (CliqueVertex S) = 18)
    (degree : ∀ C : CliqueVertex S, 10 ≤ Nat.card ((cliqueGraph S).neighborSet C)) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 157 ∧ Good T := by
  classical
  apply complete_from_columns S h size noOne count
  intro x _ c edges norm
  apply BinaryCoordinates.high_degree_binary (H := cliqueGraph S) _ _ c edges ⟨deficit S x,norm⟩
  · simpa only [Nat.card_eq_fintype_card] using count
  · intro v
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using degree v

/-- For deficits zero, two and three, a connected nonbipartite clique graph
on eighteen vertices likewise completes the family. -/
theorem deficit_three_nonbipartite_completion (S : Blocks) (h : Good S) (size : S.card = 139)
    (noOne : ∀ x, (through S x).card ≠ 12) (count : Nat.card (CliqueVertex S) = 18)
    (values : ∀ x, ¬ Light S x → deficit S x = 0 ∨ deficit S x = 3)
    (connected : (cliqueGraph S).Connected) (nonbip : ¬ (cliqueGraph S).Colorable 2) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 157 ∧ Good T := by
  classical
  apply complete_from_columns S h size noOne count
  intro x notLight c edges norm
  rcases values x notLight with full | heavy
  · rw [full, Int.cast_zero] at norm
    intro C
    have z := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (c i))).mp
      norm C (Finset.mem_univ C)
    exact Or.inl (by nlinarith [sq_nonneg (c C)])
  · refine BinaryCoordinates.norm_three_of_degree (H := cliqueGraph S) ?_ ?_ c connected nonbip edges ?_
    · simpa only [Nat.card_eq_fintype_card] using count
    · intro C
      have low := (degree_bounds S h size noOne C).1
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at low
      omega
    · simpa only [heavy, Int.cast_ofNat] using norm

end Order12.Local139

end

/- Component Erdos723.Local139.ProfileCompletion. -/
section

/- Full completions in every dense profile and in the nonbipartite degree-nine case. -/

namespace Order12.Local139

open Profile139
open scoped Classical

/-- If any deficit is four or six, the old lines extend to a full incidence plane. -/
theorem dense_profiles_full (D : Family) (dense : D.n 3 ≠ 24) :
    ∃ T : Blocks, D.S ⊆ T ∧ T.card = 157 ∧ Good T := by
  have run (size : Nat.card (CliqueVertex D.S) = 18) (degree : ∀ v, 10 ≤ deg D v) :=
    dense_clique_completion D.S D.good D.size D.noOne size (fun C => by
      simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using degree C)
  rcases D.heavy_profiles with h|h|h|h
  · obtain ⟨reg,_,n⟩ := three_sixes_graph D h.2.2.2
    apply run n
    intro v
    have s := reg v
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] at s
    change deg D v = 12 at s
    omega
  · obtain ⟨reg,_,_,n⟩ := mixed_graph D h.2.2.2
    exact run n (fun v => by have := reg v; omega)
  · obtain ⟨reg,n⟩ := nine_fours_graph D h.2.1
    exact run n (fun v => by have := reg v; omega)
  · exact (dense h.1).elim

theorem nonbipartite_threes_full (D : Family) (profile : D.n 3 = 24)
    (nonbip : ¬ (cliqueGraph D.S).Colorable 2) :
    ∃ T : Blocks, D.S ⊆ T ∧ T.card = 157 ∧ Good T := by
  obtain ⟨_,order,conn⟩ := all_threes_graph D profile
  apply deficit_three_nonbipartite_completion D.S D.good D.size D.noOne order _ conn nonbip
  have options := D.all_profiles
  dsimp only at options
  simp only [Prod.mk.injEq] at options
  have noLevel (x : Pt) (k : ℤ) (z : D.n k = 0) : D.t x ≠ k := by
    intro h
    have pos := Finset.card_pos.mpr (show (D.level k).Nonempty from ⟨x,Family.mem_level.mpr h⟩)
    rw [D.n_eq] at z
    omega
  intro x hx
  have notTwo := light_iff_deficit_two.not.mp hx
  have bound := D.bound x
  have := noLevel x 4 (by omega)
  have := noLevel x 5 (by omega)
  have := noLevel x 6 (by omega)
  change D.t x = 0 ∨ D.t x = 3
  omega

/-- Any remaining 139-line family falls into the bipartite, nine-regular case. -/
theorem full_or_bipartite_threes (D : Family) :
    (∃ T : Blocks, D.S ⊆ T ∧ T.card = 157 ∧ Good T) ∨
    (D.n 3 = 24 ∧ (cliqueGraph D.S).Colorable 2 ∧ Nat.card (CliqueVertex D.S) = 18 ∧
      (∀ v, deg D v = 9) ∧ (cliqueGraph D.S).Connected) := by
  by_cases h : D.n 3 = 24
  · by_cases b : (cliqueGraph D.S).Colorable 2
    · obtain ⟨reg,n,conn⟩ := all_threes_graph D h
      exact Or.inr ⟨h,b,n,reg,conn⟩
    · exact Or.inl (nonbipartite_threes_full D h b)
  · exact Or.inl (dense_profiles_full D h)

end Order12.Local139

end

/- Component Erdos723.PriorWork.Extensions140. -/
section

/-
MIT License

Copyright (c) 2026 Left to Solve research repository contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/


/-
# Extending intersecting 13-point block families of sizes 140, 141 and 142

Original Lean proofs by @seanm27lol and collaborators, with Codex assistance,
for the three one-line extensions in reduction R1.H1.R1 of Erdős 723, order
12. The 143-line parent seed is due to @ian139 (upstream PR #3312).
The smaller seed's existence remains open.

The counting arguments for all three sizes were recorded in
seanm27lol/left-to-solve-research at commit
79d441ee30269027e2b9d52023925b9d32a88432, notes/erdos-723-extension.md.
The initial 142-line formalization was published at
ad3eedbbb3b968621f9a1d4743e07566ddf851ff.
Mathlib's Andrásfai–Erdős–Sós theorem supplies the bipartition in the local
22-vertex graph. All incidence and extension steps are proved below.

At 140 and 142 lines a point of degree 12 provides a new line. At 141 lines
without such a point, the degrees are 9, 11 and 13 with multiplicities
4, 96 and 57. The adjacency graph of the 96 degree-11 points is recognized
as the line graph of a graph on 16 vertices. Marking its edges by a
degree-9 point gives a 12-clique which, together with that point, meets
all 141 old lines exactly once.
-/

namespace PlaneTwelve.Seed
open Finset

abbrev P := Fin 157
abbrev Block := Finset P
abbrev Valid (S : Finset Block) :=
  (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

def deg (S : Finset Block) (x : P) : ℕ := (S.filter (x ∈ ·)).card

private theorem countWeights (S : Finset Block) (w : P → ℤ) :
    (∑ x : P, (deg S x : ℤ) * w x) = ∑ L ∈ S, ∑ x ∈ L, w x := by
  classical
  have key (x : P) : (deg S x : ℤ) * w x = ∑ L ∈ S, if x ∈ L then w x else 0 := by
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    rfl
  simp_rw [key]
  rw [sum_comm]
  simp

private theorem meet_card {S : Finset Block} (hs : Valid S) {l m : Block}
    (hl : l ∈ S) (hm : m ∈ S) (hne : l ≠ m) : (l ∩ m).card = 1 := by
  obtain ⟨x,hx,uniq⟩ := hs.2 l hl m hm hne
  apply card_eq_one.mpr
  exact ⟨x, by ext y; simpa using (show (y ∈ l ∧ y ∈ m) ↔ y = x from
    ⟨uniq y, fun h => h ▸ hx⟩)⟩

private theorem onLine {S : Finset Block} (hs : Valid S) {L : Block} (hl : L ∈ S) :
    (∑ x ∈ L, (deg S x : ℤ)) = S.card + 12 := by
  classical
  have key := countWeights S (fun x => if x ∈ L then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter, sum_const, nsmul_eq_mul, mul_one] at key
  rw [key, ← sum_erase_add _ _ hl]
  have aux : (∑ M ∈ S.erase L, ((M ∩ L).card : ℤ)) = (S.erase L).card := by
    apply Eq.trans (sum_congr rfl (g := fun _ : Block => (1 : ℤ)) ?_)
    · simp
    · intro M hM
      obtain ⟨ne,mem⟩ := mem_erase.mp hM
      exact_mod_cast meet_card hs mem hl ne
  rw [aux, inter_self, hs.1 _ hl]
  have := card_erase_add_one hl
  omega

/-- The complement of all pencil lines with their common point removed is a
new line whenever that point lies on exactly twelve old lines. -/
private theorem extend_at {S : Finset Block} (hs : Valid S) (p : P) (hr : deg S p = 12) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card + 1 ∧ Valid T := by
  classical
  let pencil := S.filter (p ∈ ·)
  have pencilCard : pencil.card = 12 := hr
  have disj : ∀ l ∈ pencil, ∀ m ∈ pencil, l ≠ m → Disjoint (l.erase p) (m.erase p) := by
    intro l hl m hm ne
    obtain ⟨ll,pl⟩ := mem_filter.mp hl
    obtain ⟨mm,pm⟩ := mem_filter.mp hm
    obtain ⟨_,_,un⟩ := hs.2 l ll m mm ne
    apply disjoint_left.mpr
    intro q hq hq'
    exact (mem_erase.mp hq).1 ((un q ⟨(mem_erase.mp hq).2,(mem_erase.mp hq').2⟩).trans
      (un p ⟨pl,pm⟩).symm)
  let joined := pencil.biUnion (fun a => a.erase p)
  let newLine := (univ : Finset P) \ joined
  have joinCard : joined.card = 144 := by
    change (pencil.biUnion (fun a => a.erase p)).card = _
    rw [card_biUnion (fun a ha b hb hab => disj a ha b hb hab)]
    have sizes (a : Block) (ha : a ∈ pencil) : (a.erase p).card = 12 := by
      obtain ⟨ha',hp⟩ := mem_filter.mp ha
      rw [card_erase_of_mem hp, hs.1 _ ha']
    rw [sum_congr rfl sizes, sum_const, pencilCard]; rfl
  have newCard : newLine.card = 13 := by
    change (univ \ joined).card = _
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, joinCard]
  have hits (l : Block) (hl : l ∈ S) : (newLine ∩ l).card = 1 := by
    by_cases hp : p ∈ l
    · have equ : newLine ∩ l = {p} := by
        ext x
        simp only [newLine,joined,mem_inter,mem_sdiff,mem_univ,true_and,
          mem_biUnion,mem_erase,mem_singleton]
        constructor
        · rintro ⟨nx,hx⟩
          by_contra ne
          exact nx ⟨l,mem_filter.mpr ⟨hl,hp⟩,ne,hx⟩
        · rintro rfl
          exact ⟨fun ⟨_,_,h,_⟩ => h rfl,hp⟩
      rw [equ,card_singleton]
    · have trace : joined ∩ l = pencil.biUnion (fun a => (a.erase p) ∩ l) := by
        ext x
        simp only [joined,mem_biUnion,mem_inter]
        aesop
      have counts (a : Block) (ha : a ∈ pencil) : ((a.erase p) ∩ l).card = 1 := by
        obtain ⟨ha',pa⟩ := mem_filter.mp ha
        have eq : (a.erase p) ∩ l = a ∩ l := by
          ext x
          simp only [mem_inter,mem_erase]
          aesop
        rw [eq]; exact meet_card hs ha' hl (by rintro rfl; exact hp pa)
      have cover : (joined ∩ l).card = 12 := by
        rw [trace,card_biUnion (fun a ha b hb ne =>
          (disj a ha b hb ne).mono inter_subset_left inter_subset_left),
          sum_congr rfl counts,sum_const,pencilCard]; rfl
      have rem : newLine ∩ l = l \ joined := by ext x; simp [newLine,and_comm]
      rw [rem,card_sdiff,hs.1 _ hl,cover]
  have fresh : newLine ∉ S := by
    intro h
    have eq := hits newLine h
    rw [inter_self,newCard] at eq
    contradiction
  have newMeets {a b : Block} (h : (a ∩ b).card = 1) :
      ∃! x, x ∈ a ∧ x ∈ b := by
    obtain ⟨x,hx⟩ := card_eq_one.mp h
    have key (y : P) : (y ∈ a ∧ y ∈ b) ↔ y = x := by
      rw [← mem_inter,hx,mem_singleton]
    exact ⟨x,(key x).mpr rfl,fun y hy => (key y).mp hy⟩
  refine ⟨insert newLine S,subset_insert _ _,card_insert_of_notMem fresh,?_,?_⟩
  · intro l hl
    rcases mem_insert.mp hl with rfl | h
    · exact newCard
    · exact hs.1 _ h
  · intro l hl m hm ne
    rcases mem_insert.mp hl with rfl | hl <;> rcases mem_insert.mp hm with rfl | hm
    · exact (ne rfl).elim
    · exact newMeets (hits _ hm)
    · exact newMeets (by rw [inter_comm]; exact hits _ hl)
    · exact hs.2 _ hl _ hm ne


private def pencil (S : Finset Block) (p : P) := S.filter (p ∈ ·)
private def neighbors (S : Finset Block) (p : P) := (pencil S p).biUnion (fun L => L.erase p)

private theorem pencil_disjoint {S : Finset Block} (hs : Valid S) (p : P) :
    ((pencil S p : Finset Block) : Set Block).PairwiseDisjoint (fun L => L.erase p) := by
  intro l hl m hm ne
  obtain ⟨ls,pl⟩ := mem_filter.mp hl
  obtain ⟨ms,pm⟩ := mem_filter.mp hm
  obtain ⟨_,_,uni⟩ := hs.2 _ ls _ ms ne
  refine disjoint_left.mpr ?_
  intro q hq hq'
  exact (mem_erase.mp hq).1 ((uni q ⟨(mem_erase.mp hq).2,(mem_erase.mp hq').2⟩).trans
    (uni p ⟨pl,pm⟩).symm)

private theorem neighborhood_size {S : Finset Block} (hs : Valid S) (p : P) :
    (neighbors S p).card = deg S p * 12 := by
  rw [neighbors,card_biUnion (pencil_disjoint hs p)]
  have sizes (l : Block) (hl : l ∈ pencil S p) : (l.erase p).card = 12 := by
    have h := mem_filter.mp hl
    rw [card_erase_of_mem h.2,hs.1 _ h.1]
  rw [sum_congr rfl sizes, sum_const,nsmul_eq_mul]; rfl

private theorem degree_cap {S : Finset Block} (hs : Valid S) (p : P) : deg S p ≤ 13 := by
  have h := card_le_univ (neighbors S p)
  rw [neighborhood_size hs, Fintype.card_fin] at h
  omega

private def marks (d : ℕ) : ℤ := if Even d then 1 else 0
private def score (d : ℕ) : ℤ := (13-(d:ℤ))*(11-d)
private def surplus (d : ℕ) : ℤ := score d - 3*marks d

private theorem scoreTable (r : Fin 14) (h : r.val ≠ 12) :
    0 ≤ surplus r ∧ (surplus r = 0 ∨ 8 ≤ surplus r) ∧
    (surplus r = 0 → (r.val = 10 ∨ r.val = 11 ∨ r.val = 13)) ∧
    (r.val : ℤ)*marks r ≤ 10*marks r := by
  revert r
  decide

private theorem oneEvenPerLine {S : Finset Block} (hs : Valid S) {L : Block} (hl : L ∈ S)
    (hp : Even (∑ x ∈ L, deg S x)) : 1 ≤ ∑ x ∈ L, marks (deg S x) := by
  classical
  have h := (Finset.even_sum_iff_even_card_odd _).mp hp
  by_contra! bad
  have odds : ∀ x ∈ L, Odd (deg S x) := by
    intro x hx
    by_contra! nn
    have we : marks (deg S x) = 1 := if_pos (Nat.not_odd_iff_even.mp nn)
    have bound := single_le_sum (f := fun x => marks (deg S x))
      (fun i (_ : i ∈ L) => by dsimp [marks]; split <;> decide) hx
    omega
  rw [filter_eq_self.mpr odds,hs.1 _ hl] at h
  exact (by decide : ¬ Even 13) h

private theorem deg_classes140 {S : Finset Block} (hs : Valid S) (sz : S.card = 140)
    (no : ∀ x, deg S x ≠ 12) :
    (∑ x : P, marks (deg S x)) = 17 ∧
    ∀ x, deg S x = 10 ∨ deg S x = 11 ∨ deg S x = 13 := by
  classical
  have h₁ := countWeights S (fun _ => (1:ℤ))
  have cardL (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at h₁
  rw [sum_congr rfl cardL] at h₁
  simp [sz] at h₁
  have h₂ := countWeights S (fun x => (deg S x : ℤ))
  have ld (l : Block) (hl : l ∈ S) : (∑ x ∈ l, (deg S x : ℤ)) = 152 := by
    rw [onLine hs hl, sz]; norm_num
  rw [sum_congr rfl ld] at h₂
  simp [sz] at h₂
  let o := (univ : Finset P).filter (fun x => Even (deg S x))
  have oc : (∑ x : P, marks (deg S x)) = (o.card : ℤ) := by
    simp only [marks,← sum_filter,sum_const,nsmul_eq_mul,mul_one]; rfl
  have markEquiv (l : Block) (hl : l ∈ S) : 1 ≤ ∑ x ∈ l, marks (deg S x) := by
    have p : Even (∑ x ∈ l, deg S x) := by
      have v : ∑ x ∈ l, deg S x = 152 := by exact_mod_cast ld l hl
      rw [v]; decide
    exact oneEvenPerLine hs hl p
  have tbl (x : P) : 0 ≤ surplus (deg S x) ∧
      (surplus (deg S x) = 0 ∨ 8 ≤ surplus (deg S x)) ∧
      (surplus (deg S x) = 0 → deg S x = 10 ∨ deg S x = 11 ∨ deg S x = 13) ∧
      (deg S x : ℤ)*marks (deg S x) ≤ 10*marks (deg S x) :=
    scoreTable ⟨deg S x,by have := degree_cap hs x; omega⟩ (no x)
  have need := sum_le_sum markEquiv
  rw [← countWeights] at need
  simp only [sum_const,sz,nsmul_eq_mul,mul_one,Nat.cast_ofNat] at need
  have lim := sum_le_sum (fun x (_ : x ∈ (univ : Finset P)) => (tbl x).2.2.2)
  rw [← mul_sum,oc] at lim
  have sumScore : (∑ x : P, score (deg S x)) = 51 := by
    have e (x : P) : score (deg S x) = (deg S x : ℤ)*(deg S x) - 24*deg S x+143 := by
      dsimp [score]; ring
    simp only [e,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,h₁,h₂]; rfl
  have excess : (∑ x : P, surplus (deg S x)) = 51-3*(o.card:ℤ) := by
    simp only [surplus,sum_sub_distrib,← mul_sum,sumScore,oc]
  have small (x : P) : surplus (deg S x) ≤ 51-3*(o.card:ℤ) := by
    rw [← excess]
    exact single_le_sum (fun y _ => (tbl y).1) (mem_univ x)
  have nn := (tbl (0 : P)).1
  have q := small 0
  have co : o.card = 14 ∨ o.card = 15 ∨ o.card = 16 ∨ o.card = 17 := by omega
  have parityOdd : Even ((univ : Finset P).filter fun x => Odd (deg S x)).card := by
    apply (Finset.even_sum_iff_even_card_odd _).mp
    have v : ∑ x : P, deg S x = 1820 := by exact_mod_cast h₁
    rw [v]; decide
  have parts := card_filter_add_card_filter_not (s := (univ : Finset P)) (fun x => Even (deg S x))
  simp only [Nat.not_even_iff_odd, card_univ,Fintype.card_fin] at parts
  change o.card + _ = _ at parts
  obtain ⟨k,hk⟩ := parityOdd
  have opts : o.card = 15 ∨ o.card = 17 := by omega
  have co17 : o.card = 17 := by
    rcases opts with bad | good
    · have zeros (x : P) (_ : x ∈ (univ : Finset P)) : surplus (deg S x) = 0 := by
        have c := small x
        have a := (tbl x).2.1
        omega
      rw [sum_congr rfl zeros,bad] at excess; norm_num at excess
    · exact good
  refine ⟨by rw [oc,co17]; rfl, fun x => ?_⟩
  apply (tbl x).2.2.1
  have ub := small x
  have lb := (tbl x).1
  omega


private theorem neighbors_mem {S : Finset Block} {p q : P} :
    q ∈ neighbors S p ↔ q ≠ p ∧ ∃ L ∈ S, p ∈ L ∧ q ∈ L := by
  simp only [neighbors, pencil, mem_biUnion, mem_erase, mem_filter]
  tauto

private theorem neighbor_symm {S : Finset Block} {p q : P} :
    q ∈ neighbors S p ↔ p ∈ neighbors S q := by
  rw [neighbors_mem,neighbors_mem,ne_comm]; aesop

private theorem full_joins {S : Finset Block} (hs : Valid S) {p q : P}
    (h : deg S p = 13) (ne : q ≠ p) : q ∈ neighbors S p := by
  have eq : neighbors S p = univ.erase p := by
    apply eq_of_subset_of_card_le
    · intro x hx; exact mem_erase.mpr ⟨(neighbors_mem.mp hx).1,mem_univ _⟩
    · rw [neighborhood_size hs,h,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
  rw [eq]; exact mem_erase.mpr ⟨ne,mem_univ _⟩

private theorem pencilSum {S : Finset Block} (hs : Valid S) (p : P) (f : P → ℤ) :
    (∑ x ∈ neighbors S p, f x) + (deg S p : ℤ)*f p =
      ∑ L ∈ pencil S p, ∑ x ∈ L, f x := by
  have cst : (deg S p : ℤ)*f p = ∑ _L ∈ pencil S p, f p := by rw [sum_const,nsmul_eq_mul]; rfl
  rw [neighbors,sum_biUnion (pencil_disjoint hs p),cst,← sum_add_distrib]
  exact sum_congr rfl fun L hL => sum_erase_add L _ (mem_filter.mp hL).2

private theorem degree_twelve_140 {S : Finset Block} (hs : Valid S) (sz : S.card = 140) :
    ∃ x, deg S x = 12 := by
  classical
  by_contra! no
  obtain ⟨heavyCount,cls⟩ := deg_classes140 hs sz no
  let m (x : P) := marks (deg S x)
  let h (L : Block) := ∑ x ∈ L, m x
  have incidence (x : P) : (deg S x : ℤ)*m x = 10*m x := by
    rcases cls x with a | a | a <;> norm_num [m,a,marks,Nat.even_iff]
  have lineDegrees (L : Block) (hl : L ∈ S) : (∑ x ∈ L, (deg S x : ℤ)) = 152 := by
    rw [onLine hs hl,sz]; rfl
  have countsTotal := countWeights S (fun _ => (1:ℤ))
  have cardL (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at countsTotal
  rw [sum_congr rfl cardL] at countsTotal
  simp [sz] at countsTotal
  have lineBounds (L : Block) (hl : L ∈ S) : 1 ≤ h L ∧ h L ≤ 5 := by
    constructor
    · apply oneEvenPerLine hs hl
      have v : ∑ x ∈ L, deg S x = 152 := by exact_mod_cast lineDegrees L hl
      rw [v]; decide
    · have cost (x : P) (_ : x ∈ L) : 3*m x ≤ 13-(deg S x : ℤ) := by
        rcases cls x with a | a | a <;> norm_num [m,a,marks,Nat.even_iff]
      have t := sum_le_sum cost
      rw [← mul_sum, sum_sub_distrib, lineDegrees L hl, sum_const, hs.1 _ hl] at t
      change 3*h L ≤ _ at t
      norm_num at t; omega
  have pencilHeavy (p : P) (hp : deg S p = 10) : (∑ L ∈ pencil S p, h L) = 20 := by
    let N := neighbors S p
    let A := (univ : Finset P) \ N
    have np : N.card = 120 := by rw [show N = neighbors S p from rfl,neighborhood_size hs,hp]
    have ap : A.card = 37 := by
      rw [show A = univ \ N from rfl,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,np]
    have per (x : P) (hx : x ∈ A) : (deg S x : ℤ) + m x = 11 := by
      rcases cls x with hd | hd | hd
      · norm_num [m,hd,marks,Nat.even_iff]
      · norm_num [m,hd,marks,Nat.even_iff]
      · have xp : p ≠ x := by intro eq; subst x; omega
        exact ((mem_sdiff.mp hx).2 (neighbor_symm.mp (full_joins hs hd xp))).elim
    have sD := pencilSum hs p (fun y => (deg S y : ℤ))
    have sumD : (∑ L ∈ pencil S p, ∑ y ∈ L, (deg S y : ℤ)) = 1520 := by
      have ld (L : Block) (hL : L ∈ pencil S p) : (∑ y ∈ L, (deg S y : ℤ)) = 152 := lineDegrees L (mem_filter.mp hL).1
      rw [sum_congr rfl ld,sum_const]
      change (deg S p) • (152:ℤ) = 1520
      rw [hp]; rfl
    rw [sumD,hp] at sD
    have sepD := sum_sdiff (f := fun x => (deg S x : ℤ)) (subset_univ N)
    have sepM := sum_sdiff (f := m) (subset_univ N)
    change (∑ x ∈ A, (deg S x : ℤ)) + (∑ x ∈ N, (deg S x : ℤ)) = _ at sepD
    change (∑ x ∈ A, m x) + (∑ x ∈ N, m x) = _ at sepM
    change (∑ x ∈ N, (deg S x : ℤ)) + _ = _ at sD
    rw [countsTotal] at sepD
    have totM : (∑ x : P, m x) = 17 := heavyCount
    rw [totM] at sepM
    have mix : (∑ x ∈ A, ((deg S x : ℤ) + m x)) = 407 := by
      rw [sum_congr rfl per, sum_const, ap]; rfl
    rw [sum_add_distrib] at mix
    have hSum := pencilSum hs p m
    change (∑ x ∈ N, m x) + (deg S p : ℤ)*m p = ∑ L ∈ pencil S p, h L at hSum
    rw [hp] at hSum
    have mv : m p = 1 := by norm_num [m,marks,hp,Nat.even_iff]
    rw [mv] at hSum
    omega
  have totalLines : (∑ L ∈ S, h L) = 170 := by
    change (∑ L ∈ S, ∑ x ∈ L, m x) = _
    rw [← countWeights,sum_congr rfl (fun x _ => incidence x),← mul_sum]
    change 10*(∑ x : P, marks (deg S x)) = _
    rw [heavyCount]; rfl
  have totalSq : (∑ L ∈ S, h L * h L) = 340 := by
    have weightSq (L : Block) : h L*h L = ∑ x : P, if x ∈ L then m x*h L else 0 := by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, ← sum_mul]
    rw [sum_congr rfl (fun L _ => weightSq L),sum_comm]
    have row (p : P) (_ : p ∈ (univ : Finset P)) :
        (∑ L ∈ S, if p ∈ L then m p*h L else 0) = 20*m p := by
      rw [← sum_filter, ← mul_sum]
      change m p*(∑ L ∈ pencil S p, h L) = 20*m p
      rcases cls p with hd | hd | hd
      · rw [pencilHeavy p hd,mul_comm]
      · norm_num [m,hd,marks,Nat.even_iff]
      · norm_num [m,hd,marks,Nat.even_iff]
    rw [sum_congr rfl row,← mul_sum]
    change 20*(∑ x : P, marks (deg S x)) = _
    rw [heavyCount]; rfl
  have chord (L : Block) (hl : L ∈ S) : h L * h L ≤ 6*h L-5 := by
    have ⟨a,b⟩ := lineBounds L hl
    nlinarith [mul_nonneg (show 0 ≤ h L-1 by omega) (show 0 ≤ 5-h L by omega)]
  have con := sum_le_sum chord
  rw [sum_sub_distrib,← mul_sum,totalLines,totalSq,sum_const,sz] at con
  norm_num at con

theorem extend_140 (S : Finset Block) (sz : S.card = 140) (hs : Valid S) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card + 1 ∧ Valid T := by
  obtain ⟨p,hp⟩ := degree_twelve_140 hs sz
  exact extend_at hs p hp

private theorem score_sum141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141) :
    (∑ x : P, score (deg S x)) = 32 := by
  have h₁ := countWeights S (fun _ => (1:ℤ))
  have size (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at h₁
  rw [sum_congr rfl size] at h₁
  simp [sz] at h₁
  have h₂ := countWeights S (fun x => (deg S x : ℤ))
  have ld (l : Block) (hl : l ∈ S) : (∑ x ∈ l, (deg S x : ℤ)) = 153 := by
    rw [onLine hs hl, sz]; norm_num
  rw [sum_congr rfl ld] at h₂
  simp [sz] at h₂
  have e (x : P) : score (deg S x) = (deg S x : ℤ)*(deg S x)-24*deg S x+143 := by
    dsimp [score]; ring
  simp only [e,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,
    Fintype.card_fin,nsmul_eq_mul,h₁,h₂]; rfl

/-- With 141 lines, the absence of a degree-twelve point forces every point
degree to be odd. -/
theorem odd_degrees_141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) : ∀ x, Odd (deg S x) := by
  classical
  intro p
  by_contra! noOdd
  have pe := Nat.not_odd_iff_even.mp noOdd
  have tab : ∀ i : Fin 14, i.val ≠ 12 →
      0 ≤ score i ∧ (Even i.val → 3 ≤ score i ∧ 33 ≤ score i + 3*(i.val:ℤ)) := by decide
  have fact (x : P) : 0 ≤ score (deg S x) ∧
      (Even (deg S x) → 3 ≤ score (deg S x) ∧ 33 ≤ score (deg S x) + 3*(deg S x:ℤ)) :=
    tab ⟨deg S x,by have := degree_cap hs x; omega⟩ (no x)
  have lineNeighbor (l : Block) (hl : l ∈ pencil S p) : ∃ y ∈ l.erase p, Even (deg S y) := by
    obtain ⟨ls,pl⟩ := mem_filter.mp hl
    by_contra! failing
    have odds : ∀ y ∈ l.erase p, Odd (deg S y) := fun y hy => Nat.not_even_iff_odd.mp (failing y hy)
    have erased : Even (∑ x ∈ l.erase p, deg S x) := by
      apply (Finset.even_sum_iff_even_card_odd _).mpr
      rw [filter_eq_self.mpr odds,card_erase_of_mem pl, hs.1 _ ls]
      decide
    have v : ∑ x ∈ l, deg S x = 153 := by
      have s := onLine hs ls
      rw [sz] at s
      norm_num at s
      exact_mod_cast s
    have ev := erased.add pe
    rw [sum_erase_add _ _ pl,v] at ev
    exact (by decide : ¬Even 153) ev
  have lineBound (l : Block) (hl : l ∈ pencil S p) : (3:ℤ) ≤ ∑ x ∈ l.erase p, score (deg S x) := by
    obtain ⟨y,hy,he⟩ := lineNeighbor l hl
    have hit := ((fact y).2 he).1
    exact hit.trans (single_le_sum (fun x _ => (fact x).1) hy)
  have low := sum_le_sum lineBound
  rw [← sum_biUnion (pencil_disjoint hs p),sum_const,nsmul_eq_mul] at low
  change (deg S p:ℤ)*3 ≤ ∑ x ∈ neighbors S p, score (deg S x) at low
  have self : p ∉ neighbors S p := fun h => (neighbors_mem.mp h).1 rfl
  have addcap := sum_le_sum_of_subset_of_nonneg (f := fun x => score (deg S x))
    (subset_univ (insert p (neighbors S p))) (fun x _ _ => (fact x).1)
  rw [sum_insert self,score_sum141 hs sz] at addcap
  have strong := ((fact p).2 pe).2
  omega

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

/-- Either there is an immediate pencil completion, or the degrees of the
141-line configuration have one uniquely determined distribution. -/
theorem degree_counts_141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) :
    (∀ x, deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13) ∧
    ((univ : Finset P).filter (fun x => deg S x = 9)).card = 4 ∧
    ((univ : Finset P).filter (fun x => deg S x = 11)).card = 96 ∧
    ((univ : Finset P).filter (fun x => deg S x = 13)).card = 57 := by
  classical
  let cls (k : ℕ) := (univ : Finset P).filter (fun x => deg S x = k)
  let mark (k : ℕ) (x : P) := if deg S x = k then (1:ℤ) else 0
  have totals (k : ℕ) : (∑ x : P, mark k x) = (cls k).card := by
    simp only [mark,←sum_filter,sum_const,nsmul_eq_mul,mul_one]; rfl
  have rtable : ∀ r : Fin 14, Odd r.val →
    0 ≤ score r ∧ (score r ≤ 32 → r.val=7 ∨ r.val=9 ∨ r.val=11 ∨ r.val=13) := by decide
  have tab (x : P) : 0 ≤ score (deg S x) ∧ (score (deg S x) ≤ 32 →
      deg S x = 7 ∨ deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13) :=
    rtable ⟨deg S x,by have := degree_cap hs x; omega⟩ (odd_degrees_141 hs sz no x)
  have kinds (x : P) : deg S x = 7 ∨ deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13 := by
    apply (tab x).2
    rw [← score_sum141 hs sz]
    exact single_le_sum (fun y _ => (tab y).1) (mem_univ x)
  have sMark (x : P) (_ : x ∈ (univ : Finset P)) : score (deg S x) =
      24*mark 7 x + 8*mark 9 x := by
    rcases kinds x with h|h|h|h <;> norm_num [score,mark,h]
  have sEq := sum_congr rfl sMark
  rw [score_sum141 hs sz,sum_add_distrib,←mul_sum,←mul_sum,totals,totals] at sEq
  have defs (x : P) (_ : x ∈ (univ : Finset P)) : 13-(deg S x : ℤ) =
      6*mark 7 x + 4*mark 9 x + 2*mark 11 x := by
    rcases kinds x with h|h|h|h <;> norm_num [mark,h]
  have h₁ := countWeights S (fun _ => (1:ℤ))
  have size (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at h₁
  rw [sum_congr rfl size] at h₁
  simp [sz] at h₁
  have dEq := sum_congr rfl defs
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,totals,h₁] at dEq
  have dz : (cls 7).card = 0 := by
    by_contra! nonzero
    have k7 : (cls 7).card = 1 := by omega
    have k9 : (cls 9).card = 1 := by omega
    have k11 : (cls 11).card = 99 := by omega
    obtain ⟨z,hz⟩ := card_eq_one.mp k7
    have nz : deg S z = 7 := (mem_filter.mp (show z ∈ cls 7 by rw [hz]; simp)).2
    have lightMiss (p : P) (hp : p ∈ cls 11) : p ∈ univ \ neighbors S z := by
      have dp := (mem_filter.mp hp).2
      refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
      intro near
      let N := neighbors S p
      let A := univ \ N
      have cN : N.card = 132 := by rw [show N = neighbors S p from rfl,neighborhood_size hs,dp]
      have cA : A.card = 25 := by
        rw [show A = univ \ N from rfl,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,cN]
      have aKinds (x : P) (hx : x ∈ A) : deg S x = 9 ∨ deg S x = 11 := by
        rcases kinds x with t|t|t|t
        · have xz : x=z := by
            have mem : x ∈ cls 7 := mem_filter.mpr ⟨mem_univ _,t⟩
            rwa [hz,mem_singleton] at mem
          subst x
          exact ((mem_sdiff.mp hx).2 (neighbor_symm.mp near)).elim
        · exact Or.inl t
        · exact Or.inr t
        · have ne : p ≠ x := by intro eq; subst x; omega
          exact ((mem_sdiff.mp hx).2 (neighbor_symm.mp (full_joins hs t ne))).elim
      have per (x : P) (hx : x ∈ A) : (deg S x : ℤ) =
          11-2*mark 9 x := by rcases aKinds x hx with t|t <;> norm_num [mark,t]
      have sD := pencilSum hs p (fun y => (deg S y : ℤ))
      have singleL (L : Block) (hL : L ∈ pencil S p) :
          (∑ x ∈ L, (deg S x : ℤ)) = 153 := by
        rw [onLine hs (mem_filter.mp hL).1,sz]; norm_num
      rw [sum_congr rfl singleL, sum_const] at sD
      change (∑ x ∈ N, (deg S x:ℤ)) + (deg S p:ℤ)*(deg S p) = (deg S p) • (153:ℤ) at sD
      rw [dp] at sD
      have sep := sum_sdiff (f := fun x => (deg S x:ℤ)) (subset_univ N)
      change (∑ x ∈ A, (deg S x:ℤ)) + (∑ x ∈ N, (deg S x:ℤ)) = _ at sep
      rw [h₁] at sep
      have sumA := sum_congr rfl per
      rw [sum_sub_distrib,sum_const,cA,←mul_sum] at sumA
      have upper := sum_le_sum_of_subset_of_nonneg (f := mark 9) (subset_univ A)
        (fun x _ _ => by dsimp [mark]; split <;> decide)
      rw [totals,k9] at upper
      norm_num at upper sumA sD
      omega
    have num := card_le_card (show cls 11 ⊆ univ \ neighbors S z from lightMiss)
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,
      neighborhood_size hs,nz,k11] at num
    omega
  have eqs : (cls 9).card = 4 ∧ (cls 11).card = 96 := by omega
  have no7 (x : P) : deg S x ≠ 7 := by
    intro bad
    have hx : x ∈ cls 7 := mem_filter.mpr ⟨mem_univ _,bad⟩
    have pos := card_pos.mpr (show (cls 7).Nonempty from ⟨x,hx⟩)
    omega
  have all (x : P) (_ : x ∈ (univ : Finset P)) : (1:ℤ) = mark 9 x + mark 11 x + mark 13 x := by
    rcases (kinds x).resolve_left (no7 x) with t|t|t <;> norm_num [mark,t]
  have count := sum_congr rfl all
  simp only [sum_add_distrib,totals,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at count
  exact ⟨fun x => (kinds x).resolve_left (no7 x),eqs.1,eqs.2,
    (show (cls 13).card = 57 by omega)⟩


end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

private def gap (S : Finset Block) (p : P) := univ \ insert p (neighbors S p)

private theorem gap_mem {S : Finset Block} {p q : P} :
    q ∈ gap S p ↔ q ≠ p ∧ q ∉ neighbors S p := by simp [gap]

private theorem gap_symm {S : Finset Block} {p q : P} :
    q ∈ gap S p ↔ p ∈ gap S q := by rw [gap_mem,gap_mem,ne_comm,neighbor_symm]

private theorem self_neigh (S : Finset Block) (p : P) : p ∉ neighbors S p :=
  fun h => (neighbors_mem.mp h).1 rfl

private theorem gap_size {S : Finset Block} (hs : Valid S) (p : P) :
    (gap S p).card = 12*(13-deg S p) := by
  rw [gap,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,
    card_insert_of_notMem (self_neigh _ _),neighborhood_size hs]
  have hb := degree_cap hs p
  omega

private theorem gap_on_block {S : Finset Block} (hs : Valid S) (q : P) {L : Block} (hl : L ∈ S) :
    (L ∩ gap S q).card = if q ∈ L then 0 else 13-deg S q := by
  classical
  by_cases hq : q ∈ L
  · rw [if_pos hq]
    apply card_eq_zero.mpr
    refine eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    obtain ⟨xl,xg⟩ := mem_inter.mp hx
    have xm := gap_mem.mp xg
    exact xm.2 (neighbors_mem.mpr ⟨xm.1,L,hl,hq,xl⟩)
  · rw [if_neg hq]
    have tr : neighbors S q ∩ L = (pencil S q).biUnion (fun a => (a.erase q) ∩ L) := by
      ext x; simp only [neighbors,mem_inter,mem_biUnion]; aesop
    have ct (a : Block) (ha : a ∈ pencil S q) : ((a.erase q) ∩ L).card = 1 := by
      have ⟨as,qa⟩ := mem_filter.mp ha
      have eq : (a.erase q) ∩ L = a ∩ L := by ext x; simp only [mem_inter,mem_erase]; aesop
      rw [eq]; exact meet_card hs as hl (by rintro rfl; exact hq qa)
    have c : (neighbors S q ∩ L).card = deg S q := by
      rw [tr,card_biUnion (fun a ha b hb ne => (pencil_disjoint hs q ha hb ne).mono
        inter_subset_left inter_subset_left),sum_congr rfl ct,sum_const]; simp [deg,pencil]
    have eq : L ∩ gap S q = L \ neighbors S q := by
      ext x; simp only [gap_mem,mem_inter,mem_sdiff]; aesop
    rw [eq,card_sdiff,hs.1 _ hl,c]

private def weight (A : Finset P) (x : P) : ℤ := if x ∈ A then 1 else 0

private theorem sum_weight (W A : Finset P) :
    (∑ x ∈ W, weight A x) = (W ∩ A).card := by
  simp only [weight,←sum_filter,filter_mem_eq_inter,sum_const,nsmul_eq_mul,mul_one]

private theorem common_gaps {S : Finset Block} (hs : Valid S) {p q : P} (qp : q ≠ p) :
    ((gap S p ∩ gap S q).card : ℤ) =
      if q ∈ gap S p then (12-(deg S p:ℤ))*(13-deg S q) + deg S p - 1
      else (13-(deg S p:ℤ))*(13-deg S q) := by
  classical
  let g := gap S q
  let I := (pencil S p).filter (q ∈ ·)
  have fcard : (I.card:ℤ) = if q ∈ gap S p then 0 else 1 := by
    by_cases h : q ∈ gap S p
    · rw [if_pos h]
      have em : I = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr ?_
        intro L hL
        have ⟨ls,ql⟩ := mem_filter.mp hL
        have ⟨ls',pl⟩ := mem_filter.mp ls
        exact (gap_mem.mp h).2 (neighbors_mem.mpr ⟨qp,L,ls',pl,ql⟩)
      rw [em]; rfl
    · rw [if_neg h]
      have joined : q ∈ neighbors S p := by
        by_contra n; exact h (gap_mem.mpr ⟨qp,n⟩)
      obtain ⟨_,L,ls,pl,ql⟩ := neighbors_mem.mp joined
      have one : I.card = 1 := by
        apply card_eq_one.mpr
        refine ⟨L,?_⟩
        ext M
        simp only [I,pencil,mem_filter,mem_singleton]
        constructor
        · rintro ⟨⟨ms,pm⟩,qm⟩
          by_contra ne
          obtain ⟨_,_,uniq⟩ := hs.2 M ms L ls ne
          exact qp ((uniq q ⟨qm,ql⟩).trans (uniq p ⟨pm,pl⟩).symm)
        · rintro rfl; exact ⟨⟨ls,pl⟩,ql⟩
      exact_mod_cast one
  have partition := sum_sdiff (f := weight g) (subset_univ (insert p (neighbors S p)))
  change (∑ x ∈ gap S p, weight g x) + _ = _ at partition
  rw [sum_insert (self_neigh _ _),sum_weight,sum_weight,sum_weight,univ_inter] at partition
  have pc := pencilSum hs p (weight g)
  rw [sum_weight] at pc
  have kg : (13-deg S q:ℕ) = 13-(deg S q : ℤ) := by
    rw [Nat.cast_sub (degree_cap hs q)]; rfl
  have geom (L : Block) (hl : L ∈ pencil S p) :
      (∑ x ∈ L, weight g x) =
      (if q ∈ L then (0:ℤ) else 13-deg S q) := by
    rw [sum_weight]
    change ((L ∩ gap S q).card:ℤ) = _
    rw [gap_on_block hs q (mem_filter.mp hl).1]
    split <;> simp [*]
  rw [sum_congr rfl geom,sum_ite, sum_const_zero,zero_add,sum_const,nsmul_eq_mul] at pc
  let other := (pencil S p).filter (fun L => q ∉ L)
  have two := card_filter_add_card_filter_not (s := pencil S p) (fun L => q ∈ L)
  change I.card + other.card = deg S p at two
  have ocast : (other.card:ℤ) = (deg S p:ℤ) - I.card := by omega
  change _ = (other.card:ℤ) * (13 - (deg S q:ℤ)) at pc
  rw [ocast,fcard] at pc
  have ord : (g.card:ℤ) = 12*(13-(deg S q:ℤ)) := by
    change ((gap S q).card:ℤ) = _
    rw [gap_size hs,Nat.cast_mul,kg]; rfl
  rw [ord] at partition
  have ww : weight g p = if q ∈ gap S p then 1 else 0 := by simp [weight,g,gap_symm (p:=q) (q:=p)]
  rw [ww] at pc partition
  change ((gap S p ∩ g).card:ℤ) = _
  split <;> rename_i h
  · simp only [if_pos h] at pc partition
    nlinarith only [pc,partition]
  · simp only [if_neg h] at pc partition
    nlinarith only [pc,partition]

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

private def light (S : Finset Block) : Finset P := univ.filter (fun x => deg S x = 11)
private def heavy (S : Finset Block) : Finset P := univ.filter (fun x => deg S x = 9)

private theorem mlight {S : Finset Block} {x : P} : x ∈ light S ↔ deg S x = 11 := by simp [light]
private theorem mheavy {S : Finset Block} {x : P} : x ∈ heavy S ↔ deg S x = 9 := by simp [heavy]

private theorem breakdown141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) (p : P) (d : deg S p = 9 ∨ deg S p = 11) :
    (gap S p ∩ heavy S).card = (if deg S p = 9 then 0 else 2) ∧
    (gap S p ∩ light S).card = (if deg S p = 9 then 48 else 22) := by
  classical
  obtain ⟨kinds,_,_,_⟩ := degree_counts_141 hs sz no
  have all (x : P) (hx : x ∈ gap S p) : deg S x = 9 ∨ deg S x = 11 := by
    have g := gap_mem.mp hx
    rcases kinds x with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (g.2 (neighbor_symm.mp (full_joins hs h g.1.symm))).elim
  have degreeSum := countWeights S (fun _ => (1:ℤ))
  have sizes (L : Block) (hl : L ∈ S) : (L.card:ℤ) = 13 := by exact_mod_cast hs.1 L hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at degreeSum
  rw [sum_congr rfl sizes] at degreeSum; simp [sz] at degreeSum
  have lds (L : Block) (hl : L ∈ pencil S p) : (∑ x ∈ L, (deg S x:ℤ)) = 153 := by
    rw [onLine hs (mem_filter.mp hl).1,sz]; norm_num
  have ps := pencilSum hs p (fun y => (deg S y:ℤ))
  rw [sum_congr rfl lds,sum_const] at ps
  change _ = deg S p • (153:ℤ) at ps
  have partition := sum_sdiff (f := fun x => (deg S x:ℤ)) (subset_univ (insert p (neighbors S p)))
  change (∑ x ∈ gap S p, (deg S x:ℤ)) + _ = _ at partition
  rw [degreeSum, sum_insert (self_neigh _ _)] at partition
  have val (x : P) (hx : x ∈ gap S p) : (deg S x:ℤ) =
      11 - 2*weight (heavy S) x := by
    rcases all x hx with h|h <;> simp [weight,mheavy,h]
  have per (x : P) (hx : x ∈ gap S p) :
      weight (heavy S) x + weight (light S) x = 1 := by
    rcases all x hx with h|h <;> simp [weight,mheavy,mlight,h]
  have sumval := sum_congr rfl val
  have sumper := sum_congr rfl per
  rw [sum_add_distrib,sum_weight,sum_weight,sum_const,gap_size hs] at sumper
  rw [sum_sub_distrib,←mul_sum,sum_weight,sum_const,gap_size hs] at sumval
  rcases d with low|high
  · rw [low] at ps partition sumper sumval ⊢
    norm_num at ps partition sumper sumval
    constructor <;> split <;> omega
  · rw [high] at ps partition sumper sumval ⊢
    norm_num at ps partition sumper sumval
    constructor <;> split <;> omega

private theorem extendingClique {S : Finset Block} (hs : Valid S) (C : Block)
    (size : C.card = 13) (uncov : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → y ∈ gap S x)
    (allDeg : (∑ x ∈ C, (deg S x:ℤ)) = S.card) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card+1 ∧ Valid T := by
  classical
  have leOne (L : Block) (hl : L ∈ S) : (L ∩ C).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra h
    have g := gap_mem.mp (uncov x (mem_inter.mp hx).2 y (mem_inter.mp hy).2 h)
    exact g.2 (neighbors_mem.mpr ⟨Ne.symm h,L,hl,(mem_inter.mp hx).1,(mem_inter.mp hy).1⟩)
  have dsum := countWeights S (weight C)
  simp only [weight,mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_inter,univ_inter,
    sum_const,nsmul_eq_mul] at dsum
  rw [allDeg] at dsum
  have dif (L : Block) (hl : L ∈ S) : 0 ≤ 1-((L ∩ C).card:ℤ) := by
    have := leOne L hl; omega
  have zero : ∑ L ∈ S, (1-((L ∩ C).card:ℤ)) = 0 := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,←dsum,sub_self]
  have exact1 (L : Block) (hl : L ∈ S) : (L ∩ C).card = 1 := by
    have := (sum_eq_zero_iff_of_nonneg dif).mp zero L hl
    omega
  have fresh : C ∉ S := by
    intro hh; have t := exact1 C hh
    rw [inter_self,size] at t; contradiction
  have single {a b : Block} (h : (a ∩ b).card = 1) : ∃! x, x ∈ a ∧ x ∈ b := by
    obtain ⟨x,hx⟩ := card_eq_one.mp h
    have key (y : P) : (y ∈ a ∧ y ∈ b) ↔ y = x := by rw [← mem_inter,hx,mem_singleton]
    exact ⟨x,(key x).mpr rfl,fun y hy => (key y).mp hy⟩
  refine ⟨insert C S, subset_insert _ _, card_insert_of_notMem fresh, ?_, ?_⟩
  · intro L hl; rcases mem_insert.mp hl with rfl|h
    · exact size
    · exact hs.1 L h
  · intro a ha b hb ne
    rcases mem_insert.mp ha with hA | ha'
    · subst a
      rcases mem_insert.mp hb with hbE | hb'
      · exact (ne hbE.symm).elim
      · exact single (by rw [inter_comm]; exact exact1 _ hb')
    · rcases mem_insert.mp hb with hB | hb'
      · subst b; exact single (exact1 _ ha')
      · exact hs.2 _ ha' _ hb' ne

end PlaneTwelve.Seed

/-
# The 22 light neighbors at a point in a partial plane of order twelve

The local graph in the 141-line case has two distinguished cliques.  The
numerical coloring implication uses Mathlib's Andrásfai–Erdős–Sós theorem.
-/

namespace PlaneTwelve

open Finset SimpleGraph

/-- Three twelve-element neighborhoods in a common twenty-four-element set
cannot have all three pairwise intersections of size at most three. -/
theorem triangleFreeOfNeighborhoodCounts {V X : Type*} [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) (U : Finset X) (f : V → Finset X) (size : U.card = 24)
    (subset : ∀ x, f x ⊆ U) (degree : ∀ x, (f x).card = 12)
    (overlap : ∀ x y, Gᶜ.Adj x y → (f x ∩ f y).card ≤ 3) :
    Gᶜ.CliqueFree 3 := by
  intro s hs
  obtain ⟨x,y,z,xy,xz,yz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  have h₁ := card_union_add_card_inter (f x) (f y)
  have h₂ := card_union_add_card_inter (f x ∪ f y) (f z)
  have h₃ := card_union_le (f x ∩ f z) (f y ∩ f z)
  have h₄ := card_le_card (union_subset (union_subset (subset x) (subset y)) (subset z))
  rw [Finset.union_inter_distrib_right] at h₂
  have := overlap x y xy
  have := overlap y z yz
  have := overlap x z xz
  have := degree x
  have := degree y
  have := degree z
  omega

private theorem boundOffSide {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A K : Finset V)
    (ac : G.IsClique (A : Set V)) (kc : G.IsClique (K : Set V))
    (ca : A.card = 11) (upper : ∀ x, G.degree x ≤ 12)
    {x : V} (xa : x ∈ A) (xk : x ∈ K) :
    (K \ A).card ≤ 2 := by
  classical
  have dis : Disjoint (A.erase x) (K \ A) := by
    apply Finset.disjoint_left.mpr
    intro y ha hk
    exact (mem_sdiff.mp hk).2 (mem_of_mem_erase ha)
  have sub : A.erase x ∪ (K \ A) ⊆ G.neighborFinset x := by
    intro y hy
    apply (G.mem_neighborFinset x y).mpr
    rcases mem_union.mp hy with h | h
    · exact ac xa (mem_erase.mp h).2 (mem_erase.mp h).1.symm
    · have hyA := (mem_sdiff.mp h).2
      exact kc xk (mem_sdiff.mp h).1 (by rintro rfl; exact hyA xa)
  have h := card_le_card sub
  rw [card_union_of_disjoint dis, card_erase_of_mem xa, ca,
    G.card_neighborFinset_eq_degree] at h
  have := upper x
  omega

/-- Every clique with at least five vertices lies on one of the two sides.
In particular the only cliques of size eleven are the two sides. -/
theorem lightNeighborhoodCliques {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : Fintype.card V = 22)
    (triangle : Gᶜ.CliqueFree 3) (upper : ∀ x, G.degree x ≤ 12)
    (cliqueBound : ∀ K : Finset V, G.IsClique (K : Set V) → K.card ≤ 11) :
    ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = univ ∧
      A.card = 11 ∧ B.card = 11 ∧ G.IsClique (A : Set V) ∧ G.IsClique (B : Set V) ∧
      (∀ K : Finset V, G.IsClique (K : Set V) → 5 ≤ K.card → K ⊆ A ∨ K ⊆ B) ∧
      (∀ K : Finset V, G.IsClique (K : Set V) → K.card = 11 → K = A ∨ K = B) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have min : 9 ≤ Gᶜ.minDegree := by
    apply Gᶜ.le_minDegree_of_forall_le_degree
    intro x
    rw [SimpleGraph.degree_compl, order]
    have := upper x
    omega
  obtain ⟨C⟩ := SimpleGraph.colorable_of_cliqueFree_lt_minDegree
    (G := Gᶜ) (r := 2) triangle (by rw [order]; omega)
  let A : Finset V := univ.filter (fun x => C x = 0)
  let B : Finset V := univ \ A
  have ma (x : V) : x ∈ A ↔ C x = 0 := by simp [A]
  have mb (x : V) : x ∈ B ↔ C x ≠ 0 := by simp [B,ma]
  have side {x y : V} (h : C x = C y) (ne : x ≠ y) : G.Adj x y := by
    by_contra hxy
    exact C.valid (show Gᶜ.Adj x y from ⟨ne,hxy⟩) h
  have ac : G.IsClique (A : Set V) := by
    intro x hx y hy ne
    exact side (((ma _).mp hx).trans ((ma _).mp hy).symm) ne
  have bc : G.IsClique (B : Set V) := by
    intro x hx y hy ne
    have h₁ := (mb _).mp hx
    have h₂ := (mb _).mp hy
    apply side _ ne
    exact Fin.ext (by omega)
  have dis : Disjoint A B := Finset.disjoint_sdiff
  have union : A ∪ B = univ := by simp [B]
  have both := card_union_of_disjoint dis
  rw [union, card_univ, order] at both
  have ubA := cliqueBound A ac
  have ubB := cliqueBound B bc
  have ca : A.card = 11 := by omega
  have cb : B.card = 11 := by omega
  have cover (K : Finset V) (kc : G.IsClique (K : Set V)) (large : 5 ≤ K.card) :
      K ⊆ A ∨ K ⊆ B := by
    classical
    by_contra! fails
    obtain ⟨x,xk,nxa⟩ := Finset.not_subset.mp fails.1
    obtain ⟨y,yk,nyb⟩ := Finset.not_subset.mp fails.2
    have xb : x ∈ B := mem_sdiff.mpr ⟨mem_univ _,nxa⟩
    have ya : y ∈ A := by simpa [B] using nyb
    have offA := boundOffSide G A K ac kc ca upper ya yk
    have offB := boundOffSide G B K bc kc cb upper xb xk
    have split : K \ A ∪ (K \ B) = K := by
      ext z
      by_cases hz : z ∈ A <;> simp [B, hz]
    have h := card_union_le (K \ A) (K \ B)
    rw [split] at h
    omega
  refine ⟨A,B,dis,union,ca,cb,ac,bc,cover,?_⟩
  intro K kc size
  rcases cover K kc (by omega) with h|h
  · exact Or.inl (eq_of_subset_of_card_le h (by omega))
  · exact Or.inr (eq_of_subset_of_card_le h (by omega))

/-- Lift the two sides of an induced neighborhood to 12-cliques in the
whole graph. Every 12-clique through the fixed point is one of these two. -/
theorem liftLightPencil {L : Type*} [Fintype L] [DecidableEq L]
    (G : SimpleGraph L) [DecidableRel G.Adj] (x : L)
    (order : Fintype.card (G.neighborSet x) = 22)
    (triangle : (G.induce (G.neighborSet x))ᶜ.CliqueFree 3)
    (upper : ∀ y, (G.induce (G.neighborSet x)).degree y ≤ 12)
    (bound : ∀ K : Finset (G.neighborSet x),
      (G.induce (G.neighborSet x)).IsClique K → K.card ≤ 11) :
    ∃ A B : Finset L, G.IsNClique 12 A ∧ G.IsNClique 12 B ∧
      A ∩ B = {x} ∧ A ∪ B = insert x (G.neighborFinset x) ∧
      ∀ K : Finset L, G.IsNClique 12 K → x ∈ K → K = A ∨ K = B := by
  classical
  obtain ⟨s,t,dis,su,sc,tc,sk,tk,_,maximal⟩ :=
    lightNeighborhoodCliques (G.induce (G.neighborSet x)) order triangle upper bound
  let e : G.neighborSet x ↪ L := Function.Embedding.subtype _
  let S := s.map e
  let T := t.map e
  have neighbor {U : Finset (G.neighborSet x)} {y : L} (hy : y ∈ U.map e) :
      G.Adj x y := U.property_of_mem_map_subtype hy
  have make (U : Finset (G.neighborSet x)) (uc : U.card = 11)
      (uk : (G.induce (G.neighborSet x)).IsClique (U : Set (G.neighborSet x))) :
      G.IsNClique 12 (insert x (U.map e)) := by
    have nx : x ∉ U.map e := fun hx => (neighbor hx).ne rfl
    refine ⟨?_,by rw [card_insert_of_notMem nx,card_map,uc]⟩
    rw [coe_insert, G.isClique_insert]
    refine ⟨?_,fun y hy _ => neighbor hy⟩
    rw [coe_map]
    exact (G.isClique_induce_iff.mp uk)
  have di : Disjoint S T := by simpa [S,T] using dis
  have un : S ∪ T = G.neighborFinset x := by
    change s.map e ∪ t.map e = _
    rw [← map_union, su]
    ext y
    exact ⟨fun h => (G.mem_neighborFinset _ _).mpr (neighbor h),
      fun h => mem_map.mpr ⟨⟨y,(G.mem_neighborFinset _ _).mp h⟩,mem_univ _,rfl⟩⟩
  refine ⟨insert x S,insert x T,make s sc sk,make t tc tk,?_,?_,?_⟩
  · ext y
    by_cases h : y = x
    · simp [h]
    · have : ¬(y ∈ S ∧ y ∈ T) := fun w => disjoint_left.mp di w.1 w.2
      simp [h,this]
  · simp [un]
  · intro K k12 hx
    let E := K.erase x
    let D := E.subtype (G.Adj x)
    have pre : ∀ y ∈ E, G.Adj x y := by
      intro y hy
      exact k12.1 hx (mem_of_mem_erase hy) (mem_erase.mp hy).1.symm
    have recover : D.map e = E := subtype_map_of_mem pre
    have eleven : G.IsNClique 11 E := k12.erase_of_mem hx
    have ind : (G.induce (G.neighborSet x)).IsNClique 11 D :=
      (G.isNClique_induce_iff _ _ _).mpr (by
        change G.IsNClique 11 (D.map e)
        rw [recover]; exact eleven)
    have which := maximal D ind.1 ind.2
    have back : insert x E = K := insert_erase hx
    rcases which with eq | eq
    · left; rw [← back, ← recover,eq]
    · right; rw [← back, ← recover,eq]

/-- The 12-cliques of the light graph are the vertices of the auxiliary
graph. Each light point has two ends, distinct cliques intersect in at most
one light, and sharing a clique is exactly adjacency for distinct lights. -/
theorem lightCliqueIncidences {L : Type*} [Fintype L] [DecidableEq L]
    (G : SimpleGraph L) [DecidableRel G.Adj]
    (pencil : ∀ x, ∃ A B : Finset L, G.IsNClique 12 A ∧ G.IsNClique 12 B ∧
      A ∩ B = {x} ∧ A ∪ B = insert x (G.neighborFinset x) ∧
      ∀ K : Finset L, G.IsNClique 12 K → x ∈ K → K = A ∨ K = B) :
    let V := ↥(G.cliqueFinset 12)
    let C : V → Finset L := fun i => i.val
    (∀ u, (C u).card = 12) ∧
    (∀ x, (univ.filter (fun u => x ∈ C u)).card = 2) ∧
    (∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) ∧
    (∀ x y, G.Adj x y ↔ x ≠ y ∧ ∃ u, x ∈ C u ∧ y ∈ C u) := by
  classical
  dsimp only
  refine ⟨fun u => (SimpleGraph.mem_cliqueFinset_iff.mp u.property).2,?_,?_,?_⟩
  · intro x
    obtain ⟨A,B,as,bs,inter,_,unique⟩ := pencil x
    let a : ↥(G.cliqueFinset 12) := ⟨A,SimpleGraph.mem_cliqueFinset_iff.mpr as⟩
    let b : ↥(G.cliqueFinset 12) := ⟨B,SimpleGraph.mem_cliqueFinset_iff.mpr bs⟩
    have dist : A ≠ B := by
      rintro rfl
      rw [inter_self] at inter
      have c := as.2
      rw [inter,card_singleton] at c
      omega
    have ab : a ≠ b := fun h => dist (congrArg Subtype.val h)
    have both : x ∈ A ∧ x ∈ B := mem_inter.mp (by rw [inter]; simp)
    have eq : univ.filter (fun u : ↥(G.cliqueFinset 12) => x ∈ u.val) = {a,b} := by
      ext u
      simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
      constructor
      · intro hx
        exact (unique _ (SimpleGraph.mem_cliqueFinset_iff.mp u.property) hx).imp
          (fun h => Subtype.ext h) (fun h => Subtype.ext h)
      · rintro (rfl|rfl)
        · exact both.1
        · exact both.2
    rw [eq,card_pair ab]
  · intro u v neq
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨A,B,_,_,inter,_,unique⟩ := pencil x
    have U := unique u.val (SimpleGraph.mem_cliqueFinset_iff.mp u.property) (mem_inter.mp hx).1
    have V := unique v.val (SimpleGraph.mem_cliqueFinset_iff.mp v.property) (mem_inter.mp hx).2
    have yU := (mem_inter.mp hy).1
    have yV := (mem_inter.mp hy).2
    rcases U with uA|uB <;> rcases V with vA|vB
    · exact (neq (Subtype.ext (uA.trans vA.symm))).elim
    · have yh : y ∈ A ∩ B := mem_inter.mpr ⟨uA ▸ yU,vB ▸ yV⟩
      simpa [inter,eq_comm] using yh
    · have yh : y ∈ A ∩ B := mem_inter.mpr ⟨vA ▸ yV,uB ▸ yU⟩
      simpa [inter,eq_comm] using yh
    · exact (neq (Subtype.ext (uB.trans vB.symm))).elim
  · intro x y
    constructor
    · intro h
      obtain ⟨A,B,as,bs,inter,union,_⟩ := pencil x
      have both : x ∈ A ∧ x ∈ B := mem_inter.mp (by rw [inter]; simp)
      have either : y ∈ A ∪ B := by
        rw [union]
        exact mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr h)
      refine ⟨h.ne,?_⟩
      rcases mem_union.mp either with ha|hb
      · exact ⟨⟨A,SimpleGraph.mem_cliqueFinset_iff.mpr as⟩,both.1,ha⟩
      · exact ⟨⟨B,SimpleGraph.mem_cliqueFinset_iff.mpr bs⟩,both.2,hb⟩
    · rintro ⟨ne,u,hu,hv⟩
      exact (SimpleGraph.mem_cliqueFinset_iff.mp u.property).1 hu hv ne

/-- Convert the gap and pencil counts in an actual 141-line configuration
into the complete local-clique incidence structure. Here `i` includes light
points into the ambient point set, and `pencil` records their old lines. -/
theorem reconstructLightCliques {L P O : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq P] [DecidableEq O] (G : SimpleGraph L) [DecidableRel G.Adj]
    (i : L ↪ P) (U : L → Finset P) (gap : ∀ x y, G.Adj x y ↔ i y ∈ U x)
    (size : ∀ x, (U x).card = 24) (order : ∀ x, G.degree x = 22)
    (adjacent : ∀ x y, G.Adj x y → (U x ∩ U y).card = 12)
    (collinear : ∀ x y, x ≠ y → ¬G.Adj x y → (U x ∩ U y).card ≤ 4)
    (old : Finset O) (pencil : L → Finset O) (oldSize : old.card = 141)
    (oldSub : ∀ x, pencil x ⊆ old) (lineDeg : ∀ x, (pencil x).card = 11)
    (noJoin : ∀ x y, G.Adj x y → Disjoint (pencil x) (pencil y)) :
    let V := ↥(G.cliqueFinset 12)
    let C : V → Finset L := fun j => j.val
    (∀ u, (C u).card = 12) ∧
    (∀ x, (univ.filter (fun u => x ∈ C u)).card = 2) ∧
    (∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) ∧
    (∀ x y, G.Adj x y ↔ x ≠ y ∧ ∃ u, x ∈ C u ∧ y ∈ C u) := by
  classical
  apply lightCliqueIncidences G
  intro x
  let N := G.neighborSet x
  let I := G.induce N
  let embed : N ↪ P := (Function.Embedding.subtype _).trans i
  let F (y : N) := U x ∩ U y.val
  have hx (y : N) : G.Adj x y.val := y.property
  have fsize (y : N) : (F y).card = 12 := adjacent _ _ (hx y)
  have tr : Iᶜ.CliqueFree 3 := by
    apply triangleFreeOfNeighborhoodCounts I (U x) F (size x) (fun _ => inter_subset_left) fsize
    intro y z neg
    have yz : y.val ≠ z.val := fun he => neg.1 (Subtype.ext he)
    have bound := collinear _ _ yz (fun h => neg.2 (show I.Adj y z from h))
    have self : i x ∉ U x := fun h => ((gap x x).mpr h).ne rfl
    have outside : i x ∉ F y ∩ F z :=
      fun h => self (mem_inter.mp (mem_inter.mp h).1).1
    have inc : insert (i x) (F y ∩ F z) ⊆ U y.val ∩ U z.val := by
      intro p hp
      rcases mem_insert.mp hp with rfl|hm
      · exact mem_inter.mpr ⟨(gap _ _).mp (hx y).symm,(gap _ _).mp (hx z).symm⟩
      · exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hm).1).2,
                             (mem_inter.mp (mem_inter.mp hm).2).2⟩
    have le := card_le_card inc
    rw [card_insert_of_notMem outside] at le
    omega
  have du (y : N) : I.degree y ≤ 12 := by
    have inc : (I.neighborFinset y).map embed ⊆ F y := by
      intro p hp
      obtain ⟨z,hz,rfl⟩ := mem_map.mp hp
      have yz : G.Adj y.val z.val := (I.mem_neighborFinset y z).mp hz
      exact mem_inter.mpr ⟨(gap _ _).mp (hx z),(gap _ _).mp yz⟩
    have le := card_le_card inc
    rwa [card_map,I.card_neighborFinset_eq_degree,fsize] at le
  have cap (K : Finset N) (hc : I.IsClique K) : K.card ≤ 11 := by
    let S := K.map (Function.Embedding.subtype _)
    have nx : x ∉ S := fun h => (K.property_of_mem_map_subtype h : G.Adj x x).ne rfl
    have cs : G.IsClique (S : Set L) := by
      rw [Finset.coe_map]; exact (G.isClique_induce_iff.mp hc)
    have ci : G.IsClique ((insert x S : Finset L) : Set L) := by
      rw [coe_insert,G.isClique_insert]
      exact ⟨cs,fun y hy _ => K.property_of_mem_map_subtype hy⟩
    let T := insert x S
    have inc : T.biUnion pencil ⊆ old := by
      intro o h
      obtain ⟨v,_,hv⟩ := mem_biUnion.mp h
      exact oldSub v hv
    have pd : (T : Set L).PairwiseDisjoint pencil :=
      fun _ h _ h' ne => noJoin _ _ (ci h h' ne)
    have le := card_le_card inc
    rw [card_biUnion pd,oldSize] at le
    simp only [lineDeg,Finset.sum_const,smul_eq_mul] at le
    have cardT : T.card = K.card + 1 := by rw [show T = insert x S from rfl,
      card_insert_of_notMem nx,card_map]
    rw [cardT] at le
    omega
  apply liftLightPencil G x _ tr du cap
  simpa [SimpleGraph.degree,SimpleGraph.neighborFinset] using order x

end PlaneTwelve

namespace PlaneTwelve.Seed

open Finset

private def lightGraph (S : Finset Block) : SimpleGraph ↥(light S) where
  Adj x y := y.val ∈ gap S x.val
  symm := ⟨fun _ _ h => gap_symm.mp h⟩
  loopless := ⟨fun _ h => (gap_mem.mp h).1 rfl⟩

private instance (S : Finset Block) : DecidableRel (lightGraph S).Adj :=
  fun x y => inferInstanceAs (Decidable (y.val ∈ gap S x.val))

private theorem lightGraph_adj {S : Finset Block} (x y : ↥(light S)) :
    (lightGraph S).Adj x y ↔ y.val ∈ gap S x.val := Iff.rfl

private theorem light_clique_geometry {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) :
    let V := ↥((lightGraph S).cliqueFinset 12)
    let C : V → Finset ↥(light S) := fun u => u.val
    (∀ u, (C u).card = 12) ∧
    (∀ x, (univ.filter (fun u => x ∈ C u)).card = 2) ∧
    (∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) ∧
    (∀ x y, (lightGraph S).Adj x y ↔ x ≠ y ∧ ∃ u, x ∈ C u ∧ y ∈ C u) := by
  classical
  let G := lightGraph S
  let i : ↥(light S) ↪ P := Function.Embedding.subtype _
  have ld (x : ↥(light S)) : deg S x.val = 11 := mlight.mp x.property
  have sz24 (x : ↥(light S)) : (gap S x.val).card = 24 := by rw [gap_size hs,ld]
  have d22 (x : ↥(light S)) : G.degree x = 22 := by
    have mapped : (G.neighborFinset x).map i = gap S x.val ∩ light S := by
      ext y
      constructor
      · intro h
        obtain ⟨z,hz,rfl⟩ := mem_map.mp h
        exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mp hz,z.property⟩
      · intro h
        obtain ⟨hg,hl⟩ := mem_inter.mp h
        exact mem_map.mpr ⟨⟨y,hl⟩,(G.mem_neighborFinset _ _).mpr hg,rfl⟩
    have counts := (breakdown141 hs sz no x.val (Or.inr (ld x))).2
    simp [ld x] at counts
    rw [← counts, ← mapped,card_map,G.card_neighborFinset_eq_degree]
  have adjcount (x y : ↥(light S)) (h : G.Adj x y) :
      (gap S x.val ∩ gap S y.val).card = 12 := by
    have hg : y.val ∈ gap S x.val := h
    have v := common_gaps hs (gap_mem.mp hg).1
    rw [if_pos hg,ld x,ld y] at v
    omega
  have nonadjcount (x y : ↥(light S)) (h : x ≠ y) (ha : ¬G.Adj x y) :
      (gap S x.val ∩ gap S y.val).card ≤ 4 := by
    have hg : y.val ∉ gap S x.val := ha
    have v := common_gaps hs (show y.val ≠ x.val from fun eq => h (Subtype.ext eq.symm))
    rw [if_neg hg,ld x,ld y] at v
    omega
  have noJoin (x y : ↥(light S)) (h : G.Adj x y) :
      Disjoint (pencil S x.val) (pencil S y.val) := by
    apply disjoint_left.mpr
    intro b hb hb'
    obtain ⟨sb,xb⟩ := mem_filter.mp hb
    obtain ⟨_,yb⟩ := mem_filter.mp hb'
    obtain ⟨ne,absent⟩ := gap_mem.mp (show y.val ∈ gap S x.val from h)
    exact absent (neighbors_mem.mpr ⟨ne,b,sb,xb,yb⟩)
  exact PlaneTwelve.reconstructLightCliques G i (fun x => gap S x.val)
    (fun _ _ => Iff.rfl) sz24 d22 adjcount nonadjcount S (fun x => pencil S x.val) sz
    (fun x => filter_subset _ _) ld noJoin

end PlaneTwelve.Seed

/-
The final marked-edge argument in the 141-line extension proof.
The graph on 16 vertices has degree 12. The two endpoint weights sum to 8
on an unmarked edge and to 16 on a marked one. Six disjoint unmarked edges
force a vertex of weight 12.
-/

namespace PlaneTwelve.MarkedMatching
open Finset

theorem full_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → Finset V) (order : Fintype.card V = 16) (degree : ∀ x, (N x).card = 12)
    (w : V → ℕ) (bound : ∀ x, w x ≤ 12) (total : ∑ x, w x = 96)
    (edge : ∀ x y, y ∈ N x → w x+w y = 8 ∨ w x+w y = 16)
    (matching : Fin 6 × Bool → V) (injective : Function.Injective matching)
    (unmarked : ∀ i, w (matching (i,false)) + w (matching (i,true)) = 8) :
    ∃ x, w x = 12 := by
  classical
  have common (x y : V) : (N x ∩ N y).Nonempty := by
    apply card_pos.mp
    have a := card_union_add_card_inter (N x) (N y)
    have b := card_le_univ (N x ∪ N y)
    rw [degree,degree] at a
    omega
  have residues (x y : V) : w x % 8 = w y % 8 := by
    obtain ⟨z,hz⟩ := common x y
    have a := edge _ _ (mem_inter.mp hz).1
    have b := edge _ _ (mem_inter.mp hz).2
    omega
  have ne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v := Classical.choice ne
  obtain ⟨u,hu⟩ := card_pos.mp (show 0 < (N v).card by rw [degree]; decide)
  have law := edge _ _ hu
  have equ := residues u v
  have opts : w v % 8 = 0 ∨ w v % 8 = 4 := by omega
  by_contra! no
  rcases opts with zero | four
  · have values (x : V) : w x = 0 ∨ w x = 8 := by have := bound x; have := residues x v; omega
    let Z := (univ : Finset V).filter (fun x => w x = 0)
    have pieces (x : V) (_ : x ∈ (univ : Finset V)) :
        w x + (if w x = 0 then 8 else 0) = 8 := by
      rcases values x with h|h <;> simp [h]
    have card := sum_congr rfl pieces
    rw [sum_add_distrib,total,← sum_filter,sum_const,sum_const,card_univ,order] at card
    change 96 + Z.card • 8 = 16 • (8:ℕ) at card
    have cn : 96 + Z.card * 8 = 128 := by
      simpa using card
    have sz : Z.card = 4 := by omega
    let side (i : Fin 6) := decide (w (matching (i,false)) ≠ 0)
    have hits (i : Fin 6) : matching (i,side i) ∈ Z := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      by_cases z : w (matching (i,false)) = 0
      · simp [side,z]
      · have law := unmarked i
        have val := values (matching (i,false))
        have vtrue : w (matching (i,true)) = 0 := by omega
        simpa [side,z] using vtrue
    let pick (i : Fin 6) : Z := ⟨matching (i,side i),hits i⟩
    have inj : Function.Injective pick := by
      intro i j h
      have heq : matching (i,side i) = matching (j,side j) := congrArg Subtype.val h
      exact congrArg Prod.fst (injective heq)
    have hc := Fintype.card_le_of_injective pick inj
    rw [Fintype.card_fin, Fintype.card_coe, sz] at hc
    omega
  · have val (x : V) (_ : x ∈ (univ : Finset V)) : w x = 4 := by
      have e := residues x v
      have b := bound x
      have n := no x
      omega
    rw [sum_congr rfl val,sum_const,card_univ,order] at total
    contradiction

end PlaneTwelve.MarkedMatching

namespace PlaneTwelve.LightCliques
open Finset

variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

def ends (C : V → Finset L) (x : L) : Finset V := univ.filter (x ∈ C ·)

def neighbors (C : V → Finset L) (u : V) : Finset V :=
  (univ.erase u).filter fun v => (C u ∩ C v).Nonempty

def weight (C : V → Finset L) (M : Finset L) (u : V) : ℕ := (C u ∩ M).card

omit [Fintype L] in
/-- Count the incidences between the selected cliques and selected lights. -/
private theorem incidences (C : V → Finset L) (S : Finset V) (T : Finset L) :
    ∑ u ∈ S, (C u ∩ T).card = ∑ x ∈ T, (ends C x ∩ S).card := by
  classical
  have a (u : V) : T.bipartiteAbove (fun u x => x ∈ C u) u = C u ∩ T := by
    ext x; simp [bipartiteAbove, and_comm]
  have b (x : L) : S.bipartiteBelow (fun u x => x ∈ C u) x = ends C x ∩ S := by
    ext u; simp [bipartiteBelow, ends, and_comm]
  simpa only [a,b] using
    (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := S) (t := T) (fun u x => x ∈ C u))

theorem order (C : V → Finset L) (lightOrder : Fintype.card L = 96)
    (size : ∀ u, (C u).card = 12) (two : ∀ x, (ends C x).card = 2) :
    Fintype.card V = 16 := by
  have h := incidences C univ univ
  simp [size,two,lightOrder] at h
  omega

omit [Fintype L] in
theorem total_weight (C : V → Finset L) (M : Finset L) (sz : M.card = 48)
    (two : ∀ x, (ends C x).card = 2) : ∑ u, weight C M u = 96 := by
  simpa [weight,two,sz] using incidences C univ M

omit [Fintype L] [Fintype V] [DecidableEq V] in
theorem weight_bound (C : V → Finset L) (M : Finset L) (size : ∀ u, (C u).card = 12)
    (u : V) : weight C M u ≤ 12 := by
  simpa [weight,size] using (card_le_card (inter_subset_left (s₁ := C u) (s₂ := M)))

omit [Fintype L] in
theorem degree (C : V → Finset L) (size : ∀ u, (C u).card = 12)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) (u : V) :
    (neighbors C u).card = 12 := by
  classical
  have ht (x : L) (hx : x ∈ C u) : (ends C x ∩ univ.erase u).card = 1 := by
    have e : ends C x ∩ univ.erase u = (ends C x).erase u := by ext v; simp [and_comm]
    rw [e, card_erase_of_mem (by simpa [ends] using hx), two]
  have hi := incidences C (univ.erase u) (C u)
  rw [sum_congr rfl ht] at hi
  simp [size] at hi
  have line (v : V) (hv : v ∈ univ.erase u) :
      (C v ∩ C u).card = if (C u ∩ C v).Nonempty then 1 else 0 := by
    have ub := linear v u (mem_erase.mp hv).1
    rw [inter_comm] at ub ⊢
    by_cases h : (C u ∩ C v).Nonempty
    · have := card_pos.mpr h; simp [h]; omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  rw [sum_congr rfl line, ← sum_filter] at hi
  simpa [neighbors] using hi

omit [Fintype L] in
theorem endpoints {C : V → Finset L} (two : ∀ x, (ends C x).card = 2)
    (x : L) : ∃ u v, u ≠ v ∧ ∀ z, x ∈ C z ↔ z = u ∨ z = v := by
  obtain ⟨u,v,h,he⟩ := card_eq_two.mp (two x)
  refine ⟨u,v,h,fun z => ?_⟩
  have e := Finset.ext_iff.mp he z
  simpa [ends] using e

omit [Fintype L] in
theorem neighbor_edge {C : V → Finset L} {u v : V} (h : v ∈ neighbors C u) :
    u ≠ v ∧ ∃ x, x ∈ C u ∧ x ∈ C v := by
  obtain ⟨hn,x,hx⟩ := mem_filter.mp h
  exact ⟨(mem_erase.mp hn).1.symm,x,mem_inter.mp hx⟩

omit [Fintype L] in
/-- The marked neighbors of the light x are precisely the other marked lights
on one of its two cliques. Counting them gives the endpoint degree law. -/
theorem endpoint_weights (C : V → Finset L) (M : Finset L) (adj : L → L → Prop)
    [DecidableRel adj]
    (graph : ∀ x y, adj x y ↔ x ≠ y ∧ ∃ z, x ∈ C z ∧ y ∈ C z)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1)
    (markCounts : ∀ x, (M.filter (adj x)).card = if x ∈ M then 14 else 8)
    {u v : V} (ne : u ≠ v) {x : L} (hu : x ∈ C u) (hv : x ∈ C v) :
    weight C M u + weight C M v = if x ∈ M then 16 else 8 := by
  classical
  have uniq (z : V) (hz : x ∈ C z) : z = u ∨ z = v := by
    have sub : ({u,v} : Finset V) ⊆ ends C x := by
      intro w hw
      rcases (show w = u ∨ w = v by simpa using hw) with rfl | rfl
      · simpa [ends] using hu
      · simpa [ends] using hv
    have eq := eq_of_subset_of_card_le sub (by simp [two,ne])
    have hz' : z ∈ ends C x := by simpa [ends] using hz
    rw [← eq] at hz'; simpa using hz'
  let U := (C u ∩ M).erase x
  let W := (C v ∩ M).erase x
  have dis : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    obtain ⟨hyx, hyu, _⟩ := (show y ≠ x ∧ y ∈ C u ∧ y ∈ M by simpa [U] using hy)
    have hyv : y ∈ C v := (mem_inter.mp (mem_erase.mp hz).2).1
    exact hyx (card_le_one.mp (linear _ _ ne) _ (mem_inter.mpr ⟨hyu,hyv⟩)
      _ (mem_inter.mpr ⟨hu,hv⟩))
  have cover : U ∪ W = M.filter (adj x) := by
    ext y
    simp only [U,W,mem_union,mem_filter,mem_erase,mem_inter,graph]
    constructor
    · rintro (⟨ny,yu,ym⟩|⟨ny,yv,ym⟩)
      · exact ⟨ym,ny.symm,u,hu,yu⟩
      · exact ⟨ym,ny.symm,v,hv,yv⟩
    · rintro ⟨ym,ny,z,zx,zy⟩
      rcases uniq z zx with rfl|rfl
      · exact Or.inl ⟨ny.symm,zy,ym⟩
      · exact Or.inr ⟨ny.symm,zy,ym⟩
  have eq := card_union_of_disjoint dis
  rw [cover,markCounts] at eq
  dsimp [U,W] at eq
  by_cases hx : x ∈ M
  · rw [if_pos hx, card_erase_of_mem (mem_inter.mpr ⟨hu,hx⟩),card_erase_of_mem (mem_inter.mpr ⟨hv,hx⟩)] at eq
    have a := card_pos.mpr (show (C u ∩ M).Nonempty from ⟨x,mem_inter.mpr ⟨hu,hx⟩⟩)
    have b := card_pos.mpr (show (C v ∩ M).Nonempty from ⟨x,mem_inter.mpr ⟨hv,hx⟩⟩)
    simp [weight,hx]; omega
  · simpa [weight,hx] using eq.symm

end PlaneTwelve.LightCliques

namespace PlaneTwelve.LightCliques
open Finset
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

omit [Fintype L] in
/-- Six pairwise nonadjacent unmarked lights give the six disjoint unmarked
edges required by the marked matching argument. -/
theorem matching (C : V → Finset L) (M : Finset L) (adj : L → L → Prop)
    [DecidableRel adj]
    (graph : ∀ x y, adj x y ↔ x ≠ y ∧ ∃ z, x ∈ C z ∧ y ∈ C z)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1)
    (markCounts : ∀ x, (M.filter (adj x)).card = if x ∈ M then 14 else 8)
    (light : Fin 6 → L) (inj : Function.Injective light)
    (unmarked : ∀ i, light i ∉ M)
    (independent : ∀ i j, i ≠ j → ¬adj (light i) (light j)) :
    ∃ pick : Fin 6 × Bool → V, Function.Injective pick ∧
      ∀ i, weight C M (pick (i,false)) + weight C M (pick (i,true)) = 8 := by
  classical
  choose u v ne hv using fun i => endpoints two (light i)
  let pick : Fin 6 × Bool → V := fun ⟨i,b⟩ => if b then v i else u i
  have inc (i : Fin 6) (b : Bool) : light i ∈ C (pick (i,b)) := by
    apply (hv i _).mpr
    cases b <;> simp [pick]
  refine ⟨pick,?_,?_⟩
  · rintro ⟨i,a⟩ ⟨j,b⟩ he
    have ij : i = j := by
      by_contra ni
      exact independent i j ni ((graph _ _).mpr ⟨fun h => ni (inj h), _, inc i a, he ▸ inc j b⟩)
    subst j
    cases a <;> cases b
    · rfl
    · exact (ne i he).elim
    · exact (ne i he.symm).elim
    · rfl
  · intro i
    have h := endpoint_weights C M adj graph two linear markCounts (ne i)
      ((hv i _).mpr (Or.inl rfl)) ((hv i _).mpr (Or.inr rfl))
    simpa [pick,unmarked] using h

end PlaneTwelve.LightCliques

namespace PlaneTwelve.LightCliques
open Finset

/-- A heavy point and the six unmarked lights on one old line force an
entire 12-clique adjacent to that heavy point. -/
theorem saturated_clique {L V : Type*} [Fintype L] [Fintype V]
    [DecidableEq L] [DecidableEq V] (C : V → Finset L) (M : Finset L)
    (adj : L → L → Prop) [DecidableRel adj] (lightOrder : Fintype.card L = 96)
    (size : ∀ u, (C u).card = 12) (markedCount : M.card = 48)
    (graph : ∀ x y, adj x y ↔ x ≠ y ∧ ∃ z, x ∈ C z ∧ y ∈ C z)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1)
    (markCounts : ∀ x, (M.filter (adj x)).card = if x ∈ M then 14 else 8)
    (light : Fin 6 → L) (inj : Function.Injective light)
    (unmarked : ∀ i, light i ∉ M)
    (independent : ∀ i j, i ≠ j → ¬adj (light i) (light j)) :
    ∃ u, C u ⊆ M := by
  classical
  obtain ⟨pick, hi, hm⟩ := matching C M adj graph two linear markCounts light inj unmarked independent
  obtain ⟨u,full⟩ := PlaneTwelve.MarkedMatching.full_vertex
    (neighbors C) (order C lightOrder size two) (degree C size two linear)
    (weight C M) (weight_bound C M size) (total_weight C M markedCount two)
    (fun u v h => by
      obtain ⟨ne,x,hu,hv⟩ := neighbor_edge h
      have h := endpoint_weights C M adj graph two linear markCounts ne hu hv
      by_cases hx : x ∈ M
      · exact Or.inr (by simpa [hx] using h)
      · exact Or.inl (by simpa [hx] using h)) pick hi hm
  refine ⟨u,?_⟩
  have e : C u ∩ M = C u := eq_of_subset_of_card_le inter_subset_left (by
    change (C u).card ≤ weight C M u; rw [size,full])
  exact fun x h => (mem_inter.mp (show x ∈ C u ∩ M from e.symm ▸ h)).2

end PlaneTwelve.LightCliques


namespace PlaneTwelve.Seed
open Finset

/-- A heavy point lies on a line with no other heavy point. The six light
points on that line are mutually collinear and are collinear to the heavy
point. -/
theorem six_unmarked_141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (kinds : ∀ x, deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13)
    (heavyCard : ((univ : Finset P).filter (fun x => deg S x = 9)).card = 4)
    {e : P} (heavy : deg S e = 9) :
    ∃ light : Fin 6 → P, Function.Injective light ∧
      (∀ i, deg S (light i) = 11 ∧ light i ∈ neighbors S e) ∧
      ∀ i j, i ≠ j → light j ∈ neighbors S (light i) := by
  classical
  let H := (univ : Finset P).filter (fun x => deg S x = 9)
  have he : e ∈ H := mem_filter.mpr ⟨mem_univ _,heavy⟩
  have good : ∃ l ∈ pencil S e, ∀ x ∈ l, deg S x = 9 → x = e := by
    by_contra! no
    let F := pencil S e
    have other (l : F) : ∃ x, x ∈ l.val ∧ deg S x = 9 ∧ x ≠ e := no l.val l.property
    choose p pm ph pn using other
    let f (l : F) : H.erase e := ⟨p l,mem_erase.mpr ⟨pn l,mem_filter.mpr ⟨mem_univ _,ph l⟩⟩⟩
    have inj : Function.Injective f := by
      intro l m eqn
      have eqp : p l = p m := congrArg Subtype.val eqn
      by_contra hne
      have dne : l.val ≠ m.val := fun h => hne (Subtype.ext h)
      have dis := pencil_disjoint hs e l.property m.property dne
      exact disjoint_left.mp dis (mem_erase.mpr ⟨pn l,pm l⟩) (mem_erase.mpr ⟨pn l,eqp ▸ pm m⟩)
    have fewer := Fintype.card_le_of_injective f inj
    rw [Fintype.card_coe,Fintype.card_coe,card_erase_of_mem he] at fewer
    change deg S e ≤ H.card - 1 at fewer
    change H.card = 4 at heavyCard
    omega
  obtain ⟨l,hl,alone⟩ := good
  obtain ⟨ls,el⟩ := mem_filter.mp hl
  let T := l.filter (fun x => deg S x = 11)
  have r (x : P) (hx : x ∈ l) :
      (deg S x : ℤ) = 13 - (if x = e then 4 else 0) - (if deg S x = 11 then 2 else 0) := by
    rcases kinds x with h|h|h
    · have := alone x hx h; subst x; norm_num [heavy]
    · have ne : x ≠ e := fun heq => by subst x; omega
      norm_num [ne,h]
    · have ne : x ≠ e := fun heq => by subst x; omega
      norm_num [ne,h]
  have count := sum_congr rfl r
  rw [onLine hs ls,sz,sum_sub_distrib,sum_sub_distrib,sum_const,hs.1 l ls] at count
  simp only [sum_ite_eq',if_pos el,← sum_filter,sum_const,nsmul_eq_mul] at count
  have six : T.card = 6 := by dsimp [T]; omega
  have cardT : Fintype.card T = 6 := by simpa using six
  let light (i : Fin 6) := ((Fintype.equivFinOfCardEq cardT).symm i).val
  have lt (i : Fin 6) : light i ∈ T := ((Fintype.equivFinOfCardEq cardT).symm i).property
  have inj : Function.Injective light := by
    intro i j h
    exact (Fintype.equivFinOfCardEq cardT).symm.injective (Subtype.ext h)
  refine ⟨light,inj,?_,?_⟩
  · intro i
    obtain ⟨ll,dl⟩ := mem_filter.mp (lt i)
    refine ⟨dl,neighbors_mem.mpr ⟨?_,l,ls,el,ll⟩⟩
    intro heq; rw [heq,heavy] at dl; contradiction
  · intro i j ne
    exact neighbors_mem.mpr ⟨fun h => ne (inj h).symm,l,ls,(mem_filter.mp (lt i)).1,
      (mem_filter.mp (lt j)).1⟩

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

private theorem sixOnLine {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) (e : P) (he : e ∈ heavy S) :
    ∃ f : Fin 6 → ↑(light S), Function.Injective f ∧
      (∀ i, (f i).val ∉ gap S e) ∧
      (∀ i j, i ≠ j → (f j).val ∉ gap S (f i).val) := by
  have ⟨kinds,heavyCard,_,_⟩ := degree_counts_141 hs sz no
  obtain ⟨point,inject,members,pairs⟩ :=
    six_unmarked_141 hs sz kinds heavyCard (mheavy.mp he)
  let f (i : Fin 6) : ↑(light S) := ⟨point i, mlight.mpr (members i).1⟩
  refine ⟨f,fun i j eqn => inject (congrArg Subtype.val eqn),?_,?_⟩
  · intro i hg
    exact (gap_mem.mp hg).2 (members i).2
  · intro i j ne hg
    exact (gap_mem.mp hg).2 (pairs i j ne)

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset
open PlaneTwelve.LightCliques

private theorem saturated_extension {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) (G : SimpleGraph ↑(light S)) [DecidableRel G.Adj]
    (adj : ∀ x y : ↑(light S), G.Adj x y ↔ y.val ∈ gap S x.val)
    (cliques :
      (∀ u : ↥(G.cliqueFinset 12), u.val.card = 12) ∧
      (∀ x, (univ.filter (fun u : ↥(G.cliqueFinset 12) => x ∈ u.val)).card = 2) ∧
      (∀ u v : ↥(G.cliqueFinset 12), u ≠ v → (u.val ∩ v.val).card ≤ 1) ∧
      (∀ x y, G.Adj x y ↔ x ≠ y ∧ ∃ u : ↥(G.cliqueFinset 12), x ∈ u.val ∧ y ∈ u.val)) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card+1 ∧ Valid T := by
  classical
  obtain ⟨kinds,heavyCard,lightCard,_⟩ := degree_counts_141 hs sz no
  change (heavy S).card = 4 at heavyCard
  change (light S).card = 96 at lightCard
  obtain ⟨e,he⟩ := card_pos.mp (show 0 < (heavy S).card by omega)
  have de := mheavy.mp he
  have disj : (gap S e ∩ heavy S).card = 0 := by
    simpa [de] using (breakdown141 hs sz no e (Or.inl de)).1
  have glight (x : P) (hx : x ∈ gap S e) : x ∈ light S := by
    rcases kinds x with h|h|h
    · have f := mem_inter.mpr ⟨hx,mheavy.mpr h⟩
      rw [card_eq_zero.mp disj] at f; exact (notMem_empty _ f).elim
    · exact mlight.mpr h
    · have g := gap_mem.mp hx
      exact (g.2 (neighbor_symm.mp (full_joins hs h g.1.symm))).elim
  let M := (gap S e).subtype (· ∈ light S)
  have mMem (x : ↑(light S)) : x ∈ M ↔ x.val ∈ gap S e := mem_subtype
  have msize : M.card = 48 := by
    rw [show M = _ from rfl,card_subtype,filter_eq_self.mpr glight,gap_size hs,de]
  have markCounts (x : ↑(light S)) :
      (M.filter (G.Adj x)).card = if x ∈ M then 14 else 8 := by
    have eq : M.filter (G.Adj x) = ((gap S e ∩ gap S x.val).subtype (· ∈ light S)) := by
      ext y; simp only [mem_filter,mMem,adj,mem_subtype,mem_inter]
    have sub (y : P) (hy : y ∈ gap S e ∩ gap S x.val) : y ∈ light S :=
      glight y (mem_inter.mp hy).1
    rw [eq,card_subtype,filter_eq_self.mpr sub]
    have dx := mlight.mp x.property
    have ne : x.val ≠ e := by intro eq; rw [eq,de] at dx; contradiction
    have c := common_gaps hs ne
    rw [de,dx] at c
    by_cases h : x ∈ M
    · rw [if_pos h]
      rw [if_pos ((mMem _).mp h)] at c
      norm_num at c; exact_mod_cast c
    · rw [if_neg h]
      rw [if_neg (fun a => h ((mMem _).mpr a))] at c
      norm_num at c; exact_mod_cast c
  let E : ↑(light S) ↪ P := Function.Embedding.subtype _
  let C : ↥(G.cliqueFinset 12) → Finset ↑(light S) := fun u => u.val
  obtain ⟨f,fi,miss,ind⟩ := sixOnLine hs sz no e he
  have count : Fintype.card ↑(light S) = 96 := by simpa using lightCard
  obtain ⟨u,full⟩ := saturated_clique C M G.Adj count cliques.1 msize cliques.2.2.2
    cliques.2.1 cliques.2.2.1 markCounts f fi
    (fun i h => miss i ((mMem _).mp h))
    (fun i j ij h => ind i j ij ((adj _ _).mp h))
  let L := (C u).map E
  have sizeL : L.card = 12 := by rw [show L = _ from rfl,card_map]; exact cliques.1 u
  have ly {x : P} (hx : x ∈ L) : x ∈ light S := (C u).property_of_mem_map_subtype hx
  have fresh : e ∉ L := by intro a; have v := mlight.mp (ly a); omega
  have covered {x : P} (hx : x ∈ L) : x ∈ gap S e := by
    obtain ⟨y,hy,eq⟩ := mem_map.mp hx
    rw [← eq]
    exact (mMem _).mp (full hy)
  have clique {x y : P} (hx : x ∈ L) (hy : y ∈ L) (ne : x ≠ y) : y ∈ gap S x := by
    obtain ⟨a,ha,ax⟩ := mem_map.mp hx
    obtain ⟨b,hb,by'⟩ := mem_map.mp hy
    rw [← ax,← by']
    apply (adj _ _).mp
    exact (cliques.2.2.2 _ _).mpr ⟨fun eq => ne (ax.symm.trans ((congrArg E eq).trans by')),u,ha,hb⟩
  apply extendingClique hs (insert e L)
  · rw [card_insert_of_notMem fresh,sizeL]
  · intro x hx y hy ne
    rcases mem_insert.mp hx with ax|lx <;> rcases mem_insert.mp hy with ay|ly'
    · exact (ne (ax.trans ay.symm)).elim
    · rw [ax]; exact covered ly'
    · rw [ay]; exact gap_symm.mp (covered lx)
    · exact clique lx ly' ne
  · have dx (x : P) (hx : x ∈ L) : (deg S x:ℤ) = 11 := by exact_mod_cast mlight.mp (ly hx)
    rw [sum_insert fresh,de,sum_congr rfl dx,sum_const,sizeL,sz]; rfl

end PlaneTwelve.Seed


namespace PlaneTwelve.Seed

/-- Every 141-line seed admits a one-line extension on the same point set. -/
theorem extend_141 (S : Finset Block) (sz : S.card = 141) (hs : Valid S) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card+1 ∧ Valid T := by
  classical
  by_cases hit : ∃ p, deg S p = 12
  · obtain ⟨p, hp⟩ := hit
    exact extend_at hs p hp
  push Not at hit
  exact saturated_extension hs sz hit (lightGraph S) (fun x y => lightGraph_adj x y)
    (light_clique_geometry hs sz hit)

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

private theorem degree_twelve {S : Finset Block} (hs : Valid S) (hc : S.card = 142) :
    ∃ x, deg S x = 12 := by
  classical
  by_contra! hn
  have h₁ := countWeights S (fun _ => (1 : ℤ))
  simp only [mul_one, sum_const, nsmul_eq_mul] at h₁
  have cardL (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  rw [sum_congr rfl cardL] at h₁
  simp [hc] at h₁
  have h₂ := countWeights S (fun x => (deg S x : ℤ))
  have constant (l : Block) (hl : l ∈ S) : (∑ x ∈ l, (deg S x : ℤ)) = 154 := by
    rw [onLine hs hl, hc]; norm_num
  rw [sum_congr rfl constant] at h₂
  simp [hc] at h₂
  let weight (x : P) : ℤ := if Even (deg S x) then 1 else 0
  have per (l : Block) (hl : l ∈ S) : (1 : ℤ) ≤ ∑ x ∈ l, weight x := by
    have parity : Even (∑ x ∈ l, deg S x) := by
      have v : ∑ x ∈ l, deg S x = 154 := by
        apply Int.ofNat_inj.mp
        simpa only [Nat.cast_sum, Nat.cast_ofNat] using constant l hl
      rw [v]; decide
    have h := (Finset.even_sum_iff_even_card_odd _).mp parity
    by_contra! bad
    have oddall : ∀ x ∈ l, Odd (deg S x) := by
      intro x hx
      by_contra! nn
      have we : weight x = 1 := if_pos (Nat.not_odd_iff_even.mp nn)
      have bound := Finset.single_le_sum (f := weight)
        (fun i (_ : i ∈ l) => by dsimp [weight]; split <;> decide) hx
      omega
    have same : l.filter (fun x => Odd (deg S x)) = l := filter_eq_self.mpr oddall
    rw [same, hs.1 l hl] at h
    exact (by decide : ¬ Even 13) h
  have total := sum_le_sum per
  rw [← countWeights] at total
  simp only [sum_const, hc, nsmul_eq_mul, mul_one, Nat.cast_ofNat] at total
  have cost (x : P) :
      (deg S x : ℤ) * weight x ≤ 5 * ((deg S x : ℤ)^2 - 24 * deg S x + 143) := by
    have hx := hn x
    let r : ℤ := deg S x
    change r * weight x ≤ 5 * (r^2 - 24*r + 143)
    by_cases hii : Even (deg S x)
    · rw [show weight x = 1 from if_pos hii, mul_one]
      obtain ⟨j,hj⟩ := hii
      have sep : r ≤ 10 ∨ 14 ≤ r := by dsimp [r]; omega
      rcases sep with low | high
      · have prod : 0 ≤ (10-r)*(14-r) := mul_nonneg (by omega) (by omega)
        nlinarith
      · nlinarith [sq_nonneg (r-14)]
    · rw [show weight x = 0 from if_neg hii, mul_zero]
      have sep : r ≤ 11 ∨ 13 ≤ r := by dsimp [r]; omega
      rcases sep with low | high
      · have prod : 0 ≤ (13-r)*(11-r) := mul_nonneg (by omega) (by omega)
        nlinarith
      · have prod : 0 ≤ (r-13)*(r-11) := mul_nonneg (by omega) (by omega)
        nlinarith
  have cap := sum_le_sum (fun x (_ : x ∈ (univ : Finset P)) => cost x)
  simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,← mul_sum, sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul, pow_two] at cap
  omega

/-- Every 142-line seed in the variables and incidence relation of the
catalog extends by one line. -/
theorem extend_142 (S : Finset Block) (hc : S.card = 142) (hs : Valid S) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card + 1 ∧ Valid T := by
  obtain ⟨p,hp⟩ := degree_twelve hs hc
  exact extend_at hs p hp

end PlaneTwelve.Seed

theorem PreviousAuthors.extension140 : 
  ∀ S : Finset (Finset (Fin 157)), 140 ≤ S.card → S.card < 143 →
    (∀ b ∈ S, b.card = 13) →
    (∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧
      (∀ b ∈ T, b.card = 13) ∧
      ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c := by
  intro S lo hi size meet
  have h : S.card = 140 ∨ S.card = 141 ∨ S.card = 142 := by omega
  rcases h with h | h | h
  · exact PlaneTwelve.Seed.extend_140 S h ⟨size, meet⟩
  · exact PlaneTwelve.Seed.extend_141 S h ⟨size, meet⟩
  · exact PlaneTwelve.Seed.extend_142 S h ⟨size, meet⟩

end

/- Component Erdos723.Local139.Synthesis. -/
section

/- Complete the degree-twelve branch and reduce every other family to the bipartite profile. -/

namespace Order12

private theorem full_from_140 (S : Blocks) (size : S.card = 140) (good : Good S) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 157 ∧ Good T := by
  have grow (k : ℕ) (hk : k ≤ 17) :
      ∃ T : Blocks, S ⊆ T ∧ T.card = 140 + k ∧ Good T := by
    induction k with
    | zero => exact ⟨S, Finset.Subset.rfl, size, good⟩
    | succ k ih =>
      obtain ⟨T, sub, count, hg⟩ := ih (by omega)
      have step : Ext T := by
        by_cases low : T.card < 143
        · exact PreviousAuthors.extension140 T (by omega) low hg.1 hg.2
        · exact one_line_extension T (by omega) (by omega) hg.1 hg.2
      obtain ⟨U, sub', count', hu⟩ := step
      exact ⟨U, sub.trans sub', by omega, hu⟩
  exact grow 17 (by decide)

theorem full139_of_bipartite
    (last : ∀ D : Profile139.Family, D.n 3 = 24 →
      (Local139.cliqueGraph D.S).Colorable 2 →
      ∃ T : Blocks, D.S ⊆ T ∧ T.card = 157 ∧ Good T)
    (S : Blocks) (size : S.card = 139) (good : Good S) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 157 ∧ Good T := by
  classical
  by_cases near : ∃ p, (through S p).card = 12
  · obtain ⟨p, hp⟩ := near
    obtain ⟨U, sub, count, hu⟩ := degree12_extend S good hp
    obtain ⟨T, sub', hT⟩ := full_from_140 U (by omega) hu
    exact ⟨T, sub.trans sub', hT⟩
  · let D : Profile139.Family := ⟨S, good, size, fun p h => near ⟨p,h⟩⟩
    rcases Local139.full_or_bipartite_threes D with full | ⟨profile,bip,_⟩
    · exact full
    · exact last D profile bip


end Order12

end

/- Component Erdos723.Local139.Grid. -/
section

/- The 81 light points in the bipartite case form a nine-by-nine grid. -/

namespace Order12.Local139

open Profile139
open scoped Classical

/-- A two-coloring of the eighteen degree-nine vertices has two nine-vertex
classes. Every vertex is adjacent to every member of the opposite class. -/
theorem bipartite_nine_iso (D : Family) (profile : D.n 3 = 24)
    (bip : (cliqueGraph D.S).Colorable 2) :
    Nonempty (completeBipartiteGraph (Fin 9) (Fin 9) ≃g cliqueGraph D.S) := by
  classical
  let G := cliqueGraph D.S
  obtain ⟨reg,order,_⟩ := all_threes_graph D profile
  obtain ⟨c⟩ := bip
  have size : Fintype.card (CliqueVertex D.S) = 18 := Nat.card_eq_fintype_card.symm.trans order
  obtain ⟨u⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card (CliqueVertex D.S))).1
  obtain ⟨v,uv⟩ := has_adjacent D u
  let P := fun w : CliqueVertex D.S => c w = c u
  let L : Finset (CliqueVertex D.S) := Finset.univ.filter P
  let R : Finset (CliqueVertex D.S) := Finset.univ.filter (fun w => ¬P w)
  have memL (w) : w ∈ L ↔ P w := by simp [L]
  have memR (w) : w ∈ R ↔ ¬P w := by simp [R]
  have sameOther (w t : CliqueVertex D.S) (notW : ¬P w) (notT : ¬P t) : c w = c t :=
    (by decide : ∀ a b z : Fin 2, a ≠ z → b ≠ z → a=b) _ _ _ notW notT
  have leftSub (w) (wl : P w) : G.neighborFinset w ⊆ R := by
    intro t ht
    apply (memR t).mpr
    intro tl
    exact c.valid ((G.mem_neighborFinset w t).mp ht) (wl.trans tl.symm)
  have rightSub (w) (wr : ¬P w) : G.neighborFinset w ⊆ L := by
    intro t ht
    apply (memL t).mpr
    by_contra tr
    exact c.valid ((G.mem_neighborFinset w t).mp ht) (sameOther w t wr tr)
  have vr : ¬P v := (c.valid uv).symm
  have sizeR : 9 ≤ R.card := (reg u).symm.le.trans (Finset.card_le_card (leftSub u rfl))
  have sizeL : 9 ≤ L.card := (reg v).symm.le.trans (Finset.card_le_card (rightSub v vr))
  have total : L.card + R.card = 18 := by
    have eq := Finset.card_filter_add_card_filter_not P (s := Finset.univ)
    simpa only [Finset.card_univ,size] using eq
  have l9 : L.card = 9 := by omega
  have r9 : R.card = 9 := by omega
  have cross (w t : CliqueVertex D.S) (wl : P w) (tr : ¬P t) : G.Adj w t := by
    have eq := Finset.eq_of_subset_of_card_le (leftSub w wl) (show R.card ≤ (G.neighborFinset w).card by
      change R.card ≤ deg D w; rw [r9,reg])
    apply (G.mem_neighborFinset w t).mp
    rw [eq]
    exact (memR t).mpr tr
  let el : Fin 9 ≃ {x // P x} := Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_subtype]; exact l9.symm)
  let er : Fin 9 ≃ {x // ¬P x} := Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_subtype]; exact r9.symm)
  let e := (Equiv.sumCongr el er).trans (Equiv.sumCompl P)
  refine ⟨{toEquiv := e, map_rel_iff' := ?_}⟩
  rintro (i|i) (j|j)
  · change G.Adj (el i).val (el j).val ↔ _
    simp only [completeBipartiteGraph_adj,Sum.isLeft_inl,Sum.isRight_inl,Bool.false_eq_true,
      and_false,false_and,or_self,iff_false]
    exact fun h => c.valid h ((el i).property.trans (el j).property.symm)
  · change G.Adj (el i).val (er j).val ↔ _
    simpa [completeBipartiteGraph] using cross _ _ (el i).property (er j).property
  · change G.Adj (er i).val (el j).val ↔ _
    simpa [completeBipartiteGraph] using (cross _ _ (el j).property (er i).property).symm
  · change G.Adj (er i).val (er j).val ↔ _
    simpa [completeBipartiteGraph] using (show ¬G.Adj (er i).val (er j).val from
      fun h => c.valid h (sameOther _ _ (er i).property (er j).property))

/-- The point at (i,j) lies on exactly the two indicated row and column vertices. -/
theorem bipartite_light_grid (D : Family) (profile : D.n 3 = 24)
    (bip : (cliqueGraph D.S).Colorable 2) :
    ∃ e : completeBipartiteGraph (Fin 9) (Fin 9) ≃g cliqueGraph D.S,
    ∃ grid : Fin 9 × Fin 9 ≃ LightPoint D.S,
    ∀ (i j : Fin 9) (C : CliqueVertex D.S), (grid (i,j)).val ∈ C.val ↔ C = e (Sum.inl i) ∨ C = e (Sum.inr j) := by
  classical
  obtain ⟨e⟩ := bipartite_nine_iso D profile bip
  obtain ⟨f,mem⟩ := edge_realization D.S D.good D.size D.noOne
  let edge (ij : Fin 9 × Fin 9) : (cliqueGraph D.S).edgeSet :=
    ⟨s(e (Sum.inl ij.1), e (Sum.inr ij.2)),(cliqueGraph D.S).mem_edgeSet.mpr
      (e.map_adj_iff.mpr (by simp [completeBipartiteGraph]))⟩
  let cell (ij : Fin 9 × Fin 9) : LightPoint D.S := f.symm (edge ij)
  have belongs (ij : Fin 9 × Fin 9) (C : CliqueVertex D.S) :
      (cell ij).val ∈ C.val ↔ C = e (Sum.inl ij.1) ∨ C = e (Sum.inr ij.2) := by
    rw [← mem]
    dsimp only [cell]
    rw [f.apply_symm_apply]
    exact Sym2.mem_iff
  have inj : Function.Injective cell := by
    intro ij ab eq
    have left := (belongs ij (e (Sum.inl ij.1))).mpr (Or.inl rfl)
    have right := (belongs ij (e (Sum.inr ij.2))).mpr (Or.inr rfl)
    rw [eq] at left right
    obtain l|l := (belongs ab _).mp left
    · obtain r|r := (belongs ab _).mp right
      · cases e.injective r
      · exact Prod.ext (Sum.inl.inj (e.injective l)) (Sum.inr.inj (e.injective r))
    · cases e.injective l
  have size := (all_threes_counts D profile).1
  have card : Fintype.card (Fin 9 × Fin 9) = Fintype.card (LightPoint D.S) := by
    rw [← Nat.card_eq_fintype_card (α := LightPoint D.S),size]
    simp
  exact ⟨e,Equiv.ofBijective cell ((Fintype.bijective_iff_injective_and_card cell).mpr ⟨inj,card⟩),
    fun i j => belongs (i,j)⟩

end Order12.Local139

end

/- Component Erdos723.Local139.GridTriples. -/
section

/- Classification of heavy vectors in the edge coordinates of the complete bipartite graph K₉,₉. -/

namespace Order12.Bipartite139

open Finset

inductive Axis where
  | row
  | col
  deriving DecidableEq, Repr

instance : Fintype Axis := ⟨{.row, .col}, fun a => by cases a <;> simp⟩

/-- An actual coordinate vector is the indicated triple, possibly reflected in the light span. -/
structure HeavyTriple where
  axis : Axis
  reflected : Bool
  support : Finset (Fin 9)
  card_support : support.card = 3
  deriving DecidableEq

def indicator (s : Finset (Fin 9)) (i : Fin 9) : ℝ := if i ∈ s then 1 else 0

namespace HeavyTriple

noncomputable def shift (h : HeavyTriple) : ℝ := if h.reflected then 1 / 3 else 0

noncomputable def rowValue (h : HeavyTriple) (i : Fin 9) : ℝ :=
  match h.axis with
  | .row => indicator h.support i - h.shift
  | .col => h.shift

noncomputable def colValue (h : HeavyTriple) (j : Fin 9) : ℝ :=
  match h.axis with
  | .row => h.shift
  | .col => indicator h.support j - h.shift

/-- All 81 inner products with the light columns are unchanged by the reflection choice. -/
theorem edge_sum (h : HeavyTriple) (i j : Fin 9) :
    h.rowValue i + h.colValue j = match h.axis with
      | .row => indicator h.support i
      | .col => indicator h.support j := by
  cases a : h.axis <;> simp [rowValue, colValue, a]

end HeavyTriple

@[simp] lemma sum_indicator (s : Finset (Fin 9)) : ∑ i, indicator s i = (s.card : ℝ) := by
  simp [indicator]

/-- Binary additive edge data with a nonconstant row coordinate forces a constant column coordinate. -/
private lemma column_constant (x y : Fin 9 → ℝ)
    (bits : ∀ i j, x i + y j = 0 ∨ x i + y j = 1)
    (vary : ¬ ∀ i, x i = x 0) : ∀ j, y j = y 0 := by
  obtain ⟨a,ha⟩ := not_forall.mp vary
  intro j
  rcases bits a j with a1|a1 <;> rcases bits 0 j with b1|b1 <;>
    rcases bits a 0 with a0|a0 <;> rcases bits 0 0 with b0|b0 <;> grind

private lemma constant_half (x y : Fin 9 → ℝ)
    (bits : ∀ i j, x i + y j = 0 ∨ x i + y j = 1)
    (total : ∑ i, ∑ j, (x i + y j) = 27)
    (length : (∑ i, (x i)^2) + ∑ j, (y j)^2 = 3)
    (constant : ∀ j, y j = y 0) :
    ∃ (s : Finset (Fin 9)) (r : Bool), s.card = 3 ∧
      (∀ i, x i = indicator s i - (if r then 1/3 else 0)) ∧
      ∀ j, y j = (if r then 1/3 else 0) := by
  classical
  let t := y 0
  let s := univ.filter (fun i => x i + t = 1)
  have mark (i) : x i + t = indicator s i := by
    rcases bits i 0 with e|e
    · have hz : x i + t = 0 := e
      simp [indicator,s,hz]
    · have ho : x i + t = 1 := e
      simp [indicator,s,ho]
  have xv (i) : x i = indicator s i - t := by linarith [mark i]
  have yv (j) : y j = t := constant j
  have sum : (27 : ℝ) = 9 * ∑ i, indicator s i := by
    calc
      27 = ∑ i, ∑ j, (x i + y j) := total.symm
      _ = ∑ i, ∑ _ : Fin 9, indicator s i := by
        apply sum_congr rfl
        intro i _
        exact sum_congr rfl fun j _ => by rw [yv j,mark i]
      _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        rw [← mul_sum]
  rw [sum_indicator] at sum
  have sg : (s.card : ℝ) = 3 := by linarith
  have sc : s.card = 3 := by exact_mod_cast sg
  have squared (i) : (x i)^2 = (1-2*t) * indicator s i + t^2 := by
    rw [xv]
    by_cases h : i ∈ s <;> simp [indicator,h]
    ring
  have len : (1-2*t)*(s.card : ℝ) + 9*t^2 + 9*t^2 = 3 := by
    calc
      _ = (∑ i, ((1-2*t)*indicator s i + t^2)) + ∑ _ : Fin 9, t^2 := by
        rw [sum_add_distrib, ← mul_sum, sum_indicator]
        simp
      _ = _ := by simpa only [squared, yv] using length
  rw [sg] at len
  have zero : t * (3 * t - 1) = 0 := by nlinarith [len]
  rcases mul_eq_zero.mp zero with h|h
  · exact ⟨s,false,sc,fun i => by simpa [h] using xv i,fun j => by simpa [h] using yv j⟩
  · have tv : t = 1/3 := by linarith
    exact ⟨s,true,sc,fun i => by simpa [tv] using xv i,fun j => by simpa [tv] using yv j⟩

/-- Per-vector classification, with the number of light gaps supplied as their binary sum. -/
theorem normal_form_of_sum (x y : Fin 9 → ℝ)
    (bits : ∀ i j, x i + y j = 0 ∨ x i + y j = 1)
    (total : ∑ i, ∑ j, (x i + y j) = 27)
    (length : (∑ i, (x i)^2) + ∑ j, (y j)^2 = 3) :
    ∃ h : HeavyTriple, (∀ i, x i = h.rowValue i) ∧ ∀ j, y j = h.colValue j := by
  by_cases same : ∀ i, x i = x 0
  · have swap : ∑ i, ∑ j, (y i + x j) = 27 := by
      rw [sum_comm]
      simpa only [add_comm] using total
    obtain ⟨s,r,card,ys,xs⟩ := constant_half y x (fun i j => by simpa only [add_comm] using bits j i)
      swap (by simpa only [add_comm] using length) same
    exact ⟨⟨.col,r,s,card⟩,xs,ys⟩
  · obtain ⟨s,r,card,xs,ys⟩ := constant_half x y bits total length (column_constant x y bits same)
    exact ⟨⟨.row,r,s,card⟩,xs,ys⟩

/-- A norm-three vector meeting exactly 27 of the 81 light edges has one of the four forms. -/
theorem normal_form (x y : Fin 9 → ℝ)
    (bits : ∀ i j, x i + y j = 0 ∨ x i + y j = 1)
    (ones : (univ.filter (fun k : Fin 9 × Fin 9 => x k.1 + y k.2 = 1)).card = 27)
    (length : (∑ i, (x i)^2) + ∑ j, (y j)^2 = 3) :
    ∃ h : HeavyTriple, (∀ i, x i = h.rowValue i) ∧ ∀ j, y j = h.colValue j := by
  classical
  apply normal_form_of_sum x y bits _ length
  rw [← Fintype.sum_prod_type (fun k : Fin 9 × Fin 9 => x k.1 + y k.2)]
  calc
    _ = ∑ k : Fin 9 × Fin 9, if x k.1 + y k.2 = 1 then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro k _
      rcases bits k.1 k.2 with e|e <;> simp [e]
    _ = ((univ.filter (fun k : Fin 9 × Fin 9 => x k.1 + y k.2 = 1)).card : ℝ) := by simp
    _ = 27 := by rw [ones]; norm_num

private lemma not_constant_indicator (s : Finset (Fin 9)) (size : s.card = 3) (c : ℝ)
    (binary : c = 0 ∨ c = 1) : ¬ ∀ i, indicator s i = c := by
  intro constant
  have h : (∑ i, indicator s i) = ∑ _ : Fin 9, c := sum_congr rfl fun i _ => constant i
  rw [sum_indicator,size] at h
  rcases binary with e|e <;> norm_num [e] at h

private lemma indicator_ext {s t : Finset (Fin 9)}
    (same : ∀ i, indicator s i = indicator t i) : s = t := by
  ext i
  have eq := same i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [indicator]

/-- The axis, reflection flag and triple are determined by the actual vector coordinates. -/
theorem HeavyTriple.ext_values {h k : HeavyTriple}
    (rows : ∀ i, h.rowValue i = k.rowValue i) (cols : ∀ j, h.colValue j = k.colValue j) : h = k := by
  have edges (i j : Fin 9) := (h.edge_sum i j).symm.trans
    ((congrArg₂ (· + ·) (rows i) (cols j)).trans (k.edge_sum i j))
  have bit (s : Finset (Fin 9)) (i : Fin 9) : indicator s i = 0 ∨ indicator s i = 1 := by
    by_cases hi : i ∈ s <;> simp [indicator,hi]
  have sameAxis : h.axis = k.axis := by
    cases a : h.axis <;> cases b : k.axis <;> first | rfl | skip
    · simpa only [a,b] using (not_constant_indicator h.support h.card_support
        (indicator k.support 0) (bit _ _) (fun i => by simpa only [a,b] using edges i 0)).elim
    · simpa only [a,b] using (not_constant_indicator h.support h.card_support
        (indicator k.support 0) (bit _ _) (fun j => by simpa only [a,b] using edges 0 j)).elim
  have supports : h.support = k.support := by
    apply indicator_ext
    intro i
    cases a : h.axis <;> simpa only [← sameAxis,a] using edges i i
  have shifts : h.shift = k.shift := by
    cases a : h.axis
    · simpa only [HeavyTriple.colValue,← sameAxis,a] using cols 0
    · simpa only [HeavyTriple.rowValue,← sameAxis,a] using rows 0
  have flags : h.reflected = k.reflected := by
    cases a : h.reflected <;> cases b : k.reflected <;> first | rfl | norm_num [HeavyTriple.shift,a,b] at shifts
  cases h
  cases k
  simp_all

end Order12.Bipartite139

end

/- Component Erdos723.Local139.GridModel. -/
section

/- Coordinate data and incidence counts for the twenty-four degree-ten points. -/

namespace Order12.Bipartite139

open Profile139 Local139 Finset
open scoped Matrix
open scoped Classical

abbrev HeavyPoint (D : Family) := {p : Pt // D.t p = 3}
abbrev GridAxis := Fin 9 ⊕ Fin 9
abbrev Cell := Fin 9 × Fin 9

def oldHeavy (D : Family) (b : D.S) : Finset (HeavyPoint D) :=
  univ.filter (fun x => x.val ∈ b.val)

structure GridCoordinates (D : Family) where
  cell : Cell ≃ LightPoint D.S
  W : Matrix GridAxis Pt ℝ
  triple : HeavyPoint D → HeavyTriple
  gram : Wᵀ * W = Gram139.gap D.S
  full : ∀ p, D.t p = 0 → ∀ a, W a p = 0
  lightRow : ∀ i j k, W (.inl k) (cell (i,j)).val = if k = i then 1 else 0
  lightCol : ∀ i j k, W (.inr k) (cell (i,j)).val = if k = j then 1 else 0
  heavyRow : ∀ x i, W (.inl i) x.val = (triple x).rowValue i
  heavyCol : ∀ x j, W (.inr j) x.val = (triple x).colValue j
  cell_sum : ∀ p i j, W (.inl i) p + W (.inr j) p = Gram139.gap D.S p (cell (i,j)).val
  column_sum : ∀ p, (∑ a, W a p) = (D.t p : ℝ)
  line_sum : ∀ (b : D.S) a, (∑ p ∈ b.val, W a p) = 1

def GridCoordinates.oldLight {D : Family} (g : GridCoordinates D) (b : D.S) : Finset Cell :=
  univ.filter (fun ij => (g.cell ij).val ∈ b.val)

theorem profile_types (D : Family) (profile : D.n 3 = 24) (p : Pt) :
    D.t p = 0 ∨ D.t p = 2 ∨ D.t p = 3 := by
  have table := D.all_profiles
  dsimp only at table
  simp only [Prod.mk.injEq] at table
  have exclude (k : ℤ) (absent : D.n k = 0) : D.t p ≠ k := by
    intro eq
    have pos : 0 < (D.level k).card := card_pos.mpr ⟨p,Family.mem_level.mpr eq⟩
    rw [D.n_eq] at absent
    omega
  have four := exclude 4 (by omega)
  have five := exclude 5 (by omega)
  have six := exclude 6 (by omega)
  have := D.bound p
  omega

theorem heavy_gap_count (D : Family) (profile : D.n 3 = 24) (p : Pt) :
    (((holes D.S p).filter (fun q => D.t q = 3)).card : ℤ) = D.t p * (6 - D.t p) := by
  have extra := deficit_holes_sum D.S D.good p
  change (∑ q ∈ holes D.S p, (D.t q - 2)) = D.t p * (145 - (D.S.card : ℤ) - D.t p) at extra
  rw [D.size] at extra
  change (∑ q ∈ holes D.S p, (D.t q - 2)) = D.t p * (6 - D.t p) at extra
  rw [← extra, natCast_card_filter]
  apply sum_congr rfl
  intro q hq
  have poss := profile_types D profile q
  have low := D.hole_lower hq
  split <;> omega

private theorem count_subtype {A : Type*} [Fintype A] [DecidableEq A] (P : A → Prop)
    [DecidablePred P] (s : Finset A) :
    (univ.filter (fun p : {x // P x} => p.val ∈ s)).card = (s.filter P).card := by
  apply card_bij (fun p _ => p.val)
  · intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).2,p.property⟩
  · exact fun _ _ _ _ e => Subtype.ext e
  · intro y hy
    obtain ⟨ys, yp⟩ := mem_filter.mp hy
    exact ⟨⟨y,yp⟩,mem_filter.mpr ⟨mem_univ _,ys⟩,rfl⟩

theorem count_heavy_hits (D : Family) (p : Pt) :
    (univ.filter (fun x : HeavyPoint D => x.val ∈ holes D.S p)).card =
      ((holes D.S p).filter (fun q => D.t q = 3)).card :=
  count_subtype (fun q => D.t q = 3) _

theorem heavy_light_hits (D : Family) (profile : D.n 3 = 24) (x : HeavyPoint D) :
    (univ.filter (fun p : LightPoint D.S => p.val ∈ holes D.S x.val)).card = 27 := by
  classical
  rw [count_subtype (Light D.S)]
  have deg : (through D.S x.val).card = 10 := by
    have := x.property
    unfold Family.t deficit at this
    omega
  have hc := holes_card D.S D.good x.val
  rw [deg] at hc
  have heavy := heavy_gap_count D profile x.val
  rw [x.property] at heavy
  have part := card_filter_add_card_filter_not (s := holes D.S x.val) (Light D.S)
  have same : (holes D.S x.val).filter (fun p => ¬ Light D.S p) =
      (holes D.S x.val).filter (fun p => D.t p = 3) := by
    apply filter_congr
    intro p hp
    rw [light_iff_deficit_two]
    have := profile_types D profile p
    have := D.hole_lower hp
    omega
  rw [same] at part
  omega

end Order12.Bipartite139

end

/- Component Erdos723.Local139.BuildGrid. -/
section

/- Realize every part of the bipartite model from the labeled clique graph. -/

namespace Order12.Bipartite139

open Profile139 Local139 Finset
open scoped Matrix
open scoped Classical

theorem HeavyTriple.total (h : HeavyTriple) :
    (∑ i, h.rowValue i) + (∑ j, h.colValue j) = 3 := by
  cases a : h.axis <;> simp [rowValue,colValue,a,sum_sub_distrib,h.card_support]

/-- Full row rank and the point-coordinate sums determine all old-line sums. -/
theorem line_sum_of_column_sum (D : Family) (W : Matrix GridAxis Pt ℝ)
    (gram : Wᵀ * W = Gram139.gap D.S) (column : ∀ p, (∑ a, W a p) = (D.t p : ℝ))
    (b : D.S) (a : GridAxis) : (∑ p ∈ b.val, W a p) = 1 := by
  classical
  have rk := Matrix.rank_transpose_mul_self W
  rw [gram, (Gram139.gap139 D.S D.good D.size).2] at rk
  have inj : Function.Injective Wᵀ.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have dim := LinearMap.finrank_range_add_finrank_ker Wᵀ.mulVecLin
    change Wᵀ.rank + _ = _ at dim
    have card : Fintype.card GridAxis = 18 := by decide
    rw [Matrix.rank_transpose, ← rk, Module.finrank_pi, card] at dim
    exact Nat.add_left_cancel (show 18 + Module.finrank ℝ (LinearMap.ker Wᵀ.mulVecLin) = 18 + 0 from dim)
  have cols : Wᵀ * Gram139.ones GridAxis D.S = Matrix.of (fun p _ => (D.t p : ℝ)) := by
    ext p _
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Gram139.ones,Matrix.of_apply,mul_one]
      using column p
  have eq : Wᵀ * (W * (Gram139.incidence D.S)ᵀ) = Wᵀ * Gram139.ones GridAxis D.S := by
    rw [← Matrix.mul_assoc,gram,Gram139.gap_mul_incidence_transpose D.S D.good,cols]
  have fe : Wᵀ.mulVecLin ((W * (Gram139.incidence D.S)ᵀ).col b) =
      Wᵀ.mulVecLin ((Gram139.ones GridAxis D.S).col b) := congrArg (fun T => T.col b) eq
  have entry := congrFun (inj fe) a
  change (W * (Gram139.incidence D.S)ᵀ) a b = 1 at entry
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Gram139.incidence,Matrix.of_apply,
    mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_inter,univ_inter] using entry

/-- A labeling of the canonical cliques by the two axes produces the actual
triple of every heavy point, along with its coordinates on every old line. -/
theorem gridCoordinates_of_labels (D : Family) (profile : D.n 3 = 24)
    (e : completeBipartiteGraph (Fin 9) (Fin 9) ≃g cliqueGraph D.S)
    (grid : Cell ≃ LightPoint D.S)
    (label : ∀ i j (C : CliqueVertex D.S), (grid (i,j)).val ∈ C.val ↔
      C = e (.inl i) ∨ C = e (.inr j)) : Nonempty (GridCoordinates D) := by
  classical
  have count : Nat.card (CliqueVertex D.S) = 18 := by
    rw [← Nat.card_congr e.toEquiv]
    norm_num
  obtain ⟨V,vg,_,vc⟩ := clique_coordinates D.S D.good D.size D.noOne count
  let W : Matrix GridAxis Pt ℝ := V.submatrix e.toEquiv id
  have wg : Wᵀ * W = Gram139.gap D.S := by
    change Vᵀ.submatrix id e.toEquiv * V.submatrix e.toEquiv id = _
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id,vg]
  have squares (p : Pt) : (∑ a, (W a p)^2) = (D.t p : ℝ) := by
    have eq := congrArg (fun A : Matrix Pt Pt ℝ => A p p) wg
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← sq, Gram139.gap_entry D.S D.good, if_true] using eq
  have lr (i j k : Fin 9) : W (.inl k) (grid (i,j)).val = if k=i then 1 else 0 := by
    change V (e (.inl k)) (grid (i,j)).val = _
    simp [vc, label, e.injective.eq_iff]
  have lc (i j k : Fin 9) : W (.inr k) (grid (i,j)).val = if k=j then 1 else 0 := by
    change V (e (.inr k)) (grid (i,j)).val = _
    simp [vc, label, e.injective.eq_iff]
  have es (p : Pt) (i j : Fin 9) :
      W (.inl i) p + W (.inr j) p = Gram139.gap D.S p (grid (i,j)).val := by
    apply coordinate_edge_sum D.S D.good D.size D.noOne V vg vc (e (.inl i)) (e (.inr j))
      (fun eq => Sum.inl_ne_inr (e.injective eq)) (grid (i,j))
    · exact (label i j _).mpr (Or.inl rfl)
    · exact (label i j _).mpr (Or.inr rfl)
  have edgeValue (x : HeavyPoint D) (ij : Cell) :
      W (.inl ij.1) x.val + W (.inr ij.2) x.val =
        if (grid ij).val ∈ holes D.S x.val then 1 else 0 := by
    obtain ⟨i,j⟩ := ij
    rw [es,Gram139.gap_entry D.S D.good,if_neg]
    intro eq
    have lh := (light_iff_deficit_two (D := D)).mp (grid (i,j)).property
    have := x.property
    rw [← eq] at lh
    omega
  have forms (x : HeavyPoint D) : ∃ t : HeavyTriple,
      (∀ i, W (.inl i) x.val = t.rowValue i) ∧ (∀ j, W (.inr j) x.val = t.colValue j) := by
    apply normal_form
    · intro i j
      rw [edgeValue x (i,j)]
      split <;> simp
    · calc
        _ = (univ.filter (fun p : LightPoint D.S => p.val ∈ holes D.S x.val)).card := by
          apply card_bij (fun ij _ => grid ij)
          · intro ij hij
            apply mem_filter.mpr
            refine ⟨mem_univ _,?_⟩
            by_contra miss
            have yes := (mem_filter.mp hij).2
            change W (.inl ij.1) x.val + W (.inr ij.2) x.val = 1 at yes
            rw [edgeValue,if_neg miss] at yes
            norm_num at yes
          · exact fun _ _ _ _ h => grid.injective h
          · intro p hp
            obtain ⟨ij, rfl⟩ := grid.surjective p
            exact ⟨ij,mem_filter.mpr ⟨mem_univ _,(edgeValue x ij).trans (if_pos (mem_filter.mp hp).2)⟩,rfl⟩
        _ = 27 := heavy_light_hits D profile x
    · have eq := squares x.val
      rw [Fintype.sum_sum_type,x.property] at eq
      simpa only [Int.cast_ofNat] using eq
  choose t hr hc using forms
  have full (p : Pt) (hp : D.t p = 0) (a : GridAxis) : W a p = 0 := by
    have all := squares p
    rw [hp,Int.cast_zero] at all
    have z := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ univ) => sq_nonneg (W i p))).mp all a (mem_univ _)
    exact sq_eq_zero_iff.mp z
  have column (p : Pt) : (∑ a, W a p) = (D.t p : ℝ) := by
    rcases profile_types D profile p with zero | two | three
    · simp [full p zero,zero]
    · have lp : Light D.S p := light_iff_deficit_two.mpr two
      obtain ⟨⟨i,j⟩,eq⟩ := grid.surjective ⟨p,lp⟩
      have pe : (grid (i,j)).val = p := congrArg Subtype.val eq
      have rows (k : Fin 9) : W (.inl k) p = if k=i then 1 else 0 := pe ▸ lr i j k
      have cols (k : Fin 9) : W (.inr k) p = if k=j then 1 else 0 := pe ▸ lc i j k
      rw [Fintype.sum_sum_type,two]
      norm_num [rows,cols]
    · let x : HeavyPoint D := ⟨p,three⟩
      rw [Fintype.sum_sum_type,three]
      change (∑ i, W (.inl i) x.val) + ∑ j, W (.inr j) x.val = (3 : ℝ)
      simp only [hr, hc]
      exact (t x).total
  exact ⟨⟨grid,W,t,wg,full,lr,lc,hr,hc,es,column,line_sum_of_column_sum D W wg column⟩⟩

end Order12.Bipartite139

end

/- Component Erdos723.Local139.GridLineSums. -/
section

/- The coordinate sums on an old line split into its grid cells and its triples. -/

namespace Order12.Bipartite139.GridCoordinates

open Profile139 Local139 Finset
open scoped Classical

private theorem sum_at_subtype (s : Finset Pt) (P : Pt → Prop) [DecidablePred P] (f : Pt → ℝ) :
    (∑ x ∈ s, if P x then f x else 0) =
      ∑ x ∈ univ.filter (fun x : {q // P q} => x.val ∈ s), f x.val := by
  classical
  rw [← sum_filter]
  symm
  apply sum_bij (fun x _ => x.val)
  · exact fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).2,x.property⟩
  · exact fun _ _ _ _ h => Subtype.ext h
  · intro q hq
    obtain ⟨hit,hP⟩ := mem_filter.mp hq
    exact ⟨⟨q,hP⟩,mem_filter.mpr ⟨mem_univ _,hit⟩,rfl⟩
  · intros; rfl

private theorem line_parts {D : Family} (g : GridCoordinates D) (profile : D.n 3 = 24)
    (b : D.S) (a : GridAxis) :
    (∑ ij ∈ g.oldLight b, g.W a (g.cell ij).val) +
      (∑ h ∈ oldHeavy D b, g.W a h.val) = 1 := by
  have via : (∑ ij ∈ g.oldLight b, g.W a (g.cell ij).val) =
      ∑ l ∈ univ.filter (fun l : LightPoint D.S => l.val ∈ b.val), g.W a l.val := by
    apply sum_bij (fun ij _ => g.cell ij)
    · exact fun ij hij => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hij).2⟩
    · exact fun _ _ _ _ h => g.cell.injective h
    · intro l hl
      obtain ⟨ij,rfl⟩ := g.cell.surjective l
      exact ⟨ij,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hl).2⟩,rfl⟩
    · intros; rfl
  rw [via,← g.line_sum b a,← sum_at_subtype b.val (Light D.S) (g.W a)]
  unfold oldHeavy
  rw [← sum_at_subtype b.val (fun p => D.t p = 3) (g.W a), ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  have iff := light_iff_deficit_two (D := D) (p := p)
  rcases profile_types D profile p with zero | two | three
  · have notLight : ¬ Light D.S p := fun h => by have := iff.mp h; omega
    simp [notLight,zero,g.full p zero a]
  · simp [iff.mpr two,two]
  · have notLight : ¬ Light D.S p := fun h => by have := iff.mp h; omega
    simp [notLight,three]

theorem line_rows {D : Family} (g : GridCoordinates D) (profile : D.n 3 = 24) (b : D.S) (i : Fin 9) :
    (((g.oldLight b).filter (fun ij => ij.1 = i)).card : ℝ) +
      (∑ h ∈ oldHeavy D b, (g.triple h).rowValue i) = 1 := by
  have eq := line_parts g profile b (.inl i)
  have each (ij : Cell) : g.W (.inl i) (g.cell ij).val = if ij.1 = i then 1 else 0 := by
    obtain ⟨j,k⟩ := ij
    rw [g.lightRow]
    by_cases h : i = j <;> simp [h, eq_comm]
  simpa only [each, sum_boole, g.heavyRow] using eq

theorem line_cols {D : Family} (g : GridCoordinates D) (profile : D.n 3 = 24) (b : D.S) (i : Fin 9) :
    (((g.oldLight b).filter (fun ij => ij.2 = i)).card : ℝ) +
      (∑ h ∈ oldHeavy D b, (g.triple h).colValue i) = 1 := by
  have eq := line_parts g profile b (.inr i)
  have each (ij : Cell) : g.W (.inr i) (g.cell ij).val = if ij.2 = i then 1 else 0 := by
    obtain ⟨j,k⟩ := ij
    rw [g.lightCol]
    by_cases h : i = k <;> simp [h, eq_comm]
  simpa only [each, sum_boole, g.heavyCol] using eq

theorem eight {D : Family} (g : GridCoordinates D) (profile : D.n 3 = 24) (i j : Fin 9) :
    (∑ x, ((g.triple x).rowValue i + (g.triple x).colValue j)) = 8 := by
  let l := g.cell (i,j)
  have two : D.t l.val = 2 := light_iff_deficit_two.mp l.property
  have each (x : HeavyPoint D) : (g.triple x).rowValue i + (g.triple x).colValue j =
      if x.val ∈ holes D.S l.val then 1 else 0 := by
    have ne : x.val ≠ l.val := by intro eq; have := x.property; rw [eq,two] at this; omega
    rw [← g.heavyRow,← g.heavyCol,g.cell_sum,Gram139.gap_entry D.S D.good]
    change (if x.val = l.val then _ else if l.val ∈ holes D.S x.val then 1 else 0) = _
    simp only [if_neg ne, holes_symm D.S x.val l.val]
  simp only [each,sum_boole,count_heavy_hits]
  have n := heavy_gap_count D profile l.val
  rw [two] at n
  norm_num at n
  exact_mod_cast n

end Order12.Bipartite139.GridCoordinates

end

/- Component Erdos723.Local139.LineBalance. -/
section

/- The true coordinate sum on an old line determines the possible row and column triple counts. -/

namespace Order12.K99Counts

/-- A balanced old line or one of the two exceptional orientations. -/
def Pattern (r c mr mc : ℕ) : Prop :=
  (r = c ∧ mr = mc) ∨ (r = 6 ∧ c = 0 ∧ mr = 3 ∧ mc = 0) ∨
    (r = 0 ∧ c = 6 ∧ mr = 0 ∧ mc = 3)

/-- Every uncorrected coordinate on either axis counts contributions from the lights and the
binary heavy triples. Reflection adds one third times the signed difference of reflected
triple counts to each row and subtracts this number from each column. -/
theorem line_pattern (l r c mr mc : ℕ) (row col : Fin 9 → ℕ)
    (rowTotals : ∑ i, row i = l + 3*r) (colTotals : ∑ i, col i = l + 3*c)
    (mrle : mr ≤ r) (mcle : mc ≤ c)
    (rowSum : ∀ i, (row i : ℝ) + ((mc : ℝ) - mr)/3 = 1)
    (colSum : ∀ i, (col i : ℝ) - ((mc : ℝ) - mr)/3 = 1) :
    (r+c = 0 ∨ r+c = 2 ∨ r+c = 4 ∨ r+c = 6) ∧ Pattern r c mr mc := by
  have roweq (i : Fin 9) : (3 : ℤ) * row i + mc - mr = 3 := by
    exact_mod_cast (show (3 : ℝ) * row i + mc - mr = 3 by linarith [rowSum i])
  have coleq (i : Fin 9) : (3 : ℤ) * col i - mc + mr = 3 := by
    exact_mod_cast (show (3 : ℝ) * col i - mc + mr = 3 by linarith [colSum i])
  have hr (i : Fin 9) (_ : i ∈ Finset.univ) : row i = row 0 := by
    have := roweq i; have := roweq 0; omega
  have hc (i : Fin 9) (_ : i ∈ Finset.univ) : col i = col 0 := by
    have := coleq i; have := coleq 0; omega
  rw [Finset.sum_const_nat hr] at rowTotals
  rw [Finset.sum_const_nat hc] at colTotals
  simp only [Finset.card_univ,Fintype.card_fin] at rowTotals colTotals
  have r0 := roweq 0
  have c0 := coleq 0
  unfold Pattern
  omega

end Order12.K99Counts

end

/- Component Erdos723.Local139.GridCounts. -/
section

/- Double counting heavy incidences on old lines in the bipartite nine-regular case. -/

namespace Order12.K99Counts

open Finset

variable {H B : Type*} [Fintype H] [Fintype B] [DecidableEq H]

omit [Fintype H] in
/-- Reverse the order of counting old lines and heavy points with a line-dependent weight. -/
private lemma weighted_count (on : B → Finset H) (A : Finset H) (w : B → ℕ) :
    ∑ b, (on b ∩ A).card * w b =
      ∑ h ∈ A, ∑ b, if h ∈ on b then w b else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.sum_const,nsmul_eq_mul,Finset.inter_comm,Nat.cast_id]

omit [Fintype H] in
private lemma old_incidence (on : B → Finset H)
    (degree : ∀ h, (univ.filter (fun b => h ∈ on b)).card = 10)
    (A : Finset H) : ∑ b, (on b ∩ A).card = A.card * 10 := by
  classical
  have flip := weighted_count on A (fun _ => 1)
  simp only [mul_one,Finset.sum_boole, Nat.cast_id,degree] at flip
  simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using flip

omit [Fintype H] in
/-- The fourteen old-collinear partners of any heavy point may be counted on its ten old
lines. Distinct old lines containing that point have disjoint sets of other partners. -/
theorem encounter_sum (on : B → Finset H) (p : H)
    (apart : ∀ b c : B, b ≠ c → p ∈ on b → p ∈ on c → (on b ∩ on c) ⊆ {p})
    (fourteen : ((univ.filter (fun b => p ∈ on b)).biUnion (fun b => (on b).erase p)).card = 14) :
    (∑ b, if p ∈ on b then (on b).card - 1 else 0) = 14 := by
  classical
  let U := univ.filter fun b => p ∈ on b
  have sep : (↑U : Set B).PairwiseDisjoint (fun b => (on b).erase p) := by
    intro b hb c hc ne
    apply Finset.disjoint_left.mpr
    intro y yb yc
    obtain ⟨yp,yb⟩ := mem_erase.mp yb
    exact yp (mem_singleton.mp (apart b c ne (mem_filter.mp hb).2 (mem_filter.mp hc).2
      (mem_inter.mpr ⟨yb,(mem_erase.mp yc).2⟩)))
  change (U.biUnion _).card = 14 at fourteen
  rw [Finset.card_biUnion sep] at fourteen
  rw [← Finset.sum_filter]
  exact (Finset.sum_congr rfl (fun b hb => (card_erase_of_mem (mem_filter.mp hb).2).symm)).trans fourteen

/-- Counting heavy incidences and ordered old-collinear pairs gives b₄ + 3b₆ = 12. -/
theorem line_histogram (on : B → Finset H) (size : Fintype.card H = 24)
    (degree : ∀ h, (univ.filter (fun b => h ∈ on b)).card = 10)
    (partners : ∀ h, (∑ b, if h ∈ on b then (on b).card - 1 else 0) = 14)
    (sizes : ∀ b, (on b).card = 0 ∨ (on b).card = 2 ∨ (on b).card = 4 ∨ (on b).card = 6) :
    (univ.filter (fun b => (on b).card = 4)).card + 3 * (univ.filter (fun b => (on b).card = 6)).card = 12 := by
  classical
  have incid := old_incidence on degree univ
  simp only [inter_univ,card_univ,size] at incid
  have moment := weighted_count on univ (fun b => (on b).card - 1)
  simp only [inter_univ,partners,Finset.sum_const,nsmul_eq_mul,card_univ,size,Nat.cast_id] at moment
  have each (b : B) (_ : b ∈ univ) :
      (on b).card + (if (on b).card = 4 then 8 else 0) + (if (on b).card = 6 then 24 else 0) =
        (on b).card * ((on b).card-1) := by
    rcases sizes b with h | h | h | h <;> norm_num [h]
  have total := Finset.sum_congr rfl each
  simp only [sum_add_distrib,← sum_filter,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,incid,moment] at total
  omega

/-- At most four old lines contain six heavy points. -/
theorem six_line_bound (on : B → Finset H) (size : Fintype.card H = 24)
    (degree : ∀ h, (univ.filter (fun b => h ∈ on b)).card = 10)
    (partners : ∀ h, (∑ b, if h ∈ on b then (on b).card - 1 else 0) = 14)
    (sizes : ∀ b, (on b).card = 0 ∨ (on b).card = 2 ∨ (on b).card = 4 ∨ (on b).card = 6) :
    (univ.filter (fun b => (on b).card = 6)).card ≤ 4 := by
  have hist := line_histogram on size degree partners sizes
  omega

/-- The row and column sets have size twelve, their reflected subsets have equal sizes, and
the squared old-line signed sums of reflected triples total at most 36. -/
theorem balance (on : B → Finset H) (R M : Finset H) (size : Fintype.card H = 24)
    (degree : ∀ h, (univ.filter (fun b => h ∈ on b)).card = 10)
    (six : (univ.filter (fun b => (on b).card = 6)).card ≤ 4)
    (pattern : ∀ b, Pattern (on b ∩ R).card (on b ∩ Rᶜ).card
      (on b ∩ (R ∩ M)).card (on b ∩ (Rᶜ ∩ M)).card) :
    R.card = 12 ∧ Rᶜ.card = 12 ∧ (R ∩ M).card = (Rᶜ ∩ M).card ∧
    ∑ b, (((on b ∩ (R ∩ M)).card : ℝ) - (on b ∩ (Rᶜ ∩ M)).card)^2 ≤ 36 := by
  classical
  let r (b : B) := (on b ∩ R).card
  let c (b : B) := (on b ∩ Rᶜ).card
  let mr (b : B) := (on b ∩ (R ∩ M)).card
  let mc (b : B) := (on b ∩ (Rᶜ ∩ M)).card
  let er (b : B) : ℕ := if r b > c b then 1 else 0
  let ec (b : B) : ℕ := if c b > r b then 1 else 0
  have covers (b : B) : r b + c b = (on b).card := by
    have part := Finset.card_sdiff_add_card_inter (on b) R
    have eq : on b \ R = on b ∩ Rᶜ := by ext; simp
    rw [eq] at part
    exact (Nat.add_comm _ _).trans part
  have line (b : B) : (r b = c b ∧ mr b = mc b) ∨
      (r b = 6 ∧ c b = 0 ∧ mr b = 3 ∧ mc b = 0) ∨
      (r b = 0 ∧ c b = 6 ∧ mr b = 0 ∧ mc b = 3) := pattern b
  have localSums (b : B) :
      r b + 6 * ec b = c b + 6 * er b ∧ mr b + 3*ec b = mc b + 3*er b ∧
      er b + ec b ≤ (if (on b).card=6 then 1 else 0) ∧
      ((mr b : ℝ) - mc b)^2 ≤ (if (on b).card=6 then 9 else 0) := by
    rw [← covers b]
    rcases line b with ⟨h,h'⟩ | ⟨hr,hc,hm,hn⟩ | ⟨hr,hc,hm,hn⟩
    · simp [er,ec,h,h']; positivity
    · norm_num [er,ec,hr,hc,hm,hn]
    · norm_num [er,ec,hr,hc,hm,hn]
  have axis := Finset.sum_congr (s₁:=univ) rfl (fun b _ => (localSums b).1)
  have minus := Finset.sum_congr (s₁:=univ) rfl (fun b _ => (localSums b).2.1)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at axis minus
  change (∑ b, (on b ∩ R).card) + _ = (∑ b, (on b ∩ Rᶜ).card) + _ at axis
  change (∑ b, (on b ∩ (R ∩ M)).card) + _ = (∑ b, (on b ∩ (Rᶜ ∩ M)).card) + _ at minus
  rw [old_incidence on degree R,old_incidence on degree Rᶜ] at axis
  rw [old_incidence on degree (R ∩ M),old_incidence on degree (Rᶜ ∩ M)] at minus
  have cap := Finset.sum_le_sum (s:=univ) (fun b _ => (localSums b).2.2.1)
  rw [Finset.sum_add_distrib] at cap
  have small : (∑ b, er b) + (∑ b, ec b) ≤ 4 := cap.trans (by
    simpa only [Finset.sum_boole,Nat.cast_id] using six)
  have tot : R.card + Rᶜ.card = 24 := by
    have bound := card_le_univ R
    rw [size] at bound
    rw [card_compl,size]
    omega
  have energy := Finset.sum_le_sum (s:=univ) (fun b _ => (localSums b).2.2.2)
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul] at energy
  have realSix : ((univ.filter (fun b => (on b).card = 6)).card : ℝ) ≤ 4 := by exact_mod_cast six
  refine ⟨by omega,by omega,by omega,?_⟩
  exact energy.trans (by linarith)

/-- There are equally many exceptional lines in the two orientations, at most four together. -/
theorem exceptional_counts (on : B → Finset H) (R M : Finset H)
    (degree : ∀ h, (univ.filter (fun b => h ∈ on b)).card = 10)
    (axes : R.card = Rᶜ.card) (six : (univ.filter (fun b => (on b).card = 6)).card ≤ 4)
    (pattern : ∀ b, Pattern (on b ∩ R).card (on b ∩ Rᶜ).card
      (on b ∩ (R ∩ M)).card (on b ∩ (Rᶜ ∩ M)).card) :
    let ER := univ.filter (fun b => (on b ∩ R).card > (on b ∩ Rᶜ).card)
    let EC := univ.filter (fun b => (on b ∩ R).card < (on b ∩ Rᶜ).card)
    ER.card = EC.card ∧ ER.card + EC.card ≤ 4 := by
  classical
  let r (b : B) := (on b ∩ R).card
  let c (b : B) := (on b ∩ Rᶜ).card
  let er (b : B) : ℕ := if r b > c b then 1 else 0
  let ec (b : B) : ℕ := if r b < c b then 1 else 0
  have covers (b : B) : r b + c b = (on b).card := by
    have eq : on b \ R = on b ∩ Rᶜ := by ext; simp
    have h := card_sdiff_add_card_inter (on b) R
    rw [eq,add_comm] at h
    exact h
  have each (b : B) : r b + 6*ec b = c b + 6*er b ∧
      er b + ec b ≤ (if (on b).card=6 then 1 else 0) := by
    rw [← covers b]
    rcases pattern b with ⟨h,_⟩ | ⟨hr,hc,_,_⟩ | ⟨hr,hc,_,_⟩
    · change r b = c b at h
      simp [er,ec,h]
    · change r b = 6 at hr
      change c b = 0 at hc
      norm_num [er,ec,hr,hc]
    · change r b = 0 at hr
      change c b = 6 at hc
      norm_num [er,ec,hr,hc]
  have ax := sum_congr (s₁:=univ) rfl (fun b _ => (each b).1)
  have cap := sum_le_sum (s:=univ) (fun b _ => (each b).2)
  have rsum : ∑ b, r b = R.card * 10 := old_incidence on degree R
  have csum : ∑ b, c b = Rᶜ.card * 10 := old_incidence on degree Rᶜ
  simp only [sum_add_distrib,← mul_sum,rsum,csum,axes,er,ec,Finset.sum_boole,Nat.cast_id] at ax
  simp only [sum_add_distrib,er,ec,Finset.sum_boole,Nat.cast_id] at cap
  change (univ.filter (fun b => r b > c b)).card = (univ.filter (fun b => r b < c b)).card ∧ _
  exact ⟨by omega,cap.trans six⟩

omit [Fintype H] [DecidableEq H] in
/-- Incidences between triples and their three coordinate positions. -/
theorem total_support (A : Finset H) (support : H → Finset (Fin 9))
    (triples : ∀ h, (support h).card = 3) :
    (∑ i, (A.filter (fun h => i ∈ support h)).card) = A.card * 3 := by
  classical
  calc
    _ = ∑ i : Fin 9, ∑ h ∈ A, if i ∈ support h then 1 else 0 := by simp
    _ = ∑ h ∈ A, (support h).card := by rw [Finset.sum_comm]; simp
    _ = _ := Finset.sum_const_nat (fun h _ => triples h)

/-- The eight heavy neighbors of each light edge imply that every row coordinate and every
column coordinate belongs to exactly four triples. -/
theorem coordinate_four (R : Finset H) (support : H → Finset (Fin 9))
    (triples : ∀ h, (support h).card = 3) (rows : R.card = 12)
    (eight : ∀ i j, (R.filter (fun h => i ∈ support h)).card +
      (Rᶜ.filter (fun h => j ∈ support h)).card = 8) :
    (∀ i, (R.filter (fun h => i ∈ support h)).card = 4) ∧
    (∀ j, (Rᶜ.filter (fun h => j ∈ support h)).card = 4) := by
  let r (i : Fin 9) := (R.filter (fun h => i ∈ support h)).card
  let c (j : Fin 9) := (Rᶜ.filter (fun h => j ∈ support h)).card
  have marks (i j : Fin 9) : r i + c j = 8 := eight i j
  have same (i : Fin 9) (_ : i ∈ Finset.univ) : r i = r 0 := by
    have := marks i 0; have := marks 0 0; omega
  have sum : ∑ i, r i = R.card * 3 := total_support R support triples
  rw [Finset.sum_const_nat same,Finset.card_univ,Fintype.card_fin,rows] at sum
  have base : r 0 = 4 := by omega
  exact ⟨fun i => (same i (Finset.mem_univ _)).trans base,
    fun j => by change c j = 4; have := marks 0 j; omega⟩

end Order12.K99Counts

end

/- Component Erdos723.Local139.GridIncidence. -/
section

/- Old-line incidences among the twenty-four heavy points in the all-threes profile. -/

namespace Order12.Bipartite139

open Profile139 Finset
open scoped Classical

theorem heavy_card (D : Family) (profile : D.n 3 = 24) : Fintype.card (HeavyPoint D) = 24 := by
  rw [Fintype.card_subtype]
  have size := (D.n_eq 3).symm.trans profile
  exact_mod_cast size

@[simp] theorem mem_oldHeavy {D : Family} {b : D.S} {h : HeavyPoint D} :
    h ∈ oldHeavy D b ↔ h.val ∈ b.val := by simp [oldHeavy]

theorem heavy_old_degree (D : Family) (p : HeavyPoint D) :
    (univ.filter (fun b => p ∈ oldHeavy D b)).card = 10 := by
  calc
    _ = (through D.S p.val).card := by
      apply Finset.card_bij (fun (b : D.S) _ => b.val)
      · intro b hb
        exact mem_through.mpr ⟨b.property,mem_oldHeavy.mp (mem_filter.mp hb).2⟩
      · exact fun _ _ _ _ e => Subtype.ext e
      · intro b hb
        obtain ⟨bs,pb⟩ := mem_through.mp hb
        exact ⟨⟨b,bs⟩,mem_filter.mpr ⟨mem_univ _,mem_oldHeavy.mpr pb⟩,rfl⟩
    _ = 10 := by
      have h := p.property
      unfold Family.t deficit at h
      omega

theorem heavy_neighbors_nine (D : Family) (profile : D.n 3 = 24) (p : HeavyPoint D) :
    (univ.filter (fun q : HeavyPoint D => q.val ∈ holes D.S p.val)).card = 9 := by
  rw [count_heavy_hits]
  have eq := heavy_gap_count D profile p.val
  rw [p.property] at eq
  omega

theorem old_heavy_partners (D : Family) (profile : D.n 3 = 24) (p : HeavyPoint D) :
    (∑ b, if p ∈ oldHeavy D b then (oldHeavy D b).card - 1 else 0) = 14 := by
  classical
  apply K99Counts.encounter_sum
  · intro b c ne pb pc q qh
    obtain ⟨qb,qc⟩ := mem_inter.mp qh
    obtain ⟨w,_,only⟩ := D.good.2 b.val b.property c.val c.property
      (fun e => ne (Subtype.ext e))
    apply mem_singleton.mpr
    apply Subtype.ext
    exact (only q.val ⟨mem_oldHeavy.mp qb,mem_oldHeavy.mp qc⟩).trans
      (only p.val ⟨mem_oldHeavy.mp pb,mem_oldHeavy.mp pc⟩).symm
  · let N := univ.filter (fun q : HeavyPoint D => q.val ∈ holes D.S p.val)
    have members (q : HeavyPoint D) : q ∈ N ↔ q.val ∈ holes D.S p.val := by simp [N]
    have pair : (univ.filter (fun b => p ∈ oldHeavy D b)).biUnion (fun b => (oldHeavy D b).erase p) =
        univ.erase p \ N := by
      ext q
      constructor
      · intro h
        obtain ⟨b,pb,qb⟩ := mem_biUnion.mp h
        obtain ⟨ne,qb⟩ := mem_erase.mp qb
        refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,mem_univ _⟩,?_⟩
        intro qn
        exact (mem_holes.mp ((members q).mp qn)).2 ⟨b.val,b.property,
          mem_oldHeavy.mp (mem_filter.mp pb).2,mem_oldHeavy.mp qb⟩
      · intro h
        obtain ⟨qe,qn⟩ := mem_sdiff.mp h
        have ne := (mem_erase.mp qe).1
        have joined : ∃ b ∈ D.S, p.val ∈ b ∧ q.val ∈ b := by
          by_contra no
          exact qn ((members q).mpr (mem_holes.mpr ⟨fun e => ne (Subtype.ext e),no⟩))
        obtain ⟨b,hb,pb,qb⟩ := joined
        exact mem_biUnion.mpr ⟨⟨b,hb⟩,mem_filter.mpr ⟨mem_univ _,mem_oldHeavy.mpr pb⟩,
          mem_erase.mpr ⟨ne,mem_oldHeavy.mpr qb⟩⟩
    have sub : N ⊆ univ.erase p := by
      intro q qn
      exact mem_erase.mpr ⟨fun e => (mem_holes.mp ((members q).mp qn)).1 (congrArg Subtype.val e),mem_univ _⟩
    have cardN : N.card = 9 := heavy_neighbors_nine D profile p
    rw [pair,card_sdiff_of_subset sub,card_erase_of_mem (mem_univ _),card_univ,heavy_card D profile,cardN]

end Order12.Bipartite139

end

/- Component Erdos723.Local139.TripleCounts. -/
section

/- Express the bipartite heavy vectors in the incidence-counting theorem's notation. -/

namespace Order12.K99Counts

open Finset Bipartite139

variable {H : Type*} [Fintype H] [DecidableEq H]

def rowSet (t : H → HeavyTriple) : Finset H := univ.filter fun h => (t h).axis = .row

def minusSet (t : H → HeavyTriple) : Finset H := univ.filter fun h => (t h).reflected = true

/-- The multiplicity of a coordinate among a particular set of triples. -/
def position (t : H → HeavyTriple) (A : Finset H) (i : Fin 9) : ℕ :=
  (A.filter (fun h => i ∈ (t h).support)).card

private lemma triple_sums (t : H → HeavyTriple) (A : Finset H) (i : Fin 9) :
    (∑ h ∈ A, (t h).rowValue i) =
      position t (A ∩ rowSet t) i +
      (((A ∩ ((rowSet t)ᶜ ∩ minusSet t)).card : ℝ) - (A ∩ (rowSet t ∩ minusSet t)).card) / 3 ∧
    (∑ h ∈ A, (t h).colValue i) =
      position t (A ∩ (rowSet t)ᶜ) i -
      (((A ∩ ((rowSet t)ᶜ ∩ minusSet t)).card : ℝ) - (A ∩ (rowSet t ∩ minusSet t)).card) / 3 := by
  classical
  let R := rowSet t
  let M := minusSet t
  let mark (P : Prop) [Decidable P] : ℝ := if P then 1 else 0
  have axesApart : Axis.col ≠ Axis.row := by decide
  have each (h : H) :
      (t h).rowValue i = mark (h ∈ R ∧ i ∈ (t h).support) +
        (mark (h ∈ Rᶜ ∩ M) - mark (h ∈ R ∩ M))/3 ∧
      (t h).colValue i = mark (h ∈ Rᶜ ∧ i ∈ (t h).support) -
        (mark (h ∈ Rᶜ ∩ M) - mark (h ∈ R ∩ M))/3 := by
    cases axis : (t h).axis <;> cases flag : (t h).reflected <;> by_cases z : i ∈ (t h).support <;>
      norm_num [HeavyTriple.rowValue,HeavyTriple.colValue,HeavyTriple.shift,indicator,
        R,M,rowSet,minusSet,mark,axis,flag,z,axesApart]
  have marks (S : Finset H) :
      ∑ h ∈ A, mark (h ∈ S ∧ i ∈ (t h).support) = (position t (A ∩ S) i : ℝ) := by
    unfold mark position
    rw [Finset.sum_boole]
    congr 2
    ext h
    simp [and_assoc]
  have counts (S : Finset H) : ∑ h ∈ A, mark (h ∈ S) = ((A ∩ S).card : ℝ) := by
    simp only [mark,Finset.sum_boole,Finset.filter_mem_eq_inter]
  constructor
  · rw [Finset.sum_congr rfl (fun h (_ : h ∈ A) => (each h).1),Finset.sum_add_distrib,← Finset.sum_div,
      Finset.sum_sub_distrib,marks,counts,counts]
  · rw [Finset.sum_congr rfl (fun h (_ : h ∈ A) => (each h).2),Finset.sum_sub_distrib,← Finset.sum_div,
      Finset.sum_sub_distrib,marks,counts,counts]

private lemma sum_lights (L : Finset (Fin 9 × Fin 9)) (axis : Fin 9 × Fin 9 → Fin 9) :
    ∑ i, (L.filter fun e => axis e = i).card = L.card := by
  calc
    _ = ∑ i : Fin 9, ∑ e ∈ L, if axis e = i then 1 else 0 := by simp
    _ = _ := by rw [Finset.sum_comm]; simp

/-- On any old line, the actual row and column sums equal one, with lights given by edge
vectors. This supplies both the allowed heavy counts and their signs on exceptional lines. -/
theorem pattern_from_triples (t : H → HeavyTriple) (A : Finset H) (L : Finset (Fin 9 × Fin 9))
    (rowSum : ∀ i, ((L.filter (fun e => e.1 = i)).card : ℝ) + (∑ h ∈ A, (t h).rowValue i) = 1)
    (colSum : ∀ i, ((L.filter (fun e => e.2 = i)).card : ℝ) + (∑ h ∈ A, (t h).colValue i) = 1) :
    (A.card=0 ∨ A.card=2 ∨ A.card=4 ∨ A.card=6) ∧
    Pattern (A ∩ rowSet t).card (A ∩ (rowSet t)ᶜ).card
      (A ∩ (rowSet t ∩ minusSet t)).card (A ∩ ((rowSet t)ᶜ ∩ minusSet t)).card := by
  classical
  let R := rowSet t
  let M := minusSet t
  let wr (i : Fin 9) := (L.filter (fun e => e.1 = i)).card + position t (A ∩ R) i
  let wc (i : Fin 9) := (L.filter (fun e => e.2 = i)).card + position t (A ∩ Rᶜ) i
  have totalR : ∑ i, wr i = L.card + 3 * (A ∩ R).card := by
    simp only [wr,position,Finset.sum_add_distrib,sum_lights,
      total_support _ _ (fun h => (t h).card_support),Nat.mul_comm]
  have totalC : ∑ i, wc i = L.card + 3 * (A ∩ Rᶜ).card := by
    simp only [wc,position,Finset.sum_add_distrib,sum_lights,
      total_support _ _ (fun h => (t h).card_support),Nat.mul_comm]
  have sub (S : Finset H) : (A ∩ (S ∩ M)).card ≤ (A ∩ S).card :=
    Finset.card_le_card (fun _ hh => Finset.mem_inter.mpr
      ⟨(mem_inter.mp hh).1,(mem_inter.mp (mem_inter.mp hh).2).1⟩)
  have out := line_pattern L.card (A∩R).card (A∩Rᶜ).card (A ∩ (R∩M)).card (A ∩ (Rᶜ∩M)).card
    wr wc totalR totalC (sub R) (sub Rᶜ) (fun i => by
      have eq := rowSum i
      rw [(triple_sums t A i).1] at eq
      simpa only [wr,Nat.cast_add,add_assoc] using eq) (fun i => by
      have eq := colSum i
      rw [(triple_sums t A i).2] at eq
      simpa only [wc,Nat.cast_add,add_sub_assoc] using eq)
  have cover := card_sdiff_add_card_inter A R
  have eq : A \ R = A ∩ Rᶜ := by ext; simp
  rw [eq,add_comm] at cover
  rw [cover] at out
  exact out

/-- Eight heavy neighbors of every light edge translate directly to the support marks. -/
theorem coordinate_four_from_triples (t : H → HeavyTriple) (rows : (rowSet t).card = 12)
    (eight : ∀ i j, (∑ h, ((t h).rowValue i + (t h).colValue j)) = 8) :
    (∀ i, position t (rowSet t) i = 4) ∧ (∀ j, position t (rowSet t)ᶜ j = 4) := by
  classical
  apply coordinate_four (rowSet t) (fun h => (t h).support) (fun h => (t h).card_support) rows
  intro i j
  have eq := eight i j
  rw [Finset.sum_add_distrib,(triple_sums t univ i).1,(triple_sums t univ j).2] at eq
  simp only [Finset.univ_inter] at eq
  have marks : (position t (rowSet t) i : ℝ) + position t (rowSet t)ᶜ j = 8 := by linarith
  exact_mod_cast marks

/-- The old-line counts needed in the final sign-energy argument. -/
structure OldLineCounts {B : Type*} [Fintype B] (t : H → HeavyTriple) (on : B → Finset H) : Prop where
  six : (univ.filter fun b => (on b).card = 6).card ≤ 4
  rows : (rowSet t).card = 12
  cols : (rowSet t)ᶜ.card = 12
  reflected : (rowSet t ∩ minusSet t).card = ((rowSet t)ᶜ ∩ minusSet t).card
  row_positions : ∀ i, position t (rowSet t) i = 4
  col_positions : ∀ j, position t (rowSet t)ᶜ j = 4
  exceptional :
    let ER := univ.filter (fun b => (on b ∩ rowSet t).card > (on b ∩ (rowSet t)ᶜ).card)
    let EC := univ.filter (fun b => (on b ∩ rowSet t).card < (on b ∩ (rowSet t)ᶜ).card)
    ER.card = EC.card ∧ ER.card + EC.card ≤ 4
  energy : ∑ b, (((on b ∩ (rowSet t ∩ minusSet t)).card : ℝ) -
    (on b ∩ ((rowSet t)ᶜ ∩ minusSet t)).card)^2 ≤ 36

/-- All heavy and coordinate counts follow from the classified triples, old incidence degrees,
the old line vector sums, and the eight heavy incidences at each light edge. -/
theorem old_line_counts {B : Type*} [Fintype B] (t : H → HeavyTriple) (on : B → Finset H)
    (L : B → Finset (Fin 9 × Fin 9)) (size : Fintype.card H = 24)
    (degree : ∀ h, (univ.filter (fun b => h ∈ on b)).card = 10)
    (partners : ∀ h, (∑ b, if h ∈ on b then (on b).card - 1 else 0) = 14)
    (rowSum : ∀ b i, (((L b).filter (fun e => e.1 = i)).card : ℝ) + (∑ h ∈ on b, (t h).rowValue i) = 1)
    (colSum : ∀ b i, (((L b).filter (fun e => e.2 = i)).card : ℝ) + (∑ h ∈ on b, (t h).colValue i) = 1)
    (eight : ∀ i j, (∑ h, ((t h).rowValue i + (t h).colValue j)) = 8) : OldLineCounts t on := by
  have forms (b : B) := pattern_from_triples t (on b) (L b) (rowSum b) (colSum b)
  have cap := six_line_bound on size degree partners (fun b => (forms b).1)
  have axis := balance on (rowSet t) (minusSet t) size degree cap (fun b => (forms b).2)
  have four := coordinate_four_from_triples t axis.1 eight
  have ex := exceptional_counts on (rowSet t) (minusSet t) degree (axis.1.trans axis.2.1.symm)
    cap (fun b => (forms b).2)
  exact ⟨cap,axis.1,axis.2.1,axis.2.2.1,four.1,four.2,ex,axis.2.2.2⟩

end Order12.K99Counts

end

/- Component Erdos723.Local139.Energy. -/
section

/- Counting intersections of opposite-sign triples and the associated Gram energy. -/

namespace Order12.Energy139
open Finset Matrix
open scoped Matrix

abbrev Coord := Fin 9

def hits {H : Type*} (s : H → Finset Coord) (X : Finset H) (i : Coord) : ℕ :=
  (X.filter fun h => i ∈ s h).card

private def bit (s : Finset Coord) (i : Coord) : ℕ := if i ∈ s then 1 else 0

private lemma hits_eq {H : Type*} (s : H → Finset Coord) (X : Finset H) (i : Coord) :
    hits s X i = ∑ h ∈ X, bit (s h) i := Finset.card_filter _ _

private lemma card_bits (s : Finset Coord) : ∑ i, bit s i = s.card := by
  simp [bit]

private lemma inter_bits (s t : Finset Coord) :
    (s ∩ t).card = ∑ i, bit s i * bit t i := by
  classical
  calc
    _ = ∑ i, bit (s ∩ t) i := (card_bits _).symm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [bit,hs,ht]

theorem sum_hits {H : Type*} (s : H → Finset Coord) (X : Finset H)
    (triple : ∀ h ∈ X, (s h).card = 3) :
    ∑ i, hits s X i = 3 * X.card := by
  simp_rw [hits_eq]
  rw [Finset.sum_comm]
  simp_rw [card_bits]
  rw [sum_const_nat triple]
  omega

theorem cross_count {H : Type*} (s : H → Finset Coord) (X Y : Finset H) :
    (∑ x ∈ X, ∑ y ∈ Y, (s x ∩ s y).card) =
      ∑ i, hits s X i * hits s Y i := by
  simp_rw [inter_bits]
  calc
    _ = ∑ x ∈ X, ∑ i, ∑ y ∈ Y, bit (s x) i * bit (s y) i := by
      apply sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ x ∈ X, ∑ y ∈ Y, bit (s x) i * bit (s y) i := Finset.sum_comm
    _ = _ := by simp_rw [hits_eq, Finset.sum_mul, Finset.mul_sum]

/-- Count every intersecting pair at least once, and bound the count for either sign. -/
theorem cross_bounds {H : Type*} (s : H → Finset Coord) (X Y : Finset H)
    (triple : ∀ h ∈ X, (s h).card = 3) (four : ∀ i, hits s X i + hits s Y i = 4)
    (meet : ∀ x ∈ X, ∀ y ∈ Y, (s x ∩ s y).Nonempty) :
    X.card * Y.card ≤ ∑ i, hits s X i * hits s Y i ∧
      (∑ i, hits s X i * hits s Y i) ≤ 9 * X.card := by
  constructor
  · rw [← cross_count]
    calc
      _ = ∑ _ ∈ X, ∑ _ ∈ Y, (1 : ℕ) := by simp
      _ ≤ _ := sum_le_sum (fun x hx => sum_le_sum (fun y hy =>
        Nat.succ_le_of_lt (card_pos.mpr (meet x hx y hy))))
  · calc
      _ ≤ ∑ i, 3 * hits s X i := by
        apply sum_le_sum
        intro i _
        have bound := four i
        by_cases h : hits s X i = 0
        · simp [h]
        · have h' : hits s Y i ≤ 3 := by omega
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left (hits s X i) h'
      _ = 9 * X.card := by rw [← Finset.mul_sum, sum_hits s X triple]; omega

/-- The signed Gram energy is the sum of the cross-sign intersections on both axes. -/
theorem axis_energy {H : Type*} (s : H → Finset Coord) (X Y : Finset H)
    (triple : ∀ h ∈ X, (s h).card = 3) (four : ∀ i, hits s X i + hits s Y i = 4) :
    (∑ i, hits s X i * hits s Y i) + (∑ i, (hits s X i)^2) = 12 * X.card := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i, 4 * hits s X i := by
      apply sum_congr rfl
      intro i _
      nlinarith [four i, congrArg (fun t => hits s X i * t) (four i)]
    _ = _ := by rw [← Finset.mul_sum, sum_hits s X triple]; omega

/-- The axis counts and the bound of 36 force a common sign for all triples.
The energy inequality is supplied by the matrix identity below. -/
theorem uniform_count {H : Type*} (s : H → Finset Coord)
    (rm rp cm cp : Finset H) (k : ℕ)
    (rowMinus : rm.card = k) (colMinus : cm.card = k)
    (rowTotal : rm.card + rp.card = 12) (colTotal : cm.card + cp.card = 12)
    (triple : ∀ h, (s h).card = 3)
    (rowFour : ∀ i, hits s rm i + hits s rp i = 4)
    (colFour : ∀ i, hits s cm i + hits s cp i = 4)
    (rowMeet : ∀ x ∈ rm, ∀ y ∈ rp, (s x ∩ s y).Nonempty)
    (colMeet : ∀ x ∈ cm, ∀ y ∈ cp, (s x ∩ s y).Nonempty)
    (energy : 24*k ≤ 36 + (∑ i, (hits s rm i)^2) + (∑ i, (hits s cm i)^2)) :
    k = 0 ∨ k = 12 := by
  have r := cross_bounds s rm rp (fun h _ => triple h) rowFour rowMeet
  have c := cross_bounds s cm cp (fun h _ => triple h) colFour colMeet
  have r' := cross_bounds s rp rm (fun h _ => triple h)
    (fun i => by rw [Nat.add_comm, rowFour]) (fun y hy x hx => by
      rw [Finset.inter_comm]
      exact rowMeet x hx y hy)
  have er := axis_energy s rm rp (fun h _ => triple h) rowFour
  have ec := axis_energy s cm cp (fun h _ => triple h) colFour
  by_contra! h
  have kr : 0 < k := by omega
  have pr : 0 < rp.card := by omega
  obtain ⟨_,rUpper⟩ := r
  have rLow := (cross_bounds s rm rp (fun h _ => triple h) rowFour rowMeet).1
  have rup : rp.card ≤ 9 := by
    rw [rowMinus] at rLow rUpper
    nlinarith [Nat.le_of_lt kr]
  have kup : k ≤ 9 := by
    have lim := r'.1.trans r'.2
    rw [rowMinus] at lim
    nlinarith [Nat.le_of_lt pr]
  have kp : 3 ≤ k := by omega
  have sizes : rp.card = 12-k ∧ cp.card = 12-k := by omega
  have left := c.1
  rw [rowMinus, sizes.1] at rLow
  rw [colMinus, sizes.2] at left
  rw [rowMinus] at er
  rw [colMinus] at ec
  interval_cases k <;> omega

/-- Squared norm in a finite real coordinate system. -/
noncomputable def squared {I : Type*} [Fintype I] (v : I → ℝ) : ℝ := v ⬝ᵥ v

theorem squared_eq {I : Type*} [Fintype I] (v : I → ℝ) :
    squared v = ∑ i, (v i)^2 := by simp [squared, dotProduct, pow_two]

theorem gram_energy {H B C : Type*} [Fintype H] [Fintype B] [Fintype C] [DecidableEq H]
    (A : Matrix B H ℝ) (V : Matrix C H ℝ)
    (gram : Aᵀ * A + Vᵀ * V = (12 : ℝ) • 1 + Matrix.of (fun _ _ : H => (1 : ℝ)))
    (w : H → ℝ) (zero : ∑ h, w h = 0) :
    squared (A *ᵥ w) + squared (V *ᵥ w) = 12 * squared w := by
  have ones : (Matrix.of (fun _ _ : H => (1 : ℝ))) *ᵥ w = 0 := by
    funext i
    simpa [Matrix.mulVec,dotProduct] using zero
  have e := congrArg (fun M : Matrix H H ℝ => w ⬝ᵥ (M *ᵥ w)) gram
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    ones, add_zero, dotProduct_smul, smul_eq_mul] at e
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w,
      Matrix.vecMul_transpose] at e
  exact e

/-- The signed vector is supported precisely on the minus triples. -/
noncomputable def weight {H : Type*} [DecidableEq H] (r c : Finset H) (h : H) : ℝ :=
  (if h ∈ r then (1 : ℝ) else 0) - (if h ∈ c then (1 : ℝ) else 0)

theorem sum_weighted {H : Type*} [Fintype H] [DecidableEq H] (r c : Finset H) (a : H → ℝ) :
    (∑ h, a h * weight r c h) = ∑ h ∈ r, a h - ∑ h ∈ c, a h := by
  simp only [weight, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem weight_sum {H : Type*} [Fintype H] [DecidableEq H] (r c : Finset H)
    (same : r.card = c.card) : ∑ h, weight r c h = 0 := by
  simpa [same] using sum_weighted r c (fun _ => 1)

theorem weight_squared {H : Type*} [Fintype H] [DecidableEq H] (r c : Finset H)
    (dis : Disjoint r c) : squared (weight r c) = r.card + (c.card : ℝ) := by
  have rVal (x) (hx : x ∈ r) : weight r c x = 1 := by
    simp [weight,hx,Finset.disjoint_left.mp dis hx]
  have cVal (x) (hx : x ∈ c) : weight r c x = -1 := by
    simp [weight,hx,Finset.disjoint_right.mp dis hx]
  change (∑ h, weight r c h * weight r c h) = _
  rw [sum_weighted, Finset.sum_congr rfl rVal, Finset.sum_congr rfl cVal]
  simp

open Order12.Bipartite139

noncomputable def coordinates {H : Type*} (t : H → HeavyTriple) : Matrix (Coord ⊕ Coord) H ℝ :=
  Matrix.of fun i h => Sum.elim (t h).rowValue (t h).colValue i

private lemma indicator_dot (s t : Finset Coord) :
    (∑ i, indicator s i * indicator t i) = ((s ∩ t).card : ℝ) := by
  rw [← sum_indicator (s ∩ t)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [indicator,hs,ht]

/-- On the same axis, one reflected and one unreflected triple have scalar
product equal to their support intersection size minus one. -/
theorem dot_same_axis (u v : HeavyTriple) (ax : u.axis = v.axis)
    (minus : u.reflected = true) (plus : v.reflected = false) :
    (∑ i, u.rowValue i * v.rowValue i) + (∑ i, u.colValue i * v.colValue i)
      = ((u.support ∩ v.support).card : ℝ) - 1 := by
  cases hu : u.axis <;>
    simp [HeavyTriple.rowValue, HeavyTriple.colValue,HeavyTriple.shift,
      ← ax,hu,minus,plus,sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,
      indicator_dot,v.card_support]

/-- The matrix Gram of actual heavy columns gives the required intersection. -/
theorem same_axis_meet {H : Type*} (t : H → HeavyTriple) (x y : H)
    (axis : (t x).axis = (t y).axis)
    (minus : (t x).reflected = true) (plus : (t y).reflected = false)
    (nonneg : 0 ≤ ((coordinates t)ᵀ * coordinates t) x y) :
    ((t x).support ∩ (t y).support).Nonempty := by
  have e := dot_same_axis (t x) (t y) axis minus plus
  rw [Matrix.mul_apply,Fintype.sum_sum_type] at nonneg
  change 0 ≤ (∑ i, (t x).rowValue i * (t y).rowValue i) +
    (∑ i, (t x).colValue i * (t y).colValue i) at nonneg
  rw [e] at nonneg
  apply Finset.card_pos.mp
  by_contra! h
  simp [Nat.le_zero.mp h] at nonneg
  norm_num at nonneg

private lemma indicator_sum_hits {H : Type*} (s : H → Finset Coord) (X : Finset H) (i : Coord) :
    (∑ h ∈ X, indicator (s h) i) = (hits s X i : ℝ) := by
  simp [indicator,hits]

private lemma shifted_energy (v : Coord → ℝ) (a : ℝ) :
    ∑ i, (v i-a)^2 = ∑ i, (v i)^2 - (2*a) * ∑ i, v i + 9*a^2 := by
  calc
    _ = ∑ i, ((v i)^2 - (2*a)*v i + a^2) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by simp [sum_add_distrib,sum_sub_distrib,← mul_sum]

/-- All nonzero weights are on reflected triples, so the total squared norm is
the same as that of the two unreflected support counts. -/
theorem marked_coordinates_squared {H : Type*} [Fintype H] [DecidableEq H]
    (t : H → HeavyTriple) (r c : Finset H) (k : ℕ) (rc : r.card=k) (cc : c.card=k)
    (row : ∀ h ∈ r, (t h).axis = .row ∧ (t h).reflected = true)
    (col : ∀ h ∈ c, (t h).axis = .col ∧ (t h).reflected = true) :
    squared ((coordinates t) *ᵥ weight r c) =
      (∑ i, (hits (fun h => (t h).support) r i : ℝ)^2) +
      ∑ i, (hits (fun h => (t h).support) c i : ℝ)^2 := by
  let s := fun h => (t h).support
  let a : ℝ := 2 * k / 3
  have rval (i : Coord) : ((coordinates t) *ᵥ weight r c) (.inl i) = hits s r i - a := by
    change (∑ h, (t h).rowValue i * weight r c h) = _
    rw [sum_weighted]
    have left (h) (hmem : h ∈ r) : (t h).rowValue i = indicator (s h) i - 1 / 3 := by
      simp [s,HeavyTriple.rowValue,HeavyTriple.shift,(row h hmem).1,(row h hmem).2]
    have right (h) (hmem : h ∈ c) : (t h).rowValue i = 1 / 3 := by
      simp [HeavyTriple.rowValue,HeavyTriple.shift,(col h hmem).1,(col h hmem).2]
    rw [sum_congr rfl left, sum_congr rfl right, sum_sub_distrib, indicator_sum_hits]
    simp [rc,cc,a]
    ring
  have cval (i : Coord) : ((coordinates t) *ᵥ weight r c) (.inr i) = -(hits s c i - a) := by
    change (∑ h, (t h).colValue i * weight r c h) = _
    rw [sum_weighted]
    have left (h) (hmem : h ∈ r) : (t h).colValue i = 1 / 3 := by
      simp [HeavyTriple.colValue,HeavyTriple.shift,(row h hmem).1,(row h hmem).2]
    have right (h) (hmem : h ∈ c) : (t h).colValue i = indicator (s h) i - 1 / 3 := by
      simp [s,HeavyTriple.colValue,HeavyTriple.shift,(col h hmem).1,(col h hmem).2]
    rw [sum_congr rfl left, sum_congr rfl right, sum_sub_distrib, indicator_sum_hits]
    simp [rc,cc,a]
    ring
  have sr : (∑ i, (hits s r i : ℝ)) = 3*k := by
    exact_mod_cast (sum_hits s r (fun h _ => (t h).card_support)).trans (by rw [rc])
  have sc : (∑ i, (hits s c i : ℝ)) = 3*k := by
    exact_mod_cast (sum_hits s c (fun h _ => (t h).card_support)).trans (by rw [cc])
  rw [squared_eq,Fintype.sum_sum_type]
  simp_rw [rval,cval,neg_sq,shifted_energy,sr,sc]
  dsimp [s,a]
  ring

def part {H : Type*} [Fintype H] (t : H → HeavyTriple) (a : Axis) (reflected : Bool) : Finset H :=
  univ.filter (fun h => (t h).axis=a ∧ (t h).reflected=reflected)

@[simp] theorem mem_part {H : Type*} [Fintype H] (t : H → HeavyTriple)
    (h : H) (a : Axis) (v : Bool) :
    h ∈ part t a v ↔ (t h).axis = a ∧ (t h).reflected = v := by simp [part]

/-- Given the old line energy and the Gram identity, every heavy point uses
the same sign in the 9 by 9 branch. -/
theorem all_same_sign {H B : Type*} [Fintype H] [DecidableEq H] [Fintype B]
    (t : H → HeavyTriple) (A : Matrix B H ℝ)
    (gram : Aᵀ * A + (coordinates t)ᵀ * coordinates t =
      (12 : ℝ) • 1 + Matrix.of (fun _ _ : H => (1 : ℝ)))
    (gap : ∀ x y, x ≠ y → 0 ≤ ((coordinates t)ᵀ * coordinates t) x y)
    (total : ∀ a, (part t a true).card + (part t a false).card = 12)
    (same : (part t .row true).card = (part t .col true).card)
    (four : ∀ a i, hits (fun h => (t h).support) (part t a true) i +
      hits (fun h => (t h).support) (part t a false) i = 4)
    (old : squared (A *ᵥ weight (part t .row true) (part t .col true)) ≤ 36) :
    (∀ h, (t h).reflected=false) ∨ ∀ h, (t h).reflected=true := by
  let r := part t .row true
  let c := part t .col true
  let s := fun h => (t h).support
  let k := r.card
  have rc : r.card = k := rfl
  have cc : c.card = k := same.symm
  have dis : Disjoint r c := by
    apply Finset.disjoint_left.mpr
    intro h hr hc
    have hr' := ((mem_part t h .row true).1 hr).1
    have hc' := ((mem_part t h .col true).1 hc).1
    rw [hr'] at hc'
    contradiction
  have meets (a : Axis) (x) (hx : x ∈ part t a true) (y) (hy : y ∈ part t a false) :
      (s x ∩ s y).Nonempty := by
    obtain ⟨xa, xm⟩ := (mem_part t x a true).1 hx
    obtain ⟨ya, yp⟩ := (mem_part t y a false).1 hy
    have ne : x ≠ y := by rintro rfl; rw [xm] at yp; contradiction
    exact same_axis_meet t x y (xa.trans ya.symm) xm yp (gap x y ne)
  have e := gram_energy A (coordinates t) gram (weight r c) (weight_sum r c same)
  rw [marked_coordinates_squared t r c k rc cc
    (fun h hh => (mem_part t h .row true).1 hh) (fun h hh => (mem_part t h .col true).1 hh),
    weight_squared r c dis,rc,cc] at e
  have boundR : (24 : ℝ)*k ≤ 36 + (∑ i, (hits s r i : ℝ)^2) + ∑ i, (hits s c i : ℝ)^2 := by
    change squared (A *ᵥ weight r c) ≤ 36 at old
    dsimp only [s]
    linarith
  have bound : 24*k ≤ 36 + (∑ i, (hits s r i)^2) + ∑ i, (hits s c i)^2 := by exact_mod_cast boundR
  have possible := uniform_count s r (part t .row false) c (part t .col false) k
    rc cc (total .row) (total .col) (fun h => (t h).card_support)
    (four .row) (four .col) (meets .row) (meets .col) bound
  have vanish {a v} (hc : (part t a v).card=0) (h : H)
      (ha : (t h).axis=a) : (t h).reflected ≠ v := by
    intro hr
    have pos := Finset.card_pos.mpr ⟨h,(mem_part t h a v).mpr ⟨ha,hr⟩⟩
    omega
  rcases possible with zero|full
  · left
    intro h
    cases ha : (t h).axis
    · have neg := vanish (a:=.row) (v:=true) (rc.trans zero) h ha
      exact Bool.eq_false_of_not_eq_true neg
    · have neg := vanish (a:=.col) (v:=true) (cc.trans zero) h ha
      exact Bool.eq_false_of_not_eq_true neg
  · right
    intro h
    have rFull : (part t .row true).card = 12 := rc.trans full
    have cFull : (part t .col true).card = 12 := cc.trans full
    cases ha : (t h).axis
    · have neg := vanish (a:=.row) (v:=false) (by have := total .row; omega) h ha
      exact Bool.eq_true_of_not_eq_false neg
    · have neg := vanish (a:=.col) (v:=false) (by have := total .col; omega) h ha
      exact Bool.eq_true_of_not_eq_false neg

/-- The signed line sum is the count of reflected rows minus the count of
reflected columns on that line. -/
theorem old_energy_eq {H B : Type*} [Fintype H] [DecidableEq H] [Fintype B]
    (on : B → Finset H) (r c : Finset H) :
    squared ((Matrix.of (fun b h => if h ∈ on b then (1 : ℝ) else 0)) *ᵥ weight r c) =
      ∑ b, (((on b ∩ r).card : ℝ) - (on b ∩ c).card)^2 := by
  rw [squared_eq]
  apply sum_congr rfl
  intro b _
  congr 1
  change (∑ h, (if h ∈ on b then (1:ℝ) else 0) * weight r c h) = _
  rw [sum_weighted]
  simp [Finset.inter_comm]

def axisSet {H : Type*} [Fintype H] (t : H → HeavyTriple) (a : Axis) : Finset H :=
  univ.filter (fun h => (t h).axis=a)

def markedSet {H : Type*} [Fintype H] (t : H → HeavyTriple) : Finset H :=
  univ.filter (fun h => (t h).reflected = true)

theorem col_compl {H : Type*} [Fintype H] [DecidableEq H] (t : H → HeavyTriple) :
    axisSet t .col = (axisSet t .row)ᶜ := by
  ext h
  cases a : (t h).axis <;> simp [axisSet,a]

theorem marked_part {H : Type*} [Fintype H] [DecidableEq H] (t : H → HeavyTriple) (a : Axis) :
    part t a true = axisSet t a ∩ markedSet t := by ext h; simp [axisSet,markedSet,part]

private theorem parts_disjoint {H : Type*} [Fintype H] [DecidableEq H] (t : H → HeavyTriple)
    (a : Axis) : Disjoint (part t a true) (part t a false) := by
  apply Finset.disjoint_left.mpr
  intro h hx hy
  have eq := ((mem_part t h a true).1 hx).2.symm.trans ((mem_part t h a false).1 hy).2
  contradiction

private theorem parts_union {H : Type*} [Fintype H] [DecidableEq H] (t : H → HeavyTriple)
    (a : Axis) : part t a true ∪ part t a false = axisSet t a := by
  ext h
  cases v : (t h).reflected <;> simp [axisSet,v]

/-- Interface in terms of the row and minus subsets and old lines, as counted
by the classification of exceptional lines. -/
theorem all_same_sign_of_blocks {H B : Type*} [Fintype H] [DecidableEq H] [Fintype B]
    (t : H → HeavyTriple) (on : B → Finset H)
    (A : Matrix B H ℝ := Matrix.of (fun b h => if h ∈ on b then (1 : ℝ) else 0))
    (inc : A = Matrix.of (fun b h => if h ∈ on b then (1 : ℝ) else 0) := by rfl)
    (gram : Aᵀ * A + (coordinates t)ᵀ * coordinates t =
      (12 : ℝ) • 1 + Matrix.of (fun _ _ : H => (1 : ℝ)))
    (gap : ∀ x y, x ≠ y → 0 ≤ ((coordinates t)ᵀ * coordinates t) x y)
    (total : ∀ a, (axisSet t a).card = 12)
    (balance : (axisSet t .row ∩ markedSet t).card = (axisSet t .col ∩ markedSet t).card)
    (four : ∀ a i, hits (fun h => (t h).support) (axisSet t a) i = 4)
    (old : (∑ b, (((on b ∩ (axisSet t .row ∩ markedSet t)).card : ℝ) -
       (on b ∩ (axisSet t .col ∩ markedSet t)).card)^2) ≤ 36) :
    (∀ h, (t h).reflected=false) ∨ ∀ h, (t h).reflected=true := by
  apply all_same_sign t A gram gap
  · intro a
    rw [← Finset.card_union_of_disjoint (parts_disjoint t a),parts_union,total]
  · simpa only [marked_part] using balance
  · intro a i
    let pred := fun h : H => i ∈ (t h).support
    have dis := Finset.disjoint_of_subset_left
      (Finset.filter_subset pred (part t a true)) (Finset.disjoint_of_subset_right
        (Finset.filter_subset pred (part t a false)) (parts_disjoint t a))
    simpa only [hits,Finset.filter_union,Finset.card_union_of_disjoint dis] using
      (show (((part t a true ∪ part t a false).filter pred).card = 4) by
        rw [parts_union]; exact four a i)
  · rw [inc,old_energy_eq,marked_part,marked_part]
    exact old

/-- Restrict the point columns in a Gram identity to any injectively indexed subfamily. -/
theorem restrict_gram {P H B C : Type*} [Fintype B] [Fintype C] [DecidableEq P] [DecidableEq H]
    (A : Matrix B P ℝ) (V : Matrix C P ℝ) (p : H → P) (inj : Function.Injective p)
    (gram : Aᵀ * A + Vᵀ * V = (12 : ℝ) • 1 + Matrix.of (fun _ _ : P => (1 : ℝ))) :
    (A.submatrix id p)ᵀ * A.submatrix id p + (V.submatrix id p)ᵀ * V.submatrix id p =
      (12 : ℝ) • 1 + Matrix.of (fun _ _ : H => (1 : ℝ)) := by
  ext h k
  have e := congrFun (congrFun gram (p h)) (p k)
  simpa [Matrix.mul_apply,Matrix.one_apply,inj.eq_iff] using e

end Order12.Energy139

end

/- Component Erdos723.Local139.GridSigns. -/
section

/- Apply the energy inequality to the actual incidence columns of the 24 heavy points. -/

namespace Order12.Bipartite139

open Profile139 Finset Energy139 K99Counts
open scoped Matrix

theorem GridCoordinates.uniform_of_counts {D : Family} (G : GridCoordinates D)
    (counts : OldLineCounts G.triple (oldHeavy D)) :
    (∀ h, (G.triple h).reflected = false) ∨ ∀ h, (G.triple h).reflected = true := by
  classical
  let p : HeavyPoint D → Pt := Subtype.val
  let A := (Gram139.incidence D.S).submatrix id p
  have cols : G.W.submatrix id p = coordinates G.triple := by
    ext a h
    cases a with
    | inl i => exact G.heavyRow h i
    | inr i => exact G.heavyCol h i
  have fullgram : (Gram139.incidence D.S)ᵀ * Gram139.incidence D.S + G.Wᵀ * G.W =
      (12 : ℝ) • 1 + Matrix.of (fun _ _ : Pt => (1 : ℝ)) := by
    rw [G.gram]
    change _ + (Gram139.design Pt - _) = Gram139.design Pt
    abel
  have restricted := restrict_gram (Gram139.incidence D.S) G.W p Subtype.val_injective fullgram
  rw [cols] at restricted
  have entry (x y : HeavyPoint D) :
      ((coordinates G.triple)ᵀ * coordinates G.triple) x y = Gram139.gap D.S x.val y.val := by
    rw [← cols]
    simpa [Matrix.mul_apply, p] using congrFun (congrFun G.gram x.val) y.val
  have r : axisSet G.triple .row = rowSet G.triple := rfl
  have c : axisSet G.triple .col = (rowSet G.triple)ᶜ := by rw [col_compl, r]
  have m : markedSet G.triple = minusSet G.triple := rfl
  refine all_same_sign_of_blocks G.triple (oldHeavy D) A ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ext b h
    simp [A, p, Gram139.incidence, oldHeavy]
  · exact restricted
  · intro x y ne
    have diff : x.val ≠ y.val := fun e => ne (Subtype.ext e)
    rw [entry, Gram139.gap_entry D.S D.good, if_neg diff]
    split <;> norm_num
  · rintro (_|_)
    · simpa only [r] using counts.rows
    · simpa only [c] using counts.cols
  · simpa only [r, c, m] using counts.reflected
  · rintro (_|_) i
    · rw [r]; exact counts.row_positions i
    · rw [c]; exact counts.col_positions i
  · simpa only [r, c, m] using counts.energy

end Order12.Bipartite139

end

/- Component Erdos723.Local139.Reflection. -/
section

/- A common reflection of the nine-by-nine grid produces binary coordinates for every point. -/

namespace Order12.Bipartite139

open Finset Matrix
open scoped Matrix

namespace BinaryReflection

abbrev Side := Fin 9 ⊕ Fin 9

/-- The normal to the hyperplane spanned by the light points. -/
def normal : Side → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

noncomputable def reflect (v : Side → ℝ) : Side → ℝ :=
  v - ((v ⬝ᵥ normal) / 9) • normal

private theorem norm_normal : normal ⬝ᵥ normal = 18 := by
  norm_num [dotProduct,Fintype.sum_sum_type,normal]

private theorem reflect_dot (v w : Side → ℝ) : reflect v ⬝ᵥ reflect w = v ⬝ᵥ w := by
  simp only [reflect,sub_dotProduct,dotProduct_sub,dotProduct_smul,smul_dotProduct,
    smul_eq_mul,norm_normal]
  rw [dotProduct_comm normal w]
  ring

private theorem reflect_twice (v : Side → ℝ) : reflect (reflect v) = v := by
  funext i
  simp only [reflect,sub_dotProduct,smul_dotProduct,smul_eq_mul,norm_normal,Pi.sub_apply,
    Pi.smul_apply]
  ring

/-- The binary coordinates of a light point indexed by its row and column. -/
def cellColumn (i j : Fin 9) : Side → ℝ :=
  Sum.elim (fun x => if x=i then 1 else 0) (fun y => if y=j then 1 else 0)

noncomputable def tripleColumn (h : HeavyTriple) : Side → ℝ := Sum.elim h.rowValue h.colValue

private noncomputable def supportColumn (h : HeavyTriple) : Side → ℝ :=
  match h.axis with
  | .row => Sum.elim (indicator h.support) (fun _ => 0)
  | .col => Sum.elim (fun _ => 0) (indicator h.support)

private theorem reflect_cell (i j : Fin 9) : reflect (cellColumn i j) = cellColumn i j := by
  have orth : cellColumn i j ⬝ᵥ normal = 0 := by
    simp [dotProduct,Fintype.sum_sum_type,cellColumn,normal]
  simp [reflect,orth]

private theorem support_dot (h : HeavyTriple) :
    supportColumn h ⬝ᵥ normal = if h.axis = .row then 3 else -3 := by
  cases axis : h.axis <;> simp [dotProduct,Fintype.sum_sum_type,supportColumn,axis,normal,
    sum_indicator,h.card_support]

/-- A reflected heavy column is the orthogonal reflection of its binary support. -/
private theorem triple_eq (h : HeavyTriple) :
    tripleColumn h = if h.reflected then reflect (supportColumn h) else supportColumn h := by
  funext i
  simp only [reflect,support_dot]
  cases axis : h.axis <;> cases sign : h.reflected <;> cases i <;>
    simp [tripleColumn,HeavyTriple.rowValue,HeavyTriple.colValue,HeavyTriple.shift,
      axis,sign,supportColumn,normal] <;> ring

private theorem cell_binary (i j : Fin 9) (a : Side) :
    cellColumn i j a = 0 ∨ cellColumn i j a = 1 := by
  cases a <;> simp [cellColumn] <;> exact Or.symm (Classical.em _)

private theorem support_binary (h : HeavyTriple) (a : Side) :
    supportColumn h a = 0 ∨ supportColumn h a = 1 := by
  cases axis : h.axis <;> cases a <;> simp [supportColumn,axis,indicator] <;> exact Or.symm (Classical.em _)

private noncomputable def reflectMatrix {P : Type*} (W : Matrix Side P ℝ) : Matrix Side P ℝ :=
  Matrix.of fun i p => reflect (W.col p) i

private theorem reflect_gram {P : Type*} (W : Matrix Side P ℝ) :
    (reflectMatrix W)ᵀ * reflectMatrix W = Wᵀ * W := by
  ext p q
  exact reflect_dot (W.col p) (W.col q)

/-- Uniform signs turn the coordinates of the full points, grid cells, and triples
into a binary Gram factor of the same size. -/
theorem binary_of_uniform {H P : Type*} (t : H → HeavyTriple) (W : Matrix Side P ℝ)
    (shape : ∀ p, W.col p = 0 ∨ (∃ i j, W.col p = cellColumn i j) ∨
      ∃ h, W.col p = tripleColumn (t h))
    (uniform : (∀ h, (t h).reflected = false) ∨ ∀ h, (t h).reflected = true) :
    ∃ X : Matrix Side P ℝ, (∀ i p, X i p = 0 ∨ X i p = 1) ∧ Xᵀ * X = Wᵀ * W := by
  rcases uniform with plus|minus
  · refine ⟨W, ?_, rfl⟩
    intro a p
    change W.col p a = 0 ∨ W.col p a = 1
    rcases shape p with zero|⟨i,j,cell⟩|⟨h,heavy⟩
    · rw [zero]; exact Or.inl rfl
    · rw [cell]; exact cell_binary i j a
    · rw [heavy,triple_eq,plus]; exact support_binary _ _
  · refine ⟨reflectMatrix W, ?_, reflect_gram W⟩
    intro a p
    change reflect (W.col p) a = 0 ∨ reflect (W.col p) a = 1
    rcases shape p with zero|⟨i,j,cell⟩|⟨h,heavy⟩
    · rw [zero]; simp [reflect]
    · rw [cell,reflect_cell]; exact cell_binary i j a
    · rw [heavy,triple_eq,minus]; simpa only [Bool.true_eq,if_true,reflect_twice] using support_binary (t h) a

end BinaryReflection
end Order12.Bipartite139

end

/- Component Erdos723.Local139.GridCompletion. -/
section

/- A uniform choice of signs in a nine-by-nine grid completes the 139 old lines. -/

namespace Order12.Bipartite139

open Profile139 Local139 Matrix BinaryReflection
open scoped Matrix

/-- The full, light, and heavy points exhaust an all-threes family. Their grid
coordinates therefore give a binary factor as soon as the heavy signs agree. -/
theorem GridCoordinates.binary_of_uniform {D : Family} (G : GridCoordinates D)
    (profile : D.n 3 = 24)
    (uniform : (∀ h, (G.triple h).reflected = false) ∨ ∀ h, (G.triple h).reflected = true) :
    ∃ X : Matrix GridAxis Pt ℝ, (∀ i p, X i p = 0 ∨ X i p = 1) ∧
      Xᵀ * X = Gram139.gap D.S := by
  have shape (p : Pt) : G.W.col p = 0 ∨ (∃ i j, G.W.col p = cellColumn i j) ∨
      ∃ h, G.W.col p = tripleColumn (G.triple h) := by
    rcases profile_types D profile p with full|light|heavy
    · left; funext a; exact G.full p full a
    · right; left
      let x : LightPoint D.S := ⟨p, light_iff_deficit_two.mpr light⟩
      obtain ⟨⟨i,j⟩,eq⟩ := G.cell.surjective x
      refine ⟨i,j,?_⟩
      have val : (G.cell (i,j)).val = p := congrArg Subtype.val eq
      rw [← val]
      funext a
      cases a with
      | inl k => exact G.lightRow i j k
      | inr k => exact G.lightCol i j k
    · right; right
      let h : HeavyPoint D := ⟨p,heavy⟩
      refine ⟨h,?_⟩
      funext a
      cases a with
      | inl k => exact G.heavyRow h k
      | inr k => exact G.heavyCol h k
  obtain ⟨X,binary,gram⟩ := BinaryReflection.binary_of_uniform G.triple G.W shape uniform
  exact ⟨X,binary,gram.trans G.gram⟩

/-- A uniform grid extends the old lines to a full projective plane. -/
theorem GridCoordinates.full_of_uniform {D : Family} (G : GridCoordinates D)
    (profile : D.n 3 = 24)
    (uniform : (∀ h, (G.triple h).reflected = false) ∨ ∀ h, (G.triple h).reflected = true) :
    ∃ T : Blocks, D.S ⊆ T ∧ T.card = 157 ∧ Good T := by
  classical
  obtain ⟨X,bin,gram⟩ := G.binary_of_uniform profile uniform
  let e : Fin 18 ≃ GridAxis := Fintype.equivOfCardEq (by simp [GridAxis])
  let V : Matrix (Fin 18) Pt ℝ := X.submatrix e id
  apply Gram139.binary_factor_full D.S D.size V (fun i p => bin (e i) p)
  change Xᵀ.submatrix id e * X.submatrix e id = _
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id,gram]

end Order12.Bipartite139

end

/- Component Erdos723.Equivalence139. -/
section

/- Every compatible 139-line family on the 157 labeled points extends to a plane. -/

namespace Order12

private theorem full139_bipartite (D : Profile139.Family) (profile : D.n 3 = 24)
    (bip : (Local139.cliqueGraph D.S).Colorable 2) :
    ∃ T : Blocks, D.S ⊆ T ∧ T.card = 157 ∧ Good T := by
  classical
  obtain ⟨e, grid, label⟩ := Local139.bipartite_light_grid D profile bip
  obtain ⟨G⟩ := Bipartite139.gridCoordinates_of_labels D profile e grid label
  have counts := K99Counts.old_line_counts G.triple (Bipartite139.oldHeavy D) G.oldLight
    (Bipartite139.heavy_card D profile) (Bipartite139.heavy_old_degree D)
    (Bipartite139.old_heavy_partners D profile) (G.line_rows profile)
    (G.line_cols profile) (G.eight profile)
  exact G.full_of_uniform profile (G.uniform_of_counts counts)

/-- All the original 139 lines are preserved on the same 157 points. -/
theorem full_of_139 (S : Blocks) (size : S.card = 139) (good : Good S) :
    ∃ T : Blocks, S ⊆ T ∧ T.card = 157 ∧ Good T :=
  full139_of_bipartite full139_bipartite S size good

end Order12

end

/- The underlying cell type, three axes, and Latin property. -/
namespace Order12.Triangle
abbrev Cell := Fin 11 × Fin 11
abbrev Direction := Fin 3

def Latin (s : Cell → Fin 11) : Prop :=
  (∀ r : Fin 11, Function.Injective (fun c : Fin 11 => s (r,c))) ∧
  ∀ c : Fin 11, Function.Injective (fun r : Fin 11 => s (r,c))
end Order12.Triangle

/- Component Erdos723.Triangle.Partial, through the 139-line construction. -/
section

namespace Order12.Triangle.Partial

open Finset
abbrev Label := Direction × Fin 11
abbrev Point := Direction ⊕ (Label ⊕ Cell)
abbrev Row := Direction ⊕ (Label ⊕ Fin 103)

/-- The three coordinates are the actual row, column, and symbol of the one given square. -/
def coord (s : Cell → Fin 11) : Direction → Cell → Fin 11 := ![Prod.fst,Prod.snd,s]

def PartialTransversal (s : Cell → Fin 11) (B : Finset Cell) : Prop :=
  B.card = 10 ∧ ∀ d, Set.InjOn (coord s d) (B : Set Cell)

/-- The coordinates in which two blocks omit a common symbol. -/
def agreements (s : Cell → Fin 11) (B C : Finset Cell) : Finset Direction :=
  univ.filter (fun d => ∃ a : Fin 11, a ∉ B.image (coord s d) ∧ a ∉ C.image (coord s d))

def Compatible (s : Cell → Fin 11) (B C : Finset Cell) : Prop :=
  (B ∩ C).card + (agreements s B C).card = 1

private def fiber (s : Cell → Fin 11) (d : Direction) (a : Fin 11) :=
  univ.filter (fun x : Cell => coord s d x = a)

private def missing (s : Cell → Fin 11) (B : Finset Cell) : Finset Label :=
  univ.filter (fun t : Label => t.2 ∉ B.image (coord s t.1))

private def sideLabels (d : Direction) : Finset Label := {d} ×ˢ univ

@[simp] private lemma mem_fiber {s : Cell → Fin 11} {x : Cell} {d : Direction} {a : Fin 11} :
    x ∈ fiber s d a ↔ coord s d x = a := by simp [fiber]

@[simp] private lemma mem_missing {s : Cell → Fin 11} {B : Finset Cell} {t : Label} :
    t ∈ missing s B ↔ t.2 ∉ B.image (coord s t.1) := by simp [missing]

@[simp] private lemma mem_sideLabels {d : Direction} {t : Label} :
    t ∈ sideLabels d ↔ t.1 = d := by
  obtain ⟨e,a⟩ := t
  simp [sideLabels,eq_comm]

private lemma coord_pair (s : Cell → Fin 11) (latin : Latin s) (d e : Direction) (ne : d ≠ e) :
    Function.Bijective (fun x => (coord s d x, coord s e x)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  have rc : Function.Injective (fun x : Cell => (x.1,x.2)) := fun _ _ h => h
  have rs : Function.Injective (fun x : Cell => (x.1,s x)) := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ h
    obtain ⟨rfl,same⟩ := Prod.mk.inj h
    exact Prod.ext rfl (latin.1 _ same)
  have cs : Function.Injective (fun x : Cell => (x.2,s x)) := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ h
    obtain ⟨rfl,same⟩ := Prod.mk.inj h
    exact Prod.ext (latin.2 _ same) rfl
  have swap (f g : Cell → Fin 11) (inj : Function.Injective (fun x => (f x,g x))) :
      Function.Injective (fun x => (g x,f x)) :=
    fun _ _ h => inj (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  fin_cases d <;> fin_cases e <;>
    first | exact (ne rfl).elim | exact rc | exact rs | exact cs |
      exact swap _ _ rc | exact swap _ _ rs | exact swap _ _ cs

private lemma fiber_card (s : Cell → Fin 11) (latin : Latin s) (d : Direction) (a : Fin 11) :
    (fiber s d a).card = 11 := by
  obtain ⟨e,de⟩ := exists_ne d
  have pair := coord_pair s latin d e de.symm
  let f (x : fiber s d a) := coord s e x.val
  have bij : Function.Bijective f := by
    constructor
    · intro x y same
      exact Subtype.ext (pair.injective (Prod.ext ((mem_fiber.mp x.property).trans (mem_fiber.mp y.property).symm) same))
    · intro b
      obtain ⟨x,h⟩ := pair.surjective (a,b)
      exact ⟨⟨x,mem_fiber.mpr (congrArg Prod.fst h)⟩,congrArg Prod.snd h⟩
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_of_bijective bij

private lemma fiber_meet (s : Cell → Fin 11) (latin : Latin s) (d e : Direction) (de : d ≠ e) (a b : Fin 11) :
    (fiber s d a ∩ fiber s e b).card = 1 := by
  have pair := coord_pair s latin d e de
  obtain ⟨x,h⟩ := pair.surjective (a,b)
  apply card_eq_one_iff_existsUnique.mpr
  refine ⟨x,mem_inter.mpr ⟨mem_fiber.mpr (congrArg Prod.fst h),mem_fiber.mpr (congrArg Prod.snd h)⟩,?_⟩
  intro y hy
  obtain ⟨l,r⟩ := mem_inter.mp hy
  exact pair.injective ((Prod.ext (mem_fiber.mp l) (mem_fiber.mp r)).trans h.symm)

private lemma missing_unique {s : Cell → Fin 11} {B : Finset Cell} (part : PartialTransversal s B)
    (d : Direction) : ∃! a : Fin 11, a ∉ B.image (coord s d) := by
  have one : (univ \ B.image (coord s d)).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,card_image_of_injOn (part.2 d),part.1]
  simpa only [mem_sdiff,mem_univ,true_and] using card_eq_one_iff_existsUnique.mp one

private lemma missing_inj {s : Cell → Fin 11} {B : Finset Cell} (part : PartialTransversal s B) :
    Set.InjOn Prod.fst (missing s B : Set Label) := by
  rintro ⟨d,a⟩ ha ⟨e,b⟩ hb eq
  change d = e at eq
  subst e
  exact Prod.ext rfl ((missing_unique part d).unique (mem_missing.mp ha) (mem_missing.mp hb))

private lemma missing_card {s : Cell → Fin 11} {B : Finset Cell} (part : PartialTransversal s B) :
    (missing s B).card = 3 := by
  have all : (missing s B).image Prod.fst = univ := by
    apply eq_univ_of_forall
    intro d
    obtain ⟨a,ha,-⟩ := missing_unique part d
    exact mem_image.mpr ⟨(d,a),mem_missing.mpr ha,rfl⟩
  rw [← card_image_of_injOn (missing_inj part),all,card_univ,Fintype.card_fin]

private lemma agreements_card {s : Cell → Fin 11} {B C : Finset Cell} (part : PartialTransversal s B) :
    (missing s B ∩ missing s C).card = (agreements s B C).card := by
  have im : (missing s B ∩ missing s C).image Prod.fst = agreements s B C := by
    ext d
    simp only [agreements,mem_filter,mem_univ,true_and,mem_image,mem_inter,mem_missing]
    constructor
    · rintro ⟨⟨e,a⟩,h,rfl⟩
      exact ⟨a,h⟩
    · rintro ⟨a,h⟩
      exact ⟨(d,a),h,rfl⟩
  rw [← im,card_image_of_injOn ((missing_inj part).mono (by intro t ht; exact (mem_inter.mp ht).1))]

private def pack (A : Finset Direction) (B : Finset Label) (C : Finset Cell) : Finset Point :=
  A.disjSum (B.disjSum C)

private lemma disj_inter {α β : Type} [DecidableEq α] [DecidableEq β] (A C : Finset α) (B E : Finset β) :
    A.disjSum B ∩ C.disjSum E = (A ∩ C).disjSum (B ∩ E) := by ext x; cases x <;> simp

private lemma packed (A A' : Finset Direction) (B B' : Finset Label) (C C' : Finset Cell) :
    (pack A B C ∩ pack A' B' C').card = (A ∩ A').card + ((B ∩ B').card + (C ∩ C').card) := by
  simp only [pack,disj_inter,card_disjSum]

private def side (d : Direction) := pack (univ.erase d) (sideLabels d) ∅
private def vertex (s : Cell → Fin 11) (t : Label) := pack {t.1} {t} (fiber s t.1 t.2)
private def augment (s : Cell → Fin 11) (B : Finset Cell) := pack ∅ (missing s B) B

private def line (s : Cell → Fin 11) (B : Fin 103 → Finset Cell) : Row → Finset Point :=
  Sum.elim side (Sum.elim (vertex s) (fun i => augment s (B i)))

private lemma line_size {s : Cell → Fin 11} (latin : Latin s) {B : Fin 103 → Finset Cell}
    (each : ∀ i, PartialTransversal s (B i)) (r : Row) : (line s B r).card = 13 := by
  rcases r with d | t | i
  · change (side d).card = 13
    simp [side,pack,sideLabels,Direction]
  · change (vertex s t).card = 13
    simp [vertex,pack,fiber_card s latin]
  · change (augment s (B i)).card = 13
    simp [augment,pack,missing_card (each i),(each i).1]

private lemma side_side (d e : Direction) (ne : d ≠ e) : (side d ∩ side e).card = 1 := by
  have one : ((univ.erase d) ∩ (univ.erase e)).card = 1 := by
    fin_cases d <;> fin_cases e <;> first | exact (ne rfl).elim | decide
  have empty : sideLabels d ∩ sideLabels e = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨l,r⟩ := mem_inter.mp ht
    exact ne ((mem_sideLabels.mp l).symm.trans (mem_sideLabels.mp r))
  simp only [side,packed,one,empty,inter_self,card_empty,Nat.add_zero]

private lemma side_vertex (s : Cell → Fin 11) (d : Direction) (t : Label) :
    (side d ∩ vertex s t).card = 1 := by
  simp only [side,vertex,packed,empty_inter,card_empty,Nat.add_zero]
  by_cases e : t.1 = d <;> simp [e]

private lemma side_augment {s : Cell → Fin 11} {B : Finset Cell} (part : PartialTransversal s B)
    (d : Direction) : (side d ∩ augment s B).card = 1 := by
  have one : (sideLabels d ∩ missing s B).card = 1 := by
    obtain ⟨a,ha,unique⟩ := missing_unique part d
    apply card_eq_one_iff_existsUnique.mpr
    refine ⟨(d,a),mem_inter.mpr ⟨mem_sideLabels.mpr rfl,mem_missing.mpr ha⟩,?_⟩
    rintro ⟨e,b⟩ hb
    obtain ⟨side',miss⟩ := mem_inter.mp hb
    obtain rfl : e = d := mem_sideLabels.mp side'
    exact Prod.ext rfl (unique b (mem_missing.mp miss))
  simp [side,augment,packed,one]

private lemma vertex_vertex {s : Cell → Fin 11} (latin : Latin s) (t u : Label) (ne : t ≠ u) :
    (vertex s t ∩ vertex s u).card = 1 := by
  obtain ⟨d,a⟩ := t
  obtain ⟨e,b⟩ := u
  simp only [vertex,packed]
  by_cases eq : d = e
  · subst e
    have ab : a ≠ b := fun h => ne (Prod.ext rfl h)
    have empty : fiber s d a ∩ fiber s d b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨l,r⟩ := mem_inter.mp hx
      exact ab ((mem_fiber.mp l).symm.trans (mem_fiber.mp r))
    simp [Ne.symm ne,empty]
  · simp [Ne.symm ne,Ne.symm eq,fiber_meet s latin d e eq]

private lemma vertex_augment {s : Cell → Fin 11} {B : Finset Cell} (part : PartialTransversal s B)
    (t : Label) : (vertex s t ∩ augment s B).card = 1 := by
  simp only [vertex,augment,packed,inter_empty,card_empty,Nat.zero_add]
  by_cases h : t.2 ∈ B.image (coord s t.1)
  · obtain ⟨x,xb,xt⟩ := mem_image.mp h
    have one : (fiber s t.1 t.2 ∩ B).card = 1 := by
      apply card_eq_one_iff_existsUnique.mpr
      refine ⟨x,mem_inter.mpr ⟨mem_fiber.mpr xt,xb⟩,?_⟩
      intro y hy
      obtain ⟨yf,yb⟩ := mem_inter.mp hy
      exact part.2 t.1 yb xb ((mem_fiber.mp yf).trans xt.symm)
    simp [h,one]
  · have empty : fiber s t.1 t.2 ∩ B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨xf,xb⟩ := mem_inter.mp hx
      exact h (mem_image.mpr ⟨x,xb,mem_fiber.mp xf⟩)
    simp [h,empty]

private lemma augment_iff {s : Cell → Fin 11} {B C : Finset Cell} (part : PartialTransversal s B) :
    (augment s B ∩ augment s C).card = 1 ↔ Compatible s B C := by
  simp only [augment,packed,inter_self,card_empty,Nat.zero_add,agreements_card part,Compatible,Nat.add_comm]

private lemma line_meet {s : Cell → Fin 11} (latin : Latin s) {B : Fin 103 → Finset Cell}
    (each : ∀ i, PartialTransversal s (B i)) (pair : ∀ i j, i ≠ j → Compatible s (B i) (B j))
    (r q : Row) (ne : r ≠ q) : (line s B r ∩ line s B q).card = 1 := by
  rcases r with d | t | i <;> rcases q with e | u | j
  · exact side_side d e (by rintro rfl; exact ne rfl)
  · exact side_vertex s d u
  · exact side_augment (each j) d
  · rw [inter_comm]; exact side_vertex s e t
  · exact vertex_vertex latin t u (by rintro rfl; exact ne rfl)
  · exact vertex_augment (each j) t
  · rw [inter_comm]; exact side_augment (each i) e
  · rw [inter_comm]; exact vertex_augment (each i) u
  · exact (augment_iff (each i)).mpr (pair i j (by rintro rfl; exact ne rfl))

private lemma labeled_family {R : Type} [Fintype R] {Y : Type} [DecidableEq Y]
    (e : Y ≃ Pt) (rows : R → Finset Y) (sizes : ∀ r, (rows r).card = 13)
    (meets : ∀ r q, r ≠ q → (rows r ∩ rows q).card = 1) :
    let L (r : R) := (rows r).map e.toEmbedding
    let F := univ.image L
    Function.Injective L ∧ F.card = Fintype.card R ∧ Good F := by
  classical
  intro L F
  have number (r : R) : (L r).card = 13 := by simp [L,sizes]
  have hit (r q : R) (ne : r ≠ q) : (L r ∩ L q).card = 1 := by
    dsimp only [L]
    rw [← map_inter,card_map,meets r q ne]
  have inj : Function.Injective L := by
    intro r q eq
    by_contra ne
    have n := hit r q ne
    rw [eq,inter_self,number] at n
    omega
  refine ⟨inj,(card_image_of_injective _ inj).trans card_univ,?_,?_⟩
  · intro l hl
    obtain ⟨r,_,rfl⟩ := mem_image.mp hl
    exact number r
  · intro l hl k hk ne
    obtain ⟨r,_,rfl⟩ := mem_image.mp hl
    obtain ⟨q,_,rfl⟩ := mem_image.mp hk
    simpa only [mem_inter] using card_eq_one_iff_existsUnique.mp (hit r q (fun eq => ne (congrArg L eq)))

/-- The three sides, the 33 other vertex lines, and all 103 augmented transversals form a seed. -/
theorem seed139 {s : Cell → Fin 11} (latin : Latin s) {B : Fin 103 → Finset Cell}
    (each : ∀ i, PartialTransversal s (B i)) (pair : ∀ i j, i ≠ j → Compatible s (B i) (B j)) :
    ∃ F : Blocks, F.card = 139 ∧ Good F := by
  classical
  let e : Point ≃ Pt := Fintype.equivFinOfCardEq (by simp [Point,Label,Direction,Cell])
  have counts := labeled_family e (line s B) (line_size latin each) (line_meet latin each pair)
  refine ⟨_,counts.2.1.trans ?_,counts.2.2⟩
  simp [Row,Label,Direction]

end Order12.Triangle.Partial
end

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R3.H2 := by
  classical
  intro s B c rows cols transversals pairs
  obtain ⟨S, count, good⟩ := Order12.Triangle.Partial.seed139 (s := s) (B := B)
    ⟨rows, cols⟩ transversals pairs
  obtain ⟨T, _, size, valid⟩ := Order12.full_of_139 S count good
  let e : T ≃ Fin 157 := Fintype.equivFinOfCardEq (by simpa using size)
  refine ⟨fun i => (e.symm i).val, fun i => valid.1 _ (e.symm i).property, ?_⟩
  intro i j ne
  exact valid.2 _ (e.symm i).property _ (e.symm j).property
    (fun h => ne (e.symm.injective (Subtype.ext h)))
