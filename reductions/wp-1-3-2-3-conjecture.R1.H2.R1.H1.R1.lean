import OMAReductions.R_wp_1_3_2_3_conjecture_R1_H2_R1

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1_H1_R1

open scoped Classical in
def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
    let I (a b : P) := ¬ a ≤ b ∧ ¬ b ≤ a
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) x, e x = x) →
    (∃ a b c : P, I a b ∧ I a c ∧ I b c) →
    (∃ x : P, let N := {y : P | I x y}
      let Q := {y : P // y ≠ x}
      7 ≤ N.ncard ∧ (∀ a b : Q, a ≠ b → 2 * C P [] <
        3 * ((N.ncard+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ∧
        3 * min (C Q [(a,b)]) (C Q [(b,a)]) < C P []) ∧
      (∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a ⋖ b ∧ b ⋖ c ∧ c ⋖ d ∧
      let jump (u v : P) := 3 * C P [(x,u)] < C P [] ∧ 2 * C P [] < 3 * C P [(x,v)] ∧
        C P [] < 3 * C P [(u,x),(x,v)]
      2 * C P [] < 3 * C P [(x,a)] ∨ 2 * C P [] < 3 * C P [(d,x)] ∨
        jump a b ∨ jump b c ∨ jump c d)) →
    (let terminal (A : Type) [PartialOrder A] [Fintype A] (test : A → A → Prop) := ∃ t a b c d : A,
      let inc (u v : A) := ¬ u ≤ v ∧ ¬ v ≤ u
      a ⋖ b ∧ a ⋖ c ∧ d ⋖ c ∧ inc d a ∧ inc d b ∧ inc b c ∧
      (∀ z ∈ [a,b,c], inc t z) ∧ 2 * C A [] < 3 * C A [(b,c)] ∧
      2 * C A [] < 3 * C A [(a,t)] ∧ 3 * C A [(b,t)] < C A [] ∧ 3 * C A [(c,t)] < C A [] ∧ test b c
     let clean (b c : P) := (∀ k, b < k → c < k) ∧ ∃ d e : P, I d e ∧
       {k | k < c ∧ ¬ k < b} = ({d,e} : Set P)
     terminal P (fun b c => ¬ clean b c) ∧ terminal Pᵒᵈ (fun _ _ => True)) →
    (¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C P [p] + C P [p, q] ≤ C P [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

open scoped Classical in
def H2 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
    let I (a b : P) := ¬ a ≤ b ∧ ¬ b ≤ a
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) x, e x = x) →
    (∃ a b c : P, I a b ∧ I a c ∧ I b c) →
    (∃ x : P, let N := {y : P | I x y}
      let Q := {y : P // y ≠ x}
      7 ≤ N.ncard ∧ (∀ a b : Q, a ≠ b → 2 * C P [] <
        3 * ((N.ncard+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ∧
        3 * min (C Q [(a,b)]) (C Q [(b,a)]) < C P []) ∧
      (∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a ⋖ b ∧ b ⋖ c ∧ c ⋖ d ∧
      let jump (u v : P) := 3 * C P [(x,u)] < C P [] ∧ 2 * C P [] < 3 * C P [(x,v)] ∧
        C P [] < 3 * C P [(u,x),(x,v)]
      2 * C P [] < 3 * C P [(x,a)] ∨ 2 * C P [] < 3 * C P [(d,x)] ∨
        jump a b ∨ jump b c ∨ jump c d)) →
    (let terminal (A : Type) [PartialOrder A] [Fintype A] (test : A → A → Prop) := ∃ t a b c d : A,
      let inc (u v : A) := ¬ u ≤ v ∧ ¬ v ≤ u
      a ⋖ b ∧ a ⋖ c ∧ d ⋖ c ∧ inc d a ∧ inc d b ∧ inc b c ∧
      (∀ z ∈ [a,b,c], inc t z) ∧ 2 * C A [] < 3 * C A [(b,c)] ∧
      2 * C A [] < 3 * C A [(a,t)] ∧ 3 * C A [(b,t)] < C A [] ∧ 3 * C A [(c,t)] < C A [] ∧ test b c
     let clean (b c : P) := (∀ k, b < k → c < k) ∧ ∃ d e : P, I d e ∧
       {k | k < c ∧ ¬ k < b} = ({d,e} : Set P)
     terminal P (fun b c => clean b c ∧ 15 * C P [(b,c)] < 11 * C P []) ∧ terminal Pᵒᵈ (fun _ _ => True)) →
    (¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C P [p] + C P [p, q] ≤ C P [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

-- Swaps within each order of d,e preserve that order when b moves
-- past the later of them. Consequently the two images are disjoint.
lemma two_predecessor_counts (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ b c d e : P, ¬ b ≤ c → (∀ k, b < k → c < k) →
      (∀ k, k < c → k < b ∨ k = d ∨ k = e) →
      d < c → e < c → ¬ d ≤ b → ¬ e ≤ b → ¬ d ≤ e → ¬ e ≤ d →
      5 * C [(b,c)] ≤ 3 * C [] + C [(b,d)] + C [(b,e)] ∧
      2 * C [(b,d)] ≤ C [] ∧ 2 * C [(b,e)] ≤ C [] := by
  classical
  intro C b c d e bc upper lower dc ec db eb de ed
  have bd : ¬ b ≤ d := fun h => bc (h.trans dc.le)
  have be' : ¬ b ≤ e := fun h => bc (h.trans ec.le)
  have bn : b ≠ c := fun h => bc h.le
  have dn : b ≠ d := fun h => bd h.le
  have en : b ≠ e := fun h => be' h.le
  have den : d ≠ e := fun h => de h.le
  obtain ⟨_,_,split,_⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have half (i : P) (ic : i < c) (bi : ¬ b ≤ i) (pred : ∀ k, k < i → k < b) :
      2 * C [(b,i)] ≤ C [] := by
    have bound : C [(b,i)] ≤ C [(i,b)] := by
      apply OMA.R_wp_1_3_2_3_conjecture_R1.exchange_count_le P b i _ bi pred
      exact fun r hr ext => ⟨ext (b,i) (by simp), fun k bk => hr (ic.trans (upper k bk))⟩
    have row : C [(b,i)] + C [(i,b)] = C [] := split [] b i (fun h => bi h.le)
    omega
  have pd (k : P) (kd : k < d) : k < b := by
    rcases lower k (kd.trans dc) with h | rfl | rfl
    · exact h
    · exact kd.false.elim
    · exact (ed kd.le).elim
  have pe (k : P) (ke : k < e) : k < b := by
    rcases lower k (ke.trans ec) with h | rfl | rfl
    · exact h
    · exact (de ke.le).elim
    · exact ke.false.elim
  have hd := half d dc bd pd
  have he := half e ec be' pe
  -- Keep the leading constraint b<c explicit to partition the forward row.
  let F := [(b,c)]
  let Z := F ++ [(d,b),(e,b)]
  have reverse : C Z ≤ C [(c,b)] := by
    apply OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1.swap_cell_bound P Z [(c,b)] b c bc (by simp [Z,F])
    intro r hr ext
    refine ⟨fun k bk => hr (upper k bk),?_,?_⟩
    · intro k kc
      rcases lower k kc with h | rfl | rfl
      · exact hr h
      · exact ext (k,b) (by simp [Z,F])
      · exact ext (k,b) (by simp [Z,F])
    · intro p hp
      obtain rfl : p = (c,b) := by simpa using hp
      simpa using ext (b,c) (by simp [Z,F])
  have inside (i j : P) (jc : j < c) (bj : ¬ b ≤ j)
      (ib : i ≠ b) (ij : i ≠ j)      (pj : ∀ k, k < j → k < b)
      (members : (d = i ∨ d = j) ∧ (e = i ∨ e = j)) :
      C (F ++ [(i,b),(b,j)]) ≤ C (Z ++ [(i,j)]) := by
    apply OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1.swap_cell_bound P _ _ b j bj (by simp [F])
    intro r hr ext
    have pre := ext (i,b) (by simp [F])
    have post := ext (b,j) (by simp [F])
    have fixed := Equiv.swap_apply_of_ne_of_ne ib ij
    have unchanged := Equiv.swap_apply_of_ne_of_ne bn.symm jc.ne.symm
    refine ⟨fun k h => hr (jc.trans (upper k h)),fun k h => hr (pj k h),?_⟩
    have moved (k : P) (h : k = i ∨ k = j) :
        r (Equiv.swap b j k) < r (Equiv.swap b j b) := by
      rcases h with rfl | rfl
      · simpa [fixed] using pre.trans post
      · simpa using post
    intro p hp
    change p ∈ [(b,c),(d,b),(e,b),(i,j)] at hp
    simp only [List.mem_cons,
      List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simpa [unchanged] using hr jc
    · exact moved d members.1
    · exact moved e members.2
    · simpa [fixed] using pre
  have reorder (i j : P × P) : C (F ++ [i,j]) = C (F ++ [j,i]) := by
    apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro r
    simp [F, and_comm, and_assoc]
  -- Count the two middle cells against the two possible orders in Z.
  have middleDE := inside d e ec be' dn.symm den pe ⟨Or.inl rfl,Or.inr rfl⟩
  have middleED := inside e d dc bd en.symm den.symm pd ⟨Or.inr rfl,Or.inl rfl⟩
  have parts : C (Z ++ [(d,e)]) + C (Z ++ [(e,d)]) = C Z := split Z d e den
  have cross := reorder (e,b) (b,d)
  have cross' := reorder (b,e) (d,b)
  have first := reorder (b,e) (b,d)
  have f0 : C (F ++ [(b,d)]) + C (F ++ [(d,b)]) = C F := split F b d dn
  have f1 : C (F ++ [(b,d),(b,e)]) + C (F ++ [(b,d),(e,b)]) = C (F ++ [(b,d)]) :=
    split (F ++ [(b,d)]) b e en
  have f2 : C (F ++ [(d,b),(b,e)]) + C Z = C (F ++ [(d,b)]) :=
    split (F ++ [(d,b)]) b e en
  have f3 : C (F ++ [(b,e),(b,d)]) + C (F ++ [(b,e),(d,b)]) = C (F ++ [(b,e)]) :=
    split (F ++ [(b,e)]) b d dn
  have marg (k : P) : C (F ++ [(b,k)]) ≤ C [(b,k)] :=
    ((OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.2 _ _).2.1
  have h1 := marg d
  have h2 := marg e
  have sum : C F + C [(c,b)] = C [] := split [] b c bn
  change 5 * C F ≤ 3 * C [] + C [(b,d)] + C [(b,e)] ∧ _
  exact ⟨by omega,hd,he⟩

-- The sum bound forces one of the two named comparison probabilities
-- to reach one third. Each is already at most one half.
lemma two_predecessor_balance (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ b c d e : P, ¬ b ≤ c → (∀ k, b < k → c < k) →
      (∀ k, k < c → k < b ∨ k = d ∨ k = e) →
      d < c → e < c → ¬ d ≤ b → ¬ e ≤ b → ¬ d ≤ e → ¬ e ≤ d →
      11 * C [] ≤ 15 * C [(b,c)] →
      ∃ z ∈ [d,e], C [] ≤ 3 * C [(b,z)] ∧ 3 * C [(b,z)] ≤ 2 * C [] := by
  intro C b c d e bc upper lower dc ec db eb de ed pressure
  obtain ⟨mass,hd,he⟩ := two_predecessor_counts P b c d e bc upper lower dc ec db eb de ed
  change 5 * C [(b,c)] ≤ 3 * C [] + C [(b,d)] + C [(b,e)] at mass
  change 2 * C [(b,d)] ≤ C [] at hd
  change 2 * C [(b,e)] ≤ C [] at he
  by_cases h : C [] ≤ 3 * C [(b,d)]
  · exact ⟨d,by simp,h,by omega⟩
  · exact ⟨e,by simp,by omega,by omega⟩

theorem main : H1 → H2 → OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1.H1 := by
  classical
  intro other narrow P _ _ counts nonchain indecomp rigid three wide terminals barrier noGold
  let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
  obtain ⟨⟨t,a,b,c,k,ab,ac,kc,ka,kb,bc,inc,heavy,at',bt,ct⟩,
    ⟨t',a',b',c',k',ab',ac',kc',ka',kb',bc',inc',heavy',ha',hb',hc'⟩⟩ := terminals
  let clean := (∀ z : P, b < z → c < z) ∧ ∃ d e : P, (¬ d ≤ e ∧ ¬ e ≤ d) ∧
    {z | z < c ∧ ¬ z < b} = ({d,e} : Set P)
  by_cases h : clean
  · by_cases small : 15 * C [(b,c)] < 11 * C []
    · exact narrow P indecomp rigid three wide
        ⟨⟨t,a,b,c,k,ab,ac,kc,ka,kb,bc,inc,heavy,at',bt,ct,h,small⟩,
         ⟨t',a',b',c',k',ab',ac',kc',ka',kb',bc',inc',heavy',ha',hb',hc',trivial⟩⟩ noGold
    obtain ⟨upper,d,e,de,eq⟩ := h
    have mem (z : P) : z < c ∧ ¬ z < b ↔ z = d ∨ z = e := by
      change z ∈ {z | z < c ∧ ¬ z < b} ↔ _
      rw [eq]
      simp
    obtain ⟨dc,db⟩ := (mem d).2 (Or.inl rfl)
    obtain ⟨ec,eb⟩ := (mem e).2 (Or.inr rfl)
    have lower (z : P) (zc : z < c) : z < b ∨ z = d ∨ z = e :=
      or_iff_not_imp_left.mpr (fun h => (mem z).1 ⟨zc,h⟩)
    have below (z : P) (zc : z < c) (zb : ¬ z < b) : ¬ z ≤ b :=
      fun le => zb (lt_of_le_of_ne le (fun h => bc.1 (h ▸ zc.le)))
    obtain ⟨z,hz,lo,hi⟩ := two_predecessor_balance P b c d e bc.1 upper lower dc ec
      (below d dc db) (below e ec eb) de.1 de.2 (le_of_not_gt small)
    have ne : b ≠ z := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact fun h => bc.1 (h ▸ dc.le)
      · exact fun h => bc.1 (h ▸ ec.le)
    exact OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1.pair_of_count_bounds P b z ne lo hi
  · exact other P indecomp rigid three wide
      ⟨⟨t,a,b,c,k,ab,ac,kc,ka,kb,bc,inc,heavy,at',bt,ct,h⟩,
       ⟨t',a',b',c',k',ab',ac',kc',ka',kb',bc',inc',heavy',ha',hb',hc',trivial⟩⟩ noGold

end OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1_H1_R1
