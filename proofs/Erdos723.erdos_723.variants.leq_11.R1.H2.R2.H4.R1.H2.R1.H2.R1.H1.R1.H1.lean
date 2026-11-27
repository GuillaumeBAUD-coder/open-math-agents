import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1
import Mathlib

/-! Match the six-line incidence supports with a canonical labeling. On each layout, integer edge weights give a total exceeding what 37 triangles can cover. -/
open Finset
private abbrev Pt := Fin 19
private abbrev Line := Fin 6
private abbrev Sig := Finset Line

private def fiber (S : Pt → Sig) (t : Sig) := (univ.filter fun p => S p = t).card
private def code (t : Sig) := ∑ j ∈ t, 2^j.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem code_inj : Function.Injective code := by
  have h : ∀ a b : Sig, code a = code b → a = b := by decide +kernel
  exact fun a b e => h a b e

private lemma fiber_match (F G : Pt → Sig)
    (hm : ∀ t, 2 ≤ t.card → fiber F t = fiber G t)
    (hs : ∀ a, (univ.filter fun p => a ∈ F p).card = (univ.filter fun p => a ∈ G p).card) :
    ∃ e : Equiv.Perm Pt, ∀ p, F (e p) = G p := by
  classical
  have singles (a : Line) : fiber F {a} = fiber G {a} := by
    let U : Finset Sig := univ.filter fun t => a ∈ t
    have ha : {a} ∈ U := by simp [U]
    have eqs (S : Pt → Sig) : ∑ t ∈ U, fiber S t = (univ.filter fun p => a ∈ S p).card := by
      simpa [U,fiber] using sum_card_fiberwise_eq_card_filter (univ : Finset Pt) U S
    have eq := (eqs F).trans ((hs a).trans (eqs G).symm)
    rw [← add_sum_erase _ _ ha, ← add_sum_erase U (fiber G) ha] at eq
    have hr : ∑ t ∈ U.erase {a}, fiber F t = ∑ t ∈ U.erase {a}, fiber G t := by
      apply sum_congr rfl
      intro t ht
      obtain ⟨hne,ht⟩ := mem_erase.mp ht
      have hat := (mem_filter.mp ht).2
      apply hm
      by_contra! hc
      exact hne ((eq_of_subset_of_card_le (singleton_subset_iff.mpr hat) (by simp; omega)).symm)
    omega
  have same : ∀ t : Sig, t.Nonempty → fiber F t = fiber G t := by
    intro t ht
    by_cases H : 2 ≤ t.card
    · exact hm t H
    obtain ⟨a,rfl⟩ := card_eq_one.mp (by have := card_pos.mpr ht; omega : t.card = 1)
    exact singles a
  have empty : fiber F ∅ = fiber G ∅ := by
    have eqs (S : Pt → Sig) : ∑ t, fiber S t = 19 := by
      simpa [fiber] using sum_card_fiberwise_eq_card_filter (univ : Finset Pt) (univ : Finset Sig) S
    have eq := (eqs F).trans (eqs G).symm
    rw [← add_sum_erase _ _ (mem_univ (∅ : Sig)), ← add_sum_erase _ (fiber G) (mem_univ (∅ : Sig))] at eq
    have hr : ∑ t ∈ univ.erase (∅ : Sig), fiber F t = ∑ t ∈ univ.erase (∅ : Sig), fiber G t :=
      sum_congr rfl fun t ht => same t (nonempty_iff_ne_empty.mpr (mem_erase.mp ht).1)
    omega
  have e (t : Sig) : {p // G p = t} ≃ {p // F p = t} := Fintype.equivOfCardEq (by
    have hh : fiber G t = fiber F t := by
      rcases t.eq_empty_or_nonempty with rfl|ht
      · exact empty.symm
      · exact (same _ ht).symm
    simpa [fiber,Fintype.card_subtype] using hh)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private lemma weighted_obstruction (w : Pt → Pt → ℕ) (K : ℕ)
    (huge : 37*(2*K) < ∑ x, ∑ y, w x y) (di : ∀ x, w x x = 0)
    (sy : ∀ x y, w x y = w y x)
    (tr : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → w x y + w x z + w y z ≤ K)
    (B : Fin 37 → Finset Pt) (sz : ∀ b, (B b).card = 3)
    (cover : ∀ x y, 0 < w x y → ∃ b, x ∈ B b ∧ y ∈ B b) : False := by
  classical
  let f (b : Fin 37) (x y : Pt) := if x ∈ B b then if y ∈ B b then w x y else 0 else 0
  have localb (b : Fin 37) : ∑ x, ∑ y, f b x y ≤ 2*K := by
    obtain ⟨x,y,z,hxy,hxz,hyz,h⟩ := card_eq_three.mp (sz b)
    have sumf : ∑ x, ∑ y, f b x y = ∑ x ∈ B b, ∑ y ∈ B b, w x y := by
      simp [f,Finset.sum_ite_mem,Finset.sum_ite_irrel]
    rw [sumf,h]
    have hx' : x ∉ ({y,z} : Finset Pt) := by simp [hxy,hxz]
    have hy' : y ∉ ({z} : Finset Pt) := by simp [hyz]
    simp only [sum_insert hx',sum_insert hy',sum_singleton,di]
    have ht := tr x y z hxy hxz hyz
    rw [sy y x,sy z x,sy z y]
    omega
  have hle (x y : Pt) : w x y ≤ ∑ b, f b x y := by
    by_cases h : 0 < w x y
    · obtain ⟨b,hb,hb'⟩ := cover x y h
      simpa [f,hb,hb'] using (single_le_sum (f := fun b => f b x y) (fun _ _ => Nat.zero_le _) (mem_univ b))
    · omega
  have bound : ∑ x, ∑ y, w x y ≤ 37*(2*K) := calc
    _ ≤ ∑ x, ∑ y, ∑ b, f b x y := sum_le_sum fun x _ => sum_le_sum fun y _ => hle x y
    _ = ∑ b, ∑ x, ∑ y, f b x y := by
      simp_rw [Finset.sum_comm (f := fun y b => f b _ y)]
      rw [Finset.sum_comm]
    _ ≤ _ := by simpa using sum_le_sum (s := (univ : Finset (Fin 37))) fun b _ => localb b
  omega

private abbrev I := Fin 6
private def masks : List (List Nat) := [[3,5,6,9,10,12,17,18,33,34,52],[3,5,6,9,10,12,17,18,33,52],[3,5,6,9,10,17,18,28,33,34],[3,5,6,9,10,17,18,28,33,36],[3,5,6,9,10,17,18,33,36,56],[3,5,6,9,10,20,24,36,40,49]]
private def sigs : List (List Nat) := [[3,5,6,9,10,12,17,18,33,34,52,4,8,8,16,16,32,32,0],[3,5,6,9,10,12,17,18,33,52,2,4,8,8,16,16,32,32,32],[3,5,6,9,10,17,18,28,33,34,4,4,8,8,16,16,32,32,32],[3,5,6,9,10,17,18,28,33,36,2,4,8,8,16,16,32,32,32],[3,5,6,9,10,17,18,33,36,56,2,4,4,8,8,16,16,32,32],[3,5,6,9,10,20,24,36,40,49,1,2,2,4,8,16,16,32,32]]
private def weights : List (List Nat) := [[41175766641213440,41175748660174848,41175748421616640,41174532110680192,41174531872129040,41174511743664130,41096600998715520,41096600763827216,36109215990882432,36109215987205136,18016253935367681,41175748694254594,41174532144758930,41174532144758930,41096601032270994,41096601032270994,36109215991407762,36109215991407762,5146969928967314],[20587255852695552,20587255720574976,20587255735517184,20587255854792704,20587255869734912,20587255737614336,628139003968,627065258504,628139003968,619549037057,20587255869734912,20587255737614336,20587255871832064,20587255871832064,628139004489,628139004489,628139004489,628139004489,628139004489],[41175767716986880,41175748656504832,41175748421157888,41174531033268352,41174530797928464,41096603146133632,41096602911245328,61643020352618497,80421121958016,80421121491984,41175748690125826,41175748690125826,41174531066888338,41174531066888338,41096603179689106,41096603179689106,80421122024594,80421122024594,80421122024594],[41175765837938688,41175750535553024,41175748421157888,41174531033268352,41174528918880272,41096603146133632,41096601032197136,61643021023707137,80421121958016,80403935863810,41175765871559696,41175750569174018,41174531066888338,41174531066888338,41096603179689106,41096603179689106,80421122024594,80421122024594,80421122024594],[20587882934697984,20587806682517504,20587805744857600,20582936072159296,20582935000285192,20271224525426752,20271223453778440,321685534543936,321608225165825,78383153289,20587882936828424,20587806684647937,20587806684647937,20582936074289225,20582936074289225,20271224527524425,20271224527524425,321685534577225,321685534577225],[41175610986921984,41174666089865216,41174514021172224,41166969478643840,41166817409957904,40541349539226626,40533652928462994,642271557460994,634574975598738,5179730571456,41175765605752960,41175613537059856,41175613537059856,41174668371567618,41166971760345234,40542449055048850,40542449055048850,643371069154450,643371069154450]]
private def quota (i : I) : ℕ := ([6,2,6,6,3,6] : List Nat)[i.val]!
private def canon (i : I) (x : Pt) : Sig := univ.filter fun a => ((sigs[i.val]!)[x.val]!).testBit a.val
private def wt (i : I) (x y : Pt) : ℕ := ((weights[i.val]!)[x.val]! >>> (3*y.val)) % 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem canon_fiber (i : I) : ∀ (t : Sig), 2 ≤ t.card → fiber (canon i) t = if code t ∈ masks[i.val]! then 1 else 0 := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem canon_rows (i : I) : ∀ a : Line, (univ.filter fun p => a ∈ canon i p).card = 5 := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem heavy (i : I) : 37*(2*quota i) < ∑ x, ∑ y, wt i x y := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem zero_diag (i : I) : ∀ x, wt i x x = 0 := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem symmetry (i : I) : ∀ x y, wt i x y = wt i y x := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem pair_zero (i : I) : ∀ x y a, a ∈ canon i x → a ∈ canon i y → wt i x y = 0 := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem triangle (i : I) : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → wt i x y + wt i x z + wt i y z ≤ quota i := by
  fin_cases i <;> decide +kernel

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1.H1 := by
  classical
  rintro ⟨M,_,_,linePair,pointPair,sa,sb,sc,_,_,_,_,_,_,e,i,pat⟩
  let C (p : Pt) := univ.filter fun a : Line => M (.inl a) (.inl p) = true
  let F (p : Pt) := (C p).map e.toEmbedding
  have mat (a : Line) (p : Pt) : a ∈ F p ↔ M (.inl (e.symm a)) (.inl p) = true := by
    simp [F,C,mem_map_equiv]
  have marginal (a : Line) : (univ.filter fun p => a ∈ F p).card = 5 := by
    simp_rw [mat]
    exact sa _
  have hist (t : Sig) (ht : 2 ≤ t.card) : fiber F t = if code t ∈ masks[i.val]! then 1 else 0 := by
    have uniq : fiber F t ≤ 1 := by
      obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp ht
      apply card_le_one.mpr
      intro p hp q hq
      have hits (p : Pt) (h : F p = t) :
          M (.inl (e.symm a)) (.inl p) = true ∧ M (.inl (e.symm b)) (.inl p) = true :=
        ⟨(mat _ _).mp (h ▸ ha),(mat _ _).mp (h ▸ hb)⟩
      have ab := linePair (.inl (e.symm a)) (.inl (e.symm b)) (by simpa using hab)
      exact Sum.inl.inj (ab.unique (hits _ (mem_filter.mp hp).2) (hits _ (mem_filter.mp hq).2))
    have ex : 0 < fiber F t ↔ code t ∈ masks[i.val]! := by
      change ((univ.filter fun p : Pt => 2 ≤ (C p).card).image C).image (fun X => code (X.map e.toEmbedding)) = (masks[i.val]!).toFinset at pat
      constructor
      · intro h
        obtain ⟨p,hp⟩ := card_pos.mp h
        have eq := (mem_filter.mp hp).2
        have hC : (C p).card = t.card := by rw [← eq]; simp [F]
        have memC := mem_image_of_mem C (mem_filter.mpr ⟨mem_univ p,hC ▸ ht⟩ : p ∈ univ.filter fun p : Pt => 2 ≤ (C p).card)
        have mem := mem_image_of_mem (fun X : Sig => code (X.map e.toEmbedding)) memC
        rw [pat] at mem
        change code (F p) ∈ (masks[i.val]!).toFinset at mem
        simpa only [eq,List.mem_toFinset] using mem
      · intro h
        have h' : code t ∈ (masks[i.val]!).toFinset := List.mem_toFinset.mpr h
        rw [← pat] at h'
        obtain ⟨X,hX,he⟩ := mem_image.mp h'
        obtain ⟨p,hp,rfl⟩ := mem_image.mp hX
        exact card_pos.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,code_inj he⟩⟩
    split
    · rename_i hi
      have := ex.mpr hi
      omega
    · rename_i hi
      have := mt ex.mp hi
      omega
  obtain ⟨g,hg⟩ := fiber_match F (canon i) (fun t ht => (hist t ht).trans (canon_fiber i t ht).symm)
    (fun a => (marginal a).trans (canon_rows i a).symm)
  let B (b : Fin 37) := (univ.filter fun p : Pt => M (.inr (.inl b)) (.inl p) = true).map g.symm.toEmbedding
  apply weighted_obstruction (wt i) (quota i) (heavy i) (zero_diag i) (symmetry i) (triangle i) B (fun b => by simpa [B] using sb b)
  intro x y hw
  have hxy : x ≠ y := by rintro rfl; simpa [zero_diag] using hw
  obtain ⟨l,hl,_⟩ := pointPair (.inl (g x)) (.inl (g y)) (by simpa using hxy)
  rcases l with a|b|c
  · have hit (t : Pt) (hm : M (.inl a) (.inl (g t)) = true) : e a ∈ canon i t := by
      rw [← hg]
      exact (mat _ _).mpr (by simpa using hm)
    have hz := pair_zero i x y (e a) (hit _ hl.1) (hit _ hl.2)
    omega
  · exact ⟨b, by simpa [B,mem_map_equiv] using hl.1, by simpa [B,mem_map_equiv] using hl.2⟩
  · have one := (sc c).le
    exact False.elim (hxy (g.injective (card_le_one.mp one _ (mem_filter.mpr ⟨mem_univ _,hl.1⟩) _ (mem_filter.mpr ⟨mem_univ _,hl.2⟩))))
