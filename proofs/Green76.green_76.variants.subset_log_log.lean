import FormalConjectures.GreensOpenProblems.«76»
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Hitting rich rectangles with half of a planar point set

Split the points by x-coordinate. At each level of the partition, three-sided rectangles
admit a small family of witnesses built from y-coordinate windows. A random quarter-sample
followed by adding one point for each missed witness yields the O(log log n) threshold.
The epsilon-net bound is due to Aronov, Ezra and Sharir. Credit: @JaviSoto. -/

/- # Small witness families for one-sided rectangular ranges -/

namespace OMA.Green76Witness
open Finset Classical

variable {α : Type*} [DecidableEq α]

private noncomputable abbrev strip (A : Finset α) (y : α → ℝ) (c d : ℝ) :=
  A.filter (fun q => c ≤ y q ∧ y q ≤ d)

private noncomputable abbrev box (A : Finset α) (x y : α → ℝ) (b c d : ℝ) :=
  A.filter (fun q => x q ≤ b ∧ c ≤ y q ∧ y q ≤ d)

omit [DecidableEq α] in
private theorem eq_of_nested {U V : Finset α} (hn : U ⊆ V ∨ V ⊆ U) (hc : U.card = V.card) :
    U=V :=
  hn.elim (fun h => eq_of_subset_of_card_le h hc.ge)
    (fun h => (eq_of_subset_of_card_le h hc.le).symm)

omit [DecidableEq α] in
/-- Among t-point vertical windows through p, the number of points
strictly below p determines the whole window, including any ties at p. -/
private theorem strip_unique (A : Finset α) (y : α → ℝ) (p : α) (c d c' d' : ℝ)
    (hp : p ∈ strip A y c d) (hp' : p ∈ strip A y c' d')
    (hc : (strip A y c d).card = (strip A y c' d').card)
    (hlow : ((strip A y c d).filter (fun q => y q < y p)).card =
      ((strip A y c' d').filter (fun q => y q < y p)).card) :
    strip A y c d = strip A y c' d' := by
  classical
  let S := strip A y c d
  let T := strip A y c' d'
  let low := fun q => y q < y p
  have hpval := (mem_filter.mp hp).2
  have hpval' := (mem_filter.mp hp').2
  have hL : S.filter low = T.filter low := by
    apply eq_of_nested _ hlow
    rcases le_total c c' with h|h
    · right; intro q hq
      simp only [strip,mem_filter] at hq ⊢
      exact ⟨⟨hq.1.1, h.trans hq.1.2.1, hq.2.le.trans hpval.2⟩,hq.2⟩
    · left; intro q hq
      simp only [strip,mem_filter] at hq ⊢
      exact ⟨⟨hq.1.1, h.trans hq.1.2.1, hq.2.le.trans hpval'.2⟩,hq.2⟩
  have hU : S.filter (fun q => ¬low q) = T.filter (fun q => ¬low q) := by
    apply eq_of_nested
    · rcases le_total d d' with h|h
      · left; intro q hq
        simp only [S,T,strip,low,mem_filter,not_lt] at hq ⊢
        exact ⟨⟨hq.1.1,hpval'.1.trans hq.2,hq.1.2.2.trans h⟩,hq.2⟩
      · right; intro q hq
        simp only [S,T,strip,low,mem_filter,not_lt] at hq ⊢
        exact ⟨⟨hq.1.1,hpval.1.trans hq.2,hq.1.2.2.trans h⟩,hq.2⟩
    · have h1 := card_filter_add_card_filter_not (s:=S) low
      have h2 := card_filter_add_card_filter_not (s:=T) low
      change S.card = T.card at hc
      rw [hL] at h1
      omega
  change S=T
  ext q
  by_cases hq : low q
  · simpa [hq] using (Finset.ext_iff.mp hL q)
  · simpa [hq] using (Finset.ext_iff.mp hU q)

private noncomputable def windows (A : Finset α) (y : α → ℝ) (p : α) (t : ℕ) :
    Finset (Finset α) := A.powerset.filter
      (fun S => S.card=t ∧ p∈S ∧ ∃ c d : ℝ, S=strip A y c d)

private theorem windows_card (A : Finset α) (y : α → ℝ) (p : α) (t : ℕ) :
    (windows A y p t).card ≤ t := by
  classical
  let f (S : Finset α) := (S.filter (fun q => y q < y p)).card
  have hmem (S : Finset α) (hS : S ∈ windows A y p t) : f S ∈ range t := by
    obtain ⟨_, hc, hp, _⟩ := mem_filter.mp hS
    rw [mem_range,← hc]
    apply card_lt_card
    refine ⟨filter_subset _ _,fun h => ?_⟩
    exact (mem_filter.mp (h hp)).2.false
  have hinj : Set.InjOn f (windows A y p t) := by
    intro S hS T hT he
    obtain ⟨_, hc,hp,c,d,rfl⟩ := mem_filter.mp hS
    obtain ⟨_, hc',hp',c',d',rfl⟩ := mem_filter.mp hT
    exact strip_unique A y p c d c' d' hp hp' (hc.trans hc'.symm) he
  simpa using card_le_card_of_injOn f hmem hinj

/-- A t-rich three-sided range has one of at most t|A| fixed t-point
witnesses. The coordinates need not distinguish the elements of A. -/
theorem one_sided (A : Finset α) (x y : α → ℝ) (t : ℕ) (ht : 0<t) :
    ∃ W : Finset (Finset α), W.card ≤ t*A.card ∧
      (∀ U ∈ W, U ⊆ A ∧ U.card=t) ∧
      ∀ b c d : ℝ, t ≤ (A.filter (fun q => x q ≤ b ∧ c ≤ y q ∧ y q ≤ d)).card →
        ∃ U ∈ W, U ⊆ A.filter (fun q => x q ≤ b ∧ c ≤ y q ∧ y q ≤ d) := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases he : A.Nonempty
    · obtain ⟨p,hp,hmax⟩ := A.exists_max_image x he
      let B := A.erase p
      have hs : B ⊂ A := erase_ssubset hp
      obtain ⟨V,hV,hVmem,hcover⟩ := ih B hs
      let U := windows A y p t
      refine ⟨V ∪ U,?_,?_,?_⟩
      · have h := windows_card A y p t
        have hcard : B.card+1=A.card := card_erase_add_one hp
        rw [← hcard,Nat.mul_succ]
        exact (card_union_le _ _).trans (Nat.add_le_add hV h)
      · intro S hS
        rcases mem_union.mp hS with h|h
        · exact ⟨(hVmem S h).1.trans hs.le,(hVmem S h).2⟩
        · exact ⟨mem_powerset.mp (mem_filter.mp h).1,(mem_filter.mp h).2.1⟩
      · intro b c d hbig
        change t ≤ (box A x y b c d).card at hbig
        by_cases hsmall : t ≤ (box B x y b c d).card
        · obtain ⟨S,hS,hsub⟩ := hcover b c d hsmall
          exact ⟨S,mem_union_left _ hS,hsub.trans (by
            intro q hq; exact mem_filter.mpr ⟨hs.le (mem_filter.mp hq).1,(mem_filter.mp hq).2⟩)⟩
        · have hbox : box B x y b c d = (box A x y b c d).erase p := by
            ext q; simp [B,box,and_assoc]
          rw [hbox] at hsmall
          have hpm : p ∈ box A x y b c d := by
            by_contra h
            rw [erase_eq_of_notMem h] at hsmall
            omega
          have hpcard := card_erase_add_one hpm
          have hpval := (mem_filter.mp hpm).2.1
          have hstrip : box A x y b c d = strip A y c d := by
            ext q
            simp only [box,strip,mem_filter]
            exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(hmax _ h.1).trans hpval,h.2⟩⟩
          refine ⟨box A x y b c d,mem_union_right _ ?_,Subset.rfl⟩
          exact mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _),by omega,hpm,c,d,hstrip⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      exact ⟨∅,by simp,by simp,by simp [ht.ne']⟩

/-- One family for both horizontal orientations of three-sided rectangles. -/
theorem both_sides (A : Finset (ℝ × ℝ)) (t : ℕ) (ht : 0<t) :
    ∃ W : Finset (Finset (ℝ × ℝ)), W.card ≤ 2*t*A.card ∧
      (∀ U ∈ W, U ⊆ A ∧ U.card=t) ∧
      (∀ b c d : ℝ, t ≤ (A.filter (fun q => q.1 ≤ b ∧ c ≤ q.2 ∧ q.2 ≤ d)).card →
        ∃ U ∈ W, U ⊆ A.filter (fun q => q.1 ≤ b ∧ c ≤ q.2 ∧ q.2 ≤ d)) ∧
      (∀ a c d : ℝ, t ≤ (A.filter (fun q => a ≤ q.1 ∧ c ≤ q.2 ∧ q.2 ≤ d)).card →
        ∃ U ∈ W, U ⊆ A.filter (fun q => a ≤ q.1 ∧ c ≤ q.2 ∧ q.2 ≤ d)) := by
  obtain ⟨V,hV,hVm,hVl⟩ := one_sided A Prod.fst Prod.snd t ht
  obtain ⟨Z,hZ,hZm,hZr⟩ := one_sided A (fun p => -p.1) Prod.snd t ht
  refine ⟨V ∪ Z,?_,?_,?_,?_⟩
  · have := card_union_le V Z; nlinarith
  · exact fun U h => (mem_union.mp h).elim (hVm U) (hZm U)
  · intro b c d h
    obtain ⟨U,hU,hs⟩ := hVl b c d h
    exact ⟨U,mem_union_left _ hU,hs⟩
  · intro a c d h
    have hr := hZr (-a) c d
    simp only [neg_le_neg_iff] at hr
    obtain ⟨U,hU,hs⟩ := hr h
    exact ⟨U,mem_union_right _ hU,hs⟩

end OMA.Green76Witness

/- Binary decomposition for witnesses of rich rectangles. Each node splits in
lexicographic order; witnesses are needed only for a one-sided intersection of
a rectangle with a child of the first node where the rectangle crosses. -/
namespace OMA.Green76Split
open Finset
open scoped Classical

private abbrev Point := ℝ × ℝ

/-- The bit chooses the direction of the horizontal cut: true for a right ray. -/
def slice (right : Bool) (c lo hi : ℝ) (p : ℝ × ℝ) : Prop :=
  (if right then c ≤ p.1 else p.1 ≤ c) ∧ lo ≤ p.2 ∧ p.2 ≤ hi

private lemma split_ordered (A : Finset Point) (i : ℕ) (hi : i < A.card) :
    ∃ L R : Finset Point, L ∪ R = A ∧ Disjoint L R ∧ L.card = i ∧ R.card = A.card-i ∧
      ∀ p ∈ L, ∀ q ∈ R, p.1 ≤ q.1 := by
  let B := A.image toLex
  let e := B.orderIsoOfFin (k := A.card) (card_image_of_injective _ toLex.injective)
  let f (j : Fin A.card) := ofLex (e j).val
  let j : Fin A.card := ⟨i,hi⟩
  let L := (Iio j).image f
  have hsub : L ⊆ A := by
    intro p hp
    obtain ⟨k,_,rfl⟩ := mem_image.mp hp
    obtain ⟨p,hp,he⟩ := mem_image.mp (e k).property
    change ofLex (e k).val ∈ A
    rwa [←he]
  have hcard : L.card = i := by
    have hf : Function.Injective f := ofLex.injective.comp (Subtype.val_injective.comp e.injective)
    rw [show L=(Iio j).image f from rfl,card_image_of_injective _ hf]
    exact Fin.card_Iio _
  refine ⟨L,A\L,union_sdiff_of_subset hsub,disjoint_sdiff, hcard, ?_,?_⟩
  · rw [card_sdiff_of_subset hsub,hcard]
  · intro p hp q hq
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hp
    obtain ⟨hqA,hqL⟩ := mem_sdiff.mp hq
    let u := e.symm ⟨toLex q,mem_image_of_mem _ hqA⟩
    have hu : f u=q := congrArg (fun v : B => ofLex v.val) (e.apply_symm_apply _)
    have hju : j ≤ u := by
      by_contra! h
      exact hqL (mem_image.mpr ⟨u,mem_Iio.mpr h,hu⟩)
    rw [← hu]
    exact Prod.Lex.monotone_fst_ofLex (e.monotone ((mem_Iio.mp hk).le.trans hju))

theorem depth_bound (t : ℕ) (ht : 0<t)
    (side : ∀ (A : Finset Point) (right : Bool), ∃ W : Finset (Finset Point),
      W.card ≤ 2*t*A.card ∧ (∀ X ∈ W, X ⊆ A ∧ X.card = t) ∧
      ∀ c lo hi : ℝ, t ≤ (A.filter (slice right c lo hi)).card →
        ∃ X ∈ W, ∀ p ∈ X, slice right c lo hi p) :
    ∀ d (A : Finset Point), A.card ≤ 2^d → ∃ W : Finset (Finset Point),
      W.card ≤ 2*t*A.card*d ∧ (∀ X ∈ W, X ⊆ A ∧ X.card = t) ∧
      ∀ a b : Point, 2*t ≤ (A.filter (· ∈ Set.Icc a b)).card →
        ∃ X ∈ W, ∀ p ∈ X, p ∈ Set.Icc a b := by
  intro d
  induction d with
  | zero =>
    intro A h
    refine ⟨∅,by simp,by simp,?_⟩
    intro a b hab
    have := card_filter_le A (fun p => p ∈ Set.Icc a b)
    simp at h
    omega
  | succ d ih =>
    intro A h
    by_cases hsm : A.card ≤ 2^d
    · obtain ⟨W,hW,hgood,hcov⟩ := ih A hsm
      exact ⟨W,hW.trans (Nat.mul_le_mul_left _ (Nat.le_succ _)),hgood,hcov⟩
    obtain ⟨L,R,hunion,hdisj,hL,hR,hord⟩ := split_ordered A (2^d) (by omega)
    have hsL : L ⊆ A := hunion ▸ subset_union_left
    have hsR : R ⊆ A := hunion ▸ subset_union_right
    have hsum : L.card+R.card=A.card := by
      rw [←card_union_of_disjoint hdisj,hunion]
    have hhalf : R.card ≤ 2^d := by rw [pow_succ] at h; omega
    obtain ⟨WL,hl,hgl,hcl⟩ := ih L hL.le
    obtain ⟨WR,hr,hgr,hcr⟩ := ih R hhalf
    obtain ⟨UL,hul,hgul,hcul⟩ := side L true
    obtain ⟨UR,hur,hgur,hcur⟩ := side R false
    refine ⟨(WL ∪ WR) ∪ (UL ∪ UR),?_,?_,?_⟩
    · calc ((WL∪WR)∪(UL∪UR)).card ≤ (WL.card+WR.card)+(UL.card+UR.card) :=
            (card_union_le _ _).trans (Nat.add_le_add (card_union_le _ _) (card_union_le _ _))
           _ ≤ (2*t*L.card*d+2*t*R.card*d)+(2*t*L.card+2*t*R.card) := by omega
           _ = 2*t*A.card*(d+1) := by rw [←hsum]; ring
    · intro X hX
      simp only [mem_union] at hX
      rcases hX with (h|h)|(h|h)
      · exact ⟨(hgl X h).1.trans hsL,(hgl X h).2⟩
      · exact ⟨(hgr X h).1.trans hsR,(hgr X h).2⟩
      · exact ⟨(hgul X h).1.trans hsL,(hgul X h).2⟩
      · exact ⟨(hgur X h).1.trans hsR,(hgur X h).2⟩
    · intro a b hab
      let rl := L.filter (· ∈ Set.Icc a b)
      let rr := R.filter (· ∈ Set.Icc a b)
      have hrect : 2*t ≤ rl.card+rr.card := by
        rw [←hunion,filter_union] at hab
        exact hab.trans (card_union_le _ _)
      by_cases hleft : 2*t ≤ rl.card
      · obtain ⟨X,hX,hsub⟩ := hcl a b hleft
        exact ⟨X,by simp [hX],hsub⟩
      by_cases hright : 2*t ≤ rr.card
      · obtain ⟨X,hX,hsub⟩ := hcr a b hright
        exact ⟨X,by simp [hX],hsub⟩
      by_cases heavy : t ≤ rl.card
      · obtain ⟨q,hq⟩ := card_pos.mp (by omega : 0 < rr.card)
        obtain ⟨hqR,hqbox⟩ := mem_filter.mp hq
        have hslice : rl ⊆ L.filter (slice true a.1 a.2 b.2) := by
          intro p hp
          obtain ⟨hpL,hpbox⟩ := mem_filter.mp hp
          exact mem_filter.mpr ⟨hpL,hpbox.1.1,hpbox.1.2,hpbox.2.2⟩
        obtain ⟨X,hX,hsub⟩ := hcul a.1 a.2 b.2 (heavy.trans (card_le_card hslice))
        refine ⟨X,by simp [hX],?_⟩
        intro p hp
        obtain ⟨hx,hy,hz⟩ := hsub p hp
        exact ⟨⟨hx,hy⟩,⟨(hord p ((hgul X hX).1 hp) q hqR).trans hqbox.2.1,hz⟩⟩
      · obtain ⟨q,hq⟩ := card_pos.mp (by omega : 0 < rl.card)
        obtain ⟨hqL,hqbox⟩ := mem_filter.mp hq
        have hslice : rr ⊆ R.filter (slice false b.1 a.2 b.2) := by
          intro p hp
          obtain ⟨hpR,hpbox⟩ := mem_filter.mp hp
          exact mem_filter.mpr ⟨hpR,hpbox.2.1,hpbox.1.2,hpbox.2.2⟩
        obtain ⟨X,hX,hsub⟩ := hcur b.1 a.2 b.2 ((show t ≤ rr.card by omega).trans (card_le_card hslice))
        refine ⟨X,by simp [hX],?_⟩
        intro p hp
        obtain ⟨hx,hy,hz⟩ := hsub p hp
        exact ⟨⟨hqbox.1.1.trans (hord q hqL p ((hgur X hX).1 hp)),hy⟩,⟨hx,hz⟩⟩

/-- A family of at most `2 t n (1 + log₂ n)` witnesses for all rich rectangles. -/
theorem logarithmic (A : Finset (ℝ × ℝ)) (t : ℕ) (ht : 0 < t)
    (both : ∀ A : Finset (ℝ × ℝ), ∃ W : Finset (Finset (ℝ × ℝ)),
      W.card ≤ 2*t*A.card ∧ (∀ U ∈ W, U ⊆ A ∧ U.card=t) ∧
      (∀ b c d : ℝ, t ≤ (A.filter (fun q => q.1 ≤ b ∧ c ≤ q.2 ∧ q.2 ≤ d)).card →
        ∃ U ∈ W, U ⊆ A.filter (fun q => q.1 ≤ b ∧ c ≤ q.2 ∧ q.2 ≤ d)) ∧
      (∀ a c d : ℝ, t ≤ (A.filter (fun q => a ≤ q.1 ∧ c ≤ q.2 ∧ q.2 ≤ d)).card →
        ∃ U ∈ W, U ⊆ A.filter (fun q => a ≤ q.1 ∧ c ≤ q.2 ∧ q.2 ≤ d))) :
    ∃ W : Finset (Finset (ℝ × ℝ)), W.card ≤ 2*t*A.card*(A.card.log2+1) ∧
      (∀ X ∈ W, X ⊆ A ∧ X.card = t) ∧
      ∀ a b : ℝ × ℝ, 2*t ≤ (A.filter (· ∈ Set.Icc a b)).card →
        ∃ X ∈ W, ∀ p ∈ X, p ∈ Set.Icc a b := by
  apply depth_bound t ht _ (A.card.log2+1) A
  · rw [Nat.log2_eq_log_two]
    exact (Nat.lt_pow_succ_log_self (by decide) _).le
  · intro B right
    obtain ⟨W,hcard,hsub,hleft,hright⟩ := both B
    refine ⟨W,hcard,hsub,?_⟩
    intro c lo hi h
    cases right with
    | false =>
      have heq : B.filter (slice false c lo hi) =
          B.filter (fun q => q.1 ≤ c ∧ lo ≤ q.2 ∧ q.2 ≤ hi) := by
        ext p
        simp [slice]
      obtain ⟨U,hU,hp⟩ := hleft c lo hi (heq ▸ h)
      exact ⟨U,hU,fun p hx => (mem_filter.mp (hp hx)).2⟩
    | true =>
      have heq : B.filter (slice true c lo hi) =
          B.filter (fun q => c ≤ q.1 ∧ lo ≤ q.2 ∧ q.2 ≤ hi) := by
        ext p
        simp [slice]
      obtain ⟨U,hU,hp⟩ := hright c lo hi (heq ▸ h)
      exact ⟨U,hU,fun p hx => (mem_filter.mp (hp hx)).2⟩

end OMA.Green76Split

/- Alteration for finite witness families. Choose each point with probability 1/4
and then add one point from every missed witness. All averages are counted exactly. -/
namespace OMA.Rect76

open Finset
open scoped Classical

private lemma color_count {α : Type*} [Fintype α] [DecidableEq α] (w : Finset α)
    (C : Finset (Fin 4)) :
    (univ.filter (fun f : α → Fin 4 => ∀ x ∈ w, f x ∈ C)).card =
      C.card^w.card * 4^(Fintype.card α - w.card) := by
  classical
  let options (x : α) : Finset (Fin 4) := if x ∈ w then C else univ
  have eq : (univ.filter (fun f : α → Fin 4 => ∀ x ∈ w, f x ∈ C)) = Fintype.piFinset options := by
    ext f
    simp only [mem_filter,mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · intro h x
      by_cases hx : x ∈ w
      · simpa [options,hx] using h x hx
      · simp [options,hx]
    · intro h x hx
      simpa only [options, if_pos hx] using h x
  rw [eq,Fintype.card_piFinset]
  have each (x : α) : (options x).card = if x ∈ w then C.card else 4 := by
    by_cases h : x ∈ w <;> simp [options,h]
  simp_rw [each]
  rw [prod_ite]
  simp [show (univ.filter fun x => x ∉ w) = wᶜ by ext; simp, card_compl]

/-- If missing all the vertices of a t-set is sufficiently unlikely, some subset
of at most half the ground set hits every witness. -/
theorem alteration {α : Type*} [Fintype α] [DecidableEq α] (W : Finset (Finset α))
    (t : ℕ) (ht : 0 < t) (sz : ∀ w ∈ W, w.card = t)
    (small : 4 * W.card * 3^t ≤ Fintype.card α * 4^t) :
    ∃ H : Finset α, 2*H.card ≤ Fintype.card α ∧ ∀ w ∈ W, ∃ x ∈ H, x ∈ w := by
  classical
  by_cases hw : W.Nonempty
  swap
  · refine ⟨∅,by simp,?_⟩
    intro w hm
    exact (hw ⟨w,hm⟩).elim
  obtain ⟨w₀,hw₀⟩ := hw
  let n := Fintype.card α
  have htn : t ≤ n := (sz w₀ hw₀).symm ▸ w₀.card_le_univ
  have hn : 1 ≤ n := by omega
  let sample (f : α → Fin 4) := univ.filter fun x => f x = 0
  let misses (f : α → Fin 4) := W.filter fun w => ∀ x ∈ w, f x ≠ 0
  have hs : ∑ f, (sample f).card = n * 4^(n-1) := by
    calc _ = ∑ x : α, (univ.filter fun f : α → Fin 4 => f x = 0).card :=
          sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun (f : α → Fin 4) (x : α) => f x = 0)
         _ = ∑ _x : α, 4^(n-1) := by
           apply sum_congr rfl
           intro x _
           simpa [n] using color_count ({x} : Finset α) ({0} : Finset (Fin 4))
         _ = _ := by simp [n]
  have hm : ∑ f, (misses f).card = W.card * (3^t * 4^(n-t)) := by
    calc _ = ∑ w ∈ W, (univ.filter fun f : α → Fin 4 => ∀ x ∈ w, f x ≠ 0).card :=
           sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun (f : α → Fin 4) (w : Finset α) => ∀ x ∈ w, f x ≠ 0)
         _ = ∑ _w ∈ W, 3^t * 4^(n-t) := by
           apply sum_congr rfl
           intro w hw
           simpa [n,sz w hw] using color_count w (univ.erase (0 : Fin 4))
         _ = _ := by simp
  have power : 4^t * 4^(n-t) = (4:ℕ)^n := by rw [← pow_add]; congr 1; omega
  have power₁ : 4 * 4^(n-1) = (4:ℕ)^n := by rw [← pow_succ']; congr 1; omega
  have total : ∑ f : α → Fin 4, 2*((sample f).card+(misses f).card) ≤
      ∑ _f : α → Fin 4, n := by
    rw [← mul_sum, sum_add_distrib,hs,hm]
    simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul]
    have h := Nat.mul_le_mul_right (4^(n-t)) small
    change _ ≤ 4^n*n
    nlinarith only [h,congrArg (fun u : ℕ => u*n) power,congrArg (fun u : ℕ => u*n) power₁]
  obtain ⟨f,_,hf⟩ := exists_le_of_sum_le (s := (univ : Finset (α → Fin 4))) univ_nonempty total
  have witness : ∀ w : misses f, (w.val : Finset α).Nonempty := fun w =>
    card_pos.mp ((sz w.val (mem_filter.mp w.property).1).symm ▸ ht)
  let pick (w : misses f) : α := Classical.choose (witness w)
  let added := (univ : Finset (misses f)).image pick
  refine ⟨sample f ∪ added,?_,?_⟩
  · have h₁ := card_union_le (sample f) added
    have h₂ : added.card ≤ (misses f).card := card_image_le.trans_eq (by simp)
    omega
  · intro w hw
    by_cases bad : ∀ x ∈ w, f x ≠ 0
    · let j : misses f := ⟨w,mem_filter.mpr ⟨hw,bad⟩⟩
      exact ⟨pick j,mem_union_right _ (mem_image_of_mem _ (mem_univ j)), Classical.choose_spec (witness j)⟩
    · push Not at bad
      obtain ⟨x,hx,hzero⟩ := bad
      exact ⟨x,mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hzero⟩),hx⟩
end OMA.Rect76

/- A twofold binary logarithm suffices for the witness sampling estimate. -/
namespace OMA.Rect76
open Real

private theorem lt_pow_depth (n : ℕ) : n < 2^(Nat.log2 n + 1) := by
  simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n

/-- The witness threshold absorbs the O(log n) partition levels and its own
linear factor in the union bound. -/
theorem threshold : ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∃ t : ℕ, 0 < t ∧
    8*t*(Nat.log2 n+1)*3^t ≤ 4^t ∧ 2*t ≤ ⌈C*log (log n)⌉₊ := by
  let c₀ := log (log 3)
  have three : 1 < log 3 := by linarith [Real.log_three_gt_d9]
  have base : 0 < c₀ := Real.log_pos three
  refine ⟨600 / c₀ + 240,?_⟩
  intro n hn
  let d := Nat.log2 n + 1
  let l := Nat.log2 d + 1
  let t := 60*l
  have hl : 1 ≤ l := by simp [l]
  have h₂ : d ≤ 2^l := (lt_pow_depth d).le
  have h₁ : l ≤ 2^l := Nat.lt_two_pow_self.le
  refine ⟨t, by dsimp [t]; omega, ?_,?_⟩
  · have cmp : 8*t*d ≤ 2^(20*l) := calc
      8*t*d = 480*(l*d) := by dsimp [t]; ring
      _ ≤ 2^9*(2^l*2^l) := Nat.mul_le_mul (by decide) (Nat.mul_le_mul h₁ h₂)
      _ = 2^(9+(l+l)) := by rw [pow_add 2 9 (l+l),pow_add 2 l l]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    change 8*t*d*3^t ≤ 4^t
    apply (Nat.mul_le_mul_right _ cmp).trans
    change 2^(20*l)*3^(60*l) ≤ 4^(60*l)
    rw [show 60*l = 3*(20*l) by omega, pow_mul 3 3 (20*l), pow_mul 4 3 (20*l), ← mul_pow]
    exact Nat.pow_le_pow_left (by decide) _
  · have logn : 1 ≤ log n := three.le.trans (log_le_log (by norm_num) (by exact_mod_cast hn))
    have ll : c₀ ≤ log (log n) := log_le_log (by linarith) (log_le_log (by norm_num) (by exact_mod_cast hn))
    have ln2 : (1/2 : ℝ) < log 2 := by linarith [log_two_gt_d9]
    have logBound (a : ℕ) : (Nat.log2 a : ℝ) ≤ 2 * log a := by
      apply (Real.log2_le_logb a).trans
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith [Real.log_natCast_nonneg a, mul_nonneg (Real.log_natCast_nonneg a) (sub_nonneg.mpr ln2.le)]
    have hd : (d : ℝ) ≤ 3*log n := by
      dsimp [d]
      push_cast
      linarith [logBound n]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by dsimp [d]; omega)
    have hlogd := log_le_log hdpos hd
    rw [Real.log_mul (by norm_num) (by linarith : log (n:ℝ) ≠ 0)] at hlogd
    have llbound : (l : ℝ) ≤ 5+2*log (log n) := by
      dsimp [l]; push_cast
      linarith [logBound d,Real.log_three_lt_d9]
    have large : 600 ≤ (600/c₀) * log (log n) := calc
      (600 : ℝ) = (600/c₀)*c₀ := (div_mul_cancel₀ _ base.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ll (by positivity)
    apply (Nat.cast_le (α := ℝ)).mp
    apply le_trans _ (Nat.le_ceil _)
    dsimp [t]
    push_cast
    nlinarith only [llbound,large]
end OMA.Rect76

open Finset in
theorem OMA.solution : type_of% @Green76.green_76.variants.subset_log_log := by
  classical
  obtain ⟨C,hC⟩ := OMA.Rect76.threshold
  refine ⟨C,fun A hn => ?_⟩
  obtain ⟨t,ht,small,threshold⟩ := hC A.card hn
  obtain ⟨W,cardW,sizes,covers⟩ := OMA.Green76Split.logarithmic A t ht
    (fun B => OMA.Green76Witness.both_sides B t ht)
  let restriction (w : Finset (ℝ × ℝ)) : Finset A := w.subtype (· ∈ A)
  let V := W.image restriction
  have sz : ∀ v ∈ V, v.card = t := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    obtain ⟨hsub,hcard⟩ := sizes w hw
    simpa only [restriction,card_subtype,filter_eq_self.mpr hsub] using hcard
  have cardV : V.card ≤ 2*t*A.card*(A.card.log2+1) := card_image_le.trans cardW
  have prob : 4 * V.card * 3^t ≤ Fintype.card A * 4^t := calc
    4*V.card*3^t ≤ 4*(2*t*A.card*(A.card.log2+1))*3^t :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cardV)
    _ = A.card*(8*t*(A.card.log2+1)*3^t) := by ring
    _ ≤ _ := by simpa only [Fintype.card_coe] using Nat.mul_le_mul_left A.card small
  obtain ⟨H,hsize,hits⟩ := OMA.Rect76.alteration V t ht sz prob
  refine ⟨H.image Subtype.val,?_,?_,?_⟩
  · intro p hp
    obtain ⟨j,_,rfl⟩ := mem_image.mp hp
    exact j.property
  · have bound : (H.image Subtype.val).card ≤ H.card := card_image_le
    simp only [Fintype.card_coe] at hsize
    omega
  · intro a b hrect
    obtain ⟨w,hw,hrectw⟩ := covers a b (threshold.trans hrect)
    obtain ⟨p,hp,hpw⟩ := hits (restriction w) (mem_image_of_mem _ hw)
    exact ⟨p.val,mem_image_of_mem _ hp,hrectw p.val (mem_subtype.mp hpw)⟩
