import FormalConjectures.ErdosProblems.«210»
import Mathlib

/-!
A reduction of the odd ordinary-line bound through one-point edits of
the balanced Böröczky configurations in Green and Tao, arXiv:1208.4714.
-/

open Finset Filter EuclideanGeometry
open scoped Classical

namespace OMA.R_Erdos210_erdos_210_variants_green_tao_odd_R1

/- The unique-core and mixed-secant estimates are from merged reduction
Erdos210.erdos_210.variants.green_tao.R1, PR 6320. -/
/-- A secant from outside an affine subspace meets that subspace in at
most one point. -/
lemma unique_core (L : AffineSubspace ℝ ℝ²) {p a b : ℝ²}
    (hp : p ∉ L) (ha : a ∈ L) (hb : b ∈ L) (h : b ∈ line[ℝ,p,a]) : b = a := by
  by_contra hba
  have e := affineSpan_pair_eq_of_mem_of_mem_of_ne h
    (right_mem_affineSpan_pair ℝ p a) hba
  have hline : line[ℝ,b,a] ≤ L := affineSpan_pair_le_of_mem_of_mem hb ha
  rw [e] at hline
  exact hp (hline (left_mem_affineSpan_pair ℝ p a))

/-- Count all unblocked mixed secants before specializing the sizes. -/
lemma mixed (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) :
    let A := s.filter (· ∈ L)
    let T := s.filter (· ∉ L)
    T.card * (A.card - (T.card-1)) ≤ (ordinaryLines s).card := by
  classical
  let A := s.filter (· ∈ L)
  let T := s.filter (· ∉ L)
  let lines (p : ℝ²) := A.image (fun a => line[ℝ,p,a])
  let blocked (p : ℝ²) := (T.erase p).image (fun q => line[ℝ,p,q])
  let G (p : ℝ²) := lines p \ blocked p
  have core {a : ℝ²} (ha : a ∈ A) : a ∈ s ∧ a ∈ L := mem_filter.mp ha
  have off {p : ℝ²} (hp : p ∈ T) : p ∈ s ∧ p ∉ L := mem_filter.mp hp
  have good {p : ℝ²} (hp : p ∈ T) {l : AffineSubspace ℝ ℝ²} (hl : l ∈ G p) :
      ∃ a ∈ A, line[ℝ,p,a] = l ∧ ∀ q ∈ T, q ∈ l → q = p := by
    obtain ⟨h₁,h₂⟩ := mem_sdiff.mp hl
    obtain ⟨a,ha,he⟩ := mem_image.mp h₁
    refine ⟨a,ha,he,?_⟩
    intro q hq hql
    by_contra hqp
    apply h₂
    refine mem_image.mpr ⟨q,mem_erase.mpr ⟨hqp,hq⟩,?_⟩
    rw [←he] at hql ⊢
    exact affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair ℝ p a) hql (Ne.symm hqp)
  have ordinary {p : ℝ²} (hp : p ∈ T) {l : AffineSubspace ℝ ℝ²} (hl : l ∈ G p) :
      l ∈ ordinaryLines s := by
    obtain ⟨a,ha,he,honly⟩ := good hp hl
    have hpa : p ≠ a := fun e => (off hp).2 (e ▸ (core ha).2)
    apply mem_ordinaryLines.mpr
    refine ⟨⟨p,(off hp).1,a,(core ha).1,hpa,he⟩,?_⟩
    have hpair : s.filter (· ∈ l) = {p,a} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxs,hxl⟩ := mem_filter.mp hx
        by_cases h : x ∈ L
        · have eq := unique_core L (off hp).2 (core ha).2 h (he.symm ▸ hxl)
          simp [eq]
        · have eq := honly x (mem_filter.mpr ⟨hxs,h⟩) hxl
          simp [eq]
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact mem_filter.mpr ⟨(off hp).1,he ▸ left_mem_affineSpan_pair ℝ x a⟩
        · obtain rfl := Finset.mem_singleton.mp hx
          exact mem_filter.mpr ⟨(core ha).1,he ▸ right_mem_affineSpan_pair ℝ p x⟩
    rw [hpair]; simp [hpa]
  have size (p : ℝ²) (hp : p ∈ T) : A.card - (T.card-1) ≤ (G p).card := by
    have hinj : Set.InjOn (fun a => line[ℝ,p,a]) (A : Set ℝ²) := by
      intro a ha b hb eq
      exact unique_core L (off hp).2 (core hb).2 (core ha).2
        (by change line[ℝ,p,a] = line[ℝ,p,b] at eq; rw [←eq]; exact right_mem_affineSpan_pair ℝ p a)
    have hs₁ : (lines p).card = A.card := card_image_of_injOn hinj
    have hs₂ : (blocked p).card ≤ T.card-1 := calc
      _ ≤ (T.erase p).card := card_image_le
      _ = _ := card_erase_of_mem hp
    have hl := le_card_sdiff (blocked p) (lines p)
    dsimp only [G]
    omega
  have disj : (T : Set ℝ²).PairwiseDisjoint G := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro l hl hl'
    obtain ⟨a,ha,he,honly⟩ := good hp hl
    obtain ⟨b,hb,he',_⟩ := good hq hl'
    exact hpq (honly q hq (he' ▸ left_mem_affineSpan_pair ℝ q b)).symm
  change T.card * (A.card - (T.card-1)) ≤ _
  calc
    _ = ∑ _p ∈ T, (A.card-(T.card-1)) := by simp
    _ ≤ ∑ p ∈ T,(G p).card := sum_le_sum size
    _ = (T.biUnion G).card := (card_biUnion disj).symm
    _ ≤ _ := card_le_card (fun l hl => by
      obtain ⟨p,hp,hG⟩ := mem_biUnion.mp hl
      exact ordinary hp hG)


lemma away_erase (B : Finset ℝ²) (x : ℝ²) :
    ((ordinaryLines (B.erase x)).filter fun L => x ∉ L) =
      ((ordinaryLines B).filter fun L => x ∉ L) := by
  classical
  ext L
  simp only [mem_filter]
  by_cases hx : x ∈ L
  · simp [hx]
  simp only [not_false_eq_true, hx, and_true]
  apply ordinaryLines_eq.trans
  rw [ordinaryLines_eq]
  have heq : (((B.erase x : Finset ℝ²) : Set ℝ²) ∩ (L : Set ℝ²)) =
      ((B : Set ℝ²) ∩ (L : Set ℝ²)) := by
    ext q
    simp only [Set.mem_inter_iff, mem_coe, mem_erase]
    constructor
    · exact fun h => ⟨h.1.2,h.2⟩
    · exact fun h => ⟨⟨fun he => hx (he ▸ h.2),h.1⟩,h.2⟩
  rw [heq]

lemma away_edit (B s : Finset ℝ²) (x : ℝ²)
    (h : s = B.erase x ∨ s = insert x B) :
    ((ordinaryLines s).filter fun L => x ∉ L) =
      ((ordinaryLines B).filter fun L => x ∉ L) := by
  rcases h with rfl | rfl
  · exact away_erase B x
  · by_cases hx : x ∈ B
    · simp [hx]
    · simpa [hx] using (away_erase (insert x B) x).symm

lemma balanced_edit : ∀ (B s : Finset ℝ²) (x a b : ℝ²) (m : ℕ), a ≠ b →
    B.card = 2*m → (B.filter (· ∈ line[ℝ,a,b])).card = m →
    (s = B.erase x ∨ s = insert x B) →
    m + ((ordinaryLines s).filter fun L => x ∈ L).card ≤
      (ordinaryLines s).card + ((ordinaryLines B).filter fun L => x ∈ L).card := by
  intro B s x a b m _h hB hA hedit
  let L := line[ℝ,a,b]
  have split := Finset.card_filter_add_card_filter_not (s := B) (fun p => p ∈ L)
  have hout : (B.filter fun p => p ∉ L).card = m := by
    change (B.filter fun p => p ∈ L).card = m at hA
    omega
  have hmix := mixed B L
  change (B.filter fun p => p ∉ L).card *
      ((B.filter fun p => p ∈ L).card - ((B.filter fun p => p ∉ L).card-1)) ≤ _ at hmix
  change (B.filter fun p => p ∈ L).card = m at hA
  rw [hout,hA] at hmix
  have lower : m ≤ (ordinaryLines B).card := by
    cases m with
    | zero => omega
    | succ m => simpa using hmix
  have counts := congrArg Finset.card (away_edit B s x hedit)
  have p₁ := Finset.card_filter_add_card_filter_not (s := ordinaryLines B) (fun L => x ∈ L)
  have p₂ := Finset.card_filter_add_card_filter_not (s := ordinaryLines s) (fun L => x ∈ L)
  omega

/-- In residue three the sparse models in Green and Tao, Propositions
2.1(iii) and 2.3, all delete a direction. The incident tangents and
pairs of polygon vertices partition the polygon. Representatives may
change affine chart to keep the missing point finite. -/
def H1 : Prop := ∃ C N : ℕ, ∀ s : Finset ℝ², N ≤ s.card → s.card % 4 = 3 →
    ¬ Collinear ℝ (s : Set ℝ²) → (ordinaryLines s).card + C ≤ s.card →
    ∃ (P B : Finset ℝ²) (x a b : ℝ²) (m : ℕ),
      P.card = s.card ∧ (ordinaryLines P).card = (ordinaryLines s).card ∧ a ≠ b ∧
      B.card = 2*m ∧ (B.filter (· ∈ line[ℝ,a,b])).card = m ∧
      let e := ((ordinaryLines B).filter fun L => x ∈ L).card
      let t := ((ordinaryLines P).filter fun L => x ∈ L).card
      (x ∈ B ∧ P = B.erase x ∧ e ≤ 2 ∧ 2*t+e = m)

/-- In residue one Proposition 2.1(ii,iv) also allows addition of the
center. No old tangent goes through the center, and half the directions
create new ordinary lines. -/
def H2 : Prop := ∃ C N : ℕ, ∀ s : Finset ℝ², N ≤ s.card → s.card % 4 = 1 →
    ¬ Collinear ℝ (s : Set ℝ²) → (ordinaryLines s).card + C ≤ s.card →
    ∃ (P B : Finset ℝ²) (x a b : ℝ²) (m : ℕ),
      P.card = s.card ∧ (ordinaryLines P).card = (ordinaryLines s).card ∧ a ≠ b ∧
      B.card = 2*m ∧ (B.filter (· ∈ line[ℝ,a,b])).card = m ∧
      let e := ((ordinaryLines B).filter fun L => x ∈ L).card
      let t := ((ordinaryLines P).filter fun L => x ∈ L).card
      (x ∈ B ∧ P = B.erase x ∧ e ≤ 2 ∧ 2*t+e = m) ∨ (x ∉ B ∧ P = insert x B ∧ e = 0 ∧ m ≤ 2*t)

theorem main : H1 → H2 → type_of% @Erdos210.erdos_210.variants.green_tao_odd := by
  rintro ⟨C₃,N₃,h₃⟩ ⟨C₁,N₁,h₁⟩
  apply eventually_atTop.mpr
  refine ⟨max 3 (max (max N₃ N₁) (4 * max C₃ C₁)), ?_⟩
  intro n hn hodd
  obtain ⟨k,hodd⟩ := hodd
  apply (Erdos210.le_f_iff (by omega)).2
  intro s hs hc
  by_contra! few
  obtain ⟨P,B,x,a,b,m,hP,hOrd,hab,hB,hline,hcase⟩ :
    ∃ (P B : Finset ℝ²) (x a b : ℝ²) (m : ℕ),
      P.card = s.card ∧ (ordinaryLines P).card = (ordinaryLines s).card ∧ a ≠ b ∧
      B.card = 2*m ∧ (B.filter (· ∈ line[ℝ,a,b])).card = m ∧
      let e := ((ordinaryLines B).filter fun L => x ∈ L).card
      let t := ((ordinaryLines P).filter fun L => x ∈ L).card
      (x ∈ B ∧ P = B.erase x ∧ e ≤ 2 ∧ 2*t+e = m) ∨ (x ∉ B ∧ P = insert x B ∧ e = 0 ∧ m ≤ 2*t) := by
    by_cases hr : s.card % 4 = 3
    · obtain ⟨P,B,x,a,b,m,hP,hO,hab,hB,hL,h⟩ := h₃ s (by omega) hr hc (by omega)
      exact ⟨P,B,x,a,b,m,hP,hO,hab,hB,hL,Or.inl h⟩
    · exact h₁ s (by omega) (by omega) hc (by omega)
  dsimp only at hcase
  rcases hcase with ⟨hx,hdel,he,ht⟩ | ⟨hx,hadd,he,ht⟩
  · have h := balanced_edit B P x a b m hab hB hline (Or.inl hdel)
    have hsize := Finset.card_erase_of_mem hx
    rw [← hdel, hP, hs, hB] at hsize
    omega
  · have h := balanced_edit B P x a b m hab hB hline (Or.inr hadd)
    have hsize := Finset.card_insert_of_notMem hx
    rw [← hadd, hP, hs, hB] at hsize
    omega

end OMA.R_Erdos210_erdos_210_variants_green_tao_odd_R1
