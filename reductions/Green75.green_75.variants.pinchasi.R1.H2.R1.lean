import OMAReductions.R_Green75_green_75_variants_pinchasi_R1

/-!
Pinchasi, Lines with Many Points on Both Sides, sections 2 and 3.
Sorting the pair slopes of an actual configuration produces a finite crossing
table. Collinear triples tie; the outer crossing of every other ordered triple
lies strictly between the inner two. The table records both strict side counts.
-/
namespace OMA.R_Green75_green_75_variants_pinchasi_R1_H2_R1
open Finset
open scoped Classical

/-- Index a finite configuration in order of increasing first coordinate. -/
private theorem indexByX (A : Finset (ℝ × ℝ))
    (inj : Set.InjOn Prod.fst (↑A : Set (ℝ × ℝ))) :
    ∃ e : Fin A.card ≃ A, StrictMono (fun i => (e i).val.1) := by
  classical
  let X := A.image Prod.fst
  let f (p : A) : X := ⟨p.val.1, mem_image_of_mem _ p.property⟩
  have fi : Function.Injective f := by
    intro p q h
    exact Subtype.ext (inj p.property q.property (congrArg Subtype.val h))
  have fs : Function.Surjective f := by
    intro z
    obtain ⟨p,hp,he⟩ := mem_image.mp z.property
    exact ⟨⟨p,hp⟩,Subtype.ext he⟩
  let E := Equiv.ofBijective f ⟨fi,fs⟩
  let O := X.orderIsoOfFin (show X.card = A.card from card_image_of_injOn inj)
  refine ⟨O.toEquiv.trans E.symm,?_⟩
  intro i j hij
  have id (i) : (E.symm (O i)).val.1 = (O i).val := congrArg Subtype.val (E.apply_symm_apply _)
  change (E.symm (O i)).val.1 < (E.symm (O j)).val.1
  rw [id,id]
  exact O.strictMono hij

private theorem weightedBetween {a b c u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : c*(u+v) = a*u+b*v) :
    (a < c ∧ c < b) ∨ (b < c ∧ c < a) ∨ (a=c ∧ c=b) := by
  have strict {x y z s t : ℝ} (hs : 0 < s) (ht : 0 < t)
      (eqn : z*(s+t)=x*s+y*t) (xy : x < y) : x < z ∧ z < y := by
    have left : (z-x)*(s+t)=(y-x)*t := by linear_combination eqn
    have right : (y-z)*(s+t)=(y-x)*s := by linear_combination -eqn
    exact ⟨sub_pos.mp ((mul_pos_iff_of_pos_right (add_pos hs ht)).mp
      (left.trans_gt (mul_pos (sub_pos.mpr xy) ht))),
      sub_pos.mp ((mul_pos_iff_of_pos_right (add_pos hs ht)).mp
      (right.trans_gt (mul_pos (sub_pos.mpr xy) hs)))⟩
  rcases lt_trichotomy a b with lt|eq|gt
  · exact Or.inl (strict hu hv h lt)
  · subst b
    have z : (c-a)*(u+v)=0 := by linear_combination h
    have eq : c=a := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_right (add_pos hu hv).ne')
    exact Or.inr (Or.inr ⟨eq.symm,eq⟩)
  · exact Or.inr (Or.inl (strict hv hu (by simpa only [add_comm v u,add_comm (b*v) (a*u)] using h) gt))

/-- Real slopes can be replaced by their positions in a finite sorted set. -/
private theorem integerRanks {n : ℕ} (s : Fin n → Fin n → ℝ) :
    ∃ w : Fin n → Fin n → ℕ, ∀ i j k l, w i j < w k l ↔ s i j < s k l := by
  classical
  let E := (univ : Finset (Fin n × Fin n)).image (fun z => s z.1 z.2)
  let v (i j : Fin n) : E := ⟨s i j,mem_image.mpr ⟨(i,j),mem_univ _,rfl⟩⟩
  let O := E.orderIsoOfFin rfl
  exact ⟨fun i j => (O.symm (v i j)).val,fun i j k l => O.symm.lt_iff_lt⟩

private theorem filteredCard {α : Type*} (A : Finset α) {n : ℕ} (e : Fin n ≃ A)
    (P : α → Prop) [DecidablePred P] :
    (univ.filter fun i : Fin n => P (e i).val).card = (A.filter P).card := by
  classical
  apply card_bij (fun i _ => (e i).val)
  · intro i hi
    exact mem_filter.mpr ⟨(e i).property,(mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact e.injective (Subtype.ext h)
  · intro p hp
    let z : A := ⟨p,(mem_filter.mp hp).1⟩
    refine ⟨e.symm z,mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
    · simpa [z] using (mem_filter.mp hp).2
    · simp [z]


/-- The discrete sweep construction. The event labels are integers, equal
events may contain disjoint reversals, and simultaneous collinear points
form a single reversal. The threshold may be chosen after seeing the table. -/
def H1 : Prop := ∀ (n d : ℕ), 3 ≤ n → ∀ w : Fin n → Fin n → ℕ,
    (∀ i j, w i j = w j i) →
    (∀ i j k, i < j → j < k →
      (w i j < w i k ∧ w i k < w j k) ∨ (w j k < w i k ∧ w i k < w i j) ∨
      (w i j = w i k ∧ w i k = w j k)) →
    (∀ i j, i < j → d ≤ (((univ.filter fun k : Fin n =>
        (i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j)).card : ℤ) - ((univ.filter fun k : Fin n =>
        (i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k)).card : ℤ)).natAbs) →
    Relation.ReflTransGen (fun u v : List (Fin n) =>
      ∃ pre block post : List (Fin n), 2 ≤ block.length ∧ block.Pairwise (· < ·) ∧
        d ≤ ((pre.length : ℤ) - (post.length : ℤ)).natAbs ∧
        u = pre ++ block ++ post ∧ v = pre ++ block.reverse ++ post)
      (List.finRange n) (List.finRange n).reverse

/-- Pinchasi's centered-block bound for allowable sequences. Only integer
permutations and the distances of reversed blocks from the centre occur. -/
def H2 : Prop := ∃ C : ℝ, ∀ n d : ℕ, 3 ≤ n →
    Relation.ReflTransGen (fun u v : List (Fin n) =>
      ∃ pre block post : List (Fin n), 2 ≤ block.length ∧ block.Pairwise (· < ·) ∧
        d ≤ ((pre.length : ℤ) - (post.length : ℤ)).natAbs ∧
        u = pre ++ block ++ post ∧ v = pre ++ block.reverse ++ post)
      (List.finRange n) (List.finRange n).reverse →
    (d : ℝ) ≤ C * Real.log (Real.log n)


theorem main : H1 → H2 → OMA.R_Green75_green_75_variants_pinchasi_R1.H2 := by
  classical
  rintro sweep ⟨C,center⟩
  refine ⟨C,?_⟩
  intro A hn inj
  let n := A.card
  obtain ⟨e,mon⟩ := indexByX A inj
  let x (i : Fin n) := (e i).val.1
  let y (i : Fin n) := (e i).val.2
  change StrictMono x at mon
  let s (i j : Fin n) := (y j-y i)/(x j-x i)
  have smul (i j : Fin n) : s i j * (x j-x i) = y j-y i := by
    by_cases eq : i=j
    · simp [eq]
    · exact div_mul_cancel₀ _ (sub_ne_zero.mpr (mon.injective.ne (Ne.symm eq)))
  obtain ⟨w,rank⟩ := integerRanks s
  have same (i j k l : Fin n) (h : s i j = s k l) : w i j = w k l := by
    apply le_antisymm
    · exact le_of_not_gt (fun hh => h.not_gt ((rank k l i j).mp hh))
    · exact le_of_not_gt (fun hh => h.not_lt ((rank i j k l).mp hh))
  have sym i j : w i j = w j i := by
    apply same
    dsimp [s]
    rw [← neg_div_neg_eq,neg_sub,neg_sub]
  have middle i j k (ij : i < j) (jk : j < k) :
      (w i j < w i k ∧ w i k < w j k) ∨ (w j k < w i k ∧ w i k < w i j) ∨
      (w i j = w i k ∧ w i k = w j k) := by
    have v : s i k * ((x j-x i)+(x k-x j)) = s i j*(x j-x i)+s j k*(x k-x j) := by
      linear_combination smul i k - smul i j - smul j k
    rcases weightedBetween (sub_pos.mpr (mon ij)) (sub_pos.mpr (mon jk)) v with h|h|h
    · exact Or.inl ⟨(rank ..).mpr h.1,(rank ..).mpr h.2⟩
    · exact Or.inr (Or.inl ⟨(rank ..).mpr h.1,(rank ..).mpr h.2⟩)
    · exact Or.inr (Or.inr ⟨same _ _ _ _ h.1,same _ _ _ _ h.2⟩)
  let U (i j : Fin n) := univ.filter fun k : Fin n =>
    (i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j)
  let D (i j : Fin n) := univ.filter fun k : Fin n =>
    (i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k)
  let cost (i j : Fin n) := ((U i j).card - ((D i j).card : ℤ)).natAbs
  let pairs := (univ : Finset (Fin n × Fin n)).filter (fun z => z.1 < z.2)
  have n3 : 3 ≤ n := hn
  have non : pairs.Nonempty := by
    refine ⟨(⟨0,by omega⟩,⟨1,by omega⟩),mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    exact Nat.zero_lt_one
  obtain ⟨⟨i,j⟩,hp,hm⟩ := pairs.exists_min_image (fun z => cost z.1 z.2) non
  have ij := (mem_filter.mp hp).2
  have steps := sweep n (cost i j) n3 w sym middle (fun a b ab => hm (a,b)
    (mem_filter.mpr ⟨mem_univ _,ab⟩))
  have bound := center n (cost i j) n3 steps
  let t := s i j
  have hit : y j-t*x j = y i-t*x i := by
    change y j-s i j*x j = y i-s i j*x i
    linear_combination -(smul i j)
  have diff (k : Fin n) : y k-t*x k-(y i-t*x i)=(s i k-t)*(x k-x i) := by
    linear_combination -(smul i k)
  have above (k : Fin n) : ((i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j)) ↔
      y i-t*x i < y k-t*x k := by
    rw [rank,rank,← sub_pos (a:=y k-t*x k) (b:=y i-t*x i),diff,mul_pos_iff]
    simp only [t,sub_pos,sub_neg,mon.lt_iff_lt]
    tauto
  have below (k : Fin n) : ((i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k)) ↔
      y k-t*x k < y i-t*x i := by
    rw [rank,rank,← sub_neg (a:=y k-t*x k) (b:=y i-t*x i),diff,mul_neg_iff]
    simp only [t,sub_pos,sub_neg,mon.lt_iff_lt]
    tauto
  have au : (U i j).card = (A.filter fun z => y i-t*x i < z.2-t*z.1).card := by
    rw [← filteredCard A e (fun z => y i-t*x i < z.2-t*z.1)]
    congr 1
    ext k
    simp only [U,mem_filter,mem_univ,true_and]
    exact above k
  have ad : (D i j).card = (A.filter fun z => z.2-t*z.1 < y i-t*x i).card := by
    rw [← filteredCard A e (fun z => z.2-t*z.1 < y i-t*x i)]
    congr 1
    ext k
    simp only [D,mem_filter,mem_univ,true_and]
    exact below k
  refine ⟨(e i).val,(e i).property,(e j).val,(e j).property,mon ij,t,hit,?_⟩
  change ((|((A.filter fun z => y i-t*x i < z.2-t*z.1).card : ℤ) -
    ((A.filter fun z => z.2-t*z.1 < y i-t*x i).card : ℤ)| : ℤ) : ℝ) ≤ _
  rw [← au,← ad,← Int.natCast_natAbs,Int.cast_natCast]
  exact bound

end OMA.R_Green75_green_75_variants_pinchasi_R1_H2_R1
