import FormalConjectures.ErdosProblems.«19»

/-!
A finite certificate proof of the Erdős–Faber–Lovász theorem for fewer than ten
cliques. The mathematical result is due to N. Hindman, Canadian Journal of
Mathematics 33 (1981), 563–570, doi:10.4153/CJM-1981-046-9.

Color the supports of shared vertices on the set of clique indices. Two
supports intersect in at most one point. Keep just the supports of size at
least three and adjoin every compatible pair. Each row below gives an explicit
coloring of this completion. For each possible new large support the row also
gives a new row and a permutation witnessing the extension. The kernel checks
the empty initial state, every required extension, and disjointness in every
color class. Thus induction on the number of large supports proves coverage.
The independent enumeration produces 3, 5, 10, 24, 69 and 384 rows for four
through nine indices respectively. The pinned source handles at most three.

A row lists the large support masks, the color classes of all completed
supports, and triples (added mask, destination row, point permutation).
Each point's image occupies one low-to-high four-bit digit of the permutation.
-/

-- Credit: @zarnab222-dev

open Erdos19 Finset
namespace E19Transfer

private theorem support_transfer {V : Type*} {n : ℕ} (C : EFLConfig V n) (e : Fin n ≃ Fin n) :
    ∃ (S : V → Finset (Fin n)) (H : Finset (Finset (Fin n))),
      (∀ v i, e i ∈ S v ↔ v ∈ C.A i) ∧
      (∀ u v, u ≠ v → (S u ∩ S v).card ≤ 1) ∧
      (∀ A, A ∈ H ↔ ∃ v, S v = A ∧ 2 ≤ A.card) ∧
      (∀ A ∈ H, 2 ≤ A.card) ∧
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) ∧
      ((∃ c : H → Fin n, ∀ A B : H, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B) →
        C.graph.chromaticNumber = n) := by
  classical
  let S (v : V) := ((univ : Finset (Fin n)).filter (fun i => v ∈ C.A i)).map e.toEmbedding
  let U := (univ : Finset (Fin n)).biUnion C.A
  let H := (U.image S).filter (fun A => 2 ≤ A.card)
  have mem (v : V) (i : Fin n) : e i ∈ S v ↔ v ∈ C.A i := by simp [S]
  have inv (v : V) (i : Fin n) : i ∈ S v ↔ v ∈ C.A (e.symm i) := by
    simpa only [e.apply_symm_apply] using mem v (e.symm i)
  have small (u v : V) (hne : u ≠ v) : (S u ∩ S v).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hn
    have h := C.inter_le (e.symm i) (e.symm j) (fun eq => hn (e.symm.injective eq))
    have hu : u ∈ C.A (e.symm i) ∩ C.A (e.symm j) :=
      mem_inter.mpr ⟨(inv u i).mp (mem_inter.mp hi).1,(inv u j).mp (mem_inter.mp hj).1⟩
    have hv : v ∈ C.A (e.symm i) ∩ C.A (e.symm j) :=
      mem_inter.mpr ⟨(inv v i).mp (mem_inter.mp hi).2,(inv v j).mp (mem_inter.mp hj).2⟩
    exact hne (card_le_one.mp h u hu v hv)
  have allU (v : V) : v ∈ U := by
    obtain ⟨i,hi⟩ := C.cover v
    exact mem_biUnion.mpr ⟨i,mem_univ _,hi⟩
  have memH (A) : A ∈ H ↔ ∃ v, S v = A ∧ 2 ≤ A.card := by
    constructor
    · intro h
      obtain ⟨v,_,hv⟩ := mem_image.mp (mem_filter.mp h).1
      exact ⟨v,hv,(mem_filter.mp h).2⟩
    · rintro ⟨v,rfl,hv⟩
      exact mem_filter.mpr ⟨mem_image_of_mem S (allU v),hv⟩
  have sz (A) (h : A ∈ H) : 2 ≤ A.card := (mem_filter.mp h).2
  have linear (A) (hA : A ∈ H) (B) (hB : B ∈ H) (hne : A ≠ B) : (A ∩ B).card ≤ 1 := by
    obtain ⟨u,rfl,_⟩ := (memH A).mp hA
    obtain ⟨v,rfl,_⟩ := (memH B).mp hB
    exact small u v (fun eq => hne (congrArg S eq))
  have shared (v : V) (h : C.IsShared v) : S v ∈ H := by
    obtain ⟨i,j,hn,hi,hj⟩ := h
    apply (memH _).mpr
    exact ⟨v,rfl,one_lt_card.mpr ⟨e i,(mem v i).mpr hi,e j,(mem v j).mpr hj,
      fun eq => hn (e.injective eq)⟩⟩
  refine ⟨S,H,mem,small,memH,sz,linear,?_⟩
  rintro ⟨c,hc⟩
  let col (v : V) := if h : S v ∈ H then c ⟨S v,h⟩ else e (C.cover v).choose
  refine le_antisymm (C.colorable_of_sharedColoring col ?_).chromaticNumber_le C.le_chromaticNumber
  intro i u v hu hv su sv heq
  by_contra hne
  have huH := shared u su
  have hvH := shared v sv
  have unequal : S u ≠ S v := by
    intro eq
    have bound := small u v hne
    rw [← eq,inter_self] at bound
    have := sz _ huH
    omega
  have diff := hc ⟨S u,huH⟩ ⟨S v,hvH⟩ (fun eq => unequal (congrArg Subtype.val eq))
    ⟨e i,mem_inter.mpr ⟨(mem u i).mpr hu,(mem v i).mpr hv⟩⟩
  exact diff (by simpa only [col,dif_pos huH,dif_pos hvH] using heq)

end E19Transfer

open Finset

namespace E19Catalog

/-- A state admits its large supports and all pairs compatible with them. -/
def eligible {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) : Prop :=
  A ∈ F ∨ (A.card = 2 ∧ ∀ U ∈ F, (A ∩ U).card ≤ 1)

/-- Following one transition per large support reaches a relabeling of the entire family. -/
theorem reaches_large_family {n : ℕ} {ι : Type*} (states : ι → Finset (Finset (Fin n)))
    (initial : ∃ i, states i = ∅)
    (step : ∀ (i : ι) (B : Finset (Fin n)), 3 ≤ B.card → (∀ U ∈ states i, (B ∩ U).card ≤ 1) →
      ∃ (j : ι) (e : Fin n ≃ Fin n),
        states j = (insert B (states i)).image (Finset.map e.toEmbedding))
    (J : Finset (Finset (Fin n)))
    (large : ∀ B ∈ J, 3 ≤ B.card)
    (linear : ∀ A ∈ J, ∀ B ∈ J, A ≠ B → (A ∩ B).card ≤ 1) :
    ∃ (i : ι) (e : Fin n ≃ Fin n), states i = J.image (Finset.map e.toEmbedding) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    obtain ⟨i, hi⟩ := initial
    exact ⟨i, Equiv.refl _, by simpa using hi⟩
  | @insert B J hBJ ih =>
    have sub : J ⊆ insert B J := Finset.subset_insert _ _
    obtain ⟨i,e,hi⟩ := ih (fun U hU => large U (sub hU))
      (fun U hU V hV => linear U (sub hU) V (sub hV))
    have sizeB : 3 ≤ (B.map e.toEmbedding).card := by
      simpa using large B (Finset.mem_insert_self ..)
    have fits : ∀ U ∈ states i, (B.map e.toEmbedding ∩ U).card ≤ 1 := by
      intro U hU
      rw [hi] at hU
      obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hU
      rw [← Finset.map_inter, Finset.card_map]
      exact linear B (Finset.mem_insert_self ..) V (sub hV) (fun h => hBJ (h ▸ hV))
    obtain ⟨j,g,hj⟩ := step i (B.map e.toEmbedding) sizeB fits
    refine ⟨j, e.trans g, ?_⟩
    rw [hj, hi, ← Finset.image_insert, Finset.image_image]
    simp only [Function.comp_def, Finset.map_map]
    rfl

/-- Certified coverage and proper colorings of the catalog states imply a proper coloring
of all intersecting supports in every linear family of supports of size at least two. -/
theorem color_of_catalog {n : ℕ} {ι : Type*} (states : ι → Finset (Finset (Fin n)))
    (initial : ∃ i, states i = ∅)
    (step : ∀ (i : ι) (B : Finset (Fin n)), 3 ≤ B.card → (∀ U ∈ states i, (B ∩ U).card ≤ 1) →
      ∃ (j : ι) (e : Fin n ≃ Fin n),
        states j = (insert B (states i)).image (Finset.map e.toEmbedding))
    (colored : ∀ i, ∃ c : Finset (Fin n) → Fin n, ∀ A B,
      eligible (states i) A → eligible (states i) B → A ≠ B →
      (A ∩ B).Nonempty → c A ≠ c B)
    (H : Finset (Finset (Fin n))) (size : ∀ A ∈ H, 2 ≤ A.card)
    (linear : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) :
    ∃ c : H → Fin n, ∀ A B : H, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  let J := H.filter (fun A => 3 ≤ A.card)
  obtain ⟨i,e,hi⟩ := reaches_large_family states initial step J
    (fun B hB => (Finset.mem_filter.mp hB).2)
    (fun A hA B hB => linear A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1)
  obtain ⟨c,proper⟩ := colored i
  have included (A : H) : eligible (states i) (A.val.map e.toEmbedding) := by
    rw [hi]
    by_cases h : 3 ≤ A.val.card
    · exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨A.property,h⟩))
    · refine Or.inr ⟨?_,?_⟩
      · rw [Finset.card_map]
        have := size _ A.property
        omega
      · intro U hU
        obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hU
        obtain ⟨hBH,hbig⟩ := Finset.mem_filter.mp hB
        rw [← Finset.map_inter, Finset.card_map]
        exact linear _ A.property B hBH (fun he => h (he ▸ hbig))
  refine ⟨fun A => c (A.val.map e.toEmbedding), ?_⟩
  intro A B hne hmeet
  exact proper _ _ (included A) (included B)
    (fun h => hne (Subtype.ext (Finset.map_injective _ h)))
    (by rw [← Finset.map_inter]; exact hmeet.map)

end E19Catalog

open Finset
namespace E19Mask

def encode {n : ℕ} (A : Finset (Fin n)) : ℕ :=
  A.fold (· ||| ·) 0 (fun i => 2 ^ i.val)

def decode (n mask : ℕ) : Finset (Fin n) :=
  univ.filter (fun i => mask.testBit i.val)

def count (mask : ℕ) : ℕ := mask.bitIndices.length

theorem testBit_encode_nat {n : ℕ} (A : Finset (Fin n)) (j : ℕ) :
    (encode A).testBit j = true ↔ ∃ i ∈ A, i.val = j := by
  induction A using Finset.induction_on with
  | empty => simp [encode]
  | @insert a A ha ih =>
    rw [show encode (insert a A) = 2^a.val ||| encode A from fold_insert ha,
      Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,ih]
    simp

theorem testBit_encode {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    (encode A).testBit i.val = true ↔ i ∈ A := by
  rw [testBit_encode_nat]
  exact ⟨fun ⟨j,hj,e⟩ => (Fin.ext e : j = i) ▸ hj,fun hi => ⟨i,hi,rfl⟩⟩

theorem encode_lt {n : ℕ} (A : Finset (Fin n)) : encode A < 2^n := by
  induction A using Finset.induction_on with
  | empty => simp [encode]
  | @insert a A ha ih =>
    rw [show encode (insert a A) = 2^a.val ||| encode A from fold_insert ha]
    exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) a.isLt) ih

theorem decode_encode {n : ℕ} (A : Finset (Fin n)) : decode n (encode A) = A := by
  ext i
  simp [decode,testBit_encode]

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro A B eq
  simpa only [decode_encode] using congrArg (decode n) eq

theorem encode_decode {n mask : ℕ} (lt : mask < 2^n) : encode (decode n mask) = mask := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  rw [testBit_encode_nat]
  by_cases hj : j < n
  · constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro hb
      exact ⟨⟨j,hj⟩,mem_filter.mpr ⟨mem_univ _,hb⟩,rfl⟩
  · have h := Nat.testBit_lt_two_pow (lt.trans_le (Nat.pow_le_pow_right (by decide) (by omega : n ≤ j)))
    rw [h]
    simp only [Bool.false_eq_true,iff_false,not_exists]
    rintro i ⟨hi,he⟩
    have := i.isLt
    omega

theorem encode_inter {n : ℕ} (A B : Finset (Fin n)) :
    encode (A ∩ B) = encode A &&& encode B := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_and,Bool.and_eq_true,testBit_encode_nat,testBit_encode_nat,testBit_encode_nat]
  constructor
  · rintro ⟨i,hi,e⟩
    exact ⟨⟨i,(mem_inter.mp hi).1,e⟩,⟨i,(mem_inter.mp hi).2,e⟩⟩
  · rintro ⟨⟨i,hi,e⟩,⟨k,hk,f⟩⟩
    have eq : i = k := Fin.ext (e.trans f.symm)
    exact ⟨i,mem_inter.mpr ⟨hi,eq ▸ hk⟩,e⟩

theorem count_encode {n : ℕ} (A : Finset (Fin n)) : count (encode A) = A.card := by
  have eq : (encode A).bitIndices.toFinset = A.image Fin.val := by
    ext j
    simp only [List.mem_toFinset,Nat.mem_bitIndices,testBit_encode_nat,mem_image]
  have h := congrArg Finset.card eq
  simpa only [count,List.card_toFinset,List.dedup_eq_self.mpr Nat.bitIndices_nodup,
    card_image_of_injective _ Fin.val_injective] using h

theorem encode_eq_zero {n : ℕ} (A : Finset (Fin n)) : encode A = 0 ↔ A = ∅ := by
  have zero : encode (∅ : Finset (Fin n)) = 0 := rfl
  rw [← zero,encode_injective.eq_iff]

theorem encode_nonzero_iff {n : ℕ} (A : Finset (Fin n)) : encode A ≠ 0 ↔ A.Nonempty := by
  rw [ne_eq,encode_eq_zero,nonempty_iff_ne_empty]

theorem inter_nonzero_iff {n : ℕ} (A B : Finset (Fin n)) :
    (encode A &&& encode B) ≠ 0 ↔ (A ∩ B).Nonempty := by
  rw [← encode_inter,encode_nonzero_iff]

theorem encode_pair {n : ℕ} (i j : Fin n) (hne : i ≠ j) :
    encode {i,j} = 2^i.val ||| 2^j.val := by
  simp [encode,fold_insert,hne]

theorem pair_mask_iff {n : ℕ} (A : Finset (Fin n)) :
    A.card = 2 ↔ ∃ i j : Fin n, i < j ∧ encode A = 2^i.val ||| 2^j.val := by
  constructor
  · intro h
    obtain ⟨i,j,hn,rfl⟩ := card_eq_two.mp h
    rcases lt_or_gt_of_ne hn with lo|hi
    · exact ⟨i,j,lo,encode_pair i j hn⟩
    · exact ⟨j,i,hi,(encode_pair i j hn).trans (Nat.or_comm _ _)⟩
  · rintro ⟨i,j,lo,e⟩
    have eq : A = {i,j} := encode_injective (e.trans (encode_pair i j lo.ne).symm)
    rw [eq,card_pair lo.ne]

theorem power_of_two_iff {n : ℕ} (A : Finset (Fin n)) :
    (encode A).isPowerOfTwo ↔ A.card = 1 := by
  constructor
  · rintro ⟨k,hk⟩
    rw [← count_encode,hk,count,Nat.bitIndices_two_pow]
    rfl
  · intro h
    obtain ⟨i,rfl⟩ := card_eq_one.mp h
    exact ⟨i.val,by simp [encode]⟩

theorem two_le_iff {n : ℕ} (A : Finset (Fin n)) :
    2 ≤ A.card ↔ (encode A &&& (encode A - 1)) ≠ 0 := by
  by_cases hz : encode A = 0
  · have he := (encode_eq_zero A).mp hz
    simp [he,encode]
  · rw [ne_eq,Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hz,power_of_two_iff]
    have ha : A.card ≠ 0 := fun h => hz ((encode_eq_zero A).mpr (card_eq_zero.mp h))
    omega

theorem two_le_inter_iff {n : ℕ} (A B : Finset (Fin n)) :
    2 ≤ (A ∩ B).card ↔
      ((encode A &&& encode B) &&& ((encode A &&& encode B) - 1)) ≠ 0 := by
  rw [two_le_iff,encode_inter]

def permute (n : ℕ) (pos : ℕ → ℕ) (mask : ℕ) : ℕ :=
  (decode n mask).fold (· ||| ·) 0 (fun i => 2 ^ pos i.val)

theorem encode_map {n : ℕ} (A : Finset (Fin n)) (e : Fin n ≃ Fin n)
    (pos : ℕ → ℕ) (hp : ∀ i : Fin n, pos i.val = (e i).val) :
    encode (A.map e.toEmbedding) = permute n pos (encode A) := by
  rw [encode,fold_map,permute,decode_encode]
  apply fold_congr
  intro i hi
  simp [hp]

theorem equiv_of_range_image {n : ℕ} (pos : ℕ → ℕ)
    (h : (range n).image pos = range n) :
    ∃ e : Fin n ≃ Fin n, ∀ i : Fin n, pos i.val = (e i).val := by
  have bound (i : Fin n) : pos i.val < n := mem_range.mp
    (h ▸ mem_image_of_mem pos (mem_range.mpr i.isLt) : pos i.val ∈ range n)
  let f (i : Fin n) : Fin n := ⟨pos i.val,bound i⟩
  have surj : Function.Surjective f := by
    intro j
    have hj : j.val ∈ (range n).image pos := h.symm ▸ mem_range.mpr j.isLt
    obtain ⟨i,hi,eq⟩ := mem_image.mp hj
    exact ⟨⟨i,mem_range.mp hi⟩,Fin.ext eq⟩
  exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr surj,surj⟩,fun _ => rfl⟩

end E19Mask

open Finset
namespace E19Mask

def permuteFast (n : ℕ) (pos : ℕ → ℕ) (m : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k+1 =>
    let lower := permuteFast k pos m
    if m.testBit k then lower ||| (1 <<< pos k) else lower

private theorem testFast (n : ℕ) (pos : ℕ → ℕ) (m j : ℕ) :
    (permuteFast n pos m).testBit j = true ↔ ∃ i < n, m.testBit i = true ∧ pos i = j := by
  induction n with
  | zero => simp [permuteFast]
  | succ k ih =>
    rw [permuteFast]
    by_cases h : m.testBit k = true
    · simp only [if_pos h,Nat.testBit_or,Bool.or_eq_true,Nat.shiftLeft_eq,one_mul,
        Nat.testBit_two_pow,decide_eq_true_eq,ih]
      constructor
      · rintro (⟨i,hi,h1,h2⟩|hk)
        · exact ⟨i,by omega,h1,h2⟩
        · exact ⟨k,by omega,h,hk⟩
      · rintro ⟨i,hi,h1,h2⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
        · exact Or.inl ⟨i,hi,h1,h2⟩
        · exact Or.inr h2
    · rw [if_neg h,ih]
      constructor
      · rintro ⟨i,hi,h1,h2⟩
        exact ⟨i,by omega,h1,h2⟩
      · rintro ⟨i,hi,h1,h2⟩
        have ne : i ≠ k := fun eq => h (eq ▸ h1)
        exact ⟨i,by omega,h1,h2⟩

theorem permuteFast_eq (n : ℕ) (pos : ℕ → ℕ) (m : ℕ) :
    permuteFast n pos m = permute n pos m := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  have bits (A : Finset (Fin n)) :
      (A.fold (fun a b : ℕ => a ||| b) 0 (fun i : Fin n => 2 ^ pos i.val)).testBit j = true ↔
        ∃ i ∈ A, pos i.val = j := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert a A ha ih =>
      rw [fold_insert ha,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,ih]
      simp
  rw [testFast,permute,bits]
  constructor
  · rintro ⟨i,hi,h1,h2⟩
    exact ⟨⟨i,hi⟩,mem_filter.mpr ⟨mem_univ _,h1⟩,h2⟩
  · rintro ⟨i,hi,h2⟩
    exact ⟨i.val,i.isLt,(mem_filter.mp hi).2,h2⟩

def clear (m : ℕ) : ℕ := m &&& (m-1)

theorem count_clear (m : ℕ) : count (clear m) = count m - 1 := by
  induction m using Nat.binaryRec with
  | zero => simp [count,clear]
  | bit b m ih =>
    cases b
    · by_cases h : m = 0
      · subst m; simp [count,clear]
      have pred : Nat.bit false m - 1 = Nat.bit true (m-1) := by
        change 2*m-1 = 2*(m-1)+1
        omega
      have eq : clear (Nat.bit false m) = Nat.bit false (clear m) := by
        simp only [clear,pred,Nat.land_bit,Bool.false_and]
      simpa only [eq,count,Nat.bitIndices_bit_false,List.length_map] using ih
    · have pred : Nat.bit true m - 1 = Nat.bit false m := by
        change 2*m+1-1 = 2*m
        omega
      have eq : clear (Nat.bit true m) = Nat.bit false m := by
        simp only [clear,pred,Nat.land_bit,Bool.true_and,Nat.and_self]
      rw [eq]
      simp only [count,Nat.bitIndices_bit_true,Nat.bitIndices_bit_false,List.length_cons,
        List.length_map,Nat.add_sub_cancel]

theorem count_zero_iff (m : ℕ) : count m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have empty : m.bitIndices = [] := List.length_eq_zero_iff.mp h
    have s := Nat.sum_map_two_pow_bitIndices m
    simpa only [empty,List.map_nil,List.sum_nil] using s.symm
  · rintro rfl
    simp [count]

theorem clear_zero_test (m : ℕ) : (clear m == 0) = decide (count m ≤ 1) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq,decide_eq_true_eq,← count_zero_iff,count_clear]
  omega

theorem clear_twice_test (m : ℕ) : (clear (clear m) != 0) = decide (3 ≤ count m) := by
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne,decide_eq_true_eq,ne_eq,← count_zero_iff,count_clear,count_clear]
  omega

end E19Mask

namespace E19Cert

structure Row where
  blocks : List Nat
  groups : List (List Nat)
  extensions : List (Nat × Nat × Nat)
deriving Inhabited

def state (n : ℕ) (row : Row) : Finset (Finset (Fin n)) :=
  row.blocks.toFinset.image (E19Mask.decode n)

def bounded (n : ℕ) (row : Row) : Bool := row.blocks.all (· < 2^n)

def pos (w i : ℕ) : ℕ := (w >>> (4*i)) % 16

def permOK (n w : ℕ) : Bool :=
  (List.range n).all fun i => pos w i < n &&
    (List.range n).all (fun j => i == j || pos w i != pos w j)

def fits (blocks : List Nat) (b : Nat) : Bool :=
  blocks.all (fun u => E19Mask.count (b &&& u) ≤ 1)

def candidates (n : ℕ) (row : Row) : List Nat :=
  (List.range (2^n)).filter (fun b => 3 ≤ E19Mask.count b && fits row.blocks b)

def entryOK (n : ℕ) (rows : Array Row) (row : Row) (t : Nat × Nat × Nat) : Bool :=
  let (b,j,w) := t
  match rows[j]? with
  | none => false
  | some dst =>
    let mapped := (b :: row.blocks).map (E19Mask.permute n (pos w))
    permOK n w && mapped.all dst.blocks.contains && dst.blocks.all mapped.contains

def transitionsOK (n : ℕ) (rows : Array Row) (row : Row) : Bool :=
  row.extensions.map Prod.fst == candidates n row && row.extensions.all (entryOK n rows row)

end E19Cert

open Finset

namespace E19Cert

def colorOK (n : ℕ) (row : Row) : Bool :=
  let assigned (a : ℕ) := row.groups.any fun g => g.contains a
  decide (row.groups.length ≤ n) &&
    row.groups.all (fun g => g.all fun a => g.all fun b => a == b || (a &&& b) == 0) &&
    row.blocks.all assigned &&
    (List.range n).all (fun j => (List.range j).all fun i =>
      let pair := 2^i ||| 2^j
      !(fits row.blocks pair) || assigned pair)

theorem row_colored {n : ℕ} (hn : 0 < n) (row : Row) (hb : bounded n row = true)
    (hc : colorOK n row = true) :
    ∃ c : Finset (Fin n) → Fin n, ∀ A B, E19Catalog.eligible (state n row) A →
      E19Catalog.eligible (state n row) B → A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  simp only [colorOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨size,clean⟩,blocks⟩,pairs⟩ := hc
  have bound : ∀ u ∈ row.blocks, u < 2^n := by
    simpa only [bounded,List.all_eq_true,decide_eq_true_eq] using hb
  have covered (A : Finset (Fin n)) (hA : E19Catalog.eligible (state n row) A) :
      ∃ g ∈ row.groups, E19Mask.encode A ∈ g := by
    have casted : (row.groups.any fun g => g.contains (E19Mask.encode A)) = true := by
      rcases hA with big | ⟨hpair,linear⟩
      · obtain ⟨u,hu,rfl⟩ := mem_image.mp big
        have inList := List.mem_toFinset.mp hu
        rw [E19Mask.encode_decode (bound u inList)]
        exact blocks u inList
      · obtain ⟨i,j,lt,eq⟩ := (E19Mask.pair_mask_iff A).mp hpair
        have fit : fits row.blocks (E19Mask.encode A) = true := by
          simp only [fits,List.all_eq_true,decide_eq_true_eq]
          intro u hu
          have member : E19Mask.decode n u ∈ state n row :=
            mem_image_of_mem _ (List.mem_toFinset.mpr hu)
          have cap := linear _ member
          rw [← E19Mask.count_encode, E19Mask.encode_inter, E19Mask.encode_decode (bound u hu)] at cap
          exact cap
        have checked := pairs j.val (List.mem_range.mpr j.isLt) i.val (List.mem_range.mpr lt)
        rw [← eq,fit] at checked
        simpa using checked
    simpa only [List.any_eq_true,List.contains_iff_mem] using casted
  let atColor (A : Finset (Fin n)) (i : Fin n) :=
    ∃ h : i.val < row.groups.length, E19Mask.encode A ∈ row.groups[i.val]'h
  have colorExists (A) (hA : E19Catalog.eligible (state n row) A) : ∃ i, atColor A i := by
    obtain ⟨g,hg,ha⟩ := covered A hA
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
    exact ⟨⟨j,hj.trans_le size⟩,hj,eq ▸ ha⟩
  let c (A : Finset (Fin n)) : Fin n :=
    if h : E19Catalog.eligible (state n row) A then (colorExists A h).choose else ⟨0,hn⟩
  have assigned (A) (h : E19Catalog.eligible (state n row) A) : atColor A (c A) := by
    simpa only [c,dif_pos h] using (colorExists A h).choose_spec
  refine ⟨c,?_⟩
  intro A B a b ne meet eq
  obtain ⟨ha,haMem⟩ := assigned A a
  have bh : atColor B (c A) := eq ▸ assigned B b
  obtain ⟨_,hbMem⟩ := bh
  have pair := clean _ (List.getElem_mem ha) _ haMem _ hbMem
  rw [Bool.or_eq_true,beq_iff_eq,beq_iff_eq] at pair
  exact pair.elim (fun h => ne (E19Mask.encode_injective h)) ((E19Mask.inter_nonzero_iff A B).mpr meet)

end E19Cert

open Finset
namespace E19Cert

private theorem witness_equiv {n w : ℕ} (ok : permOK n w = true) :
    ∃ e : Fin n ≃ Fin n, ∀ i : Fin n, pos w i.val = (e i).val := by
  simp only [permOK,List.all_eq_true,List.mem_range,Bool.and_eq_true,decide_eq_true_eq,
    Bool.or_eq_true,beq_iff_eq,bne_iff_ne] at ok
  let f (i : Fin n) : Fin n := ⟨pos w i.val,(ok _ i.isLt).1⟩
  have inj : Function.Injective f := by
    intro i j he
    have eq : pos w i.val = pos w j.val := congrArg Fin.val he
    exact Fin.ext (((ok _ i.isLt).2 _ j.isLt).resolve_right (fun h => h eq))
  exact ⟨Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj), fun _ => rfl⟩

private theorem row_step {n : ℕ} (rows : Array Row) (i : Fin rows.size)
    (hb : bounded n rows[i] = true) (ok : transitionsOK n rows rows[i] = true)
    (B : Finset (Fin n)) (large : 3 ≤ B.card)
    (linear : ∀ U ∈ state n rows[i], (B ∩ U).card ≤ 1) :
    ∃ (j : Fin rows.size) (e : Fin n ≃ Fin n),
      state n rows[j] = (insert B (state n rows[i])).image (Finset.map e.toEmbedding) := by
  classical
  let row := rows[i]
  have boundedB (u) (hu : u ∈ row.blocks) : u < 2^n := by
    exact of_decide_eq_true (List.all_eq_true.mp hb u hu)
  have fitsB : fits row.blocks (E19Mask.encode B) = true := by
    apply List.all_eq_true.mpr
    intro u hu
    have member : E19Mask.decode n u ∈ state n row :=
      mem_image_of_mem _ (List.mem_toFinset.mpr hu)
    have cards := linear _ member
    rw [← E19Mask.count_encode, E19Mask.encode_inter, E19Mask.encode_decode (boundedB u hu)] at cards
    exact decide_eq_true cards
  have cand : E19Mask.encode B ∈ candidates n row := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (E19Mask.encode_lt B),
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true (by simpa only [E19Mask.count_encode] using large),fitsB⟩⟩
  obtain ⟨entries,valid⟩ := Bool.and_eq_true_iff.mp ok
  change (row.extensions.map Prod.fst == candidates n row) = true at entries
  rw [← beq_iff_eq.mp entries] at cand
  obtain ⟨⟨b,j,w⟩,he,eq⟩ := List.mem_map.mp cand
  change b = E19Mask.encode B at eq
  subst b
  have check := List.all_eq_true.mp valid _ he
  change entryOK n rows row (E19Mask.encode B,j,w) = true at check
  dsimp only [entryOK] at check
  split at check
  · contradiction
  · rename_i dst hd
    obtain ⟨hj,hdst⟩ := Array.getElem?_eq_some_iff.mp hd
    let idx : Fin rows.size := ⟨j,hj⟩
    have di : rows[idx] = dst := hdst
    obtain ⟨a,backward⟩ := Bool.and_eq_true_iff.mp check
    obtain ⟨pw,forward⟩ := Bool.and_eq_true_iff.mp a
    obtain ⟨e,hpos⟩ := witness_equiv pw
    refine ⟨idx,e,?_⟩
    rw [di]
    have decoder (u : ℕ) (hu : u ∈ E19Mask.encode B :: row.blocks) :
        E19Mask.decode n (E19Mask.permute n (pos w) u) = (E19Mask.decode n u).map e.toEmbedding := by
      have hlt : u < 2^n := (List.mem_cons.mp hu).elim
        (fun h => h ▸ E19Mask.encode_lt B) (boundedB u)
      have eq := E19Mask.encode_map (E19Mask.decode n u) e (pos w) hpos
      rw [E19Mask.encode_decode hlt] at eq
      rw [← eq,E19Mask.decode_encode]
    have seteq : insert B (state n row) =
        (E19Mask.encode B :: row.blocks).toFinset.image (E19Mask.decode n) := by
      simp [state,E19Mask.decode_encode]
    change state n dst = (insert B (state n row)).image (Finset.map e.toEmbedding)
    rw [seteq]
    ext A
    constructor
    · rintro hA
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hA
      have hm' := List.contains_iff_mem.mp (List.all_eq_true.mp backward m (List.mem_toFinset.mp hm))
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hm'
      exact mem_image.mpr ⟨_,mem_image_of_mem _ (List.mem_toFinset.mpr hu),(decoder u hu).symm⟩
    · intro hA
      obtain ⟨U,hU,rfl⟩ := mem_image.mp hA
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hU
      have hu' := List.mem_toFinset.mp hu
      have member := List.contains_iff_mem.mp
        (List.all_eq_true.mp forward _ (List.mem_map_of_mem hu'))
      exact mem_image.mpr ⟨_,List.mem_toFinset.mpr member,decoder u hu'⟩

end E19Cert

namespace E19Cert

def quickFits (blocks : List ℕ) (b : ℕ) : Bool :=
  blocks.all (fun u => E19Mask.clear (b &&& u) == 0)

def quickCandidates (n : ℕ) (row : Row) : List ℕ :=
  (List.range (1 <<< n)).filter (fun b =>
    E19Mask.clear (E19Mask.clear b) != 0 && quickFits row.blocks b)

def quickEntry (n : ℕ) (blocks : Array (List ℕ)) (row : Row) (t : ℕ × ℕ × ℕ) : Bool :=
  let (b,j,w) := t
  match blocks[j]? with
  | none => false
  | some dst =>
    let mapped := (b :: row.blocks).map (E19Mask.permuteFast n (pos w))
    permOK n w && mapped.all dst.contains && dst.all mapped.contains

def quickColor (n : ℕ) (row : Row) : Bool :=
  let assigned (a : ℕ) := row.groups.any fun g => g.contains a
  decide (row.groups.length ≤ n) &&
    row.groups.all (fun g => g.all fun a => g.all fun b => a == b || (a &&& b) == 0) &&
    row.blocks.all assigned &&
    (List.range n).all (fun j => (List.range j).all fun i =>
      let pair := (1 <<< i) ||| (1 <<< j)
      !(quickFits row.blocks pair) || assigned pair)

def quick (n : ℕ) (blocks : Array (List ℕ)) (row : Row) : Bool :=
  let bound := row.blocks.all (· < (1 <<< n))
  let transitions := row.extensions.map Prod.fst == quickCandidates n row &&
    row.extensions.all (quickEntry n blocks row)
  (bound && transitions) && quickColor n row

private theorem quickFits_eq (blocks : List ℕ) (b : ℕ) : quickFits blocks b = fits blocks b := by
  simp only [quickFits,fits,E19Mask.clear_zero_test]

private theorem quickCandidates_eq (n : ℕ) (row : Row) : quickCandidates n row = candidates n row := by
  simp only [quickCandidates,candidates,Nat.shiftLeft_eq,one_mul,E19Mask.clear_twice_test,quickFits_eq]

private theorem quickEntry_eq (n : ℕ) (rows : Array Row) (row : Row) (t : ℕ × ℕ × ℕ) :
    quickEntry n (rows.map Row.blocks) row t = entryOK n rows row t := by
  rcases t with ⟨b,j,w⟩
  have perm : E19Mask.permuteFast n (pos w) = E19Mask.permute n (pos w) :=
    funext (E19Mask.permuteFast_eq n (pos w))
  simp only [quickEntry,entryOK,Array.getElem?_map]
  cases h : rows[j]? <;> simp only [Option.map_none,Option.map_some,perm]

private theorem quickColor_eq (n : ℕ) (row : Row) : quickColor n row = colorOK n row := by
  simp only [quickColor,colorOK,quickFits_eq,Nat.shiftLeft_eq,one_mul]

theorem quick_eq (n : ℕ) (rows : Array Row) (blocks : Array (List ℕ)) (row : Row)
    (h : blocks = rows.map Row.blocks) :
    quick n blocks row = ((bounded n row && transitionsOK n rows row) && colorOK n row) := by
  subst blocks
  have agree : quickEntry n (rows.map Row.blocks) row = entryOK n rows row :=
    funext (quickEntry_eq n rows row)
  simp only [quick,bounded,transitionsOK,quickCandidates_eq,agree,quickColor_eq,Nat.shiftLeft_eq,one_mul]

end E19Cert

namespace E19Cert

def certified (n : ℕ) (rows : Array Row) : Bool :=
  rows.all (fun row => bounded n row && transitionsOK n rows row && colorOK n row)

private theorem certified_of_quick (n : ℕ) (rows : Array Row) (blocks : Array (List ℕ))
    (project : blocks = rows.map Row.blocks) (quick_checked : rows.all (quick n blocks) = true) :
    certified n rows = true := by
  apply Array.all_eq_true.mpr
  intro i hi
  exact (quick_eq n rows blocks rows[i] project) ▸ (Array.all_eq_true.mp quick_checked i hi)

private theorem solve {n : ℕ} (hn : 0 < n) (rows : Array Row)
    (i0 : Fin rows.size) (h0 : rows[i0].blocks = []) (checks : certified n rows = true)
    {V : Type*} (C : Erdos19.EFLConfig V n) : C.graph.chromaticNumber = n := by
  obtain ⟨_,H,_,_,_,small,linear,finish⟩ := E19Transfer.support_transfer C (Equiv.refl _)
  apply finish
  have good (i : Fin rows.size) := Array.all_eq_true.mp checks i.val i.isLt
  simp only [Bool.and_eq_true] at good
  apply E19Catalog.color_of_catalog (fun i : Fin rows.size => state n rows[i]) _ _ _ H small linear
  · refine ⟨i0, ?_⟩
    change rows[i0].blocks.toFinset.image (E19Mask.decode n) = ∅
    rw [h0]
    simp
  · intro i
    exact row_step rows i (good i).1.1 (good i).1.2
  · intro i
    exact row_colored hn rows[i] (good i).1.1 (good i).2

end E19Cert

private def data4 : Array E19Cert.Row := #[
⟨[],[[3,12],[5,10],[6,9],[]],[(7,1,12816),(11,1,8976),(13,1,8496),(14,1,8451),(15,2,12816)]⟩,
⟨[7],[[7],[9],[10],[12]],[]⟩,
⟨[15],[[15],[],[],[]],[]⟩
]

private def blocks4 : Array (List Nat) := #[[],[7],[15]]
private theorem blocks_eq4 : blocks4 = data4.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked4 : data4.all (E19Cert.quick 4 blocks4) = true := by
  decide +kernel

private def data5 : Array E19Cert.Row := #[
⟨[],[[3,24],[5,18],[6,9],[12,17],[10,20]],[(7,1,274960),(11,1,271120),(13,1,270640),(14,1,270595),(15,2,274960),(19,1,148240),(21,1,147760),(22,1,147715),(23,2,213520),(25,1,136240),(26,1,136195),(27,2,205840),(28,1,135235),(29,2,205120),(30,2,205060),(31,3,274960)]⟩,
⟨[7],[[7,24],[9,20],[10,17],[12,18],[]],[(25,4,274960),(26,4,274945),(28,4,274465)]⟩,
⟨[15],[[15],[17],[18],[20],[24]],[]⟩,
⟨[31],[[31],[],[],[],[]],[]⟩,
⟨[7,25],[[7],[25],[10,20],[12,18],[]],[]⟩
]

private def blocks5 : Array (List Nat) := #[[],[7],[15],[31],[7,25]]
private theorem blocks_eq5 : blocks5 = data5.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked5 : data5.all (E19Cert.quick 5 blocks5) = true := by
  decide +kernel

private def data6 : Array E19Cert.Row := #[
⟨[],[[3,24,36],[5,18,40],[6,9,48],[12,17,34],[10,20,33],[]],[(7,1,5517840),(11,1,5514000),(13,1,5513520),(14,1,5513475),(15,2,5517840),(19,1,5391120),(21,1,5390640),(22,1,5390595),(23,2,5456400),(25,1,5379120),(26,1,5379075),(27,2,5448720),(28,1,5378115),(29,2,5448000),(30,2,5447940),(31,3,5517840),(35,1,2442000),(37,1,2441520),(38,1,2441475),(39,2,3490320),(41,1,2430000),(42,1,2429955),(43,2,3482640),(44,1,2428995),(45,2,3481920),(46,2,3481860),(47,3,4534800),(49,1,2184240),(50,1,2184195),(51,2,3298320),(52,1,2183235),(53,2,3297600),(54,2,3297540),(55,3,4411920),(56,1,2164035),(57,2,3282240),(58,2,3282180),(59,3,4400400),(60,2,3280980),(61,3,4399440),(62,3,4399365),(63,4,5517840)]⟩,
⟨[7],[[7,24],[9,18,36],[10,20,33],[12,48],[17,40],[34]],[(25,5,5517840),(26,5,5517825),(28,5,5517345),(41,5,4534800),(42,5,4534785),(44,5,4534305),(49,5,4411920),(50,5,4411905),(52,5,4411425),(56,6,5517840),(57,7,5517840),(58,7,5517825),(60,7,5517345)]⟩,
⟨[15],[[15,48],[17,36],[18,33],[20,40],[24,34],[]],[(49,7,2184240),(50,7,2184195),(52,7,2183235),(56,7,2164035)]⟩,
⟨[31],[[31],[33],[34],[36],[40],[48]],[]⟩,
⟨[63],[[63],[],[],[],[],[]],[]⟩,
⟨[7,25],[[7,40],[25,34],[10,36],[12,18,33],[48],[20]],[(42,8,5517840),(44,8,5517600),(50,8,5456400),(52,8,5456160)]⟩,
⟨[7,56],[[7,56],[9,20,34],[10,17,36],[12,18,33],[],[]],[]⟩,
⟨[7,57],[[7],[57],[10,36],[12,18],[20,34],[]],[]⟩,
⟨[7,25,42],[[7,48],[25,36],[20,42],[12,18,33],[],[]],[(52,9,5517840)]⟩,
⟨[7,25,42,52],[[7],[25],[42],[52],[12,18,33],[]],[]⟩
]

private def blocks6 : Array (List Nat) := #[[],[7],[15],[31],[63],[7,25],[7,56],[7,57],[7,25,42],[7,25,42,52]]
private theorem blocks_eq6 : blocks6 = data6.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked6 : data6.all (E19Cert.quick 6 blocks6) = true := by
  decide +kernel

private def data7 : Array E19Cert.Row := #[
⟨[],[[3,24,68],[5,18,40],[6,9,96],[17,34,72],[20,33,66],[12,48,65],[10,36,80]],[(7,1,106181136),(11,1,106177296),(13,1,106176816),(14,1,106176771),(15,2,106181136),(19,1,106054416),(21,1,106053936),(22,1,106053891),(23,2,106119696),(25,1,106042416),(26,1,106042371),(27,2,106112016),(28,1,106041411),(29,2,106111296),(30,2,106111236),(31,3,106181136),(35,1,103105296),(37,1,103104816),(38,1,103104771),(39,2,104153616),(41,1,103093296),(42,1,103093251),(43,2,104145936),(44,1,103092291),(45,2,104145216),(46,2,104145156),(47,3,105198096),(49,1,102847536),(50,1,102847491),(51,2,103961616),(52,1,102846531),(53,2,103960896),(54,2,103960836),(55,3,105075216),(56,1,102827331),(57,2,103945536),(58,2,103945476),(59,3,105063696),(60,2,103944276),(61,3,105062736),(62,3,105062661),(63,4,106181136),(67,1,40190736),(69,1,40190256),(70,1,40190211),(71,2,56967696),(73,1,40178736),(74,1,40178691)]++[(75,2,56960016),(76,1,40177731),(77,2,56959296),(78,2,56959236),(79,3,73740816),(81,1,39932976),(82,1,39932931),(83,2,56775696),(84,1,39931971),(85,2,56774976),(86,2,56774916),(87,3,73617936),(88,1,39912771),(89,2,56759616),(90,2,56759556),(91,3,73606416),(92,2,56758356),(93,3,73605456),(94,3,73605381),(95,4,90452496),(97,1,35017776),(98,1,35017731),(99,2,52843536),(100,1,35016771),(101,2,52842816),(102,2,52842756),(103,3,70668816),(104,1,34997571),(105,2,52827456),(106,2,52827396),(107,3,70657296),(108,2,52826196),(109,3,70656336),(110,3,70656261),(111,4,88486416),(112,1,34628931),(113,2,52520256),(114,2,52520196),(115,3,70411536),(116,2,52518996),(117,3,70410576),(118,3,70410501),(119,4,88302096),(120,2,52495956),(121,3,70391376),(122,3,70391301),(123,4,88286736),(124,3,70389861)]++[(125,4,88285536),(126,4,88285446),(127,5,106181136)]⟩,
⟨[7],[[7,24,96],[9,18,36],[10,33,80],[12,48,65],[17,40,66],[20,34,72],[68]],[(25,6,106181136),(26,6,106181121),(28,6,106180641),(41,6,105198096),(42,6,105198081),(44,6,105197601),(49,6,105075216),(50,6,105075201),(52,6,105074721),(56,7,106181136),(57,8,106181136),(58,8,106181121),(60,8,106180641),(73,6,73740816),(74,6,73740801),(76,6,73740321),(81,6,73617936),(82,6,73617921),(84,6,73617441),(88,7,90452496),(89,8,90452496),(90,8,90452481),(92,8,90452001),(97,6,70668816),(98,6,70668801),(100,6,70668321),(104,7,88486416),(105,8,88486416),(106,8,88486401),(108,8,88485921),(112,7,88302096),(113,8,88302096),(114,8,88302081),(116,8,88301601),(120,9,106181136),(121,10,106181136),(122,10,106181121),(124,10,106180641)]⟩,
⟨[15],[[15,48],[17,34,68],[18,36,65],[20,33,72],[24,96],[40,80],[66]],[(49,8,102847536),(50,8,102847491),(52,8,102846531),(56,8,102827331),(81,8,39932976),(82,8,39932931),(84,8,39931971),(88,8,39912771),(97,8,35017776),(98,8,35017731),(100,8,35016771),(104,8,34997571),(112,9,34628931),(113,11,106181136),(114,11,106181121),(116,11,106180641),(120,11,106169121)]⟩,
⟨[31],[[31,96],[33,68],[34,65],[36,72],[40,80],[48,66],[]],[(97,10,35017776),(98,10,35017731),(100,10,35016771),(104,10,34997571),(112,10,34628931)]⟩,
⟨[63],[[63],[65],[66],[68],[72],[80],[96]],[]⟩,
⟨[127],[[127],[],[],[],[],[],[]],[]⟩,
⟨[7,25],[[7,40,80],[25,36,66],[10,33,68],[12,18,96],[20,34,72],[48,65],[]],[(42,12,106181136),(44,12,106180896),(50,12,106119696),(52,12,106119456),(74,12,90452496),(76,12,90452256),(82,12,90391056),(84,12,90390816),(97,13,106181136),(98,14,106181136),(100,14,106180896),(104,14,106042416),(106,15,106181136),(108,15,106180896),(112,14,105980976),(114,15,106119696),(116,15,106119456)]⟩,
⟨[7,56],[[7,72],[56,65],[17,36,66],[9,18,68],[12,34,80],[10,20,96],[33]],[(73,14,40178736),(74,14,40178691),(76,14,40177731),(81,14,39932976),(82,14,39932931),(84,14,39931971),(97,14,35017776),(98,14,35017731),(100,14,35016771)]⟩,
⟨[7,57],[[57,66],[7,72],[10,36,80],[12,18,96],[34,68],[20,65],[]],[(74,15,73740801),(76,15,73740321),(82,15,73617921),(84,15,73617441),(98,15,70668801),(100,15,70668321)]⟩,
⟨[7,120],[[7,120],[9,20,66],[10,17,36],[12,18,33],[34,65],[68],[]],[]⟩,
⟨[7,121],[[7],[121],[10,36],[12,18],[34,68],[20,66],[]],[]⟩,
⟨[15,113],[[15],[113],[18,40,68],[20,34,72],[24,36,66],[],[]],[]⟩,
⟨[7,25,42],[[7,96],[25,68],[20,42,65],[12,33,80],[18,36,72],[48,66],[]],[(52,16,106181136),(76,17,106181136),(82,17,106042416),(84,18,106181136),(97,17,103093251),(100,18,105198081),(112,18,104990001),(116,19,106181136)]⟩,
⟨[7,25,97],[[7,40,80],[25,34,68],[10,20,97],[12,18],[36,66],[48,72],[]],[(42,17,103093251),(44,17,103092291),(50,17,102847491),(52,17,102846531),(74,17,40178691),(76,17,40177731),(82,17,39932931),(84,17,39931971)]⟩,
⟨[7,25,98],[[25,36],[7,40,80],[12,98],[20,33,72],[10,48,68],[18,65],[]],[(44,18,105197601),(52,18,105074721),(76,18,73740321),(84,18,73617441)]⟩,
⟨[7,25,106],[[20,106],[7,80],[25,36],[12,48,65],[18,33,68],[],[]],[(52,19,106119456),(84,19,90390816)]⟩,
⟨[7,25,42,52],[[7,72],[25,68],[42,65],[52,66],[12,18,33],[80],[96]],[(76,20,106181136),(82,20,106119456),(97,20,104153346)]⟩,
⟨[7,25,42,76],[[7,48],[25,36,66],[42,80],[18,33,76],[20,96],[65],[]],[(52,20,106181136),(82,20,90452256),(97,20,88486146),(112,21,106181136)]⟩,
⟨[7,25,42,84],[[42,84],[7,96],[25,36,66],[18,33,72],[12,48,65],[],[]],[(97,21,103093251)]⟩,
⟨[7,25,42,116],[[116],[7,72],[25,66],[42,65],[12,18,33],[],[]],[]⟩,
⟨[7,25,42,52,76],[[7,80],[25,96],[42,65],[52,66],[18,33,76],[],[]],[(82,22,106181136),(97,22,105198081)]⟩,
⟨[7,25,42,76,112],[[7,112],[25,36,66],[20,42,65],[18,33,76],[],[],[]],[]⟩,
⟨[7,25,42,52,76,82],[[7,96],[25],[42,65],[52],[33,76],[82],[]],[(97,23,106181136)]⟩,
⟨[7,25,42,52,76,82,97],[[7],[25],[42],[52],[76],[82],[97]],[]⟩
]

private def blocks7 : Array (List Nat) := #[[],[7],[15],[31],[63],[127],[7,25],[7,56],[7,57],[7,120],[7,121],[15,113],[7,25,42],[7,25,97],[7,25,98],[7,25,106],[7,25,42,52],[7,25,42,76],[7,25,42,84],[7,25,42,116],[7,25,42,52,76],[7,25,42,76,112],[7,25,42,52,76,82],[7,25,42,52,76,82,97]]
private theorem blocks_eq7 : blocks7 = data7.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked7 : data7.all (E19Cert.quick 7 blocks7) = true := by
  decide +kernel

private def data8Part0 : Array E19Cert.Row := #[
⟨[],[[3,24,68,160],[5,18,40,192],[6,9,96,144],[17,34,72,132],[20,33,66,136],[12,48,65,130],[10,36,80,129],[]],[(7,1,1985229328),(11,1,1985225488),(13,1,1985225008),(14,1,1985224963),(15,2,1985229328),(19,1,1985102608),(21,1,1985102128),(22,1,1985102083),(23,2,1985167888),(25,1,1985090608),(26,1,1985090563),(27,2,1985160208),(28,1,1985089603),(29,2,1985159488),(30,2,1985159428),(31,3,1985229328),(35,1,1982153488),(37,1,1982153008),(38,1,1982152963),(39,2,1983201808),(41,1,1982141488),(42,1,1982141443),(43,2,1983194128),(44,1,1982140483),(45,2,1983193408),(46,2,1983193348),(47,3,1984246288),(49,1,1981895728),(50,1,1981895683),(51,2,1983009808),(52,1,1981894723),(53,2,1983009088),(54,2,1983009028),(55,3,1984123408),(56,1,1981875523),(57,2,1982993728),(58,2,1982993668),(59,3,1984111888),(60,2,1982992468),(61,3,1984110928),(62,3,1984110853),(63,4,1985229328),(67,1,1919238928),(69,1,1919238448),(70,1,1919238403),(71,2,1936015888),(73,1,1919226928),(74,1,1919226883)]++[(75,2,1936008208),(76,1,1919225923),(77,2,1936007488),(78,2,1936007428),(79,3,1952789008),(81,1,1918981168),(82,1,1918981123),(83,2,1935823888),(84,1,1918980163),(85,2,1935823168),(86,2,1935823108),(87,3,1952666128),(88,1,1918960963),(89,2,1935807808),(90,2,1935807748),(91,3,1952654608),(92,2,1935806548),(93,3,1952653648),(94,3,1952653573),(95,4,1969500688),(97,1,1914065968),(98,1,1914065923),(99,2,1931891728),(100,1,1914064963),(101,2,1931891008),(102,2,1931890948),(103,3,1949717008),(104,1,1914045763),(105,2,1931875648),(106,2,1931875588),(107,3,1949705488),(108,2,1931874388),(109,3,1949704528),(110,3,1949704453),(111,4,1967534608),(112,1,1913677123),(113,2,1931568448),(114,2,1931568388),(115,3,1949459728),(116,2,1931567188),(117,3,1949458768),(118,3,1949458693),(119,4,1967350288),(120,2,1931544148),(121,3,1949439568),(122,3,1949439493),(123,4,1967334928),(124,3,1949438053)]++[(125,4,1967333728),(126,4,1967333638),(127,5,1985229328),(131,1,660947728),(133,1,660947248),(134,1,660947203),(135,2,929382928),(137,1,660935728),(138,1,660935683),(139,2,929375248),(140,1,660934723),(141,2,929374528),(142,2,929374468),(143,3,1197814288),(145,1,660689968),(146,1,660689923),(147,2,929190928),(148,1,660688963),(149,2,929190208),(150,2,929190148),(151,3,1197691408),(152,1,660669763),(153,2,929174848),(154,2,929174788),(155,3,1197679888),(156,2,929173588),(157,3,1197678928),(158,3,1197678853),(159,4,1466184208),(161,1,655774768),(162,1,655774723),(163,2,925258768),(164,1,655773763),(165,2,925258048),(166,2,925257988),(167,3,1194742288),(168,1,655754563),(169,2,925242688),(170,2,925242628),(171,3,1194730768),(172,2,925241428),(173,3,1194729808),(174,3,1194729733),(175,4,1464218128),(176,1,655385923),(177,2,924935488),(178,2,924935428),(179,3,1194485008)]++[(180,2,924934228),(181,3,1194484048),(182,3,1194483973),(183,4,1464033808),(184,2,924911188),(185,3,1194464848),(186,3,1194464773),(187,4,1464018448),(188,3,1194463333),(189,4,1464017248),(190,4,1464017158),(191,5,1733571088),(193,1,561402928),(194,1,561402883),(195,2,846615568),(196,1,561401923),(197,2,846614848),(198,2,846614788),(199,3,1131827728),(200,1,561382723),(201,2,846599488),(202,2,846599428),(203,3,1131816208),(204,2,846598228),(205,3,1131815248),(206,3,1131815173),(207,4,1417032208),(208,1,561014083),(209,2,846292288),(210,2,846292228),(211,3,1131570448),(212,2,846291028),(213,3,1131569488),(214,3,1131569413),(215,4,1416847888),(216,2,846267988),(217,3,1131550288),(218,3,1131550213),(219,4,1416832528),(220,3,1131548773),(221,4,1416831328),(222,4,1416831238),(223,5,1702113808),(224,1,554132803),(225,2,840394048),(226,2,840393988),(227,3,1126655248),(228,2,840392788)]++[(229,3,1126654288),(230,3,1126654213),(231,4,1412915728),(232,2,840369748),(233,3,1126635088),(234,3,1126635013),(235,4,1412900368),(236,3,1126633573),(237,4,1412899168),(238,4,1412899078),(239,5,1699164688),(240,2,839939668),(241,3,1126266448),(242,3,1126266373),(243,4,1412593168),(244,3,1126264933),(245,4,1412591968),(246,4,1412591878),(247,5,1698918928),(248,3,1126238053),(249,4,1412568928),(250,4,1412568838),(251,5,1698899728),(252,4,1412567158),(253,5,1698898288),(254,5,1698898183),(255,6,1985229328)]⟩,
⟨[7],[[7,24,96],[9,18,36,192],[10,33,68,144],[12,48,66,129],[20,40,65,130],[17,72,160],[34,80,136],[132]],[(25,7,1985229328),(26,7,1985229313),(28,7,1985228833),(41,7,1984246288),(42,7,1984246273),(44,7,1984245793),(49,7,1984123408),(50,7,1984123393),(52,7,1984122913),(56,8,1985229328),(57,9,1985229328),(58,9,1985229313),(60,9,1985228833),(73,7,1952789008),(74,7,1952788993),(76,7,1952788513),(81,7,1952666128),(82,7,1952666113),(84,7,1952665633),(88,8,1969500688),(89,9,1969500688),(90,9,1969500673),(92,9,1969500193),(97,7,1949717008),(98,7,1949716993),(100,7,1949716513),(104,8,1967534608),(105,9,1967534608),(106,9,1967534593),(108,9,1967534113),(112,8,1967350288),(113,9,1967350288),(114,9,1967350273),(116,9,1967349793),(120,10,1985229328),(121,11,1985229328),(122,11,1985229313),(124,11,1985228833),(137,7,1197814288),(138,7,1197814273),(140,7,1197813793),(145,7,1197691408),(146,7,1197691393),(148,7,1197690913),(152,8,1466184208),(153,9,1466184208),(154,9,1466184193),(156,9,1466183713)]++[(161,7,1194742288),(162,7,1194742273),(164,7,1194741793),(168,8,1464218128),(169,9,1464218128),(170,9,1464218113),(172,9,1464217633),(176,8,1464033808),(177,9,1464033808),(178,9,1464033793),(180,9,1464033313),(184,10,1733571088),(185,11,1733571088),(186,11,1733571073),(188,11,1733570593),(193,7,1131827728),(194,7,1131827713),(196,7,1131827233),(200,8,1417032208),(201,9,1417032208),(202,9,1417032193),(204,9,1417031713),(208,8,1416847888),(209,9,1416847888),(210,9,1416847873),(212,9,1416847393),(216,10,1702113808),(217,11,1702113808),(218,11,1702113793),(220,11,1702113313),(224,8,1412915728),(225,9,1412915728),(226,9,1412915713),(228,9,1412915233),(232,10,1699164688),(233,11,1699164688),(234,11,1699164673),(236,11,1699164193),(240,10,1698918928),(241,11,1698918928),(242,11,1698918913),(244,11,1698918433),(248,12,1985229328),(249,13,1985229328),(250,13,1985229313),(252,13,1985228833)]⟩,
⟨[15],[[15,48,192],[17,34,68,136],[18,65,160],[20,33,72,130],[24,96,132],[36,80,129],[40,66,144],[]],[(49,9,1981895728),(50,9,1981895683),(52,9,1981894723),(56,9,1981875523),(81,9,1918981168),(82,9,1918981123),(84,9,1918980163),(88,9,1918960963),(97,9,1914065968),(98,9,1914065923),(100,9,1914064963),(104,9,1914045763),(112,10,1913677123),(113,14,1985229328),(114,14,1985229313),(116,14,1985228833),(120,14,1985217313),(145,9,660689968),(146,9,660689923),(148,9,660688963),(152,9,660669763),(161,9,655774768),(162,9,655774723),(164,9,655773763),(168,9,655754563),(176,10,655385923),(177,14,1733571088),(178,14,1733571073),(180,14,1733570593),(184,14,1733559073),(193,9,561402928),(194,9,561402883),(196,9,561401923),(200,9,561382723),(208,10,561014083),(209,14,1702113808),(210,14,1702113793),(212,14,1702113313),(216,14,1702101793),(224,10,554132803),(225,14,1699164688),(226,14,1699164673),(228,14,1699164193),(232,14,1699152673),(240,15,1985229328),(241,16,1985229328),(242,16,1985229313),(244,16,1985228833)]++[(248,16,1985217313)]⟩,
⟨[31],[[31,96],[33,66,132],[34,72,129],[36,65,136],[40,68,144],[48,192],[80,160],[130]],[(97,11,1914065968),(98,11,1914065923),(100,11,1914064963),(104,11,1914045763),(112,11,1913677123),(161,11,655774768),(162,11,655774723),(164,11,655773763),(168,11,655754563),(176,11,655385923),(193,11,561402928),(194,11,561402883),(196,11,561401923),(200,11,561382723),(208,11,561014083),(224,12,554132803),(225,16,840394048),(226,16,840393988),(228,16,840392788),(232,16,840369748),(240,16,839939668)]⟩,
⟨[63],[[63,192],[65,132],[66,129],[68,136],[72,144],[80,160],[96,130],[]],[(193,13,561402928),(194,13,561402883),(196,13,561401923),(200,13,561382723),(208,13,561014083),(224,13,554132803)]⟩,
⟨[127],[[127],[129],[130],[132],[136],[144],[160],[192]],[]⟩,
⟨[255],[[255],[],[],[],[],[],[],[]],[]⟩,
⟨[7,25],[[7,40,192],[25,66,132],[10,48,68,129],[12,96,130],[20,72,160],[33,80,136],[34,65,144],[18,36]],[(42,17,1985229328),(44,17,1985229088),(50,17,1985167888),(52,17,1985167648),(74,17,1969500688),(76,17,1969500448),(82,17,1969439248),(84,17,1969439008),(97,18,1985229328),(98,19,1985229328),(100,19,1985229088),(104,19,1985090608),(106,20,1985229328),(108,20,1985229088),(112,19,1985029168),(114,20,1985167888),(116,20,1985167648),(138,17,1466184208),(140,17,1466183968),(146,17,1466122768),(148,17,1466122528),(161,18,1733571088),(162,19,1733571088),(164,19,1733570848),(168,19,1733432368),(170,20,1733571088),(172,20,1733570848),(176,19,1733370928),(178,20,1733509648),(180,20,1733509408),(193,18,1702113808),(194,19,1702113808),(196,19,1702113568),(200,19,1701975088),(202,20,1702113808),(204,20,1702113568),(208,19,1701913648),(210,20,1702052368),(212,20,1702052128),(224,21,1985229328),(225,22,1985229328),(226,23,1985229328),(228,23,1985229088),(232,23,1985090608),(234,24,1985229328),(236,24,1985229088),(240,23,1985029168),(242,24,1985167888)]++[(244,24,1985167648)]⟩,
⟨[7,56],[[7,56,192],[12,65,130],[9,36,66,144],[18,33,68,136],[20,34,72,129],[10,80,160],[17,96,132],[]],[(73,19,1919226928),(74,19,1919226883),(76,19,1919225923),(81,19,1918981168),(82,19,1918981123),(84,19,1918980163),(97,19,1914065968),(98,19,1914065923),(100,19,1914064963),(137,19,660935728),(138,19,660935683),(140,19,660934723),(145,19,660689968),(146,19,660689923),(148,19,660688963),(161,19,655774768),(162,19,655774723),(164,19,655773763),(193,21,1131827728),(194,21,1131827713),(196,21,1131827233),(200,21,1126238053),(201,25,1985229328),(202,25,1985229313),(204,25,1985228833),(208,21,1126176613),(209,25,1985167888),(210,25,1985167873),(212,25,1985167393),(224,21,1124210533),(225,25,1983201808),(226,25,1983201793),(228,25,1983201313)]⟩,
⟨[7,57],[[57,68,130],[7,72,144],[10,96,132],[12,34,192],[36,80,136],[20,66,129],[18,65,160],[]],[(74,20,1952788993),(76,20,1952788513),(82,20,1952666113),(84,20,1952665633),(98,20,1949716993),(100,20,1949716513),(138,20,1197814273),(140,20,1197813793),(146,20,1197691393),(148,20,1197690913),(162,20,1194742273),(164,20,1194741793),(193,22,1131827728),(194,23,1131827713),(196,23,1131827233),(200,25,1417032208),(202,26,1985229328),(204,26,1985229088),(208,25,1416847888),(210,26,1985167888),(212,26,1985167648),(224,25,1412915728),(226,26,1983201808),(228,26,1983201568)]⟩,
⟨[7,120],[[120,129],[7,136],[9,36,66,144],[12,18,65,160],[10,20,33,192],[17,68,130],[34,132],[]],[(137,23,660935728),(138,23,660935683),(140,23,660934723),(145,23,660689968),(146,23,660689923),(148,23,660688963),(161,23,655774768),(162,23,655774723),(164,23,655773763),(193,23,561402928),(194,23,561402883),(196,23,561401923)]⟩,
⟨[7,121],[[121,130],[7,136],[10,36,144],[12,18,160],[34,68,129],[66,132],[20,192],[]],[(138,24,1197814273),(140,24,1197813793),(146,24,1197691393),(148,24,1197690913),(162,24,1194742273),(164,24,1194741793),(194,24,1131827713),(196,24,1131827233)]⟩
]
private def data8Part1 : Array E19Cert.Row := #[
⟨[7,248],[[7,248],[9,20,66],[10,17,132],[12,18,33],[36,65,130],[34,68,129],[],[]],[]⟩,
⟨[7,249],[[7],[249],[10,36],[12,18],[34,68],[66,132],[20,130],[]],[]⟩,
⟨[15,113],[[15,144],[113,130],[18,40,132],[20,34,192],[24,68,160],[36,66,136],[72,129],[]],[(146,26,660689923),(148,26,660688963),(152,26,660669763),(162,26,655774723),(164,26,655773763),(168,26,655754563),(194,26,561402883),(196,26,561401923),(200,26,561382723)]⟩,
⟨[15,240],[[15,240],[17,36,66,136],[18,33,72,132],[20,40,65,130],[24,34,68,129],[],[],[]],[]⟩,
⟨[15,241],[[15],[241],[18,40,132],[20,34,72],[24,36,66],[68,130],[136],[]],[]⟩,
⟨[7,25,42],[[7,48,136],[25,68,160],[20,42,192],[12,65,144],[18,96,132],[36,80,130],[66,129],[33,72]],[(52,27,1985229328),(76,28,1985229328),(82,28,1985090608),(84,29,1985229328),(97,28,1982141443),(100,29,1984246273),(112,29,1984038193),(116,30,1985229328),(140,28,1733571088),(146,28,1733432368),(148,29,1733571088),(161,28,1730483203),(164,29,1732588033),(176,29,1732379953),(180,30,1733571088),(193,31,1985229328),(194,31,1984246273),(196,32,1985229328),(200,31,1984038193),(204,33,1985229328),(208,32,1985090608),(210,33,1985090608),(212,34,1985229328),(224,32,1982141443),(225,33,1982141443),(228,34,1984246273),(240,34,1984038193),(244,35,1985229328)]⟩,
⟨[7,25,97],[[7,48,136],[25,68,130],[18,97,132],[20,40,66,129],[36,72,144],[10,80,160],[12,34,192],[]],[(42,28,1982141443),(44,28,1982140483),(50,28,1981895683),(52,28,1981894723),(74,28,1919226883),(76,28,1919225923),(82,28,1918981123),(84,28,1918980163),(138,31,1466184208),(140,31,1466183968),(146,31,1466122768),(148,31,1466122528),(162,31,1412915728),(164,31,1412915488),(168,31,1412568928),(170,36,1985229328),(172,36,1985229088),(176,31,1412507488),(178,36,1985167888),(180,36,1985167648),(194,31,1397187088),(196,31,1397186848),(200,31,1396840288),(202,36,1969500688),(204,36,1969500448),(208,31,1396778848),(210,36,1969439248),(212,36,1969439008)]⟩,
⟨[7,25,98],[[25,98,132],[7,40,192],[12,48,129],[20,72,160],[18,36,65,136],[10,33,68,144],[80,130],[]],[(44,29,1984245793),(52,29,1984122913),(76,29,1952788513),(84,29,1952665633),(138,31,1197814273),(140,32,1466183968),(146,31,1197691393),(148,32,1466122528),(161,31,1161257488),(164,32,1412915458),(168,37,1985229328),(172,38,1985229328),(176,37,1985167888),(180,38,1985167888),(193,31,1129800208),(196,32,1397186818),(200,37,1969500688),(204,38,1969500688),(208,37,1969439248),(212,38,1969439248)]⟩,
⟨[7,25,106],[[20,106,129],[7,80,160],[25,132],[12,18,33,192],[36,65,144],[48,68,130],[136],[]],[(52,30,1985167648),(84,30,1969439008),(140,33,1466183968),(146,33,1465984048),(148,34,1466122528),(161,36,1733571088),(164,38,1733570848),(176,38,1733370928),(180,39,1985229328),(193,36,1702113808),(196,38,1702113568),(208,38,1701913648),(212,39,1969500688)]⟩,
⟨[7,25,224],[[7,224],[25,34,68],[10,36,65,144],[18,40,132],[12,48,66,129],[20,33,72,130],[80,136],[]],[(42,32,1982141443),(44,32,1982140483),(50,32,1981895683),(52,32,1981894723),(74,32,1919226883),(76,32,1919225923),(82,32,1918981123),(84,32,1918980163),(138,32,660935683),(140,32,660934723),(146,32,660689923),(148,32,660688963)]⟩,
⟨[7,25,225],[[10,20,225],[7,40,80],[25,34,68],[12,18],[36,66,136],[48,72,130],[132],[144]],[(42,33,1982141443),(44,33,1982140483),(50,33,1981895683),(52,33,1981894723),(74,33,1919226883),(76,33,1919225923),(82,33,1918981123),(84,33,1918980163),(138,33,660935683),(140,33,660934723),(146,33,660689923),(148,33,660688963)]⟩,
⟨[7,25,226],[[12,226],[7,80,136],[25,36],[10,33,68,144],[48,72,132],[20,40,129],[18,65],[]],[(44,34,1984245793),(52,34,1984122913),(76,34,1952788513),(84,34,1952665633),(140,34,1197813793),(148,34,1197690913)]⟩
]
private def data8Part2 : Array E19Cert.Row := #[
⟨[7,25,234],[[20,234],[7,80],[25,36],[12,65,144],[48,68,129],[18,33,132],[],[]],[(52,35,1985167648),(84,35,1969439008),(148,35,1466122528)]⟩,
⟨[7,56,201],[[18,36,201],[7,80,160],[56,66,132],[34,68,144],[10,20,96],[12,17,130],[33],[]],[(82,38,1918981123),(84,38,1918980163),(98,38,1914065923),(100,38,1914064963),(146,38,660689923),(148,38,660688963),(162,38,655774723),(164,38,655773763)]⟩,
⟨[7,57,202],[[57,68],[20,202],[7,80,160],[12,96,144],[18,36,129],[34,65,132],[],[]],[(84,39,1952665633),(100,39,1949716513),(148,39,1197690913),(164,39,1194741793)]⟩,
⟨[7,25,42,52],[[7,72,160],[25,68,130],[42,65,132],[52,66,129],[12,18,33,192],[80,136],[96,144],[]],[(76,40,1985229328),(82,40,1985167648),(97,40,1983201538),(140,40,1733571088),(146,40,1733509408),(161,40,1731543298),(193,41,1985229328),(194,41,1984246273),(196,41,1984122913),(200,41,1984038193),(204,42,1985229328),(208,41,1983914833),(210,42,1985167648),(224,41,1979982613),(225,42,1983201538)]⟩,
⟨[7,25,42,76],[[7,48,192],[25,96,132],[42,65,144],[18,76,160],[36,80,130],[20,33,66,136],[129],[]],[(52,40,1985229328),(82,40,1969500448),(97,40,1967534338),(112,43,1985229328),(146,44,1985229328),(148,44,1969500448),(161,44,1984246273),(164,44,1967534338),(176,45,1985229328),(180,46,1985229328),(193,44,1952788513),(194,44,1951805458),(208,45,1969500448),(210,46,1969500448),(224,45,1967534338),(225,46,1967534338),(240,47,1985229328)]⟩,
⟨[7,25,42,84],[[42,84,129],[7,96,136],[25,66,160],[12,18,33,192],[48,65,132],[36,72,130],[144],[]],[(97,43,1982141443),(140,44,1466183968),(146,44,1450394128),(161,45,1730483203),(164,48,1985229328),(176,48,1985090608),(193,45,1651593283),(194,48,1969439008),(200,48,1969300288),(224,49,1985229328),(225,50,1985229328)]⟩,
⟨[7,25,42,116],[[116,136],[7,72,144],[25,130],[42,192],[12,18,129],[33,66,132],[65,160],[]],[(140,46,1733571088),(146,46,1733432368),(161,46,1730483203),(193,51,1985229328),(194,51,1984246273),(200,51,1984038193)]⟩,
⟨[7,25,42,193],[[20,42,193],[7,72,144],[25,36,66],[12,80,160],[48,68,136],[18,96,132],[33,130],[]],[(52,41,1985229328),(76,44,1952788513),(82,44,1952458033),(84,45,1651593283),(100,48,1966489858),(112,48,1966147138),(116,51,1985229328),(140,44,1197813793),(146,44,1197483313),(148,45,644960323),(164,48,1463173378),(176,48,1462830658),(180,51,1733571088)]⟩,
⟨[7,25,42,196],[[25,196],[7,48,136],[20,42,65],[36,80,130],[12,33,66,144],[18,96,129],[72,160],[]],[(52,41,1984122913),(82,45,1969300528),(97,45,1964385283),(112,49,1984038193),(146,45,1465984048),(161,45,1461068803),(176,49,1732379953)]⟩,
⟨[7,25,42,204],[[18,33,204],[7,48],[25,66,160],[42,80,129],[36,65,144],[20,96,130],[],[]],[(52,42,1985229328),(82,46,1969300528),(97,46,1964385283),(112,50,1984038193),(146,46,1465984048),(161,46,1461068803),(176,50,1732379953)]⟩,
⟨[7,25,42,212],[[33,212],[7,72,160],[25,36,130],[42,65],[12,18,96,129],[48,66,136],[],[]],[(97,47,1982141443),(161,47,1730483203)]⟩,
⟨[7,25,42,244],[[244],[7,72],[25,66],[42,129],[12,65,130],[18,33,136],[],[]],[]⟩
]
private def data8Part3 : Array E19Cert.Row := #[
⟨[7,25,97,170],[[20,170],[7,48,192],[25,66,132],[12,97,144],[18,68,129],[36,80],[72],[]],[(52,46,1981894723),(76,46,1901469763),(82,46,1901086243),(84,47,1918980163),(148,51,1466122528),(196,51,1397186848),(208,51,1396778848),(212,52,1985229328)]⟩,
⟨[7,25,98,168],[[7,80,168],[25,68,130],[20,98,129],[12,65,144],[48,72,132],[18,36,192],[10,33],[]],[(52,48,1981894723),(76,48,1901469748),(84,49,1952665633),(146,48,391132708),(148,49,1197482833),(193,48,272062018),(196,49,1076323093),(208,49,69408613),(212,53,1985229328)]⟩,
⟨[7,25,98,172],[[18,65,172],[25,98],[7,80],[20,72,129],[10,33,68,144],[48,192],[130],[]],[(84,50,1952665633),(146,51,1197691393),(193,51,1129800208),(208,53,1969439248)]⟩,
⟨[7,25,106,180],[[106,129],[65,180],[7,80,136],[25,68,130],[12,18,33,192],[],[],[]],[(193,52,1702113808)]⟩,
⟨[7,25,42,52,76],[[7,96,144],[25,66,160],[42,80,129],[52,192],[18,33,76],[65,132],[130],[136]],[(82,54,1985229328),(97,54,1984246273),(146,55,1985229328),(161,55,1984246273),(193,56,1985229328),(194,56,1984246273),(208,56,1980772948),(210,57,1985229328),(224,56,1979789893),(225,57,1984246273)]⟩,
⟨[7,25,42,52,193],[[42,193],[7,96,136],[25,68,160],[12,33,66,144],[52,72,130],[80,132],[18],[]],[(76,56,1985229328),(82,56,1985167648),(140,56,1733571088),(146,56,1733509408)]⟩,
⟨[7,25,42,52,204],[[18,33,204],[7,80,160],[25,96,130],[42,65,144],[52,66,129],[],[],[]],[(82,57,1985167648),(97,57,1983201538),(146,57,1733509408),(161,57,1731543298)]⟩,
⟨[7,25,42,76,112],[[7,112,136],[25,36,130],[20,42,192],[18,76,129],[33,66,132],[65,160],[144],[]],[(146,58,1985229328),(148,58,1969500448),(161,58,1984246273),(164,58,1967534338),(193,58,1952788513),(194,58,1951805458)]⟩,
⟨[7,25,42,76,146],[[33,76,146],[7,96,136],[25,36,192],[42,80,129],[20,65,160],[48,66,132],[],[]],[(52,55,1985229328),(97,56,1967534338),(112,58,1985229328),(161,56,1463879218),(164,58,654721333),(193,58,644891923),(224,59,1985229328),(225,60,1985229328)]⟩,
⟨[7,25,42,76,176],[[7,176],[25,96,130],[20,42,192],[18,76,129],[36,65,136],[33,66,132],[80],[]],[(82,56,1902130468),(97,56,1896232258),(193,59,1952788513),(194,59,1951805458)]⟩,
⟨[7,25,42,76,180],[[66,180],[7,192],[25,96,130],[42,65],[18,76,129],[33,80,136],[],[]],[(82,57,1969500448),(97,57,1967534338),(193,60,1952788513),(194,60,1951805458)]⟩,
⟨[7,25,42,76,240],[[7,240],[25,66,132],[20,42,129],[33,76,130],[18,36,65,136],[],[],[]],[]⟩
]
private def data8Part4 : Array E19Cert.Row := #[
⟨[7,25,42,84,164],[[25,96,130],[42,84,129],[7,48,192],[18,65,164],[33,66,136],[72,144],[12],[]],[(97,58,1883398483),(146,58,119824693),(193,59,543454033),(194,59,38171413),(200,61,1985229328)]⟩,
⟨[7,25,42,84,224],[[7,224],[42,84,129],[25,36,130],[18,65,136],[48,72,132],[12,33,66,144],[],[]],[(140,59,1466183968),(146,59,1450394128)]⟩,
⟨[7,25,42,84,225],[[12,18,225],[42,84],[7,48,136],[25,36,130],[66,132],[72,144],[],[]],[(140,60,1466183968),(146,60,1450394128)]⟩,
⟨[7,25,42,116,193],[[116,130],[42,193],[7,136],[25,66,132],[12,18,160],[33,72,144],[],[]],[(140,60,1197813793),(146,60,1197483313)]⟩,
⟨[7,25,97,170,212],[[170],[212],[7,48,72],[25,36,66],[12,18,97],[129],[],[]],[]⟩,
⟨[7,25,98,168,212],[[10,33,212],[7,168],[25,98],[12,48,65,130],[18,36,72,129],[],[],[]],[]⟩,
⟨[7,25,42,52,76,82],[[7,192],[25,160],[42,65,132],[52,129],[33,76,130],[82,136],[96,144],[]],[(97,62,1985229328),(161,63,1985229328),(193,63,1969439248),(224,63,1963140118),(225,64,1985229328)]⟩,
⟨[7,25,42,52,76,146],[[33,76,146],[7,80,160],[25,192],[42,65,132],[52,66,129],[96,136],[],[]],[(97,63,1984246273),(161,63,1732464673),(193,65,1985229328),(224,65,1979982613),(225,66,1985229328)]⟩,
⟨[7,25,42,52,76,193],[[42,193],[7,96,144],[25,66,132],[18,76,160],[52,130],[33,80,136],[],[]],[(82,63,1969439248),(146,65,1985229328)]⟩,
⟨[7,25,42,52,76,210],[[33,210],[7,96,136],[25,160],[42,65,132],[52,129],[76],[],[]],[(97,64,1984246273),(161,66,1984246273)]⟩,
⟨[7,25,42,76,112,146],[[7,112,136],[33,76,146],[25,36,192],[20,42,129],[65,132],[66,160],[],[]],[(161,65,1463879218),(164,67,1985229328),(193,67,1952788513)]⟩,
⟨[7,25,42,76,146,224],[[7,224],[33,76,146],[20,42,129],[25,36,66],[48,65,136],[80,132],[],[]],[(52,65,1979982613)]⟩
]
private def data8Part5 : Array E19Cert.Row := #[
⟨[7,25,42,76,146,225],[[20,225],[76,146],[7,48,136],[25,36,66],[42,80,132],[],[],[]],[(52,66,1985229328)]⟩,
⟨[7,25,42,84,164,200],[[7,96,144],[25,66,164],[42,84,129],[18,33,200],[12,48,65,130],[],[],[]],[(97,67,1698120193),(146,67,1450394128)]⟩,
⟨[7,25,42,52,76,82,97],[[7,192],[25,132],[42,129],[52,130],[76,144],[82,160],[97,136],[]],[]⟩,
⟨[7,25,42,52,76,82,161],[[76,161],[7,96,144],[25,130],[42,65,132],[52,192],[82,136],[],[]],[]⟩,
⟨[7,25,42,52,76,82,225],[[225],[7,144],[25,130],[42,132],[52,136],[76],[82],[]],[]⟩,
⟨[7,25,42,52,76,146,193],[[42,193],[33,76,146],[7,80,160],[25,96,132],[52,66,136],[],[],[]],[]⟩,
⟨[7,25,42,52,76,146,225],[[225],[76,146],[7,80,136],[25,66,132],[42],[52],[],[]],[]⟩,
⟨[7,25,42,76,112,146,164],[[7,112,136],[25,66,164],[33,76,146],[20,42,65],[129],[192],[],[]],[(193,68,1985229328)]⟩,
⟨[7,25,42,76,112,146,164,193],[[7,112,136],[25,66,164],[20,42,193],[33,76,146],[],[],[],[]],[]⟩
]
private def data8 : Array E19Cert.Row := data8Part0 ++ data8Part1 ++ data8Part2 ++ data8Part3 ++ data8Part4 ++ data8Part5

private def blocks8Part0 : Array (List Nat) := #[[],[7],[15],[31],[63],[127],[255],[7,25],[7,56],[7,57],[7,120],[7,121]]
private theorem blocks_eq8Part0 : blocks8Part0 = data8Part0.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks8Part1 : Array (List Nat) := #[[7,248],[7,249],[15,113],[15,240],[15,241],[7,25,42],[7,25,97],[7,25,98],[7,25,106],[7,25,224],[7,25,225],[7,25,226]]
private theorem blocks_eq8Part1 : blocks8Part1 = data8Part1.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks8Part2 : Array (List Nat) := #[[7,25,234],[7,56,201],[7,57,202],[7,25,42,52],[7,25,42,76],[7,25,42,84],[7,25,42,116],[7,25,42,193],[7,25,42,196],[7,25,42,204],[7,25,42,212],[7,25,42,244]]
private theorem blocks_eq8Part2 : blocks8Part2 = data8Part2.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks8Part3 : Array (List Nat) := #[[7,25,97,170],[7,25,98,168],[7,25,98,172],[7,25,106,180],[7,25,42,52,76],[7,25,42,52,193],[7,25,42,52,204],[7,25,42,76,112],[7,25,42,76,146],[7,25,42,76,176],[7,25,42,76,180],[7,25,42,76,240]]
private theorem blocks_eq8Part3 : blocks8Part3 = data8Part3.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks8Part4 : Array (List Nat) := #[[7,25,42,84,164],[7,25,42,84,224],[7,25,42,84,225],[7,25,42,116,193],[7,25,97,170,212],[7,25,98,168,212],[7,25,42,52,76,82],[7,25,42,52,76,146],[7,25,42,52,76,193],[7,25,42,52,76,210],[7,25,42,76,112,146],[7,25,42,76,146,224]]
private theorem blocks_eq8Part4 : blocks8Part4 = data8Part4.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks8Part5 : Array (List Nat) := #[[7,25,42,76,146,225],[7,25,42,84,164,200],[7,25,42,52,76,82,97],[7,25,42,52,76,82,161],[7,25,42,52,76,82,225],[7,25,42,52,76,146,193],[7,25,42,52,76,146,225],[7,25,42,76,112,146,164],[7,25,42,76,112,146,164,193]]
private theorem blocks_eq8Part5 : blocks8Part5 = data8Part5.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks8 : Array (List Nat) := blocks8Part0 ++ blocks8Part1 ++ blocks8Part2 ++ blocks8Part3 ++ blocks8Part4 ++ blocks8Part5
private theorem blocks_eq8 : blocks8 = data8.map E19Cert.Row.blocks := by
  simp only [blocks8, data8, Array.map_append, blocks_eq8Part0, blocks_eq8Part1, blocks_eq8Part2, blocks_eq8Part3, blocks_eq8Part4, blocks_eq8Part5]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked8Part0 : data8Part0.all (E19Cert.quick 8 blocks8) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked8Part1 : data8Part1.all (E19Cert.quick 8 blocks8) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked8Part2 : data8Part2.all (E19Cert.quick 8 blocks8) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked8Part3 : data8Part3.all (E19Cert.quick 8 blocks8) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked8Part4 : data8Part4.all (E19Cert.quick 8 blocks8) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked8Part5 : data8Part5.all (E19Cert.quick 8 blocks8) = true := by
  decide +kernel
private theorem quick_checked8 : data8.all (E19Cert.quick 8 blocks8) = true := by
  simp only [data8, Array.all_append, quick_checked8Part0, quick_checked8Part1, quick_checked8Part2, quick_checked8Part3, quick_checked8Part4, quick_checked8Part5, Bool.true_and]

private def data9Part0 : Array E19Cert.Row := #[
⟨[],[[3,24,68,288],[5,18,40,384],[6,9,192,272],[17,34,72,132],[33,66,136,260],[48,65,130,264],[36,80,129,258],[12,96,144,257],[10,20,160,320]],[(7,1,36344967696),(11,1,36344963856),(13,1,36344963376),(14,1,36344963331),(15,2,36344967696),(19,1,36344840976),(21,1,36344840496),(22,1,36344840451),(23,2,36344906256),(25,1,36344828976),(26,1,36344828931),(27,2,36344898576),(28,1,36344827971),(29,2,36344897856),(30,2,36344897796),(31,3,36344967696),(35,1,36341891856),(37,1,36341891376),(38,1,36341891331),(39,2,36342940176),(41,1,36341879856),(42,1,36341879811),(43,2,36342932496),(44,1,36341878851),(45,2,36342931776),(46,2,36342931716),(47,3,36343984656),(49,1,36341634096),(50,1,36341634051),(51,2,36342748176),(52,1,36341633091),(53,2,36342747456),(54,2,36342747396),(55,3,36343861776),(56,1,36341613891),(57,2,36342732096),(58,2,36342732036),(59,3,36343850256),(60,2,36342730836),(61,3,36343849296),(62,3,36343849221),(63,4,36344967696),(67,1,36278977296),(69,1,36278976816),(70,1,36278976771),(71,2,36295754256),(73,1,36278965296),(74,1,36278965251)]++[(75,2,36295746576),(76,1,36278964291),(77,2,36295745856),(78,2,36295745796),(79,3,36312527376),(81,1,36278719536),(82,1,36278719491),(83,2,36295562256),(84,1,36278718531),(85,2,36295561536),(86,2,36295561476),(87,3,36312404496),(88,1,36278699331),(89,2,36295546176),(90,2,36295546116),(91,3,36312392976),(92,2,36295544916),(93,3,36312392016),(94,3,36312391941),(95,4,36329239056),(97,1,36273804336),(98,1,36273804291),(99,2,36291630096),(100,1,36273803331),(101,2,36291629376),(102,2,36291629316),(103,3,36309455376),(104,1,36273784131),(105,2,36291614016),(106,2,36291613956),(107,3,36309443856),(108,2,36291612756),(109,3,36309442896),(110,3,36309442821),(111,4,36327272976),(112,1,36273415491),(113,2,36291306816),(114,2,36291306756),(115,3,36309198096),(116,2,36291305556),(117,3,36309197136),(118,3,36309197061),(119,4,36327088656),(120,2,36291282516),(121,3,36309177936),(122,3,36309177861),(123,4,36327073296),(124,3,36309176421)]++[(125,4,36327072096),(126,4,36327072006),(127,5,36344967696),(131,1,35020686096),(133,1,35020685616),(134,1,35020685571),(135,2,35289121296),(137,1,35020674096),(138,1,35020674051),(139,2,35289113616),(140,1,35020673091),(141,2,35289112896),(142,2,35289112836),(143,3,35557552656),(145,1,35020428336),(146,1,35020428291),(147,2,35288929296),(148,1,35020427331),(149,2,35288928576),(150,2,35288928516),(151,3,35557429776),(152,1,35020408131),(153,2,35288913216),(154,2,35288913156),(155,3,35557418256),(156,2,35288911956),(157,3,35557417296),(158,3,35557417221),(159,4,35825922576),(161,1,35015513136),(162,1,35015513091),(163,2,35284997136),(164,1,35015512131),(165,2,35284996416),(166,2,35284996356),(167,3,35554480656),(168,1,35015492931),(169,2,35284981056),(170,2,35284980996),(171,3,35554469136),(172,2,35284979796),(173,3,35554468176),(174,3,35554468101),(175,4,35823956496),(176,1,35015124291),(177,2,35284673856),(178,2,35284673796),(179,3,35554223376)]++[(180,2,35284672596),(181,3,35554222416),(182,3,35554222341),(183,4,35823772176),(184,2,35284649556),(185,3,35554203216),(186,3,35554203141),(187,4,35823756816),(188,3,35554201701),(189,4,35823755616),(190,4,35823755526),(191,5,36093309456),(193,1,34921141296),(194,1,34921141251),(195,2,35206353936),(196,1,34921140291),(197,2,35206353216),(198,2,35206353156),(199,3,35491566096),(200,1,34921121091),(201,2,35206337856),(202,2,35206337796),(203,3,35491554576),(204,2,35206336596),(205,3,35491553616),(206,3,35491553541),(207,4,35776770576),(208,1,34920752451),(209,2,35206030656),(210,2,35206030596),(211,3,35491308816),(212,2,35206029396),(213,3,35491307856),(214,3,35491307781),(215,4,35776586256),(216,2,35206006356),(217,3,35491288656),(218,3,35491288581),(219,4,35776570896),(220,3,35491287141),(221,4,35776569696),(222,4,35776569606),(223,5,36061852176),(224,1,34913871171),(225,2,35200132416),(226,2,35200132356),(227,3,35486393616),(228,2,35200131156)]++[(229,3,35486392656),(230,3,35486392581),(231,4,35772654096),(232,2,35200108116),(233,3,35486373456),(234,3,35486373381),(235,4,35772638736),(236,3,35486371941),(237,4,35772637536),(238,4,35772637446),(239,5,36058903056),(240,2,35199678036),(241,3,35486004816),(242,3,35486004741),(243,4,35772331536),(244,3,35486003301),(245,4,35772330336),(246,4,35772330246),(247,5,36058657296),(248,3,35485976421),(249,4,35772307296),(250,4,35772307206),(251,5,36058638096),(252,4,35772305526),(253,5,36058636656),(254,5,36058636551),(255,6,36344967696),(259,1,10861495056),(261,1,10861494576),(262,1,10861494531),(263,2,15156462096),(265,1,10861483056),(266,1,10861483011),(267,2,15156454416),(268,1,10861482051),(269,2,15156453696),(270,2,15156453636),(271,3,19451425296),(273,1,10861237296),(274,1,10861237251),(275,2,15156270096),(276,1,10861236291),(277,2,15156269376),(278,2,15156269316),(279,3,19451302416),(280,1,10861217091),(281,2,15156254016),(282,2,15156253956)]++[(283,3,19451290896),(284,2,15156252756),(285,3,19451289936),(286,3,19451289861),(287,4,23746327056),(289,1,10856322096),(290,1,10856322051),(291,2,15152337936),(292,1,10856321091),(293,2,15152337216),(294,2,15152337156),(295,3,19448353296),(296,1,10856301891),(297,2,15152321856),(298,2,15152321796),(299,3,19448341776),(300,2,15152320596),(301,3,19448340816),(302,3,19448340741),(303,4,23744360976),(304,1,10855933251),(305,2,15152014656),(306,2,15152014596),(307,3,19448096016),(308,2,15152013396),(309,3,19448095056),(310,3,19448094981),(311,4,23744176656),(312,2,15151990356),(313,3,19448075856),(314,3,19448075781),(315,4,23744161296),(316,3,19448074341),(317,4,23744160096),(318,4,23744160006),(319,5,28040245776),(321,1,10761950256),(322,1,10761950211),(323,2,15073694736),(324,1,10761949251),(325,2,15073694016),(326,2,15073693956),(327,3,19385438736),(328,1,10761930051),(329,2,15073678656),(330,2,15073678596),(331,3,19385427216),(332,2,15073677396)]++[(333,3,19385426256),(334,3,19385426181),(335,4,23697175056),(336,1,10761561411),(337,2,15073371456),(338,2,15073371396),(339,3,19385181456),(340,2,15073370196),(341,3,19385180496),(342,3,19385180421),(343,4,23696990736),(344,2,15073347156),(345,3,19385161296),(346,3,19385161221),(347,4,23696975376),(348,3,19385159781),(349,4,23696974176),(350,4,23696974086),(351,5,28008788496),(352,1,10754680131),(353,2,15067473216),(354,2,15067473156),(355,3,19380266256),(356,2,15067471956),(357,3,19380265296),(358,3,19380265221),(359,4,23693058576),(360,2,15067448916),(361,3,19380246096),(362,3,19380246021),(363,4,23693043216),(364,3,19380244581),(365,4,23693042016),(366,4,23693041926),(367,5,28005839376),(368,2,15067018836),(369,3,19379877456),(370,3,19379877381),(371,4,23692736016),(372,3,19379875941),(373,4,23692734816),(374,4,23692734726),(375,5,28005593616),(376,3,19379849061),(377,4,23692711776),(378,4,23692711686),(379,5,28005574416),(380,4,23692710006)]++[(381,5,28005572976),(382,5,28005572871),(383,6,32318435856),(385,1,9000342576),(386,1,9000342531),(387,2,13563745296),(388,1,9000341571),(389,2,13563744576),(390,2,13563744516),(391,3,18127147536),(392,1,9000322371),(393,2,13563729216),(394,2,13563729156),(395,3,18127136016),(396,2,13563727956),(397,3,18127135056),(398,3,18127134981),(399,4,22690542096),(400,1,8999953731),(401,2,13563422016),(402,2,13563421956),(403,3,18126890256),(404,2,13563420756),(405,3,18126889296),(406,3,18126889221),(407,4,22690357776),(408,2,13563397716),(409,3,18126870096),(410,3,18126870021),(411,4,22690342416),(412,3,18126868581),(413,4,22690341216),(414,4,22690341126),(415,5,27253813776),(416,1,8993072451),(417,2,13557523776),(418,2,13557523716),(419,3,18121975056),(420,2,13557522516),(421,3,18121974096),(422,3,18121974021),(423,4,22686425616),(424,2,13557499476),(425,3,18121954896),(426,3,18121954821),(427,4,22686410256),(428,3,18121953381),(429,4,22686409056)]++[(430,4,22686408966),(431,5,27250864656),(432,2,13557069396),(433,3,18121586256),(434,3,18121586181),(435,4,22686103056),(436,3,18121584741),(437,4,22686101856),(438,4,22686101766),(439,5,27250618896),(440,3,18121557861),(441,4,22686078816),(442,4,22686078726),(443,5,27250599696),(444,4,22686077046),(445,5,27250598256),(446,5,27250598151),(447,6,31815119376),(448,1,8867243331),(449,2,13447423296),(450,2,13447423236),(451,3,18027603216),(452,2,13447422036),(453,3,18027602256),(454,3,18027602181),(455,4,22607782416),(456,2,13447398996),(457,3,18027583056),(458,3,18027582981),(459,4,22607767056),(460,3,18027581541),(461,4,22607765856),(462,4,22607765766),(463,5,27187950096),(464,2,13446968916),(465,3,18027214416),(466,3,18027214341),(467,4,22607459856),(468,3,18027212901),(469,4,22607458656),(470,4,22607458566),(471,5,27187704336),(472,3,18027186021),(473,4,22607435616),(474,4,22607435526),(475,5,27187685136),(476,4,22607433846),(477,5,27187683696)]++[(478,5,27187683591),(479,6,31767933456),(480,2,13439104596),(481,3,18020333136),(482,3,18020333061),(483,4,22601561616),(484,3,18020331621),(485,4,22601560416),(486,4,22601560326),(487,5,27182789136),(488,3,18020304741),(489,4,22601537376),(490,4,22601537286),(491,5,27182769936),(492,4,22601535606),(493,5,27182768496),(494,5,27182768391),(495,6,31764001296),(496,3,18019813221),(497,4,22601107296),(498,4,22601107206),(499,5,27182401296),(500,4,22601105526),(501,5,27182399856),(502,5,27182399751),(503,6,31763694096),(504,4,22601074806),(505,5,27182372976),(506,5,27182372871),(507,6,31763671056),(508,5,27182370951),(509,6,31763669376),(510,6,31763669256),(511,7,36344967696)]⟩,
⟨[7],[[7,24,96,384],[9,36,130,272],[10,33,144,320],[12,48,66,129],[18,40,192,257],[17,72,160,260],[20,65,136,288],[34,80,132,264],[68,258]],[(25,8,36344967696),(26,8,36344967681),(28,8,36344967201),(41,8,36343984656),(42,8,36343984641),(44,8,36343984161),(49,8,36343861776),(50,8,36343861761),(52,8,36343861281),(56,9,36344967696),(57,10,36344967696),(58,10,36344967681),(60,10,36344967201),(73,8,36312527376),(74,8,36312527361),(76,8,36312526881),(81,8,36312404496),(82,8,36312404481),(84,8,36312404001),(88,9,36329239056),(89,10,36329239056),(90,10,36329239041),(92,10,36329238561),(97,8,36309455376),(98,8,36309455361),(100,8,36309454881),(104,9,36327272976),(105,10,36327272976),(106,10,36327272961),(108,10,36327272481),(112,9,36327088656),(113,10,36327088656),(114,10,36327088641),(116,10,36327088161),(120,11,36344967696),(121,12,36344967696),(122,12,36344967681),(124,12,36344967201),(137,8,35557552656),(138,8,35557552641),(140,8,35557552161),(145,8,35557429776),(146,8,35557429761),(148,8,35557429281),(152,9,35825922576),(153,10,35825922576),(154,10,35825922561),(156,10,35825922081)]++[(161,8,35554480656),(162,8,35554480641),(164,8,35554480161),(168,9,35823956496),(169,10,35823956496),(170,10,35823956481),(172,10,35823956001),(176,9,35823772176),(177,10,35823772176),(178,10,35823772161),(180,10,35823771681),(184,11,36093309456),(185,12,36093309456),(186,12,36093309441),(188,12,36093308961),(193,8,35491566096),(194,8,35491566081),(196,8,35491565601),(200,9,35776770576),(201,10,35776770576),(202,10,35776770561),(204,10,35776770081),(208,9,35776586256),(209,10,35776586256),(210,10,35776586241),(212,10,35776585761),(216,11,36061852176),(217,12,36061852176),(218,12,36061852161),(220,12,36061851681),(224,9,35772654096),(225,10,35772654096),(226,10,35772654081),(228,10,35772653601),(232,11,36058903056),(233,12,36058903056),(234,12,36058903041),(236,12,36058902561),(240,11,36058657296),(241,12,36058657296),(242,12,36058657281),(244,12,36058656801),(248,13,36344967696),(249,14,36344967696),(250,14,36344967681),(252,14,36344967201),(265,8,19451425296),(266,8,19451425281)]++[(268,8,19451424801),(273,8,19451302416),(274,8,19451302401),(276,8,19451301921),(280,9,23746327056),(281,10,23746327056),(282,10,23746327041),(284,10,23746326561),(289,8,19448353296),(290,8,19448353281),(292,8,19448352801),(296,9,23744360976),(297,10,23744360976),(298,10,23744360961),(300,10,23744360481),(304,9,23744176656),(305,10,23744176656),(306,10,23744176641),(308,10,23744176161),(312,11,28040245776),(313,12,28040245776),(314,12,28040245761),(316,12,28040245281),(321,8,19385438736),(322,8,19385438721),(324,8,19385438241),(328,9,23697175056),(329,10,23697175056),(330,10,23697175041),(332,10,23697174561),(336,9,23696990736),(337,10,23696990736),(338,10,23696990721),(340,10,23696990241),(344,11,28008788496),(345,12,28008788496),(346,12,28008788481),(348,12,28008788001),(352,9,23693058576),(353,10,23693058576),(354,10,23693058561),(356,10,23693058081),(360,11,28005839376),(361,12,28005839376),(362,12,28005839361),(364,12,28005838881),(368,11,28005593616),(369,12,28005593616)]++[(370,12,28005593601),(372,12,28005593121),(376,13,32318435856),(377,14,32318435856),(378,14,32318435841),(380,14,32318435361),(385,8,18127147536),(386,8,18127147521),(388,8,18127147041),(392,9,22690542096),(393,10,22690542096),(394,10,22690542081),(396,10,22690541601),(400,9,22690357776),(401,10,22690357776),(402,10,22690357761),(404,10,22690357281),(408,11,27253813776),(409,12,27253813776),(410,12,27253813761),(412,12,27253813281),(416,9,22686425616),(417,10,22686425616),(418,10,22686425601),(420,10,22686425121),(424,11,27250864656),(425,12,27250864656),(426,12,27250864641),(428,12,27250864161),(432,11,27250618896),(433,12,27250618896),(434,12,27250618881),(436,12,27250618401),(440,13,31815119376),(441,14,31815119376),(442,14,31815119361),(444,14,31815118881),(448,9,22607782416),(449,10,22607782416),(450,10,22607782401),(452,10,22607781921),(456,11,27187950096),(457,12,27187950096),(458,12,27187950081),(460,12,27187949601),(464,11,27187704336),(465,12,27187704336),(466,12,27187704321)]++[(468,12,27187703841),(472,13,31767933456),(473,14,31767933456),(474,14,31767933441),(476,14,31767932961),(480,11,27182789136),(481,12,27182789136),(482,12,27182789121),(484,12,27182788641),(488,13,31764001296),(489,14,31764001296),(490,14,31764001281),(492,14,31764000801),(496,13,31763694096),(497,14,31763694096),(498,14,31763694081),(500,14,31763693601),(504,15,36344967696),(505,16,36344967696),(506,16,36344967681),(508,16,36344967201)]⟩,
⟨[15],[[15,48,192],[17,68,136,288],[18,40,65,384],[20,72,130,257],[24,96,132,258],[34,80,129,260],[33,144,320],[66,160,272],[36,264]],[(49,10,36341634096),(50,10,36341634051),(52,10,36341633091),(56,10,36341613891),(81,10,36278719536),(82,10,36278719491),(84,10,36278718531),(88,10,36278699331),(97,10,36273804336),(98,10,36273804291),(100,10,36273803331),(104,10,36273784131),(112,11,36273415491),(113,17,36344967696),(114,17,36344967681),(116,17,36344967201),(120,17,36344955681),(145,10,35020428336),(146,10,35020428291),(148,10,35020427331),(152,10,35020408131),(161,10,35015513136),(162,10,35015513091),(164,10,35015512131),(168,10,35015492931),(176,11,35015124291),(177,17,36093309456),(178,17,36093309441),(180,17,36093308961),(184,17,36093297441),(193,10,34921141296),(194,10,34921141251),(196,10,34921140291),(200,10,34921121091),(208,11,34920752451),(209,17,36061852176),(210,17,36061852161),(212,17,36061851681),(216,17,36061840161),(224,11,34913871171),(225,17,36058903056),(226,17,36058903041),(228,17,36058902561),(232,17,36058891041),(240,18,36344967696),(241,19,36344967696),(242,19,36344967681),(244,19,36344967201)]++[(248,19,36344955681),(273,10,10861237296),(274,10,10861237251),(276,10,10861236291),(280,10,10861217091),(289,10,10856322096),(290,10,10856322051),(292,10,10856321091),(296,10,10856301891),(304,11,10855933251),(305,17,28040245776),(306,17,28040245761),(308,17,28040245281),(312,17,28040233761),(321,10,10761950256),(322,10,10761950211),(324,10,10761949251),(328,10,10761930051),(336,11,10761561411),(337,17,28008788496),(338,17,28008788481),(340,17,28008788001),(344,17,28008776481),(352,11,10754680131),(353,17,28005839376),(354,17,28005839361),(356,17,28005838881),(360,17,28005827361),(368,18,32318435856),(369,19,32318435856),(370,19,32318435841),(372,19,32318435361),(376,19,32318423841),(385,10,9000342576),(386,10,9000342531),(388,10,9000341571),(392,10,9000322371),(400,11,8999953731),(401,17,27253813776),(402,17,27253813761),(404,17,27253813281),(408,17,27253801761),(416,11,8993072451),(417,17,27250864656),(418,17,27250864641),(420,17,27250864161),(424,17,27250852641),(432,18,31815119376)]++[(433,19,31815119376),(434,19,31815119361),(436,19,31815118881),(440,19,31815107361),(448,11,8867243331),(449,17,27187950096),(450,17,27187950081),(452,17,27187949601),(456,17,27187938081),(464,18,31767933456),(465,19,31767933456),(466,19,31767933441),(468,19,31767932961),(472,19,31767921441),(480,18,31764001296),(481,19,31764001296),(482,19,31764001281),(484,19,31764000801),(488,19,31763989281),(496,20,36344967696),(497,21,36344967696),(498,21,36344967681),(500,21,36344967201),(504,21,36344955681)]⟩,
⟨[31],[[31,96,384],[33,66,132,264],[34,129,320],[36,65,136,258],[40,68,144,257],[48,192,260],[72,160,272],[80,130,288],[]],[(97,12,36273804336),(98,12,36273804291),(100,12,36273803331),(104,12,36273784131),(112,12,36273415491),(161,12,35015513136),(162,12,35015513091),(164,12,35015512131),(168,12,35015492931),(176,12,35015124291),(193,12,34921141296),(194,12,34921141251),(196,12,34921140291),(200,12,34921121091),(208,12,34920752451),(224,13,34913871171),(225,19,35200132416),(226,19,35200132356),(228,19,35200131156),(232,19,35200108116),(240,19,35199678036),(289,12,10856322096),(290,12,10856322051),(292,12,10856321091),(296,12,10856301891),(304,12,10855933251),(321,12,10761950256),(322,12,10761950211),(324,12,10761949251),(328,12,10761930051),(336,12,10761561411),(352,13,10754680131),(353,19,15067473216),(354,19,15067473156),(356,19,15067471956),(360,19,15067448916),(368,19,15067018836),(385,12,9000342576),(386,12,9000342531),(388,12,9000341571),(392,12,9000322371),(400,12,8999953731),(416,13,8993072451),(417,19,13557523776),(418,19,13557523716),(420,19,13557522516),(424,19,13557499476),(432,19,13557069396)]++[(448,13,8867243331),(449,19,13447423296),(450,19,13447423236),(452,19,13447422036),(456,19,13447398996),(464,19,13446968916),(480,20,13439104596),(481,22,36344967696),(482,22,36344967681),(484,22,36344967201),(488,22,36344955681),(496,22,36344709921)]⟩
]
private def data9Part1 : Array E19Cert.Row := #[
⟨[63],[[63,192],[65,130,260],[66,144,257],[68,129,264],[72,132,272],[80,136,288],[96,384],[160,320],[258]],[(193,14,34921141296),(194,14,34921141251),(196,14,34921140291),(200,14,34921121091),(208,14,34920752451),(224,14,34913871171),(321,14,10761950256),(322,14,10761950211),(324,14,10761949251),(328,14,10761930051),(336,14,10761561411),(352,14,10754680131),(385,14,9000342576),(386,14,9000342531),(388,14,9000341571),(392,14,9000322371),(400,14,8999953731),(416,14,8993072451),(448,15,8867243331),(449,21,13447423296),(450,21,13447423236),(452,21,13447422036),(456,21,13447398996),(464,21,13446968916),(480,21,13439104596)]⟩,
⟨[127],[[127,384],[129,260],[130,257],[132,264],[136,272],[144,288],[160,320],[192,258],[]],[(385,16,9000342576),(386,16,9000342531),(388,16,9000341571),(392,16,9000322371),(400,16,8999953731),(416,16,8993072451),(448,16,8867243331)]⟩,
⟨[255],[[255],[257],[258],[260],[264],[272],[288],[320],[384]],[]⟩,
⟨[511],[[511],[],[],[],[],[],[],[],[]],[]⟩
]
private def data9Part2 : Array E19Cert.Row := #[
⟨[7,25],[[7,40,192,272],[25,66,132,288],[10,68,160,257],[12,96,129,258],[48,72,384],[18,36,136,320],[33,80,130,264],[34,65,144,260],[20]],[(42,23,36344967696),(44,23,36344967456),(50,23,36344906256),(52,23,36344906016),(74,23,36329239056),(76,23,36329238816),(82,23,36329177616),(84,23,36329177376),(97,24,36344967696),(98,25,36344967696),(100,25,36344967456),(104,25,36344828976),(106,26,36344967696),(108,26,36344967456),(112,25,36344767536),(114,26,36344906256),(116,26,36344906016),(138,23,35825922576),(140,23,35825922336),(146,23,35825861136),(148,23,35825860896),(161,24,36093309456),(162,25,36093309456),(164,25,36093309216),(168,25,36093170736),(170,26,36093309456),(172,26,36093309216),(176,25,36093109296),(178,26,36093248016),(180,26,36093247776),(193,24,36061852176),(194,25,36061852176),(196,25,36061851936),(200,25,36061713456),(202,26,36061852176),(204,26,36061851936),(208,25,36061652016),(210,26,36061790736),(212,26,36061790496),(224,27,36344967696),(225,28,36344967696),(226,29,36344967696),(228,29,36344967456),(232,29,36344828976),(234,30,36344967696),(236,30,36344967456),(240,29,36344767536),(242,30,36344906256)]++[(244,30,36344906016),(266,23,23746327056),(268,23,23746326816),(274,23,23746265616),(276,23,23746265376),(289,24,28040245776),(290,25,28040245776),(292,25,28040245536),(296,25,28040107056),(298,26,28040245776),(300,26,28040245536),(304,25,28040045616),(306,26,28040184336),(308,26,28040184096),(321,24,28008788496),(322,25,28008788496),(324,25,28008788256),(328,25,28008649776),(330,26,28008788496),(332,26,28008788256),(336,25,28008588336),(338,26,28008727056),(340,26,28008726816),(352,27,32318435856),(353,28,32318435856),(354,29,32318435856),(356,29,32318435616),(360,29,32318297136),(362,30,32318435856),(364,30,32318435616),(368,29,32318235696),(370,30,32318374416),(372,30,32318374176),(385,24,27253813776),(386,25,27253813776),(388,25,27253813536),(392,25,27253675056),(394,26,27253813776),(396,26,27253813536),(400,25,27253613616),(402,26,27253752336),(404,26,27253752096),(416,27,31815119376),(417,28,31815119376),(418,29,31815119376),(420,29,31815119136),(424,29,31814980656),(426,30,31815119376)]++[(428,30,31815119136),(432,29,31814919216),(434,30,31815057936),(436,30,31815057696),(448,27,31767933456),(449,28,31767933456),(450,29,31767933456),(452,29,31767933216),(456,29,31767794736),(458,30,31767933456),(460,30,31767933216),(464,29,31767733296),(466,30,31767872016),(468,30,31767871776),(480,31,36344967696),(481,32,36344967696),(482,33,36344967696),(484,33,36344967456),(488,33,36344828976),(490,34,36344967696),(492,34,36344967456),(496,33,36344767536),(498,34,36344906256),(500,34,36344906016)]⟩,
⟨[7,56],[[7,56,192],[10,65,144,260],[36,66,136,257],[17,68,130,264],[9,34,132,320],[72,160,272],[12,80,129,288],[18,96,384],[20,33,258]],[(73,25,36278965296),(74,25,36278965251),(76,25,36278964291),(81,25,36278719536),(82,25,36278719491),(84,25,36278718531),(97,25,36273804336),(98,25,36273804291),(100,25,36273803331),(137,25,35020674096),(138,25,35020674051),(140,25,35020673091),(145,25,35020428336),(146,25,35020428291),(148,25,35020427331),(161,25,35015513136),(162,25,35015513091),(164,25,35015512131),(193,27,35491566096),(194,27,35491566081),(196,27,35491565601),(200,27,35485976421),(201,35,36344967696),(202,35,36344967681),(204,35,36344967201),(208,27,35485914981),(209,35,36344906256),(210,35,36344906241),(212,35,36344905761),(224,27,35483948901),(225,35,36342940176),(226,35,36342940161),(228,35,36342939681),(265,25,10861483056),(266,25,10861483011),(268,25,10861482051),(273,25,10861237296),(274,25,10861237251),(276,25,10861236291),(289,25,10856322096),(290,25,10856322051),(292,25,10856321091),(321,27,19385438736),(322,27,19385438721),(324,27,19385438241),(328,27,19379849061),(329,35,32318435856),(330,35,32318435841)]++[(332,35,32318435361),(336,27,19379787621),(337,35,32318374416),(338,35,32318374401),(340,35,32318373921),(352,27,19377821541),(353,35,32316408336),(354,35,32316408321),(356,35,32316407841),(385,27,18127147536),(386,27,18127147521),(388,27,18127147041),(392,27,18121557861),(393,35,31815119376),(394,35,31815119361),(396,35,31815118881),(400,27,18121496421),(401,35,31815057936),(402,35,31815057921),(404,35,31815057441),(416,27,18119530341),(417,35,31813091856),(418,35,31813091841),(420,35,31813091361),(448,36,36344967696),(449,37,36344967696),(450,37,36344967681),(452,37,36344967201),(456,37,36341613891),(457,38,36344967696),(458,38,36344967681),(460,38,36344967201),(464,37,36341552451),(465,38,36344906256),(466,38,36344906241),(468,38,36344905761),(480,37,36339586371),(481,38,36342940176),(482,38,36342940161),(484,38,36342939681)]⟩,
⟨[7,57],[[57,68,130],[7,72,384],[10,132,320],[12,18,192,288],[20,96,136,258],[36,65,144,264],[80,160,260],[66,129,272],[34,257]],[(74,26,36312527361),(76,26,36312526881),(82,26,36312404481),(84,26,36312404001),(98,26,36309455361),(100,26,36309454881),(138,26,35557552641),(140,26,35557552161),(146,26,35557429761),(148,26,35557429281),(162,26,35554480641),(164,26,35554480161),(193,28,35491566096),(194,29,35491566081),(196,29,35491565601),(200,35,35776770576),(202,39,36344967696),(204,39,36344967456),(208,35,35776586256),(210,39,36344906256),(212,39,36344906016),(224,35,35772654096),(226,39,36342940176),(228,39,36342939936),(266,26,19451425281),(268,26,19451424801),(274,26,19451302401),(276,26,19451301921),(290,26,19448353281),(292,26,19448352801),(321,28,19385438736),(322,29,19385438721),(324,29,19385438241),(328,35,23697175056),(330,39,32318435856),(332,39,32318435616),(336,35,23696990736),(338,39,32318374416),(340,39,32318374176),(352,35,23693058576),(354,39,32316408336),(356,39,32316408096),(385,28,18127147536),(386,29,18127147521),(388,29,18127147041),(392,35,22690542096),(394,39,31815119376),(396,39,31815119136)]++[(400,35,22690357776),(402,39,31815057936),(404,39,31815057696),(416,35,22686425616),(418,39,31813091856),(420,39,31813091616),(448,37,22607782416),(449,40,36344967696),(450,41,36344967696),(452,41,36344967456),(456,42,36344967696),(458,43,36344967696),(460,43,36344967456),(464,42,36344906256),(466,43,36344906256),(468,43,36344906016),(480,42,36342940176),(482,43,36342940176),(484,43,36342939936)]⟩,
⟨[7,120],[[7,120,384],[20,65,136,258],[9,66,144,260],[10,68,160,257],[12,17,192,288],[18,36,129,264],[33,130,272],[34,132,320],[]],[(137,29,35020674096),(138,29,35020674051),(140,29,35020673091),(145,29,35020428336),(146,29,35020428291),(148,29,35020427331),(161,29,35015513136),(162,29,35015513091),(164,29,35015512131),(193,29,34921141296),(194,29,34921141251),(196,29,34921140291),(265,29,10861483056),(266,29,10861483011),(268,29,10861482051),(273,29,10861237296),(274,29,10861237251),(276,29,10861236291),(289,29,10856322096),(290,29,10856322051),(292,29,10856321091),(321,29,10761950256),(322,29,10761950211),(324,29,10761949251),(385,31,18127147536),(386,31,18127147521),(388,31,18127147041),(392,37,9000322371),(393,42,22690542096),(394,42,22690542081),(396,42,22690541601),(400,37,8999953731),(401,42,22690357776),(402,42,22690357761),(404,42,22690357281),(416,37,8993072451),(417,42,22686425616),(418,42,22686425601),(420,42,22686425121),(448,37,8867243331),(449,42,22607782416),(450,42,22607782401),(452,42,22607781921)]⟩
]
private def data9Part3 : Array E19Cert.Row := #[
⟨[7,121],[[121,132,258],[7,136,272],[10,160,260],[12,66,384],[18,36,192,264],[34,68,144,257],[20,130,288],[129,320],[]],[(138,30,35557552641),(140,30,35557552161),(146,30,35557429761),(148,30,35557429281),(162,30,35554480641),(164,30,35554480161),(194,30,35491566081),(196,30,35491565601),(266,30,19451425281),(268,30,19451424801),(274,30,19451302401),(276,30,19451301921),(290,30,19448353281),(292,30,19448352801),(322,30,19385438721),(324,30,19385438241),(385,32,18127147536),(386,33,18127147521),(388,33,18127147041),(392,38,22690542096),(394,43,22690542081),(396,43,22690541601),(400,38,22690357776),(402,43,22690357761),(404,43,22690357281),(416,38,22686425616),(418,43,22686425601),(420,43,22686425121),(448,38,22607782416),(450,43,22607782401),(452,43,22607781921)]⟩,
⟨[7,248],[[248,257],[7,264],[10,36,129,272],[18,65,132,288],[9,20,34,320],[12,17,66,384],[33,68,258],[130,260],[]],[(265,33,10861483056),(266,33,10861483011),(268,33,10861482051),(273,33,10861237296),(274,33,10861237251),(276,33,10861236291),(289,33,10856322096),(290,33,10856322051),(292,33,10856321091),(321,33,10761950256),(322,33,10761950211),(324,33,10761949251),(385,33,9000342576),(386,33,9000342531),(388,33,9000341571)]⟩,
⟨[7,249],[[249,258],[7,264],[10,36,272],[12,18,320],[34,68,384],[66,132,288],[130,260],[20,257],[]],[(266,34,19451425281),(268,34,19451424801),(274,34,19451302401),(276,34,19451301921),(290,34,19448353281),(292,34,19448352801),(322,34,19385438721),(324,34,19385438241),(386,34,18127147521),(388,34,18127147041)]⟩,
⟨[7,504],[[7,504],[9,20,66],[10,17,132],[12,18,33],[65,130,260],[36,129,258],[34,68,257],[],[]],[]⟩
]
private def data9Part4 : Array E19Cert.Row := #[
⟨[7,505],[[7],[505],[10,36],[12,18],[34,68],[66,132],[130,260],[20,258],[]],[]⟩,
⟨[15,113],[[15,144,288],[113,132,258],[18,40,192,260],[20,66,160,264],[24,34,68,384],[36,72,130,272],[136,257],[129,320],[]],[(146,39,35020428291),(148,39,35020427331),(152,39,35020408131),(162,39,35015513091),(164,39,35015512131),(168,39,35015492931),(194,39,34921141251),(196,39,34921140291),(200,39,34921121091),(274,39,10861237251),(276,39,10861236291),(280,39,10861217091),(290,39,10856322051),(292,39,10856321091),(296,39,10856301891),(322,39,10761950211),(324,39,10761949251),(328,39,10761930051),(385,40,9000342576),(386,42,9000342531),(388,42,9000341571),(392,42,9000322371),(400,42,8946485091),(402,44,36344967696),(404,44,36344967456),(408,44,36344959776),(416,42,8942552931),(418,44,36343984656),(420,44,36343984416),(424,44,36343976736),(448,42,8863909731),(450,44,36312527376),(452,44,36312527136),(456,44,36312519456)]⟩,
⟨[15,240],[[15,272],[240,257],[17,40,132,258],[34,72,129,260],[20,33,66,264],[24,68,130,288],[18,36,136,320],[65,384],[]],[(273,41,10861237296),(274,41,10861237251),(276,41,10861236291),(280,41,10861217091),(289,41,10856322096),(290,41,10856322051),(292,41,10856321091),(296,41,10856301891),(321,41,10761950256),(322,41,10761950211),(324,41,10761949251),(328,41,10761930051),(385,41,9000342576),(386,41,9000342531),(388,41,9000341571),(392,41,9000322371)]⟩,
⟨[15,241],[[241,258],[15,272],[18,40,260],[20,34,72,384],[24,68,130,288],[36,136,320],[66,132,264],[257],[]],[(274,43,10861237251),(276,43,10861236291),(280,43,10861217091),(290,43,10856322051),(292,43,10856321091),(296,43,10856301891),(322,43,10761950211),(324,43,10761949251),(328,43,10761930051),(386,43,9000342531),(388,43,9000341571),(392,43,9000322371)]⟩
]
private def data9Part5 : Array E19Cert.Row := #[
⟨[15,496],[[15,496],[17,36,66,264],[18,33,72,132],[20,40,65,258],[24,34,68,129],[130,257],[136,260],[],[]],[]⟩,
⟨[15,497],[[15],[497],[18,40,132],[20,34,264],[24,36,66],[72,130,260],[68,136,258],[],[]],[]⟩,
⟨[31,481],[[31],[481],[34,72,132,272],[36,66,144,264],[40,80,130,260],[48,68,136,258],[],[],[]],[]⟩,
⟨[7,25,42],[[7,48,136,320],[25,68,130,288],[20,42,192,257],[12,96,129,272],[33,80,132,264],[18,72,160,260],[36,65,384],[66,144],[258]],[(52,45,36344967696),(76,46,36344967696),(82,46,36344828976),(84,47,36344967696),(97,46,36341879811),(100,47,36343984641),(112,47,36343776561),(116,48,36344967696),(140,46,36093309456),(146,46,36093170736),(148,47,36093309456),(161,46,36090221571),(164,47,36092326401),(176,47,36092118321),(180,48,36093309456),(193,49,36344967696),(194,49,36343984641),(196,50,36344967696),(200,49,36343776561),(204,51,36344967696),(208,50,36344828976),(210,51,36344828976),(212,52,36344967696),(224,50,36341879811),(225,51,36341879811),(228,52,36343984641),(240,52,36343776561),(244,53,36344967696),(268,46,28040245776),(274,46,28040107056),(276,47,28040245776),(289,46,28037157891),(292,47,28039262721),(304,47,28039054641),(308,48,28040245776),(321,49,32318435856),(322,49,32317452801),(324,50,32318435856),(328,49,32317244721),(332,51,32318435856),(336,50,32318297136),(338,51,32318297136),(340,52,32318435856),(352,50,32315347971),(353,51,32315347971),(356,52,32317452801),(368,52,32317244721),(372,53,32318435856)]++[(385,49,31815119376),(386,49,31814136321),(388,50,31815119376),(392,49,31813928241),(396,51,31815119376),(400,50,31814980656),(402,51,31814980656),(404,52,31815119376),(416,50,31812031491),(417,51,31812031491),(420,52,31814136321),(432,52,31813928241),(436,53,31815119376),(448,54,36344967696),(449,55,36344967696),(450,55,36343984641),(452,56,36344967696),(456,55,36343776561),(460,57,36344967696),(464,56,36344828976),(466,57,36344828976),(468,58,36344967696),(480,56,36341879811),(481,57,36341879811),(484,58,36343984641),(496,58,36343776561),(500,59,36344967696)]⟩
]
private def data9Part6 : Array E19Cert.Row := #[
⟨[7,25,97],[[7,48,72,384],[25,68,130,288],[20,97,136,258],[18,36,129,264],[12,66,144,257],[40,132,320],[10,80,160,260],[34,192,272],[]],[(42,46,36341879811),(44,46,36341878851),(50,46,36341634051),(52,46,36341633091),(74,46,36278965251),(76,46,36278964291),(82,46,36278719491),(84,46,36278718531),(138,49,35825922576),(140,49,35825922336),(146,49,35825861136),(148,49,35825860896),(162,49,35772654096),(164,49,35772653856),(168,49,35772307296),(170,60,36344967696),(172,60,36344967456),(176,49,35772245856),(178,60,36344906256),(180,60,36344906016),(194,49,35756925456),(196,49,35756925216),(200,49,35756578656),(202,60,36329239056),(204,60,36329238816),(208,49,35756517216),(210,60,36329177616),(212,60,36329177376),(266,49,23746327056),(268,49,23746326816),(274,49,23746265616),(276,49,23746265376),(290,49,23693058576),(292,49,23693058336),(296,49,23692711776),(298,60,32318435856),(300,60,32318435616),(304,49,23692650336),(306,60,32318374416),(308,60,32318374176),(322,49,23677329936),(324,49,23677329696),(328,49,23676983136),(330,60,32302707216),(332,60,32302706976),(336,49,23676921696),(338,60,32302645776),(340,60,32302645536)]++[(385,61,36344967696),(386,62,36344967696),(388,62,36344967456),(392,62,36344828976),(394,63,36344967696),(396,63,36344967456),(400,62,36344767536),(402,63,36344906256),(404,63,36344906016),(416,62,36273804336),(418,63,36309455376),(420,63,36309455136),(424,63,36309177936),(426,64,36344967696),(428,64,36344967456),(432,63,36309116496),(434,64,36344906256),(436,64,36344906016),(448,62,36258075696),(450,63,36293726736),(452,63,36293726496),(456,63,36293449296),(458,64,36329239056),(460,64,36329238816),(464,63,36293387856),(466,64,36329177616),(468,64,36329177376)]⟩,
⟨[7,25,98],[[25,98,132],[7,144,264],[12,33,130,272],[20,72,129,288],[18,40,192,260],[36,136,320],[10,48,68,384],[80,160,257],[65,258]],[(44,47,36343984161),(52,47,36343861281),(76,47,36312526881),(84,47,36312404001),(138,49,35557552641),(140,50,35825922336),(146,49,35557429761),(148,50,35825860896),(161,49,35520995856),(164,50,35772653826),(168,65,36344967696),(172,66,36344967696),(176,65,36344906256),(180,66,36344906256),(193,49,35489538576),(196,50,35756925186),(200,65,36329239056),(204,66,36329239056),(208,65,36329177616),(212,66,36329177616),(266,49,19451425281),(268,50,23746326816),(274,49,19451302401),(276,50,23746265376),(289,49,19414868496),(292,50,23693058306),(296,65,32318435856),(300,66,32318435856),(304,65,32318374416),(308,66,32318374416),(321,49,19383411216),(324,50,23677329666),(328,65,32302707216),(332,66,32302707216),(336,65,32302645776),(340,66,32302645776),(385,62,27253813776),(386,62,27182789121),(388,67,36344967696),(392,68,36344967696),(394,69,36344967696),(396,70,36344967696),(400,68,36344906256),(402,69,36344906256),(404,70,36344906256),(416,68,36309455361),(417,69,36309455361),(420,70,36309455361)]++[(424,71,36344967696),(428,72,36344967696),(432,71,36344906256),(436,72,36344906256),(448,68,36293726721),(449,69,36293726721),(452,70,36293726721),(456,71,36329239056),(460,72,36329239056),(464,71,36329177616),(468,72,36329177616)]⟩,
⟨[7,25,106],[[20,106,384],[7,48,192,264],[25,132,288],[12,65,160,272],[33,80,130,260],[18,36,129,320],[68,144,258],[136,257],[]],[(52,48,36344906016),(84,48,36329177376),(140,51,35825922336),(146,51,35825722416),(148,52,35825860896),(161,60,36093309456),(164,66,36093309216),(176,66,36093109296),(180,73,36344967696),(193,60,36061852176),(196,66,36061851936),(208,66,36061652016),(212,73,36329239056),(268,51,23746326816),(274,51,23746126896),(276,52,23746265376),(289,60,28040245776),(292,66,28040245536),(304,66,28040045616),(308,73,32318435856),(321,60,28008788496),(324,66,28008788256),(336,66,28008588336),(340,73,32302707216),(385,63,27253813776),(386,69,27253813776),(388,70,27253813536),(392,69,27253675056),(396,74,36344967696),(400,70,27253613616),(402,74,36344828976),(404,75,36344967696),(416,76,36344967696),(417,77,36344967696),(420,78,36344967696),(432,78,36344828976),(436,79,36344967696),(448,76,36329239056),(449,77,36329239056),(452,78,36329239056),(464,78,36329100336),(468,79,36329239056)]⟩,
⟨[7,25,224],[[25,224,258],[7,72,144,288],[12,48,130,320],[20,40,66,384],[18,65,136,260],[36,80,129,264],[10,33,68,272],[34,132,257],[]],[(42,50,36341879811),(44,50,36341878851),(50,50,36341634051),(52,50,36341633091),(74,50,36278965251),(76,50,36278964291),(82,50,36278719491),(84,50,36278718531),(138,50,35020674051),(140,50,35020673091),(146,50,35020428291),(148,50,35020427331),(266,54,23746327056),(268,54,23746326816),(274,54,23746265616),(276,54,23746265376),(289,62,10856322096),(290,68,19448353281),(292,68,19448352801),(296,68,19448071761),(298,76,28040245776),(300,76,28040245536),(304,68,19447948881),(306,76,28040184336),(308,76,28040184096),(321,62,10761950256),(322,68,19385438721),(324,68,19385438241),(328,68,19385157201),(330,76,28008788496),(332,76,28008788256),(336,68,19385034321),(338,76,28008727056),(340,76,28008726816),(385,62,9000342576),(386,68,18127147521),(388,68,18127147041),(392,68,18126866001),(394,76,27253813776),(396,76,27253813536),(400,68,18126743121),(402,76,27253752336),(404,76,27253752096)]⟩,
⟨[7,25,225],[[20,225,258],[7,48,264],[25,66,260],[18,36,136,257],[40,68,130,272],[10,80,132,288],[12,34,144,320],[72,384],[]],[(42,51,36341879811),(44,51,36341878851),(50,51,36341634051),(52,51,36341633091),(74,51,36278965251),(76,51,36278964291),(82,51,36278719491),(84,51,36278718531),(138,51,35020674051),(140,51,35020673091),(146,51,35020428291),(148,51,35020427331),(266,55,23746327056),(268,55,23746326816),(274,55,23746265616),(276,55,23746265376),(290,69,19448353281),(292,69,19448352801),(296,69,19448071761),(298,77,28040245776),(300,77,28040245536),(304,69,19447948881),(306,77,28040184336),(308,77,28040184096),(322,69,19385438721),(324,69,19385438241),(328,69,19385157201),(330,77,28008788496),(332,77,28008788256),(336,69,19385034321),(338,77,28008727056),(340,77,28008726816),(386,69,18127147521),(388,69,18127147041),(392,69,18126866001),(394,77,27253813776),(396,77,27253813536),(400,69,18126743121),(402,77,27253752336),(404,77,27253752096)]⟩,
⟨[7,25,226],[[25,226,260],[7,40,272],[18,36,65,264],[48,68,136,257],[10,80,132,288],[12,33,144,320],[20,72,384],[129,258],[]],[(44,52,36343984161),(52,52,36343861281),(76,52,36312526881),(84,52,36312404001),(140,52,35557552161),(148,52,35557429281),(266,55,19451425281),(268,56,23746326816),(274,55,19451302401),(276,56,23746265376),(289,63,19448353296),(292,70,19448352801),(296,71,28040107056),(300,78,28040245536),(304,71,28040045616),(308,78,28040184096),(321,63,19385438736),(324,70,19385438241),(328,71,28008649776),(332,78,28008788256),(336,71,28008588336),(340,78,28008726816),(385,63,18127147536),(388,70,18127147041),(392,71,27253675056),(396,78,27253813536),(400,71,27253613616),(404,78,27253752096)]⟩,
⟨[7,25,234],[[20,234,257],[7,80,288],[25,260],[12,33,144,320],[18,36,65,384],[68,129,272],[48,132,258],[264],[]],[(52,53,36344906016),(84,53,36329177376),(148,53,35825860896),(268,57,23746326816),(274,57,23746126896),(276,58,23746265376),(289,64,28040245776),(292,72,28040245536),(304,72,28040045616),(308,79,28040184096),(321,64,28008788496),(324,72,28008788256),(336,72,28008588336),(340,79,28008726816),(385,64,27253813776),(388,72,27253813536),(400,72,27253613616),(404,79,27253752096)]⟩,
⟨[7,25,480],[[7,480],[25,34,132],[10,36,65,144],[18,40,129,260],[12,48,66,257],[20,33,72,258],[68,136,272],[80,130,264],[]],[(42,56,36341879811),(44,56,36341878851),(50,56,36341634051),(52,56,36341633091),(74,56,36278965251),(76,56,36278964291),(82,56,36278719491),(84,56,36278718531),(138,56,35020674051),(140,56,35020673091),(146,56,35020428291),(148,56,35020427331),(266,56,10861483011),(268,56,10861482051),(274,56,10861237251),(276,56,10861236291)]⟩,
⟨[7,25,481],[[10,20,481],[7,40,80],[25,34,68],[12,18],[36,66,136,272],[48,72,130,260],[132,258],[144,264],[]],[(42,57,36341879811),(44,57,36341878851),(50,57,36341634051),(52,57,36341633091),(74,57,36278965251),(76,57,36278964291),(82,57,36278719491),(84,57,36278718531),(138,57,35020674051),(140,57,35020673091),(146,57,35020428291),(148,57,35020427331),(266,57,10861483011),(268,57,10861482051),(274,57,10861237251),(276,57,10861236291)]⟩,
⟨[7,25,482],[[12,482],[7,80,136],[25,36],[33,68,144,264],[40,65,132,272],[10,48,129,260],[20,72,257],[18],[]],[(44,58,36343984161),(52,58,36343861281),(76,58,36312526881),(84,58,36312404001),(140,58,35557552161),(148,58,35557429281),(268,58,19451424801),(276,58,19451301921)]⟩,
⟨[7,25,490],[[20,490],[7,80],[25,36],[12,65,144],[68,129,272],[48,132,257],[18,33,260],[],[]],[(52,59,36344906016),(84,59,36329177376),(148,59,35825860896),(276,59,23746265376)]⟩,
⟨[7,56,201],[[18,36,201],[7,56,320],[20,66,160,257],[34,68,272],[33,80,132,258],[10,96,144,260],[12,17,130,288],[264],[384]],[(82,66,36278719491),(84,66,36278718531),(98,66,36273804291),(100,66,36273803331),(146,66,35020428291),(148,66,35020427331),(162,66,35015513091),(164,66,35015512131),(266,69,10861483011),(268,69,10861482051),(273,69,10859066961),(274,71,10861237251),(276,71,10861236291),(289,69,10855134801),(290,71,10856322051),(292,71,10856321091),(322,76,18849681921),(324,76,18849681441),(336,76,18842916981),(338,80,36344967696),(340,80,36344967456),(352,76,18840950901),(354,80,36343984656),(356,80,36343984416),(386,76,18094707201),(388,76,18094706721),(400,76,18087942261),(402,80,36093309456),(404,80,36093309216),(416,76,18085976181),(418,80,36092326416),(420,80,36092326176)]⟩,
⟨[7,56,448],[[7,56,448],[9,34,68,144],[10,65,132,272],[12,17,66,288],[33,72,130,260],[36,80,136,257],[18,96,129,264],[20,160,258],[]],[(73,67,36278965296),(74,67,36278965251),(76,67,36278964291),(81,67,36278719536),(82,67,36278719491),(84,67,36278718531),(97,67,36273804336),(98,67,36273804291),(100,67,36273803331),(137,67,35020674096),(138,67,35020674051),(140,67,35020673091),(145,67,35020428336),(146,67,35020428291),(148,67,35020427331),(161,67,35015513136),(162,67,35015513091),(164,67,35015512131),(265,67,10861483056),(266,67,10861483011),(268,67,10861482051),(273,67,10861237296),(274,67,10861237251),(276,67,10861236291),(289,67,10856322096),(290,67,10856322051),(292,67,10856321091)]⟩,
⟨[7,56,449],[[56,449],[7,72,144,288],[36,66,136,272],[18,68,160,264],[12,34,80],[10,17,96,132],[9,130,260],[20,33,258],[]],[(74,70,36278965251),(76,70,36278964291),(82,70,36278719491),(84,70,36278718531),(98,70,36273804291),(100,70,36273803331),(138,70,35020674051),(140,70,35020673091),(146,70,35020428291),(148,70,35020427331),(162,70,35015513091),(164,70,35015512131),(266,70,10861483011),(268,70,10861482051),(274,70,10861237251),(276,70,10861236291),(290,70,10856322051),(292,70,10856321091)]⟩,
⟨[7,56,457],[[18,36,457],[7,80,288],[56,66,132],[33,68,130,272],[20,96,258],[12,34,144],[10,17,160,260],[],[]],[(82,72,36278719491),(84,72,36278718531),(98,72,36273804291),(100,72,36273803331),(146,72,35020428291),(148,72,35020427331),(162,72,35015513091),(164,72,35015512131),(274,72,10861237251),(276,72,10861236291),(290,72,10856322051),(292,72,10856321091)]⟩,
⟨[7,57,202],[[57,260],[20,202,288],[7,96,384],[12,65,160,272],[18,36,129,320],[34,68,144,257],[80,132,258],[264],[]],[(84,73,36312404001),(100,73,36309454881),(148,73,35557429281),(164,73,35554480161),(268,74,19451424801),(274,77,19451302401),(276,78,19451301921),(290,77,19448353281),(292,78,19448352801),(321,77,18849681936),(324,78,18849681426),(336,80,23696990736),(340,81,36344967696),(352,80,23693058576),(356,81,36343984656),(385,77,18094707216),(388,78,18094706706),(400,80,22690357776),(404,81,36093309456),(416,80,22686425616),(420,81,36092326416)]⟩,
⟨[7,57,449],[[57,66,260],[10,36,449],[7,72,144,288],[12,18,96],[20,34,136],[68,130,264],[80,132,258],[160,272],[]],[(74,74,36278965251),(76,74,36278964291),(82,74,36278719491),(84,74,36278718531),(98,74,36273804291),(100,74,36273803331),(138,74,35020674051),(140,74,35020673091),(146,74,35020428291),(148,74,35020427331),(162,74,35015513091),(164,74,35015512131),(266,74,10861483011),(268,74,10861482051),(274,74,10861237251),(276,74,10861236291),(290,74,10856322051),(292,74,10856321091)]⟩,
⟨[7,57,450],[[57,68],[7,72,144,288],[12,450],[10,20,160,257],[36,65,136,272],[34,80,132,264],[18,96,129,260],[],[]],[(76,75,36312526881),(84,75,36312404001),(100,75,36309454881),(140,75,35557552161),(148,75,35557429281),(164,75,35554480161),(268,75,19451424801),(276,75,19451301921),(292,75,19448352801)]⟩,
⟨[7,57,456],[[7,456],[57,66,260],[34,80,132,257],[20,96,130],[18,36,65],[68,144,258],[10,160,272],[12,129,288],[]],[(82,78,36278719491),(84,78,36278718531),(98,78,36273804291),(100,78,36273803331),(146,78,35020428291),(148,78,35020427331),(162,78,35015513091),(164,78,35015512131),(274,78,10861237251),(276,78,10861236291),(290,78,10856322051),(292,78,10856321091)]⟩,
⟨[7,57,458],[[20,458],[57,68],[7,160,272],[12,65,144,288],[36,80,257],[18,96,132],[34,129,260],[],[]],[(84,79,36312404001),(100,79,36309454881),(148,79,35557429281),(164,79,35554480161),(276,79,19451301921),(292,79,19448352801)]⟩,
⟨[15,113,402],[[15,160,320],[113,132,264],[36,72,402],[20,40,192,257],[24,68,129,288],[34,136,260],[66],[],[]],[(164,81,35015512131),(168,81,35015492931),(196,81,34921140291),(200,81,34921121091),(292,81,10856321091),(296,81,10856301891),(324,81,10761949251),(328,81,10761930051)]⟩,
⟨[7,25,42,52],[[7,72,144,288],[25,68,160,258],[42,65,384],[52,66,136,257],[12,18,33,192],[80,132,264],[96,129,260],[130,320],[272]],[(76,82,36344967696),(82,82,36344906016),(97,82,36342939906),(140,82,36093309456),(146,82,36093247776),(161,82,36091281666),(193,83,36344967696),(194,83,36343984641),(196,83,36343861281),(200,83,36343776561),(204,84,36344967696),(208,83,36343653201),(210,84,36344906016),(224,83,36339720981),(225,84,36342939906),(268,82,28040245776),(274,82,28040184096),(289,82,28038217986),(321,83,32318435856),(322,83,32317452801),(324,83,32317329441),(328,83,32317244721),(332,84,32318435856),(336,83,32317121361),(338,84,32318374176),(352,83,32313189141),(353,84,32316408066),(385,83,31815119376),(386,83,31814136321),(388,83,31814012961),(392,83,31813928241),(396,84,31815119376),(400,83,31813804881),(402,84,31815057696),(416,83,31809872661),(417,84,31813091586),(448,85,36344967696),(449,86,36344967696),(450,86,36343984641),(452,86,36343861281),(456,86,36343776561),(460,87,36344967696),(464,86,36343653201),(466,87,36344906016),(480,86,36339720981),(481,87,36342939906)]⟩,
⟨[7,25,42,76],[[7,48,136,320],[25,96,132,258],[42,65,144,260],[18,33,76,384],[36,192,272],[80,130,288],[20,66,160,257],[129,264],[]],[(52,82,36344967696),(82,82,36329238816),(97,82,36327272706),(112,88,36344967696),(146,89,36344967696),(148,89,36329238816),(161,89,36343984641),(164,89,36327272706),(176,90,36344967696),(180,91,36344967696),(193,89,36312526881),(194,89,36311543826),(208,90,36329238816),(210,91,36329238816),(224,90,36327272706),(225,91,36327272706),(240,92,36344967696),(274,89,32318435856),(276,89,32302706976),(289,89,32317452801),(292,89,32300740866),(304,90,32318435856),(308,91,32318435856),(321,89,32285995041),(322,89,32285011986),(336,90,32302706976),(338,91,32302706976),(352,90,32300740866),(353,91,32300740866),(368,92,32318435856),(385,93,36344967696),(386,93,36343984641),(388,93,36312526881),(392,94,36344967696),(400,95,36344967696),(402,96,36344967696),(404,96,36329238816),(416,95,36343984641),(417,96,36343984641),(420,96,36327272706),(432,97,36344967696),(436,98,36344967696),(448,95,36312526881),(449,96,36312526881),(450,96,36311543826),(464,97,36329238816),(466,98,36329238816),(480,97,36327272706)]++[(481,98,36327272706),(496,99,36344967696)]⟩,
⟨[7,25,42,84],[[42,84,129],[7,192,288],[25,160,320],[33,72,130,260],[18,96,132,257],[12,48,65,384],[36,66,136,272],[144,258],[264]],[(97,88,36341879811),(140,89,35825922336),(146,89,35810132496),(161,90,36090221571),(164,100,36344967696),(176,100,36344828976),(193,90,36011331651),(194,100,36329177376),(200,100,36329038656),(224,101,36344967696),(225,102,36344967696),(268,89,23746326816),(274,89,23730536976),(289,90,28037157891),(292,100,32318435856),(304,100,32318297136),(321,90,27958267971),(322,100,32302645536),(328,100,32302506816),(352,101,32318435856),(353,102,32318435856),(385,103,36344967696),(386,104,36344967696),(388,104,36329177376),(392,104,36344828976),(396,105,36344967696),(400,104,36329038656),(402,105,36329177376),(416,106,36344967696),(417,107,36344967696),(420,108,36344967696),(432,108,36344828976),(448,106,36329177376),(449,107,36329177376),(450,108,36329177376),(456,108,36329038656),(480,109,36344967696),(481,110,36344967696)]⟩
]
private def data9Part7 : Array E19Cert.Row := #[
⟨[7,25,42,116],[[116,136,258],[7,72,384],[25,66,160,260],[42,192,257],[12,33,130,320],[18,65,132,264],[129,272],[144,288],[]],[(140,91,36093309456),(146,91,36093170736),(161,91,36090221571),(193,111,36344967696),(194,111,36343984641),(200,111,36343776561),(268,91,28040245776),(274,91,28040107056),(289,91,28037157891),(321,111,32318435856),(322,111,32317452801),(328,111,32317244721),(385,112,36344967696),(386,112,36343984641),(388,113,36344967696),(392,112,36343776561),(396,114,36344967696),(400,113,36344828976),(402,114,36344828976),(416,113,36341879811),(417,114,36341879811),(448,115,36344967696),(449,116,36344967696),(450,116,36343984641),(456,116,36343776561)]⟩,
⟨[7,25,42,193],[[20,42,193],[7,48,72,384],[25,96,130,260],[12,80,288],[36,66,136,272],[33,68,144,264],[18,132,320],[160,258],[257]],[(52,83,36344967696),(76,89,36312526881),(82,89,36312196401),(84,90,36011331651),(100,100,36326228226),(112,100,36325885506),(116,111,36344967696),(140,89,35557552161),(146,89,35557221681),(148,90,35004698691),(164,100,35822911746),(176,100,35822569026),(180,111,36093309456),(268,93,28040245776),(274,93,28040107056),(276,103,28040245776),(289,94,28037157891),(292,104,28039262721),(304,104,28039054641),(308,112,28040245776),(322,117,36344967696),(324,118,36344967696),(328,117,36344828976),(332,119,36344967696),(336,118,36344828976),(338,119,36344828976),(340,120,36344967696),(352,121,36344967696),(356,122,36344967696),(368,122,36344828976),(372,123,36344967696),(386,117,36093309456),(388,118,36093309456),(392,117,36093170736),(396,119,36093309456),(400,118,36093170736),(402,119,36093170736),(404,120,36093309456),(416,121,36093309456),(420,122,36093309456),(432,122,36093170736),(436,123,36093309456)]⟩,
⟨[7,25,42,196],[[25,196,288],[7,48,136,320],[42,80,129,260],[20,66,160,257],[36,65,130,272],[12,18,96,384],[33,72,144,258],[264],[]],[(52,83,36343861281),(82,90,36329038896),(97,90,36324123651),(112,101,36343776561),(146,90,35825722416),(161,90,35820807171),(176,101,36092118321),(268,93,19451424801),(274,95,28040107056),(276,104,23746265376),(289,95,28037157891),(292,104,23743316226),(304,106,28039054641),(308,113,28040245776),(321,118,32318435856),(322,118,32317452801),(328,121,32317244721),(336,124,36344967696),(338,125,36344967696),(352,124,36343984641),(353,125,36343984641),(368,126,36344967696),(385,118,31815119376),(386,118,31814136321),(392,121,31813928241),(400,124,36093309456),(402,125,36093309456),(416,124,36092326401),(417,125,36092326401),(432,126,36093309456)]⟩,
⟨[7,25,42,204],[[18,204,288],[7,48,320],[25,96,130,260],[42,129,272],[80,160,257],[36,65,144,258],[20,33,66,384],[264],[]],[(52,84,36344967696),(82,91,36329038896),(97,91,36324123651),(112,102,36343776561),(146,91,35825722416),(161,91,35820807171),(176,102,36092118321),(274,96,28040107056),(276,105,28040245776),(289,96,28037157891),(292,105,28039262721),(304,107,28039054641),(308,114,28040245776),(321,119,32318435856),(322,119,32317452801),(336,125,32318297136),(338,127,36344967696),(352,125,32315347971),(353,127,36343984641),(368,128,36344967696),(385,119,31815119376),(386,119,31814136321),(400,125,31814980656),(402,127,36093309456),(416,125,31812031491),(417,127,36092326401),(432,128,36093309456)]⟩,
⟨[7,25,42,212],[[42,212,257],[7,96,384],[25,160,258],[12,65,130,288],[36,72,129,272],[33,66,264],[48,136,320],[18,260],[]],[(97,92,36341879811),(161,92,36090221571),(268,96,23746326816),(274,96,23746126896),(289,97,28037157891),(292,108,28039262721),(304,108,28039054641),(321,120,32318435856),(322,122,32317452801),(328,122,32317244721),(352,126,32315347971),(353,128,32315347971),(385,120,31815119376),(386,122,31814136321),(392,122,31813928241),(416,126,31812031491),(417,128,31812031491)]⟩,
⟨[7,25,42,244],[[244,264],[7,72,384],[25,258],[42,129,320],[12,66,257],[18,65,136,288],[33,130,260],[272],[]],[(268,98,28040245776),(274,98,28040107056),(289,98,28037157891),(321,123,32318435856),(322,123,32317452801),(328,123,32317244721),(385,123,31815119376),(386,123,31814136321),(392,123,31813928241)]⟩,
⟨[7,25,42,448],[[7,48,448],[25,68,160,258],[42,80,129,260],[12,96,144,257],[36,65,130,272],[20,33,66,136],[18,72,132,288],[264],[]],[(52,85,36344967696),(76,95,36312526881),(82,95,36312196401),(84,106,36329177376),(97,95,36306298131),(100,106,36326228226),(112,106,36325885506),(116,115,36344967696),(140,95,35557552161),(146,95,35557221681),(148,106,35825860896),(161,95,35551323411),(164,106,35822911746),(176,106,35822569026),(180,115,36093309456),(268,95,19451424801),(274,95,19451094321),(276,106,23746265376),(289,95,19445196051),(292,106,23743316226),(304,106,23742973506),(308,115,28040245776)]⟩,
⟨[7,25,42,449],[[20,42,449],[7,48,72],[25,36,130],[33,68,136,272],[18,96,132,264],[80,160,260],[12,66,144,288],[258],[]],[(52,86,36344967696),(76,96,36312526881),(82,96,36312196401),(84,107,36329177376),(100,108,36326228226),(112,108,36325885506),(116,116,36344967696),(140,96,35557552161),(146,96,35557221681),(148,107,35825860896),(164,108,35822911746),(176,108,35822569026),(180,116,36093309456),(268,96,19451424801),(274,96,19451094321),(276,107,23746265376),(292,108,23743316226),(304,108,23742973506),(308,116,28040245776)]⟩,
⟨[7,25,42,452],[[25,452],[7,48,72],[20,42,257],[36,80,129,258],[12,33,66,144],[96,130,272],[18,65,160,264],[136,288],[]],[(52,86,36343861281),(82,97,36329038896),(97,97,36324123651),(112,109,36343776561),(146,97,35825722416),(161,97,35820807171),(176,109,36092118321),(274,97,23746126896),(289,97,23741211651),(304,109,28039054641)]⟩,
⟨[7,25,42,460],[[18,33,460],[7,48],[25,66,160],[42,80,257],[65,144,288],[36,130,272],[20,96,129,258],[],[]],[(52,87,36344967696),(82,98,36329038896),(97,98,36324123651),(112,110,36343776561),(146,98,35825722416),(161,98,35820807171),(176,110,36092118321),(274,98,23746126896),(289,98,23741211651),(304,110,28039054641)]⟩,
⟨[7,25,42,468],[[33,468],[7,96,264],[25,130,288],[42,65],[48,72,129,258],[12,66,160,257],[18,36,136],[],[]],[(97,99,36341879811),(161,99,36090221571),(289,99,28037157891)]⟩,
⟨[7,25,42,500],[[500],[7,72],[25,258],[42,129],[12,66,257],[18,65,136],[33,130,264],[],[]],[]⟩,
⟨[7,25,97,170],[[20,170,257],[7,192,272],[25,132,320],[12,18,97,384],[48,72,129,260],[36,66,144,264],[68,258],[80,288],[]],[(52,91,36341633091),(76,91,36261208131),(82,91,36260824611),(84,92,36278718531),(148,111,35825860896),(196,111,35756925216),(208,111,35756517216),(212,129,36344967696),(268,119,23746326816),(274,119,23746126896),(276,120,23746265376),(292,119,23693058336),(304,119,23692650336),(308,130,36344967696),(322,119,23641678896),(324,120,23677329696),(328,119,23641470816),(332,130,36309455376),(336,120,23676921696),(338,130,36309177936),(340,131,36344967696),(385,132,36344967696),(388,133,36344967696),(400,133,36344828976),(404,134,36344967696),(448,133,36273804336),(452,134,36309455376),(464,134,36309177936),(468,135,36344967696)]⟩,
⟨[7,25,97,385],[[7,40,144,320],[25,34,132],[10,20,97],[12,18,385],[36,72,130,272],[48,66,136,260],[68,160,258],[192,288],[80,264]],[(42,94,36341879811),(44,94,36341878851),(50,94,36341634051),(52,94,36341633091),(74,94,36278965251),(76,94,36278964291),(82,94,36278719491),(84,94,36278718531),(138,94,26448565251),(140,94,26448564291),(146,94,26448319491),(148,94,26448318531),(162,94,26392163331),(164,94,26392162371),(168,94,26391873651),(170,132,36344967696),(172,132,36344967456),(176,94,26391627891),(178,132,36344906256),(180,132,36344906016),(194,94,26329248771),(196,94,26329247811),(200,94,26328959091),(202,132,36329239056),(204,132,36329238816),(208,94,26328713331),(210,132,36329177616),(212,132,36329177376),(266,94,10342437891),(268,94,10342436931),(274,94,10342192131),(276,94,10342191171),(290,94,10286035971),(292,94,10286035011),(296,94,10285746291),(298,132,32318435856),(300,132,32318435616),(304,94,10285500531),(306,132,32318374416),(308,132,32318374176),(322,94,10223121411),(324,94,10223120451),(328,94,10222831731),(330,132,32302707216),(332,132,32302706976),(336,94,10222585971),(338,132,32302645776),(340,132,32302645536)]⟩,
⟨[7,25,97,386],[[12,97,386],[7,48,192,264],[25,66,132,288],[40,80,129,260],[20,72,160,257],[10,36,144,320],[34,68,136,272],[18],[]],[(42,93,36341879811),(44,95,36341878851),(50,93,36341634051),(52,95,36341633091),(74,93,36278965251),(76,95,36278964291),(82,93,36278719491),(84,95,36278718531),(140,104,26985443361),(148,104,26985320481),(164,104,26931130401),(168,121,35772307296),(172,133,36344967456),(176,121,35772245856),(180,133,36344906016),(196,104,26899673121),(200,121,35756578656),(204,133,36329238816),(208,121,35756517216),(212,133,36329177376),(268,104,18932379681),(276,104,18932256801),(292,104,18878066721),(296,121,23692711776),(300,133,32318435616),(304,121,23692650336),(308,133,32318374176),(324,104,18846609441),(328,121,23676983136),(332,133,32302706976),(336,121,23676921696),(340,133,32302645536)]⟩,
⟨[7,25,97,394],[[20,97,394],[7,72,160,272],[25,36,192],[12,80,129,288],[34,68,144,257],[18,40,132,320],[48,66,260],[],[]],[(44,96,36341878851),(50,96,36341564691),(52,97,36341633091),(76,96,36278964291),(82,96,36278650131),(84,97,36278718531),(148,112,27253752096),(164,122,35772653856),(176,122,35772245856),(180,134,36344906016),(196,122,35756925216),(208,122,35756517216),(212,134,36329177376),(276,112,23227220256),(292,122,23693058336),(304,122,23692650336),(308,134,32318374176),(324,122,23677329696),(336,122,23676921696),(340,134,32302645536)]⟩,
⟨[7,25,97,426],[[20,426],[7,192,272],[25,132,320],[97,144,260],[12,80,129],[18,36,72,257],[48,68],[66],[]],[(52,98,36341633091),(76,98,36261208131),(82,98,36260824611),(84,99,36278718531),(148,123,35825860896),(196,123,35756925216),(208,123,35756517216),(212,135,36329177376),(276,123,23746265376),(324,123,23677329696),(336,123,23676921696),(340,135,32302645536)]⟩,
⟨[7,25,98,168],[[7,168,272],[25,192,260],[20,98,257],[12,33,144,320],[48,68,129,258],[18,72,132,288],[10,36,80,384],[65,130,264],[]],[(52,100,36341633091),(76,100,36261208116),(84,101,36312404001),(146,100,34750871076),(148,101,35557221201),(193,100,34631800386),(196,101,35436061461),(208,101,34429146981),(212,136,36344967696),(266,117,10861483011),(268,121,19199558481),(274,121,19451302401),(276,124,23746265376),(289,117,10822837296),(292,121,19093021461),(304,121,17834383461),(308,137,36344967696),(321,121,19383411216),(324,124,23677329666),(328,121,17768581206),(332,137,36309455361),(336,138,36344967696),(340,139,36344967696),(385,121,18124773216),(386,121,18020325126),(388,138,36093170736),(400,124,22418622306),(402,137,35554199121),(404,139,36093170736),(448,124,22297462566),(449,137,35467507221),(452,139,36005434371),(464,139,34998585171),(468,140,36344967696)]⟩,
⟨[7,25,98,172],[[18,172,320],[25,98,384],[7,192,272],[10,20,65,288],[80,129,260],[33,68,144,258],[48,72,130,257],[264],[]],[(84,102,36312404001),(146,111,35557429761),(193,111,35489538576),(208,136,36329177616),(266,119,19451425281),(274,122,19451302401),(276,125,23746265376),(289,119,19414868496),(304,137,32318374416),(321,122,19383411216),(324,125,23677329666),(328,137,32267194881),(336,139,32302645776),(340,141,36344967696),(385,133,27253813536),(386,133,27182788866),(400,142,36344967696),(402,143,36344967696),(448,142,36309455361),(449,143,36309455361),(464,144,36344967696)]⟩,
⟨[7,25,98,388],[[25,98,388],[7,40,192,272],[10,48,68,129],[12,18,160,320],[20,72,130,288],[33,80,136,258],[36,65,144,264],[257],[]],[(44,103,36343984161),(52,103,36343861281),(76,103,36312526881),(84,103,36312404001),(138,103,26985443841),(146,103,26985320961),(161,103,26931130896),(168,138,36093170736),(176,138,36093109296),(193,103,26899673616),(200,138,36061713456),(208,138,36061652016),(266,103,18932380161),(274,103,18932257281),(289,103,18878067216),(296,138,28040107056),(304,138,28040045616),(321,103,18846609936),(328,138,28008649776),(336,138,28008588336)]⟩,
⟨[7,25,98,392],[[20,98,392],[7,72,160,272],[25,36,192,258],[48,68,130,257],[18,65,132,288],[40,80,129,260],[12,33,144,320],[10],[]],[(44,104,36341878851),(52,106,36343861281),(76,104,36278964291),(84,106,36312404001),(146,104,26448250131),(148,106,26985112401),(161,118,34982028336),(164,124,35520995346),(176,124,22418560866),(180,142,36344906256),(193,118,34919113776),(196,124,35489538066),(208,124,22355646306),(212,142,36329177616),(274,104,10342122771),(276,106,18932048721),(289,118,10822837296),(292,124,19414867986),(304,124,14365497186),(308,142,32318374416),(321,118,10759922736),(324,124,19383410706),(336,124,14302582626),(340,142,32302645776)]⟩,
⟨[7,25,98,394],[[20,65,394],[25,36,192],[7,80,288],[12,98,129,272],[40,68,144,257],[18,33,132,320],[48,72,260],[160],[]],[(44,105,36343984161),(52,108,36343861281),(76,105,36312526881),(84,108,36312404001),(148,113,27253752096),(161,119,34982028336),(164,125,35520995346),(176,137,35554076241),(180,143,36344906256),(193,119,34919113776),(196,125,35489538066),(208,137,35491161681),(212,143,36329177616),(276,113,23227220256),(289,119,10822837296),(292,125,19414867986),(304,137,19447948881),(308,143,32318374416),(321,119,10759922736),(324,125,19383410706),(336,137,19385034321),(340,143,32302645776)]⟩,
⟨[7,25,98,396],[[18,65,396],[25,68,130,288],[7,48,192],[20,98,257],[40,80,129,258],[10,33,144,320],[72,160,272],[36],[]],[(52,107,36343861281),(84,107,36312404001),(146,112,26985320961),(161,120,35520995856),(176,139,36093109296),(193,120,35489538576),(208,139,36061652016),(274,112,18932257281),(289,120,19414868496),(304,139,28040045616),(321,120,19383411216),(336,139,28008588336)]⟩,
⟨[7,25,98,424],[[20,65,424],[25,98,132],[7,144,320],[10,36,192,272],[48,68,130,257],[12,80,129,258],[18,33,72,260],[],[]],[(52,108,36341633091),(76,108,36261208116),(84,109,36312404001),(146,122,35020428291),(148,126,35825860896),(193,122,34919113776),(196,126,35756925186),(208,139,34919696211),(212,144,36329177616),(274,122,10861237251),(276,126,23746265376),(321,122,10759922736),(324,126,23677329666),(336,139,10760505171),(340,144,32302645776)]⟩
]
private def data9Part8 : Array E19Cert.Row := #[
⟨[7,25,98,428],[[18,65,428],[25,98],[7,80],[20,72,129,258],[10,68,144,257],[33,192,272],[48,130,320],[],[]],[(84,110,36312404001),(146,123,35557429761),(193,123,35489538576),(208,140,36329177616),(274,123,19451302401),(321,123,19383411216),(336,140,32302645776)]⟩,
⟨[7,25,106,180],[[106,129,260],[65,180,264],[7,136,320],[25,68,384],[12,18,192,257],[33,130,272],[80,258],[288],[]],[(193,129,36061852176),(268,127,23746326816),(274,127,23494607376),(289,130,28040245776),(321,134,28008788496),(324,143,28008788256),(336,143,28008588336),(385,134,27253752096),(386,143,27253752336),(392,143,27253674816),(448,145,36344967696),(449,146,36344967696)]⟩,
⟨[7,25,106,396],[[106,144,257],[18,65,396],[7,48,320],[25,68,160,258],[36,80,129],[33,192,272],[20,130,288],[],[]],[(52,114,36344767296),(84,114,36329038656),(146,114,27253613616),(161,130,35554480656),(176,141,36093109296),(193,130,35491566096),(208,141,36061652016),(274,114,23227081776),(289,130,19448353296),(304,141,28040045616),(321,130,19385438736),(336,141,28008588336)]⟩,
⟨[7,25,106,404],[[106,129],[7,160,320],[25,192,288],[33,404],[18,36,65,264],[12,80,130,257],[48,68,136,258],[],[]],[(161,131,36093309456),(193,131,36061852176),(289,131,28040245776),(321,131,28008788496)]⟩,
⟨[7,25,106,416],[[20,106,257],[25,68,416],[7,192,272],[12,18,129,320],[33,80,130,260],[36,65,144,258],[48,132,264],[136],[]],[(52,113,36341633091),(84,115,36329177376),(140,125,30742483011),(146,125,30742168851),(148,126,30742237251),(193,133,34921141296),(196,142,35491565601),(208,142,35491161681),(212,145,36329239056),(268,125,10609823811),(274,125,10609509651),(276,126,10609578051),(321,133,10761950256),(324,142,19385438241),(336,142,19385034321),(340,145,32302707216)]⟩,
⟨[7,25,106,417],[[20,106],[18,68,417],[7,80,136],[25,132,320],[12,65,130,272],[48,192,260],[36,144,264],[258],[]],[(52,114,36341633091),(84,116,36329177376),(140,127,35557552161),(146,127,35557221681),(148,128,30742237251),(196,143,35491565601),(208,143,35491161681),(212,146,36329239056),(268,127,19451424801),(274,127,19451094321),(276,128,10609578051),(324,143,19385438241),(336,143,19385034321),(340,146,32302707216)]⟩,
⟨[7,25,106,420],[[25,420],[20,106,129],[7,80,264],[33,68,144,258],[12,65,130,272],[18,192,257],[48,136,320],[],[]],[(84,116,36312404001),(146,128,35825722416),(193,134,35491566096),(208,144,36061652016),(274,128,23746126896),(321,134,19385438736),(336,144,28008588336)]⟩,
⟨[7,25,106,436],[[65,436],[106,129],[7,136,320],[25,68,258],[12,18,192,257],[33,80,130,264],[],[],[]],[(193,135,36061852176),(321,135,28008788496)]⟩,
⟨[7,56,201,338],[[36,201],[33,132,338],[7,56,384],[17,68,160,264],[12,130,288],[10,96,144,260],[20,34,257],[],[]],[(100,141,36273803331),(148,143,35020427331),(162,143,35014325781),(164,144,35015512131),(268,143,10861482036),(289,143,10855073361),(292,144,10856259636),(388,145,18077933601),(416,145,18069198966),(420,147,36344967696)]⟩,
⟨[7,57,202,340],[[57,132,258],[36,202,257],[160,340],[7,96,144,264],[12,18,129,288],[34,65,384],[],[],[]],[(164,146,35554480161),(290,146,19448291841),(385,146,18077934096),(416,147,22686425616)]⟩,
⟨[7,25,42,52,76],[[7,96,144,264],[25,66,160,260],[42,129,320],[52,192,257],[18,33,76,384],[65,132,258],[80,130,288],[136,272],[]],[(82,148,36344967696),(97,148,36343984641),(146,149,36344967696),(161,149,36343984641),(193,150,36344967696),(194,150,36343984641),(208,150,36340511316),(210,151,36344967696),(224,150,36339528261),(225,151,36343984641),(274,149,32318435856),(289,149,32317452801),(321,150,32318435856),(322,150,32317452801),(336,150,32313979476),(338,151,32318435856),(352,150,32312996421),(353,151,32317452801),(385,152,36344967696),(386,152,36343984641),(388,153,36344967696),(392,153,36344767296),(400,152,36340511316),(402,154,36344967696),(416,152,36339528261),(417,154,36343984641),(448,155,36344967696),(449,156,36344967696),(450,156,36343984641),(464,156,36340511316),(466,157,36344967696),(480,156,36339528261),(481,157,36343984641)]⟩,
⟨[7,25,42,52,193],[[42,193,260],[7,96,144,264],[25,66,132,288],[52,72,130,257],[12,18,33,320],[80,384],[68,160,258],[136,272],[]],[(76,150,36344967696),(82,150,36344906016),(140,150,36093309456),(146,150,36093247776),(268,152,28040245776),(274,152,28040184096),(289,153,28038217986),(322,158,36344967696),(324,158,36344906016),(328,158,36344828976),(332,159,36344967696),(336,158,36344767296),(338,159,36344906016),(352,160,36344967696),(386,158,36093309456),(388,158,36093247776),(392,158,36093170736),(396,159,36093309456),(400,158,36093109056),(402,159,36093247776),(416,160,36093309456)]⟩,
⟨[7,25,42,52,204],[[18,33,204],[7,160,272],[25,130,288],[42,80,257],[52,65,258],[66,129,260],[144,320],[96,384],[264]],[(82,151,36344906016),(97,151,36342939906),(146,151,36093247776),(161,151,36091281666),(274,154,28040184096),(289,154,28038217986),(321,159,32318435856),(322,159,32317452801),(336,159,32313979476),(338,161,36344967696),(352,159,32312996421),(353,161,36343984641),(385,159,31815119376),(386,159,31814136321),(400,159,31810662996),(402,161,36093309456),(416,159,31809679941),(417,161,36092326401)]⟩,
⟨[7,25,42,52,448],[[7,448],[52,65,136,258],[25,66,160,260],[42,68,129,272],[18,72,132,257],[12,80,130,288],[96,144,264],[33],[]],[(76,155,36344967696),(82,155,36344906016),(97,155,36342939906),(140,155,36093309456),(146,155,36093247776),(161,155,36091281666),(268,155,28040245776),(274,155,28040184096),(289,155,28038217986)]⟩,
⟨[7,25,42,52,449],[[42,449],[7,96,144,264],[25,68,160,258],[12,18,33],[52,66,136],[72,132,272],[80,130,260],[288],[]],[(76,156,36344967696),(82,156,36344906016),(140,156,36093309456),(146,156,36093247776),(268,156,28040245776),(274,156,28040184096)]⟩,
⟨[7,25,42,52,460],[[18,33,460],[7,80,288],[25,96,258],[42,65,144],[52,66,129],[130,257],[160,272],[],[]],[(82,157,36344906016),(97,157,36342939906),(146,157,36093247776),(161,157,36091281666),(274,157,28040184096),(289,157,28038217986)]⟩,
⟨[7,25,42,76,112],[[7,112,136],[25,66,160,260],[42,144,257],[18,33,76,384],[36,65,130,264],[20,129,320],[132,258],[192,272],[288]],[(146,162,36344967696),(148,162,36329238816),(161,162,36343984641),(164,162,36327272706),(193,162,36312526881),(194,162,36311543826),(274,162,32318435856),(276,162,32302706976),(289,162,32317452801),(292,162,32300740866),(321,162,32285995041),(322,162,32285011986),(385,163,36344967696),(386,163,36343984641),(388,163,36312526881),(392,164,36344967696),(400,163,36273403476),(402,165,36344967696),(404,165,36329238816),(416,163,36272420421),(417,165,36343984641),(420,165,36327272706),(448,163,36240962661),(449,165,36312526881),(450,165,36311543826)]⟩,
⟨[7,25,42,76,146],[[33,76,146],[7,48,136,320],[25,66,132,288],[20,42,192,257],[65,160,272],[96,129,260],[36,80,384],[258],[264]],[(52,149,36344967696),(97,150,36327272706),(112,162,36344967696),(161,150,35823617586),(164,162,35014459701),(193,162,35004630291),(224,166,36344967696),(225,167,36344967696),(276,168,36344967696),(289,169,36344967696),(292,170,36344967696),(304,170,36093170736),(308,171,36344967696),(321,170,32285995041),(322,172,36344967696),(336,173,36344967696),(352,174,36344967696),(353,175,36344967696),(368,176,36344967696),(385,170,31279031601),(388,173,36093170736),(392,172,36093170736),(416,174,36093170736),(417,175,36093170736),(420,176,36093170736),(448,177,36344967696),(449,178,36344967696),(480,179,36344967696),(481,180,36344967696)]⟩,
⟨[7,25,42,76,176],[[7,176,320],[25,96,130,260],[20,42,192,257],[18,33,76,384],[36,65,136,258],[66,132,272],[80,129,288],[264],[]],[(82,150,36261868836),(97,150,36255970626),(193,166,36312526881),(194,166,36311543826),(274,170,28040107056),(276,173,32302706976),(289,170,28037157891),(292,173,32300740866),(321,174,32285995041),(322,174,32285011986),(336,181,36344967696),(338,182,36344967696),(352,181,36343984641),(353,182,36343984641),(385,183,36344967696),(386,183,36343984641),(388,184,36344967696),(392,185,36344967696),(448,186,36344967696),(449,187,36344967696),(450,187,36343984641)]⟩,
⟨[7,25,42,76,180],[[65,180,258],[7,192,288],[25,130,320],[42,80,257],[18,33,76,384],[66,129,264],[96,136,272],[260],[]],[(82,151,36329238816),(97,151,36327272706),(193,167,36312526881),(194,167,36311543826),(274,171,32318435856),(289,171,32317452801),(321,175,32285995041),(322,175,32285011986),(336,182,32302706976),(338,188,36344967696),(352,182,32300740866),(353,188,36343984641),(385,189,36344967696),(386,189,36343984641),(392,190,36344967696),(448,191,36344967696),(449,192,36344967696),(450,192,36343984641)]⟩,
⟨[7,25,42,76,240],[[7,240,264],[25,132,258],[42,129,260],[18,33,76,384],[20,66,136,257],[65,130,288],[36,272],[320],[]],[(274,176,32318435856),(276,176,32302706976),(289,176,32317452801),(292,176,32300740866),(321,176,32285995041),(322,176,32285011986),(385,193,36344967696),(386,193,36343984641),(388,193,36312526881),(392,194,36344967696)]⟩,
⟨[7,25,42,76,385],[[42,80,385],[7,96,136,272],[25,66,160,260],[33,76,144,258],[48,65,132,264],[20,192,288],[18,36,320],[130],[]],[(52,152,36344967696),(82,152,36329238816),(97,153,36327272706),(112,163,36344967696),(146,170,31279031601),(148,170,31247573841),(164,173,36056797956),(176,183,36344967696),(180,189,36344967696),(194,173,36009611316),(208,183,36329238816),(210,189,36329238816),(224,184,36327272706),(240,193,36344967696),(274,170,19199436081),(276,170,19167978321),(292,173,28003734276),(304,183,32318435856),(308,189,32318435856),(322,173,27956547636),(336,183,32302706976),(338,189,32302706976),(352,184,32300740866),(368,193,32318435856)]⟩,
⟨[7,25,42,76,392],[[7,48,392],[25,36,192,258],[42,80,132,257],[18,76,129,288],[33,144,320],[96,130,272],[20,65,160],[66,260],[]],[(52,153,36344767296),(82,153,36329038896),(97,153,36324123651),(112,164,36344967696),(146,172,36093170736),(148,172,36061713216),(161,172,36090221571),(164,172,36056797956),(176,185,36344967696),(180,190,36344967696),(193,172,36011577411),(194,172,36009611316),(208,185,36329238816),(210,190,36329238816),(224,185,36327272706),(225,190,36327272706),(240,194,36344967696),(274,172,28040107056),(276,172,28008649536),(289,172,28037157891),(292,172,28003734276),(304,185,32318435856),(308,190,32318435856),(321,172,27958513731),(322,172,27956547636),(336,185,32302706976),(338,190,32302706976),(352,185,32300740866),(353,190,32300740866),(368,194,32318435856)]⟩,
⟨[7,25,42,76,400],[[7,96,400],[25,36,130,320],[48,76,129,258],[42,80,132,257],[18,33,192,260],[20,65,160,264],[66,136,288],[],[]],[(52,152,36340511316),(82,152,36261868836),(97,155,36327272706),(112,163,36273403476),(161,174,36090221571),(164,177,36327272706),(193,174,36011577411),(194,177,36311543826),(224,186,36327272706),(225,191,36327272706),(289,174,28037157891),(292,177,32300740866),(321,174,27958513731),(322,177,32285011986),(352,186,32300740866),(353,191,32300740866)]⟩
]
private def data9Part9 : Array E19Cert.Row := #[
⟨[7,25,42,76,402],[[33,76,402],[7,96,264],[25,36,192],[42,80,129,260],[20,160,320],[65,132,288],[48,66,136,257],[],[]],[(52,154,36344967696),(97,156,36327272706),(112,165,36344967696),(161,175,36090221571),(164,178,36327272706),(193,176,36011577411),(224,187,36327272706),(225,192,36327272706),(289,175,28037157891),(292,178,32300740866),(321,176,27958513731),(352,187,32300740866),(353,192,32300740866)]⟩,
⟨[7,25,42,76,432],[[7,432],[25,36,130,320],[20,42,192,257],[18,76,129],[65,136,258],[33,66,132,264],[80,260],[96],[]],[(82,156,36261868836),(97,156,36255970626),(193,179,36312526881),(194,179,36311543826),(321,179,32285995041),(322,179,32285011986)]⟩,
⟨[7,25,42,76,436],[[66,436],[7,192,264],[25,130,320],[42,65],[18,76,129],[33,80,136,258],[96,257],[],[]],[(82,157,36329238816),(97,157,36327272706),(193,180,36312526881),(194,180,36311543826),(321,180,32285995041),(322,180,32285011986)]⟩,
⟨[7,25,42,76,496],[[7,496],[25,132,258],[42,129,260],[76,130,257],[18,36,65,136],[20,33,66,264],[],[],[]],[]⟩,
⟨[7,25,42,84,164],[[25,192,258],[42,84,384],[7,48,136,320],[18,65,164,264],[12,66,129,288],[33,72,130,272],[96,144,257],[260],[]],[(97,162,36243136851),(146,162,34479563061),(193,166,34903192401),(194,166,34397909781),(200,195,36344967696),(268,172,23746326816),(274,173,23746126896),(289,173,23489553411),(304,196,36344967696),(321,183,27958267971),(322,197,36344967696),(328,198,36344967696),(352,199,36344967696),(353,200,36344967696),(385,197,36092326401),(386,183,26442420276),(392,198,36092326401),(400,199,36092326401),(402,200,36092326401),(448,201,36344967696),(449,202,36344967696),(450,202,36092326401),(456,203,36344967696)]⟩,
⟨[7,25,42,84,224],[[7,224,264],[42,84,384],[25,66,132,288],[18,33,136,260],[36,65,144,258],[12,48,129,320],[72,130,272],[257],[]],[(140,166,35825922336),(146,166,35810132496),(268,177,23746326816),(274,177,23730536976),(289,184,28037157891),(292,199,32318435856),(304,199,32318297136),(321,184,27958267971),(322,199,32302645536),(328,199,32302506816),(385,204,36344967696),(386,205,36344967696),(388,205,36329177376),(392,205,36344828976),(396,206,36344967696),(400,205,36329038656),(402,206,36329177376)]⟩,
⟨[7,25,42,84,225],[[12,225,258],[42,84,384],[7,72,144,288],[25,130,260],[48,66,132,264],[18,36,136,320],[272],[257],[]],[(140,167,35825922336),(146,167,35810132496),(268,178,23746326816),(274,178,23730536976),(292,200,32318435856),(304,200,32318297136),(322,200,32302645536),(328,200,32302506816),(386,207,36344967696),(388,207,36329177376),(392,207,36344828976),(396,208,36344967696),(400,207,36329038656),(402,208,36329177376)]⟩,
⟨[7,25,42,84,385],[[42,84,385],[7,136,288],[25,36,192,258],[12,18,160,320],[96,132,264],[48,72,130,260],[33,66,144],[65,272],[]],[(97,164,36341879811),(140,169,35825922336),(146,169,35810132496),(164,197,36092326401),(176,197,36092118321),(194,197,36045017121),(200,197,36044809041),(224,204,36344967696),(268,169,23746326816),(274,169,23730536976),(292,197,28039262721),(304,197,28039054641),(322,197,27991953441),(328,197,27991745361),(352,204,32318435856)]⟩,
⟨[7,25,42,84,386],[[33,84,386],[25,192,260],[7,48,136,320],[42,65,132,272],[36,66,129,264],[18,72,160,257],[12,96,144],[288],[]],[(97,163,36341879811),(140,170,35825922336),(161,174,31273133331),(164,183,26442420276),(176,198,31542412836),(193,181,36011331651),(200,199,36044809041),(224,205,36344967696),(225,207,36344967696),(268,170,23746326816),(289,174,19193537811),(292,183,10336292916),(304,198,23489349156),(321,181,27958267971),(328,199,27991745361),(352,205,32318435856),(353,207,32318435856)]⟩,
⟨[7,25,42,84,396],[[33,66,396],[42,84,129],[7,48,320],[25,192,288],[36,65,130,272],[18,96,257],[72,160,258],[144],[]],[(97,165,36278649171),(146,171,35810132496),(161,182,36090221571),(176,200,36092118321),(193,182,36011262291),(194,200,36045017121),(224,206,36344967696),(225,208,36344967696),(274,171,23730536976),(289,182,28037157891),(304,200,28039054641),(321,182,27958198611),(322,200,27991953441),(352,206,32318435856),(353,208,32318435856)]⟩,
⟨[7,25,42,84,416],[[84,416],[42,65,132,272],[7,96,144,264],[18,33,192,260],[25,36,130,320],[48,72,129,258],[66,136,257],[12],[]],[(97,163,36306298131),(140,174,35825922336),(146,174,35825722416),(193,186,36011331651),(194,201,36329177376),(200,201,36329038656),(268,174,23746326816),(274,174,23746126896),(321,186,27958267971),(322,201,32302645536),(328,201,32302506816)]⟩,
⟨[7,25,42,84,417],[[12,66,417],[42,84],[7,72,144],[25,192,260],[48,65,130,264],[18,36,136,320],[96,132,258],[272],[]],[(140,175,35825922336),(146,175,35825722416),(194,202,36329177376),(200,202,36329038656),(268,175,23746326816),(274,175,23746126896),(322,202,32302645536),(328,202,32302506816)]⟩,
⟨[7,25,42,84,420],[[25,66,420],[42,84,129],[7,72,144],[12,65,130,272],[48,192,258],[18,96,136,257],[33,320],[264],[]],[(97,165,36243136851),(146,176,35825722416),(193,187,36011331651),(194,202,36045017121),(200,203,36329038656),(274,176,23746126896),(321,187,27958267971),(322,202,27991953441),(328,203,32302506816)]⟩,
⟨[7,25,42,84,480],[[7,480],[42,84,129],[25,130,260],[36,65,136,272],[18,33,132,264],[12,66,144,257],[48,72,258],[],[]],[(140,179,35825922336),(146,179,35810132496),(268,179,23746326816),(274,179,23730536976)]⟩,
⟨[7,25,42,84,481],[[12,18,481],[42,84],[7,136,272],[25,130,260],[48,72,132,258],[36,66,144,264],[],[],[]],[(140,180,35825922336),(146,180,35810132496),(268,180,23746326816),(274,180,23730536976)]⟩,
⟨[7,25,42,116,193],[[116,136,258],[42,193,260],[7,144,264],[25,66,132,288],[12,18,33,384],[72,130,257],[160,320],[272],[]],[(140,167,35557552161),(146,167,35557221681),(268,189,28040245776),(274,189,28040107056),(289,190,28037157891),(322,209,36344967696),(328,209,36344828976),(386,210,36344967696),(388,211,36344967696),(392,210,36344828976),(396,212,36344967696),(400,211,36344828976),(402,212,36344828976),(416,213,36344967696)]⟩,
⟨[7,25,42,116,385],[[116,136,258],[42,385],[7,72,144,288],[25,192,260],[12,33,130,320],[66,132,264],[18,65,160],[272],[]],[(140,175,31279362081),(146,175,31279031601),(194,210,36343984641),(200,210,36343776561),(268,175,19199766561),(274,175,19199436081),(322,210,32317452801),(328,210,32317244721)]⟩,
⟨[7,25,42,116,388],[[116,136,258],[25,66,388],[7,72,144,288],[12,130,257],[42,129,320],[18,33,192,264],[65,160,272],[],[]],[(146,182,31547532336),(161,182,31542617091),(193,211,36344967696),(194,211,36343984641),(200,213,36343776561),(274,182,23494468656),(289,182,23489553411),(321,211,32318435856),(322,211,32317452801),(328,213,32317244721)]⟩,
⟨[7,25,42,116,396],[[116,130,257],[18,65,396],[7,192,272],[25,66,160],[42,129,320],[33,72,144,258],[288],[],[]],[(146,188,36093170736),(161,188,36090221571),(193,212,36344967696),(194,212,36343984641),(274,188,28040107056),(289,188,28037157891),(321,212,32318435856),(322,212,32317452801)]⟩,
⟨[7,25,42,116,448],[[116,129,258],[42,448],[25,66,132,288],[7,144,264],[12,18,160,257],[33,72,130,260],[65,136,272],[],[]],[(140,191,36093309456),(146,191,36093170736),(161,191,36090221571),(268,191,28040245776),(274,191,28040107056),(289,191,28037157891)]⟩,
⟨[7,25,42,116,449],[[42,449],[116,130,264],[7,72,160,272],[25,132,258],[12,18,33],[66,144,260],[136,288],[],[]],[(140,192,36093309456),(146,192,36093170736),(268,192,28040245776),(274,192,28040107056)]⟩,
⟨[7,25,42,193,322],[[25,36,322],[20,42,193],[7,48,72,384],[12,144,288],[96,132,272],[18,33,136,260],[68,160,264],[80,130,257],[]],[(52,158,36344967696),(76,168,36312526881),(84,173,31432269891),(100,173,23373307956),(112,196,36325885506),(116,209,36344967696),(140,173,35004944451),(146,172,35004630291),(148,181,35004698691),(164,197,30958706721),(176,199,35537295186),(180,210,36093309456),(268,173,10843787316),(276,197,19435573281),(289,172,10838558001),(292,181,10839609396),(304,199,19428218661),(308,210,28039262721),(388,158,22607782416),(392,196,13162206786),(396,209,22607782416),(400,199,12910356306),(404,210,22607720976),(416,199,826828581),(420,210,18579223041),(432,214,36344967696),(436,215,36344967696)]⟩,
⟨[7,25,42,193,324],[[42,144,324],[25,160,258],[7,48,72,384],[12,18,193,288],[36,66,136,272],[20,96,130,257],[33,80,132,264],[],[]],[(52,158,36344906016),(82,170,36011263251),(112,199,36325885506),(140,170,30140670291),(146,174,35004630291),(148,174,30140424531),(164,183,26077590336),(176,201,35822569026),(180,211,36093309456),(274,183,23746126896),(289,185,23741211651),(304,205,28039054641),(386,158,22356124176),(392,199,13162206306),(400,201,13162083426),(402,211,22607720736),(416,205,17723585361),(432,216,36344967696)]⟩,
⟨[7,25,42,193,332],[[18,33,332],[42,193,272],[7,144,288],[25,160,258],[48,66,132,257],[20,96,384],[36,80,130],[136],[]],[(52,159,36344967696),(82,171,36312196401),(112,200,36325885506),(146,176,35004630291),(148,182,35004629331),(164,200,35537768466),(176,202,35822569026),(180,212,36093309456),(274,189,23746126896),(289,190,23741211651),(304,207,28039054641),(386,209,22356124176),(400,211,22355715696),(402,217,36344967696),(416,218,36344967696),(432,219,36344967696)]⟩
]
private def data9Part10 : Array E19Cert.Row := #[
⟨[7,25,42,193,340],[[33,136,340],[42,193],[7,72,144,288],[25,160,258],[12,48,130,257],[36,66,384],[18,96,132,264],[],[]],[(140,175,35004944451),(146,175,35004630291),(164,202,35537768466),(176,202,35537295186),(289,194,28037157891),(386,210,22356062736),(392,210,22355777136),(416,220,36344967696)]⟩,
⟨[7,25,42,193,352],[[7,144,352],[20,42,193],[25,36,66,384],[48,72,132,258],[12,18,160,257],[33,68,136,272],[80,130,260],[264],[]],[(52,160,36344967696),(76,173,36312526881),(82,173,36312196401),(84,184,36011331651),(140,177,35557552161),(146,177,35557221681),(148,186,35004698691),(164,198,35537768466),(176,198,35537295186),(180,213,36093309456),(268,184,23744360706),(274,184,23744022066),(276,204,28040245776),(386,199,323512101),(388,205,17220268881),(392,199,323430501),(396,218,36093309456),(400,205,17219934321),(402,218,36093170736),(404,220,36093309456)]⟩,
⟨[7,25,42,193,356],[[18,136,356],[42,193,272],[7,48,72,384],[12,33,144,258],[25,66,132],[80,130,264],[20,160,257],[],[]],[(82,176,36312196401),(140,178,35557552161),(146,179,35557221681),(148,187,35004698691),(176,203,35822569026),(274,193,28040107056),(386,210,18075906561),(392,214,36093170736),(400,216,36093170736),(402,219,36093170736)]⟩,
⟨[7,25,42,193,372],[[136,372],[42,193],[7,144,264],[25,132,258],[12,130,257],[18,33,72,384],[66,160],[],[]],[(140,180,35557552161),(146,180,35557221681),(386,215,36093309456),(392,215,36093170736)]⟩,
⟨[7,25,42,196,336],[[42,129,336],[7,160,264],[25,36,66,384],[33,196,258],[20,65,130,288],[48,136,257],[96,144,260],[12,18],[72]],[(52,158,36341633091),(97,181,36306298131),(146,183,35557221681),(161,186,35820807171),(176,205,35822569026),(268,183,19451424801),(289,186,23741072931),(292,205,23743316226),(385,201,4354045026),(386,205,8665854741),(392,205,612570741),(416,221,36344967696),(417,222,36344967696)]⟩,
⟨[7,25,42,196,338],[[36,129,338],[25,196,288],[7,160,264],[42,65,144,260],[20,33,136],[12,96,130,257],[48,72,384],[],[]],[(52,159,36343861281),(97,182,36306298131),(161,187,35820807171),(176,206,35820602916),(268,189,19451424801),(289,191,23741072931),(292,207,23743316226),(385,211,18077872416),(392,218,27787396401),(416,222,36092326401),(417,223,36344967696)]⟩,
⟨[7,25,42,196,368],[[12,129,368],[42,196,257],[25,36,66,384],[7,144,264],[18,65,160,260],[20,33,72,130],[136,258],[],[]],[(146,187,35557221681),(161,187,35551323411),(268,193,19451424801),(385,216,31815119376),(386,216,31814136321),(392,220,27787396401)]⟩,
⟨[7,25,42,204,338],[[48,204,257],[33,338],[7,144,288],[25,160,260],[20,42,65,384],[36,129,264],[96,130],[],[]],[(52,161,36344967696),(97,188,36306298131),(161,192,35820807171),(176,208,35820602916),(289,192,23741072931),(292,208,28039262721),(385,217,31815119376),(416,223,31812031491),(417,224,36344967696)]⟩,
⟨[7,25,42,204,368],[[7,368],[18,204,257],[25,160,258],[42,129,260],[20,33,130,264],[36,65,384],[66,144],[],[]],[(146,192,35557221681),(161,192,35551323411),(385,219,31815119376),(386,219,31814136321)]⟩,
⟨[7,25,97,170,212],[[170,257],[212,288],[7,48,264],[25,66,260],[12,97,258],[36,72,129,272],[18,320],[384],[]],[(268,217,23746326816),(274,217,23730536976),(292,217,23693058336),(304,217,23692650336),(322,217,23677268496),(328,217,23676982896),(385,225,36344967696)]⟩,
⟨[7,25,97,170,308],[[68,170,257],[66,129,308],[7,192,264],[25,132,320],[12,97,144,258],[18,72,384],[80],[],[]],[(76,188,36243382611),(82,188,32216605971),(196,212,35721274176),(208,212,35721004896),(322,212,23641617456),(328,212,23641470576),(385,225,27253813776),(448,226,36344967696)]⟩,
⟨[7,25,97,170,340],[[170,257],[7,48,72,384],[25,66,132,288],[12,97,144,258],[129,340],[18,36,192,264],[],[],[]],[(385,227,36344967696)]⟩,
⟨[7,25,97,170,385],[[80,170,260],[7,48,192,264],[25,132,320],[12,97,272],[20,66,385],[18,68,288],[36,72,144,258],[],[]],[(52,190,36341633091),(76,190,36261208131),(82,190,36260824611),(84,194,36278718531),(148,190,26448318531),(196,190,26329247811),(208,190,26328713331),(212,225,36344967696),(268,190,5779103811),(274,190,5778720291),(276,194,10342191171),(292,190,5740458051),(304,190,5739923571),(308,225,27253813776),(322,190,5641893411),(324,194,10223120451),(328,190,5641742451),(332,225,27182789136),(336,194,10222585971),(338,225,27182372976),(340,227,36344967696)]⟩,
⟨[7,25,97,170,388],[[80,170,257],[18,97,388],[7,72,272],[25,68,258],[48,66,129,264],[12,144,320],[20,192,288],[36],[]],[(52,189,36341633091),(76,189,36261208131),(82,191,36260824611),(84,193,36278718531),(208,213,35756517216),(274,207,18932257281),(304,218,23692650336),(322,207,18846609921),(328,218,23641470816),(336,220,23676921696),(338,226,36309177936)]⟩,
⟨[7,25,97,170,404],[[72,404],[68,170,257],[7,80,264],[25,36,320],[12,97,258],[48,66,129],[18,192,288],[],[]],[(76,192,36261208131),(82,192,36260824611),(322,219,23641678896),(328,219,23641470816)]⟩,
⟨[7,25,97,170,468],[[468],[170,257],[7,48,264],[25,66,288],[12,97,258],[18,36,72,129],[],[],[]],[]⟩,
⟨[7,25,98,168,212],[[33,212,264],[7,168,272],[25,98,384],[12,48,65,258],[18,36,72,257],[10,129,288],[130,260],[320],[]],[(266,214,10861483011),(268,218,18932171601),(274,218,19435573761),(289,214,10822837296),(292,218,18824590101),(304,218,17817606261),(321,218,19383349776),(328,218,17768515671),(385,218,18124772976),(386,218,18020324871)]⟩,
⟨[7,25,98,168,308],[[65,130,308],[7,80,168],[25,98,384],[10,192,257],[33,72,132,258],[18,68,129,264],[12,144,320],[],[]],[(76,200,36261208116),(146,200,34750871076),(193,203,34631800386),(196,206,34631799366),(208,206,34379810646),(266,209,10861483011),(321,213,19383349776),(328,218,9683994711),(385,213,18124772976),(386,218,8929170951),(448,222,22297462566),(449,228,36344967696)]⟩,
⟨[7,25,98,168,336],[[7,168,336],[25,98,132],[12,33,192,258],[20,65,130,264],[18,72,129,260],[10,36,384],[68,144,288],[48,257],[]],[(52,197,36341633091),(76,197,32252432451),(146,197,30151952406),(148,204,35557221201),(193,197,30102861921),(196,204,35436061461),(266,197,1934895126),(268,204,19435488081),(289,197,1948473441),(292,204,19361329941),(385,204,18091219056),(386,204,18020194311),(388,229,36344967696)]⟩,
⟨[7,25,98,168,340],[[10,129,340],[7,72,144,288],[25,98,384],[18,168,257],[48,65,132,258],[33,130,264],[12,192],[36],[]],[(146,202,34750871076),(193,202,34631800386),(266,210,10845754371),(289,210,10822775856),(385,220,18124772976),(386,220,18020324871)]⟩,
⟨[7,25,98,168,468],[[10,33,468],[7,168],[25,98],[12,48,130,257],[36,65,258],[18,129,264],[72,288],[],[]],[(266,215,10861483011),(289,215,10822837296)]⟩,
⟨[7,25,98,172,340],[[65,172,258],[10,129,340],[25,98,384],[7,72,144,288],[48,130,257],[18,33,192,264],[],[],[]],[(146,212,35557429761),(193,212,35489538576),(266,212,19435696641),(289,212,19414807056),(385,226,18126869856),(386,226,18020332806)]⟩,
⟨[7,25,98,172,400],[[65,172,258],[98,400],[7,48,320],[25,68,130,288],[80,129,264],[18,72,257],[10,33,192,260],[20],[]],[(84,207,36278718531),(193,211,34919113776),(266,207,10342368531),(289,211,5773674096),(321,216,10759861296),(324,222,19383349266),(328,222,14302644066)]⟩,
⟨[7,25,98,172,402],[[80,172,257],[33,68,402],[25,98,260],[7,48,192,264],[10,20,65,288],[129,320],[72],[],[]],[(84,208,36312404001),(193,212,34919113776),(289,217,19414868496),(321,219,10759861296),(324,223,23677329666),(328,228,32267194881)]⟩
]
private def data9Part11 : Array E19Cert.Row := #[
⟨[7,25,98,172,464],[[10,33,464],[65,172,258],[25,98,260],[7,48,264],[20,72,130,257],[18,68,129,288],[],[],[]],[(266,219,19451425281),(289,219,19414868496)]⟩,
⟨[7,25,106,180,448],[[106,257],[65,180,258],[25,448],[12,18,129,288],[7,80,264],[33,130,260],[68,136,272],[],[]],[(268,223,10578366531),(274,223,10326463491),(289,226,28040245776)]⟩,
⟨[7,25,106,180,449],[[106,260],[180,264],[12,18,449],[7,80,136,288],[25,68,258],[33,130,272],[],[],[]],[(268,224,23746326816),(274,224,23494607376)]⟩,
⟨[7,56,201,338,420],[[20,34,201],[12,33,338],[10,17,420],[7,96,144,264],[56,68,130,257],[],[],[],[]],[]⟩,
⟨[7,25,42,52,76,82],[[7,96,384],[76,129,258],[25,160,320],[42,192,272],[52,65,130,264],[82,132,257],[33,136,260],[144,288],[]],[(97,230,36344967696),(161,231,36344967696),(193,231,36329177616),(224,231,36322878486),(225,232,36344967696),(289,231,32318435856),(321,231,32302645776),(352,231,32296346646),(353,232,32318435856),(385,233,36344967696),(386,234,36344967696),(388,234,36329238816),(392,234,36322939686),(400,234,36244112166),(416,233,36339720981),(417,235,36344967696),(448,233,36245226261),(449,235,36329177616),(480,235,36322878486),(481,236,36344967696)]⟩,
⟨[7,25,42,52,76,146],[[33,76,146],[7,160,320],[25,96,384],[42,192,257],[52,65,136,258],[80,129,260],[66,132,288],[264],[272]],[(97,231,36343984641),(161,231,36092203041),(193,237,36344967696),(224,237,36339720981),(225,238,36344967696),(289,239,36344967696),(321,240,36344967696),(322,241,36344967696),(336,241,36339528261),(352,240,36339720981),(353,242,36344967696),(385,240,36093247776),(388,241,36093247776),(392,241,36087993381),(416,240,36087993381),(417,242,36093247776),(448,243,36344967696),(449,244,36344967696),(480,244,36339720981),(481,245,36344967696)]⟩,
⟨[7,25,42,52,76,193],[[42,193,272],[7,144,288],[25,96,130,260],[18,33,76,384],[52,136,320],[80,132,258],[66,160,257],[264],[]],[(82,231,36329177616),(146,237,36344967696),(274,240,32318435856),(289,241,32317452801),(322,246,36344967696),(336,246,36344767296),(338,247,36344967696),(352,248,36344967696),(386,249,36344967696),(388,250,36344967696),(392,250,36344767296),(400,249,36344767296),(402,251,36344967696),(416,252,36344967696)]⟩,
⟨[7,25,42,52,76,210],[[33,210,264],[7,160,320],[25,96,260],[42,65,384],[52,136,257],[76,129,288],[132,258],[272],[]],[(97,232,36343984641),(161,238,36343984641),(289,242,32317452801),(321,247,32318435856),(352,247,32313189141),(353,253,36344967696),(385,254,36344967696),(388,255,36344967696),(392,255,36339720981),(416,254,36339720981),(417,256,36344967696)]⟩,
⟨[7,25,42,52,76,385],[[42,80,385],[7,192,288],[25,66,160,260],[52,65,136,258],[33,76,130,272],[144,320],[18,96,132,264],[],[]],[(82,233,36344967696),(97,234,36343984641),(146,240,36093247776),(194,249,36343984641),(208,249,36343653201),(210,254,36344967696),(224,252,36339528261),(274,240,28040184096),(322,249,32317452801),(336,249,32317121361),(338,254,32318435856),(352,252,32312996421)]⟩,
⟨[7,25,42,52,76,388],[[25,66,388],[7,96,144,264],[52,130,320],[18,76,129,288],[42,192,257],[65,160,258],[33,80,136],[272],[]],[(82,234,36329238816),(97,234,36327272706),(146,241,36093247776),(161,241,36091281666),(193,250,36344967696),(194,250,36343984641),(208,250,36340511316),(210,255,36344967696),(224,250,36339528261),(225,255,36343984641),(274,241,28040184096),(289,241,28038217986),(321,250,32318435856),(322,250,32317452801),(336,250,32313979476),(338,255,32318435856),(352,250,32312996421),(353,255,32317452801)]⟩,
⟨[7,25,42,52,76,402],[[33,76,402],[7,192,288],[25,160,320],[42,65,132],[52,66,129,264],[96,136,257],[80,260],[],[]],[(97,235,36343984641),(161,242,36091281666),(193,251,36344967696),(224,251,36339720981),(225,256,36343984641),(289,242,28038217986),(321,251,32318435856),(352,251,32313189141),(353,256,32317452801)]⟩,
⟨[7,25,42,52,76,448],[[7,448],[33,76,144,258],[52,65,130,264],[25,66,160,260],[42,80,132,257],[96,129,272],[18,136,288],[],[]],[(82,233,36245226261),(97,233,36241294161),(146,243,36344967696),(161,243,36343984641),(274,243,32318435856),(289,243,32317452801)]⟩,
⟨[7,25,42,52,76,449],[[42,449],[7,96,144,264],[25,66,160,260],[18,76,288],[52,136,258],[33,130,272],[80,132],[],[]],[(82,235,36329177616),(146,244,36344967696),(274,244,32318435856)]⟩,
⟨[7,25,42,52,76,466],[[33,466],[7,136,288],[25,160,260],[42,65,132],[52,129,264],[76,257],[96],[],[]],[(97,236,36343984641),(161,245,36343984641),(289,245,32317452801)]⟩,
⟨[7,25,42,52,193,322],[[52,193,264],[25,132,322],[42,68,144,257],[7,80,136,288],[12,18,33,384],[96,130,260],[72,160,272],[],[]],[(76,246,36344967696),(140,249,36093309456),(146,250,36093247776),(268,249,28039262721),(289,250,28038217986),(388,257,36344967696),(392,258,36344967696),(396,259,36344967696),(400,260,36344967696),(416,260,32317452801)]⟩,
⟨[7,25,42,52,193,332],[[18,33,332],[42,193,272],[7,96,144],[25,160,258],[52,130,257],[80,384],[66,132,288],[136],[]],[(82,247,36344906016),(146,251,36093247776),(274,254,28040184096),(289,255,28038217986),(386,259,36093309456),(400,259,36093109056),(402,261,36344967696),(416,262,36344967696)]⟩,
⟨[7,25,42,52,193,352],[[52,193,264],[25,130,352],[42,68,384],[7,72,160,272],[33,80,132,258],[18,136,260],[12,66,144,257],[],[]],[(76,248,36344967696),(82,248,36344906016),(140,252,36093309456),(146,252,36093247776),(268,252,28034806341),(274,252,28034929701),(386,260,31814136321),(388,260,31814012961),(392,260,31813928241),(396,262,36093309456),(400,260,31813804881),(402,262,36093247776)]⟩,
⟨[7,25,42,52,204,338],[[33,204],[129,338],[7,144,288],[25,160,260],[42,257],[52,65,384],[96,130,264],[],[]],[(97,253,36342939906),(161,256,36091281666),(289,256,28038156306),(385,261,31815119376),(416,261,31809872661),(417,263,36344967696)]⟩,
⟨[7,25,42,76,112,146],[[7,112,384],[76,146,257],[25,66,132,288],[20,42,129,320],[65,160,260],[33,192,264],[36,136,258],[272],[]],[(161,237,35823617586),(164,264,36344967696),(193,264,36312526881),(276,265,36344967696),(289,266,36344967696),(292,267,36344967696),(321,267,32285995041),(322,265,36272420421),(385,268,36344967696),(388,269,36344967696),(392,270,36344967696),(416,268,36272420421),(417,271,36344967696),(420,272,36344967696),(448,269,36272420421),(449,272,36272420421)]⟩,
⟨[7,25,42,76,112,385],[[112,385],[7,192,272],[25,36,130,320],[18,33,76],[42,65,132],[20,160,258],[66,136,260],[144,288],[264]],[(146,268,36344967696),(148,268,36329238816),(164,269,36327272706),(194,269,36311543826),(274,268,32318435856),(276,268,32302706976),(292,269,32300740866),(322,269,32285011986)]⟩,
⟨[7,25,42,76,112,392],[[7,112,392],[25,36,130,320],[20,42,192,257],[18,76,129,288],[65,160,258],[33,66,132,272],[144,260],[],[]],[(146,270,36344967696),(148,270,36329238816),(161,270,36343984641),(164,270,36327272706),(193,270,36312526881),(194,270,36311543826),(274,270,32318435856),(276,270,32302706976),(289,270,32317452801),(292,270,32300740866),(321,270,32285995041),(322,270,32285011986)]⟩,
⟨[7,25,42,76,112,402],[[33,76,402],[7,112,264],[25,36,192],[42,129,260],[20,66,160,257],[65,132,288],[136,320],[],[]],[(161,271,36343984641),(164,272,36239979606),(193,272,36312526881),(289,271,32317452801),(292,272,32213447766),(321,272,32285995041)]⟩,
⟨[7,25,42,76,146,224],[[7,224,264],[76,146,257],[42,65,132,272],[25,36,320],[48,66,136,260],[20,33,384],[80,129,258],[288],[]],[(52,237,36339720981),(276,273,36344967696),(289,274,36344967696),(292,275,36344967696),(304,275,36093170736),(308,276,36344967696),(321,277,36344967696),(322,278,36344967696),(336,279,36344967696),(385,277,36093170736),(388,279,36093170736),(392,278,36093170736)]⟩,
⟨[7,25,42,76,146,225],[[225,260],[76,146,288],[7,48,264],[25,36,258],[42,80,132,257],[66,136,272],[20,320],[384],[]],[(52,238,36344967696),(276,280,36344967696),(292,281,36344967696),(304,281,36093170736),(308,282,36344967696),(322,283,36344967696),(336,284,36344967696),(388,284,36093170736),(392,283,36093170736)]⟩
]
private def data9Part12 : Array E19Cert.Row := #[
⟨[7,25,42,76,146,276],[[42,65,276],[33,76,146],[7,96,384],[25,160,320],[36,66,136,257],[80,129,288],[48,192,258],[132,264],[]],[(97,246,36327272706),(112,265,36344967696),(161,246,35823617586),(164,265,36093170736),(193,266,36011577411),(224,273,36344967696),(225,280,36344967696),(289,266,28037157891),(321,246,23696835426),(322,265,28008649536),(352,273,32302706976),(353,280,32302706976),(385,246,22690357506),(392,265,27253752336),(416,273,27253752336),(417,280,27253752336),(448,273,23211491616),(449,280,23211491616),(480,285,36344967696),(481,286,36344967696)]⟩,
⟨[7,25,42,76,146,289],[[76,146,289],[7,80,160,264],[25,96,384],[20,42,129,320],[36,192,272],[48,65,136,260],[66,132],[258],[]],[(52,239,36344967696),(112,266,36344967696),(164,266,36093170736),(193,270,35004630291),(224,274,36344967696),(276,266,28037157891),(322,270,10838558001),(336,274,32317452801),(388,274,31813928241),(392,270,10335106881),(448,287,36344967696)]⟩,
⟨[7,25,42,76,146,292],[[76,146,257],[25,66,292],[7,48,192,264],[20,42,129,320],[33,80,136,258],[96,384],[65,160,272],[132],[]],[(97,240,32300740866),(112,267,36344967696),(161,246,35820668451),(193,268,36011577411),(224,275,36344967696),(225,281,36344967696),(321,268,28003734276),(322,250,23690937126),(336,277,32300740866),(385,275,31279031601),(392,278,31277979186),(448,288,36344967696),(449,289,36344967696)]⟩,
⟨[7,25,42,76,146,308],[[65,136,308],[33,76,146],[7,96,384],[25,160,320],[42,192,257],[66,129,264],[80,132,258],[],[]],[(97,247,36327272706),(161,247,35823617586),(193,271,35004630291),(224,276,36344967696),(225,282,36344967696),(321,281,32285995041),(322,283,32285011986),(385,281,31279031601),(392,283,31277979186),(448,290,36344967696),(449,291,36344967696)]⟩,
⟨[7,25,42,76,146,322],[[25,160,322],[33,76,146],[7,80,136,288],[20,42,65,384],[48,132,257],[96,129,260],[36,192,272],[264],[]],[(52,241,36344967696),(97,241,32285011986),(112,265,36272420421),(161,250,35820668451),(164,270,35014459701),(193,265,36011577411),(224,278,36344967696),(225,283,36344967696),(276,265,28008649536),(289,270,10838558001),(292,250,23690937126),(304,278,32285011986),(308,283,32285011986),(385,278,17305855251),(388,278,1116168981),(392,292,36344967696),(416,293,36344967696),(417,294,36344967696),(420,294,32285011986)]⟩,
⟨[7,25,42,76,146,336],[[7,160,336],[48,76,257],[25,66,132,288],[20,42,65,384],[36,146,264],[33,136,258],[96,129,260],[192],[]],[(52,241,36339528261),(97,248,36327272706),(161,249,35823617586),(164,269,36093170736),(193,267,30140356131),(224,279,36344967696),(225,284,36344967696),(289,274,32317452801),(292,277,32300740866),(385,275,17305785891),(388,295,36344967696),(392,278,612570981),(416,296,36344967696),(417,297,36344967696),(420,298,36344967696)]⟩,
⟨[7,25,42,76,146,352],[[7,136,352],[76,146,257],[42,80,129,260],[25,36,66,384],[48,65,132,264],[20,160,258],[33,192,272],[],[]],[(52,240,36339720981),(161,249,35820668451),(164,268,35014459701),(193,269,36011577411),(276,273,32302706976),(385,288,31279031601),(388,296,36093170736),(392,293,36093170736)]⟩,
⟨[7,25,42,76,146,353],[[132,353],[76,146],[7,160,272],[25,36,66,384],[42,80,129,260],[20,136,258],[48,192,264],[],[]],[(52,242,36344967696),(164,271,36093170736),(276,280,32302706976),(388,297,36093170736),(392,294,36093170736)]⟩,
⟨[7,25,42,76,146,368],[[7,136,368],[76,146,257],[25,132,258],[20,42,65,384],[36,66,129,264],[160,260],[33,192],[],[]],[(161,251,35823617586),(164,272,36093170736),(193,272,36011577411),(385,289,31279031601),(388,298,36093170736),(392,294,31277979186)]⟩,
⟨[7,25,42,76,146,448],[[7,48,448],[76,146,288],[25,96,260],[42,65,132,272],[36,80,129,264],[20,66,160,257],[33,136,258],[],[]],[(52,243,36344967696),(97,252,36327272706),(112,269,36272420421),(161,252,35823617586),(164,269,35014459701),(276,273,23211491616),(289,287,36344967696),(292,288,36344967696),(304,288,36093170736),(308,290,36344967696)]⟩,
⟨[7,25,42,76,146,449],[[20,42,449],[76,146,288],[7,80,160,264],[25,36,258],[48,66,136,260],[96,132,272],[33],[],[]],[(52,244,36344967696),(112,272,36272420421),(164,272,35014459701),(276,280,23211491616),(292,289,36344967696),(304,289,36093170736),(308,291,36344967696)]⟩,
⟨[7,25,42,76,146,480],[[7,480],[76,146,257],[42,80,129,260],[25,36,258],[20,33,66,264],[65,136,272],[48,132],[],[]],[(52,244,36339720981),(276,285,36344967696)]⟩,
⟨[7,25,42,76,146,481],[[20,481],[76,146],[7,136,272],[25,36,258],[42,80,260],[48,66,132,264],[],[],[]],[(52,245,36344967696),(276,286,36344967696)]⟩,
⟨[7,25,42,76,176,336],[[7,176,264],[42,129,336],[18,33,76,384],[25,66,132,288],[36,65,136,258],[20,192,257],[96,130,260],[],[]],[(97,246,36255970626),(193,275,36011577411),(194,279,36311543826),(289,275,28037157891),(292,279,32300740866),(385,299,36344967696),(386,300,36344967696),(388,300,32302706976),(392,293,8694995061)]⟩,
⟨[7,25,42,76,176,338],[[33,136,338],[7,176,264],[25,36,384],[42,65,132],[76,129,288],[20,192,257],[96,130,260],[],[]],[(97,247,36255970626),(193,276,36312526881),(289,281,28037157891),(292,284,32300740866),(385,301,36344967696),(388,302,36344967696),(392,303,36344967696)]⟩,
⟨[7,25,42,76,176,385],[[76,176,258],[7,96,136,272],[42,80,385],[25,66,132,288],[18,33,192,260],[20,130,320],[36,65,264],[],[]],[(82,249,36312196401),(97,250,36255970626),(194,279,36009611316),(274,268,23221962516),(276,275,1215386211),(292,295,32300740866),(322,296,27956547636),(336,299,36344967696),(338,301,36344967696),(352,300,36343984641)]⟩,
⟨[7,25,42,76,176,388],[[7,176,320],[42,65,388],[25,36,192,258],[18,76,129,288],[96,130,272],[20,66,136,257],[33,80,264],[],[]],[(82,252,36261868836),(97,252,36255970626),(193,277,36011577411),(194,277,36009611316),(274,277,23492363826),(289,277,23489414691),(321,288,19067707731),(322,288,19065741621),(336,300,32302706976),(338,302,36344967696),(352,300,32300740866),(353,302,36343984641)]⟩,
⟨[7,25,42,76,176,392],[[7,96,392],[76,176,258],[25,66,132,288],[20,42,192,257],[18,36,129,320],[65,130,272],[33,80,260],[],[]],[(82,250,36312196401),(97,250,36306298131),(193,278,36011577411),(194,278,36009611316),(274,250,18657519366),(276,278,8728548981),(289,250,18659485536),(292,278,8727565911),(321,293,27958513731),(322,293,27956547636),(336,293,8694995061),(338,303,36344967696),(352,293,8694011991),(353,303,36343984641)]⟩,
⟨[7,25,42,76,176,448],[[20,42,448],[76,176,257],[7,96,136,272],[25,66,132,288],[36,65,258],[18,33,260],[80,129,264],[130],[]],[(82,249,36261868836),(97,249,36255970626),(274,288,28040107056),(276,296,32302706976),(289,288,28037157891),(292,296,32300740866)]⟩,
⟨[7,25,42,76,176,449],[[18,36,449],[76,176,258],[25,66,132,288],[7,96,136,272],[42,80,260],[20,33,130,264],[],[],[]],[(82,251,36312196401),(274,289,28040107056),(276,297,32302706976),(292,298,32300740866)]⟩,
⟨[7,25,42,76,180,338],[[65,180,264],[33,136,338],[7,96,384],[25,192,288],[42,129,260],[76,130,257],[],[],[]],[(97,253,36327272706),(193,282,36312526881),(289,282,32317452801),(385,304,36344967696),(392,305,36344967696)]⟩,
⟨[7,25,42,76,180,385],[[65,180,258],[42,80,385],[7,136,320],[25,66,288],[33,76,130,272],[18,96,264],[192,260],[],[]],[(82,254,36329238816),(97,255,36327272706),(194,284,36009611316),(274,281,19199436081),(322,297,27956547636),(336,301,32302706976),(338,304,36344967696),(352,302,32300740866)]⟩,
⟨[7,25,42,76,180,392],[[180,320],[7,80,392],[25,96,130,260],[42,65,272],[18,76,257],[66,129,288],[33,192,258],[],[]],[(82,255,36245348661),(97,255,36243382611),(193,283,36011577411),(194,283,36009611316),(274,283,19198383666),(289,283,19193468451),(321,294,27958513731),(322,294,27956547636),(336,303,32302706976),(338,305,36344967696),(352,303,32300740866),(353,305,36343984641)]⟩,
⟨[7,25,42,76,180,448],[[65,180,264],[42,448],[18,76,257],[7,80,136,288],[25,96,258],[66,129,272],[33,130,260],[],[]],[(82,254,36245156901),(97,254,36240241746),(274,290,32318435856),(289,290,32317452801)]⟩
]
private def data9Part13 : Array E19Cert.Row := #[
⟨[7,25,42,76,180,449],[[42,449],[66,180,264],[7,96,136,272],[25,258],[18,76,288],[33,80,130,260],[],[],[]],[(82,256,36329238816),(274,291,32318435856)]⟩,
⟨[7,25,42,76,240,385],[[7,240,264],[18,76,385],[25,36,258],[42,65,132,272],[33,66,136,260],[20,130,288],[320],[],[]],[(274,289,19199436081),(276,289,19167978321),(292,298,28003734276),(322,298,27956547636)]⟩,
⟨[7,25,42,76,240,392],[[7,240],[18,36,65,392],[25,66,260],[20,42,257],[33,76,258],[129,320],[130,272],[132,288],[]],[(274,294,19198383666),(276,294,19151197026),(289,294,19193468451),(292,294,19143332646),(321,294,19067638371),(322,294,19064689206)]⟩,
⟨[7,25,42,84,164,200],[[7,200,272],[25,164,258],[42,84,257],[12,18,96,384],[66,144,288],[48,65,130,260],[33,320],[129,264],[]],[(97,264,36057858561),(146,264,35810132496),(268,292,23746326816),(274,295,23730536976),(289,295,23223288321),(304,306,36344967696),(321,295,23144178801),(322,306,34712531526),(352,295,21526626936),(353,307,36344967696),(385,306,35726045796),(386,295,22381339671),(400,295,22286516871),(402,307,36092326401)]⟩,
⟨[7,25,42,84,164,304],[[7,192,264],[25,164,320],[42,84,384],[12,66,129,304],[18,65,136,260],[33,72,144,258],[96,130,257],[],[]],[(97,265,36243136851),(146,265,34479563061),(193,279,34903192401),(194,279,34397909781),(200,306,36344967696),(268,265,2267100261),(321,279,10743927921),(322,306,6447920166),(328,279,2185434741),(385,306,4432688226),(386,279,8727712791),(392,279,674502231),(448,258,22585376886),(449,308,36344967696),(450,308,36092326401),(456,308,28039054641)]⟩,
⟨[7,25,42,84,164,322],[[25,164,322],[42,84,129],[7,72,144,288],[33,136,272],[12,96,130,257],[48,65,384],[18,192,264],[260],[]],[(97,266,36324123651),(146,270,34479563061),(193,274,34903192401),(200,306,34712531526),(268,270,2188788501),(289,274,10838558001),(304,306,6447920166),(385,309,36344967696),(392,310,36344967696),(400,310,32302645536)]⟩,
⟨[7,25,42,84,164,328],[[18,164,328],[7,96,384],[42,84,129],[25,130,288],[12,66,144,257],[33,192,272],[48,65,136,258],[260],[]],[(97,267,32234291811),(146,269,35825722416),(193,277,35440976211),(194,279,34429428021),(274,269,23730536976),(289,277,19445126691),(304,279,2185434741),(385,310,36092326401),(386,300,26441367861),(400,300,10209137781),(402,311,36344967696)]⟩,
⟨[7,25,42,84,164,352],[[25,130,352],[7,192,272],[42,84,384],[18,65,164,264],[12,33,144,258],[48,66,136,257],[72,129,260],[],[]],[(146,269,34479563061),(193,277,34903192401),(194,273,34397909781),(200,295,21526626936),(268,278,23746326816),(274,279,23746126896),(385,310,31544721666),(386,296,8694289431),(392,300,8694273111),(400,260,22317990006),(402,312,36344967696)]⟩,
⟨[7,25,42,84,164,353],[[18,136,353],[25,164,258],[42,84,384],[7,144,264],[48,72,130,260],[12,192,272],[66,129],[],[]],[(146,272,34479563061),(194,276,34397909781),(200,307,36344967696),(268,283,23746326816),(274,284,23746126896),(386,301,26442420276),(392,311,36092326401),(400,312,36092326401),(402,313,36344967696)]⟩,
⟨[7,25,42,84,164,448],[[42,448],[84,129,288],[25,164,258],[7,96,136,272],[33,66,144,264],[48,65,130,260],[18,72,257],[12],[]],[(97,268,36243136851),(146,268,34479563061),(268,293,23746326816),(274,296,23746126896),(289,296,23489553411),(304,258,22585376886)]⟩,
⟨[7,25,42,84,164,449],[[42,449],[25,164,258],[33,84,130,264],[7,72,272],[48,66,136,260],[12,18,288],[96,144],[],[]],[(146,271,35825722416),(268,294,23746326816),(274,297,23746126896),(304,308,36344967696)]⟩,
⟨[7,25,42,84,164,456],[[7,48,456],[25,164,258],[42,84,257],[12,33,130,272],[18,96,129,260],[66,144,288],[65],[],[]],[(97,272,36324123651),(146,272,35825722416),(274,298,23746126896),(289,298,23489553411),(304,308,28039054641)]⟩,
⟨[7,25,42,84,224,385],[[42,84,385],[7,224,264],[25,66,132,288],[36,72,144,258],[48,65,130,260],[12,33,272],[18,136,320],[],[]],[(140,274,35825922336),(146,274,35810132496),(268,287,23746326816),(274,287,23730536976),(292,310,23491657986),(304,310,23491315266),(322,310,23412891666),(328,310,23412610146)]⟩,
⟨[7,25,42,84,224,386],[[25,224,260],[42,84,257],[7,72,144,288],[12,48,65,386],[18,36,129,264],[33,66,132,272],[136,320],[],[]],[(140,275,35825922336),(268,288,23746326816),(289,288,1192777266),(292,296,641225751),(304,300,640964631),(321,300,23379206211),(328,260,14296746006)]⟩,
⟨[7,25,42,84,224,396],[[18,33,396],[7,224,272],[42,84,257],[25,66,288],[36,65,144,258],[48,129,320],[72,130],[],[]],[(146,276,35810132496),(274,290,23730536976),(289,302,28037157891),(304,312,32318297136),(321,302,27958198611),(322,312,32302645536)]⟩,
⟨[7,25,42,84,225,386],[[18,225,260],[42,84,257],[25,36,386],[7,48,136,320],[66,132,264],[12,272],[72,144,288],[],[]],[(140,281,35825922336),(268,289,23746326816),(292,301,10336292916),(304,311,28039054641),(328,312,27991745361)]⟩,
⟨[7,25,42,84,225,396],[[225,258],[18,396],[42,84,257],[7,72,272],[25,36,130,320],[48,66],[144,288],[],[]],[(146,282,35810132496),(274,291,23730536976),(304,313,32318297136),(322,313,32302645536)]⟩,
⟨[7,25,42,116,193,322],[[116,130,264],[25,132,322],[42,193,260],[7,136,288],[12,18,33,384],[72,144,257],[160,272],[],[]],[(140,284,35004944451),(146,283,35004630291),(268,284,10843787316),(289,283,10838558001),(388,259,22607782416),(392,308,13162206786),(396,314,36344967696),(400,312,12910356306),(416,312,826828581)]⟩,
⟨[7,25,42,116,193,386],[[116,264],[25,386],[42,132,257],[7,72,160,272],[12,18,193,288],[33,66,136,260],[144,320],[],[]],[(140,280,35557552161),(268,297,10340470836),(289,294,10335241521),(328,308,13162137426)]⟩,
⟨[7,25,42,116,193,388],[[116,136,258],[42,193,272],[25,66,388],[7,72,144,288],[12,18,160,257],[33,130,264],[320],[],[]],[(146,281,35004630291),(274,301,23494468656),(289,303,642281811),(322,259,22607782416),(328,312,12910548066)]⟩,
⟨[7,25,42,116,193,396],[[116,258],[18,33,396],[42,193,272],[7,144,320],[25,66,288],[72,130,257],[160],[],[]],[(146,282,35557221681),(274,304,28040107056),(289,305,28037157891),(322,314,36344967696)]⟩,
⟨[7,25,42,116,193,416],[[116,136,257],[7,72,416],[42,193,260],[18,33,132,264],[25,258],[12,66,272],[130,320],[144],[]],[(140,284,35557552161),(146,284,35557221681),(268,302,23492702466),(274,302,23492363826),(322,312,826828581),(328,312,826746981)]⟩,
⟨[7,25,42,193,322,432],[[12,432],[25,36,322],[20,42,193],[18,33,68,136],[7,80,264],[72,132,257],[96,130,260],[],[]],[(76,285,36312526881),(84,298,31432269891),(100,298,23373307956),(140,298,35004944451),(268,298,10843787316)]⟩,
⟨[7,25,42,193,322,436],[[72,436],[25,322],[42,68,257],[7,96,136],[12,18,193],[33,80,130,264],[],[],[]],[(76,286,36312526881)]⟩
]
private def data9Part14 : Array E19Cert.Row := #[
⟨[7,25,42,193,324,432],[[7,72,432],[42,324],[25,36,130],[12,18,193],[33,80,136,258],[20,66,264],[96,132,257],[],[]],[(82,289,36011263251),(140,289,30140670291)]⟩,
⟨[7,25,42,193,332,402],[[33,332],[36,402],[20,42,193],[7,48,136],[25,66,132,288],[80,160,257],[96],[],[]],[(52,261,36344967696),(112,313,36325885506),(164,313,35822911746),(289,305,19445196051)]⟩,
⟨[7,25,42,193,332,416],[[48,130,332],[7,80,416],[20,42,193],[25,36,258],[18,96,132,257],[33,66,144],[136,272],[],[]],[(52,262,36344967696),(82,290,36312196401),(112,311,36040611666),(146,298,35557221681),(148,302,35004629331),(274,302,19198383666)]⟩,
⟨[7,25,42,193,332,432],[[7,432],[18,33,332],[20,42,193],[25,96,130],[36,80,136,258],[66,132,257],[],[],[]],[(82,291,36312196401)]⟩,
⟨[7,25,42,193,340,416],[[33,130,340],[7,72,416],[42,193],[25,96,132,258],[36,66,144,264],[48,136,257],[12,18],[],[]],[(140,297,35557552161),(146,297,35557221681)]⟩,
⟨[7,25,42,196,336,416],[[7,136,336],[25,196,258],[20,42,65],[12,18,416],[36,66,129,264],[33,72,144,260],[48,130,257],[96],[]],[(52,257,36341633091),(97,299,36306298131),(146,299,35557221681),(268,299,19451424801)]⟩,
⟨[7,25,42,196,336,417],[[12,18,417],[20,42,65],[7,136,336],[25,196,258],[36,66,144,264],[48,72,130,260],[96],[],[]],[(52,259,36341633091),(146,301,35557221681),(268,301,19451424801)]⟩,
⟨[7,25,42,196,338,417],[[12,338],[20,72,417],[42,196],[7,48,136],[25,96,130,260],[36,65,144,264],[],[],[]],[(52,261,36343861281),(268,304,19451424801)]⟩,
⟨[7,25,42,204,338,417],[[48,204],[36,338],[20,417],[7,96,144,264],[25,130,260],[42,65],[],[],[]],[(52,263,36344967696)]⟩,
⟨[7,25,97,170,212,385],[[170,260],[212,264],[7,72,288],[25,36,258],[12,97,272],[48,66,385],[18,320],[],[]],[(268,305,1215701331),(274,305,1199727891),(292,305,1177055571),(304,305,1176590451),(322,305,1114080531),(328,305,1113921411)]⟩,
⟨[7,25,97,170,308,448],[[68,170,257],[72,129,308],[7,448],[18,97,132,264],[25,66],[12,80,258],[144],[],[]],[(76,304,36243382611),(82,304,32216605971)]⟩,
⟨[7,25,97,170,340,385],[[170,340],[7,48,192,264],[25,66,132,288],[12,97,144,258],[18,36,72,385],[],[],[],[]],[]⟩,
⟨[7,25,98,168,308,449],[[72,130,308],[12,18,449],[7,80,168],[25,98,132],[10,33,68,144],[258],[264],[],[]],[(76,313,36261208116),(146,313,34750871076),(266,314,10861483011)]⟩,
⟨[7,25,98,168,336,388],[[7,168,336],[25,98,388],[10,48,68,129],[12,18,192,257],[20,72,130,288],[36,65,144,264],[33,258],[],[]],[(52,309,36341633091),(76,309,32252432451),(146,309,26448319491),(193,309,26329248816),(266,309,10326709251),(289,309,10285974576)]⟩,
⟨[7,25,42,52,76,82,97],[[7,384],[52,129,264],[25,130,320],[42,132,257],[97,136,258],[76,144,288],[82,160,260],[192,272],[]],[(385,315,36344967696),(386,315,36343984641),(388,315,36312526881),(392,315,36343776561),(400,315,36312196401),(416,315,36272751921),(448,315,36241171761)]⟩,
⟨[7,25,42,52,76,82,161],[[76,161,258],[82,384],[7,192,264],[25,96,130,260],[42,132,320],[52,136,257],[65,144,288],[272],[]],[(321,316,36344967696),(352,316,36339720981),(386,317,36344967696),(388,317,36344906016),(392,317,36344828976),(400,317,36344767296),(448,318,36344967696)]⟩,
⟨[7,25,42,52,76,82,225],[[225,258],[25,384],[52,130,257],[76,144,288],[42,132,320],[82,136,260],[7,264],[272],[]],[(386,319,36344967696),(388,319,36329238816),(392,319,36344828976),(400,319,36329038896)]⟩,
⟨[7,25,42,52,76,82,385],[[42,385],[7,192,288],[25,160,320],[33,76,130,272],[52,65,136,258],[82,132,264],[96,144,260],[],[]],[(97,315,36344967696),(224,318,36322878486),(352,318,32296346646)]⟩,
⟨[7,25,42,52,76,82,386],[[25,96,386],[7,160,320],[42,192,257],[33,82,132,264],[52,65,136],[76,129,288],[144,260],[272],[]],[(97,315,36343984641),(161,317,36344967696),(193,317,36329177616),(224,317,36322878486),(225,319,36344967696),(289,317,32318435856),(321,317,32302645776),(352,317,32296346646),(353,319,32318435856)]⟩,
⟨[7,25,42,52,76,82,417],[[76,417],[7,96,144,264],[25,130,320],[42,65,132,272],[52,192,258],[82,136,260],[],[],[]],[]⟩,
⟨[7,25,42,52,76,82,481],[[481],[7,144,264],[25,130,260],[42,132,272],[52,136,258],[76],[82],[],[]],[]⟩,
⟨[7,25,42,52,76,146,193],[[42,193,260],[33,76,146],[7,80,136,288],[25,96,132,258],[52,66,257],[160,320],[384],[264],[272]],[(289,320,36344967696),(322,321,36344967696),(336,321,36344767296),(352,322,36344967696),(388,321,36093247776),(392,321,36093170736),(416,322,36093247776)]⟩,
⟨[7,25,42,52,76,146,225],[[225,258],[76,146,257],[7,80,264],[25,66,260],[42,132,272],[52,136,320],[384],[288],[]],[(322,323,36344967696),(336,323,36344767296),(388,323,36093247776),(392,323,36093170736)]⟩,
⟨[7,25,42,52,76,146,289],[[76,146,289],[7,80,136],[25,96,384],[42,65,132,272],[52,192,258],[129,320],[66,160,260],[264],[]],[(193,320,36344967696),(224,320,36339720981),(322,320,32317452801),(336,320,32317121361),(388,320,31814012961),(392,320,31813928241),(448,324,36344967696)]⟩
]
private def data9Part15 : Array E19Cert.Row := #[
⟨[7,25,42,52,76,146,321],[[42,132,321],[76,146,288],[7,96,136,272],[25,66,384],[52,129,258],[80,160,260],[33,192,264],[],[]],[(161,317,36092203041),(224,322,36339720981),(388,325,36344967696),(392,325,36344767296),(416,326,36344967696)]⟩,
⟨[7,25,42,52,76,146,322],[[25,160,322],[33,76,146],[7,80,136,288],[42,65,384],[52,192,257],[96,129,260],[132,272],[264],[]],[(97,316,36343984641),(161,317,36091219986),(193,321,36344967696),(224,321,36339720981),(225,323,36344967696),(289,320,32317452801),(385,325,36093247776),(388,327,36344967696),(392,327,36339720981),(416,325,36087993381),(417,328,36344967696)]⟩,
⟨[7,25,42,52,76,146,353],[[146,353],[76,160,258],[7,136,272],[25,66,132],[42,192,260],[52,384],[80,129,264],[],[]],[(388,328,36093247776),(392,328,36093170736)]⟩,
⟨[7,25,42,52,76,146,448],[[7,448],[76,146,288],[42,65,260],[25,96,132,258],[52,66,129,264],[80,160,257],[33,136,272],[],[]],[(97,318,36343984641),(161,318,36092203041),(289,324,36344967696)]⟩,
⟨[7,25,42,52,76,146,449],[[42,449],[76,146,288],[7,80,160,264],[25,96,260],[52,136,258],[33,66,132,272],[],[],[]],[]⟩,
⟨[7,25,42,52,76,146,481],[[481],[76,146],[7,136,272],[25,132,258],[42,80,260],[52,66,264],[],[],[]],[]⟩,
⟨[7,25,42,52,76,193,322],[[52,193,264],[25,160,322],[42,144,260],[7,96,136,272],[18,33,76,384],[80,130,257],[132,288],[],[]],[(146,321,36344967696),(289,321,32317452801),(388,329,36344967696),(392,330,36344967696),(400,331,36344967696),(416,331,32317452801)]⟩,
⟨[7,25,42,52,76,193,338],[[33,132,338],[42,193,260],[7,136,288],[25,160],[76,144,257],[52,384],[96,130,264],[],[]],[(289,323,32317452801),(388,332,36344967696),(392,332,36344767296),(416,333,36344967696)]⟩,
⟨[7,25,42,52,76,193,352],[[52,193,258],[7,144,352],[33,76,130,272],[25,66,384],[42,80,132,257],[18,136,260],[160,264],[],[]],[(82,316,36245226261),(146,322,36344967696),(274,322,32313189141),(386,334,36344967696),(388,335,36344967696),(392,335,36344767296),(400,334,36344767296),(402,336,36344967696)]⟩,
⟨[7,25,42,52,76,193,386],[[25,96,386],[52,193,264],[7,80,136,288],[42,144,257],[33,76,272],[66,160,260],[18,132,320],[],[]],[(82,317,36329177616),(289,325,28038217986),(336,331,36344767296),(352,334,36344967696)]⟩,
⟨[7,25,42,52,76,193,388],[[42,193,272],[25,66,388],[52,136,258],[7,144,288],[18,33,76],[96,130,257],[160,320],[80,264],[]],[(82,317,36329238816),(146,321,36093247776),(274,325,32318435856),(289,327,32317452801),(322,329,36344967696),(336,330,36344767296),(338,332,36344967696),(352,335,36344967696)]⟩,
⟨[7,25,42,52,76,193,402],[[33,76,402],[42,193,260],[7,96,264],[25,66,132,288],[52,136,257],[160,320],[80],[],[]],[(289,328,32317452801),(352,336,36344967696)]⟩,
⟨[7,25,42,52,76,193,416],[[25,66,416],[52,193,258],[42,144,320],[18,76,257],[7,96,136,272],[33,80,130,260],[132,264],[],[]],[(82,318,36329177616),(146,322,36093247776),(274,326,32318435856),(322,331,32317452801),(336,331,32317121361),(338,333,36344967696)]⟩,
⟨[7,25,42,52,76,210,353],[[210,264],[132,353],[7,136,272],[25,160,260],[42,384],[52,129,258],[76],[],[]],[(388,337,36344967696),(392,337,36344767296)]⟩,
⟨[7,25,42,52,76,210,385],[[33,210,264],[76,385],[7,136,288],[25,96,132,258],[42,65,260],[52,320],[160,272],[],[]],[(97,319,36343984641),(352,333,32313189141)]⟩,
⟨[7,25,42,52,76,210,388],[[33,210,264],[25,96,388],[7,136,288],[52,129,320],[76,160,257],[42,65,272],[258],[],[]],[(97,319,36327272706),(161,323,36091281666),(289,328,28038217986),(321,332,32318435856),(352,332,32312996421),(353,337,36344967696)]⟩,
⟨[7,25,42,52,76,210,417],[[76,417],[210,260],[7,96,264],[25,132,258],[42,65,272],[52,136,320],[],[],[]],[]⟩,
⟨[7,25,42,52,193,322,388],[[25,96,388],[42,193,272],[52,136,322],[7,72,144,288],[12,18,33],[68,160,264],[80,130,257],[],[]],[(76,329,36344967696),(146,329,36093247776),(289,329,28038217986)]⟩,
⟨[7,25,42,52,193,322,392],[[52,193],[7,96,392],[25,132,322],[42,144,260],[12,18,33],[80,130,288],[68,160,272],[72,257],[]],[(76,330,36344967696),(146,330,36093170736),(289,330,28037157891)]⟩,
⟨[7,25,42,52,193,322,396],[[18,33,396],[52,193],[25,160,322],[42,80,257],[7,96,144],[72,130,288],[68,272],[],[]],[(146,332,36093247776),(289,332,28038217986)]⟩,
⟨[7,25,42,52,193,322,400],[[42,193,260],[52,136,322],[7,72,400],[25,68,160],[12,18,33],[80,132,288],[96,130,264],[257],[]],[(76,331,36344967696),(140,331,36093109056),(268,334,28039262721),(289,335,28038217986)]⟩,
⟨[7,25,42,52,193,332,402],[[33,332],[96,402],[42,193],[7,80,160],[25,66,132,288],[52,136,257],[],[],[]],[(289,337,28038217986)]⟩,
⟨[7,25,42,52,193,332,416],[[18,33,332],[42,193,272],[7,80,416],[25,96,132,258],[52,130,257],[66,144],[136],[],[]],[(82,333,36344906016),(146,336,36093247776),(274,333,27783271461)]⟩,
⟨[7,25,42,52,204,338,417],[[204],[338],[417],[7,96,144,264],[25,130,260],[42,65],[52],[],[]],[]⟩
]
private def data9Part16 : Array E19Cert.Row := #[
⟨[7,25,42,76,112,146,164],[[7,112,384],[25,164,258],[76,146,257],[20,42,129,320],[33,66,136,260],[65,288],[192,264],[272],[]],[(193,338,36344967696),(276,339,36344967696),(289,340,36344967696),(321,341,36344967696),(322,340,35973763671),(385,341,36093170736),(392,340,34463699991),(448,341,34463699991),(449,342,36344967696)]⟩,
⟨[7,25,42,76,112,146,276],[[7,112,384],[42,129,276],[76,146,257],[25,192,288],[65,160,258],[33,136,320],[66,132,264],[36],[]],[(161,321,35823617586),(164,339,36344967696),(193,340,36312526881),(289,340,32317452801),(321,321,23696835426),(322,339,32302706976),(385,330,22690357506),(392,343,36344967696),(416,344,36344967696),(417,345,36344967696),(448,344,32302706976),(449,345,32302706976)]⟩,
⟨[7,25,42,76,112,146,289],[[76,146,289],[7,112,384],[25,36,192,258],[20,42,129,320],[65,132,264],[66,160,260],[136,272],[],[]],[(164,340,36344967696),(193,340,36037662501),(276,340,32317452801),(322,340,27987547986),(388,346,36344967696),(392,347,36344967696),(448,346,32246871636)]⟩,
⟨[7,25,42,76,112,146,292],[[76,146,257],[7,112,264],[25,66,292],[20,42,65,384],[33,192,258],[129,320],[132,272],[136],[160]],[(161,321,35820668451),(193,341,36312526881),(321,341,32300740866),(322,321,23675143191),(385,348,36344967696),(392,349,36344967696),(448,348,32213447766),(449,350,36344967696)]⟩,
⟨[7,25,42,76,112,146,385],[[20,42,385],[7,112,264],[76,146,288],[25,132,320],[36,65,136,258],[33,192,260],[66,160,272],[],[]],[(164,341,36093170736),(276,330,22690357506),(292,348,36344967696),(322,344,36272420421)]⟩,
⟨[7,25,42,76,112,146,388],[[112,388],[7,160,320],[33,76,146],[25,36,192,258],[20,42,257],[65,136,288],[66,129,264],[272],[]],[(161,322,35823617586),(193,341,34434274851),(289,346,36344967696),(321,348,32285995041),(322,344,32229176646)]⟩,
⟨[7,25,42,76,112,146,392],[[7,112,392],[33,76,146],[25,36,320],[20,42,192,257],[65,160,258],[66,129,260],[132,288],[272],[]],[(161,320,35823617586),(164,340,34463699991),(193,340,34399803201),(276,343,36344967696),(289,347,36344967696),(292,349,36344967696),(321,349,32285995041),(322,343,27145619511)]⟩,
⟨[7,25,42,76,112,146,417],[[20,66,417],[7,112,264],[76,146],[25,36,192,258],[42,65,260],[132,320],[136,272],[],[]],[(276,345,36344967696),(322,345,36272420421)]⟩,
⟨[7,25,42,76,112,146,420],[[25,66,420],[7,112,264],[76,146,257],[20,42,129,320],[65,136,258],[33,192,272],[],[],[]],[(193,342,36312526881),(321,350,32285995041),(322,345,32229176646)]⟩,
⟨[7,25,42,76,146,224,276],[[7,224,264],[42,129,276],[33,76,146],[36,66,136,257],[25,132,288],[48,65,384],[320],[80,258],[]],[(289,346,28037157891),(321,331,23696835426),(322,344,28008649536),(385,331,22690357506),(392,344,27253752336)]⟩,
⟨[7,25,42,76,146,224,289],[[76,146,289],[7,224,272],[20,42,129,320],[25,36,258],[48,65,136,260],[80,132,264],[66,384],[],[]],[(52,320,36339720981),(276,346,28037157891),(322,349,1947751986),(336,351,36344967696),(388,351,36093170736),(392,349,1192638546)]⟩,
⟨[7,25,42,76,146,224,292],[[25,66,292],[76,146,257],[7,224,264],[42,65,132,272],[80,129,258],[20,33,136,320],[48,384],[],[]],[(321,348,28003734276),(322,325,23422567206),(336,352,36344967696),(385,352,31279031601),(392,335,18542501991)]⟩,
⟨[7,25,42,76,146,224,308],[[65,136,308],[7,224,264],[76,146,257],[42,129,320],[25,66,384],[33,80,132,258],[],[],[]],[(321,353,36344967696),(322,354,36344967696),(385,353,36093170736),(392,354,36093170736)]⟩,
⟨[7,25,42,76,146,224,321],[[76,146,288],[25,224,260],[20,42,321],[7,48,384],[36,66,136,272],[33,80,132,258],[129,264],[],[]],[(52,322,36339720981),(276,331,23696835426),(292,348,28003734276),(304,352,32285995041),(308,353,36344967696),(388,352,1098404706),(392,355,36344967696)]⟩,
⟨[7,25,42,76,146,224,322],[[25,36,322],[7,224,264],[76,146,288],[42,80,132,257],[48,129,260],[20,33,384],[65,136,272],[],[]],[(52,321,36339720981),(276,344,28008649536),(289,349,1947751986),(292,325,23422567206),(304,335,17535363111),(308,354,36344967696),(385,355,36093170736),(388,344,594039111),(392,327,22599378456)]⟩,
⟨[7,25,42,76,146,224,336],[[7,224,264],[25,66,132,288],[20,42,257],[33,76,146],[36,129,336],[48,65,136,260],[384],[258],[]],[(52,321,36339528261),(289,351,36344967696),(292,352,36344967696),(385,352,343107666),(388,356,36344967696),(392,344,845236311)]⟩,
⟨[7,25,42,76,146,225,276],[[225,276],[42,80,132,257],[76,146,288],[7,48,136,320],[25,36,258],[66,264],[384],[],[]],[(322,345,28008649536),(392,345,27253752336)]⟩,
⟨[7,25,42,76,146,225,292],[[20,225,258],[76,146,257],[25,66,292],[7,80,264],[42,384],[136,272],[48,132,320],[],[]],[(322,332,23690937126),(336,353,32300740866),(392,354,31277979186)]⟩,
⟨[7,25,42,76,146,225,308],[[225,258],[66,136,308],[76,146,257],[7,80,264],[25,132,320],[42,384],[],[],[]],[(322,357,36344967696),(392,357,36093170736)]⟩,
⟨[7,25,42,76,146,225,322],[[225,260],[25,36,322],[76,146,288],[7,48,264],[42,132,272],[20,136,257],[80,384],[],[]],[(52,323,36344967696),(276,345,28008649536),(292,332,23690937126),(304,354,32285011986),(308,357,36344967696),(388,354,1116168981),(392,358,36344967696)]⟩,
⟨[7,25,42,76,146,225,336],[[20,225,264],[7,136,336],[76,146,288],[25,36,66,384],[42,260],[48,132,258],[257],[],[]],[(52,323,36344767296),(292,353,32300740866),(388,359,36344967696),(392,354,612570981)]⟩,
⟨[7,25,42,76,146,276,480],[[7,480],[42,129,276],[76,146,257],[25,36,66],[48,65,136,258],[33,80,132,264],[],[],[]],[]⟩,
⟨[7,25,42,76,146,276,481],[[481],[42,276],[76,146],[7,80,136],[25,36,258],[48,66,132,264],[],[],[]],[]⟩,
⟨[7,25,42,76,146,289,448],[[7,48,448],[76,146,289],[42,80,129,260],[25,96,132,258],[20,65,160,264],[36,66,136,272],[],[],[]],[(52,324,36344967696),(112,346,32246871636),(164,346,30737322036),(276,346,10609578051)]⟩
]
private def data9Part17 : Array E19Cert.Row := #[
⟨[7,25,42,76,146,292,448],[[25,448],[65,146,292],[42,80,132,257],[33,76,272],[7,48,136],[20,96,129,258],[66,160,264],[],[]],[(97,326,32300740866),(112,348,32213447766),(161,331,31273063971)]⟩,
⟨[7,25,42,76,146,292,449],[[20,42,449],[33,76,146],[25,66,292],[7,80,160,264],[48,132,258],[96,136,272],[],[],[]],[(112,350,36344967696)]⟩,
⟨[7,25,42,76,146,308,448],[[65,136,308],[42,448],[33,76,146],[7,96,264],[80,129,258],[25,66,160],[132,257],[],[]],[(97,333,36327272706),(161,333,35823617586)]⟩,
⟨[7,25,42,76,146,308,449],[[42,449],[66,136,308],[33,76,146],[7,80,160,264],[25,96,132,258],[],[],[],[]],[]⟩,
⟨[7,25,42,76,146,322,392],[[7,48,392],[25,36,322],[33,76,146],[20,42,192,257],[65,132,288],[80,160,260],[96,129,272],[],[]],[(52,327,36339720981),(97,327,32279766291),(112,343,27145619511),(161,327,26709665556),(164,343,35014459701),(193,339,27171176481),(224,327,22599378456),(225,358,36344967696),(276,339,23211491616),(289,343,10838558001),(292,327,14579934231),(304,327,18639693846),(308,358,32285011986)]⟩,
⟨[7,25,42,76,146,322,416],[[7,80,416],[33,76,146],[25,36,322],[20,42,192,257],[48,65,136,260],[96,129,272],[132,264],[],[]],[(52,325,36087993381),(97,325,27968083236),(112,330,22567479351),(193,344,31432515651),(276,344,23463011136)]⟩,
⟨[7,25,42,76,146,322,417],[[76,417],[25,132,322],[96,146,260],[7,48,192,264],[20,42,65],[36,80,136],[272],[],[]],[(52,328,36344967696),(112,345,36272420421),(276,345,23463011136)]⟩,
⟨[7,25,42,76,146,336,388],[[42,65,388],[7,160,336],[25,36,192,258],[33,76,146],[20,66,129,288],[96,136,257],[48,264],[],[]],[(52,327,36087939381),(97,334,36327272706),(161,334,35823617586),(193,341,30425637891),(224,356,36344967696),(225,359,36344967696),(289,351,28037157891)]⟩,
⟨[7,25,42,76,146,336,416],[[76,416],[7,136,336],[96,146,257],[25,36,192,258],[42,65,132],[48,66,129,260],[20,33,264],[],[]],[(52,325,36087939381),(97,334,32213709906),(193,348,30140356131)]⟩,
⟨[7,25,42,76,146,336,417],[[20,66,417],[42,132,336],[76,146],[25,96,260],[7,48,192,264],[36,65,136,258],[],[],[]],[(52,328,36344767296)]⟩,
⟨[7,25,42,76,146,336,420],[[65,420],[42,129,336],[33,76,146],[7,96,264],[25,192,258],[48,66,136,257],[20],[],[]],[(97,336,36327272706),(193,350,30140356131)]⟩,
⟨[7,25,42,76,176,336,385],[[7,96,136],[42,132,336],[76,176,258],[25,36,66],[20,65,130,288],[18,385],[33,192,260],[264],[]],[(97,329,36255970626),(194,356,36311543826),(292,356,32300740866)]⟩,
⟨[7,25,42,76,176,336,386],[[7,176,264],[33,76,386],[25,96,132],[42,129,336],[18,65,136,260],[36,192,257],[20,66,288],[],[]],[(97,331,36255970626),(193,352,36011577411),(289,348,23222945601),(292,352,4415841576)]⟩,
⟨[7,25,42,76,176,338,385],[[36,136,338],[76,176],[7,96,264],[20,42,385],[25,192,260],[33,132],[65,130,288],[],[]],[(97,332,36255970626),(292,359,32300740866)]⟩,
⟨[7,25,42,76,176,338,388],[[36,129,338],[7,176,264],[42,65,388],[25,192,288],[33,76,130],[20,96,136,257],[],[],[]],[(97,333,36255970626),(193,353,36011577411),(289,353,23489414691)]⟩,
⟨[7,25,42,76,176,338,392],[[33,132,338],[7,96,392],[76,176,257],[25,36,192],[42,129,260],[20,65,130,288],[],[],[]],[(97,332,36306298131),(193,354,36011577411),(289,332,18659485536),(292,354,8727565911)]⟩,
⟨[7,25,42,76,180,338,385],[[65,180,264],[33,136,338],[42,385],[7,96],[25,192,260],[76,130,288],[],[],[]],[(97,337,36327272706)]⟩,
⟨[7,25,42,76,180,338,392],[[65,180],[33,338],[7,96,392],[25,192,288],[42,129,260],[76,130,257],[],[],[]],[(97,337,36324123651),(193,357,36011577411),(289,357,28037157891)]⟩,
⟨[7,25,42,84,164,200,304],[[7,200,304],[25,130,320],[42,84,384],[18,164,257],[12,65,144,258],[33,66,260],[96,129,264],[],[]],[(97,340,36025934961),(146,340,35266044951),(268,343,1696678791),(321,351,10492265856),(322,360,36344967696),(385,360,36092326401),(386,351,8979367176)]⟩,
⟨[7,25,42,84,164,200,353],[[12,18,353],[7,200,272],[25,164,258],[42,84,384],[48,130,260],[66,144,264],[129],[],[]],[(146,342,35810132496),(268,358,23746326816),(274,359,23730536976),(386,359,21861253686),(400,359,21750817926),(402,361,36344967696)]⟩,
⟨[7,25,42,84,164,304,449],[[12,18,449],[7,72,304],[25,66,164],[33,84,130,264],[42,144,260],[96,136,258],[],[],[]],[(146,345,34479563061),(268,345,2267100261)]⟩,
⟨[7,25,42,84,164,322,385],[[25,164,322],[42,84,385],[7,48,192,264],[12,96,130,272],[33,72,144,260],[18,65,136,288],[],[],[]],[(97,347,36324123651),(146,347,35825722416),(200,360,36044809041),(268,347,23730459456),(304,360,28039054641)]⟩,
⟨[7,25,42,84,164,322,392],[[25,164,322],[33,84,392],[7,192,288],[42,65,144,260],[12,96,129,272],[48,72,130,257],[18],[],[]],[(97,346,36324123651),(146,349,30467768886),(193,351,31432269891),(289,346,18911613456),(304,351,4952753736)]⟩,
⟨[7,25,42,84,164,328,402],[[12,33,402],[25,66,164],[7,48,328],[42,84,129],[65,136,288],[96,257],[192,260],[],[]],[(97,350,36324123651),(193,353,35440976211),(289,353,19445126691)]⟩
]
private def data9Part18 : Array E19Cert.Row := #[
⟨[7,25,42,84,164,352,402],[[12,65,402],[25,66,164],[7,136,352],[42,84,257],[48,72,129,260],[33,192,264],[],[],[]],[(193,353,34903192401),(200,359,21495227496),(268,354,23746326816)]⟩,
⟨[7,25,42,84,164,353,402],[[12,353],[72,402],[25,66,164],[42,84,129],[7,48,192,264],[136,260],[],[],[]],[(200,361,36344967696),(268,357,23746326816)]⟩,
⟨[7,25,42,116,193,322,396],[[116,130,257],[18,33,396],[25,160,322],[42,193,272],[7,72,144,288],[],[],[],[]],[(146,357,35004630291),(289,357,10838558001)]⟩,
⟨[7,25,42,52,76,82,97,385],[[42,385],[7,192,264],[25,132,258],[97,144,260],[52,130,320],[76,160,272],[82,136,288],[],[]],[]⟩,
⟨[7,25,42,52,76,82,161,321],[[76,161,258],[52,130,321],[82,384],[25,192,260],[42,132,272],[7,136,288],[96,144,264],[],[]],[(386,362,36344967696),(388,362,32302706976),(392,362,36344828976),(400,362,32302507056)]⟩,
⟨[7,25,42,52,76,82,161,386],[[25,96,386],[76,161,272],[7,136,320],[42,65,144,260],[52,192,257],[82,132,288],[264],[],[]],[(321,362,36344967696),(352,362,36339720981)]⟩,
⟨[7,25,42,52,76,82,161,448],[[25,448],[76,161,258],[52,130,257],[82,132,288],[42,65,144,260],[7,96,264],[136,272],[],[]],[]⟩,
⟨[7,25,42,52,76,82,225,386],[[225,260],[25,386],[7,144,320],[42,132,272],[82,264],[52,136,257],[76,288],[],[]],[]⟩,
⟨[7,25,42,52,76,146,193,289],[[76,146,289],[42,193,272],[7,80,384],[25,66,160,260],[52,136,320],[96,132,258],[264],[],[]],[(322,363,36344967696),(336,363,36344767296),(388,363,36093247776),(392,363,36093170736)]⟩,
⟨[7,25,42,52,76,146,193,322],[[52,193,264],[25,160,322],[42,80,384],[33,76,146],[7,136,288],[96,132,257],[260],[272],[]],[(289,363,36344967696),(388,364,36344967696),(392,365,36344967696),(416,366,36344967696)]⟩,
⟨[7,25,42,52,76,146,193,352],[[146,352],[42,193,260],[76,160,272],[25,66,132],[7,80,384],[52,136,257],[33,258],[264],[]],[(388,366,36093247776),(392,366,36093170736)]⟩,
⟨[7,25,42,52,76,146,225,322],[[225,260],[25,132,322],[76,146,257],[7,80,264],[42,272],[52,384],[136,288],[],[]],[(388,367,36344967696),(392,367,36339720981)]⟩,
⟨[7,25,42,52,76,146,289,448],[[7,448],[76,146,289],[52,65,136,258],[25,66,160,260],[42,80,129],[96,132,272],[264],[],[]],[]⟩,
⟨[7,25,42,52,76,146,321,388],[[42,321],[25,96,388],[33,76,146],[7,80,160,264],[52,192,258],[66,129,288],[136,272],[],[]],[(161,362,36092203041),(224,366,36087939381)]⟩,
⟨[7,25,42,52,76,146,321,416],[[146,321],[76,416],[42,192,260],[25,96,132,258],[52,66,129,264],[7,80,136],[33,272],[],[]],[]⟩,
⟨[7,25,42,52,76,146,322,388],[[25,160,322],[42,65,388],[52,192,257],[33,76,146],[7,96,136,272],[80,129,288],[264],[],[]],[(97,362,32300740866),(161,362,36091219986),(193,364,36344967696),(224,365,36339720981),(225,367,36344967696),(289,363,28038217986)]⟩,
⟨[7,25,42,52,76,146,322,417],[[76,417],[25,132,322],[96,146,260],[7,80,136],[42,192,272],[52,65,264],[],[],[]],[]⟩,
⟨[7,25,42,52,76,193,322,388],[[25,96,388],[42,193,272],[52,136,322],[7,144,288],[18,33,76],[80,130,257],[160,264],[],[]],[(146,364,36344967696),(289,364,32317452801)]⟩,
⟨[7,25,42,52,76,193,322,392],[[52,193],[7,80,392],[25,160,322],[42,144,257],[18,33,76],[96,130,272],[132,288],[260],[]],[(146,365,36344967696),(289,365,32317452801)]⟩,
⟨[7,25,42,52,76,193,322,400],[[42,400],[52,193,264],[25,160,322],[18,33,76],[7,80,136,288],[96,130,260],[132,257],[],[]],[(289,366,32317452801)]⟩,
⟨[7,25,42,52,76,193,338,388],[[33,136,338],[42,193],[25,96,388],[52,130,257],[7,160,264],[76,144,288],[],[],[]],[(289,367,32317452801)]⟩,
⟨[7,25,42,52,76,193,338,416],[[33,132,338],[25,416],[42,193,260],[76,130,257],[7,96,144,264],[52,136],[],[],[]],[]⟩,
⟨[7,25,42,52,76,193,352,386],[[52,386],[42,193,272],[25,132,352],[18,76,160,257],[33,66,144,260],[7,80,136],[264],[],[]],[(82,362,36245226261)]⟩,
⟨[7,25,42,52,76,193,352,388],[[25,66,388],[42,193,272],[7,144,352],[52,130,264],[18,33,76],[80,160,258],[136,257],[],[]],[(82,362,36245348661),(146,366,36093247776),(274,366,28034875701)]⟩
]
private def data9Part19 : Array E19Cert.Row := #[
⟨[7,25,42,52,76,193,352,402],[[33,76,402],[42,193,260],[25,132,352],[7,80,160,264],[52,66,136,257],[],[],[],[]],[]⟩,
⟨[7,25,42,52,76,210,353,388],[[210,264],[136,353],[25,388],[7,160,272],[52,129,258],[76],[42],[],[]],[]⟩,
⟨[7,25,42,76,112,146,164,193],[[7,112,264],[25,164,258],[42,193,260],[76,146,257],[20,66,136,288],[33,320],[272],[384],[]],[(276,368,36344967696),(289,368,36327272706),(322,368,35237818656),(392,368,35489130096)]⟩,
⟨[7,25,42,76,112,146,164,276],[[7,112,384],[25,164,320],[42,65,276],[76,146,257],[66,129,288],[33,136,258],[192,264],[],[]],[(193,368,36344967696),(289,369,36344967696),(321,365,23662362996),(322,369,27700560936),(385,365,22690357506),(392,369,30467768886),(448,365,22079041896),(449,370,36344967696)]⟩,
⟨[7,25,42,76,112,146,164,289],[[76,146,289],[7,112,384],[25,164,320],[42,192,260],[20,65,136,258],[66,129,264],[272],[],[]],[(193,368,36327272706),(276,369,36344967696),(322,371,36344967696),(392,371,36093170736),(448,372,36344967696)]⟩,
⟨[7,25,42,76,112,146,164,321],[[20,42,321],[7,112,384],[25,164,258],[76,146,288],[66,129,264],[33,136,260],[192,272],[],[]],[(276,365,23662362996),(392,372,34478510646)]⟩,
⟨[7,25,42,76,112,146,164,449],[[20,42,449],[7,112,264],[25,164,258],[76,146,288],[33,66,136,272],[260],[],[],[]],[(276,370,36344967696)]⟩,
⟨[7,25,42,76,112,146,276,392],[[7,112,392],[42,65,276],[33,76,146],[25,160,320],[36,192,257],[66,129,288],[132,258],[],[]],[(161,363,35823617586),(164,369,30467768886),(193,371,36011577411),(289,371,28037157891),(321,363,23696835426),(322,369,6182748966)]⟩,
⟨[7,25,42,76,112,146,276,416],[[25,66,416],[42,65,276],[7,112,264],[76,146,257],[33,192,258],[36,129,320],[132],[136],[]],[(193,372,36312526881),(321,366,23696835426),(322,365,9936533016)]⟩,
⟨[7,25,42,76,112,146,276,417],[[76,417],[7,112,264],[42,192,276],[36,65,146],[25,66,132],[136,320],[258],[],[]],[(322,370,32302706976)]⟩,
⟨[7,25,42,76,112,146,289,388],[[112,388],[76,146,289],[7,136,320],[20,42,65],[25,36,192,258],[66,129,264],[160,272],[],[]],[(193,372,36037662501),(322,372,27987547986)]⟩,
⟨[7,25,42,76,112,146,289,392],[[7,112,392],[76,146,289],[25,66,160,260],[20,42,129,320],[65,132,272],[36,192,258],[],[],[]],[(164,371,36093170736),(193,371,34399803201),(276,371,28037157891),(322,371,2184599316)]⟩,
⟨[7,25,42,76,112,146,292,385],[[20,42,385],[33,76,146],[7,112,264],[25,192,258],[65,136,292],[132,320],[66,160,272],[],[]],[(322,366,23675143191)]⟩,
⟨[7,25,42,76,112,146,292,392],[[7,112,392],[76,146,257],[25,192,292],[20,42,129,320],[65,160,258],[33,66,132,272],[],[],[]],[(161,363,35820668451),(193,372,34399803201),(321,372,2168935266),(322,363,19111744776)]⟩,
⟨[7,25,42,76,112,146,292,449],[[20,42,449],[33,76,146],[7,112,136],[25,66,292],[132,258],[160,264],[272],[],[]],[]⟩,
⟨[7,25,42,76,146,224,289,336],[[7,136,336],[76,146,289],[25,224,260],[20,42,65,384],[48,66,132,264],[36,129,258],[],[],[]],[(52,363,32313979476),(388,373,36344967696),(392,372,13155719286)]⟩,
⟨[7,25,42,76,146,224,292,336],[[7,224,264],[25,66,292],[76,146,257],[42,129,336],[20,33,136,258],[48,65,384],[132],[],[]],[(385,374,36344967696),(392,366,8644859256)]⟩,
⟨[7,25,42,76,146,224,308,321],[[66,129,308],[33,76,146],[7,224,264],[42,132,321],[25,384],[80,136,258],[],[],[]],[(392,375,36344967696)]⟩,
⟨[7,25,42,76,146,224,308,322],[[65,136,308],[25,132,322],[7,224,264],[76,146,257],[42,80,129],[33,384],[],[],[]],[(385,375,36093170736),(392,367,22599378456)]⟩,
⟨[7,25,42,76,146,224,321,392],[[7,48,392],[76,146,288],[25,224,260],[20,42,321],[36,66,129,272],[33,80,132,258],[],[],[]],[(52,366,36087993381),(276,366,19151197026),(292,366,14265356406),(304,366,640948311),(308,375,36344967696)]⟩,
⟨[7,25,42,76,146,224,336,388],[[7,224,264],[25,66,288],[20,42,257],[33,76,146],[48,65,388],[36,129,336],[136,258],[],[]],[(52,364,36087939381),(289,373,36344967696)]⟩,
⟨[7,25,42,76,146,225,308,322],[[225,264],[136,308],[25,132,322],[76,146,257],[7,80,384],[42],[],[],[]],[(392,376,36344967696)]⟩,
⟨[7,25,42,76,146,225,322,392],[[20,225],[7,48,392],[25,36,322],[76,146,288],[42,80,260],[132,272],[257],[],[]],[(52,367,36339720981),(276,370,23211491616),(292,367,14579934231),(304,367,18639693846),(308,376,36344967696)]⟩,
⟨[7,25,42,76,146,225,336,388],[[20,225,264],[42,388],[7,136,336],[25,36,258],[76,146,288],[48,66,257],[],[],[]],[(52,367,36087939381)]⟩
]
private def data9Part20 : Array E19Cert.Row := #[
⟨[7,25,42,84,164,200,304,322],[[7,200,304],[25,164,322],[42,65,384],[33,84,130,264],[18,96,129,260],[12,144,257],[],[],[]],[(97,371,36324123651),(146,371,35266044951),(268,371,15038828871),(385,377,36344967696)]⟩,
⟨[7,25,42,84,164,200,353,402],[[12,353],[402],[7,48,264],[25,66,164],[42,84,129],[200,260],[],[],[]],[(268,376,23746326816)]⟩,
⟨[7,25,42,52,76,82,161,321,386],[[25,96,386],[76,161,272],[52,136,321],[7,144,264],[42,132],[82,260],[192,288],[],[]],[]⟩,
⟨[7,25,42,52,76,146,193,289,322],[[52,193,264],[76,146,289],[25,132,322],[42,80,384],[7,96,136,272],[160,260],[],[],[]],[(388,378,36344967696),(392,379,36344967696)]⟩,
⟨[7,25,42,52,76,146,193,322,388],[[25,96,388],[42,193,272],[52,136,322],[33,76,146],[7,80,288],[160,257],[264],[],[]],[(289,378,36344967696)]⟩,
⟨[7,25,42,52,76,146,193,322,392],[[52,193],[7,96,392],[25,160,322],[42,80,132,257],[33,76,146],[288],[260],[272],[]],[(289,379,36344967696)]⟩,
⟨[7,25,42,52,76,146,193,322,416],[[25,416],[52,136,322],[42,193,260],[76,146,257],[7,96,272],[33,80,132,264],[],[],[]],[]⟩,
⟨[7,25,42,52,76,146,225,322,388],[[225,272],[25,322],[42,80,388],[52,264],[76,146,257],[7,136,288],[],[],[]],[]⟩,
⟨[7,25,42,76,112,146,164,193,276],[[42,193,276],[7,112,264],[25,164,258],[76,146,257],[66,136,288],[33,320],[384],[],[]],[(289,380,36344967696),(322,380,35255513601),(392,380,35453739111)]⟩,
⟨[7,25,42,76,112,146,164,276,289],[[76,146,289],[7,112,384],[25,164,320],[42,192,276],[65,136,258],[66,129,264],[],[],[]],[(193,380,36344967696),(322,380,32317452801),(392,380,5238837351),(448,379,9750806646)]⟩,
⟨[7,25,42,76,112,146,164,276,449],[[42,449],[7,112,264],[25,164,258],[76,146,288],[33,66,136,276],[],[],[],[]],[]⟩,
⟨[7,25,42,76,112,146,164,289,322],[[25,164,322],[76,146,289],[7,112,384],[42,129,260],[20,192,264],[65,136,272],[],[],[]],[(193,380,35237818656),(276,380,32317452801),(392,381,36344967696)]⟩,
⟨[7,25,42,76,112,146,164,289,448],[[20,42,448],[76,146,289],[7,112,264],[25,164,258],[65,136,260],[66,129,272],[],[],[]],[(276,379,9750806646)]⟩,
⟨[7,25,42,76,146,224,289,336,388],[[7,136,336],[25,224,258],[20,42,65],[76,146,289],[48,66,388],[36,129,264],[],[],[]],[(52,378,27785252931)]⟩,
⟨[7,25,42,76,146,224,292,336,385],[[7,136,336],[25,66,292],[20,42,385],[33,76,146],[224,258],[48,65,132,264],[],[],[]],[]⟩,
⟨[7,25,42,76,146,224,308,321,392],[[66,129,308],[7,80,392],[33,76,146],[25,224,258],[42,132,321],[],[],[],[]],[]⟩,
⟨[7,25,42,76,146,225,308,322,392],[[225],[308],[7,80,392],[25,132,322],[76,146,257],[42],[],[],[]],[]⟩,
⟨[7,25,42,84,164,200,304,322,385],[[7,96,144,264],[25,164,322],[42,84,385],[12,65,130,304],[18,33,200,260],[],[],[],[]],[(97,381,36057858561),(146,381,35810132496),(268,381,23746326816)]⟩,
⟨[7,25,42,52,76,146,193,289,322,388],[[25,96,388],[42,193,272],[52,136,322],[76,146,289],[7,80,160,264],[],[],[],[]],[]⟩,
⟨[7,25,42,52,76,146,193,289,322,392],[[52,193],[76,146,289],[7,96,392],[25,132,322],[42,80,260],[160,272],[],[],[]],[]⟩,
⟨[7,25,42,76,112,146,164,193,276,289],[[42,193,276],[76,146,289],[7,112,264],[25,164,258],[136,320],[66,384],[],[],[]],[(322,382,36344967696),(392,382,36093170736)]⟩,
⟨[7,25,42,76,112,146,164,289,322,392],[[7,112,392],[25,164,322],[76,146,289],[20,42,65],[129,260],[192,272],[],[],[]],[(193,382,34667455296),(276,382,28037157891)]⟩,
⟨[7,25,42,76,112,146,164,193,276,289,322],[[25,164,322],[42,193,276],[76,146,289],[7,112,136],[264],[384],[],[],[]],[(392,383,36344967696)]⟩,
⟨[7,25,42,76,112,146,164,193,276,289,322,392],[[7,112,392],[25,164,322],[42,193,276],[76,146,289],[],[],[],[],[]],[]⟩
]
private def data9 : Array E19Cert.Row := data9Part0 ++ data9Part1 ++ data9Part2 ++ data9Part3 ++ data9Part4 ++ data9Part5 ++ data9Part6 ++ data9Part7 ++ data9Part8 ++ data9Part9 ++ data9Part10 ++ data9Part11 ++ data9Part12 ++ data9Part13 ++ data9Part14 ++ data9Part15 ++ data9Part16 ++ data9Part17 ++ data9Part18 ++ data9Part19 ++ data9Part20

private def blocks9Part0 : Array (List Nat) := #[[],[7],[15],[31]]
private theorem blocks_eq9Part0 : blocks9Part0 = data9Part0.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part1 : Array (List Nat) := #[[63],[127],[255],[511]]
private theorem blocks_eq9Part1 : blocks9Part1 = data9Part1.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part2 : Array (List Nat) := #[[7,25],[7,56],[7,57],[7,120]]
private theorem blocks_eq9Part2 : blocks9Part2 = data9Part2.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part3 : Array (List Nat) := #[[7,121],[7,248],[7,249],[7,504]]
private theorem blocks_eq9Part3 : blocks9Part3 = data9Part3.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part4 : Array (List Nat) := #[[7,505],[15,113],[15,240],[15,241]]
private theorem blocks_eq9Part4 : blocks9Part4 = data9Part4.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part5 : Array (List Nat) := #[[15,496],[15,497],[31,481],[7,25,42]]
private theorem blocks_eq9Part5 : blocks9Part5 = data9Part5.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part6 : Array (List Nat) := #[[7,25,97],[7,25,98],[7,25,106],[7,25,224],[7,25,225],[7,25,226],[7,25,234],[7,25,480],[7,25,481],[7,25,482],[7,25,490],[7,56,201],[7,56,448],[7,56,449],[7,56,457],[7,57,202],[7,57,449],[7,57,450],[7,57,456],[7,57,458],[15,113,402],[7,25,42,52],[7,25,42,76],[7,25,42,84]]
private theorem blocks_eq9Part6 : blocks9Part6 = data9Part6.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part7 : Array (List Nat) := #[[7,25,42,116],[7,25,42,193],[7,25,42,196],[7,25,42,204],[7,25,42,212],[7,25,42,244],[7,25,42,448],[7,25,42,449],[7,25,42,452],[7,25,42,460],[7,25,42,468],[7,25,42,500],[7,25,97,170],[7,25,97,385],[7,25,97,386],[7,25,97,394],[7,25,97,426],[7,25,98,168],[7,25,98,172],[7,25,98,388],[7,25,98,392],[7,25,98,394],[7,25,98,396],[7,25,98,424]]
private theorem blocks_eq9Part7 : blocks9Part7 = data9Part7.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part8 : Array (List Nat) := #[[7,25,98,428],[7,25,106,180],[7,25,106,396],[7,25,106,404],[7,25,106,416],[7,25,106,417],[7,25,106,420],[7,25,106,436],[7,56,201,338],[7,57,202,340],[7,25,42,52,76],[7,25,42,52,193],[7,25,42,52,204],[7,25,42,52,448],[7,25,42,52,449],[7,25,42,52,460],[7,25,42,76,112],[7,25,42,76,146],[7,25,42,76,176],[7,25,42,76,180],[7,25,42,76,240],[7,25,42,76,385],[7,25,42,76,392],[7,25,42,76,400]]
private theorem blocks_eq9Part8 : blocks9Part8 = data9Part8.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part9 : Array (List Nat) := #[[7,25,42,76,402],[7,25,42,76,432],[7,25,42,76,436],[7,25,42,76,496],[7,25,42,84,164],[7,25,42,84,224],[7,25,42,84,225],[7,25,42,84,385],[7,25,42,84,386],[7,25,42,84,396],[7,25,42,84,416],[7,25,42,84,417],[7,25,42,84,420],[7,25,42,84,480],[7,25,42,84,481],[7,25,42,116,193],[7,25,42,116,385],[7,25,42,116,388],[7,25,42,116,396],[7,25,42,116,448],[7,25,42,116,449],[7,25,42,193,322],[7,25,42,193,324],[7,25,42,193,332]]
private theorem blocks_eq9Part9 : blocks9Part9 = data9Part9.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part10 : Array (List Nat) := #[[7,25,42,193,340],[7,25,42,193,352],[7,25,42,193,356],[7,25,42,193,372],[7,25,42,196,336],[7,25,42,196,338],[7,25,42,196,368],[7,25,42,204,338],[7,25,42,204,368],[7,25,97,170,212],[7,25,97,170,308],[7,25,97,170,340],[7,25,97,170,385],[7,25,97,170,388],[7,25,97,170,404],[7,25,97,170,468],[7,25,98,168,212],[7,25,98,168,308],[7,25,98,168,336],[7,25,98,168,340],[7,25,98,168,468],[7,25,98,172,340],[7,25,98,172,400],[7,25,98,172,402]]
private theorem blocks_eq9Part10 : blocks9Part10 = data9Part10.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part11 : Array (List Nat) := #[[7,25,98,172,464],[7,25,106,180,448],[7,25,106,180,449],[7,56,201,338,420],[7,25,42,52,76,82],[7,25,42,52,76,146],[7,25,42,52,76,193],[7,25,42,52,76,210],[7,25,42,52,76,385],[7,25,42,52,76,388],[7,25,42,52,76,402],[7,25,42,52,76,448],[7,25,42,52,76,449],[7,25,42,52,76,466],[7,25,42,52,193,322],[7,25,42,52,193,332],[7,25,42,52,193,352],[7,25,42,52,204,338],[7,25,42,76,112,146],[7,25,42,76,112,385],[7,25,42,76,112,392],[7,25,42,76,112,402],[7,25,42,76,146,224],[7,25,42,76,146,225]]
private theorem blocks_eq9Part11 : blocks9Part11 = data9Part11.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part12 : Array (List Nat) := #[[7,25,42,76,146,276],[7,25,42,76,146,289],[7,25,42,76,146,292],[7,25,42,76,146,308],[7,25,42,76,146,322],[7,25,42,76,146,336],[7,25,42,76,146,352],[7,25,42,76,146,353],[7,25,42,76,146,368],[7,25,42,76,146,448],[7,25,42,76,146,449],[7,25,42,76,146,480],[7,25,42,76,146,481],[7,25,42,76,176,336],[7,25,42,76,176,338],[7,25,42,76,176,385],[7,25,42,76,176,388],[7,25,42,76,176,392],[7,25,42,76,176,448],[7,25,42,76,176,449],[7,25,42,76,180,338],[7,25,42,76,180,385],[7,25,42,76,180,392],[7,25,42,76,180,448]]
private theorem blocks_eq9Part12 : blocks9Part12 = data9Part12.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part13 : Array (List Nat) := #[[7,25,42,76,180,449],[7,25,42,76,240,385],[7,25,42,76,240,392],[7,25,42,84,164,200],[7,25,42,84,164,304],[7,25,42,84,164,322],[7,25,42,84,164,328],[7,25,42,84,164,352],[7,25,42,84,164,353],[7,25,42,84,164,448],[7,25,42,84,164,449],[7,25,42,84,164,456],[7,25,42,84,224,385],[7,25,42,84,224,386],[7,25,42,84,224,396],[7,25,42,84,225,386],[7,25,42,84,225,396],[7,25,42,116,193,322],[7,25,42,116,193,386],[7,25,42,116,193,388],[7,25,42,116,193,396],[7,25,42,116,193,416],[7,25,42,193,322,432],[7,25,42,193,322,436]]
private theorem blocks_eq9Part13 : blocks9Part13 = data9Part13.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part14 : Array (List Nat) := #[[7,25,42,193,324,432],[7,25,42,193,332,402],[7,25,42,193,332,416],[7,25,42,193,332,432],[7,25,42,193,340,416],[7,25,42,196,336,416],[7,25,42,196,336,417],[7,25,42,196,338,417],[7,25,42,204,338,417],[7,25,97,170,212,385],[7,25,97,170,308,448],[7,25,97,170,340,385],[7,25,98,168,308,449],[7,25,98,168,336,388],[7,25,42,52,76,82,97],[7,25,42,52,76,82,161],[7,25,42,52,76,82,225],[7,25,42,52,76,82,385],[7,25,42,52,76,82,386],[7,25,42,52,76,82,417],[7,25,42,52,76,82,481],[7,25,42,52,76,146,193],[7,25,42,52,76,146,225],[7,25,42,52,76,146,289]]
private theorem blocks_eq9Part14 : blocks9Part14 = data9Part14.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part15 : Array (List Nat) := #[[7,25,42,52,76,146,321],[7,25,42,52,76,146,322],[7,25,42,52,76,146,353],[7,25,42,52,76,146,448],[7,25,42,52,76,146,449],[7,25,42,52,76,146,481],[7,25,42,52,76,193,322],[7,25,42,52,76,193,338],[7,25,42,52,76,193,352],[7,25,42,52,76,193,386],[7,25,42,52,76,193,388],[7,25,42,52,76,193,402],[7,25,42,52,76,193,416],[7,25,42,52,76,210,353],[7,25,42,52,76,210,385],[7,25,42,52,76,210,388],[7,25,42,52,76,210,417],[7,25,42,52,193,322,388],[7,25,42,52,193,322,392],[7,25,42,52,193,322,396],[7,25,42,52,193,322,400],[7,25,42,52,193,332,402],[7,25,42,52,193,332,416],[7,25,42,52,204,338,417]]
private theorem blocks_eq9Part15 : blocks9Part15 = data9Part15.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part16 : Array (List Nat) := #[[7,25,42,76,112,146,164],[7,25,42,76,112,146,276],[7,25,42,76,112,146,289],[7,25,42,76,112,146,292],[7,25,42,76,112,146,385],[7,25,42,76,112,146,388],[7,25,42,76,112,146,392],[7,25,42,76,112,146,417],[7,25,42,76,112,146,420],[7,25,42,76,146,224,276],[7,25,42,76,146,224,289],[7,25,42,76,146,224,292],[7,25,42,76,146,224,308],[7,25,42,76,146,224,321],[7,25,42,76,146,224,322],[7,25,42,76,146,224,336],[7,25,42,76,146,225,276],[7,25,42,76,146,225,292],[7,25,42,76,146,225,308],[7,25,42,76,146,225,322],[7,25,42,76,146,225,336],[7,25,42,76,146,276,480],[7,25,42,76,146,276,481],[7,25,42,76,146,289,448]]
private theorem blocks_eq9Part16 : blocks9Part16 = data9Part16.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part17 : Array (List Nat) := #[[7,25,42,76,146,292,448],[7,25,42,76,146,292,449],[7,25,42,76,146,308,448],[7,25,42,76,146,308,449],[7,25,42,76,146,322,392],[7,25,42,76,146,322,416],[7,25,42,76,146,322,417],[7,25,42,76,146,336,388],[7,25,42,76,146,336,416],[7,25,42,76,146,336,417],[7,25,42,76,146,336,420],[7,25,42,76,176,336,385],[7,25,42,76,176,336,386],[7,25,42,76,176,338,385],[7,25,42,76,176,338,388],[7,25,42,76,176,338,392],[7,25,42,76,180,338,385],[7,25,42,76,180,338,392],[7,25,42,84,164,200,304],[7,25,42,84,164,200,353],[7,25,42,84,164,304,449],[7,25,42,84,164,322,385],[7,25,42,84,164,322,392],[7,25,42,84,164,328,402]]
private theorem blocks_eq9Part17 : blocks9Part17 = data9Part17.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part18 : Array (List Nat) := #[[7,25,42,84,164,352,402],[7,25,42,84,164,353,402],[7,25,42,116,193,322,396],[7,25,42,52,76,82,97,385],[7,25,42,52,76,82,161,321],[7,25,42,52,76,82,161,386],[7,25,42,52,76,82,161,448],[7,25,42,52,76,82,225,386],[7,25,42,52,76,146,193,289],[7,25,42,52,76,146,193,322],[7,25,42,52,76,146,193,352],[7,25,42,52,76,146,225,322],[7,25,42,52,76,146,289,448],[7,25,42,52,76,146,321,388],[7,25,42,52,76,146,321,416],[7,25,42,52,76,146,322,388],[7,25,42,52,76,146,322,417],[7,25,42,52,76,193,322,388],[7,25,42,52,76,193,322,392],[7,25,42,52,76,193,322,400],[7,25,42,52,76,193,338,388],[7,25,42,52,76,193,338,416],[7,25,42,52,76,193,352,386],[7,25,42,52,76,193,352,388]]
private theorem blocks_eq9Part18 : blocks9Part18 = data9Part18.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part19 : Array (List Nat) := #[[7,25,42,52,76,193,352,402],[7,25,42,52,76,210,353,388],[7,25,42,76,112,146,164,193],[7,25,42,76,112,146,164,276],[7,25,42,76,112,146,164,289],[7,25,42,76,112,146,164,321],[7,25,42,76,112,146,164,449],[7,25,42,76,112,146,276,392],[7,25,42,76,112,146,276,416],[7,25,42,76,112,146,276,417],[7,25,42,76,112,146,289,388],[7,25,42,76,112,146,289,392],[7,25,42,76,112,146,292,385],[7,25,42,76,112,146,292,392],[7,25,42,76,112,146,292,449],[7,25,42,76,146,224,289,336],[7,25,42,76,146,224,292,336],[7,25,42,76,146,224,308,321],[7,25,42,76,146,224,308,322],[7,25,42,76,146,224,321,392],[7,25,42,76,146,224,336,388],[7,25,42,76,146,225,308,322],[7,25,42,76,146,225,322,392],[7,25,42,76,146,225,336,388]]
private theorem blocks_eq9Part19 : blocks9Part19 = data9Part19.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9Part20 : Array (List Nat) := #[[7,25,42,84,164,200,304,322],[7,25,42,84,164,200,353,402],[7,25,42,52,76,82,161,321,386],[7,25,42,52,76,146,193,289,322],[7,25,42,52,76,146,193,322,388],[7,25,42,52,76,146,193,322,392],[7,25,42,52,76,146,193,322,416],[7,25,42,52,76,146,225,322,388],[7,25,42,76,112,146,164,193,276],[7,25,42,76,112,146,164,276,289],[7,25,42,76,112,146,164,276,449],[7,25,42,76,112,146,164,289,322],[7,25,42,76,112,146,164,289,448],[7,25,42,76,146,224,289,336,388],[7,25,42,76,146,224,292,336,385],[7,25,42,76,146,224,308,321,392],[7,25,42,76,146,225,308,322,392],[7,25,42,84,164,200,304,322,385],[7,25,42,52,76,146,193,289,322,388],[7,25,42,52,76,146,193,289,322,392],[7,25,42,76,112,146,164,193,276,289],[7,25,42,76,112,146,164,289,322,392],[7,25,42,76,112,146,164,193,276,289,322],[7,25,42,76,112,146,164,193,276,289,322,392]]
private theorem blocks_eq9Part20 : blocks9Part20 = data9Part20.map E19Cert.Row.blocks := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  rfl
private def blocks9 : Array (List Nat) := blocks9Part0 ++ blocks9Part1 ++ blocks9Part2 ++ blocks9Part3 ++ blocks9Part4 ++ blocks9Part5 ++ blocks9Part6 ++ blocks9Part7 ++ blocks9Part8 ++ blocks9Part9 ++ blocks9Part10 ++ blocks9Part11 ++ blocks9Part12 ++ blocks9Part13 ++ blocks9Part14 ++ blocks9Part15 ++ blocks9Part16 ++ blocks9Part17 ++ blocks9Part18 ++ blocks9Part19 ++ blocks9Part20
private theorem blocks_eq9 : blocks9 = data9.map E19Cert.Row.blocks := by
  simp only [blocks9, data9, Array.map_append, blocks_eq9Part0, blocks_eq9Part1, blocks_eq9Part2, blocks_eq9Part3, blocks_eq9Part4, blocks_eq9Part5, blocks_eq9Part6, blocks_eq9Part7, blocks_eq9Part8, blocks_eq9Part9, blocks_eq9Part10, blocks_eq9Part11, blocks_eq9Part12, blocks_eq9Part13, blocks_eq9Part14, blocks_eq9Part15, blocks_eq9Part16, blocks_eq9Part17, blocks_eq9Part18, blocks_eq9Part19, blocks_eq9Part20]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part0 : data9Part0.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part1 : data9Part1.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part2 : data9Part2.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part3 : data9Part3.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part4 : data9Part4.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part5 : data9Part5.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part6 : data9Part6.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part7 : data9Part7.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part8 : data9Part8.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part9 : data9Part9.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part10 : data9Part10.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part11 : data9Part11.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part12 : data9Part12.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part13 : data9Part13.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part14 : data9Part14.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part15 : data9Part15.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part16 : data9Part16.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part17 : data9Part17.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part18 : data9Part18.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part19 : data9Part19.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
private theorem quick_checked9Part20 : data9Part20.all (E19Cert.quick 9 blocks9) = true := by
  decide +kernel
private theorem quick_checked9 : data9.all (E19Cert.quick 9 blocks9) = true := by
  simp only [data9, Array.all_append, quick_checked9Part0, quick_checked9Part1, quick_checked9Part2, quick_checked9Part3, quick_checked9Part4, quick_checked9Part5, quick_checked9Part6, quick_checked9Part7, quick_checked9Part8, quick_checked9Part9, quick_checked9Part10, quick_checked9Part11, quick_checked9Part12, quick_checked9Part13, quick_checked9Part14, quick_checked9Part15, quick_checked9Part16, quick_checked9Part17, quick_checked9Part18, quick_checked9Part19, quick_checked9Part20, Bool.true_and]

private theorem checked4 : E19Cert.certified 4 data4 = true :=
  E19Cert.certified_of_quick 4 data4 blocks4 blocks_eq4 quick_checked4

private theorem checked5 : E19Cert.certified 5 data5 = true :=
  E19Cert.certified_of_quick 5 data5 blocks5 blocks_eq5 quick_checked5

private theorem checked6 : E19Cert.certified 6 data6 = true :=
  E19Cert.certified_of_quick 6 data6 blocks6 blocks_eq6 quick_checked6

private theorem checked7 : E19Cert.certified 7 data7 = true :=
  E19Cert.certified_of_quick 7 data7 blocks7 blocks_eq7 quick_checked7

private theorem checked8 : E19Cert.certified 8 data8 = true :=
  E19Cert.certified_of_quick 8 data8 blocks8 blocks_eq8 quick_checked8

private theorem checked9 : E19Cert.certified 9 data9 = true :=
  E19Cert.certified_of_quick 9 data9 blocks9 blocks_eq9 quick_checked9

set_option maxRecDepth 16000 in
set_option maxHeartbeats 32000000 in
theorem OMA.solution : type_of% @Erdos19.erdos_19.variants.lt_ten := by
  intro V n C hn
  by_cases small : n ≤ 3
  · exact Erdos19.erdos_19.variants.le_three C small
  have lo : 4 ≤ n := by omega
  interval_cases n
  · exact E19Cert.solve (n := 4) (by decide) data4 ⟨0,by decide⟩ rfl checked4 C
  · exact E19Cert.solve (n := 5) (by decide) data5 ⟨0,by decide⟩ rfl checked5 C
  · exact E19Cert.solve (n := 6) (by decide) data6 ⟨0,by decide⟩ rfl checked6 C
  · exact E19Cert.solve (n := 7) (by decide) data7 ⟨0,by decide⟩ rfl checked7 C
  · exact E19Cert.solve (n := 8) (by decide) data8 ⟨0,by decide⟩ rfl checked8 C
  · exact E19Cert.solve (n := 9) (by decide) data9 ⟨0,by decide⟩ rfl checked9 C
