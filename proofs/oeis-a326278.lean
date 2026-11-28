import OMAStatements.S_oeis_a326278

open OMA.S_oeis_a326278 Finset

private theorem card_by_order {α : Type} (S : Finset α) (n k : ℕ)
    (decode : α → Fin k → ℕ) (encode : (Fin k → ℕ) → α)
    (hmem : ∀ q, q ∈ S ↔ StrictMono (decode q) ∧ ∀ i, decode q i < n)
    (hdec : ∀ f, decode (encode f) = f) (henc : ∀ q, encode (decode q) = q) :
    S.card = n.choose k := by
  classical
  let vertices (q : α) : Finset ℕ := univ.image (decode q)
  have hcard (q : α) (hq : q ∈ S) : (vertices q).card = k := by
    dsimp only [vertices]
    rw [card_image_of_injective _ ((hmem q).mp hq).1.injective]
    simp
  have hsorted (q : α) (hq : q ∈ S) :
      decode q = (vertices q).orderEmbOfFin (hcard q hq) :=
    orderEmbOfFin_unique _ (fun i => mem_image_of_mem _ (mem_univ i)) ((hmem q).mp hq).1
  rw [← card_range n, ← card_powersetCard]
  apply card_bij (fun q _ => vertices q)
  · intro q hq
    refine mem_powersetCard.mpr ⟨?_, hcard q hq⟩
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact mem_range.mpr (((hmem q).mp hq).2 i)
  · intro a ha b hb hab
    have he : decode a = decode b := by
      rw [← ((hmem a).mp ha).1.range_inj ((hmem b).mp hb).1]
      rw [hsorted a ha, hsorted b hb]
      simp only [range_orderEmbOfFin, hab]
    rw [← henc a, ← henc b, he]
  · intro u hu
    obtain ⟨hsub,hk⟩ := mem_powersetCard.mp hu
    let f := u.orderEmbOfFin hk
    have hq : encode f ∈ S := by
      rw [hmem, hdec]
      exact ⟨f.strictMono, fun i => mem_range.mp (hsub (orderEmbOfFin_mem _ _ _))⟩
    refine ⟨encode f,hq,?_⟩
    simp only [vertices, hdec, f, image_orderEmbOfFin_univ]

private def pairSeq (p : ℕ × ℕ) : Fin 2 → ℕ := ![p.1,p.2]

private theorem mono_pair (f : Fin 2 → ℕ) : StrictMono f ↔ f 0 < f 1 := by
  constructor
  · exact fun h => h (by decide)
  · intro h
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    exact h

private def edgeSet (n : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter (fun p => p.1 < p.2)

private theorem card_edges (n : ℕ) : (edgeSet n).card = n.choose 2 := by
  refine card_by_order (edgeSet n) n 2 pairSeq (fun f => (f 0,f 1)) ?_ ?_ ?_
  · intro p
    simp only [edgeSet, mem_filter, mem_product, mem_range, mono_pair, pairSeq]
    constructor
    · rintro ⟨⟨ha,hb⟩,hab⟩
      refine ⟨hab,fun i => ?_⟩
      fin_cases i
      · exact ha
      · exact hb
    · rintro ⟨hab,h⟩
      exact ⟨⟨h 0,h 1⟩,hab⟩
  · intro f
    funext i
    fin_cases i <;> rfl
  · intro p
    rfl

private abbrev Quad := ℕ × ℕ × ℕ × ℕ

private def edges (n : ℕ) : Finset Quad :=
  (range n ×ˢ range n ×ˢ range n ×ˢ range n).filter
    (fun q : Quad => q.1 < q.2.1 ∧ q.2.2.1 < q.2.2.2)

private theorem edges_mem (n : ℕ) (q : Quad) :
    q ∈ edges n ↔
      q.1 < n ∧ q.2.1 < n ∧ q.2.2.1 < n ∧ q.2.2.2 < n ∧
      q.1 < q.2.1 ∧ q.2.2.1 < q.2.2.2 := by
  simp only [edges, mem_filter, mem_product, mem_range]
  tauto

private theorem card_all (n : ℕ) : (edges n).card = (n.choose 2)^2 := by
  rw [pow_two, ← card_edges, ← card_product]
  refine card_bij' (fun q _ => ((q.1,q.2.1),(q.2.2.1,q.2.2.2)))
    (fun p _ => (p.1.1,p.1.2,p.2.1,p.2.2)) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [edgeSet, mem_filter, mem_product, mem_range]
    exact (by have := (edges_mem n q).1 hq; tauto)
  · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ hp
    simp only [edgeSet, mem_filter, mem_product, mem_range] at hp
    exact (edges_mem n (a,b,c,d)).2 (by tauto)
  · intro q _
    rfl
  · intro p _
    rfl

private def flipEdges (q : Quad) : Quad := (q.2.2.1,q.2.2.2,q.1,q.2.1)

private theorem flipEdges_involutive (q : Quad) : flipEdges (flipEdges q) = q := rfl

private theorem flip_mem (n : ℕ) (q : Quad) : flipEdges q ∈ edges n ↔ q ∈ edges n := by
  simp only [edges_mem, flipEdges]
  tauto

private def firstBad (nest : Bool) (q : Quad) : Prop :=
  q.1 < q.2.2.1 ∧
    if nest then q.2.2.1 < q.2.2.2 ∧ q.2.2.2 < q.2.1
    else q.2.2.1 < q.2.1 ∧ q.2.1 < q.2.2.2

private instance (nest : Bool) (q : Quad) : Decidable (firstBad nest q) := by
  cases nest <;> unfold firstBad <;> infer_instance

private def quadSeq (nest : Bool) (q : Quad) : Fin 4 → ℕ :=
  if nest then ![q.1,q.2.2.1,q.2.2.2,q.2.1] else ![q.1,q.2.2.1,q.2.1,q.2.2.2]

private def quadFrom (nest : Bool) (f : Fin 4 → ℕ) : Quad :=
  if nest then (f 0,f 3,f 1,f 2) else (f 0,f 2,f 1,f 3)

private theorem card_first (n : ℕ) (nest : Bool) :
    ((edges n).filter (firstBad nest)).card = n.choose 4 := by
  refine card_by_order _ n 4 (quadSeq nest) (quadFrom nest) ?_ ?_ ?_
  · intro q
    have hbound (f : Fin 4 → ℕ) : (∀ i, f i < n) ↔
        f 0 < n ∧ f 1 < n ∧ f 2 < n ∧ f 3 < n := by
      constructor
      · exact fun h => ⟨h 0,h 1,h 2,h 3⟩
      · rintro ⟨h₁,h₂,h₃,h₄⟩ i
        fin_cases i
        · exact h₁
        · exact h₂
        · exact h₃
        · exact h₄
    cases nest <;>
      simp [edges_mem, firstBad, hbound, quadSeq] <;>
      omega
  · intro f
    funext i
    cases nest <;> fin_cases i <;> rfl
  · intro q
    cases nest <;> rfl

private theorem card_second (n : ℕ) (nest : Bool) :
    ((edges n).filter (fun q => firstBad nest (flipEdges q))).card = n.choose 4 := by
  rw [← card_first n nest]
  refine card_bij' (fun q _ => flipEdges q) (fun q _ => flipEdges q) ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_filter] at hq
    exact mem_filter.mpr ⟨(flip_mem _ _).2 hq.1, hq.2⟩
  · intro q hq
    rw [mem_filter] at hq ⊢
    exact ⟨(flip_mem _ _).2 hq.1, by rw [flipEdges_involutive]; exact hq.2⟩
  · exact fun q _ => flipEdges_involutive q
  · exact fun q _ => flipEdges_involutive q

private def goodCount (n : ℕ) (nest : Bool) : ℕ :=
  ((edges n).filter (fun q => ¬firstBad nest q ∧ ¬firstBad nest (flipEdges q))).card

private theorem split_count (n : ℕ) (nest : Bool) :
    goodCount n nest + 2 * n.choose 4 = (n.choose 2)^2 := by
  classical
  have hd : Disjoint ((edges n).filter (firstBad nest))
      ((edges n).filter (fun q => firstBad nest (flipEdges q))) := by
    rw [disjoint_left]
    intro q hq hq'
    have h := (mem_filter.mp hq).2.1
    have h' := (mem_filter.mp hq').2.1
    change q.2.2.1 < q.1 at h'
    exact (not_lt_of_ge h.le) h'
  have hunion : (edges n).filter (fun q => firstBad nest q ∨ firstBad nest (flipEdges q)) =
      (edges n).filter (firstBad nest) ∪ (edges n).filter (fun q => firstBad nest (flipEdges q)) := by
    ext q
    simp only [mem_filter, mem_union]
    tauto
  have h := card_filter_add_card_filter_not (s := edges n)
    (p := fun q => firstBad nest q ∨ firstBad nest (flipEdges q))
  rw [hunion, card_union_of_disjoint hd, card_first, card_second, card_all] at h
  simpa only [goodCount, not_or, two_mul, add_comm] using h

private theorem count_nesting (n : ℕ) : notNesting n = goodCount n true := by
  unfold notNesting goodCount edges
  congr 1
  ext q
  simp only [mem_filter, firstBad, flipEdges, if_true]
  tauto

private theorem count_crossing (n : ℕ) : notCrossing n = goodCount n false := by
  unfold notCrossing goodCount edges
  congr 1
  ext q
  simp only [mem_filter, firstBad, flipEdges, Bool.false_eq_true, if_false]
  tauto

private theorem nesting_formula (n : ℕ) :
    6 * notNesting n + 4 * n^2 = n*(n^3+3) := by
  by_cases hn : 4 ≤ n
  · have hc : (notNesting n : ℚ) + 2*(n.choose 4 : ℚ) = (n.choose 2 : ℚ)^2 := by
      rw [count_nesting]
      exact_mod_cast split_count n true
    have h₂ : 2*(n.choose 2 : ℚ) = (n:ℚ)*((n:ℚ)-1) := by
      have h := Nat.descFactorial_eq_factorial_mul_choose n 2
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one] at h
      have h' : ((n-1 : ℕ) : ℚ)*(n:ℚ) = 2*(n.choose 2 : ℚ) := by exact_mod_cast h
      rw [Nat.cast_sub (by omega)] at h'
      linear_combination -h'
    have h₄ : 24*(n.choose 4 : ℚ) = (n:ℚ)*((n:ℚ)-1)*((n:ℚ)-2)*((n:ℚ)-3) := by
      have h := Nat.descFactorial_eq_factorial_mul_choose n 4
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one] at h
      have h' : ((n-3 : ℕ) : ℚ)*(((n-2 : ℕ) : ℚ)*(((n-1 : ℕ) : ℚ)*(n:ℚ))) =
          24*(n.choose 4 : ℚ) := by exact_mod_cast h
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at h'
      linear_combination -h'
    have hs := congrArg (fun t : ℚ => t^2) h₂
    have hf : (6:ℚ)*(notNesting n : ℚ) + 4*(n:ℚ)^2 = (n:ℚ)*((n:ℚ)^3+3) := by
      linear_combination 6*hc + (3/2 : ℚ)*hs - (1/2 : ℚ)*h₄
    exact_mod_cast hf
  · interval_cases n <;> decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a326278.main := by
  refine ⟨nesting_formula, ?_, ?_⟩
  · intro n
    rw [count_crossing, count_nesting]
    have h₁ := split_count n true
    have h₂ := split_count n false
    omega
  · intro n hn
    have h (k : ℕ) : 6 * (notNesting k : ℤ) + 4*(k:ℤ)^2 = (k:ℤ)*((k:ℤ)^3+3) :=
      by exact_mod_cast nesting_formula k
    have h₀ := h n
    have h₁ := h (n-1)
    have h₂ := h (n-2)
    have h₃ := h (n-3)
    have h₄ := h (n-4)
    have h₅ := h (n-5)
    simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
      Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n),
      Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_ofNat, Nat.cast_one] at h₁ h₂ h₃ h₄ h₅
    apply mul_left_cancel₀ (show (6:ℤ) ≠ 0 by decide)
    linear_combination h₀ - 5*h₁ + 10*h₂ - 10*h₃ + 5*h₄ - h₅