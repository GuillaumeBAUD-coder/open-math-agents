import FormalConjectures.ErdosProblems.«19»

-- Reduction Erdos19.erdos_19.variants.kahn.R1 of Erdős Problem 19 — kahn
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Dualise EFL to a linear family on Fin n (supports of shared vertices); colour supports of rank
-- > 2q^2 greedily in descending rank (n + n/q colours), list-colour rank <= 2q avoiding those
-- colours (H1), and give ranks in (2q, 2q^2] their own palette of about n/q colours (H2).

open Filter

namespace OMA.R_Erdos19_erdos_19_variants_kahn_R1

open Erdos19 Erdos19.EFLConfig

/-- Asymptotic list edge-colouring of linear hypergraphs of rank at most 2q with lists of
size D + D/q, D the maximum degree (Kahn 1996, codegree one, bounded rank). -/
def H1 : Prop :=
  ∀ q : ℕ, 0 < q → ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
    ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ 2 * q) →
      (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) → (∀ A ∈ H, D + D / q ≤ (L A).card) →
      ∃ c : Finset (Fin n) → Fin m,
        (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A

/-- Bounded-rank linear hypergraphs of large maximum degree D have chromatic index at most 2D. -/
def H2 : Prop :=
  ∀ r : ℕ, ∃ D₀ : ℕ, ∀ n D : ℕ, D₀ ≤ D → ∀ H : Finset (Finset (Fin n)),
    (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r) →
    (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) →
    ∃ c : Finset (Fin n) → Fin (2 * D),
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B

open scoped Classical in
/-- generalisation of colorable_of_sharedColoring to m >= n colours -/
theorem colorable_of_sharedColoring_le {V : Type*} {n : ℕ} (C : EFLConfig V n) (m : ℕ)
    (hm : n ≤ m) (c : V → Fin m)
    (hc : ∀ i u v, u ∈ C.A i → v ∈ C.A i → C.IsShared u → C.IsShared v → c u = c v → u = v) :
    C.graph.Colorable m := by
  let P : Fin n → Finset V := fun i => (C.A i).filter (fun v => ¬ C.IsShared v)
  let U : Fin n → Finset V := fun i => (C.A i).filter C.IsShared
  let F : Fin n → Finset (Fin m) := fun i => Finset.univ \ (U i).image c
  have hcard : ∀ i, (P i).card ≤ (F i).card := by
    intro i
    have h1 : (U i).card + (P i).card = n := by
      rw [← C.card_eq i]; exact Finset.card_filter_add_card_filter_not _
    have h2 : ((U i).image c).card ≤ (U i).card := Finset.card_image_le
    have h3 : (F i).card = m - ((U i).image c).card := by
      simp [F, Finset.card_sdiff]
    omega
  have hne : ∀ i, Nonempty (P i ↪ F i) := fun i =>
    Function.Embedding.nonempty_of_card_le (by simpa using hcard i)
  let e : ∀ i, P i ↪ F i := fun i => Classical.choice (hne i)
  let idx : V → Fin n := fun v => Classical.choose (C.cover v)
  have hidx : ∀ v, v ∈ C.A (idx v) := fun v => Classical.choose_spec (C.cover v)
  let col : V → Fin m := fun v =>
    if h : C.IsShared v then c v
    else ((e (idx v) ⟨v, Finset.mem_filter.2 ⟨hidx v, h⟩⟩ : F (idx v)) : Fin m)
  have col_priv : ∀ v (hv : ¬ C.IsShared v) j (hj : v ∈ C.A j),
      col v = ((e j ⟨v, Finset.mem_filter.2 ⟨hj, hv⟩⟩ : F j) : Fin m) := by
    intro v hv j hj
    have key : ∀ i (hi : i = j) (p : v ∈ P i), ((e i ⟨v, p⟩ : F i) : Fin m) =
        ((e j ⟨v, Finset.mem_filter.2 ⟨hj, hv⟩⟩ : F j) : Fin m) := by
      rintro i rfl p; rfl
    simp only [col, dif_neg hv]
    exact key _ (C.eq_of_not_shared hv (hidx v) hj) _
  have col_free : ∀ v (hv : ¬ C.IsShared v) j (hj : v ∈ C.A j), col v ∈ F j := by
    intro v hv j hj
    rw [col_priv v hv j hj]; exact Subtype.property _
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  rintro u v ⟨huv, j, hu, hv⟩ heq
  by_cases su : C.IsShared u <;> by_cases sv : C.IsShared v
  · have : col u = c u := dif_pos su
    have : col v = c v := dif_pos sv
    exact huv (hc j u v hu hv su sv (by simp_all))
  · have h1 := col_free v sv j hv
    have : col u = c u := dif_pos su
    simp only [F, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image] at h1
    exact h1 ⟨u, Finset.mem_filter.2 ⟨hu, su⟩, by rw [← this, heq]⟩
  · have h1 := col_free u su j hu
    have : col v = c v := dif_pos sv
    simp only [F, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image] at h1
    exact h1 ⟨v, Finset.mem_filter.2 ⟨hv, sv⟩, by rw [← this, ← heq]⟩
  · rw [col_priv u su j hu, col_priv v sv j hv] at heq
    have := (e j).injective (Subtype.ext heq)
    exact huv (congrArg Subtype.val this)

theorem le_floor_mul (ε : ℝ) (hε : 0 < ε) (n : ℕ) : n ≤ ⌊(1 + ε) * n⌋₊ := by
  apply Nat.le_floor
  have : (0 : ℝ) ≤ ε * n := by positivity
  nlinarith

open Finset
open scoped BigOperators

theorem linear_mono {n : ℕ} {H K : Finset (Finset (Fin n))}
    (h : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hKH : K ⊆ H) : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1 :=
  fun A hA B hB => h A (hKH hA) B (hKH hB)

theorem incident_mul_le {n : ℕ} {H : Finset (Finset (Fin n))} (h : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (r : ℕ) (hr : ∀ A ∈ H, r + 1 ≤ A.card) (i : Fin n) :
    r * (H.filter (fun A => i ∈ A)).card ≤ n := by
  let K := H.filter (fun A => i ∈ A)
  have hd : (K : Set (Finset (Fin n))).PairwiseDisjoint (fun A => A.erase i) := by
    intro A hA B hB hAB
    obtain ⟨hA', hiA⟩ := mem_filter.mp hA
    obtain ⟨hB', hiB⟩ := mem_filter.mp hB
    apply Finset.disjoint_left.mpr
    intro j hjA hjB
    have hji := (Finset.mem_erase.mp hjA).1
    exact hji (Finset.card_le_one.mp (h A hA' B hB' hAB) j
      (mem_inter.mpr ⟨mem_of_mem_erase hjA, mem_of_mem_erase hjB⟩)
      i (mem_inter.mpr ⟨hiA, hiB⟩))
  calc
    r * K.card = ∑ _A ∈ K, r := by simp [Nat.mul_comm]
    _ ≤ ∑ A ∈ K, (A.erase i).card := by
      apply Finset.sum_le_sum
      intro A hA
      obtain ⟨hA', hiA⟩ := mem_filter.mp hA
      rw [Finset.card_erase_of_mem hiA]
      have := hr A hA'
      omega
    _ = (K.biUnion (fun A => A.erase i)).card := (Finset.card_biUnion hd).symm
    _ ≤ n := by simpa using Finset.card_le_univ (K.biUnion (fun A => A.erase i))

theorem meeting_card_le {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (d : ℕ) (hd : ∀ i ∈ A, (H.filter (fun A => i ∈ A)).card ≤ d) :
    (H.filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * d := by
  have heq : H.filter (fun B => (A ∩ B).Nonempty) = A.biUnion (fun i => H.filter (fun A => i ∈ A)) := by
    ext B
    simp only [mem_filter, mem_biUnion, Finset.Nonempty, mem_inter]
    constructor
    · rintro ⟨hB, i, hiA, hiB⟩
      exact ⟨i, hiA, hB, hiB⟩
    · rintro ⟨i, hiA, hB, hiB⟩
      exact ⟨hB, i, hiA, hiB⟩
  calc
    (H.filter (fun B => (A ∩ B).Nonempty)).card = (A.biUnion (fun i => H.filter (fun A => i ∈ A))).card := congrArg Finset.card heq
    _ ≤ ∑ i ∈ A, (H.filter (fun A => i ∈ A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, d := Finset.sum_le_sum hd
    _ = A.card * d := by simp

/-- Color large supports in descending order of size. -/
theorem large_rank_color {n : ℕ} (H : Finset (Finset (Fin n))) (q m : ℕ)
    (hq : 0 < q) (hm : n + n / q < m) (h : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hsize : ∀ A ∈ H, q + 1 ≤ A.card) :
    ∃ c : Finset (Fin n) → Fin m, (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) := by
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    by_cases hH : H.Nonempty
    · obtain ⟨A, hA, hmin⟩ := H.exists_min_image Finset.card hH
      let K := H.erase A
      have hKH : K ⊆ H := Finset.erase_subset _ _
      obtain ⟨c, hc⟩ := ih K (Finset.erase_ssubset hA) (linear_mono h hKH)
        (fun B hB => hsize B (hKH hB))
      let s := A.card - 1
      have hs : A.card = s + 1 := by
        have := hsize A hA
        dsimp [s]
        omega
      have hqs : q ≤ s := by have := hsize A hA; omega
      have hsp : 0 < s := hq.trans_le hqs
      have hmeet : (K.filter (fun B => (A ∩ B).Nonempty)).card ≤ n + n / q := by
        calc
          (K.filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * (n / s) := by
            apply meeting_card_le
            intro i _
            rw [Nat.le_div_iff_mul_le hsp, Nat.mul_comm]
            exact incident_mul_le (linear_mono h hKH) s
              (fun B hB => hs ▸ hmin B (hKH hB)) i
          _ = s * (n / s) + n / s := by rw [hs, Nat.add_mul, Nat.one_mul]
          _ ≤ n + n / q := Nat.add_le_add
            (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
            ((Nat.le_div_iff_mul_le hq).mpr <|
              (Nat.mul_le_mul_left (n / s) hqs).trans (Nat.div_mul_le_self _ _))
      let blocked := (K.filter (fun B => (A ∩ B).Nonempty)).image c
      have hblocked : blocked.card < m := (Finset.card_image_le.trans hmeet).trans_lt hm
      have hfree : (univ \ blocked).Nonempty := by
        apply Finset.card_pos.mp
        rwa [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, Nat.sub_pos_iff_lt]
      obtain ⟨w, hw⟩ := hfree
      have hne : ∀ B ∈ K, (A ∩ B).Nonempty → w ≠ c B := by
        intro B hB hi he
        exact (mem_sdiff.mp hw).2 (he ▸ mem_image_of_mem c (mem_filter.mpr ⟨hB, hi⟩))
      refine ⟨fun B => if B = A then w else c B, ?_⟩
      intro B hB D hD hBD hi
      by_cases hBA : B = A
      · subst B
        have hDA := Ne.symm hBD
        simpa only [if_pos rfl, if_true, if_neg hDA] using hne D (mem_erase.mpr ⟨hDA, hD⟩) hi
      by_cases hDA : D = A
      · subst D
        have hi' : (A ∩ B).Nonempty := by simpa only [Finset.inter_comm] using hi
        simpa only [if_pos rfl, if_true, if_neg hBA] using
          (hne B (mem_erase.mpr ⟨hBA, hB⟩) hi').symm
      simpa only [if_neg hBA, if_neg hDA] using
        hc B (mem_erase.mpr ⟨hBA, hB⟩) D (mem_erase.mpr ⟨hDA, hD⟩) hBD hi
    · have : 0 < m := Nat.zero_le _ |>.trans_lt hm
      exact ⟨fun _ => ⟨0, this⟩, fun A hA => (hH ⟨A, hA⟩).elim⟩

open scoped Classical in
theorem mem_support {V : Type*} {n : ℕ} (C : EFLConfig V n) (v : V) (i : Fin n) :
    i ∈ (univ.filter (fun i => v ∈ C.A i)) ↔ v ∈ C.A i := by
  simp

open scoped Classical in
theorem support_inter_le {V : Type*} {n : ℕ} (C : EFLConfig V n) {u v : V}
    (huv : u ≠ v) : ((univ.filter (fun i => u ∈ C.A i)) ∩
      (univ.filter (fun i => v ∈ C.A i))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra h
  obtain ⟨hiu, hiv⟩ := mem_inter.mp hi
  obtain ⟨hju, hjv⟩ := mem_inter.mp hj
  exact huv (Finset.card_le_one.mp (C.inter_le i j h) u
    (mem_inter.mpr ⟨(mem_support C u i).mp hiu, (mem_support C u j).mp hju⟩) v
    (mem_inter.mpr ⟨(mem_support C v i).mp hiv, (mem_support C v j).mp hjv⟩))

open scoped Classical in
theorem shared_of_linear_color {V : Type*} {n m : ℕ} (C : EFLConfig V n)
    (hcol : ∀ H : Finset (Finset (Fin n)), (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) → (∀ A ∈ H, 2 ≤ A.card) →
      ∃ c : Finset (Fin n) → Fin m, (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)) :
    ∃ c : V → Fin m, ∀ i u v, u ∈ C.A i → v ∈ C.A i → C.IsShared u →
      C.IsShared v → c u = c v → u = v := by
  let H := C.sharedSet.image (fun v => (univ.filter (fun i => v ∈ C.A i)))
  have mem_shared (v : V) (hv : C.IsShared v) : v ∈ C.sharedSet := by
    obtain ⟨i, hi⟩ := C.cover v
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _, hi⟩, hv⟩
  have size (v : V) (hv : C.IsShared v) : 2 ≤ ((univ.filter (fun i => v ∈ C.A i))).card := by
    obtain ⟨i, j, hij, hi, hj⟩ := hv
    exact Finset.one_lt_card.mpr ⟨i, (mem_support C v i).mpr hi, j,
      (mem_support C v j).mpr hj, hij⟩
  obtain ⟨c, hc⟩ := hcol H (by
    intro A hA B hB hAB
    obtain ⟨u, _, rfl⟩ := mem_image.mp hA
    obtain ⟨v, _, rfl⟩ := mem_image.mp hB
    exact support_inter_le C (fun e => hAB (congrArg (fun v => (univ.filter (fun i => v ∈ C.A i))) e))) (by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hA
    exact size v (mem_filter.mp hv).2)
  refine ⟨c ∘ (fun v => (univ.filter (fun i => v ∈ C.A i))), ?_⟩
  intro i u v hu hv hsu hsv he
  by_contra huv
  have hs : (univ.filter (fun i => u ∈ C.A i)) ≠ (univ.filter (fun i => v ∈ C.A i)) := by
    intro h
    have hle := support_inter_le C huv
    rw [← h, Finset.inter_self] at hle
    exact (Nat.not_succ_le_self 1) ((size u hsu).trans hle)
  exact hc _ (mem_image_of_mem _ (mem_shared u hsu))
    _ (mem_image_of_mem _ (mem_shared v hsv)) hs
    ⟨i, mem_inter.mpr ⟨(mem_support C u i).mpr hu, (mem_support C v i).mpr hv⟩⟩ he

theorem properOn_map {n : ℕ} {κ τ : Type*} {H : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → κ} (hc : (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)) {f : κ → τ}
    (hf : Function.Injective f) :
    (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → (f ∘ c) A ≠ (f ∘ c) B) :=
  fun A hA B hB hAB hi he => hc A hA B hB hAB hi (hf he)

theorem properOn_piecewise {n : ℕ} {κ : Type*} {H K : Finset (Finset (Fin n))}
    {c d : Finset (Fin n) → κ} (hc : (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)) 
    (hd : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → d A ≠ d B)
    (hcross : ∀ A ∈ H, ∀ B ∈ K, (A ∩ B).Nonempty → c A ≠ d B) :
    ∀ A ∈ H ∪ K, ∀ B ∈ H ∪ K, A ≠ B → (A ∩ B).Nonempty →
      (fun A => if A ∈ H then c A else d A) A ≠ (fun A => if A ∈ H then c A else d A) B := by
  intro A hA B hB hAB hi
  by_cases ha : A ∈ H <;> by_cases hb : B ∈ H
  · simpa only [if_pos ha, if_pos hb] using hc A ha B hb hAB hi
  · simpa only [if_pos ha, if_neg hb] using
      hcross A ha B ((mem_union.mp hB).resolve_left hb) hi
  · have hi' : (B ∩ A).Nonempty := by simpa only [Finset.inter_comm] using hi
    simpa only [if_neg ha, if_pos hb] using
      (hcross B hb A ((mem_union.mp hA).resolve_left ha) hi').symm
  · simpa only [if_neg ha, if_neg hb] using
      hd A ((mem_union.mp hA).resolve_left ha) B ((mem_union.mp hB).resolve_left hb) hAB hi

/-- Use one palette for the large and small supports and a second for the middle ranks. -/
theorem linear_color (h1 : H1) (h2 : H2) (q : ℕ) (hq : 0 < q) :
    ∀ᶠ n in atTop, ∀ H : Finset (Finset (Fin n)), (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card) →
      ∃ c : Finset (Fin n) → Fin ((n + 2 * (n / q) + 1) + (n / q + 1)), (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) := by
  let lo := 2 * q
  let hi := lo * q
  have hlo : 0 < lo := by dsimp [lo]; omega
  have hlohi : lo ≤ hi := by
    dsimp [hi]
    exact Nat.le_mul_of_pos_right _ hq
  have hqhi : q ≤ hi := by
    dsimp [hi]
    exact Nat.le_mul_of_pos_left _ hlo
  have hhi : 0 < hi := hlo.trans_le hlohi
  obtain ⟨Ds, hs⟩ := h1 q hq
  obtain ⟨Dm, hm⟩ := h2 hi
  filter_upwards [eventually_ge_atTop Ds, eventually_ge_atTop (Dm * lo)] with n hDs hDm H hH hmin
  let S := H.filter (fun A => A.card ≤ lo)
  let M := H.filter (fun A => lo < A.card ∧ A.card ≤ hi)
  let B := H.filter (fun A => hi < A.card)
  have hSH : S ⊆ H := filter_subset _ _
  have hMH : M ⊆ H := filter_subset _ _
  have hBH : B ⊆ H := filter_subset _ _
  let m₁ := n + 2 * (n / q) + 1
  let m₂ := n / q + 1
  obtain ⟨b, hb⟩ := large_rank_color B q m₁ hq (by dsimp [m₁]; omega) (linear_mono hH hBH)
    (fun A hA => Nat.succ_le_of_lt (hqhi.trans_lt (mem_filter.mp hA).2))
  have hBdeg (i : Fin n) : (B.filter (fun A => i ∈ A)).card ≤ n / hi := by
    rw [Nat.le_div_iff_mul_le hhi, Nat.mul_comm]
    exact incident_mul_le (linear_mono hH hBH) hi (fun A hA => (mem_filter.mp hA).2) i
  let blocked (A : Finset (Fin n)) := (B.filter (fun D => (A ∩ D).Nonempty)).image b
  have hblocked (A : Finset (Fin n)) (hA : A ∈ S) : (blocked A).card ≤ n / q := by
    calc
      (blocked A).card ≤ (B.filter (fun D => (A ∩ D).Nonempty)).card := Finset.card_image_le
      _ ≤ A.card * (n / hi) := meeting_card_le B A _ (fun i _ => hBdeg i)
      _ ≤ lo * (n / hi) := Nat.mul_le_mul_right _ (mem_filter.mp hA).2
      _ ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by
        calc
          lo * (n / hi) * q = (n / hi) * hi := by dsimp [hi]; ac_rfl
          _ ≤ n := Nat.div_mul_le_self _ _)
  obtain ⟨s, hsp, hsl⟩ := hs n n m₁ hDs (by dsimp [m₁]; omega) S
    (fun A => univ \ blocked A) (linear_mono hH hSH)
    (fun A hA => ⟨hmin A (hSH hA), (mem_filter.mp hA).2⟩) (by
      intro i
      simpa using incident_mul_le (linear_mono hH hSH) 1 (fun A hA => hmin A (hSH hA)) i) (by
      intro A hA
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have := hblocked A hA
      dsimp [m₁]
      omega)
  have h2lo : 2 * (n / lo) ≤ m₂ := by
    have h : 2 * (n / lo) ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by
      calc
        2 * (n / lo) * q = (n / lo) * lo := by dsimp [lo]; ac_rfl
        _ ≤ n := Nat.div_mul_le_self _ _)
    dsimp [m₂]
    omega
  obtain ⟨c₀, hc₀⟩ := hm n (n / lo) ((Nat.le_div_iff_mul_le hlo).mpr hDm)
    M (linear_mono hH hMH)
    (fun A hA => ⟨hmin A (hMH hA), (mem_filter.mp hA).2.2⟩) (by
      intro i
      rw [Nat.le_div_iff_mul_le hlo, Nat.mul_comm]
      exact incident_mul_le (linear_mono hH hMH) lo (fun A hA => (mem_filter.mp hA).2.1) i)
  let c : Finset (Fin n) → Fin m₂ := fun A => Fin.castLE h2lo (c₀ A)
  have hc : ∀ A ∈ M, ∀ D ∈ M, A ≠ D → (A ∩ D).Nonempty → c A ≠ c D :=
    properOn_map hc₀ (Fin.castLE_injective h2lo)
  let first (A : Finset (Fin n)) := if A ∈ S then s A else b A
  have hfirst : ∀ A ∈ S ∪ B, ∀ D ∈ S ∪ B, A ≠ D → (A ∩ D).Nonempty → first A ≠ first D :=
    properOn_piecewise hsp hb (by
    intro A hA D hD hAD he
    have hmem : b D ∈ blocked A := mem_image_of_mem b (mem_filter.mpr ⟨hD, hAD⟩)
    exact (mem_sdiff.mp (hsl A hA)).2 (he.symm ▸ hmem))
  have hunion : (S ∪ B) ∪ M = H := by
    ext A
    simp only [S, B, M, mem_union, mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hA
      by_cases hsmall : A.card ≤ lo
      · exact Or.inl (Or.inl ⟨hA, hsmall⟩)
      by_cases hlarge : hi < A.card
      · exact Or.inl (Or.inr ⟨hA, hlarge⟩)
      exact Or.inr ⟨hA, Nat.lt_of_not_ge hsmall, Nat.le_of_not_gt hlarge⟩
  have hoff : Function.Injective (@Fin.natAdd m₂ m₁) := by
    intro a b he
    apply Fin.ext
    have he' := congrArg Fin.val he
    change m₁ + a.val = m₁ + b.val at he'
    omega
  have hproper := properOn_piecewise (properOn_map hfirst (Fin.castAdd_injective m₁ m₂))
    (properOn_map hc hoff) (by
    intro A _ D _ _ he
    have he' := congrArg Fin.val he
    change (first A).val = m₁ + (c D).val at he'
    have hlt := (first A).isLt
    omega)
  rw [hunion] at hproper
  exact ⟨_, hproper⟩

theorem palette_le_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      (n + 2 * (n / q) + 1) + (n / q + 1) ≤ ⌊(1 + ε) * (n : ℝ)⌋₊ := by
  obtain ⟨q, hq⟩ := exists_nat_gt (6 / ε)
  have hεq : (6 : ℝ) < ε * q := by
    rw [mul_comm]
    exact (div_lt_iff₀ hε).mp hq
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hεq
      norm_num at hεq
    · exact h
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hεn : 4 ≤ ε * (n : ℝ) := by
    have h : (4 : ℝ) < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have hle : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [mul_comm]
    exact h.le.trans (mul_le_mul_of_nonneg_right hle hε.le)
  have hd : (↑(n / q : ℕ) : ℝ) * q ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n q
  have hbound : 6 * (↑(n / q : ℕ) : ℝ) ≤ ε * n := by
    calc
      _ ≤ (ε * q) * (↑(n / q : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hεq.le (by positivity)
      _ = ε * ((↑(n / q : ℕ) : ℝ) * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hε.le
  apply Nat.le_floor
  push_cast
  nlinarith

/-- Kahn 1992: the shared vertices (= edges of the dual linear hypergraph on n vertices)
can be properly coloured with floor((1+eps)n) colours for n large. -/
theorem kahn_shared (h1 : H1) (h2 : H2) : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ (V : Type) (C : EFLConfig V n),
    ∃ c : V → Fin ⌊(1 + ε) * n⌋₊, ∀ i u v, u ∈ C.A i → v ∈ C.A i → C.IsShared u →
      C.IsShared v → c u = c v → u = v := by
  intro ε hε
  obtain ⟨q, hq, hfloor⟩ := palette_le_floor ε hε
  filter_upwards [linear_color h1 h2 q hq, hfloor] with n hn hf V C
  apply shared_of_linear_color C
  intro H hH hm
  obtain ⟨c, hc⟩ := hn H hH hm
  exact ⟨_, properOn_map hc (Fin.castLE_injective hf)⟩

theorem main : H1 → H2 → type_of% @Erdos19.erdos_19.variants.kahn := by
  intro h1 h2 ε hε
  filter_upwards [kahn_shared h1 h2 ε hε] with n hn V C
  obtain ⟨c, hc⟩ := hn V C
  exact colorable_of_sharedColoring_le C _ (le_floor_mul ε hε n) c hc

end OMA.R_Erdos19_erdos_19_variants_kahn_R1
