import OMAStatements.S_erdos_129
import Mathlib

open scoped Classical

namespace E129

/-! ## Definitions -/

/-- `c` has no red (colour `0`) triangle. -/
def NoRedTri {n : ℕ} (c : Sym2 (Fin n) → Fin 2) : Prop :=
  ∀ x y z : Fin n, x ≠ y → y ≠ z → x ≠ z →
    ¬ (c s(x, y) = 0 ∧ c s(y, z) = 0 ∧ c s(x, z) = 0)

/-- Number of two-colourings of `K_n` with no red triangle. -/
noncomputable def T (n : ℕ) : ℕ := Fintype.card {c : Sym2 (Fin n) → Fin 2 // NoRedTri c}

/-- A colouring is good for `n, M` when every `n`-element vertex set carries a monochromatic
triangle in each of the two colours. -/
def Good (n M : ℕ) (c : Sym2 (Fin M) → Fin 2) : Prop :=
  ∀ S : Finset (Fin M), S.card = n → ∀ i : Fin 2,
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      c s(x, y) = i ∧ c s(y, z) = i ∧ c s(x, z) = i

/-! ## Independent sets in the red graph -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `I` is independent in the red graph of the colouring `c`. -/
def Indep (c : Sym2 V → Fin 2) (I : Finset V) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → c s(x, y) ≠ 0

/-- The number of red-independent subsets of the whole vertex set. -/
noncomputable def ia (c : Sym2 V → Fin 2) : ℕ := Fintype.card {I : Finset V // Indep c I}

/-- The number of red-independent subsets of `W`. -/
noncomputable def iaIn (c : Sym2 V → Fin 2) (W : Finset V) : ℕ :=
  Fintype.card {I : Finset V // I ⊆ W ∧ Indep c I}

lemma iaIn_eq_card (c : Sym2 V → Fin 2) (W : Finset V) :
    iaIn c W = (W.powerset.filter (fun I => Indep c I)).card := by
  unfold iaIn
  rw [Fintype.card_subtype]
  congr 1
  ext I
  simp [Finset.mem_powerset, Finset.mem_filter, and_comm]

lemma ia_eq_iaIn_univ (c : Sym2 V → Fin 2) : ia c = iaIn c Finset.univ := by
  unfold ia iaIn
  refine Fintype.card_congr (Equiv.subtypeEquivRight ?_)
  intro I
  simp

lemma Indep.mono {c : Sym2 V → Fin 2} {I J : Finset V} (h : Indep c I) (hJI : J ⊆ I) :
    Indep c J := fun x hx y hy hxy => h x (hJI hx) y (hJI hy) hxy

lemma Indep.erase {c : Sym2 V → Fin 2} {I : Finset V} (h : Indep c I) (x : V) :
    Indep c (I.erase x) := h.mono (Finset.erase_subset _ _)

lemma iaIn_mono {c : Sym2 V → Fin 2} {W W' : Finset V} (h : W ⊆ W') :
    iaIn c W ≤ iaIn c W' := by
  rw [iaIn_eq_card, iaIn_eq_card]
  refine Finset.card_le_card ?_
  intro I hI
  simp only [Finset.mem_filter, Finset.mem_powerset] at hI ⊢
  exact ⟨hI.1.trans h, hI.2⟩

lemma iaIn_le_pow (c : Sym2 V → Fin 2) (W : Finset V) : iaIn c W ≤ 2 ^ W.card := by
  rw [iaIn_eq_card]
  calc (W.powerset.filter (fun I => Indep c I)).card ≤ W.powerset.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ W.card := Finset.card_powerset W

/-- **Peeling one red edge.**  The independent sets inside `W` either avoid both endpoints of a
red edge `{x,y}`, or meet it in exactly one of them; the last two classes inject into the first
by deleting the endpoint. -/
lemma iaIn_peel {c : Sym2 V → Fin 2} {W : Finset V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) (hred : c s(x, y) = 0) :
    iaIn c W ≤ 3 * iaIn c ((W.erase x).erase y) := by
  classical
  set B : Finset V := (W.erase x).erase y with hB
  have hmemB : ∀ z : V, z ∈ B ↔ z ∈ W ∧ z ≠ x ∧ z ≠ y := by
    intro z
    rw [hB, Finset.mem_erase, Finset.mem_erase]
    constructor
    · rintro ⟨hzy, hzx, hzW⟩
      exact ⟨hzW, hzx, hzy⟩
    · rintro ⟨hzW, hzx, hzy⟩
      exact ⟨hzy, hzx, hzW⟩
  set F : Finset (Finset V) := B.powerset.filter (fun I => Indep c I) with hF
  have hFB : ∀ I ∈ F, I ⊆ B ∧ Indep c I := by
    intro I hI
    simp only [hF, Finset.mem_filter, Finset.mem_powerset] at hI
    exact hI
  have hsub : W.powerset.filter (fun I => Indep c I) ⊆
      F ∪ F.image (insert x) ∪ F.image (insert y) := by
    intro I hI
    simp only [Finset.mem_filter, Finset.mem_powerset] at hI
    obtain ⟨hIW, hInd⟩ := hI
    by_cases hxI : x ∈ I
    · -- `I` contains `x`, hence not `y`
      have hyI : y ∉ I := by
        intro hy'
        exact hInd x hxI y hy' hxy hred
      have hsub1 : I.erase x ⊆ B := by
        intro z hz
        rw [hmemB]
        have hzI : z ∈ I := Finset.mem_of_mem_erase hz
        refine ⟨hIW hzI, (Finset.mem_erase.mp hz).1, ?_⟩
        intro hzy
        exact hyI (hzy ▸ hzI)
      have hIF : I.erase x ∈ F := by
        simp only [hF, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hsub1, hInd.erase x⟩
      have : I = insert x (I.erase x) := (Finset.insert_erase hxI).symm
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨_, hIF, this.symm⟩)
    · by_cases hyI : y ∈ I
      · have hsub1 : I.erase y ⊆ B := by
          intro z hz
          rw [hmemB]
          have hzI : z ∈ I := Finset.mem_of_mem_erase hz
          refine ⟨hIW hzI, ?_, (Finset.mem_erase.mp hz).1⟩
          intro hzx
          exact hxI (hzx ▸ hzI)
        have hIF : I.erase y ∈ F := by
          simp only [hF, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hsub1, hInd.erase y⟩
        have : I = insert y (I.erase y) := (Finset.insert_erase hyI).symm
        simp only [Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨_, hIF, this.symm⟩
      · have hsub1 : I ⊆ B := by
          intro z hz
          rw [hmemB]
          exact ⟨hIW hz, fun h => hxI (h ▸ hz), fun h => hyI (h ▸ hz)⟩
        have hIF : I ∈ F := by
          simp only [hF, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hsub1, hInd⟩
        simp only [Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl hIF)
  have h1 : (W.powerset.filter (fun I => Indep c I)).card ≤
      (F ∪ F.image (insert x) ∪ F.image (insert y)).card := Finset.card_le_card hsub
  have h2 : (F ∪ F.image (insert x) ∪ F.image (insert y)).card ≤
      F.card + F.card + F.card := by
    have ha := Finset.card_union_le (F ∪ F.image (insert x)) (F.image (insert y))
    have hb := Finset.card_union_le F (F.image (insert x))
    have hc : (F.image (insert x)).card ≤ F.card := Finset.card_image_le
    have hd : (F.image (insert y)).card ≤ F.card := Finset.card_image_le
    omega
  have hFcard : F.card = iaIn c B := by
    rw [iaIn_eq_card]
  rw [iaIn_eq_card, ← hFcard]
  omega

/-! ## Packings of red edges -/

/-- The two endpoints of an ordered pair. -/
def pairSet (p : V × V) : Finset V := {p.1, p.2}

/-- All endpoints of a set of ordered pairs. -/
def ends (P : Finset (V × V)) : Finset V := P.biUnion pairSet

/-- A set of pairwise disjoint red edges inside `W`, written as ordered pairs. -/
def IsPacking (c : Sym2 V → Fin 2) (W : Finset V) (P : Finset (V × V)) : Prop :=
  (∀ p ∈ P, p.1 ∈ W ∧ p.2 ∈ W ∧ p.1 ≠ p.2 ∧ c s(p.1, p.2) = 0) ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (pairSet p) (pairSet q))

lemma mem_pairSet {p : V × V} {z : V} : z ∈ pairSet p ↔ z = p.1 ∨ z = p.2 := by
  simp [pairSet]

lemma mem_ends {P : Finset (V × V)} {z : V} : z ∈ ends P ↔ ∃ p ∈ P, z = p.1 ∨ z = p.2 := by
  simp [ends, mem_pairSet]

lemma ends_insert (p : V × V) (P : Finset (V × V)) :
    ends (insert p P) = pairSet p ∪ ends P := by
  simp [ends]

lemma IsPacking.mono {c : Sym2 V → Fin 2} {W : Finset V} {P Q : Finset (V × V)}
    (h : IsPacking c W P) (hQP : Q ⊆ P) : IsPacking c W Q :=
  ⟨fun p hp => h.1 p (hQP hp), fun p hp q hq hpq => h.2 p (hQP hp) q (hQP hq) hpq⟩

lemma IsPacking.ends_subset {c : Sym2 V → Fin 2} {W : Finset V} {P : Finset (V × V)}
    (h : IsPacking c W P) : ends P ⊆ W := by
  intro z hz
  rw [mem_ends] at hz
  obtain ⟨p, hp, hzp | hzp⟩ := hz
  · rw [hzp]; exact (h.1 p hp).1
  · rw [hzp]; exact (h.1 p hp).2.1

lemma IsPacking.ends_card {c : Sym2 V → Fin 2} {W : Finset V} {P : Finset (V × V)}
    (h : IsPacking c W P) : (ends P).card = 2 * P.card := by
  have hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (pairSet p) (pairSet q) := h.2
  rw [ends, Finset.card_biUnion hdisj]
  calc (∑ p ∈ P, (pairSet p).card) = ∑ _p ∈ P, 2 := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        simp [pairSet, (h.1 p hp).2.2.1]
    _ = 2 * P.card := by simp [Finset.sum_const, Nat.mul_comm]

lemma notMem_ends_of_disjoint {P : Finset (V × V)} {p : V × V}
    (hdisj : ∀ q ∈ P, Disjoint (pairSet p) (pairSet q)) (z : V)
    (hz : z = p.1 ∨ z = p.2) : z ∉ ends P := by
  intro hzP
  rw [mem_ends] at hzP
  obtain ⟨q, hq, hzq⟩ := hzP
  exact (Finset.disjoint_left.mp (hdisj q hq)) (mem_pairSet.mpr hz) (mem_pairSet.mpr hzq)

/-- **Peeling a whole packing.**  Each red matching edge costs a factor `3` and deletes two
vertices. -/
theorem iaIn_le_packing {c : Sym2 V → Fin 2} {W : Finset V} :
    ∀ P : Finset (V × V), IsPacking c W P →
      iaIn c W ≤ 3 ^ P.card * iaIn c (W \ ends P) := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
      intro _
      simp [ends]
  | insert p P hpmem ih =>
      intro hP
      have hP' : IsPacking c W P := hP.mono (Finset.subset_insert p P)
      have hp := hP.1 p (Finset.mem_insert_self p P)
      have hpq : p ∉ P := hpmem
      have hdisj : ∀ q ∈ P, Disjoint (pairSet p) (pairSet q) := by
        intro q hq
        exact hP.2 p (Finset.mem_insert_self p P) q (Finset.mem_insert_of_mem hq)
          (fun h => hpq (h ▸ hq))
      have h1 : p.1 ∈ W \ ends P := by
        rw [Finset.mem_sdiff]
        exact ⟨hp.1, notMem_ends_of_disjoint hdisj p.1 (Or.inl rfl)⟩
      have h2 : p.2 ∈ W \ ends P := by
        rw [Finset.mem_sdiff]
        exact ⟨hp.2.1, notMem_ends_of_disjoint hdisj p.2 (Or.inr rfl)⟩
      have hset : ((W \ ends P).erase p.1).erase p.2 = W \ ends (insert p P) := by
        rw [ends_insert]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_union, mem_pairSet]
        tauto
      calc iaIn c W ≤ 3 ^ P.card * iaIn c (W \ ends P) := ih hP'
        _ ≤ 3 ^ P.card * (3 * iaIn c ((W \ ends P).erase p.1 |>.erase p.2)) := by
            have hpeel := iaIn_peel h1 h2 hp.2.2.1 hp.2.2.2
            gcongr
        _ = 3 ^ (insert p P).card * iaIn c (W \ ends (insert p P)) := by
            rw [hset, Finset.card_insert_of_notMem hpmem]
            ring

/-- A packing of red edges of maximum size. -/
theorem exists_max_packing {c : Sym2 V → Fin 2} {W : Finset V} :
    ∃ P : Finset (V × V), IsPacking c W P ∧ ∀ Q : Finset (V × V), IsPacking c W Q → Q.card ≤ P.card := by
  classical
  set S : Finset (Finset (V × V)) := Finset.univ.filter (fun P => IsPacking c W P) with hS
  have hne : S.Nonempty := ⟨∅, by simp [hS, IsPacking]⟩
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image S (fun P => P.card) hne
  exact ⟨P, by simpa [hS] using hP, fun Q hQ => hmax Q (by simp [hS, hQ])⟩

/-- A maximum packing meets every red edge: its endpoints form a vertex cover. -/
lemma packing_cover {c : Sym2 V → Fin 2} {W : Finset V} {P : Finset (V × V)}
    (hP : IsPacking c W P) (hmax : ∀ Q, IsPacking c W Q → Q.card ≤ P.card) :
    ∀ u ∈ W, ∀ v ∈ W, u ≠ v → c s(u, v) = 0 → u ∈ ends P ∨ v ∈ ends P := by
  intro u hu v hv huv hred
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨huE, hvE⟩ := hcon
  have hmemP : (u, v) ∉ P := fun h => huE (mem_ends.mpr ⟨(u, v), h, Or.inl rfl⟩)
  have hnotends : ∀ q ∈ P, Disjoint (pairSet (u, v)) (pairSet q) := by
    intro q hq
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [mem_pairSet] at hz
    rcases hz with rfl | rfl
    · exact huE (mem_ends.mpr ⟨q, hq, (mem_pairSet.mp hz')⟩)
    · exact hvE (mem_ends.mpr ⟨q, hq, (mem_pairSet.mp hz')⟩)
  have hnew : IsPacking c W (insert (u, v) P) := by
    constructor
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨hu, hv, huv, hred⟩
      · exact hP.1 q hq
    · intro q hq q' hq' hqq'
      rcases Finset.mem_insert.mp hq with rfl | hq <;>
        rcases Finset.mem_insert.mp hq' with rfl | hq'
      · exact absurd rfl hqq'
      · exact hnotends q' hq'
      · exact (hnotends q hq).symm
      · exact hP.2 q hq q' hq' hqq'
  have hcard := hmax _ hnew
  rw [Finset.card_insert_of_notMem hmemP] at hcard
  omega

lemma pow_le_pow_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {k m : ℕ} (hkm : k ≤ m) :
    x ^ m ≤ x ^ k := by
  have h : x ^ m = x ^ k * x ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' hkm]
  rw [h]
  calc x ^ k * x ^ (m - k) ≤ x ^ k * 1 := by
        gcongr
        exact pow_le_one₀ hx0 hx1
    _ = x ^ k := by ring

/-! ## Stage (iii): the split bound -/

/-- The restriction of a colouring of `K_{m+m}` to the first block of `m` vertices. -/
def resA {m : ℕ} (c : Sym2 (Fin (m + m)) → Fin 2) : Sym2 (Fin m) → Fin 2 :=
  fun e => c (e.map (Fin.castAdd m))

/-- The restriction of a colouring of `K_{m+m}` to the second block of `m` vertices. -/
def resB {m : ℕ} (c : Sym2 (Fin (m + m)) → Fin 2) : Sym2 (Fin m) → Fin 2 :=
  fun e => c (e.map (Fin.natAdd m))

/-- The cross colouring of a colouring of `K_{m+m}`. -/
def cross {m : ℕ} (c : Sym2 (Fin (m + m)) → Fin 2) : Fin m × Fin m → Fin 2 :=
  fun p => c s(Fin.castAdd m p.1, Fin.natAdd m p.2)

/-- The red neighbourhood of `v` in the cross colouring, as a subset of the first block. -/
def col {m : ℕ} (x : Fin m × Fin m → Fin 2) (v : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun u => x (u, v) = 0)

/-- Every red cross-neighbourhood of a block is independent in the restriction. -/
def CrossOK {m : ℕ} (cA : Sym2 (Fin m) → Fin 2) (x : Fin m × Fin m → Fin 2) : Prop :=
  ∀ v : Fin m, Indep cA (col x v)

lemma castAdd_ne_natAdd {m : ℕ} (u v : Fin m) : (Fin.castAdd m u : Fin (m + m)) ≠ Fin.natAdd m v := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma cross_apply {m : ℕ} (c : Sym2 (Fin (m + m)) → Fin 2) (u v : Fin m) :
    c s(Fin.castAdd m u, Fin.natAdd m v) = cross c (u, v) := rfl

lemma resA_apply {m : ℕ} (c : Sym2 (Fin (m + m)) → Fin 2) (u v : Fin m) :
    c s(Fin.castAdd m u, Fin.castAdd m v) = resA c s(u, v) := by
  simp [resA, Sym2.map_mk]

lemma resB_apply {m : ℕ} (c : Sym2 (Fin (m + m)) → Fin 2) (u v : Fin m) :
    c s(Fin.natAdd m u, Fin.natAdd m v) = resB c s(u, v) := by
  simp [resB, Sym2.map_mk]

/-- In `Fin 2` every element is `0` or `1`. -/
lemma fin_two_eq (a : Fin 2) : a = 0 ∨ a = 1 := by
  have h : (a : ℕ) = 0 ∨ (a : ℕ) = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Fin.ext (by simpa using h))

/-- A colouring of `K_{m+m}` is determined by its two halves and its cross colouring. -/
theorem res_injective (m : ℕ) :
    Function.Injective (fun c : Sym2 (Fin (m + m)) → Fin 2 => (resA c, resB c, cross c)) := by
  intro c c' h
  have hA : resA c = resA c' := congrArg (fun p => p.1) h
  have hB : resB c = resB c' := congrArg (fun p => p.2.1) h
  have hX : cross c = cross c' := congrArg (fun p => p.2.2) h
  have key : ∀ u v : Fin (m + m), c s(u, v) = c' s(u, v) := by
    intro u v
    induction u using Fin.addCases with
    | left i =>
        induction v using Fin.addCases with
        | left j => exact congrFun hA s(i, j)
        | right j => exact congrFun hX (i, j)
    | right i =>
        induction v using Fin.addCases with
        | left j =>
            rw [Sym2.eq_swap]
            exact congrFun hX (j, i)
        | right j => exact congrFun hB s(i, j)
  funext e
  induction e using Sym2.ind with
  | _ u v => exact key u v

/-- If a colouring of `K_{m+m}` has no red triangle, every red cross-neighbourhood is independent. -/
theorem noRedTri_crossOK {m : ℕ} {c : Sym2 (Fin (m + m)) → Fin 2} (hc : NoRedTri c) :
    CrossOK (resA c) (cross c) := by
  intro v u₁ hu₁ u₂ hu₂ hu₁₂ hred
  simp only [col, Finset.mem_univ, Finset.mem_filter, true_and] at hu₁ hu₂
  refine hc (Fin.castAdd m u₁) (Fin.castAdd m u₂) (Fin.natAdd m v) ?_ ?_ ?_ ⟨hred, hu₂, hu₁⟩
  · intro h; exact hu₁₂ (Fin.castAdd_inj.mp h)
  · exact castAdd_ne_natAdd u₂ v
  · exact castAdd_ne_natAdd u₁ v

/-- Given independent sets `I v`, the cross colouring whose red neighbourhood of `v` is `I v`. -/
def mkCross {m : ℕ} (F : (_ : Fin m) → Finset (Fin m)) : Fin m × Fin m → Fin 2 :=
  fun p => if p.1 ∈ F p.2 then 0 else 1

lemma mem_col {m : ℕ} (x : Fin m × Fin m → Fin 2) (v u : Fin m) :
    u ∈ col x v ↔ x (u, v) = 0 := by
  simp [col]

lemma col_mkCross {m : ℕ} (F : (_ : Fin m) → Finset (Fin m)) (v : Fin m) :
    col (mkCross F) v = F v := by
  ext u
  rw [mem_col]
  by_cases h : u ∈ F v
  · rw [mkCross, if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [mkCross, if_neg h]
    exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 h⟩

/-- The cross colourings with all red neighbourhoods independent are exactly a product of
choices of independent sets, one per vertex of the second block. -/
noncomputable def colEquiv {m : ℕ} (cA : Sym2 (Fin m) → Fin 2) :
    {x : Fin m × Fin m → Fin 2 // CrossOK cA x} ≃
      ((_ : Fin m) → {I : Finset (Fin m) // Indep cA I}) where
  toFun x := fun v => ⟨col x.1 v, x.2 v⟩
  invFun F := ⟨mkCross (fun v => (F v).1), by
    intro v
    rw [col_mkCross]
    exact (F v).2⟩
  left_inv x := by
    refine Subtype.ext ?_
    funext p
    obtain ⟨u, v⟩ := p
    simp only [mkCross]
    by_cases h : u ∈ col (x : Fin m × Fin m → Fin 2) v
    · rw [if_pos h]
      have hx : (x : Fin m × Fin m → Fin 2) (u, v) = 0 := (mem_col _ v u).mp h
      exact hx.symm
    · rw [if_neg h]
      have hx : (x : Fin m × Fin m → Fin 2) (u, v) ≠ 0 := fun hh => h ((mem_col _ v u).mpr hh)
      rcases fin_two_eq ((x : Fin m × Fin m → Fin 2) (u, v)) with h0 | h1
      · exact absurd h0 hx
      · exact h1.symm
  right_inv F := by
    refine funext ?_
    intro v
    refine Subtype.ext ?_
    exact col_mkCross (fun v => (F v).1) v

/-- The number of cross colourings keeping all red neighbourhoods independently is a power of `ia`. -/
theorem card_crossOK {m : ℕ} (cA : Sym2 (Fin m) → Fin 2) :
    Fintype.card {x : Fin m × Fin m → Fin 2 // CrossOK cA x} = (ia cA) ^ m := by
  rw [Fintype.card_congr (colEquiv cA), Fintype.card_pi]
  simp [Finset.prod_const, Finset.card_univ, ia]

/-- Reassemble a subtype of a product whose predicate only involves the second factor. -/
def sndSubtypeEquiv {β γ : Type*} (P : γ → Prop) : {q : β × γ // P q.2} ≃ β × {x : γ // P x} where
  toFun q := (q.1.1, ⟨q.1.2, q.2⟩)
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv q := by cases q with
    | mk val property => cases val with
      | mk fst snd => rfl
  right_inv q := by cases q with
    | mk fst snd => cases snd with
      | mk val property => rfl

lemma card_colourings (m : ℕ) : Fintype.card (Sym2 (Fin m) → Fin 2) = 2 ^ (m * (m + 1) / 2) := by
  rw [Fintype.card_fun]
  congr 1
  rw [← Finset.card_univ, ← Finset.sym2_univ, Finset.card_sym2]
  simp [Nat.choose_two_right, Nat.mul_comm]

/-- **Stage (iii).**  A colouring of `K_{2m}` without red triangle is determined by the colouring
of one half and a cross colouring whose red neighbourhoods are independent there. -/
theorem T_split (m : ℕ) :
    T (m + m) ≤ 2 ^ (m * (m + 1) / 2) * ∑ cA : Sym2 (Fin m) → Fin 2, (ia cA) ^ m := by
  have step1 : T (m + m) ≤
      Fintype.card {c : Sym2 (Fin (m + m)) → Fin 2 // CrossOK (resA c) (cross c)} := by
    rw [T]
    refine Fintype.card_le_of_injective (fun c => ⟨c.1, noRedTri_crossOK c.2⟩) ?_
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have hval : c = c' := by simpa using h
    exact Subtype.ext hval
  have step2 : Fintype.card {c : Sym2 (Fin (m + m)) → Fin 2 // CrossOK (resA c) (cross c)} ≤
      Fintype.card {p : (Sym2 (Fin m) → Fin 2) × (Sym2 (Fin m) → Fin 2) × (Fin m × Fin m → Fin 2) //
        CrossOK p.1 p.2.2} := by
    refine Fintype.card_le_of_injective
      (fun c => ⟨(resA c.1, resB c.1, cross c.1), c.2⟩) ?_
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have hval : (resA c, resB c, cross c) = (resA c', resB c', cross c') := by simpa using h
    have hcc : c = c' := res_injective m hval
    exact Subtype.ext hcc
  have step3 : Fintype.card {p : (Sym2 (Fin m) → Fin 2) × (Sym2 (Fin m) → Fin 2) ×
        (Fin m × Fin m → Fin 2) // CrossOK p.1 p.2.2} =
      2 ^ (m * (m + 1) / 2) * ∑ cA : Sym2 (Fin m) → Fin 2, (ia cA) ^ m := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (p := fun (a : Sym2 (Fin m) → Fin 2)
        (q : (Sym2 (Fin m) → Fin 2) × (Fin m × Fin m → Fin 2)) => CrossOK a q.2))]
    rw [Fintype.card_sigma]
    have hterm : ∀ cA : Sym2 (Fin m) → Fin 2,
        Fintype.card {q : (Sym2 (Fin m) → Fin 2) × (Fin m × Fin m → Fin 2) // CrossOK cA q.2} =
          2 ^ (m * (m + 1) / 2) * (ia cA) ^ m := by
      intro cA
      rw [Fintype.card_congr (sndSubtypeEquiv (β := Sym2 (Fin m) → Fin 2)
        (γ := Fin m × Fin m → Fin 2) (P := fun x => CrossOK cA x))]
      rw [Fintype.card_prod, card_colourings, card_crossOK]
    simp only [hterm]
    rw [← Finset.mul_sum]
  linarith [step1, step2, step3]




/-! ## Counting red edges as unordered pairs -/

/-- The number of red (colour `0`) non-diagonal edges of a colouring. -/
noncomputable def redC (c : Sym2 V → Fin 2) : ℕ :=
  (Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ c e = 0)).card

/-- The red edges through a fixed vertex. -/
noncomputable def through (c : Sym2 V → Fin 2) (z : V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ c e = 0 ∧ z ∈ e)

lemma mem_through {c : Sym2 V → Fin 2} {z : V} {e : Sym2 V} :
    e ∈ through c z ↔ ¬ e.IsDiag ∧ c e = 0 ∧ z ∈ e := by
  simp [through]

/-- At most `a` red edges pass through a fixed vertex. -/
lemma card_red_through (c : Sym2 V → Fin 2) (z : V) : (through c z).card ≤ Fintype.card V := by
  classical
  rw [← Fintype.card_coe (through c z)]
  refine Fintype.card_le_of_injective (fun e : ↥(through c z) =>
    Sym2.Mem.other ((mem_through.mp e.2).2.2)) ?_
  intro e₁ e₂ h
  have h₁ := Sym2.other_spec ((mem_through.mp e₁.2).2.2)
  have h₂ := Sym2.other_spec ((mem_through.mp e₂.2).2.2)
  have h' : Sym2.Mem.other ((mem_through.mp e₁.2).2.2) =
      Sym2.Mem.other ((mem_through.mp e₂.2).2.2) := h
  exact Subtype.ext (by rw [← h₁, ← h₂, h'])

/-- The set of red edges is covered by the red edges through the elements of a vertex cover. -/
lemma redC_subset {c : Sym2 V → Fin 2} (C : Finset V)
    (hcover : ∀ u v, u ≠ v → c s(u, v) = 0 → u ∈ C ∨ v ∈ C) :
    Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ c e = 0) ⊆ C.biUnion (through c) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hnd, hred⟩ := he
    have hxy : x ≠ y := fun h => hnd (Sym2.mk_isDiag_iff.mpr h)
    rcases hcover x y hxy hred with hx | hy
    · refine Finset.mem_biUnion.mpr ⟨x, hx, ?_⟩
      rw [mem_through]
      exact ⟨hnd, hred, Sym2.mem_mk_left x y⟩
    · refine Finset.mem_biUnion.mpr ⟨y, hy, ?_⟩
      rw [mem_through]
      exact ⟨hnd, hred, Sym2.mem_mk_right x y⟩

/-- The red-edge count is controlled by a maximum packing. -/
lemma redC_le {c : Sym2 V → Fin 2} {P : Finset (V × V)} (hP : IsPacking c Finset.univ P)
    (hcover : ∀ u v, u ≠ v → c s(u, v) = 0 → u ∈ ends P ∨ v ∈ ends P) :
    redC c ≤ 2 * P.card * Fintype.card V := by
  classical
  have h1 : redC c ≤ ((ends P).biUnion (through c)).card :=
    Finset.card_le_card (redC_subset (ends P) hcover)
  have h2 : ((ends P).biUnion (through c)).card ≤ ∑ z ∈ ends P, (through c z).card :=
    Finset.card_biUnion_le
  have h3 : ∑ z ∈ ends P, (through c z).card ≤ ∑ _z ∈ ends P, Fintype.card V :=
    Finset.sum_le_sum (fun z _ => card_red_through c z)
  have h5 : (ends P).card = 2 * P.card := IsPacking.ends_card hP
  have h4 : (∑ _z ∈ ends P, Fintype.card V) = 2 * P.card * Fintype.card V := by
    rw [Finset.sum_const, smul_eq_mul, h5]
  omega

/-- **The independent-set bound**, with the red-edge count as exponent. -/
theorem ia_pow_le (c : Sym2 V → Fin 2) (hV : 0 < Fintype.card V) :
    (ia c : ℝ) ^ Fintype.card V ≤
      (2 : ℝ) ^ (Fintype.card V * Fintype.card V) * (87 / 100 : ℝ) ^ (redC c) := by
  classical
  set a : ℕ := Fintype.card V with ha
  obtain ⟨P, hP, hmax⟩ := exists_max_packing (c := c) (W := (Finset.univ : Finset V))
  have hcover := packing_cover hP hmax
  have hμ : (ends P).card = 2 * P.card := IsPacking.ends_card hP
  have hcompl : (Finset.univ \ ends P).card = a - 2 * P.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ha, hμ]
  have h2μ : 2 * P.card ≤ a := by
    have hsub := IsPacking.ends_subset (c := c) (W := (Finset.univ : Finset V)) hP
    have hc : (ends P).card ≤ a := by simpa [ha] using Finset.card_le_card hsub
    omega
  -- (i) the numeric independent-set bound
  have h1 : ia c ≤ 3 ^ P.card * 2 ^ (a - 2 * P.card) := by
    rw [ia_eq_iaIn_univ]
    have hpk := iaIn_le_packing (c := c) (W := (Finset.univ : Finset V)) P hP
    have hpow := iaIn_le_pow c (Finset.univ \ ends P)
    rw [hcompl] at hpow
    calc iaIn c Finset.univ ≤ 3 ^ P.card * iaIn c (Finset.univ \ ends P) := hpk
      _ ≤ 3 ^ P.card * 2 ^ (a - 2 * P.card) := by gcongr
  -- (ii) the red edge count
  have h2 : redC c ≤ 2 * P.card * a := by
    have hc := redC_le (c := c) hP (by simpa using hcover)
    simpa [ha] using hc
  -- (iii) the real chain
  have hreal : (ia c : ℝ) ≤ (3 : ℝ) ^ P.card * 2 ^ (a - 2 * P.card) := by
    exact_mod_cast h1
  have hstep1 : (ia c : ℝ) ^ a ≤ ((3 : ℝ) ^ P.card * 2 ^ (a - 2 * P.card)) ^ a :=
    pow_le_pow_left₀ (by positivity) hreal a
  have hnat : (a - 2 * P.card) * a + 2 * (P.card * a) = a * a := by
    have hle : 2 * (P.card * a) ≤ a * a := by
      have h := Nat.mul_le_mul_right a h2μ
      calc 2 * (P.card * a) = 2 * P.card * a := by ring
        _ ≤ a * a := h
    rw [Nat.sub_mul, show 2 * P.card * a = 2 * (P.card * a) from by ring]
    exact Nat.sub_add_cancel hle
  have hpow : (2 : ℝ) ^ ((a - 2 * P.card) * a) * (4 : ℝ) ^ (P.card * a) = 2 ^ (a * a) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, hnat]
  have hkey : ((3 : ℝ) ^ P.card * 2 ^ (a - 2 * P.card)) ^ a =
      (2 : ℝ) ^ (a * a) * ((3 : ℝ) / 4) ^ (P.card * a) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, div_pow, ← hpow]
    field_simp
  have hbase : (3 : ℝ) / 4 ≤ (87 / 100 : ℝ) ^ 2 := by norm_num
  have hstep2 : ((3 : ℝ) / 4) ^ (P.card * a) ≤ (87 / 100 : ℝ) ^ (redC c) := by
    have hmono : ((3 : ℝ) / 4) ^ (P.card * a) ≤ ((87 / 100 : ℝ) ^ 2) ^ (P.card * a) :=
      pow_le_pow_left₀ (by norm_num) hbase _
    have hrew : ((87 / 100 : ℝ) ^ 2) ^ (P.card * a) = (87 / 100 : ℝ) ^ (2 * (P.card * a)) := by
      rw [← pow_mul]
    have hfin : (87 / 100 : ℝ) ^ (2 * (P.card * a)) ≤ (87 / 100 : ℝ) ^ (redC c) := by
      refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      have h4 : 2 * (P.card * a) = 2 * P.card * a := by ring
      omega
    linarith [hmono, hrew ▸ hfin]
  calc (ia c : ℝ) ^ a ≤ ((3 : ℝ) ^ P.card * 2 ^ (a - 2 * P.card)) ^ a := hstep1
    _ = (2 : ℝ) ^ (a * a) * ((3 : ℝ) / 4) ^ (P.card * a) := hkey
    _ ≤ (2 : ℝ) ^ (a * a) * (87 / 100 : ℝ) ^ (redC c) := by gcongr



/-! ## Stage (iv): summing over colourings -/

lemma prod_ite_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (x : ℝ) : (∏ i ∈ s, (if p i then x else 1)) = x ^ (s.filter p).card := by
  rw [← Finset.prod_filter_mul_prod_filter_not s p (fun i => (if p i then x else 1))]
  have h1 : (∏ i ∈ s.filter p, (if p i then x else 1)) = ∏ _i ∈ s.filter p, x := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [if_pos (Finset.mem_filter.mp hi).2]
  have h2 : (∏ i ∈ s.filter (fun i => ¬ p i), (if p i then x else 1)) =
      ∏ _i ∈ s.filter (fun i => ¬ p i), 1 := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [if_neg (Finset.mem_filter.mp hi).2]
  rw [h1, h2, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

lemma sum_pow_filter_card {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (x : ℝ) : (∑ s : Finset ι, x ^ (s.filter p).card) = ∏ i : ι, (if p i then x + 1 else 1 + 1) := by
  have key : (∏ i : ι, ((if p i then x else 1) + 1)) =
      ∑ s : Finset ι, ∏ i ∈ s, (if p i then x else 1) := by
    rw [Finset.prod_add (fun i => if p i then x else 1) (fun _ => (1 : ℝ)) Finset.univ]
    have h : (Finset.univ : Finset ι).powerset = Finset.univ := by
      ext s; simp [Finset.mem_powerset]
    rw [h]
    refine Finset.sum_congr rfl ?_
    intro s _
    rw [Finset.prod_const, one_pow, mul_one]
  have hgoal : (∑ s : Finset ι, x ^ (s.filter p).card) =
      ∏ i : ι, ((if p i then x else 1) + 1) := by
    rw [show (∑ s : Finset ι, x ^ (s.filter p).card) =
        ∑ s : Finset ι, ∏ i ∈ s, (if p i then x else 1) from
      Finset.sum_congr rfl (fun s _ => (prod_ite_pow s p x).symm)]
    exact key.symm
  rw [hgoal]
  congr 1
  funext i
  by_cases h : p i <;> simp [h]

lemma card_filter_compl {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i => ¬ p i)).card = Fintype.card ι - (Finset.univ.filter p).card := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι)) (p := p)
  rw [Finset.card_univ] at h
  omega

lemma card_diag (m : ℕ) : (Finset.univ.filter (fun e : Sym2 (Fin m) => e.IsDiag)).card = m := by
  have h1 : (Finset.univ.filter (fun e : Sym2 (Fin m) => e.IsDiag)).card =
      Fintype.card {e : Sym2 (Fin m) // e.IsDiag} := (Fintype.card_subtype _).symm
  rw [h1, Fintype.card_congr (Sym2.diagElemEquiv (α := Fin m)), Fintype.card_fin]

lemma card_nondiag (m : ℕ) :
    (Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ e.IsDiag)).card = m * (m - 1) / 2 := by
  rw [card_filter_compl (fun e : Sym2 (Fin m) => e.IsDiag), card_diag]
  have hcard : Fintype.card (Sym2 (Fin m)) = (m + 1).choose 2 := by
    rw [← Finset.card_univ, ← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ,
      Fintype.card_fin]
  rw [hcard, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_two_right]
  omega

/-- Colourings of the edges of `K_m` are the same as red-edge sets. -/
noncomputable def colourEquiv (m : ℕ) :
    (Sym2 (Fin m) → Fin 2) ≃ Finset (Sym2 (Fin m)) where
  toFun f := Finset.univ.filter (fun e => f e = 0)
  invFun s := fun e => if e ∈ s then 0 else 1
  left_inv f := by
    funext i
    have h : (if f i = 0 then (0 : Fin 2) else 1) = f i := by
      rcases fin_two_eq (f i) with h0 | h1
      · rw [if_pos h0]; exact h0.symm
      · rw [if_neg (by rw [h1]; decide)]; exact h1.symm
    simpa [Finset.mem_filter] using h
  right_inv s := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : i ∈ s
    · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]; exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 h⟩

lemma redC_eq (c : Sym2 (Fin m) → Fin 2) :
    redC c = ((colourEquiv m c).filter (fun e => ¬ e.IsDiag)).card := by
  rw [redC, show colourEquiv m c = Finset.univ.filter (fun e => c e = 0) from rfl,
    Finset.filter_filter]
  congr 1
  refine Finset.filter_congr ?_
  intro e _
  exact and_comm

/-- The weight of a colouring only depends on its red-edge set. -/
theorem sum_redC (m : ℕ) :
    (∑ c : Sym2 (Fin m) → Fin 2, (87 / 100 : ℝ) ^ (redC c)) =
      2 ^ m * (187 / 100 : ℝ) ^ (m * (m - 1) / 2) := by
  have hsum : (∑ c : Sym2 (Fin m) → Fin 2, (87 / 100 : ℝ) ^ (redC c)) =
      ∑ R : Finset (Sym2 (Fin m)),
        (87 / 100 : ℝ) ^ (R.filter (fun e => ¬ e.IsDiag)).card := by
    refine Fintype.sum_equiv (colourEquiv m) _ _ ?_
    intro c
    rw [redC_eq]
  rw [hsum, sum_pow_filter_card (fun e : Sym2 (Fin m) => ¬ e.IsDiag) (87 / 100)]
  have hprod : (∏ e : Sym2 (Fin m), (if ¬ e.IsDiag then (87 / 100 : ℝ) + 1 else 1 + 1)) =
      ((87 / 100 : ℝ) + 1) ^ (m * (m - 1) / 2) * 2 ^ m := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Sym2 (Fin m)))
      (fun e => ¬ e.IsDiag) (fun e => (if ¬ e.IsDiag then (87 / 100 : ℝ) + 1 else 1 + 1))]
    have h1 : (∏ e ∈ Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ e.IsDiag),
        (if ¬ e.IsDiag then (87 / 100 : ℝ) + 1 else 1 + 1)) =
        ∏ _e ∈ Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ e.IsDiag),
          ((87 / 100 : ℝ) + 1) := by
      refine Finset.prod_congr rfl ?_
      intro e he
      rw [if_pos (Finset.mem_filter.mp he).2]
    have h2 : (∏ e ∈ Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ ¬ e.IsDiag),
        (if ¬ e.IsDiag then (87 / 100 : ℝ) + 1 else 1 + 1)) =
        ∏ _e ∈ Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ ¬ e.IsDiag), ((1 : ℝ) + 1) := by
      refine Finset.prod_congr rfl ?_
      intro e he
      rw [if_neg (Finset.mem_filter.mp he).2]
    rw [h1, h2, Finset.prod_const, Finset.prod_const, card_nondiag]
    rw [show (Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ ¬ e.IsDiag)) =
      (Finset.univ.filter (fun e : Sym2 (Fin m) => e.IsDiag)) from by ext e; simp]
    rw [card_diag]
    norm_num
  rw [hprod, show ((87 : ℝ) / 100 + 1) = 187 / 100 by norm_num]
  ring



/-! ## Stage (v): the union bound -/

/-- `c` has no monochromatic triangle of colour `i`. -/
def NoTriG {α : Type*} (c : Sym2 α → Fin 2) (i : Fin 2) : Prop :=
  ∀ x y z : α, x ≠ y → y ≠ z → x ≠ z →
    ¬ (c s(x, y) = i ∧ c s(y, z) = i ∧ c s(x, z) = i)

/-- Restriction of a colouring along a vertex map. -/
def resSym {α β : Type*} (φ : α → β) (c : Sym2 β → Fin 2) : Sym2 α → Fin 2 :=
  fun e => c (e.map φ)

lemma map_symm_map {α β : Type*} (e : α ≃ β) (s : Sym2 α) : (s.map e).map e.symm = s := by
  rw [Sym2.map_map, show (⇑e.symm ∘ ⇑e) = id from by funext x; simp]
  exact congrFun Sym2.map_id s

lemma noTriG_resSym {α β : Type*} (e : α ≃ β) {c : Sym2 α → Fin 2} {i : Fin 2}
    (h : NoTriG c i) : NoTriG (resSym e.symm c) i := by
  intro x y z hxy hyz hxz ht
  exact h (e.symm x) (e.symm y) (e.symm z) (fun hh => hxy (e.symm.injective hh))
    (fun hh => hyz (e.symm.injective hh)) (fun hh => hxz (e.symm.injective hh)) ht

lemma resSym_symm_injective {α β : Type*} (e : α ≃ β) :
    Function.Injective (fun c : Sym2 α → Fin 2 => resSym e.symm c) := by
  intro c c' h
  funext s
  have hs := map_symm_map e s
  have h2 := congrFun h (s.map e)
  simpa [resSym, hs] using h2

lemma resSym_comp_self {α β : Type*} (e : α ≃ β) (c : Sym2 β → Fin 2) :
    resSym e.symm (resSym e c) = c := by
  funext s
  show c ((s.map e.symm).map e) = c s
  rw [Sym2.map_map, show (⇑e ∘ ⇑e.symm) = id from by funext x; simp, congrFun Sym2.map_id s]
  rfl

lemma card_noTriG_congr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (i : Fin 2) :
    Fintype.card {c : Sym2 α → Fin 2 // NoTriG c i} =
      Fintype.card {c : Sym2 β → Fin 2 // NoTriG c i} := by
  refine le_antisymm ?_ ?_
  · refine Fintype.card_le_of_injective
      (fun c => ⟨resSym e.symm c.1, noTriG_resSym e c.2⟩) ?_
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have h' : resSym e.symm c = resSym e.symm c' := congrArg Subtype.val h
    exact Subtype.ext (resSym_symm_injective e h')
  · refine Fintype.card_le_of_injective
      (fun c => ⟨resSym e c.1, ?_⟩) ?_
    · have h := noTriG_resSym e.symm c.2
      rwa [show (e.symm).symm = e from rfl] at h
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      have h' : resSym e c = resSym e c' := congrArg Subtype.val h
      have h2 : resSym e.symm (resSym e c) = resSym e.symm (resSym e c') := by rw [h']
      rw [resSym_comp_self, resSym_comp_self] at h2
      exact Subtype.ext h2

lemma noMono_iff_noTriG {M : ℕ} {c : Sym2 (Fin M) → Fin 2} {S : Finset (Fin M)} {i : Fin 2} :
    OMA.S_erdos_129.NoMonoTriangle c S i ↔ NoTriG (resSym (Subtype.val : ↥S → Fin M) c) i := by
  constructor
  · intro h x y z hxy hyz hxz ht
    exact h x.1 x.2 y.1 y.2 z.1 z.2 (fun h1 => hxy (Subtype.ext h1))
      (fun h1 => hyz (Subtype.ext h1)) (fun h1 => hxz (Subtype.ext h1)) ht
  · intro h x hx y hy z hz hxy hyz hxz ht
    exact h ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ (fun h1 => hxy (congrArg Subtype.val h1))
      (fun h1 => hyz (congrArg Subtype.val h1)) (fun h1 => hxz (congrArg Subtype.val h1)) ht

/-- Swapping the two colours. -/
def swapCol {α : Type*} (c : Sym2 α → Fin 2) : Sym2 α → Fin 2 :=
  fun e => if c e = 0 then 1 else 0

lemma swapVal_zero (a : Fin 2) : (if a = 0 then (1 : Fin 2) else 0) = 0 ↔ a = 1 := by
  constructor
  · intro h
    by_contra h1
    have h0 : a = 0 := by
      rcases fin_two_eq a with h2 | h2
      · exact h2
      · exact absurd h2 h1
    rw [if_pos h0] at h
    exact absurd h (by decide)
  · intro h; rw [h]; simp

lemma swapVal_one (a : Fin 2) : (if a = 0 then (1 : Fin 2) else 0) = 1 ↔ a = 0 := by
  constructor
  · intro h
    by_contra h1
    rw [if_neg h1] at h
    exact absurd h (by decide)
  · intro h; rw [h]; simp

lemma noTriG_swap {α : Type*} (c : Sym2 α → Fin 2) :
    NoTriG c 1 ↔ NoTriG (swapCol c) 0 := by
  constructor
  · intro h x y z hxy hyz hxz ht
    exact h x y z hxy hyz hxz ⟨(swapVal_zero _).mp ht.1, (swapVal_zero _).mp ht.2.1,
      (swapVal_zero _).mp ht.2.2⟩
  · intro h x y z hxy hyz hxz ht
    exact h x y z hxy hyz hxz ⟨(swapVal_zero _).mpr ht.1, (swapVal_zero _).mpr ht.2.1,
      (swapVal_zero _).mpr ht.2.2⟩

lemma swapCol_swapCol {α : Type*} (c : Sym2 α → Fin 2) : swapCol (swapCol c) = c := by
  funext e
  show (if (if c e = 0 then (1 : Fin 2) else 0) = 0 then 1 else 0) = c e
  by_cases h : c e = 0
  · rw [h]
    simp
  · rcases fin_two_eq (c e) with h0 | h1
    · exact absurd h0 h
    · rw [h1]
      simp

lemma card_noTriG_one {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card {c : Sym2 α → Fin 2 // NoTriG c 1} =
      Fintype.card {c : Sym2 α → Fin 2 // NoTriG c 0} := by
  have hb : Function.Bijective (swapCol : (Sym2 α → Fin 2) → (Sym2 α → Fin 2)) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨swapCol, swapCol_swapCol, swapCol_swapCol⟩
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective swapCol hb) ?_)
  intro c
  exact noTriG_swap c


/-! ### Cardinalities of symmetric squares -/

lemma card_sym2_fin (m : ℕ) : Fintype.card (Sym2 (Fin m)) = m * (m + 1) / 2 := by
  rw [← Finset.card_univ, ← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ,
    Fintype.card_fin]
  simp [Nat.choose_two_right, Nat.mul_comm]

def sym2_equiv_of_equiv {α β : Type*} (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun s := s.map e
  invFun s := s.map e.symm
  left_inv s := map_symm_map e s
  right_inv s := map_symm_map e.symm s

lemma card_sym2_eq (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (Sym2 α) = Fintype.card α * (Fintype.card α + 1) / 2 := by
  have h : Fintype.card (Sym2 α) = Fintype.card (Sym2 (Fin (Fintype.card α))) :=
    Fintype.card_congr (sym2_equiv_of_equiv (Fintype.equivFin α))
  rw [h, card_sym2_fin]

lemma card_sym2_coe {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    Fintype.card (Sym2 ↥S) = S.card * (S.card + 1) / 2 := by
  rw [card_sym2_eq, Fintype.card_coe]

/-- The red set of a colouring of `K_m` and the number of its colourings. -/
lemma T_eq (n : ℕ) : T n = Fintype.card {c : Sym2 (Fin n) → Fin 2 // NoTriG c 0} := rfl

theorem card_noTriG_eq_T {M n : ℕ} {S : Finset (Fin M)} (hS : S.card = n) (i : Fin 2) :
    Fintype.card {g : Sym2 ↥S → Fin 2 // NoTriG g i} = T n := by
  have hbase : T n = Fintype.card {c : Sym2 (Fin n) → Fin 2 // NoTriG c 0} := T_eq n
  rw [hbase]
  rcases fin_two_eq i with rfl | rfl
  · rw [← card_noTriG_congr (Finset.equivFinOfCardEq hS) 0]
  · rw [card_noTriG_one, ← card_noTriG_congr (Finset.equivFinOfCardEq hS) 0]

/-- **The fibre bound.**  At most `T n * 2^(E_M - E_n)` colourings of `K_M` agree with a
triangle-free colouring of an `n`-set and are free elsewhere. -/
theorem card_restrict_le {M : ℕ} (S : Finset (Fin M)) (i : Fin 2) :
    Fintype.card {c : Sym2 (Fin M) → Fin 2 // NoTriG (resSym (Subtype.val : ↥S → Fin M) c) i} ≤
      Fintype.card {g : Sym2 ↥S → Fin 2 // NoTriG g i} *
        2 ^ (Fintype.card (Sym2 (Fin M)) - Fintype.card (Sym2 ↥S)) := by
  classical
  set A : Finset (Sym2 (Fin M)) := Finset.univ.image (fun e : Sym2 ↥S => e.map Subtype.val) with hA
  have hAcard : A.card = Fintype.card (Sym2 ↥S) := by
    rw [hA, Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    simp
  let f : {c : Sym2 (Fin M) → Fin 2 // NoTriG (resSym (Subtype.val : ↥S → Fin M) c) i} →
      {g : Sym2 ↥S → Fin 2 // NoTriG g i} × (↥(Aᶜ) → Fin 2) :=
    fun c => (⟨resSym (Subtype.val : ↥S → Fin M) c.1, c.2⟩, fun e => c.1 e.1)
  have hinj : Function.Injective f := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have h1 : resSym (Subtype.val : ↥S → Fin M) c = resSym Subtype.val c' :=
      congrArg (fun p => p.1.val) h
    have h2 : (fun e : ↥(Aᶜ) => c e.1) = (fun e : ↥(Aᶜ) => c' e.1) := congrArg (fun p => p.2) h
    have hmain : ∀ e : Sym2 (Fin M), c e = c' e := by
      intro e
      by_cases he : e ∈ A
      · have he' : e ∈ Finset.univ.image (fun e : Sym2 ↥S => e.map Subtype.val) := by
          simpa [hA] using he
        obtain ⟨s, -, hs⟩ := Finset.mem_image.mp he'
        have h3 := congrFun h1 s
        rw [← hs]
        exact h3
      · have := congrFun h2 ⟨e, by simpa using he⟩
        exact this
    exact Subtype.ext (funext hmain)
  refine le_trans (Fintype.card_le_of_injective f hinj) ?_
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Finset.card_compl, hAcard,
    Fintype.card_fin]

/-- **The counting of one colour.**  For an `n`-set `S` and a colour `i`, at most
`T n * 2^(E_M - E_n)` colourings of `K_M` have no `i`-triangle inside `S`. -/
theorem card_noMono_le {M n : ℕ} {S : Finset (Fin M)} (hS : S.card = n) (i : Fin 2) :
    Fintype.card {c : Sym2 (Fin M) → Fin 2 // OMA.S_erdos_129.NoMonoTriangle c S i} ≤
      T n * 2 ^ (Fintype.card (Sym2 (Fin M)) - n * (n + 1) / 2) := by
  have h1 : Fintype.card {c : Sym2 (Fin M) → Fin 2 // OMA.S_erdos_129.NoMonoTriangle c S i} =
      Fintype.card {c : Sym2 (Fin M) → Fin 2 //
        NoTriG (resSym (Subtype.val : ↥S → Fin M) c) i} := by
    refine Fintype.card_congr (Equiv.subtypeEquivRight ?_)
    intro c
    exact noMono_iff_noTriG
  rw [h1]
  refine le_trans (card_restrict_le S i) ?_
  rw [card_noTriG_eq_T hS i, card_sym2_coe S, hS]

lemma exists_noMono_of_not_good {n M : ℕ} (c : Sym2 (Fin M) → Fin 2) (hc : ¬ Good n M c) :
    ∃ S : Finset (Fin M), S.card = n ∧ ∃ i : Fin 2, OMA.S_erdos_129.NoMonoTriangle c S i := by
  by_contra hh
  apply hc
  intro S hS i
  by_contra htri
  exact hh ⟨S, hS, i, fun x hx y hy z hz hxy hyz hxz ht =>
    htri ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, ht.1, ht.2.1, ht.2.2⟩⟩

/-- **Stage (v).**  The union bound. -/
theorem exists_good {M n : ℕ} (h : 2 * M ^ n * T n < 2 ^ (n * (n + 1) / 2)) :
    ∃ c : Sym2 (Fin M) → Fin 2, Good n M c := by
  classical
  rcases Nat.lt_or_ge M n with hlt | hge
  · refine ⟨fun _ => 0, ?_⟩
    intro S hS i
    have hcard : S.card ≤ M := by simpa using Finset.card_le_univ S
    omega
  · by_contra hcon
    have hcon' : ∀ c : Sym2 (Fin M) → Fin 2, ¬ Good n M c := by
      intro c hc
      exact hcon ⟨c, hc⟩
    -- every colouring is covered by a pair (S, i) with no i-triangle inside S
    set P : Finset (Finset (Fin M) × Fin 2) :=
      (Finset.univ.filter (fun S : Finset (Fin M) => S.card = n)) ×ˢ
        (Finset.univ : Finset (Fin 2)) with hP
    have hcover : (Finset.univ : Finset (Sym2 (Fin M) → Fin 2)) ⊆
        P.biUnion (fun p => Finset.univ.filter (fun c : Sym2 (Fin M) → Fin 2 =>
          OMA.S_erdos_129.NoMonoTriangle c p.1 p.2)) := by
      intro c _
      obtain ⟨S, hS, i, hi⟩ := exists_noMono_of_not_good c (hcon' c)
      exact Finset.mem_biUnion.mpr ⟨(S, i), by simp [hP, hS], by simpa using hi⟩
    have hbound : Fintype.card (Sym2 (Fin M) → Fin 2) ≤
        ∑ p ∈ P, Fintype.card {c : Sym2 (Fin M) → Fin 2 //
          OMA.S_erdos_129.NoMonoTriangle c p.1 p.2} := by
      rw [← Finset.card_univ]
      calc (Finset.univ : Finset (Sym2 (Fin M) → Fin 2)).card
          ≤ (P.biUnion (fun p => Finset.univ.filter (fun c : Sym2 (Fin M) → Fin 2 =>
              OMA.S_erdos_129.NoMonoTriangle c p.1 p.2))).card := Finset.card_le_card hcover
        _ ≤ ∑ p ∈ P, (Finset.univ.filter (fun c : Sym2 (Fin M) → Fin 2 =>
              OMA.S_erdos_129.NoMonoTriangle c p.1 p.2)).card := Finset.card_biUnion_le
        _ = ∑ p ∈ P, Fintype.card {c : Sym2 (Fin M) → Fin 2 //
              OMA.S_erdos_129.NoMonoTriangle c p.1 p.2} := by
            refine Finset.sum_congr rfl (fun p hp => ?_)
            rw [Fintype.card_subtype]
    have hterm : ∀ p ∈ P, Fintype.card {c : Sym2 (Fin M) → Fin 2 //
        OMA.S_erdos_129.NoMonoTriangle c p.1 p.2} ≤
        T n * 2 ^ (Fintype.card (Sym2 (Fin M)) - n * (n + 1) / 2) := by
      intro p hp
      have hpP : p ∈ (Finset.univ.filter (fun S : Finset (Fin M) => S.card = n)) ×ˢ
          (Finset.univ : Finset (Fin 2)) := by simpa [hP] using hp
      have hpS : p.1.card = n := by
        have h1 : p.1 ∈ Finset.univ.filter (fun S : Finset (Fin M) => S.card = n) :=
          (Finset.mem_product.mp hpP).1
        simpa using h1
      exact card_noMono_le hpS p.2
    have hsum : (∑ p ∈ P, Fintype.card {c : Sym2 (Fin M) → Fin 2 //
        OMA.S_erdos_129.NoMonoTriangle c p.1 p.2}) ≤
        P.card * (T n * 2 ^ (Fintype.card (Sym2 (Fin M)) - n * (n + 1) / 2)) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, smul_eq_mul]
    have hPcard : P.card = M.choose n * 2 := by
      rw [hP, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      congr 1
      have hpow : (Finset.univ.filter (fun S : Finset (Fin M) => S.card = n)) =
          Finset.powersetCard n (Finset.univ : Finset (Fin M)) := by
        ext S
        simp [Finset.mem_powersetCard]
      rw [hpow, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    -- the arithmetic
    set EM : ℕ := Fintype.card (Sym2 (Fin M)) with hEM
    set En : ℕ := n * (n + 1) / 2 with hEn
    have hEnEM : En ≤ EM := by
      rw [hEM, hEn, card_sym2_fin]
      have h1 : n ≤ M := hge
      have h2 : n * (n + 1) ≤ M * (M + 1) := Nat.mul_le_mul h1 (by omega)
      omega
    have hcardall : Fintype.card (Sym2 (Fin M) → Fin 2) = 2 ^ EM := by
      rw [Fintype.card_fun, Fintype.card_fin, hEM]
    have hmain : 2 ^ En * 2 ^ (EM - En) ≤ (2 * M.choose n * T n) * 2 ^ (EM - En) := by
      calc 2 ^ En * 2 ^ (EM - En) = 2 ^ EM := by rw [← pow_add, Nat.add_sub_cancel' hEnEM]
        _ = Fintype.card (Sym2 (Fin M) → Fin 2) := hcardall.symm
        _ ≤ P.card * (T n * 2 ^ (EM - En)) := by
            rw [hEM, hEn]
            exact le_trans hbound hsum
        _ = (2 * M.choose n * T n) * 2 ^ (EM - En) := by rw [hPcard]; ring
    have hcancel : 2 ^ En ≤ 2 * M.choose n * T n :=
      Nat.le_of_mul_le_mul_right hmain (by positivity)
    have hchoose : M.choose n ≤ M ^ n := Nat.choose_le_pow M n
    have : 2 * M ^ n * T n < 2 ^ En := by
      rw [hEn]; exact h
    nlinarith [hcancel, hchoose, Nat.zero_le (T n), this]


/-- **Stage (iii)+(ii)+(iv).**  The counting theorem, in the explicit form needed. -/
theorem T_bound (m : ℕ) (hm : 1 ≤ m) :
    (T (m + m) : ℝ) ≤ (2 : ℝ) ^ (m * (m + 1) / 2) *
      ((2 : ℝ) ^ (m * m) * (2 ^ m * (187 / 100 : ℝ) ^ (m * (m - 1) / 2))) := by
  have h1 : (T (m + m) : ℝ) ≤ (2 : ℝ) ^ (m * (m + 1) / 2) *
      ∑ cA : Sym2 (Fin m) → Fin 2, (ia cA : ℝ) ^ m := by
    have h := T_split m
    have h' : ((T (m + m) : ℕ) : ℝ) ≤ ((2 ^ (m * (m + 1) / 2) *
        ∑ cA : Sym2 (Fin m) → Fin 2, (ia cA) ^ m : ℕ) : ℝ) := by exact_mod_cast h
    calc (T (m + m) : ℝ) ≤ ((2 ^ (m * (m + 1) / 2) *
          ∑ cA : Sym2 (Fin m) → Fin 2, (ia cA) ^ m : ℕ) : ℝ) := h'
      _ = (2 : ℝ) ^ (m * (m + 1) / 2) *
          ∑ cA : Sym2 (Fin m) → Fin 2, (ia cA : ℝ) ^ m := by
          push_cast
          ring
  have h2 : (∑ cA : Sym2 (Fin m) → Fin 2, (ia cA : ℝ) ^ m) ≤
      (2 : ℝ) ^ (m * m) * ∑ cA : Sym2 (Fin m) → Fin 2, (87 / 100 : ℝ) ^ (redC cA) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro cA _
    have h := ia_pow_le cA (by rw [Fintype.card_fin]; omega)
    simpa [Fintype.card_fin] using h
  calc (T (m + m) : ℝ) ≤ (2 : ℝ) ^ (m * (m + 1) / 2) *
        ∑ cA : Sym2 (Fin m) → Fin 2, (ia cA : ℝ) ^ m := h1
    _ ≤ (2 : ℝ) ^ (m * (m + 1) / 2) * ((2 : ℝ) ^ (m * m) *
        ∑ cA : Sym2 (Fin m) → Fin 2, (87 / 100 : ℝ) ^ (redC cA)) := by gcongr
    _ = (2 : ℝ) ^ (m * (m + 1) / 2) *
        ((2 : ℝ) ^ (m * m) * (2 ^ m * (187 / 100 : ℝ) ^ (m * (m - 1) / 2))) := by
        rw [sum_redC]

lemma two_pow_three (a b c : ℕ) (x : ℝ) :
    (2 : ℝ) ^ a * ((2 : ℝ) ^ b * ((2 : ℝ) ^ c * x)) = (2 : ℝ) ^ (a + b + c) * x := by
  have e : (2 : ℝ) ^ (a + b + c) = (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c := by
    rw [pow_add, pow_add]
  rw [e]
  ring

lemma two_pow_two (a b : ℕ) (x : ℝ) :
    (2 : ℝ) ^ a * ((2 : ℝ) ^ b * x) = (2 : ℝ) ^ (a + b) * x := by
  rw [pow_add]
  ring

lemma two_pow_one (a : ℕ) (x : ℝ) :
    (2 : ℝ) ^ a * ((2 : ℝ) * x) = (2 : ℝ) ^ (a + 1) * x := by
  rw [pow_add]
  ring

/-- **The counting theorem for large even `n`.** -/
theorem T_le_pow (m : ℕ) (hm : 1000 ≤ m) :
    (T (m + m) : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2) := by
  have h := T_bound m (by omega)
  set K : ℕ := m * (m - 1) / 2 with hKdef
  have hKle : (K : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [hKdef]
    have h1 : ((m * (m - 1) / 2 : ℕ) : ℝ) ≤ ((m * (m - 1) : ℕ) : ℝ) / 2 :=
      Nat.cast_div_le
    have h2 : ((m * (m - 1) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ m by omega)]
      norm_num
    linarith
  -- split the power of `187/100`
  have hsplit : (187 / 100 : ℝ) ^ K ≤ (2 : ℝ) ^ (19 * (K / 20)) * (187 / 100 : ℝ) ^ 19 := by
    have h1 : (187 / 100 : ℝ) ^ 20 ≤ (2 : ℝ) ^ 19 := by norm_num
    have h2 : K = 20 * (K / 20) + K % 20 := (Nat.div_add_mod K 20).symm
    have h3 : K % 20 ≤ 19 := by have := Nat.mod_lt K (by norm_num : 0 < 20); omega
    calc (187 / 100 : ℝ) ^ K = (187 / 100 : ℝ) ^ (20 * (K / 20) + K % 20) := by
          conv_lhs => rw [h2]
      _ = (187 / 100 : ℝ) ^ (20 * (K / 20)) * (187 / 100 : ℝ) ^ (K % 20) :=
          pow_add _ _ _
      _ = ((187 / 100 : ℝ) ^ 20) ^ (K / 20) * (187 / 100 : ℝ) ^ (K % 20) := by
          rw [pow_mul]
      _ ≤ ((2 : ℝ) ^ 19) ^ (K / 20) * (187 / 100 : ℝ) ^ 19 := by
          exact mul_le_mul (pow_le_pow_left₀ (by norm_num) h1 _)
            (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 187 / 100) h3) (by positivity)
            (by positivity)
      _ = (2 : ℝ) ^ (19 * (K / 20)) * (187 / 100 : ℝ) ^ 19 := by rw [pow_mul]
  have h19 : (187 / 100 : ℝ) ^ 19 ≤ (2 : ℝ) ^ 18 := by norm_num
  have hexp : (((m * (m + 1) / 2 + m * m + m + 19 * (K / 20) + 18 : ℕ)) : ℝ) ≤
      (1 / 2 - 1 / 2000 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2 := by
    have hcast : (((m * (m + 1) / 2 + m * m + m + 19 * (K / 20) + 18 : ℕ)) : ℝ) =
        ((m * (m + 1) / 2 : ℕ) : ℝ) + ((m * m : ℕ) : ℝ) + (m : ℝ) +
          ((19 * (K / 20) : ℕ) : ℝ) + 18 := by
      push_cast
      ring
    rw [hcast]
    have hKle' : (K : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) / 2 := hKle
    have h1 : ((19 * (K / 20) : ℕ) : ℝ) ≤ 19 * (K : ℝ) / 20 := by
      have h2 : ((K / 20 : ℕ) : ℝ) ≤ (K : ℝ) / 20 := Nat.cast_div_le
      push_cast
      linarith
    have hA : ((m * (m + 1) / 2 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 / 2 + (m : ℝ) / 2 := by
      have h4 : ((m * (m + 1) / 2 : ℕ) : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 1) / 2 := by
        have h := Nat.cast_div_le (α := ℝ) (m := m * (m + 1)) (n := 2)
        rw [Nat.cast_mul] at h
        push_cast at h
        linarith
      nlinarith [h4]
    have hB : ((19 * (K / 20) : ℕ) : ℝ) ≤ 19 / 40 * (m : ℝ) ^ 2 := by
      nlinarith [h1, hKle']
    have h5 : ((m * m : ℕ) : ℝ) = (m : ℝ) ^ 2 := by
      rw [Nat.cast_mul]; ring
    have h6 : ((m + m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    have hm' : (1000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [h5, h6]
    nlinarith [hA, hB, hm']
  calc (T (m + m) : ℝ) ≤ (2 : ℝ) ^ (m * (m + 1) / 2) *
        ((2 : ℝ) ^ (m * m) * (2 ^ m * (187 / 100 : ℝ) ^ K)) := h
    _ = (2 : ℝ) ^ (m * (m + 1) / 2 + m * m + m) * (187 / 100 : ℝ) ^ K := by
        rw [two_pow_three]
    _ ≤ (2 : ℝ) ^ (m * (m + 1) / 2 + m * m + m) *
        ((2 : ℝ) ^ (19 * (K / 20)) * (187 / 100 : ℝ) ^ 19) := by gcongr
    _ = (2 : ℝ) ^ (m * (m + 1) / 2 + m * m + m + 19 * (K / 20)) *
        (187 / 100 : ℝ) ^ 19 := by
        rw [two_pow_two]
    _ ≤ (2 : ℝ) ^ (m * (m + 1) / 2 + m * m + m + 19 * (K / 20)) * (2 : ℝ) ^ 18 := by
        gcongr
    _ = (2 : ℝ) ^ (m * (m + 1) / 2 + m * m + m + 19 * (K / 20) + 18) := by
        rw [← pow_add]
    _ = (2 : ℝ) ^ (((m * (m + 1) / 2 + m * m + m + 19 * (K / 20) + 18 : ℕ)) : ℝ) := by
        rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * ((m + m : ℕ) : ℝ) ^ 2) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp


/-- Pull a good colouring back along an injection of vertex sets. -/
theorem restrict_good_aux {n M N : ℕ} (hNM : N ≤ M) (c : Sym2 (Fin M) → Fin 2)
    (hc : Good n M c) : ∃ c' : Sym2 (Fin N) → Fin 2, Good n N c' := by
  classical
  refine ⟨fun e => c (e.map (fun i => (⟨i.1, lt_of_lt_of_le i.2 hNM⟩ : Fin M))), ?_⟩
  intro S hS i
  have hinj : Function.Injective (fun i : Fin N => (⟨i.1, lt_of_lt_of_le i.2 hNM⟩ : Fin M)) := by
    intro a b hab
    have h : (a : ℕ) = (b : ℕ) := congrArg (fun x : Fin M => (x : ℕ)) hab
    exact Fin.ext h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hcxy, hcyz, hcxz⟩ :=
    hc (S.image (fun i : Fin N => (⟨i.1, lt_of_lt_of_le i.2 hNM⟩ : Fin M)))
      (by rw [Finset.card_image_of_injective _ hinj]; exact hS) i
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
  refine ⟨x', hx', y', hy', z', hz', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hxy (by rw [h])
  · intro h; exact hyz (by rw [h])
  · intro h; exact hxz (by rw [h])
  · simpa [Sym2.map_mk] using hcxy
  · simpa [Sym2.map_mk] using hcyz
  · simpa [Sym2.map_mk] using hcxz

/-- **Stage (vi): the asymptotics.**  For every `C > 1` there is an even `n` at which the
union bound applies. -/
theorem exists_large (C : ℝ) (hC1 : 1 < C) :
    ∃ m : ℕ, 1000 ≤ m ∧
      2 * (Nat.floor (C ^ Real.sqrt ((m + m : ℕ) : ℝ)) + 1) ^ (m + m) * T (m + m)
        < 2 ^ ((m + m) * (m + m + 1) / 2) := by
  set L : ℝ := Real.logb 2 C with hL
  have hL0 : 0 < L := Real.logb_pos (by norm_num) hC1
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max 4000 ((4000 * (L + 1)) ^ 2))
  refine ⟨max N₀ 2000, by omega, ?_⟩
  set m : ℕ := max N₀ 2000 with hm
  set n : ℕ := m + m with hn
  have hm2000 : 2000 ≤ m := le_max_right _ _
  have hm1000 : 1000 ≤ m := by omega
  have hn4000 : 4000 ≤ n := by rw [hn]; omega
  have hN₀' : (4000 : ℝ) < (N₀ : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN₀
  have hN₀'' : ((4000 * (L + 1)) ^ 2 : ℝ) < (N₀ : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN₀
  have hmge : (N₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_left N₀ 2000
  have hnge : (N₀ : ℝ) ≤ (n : ℝ) := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by rw [hn]; push_cast; linarith
    linarith
  -- the counting theorem
  have hT : (T n : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) := by
    rw [hn]; exact T_le_pow m hm1000
  -- `C = 2 ^ L`
  have hCeq : C = (2 : ℝ) ^ L :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
  -- `4000 L ≤ sqrt n`
  have hLle : (4000 : ℝ) * L ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h2 : ((4000 * L) ^ 2 : ℝ) ≤ (4000 * (L + 1)) ^ 2 := by
      have h3 : (0:ℝ) ≤ 4000 * L := by positivity
      nlinarith
    linarith
  -- `M ≤ 2 * C ^ sqrt n`
  have hMle : ((Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1 : ℕ) : ℝ) ≤ 2 * C ^ Real.sqrt (n : ℝ) := by
    have h1 : ((Nat.floor (C ^ Real.sqrt (n : ℝ)) : ℕ) : ℝ) ≤ C ^ Real.sqrt (n : ℝ) :=
      Nat.floor_le (by positivity)
    have h2 : (1 : ℝ) ≤ C ^ Real.sqrt (n : ℝ) :=
      Real.one_le_rpow hC1.le (Real.sqrt_nonneg _)
    push_cast
    linarith
  -- the estimate on `M ^ n`
  have hMn : (((Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1 : ℕ) : ℝ)) ^ n ≤
      (2 * C ^ Real.sqrt (n : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) hMle n
  have hCsplit : (2 * C ^ Real.sqrt (n : ℝ)) ^ n =
      (2:ℝ) ^ n * (2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) := by
    have h1 : C ^ Real.sqrt (n:ℝ) = (2:ℝ) ^ (L * Real.sqrt (n:ℝ)) := by
      rw [hCeq, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [mul_pow, h1]
    have h2 : ((2:ℝ) ^ (L * Real.sqrt (n:ℝ))) ^ n =
        (2:ℝ) ^ (L * (Real.sqrt (n:ℝ) * n)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    rw [h2]
  -- the exponent bound for the `C`-part
  have hexpC : L * (Real.sqrt (n : ℝ) * n) ≤ (1 / 2000 / 2) * (n : ℝ) ^ 2 := by
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    have h3 : L ≤ Real.sqrt (n:ℝ) / 4000 := by linarith [hLle]
    have h4 : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
      rw [← pow_two]; exact Real.sq_sqrt hn0
    have h7 : (0:ℝ) ≤ Real.sqrt (n:ℝ) * n := by positivity
    have h5 : L * (Real.sqrt (n:ℝ) * n) ≤ (Real.sqrt (n:ℝ) / 4000) * (Real.sqrt (n:ℝ) * n) := by
      nlinarith [h3, h7]
    have h8 : (Real.sqrt (n:ℝ) / 4000) * (Real.sqrt (n:ℝ) * n) = (n:ℝ)^2/4000 := by
      calc (Real.sqrt (n:ℝ) / 4000) * (Real.sqrt (n:ℝ) * n)
          = (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) * n / 4000 := by ring
        _ = (n:ℝ) * n / 4000 := by rw [h4]
        _ = (n:ℝ)^2/4000 := by ring
    rw [h8] at h5
    have h9 : (1 / 2000 / 2 : ℝ) = 1/4000 := by norm_num
    rw [h9]
    linarith [h5]
  have hfinal : 2 * (2:ℝ) ^ n * (2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) *
      (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) < (2:ℝ) ^ (n * (n + 1) / 2) := by
    have h1 : (2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) ≤ (2:ℝ) ^ ((1 / 2000 / 2) * (n:ℝ)^2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpC
    have hstep : 2 * (2:ℝ) ^ n * (2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) *
        (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) ≤
        (2:ℝ) ^ ((1:ℝ) + (n:ℝ) + (1 / 2000 / 2) * (n:ℝ)^2 +
          (1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) := by
      have h2 : (2 * (2:ℝ) ^ n) = (2:ℝ) ^ ((1:ℝ) + (n:ℝ)) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast]
      have h3 : (2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) * (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2)
          ≤ (2:ℝ) ^ ((1 / 2000 / 2) * (n:ℝ)^2) * (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) := by
        exact mul_le_mul h1 (le_refl _) (by positivity) (by positivity)
      rw [show 2 * (2:ℝ) ^ n * (2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) *
          (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2)
          = (2 * (2:ℝ) ^ n) * ((2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) *
            (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2)) from by ring]
      rw [h2]
      refine le_trans (mul_le_mul (le_refl _) h3 (by positivity) (by positivity)) ?_
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
      ring_nf
      exact le_refl _
    refine lt_of_le_of_lt hstep ?_
    have hnc : ((n * (n + 1) / 2 : ℕ) : ℝ) = (n:ℝ) * ((n:ℝ) + 1) / 2 := by
      have h1 : n * (n + 1) = 2 * (m * (2 * m + 1)) := by
        rw [hn]; ring
      rw [h1, Nat.mul_div_right _ (by norm_num : 0 < 2), hn]
      push_cast
      ring
    rw [← Real.rpow_natCast (2:ℝ) (n * (n + 1) / 2), hnc]
    refine Real.rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) ?_
    have h4 : (4000:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4000
    have h5 : (n:ℝ) * ((n:ℝ) + 1) / 2 = (n:ℝ)^2/2 + (n:ℝ)/2 := by ring
    rw [h5]
    nlinarith [h4]
  have hreal : (2 : ℝ) * ((Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1 : ℕ) : ℝ) ^ n * (T n : ℝ) <
      (2 : ℝ) ^ (n * (n + 1) / 2) := by
    calc (2 : ℝ) * ((Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1 : ℕ) : ℝ) ^ n * (T n : ℝ)
        ≤ 2 * (2 * C ^ Real.sqrt (n : ℝ)) ^ n *
            (2 : ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) := by
          have h1 : (0:ℝ) ≤ ((Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1 : ℕ) : ℝ) ^ n := by
            positivity
          have h2 : (0:ℝ) < (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) := by positivity
          nlinarith [hMn, hT, h1, h2]
      _ = 2 * (2:ℝ) ^ n * (2:ℝ) ^ (L * (Real.sqrt (n : ℝ) * n)) *
            (2:ℝ) ^ ((1 / 2 - 1 / 2000 : ℝ) * (n : ℝ) ^ 2) := by rw [hCsplit]; ring
      _ < (2:ℝ) ^ (n * (n + 1) / 2) := hfinal
  have hcast : ((2 * (Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1) ^ n * T n : ℕ) : ℝ) <
      ((2 ^ (n * (n + 1) / 2) : ℕ) : ℝ) := by
    rw [show ((2 * (Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1) ^ n * T n : ℕ) : ℝ) =
        2 * ((Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1 : ℕ) : ℝ) ^ n * (T n : ℝ) from by
      push_cast; ring]
    rw [Nat.cast_pow]
    exact hreal
  exact_mod_cast hcast

/-- The negation of the statement, with the counting and the union bound assembled. -/
theorem disproof_aux : ¬ (type_of% @OMA.S_erdos_129.main) := by
  intro h
  obtain ⟨C, hC1, hC⟩ := h 2 (by norm_num)
  obtain ⟨m, hm, hlt⟩ := exists_large C hC1
  set n : ℕ := m + m with hn
  set M : ℕ := Nat.floor (C ^ Real.sqrt (n : ℝ)) + 1 with hM
  obtain ⟨c, hc⟩ := exists_good hlt
  obtain ⟨N, hNlt, hN⟩ := hC n
  have hNM : N ≤ M := by
    have h1 : (N : ℝ) < C ^ Real.sqrt (n : ℝ) := hNlt
    have h2 : (N : ℝ) < (Nat.floor (C ^ Real.sqrt (n : ℝ)) : ℝ) + 1 := by
      have h3 : C ^ Real.sqrt (n : ℝ) < ((Nat.floor (C ^ Real.sqrt (n : ℝ)) : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith [h1, h3]
    have h3 : N < M := by
      rw [hM]
      exact_mod_cast h2
    omega
  obtain ⟨c', hc'⟩ := restrict_good_aux hNM c hc
  obtain ⟨S, hS, i, hi⟩ := hN c'
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, h1, h2, h3⟩ := hc' S hS i
  exact hi x hx y hy z hz hxy hyz hxz ⟨h1, h2, h3⟩

end E129

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_129.main) := E129.disproof_aux
