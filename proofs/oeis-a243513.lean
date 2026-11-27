import OMAStatements.S_oeis_a243513

namespace OMA.P_oeis_a243513
open Classical

private def inZ {m : ℕ} (w : Fin m → Fin 5) : Prop :=
  ∀ i, (w i).val = 0

private def inS1 {m : ℕ} (w : Fin m → Fin 5) : Prop :=
  (∃ i, (w i).val = 1) ∧ ∀ i, (w i).val ≤ 1

private def inS2 {m : ℕ} (w : Fin m → Fin 5) : Prop :=
  (∃ i, (w i).val = 2) ∧ ∀ i, (w i).val ≤ 2

private def inS34 {m : ℕ} (w : Fin m → Fin 5) : Prop :=
  ∃ i, 3 ≤ (w i).val

private lemma validWord_zero {n : ℕ} {w : Fin (n + 1) → Fin 5}
    (hw : OMA.S_oeis_a243513.validWord w) : (w 0).val = 0 := by
  by_contra h0
  obtain ⟨j, hj, _⟩ := hw.1 0 (Nat.pos_of_ne_zero h0)
  have hj0 : j.val < 0 := hj
  omega

private lemma validWord_exists_of_le {m : ℕ} {w : Fin m → Fin 5}
    (hw : OMA.S_oeis_a243513.validWord w) :
    ∀ d : ℕ, ∀ (k : ℕ) (i : Fin m), (w i).val = k + d →
      ∃ j : Fin m, j ≤ i ∧ (w j).val = k := by
  intro d
  induction d with
  | zero =>
    intro k i hi
    exact ⟨i, le_rfl, by simpa using hi⟩
  | succ d ih =>
    intro k i hi
    have hpos : 0 < (w i).val := by omega
    obtain ⟨j', hj'i, hj'val⟩ := hw.1 i hpos
    have hkd : (w j').val = k + d := by omega
    obtain ⟨j, hjj', hjval⟩ := ih k j' hkd
    exact ⟨j, le_trans hjj' (le_of_lt hj'i), hjval⟩

private lemma validWord_last_ne {n : ℕ} {w : Fin (n + 2) → Fin 5}
    (hw : OMA.S_oeis_a243513.validWord w) (hne : ∃ i, (w i).val ≠ 0) :
    w ⟨n, by omega⟩ ≠ w ⟨n + 1, by omega⟩ := by
  have step : ∀ k : ℕ, ∀ hk : k < n + 2, 1 ≤ k →
      (∃ i : Fin (n + 2), i.val ≤ k ∧ (w i).val ≠ 0) →
      w ⟨k - 1, by omega⟩ ≠ w ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro _ h1; omega
    | succ k ih =>
      intro hk _ hne_k
      by_cases hprev : ∀ i : Fin (n + 2), i.val ≤ k → (w i).val = 0
      · obtain ⟨i, hik, hi0⟩ := hne_k
        have hik_eq : i.val = k + 1 := by
          by_contra hlt
          exact hi0 (hprev i (by omega))
        have hw_k : (w ⟨k, by omega⟩).val = 0 := hprev ⟨k, by omega⟩ (by dsimp; omega)
        have hw_k1 : (w ⟨k + 1, hk⟩).val ≠ 0 := by
          have hidx : i = ⟨k + 1, hk⟩ := Fin.ext hik_eq
          rw [← hidx]
          exact hi0
        intro heq
        apply hw_k1
        have hval := congrArg Fin.val heq
        dsimp at hval
        omega
      · have hk1 : 1 ≤ k := by
          by_contra hk0
          apply hprev
          intro i hik
          have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
          subst hi0
          exact validWord_zero hw
        have hex : ∃ i : Fin (n + 2), i.val ≤ k ∧ (w i).val ≠ 0 := by
          by_contra hnone
          apply hprev
          intro i hik
          by_contra hi0
          exact hnone ⟨i, hik, hi0⟩
        have hih := ih (by omega) hk1 hex
        have hj_eq : (⟨k, by omega⟩ : Fin (n + 2)).val = (⟨k - 1, by omega⟩ : Fin (n + 2)).val + 1 := by
          dsimp; omega
        have hk_eq : (⟨k + 1, hk⟩ : Fin (n + 2)).val = (⟨k, by omega⟩ : Fin (n + 2)).val + 1 := rfl
        have h2 := hw.2 ⟨k - 1, by omega⟩ ⟨k, by omega⟩ ⟨k + 1, hk⟩ hj_eq hk_eq hih
        exact h2.2.symm
  exact step (n + 1) (by omega) (by omega) (by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by omega, hi⟩)

private lemma validWord_init {m : ℕ} {w : Fin (m + 1) → Fin 5}
    (hw : OMA.S_oeis_a243513.validWord w) : OMA.S_oeis_a243513.validWord (Fin.init w) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨j, hji, hjval⟩ := hw.1 i.castSucc hi
    let j' : Fin m := ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩
    have hj'_eq : j'.castSucc = j := Fin.ext rfl
    refine ⟨j', ?_, ?_⟩
    · change j'.val < i.val; exact hji
    · dsimp only [Fin.init]; rw [hj'_eq]; exact hjval
  · intro i j k hij hjk hne
    exact hw.2 i.castSucc j.castSucc k.castSucc hij hjk hne

private lemma validWord_snoc_iff {n : ℕ} (u : Fin (n + 2) → Fin 5) (c : Fin 5) :
    OMA.S_oeis_a243513.validWord (Fin.snoc u c) ↔
      OMA.S_oeis_a243513.validWord u ∧
      (0 < c.val → ∃ j : Fin (n + 2), (u j).val + 1 = c.val) ∧
      (u ⟨n, by omega⟩ ≠ u ⟨n + 1, by omega⟩ →
        c ≠ u ⟨n, by omega⟩ ∧ c ≠ u ⟨n + 1, by omega⟩) := by
  constructor
  · intro hw
    have hinit : OMA.S_oeis_a243513.validWord u := by
      have h0 := validWord_init (m := n + 2) (w := (Fin.snoc u c : Fin (n + 3) → Fin 5)) hw
      rwa [Fin.init_snoc] at h0
    refine ⟨hinit, ?_, ?_⟩
    · intro hc
      obtain ⟨j, hj, hjval⟩ := hw.1 (Fin.last (n + 2)) (by simpa [Fin.snoc_last] using hc)
      have hj_lt : j.val < n + 2 := by
        change j.val < (Fin.last (n + 2)).val at hj
        rw [Fin.val_last] at hj
        exact hj
      let j' : Fin (n + 2) := ⟨j.val, hj_lt⟩
      have hj_eq : j = j'.castSucc := Fin.ext rfl
      refine ⟨j', ?_⟩
      rw [hj_eq, Fin.snoc_castSucc, Fin.snoc_last] at hjval
      exact hjval
    · intro hne
      let i0 : Fin (n + 2) := ⟨n, by omega⟩
      let j0 : Fin (n + 2) := ⟨n + 1, by omega⟩
      have h2 := hw.2 i0.castSucc j0.castSucc (Fin.last (n + 2))
        (by simp [i0, j0]) (by simp [j0, Fin.val_last])
        (by simpa [Fin.snoc_castSucc] using hne)
      simpa [Fin.snoc_castSucc, Fin.snoc_last] using h2
  · rintro ⟨hu, h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hil : i.val < n + 2
      · let i' : Fin (n + 2) := ⟨i.val, hil⟩
        have hieq : i = i'.castSucc := Fin.ext rfl
        rw [hieq, Fin.snoc_castSucc] at hi
        obtain ⟨j, hji, hjval⟩ := hu.1 i' hi
        refine ⟨j.castSucc, hji, ?_⟩
        rw [hieq, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hjval
      · have hieq : i = Fin.last (n + 2) :=
          Fin.ext (by have := i.isLt; rw [Fin.val_last]; omega)
        subst hieq
        rw [Fin.snoc_last] at hi ⊢
        obtain ⟨j, hjval⟩ := h1 hi
        refine ⟨j.castSucc, ?_, ?_⟩
        · change j.val < (Fin.last (n + 2)).val
          rw [Fin.val_last]
          exact j.isLt
        · rw [Fin.snoc_castSucc]
          exact hjval
    · intro i j k hij hjk hne
      by_cases hkl : k.val < n + 2
      · let i' : Fin (n + 2) := ⟨i.val, by omega⟩
        let j' : Fin (n + 2) := ⟨j.val, by omega⟩
        let k' : Fin (n + 2) := ⟨k.val, hkl⟩
        have hieq : i = i'.castSucc := Fin.ext rfl
        have hjeq : j = j'.castSucc := Fin.ext rfl
        have hkeq : k = k'.castSucc := Fin.ext rfl
        have hne' : u i' ≠ u j' := by
          rw [hieq, hjeq, Fin.snoc_castSucc, Fin.snoc_castSucc] at hne
          exact hne
        rw [hieq, hjeq, hkeq, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hu.2 i' j' k' hij hjk hne'
      · let i0 : Fin (n + 2) := ⟨n, by omega⟩
        let j0 : Fin (n + 2) := ⟨n + 1, by omega⟩
        have hkeq : k = Fin.last (n + 2) :=
          Fin.ext (by have := k.isLt; rw [Fin.val_last]; omega)
        have hkj : k.val = n + 2 := by rw [hkeq, Fin.val_last]
        have hieq : i = i0.castSucc := Fin.ext (by dsimp [i0]; omega)
        have hjeq : j = j0.castSucc := Fin.ext (by dsimp [j0]; omega)
        have hne' : u i0 ≠ u j0 := by
          rw [hieq, hjeq, Fin.snoc_castSucc, Fin.snoc_castSucc] at hne
          exact hne
        rw [hieq, hjeq, hkeq, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
        exact h2 hne'

private noncomputable def W (n : ℕ) : Finset (Fin (n + 2) → Fin 5) :=
  Finset.univ.filter OMA.S_oeis_a243513.validWord

private noncomputable def Z (n : ℕ) : Finset (Fin (n + 2) → Fin 5) := (W n).filter inZ
private noncomputable def S1 (n : ℕ) : Finset (Fin (n + 2) → Fin 5) := (W n).filter inS1
private noncomputable def S2 (n : ℕ) : Finset (Fin (n + 2) → Fin 5) := (W n).filter inS2
private noncomputable def S34 (n : ℕ) : Finset (Fin (n + 2) → Fin 5) := (W n).filter inS34

private lemma count_eq_W_card (n : ℕ) : OMA.S_oeis_a243513.count n = (W n).card := by
  rw [OMA.S_oeis_a243513.count, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private lemma W_card_split (n : ℕ) :
    (W n).card = (Z n).card + (S1 n).card + (S2 n).card + (S34 n).card := by
  have huniv : ∀ w : Fin (n + 2) → Fin 5,
      inZ w ∨ inS1 w ∨ inS2 w ∨ inS34 w := by
    intro w
    by_cases h3 : ∃ i, 3 ≤ (w i).val
    · right; right; right; exact h3
    · have hle2 : ∀ i, (w i).val ≤ 2 := by
        intro i
        by_contra hgt
        exact h3 ⟨i, by omega⟩
      by_cases h2 : ∃ i, (w i).val = 2
      · right; right; left; exact ⟨h2, hle2⟩
      · have hle1 : ∀ i, (w i).val ≤ 1 := by
          intro i
          by_contra hgt
          have : (w i).val = 2 := by have := hle2 i; omega
          exact h2 ⟨i, this⟩
        by_cases h1 : ∃ i, (w i).val = 1
        · right; left; exact ⟨h1, hle1⟩
        · left
          intro i
          by_contra h0
          have : (w i).val = 1 := by have := hle1 i; omega
          exact h1 ⟨i, this⟩
  have hEq : W n = Z n ∪ S1 n ∪ S2 n ∪ S34 n := by
    ext w
    simp only [Z, S1, S2, S34, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hw
      rcases huniv w with h | h | h | h
      · left; left; left; exact ⟨hw, h⟩
      · left; left; right; exact ⟨hw, h⟩
      · left; right; exact ⟨hw, h⟩
      · right; exact ⟨hw, h⟩
    · rintro (((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨hw, _⟩) | ⟨hw, _⟩) <;> exact hw
  have hdZ1 : Disjoint (Z n) (S1 n) := by
    rw [Finset.disjoint_left]
    rintro w hZ hS
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hS).2.1
    have := (Finset.mem_filter.mp hZ).2 i
    omega
  have hdZ12 : Disjoint (Z n ∪ S1 n) (S2 n) := by
    rw [Finset.disjoint_left]
    rintro w hZS hS2
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hS2).2.1
    rcases Finset.mem_union.mp hZS with hZ | hS1
    · have := (Finset.mem_filter.mp hZ).2 i; omega
    · have := (Finset.mem_filter.mp hS1).2.2 i; omega
  have hdZ123 : Disjoint (Z n ∪ S1 n ∪ S2 n) (S34 n) := by
    rw [Finset.disjoint_left]
    rintro w hZ12 hS34
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hS34).2
    rcases Finset.mem_union.mp hZ12 with hZS | hS2
    · rcases Finset.mem_union.mp hZS with hZ | hS1
      · have := (Finset.mem_filter.mp hZ).2 i; omega
      · have := (Finset.mem_filter.mp hS1).2.2 i; omega
    · have := (Finset.mem_filter.mp hS2).2.2 i; omega
  rw [hEq, Finset.card_union_of_disjoint hdZ123, Finset.card_union_of_disjoint hdZ12,
    Finset.card_union_of_disjoint hdZ1]

private lemma card_filter_snoc (n : ℕ) (P : (Fin (n + 3) → Fin 5) → Prop) :
    ((W (n + 1)).filter P).card =
      ∑ u ∈ W n, (Finset.univ.filter (fun c : Fin 5 =>
        OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ P (Fin.snoc u c))).card := by
  let S := (W n).sigma (fun u =>
    Finset.univ.filter (fun c : Fin 5 =>
      OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ P (Fin.snoc u c)))
  have hbij : S.card = ((W (n + 1)).filter P).card := by
    refine Finset.card_bij (fun p _ => Fin.snoc p.1 p.2) ?_ ?_ ?_
    · intro ⟨u, c⟩ hp
      simp only [S, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.2
    · intro ⟨u1, c1⟩ _ ⟨u2, c2⟩ _ heq
      obtain ⟨hu, hc⟩ := Fin.snoc_inj.mp heq
      subst hu hc
      rfl
    · intro w hw
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨⟨Fin.init w, w (Fin.last (n + 2))⟩, ?_, Fin.snoc_init_self w⟩
      simp only [S, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
        W, Fin.snoc_init_self]
      exact ⟨validWord_init hw.1, hw⟩
  rw [← hbij, Finset.card_sigma]

private lemma inZ_snoc {m : ℕ} (u : Fin m → Fin 5) (c : Fin 5) :
    inZ (Fin.snoc u c : Fin (m + 1) → Fin 5) ↔ inZ u ∧ c = 0 := by
  constructor
  · intro h
    refine ⟨fun i => ?_, Fin.ext (by simpa [Fin.snoc_last] using h (Fin.last m))⟩
    simpa [Fin.snoc_castSucc] using h i.castSucc
  · rintro ⟨hu, rfl⟩ i
    by_cases hil : i.val < m
    · let i' : Fin m := ⟨i.val, hil⟩
      have hieq : i = i'.castSucc := Fin.ext rfl
      rw [hieq, Fin.snoc_castSucc]
      exact hu i'
    · have hieq : i = Fin.last m := Fin.ext (by have := i.isLt; rw [Fin.val_last]; omega)
      subst hieq
      simp [Fin.snoc_last]

private lemma forall_le_snoc {m : ℕ} (u : Fin m → Fin 5) (c : Fin 5) (k : ℕ) :
    (∀ i, ((Fin.snoc u c : Fin (m + 1) → Fin 5) i).val ≤ k) ↔
      (∀ i, (u i).val ≤ k) ∧ c.val ≤ k := by
  constructor
  · intro h
    refine ⟨fun i => by simpa [Fin.snoc_castSucc] using h i.castSucc,
      by simpa [Fin.snoc_last] using h (Fin.last m)⟩
  · rintro ⟨hu, hc⟩ i
    by_cases hil : i.val < m
    · let i' : Fin m := ⟨i.val, hil⟩
      have hieq : i = i'.castSucc := Fin.ext rfl
      rw [hieq, Fin.snoc_castSucc]
      exact hu i'
    · have hieq : i = Fin.last m := Fin.ext (by have := i.isLt; rw [Fin.val_last]; omega)
      subst hieq
      simpa [Fin.snoc_last] using hc

private lemma exists_eq_snoc {m : ℕ} (u : Fin m → Fin 5) (c : Fin 5) (k : ℕ) :
    (∃ i, ((Fin.snoc u c : Fin (m + 1) → Fin 5) i).val = k) ↔
      (∃ i, (u i).val = k) ∨ c.val = k := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases hil : i.val < m
    · let i' : Fin m := ⟨i.val, hil⟩
      have hieq : i = i'.castSucc := Fin.ext rfl
      rw [hieq, Fin.snoc_castSucc] at hi
      left; exact ⟨i', hi⟩
    · have hieq : i = Fin.last m := Fin.ext (by have := i.isLt; rw [Fin.val_last]; omega)
      subst hieq
      right; simpa [Fin.snoc_last] using hi
  · rintro (⟨i, hi⟩ | hc)
    · exact ⟨i.castSucc, by simpa [Fin.snoc_castSucc] using hi⟩
    · exact ⟨Fin.last m, by simpa [Fin.snoc_last] using hc⟩

private lemma exists_ge_snoc {m : ℕ} (u : Fin m → Fin 5) (c : Fin 5) (k : ℕ) :
    (∃ i, k ≤ ((Fin.snoc u c : Fin (m + 1) → Fin 5) i).val) ↔
      (∃ i, k ≤ (u i).val) ∨ k ≤ c.val := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases hil : i.val < m
    · let i' : Fin m := ⟨i.val, hil⟩
      have hieq : i = i'.castSucc := Fin.ext rfl
      rw [hieq, Fin.snoc_castSucc] at hi
      left; exact ⟨i', hi⟩
    · have hieq : i = Fin.last m := Fin.ext (by have := i.isLt; rw [Fin.val_last]; omega)
      subst hieq
      right; simpa [Fin.snoc_last] using hi
  · rintro (⟨i, hi⟩ | hc)
    · exact ⟨i.castSucc, by simpa [Fin.snoc_castSucc] using hi⟩
    · exact ⟨Fin.last m, by simpa [Fin.snoc_last] using hc⟩

private lemma card_Z_succ (n : ℕ) : (Z (n + 1)).card = (Z n).card := by
  rw [Z, card_filter_snoc]
  have hsum : ∀ u ∈ W n,
      (Finset.univ.filter (fun c : Fin 5 =>
        OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inZ (Fin.snoc u c))).card =
        if inZ u then 1 else 0 := by
    intro u hu
    have hvu : OMA.S_oeis_a243513.validWord u := (Finset.mem_filter.mp hu).2
    by_cases hZ : inZ u
    · simp only [hZ, ↓reduceIte]
      have hEq : Finset.univ.filter (fun c : Fin 5 =>
          OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inZ (Fin.snoc u c)) = {0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          validWord_snoc_iff, inZ_snoc]
        constructor
        · rintro ⟨_, _, hc⟩; exact hc
        · rintro rfl
          refine ⟨⟨hvu, fun h => absurd h (by decide), fun h => ?_⟩, hZ, rfl⟩
          exfalso
          have h1 := hZ ⟨n, by omega⟩
          have h2 := hZ ⟨n + 1, by omega⟩
          exact h (Fin.ext (by omega))
      rw [hEq, Finset.card_singleton]
    · simp only [hZ, ↓reduceIte]
      have hEq : Finset.univ.filter (fun c : Fin 5 =>
          OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inZ (Fin.snoc u c)) = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and, inZ_snoc]
        intro _ hzu _
        exact hZ hzu
      rw [hEq, Finset.card_empty]
  rw [Finset.sum_congr rfl hsum, Finset.sum_boole, Nat.cast_id]
  rfl

private lemma card_S1_succ (n : ℕ) : (S1 (n + 1)).card = (Z n).card := by
  rw [S1, card_filter_snoc]
  have hsum : ∀ u ∈ W n,
      (Finset.univ.filter (fun c : Fin 5 =>
        OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS1 (Fin.snoc u c))).card =
        if inZ u then 1 else 0 := by
    intro u hu
    have hvu : OMA.S_oeis_a243513.validWord u := (Finset.mem_filter.mp hu).2
    by_cases hZ : inZ u
    · simp only [hZ, ↓reduceIte]
      have hEq : Finset.univ.filter (fun c : Fin 5 =>
          OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS1 (Fin.snoc u c)) = {1} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          validWord_snoc_iff, inS1, exists_eq_snoc, forall_le_snoc]
        constructor
        · rintro ⟨_, (⟨i, hi⟩ | hc1), _, _⟩
          · have := hZ i; omega
          · exact Fin.ext hc1
        · rintro rfl
          refine ⟨⟨hvu, fun _ => ⟨0, by rw [hZ 0]; decide⟩, fun h => ?_⟩,
            Or.inr rfl, fun i => by rw [hZ i]; decide, by decide⟩
          exfalso
          have h1 := hZ ⟨n, by omega⟩
          have h2 := hZ ⟨n + 1, by omega⟩
          exact h (Fin.ext (by omega))
      rw [hEq, Finset.card_singleton]
    · simp only [hZ, ↓reduceIte]
      have hEq : Finset.univ.filter (fun c : Fin 5 =>
          OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS1 (Fin.snoc u c)) = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and, validWord_snoc_iff, inS1, exists_eq_snoc, forall_le_snoc]
        rintro ⟨_, _, hne⟩ _ hu_le1 hc_le1
        have hne_u : ∃ i, (u i).val ≠ 0 := by
          by_contra hz
          apply hZ
          intro i
          by_contra hi
          exact hz ⟨i, hi⟩
        have hlast := validWord_last_ne hvu hne_u
        obtain ⟨hcn, hcn1⟩ := hne hlast
        have hn_le := hu_le1 ⟨n, by omega⟩
        have hn1_le := hu_le1 ⟨n + 1, by omega⟩
        have hne_val : (u ⟨n, by omega⟩).val ≠ (u ⟨n + 1, by omega⟩).val :=
          fun h => hlast (Fin.ext h)
        have hcn_val : c.val ≠ (u ⟨n, by omega⟩).val := fun h => hcn (Fin.ext h)
        have hcn1_val : c.val ≠ (u ⟨n + 1, by omega⟩).val := fun h => hcn1 (Fin.ext h)
        omega
      rw [hEq, Finset.card_empty]
  rw [Finset.sum_congr rfl hsum, Finset.sum_boole, Nat.cast_id]
  rfl

private lemma card_S2_succ (n : ℕ) : (S2 (n + 1)).card = (S1 n).card + (S2 n).card := by
  have hdec1 : ∀ a b : Fin 5, a ≠ b → a.val ≤ 2 → b.val ≤ 2 →
      (Finset.univ.filter (fun c : Fin 5 => c.val ≤ 2 ∧ c ≠ a ∧ c ≠ b)).card = 1 := by
    decide
  rw [S2, card_filter_snoc]
  have hsum : ∀ u ∈ W n,
      (Finset.univ.filter (fun c : Fin 5 =>
        OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS2 (Fin.snoc u c))).card =
        (if inS1 u then 1 else 0) + (if inS2 u then 1 else 0) := by
    intro u hu
    have hvu : OMA.S_oeis_a243513.validWord u := (Finset.mem_filter.mp hu).2
    by_cases h1 : inS1 u
    · have h2not : ¬ inS2 u := by
        intro h2
        obtain ⟨i, hi⟩ := h2.1
        have := h1.2 i
        omega
      simp only [h1, h2not, ↓reduceIte]
      have hEq : Finset.univ.filter (fun c : Fin 5 =>
          OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS2 (Fin.snoc u c)) = {2} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          validWord_snoc_iff, inS2, exists_eq_snoc, forall_le_snoc]
        constructor
        · rintro ⟨_, (⟨i, hi⟩ | hc2), _, _⟩
          · have := h1.2 i; omega
          · exact Fin.ext hc2
        · rintro rfl
          obtain ⟨j1, hj1⟩ := h1.1
          refine ⟨⟨hvu, fun _ => ⟨j1, by omega⟩, fun _ => ?_⟩,
            Or.inr rfl, fun i => le_trans (h1.2 i) (by decide), by decide⟩
          have hn1 := h1.2 ⟨n, by omega⟩
          have hn2 := h1.2 ⟨n + 1, by omega⟩
          exact ⟨fun h => by have := congrArg Fin.val h; omega,
            fun h => by have := congrArg Fin.val h; omega⟩
      rw [hEq, Finset.card_singleton]
    · by_cases h2 : inS2 u
      · simp only [h1, h2, ↓reduceIte]
        have hne_u : ∃ i, (u i).val ≠ 0 := by
          obtain ⟨i, hi⟩ := h2.1
          exact ⟨i, by omega⟩
        have hlast := validWord_last_ne hvu hne_u
        have hEq : Finset.univ.filter (fun c : Fin 5 =>
            OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS2 (Fin.snoc u c)) =
            Finset.univ.filter (fun c : Fin 5 =>
              c.val ≤ 2 ∧ c ≠ u ⟨n, by omega⟩ ∧ c ≠ u ⟨n + 1, by omega⟩) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            validWord_snoc_iff, inS2, exists_eq_snoc, forall_le_snoc]
          constructor
          · rintro ⟨⟨_, _, hne⟩, _, _, hcle⟩
            obtain ⟨hcn, hcn1⟩ := hne hlast
            exact ⟨hcle, hcn, hcn1⟩
          · rintro ⟨hcle, hcn, hcn1⟩
            refine ⟨⟨hvu, fun hcpos => ?_, fun _ => ⟨hcn, hcn1⟩⟩,
              Or.inl h2.1, h2.2, hcle⟩
            obtain ⟨i2, hi2⟩ := h2.1
            obtain ⟨j, _, hj⟩ := validWord_exists_of_le hvu ((u i2).val - (c.val - 1))
              (c.val - 1) i2 (by omega)
            exact ⟨j, by omega⟩
        rw [hEq]
        exact hdec1 (u ⟨n, by omega⟩) (u ⟨n + 1, by omega⟩) hlast
          (h2.2 ⟨n, by omega⟩) (h2.2 ⟨n + 1, by omega⟩)
      · simp only [h1, h2, ↓reduceIte]
        have hEq : Finset.univ.filter (fun c : Fin 5 =>
            OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS2 (Fin.snoc u c)) = ∅ := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and, validWord_snoc_iff, inS2, exists_eq_snoc, forall_le_snoc]
          rintro ⟨_, h1c, _⟩ (⟨i2, hi2⟩ | hc2) hu_le2 _
          · exact h2 ⟨⟨i2, hi2⟩, hu_le2⟩
          · obtain ⟨j, hj⟩ := h1c (by omega)
            have hj1 : (u j).val = 1 := by omega
            exact h1 ⟨⟨j, hj1⟩, fun i => by
              by_contra hgt
              have hi2_val : (u i).val = 2 := by have := hu_le2 i; omega
              exact h2 ⟨⟨i, hi2_val⟩, hu_le2⟩⟩
        rw [hEq, Finset.card_empty]
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
    Nat.cast_id, Nat.cast_id]
  rfl

private lemma card_S34_succ (n : ℕ) : (S34 (n + 1)).card = (S2 n).card + 3 * (S34 n).card := by
  have hdec3 : ∀ a b : Fin 5, a ≠ b →
      (Finset.univ.filter (fun c : Fin 5 => c ≠ a ∧ c ≠ b)).card = 3 := by
    decide
  rw [S34, card_filter_snoc]
  have hsum : ∀ u ∈ W n,
      (Finset.univ.filter (fun c : Fin 5 =>
        OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS34 (Fin.snoc u c))).card =
        (if inS2 u then 1 else 0) + 3 * (if inS34 u then 1 else 0) := by
    intro u hu
    have hvu : OMA.S_oeis_a243513.validWord u := (Finset.mem_filter.mp hu).2
    by_cases h2 : inS2 u
    · have h3not : ¬ inS34 u := by
        rintro ⟨i, hi⟩
        have := h2.2 i
        omega
      simp only [h2, h3not, ↓reduceIte]
      have hEq : Finset.univ.filter (fun c : Fin 5 =>
          OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS34 (Fin.snoc u c)) = {3} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          validWord_snoc_iff, inS34, exists_ge_snoc]
        constructor
        · rintro ⟨⟨_, h1c, _⟩, (⟨i, hi⟩ | hc3)⟩
          · have := h2.2 i; omega
          · obtain ⟨j, hj⟩ := h1c (by omega)
            have := h2.2 j
            exact Fin.ext (by omega)
        · rintro rfl
          obtain ⟨i2, hi2⟩ := h2.1
          refine ⟨⟨hvu, fun _ => ⟨i2, by omega⟩, fun _ => ?_⟩, Or.inr (by decide)⟩
          have hn1 := h2.2 ⟨n, by omega⟩
          have hn2 := h2.2 ⟨n + 1, by omega⟩
          exact ⟨fun h => by have := congrArg Fin.val h; omega,
            fun h => by have := congrArg Fin.val h; omega⟩
      rw [hEq, Finset.card_singleton]
    · by_cases h34 : inS34 u
      · simp only [h2, h34, ↓reduceIte]
        obtain ⟨i3, hi3⟩ := h34
        have hne_u : ∃ i, (u i).val ≠ 0 := ⟨i3, by omega⟩
        have hlast := validWord_last_ne hvu hne_u
        have hEq : Finset.univ.filter (fun c : Fin 5 =>
            OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS34 (Fin.snoc u c)) =
            Finset.univ.filter (fun c : Fin 5 => c ≠ u ⟨n, by omega⟩ ∧ c ≠ u ⟨n + 1, by omega⟩) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            validWord_snoc_iff, inS34, exists_ge_snoc]
          constructor
          · rintro ⟨⟨_, _, hne⟩, _⟩
            exact hne hlast
          · rintro ⟨hcn, hcn1⟩
            refine ⟨⟨hvu, fun hcpos => ?_, fun _ => ⟨hcn, hcn1⟩⟩, Or.inl ⟨i3, hi3⟩⟩
            have hcle : c.val - 1 ≤ (u i3).val := by
              have := c.isLt
              omega
            obtain ⟨j, _, hj⟩ := validWord_exists_of_le hvu ((u i3).val - (c.val - 1))
              (c.val - 1) i3 (by omega)
            exact ⟨j, by omega⟩
        rw [hEq]
        simp only [zero_add, mul_one]
        exact hdec3 (u ⟨n, by omega⟩) (u ⟨n + 1, by omega⟩) hlast
      · simp only [h2, h34, ↓reduceIte]
        have hEq : Finset.univ.filter (fun c : Fin 5 =>
            OMA.S_oeis_a243513.validWord (Fin.snoc u c) ∧ inS34 (Fin.snoc u c)) = ∅ := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and, validWord_snoc_iff, inS34, exists_ge_snoc]
          rintro ⟨_, h1c, _⟩ (⟨i, hi⟩ | hc3)
          · exact h34 ⟨i, hi⟩
          · obtain ⟨j, hj⟩ := h1c (by omega)
            have hle2 : ∀ i, (u i).val ≤ 2 := by
              intro i
              by_contra hgt
              exact h34 ⟨i, by omega⟩
            have hj2 : (u j).val = 2 := by
              have := hle2 j
              omega
            exact h2 ⟨⟨j, hj2⟩, hle2⟩
        rw [hEq, Finset.card_empty]
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, Nat.cast_id, Nat.cast_id]
  rfl

private lemma base_cards :
    (Z 0).card = 1 ∧ (S1 0).card = 1 ∧ (S2 0).card = 0 ∧ (S34 0).card = 0 := by
  have hvalid0 : ∀ w : Fin 2 → Fin 5,
      OMA.S_oeis_a243513.validWord w ↔ w = (fun _ => 0) ∨ w = ![0, 1] := by
    intro w
    constructor
    · intro hw
      have hw0 : (w 0).val = 0 := validWord_zero hw
      have h1 : (w 1).val = 0 ∨ (w 1).val = 1 := by
        by_cases hpos : 0 < (w 1).val
        · obtain ⟨j, hj, hjval⟩ := hw.1 1 hpos
          have hj0 : j = 0 := Fin.ext (by have := j.isLt; exact Nat.lt_one_iff.mp hj)
          subst hj0
          omega
        · omega
      rcases h1 with h10 | h11
      · left; ext i; fin_cases i <;> simp [hw0, h10]
      · right; ext i; fin_cases i <;> simp [hw0, h11]
    · rintro (rfl | rfl)
      · refine ⟨fun i hi => by simp at hi, fun i j k hij hjk _ => by
          have := i.isLt; have := k.isLt; omega⟩
      · refine ⟨fun i hi => ?_, fun i j k hij hjk _ => by
          have := i.isLt; have := k.isLt; omega⟩
        fin_cases i
        · simp at hi
        · exact ⟨0, by decide, by decide⟩
  have hZ : Z 0 = {fun _ => 0} := by
    ext w
    simp only [Z, W, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hvalid0]
    constructor
    · rintro ⟨rfl | rfl, hz⟩
      · rfl
      · exfalso; have := hz 1; simp at this
    · rintro rfl
      exact ⟨Or.inl rfl, fun _ => rfl⟩
  have hS1 : S1 0 = {![0, 1]} := by
    ext w
    simp only [S1, W, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hvalid0,
      inS1]
    constructor
    · rintro ⟨rfl | rfl, ⟨i, hi⟩, _⟩
      · simp at hi
      · rfl
    · rintro rfl
      refine ⟨Or.inr rfl, ⟨1, rfl⟩, fun i => by fin_cases i <;> decide⟩
  have hS2 : S2 0 = ∅ := by
    ext w
    simp only [S2, W, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, hvalid0, inS2]
    rintro (rfl | rfl) ⟨i, hi⟩ _
    · simp at hi
    · fin_cases i <;> simp at hi
  have hS34 : S34 0 = ∅ := by
    ext w
    simp only [S34, W, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, hvalid0, inS34]
    rintro (rfl | rfl) ⟨i, hi⟩
    · simp at hi
    · fin_cases i <;> simp at hi
  rw [hZ, hS1, hS2, hS34, Finset.card_singleton, Finset.card_singleton, Finset.card_empty]
  exact ⟨rfl, rfl, rfl, rfl⟩

private lemma state_cards (n : ℕ) :
    (Z n).card = 1 ∧ (S1 n).card = 1 ∧ (S2 n).card = n ∧
      4 * (S34 n).card + 1 + 2 * n = 3 ^ n := by
  induction n with
  | zero =>
    obtain ⟨hz, hs1, hs2, hs34⟩ := base_cards
    omega
  | succ n ih =>
    obtain ⟨hz, hs1, hs2, hs34⟩ := ih
    have hz' := card_Z_succ n
    have hs1' := card_S1_succ n
    have hs2' := card_S2_succ n
    have hs34' := card_S34_succ n
    have hpow : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
    omega

private lemma count_formula (n : ℕ) : 4 * OMA.S_oeis_a243513.count n = 7 + 3 ^ n + 2 * n := by
  rw [count_eq_W_card, W_card_split]
  obtain ⟨hz, hs1, hs2, hs34⟩ := state_cards n
  omega

end OMA.P_oeis_a243513

theorem OMA.solution : type_of% @OMA.S_oeis_a243513.main := by
  refine ⟨fun n _ => OMA.P_oeis_a243513.count_formula n, ?_⟩
  let S := OMA.S_oeis_a243513.series
  have hlhs : S * ((1 - PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X)) =
      S - PowerSeries.C (5 : ℚ) * (PowerSeries.X * S) +
        PowerSeries.C (7 : ℚ) * (PowerSeries.X * (PowerSeries.X * S)) -
        PowerSeries.C (3 : ℚ) * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * S))) := by
    simp only [map_ofNat]
    ring
  have hrhs : PowerSeries.X * (3 - 10 * PowerSeries.X + 6 * PowerSeries.X ^ 2) =
      PowerSeries.C (3 : ℚ) * PowerSeries.X -
        PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 2 +
        PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
    ring
  change S * ((1 - PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X)) =
    PowerSeries.X * (3 - 10 * PowerSeries.X + 6 * PowerSeries.X ^ 2)
  rw [hlhs, hrhs]
  have hc1 : OMA.S_oeis_a243513.count 1 = 3 := by
    have := OMA.P_oeis_a243513.count_formula 1; omega
  have hc2 : OMA.S_oeis_a243513.count 2 = 5 := by
    have := OMA.P_oeis_a243513.count_formula 2; omega
  have hc3 : OMA.S_oeis_a243513.count 3 = 10 := by
    have := OMA.P_oeis_a243513.count_formula 3; omega
  have hcoeff0 : PowerSeries.coeff 0 OMA.S_oeis_a243513.series = 0 := by
    simp [OMA.S_oeis_a243513.series]
  have hcoeff : ∀ m : ℕ, 1 ≤ m →
      PowerSeries.coeff m OMA.S_oeis_a243513.series = (OMA.S_oeis_a243513.count m : ℚ) := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    simp [OMA.S_oeis_a243513.series, hm0]
  ext m
  by_cases hm4 : m < 4
  · interval_cases m
    · simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_zero_X, PowerSeries.coeff_X_pow]
      dsimp only [S]
      rw [hcoeff0]
      norm_num
    · simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      dsimp only [S]
      rw [hcoeff0, hcoeff 1 (by omega), hc1]
      norm_num
    · simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      dsimp only [S]
      rw [hcoeff0, hcoeff 1 (by omega), hcoeff 2 (by omega), hc1, hc2]
      norm_num
    · simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      dsimp only [S]
      rw [hcoeff0, hcoeff 1 (by omega), hcoeff 2 (by omega), hcoeff 3 (by omega), hc1, hc2, hc3]
      norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    have hne1 : k + 4 ≠ 1 := by omega
    have hne2 : k + 4 ≠ 2 := by omega
    have hne3 : k + 4 ≠ 3 := by omega
    simp only [hne1, hne2, hne3, ↓reduceIte]
    dsimp only [S]
    rw [hcoeff (k + 4) (by omega), hcoeff (k + 3) (by omega),
      hcoeff (k + 2) (by omega), hcoeff (k + 1) (by omega)]
    have h4 : (4 : ℚ) * (OMA.S_oeis_a243513.count (k + 4) : ℚ) =
        7 + 3 ^ (k + 4) + 2 * ((k + 4 : ℕ) : ℚ) := by
      exact_mod_cast OMA.P_oeis_a243513.count_formula (k + 4)
    have h3 : (4 : ℚ) * (OMA.S_oeis_a243513.count (k + 3) : ℚ) =
        7 + 3 ^ (k + 3) + 2 * ((k + 3 : ℕ) : ℚ) := by
      exact_mod_cast OMA.P_oeis_a243513.count_formula (k + 3)
    have h2 : (4 : ℚ) * (OMA.S_oeis_a243513.count (k + 2) : ℚ) =
        7 + 3 ^ (k + 2) + 2 * ((k + 2 : ℕ) : ℚ) := by
      exact_mod_cast OMA.P_oeis_a243513.count_formula (k + 2)
    have h1 : (4 : ℚ) * (OMA.S_oeis_a243513.count (k + 1) : ℚ) =
        7 + 3 ^ (k + 1) + 2 * ((k + 1 : ℕ) : ℚ) := by
      exact_mod_cast OMA.P_oeis_a243513.count_formula (k + 1)
    push_cast at h4 h3 h2 h1
    linear_combination (1 / 4 : ℚ) * (h4 - 5 * h3 + 7 * h2 - 3 * h1)
