import OMAStatements.S_oeis_a242235

-- Problem: A242235: Number of length n+4+1 0..4 arrays with every value 0..4 appearing at least once in every consecutive 4+2 elements, and new values
-- Upstream: formal-conjectures statements/oeis-a242235.lean:0 (declaration OMA.S_oeis_a242235.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Status of the mathematics: a known result, formalized here. The site lists this entry as
-- a known result, and a desk note points to a written derivation of the generating functions of
-- all columns of A242239 (github.com/pandolfonicolo/oeis-proofs, project
-- a242239-window-covering-words). This file is an independent Lean proof by a transfer argument.
--
-- Proof idea. For an admissible array let cnt n k be the number of admissible arrays of length
-- n + 5 whose last k entries are pairwise distinct (k = 0..5). Appending one entry v to an
-- admissible array x keeps it admissible exactly when v together with the last five entries of x
-- covers all five values. If the last five entries of x are distinct, every v is allowed;
-- otherwise exactly four values occur among them and v is forced. Counting the appended arrays
-- whose last k + 1 entries are distinct gives, for n >= 1 and k <= 4,
--   cnt (n + 1) (k + 1) = (4 - k) * cnt n 5 + cnt n k.
-- This linear system has characteristic polynomial x^5 - x^4 - x^3 - x^2 - x - 1, which is the
-- recurrence. The initial values come from listing the fifteen admissible arrays of length six.

namespace A242235

open OMA.S_oeis_a242235

/-- The entry at position `n + i`, one of the final five entries. -/
def tl {n : ℕ} (x : Fin (n + 5) → Fin 5) (i : Fin 5) : Fin 5 := x ⟨n + i.val, by omega⟩

/-- The last `k` entries (`k ≤ 5`) are pairwise distinct. -/
def LD {n : ℕ} (k : ℕ) (x : Fin (n + 5) → Fin 5) : Prop :=
  ∀ i j : Fin 5, 5 ≤ i.val + k → 5 ≤ j.val + k → tl x i = tl x j → i = j

instance {n : ℕ} (k : ℕ) (x : Fin (n + 5) → Fin 5) : Decidable (LD k x) := by
  unfold LD; infer_instance

/-- Number of admissible arrays of length `n + 5` whose last `k` entries are distinct. -/
def cnt (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 5) → Fin 5)).filter
    (fun x => (AllInWindows x ∧ NewInOrder x) ∧ LD k x)).card

/-- Append one entry. -/
def sn {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) : Fin (n + 1 + 5) → Fin 5 :=
  fun i => if h : i.val < n + 5 then x ⟨i.val, h⟩ else v

/-- Drop the last entry. -/
def ini {n : ℕ} (y : Fin (n + 1 + 5) → Fin 5) : Fin (n + 5) → Fin 5 :=
  fun i => y ⟨i.val, by omega⟩

lemma sn_lt {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) (j : Fin (n + 1 + 5))
    (h : j.val < n + 5) : sn x v j = x ⟨j.val, h⟩ := by
  simp [sn, h]

lemma sn_ge {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) (j : Fin (n + 1 + 5))
    (h : ¬ j.val < n + 5) : sn x v j = v := by
  simp [sn, h]

lemma xeq {m : ℕ} (x : Fin m → Fin 5) (i j : Fin m) (h : i.val = j.val) : x i = x j := by
  rw [Fin.ext h]

lemma ini_sn {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) : ini (sn x v) = x := by
  funext i
  unfold ini
  rw [sn_lt x v _ i.isLt]

lemma sn_ini {n : ℕ} (y : Fin (n + 1 + 5) → Fin 5) : sn (ini y) (y ⟨n + 5, by omega⟩) = y := by
  funext i
  by_cases h : i.val < n + 5
  · rw [sn_lt _ _ _ h]; rfl
  · rw [sn_ge _ _ _ h]; exact xeq y _ _ (by have := i.isLt; simp; omega)

lemma aw_sn {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) :
    AllInWindows (sn x v) ↔ AllInWindows x ∧ ∀ u : Fin 5, u = v ∨ ∃ i : Fin 5, tl x i = u := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi u
      obtain ⟨j, h1, h2, h3⟩ := h ⟨i.val, by omega⟩ (by simp only; omega) u
      simp only at h1 h2
      have hj : j.val < n + 5 := by omega
      rw [sn_lt _ _ _ hj] at h3
      exact ⟨⟨j.val, hj⟩, h1, h2, h3⟩
    · intro u
      obtain ⟨j, h1, h2, h3⟩ := h ⟨n, by omega⟩ (by simp only; omega) u
      simp only at h1 h2
      by_cases hj : j.val < n + 5
      · right
        rw [sn_lt _ _ _ hj] at h3
        refine ⟨⟨j.val - n, by omega⟩, ?_⟩
        rw [← h3]
        exact xeq x _ _ (by simp only; omega)
      · left
        rw [sn_ge _ _ _ hj] at h3
        exact h3.symm
  · rintro ⟨h, h'⟩ i hi u
    by_cases hi' : i.val + 6 ≤ n + 5
    · obtain ⟨j, h1, h2, h3⟩ := h ⟨i.val, by omega⟩ hi' u
      simp only at h1 h2
      refine ⟨⟨j.val, by omega⟩, h1, h2, ?_⟩
      rw [sn_lt _ _ _ j.isLt]
      exact h3
    · rcases h' u with rfl | ⟨t, ht⟩
      · refine ⟨⟨n + 5, by omega⟩, by simp only; omega, by simp only; omega, ?_⟩
        rw [sn_ge _ _ _ (by simp)]
      · refine ⟨⟨n + t.val, by omega⟩, by simp only; omega, by simp only; omega, ?_⟩
        rw [sn_lt _ _ _ (by simp only; omega)]
        exact ht

lemma nio_ini {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) (h : NewInOrder (sn x v)) :
    NewInOrder x := by
  intro j w hw
  obtain ⟨k, hk, hk'⟩ := h ⟨j.val, by omega⟩ w (by rw [sn_lt _ _ _ j.isLt]; exact hw)
  have hkl : k.val < n + 5 := by
    have := Fin.lt_def.mp hk
    simp only at this
    omega
  rw [sn_lt _ _ _ hkl] at hk'
  exact ⟨⟨k.val, hkl⟩, Fin.lt_def.mpr (Fin.lt_def.mp hk), hk'⟩

lemma nio_sn {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) (h : NewInOrder x)
    (hs : ∀ w : Fin 5, ∃ k : Fin (n + 5), x k = w) : NewInOrder (sn x v) := by
  intro j w hw
  by_cases hj : j.val < n + 5
  · rw [sn_lt _ _ _ hj] at hw
    obtain ⟨k, hk, hk'⟩ := h ⟨j.val, hj⟩ w hw
    refine ⟨⟨k.val, by omega⟩, Fin.lt_def.mpr (Fin.lt_def.mp hk), ?_⟩
    rw [sn_lt _ _ _ k.isLt]
    exact hk'
  · obtain ⟨k, hk⟩ := hs w
    refine ⟨⟨k.val, by omega⟩, Fin.lt_def.mpr (by simp only; omega), ?_⟩
    rw [sn_lt _ _ _ k.isLt]
    exact hk

lemma surj_of_aw {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 5) → Fin 5) (h : AllInWindows x)
    (w : Fin 5) : ∃ k, x k = w := by
  obtain ⟨j, -, -, hj⟩ := h ⟨0, by omega⟩ (by simp only; omega) w
  exact ⟨j, hj⟩

lemma tail_cover {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 5) → Fin 5) (h : AllInWindows x) :
    ∀ u : Fin 5, u = x ⟨n - 1, by omega⟩ ∨ ∃ i : Fin 5, tl x i = u := by
  intro u
  obtain ⟨j, h1, h2, h3⟩ := h ⟨n - 1, by omega⟩ (by simp only; omega) u
  simp only at h1 h2
  by_cases hj : j.val = n - 1
  · left
    rw [← h3]
    exact xeq x _ _ hj
  · right
    refine ⟨⟨j.val - n, by omega⟩, ?_⟩
    rw [← h3]
    exact xeq x _ _ (by simp only; omega)

lemma tl_sn_lt {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) (i : Fin 5) (h : i.val < 4) :
    tl (sn x v) i = tl x ⟨i.val + 1, by omega⟩ := by
  unfold tl
  rw [sn_lt _ _ _ (by simp only; omega)]
  exact xeq x _ _ (by simp only; omega)

lemma tl_sn_last {n : ℕ} (x : Fin (n + 5) → Fin 5) (v : Fin 5) (i : Fin 5) (h : i.val = 4) :
    tl (sn x v) i = v := by
  unfold tl
  rw [sn_ge _ _ _ (by simp only; omega)]

lemma tl_congr {n : ℕ} (x : Fin (n + 5) → Fin 5) (i j : Fin 5) (h : i.val = j.val) :
    tl x i = tl x j := by
  rw [Fin.ext h]

lemma ld_sn {n k : ℕ} (hk : k ≤ 4) (x : Fin (n + 5) → Fin 5) (v : Fin 5) :
    LD (k + 1) (sn x v) ↔ LD k x ∧ ∀ i : Fin 5, 5 ≤ i.val + k → tl x i ≠ v := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hi hj hij
      have e1 : tl (sn x v) ⟨i.val - 1, by omega⟩ = tl x i :=
        (tl_sn_lt x v _ (by simp only; omega)).trans (tl_congr x _ i (by simp only; omega))
      have e2 : tl (sn x v) ⟨j.val - 1, by omega⟩ = tl x j :=
        (tl_sn_lt x v _ (by simp only; omega)).trans (tl_congr x _ j (by simp only; omega))
      have h1 := h ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ (by simp only; omega)
        (by simp only; omega) (by rw [e1, e2]; exact hij)
      have h2 := Fin.ext_iff.mp h1
      simp only at h2
      exact Fin.ext (by omega)
    · intro i hi hv
      have e1 : tl (sn x v) ⟨i.val - 1, by omega⟩ = tl x i :=
        (tl_sn_lt x v _ (by simp only; omega)).trans (tl_congr x _ i (by simp only; omega))
      have h1 := h ⟨i.val - 1, by omega⟩ ⟨4, by omega⟩ (by simp only; omega) (by simp only; omega)
        (by rw [e1, tl_sn_last _ _ _ rfl]; exact hv)
      have h2 := Fin.ext_iff.mp h1
      simp only at h2
      omega
  · rintro ⟨h, h'⟩ i j hi hj hij
    by_cases hi4 : i.val = 4 <;> by_cases hj4 : j.val = 4
    · exact Fin.ext (by omega)
    · exfalso
      rw [tl_sn_last _ _ _ hi4, tl_sn_lt _ _ _ (by omega)] at hij
      exact h' ⟨j.val + 1, by omega⟩ (by simp only; omega) hij.symm
    · exfalso
      rw [tl_sn_last _ _ _ hj4, tl_sn_lt _ _ _ (by omega)] at hij
      exact h' ⟨i.val + 1, by omega⟩ (by simp only; omega) hij
    · rw [tl_sn_lt _ _ _ (by omega), tl_sn_lt _ _ _ (by omega)] at hij
      have h1 := h _ _ (by simp only; omega) (by simp only; omega) hij
      have h2 := Fin.ext_iff.mp h1
      simp only at h2
      exact Fin.ext (by omega)

lemma ld5 {n : ℕ} (x : Fin (n + 5) → Fin 5) : LD 5 x ↔ Function.Injective (tl x) := by
  constructor
  · intro h i j hij
    exact h i j (by omega) (by omega) hij
  · intro h i j _ _ hij
    exact h hij

lemma ld_mono {n k : ℕ} (x : Fin (n + 5) → Fin 5) (h : LD 5 x) : LD k x := by
  intro i j _ _ hij
  exact h i j (by omega) (by omega) hij

lemma card_Ak (k : ℕ) (hk : k ≤ 5) :
    ((Finset.univ : Finset (Fin 5)).filter (fun i => 5 ≤ i.val + k)).card = k := by
  interval_cases k <;> decide

lemma count_v (g : Fin 5 → Fin 5) (c : Fin 5) (hc : ∀ u, u = c ∨ ∃ i, g i = u) (k : ℕ)
    (hk : k ≤ 4) :
    ((Finset.univ : Finset (Fin 5)).filter
      (fun v => (∀ i : Fin 5, 5 ≤ i.val + k → g i ≠ v) ∧ ∀ u, u = v ∨ ∃ i, g i = u)).card
      = if Function.Injective g then 5 - k else 1 := by
  classical
  split_ifs with hinj
  · have hsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hinj
    have hset : ((Finset.univ : Finset (Fin 5)).filter
        (fun v => (∀ i : Fin 5, 5 ≤ i.val + k → g i ≠ v) ∧ ∀ u, u = v ∨ ∃ i, g i = u))
        = (((Finset.univ : Finset (Fin 5)).filter (fun i : Fin 5 => 5 ≤ i.val + k)).image g)ᶜ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_image,
        not_exists, not_and]
      constructor
      · rintro ⟨h1, -⟩ i hi
        exact h1 i hi
      · intro h
        exact ⟨fun i hi => h i hi, fun u => Or.inr (hsurj u)⟩
    rw [hset, Finset.card_compl, Finset.card_image_of_injective _ hinj, card_Ak k (by omega)]
    simp
  · obtain ⟨I, hI⟩ : ∃ I : Finset (Fin 5), I = (Finset.univ : Finset (Fin 5)).image g := ⟨_, rfl⟩
    have hIm : ∀ u, u ∈ I ↔ ∃ i, g i = u := by
      intro u
      rw [hI]
      simp
    have h1 : I.card < 5 := by
      by_contra hcon
      apply hinj
      have hle := Finset.card_image_le (s := (Finset.univ : Finset (Fin 5))) (f := g)
      rw [← hI] at hle
      simp only [Finset.card_univ, Fintype.card_fin] at hle
      have hcard : ((Finset.univ : Finset (Fin 5)).image g).card
          = (Finset.univ : Finset (Fin 5)).card := by
        rw [← hI]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      have hinjOn := Finset.card_image_iff.mp hcard
      intro p q hpq
      exact hinjOn (by simp) (by simp) hpq
    have h2 : 5 ≤ I.card + 1 := by
      have hsub : (Finset.univ : Finset (Fin 5)) ⊆ insert c I := by
        intro u _
        rcases hc u with rfl | hi
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem ((hIm u).mpr hi)
      have h3 := Finset.card_le_card hsub
      have h4 := Finset.card_insert_le c I
      simp only [Finset.card_univ, Fintype.card_fin] at h3
      omega
    have h3 : Iᶜ.card = 1 := by
      rw [Finset.card_compl]
      simp only [Fintype.card_fin]
      omega
    obtain ⟨u0, hu0⟩ := Finset.card_eq_one.mp h3
    have hmem : ∀ u, u ∉ I ↔ u = u0 := by
      intro u
      rw [← Finset.mem_compl, hu0, Finset.mem_singleton]
    have hset : ((Finset.univ : Finset (Fin 5)).filter
        (fun v => (∀ i : Fin 5, 5 ≤ i.val + k → g i ≠ v) ∧ ∀ u, u = v ∨ ∃ i, g i = u)) = {u0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        rcases h u0 with h | hi
        · exact h.symm
        · exact absurd ((hIm u0).mpr hi) ((hmem u0).mpr rfl)
      · rintro rfl
        refine ⟨fun i _ hi => (hmem v).mpr rfl ((hIm v).mpr ⟨i, hi⟩), fun u => ?_⟩
        by_cases hu : u ∈ I
        · exact Or.inr ((hIm u).mp hu)
        · exact Or.inl ((hmem u).mp hu)
    rw [hset, Finset.card_singleton]

/-- The fibre of `ini` over an admissible array. -/
lemma fibre_iff {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ 4) (x : Fin (n + 5) → Fin 5)
    (hx : AllInWindows x ∧ NewInOrder x) (v : Fin 5) :
    ((AllInWindows (sn x v) ∧ NewInOrder (sn x v)) ∧ LD (k + 1) (sn x v)) ↔
      (LD k x ∧ (∀ i : Fin 5, 5 ≤ i.val + k → tl x i ≠ v) ∧ ∀ u, u = v ∨ ∃ i, tl x i = u) := by
  rw [aw_sn, ld_sn hk]
  constructor
  · rintro ⟨⟨⟨-, h1⟩, -⟩, h2, h3⟩
    exact ⟨h2, h3, h1⟩
  · rintro ⟨h2, h3, h1⟩
    exact ⟨⟨⟨hx.1, h1⟩, nio_sn x v hx.2 (surj_of_aw hn x hx.1)⟩, h2, h3⟩

lemma down {n k : ℕ} (hk : k ≤ 4) (y : Fin (n + 1 + 5) → Fin 5)
    (hy : (AllInWindows y ∧ NewInOrder y) ∧ LD (k + 1) y) :
    (AllInWindows (ini y) ∧ NewInOrder (ini y)) ∧ LD k (ini y) := by
  rw [← sn_ini y] at hy
  rw [aw_sn, ld_sn hk] at hy
  exact ⟨⟨hy.1.1.1, nio_ini _ _ hy.1.2⟩, hy.2.1⟩

lemma step {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ 4) :
    cnt (n + 1) (k + 1) = (4 - k) * cnt n 5 + cnt n k := by
  classical
  have hfib : ∀ x ∈ ((Finset.univ : Finset (Fin (n + 5) → Fin 5)).filter
      (fun x => (AllInWindows x ∧ NewInOrder x) ∧ LD k x)),
      ((((Finset.univ : Finset (Fin (n + 1 + 5) → Fin 5)).filter
        (fun y => (AllInWindows y ∧ NewInOrder y) ∧ LD (k + 1) y)).filter
          (fun y => ini y = x)).card) = if Function.Injective (tl x) then 5 - k else 1 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [← count_v (tl x) _ (tail_cover hn x hx.1.1) k hk]
    symm
    refine Finset.card_bij (fun v _ => sn x v) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨(fibre_iff hn hk x hx.1 v).mpr ⟨hx.2, hv.1, hv.2⟩, ini_sn x v⟩
    · intro v _ v' _ hvv
      have h1 := congrFun hvv ⟨n + 5, by omega⟩
      rw [sn_ge _ _ _ (by simp), sn_ge _ _ _ (by simp)] at h1
      exact h1
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨hy1, rfl⟩ := hy
      refine ⟨y ⟨n + 5, by omega⟩, ?_, sn_ini y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h2 := hy1
      rw [← sn_ini y] at h2
      exact ((fibre_iff hn hk _ hx.1 _).mp h2).2
  have hmaps : Set.MapsTo ini
      (↑((Finset.univ : Finset (Fin (n + 1 + 5) → Fin 5)).filter
        (fun y => (AllInWindows y ∧ NewInOrder y) ∧ LD (k + 1) y)) : Set (Fin (n + 1 + 5) → Fin 5))
      (↑((Finset.univ : Finset (Fin (n + 5) → Fin 5)).filter
        (fun x => (AllInWindows x ∧ NewInOrder x) ∧ LD k x)) : Set (Fin (n + 5) → Fin 5)) := by
    intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact down hk y hy
  have h5 : (((Finset.univ : Finset (Fin (n + 5) → Fin 5)).filter
        (fun x => (AllInWindows x ∧ NewInOrder x) ∧ LD k x)).filter
          (fun x => Function.Injective (tl x))).card = cnt n 5 := by
    unfold cnt
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, (ld5 x).mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, ld_mono x h2⟩, (ld5 x).mp h2⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := ((Finset.univ : Finset (Fin (n + 5) → Fin 5)).filter
        (fun x => (AllInWindows x ∧ NewInOrder x) ∧ LD k x)))
    (fun x => Function.Injective (tl x))
  rw [h5] at hsplit
  have hCk : cnt n k = ((Finset.univ : Finset (Fin (n + 5) → Fin 5)).filter
        (fun x => (AllInWindows x ∧ NewInOrder x) ∧ LD k x)).card := rfl
  have hCn : cnt (n + 1) (k + 1) = ((Finset.univ : Finset (Fin (n + 1 + 5) → Fin 5)).filter
        (fun y => (AllInWindows y ∧ NewInOrder y) ∧ LD (k + 1) y)).card := rfl
  rw [hCn, Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_ite,
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, h5, hCk, ← hsplit]
  have h54 : 5 - k = (4 - k) + 1 := by omega
  rw [h54]
  ring

/-- Restricted growth: an array with new values in order has `x j ≤ j`. -/
lemma rg {m : ℕ} (x : Fin m → Fin 5) (h : NewInOrder x) :
    ∀ (t : ℕ) (j : Fin m), j.val = t → (x j).val ≤ j.val := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro j hj
    by_contra hlt
    obtain ⟨k, hk, hk'⟩ := h j ⟨(x j).val - 1, by omega⟩ (Fin.lt_def.mpr (by simp only; omega))
    have h1 := Fin.lt_def.mp hk
    have h2 := ih k.val (by omega) k rfl
    rw [hk'] at h2
    simp only at h2
    omega

/-- The fifteen admissible arrays of length six. -/
def V6 : Finset (Fin (1 + 5) → Fin 5) :=
  {![0, 0, 1, 2, 3, 4], ![0, 1, 0, 2, 3, 4], ![0, 1, 1, 2, 3, 4], ![0, 1, 2, 0, 3, 4],
   ![0, 1, 2, 1, 3, 4], ![0, 1, 2, 2, 3, 4], ![0, 1, 2, 3, 0, 4], ![0, 1, 2, 3, 1, 4],
   ![0, 1, 2, 3, 2, 4], ![0, 1, 2, 3, 3, 4], ![0, 1, 2, 3, 4, 0], ![0, 1, 2, 3, 4, 1],
   ![0, 1, 2, 3, 4, 2], ![0, 1, 2, 3, 4, 3], ![0, 1, 2, 3, 4, 4]}

set_option maxRecDepth 1000000 in
lemma base_key : ∀ a1 : Fin 5, a1.val ≤ 1 → ∀ a2 : Fin 5, a2.val ≤ 2 → ∀ a3 : Fin 5, a3.val ≤ 3 →
    ∀ a4 a5 : Fin 5,
    (AllInWindows (![0, a1, a2, a3, a4, a5] : Fin (1 + 5) → Fin 5) ∧
      NewInOrder (![0, a1, a2, a3, a4, a5] : Fin (1 + 5) → Fin 5)) →
    (![0, a1, a2, a3, a4, a5] : Fin (1 + 5) → Fin 5) ∈ V6 := by
  decide +kernel

set_option maxRecDepth 1000000 in
lemma base_mem : ∀ x ∈ V6, AllInWindows x ∧ NewInOrder x := by
  intro x hx
  simp only [V6, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

lemma base_set : ((Finset.univ : Finset (Fin (1 + 5) → Fin 5)).filter
    (fun x => AllInWindows x ∧ NewInOrder x)) = V6 := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have h0 := rg x hx.2 _ ⟨0, by omega⟩ rfl
    have h1 := rg x hx.2 _ ⟨1, by omega⟩ rfl
    have h2 := rg x hx.2 _ ⟨2, by omega⟩ rfl
    have h3 := rg x hx.2 _ ⟨3, by omega⟩ rfl
    simp only at h0 h1 h2 h3
    have hx0 : x ⟨0, by omega⟩ = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have key := base_key (x ⟨1, by omega⟩) h1 (x ⟨2, by omega⟩) h2 (x ⟨3, by omega⟩) h3
      (x ⟨4, by omega⟩) (x ⟨5, by omega⟩)
    have hx' : (![0, x ⟨1, by omega⟩, x ⟨2, by omega⟩, x ⟨3, by omega⟩, x ⟨4, by omega⟩,
        x ⟨5, by omega⟩] : Fin (1 + 5) → Fin 5) = x := by
      funext i
      rw [← hx0]
      fin_cases i <;> rfl
    rw [hx'] at key
    exact key hx
  · exact base_mem x

lemma base_cnt (k : ℕ) : cnt 1 k = (V6.filter (fun x => LD (n := 1) k x)).card := by
  unfold cnt
  rw [← base_set, Finset.filter_filter]

lemma base_vals : cnt 1 0 = 15 ∧ cnt 1 2 = 14 ∧ cnt 1 3 = 12 ∧ cnt 1 4 = 9 ∧ cnt 1 5 = 5 := by
  rw [base_cnt, base_cnt, base_cnt, base_cnt, base_cnt]
  decide

lemma a_eq (n : ℕ) : a n = cnt n 0 := by
  unfold OMA.S_oeis_a242235.a cnt
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · intro h
    exact ⟨h, fun i j hi _ _ => by have := i.isLt; omega⟩
  · exact fun h => h.1

lemma cnt01 (n : ℕ) : cnt n 1 = cnt n 0 := by
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · rintro ⟨h, -⟩
    exact ⟨h, fun i j hi _ _ => by have := i.isLt; omega⟩
  · rintro ⟨h, -⟩
    exact ⟨h, fun i j hi hj _ => Fin.ext (by have := i.isLt; have := j.isLt; omega)⟩

lemma eqs (n : ℕ) (hn : 1 ≤ n) :
    a (n + 1) = 4 * cnt n 5 + a n ∧ cnt (n + 1) 2 = 3 * cnt n 5 + a n ∧
    cnt (n + 1) 3 = 2 * cnt n 5 + cnt n 2 ∧ cnt (n + 1) 4 = cnt n 5 + cnt n 3 ∧
    cnt (n + 1) 5 = cnt n 4 := by
  have h0 := step (k := 0) hn (by omega)
  have h1 := step (k := 1) hn (by omega)
  have h2 := step (k := 2) hn (by omega)
  have h3 := step (k := 3) hn (by omega)
  have h4 := step (k := 4) hn (by omega)
  have e1 := cnt01 n
  have e2 := cnt01 (n + 1)
  rw [a_eq, a_eq]
  norm_num at h0 h1 h2 h3 h4
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

lemma rec5_aux (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ)
    (h : ∀ n, 1 ≤ n → f (n + 1) = 4 * g n 5 + f n ∧ g (n + 1) 2 = 3 * g n 5 + f n ∧
      g (n + 1) 3 = 2 * g n 5 + g n 2 ∧ g (n + 1) 4 = g n 5 + g n 3 ∧ g (n + 1) 5 = g n 4)
    (m : ℕ) (hm : 1 ≤ m) :
    f (m + 5) = f (m + 4) + f (m + 3) + f (m + 2) + f (m + 1) + f m := by
  obtain ⟨a0, b0, c0, d0, e0⟩ := h m hm
  obtain ⟨a1, b1, c1, d1, e1⟩ := h (m + 1) (by omega)
  obtain ⟨a2, b2, c2, d2, e2⟩ := h (m + 2) (by omega)
  obtain ⟨a3, b3, c3, d3, e3⟩ := h (m + 3) (by omega)
  obtain ⟨a4, b4, c4, d4, e4⟩ := h (m + 4) (by omega)
  have s1 : m + 1 + 1 = m + 2 := rfl
  have s2 : m + 2 + 1 = m + 3 := rfl
  have s3 : m + 3 + 1 = m + 4 := rfl
  have s4 : m + 4 + 1 = m + 5 := rfl
  rw [s1] at a1 b1 c1 d1 e1
  rw [s2] at a2 b2 c2 d2 e2
  rw [s3] at a3 b3 c3 d3 e3
  rw [s4] at a4 b4 c4 d4 e4
  linarith

lemma rec5 (m : ℕ) (hm : 1 ≤ m) :
    a (m + 5) = a (m + 4) + a (m + 3) + a (m + 2) + a (m + 1) + a m :=
  rec5_aux a cnt eqs m hm

lemma vals_aux (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ)
    (h : ∀ n, 1 ≤ n → f (n + 1) = 4 * g n 5 + f n ∧ g (n + 1) 2 = 3 * g n 5 + f n ∧
      g (n + 1) 3 = 2 * g n 5 + g n 2 ∧ g (n + 1) 4 = g n 5 + g n 3 ∧ g (n + 1) 5 = g n 4)
    (b : f 1 = 15 ∧ g 1 2 = 14 ∧ g 1 3 = 12 ∧ g 1 4 = 9 ∧ g 1 5 = 5) :
    f 1 = 15 ∧ f 2 = 35 ∧ f 3 = 71 ∧ f 4 = 139 ∧ f 5 = 271 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  have e1 : f 2 = 4 * g 1 5 + f 1 ∧ g 2 2 = 3 * g 1 5 + f 1 ∧
      g 2 3 = 2 * g 1 5 + g 1 2 ∧ g 2 4 = g 1 5 + g 1 3 ∧ g 2 5 = g 1 4 := h 1 (by omega)
  have e2 : f 3 = 4 * g 2 5 + f 2 ∧ g 3 2 = 3 * g 2 5 + f 2 ∧
      g 3 3 = 2 * g 2 5 + g 2 2 ∧ g 3 4 = g 2 5 + g 2 3 ∧ g 3 5 = g 2 4 := h 2 (by omega)
  have e3 : f 4 = 4 * g 3 5 + f 3 ∧ g 4 2 = 3 * g 3 5 + f 3 ∧
      g 4 3 = 2 * g 3 5 + g 3 2 ∧ g 4 4 = g 3 5 + g 3 3 ∧ g 4 5 = g 3 4 := h 3 (by omega)
  have e4 : f 5 = 4 * g 4 5 + f 4 ∧ g 5 2 = 3 * g 4 5 + f 4 ∧
      g 5 3 = 2 * g 4 5 + g 4 2 ∧ g 5 4 = g 4 5 + g 4 3 ∧ g 5 5 = g 4 4 := h 4 (by omega)
  obtain ⟨p1, p2, p3, p4, p5⟩ := e1
  obtain ⟨q1, q2, q3, q4, q5⟩ := e2
  obtain ⟨r1, r2, r3, r4, r5⟩ := e3
  obtain ⟨t1, t2, t3, t4, t5⟩ := e4
  refine ⟨b1, by linarith, by linarith, by linarith, by linarith⟩

lemma vals : a 1 = 15 ∧ a 2 = 35 ∧ a 3 = 71 ∧ a 4 = 139 ∧ a 5 = 271 := by
  have b := base_vals
  rw [← a_eq] at b
  exact vals_aux a cnt eqs b

end A242235

theorem OMA.solution : type_of% @OMA.S_oeis_a242235.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have h : OMA.S_oeis_a242235.a (m + 6) = OMA.S_oeis_a242235.a (m + 5)
        + OMA.S_oeis_a242235.a (m + 4) + OMA.S_oeis_a242235.a (m + 3)
        + OMA.S_oeis_a242235.a (m + 2) + OMA.S_oeis_a242235.a (m + 1) := A242235.rec5 (m + 1) (by omega)
    have e1 : m + 6 - 1 = m + 5 := by omega
    have e2 : m + 6 - 2 = m + 4 := by omega
    have e3 : m + 6 - 3 = m + 3 := by omega
    have e4 : m + 6 - 4 = m + 2 := by omega
    have e5 : m + 6 - 5 = m + 1 := by omega
    rw [e1, e2, e3, e4, e5]
    exact_mod_cast h
  · have hX : (1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4
        - PowerSeries.X ^ 5 : PowerSeries ℤ) = 1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 2
        - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
      rw [pow_one]
    have hR : (PowerSeries.X * (15 + 20 * PowerSeries.X + 21 * PowerSeries.X ^ 2
        + 18 * PowerSeries.X ^ 3 + 11 * PowerSeries.X ^ 4) : PowerSeries ℤ)
        = PowerSeries.C 15 * PowerSeries.X ^ 1 + PowerSeries.C 20 * PowerSeries.X ^ 2
        + PowerSeries.C 21 * PowerSeries.X ^ 3 + PowerSeries.C 18 * PowerSeries.X ^ 4
        + PowerSeries.C 11 * PowerSeries.X ^ 5 := by
      simp only [map_ofNat]
      ring
    rw [hX, hR]
    obtain ⟨v1, v2, v3, v4, v5⟩ := A242235.vals
    ext n
    simp only [mul_sub, mul_one, map_sub, map_add, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    by_cases hn : n < 6
    · interval_cases n <;> simp [v1, v2, v3, v4, v5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have h : OMA.S_oeis_a242235.a (m + 6) = OMA.S_oeis_a242235.a (m + 5)
          + OMA.S_oeis_a242235.a (m + 4) + OMA.S_oeis_a242235.a (m + 3)
          + OMA.S_oeis_a242235.a (m + 2) + OMA.S_oeis_a242235.a (m + 1) := A242235.rec5 (m + 1) (by omega)
      have h' : (OMA.S_oeis_a242235.a (m + 6) : ℤ) = OMA.S_oeis_a242235.a (m + 5)
          + OMA.S_oeis_a242235.a (m + 4) + OMA.S_oeis_a242235.a (m + 3)
          + OMA.S_oeis_a242235.a (m + 2) + OMA.S_oeis_a242235.a (m + 1) := by exact_mod_cast h
      have e1 : m + 6 - 1 = m + 5 := by omega
      have e2 : m + 6 - 2 = m + 4 := by omega
      have e3 : m + 6 - 3 = m + 3 := by omega
      have e4 : m + 6 - 4 = m + 2 := by omega
      have e5 : m + 6 - 5 = m + 1 := by omega
      simp only [e1, e2, e3, e4, e5]
      simp
      linarith
