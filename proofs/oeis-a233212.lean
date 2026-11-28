import OMAStatements.S_oeis_a233212

namespace A233212Proof

open OMA.S_oeis_a233212 PowerSeries Finset

abbrev Sym := Bool × Bool × Bool

def applySym (g : Sym) (v : Fin 6) : Fin 6 :=
  let v1 : Fin 6 := match v with
    | ⟨1, _⟩ => if g.1 then 4 else 1
    | ⟨4, _⟩ => if g.1 then 1 else 4
    | ⟨2, _⟩ => if g.2.1 then 3 else 2
    | ⟨3, _⟩ => if g.2.1 then 2 else 3
    | x => x
  if g.2.2 then
    match v1 with
    | ⟨1, _⟩ => 2
    | ⟨4, _⟩ => 3
    | ⟨2, _⟩ => 1
    | ⟨3, _⟩ => 4
    | x => x
  else v1

def invSym (g : Sym) : Sym :=
  if g.2.2 then (g.2.1, g.1, true) else (g.1, g.2.1, false)

lemma applySym_inv (g : Sym) (v : Fin 6) : applySym (invSym g) (applySym g v) = v := by
  revert g v; decide

lemma applySym_inv' (g : Sym) (v : Fin 6) : applySym g (applySym (invSym g) v) = v := by
  revert g v; decide

lemma applySym_zero (g : Sym) : applySym g 0 = 0 := by
  revert g; decide

lemma applySym_sum_ne5 (g : Sym) (a b : Fin 6) :
    (applySym g a).val + (applySym g b).val ≠ 5 ↔ a.val + b.val ≠ 5 := by
  revert g a b; decide

def symArr {n : ℕ} (g : Sym) (x : Fin n → Fin 3 → Fin 6) : Fin n → Fin 3 → Fin 6 :=
  fun i j => applySym g (x i j)

lemma symArr_inv {n : ℕ} (g : Sym) (x : Fin n → Fin 3 → Fin 6) :
    symArr (invSym g) (symArr g x) = x := by
  funext i j; exact applySym_inv g (x i j)

lemma symArr_inv' {n : ℕ} (g : Sym) (x : Fin n → Fin 3 → Fin 6) :
    symArr g (symArr (invSym g) x) = x := by
  funext i j; exact applySym_inv' g (x i j)

lemma cond_symArr {n : ℕ} (g : Sym) (x : Fin n → Fin 3 → Fin 6) :
    Cond (symArr g x) ↔ Cond x := by
  unfold Cond symArr
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j j' hj => (applySym_sum_ne5 g _ _).mp (h1 i j j' hj),
           fun i i' j j' hi hj => (applySym_sum_ne5 g _ _).mp (h2 i i' j j' hi hj)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j j' hj => (applySym_sum_ne5 g _ _).mpr (h1 i j j' hj),
           fun i i' j j' hi hj => (applySym_sum_ne5 g _ _).mpr (h2 i i' j j' hi hj)⟩

def TopZero {n : ℕ} (x : Fin n → Fin 3 → Fin 6) : Prop :=
  ∀ i j, i.val = 0 → j.val = 0 → x i j = 0

instance {n : ℕ} : DecidablePred (@TopZero n) := fun x => by unfold TopZero; infer_instance

lemma topZero_symArr {n : ℕ} (g : Sym) (x : Fin n → Fin 3 → Fin 6) :
    TopZero (symArr g x) ↔ TopZero x := by
  unfold TopZero symArr
  constructor
  · intro h i j hi hj
    have hv := congrArg (applySym (invSym g)) (h i j hi hj)
    rw [applySym_inv, applySym_zero] at hv
    exact hv
  · intro h i j hi hj
    rw [h i j hi hj, applySym_zero]

lemma eq_zero_of_no_mid {n : ℕ} (x : Fin n → Fin 3 → Fin 6)
    (hc : Cond x) (htz : TopZero x)
    (hno : ∀ i j, x i j = 0 ∨ x i j = 5) : x = fun _ _ => 0 := by
  have hrow : ∀ (i : ℕ) (hi : i < n), ∀ j : Fin 3, x ⟨i, hi⟩ j = 0 := by
    intro i
    induction i with
    | zero =>
      intro hi j
      have h0 : x ⟨0, hi⟩ 0 = 0 := htz ⟨0, hi⟩ 0 rfl rfl
      have h1 : x ⟨0, hi⟩ 1 = 0 := by
        rcases hno ⟨0, hi⟩ 1 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨0, hi⟩ 0 1 rfl; rw [h0, h] at this; exact this rfl
      have h2 : x ⟨0, hi⟩ 2 = 0 := by
        rcases hno ⟨0, hi⟩ 2 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨0, hi⟩ 1 2 rfl; rw [h1, h] at this; exact this rfl
      fin_cases j <;> assumption
    | succ i ih =>
      intro hi j
      have hip : x ⟨i, by omega⟩ 1 = 0 := ih (by omega) 1
      have h0 : x ⟨i + 1, hi⟩ 0 = 0 := by
        rcases hno ⟨i + 1, hi⟩ 0 with h | h
        · exact h
        · exfalso; have := hc.2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ 1 0 rfl rfl
          rw [hip, h] at this; exact this rfl
      have h1 : x ⟨i + 1, hi⟩ 1 = 0 := by
        rcases hno ⟨i + 1, hi⟩ 1 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨i + 1, hi⟩ 0 1 rfl; rw [h0, h] at this; exact this rfl
      have h2 : x ⟨i + 1, hi⟩ 2 = 0 := by
        rcases hno ⟨i + 1, hi⟩ 2 with h | h
        · exact h
        · exfalso; have := hc.1 ⟨i + 1, hi⟩ 1 2 rfl; rw [h1, h] at this; exact this rfl
      fin_cases j <;> assumption
  funext i j; exact hrow i.1 i.2 j

lemma norm_zero (n : ℕ) : Norm (fun (_ : Fin n) (_ : Fin 3) => (0 : Fin 6)) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

lemma cond_zero (n : ℕ) : Cond (fun (_ : Fin n) (_ : Fin 3) => (0 : Fin 6)) := by
  refine ⟨fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩

def inP14 (v : Fin 6) : Prop := v = 1 ∨ v = 4
def inP23 (v : Fin 6) : Prop := v = 2 ∨ v = 3
def inMid (v : Fin 6) : Prop := v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4

instance : DecidablePred inP14 := fun v => by unfold inP14; infer_instance
instance : DecidablePred inP23 := fun v => by unfold inP23; infer_instance
instance : DecidablePred inMid := fun v => by unfold inMid; infer_instance

lemma applySym_inP14_iff (g : Sym) (v : Fin 6) :
    inP14 (applySym g v) ↔ if g.2.2 then inP23 v else inP14 v := by revert g v; decide

lemma applySym_inP23_iff (g : Sym) (v : Fin 6) :
    inP23 (applySym g v) ↔ if g.2.2 then inP14 v else inP23 v := by revert g v; decide

lemma applySym_inMid_iff (g : Sym) (v : Fin 6) :
    inMid (applySym g v) ↔ inMid v := by revert g v; decide

lemma applySym_snd_false_of_eq_one (g : Sym) (v : Fin 6) (h1 : applySym g v = 1) (hp : inP14 v) :
    g.2.2 = false := by revert g v h1 hp; decide

lemma applySym_snd_true_of_eq_one (g : Sym) (v : Fin 6) (h1 : applySym g v = 1) (hp : inP23 v) :
    g.2.2 = true := by revert g v h1 hp; decide

lemma applySym_g0_false_1 (v w : Fin 6) (hp : inP14 v) :
    applySym (v == 4, w == 3, false) v = 1 := by revert v w hp; decide

lemma applySym_g0_false_2 (v w : Fin 6) (hp : inP23 w) :
    applySym (v == 4, w == 3, false) w = 2 := by revert v w hp; decide

lemma applySym_g0_false_uniq (b1 b2 : Bool) (v w : Fin 6)
    (hp1 : inP14 v) (hp2 : inP23 w)
    (h1 : applySym (b1, b2, false) v = 1) (h2 : applySym (b1, b2, false) w = 2) :
    (b1, b2, false) = (v == 4, w == 3, false) := by revert b1 b2 v w hp1 hp2 h1 h2; decide

lemma applySym_g0_true_1 (v w : Fin 6) (hp : inP23 v) :
    applySym (w == 4, v == 3, true) v = 1 := by revert v w hp; decide

lemma applySym_g0_true_2 (v w : Fin 6) (hp : inP14 w) :
    applySym (w == 4, v == 3, true) w = 2 := by revert v w hp; decide

lemma applySym_g0_true_uniq (b1 b2 : Bool) (v w : Fin 6)
    (hp1 : inP23 v) (hp2 : inP14 w)
    (h1 : applySym (b1, b2, true) v = 1) (h2 : applySym (b1, b2, true) w = 2) :
    (b1, b2, true) = (w == 4, v == 3, true) := by revert b1 b2 v w hp1 hp2 h1 h2; decide

lemma fin6_zero_or_five (v : Fin 6) (h1 : ¬ inP14 v) (h2 : ¬ inP23 v) : v = 0 ∨ v = 5 := by
  revert v h1 h2; decide

lemma fin6_inP23_of_mid_not_14 (v : Fin 6) (hm : inMid v) (h1 : ¬ inP14 v) : inP23 v := by
  revert v hm h1; decide

lemma hord3 {n : ℕ} (i' i : Fin n) (j' j : Fin 3) :
    (i' < i ∨ (i' = i ∧ j' < j)) ↔ i'.1 * 3 + j'.1 < i.1 * 3 + j.1 := by
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · have := j'.2; have := j.2; have : i'.1 < i.1 := h; omega
    · have : j'.1 < j.1 := h; omega
  · intro h
    by_cases heq : i'.1 = i.1
    · right; exact ⟨Fin.ext heq, by show j'.1 < j.1; omega⟩
    · left; show i'.1 < i.1; have := j'.2; have := j.2; omega

lemma sym_exists_unique_both {n : ℕ} (x : Fin n → Fin 3 → Fin 6) (htz : TopZero x)
    (h14 : ∃ i j, inP14 (x i j)) (h23 : ∃ i j, inP23 (x i j)) :
    ∃! g : Sym, Norm (symArr g x) := by
  classical
  have hexM : ∃ k : ℕ, ∃ (i : Fin n) (j : Fin 3), i.1 * 3 + j.1 = k ∧ inMid (x i j) := by
    rcases h14 with ⟨i, j, h⟩
    refine ⟨i.1 * 3 + j.1, i, j, rfl, ?_⟩
    rcases h with h | h <;> simp [inMid, h]
  let k1 := Nat.find hexM
  have hk1 := Nat.find_spec hexM
  have hmin1 : ∀ (i' : Fin n) (j' : Fin 3), i'.1 * 3 + j'.1 < k1 → ¬ inMid (x i' j') :=
    fun i' j' hlt hm => Nat.find_min hexM hlt ⟨i', j', rfl, hm⟩
  rcases hk1 with ⟨i1, j1, hpos1, hm1⟩
  have huniq_pos : ∀ (i a : Fin n) (j b : Fin 3), i.1 * 3 + j.1 = a.1 * 3 + b.1 → i = a ∧ j = b := by
    intro i a j b heq; have := j.2; have := b.2
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  have hsym_norm_iff : ∀ g : Sym, Norm (symArr g x) ↔
      applySym g (x i1 j1) = 1 ∧
      ∃ i2 j2, (∀ i' j', i'.1 * 3 + j'.1 < i2.1 * 3 + j2.1 → ¬ inP23 (applySym g (x i' j'))) ∧
        applySym g (x i2 j2) = 2 := by
    intro g
    constructor
    · intro hng
      have h1 : applySym g (x i1 j1) = 1 := by
        have hm : inMid (applySym g (x i1 j1)) := (applySym_inMid_iff g _).mpr hm1
        rcases hm with h | h | h | h
        · exact h
        · exfalso; rcases hng.2.1 i1 j1 (Or.inl h) with ⟨i', j', hlt, hx1⟩
          have : inMid (x i' j') := (applySym_inMid_iff g _).mp (Or.inl hx1)
          exact hmin1 i' j' (by dsimp only [k1]; rw [← hpos1]; exact (hord3 _ _ _ _).mp hlt) this
        · exfalso; rcases hng.2.1 i1 j1 (Or.inr (Or.inl h)) with ⟨i', j', hlt, hx1⟩
          have : inMid (x i' j') := (applySym_inMid_iff g _).mp (Or.inl hx1)
          exact hmin1 i' j' (by dsimp only [k1]; rw [← hpos1]; exact (hord3 _ _ _ _).mp hlt) this
        · exfalso; rcases hng.2.1 i1 j1 (Or.inr (Or.inr h)) with ⟨i', j', hlt, hx1⟩
          have : inMid (x i' j') := (applySym_inMid_iff g _).mp (Or.inl hx1)
          exact hmin1 i' j' (by dsimp only [k1]; rw [← hpos1]; exact (hord3 _ _ _ _).mp hlt) this
      have hex23 : ∃ k, ∃ i j, i.1 * 3 + j.1 = k ∧ inP23 (applySym g (x i j)) := by
        by_cases hs : g.2.2
        · rcases h14 with ⟨i, j, h⟩
          exact ⟨i.1 * 3 + j.1, i, j, rfl, (applySym_inP23_iff g _).mpr (by simp [hs, h])⟩
        · rcases h23 with ⟨i, j, h⟩
          exact ⟨i.1 * 3 + j.1, i, j, rfl, (applySym_inP23_iff g _).mpr (by simp [hs, h])⟩
      rcases Nat.find_spec hex23 with ⟨i2, j2, hpos2, hm2⟩
      have hmin2 : ∀ i' j', i'.1 * 3 + j'.1 < i2.1 * 3 + j2.1 → ¬ inP23 (applySym g (x i' j')) := by
        intro i' j' hlt hm; exact Nat.find_min hex23 (by rw [← hpos2]; exact hlt) ⟨i', j', rfl, hm⟩
      refine ⟨h1, i2, j2, hmin2, ?_⟩
      rcases hm2 with h2 | h3
      · exact h2
      · exfalso; rcases hng.2.2 i2 j2 h3 with ⟨i', j', hlt, hx2⟩
        exact hmin2 i' j' ((hord3 _ _ _ _).mp hlt) (Or.inl hx2)
    · rintro ⟨h1, i2, j2, hmin2, h2⟩
      refine ⟨(topZero_symArr g x).mpr htz, ?_, ?_⟩
      · intro i j h234
        have hm : inMid (x i j) := (applySym_inMid_iff g _).mp (by rcases h234 with h | h | h <;> simp [inMid, symArr] at h ⊢ <;> simp [h])
        have hge : k1 ≤ i.1 * 3 + j.1 := by by_contra hlt; exact hmin1 i j (by omega) hm
        have hne : i1.1 * 3 + j1.1 ≠ i.1 * 3 + j.1 := by
          intro heq
          rcases huniq_pos i1 i j1 j heq with ⟨rfl, rfl⟩
          simp only [symArr, h1] at h234
          rcases h234 with h | h | h <;> exact absurd h (by decide)
        exact ⟨i1, j1, (hord3 _ _ _ _).mpr (by dsimp only [k1] at hge; omega), h1⟩
      · intro i j h3
        have hge : i2.1 * 3 + j2.1 ≤ i.1 * 3 + j.1 := by
          by_contra hlt; exact hmin2 i j (by omega) (Or.inr h3)
        have hne : i2.1 * 3 + j2.1 ≠ i.1 * 3 + j.1 := by
          intro heq
          rcases huniq_pos i2 i j2 j heq with ⟨rfl, rfl⟩
          simp only [symArr, h2] at h3; exact absurd h3 (by decide)
        exact ⟨i2, j2, (hord3 _ _ _ _).mpr (by omega), h2⟩
  by_cases hp1 : inP14 (x i1 j1)
  · have hex2 : ∃ k, ∃ i j, i.1 * 3 + j.1 = k ∧ inP23 (x i j) := by
      rcases h23 with ⟨i, j, h⟩; exact ⟨i.1 * 3 + j.1, i, j, rfl, h⟩
    rcases Nat.find_spec hex2 with ⟨i2, j2, hpos2, hp2⟩
    have hmin2 : ∀ i' j', i'.1 * 3 + j'.1 < i2.1 * 3 + j2.1 → ¬ inP23 (x i' j') :=
      fun i' j' hlt hm => Nat.find_min hex2 (by rw [← hpos2]; exact hlt) ⟨i', j', rfl, hm⟩
    let g0 : Sym := (x i1 j1 == 4, x i2 j2 == 3, false)
    refine ⟨g0, (hsym_norm_iff g0).mpr ⟨applySym_g0_false_1 _ _ hp1, i2, j2,
      fun i' j' hlt => by rw [applySym_inP23_iff]; simp; exact hmin2 i' j' hlt,
      applySym_g0_false_2 _ _ hp2⟩, ?_⟩
    intro g hng
    rcases (hsym_norm_iff g).mp hng with ⟨hg1, i2', j2', hmin2', hg2⟩
    have hgf : g.2.2 = false := applySym_snd_false_of_eq_one g _ hg1 hp1
    have h23_eq : ∀ v, inP23 (applySym g v) ↔ inP23 v := fun v => by rw [applySym_inP23_iff, hgf]; simp
    have hi2eq : i2' = i2 ∧ j2' = j2 := by
      have hle1 : i2'.1 * 3 + j2'.1 ≤ i2.1 * 3 + j2.1 := by
        by_contra hlt; exact hmin2' i2 j2 (by omega) ((h23_eq _).mpr hp2)
      have hle2 : i2.1 * 3 + j2.1 ≤ i2'.1 * 3 + j2'.1 := by
        by_contra hlt; exact hmin2 i2' j2' (by omega) ((h23_eq _).mp (Or.inl hg2))
      exact huniq_pos i2' i2 j2' j2 (by omega)
    rcases hi2eq with ⟨rfl, rfl⟩
    rcases g with ⟨b1, b2, bs⟩
    dsimp only at hgf; subst hgf
    exact applySym_g0_false_uniq b1 b2 _ _ hp1 hp2 hg1 hg2
  · have hp1' : inP23 (x i1 j1) := fin6_inP23_of_mid_not_14 _ hm1 hp1
    have hex2 : ∃ k, ∃ i j, i.1 * 3 + j.1 = k ∧ inP14 (x i j) := by
      rcases h14 with ⟨i, j, h⟩; exact ⟨i.1 * 3 + j.1, i, j, rfl, h⟩
    rcases Nat.find_spec hex2 with ⟨i2, j2, hpos2, hp2⟩
    have hmin2 : ∀ i' j', i'.1 * 3 + j'.1 < i2.1 * 3 + j2.1 → ¬ inP14 (x i' j') :=
      fun i' j' hlt hm => Nat.find_min hex2 (by rw [← hpos2]; exact hlt) ⟨i', j', rfl, hm⟩
    let g0 : Sym := (x i2 j2 == 4, x i1 j1 == 3, true)
    refine ⟨g0, (hsym_norm_iff g0).mpr ⟨applySym_g0_true_1 _ _ hp1', i2, j2,
      fun i' j' hlt => by rw [applySym_inP23_iff]; exact hmin2 i' j' hlt,
      applySym_g0_true_2 _ _ hp2⟩, ?_⟩
    intro g hng
    rcases (hsym_norm_iff g).mp hng with ⟨hg1, i2', j2', hmin2', hg2⟩
    have hgt : g.2.2 = true := applySym_snd_true_of_eq_one g _ hg1 hp1'
    have h23_eq : ∀ v, inP23 (applySym g v) ↔ inP14 v := fun v => by rw [applySym_inP23_iff, hgt]; simp
    have hi2eq : i2' = i2 ∧ j2' = j2 := by
      have hle1 : i2'.1 * 3 + j2'.1 ≤ i2.1 * 3 + j2.1 := by
        by_contra hlt; exact hmin2' i2 j2 (by omega) ((h23_eq _).mpr hp2)
      have hle2 : i2.1 * 3 + j2.1 ≤ i2'.1 * 3 + j2'.1 := by
        by_contra hlt; exact hmin2 i2' j2' (by omega) ((h23_eq _).mp (Or.inl hg2))
      exact huniq_pos i2' i2 j2' j2 (by omega)
    rcases hi2eq with ⟨rfl, rfl⟩
    rcases g with ⟨b1, b2, bs⟩
    dsimp only at hgt; subst hgt
    exact applySym_g0_true_uniq b1 b2 _ _ hp1' hp2 hg1 hg2

lemma norm_xor_swap14 {n : ℕ} (x : Fin n → Fin 3 → Fin 6)
    (htz : TopZero x) (h14 : ∃ i j, inP14 (x i j)) (hno23 : ∀ i j, ¬ inP23 (x i j)) :
    Norm x ↔ ¬ Norm (symArr (true, false, false) x) := by
  classical
  have hex : ∃ k, ∃ i j, i.1 * 3 + j.1 = k ∧ inP14 (x i j) := by
    rcases h14 with ⟨i, j, h⟩; exact ⟨i.1 * 3 + j.1, i, j, rfl, h⟩
  let k0 := Nat.find hex
  rcases Nat.find_spec hex with ⟨i0, j0, hpos, hp0⟩
  have hmin : ∀ i' j', i'.1 * 3 + j'.1 < k0 → ¬ inP14 (x i' j') :=
    fun i' j' hlt hm => Nat.find_min hex hlt ⟨i', j', rfl, hm⟩
  have hno23s : ∀ i j, ¬ inP23 (symArr (true, false, false) x i j) := by
    intro i j; simp only [symArr, applySym_inP23_iff]; simp [hno23 i j]
  have huniq : ∀ (i a : Fin n) (j b : Fin 3), i.1 * 3 + j.1 = a.1 * 3 + b.1 → i = a ∧ j = b := by
    intro i a j b heq; have := j.2; have := b.2; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  rcases hp0 with h1 | h4
  · have hnx : Norm x := by
      refine ⟨htz, fun i j h234 => ?_, fun i j h3 => absurd (Or.inr h3) (hno23 i j)⟩
      have h4' : x i j = 4 := by
        rcases h234 with h | h | h
        · exact absurd (Or.inl h) (hno23 i j)
        · exact absurd (Or.inr h) (hno23 i j)
        · exact h
      have hge : k0 ≤ i.1 * 3 + j.1 := by by_contra hlt; exact hmin i j (by omega) (Or.inr h4')
      have hne : i0.1 * 3 + j0.1 ≠ i.1 * 3 + j.1 := by
        intro heq; rcases huniq i0 i j0 j heq with ⟨rfl, rfl⟩
        rw [h4'] at h1; exact absurd h1 (by decide)
      exact ⟨i0, j0, (hord3 _ _ _ _).mpr (by dsimp only [k0] at hge; omega), h1⟩
    have hns : ¬ Norm (symArr (true, false, false) x) := by
      intro hns
      have hs4 : symArr (true, false, false) x i0 j0 = 4 := by dsimp [symArr]; rw [h1]; rfl
      rcases hns.2.1 i0 j0 (Or.inr (Or.inr hs4)) with ⟨i', j', hlt, hs1⟩
      have hx4 : x i' j' = 4 := by
        have hv := congrArg (applySym (true, false, false)) hs1
        dsimp only [symArr] at hv
        have : applySym (true, false, false) (applySym (true, false, false) (x i' j')) = x i' j' :=
          applySym_inv (true, false, false) (x i' j')
        rw [this] at hv; exact hv
      exact hmin i' j' (by dsimp only [k0]; rw [← hpos]; exact (hord3 _ _ _ _).mp hlt) (Or.inr hx4)
    exact ⟨fun _ => hns, fun _ => hnx⟩
  · have hnx : ¬ Norm x := by
      intro hnx
      rcases hnx.2.1 i0 j0 (Or.inr (Or.inr h4)) with ⟨i', j', hlt, hx1⟩
      exact hmin i' j' (by dsimp only [k0]; rw [← hpos]; exact (hord3 _ _ _ _).mp hlt) (Or.inl hx1)
    have hns : Norm (symArr (true, false, false) x) := by
      refine ⟨(topZero_symArr _ x).mpr htz, fun i j h234 => ?_, fun i j h3 => absurd (Or.inr h3) (hno23s i j)⟩
      have hs4 : symArr (true, false, false) x i j = 4 := by
        rcases h234 with h | h | h
        · exact absurd (Or.inl h) (hno23s i j)
        · exact absurd (Or.inr h) (hno23s i j)
        · exact h
      have hx1 : x i j = 1 := by
        have hv := congrArg (applySym (true, false, false)) hs4
        dsimp only [symArr] at hv
        have : applySym (true, false, false) (applySym (true, false, false) (x i j)) = x i j :=
          applySym_inv (true, false, false) (x i j)
        rw [this] at hv; exact hv
      have hge : k0 ≤ i.1 * 3 + j.1 := by by_contra hlt; exact hmin i j (by omega) (Or.inl hx1)
      have hne : i0.1 * 3 + j0.1 ≠ i.1 * 3 + j.1 := by
        intro heq; rcases huniq i0 i j0 j heq with ⟨rfl, rfl⟩
        rw [hx1] at h4; exact absurd h4 (by decide)
      exact ⟨i0, j0, (hord3 _ _ _ _).mpr (by dsimp only [k0] at hge; omega), by dsimp [symArr]; rw [h4]; rfl⟩
    exact ⟨fun h => absurd h hnx, fun h => absurd hns h⟩

def U6 (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 3 → Fin 6)).filter (fun x => Cond x ∧ TopZero x)).card

def U14 (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 3 → Fin 6)).filter
    (fun x => Cond x ∧ TopZero x ∧ ∀ i j, ¬ inP23 (x i j))).card

def validRow6 (r : Fin 3 → Fin 6) : Prop :=
  ∀ j j' : Fin 3, j'.val = j.val + 1 → (r j).val + (r j').val ≠ 5

def validNext6 (r r' : Fin 3 → Fin 6) : Prop :=
  validRow6 r' ∧ ∀ j j' : Fin 3, j.val = j'.val + 1 → (r j).val + (r' j').val ≠ 5

instance : DecidablePred validRow6 := fun r => by unfold validRow6; infer_instance
instance (r : Fin 3 → Fin 6) : DecidablePred (validNext6 r) := fun r' => by unfold validNext6; infer_instance

lemma sum_validNext6 : ∀ x1 x2 : Fin 6, x1.val + x2.val ≠ 5 →
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if a.val + b.val ≠ 5 ∧ b.val + c.val ≠ 5 ∧ x1.val + a.val ≠ 5 ∧ x2.val + b.val ≠ 5
      then 1 else 0) = 105 := by decide

lemma sum_validNext14 : ∀ x1 x2 : Fin 6, x1.val + x2.val ≠ 5 → ¬ inP23 x1 → ¬ inP23 x2 →
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if (a.val + b.val ≠ 5 ∧ b.val + c.val ≠ 5 ∧ x1.val + a.val ≠ 5 ∧ x2.val + b.val ≠ 5) ∧
         ¬ inP23 a ∧ ¬ inP23 b ∧ ¬ inP23 c
      then 1 else 0) = 21 := by decide

lemma card_validNext6 (r : Fin 3 → Fin 6) (hr : validRow6 r) :
    ((univ : Finset (Fin 3 → Fin 6)).filter (validNext6 r)).card = 105 := by
  rw [← Fintype.card_subtype]
  have hbij : Fintype.card { r' : Fin 3 → Fin 6 // validNext6 r r' } =
      Fintype.card { t : Fin 6 × Fin 6 × Fin 6 //
        t.1.val + t.2.1.val ≠ 5 ∧ t.2.1.val + t.2.2.val ≠ 5 ∧
        (r 1).val + t.1.val ≠ 5 ∧ (r 2).val + t.2.1.val ≠ 5 } := by
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨r', hr'⟩
      exact ⟨(r' 0, r' 1, r' 2), ⟨hr'.1 0 1 rfl, hr'.1 1 2 rfl, hr'.2 1 0 rfl, hr'.2 2 1 rfl⟩⟩
    · intro ⟨⟨a, b, c⟩, ht⟩
      let r' : Fin 3 → Fin 6 := fun j => match j with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c
      refine ⟨r', ⟨?_, ?_⟩⟩
      · intro j j' hj; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact ht.1
        · exact ht.2.1
      · intro j j' hj; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact ht.2.2.1
        · exact ht.2.2.2
    · intro ⟨r', _⟩; apply Subtype.ext; funext j; fin_cases j <;> rfl
    · intro ⟨⟨a, b, c⟩, _⟩; rfl
  rw [hbij, Fintype.card_subtype, Finset.card_filter]
  simp_rw [Fintype.sum_prod_type]
  exact sum_validNext6 (r 1) (r 2) (hr 1 2 rfl)

lemma card_validNext14 (r : Fin 3 → Fin 6) (hr : validRow6 r) (hno : ∀ j, ¬ inP23 (r j)) :
    ((univ : Finset (Fin 3 → Fin 6)).filter (fun r' => validNext6 r r' ∧ ∀ j, ¬ inP23 (r' j))).card = 21 := by
  rw [← Fintype.card_subtype]
  have hbij : Fintype.card { r' : Fin 3 → Fin 6 // validNext6 r r' ∧ ∀ j, ¬ inP23 (r' j) } =
      Fintype.card { t : Fin 6 × Fin 6 × Fin 6 //
        (t.1.val + t.2.1.val ≠ 5 ∧ t.2.1.val + t.2.2.val ≠ 5 ∧
         (r 1).val + t.1.val ≠ 5 ∧ (r 2).val + t.2.1.val ≠ 5) ∧
        ¬ inP23 t.1 ∧ ¬ inP23 t.2.1 ∧ ¬ inP23 t.2.2 } := by
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨r', hr'⟩
      exact ⟨(r' 0, r' 1, r' 2),
        ⟨⟨hr'.1.1 0 1 rfl, hr'.1.1 1 2 rfl, hr'.1.2 1 0 rfl, hr'.1.2 2 1 rfl⟩,
         hr'.2 0, hr'.2 1, hr'.2 2⟩⟩
    · intro ⟨⟨a, b, c⟩, ht⟩
      let r' : Fin 3 → Fin 6 := fun j => match j with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c
      refine ⟨r', ⟨?_, ?_⟩, ?_⟩
      · intro j j' hj; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact ht.1.1
        · exact ht.1.2.1
      · intro j j' hj; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact ht.1.2.2.1
        · exact ht.1.2.2.2
      · intro j; fin_cases j
        · exact ht.2.1
        · exact ht.2.2.1
        · exact ht.2.2.2
    · intro ⟨r', _⟩; apply Subtype.ext; funext j; fin_cases j <;> rfl
    · intro ⟨⟨a, b, c⟩, _⟩; rfl
  rw [hbij, Fintype.card_subtype, Finset.card_filter]
  simp_rw [Fintype.sum_prod_type]
  exact sum_validNext14 (r 1) (r 2) (hr 1 2 rfl) (hno 1) (hno 2)

lemma sum_U6_1 : (∑ a : Fin 6, ∑ b : Fin 6,
    if (0 : Fin 6).val + a.val ≠ 5 ∧ a.val + b.val ≠ 5 then 1 else 0) = 25 := by decide

lemma sum_U14_1 : (∑ a : Fin 6, ∑ b : Fin 6,
    if ((0 : Fin 6).val + a.val ≠ 5 ∧ a.val + b.val ≠ 5) ∧ ¬ inP23 a ∧ ¬ inP23 b then 1 else 0) = 9 := by decide

lemma U6_one : U6 1 = 25 := by
  unfold U6
  rw [← Fintype.card_subtype]
  have hbij : Fintype.card { x : Fin 1 → Fin 3 → Fin 6 // Cond x ∧ TopZero x } =
      Fintype.card { t : Fin 6 × Fin 6 // (0 : Fin 6).val + t.1.val ≠ 5 ∧ t.1.val + t.2.val ≠ 5 } := by
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨x, hx⟩
      have h0 : x 0 0 = 0 := hx.2 0 0 rfl rfl
      exact ⟨(x 0 1, x 0 2), ⟨by rw [← h0]; exact hx.1.1 0 0 1 rfl, hx.1.1 0 1 2 rfl⟩⟩
    · intro ⟨⟨a, b⟩, ht⟩
      let x : Fin 1 → Fin 3 → Fin 6 := fun _ j => match j with | ⟨0, _⟩ => 0 | ⟨1, _⟩ => a | ⟨2, _⟩ => b
      refine ⟨x, ⟨?_, ?_⟩, ?_⟩
      · intro i j j' hj; fin_cases i; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact ht.1
        · exact ht.2
      · intro i i' _ _ hi _; fin_cases i; fin_cases i'; simp at hi
      · intro i j _ hj; fin_cases i; fin_cases j <;> simp at hj ⊢; rfl
    · intro ⟨x, hx⟩; apply Subtype.ext; funext i j; fin_cases i; fin_cases j
      · exact (hx.2 0 0 rfl rfl).symm
      · rfl
      · rfl
    · intro ⟨⟨a, b⟩, _⟩; rfl
  rw [hbij, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  exact sum_U6_1

lemma U14_one : U14 1 = 9 := by
  unfold U14
  rw [← Fintype.card_subtype]
  have hbij : Fintype.card { x : Fin 1 → Fin 3 → Fin 6 // Cond x ∧ TopZero x ∧ ∀ i j, ¬ inP23 (x i j) } =
      Fintype.card { t : Fin 6 × Fin 6 //
        ((0 : Fin 6).val + t.1.val ≠ 5 ∧ t.1.val + t.2.val ≠ 5) ∧ ¬ inP23 t.1 ∧ ¬ inP23 t.2 } := by
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨x, hx⟩
      have h0 : x 0 0 = 0 := hx.2.1 0 0 rfl rfl
      exact ⟨(x 0 1, x 0 2), ⟨⟨by rw [← h0]; exact hx.1.1 0 0 1 rfl, hx.1.1 0 1 2 rfl⟩,
        hx.2.2 0 1, hx.2.2 0 2⟩⟩
    · intro ⟨⟨a, b⟩, ht⟩
      let x : Fin 1 → Fin 3 → Fin 6 := fun _ j => match j with | ⟨0, _⟩ => 0 | ⟨1, _⟩ => a | ⟨2, _⟩ => b
      refine ⟨x, ⟨?_, ?_⟩, ?_, ?_⟩
      · intro i j j' hj; fin_cases i; fin_cases j <;> fin_cases j' <;> simp at hj
        · exact ht.1.1
        · exact ht.1.2
      · intro i i' _ _ hi _; fin_cases i; fin_cases i'; simp at hi
      · intro i j _ hj; fin_cases i; fin_cases j <;> simp at hj ⊢; rfl
      · intro i j; fin_cases i; fin_cases j
        · simp [x, inP23]
        · exact ht.2.1
        · exact ht.2.2
    · intro ⟨x, hx⟩; apply Subtype.ext; funext i j; fin_cases i; fin_cases j
      · exact (hx.2.1 0 0 rfl rfl).symm
      · rfl
      · rfl
    · intro ⟨⟨a, b⟩, _⟩; rfl
  rw [hbij, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  exact sum_U14_1

lemma U6_succ (n : ℕ) (hn : 1 ≤ n) : U6 (n + 1) = 105 * U6 n := by
  let S (m : ℕ) := (univ : Finset (Fin m → Fin 3 → Fin 6)).filter (fun x => Cond x ∧ TopZero x)
  change (S (n + 1)).card = 105 * (S n).card
  let init : (Fin (n + 1) → Fin 3 → Fin 6) → (Fin n → Fin 3 → Fin 6) := fun x i => x ⟨i.1, by omega⟩
  let snoc : (Fin n → Fin 3 → Fin 6) → (Fin 3 → Fin 6) → (Fin (n + 1) → Fin 3 → Fin 6) :=
    fun x r i => if h : (i : ℕ) < n then x ⟨i.1, h⟩ else r
  have hbij : (S (n + 1)).card =
      ((S n).sigma (fun x => (univ : Finset (Fin 3 → Fin 6)).filter (validNext6 (x ⟨n - 1, by omega⟩)))).card := by
    symm
    refine Finset.card_bij (fun p _ => snoc p.1 p.2) ?_ ?_ ?_
    · intro ⟨x, r⟩ hp
      simp only [mem_sigma, S, mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i j j' hj; dsimp only [snoc]; split_ifs with hi
        · exact hp.1.1.1 ⟨i.1, hi⟩ j j' hj
        · exact hp.2.1 j j' hj
      · intro i i' j j' hi hj; dsimp only [snoc]
        by_cases hi' : (i' : ℕ) < n
        · have hi1 : (i : ℕ) < n := by omega
          simp only [hi1, hi', ↓reduceDIte]; exact hp.1.1.2 ⟨i.1, hi1⟩ ⟨i'.1, hi'⟩ j j' hi hj
        · have hi1 : (i : ℕ) < n := by omega
          have hieq : (⟨i.1, hi1⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          simp only [hi1, hi', ↓reduceDIte, hieq]
          exact hp.2.2 j j' hj
      · intro i j hi hj; dsimp only [snoc]
        have h0 : (i : ℕ) < n := by omega
        simp only [h0, ↓reduceDIte]; exact hp.1.2 ⟨i.1, h0⟩ j hi hj
    · intro ⟨x1, r1⟩ _ ⟨x2, r2⟩ _ heq
      have hx : x1 = x2 := by funext i j; simpa [snoc, i.2] using congrFun (congrFun heq ⟨i.1, by omega⟩) j
      have hr : r1 = r2 := by funext j; simpa [snoc] using congrFun (congrFun heq ⟨n, Nat.lt_succ_self n⟩) j
      subst hx; subst hr; rfl
    · intro y hy
      simp only [S, mem_filter, mem_univ, true_and] at hy
      refine ⟨⟨init y, y ⟨n, Nat.lt_succ_self n⟩⟩, ?_, ?_⟩
      · simp only [mem_sigma, S, mem_filter, mem_univ, true_and]
        refine ⟨⟨⟨fun i j j' hj => hy.1.1 ⟨i.1, by omega⟩ j j' hj,
                  fun i i' j j' hi hj => hy.1.2 ⟨i.1, by omega⟩ ⟨i'.1, by omega⟩ j j' hi hj⟩,
                 fun i j hi hj => hy.2 ⟨i.1, by omega⟩ j hi hj⟩,
                ⟨fun j j' hj => hy.1.1 ⟨n, Nat.lt_succ_self n⟩ j j' hj,
                 fun j j' hj => hy.1.2 ⟨n - 1, by omega⟩ ⟨n, Nat.lt_succ_self n⟩ j j' (by dsimp; omega) hj⟩⟩
      · funext i j; dsimp only [snoc, init]; split_ifs with hi
        · rfl
        · have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; omega); rw [this]
  rw [hbij, Finset.card_sigma]
  have hconst : ∀ x ∈ S n, ((univ : Finset (Fin 3 → Fin 6)).filter (validNext6 (x ⟨n - 1, by omega⟩))).card = 105 := by
    intro x hx; simp only [S, mem_filter, mem_univ, true_and] at hx
    exact card_validNext6 _ (fun j j' hj => hx.1.1 ⟨n - 1, by omega⟩ j j' hj)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]

lemma U14_succ (n : ℕ) (hn : 1 ≤ n) : U14 (n + 1) = 21 * U14 n := by
  let S (m : ℕ) := (univ : Finset (Fin m → Fin 3 → Fin 6)).filter
    (fun x => Cond x ∧ TopZero x ∧ ∀ i j, ¬ inP23 (x i j))
  change (S (n + 1)).card = 21 * (S n).card
  let init : (Fin (n + 1) → Fin 3 → Fin 6) → (Fin n → Fin 3 → Fin 6) := fun x i => x ⟨i.1, by omega⟩
  let snoc : (Fin n → Fin 3 → Fin 6) → (Fin 3 → Fin 6) → (Fin (n + 1) → Fin 3 → Fin 6) :=
    fun x r i => if h : (i : ℕ) < n then x ⟨i.1, h⟩ else r
  have hbij : (S (n + 1)).card =
      ((S n).sigma (fun x => (univ : Finset (Fin 3 → Fin 6)).filter
        (fun r => validNext6 (x ⟨n - 1, by omega⟩) r ∧ ∀ j, ¬ inP23 (r j)))).card := by
    symm
    refine Finset.card_bij (fun p _ => snoc p.1 p.2) ?_ ?_ ?_
    · intro ⟨x, r⟩ hp
      simp only [mem_sigma, S, mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro i j j' hj; dsimp only [snoc]; split_ifs with hi
        · exact hp.1.1.1 ⟨i.1, hi⟩ j j' hj
        · exact hp.2.1.1 j j' hj
      · intro i i' j j' hi hj; dsimp only [snoc]
        by_cases hi' : (i' : ℕ) < n
        · have hi1 : (i : ℕ) < n := by omega
          simp only [hi1, hi', ↓reduceDIte]; exact hp.1.1.2 ⟨i.1, hi1⟩ ⟨i'.1, hi'⟩ j j' hi hj
        · have hi1 : (i : ℕ) < n := by omega
          have hieq : (⟨i.1, hi1⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          simp only [hi1, hi', ↓reduceDIte, hieq]
          exact hp.2.1.2 j j' hj
      · intro i j hi hj; dsimp only [snoc]
        have h0 : (i : ℕ) < n := by omega
        simp only [h0, ↓reduceDIte]; exact hp.1.2.1 ⟨i.1, h0⟩ j hi hj
      · intro i j; dsimp only [snoc]; split_ifs with hi
        · exact hp.1.2.2 ⟨i.1, hi⟩ j
        · exact hp.2.2 j
    · intro ⟨x1, r1⟩ _ ⟨x2, r2⟩ _ heq
      have hx : x1 = x2 := by funext i j; simpa [snoc, i.2] using congrFun (congrFun heq ⟨i.1, by omega⟩) j
      have hr : r1 = r2 := by funext j; simpa [snoc] using congrFun (congrFun heq ⟨n, Nat.lt_succ_self n⟩) j
      subst hx; subst hr; rfl
    · intro y hy
      simp only [S, mem_filter, mem_univ, true_and] at hy
      refine ⟨⟨init y, y ⟨n, Nat.lt_succ_self n⟩⟩, ?_, ?_⟩
      · simp only [mem_sigma, S, mem_filter, mem_univ, true_and]
        refine ⟨⟨⟨fun i j j' hj => hy.1.1 ⟨i.1, by omega⟩ j j' hj,
                  fun i i' j j' hi hj => hy.1.2 ⟨i.1, by omega⟩ ⟨i'.1, by omega⟩ j j' hi hj⟩,
                 fun i j hi hj => hy.2.1 ⟨i.1, by omega⟩ j hi hj,
                 fun i j => hy.2.2 ⟨i.1, by omega⟩ j⟩,
                ⟨⟨fun j j' hj => hy.1.1 ⟨n, Nat.lt_succ_self n⟩ j j' hj,
                  fun j j' hj => hy.1.2 ⟨n - 1, by omega⟩ ⟨n, Nat.lt_succ_self n⟩ j j' (by dsimp; omega) hj⟩,
                 fun j => hy.2.2 ⟨n, Nat.lt_succ_self n⟩ j⟩⟩
      · funext i j; dsimp only [snoc, init]; split_ifs with hi
        · rfl
        · have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; omega); rw [this]
  rw [hbij, Finset.card_sigma]
  have hconst : ∀ x ∈ S n, ((univ : Finset (Fin 3 → Fin 6)).filter
      (fun r => validNext6 (x ⟨n - 1, by omega⟩) r ∧ ∀ j, ¬ inP23 (r j))).card = 21 := by
    intro x hx; simp only [S, mem_filter, mem_univ, true_and] at hx
    exact card_validNext14 _ (fun j j' hj => hx.1.1 ⟨n - 1, by omega⟩ j j' hj)
      (fun j => hx.2.2 ⟨n - 1, by omega⟩ j)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]

lemma U6_closed (n : ℕ) (hn : 1 ≤ n) : U6 n = 25 * 105 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn; rw [add_comm 1 k]
  induction k with
  | zero => simp [U6_one]
  | succ k ih => rw [show k + 1 + 1 = (k + 1) + 1 from rfl, U6_succ (k + 1) (by omega), ih]; simp [pow_succ]; ring

lemma U14_closed (n : ℕ) (hn : 1 ≤ n) : U14 n = 9 * 21 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn; rw [add_comm 1 k]
  induction k with
  | zero => simp [U14_one]
  | succ k ih => rw [show k + 1 + 1 = (k + 1) + 1 from rfl, U14_succ (k + 1) (by omega), ih]; simp [pow_succ]; ring

lemma eight_mul_a (n : ℕ) (hn : 1 ≤ n) :
    8 * a n = 5 + 18 * 21 ^ (n - 1) + 25 * 105 ^ (n - 1) := by
  let S := (univ : Finset (Fin n → Fin 3 → Fin 6)).filter (fun x => Cond x ∧ TopZero x)
  let z : Fin n → Fin 3 → Fin 6 := fun _ _ => 0
  let S14 := S.filter (fun x => (∃ i j, inP14 (x i j)) ∧ ∀ i j, ¬ inP23 (x i j))
  let S23 := S.filter (fun x => (∃ i j, inP23 (x i j)) ∧ ∀ i j, ¬ inP14 (x i j))
  let Sboth := S.filter (fun x => (∃ i j, inP14 (x i j)) ∧ (∃ i j, inP23 (x i j)))
  have hz14 : z ∉ S14 := by
    intro h; rcases (Finset.mem_filter.mp h).2.1 with ⟨_, _, h1 | h4⟩
    · exact absurd h1 (by decide)
    · exact absurd h4 (by decide)
  have hz23 : z ∉ S23 := by
    intro h; rcases (Finset.mem_filter.mp h).2.1 with ⟨_, _, h2 | h3⟩
    · exact absurd h2 (by decide)
    · exact absurd h3 (by decide)
  have hzboth : z ∉ Sboth := by
    intro h; rcases (Finset.mem_filter.mp h).2.1 with ⟨_, _, h1 | h4⟩
    · exact absurd h1 (by decide)
    · exact absurd h4 (by decide)
  have h14_card : S14.card + 1 = U14 n := by
    have hset : (univ : Finset (Fin n → Fin 3 → Fin 6)).filter
        (fun x => Cond x ∧ TopZero x ∧ ∀ i j, ¬ inP23 (x i j)) = insert z S14 := by
      ext x; simp only [mem_insert, S14, S, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hc, htz, hno23⟩
        by_cases h14 : ∃ i j, inP14 (x i j)
        · exact Or.inr ⟨⟨hc, htz⟩, h14, hno23⟩
        · left; exact eq_zero_of_no_mid x hc htz
            (fun i j => fin6_zero_or_five _ (fun h => h14 ⟨i, j, h⟩) (hno23 i j))
      · rintro (rfl | ⟨⟨hc, htz⟩, _, hno23⟩)
        · exact ⟨cond_zero n, fun _ _ _ _ => rfl, fun _ _ => by decide⟩
        · exact ⟨hc, htz, hno23⟩
    unfold U14; rw [hset, card_insert_of_notMem hz14]
  have h23_eq : S23.card = S14.card := by
    refine Finset.card_bij (fun x _ => symArr (false, false, true) x) ?_ ?_ ?_
    · intro x hx
      simp only [S23, S14, S, mem_filter, mem_univ, true_and] at hx ⊢
      refine ⟨⟨(cond_symArr _ x).mpr hx.1.1, (topZero_symArr _ x).mpr hx.1.2⟩, ?_, ?_⟩
      · rcases hx.2.1 with ⟨i, j, h⟩
        exact ⟨i, j, (applySym_inP14_iff _ _).mpr (by simp [h])⟩
      · intro i j; simp only [symArr, applySym_inP23_iff]; simp [hx.2.2 i j]
    · intro x1 _ x2 _ h
      have h1 := congrArg (symArr (invSym (false, false, true))) h
      rwa [symArr_inv, symArr_inv] at h1
    · intro y hy
      simp only [S14, S23, S, mem_filter, mem_univ, true_and] at hy ⊢
      refine ⟨symArr (false, false, true) y, ?_, symArr_inv (false, false, true) y⟩
      refine ⟨⟨(cond_symArr _ y).mpr hy.1.1, (topZero_symArr _ y).mpr hy.1.2⟩, ?_, ?_⟩
      · rcases hy.2.1 with ⟨i, j, h⟩
        exact ⟨i, j, (applySym_inP23_iff _ _).mpr (by simp [h])⟩
      · intro i j; simp only [symArr, applySym_inP14_iff]; simp [hy.2.2 i j]
  have hU_part : U6 n = 1 + S14.card + S23.card + Sboth.card := by
    have hdisj1 : Disjoint S14 S23 := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [S14, S23, mem_filter] at h1 h2
      rcases h1.2.1 with ⟨i, j, h⟩; exact h2.2.2 i j h
    have hdisj2 : Disjoint (S14 ∪ S23) Sboth := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [mem_union, S14, S23, Sboth, mem_filter] at h1 h2
      rcases h1 with h1 | h1
      · rcases h2.2.2 with ⟨i, j, h⟩; exact h1.2.2 i j h
      · rcases h2.2.1 with ⟨i, j, h⟩; exact h1.2.2 i j h
    have hunion : S = insert z ((S14 ∪ S23) ∪ Sboth) := by
      ext x; simp only [mem_insert, mem_union, S14, S23, Sboth, S, mem_filter, mem_univ, true_and]
      constructor
      · intro hx
        by_cases h14 : ∃ i j, inP14 (x i j)
        · by_cases h23 : ∃ i j, inP23 (x i j)
          · exact Or.inr (Or.inr ⟨hx, h14, h23⟩)
          · exact Or.inr (Or.inl (Or.inl ⟨hx, h14, fun i j h => h23 ⟨i, j, h⟩⟩))
        · by_cases h23 : ∃ i j, inP23 (x i j)
          · exact Or.inr (Or.inl (Or.inr ⟨hx, h23, fun i j h => h14 ⟨i, j, h⟩⟩))
          · left; exact eq_zero_of_no_mid x hx.1 hx.2
              (fun i j => fin6_zero_or_five _ (fun h => h14 ⟨i, j, h⟩) (fun h => h23 ⟨i, j, h⟩))
      · rintro (rfl | ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩))
        · exact ⟨cond_zero n, fun _ _ _ _ => rfl⟩
        · exact hx
        · exact hx
        · exact hx
    change S.card = 1 + S14.card + S23.card + Sboth.card
    rw [hunion, card_insert_of_notMem, card_union_of_disjoint hdisj2, card_union_of_disjoint hdisj1]
    · omega
    · simp only [mem_union, not_or]; exact ⟨⟨hz14, hz23⟩, hzboth⟩
  let A14 := S14.filter Norm
  let Aboth := Sboth.filter Norm
  have ha_part : a n = 1 + A14.card + Aboth.card := by
    have hdisj : Disjoint A14 Aboth := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [A14, Aboth, S14, Sboth, mem_filter] at h1 h2
      rcases h2.1.2.2 with ⟨i, j, h⟩; exact h1.1.2.2 i j h
    have hset : (univ : Finset (Fin n → Fin 3 → Fin 6)).filter (fun x => Cond x ∧ Norm x) =
        insert z (A14 ∪ Aboth) := by
      ext x; simp only [mem_insert, mem_union, A14, Aboth, S14, Sboth, S, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hc, hnx⟩
        by_cases h14 : ∃ i j, inP14 (x i j)
        · by_cases h23 : ∃ i j, inP23 (x i j)
          · exact Or.inr (Or.inr ⟨⟨⟨hc, hnx.1⟩, h14, h23⟩, hnx⟩)
          · exact Or.inr (Or.inl ⟨⟨⟨hc, hnx.1⟩, h14, fun i j h => h23 ⟨i, j, h⟩⟩, hnx⟩)
        · by_cases h23 : ∃ i j, inP23 (x i j)
          · exfalso; rcases h23 with ⟨i, j, h⟩
            rcases hnx.2.1 i j (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) with ⟨i', j', _, hx1⟩
            exact h14 ⟨i', j', Or.inl hx1⟩
          · left; exact eq_zero_of_no_mid x hc hnx.1
              (fun i j => fin6_zero_or_five _ (fun h => h14 ⟨i, j, h⟩) (fun h => h23 ⟨i, j, h⟩))
      · rintro (rfl | ⟨⟨⟨hc, _⟩, _⟩, hnx⟩ | ⟨⟨⟨hc, _⟩, _⟩, hnx⟩)
        · exact ⟨cond_zero n, norm_zero n⟩
        · exact ⟨hc, hnx⟩
        · exact ⟨hc, hnx⟩
    unfold a; rw [hset, card_insert_of_notMem, card_union_of_disjoint hdisj]
    · omega
    · simp only [mem_union, A14, Aboth, mem_filter, not_or]
      exact ⟨fun h => hz14 h.1, fun h => hzboth h.1⟩
  have h14_half : 2 * A14.card = S14.card := by
    let B14 := S14.filter (fun x => ¬ Norm x)
    have hbij : A14.card = B14.card := by
      refine Finset.card_bij (fun x _ => symArr (true, false, false) x) ?_ ?_ ?_
      · intro x hx
        simp only [A14, B14, S14, S, mem_filter, mem_univ, true_and] at hx ⊢
        refine ⟨⟨⟨(cond_symArr _ x).mpr hx.1.1.1, (topZero_symArr _ x).mpr hx.1.1.2⟩, ?_, ?_⟩,
                (norm_xor_swap14 x hx.1.1.2 hx.1.2.1 hx.1.2.2).mp hx.2⟩
        · rcases hx.1.2.1 with ⟨i, j, h⟩
          exact ⟨i, j, (applySym_inP14_iff _ _).mpr (by simp [h])⟩
        · intro i j; simp only [symArr, applySym_inP23_iff]; simp [hx.1.2.2 i j]
      · intro x1 _ x2 _ h
        have h1 := congrArg (symArr (invSym (true, false, false))) h
        rwa [symArr_inv, symArr_inv] at h1
      · intro y hy
        simp only [A14, B14, S14, S, mem_filter, mem_univ, true_and] at hy ⊢
        refine ⟨symArr (true, false, false) y, ?_, symArr_inv (true, false, false) y⟩
        have h14' : ∃ i j, inP14 (symArr (true, false, false) y i j) := by
          rcases hy.1.2.1 with ⟨i, j, h⟩
          exact ⟨i, j, (applySym_inP14_iff _ _).mpr (by simp [h])⟩
        have hno23' : ∀ i j, ¬ inP23 (symArr (true, false, false) y i j) := by
          intro i j; simp only [symArr, applySym_inP23_iff]; simp [hy.1.2.2 i j]
        have htz' : TopZero (symArr (true, false, false) y) := (topZero_symArr _ y).mpr hy.1.1.2
        refine ⟨⟨⟨(cond_symArr _ y).mpr hy.1.1.1, htz'⟩, h14', hno23'⟩, ?_⟩
        have hxor := norm_xor_swap14 (symArr (true, false, false) y) htz' h14' hno23'
        have hinvol : symArr (true, false, false) (symArr (true, false, false) y) = y :=
          symArr_inv (true, false, false) y
        rw [hinvol] at hxor
        exact hxor.mpr hy.2
    have hsum : S14.card = A14.card + B14.card := by
      have hdisj : Disjoint A14 B14 := by
        rw [Finset.disjoint_left]; intro x h1 h2; simp only [A14, B14, mem_filter] at h1 h2; exact h2.2 h1.2
      rw [← card_union_of_disjoint hdisj]; congr 1; ext x
      simp only [mem_union, A14, B14, mem_filter]; tauto
    omega
  have hboth_sym : ∀ (g : Sym) (x : Fin n → Fin 3 → Fin 6), x ∈ Sboth → symArr g x ∈ Sboth := by
    intro g x hx
    simp only [Sboth, S, mem_filter, mem_univ, true_and] at hx ⊢
    refine ⟨⟨(cond_symArr g x).mpr hx.1.1, (topZero_symArr g x).mpr hx.1.2⟩, ?_, ?_⟩
    · by_cases hs : g.2.2
      · rcases hx.2.2 with ⟨i, j, h⟩; exact ⟨i, j, (applySym_inP14_iff g _).mpr (by simp [hs, h])⟩
      · rcases hx.2.1 with ⟨i, j, h⟩; exact ⟨i, j, (applySym_inP14_iff g _).mpr (by simp [hs, h])⟩
    · by_cases hs : g.2.2
      · rcases hx.2.1 with ⟨i, j, h⟩; exact ⟨i, j, (applySym_inP23_iff g _).mpr (by simp [hs, h])⟩
      · rcases hx.2.2 with ⟨i, j, h⟩; exact ⟨i, j, (applySym_inP23_iff g _).mpr (by simp [hs, h])⟩
  have hboth_eight : 8 * Aboth.card = Sboth.card := by
    have hcard_sym : (univ : Finset Sym).card = 8 := by decide
    rw [← hcard_sym, ← Finset.card_product]
    refine Finset.card_bij (fun p _ => symArr (invSym p.1) p.2) ?_ ?_ ?_
    · intro ⟨g, y⟩ hp
      simp only [mem_product, mem_univ, true_and, Aboth, mem_filter] at hp
      exact hboth_sym (invSym g) y hp.1
    · intro ⟨g1, y1⟩ hp1 ⟨g2, y2⟩ hp2 heq
      simp only [mem_product, mem_univ, true_and, Aboth, mem_filter] at hp1 hp2
      dsimp only at heq
      let x := symArr (invSym g1) y1
      have h1 : symArr g1 x = y1 := symArr_inv' g1 y1
      have h2 : symArr g2 x = y2 := by dsimp only [x]; rw [heq]; exact symArr_inv' g2 y2
      have hx_mem : x ∈ Sboth := hboth_sym (invSym g1) y1 hp1.1
      simp only [Sboth, S, mem_filter, mem_univ, true_and] at hx_mem
      rcases sym_exists_unique_both x hx_mem.1.2 hx_mem.2.1 hx_mem.2.2 with ⟨g0, _, huniq⟩
      have hg1 : g1 = g0 := huniq g1 (by dsimp only; rw [h1]; exact hp1.2)
      have hg2 : g2 = g0 := huniq g2 (by dsimp only; rw [h2]; exact hp2.2)
      subst hg1; subst hg2
      have hy : y1 = y2 := by rw [← h1, ← h2]
      subst hy; rfl
    · intro x hx
      have hx' := hx
      simp only [Sboth, S, mem_filter, mem_univ, true_and] at hx
      rcases sym_exists_unique_both x hx.1.2 hx.2.1 hx.2.2 with ⟨g, hng, _⟩
      refine ⟨(g, symArr g x), ?_, symArr_inv g x⟩
      simp only [mem_product, mem_univ, true_and, Aboth, mem_filter]
      exact ⟨hboth_sym g x hx', hng⟩
  have hU6 := U6_closed n hn
  have hU14 := U14_closed n hn
  omega

lemma a_closed_rat (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (105 + 2 * 3 ^ (2 + n) * 7 ^ n + 5 ^ (1 + n) * 21 ^ n) / 168 := by
  have h8 : (8 * a n : ℚ) = 5 + 18 * (21 : ℚ) ^ (n - 1) + 25 * (105 : ℚ) ^ (n - 1) := by
    exact_mod_cast eight_mul_a n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 k] at h8 ⊢
  simp only [Nat.add_sub_cancel] at h8
  have h21 : (21 : ℚ) ^ k = (3 : ℚ) ^ k * (7 : ℚ) ^ k := by rw [← mul_pow]; norm_num
  have h105 : (105 : ℚ) ^ k = (5 : ℚ) ^ k * (21 : ℚ) ^ k := by rw [← mul_pow]; norm_num
  have h3a : (3 : ℚ) ^ (2 + (k + 1)) = 27 * (3 : ℚ) ^ k := by
    rw [show 2 + (k + 1) = k + 3 by omega, pow_add]; ring
  have h7a : (7 : ℚ) ^ (k + 1) = 7 * (7 : ℚ) ^ k := by rw [pow_succ]; ring
  have h5a : (5 : ℚ) ^ (1 + (k + 1)) = 25 * (5 : ℚ) ^ k := by
    rw [show 1 + (k + 1) = k + 2 by omega, pow_add]; ring
  have h21a : (21 : ℚ) ^ (k + 1) = 21 * (21 : ℚ) ^ k := by rw [pow_succ]; ring
  rw [h3a, h7a, h5a, h21a, h21]
  rw [h105, h21] at h8
  linarith

lemma gf_main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 21 * X) * (1 - 105 * X)) = 2 * X * (3 - 193 * X + 840 * X ^ 2) := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hlhs : F * ((1 - X) * (1 - 21 * X) * (1 - 105 * X)) =
      F - PowerSeries.C (127 : ℚ) * (X ^ 1 * F) + PowerSeries.C (2331 : ℚ) * (X ^ 2 * F) -
      PowerSeries.C (2205 : ℚ) * (X ^ 3 * F) := by
    simp only [map_ofNat]; ring
  have hrhs : (2 * X * (3 - 193 * X + 840 * X ^ 2) : PowerSeries ℚ) =
      PowerSeries.C (6 : ℚ) * (X ^ 1 : PowerSeries ℚ) -
      PowerSeries.C (386 : ℚ) * (X ^ 2 : PowerSeries ℚ) +
      PowerSeries.C (1680 : ℚ) * (X ^ 3 : PowerSeries ℚ) := by
    simp only [map_ofNat]; ring
  change F * ((1 - X) * (1 - 21 * X) * (1 - 105 * X)) = 2 * X * (3 - 193 * X + 840 * X ^ 2)
  rw [hlhs, hrhs]
  have hf : ∀ n : ℕ, (if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      if n = 0 then 0 else (105 + 2 * 3 ^ (2 + n) * 7 ^ n + 5 ^ (1 + n) * 21 ^ n) / 168 := by
    intro n; split_ifs with h
    · rfl
    · exact a_closed_rat n (by omega)
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
             PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk, hf]
  rcases k with _ | _ | _ | _ | m
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have e0 : m + 1 + 1 + 1 + 1 = m + 4 := by omega
    have h1 : m + 4 - 1 = m + 3 := by omega
    have h2 : m + 4 - 2 = m + 2 := by omega
    have h3 : m + 4 - 3 = m + 1 := by omega
    rw [e0, h1, h2, h3]
    have c0 : ¬ (m + 4 = 0) := by omega
    have c1 : ¬ (m + 3 = 0) := by omega
    have c2 : ¬ (m + 2 = 0) := by omega
    have c3 : ¬ (m + 1 = 0) := by omega
    have l1 : 1 ≤ m + 4 := by omega
    have l2 : 2 ≤ m + 4 := by omega
    have l3 : 3 ≤ m + 4 := by omega
    have n1 : ¬ (m + 4 = 1) := by omega
    have n2 : ¬ (m + 4 = 2) := by omega
    have n3 : ¬ (m + 4 = 3) := by omega
    simp only [c0, c1, c2, c3, l1, l2, l3, n1, n2, n3, ite_true, ite_false]
    have p3a : (3 : ℚ) ^ (2 + (m + 4)) = 27 * (3 : ℚ) ^ (2 + (m + 1)) := by
      rw [show 2 + (m + 4) = (2 + (m + 1)) + 3 by omega, pow_add]; ring
    have p3b : (3 : ℚ) ^ (2 + (m + 3)) = 9 * (3 : ℚ) ^ (2 + (m + 1)) := by
      rw [show 2 + (m + 3) = (2 + (m + 1)) + 2 by omega, pow_add]; ring
    have p3c : (3 : ℚ) ^ (2 + (m + 2)) = 3 * (3 : ℚ) ^ (2 + (m + 1)) := by
      rw [show 2 + (m + 2) = (2 + (m + 1)) + 1 by omega, pow_succ]; ring
    have p7a : (7 : ℚ) ^ (m + 4) = 343 * (7 : ℚ) ^ (m + 1) := by
      rw [show m + 4 = (m + 1) + 3 by omega, pow_add]; ring
    have p7b : (7 : ℚ) ^ (m + 3) = 49 * (7 : ℚ) ^ (m + 1) := by
      rw [show m + 3 = (m + 1) + 2 by omega, pow_add]; ring
    have p7c : (7 : ℚ) ^ (m + 2) = 7 * (7 : ℚ) ^ (m + 1) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring
    have p5a : (5 : ℚ) ^ (1 + (m + 4)) = 125 * (5 : ℚ) ^ (1 + (m + 1)) := by
      rw [show 1 + (m + 4) = (1 + (m + 1)) + 3 by omega, pow_add]; ring
    have p5b : (5 : ℚ) ^ (1 + (m + 3)) = 25 * (5 : ℚ) ^ (1 + (m + 1)) := by
      rw [show 1 + (m + 3) = (1 + (m + 1)) + 2 by omega, pow_add]; ring
    have p5c : (5 : ℚ) ^ (1 + (m + 2)) = 5 * (5 : ℚ) ^ (1 + (m + 1)) := by
      rw [show 1 + (m + 2) = (1 + (m + 1)) + 1 by omega, pow_succ]; ring
    have p21a : (21 : ℚ) ^ (m + 4) = 9261 * (21 : ℚ) ^ (m + 1) := by
      rw [show m + 4 = (m + 1) + 3 by omega, pow_add]; ring
    have p21b : (21 : ℚ) ^ (m + 3) = 441 * (21 : ℚ) ^ (m + 1) := by
      rw [show m + 3 = (m + 1) + 2 by omega, pow_add]; ring
    have p21c : (21 : ℚ) ^ (m + 2) = 21 * (21 : ℚ) ^ (m + 1) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]; ring
    rw [p3a, p3b, p3c, p7a, p7b, p7c, p5a, p5b, p5c, p21a, p21b, p21c]
    ring

end A233212Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a233212.main :=
  ⟨A233212Proof.gf_main, A233212Proof.a_closed_rat⟩
