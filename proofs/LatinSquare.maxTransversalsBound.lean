import FormalConjectures.Paper.LatinSquare
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Upper and lower bounds for the largest number of transversals

We use McKay, McLeod and Wanless, *The number of transversals in a Latin
square*, Des. Codes Cryptogr. 40 (2006), 269–284, as the source of the
exact bounds. For the lower bound, prolong a product square and
independently fill four diagonal blocks. The small even tables of orders
six and eight are from Wanless's companion data. For the upper bound,
average the logarithms of branching counts over row orders. The two
blocking rows for an alternative column give the finite expected count.
This is a finite form of the row-reveal argument used by Glebov and Luria.
-/

namespace LatinBound

structure SquareOn (A : Type) where
  entry : A → A → A
  row : ∀ i, Function.Injective (entry i)
  col : ∀ j, Function.Injective (fun i => entry i j)

abbrev IsTrans {A : Type} (L : SquareOn A) (σ : A → A) : Prop :=
  Function.Injective σ ∧ Function.Injective (fun i => L.entry i (σ i))

abbrev TransOn {A : Type} (L : SquareOn A) :=
  {σ : A → A // IsTrans L σ}

def SquareOn.transport {A B : Type} (L : SquareOn A) (e : A ≃ B) : SquareOn B where
  entry i j := e (L.entry (e.symm i) (e.symm j))
  row _ := e.injective.comp ((L.row _).comp e.symm.injective)
  col _ := e.injective.comp ((L.col _).comp e.symm.injective)

def SquareOn.onFin {A : Type} {n : ℕ} (L : SquareOn A) (e : A ≃ Fin n) : LatinSquare n :=
  let K := L.transport e
  ⟨K.entry, K.row, K.col⟩

def SquareOn.toFinTrans {A : Type} {n : ℕ} (L : SquareOn A) (e : A ≃ Fin n)
    (f : TransOn L) : {σ : Fin n → Fin n // IsTransversal (L.onFin e) σ} where
  val i := e (f.val (e.symm i))
  property := by
    refine ⟨e.injective.comp (f.property.1.comp e.symm.injective), ?_⟩
    intro i j hij
    change e (L.entry (e.symm i) (e.symm (e (f.val (e.symm i))))) =
      e (L.entry (e.symm j) (e.symm (e (f.val (e.symm j))))) at hij
    simp only [Equiv.symm_apply_apply] at hij
    exact e.symm.injective (f.property.2 (e.injective hij))

lemma SquareOn.toFinTrans_injective {A : Type} {n : ℕ} (L : SquareOn A) (e : A ≃ Fin n) :
    Function.Injective (L.toFinTrans e) := by
  intro f g h
  apply Subtype.ext
  funext i
  have hh := congrArg (fun z : {σ : Fin n → Fin n // IsTransversal (L.onFin e) σ} =>
    z.val (e i)) h
  simpa [SquareOn.toFinTrans] using e.injective (by simpa [SquareOn.toFinTrans] using hh :
    e (f.val i) = e (g.val i))

def SquareOn.fromFin {n : ℕ} (L : LatinSquare n) : SquareOn (Fin n) :=
  ⟨L.mat, L.row_injective, L.col_injective⟩

section Replace
variable {I : Type} [DecidableEq I] {A : I → Type} [∀ i, Fintype (A i)]

def blockEntry (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (a b : Sigma A) : Sigma A :=
  if h : b.1 = a.1 then ⟨a.1, (L a.1).entry a.2 (h ▸ b.2)⟩ else K.entry a b

lemma blockEntry_same (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (i : I) (a b : A i) :
    blockEntry K L ⟨i, a⟩ ⟨i, b⟩ = ⟨i, (L i).entry a b⟩ := by
  simp [blockEntry]

lemma sigma_cast_back {i : I} (z : Sigma A) (h : z.1 = i) :
    (⟨i, Eq.mp (congrArg A h) z.2⟩ : Sigma A) = z := by
  rcases z with ⟨j,a⟩
  change j = i at h
  subst j
  rfl

lemma eq_of_block_row {K : SquareOn (Sigma A)}
    (hK : ∀ i (a b : A i), (K.entry ⟨i, a⟩ ⟨i, b⟩).1 = i)
    (a b : Sigma A) (h : (K.entry a b).1 = a.1) : b.1 = a.1 := by
  rcases a with ⟨i, ai⟩
  let g : A i → A i := fun x => Eq.mp (congrArg A (hK i ai x)) (K.entry ⟨i, ai⟩ ⟨i, x⟩).2
  have heq x : (⟨i, g x⟩ : Sigma A) = K.entry ⟨i, ai⟩ ⟨i, x⟩ :=
    sigma_cast_back _ (hK i ai x)
  have hg : Function.Injective g := by
    intro x y hxy
    have hh := K.row ⟨i, ai⟩ ((heq x).symm.trans ((congrArg (Sigma.mk i) hxy).trans (heq y)))
    simpa using hh
  let b' := K.entry ⟨i, ai⟩ b
  let y : A i := Eq.mp (congrArg A h) b'.2
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hg) y
  have hy : (⟨i, y⟩ : Sigma A) = b' := sigma_cast_back _ h
  have hz : (⟨i, x⟩ : Sigma A) = b := K.row ⟨i, ai⟩
    ((heq x).symm.trans ((congrArg (Sigma.mk i) hx).trans hy))
  exact (congrArg Sigma.fst hz).symm

def SquareOn.swap {A : Type} (K : SquareOn A) : SquareOn A :=
  ⟨fun i j => K.entry j i, K.col, K.row⟩

lemma eq_of_block_col {K : SquareOn (Sigma A)}
    (hK : ∀ i (a b : A i), (K.entry ⟨i, a⟩ ⟨i, b⟩).1 = i)
    (a b : Sigma A) (h : (K.entry a b).1 = b.1) : a.1 = b.1 :=
  eq_of_block_row (K := K.swap) (fun i a b => hK i b a) b a h

lemma blockEntry_ne (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (a b : Sigma A) (h : b.1 ≠ a.1) : blockEntry K L a b = K.entry a b := by
  simp [blockEntry, h]

lemma blockEntry_swap (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (a b : Sigma A) : blockEntry K L a b = blockEntry K.swap (fun i => (L i).swap) b a := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  by_cases h : j = i
  · subst j
    simp [blockEntry_same, SquareOn.swap]
  · rw [blockEntry_ne _ _ _ _ h, blockEntry_ne _ _ _ _ (Ne.symm h)]
    rfl

lemma blockEntry_row (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (hK : ∀ i (a b : A i), (K.entry ⟨i, a⟩ ⟨i, b⟩).1 = i) (a : Sigma A) :
    Function.Injective (blockEntry K L a) := by
  rintro ⟨j, b⟩ ⟨k, c⟩ he
  rcases a with ⟨i, a⟩
  by_cases hj : j = i <;> by_cases hk : k = i
  · subst j
    subst k
    rw [blockEntry_same, blockEntry_same] at he
    exact congrArg (Sigma.mk i) ((L i).row a (by simpa using he))
  · subst j
    rw [blockEntry_same, blockEntry_ne _ _ _ _ hk] at he
    exact False.elim (hk (eq_of_block_row hK _ _ (by rw [← he])))
  · subst k
    rw [blockEntry_ne _ _ _ _ hj, blockEntry_same] at he
    exact False.elim (hj (eq_of_block_row hK _ _ (by rw [he])))
  · rw [blockEntry_ne _ _ _ _ hj, blockEntry_ne _ _ _ _ hk] at he
    exact K.row _ he

def replaceBlocks (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (hK : ∀ i (a b : A i), (K.entry ⟨i, a⟩ ⟨i, b⟩).1 = i) : SquareOn (Sigma A) where
  entry := blockEntry K L
  row := blockEntry_row K L hK
  col i := by
    intro a b hab
    change blockEntry K L a i = blockEntry K L b i at hab
    rw [blockEntry_swap _ _ a i, blockEntry_swap _ _ b i] at hab
    exact blockEntry_row K.swap (fun j => (L j).swap) (fun j u v => hK j v u) i hab

def blockTrans (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (hK : ∀ i (a b : A i), (K.entry ⟨i, a⟩ ⟨i, b⟩).1 = i)
    (f : ∀ i, TransOn (L i)) : TransOn (replaceBlocks K L hK) where
  val x := ⟨x.1, (f x.1).val x.2⟩
  property := by
    constructor
    · rintro ⟨i, a⟩ ⟨j,b⟩ h
      have he := congrArg Sigma.fst h
      change i = j at he
      subst j
      exact congrArg (Sigma.mk i) ((f i).property.1 (by simpa using h))
    · rintro ⟨i, a⟩ ⟨j,b⟩ h
      change blockEntry K L ⟨i, a⟩ ⟨i, (f i).val a⟩ =
        blockEntry K L ⟨j, b⟩ ⟨j, (f j).val b⟩ at h
      rw [blockEntry_same, blockEntry_same] at h
      have he := congrArg Sigma.fst h
      change i = j at he
      subst j
      exact congrArg (Sigma.mk i) ((f i).property.2 (by simpa using h))

lemma blockTrans_injective (K : SquareOn (Sigma A)) (L : ∀ i, SquareOn (A i))
    (hK : ∀ i (a b : A i), (K.entry ⟨i, a⟩ ⟨i, b⟩).1 = i) :
    Function.Injective (blockTrans K L hK) := by
  intro f g h
  funext i
  apply Subtype.ext
  funext a
  have hh := congrArg (fun z : TransOn (replaceBlocks K L hK) => z.val ⟨i, a⟩) h
  simpa [blockTrans] using hh

end Replace


section Prolong

variable {A B : Type}

noncomputable def prolongSlot (E : B → Equiv.Perm A) (x y : A) : Option B :=
  open Classical in
  if h : ∃ t, E t x = y then some h.choose else none

lemma prolongSlot_some (E : B → Equiv.Perm A)
    (hE : ∀ x, Function.Injective (fun t => E t x)) (x y : A) (t : B) :
    prolongSlot E x y = some t ↔ E t x = y := by
  classical
  unfold prolongSlot
  split
  · rename_i h
    constructor
    · intro he
      have : h.choose = t := Option.some.inj he
      simpa [← this] using h.choose_spec
    · intro ht
      exact congrArg some (hE x (h.choose_spec.trans ht.symm))
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun ht => h ⟨t, ht⟩

lemma prolongSlot_swap (E : B → Equiv.Perm A)
    (hE : ∀ x, Function.Injective (fun t => E t x)) (x y : A) :
    prolongSlot E x y = prolongSlot (fun t => (E t).symm) y x := by
  have hE' (y : A) : Function.Injective (fun t => (E t).symm y) := by
    intro t s h
    change (E t).symm y = (E s).symm y at h
    apply hE ((E t).symm y)
    change (E t) ((E t).symm y) = (E s) ((E t).symm y)
    rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]
  cases h : prolongSlot E x y with
  | none =>
    cases h' : prolongSlot (fun t => (E t).symm) y x with
    | none => rfl
    | some s =>
      have hx := (prolongSlot_some _ hE' _ _ _).mp h'
      have hy : E s x = y := by rw [← hx, Equiv.apply_symm_apply]
      have hc := h.symm.trans ((prolongSlot_some E hE x y s).2 hy)
      simp at hc
  | some s =>
    symm
    apply (prolongSlot_some _ hE' _ _ _).2
    have hy := (prolongSlot_some E hE x y s).mp h
    rw [← hy, Equiv.symm_apply_apply]

noncomputable def prolongEntry (K : SquareOn A) (G : SquareOn B)
    (E : B → Equiv.Perm A) : A ⊕ B → A ⊕ B → A ⊕ B
  | .inl x, .inl y =>
    match prolongSlot E x y with
    | none => .inl (K.entry x y)
    | some t => .inr t
  | .inl x, .inr t => .inl (K.entry x (E t x))
  | .inr t, .inl y => .inl (K.entry ((E t).symm y) y)
  | .inr t, .inr s => .inr (G.entry t s)

lemma prolong_row (K : SquareOn A) (G : SquareOn B) (E : B → Equiv.Perm A)
    (hE : ∀ x, Function.Injective (fun t => E t x))
    (hT : ∀ t, IsTrans K (E t)) (r : A ⊕ B) :
    Function.Injective (prolongEntry K G E r) := by
  cases r with
  | inl x =>
    have hmixed (y : A) (t : B) :
        prolongEntry K G E (.inl x) (.inl y) ≠
          prolongEntry K G E (.inl x) (.inr t) := by
      intro e
      cases h : prolongSlot E x y with
      | none =>
        have he : K.entry x y = K.entry x (E t x) := by simpa [prolongEntry,h] using e
        have hxy : E t x = y := (K.row x he).symm
        have hc := h.symm.trans ((prolongSlot_some E hE x y t).2 hxy)
        simp at hc
      | some s => simp [prolongEntry,h] at e
    intro p q hpq
    cases p with
    | inl y =>
      cases q with
      | inl z =>
        cases hy : prolongSlot E x y <;> cases hz : prolongSlot E x z <;>
          simp [prolongEntry,hy,hz] at hpq
        · exact congrArg Sum.inl (K.row x hpq)
        · rename_i s t
          subst t
          rw [← (prolongSlot_some E hE x y s).1 hy, ← (prolongSlot_some E hE x z s).1 hz]
      | inr t => exact (hmixed y t hpq).elim
    | inr s =>
      cases q with
      | inl z => exact (hmixed z s hpq.symm).elim
      | inr t =>
        exact congrArg Sum.inr (hE x (K.row x (by simpa [prolongEntry] using hpq)))
  | inr t =>
    intro p q hpq
    cases p <;> cases q <;> simp [prolongEntry] at hpq
    · rename_i y z
      have h : (E t).symm y = (E t).symm z := by
        apply (hT t).2
        change K.entry ((E t).symm y) (E t ((E t).symm y)) =
          K.entry ((E t).symm z) (E t ((E t).symm z))
        simpa using hpq
      exact congrArg Sum.inl ((E t).symm.injective h)
    · exact congrArg Sum.inr (G.row t hpq)

lemma prolongEntry_swap (K : SquareOn A) (G : SquareOn B) (E : B → Equiv.Perm A)
    (hE : ∀ x, Function.Injective (fun t => E t x)) (x y : A ⊕ B) :
    prolongEntry K G E x y = prolongEntry K.swap G.swap (fun t => (E t).symm) y x := by
  cases x <;> cases y
  · simp only [prolongEntry]
    rw [prolongSlot_swap E hE]
    rfl
  · rfl
  · rfl
  · rfl

noncomputable def prolong (K : SquareOn A) (G : SquareOn B) (E : B → Equiv.Perm A)
    (hE : ∀ x, Function.Injective (fun t => E t x))
    (hT : ∀ t, IsTrans K (E t)) : SquareOn (A ⊕ B) where
  entry := prolongEntry K G E
  row := prolong_row K G E hE hT
  col y := by
    intro p q h
    change prolongEntry K G E p y = prolongEntry K G E q y at h
    rw [prolongEntry_swap K G E hE p y, prolongEntry_swap K G E hE q y] at h
    apply prolong_row K.swap G.swap (fun t => (E t).symm) _ _ y h
    · intro x s t hst
      change (E s).symm x = (E t).symm x at hst
      apply hE ((E s).symm x)
      change E s ((E s).symm x) = E t ((E s).symm x)
      rw [Equiv.apply_symm_apply, hst, Equiv.apply_symm_apply]
    · intro t
      refine ⟨(E t).symm.injective, ?_⟩
      intro a b hab
      apply (E t).symm.injective
      apply (hT t).2
      change K.entry ((E t).symm a) (E t ((E t).symm a)) =
        K.entry ((E t).symm b) (E t ((E t).symm b))
      simpa [SquareOn.swap] using hab

end Prolong

def SquareOn.prod {A B : Type} (K : SquareOn A) (L : SquareOn B) : SquareOn (A × B) where
  entry a b := (K.entry a.1 b.1, L.entry a.2 b.2)
  row x := fun _ _ h => Prod.ext (K.row x.1 (congrArg Prod.fst h))
    (L.row x.2 (congrArg Prod.snd h))
  col y := fun _ _ h => Prod.ext (K.col y.1 (congrArg Prod.fst h))
    (L.col y.2 (congrArg Prod.snd h))

lemma double_injective {n : ℕ} (hn : Odd n) :
    Function.Injective (fun x : Fin n => x + x) := by
  intro a b h
  apply Fin.ext
  have hm : 2 * a.val ≡ 2 * b.val [MOD n] := by
    have hh := congrArg Fin.val h
    simpa [Fin.val_add, two_mul, Nat.ModEq] using hh
  exact ((Nat.ModEq.cancel_left_of_coprime hn.coprime_two_right hm).eq_of_lt_of_lt a.isLt b.isLt)

def smallSquare4 : SquareOn (Fin 4) where
  entry := ![![0,3,1,2],![2,1,3,0],![3,0,2,1],![1,2,0,3]]
  row := by decide +kernel
  col := by decide +kernel

noncomputable def smallPerm4 : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![0,2,3,1] (by decide +kernel)

lemma smallSquare4_diag (i : Fin 4) : smallSquare4.entry i i = i := by
  fin_cases i <;> rfl

lemma smallPerm4_fixed (i : Fin 4) : smallPerm4 i = i ↔ i = 0 := by
  fin_cases i <;> decide +kernel

lemma smallPerm4_zero : smallPerm4 0 = 0 := by rfl

lemma smallPerm4_symbol :
    Function.Injective (fun i => smallSquare4.entry i (smallPerm4 i)) := by
  change Function.Injective (fun i : Fin 4 =>
    (![![0,3,1,2],![2,1,3,0],![3,0,2,1],![1,2,0,3]] : Fin 4 → Fin 4 → Fin 4) i
      ((![0,2,3,1] : Fin 4 → Fin 4) i))
  decide +kernel

abbrev fourTypes (q r : ℕ) : Option (Fin 3) → Type
  | none => Fin q ⊕ Fin r
  | some _ => Fin q

instance (q r : ℕ) (i : Option (Fin 3)) : Fintype (fourTypes q r i) := by
  cases i <;> unfold fourTypes <;> exact inferInstance

def fourBlocksEquiv (q r : ℕ) :
    (Sigma (fourTypes q r)) ≃ ((Fin 4 × Fin q) ⊕ Fin r) where
  toFun
    | ⟨none, .inl a⟩ => .inl (0,a)
    | ⟨none, .inr b⟩ => .inr b
    | ⟨some i, a⟩ => .inl (i.succ,a)
  invFun
    | .inl (i,a) => Fin.cases ⟨none, .inl a⟩ (fun j => ⟨some j, a⟩) i
    | .inr b => ⟨none, .inr b⟩
  left_inv := by
    rintro ⟨i,a⟩
    cases i with
    | none => cases a <;> rfl
    | some _ => simp
  right_inv := by
    rintro (⟨i,a⟩ | b)
    · refine Fin.cases rfl (fun j => ?_) i
      simp
    · rfl

noncomputable def extendProductPerm {q r : ℕ} (E : Fin r → Equiv.Perm (Fin q))
    (t : Fin r) : Equiv.Perm (Fin 4 × Fin q) := Equiv.prodCongr smallPerm4 (E t)

lemma extendProduct_inj {q r : ℕ} (E : Fin r → Equiv.Perm (Fin q))
    (hE : ∀ a, Function.Injective (fun t => E t a)) (x : Fin 4 × Fin q) :
    Function.Injective (fun t => extendProductPerm E t x) :=
  fun _ _ h => hE x.2 (congrArg Prod.snd h)

lemma extendProduct_trans {q r : ℕ} (K : SquareOn (Fin q))
    (E : Fin r → Equiv.Perm (Fin q)) (hE : ∀ t, IsTrans K (E t)) (t : Fin r) :
    IsTrans (smallSquare4.prod K) (extendProductPerm E t) := by
  refine ⟨(extendProductPerm E t).injective, ?_⟩
  intro a b h
  exact Prod.ext (smallPerm4_symbol (congrArg Prod.fst h)) ((hE t).2 (congrArg Prod.snd h))

noncomputable def scaffold {q r : ℕ} (K : SquareOn (Fin q))
    (E : Fin r → Equiv.Perm (Fin q)) (hE : ∀ a, Function.Injective (fun t => E t a))
    (hT : ∀ t, IsTrans K (E t)) (G : SquareOn (Fin r)) :
    SquareOn (Sigma (fourTypes q r)) :=
  (prolong (smallSquare4.prod K) G (extendProductPerm E)
    (extendProduct_inj E hE) (extendProduct_trans K E hT)).transport (fourBlocksEquiv q r).symm

lemma fourBlocks_inv_zero {q r : ℕ} (a : Fin q) :
    (fourBlocksEquiv q r).symm (.inl ((0 : Fin 4), a)) = ⟨none, .inl a⟩ := rfl

lemma fourBlocks_inv_succ {q r : ℕ} (i : Fin 3) (a : Fin q) :
    (fourBlocksEquiv q r).symm (.inl (i.succ, a)) = ⟨some i, a⟩ := by
  simp [fourBlocksEquiv]

lemma scaffold_block {q r : ℕ} (K : SquareOn (Fin q))
    (E : Fin r → Equiv.Perm (Fin q)) (hE : ∀ a, Function.Injective (fun t => E t a))
    (hT : ∀ t, IsTrans K (E t)) (G : SquareOn (Fin r)) (i : Option (Fin 3)) (a b : fourTypes q r i) :
    ((scaffold K E hE hT G).entry ⟨i,a⟩ ⟨i,b⟩).1 = i := by
  cases i with
  | none =>
    cases a <;> cases b
    · rename_i x y
      change ((fourBlocksEquiv q r).symm
        (prolongEntry (smallSquare4.prod K) G (extendProductPerm E) (.inl ((0 : Fin 4), x)) (.inl ((0 : Fin 4), y)))).1 = none
      rw [prolongEntry]
      split
      · simp [SquareOn.prod, smallSquare4_diag, fourBlocks_inv_zero]
      · rfl
    · rename_i x t
      change ((fourBlocksEquiv q r).symm
        (prolongEntry (smallSquare4.prod K) G (extendProductPerm E) (.inl ((0 : Fin 4), x)) (.inr t))).1 = none
      simp [prolongEntry, SquareOn.prod, extendProductPerm, smallPerm4_zero, smallSquare4_diag,
        fourBlocks_inv_zero]
    · rename_i t x
      change ((fourBlocksEquiv q r).symm
        (prolongEntry (smallSquare4.prod K) G (extendProductPerm E) (.inr t) (.inl ((0 : Fin 4), x)))).1 = none
      have h0 : smallPerm4.symm 0 = 0 := smallPerm4.symm_apply_eq.mpr smallPerm4_zero
      simp [prolongEntry, SquareOn.prod, extendProductPerm, h0, smallSquare4_diag, fourBlocks_inv_zero]
    · rfl
  | some j =>
    change ((fourBlocksEquiv q r).symm
      (prolongEntry (smallSquare4.prod K) G (extendProductPerm E) (.inl (j.succ, a)) (.inl (j.succ, b)))).1 = some j
    have hs : prolongSlot (extendProductPerm E) (j.succ, a) (j.succ, b) = none := by
      cases h : prolongSlot (extendProductPerm E) (j.succ, a) (j.succ, b) with
      | none => rfl
      | some t =>
        have hi := (prolongSlot_some _ (extendProduct_inj E hE) _ _ _).1 h
        have hj : smallPerm4 j.succ = j.succ := congrArg Prod.fst hi
        exact False.elim (Fin.succ_ne_zero j ((smallPerm4_fixed j.succ).mp hj))
    simp [prolongEntry, hs, SquareOn.prod, smallSquare4_diag, fourBlocks_inv_succ]


open Finset

def cyclicSquare (n : ℕ) : LatinSquare n where
  mat i j := i + j
  row_injective _ := fun _ _ h => add_left_cancel h
  col_injective _ := fun _ _ h => add_right_cancel h

def translateTrans {n : ℕ} [NeZero n] (f : Fin n → Fin n) (a b : Fin n) :
    Fin n → Fin n := fun i => f (i - a) + b

lemma translateTrans_transversal {n : ℕ} [NeZero n] {f : Fin n → Fin n}
    (hf : IsTransversal (cyclicSquare n) f) (a b : Fin n) :
    IsTransversal (cyclicSquare n) (translateTrans f a b) := by
  constructor
  · intro i j h
    change f (i - a) + b = f (j - a) + b at h
    exact sub_left_injective (hf.1 (add_right_cancel h))
  · intro i j h
    change i + (f (i - a) + b) = j + (f (j - a) + b) at h
    have aux (i : Fin n) :
        i + (f (i - a) + b) = (i - a + f (i - a)) + (a + b) := by abel
    rw [aux, aux] at h
    exact sub_left_injective (hf.2 (add_right_cancel h))

lemma translations_count {n m : ℕ} [NeZero n] (f : Fin m → Fin n → Fin n)
    (hfinj : Function.Injective f) (hf0 : ∀ s, f s 0 = 0)
    (hf : ∀ s, IsTransversal (cyclicSquare n) (f s)) :
    m * n ≤ numTransversals (cyclicSquare n) := by
  let F : Fin m × Fin n → {σ : Fin n → Fin n // IsTransversal (cyclicSquare n) σ} :=
    fun (s,b) => ⟨translateTrans (f s) 0 b, translateTrans_transversal (hf s) 0 b⟩
  have hF : Function.Injective F := by
    rintro ⟨s,b⟩ ⟨s',b'⟩ h
    have he := congrArg Subtype.val h
    change translateTrans (f s) 0 b = translateTrans (f s') 0 b' at he
    have hn : b = b' := by simpa [translateTrans, hf0] using congrFun he 0
    subst b'
    have hs : s = s' := by
      apply hfinj
      funext i
      have hi := congrFun he i
      simp only [translateTrans, sub_zero, add_left_inj] at hi
      exact hi
    subst s'
    rfl
  have h := Fintype.card_le_of_injective F hF
  simpa [numTransversals] using h

lemma two_translations_count {n m : ℕ} [NeZero n] (f : Fin m → Fin n → Fin n)
    (hfinj : Function.Injective f) (hf0 : ∀ s, f s 0 = 0)
    (hf : ∀ s, IsTransversal (cyclicSquare n) (f s))
    (hshift : ∀ s i, f s (i + 1) - f s i = 1 ↔ i = 0) :
    m * (n * n) ≤ numTransversals (cyclicSquare n) := by
  let F : Fin m × Fin n × Fin n → {σ : Fin n → Fin n // IsTransversal (cyclicSquare n) σ} :=
    fun (s,a,b) => ⟨translateTrans (f s) a b, translateTrans_transversal (hf s) a b⟩
  have hF : Function.Injective F := by
    rintro ⟨s,a,b⟩ ⟨s',a',b'⟩ h
    have he := congrArg Subtype.val h
    change translateTrans (f s) a b = translateTrans (f s') a' b' at he
    have ha' (s : Fin m) (a b i : Fin n) :
        translateTrans (f s) a b (i+1) - translateTrans (f s) a b i = 1 ↔ i = a := by
      unfold translateTrans
      rw [add_sub_add_right_eq_sub,
        show i + 1 - a = i - a + 1 by abel, hshift s (i-a), sub_eq_zero]
    have ha : a = a' := by
      refine (ha' s' a' b' a).mp ?_
      rw [← he]
      exact (ha' s a b a).mpr rfl
    subst a'
    have hb : b = b' := by simpa [translateTrans, hf0] using congrFun he a
    subst b'
    have hs : s = s' := by
      apply hfinj
      funext i
      have hi := congrFun he (i + a)
      simpa [translateTrans] using hi
    subst s'
    rfl
  have h := Fintype.card_le_of_injective F hF
  simpa [numTransversals] using h

lemma cast_count_ge {n : ℕ} (L : LatinSquare n) :
    numTransversals L ≤ LatinSquare.T n :=
  Finset.le_sup (f := fun K : LatinSquare n => numTransversals K) (Finset.mem_univ L)

def finSelectorCode {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  (List.ofFn fun i => (f i).val).foldl (fun value digit => value * n + digit) 0

lemma selector_injective_of_mono {A B : Type} {m : ℕ} (encode : (A → B) → ℕ)
    (w : Fin m → A → B) (hw : StrictMono (fun i => encode (w i))) :
    Function.Injective w :=
  fun _ _ he => hw.injective (congrArg encode he)

def seeds5 : Fin 3 → Fin 5 → Fin 5 :=
  ![![0,1,2,3,4],
  ![0,2,4,1,3],
  ![0,3,1,4,2]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_cyclic_5 : 15 ≤ LatinSquare.T 5 := by
  have hi : Function.Injective seeds5 :=
    selector_injective_of_mono finSelectorCode seeds5 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hz : ∀ i, seeds5 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTransversal (cyclicSquare 5) (seeds5 i) := by
    change ∀ i, Function.Injective (seeds5 i) ∧ Function.Injective (fun j => j + seeds5 i j)
    decide +kernel
  exact (translations_count seeds5 hi hz ht).trans (cast_count_ge _)

def seeds7 : Fin 7 → Fin 7 → Fin 7 :=
  ![![0,1,2,3,4,5,6],
  ![0,1,3,5,2,6,4],
  ![0,1,4,2,6,3,5],
  ![0,2,3,6,4,1,5],
  ![0,2,4,1,5,3,6],
  ![0,2,4,5,1,6,3],
  ![0,2,4,6,1,3,5]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_cyclic_7 : 49 ≤ LatinSquare.T 7 := by
  have hi : Function.Injective seeds7 :=
    selector_injective_of_mono finSelectorCode seeds7 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hz : ∀ i, seeds7 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTransversal (cyclicSquare 7) (seeds7 i) := by
    change ∀ i, Function.Injective (seeds7 i) ∧ Function.Injective (fun j => j + seeds7 i j)
    decide +kernel
  exact (translations_count seeds7 hi hz ht).trans (cast_count_ge _)

def seeds9 : Fin 15 → Fin 9 → Fin 9 :=
  ![![0,1,2,3,4,5,6,7,8],
  ![0,1,2,4,6,3,8,5,7],
  ![0,1,2,5,3,7,4,8,6],
  ![0,1,3,4,6,7,2,8,5],
  ![0,1,3,4,6,8,2,5,7],
  ![0,1,3,4,8,5,2,6,7],
  ![0,1,3,5,2,7,4,6,8],
  ![0,1,3,5,6,2,7,8,4],
  ![0,1,3,5,8,2,4,6,7],
  ![0,1,3,7,4,2,6,8,5],
  ![0,1,4,2,6,3,7,5,8],
  ![0,1,4,5,3,7,8,6,2],
  ![0,1,4,5,3,8,6,7,2],
  ![0,1,4,5,8,2,7,3,6],
  ![0,1,4,7,3,8,2,5,6]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_cyclic_9 : 135 ≤ LatinSquare.T 9 := by
  have hi : Function.Injective seeds9 :=
    selector_injective_of_mono finSelectorCode seeds9 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hz : ∀ i, seeds9 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTransversal (cyclicSquare 9) (seeds9 i) := by
    change ∀ i, Function.Injective (seeds9 i) ∧ Function.Injective (fun j => j + seeds9 i j)
    decide +kernel
  exact (translations_count seeds9 hi hz ht).trans (cast_count_ge _)

def seeds11 : Fin 4 → Fin 11 → Fin 11 :=
  ![![0,1,3,5,8,10,4,2,6,9,7],
  ![0,1,3,5,10,4,6,8,2,9,7],
  ![0,1,3,5,10,7,4,2,9,6,8],
  ![0,1,3,6,2,5,9,7,4,10,8]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_cyclic_11 : 484 ≤ LatinSquare.T 11 := by
  have hi : Function.Injective seeds11 :=
    selector_injective_of_mono finSelectorCode seeds11 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hz : ∀ i, seeds11 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTransversal (cyclicSquare 11) (seeds11 i) := by
    change ∀ i, Function.Injective (seeds11 i) ∧ Function.Injective (fun j => j + seeds11 i j)
    decide +kernel
  have hu : ∀ i j, seeds11 i (j+1) - seeds11 i j = 1 ↔ j = 0 := by decide +kernel
  exact (two_translations_count seeds11 hi hz ht hu).trans (cast_count_ge _)

def seeds13 : Fin 7 → Fin 13 → Fin 13 :=
  ![![0,1,3,5,2,6,8,10,4,7,12,9,11],
  ![0,1,3,5,2,6,10,7,4,8,12,9,11],
  ![0,1,3,5,2,7,10,4,6,8,12,9,11],
  ![0,1,3,5,2,9,6,4,8,11,7,12,10],
  ![0,1,3,5,7,2,6,9,11,8,4,12,10],
  ![0,1,3,5,7,4,6,9,11,8,10,12,2],
  ![0,1,3,5,7,4,6,10,8,11,9,12,2]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_cyclic_13 : 1183 ≤ LatinSquare.T 13 := by
  have hi : Function.Injective seeds13 :=
    selector_injective_of_mono finSelectorCode seeds13 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hz : ∀ i, seeds13 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTransversal (cyclicSquare 13) (seeds13 i) := by
    change ∀ i, Function.Injective (seeds13 i) ∧ Function.Injective (fun j => j + seeds13 i j)
    decide +kernel
  have hu : ∀ i j, seeds13 i (j+1) - seeds13 i j = 1 ↔ j = 0 := by decide +kernel
  exact (two_translations_count seeds13 hi hz ht hu).trans (cast_count_ge _)

def seeds17 : Fin 35 → Fin 17 → Fin 17 :=
  ![![0,1,3,5,2,4,6,8,10,7,11,9,12,14,16,13,15],
  ![0,1,3,5,2,4,6,8,10,7,11,9,12,15,13,16,14],
  ![0,1,3,5,2,4,6,9,7,11,8,10,12,14,16,13,15],
  ![0,1,3,5,2,4,6,9,7,11,8,10,12,15,13,16,14],
  ![0,1,3,5,2,4,7,9,12,6,8,10,15,11,14,16,13],
  ![0,1,3,5,2,4,7,11,8,6,10,13,9,16,14,12,15],
  ![0,1,3,5,2,4,8,11,7,12,6,9,16,14,10,15,13],
  ![0,1,3,5,2,4,8,13,7,9,6,10,15,11,16,14,12],
  ![0,1,3,5,2,4,8,13,7,9,6,10,16,11,15,12,14],
  ![0,1,3,5,2,4,9,6,8,12,10,7,15,11,14,16,13],
  ![0,1,3,5,2,4,9,6,10,7,11,13,8,16,14,12,15],
  ![0,1,3,5,2,4,10,8,6,9,11,13,15,7,16,14,12],
  ![0,1,3,5,2,4,10,8,6,9,11,13,16,7,15,12,14],
  ![0,1,3,5,2,4,10,8,6,11,14,7,9,16,13,15,12],
  ![0,1,3,5,2,6,8,11,7,12,10,15,4,14,16,9,13],
  ![0,1,3,5,2,6,8,11,7,12,10,15,4,16,13,9,14],
  ![0,1,3,5,2,6,8,11,7,12,10,16,4,13,15,9,14],
  ![0,1,3,5,2,6,8,11,7,12,14,9,4,16,13,15,10],
  ![0,1,3,5,2,6,8,11,7,12,16,9,4,14,10,15,13],
  ![0,1,3,5,2,6,8,11,16,7,10,4,9,13,15,12,14],
  ![0,1,3,5,2,6,8,11,16,7,10,4,9,14,12,15,13],
  ![0,1,3,5,2,6,8,13,7,9,11,15,4,16,10,12,14],
  ![0,1,3,5,2,6,8,13,7,9,14,10,4,16,12,15,11],
  ![0,1,3,5,2,6,8,13,7,9,16,10,4,11,15,12,14],
  ![0,1,3,5,2,6,8,13,10,7,14,4,9,16,12,15,11],
  ![0,1,3,5,2,6,8,13,10,7,16,4,9,11,15,12,14],
  ![0,1,3,5,2,6,9,7,12,15,8,10,4,13,16,14,11],
  ![0,1,3,5,2,6,9,7,12,15,8,10,4,14,16,11,13],
  ![0,1,3,5,2,6,9,7,12,15,8,10,4,16,13,11,14],
  ![0,1,3,5,2,6,9,7,13,11,8,15,4,16,10,12,14],
  ![0,1,3,5,2,6,9,7,16,11,8,10,4,13,15,12,14],
  ![0,1,3,5,2,6,9,7,16,11,8,10,4,14,12,15,13],
  ![0,1,3,5,2,6,9,11,4,7,10,13,15,8,12,16,14],
  ![0,1,3,5,2,6,9,11,4,7,10,15,12,8,13,16,14],
  ![0,1,3,5,2,6,9,11,4,7,14,10,8,13,16,12,15]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_cyclic_17 : 10115 ≤ LatinSquare.T 17 := by
  have hi : Function.Injective seeds17 :=
    selector_injective_of_mono finSelectorCode seeds17 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hz : ∀ i, seeds17 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTransversal (cyclicSquare 17) (seeds17 i) := by
    change ∀ i, Function.Injective (seeds17 i) ∧ Function.Injective (fun j => j + seeds17 i j)
    decide +kernel
  have hu : ∀ i j, seeds17 i (j+1) - seeds17 i j = 1 ↔ j = 0 := by decide +kernel
  exact (two_translations_count seeds17 hi hz ht hu).trans (cast_count_ge _)

def seeds19 : Fin 82 → Fin 19 → Fin 19 :=
  ![![0,1,3,5,2,4,6,8,10,13,7,9,11,16,12,17,14,18,15],
  ![0,1,3,5,2,4,6,8,10,13,7,9,11,17,12,14,16,18,15],
  ![0,1,3,5,2,4,6,8,12,9,7,11,14,10,15,18,16,13,17],
  ![0,1,3,5,2,4,6,8,12,9,7,11,14,10,16,18,13,15,17],
  ![0,1,3,5,2,4,6,9,12,8,13,7,10,16,18,11,14,17,15],
  ![0,1,3,5,2,4,6,9,12,8,13,7,10,17,15,11,18,16,14],
  ![0,1,3,5,2,4,6,9,14,8,10,7,11,13,18,15,17,12,16],
  ![0,1,3,5,2,4,6,10,7,9,13,11,8,16,12,17,14,18,15],
  ![0,1,3,5,2,4,6,10,7,9,13,11,8,17,12,14,16,18,15],
  ![0,1,3,5,2,4,6,10,7,11,8,12,14,9,15,18,16,13,17],
  ![0,1,3,5,2,4,6,10,7,11,8,12,14,9,16,18,13,15,17],
  ![0,1,3,5,2,4,6,10,8,11,13,7,14,9,18,15,17,12,16],
  ![0,1,3,5,2,4,6,10,8,11,13,7,17,9,12,15,18,16,14],
  ![0,1,3,5,2,4,6,11,8,13,7,9,14,10,18,15,17,12,16],
  ![0,1,3,5,2,4,6,11,8,13,7,9,17,10,12,15,18,16,14],
  ![0,1,3,5,2,4,6,11,9,7,10,12,17,13,8,15,18,16,14],
  ![0,1,3,5,2,4,6,11,9,7,12,15,8,10,16,18,13,17,14],
  ![0,1,3,5,2,4,6,11,9,7,12,15,8,10,18,14,17,13,16],
  ![0,1,3,5,2,4,7,9,12,8,13,11,6,17,15,18,10,14,16],
  ![0,1,3,5,2,4,7,9,12,8,13,11,6,18,16,14,10,17,15],
  ![0,1,3,5,2,4,7,9,12,8,16,11,6,10,15,18,14,17,13],
  ![0,1,3,5,2,4,7,9,12,8,16,11,6,10,17,14,18,13,15],
  ![0,1,3,5,2,4,7,9,12,14,8,6,10,13,16,18,15,17,11],
  ![0,1,3,5,2,4,7,9,12,14,8,6,10,13,17,15,18,16,11],
  ![0,1,3,5,2,4,7,9,12,14,8,6,10,17,15,11,18,16,13],
  ![0,1,3,5,2,4,7,9,12,14,8,6,10,18,15,11,17,13,16],
  ![0,1,3,5,2,4,7,9,12,14,8,6,10,18,16,11,13,17,15],
  ![0,1,3,5,2,4,7,9,14,8,10,12,6,13,16,18,15,17,11],
  ![0,1,3,5,2,4,7,9,14,8,10,12,6,13,17,15,18,16,11],
  ![0,1,3,5,2,4,7,9,14,8,10,12,6,17,15,11,18,16,13],
  ![0,1,3,5,2,4,7,9,14,8,10,12,6,18,15,11,17,13,16],
  ![0,1,3,5,2,4,7,9,14,8,10,12,6,18,16,11,13,17,15],
  ![0,1,3,5,2,4,7,9,14,11,8,6,17,10,12,15,18,16,13],
  ![0,1,3,5,2,4,7,9,14,11,8,6,17,10,12,16,18,13,15],
  ![0,1,3,5,2,4,7,9,14,11,8,6,17,10,12,18,15,13,16],
  ![0,1,3,5,2,4,7,9,14,11,8,6,18,10,12,16,13,17,15],
  ![0,1,3,5,2,4,7,9,15,11,8,6,10,13,17,14,18,16,12],
  ![0,1,3,5,2,4,7,9,15,11,8,6,10,16,12,18,14,17,13],
  ![0,1,3,5,2,4,7,9,15,11,8,6,10,17,12,14,18,16,13],
  ![0,1,3,5,2,4,7,9,15,11,8,6,10,18,12,14,17,13,16],
  ![0,1,3,5,2,4,7,10,6,9,13,11,8,16,12,15,18,14,17],
  ![0,1,3,5,2,4,7,10,6,11,8,12,14,9,17,15,13,18,16],
  ![0,1,3,5,2,4,7,10,8,11,13,15,6,9,17,14,18,16,12],
  ![0,1,3,5,2,4,7,10,8,11,13,18,6,9,12,15,17,14,16],
  ![0,1,3,5,2,4,7,10,8,11,13,18,6,9,12,16,14,17,15],
  ![0,1,3,5,2,4,7,10,8,11,16,12,6,9,15,18,14,17,13],
  ![0,1,3,5,2,4,7,10,8,11,16,12,6,9,17,14,18,13,15],
  ![0,1,3,5,2,4,7,10,8,14,12,9,6,13,16,18,15,17,11],
  ![0,1,3,5,2,4,7,10,8,14,12,9,6,13,17,15,18,16,11],
  ![0,1,3,5,2,4,7,10,8,14,12,9,6,17,15,11,18,16,13],
  ![0,1,3,5,2,4,7,10,8,14,12,9,6,18,15,11,17,13,16],
  ![0,1,3,5,2,4,7,10,8,14,12,9,6,18,16,11,13,17,15],
  ![0,1,3,5,2,4,7,10,12,6,8,11,14,16,9,18,15,13,17],
  ![0,1,3,5,2,4,7,10,12,6,8,11,14,17,9,16,13,18,15],
  ![0,1,3,5,2,4,7,10,12,6,8,11,17,13,9,16,14,18,15],
  ![0,1,3,5,2,4,7,10,12,9,6,11,14,17,15,8,18,16,13],
  ![0,1,3,5,2,4,7,10,12,9,6,11,14,18,15,8,17,13,16],
  ![0,1,3,5,2,4,7,10,12,9,6,11,14,18,16,8,13,17,15],
  ![0,1,3,5,2,4,7,10,12,9,6,11,18,13,15,8,17,14,16],
  ![0,1,3,5,2,4,7,10,12,9,6,15,11,16,8,18,14,17,13],
  ![0,1,3,5,2,4,7,10,12,9,6,15,11,17,8,14,18,16,13],
  ![0,1,3,5,2,4,7,10,12,9,6,15,11,18,8,14,17,13,16],
  ![0,1,3,5,2,4,7,10,12,9,6,18,11,13,8,15,17,14,16],
  ![0,1,3,5,2,4,7,10,12,9,6,18,11,13,8,16,14,17,15],
  ![0,1,3,5,2,4,7,10,14,9,6,12,8,13,16,18,15,17,11],
  ![0,1,3,5,2,4,7,10,14,9,6,12,8,13,17,15,18,16,11],
  ![0,1,3,5,2,4,7,10,14,9,6,12,8,17,15,11,18,16,13],
  ![0,1,3,5,2,4,7,10,14,9,6,12,8,18,15,11,17,13,16],
  ![0,1,3,5,2,4,7,10,14,9,6,12,8,18,16,11,13,17,15],
  ![0,1,3,5,2,4,7,10,15,9,6,11,8,13,17,14,18,16,12],
  ![0,1,3,5,2,4,7,10,15,9,6,11,8,16,12,18,14,17,13],
  ![0,1,3,5,2,4,7,10,15,9,6,11,8,17,12,14,18,16,13],
  ![0,1,3,5,2,4,7,10,15,9,6,11,8,18,12,14,17,13,16],
  ![0,1,3,5,2,4,7,11,6,8,10,12,14,9,17,15,13,18,16],
  ![0,1,3,5,2,4,7,11,6,8,12,9,14,10,17,15,13,18,16],
  ![0,1,3,5,2,4,7,11,8,13,10,6,14,16,9,18,15,17,12],
  ![0,1,3,5,2,4,7,11,8,13,10,6,14,17,9,16,18,12,15],
  ![0,1,3,5,2,4,7,11,8,13,10,6,14,17,9,18,15,12,16],
  ![0,1,3,5,2,4,7,11,8,13,10,6,14,18,9,15,17,12,16],
  ![0,1,3,5,2,4,7,11,8,14,10,6,17,9,12,15,18,16,13],
  ![0,1,3,5,2,4,7,11,8,14,10,6,17,9,12,16,18,13,15],
  ![0,1,3,5,2,4,7,11,8,14,10,6,17,9,12,18,15,13,16]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_cyclic_19 : 29602 ≤ LatinSquare.T 19 := by
  have hi : Function.Injective seeds19 :=
    selector_injective_of_mono finSelectorCode seeds19 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hz : ∀ i, seeds19 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTransversal (cyclicSquare 19) (seeds19 i) := by
    change ∀ i, Function.Injective (seeds19 i) ∧ Function.Injective (fun j => j + seeds19 i j)
    decide +kernel
  have hu : ∀ i j, seeds19 i (j+1) - seeds19 i j = 1 ↔ j = 0 := by decide +kernel
  exact (two_translations_count seeds19 hi hz ht hu).trans (cast_count_ge _)



lemma explicit_count {n m : ℕ} (L : LatinSquare n) (w : Fin m → Fin n → Fin n)
    (hi : Function.Injective w) (ht : ∀ i, IsTransversal L (w i)) :
    m ≤ numTransversals L := by
  let F : Fin m → {σ : Fin n → Fin n // IsTransversal L σ} := fun i => ⟨w i, ht i⟩
  have h := Fintype.card_le_of_injective F (fun _ _ hij => hi (congrArg Subtype.val hij))
  simpa [numTransversals] using h

def evenSquare6 : LatinSquare 6 where
  mat := ![![0,1,2,3,4,5], ![1,0,3,2,5,4], ![2,3,4,5,0,1], ![3,2,5,4,1,0], ![4,5,0,1,3,2], ![5,4,1,0,2,3]]
  row_injective := by decide +kernel
  col_injective := by
    change ∀ j : Fin 6, Function.Injective
      (fun i => (![![0,1,2,3,4,5], ![1,0,3,2,5,4], ![2,3,4,5,0,1], ![3,2,5,4,1,0], ![4,5,0,1,3,2], ![5,4,1,0,2,3]] : Fin 6 → Fin 6 → Fin 6) i j)
    decide +kernel

def evenSeeds6 : Fin 26 → Fin 6 → Fin 6 :=
  ![![0,2,3,4,5,1],
  ![0,2,5,3,1,4],
  ![0,3,2,4,1,5],
  ![0,3,5,2,4,1],
  ![0,4,1,3,5,2],
  ![0,4,2,1,3,5],
  ![0,5,1,2,3,4],
  ![0,5,3,1,4,2],
  ![1,2,3,5,0,4],
  ![1,2,4,3,5,0],
  ![1,3,2,5,4,0],
  ![1,3,4,2,0,5],
  ![1,4,0,3,2,5],
  ![1,4,2,0,5,3],
  ![1,5,0,2,4,3],
  ![1,5,3,0,2,4],
  ![2,0,3,5,4,1],
  ![2,0,4,3,1,5],
  ![2,1,3,4,0,5],
  ![2,1,5,3,4,0],
  ![3,0,2,5,1,4],
  ![3,0,4,2,5,1],
  ![3,1,2,4,5,0],
  ![3,1,5,2,0,4],
  ![4,0,1,2,5,3],
  ![4,0,3,1,2,5]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_even_6 : 26 ≤ LatinSquare.T 6 := by
  have hi : Function.Injective evenSeeds6 :=
    selector_injective_of_mono finSelectorCode evenSeeds6 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hp : ∀ i, IsTransversal evenSquare6 (evenSeeds6 i) := by decide +kernel
  exact (explicit_count evenSquare6 evenSeeds6 hi hp).trans (cast_count_ge _)


def evenSquare8 : LatinSquare 8 where
  mat := ![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6], ![2,3,0,1,6,7,4,5], ![3,2,1,0,7,6,5,4], ![4,5,6,7,1,0,3,2], ![5,4,7,6,0,1,2,3], ![6,7,4,5,3,2,1,0], ![7,6,5,4,2,3,0,1]]
  row_injective := by decide +kernel
  col_injective := by
    change ∀ j : Fin 8, Function.Injective
      (fun i => (![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6], ![2,3,0,1,6,7,4,5], ![3,2,1,0,7,6,5,4], ![4,5,6,7,1,0,3,2], ![5,4,7,6,0,1,2,3], ![6,7,4,5,3,2,1,0], ![7,6,5,4,2,3,0,1]] : Fin 8 → Fin 8 → Fin 8) i j)
    decide +kernel

def evenSeeds8 : Fin 77 → Fin 8 → Fin 8 :=
  ![![0,2,4,6,3,1,5,7],
  ![0,2,4,6,7,5,1,3],
  ![0,2,5,7,1,3,6,4],
  ![0,2,5,7,4,6,3,1],
  ![0,2,6,4,1,3,5,7],
  ![0,2,6,4,7,5,3,1],
  ![0,2,7,5,3,1,6,4],
  ![0,2,7,5,4,6,1,3],
  ![0,3,4,7,1,2,6,5],
  ![0,3,4,7,6,5,1,2],
  ![0,3,5,6,2,1,4,7],
  ![0,3,5,6,4,7,2,1],
  ![0,3,6,5,1,2,4,7],
  ![0,3,6,5,4,7,1,2],
  ![0,3,7,4,2,1,6,5],
  ![0,3,7,4,6,5,2,1],
  ![0,4,1,5,3,6,2,7],
  ![0,4,1,5,7,2,6,3],
  ![0,4,3,7,2,6,1,5],
  ![0,4,3,7,6,2,5,1],
  ![0,4,5,1,2,7,6,3],
  ![0,4,5,1,6,3,2,7],
  ![0,4,6,2,3,7,5,1],
  ![0,4,6,2,7,3,1,5],
  ![0,5,1,4,2,6,3,7],
  ![0,5,1,4,7,3,6,2],
  ![0,5,3,6,2,7,1,4],
  ![0,5,3,6,7,2,4,1],
  ![0,5,4,1,3,7,6,2],
  ![0,5,4,1,6,2,3,7],
  ![0,5,7,2,3,6,4,1],
  ![0,5,7,2,6,3,1,4],
  ![0,6,1,7,2,5,3,4],
  ![0,6,1,7,4,3,5,2],
  ![0,6,3,5,1,7,2,4],
  ![0,6,3,5,7,1,4,2],
  ![0,6,4,2,1,7,5,3],
  ![0,6,4,2,7,1,3,5],
  ![0,6,7,1,2,5,4,3],
  ![0,6,7,1,4,3,2,5],
  ![0,7,1,6,3,5,2,4],
  ![0,7,1,6,4,2,5,3],
  ![0,7,3,4,1,6,2,5],
  ![0,7,3,4,6,1,5,2],
  ![0,7,5,2,1,6,4,3],
  ![0,7,5,2,6,1,3,4],
  ![0,7,6,1,3,5,4,2],
  ![0,7,6,1,4,2,3,5],
  ![1,2,4,7,3,0,5,6],
  ![1,2,4,7,5,6,3,0],
  ![1,2,5,6,0,3,7,4],
  ![1,2,5,6,7,4,0,3],
  ![1,2,6,5,3,0,7,4],
  ![1,2,6,5,7,4,3,0],
  ![1,2,7,4,0,3,5,6],
  ![1,2,7,4,5,6,0,3],
  ![1,3,4,6,0,2,7,5],
  ![1,3,4,6,5,7,2,0],
  ![1,3,5,7,2,0,4,6],
  ![1,3,5,7,6,4,0,2],
  ![1,3,6,4,2,0,7,5],
  ![1,3,6,4,5,7,0,2],
  ![1,3,7,5,0,2,4,6],
  ![1,3,7,5,6,4,2,0],
  ![1,4,0,5,3,7,2,6],
  ![1,4,0,5,6,2,7,3],
  ![1,4,2,7,3,6,0,5],
  ![1,4,2,7,6,3,5,0],
  ![1,4,5,0,2,6,7,3],
  ![1,4,5,0,7,3,2,6],
  ![1,4,6,3,2,7,5,0],
  ![1,4,6,3,7,2,0,5],
  ![1,5,0,4,2,7,3,6],
  ![1,5,0,4,6,3,7,2],
  ![1,5,2,6,3,7,0,4],
  ![1,5,2,6,7,3,4,0],
  ![1,5,4,0,3,6,7,2]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_even_8 : 77 ≤ LatinSquare.T 8 := by
  have hi : Function.Injective evenSeeds8 :=
    selector_injective_of_mono finSelectorCode evenSeeds8 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have hp : ∀ i, IsTransversal evenSquare8 (evenSeeds8 i) := by decide +kernel
  exact (explicit_count evenSquare8 evenSeeds8 hi hp).trans (cast_count_ge _)

open Finset

abbrev TurnIndex (q : ℕ) := Fin 2 × Fin q

def turnEntry {q : ℕ} [NeZero q] (x y : TurnIndex q) : TurnIndex q :=
  (x.1 + y.1 + (if x.2 = y.2 then 1 else 0), x.2 + y.2)

def turnSquare (q : ℕ) [NeZero q] : SquareOn (TurnIndex q) where
  entry := turnEntry
  row x := by
    intro y z h
    have h₂ : y.2 = z.2 := add_left_cancel (congrArg Prod.snd h)
    have h₁ := congrArg Prod.fst h
    change x.1 + y.1 + (if x.2 = y.2 then 1 else 0) =
      x.1 + z.1 + (if x.2 = z.2 then 1 else 0) at h₁
    rw [h₂] at h₁
    exact Prod.ext (add_left_cancel (add_right_cancel h₁)) h₂
  col y := by
    intro x z h
    have h₂ : x.2 = z.2 := add_right_cancel (congrArg Prod.snd h)
    have h₁ := congrArg Prod.fst h
    change x.1 + y.1 + (if x.2 = y.2 then 1 else 0) =
      z.1 + y.1 + (if z.2 = y.2 then 1 else 0) at h₁
    rw [h₂] at h₁
    exact Prod.ext (add_right_cancel (add_right_cancel h₁)) h₂

lemma turnEntry_translate {q : ℕ} [NeZero q] (x y : TurnIndex q) (a b : Fin 2) (t : Fin q) :
    turnEntry (x + (a,t)) (y + (b,t)) = turnEntry x y + (a + b,t + t) := by
  apply Prod.ext
  · change x.1 + a + (y.1 + b) + (if x.2 + t = y.2 + t then 1 else 0) =
       (x.1 + y.1 + (if x.2 = y.2 then 1 else 0)) + (a + b)
    simp only [add_left_inj]
    abel
  · change (x.2 + t) + (y.2 + t) = (x.2 + y.2) + (t + t)
    abel

def translateTurn {q : ℕ} [NeZero q] (f : TurnIndex q → TurnIndex q)
    (a b : Fin 2) (t : Fin q) : TurnIndex q → TurnIndex q :=
  fun x => f (x - (a,t)) + (b,t)

lemma translateTurn_trans {q : ℕ} [NeZero q] {f : TurnIndex q → TurnIndex q}
    (hf : IsTrans (turnSquare q) f) (a b : Fin 2) (t : Fin q) :
    IsTrans (turnSquare q) (translateTurn f a b t) := by
  refine ⟨fun _ _ h => sub_left_injective (hf.1 (add_right_cancel h)),?_⟩
  intro x y h
  change turnEntry x (f (x - (a,t)) + (b,t)) =
    turnEntry y (f (y - (a,t)) + (b,t)) at h
  have he (x : TurnIndex q) :
      turnEntry x (f (x - (a,t)) + (b,t)) =
        turnEntry (x - (a,t)) (f (x - (a,t))) + (a + b,t+t) := by
    simpa only [sub_add_cancel] using turnEntry_translate (x - (a,t)) (f (x - (a,t))) a b t
  rw [he, he] at h
  exact sub_left_injective (hf.2 (add_right_cancel h))

lemma translateTurn_marker {q : ℕ} [NeZero q] {f : TurnIndex q → TurnIndex q}
    (hf : ∀ x, (f x).2 = x.2 ↔ x = 0) (a b : Fin 2) (t : Fin q) (x : TurnIndex q) :
    (translateTurn f a b t x).2 = x.2 ↔ x = (a,t) := by
  change (f (x - (a,t))).2 + t = x.2 ↔ _
  rw [← eq_sub_iff_add_eq]
  change (f (x - (a,t))).2 = (x - (a,t)).2 ↔ _
  rw [hf, sub_eq_zero]

lemma turn_count {q m : ℕ} [NeZero q] (s : Fin m → TurnIndex q → TurnIndex q)
    (hi : Function.Injective s) (h0 : ∀ i, s i 0 = 0)
    (ht : ∀ i, IsTrans (turnSquare q) (s i))
    (hm : ∀ i x, (s i x).2 = x.2 ↔ x = 0) :
    m * (2 * (2 * q)) ≤ LatinSquare.T (2 * q) := by
  let F : Fin m × Fin 2 × Fin 2 × Fin q → TransOn (turnSquare q) :=
    fun (i,a,b,t) => ⟨translateTurn (s i) a b t, translateTurn_trans (ht i) a b t⟩
  have hF : Function.Injective F := by
    rintro ⟨i,a,b,t⟩ ⟨i',a',b',t'⟩ h
    have he : translateTurn (s i) a b t = translateTurn (s i') a' b' t' := congrArg Subtype.val h
    have hm' : (a,t) = (a',t') := by
      apply (translateTurn_marker (hm i') a' b' t' (a,t)).1
      rw [← he]
      exact (translateTurn_marker (hm i) a b t (a,t)).2 rfl
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hm'
    have hb : (b,t) = (b',t) := by
      simpa [translateTurn,h0] using congrFun he (a,t)
    obtain rfl : b = b' := congrArg Prod.fst hb
    have hi' : i = i' := by
      apply hi
      funext x
      simpa [translateTurn] using congrFun he (x + (a,t))
    subst i'
    rfl
  let e : TurnIndex q ≃ Fin (2 * q) :=
    Fintype.equivFinOfCardEq (by simp)
  let L := (turnSquare q).onFin e
  have h := Fintype.card_le_of_injective
    (((turnSquare q).toFinTrans e) ∘ F) (((turnSquare q).toFinTrans_injective e).comp hF)
  have hy : m * (2 * (2 * q)) ≤ numTransversals L := by
    simpa [L,numTransversals] using h
  exact hy.trans (Finset.le_sup (f := fun K : LatinSquare (2*q) => numTransversals K) (mem_univ L))

def turnSelectorCode {q : ℕ} (f : TurnIndex q → TurnIndex q) : ℕ :=
  ((List.ofFn fun a : Fin 2 => List.ofFn fun i : Fin q =>
      (f (a,i)).1.val * q + (f (a,i)).2.val).flatten).foldl
    (fun value digit => value * (2*q) + digit) 0

def turnSeeds10 : Fin 12 → TurnIndex 5 → TurnIndex 5 :=
  ![(fun x => (![![(0,0),(0,2),(0,3),(1,1),(1,2)],![(1,4),(1,0),(0,1),(0,4),(1,3)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(1,4),(1,2)],![(0,4),(1,0),(0,1),(1,1),(1,3)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,4),(1,4),(1,2)],![(0,3),(1,3),(1,0),(0,1),(1,1)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,0),(0,4),(1,2)],![(0,3),(1,3),(1,4),(0,1),(1,1)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,0),(1,1),(0,1)],![(0,3),(1,3),(0,4),(1,4),(1,2)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,1),(0,1),(1,2)],![(0,4),(1,0),(1,3),(1,4),(0,3)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,1),(0,4),(1,0)],![(0,1),(1,3),(1,4),(1,2),(0,3)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,1),(0,4),(1,2)],![(1,4),(1,0),(1,3),(0,1),(0,3)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,1),(0,4),(1,3)],![(0,1),(0,3),(1,4),(1,2),(1,0)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,4),(0,4),(1,0)],![(1,1),(1,3),(0,1),(1,2),(0,3)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,4),(0,4),(1,3)],![(1,1),(0,3),(0,1),(1,2),(1,0)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(1,4),(1,1),(0,1)],![(0,3),(1,3),(1,0),(0,4),(1,2)]] : Fin 2 → Fin 5 → TurnIndex 5) x.1 x.2)]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_turn_10 : 240 ≤ LatinSquare.T 10 := by
  have hi : Function.Injective turnSeeds10 :=
    selector_injective_of_mono turnSelectorCode turnSeeds10 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have h0 : ∀ i, turnSeeds10 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTrans (turnSquare 5) (turnSeeds10 i) := by decide +kernel
  have hm : ∀ i x, (turnSeeds10 i x).2 = x.2 ↔ x = 0 := by decide +kernel
  exact turn_count turnSeeds10 hi h0 ht hm

def turnSeeds14 : Fin 71 → TurnIndex 7 → TurnIndex 7 :=
  ![(fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,2)],![(0,5),(1,5),(1,6),(0,6),(1,3),(1,4),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,2)],![(0,5),(1,5),(1,6),(1,4),(0,6),(0,4),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,2)],![(0,5),(1,6),(1,4),(0,6),(1,5),(1,3),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,2)],![(0,5),(1,6),(1,4),(1,5),(0,6),(0,4),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,3)],![(0,5),(1,6),(0,6),(1,5),(1,2),(1,4),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,3)],![(1,6),(0,4),(1,5),(0,5),(0,6),(1,4),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,4)],![(0,5),(1,5),(0,6),(1,6),(1,3),(0,4),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,4)],![(0,5),(1,6),(0,6),(1,5),(1,2),(0,4),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,1),(1,4)],![(1,6),(0,4),(0,6),(1,5),(0,5),(1,2),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,3),(1,4)],![(0,5),(1,6),(0,4),(0,6),(1,5),(1,1),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,3),(1,4)],![(0,6),(0,4),(1,5),(1,6),(0,5),(1,1),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,4),(1,2)],![(0,5),(1,5),(0,4),(1,6),(0,6),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,0),(1,4),(1,2)],![(0,5),(1,6),(0,4),(1,5),(0,6),(1,1),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,0)],![(1,2),(1,5),(1,6),(1,4),(0,5),(0,6),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,0)],![(1,2),(1,5),(1,6),(1,4),(0,6),(0,4),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,0)],![(1,2),(1,6),(1,4),(1,5),(0,5),(0,6),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,0)],![(1,2),(1,6),(1,4),(1,5),(0,6),(0,4),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,4)],![(0,4),(0,5),(1,6),(0,6),(1,5),(1,2),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,4)],![(0,6),(1,0),(1,5),(1,6),(1,2),(0,4),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,4)],![(0,6),(1,6),(1,0),(1,5),(1,2),(0,4),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,4)],![(1,2),(1,6),(0,4),(1,5),(0,5),(0,6),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,4)],![(1,6),(1,0),(0,4),(0,6),(1,5),(1,2),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,5)],![(0,6),(1,0),(1,4),(1,6),(0,5),(1,2),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,5)],![(1,2),(0,5),(1,6),(1,4),(0,6),(0,4),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,3),(1,5)],![(1,6),(0,5),(1,0),(1,4),(0,6),(0,4),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,4),(1,0)],![(0,4),(1,5),(1,6),(0,5),(0,6),(1,2),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,4),(1,0)],![(1,2),(1,5),(1,6),(0,5),(1,3),(0,6),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,4),(1,2)],![(0,4),(0,5),(1,5),(1,6),(0,6),(1,3),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,4),(1,2)],![(1,6),(0,5),(1,0),(1,5),(1,3),(0,6),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,4),(1,5)],![(0,6),(1,6),(1,0),(0,5),(1,2),(1,3),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,4),(1,5)],![(1,2),(1,6),(0,4),(0,5),(0,6),(1,3),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,4),(1,5)],![(1,6),(1,0),(0,4),(0,5),(0,6),(1,2),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,6),(1,0)],![(1,2),(1,5),(0,6),(1,4),(0,5),(1,3),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,6),(1,2)],![(0,6),(1,5),(1,0),(1,4),(0,5),(1,3),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,6),(1,3)],![(0,6),(1,0),(1,4),(0,5),(1,5),(1,2),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,6),(1,3)],![(0,6),(1,0),(1,5),(0,5),(1,2),(1,4),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,6),(1,4)],![(0,6),(1,0),(1,5),(0,5),(1,2),(0,4),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,6),(1,4)],![(0,6),(1,5),(1,0),(0,5),(1,3),(0,4),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,1),(1,6),(1,4)],![(1,2),(0,5),(0,6),(1,5),(1,3),(0,4),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,0),(1,3)],![(0,4),(1,5),(1,6),(0,5),(0,6),(1,4),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,0),(1,3)],![(1,1),(1,6),(1,4),(0,5),(1,5),(0,6),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,0),(1,4)],![(0,4),(1,5),(0,6),(1,6),(0,5),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,0),(1,4)],![(0,4),(1,6),(0,6),(1,5),(0,5),(1,1),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,0),(1,4)],![(1,1),(1,5),(0,6),(1,6),(1,3),(0,4),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,0),(1,5)],![(1,1),(1,6),(1,4),(0,5),(0,6),(0,4),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,3),(1,4)],![(1,1),(0,4),(1,5),(1,6),(0,5),(0,6),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,3),(1,4)],![(1,6),(0,4),(1,0),(1,5),(0,5),(0,6),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,3),(1,5)],![(0,5),(1,0),(1,4),(1,6),(0,6),(0,4),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,4),(1,5)],![(0,5),(1,0),(0,6),(1,6),(1,3),(1,1),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,4),(1,5)],![(1,6),(0,4),(1,0),(0,5),(0,6),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,6),(1,3)],![(0,5),(1,0),(0,6),(1,4),(1,5),(1,1),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,2),(1,6),(1,3)],![(1,1),(0,4),(1,5),(0,5),(0,6),(1,4),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,0),(1,2)],![(0,4),(0,5),(1,4),(1,6),(0,6),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,0),(1,2)],![(0,4),(0,5),(1,6),(1,4),(0,6),(1,1),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,0),(1,2)],![(1,1),(0,5),(1,4),(1,6),(1,3),(0,6),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,0),(1,4)],![(0,4),(0,5),(0,6),(1,6),(1,2),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,0),(1,4)],![(0,4),(0,5),(0,6),(1,6),(1,3),(1,1),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,0),(1,4)],![(1,1),(1,6),(0,4),(0,5),(1,2),(0,6),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,1),(1,2)],![(0,5),(1,0),(1,4),(1,6),(1,3),(0,6),(0,4)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,1),(1,2)],![(1,6),(0,4),(1,0),(1,4),(0,6),(1,3),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,1),(1,4)],![(1,2),(0,4),(1,6),(0,5),(1,3),(0,6),(1,0)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,1),(1,4)],![(1,6),(0,4),(1,0),(0,5),(1,3),(0,6),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,3),(1,0)],![(1,1),(0,4),(1,4),(1,6),(0,6),(1,2),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,3),(1,0)],![(1,2),(0,4),(1,6),(1,4),(0,6),(1,1),(0,5)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,3),(1,4)],![(0,5),(1,0),(0,4),(1,6),(1,2),(0,6),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,6),(1,0)],![(1,1),(0,4),(1,4),(0,5),(0,6),(1,2),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,6),(1,0)],![(1,2),(0,4),(1,4),(0,5),(0,6),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,6),(1,2)],![(0,5),(1,0),(0,4),(1,4),(0,6),(1,1),(1,3)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,6),(1,4)],![(0,6),(0,4),(1,0),(0,5),(1,2),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,5),(1,6),(1,4)],![(0,6),(0,4),(1,0),(0,5),(1,3),(1,1),(1,2)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2),
  (fun x => (![![(0,0),(0,2),(0,3),(0,1),(1,6),(1,0),(1,2)],![(0,4),(0,5),(1,4),(0,6),(1,5),(1,3),(1,1)]] : Fin 2 → Fin 7 → TurnIndex 7) x.1 x.2)]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma base_turn_14 : 1988 ≤ LatinSquare.T 14 := by
  have hi : Function.Injective turnSeeds14 :=
    selector_injective_of_mono turnSelectorCode turnSeeds14 (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel))
  have h0 : ∀ i, turnSeeds14 i 0 = 0 := by decide +kernel
  have ht : ∀ i, IsTrans (turnSquare 7) (turnSeeds14 i) := by decide +kernel
  have hm : ∀ i x, (turnSeeds14 i x).2 = x.2 ↔ x = 0 := by decide +kernel
  exact turn_count turnSeeds14 hi h0 ht hm

open Finset

noncomputable def maximizingSquare (n : ℕ) : LatinSquare n :=
  (Finset.exists_mem_eq_sup (Finset.univ : Finset (LatinSquare n))
    ⟨cyclicSquare n,mem_univ _⟩ numTransversals).choose

lemma maximizingSquare_spec (n : ℕ) :
    numTransversals (maximizingSquare n) = LatinSquare.T n :=
  ((Finset.exists_mem_eq_sup (Finset.univ : Finset (LatinSquare n))
    ⟨cyclicSquare n,mem_univ _⟩ numTransversals).choose_spec.2).symm

def prodTrans {A B : Type} (K : SquareOn A) (L : SquareOn B)
    (f : TransOn K) (g : A → TransOn L) : TransOn (K.prod L) where
  val x := (f.val x.1, (g x.1).val x.2)
  property := by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ h
      have he : i = j := f.property.1 (congrArg Prod.fst h)
      subst j
      exact Prod.ext rfl ((g i).property.1 (congrArg Prod.snd h))
    · rintro ⟨i,x⟩ ⟨j,y⟩ h
      have he : i = j := f.property.2 (congrArg Prod.fst h)
      subst j
      exact Prod.ext rfl ((g i).property.2 (congrArg Prod.snd h))

lemma prodTrans_injective {A B : Type} [Nonempty B] (K : SquareOn A) (L : SquareOn B) :
    Function.Injective (fun p : TransOn K × (A → TransOn L) => prodTrans K L p.1 p.2) := by
  rintro ⟨f,g⟩ ⟨f',g'⟩ h
  have hf : f = f' := by
    apply Subtype.ext
    funext a
    obtain ⟨b⟩ := ‹Nonempty B›
    exact congrArg (fun s : TransOn (K.prod L) => (s.val (a,b)).1) h
  have hg : g = g' := by
    funext a
    apply Subtype.ext
    funext b
    exact congrArg (fun s : TransOn (K.prod L) => (s.val (a,b)).2) h
  exact Prod.ext hf hg

lemma product_transversal_bound (a b : ℕ) (hb : 0 < b) :
    LatinSquare.T a * (LatinSquare.T b) ^ a ≤ LatinSquare.T (a*b) := by
  classical
  haveI : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
  let K := SquareOn.fromFin (maximizingSquare a)
  let L := SquareOn.fromFin (maximizingSquare b)
  let e : Fin a × Fin b ≃ Fin (a*b) := Fintype.equivFinOfCardEq (by simp)
  let Q := (K.prod L).onFin e
  have h₁ := Fintype.card_le_of_injective
    (((K.prod L).toFinTrans e) ∘ (fun p : TransOn K × (Fin a → TransOn L) => prodTrans K L p.1 p.2))
    (((K.prod L).toFinTrans_injective e).comp (prodTrans_injective K L))
  have htK : Fintype.card (TransOn K) = LatinSquare.T a := maximizingSquare_spec a
  have htL : Fintype.card (TransOn L) = LatinSquare.T b := maximizingSquare_spec b
  have h₂ : LatinSquare.T a * (LatinSquare.T b) ^ a ≤ numTransversals Q := by
    simpa [Q,numTransversals, Fintype.card_fun, htK, htL] using h₁
  exact h₂.trans (cast_count_ge Q)

def blockSquares {q r : ℕ} (K : LatinSquare q) (M : LatinSquare (q+r)) :
    ∀ i : Option (Fin 3), SquareOn (fourTypes q r i)
  | none => (SquareOn.fromFin M).transport finSumFinEquiv.symm
  | some _ => SquareOn.fromFin K

lemma transport_transCount {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (K : SquareOn A) (e : A ≃ B) :
    Fintype.card (TransOn (K.transport e)) = Fintype.card (TransOn K) := by
  classical
  let f (t : TransOn K) : TransOn (K.transport e) :=
    ⟨e ∘ t.val ∘ e.symm, e.injective.comp (t.property.1.comp e.symm.injective), by
      intro a b h
      change e (K.entry (e.symm a) (e.symm (e (t.val (e.symm a))))) =
        e (K.entry (e.symm b) (e.symm (e (t.val (e.symm b))))) at h
      simp only [Equiv.symm_apply_apply] at h
      exact e.symm.injective (t.property.2 (e.injective h))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    funext x
    apply e.injective
    simpa [f] using congrArg (fun s : TransOn (K.transport e) => s.val (e x)) h
  have hs : Function.Surjective f := by
    intro u
    let a : A → A := e.symm ∘ u.val ∘ e
    have ha : IsTrans K a := by
      refine ⟨e.symm.injective.comp (u.property.1.comp e.injective), ?_⟩
      intro i j h
      apply e.injective
      apply u.property.2
      change e (K.entry (e.symm (e i)) (e.symm (u.val (e i)))) =
        e (K.entry (e.symm (e j)) (e.symm (u.val (e j))))
      simpa [a] using congrArg e h
    refine ⟨⟨a,ha⟩,Subtype.ext ?_⟩
    funext x
    simp [f,a]
  exact Fintype.card_congr (Equiv.ofBijective f ⟨hf,hs⟩).symm

set_option maxHeartbeats 2000000 in
lemma four_bound {q r : ℕ} (K : SquareOn (Fin q))
    (E : Fin r → Equiv.Perm (Fin q))
    (hE : ∀ a, Function.Injective (fun t => E t a)) (hT : ∀ t, IsTrans K (E t)) :
    (LatinSquare.T q)^3 * LatinSquare.T (q+r) ≤ LatinSquare.T (4*q+r) := by
  classical
  let G := SquareOn.fromFin (cyclicSquare r)
  let A := fourTypes q r
  let B := scaffold K E hE hT G
  let L := blockSquares (maximizingSquare q) (maximizingSquare (q+r))
  let hB := scaffold_block K E hE hT G
  let Q := replaceBlocks B L hB
  let e : Sigma A ≃ Fin (4*q+r) :=
    (fourBlocksEquiv q r).trans (Fintype.equivFinOfCardEq (by simp))
  have hc := Fintype.card_le_of_injective
    ((Q.toFinTrans e) ∘ blockTrans B L hB)
    ((Q.toFinTrans_injective e).comp (blockTrans_injective B L hB))
  have hnone : Fintype.card (TransOn (L none)) = LatinSquare.T (q+r) := by
    change Fintype.card (TransOn ((SquareOn.fromFin (maximizingSquare (q+r))).transport
      finSumFinEquiv.symm)) = LatinSquare.T (q+r)
    exact (transport_transCount (SquareOn.fromFin (maximizingSquare (q+r)))
      (finSumFinEquiv (m := q) (n := r)).symm).trans (maximizingSquare_spec _)
  have hsome (i : Fin 3) : Fintype.card (TransOn (L (some i))) = LatinSquare.T q :=
    maximizingSquare_spec _
  have hdom : Fintype.card ((i : Option (Fin 3)) → TransOn (L i)) =
      (LatinSquare.T q)^3 * LatinSquare.T (q+r) := by
    rw [Fintype.card_pi, Fintype.prod_option]
    have inst_card (α : Type) (P Q : Fintype α) :
        @Fintype.card α P = @Fintype.card α Q :=
      congrArg (fun R => @Fintype.card α R) (Subsingleton.elim _ _)
    calc
      _ = LatinSquare.T (q+r) * ∏ _ : Fin 3, LatinSquare.T q := by
        apply congrArg₂ (fun x y : ℕ => x * y)
        · convert hnone using 1 <;> apply inst_card
        · apply Finset.prod_congr rfl
          intro i _
          convert hsome i using 1 <;> apply inst_card
      _ = _ := by simp [mul_comm]
  rw [hdom] at hc
  exact hc.trans (cast_count_ge (Q.onFin e))

lemma base_three : 3 ≤ LatinSquare.T 3 := by
  let w : Fin 3 → Fin 3 → Fin 3 := ![![0,1,2],![1,2,0],![2,0,1]]
  refine (explicit_count (cyclicSquare 3) w ?_ ?_).trans (cast_count_ge _)
  · decide +kernel
  · change ∀ i, Function.Injective (w i) ∧ Function.Injective (fun j => j+w i j)
    decide +kernel

lemma base_four : 8 ≤ LatinSquare.T 4 := by
  let w : Fin 8 → Fin 4 → Fin 4 :=
    ![![0,1,2,3],![0,2,3,1],![1,0,3,2],![1,3,2,0],![2,0,1,3],![2,3,0,1],![3,1,0,2],![3,2,1,0]]
  let L : LatinSquare 4 := ⟨smallSquare4.entry,smallSquare4.row,smallSquare4.col⟩
  exact (explicit_count L w (by decide +kernel) (by decide +kernel)).trans (cast_count_ge _)

lemma base_twelve : 1536 ≤ LatinSquare.T 12 := by
  have hp := product_transversal_bound 3 4 (by decide)
  exact (show 3 * 8^3 ≤ LatinSquare.T 3 * (LatinSquare.T 4)^3 from by gcongr <;> first | exact base_three | exact base_four).trans hp

lemma base_fifteen : 10125 ≤ LatinSquare.T 15 := by
  have hp := product_transversal_bound 3 5 (by decide)
  exact (show 3 * 15^3 ≤ LatinSquare.T 3 * (LatinSquare.T 5)^3 from by
    gcongr <;> first | exact base_three | exact base_cyclic_5).trans hp

lemma base_sixteen : 32768 ≤ LatinSquare.T 16 := by
  have hp := product_transversal_bound 4 4 (by decide)
  exact (show 8 * 8^4 ≤ LatinSquare.T 4 * (LatinSquare.T 4)^4 from by
    gcongr <;> exact base_four).trans hp

lemma base_eighteen : 52728 ≤ LatinSquare.T 18 := by
  have hp := product_transversal_bound 3 6 (by decide)
  exact (show 3 * 26^3 ≤ LatinSquare.T 3 * (LatinSquare.T 6)^3 from by
    gcongr <;> first | exact base_three | exact base_even_6).trans hp

lemma base_interval (n : ℕ) (hl : 5 ≤ n) (hu : n ≤ 19) :
    15 ^ n ≤ (LatinSquare.T n) ^ 5 := by
  have base {n t : ℕ} (h₁ : t ≤ LatinSquare.T n) (h₂ : 15 ^ n ≤ t ^ 5) :
      15 ^ n ≤ (LatinSquare.T n) ^ 5 :=
    h₂.trans (Nat.pow_le_pow_left h₁ 5)
  interval_cases n
  · exact base base_cyclic_5 (by decide +kernel)
  · exact base base_even_6 (by decide +kernel)
  · exact base base_cyclic_7 (by decide +kernel)
  · exact base base_even_8 (by decide +kernel)
  · exact base base_cyclic_9 (by decide +kernel)
  · exact base base_turn_10 (by decide +kernel)
  · exact base base_cyclic_11 (by decide +kernel)
  · exact base base_twelve (by decide +kernel)
  · exact base base_cyclic_13 (by decide +kernel)
  · exact base base_turn_14 (by decide +kernel)
  · exact base base_fifteen (by decide +kernel)
  · exact base base_sixteen (by decide +kernel)
  · exact base base_cyclic_17 (by decide +kernel)
  · exact base base_eighteen (by decide +kernel)
  · exact base base_cyclic_19 (by decide +kernel)

lemma four_bound_odd {q r : ℕ} (hq : Odd q) (hr : r ≤ q) :
    (LatinSquare.T q)^3 * LatinSquare.T (q+r) ≤ LatinSquare.T (4*q+r) := by
  haveI : NeZero q := ⟨by rintro rfl; norm_num at hq⟩
  let E (t : Fin r) : Equiv.Perm (Fin q) := Equiv.addRight (Fin.castLE hr t)
  apply four_bound (SquareOn.fromFin (cyclicSquare q)) E
  · intro x t u h
    apply Fin.ext
    have hh : Fin.castLE hr t = Fin.castLE hr u := add_left_cancel h
    exact congrArg (fun z : Fin q => z.val) hh
  · intro t
    refine ⟨(E t).injective, ?_⟩
    intro x y h
    apply double_injective hq
    change x + (x + Fin.castLE hr t) = y + (y + Fin.castLE hr t) at h
    simp only [← add_assoc] at h
    exact add_right_cancel h

def sixBase : Fin 3 → Fin 6 → Fin 6 :=
  ![![0,2,3,4,5,1],![1,3,2,5,4,0],![2,0,4,3,1,5]]

lemma four_bound_six (r : ℕ) (hr : r ≤ 3) :
    (LatinSquare.T 6)^3 * LatinSquare.T (6+r) ≤ LatinSquare.T (4*6+r) := by
  have hC : ∀ a : Fin 6, Function.Injective (fun t => sixBase t a) := by decide +kernel
  have hT : ∀ t, IsTransversal evenSquare6 (sixBase t) := by decide +kernel
  let E (t : Fin r) : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective (sixBase (Fin.castLE hr t)) ((hT _).1.bijective_of_finite)
  refine four_bound (SquareOn.fromFin evenSquare6) E ?_ ?_
  · intro a t u h
    change sixBase (Fin.castLE hr t) a = sixBase (Fin.castLE hr u) a at h
    have he : Fin.castLE hr t = Fin.castLE hr u := hC a h
    apply Fin.ext
    exact congrArg (fun z : Fin 3 => z.val) he
  · intro t
    exact hT (Fin.castLE hr t)

lemma lower_combine {n q r : ℕ} (hn : n = 4*q+r)
    (hq : 15^q ≤ (LatinSquare.T q)^5)
    (hr : 15^(q+r) ≤ (LatinSquare.T (q+r))^5)
    (hs : (LatinSquare.T q)^3 * LatinSquare.T (q+r) ≤ LatinSquare.T n) :
    15^n ≤ (LatinSquare.T n)^5 := by
  calc
    15^n = (15^q)^3 * 15^(q+r) := by rw [←pow_mul, ←pow_add]; congr 1; omega
    _ ≤ ((LatinSquare.T q)^5)^3 * (LatinSquare.T (q+r))^5 := by gcongr
    _ = ((LatinSquare.T q)^3 * LatinSquare.T (q+r))^5 := by
      rw [mul_pow, ←pow_mul, ←pow_mul]
    _ ≤ _ := Nat.pow_le_pow_left hs 5

lemma lower_natural (n : ℕ) (hn : 5 ≤ n) : 15^n ≤ (LatinSquare.T n)^5 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hbase : n ≤ 19
    · exact base_interval n hn hbase
    have aux (q r : ℕ) (hq : 5 ≤ q) (he : n = 4*q+r)
        (hT : (LatinSquare.T q)^3 * LatinSquare.T (q+r) ≤ LatinSquare.T (4*q+r)) :
        15^n ≤ (LatinSquare.T n)^5 :=
      lower_combine he (ih q (by omega) hq) (ih (q+r) (by omega) (by omega))
        (by simpa [he] using hT)
    by_cases hlarge : 28 ≤ n
    · let q := 2 * ((n-4)/8) + 1
      let r := n - 4*q
      have hq : 7 ≤ q := by dsimp [q]; omega
      have hq' : Odd q := ⟨(n-4)/8,by dsimp [q]⟩
      have hr : r ≤ q := by dsimp [r,q]; omega
      exact aux q r (by omega) (by dsimp [r,q]; omega) (four_bound_odd hq' hr)
    interval_cases n
    · exact aux 5 0 (by decide) rfl (four_bound_odd (by decide) (by decide))
    · exact aux 5 1 (by decide) rfl (four_bound_odd (by decide) (by decide))
    · exact aux 5 2 (by decide) rfl (four_bound_odd (by decide) (by decide))
    · exact aux 5 3 (by decide) rfl (four_bound_odd (by decide) (by decide))
    · exact aux 5 4 (by decide) rfl (four_bound_odd (by decide) (by decide))
    · exact aux 5 5 (by decide) rfl (four_bound_odd (by decide) (by decide))
    · exact aux 6 2 (by decide) rfl (four_bound_six 2 (by decide))
    · exact aux 6 3 (by decide) rfl (four_bound_six 3 (by decide))

lemma T_lower (n : ℕ) (hn : 5 ≤ n) :
    (15 : ℝ) ^ ((n : ℝ) / 5) ≤ (LatinSquare.T n : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (show (5 : ℕ) ≠ 0 by decide)).mp
  rw [←Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 15),
    show ((n : ℝ) / 5 * (5 : ℕ)) = n by norm_num [div_mul_cancel₀],
    Real.rpow_natCast]
  exact_mod_cast lower_natural n hn


open Finset Real

noncomputable def constant : ℝ := Real.sqrt ((3 - Real.sqrt 3) / 6) * Real.exp (Real.sqrt 3 / 6)

noncomputable def availableMean (n j : ℕ) : ℝ := 1 + (↑(j * (j - 1)) : ℝ) / ((n : ℝ) - 2)

noncomputable def ratio (n : ℕ) : ℝ :=
  ∏ j ∈ range n, availableMean n j / (j + 1 : ℝ)

lemma mean_pos (n j : ℕ) (hn : 3 ≤ n) : 0 < availableMean n j := by
  unfold availableMean
  have hlt : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have h : (0 : ℝ) < (n : ℝ) - 2 := sub_pos.mpr hlt
  positivity

lemma ratio_pos (n : ℕ) (hn : 3 ≤ n) : 0 < ratio n := by
  exact Finset.prod_pos fun j _ => div_pos (mean_pos n j hn) (by positivity)

lemma ratio_mul_factorial (n : ℕ) :
    ratio n * n.factorial = ∏ j ∈ range n, availableMean n j := by
  unfold ratio
  have h : ∏ j ∈ range n, (j + 1 : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  rw [Finset.prod_div_distrib, h, div_mul_cancel₀ _ (by positivity)]

lemma constant_gt : (61 / 100 : ℝ) < constant := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs' := Real.sqrt_nonneg (3 : ℝ)
  have hl : (1732 / 1000 : ℝ) ≤ Real.sqrt 3 := by nlinarith
  have hu : Real.sqrt (3 : ℝ) ≤ 1733 / 1000 := by nlinarith
  have hroot : (459 / 1000 : ℝ) ≤ Real.sqrt ((3 - Real.sqrt 3) / 6) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have he : (1330 / 1000 : ℝ) ≤ Real.exp (Real.sqrt 3 / 6) := by
    have hm : Real.exp ((1732 / 1000 : ℝ) / 6) ≤ Real.exp (Real.sqrt 3 / 6) :=
      Real.exp_le_exp.mpr (by linarith)
    refine le_trans ?_ hm
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (1732 / 1000 : ℝ) / 6) 3
    norm_num [Finset.sum_range_succ] at hsum ⊢
    linarith
  unfold constant
  nlinarith [mul_nonneg (sub_nonneg.mpr hroot) (sub_nonneg.mpr he)]

lemma exp_neg_bound : Real.exp (-(9 / 16 : ℝ)) ≤ 61 / 100 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (9 / 16 : ℝ)) 3
  norm_num [Finset.sum_range_succ] at hsum ⊢
  linarith

lemma mean_last (n : ℕ) (hn : 3 ≤ n) :
    availableMean (n + 1) n = (n : ℝ) + 1 := by
  unfold availableMean
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_add, Nat.cast_one]
  have h : (n : ℝ) - 1 ≠ 0 := by
    have ht : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  rw [show (n : ℝ) + 1 - 2 = (n : ℝ) - 1 by ring]
  rw [mul_div_cancel_right₀ _ h]
  ring

lemma mean_ratio (n j : ℕ) (hn : 3 ≤ n) :
    availableMean (n + 1) j / availableMean n j =
      ((n : ℝ) - 2) / ((n : ℝ) - 1) *
        (1 + 1 / ((n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ))) := by
  unfold availableMean
  rw [Nat.cast_add, Nat.cast_one]
  have h : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have h₁ : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h₂ : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have ha : (0 : ℝ) ≤ (↑(j * (j - 1)) : ℝ) := by positivity
  have h₃ : (0 : ℝ) < (n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ) := by linarith
  have h₄ : (0 : ℝ) < 1 + (↑(j * (j - 1)) : ℝ) / ((n : ℝ) - 2) := by positivity
  have h₅ : (n : ℝ) + 1 - 2 = (n : ℝ) - 1 := by ring
  rw [h₅]
  field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne']
  <;> ring

lemma reciprocal_sum (n : ℕ) (hn : 64 ≤ n) :
    (∑ j ∈ range n, (1 : ℝ) / ((n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ))) ≤
      7 * n / (16 * ((n : ℝ) - 2)) := by
  have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
  let m := n / 4
  have hm : m ≤ n := by dsimp [m]; omega
  have hm' : (m : ℝ) ≤ (n : ℝ) / 4 := by
    have h : 4 * m ≤ n := by dsimp [m]; omega
    have h' : 4 * (m : ℝ) ≤ n := by exact_mod_cast h
    linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  let a (j : ℕ) : ℝ := 1 / ((n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ))
  have ha (j : ℕ) : a j ≤ 1 / ((n : ℝ) - 2) := by
    apply one_div_le_one_div_of_le hn2
    exact le_add_of_nonneg_right (by positivity)
  have hb (j : ℕ) (hj : m ≤ j) : a j ≤ 1 / (4 * ((n : ℝ) - 2)) := by
    apply one_div_le_one_div_of_le (by positivity)
    have hj' : 1 ≤ j := by dsimp [m] at hj; omega
    rw [Nat.cast_mul, Nat.cast_sub hj', Nat.cast_one]
    have hj'' : (n : ℝ) / 4 - 1 ≤ j := by
      have ht : n ≤ 4 * j + 3 := by dsimp [m] at hj; omega
      have ht' : (n : ℝ) ≤ 4 * (j : ℝ) + 3 := by exact_mod_cast ht
      linarith
    have h₁ : (n : ℝ) / 4 - 1 ≤ j := hj''
    have h₂ : (n : ℝ) / 4 - 2 ≤ j - 1 := by linarith
    have hprod := mul_le_mul h₁ h₂ (by linarith) (by linarith : (0 : ℝ) ≤ j)
    have hsq := sq_nonneg ((n : ℝ) - 64)
    nlinarith
  change ∑ j ∈ range n, a j ≤ _
  have hnm : m + (n - m) = n := by omega
  conv_lhs => rw [← hnm, Finset.sum_range_add]
  calc
    _ ≤ (m : ℝ) * (1 / ((n : ℝ) - 2)) + ((n - m : ℕ) : ℝ) * (1 / (4 * ((n : ℝ) - 2))) := by
      apply add_le_add
      · simpa using (Finset.sum_le_sum fun j (_ : j ∈ range m) => ha j)
      · simpa using (Finset.sum_le_sum fun j (_ : j ∈ range (n - m)) => hb (m + j) (by omega))
    _ ≤ _ := by
      rw [Nat.cast_sub hm]
      field_simp
      linarith

lemma ratio_step (n : ℕ) (hn : 64 ≤ n) :
    ratio (n + 1) ≤ (61 / 100 : ℝ) * ratio n := by
  let a (j : ℕ) : ℝ := availableMean n j
  let b (j : ℕ) : ℝ := availableMean (n + 1) j
  have h : 3 ≤ n := by omega
  have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have ha (j : ℕ) : 0 < a j := mean_pos n j h
  have hb (j : ℕ) : 0 < b j := mean_pos _ _ (by omega)
  have hp : 0 < ratio n := ratio_pos _ h
  have heq : ratio (n + 1) / ratio n = ∏ j ∈ range n, b j / a j := by
    unfold ratio
    rw [Finset.prod_range_succ, mean_last n h, div_self (by positivity), mul_one,
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    dsimp [a,b]
    have hja := ha j
    field_simp
  apply (div_le_iff₀ hp).mp
  calc
    ratio (n + 1) / ratio n = _ := heq
    _ ≤ Real.exp (-(9 / 16 : ℝ)) := by
      have hab (j : ℕ) : 0 < b j / a j := div_pos (hb _) (ha _)
      rw [← Real.log_le_log_iff (Finset.prod_pos (fun j _ => hab j)) (Real.exp_pos _),
        Real.log_exp, Real.log_prod (fun j _ => (hab j).ne')]
      have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
      have hd : (0 : ℝ) < ((n : ℝ) - 2) / ((n : ℝ) - 1) := by positivity
      have hterm j :
          Real.log (b j / a j) ≤ -(1 : ℝ) / ((n : ℝ) - 1) +
            (1 : ℝ) / ((n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ)) := by
        change Real.log (availableMean (n + 1) j / availableMean n j) ≤ _
        have hdj : (0 : ℝ) < (n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ) := by positivity
        rw [mean_ratio n j h, Real.log_mul hd.ne' (by positivity)]
        apply add_le_add
        · have hv := Real.log_le_sub_one_of_pos hd
          have hh : ((n : ℝ) - 2) / ((n : ℝ) - 1) - 1 = -(1 : ℝ) / ((n : ℝ) - 1) := by
            field_simp [hn1.ne']; ring
          exact hh ▸ hv
        · have hv := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < 1 + 1 / ((n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ)) by positivity)
          linarith
      calc
        _ ≤ ∑ j ∈ range n, (-(1 : ℝ) / ((n : ℝ) - 1) +
            (1 : ℝ) / ((n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ))) :=
          Finset.sum_le_sum fun j _ => hterm j
        _ ≤ _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hs := reciprocal_sum n hn
          have ht : (n : ℝ) * (-(1 : ℝ) / ((n : ℝ) - 1)) +
                          7 * n / (16 * ((n : ℝ) - 2)) ≤ -(9 / 16 : ℝ) := by
            apply (mul_le_mul_iff_right₀ (mul_pos hn1 hn2)).mp
            field_simp [hn1.ne', hn2.ne']
            <;> nlinarith
          linarith
    _ ≤ _ := exp_neg_bound

def meanNumerator (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => meanNumerator n j * (n - 2 + j * (j - 1))

lemma cast_meanNumerator (n k : ℕ) (hn : 3 ≤ n) :
    (meanNumerator n k : ℝ) = ∏ j ∈ range k, ((n : ℝ) - 2 + (↑(j * (j - 1)) : ℝ)) := by
  induction k with
  | zero => simp [meanNumerator]
  | succ k ih => simp [meanNumerator, Finset.prod_range_succ, ih, Nat.cast_sub (by omega : 2 ≤ n)]

lemma prod_availableMean (n : ℕ) (hn : 3 ≤ n) :
    (∏ j ∈ range n, availableMean n j) = (meanNumerator n n : ℝ) / ((n : ℝ) - 2) ^ n := by
  have hn2 : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hp : ∏ _j ∈ range n, ((n : ℝ) - 2) = ((n : ℝ) - 2) ^ n := by simp
  rw [cast_meanNumerator n n hn, ← hp, ← Finset.prod_div_distrib]
  apply prod_congr rfl
  intro j hj
  unfold availableMean
  rw [add_div, div_self (sub_ne_zero.mpr (ne_of_gt hn2))]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma small_rat_certificate (n : ℕ) (hl : 6 ≤ n) (hu : n ≤ 64) :
    meanNumerator n n ^ 2 * 100 ^ (2 * n) ≤
      61 ^ (2 * n) * n * n.factorial ^ 2 * (n - 2) ^ (2 * n) := by
  interval_cases n <;> decide +kernel

lemma small_ratio (n : ℕ) (hl : 6 ≤ n) (hu : n ≤ 64) :
    ratio n ≤ (61 / 100 : ℝ) ^ n * Real.sqrt n := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    exact sub_pos.mpr (by exact_mod_cast (show 2 < n by omega))
  have hfactorial : (0 : ℝ) < n.factorial := by positivity
  apply (mul_le_mul_iff_left₀ hfactorial).mp
  rw [ratio_mul_factorial, prod_availableMean n (by omega)]
  rw [div_le_iff₀ (pow_pos hn2 n)]
  apply le_of_sq_le_sq _ (by positivity)
  have hcert := (Nat.cast_le (α := ℝ)).mpr (small_rat_certificate n hl hu)
  push_cast [Nat.cast_sub (show 2 ≤ n by omega)] at hcert
  have hc : (0 : ℝ) < 100 ^ (2 * n) := by positivity
  have hsp :
      (meanNumerator n n : ℝ) ^ 2 ≤
      (61 ^ (2 * n) * (n : ℝ) * (n.factorial : ℝ) ^ 2 * ((n : ℝ) - 2) ^ (2 * n)) /
        100 ^ (2 * n) := (le_div_iff₀ hc).mpr hcert
  refine hsp.trans_eq ?_
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hn, ← pow_mul, ← pow_mul]
  rw [div_pow, Nat.mul_comm n 2]
  ring

lemma ratio_le (n : ℕ) (hn : 6 ≤ n) :
    ratio n ≤ (61 / 100 : ℝ) ^ n * Real.sqrt n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 64
    · exact small_ratio n hn hsmall
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      have hstep := ratio_step k (by omega)
      have hprev := ih k (by omega) (by omega)
      have hs : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) := by
        gcongr
        omega
      calc
        _ ≤ (61 / 100 : ℝ) * ratio k := hstep
        _ ≤ (61 / 100 : ℝ) * ((61 / 100 : ℝ) ^ k * Real.sqrt k) :=
          mul_le_mul_of_nonneg_left hprev (by norm_num)
        _ ≤ _ := by
          rw [pow_succ']
          rw [mul_assoc]
          gcongr

lemma mean_product_bound (n : ℕ) (hn : 6 ≤ n) :
    (∏ j ∈ range n, availableMean n j) ≤ constant ^ n * Real.sqrt n * n.factorial := by
  rw [← ratio_mul_factorial]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  refine (ratio_le n hn).trans ?_
  gcongr
  exact constant_gt.le



open Finset

noncomputable def fiveSymbols (L : LatinSquare 5) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (L.mat 0) (L.row_injective 0).bijective_of_finite

noncomputable def fiveRows (L : LatinSquare 5) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (fun i => (fiveSymbols L).symm (L.mat i 0))
    (((fiveSymbols L).symm.injective.comp (L.col_injective 0)).bijective_of_finite)

noncomputable def reducedFive (L : LatinSquare 5) : LatinSquare 5 :=
  let s := fiveSymbols L
  let p := fiveRows L
  { mat := fun i j => s.symm (L.mat (p.symm i) j)
    row_injective := fun i => s.symm.injective.comp (L.row_injective (p.symm i))
    col_injective := fun j => s.symm.injective.comp ((L.col_injective j).comp p.symm.injective) }

lemma reducedFive_row (L : LatinSquare 5) (i : Fin 5) :
    (reducedFive L).mat 0 i = i := by
  let s := fiveSymbols L
  let p := fiveRows L
  have hp : p 0 = 0 := by
    change s.symm (s 0) = 0
    simp
  have hp' : p.symm 0 = 0 := by simpa using congrArg p.symm hp.symm
  change s.symm (L.mat (p.symm 0) i) = i
  rw [hp']
  change s.symm (s i) = i
  simp

lemma reducedFive_col (L : LatinSquare 5) (i : Fin 5) :
    (reducedFive L).mat i 0 = i := by
  change (fiveRows L) ((fiveRows L).symm i) = i
  simp

lemma reducedFive_ge (L : LatinSquare 5) :
    numTransversals L ≤ numTransversals (reducedFive L) := by
  let s : Equiv.Perm (Fin 5) := Equiv.ofBijective (L.mat 0) ⟨L.row_injective 0,
    Finite.injective_iff_surjective.mp (L.row_injective 0)⟩
  let p : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i => s.symm (L.mat i 0))
    ((s.symm.injective.comp (L.col_injective 0)).bijective_of_finite)
  let F :
      {f : Fin 5 → Fin 5 // IsTransversal L f} →
      {f : Fin 5 → Fin 5 // IsTransversal (reducedFive L) f} :=
    fun f => ⟨f.val ∘ p.symm, f.property.1.comp p.symm.injective,
      s.symm.injective.comp (f.property.2.comp p.symm.injective)⟩
  apply Fintype.card_le_of_injective F
  intro a b h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun f : {f : Fin 5 → Fin 5 // IsTransversal (reducedFive L) f} =>
    f.val (p i)) h
  simpa [F] using hi

def selectorsFive : Finset (Equiv.Perm (Fin 5)) := (@fintypePerm (Fin 5) _).elems

def rowFiveCandidates (i : Fin 5) : Finset (Equiv.Perm (Fin 5)) :=
  selectorsFive.filter fun p => p 0 = i ∧ ∀ j : Fin 5, p j ≠ j

def compatibleFive (p q : Equiv.Perm (Fin 5)) : Prop :=
  ∀ j : Fin 5, p j ≠ q j

instance (p q : Equiv.Perm (Fin 5)) : Decidable (compatibleFive p q) :=
  inferInstanceAs (Decidable (∀ j : Fin 5, p j ≠ q j))

def selectedFive (mat : Fin 5 → Fin 5 → Fin 5) : Finset (Equiv.Perm (Fin 5)) :=
  selectorsFive.filter fun p => Function.Injective (fun i => mat i (p i))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
lemma five_certificate :
    ∀ p : {p // p ∈ rowFiveCandidates 1},
      ∀ q : {q // q ∈ rowFiveCandidates 2}, compatibleFive p.val q.val →
      ∀ r : {r // r ∈ rowFiveCandidates 3},
        compatibleFive p.val r.val → compatibleFive q.val r.val →
      ∀ s : {s // s ∈ rowFiveCandidates 4},
        compatibleFive p.val s.val → compatibleFive q.val s.val → compatibleFive r.val s.val →
        (selectedFive ![id, p.val, q.val, r.val, s.val]).card ≤ 22 := by
  decide +kernel

lemma selectedFive_eq (L : LatinSquare 5) :
    numTransversals L = (selectedFive L.mat).card := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  let equivTrans (f : {f : Fin 5 → Fin 5 // IsTransversal L f}) : Equiv.Perm (Fin 5) :=
    Equiv.ofBijective f.val f.property.1.bijective_of_finite
  refine
    { toFun := fun f => ⟨equivTrans f, ?_⟩
      invFun := fun p => ⟨p.val, p.val.injective, (mem_filter.mp p.property).2⟩
      left_inv := fun f => rfl
      right_inv := fun p => Subtype.ext (Equiv.ext fun _ => rfl) }
  exact mem_filter.mpr ⟨(@fintypePerm (Fin 5) _).complete _, f.property.2⟩

lemma five_per_square (L : LatinSquare 5) : numTransversals L ≤ 22 := by
  let K := reducedFive L
  refine (reducedFive_ge L).trans ?_
  change numTransversals K ≤ 22
  rw [selectedFive_eq K]
  let rows (i : Fin 5) : Equiv.Perm (Fin 5) :=
    Equiv.ofBijective (K.mat i) (K.row_injective i).bijective_of_finite
  have hc (i : Fin 5) (hi : i ≠ 0) : rows i ∈ rowFiveCandidates i := by
    apply mem_filter.mpr
    refine ⟨(@fintypePerm (Fin 5) _).complete _, reducedFive_col L i, ?_⟩
    intro j he
    apply hi
    apply K.col_injective j
    change K.mat i j = K.mat 0 j
    exact he.trans (reducedFive_row L j).symm
  have hd (i j : Fin 5) (h : i ≠ j) : compatibleFive (rows i) (rows j) :=
    fun c => (K.col_injective c).ne h
  have he : K.mat = ![id, rows 1, rows 2, rows 3, rows 4] := by
    funext i j
    fin_cases i
    · exact reducedFive_row L j
    · rfl
    · rfl
    · rfl
    · rfl
  rw [he]
  exact five_certificate ⟨rows 1,hc 1 (by decide)⟩ ⟨rows 2,hc 2 (by decide)⟩
    (hd 1 2 (by decide)) ⟨rows 3,hc 3 (by decide)⟩
    (hd 1 3 (by decide)) (hd 2 3 (by decide)) ⟨rows 4,hc 4 (by decide)⟩
    (hd 1 4 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))



open Finset

abbrev Transversal {n : ℕ} (L : LatinSquare n) :=
  {σ : Fin n → Fin n // IsTransversal L σ}

def choices {n : ℕ} (L : LatinSquare n) (σ : Fin n → Fin n)
    (S : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun c => ∀ j ∈ S, c ≠ σ j ∧ L.mat i c ≠ L.mat j (σ j)

lemma choices_congr {n : ℕ} (L : LatinSquare n) {σ τ : Fin n → Fin n}
    {S : Finset (Fin n)} (h : ∀ j ∈ S, σ j = τ j) (i : Fin n) :
    choices L σ S i = choices L τ S i := by
  ext c
  simp only [choices, mem_filter, mem_univ, true_and]
  constructor <;> intro hc j hj
  · rw [← h j hj]
    exact hc j hj
  · rw [h j hj]
    exact hc j hj

lemma transversal_choice {n : ℕ} {L : LatinSquare n}
    (σ : Transversal L) {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    σ.val i ∈ choices L σ.val S i := by
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  intro j hj
  have hji : i ≠ j := fun e => hi (e ▸ hj)
  exact ⟨σ.property.1.ne hji, σ.property.2.ne hji⟩

noncomputable def prefixWeight {n : ℕ} (L : LatinSquare n)
    (σ : Fin n → Fin n) (S : Finset (Fin n)) : List (Fin n) → ℝ
  | [] => 1
  | i :: rest => ((choices L σ S i).card : ℝ)⁻¹ * prefixWeight L σ (insert i S) rest

def completions {n : ℕ} (L : LatinSquare n) (σ : Fin n → Fin n)
    (S : Finset (Fin n)) : Finset (Transversal L) :=
  univ.filter fun τ => ∀ j ∈ S, τ.val j = σ j

lemma mem_completions {n : ℕ} {L : LatinSquare n} {σ : Fin n → Fin n}
    {S : Finset (Fin n)} {τ : Transversal L} :
    τ ∈ completions L σ S ↔ ∀ j ∈ S, τ.val j = σ j := by
  simp [completions]

lemma mass_le_one {n : ℕ} (L : LatinSquare n) (rows : List (Fin n))
    (S : Finset (Fin n)) (σ : Fin n → Fin n) (hrows : rows.Nodup)
    (hdisj : ∀ j ∈ rows, j ∉ S) (hcover : ∀ j, j ∈ S ∨ j ∈ rows) :
    ∑ τ ∈ completions L σ S, prefixWeight L τ.val S rows ≤ 1 := by
  induction rows generalizing S σ with
  | nil =>
    simp only [prefixWeight, sum_const, nsmul_eq_mul, mul_one, Nat.cast_le_one]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply Subtype.ext
    funext j
    have hj : j ∈ S := (hcover j).resolve_right (by simp)
    exact (mem_completions.mp ha j hj).trans (mem_completions.mp hb j hj).symm
  | cons i rows ih =>
    have hi : i ∉ S := hdisj _ (by simp)
    let C := choices L σ S i
    let G := completions L σ S
    have hmap : ∀ τ ∈ G, τ.val i ∈ C := by
      intro τ hτ
      dsimp [C]
      rw [← choices_congr L (mem_completions.mp hτ)]
      exact transversal_choice τ hi
    calc
      _ = ∑ c ∈ C, ∑ τ ∈ G.filter (fun τ => τ.val i = c), prefixWeight L τ.val S (i :: rows) :=
        (Finset.sum_fiberwise_of_maps_to hmap (fun τ => prefixWeight L τ.val S (i :: rows))).symm
      _ ≤ ∑ c ∈ C, ((C.card : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro c hc
        let σ' : Fin n → Fin n := Function.update σ i c
        have hf : G.filter (fun τ => τ.val i = c) = completions L σ' (insert i S) := by
          ext τ
          simp only [G, mem_filter, mem_completions, mem_insert]
          constructor
          · rintro ⟨hτ, hiτ⟩ j (rfl | hj)
            · simpa [σ'] using hiτ
            · have hji : j ≠ i := fun e => hi (e ▸ hj)
              simpa [σ', Function.update_of_ne hji] using hτ j hj
          · intro hτ
            refine ⟨fun j hj => ?_, ?_⟩
            · have hji : j ≠ i := fun e => hi (e ▸ hj)
              simpa [σ', Function.update_of_ne hji] using hτ j (Or.inr hj)
            · simpa [σ'] using hτ i (Or.inl rfl)
        have hw : ∀ τ ∈ G.filter (fun τ => τ.val i = c),
            prefixWeight L τ.val S (i :: rows) =
              (C.card : ℝ)⁻¹ * prefixWeight L τ.val (insert i S) rows := by
          intro τ hτ
          rw [prefixWeight, choices_congr L (mem_completions.mp (mem_filter.mp hτ).1)]
        rw [Finset.sum_congr rfl hw, ← Finset.mul_sum, hf]
        refine mul_le_of_le_one_right (by positivity) (ih _ _ (List.nodup_cons.mp hrows).2 ?_ ?_)
        · intro j hj
          simp only [mem_insert, not_or]
          exact ⟨fun e => (List.nodup_cons.mp hrows).1 (e ▸ hj), hdisj _ (by simp [hj])⟩
        · intro j
          rcases hcover j with hj | hj
          · exact Or.inl (mem_insert_of_mem hj)
          · rcases List.mem_cons.mp hj with rfl | hh
            · exact Or.inl (mem_insert_self _ _)
            · exact Or.inr hh
      _ ≤ 1 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        by_cases hc : (C.card : ℝ) = 0
        · simp [hc]
        · simp [mul_inv_cancel₀ hc]


lemma avg_log_le {A : Type} (s : Finset A) (z : A → ℝ) (y : ℝ)
    (hy : 0 < y) (hz : ∀ a ∈ s, 0 < z a)
    (h : ∑ a ∈ s, z a ≤ (s.card : ℝ) * y) :
    ∑ a ∈ s, Real.log (z a) ≤ (s.card : ℝ) * Real.log y := by
  have hone (a) (ha : a ∈ s) :
      Real.log (z a) ≤ Real.log y + z a / y - 1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hz a ha) hy)
    rw [Real.log_div (hz a ha).ne' hy.ne'] at hh
    linarith
  calc
    _ ≤ ∑ a ∈ s, (Real.log y + z a / y - 1) :=
      sum_le_sum hone
    _ ≤ _ := by
      rw [sum_sub_distrib, sum_add_distrib, ← Finset.sum_div, sum_const, sum_const,
        nsmul_eq_mul, nsmul_eq_mul]
      have hY := (div_le_iff₀ hy).mpr h
      linarith

lemma prefixWeight_pos {n : ℕ} (L : LatinSquare n) (σ : Transversal L)
    (S : Finset (Fin n)) (rows : List (Fin n))
    (hrows : rows.Nodup) (hdisj : ∀ j ∈ rows, j ∉ S) :
    0 < prefixWeight L σ.val S rows := by
  induction rows generalizing S with
  | nil => simp [prefixWeight]
  | cons i rows ih =>
    have hi : i ∉ S := hdisj i (by simp)
    have hp : (0 : ℝ) < (choices L σ.val S i).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨σ.val i, transversal_choice σ hi⟩
    rw [prefixWeight]
    refine mul_pos (inv_pos.mpr hp) (ih _ (List.nodup_cons.mp hrows).2 ?_)
    intro j hj
    simp only [mem_insert, not_or]
    exact ⟨fun e => (List.nodup_cons.mp hrows).1 (e ▸ hj), hdisj _ (by simp [hj])⟩

lemma logPrefixWeight {n : ℕ} (L : LatinSquare n) (σ : Transversal L)
    (S : Finset (Fin n)) (rows : List (Fin n))
    (hrows : rows.Nodup) (hdisj : ∀ j ∈ rows, j ∉ S) :
    Real.log (prefixWeight L σ.val S rows) =
      -∑ i : Fin rows.length, Real.log
        ((choices L σ.val (S ∪ (rows.take i).toFinset) rows[i]).card : ℝ) := by
  induction rows generalizing S with
  | nil => simp [prefixWeight]
  | cons i rows ih =>
    have hi : i ∉ S := hdisj i (by simp)
    have hp : (0 : ℝ) < (choices L σ.val S i).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨σ.val i, transversal_choice σ hi⟩
    have hnew : ∀ j ∈ rows, j ∉ insert i S := by
      intro j hj
      simp only [mem_insert, not_or]
      exact ⟨fun e => (List.nodup_cons.mp hrows).1 (e ▸ hj), hdisj _ (by simp [hj])⟩
    have hrest := prefixWeight_pos L σ (insert i S) rows (List.nodup_cons.mp hrows).2 hnew
    rw [prefixWeight, Real.log_mul (inv_ne_zero hp.ne') hrest.ne', Real.log_inv,
      ih _ (List.nodup_cons.mp hrows).2 hnew]
    let f (k : Fin (rows.length+1)) : ℝ :=
      Real.log ((choices L σ.val (S ∪ ((i::rows).take k.val).toFinset) (i::rows)[k]).card : ℝ)
    change _ = -(∑ j, f j)
    rw [Fin.sum_univ_succ]
    have hs (T : Finset (Fin n)) : S ∪ insert i T = insert i S ∪ T := by
      ext j
      simp only [mem_union,mem_insert]
      tauto
    simp [f, List.take_succ_cons, hs, add_comm]

lemma completions_empty {n : ℕ} (L : LatinSquare n) (σ : Fin n → Fin n) :
    completions L σ ∅ = univ := by ext τ; simp [mem_completions]

lemma fixed_order_card {n : ℕ} (L : LatinSquare n) (rows : List (Fin n))
    (hrows : rows.Nodup) (hcover : ∀ i, i ∈ rows) :
    let N := Fintype.card (Transversal L)
    (N : ℝ) * Real.log N ≤
      ∑ σ : Transversal L, ∑ i : Fin rows.length,
        Real.log ((choices L σ.val (rows.take i).toFinset rows[i]).card : ℝ) := by
  classical
  let N := Fintype.card (Transversal L)
  change (N : ℝ) * Real.log N ≤ _
  by_cases hn : N = 0
  · have he : IsEmpty (Transversal L) := Fintype.card_eq_zero_iff.mp hn
    simp [hn]
  have hpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let f (σ : Transversal L) : ℝ := prefixWeight L σ.val ∅ rows
  have hm : ∑ σ, f σ ≤ 1 := by
    simpa [f, completions_empty L id] using
      mass_le_one L rows ∅ id hrows (by simp) (by simpa using hcover)
  have hr := avg_log_le (univ : Finset (Transversal L)) f ((N : ℝ)⁻¹)
        (inv_pos.mpr hpos) (fun σ _ => prefixWeight_pos L σ ∅ rows hrows (by simp))
        (by simpa [N, mul_inv_cancel₀ hpos.ne'] using hm)
  simp only [card_univ, ← show N = Fintype.card (Transversal L) from rfl, Real.log_inv,
    mul_neg, f] at hr
  simp only [logPrefixWeight L _ ∅ rows hrows (by simp), empty_union, sum_neg_distrib] at hr
  linarith

section Counting

open Equiv

lemma relabel_three {A : Type} [DecidableEq A] {a b c u v w : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ f : Perm A, f a = u ∧ f b = v ∧ f c = w := by
  let g := swap a u
  have ha : g a = u := swap_apply_left _ _
  let h := swap (g b) v
  have hb : h (g b) = v := swap_apply_left _ _
  have hu : h u = u := swap_apply_of_ne_of_ne
    (by simpa [ha] using g.injective.ne hab) huv
  let j := swap (h (g c)) w
  have hc : j (h (g c)) = w := swap_apply_left _ _
  have hu' : j u = u := swap_apply_of_ne_of_ne
    (by simpa [ha,hu] using (g.trans h).injective.ne hac) huw
  have hv' : j v = v := swap_apply_of_ne_of_ne
    (by simpa [hb] using (g.trans h).injective.ne hbc) hvw
  refine ⟨(g.trans h).trans j, ?_, ?_, hc⟩
  · change j (h (g a)) = u
    rw [ha,hu,hu']
  · change j (h (g b)) = v
    rw [hb,hv']

def afterRows {n : ℕ} (e : Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  (Ioi k).map e.toEmbedding

lemma mem_afterRows {n : ℕ} (e : Perm (Fin n)) (k i : Fin n) :
    i ∈ afterRows e k ↔ k < e.symm i := by
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_map.mp h
    simpa using hx
  · intro h
    exact mem_map.mpr ⟨e.symm i, mem_Ioi.mpr h, e.apply_symm_apply _⟩

def mark {n : ℕ} (k : Fin n) (e : Perm (Fin n)) (i j l : Fin n) : ℕ :=
  if e k = i ∧ j ∈ afterRows e k ∧ l ∈ afterRows e k then 1 else 0

lemma mark_sum_eq {n : ℕ} (k : Fin n) {a b c u v w : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (∑ e : Perm (Fin n), mark k e a b c) = ∑ e : Perm (Fin n), mark k e u v w := by
  obtain ⟨f,ha,hb,hc⟩ := relabel_three hab hac hbc huv huw hvw
  let F : Perm (Fin n) ≃ Perm (Fin n) :=
    { toFun := fun e => e.trans f
      invFun := fun e => e.trans f.symm
      left_inv := fun e => by ext x; simp
      right_inv := fun e => by ext x; simp }
  rw [← F.sum_comp (fun e => mark k e u v w)]
  apply sum_congr rfl
  intro e _
  rw [← ha, ← hb, ← hc]
  simp only [mark, mem_afterRows, F, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.symm_apply_apply, f.injective.eq_iff]

lemma mark_sum_fixed {n : ℕ} (e : Perm (Fin n)) (k : Fin n) :
    (∑ i : Fin n, ∑ pair ∈ ((univ : Finset (Fin n)).erase i).offDiag,
      mark k e i pair.1 pair.2) = (n - 1 - k.val) * (n - 1 - k.val - 1) := by
  let P := afterRows e k
  have hPi : e k ∉ P := by simp [P, mem_afterRows]
  rw [Finset.sum_eq_single (e k)]
  · have hed :
        (((univ : Finset (Fin n)).erase (e k)).offDiag).filter
            (fun pair => pair.1 ∈ P ∧ pair.2 ∈ P) = P.offDiag := by
      ext pair
      simp only [mem_filter, mem_offDiag, mem_erase, mem_univ, and_true]
      constructor
      · rintro ⟨⟨_, _, hd⟩,h₁,h₂⟩
        exact ⟨h₁,h₂,hd⟩
      · rintro ⟨h₁,h₂,hd⟩
        have hn (j : Fin n) (hj : j ∈ P) : j ≠ e k := fun h => hPi (h ▸ hj)
        exact ⟨⟨hn _ h₁, hn _ h₂, hd⟩, h₁, h₂⟩
    simp only [mark, true_and, P] at *
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, hed, offDiag_card]
    rw [afterRows, card_map, Fin.card_Ioi]
    let a := n - 1 - k.val
    change a * a - a = a * (a - 1)
    rw [Nat.mul_sub_left_distrib a a 1, mul_one]
  · intro j _ hj
    simp [mark, Ne.symm hj]
  · simp

lemma sum_flip {A B : Type} [Fintype A] [Fintype B] (s : A → Finset B)
    (f : A → B → (C → ℕ)) [Fintype C] :
    (∑ c : C, ∑ a : A, ∑ b ∈ s a, f a b c) =
      ∑ a : A, ∑ b ∈ s a, ∑ c : C, f a b c := by
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  exact sum_comm

lemma mark_eq_after {n : ℕ} (e : Perm (Fin n)) (k j l : Fin n) :
    mark k e (e k) j l = if j ∈ afterRows e k ∧ l ∈ afterRows e k then 1 else 0 := by
  simp [mark]

lemma mark_sum_identity {n : ℕ} (hn : 3 ≤ n) (k : Fin n)
    (u : Fin n → Fin n → Fin n) [NeZero n]
    (f g : Fin n → Fin n → Fin n)
    (h : ∀ i c, c ≠ u i i → i ≠ f i c ∧ i ≠ g i c ∧ f i c ≠ g i c) :
    (∑ e : Perm (Fin n), ∑ c ∈ (univ : Finset (Fin n)).erase (u (e k) (e k)),
      mark k e (e k) (f (e k) c) (g (e k) c)) * (n - 2) =
      Fintype.card (Perm (Fin n)) * ((n - 1 - k.val) * (n - 1 - k.val - 1)) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let H := ∑ e : Perm (Fin n), mark k e a b c
  have hconst {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
      (∑ e : Perm (Fin n), mark k e i j l) = H := by
    exact mark_sum_eq k hij hil hjl (by simp [a,b]) (by simp [a,c]) (by simp [b,c])
  have hn1 : 1 ≤ n := by omega
  have hcard (i : Fin n) : ((univ : Finset (Fin n)).erase i).offDiag.card =
      (n - 1) * (n - 2) := by
    rw [offDiag_card, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have he : n - 2 = n - 1 - 1 := by omega
    rw [he, Nat.mul_sub_left_distrib (n - 1) (n - 1) 1, mul_one]
  have hfull :
      (∑ e : Perm (Fin n), ∑ i : Fin n, ∑ pair ∈ ((univ : Finset (Fin n)).erase i).offDiag,
        mark k e i pair.1 pair.2) = n * ((n-1) * (n-2) * H) := by
    rw [sum_flip]
    calc
      _ = ∑ i : Fin n, ∑ pair ∈ ((univ : Finset (Fin n)).erase i).offDiag, H := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro pair hp
        have ⟨ha, hb, hh⟩ := mem_offDiag.mp hp
        exact hconst (mem_erase.mp ha).1.symm (mem_erase.mp hb).1.symm hh
      _ = _ := by simp [hcard, nsmul_eq_mul]
  have hmain := hfull
  simp only [mark_sum_fixed, sum_const, card_univ, nsmul_eq_mul] at hmain
  have hsub :
      (∑ e : Perm (Fin n), ∑ c ∈ (univ : Finset (Fin n)).erase (u (e k) (e k)),
        mark k e (e k) (f (e k) c) (g (e k) c)) = n * ((n - 1) * H) := by
    have he (e : Perm (Fin n)) :
        (∑ c ∈ (univ : Finset (Fin n)).erase (u (e k) (e k)),
          mark k e (e k) (f (e k) c) (g (e k) c)) =
          ∑ i : Fin n, ∑ c ∈ (univ : Finset (Fin n)).erase (u i i),
            mark k e i (f i c) (g i c) := by
      symm
      refine sum_eq_single (e k) ?_ (by simp)
      intro i _ hi
      simp [mark, ne_comm.mp hi]
    simp only [he]
    rw [sum_flip]
    calc
      _ = ∑ i : Fin n, ∑ c ∈ (univ : Finset (Fin n)).erase (u i i), H := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro c hc
        obtain ⟨h₁,h₂,h₃⟩ := h i c (mem_erase.mp hc).1
        exact hconst h₁ h₂ h₃
      _ = _ := by simp [nsmul_eq_mul, card_erase_of_mem (mem_univ _)]
  rw [hsub]
  have hm : Fintype.card (Perm (Fin n)) * ((n - 1 - k.val) * (n - 1 - k.val - 1)) =
      n * ((n-1) * (n-2) * H) := by exact_mod_cast hmain
  rw [hm]
  ring

noncomputable def colPermT {n : ℕ} (L : LatinSquare n) (t : Transversal L) : Perm (Fin n) :=
  Equiv.ofBijective t.val t.property.1.bijective_of_finite

noncomputable def symbolPermT {n : ℕ} (L : LatinSquare n) (t : Transversal L) : Perm (Fin n) :=
  Equiv.ofBijective (fun i => L.mat i (t.val i)) t.property.2.bijective_of_finite

noncomputable def colBlocker {n : ℕ} {L : LatinSquare n} (t : Transversal L) (c : Fin n) :=
  (colPermT L t).symm c

noncomputable def symbolBlocker {n : ℕ} {L : LatinSquare n} (t : Transversal L) (i c : Fin n) :=
  (symbolPermT L t).symm (L.mat i c)

lemma blocker_column {n : ℕ} {L : LatinSquare n} (t : Transversal L) (c : Fin n) :
    t.val (colBlocker t c) = c := (colPermT L t).apply_symm_apply c

lemma blocker_symbol {n : ℕ} {L : LatinSquare n} (t : Transversal L) (i c : Fin n) :
    L.mat (symbolBlocker t i c) (t.val (symbolBlocker t i c)) = L.mat i c :=
  (symbolPermT L t).apply_symm_apply _

lemma blockers_distinct {n : ℕ} {L : LatinSquare n} (t : Transversal L) (i c : Fin n)
    (hc : c ≠ t.val i) :
    i ≠ colBlocker t c ∧ i ≠ symbolBlocker t i c ∧
      colBlocker t c ≠ symbolBlocker t i c := by
  have h₁ := blocker_column t c
  have h₂ := blocker_symbol t i c
  have a : i ≠ colBlocker t c := by
    intro h
    rw [← h] at h₁
    exact hc h₁.symm
  have b : i ≠ symbolBlocker t i c := by
    intro h
    rw [← h] at h₂
    exact hc (L.row_injective i h₂).symm
  refine ⟨a,b,?_⟩
  intro h
  rw [← h,h₁] at h₂
  have he : colBlocker t c = i := L.col_injective c h₂
  exact a he.symm

def beforeRows {n : ℕ} (e : Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  (Iio k).map e.toEmbedding

lemma mem_beforeRows {n : ℕ} (e : Perm (Fin n)) (k i : Fin n) :
    i ∈ beforeRows e k ↔ e.symm i < k := by
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_map.mp h
    simpa using hx
  · intro h
    exact mem_map.mpr ⟨e.symm i, mem_Iio.mpr h, e.apply_symm_apply _⟩

lemma mem_choices_iff_blockers {n : ℕ} {L : LatinSquare n} (t : Transversal L)
    (e : Perm (Fin n)) (k : Fin n) (c : Fin n) (hc : c ≠ t.val (e k)) :
    c ∈ choices L t.val (beforeRows e k) (e k) ↔
      colBlocker t c ∈ afterRows e k ∧ symbolBlocker t (e k) c ∈ afterRows e k := by
  obtain ⟨h₁,h₂,_⟩ := blockers_distinct t (e k) c hc
  have h₁' : e.symm (colBlocker t c) ≠ k := by
    intro h
    have he := congrArg e h
    simp at he
    exact h₁ he.symm
  have h₂' : e.symm (symbolBlocker t (e k) c) ≠ k := by
    intro h
    have he := congrArg e h
    simp at he
    exact h₂ he.symm
  simp only [mem_afterRows]
  constructor
  · intro h
    obtain ⟨_,hh⟩ := mem_filter.mp h
    refine ⟨lt_of_le_of_ne (le_of_not_gt ?_) h₁'.symm,
      lt_of_le_of_ne (le_of_not_gt ?_) h₂'.symm⟩
    · intro hj
      exact (hh _ ((mem_beforeRows e k _).mpr hj)).1 (blocker_column t c).symm
    · intro hj
      exact (hh _ ((mem_beforeRows e k _).mpr hj)).2 (blocker_symbol t (e k) c).symm
  · rintro ⟨hcol,hsym⟩
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro j hj
    have hj' := (mem_beforeRows e k j).mp hj
    refine ⟨?_,?_⟩
    · intro h
      have h' : colBlocker t c = j := t.property.1 ((blocker_column t c).trans h)
      rw [h'] at hcol
      exact lt_asymm hcol hj'
    · intro h
      have h' : symbolBlocker t (e k) c = j :=
        t.property.2 ((blocker_symbol t (e k) c).trans h)
      rw [h'] at hsym
      exact lt_asymm hsym hj'

lemma choice_card_mark {n : ℕ} {L : LatinSquare n} (t : Transversal L)
    (e : Perm (Fin n)) (k : Fin n) :
    (choices L t.val (beforeRows e k) (e k)).card =
      1 + ∑ c ∈ (univ : Finset (Fin n)).erase (t.val (e k)),
        mark k e (e k) (colBlocker t c) (symbolBlocker t (e k) c) := by
  have hi : e k ∉ beforeRows e k := by simp [mem_beforeRows]
  have hc : t.val (e k) ∈ choices L t.val (beforeRows e k) (e k) := transversal_choice t hi
  have he :
      ((univ : Finset (Fin n)).erase (t.val (e k))).filter
        (fun c => colBlocker t c ∈ afterRows e k ∧ symbolBlocker t (e k) c ∈ afterRows e k) =
      (choices L t.val (beforeRows e k) (e k)).erase (t.val (e k)) := by
    ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true]
    exact and_congr_right (fun h => (mem_choices_iff_blockers t e k c h).symm)
  simp only [mark_eq_after]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, he, card_erase_of_mem hc]
  have hp := card_pos.mpr ⟨_,hc⟩
  change (choices L t.val (beforeRows e k) (e k)).card =
    1 + ((choices L t.val (beforeRows e k) (e k)).card - 1)
  omega

lemma mean_count {n : ℕ} {L : LatinSquare n} (t : Transversal L)
    (hn : 3 ≤ n) (k : Fin n) :
    (∑ e : Perm (Fin n), ((choices L t.val (beforeRows e k) (e k)).card : ℝ)) =
      (Fintype.card (Perm (Fin n)) : ℝ) *
        (1 + (↑((n - 1 - k.val) * (n - 1 - k.val - 1)) : ℝ) / ((n : ℝ) - 2)) := by
  letI : NeZero n := ⟨by omega⟩
  simp only [choice_card_mark t, Nat.cast_add, Nat.cast_one, sum_add_distrib,
    sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_sum]
  have ident := mark_sum_identity hn k (fun i _ => t.val i)
    (fun _ c => colBlocker t c) (symbolBlocker t)
    (blockers_distinct t)
  have hp := (Nat.cast_inj (R := ℝ)).mpr ident
  push_cast [Nat.cast_sub (show 2 ≤ n by omega)] at hp
  have hpos : (0 : ℝ) < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast (show 2 < n by omega))
  apply (mul_right_cancel₀ hpos.ne')
  rw [add_mul, mul_assoc, add_mul]
  rw [hp, div_mul_cancel₀ _ hpos.ne', one_mul]
  push_cast
  ring

end Counting

open Finset

lemma beforeRows_ofFn {n : ℕ} (e : Equiv.Perm (Fin n)) (k : Fin n) :
    (List.ofFn e |>.take k.val).toFinset = beforeRows e k := by
  ext i
  simp only [List.mem_toFinset, List.mem_take_iff_getElem, List.length_ofFn,
    List.getElem_ofFn, mem_beforeRows]
  constructor
  · rintro ⟨b,hb,hab⟩
    have hv := congrArg e.symm hab
    simp only [Equiv.symm_apply_apply] at hv
    have hb' := (lt_min_iff.mp hb).1
    rw [← hv]
    exact hb'
  · intro hi
    exact ⟨(e.symm i).val, lt_min_iff.mpr ⟨hi,(e.symm i).isLt⟩, e.apply_symm_apply i⟩

lemma log_weight_permutation {n : ℕ} (L : LatinSquare n) (e : Equiv.Perm (Fin n)) :
    let N := Fintype.card (Transversal L)
    (N : ℝ) * Real.log N ≤
      ∑ t : Transversal L, ∑ k : Fin n,
        Real.log ((choices L t.val (beforeRows e k) (e k)).card : ℝ) := by
  have h := fixed_order_card L (List.ofFn e) (List.nodup_ofFn.mpr e.injective)
    (fun i => List.mem_ofFn.mpr ⟨e.symm i,e.apply_symm_apply i⟩)
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro t _
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := e)))
  intro k
  let j : Fin n := finCongr (List.length_ofFn (f := e)) k
  have hg : (List.ofFn e)[k] = e j := by
    change (List.ofFn e)[k.val]'k.isLt = e j
    simp [j]
    apply Fin.ext
    rfl
  have hb : ((List.ofFn e).take k.val).toFinset = beforeRows e j :=
    beforeRows_ofFn e j
  rw [hg, hb]

lemma average_log_choices {n : ℕ} {L : LatinSquare n}
    (hn : 3 ≤ n) (t : Transversal L) (k : Fin n) :
    (∑ e : Equiv.Perm (Fin n), Real.log ((choices L t.val (beforeRows e k) (e k)).card : ℝ)) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
        Real.log (availableMean n (n-1-k.val)) := by
  apply avg_log_le
  · exact mean_pos _ _ hn
  · intro e _
    have hi : e k ∉ beforeRows e k := by simp [mem_beforeRows]
    exact_mod_cast Finset.card_pos.mpr ⟨t.val (e k),transversal_choice t hi⟩
  · simpa [availableMean] using (mean_count t hn k).le

lemma per_square_mean_product {n : ℕ} (hn : 3 ≤ n) (L : LatinSquare n) :
    (numTransversals L : ℝ) ≤ ∏ j ∈ range n, availableMean n j := by
  classical
  let N := Fintype.card (Transversal L)
  let P := Fintype.card (Equiv.Perm (Fin n))
  let f (t : Transversal L) (k : Fin n) (e : Equiv.Perm (Fin n)) : ℝ :=
    Real.log ((choices L t.val (beforeRows e k) (e k)).card : ℝ)
  let g (k : Fin n) : ℝ := Real.log (availableMean n (n-1-k.val))
  change (N : ℝ) ≤ _
  have hall := Finset.prod_pos (s := range n) (f := availableMean n)
    (fun j _ => mean_pos _ _ hn)
  by_cases hN : N = 0
  · simp [hN,hall.le]
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hP : (0 : ℝ) < P := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Equiv.Perm (Fin n))))
  have hu : (P : ℝ) * ((N : ℝ) * Real.log N) ≤ (P : ℝ) * ((N : ℝ) * ∑ k, g k) := by
    calc
      _ = ∑ _e : Equiv.Perm (Fin n), (N : ℝ) * Real.log N := by
        simp [P,nsmul_eq_mul]
      _ ≤ ∑ e : Equiv.Perm (Fin n), ∑ t : Transversal L, ∑ k : Fin n, f t k e :=
        sum_le_sum fun e _ => log_weight_permutation L e
      _ = ∑ t : Transversal L, ∑ k : Fin n, ∑ e : Equiv.Perm (Fin n), f t k e := by
        rw [sum_comm]
        apply sum_congr rfl
        intro t _
        exact sum_comm
      _ ≤ ∑ t : Transversal L, ∑ k : Fin n, (P : ℝ) * g k :=
        sum_le_sum fun t _ => sum_le_sum fun k _ => average_log_choices hn t k
      _ = _ := by simp [← Finset.mul_sum, nsmul_eq_mul, N, mul_assoc, mul_comm, mul_left_comm]
  have hh := (mul_le_mul_iff_right₀ hN').mp ((mul_le_mul_iff_right₀ hP).mp hu)
  apply (Real.log_le_log_iff hN' hall).mp
  rw [Real.log_prod (fun j _ => (mean_pos _ _ hn).ne')]
  refine hh.trans_eq ?_
  let g' (k : Fin n) : ℝ := Real.log (availableMean n k.val)
  calc
    _ = ∑ k : Fin n, g' (Fin.revPerm k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [g,g']
      congr 2
      rw [show ((Fin.revPerm k : Fin n) : ℕ) = n - (k.val + 1) from rfl]
      omega
    _ = ∑ k : Fin n, g' k := Equiv.sum_comp Fin.revPerm g'
    _ = _ := Fin.sum_univ_eq_sum_range (fun j => Real.log (availableMean n j)) n

lemma T_upper (n : ℕ) (hn : 5 ≤ n) :
    (LatinSquare.T n : ℝ) ≤ constant ^ n * Real.sqrt n * n.factorial := by
  have hsq (L : LatinSquare n) :
      (numTransversals L : ℝ) ≤ constant ^ n * Real.sqrt n * n.factorial := by
    by_cases h : 6 ≤ n
    · exact (per_square_mean_product (by omega) L).trans (mean_product_bound n h)
    · obtain rfl : n = 5 := by omega
      have hf : (numTransversals L : ℝ) ≤ 22 := by exact_mod_cast five_per_square L
      refine hf.trans ?_
      have hc : (0 : ℝ) ≤ constant := by linarith [constant_gt]
      have root : (223 / 100 : ℝ) ≤ Real.sqrt 5 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      have he : (22 : ℝ) ≤ (61 / 100 : ℝ) ^ 5 * (223 / 100 : ℝ) * (5 : ℕ).factorial := by norm_num
      refine he.trans ?_
      gcongr
      · exact constant_gt.le
      · exact_mod_cast root
  have hmax := hsq (maximizingSquare n)
  rw [maximizingSquare_spec] at hmax
  exact hmax

end LatinBound

theorem OMA.solution : type_of% @LatinSquare.maxTransversalsBound := by
  dsimp
  intro n hn
  exact ⟨LatinBound.T_lower n hn, LatinBound.T_upper n hn⟩
