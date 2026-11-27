import FormalConjectures.Paper.ClaudesCycles

-- Problem: Claude's Cycles — cube hamiltonian arc decomposition even
-- Upstream: formal-conjectures FormalConjectures/Paper/ClaudesCycles.lean:137 (declaration ClaudesCycles.cube_hamiltonian_arc_decomposition_even)
-- Credit: @iLc0 (the owner of the agent is credited as the solver)

/-!
# Claude's Cycles, cas pair : ossature

Méthode : certificat de position. Une application `f` d'un ensemble fini de cardinal `N` est un
seul cycle dès qu'il existe `pos : α → ZMod N` avec `pos (f a) = pos a + 1`.

* La règle n'est pas triviale que sur les fibres `-2` (table `A`) et `-1` (table `B`) ;
  la carte de retour `retOf A B c` sur la fibre 0 (coordonnées `(i, j)`) suffit
  (`pos3_of_pos2`, `decomp_of_certs`).
* `m = 4, 6` : tables d'Aquino-Michaels, certificats tabulés, `decide`.
* `m` pair `≥ 8` : règle de Ho (`hoA`, `hoB`), certificats `hoCert0/1/2` (preuve GPT26).
-/

namespace OMAClaude

open ClaudesCycles

/- ## 1. Certificat de position générique -/

/-- (L1) Si `pos (f a) = pos a + 1` dans `ZMod N`, `N = card α > 1`, alors `f` est un seul cycle
de support plein. -/
theorem cycle_of_pos {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) (N : ℕ) [NeZero N]
    (hN : Fintype.card α = N) (hN1 : 1 < N) (pos : α → ZMod N)
    (h : ∀ a, pos (f a) = pos a + 1) :
    ∃ σ : Equiv.Perm α, (∀ a, σ a = f a) ∧ σ.IsCycle ∧ σ.support = Finset.univ := by
  have : Fact (1 < N) := ⟨hN1⟩
  have hit : ∀ n : ℕ, ∀ a, pos (f^[n] a) = pos a + n := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', h, ih]
      push_cast; ring
  have hne : Nonempty α := by
    rw [← Fintype.card_pos_iff, hN]; omega
  obtain ⟨a0⟩ := hne
  have hsurj : Function.Surjective pos := by
    intro z
    refine ⟨f^[(z - pos a0).val] a0, ?_⟩
    rw [hit, ZMod.natCast_zmod_val]; ring
  have hbij : Function.Bijective pos := by
    rw [Fintype.bijective_iff_surjective_and_card]
    exact ⟨hsurj, by rw [hN, ZMod.card]⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply hbij.1
    have := congrArg pos hab
    rw [h, h] at this
    exact add_right_cancel this
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  have hmove : ∀ a, f a ≠ a := by
    intro a ha
    have h' := h a
    rw [ha] at h'
    exact one_ne_zero (by linear_combination h'.symm : (1 : ZMod N) = 0)
  refine ⟨Equiv.ofBijective f hfbij, fun a => rfl, ?_, ?_⟩
  · refine ⟨a0, hmove a0, ?_⟩
    intro y _
    refine ⟨((pos y - pos a0).val : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    apply hbij.1
    have e : (⇑(Equiv.ofBijective f hfbij))^[(pos y - pos a0).val] a0 =
        f^[(pos y - pos a0).val] a0 := rfl
    rw [e, hit, ZMod.natCast_zmod_val]; ring
  · ext y
    simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
    exact hmove y

/- ## 2. Les six permutations

Convention `abc` : la couleur 0 bumpe la coordonnée `a`, la couleur 1 la coordonnée `b`,
la couleur 2 la coordonnée `c`. -/

def p012 : Equiv.Perm (Fin 3) := 1
def p021 : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
def p102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
def p120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
def p201 : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
def p210 : Equiv.Perm (Fin 3) :=
  ⟨![2, 1, 0], ![2, 1, 0], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩

@[simp] theorem p012_apply (c : Fin 3) : p012 c = c := rfl
@[simp] theorem p021_0 : p021 0 = 0 := rfl
@[simp] theorem p021_1 : p021 1 = 2 := rfl
@[simp] theorem p021_2 : p021 2 = 1 := rfl
@[simp] theorem p102_0 : p102 0 = 1 := rfl
@[simp] theorem p102_1 : p102 1 = 0 := rfl
@[simp] theorem p102_2 : p102 2 = 2 := rfl
@[simp] theorem p120_0 : p120 0 = 1 := rfl
@[simp] theorem p120_1 : p120 1 = 2 := rfl
@[simp] theorem p120_2 : p120 2 = 0 := rfl
@[simp] theorem p201_0 : p201 0 = 2 := rfl
@[simp] theorem p201_1 : p201 1 = 0 := rfl
@[simp] theorem p201_2 : p201 2 = 1 := rfl
@[simp] theorem p210_0 : p210 0 = 2 := rfl
@[simp] theorem p210_1 : p210 1 = 1 := rfl
@[simp] theorem p210_2 : p210 2 = 0 := rfl

/- ## 3. Règle à deux couches et carte de retour -/

/-- Direction au sommet `v` : table `A` sur la fibre `-2`, table `B` sur la fibre `-1`,
identité ailleurs. Les tables sont lues sur les deux premières coordonnées. -/
def dirOf {m : ℕ} [NeZero m] (A B : ZMod m → ZMod m → Equiv.Perm (Fin 3)) (v : Vertex m) :
    Equiv.Perm (Fin 3) :=
  if v 0 + v 1 + v 2 = -2 then A (v 0) (v 1)
  else if v 0 + v 1 + v 2 = -1 then B (v 0) (v 1) else 1

/-- Le pas de couleur `c`. -/
def stepOf {m : ℕ} [NeZero m] (A B : ZMod m → ZMod m → Equiv.Perm (Fin 3)) (c : Fin 3)
    (v : Vertex m) : Vertex m :=
  bumpAt (dirOf A B v c) v

/-- Effet d'un pas de direction `d` sur les coordonnées `(i, j)` ; la troisième coordonnée
est implicite (`k = s - i - j`). -/
def mv {m : ℕ} [NeZero m] (d : Fin 3) (p : ZMod m × ZMod m) : ZMod m × ZMod m :=
  (if d = 0 then p.1 + 1 else p.1, if d = 1 then p.2 + 1 else p.2)

/-- Carte de retour de la couleur `c` sur la fibre 0, en coordonnées `(i, j)` : `m - 2` pas
triviaux (la coordonnée `c` perd 2), un pas sur la fibre `-2` (table `A`), un pas sur la fibre
`-1` (table `B`). -/
def retOf {m : ℕ} [NeZero m] (A B : ZMod m → ZMod m → Equiv.Perm (Fin 3)) (c : Fin 3)
    (p : ZMod m × ZMod m) : ZMod m × ZMod m :=
  let q : ZMod m × ZMod m := (if c = 0 then p.1 - 2 else p.1, if c = 1 then p.2 - 2 else p.2)
  let r := mv (A q.1 q.2 c) q
  mv (B r.1 r.2 c) r

/- ## 4. Relèvement aux fibres et assemblage -/

/-- Fibre d'un sommet. -/
def fib {m : ℕ} [NeZero m] (v : Vertex m) : ZMod m := v 0 + v 1 + v 2

/-- Projection sur les deux premières coordonnées. -/
def pr {m : ℕ} [NeZero m] (v : Vertex m) : ZMod m × ZMod m := (v 0, v 1)

/-- Point de la fibre 0 dont part la montée de couleur `c` qui atteint `v` (fibres basses). -/
def baseOf {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m) : ZMod m × ZMod m :=
  (if c = 0 then v 0 - fib v else v 0, if c = 1 then v 1 - fib v else v 1)

theorem fib_bumpAt {m : ℕ} [NeZero m] (d : Fin 3) (v : Vertex m) :
    fib (bumpAt d v) = fib v + 1 := by
  fin_cases d <;> simp [fib, bumpAt, ] <;> ring

theorem pr_bumpAt {m : ℕ} [NeZero m] (d : Fin 3) (v : Vertex m) :
    pr (bumpAt d v) = mv d (pr v) := by
  fin_cases d <;> simp [pr, mv, bumpAt, ]

theorem baseOf_bumpAt_self {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m) :
    baseOf c (bumpAt c v) = baseOf c v := by
  fin_cases c <;> simp [baseOf, fib, bumpAt, ] <;> ring

theorem val_eq_iff_eq_natCast {m : ℕ} [NeZero m] (x : ZMod m) (k : ℕ) (hk : k < m) :
    x.val = k ↔ x = (k : ZMod m) := by
  constructor
  · intro hx; rw [← hx, ZMod.natCast_zmod_val]
  · intro hx; rw [hx, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem lift_add_one {m : ℕ} [NeZero m] (hm : 1 < m) (x : ZMod (m ^ 2)) :
    ((m * (x + 1).val : ℕ) : ZMod (m ^ 3)) = ((m * x.val : ℕ) : ZMod (m ^ 3)) + m := by
  have h2 : 1 < m ^ 2 := Nat.one_lt_pow (by norm_num) hm
  have : Fact (1 < m ^ 2) := ⟨h2⟩
  rw [ZMod.val_add, ZMod.val_one]
  generalize ha : x.val + 1 = a
  have key := Nat.mod_add_div a (m ^ 2)
  have e : m * (a % m ^ 2) + m ^ 3 * (a / m ^ 2) = m * a := by
    conv_rhs => rw [← key]
    ring
  have e2 : ((m * (a % m ^ 2) : ℕ) : ZMod (m ^ 3)) = ((m * a : ℕ) : ZMod (m ^ 3)) := by
    rw [← e, Nat.cast_add, Nat.cast_mul (m ^ 3), ZMod.natCast_self, zero_mul, add_zero]
  rw [e2, ← ha]
  push_cast; ring

/-- (L2) GPT26, lemme 2, sous forme de certificat : un certificat de la carte de retour sur la
fibre 0 donne un certificat du pas sur tout le cube. -/
theorem pos3_of_pos2 {m : ℕ} [NeZero m] (hm : 2 < m)
    (A B : ZMod m → ZMod m → Equiv.Perm (Fin 3)) (c : Fin 3)
    (pos : ZMod m × ZMod m → ZMod (m ^ 2)) (h : ∀ p, pos (retOf A B c p) = pos p + 1) :
    ∃ pos3 : Vertex m → ZMod (m ^ 3), ∀ v, pos3 (stepOf A B c v) = pos3 v + 1 := by
  have hm1 : 1 < m := by omega
  have : Fact (1 < m) := ⟨hm1⟩
  have hneg2 : ∀ x : ZMod m, x = -2 ↔ x.val = m - 2 := by
    intro x
    rw [val_eq_iff_eq_natCast x (m - 2) (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
    constructor <;> intro hx <;> rw [hx] <;> ring
  have hneg1 : ∀ x : ZMod m, x = -1 ↔ x.val = m - 1 := by
    intro x
    rw [val_eq_iff_eq_natCast x (m - 1) (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
    constructor <;> intro hx <;> rw [hx] <;> ring
  have hfibdef : ∀ v : Vertex m, v 0 + v 1 + v 2 = fib v := fun v => rfl
  refine ⟨fun v => if (fib v).val + 2 ≤ m then
      ((m * (pos (baseOf c v)).val + (fib v).val : ℕ) : ZMod (m ^ 3))
      else ((m * (pos (pr (stepOf A B c v))).val : ℕ) : ZMod (m ^ 3)) - 1, ?_⟩
  intro v
  have ht := ZMod.val_lt (fib v)
  rcases (by omega : (fib v).val + 3 ≤ m ∨ (fib v).val = m - 2 ∨ (fib v).val = m - 1)
    with h1 | h1 | h1
  · -- fibres basses : pas trivial
    have hd : dirOf A B v = 1 := by
      unfold dirOf
      rw [hfibdef, if_neg, if_neg]
      · rw [hneg1]; omega
      · rw [hneg2]; omega
    have hs : stepOf A B c v = bumpAt c v := by simp [stepOf, hd]
    have hfv : (fib (bumpAt c v)).val = (fib v).val + 1 := by
      rw [fib_bumpAt, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, baseOf_bumpAt_self, hfv]
    rw [if_pos (by omega), if_pos (by omega)]
    push_cast; ring
  · -- fibre -2 : la montée s'achève par A puis B
    have hv2 : fib v = -2 := (hneg2 _).2 h1
    have hd : dirOf A B v = A (v 0) (v 1) := by
      unfold dirOf; rw [hfibdef, if_pos hv2]
    have hw' : stepOf A B c v = bumpAt (A (v 0) (v 1) c) v := by simp [stepOf, hd]
    have hfw : fib (stepOf A B c v) = -1 := by rw [hw', fib_bumpAt, hv2]; ring
    have hfwv : (fib (stepOf A B c v)).val = m - 1 := (hneg1 _).1 hfw
    have hdw : dirOf A B (stepOf A B c v) =
        B ((stepOf A B c v) 0) ((stepOf A B c v) 1) := by
      unfold dirOf
      rw [hfibdef, if_neg, if_pos hfw]
      rw [hfw]
      intro h12
      have : (1 : ZMod m) = 0 := by linear_combination h12
      exact one_ne_zero this
    have hq : ((if c = 0 then (baseOf c v).1 - 2 else (baseOf c v).1),
        (if c = 1 then (baseOf c v).2 - 2 else (baseOf c v).2)) = pr v := by
      fin_cases c <;> simp [baseOf, pr, hv2] <;> ring
    have hq1 : (if c = 0 then (baseOf c v).1 - 2 else (baseOf c v).1) = v 0 := by
      fin_cases c <;> simp [baseOf, hv2] <;> ring
    have hq2 : (if c = 1 then (baseOf c v).2 - 2 else (baseOf c v).2) = v 1 := by
      fin_cases c <;> simp [baseOf, hv2] <;> ring
    have hret : retOf A B c (baseOf c v) = pr (stepOf A B c (stepOf A B c v)) := by
      have hsw : stepOf A B c (stepOf A B c v) =
          bumpAt (B ((stepOf A B c v) 0) ((stepOf A B c v) 1) c) (stepOf A B c v) := by
        show bumpAt (dirOf A B (stepOf A B c v) c) (stepOf A B c v) = _
        rw [hdw]
      have hpw : pr (stepOf A B c v) = mv (A (v 0) (v 1) c) (pr v) := by rw [hw', pr_bumpAt]
      rw [hsw, pr_bumpAt]
      simp only [retOf]
      rw [hq1, hq2]
      have e0 : (stepOf A B c v) 0 = (pr (stepOf A B c v)).1 := rfl
      have e1 : (stepOf A B c v) 1 = (pr (stepOf A B c v)).2 := rfl
      rw [e0, e1, hpw]
      rfl
    simp only []
    rw [if_neg (by omega), if_pos (by omega), ← hret, h, lift_add_one hm1, h1]
    push_cast [Nat.cast_sub (by omega : 2 ≤ m)]
    ring
  · -- fibre -1 : le pas B ramène sur la fibre 0
    have hv1 : fib v = -1 := (hneg1 _).2 h1
    have hd : dirOf A B v = B (v 0) (v 1) := by
      unfold dirOf
      rw [hfibdef, if_neg, if_pos hv1]
      rw [hv1]
      intro h12
      have : (1 : ZMod m) = 0 := by linear_combination h12
      exact one_ne_zero this
    have hw' : stepOf A B c v = bumpAt (B (v 0) (v 1) c) v := by simp [stepOf, hd]
    have hfw : fib (stepOf A B c v) = 0 := by rw [hw', fib_bumpAt, hv1]; ring
    have hb : baseOf c (stepOf A B c v) = pr (stepOf A B c v) := by
      simp [baseOf, pr, hfw]
    simp only []
    rw [if_pos (by rw [hfw, ZMod.val_zero]; omega), if_neg (by omega), hb, hfw, ZMod.val_zero]
    push_cast; ring

/-- (L3) Assemblage : trois certificats de retour donnent la décomposition. -/
theorem decomp_of_certs {m : ℕ} [NeZero m] (hm : 2 < m)
    (A B : ZMod m → ZMod m → Equiv.Perm (Fin 3))
    (h : ∀ c : Fin 3, ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf A B c p) = pos p + 1) :
    HasHamiltonianArcDecomposition m := by
  have key : ∀ c : Fin 3, ∃ σ : Equiv.Perm (Vertex m), (∀ v, σ v = stepOf A B c v) ∧
      σ.IsCycle ∧ σ.support = Finset.univ := by
    intro c
    obtain ⟨pos, hpos⟩ := h c
    obtain ⟨pos3, hpos3⟩ := pos3_of_pos2 hm A B c pos hpos
    exact cycle_of_pos (stepOf A B c) (m ^ 3) (by simp)
      (Nat.one_lt_pow (by norm_num) (by omega)) pos3 hpos3
  choose σ hσ hcyc hsupp using key
  refine ⟨σ, fun c => ⟨fun v => ⟨dirOf A B v c, (hσ c v).symm⟩, hcyc c, hsupp c⟩, ?_⟩
  intro v b
  refine ⟨(dirOf A B v).symm b, ?_, ?_⟩
  · show σ ((dirOf A B v).symm b) v = bumpAt b v
    rw [hσ]
    show bumpAt (dirOf A B v ((dirOf A B v).symm b)) v = bumpAt b v
    rw [Equiv.apply_symm_apply]
  · intro c hc
    have hc1 : σ c v = bumpAt b v := hc
    rw [hσ] at hc1
    have hc' : bumpAt (dirOf A B v c) v = bumpAt b v := hc1
    have hdir : dirOf A B v c = b := bumpAt_injective (by omega) v hc'
    rw [← hdir, Equiv.symm_apply_apply]

/- ## 5. Petits cas `m = 4` et `m = 6` : tables d'Aquino-Michaels

Tables lues dans `residue/constructions/even_construction.py` (couches `m - 2` et `m - 1`,
identité sur les autres) ; certificats calculés par `calc/small.py`. -/

def smallA4 (i j : ZMod 4) : Equiv.Perm (Fin 3) :=
  ![![p012, p012, p102, p120],
    ![p021, p021, p210, p201],
    ![p021, p120, p021, p201],
    ![p102, p021, p021, p210]] i j
def smallB4 (i j : ZMod 4) : Equiv.Perm (Fin 3) :=
  ![![p201, p201, p201, p201],
    ![p102, p102, p102, p102],
    ![p102, p102, p102, p102],
    ![p201, p201, p201, p201]] i j
def pos4c0 (p : ZMod 4 × ZMod 4) : ZMod (4 ^ 2) :=
  ![![0, 14, 4, 11],
    ![8, 13, 3, 6],
    ![12, 2, 10, 15],
    ![1, 9, 5, 7]] p.1 p.2
def pos4c1 (p : ZMod 4 × ZMod 4) : ZMod (4 ^ 2) :=
  ![![0, 6, 3, 9],
    ![13, 4, 10, 7],
    ![11, 8, 1, 14],
    ![2, 15, 12, 5]] p.1 p.2
def pos4c2 (p : ZMod 4 × ZMod 4) : ZMod (4 ^ 2) :=
  ![![0, 1, 2, 3],
    ![5, 6, 7, 4],
    ![10, 11, 8, 9],
    ![13, 14, 12, 15]] p.1 p.2

def smallA6 (i j : ZMod 6) : Equiv.Perm (Fin 3) :=
  ![![p012, p012, p012, p012, p210, p102],
    ![p012, p012, p012, p012, p201, p210],
    ![p021, p021, p021, p120, p102, p021],
    ![p021, p021, p120, p021, p201, p021],
    ![p012, p102, p021, p021, p210, p012],
    ![p102, p012, p012, p012, p210, p012]] i j
def smallB6 (i j : ZMod 6) : Equiv.Perm (Fin 3) :=
  ![![p120, p120, p120, p120, p120, p120],
    ![p120, p120, p120, p120, p120, p120],
    ![p210, p210, p210, p210, p210, p210],
    ![p210, p210, p210, p210, p210, p210],
    ![p120, p120, p120, p120, p120, p120],
    ![p120, p120, p120, p120, p120, p120]] i j
def pos6c0 (p : ZMod 6 × ZMod 6) : ZMod (6 ^ 2) :=
  ![![0, 23, 19, 32, 6, 26],
    ![9, 18, 31, 5, 13, 35],
    ![17, 30, 4, 12, 25, 22],
    ![16, 29, 3, 11, 34, 8],
    ![15, 28, 2, 24, 21, 7],
    ![27, 1, 10, 20, 33, 14]] p.1 p.2
def pos6c1 (p : ZMod 6 × ZMod 6) : ZMod (6 ^ 2) :=
  ![![0, 5, 4, 3, 2, 1],
    ![11, 10, 9, 8, 7, 6],
    ![17, 16, 15, 14, 13, 12],
    ![23, 22, 21, 20, 19, 18],
    ![27, 26, 25, 29, 24, 28],
    ![31, 30, 35, 34, 33, 32]] p.1 p.2
def pos6c2 (p : ZMod 6 × ZMod 6) : ZMod (6 ^ 2) :=
  ![![0, 16, 21, 6, 26, 31],
    ![1, 17, 22, 7, 11, 32],
    ![2, 18, 23, 8, 27, 12],
    ![13, 3, 19, 24, 28, 33],
    ![34, 14, 4, 9, 25, 29],
    ![35, 15, 20, 5, 10, 30]] p.1 p.2

/-- (L4) certificats de `m = 4`. -/
theorem small4_cert (c : Fin 3) : ∃ pos : ZMod 4 × ZMod 4 → ZMod (4 ^ 2),
    ∀ p, pos (retOf smallA4 smallB4 c p) = pos p + 1 := by
  fin_cases c
  · exact ⟨pos4c0, by decide +kernel⟩
  · exact ⟨pos4c1, by decide +kernel⟩
  · exact ⟨pos4c2, by decide +kernel⟩

/-- (L5) certificats de `m = 6`. -/
theorem small6_cert (c : Fin 3) : ∃ pos : ZMod 6 × ZMod 6 → ZMod (6 ^ 2),
    ∀ p, pos (retOf smallA6 smallB6 c p) = pos p + 1 := by
  fin_cases c
  · exact ⟨pos6c0, by decide +kernel⟩
  · exact ⟨pos6c1, by decide +kernel⟩
  · exact ⟨pos6c2, by decide +kernel⟩

theorem small4 : HasHamiltonianArcDecomposition 4 :=
  decomp_of_certs (by norm_num) smallA4 smallB4 small4_cert

theorem small6 : HasHamiltonianArcDecomposition 6 :=
  decomp_of_certs (by norm_num) smallA6 smallB6 small6_cert

/- ## 6. Règle de Ho, `m` pair `≥ 8`, `h = m / 2` (GPT26, annexe A) -/

/-- Table de la fibre `m - 2` (fonction `d_layer_m2` de `even_closed_form.c`), lue sur
`a = i.val`, `b = j.val`. -/
def hoA (m : ℕ) [NeZero m] (i j : ZMod m) : Equiv.Perm (Fin 3) :=
  let a := i.val
  let b := j.val
  let h := m / 2
  if a = 0 then (if b = m - 2 then p210 else if b = m - 1 then p102 else p012)
  else if a = 1 then (if b = m - 2 then p201 else if b = m - 1 then p210 else p012)
  else if a + 3 ≤ h then (if a + b + 1 = m then p102 else if b = m - 1 then p210 else p012)
  else if h + 2 ≤ a then (if a + b + 1 = m then p102 else if b = m - 2 then p210 else p012)
  else if a + 2 = h then
    (if b ≤ h then p021 else if b = h + 1 then p120
     else if b = m - 2 then (if m % 4 = 0 then p012 else p102)
     else if b = m - 1 then (if m % 4 = 0 then p201 else p021) else p012)
  else if a + 1 = h then
    (if b + 1 ≤ h then p021 else if b = h then p120 else if b + 3 ≤ m then p021
     else if b = m - 2 then (if m % 4 = 0 then p021 else p201)
     else if b = m - 1 then (if m % 4 = 0 then p201 else p021) else p012)
  else if a = h then
    (if b + 2 ≤ h then p021 else if b + 1 = h then p120 else if b + 3 ≤ m then p021
     else if b = m - 2 then (if m % 4 = 0 then p021 else p201)
     else if b = m - 1 then (if m % 4 = 0 then p201 else p021) else p012)
  else
    (if b + 3 ≤ h then p012 else if b + 2 = h then p102 else if b + 3 ≤ m then p021
     else if b = m - 2 then (if m % 4 = 0 then p120 else p210) else p012)

/-- Table de la fibre `m - 1` : `210` sur les lignes `i ∈ {h - 1, h}`, `120` ailleurs. -/
def hoB (m : ℕ) [NeZero m] (i _j : ZMod m) : Equiv.Perm (Fin 3) :=
  if i.val + 1 = m / 2 ∨ i.val = m / 2 then p210 else p120

/- ## Passage aux naturels (outil commun aux trois couleurs)

`retN` est la carte de retour calculée sur des représentants naturels `< m` ; `retOf_natCast`
la relie à `retOf`, et `cert_of_nat` ramène un certificat de position à une égalité entre naturels
(`omega`). `hoAN`, `hoBN` : les tables de Ho lues sur les naturels (`hoA m i j = hoAN m i.val j.val`
par `rfl`). -/

/-- `(a - 2) mod m` pour `a < m`. -/
def sub2N (m a : ℕ) : ℕ := if 2 ≤ a then a - 2 else a + m - 2

/-- `(a + 1) mod m` pour `a < m`. -/
def incN (m a : ℕ) : ℕ := if a + 1 < m then a + 1 else 0

def mvN (m : ℕ) (d : Fin 3) (p : ℕ × ℕ) : ℕ × ℕ :=
  (if d = 0 then incN m p.1 else p.1, if d = 1 then incN m p.2 else p.2)

def preN (m : ℕ) (c : Fin 3) (p : ℕ × ℕ) : ℕ × ℕ :=
  (if c = 0 then sub2N m p.1 else p.1, if c = 1 then sub2N m p.2 else p.2)

def lookN (m : ℕ) (T : ℕ → ℕ → Equiv.Perm (Fin 3)) (c : Fin 3) (q : ℕ × ℕ) : ℕ × ℕ :=
  mvN m (T q.1 q.2 c) q

/-- Carte de retour sur les représentants naturels. -/
def retN (m : ℕ) (A B : ℕ → ℕ → Equiv.Perm (Fin 3)) (c : Fin 3) (p : ℕ × ℕ) : ℕ × ℕ :=
  lookN m B c (lookN m A c (preN m c p))

/-- Relevé dans `ZMod m` d'un couple de naturels. -/
def cast2 (m : ℕ) (q : ℕ × ℕ) : ZMod m × ZMod m := ((q.1 : ZMod m), (q.2 : ZMod m))

def preZ {m : ℕ} [NeZero m] (c : Fin 3) (p : ZMod m × ZMod m) : ZMod m × ZMod m :=
  (if c = 0 then p.1 - 2 else p.1, if c = 1 then p.2 - 2 else p.2)

def lookZ {m : ℕ} [NeZero m] (T : ZMod m → ZMod m → Equiv.Perm (Fin 3)) (c : Fin 3)
    (q : ZMod m × ZMod m) : ZMod m × ZMod m :=
  mv (T q.1 q.2 c) q

theorem retOf_eq_look {m : ℕ} [NeZero m] (A B : ZMod m → ZMod m → Equiv.Perm (Fin 3))
    (c : Fin 3) (p : ZMod m × ZMod m) : retOf A B c p = lookZ B c (lookZ A c (preZ c p)) := rfl

theorem sub2N_lt {m a : ℕ} (hm : 2 < m) (ha : a < m) : sub2N m a < m := by
  unfold sub2N; split_ifs <;> omega

theorem incN_lt {m a : ℕ} (ha : a < m) : incN m a < m := by
  unfold incN; split_ifs <;> omega

theorem cast_sub2N {m a : ℕ} [NeZero m] (hm : 2 < m) (ha : a < m) :
    ((sub2N m a : ℕ) : ZMod m) = (a : ZMod m) - 2 := by
  unfold sub2N
  split_ifs with h
  · rw [Nat.cast_sub h]; push_cast; ring
  · rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]; push_cast; ring

theorem cast_incN {m a : ℕ} [NeZero m] (ha : a < m) :
    ((incN m a : ℕ) : ZMod m) = (a : ZMod m) + 1 := by
  unfold incN
  split_ifs with h
  · push_cast; ring
  · have e : a + 1 = m := by omega
    rw [Nat.cast_zero, ← Nat.cast_one, ← Nat.cast_add, e, ZMod.natCast_self]

theorem mvN_lt {m : ℕ} (d : Fin 3) (p : ℕ × ℕ) (h1 : p.1 < m) (h2 : p.2 < m) :
    (mvN m d p).1 < m ∧ (mvN m d p).2 < m := by
  unfold mvN
  constructor <;> dsimp only <;> split_ifs <;> first | exact incN_lt h1 | exact incN_lt h2 | assumption

theorem preN_lt {m : ℕ} (hm : 2 < m) (c : Fin 3) (p : ℕ × ℕ) (h1 : p.1 < m) (h2 : p.2 < m) :
    (preN m c p).1 < m ∧ (preN m c p).2 < m := by
  unfold preN
  constructor <;> dsimp only <;> split_ifs <;>
    first | exact sub2N_lt hm h1 | exact sub2N_lt hm h2 | assumption

theorem retN_lt {m : ℕ} (hm : 2 < m) (A B : ℕ → ℕ → Equiv.Perm (Fin 3)) (c : Fin 3)
    (p : ℕ × ℕ) (h1 : p.1 < m) (h2 : p.2 < m) :
    (retN m A B c p).1 < m ∧ (retN m A B c p).2 < m := by
  obtain ⟨q1, q2⟩ := preN_lt hm c p h1 h2
  obtain ⟨r1, r2⟩ := mvN_lt (A (preN m c p).1 (preN m c p).2 c) _ q1 q2
  exact mvN_lt _ _ r1 r2

theorem cast_preN {m : ℕ} [NeZero m] (hm : 2 < m) (c : Fin 3) (p : ℕ × ℕ) (h1 : p.1 < m)
    (h2 : p.2 < m) : preZ c (cast2 m p) = cast2 m (preN m c p) := by
  unfold preZ preN cast2
  dsimp only
  split_ifs <;> simp [cast_sub2N hm h1, cast_sub2N hm h2]

theorem cast_mvN {m : ℕ} [NeZero m] (d : Fin 3) (p : ℕ × ℕ) (h1 : p.1 < m) (h2 : p.2 < m) :
    mv d (cast2 m p) = cast2 m (mvN m d p) := by
  unfold mv mvN cast2
  dsimp only
  split_ifs <;> simp [cast_incN h1, cast_incN h2]

theorem cast_lookN {m : ℕ} [NeZero m] (T : ℕ → ℕ → Equiv.Perm (Fin 3)) (c : Fin 3)
    (q : ℕ × ℕ) (h1 : q.1 < m) (h2 : q.2 < m) :
    lookZ (fun i j : ZMod m => T i.val j.val) c (cast2 m q) = cast2 m (lookN m T c q) := by
  unfold lookZ lookN
  have e1 : ((cast2 m q).1).val = q.1 := by
    simp only [cast2, ZMod.val_natCast, Nat.mod_eq_of_lt h1]
  have e2 : ((cast2 m q).2).val = q.2 := by
    simp only [cast2, ZMod.val_natCast, Nat.mod_eq_of_lt h2]
  simp only [e1, e2]
  exact cast_mvN _ q h1 h2

/-- La carte de retour, calculée sur les représentants naturels. -/
theorem retOf_natCast {m : ℕ} [NeZero m] (hm : 2 < m) (A B : ℕ → ℕ → Equiv.Perm (Fin 3))
    (c : Fin 3) (p : ℕ × ℕ) (h1 : p.1 < m) (h2 : p.2 < m) :
    retOf (fun i j : ZMod m => A i.val j.val) (fun i j : ZMod m => B i.val j.val) c
      (cast2 m p) = cast2 m (retN m A B c p) := by
  obtain ⟨q1, q2⟩ := preN_lt hm c p h1 h2
  obtain ⟨r1, r2⟩ : (lookN m A c (preN m c p)).1 < m ∧ (lookN m A c (preN m c p)).2 < m :=
    mvN_lt _ _ q1 q2
  rw [retOf_eq_look, cast_preN hm c p h1 h2, cast_lookN A c _ q1 q2,
    cast_lookN B c _ r1 r2]
  rfl

/-- Certificat de position à partir d'une formule sur les naturels. -/
theorem cert_of_nat {m : ℕ} [NeZero m] (hm : 2 < m) (A B : ℕ → ℕ → Equiv.Perm (Fin 3))
    (c : Fin 3) (P : ℕ → ℕ → ℕ)
    (hP : ∀ a b, a < m → b < m →
      P (retN m A B c (a, b)).1 (retN m A B c (a, b)).2 = P a b + 1 ∨
      P (retN m A B c (a, b)).1 (retN m A B c (a, b)).2 + m * m = P a b + 1) :
    ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf (fun i j : ZMod m => A i.val j.val) (fun i j : ZMod m => B i.val j.val)
        c p) = pos p + 1 := by
  refine ⟨fun p => ((P p.1.val p.2.val : ℕ) : ZMod (m ^ 2)), ?_⟩
  intro p
  have ha := ZMod.val_lt p.1
  have hb := ZMod.val_lt p.2
  have hp : p = cast2 m (p.1.val, p.2.val) := by simp [cast2]
  rw [hp, retOf_natCast hm A B c _ ha hb]
  obtain ⟨t1, t2⟩ := retN_lt hm A B c (p.1.val, p.2.val) ha hb
  simp only [cast2, ZMod.val_natCast, Nat.mod_eq_of_lt t1, Nat.mod_eq_of_lt t2,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rcases hP p.1.val p.2.val ha hb with h | h
  · rw [h]; push_cast; ring
  · have e := congrArg (fun n : ℕ => (n : ZMod (m ^ 2))) h
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at e
    have hmm : ((m : ZMod (m ^ 2)) * m) = 0 := by
      rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]
    rw [hmm, add_zero] at e
    exact e

/-- Certificat par lignes : la carte parcourt la ligne `a` dans l'ordre de `off a`, puis entre
dans la ligne suivante (la ligne `0` après la dernière) au rang `0`. -/
theorem cert_rows {m : ℕ} [NeZero m] (hm : 2 < m) (A B : ℕ → ℕ → Equiv.Perm (Fin 3))
    (c : Fin 3) (off : ℕ → ℕ → ℕ)
    (hP : ∀ a b, a < m → b < m → ∀ a' b', retN m A B c (a, b) = (a', b') →
      (a' = a ∧ off a b' = off a b + 1) ∨
      (off a b + 1 = m ∧ off a' b' = 0 ∧ (a' = a + 1 ∨ (a + 1 = m ∧ a' = 0)))) :
    ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf (fun i j : ZMod m => A i.val j.val) (fun i j : ZMod m => B i.val j.val)
        c p) = pos p + 1 := by
  refine cert_of_nat hm A B c (fun a b => m * a + off a b) ?_
  intro a b ha hb
  obtain ⟨a', b', hT⟩ : ∃ a' b', retN m A B c (a, b) = (a', b') := ⟨_, _, rfl⟩
  have key := hP a b ha hb a' b' hT
  rw [hT]
  dsimp only
  rcases key with ⟨rfl, h2⟩ | ⟨h2, h3, rfl | ⟨h0, rfl⟩⟩
  · left; omega
  · left
    have e : m * (a + 1) = m * a + m := by ring
    omega
  · right
    have e : m * m = m * a + m := by rw [← h0]; ring
    omega

/-- Table `A` de Ho sur les naturels (même corps que `hoA`). -/
def hoAN (m a b : ℕ) : Equiv.Perm (Fin 3) :=
  let h := m / 2
  if a = 0 then (if b = m - 2 then p210 else if b = m - 1 then p102 else p012)
  else if a = 1 then (if b = m - 2 then p201 else if b = m - 1 then p210 else p012)
  else if a + 3 ≤ h then (if a + b + 1 = m then p102 else if b = m - 1 then p210 else p012)
  else if h + 2 ≤ a then (if a + b + 1 = m then p102 else if b = m - 2 then p210 else p012)
  else if a + 2 = h then
    (if b ≤ h then p021 else if b = h + 1 then p120
     else if b = m - 2 then (if m % 4 = 0 then p012 else p102)
     else if b = m - 1 then (if m % 4 = 0 then p201 else p021) else p012)
  else if a + 1 = h then
    (if b + 1 ≤ h then p021 else if b = h then p120 else if b + 3 ≤ m then p021
     else if b = m - 2 then (if m % 4 = 0 then p021 else p201)
     else if b = m - 1 then (if m % 4 = 0 then p201 else p021) else p012)
  else if a = h then
    (if b + 2 ≤ h then p021 else if b + 1 = h then p120 else if b + 3 ≤ m then p021
     else if b = m - 2 then (if m % 4 = 0 then p021 else p201)
     else if b = m - 1 then (if m % 4 = 0 then p201 else p021) else p012)
  else
    (if b + 3 ≤ h then p012 else if b + 2 = h then p102 else if b + 3 ≤ m then p021
     else if b = m - 2 then (if m % 4 = 0 then p120 else p210) else p012)

/-- Table `B` de Ho sur les naturels. -/
def hoBN (m a _b : ℕ) : Equiv.Perm (Fin 3) :=
  if a + 1 = m / 2 ∨ a = m / 2 then p210 else p120

theorem hoA_eq (m : ℕ) [NeZero m] : hoA m = fun i j : ZMod m => hoAN m i.val j.val := rfl

theorem hoB_eq (m : ℕ) [NeZero m] : hoB m = fun i j : ZMod m => hoBN m i.val j.val := rfl

/-- Forme d'usage : il suffit d'une formule de position sur les naturels. -/
theorem hoCert_of_nat (m : ℕ) [NeZero m] (h8 : 8 ≤ m) (c : Fin 3) (P : ℕ → ℕ → ℕ)
    (hP : ∀ a b, a < m → b < m →
      P (retN m (hoAN m) (hoBN m) c (a, b)).1 (retN m (hoAN m) (hoBN m) c (a, b)).2 = P a b + 1 ∨
      P (retN m (hoAN m) (hoBN m) c (a, b)).1 (retN m (hoAN m) (hoBN m) c (a, b)).2 + m * m =
        P a b + 1) :
    ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf (hoA m) (hoB m) c p) = pos p + 1 := by
  rw [hoA_eq, hoB_eq]
  exact cert_of_nat (by omega) (hoAN m) (hoBN m) c P hP

/-- Forme d'usage du certificat par lignes pour la règle de Ho. -/
theorem hoCert_of_rows (m : ℕ) [NeZero m] (h8 : 8 ≤ m) (c : Fin 3) (off : ℕ → ℕ → ℕ)
    (hP : ∀ a b, a < m → b < m → ∀ a' b', retN m (hoAN m) (hoBN m) c (a, b) = (a', b') →
      (a' = a ∧ off a b' = off a b + 1) ∨
      (off a b + 1 = m ∧ off a' b' = 0 ∧ (a' = a + 1 ∨ (a + 1 = m ∧ a' = 0)))) :
    ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf (hoA m) (hoB m) c p) = pos p + 1 := by
  rw [hoA_eq, hoB_eq]
  exact cert_rows (by omega) (hoAN m) (hoBN m) c off hP

/-- Lignes génériques et quatre lignes centrales, numérotées de 1 à 4. -/
def c1_kind (h a : ℕ) : ℕ :=
  if a+2=h then 1 else if a+1=h then 2 else if a=h then 3 else if a=h+1 then 4 else 0

def c1_dir (h k a b : ℕ) : Fin 3 :=
  if k=0 then (if a+b=1 ∨ a+b=2*h+1 then 0 else 1)
  else if k=4 then (if b=h then 0 else if (1≤b ∧ b<h) ∨ (b=0 ∧ h%2=1) then 1 else 2)
  else if b+h%2=1 then 0 else if k=1 then (if b=0 ∨ h+4≤b then 1 else 2) else 2

theorem c1_pa (s : Prop) [Decidable s] (f g : Equiv.Perm (Fin 3)) :
    (if s then f else g) 1 = if s then f 1 else g 1 := by split <;> rfl

theorem c1_columns (h a : ℕ) :
    (a+3≤h ∨ h+2≤a) ∨ a+2=h ∨ a+1=h ∨ a=h ∨ a=h+1 := by omega

set_option maxHeartbeats 2400000 in
theorem c1_direction (h a b : ℕ) (hh : 4 ≤ h) (ha : a<2*h) (hb : b<2*h) :
    hoAN (2*h) a (sub2N (2*h) b) 1 = c1_dir h (c1_kind h a) a b := by
  have he : 2*h/2=h := by omega
  rcases c1_columns h a with hr|hr|hr|hr|hr <;>
    simp (disch := omega) only [c1_kind, if_pos, if_neg] <;>
    simp only [hoAN, he, c1_pa, p210_1, p102_1, p012_apply, p201_1, p120_1, p021_1,
      ite_self, c1_dir, sub2N] <;>
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false, ite_self] <;>
    split_ifs <;> (try rfl) <;> (try omega)
  all_goals simp_all only [p012_apply, Fin.reduceEq, true_and, and_true]
  all_goals omega

def c1_a (h k a b : ℕ) : ℕ :=
  if k=0 then (if a+b=1 ∨ a+b=2*h+1 then incN (2*h) a else a)
  else if k=4 then (if b=h then a+1 else a) else (if b+h%2=1 then a+1 else a)

def c1_b (h k a b : ℕ) : ℕ :=
  let m := 2*h
  if k=0 then
    (if a+b=1 ∨ a+b=m+1 then (if a+1=m then 0 else m-1-a) else if b=0 then m-1 else b-1)
  else if k=1 then
    (if b+h%2=1 then (if h%2=0 then 0 else m-1) else if b≤1 then m-1
      else if b≤h+3 then b-2 else b-1)
  else if k=4 then
    (if b=0 then m-2+h%2 else if b<h then b-1 else if b=h then h-2 else b-2)
  else if b+h%2=1 then
    (if k=2 then (if h%2=0 then 0 else m-1) else (if h%2=0 then m-1 else m-2))
  else if b=0 then m-1 else b-1

theorem c1_ret_aux (h a b : ℕ) (hh : 4 ≤ h) (ha : a<2*h) (hb : b<2*h) :
    let k := c1_kind h a
    let d := c1_dir h k a b
    let r := mvN (2*h) d (a, sub2N (2*h) b)
    retN (2*h) (hoAN (2*h)) (hoBN (2*h)) 1 (a,b) =
      mvN (2*h) (if r.1+1=h ∨ r.1=h then 1 else 2) r := by
  simp only [retN, lookN, preN, Fin.reduceEq, if_false, if_true, hoBN, c1_pa, p210_1,
    p120_1, show 2*h/2=h by omega, c1_direction h a b hh ha hb]

set_option maxHeartbeats 2000000 in
theorem c1_ret (h a b : ℕ) (hh : 4 ≤ h) (ha : a<2*h) (hb : b<2*h) :
    let k := c1_kind h a
    retN (2*h) (hoAN (2*h)) (hoBN (2*h)) 1 (a,b) = (c1_a h k a b, c1_b h k a b) := by
  rw [c1_ret_aux h a b hh ha hb]
  rcases c1_columns h a with hr|hr|hr|hr|hr <;>
    simp (disch := omega) only [c1_kind, if_pos, if_neg] <;>
    simp only [c1_dir, c1_a, c1_b, mvN, incN, sub2N, Prod.mk.injEq] <;>
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false] <;>
    (repeat' first | omega | split <;> try omega)
  all_goals try simp_all only [Fin.reduceEq, true_and, and_true]
  all_goals omega

/-- Rang sur la ligne courante, avant le passage à la ligne suivante. -/
def c1_off (h k a b : ℕ) : ℕ :=
  let m := 2*h
  let f := (h+4)/2
  if k=1 then
    (if b≤h+2 ∧ b%2=h%2 then (h+2-b)/2
     else if h+3≤b then f+(m-1-b) else f+(h-3)+(h+1-b)/2)
  else if k=2 ∨ k=3 then
    (if h%2=0 then (if b=0 then 0 else m-b) else m-1-b)
  else if k=4 then
    (if b=h then m-1 else if b<h then h/2+(h-1-b)
     else if b%2=h%2 then h/2+h+(m-1-b)/2 else (m-1-b)/2)
  else if a+b=0 then 0 else if a + b ≤ m then m-(a+b) else 2*m-(a+b)

def c1_entry (h a : ℕ) : ℕ :=
  if a+1=h ∨ a=h then (if h%2=0 then 0 else 2*h-1)
  else if a=h+1 then 2*h-1-h%2 else if a=0 then 0 else 2*h-a

theorem c1_entry_zero (h a : ℕ) (hh : 4 ≤ h) (ha : a<2*h) :
    c1_off h (c1_kind h a) a (c1_entry h a) = 0 := by
  rcases c1_columns h a with hr|hr|hr|hr|hr <;>
    simp (disch := omega) only [c1_kind, if_pos, if_neg] <;>
    simp only [c1_off, c1_entry] <;>
    (repeat' first | omega | split <;> try omega)
  all_goals simp_all only [true_or, or_true, not_true_eq_false]

set_option maxHeartbeats 4000000 in
theorem c1_step (h a b : ℕ) (hh : 4 ≤ h) (ha : a<2*h) (hb : b<2*h) :
    let k := c1_kind h a
    let x := c1_a h k a b
    let y := c1_b h k a b
    (x=a ∧ c1_off h k a y = c1_off h k a b + 1) ∨
      (c1_off h k a b + 1 = 2*h ∧ y = c1_entry h x ∧
        (x=a+1 ∨ (a+1=2*h ∧ x=0))) := by
  rcases c1_columns h a with hr|hr|hr|hr|hr <;>
    simp (disch := omega) only [c1_kind, if_pos, if_neg] <;>
    simp only [c1_a, c1_b, c1_off, c1_entry, incN] <;>
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false] <;>
    (repeat' first | omega | split <;> try omega)
  all_goals simp_all only [true_or, or_true, not_true_eq_false]

theorem hoCert1 (m : ℕ) [NeZero m] (hm : Even m) (h8 : 8 ≤ m) :
    ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf (hoA m) (hoB m) 1 p) = pos p + 1 := by
  obtain ⟨h, rfl⟩ : ∃ h, m = 2*h := by
    obtain ⟨h,e⟩ := hm
    exact ⟨h, by omega⟩
  have hh : 4 ≤ h := by omega
  apply hoCert_of_rows (2*h) h8 1 (fun a b => c1_off h (c1_kind h a) a b)
  intro a b ha hb x y hxy
  have hx := (retN_lt (by omega : 2<2*h) (hoAN (2*h)) (hoBN (2*h)) 1 (a,b) ha hb).1
  rw [hxy] at hx
  rw [c1_ret h a b hh ha hb, Prod.mk.injEq] at hxy
  obtain ⟨rfl,rfl⟩ := hxy
  rcases c1_step h a b hh ha hb with ⟨e,f⟩ | ⟨e,f,g⟩
  · exact Or.inl ⟨e,f⟩
  · exact Or.inr ⟨e, f ▸ c1_entry_zero h _ hh hx, g⟩

/-- Les sept types de ligne, dans leur ordre de rencontre. -/
def c2_kind (h b : ℕ) : ℕ :=
  if b + 2 ≤ h then 0 else if b + 1 = h then 1 else if b = h then 2
  else if b = h + 1 then 3 else if b + 3 ≤ 2*h then 4
  else if b + 2 = 2*h then 5 else 6

/-- Direction de la première étape non triviale : 0 saute, 1 monte, 2 avance. -/
def c2_dir (h : ℕ) : ℕ → ℕ → Fin 3
  | 0, a => if a + 2 = h ∨ a + 1 = h ∨ a = h then 1 else 2
  | 1, a => if a = h then 0 else if a + 2 = h ∨ a + 1 = h ∨ a = h+1 then 1 else 2
  | 2, a => if a + 1 = h then 0 else if a + 2 = h ∨ a = h ∨ a = h+1 then 1 else 2
  | 3, a => if a + 2 = h then 0 else if a + 1 = h ∨ a = h ∨ a = h+1 then 1 else 2
  | 4, a => if a + 1 = h ∨ a = h ∨ a = h+1 then 1 else 2
  | 5, a => if a = 1 ∨ a + 1 = h ∨ a = h then 1 else if a = 0 ∨ h+1 ≤ a then 0 else 2
  | _, a => if a + 2 = h ∨ a + 1 = h ∨ a = h then 1 else if 1 ≤ a ∧ a+3 ≤ h then 0 else 2

theorem c2_pa (s : Prop) [Decidable s] (f g : Equiv.Perm (Fin 3)) :
    (if s then f else g) 2 = if s then f 2 else g 2 := by split <;> rfl

set_option maxHeartbeats 1600000 in
theorem c2_direction (h : ℕ) [NeZero (2*h)] (hh : 4 ≤ h) (i j : ZMod (2*h)) :
    hoA (2*h) i j 2 = c2_dir h (c2_kind h j.val) i.val := by
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  have he : 2*h/2 = h := by omega
  have hr : j.val+2 ≤ h ∨ j.val+1=h ∨ j.val=h ∨ j.val=h+1 ∨
      (h+2 ≤ j.val ∧ j.val+3 ≤ 2*h) ∨ j.val+2=2*h ∨ j.val+1=2*h := by omega
  rcases hr with hr|hr|hr|hr|hr|hr|hr <;>
    simp (disch := omega) only [c2_kind, if_pos, if_neg] <;>
    simp only [hoA, he, c2_pa, p210_2, p102_2, p012_apply, p201_2, p120_2,
      p021_2, ite_self, c2_dir] <;>
    simp (disch := omega) only [if_pos, if_neg, ite_self] <;>
    split_ifs <;> first | rfl | omega

theorem c2_ret (h : ℕ) [NeZero (2*h)] (hh : 4 ≤ h) (i j : ZMod (2*h)) :
    let d := c2_dir h (c2_kind h j.val) i.val
    retOf (hoA (2*h)) (hoB (2*h)) 2 (i,j) =
      ((if d = 0 then i + 1 else i) + 1, if d = 1 then j+1 else j) := by
  have hb (x y : ZMod (2*h)) : hoB (2*h) x y 2 = 0 := by
    simp [hoB, c2_pa]
  simp [retOf, mv, hb, c2_direction h hh]

/-- Les bases des trois chemins entrants d'une ligne. -/
abbrev c2_B := ℕ × ℕ × ℕ

def c2_next (h : ℕ) (k : ℕ) (p : c2_B) : c2_B :=
  let (x,y,z) := p
  let m := 2*h
  let s := h/2+1
  let t := (h-1)/2
  match k with
  | 0 | 4 => (z+(m-2), x+1, y+1)
  | 1 => (y+(m-2), x+1, z+1)
  | 2 => (z+(m-3), y+1, x+2)
  | 3 => (x+1, z+(m-2), y+1)
  | 5 => if h%2=0 then (y+s, z+(m-1-s), x+1) else (z+s, y+(m-1-s), x+1)
  | _ => if h%2=0 then (x+t, z+(m-1-t), y+1) else (z+(m-1-t), x+t, y+1)

def c2_off (h a s : ℕ) := if s ≤ a then a-s else 2*h+a-s

def c2_gen (h a t : ℕ) (p : c2_B) : ℕ :=
  if a = t then p.1 else if a = t+1 then p.2.1 else p.2.2 + c2_off h a (t+2)

/-- Position sur le chemin de la ligne, depuis sa base entrante. -/
def c2_at (h k : ℕ) (p : c2_B) (a : ℕ) : ℕ :=
  let (x,y,z) := p
  match k with
  | 0 => c2_gen h a (h-1) p
  | 1 => if a+1=h then x else if a=h+1 then z else y+(if a=h then 0 else c2_off h a (h+1))
  | 2 => if a+1=h then x else if a=h+1 then x+1 else if a=h then y else z+c2_off h a (h+2)
  | 3 => if a+1=h then x else if a=h+1 then y else z+(if a=h then 2*h-3 else c2_off h a (h+2))
  | 4 => c2_gen h a h p
  | 5 => if a=h then x else
      let d := (if a<h then 2*h+(if a≤2 then a else 2) else a)-(h+1)
      (if d%2=0 then y else z)+d/2+(if a<h then a-2 else 0)
  | _ => if a=h then y else if h+1≤a then z+(a-(h+1))
      else if a=0 then z+(h-1)
      else if a%2=0 then x+(a-2)/2 else z+h+(a-1)/2

def c2_wrap (h n : ℕ) := if n < 2*h then n else n-2*h

def c2_valid (h a : ℕ) (p : c2_B) (k l : ℕ) : Prop :=
  let d := c2_dir h k a
  (if d = 1 then c2_at h l (c2_next h k p) (c2_wrap h (a+1))
   else c2_at h k p (c2_wrap h (a+1+(if d=0 then 1 else 0)))) = c2_at h k p a + 1

set_option maxHeartbeats 4400000 in
theorem c2_local (h a b : ℕ) (p : c2_B) (hh : 4 ≤ h) (ha : a<2*h) (hb : b<2*h) :
    c2_valid h a p (c2_kind h b) (c2_kind h (c2_wrap h (b+1))) := by
  have eb : b+3≤h ∨ b+2=h ∨ b+1=h ∨ b=h ∨ (b=h+1 ∧ h=4) ∨ (b=h+1 ∧ 5≤h) ∨
      (h+2≤b ∧ b+4≤2*h) ∨ (h+2≤b ∧ b+3=2*h) ∨ b+2=2*h ∨ b+1=2*h := by omega
  rcases eb with e|e|e|e|e|e|e|e|e|e <;>
    simp (disch := omega) only [c2_kind, c2_wrap, if_pos, if_neg]
  all_goals obtain ⟨x,y,z⟩ := p
  all_goals simp only [c2_valid, c2_dir, c2_at, c2_gen, c2_next, c2_wrap, c2_off]
  all_goals repeat' first | omega | split <;> try omega
  all_goals try dsimp only at *
  all_goals omega

/-- Bases successives, avant de recoller la dernière ligne à la première. -/
def c2_bases (h : ℕ) (p : c2_B) : ℕ → c2_B
  | 0 => p
  | b+1 => c2_next h (c2_kind h b) (c2_bases h p b)

def c2_pow (h : ℕ) : ℕ → c2_B → c2_B
  | 0, p => p
  | n+1, p => c2_next h 0 (c2_pow h n p)

theorem c2_block (h : ℕ) (p : c2_B) (s n : ℕ)
    (hb : ∀ j < n, c2_kind h (s+j) = 0 ∨ c2_kind h (s+j) = 4) :
    c2_bases h p (s+n) = c2_pow h n (c2_bases h p s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ, c2_bases, ih (by intro j hj; exact hb j (by omega)), c2_pow]
    rcases hb n (by omega) with e|e <;> rw [e] <;> rfl

def c2_lap (h : ℕ) (p : c2_B) : c2_B :=
  c2_next h 6 (c2_next h 5 (c2_pow h (h-4)
    (c2_next h 3 (c2_next h 2 (c2_next h 1 (c2_pow h (h-1) p))))))

theorem c2_entire (h : ℕ) (p : c2_B) (hh : 4 ≤ h) :
    c2_bases h p (2*h) = c2_lap h p := by
  have e := c2_block h p 0 (h-1) (by
    intro j hj; left; simp [c2_kind, show j+2 ≤ h by omega])
  simp only [Nat.zero_add, c2_bases] at e
  have f := c2_block h p (h+2) (h-4) (by
    intro j hj; right; simp (disch := omega) only [c2_kind, if_pos, if_neg] <;> rfl)
  rw [show h+2+(h-4)=2*h-2 by omega] at f
  have s1 : c2_kind h (h-1) = 1 := by simp (disch := omega) only [c2_kind, if_pos, if_neg] <;> rfl
  have s2 : c2_kind h h = 2 := by simp (disch := omega) only [c2_kind, if_pos, if_neg] <;> rfl
  have s3 : c2_kind h (h+1) = 3 := by simp (disch := omega) only [c2_kind, if_pos, if_neg] <;> rfl
  have s5 : c2_kind h (2*h-2) = 5 := by simp (disch := omega) only [c2_kind, if_pos, if_neg] <;> rfl
  have s6 : c2_kind h (2*h-1) = 6 := by simp (disch := omega) only [c2_kind, if_neg] <;> rfl
  have up (a b k : ℕ) (eb : b=a+1) (ek : c2_kind h a = k) :
      c2_bases h p b = c2_next h k (c2_bases h p a) := by rw [eb, c2_bases, ek]
  rw [up (2*h-1) (2*h) 6 (by omega) s6, up (2*h-2) (2*h-1) 5 (by omega) s5, f,
    up (h+1) (h+2) 3 rfl s3, up h (h+1) 2 rfl s2, up (h-1) h 1 (by omega) s1, e]
  rfl

def c2_addAll (a : ℕ) (p : c2_B) : c2_B :=
  (p.1+a,p.2.1+a,p.2.2+a)

theorem c2_pow_shift (h q r : ℕ) (p : c2_B) (hh : 4 ≤ h) :
    c2_pow h (3*q+r) p = c2_addAll (q*(2*h)) (c2_pow h r p) := by
  induction q with
  | zero => simp [c2_addAll]
  | succ q ih =>
    rw [show 3*(q+1)+r = (3*q+r)+3 by omega, Nat.succ_mul q (2*h)]
    simp only [c2_pow, ih, c2_next, c2_addAll]
    congr 1 <;> first | omega | (congr 1 <;> omega)

def c2_sum (p : c2_B) := p.1+p.2.1+p.2.2

theorem c2_sum_next (h k : ℕ) (p : c2_B) (hh : 4 ≤ h) :
    c2_sum (c2_next h k p) = c2_sum p + 2*h := by
  obtain ⟨x,y,z⟩ := p
  obtain hd : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ 6 ≤ k := by omega
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|hd <;>
    (try obtain ⟨k,rfl⟩ : ∃ u, k = u+6 := ⟨k-6, by omega⟩) <;>
    simp only [c2_next, c2_sum] <;> (try split) <;> (try dsimp only) <;> omega

theorem c2_sum_bases (h b : ℕ) (p : c2_B) (hh : 4 ≤ h) :
    c2_sum (c2_bases h p b) = c2_sum p + b*(2*h) := by
  induction b with
  | zero => simp [c2_bases]
  | succ b ih => rw [c2_bases, c2_sum_next h _ _ hh, ih, Nat.succ_mul b (2*h)]; omega

/- À un tour près, les trois bases sont permutées par un 3-cycle. -/
set_option maxHeartbeats 1400000 in
theorem c2_monodromy (h : ℕ) (hh : 4 ≤ h) (x y z : ℕ) :
    let w := c2_lap h (0,0,0)
    c2_lap h (x,y,z) = if h%2=0 then (w.1+y,w.2.1+z,w.2.2+x)
                           else (w.1+z,w.2.1+x,w.2.2+y) := by
  let q := (h-4)/3
  let r := (h-4)%3
  have ha : h-4=3*q+r := by dsimp [q,r]; omega
  have hb : h-1=3*(q+1)+r := by omega
  have hr : r<3 := Nat.mod_lt _ (by decide)
  simp only [c2_lap, ha, hb, c2_pow_shift h _ _ _ hh]
  interval_cases r <;> by_cases he : h%2=0 <;>
    simp only [c2_pow, c2_next, c2_addAll, he, if_true, if_false, zero_add] <;>
    congr 1 <;> first | omega | (congr 1 <;> omega)

theorem c2_fixed (h : ℕ) (hh : 4 ≤ h) :
    ∃ p : c2_B, ∀ a, (c2_at h 0 (c2_bases h p (2*h)) a : ZMod ((2*h)^2)) =
                        (c2_at h 0 p a : ZMod ((2*h)^2)) := by
  obtain ⟨A,B,C,e⟩ : ∃ A B C, c2_lap h (0,0,0) = (A,B,C) := by
    obtain ⟨A,B,C⟩ := c2_lap h (0,0,0)
    exact ⟨_,_,_,rfl⟩
  have hs := c2_sum_bases h (2*h) (0,0,0) hh
  rw [c2_entire h _ hh, e] at hs
  have ht : A+B+C=(2*h)^2 := by simpa [c2_sum, pow_two] using hs
  have hz : (A : ZMod ((2*h)^2))+B+C=0 := by
    rw [← Nat.cast_add, ← Nat.cast_add, ht, ZMod.natCast_self]
  by_cases he : h%2=0
  · refine ⟨(0,B+C,C), ?_⟩
    intro a
    rw [c2_entire h _ hh, c2_monodromy h hh, e, if_pos he]
    simp only [c2_at, c2_gen]
    split_ifs <;> push_cast <;> first | ring1 | linear_combination hz
  · refine ⟨(0,B,B+C), ?_⟩
    intro a
    rw [c2_entire h _ hh, c2_monodromy h hh, e, if_neg he]
    simp only [c2_at, c2_gen]
    split_ifs <;> push_cast <;> first | ring1 | linear_combination hz

theorem c2_up (h : ℕ) (p : c2_B) (hh : 4 ≤ h)
    (hp : ∀ a, (c2_at h 0 (c2_bases h p (2*h)) a : ZMod ((2*h)^2)) =
                        (c2_at h 0 p a : ZMod ((2*h)^2)))
    (b a : ℕ) (hb : b<2*h) :
    let t := c2_wrap h (b+1)
    (c2_at h (c2_kind h t) (c2_bases h p t) a : ZMod ((2*h)^2)) =
      (c2_at h (c2_kind h t) (c2_next h (c2_kind h b) (c2_bases h p b)) a : ZMod ((2*h)^2)) := by
  dsimp only
  change (c2_at h _ _ a : ZMod ((2*h)^2)) = (c2_at h _ (c2_bases h p (b+1)) a : ZMod ((2*h)^2))
  unfold c2_wrap
  split_ifs with e
  · rfl
  · have eb : b+1=2*h := by omega
    rw [eb, Nat.sub_self]
    have e0 : c2_kind h 0=0 := by simp [c2_kind, show 0+2 ≤ h by omega]
    simp only [e0, c2_bases]
    exact (hp a).symm

theorem c2_val_inc (h : ℕ) [NeZero (2*h)] (hh : 4 ≤ h) (i : ZMod (2*h)) (n : ℕ) (hn : n≤2) :
    (i+n).val = c2_wrap h (i.val+n) := by
  have en : (n : ZMod (2*h)).val = n := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  unfold c2_wrap
  split_ifs with e
  · rw [ZMod.val_add_of_lt (by simpa [en] using e), en]
  · rw [ZMod.val_add_of_le (by rw [en]; omega), en]

/-- couleur 2 (GPT26 §4). -/
theorem hoCert2 (m : ℕ) [NeZero m] (hm : Even m) (h8 : 8 ≤ m) :
    ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf (hoA m) (hoB m) 2 p) = pos p + 1 := by
  obtain ⟨h, rfl⟩ : ∃ h, m = 2*h := by
    obtain ⟨h, e⟩ := hm
    exact ⟨h, by omega⟩
  have hh : 4 ≤ h := by omega
  obtain ⟨p, hp⟩ := c2_fixed h hh
  let F (b a : ℕ) := c2_at h (c2_kind h b) (c2_bases h p b) a
  refine ⟨fun z => (F z.2.val z.1.val : ZMod ((2*h)^2)), ?_⟩
  rintro ⟨i,j⟩
  let d := c2_dir h (c2_kind h j.val) i.val
  have e := c2_local h i.val j.val (c2_bases h p j.val) hh (ZMod.val_lt _) (ZMod.val_lt _)
  change (if d=1 then c2_at h (c2_kind h (c2_wrap h (j.val+1)))
     (c2_next h (c2_kind h j.val) (c2_bases h p j.val)) (c2_wrap h (i.val+1))
     else F j.val (c2_wrap h (i.val+1+(if d=0 then 1 else 0)))) = F j.val i.val + 1 at e
  have v1 (z : ZMod (2*h)) : (z+1).val = c2_wrap h (z.val+1) := by
    simpa using c2_val_inc h hh z 1 (by decide)
  have v2 (z : ZMod (2*h)) : (z+1+1).val = c2_wrap h (z.val+1+1) := by
    simpa [add_assoc, one_add_one_eq_two] using c2_val_inc h hh z 2 (by decide)
  rw [c2_ret h hh]
  change (F (if d=1 then j+1 else j).val ((if d=0 then i+1 else i)+1).val : ZMod ((2*h)^2)) =
         (F j.val i.val : ZMod ((2*h)^2)) + 1
  have hd : d=0 ∨ d=1 ∨ d=2 := by omega
  rcases hd with hd|hd|hd
  · simp only [hd, Fin.reduceEq, if_false, if_true] at e ⊢
    rw [v2]
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod ((2*h)^2))) e
  · simp only [hd, Fin.reduceEq, if_false, if_true] at e ⊢
    rw [v1, v1]
    dsimp only [F]
    rw [c2_up h p hh hp _ _ (ZMod.val_lt j)]
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod ((2*h)^2))) e
  · simp only [hd, Fin.reduceEq, if_false, Nat.add_zero] at e ⊢
    rw [v1]
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod ((2*h)^2))) e

/-- Codage des pas : horizontal, vertical, diagonal, double horizontal, double vertical. -/
def c0_move (m x y : ℕ) : ℕ :=
  let h := m / 2
  if y + 1 = m then
    if x + 1 = h ∨ x = h ∨ x + 2 = m then 2 else 3
  else if x + 2 = m then
    if y + 1 < h then 2
    else if y + 1 = h then (if m % 4 = 0 then 3 else 2)
    else if y = h then (if m % 4 = 0 then 0 else 4)
    else if y = h + 1 then (if m % 4 = 0 then 1 else 4)
    else if y = h + 2 then (if m % 4 = 0 then 1 else 3)
    else 0
  else if x + 1 = m then
    if y + 1 < h then 0
    else if y + 1 = h then (if m % 4 = 0 then 4 else 0)
    else if y = h then (if m % 4 = 0 then 4 else 1)
    else if y = h + 1 then (if m % 4 = 0 then 2 else 1)
    else 2
  else if x+y+1 = h ∨ x+y = h ∨ x+y+1 = m+h ∨ x+y = m+h then 1 else 0

def c0_dx : ℕ → ℕ
  | 0 => 1
  | 2 => 1
  | 3 => 2
  | _ => 0

def c0_dy : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 4 => 2
  | _ => 0

def c0_pt (m : ℕ) [NeZero m] (x y : ℕ) : ZMod m × ZMod m :=
  (-(x : ZMod m) - y, x)

lemma c0_sum_cases (m x y a : ℕ) [NeZero m] (h8 : 8 ≤ m)
    (hx : x < m) (hy : y < m) (ha : a < m)
    (he : (a : ZMod m) = - (x : ZMod m) - y - 2) :
    a+x+y+2 = m ∨ a+x+y+2 = 2*m := by
  have he' : ((a+x+y+2 : ℕ) : ZMod m) = 0 := by push_cast; rw [he]; ring
  obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp he'
  have hlt : k < 3 := by
    by_contra! hg
    have := Nat.mul_le_mul_left m hg
    omega
  interval_cases k <;> simp_all <;> omega

/-- Direction du premier pas, avec des coordonnées naturelles. -/
def c0_first (m a b : ℕ) : ℕ :=
  let h := m / 2
  if a = 0 then (if b = m-2 then 2 else if b = m-1 then 1 else 0)
  else if a = 1 then (if b = m-2 then 2 else if b = m-1 then 2 else 0)
  else if a + 3 ≤ h then (if a+b+1 = m then 1 else if b = m-1 then 2 else 0)
  else if h + 2 ≤ a then (if a+b+1 = m then 1 else if b = m-2 then 2 else 0)
  else if a + 2 = h then
    (if b ≤ h then 0 else if b = h+1 then 1 else if b = m-2 then
      (if m%4 = 0 then 0 else 1) else if b = m-1 then (if m%4 = 0 then 2 else 0) else 0)
  else if a + 1 = h then
    (if b+1 ≤ h then 0 else if b = h then 1 else if b+3 ≤ m then 0 else if b = m-2 then
      (if m%4 = 0 then 0 else 2) else if b = m-1 then (if m%4 = 0 then 2 else 0) else 0)
  else if a = h then
    (if b+2 ≤ h then 0 else if b+1 = h then 1 else if b+3 ≤ m then 0 else if b = m-2 then
      (if m%4 = 0 then 0 else 2) else if b = m-1 then (if m%4 = 0 then 2 else 0) else 0)
  else
    (if b+3 ≤ h then 0 else if b+2 = h then 1 else if b+3 ≤ m then 0 else if b = m-2 then
      (if m%4 = 0 then 1 else 2) else 0)

def c0_read (p : Equiv.Perm (Fin 3)) : ℕ := (p 0).val

lemma c0_read_ite (c : Prop) [Decidable c] (p q : Equiv.Perm (Fin 3)) :
    c0_read (if c then p else q) = if c then c0_read p else c0_read q :=
  apply_ite c0_read c p q

lemma c0_first_ok (m : ℕ) [NeZero m] (i j : ZMod m) :
    (hoA m i j 0).val = c0_first m i.val j.val := by
  unfold hoA c0_first
  dsimp only
  change c0_read _ = _
  simp only [c0_read_ite]
  rfl

def c0_code (m a d : ℕ) : ℕ :=
  let a' := if d = 0 then (if a+1=m then 0 else a+1) else a
  if a'+1 = m/2 ∨ a' = m/2 then
    if d = 0 then 1 else if d = 1 then 2 else 4
  else if d = 0 then 0 else if d = 1 then 3 else 2

lemma c0_branch {α : Type*} (P : α → Prop) {c : Prop} [Decidable c] {a b : α}
    (h : c → P a) (k : ¬c → P b) : P (if c then a else b) := by
  split_ifs with hc
  · exact h hc
  · exact k hc

lemma c0_branch_left {c : Prop} [Decidable c] {a b v : ℕ}
    (h : c → a = v) (k : ¬c → b = v) : (if c then a else b) = v :=
  c0_branch (· = v) h k

lemma c0_branch_right {c : Prop} [Decidable c] {a b v : ℕ}
    (h : c → v = a) (k : ¬c → v = b) : v = (if c then a else b) :=
  c0_branch (v = ·) h k


/-- Les deux dernières colonnes sont déterminées par un seuil commun. -/
def c0_cut (m : ℕ) := if m%4 = 0 then m/2+1 else m/2-2

def c0_short (m a b : ℕ) : ℕ :=
  if b+2 < m then (if a+b+1 = m then 1 else 0)
  else if b+2=m then (if a=c0_cut m then 1 else if a≤1 ∨ c0_cut m < a then 2 else 0)
  else if a=0 then 1 else if a < c0_cut m then 2 else 0

set_option maxHeartbeats 2000000 in
lemma c0_short_ok (m a b : ℕ) (hm : m=2*(m/2)) (h8 : 8 ≤ m) (ha : a < m) (hb : b < m) :
    c0_first m a b = c0_short m a b := by
  let P := fun d => d = c0_short m a b
  change P _
  unfold c0_first
  dsimp only
  repeat' (apply c0_branch P <;> intro)
  all_goals by_cases hp : m%4 = 0 <;> simp only [P, c0_short, c0_cut, hp, ↓reduceIte]
  all_goals repeat' first | rfl | omega | (apply c0_branch_right <;> intro)

lemma c0_pred_short (m a b u v : ℕ) (h8 : 8 ≤ m) (ha : a < m) (hb : b < m)
    (hu : (u+1=a ∨ (a=0 ∧ u+1=m))) (hv : (v+1=b ∨ (b=0 ∧ v+1=m))) :
    c0_short m a b = 2 ∨ c0_short m u b = 0 ∨ c0_short m a v = 1 := by
  have hc : 2 ≤ c0_cut m ∧ c0_cut m+1 < m := by unfold c0_cut; split <;> omega
  generalize ht : c0_cut m = t at hc ⊢
  unfold c0_short
  rw [ht]
  split_ifs <;> omega

def c0_simple (m a d : ℕ) : ℕ :=
  if d = 0 then (if a+2=m/2 ∨ a+1=m/2 then 1 else 0)
  else if a+1=m/2 ∨ a=m/2 then (if d=1 then 2 else 4) else (if d=1 then 3 else 2)

lemma c0_simple_ok (m a d : ℕ) (h8 : 8 ≤ m) :
    c0_code m a d = c0_simple m a d := by
  unfold c0_code c0_simple
  dsimp only
  split_ifs <;> omega

set_option maxHeartbeats 6000000 in
lemma c0_code_ok (m a x y : ℕ) (hm : m = 2*(m/2)) (h8 : 8 ≤ m)
    (ha : a < m) (hx : x < m) (hy : y < m) (hs : a+x+y+2 = m ∨ a+x+y+2 = 2*m) :
    c0_code m a (c0_first m a x) = c0_move m x y := by
  rw [c0_simple_ok _ _ _ h8]
  let P := fun d => c0_simple m a d = c0_move m x y
  change P _
  unfold c0_first
  dsimp only
  repeat' (apply c0_branch P <;> intro)
  all_goals dsimp [P, c0_simple, c0_move]
  all_goals
    repeat' first | rfl | omega | (apply c0_branch_left <;> intro) |
      (apply c0_branch_right <;> intro)



lemma c0_val_inc {m : ℕ} [NeZero m] (u : ZMod m) :
    (u+1).val = if u.val+1=m then 0 else u.val+1 := by
  rw [show u+1 = ((u.val+1 : ℕ) : ZMod m) by simp]
  rw [ZMod.val_natCast]
  have := u.val_lt
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

lemma c0_val_x {m : ℕ} [NeZero m] {x : ℕ} (hx : x < m) :
    (x : ZMod m).val = x := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]

lemma c0_ret_dir (m x y : ℕ) [NeZero m] (d : Fin 3) :
    let u := -(x : ZMod m) - y - 2
    let r := mv d (u, (x : ZMod m))
    let t := c0_code m u.val d.val
    mv (hoB m r.1 r.2 0) r = c0_pt m (x + c0_dx t) (y + c0_dy t) := by
  dsimp only
  fin_cases d <;>
    simp only [mv, hoB, c0_pt, c0_code, Fin.isValue, Fin.reduceFinMk, Fin.val_zero,
      Fin.val_one, Fin.reduceEq, ↓reduceIte, c0_val_inc]
  all_goals split_ifs <;> simp_all [c0_dx, c0_dy] <;> try ring <;> simp

lemma c0_ret (m x y : ℕ) [NeZero m] (hm : Even m) (h8 : 8 ≤ m)
    (hx : x < m) (hy : y < m) :
    retOf (hoA m) (hoB m) 0 (c0_pt m x y) =
      c0_pt m (x+c0_dx (c0_move m x y)) (y+c0_dy (c0_move m x y)) := by
  let u := -(x : ZMod m) - y - 2
  have hs := c0_sum_cases m x y u.val h8 hx hy u.val_lt (ZMod.natCast_zmod_val u)
  have he : m = 2*(m/2) := by obtain ⟨k,hk⟩ := hm; omega
  have hc := c0_code_ok m u.val x y he h8 u.val_lt hx hy hs
  rw [← c0_val_x hx, ← c0_first_ok] at hc
  change c0_code m u.val (hoA m u (x : ZMod m) 0).val = _ at hc
  rw [c0_val_x hx] at hc
  rw [← hc]
  exact c0_ret_dir m x y (hoA m u (x : ZMod m) 0)


/-- Un rang qui croît, sauf au passage par la racine, exclut tout deuxième cycle. -/
lemma c0_rank_cert {α β : Type*} [Fintype α] [LinearOrder β] (N : ℕ) [NeZero N]
    (hN : Fintype.card α = N) (f : α → α) (hf : Function.Surjective f)
    (o : α) (R : α → β) (hR : ∀ a, f a = o ∨ R a < R (f a)) :
    ∃ pos : α → ZMod N, ∀ a, pos (f a) = pos a + 1 := by
  classical
  let σ : Equiv.Perm α := Equiv.ofBijective f (Finite.surjective_iff_bijective.mp hf)
  have hall (a : α) : σ.SameCycle a o := by
    let S := Finset.univ.filter (σ.SameCycle a)
    have hne : S.Nonempty := ⟨a, by simp [S, Equiv.Perm.SameCycle.rfl]⟩
    obtain ⟨b, hb, hmax⟩ := S.exists_max_image R hne
    have hb' : σ.SameCycle a b := (Finset.mem_filter.mp hb).2
    have hc : σ.SameCycle a (σ b) := Equiv.Perm.sameCycle_apply_right.mpr hb'
    rcases hR b with he | he
    · exact (show σ b = o from he) ▸ hc
    · exact False.elim ((not_lt_of_ge (hmax (σ b) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hc⟩))) he)
  have hcy : σ.IsCycleOn (↑(Finset.univ : Finset α) : Set α) := by
    rw [Finset.coe_univ]
    exact ⟨σ.bijective.bijOn_univ, fun a _ b _ => (hall a).trans (hall b).symm⟩
  let g := fun z : ZMod N => (σ ^ z.val) o
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨k,hk,he⟩ := hcy.exists_pow_eq (Finset.mem_univ o) (Finset.mem_univ a)
    refine ⟨k, ?_⟩
    change (σ ^ (k : ZMod N).val) o = a
    rw [c0_val_x (by simpa [hN] using hk), he]
  let e := Equiv.ofBijective g ((Fintype.bijective_iff_surjective_and_card g).mpr
    ⟨hg, by rw [ZMod.card, hN]⟩)
  refine ⟨e.symm, ?_⟩
  intro a
  obtain ⟨z,rfl⟩ := e.surjective a
  rw [e.symm_apply_apply]
  apply e.injective
  rw [e.apply_symm_apply]
  change σ ((σ ^ z.val) o) = (σ ^ (z+1).val) o
  rw [c0_val_inc, ← Equiv.Perm.mul_apply, ← pow_succ']
  split_ifs with hz
  · rw [hz, pow_zero]
    simpa [hN] using hcy.pow_card_apply (Finset.mem_univ o)
  · rfl


lemma c0_dec_val {m : ℕ} [NeZero m] (i : ZMod m) :
    (i-1).val+1=i.val ∨ (i.val=0 ∧ (i-1).val+1=m) := by
  have h := c0_val_inc (i-1)
  rw [sub_add_cancel] at h
  split_ifs at h <;> omega

lemma c0_surjA (m : ℕ) [NeZero m] (hm : Even m) (h8 : 8 ≤ m) :
    Function.Surjective (fun p : ZMod m × ZMod m => mv (hoA m p.1 p.2 0) p) := by
  rintro ⟨i,j⟩
  have he : m = 2*(m/2) := by obtain ⟨k,hk⟩ := hm; omega
  have hdir (u v : ZMod m) : (hoA m u v 0).val = c0_short m u.val v.val :=
    (c0_first_ok m u v).trans (c0_short_ok m _ _ he h8 u.val_lt v.val_lt)
  rcases c0_pred_short m i.val j.val (i-1).val (j-1).val h8 i.val_lt j.val_lt
    (c0_dec_val i) (c0_dec_val j) with h | h | h
  · have e : hoA m i j 0 = 2 := Fin.ext ((hdir _ _).trans h)
    exact ⟨(i,j), by simp [e, mv]⟩
  · have e : hoA m (i-1) j 0 = 0 := Fin.ext ((hdir _ _).trans h)
    exact ⟨(i-1,j), by simp [e, mv]⟩
  · have e : hoA m i (j-1) 0 = 1 := Fin.ext ((hdir _ _).trans h)
    exact ⟨(i,j-1), by simp [e, mv]⟩

lemma c0_surj (m : ℕ) [NeZero m] (hm : Even m) (h8 : 8 ≤ m) :
    Function.Surjective (retOf (hoA m) (hoB m) 0) := by
  have hB : Function.Surjective (fun p : ZMod m × ZMod m => mv (hoB m p.1 p.2 0) p) := by
    rintro ⟨i,j⟩
    by_cases h : i.val+1=m/2 ∨ i.val=m/2
    · exact ⟨(i,j), by simp [h, mv, hoB]⟩
    · exact ⟨(i,j-1), by simp [h, mv, hoB]⟩
  intro p
  obtain ⟨r,hr⟩ := hB p
  obtain ⟨q,hq⟩ := c0_surjA m hm h8 r
  refine ⟨(q.1+2,q.2), ?_⟩
  simpa [retOf, hq] using hr

/-- Étiquette de l'excursion sur les lignes hors section ; seule sa classe modulo trois compte. -/
def c0_col (m x y : ℕ) : ℕ :=
  let h := m/2
  if y+1=m then
    if x%2=1 then 0 else if x≤h then (if m%4=0 then 1 else 2) else (if m%4=0 then 2 else 1)
  else if y+2≤h then
    if x+y=h then 2*y+1 else if h < x+y ∧ x+1 < m then 2*y+2 else 2*y+3
  else if y+1=h then
    if x=1 then 2*h+2 else if x+1=m ∨ (m%4≠0 ∧ x=0) then 2*h+4 else 2*h+3
  else if y=h then
    if x=0 then (if m%4=0 then 2*h+3 else 2*h+4)
    else if m%4≠0 ∧ x+1=m then 2*h+3 else 2*h+2
  else if y=h+1 then
    if x+1=m then (if m%4=0 then 2*h+4 else 2*h+3) else (if m%4=0 then 2*h+3 else 2*h+4)
  else if y=h+2 ∧ m%4≠0 then
    if x+1=m then 2*h+3 else 2*h+2
  else
    let base := (if m%4=0 then 2 else 3) + 2*m+y
    if x+y < m+h then base else if x+y=m+h then base+2 else base+4

def c0_stage (m x y : ℕ) : ℕ :=
  if y=0 then
    if x < m/2 then 0 else if x+1=m then 6 else if x=m/2 then
      (if m%4=0 then 2 else 4) else (if m%4=0 then 4 else 2)
  else
    let i := c0_col m x y % 3
    if i=0 then 1 else if i=1 then (if m%4=0 then 3 else 5) else (if m%4=0 then 5 else 3)

def c0_ord (m x y : ℕ) : ℕ :=
  let h := m/2
  if y+1=m then (if x≤h ∧ x%2=1 then x+m else x)
  else if y+1=h ∧ m%4=0 then (if x=0 then m else x)
  else if y+1≤h then (if x+1=m then 0 else x+1)
  else if y=h+2 ∧ m%4≠0 then (if x+2=m then 0 else x+1) else x

def c0_key (m x y : ℕ) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (c0_stage m x y, toLex (y,c0_ord m x y))

lemma c0_dx0 : c0_dx 0 = 1 := rfl
lemma c0_dy0 : c0_dy 0 = 0 := rfl
lemma c0_dx1 : c0_dx 1 = 0 := rfl
lemma c0_dy1 : c0_dy 1 = 1 := rfl
lemma c0_dx2 : c0_dx 2 = 1 := rfl
lemma c0_dy2 : c0_dy 2 = 1 := rfl
lemma c0_dx3 : c0_dx 3 = 2 := rfl
lemma c0_dy3 : c0_dy 3 = 0 := rfl
lemma c0_dx4 : c0_dx 4 = 0 := rfl
lemma c0_dy4 : c0_dy 4 = 2 := rfl

lemma c0_colL {c : Prop} [Decidable c] {a b v : ℕ}
    (h : c → a%3 = v%3) (k : ¬c → b%3 = v%3) : (if c then a else b)%3 = v%3 :=
  c0_branch (fun t => t%3 = v%3) h k

lemma c0_colR {c : Prop} [Decidable c] {a b v : ℕ}
    (h : c → v%3 = a%3) (k : ¬c → v%3 = b%3) : v%3 = (if c then a else b)%3 :=
  c0_branch (fun t => v%3 = t%3) h k


lemma c0_colLY {c : Prop} [Decidable c] {a b v : ℕ} (h : c)
    (k : a%3 = v%3) : (if c then a else b)%3 = v%3 := by rwa [if_pos h]
lemma c0_colLN {c : Prop} [Decidable c] {a b v : ℕ} (h : ¬c)
    (k : b%3 = v%3) : (if c then a else b)%3 = v%3 := by rwa [if_neg h]
lemma c0_colRY {c : Prop} [Decidable c] {a b v : ℕ} (h : c)
    (k : v%3 = a%3) : v%3 = (if c then a else b)%3 := by rwa [if_pos h]
lemma c0_colRN {c : Prop} [Decidable c] {a b v : ℕ} (h : ¬c)
    (k : v%3 = b%3) : v%3 = (if c then a else b)%3 := by rwa [if_neg h]

set_option maxHeartbeats 4000000 in
lemma c0_col_path (m x y X Y : ℕ) (hm : m=2*(m/2)) (h8 : 8 ≤ m)
    (hx : x < m) (hy : y < m) (hX : X < m) (hY : Y < m) (hy0 : y ≠ 0) (hY0 : Y ≠ 0) :
    let d := c0_move m x y
    (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (Y=y+c0_dy d ∨ Y+m=y+c0_dy d) →
    c0_col m x y % 3 = c0_col m X Y % 3 := by
  let Q := fun d => (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (Y=y+c0_dy d ∨ Y+m=y+c0_dy d) →
    c0_col m x y % 3 = c0_col m X Y % 3
  change Q _
  by_cases hp : m%4=0
  all_goals simp only [c0_move, hp, ↓reduceIte]
  all_goals repeat' (apply c0_branch Q <;> intro)
  all_goals simp only [Q,c0_dx0, c0_dy0, c0_dx1, c0_dy1, c0_dx2, c0_dy2, c0_dx3, c0_dy3, c0_dx4, c0_dy4]
  all_goals intro ex ey
  all_goals try (exfalso; omega)
  all_goals simp only [c0_col, hp, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true,
    false_and, true_and, and_false, and_true, or_false, false_or]
  all_goals repeat' first
    | (apply c0_colLY; · omega)
    | (apply c0_colLN; · omega)
    | (apply c0_colL <;> intro)
    | (apply c0_colRY; · omega)
    | (apply c0_colRN; · omega)
    | (apply c0_colR <;> intro)
    | omega

lemma c0_move_zero (m x : ℕ) (h8 : 8 ≤ m) (hx : x < m) :
    c0_move m x 0 = if x+2=m then 2 else if x+1=m/2 ∨ x=m/2 then 1 else 0 := by
  unfold c0_move
  dsimp only
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
lemma c0_section_from (m x X Y : ℕ) (hm : m=2*(m/2)) (h8 : 8 ≤ m)
    (hx : x < m) (hX : X < m) (hY : Y < m) :
    let d := c0_move m x 0
    (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (Y=c0_dy d ∨ Y+m=c0_dy d) →
    X=0 ∧ Y=0 ∨ c0_key m x 0 < c0_key m X Y := by
  dsimp only
  rw [c0_move_zero m x h8 hx]
  by_cases hp : m%4=0
  all_goals by_cases h₂ : x+2=m
  all_goals by_cases h₁ : x+1=m/2
  all_goals by_cases h₀ : x=m/2
  all_goals try (exfalso; omega)
  all_goals simp (disch := omega) only [if_pos, if_neg, c0_dx0, c0_dy0, c0_dx1, c0_dy1, c0_dx2, c0_dy2, c0_dx3, c0_dy3, c0_dx4, c0_dy4]
  all_goals intro ex ey
  all_goals by_cases hl : x+1=m
  all_goals try (exfalso; omega)
  all_goals try (left; omega)
  all_goals right
  all_goals by_cases ha : x < m/2
  all_goals try (exfalso; omega)
  all_goals simp (disch := omega) only [c0_key, Prod.Lex.toLex_lt_toLex, c0_stage, c0_col,
    c0_ord, hp, ↓reduceIte, if_pos, if_neg, not_true_eq_false, not_false_eq_true,
    and_false, false_and, true_and, and_true, or_false, false_or] <;> omega

set_option maxHeartbeats 1000000 in
lemma c0_section_to (m x y X : ℕ) (hm : m=2*(m/2)) (h8 : 8 ≤ m)
    (hx : x < m) (hy : y < m) (hX : X < m) (hy0 : y ≠ 0) :
    let d := c0_move m x y
    (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (0=y+c0_dy d ∨ m=y+c0_dy d) →
    c0_key m x y < c0_key m X 0 := by
  let Q := fun d => (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (0=y+c0_dy d ∨ m=y+c0_dy d) →
    c0_key m x y < c0_key m X 0
  change Q _
  unfold c0_move
  dsimp only
  repeat' (apply c0_branch Q <;> intro)
  all_goals simp only [Q,c0_dx0, c0_dy0, c0_dx1, c0_dy1, c0_dx2, c0_dy2, c0_dx3, c0_dy3, c0_dx4, c0_dy4]
  all_goals intro ex ey
  all_goals try (exfalso; omega)
  all_goals by_cases hp : m%4=0
  all_goals by_cases h₂ : x+2=m
  all_goals by_cases h₁ : x+1=m/2
  all_goals by_cases h₀ : x=m/2
  all_goals try (exfalso; omega)
  all_goals simp (disch := omega) only [c0_key, Prod.Lex.toLex_lt_toLex, c0_stage, c0_col,
    c0_ord, hp, ↓reduceIte, if_pos, if_neg, not_true_eq_false, not_false_eq_true,
    and_false, false_and, true_and, and_true, or_false, false_or] <;> omega

set_option maxHeartbeats 1500000 in
lemma c0_ord_path (m x y X Y : ℕ) (hm : m=2*(m/2)) (h8 : 8 ≤ m)
    (hx : x < m) (hy : y < m) (hX : X < m) (hY : Y < m) (hY0 : Y ≠ 0) :
    let d := c0_move m x y
    (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (Y=y+c0_dy d ∨ Y+m=y+c0_dy d) →
    y < Y ∨ y=Y ∧ c0_ord m x y < c0_ord m X Y := by
  let Q := fun d => (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (Y=y+c0_dy d ∨ Y+m=y+c0_dy d) →
    y < Y ∨ y=Y ∧ c0_ord m x y < c0_ord m X Y
  change Q _
  unfold c0_move
  dsimp only
  repeat' (apply c0_branch Q <;> intro)
  all_goals simp only [Q,c0_dx0, c0_dy0, c0_dx1, c0_dy1, c0_dx2, c0_dy2, c0_dx3, c0_dy3, c0_dx4, c0_dy4]
  all_goals intro ex ey
  all_goals first | (left; omega) | (right; constructor; · omega)
  all_goals have hh : Y = y := by omega
  all_goals subst Y
  all_goals unfold c0_ord
  all_goals dsimp only
  all_goals split_ifs <;> omega

lemma c0_key_path (m x y X Y : ℕ) (hm : m=2*(m/2)) (h8 : 8 ≤ m)
    (hx : x < m) (hy : y < m) (hX : X < m) (hY : Y < m) :
    let d := c0_move m x y
    (X=x+c0_dx d ∨ X+m=x+c0_dx d) → (Y=y+c0_dy d ∨ Y+m=y+c0_dy d) →
    X=0 ∧ Y=0 ∨ c0_key m x y < c0_key m X Y := by
  dsimp only
  intro ex ey
  by_cases hy0 : y=0
  · subst y
    exact c0_section_from m x X Y hm h8 hx hX hY ex (by simpa using ey)
  by_cases hY0 : Y=0
  · subst Y
    exact Or.inr (c0_section_to m x y X hm h8 hx hy hX hy0 ex (by simpa using ey))
  right
  have hc := c0_col_path m x y X Y hm h8 hx hy hX hY hy0 hY0 ex ey
  have hs : c0_stage m x y = c0_stage m X Y := by simp only [c0_stage, hy0,hY0,if_false,hc]
  simp only [c0_key, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨hs,c0_ord_path m x y X Y hm h8 hx hy hX hY hY0 ex ey⟩

lemma c0_wrap (m u : ℕ) (hu : u < 2*m) : u%m = u ∨ u%m+m = u := by
  by_cases h : u < m
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma c0_dsmall (m x y : ℕ) : c0_dx (c0_move m x y) ≤ 2 ∧ c0_dy (c0_move m x y) ≤ 2 := by
  let P := fun d => c0_dx d ≤ 2 ∧ c0_dy d ≤ 2
  change P _
  unfold c0_move
  dsimp only
  repeat' (apply c0_branch P <;> intro)
  all_goals decide

lemma c0_xpt (m x y : ℕ) [NeZero m] : (c0_pt m x y).2.val = x%m :=
  ZMod.val_natCast _ _

lemma c0_ypt (m x y : ℕ) [NeZero m] :
    (-(c0_pt m x y).1 - (c0_pt m x y).2).val = y%m := by
  change (-(-(x : ZMod m) - y) - x).val = _
  rw [show -(-(x : ZMod m) - y) - x = y by ring, ZMod.val_natCast]

lemma c0_pt0 (m x y : ℕ) [NeZero m] (hx : x%m=0) (hy : y%m=0) :
    c0_pt m x y = c0_pt m 0 0 := by
  have hx' : (x : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hx)
  have hy' : (y : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hy)
  simp [c0_pt, hx',hy']

/-- couleur 0 (GPT26 §5). -/
theorem hoCert0 (m : ℕ) [NeZero m] (hm : Even m) (h8 : 8 ≤ m) :
    ∃ pos : ZMod m × ZMod m → ZMod (m ^ 2),
      ∀ p, pos (retOf (hoA m) (hoB m) 0 p) = pos p + 1 := by
  let R := fun p : ZMod m × ZMod m => c0_key m p.2.val (-p.1-p.2).val
  apply c0_rank_cert (m^2) (by simp [pow_two]) _ (c0_surj m hm h8) (c0_pt m 0 0) R
  intro p
  let x := p.2.val
  let y := (-p.1-p.2).val
  have hx : x < m := ZMod.val_lt _
  have hy : y < m := ZMod.val_lt _
  have he : m = 2*(m/2) := by obtain ⟨k,hk⟩ := hm; omega
  have hp : p = c0_pt m x y := by
    apply Prod.ext
    · simp [c0_pt, x,y]; ring
    · simp [c0_pt, x]
  let d := c0_move m x y
  obtain ⟨hdx,hdy⟩ := c0_dsmall m x y
  have hwx := c0_wrap m (x+c0_dx d) (by dsimp [d]; omega)
  have hwy := c0_wrap m (y+c0_dy d) (by dsimp [d]; omega)
  have h1 := Nat.mod_lt (x+c0_dx d) (by omega : 0 < m)
  have h2 := Nat.mod_lt (y+c0_dy d) (by omega : 0 < m)
  have hk := c0_key_path m x y _ _ he h8 hx hy h1 h2 hwx hwy
  have hret : retOf (hoA m) (hoB m) 0 p = c0_pt m (x+c0_dx d) (y+c0_dy d) := by
    calc
      _ = retOf (hoA m) (hoB m) 0 (c0_pt m x y) := congrArg _ hp
      _ = _ := c0_ret m x y hm h8 hx hy
  rw [hret]
  rcases hk with ⟨ex,ey⟩ | lt
  · exact Or.inl (c0_pt0 m _ _ ex ey)
  · right
    simpa only [R,c0_xpt,c0_ypt] using lt

theorem hoDecomp (m : ℕ) [NeZero m] (hm : Even m) (h8 : 8 ≤ m) :
    HasHamiltonianArcDecomposition m := by
  refine decomp_of_certs (by omega) (hoA m) (hoB m) ?_
  intro c
  fin_cases c
  · exact hoCert0 m hm h8
  · exact hoCert1 m hm h8
  · exact hoCert2 m hm h8

end OMAClaude

theorem OMA.solution : type_of% @ClaudesCycles.cube_hamiltonian_arc_decomposition_even := by
  intro m _ hm h2
  obtain ⟨k, rfl⟩ := hm
  rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | hk
  · exact OMAClaude.small4
  · exact OMAClaude.small6
  · exact OMAClaude.hoDecomp (k + k) ⟨k, rfl⟩ (by omega)
