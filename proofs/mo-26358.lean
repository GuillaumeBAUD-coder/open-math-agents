import OMAStatements.S_mo_26358

/-!
There is no rainbow-cascade coloring with 211 colors.

The reduction from colorings to cyclic logarithms follows Wang and Wang,
*Obstructions to coloring arithmetic graphs*, Theorem 3.1 and Corollary 3.3
(https://arxiv.org/abs/2609.15081). Blackburn and McKee reported the finite
logarithm obstruction in *Constructing k-radius sequences*, Section 9.3
(https://doi.org/10.1090/S0025-5718-2011-02510-X).

The finite search needs only labels whose prime factors are at most 41.
After normalizing the logarithm of 2 to 1, doubling a label increments its
residue by 1. Accordingly the search groups these labels into consecutive
runs of residues. The checked branches cover every value of the logarithm of 3.

Credit: @wtho704
-/

open scoped BigOperators
open Finset Polynomial

namespace OMA.RainbowCascade

private def multiplier {q : ℕ} (i : Fin q) : ℕ+ := ⟨i.val + 1, Nat.succ_pos _⟩

private def dilation (R : Type*) [CommSemiring R] : ℕ+ →* Module.End R (ℕ+ → R) where
  toFun a :=
    { toFun := fun f b => f (b * a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext b
    change f (b * 1) = f b
    rw [mul_one]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    funext x
    change f (x * (a * b)) = f (x * a * b)
    rw [mul_assoc]

private noncomputable def act (R : Type*) [CommSemiring R] :
    MonoidAlgebra R ℕ+ →ₐ[R] Module.End R (ℕ+ → R) :=
  MonoidAlgebra.lift R (Module.End R (ℕ+ → R)) ℕ+ (dilation R)

private noncomputable def tile (R : Type*) [CommSemiring R] (q : ℕ) : MonoidAlgebra R ℕ+ :=
  ∑ i : Fin q, MonoidAlgebra.of R ℕ+ (multiplier i)

@[simp] private lemma act_of (R : Type*) [CommSemiring R] (a : ℕ+) (f : ℕ+ → R) (b : ℕ+) :
    act R (MonoidAlgebra.of R ℕ+ a) f b = f (b * a) := by
  rw [act, MonoidAlgebra.lift_of]
  rfl

@[simp] private lemma act_tile {R : Type*} [CommSemiring R] (q : ℕ) (f : ℕ+ → R) (b : ℕ+) :
    act R (tile R q) f b = ∑ i : Fin q, f (b * multiplier i) := by
  simp only [tile, map_sum, LinearMap.sum_apply, Finset.sum_apply, act_of]

private lemma indicator_sum {R : Type*} [CommSemiring R] {q : ℕ} (c : ℕ+ → Fin q)
    (hc : ∀ a, Function.Injective fun i : Fin q => c (a * multiplier i)) (a : ℕ+) (j : Fin q) :
    (∑ i : Fin q, if c (a * multiplier i) = j then (1 : R) else 0) = 1 := by
  let e := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (hc a))
  change (∑ i : Fin q, if e i = j then (1 : R) else 0) = 1
  exact (Equiv.sum_comp e (fun k => if k = j then (1 : R) else 0)).trans (by simp)

private lemma chi_periodic {q : ℕ} [Fact q.Prime] (c : ℕ+ → Fin q)
    (hc : ∀ a, Function.Injective fun i : Fin q => c (a * multiplier i)) :
    ∀ (a : ℕ+) (i : Fin q), c (a * multiplier i ^ q) = c a := by
  have hAlg : Function.Injective (algebraMap (ZMod q) (MonoidAlgebra (ZMod q) ℕ+)) := by
    intro u v h
    have he := congrArg (fun f : MonoidAlgebra (ZMod q) ℕ+ => f.coeff 1) h
    simpa [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.coeff_single, Finsupp.single_apply] using he
  have : ExpChar (MonoidAlgebra (ZMod q) ℕ+) q :=
    expChar_of_injective_algebraMap hAlg q
  intro a i
  let indicator (b : ℕ+) : ZMod q := if c b = c a then 1 else 0
  let S := act (ZMod q) (tile (ZMod q) q)
  have hS : S indicator = fun _ => 1 := by
    funext b
    simpa [S, indicator] using (indicator_sum (R := ZMod q) c hc b (c a))
  have hconst : S (fun _ => 1) = 0 := by
    funext b
    simp [S]
  have hpow : S ^ q = S ^ (q - 2) * (S * S) := by
    rw [← pow_two, ← pow_add, Nat.sub_add_cancel (Fact.out : Nat.Prime q).two_le]
  have hkill : (S ^ q) indicator = 0 := by
    rw [hpow, Module.End.mul_apply, Module.End.mul_apply, hS, hconst, map_zero]
  have hsum : (∑ k : Fin q, indicator (a * multiplier k ^ q)) = 0 := by
    have hv := congrFun hkill a
    change ((act (ZMod q) (tile (ZMod q) q)) ^ q) indicator a = 0 at hv
    rw [← map_pow, tile, sum_pow_char, map_sum, LinearMap.sum_apply, Finset.sum_apply] at hv
    simp only [← map_pow, act_of] at hv
    exact hv
  let matching := (univ : Finset (Fin q)).filter (fun k => c (a * multiplier k ^ q) = c a)
  have hm : (matching.card : ZMod q) = 0 := by
    simpa only [matching, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, indicator] using hsum
  have hd : q ∣ matching.card := (ZMod.natCast_eq_zero_iff _ _).mp hm
  have h0 : (⟨0, (Fact.out : Nat.Prime q).pos⟩ : Fin q) ∈ matching := by
    have h1 : multiplier (⟨0, (Fact.out : Nat.Prime q).pos⟩ : Fin q) = 1 := rfl
    exact mem_filter.mpr ⟨mem_univ _, by rw [h1, one_pow, mul_one]⟩
  have hle : matching.card ≤ q := by simpa using card_le_univ matching
  have he : matching = univ := by
    apply eq_univ_of_card
    simpa using le_antisymm hle (Nat.le_of_dvd (card_pos.mpr ⟨_, h0⟩) hd)
  exact (mem_filter.mp (he.symm ▸ mem_univ i : i ∈ matching)).2

private lemma act_dilation_mul (a b : ℕ+) (f : ℕ+ → ℂ) :
    act ℂ (MonoidAlgebra.of ℂ ℕ+ (a * b)) f =
      act ℂ (MonoidAlgebra.of ℂ ℕ+ a) (act ℂ (MonoidAlgebra.of ℂ ℕ+ b) f) := by
  rw [map_mul (MonoidAlgebra.of ℂ ℕ+), map_mul, Module.End.mul_apply]

private lemma act_comm (u v : MonoidAlgebra ℂ ℕ+) (f : ℕ+ → ℂ) :
    act ℂ u (act ℂ v f) = act ℂ v (act ℂ u f) := by
  calc
    _ = act ℂ (u * v) f := by rw [map_mul, Module.End.mul_apply]
    _ = act ℂ (v * u) f := by rw [mul_comm]
    _ = _ := by rw [map_mul, Module.End.mul_apply]

private lemma find_eigenvalue {q : ℕ} {ζ : ℂ} (hq : 0 < q) (hz : IsPrimitiveRoot ζ q)
    (m : ℕ+) (f : ℕ+ → ℂ) (hf : f ≠ 0)
    (hperiod : act ℂ (MonoidAlgebra.of ℂ ℕ+ m ^ q) f = f) :
    ∃ j : Fin q, ∃ u : MonoidAlgebra ℂ ℕ+,
      act ℂ u f ≠ 0 ∧ act ℂ (MonoidAlgebra.of ℂ ℕ+ m) (act ℂ u f) = ζ ^ j.val • act ℂ u f := by
  classical
  let d := MonoidAlgebra.of ℂ ℕ+ m
  let factor (z : ℂ) := d - algebraMap ℂ (MonoidAlgebra ℂ ℕ+) z
  have hfactor : d ^ q - 1 = ∏ z ∈ nthRootsFinset q (1 : ℂ), factor z := by
    simpa [factor] using congrArg (aeval d) (X_pow_sub_one_eq_prod hq hz)
  have hann : act ℂ (∏ z ∈ nthRootsFinset q (1 : ℂ), factor z) f = 0 := by
    rw [← hfactor, map_sub, LinearMap.sub_apply, map_one, Module.End.one_apply, hperiod, sub_self]
  have find (s : Finset ℂ) (h : act ℂ (∏ z ∈ s, factor z) f = 0) :
      ∃ z ∈ s, ∃ u : MonoidAlgebra ℂ ℕ+,
        act ℂ u f ≠ 0 ∧ act ℂ d (act ℂ u f) = z • act ℂ u f := by
    induction s using Finset.induction_on with
    | empty => simp [hf] at h
    | insert z s hzs ih =>
      let u := ∏ w ∈ s, factor w
      by_cases hu : act ℂ u f = 0
      · obtain ⟨w, hw, v, hn, hv⟩ := ih hu
        exact ⟨w, mem_insert_of_mem hw, v, hn, hv⟩
      · rw [prod_insert hzs, map_mul, Module.End.mul_apply] at h
        change act ℂ (factor z) (act ℂ u f) = 0 at h
        refine ⟨z, mem_insert_self z s, u, hu, ?_⟩
        change act ℂ (d - algebraMap ℂ _ z) (act ℂ u f) = 0 at h
        rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, sub_eq_zero] at h
        simpa using h
  obtain ⟨z, hzmem, u, hu, huv⟩ := find _ hann
  let : NeZero q := ⟨hq.ne'⟩
  obtain ⟨j, hj, rfl⟩ := hz.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hq (1 : ℂ)).mp hzmem)
  exact ⟨⟨j, hj⟩, u, hu, huv⟩

private lemma joint_eigenfunction {q : ℕ} {ζ : ℂ} (hq : 0 < q) (hz : IsPrimitiveRoot ζ q)
    (f : ℕ+ → ℂ) (hf : f ≠ 0) (hzero : act ℂ (tile ℂ q) f = 0)
    (hperiod : ∀ i : Fin q, act ℂ (MonoidAlgebra.of ℂ ℕ+ (multiplier i) ^ q) f = f) :
    ∃ g : ℕ+ → ℂ, g ≠ 0 ∧ act ℂ (tile ℂ q) g = 0 ∧
      ∃ e : Fin q → Fin q, ∀ i, act ℂ (MonoidAlgebra.of ℂ ℕ+ (multiplier i)) g = ζ ^ (e i).val • g := by
  classical
  let d (i : Fin q) := MonoidAlgebra.of ℂ ℕ+ (multiplier i)
  have build (s : Finset (Fin q)) :
      ∃ g : ℕ+ → ℂ, g ≠ 0 ∧ act ℂ (tile ℂ q) g = 0 ∧
        (∀ i : Fin q, act ℂ (d i ^ q) g = g) ∧
        ∀ i ∈ s, ∃ j : Fin q, act ℂ (d i) g = ζ ^ j.val • g := by
    induction s using Finset.induction_on with
    | empty => exact ⟨f, hf, hzero, hperiod, by simp⟩
    | insert i s hi ih =>
      obtain ⟨g, hg, hgzero, hgperiod, hprev⟩ := ih
      obtain ⟨e, u, hnew, he⟩ := find_eigenvalue hq hz (multiplier i) g hg (hgperiod i)
      refine ⟨act ℂ u g, hnew, ?_, ?_, ?_⟩
      · rw [act_comm, hgzero, map_zero]
      · intro j
        rw [act_comm, hgperiod]
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · exact ⟨e, he⟩
        · obtain ⟨a, ha⟩ := hprev j hj
          exact ⟨a, by rw [act_comm, ha, LinearMap.map_smul]⟩
  obtain ⟨g, hg, hgzero, _, hprev⟩ := build univ
  choose e he using fun i => hprev i (mem_univ i)
  exact ⟨g, hg, hgzero, e, he⟩

private lemma powers_injective {q : ℕ} {ζ : ℂ} (hp : q.Prime) (hζ : IsPrimitiveRoot ζ q)
    (e : Fin q → Fin q) (hsum : ∑ i, ζ ^ (e i).val = 0) : Function.Injective e := by
  classical
  let count (j : Fin q) : ℤ := ∑ i : Fin q, if e i = j then 1 else 0
  have hor : ∑ j : Fin q, (count j : ℂ) * ζ ^ j.val = 0 := by
    simp only [count, Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero, sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, if_true, one_mul]
    exact hsum
  have heq := (hζ.sum_eq_zero_iff_forall_eq_int hp count).mp hor
  have hs : Function.Surjective e := by
    intro j
    let k : Fin q := ⟨0, hp.pos⟩
    by_contra! hn
    have hz : count j = 0 := by simp [count, hn]
    have hpos : 1 ≤ count (e k) := by
      calc
        1 = (if e k = e k then 1 else 0 : ℤ) := by simp
        _ ≤ _ := single_le_sum (f := fun i => if e i = e k then (1 : ℤ) else 0)
            (fun i _ => by split <;> norm_num) (mem_univ k)
    rw [heq (e k) j, hz] at hpos
    norm_num at hpos
  exact Finite.injective_iff_surjective.mpr hs

private def IsLogarithm (q : ℕ) (h : ℕ → ZMod q) : Prop :=
  Set.InjOn h (Set.Icc 1 q) ∧ h 1 = 0 ∧
    ∀ a b, 0 < a → 0 < b → a * b ≤ q → h (a * b) = h a + h b

private lemma logarithm_of_coloring {q : ℕ} (hp : q.Prime) (c : ℕ+ → Fin q)
    (hc : ∀ a, Function.Injective fun i : Fin q => c (a * multiplier i)) :
    ∃ h : ℕ → ZMod q, IsLogarithm q h := by
  classical
  have : Fact q.Prime := ⟨hp⟩
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hp.ne_zero
  let f (a : ℕ+) : ℂ := (if c a = c 1 then (q : ℂ) else 0) - 1
  have hqne : (q : ℂ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hf : f ≠ 0 := by
    intro h
    have e := congrFun h 1
    exact hqne (sub_eq_zero.mp (by simpa [f] using e))
  have hzero : act ℂ (tile ℂ q) f = 0 := by
    funext a
    have hscaled := congrArg (fun x : ℂ => x * (q : ℂ))
      (indicator_sum (R := ℂ) c hc a (c 1))
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul] at hscaled
    simp [f, sum_sub_distrib, hscaled]
  have hperiod (i : Fin q) : act ℂ (MonoidAlgebra.of ℂ ℕ+ (multiplier i) ^ q) f = f := by
    funext a
    rw [← map_pow, act_of]
    simp [f, chi_periodic c hc]
  obtain ⟨g, hg, hgzero, e, he⟩ := joint_eigenfunction hp.pos hζ f hf hzero hperiod
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
    by_contra! hh
    exact hg (funext hh)
  have hsum : ∑ i : Fin q, ζ ^ (e i).val = 0 := by
    have hxzero := congrFun hgzero x
    unfold tile at hxzero
    simp only [map_sum, LinearMap.sum_apply, he, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, ← sum_mul] at hxzero
    exact (mul_eq_zero.mp hxzero).resolve_right hx
  have hinj := powers_injective hp hζ e hsum
  let expn (n : ℕ) : ℕ := if h : 0 < n ∧ n ≤ q then (e ⟨n - 1, by omega⟩).val else 0
  let h (n : ℕ) : ZMod q := expn n
  have bounded (n : ℕ) (hn : 0 < n) (hnq : n ≤ q) : expn n < q := by
    simp only [expn, dif_pos (show 0 < n ∧ n ≤ q from ⟨hn, hnq⟩)]
    exact Fin.isLt _
  have heigen (n : ℕ) (hn : 0 < n) (hnq : n ≤ q) :
      act ℂ (MonoidAlgebra.of ℂ ℕ+ ⟨n, hn⟩) g = ζ ^ expn n • g := by
    have hindex : multiplier (⟨n-1, by omega⟩ : Fin q) = ⟨n, hn⟩ := by
      apply Subtype.ext
      change n - 1 + 1 = n
      omega
    simpa [expn, dif_pos (show 0 < n ∧ n ≤ q from ⟨hn, hnq⟩), hindex] using he (⟨n - 1, by omega⟩ : Fin q)
  have hmul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a * b ≤ q) :
      h (a * b) = h a + h b := by
    have haq : a ≤ q := (Nat.le_mul_of_pos_right a hb).trans hab
    have hbq : b ≤ q := (Nat.le_mul_of_pos_left b ha).trans hab
    let ofPNat := MonoidAlgebra.of ℂ ℕ+
    have huv : (⟨a * b, Nat.mul_pos ha hb⟩ : ℕ+) = (⟨a, ha⟩ : ℕ+) * (⟨b, hb⟩ : ℕ+) := rfl
    have hs : ζ ^ expn (a * b) • g = ζ ^ (expn a + expn b) • g := by
      calc
        ζ ^ expn (a * b) • g = act ℂ (ofPNat ⟨a * b, Nat.mul_pos ha hb⟩) g :=
          (heigen _ _ hab).symm
        _ = act ℂ (ofPNat ⟨a, ha⟩) (act ℂ (ofPNat ⟨b, hb⟩) g) := by
          exact (congrArg (fun m : ℕ+ => act ℂ (ofPNat m) g) huv).trans
            (act_dilation_mul (⟨a, ha⟩ : ℕ+) (⟨b, hb⟩ : ℕ+) g)
        _ = ζ ^ (expn a + expn b) • g := by
          rw [heigen b hb hbq, LinearMap.map_smul, heigen a ha haq, smul_smul, pow_add, mul_comm]
    have hpow : ζ ^ expn (a * b) = ζ ^ (expn a + expn b) :=
      mul_right_cancel₀ hx (congrFun hs x)
    have hm : expn (a * b) ≡ expn a + expn b [MOD q] := by
      rw [hζ.eq_orderOf]
      exact (hζ.isOfFinOrder hp.ne_zero).pow_eq_pow_iff_modEq.mp hpow
    have hcast := (ZMod.natCast_eq_natCast_iff _ _ q).mpr hm
    simpa [h, Nat.cast_add] using hcast
  refine ⟨h, ?_, ?_, hmul⟩
  · intro a ha b hb heq
    rw [Set.mem_Icc] at ha hb
    have ha0 : 0 < a := by omega
    have hb0 : 0 < b := by omega
    have heq' := congrArg ZMod.val heq
    change (↑(expn a) : ZMod q).val = (↑(expn b) : ZMod q).val at heq'
    rw [ZMod.val_natCast_of_lt (bounded a ha0 ha.2), ZMod.val_natCast_of_lt (bounded b hb0 hb.2)] at heq'
    have heq'' : (e (⟨a - 1, by omega⟩ : Fin q)).val = (e (⟨b - 1, by omega⟩ : Fin q)).val := by
      simpa only [expn, dif_pos (show 0 < a ∧ a ≤ q from ⟨ha0, ha.2⟩), dif_pos (show 0 < b ∧ b ≤ q from ⟨hb0, hb.2⟩)] using heq'
    have := congrArg Fin.val (hinj (Fin.ext heq''))
    change a - 1 = b - 1 at this
    omega
  · have ha := hmul 1 1 (by decide) (by decide) (by simpa using hp.one_lt.le)
    simp only [mul_one, left_eq_add] at ha
    exact ha



private structure Entry where
  label : ℕ
  cofactor : ℕ
  exponent : ℕ
  deriving DecidableEq

private structure Batch where
  prime : ℕ
  linear : List Entry
  higher : List Entry
  runs : List (ℕ × ℕ)
  saved : List Entry
  deriving Inhabited

private def Batch.entries (b : Batch) : List Entry := b.linear ++ b.higher

private structure SearchState where
  used : ℕ
  packed : ℕ

private def getResidue (s : SearchState) (n : ℕ) : ℕ :=
  Nat.land 255 (Nat.shiftRight s.packed (Nat.mul 8 n))

private def writeResidue (u n v : ℕ) : ℕ :=
  let slot := Nat.shiftLeft 255 (Nat.mul 8 n)
  Nat.lor (Nat.xor u (Nat.land u slot)) (Nat.shiftLeft v (Nat.mul 8 n))

private def initial : SearchState := ⟨1, 0⟩

private def forceNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n + 1 => f (n + 1)

/-- The bit mask with bits 0 through 210 set. -/
private def full : ℕ := 3291009114642412084309938365114701009965471731267159726697218047

/-- Three consecutive copies of the unused-residue mask. -/
private def periodicFree (used : ℕ) : ℕ :=
  Nat.mul (Nat.xor full used) 10830740992659433045228180406808920716548582325686783496759685865066873598258137174309838388958996236908406149085142429154148353

private def modulo211 (n : ℕ) : ℕ := Nat.mod n 211

private def packedToMask (n : ℕ) : ℕ := Nat.lor (Nat.land n full) (Nat.shiftRight n 211)

private def windowTwo (u : ℕ) : ℕ := Nat.land u (Nat.shiftRight u 1)

private def windowThree (u t : ℕ) : ℕ := Nat.land t (Nat.shiftRight u 2)

private def windowFive (u t : ℕ) : ℕ := Nat.land (Nat.land t (Nat.shiftRight t 2)) (Nat.shiftRight u 4)

private def runWindow (u : ℕ) (len : ℕ) : ℕ :=
  let pair := windowTwo u
  let triple := windowThree u pair
  let four := Nat.land pair (Nat.shiftRight pair 2)
  match len with
  | 1 => u
  | 2 => pair
  | 3 => triple
  | 4 => four
  | 5 => windowFive u pair
  | 6 => Nat.land four (Nat.shiftRight pair 4)
  | _ => Nat.land four (Nat.shiftRight triple 4)

/-- The low 211 bits enumerate shifts whose translated runs avoid the used residues. -/
private def freeOffsets (state : SearchState) (runs : List (ℕ × ℕ)) : ℕ :=
  forceNat (periodicFree state.used) fun free => loop state free runs full
where
  loop (state : SearchState) (free : ℕ) : List (ℕ × ℕ) → ℕ → ℕ
    | [], allowed => allowed
    | (cofactor, len) :: rest, allowed =>
      bif Nat.beq allowed 0 then 0 else
        loop state free rest (Nat.land allowed
          (Nat.shiftRight (runWindow free len) (getResidue state cofactor)))

private def anyMarked : ℕ → ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, start, bits, test => bif Nat.beq bits 0 then false else test start
  | depth + 1, start, bits, test =>
    bif Nat.beq bits 0 then false else
      let half := Nat.pow 2 depth
      bif anyMarked depth start (Nat.mod bits (Nat.pow 2 half)) test then true else
        anyMarked depth (Nat.add start half) (Nat.shiftRight bits half) test

private def bitOn (n i : ℕ) : Bool :=
  Bool.not (Nat.beq (Nat.land 1 (Nat.shiftRight n i)) 0)

/-- Cofactor labels whose residues can be read by a later batch. -/
private def store (n : ℕ) : Bool :=
  Nat.testBit 18446744147983720446 n

private def place (w : ℕ) : List Entry → SearchState → Option SearchState
  | [], state => some state
  | row :: rows, state =>
    forceNat (Nat.mod (Nat.add (getResidue state row.cofactor) (Nat.mul row.exponent w)) 211) fun v =>
      bif bitOn state.used v then none
      else place w rows ⟨Nat.lor state.used (Nat.shiftLeft 1 v),
        bif store row.label then writeResidue state.packed row.label v else state.packed⟩

private def linearMask (state : SearchState) (runs : List (ℕ × ℕ)) : ℕ :=
  let both := runs.foldl (fun mask (n, len) =>
    Nat.lor mask (Nat.shiftLeft (Nat.sub (Nat.pow 2 len) 1) (getResidue state n))) 0
  packedToMask both

private def writeLinear (state : SearchState) (rows : List Entry) (w : ℕ) : ℕ :=
  rows.foldl (fun packed row =>
    writeResidue packed row.label (Nat.mod (Nat.add (getResidue state row.cofactor) w) 211)) state.packed

private def shiftedMask (mask w : ℕ) : ℕ :=
  Nat.mod (Nat.shiftLeft mask w) full

private def shiftedMaskClassic (mask w : ℕ) : ℕ :=
  ((mask <<< w) ||| (mask >>> (211-w))) &&& full

private def search : List Batch → SearchState → Bool
  | [], _ => true
  | b :: rest, state =>
    forceNat state.used fun used =>
      forceNat state.packed fun packed =>
        let state := (⟨used, packed⟩ : SearchState)
        let offsets := freeOffsets state b.runs
        bif Nat.beq offsets 0 then false else
          forceNat (linearMask state b.runs) fun mask =>
            anyMarked 8 0 offsets fun w =>
              let next : SearchState := ⟨Nat.lor used (shiftedMask mask w), writeLinear state b.saved w⟩
              match place w b.higher next with
              | none => false
              | some next => search rest next

private def batches : List Batch := [
  ⟨2, [⟨2, 1, 1⟩],
    [⟨4, 1, 2⟩, ⟨8, 1, 3⟩, ⟨16, 1, 4⟩, ⟨32, 1, 5⟩, ⟨64, 1, 6⟩, ⟨128, 1, 7⟩], [(1, 1)], [⟨2, 1, 1⟩]⟩,
  ⟨3, [⟨3, 1, 1⟩, ⟨6, 2, 1⟩, ⟨12, 4, 1⟩, ⟨24, 8, 1⟩, ⟨48, 16, 1⟩, ⟨96, 32, 1⟩, ⟨192, 64, 1⟩],
    [⟨9, 1, 2⟩, ⟨27, 1, 3⟩, ⟨81, 1, 4⟩, ⟨18, 2, 2⟩, ⟨54, 2, 3⟩, ⟨162, 2, 4⟩, ⟨36, 4, 2⟩, ⟨108, 4, 3⟩, ⟨72, 8, 2⟩, ⟨144, 16, 2⟩], [(1, 7)], [⟨3, 1, 1⟩, ⟨6, 2, 1⟩, ⟨12, 4, 1⟩, ⟨24, 8, 1⟩]⟩,
  ⟨5, [⟨5, 1, 1⟩, ⟨10, 2, 1⟩, ⟨15, 3, 1⟩, ⟨20, 4, 1⟩, ⟨30, 6, 1⟩, ⟨40, 8, 1⟩, ⟨45, 9, 1⟩, ⟨60, 12, 1⟩, ⟨80, 16, 1⟩, ⟨90, 18, 1⟩, ⟨120, 24, 1⟩, ⟨135, 27, 1⟩, ⟨160, 32, 1⟩, ⟨180, 36, 1⟩],
    [⟨25, 1, 2⟩, ⟨125, 1, 3⟩, ⟨50, 2, 2⟩, ⟨75, 3, 2⟩, ⟨100, 4, 2⟩, ⟨150, 6, 2⟩, ⟨200, 8, 2⟩], [(1, 6), (3, 4), (9, 3), (27, 1)], [⟨5, 1, 1⟩, ⟨10, 2, 1⟩, ⟨15, 3, 1⟩, ⟨20, 4, 1⟩, ⟨30, 6, 1⟩]⟩,
  ⟨7, [⟨7, 1, 1⟩, ⟨14, 2, 1⟩, ⟨21, 3, 1⟩, ⟨28, 4, 1⟩, ⟨35, 5, 1⟩, ⟨42, 6, 1⟩, ⟨56, 8, 1⟩, ⟨63, 9, 1⟩, ⟨70, 10, 1⟩, ⟨84, 12, 1⟩, ⟨105, 15, 1⟩, ⟨112, 16, 1⟩, ⟨126, 18, 1⟩, ⟨140, 20, 1⟩, ⟨168, 24, 1⟩, ⟨175, 25, 1⟩, ⟨189, 27, 1⟩, ⟨210, 30, 1⟩],
    [⟨49, 1, 2⟩, ⟨98, 2, 2⟩, ⟨147, 3, 2⟩, ⟨196, 4, 2⟩], [(1, 5), (3, 4), (5, 3), (9, 2), (15, 2), (25, 1), (27, 1)], [⟨7, 1, 1⟩, ⟨14, 2, 1⟩]⟩,
  ⟨11, [⟨11, 1, 1⟩, ⟨22, 2, 1⟩, ⟨33, 3, 1⟩, ⟨44, 4, 1⟩, ⟨55, 5, 1⟩, ⟨66, 6, 1⟩, ⟨77, 7, 1⟩, ⟨88, 8, 1⟩, ⟨99, 9, 1⟩, ⟨110, 10, 1⟩, ⟨132, 12, 1⟩, ⟨154, 14, 1⟩, ⟨165, 15, 1⟩, ⟨176, 16, 1⟩, ⟨198, 18, 1⟩],
    [⟨121, 1, 2⟩], [(1, 5), (3, 3), (5, 2), (7, 2), (9, 2), (15, 1)], [⟨11, 1, 1⟩]⟩,
  ⟨13, [⟨13, 1, 1⟩, ⟨26, 2, 1⟩, ⟨39, 3, 1⟩, ⟨52, 4, 1⟩, ⟨65, 5, 1⟩, ⟨78, 6, 1⟩, ⟨91, 7, 1⟩, ⟨104, 8, 1⟩, ⟨117, 9, 1⟩, ⟨130, 10, 1⟩, ⟨143, 11, 1⟩, ⟨156, 12, 1⟩, ⟨182, 14, 1⟩, ⟨195, 15, 1⟩, ⟨208, 16, 1⟩],
    [⟨169, 1, 2⟩], [(1, 5), (3, 3), (5, 2), (7, 2), (9, 1), (11, 1), (15, 1)], []⟩,
  ⟨17, [⟨17, 1, 1⟩, ⟨34, 2, 1⟩, ⟨51, 3, 1⟩, ⟨68, 4, 1⟩, ⟨85, 5, 1⟩, ⟨102, 6, 1⟩, ⟨119, 7, 1⟩, ⟨136, 8, 1⟩, ⟨153, 9, 1⟩, ⟨170, 10, 1⟩, ⟨187, 11, 1⟩, ⟨204, 12, 1⟩],
    [], [(1, 4), (3, 3), (5, 2), (7, 1), (9, 1), (11, 1)], []⟩,
  ⟨19, [⟨19, 1, 1⟩, ⟨38, 2, 1⟩, ⟨57, 3, 1⟩, ⟨76, 4, 1⟩, ⟨95, 5, 1⟩, ⟨114, 6, 1⟩, ⟨133, 7, 1⟩, ⟨152, 8, 1⟩, ⟨171, 9, 1⟩, ⟨190, 10, 1⟩, ⟨209, 11, 1⟩],
    [], [(1, 4), (3, 2), (5, 2), (7, 1), (9, 1), (11, 1)], []⟩,
  ⟨23, [⟨23, 1, 1⟩, ⟨46, 2, 1⟩, ⟨69, 3, 1⟩, ⟨92, 4, 1⟩, ⟨115, 5, 1⟩, ⟨138, 6, 1⟩, ⟨161, 7, 1⟩, ⟨184, 8, 1⟩, ⟨207, 9, 1⟩],
    [], [(1, 4), (3, 2), (5, 1), (7, 1), (9, 1)], []⟩,
  ⟨29, [⟨29, 1, 1⟩, ⟨58, 2, 1⟩, ⟨87, 3, 1⟩, ⟨116, 4, 1⟩, ⟨145, 5, 1⟩, ⟨174, 6, 1⟩, ⟨203, 7, 1⟩],
    [], [(1, 3), (3, 2), (5, 1), (7, 1)], []⟩,
  ⟨31, [⟨31, 1, 1⟩, ⟨62, 2, 1⟩, ⟨93, 3, 1⟩, ⟨124, 4, 1⟩, ⟨155, 5, 1⟩, ⟨186, 6, 1⟩],
    [], [(1, 3), (3, 2), (5, 1)], []⟩,
  ⟨37, [⟨37, 1, 1⟩, ⟨74, 2, 1⟩, ⟨111, 3, 1⟩, ⟨148, 4, 1⟩, ⟨185, 5, 1⟩],
    [], [(1, 3), (3, 1), (5, 1)], []⟩,
  ⟨41, [⟨41, 1, 1⟩, ⟨82, 2, 1⟩, ⟨123, 3, 1⟩, ⟨164, 4, 1⟩, ⟨205, 5, 1⟩],
    [], [(1, 3), (3, 1), (5, 1)], []⟩]

private def firstState : Option SearchState := place 1 batches.head!.entries initial

private def commonAvailSpec (free x1 x3 x5 x7 x15 : ℕ) : ℕ :=
  Nat.land (Nat.land full (Nat.shiftRight (runWindow free 5) x1))
    (Nat.land (Nat.shiftRight (runWindow free 3) x3)
      (Nat.land (Nat.shiftRight (runWindow free 2) x5)
        (Nat.land (Nat.shiftRight (runWindow free 2) x7) (Nat.shiftRight (runWindow free 1) x15))))

private def commonAvail (free pair x3 x5 x7 x15 : ℕ) : ℕ :=
  Nat.land (Nat.land full (windowFive free pair))
    (Nat.land (Nat.shiftRight (windowThree free pair) x3)
      (Nat.land (Nat.shiftRight pair x5)
        (Nat.land (Nat.shiftRight pair x7) (Nat.shiftRight free x15))))

private def eleven : Batch := (batches.drop 4).head!
private def thirteen : Batch := (batches.drop 5).head!

private def mask11 (s : SearchState) : ℕ :=
  packedToMask (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (Nat.shiftLeft 31 (getResidue s 1))) (Nat.shiftLeft 7 (getResidue s 3))) (Nat.shiftLeft 3 (getResidue s 5))) (Nat.shiftLeft 3 (getResidue s 7))) (Nat.shiftLeft 3 (getResidue s 9))) (Nat.shiftLeft 1 (getResidue s 15)))

private def mask13 (s : SearchState) : ℕ :=
  packedToMask (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (Nat.shiftLeft 31 (getResidue s 1))) (Nat.shiftLeft 7 (getResidue s 3))) (Nat.shiftLeft 3 (getResidue s 5))) (Nat.shiftLeft 3 (getResidue s 7))) (Nat.shiftLeft 1 (getResidue s 9))) (Nat.shiftLeft 1 (getResidue s 11))) (Nat.shiftLeft 1 (getResidue s 15)))

private lemma mask11_eq (s : SearchState) : mask11 s = linearMask s eleven.runs := rfl

private lemma mask13_eq (s : SearchState) : mask13 s = linearMask s thirteen.runs := rfl

private def checkSquare (used mask w : ℕ) (next : ℕ → Bool) : Bool :=
  forceNat (modulo211 (Nat.add w w)) fun square =>
    bif bitOn used square || bitOn mask w then false
    else next (Nat.lor (Nat.lor used (shiftedMask mask w)) (Nat.shiftLeft 1 square))

private def searchAfterEleven (s : SearchState) (x3 x5 x7 x9 x15 w11 : ℕ) : Bool :=
  forceNat s.used fun used =>
  forceNat (periodicFree used) fun free =>
  forceNat (windowTwo free) fun pair =>
    let cand := Nat.land (commonAvail free pair x3 x5 x7 x15)
      (Nat.land (Nat.shiftRight free x9) (Nat.shiftRight free w11))
    anyMarked 8 0 cand fun w =>
      checkSquare used (mask13 s) w fun newUsed =>
        search (batches.drop 6) ⟨newUsed, s.packed⟩

/-- The batches for 11 and 13 share five runs, with their squares checked separately. -/
private def searchAfterSevenSpec (s : SearchState) : Bool :=
  forceNat s.used fun used => forceNat s.packed fun packed =>
    let s : SearchState := ⟨used, packed⟩
    forceNat (getResidue s 3) fun x3 =>
    forceNat (getResidue s 5) fun x5 => forceNat (getResidue s 7) fun x7 =>
    forceNat (getResidue s 9) fun x9 => forceNat (getResidue s 15) fun x15 =>
    forceNat (mask11 s) fun mask =>
    forceNat (periodicFree used) fun free =>
    forceNat (windowTwo free) fun pair =>
      let cand := Nat.land (commonAvail free pair x3 x5 x7 x15) (Nat.shiftRight pair x9)
      anyMarked 8 0 cand fun w =>
        checkSquare used mask w fun newUsed =>
          searchAfterEleven ⟨newUsed, writeResidue packed 11 w⟩ x3 x5 x7 x9 x15 w

/-- The batches for 11 and 13 share five runs, with their squares checked separately. -/
private def searchAfterSeven (s : SearchState) : Bool :=
  forceNat s.used fun used => forceNat s.packed fun packed =>
    let s : SearchState := ⟨used, packed⟩
    forceNat (getResidue s 3) fun x3 => forceNat (getResidue s 5) fun x5 =>
    forceNat (getResidue s 7) fun x7 => forceNat (getResidue s 9) fun x9 =>
    forceNat (getResidue s 15) fun x15 =>
    forceNat (mask11 s) fun occupied11 =>
    forceNat (periodicFree used) fun free =>
    forceNat (windowTwo free) fun pair =>
      let cand := Nat.land (commonAvail free pair x3 x5 x7 x15) (Nat.shiftRight pair x9)
      anyMarked 8 0 cand fun w11 =>
        forceNat (modulo211 (Nat.add w11 w11)) fun q11 =>
          bif bitOn used q11 || bitOn occupied11 w11 then false else
            forceNat (Nat.lor (Nat.lor used (shiftedMask occupied11 w11)) (Nat.shiftLeft 1 q11)) fun used11 =>
            forceNat (periodicFree used11) fun free11 =>
            forceNat (windowTwo free11) fun pair11 =>
              let cand13 := Nat.land (commonAvail free11 pair11 x3 x5 x7 x15)
                (Nat.land (Nat.shiftRight free11 x9) (Nat.shiftRight free11 w11))
              anyMarked 8 0 cand13 fun w13 =>
                forceNat (modulo211 (Nat.add w13 w13)) fun q13 =>
                  let occupied13 := mask13 ⟨used11, writeResidue packed 11 w11⟩
                  bif bitOn used11 q13 || bitOn occupied13 w13 then false else
                    let used13 := Nat.lor (Nat.lor used11 (shiftedMask occupied13 w13)) (Nat.shiftLeft 1 q13)
                    search (batches.drop 6) ⟨used13, writeResidue packed 11 w11⟩

private lemma searchAfterSeven_spec (s : SearchState) :
    searchAfterSeven s = searchAfterSevenSpec s := rfl

private def searchWithNext (b : Batch) (s : SearchState) (next : SearchState → Bool) : Bool :=
  forceNat s.used fun used => forceNat s.packed fun packed =>
  let s : SearchState := ⟨used, packed⟩
  forceNat (linearMask s b.runs) fun mask =>
    anyMarked 8 0 (freeOffsets s b.runs) fun w =>
      let advanced : SearchState := ⟨Nat.lor used (shiftedMask mask w), writeLinear s b.saved w⟩
      match place w b.higher advanced with
      | none => false
      | some out => next out

private def seven : Batch := (batches.drop 3).head!

/-- The four exponent-two entries in the batch for 7 can be placed as translates of one mask. -/
private def sevenHigher : Batch :=
  ⟨49, [⟨49, 1, 1⟩, ⟨98, 2, 1⟩, ⟨147, 3, 1⟩, ⟨196, 4, 1⟩], [], [(1, 3), (3, 1)], []⟩

private def searchAfterFive (s : SearchState) : Bool :=
  forceNat s.used fun used => forceNat s.packed fun packed =>
  let s : SearchState := ⟨used, packed⟩
  forceNat (linearMask s seven.runs) fun mask =>
  forceNat (linearMask s sevenHigher.runs) fun baseHigh =>
    anyMarked 8 0 (freeOffsets s seven.runs) fun w =>
      let linear : SearchState := ⟨Nat.lor used (shiftedMask mask w), writeLinear s seven.saved w⟩
      forceNat (shiftedMask baseHigh (modulo211 (Nat.add w w))) fun highMask =>
        bif Nat.beq (Nat.land linear.used highMask) 0 then
          searchAfterSeven ⟨Nat.lor linear.used highMask, linear.packed⟩
        else false

private def searchFor3 (w : ℕ) : Bool :=
  match firstState.bind (place w batches.tail.head!.entries) with
  | none => false
  | some s => searchWithNext (batches.drop 2).head! s searchAfterFive

private lemma bitOn_eq (n i : ℕ) : bitOn n i = n.testBit i := by
  let x := Nat.land 1 (Nat.shiftRight n i)
  change (!Nat.beq x 0) = (x != 0)
  cases he : Nat.beq x 0 with
  | false =>
    have hne : x ≠ 0 := by intro h; rw [h, Nat.beq_refl] at he; contradiction
    simp [hne]
  | true => simp [Nat.eq_of_beq_eq_true he]

private lemma full_eq : full = 2 ^ 211 - 1 := rfl

private lemma forceNat_eq {α : Type} (n : ℕ) (f : ℕ → α) : forceNat n f = f n := by
  cases n <;> rfl

private lemma residue_bit (st : SearchState) (n j : ℕ) (hj : j < 8) :
    (getResidue st n).testBit j = st.packed.testBit (8*n+j) := by
  change (255 &&& (st.packed >>> (8*n))).testBit j = _
  rw [Nat.and_comm, show (255 : ℕ) = 2^8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true hj, Bool.true_and]

private lemma slot_bit (i n j : ℕ) (hj : j < 8) :
    (255 <<< (8 * n) : ℕ).testBit (8 * i + j) = decide (i = n) := by
  rw [Nat.testBit_shiftLeft]
  by_cases he : i = n
  · subst i
    have hs : 8*n ≤ 8*n + j := by omega
    have he' : 8*n+j-8*n = j := by omega
    change (decide _ && (2 ^ 8 - 1 : ℕ).testBit _) = _
    simp only [he', hs, decide_true, Nat.testBit_two_pow_sub_one, hj, Bool.true_and]
  · by_cases hi : i < n
    · have hs : ¬8*n ≤ 8*i+j := by omega
      simp [he, hs]
    · have hge : 8 ≤ 8*i+j-8*n := by omega
      change (_ && (2 ^ 8 - 1 : ℕ).testBit _) = _
      simp only [Nat.testBit_two_pow_sub_one, not_lt_of_ge hge, decide_false, Bool.and_false, he]

private lemma residue_write (st : SearchState) (i n v u : ℕ) (hv : v < 256) :
    getResidue ⟨u, writeResidue st.packed n v⟩ i = if i = n then v else getResidue st i := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · rw [residue_bit _ _ _ hj]
    change ((st.packed ^^^ (st.packed &&& (255 <<< (8*n)))) ||| (v <<< (8*n))).testBit
      (8*i+j) = _
    simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, slot_bit _ _ _ hj, Nat.testBit_shiftLeft]
    by_cases he : i = n
    · subst i
      have hk : 8*n+j-8*n = j := by omega
      simp [hk]
    · rw [if_neg he, residue_bit _ _ _ hj]
      by_cases hi : i < n
      · have hs : ¬8*n ≤ 8*i+j := by omega
        simp [he, hs]
      · have hs : 8 ≤ 8*i+j-8*n := by omega
        have hz : v.testBit (8*i+j-8*n) = false :=
          Nat.testBit_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hs))
        simp [he, hz]
  · have hwhole (x : SearchState) : (getResidue x i).testBit j = false := by
      apply Nat.testBit_lt_two_pow
      have hsmall : getResidue x i < 2^8 := by
        change 255 &&& (x.packed >>> (8*i)) < 2^8
        rw [Nat.and_comm]
        exact Nat.and_lt_two_pow _ (by decide)
      exact hsmall.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (le_of_not_gt hj))
    rw [hwhole]
    split
    · exact (Nat.testBit_lt_two_pow (hv.trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) (le_of_not_gt hj)))).symm
    · exact (hwhole st).symm

private def extendLabels (known : List ℕ) (rows : List Entry) : List ℕ :=
  rows.foldl (fun labels row => row.label :: labels) known

private def entriesReady (p : ℕ) : List Entry → List ℕ → Prop
  | [], _ => True
  | row :: rows, known =>
    row.label ∉ known ∧ row.cofactor ∈ known ∧ store row.cofactor = true ∧
    0 < row.label ∧ row.label ≤ 211 ∧ p ^ row.exponent * row.cofactor = row.label ∧
    entriesReady p rows (row.label :: known)

private instance decidableEntriesReady (p : ℕ) (rows : List Entry) (known : List ℕ) :
    Decidable (entriesReady p rows known) := by
  induction rows generalizing known with
  | nil => simp only [entriesReady]; infer_instance
  | cons row rows ih =>
    simp only [entriesReady]
    have := ih (row.label :: known)
    infer_instance

private def batchReady (b : Batch) (known : List ℕ) : Prop :=
  0 < b.prime ∧ b.prime ≤ 211 ∧ entriesReady b.prime b.entries known ∧
    ∀ row ∈ b.linear, row.exponent = 1 ∧ row.cofactor ∈ known ∧ store row.cofactor = true ∧ row.label ∉ known ∧
      0 < row.label ∧ row.label ≤ 211 ∧ b.prime * row.cofactor = row.label

private instance decidableBatchReady (b : Batch) (known : List ℕ) : Decidable (batchReady b known) := by
  unfold batchReady
  infer_instance

private def batchesReady : List Batch → List ℕ → Prop
  | [], _ => True
  | b :: rest, known => batchReady b known ∧ batchesReady rest (extendLabels known b.entries)

private instance decidableBatchesReady (bs : List Batch) (known : List ℕ) :
    Decidable (batchesReady bs known) := by
  induction bs generalizing known with
  | nil => simp only [batchesReady]; infer_instance
  | cons b rest ih =>
    simp only [batchesReady]
    have := ih (extendLabels known b.entries)
    infer_instance

private def Tracks (h : ℕ → ZMod 211) (known : List ℕ) (s : SearchState) : Prop :=
  (∀ n ∈ known, 0 < n ∧ n ≤ 211 ∧ (store n = true → getResidue s n = (h n).val)) ∧
    ∀ v, s.used.testBit v = true → ∃ n ∈ known, (h n).val = v

private lemma not_occurs (h : ℕ → ZMod 211) (hinj : Set.InjOn h (Set.Icc 1 211))
    {s : SearchState} {known : List ℕ} (hst : Tracks h known s)
    {n : ℕ} (hn : 0 < n) (hnq : n ≤ 211) (hnfresh : n ∉ known) :
    s.used.testBit (h n).val = false := by
  cases he : s.used.testBit (h n).val with
  | false => rfl
  | true =>
    obtain ⟨m, hm, hmval⟩ := hst.2 _ he
    obtain ⟨hmpos, hmq, _⟩ := hst.1 m hm
    have eq := hinj ⟨by omega, hmq⟩ ⟨by omega, hnq⟩ (ZMod.val_injective 211 hmval)
    exact (hnfresh (eq ▸ hm)).elim

private lemma log_pow_mul {h : ℕ → ZMod 211}
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a * b ≤ 211 → h (a * b) = h a + h b)
    {p c e : ℕ} (hp : 0 < p) (hc : 0 < c) (hpc : p ^ e * c ≤ 211) :
    h (p ^ e * c) = (e : ZMod 211) * h p + h c := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpos : 0 < p ^ e * c := Nat.mul_pos (pow_pos hp e) hc
    rw [pow_succ' p e, mul_assoc] at hpc ⊢
    rw [hmul p _ hp hpos hpc, ih ((Nat.le_mul_of_pos_left _ hp).trans hpc), Nat.cast_succ]
    ring

private lemma entry_value {h : ℕ → ZMod 211}
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a * b ≤ 211 → h (a * b) = h a + h b)
    {s : SearchState} {known : List ℕ} (hst : Tracks h known s) (row : Entry)
    {p : ℕ} (hp : 0 < p) (hc : row.cofactor ∈ known) (hcsmall : store row.cofactor = true)
    (he : p ^ row.exponent * row.cofactor = row.label) (hr : row.label ≤ 211) :
    (getResidue s row.cofactor + row.exponent * (h p).val) % 211 = (h row.label).val := by
  obtain ⟨hcpos, _, hcval⟩ := hst.1 _ hc
  rw [hcval hcsmall, ← ZMod.val_natCast, ← he, log_pow_mul hmul hp hcpos (he ▸ hr)]
  push_cast
  simp [add_comm]

private lemma initial_tracks {h : ℕ → ZMod 211} (h1 : h 1 = 0) : Tracks h [1] initial := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have eq : n = 1 := by simpa using hn
    subst n
    simp [initial, getResidue, h1]
  · intro v hv
    have eq : v = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hv
    exact ⟨1, by simp, by simp [h1, eq]⟩

private lemma place_complete {h : ℕ → ZMod 211} (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a * b ≤ 211 → h (a * b) = h a + h b)
    {p : ℕ} (hp : 0 < p) (rows : List Entry) (known : List ℕ) (s : SearchState)
    (hready : entriesReady p rows known) (hst : Tracks h known s) :
    ∃ out, place (h p).val rows s = some out ∧ Tracks h (extendLabels known rows) out := by
  induction rows generalizing known s with
  | nil => exact ⟨s, rfl, hst⟩
  | cons row rows ih =>
    obtain ⟨hfresh, hcofactor, hcsmall, hn, hnq, heq, htail⟩ := hready
    have hv := entry_value hmul hst row hp hcofactor hcsmall heq hnq
    let next : SearchState := ⟨s.used ||| (2 ^ (h row.label).val), bif store row.label then writeResidue s.packed row.label (h row.label).val else s.packed⟩
    have hnext : Tracks h (row.label :: known) next := by
      refine ⟨?_, ?_⟩
      · intro n hnmem
        rcases List.mem_cons.mp hnmem with rfl | hmem
        · refine ⟨hn, hnq, fun hs => ?_⟩
          simp only [next, hs, Bool.cond_true, residue_write s row.label row.label _ _
            ((ZMod.val_lt (h row.label)).trans (by decide : 211 < 256)), if_true]
        · obtain ⟨hpos, hbound, hval⟩ := hst.1 n hmem
          refine ⟨hpos, hbound, fun hs => ?_⟩
          have hne : n ≠ row.label := fun h => hfresh (h ▸ hmem)
          cases hr : store row.label
          · simpa only [next, hr, Bool.cond_false, getResidue] using hval hs
          · simpa only [next, hr, Bool.cond_true, residue_write s n row.label _ _
              ((ZMod.val_lt (h row.label)).trans (by decide : 211 < 256)), if_neg hne]
              using hval hs
      · intro v hbit
        change (s.used ||| 2 ^ (h row.label).val).testBit v = true at hbit
        simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hbit
        rcases hbit with hold | hnew
        · obtain ⟨n, hnknown, hval⟩ := hst.2 _ hold
          exact ⟨n, List.mem_cons_of_mem _ hnknown, hval⟩
        · exact ⟨row.label, List.mem_cons_self .., hnew⟩
    obtain ⟨out, hout, htrack⟩ := ih (row.label :: known) next htail hnext
    refine ⟨out, ?_, htrack⟩
    have hv' : Nat.mod (Nat.add (getResidue s row.cofactor)
        (Nat.mul row.exponent (h p).val)) 211 = (h row.label).val := hv
    have shiftOne (v : ℕ) : Nat.shiftLeft 1 v = 2 ^ v := by
      simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
    simpa only [place, hv', forceNat_eq, bitOn_eq, not_occurs h hinj hst hn hnq hfresh,
      Bool.cond_false, Nat.lor_eq, shiftOne, next] using hout

private lemma anyMarked_complete {depth start bits w : ℕ} {check : ℕ → Bool}
    (hw : w < 2 ^ depth) (hbit : bits.testBit w = true) (hgood : check (start + w) = true) :
    anyMarked depth start bits check = true := by
  have nonzero {m i : ℕ} (hb : m.testBit i = true) : Nat.beq m 0 = false := by
    cases he : Nat.beq m 0 with
    | false => rfl
    | true => simp [Nat.eq_of_beq_eq_true he] at hb
  induction depth generalizing start bits w with
  | zero =>
    have hzero : w = 0 := by simpa using hw
    simpa only [anyMarked, nonzero hbit, Bool.cond_false, hzero, add_zero] using hgood
  | succ depth ih =>
    change (bif Nat.beq bits 0 then false else
      anyMarked depth start (bits % 2 ^ (2 ^ depth)) check ||
        anyMarked depth (start + 2 ^ depth) (bits >>> 2 ^ depth) check) = true
    simp only [nonzero hbit, Bool.cond_false, Bool.or_eq_true_iff]
    by_cases h : w < 2 ^ depth
    · left
      exact ih (start := start) (bits := bits % 2 ^ (2 ^ depth)) h
        (by simpa only [Nat.testBit_mod_two_pow, decide_eq_true h, Bool.true_and] using hbit) hgood
    · right
      have he : 2 ^ depth + (w - 2 ^ depth) = w := Nat.add_sub_of_le (le_of_not_gt h)
      have hlt : w - 2 ^ depth < 2 ^ depth := by rw [pow_succ] at hw; omega
      exact ih (start := start + 2 ^ depth) (bits := bits >>> 2 ^ depth) hlt
        (by simpa only [Nat.testBit_shiftRight, he] using hbit)
        (by simpa only [Nat.add_assoc, he] using hgood)

private lemma mem_extendLabels {n : ℕ} (known : List ℕ) (rows : List Entry) :
    n ∈ extendLabels known rows ↔ n ∈ known ∨ ∃ row ∈ rows, row.label = n := by
  induction rows generalizing known with
  | nil => simp [extendLabels]
  | cons row rows ih =>
    change n ∈ extendLabels (row.label :: known) rows ↔ _
    rw [ih]
    simp only [List.mem_cons]
    constructor
    · rintro ((rfl | h) | ⟨r, hr, e⟩)
      · exact Or.inr ⟨row, Or.inl rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, Or.inr hr, e⟩
    · rintro (h | ⟨r, (rfl | hr), he⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl he.symm)
      · exact Or.inr ⟨r, hr, he⟩

private lemma extendLabels_append (known : List ℕ) (a b : List Entry) :
    extendLabels known (a ++ b) = extendLabels (extendLabels known a) b := by
  simp [extendLabels, List.foldl_append]

private lemma entriesReady_append {p : ℕ} (a b : List Entry) (known : List ℕ)
    (h : entriesReady p (a ++ b) known) : entriesReady p b (extendLabels known a) := by
  induction a generalizing known with
  | nil => exact h
  | cons row rest ih => exact ih (row.label :: known) h.2.2.2.2.2.2


private def RunsReady (b : Batch) : Prop :=
  (∀ r ∈ b.runs, 0 < r.2 ∧ r.2 ≤ 7 ∧ ∀ i : Fin r.2,
    ∃ row ∈ b.linear, row.cofactor = 2 ^ i.val * r.1) ∧
  b.saved = b.linear.filter (fun row => store row.label)

private instance (b : Batch) : Decidable (RunsReady b) := by
  unfold RunsReady
  infer_instance

private lemma used_lt {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) : s.used < 2 ^ 211 := by
  apply Nat.lt_pow_two_of_testBit
  intro v hv
  cases hb : s.used.testBit v with
  | false => rfl
  | true =>
    obtain ⟨n, _, hn⟩ := hst.2 v hb
    have := ZMod.val_lt (h n)
    omega

private lemma periodic_bit {used : ℕ} (hu : used < 2^211) {j : ℕ} (hj : j < 633) :
    (periodicFree used).testBit j = !used.testBit (j % 211) := by
  let f := full ^^^ used
  have hf : f < 2^211 := Nat.xor_lt_two_pow (by rw [full_eq]; omega) hu
  have hfbit (k : ℕ) (hk : k < 211) : f.testBit k = !used.testBit k := by
    simp only [f, full_eq, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hk]
    cases used.testBit k <;> rfl
  have he : periodicFree used = 2^211 * (2^211 * f + f) + f := by
    change f * (2^211 * (2^211 + 1) + 1) = _
    ring
  rw [he, Nat.testBit_two_pow_mul_add _ hf]
  by_cases h1 : j < 211
  · rw [if_pos h1, Nat.mod_eq_of_lt h1, hfbit j h1]
  · rw [if_neg h1, Nat.testBit_two_pow_mul_add _ hf]
    by_cases h2 : j - 211 < 211
    · rw [if_pos h2, hfbit _ h2, show j % 211 = j - 211 by omega]
    · have h3 : j - 211 - 211 < 211 := by omega
      rw [if_neg h2, hfbit _ h3, show j % 211 = j - 211 - 211 by omega]

private lemma window_bit {u len p : ℕ} (hlen : 0 < len) (hl : len ≤ 7)
    (h : ∀ i < len, u.testBit (p+i) = true) : (runWindow u len).testBit p = true := by
  have h0 (i : ℕ) (hi : i < len) : u.testBit (i+p) = true := by
    rw [Nat.add_comm]
    exact h i hi
  have firstBit : u.testBit p = true := by simpa only [Nat.add_zero] using h 0 hlen
  interval_cases len <;>
    simp only [runWindow, windowTwo, windowThree, windowFive, Nat.land_eq, Nat.shiftRight_eq',
      Nat.testBit_and, Nat.testBit_shiftRight, ← Nat.add_assoc, Bool.and_eq_true]
  all_goals
    repeat' apply And.intro
    all_goals first | exact firstBit | apply h0; omega

private lemma run_cofactor {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    {b : Batch} (hb : batchReady b known) (hr : RunsReady b)
    {r : ℕ × ℕ} (hm : r ∈ b.runs) (i : Fin r.2) :
    ∃ row ∈ b.linear, (getResidue s r.1 + i.val) % 211 = getResidue s row.cofactor ∧
      getResidue s r.1 < 211 := by
  obtain ⟨hlen, _, hrow⟩ := hr.1 r hm
  obtain ⟨row, hmrow, hcf⟩ := hrow i
  obtain ⟨base, hbase, hcb⟩ := hrow ⟨0, hlen⟩
  have hcb' : base.cofactor = r.1 := by simpa using hcb
  obtain ⟨_, hmem, hsmall, _, _, _, _⟩ := hb.2.2.2 row hmrow
  obtain ⟨_, hmem0, hsmall0, _, _, _, _⟩ := hb.2.2.2 base hbase
  rw [hcb'] at hmem0 hsmall0
  obtain ⟨hpos, _, hstored⟩ := hst.1 _ hmem0
  obtain ⟨_, hrowbound, hrowstored⟩ := hst.1 _ hmem
  refine ⟨row, hmrow, ?_, ?_⟩
  · rw [hstored hsmall0, hrowstored hsmall, ← ZMod.val_natCast, hcf,
      log_pow_mul hmul (by decide : 0 < 2) hpos (hcf ▸ hrowbound), h2]
    push_cast
    simp [add_comm]
  · rw [hstored hsmall0]
    exact ZMod.val_lt _

private lemma run_free {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    {b : Batch} (hb : batchReady b known) (hr : RunsReady b)
    {r : ℕ × ℕ} (hm : r ∈ b.runs) :
    ((runWindow (periodicFree s.used) r.2) >>> getResidue s r.1).testBit (h b.prime).val = true := by
  rw [Nat.testBit_shiftRight]
  obtain ⟨hlen, hle, _⟩ := hr.1 r hm
  apply window_bit hlen hle
  intro i hi
  obtain ⟨row, hrow, hcf, hbase⟩ := run_cofactor hst h2 hmul hb hr hm ⟨i, hi⟩
  have hw : (h b.prime).val < 211 := ZMod.val_lt _
  rw [periodic_bit (used_lt hst) (by omega)]
  obtain ⟨hexp, hmem, hsmall, hfresh, hpos, hbound, he⟩ := hb.2.2.2 row hrow
  have e : b.prime ^ row.exponent * row.cofactor = row.label := by rwa [hexp, pow_one]
  have hv := entry_value hmul hst row hb.1 hmem hsmall e hbound
  simp only [hexp, one_mul] at hv
  have hv' : ((getResidue s r.1 + (h b.prime).val) + i) % 211 = (h row.label).val := by
    calc
      _ = (((getResidue s r.1 + i) % 211) + (h b.prime).val) % 211 := by
        rw [Nat.mod_add_mod]; congr 1; omega
      _ = (h row.label).val := by rw [hcf, hv]
  rw [hv', not_occurs h hinj hst hpos hbound hfresh]
  rfl

private lemma freeOffsets_complete {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    {b : Batch} (hb : batchReady b known) (hr : RunsReady b) :
    (freeOffsets s b.runs).testBit (h b.prime).val = true := by
  let w := (h b.prime).val
  let free := periodicFree s.used
  have fullBit : full.testBit w = true := by
    rw [full_eq, Nat.testBit_two_pow_sub_one, decide_eq_true (ZMod.val_lt (h b.prime))]
  have loop (rs : List (ℕ × ℕ)) (a : ℕ) (hrs : ∀ r ∈ rs, r ∈ b.runs)
      (ha : a.testBit w = true) : (freeOffsets.loop s free rs a).testBit w = true := by
    induction rs generalizing a with
    | nil => exact ha
    | cons r rs ih =>
      obtain ⟨n, len⟩ := r
      have nz : Nat.beq a 0 = false := by
        cases he : Nat.beq a 0 with
        | false => rfl
        | true => simp [Nat.eq_of_beq_eq_true he] at ha
      rw [freeOffsets.loop, nz, Bool.cond_false]
      apply ih _ (fun r hh => hrs r (List.mem_cons_of_mem _ hh))
      rw [Nat.land_eq, Nat.testBit_and, ha]
      exact run_free hst h2 hinj hmul hb hr (hrs _ (List.mem_cons_self ..))
  rw [freeOffsets, forceNat_eq]
  exact loop _ _ (fun _ e => e) fullBit

private lemma linearMask_origin {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    {b : Batch} (hb : batchReady b known) (hr : RunsReady b)
    {v : ℕ} (hv : (linearMask s b.runs).testBit v = true) :
    ∃ row ∈ b.linear, getResidue s row.cofactor = v := by
  let step (a : ℕ) (r : ℕ × ℕ) := a ||| ((2 ^ r.2 - 1) <<< getResidue s r.1)
  have find {j : ℕ} (rs : List (ℕ × ℕ)) (a : ℕ)
      (he : (rs.foldl step a).testBit j = true) :
      a.testBit j = true ∨ ∃ r ∈ rs, ∃ i : Fin r.2, j = getResidue s r.1 + i.val := by
    induction rs generalizing a with
    | nil => exact Or.inl he
    | cons r rs ih =>
      change (rs.foldl step (step a r)).testBit j = true at he
      rcases ih _ he with hh | ⟨r', hmem, i, ei⟩
      · simp only [step, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
          Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hh
        rcases hh with ho | ⟨hle, hlt⟩
        · exact Or.inl ho
        · exact Or.inr ⟨r, List.mem_cons_self .., ⟨j - getResidue s r.1, hlt⟩, by change j = _ + (j - _); omega⟩
      · exact Or.inr ⟨r', List.mem_cons_of_mem _ hmem, i, ei⟩
  change (packedToMask (b.runs.foldl step 0)).testBit v = true at hv
  simp only [packedToMask, Nat.lor_eq, Nat.land_eq, Nat.shiftRight_eq', Nat.testBit_or,
    Nat.testBit_and, Nat.testBit_shiftRight, full_eq, Nat.testBit_two_pow_sub_one,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with ⟨hbit, hlt⟩ | hbit
  · obtain ⟨r, hm, i, ei⟩ := (find _ _ hbit).resolve_left (by simp)
    obtain ⟨row, hrow, hv', _⟩ := run_cofactor hst h2 hmul hb hr hm i
    exact ⟨row, hrow, by rw [← hv', ← ei, Nat.mod_eq_of_lt hlt]⟩
  · obtain ⟨r, hm, i, ei⟩ := (find _ _ hbit).resolve_left (by simp)
    obtain ⟨row, hrow, hv', hx⟩ := run_cofactor hst h2 hmul hb hr hm i
    have hi : i.val < 7 := i.isLt.trans_le ((hr.1 r hm).2.1)
    exact ⟨row, hrow, by rw [← hv']; omega⟩

private lemma shiftedMask_cases {mask w : ℕ} (hm : mask < 2^211) (hw : w < 211) :
    shiftedMask mask w = shiftedMaskClassic mask w ∨ shiftedMask mask w = 0 := by
  let lo := (mask <<< w) % 2 ^ 211
  let hi := mask >>> (211-w)
  have hprod : (2 : ℕ)^211 = 2^(211-w) * 2^w := by
    rw [← pow_add]
    congr 1
    omega
  have hhi : (mask <<< w) / 2^211 = hi := by
    rw [Nat.shiftLeft_eq, hprod, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos w)]
    exact (Nat.shiftRight_eq_div_pow mask _).symm
  have hlo : lo = (mask % 2^(211-w)) <<< w := by
    dsimp only [lo]
    simp only [Nat.shiftLeft_eq]
    rw [hprod, Nat.mul_mod_mul_right]
  have hhiLt : hi < 2^w := by
    dsimp only [hi]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← hprod]
    exact hm
  have hhiBound : hi < 2^211 := hhiLt.trans_le (Nat.pow_le_pow_right (by decide) hw.le)
  have hloBound : lo < 2^211 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hor : lo + hi = lo ||| hi := by
    rw [hlo]
    exact Nat.shiftLeft_add_eq_or_of_lt hhiLt _
  have hsum : lo + hi < 2^211 := by
    rw [hor]
    exact Nat.or_lt_two_pow hloBound hhiBound
  have hclassic : shiftedMaskClassic mask w = lo ||| hi := by
    unfold shiftedMaskClassic
    rw [full_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.or_mod_two_pow, Nat.mod_eq_of_lt hhiBound]
  have hbits : mask <<< w = 2^211 * hi + lo := by
    have h := Nat.div_add_mod (mask <<< w) (2^211)
    rw [hhi] at h
    exact h.symm
  have hbase : (2 : ℕ)^211 = full + 1 := by rw [full_eq]; omega
  have hfast : shiftedMask mask w = (lo+hi) % full := by
    change (mask <<< w) % full = _
    rw [hbits, hbase, add_mul, one_mul, Nat.add_assoc, Nat.mul_add_mod, Nat.add_comm hi lo]
  by_cases he : lo+hi = full
  · right
    rw [hfast, he, Nat.mod_self]
  · left
    have hs : lo+hi < full := by rw [hbase] at hsum; omega
    rw [hfast, Nat.mod_eq_of_lt hs, hclassic, hor]

private lemma shiftedMask_origin {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    {b : Batch} (hb : batchReady b known) (hr : RunsReady b)
    {w v : ℕ} (hw : w < 211) (hv : (shiftedMask (linearMask s b.runs) w).testBit v = true) :
    ∃ row ∈ b.linear, (getResidue s row.cofactor + w) % 211 = v := by
  have hm : linearMask s b.runs < 2^211 := by
    apply Nat.lt_pow_two_of_testBit
    intro k hk
    cases he : (linearMask s b.runs).testBit k with
    | false => rfl
    | true =>
      obtain ⟨row, hrow, hvalue⟩ := linearMask_origin hst h2 hmul hb hr he
      obtain ⟨_, hmem, hsmall, _, _, _, _⟩ := hb.2.2.2 row hrow
      have hlt : getResidue s row.cofactor < 211 := by
        rw [(hst.1 _ hmem).2.2 hsmall]
        exact ZMod.val_lt _
      omega
  rcases shiftedMask_cases hm hw with hrot | hzero
  · rw [hrot] at hv
    simp only [shiftedMaskClassic, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, full_eq, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨hle, hbit⟩ | hbit, hvlt⟩
    · obtain ⟨row, hrow, e⟩ := linearMask_origin hst h2 hmul hb hr hbit
      exact ⟨row, hrow, by rw [e]; omega⟩
    · obtain ⟨row, hrow, e⟩ := linearMask_origin hst h2 hmul hb hr hbit
      obtain ⟨_, hmem, hsmall, _, _, _, _⟩ := hb.2.2.2 row hrow
      have hlt : getResidue s row.cofactor < 211 := by
        rw [(hst.1 _ hmem).2.2 hsmall]
        exact ZMod.val_lt _
      exact ⟨row, hrow, by omega⟩
  · simp [hzero] at hv

private def applyLinear (s : SearchState) (b : Batch) (w : ℕ) : SearchState :=
  ⟨s.used ||| shiftedMask (linearMask s b.runs) w, writeLinear s b.saved w⟩

private lemma applyLinear_complete {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a * b ≤ 211 → h (a * b) = h a + h b)
    {b : Batch} (hb : batchReady b known) (hruns : RunsReady b) :
    Tracks h (extendLabels known b.linear) (applyLinear s b (h b.prime).val) := by
  let w := (h b.prime).val
  have hw : w < 211 := ZMod.val_lt _
  let value (r : Entry) := (getResidue s r.cofactor + w) % 211
  have good (r : Entry) (hr : r ∈ b.linear) :
      0 < r.label ∧ r.label ≤ 211 ∧ getResidue s r.cofactor < 211 ∧ value r = (h r.label).val := by
    obtain ⟨hexp, hmem, hcsmall, _, hpos, hbound, he⟩ := hb.2.2.2 r hr
    have he' : b.prime ^ r.exponent * r.cofactor = r.label := by rwa [hexp, pow_one]
    have hv := entry_value hmul hst r hb.1 hmem hcsmall he' hbound
    refine ⟨hpos, hbound, ?_, ?_⟩
    · rw [(hst.1 r.cofactor hmem).2.2 hcsmall]
      exact ZMod.val_lt _
    · simpa [value, w, hexp] using hv
  refine ⟨?_, ?_⟩
  · intro n hmem
    have hknown := (mem_extendLabels known b.linear).mp hmem
    have hn : 0 < n ∧ n ≤ 211 := by
      rcases hknown with ha | ⟨r, hr, hrn⟩
      · exact ⟨(hst.1 _ ha).1, (hst.1 _ ha).2.1⟩
      · rw [← hrn]
        exact ⟨(good r hr).1, (good r hr).2.1⟩
    refine ⟨hn.1, hn.2, fun hnsmall => ?_⟩
    let write (packed : ℕ) (row : Entry) := writeResidue packed row.label (value row)
    let filtered := b.linear.filter (fun row => store row.label)
    have fold (rs : List Entry) (packed : ℕ) (hsub : ∀ row ∈ rs, row ∈ filtered)
        (hex : getResidue ⟨0, packed⟩ n = (h n).val ∨ ∃ row ∈ rs, row.label = n) :
        getResidue ⟨0, rs.foldl write packed⟩ n = (h n).val := by
      induction rs generalizing packed with
      | nil => simpa using hex
      | cons row rows ih =>
        apply ih (write packed row) (fun r hr => hsub r (List.mem_cons_of_mem _ hr))
        have rh := List.mem_filter.mp (hsub row (List.mem_cons_self ..))
        have hval := (good row rh.1).2.2.2
        have hfit : value row < 256 := (Nat.mod_lt _ (by decide)).trans (by decide : 211 < 256)
        have hlookup := residue_write ⟨0, packed⟩ n row.label (value row) 0 hfit
        by_cases he : n = row.label
        · left
          rw [show write packed row = writeResidue packed row.label (value row) by rfl,
            hlookup, if_pos he, hval, he]
        · simp only [List.mem_cons] at hex
          rcases hex with heold | ⟨r, (rfl | hr), heq⟩
          · exact Or.inl (by simpa [write, hlookup, he] using heold)
          · exact (he heq.symm).elim
          · exact Or.inr ⟨r, hr, heq⟩
    change getResidue ⟨0, b.saved.foldl write s.packed⟩ n = (h n).val
    rw [hruns.2]
    apply fold filtered s.packed (fun _ h => h)
    rcases hknown with ho | ⟨r, hr, hEq⟩
    · exact Or.inl ((hst.1 _ ho).2.2 hnsmall)
    · exact Or.inr ⟨r, List.mem_filter.mpr ⟨hr, (hEq ▸ hnsmall : store r.label = true)⟩, hEq⟩
  · intro v hv
    change (s.used ||| shiftedMask (linearMask s b.runs) w).testBit v = true at hv
    rw [Nat.testBit_or, Bool.or_eq_true_iff] at hv
    rcases hv with ht | ht
    · obtain ⟨n, hn, hval⟩ := hst.2 v ht
      exact ⟨n, (mem_extendLabels known b.linear).mpr (.inl hn), hval⟩
    · obtain ⟨r, hr, hval⟩ := shiftedMask_origin hst h2 hmul hb hruns hw ht
      exact ⟨r.label, (mem_extendLabels known b.linear).mpr (.inr ⟨r, hr, rfl⟩),
        (good r hr).2.2.2.symm.trans hval⟩

private lemma batch_advance_complete {h : ℕ → ZMod 211} (h2 : h 2 = 1) (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a * b ≤ 211 → h (a * b) = h a + h b)
    {b : Batch} {known : List ℕ} {s : SearchState} (hb : batchReady b known)
    (hruns : RunsReady b) (hst : Tracks h known s) :
    ∃ next, place (h b.prime).val b.higher
      (applyLinear s b (h b.prime).val) = some next ∧
        Tracks h (extendLabels known b.entries) next := by
  have hr := entriesReady_append b.linear b.higher known hb.2.2.1
  obtain ⟨out, hout, htrack⟩ := place_complete hinj hmul hb.1 b.higher
    (extendLabels known b.linear) _ hr (applyLinear_complete hst h2 hmul hb hruns)
  exact ⟨out, hout, by simpa only [Batch.entries, extendLabels_append] using htrack⟩

private lemma search_complete {h : ℕ → ZMod 211} (h2 : h 2 = 1) (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a * b ≤ 211 → h (a * b) = h a + h b)
    (bs : List Batch) (known : List ℕ) (s : SearchState) (hReady : batchesReady bs known)
    (hruns : ∀ b ∈ bs, RunsReady b) (hst : Tracks h known s) : search bs s = true := by
  induction bs generalizing known s with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨hBatch, hRest⟩ := hReady
    have hbr := hruns b (List.mem_cons_self ..)
    have hAllow := freeOffsets_complete hst h2 hinj hmul hBatch hbr
    have hnz : Nat.beq (freeOffsets s b.runs) 0 = false := by
      cases he : Nat.beq (freeOffsets s b.runs) 0 with
      | false => rfl
      | true => simp [Nat.eq_of_beq_eq_true he] at hAllow
    obtain ⟨out, hout, htrack⟩ := batch_advance_complete h2 hinj hmul hBatch hbr hst
    have ha : anyMarked 8 0 (freeOffsets s b.runs) (fun w =>
        match place w b.higher (applyLinear s b w) with
        | none => false
        | some next => search rest next) = true := by
      apply anyMarked_complete (w := (h b.prime).val)
        ((ZMod.val_lt (h b.prime)).trans (by decide : 211 < 2 ^ 8)) hAllow
      simpa only [zero_add, hout] using ih _ _ hRest (fun r hr => hruns r (List.mem_cons_of_mem _ hr)) htrack
    rw [search, forceNat_eq, forceNat_eq]
    cases s
    simpa only [hnz, Bool.cond_false, forceNat_eq, applyLinear, Nat.lor_eq] using ha

private lemma bit_and_true {a b w : ℕ} (ha : a.testBit w = true) (hb : b.testBit w = true) :
    (Nat.land a b).testBit w = true := by
  rw [Nat.land_eq, Nat.testBit_and, ha, hb]
  rfl

private lemma coreCommonSpec_bit {s : SearchState} {b : Batch} {h : ℕ → ZMod 211} {known : List ℕ}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    (hb : batchReady b known) (hr : RunsReady b)
    (hm1 : (1,5) ∈ b.runs) (hm3 : (3,3) ∈ b.runs)
    (hm5 : (5,2) ∈ b.runs) (hm7 : (7,2) ∈ b.runs) (hm15 : (15,1) ∈ b.runs) :
    (commonAvailSpec (periodicFree s.used) (getResidue s 1) (getResidue s 3)
      (getResidue s 5) (getResidue s 7) (getResidue s 15)).testBit (h b.prime).val = true := by
  have bound : full.testBit (h b.prime).val = true := by
    rw [full_eq, Nat.testBit_two_pow_sub_one, decide_eq_true (ZMod.val_lt (h b.prime))]
  exact bit_and_true (bit_and_true bound (run_free hst h2 hinj hmul hb hr hm1))
    (bit_and_true (run_free hst h2 hinj hmul hb hr hm3)
      (bit_and_true (run_free hst h2 hinj hmul hb hr hm5)
        (bit_and_true (run_free hst h2 hinj hmul hb hr hm7) (run_free hst h2 hinj hmul hb hr hm15))))

private lemma commonAvail_eq (free x3 x5 x7 x15 : ℕ) :
    commonAvail free (windowTwo free) x3 x5 x7 x15 = commonAvailSpec free 0 x3 x5 x7 x15 := rfl

private lemma coreCommon_bit {s : SearchState} {b : Batch} {h : ℕ → ZMod 211} {known : List ℕ}
    (hst : Tracks h known s) (h2 : h 2 = 1) (hz : getResidue s 1 = 0)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    (hb : batchReady b known) (hr : RunsReady b)
    (hm1 : (1,5) ∈ b.runs) (hm3 : (3,3) ∈ b.runs)
    (hm5 : (5,2) ∈ b.runs) (hm7 : (7,2) ∈ b.runs) (hm15 : (15,1) ∈ b.runs) :
    (commonAvail (periodicFree s.used) (windowTwo (periodicFree s.used)) (getResidue s 3)
      (getResidue s 5) (getResidue s 7) (getResidue s 15)).testBit (h b.prime).val = true := by
  have he : commonAvail (periodicFree s.used) (windowTwo (periodicFree s.used)) (getResidue s 3)
      (getResidue s 5) (getResidue s 7) (getResidue s 15) =
      commonAvailSpec (periodicFree s.used) (getResidue s 1) (getResidue s 3) (getResidue s 5)
        (getResidue s 7) (getResidue s 15) :=
    (commonAvail_eq _ _ _ _ _).trans (congrArg (fun x =>
      commonAvailSpec (periodicFree s.used) x (getResidue s 3) (getResidue s 5)
        (getResidue s 7) (getResidue s 15)) hz.symm)
  exact (congrArg (fun m : ℕ => m.testBit (h b.prime).val) he).trans
    (coreCommonSpec_bit hst h2 hinj hmul hb hr hm1 hm3 hm5 hm7 hm15)

private lemma place11_form (s : SearchState) (hz : getResidue s 1 = 0)
    {w : ℕ} (hw : w < 211) :
    let lin := s.used ||| shiftedMask (linearMask s eleven.runs) w
    let square := (w+w) % 211
    place w eleven.higher (applyLinear s eleven w) =
      (bif lin.testBit square then none else
        some ⟨lin ||| (1 <<< square), writeResidue s.packed 11 w⟩) := by
  have hw' : w < 256 := hw.trans (by decide)
  have hpacked : writeLinear s eleven.saved w = writeResidue s.packed 11 w := by
    change writeResidue s.packed 11 ((getResidue s 1 + w) % 211) = _
    rw [hz, zero_add, Nat.mod_eq_of_lt hw]
  have write : applyLinear s eleven w =
      ⟨s.used ||| shiftedMask (linearMask s eleven.runs) w, writeResidue s.packed 11 w⟩ :=
    congrArg (fun p => (⟨s.used ||| shiftedMask (linearMask s eleven.runs) w, p⟩ : SearchState)) hpacked
  have hread {u : ℕ} : getResidue ⟨u, writeResidue s.packed 11 w⟩ 1 = 0 := by
    rw [residue_write s 1 11 w u hw', if_neg (by decide : (1:ℕ) ≠ 11), hz]
  rw [write]
  have shape : eleven.higher = [⟨121,1,2⟩] := rfl
  rw [shape, place, forceNat_eq]
  have hval : Nat.mod (Nat.add (getResidue ⟨s.used ||| shiftedMask (linearMask s eleven.runs) w,
        writeResidue s.packed 11 w⟩ 1) (Nat.mul 2 w)) 211 = (w + w) % 211 := by
    change (getResidue _ 1 + 2*w) % 211 = _
    rw [hread, zero_add, two_mul]
  have nv : store 121 = false := by decide +kernel
  simp only [hval, nv, Bool.cond_false, place, bitOn_eq, Nat.lor_eq, Nat.shiftLeft_eq']

private lemma place13_form (s : SearchState) (hz : getResidue s 1 = 0) (w : ℕ) :
    let lin := s.used ||| shiftedMask (linearMask s thirteen.runs) w
    let square := (w+w) % 211
    place w thirteen.higher (applyLinear s thirteen w) =
      (bif lin.testBit square then none else some ⟨lin ||| (1 <<< square), s.packed⟩) := by
  have write : applyLinear s thirteen w =
      ⟨s.used ||| shiftedMask (linearMask s thirteen.runs) w, s.packed⟩ := rfl
  rw [write]
  have shape : thirteen.higher = [⟨169,1,2⟩] := rfl
  rw [shape, place, forceNat_eq]
  have hval : Nat.mod (Nat.add (getResidue ⟨s.used ||| shiftedMask (linearMask s thirteen.runs) w,
        s.packed⟩ 1) (Nat.mul 2 w)) 211 = (w + w) % 211 := by
    change (getResidue s 1 + 2*w) % 211 = _
    rw [hz, zero_add, two_mul]
  have nv : store 169 = false := by decide +kernel
  simp only [hval, nv, Bool.cond_false, place, bitOn_eq, Nat.lor_eq, Nat.shiftLeft_eq']

private lemma searchWithNext_complete {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    {b : Batch} {next : SearchState → Bool}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    (hb : batchReady b known) (hr : RunsReady b)
    (hnext : ∀ out, Tracks h (extendLabels known b.entries) out → next out = true) :
    searchWithNext b s next = true := by
  obtain ⟨out, hstep, hout⟩ := batch_advance_complete h2 hinj hmul hb hr hst
  unfold searchWithNext
  simp only [forceNat_eq]
  cases s
  apply anyMarked_complete (w := (h b.prime).val)
    ((ZMod.val_lt (h b.prime)).trans (by decide : 211 < 2^8))
    (freeOffsets_complete hst h2 hinj hmul hb hr)
  rw [zero_add]
  change (match place (h b.prime).val b.higher (applyLinear _ b (h b.prime).val) with
    | none => false
    | some y => next y) = true
  rw [hstep]
  exact hnext out hout

private lemma noSquareCofactor {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    {b : Batch} (hb : batchReady b known) (hr : RunsReady b)
    (hn : ∀ row ∈ b.linear, row.cofactor ≠ b.prime) :
    (linearMask s b.runs).testBit (h b.prime).val = false := by
  cases he : (linearMask s b.runs).testBit (h b.prime).val with
  | false => rfl
  | true =>
    obtain ⟨row, hrow, hv⟩ := linearMask_origin hst h2 hmul hb hr he
    obtain ⟨_, hmem, hsmall, _, _, _, _⟩ := hb.2.2.2 row hrow
    obtain ⟨hp, hle, hval⟩ := hst.1 _ hmem
    rw [hval hsmall] at hv
    have hc := hinj ⟨by omega, hle⟩ ⟨by have := hb.1; omega, hb.2.1⟩ (ZMod.val_injective _ hv)
    exact (hn row hrow hc).elim

private lemma checkSquare_clear (used mask w : ℕ) (next : ℕ → Bool)
    (free : (used ||| shiftedMask mask w).testBit ((w+w)%211) = false)
    (maskFree : mask.testBit w = false) :
    checkSquare used mask w next = next (used ||| shiftedMask mask w ||| (1 <<< ((w+w)%211))) := by
  rw [Nat.testBit_or, Bool.or_eq_false_iff] at free
  unfold checkSquare
  simp only [forceNat_eq, bitOn_eq, Nat.lor_eq, Nat.shiftLeft_eq', modulo211]
  change (bif used.testBit ((w+w)%211) || mask.testBit w then false else _) = _
  rw [free.1, maskFree]
  rfl

private lemma transportWindowBit {u v n w : ℕ} (he : u = v)
    (hb : (u >>> n).testBit w = true) : (v >>> n).testBit w = true :=
  (congrArg (fun x => (x >>> n).testBit w) he).symm.trans hb

private lemma runWindow_one (u : ℕ) : runWindow u 1 = u := rfl
private lemma runWindow_two (u : ℕ) : runWindow u 2 = windowTwo u := rfl

set_option maxRecDepth 6000 in
private lemma searchAfterEleven_complete {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (hz : getResidue s 1 = 0) (h2 : h 2 = 1)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    (hb : batchReady thirteen known)
    (hbTail : batchesReady (batches.drop 6) (extendLabels known thirteen.entries))
    (hrTail : ∀ b ∈ batches.drop 6, RunsReady b) :
    searchAfterEleven s (getResidue s 3) (getResidue s 5)
      (getResidue s 7) (getResidue s 9) (getResidue s 15) (getResidue s 11) = true := by
  have hr : RunsReady thirteen := by decide +kernel
  let w := (h thirteen.prime).val
  have hw : w < 211 := ZMod.val_lt _
  let lin := s.used ||| shiftedMask (linearMask s thirteen.runs) w
  let q := (w+w) % 211
  let dest : SearchState := ⟨lin ||| (1 <<< q), s.packed⟩
  obtain ⟨out, hp, ht⟩ := batch_advance_complete h2 hinj hmul hb hr hst
  have form : (bif lin.testBit q then none else some dest) = some out :=
    (place13_form s hz w).symm.trans hp
  have guard : lin.testBit q = false := by
    cases e : lin.testBit q with
    | false => rfl
    | true => simp only [e, Bool.cond_true, reduceCtorEq] at form
  have ht' : Tracks h (extendLabels known thirteen.entries) dest := by
    have e : dest = out := Option.some.inj (by simpa only [guard, Bool.cond_false] using form)
    exact e.symm ▸ ht
  have hcommon := coreCommon_bit hst h2 hz hinj hmul hb hr
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have extra9 := transportWindowBit (runWindow_one _)
    (run_free hst h2 hinj hmul hb hr (r := (9,1)) (by decide))
  have extra11 := transportWindowBit (runWindow_one _)
    (run_free hst h2 hinj hmul hb hr (r := (11,1)) (by decide))
  have hbit := bit_and_true hcommon (bit_and_true extra9 extra11)
  unfold searchAfterEleven
  simp only [forceNat_eq]
  apply anyMarked_complete (w := w) (hw.trans (by decide : 211 < 2^8)) hbit
  have hno := noSquareCofactor hst h2 hinj hmul hb hr (by decide +kernel)
  rw [zero_add, mask13_eq, checkSquare_clear _ _ _ _ guard hno]
  exact search_complete h2 hinj hmul _ _ dest hbTail hrTail ht'

set_option maxRecDepth 6000 in
private lemma searchAfterSevenSpec_complete {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h1 : h 1 = 0) (h2 : h 2 = 1) (hmem1 : 1 ∈ known)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    (hb11 : batchReady eleven known)
    (hb13 : batchReady thirteen (extendLabels known eleven.entries))
    (hbTail : batchesReady (batches.drop 6)
      (extendLabels (extendLabels known eleven.entries) thirteen.entries))
    (hrTail : ∀ b ∈ batches.drop 6, RunsReady b) : searchAfterSevenSpec s = true := by
  have hr11 : RunsReady eleven := by decide +kernel
  have hz : getResidue s 1 = 0 := by
    rw [(hst.1 1 hmem1).2.2 (by decide), h1, ZMod.val_zero]
  let w := (h eleven.prime).val
  have hw : w < 211 := ZMod.val_lt _
  let lin := s.used ||| shiftedMask (linearMask s eleven.runs) w
  let sq := (w+w) % 211
  let dest : SearchState := ⟨lin ||| (1 <<< sq), writeResidue s.packed 11 w⟩
  obtain ⟨out, hp, ht⟩ := batch_advance_complete h2 hinj hmul hb11 hr11 hst
  have form : (bif lin.testBit sq then none else some dest) = some out :=
    (place11_form s hz hw).symm.trans hp
  have guard : lin.testBit sq = false := by
    cases e : lin.testBit sq with
    | false => rfl
    | true => simp only [e, Bool.cond_true, reduceCtorEq] at form
  have ht' : Tracks h (extendLabels known eleven.entries) dest := by
    have e : dest = out := Option.some.inj (by simpa only [guard, Bool.cond_false] using form)
    exact e.symm ▸ ht
  have read11 (n : ℕ) : getResidue dest n = if n = 11 then w else getResidue s n :=
    residue_write s n 11 w _ (hw.trans (by decide))
  have readOld (n : ℕ) (hne : n ≠ 11) : getResidue dest n = getResidue s n := by
    rw [read11, if_neg hne]
  have hz' : getResidue dest 1 = 0 := (readOld 1 (by decide)).trans hz
  have new11 : getResidue dest 11 = w := by rw [read11, if_pos rfl]
  have hcommon := coreCommon_bit hst h2 hz hinj hmul hb11 hr11
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have extra9 := transportWindowBit (runWindow_two _)
    (run_free hst h2 hinj hmul hb11 hr11 (r := (9,2)) (by decide))
  have hbit := bit_and_true hcommon extra9
  unfold searchAfterSevenSpec
  simp only [forceNat_eq]
  cases s
  dsimp only
  apply anyMarked_complete (w := w) (hw.trans (by decide : 211 < 2^8)) hbit
  have hno := noSquareCofactor hst h2 hinj hmul hb11 hr11 (by decide +kernel)
  rw [zero_add, mask11_eq, checkSquare_clear _ _ _ _ guard hno]
  have hnext := searchAfterEleven_complete ht' hz' h2 hinj hmul hb13 hbTail hrTail
  rw [readOld 3 (by decide), readOld 5 (by decide), readOld 7 (by decide),
    readOld 9 (by decide), readOld 15 (by decide), new11] at hnext
  exact hnext

private lemma searchAfterFive_complete {h : ℕ → ZMod 211} {known : List ℕ} {s : SearchState}
    (hst : Tracks h known s) (h2 : h 2 = 1)
    (hinj : Set.InjOn h (Set.Icc 1 211))
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → a*b ≤ 211 → h (a*b) = h a + h b)
    (hknown1 : 1 ∈ known) (hknown3 : 3 ∈ known)
    (hb : batchReady seven known)
    (hbHigh : batchReady sevenHigher (extendLabels known seven.linear))
    (hnext : ∀ out, Tracks h (extendLabels known seven.entries) out → searchAfterSeven out = true) :
    searchAfterFive s = true := by
  have hr : RunsReady seven := by decide +kernel
  have hrHigh : RunsReady sevenHigher := by decide +kernel
  let w := (h seven.prime).val
  let linear := applyLinear s seven w
  let square := (h sevenHigher.prime).val
  have hsq : square = (w+w) % 211 := by
    change (h 49).val = ((h 7).val + (h 7).val) % 211
    rw [show h 49 = h 7 + h 7 from hmul 7 7 (by decide) (by decide) (by decide), ← ZMod.val_natCast]
    push_cast
    simp
  let highMask := shiftedMask (linearMask linear sevenHigher.runs) square
  have hstLin : Tracks h (extendLabels known seven.linear) linear :=
    applyLinear_complete hst h2 hmul hb hr
  have same (n : ℕ) (hn : n ∈ known) (hs : store n = true) :
      getResidue linear n = getResidue s n :=
    ((hstLin.1 n ((mem_extendLabels known seven.linear).mpr (.inl hn))).2.2 hs).trans
      ((hst.1 n hn).2.2 hs).symm
  have high_eq : linearMask s sevenHigher.runs = linearMask linear sevenHigher.runs := by
    let f (x y : ℕ) := packedToMask (Nat.lor (Nat.lor 0 (Nat.shiftLeft 7 x)) (Nat.shiftLeft 1 y))
    change f (getResidue s 1) (getResidue s 3) = f (getResidue linear 1) (getResidue linear 3)
    rw [same 1 hknown1 (by decide), same 3 hknown3 (by decide)]
  have hdisjoint : Nat.land linear.used highMask = 0 := by
    apply Nat.eq_of_testBit_eq
    intro v
    rw [Nat.land_eq, Nat.testBit_and]
    cases hv : highMask.testBit v with
    | false => simp
    | true =>
      obtain ⟨r, hrMem, hval⟩ := shiftedMask_origin hstLin h2 hmul hbHigh hrHigh (ZMod.val_lt _) hv
      obtain ⟨hexp, hmem, hsmall, hfresh, hpos, hbound, e⟩ := hbHigh.2.2.2 r hrMem
      have e' : sevenHigher.prime ^ r.exponent * r.cofactor = r.label := by rwa [hexp, pow_one]
      have hv' := entry_value hmul hstLin r hbHigh.1 hmem hsmall e' hbound
      simp only [hexp, one_mul] at hv'
      rw [← hval, hv', not_occurs h hinj hstLin hpos hbound hfresh]
      simp
  have hstOut : Tracks h (extendLabels (extendLabels known seven.linear) sevenHigher.linear)
      (applyLinear linear sevenHigher square) := applyLinear_complete hstLin h2 hmul hbHigh hrHigh
  have hknown : extendLabels (extendLabels known seven.linear) sevenHigher.linear =
      extendLabels known seven.entries := by
    rw [Batch.entries, extendLabels_append]
    rfl
  rw [hknown] at hstOut
  unfold searchAfterFive
  simp only [forceNat_eq]
  obtain ⟨used, packed⟩ := s
  dsimp only
  apply anyMarked_complete (w := w) ((ZMod.val_lt (h seven.prime)).trans (by decide : 211 < 2^8))
    (freeOffsets_complete hst h2 hinj hmul hb hr)
  rw [zero_add]
  change (bif Nat.beq (Nat.land linear.used
      (shiftedMask (linearMask ⟨used, packed⟩ sevenHigher.runs) ((w+w)%211))) 0 then
      searchAfterSeven ⟨linear.used ||| shiftedMask (linearMask ⟨used, packed⟩ sevenHigher.runs) ((w+w)%211),
        linear.packed⟩ else false) = true
  rw [high_eq, ← hsq, hdisjoint, Nat.beq_refl, Bool.cond_true]
  exact hnext _ hstOut

set_option maxRecDepth 10000 in
private lemma batches_validated : batchesReady batches [1] := by decide +kernel

set_option maxRecDepth 10000 in
private lemma runs_validated : ∀ b ∈ batches, RunsReady b := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private lemma find_searchFor3 (h : ℕ → ZMod 211) (hl : IsLogarithm 211 h) (h2 : h 2 = 1) :
    searchFor3 (h 3).val = true := by
  obtain ⟨hinj, h1, hmul⟩ := hl
  let two := batches.head!
  let three := batches.tail.head!
  let five := (batches.drop 2).head!
  let beforeThree := extendLabels [1] two.entries
  let beforeFive := extendLabels beforeThree three.entries
  let beforeSeven := extendLabels beforeFive five.entries
  let beforeEleven := extendLabels beforeSeven seven.entries
  have readyTwo : batchReady two [1] := batches_validated.1
  have readyThree : batchReady three beforeThree := batches_validated.2.1
  have readyFive : batchReady five beforeFive := batches_validated.2.2.1
  have readySeven : batchReady seven beforeSeven := batches_validated.2.2.2.1
  have readyEleven : batchReady eleven beforeEleven := batches_validated.2.2.2.2.1
  have readyThirteen : batchReady thirteen (extendLabels beforeEleven eleven.entries) :=
    batches_validated.2.2.2.2.2.1
  have readyTail : batchesReady (batches.drop 6)
      (extendLabels (extendLabels beforeEleven eleven.entries) thirteen.entries) :=
    batches_validated.2.2.2.2.2.2
  obtain ⟨s2, hs2, ht2⟩ := place_complete hinj hmul readyTwo.1 two.entries [1] initial
    readyTwo.2.2.1 (initial_tracks h1)
  obtain ⟨s3, hs3, ht3⟩ := place_complete hinj hmul readyThree.1 three.entries beforeThree s2
    readyThree.2.2.1 ht2
  have hst : firstState = some s2 := by
    change place (h 2).val two.entries initial = some s2 at hs2
    have hone : (1 : ZMod 211).val = 1 := rfl
    simpa only [h2, hone, firstState, two] using hs2
  have hs3' : place (h 3).val batches.tail.head!.entries s2 = some s3 := hs3
  unfold searchFor3
  rw [hst]
  simp only [Option.bind_some, hs3']
  apply searchWithNext_complete ht3 h2 hinj hmul readyFive (by decide +kernel)
  intro s5 ht5
  have readyHigh : batchReady sevenHigher (extendLabels beforeSeven seven.linear) := by decide +kernel
  apply searchAfterFive_complete ht5 h2 hinj hmul (by decide +kernel) (by decide +kernel) readySeven readyHigh
  intro s7 ht7
  have hm : 1 ∈ beforeEleven := by decide +kernel
  exact (searchAfterSeven_spec s7).trans
    (searchAfterSevenSpec_complete ht7 h1 h2 hm hinj hmul readyEleven readyThirteen readyTail
      (fun b hb => runs_validated b (List.mem_of_mem_drop hb)))

private lemma prime211 : Nat.Prime 211 := by norm_num

private lemma normalize_log (h : ℕ → ZMod 211) (hl : IsLogarithm 211 h) :
    ∃ g : ℕ → ZMod 211, IsLogarithm 211 g ∧ g 2 = 1 := by
  have hp : Fact (Nat.Prime 211) := ⟨prime211⟩
  have ht : h 2 ≠ 0 := by
    intro he
    have e : (2 : ℕ) = 1 := hl.1 (by decide) (by decide) (he.trans hl.2.1.symm)
    omega
  let g (n : ℕ) := (h 2)⁻¹ * h n
  refine ⟨g, ⟨?_, by simp [g, hl.2.1], ?_⟩, ?_⟩
  · intro a ha b hb he
    exact hl.1 ha hb (mul_left_cancel₀ (inv_ne_zero ht) he)
  · intro a b ha hb hprod
    simp [g, hl.2.2 a b ha hb hprod, mul_add]
  · exact inv_mul_cancel₀ ht

set_option maxRecDepth 6000 in
private lemma disproof_from_certificate (certificate : ∀ w : ℕ, w < 211 → searchFor3 w = false) :
    ¬ (∀ n : ℕ, 1 ≤ n → ∃ c : ℕ+ → Fin n, ∀ a : ℕ+,
      Function.Injective (fun i : Fin n => c (a * ⟨i.val + 1, Nat.succ_pos _⟩))) := by
  intro h
  obtain ⟨c, hc⟩ := h 211 (by decide)
  obtain ⟨l, hl⟩ := logarithm_of_coloring prime211 c hc
  obtain ⟨g, hg, h2⟩ := normalize_log l hl
  have he := find_searchFor3 g hg h2
  have hf := certificate (g 3).val (ZMod.val_lt _)
  exact Bool.noConfusion (hf.symm.trans he)

/-- Extend the exhaustive certificate by one possible value of the logarithm of 3. -/
private lemma extendCertificate {k : ℕ} (earlier : ∀ w < k, searchFor3 w = false)
    (last : searchFor3 k = false) : ∀ w < k + 1, searchFor3 w = false := by
  intro w hw
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hw) with h | rfl
  · exact earlier w h
  · exact last

private lemma checkedThrough0 : ∀ w < 0, searchFor3 w = false := by
  intro w h
  exact (Nat.not_lt_zero w h).elim

-- Separate kernel checks keep the finite proof's working set bounded.
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked0 : searchFor3 0 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked1 : searchFor3 1 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked2 : searchFor3 2 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked3 : searchFor3 3 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked4 : searchFor3 4 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked5 : searchFor3 5 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked6 : searchFor3 6 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked7 : searchFor3 7 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked8 : searchFor3 8 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked9 : searchFor3 9 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked10 : searchFor3 10 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked11 : searchFor3 11 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked12 : searchFor3 12 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked13 : searchFor3 13 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked14 : searchFor3 14 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked15 : searchFor3 15 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked16 : searchFor3 16 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked17 : searchFor3 17 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked18 : searchFor3 18 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked19 : searchFor3 19 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked20 : searchFor3 20 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked21 : searchFor3 21 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked22 : searchFor3 22 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked23 : searchFor3 23 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked24 : searchFor3 24 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked25 : searchFor3 25 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked26 : searchFor3 26 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked27 : searchFor3 27 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked28 : searchFor3 28 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked29 : searchFor3 29 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked30 : searchFor3 30 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked31 : searchFor3 31 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked32 : searchFor3 32 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked33 : searchFor3 33 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked34 : searchFor3 34 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked35 : searchFor3 35 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked36 : searchFor3 36 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked37 : searchFor3 37 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked38 : searchFor3 38 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked39 : searchFor3 39 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked40 : searchFor3 40 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked41 : searchFor3 41 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked42 : searchFor3 42 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked43 : searchFor3 43 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked44 : searchFor3 44 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked45 : searchFor3 45 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked46 : searchFor3 46 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked47 : searchFor3 47 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked48 : searchFor3 48 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked49 : searchFor3 49 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked50 : searchFor3 50 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked51 : searchFor3 51 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked52 : searchFor3 52 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked53 : searchFor3 53 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked54 : searchFor3 54 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked55 : searchFor3 55 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked56 : searchFor3 56 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked57 : searchFor3 57 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked58 : searchFor3 58 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked59 : searchFor3 59 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked60 : searchFor3 60 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked61 : searchFor3 61 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked62 : searchFor3 62 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked63 : searchFor3 63 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked64 : searchFor3 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked65 : searchFor3 65 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked66 : searchFor3 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked67 : searchFor3 67 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked68 : searchFor3 68 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked69 : searchFor3 69 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked70 : searchFor3 70 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked71 : searchFor3 71 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked72 : searchFor3 72 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked73 : searchFor3 73 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked74 : searchFor3 74 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked75 : searchFor3 75 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked76 : searchFor3 76 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked77 : searchFor3 77 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked78 : searchFor3 78 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked79 : searchFor3 79 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked80 : searchFor3 80 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked81 : searchFor3 81 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked82 : searchFor3 82 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked83 : searchFor3 83 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked84 : searchFor3 84 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked85 : searchFor3 85 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked86 : searchFor3 86 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked87 : searchFor3 87 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked88 : searchFor3 88 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked89 : searchFor3 89 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked90 : searchFor3 90 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked91 : searchFor3 91 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked92 : searchFor3 92 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked93 : searchFor3 93 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked94 : searchFor3 94 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked95 : searchFor3 95 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked96 : searchFor3 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked97 : searchFor3 97 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked98 : searchFor3 98 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked99 : searchFor3 99 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked100 : searchFor3 100 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked101 : searchFor3 101 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked102 : searchFor3 102 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked103 : searchFor3 103 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked104 : searchFor3 104 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked105 : searchFor3 105 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked106 : searchFor3 106 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked107 : searchFor3 107 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked108 : searchFor3 108 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked109 : searchFor3 109 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked110 : searchFor3 110 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked111 : searchFor3 111 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked112 : searchFor3 112 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked113 : searchFor3 113 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked114 : searchFor3 114 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked115 : searchFor3 115 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked116 : searchFor3 116 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked117 : searchFor3 117 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked118 : searchFor3 118 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked119 : searchFor3 119 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked120 : searchFor3 120 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked121 : searchFor3 121 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked122 : searchFor3 122 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked123 : searchFor3 123 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked124 : searchFor3 124 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked125 : searchFor3 125 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked126 : searchFor3 126 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked127 : searchFor3 127 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked128 : searchFor3 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked129 : searchFor3 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked130 : searchFor3 130 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked131 : searchFor3 131 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked132 : searchFor3 132 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked133 : searchFor3 133 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked134 : searchFor3 134 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked135 : searchFor3 135 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked136 : searchFor3 136 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked137 : searchFor3 137 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked138 : searchFor3 138 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked139 : searchFor3 139 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked140 : searchFor3 140 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked141 : searchFor3 141 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked142 : searchFor3 142 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked143 : searchFor3 143 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked144 : searchFor3 144 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked145 : searchFor3 145 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked146 : searchFor3 146 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked147 : searchFor3 147 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked148 : searchFor3 148 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked149 : searchFor3 149 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked150 : searchFor3 150 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked151 : searchFor3 151 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked152 : searchFor3 152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked153 : searchFor3 153 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked154 : searchFor3 154 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked155 : searchFor3 155 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked156 : searchFor3 156 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked157 : searchFor3 157 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked158 : searchFor3 158 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked159 : searchFor3 159 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked160 : searchFor3 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked161 : searchFor3 161 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked162 : searchFor3 162 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked163 : searchFor3 163 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked164 : searchFor3 164 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked165 : searchFor3 165 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked166 : searchFor3 166 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked167 : searchFor3 167 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked168 : searchFor3 168 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked169 : searchFor3 169 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked170 : searchFor3 170 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked171 : searchFor3 171 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked172 : searchFor3 172 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked173 : searchFor3 173 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked174 : searchFor3 174 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked175 : searchFor3 175 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked176 : searchFor3 176 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked177 : searchFor3 177 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked178 : searchFor3 178 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked179 : searchFor3 179 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked180 : searchFor3 180 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked181 : searchFor3 181 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked182 : searchFor3 182 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked183 : searchFor3 183 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked184 : searchFor3 184 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked185 : searchFor3 185 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked186 : searchFor3 186 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked187 : searchFor3 187 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked188 : searchFor3 188 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked189 : searchFor3 189 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked190 : searchFor3 190 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked191 : searchFor3 191 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked192 : searchFor3 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked193 : searchFor3 193 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked194 : searchFor3 194 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked195 : searchFor3 195 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked196 : searchFor3 196 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked197 : searchFor3 197 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked198 : searchFor3 198 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked199 : searchFor3 199 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked200 : searchFor3 200 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked201 : searchFor3 201 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked202 : searchFor3 202 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked203 : searchFor3 203 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked204 : searchFor3 204 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked205 : searchFor3 205 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked206 : searchFor3 206 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked207 : searchFor3 207 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked208 : searchFor3 208 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked209 : searchFor3 209 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private lemma checked210 : searchFor3 210 = false := by decide +kernel

private lemma checkedThrough12 : ∀ w < 12, searchFor3 w = false := by
  have h1 := extendCertificate checkedThrough0 checked0
  have h2 := extendCertificate h1 checked1
  have h3 := extendCertificate h2 checked2
  have h4 := extendCertificate h3 checked3
  have h5 := extendCertificate h4 checked4
  have h6 := extendCertificate h5 checked5
  have h7 := extendCertificate h6 checked6
  have h8 := extendCertificate h7 checked7
  have h9 := extendCertificate h8 checked8
  have h10 := extendCertificate h9 checked9
  have h11 := extendCertificate h10 checked10
  have h12 := extendCertificate h11 checked11
  exact h12

private lemma checkedThrough24 : ∀ w < 24, searchFor3 w = false := by
  have h13 := extendCertificate checkedThrough12 checked12
  have h14 := extendCertificate h13 checked13
  have h15 := extendCertificate h14 checked14
  have h16 := extendCertificate h15 checked15
  have h17 := extendCertificate h16 checked16
  have h18 := extendCertificate h17 checked17
  have h19 := extendCertificate h18 checked18
  have h20 := extendCertificate h19 checked19
  have h21 := extendCertificate h20 checked20
  have h22 := extendCertificate h21 checked21
  have h23 := extendCertificate h22 checked22
  have h24 := extendCertificate h23 checked23
  exact h24

private lemma checkedThrough36 : ∀ w < 36, searchFor3 w = false := by
  have h25 := extendCertificate checkedThrough24 checked24
  have h26 := extendCertificate h25 checked25
  have h27 := extendCertificate h26 checked26
  have h28 := extendCertificate h27 checked27
  have h29 := extendCertificate h28 checked28
  have h30 := extendCertificate h29 checked29
  have h31 := extendCertificate h30 checked30
  have h32 := extendCertificate h31 checked31
  have h33 := extendCertificate h32 checked32
  have h34 := extendCertificate h33 checked33
  have h35 := extendCertificate h34 checked34
  have h36 := extendCertificate h35 checked35
  exact h36

private lemma checkedThrough48 : ∀ w < 48, searchFor3 w = false := by
  have h37 := extendCertificate checkedThrough36 checked36
  have h38 := extendCertificate h37 checked37
  have h39 := extendCertificate h38 checked38
  have h40 := extendCertificate h39 checked39
  have h41 := extendCertificate h40 checked40
  have h42 := extendCertificate h41 checked41
  have h43 := extendCertificate h42 checked42
  have h44 := extendCertificate h43 checked43
  have h45 := extendCertificate h44 checked44
  have h46 := extendCertificate h45 checked45
  have h47 := extendCertificate h46 checked46
  have h48 := extendCertificate h47 checked47
  exact h48

private lemma checkedThrough60 : ∀ w < 60, searchFor3 w = false := by
  have h49 := extendCertificate checkedThrough48 checked48
  have h50 := extendCertificate h49 checked49
  have h51 := extendCertificate h50 checked50
  have h52 := extendCertificate h51 checked51
  have h53 := extendCertificate h52 checked52
  have h54 := extendCertificate h53 checked53
  have h55 := extendCertificate h54 checked54
  have h56 := extendCertificate h55 checked55
  have h57 := extendCertificate h56 checked56
  have h58 := extendCertificate h57 checked57
  have h59 := extendCertificate h58 checked58
  have h60 := extendCertificate h59 checked59
  exact h60

private lemma checkedThrough72 : ∀ w < 72, searchFor3 w = false := by
  have h61 := extendCertificate checkedThrough60 checked60
  have h62 := extendCertificate h61 checked61
  have h63 := extendCertificate h62 checked62
  have h64 := extendCertificate h63 checked63
  have h65 := extendCertificate h64 checked64
  have h66 := extendCertificate h65 checked65
  have h67 := extendCertificate h66 checked66
  have h68 := extendCertificate h67 checked67
  have h69 := extendCertificate h68 checked68
  have h70 := extendCertificate h69 checked69
  have h71 := extendCertificate h70 checked70
  have h72 := extendCertificate h71 checked71
  exact h72

private lemma checkedThrough84 : ∀ w < 84, searchFor3 w = false := by
  have h73 := extendCertificate checkedThrough72 checked72
  have h74 := extendCertificate h73 checked73
  have h75 := extendCertificate h74 checked74
  have h76 := extendCertificate h75 checked75
  have h77 := extendCertificate h76 checked76
  have h78 := extendCertificate h77 checked77
  have h79 := extendCertificate h78 checked78
  have h80 := extendCertificate h79 checked79
  have h81 := extendCertificate h80 checked80
  have h82 := extendCertificate h81 checked81
  have h83 := extendCertificate h82 checked82
  have h84 := extendCertificate h83 checked83
  exact h84

private lemma checkedThrough96 : ∀ w < 96, searchFor3 w = false := by
  have h85 := extendCertificate checkedThrough84 checked84
  have h86 := extendCertificate h85 checked85
  have h87 := extendCertificate h86 checked86
  have h88 := extendCertificate h87 checked87
  have h89 := extendCertificate h88 checked88
  have h90 := extendCertificate h89 checked89
  have h91 := extendCertificate h90 checked90
  have h92 := extendCertificate h91 checked91
  have h93 := extendCertificate h92 checked92
  have h94 := extendCertificate h93 checked93
  have h95 := extendCertificate h94 checked94
  have h96 := extendCertificate h95 checked95
  exact h96

private lemma checkedThrough108 : ∀ w < 108, searchFor3 w = false := by
  have h97 := extendCertificate checkedThrough96 checked96
  have h98 := extendCertificate h97 checked97
  have h99 := extendCertificate h98 checked98
  have h100 := extendCertificate h99 checked99
  have h101 := extendCertificate h100 checked100
  have h102 := extendCertificate h101 checked101
  have h103 := extendCertificate h102 checked102
  have h104 := extendCertificate h103 checked103
  have h105 := extendCertificate h104 checked104
  have h106 := extendCertificate h105 checked105
  have h107 := extendCertificate h106 checked106
  have h108 := extendCertificate h107 checked107
  exact h108

private lemma checkedThrough120 : ∀ w < 120, searchFor3 w = false := by
  have h109 := extendCertificate checkedThrough108 checked108
  have h110 := extendCertificate h109 checked109
  have h111 := extendCertificate h110 checked110
  have h112 := extendCertificate h111 checked111
  have h113 := extendCertificate h112 checked112
  have h114 := extendCertificate h113 checked113
  have h115 := extendCertificate h114 checked114
  have h116 := extendCertificate h115 checked115
  have h117 := extendCertificate h116 checked116
  have h118 := extendCertificate h117 checked117
  have h119 := extendCertificate h118 checked118
  have h120 := extendCertificate h119 checked119
  exact h120

private lemma checkedThrough132 : ∀ w < 132, searchFor3 w = false := by
  have h121 := extendCertificate checkedThrough120 checked120
  have h122 := extendCertificate h121 checked121
  have h123 := extendCertificate h122 checked122
  have h124 := extendCertificate h123 checked123
  have h125 := extendCertificate h124 checked124
  have h126 := extendCertificate h125 checked125
  have h127 := extendCertificate h126 checked126
  have h128 := extendCertificate h127 checked127
  have h129 := extendCertificate h128 checked128
  have h130 := extendCertificate h129 checked129
  have h131 := extendCertificate h130 checked130
  have h132 := extendCertificate h131 checked131
  exact h132

private lemma checkedThrough144 : ∀ w < 144, searchFor3 w = false := by
  have h133 := extendCertificate checkedThrough132 checked132
  have h134 := extendCertificate h133 checked133
  have h135 := extendCertificate h134 checked134
  have h136 := extendCertificate h135 checked135
  have h137 := extendCertificate h136 checked136
  have h138 := extendCertificate h137 checked137
  have h139 := extendCertificate h138 checked138
  have h140 := extendCertificate h139 checked139
  have h141 := extendCertificate h140 checked140
  have h142 := extendCertificate h141 checked141
  have h143 := extendCertificate h142 checked142
  have h144 := extendCertificate h143 checked143
  exact h144

private lemma checkedThrough156 : ∀ w < 156, searchFor3 w = false := by
  have h145 := extendCertificate checkedThrough144 checked144
  have h146 := extendCertificate h145 checked145
  have h147 := extendCertificate h146 checked146
  have h148 := extendCertificate h147 checked147
  have h149 := extendCertificate h148 checked148
  have h150 := extendCertificate h149 checked149
  have h151 := extendCertificate h150 checked150
  have h152 := extendCertificate h151 checked151
  have h153 := extendCertificate h152 checked152
  have h154 := extendCertificate h153 checked153
  have h155 := extendCertificate h154 checked154
  have h156 := extendCertificate h155 checked155
  exact h156

private lemma checkedThrough168 : ∀ w < 168, searchFor3 w = false := by
  have h157 := extendCertificate checkedThrough156 checked156
  have h158 := extendCertificate h157 checked157
  have h159 := extendCertificate h158 checked158
  have h160 := extendCertificate h159 checked159
  have h161 := extendCertificate h160 checked160
  have h162 := extendCertificate h161 checked161
  have h163 := extendCertificate h162 checked162
  have h164 := extendCertificate h163 checked163
  have h165 := extendCertificate h164 checked164
  have h166 := extendCertificate h165 checked165
  have h167 := extendCertificate h166 checked166
  have h168 := extendCertificate h167 checked167
  exact h168

private lemma checkedThrough180 : ∀ w < 180, searchFor3 w = false := by
  have h169 := extendCertificate checkedThrough168 checked168
  have h170 := extendCertificate h169 checked169
  have h171 := extendCertificate h170 checked170
  have h172 := extendCertificate h171 checked171
  have h173 := extendCertificate h172 checked172
  have h174 := extendCertificate h173 checked173
  have h175 := extendCertificate h174 checked174
  have h176 := extendCertificate h175 checked175
  have h177 := extendCertificate h176 checked176
  have h178 := extendCertificate h177 checked177
  have h179 := extendCertificate h178 checked178
  have h180 := extendCertificate h179 checked179
  exact h180

private lemma checkedThrough192 : ∀ w < 192, searchFor3 w = false := by
  have h181 := extendCertificate checkedThrough180 checked180
  have h182 := extendCertificate h181 checked181
  have h183 := extendCertificate h182 checked182
  have h184 := extendCertificate h183 checked183
  have h185 := extendCertificate h184 checked184
  have h186 := extendCertificate h185 checked185
  have h187 := extendCertificate h186 checked186
  have h188 := extendCertificate h187 checked187
  have h189 := extendCertificate h188 checked188
  have h190 := extendCertificate h189 checked189
  have h191 := extendCertificate h190 checked190
  have h192 := extendCertificate h191 checked191
  exact h192

private lemma checkedThrough204 : ∀ w < 204, searchFor3 w = false := by
  have h193 := extendCertificate checkedThrough192 checked192
  have h194 := extendCertificate h193 checked193
  have h195 := extendCertificate h194 checked194
  have h196 := extendCertificate h195 checked195
  have h197 := extendCertificate h196 checked196
  have h198 := extendCertificate h197 checked197
  have h199 := extendCertificate h198 checked198
  have h200 := extendCertificate h199 checked199
  have h201 := extendCertificate h200 checked200
  have h202 := extendCertificate h201 checked201
  have h203 := extendCertificate h202 checked202
  have h204 := extendCertificate h203 checked203
  exact h204

private lemma checkedThrough211 : ∀ w < 211, searchFor3 w = false := by
  have h205 := extendCertificate checkedThrough204 checked204
  have h206 := extendCertificate h205 checked205
  have h207 := extendCertificate h206 checked206
  have h208 := extendCertificate h207 checked207
  have h209 := extendCertificate h208 checked208
  have h210 := extendCertificate h209 checked209
  have h211 := extendCertificate h210 checked210
  exact h211

private theorem result : ¬ (type_of% @OMA.S_mo_26358.main) :=
  disproof_from_certificate checkedThrough211

end OMA.RainbowCascade

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_26358.main) := by
  exact OMA.RainbowCascade.result
