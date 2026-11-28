import OMAStatements.S_oeis_a085807
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
The prime congruence is proved using the cyclic shift action, following the
argument of Qiping Zhou at https://mathoverflow.net/questions/402745.
Ryser’s formula gives a finite verification of permanent minimization through size six.

For higher sizes, place the largest unplaced weight by moving it one distance
at a time. The two remaining inequalities distinguish whether a row can
contain two entries at the nearer distance.
-/

namespace OMA.R_oeis_a085807_R1

open OMA.S_oeis_a085807

/-- Move the largest unplaced weight one band outward when the nearer band
can contribute two entries to a row. All larger weights are already placed. -/
def H1 : Prop :=
  ∀ (n r d : ℕ) (f : ℕ → ℕ), 6 < n → 1 ≤ d → d < r → r < n → 2 * d < n →
    f 0 = 0 → Set.BijOn f (Set.Ico 1 n) (Set.Ico 1 n) →
    (∀ i, r < i → i < n → f i = i) → f d = r → f (d + 1) < r →
    matrixPerm (toeplitzMatrix n (f ∘ Equiv.swap d (d + 1))) ≤
      matrixPerm (toeplitzMatrix n f)

/-- The corresponding exchange when both bands contribute at most one entry
per row. The undirected edges of each band then form a matching. -/
def H2 : Prop :=
  ∀ (n r d : ℕ) (f : ℕ → ℕ), 6 < n → 1 ≤ d → d < r → r < n → n ≤ 2 * d →
    f 0 = 0 → Set.BijOn f (Set.Ico 1 n) (Set.Ico 1 n) →
    (∀ i, r < i → i < n → f i = i) → f d = r → f (d + 1) < r →
    matrixPerm (toeplitzMatrix n (f ∘ Equiv.swap d (d + 1))) ≤
      matrixPerm (toeplitzMatrix n f)

open MulAction

private theorem sum_eq_sum_fixed {p : ℕ} [Fact p.Prime] {G A : Type*}
    [Group G] [MulAction G A] [Fintype A] [Fintype (fixedPoints G A)]
    (hG : IsPGroup p G)
    (w : A → ZMod p) (hw : ∀ (g : G) (a : A), w (g • a) = w a) :
    ∑ a, w a = ∑ a : fixedPoints G A, w a.val := by
  classical
  let q : A → Quotient (orbitRel G A) := Quotient.mk''
  have fiber (a : A) : {b // q b = q a} ≃ orbit G a :=
    Equiv.subtypeEquivRight fun b => Quotient.eq''
  have key (a : A) :
      (∑ b : {b // q b = q a}, w b.val) =
        (Fintype.card (orbit G a) : ZMod p) * w a := by
    calc
      _ = ∑ _b : {b // q b = q a}, w a := by
        apply Finset.sum_congr rfl
        intro b _
        have hb : b.val ∈ orbit G a := Quotient.exact' b.property
        obtain ⟨g, hg⟩ := hb
        exact (congrArg w hg.symm).trans (hw g a)
      _ = _ := by simp [Fintype.card_congr (fiber a), nsmul_eq_mul]
  -- In characteristic p, only singleton orbits can contribute to the sum.
  rw [← Fintype.sum_fiberwise q w]
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => q a.val) (by simp) ?_ ?_ ?_
  · intro a₁ _ _ a₂ _ _ h
    exact Subtype.ext (mem_fixedPoints'.mp a₂.property a₁.val (Quotient.exact' h))
  · intro b
    refine Quotient.inductionOn' b (fun a _ ha => ?_)
    rw [key a] at ha
    obtain ⟨k, hk⟩ := hG.card_orbit a
    rw [Nat.card_eq_fintype_card] at hk
    have hk0 : k = 0 := by
      by_contra h
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
      simp [hk, pow_succ] at ha
    have hf : a ∈ fixedPoints G A :=
      mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rw [hk, hk0, pow_zero])
    exact ⟨⟨a, hf⟩, Finset.mem_univ _, by simpa [hk, hk0] using ha, rfl⟩
  · intro a _ _
    rw [key, mem_fixedPoints_iff_card_orbit_eq_one.mp a.property, Nat.cast_one, one_mul]

/-- A circulant of prime-power size over the corresponding prime field has permanent
equal to the sum of its weights. -/
private theorem circulant_permanent (p n k : ℕ) [Fact p.Prime] [NeZero n]
    (hn : n = p ^ k) (w : ZMod n → ZMod p) :
    (∑ σ : Equiv.Perm (ZMod n), ∏ x : ZMod n, w (σ x - x)) = ∑ d : ZMod n, w d := by
  classical
  let _ : MulAction (Multiplicative (ZMod n)) (Equiv.Perm (ZMod n)) := by
    exact {
      smul := fun g σ => (Equiv.addRight g.toAdd).permCongr σ
      one_smul := fun σ => by
        apply Equiv.ext
        intro x
        change σ (x + -0) + 0 = σ x
        simp
      mul_smul := fun g h σ => by
        apply Equiv.ext
        intro x
        change σ (x + -(g.toAdd + h.toAdd)) + (g.toAdd + h.toAdd) =
          σ (x + -g.toAdd + -h.toAdd) + h.toAdd + g.toAdd
        rw [show x + -(g.toAdd + h.toAdd) = x + -g.toAdd + -h.toAdd by abel]
        abel
    }
  let weight (σ : Equiv.Perm (ZMod n)) := ∏ x : ZMod n, w (σ x - x)
  have hG : IsPGroup p (Multiplicative (ZMod n)) :=
    IsPGroup.of_card (n := k) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, hn])
  have hweight (g : Multiplicative (ZMod n)) (σ : Equiv.Perm (ZMod n)) :
      weight (g • σ) = weight σ := by
    unfold weight
    apply Fintype.prod_equiv (Equiv.addRight (-g.toAdd))
    intro x
    change w (σ (x + -g.toAdd) + g.toAdd - x) = w (σ (x + -g.toAdd) - (x + -g.toAdd))
    congr 1
    abel
  change ∑ σ, weight σ = _
  rw [sum_eq_sum_fixed hG weight hweight]
  symm
  let translations : ZMod n ≃ fixedPoints (Multiplicative (ZMod n)) (Equiv.Perm (ZMod n)) := by
    refine {
      toFun := fun d => ⟨Equiv.addRight d, ?_⟩
      invFun := fun σ => σ.val 0
      left_inv := fun d => zero_add d
      right_inv := ?_
    }
    · rw [mem_fixedPoints]
      intro g
      apply Equiv.ext
      intro x
      change (x + -g.toAdd) + d + g.toAdd = x + d
      abel
    · intro σ
      apply Subtype.ext
      apply Equiv.ext
      intro x
      have h := congrArg (fun τ : Equiv.Perm (ZMod n) => τ x)
        (mem_fixedPoints.mp σ.property (Multiplicative.ofAdd x))
      change σ.val (x + -x) + x = σ.val x at h
      change x + σ.val 0 = σ.val x
      simpa [add_comm] using h
  apply Fintype.sum_equiv translations
  intro d
  change w d = ∏ x : ZMod n, w (x + d - x)
  have hdiff (x : ZMod n) : x + d - x = d := by abel
  simp only [hdiff, Finset.prod_const, Finset.card_univ, ZMod.card, hn, ZMod.pow_card_pow]

private theorem finEquiv_val {p : ℕ} [NeZero p] (i : Fin p) :
    (ZMod.finEquiv p i).val = i.val := by
  cases p
  · exact (NeZero.ne 0 rfl).elim
  · rfl

private theorem signedWeight_sub {p n : ℕ} [NeZero n] (hn : Odd n) (hn0 : (n : ZMod p) = 0)
    (i j : Fin n) :
    (-1 : ZMod p) ^ (ZMod.finEquiv n j - ZMod.finEquiv n i).val *
        ((ZMod.finEquiv n j - ZMod.finEquiv n i).val : ZMod p) =
      (-1 : ZMod p) ^ i.val * (-1) ^ j.val *
        ((Int.natAbs ((i.val : ℤ) - j.val) : ℕ) : ZMod p) := by
  let x := ZMod.finEquiv n i
  let y := ZMod.finEquiv n j
  have hx : x.val = i.val := finEquiv_val i
  have hy : y.val = j.val := finEquiv_val j
  change (-1 : ZMod p) ^ (y - x).val * ((y - x).val : ZMod p) = _
  by_cases hij : i.val ≤ j.val
  · have hval : (y - x).val = j.val - i.val := by
      rw [ZMod.val_sub (a := y) (b := x) (by simpa only [hx, hy] using hij), hx, hy]
    have habs : Int.natAbs ((i.val : ℤ) - j.val) = j.val - i.val := by omega
    have hsign : (-1 : ZMod p) ^ i.val * (-1) ^ j.val = (-1) ^ (j.val - i.val) := by
      rw [← pow_add, show i.val + j.val = 2 * i.val + (j.val - i.val) by omega,
        pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    rw [hval, hsign, habs]
  · have hval : (x - y).val = i.val - j.val := by
      rw [ZMod.val_sub (a := x) (b := y)
        (by simpa only [hx, hy] using (show j.val ≤ i.val by omega)), hx, hy]
    have hne : x - y ≠ 0 := by
      intro h
      have he := congrArg ZMod.val h
      rw [hval, ZMod.val_zero] at he
      omega
    have hneg : (y - x).val = n - (i.val - j.val) := by
      rw [← neg_sub x y, ZMod.neg_val, if_neg hne, hval]
    have habs : Int.natAbs ((i.val : ℤ) - j.val) = i.val - j.val := by omega
    have hcast : ((n - (i.val - j.val) : ℕ) : ZMod p) = -((i.val - j.val : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by have hi := i.isLt; omega), hn0, zero_sub]
    have hpar : (n - (i.val - j.val)) % 2 = (i.val + j.val + 1) % 2 := by
      obtain ⟨k, hk⟩ := hn
      have hi := i.isLt
      omega
    have hsign : (-1 : ZMod p) ^ (n - (i.val - j.val)) = -((-1) ^ i.val * (-1) ^ j.val) := by
      calc
        _ = (-1 : ZMod p) ^ (i.val + j.val + 1) := by
          rw [neg_one_pow_eq_pow_mod_two (n - (i.val - j.val)),
            neg_one_pow_eq_pow_mod_two (i.val + j.val + 1), hpar]
        _ = _ := by rw [pow_succ, pow_add]; ring
    rw [hneg, habs, hcast, hsign]
    ring

private theorem alternating_sum (R : Type*) [CommRing R] (m : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1), (-1 : R) ^ i * (i : R)) = (m : R) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : (-1 : R) ^ (2 * m + 2) = 1 := (show Even (2 * m + 2) from ⟨m + 1, by omega⟩).neg_one_pow
    have ho : (-1 : R) ^ (2 * m + 1) = -1 := (show Odd (2 * m + 1) from ⟨m, rfl⟩).neg_one_pow
    rw [show 2 * (m + 1) + 1 = (2 * m + 1 + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, ho,
      show 2 * m + 1 + 1 = 2 * m + 2 by omega, he]
    push_cast
    ring

/-- The permanent congruence holds at every positive power of an odd prime,
modulo the underlying prime. -/
private theorem prime_power_congruence (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    (p : ℤ) ∣ 2 * a (p ^ k) + 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let n := p ^ k
  let _ : NeZero n := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hodd : Odd n := (hp.odd_of_ne_two hp2).pow
  have hn0 : (n : ZMod p) = 0 := by
    simp [n, Nat.cast_pow, ne_of_gt hk]
  let e := (ZMod.finEquiv n).toEquiv
  let signedWeight (x : ZMod n) : ZMod p := (-1) ^ x.val * (x.val : ZMod p)
  have ha : (a n : ZMod p) = ∑ σ : Equiv.Perm (ZMod n), ∏ x : ZMod n,
      signedWeight (σ x - x) := by
    simp only [a, matrixPerm, toeplitzMatrix, Int.cast_sum, Int.cast_prod, Int.cast_natCast, id_eq]
    apply Fintype.sum_equiv (e.permCongr)
    intro σ
    rw [← Fintype.prod_equiv e (fun i => signedWeight (e (σ i) - e i)) _
      (fun i => by rw [Equiv.permCongr_apply, e.symm_apply_apply])]
    simp_rw [show ∀ i j : Fin n, signedWeight (e j - e i) = _ from signedWeight_sub hodd hn0,
      Finset.prod_mul_distrib]
    -- The row and column signs have the same product because σ permutes the indices.
    have hsigns : (∏ i : Fin n, (-1 : ZMod p) ^ (σ i).val) =
        ∏ i : Fin n, (-1 : ZMod p) ^ i.val :=
      Fintype.prod_equiv σ _ _ (fun _ => rfl)
    rw [hsigns, ← Finset.prod_mul_distrib]
    simp [← pow_add, ← two_mul, pow_mul]
  change (p : ℤ) ∣ 2 * a n + 1
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Int.cast_one, ha, circulant_permanent p n k rfl]
  have hsum : (∑ x : ZMod n, signedWeight x) =
      ∑ i ∈ Finset.range n, (-1 : ZMod p) ^ i * (i : ZMod p) := by
    rw [← Fin.sum_univ_eq_sum_range]
    symm
    apply Fintype.sum_equiv e
    intro i
    change _ = (-1 : ZMod p) ^ (e i).val * ((e i).val : ZMod p)
    rw [show (e i).val = i.val from finEquiv_val i]
  obtain ⟨m, hm⟩ := hodd
  have hbound : Finset.range n = Finset.range (2 * m + 1) := congrArg Finset.range hm
  rw [hsum, hbound, alternating_sum]
  have hcast : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by rwa [← hm]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hcast

/-- The first conjunct of A085807 holds for every odd prime. -/
private theorem prime_congruence (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ℤ) ∣ 2 * a p + 1 := by
  simpa only [pow_one] using prime_power_congruence p 1 hp hp2 Nat.one_pos

open Finset in
/-- Ryser's inclusion-exclusion formula. The proof follows the one by
@cjchaffin in proofs/mo-513259.lean. -/
private theorem matrixPerm_eq_ryser {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    matrixPerm A = ∑ s ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℤ)^(n-s.card) * ∏ i, ∑ j ∈ s, A i j := by
  classical
  let S (j : Fin n) : Finset (Fin n → Fin n) := univ.filter fun f => ∀ i, f i ≠ j
  let w (f : Fin n → Fin n) := ∏ i, A i (f i)
  have good (f : Fin n → Fin n) :
      f ∈ (univ.inf (fun j => (S j)ᶜ)) ↔ Function.Surjective f := by
    simp [S, Finset.mem_inf, Function.Surjective]
  have avoid (t : Finset (Fin n)) : t.inf S = Fintype.piFinset (fun _ : Fin n => tᶜ) := by
    ext f
    simp only [Finset.mem_inf, S, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_compl]
    constructor
    · intro h i hi
      exact h (f i) hi i rfl
    · intro h j hj i he
      exact h i (he ▸ hj)
  calc
    _ = ∑ f ∈ (univ.inf (fun j => (S j)ᶜ)), w f := by
      unfold matrixPerm
      apply sum_bij (fun (σ : Equiv.Perm (Fin n)) _ => (σ : Fin n → Fin n))
      · intro σ _; exact (good _).mpr σ.surjective
      · intro σ _ τ _ h; exact Equiv.ext (congrFun h)
      · intro f hf
        have hb := (Finite.surjective_iff_bijective).mp ((good _).mp hf)
        exact ⟨Equiv.ofBijective f hb, mem_univ _, rfl⟩
      · intros; rfl
    _ = ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (-1 : ℤ)^t.card • ∑ f ∈ t.inf S, w f :=
      inclusion_exclusion_sum_inf_compl _ _ _
    _ = _ := by
      apply sum_bij (fun t _ => tᶜ)
      · intros; simp
      · intro t _ s _ h; simpa using congrArg (fun v : Finset (Fin n) => vᶜ) h
      · intro s _; exact ⟨sᶜ, by simp, compl_compl s⟩
      · intro t ht
        have hc : t.card ≤ n := by simpa using card_le_univ t
        rw [avoid, show (∑ f ∈ Fintype.piFinset (fun _ : Fin n => tᶜ), w f) =
          ∏ i, ∑ j ∈ tᶜ, A i j from sum_prod_piFinset _ _]
        simp [Finset.card_compl, Nat.sub_sub_self hc]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem small_perm_minimum (n : ℕ) (hn : n ≤ 6) :
    ∀ σ : Equiv.Perm (Fin n),
      (∀ i : Fin n, i.val = 0 → (σ i).val = 0) →
      a n ≤ matrixPerm (toeplitzMatrix n (fun k => if hk : k < n then (σ ⟨k, hk⟩).val else 0)) := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  simp only [a, matrixPerm_eq_ryser]
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

/-- The distance matrix minimizes the permanent in dimensions up to six. -/
private theorem minimum_small (n : ℕ) (hn : n ≤ 6) (f : ℕ → ℕ) (hf : f 0 = 0)
    (h : Set.BijOn f (Set.Ico 1 n) (Set.Ico 1 n)) :
    a n ≤ matrixPerm (toeplitzMatrix n f) := by
  have inside (i : Fin n) (hi : i.val ≠ 0) : i.val ∈ Set.Ico 1 n :=
    ⟨Nat.one_le_iff_ne_zero.mpr hi, i.isLt⟩
  let w (i : Fin n) : Fin n := ⟨f i.val, by
    by_cases hi : i.val = 0
    · rw [hi, hf]
      exact Nat.zero_lt_of_lt i.isLt
    · exact (h.mapsTo (inside i hi)).2⟩
  have inj : Function.Injective w := by
    intro i j hij
    have he : f i.val = f j.val := congrArg Fin.val hij
    apply Fin.ext
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · exact hi.trans hj.symm
      · have hpos := (h.mapsTo (inside j hj)).1
        rw [hi, hf] at he
        omega
    · by_cases hj : j.val = 0
      · have hpos := (h.mapsTo (inside i hi)).1
        rw [hj, hf] at he
        omega
      · exact h.injOn (inside i hi) (inside j hj) he
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective w inj.bijective_of_finite
  have hz (i : Fin n) (hi : i.val = 0) : (σ i).val = 0 := by
    change f i.val = 0
    rw [hi, hf]
  have hm : toeplitzMatrix n (fun k => if hk : k < n then (σ ⟨k, hk⟩).val else 0) = toeplitzMatrix n f := by
    apply Matrix.ext
    intro i j
    have hd : ((i.val : ℤ) - j.val).natAbs < n := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp only [toeplitzMatrix, dif_pos hd]
    rfl
  rw [← hm]
  exact small_perm_minimum n hn σ hz

private theorem swap_bijOn (n d : ℕ) (hd : d ∈ Set.Ico 1 n)
    (hd' : d + 1 ∈ Set.Ico 1 n) :
    Set.BijOn (Equiv.swap d (d + 1)) (Set.Ico 1 n) (Set.Ico 1 n) := by
  have hmap : Set.MapsTo (Equiv.swap d (d + 1)) (Set.Ico 1 n) (Set.Ico 1 n) := by
    intro i hi
    rcases eq_or_ne i d with rfl | hi₁
    · simpa only [Equiv.swap_apply_left] using hd'
    rcases eq_or_ne i (d + 1) with rfl | hi₂
    · simpa only [Equiv.swap_apply_right] using hd
    · rwa [Equiv.swap_apply_of_ne_of_ne hi₁ hi₂]
  exact ⟨hmap, (Equiv.swap d (d + 1)).injective.injOn,
    fun i hi => ⟨(Equiv.swap d (d + 1)) i, hmap hi, Equiv.swap_apply_self _ _ _⟩⟩

private theorem swap_decreases_score (n d : ℕ) (hd : 1 ≤ d) (hd' : d + 1 < n)
    (f : ℕ → ℕ) (hlt : f (d + 1) < f d) :
    (∑ i ∈ Finset.Ico 1 n, (n - i) * (f ∘ Equiv.swap d (d + 1)) i) <
      ∑ i ∈ Finset.Ico 1 n, (n - i) * f i := by
  let s := Finset.Ico 1 n
  let g := f ∘ Equiv.swap d (d + 1)
  let w (h : ℕ → ℕ) (i : ℕ) := (n - i) * h i
  have ha : d ∈ s := Finset.mem_Ico.mpr ⟨hd, by omega⟩
  have hb : d + 1 ∈ s.erase d :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, hd'⟩⟩
  have hsplit (h : ℕ → ℕ) :
      (∑ i ∈ (s.erase d).erase (d + 1), w h i) + w h (d + 1) + w h d =
        ∑ i ∈ s, w h i := by
    rw [Finset.sum_erase_add _ _ hb, Finset.sum_erase_add _ _ ha]
  have hrest : (∑ i ∈ (s.erase d).erase (d + 1), w g i) =
      ∑ i ∈ (s.erase d).erase (d + 1), w f i := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi₁, hi'⟩ := Finset.mem_erase.mp hi
    obtain ⟨hi₂, _⟩ := Finset.mem_erase.mp hi'
    simp only [w, g, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hi₂ hi₁]
  change (∑ i ∈ s, w g i) < ∑ i ∈ s, w f i
  rw [← hsplit g, ← hsplit f, hrest]
  simp only [w, g, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hweight : n - d = n - (d + 1) + 1 := by omega
  rw [hweight, Nat.add_mul, Nat.add_mul]
  simp only [one_mul]
  omega

private theorem min_from_swaps (h1 : H1) (h2 : H2) (n : ℕ) (hn : 6 < n) :
    ∀ f : ℕ → ℕ, f 0 = 0 → Set.BijOn f (Set.Ico 1 n) (Set.Ico 1 n) →
      a n ≤ matrixPerm (toeplitzMatrix n f) := by
  classical
  let score (f : ℕ → ℕ) := ∑ i ∈ Finset.Ico 1 n, (n - i) * f i
  suffices h : ∀ k (f : ℕ → ℕ), score f = k → f 0 = 0 →
      Set.BijOn f (Set.Ico 1 n) (Set.Ico 1 n) →
      a n ≤ matrixPerm (toeplitzMatrix n f) by
    intro f
    exact h (score f) f rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f hscore hf hbij
    by_cases hsorted : ∀ i ∈ Set.Ico 1 n, f i = i
    · have hmatrix : toeplitzMatrix n f = toeplitzMatrix n id := by
        apply Matrix.ext
        intro i j
        let d := ((i.val : ℤ) - j.val).natAbs
        have hd : d < n := by
          have hi := i.isLt
          have hj := j.isLt
          dsimp [d]
          omega
        change (f d : ℤ) = (d : ℤ)
        by_cases hzero : d = 0
        · rw [hzero, hf]
        · rw [hsorted d ⟨by omega, hd⟩]
      rw [hmatrix, a]
    · push Not at hsorted
      obtain ⟨i, hi, hii⟩ := hsorted
      let bad := (Finset.Ico 1 n).filter (fun i => f i ≠ i)
      have hbad : bad.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hi, hii⟩⟩
      let r := bad.max' hbad
      obtain ⟨hr, hrne⟩ := Finset.mem_filter.mp (Finset.max'_mem bad hbad)
      have hrset : r ∈ Set.Ico 1 n := Finset.mem_Ico.mp hr
      have htail (j : ℕ) (hjr : r < j) (hjn : j < n) : f j = j := by
        by_contra hj
        have hjmem : j ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
          ⟨by have := hrset.1; omega, hjn⟩, hj⟩
        exact (not_le_of_gt hjr) (Finset.le_max' bad j hjmem)
      obtain ⟨d, hd, hdr⟩ := hbij.surjOn hrset
      have hdlt : d < r := by
        rcases lt_trichotomy d r with h | h | h
        · exact h
        · subst d
          exact (hrne hdr).elim
        · exact (ne_of_gt h) ((htail d h hd.2).symm.trans hdr) |>.elim
      have hd' : d + 1 ∈ Set.Ico 1 n := ⟨by have := hd.1; omega,
        by have := hrset.2; omega⟩
      have hinv : f (d + 1) < r := by
        have hmem := hbij.mapsTo hd'
        rcases lt_trichotomy (f (d + 1)) r with h | h | h
        · exact h
        · have he := hbij.injOn hd' hd (h.trans hdr.symm)
          omega
        · have hv := htail _ h hmem.2
          have he := hbij.injOn hd' hmem hv.symm
          omega
      let g := f ∘ Equiv.swap d (d + 1)
      have hg0 : g 0 = 0 := by
        have hdpos := hd.1
        simp only [g, Function.comp_apply,
          Equiv.swap_apply_of_ne_of_ne (by omega : 0 ≠ d) (by omega : 0 ≠ d + 1), hf]
      have hgbij : Set.BijOn g (Set.Ico 1 n) (Set.Ico 1 n) :=
        hbij.comp (swap_bijOn n d hd hd')
      have hscore' : score g < k := hscore ▸ swap_decreases_score n d hd.1 hd'.2 f
        (by rw [hdr]; exact hinv)
      have hle := ih (score g) hscore' g rfl hg0 hgbij
      apply hle.trans
      by_cases hnear : 2 * d < n
      · exact h1 n r d f hn hd.1 hdlt hrset.2 hnear hf hbij htail hdr hinv
      · exact h2 n r d f hn hd.1 hdlt hrset.2 (Nat.le_of_not_gt hnear)
          hf hbij htail hdr hinv

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085807.main := by
  intro h1 h2
  refine ⟨prime_congruence, ?_⟩
  intro n f hf hbij
  by_cases hn : n ≤ 6
  · exact minimum_small n hn f hf hbij
  · exact min_from_swaps h1 h2 n (lt_of_not_ge hn) f hf hbij

end OMA.R_oeis_a085807_R1
