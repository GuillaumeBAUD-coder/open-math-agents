import FormalConjectures.GreensOpenProblems.«44»

/-! A second-moment sieve using iterated interval averages. Each pair of
distinct primes gives a centered function of period at most N. Averaging
over 3N integers contracts its sup norm by a factor of three. After eight
averages the off-diagonal terms are small. The enlarged interval has length
25N, and its total smoothed mass dominates the original mass on [1,N]. -/

noncomputable section
open Finset
namespace Green44Sieve

private def avg (H : ℕ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  (∑ t ∈ range H, f (x - t)) / H

private def smooth (H : ℕ) : ℕ → (ℤ → ℝ) → ℤ → ℝ
  | 0, f => f
  | k + 1, f => avg H (smooth H k f)

private def zeroBlock (q : ℕ) (f : ℤ → ℝ) : Prop :=
  ∀ x, ∑ t ∈ range q, f (x - t) = 0

private lemma zeroBlock_avg {q H : ℕ} {f : ℤ → ℝ} (h : zeroBlock q f) :
    zeroBlock q (avg H f) := by
  intro x
  simp only [avg, ← sum_div, sum_comm (s := range q) (t := range H)]
  have e (t : ℕ) : (∑ u ∈ range q, f (x - u - t)) = 0 := by
    convert h (x - t) using 1
    apply sum_congr rfl
    intro u _
    congr 1
    omega
  simp [e]

private lemma zeroBlock_smooth {q H : ℕ} {f : ℤ → ℝ} (h : zeroBlock q f) (k : ℕ) :
    zeroBlock q (smooth H k f) := by
  induction k with
  | zero => exact h
  | succ k ih => exact zeroBlock_avg ih

private lemma block_mul {q : ℕ} {f : ℤ → ℝ} (h : zeroBlock q f) (l : ℕ) (x : ℤ) :
    ∑ t ∈ range (l*q), f (x - t) = 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Nat.succ_mul, sum_range_add, ih, zero_add]
    simpa only [Nat.cast_add, sub_add_eq_sub_sub] using h (x - ↑(l*q))

private lemma avg_small {q H : ℕ} {f : ℤ → ℝ} {B : ℝ} (h : zeroBlock q f)
    (hf : ∀ x, |f x| ≤ B) (hq : 0 < q) (hH : 3*q ≤ H) (x : ℤ) :
    |avg H f x| ≤ B / 3 := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  have splitting : H / q * q + H % q = H := by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have e : (∑ t ∈ range H, f (x-t)) =
      ∑ t ∈ range (H%q), f (x - ↑(H/q*q + t)) := by
    conv_lhs => rw [← splitting, sum_range_add, block_mul h, zero_add]
  rw [avg, abs_div, abs_of_pos hHp, div_le_iff₀ hHp, e]
  calc |∑ t ∈ range (H%q), f (x - ↑(H/q*q + t))| ≤
      ∑ t ∈ range (H%q), |f (x - ↑(H/q*q + t))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ range (H%q), B := sum_le_sum fun t _ => hf _
    _ = (H%q : ℕ) * B := by simp
    _ ≤ B / 3 * H := by
      have hq' : (3:ℝ) * (H%q : ℕ) ≤ H := by
        exact_mod_cast (show 3*(H%q) ≤ H by have := Nat.mod_lt H hq; omega)
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hq')]

private lemma smooth_small {q H : ℕ} {f : ℤ → ℝ} (B : ℝ) (h : zeroBlock q f)
    (hf : ∀ x, |f x| ≤ B) (hq : 0 < q) (hH : 3*q ≤ H) (k : ℕ) (x : ℤ) :
    |smooth H k f x| ≤ B / 3 ^ k := by
  induction k generalizing x with
  | zero => simpa [smooth] using hf x
  | succ k ih =>
    simpa [smooth, pow_succ, ← div_mul_eq_div_div] using
      avg_small (zeroBlock_smooth h k) ih hq hH x

private lemma smooth_le {H : ℕ} (hH : 0 < H) {f : ℤ → ℝ} {B : ℝ}
    (hf : ∀ x, f x ≤ B) (k : ℕ) (x : ℤ) : smooth H k f x ≤ B := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih =>
    change (∑ t ∈ range H, smooth H k f (x-t)) / H ≤ B
    apply (div_le_iff₀ (by exact_mod_cast hH : (0:ℝ) < H)).mpr
    simpa [mul_comm] using (sum_le_sum (s := range H) (fun t _ => ih (x - t)))

private lemma smooth_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ → ℝ)
    (H k : ℕ) (x : ℤ) :
    smooth H k (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, smooth H k (g i) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [smooth, avg, ih, ← sum_div, sum_comm (s := range H) (t := s)]

private lemma smooth_nonneg (H k : ℕ) {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℤ) :
    0 ≤ smooth H k f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih => exact div_nonneg (sum_nonneg fun t _ => ih _) (Nat.cast_nonneg _)

private lemma shift_mass {M H : ℕ} (f : ℤ → ℝ) (hf : ∀ x, 0 ≤ f x) {t : ℕ}
    (ht : t ∈ range H) :
    (∑ x ∈ Icc (1:ℤ) M, f x) ≤ ∑ x ∈ Icc (1:ℤ) (M+H:ℕ), f (x-t) := by
  let e := Equiv.addRight (t : ℤ)
  have hs : (Icc (1:ℤ) M).map e.toEmbedding ⊆ Icc 1 (M+H:ℕ) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    change y + t ∈ _
    rw [mem_Icc] at hy ⊢
    have := mem_range.mp ht
    push_cast
    omega
  have h := sum_le_sum_of_subset_of_nonneg (f := fun x : ℤ => f (x-t)) hs
    (fun x _ _ => hf _)
  simpa [e] using h

private lemma mass_le {H : ℕ} (hH : 0 < H) {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (N k : ℕ) :
    (∑ x ∈ Icc (1:ℤ) N, f x) ≤ ∑ x ∈ Icc (1:ℤ) (N+k*H:ℕ), smooth H k f x := by
  induction k with
  | zero => simp [smooth]
  | succ k ih =>
    refine ih.trans ?_
    simp only [smooth, avg, Nat.succ_mul, ← Nat.add_assoc, ← sum_div,
      sum_comm (t := range H)]
    apply (le_div_iff₀ (by exact_mod_cast hH : (0:ℝ) < H)).mpr
    calc _ = ∑ _ ∈ range H, ∑ x ∈ Icc (1:ℤ) (N+k*H:ℕ), smooth H k f x := by
              simp [mul_comm]
         _ ≤ _ := sum_le_sum fun t ht => shift_mass _ (smooth_nonneg H k hf) ht

/-- The score is one on surviving residue classes and has mean zero. -/
private def score {p : ℕ} (A : Finset (ZMod p)) (z : ZMod p) : ℝ :=
  1 - if z ∈ A then (p:ℝ) / A.card else 0

private lemma score_sum {p : ℕ} [NeZero p] {A : Finset (ZMod p)} (hA : A.card ≠ 0) :
    ∑ z, score A z = 0 := by
  classical
  simp [score, sum_sub_distrib, sum_ite_mem, ZMod.card, hA, mul_div_cancel₀]

private lemma score_abs {p : ℕ} {A : Finset (ZMod p)} (hp : 5 ≤ p) (ha : A.card = p/2)
    (z : ZMod p) : |score A z| ≤ 3/2 := by
  simp only [score]; split_ifs with h
  · have hc : (0:ℝ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
    have hu : (2:ℝ)*p ≤ 5*A.card := by exact_mod_cast (by omega : 2*p ≤ 5*A.card)
    rw [abs_le]
    constructor
    · have hdiv := (div_le_iff₀ hc).mpr (show (p:ℝ) ≤ 5/2 * A.card by linarith)
      linarith
    · have := div_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hc.le
      linarith
  · norm_num

private lemma finEquiv_apply_val {m : ℕ} [hm : NeZero m] (i : Fin m) :
    ZMod.finEquiv m i = (i.val : ZMod m) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    exact (ZMod.natCast_zmod_val (n := m+1) i).symm

private lemma pair_zero {p q : ℕ} [NeZero p] [NeZero q] (hpq : p.Coprime q)
    (A : Finset (ZMod p)) (B : Finset (ZMod q)) (hb : B.card ≠ 0) :
    zeroBlock (p*q) (fun x => score A (x : ZMod p) * score B (x : ZMod q)) := by
  intro x
  let crt := ZMod.chineseRemainder hpq
  let e := (ZMod.finEquiv (p*q)).toEquiv.trans
    ((Equiv.subLeft (x : ZMod (p*q))).trans crt.toEquiv)
  let F := fun z : ZMod p × ZMod q => score A z.1 * score B z.2
  rw [← Fin.sum_univ_eq_sum_range]
  calc _ = ∑ i : Fin (p*q), F (e i) := by
          apply sum_congr rfl
          intro i _
          simp [F, e, Equiv.subLeft, finEquiv_apply_val, crt, map_sub, map_natCast, map_intCast]
       _ = ∑ z, F z := e.sum_comp _
       _ = 0 := by
         rw [Fintype.sum_prod_type]
         simp [F, ← mul_sum, score_sum hb]

/-- Bound the smoothed square of the total score by summing the diagonal
and off-diagonal terms separately. -/
private lemma moment {N : ℕ} (hN : 0 < N) (g : Fin 900 → ℤ → ℝ)
    (hg : ∀ i x, |g i x| ≤ 3/2)
    (hpair : ∀ i j, i ≠ j → ∃ q, 0 < q ∧ q ≤ N ∧
      zeroBlock q (fun x => g i x * g j x)) (x : ℤ) :
    smooth (3*N) 8 (fun y => (∑ i, g i y)^2) x ≤
      900 * (9/4 + 900*(9/4/6561)) := by
  have hprod (i j : Fin 900) (y : ℤ) : |g i y * g j y| ≤ 9/4 := by
    rw [abs_mul]
    have := mul_le_mul (hg i y) (hg j y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
    linarith
  have hb (i j : Fin 900) : smooth (3*N) 8 (fun y => g i y * g j y) x ≤
      (if j = i then 9/4 else 0) + 9/4/6561 := by
    split_ifs with hij
    · exact (smooth_le (by omega) (fun y => (le_abs_self _).trans (hprod i j y)) 8 x).trans
        (by norm_num)
    · obtain ⟨q,hq,hqn,hz⟩ := hpair i j (Ne.symm hij)
      have h := smooth_small (9/4) hz (hprod i j) hq (by omega : 3*q ≤ 3*N) 8 x
      exact (le_abs_self _).trans (by norm_num at h ⊢; exact h)
  have ident : (fun y => (∑ i, g i y)^2) =
      fun y => ∑ i, ∑ j, g i y * g j y := by
    funext y
    simp [sq, sum_mul, mul_sum]
    exact sum_comm
  rw [ident, smooth_sum]
  simp only [smooth_sum]
  calc _ ≤ ∑ i : Fin 900, ∑ j : Fin 900,
          ((if j = i then (9:ℝ)/4 else 0) + 9/4/6561) :=
            sum_le_sum fun i _ => sum_le_sum fun j _ => hb i j
       _ = _ := by simp [sum_add_distrib]; ring

end Green44Sieve

open Green44Sieve in
theorem OMA.solution : type_of% @Green44.green_44.variants.less_than_sqrt := by
  classical
  intro N p A
  dsimp only
  intro hp hm hN hA
  let pick (i : Fin 900) : Fin 1000 := ⟨100+i.val, by omega⟩
  have hlarge (i : Fin 900) : 5 ≤ p (pick i) := by
    have h0 := (hp 0).two_le
    have h1 := hm (show (0:Fin 1000) < 1 by decide)
    have h2 := hm (show (1:Fin 1000) < 2 by decide)
    have h3 := hm (show (2:Fin 1000) < pick i from by change 2 < 100+i.val; omega)
    omega
  let g (i : Fin 900) (y : ℤ) : ℝ := score (A (pick i)) (y : ZMod (p (pick i)))
  have hg (i : Fin 900) (y : ℤ) : |g i y| ≤ 3/2 :=
    score_abs (hlarge i) (hA _) _
  have hpair (i j : Fin 900) (hne : i ≠ j) : ∃ q, 0 < q ∧ q ≤ N ∧
      zeroBlock q (fun x => g i x * g j x) := by
    let a := p (pick i)
    let b := p (pick j)
    have ha : a.Prime := hp _
    have hb : b.Prime := hp _
    let : NeZero a := ⟨ha.ne_zero⟩
    let : NeZero b := ⟨hb.ne_zero⟩
    have hab : a ≠ b := by
      intro h
      have hh := congrArg Fin.val (hm.injective h)
      exact hne (Fin.ext (by dsimp [pick] at hh; omega))
    have hcop : a.Coprime b := Nat.coprime_primes ha hb |>.mpr hab
    have hle (k : Fin 900) : p (pick k) ≤ p 999 :=
      hm.monotone (show pick k ≤ 999 from Fin.le_last _)
    refine ⟨a*b, Nat.mul_pos ha.pos hb.pos, ?_, ?_⟩
    · exact (Nat.mul_le_mul (hle i) (hle j)).trans (by simpa [sq] using hN.le)
    · exact pair_zero hcop _ _ (by have := hA (pick j); have := hlarge j; omega)
  let R := (Icc 1 N).filter (fun x : ℕ => ∀ i, (x : ZMod (p i)) ∉ A i)
  let W := fun y : ℤ => (∑ i, g i y)^2
  have hW (y : ℤ) : 0 ≤ W y := sq_nonneg _
  have hpoint (u : ℕ) (hu : u ∈ R) : W (u : ℤ) = 900^2 := by
    have h := (mem_filter.mp hu).2
    simp [W, g, score, h]
  let inj : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
  have hsub : R.map inj ⊆ Icc (1:ℤ) N := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hy
    change (u:ℤ) ∈ _
    have hh := mem_Icc.mp (mem_filter.mp hu).1
    rw [mem_Icc]
    exact_mod_cast hh
  have hmass : (R.card : ℝ) * 900^2 ≤ ∑ y ∈ Icc (1:ℤ) N, W y := by
    calc _ = ∑ y ∈ R.map inj, W y := by
              rw [sum_map]
              change _ = ∑ u ∈ R, W (u:ℤ)
              rw [sum_congr rfl hpoint, sum_const, nsmul_eq_mul]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => hW y
  have hn : 0 < N := by omega
  have hmom := fun x => moment hn g hg hpair x
  have hbound : (R.card : ℝ)*900^2 ≤
      ((N + 8*(3*N):ℕ):ℝ)*(900*(9/4 + 900*(9/4/6561))) := by
    refine (hmass.trans (mass_le (by omega : 0 < 3*N) hW N 8)).trans ?_
    have hb := sum_le_sum (s := Icc (1:ℤ) (N+8*(3*N):ℕ)) (fun y _ => hmom y)
    simpa only [sum_const, Int.card_Icc, add_sub_cancel_right, Int.toNat_natCast,
      nsmul_eq_mul] using hb
  change 10 * R.card ≤ N
  exact_mod_cast (show 10*(R.card:ℝ) ≤ N by push_cast at hbound; nlinarith)

end
