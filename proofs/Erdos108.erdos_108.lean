import FormalConjectures.ErdosProblems.«108»

/-!
# Erdos Problem 108

We disprove the Erdos-Hajnal girth-chromatic conjecture at girth 5 and chromatic threshold 5.
Following the line-digraph and unbalanced random multipartite method of Kohlmeyer-Kruer and
Nguyen-Walczak, for every target threshold `f` we construct a finite oriented multipartite graph
whose line graph has chromatic number at least `f`, is triangle-free, and has the property that
every `C_4`-free subgraph is `4`-colorable. Consequently every subgraph of girth at least `5` has
chromatic number at most `4`.
-/

namespace OMAErdos108

open Finset SimpleGraph
open scoped Classical

/- ## Section 1: Elementary factorial, binomial, and geometric bounds -/

lemma choose_mul_factorial_le_pow : ∀ (A k : ℕ), A.choose k * k.factorial ≤ A ^ k
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | A + 1, k + 1 => by
      have ih := choose_mul_factorial_le_pow A k
      have hchoose : (A + 1).choose (k + 1) * (k + 1) = (A + 1) * A.choose k := by
        simpa [mul_comm] using (Nat.add_one_mul_choose_eq A k).symm
      calc
        (A + 1).choose (k + 1) * (k + 1).factorial
            = ((A + 1).choose (k + 1) * (k + 1)) * k.factorial := by
                rw [Nat.factorial_succ]; ring
        _ = (A + 1) * (A.choose k * k.factorial) := by rw [hchoose]; ring
        _ ≤ (A + 1) * A ^ k := Nat.mul_le_mul_left (A + 1) ih
        _ ≤ (A + 1) * (A + 1) ^ k :=
            Nat.mul_le_mul_left (A + 1) (Nat.pow_le_pow_left (Nat.le_succ A) k)
        _ = (A + 1) ^ (k + 1) := by rw [pow_succ']

lemma two_pow_pred_le_factorial : ∀ m : ℕ, 2 ≤ m → 2 ^ (m - 1) ≤ m.factorial
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by norm_num [Nat.factorial]
  | m + 3, _ => by
      have ih := two_pow_pred_le_factorial (m + 2) (by omega)
      calc
        2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ']
        _ ≤ (m + 3) * (m + 2).factorial := Nat.mul_le_mul (by omega) ih
        _ = (m + 3).factorial := (Nat.factorial_succ (m + 2)).symm

lemma sum_two_pow_lt : ∀ n : ℕ, ∑ i ∈ Finset.range n, 2 ^ i < 2 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, pow_succ']
      have ih := sum_two_pow_lt n
      omega

lemma succ_pow_le_three_mul_pow (k : ℕ) (hk : 1 ≤ k) : (k + 1) ^ k ≤ 3 * k ^ k := by
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  suffices h : 2 ^ (k - 1) * (1 + k) ^ k ≤ 2 ^ (k - 1) * (3 * k ^ k) by
    rw [add_comm] at h
    exact Nat.le_of_mul_le_mul_left h hpos
  rw [add_pow]
  rw [Finset.mul_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      2 ^ (k - 1) * (1 ^ m * k ^ (k - m) * k.choose m) ≤
        (if m = 0 then 2 ^ (k - 1) else if m = 1 then 2 ^ (k - 1) else 2 ^ (k - m)) * k ^ k := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hmk : m ≤ k := by omega
    simp only [one_pow, one_mul]
    have hcf : k.choose m * m.factorial ≤ k ^ m := choose_mul_factorial_le_pow k m
    have hkpow : k ^ (k - m) * k ^ m = k ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hmk]
    rcases m with _ | _ | m'
    · simp
    · simp only [zero_add, Nat.reduceEqDiff, ↓reduceIte, Nat.choose_one_right]
      have h1 : k ^ (k - 1) * k = k ^ k := by
        simpa [pow_one] using hkpow
      rw [h1]
    · have hm2 : 2 ≤ m' + 2 := by omega
      simp only [Nat.add_eq_zero_iff, and_false, ↓reduceIte,
        Nat.reduceEqDiff]
      have hfac : 2 ^ (m' + 1) ≤ (m' + 2).factorial := two_pow_pred_le_factorial (m' + 2) hm2
      have h1 : k.choose (m' + 2) * 2 ^ (m' + 1) ≤ k ^ (m' + 2) :=
        (Nat.mul_le_mul_left _ hfac).trans hcf
      have h2 : 2 ^ (k - 1) = 2 ^ (k - (m' + 2)) * 2 ^ (m' + 1) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        2 ^ (k - 1) * (k ^ (k - (m' + 2)) * k.choose (m' + 2))
            = 2 ^ (k - (m' + 2)) * k ^ (k - (m' + 2)) * (k.choose (m' + 2) * 2 ^ (m' + 1)) := by
                rw [h2]; ring
        _ ≤ 2 ^ (k - (m' + 2)) * k ^ (k - (m' + 2)) * k ^ (m' + 2) :=
            Nat.mul_le_mul_left _ h1
        _ = 2 ^ (k - (m' + 2)) * k ^ k := by rw [mul_assoc, hkpow]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hcoeff : ∑ m ∈ Finset.range (k + 1),
      (if m = 0 then 2 ^ (k - 1) else if m = 1 then 2 ^ (k - 1) else 2 ^ (k - m)) ≤
        3 * 2 ^ (k - 1) := by
    rcases eq_or_lt_of_le hk with rfl | hk2
    · norm_num [Finset.sum_range_succ]
    · have hsplit : Finset.range (k + 1) = insert 0 (insert 1 (Finset.Ico 2 (k + 1))) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
        omega
      rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      simp only [↓reduceIte, one_ne_zero]
      have hico : ∑ m ∈ Finset.Ico 2 (k + 1),
          (if m = 0 then 2 ^ (k - 1) else if m = 1 then 2 ^ (k - 1) else 2 ^ (k - m)) =
          ∑ i ∈ Finset.range (k - 1), 2 ^ i := by
        refine Finset.sum_bij (fun m _ => k - m) ?_ ?_ ?_ ?_
        · intro m hm
          rw [Finset.mem_Ico] at hm
          rw [Finset.mem_range]
          omega
        · intro m₁ hm₁ m₂ hm₂ heq
          rw [Finset.mem_Ico] at hm₁ hm₂
          omega
        · intro i hi
          rw [Finset.mem_range] at hi
          refine ⟨k - i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro m hm
          rw [Finset.mem_Ico] at hm
          have hm0 : m ≠ 0 := by omega
          have hm1 : m ≠ 1 := by omega
          simp [hm0, hm1]
      rw [hico]
      have hlt := sum_two_pow_lt (k - 1)
      omega
  calc
    (∑ m ∈ Finset.range (k + 1),
        (if m = 0 then 2 ^ (k - 1) else if m = 1 then 2 ^ (k - 1) else 2 ^ (k - m))) * k ^ k
        ≤ (3 * 2 ^ (k - 1)) * k ^ k := Nat.mul_le_mul_right _ hcoeff
    _ = 2 ^ (k - 1) * (3 * k ^ k) := by ring

lemma pow_le_three_pow_mul_factorial : ∀ k : ℕ, k ^ k ≤ 3 ^ k * k.factorial
  | 0 => by simp
  | k + 1 => by
      rcases eq_or_ne k 0 with rfl | hk0
      · norm_num [Nat.factorial]
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
        have ih := pow_le_three_pow_mul_factorial k
        have hstep := succ_pow_le_three_mul_pow k hk1
        calc
          (k + 1) ^ (k + 1) = (k + 1) * (k + 1) ^ k := by rw [pow_succ']
          _ ≤ (k + 1) * (3 * k ^ k) := Nat.mul_le_mul_left (k + 1) hstep
          _ = 3 * (k + 1) * k ^ k := by ring
          _ ≤ 3 * (k + 1) * (3 ^ k * k.factorial) := Nat.mul_le_mul_left _ ih
          _ = 3 ^ (k + 1) * (k + 1).factorial := by
              rw [pow_succ', Nat.factorial_succ]; ring

lemma choose_mul_pow_le (A k : ℕ) : A.choose k * k ^ k ≤ (3 * A) ^ k := by
  have hpos : 0 < k.factorial := Nat.factorial_pos k
  suffices h : A.choose k * k ^ k * k.factorial ≤ (3 * A) ^ k * k.factorial by
    exact Nat.le_of_mul_le_mul_right h hpos
  calc
    A.choose k * k ^ k * k.factorial
        = A.choose k * k.factorial * k ^ k := by ring
    _ ≤ A ^ k * (3 ^ k * k.factorial) :=
        Nat.mul_le_mul (choose_mul_factorial_le_pow A k) (pow_le_three_pow_mul_factorial k)
    _ = (3 * A) ^ k * k.factorial := by rw [mul_pow]; ring

lemma nat_lt_two_pow_succ : ∀ n : ℕ, n < 2 ^ (n + 1)
  | 0 => by norm_num
  | n + 1 => by
      have ih := nat_lt_two_pow_succ n
      have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [pow_succ']
      omega

lemma sum_geom_Icc_four_le {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (M : ℕ) :
    ∑ r ∈ Finset.Icc 4 M, x ^ r ≤ 2 * x ^ 4 := by
  by_cases hM : M < 4
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hbij : ∑ r ∈ Finset.Icc 4 M, x ^ r = x ^ 4 * ∑ k ∈ Finset.range (M - 3), x ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun r _ => r - 4) ?_ ?_ ?_ ?_
      · intro r hr; rw [Finset.mem_Icc] at hr; rw [Finset.mem_range]; omega
      · intro r₁ hr₁ r₂ hr₂ h; rw [Finset.mem_Icc] at hr₁ hr₂; omega
      · intro k hk; rw [Finset.mem_range] at hk
        exact ⟨k + 4, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro r hr
        rw [Finset.mem_Icc] at hr
        rw [← pow_add]
        congr 1
        omega
    rw [hbij]
    have hgeom : ∑ k ∈ Finset.range (M - 3), x ^ k ≤ 2 := by
      have hid : (1 - x) * ∑ k ∈ Finset.range (M - 3), x ^ k = 1 - x ^ (M - 3) := by
        have h := geom_sum_mul_neg x (M - 3)
        linarith
      have hxpow : 0 ≤ x ^ (M - 3) := pow_nonneg hx0 _
      nlinarith
    exact (mul_le_mul_of_nonneg_left hgeom (pow_nonneg hx0 4)).trans_eq (mul_comm _ _)

def sixToTwoSet : Fin 6 → { s : Finset (Fin 4) // s.card = 2 }
  | ⟨0, _⟩ => ⟨{0, 1}, by decide⟩
  | ⟨1, _⟩ => ⟨{0, 2}, by decide⟩
  | ⟨2, _⟩ => ⟨{0, 3}, by decide⟩
  | ⟨3, _⟩ => ⟨{1, 2}, by decide⟩
  | ⟨4, _⟩ => ⟨{1, 3}, by decide⟩
  | ⟨5, _⟩ => ⟨{2, 3}, by decide⟩

lemma sixToTwoSet_injective : Function.Injective sixToTwoSet := by
  decide

/- ## Section 2: Unbalanced random multipartite graph and counting bounds -/

section Construction

variable (f : ℕ)

abbrev k0 : ℕ := max f 1
abbrev qParam : ℕ := 2 ^ k0 f
abbrev CParam : ℕ := 16 * (qParam f) ^ 2
abbrev dParam : ℕ := CParam f - 1
abbrev deltaParam : ℕ := dParam f + dParam f * dParam f
abbrev DParam : ℕ := 576 * deltaParam f * (CParam f) ^ 2

lemma qParam_ge_two : 2 ≤ qParam f := by
  have hk : 1 ≤ k0 f := le_max_right f 1
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k0 f := Nat.pow_le_pow_right (by norm_num) hk

lemma CParam_ge_64 : 64 ≤ CParam f := by
  have hq : 2 ≤ qParam f := qParam_ge_two f
  dsimp [CParam]
  nlinarith

lemma deltaParam_pos : 1 ≤ deltaParam f := by
  have hC := CParam_ge_64 f
  dsimp [deltaParam, dParam]
  omega

lemma DParam_ge_C_add_two : CParam f + 2 ≤ DParam f := by
  have hC := CParam_ge_64 f
  have hdel := deltaParam_pos f
  dsimp [DParam]
  nlinarith

def blockExp (i : ℕ) : ℕ := 3 ^ CParam f - 3 ^ i

def blockSize (i : Fin (CParam f)) : ℕ := (DParam f) ^ (blockExp f i.val)

lemma blockExp_ge_two (i : Fin (CParam f)) : 2 ≤ blockExp f i.val := by
  have hpow : 3 ^ (i.val + 1) ≤ 3 ^ CParam f :=
    Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt i.isLt)
  have h1 : 1 ≤ 3 ^ i.val := Nat.one_le_pow _ _ (by norm_num)
  dsimp [blockExp]
  rw [pow_succ'] at hpow
  omega

lemma blockSize_ge_D_sq (i : Fin (CParam f)) : (DParam f) ^ 2 ≤ blockSize f i :=
  Nat.pow_le_pow_right (by have := DParam_ge_C_add_two f; omega) (blockExp_ge_two f i)

lemma blockSize_pos (i : Fin (CParam f)) : 0 < blockSize f i := by
  have hD : 1 ≤ DParam f := by have := DParam_ge_C_add_two f; omega
  have h := blockSize_ge_D_sq f i
  nlinarith

lemma blockSize_ge_C_add_two (i : Fin (CParam f)) : CParam f + 2 ≤ blockSize f i := by
  have hD := DParam_ge_C_add_two f
  have h := blockSize_ge_D_sq f i
  nlinarith

lemma blockSize_step {a b : Fin (CParam f)} (hab : a < b) :
    (DParam f) ^ 2 * blockSize f b ≤ blockSize f a := by
  have hexp : 2 + blockExp f b.val ≤ blockExp f a.val := by
    have hlt : a.val + 1 ≤ b.val := hab
    have hp1 : 3 ^ (a.val + 1) ≤ 3 ^ b.val := Nat.pow_le_pow_right (by norm_num) hlt
    have hp2 : 3 ^ b.val ≤ 3 ^ CParam f :=
      Nat.pow_le_pow_right (by norm_num) (le_of_lt b.isLt)
    have ha1 : 1 ≤ 3 ^ a.val := Nat.one_le_pow _ _ (by norm_num)
    dsimp [blockExp]
    rw [pow_succ'] at hp1
    omega
  calc
    (DParam f) ^ 2 * blockSize f b
        = (DParam f) ^ (2 + blockExp f b.val) := by rw [blockSize, pow_add]
    _ ≤ (DParam f) ^ (blockExp f a.val) :=
        Nat.pow_le_pow_right (by have := DParam_ge_C_add_two f; omega) hexp
    _ = blockSize f a := rfl

lemma blockSize_anti {a b : Fin (CParam f)} (hab : a ≤ b) :
    blockSize f b ≤ blockSize f a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · have hD : 1 ≤ (DParam f) ^ 2 := by have := DParam_ge_C_add_two f; nlinarith
    exact (Nat.le_mul_of_pos_left _ hD).trans (blockSize_step f hlt)

lemma blockSize_dexp {i : Fin (CParam f)} (hi : 1 ≤ i.val) :
    DParam f * (blockSize f ⟨0, by have := CParam_ge_64 f; omega⟩) ^ 2 * blockSize f i ≤
      (blockSize f ⟨i.val - 1, by omega⟩) ^ 3 := by
  have hC := CParam_ge_64 f
  have hip1 : 3 ^ i.val ≤ 3 ^ CParam f :=
    Nat.pow_le_pow_right (by norm_num) (le_of_lt i.isLt)
  have hip0 : 1 ≤ 3 ^ CParam f := Nat.one_le_pow _ _ (by norm_num)
  have hprev : 3 ^ (i.val - 1) ≤ 3 ^ CParam f :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul3 : 3 * 3 ^ (i.val - 1) = 3 ^ i.val := by
    conv_rhs => rw [show i.val = (i.val - 1) + 1 by omega, pow_succ']
  have hexp : 2 + 2 * blockExp f 0 + blockExp f i.val = 3 * blockExp f (i.val - 1) := by
    dsimp [blockExp]
    omega
  have hD1 : DParam f ≤ (DParam f) ^ 2 := by
    have := DParam_ge_C_add_two f
    nlinarith
  calc
    DParam f * (blockSize f ⟨0, by omega⟩) ^ 2 * blockSize f i
        ≤ (DParam f) ^ 2 * (blockSize f ⟨0, by omega⟩) ^ 2 * blockSize f i := by
            gcongr
    _ = (DParam f) ^ (2 + 2 * blockExp f 0 + blockExp f i.val) := by
          dsimp [blockSize]
          rw [← pow_mul, ← pow_add, ← pow_add]
          congr 1
          ring
    _ = (DParam f) ^ (3 * blockExp f (i.val - 1)) := by rw [hexp]
    _ = (blockSize f ⟨i.val - 1, by omega⟩) ^ 3 := by
          dsimp [blockSize]
          rw [← pow_mul, mul_comm]

lemma blockSize_four_delta_le {i : Fin (CParam f)} (hi : 1 ≤ i.val) :
    4 * deltaParam f * blockSize f i ≤ blockSize f ⟨i.val - 1, by omega⟩ := by
  have hlt : (⟨i.val - 1, by omega⟩ : Fin (CParam f)) < i :=
    Fin.mk_lt_mk.mpr (by omega)
  have hstep := blockSize_step f hlt
  have hD1 : 4 * deltaParam f ≤ DParam f := by
    have hC1 : 1 ≤ (CParam f) ^ 2 := by
      have := CParam_ge_64 f
      nlinarith
    calc
      4 * deltaParam f ≤ 576 * deltaParam f * 1 := by omega
      _ ≤ 576 * deltaParam f * (CParam f) ^ 2 := Nat.mul_le_mul_left _ hC1
  have hD2 : DParam f ≤ (DParam f) ^ 2 := by
    have := DParam_ge_C_add_two f
    nlinarith
  exact (Nat.mul_le_mul_right _ (hD1.trans hD2)).trans hstep

lemma tail_sum_blockSize_aux : ∀ k : ℕ, (hk : k ≤ CParam f) →
    ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => CParam f - k ≤ j.val), blockSize f j ≤
      if h : 0 < k then 2 * blockSize f ⟨CParam f - k, by omega⟩ else 0
  | 0, _ => by
      have hemp : (Finset.univ.filter fun j : Fin (CParam f) => CParam f - 0 ≤ j.val) = ∅ := by
        ext j; simp [j.isLt]
      rw [hemp]
      simp
  | k + 1, hk => by
      simp only [Nat.zero_lt_succ, ↓reduceDIte]
      let a : Fin (CParam f) := ⟨CParam f - (k + 1), by omega⟩
      have hsplit : (Finset.univ.filter fun j : Fin (CParam f) => CParam f - (k + 1) ≤ j.val) =
          insert a (Finset.univ.filter fun j : Fin (CParam f) => CParam f - k ≤ j.val) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, a]
        omega
      have hnot : a ∉ Finset.univ.filter (fun j : Fin (CParam f) => CParam f - k ≤ j.val) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
        omega
      rw [hsplit, Finset.sum_insert hnot]
      have ih := tail_sum_blockSize_aux k (by omega)
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hkpos
      · simp only [lt_self_iff_false, ↓reduceDIte] at ih
        change blockSize f a + _ ≤ 2 * blockSize f a
        omega
      · simp only [hkpos, ↓reduceDIte] at ih
        let b : Fin (CParam f) := ⟨CParam f - k, by omega⟩
        have hab : a < b := Fin.mk_lt_mk.mpr (by omega)
        have hstep := blockSize_step f hab
        have hD : 2 ≤ (DParam f) ^ 2 := by have := DParam_ge_C_add_two f; nlinarith
        have h2b : 2 * blockSize f b ≤ blockSize f a :=
          (Nat.mul_le_mul_right _ hD).trans hstep
        change blockSize f a + _ ≤ 2 * blockSize f a
        change _ ≤ 2 * blockSize f b at ih
        omega

lemma tail_sum_blockSize (i : Fin (CParam f)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => i ≤ j), blockSize f j ≤
      2 * blockSize f i := by
  have h := tail_sum_blockSize_aux f (CParam f - i.val) (by omega)
  have hpos : 0 < CParam f - i.val := by omega
  simp only [hpos, ↓reduceDIte] at h
  have hfilt : (Finset.univ.filter fun j : Fin (CParam f) => i ≤ j) =
      Finset.univ.filter (fun j : Fin (CParam f) => CParam f - (CParam f - i.val) ≤ j.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  rw [hfilt]
  exact h.trans_eq (by congr 2; ext; simp; omega)

lemma total_sum_blockSize :
    ∑ j : Fin (CParam f), blockSize f j ≤
      2 * blockSize f ⟨0, by have := CParam_ge_64 f; omega⟩ := by
  let i0 : Fin (CParam f) := ⟨0, by have := CParam_ge_64 f; omega⟩
  have h := tail_sum_blockSize f i0
  have huniv : (Finset.univ.filter fun j : Fin (CParam f) => i0 ≤ j) = Finset.univ := by
    ext j; simp [i0]
  rwa [huniv] at h

abbrev BaseVert : Type := Σ i : Fin (CParam f), Fin (blockSize f i)

abbrev Coord : Type :=
  Σ i : Fin (CParam f), Σ _j : { j : Fin (CParam f) // i < j }, Fin (blockSize f i)

abbrev Space : Type := ∀ p : Coord f, Fin (blockSize f p.2.1.val)

lemma space_card_pos : 0 < Fintype.card (Space f) := by
  rw [Fintype.card_pi]
  exact Finset.prod_pos fun p _ => by
    rw [Fintype.card_fin]
    exact blockSize_pos f p.2.1.val

def baseArc (ω : Space f) (u v : BaseVert f) : Prop :=
  ∃ h : u.1 < v.1, ω ⟨u.1, ⟨v.1, h⟩, u.2⟩ = v.2

def baseGraph (ω : Space f) : SimpleGraph (BaseVert f) where
  Adj u v := baseArc f ω u v ∨ baseArc f ω v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact lt_irrefl _ hlt⟩

/- ### Subsection 2.1: Heavy independent sets (`Bad1`) -/

def partCard (S : Finset (BaseVert f)) (j : Fin (CParam f)) : ℕ :=
  (Finset.univ.filter fun x : Fin (blockSize f j) => (⟨j, x⟩ : BaseVert f) ∈ S).card

noncomputable def setWeight (S : Finset (BaseVert f)) : ℝ :=
  ∑ j : Fin (CParam f), (partCard f S j : ℝ) / (blockSize f j : ℝ)

def IsIndepFinset (ω : Space f) (S : Finset (BaseVert f)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ (baseGraph f ω).Adj u v

def tailVerts (i0 : Fin (CParam f)) : Finset (BaseVert f) :=
  Finset.univ.filter fun v : BaseVert f => i0 ≤ v.1

lemma card_tailVerts_le (i0 : Fin (CParam f)) :
    (tailVerts f i0).card ≤ 2 * blockSize f i0 := by
  have hcard : (tailVerts f i0).card =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => i0 ≤ j), blockSize f j := by
    have heq : tailVerts f i0 =
        (Finset.univ.filter fun j : Fin (CParam f) => i0 ≤ j).sigma
          (fun j => (Finset.univ : Finset (Fin (blockSize f j)))) := by
      ext ⟨j, x⟩
      simp [tailVerts]
    rw [heq, Finset.card_sigma]
    simp
  rw [hcard]
  exact tail_sum_blockSize f i0

def GoodTailSet (i0 : Fin (CParam f)) (T : Finset (BaseVert f)) : Prop :=
  T ⊆ tailVerts f i0 ∧
    blockSize f i0 ≤ 2 * qParam f * partCard f T i0 ∧
    8 * (qParam f : ℝ) ≤ setWeight f T

def Bad1 (ω : Space f) : Prop :=
  ∃ S : Finset (BaseVert f), IsIndepFinset f ω S ∧ 16 * (qParam f : ℝ) ≤ setWeight f S

lemma bad1_implies_goodTail {ω : Space f} (hbad : Bad1 f ω) :
    ∃ i0 : Fin (CParam f), ∃ T ∈ (tailVerts f i0).powerset,
      GoodTailSet f i0 T ∧ IsIndepFinset f ω T := by
  classical
  rcases hbad with ⟨S, hind, hw⟩
  let heavy : Finset (Fin (CParam f)) :=
    Finset.univ.filter fun j : Fin (CParam f) => blockSize f j ≤ 2 * qParam f * partCard f S j
  have hlight_sum : ∑ j ∈ Finset.univ \ heavy,
      (partCard f S j : ℝ) / (blockSize f j : ℝ) ≤ 8 * (qParam f : ℝ) := by
    have hqpos : (0 : ℝ) < 2 * (qParam f : ℝ) := by
      have := qParam_ge_two f; positivity
    have hterm : ∀ j ∈ Finset.univ \ heavy,
        (partCard f S j : ℝ) / (blockSize f j : ℝ) ≤ 1 / (2 * (qParam f : ℝ)) := by
      intro j hj
      have hnot : ¬ blockSize f j ≤ 2 * qParam f * partCard f S j :=
        (Finset.mem_sdiff.mp hj).2 ∘ (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
      have hlt : (2 * (qParam f : ℝ)) * (partCard f S j : ℝ) ≤ (blockSize f j : ℝ) := by
        exact_mod_cast le_of_lt (lt_of_not_ge hnot)
      have hbpos : (0 : ℝ) < (blockSize f j : ℝ) := Nat.cast_pos.mpr (blockSize_pos f j)
      rw [div_le_div_iff₀ hbpos hqpos]
      linarith
    calc
      ∑ j ∈ Finset.univ \ heavy, (partCard f S j : ℝ) / (blockSize f j : ℝ)
          ≤ ∑ _j ∈ Finset.univ \ heavy, (1 / (2 * (qParam f : ℝ))) := Finset.sum_le_sum hterm
      _ = ((Finset.univ \ heavy).card : ℝ) * (1 / (2 * (qParam f : ℝ))) := by simp
      _ ≤ (CParam f : ℝ) * (1 / (2 * (qParam f : ℝ))) := by
          gcongr
          exact_mod_cast (Finset.card_le_univ (Finset.univ \ heavy)).trans_eq (Fintype.card_fin _)
      _ = 8 * (qParam f : ℝ) := by
          have hq0 : (qParam f : ℝ) ≠ 0 := by have := qParam_ge_two f; positivity
          push_cast [CParam]
          field_simp
          ring
  have hsplit : setWeight f S =
      ∑ j ∈ heavy, (partCard f S j : ℝ) / (blockSize f j : ℝ) +
      ∑ j ∈ Finset.univ \ heavy, (partCard f S j : ℝ) / (blockSize f j : ℝ) := by
    dsimp [setWeight]
    exact (Finset.sum_sdiff (Finset.subset_univ heavy)).symm.trans (add_comm _ _)
  have hheavy_ge : 8 * (qParam f : ℝ) ≤
      ∑ j ∈ heavy, (partCard f S j : ℝ) / (blockSize f j : ℝ) := by
    linarith
  have hheavy_ne : heavy.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hheavy_ge
    have := qParam_ge_two f
    linarith [show (2 : ℝ) ≤ (qParam f : ℝ) by exact_mod_cast this]
  let i0 : Fin (CParam f) := heavy.min' hheavy_ne
  let T : Finset (BaseVert f) := S.filter fun v => v.1 ∈ heavy
  have hT_sub_S : T ⊆ S := Finset.filter_subset _ _
  have hT_tail : T ⊆ tailVerts f i0 := by
    intro v hv
    rw [Finset.mem_filter] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, Finset.min'_le heavy v.1 hv.2⟩
  have hpart_eq : ∀ j : Fin (CParam f),
      partCard f T j = if j ∈ heavy then partCard f S j else 0 := by
    intro j
    by_cases hj : j ∈ heavy
    · simp only [hj, ↓reduceIte, partCard]
      congr 1
      ext x
      simp [T, hj]
    · simp only [hj, ↓reduceIte, partCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      simp [T, hj]
  have hwT : setWeight f T = ∑ j ∈ heavy, (partCard f S j : ℝ) / (blockSize f j : ℝ) := by
    dsimp [setWeight]
    rw [← Finset.sum_subset (Finset.subset_univ heavy)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [hpart_eq j, if_pos hj]
    · intro j _ hj
      rw [hpart_eq j, if_neg hj]
      simp
  have hi0_mem : i0 ∈ heavy := Finset.min'_mem heavy hheavy_ne
  have hi0_heavy : blockSize f i0 ≤ 2 * qParam f * partCard f T i0 := by
    rw [hpart_eq i0, if_pos hi0_mem]
    exact (Finset.mem_filter.mp hi0_mem).2
  refine ⟨i0, T, Finset.mem_powerset.mpr hT_tail, ⟨hT_tail, hi0_heavy, ?_⟩, ?_⟩
  · linarith
  · intro u hu v hv
    exact hind u (hT_sub_S hu) v (hT_sub_S hv)

lemma count_indep_goodTail_le (i0 : Fin (CParam f)) (T : Finset (BaseVert f))
    (hgood : GoodTailSet f i0 T) :
    ((Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T).card : ℝ) ≤
      (Fintype.card (Space f) : ℝ) * ((1 / 8 : ℝ) ^ blockSize f i0) := by
  classical
  let allowed : ∀ p : Coord f, Finset (Fin (blockSize f p.2.1.val)) := fun p =>
    if p.1 = i0 ∧ (⟨p.1, p.2.2⟩ : BaseVert f) ∈ T then
      Finset.univ.filter fun y : Fin (blockSize f p.2.1.val) =>
        (⟨p.2.1.val, y⟩ : BaseVert f) ∉ T
    else
      Finset.univ
  have hsub : (Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T) ⊆
      Fintype.piFinset allowed := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [Fintype.mem_piFinset]
    intro p
    dsimp only [allowed]
    split_ifs with hp
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hmem => ?_⟩
      have hadj : (baseGraph f ω).Adj ⟨p.1, p.2.2⟩ ⟨p.2.1.val, ω p⟩ :=
        Or.inl ⟨p.2.1.2, rfl⟩
      exact hω.2 ⟨p.1, p.2.2⟩ hp.2 ⟨p.2.1.val, ω p⟩ hmem hadj
    · exact Finset.mem_univ _
  have hcard_le : (Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T).card ≤
      ∏ p : Coord f, (allowed p).card :=
    (Finset.card_le_card hsub).trans_eq (Fintype.card_piFinset allowed)
  let expTerm : Coord f → ℝ := fun p =>
    if p.1 = i0 ∧ (⟨p.1, p.2.2⟩ : BaseVert f) ∈ T then
      - ((partCard f T p.2.1.val : ℝ) / (blockSize f p.2.1.val : ℝ))
    else
      0
  have hpt : ∀ p : Coord f,
      ((allowed p).card : ℝ) ≤ (blockSize f p.2.1.val : ℝ) * Real.exp (expTerm p) := by
    intro p
    dsimp only [allowed, expTerm]
    split_ifs with hp
    · let j := p.2.1.val
      have hcompl : (Finset.univ.filter fun y : Fin (blockSize f j) =>
          (⟨j, y⟩ : BaseVert f) ∉ T).card + partCard f T j = blockSize f j := by
        have hcard := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (blockSize f j))))
          (p := fun y => (⟨j, y⟩ : BaseVert f) ∈ T)
        rw [Finset.card_univ, Fintype.card_fin] at hcard
        dsimp [partCard]
        omega
      have hsub_real : ((Finset.univ.filter fun y : Fin (blockSize f j) =>
          (⟨j, y⟩ : BaseVert f) ∉ T).card : ℝ) =
          (blockSize f j : ℝ) - (partCard f T j : ℝ) := by
        have hnat : ((Finset.univ.filter fun y : Fin (blockSize f j) =>
            (⟨j, y⟩ : BaseVert f) ∉ T).card : ℝ) + (partCard f T j : ℝ) =
            (blockSize f j : ℝ) := by exact_mod_cast hcompl
        linarith
      rw [hsub_real]
      have hbpos : (0 : ℝ) < (blockSize f j : ℝ) := Nat.cast_pos.mpr (blockSize_pos f j)
      have hexp := Real.add_one_le_exp (- ((partCard f T j : ℝ) / (blockSize f j : ℝ)))
      have hid : (blockSize f j : ℝ) - (partCard f T j : ℝ) =
          (blockSize f j : ℝ) * (- ((partCard f T j : ℝ) / (blockSize f j : ℝ)) + 1) := by
        field_simp
        ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left hexp hbpos.le
    · simp
  have hprod : ((Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T).card : ℝ) ≤
      (Fintype.card (Space f) : ℝ) * Real.exp (∑ p : Coord f, expTerm p) := by
    have h1 : ((Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T).card : ℝ) ≤
        ∏ p : Coord f, ((allowed p).card : ℝ) := by exact_mod_cast hcard_le
    have h2 : ∏ p : Coord f, ((allowed p).card : ℝ) ≤
        ∏ p : Coord f, ((blockSize f p.2.1.val : ℝ) * Real.exp (expTerm p)) :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun p _ => hpt p)
    rw [Finset.prod_mul_distrib, ← Real.exp_sum] at h2
    have hspace : (∏ p : Coord f, (blockSize f p.2.1.val : ℝ)) =
        (Fintype.card (Space f) : ℝ) := by
      rw [Fintype.card_pi]
      simp
    rw [hspace] at h2
    exact h1.trans h2
  have hsum_exp : ∑ p : Coord f, expTerm p =
      - ((partCard f T i0 : ℝ) *
          ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => i0 < j),
            (partCard f T j : ℝ) / (blockSize f j : ℝ)) := by
    rw [Fintype.sum_sigma, Fintype.sum_eq_single i0]
    · rw [Fintype.sum_sigma]
      have hinner : ∀ j : { j : Fin (CParam f) // i0 < j },
          ∑ x : Fin (blockSize f i0), expTerm ⟨i0, j, x⟩ =
            - ((partCard f T i0 : ℝ) *
                ((partCard f T j.1 : ℝ) / (blockSize f j.1 : ℝ))) := by
        intro j
        have hrew : ∑ x : Fin (blockSize f i0), expTerm ⟨i0, j, x⟩ =
            ∑ x ∈ Finset.univ.filter (fun x : Fin (blockSize f i0) =>
              (⟨i0, x⟩ : BaseVert f) ∈ T),
              (- ((partCard f T j.1 : ℝ) / (blockSize f j.1 : ℝ))) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hmem : (⟨i0, x⟩ : BaseVert f) ∈ T <;> simp [expTerm, hmem]
        rw [hrew, Finset.sum_const, nsmul_eq_mul]
        dsimp [partCard]
        ring
      simp_rw [hinner]
      have hsub_sum : ∑ j : { j : Fin (CParam f) // i0 < j },
          - ((partCard f T i0 : ℝ) * ((partCard f T j.1 : ℝ) / (blockSize f j.1 : ℝ))) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => i0 < j),
            - ((partCard f T i0 : ℝ) * ((partCard f T j : ℝ) / (blockSize f j : ℝ))) := by
        exact (Finset.sum_subtype
          (Finset.univ.filter fun j : Fin (CParam f) => i0 < j)
          (fun _ => by simp)
          (fun j => - ((partCard f T i0 : ℝ) * ((partCard f T j : ℝ) / (blockSize f j : ℝ))))).symm
      rw [hsub_sum, Finset.sum_neg_distrib, ← Finset.mul_sum]
    · intro i hi
      rw [Fintype.sum_sigma]
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x _ => ?_
      dsimp [expTerm]
      rw [if_neg (fun h => hi h.1)]
  obtain ⟨hT_tail, hi0_heavy, hwT⟩ := hgood
  have hpart_lt_zero : ∀ j : Fin (CParam f), j < i0 → partCard f T j = 0 := by
    intro j hj
    dsimp [partCard]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hxT
    have := (Finset.mem_filter.mp (hT_tail hxT)).2
    exact not_le_of_gt hj this
  have hwT_split : setWeight f T =
      (partCard f T i0 : ℝ) / (blockSize f i0 : ℝ) +
        ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => i0 < j),
          (partCard f T j : ℝ) / (blockSize f j : ℝ) := by
    dsimp [setWeight]
    have huniv : (Finset.univ : Finset (Fin (CParam f))) =
        insert i0 ((Finset.univ.filter fun j : Fin (CParam f) => j < i0) ∪
          (Finset.univ.filter fun j : Fin (CParam f) => i0 < j)) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
        true_and, true_iff]
      rcases lt_trichotomy j i0 with h | heq | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl heq
      · exact Or.inr (Or.inr h)
    have hnot : i0 ∉ (Finset.univ.filter fun j : Fin (CParam f) => j < i0) ∪
        (Finset.univ.filter fun j : Fin (CParam f) => i0 < j) := by
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl,
        or_self, not_false_eq_true]
    have hdisj : Disjoint (Finset.univ.filter fun j : Fin (CParam f) => j < i0)
        (Finset.univ.filter fun j : Fin (CParam f) => i0 < j) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact lt_asymm h1 h2
    conv_lhs => rw [huniv]
    rw [Finset.sum_insert hnot, Finset.sum_union hdisj]
    have hzero : ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => j < i0),
        (partCard f T j : ℝ) / (blockSize f j : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hpart_lt_zero j (Finset.mem_filter.mp hj).2]
      simp
    rw [hzero, zero_add]
  let w0 : ℝ := (partCard f T i0 : ℝ) / (blockSize f i0 : ℝ)
  have hb0_pos : (0 : ℝ) < (blockSize f i0 : ℝ) := Nat.cast_pos.mpr (blockSize_pos f i0)
  have hw0_le_one : w0 ≤ 1 := by
    dsimp [w0]
    rw [div_le_one hb0_pos]
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)
  have hw0_nonneg : 0 ≤ w0 := by dsimp [w0]; positivity
  have h2qw0 : 1 ≤ 2 * (qParam f : ℝ) * w0 := by
    dsimp [w0]
    rw [le_div_iff₀ hb0_pos] at *
    have hcast : (blockSize f i0 : ℝ) ≤ 2 * (qParam f : ℝ) * (partCard f T i0 : ℝ) := by
      exact_mod_cast hi0_heavy
    have : (blockSize f i0 : ℝ) ≤ (2 * (qParam f : ℝ) * (partCard f T i0 : ℝ)) := hcast
    calc
      (1 : ℝ) = (blockSize f i0 : ℝ) / (blockSize f i0 : ℝ) := (div_self hb0_pos.ne').symm
      _ ≤ (2 * (qParam f : ℝ) * (partCard f T i0 : ℝ)) / (blockSize f i0 : ℝ) :=
          div_le_div_of_nonneg_right this hb0_pos.le
      _ = 2 * (qParam f : ℝ) * ((partCard f T i0 : ℝ) / (blockSize f i0 : ℝ)) := by ring
  have hw0_prod : 4 ≤ w0 * setWeight f T := by
    have hqpos : (0 : ℝ) < (qParam f : ℝ) := by have := qParam_ge_two f; positivity
    have hmul : 8 * (qParam f : ℝ) ≤ (2 * (qParam f : ℝ) * w0) * setWeight f T := by
      nlinarith
    nlinarith
  have hexp_le : ∑ p : Coord f, expTerm p ≤ - (3 * (blockSize f i0 : ℝ)) := by
    rw [hsum_exp]
    have htail_w : ∑ j ∈ Finset.univ.filter (fun j : Fin (CParam f) => i0 < j),
        (partCard f T j : ℝ) / (blockSize f j : ℝ) = setWeight f T - w0 := by
      dsimp [w0] at hwT_split ⊢
      linarith
    rw [htail_w]
    have hs0 : (partCard f T i0 : ℝ) = w0 * (blockSize f i0 : ℝ) := by
      dsimp [w0]; field_simp
    rw [hs0]
    have h3 : 3 ≤ w0 * (setWeight f T - w0) := by nlinarith
    nlinarith
  have hexp_bound : Real.exp (∑ p : Coord f, expTerm p) ≤ (1 / 8 : ℝ) ^ blockSize f i0 := by
    have h1 : Real.exp (∑ p : Coord f, expTerm p) ≤ Real.exp (↑(blockSize f i0) * (-3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    rw [Real.exp_nat_mul] at h1
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have he3 : (8 : ℝ) ≤ Real.exp 3 := by
      have hpow : (2 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by positivity) he1 3
      have hmul := Real.exp_nat_mul 1 3
      norm_num at hpow hmul
      linarith
    have hem3 : Real.exp (-3) ≤ (1 / 8 : ℝ) := by
      rw [Real.exp_neg]
      have hexp3_pos : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
      rw [inv_eq_one_div, div_le_div_iff₀ hexp3_pos (by norm_num)]
      linarith
    exact h1.trans (pow_le_pow_left₀ (Real.exp_pos _).le hem3 _)
  exact hprod.trans (mul_le_mul_of_nonneg_left hexp_bound (by positivity))

lemma two_mul_card_bad1_lt :
    2 * (Finset.univ.filter (fun ω : Space f => Bad1 f ω)).card < Fintype.card (Space f) := by
  classical
  let badFin := Finset.univ.filter (fun ω : Space f => Bad1 f ω)
  let goodSets : Fin (CParam f) → Finset (Finset (BaseVert f)) := fun i0 =>
    (tailVerts f i0).powerset.filter (fun T => GoodTailSet f i0 T)
  have hcov : badFin ⊆ Finset.univ.biUnion (fun i0 : Fin (CParam f) =>
      (goodSets i0).biUnion (fun T => Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨i0, T, hTpow, hgood, hind⟩ := bad1_implies_goodTail f hω.2
    exact Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨T, Finset.mem_filter.mpr ⟨hTpow, hgood⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hind⟩⟩⟩
  have hcard_nat : badFin.card ≤ ∑ i0 : Fin (CParam f),
      ∑ T ∈ goodSets i0, (Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T).card := by
    refine (Finset.card_le_card hcov).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    exact Finset.sum_le_sum fun i0 _ => Finset.card_biUnion_le
  have hcard_real : (badFin.card : ℝ) ≤
      (Fintype.card (Space f) : ℝ) *
        ((CParam f : ℝ) * ((1 / 2 : ℝ) ^ (CParam f + 2))) := by
    calc
      (badFin.card : ℝ)
          ≤ ∑ i0 : Fin (CParam f),
              ∑ T ∈ goodSets i0,
                ((Finset.univ.filter fun ω : Space f => IsIndepFinset f ω T).card : ℝ) := by
            exact_mod_cast hcard_nat
      _ ≤ ∑ i0 : Fin (CParam f),
            ∑ _T ∈ goodSets i0,
              ((Fintype.card (Space f) : ℝ) * ((1 / 8 : ℝ) ^ blockSize f i0)) := by
          refine Finset.sum_le_sum fun i0 _ => Finset.sum_le_sum fun T hT => ?_
          exact count_indep_goodTail_le f i0 T (Finset.mem_filter.mp hT).2
      _ = ∑ i0 : Fin (CParam f),
            ((goodSets i0).card : ℝ) *
              ((Fintype.card (Space f) : ℝ) * ((1 / 8 : ℝ) ^ blockSize f i0)) := by
          simp
      _ ≤ ∑ i0 : Fin (CParam f),
            (Fintype.card (Space f) : ℝ) * ((1 / 2 : ℝ) ^ (CParam f + 2)) := by
          refine Finset.sum_le_sum fun i0 _ => ?_
          have hgs : (goodSets i0).card ≤ 2 ^ (2 * blockSize f i0) := by
            calc
              (goodSets i0).card ≤ (tailVerts f i0).powerset.card := Finset.card_filter_le _ _
              _ = 2 ^ (tailVerts f i0).card := Finset.card_powerset _
              _ ≤ 2 ^ (2 * blockSize f i0) :=
                  Nat.pow_le_pow_right (by norm_num) (card_tailVerts_le f i0)
          have hgs_real : ((goodSets i0).card : ℝ) ≤ (4 : ℝ) ^ blockSize f i0 := by
            have h1 : ((goodSets i0).card : ℝ) ≤ ((2 ^ (2 * blockSize f i0) : ℕ) : ℝ) :=
              Nat.cast_le.mpr hgs
            have h2 : ((2 ^ (2 * blockSize f i0) : ℕ) : ℝ) = (4 : ℝ) ^ blockSize f i0 := by
              push_cast
              rw [pow_mul]
              norm_num
            exact h1.trans_eq h2
          have hprod_i0 : ((goodSets i0).card : ℝ) * ((1 / 8 : ℝ) ^ blockSize f i0) ≤
              (1 / 2 : ℝ) ^ (CParam f + 2) := by
            calc
              ((goodSets i0).card : ℝ) * ((1 / 8 : ℝ) ^ blockSize f i0)
                  ≤ (4 : ℝ) ^ blockSize f i0 * ((1 / 8 : ℝ) ^ blockSize f i0) :=
                    mul_le_mul_of_nonneg_right hgs_real (by positivity)
              _ = (1 / 2 : ℝ) ^ blockSize f i0 := by
                  rw [← mul_pow]
                  norm_num
              _ ≤ (1 / 2 : ℝ) ^ (CParam f + 2) :=
                  pow_le_pow_of_le_one (by norm_num) (by norm_num) (blockSize_ge_C_add_two f i0)
          calc
            ((goodSets i0).card : ℝ) *
                ((Fintype.card (Space f) : ℝ) * ((1 / 8 : ℝ) ^ blockSize f i0))
                = (Fintype.card (Space f) : ℝ) *
                    (((goodSets i0).card : ℝ) * ((1 / 8 : ℝ) ^ blockSize f i0)) := by ring
            _ ≤ (Fintype.card (Space f) : ℝ) * ((1 / 2 : ℝ) ^ (CParam f + 2)) :=
                mul_le_mul_of_nonneg_left hprod_i0 (by positivity)
      _ = (Fintype.card (Space f) : ℝ) *
            ((CParam f : ℝ) * ((1 / 2 : ℝ) ^ (CParam f + 2))) := by
          simp [Fintype.card_fin]; ring
  have hratio : (CParam f : ℝ) * ((1 / 2 : ℝ) ^ (CParam f + 2)) < 1 / 2 := by
    have hlt_nat : CParam f < 2 ^ (CParam f + 1) := nat_lt_two_pow_succ (CParam f)
    have hlt_real : (CParam f : ℝ) < (2 : ℝ) ^ (CParam f + 1) := by exact_mod_cast hlt_nat
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (CParam f + 2) := by positivity
    have hid : ((1 / 2 : ℝ) ^ (CParam f + 2)) = 1 / ((2 : ℝ) ^ (CParam f + 2)) := by
      rw [one_div_pow]
    rw [hid, mul_one_div, div_lt_div_iff₀ hpow_pos (by norm_num)]
    rw [pow_succ']
    linarith
  have hsp_pos : (0 : ℝ) < (Fintype.card (Space f) : ℝ) := Nat.cast_pos.mpr (space_card_pos f)
  have hlt_final : 2 * (badFin.card : ℝ) < (Fintype.card (Space f) : ℝ) := by
    nlinarith
  exact_mod_cast hlt_final

/- ### Subsection 2.2: Left-segment sparsity (`Bad2`) -/

def leftVerts (i : Fin (CParam f)) : Finset (BaseVert f) :=
  Finset.univ.filter fun v : BaseVert f => v.1 < i

lemma card_leftVerts_le (i : Fin (CParam f)) :
    (leftVerts f i).card ≤
      2 * blockSize f ⟨0, by have := CParam_ge_64 f; omega⟩ := by
  have hle : (leftVerts f i).card ≤ Fintype.card (BaseVert f) := Finset.card_le_univ _
  have htot : Fintype.card (BaseVert f) = ∑ j : Fin (CParam f), blockSize f j := by
    simp [BaseVert, Fintype.card_sigma]
  exact (hle.trans_eq htot).trans (total_sum_blockSize f)

def dirPairs (X : Finset (BaseVert f)) : Finset (BaseVert f × BaseVert f) :=
  (X ×ˢ X).filter fun e => e.1.1 < e.2.1

lemma card_dirPairs_le (X : Finset (BaseVert f)) :
    (dirPairs f X).card ≤ X.card * (X.card - 1) / 2 := by
  classical
  let toPair : BaseVert f × BaseVert f → Finset (BaseVert f) := fun e => {e.1, e.2}
  have hinj : Set.InjOn toPair (dirPairs f X : Set (BaseVert f × BaseVert f)) := by
    intro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
    simp only [Finset.mem_coe, dirPairs, Finset.mem_filter] at h₁ h₂
    change ({u₁, v₁} : Finset (BaseVert f)) = {u₂, v₂} at heq
    have hmem₁ : u₁ ∈ ({u₂, v₂} : Finset (BaseVert f)) := by
      rw [← heq]
      exact Finset.mem_insert_self u₁ {v₁}
    have hmem₂ : v₁ ∈ ({u₂, v₂} : Finset (BaseVert f)) := by
      rw [← heq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v₁)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₁ hmem₂
    rcases hmem₁ with rfl | rfl <;> rcases hmem₂ with rfl | rfl
    · exact absurd h₁.2 (lt_irrefl _)
    · rfl
    · exact absurd (h₁.2.trans h₂.2) (lt_irrefl _)
    · exact absurd h₁.2 (lt_irrefl _)
  have hsub : (dirPairs f X).image toPair ⊆ X.powersetCard 2 := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨⟨u, v⟩, huv, rfl⟩
    simp only [dirPairs, Finset.mem_filter, Finset.mem_product] at huv
    have hne : u ≠ v := fun h => lt_irrefl _ (h ▸ huv.2)
    refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hne⟩
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact huv.1
  calc
    (dirPairs f X).card = ((dirPairs f X).image toPair).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (X.powersetCard 2).card := Finset.card_le_card hsub
    _ = X.card.choose 2 := Finset.card_powersetCard 2 X
    _ = X.card * (X.card - 1) / 2 := Nat.choose_two_right X.card

noncomputable def dirEdges (ω : Space f) (X : Finset (BaseVert f)) :
    Finset (BaseVert f × BaseVert f) :=
  (dirPairs f X).filter fun e => baseArc f ω e.1 e.2

def Bad2 (ω : Space f) : Prop :=
  ∃ (i : Fin (CParam f)) (_ : 1 ≤ i.val) (X : Finset (BaseVert f)),
    X ⊆ leftVerts f i ∧ 4 ≤ X.card ∧ X.card ≤ 4 * deltaParam f * blockSize f i ∧
      (3 * X.card + 1) / 2 ≤ (dirEdges f ω X).card

lemma count_pairSet_le {i : Fin (CParam f)} (hi : 1 ≤ i.val) {X : Finset (BaseVert f)}
    (hX : X ⊆ leftVerts f i) {m : ℕ} {P : Finset (BaseVert f × BaseVert f)}
    (hP : P ∈ (dirPairs f X).powersetCard m) :
    (Finset.univ.filter fun ω : Space f => ∀ e ∈ P, baseArc f ω e.1 e.2).card *
      (blockSize f ⟨i.val - 1, by omega⟩) ^ m ≤ Fintype.card (Space f) := by
  classical
  obtain ⟨hPsub, hPcard⟩ := Finset.mem_powersetCard.mp hP
  let target : Finset (Space f) :=
    Finset.univ.filter fun ω : Space f => ∀ e ∈ P, baseArc f ω e.1 e.2
  by_cases hcoll : ∃ e₁ ∈ P, ∃ e₂ ∈ P, e₁ ≠ e₂ ∧ e₁.1 = e₂.1 ∧ e₁.2.1 = e₂.2.1
  · have hemp : target = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      rw [Finset.mem_filter] at hω
      rcases hcoll with ⟨e₁, he₁, e₂, he₂, hne, hu, hv1⟩
      obtain ⟨hlt₁, heq₁⟩ := hω.2 e₁ he₁
      obtain ⟨hlt₂, heq₂⟩ := hω.2 e₂ he₂
      have hc_eq : (⟨e₁.1.1, ⟨e₁.2.1, hlt₁⟩, e₁.1.2⟩ : Coord f) =
          ⟨e₂.1.1, ⟨e₂.2.1, hlt₂⟩, e₂.1.2⟩ := by
        rcases e₁ with ⟨⟨a₁, x₁⟩, ⟨b₁, y₁⟩⟩
        rcases e₂ with ⟨⟨a₂, x₂⟩, ⟨b₂, y₂⟩⟩
        dsimp only at hu hv1
        have ha : a₁ = a₂ := congrArg Sigma.fst hu
        subst ha
        subst hv1
        have hx : x₁ = x₂ := eq_of_heq (Sigma.mk.inj_iff.mp hu).2
        subst hx
        rfl
      have hv_eq : e₁.2 = e₂.2 := by
        calc
          e₁.2 = (⟨e₁.2.1, ω ⟨e₁.1.1, ⟨e₁.2.1, hlt₁⟩, e₁.1.2⟩⟩ : BaseVert f) := by
            rw [heq₁]
          _ = ⟨e₂.2.1, ω ⟨e₂.1.1, ⟨e₂.2.1, hlt₂⟩, e₂.1.2⟩⟩ :=
            congrArg (fun q : Coord f => (⟨q.2.1.val, ω q⟩ : BaseVert f)) hc_eq
          _ = e₂.2 := by rw [heq₂]
      exact hne (Prod.ext hu hv_eq)
    change target.card * _ ≤ _
    rw [hemp, Finset.card_empty, zero_mul]
    exact Nat.zero_le _
  · push Not at hcoll
    let coordOf : { e // e ∈ P } → Coord f := fun e =>
      ⟨e.1.1.1, ⟨e.1.2.1, (Finset.mem_filter.mp (hPsub e.2)).2⟩, e.1.1.2⟩
    have hcoord_inj : Function.Injective coordOf := by
      intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hc
      apply Subtype.ext
      by_contra hne
      have hfst1 : e₁.1 = e₂.1 ∧ e₁.2.1 = e₂.2.1 := by
        rcases e₁ with ⟨⟨a₁, x₁⟩, ⟨b₁, y₁⟩⟩
        rcases e₂ with ⟨⟨a₂, x₂⟩, ⟨b₂, y₂⟩⟩
        dsimp only [coordOf] at hc ⊢
        have ha : a₁ = a₂ := congrArg Sigma.fst hc
        subst ha
        have h2 : (⟨⟨b₁, _⟩, x₁⟩ : Σ _j : { j : Fin (CParam f) // a₁ < j }, Fin (blockSize f a₁)) =
            ⟨⟨b₂, _⟩, x₂⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hc).2
        have hb : b₁ = b₂ := congrArg (fun s => s.1.1) h2
        subst hb
        have hx : x₁ = x₂ := eq_of_heq (Sigma.mk.inj_iff.mp h2).2
        subst hx
        exact ⟨rfl, rfl⟩
      exact hcoll e₁ he₁ e₂ he₂ hne hfst1.1 hfst1.2
    let Pcoords : Finset (Coord f) := P.attach.image coordOf
    have hPcoords_card : Pcoords.card = m := by
      rw [Finset.card_image_of_injective _ hcoord_inj, Finset.card_attach, hPcard]
    let allowed : ∀ p : Coord f, Finset (Fin (blockSize f p.2.1.val)) := fun p =>
      Finset.univ.filter fun y : Fin (blockSize f p.2.1.val) =>
        ∀ e ∈ P, e.1 = ⟨p.1, p.2.2⟩ → e.2.1 = p.2.1.val →
          (⟨p.2.1.val, y⟩ : BaseVert f) = e.2
    have hsub : target ⊆ Fintype.piFinset allowed := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      rw [Fintype.mem_piFinset]
      intro p
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he hu hv1 => ?_⟩
      obtain ⟨hlt, heq⟩ := hω.2 e he
      have hc_eq : (⟨e.1.1, ⟨e.2.1, hlt⟩, e.1.2⟩ : Coord f) = p := by
        rcases p with ⟨a, ⟨b, hab⟩, x⟩
        rcases e with ⟨⟨a', x'⟩, ⟨b', y'⟩⟩
        dsimp only at hu hv1
        have ha' : a' = a := congrArg Sigma.fst hu
        subst ha'
        subst hv1
        have hx' : x' = x := eq_of_heq (Sigma.mk.inj_iff.mp hu).2
        subst hx'
        rfl
      calc
        (⟨p.2.1.val, ω p⟩ : BaseVert f)
            = ⟨e.2.1, ω ⟨e.1.1, ⟨e.2.1, hlt⟩, e.1.2⟩⟩ := by
                exact congrArg (fun q : Coord f => (⟨q.2.1.val, ω q⟩ : BaseVert f)) hc_eq.symm
        _ = e.2 := by rw [heq]
    have hcard_target : target.card ≤ ∏ p : Coord f, (allowed p).card :=
      (Finset.card_le_card hsub).trans_eq (Fintype.card_piFinset allowed)
    have hall_le_one : ∀ p ∈ Pcoords, (allowed p).card ≤ 1 := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨⟨e₀, he₀⟩, _, rfl⟩
      rw [Finset.card_le_one_iff]
      intro y₁ y₂ hy₁ hy₂
      have h₁ := (Finset.mem_filter.mp hy₁).2 e₀ he₀ rfl rfl
      have h₂ := (Finset.mem_filter.mp hy₂).2 e₀ he₀ rfl rfl
      exact eq_of_heq (Sigma.mk.inj_iff.mp (h₁.trans h₂.symm)).2
    have hall_le_block : ∀ p : Coord f, (allowed p).card ≤ blockSize f p.2.1.val := fun p =>
      (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)
    have hp_prev_le : ∀ p ∈ Pcoords,
        blockSize f ⟨i.val - 1, by omega⟩ ≤ blockSize f p.2.1.val := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨⟨e₀, he₀⟩, _, rfl⟩
      have he₀_prod := (Finset.mem_product.mp (Finset.mem_filter.mp (hPsub he₀)).1).2
      have hv_lt_i : e₀.2.1 < i := (Finset.mem_filter.mp (hX he₀_prod)).2
      have hv_le : e₀.2.1 ≤ ⟨i.val - 1, by omega⟩ := by
        simp only [Fin.le_def]; omega
      exact blockSize_anti f hv_le
    calc
      target.card * (blockSize f ⟨i.val - 1, by omega⟩) ^ m
          ≤ (∏ p : Coord f, (allowed p).card) * (blockSize f ⟨i.val - 1, by omega⟩) ^ m :=
            Nat.mul_le_mul_right _ hcard_target
      _ = (∏ p ∈ Finset.univ \ Pcoords, (allowed p).card) *
            ((∏ p ∈ Pcoords, (allowed p).card) *
              (∏ _p ∈ Pcoords, blockSize f ⟨i.val - 1, by omega⟩)) := by
          rw [← Finset.prod_sdiff (Finset.subset_univ Pcoords), Finset.prod_const, hPcoords_card]
          ring
      _ = (∏ p ∈ Finset.univ \ Pcoords, (allowed p).card) *
            ∏ p ∈ Pcoords, ((allowed p).card * blockSize f ⟨i.val - 1, by omega⟩) := by
          rw [Finset.prod_mul_distrib]
      _ ≤ (∏ p ∈ Finset.univ \ Pcoords, blockSize f p.2.1.val) *
            ∏ p ∈ Pcoords, blockSize f p.2.1.val := by
          refine Nat.mul_le_mul (Finset.prod_le_prod' fun p _ => hall_le_block p) ?_
          refine Finset.prod_le_prod' fun p hp => ?_
          calc
            (allowed p).card * blockSize f ⟨i.val - 1, by omega⟩
                ≤ 1 * blockSize f ⟨i.val - 1, by omega⟩ :=
                  Nat.mul_le_mul_right _ (hall_le_one p hp)
            _ = blockSize f ⟨i.val - 1, by omega⟩ := one_mul _
            _ ≤ blockSize f p.2.1.val := hp_prev_le p hp
      _ = ∏ p : Coord f, blockSize f p.2.1.val :=
          Finset.prod_sdiff (Finset.subset_univ Pcoords)
      _ = Fintype.card (Space f) := by
          rw [Fintype.card_pi]; simp

lemma count_bad2_ir_le {i : Fin (CParam f)} (hi : 1 ≤ i.val) {r : ℕ}
    (hr4 : 4 ≤ r) (hrmax : r ≤ 4 * deltaParam f * blockSize f i) :
    (Finset.univ.filter fun ω : Space f =>
      ∃ X ∈ (leftVerts f i).powersetCard r,
        (3 * r + 1) / 2 ≤ (dirEdges f ω X).card).card * (2 * CParam f) ^ r ≤
      Fintype.card (Space f) := by
  classical
  let m : ℕ := (3 * r + 1) / 2
  let Nprev : ℕ := blockSize f ⟨i.val - 1, by omega⟩
  let N0 : ℕ := blockSize f ⟨0, by have := CParam_ge_64 f; omega⟩
  let B : ℕ := r * (r - 1) / 2
  let eventIR := Finset.univ.filter fun ω : Space f =>
    ∃ X ∈ (leftVerts f i).powersetCard r, m ≤ (dirEdges f ω X).card
  have hcov : eventIR ⊆ ((leftVerts f i).powersetCard r).biUnion (fun X =>
      ((dirPairs f X).powersetCard m).biUnion (fun P =>
        Finset.univ.filter fun ω : Space f => ∀ e ∈ P, baseArc f ω e.1 e.2)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases hω.2 with ⟨X, hX, hm_le⟩
    obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hm_le
    have hPdp : P ⊆ dirPairs f X := fun e he => (Finset.mem_filter.mp (hPsub he)).1
    have hall : ∀ e ∈ P, baseArc f ω e.1 e.2 := fun e he => (Finset.mem_filter.mp (hPsub he)).2
    exact Finset.mem_biUnion.mpr ⟨X, hX,
      Finset.mem_biUnion.mpr ⟨P, Finset.mem_powersetCard.mpr ⟨hPdp, hPcard⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩⟩⟩
  have hsum_count : eventIR.card * Nprev ^ m ≤
      (leftVerts f i).card.choose r * B.choose m * Fintype.card (Space f) := by
    have h1 : eventIR.card ≤ ∑ X ∈ (leftVerts f i).powersetCard r,
        ∑ P ∈ (dirPairs f X).powersetCard m,
          (Finset.univ.filter fun ω : Space f => ∀ e ∈ P, baseArc f ω e.1 e.2).card := by
      refine (Finset.card_le_card hcov).trans ?_
      refine Finset.card_biUnion_le.trans ?_
      exact Finset.sum_le_sum fun X _ => Finset.card_biUnion_le
    calc
      eventIR.card * Nprev ^ m
          ≤ (∑ X ∈ (leftVerts f i).powersetCard r,
              ∑ P ∈ (dirPairs f X).powersetCard m,
                (Finset.univ.filter fun ω : Space f => ∀ e ∈ P, baseArc f ω e.1 e.2).card) *
              Nprev ^ m := Nat.mul_le_mul_right _ h1
      _ = ∑ X ∈ (leftVerts f i).powersetCard r,
            ∑ P ∈ (dirPairs f X).powersetCard m,
              (Finset.univ.filter fun ω : Space f => ∀ e ∈ P, baseArc f ω e.1 e.2).card *
                Nprev ^ m := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun X _ => Finset.sum_mul _ _ _
      _ ≤ ∑ X ∈ (leftVerts f i).powersetCard r,
            ∑ _P ∈ (dirPairs f X).powersetCard m, Fintype.card (Space f) := by
          refine Finset.sum_le_sum fun X hX => Finset.sum_le_sum fun P hP => ?_
          exact count_pairSet_le f hi (Finset.mem_powersetCard.mp hX).1 hP
      _ ≤ ∑ _X ∈ (leftVerts f i).powersetCard r, B.choose m * Fintype.card (Space f) := by
          refine Finset.sum_le_sum fun X hX => ?_
          rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]
          have hcardX : X.card = r := (Finset.mem_powersetCard.mp hX).2
          have hdp : (dirPairs f X).card ≤ B := by
            have := card_dirPairs_le f X
            rwa [hcardX] at this
          exact Nat.mul_le_mul_right _ (Nat.choose_le_choose m hdp)
      _ = (leftVerts f i).card.choose r * B.choose m * Fintype.card (Space f) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, mul_assoc]
  have hchoose_L : (leftVerts f i).card.choose r * r ^ r ≤ (6 * N0) ^ r := by
    refine (choose_mul_pow_le (leftVerts f i).card r).trans ?_
    refine Nat.pow_le_pow_left ?_ r
    have hL : (leftVerts f i).card ≤ 2 * N0 := card_leftVerts_le f i
    omega
  have hchoose_B : B.choose m ≤ r ^ m := by
    have hm_pos : 0 < m ^ m := by
      have : 1 ≤ m := by dsimp [m]; omega
      positivity
    suffices h : B.choose m * m ^ m ≤ r ^ m * m ^ m from
      Nat.le_of_mul_le_mul_right h hm_pos
    have h3B : 3 * B ≤ r * m := by
      have h2B : 2 * B ≤ r * r := by
        dsimp [B]
        have := Nat.div_mul_le_self (r * (r - 1)) 2
        nlinarith [Nat.sub_le r 1]
      have h2m : 3 * r ≤ 2 * m := by dsimp [m]; omega
      nlinarith
    calc
      B.choose m * m ^ m ≤ (3 * B) ^ m := choose_mul_pow_le B m
      _ ≤ (r * m) ^ m := Nat.pow_le_pow_left h3B m
      _ = r ^ m * m ^ m := mul_pow r m m
  have hstep1 : eventIR.card * Nprev ^ m * r ^ r ≤
      (6 * N0) ^ r * r ^ m * Fintype.card (Space f) := by
    calc
      eventIR.card * Nprev ^ m * r ^ r
          ≤ (leftVerts f i).card.choose r * B.choose m * Fintype.card (Space f) * r ^ r :=
            Nat.mul_le_mul_right _ hsum_count
      _ = ((leftVerts f i).card.choose r * r ^ r) * B.choose m * Fintype.card (Space f) := by
          ring
      _ ≤ (6 * N0) ^ r * r ^ m * Fintype.card (Space f) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hchoose_L hchoose_B)
  have hsq : (eventIR.card * (2 * CParam f) ^ r) ^ 2 ≤ (Fintype.card (Space f)) ^ 2 := by
    let s : ℕ := 2 * m - 3 * r
    have h2m : 2 * m = 3 * r + s := by dsimp [s, m]; omega
    have hr_le_Nprev : r ≤ Nprev := hrmax.trans (blockSize_four_delta_le f hi)
    have hbase : 36 * N0 ^ 2 * r * (2 * CParam f) ^ 2 ≤ Nprev ^ 3 := by
      have hdexp := blockSize_dexp f hi
      calc
        36 * N0 ^ 2 * r * (2 * CParam f) ^ 2
            ≤ 36 * N0 ^ 2 * (4 * deltaParam f * blockSize f i) * (4 * (CParam f) ^ 2) := by
              have h1 : (2 * CParam f) ^ 2 = 4 * (CParam f) ^ 2 := by ring
              rw [h1]
              gcongr
        _ = DParam f * N0 ^ 2 * blockSize f i := by dsimp [DParam]; ring
        _ ≤ Nprev ^ 3 := hdexp
    have hpow_cmp : ((6 * N0) ^ r * r ^ m) ^ 2 * ((2 * CParam f) ^ r) ^ 2 ≤
        (Nprev ^ m * r ^ r) ^ 2 := by
      calc
        ((6 * N0) ^ r * r ^ m) ^ 2 * ((2 * CParam f) ^ r) ^ 2
            = ((6 * N0) ^ 2) ^ r * r ^ (2 * m) * ((2 * CParam f) ^ 2) ^ r := by
                simp only [mul_pow, ← pow_mul]
                ring_nf
        _ = (36 * N0 ^ 2 * r * (2 * CParam f) ^ 2) ^ r * r ^ s * (r ^ r) ^ 2 := by
            rw [h2m, pow_add, show 3 * r = r + 2 * r by omega, pow_add, pow_mul' r 2 r]
            have h6 : (6 * N0) ^ 2 = 36 * N0 ^ 2 := by ring
            rw [h6]
            simp only [mul_pow]
            ring
        _ ≤ (Nprev ^ 3) ^ r * Nprev ^ s * (r ^ r) ^ 2 := by
            gcongr
        _ = (Nprev ^ m * r ^ r) ^ 2 := by
            rw [← pow_mul Nprev 3 r, ← pow_add Nprev (3 * r) s, ← h2m]
            simp only [mul_pow, ← pow_mul]
            ring_nf
    have hpos_cancel : 0 < (Nprev ^ m * r ^ r) ^ 2 := by
      have hNp : 0 < Nprev := blockSize_pos f ⟨i.val - 1, by omega⟩
      have hrp : 0 < r := by omega
      positivity
    suffices hmul_sq : (eventIR.card * (2 * CParam f) ^ r) ^ 2 * (Nprev ^ m * r ^ r) ^ 2 ≤
        (Fintype.card (Space f)) ^ 2 * (Nprev ^ m * r ^ r) ^ 2 from
      Nat.le_of_mul_le_mul_right hmul_sq hpos_cancel
    have hstep1_sq : (eventIR.card * Nprev ^ m * r ^ r) ^ 2 ≤
        ((6 * N0) ^ r * r ^ m * Fintype.card (Space f)) ^ 2 :=
      Nat.pow_le_pow_left hstep1 2
    calc
      (eventIR.card * (2 * CParam f) ^ r) ^ 2 * (Nprev ^ m * r ^ r) ^ 2
          = (eventIR.card * Nprev ^ m * r ^ r) ^ 2 * ((2 * CParam f) ^ r) ^ 2 := by ring
      _ ≤ ((6 * N0) ^ r * r ^ m * Fintype.card (Space f)) ^ 2 * ((2 * CParam f) ^ r) ^ 2 :=
          Nat.mul_le_mul_right _ hstep1_sq
      _ = (((6 * N0) ^ r * r ^ m) ^ 2 * ((2 * CParam f) ^ r) ^ 2) *
            (Fintype.card (Space f)) ^ 2 := by ring
      _ ≤ (Nprev ^ m * r ^ r) ^ 2 * (Fintype.card (Space f)) ^ 2 :=
          Nat.mul_le_mul_right _ hpow_cmp
      _ = (Fintype.card (Space f)) ^ 2 * (Nprev ^ m * r ^ r) ^ 2 := mul_comm _ _
  change eventIR.card * (2 * CParam f) ^ r ≤ Fintype.card (Space f)
  by_contra hgt
  push Not at hgt
  nlinarith

lemma two_mul_card_bad2_lt :
    2 * (Finset.univ.filter (fun ω : Space f => Bad2 f ω)).card < Fintype.card (Space f) := by
  classical
  let badFin := Finset.univ.filter (fun ω : Space f => Bad2 f ω)
  let validI := Finset.univ.filter (fun i : Fin (CParam f) => 1 ≤ i.val)
  let eventIR : Fin (CParam f) → ℕ → Finset (Space f) := fun i r =>
    Finset.univ.filter fun ω : Space f =>
      ∃ X ∈ (leftVerts f i).powersetCard r, (3 * r + 1) / 2 ≤ (dirEdges f ω X).card
  have hcov : badFin ⊆ validI.biUnion (fun i =>
      (Finset.Icc 4 (4 * deltaParam f * blockSize f i)).biUnion (fun r => eventIR i r)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases hω.2 with ⟨i, hi, X, hX, hr4, hrmax, hm⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
      Finset.mem_biUnion.mpr ⟨X.card, Finset.mem_Icc.mpr ⟨hr4, hrmax⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, X, Finset.mem_powersetCard.mpr ⟨hX, rfl⟩, hm⟩⟩⟩
  have hcard_nat : badFin.card ≤ ∑ i ∈ validI,
      ∑ r ∈ Finset.Icc 4 (4 * deltaParam f * blockSize f i), (eventIR i r).card := by
    refine (Finset.card_le_card hcov).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    exact Finset.sum_le_sum fun i _ => Finset.card_biUnion_le
  let x : ℝ := 1 / (2 * (CParam f : ℝ))
  have hC64 := CParam_ge_64 f
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (64 : ℝ) ≤ (CParam f : ℝ) := by exact_mod_cast hC64
    linarith
  have hir_real : ∀ i ∈ validI, ∀ r ∈ Finset.Icc 4 (4 * deltaParam f * blockSize f i),
      ((eventIR i r).card : ℝ) ≤ (Fintype.card (Space f) : ℝ) * x ^ r := by
    intro i hi r hr
    have hi1 : 1 ≤ i.val := (Finset.mem_filter.mp hi).2
    obtain ⟨hr4, hrmax⟩ := Finset.mem_Icc.mp hr
    have hnat := count_bad2_ir_le f hi1 hr4 hrmax
    have hreal : ((eventIR i r).card : ℝ) * ((2 * (CParam f : ℝ)) ^ r) ≤
        (Fintype.card (Space f) : ℝ) := by exact_mod_cast hnat
    have hpos : (0 : ℝ) < (2 * (CParam f : ℝ)) ^ r := by positivity
    dsimp [x]
    rw [one_div_pow, mul_one_div, le_div_iff₀ hpos]
    exact hreal
  have hcard_real : (badFin.card : ℝ) ≤
      (Fintype.card (Space f) : ℝ) * ((CParam f : ℝ) * (2 * x ^ 4)) := by
    calc
      (badFin.card : ℝ)
          ≤ ∑ i ∈ validI, ∑ r ∈ Finset.Icc 4 (4 * deltaParam f * blockSize f i),
              ((eventIR i r).card : ℝ) := by exact_mod_cast hcard_nat
      _ ≤ ∑ i ∈ validI, ∑ r ∈ Finset.Icc 4 (4 * deltaParam f * blockSize f i),
            ((Fintype.card (Space f) : ℝ) * x ^ r) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun r hr => hir_real i hi r hr
      _ = ∑ i ∈ validI, (Fintype.card (Space f) : ℝ) *
            ∑ r ∈ Finset.Icc 4 (4 * deltaParam f * blockSize f i), x ^ r := by
          refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ _i ∈ validI, (Fintype.card (Space f) : ℝ) * (2 * x ^ 4) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (sum_geom_Icc_four_le hx0 hxhalf _) (by positivity)
      _ ≤ (CParam f : ℝ) * ((Fintype.card (Space f) : ℝ) * (2 * x ^ 4)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (Finset.card_le_univ validI).trans_eq (Fintype.card_fin _)
      _ = (Fintype.card (Space f) : ℝ) * ((CParam f : ℝ) * (2 * x ^ 4)) := by ring
  have hsmall : (CParam f : ℝ) * (2 * x ^ 4) < 1 / 2 := by
    have hCr : (64 : ℝ) ≤ (CParam f : ℝ) := by exact_mod_cast hC64
    dsimp [x]
    have hcpos : (0 : ℝ) < (CParam f : ℝ) := by linarith
    have hid : (CParam f : ℝ) * (2 * (1 / (2 * (CParam f : ℝ))) ^ 4) =
        1 / (8 * (CParam f : ℝ) ^ 3) := by
      field_simp
      ring
    rw [hid, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have hpow3 : (64 : ℝ) ^ 3 ≤ (CParam f : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hCr 3
    norm_num at hpow3 ⊢
    linarith
  have hsp_pos : (0 : ℝ) < (Fintype.card (Space f) : ℝ) := Nat.cast_pos.mpr (space_card_pos f)
  have hlt_final : 2 * (badFin.card : ℝ) < (Fintype.card (Space f) : ℝ) := by
    nlinarith
  exact_mod_cast hlt_final

lemma exists_good_omega : ∃ ω : Space f, ¬ Bad1 f ω ∧ ¬ Bad2 f ω := by
  classical
  by_contra hnone
  push Not at hnone
  have huniv : (Finset.univ : Finset (Space f)) ⊆
      (Finset.univ.filter fun ω : Space f => Bad1 f ω) ∪
      (Finset.univ.filter fun ω : Space f => Bad2 f ω) := by
    intro ω _
    by_cases h1 : Bad1 f ω
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone ω h1⟩)
  have hcard := (Finset.card_le_card huniv).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ] at hcard
  have h1 := two_mul_card_bad1_lt f
  have h2 := two_mul_card_bad2_lt f
  omega

/- ## Section 3: Bounded-degree subgraphs are 6-colorable and line graph analysis -/

lemma sub_base_min_deg_le_five {ω : Space f} (hnotBad2 : ¬ Bad2 f ω)
    (Q : SimpleGraph (BaseVert f)) [DecidableRel Q.Adj] (hQsub : Q ≤ baseGraph f ω)
    {S : Finset (BaseVert f)} (hSne : S.Nonempty)
    (hmax : ∀ v ∈ S, (S.filter (Q.Adj v)).card ≤ deltaParam f) :
    ∃ v ∈ S, (S.filter (Q.Adj v)).card ≤ 5 := by
  classical
  let tailS : ℕ → Finset (BaseVert f) := fun m => S.filter fun v => m ≤ v.1.val
  have hex_i : ∃ m ∈ Finset.Icc 1 (CParam f), (tailS m).card * (2 * deltaParam f) < S.card := by
    refine ⟨CParam f, Finset.mem_Icc.mpr ⟨by have := CParam_ge_64 f; omega, le_rfl⟩, ?_⟩
    have hemp : tailS (CParam f) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      exact not_le_of_gt v.1.isLt (Finset.mem_filter.mp hv).2
    rw [hemp, Finset.card_empty, zero_mul]
    exact Finset.card_pos.mpr hSne
  let validM := (Finset.Icc 1 (CParam f)).filter fun m =>
    (tailS m).card * (2 * deltaParam f) < S.card
  have hvalid_ne : validM.Nonempty := by
    rcases hex_i with ⟨m, hm1, hm2⟩
    exact ⟨m, Finset.mem_filter.mpr ⟨hm1, hm2⟩⟩
  let m0 : ℕ := validM.min' hvalid_ne
  have hm0_mem : m0 ∈ validM := Finset.min'_mem validM hvalid_ne
  obtain ⟨hm0_icc, hm0_small⟩ := Finset.mem_filter.mp hm0_mem
  obtain ⟨hm0_ge1, hm0_leC⟩ := Finset.mem_Icc.mp hm0_icc
  let idx : Fin (CParam f) := ⟨m0 - 1, by omega⟩
  have hS_le_tail : S.card ≤ 4 * deltaParam f * blockSize f idx := by
    have hprev_big : S.card ≤ (tailS (m0 - 1)).card * (2 * deltaParam f) := by
      rcases eq_or_lt_of_le hm0_ge1 with h1eq | hgt1
      · rw [← h1eq]
        have h0 : tailS 0 = S := by ext v; simp [tailS]
        rw [Nat.sub_self, h0]
        have := deltaParam_pos f
        nlinarith
      · by_contra hlt
        have hmem_prev : m0 - 1 ∈ validM :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, lt_of_not_ge hlt⟩
        have := Finset.min'_le validM (m0 - 1) hmem_prev
        omega
    have htail_le : (tailS (m0 - 1)).card ≤ 2 * blockSize f idx := by
      have hsub : tailS (m0 - 1) ⊆ tailVerts f idx := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
      exact (Finset.card_le_card hsub).trans (card_tailVerts_le f idx)
    nlinarith
  let X : Finset (BaseVert f) := S.filter fun v => v.1.val < m0 - 1
  let Y : Finset (BaseVert f) := S.filter fun v => v.1.val = m0 - 1
  let Z : Finset (BaseVert f) := tailS m0
  have hX_le_S : X.card ≤ S.card := Finset.card_filter_le _ _
  have hQX_edges : ((X ×ˢ X).filter fun p => Q.Adj p.1 p.2).card ≤ 3 * X.card := by
    have hbi : ((X ×ˢ X).filter fun p => Q.Adj p.1 p.2).card ≤ 2 * (dirEdges f ω X).card := by
      let lowEnd : BaseVert f × BaseVert f → BaseVert f × BaseVert f := fun p =>
        if p.1.1 < p.2.1 then p else (p.2, p.1)
      have hmaps : ∀ p ∈ (X ×ˢ X).filter (fun p => Q.Adj p.1 p.2),
          lowEnd p ∈ dirEdges f ω X := by
        intro ⟨u, v⟩ hp
        obtain ⟨huvX, hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨huX, hvX⟩ := Finset.mem_product.mp huvX
        rcases hQsub hadj with harc | harc
        · have hlt : u.1 < v.1 := harc.1
          simp only [lowEnd, if_pos hlt]
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨huvX, hlt⟩, harc⟩
        · have hlt : v.1 < u.1 := harc.1
          have hnot : ¬ u.1 < v.1 := asymm hlt
          simp only [lowEnd, if_neg hnot]
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hvX, huX⟩, hlt⟩, harc⟩
      have hfib : ∀ e ∈ dirEdges f ω X,
          (((X ×ˢ X).filter fun p => Q.Adj p.1 p.2).filter (fun p => lowEnd p = e)).card ≤ 2 := by
        intro ⟨a, b⟩ _
        have hsub_ab : (((X ×ˢ X).filter fun p => Q.Adj p.1 p.2).filter (fun p => lowEnd p = (a, b))) ⊆
            {(a, b), (b, a)} := by
          intro ⟨u, v⟩ hp
          have heq := (Finset.mem_filter.mp hp).2
          dsimp [lowEnd] at heq
          split_ifs at heq
          · simp [heq]
          · rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
            simp
        exact (Finset.card_le_card hsub_ab).trans Finset.card_le_two
      calc
        ((X ×ˢ X).filter fun p => Q.Adj p.1 p.2).card
            = ∑ e ∈ dirEdges f ω X,
                (((X ×ˢ X).filter fun p => Q.Adj p.1 p.2).filter (fun p => lowEnd p = e)).card :=
              Finset.card_eq_sum_card_fiberwise hmaps
        _ ≤ ∑ _e ∈ dirEdges f ω X, 2 := Finset.sum_le_sum hfib
        _ = 2 * (dirEdges f ω X).card := by simp [mul_comm]
    by_cases hX4 : X.card < 4
    · have hdp := card_dirPairs_le f X
      have hde : (dirEdges f ω X).card ≤ X.card * (X.card - 1) / 2 :=
        (Finset.card_filter_le _ _).trans hdp
      interval_cases X.card <;> omega
    · have hm0_ge2 : 1 ≤ idx.val := by
        by_contra h0
        have hm0_1 : m0 = 1 := by dsimp [idx] at h0; omega
        have hempX : X = ∅ := by ext v; simp [X, hm0_1]
        rw [hempX, Finset.card_empty] at hX4
        omega
      have hX_left : X ⊆ leftVerts f idx := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
      have hde_lt : (dirEdges f ω X).card < (3 * X.card + 1) / 2 := by
        by_contra hge
        exact hnotBad2 ⟨idx, hm0_ge2, X, hX_left, by omega, hX_le_S.trans hS_le_tail, not_lt.mp hge⟩
      omega
  have hXY_edges : ((X ×ˢ Y).filter fun p => Q.Adj p.1 p.2).card ≤ X.card := by
    have hfib : ∀ x ∈ X, (Y.filter (Q.Adj x)).card ≤ 1 := by
      intro x hx
      rw [Finset.card_le_one_iff]
      intro y₁ y₂ hy₁ hy₂
      obtain ⟨hy₁Y, hadj₁⟩ := Finset.mem_filter.mp hy₁
      obtain ⟨hy₂Y, hadj₂⟩ := Finset.mem_filter.mp hy₂
      have hy₁_idx : y₁.1 = idx := Fin.ext (Finset.mem_filter.mp hy₁Y).2
      have hy₂_idx : y₂.1 = idx := Fin.ext (Finset.mem_filter.mp hy₂Y).2
      have hx_lt : x.1 < idx := Fin.mk_lt_mk.mpr (Finset.mem_filter.mp hx).2
      have harc₁ : baseArc f ω x y₁ :=
        (hQsub hadj₁).resolve_right fun h => asymm hx_lt (hy₁_idx ▸ h.1)
      have harc₂ : baseArc f ω x y₂ :=
        (hQsub hadj₂).resolve_right fun h => asymm hx_lt (hy₂_idx ▸ h.1)
      obtain ⟨hlt₁, heq₁⟩ := harc₁
      obtain ⟨hlt₂, heq₂⟩ := harc₂
      have hc : (⟨x.1, ⟨y₁.1, hlt₁⟩, x.2⟩ : Coord f) = ⟨x.1, ⟨y₂.1, hlt₂⟩, x.2⟩ := by
        rcases y₁ with ⟨a₁, z₁⟩
        rcases y₂ with ⟨a₂, z₂⟩
        dsimp only at hy₁_idx hy₂_idx
        subst hy₁_idx; subst hy₂_idx; rfl
      calc
        y₁ = (⟨y₁.1, ω ⟨x.1, ⟨y₁.1, hlt₁⟩, x.2⟩⟩ : BaseVert f) := by rw [heq₁]
        _ = ⟨y₂.1, ω ⟨x.1, ⟨y₂.1, hlt₂⟩, x.2⟩⟩ :=
            congrArg (fun q : Coord f => (⟨q.2.1.val, ω q⟩ : BaseVert f)) hc
        _ = y₂ := by rw [heq₂]
    calc
      ((X ×ˢ Y).filter fun p => Q.Adj p.1 p.2).card
          = ∑ x ∈ X, (Y.filter (Q.Adj x)).card := by
              rw [Finset.card_filter, Finset.sum_product]
              simp only [Finset.card_filter]
      _ ≤ ∑ _x ∈ X, 1 := Finset.sum_le_sum hfib
      _ = X.card := by simp
  have hYX_edges : ((Y ×ˢ X).filter fun p => Q.Adj p.1 p.2).card ≤ X.card := by
    have hbij : ((Y ×ˢ X).filter fun p => Q.Adj p.1 p.2).card =
        ((X ×ˢ Y).filter fun p => Q.Adj p.1 p.2).card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro ⟨y, x⟩ hp
        obtain ⟨hyx, hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨hy, hx⟩ := Finset.mem_product.mp hyx
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hadj.symm⟩
      · intro ⟨y₁, x₁⟩ _ ⟨y₂, x₂⟩ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro ⟨x, y⟩ hp
        obtain ⟨hxy, hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
        exact ⟨(y, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, hadj.symm⟩, rfl⟩
    rw [hbij]
    exact hXY_edges
  have hYY_edges : ((Y ×ˢ Y).filter fun p => Q.Adj p.1 p.2) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ⟨y₁, y₂⟩ hp
    obtain ⟨hyy, hadj⟩ := Finset.mem_filter.mp hp
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_product.mp hyy
    have h1 := (Finset.mem_filter.mp hy₁).2
    have h2 := (Finset.mem_filter.mp hy₂).2
    rcases hQsub hadj with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;>
      (simp only [Fin.lt_def] at hlt; omega)
  have hZS_edges : ((Z ×ˢ S).filter fun p => Q.Adj p.1 p.2).card ≤ Z.card * deltaParam f := by
    calc
      ((Z ×ˢ S).filter fun p => Q.Adj p.1 p.2).card
          = ∑ z ∈ Z, (S.filter (Q.Adj z)).card := by
              rw [Finset.card_filter, Finset.sum_product]
              simp only [Finset.card_filter]
      _ ≤ ∑ _z ∈ Z, deltaParam f :=
          Finset.sum_le_sum fun z hz => hmax z (Finset.mem_filter.mp hz).1
      _ = Z.card * deltaParam f := by simp
  have hSZ_edges : ((S ×ˢ Z).filter fun p => Q.Adj p.1 p.2).card ≤ Z.card * deltaParam f := by
    have hbij : ((S ×ˢ Z).filter fun p => Q.Adj p.1 p.2).card =
        ((Z ×ˢ S).filter fun p => Q.Adj p.1 p.2).card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro ⟨u, z⟩ hp
        obtain ⟨huz, hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨hu, hz⟩ := Finset.mem_product.mp huz
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hu⟩, hadj.symm⟩
      · intro ⟨u₁, z₁⟩ _ ⟨u₂, z₂⟩ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro ⟨z, u⟩ hp
        obtain ⟨hzu, hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨hz, hu⟩ := Finset.mem_product.mp hzu
        exact ⟨(u, z), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hz⟩, hadj.symm⟩, rfl⟩
    rw [hbij]
    exact hZS_edges
  have hcov_edges : ((S ×ˢ S).filter fun p => Q.Adj p.1 p.2) ⊆
      (((X ×ˢ X).filter fun p => Q.Adj p.1 p.2) ∪
       ((X ×ˢ Y).filter fun p => Q.Adj p.1 p.2) ∪
       ((Y ×ˢ X).filter fun p => Q.Adj p.1 p.2) ∪
       ((Z ×ˢ S).filter fun p => Q.Adj p.1 p.2) ∪
       ((S ×ˢ Z).filter fun p => Q.Adj p.1 p.2)) := by
    intro ⟨u, v⟩ hp
    obtain ⟨huv, hadj⟩ := Finset.mem_filter.mp hp
    obtain ⟨huS, hvS⟩ := Finset.mem_product.mp huv
    by_cases huZ : m0 ≤ u.1.val
    · have huZm : u ∈ Z := Finset.mem_filter.mpr ⟨huS, huZ⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huZm, hvS⟩, hadj⟩))
    · by_cases hvZ : m0 ≤ v.1.val
      · have hvZm : v ∈ Z := Finset.mem_filter.mpr ⟨hvS, hvZ⟩
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS, hvZm⟩, hadj⟩)
      · by_cases huY : u.1.val = m0 - 1 <;> by_cases hvY : v.1.val = m0 - 1
        · have hmemYY : (u, v) ∈ (Y ×ˢ Y).filter (fun p => Q.Adj p.1 p.2) :=
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_filter.mpr ⟨huS, huY⟩, Finset.mem_filter.mpr ⟨hvS, hvY⟩⟩, hadj⟩
          rw [hYY_edges] at hmemYY
          exact absurd hmemYY (Finset.notMem_empty _)
        · have hvXm : v ∈ X := Finset.mem_filter.mpr ⟨hvS, by omega⟩
          have huYm : u ∈ Y := Finset.mem_filter.mpr ⟨huS, huY⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huYm, hvXm⟩, hadj⟩)))
        · have huXm : u ∈ X := Finset.mem_filter.mpr ⟨huS, by omega⟩
          have hvYm : v ∈ Y := Finset.mem_filter.mpr ⟨hvS, hvY⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huXm, hvYm⟩, hadj⟩))))
        · have huXm : u ∈ X := Finset.mem_filter.mpr ⟨huS, by omega⟩
          have hvXm : v ∈ X := Finset.mem_filter.mpr ⟨hvS, by omega⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huXm, hvXm⟩, hadj⟩))))
  have hsum_deg_lt : ∑ v ∈ S, (S.filter (Q.Adj v)).card < 6 * S.card := by
    have hsum_eq : ∑ v ∈ S, (S.filter (Q.Adj v)).card =
        ((S ×ˢ S).filter fun p => Q.Adj p.1 p.2).card := by
      rw [Finset.card_filter, Finset.sum_product]
      simp only [Finset.card_filter]
    rw [hsum_eq]
    have hc1 := (Finset.card_le_card hcov_edges).trans (Finset.card_union_le _ _)
    have hc2 := Finset.card_union_le
      (((X ×ˢ X).filter fun p => Q.Adj p.1 p.2) ∪
       ((X ×ˢ Y).filter fun p => Q.Adj p.1 p.2) ∪
       ((Y ×ˢ X).filter fun p => Q.Adj p.1 p.2))
      ((Z ×ˢ S).filter fun p => Q.Adj p.1 p.2)
    have hc3 := Finset.card_union_le
      (((X ×ˢ X).filter fun p => Q.Adj p.1 p.2) ∪
       ((X ×ˢ Y).filter fun p => Q.Adj p.1 p.2))
      ((Y ×ˢ X).filter fun p => Q.Adj p.1 p.2)
    have hc4 := Finset.card_union_le
      ((X ×ˢ X).filter fun p => Q.Adj p.1 p.2)
      ((X ×ˢ Y).filter fun p => Q.Adj p.1 p.2)
    have hZ_sum : ((Z ×ˢ S).filter fun p => Q.Adj p.1 p.2).card +
        ((S ×ˢ Z).filter fun p => Q.Adj p.1 p.2).card < S.card := by
      have h1 : ((Z ×ˢ S).filter fun p => Q.Adj p.1 p.2).card +
          ((S ×ˢ Z).filter fun p => Q.Adj p.1 p.2).card ≤ 2 * (Z.card * deltaParam f) := by
        linarith
      have h2 : 2 * (Z.card * deltaParam f) = (tailS m0).card * (2 * deltaParam f) := by
        dsimp [Z]; ring
      linarith
    linarith
  by_contra hno
  push Not at hno
  have hge : 6 * S.card ≤ ∑ v ∈ S, (S.filter (Q.Adj v)).card := by
    calc
      6 * S.card = ∑ _v ∈ S, 6 := by simp [mul_comm]
      _ ≤ ∑ v ∈ S, (S.filter (Q.Adj v)).card := Finset.sum_le_sum fun v hv => hno v hv
  omega

lemma six_color_of_min_deg_five {V0 : Type} [Fintype V0] [DecidableEq V0]
    (Q : SimpleGraph V0) [DecidableRel Q.Adj]
    (hdeg : ∀ S : Finset V0, S.Nonempty → ∃ v ∈ S, (S.filter (Q.Adj v)).card ≤ 5) :
    ∀ n : ℕ, ∀ S : Finset V0, S.card = n →
      ∃ c : V0 → Fin 6, ∀ u ∈ S, ∀ v ∈ S, Q.Adj u v → c u ≠ c v
  | 0, S, hcard => by
      have hemp := Finset.card_eq_zero.mp hcard
      subst hemp
      exact ⟨fun _ => 0, by simp⟩
  | n + 1, S, hcard => by
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hvS, hvdeg⟩ := hdeg S hSne
      let S' := S.erase v
      have hcard' : S'.card = n := by
        rw [Finset.card_erase_of_mem hvS, hcard]; omega
      obtain ⟨c', hc'⟩ := six_color_of_min_deg_five Q hdeg n S' hcard'
      let used : Finset (Fin 6) := (S'.filter (Q.Adj v)).image c'
      have hused_lt : used.card < (Finset.univ : Finset (Fin 6)).card := by
        have hsub : S'.filter (Q.Adj v) ⊆ S.filter (Q.Adj v) :=
          Finset.filter_subset_filter _ (Finset.erase_subset v S)
        have hc_le : used.card ≤ (S.filter (Q.Adj v)).card :=
          Finset.card_image_le.trans (Finset.card_le_card hsub)
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      have hex_col : (Finset.univ \ used).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : (Finset.univ : Finset (Fin 6)) ⊆ used :=
          Finset.sdiff_eq_empty_iff_subset.mp hemp
        exact not_le_of_gt hused_lt (Finset.card_le_card hsub)
      obtain ⟨cv, hcv⟩ := hex_col
      have hcv_not_used : cv ∉ used := (Finset.mem_sdiff.mp hcv).2
      let c : V0 → Fin 6 := fun x => if x = v then cv else c' x
      refine ⟨c, ?_⟩
      intro x hx y hy hadj
      by_cases hxv : x = v <;> by_cases hyv : y = v
      · subst hxv; subst hyv; exact absurd hadj (Q.loopless.irrefl _)
      · subst hxv
        have hyS' : y ∈ S' := Finset.mem_erase.mpr ⟨hyv, hy⟩
        simp only [c, ↓reduceIte, if_neg hyv]
        intro heq
        exact hcv_not_used (Finset.mem_image.mpr
          ⟨y, Finset.mem_filter.mpr ⟨hyS', hadj⟩, heq.symm⟩)
      · subst hyv
        have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxv, hx⟩
        simp only [c, if_neg hxv, ↓reduceIte]
        intro heq
        exact hcv_not_used (Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨hxS', hadj.symm⟩, heq⟩)
      · simp only [c, if_neg hxv, if_neg hyv]
        exact hc' x (Finset.mem_erase.mpr ⟨hxv, hx⟩) y (Finset.mem_erase.mpr ⟨hyv, hy⟩) hadj

/- ### Subsection 3.1: Line graph, chromatic lower bound, and 4-colorability of girth-5 subgraphs -/

abbrev ArcVert (ω : Space f) : Type := { e : BaseVert f × BaseVert f // baseArc f ω e.1 e.2 }

def lineGraph (ω : Space f) : SimpleGraph (ArcVert f ω) where
  Adj a b := a.1.2 = b.1.1 ∨ b.1.2 = a.1.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => by
    rcases h with heq | heq
    · exact lt_irrefl _ (heq ▸ a.2.1)
    · exact lt_irrefl _ (heq ▸ a.2.1)⟩

lemma arcVert_nonempty (ω : Space f) : Nonempty (ArcVert f ω) := by
  have hC := CParam_ge_64 f
  let i0 : Fin (CParam f) := ⟨0, by omega⟩
  let i1 : Fin (CParam f) := ⟨1, by omega⟩
  have h01 : i0 < i1 := by simp [i0, i1, Fin.lt_def]
  let x0 : Fin (blockSize f i0) := ⟨0, blockSize_pos f i0⟩
  let y1 : Fin (blockSize f i1) := ω ⟨i0, ⟨i1, h01⟩, x0⟩
  exact ⟨⟨(⟨i0, x0⟩, ⟨i1, y1⟩), ⟨h01, rfl⟩⟩⟩

lemma not_lineGraph_colorable {ω : Space f} (hnotBad1 : ¬ Bad1 f ω) :
    ¬ (lineGraph f ω).Colorable (k0 f) := by
  classical
  rintro ⟨col⟩
  let outSet : BaseVert f → Finset (Fin (k0 f)) := fun v =>
    Finset.univ.filter fun c : Fin (k0 f) =>
      ∃ e : ArcVert f ω, e.1.1 = v ∧ col e = c
  have hproper : ∀ {u v : BaseVert f}, (baseGraph f ω).Adj u v → outSet u ≠ outSet v := by
    intro u v hadj heq
    have checkDir : ∀ {a b : BaseVert f}, baseArc f ω a b → outSet a = outSet b → False := by
      intro a b harc hout
      let e0 : ArcVert f ω := ⟨(a, b), harc⟩
      have hmem_a : col e0 ∈ outSet a :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, e0, rfl, rfl⟩
      rw [hout] at hmem_a
      rcases (Finset.mem_filter.mp hmem_a).2 with ⟨e1, he1_fst, hcol_eq⟩
      have hadj_line : (lineGraph f ω).Adj e0 e1 := Or.inl he1_fst.symm
      exact col.valid hadj_line hcol_eq.symm
    rcases hadj with harc | harc
    · exact checkDir harc heq
    · exact checkDir harc heq.symm
  let fiber : Finset (Fin (k0 f)) → Finset (BaseVert f) := fun S =>
    Finset.univ.filter fun v : BaseVert f => outSet v = S
  have hfib_indep : ∀ S : Finset (Fin (k0 f)), IsIndepFinset f ω (fiber S) := by
    intro S u hu v hv hadj
    exact hproper hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  have hfib_lt : ∀ S : Finset (Fin (k0 f)), setWeight f (fiber S) < 16 * (qParam f : ℝ) := by
    intro S
    by_contra hge
    exact hnotBad1 ⟨fiber S, hfib_indep S, not_lt.mp hge⟩
  have hsum_weights : ∑ S : Finset (Fin (k0 f)), setWeight f (fiber S) = (CParam f : ℝ) := by
    dsimp [setWeight]
    rw [Finset.sum_comm]
    have hj_eq : ∀ j : Fin (CParam f),
        ∑ S : Finset (Fin (k0 f)), (partCard f (fiber S) j : ℝ) / (blockSize f j : ℝ) = 1 := by
      intro j
      rw [← Finset.sum_div]
      have hpart_sum : ∑ S : Finset (Fin (k0 f)), partCard f (fiber S) j = blockSize f j := by
        dsimp [partCard]
        have hbi := Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (Fin (blockSize f j))))
          (t := (Finset.univ : Finset (Finset (Fin (k0 f)))))
          (f := fun x => outSet ⟨j, x⟩)
          (fun _ _ => Finset.mem_univ _)
        rw [Finset.card_univ, Fintype.card_fin] at hbi
        refine Eq.symm (hbi.trans ?_)
        refine Finset.sum_congr rfl fun S _ => ?_
        congr 1
        ext x
        simp [fiber]
      have hb0 : (blockSize f j : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (blockSize_pos f j).ne'
      have hcast : ∑ S : Finset (Fin (k0 f)), (partCard f (fiber S) j : ℝ) =
          (blockSize f j : ℝ) := by exact_mod_cast hpart_sum
      rw [hcast, div_self hb0]
    simp [hj_eq, Fintype.card_fin]
  have hcard_pow : Fintype.card (Finset (Fin (k0 f))) = qParam f := by
    simp [qParam]
  have hlt_sum : ∑ S : Finset (Fin (k0 f)), setWeight f (fiber S) <
      ∑ _S : Finset (Fin (k0 f)), (16 * (qParam f : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun S _ => hfib_lt S
  rw [hsum_weights, Finset.sum_const, Finset.card_univ, hcard_pow, nsmul_eq_mul] at hlt_sum
  have hCeq : (CParam f : ℝ) = (qParam f : ℝ) * (16 * (qParam f : ℝ)) := by
    push_cast [CParam]; ring
  linarith

lemma c4_free_four_colorable {ω : Space f} (hnotBad2 : ¬ Bad2 f ω)
    (H : SimpleGraph (ArcVert f ω)) [DecidableRel H.Adj] (hHsub : H ≤ lineGraph f ω)
    (hc4 : ∀ e₁ e₂ e₃ e₄ : ArcVert f ω,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₁ ≠ e₄ → e₂ ≠ e₃ → e₂ ≠ e₄ → e₃ ≠ e₄ →
      ¬ (H.Adj e₁ e₂ ∧ H.Adj e₂ e₃ ∧ H.Adj e₃ e₄ ∧ H.Adj e₄ e₁)) :
    H.Colorable 4 := by
  classical
  let outH : ArcVert f ω → Finset (ArcVert f ω) := fun e =>
    Finset.univ.filter fun e' : ArcVert f ω => e.1.2 = e'.1.1 ∧ H.Adj e e'
  let qArc : BaseVert f → BaseVert f → Prop := fun u v =>
    ∃ h : baseArc f ω u v, 2 ≤ (outH ⟨(u, v), h⟩).card
  let Q : SimpleGraph (BaseVert f) := {
    Adj := fun u v => qArc u v ∨ qArc v u
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun u h => by
      rcases h with ⟨⟨hlt, _⟩, _⟩ | ⟨⟨hlt, _⟩, _⟩ <;> exact lt_irrefl _ hlt⟩
  }
  have hQsub : Q ≤ baseGraph f ω := by
    intro u v hadj
    rcases hadj with ⟨harc, _⟩ | ⟨harc, _⟩
    · exact Or.inl harc
    · exact Or.inr harc
  have hQmax : ∀ v : BaseVert f,
      (Finset.univ.filter (Q.Adj v)).card ≤ deltaParam f := by
    intro v
    let outG : Finset (BaseVert f) := Finset.univ.filter fun w => baseArc f ω v w
    have houtG_le : outG.card ≤ dParam f := by
      let projPart : BaseVert f → Fin (CParam f) := Sigma.fst
      have hinj : Set.InjOn projPart (outG : Set (BaseVert f)) := by
        intro w₁ hw₁ w₂ hw₂ heq
        simp only [Finset.mem_coe, outG, Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
        obtain ⟨hlt₁, heq₁⟩ := hw₁
        obtain ⟨hlt₂, heq₂⟩ := hw₂
        have hc : (⟨v.1, ⟨w₁.1, hlt₁⟩, v.2⟩ : Coord f) = ⟨v.1, ⟨w₂.1, hlt₂⟩, v.2⟩ := by
          rcases w₁ with ⟨a₁, z₁⟩
          rcases w₂ with ⟨a₂, z₂⟩
          dsimp [projPart] at heq
          subst heq
          rfl
        calc
          w₁ = (⟨w₁.1, ω ⟨v.1, ⟨w₁.1, hlt₁⟩, v.2⟩⟩ : BaseVert f) := by rw [heq₁]
          _ = ⟨w₂.1, ω ⟨v.1, ⟨w₂.1, hlt₂⟩, v.2⟩⟩ := by
              exact congrArg (fun q : Coord f => (⟨q.2.1.val, ω q⟩ : BaseVert f)) hc
          _ = w₂ := by rw [heq₂]
      have hsub : outG.image projPart ⊆ Finset.univ.erase v.1 := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨w, hw, rfl⟩
        have hlt := (Finset.mem_filter.mp hw).2.1
        exact Finset.mem_erase.mpr ⟨(ne_of_lt hlt).symm, Finset.mem_univ _⟩
      calc
        outG.card = (outG.image projPart).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ.erase v.1).card := Finset.card_le_card hsub
        _ = dParam f := by simp [dParam, Finset.card_erase_of_mem]
    let outQ : Finset (BaseVert f) := Finset.univ.filter fun w => qArc v w
    let inQ : Finset (BaseVert f) := Finset.univ.filter fun u => qArc u v
    have houtQ_le : outQ.card ≤ dParam f := by
      refine (Finset.card_le_card ?_).trans houtG_le
      intro w hw
      obtain ⟨harc, _⟩ := (Finset.mem_filter.mp hw).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, harc⟩
    have hinQ_le : inQ.card ≤ dParam f * dParam f := by
      have hex_pair : ∀ u : { u // u ∈ inQ },
          ∃ f₁ f₂ : ArcVert f ω, f₁ ≠ f₂ ∧
            f₁ ∈ outH ⟨(u.1, v), (Finset.mem_filter.mp u.2).2.choose⟩ ∧
            f₂ ∈ outH ⟨(u.1, v), (Finset.mem_filter.mp u.2).2.choose⟩ := by
        intro u
        have h2 : 1 < (outH ⟨(u.1, v), (Finset.mem_filter.mp u.2).2.choose⟩).card := by
          have := (Finset.mem_filter.mp u.2).2.choose_spec
          omega
        obtain ⟨f₁, f₂, hf₁, hf₂, hne⟩ := Finset.one_lt_card_iff.mp h2
        exact ⟨f₁, f₂, hne, hf₁, hf₂⟩
      choose f₁ f₂ hne hf₁ hf₂ using hex_pair
      let pairMap : { u // u ∈ inQ } → BaseVert f × BaseVert f := fun u =>
        ((f₁ u).1.2, (f₂ u).1.2)
      have hpair_mem : ∀ u : { u // u ∈ inQ }, pairMap u ∈ outG ×ˢ outG := by
        intro u
        have hv1 : v = (f₁ u).1.1 := (Finset.mem_filter.mp (hf₁ u)).2.1
        have hv2 : v = (f₂ u).1.1 := (Finset.mem_filter.mp (hf₂ u)).2.1
        refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        · rw [hv1]; exact (f₁ u).2
        · rw [hv2]; exact (f₂ u).2
      have hpair_inj : Function.Injective pairMap := by
        intro u₁ u₂ heq
        apply Subtype.ext
        by_contra hu_ne
        let e₁ : ArcVert f ω := ⟨(u₁.1, v), (Finset.mem_filter.mp u₁.2).2.choose⟩
        let e₂ : ArcVert f ω := ⟨(u₂.1, v), (Finset.mem_filter.mp u₂.2).2.choose⟩
        have hf1_eq : f₁ u₁ = f₁ u₂ := by
          apply Subtype.ext
          have hv1 : (f₁ u₁).1.1 = v := (Finset.mem_filter.mp (hf₁ u₁)).2.1.symm
          have hv2 : (f₁ u₂).1.1 = v := (Finset.mem_filter.mp (hf₁ u₂)).2.1.symm
          exact Prod.ext (hv1.trans hv2.symm) (congrArg Prod.fst heq)
        have hf2_eq : f₂ u₁ = f₂ u₂ := by
          apply Subtype.ext
          have hv1 : (f₂ u₁).1.1 = v := (Finset.mem_filter.mp (hf₂ u₁)).2.1.symm
          have hv2 : (f₂ u₂).1.1 = v := (Finset.mem_filter.mp (hf₂ u₂)).2.1.symm
          have heq2 : (f₂ u₁).1.2 = (f₂ u₂).1.2 :=
            (Prod.ext_iff.mp heq).2
          exact Prod.ext (hv1.trans hv2.symm) heq2
        have he12 : e₁ ≠ e₂ := fun h => hu_ne (congrArg (fun x : ArcVert f ω => x.1.1) h)
        have he1_f1 : e₁ ≠ f₁ u₁ := by
          intro h
          have hpart : u₁.1.1 = v.1 := congrArg (fun z : BaseVert f => z.1)
            ((congrArg (fun x : ArcVert f ω => x.1.1) h).trans
              (Finset.mem_filter.mp (hf₁ u₁)).2.1.symm)
          have hlt : u₁.1.1 < v.1 := e₁.2.1
          exact lt_irrefl _ (hpart ▸ hlt)
        have he1_f2 : e₁ ≠ f₂ u₁ := by
          intro h
          have hpart : u₁.1.1 = v.1 := congrArg (fun z : BaseVert f => z.1)
            ((congrArg (fun x : ArcVert f ω => x.1.1) h).trans
              (Finset.mem_filter.mp (hf₂ u₁)).2.1.symm)
          have hlt : u₁.1.1 < v.1 := e₁.2.1
          exact lt_irrefl _ (hpart ▸ hlt)
        have he2_f1 : e₂ ≠ f₁ u₁ := by
          intro h
          have hpart : u₂.1.1 = v.1 := congrArg (fun z : BaseVert f => z.1)
            ((congrArg (fun x : ArcVert f ω => x.1.1) h).trans
              (Finset.mem_filter.mp (hf₁ u₁)).2.1.symm)
          have hlt : u₂.1.1 < v.1 := e₂.2.1
          exact lt_irrefl _ (hpart ▸ hlt)
        have he2_f2 : e₂ ≠ f₂ u₁ := by
          intro h
          have hpart : u₂.1.1 = v.1 := congrArg (fun z : BaseVert f => z.1)
            ((congrArg (fun x : ArcVert f ω => x.1.1) h).trans
              (Finset.mem_filter.mp (hf₂ u₁)).2.1.symm)
          have hlt : u₂.1.1 < v.1 := e₂.2.1
          exact lt_irrefl _ (hpart ▸ hlt)
        have hadj1 : H.Adj e₁ (f₁ u₁) := (Finset.mem_filter.mp (hf₁ u₁)).2.2
        have hadj2 : H.Adj (f₁ u₁) e₂ := by
          rw [hf1_eq]
          exact ((Finset.mem_filter.mp (hf₁ u₂)).2.2).symm
        have hadj3 : H.Adj e₂ (f₂ u₁) := by
          rw [hf2_eq]
          exact (Finset.mem_filter.mp (hf₂ u₂)).2.2
        have hadj4 : H.Adj (f₂ u₁) e₁ := ((Finset.mem_filter.mp (hf₂ u₁)).2.2).symm
        exact hc4 e₁ (f₁ u₁) e₂ (f₂ u₁)
          he1_f1 he12 he1_f2 he2_f1.symm (hne u₁) he2_f2 ⟨hadj1, hadj2, hadj3, hadj4⟩
      have hcard_img : inQ.attach.card ≤ (outG ×ˢ outG).card := by
        rw [← Finset.card_image_of_injective _ hpair_inj]
        refine Finset.card_le_card fun p hp => ?_
        rcases Finset.mem_image.mp hp with ⟨u, _, rfl⟩
        exact hpair_mem u
      rw [Finset.card_attach, Finset.card_product] at hcard_img
      exact hcard_img.trans (Nat.mul_le_mul houtG_le houtG_le)
    have hcov : Finset.univ.filter (Q.Adj v) ⊆ outQ ∪ inQ := by
      intro w hw
      rcases (Finset.mem_filter.mp hw).2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    calc
      (Finset.univ.filter (Q.Adj v)).card
          ≤ (outQ ∪ inQ).card := Finset.card_le_card hcov
      _ ≤ outQ.card + inQ.card := Finset.card_union_le _ _
      _ ≤ dParam f + dParam f * dParam f := Nat.add_le_add houtQ_le hinQ_le
  have hQmin5 : ∀ S : Finset (BaseVert f), S.Nonempty →
      ∃ v ∈ S, (S.filter (Q.Adj v)).card ≤ 5 := by
    intro S hSne
    refine sub_base_min_deg_le_five f hnotBad2 Q hQsub hSne fun v _ => ?_
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))).trans (hQmax v)
  obtain ⟨c6, hc6⟩ := six_color_of_min_deg_five Q hQmin5
    (Fintype.card (BaseVert f)) Finset.univ Finset.card_univ
  let pairCol : BaseVert f → { s : Finset (Fin 4) // s.card = 2 } := fun v => sixToTwoSet (c6 v)
  have hpair_proper : ∀ {u v : BaseVert f}, Q.Adj u v → pairCol u ≠ pairCol v := by
    intro u v hadj heq
    exact hc6 u (Finset.mem_univ _) v (Finset.mem_univ _) hadj (sixToTwoSet_injective heq)
  let rankE : ArcVert f ω → ℕ := fun e => CParam f - e.1.1.1.val
  have hwf : WellFounded (fun a b : ArcVert f ω => rankE a < rankE b) :=
    InvImage.wf rankE wellFounded_lt
  let stepFn : ∀ e : ArcVert f ω,
      (∀ e' : ArcVert f ω, rankE e' < rankE e → { c : Fin 4 // c ∈ (pairCol e'.1.1).1 }) →
      { c : Fin 4 // c ∈ (pairCol e.1.1).1 } := fun e rec =>
    if hq : 2 ≤ (outH e).card then
      have hQadj : Q.Adj e.1.1 e.1.2 := Or.inl ⟨e.2, hq⟩
      have hne_set : (pairCol e.1.1).1 ≠ (pairCol e.1.2).1 :=
        fun h => hpair_proper hQadj (Subtype.ext h)
      have hdiff_ne : ((pairCol e.1.1).1 \ (pairCol e.1.2).1).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : (pairCol e.1.1).1 ⊆ (pairCol e.1.2).1 :=
          Finset.sdiff_eq_empty_iff_subset.mp hemp
        have heq_set := Finset.eq_of_subset_of_card_le hsub
          (by rw [(pairCol e.1.1).2, (pairCol e.1.2).2])
        exact hne_set heq_set
      ⟨Classical.choose hdiff_ne,
        (Finset.mem_sdiff.mp (Classical.choose_spec hdiff_ne)).1⟩
    else
      let used : Finset (Fin 4) := (outH e).attach.image fun (e' : { x // x ∈ outH e }) =>
        have hlt_part : e.1.1.1.val < e'.1.1.1.1.val := by
          have hv : e.1.2 = e'.1.1.1 := (Finset.mem_filter.mp e'.2).2.1
          have hv1 : e.1.2.1 = e'.1.1.1.1 := congrArg Sigma.fst hv
          have h0 : e.1.1.1 < e.1.2.1 := e.2.1
          exact hv1 ▸ h0
        have hlt_rank : rankE e'.1 < rankE e := by
          dsimp [rankE]
          have := e'.1.1.1.1.isLt
          omega
        (rec e'.1 hlt_rank).1
      have hused_lt : used.card < ((pairCol e.1.1).1).card := by
        rw [(pairCol e.1.1).2]
        have h1 : used.card ≤ (outH e).attach.card := Finset.card_image_le
        rw [Finset.card_attach] at h1
        omega
      have hdiff_ne : ((pairCol e.1.1).1 \ used).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : (pairCol e.1.1).1 ⊆ used := Finset.sdiff_eq_empty_iff_subset.mp hemp
        exact not_le_of_gt hused_lt (Finset.card_le_card hsub)
      ⟨Classical.choose hdiff_ne,
        (Finset.mem_sdiff.mp (Classical.choose_spec hdiff_ne)).1⟩
  let arcCol : ∀ e : ArcVert f ω, { c : Fin 4 // c ∈ (pairCol e.1.1).1 } :=
    WellFounded.fix hwf stepFn
  have harcCol_ne : ∀ {a b : ArcVert f ω}, b ∈ outH a → (arcCol a).1 ≠ (arcCol b).1 := by
    intro a b hb
    have harc_eq : arcCol a = stepFn a (fun e' _ => arcCol e') :=
      WellFounded.fix_eq hwf stepFn a
    by_cases hq : 2 ≤ (outH a).card
    · have hval : (arcCol a).1 ∈ (pairCol a.1.1).1 \ (pairCol a.1.2).1 := by
        rw [harc_eq]
        dsimp only [stepFn]
        rw [dif_pos hq]
        exact Classical.choose_spec _
      intro heq
      have hb_mem : (arcCol b).1 ∈ (pairCol a.1.2).1 := by
        have hv : a.1.2 = b.1.1 := (Finset.mem_filter.mp hb).2.1
        rw [hv]
        exact (arcCol b).2
      exact (Finset.mem_sdiff.mp hval).2 (heq ▸ hb_mem)
    · have hval : (arcCol a).1 ∈ (pairCol a.1.1).1 \
          ((outH a).attach.image fun (e' : { x // x ∈ outH a }) => (arcCol e'.1).1) := by
        rw [harc_eq]
        dsimp only [stepFn]
        rw [dif_neg hq]
        exact Classical.choose_spec _
      intro heq
      apply (Finset.mem_sdiff.mp hval).2
      exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_attach _ _, heq.symm⟩
  refine ⟨SimpleGraph.Coloring.mk (fun e => (arcCol e).1) ?_⟩
  intro a b hadj
  rcases hHsub hadj with hdir | hdir
  · exact harcCol_ne (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdir, hadj⟩)
  · exact (harcCol_ne (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdir, hadj.symm⟩)).symm

end Construction

end OMAErdos108

theorem OMA.disproof : ¬ (type_of% @Erdos108.erdos_108) := by
  classical
  intro h108
  obtain ⟨f, hf⟩ := h108 5 (by omega) 5 (by omega)
  obtain ⟨ω, hnotBad1, hnotBad2⟩ := OMAErdos108.exists_good_omega f
  let E := OMAErdos108.ArcVert f ω
  let LG := OMAErdos108.lineGraph f ω
  let Vu := ULift E
  let LGu : SimpleGraph Vu := {
    Adj := fun x y => LG.Adj x.down y.down
    symm := ⟨fun _ _ h => LG.adj_symm h⟩
    loopless := ⟨fun x h => LG.loopless.irrefl x.down h⟩
  }
  have hVu_ne : Nonempty Vu :=
    let ⟨e0⟩ := OMAErdos108.arcVert_nonempty f ω
    ⟨ULift.up e0⟩
  have hnot_col_u : ¬ LGu.Colorable (OMAErdos108.k0 f) := by
    rintro ⟨cu⟩
    apply OMAErdos108.not_lineGraph_colorable f hnotBad1
    refine ⟨SimpleGraph.Coloring.mk (fun e => cu (ULift.up e)) ?_⟩
    intro a b hadj
    exact cu.valid hadj
  have hchro_u : (f : ℕ∞) ≤ LGu.chromaticNumber := by
    have hk1_le : ((OMAErdos108.k0 f + 1 : ℕ) : ℕ∞) ≤ LGu.chromaticNumber := by
      rw [SimpleGraph.le_chromaticNumber_iff_not_colorable (by omega)]
      simpa using hnot_col_u
    have hfk : (f : ℕ∞) ≤ ((OMAErdos108.k0 f + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast (le_max_left f 1).trans (Nat.le_succ _)
    exact hfk.trans hk1_le
  obtain ⟨Hu, hgirth, hchroH⟩ := hf Vu LGu hVu_ne hchro_u
  let H : SimpleGraph E := {
    Adj := fun a b => Hu.Adj (ULift.up a) (ULift.up b)
    symm := ⟨fun _ _ h => Hu.adj_symm h⟩
    loopless := ⟨fun a h => Hu.loopless.irrefl (ULift.up a) h⟩
  }
  have hHsub : H ≤ LG := fun a b h => Hu.adj_sub h
  have hc4 : ∀ e₁ e₂ e₃ e₄ : E,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₁ ≠ e₄ → e₂ ≠ e₃ → e₂ ≠ e₄ → e₃ ≠ e₄ →
      ¬ (H.Adj e₁ e₂ ∧ H.Adj e₂ e₃ ∧ H.Adj e₃ e₄ ∧ H.Adj e₄ e₁) := by
    intro e₁ e₂ e₃ e₄ h12 h13 h14 h23 h24 h34 ⟨a12, a23, a34, a41⟩
    let x₁ : Hu.verts := ⟨ULift.up e₁, Hu.edge_vert a12⟩
    let x₂ : Hu.verts := ⟨ULift.up e₂, Hu.edge_vert a23⟩
    let x₃ : Hu.verts := ⟨ULift.up e₃, Hu.edge_vert a34⟩
    let x₄ : Hu.verts := ⟨ULift.up e₄, Hu.edge_vert a41⟩
    have hx12 : x₁ ≠ x₂ := fun h => h12 (ULift.up.inj (congrArg Subtype.val h))
    have hx13 : x₁ ≠ x₃ := fun h => h13 (ULift.up.inj (congrArg Subtype.val h))
    have hx14 : x₁ ≠ x₄ := fun h => h14 (ULift.up.inj (congrArg Subtype.val h))
    have hx23 : x₂ ≠ x₃ := fun h => h23 (ULift.up.inj (congrArg Subtype.val h))
    have hx24 : x₂ ≠ x₄ := fun h => h24 (ULift.up.inj (congrArg Subtype.val h))
    have hx34 : x₃ ≠ x₄ := fun h => h34 (ULift.up.inj (congrArg Subtype.val h))
    have ha12 : Hu.coe.Adj x₁ x₂ := a12
    have ha23 : Hu.coe.Adj x₂ x₃ := a23
    have ha34 : Hu.coe.Adj x₃ x₄ := a34
    have ha41 : Hu.coe.Adj x₄ x₁ := a41
    let w : Hu.coe.Walk x₁ x₁ := .cons ha12 (.cons ha23 (.cons ha34 (.cons ha41 .nil)))
    have hw : w.IsCycle := by
      refine { isCircuit := { edges_nodup := ?_, ne_nil := by simp [w] }, support_nodup := ?_ }
      · simp [w, hx12, hx13, hx14, hx23, hx24, hx34,
          hx12.symm, hx13.symm, hx14.symm]
      · simp [w, hx12.symm, hx13.symm, hx14.symm, hx23, hx24, hx34]
    have hg_le : Hu.coe.girth ≤ 4 := by
      simpa [w] using SimpleGraph.girth_le_length hw
    omega
  have hcol4 : H.Colorable 4 :=
    OMAErdos108.c4_free_four_colorable f hnotBad2 H hHsub hc4
  rcases hcol4 with ⟨c4⟩
  have hHu_col4 : Hu.coe.Colorable 4 := by
    refine ⟨SimpleGraph.Coloring.mk (fun x => c4 x.1.down) ?_⟩
    intro x y hadj
    exact c4.valid hadj
  have hchro_le4 : Hu.coe.chromaticNumber ≤ (4 : ℕ∞) :=
    SimpleGraph.chromaticNumber_le_iff_colorable.mpr hHu_col4
  have h5_le_4 : (5 : ℕ∞) ≤ (4 : ℕ∞) := hchroH.trans hchro_le4
  norm_cast at h5_le_4
