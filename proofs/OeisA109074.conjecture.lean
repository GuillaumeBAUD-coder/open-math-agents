import FormalConjectures.OEIS.«109074»
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.FractionRing

section

namespace OeisA109074.Partial

/-- 从给定前缀和出发，检查读入左半行时前缀和是否始终落在 0 或 1。 -/
def prefixOK : Int → List Int → Bool
  | _, [] => true
  | s, x :: xs =>
    let t := s + x
    (t == 0 || t == 1) && prefixOK t xs

private theorem valid_sum (s : Int) (xs : List Int)
    (h : isAsmLineAux s xs = true) : s + xs.sum = 1 := by
  induction xs generalizing s with
  | nil => simpa [isAsmLineAux] using h
  | cons x xs ih =>
    have h' := (Bool.and_eq_true_iff.mp h).2
    have := ih (s + x) h'
    simp only [List.sum_cons]
    omega

private theorem check_append (s : Int) (xs ys : List Int) :
    isAsmLineAux s (xs ++ ys) =
      (prefixOK s xs && isAsmLineAux (s + xs.sum) ys) := by
  induction xs generalizing s with
  | nil => simp [prefixOK]
  | cons x xs ih =>
    simp [prefixOK, isAsmLineAux, ih, Int.add_assoc, Bool.and_assoc]

/-- 镜像后，新前缀和等于原前缀和的补数 1-s。 -/
private theorem check_reflection (xs : List Int) (s : Int) (hs : s = 0 ∨ s = 1)
    (h : prefixOK s xs = true) (tail : List Int) :
    isAsmLineAux (1 - (s + xs.sum)) (xs.reverse ++ tail) =
      isAsmLineAux (1 - s) tail := by
  induction xs generalizing s tail with
  | nil => simp
  | cons x xs ih =>
    have ⟨hx, hxs⟩ := Bool.and_eq_true_iff.mp h
    have hx' : s + x = 0 ∨ s + x = 1 := by simpa using hx
    simp only [List.sum_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    rw [← Int.add_assoc, ih (s + x) hx' hxs (x :: tail)]
    have he : 1 - (s + x) + x = 1 - s := by omega
    simp only [isAsmLineAux, he]
    rcases hs with hs | hs <;> simp [hs]

private theorem last_prefix (s : Int) (xs : List Int) (hs : s = 0 ∨ s = 1)
    (h : prefixOK s xs = true) : s + xs.sum = 0 ∨ s + xs.sum = 1 := by
  induction xs generalizing s with
  | nil => simpa using hs
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := Bool.and_eq_true_iff.mp h
    simpa [Int.add_assoc] using ih (s + x) (by simpa using hx) hxs

/-- 给定左半行，合法对称行的中项唯一；前缀条件也足以构造整行。 -/
theorem symmetric_row_iff (half : List Int) (mid : Int) :
    isAsmLine (half ++ [mid] ++ half.reverse) = true ↔
      prefixOK 0 half = true ∧ mid = 1 - 2 * half.sum := by
  change isAsmLineAux 0 _ = true ↔ _
  rw [List.append_assoc, check_append, Bool.and_eq_true_iff]
  constructor
  · intro ⟨hp, hm⟩
    have he := valid_sum _ _ hm
    simp at he
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, rfl⟩
    refine ⟨hp, ?_⟩
    have hs : half.sum = 0 ∨ half.sum = 1 := by
      simpa using last_prefix 0 half (Or.inl rfl) hp
    have hr := check_reflection half 0 (Or.inl rfl) hp []
    simp [isAsmLineAux] at hr
    have he : half.sum + (1 - 2 * half.sum) = 1 - half.sum := by omega
    simp only [List.singleton_append, Int.zero_add, isAsmLineAux, he]
    rcases hs with hs | hs <;> simp_all

private theorem count_extensions (halves : List (List Int)) (s : Int) (hs : s = 0 ∨ s = 1) :
    (halves.flatMap (fun xs => [(-1 : Int) :: xs, 0 :: xs, 1 :: xs])).countP (prefixOK s) =
      halves.countP (prefixOK 0) + halves.countP (prefixOK 1) := by
  induction halves with
  | nil => simp
  | cons x xs ih =>
    rcases hs with rfl | rfl <;>
      simp [List.countP_cons, prefixOK, ih, Int.reduceNeg] <;> omega

private theorem count_halves (n : Nat) (s : Int) (hs : s = 0 ∨ s = 1) :
    (trinaryLists n).countP (prefixOK s) = 2 ^ n := by
  induction n generalizing s with
  | zero => simp [trinaryLists, List.countP_cons, prefixOK]
  | succ n ih =>
    rw [trinaryLists, count_extensions _ _ hs, ih 0 (Or.inl rfl), ih 1 (Or.inr rfl),
      Nat.pow_succ]
    omega

private theorem rows_per_half (half : List Int) :
    (([(-1 : Int), 0, 1] : List Int).filterMap fun mid =>
      let row := half ++ [mid] ++ half.reverse
      if isAsmLine row then some row else none).length =
      if prefixOK 0 half then 1 else 0 := by
  have criterion (mid : Int) : isAsmLine (half ++ mid :: half.reverse) = true ↔
      prefixOK 0 half = true ∧ mid = 1 - 2 * half.sum := by
    simpa only [List.append_assoc, List.singleton_append] using symmetric_row_iff half mid
  by_cases hp : prefixOK 0 half = true
  · have hs : half.sum = 0 ∨ half.sum = 1 := by
      simpa using last_prefix 0 half (Or.inl rfl) hp
    rcases hs with hs | hs <;>
      simp [criterion, hp, hs]
  · simp [criterion, hp]

/-- 对任意 n，上游枚举器恰好生成 2^n 个可选的对称行。 -/
theorem number_of_symmetric_rows (n : Nat) : (symAsmRows n).length = 2 ^ n := by
  rw [← count_halves n 0 (Or.inl rfl)]
  unfold symAsmRows
  induction trinaryLists n with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, rows_per_half, ih, List.countP_cons]
    omega

-- 直接用内核计算这个边界值，避免引入上游原生求值器的信任假设。
set_option maxRecDepth 4096 in
private theorem count_size_nine : b 4 = 646 := by decide +kernel

/-- 原目标在前四个下标上成立。 -/
theorem ratio_first_four (n : Nat) (hn : n ≤ 3) :
    frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ) := by
  have cases_n : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases_n with rfl | rfl | rfl | rfl
  · change frac 1 = (b 1 : ℚ) / (b 0 : ℚ)
    rw [b_1, b_0]
    decide +kernel
  · change frac 2 = (b 2 : ℚ) / (b 1 : ℚ)
    rw [b_2, b_1]
    decide +kernel
  · change frac 3 = (b 3 : ℚ) / (b 2 : ℚ)
    rw [b_3, b_2]
    decide +kernel
  · change frac 4 = (b 4 : ℚ) / (b 3 : ℚ)
    rw [count_size_nine, b_3]
    decide +kernel

private def reflectRow (half : List Int) (center : Int) :=
  half ++ center :: half.reverse

private theorem halves_length {n : Nat} {half : List Int} (h : half ∈ trinaryLists n) :
    half.length = n := by
  induction n generalizing half with
  | zero => simpa [trinaryLists] using congrArg List.length (show half = [] by simpa [trinaryLists] using h)
  | succ n ih =>
    obtain ⟨xs, hxs, hm⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp [ih hxs]

private theorem rows_for_prefix (h : List Int) :
    ([(-1 : Int), 0, 1].filterMap fun m =>
      let r := h ++ [m] ++ h.reverse
      if isAsmLine r then some r else none) =
      if prefixOK 0 h then [reflectRow h (1 - 2 * h.sum)] else [] := by
  have crit (m : Int) : isAsmLine (h ++ m :: h.reverse) = true ↔
      prefixOK 0 h = true ∧ m = 1 - 2 * h.sum := by
    simpa only [List.append_assoc, List.singleton_append] using symmetric_row_iff h m
  by_cases hp : prefixOK 0 h = true
  · have hs : h.sum = 0 ∨ h.sum = 1 := by simpa using last_prefix 0 h (Or.inl rfl) hp
    rcases hs with hs | hs <;> simp [reflectRow, crit, hp, hs]
  · simp [crit, hp]

private theorem zip_reflect (s h : List Int) (c m : Int) (hlen : s.length = h.length) :
    List.zipWith (· + ·) (reflectRow s c) (reflectRow h m) =
      reflectRow (List.zipWith (· + ·) s h) (c + m) := by
  simp only [reflectRow, List.zipWith_append hlen, List.zipWith_cons_cons, List.reverse_zipWith hlen]

private theorem all_reflect (p : Int → Bool) (s : List Int) (c : Int) :
    (reflectRow s c).all p = (s.all p && p c) := by
  simp [reflectRow, Bool.and_left_comm, Bool.and_comm]

private theorem fold_same_on {xs : List α} {f g : β → α → β}
    (h : ∀ x ∈ xs, ∀ acc, f acc x = g acc x) (acc : β) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

/-- 半宽转移计数。s 记录左侧各列的部分和，c 记录中心列的部分和。
    合法行把 c 翻转，并且其左半行的和必须等于旧的 c。 -/
def countHalf (n : Nat) : Nat → List Int → Int → Nat
  | 0, s, c => if s.all (· == 1) && c == 1 then 1 else 0
  | k + 1, s, c =>
    (trinaryLists n).foldl (fun acc h =>
      let t := List.zipWith (· + ·) s h
      if prefixOK 0 h && h.sum == c && t.all (fun x => x == 0 || x == 1)
      then acc + countHalf n k t (1 - c) else acc) 0

private theorem count_reflect (n k : Nat) (s : List Int) (c : Int)
    (hlen : s.length = n) (hc : c = 0 ∨ c = 1) :
    countVsasmRows (symAsmRows n) k (reflectRow s c) = countHalf n k s c := by
  induction k generalizing s c with
  | zero => simp [countVsasmRows, countHalf, all_reflect]
  | succ k ih =>
    rw [countVsasmRows, countHalf]
    conv => lhs; arg 3; unfold symAsmRows
    rw [List.foldl_flatMap]
    apply fold_same_on
    intro h hm acc
    have hlen' : s.length = h.length := hlen.trans (halves_length hm).symm
    have ht : (List.zipWith (· + ·) s h).length = n := by
      simp [hlen, halves_length hm]
    rw [rows_for_prefix]
    by_cases hp : prefixOK 0 h = true
    · have hs : h.sum = 0 ∨ h.sum = 1 := by simpa using last_prefix 0 h (Or.inl rfl) hp
      simp only [hp, ite_true, List.foldl_cons, List.foldl_nil, zip_reflect _ _ _ _ hlen',
        all_reflect]
      rcases hc with rfl | rfl <;> rcases hs with hs | hs <;>
        simp [hs, ih _ _ ht]
    · simp [hp]

/-- 所有规模的矩阵总数都由半宽列状态上的递推精确给出。 -/
theorem count_by_half_columns (n : Nat) :
    b n = countHalf n (2*n+1) (List.replicate n 0) 0 := by
  have h : reflectRow (List.replicate n 0) 0 = List.replicate (2*n+1) 0 := by
    unfold reflectRow
    rw [List.reverse_replicate]
    change List.replicate n (0 : Int) ++ List.replicate (n+1) 0 = _
    rw [List.replicate_append_replicate]
    congr 1 <;> omega
  unfold b
  rw [← h]
  exact count_reflect _ _ _ _ (by simp) (Or.inl rfl)

private theorem trinary_mem (xs : List Int)
    (hd : ∀ x ∈ xs, x = -1 ∨ x = 0 ∨ x = 1) : xs ∈ trinaryLists xs.length := by
  induction xs with
  | nil => simp [trinaryLists]
  | cons x xs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨xs, ih (fun y hy => hd y (by simp [hy])), ?_⟩
    rcases hd x (by simp) with rfl | rfl | rfl <;> simp

private theorem fold_at_least {xs : List α} {f : Nat → α → Nat} {x : α}
    (inc : ∀ a y, a ≤ f a y) (hx : x ∈ xs) (bound : Nat)
    (hit : ∀ a, bound ≤ f a x) (a : Nat) : bound ≤ xs.foldl f a := by
  have mono (ys : List α) (v : Nat) : v ≤ ys.foldl f v := by
    induction ys generalizing v with
    | nil => exact Nat.le_refl _
    | cons y ys ih => exact Nat.le_trans (inc v y) (ih _)
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Nat.le_trans (hit a) (mono ys _)
    · exact ih hm _

private theorem positive_step {n k : Nat} {s h : List Int} {c : Int}
    (hm : h ∈ trinaryLists n) (hp : prefixOK 0 h = true) (hs : h.sum = c)
    (hb : (List.zipWith (· + ·) s h).all (fun x => x == 0 || x == 1) = true)
    (ht : 0 < countHalf n k (List.zipWith (· + ·) s h) (1 - c)) :
    0 < countHalf n (k+1) s c := by
  rw [countHalf]
  apply fold_at_least (x := h) (bound := 1) _ hm
  · intro a
    simp [hp, hs, hb]
    omega
  · intro a y
    dsimp
    split <;> omega

private theorem prefix_zeros (m : Nat) (s : Int) (hs : s = 0 ∨ s = 1) (xs : List Int) :
    prefixOK s (List.replicate m 0 ++ xs) = prefixOK s xs := by
  induction m with
  | zero => simp
  | succ m ih => rcases hs with rfl | rfl <;> simp [List.replicate_succ, prefixOK, ih]

-- 每次选两行：先保持左半边的列和，再把一个 0 变成 1。
private theorem positive_completion (z a : Nat) :
    0 < countHalf (z+a) (2*z+1) (List.replicate z 0 ++ List.replicate a 1) 0 := by
  let bits := fun (x : Int) => x == 0 || x == 1
  have binary (u v : Nat) : (List.replicate u (0 : Int) ++ List.replicate v 1).all bits = true := by
    simp [bits]
  have zeros (m : Nat) : (List.replicate m (0 : Int)).sum = 0 := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, ih]
  have stay (u v : Nat) : List.zipWith (· + ·)
      (List.replicate u (0 : Int) ++ List.replicate v 1)
      (List.replicate (u+v) 0) = List.replicate u 0 ++ List.replicate v 1 := by
    rw [← List.replicate_append_replicate (n := u) (m := v)]
    rw [List.zipWith_append (by simp)]
    simp
  apply positive_step (h := List.replicate (z+a) 0)
  · simpa using trinary_mem (List.replicate (z+a) 0) (by simp [List.mem_replicate])
  · simpa [prefixOK] using prefix_zeros (z+a) 0 (Or.inl rfl) []
  · apply zeros
  · simpa only [stay] using binary z a
  rw [stay]
  change 0 < countHalf (z+a) (2*z) _ 1
  cases z with
  | zero => simp [countHalf]
  | succ z =>
    let h := List.replicate z (0 : Int) ++ 1 :: List.replicate a 0
    have state : List.replicate (z+1) (0 : Int) ++ List.replicate a 1 =
        List.replicate z 0 ++ 0 :: List.replicate a 1 := by
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    have next : List.zipWith (· + ·) (List.replicate (z+1) 0 ++ List.replicate a 1) h =
        List.replicate z 0 ++ List.replicate (a+1) 1 := by
      rw [state]
      simp [h, List.zipWith_append, List.replicate_succ]
    rw [show 2*(z+1) = (2*z+1)+1 by omega]
    apply positive_step (h := h)
    · have hh := trinary_mem h (by simp [h, List.mem_replicate]; grind)
      simpa [h, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using hh
    · rw [show h = _ from rfl, prefix_zeros z 0 (Or.inl rfl)]
      simp only [prefixOK, Int.zero_add]
      have ht := prefix_zeros a 1 (Or.inr rfl) []
      simpa [prefixOK] using ht
    · simp [h, zeros]
    · simpa only [next] using binary z (a+1)
    · rw [next]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using positive_completion z (a+1)
termination_by z

/-- 原题比值的分母在每个自然数下标都严格为正。 -/
theorem count_positive (n : Nat) : 0 < b n := by
  rw [count_by_half_columns]
  simpa using positive_completion n 0

namespace SixVertex

/-- 相同的两条入边只有一种出边，权为 a；不同的入边可以直行或交换。 -/
structure Weights (R : Type) where
  a : R
  b : R
  c : R

variable {R : Type} [Lean.Grind.CommRing R]

def scatter (w : Weights R) (f : Bool → Bool → R) (i j : Bool) : R :=
  if i = j then w.a * f i j else w.b * f i j + w.c * f j i

/-- 乘法谱参数 x/y 的六顶点权；清去公共分母，使局部恒等式成为多项式恒等式。 -/
def spectral (q x y : R) : Weights R :=
  ⟨q*q*x*x - y*y, q*(x*x - y*y), (q*q - 1)*x*y⟩

def act12 (w : Weights R) (f : Bool → Bool → Bool → R) (i j k : Bool) : R :=
  scatter w (fun a b => f a b k) i j

def act13 (w : Weights R) (f : Bool → Bool → Bool → R) (i j k : Bool) : R :=
  scatter w (fun a b => f a j b) i k

def act23 (w : Weights R) (f : Bool → Bool → Bool → R) (i j k : Bool) : R :=
  scatter w (fun a b => f i a b) j k

theorem yang_baxter (q x y z : R) (f : Bool → Bool → Bool → R) :
    act12 (spectral q x y) (act13 (spectral q x z) (act23 (spectral q y z) f)) =
    act23 (spectral q y z) (act13 (spectral q x z) (act12 (spectral q x y) f)) := by
  funext i j k
  cases i <;> cases j <;> cases k <;>
    simp [act12, act13, act23, scatter, spectral] <;> grind

/-- 对角反射边界，两种箭头方向使用不同的权。 -/
def boundary (d x : R) (i : Bool) : R := if i then d - x*x else d*x*x - 1

theorem reflection (q d x y : R) (f : Bool → Bool → R) :
    scatter (spectral q x y)
      (fun i j => boundary d x i * scatter (spectral q (x*y) 1)
        (fun a b => boundary d y b * f a b) i j) =
    (fun i j => boundary d y j * scatter (spectral q (x*y) 1)
      (fun a b => boundary d x a * scatter (spectral q x y) f a b) i j) := by
  funext i j
  cases i <;> cases j <;> simp [scatter, spectral, boundary] <;> grind

theorem equal_weights (q : R) (hq : q*q + 1 = q) :
    spectral q q 1 = ⟨(q*q - 1)*q, (q*q - 1)*q, (q*q - 1)*q⟩ := by
  unfold spectral
  congr 1 <;> grind

/-- 两条谱线取相同参数时，只留下交换两条边的局部配置。 -/
theorem freeze_crossing (q x : R) (f : Bool → Bool → R) (i j : Bool) :
    scatter (spectral q x x) f i j = (q*q - 1)*x*x * f j i := by
  cases i <;> cases j <;> simp [scatter, spectral] <;> grind

/-- 固定反射方向时只保留一个边界权；它仍带有公共归一化因子。 -/
theorem fixed_reflection (x : R) (i : Bool) :
    boundary (x*x) x i = if i then 0 else x*x*x*x - 1 := by
  cases i <;> simp [boundary] <;> grind

private def bit (x : Bool) : Int := if x then 1 else 0

/-- 固定上边各列的状态和本行各格的增量。沿行收缩 R 矩阵，
    对未指定的内部水平箭头求和，只保留给定的右端箭头。 -/
def strip (w : Weights R) : List Bool → List Int → Bool → Bool → R
  | [], [], right, left => if left = right then 1 else 0
  | s :: ss, h :: hs, right, left =>
    scatter w (fun j t => if bit t = bit s + h then strip w ss hs right j else 0) left s
  | _, _, _, _ => 0

private def binary (x : Int) := x == 0 || x == 1

/-- 单位权下一行的配分函数恰是半宽递推的合法性检验。水平箭头的
    补数是当前行的前缀和，列状态是垂直箭头。 -/
theorem strip_unit (s : List Bool) (h : List Int) (right left : Bool)
    (hlen : s.length = h.length) :
    strip (⟨1, 1, 1⟩ : Weights Int) s h right left =
      if prefixOK (1 - bit left) h &&
          (1 - bit left + h.sum == 1 - bit right) &&
          (List.zipWith (· + ·) (s.map bit) h).all binary
      then 1 else 0 := by
  induction s generalizing h left with
  | nil =>
    cases h <;> simp_all
    cases left <;> cases right <;> decide
  | cons v vs ih =>
    cases h with
    | nil => simp at hlen
    | cons x xs =>
      have len : vs.length = xs.length := by simpa using hlen
      by_cases hm : x = -1
      · subst x
        cases left <;> cases v <;>
          simp [strip, scatter, bit, prefixOK, binary, ih xs _ len, ← Int.add_assoc]
      · by_cases hz : x = 0
        · subst x
          cases left <;> cases v <;>
            simp [strip, scatter, bit, prefixOK, binary, ih xs _ len]
        · by_cases hp : x = 1
          · subst x
            cases left <;> cases v <;>
              simp [strip, scatter, bit, prefixOK, binary, ih xs _ len]
          · have ha : 1 + x ≠ 0 := by omega
            have hb : 1 + x ≠ 1 := by omega
            cases left <;> cases v <;>
              simp [strip, scatter, bit, prefixOK, binary, hz, hp, ha, hb,
                Ne.symm hz, Ne.symm hp, Ne.symm ha, Ne.symm hb]

/-- 一列中两行的交点，固定该列上下端的箭头；f 接收右侧两条水平边。 -/
def twoCrossings (q x y z : R) (top bottom : Bool) (f : Bool → Bool → R) :
    Bool → Bool → R := fun i j =>
  act13 (spectral q x z) (act23 (spectral q y z)
    (fun a b k => if k = bottom then f a b else 0)) i j top

private theorem slide_one (q x y z : R) (top bottom : Bool) (f : Bool → Bool → R) :
    scatter (spectral q x y) (twoCrossings q x y z top bottom f) =
    (fun i j => twoCrossings q y x z top bottom
      (fun b a => scatter (spectral q x y) f a b) j i) := by
  funext i j
  have h := congrFun (congrFun (congrFun (yang_baxter q x y z
    (fun a b k => if k = bottom then f a b else 0)) i) j) top
  apply h.trans
  cases top <;> cases bottom <;> cases i <;> cases j <;>
    simp [twoCrossings, act23, act13, act12, scatter] <;> grind

/-- 任意列宽的两行条带，各列可有独立谱参数以及任意固定的上下边界。 -/
def twoRows (q x y : R) : List (R × Bool × Bool) → (Bool → Bool → R) → Bool → Bool → R
  | [], f => f
  | (z, top, bottom) :: cols, f =>
    twoCrossings q x y z top bottom (twoRows q x y cols f)

theorem slide_across_rows (q x y : R) (cols : List (R × Bool × Bool))
    (f : Bool → Bool → R) :
    scatter (spectral q x y) (twoRows q x y cols f) =
      fun i j => twoRows q y x cols (fun b a => scatter (spectral q x y) f a b) j i := by
  induction cols with
  | nil => rfl
  | cons col cols ih =>
    obtain ⟨z, top, bottom⟩ := col
    simp only [twoRows, slide_one, ih]

end SixVertex

end OeisA109074.Partial

end

section

namespace OeisA109074.Partial.Interlace

def weightSum (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

private theorem weight_flatMap (xs : List α) (g : α → List β) (f : β → Nat) :
    weightSum (xs.flatMap g) f = weightSum xs (fun x => weightSum (g x) f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [weightSum, List.sum_append]

private theorem weight_congr (xs : List α) (f g : α → Nat)
    (he : ∀ x ∈ xs, f x = g x) : weightSum xs f = weightSum xs g := by
  unfold weightSum
  exact congrArg List.sum (List.map_congr_left he)

def bit (x : Bool) : Int := if x then 1 else 0

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).flatMap fun xs => [false :: xs, true :: xs]

def isBit (x : Int) := x == 0 || x == 1

private def increase (s : List Bool) (h : List Int) := List.zipWith (· + ·) (s.map bit) h

def difference (s t : List Bool) := List.zipWith (· - ·) (t.map bit) (s.map bit)

/-- 换元 t=s+h：逐项累加的三值行增量与下一行的二值列状态一一对应。 -/
theorem reindex (s : List Bool) (f : List Int → List Int → Nat) :
    weightSum (trinaryLists s.length)
      (fun h => if (increase s h).all isBit then f h (increase s h) else 0) =
      weightSum (words s.length) (fun t => f (difference s t) (t.map bit)) := by
  induction s generalizing f with
  | nil => simp [weightSum, trinaryLists, words, increase, difference]
  | cons v s ih =>
    simp only [List.length_cons, trinaryLists, words, weight_flatMap]
    cases v with
    | false =>
      let g := fun h t => f (0 :: h) (0 :: t) + f (1 :: h) (1 :: t)
      calc
        _ = weightSum (trinaryLists s.length) (fun h =>
            if (increase s h).all isBit then g h (increase s h) else 0) := by
          apply weight_congr
          intro h _
          cases hc : (increase s h).all isBit <;> simp_all [increase, bit, isBit, weightSum, g] <;> grind
        _ = _ := ih g
        _ = _ := by
          apply weight_congr
          intro t _
          simp [g, weightSum, difference, bit]
    | true =>
      let g := fun h t => f ((-1) :: h) (0 :: t) + f (0 :: h) (1 :: t)
      calc
        _ = weightSum (trinaryLists s.length) (fun h =>
            if (increase s h).all isBit then g h (increase s h) else 0) := by
          apply weight_congr
          intro h _
          cases hc : (increase s h).all isBit <;> simp_all [increase, bit, isBit, weightSum, g] <;> grind
        _ = _ := ih g
        _ = _ := by
          apply weight_congr
          intro t _
          simp [g, weightSum, difference, bit]

private theorem fold_weight (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun z x => z + f x) a = a + weightSum xs f := by
  induction xs generalizing a with
  | nil => simp [weightSum]
  | cons x xs ih => simp [weightSum, ih, Nat.add_assoc]

private theorem words_length {n : Nat} {t : List Bool} (h : t ∈ words n) : t.length = n := by
  induction n generalizing t with
  | zero => simpa [words] using congrArg List.length (show t = [] by simpa [words] using h)
  | succ n ih =>
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [ih hs]

/-- 前缀差属于 {0,1}，使两组粒子交错；初末前缀差通过参数给定。 -/
def admissible (p e : Int) (s t : List Bool) : Bool :=
  let h := difference s t
  prefixOK p h && p + h.sum == e

def walk (n : Nat) : Nat → List Bool → Int → Nat
  | 0, s, c => if s.all id && c == 1 then 1 else 0
  | k+1, s, c => weightSum (words n) (fun t =>
      if admissible 0 c s t then walk n k t (1-c) else 0)

theorem countHalf_walk (n k : Nat) (s : List Bool) (hs : s.length = n) (c : Int) :
    countHalf n k (s.map bit) c = walk n k s c := by
  induction k generalizing s c with
  | zero =>
    have h : (s.map bit).all (· == 1) = s.all id := by
      clear hs
      induction s with
      | nil => rfl
      | cons x xs ih =>
        cases x <;> simp_all [bit]
    simp [countHalf, walk, h]
  | succ k ih =>
    subst n
    let f := fun (h v : List Int) =>
      if prefixOK 0 h && h.sum == c then countHalf s.length k v (1-c) else 0
    have fold_form : countHalf s.length (k+1) (s.map bit) c =
        weightSum (trinaryLists s.length) (fun h =>
          if (increase s h).all isBit then f h (increase s h) else 0) := by
      unfold countHalf
      rw [← Nat.zero_add (weightSum ..), ← fold_weight]
      congr 1
      funext a h
      change (if prefixOK 0 h && h.sum == c && (increase s h).all isBit
        then a + countHalf _ _ _ _ else a) = _
      cases ha : (increase s h).all isBit <;>
        cases hb : (prefixOK 0 h && h.sum == c) <;> simp_all [f, increase]
    rw [fold_form, reindex, walk]
    apply weight_congr
    intro t ht
    simp [f, admissible, ih _ (words_length ht)]

theorem count_as_interlacing_walk (n : Nat) :
    b n = walk n (2*n+1) (List.replicate n false) 0 := by
  rw [count_by_half_columns, ← countHalf_walk _ _ _ (by simp)]
  simp [bit]

private theorem weight_add (xs : List α) (f g : α → Nat) :
    weightSum xs (fun x => f x + g x) = weightSum xs f + weightSum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [weightSum]; omega

theorem word_sum (n : Nat) (f : List Bool → Nat) :
    weightSum (words (n+1)) f =
      weightSum (words n) (fun t => f (false :: t)) +
      weightSum (words n) (fun t => f (true :: t)) := by
  rw [words, weight_flatMap, ← weight_add]
  apply weight_congr
  simp [weightSum]

private theorem weight_mul (xs : List α) (c : Nat) (f : α → Nat) :
    weightSum xs (fun x => c * f x) = c * weightSum xs f := by
  induction xs with
  | nil => simp [weightSum]
  | cons x xs ih => simp_all [weightSum, Nat.mul_add]

private theorem sum_zeros (xs : List α) : (xs.map (fun _ => 0 : α → Nat)).sum = 0 := by
  induction xs <;> simp_all

private theorem weight_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    weightSum xs (fun x => weightSum ys (f x)) =
      weightSum ys (fun y => weightSum xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [weightSum, sum_zeros]
  | cons x xs ih =>
    change weightSum ys (f x) + weightSum xs _ =
      weightSum ys (fun y => f x y + weightSum xs (fun z => f z y))
    rw [weight_add, ih]

/-- 允许给定的左端前缀差，返回单行转移的整数权（零或一）。 -/
def one (p e : Int) (s t : List Bool) : Nat :=
  if isBit p && admissible p e s t then 1 else 0

private theorem one_nil (p e : Int) :
    one p e [] [] = if isBit p && p == e then 1 else 0 := by
  simp [one, admissible, difference, prefixOK]

private theorem one_cons (p e : Int) (s t : Bool) (ss ts : List Bool) :
    one p e (s :: ss) (t :: ts) =
      if isBit p then one (p + (bit t - bit s)) e ss ts else 0 := by
  simp [one, admissible, difference, prefixOK, isBit, Int.add_assoc]
  grind

/-- 双行转移：枚举中间行 t，对两个单行转移权的积求和。 -/
def two (p q e f : Int) (s u : List Bool) : Nat :=
  weightSum (words s.length) (fun t => one p e s t * one q f t u)

theorem two_nil (p q e f : Int) : two p q e f [] [] =
    (if isBit p && p == e then 1 else 0) * (if isBit q && q == f then 1 else 0) := by
  simp [two, words, weightSum, one_nil]

theorem two_cons (p q e f : Int) (s u : Bool) (ss us : List Bool) :
    two p q e f (s :: ss) (u :: us) =
      if isBit p && isBit q then
        two (p - bit s) (q + bit u) e f ss us +
        two (p + (1 - bit s)) (q + (bit u - 1)) e f ss us
      else 0 := by
  unfold two
  rw [List.length_cons, word_sum]
  simp only [one_cons]
  cases hp : isBit p <;> cases hq : isBit q <;>
    simp [bit, weightSum, Int.sub_eq_add_neg, sum_zeros]

private theorem one_from_zero (e : Int) (s t : List Bool) (v : Nat) :
    (if admissible 0 e s t then v else 0) = one 0 e s t * v := by
  cases h : admissible 0 e s t <;> simp [one, isBit, h]

theorem walk_two_rows (n k : Nat) (s : List Bool) (hs : s.length = n) (c : Int) :
    walk n (k+2) s c = weightSum (words n)
      (fun u => two 0 0 c (1-c) s u * walk n k u c) := by
  simp only [walk, one_from_zero]
  have h : 1 - (1 - c) = c := by omega
  simp only [h, ← weight_mul]
  rw [weight_swap]
  apply weight_congr
  intro u _
  unfold two
  rw [hs, Nat.mul_comm (weightSum ..), ← weight_mul]
  apply weight_congr
  intro t _
  simp [Nat.mul_comm, Nat.mul_assoc]

theorem two_bad_start (p q e f : Int) (s u : List Bool) (h : isBit p = false) :
    two p q e f s u = 0 := by
  simp [two, one, h, weightSum, sum_zeros]

theorem two_bad_second (p q e f : Int) (s u : List Bool) (h : isBit q = false) :
    two p q e f s u = 0 := by
  simp [two, one, h, weightSum, sum_zeros]

private def project (d : Int) (v : Nat × Nat) : Nat × Nat :=
  (if isBit d then v.1 else 0, if isBit (d-1) then v.2 else 0)

/-- 第一个水平前缀和只能为 0 或 1。两个前缀和的和 d 则由上下边界
    决定，与中间行无关。每列只需一次三角矩阵乘法及投影。 -/
def columnPair (e f : Int) : List Bool → List Bool → Int → Nat × Nat
  | [], [], d => project d
      (if e == 0 && d == f then 1 else 0, if e == 1 && d-1 == f then 1 else 0)
  | s :: ss, u :: us, d =>
    let v := columnPair e f ss us (d + bit u - bit s)
    project d (if s then (v.1, v.1 + v.2) else (v.1 + v.2, v.2))
  | _, _, _ => (0, 0)

theorem two_columnPair (e f : Int) (s u : List Bool) (d : Int) (hlen : s.length = u.length) :
    two 0 d e f s u = (columnPair e f s u d).1 ∧
    two 1 (d-1) e f s u = (columnPair e f s u d).2 := by
  induction s generalizing u d with
  | nil =>
    cases u <;> simp_all
    simp [two, words, weightSum, one_nil, columnPair, project, isBit]
    grind
  | cons s ss ih =>
    cases u with
    | nil => simp at hlen
    | cons u us =>
      have he : ss.length = us.length := by simpa using hlen
      have hh := ih us (d + bit u - bit s) he
      have hn := two_bad_start (-1) (d + bit u) e f ss us (by decide)
      have ht := two_bad_start 2 (d - 1 + (bit u - 1)) e f ss us (by decide)
      cases s <;> cases u <;>
        simp only [two_cons, columnPair, project, bit, Bool.false_eq_true, ite_true,
          ite_false] at * <;> simp [isBit] at * <;> grind

/-- 每个双行系数仅需一次宽度 n 的扫描。求和范围为二值输出行。 -/
theorem walk_two_rows_columns (n k : Nat) (s : List Bool) (hs : s.length = n) (c : Int) :
    walk n (k+2) s c = weightSum (words n)
      (fun u => (columnPair c (1-c) s u 0).1 * walk n k u c) := by
  rw [walk_two_rows n k s hs c]
  apply weight_congr
  intro u hu
  rw [(two_columnPair c (1-c) s u 0 (hs.trans (words_length hu).symm)).1]

/-- 前 k 列中占据的位置数。 -/
def rank : List Bool → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | b :: bs, k+1 => b.toNat + rank bs k

/-- 第 i 个粒子（一基坐标，i 从零起算）所在的位置；缺失时返回 n+1。 -/
def position : List Bool → Nat → Nat
  | [], _ => 1
  | false :: bs, i => position bs i + 1
  | true :: _, 0 => 1
  | true :: bs, i+1 => position bs i + 1

private theorem rank_zero (s : List Bool) : rank s 0 = 0 := by cases s <;> rfl

private theorem position_le (s : List Bool) (i : Nat) : position s i ≤ s.length + 1 := by
  induction s generalizing i with
  | nil => simp [position]
  | cons v vs ih =>
    cases v <;> cases i <;> simp [position, Nat.add_le_add_right (ih _) 1]

private theorem position_pos (s : List Bool) (i : Nat) : 0 < position s i := by
  cases s with
  | nil => simp [position]
  | cons v vs => cases v <;> cases i <;> simp [position]

theorem rank_position (s : List Bool) (k i : Nat) (hk : k ≤ s.length) :
    i < rank s k ↔ position s i ≤ k := by
  induction s generalizing k i with
  | nil => simp_all [rank, position]
  | cons v vs ih =>
    cases k with
    | zero => simp [rank_zero, Nat.not_le.mpr (position_pos _ _)]
    | succ k =>
      have hj : k ≤ vs.length := by simpa using hk
      cases v <;> cases i <;> simp [rank, position, ih _ _ hj, Nat.add_comm] <;>
        first | omega | (rename_i i; have h := ih k i hj; omega)

private theorem bit_cast (v : Bool) : (v.toNat : Int) = bit v := by cases v <;> rfl

theorem one_prefix (p e : Int) (s t : List Bool) (hlen : s.length = t.length) :
    one p e s t = 1 ↔
      p + (rank t t.length : Int) - rank s s.length = e ∧
      ∀ k ≤ s.length, isBit (p + (rank t k : Int) - rank s k) = true := by
  induction s generalizing t p with
  | nil =>
    cases t <;> simp_all
    simp [one_nil, isBit]
    grind
  | cons v vs ih =>
    cases t with
    | nil => simp at hlen
    | cons w ws =>
      have hlen' : vs.length = ws.length := by simpa using hlen
      rw [one_cons]
      by_cases hp : isBit p = true
      · simp only [hp, ite_true, ih _ _ hlen', List.length_cons, rank,
          Int.natCast_add, bit_cast]
        constructor
        · rintro ⟨he, hh⟩
          refine ⟨by omega, ?_⟩
          intro k hk
          cases k with
          | zero => simpa [rank, Int.add_zero] using hp
          | succ k =>
            simp only [rank, Int.natCast_add, bit_cast]
            have hv := hh k (by omega)
            simp [isBit] at hv ⊢
            omega
        · rintro ⟨he, hh⟩
          refine ⟨by omega, ?_⟩
          intro k hk
          have h := hh (k+1) (by omega)
          simp only [rank, Int.natCast_add, bit_cast] at h
          simp [isBit] at h ⊢
          omega
      · rw [if_neg hp]
        constructor
        · intro h; omega
        · rintro ⟨_, hh⟩
          exact False.elim (hp (by simpa [rank] using hh 0 (Nat.zero_le _)))

private theorem ordered_ranks (s t : List Bool) (off : Nat) (hlen : s.length = t.length) :
    (∀ k ≤ s.length, rank t k ≤ rank s k + off) ↔
      ∀ i, position s i ≤ position t (i+off) := by
  constructor
  · intro hh i
    by_cases hc : position t (i+off) ≤ s.length
    · have hi := (rank_position t _ (i+off) (by omega)).2 (Nat.le_refl _)
      apply (rank_position s _ i hc).1
      have hj := hh _ hc
      omega
    · have hb := position_le s i
      omega
  · intro hh k hk
    apply Classical.byContradiction
    intro hn
    have hn : rank s k + off < rank t k := by omega
    have hpos := (rank_position t k (rank s k + off) (by omega)).1 hn
    have hbad := (rank_position s k (rank s k) hk).2 (Nat.le_trans (hh _) hpos)
    omega

theorem one_interlaces (e : Int) (s t : List Bool) (hlen : s.length = t.length) :
    one 0 e s t = 1 ↔
      (rank t t.length : Int) - rank s s.length = e ∧
      (∀ i, position t i ≤ position s i) ∧
      (∀ i, position s i ≤ position t (i+1)) := by
  rw [one_prefix _ _ _ _ hlen, ← ordered_ranks s t 1 hlen]
  have hr := ordered_ranks t s 0 hlen.symm
  simp only [Nat.add_zero, ← hlen] at hr
  rw [← hr]
  simp only [Int.zero_add, isBit, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨he, hh⟩
    exact ⟨he, fun k hk => by have := hh k hk; omega, fun k hk => by have := hh k hk; omega⟩
  · rintro ⟨he, hlow, hhigh⟩
    exact ⟨he, fun k hk => by have := hlow k hk; have := hhigh k hk; omega⟩

/-- 两个相邻交错约束夹住第 i 个中间粒子的位置。 -/
structure Band where
  lo : Nat
  hi : Nat
deriving DecidableEq

def particleBand (s u : List Bool) (i : Nat) : Band :=
  let preceding := match i with
    | 0 => 0
    | j+1 => position s j
  ⟨max (position u i) preceding, min (position s i) (position u (i+1))⟩

theorem two_interlaces (s t u : List Bool) (hst : s.length = t.length)
    (htu : t.length = u.length) :
    one 0 1 s t = 1 ∧ one 0 0 t u = 1 ↔
      rank t t.length = rank s s.length + 1 ∧ rank u u.length = rank t t.length ∧
      ∀ i, (particleBand s u i).lo ≤ position t i ∧
        position t i ≤ (particleBand s u i).hi := by
  rw [one_interlaces _ _ _ hst, one_interlaces _ _ _ htu]
  constructor
  · rintro ⟨⟨hcard, hts, hst'⟩, hcard', hut, htu'⟩
    refine ⟨by omega, by omega, ?_⟩
    intro i
    cases i with
    | zero => exact ⟨Nat.max_le.mpr ⟨hut 0, Nat.zero_le _⟩, Nat.le_min.mpr ⟨hts 0, htu' 0⟩⟩
    | succ j => exact ⟨Nat.max_le.mpr ⟨hut _, hst' j⟩, Nat.le_min.mpr ⟨hts _, htu' _⟩⟩
  · rintro ⟨hc, hc', h⟩
    have hlow (i : Nat) := Nat.le_trans (Nat.le_max_left ..) (h i).1
    have hprev (i : Nat) := Nat.le_trans (Nat.le_max_right ..) (h (i+1)).1
    have hhigh (i : Nat) := Nat.le_trans (h i).2 (Nat.min_le_left ..)
    have hnext (i : Nat) := Nat.le_trans (h i).2 (Nat.min_le_right ..)
    exact ⟨⟨by omega, hhigh, hprev⟩, by omega, hlow, hnext⟩

namespace Band

def width (a : Band) := a.hi + 1 - a.lo
def choices (a : Band) := List.range' a.lo a.width

/-- 严格递增选取，每个区间恰取一个整数。 -/
def suffix : List Band → Nat → Nat
  | [], _ => 1
  | a :: as, p => weightSum a.choices fun q =>
      if p < q then suffix as q else 0

def number : List Band → Nat
  | [] => 1
  | a :: as => weightSum a.choices (suffix as)

private theorem within (a : Band) {x : Nat} (h : x ∈ a.choices) : a.lo ≤ x ∧ x ≤ a.hi := by
  rcases List.mem_range'.mp h with ⟨i, hi, hx⟩
  simp only [Nat.one_mul] at hx
  unfold width at hi
  omega

private theorem before (a : Band) (as : List Band) (p : Nat) (hp : p < a.lo) :
    suffix (a :: as) p = number (a :: as) := by
  apply weight_congr
  intro x hx
  have ha := within a hx
  simp [show p < x by omega]

private theorem weight_const (xs : List α) (c : Nat) :
    weightSum xs (fun _ => c) = xs.length * c := by
  induction xs with
  | nil => simp [weightSum]
  | cons x xs ih =>
    change c + weightSum xs _ = (xs.length + 1)*c
    rw [ih, Nat.add_mul]; omega

private theorem cut_left (a : Band) (as : List Band) (ha : a.lo ≤ a.hi) :
    suffix (a :: as) a.lo + suffix as a.lo = number (a :: as) := by
  have hw : a.width = (a.hi - a.lo) + 1 := by unfold width; omega
  simp only [suffix, number, choices, hw, List.range'_succ]
  change (if a.lo < a.lo then _ else _) + weightSum _ _ + _ = _ + weightSum _ _
  simp only [Nat.lt_irrefl, ite_false, Nat.zero_add]
  rw [Nat.add_comm]
  congr 1
  apply weight_congr
  intro x hx
  obtain ⟨i, hi, hx⟩ := List.mem_range'.mp hx
  simp [show a.lo < x by omega]

/-- 相邻区间分开时，选择第一个区间的位置给出 width 个独立选择。 -/
theorem apart (a b : Band) (bs : List Band) (hab : a.hi < b.lo) :
    number (a :: b :: bs) = a.width * number (b :: bs) := by
  unfold number
  calc
    _ = weightSum a.choices (fun _ => number (b :: bs)) := by
      apply weight_congr
      intro x hx
      exact before b bs x (by have := within a hx; omega)
    _ = _ := by rw [weight_const]; simp [choices, number]

/-- 区间在单一点相接时，唯一冲突为相邻两粒子同时占据该端点。 -/
theorem touching (a b : Band) (bs : List Band) (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi)
    (hab : a.hi = b.lo) (hr : suffix bs b.lo = number bs) :
    number (a :: b :: bs) + number bs = a.width * number (b :: bs) := by
  have hw : a.width = (a.hi - a.lo) + 1 := by unfold width; omega
  have hend : a.lo + (a.hi - a.lo) = b.lo := by omega
  have initial : weightSum (List.range' a.lo (a.hi-a.lo)) (suffix (b :: bs)) =
      (a.hi-a.lo) * number (b :: bs) := by
    calc
      _ = weightSum (List.range' a.lo (a.hi-a.lo)) (fun _ => number (b::bs)) := by
        apply weight_congr
        intro x hx
        obtain ⟨i, hi, hx⟩ := List.mem_range'.mp hx
        simp only [Nat.one_mul] at hx
        exact before b bs x (by omega)
      _ = _ := by simp [weight_const]
  change weightSum a.choices _ + _ = _
  rw [choices, hw, List.range'_1_concat, hend]
  have app (xs ys : List Nat) (f : Nat → Nat) :
      weightSum (xs ++ ys) f = weightSum xs f + weightSum ys f := by
    simp [weightSum, List.sum_append]
  rw [app, initial, Nat.add_mul]
  have hcut := cut_left b bs hb
  rw [hr] at hcut
  change _ + (suffix (b :: bs) b.lo + 0) + _ = _
  omega

def regular : List Band → Prop
  | [] => True
  | [a] => a.lo ≤ a.hi
  | a :: b :: bs => a.lo ≤ a.hi ∧ a.lo < b.lo ∧ a.hi ≤ b.lo ∧ regular (b::bs)

private theorem regular_tail {a : Band} {as : List Band} (h : regular (a::as)) : regular as := by
  cases as with
  | nil => trivial
  | cons b bs => exact h.2.2.2

private theorem regular_head {a : Band} {as : List Band} (h : regular (a::as)) : a.lo ≤ a.hi := by
  cases as with
  | nil => exact h
  | cons b bs => exact h.1

private theorem released (b : Band) (bs : List Band) (h : regular (b::bs)) :
    suffix bs b.lo = number bs := by
  cases bs with
  | nil => rfl
  | cons c cs => exact before _ _ _ h.2.1

/-- 路径三对角行列式的递推：对角元为区间宽度，
    相邻上下对角元的乘积为两个区间是否接触。 -/
def continuant : List Band → Nat
  | [] => 1
  | [a] => a.width
  | a :: b :: bs => a.width * continuant (b::bs) -
      (if a.hi = b.lo then continuant bs else 0)

theorem number_eq_continuant : ∀ as : List Band, regular as → number as = continuant as
  | [], _ => rfl
  | [a], _ => by
    change weightSum a.choices (fun _ => 1) = a.width
    simp [weight_const, choices]
  | a::b::bs, h => by
    have hr := regular_tail h
    rw [continuant, ← number_eq_continuant (b::bs) hr, ← number_eq_continuant bs (regular_tail hr)]
    by_cases ht : a.hi = b.lo
    · have he := touching a b bs h.1 (regular_head hr) ht (released _ _ hr)
      simp [ht]
      omega
    · simpa [ht] using apart a b bs (by have := h.2.2.1; omega)

/-- 二值字的真位从左至右依次填入区间，p 为该字左端已经扫描的列数。 -/
def fits (p : Nat) : List Band → List Bool → Bool
  | bs, [] => bs.isEmpty
  | bs, false :: xs => fits (p+1) bs xs
  | [], true :: _ => false
  | b::bs, true :: xs => decide (b.lo ≤ p+1 ∧ p+1 ≤ b.hi) && fits (p+1) bs xs

theorem fits_positions (p : Nat) (bs : List Band) (xs : List Bool) :
    fits p bs xs = true ↔
    rank xs xs.length = bs.length ∧
      ∀ i (hi : i < bs.length), bs[i].lo ≤ p + position xs i ∧ p + position xs i ≤ bs[i].hi := by
  induction xs generalizing p bs with
  | nil => cases bs <;> simp [fits, rank]
  | cons v xs ih =>
    cases v with
    | false =>
      simp only [fits, ih, List.length_cons, rank, Bool.toNat_false, Nat.zero_add,
        position]
      grind
    | true =>
      cases bs with
      | nil => simp [fits, rank]
      | cons b bs =>
        simp only [fits, Bool.and_eq_true, decide_eq_true_eq, ih, List.length_cons,
          rank, Bool.toNat_true, Nat.add_comm 1, Nat.add_right_cancel_iff]
        constructor
        · rintro ⟨⟨hl, hh⟩, hr, hbound⟩
          refine ⟨hr, ?_⟩
          intro i hi
          cases i with
          | zero => exact ⟨hl, hh⟩
          | succ j =>
            have hj := hbound j (by omega)
            simpa [position, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hj
        · rintro ⟨hr, hb⟩
          refine ⟨hb 0 (by omega), hr, ?_⟩
          intro j hj
          have hh := hb (j+1) (by omega)
          simpa [position, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

private theorem choice_iff (a : Band) (p : Nat) :
    p ∈ a.choices ↔ a.lo ≤ p ∧ p ≤ a.hi := by
  constructor
  · exact within a
  · rintro ⟨hl, hh⟩
    apply List.mem_range'.mpr
    exact ⟨p-a.lo, by unfold width; omega, by omega⟩

private theorem weight_point (xs : List Nat) (k c : Nat) (hu : xs.Nodup) :
    weightSum xs (fun x => if x = k then c else 0) = if k ∈ xs then c else 0 := by
  induction xs with
  | nil => simp [weightSum]
  | cons x xs ih =>
    rw [List.nodup_cons] at hu
    change _ + weightSum xs _ = _
    rw [ih hu.2]
    by_cases he : x = k
    · subst k; simp [hu.1]
    · simp [he, Ne.symm he]

private theorem advance (p : Nat) (a : Band) (as : List Band) :
    suffix (a::as) p = suffix (a::as) (p+1) +
      (if a.lo ≤ p+1 ∧ p+1 ≤ a.hi then suffix as (p+1) else 0) := by
  simp only [suffix]
  have point := weight_point a.choices (p+1) (suffix as (p+1)) (List.nodup_range')
  simp only [choice_iff] at point
  rw [← point, ← weight_add]
  apply weight_congr
  intro x _
  by_cases hx : x = p+1
  · subst x; simp
  · by_cases hk : p < x <;> simp [hx, hk, show p+1 < x ↔ p < x by omega]

/-- 若右端在最后一列前结束，按字枚举的计数和按粒子位置枚举的计数相等。 -/
theorem word_count (n p : Nat) (bs : List Band) (bound : ∀ b ∈ bs, b.hi ≤ p+n) :
    weightSum (words n) (fun v => if fits p bs v then 1 else 0) = suffix bs p := by
  induction n generalizing p bs with
  | zero =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [words, weightSum, fits, List.isEmpty, List.sum_cons, List.map_cons,
        List.map_nil, List.sum_nil, Bool.false_eq_true, ite_false, Nat.zero_add]
      unfold suffix
      have he : weightSum b.choices (fun q => if p < q then suffix bs q else 0) =
          weightSum b.choices (fun _ => 0) := by
        apply weight_congr
        intro q hq
        have hh := bound b (by simp)
        have hj := within b hq
        simp [show ¬ p < q by omega]
      exact (he.trans (by simp [weightSum, sum_zeros])).symm
  | succ n ih =>
    rw [word_sum]
    have hb : ∀ b ∈ bs, b.hi ≤ p+1+n := by intro b h; have := bound b h; omega
    change weightSum (words n) (fun t => if fits (p+1) bs t then 1 else 0) + _ = _
    rw [ih (p+1) bs hb]
    cases bs with
    | nil => simp [fits, weightSum, sum_zeros, suffix]
    | cons b bs =>
      rw [advance p b bs]
      by_cases hc : b.lo ≤ p+1 ∧ p+1 ≤ b.hi
      · simp [fits, hc, ih (p+1) bs (fun v hv => hb v (by simp [hv]))]
      · have hc' : ¬(b.lo ≤ p+1 ∧ p < b.hi) := by omega
        simp [fits, hc, hc', weightSum, sum_zeros]

end Band

private theorem position_absent (s : List Bool) (i : Nat) (hi : rank s s.length ≤ i) :
    position s i = s.length + 1 := by
  have hl := position_le s i
  have he := rank_position s s.length i (Nat.le_refl _)
  omega

/-- 实际中间粒子的闭区间，上界截断到棋盘右端。 -/
def occupiedBands (s u : List Bool) : List Band :=
  List.ofFn fun i : Fin (rank u u.length) =>
    let b := particleBand s u i
    ⟨b.lo, min b.hi s.length⟩

theorem two_fits (s t u : List Bool) (hst : s.length = t.length)
    (htu : t.length = u.length) (hcard : rank u u.length = rank s s.length + 1) :
    one 0 1 s t = 1 ∧ one 0 0 t u = 1 ↔ Band.fits 0 (occupiedBands s u) t = true := by
  rw [two_interlaces _ _ _ hst htu, Band.fits_positions]
  simp only [occupiedBands, List.length_ofFn, List.getElem_ofFn, Nat.zero_add]
  constructor
  · rintro ⟨ht, hu, hh⟩
    refine ⟨hu.symm, ?_⟩
    intro i hi
    have hw := (rank_position t t.length i (Nat.le_refl _)).1 (by omega)
    exact ⟨(hh i).1, Nat.le_min.mpr ⟨(hh i).2, by omega⟩⟩
  · rintro ⟨ht, hh⟩
    refine ⟨by omega, ht.symm, ?_⟩
    intro i
    by_cases hi : i < rank u u.length
    · exact ⟨(hh i hi).1, Nat.le_trans (hh i hi).2 (Nat.min_le_left ..)⟩
    · have ht' := position_absent t i (by omega)
      have hs' := position_absent s i (by omega)
      have hu' := position_absent u (i+1) (by omega)
      have hull : (particleBand s u i).lo ≤ t.length+1 := by
        cases i with
        | zero => simp [particleBand]; have hj := position_le u 0; omega
        | succ j =>
          change max (position u (j+1)) (position s j) ≤ _
          exact Nat.max_le.mpr ⟨by have hj := position_le u (j+1); omega,
            by have hj := position_le s j; omega⟩
      refine ⟨by omega, ?_⟩
      change position t i ≤ min (position s i) (position u (i+1))
      simp [ht', hs', hu', hst, htu]

theorem two_particle_count (s u : List Bool) (hlen : s.length = u.length)
    (hcard : rank u u.length = rank s s.length + 1) :
    two 0 0 1 0 s u = Band.suffix (occupiedBands s u) 0 := by
  have bound : ∀ b ∈ occupiedBands s u, b.hi ≤ 0+s.length := by
    intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    simpa only [Nat.zero_add] using (Nat.min_le_right (particleBand s u i).hi s.length)
  rw [← Band.word_count s.length 0 _ bound]
  unfold two
  apply weight_congr
  intro t ht
  have ht' := words_length ht
  have hf := two_fits s t u ht'.symm (ht'.trans hlen) hcard
  have bin (e : Int) (w z : List Bool) : one 0 e w z = 0 ∨ one 0 e w z = 1 := by
    unfold one
    split <;> simp
  rcases bin 1 s t with h | h <;> rcases bin 0 t u with j | j <;> simp_all

theorem two_particle_continuant (s u : List Bool) (hlen : s.length = u.length)
    (hcard : rank u u.length = rank s s.length + 1)
    (hreg : Band.regular (occupiedBands s u)) :
    two 0 0 1 0 s u = Band.continuant (occupiedBands s u) := by
  rw [two_particle_count _ _ hlen hcard, ← Band.number_eq_continuant _ hreg]
  have positive : ∀ b ∈ occupiedBands s u, 0 < b.lo := by
    intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact Nat.lt_of_lt_of_le (position_pos u i) (Nat.le_max_left ..)
  cases he : occupiedBands s u with
  | nil => rfl
  | cons b bs =>
    apply Band.before
    exact positive b (by simp [he])

private theorem position_next (s : List Bool) (i : Nat) (hi : i < rank s s.length) :
    position s i < position s (i+1) := by
  induction s generalizing i with
  | nil => simp [rank] at hi
  | cons v vs ih =>
    cases v with
    | false =>
      simp [rank] at hi
      simpa [position] using ih i hi
    | true =>
      cases i with
      | zero => simpa [position] using position_pos vs 0
      | succ i =>
        simp [rank] at hi
        simpa [position] using ih i (by omega)

private theorem regular_from_indices (bs : List Band)
    (hpos : ∀ b ∈ bs, b.lo ≤ b.hi)
    (hadj : ∀ i (hi : i+1 < bs.length), bs[i].lo < bs[i+1].lo ∧ bs[i].hi ≤ bs[i+1].lo) :
    Band.regular bs := by
  cases bs with
  | nil => trivial
  | cons a xs =>
    cases xs with
    | nil => exact hpos a (by simp)
    | cons b bs =>
      obtain ⟨hs, he⟩ := hadj 0 (by simp)
      refine ⟨hpos a (by simp), hs, he, regular_from_indices (b::bs) ?_ ?_⟩
      · intro v hv; exact hpos v (by simp [hv])
      · intro i hi
        exact hadj (i+1) (by simpa using hi)

private theorem bands_regular (s u : List Bool)
    (hcard : rank u u.length = rank s s.length + 1)
    (hpos : ∀ b ∈ occupiedBands s u, b.lo ≤ b.hi) : Band.regular (occupiedBands s u) := by
  apply regular_from_indices _ hpos
  intro i hi
  simp only [occupiedBands, List.length_ofFn] at hi
  simp only [occupiedBands, List.getElem_ofFn]
  have hu := position_next u i (by omega)
  have hs : (particleBand s u i).lo < (particleBand s u (i+1)).lo := by
    cases i with
    | zero =>
      change max (position u 0) 0 < max (position u 1) (position s 0)
      simpa using Nat.lt_of_lt_of_le hu (Nat.le_max_left (position u 1) (position s 0))
    | succ i =>
      have hs := position_next s i (by omega)
      change max (position u (i+1)) (position s i) < max (position u (i+1+1)) (position s (i+1))
      omega
  exact ⟨hs, Nat.le_trans (Nat.min_le_left ..)
    (Nat.le_trans (Nat.min_le_left ..) (Nat.le_max_right ..))⟩

private theorem two_wrong_rank (s u : List Bool) (hlen : s.length = u.length)
    (hc : rank u u.length ≠ rank s s.length + 1) : two 0 0 1 0 s u = 0 := by
  have hz : two 0 0 1 0 s u = weightSum (words s.length) (fun _ => 0) := by
    apply weight_congr
    intro t ht
    have ht' := words_length ht
    have hbad : ¬ (one 0 1 s t = 1 ∧ one 0 0 t u = 1) := by
      intro h
      obtain ⟨h1, h2, _⟩ := (two_interlaces s t u ht'.symm (ht'.trans hlen)).1 h
      omega
    unfold one at *
    split <;> split <;> simp_all
  simpa [weightSum, sum_zeros] using hz

/-- 无条件的双行转移行列式；错误的总粒子数或空区间贡献零。 -/
def doubleRowDet (s u : List Bool) : Nat :=
  let bs := occupiedBands s u
  if rank u u.length = rank s s.length + 1 ∧ bs.all (fun b => decide (b.lo ≤ b.hi)) then
    Band.continuant bs
  else 0

theorem two_eq_doubleRowDet (s u : List Bool) (hlen : s.length = u.length) :
    two 0 0 1 0 s u = doubleRowDet s u := by
  by_cases hc : rank u u.length = rank s s.length + 1
  · by_cases hp : ∀ b ∈ occupiedBands s u, b.lo ≤ b.hi
    · have ha : (occupiedBands s u).all (fun b => decide (b.lo ≤ b.hi)) = true := by
        simpa using hp
      simpa [doubleRowDet, ha, hc] using two_particle_continuant s u hlen hc (bands_regular s u hc hp)
    · have hzero : ∀ t : List Bool, t.length = s.length → ¬Band.fits 0 (occupiedBands s u) t = true := by
        intro t _ hfit
        obtain ⟨_, hh⟩ := (Band.fits_positions _ _ _).1 hfit
        apply hp
        intro b hb
        obtain ⟨i, hi, he⟩ := List.getElem_of_mem hb
        have h := hh i hi
        rw [he] at h
        omega
      have hz : two 0 0 1 0 s u = weightSum (words s.length) (fun _ => 0) := by
        apply weight_congr
        intro t ht
        have hl := words_length ht
        have hf := two_fits s t u hl.symm (hl.trans hlen) hc
        have hn := hzero t hl
        unfold one at *
        split <;> split <;> simp_all
      simpa [doubleRowDet, hp, hc, weightSum, sum_zeros] using hz
  · simpa [doubleRowDet, hc] using two_wrong_rank s u hlen hc

private theorem rank_false (n : Nat) : rank (List.replicate n false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, rank, ih]

private theorem rank_zero_word (t : List Bool) (h : rank t t.length = 0) :
    t = List.replicate t.length false := by
  induction t with
  | nil => rfl
  | cons v vs ih =>
    cases v <;> simp [rank] at h
    simp [List.replicate_succ, ← ih h]

private theorem word_delta (s : List Bool) (w : Nat) :
    weightSum (words s.length) (fun t => if t = s then w else 0) = w := by
  induction s with
  | nil => simp [words, weightSum]
  | cons v vs ih =>
    rw [List.length_cons, word_sum]
    cases v <;> simp [weightSum, sum_zeros] at * <;> exact ih

theorem first_row_forced (n k : Nat) :
    walk n (k+1) (List.replicate n false) 0 =
      walk n k (List.replicate n false) 1 := by
  rw [walk]
  have hd := word_delta (List.replicate n false) (walk n k (List.replicate n false) 1)
  rw [List.length_replicate] at hd
  rw [← hd]
  apply weight_congr
  intro t ht
  have hl := words_length ht
  by_cases hh : admissible 0 0 (List.replicate n false) t = true
  · have ho : one 0 0 (List.replicate n false) t = 1 := by simp [one, isBit, hh]
    have he := ((one_interlaces 0 _ t (by simp [hl])).1 ho).1
    rw [List.length_replicate, rank_false] at he
    have hf := rank_zero_word t (by omega)
    rw [hl] at hf
    subst t; simp [hh]
  · have ht' : t ≠ List.replicate n false := by
      intro he
      subst t
      have bound (i : Nat) : position (List.replicate n false) i = n+1 := by
        simpa using position_absent (List.replicate n false) i (by simp [rank_false])
      have hv := (one_interlaces 0 (List.replicate n false) (List.replicate n false) rfl).2
        (by simp [bound])
      simp [one, isBit, hh] at hv
    simp [hh, ht']

/-- 对具有相同宽度的相邻层用三对角行列式收缩；每次递推粒子数增加一。 -/
def layers (n : Nat) : Nat → List Bool → Nat
  | 0, s => if s.all id then 1 else 0
  | r+1, s => weightSum (words n) (fun u => doubleRowDet s u * layers n r u)

theorem walk_eq_layers (n r : Nat) (s : List Bool) (hs : s.length = n) :
    walk n (2*r) s 1 = layers n r s := by
  induction r generalizing s with
  | zero => simp [walk, layers]
  | succ r ih =>
    rw [show 2*(r+1) = 2*r+2 by omega, walk_two_rows n _ _ hs, layers]
    apply weight_congr
    intro u hu
    have hl := words_length hu
    simpa [ih u hl] using congrArg (· * layers n r u) (two_eq_doubleRowDet s u (hs.trans hl.symm))

theorem count_as_continuant_layers (n : Nat) :
    b n = layers n n (List.replicate n false) := by
  rw [count_as_interlacing_walk, first_row_forced, walk_eq_layers _ _ _ (by simp)]

end OeisA109074.Partial.Interlace

end

section

namespace OeisA109074.Partial.SixVertex

variable {R X : Type} [Lean.Grind.CommRing R]

-- T 作用在水平箭头及已有列的边界状态上。
abbrev Transfer (R X : Type) := (Bool → X → R) → Bool → X → R

structure TransferLinear (u : Transfer R X) : Prop where
  add (f g : Bool → X → R) :
    u (fun i s => f i s + g i s) = fun i s => u f i s + u g i s
  scale (r : R) (f : Bool → X → R) :
    u (fun i s => r * f i s) = fun i s => r * u f i s

private abbrev PairFn (R X : Type) := Bool → Bool → X → R
private abbrev TripleFn (R X : Type) := Bool → Bool → Bool → X → R

private def left (u : Transfer R X) (f : PairFn R X) : PairFn R X :=
  fun i j => u (fun a s => f a j s) i

private def right (u : Transfer R X) (f : PairFn R X) : PairFn R X :=
  fun i j => u (fun b s => f i b s) j

private def exchange (w : Weights R) (f : PairFn R X) : PairFn R X :=
  fun i j s => scatter w (fun a b => f a b s) i j

/-- 两条反射谱线共有 X 上的量子状态。等式保留全部外部箭头。 -/
def SatisfiesReflection (q x y : R) (u v : Transfer R X) : Prop :=
  ∀ f : PairFn R X,
    exchange (spectral q x y) (left u (exchange (spectral q (x*y) 1) (right v f))) =
      right v (exchange (spectral q (x*y) 1) (left u (exchange (spectral q x y) f)))

/-- 在已有反射行的外侧添一列；穿入的参数为 x/z，穿出的参数为 xz。 -/
def addColumn (q x z : R) (u : Transfer R X) : Transfer R (Bool × X) :=
  fun f i (k,s) => scatter (spectral q x z) (fun a k' =>
    u (fun b t => scatter (spectral q (x*z) 1) (fun c k'' => f c (k'',t)) b k') a s) i k

private def ab (w : Weights R) (f : TripleFn R X) : TripleFn R X :=
  fun i j k s => scatter w (fun a b => f a b k s) i j
private def ac (w : Weights R) (f : TripleFn R X) : TripleFn R X :=
  fun i j k s => scatter w (fun a c => f a j c s) i k
private def bc (w : Weights R) (f : TripleFn R X) : TripleFn R X :=
  fun i j k s => scatter w (fun b c => f i b c s) j k
private def ax (u : Transfer R X) (f : TripleFn R X) : TripleFn R X :=
  fun i j k => u (fun a s => f a j k s) i
private def bx (v : Transfer R X) (f : TripleFn R X) : TripleFn R X :=
  fun i j k => v (fun b s => f i b k s) j

private theorem commute_ax_bc {u : Transfer R X} (hu : TransferLinear u)
    (w : Weights R) (f : TripleFn R X) : ax u (bc w f) = bc w (ax u f) := by
  funext i j k s
  cases j <;> cases k <;> simp [ax, bc, scatter, hu.add, hu.scale]

private theorem commute_bx_ac {v : Transfer R X} (hv : TransferLinear v)
    (w : Weights R) (f : TripleFn R X) : bx v (ac w f) = ac w (bx v f) := by
  funext i j k s
  cases i <;> cases k <;> simp [bx, ac, scatter, hv.add, hv.scale]

-- 三种过线次序对应正向、反向以及一正一反的局部交点。
private theorem incoming (q x y z : R) (f : TripleFn R X) :
    ab (spectral q x y) (ac (spectral q x z) (bc (spectral q y z) f)) =
      bc (spectral q y z) (ac (spectral q x z) (ab (spectral q x y) f)) := by
  funext i j k s
  exact congrFun (congrFun (congrFun (yang_baxter q x y z (fun a b c => f a b c s)) i) j) k

private theorem outgoing (q x y z : R) (f : TripleFn R X) :
    ab (spectral q x y) (ac (spectral q (x*z) 1) (bc (spectral q (y*z) 1) f)) =
      bc (spectral q (y*z) 1) (ac (spectral q (x*z) 1) (ab (spectral q x y) f)) := by
  funext i j k s
  cases i <;> cases j <;> cases k <;> simp [ab, ac, bc, scatter, spectral] <;> grind

private theorem crossing_out_in (q x y z : R) (f : TripleFn R X) :
    ac (spectral q (x*z) 1) (ab (spectral q (x*y) 1) (bc (spectral q y z) f)) =
      bc (spectral q y z) (ab (spectral q (x*y) 1) (ac (spectral q (x*z) 1) f)) := by
  funext i j k s
  cases i <;> cases j <;> cases k <;> simp [ab, ac, bc, scatter, spectral] <;> grind

private theorem crossing_in_out (q x y z : R) (f : TripleFn R X) :
    ac (spectral q x z) (ab (spectral q (x*y) 1) (bc (spectral q (y*z) 1) f)) =
      bc (spectral q (y*z) 1) (ab (spectral q (x*y) 1) (ac (spectral q x z) f)) := by
  funext i j k s
  cases i <;> cases j <;> cases k <;> simp [ab, ac, bc, scatter, spectral] <;> grind

private theorem inner_reflection {q x y : R} {u v : Transfer R X}
    (huv : SatisfiesReflection q x y u v) (f : TripleFn R X) :
    ab (spectral q x y) (ax u (ab (spectral q (x*y) 1) (bx v f))) =
      bx v (ab (spectral q (x*y) 1) (ax u (ab (spectral q x y) f))) := by
  funext i j k s
  exact congrFun (congrFun (congrFun (huv (fun a b t => f a b k t)) i) j) s

/-- 一列的穿入、反射和穿出保持整个反射方程。 -/
theorem reflection_addColumn {q x y : R} (z : R) {u v : Transfer R X}
    (hu : TransferLinear u) (hv : TransferLinear v) (huv : SatisfiesReflection q x y u v) :
    SatisfiesReflection q x y (addColumn q x z u) (addColumn q y z v) := by
  intro f
  let g : TripleFn R X := fun a b k s => f a b (k,s)
  suffices eqn :
      ab (spectral q x y) (ac (spectral q x z) (ax u (ac (spectral q (x*z) 1)
        (ab (spectral q (x*y) 1) (bc (spectral q y z) (bx v (bc (spectral q (y*z) 1) g))))))) =
      bc (spectral q y z) (bx v (bc (spectral q (y*z) 1) (ab (spectral q (x*y) 1)
        (ac (spectral q x z) (ax u (ac (spectral q (x*z) 1) (ab (spectral q x y) g))))))) by
    funext i j ⟨k,s⟩
    exact congrFun (congrFun (congrFun (congrFun eqn i) j) k) s
  rw [crossing_out_in, commute_ax_bc hu, ← commute_bx_ac hv, incoming, inner_reflection huv,
    outgoing, ← commute_bx_ac hv, commute_ax_bc hu, crossing_in_out]

private theorem scatter_add (w : Weights R) (f g : Bool → Bool → R) (i j : Bool) :
    scatter w (fun a b => f a b + g a b) i j = scatter w f i j + scatter w g i j := by
  cases i <;> cases j <;> simp [scatter] <;> grind

private theorem scatter_scale (w : Weights R) (r : R) (f : Bool → Bool → R) (i j : Bool) :
    scatter w (fun a b => r * f a b) i j = r * scatter w f i j := by
  cases i <;> cases j <;> simp [scatter] <;> grind

theorem linear_addColumn (q x z : R) {u : Transfer R X} (hu : TransferLinear u) :
    TransferLinear (addColumn q x z u) where
  add := by
    intro f g
    funext i ⟨k,s⟩
    simp only [addColumn, scatter_add, hu.add]
  scale := by
    intro r f
    funext i ⟨k,s⟩
    simp only [addColumn, scatter_scale, hu.scale]

/-- 最内侧的反射边界不改变水平箭头，只给它附加对角权。 -/
def bare (d x : R) : Transfer R Unit := fun f i s => boundary d x i * f i s

private theorem linear_bare (d x : R) : TransferLinear (bare d x) where
  add := by intro f g; funext i s; simp [bare]; grind
  scale := by intro r f; funext i s; simp [bare]; grind

private theorem reflection_bare (q d x y : R) :
    SatisfiesReflection q x y (bare d x) (bare d y) := by
  intro f
  funext i j s
  exact congrFun (congrFun (reflection q d x y (fun a b => f a b s)) i) j

/-- 固定宽度的列箭头，从外侧到反射端排列。 -/
abbrev Site : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Site n

/-- 一对反射行的所有边界条件都保留在转移算子中。 -/
def folded (q d x : R) : (cols : List R) → Transfer R (Site cols.length)
  | [] => bare d x
  | z :: zs => addColumn q x z (folded q d x zs)

theorem folded_linear (q d x : R) (cols : List R) : TransferLinear (folded q d x cols) := by
  induction cols with
  | nil => exact linear_bare _ _
  | cons z zs ih => exact linear_addColumn _ _ _ ih

theorem folded_reflection (q d x y : R) (cols : List R) :
    SatisfiesReflection q x y (folded q d x cols) (folded q d y cols) := by
  induction cols with
  | nil => exact reflection_bare _ _ _ _
  | cons z zs ih =>
    exact reflection_addColumn z (folded_linear _ _ _ zs) (folded_linear _ _ _ zs) ih

/-- 固定左边界，入射箭头为 1、出射箭头为 0 的双行算子。 -/
def create (u : Transfer R X) (f : X → R) : X → R :=
  u (fun i s => if i then 0 else f s) true

private theorem transfer_zero {u : Transfer R X} (hu : TransferLinear u) :
    u (fun _ _ => 0) = fun _ _ => 0 := by
  have h := hu.scale 0 (fun _ _ => 0)
  simpa only [Lean.Grind.Semiring.zero_mul] using h

-- 固定四条外部水平边，仅有两个标量权留在反射方程的两端。
theorem create_exchange_scaled {q x y : R} {u v : Transfer R X}
    (hu : TransferLinear u) (hv : TransferLinear v) (huv : SatisfiesReflection q x y u v)
    (f : X → R) (s : X) :
    (spectral q x y).a * (spectral q (x*y) 1).b * create u (create v f) s =
    (spectral q x y).a * (spectral q (x*y) 1).b * create v (create u f) s := by
  let g : PairFn R X := fun i j t => if i then 0 else if j then 0 else f t
  have h := congrFun (congrFun (congrFun (huv g) true) true) s
  let r := spectral q x y
  let m := spectral q (x*y) 1
  have lhs : (fun i t => exchange m (right v g) i true t) =
      (fun i t => m.b * (if i then 0 else create v f t)) := by
    funext i t
    cases i <;> simp [exchange, right, scatter, g, create, transfer_zero hv] <;> grind
  have outer : exchange r g = fun i j t =>
      r.a * (if i then 0 else if j then 0 else f t) := by
    funext i j t
    cases i <;> cases j <;> simp [exchange, scatter, g] <;> grind
  have rhs : (fun j t => exchange m (left u (exchange r g)) true j t) =
      (fun j t => m.b * (r.a * (if j then 0 else create u f t))) := by
    have l : left u (exchange r g) = fun i j t => r.a * left u g i j t := by
      rw [outer]
      funext i j t
      exact congrFun (congrFun (hu.scale r.a (fun a s => g a j s)) i) t
    rw [l]
    funext j t
    cases j <;> simp [exchange, left, scatter, g, create, transfer_zero hu] <;> grind
  change r.a * u (fun i t => exchange m (right v g) i true t) true s =
    v (fun j t => exchange m (left u (exchange r g)) true j t) true s at h
  rw [lhs, rhs, hu.scale, hv.scale, hv.scale] at h
  simp only [create] at *
  grind

theorem folded_create_exchange (q d x y : R) (cols : List R)
    (cancel : Function.Injective (fun t : R => (spectral q x y).a * (spectral q (x*y) 1).b * t))
    (f : Site cols.length → R) :
    create (folded q d x cols) (create (folded q d y cols) f) =
      create (folded q d y cols) (create (folded q d x cols) f) := by
  funext s
  exact cancel (create_exchange_scaled (folded_linear _ _ _ _) (folded_linear _ _ _ _)
    (folded_reflection q d x y cols) f s)

def emptySite : (n : Nat) → Site n
  | 0 => ()
  | n+1 => (false, emptySite n)

def fullSiteWeight : (n : Nat) → Site n → R
  | 0, _ => 1
  | n+1, (k,s) => if k then fullSiteWeight n s else 0

def stackRows (q d : R) (cols : List R) : List R → (Site cols.length → R) → Site cols.length → R
  | [], f => f
  | x :: xs, f => create (folded q d x cols) (stackRows q d cols xs f)

def domainPartition (q d : R) (rows cols : List R) : R :=
  stackRows q d cols rows (fullSiteWeight cols.length) (emptySite cols.length)

private theorem addColumn_occupied (q x z : R) {u : Transfer R X} (hu : TransferLinear u)
    (f : Bool × X → R) (s : X) :
    create (addColumn q x z u) f (true,s) =
    (spectral q x z).a * (spectral q (x*z) 1).b * create u (fun t => f (true,t)) s := by
  let w := spectral q (x*z) 1
  have h : (fun b t => scatter w (fun c k => if c then 0 else f (k,t)) b true) =
      (fun b t => w.b * (if b then 0 else f (true,t))) := by
    funext b t
    cases b <;> simp [scatter] <;> grind
  change (spectral q x z).a * u _ true s = _
  rw [h, hu.scale]
  simp only [create]
  grind

private theorem addColumn_frozen (q x : R) (u : Transfer R X) (hu : TransferLinear u)
    (f : Bool × X → R) (s : X) :
    create (addColumn q x x u) f (false,s) =
      ((q*q-1)*x*x) * (spectral q (x*x) 1).b *
      u (fun b t => if b then 0 else f (true,t)) false s := by
  let w := spectral q (x*x) 1
  have h : (fun b t => scatter w (fun c k => if c then 0 else f (k,t)) b true) =
      (fun b t => w.b * (if b then 0 else f (true,t))) := by
    funext b t
    cases b <;> simp [scatter] <;> grind
  simp only [create, addColumn, freeze_crossing]
  rw [h, hu.scale]
  grind

/-- 所有列和及水平输入均为零时，没有可分支的顶点。 -/
def emptyFactor (q d x : R) : List R → R
  | [] => boundary d x false
  | z :: zs => (spectral q x z).a * (spectral q (x*z) 1).a * emptyFactor q d x zs

private theorem folded_empty (q d x : R) (cols : List R) (f : Bool → Site cols.length → R) :
    folded q d x cols f false (emptySite cols.length) =
      emptyFactor q d x cols * f false (emptySite cols.length) := by
  induction cols with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.length_cons, folded, addColumn, emptySite, scatter, ite_true, emptyFactor]
    rw [ih]
    simp
    grind

def occupiedFactor (q z : R) : List R → R
  | [] => 1
  | x :: xs => ((spectral q x z).a * (spectral q (x*z) 1).b) * occupiedFactor q z xs

private theorem create_scale {u : Transfer R X} (hu : TransferLinear u) (a : R) (f : X → R) :
    create u (fun s => a * f s) = fun s => a * create u f s := by
  have h : (fun (i : Bool) s => if i then 0 else a * f s) =
      (fun (i : Bool) s => a * (if i then 0 else f s)) := by
    funext i s
    cases i <;> simp <;> grind
  simp only [create, h, hu.scale]

private theorem stack_occupied (q d z : R) (cols rows : List R)
    (f : Site (z::cols).length → R) :
    (fun s => stackRows q d (z::cols) rows f (true,s)) =
      fun s => occupiedFactor q z rows * stackRows q d cols rows (fun t => f (true,t)) s := by
  induction rows with
  | nil => funext s; simp [stackRows, occupiedFactor]; grind
  | cons x xs ih =>
    funext s
    simp only [List.length_cons, stackRows, folded, addColumn_occupied _ _ _ (folded_linear _ _ _ _)]
    rw [ih, create_scale (folded_linear _ _ _ _)]
    simp [occupiedFactor]
    grind

/-- 第一个行参数等于第一列参数时，完整反射网格同时删去一对行和一列。 -/
theorem freeze_domain (q d z : R) (rows cols : List R) :
    domainPartition q d (z :: rows) (z :: cols) =
      ((q*q-1)*z*z) * (spectral q (z*z) 1).b * emptyFactor q d z cols *
      occupiedFactor q z rows * domainPartition q d rows cols := by
  unfold domainPartition
  simp only [List.length_cons, stackRows, folded, emptySite, addColumn_frozen _ _ _ (folded_linear _ _ _ _),
    folded_empty, Bool.false_eq_true, ite_false]
  have h := congrFun (stack_occupied q d z cols rows (fullSiteWeight _)) (emptySite cols.length)
  change stackRows q d (z::cols) rows (fullSiteWeight (cols.length+1)) (true, emptySite _) =
    occupiedFactor q z rows * stackRows q d cols rows (fullSiteWeight _) (emptySite _) at h
  rw [h]
  grind

private def projectEmpty (f : X → R) : Bool × X → R := fun (k,s) => if k then 0 else f s

private theorem addColumn_projectEmpty (q x z : R) {u : Transfer R X} (hu : TransferLinear u)
    (f : X → R) :
    create (addColumn q x z u) (projectEmpty f) =
      fun (k,s) => (spectral q x z).b * (spectral q (x*z) 1).a * projectEmpty (create u f) (k,s) := by
  let w := spectral q (x*z) 1
  have h0 : (fun b t => scatter w (fun c k => if c then 0 else projectEmpty f (k,t)) b false) =
      (fun b t => w.a * (if b then 0 else f t)) := by
    funext b t
    cases b <;> simp [scatter, projectEmpty] <;> grind
  have h1 : (fun b t => scatter w (fun c k => if c then 0 else projectEmpty f (k,t)) b true) =
      (fun _ _ => 0) := by
    funext b t
    cases b <;> simp [scatter, projectEmpty] <;> grind
  funext ⟨k,s⟩
  cases k
  · change (spectral q x z).b * u _ true s + (spectral q x z).c * u _ false s = _
    rw [h0, h1, hu.scale, transfer_zero hu]
    change _ = (spectral q x z).b * w.a * u _ true s
    grind
  · change (spectral q x z).a * u _ true s = _
    rw [h1, transfer_zero hu]
    change _ = (spectral q x z).b * w.a * 0
    grind

def vacantFactor (q z : R) : List R → R
  | [] => 1
  | x :: xs => (spectral q x z).b * (spectral q (x*z) 1).a * vacantFactor q z xs

private theorem stack_scale (q d : R) (cols rows : List R) (r : R) (f : Site cols.length → R) :
    stackRows q d cols rows (fun s => r * f s) = fun s => r * stackRows q d cols rows f s := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simp only [stackRows, ih, create_scale (folded_linear _ _ _ _)]

private theorem stack_projectEmpty (q d z : R) (cols rows : List R)
    (f : Site cols.length → R) :
    stackRows q d (z::cols) rows (projectEmpty f) =
      fun s => vacantFactor q z rows * projectEmpty (stackRows q d cols rows f) s := by
  induction rows with
  | nil => funext s; simp [stackRows, vacantFactor]; grind
  | cons x xs ih =>
    simp only [stackRows, ih]
    apply (create_scale (folded_linear q d x (z::cols)) (vacantFactor q z xs)
      (projectEmpty (stackRows q d cols xs f))).trans
    change (fun s => _ * create (addColumn q x z (folded q d x cols)) (projectEmpty _) s) = _
    rw [addColumn_projectEmpty _ _ _ (folded_linear _ _ _ _)]
    funext ⟨k,s⟩
    simp [vacantFactor]
    grind

private def projectFull (f : X → R) : Bool → X → R := fun i s => if i then f s else 0

def fullFactor (q d x : R) : List R → R
  | [] => boundary d x true
  | z :: zs => (spectral q x z).a * (spectral q (x*z) 1).a * fullFactor q d x zs

private theorem folded_full (q d x : R) (cols : List R) :
    folded q d x cols (projectFull (fullSiteWeight _)) =
      fun i s => fullFactor q d x cols * projectFull (fullSiteWeight _) i s := by
  induction cols with
  | nil =>
    funext i s
    cases i <;> simp [folded, bare, projectFull, fullFactor] <;> grind
  | cons z zs ih =>
    let w := spectral q (x*z) 1
    have h1 : (fun b (t : Site zs.length) => scatter w
        (fun c k => projectFull (fullSiteWeight (zs.length+1)) c (k,t)) b true) =
        fun b t => w.a * projectFull (fullSiteWeight _) b t := by
      funext b t
      cases b <;> simp [scatter, projectFull, fullSiteWeight] <;> grind
    have h0 : (fun b (t : Site zs.length) => scatter w
        (fun c k => projectFull (fullSiteWeight (zs.length+1)) c (k,t)) b false) =
        fun _ _ => 0 := by
      funext b t
      cases b <;> simp [scatter, projectFull, fullSiteWeight] <;> grind
    have h : ∀ b k (s : Site zs.length), folded q d x zs
        (fun c t => scatter w (fun e l => projectFull (fullSiteWeight (zs.length+1)) e (l,t)) c k)
        b s = if k then w.a * (fullFactor q d x zs * projectFull (fullSiteWeight _) b s) else 0 := by
      intro b k s
      cases k
      · rw [h0, transfer_zero (folded_linear _ _ _ _)]
        rfl
      · rw [h1, (folded_linear _ _ _ _).scale, ih]
        rfl
    funext b ⟨k,s⟩
    change scatter (spectral q x z) (fun a k' => folded q d x zs
      (fun e t => scatter w (fun c l => projectFull (fullSiteWeight (zs.length+1)) c (l,t)) e k') a s) b k = _
    simp only [h]
    cases b <;> cases k <;> simp [scatter, List.length_cons, projectFull, fullSiteWeight, fullFactor, w] <;> grind

private theorem freeze_last (q d x z : R) (hz : x*z = 1) (cols : List R) :
    create (folded q d x (z::cols)) (fullSiteWeight _) =
      fun s => (spectral q x z).b * (q*q-1) * fullFactor q d x cols *
        projectEmpty (fullSiteWeight cols.length) s := by
  let w := spectral q (x*z) 1
  let f : Bool → Bool → Site cols.length → R :=
    fun b k t => if b then 0 else fullSiteWeight (cols.length+1) (k,t)
  have h0 : (fun b t => scatter w (fun c l => f c l t) b false) =
      fun b t => (q*q-1) * projectFull (fullSiteWeight _) b t := by
    funext b t
    cases b <;> simp [w, hz, freeze_crossing, f, fullSiteWeight, projectFull] <;> grind
  have h1 : (fun b t => scatter w (fun c l => f c l t) b true) = fun _ _ => 0 := by
    funext b t
    cases b <;> simp [w, hz, freeze_crossing, f] <;> grind
  have h (i k : Bool) (t : Site cols.length) :
      folded q d x cols (fun b t => scatter w (fun c l => f c l t) b k) i t =
        if k then 0 else (q*q-1) * (fullFactor q d x cols * projectFull (fullSiteWeight _) i t) := by
    cases k
    · rw [h0, (folded_linear q d x cols).scale, folded_full]
      rfl
    · rw [h1, transfer_zero (folded_linear _ _ _ _)]
      rfl
  funext ⟨k,t⟩
  change scatter (spectral q x z) (fun i k => folded q d x cols
    (fun b t => scatter w (fun c l => f c l t) b k) i t) true k = _
  simp only [h]
  cases k <;> simp [scatter, projectFull, projectEmpty] <;> grind

private theorem stack_append (q d : R) (cols a b : List R) (f : Site cols.length → R) :
    stackRows q d cols (a ++ b) f = stackRows q d cols a (stackRows q d cols b f) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [stackRows, ih]

/-- 最后一对行的反向谱线在 x*z=1 时与首列冻结，给出第二组降阶点。 -/
theorem freeze_domain_inverse (q d x z : R) (hz : x*z = 1) (rows cols : List R) :
    domainPartition q d (rows ++ [x]) (z::cols) =
      (spectral q x z).b * (q*q-1) * fullFactor q d x cols *
      vacantFactor q z rows * domainPartition q d rows cols := by
  unfold domainPartition
  rw [stack_append]
  simp only [stackRows, freeze_last q d x z hz cols]
  let v := (spectral q x z).b * (q*q-1) * fullFactor q d x cols
  apply (congrFun (stack_scale q d (z::cols) rows v (projectEmpty (fullSiteWeight cols.length)))
    (false, emptySite cols.length)).trans
  rw [stack_projectEmpty q d z cols rows]
  change v * (vacantFactor q z rows * _) = v * vacantFactor q z rows * _
  simp [projectEmpty, v]
  grind

/-- 保留水平入端 i 和出端 j。四种矩阵元都作用于已有列的状态。 -/
def entry (u : Transfer R X) (i j : Bool) (f : X → R) : X → R :=
  u (fun b s => if b = j then f s else 0) i

private theorem entry_add {u : Transfer R X} (hu : TransferLinear u) (i j : Bool) (f g : X → R) :
    entry u i j (fun s => f s + g s) = fun s => entry u i j f s + entry u i j g s := by
  have h : (fun b s => if b = j then f s + g s else 0) =
      fun b s => (if b = j then f s else 0) + (if b = j then g s else 0) := by
    funext b s
    by_cases hb : b = j <;> simp [hb] <;> grind
  simp only [entry, h, hu.add]

private theorem entry_scale {u : Transfer R X} (hu : TransferLinear u) (i j : Bool) (r : R) (f : X → R) :
    entry u i j (fun s => r * f s) = fun s => r * entry u i j f s := by
  have h : (fun b s => if b = j then r * f s else 0) =
      fun b s => r * (if b = j then f s else 0) := by
    funext b s
    by_cases hb : b = j <;> simp [hb] <;> grind
  simp only [entry, h, hu.scale]

private theorem create_entry (u : Transfer R X) (f : X → R) :
    create u f = entry u true false f := by
  have h : (fun (b : Bool) s => if b then 0 else f s) = fun b s => if b = false then f s else 0 := by
    funext b s
    cases b <;> rfl
  simp only [create, entry, h]

-- 空的首列在该双行内或者维持原状，或者在两个交点之一被占据。
private theorem addColumn_vacant (q x z : R) {u : Transfer R X} (hu : TransferLinear u)
    (f : Bool × X → R) (s : X) :
    create (addColumn q x z u) f (false,s) =
      (spectral q x z).b * (spectral q (x*z) 1).a * entry u true false (fun t => f (false,t)) s +
      (spectral q x z).b * (spectral q (x*z) 1).c * entry u true true (fun t => f (true,t)) s +
      (spectral q x z).c * (spectral q (x*z) 1).b * entry u false false (fun t => f (true,t)) s := by
  let w := spectral q (x*z) 1
  have h0 : (fun b t => scatter w (fun c k => if c then 0 else f (k,t)) b false) =
      (fun b t => w.a * (if b = false then f (false,t) else 0) +
        w.c * (if b = true then f (true,t) else 0)) := by
    funext b t
    cases b <;> simp [scatter] <;> grind
  have h1 : (fun b t => scatter w (fun c k => if c then 0 else f (k,t)) b true) =
      (fun b t => w.b * (if b = false then f (true,t) else 0)) := by
    funext b t
    cases b <;> simp [scatter] <;> grind
  change (spectral q x z).b * u _ true s + (spectral q x z).c * u _ false s = _
  rw [h0, h1, hu.add, hu.scale, hu.scale, hu.scale]
  unfold entry
  grind

section PolynomialBounds

open Polynomial
variable {F : Type} [CommRing F]

-- 允许 n=0，此时只有零多项式。odd 表示已经提取变量 z 的一个因子。
private def InBox (odd : Bool) (n : Nat) (v : F → F) : Prop :=
  ∃ p : Polynomial F, (p = 0 ∨ p.natDegree < n) ∧
    ∀ z, v z = (if odd then z else 1) * p.eval (z*z)

private theorem box_zero (e : Bool) (n : Nat) : InBox e n (fun _ : F => 0) := by
  exact ⟨0, Or.inl rfl, by simp⟩

private theorem box_const (c : F) : InBox false 1 (fun _ => c) := by
  exact ⟨C c, Or.inr (by simp), by simp⟩

private theorem box_add {e : Bool} {n : Nat} {v w : F → F} (hv : InBox e n v)
    (hw : InBox e n w) : InBox e n (fun z => v z + w z) := by
  obtain ⟨p, hp, pv⟩ := hv
  obtain ⟨r, hr, rw'⟩ := hw
  refine ⟨p+r, ?_, ?_⟩
  · rcases hp with rfl | hp
    · simpa using hr
    rcases hr with rfl | hr
    · exact Or.inr (by simpa using hp)
    exact Or.inr ((natDegree_add_le _ _).trans_lt (max_lt hp hr))
  · intro z; simp only [pv, rw', eval_add, mul_add]

private theorem box_scale {e : Bool} {n : Nat} {v : F → F} (c : F) (hv : InBox e n v) :
    InBox e n (fun z => c * v z) := by
  obtain ⟨p, hp, pv⟩ := hv
  refine ⟨C c * p, ?_, ?_⟩
  · rcases hp with rfl | hp
    · exact Or.inl (mul_zero _)
    exact Or.inr ((natDegree_C_mul_le c p).trans_lt hp)
  · intro z; simp only [pv, eval_mul, eval_C]; ring

private theorem box_times {e : Bool} {n m : Nat} (p : Polynomial F)
    (hp : p.natDegree ≤ m) {v : F → F} (hv : InBox e n v) :
    InBox e (n+m) (fun z => p.eval (z*z) * v z) := by
  obtain ⟨r, hr, rv⟩ := hv
  refine ⟨p*r, ?_, ?_⟩
  · rcases hr with rfl | hr
    · exact Or.inl (mul_zero _)
    have h := natDegree_mul_le (p := p) (q := r)
    exact Or.inr (by omega)
  · intro z; simp only [rv, eval_mul]; ring

private theorem box_extract {n : Nat} {v : F → F} (hv : InBox false n v) :
    InBox true n (fun z => z * v z) := by
  obtain ⟨p, hp, pv⟩ := hv
  exact ⟨p, hp, by simpa [pv]⟩

private noncomputable def affine (a b : F) : Polynomial F := C a + C b * Polynomial.X

private theorem affine_deg (a b : F) : (affine a b).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le (by simp)
  exact (natDegree_C_mul_le _ _).trans natDegree_X_le

private theorem affine_val (a b v : F) : (affine a b).eval v = a + b*v := by
  simp [affine]

-- 固定谱参数下的任意有限网格保留次数界，因为局部操作只使用加法和常数倍。
private theorem scatter_box {e : Bool} {n : Nat} (w : Weights F) (f : F → Bool → Bool → F)
    (hf : ∀ i j, InBox e n (fun z => f z i j)) (i j : Bool) :
    InBox e n (fun z => scatter w (f z) i j) := by
  by_cases h : i = j
  · simp only [scatter, h, ite_true]; exact box_scale _ (hf _ _)
  · simp only [scatter, h, ite_false]
    exact box_add (box_scale _ (hf _ _)) (box_scale _ (hf _ _))

private theorem folded_box {e : Bool} {n : Nat} (q d x : F) (cols : List F)
    (f : F → Bool → Site cols.length → F)
    (hf : ∀ i s, InBox e n (fun z => f z i s)) (i : Bool) (s : Site cols.length) :
    InBox e n (fun z => folded q d x cols (f z) i s) := by
  induction cols generalizing i with
  | nil => exact box_scale _ (hf _ _)
  | cons y ys ih =>
    obtain ⟨k,s⟩ := s
    apply scatter_box (spectral q x y)
    intro a b
    apply ih
    intro j t
    apply scatter_box (spectral q (x*y) 1)
    exact fun a k => hf a (k,t)

private theorem entry_box {e : Bool} {n : Nat} (q d x : F) (cols : List F) (i j : Bool)
    (f : F → Site cols.length → F) (hf : ∀ s, InBox e n (fun z => f z s)) (s : Site cols.length) :
    InBox e n (fun z => entry (folded q d x cols) i j (f z) s) := by
  apply folded_box
  intro b t
  by_cases hb : b = j
  · simpa only [hb, ite_true] using hf t
  · exact (by simpa [hb] using (box_zero e n (F := F)))

private theorem stack_box (q d : F) (cols rows : List F) (s : Site cols.length) :
    InBox false (2*rows.length+1) (fun z =>
      stackRows q d (z::cols) rows (fullSiteWeight _) (true,s)) ∧
    InBox true (2*rows.length) (fun z =>
      stackRows q d (z::cols) rows (fullSiteWeight _) (false,s)) := by
  induction rows generalizing s with
  | nil => exact ⟨box_const _, box_zero _ _⟩
  | cons x xs ih =>
    -- 进入和离开反射列的直行权均为 z² 的仿射函数，换向权正比于 z。
    let a := affine (q*q*x*x) (-1 : F)
    let b := affine (q*x*x) (-q)
    let a' := affine (-1 : F) (q*q*x*x)
    let b' := affine (-q) (q*x*x)
    let c := (q*q-1)*x
    have ain (z : F) : (spectral q x z).a = a.eval (z*z) := by simp [a, affine_val, spectral, sub_eq_add_neg]
    have bin (z : F) : (spectral q x z).b = b.eval (z*z) := by simp [b, affine_val, spectral]; ring
    have aout (z : F) : (spectral q (x*z) 1).a = a'.eval (z*z) := by simp [a', affine_val, spectral]; ring
    have bout (z : F) : (spectral q (x*z) 1).b = b'.eval (z*z) := by simp [b', affine_val, spectral]; ring
    have cin (z : F) : (spectral q x z).c = z*c := by simp [c, spectral]; ring
    have cout (z : F) : (spectral q (x*z) 1).c = z*c := by simp [c, spectral]; ring
    let inner (z : F) (k : Bool) (t : Site cols.length) :=
      stackRows q d (z::cols) xs (fullSiteWeight _) (k,t)
    let u := folded q d x cols
    have hu := folded_linear q d x cols
    have hEven (i j : Bool) := entry_box q d x cols i j (fun z => inner z true)
      (fun t => (ih t).1) s
    have hOdd := entry_box q d x cols true false (fun z => inner z false)
      (fun t => (ih t).2) s
    constructor
    · have hs := box_times a (affine_deg _ _)
        (box_times b' (affine_deg _ _) (hEven true false))
      rw [show 2*(x::xs).length+1 = 2*xs.length+1+1+1 by simp; omega]
      convert hs using 1
      funext z
      change create (addColumn q x z u) _ (true,s) = _
      rw [addColumn_occupied q x z hu, create_entry, ain, bout]
      simp only [inner, u]; ring
    · have hStay := box_times b (affine_deg _ _) (box_times a' (affine_deg _ _) hOdd)
      have hDirect := box_extract (box_times b (affine_deg _ _) (box_scale c (hEven true true)))
      have hSwap := box_extract (box_times b' (affine_deg _ _) (box_scale c (hEven false false)))
      have allTerms := box_add (box_add hStay hDirect) hSwap
      rw [show 2*(x::xs).length = 2*xs.length+1+1 by simp; omega]
      convert allTerms using 1
      funext z
      change create (addColumn q x z u) _ (false,s) = _
      rw [addColumn_vacant q x z hu, bin, aout, cin, cout, bout]
      simp only [inner, u]; ring

/-- 首列变量总能提取一个 z；其余关于 z² 的次数严格小于反射行对数的两倍。 -/
theorem domain_first_polynomial (q d : F) (rows cols : List F) :
    ∃ p : Polynomial F, (p = 0 ∨ p.natDegree < 2*rows.length) ∧
      ∀ z, domainPartition q d rows (z::cols) = z * p.eval (z*z) := by
  obtain ⟨p, hp, h⟩ := (stack_box q d cols rows (emptySite cols.length)).2
  exact ⟨p, hp, by simpa only [domainPartition, List.length_cons, emptySite, ite_true] using h⟩

end PolynomialBounds

end OeisA109074.Partial.SixVertex

end

section

namespace OeisA109074.Partial.Partition

open SixVertex
open scoped BigOperators

private instance siteFinite : (n : Nat) → Fintype (Site n)
  | 0 => (inferInstance : Fintype Unit)
  | n+1 => @instFintypeProd Bool (Site n) inferInstance (siteFinite n)

private instance siteEq : (n : Nat) → DecidableEq (Site n)
  | 0 => (inferInstance : DecidableEq Unit)
  | n+1 => @instDecidableEqProd Bool (Site n) inferInstance (siteEq n)

def asList : (n : Nat) → Site n → List Bool
  | 0, _ => []
  | n+1, (v,s) => v :: asList n s

@[simp] theorem asList_length (n : Nat) (s : Site n) : (asList n s).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => obtain ⟨v,s⟩ := s; simp [asList, ih]

private theorem sum_words (n : Nat) (f : List Bool → Nat) :
    ∑ s : Site n, f (asList n s) = Interlace.weightSum (Interlace.words n) f := by
  induction n generalizing f with
  | zero => change (∑ _ : Unit, f []) = _; simp [Interlace.words, Interlace.weightSum]
  | succ n ih =>
    change (∑ s : Bool × Site n, f (s.1 :: asList n s.2)) = _
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Interlace.word_sum]
    rw [ih (fun s => f (true :: s)), ih (fun s => f (false :: s))]
    omega

section Transfer

variable {R X : Type} [CommRing R] [Fintype X] [DecidableEq X]

def coeff (u : Transfer R X) (i : Bool) (s : X) (j : Bool) (t : X) : R :=
  u (fun a v => if a = j ∧ v = t then 1 else 0) i s

omit [Fintype X] [DecidableEq X] in
private theorem transfer_sum {u : Transfer R X} (hu : TransferLinear u) {ι : Type}
    (A : Finset ι) (g : ι → Bool → X → R) :
    u (fun a v => ∑ l ∈ A, g l a v) = fun a v => ∑ l ∈ A, u (g l) a v := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    simpa using hu.scale 0 (fun _ _ => 0)
  | insert l A hl ih =>
    simp only [Finset.sum_insert hl, hu.add, ih]

/-- 用有限状态基展开一个完整的反射转移。 -/
theorem coefficient_expansion {u : Transfer R X} (hu : TransferLinear u)
    (f : Bool → X → R) (i : Bool) (s : X) :
    u f i s = ∑ j : Bool, ∑ t : X, coeff u i s j t * f j t := by
  classical
  let term := fun (j : Bool) (t : X) (a : Bool) (v : X) =>
    f j t * (if a = j ∧ v = t then 1 else 0)
  have expand : f = fun a v => ∑ j : Bool, ∑ t : X, term j t a v := by
    funext a v
    simp [term, mul_ite, ite_and]
  conv => lhs; rw [expand, transfer_sum hu]
  simp only [transfer_sum hu, term, hu.scale, coeff, mul_comm]

def vertex (w : Weights R) (i v j t : Bool) : R :=
  scatter w (fun a b => if a = j ∧ b = t then 1 else 0) i v

private theorem scatter_expand (w : Weights R) (f : Bool → Bool → R) (i v : Bool) :
    scatter w f i v = ∑ j : Bool, ∑ t : Bool, vertex w i v j t * f j t := by
  cases i <;> cases v <;> simp [scatter, vertex, add_comm]

/-- 外侧一列有一个去程顶点和一个回程顶点，中间的垂直箭头在二者间共享。 -/
theorem coeff_add_column (q x z : R) (u : Transfer R X) (hu : TransferLinear u)
    (i j v t : Bool) (s e : X) :
    coeff (addColumn q x z u) i (v,s) j (t,e) =
      ∑ a : Bool, ∑ k : Bool, ∑ b : Bool,
        vertex (spectral q x z) i v a k * coeff u a s b e *
        vertex (spectral q (x*z) 1) b k j t := by
  classical
  simp only [coeff, addColumn]
  rw [scatter_expand]
  congr 1; ext a
  congr 1; ext k
  rw [coefficient_expansion hu]
  simp_rw [Finset.mul_sum]
  congr 1; ext b
  have he (w : X) : scatter (spectral q (x*z) 1)
        (fun c k' => if c = j ∧ (k',w) = (t,e) then 1 else 0) b k =
      if w = e then vertex (spectral q (x*z) 1) b k j t else 0 := by
    by_cases h : w = e
    · simp [h, vertex]
    · cases b <;> cases k <;> simp [scatter, h, Prod.mk.injEq]
  simp only [he, mul_ite, mul_zero]
  simp [← mul_assoc, coeff]

end Transfer

section Homogeneous

variable {R : Type} [CommRing R]

def bulkWeight (q : R) := (q*q-1)*q

def rowWeight (q : R) : Nat → R
  | 0 => q*q*q*q-1
  | n+1 => bulkWeight q * rowWeight q n * bulkWeight q

theorem rowWeight_formula (q : R) (n : Nat) :
    rowWeight q n = (q^4-1) * bulkWeight q ^ (2*n) := by
  induction n with
  | zero => simp [rowWeight]; ring
  | succ n ih => rw [rowWeight, ih, Nat.mul_succ, pow_add]; ring

private theorem bad_p_neg (p e f : Int) (s t : List Bool) :
    Interlace.two (-1) p e f s t = 0 := by apply Interlace.two_bad_start; decide
private theorem bad_p_two (p e f : Int) (s t : List Bool) :
    Interlace.two 2 p e f s t = 0 := by apply Interlace.two_bad_start; decide
private theorem bad_q_neg (p e f : Int) (s t : List Bool) :
    Interlace.two p (-1) e f s t = 0 := by apply Interlace.two_bad_second; decide
private theorem bad_q_two (p e f : Int) (s t : List Bool) :
    Interlace.two p 2 e f s t = 0 := by apply Interlace.two_bad_second; decide

/-- 两行权和中的右侧转弯固定向下。左端去程箭头取补，回程箭头直接
    给出另一行的起始前缀和。每一列正好贡献两个相同的局部权。 -/
theorem homogeneous_coefficient (q : R) (hq : q*q+1=q)
    (cs : List R) (hcs : ∀ z ∈ cs, z = 1)
    (i j : Bool) (s t : Site cs.length) :
    coeff (folded q (q*q) q cs) i s j t =
      rowWeight q cs.length *
        (Interlace.two (1-Interlace.bit i) (Interlace.bit j) 1 0
          (asList _ s) (asList _ t) : R) := by
  induction cs generalizing i j with
  | nil =>
    obtain ⟨⟩ := s; obtain ⟨⟩ := t
    cases i <;> cases j <;>
      simp [coeff, folded, bare, fixed_reflection, asList, Interlace.two_nil,
        Interlace.isBit, Interlace.bit, rowWeight]
  | cons z cs ih =>
    obtain rfl := hcs z (by simp)
    obtain ⟨v,s⟩ := s; obtain ⟨u,t⟩ := t
    have inner := ih (fun z hz => hcs z (List.mem_cons_of_mem _ hz))
    change coeff (addColumn q q 1 (folded q (q*q) q cs)) i (v,s) j (u,t) = _
    rw [coeff_add_column _ _ _ _ (folded_linear ..)]
    simp only [mul_one, equal_weights _ hq, inner, List.length_cons, asList,
      rowWeight, Interlace.two_cons]
    cases i <;> cases j <;> cases u <;> cases v <;>
      simp [vertex, scatter, Interlace.isBit, Interlace.bit, bulkWeight,
        bad_p_neg, bad_p_two, bad_q_neg, bad_q_two] <;> ring

private theorem create_homogeneous (q : R) (hq : q*q+1=q)
    (cs : List R) (hcs : ∀ z ∈ cs, z = 1) (f : Site cs.length → R) (s : Site cs.length) :
    create (folded q (q*q) q cs) f s =
      rowWeight q cs.length * ∑ t : Site cs.length,
        (Interlace.two 0 0 1 0 (asList _ s) (asList _ t) : R) * f t := by
  unfold create
  rw [coefficient_expansion (folded_linear ..)]
  simp [homogeneous_coefficient q hq cs hcs, Interlace.bit, Finset.mul_sum, mul_assoc]

@[simp] private theorem full_eq (n : Nat) (s : Site n) :
    fullSiteWeight (R := R) n s = if (asList n s).all id then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih => obtain ⟨v,s⟩ := s; cases v <;> simp [asList, fullSiteWeight, ih]

private theorem stack_homogeneous (q : R) (hq : q*q+1=q) (cols : List R)
    (hc : ∀ z ∈ cols, z = 1) (rows : List R) (hr : ∀ x ∈ rows, x = q)
    (s : Site cols.length) :
    stackRows q (q*q) cols rows (fullSiteWeight _) s =
      rowWeight q cols.length ^ rows.length *
      (Interlace.walk cols.length (2*rows.length) (asList _ s) 1 : R) := by
  induction rows generalizing s with
  | nil => simp [stackRows, Interlace.walk, apply_ite Nat.cast]
  | cons x xs ih =>
    obtain rfl := hr x (by simp)
    rw [stackRows, create_homogeneous _ hq _ hc]
    simp only [ih (fun y hy => hr y (List.mem_cons_of_mem _ hy)), List.length_cons,
      Nat.mul_succ, Interlace.walk_two_rows _ _ _ (asList_length ..), Int.reduceSub,
      ← sum_words, Nat.cast_sum, Nat.cast_mul, pow_succ]
    simp [Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]

@[simp] private theorem empty_list (n : Nat) :
    asList n (emptySite n) = List.replicate n false := by
  induction n <;> simp_all [emptySite, asList, List.replicate_succ]

private theorem first_condition (n : Nat) (s : Site n) :
    Interlace.admissible 0 0 (List.replicate n false) (asList n s) = true ↔ s = emptySite n := by
  have diff : Interlace.difference (List.replicate n false) (asList n s) =
      (asList n s).map Interlace.bit := by
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨v,s⟩ := s
      simpa [List.replicate_succ, Interlace.difference, asList, Interlace.bit] using ih s
  have nonneg : ∀ k (s : Site k), 0 ≤ ((asList k s).map Interlace.bit).sum := by
    intro k s
    induction k with
    | zero => simp [asList]
    | succ k ih =>
      obtain ⟨v,s⟩ := s
      cases v <;> simp [asList, Interlace.bit] <;> have := ih s <;> omega
  have sum0 (k : Nat) (s : Site k) : ((asList k s).map Interlace.bit).sum = 0 ↔ s = emptySite k := by
    induction k with
    | zero => obtain ⟨⟩ := s; simp [asList, emptySite]
    | succ k ih =>
      obtain ⟨v,s⟩ := s
      cases v <;> simp [asList, Interlace.bit, emptySite, ih] <;> have := nonneg k s <;> omega
  constructor
  · intro h
    exact (sum0 n s).mp (by simpa [Interlace.admissible, diff] using (Bool.and_eq_true_iff.mp h).2)
  · rintro rfl
    rw [Interlace.admissible, diff, empty_list]
    clear diff
    induction n <;> simp_all [List.replicate_succ, Interlace.bit, prefixOK]

private theorem peel_first (n k : Nat) : Interlace.walk n (k+1) (List.replicate n false) 0 =
    Interlace.walk n k (List.replicate n false) 1 := by
  rw [Interlace.walk, ← sum_words]
  simp [first_condition]

/-- 冰点同质化。整张 n×n 的反射双行网格经一个显式因子归一化后，
    给出原题的递归矩阵计数；等式保留公共因子，避免在零因子上除法。 -/
theorem domain_counts_vsasm (q : R) (hq : q*q+1=q) (n : Nat) :
    domainPartition q (q*q) (List.replicate n q) (List.replicate n 1) =
      ((q^4-1)*bulkWeight q ^ (2*n)) ^ n * (b n : R) := by
  rw [domainPartition, stack_homogeneous _ hq _ (by simp) _ (by simp)]
  simp only [List.length_replicate, rowWeight_formula, empty_list,
    Interlace.count_as_interlacing_walk, peel_first]

end Homogeneous

end OeisA109074.Partial.Partition

end

section

namespace OeisA109074.Confluence

open Polynomial Finset Matrix
open scoped BigOperators

/-- 齐次合流时，用平方节点上的首一多项式取代选择数的奇次多项式。 -/
noncomputable def nodePoly : ℕ → ℚ[X]
  | 0 => 1
  | j+1 => nodePoly j * (X - C (((j:ℚ)+1)^2))

private theorem node_monic (j : ℕ) : (nodePoly j).Monic := by
  induction j with
  | zero => exact monic_one
  | succ j ih => exact ih.mul (monic_X_sub_C _)

private theorem node_degree (j : ℕ) : (nodePoly j).natDegree = j := by
  induction j with
  | zero => simp [nodePoly]
  | succ j ih =>
    rw [nodePoly, natDegree_mul (node_monic j).ne_zero (monic_X_sub_C _).ne_zero,
      natDegree_X_sub_C, ih]

private theorem desc_pair (s j : ℕ) :
    ((s+j+1).descFactorial (2*j+3) : ℚ) =
      ((s+j).descFactorial (2*j+1) : ℚ) * ((s:ℚ)^2 - ((j:ℚ)+1)^2) := by
  rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
  by_cases h : 2*j+1 ≤ s+j
  · push_cast [Nat.cast_sub h]
    ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : s+j < 2*j+1)]
    simp

theorem factorial_choose_eval (s j : ℕ) :
    ((2*j+1).factorial : ℚ) * ((s+j).choose (2*j+1) : ℚ) =
      (s:ℚ) * (nodePoly j).eval ((s:ℚ)^2) := by
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose]
  induction j with
  | zero => simp [nodePoly]
  | succ j ih =>
    rw [show s+(j+1) = s+j+1 by omega, show 2*(j+1)+1 = 2*j+3 by omega,
      desc_pair, ih, nodePoly]
    simp [mul_assoc]

/-- 任意自然数节点的合流行列式，重复节点和 s<j 造成的零项也包括在内。 -/
theorem choose_determinant (m : ℕ) (s : Fin m → ℕ) :
    (∏ j : Fin m, ((2*j.val+1).factorial : ℚ)) *
      (Matrix.of (fun i j : Fin m => ((s i+j.val).choose (2*j.val+1) : ℚ))).det =
    (∏ i : Fin m, (s i : ℚ)) *
      ∏ i : Fin m, ∏ j ∈ Ioi i, ((s j:ℚ)^2 - (s i:ℚ)^2) := by
  let A := Matrix.of (fun i j : Fin m => ((s i+j.val).choose (2*j.val+1) : ℚ))
  let B := Matrix.of (fun i j : Fin m => (nodePoly j.val).eval ((s i:ℚ)^2))
  have he : (Matrix.of (fun i j : Fin m => ((2*j.val+1).factorial : ℚ) * A i j)) =
      Matrix.of (fun i j : Fin m => (s i : ℚ) * B i j) := by
    ext i j
    exact factorial_choose_eval (s i) j.val
  have h := congrArg Matrix.det he
  rw [Matrix.det_mul_column, Matrix.det_mul_row] at h
  change _ * A.det = _
  rw [h]
  congr 1
  rw [← Matrix.det_vandermonde]
  exact (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde _
    (fun j : Fin m => nodePoly j.val) (fun j => node_degree _) (fun j => node_monic _)).symm

section Newton

variable {K : Type} [CommRing K]

noncomputable def basis : {n : ℕ} → (Fin n → K) → Fin n → K[X]
  | 0, _, i => i.elim0
  | _+1, v, i => Fin.cases 1
      (fun j => (X-C (v 0)) * basis (fun k => v k.succ) j) i

/-- 除以首一一次多项式的商定义差商，节点重合时仍有定义。 -/
noncomputable def divided : {n : ℕ} → (Fin n → K) → K[X] → Fin n → K
  | 0, _, _, i => i.elim0
  | _+1, v, p, i => Fin.cases (p.eval (v 0))
      (fun j => divided (fun k => v k.succ) (p /ₘ (X-C (v 0))) j) i

private theorem basis_properties [IsDomain K] {n : ℕ} (v : Fin n → K) (i : Fin n) :
    (basis v i).Monic ∧ (basis v i).natDegree = i.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [basis]
    · have ⟨hm, hd⟩ := ih (fun k => v k.succ) j
      change ((X - C (v 0)) * _).Monic ∧ _
      exact ⟨(monic_X_sub_C _).mul hm, by
        simp [basis, natDegree_mul (monic_X_sub_C _).ne_zero hm.ne_zero, hd, Nat.add_comm]⟩

private theorem newton_eval {n : ℕ} (v : Fin n → K) (p : K[X]) (i : Fin n) :
    p.eval (v i) = ∑ j : Fin n, (basis v j).eval (v i) * divided v p j := by
  induction n generalizing p with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.sum_univ_succ]
      simp [basis, divided]
    · rw [Fin.sum_univ_succ]
      simp only [basis, divided, Fin.cases_zero, Fin.cases_succ, eval_one, one_mul,
        eval_mul, eval_sub, eval_X, eval_C, mul_assoc, ← Finset.mul_sum]
      rw [← ih (fun l => v l.succ) (p /ₘ (X-C (v 0))) k]
      have h := congrArg (fun f : K[X] => f.eval (v k.succ))
        (modByMonic_add_div p (X - C (v 0)))
      simpa [modByMonic_X_sub_C_eq_C_eval] using h.symm

noncomputable def normalizedAlternant {n : ℕ} (v : Fin n → K) (p : Fin n → K[X]) : K :=
  (Matrix.of (fun i j : Fin n => divided v (p j) i)).det

/-- 消去全部节点差。等式对节点重复的情形仍成立。 -/
theorem factor_alternant [IsDomain K] {n : ℕ} (v : Fin n → K) (p : Fin n → K[X]) :
    (Matrix.of (fun i j : Fin n => (p j).eval (v i))).det =
      (Matrix.vandermonde v).det * normalizedAlternant v p := by
  have he : Matrix.of (fun i j : Fin n => (p j).eval (v i)) =
      Matrix.of (fun i j : Fin n => (basis v j).eval (v i)) *
      Matrix.of (fun i j : Fin n => divided v (p j) i) := by
    ext i j
    exact newton_eval v (p j) i
  rw [he, Matrix.det_mul, ← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
    (basis v) (fun i => (basis_properties v i).2) (fun i => (basis_properties v i).1)]
  rfl

private theorem coeff_shift (p : K[X]) (a : K) (j : ℕ) :
    (taylor a (p /ₘ (X-C a))).coeff j = (taylor a p).coeff (j+1) := by
  have he := congrArg (taylor a) (modByMonic_add_div p (X-C a))
  rw [modByMonic_X_sub_C_eq_C_eval] at he
  have hh := congrArg (fun f : K[X] => f.coeff (j+1)) he
  simpa [taylor_mul, coeff_X_mul] using hh

theorem divided_constant {n : ℕ} (a : K) (p : K[X]) (i : Fin n) :
    divided (fun _ => a) p i = (taylor a p).coeff i.val := by
  induction n generalizing p with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [divided, taylor_coeff_zero]
    · simp [divided, ih, coeff_shift]

theorem normalized_constant {n : ℕ} (a : K) (p : Fin n → K[X]) :
    normalizedAlternant (fun _ => a) p =
      (Matrix.of (fun i j : Fin n => (taylor a (p j)).coeff i.val)).det := by
  simp [normalizedAlternant, divided_constant]

end Newton

/-- 第二类 Chebyshev 多项式取参数 X/2，使用整系数递推。 -/
noncomputable def character : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | n+2 => X * character (n+1) - character n

private theorem pascal_two (n k : ℕ) :
    (n+2).choose (k+2) + n.choose (k+2) =
      2 * (n+1).choose (k+2) + n.choose k := by
  rw [Nat.choose_succ_succ (n+1) (k+1), Nat.choose_succ_succ n (k+1),
      Nat.choose_succ_succ n k]
  simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd]
  omega

theorem character_coeff (m j : ℕ) :
    (taylor (2:ℚ) (character m)).coeff j = ((m+j+1).choose (2*j+1) : ℚ) := by
  induction m using Nat.twoStepInduction generalizing j with
  | zero =>
    cases j with
    | zero => simp [character]
    | succ j =>
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp [character, coeff_one]
  | one =>
    cases j with
    | zero => norm_num [character, taylor_X]
    | succ j =>
      cases j with
      | zero => norm_num [character, taylor_X]
      | succ j =>
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp [character, taylor_X, coeff_X]
  | more m h₀ h₁ =>
    rw [character, map_sub, taylor_mul, taylor_X, add_mul]
    cases j with
    | zero =>
      simp [h₀, h₁]
      ring
    | succ j =>
      simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul, h₀, h₁]
      have hp := pascal_two (m+j+2) (2*j+1)
      have he : ((m+j+2+2).choose (2*j+1+2) : ℚ) + (m+j+2).choose (2*j+1+2) =
          2 * ((m+j+2+1).choose (2*j+1+2) : ℚ) + (m+j+2).choose (2*j+1) := by
        exact_mod_cast hp
      simp only [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at he ⊢
      linarith

noncomputable def cubic : ℚ[X] := X^3 - 3*X

theorem character_cubic (m : ℕ) :
    cubic * character (m+3) = character (m+6) + character m := by
  unfold cubic
  simp only [show m+6 = (m+4)+2 by omega, character.eq_3,
    show m+4+1 = (m+3)+2 by omega]
  ring

/-- 交错排列两族列：1,X,F,XF,F²,XF²,…，其中 F=X³−3X。 -/
noncomputable def rawColumn : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | k+2 => cubic * rawColumn k

private noncomputable def decode : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  Polynomial.lsum fun k => (LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (rawColumn k)

private theorem decode_monomial (k : ℕ) (r : ℚ) :
    decode (monomial k r) = r • rawColumn k := by
  simp [decode, Polynomial.sum_monomial_index]

private theorem decode_shift (p : ℚ[X]) : decode (X^2 * p) = cubic * decode p := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [mul_add, hp, hr]
  | monomial k r =>
    rw [← monomial_one_right_eq_X_pow, monomial_mul_monomial, one_mul,
      Nat.add_comm 2 k, decode_monomial, decode_monomial, rawColumn, mul_smul_comm]

private noncomputable def encoding : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | 2 => X^2+X
  | 3 => X^3+1
  | k+4 => X^2 * encoding (k+2) - encoding k

private theorem decode_encoding (k : ℕ) :
    decode (encoding k) = character (k + k/2) := by
  have hp (n : ℕ) : decode (X^n) = rawColumn n := by
    rw [← monomial_one_right_eq_X_pow, decode_monomial, one_smul]
  have ho : decode 1 = 1 := by simpa [rawColumn] using hp 0
  have hx : decode X = X := by simpa [rawColumn] using hp 1
  match k with
  | 0 => exact ho
  | 1 => exact hx
  | 2 =>
    change decode (X^2+X) = character 3
    rw [map_add, hp, hx]
    simp [rawColumn, character, cubic]; ring
  | 3 =>
    change decode (X^3+1) = character 4
    rw [map_add, hp, ho]
    simp [rawColumn, character, cubic]; ring
  | k+4 =>
    rw [encoding, map_sub, decode_shift, decode_encoding (k+2), decode_encoding k]
    rw [show k+2+(k+2)/2 = k+k/2+3 by omega,
      show k+4+(k+4)/2 = k+k/2+6 by omega, character_cubic]
    ring
termination_by k

theorem raw_even (k : ℕ) : rawColumn (2*k) = cubic^k := by
  induction k with
  | zero => simp [rawColumn]
  | succ k ih => rw [Nat.mul_succ, rawColumn, ih, pow_succ']

theorem raw_odd (k : ℕ) : rawColumn (2*k+1) = X*cubic^k := by
  induction k with
  | zero => simp [rawColumn]
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+2 by omega, rawColumn, ih, pow_succ]; ring

private theorem encoding_properties (k : ℕ) : (encoding k).Monic ∧ (encoding k).natDegree = k := by
  match k with
  | 0 => simp [encoding]
  | 1 => simp [encoding]
  | 2 =>
    exact ⟨(monic_X_pow 2).add_of_left (by simp), natDegree_add_eq_left_of_natDegree_lt (by simp) |>.trans (by simp)⟩
  | 3 =>
    exact ⟨(monic_X_pow 3).add_of_left (by simp), natDegree_add_eq_left_of_natDegree_lt (by simp) |>.trans (by simp)⟩
  | k+4 =>
    obtain ⟨h1,h2⟩ := encoding_properties (k+2)
    obtain ⟨_,h3⟩ := encoding_properties k
    have hm := (monic_X_pow (R := ℚ) 2).mul h1
    have hd : (X^2 * encoding (k+2)).natDegree = k+4 := by
      rw [natDegree_mul (monic_X_pow 2).ne_zero h1.ne_zero, natDegree_X_pow, h2]; omega
    have lt : (encoding k).natDegree < (X^2 * encoding (k+2)).natDegree := by omega
    exact ⟨hm.sub_of_left (degree_lt_degree lt), (natDegree_sub_eq_left_of_natDegree_lt lt).trans hd⟩
termination_by k

private theorem character_expansion {n : ℕ} (j : Fin n) :
    character (j.val + j.val/2) =
      ∑ k : Fin n, (encoding j.val).coeff k.val • rawColumn k.val := by
  rw [← decode_encoding, Fin.sum_univ_eq_sum_range
    (fun k => (encoding j.val).coeff k • rawColumn k)]
  have hd := (encoding_properties j.val).2
  have he := (encoding j.val).as_sum_range' n (by omega)
  conv => lhs; rw [he]
  simp [decode_monomial]

/-- 两族列之间的变换是对角线为 1 的上三角矩阵，对任意线性观测都保持行列式。 -/
theorem character_basis_det {n : ℕ} (L : Fin n → ℚ[X] →ₗ[ℚ] ℚ) :
    (Matrix.of (fun i j : Fin n => L i (rawColumn j.val))).det =
    (Matrix.of (fun i j : Fin n => L i (character (j.val + j.val/2)))).det := by
  let A := Matrix.of (fun i j : Fin n => L i (rawColumn j.val))
  let U := Matrix.of (fun k j : Fin n => (encoding j.val).coeff k.val)
  have eqM : Matrix.of (fun i j : Fin n => L i (character (j.val+j.val/2))) = A * U := by
    ext i j
    change L i (character (j.val+j.val/2)) = _
    rw [character_expansion j]
    simp [A, U, Matrix.mul_apply, mul_comm]
  have upper : U.IsUpperTriangular := by
    intro i j hij
    exact coeff_eq_zero_of_natDegree_lt ((encoding_properties j.val).2.trans_lt hij)
  have diag (j : Fin n) : U j j = 1 := by
    obtain ⟨hm,hd⟩ := encoding_properties j.val
    change (encoding j.val).coeff j.val = 1
    simpa only [hd] using hm.coeff_natDegree
  rw [eqM, Matrix.det_mul, Matrix.det_of_isUpperTriangular upper]
  simp [diag, A]

theorem homogeneous_alternant (n : ℕ) :
    normalizedAlternant (fun _ : Fin n => (2:ℚ)) (fun j => rawColumn j.val) =
      (Matrix.of (fun i j : Fin n => (((j.val+j.val/2)+i.val+1).choose (2*i.val+1) : ℚ))).det := by
  rw [normalized_constant]
  have h := character_basis_det (fun i : Fin n => (lcoeff ℚ i.val).comp (taylor (2:ℚ)))
  simpa [character_coeff] using h

/-- 归一化交错行列式在所有节点同时取 2 时的无分母乘积公式。 -/
theorem homogeneous_product (n : ℕ) :
    (∏ j : Fin n, ((2*j.val+1).factorial : ℚ)) *
        normalizedAlternant (fun _ : Fin n => (2:ℚ)) (fun j => rawColumn j.val) =
      (∏ j : Fin n, ((j.val + j.val/2 + 1 : ℕ) : ℚ)) *
      ∏ i : Fin n, ∏ j ∈ Ioi i,
        (((j.val + j.val/2 + 1 : ℕ) : ℚ)^2 - ((i.val + i.val/2 + 1 : ℕ) : ℚ)^2) := by
  rw [homogeneous_alternant, ← Matrix.det_transpose]
  simpa [Matrix.transpose, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    choose_determinant n (fun j => j.val + j.val/2 + 1)

theorem divided_map {K F : Type} [CommRing K] [CommRing F] (φ : K →+* F)
    {n : ℕ} (v : Fin n → K) (p : K[X]) (i : Fin n) :
    φ (divided v p i) = divided (fun j => φ (v j)) (p.map φ) i := by
  induction n generalizing p with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [divided]
    · simp [divided, ih, map_divByMonic φ (monic_X_sub_C _)]

theorem normalized_map {K F : Type} [CommRing K] [CommRing F] (φ : K →+* F)
    {n : ℕ} (v : Fin n → K) (p : Fin n → K[X]) :
    φ (normalizedAlternant v p) =
      normalizedAlternant (fun i => φ (v i)) (fun j => (p j).map φ) := by
  unfold normalizedAlternant
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  exact divided_map φ v (p j) i

end OeisA109074.Confluence

end

section

/-!
Kuperberg 定理 10 的 U 型核为 1/Uᵢⱼ − 1/Vᵢⱼ。
在每行清除分母后，行列式在冻结点仍有定义，可直接沿首行展开。
-/
namespace OeisA109074.Tsuchiya

open scoped BigOperators
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- 每一行同时乘上该行所有分母后的矩阵。 -/
def cleared (N D : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => N i j * ∏ k, if k = j then 1 else D i k

def tail (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : Matrix (Fin n) (Fin n) R :=
  A.submatrix Fin.succ Fin.succ

/-- 此式在任意交换环中成立，故可用于谱参数特化产生分母零点的情形。 -/
theorem det_cleared_freeze (N D : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (h : D 0 0 = 0) :
    (cleared N D).det = N 0 0 * (∏ j : Fin n, D 0 j.succ) *
      (∏ i : Fin n, D i.succ 0) * (cleared (tail N) (tail D)).det := by
  have off (j : Fin (n+1)) (hj : j ≠ 0) : cleared N D 0 j = 0 := by
    simp [cleared, Fin.prod_univ_succ, Ne.symm hj, h]
  have corner : cleared N D 0 0 = N 0 0 * ∏ j : Fin n, D 0 j.succ := by
    simp [cleared, Fin.prod_univ_succ]
  have minor : (cleared N D).submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j : Fin n => D i.succ 0 * cleared (tail N) (tail D) i j) := by
    ext i j
    simp [cleared, tail, Fin.prod_univ_succ, Ne.symm (Fin.succ_ne_zero j), mul_left_comm]
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (0 : Fin (n+1))]
  · simp [corner, minor, Matrix.det_mul_column, mul_assoc]
  · intro j _ hj
    rw [off j hj]
    simp
  · simp

section Field
variable {K : Type*} [Field K]

/-- 普通参数处，正则化行列式正好把所有单元的分母乘入原行列式。 -/
theorem det_cleared_eq (N D : Matrix (Fin n) (Fin n) K) (hd : ∀ i j, D i j ≠ 0) :
    (cleared N D).det = (∏ i, ∏ j, D i j) * (Matrix.of fun i j => N i j / D i j).det := by
  rw [← Matrix.det_mul_column]
  congr 1
  ext i j
  simp only [cleared, Matrix.of_apply]
  have exclude : (∏ k, if k = j then 1 else D i k) = ∏ k ∈ Finset.univ.erase j, D i k := by
    rw [← Finset.prod_erase_mul Finset.univ (fun k => if k = j then 1 else D i k)
      (Finset.mem_univ j)]
    simp only [ite_true, mul_one]
    apply Finset.prod_congr rfl
    intro k hk
    simp [Finset.ne_of_mem_erase hk]
  rw [exclude, ← Finset.prod_erase_mul Finset.univ (D i) (Finset.mem_univ j)]
  field_simp [hd]

def sigma (u : K) := u - u⁻¹
def traceSq (u : K) := u^2 + (u⁻¹)^2
def alpha (a u : K) := sigma (a*u) * sigma (a/u)
def quad (g X Y : K) := X^2 + Y^2 - g*X*Y + g^2 - 4

theorem alpha_pair (a x y : K) (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    alpha a (x/y) * alpha a (x*y) = quad (traceSq a) (traceSq x) (traceSq y) := by
  unfold alpha sigma quad traceSq
  field_simp
  ring

theorem alpha_diff (a x y : K) (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    alpha a (x*y) - alpha a (x/y) = - sigma (x^2) * sigma (y^2) := by
  unfold alpha sigma
  field_simp
  ring

theorem vandermonde_pair (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    sigma (x/y) * sigma (x*y) = traceSq x - traceSq y := by
  unfold sigma traceSq
  field_simp
  ring

theorem quad_ice (X Y : K) :
    (X-Y) * quad (-1) X Y = (X^3-3*X) - (Y^3-3*Y) := by
  unfold quad
  ring

def core (g : K) (x y : Fin n → K) :=
  (cleared (Matrix.of fun _ _ : Fin n => (1:K))
    (Matrix.of fun i j => quad g (x i) (y j))).det

theorem core_freeze (g : K) (x y : Fin (n+1) → K) (h : quad g (x 0) (y 0) = 0) :
    core g x y = (∏ j : Fin n, quad g (x 0) (y j.succ)) *
      (∏ i : Fin n, quad g (x i.succ) (y 0)) *
      core g (fun i => x i.succ) (fun j => y j.succ) := by
  simpa [core, tail, Matrix.submatrix] using det_cleared_freeze (Matrix.of fun _ _ : Fin (n+1) => (1:K))
    (Matrix.of fun i j => quad g (x i) (y j)) h

/-- 两组交错因子都按后一参数减前一参数取向；它们的乘积与同时反向相同。 -/
def vand : {m : ℕ} → (Fin m → K) → K
  | 0, _ => 1
  | m+1, x => (∏ i : Fin m, (x i.succ - x 0)) * vand (fun i => x i.succ)

theorem vand_ne_zero (x : Fin n → K) (hinj : Function.Injective x) : vand x ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero
  | succ m ih =>
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      exact fun i _ => sub_ne_zero.mpr (hinj.ne (Fin.succ_ne_zero i))
    · exact ih _ (hinj.comp (Fin.succ_injective _))

/-- 此商用于互异参数，重合的齐次极限需要其多项式延拓。 -/
def normalize (g : K) (x y : Fin n → K) := core g x y / (vand x * vand y)

theorem normalized_freeze (g : K) (x y : Fin (n+1) → K)
    (hx : Function.Injective x) (hy : Function.Injective y) (h : quad g (x 0) (y 0) = 0) :
    normalize g x y =
      (∏ j : Fin n, (y j.succ + y 0 - g*x 0)) *
      (∏ i : Fin n, (x i.succ + x 0 - g*y 0)) *
      normalize g (fun i => x i.succ) (fun j => y j.succ) := by
  have col (j : Fin n) : quad g (x 0) (y j.succ) =
      (y j.succ - y 0) * (y j.succ + y 0 - g*x 0) := by
    unfold quad at *
    linear_combination h
  have row (i : Fin n) : quad g (x i.succ) (y 0) =
      (x i.succ - x 0) * (x i.succ + x 0 - g*y 0) := by
    unfold quad at *
    linear_combination h
  have dx : (∏ i : Fin n, (x i.succ - x 0)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    exact fun i _ => sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
  have dy : (∏ j : Fin n, (y j.succ - y 0)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    exact fun j _ => sub_ne_zero.mpr (hy.ne (Fin.succ_ne_zero j))
  unfold normalize
  rw [core_freeze _ _ _ h]
  simp only [vand]
  simp only [col, row, Finset.prod_mul_distrib]
  field_simp [dx, dy, vand_ne_zero _ (hx.comp (Fin.succ_injective _)),
    vand_ne_zero _ (hy.comp (Fin.succ_injective _))]

theorem freeze_spectral (a x : K) (ha : a ≠ 0) (hx : x ≠ 0) :
    quad (traceSq a) (traceSq x) (traceSq (a*x)) = 0 ∧
    quad (traceSq a) (traceSq x) (traceSq (a/x)) = 0 := by
  unfold quad traceSq
  constructor <;> field_simp <;> ring

/-! 下列定义使用本地六顶点权 a=q²x²−z², b=q(x²−z²), c=(q²−1)xz。 -/
def crossingTrace (q x : K) := q*x^2 + (q*x^2)⁻¹
def anisotropy (q : K) := q + q⁻¹
def weightA (q x z : K) := q^2*x^2 - z^2
def weightB (q x z : K) := q*(x^2-z^2)
def weightC (q x z : K) := (q^2-1)*x*z
def prefOne (q d x z : K) := q*(q^2-1)*x*z*(x^4-1)*(d*z^2-1)
def prefPair (q x z u v : K) := -(q^4)*(x*z)^2*(u*v)^2

def prefactor (q d : K) : {m : ℕ} → (Fin m → K) → (Fin m → K) → K
  | 0, _, _ => 1
  | m+1, x, z => prefOne q d (x 0) (z 0) *
      (∏ i : Fin m, prefPair q (x 0) (z 0) (x i.succ) (z i.succ)) *
      prefactor q d (fun i => x i.succ) (fun j => z j.succ)

def candidate (q d : K) (x z : Fin n → K) :=
  prefactor q d x z * normalize (anisotropy q) (fun i => crossingTrace q (x i))
    (fun j => traceSq (z j))

theorem native_freeze_point (q z : K) (hq : q ≠ 0) (hz : z ≠ 0) :
    quad (anisotropy q) (crossingTrace q z) (traceSq z) = 0 := by
  unfold quad anisotropy crossingTrace traceSq
  field_simp
  ring

private theorem freeze_pair (q z u v : K) (hq : q ≠ 0) (hz : z ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    prefPair q z z u v *
      (traceSq v + traceSq z - anisotropy q * crossingTrace q z) *
      (crossingTrace q u + crossingTrace q z - anisotropy q * traceSq z) =
    weightA q z v * weightA q (z*v) 1 * weightA q u z * weightB q (u*z) 1 := by
  unfold prefPair anisotropy crossingTrace traceSq weightA weightB
  field_simp
  ring

/-- 两个谱参数相等时的全行列式候选递推，保留边界与每一条谱线的权。 -/
theorem candidate_freeze (q d : K) (x z : Fin (n+1) → K) (hq : q ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hz : ∀ j, z j ≠ 0)
    (ix : Function.Injective fun i => crossingTrace q (x i))
    (iz : Function.Injective fun j => traceSq (z j)) (h : x 0 = z 0) :
    candidate q d x z =
      weightC q (z 0) (z 0) * weightB q ((z 0)^2) 1 * (d*(z 0)^2-1) *
      (∏ j : Fin n, (weightA q (z 0) (z j.succ) * weightA q (z 0 * z j.succ) 1)) *
      (∏ i : Fin n, (weightA q (x i.succ) (z 0) * weightB q (x i.succ * z 0) 1)) *
      candidate q d (fun i => x i.succ) (fun j => z j.succ) := by
  have hf : quad (anisotropy q) (crossingTrace q (x 0)) (traceSq (z 0)) = 0 :=
    h ▸ native_freeze_point q (z 0) hq (hz 0)
  have ho : prefOne q d (z 0) (z 0) =
      weightC q (z 0) (z 0) * weightB q ((z 0)^2) 1 * (d*(z 0)^2-1) := by
    unfold prefOne weightC weightB
    ring
  unfold candidate
  rw [normalized_freeze _ _ _ ix iz hf, prefactor]
  simp only [h, ho]
  have cross := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin n) _ => freeze_pair q (z 0) (x i.succ) (z i.succ) hq (hz 0) (hx _) (hz _))
  simp only [Finset.prod_mul_distrib] at cross ⊢
  linear_combination (weightC q (z 0) (z 0) * weightB q ((z 0)^2) 1 * (d*(z 0)^2-1) *
    prefactor q d (fun i => x i.succ) (fun j => z j.succ) *
    normalize (anisotropy q) (fun i => crossingTrace q (x i.succ))
      (fun j => traceSq (z j.succ))) * cross

section Interpolation

open Polynomial

private noncomputable def quadP (g a : K) : K[X] :=
  C (a^2+g^2-4) + X^2 - C (g*a)*X

private def rowRest (g a : K) (y : Fin n → K) (j : Fin n) : K :=
  ∏ k, if k = j then 1 else quad g a (y k)

private noncomputable def coreMatrixP (g : K) (x : Fin (n+1) → K) (y : Fin n → K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K[X] :=
  Matrix.of fun i => Fin.cons (C (∏ l, quad g (x i) (y l))) fun j =>
    quadP g (x i) * C (rowRest g (x i) y j)

private theorem eval_coreMatrixP (g Y : K) (x : Fin (n+1) → K) (y : Fin n → K) :
    ((coreMatrixP g x y).det).eval Y = core g x (Fin.cons Y y) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  unfold core
  congr 1
  ext i j
  induction j using Fin.cases with
  | zero =>
    simp [coreMatrixP, cleared, RingHom.mapMatrix_apply, Fin.prod_univ_succ, Polynomial.eval_prod]
  | succ j =>
    simp [coreMatrixP, cleared, RingHom.mapMatrix_apply, Fin.prod_univ_succ,
      Ne.symm (Fin.succ_ne_zero j), quadP, rowRest, quad, Polynomial.eval_prod]
    left
    ring

private theorem coreMatrixP_degree (g : K) (x : Fin (n+1) → K) (y : Fin n → K) :
    ((coreMatrixP g x y).det).natDegree ≤ 2*n := by
  have bound (i j : Fin (n+1)) :
      ((coreMatrixP g x y) i j).natDegree ≤ if j = 0 then 0 else 2 := by
    induction j using Fin.cases with
    | zero => simp only [coreMatrixP, Matrix.of_apply, Fin.cons_zero, natDegree_C, ite_true, le_refl]
    | succ j =>
      simp [coreMatrixP, quadP]
      compute_degree
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro p _
  apply (Polynomial.natDegree_mul_le ..).trans
  simp only [natDegree_intCast, zero_add]
  apply (Polynomial.natDegree_prod_le ..).trans
  calc
    _ ≤ ∑ j : Fin (n+1), (if j = 0 then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j _ => bound (p j) j
    _ = 2*n := by simp [Fin.sum_univ_succ, Nat.mul_comm]

private theorem core_zero_of_eq (g : K) (x y : Fin n → K) {a b : Fin n}
    (hne : a ≠ b) (hy : y a = y b) : core g x y = 0 := by
  unfold core
  apply Matrix.det_zero_of_column_eq hne
  intro i
  simp only [cleared, Matrix.of_apply, one_mul]
  apply Finset.prod_equiv (Equiv.swap a b) (by simp)
  intro k _
  by_cases ka : k = a
  · simp [ka]
  by_cases kb : k = b
  · simp [kb, Ne.symm hne, hne, hy]
  · simp [Equiv.swap_apply_of_ne_of_ne ka kb, ka, kb]

/-- 清除两组范德蒙因子后，商在任一单独的迹参数中为次数至多 n 的多项式
    （总共有 n+1 列）。在首参数和其他点重合时，由多项式提供延拓。 -/
theorem normalize_polynomial (g : K) (x : Fin (n+1) → K) (y : Fin n → K)
    (hy : Function.Injective y) : ∃ p : K[X], p.natDegree ≤ n ∧
    ∀ Y, (∀ j, Y ≠ y j) → normalize g x (Fin.cons Y y) = p.eval Y := by
  let P := (coreMatrixP g x y).det
  let D := Lagrange.nodal Finset.univ y
  have hD : D ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      exact (sub_ne_zero.mpr (hy.ne hij)).isUnit
    · intro j _
      apply Polynomial.dvd_iff_isRoot.mpr
      change P.eval (y j) = 0
      rw [show P = _ from rfl, eval_coreMatrixP]
      exact core_zero_of_eq _ _ _ (Ne.symm (Fin.succ_ne_zero j)) (by simp)
  obtain ⟨Q, hQ⟩ := hD
  have hdeg : Q.natDegree ≤ n := by
    by_cases hz : Q = 0
    · simp [hz]
    have hn := coreMatrixP_degree g x y
    change P.natDegree ≤ 2*n at hn
    rw [hQ, Polynomial.natDegree_mul (by exact Lagrange.nodal_ne_zero) hz] at hn
    simp [D, Lagrange.natDegree_nodal] at hn
    omega
  refine ⟨C (((-1 : K)^n) / (vand x * vand y)) * Q, ?_, ?_⟩
  · exact (Polynomial.natDegree_mul_le ..).trans (by simpa using hdeg)
  · intro Y hY
    have nz : D.eval Y ≠ 0 :=
      Lagrange.eval_nodal_not_at_node fun i _ => hY i
    have vf : vand (Fin.cons Y y) = (-1 : K)^n * D.eval Y * vand y := by
      rw [vand]
      simp only [Fin.cons_zero, Fin.cons_succ, D, Lagrange.eval_nodal]
      congr 1
      calc
        _ = ∏ j, ((-1 : K) * (Y - y j)) := Finset.prod_congr rfl (fun j _ => by ring)
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    unfold normalize
    rw [← eval_coreMatrixP]
    change P.eval Y / _ = _
    rw [hQ, Polynomial.eval_mul, vf]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    have hsign : ((-1 : K)^n) * (-1)^n = 1 := by rw [← mul_pow]; simp
    by_cases hx : vand x = 0
    · simp [hx]
    field_simp [hx, nz, vand_ne_zero _ hy]
    linear_combination -Q.eval Y * hsign

private theorem prefactor_first (q d : K) (x : Fin (n+1) → K) (zs : Fin n → K) :
    ∃ scalar : K, ∀ z, prefactor q d x (Fin.cons z zs) =
        scalar * z^(2*n+1) * (d*z^2-1) := by
  refine ⟨q*(q^2-1)*x 0*((x 0)^4-1) *
    (∏ i : Fin n, prefPair q (x 0) 1 (x i.succ) (zs i)) *
    prefactor q d (fun i => x i.succ) zs, ?_⟩
  intro z
  have pair (i : Fin n) : prefPair q (x 0) z (x i.succ) (zs i) =
      z^2 * prefPair q (x 0) 1 (x i.succ) (zs i) := by unfold prefPair; ring
  rw [prefactor]
  simp only [Fin.cons_zero, Fin.cons_succ, pair, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, prefOne, ← pow_mul]
  ring

private noncomputable def liftTrace (p : K[X]) (n : ℕ) :=
  ∑ k ∈ Finset.range (n+1), C (p.coeff k) * (X^2+1)^k * X^(n-k)

private theorem liftTrace_degree (p : K[X]) (n : ℕ) :
    (liftTrace p n).natDegree ≤ 2*n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hbase : (X^2+1 : K[X]).natDegree ≤ 2 := by compute_degree
  apply (Polynomial.natDegree_mul_le ..).trans
  apply le_trans (Nat.add_le_add_right (Polynomial.natDegree_mul_le ..) _)
  simp only [natDegree_C, zero_add, natDegree_pow, natDegree_X, mul_one]
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left k hbase) _).trans (by omega)

private theorem eval_liftTrace (p : K[X]) (n : ℕ) (hn : p.natDegree ≤ n)
    (t : K) (ht : t ≠ 0) :
    (liftTrace p n).eval t = t^n * p.eval (t+t⁻¹) := by
  rw [liftTrace, Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (n := n+1) (by omega) (t+t⁻¹)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using hk
  have hpow : t^n = t^k * t^(n-k) := by rw [← pow_add, Nat.add_sub_of_le hkn]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
  rw [hpow, show t+t⁻¹ = (t^2+1)/t by field_simp, div_pow]
  field_simp

/-- 与双行网格相同的插值次数界。对固定的其他参数，首列贡献为
    z·p(z²)，其中 deg p ≤ 2n+1；此处共有 n+1 对行。 -/
theorem candidate_first_polynomial (q d : K) (x : Fin (n+1) → K) (zs : Fin n → K)
    (hy : Function.Injective fun j => traceSq (zs j)) :
    ∃ p : K[X], p.natDegree ≤ 2*n+1 ∧ ∀ z, z ≠ 0 →
      (∀ j, traceSq z ≠ traceSq (zs j)) →
      candidate q d x (Fin.cons z zs) = z * p.eval (z^2) := by
  obtain ⟨P, hp, he⟩ := normalize_polynomial (anisotropy q)
    (fun i => crossingTrace q (x i)) (fun i => traceSq (zs i)) hy
  obtain ⟨A, ha⟩ := prefactor_first q d x zs
  refine ⟨C A * (C d * X - 1) * liftTrace P n, ?_, ?_⟩
  · have ha1 : (C A * (C d * X - 1)).natDegree ≤ 1 := by compute_degree
    exact (Polynomial.natDegree_mul_le ..).trans
      ((Nat.add_le_add ha1 (liftTrace_degree P n)).trans (by omega))
  · intro z hz hdistinct
    have hc : (fun j : Fin (n+1) => traceSq (Fin.cons (α := fun _ => K) z zs j)) =
        (Fin.cons (α := fun _ : Fin (n+1) => K) (traceSq z) (fun j => traceSq (zs j))) := by
      funext j; induction j using Fin.cases <;> simp
    rw [candidate, hc, ha, he _ hdistinct]
    simp only [Polynomial.eval_mul, eval_C, eval_sub, eval_X, eval_one,
      eval_liftTrace _ _ hp _ (pow_ne_zero _ hz), traceSq, inv_pow]
    ring

end Interpolation

section Alternant
open Polynomial

def cubic (t : K) := t^3 - 3*t

/-- 前 n 列是 f^k，后 n 列是 t f^k，纵向拼接 x 与 y 两组取值。 -/
noncomputable def cubicAlternant (x y : Fin n → K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  let A := Matrix.vandermonde (fun i => cubic (x i))
  let B := Matrix.vandermonde (fun i => cubic (y i))
  Matrix.fromBlocks A (Matrix.diagonal x * A) B (Matrix.diagonal y * B)

private noncomputable def interpolateMatrix (t u : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (Lagrange.basis Finset.univ t j).eval (u i)

private theorem interpolation_mul (t u : Fin n → K) (ht : Function.Injective t) :
    interpolateMatrix t u * Matrix.vandermonde t = Matrix.vandermonde u := by
  ext i j
  have deg : ((X : K[X])^j.val).degree < (Finset.univ : Finset (Fin n)).card := by
    simp
  have h := congrArg (Polynomial.eval (u i))
    (Lagrange.eq_interpolate (f := (X : K[X])^j.val)
      (s := Finset.univ) (v := t) ht.injOn deg)
  simpa [interpolateMatrix, Matrix.mul_apply, Matrix.vandermonde_apply, Lagrange.interpolate_eq_sum,
    Polynomial.eval_finsetSum, mul_comm] using h.symm

private theorem schur_alternant (x y : Fin n → K) (t u : Fin n → K)
    (ht : Function.Injective t) :
    (Matrix.fromBlocks (Matrix.vandermonde t) (Matrix.diagonal x * Matrix.vandermonde t)
      (Matrix.vandermonde u) (Matrix.diagonal y * Matrix.vandermonde u)).det =
    (Matrix.vandermonde t).det^2 *
      (Matrix.of fun i j => (y i - x j) * (interpolateMatrix t u) i j).det := by
  let A := Matrix.vandermonde t
  let L := interpolateMatrix t u
  have factor :
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) K) (Matrix.diagonal x) L
        (Matrix.diagonal y * L) * Matrix.fromBlocks A 0 0 A =
      Matrix.fromBlocks A (Matrix.diagonal x * A) (Matrix.vandermonde u)
        (Matrix.diagonal y * Matrix.vandermonde u) := by
    simp [Matrix.fromBlocks_multiply, A, L, Matrix.mul_assoc, interpolation_mul t u ht]
  have sc : Matrix.diagonal y * L - L * Matrix.diagonal x =
      Matrix.of fun i j => (y i - x j) * (interpolateMatrix t u) i j := by
    ext i j
    simp [L, Matrix.diagonal_mul, Matrix.mul_diagonal, sub_mul, mul_comm]
  rw [← factor, Matrix.det_mul, Matrix.det_fromBlocks_one₁₁, sc, Matrix.det_fromBlocks_zero₁₂]
  dsimp [A]
  ring

def differenceProd (t : Fin n → K) (i : Fin n) :=
  ∏ k ∈ Finset.univ.erase i, (t i - t k)

private theorem lagrange_kernel (t u : Fin n → K) (ht : Function.Injective t) (i j : Fin n) :
    interpolateMatrix t u i j * differenceProd t j =
      ∏ k ∈ Finset.univ.erase j, (u i - t k) := by
  simp only [interpolateMatrix, Matrix.of_apply, differenceProd, Lagrange.basis, Polynomial.eval_prod,
    Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have ne : t j - t k ≠ 0 := sub_ne_zero.mpr (ht.ne (Finset.ne_of_mem_erase hk).symm)
  field_simp [ne]

private theorem cleared_transpose (D : Matrix (Fin n) (Fin n) K) (hd : ∀ i j, D i j ≠ 0) :
    (cleared (Matrix.of fun _ _ => (1 : K)) D.transpose).det =
      (cleared (Matrix.of fun _ _ => (1 : K)) D).det := by
  rw [det_cleared_eq _ D.transpose (fun i j => hd j i), det_cleared_eq _ D hd]
  congr 1
  · simpa only [Matrix.transpose_apply] using
      (Finset.prod_comm (s := Finset.univ) (t := Finset.univ) (f := fun i j => D j i))
  · rw [← Matrix.det_transpose (Matrix.of fun i j => (Matrix.of (fun _ _ => (1 : K))) i j / D i j)]
    rfl

theorem cubic_alternant_det (x y : Fin n → K)
    (hinj : Function.Injective fun i => cubic (x i))
    (hq : ∀ i j, quad (-1) (x i) (y j) ≠ 0) :
    (cubicAlternant x y).det * (∏ j, differenceProd (fun k => cubic (x k)) j) =
      (Matrix.vandermonde (fun j => cubic (x j))).det^2 *
      (∏ i, ∏ j, (y i - x j)) * core (-1) x y := by
  let t := fun i => cubic (x i)
  let u := fun i => cubic (y i)
  let D : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => quad (-1) (x i) (y j)
  let S : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (y i - x j) * interpolateMatrix t u i j
  have entry (i j : Fin n) :
      differenceProd t j * S i j =
        (∏ k, (y i - x k)) * (cleared (Matrix.of fun _ _ => (1 : K)) D.transpose) i j := by
    change differenceProd t j * ((y i - x j) * interpolateMatrix t u i j) = _
    rw [show differenceProd t j * ((y i-x j)*interpolateMatrix t u i j) =
      (y i-x j)*(interpolateMatrix t u i j * differenceProd t j) by ring, lagrange_kernel _ _ hinj]
    have fact (k : Fin n) : u i - cubic (x k) = (y i - x k) * D k i := by
      dsimp [u,t,D,cubic,quad]
      ring
    simp only [fact, Finset.prod_mul_distrib, cleared, Matrix.of_apply, one_mul, Matrix.transpose_apply]
    have erase : (∏ k, if k = j then 1 else D k i) = ∏ k ∈ Finset.univ.erase j, D k i := by
      rw [← Finset.prod_erase_mul Finset.univ (fun k => if k = j then 1 else D k i) (Finset.mem_univ j)]
      simp only [ite_true, mul_one]
      exact Finset.prod_congr rfl fun k hk => by simp [Finset.ne_of_mem_erase hk]
    rw [erase, ← Finset.prod_erase_mul Finset.univ (fun k => y i - x k) (Finset.mem_univ j)]
    ring
  have scales : (Matrix.of fun i j => differenceProd t j * S i j) =
      (Matrix.of fun i j => (∏ k, (y i - x k)) *
        (cleared (Matrix.of fun _ _ => (1 : K)) D.transpose) i j) := by
    ext i j; exact entry i j
  have dets := congrArg Matrix.det scales
  rw [Matrix.det_mul_row, Matrix.det_mul_column, cleared_transpose D hq] at dets
  rw [cubicAlternant, schur_alternant _ _ _ _ hinj]
  change (Matrix.vandermonde t).det^2 * S.det * _ = _
  change (∏ j, differenceProd t j) * S.det = _ * core (-1) x y at dets
  linear_combination (Matrix.vandermonde t).det^2 * dets

theorem vand_eq_det (t : Fin n → K) : vand t = (Matrix.vandermonde t).det := by
  rw [Matrix.det_vandermonde]
  have upper {m : ℕ} (v : Fin m → K) (i : Fin m) :
      (∏ j ∈ Finset.Ioi i, (v j - v i)) = ∏ j, if i < j then v j - v i else 1 := by
    simpa only [Finset.mem_Ioi] using
      (Finset.prod_ite_mem_eq (Finset.Ioi i) (fun j => v j - v i)).symm
  simp only [upper]
  induction n with
  | zero => simp [vand]
  | succ m ih =>
    rw [vand, Fin.prod_univ_succ, ih (fun i => t i.succ)]
    have pos (i : Fin m) : 0 < i.succ := by exact Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero i)
    simp only [Fin.prod_univ_succ, lt_irrefl, ite_false, pos, ite_true,
      one_mul, Fin.not_lt_zero, Fin.succ_lt_succ_iff]

private theorem differenceProd_ite (t : Fin n → K) (i : Fin n) :
    differenceProd t i = ∏ k, if k = i then 1 else t i - t k := by
  rw [differenceProd, ← Finset.prod_erase_mul Finset.univ
    (fun k => if k = i then 1 else t i - t k) (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  exact Finset.prod_congr rfl fun k hk => by simp [Finset.ne_of_mem_erase hk]

def blockSign (K : Type*) [Field K] : ℕ → K
  | 0 => 1
  | n+1 => (-1)^n * blockSign K n

theorem blockSign_sq (m : ℕ) : (blockSign K m)^2 = 1 := by
  induction m with
  | zero => simp [blockSign]
  | succ m ih => rw [blockSign, mul_pow, ih, mul_one, ← pow_mul, Nat.mul_comm, pow_mul]; simp

theorem differenceProd_all (t : Fin n → K) :
    (∏ j, differenceProd t j) = blockSign K n * (vand t)^2 := by
  induction n with
  | zero => simp [vand, blockSign]
  | succ m ih =>
    rw [Fin.prod_univ_succ, vand, blockSign]
    have first : differenceProd t 0 = (-1 : K)^m * ∏ j : Fin m, (t j.succ - t 0) := by
      rw [differenceProd_ite, Fin.prod_univ_succ]
      simp only [ite_true, Fin.succ_ne_zero, ite_false, one_mul]
      calc
        _ = ∏ j : Fin m, ((-1 : K) * (t j.succ - t 0)) :=
          Finset.prod_congr rfl fun _ _ => by ring
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    have rest (j : Fin m) : differenceProd t j.succ =
        (t j.succ - t 0) * differenceProd (fun k => t k.succ) j := by
      rw [differenceProd_ite, Fin.prod_univ_succ, differenceProd_ite]
      simp [Ne.symm (Fin.succ_ne_zero j)]
    simp only [first, rest, Finset.prod_mul_distrib, ih]
    ring

theorem cubic_alternant_core (x y : Fin n → K) (hinj : Function.Injective fun i => cubic (x i))
    (hq : ∀ i j, quad (-1) (x i) (y j) ≠ 0) :
    blockSign K n * (cubicAlternant x y).det =
      (∏ i, ∏ j, (y i - x j)) * core (-1) x y := by
  have h := cubic_alternant_det x y hinj hq
  rw [differenceProd_all, ← vand_eq_det] at h
  apply mul_right_cancel₀ (pow_ne_zero 2 (vand_ne_zero _ hinj))
  linear_combination h

def position : Fin n ⊕ Fin n → Fin (2*n)
  | .inl i => ⟨2*i.val, by omega⟩
  | .inr i => ⟨2*i.val+1, by omega⟩

noncomputable def interleaveIndex (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2*m) :=
  Equiv.ofBijective position <| by
    constructor
    · intro a b h
      cases a <;> cases b <;> simp [position, Fin.ext_iff] at h ⊢ <;> omega
    · intro j
      let i : Fin m := ⟨j.val/2, by omega⟩
      by_cases h : j.val % 2 = 0
      · exact ⟨.inl i, Fin.ext (by simp [position, i]; omega)⟩
      · exact ⟨.inr i, Fin.ext (by simp [position, i]; omega)⟩

noncomputable def interleave (x y : Fin n → K) (i : Fin (2*n)) : K :=
  Sum.elim x y ((interleaveIndex n).symm i)

omit [Field K] in
private theorem interleave_get (x y : Fin n → K) (p : Fin n ⊕ Fin n) :
    interleave x y (position p) = Sum.elim x y p :=
  congrArg _ ((interleaveIndex n).symm_apply_apply p)

private theorem vand_as_pairs (t : Fin n → K) :
    vand t = ∏ i, ∏ j, if i < j then t j - t i else 1 := by
  rw [vand_eq_det, Matrix.det_vandermonde]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Finset.mem_Ioi] using
    (Finset.prod_ite_mem_eq (Finset.Ioi i) (fun j => t j - t i)).symm

private theorem neg_triangle : (∏ i : Fin n, ∏ j : Fin n, if j < i then (-1:K) else 1) =
    blockSign K n := by
  induction n with
  | zero => simp [blockSign]
  | succ m ih =>
    rw [Fin.prod_univ_succ, blockSign]
    have pos (i : Fin m) : 0 < i.succ := Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero i)
    simp only [Fin.not_lt_zero, ite_false, Finset.prod_const_one, one_mul,
      Fin.prod_univ_succ, pos, ite_true, Fin.succ_lt_succ_iff]
    rw [Finset.prod_mul_distrib, ih]
    simp

theorem vand_interleave (x y : Fin n → K) :
    vand (interleave x y) = blockSign K n * vand x * vand y * (∏ i, ∏ j, (y i - x j)) := by
  let e := interleaveIndex n
  have re (f : Fin (2*n) → K) : (∏ i, f i) =
      (∏ i : Fin n, f (position (.inl i))) * ∏ i : Fin n, f (position (.inr i)) := by
    rw [← e.prod_comp f, Fintype.prod_sum_type]
    rfl
  rw [vand_as_pairs, re]
  simp_rw [re fun j => if _ < j then interleave x y j - _ else 1]
  have ll (i j : Fin n) : position (.inl i) < position (.inl j) ↔ i < j := by
    simp only [Fin.lt_def, position]; omega
  have rr (i j : Fin n) : position (.inr i) < position (.inr j) ↔ i < j := by
    simp only [Fin.lt_def, position]; omega
  have lr (i j : Fin n) : position (.inl i) < position (.inr j) ↔ i ≤ j := by
    simp only [Fin.lt_def, Fin.le_def, position]; omega
  have rl (i j : Fin n) : position (.inr i) < position (.inl j) ↔ i < j := by
    simp only [Fin.lt_def, position]; omega
  simp only [interleave_get, Sum.elim_inl, Sum.elim_inr, ll, rr, lr, rl,
    Finset.prod_mul_distrib, ← vand_as_pairs]
  have align : (∏ i : Fin n, ∏ j : Fin n, if i < j then x j - y i else 1) =
      ∏ j : Fin n, ∏ i : Fin n, if i < j then x j - y i else 1 := Finset.prod_comm
  rw [align]
  have cross :
      (∏ i : Fin n, ∏ j : Fin n, if i ≤ j then y j - x i else 1) *
      (∏ i : Fin n, ∏ j : Fin n, if j < i then x i - y j else 1) =
      blockSign K n * (∏ i : Fin n, ∏ j : Fin n, (y j - x i)) := by
    rw [← neg_triangle, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases h : i ≤ j
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  rw [Finset.prod_comm (f := fun i j => y i - x j)]
  linear_combination (vand x * vand y) * cross

variable {L : Type} [Field L] [CharZero L]

noncomputable def columns (L : Type) [Field L] [CharZero L] (m : ℕ) : L[X] :=
  (OeisA109074.Confluence.rawColumn m).map (algebraMap ℚ L)

private theorem eval_interleaved_columns (x y : Fin n → L) :
    (Matrix.of fun i j : Fin (2*n) => (columns L j.val).eval (interleave x y i)).det =
    (cubicAlternant x y).det := by
  rw [← Matrix.det_submatrix_equiv_self (interleaveIndex n)]
  apply congrArg Matrix.det
  ext i j
  change (columns L (position j).val).eval (interleave x y (position i)) = _
  rw [interleave_get]
  cases i <;> cases j <;>
    simp [columns, position, Confluence.raw_even, Confluence.raw_odd, Confluence.cubic,
      cubicAlternant, cubic, Matrix.diagonal_mul]

/-- 交错排列两组行参数及两族多项式列，避免齐次取极限时除以节点差。 -/
theorem normalize_eq_newton (x y : Fin n → L) (hx : Function.Injective x)
    (hy : Function.Injective y) (hcross : ∀ i j, y i ≠ x j)
    (hc : Function.Injective fun i => cubic (x i)) (hq : ∀ i j, quad (-1) (x i) (y j) ≠ 0) :
    normalize (-1) x y =
      Confluence.normalizedAlternant (interleave x y) (fun j => columns L j.val) := by
  have h := Confluence.factor_alternant (interleave x y) (fun j => columns L j.val)
  rw [eval_interleaved_columns, ← vand_eq_det, vand_interleave] at h
  have hh := cubic_alternant_core x y hc hq
  rw [h] at hh
  have sign := blockSign_sq (K := L) n
  have cross : (∏ i, ∏ j, (y i - x j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    exact fun j _ => sub_ne_zero.mpr (hcross i j)
  apply (div_eq_iff (mul_ne_zero (vand_ne_zero _ hx) (vand_ne_zero _ hy))).mpr
  apply mul_left_cancel₀ cross
  linear_combination -hh + (vand x * vand y * (∏ i, ∏ j, (y i - x j)) *
    Confluence.normalizedAlternant (interleave x y) (fun j => columns L j.val)) * sign

theorem vand_neg (x : Fin n → K) :
    vand (fun i => - x i) = blockSign K n * vand x := by
  induction n with
  | zero => simp [blockSign, vand]
  | succ m ih =>
    rw [vand, blockSign, vand, ih (fun i => x i.succ)]
    have pf : (∏ j : Fin m, ((-x j.succ) - (-x 0))) =
        (-1 : K)^m * ∏ j : Fin m, (x j.succ - x 0) := by
      calc
        _ = ∏ j : Fin m, ((-1 : K) * (x j.succ - x 0)) :=
          Finset.prod_congr rfl fun _ _ => by ring
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    rw [pf]; ring

theorem ice_newton (x y : Fin n → L) (hx : Function.Injective x) (hy : Function.Injective y)
    (hcross : ∀ i j, y i ≠ -x j) (hci : Function.Injective fun i => cubic (-x i))
    (hq : ∀ i j, quad (-1) (-x i) (y j) ≠ 0) :
    normalize 1 x y = blockSign L n *
      Confluence.normalizedAlternant (interleave (fun i => -x i) y) (fun j => columns L j.val) := by
  have h := normalize_eq_newton (fun i => -x i) y (neg_injective.comp hx) hy hcross hci hq
  rw [← h]
  have hc : core (-1) (fun i => -x i) y = core 1 x y := by
    unfold core
    congr 3
    ext i j
    simp [quad]
  unfold normalize
  rw [hc, vand_neg]
  have hs := blockSign_sq (K := L) n
  have hn : blockSign L n ≠ 0 := fun he => by simp [he] at hs
  field_simp [hn, vand_ne_zero _ hx, vand_ne_zero _ hy]

end Alternant
end Field
end OeisA109074.Tsuchiya

end

section

namespace OeisA109074.Tsuchiya

open scoped BigOperators

variable {K : Type*} [Field K]

/-- 每个齐次六顶点的公共权，同时也是固定方向的反射端权。 -/
def iceWeight (q : K) := (q^2 - 1)*q

private theorem ice_cubic (q : K) (hq : q^2+1=q) : q^3 = -1 := by
  linear_combination (q+1)*hq

theorem ice_weights (q : K) (hq : q^2+1=q) :
    q^4-1 = iceWeight q ∧ (iceWeight q)^2 = 3*q := by
  unfold iceWeight
  constructor
  · linear_combination (q^2-1)*hq
  · linear_combination (q^4+q^3-2*q^2-3*q)*hq

theorem ice_traces (q : K) (hq : q^2+1=q) :
    anisotropy q = 1 ∧ crossingTrace q q = -2 ∧ traceSq (1 : K) = 2 := by
  have hn : q ≠ 0 := by rintro rfl; simp at hq
  have invq : q⁻¹ = 1-q := by
    field_simp [hn]
    linear_combination hq
  have hc : q*q^2 = -1 := by simpa [pow_succ, mul_assoc] using ice_cubic q hq
  constructor
  · simp [anisotropy, invq]
  · simp [traceSq, crossingTrace, hc]; norm_num

theorem ice_prefactors (q : K) (hq : q^2+1=q) :
    prefOne q (q*q) q 1 = (iceWeight q)^3 ∧
    prefPair q q 1 q 1 = -q^2 := by
  have hb := (ice_weights q hq).1
  have hc := ice_cubic q hq
  constructor
  · unfold prefOne
    rw [hb]
    unfold iceWeight
    ring
  · unfold prefPair
    linear_combination -(q^2)*(q^3-1)*hc

theorem ice_prefactor (q : K) (hq : q^2+1=q) (n : Nat) :
    prefactor q (q*q) (fun _ : Fin n => q) (fun _ => 1) =
      (iceWeight q)^(3*n) * (-q^2)^(n.choose 2) := by
  induction n with
  | zero => simp [prefactor]
  | succ n ih =>
    rw [prefactor]
    simp only [(ice_prefactors q hq).1, (ice_prefactors q hq).2, ih, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.choose_succ_succ, Nat.choose_one_right,
      Nat.mul_succ, pow_add]
    ring

/-- 仅将第一组迹参数变号，范德蒙贡献组合数个负号。 -/
theorem vand_neg_all {n : Nat} (x : Fin n → K) :
    vand (fun i => -x i) = (-1 : K)^(n.choose 2)*vand x := by
  induction n with
  | zero => simp [vand]
  | succ n ih =>
    simp only [vand, ih, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    have pr : (∏ i : Fin n, ((-x i.succ)-(-x 0))) =
        (-1 : K)^n * ∏ i : Fin n, (x i.succ-x 0) := by
      calc
        _ = ∏ i : Fin n, ((-1)*(x i.succ-x 0)) := by
          apply Finset.prod_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    rw [pr]
    ring

theorem normalize_sign {n : Nat} (x y : Fin n → K) :
    normalize (1 : K) (fun i => -x i) y = (-1:K)^(n.choose 2) * normalize (-1) x y := by
  have cm : core (1 : K) (fun i => -x i) y = core (-1) x y := by
    unfold core
    congr 2
    ext i j
    simp [quad]
  unfold normalize
  rw [cm, vand_neg_all]
  have hsg : ((-1:K)^(n.choose 2))⁻¹ = (-1:K)^(n.choose 2) := by rw [← inv_pow]; simp
  simp only [div_eq_mul_inv, mul_inv_rev, hsg]
  ring

private theorem twice_choose (n : Nat) : 2*(n.choose 2) = n*(n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    cases n <;> simp_all +arith [Nat.mul_add, Nat.add_mul]

/-- 候选行列式在冰点的公共因子。交错子取第一组变量的负号后，
    最终仅余 3^(n*(n−1))；等式以交叉相乘表述，适用于任意特征。 -/
theorem homogeneous_scale (q : K) (hq : q^2+1=q) (n : Nat) :
    prefactor q (q*q) (fun _ : Fin n => q) (fun _ => 1) *
      (-1 : K)^(n.choose 2) * 3^(n*(n-1)) =
      ((q^4-1)*(iceWeight q)^(2*n))^n := by
  rw [ice_prefactor q hq, ← twice_choose, (ice_weights q hq).1]
  have hp : ((-q^2)*(-1)*3^2 : K) = (iceWeight q)^4 := by
    rw [show iceWeight q ^ 4 = (iceWeight q^2)^2 by ring, (ice_weights q hq).2]
    ring
  have he : 3*n + 4*(n.choose 2) = n + (2*n)*n := by
    have hh := twice_choose n
    cases n with
    | zero => rfl
    | succ m =>
      simp only [Nat.succ_sub_one] at hh
      nlinarith
  calc
    _ = iceWeight q ^ (3*n) * (((-q^2)*(-1)*3^2)^(n.choose 2)) := by
      simp only [mul_pow, mul_assoc, pow_mul]
    _ = _ := by
      rw [hp, ← pow_mul, ← pow_add, he, pow_add, pow_mul, mul_pow]

end OeisA109074.Tsuchiya

end

section

namespace OeisA109074.Tsuchiya

open OeisA109074.Partial.SixVertex
open scoped BigOperators
variable {K : Type} [Field K] {n : Nat}

private def singlePart (one : K → K) : List K → K
  | [] => 1
  | x :: xs => one x * (xs.map (fun t => x^2*t^2)).prod * singlePart one xs

private theorem singlePart_perm (one : K → K) {s t : List K} (h : s.Perm t) :
    singlePart one s = singlePart one t := by
  induction h with
  | nil => rfl
  | cons x h ih => rw [singlePart, singlePart, (h.map _).prod_eq, ih]
  | swap x y t => simp only [singlePart, List.map_cons, List.prod_cons]; ring
  | trans _ _ h1 h2 => exact h1.trans h2

private def qPart (q : K) : Nat → K
  | 0 => 1
  | n+1 => q*(q^2-1)*(-q^4)^n*qPart q n

private theorem separate_prefactor (q d : K) (x z : Fin n → K) :
    prefactor q d x z = qPart q n *
      singlePart (fun t => t*(t^4-1)) (List.ofFn x) *
      singlePart (fun t => t*(d*t^2-1)) (List.ofFn z) := by
  induction n with
  | zero => simp [prefactor, qPart, singlePart]
  | succ n ih =>
    rw [prefactor, ih]
    simp only [List.ofFn_succ, singlePart, List.map_ofFn, List.prod_ofFn, qPart]
    have h (i : Fin n) : prefPair q (x 0) (z 0) (x i.succ) (z i.succ) =
      (-q^4) * ((x 0)^2 * (x i.succ)^2) * ((z 0)^2 * (z i.succ)^2) := by
      unfold prefPair; ring
    simp only [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, prefOne, Function.comp_apply]
    ring

private theorem normalize_perm (g : K) (x z : Fin n → K) (e : Equiv.Perm (Fin n)) :
    normalize g (x ∘ e) z = normalize g x z := by
  classical
  have hv : vand (x ∘ e) = (Equiv.Perm.sign e : ℤ) * vand x := by
    rw [vand_eq_det, vand_eq_det]
    exact Matrix.det_permute e (Matrix.vandermonde x)
  have hc : core g (x ∘ e) z = (Equiv.Perm.sign e : ℤ) * core g x z := by
    unfold core
    exact Matrix.det_permute e (cleared (Matrix.of fun _ _ : Fin n => (1:K))
      (Matrix.of fun i j => quad g (x i) (z j)))
  have hs : ((Equiv.Perm.sign e : ℤ) : K) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
  unfold normalize
  rw [hv, hc, mul_assoc, mul_div_mul_left _ _ hs]

theorem candidate_perm_rows (q d : K) (x z : Fin n → K) (e : Equiv.Perm (Fin n)) :
    candidate q d (x ∘ e) z = candidate q d x z := by
  have h : prefactor q d (x ∘ e) z = prefactor q d x z := by
    simp only [separate_prefactor, singlePart_perm _ (e.ofFn_comp_perm x)]
  unfold candidate
  rw [h]
  congr 1
  exact normalize_perm _ (fun i => crossingTrace q (x i)) _ e

private theorem inverse_pair (q x u v : K) (hq : q ≠ 0) (hx : x ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    prefPair q x x⁻¹ u v *
      (traceSq v + traceSq x⁻¹ - anisotropy q * crossingTrace q x) *
      (crossingTrace q u + crossingTrace q x - anisotropy q * traceSq x⁻¹) =
      weightA q x v * weightA q (x*v) 1 * weightB q u x⁻¹ * weightA q (u*x⁻¹) 1 := by
  unfold prefPair traceSq crossingTrace anisotropy weightA weightB
  field_simp
  ring

theorem candidate_freeze_inverse (q d : K) (x z : Fin (n+1) → K) (hq : q ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hz : ∀ j, z j ≠ 0)
    (ix : Function.Injective fun i => crossingTrace q (x i))
    (iz : Function.Injective fun j => traceSq (z j)) (h : z 0 = (x 0)⁻¹) :
    candidate q d x z =
      weightB q (x 0) (z 0) * (q^2-1) * (d-(x 0)^2) *
      (∏ j : Fin n, (weightA q (x 0) (z j.succ) * weightA q (x 0 * z j.succ) 1)) *
      (∏ i : Fin n, (weightB q (x i.succ) (z 0) * weightA q (x i.succ * z 0) 1)) *
      candidate q d (fun i => x i.succ) (fun j => z j.succ) := by
  have hi (t : K) : traceSq t⁻¹ = traceSq t := by simp [traceSq, add_comm]
  have hf : quad (anisotropy q) (crossingTrace q (x 0)) (traceSq (z 0)) = 0 := by
    rw [h, hi]; exact native_freeze_point _ _ hq (hx 0)
  have ho : prefOne q d (x 0) (z 0) = weightB q (x 0) (z 0) * (q^2-1) * (d-(x 0)^2) := by
    rw [h]; unfold prefOne weightB; field_simp [hx 0]
  unfold candidate
  rw [normalized_freeze _ _ _ ix iz hf, prefactor]
  rw [ho]
  simp only [h]
  have cross := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun (i : Fin n) _ =>
    inverse_pair q (x 0) (x i.succ) (z i.succ) hq (hx 0) (hx _) (hz _))
  simp only [Finset.prod_mul_distrib] at cross ⊢
  linear_combination (weightB q (x 0) (x 0)⁻¹ * (q^2-1) * (d-(x 0)^2) *
    prefactor q d (fun i => x i.succ) (fun j => z j.succ) *
    normalize (anisotropy q) (fun i => crossingTrace q (x i.succ)) (fun j => traceSq (z j.succ))) * cross

def grid (q d : K) (x z : Fin n → K) := domainPartition q d (List.ofFn x) (List.ofFn z)

private def RowRegular (q : K) (xs : List K) :=
  ∀ x ∈ xs, ∀ y ∈ xs, (spectral q x y).a * (spectral q (x*y) 1).b ≠ 0

private theorem rows_perm (q d : K) (cols : List K) {xs ys : List K} (p : xs.Perm ys)
    (h : RowRegular q xs) (f : Site cols.length → K) :
    stackRows q d cols xs f = stackRows q d cols ys f := by
  induction p with
  | nil => rfl
  | cons x hxy ih =>
    simp only [stackRows]
    rw [ih (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))]
  | swap x y ys =>
    apply folded_create_exchange
    exact (mul_right_injective₀ (h _ (by simp) _ (by simp)))
  | trans hp _ h1 h2 =>
    exact (h1 h).trans (h2 (fun a ha b hb => h a (hp.mem_iff.mpr ha) b (hp.mem_iff.mpr hb)))

private theorem row_regular_ofFn (q : K) (x : Fin n → K)
    (h : ∀ i j, (spectral q (x i) (x j)).a * (spectral q (x i*x j) 1).b ≠ 0) :
    RowRegular q (List.ofFn x) := by
  intro a ha b hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  exact h i j

private theorem grid_perm_rows (q d : K) (x z : Fin n → K) (e : Equiv.Perm (Fin n))
    (h : RowRegular q (List.ofFn x)) :
    grid q d (x ∘ e) z = grid q d x z := by
  unfold grid domainPartition
  exact congrFun (rows_perm q d _ (e.ofFn_comp_perm x).symm h _).symm _

private theorem empty_as_prod (q d x : K) (zs : List K) :
    emptyFactor q d x zs = (d*x^2-1) * (zs.map (fun z => weightA q x z * weightA q (x*z) 1)).prod := by
  induction zs with
  | nil => simp [emptyFactor, boundary, pow_two, mul_assoc]
  | cons z zs ih => simp only [emptyFactor, ih, List.map_cons, List.prod_cons, spectral, weightA]; ring

private theorem full_as_prod (q d x : K) (zs : List K) :
    fullFactor q d x zs = (d-x^2) * (zs.map (fun z => weightA q x z * weightA q (x*z) 1)).prod := by
  induction zs with
  | nil => simp [fullFactor, boundary, pow_two]
  | cons z zs ih => simp only [fullFactor, ih, List.map_cons, List.prod_cons, spectral, weightA]; ring

private theorem occupied_as_prod (q z : K) (xs : List K) :
    occupiedFactor q z xs = (xs.map (fun x => weightA q x z * weightB q (x*z) 1)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [occupiedFactor, ih, List.map_cons, List.prod_cons, spectral, weightA, weightB]; ring

private theorem vacant_as_prod (q z : K) (xs : List K) :
    vacantFactor q z xs = (xs.map (fun x => weightB q x z * weightA q (x*z) 1)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [vacantFactor, ih, List.map_cons, List.prod_cons, spectral, weightA, weightB]; ring

private theorem match_at_row (q d : K) (x z : Fin (n+1) → K) (hq : q ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hz : ∀ j, z j ≠ 0)
    (ix : Function.Injective fun i => crossingTrace q (x i))
    (iz : Function.Injective fun j => traceSq (z j)) (h : x 0 = z 0)
    (ih : grid q d (x ∘ Fin.succ) (z ∘ Fin.succ) = candidate q d (x ∘ Fin.succ) (z ∘ Fin.succ)) :
    grid q d x z = candidate q d x z := by
  simp only [Function.comp_def] at ih
  rw [candidate_freeze _ _ _ _ hq hx hz ix iz h, ← ih]
  unfold grid
  simp only [List.ofFn_succ]
  rw [h, freeze_domain, empty_as_prod, occupied_as_prod]
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply, weightC, weightB, spectral]
  ring

private theorem match_at_inverse (q d : K) (x z : Fin (n+1) → K) (hq : q ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hz : ∀ j, z j ≠ 0)
    (ix : Function.Injective fun i => crossingTrace q (x i))
    (iz : Function.Injective fun j => traceSq (z j)) (h : z 0 = (x 0)⁻¹)
    (reg : RowRegular q (List.ofFn x))
    (ih : grid q d (x ∘ Fin.succ) (z ∘ Fin.succ) = candidate q d (x ∘ Fin.succ) (z ∘ Fin.succ)) :
    grid q d x z = candidate q d x z := by
  simp only [Function.comp_def] at ih
  rw [candidate_freeze_inverse _ _ _ _ hq hx hz ix iz h, ← ih]
  unfold grid
  simp only [List.ofFn_succ]
  let xs := List.ofFn (fun i : Fin n => x i.succ)
  let zs := List.ofFn (fun i : Fin n => z i.succ)
  have perm : (x 0 :: xs).Perm (xs ++ [x 0]) := by
    simpa using (List.perm_append_comm (l₁ := [x 0]) (l₂ := xs))
  have hm : domainPartition q d (x 0 :: xs) (z 0 :: zs) =
      domainPartition q d (xs ++ [x 0]) (z 0 :: zs) := by
    apply congrFun (rows_perm q d _ perm _ _)
    simpa only [xs, List.ofFn_succ] using reg
  change domainPartition q d (x 0 :: xs) (z 0 :: zs) = _
  rw [hm, freeze_domain_inverse _ _ _ _ (by rw [h]; exact mul_inv_cancel₀ (hx 0)),
    full_as_prod, vacant_as_prod]
  simp only [xs, zs, List.map_ofFn, List.prod_ofFn, Function.comp_apply, weightB, spectral]
  ring

/-- 两组插值点分别由直行和反射冻结给出。 -/
def node (x : Fin n → K) (r : Fin n × Bool) := if r.2 then x r.1 else (x r.1)⁻¹

structure GridGeneric (q : K) (x z : Fin n → K) : Prop where
  q0 : q ≠ 0
  x0 : ∀ i, x i ≠ 0
  z0 : ∀ j, z j ≠ 0
  rows : Function.Injective fun i => crossingTrace q (x i)
  cols : Function.Injective fun j => traceSq (z j)
  disjoint : ∀ i j, traceSq (x i) ≠ traceSq (z j)
  nodes : Function.Injective fun r => (node x r)^2
  exchange : ∀ i j, (spectral q (x i) (x j)).a * (spectral q (x i*x j) 1).b ≠ 0

theorem GridGeneric.restrict {q : K} {x z : Fin n → K} (h : GridGeneric q x z)
    {m : Nat} (a b : Fin m → Fin n) (ha : Function.Injective a) (hb : Function.Injective b) :
    GridGeneric q (x ∘ a) (z ∘ b) where
  q0 := h.q0
  x0 i := h.x0 _
  z0 j := h.z0 _
  rows := h.rows.comp ha
  cols := h.cols.comp hb
  disjoint i j := h.disjoint _ _
  nodes := by
    rintro ⟨i,e⟩ ⟨j,f⟩ hij
    have ho : ((a i,e) : Fin n × Bool) = (a j,f) := h.nodes hij
    exact Prod.ext (ha (congrArg Prod.fst ho)) (congrArg (fun p : Fin n × Bool => p.2) ho)
  exchange i j := h.exchange _ _

private theorem trace_node (x : Fin n → K) (r : Fin n × Bool) :
    traceSq (node x r) = traceSq (x r.1) := by
  rcases r with ⟨i, b⟩
  cases b <;> simp [node, traceSq, add_comm]

private theorem trace_cons (t : K) (z : Fin n → K) :
    (fun j => traceSq (Fin.cons (α := fun _ => K) t z j)) =
      Fin.cons (α := fun _ => K) (traceSq t) (fun j => traceSq (z j)) := by
  funext j
  induction j using Fin.cases <;> rfl

private theorem interpolated_step (q d : K) (x z : Fin (n+1) → K)
    (h : GridGeneric q x z)
    (ih : ∀ (x' z' : Fin n → K), GridGeneric q x' z' →
      grid q d x' z' = candidate q d x' z') :
    grid q d x z = candidate q d x z := by
  classical
  let tail := fun j : Fin n => z j.succ
  let consCol (t : K) := Fin.cons (α := fun _ => K) t tail
  have izTail : Function.Injective (fun j => traceSq (tail j)) := h.cols.comp (Fin.succ_injective _)
  obtain ⟨P, hP, p⟩ := domain_first_polynomial q d (List.ofFn x) (List.ofFn tail)
  obtain ⟨Q, hQ, f⟩ := candidate_first_polynomial q d x tail izTail
  have phys (t : K) : grid q d x (consCol t) = t * P.eval (t^2) := by
    simpa only [grid, consCol, List.ofFn_succ (f := Fin.cons t tail), Fin.cons_zero,
      Fin.cons_succ, pow_two] using p t
  have sample (r : Fin (n+1) × Bool) :
      grid q d x (consCol (node x r)) = candidate q d x (consCol (node x r)) := by
    let e : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 r.1
    let y := x ∘ e
    let t := node x r
    have hy0 : y 0 = x r.1 := by simp [y,e]
    have ht : t ≠ 0 := by simp [t, node]; split <;> simp [h.x0]
    have zPos : ∀ j, consCol t j ≠ 0 := by
      intro j
      induction j using Fin.cases <;> simp [consCol, ht, tail, h.z0]
    have zInj : Function.Injective (fun j => traceSq (consCol t j)) := by
      rw [show (fun j => traceSq (consCol t j)) = _ from trace_cons t tail]
      apply Fin.cons_injective_iff.mpr
      refine ⟨?_, izTail⟩
      rintro ⟨i, hi⟩
      rw [trace_node] at hi
      exact h.disjoint r.1 i.succ hi.symm
    have small : grid q d (y ∘ Fin.succ) (consCol t ∘ Fin.succ) =
        candidate q d (y ∘ Fin.succ) (consCol t ∘ Fin.succ) := by
      apply ih
      exact h.restrict (e ∘ Fin.succ) Fin.succ (e.injective.comp (Fin.succ_injective _))
        (Fin.succ_injective _)
    rw [← grid_perm_rows q d x _ e (row_regular_ofFn q x h.exchange), ← candidate_perm_rows q d x _ e]
    change grid q d y (consCol t) = candidate q d y (consCol t)
    by_cases hb : r.2 = true
    · apply match_at_row q d _ _ h.q0 (fun i => h.x0 (e i)) zPos (h.rows.comp e.injective) zInj _ small
      simp [consCol, t, node, hb, e]
    · apply match_at_inverse q d _ _ h.q0 (fun i => h.x0 (e i)) zPos (h.rows.comp e.injective) zInj _
        (row_regular_ofFn q y (fun i j => h.exchange (e i) (e j))) small
      simp [consCol, t, node, hb, e]
  have pq : P = Q := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q h.nodes
    · intro r
      have nz : node x r ≠ 0 := by simp [node]; split <;> simp [h.x0]
      have eq := sample r
      rw [phys, f (node x r) nz (by intro j; rw [trace_node]; exact h.disjoint _ j.succ)] at eq
      exact mul_left_cancel₀ nz eq
    · simp only [List.length_ofFn] at hP
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      rcases hP with rfl | hP
      · simp; omega
      · omega
  have hz : consCol (z 0) = z := by funext j; induction j using Fin.cases <;> rfl
  calc
    grid q d x z = (z 0) * P.eval ((z 0)^2) := hz ▸ phys (z 0)
    _ = (z 0) * Q.eval ((z 0)^2) := by rw [pq]
    _ = candidate q d x z := hz ▸ (f (z 0) (h.z0 0)
      (fun j => h.cols.ne (Fin.succ_ne_zero j).symm)).symm

theorem grid_eq_candidate {q : K} (d : K) (x z : Fin n → K) (h : GridGeneric q x z) :
    grid q d x z = candidate q d x z := by
  induction n with
  | zero => simp [grid, domainPartition, stackRows, fullSiteWeight, emptySite, candidate,
      prefactor, normalize, core, vand] <;> rfl
  | succ n ih => exact interpolated_step q d x z h ih

end OeisA109074.Tsuchiya

end

section

namespace OeisA109074.Specialization

open OeisA109074.Partial.SixVertex
open LaurentPolynomial
open scoped LaurentPolynomial BigOperators

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

private def liftSite : (cs : List R) → Site cs.length → Site (cs.map φ).length
  | [], _ => ()
  | _ :: cs, (v,s) => (v,liftSite cs s)

private theorem map_scatter (q x z : R) (i j : Bool) (f : Bool → Bool → R) :
    φ (scatter (spectral q x z) f i j) =
      scatter (spectral (φ q) (φ x) (φ z)) (fun a b => φ (f a b)) i j := by
  cases i <;> cases j <;> simp [scatter, spectral]

private theorem map_folded (q d x : R) (cs : List R)
    (f : Bool → Site cs.length → R) (g : Bool → Site (cs.map φ).length → S)
    (h : ∀ i s, φ (f i s) = g i (liftSite φ cs s)) (i : Bool) (s : Site cs.length) :
    φ (folded q d x cs f i s) =
      folded (φ q) (φ d) (φ x) (cs.map φ) g i (liftSite φ cs s) := by
  induction cs generalizing i with
  | nil =>
    obtain ⟨⟩ := s
    change φ (bare d x f i ()) = bare (φ d) (φ x) g i ()
    cases i <;> simp [bare, boundary, h, liftSite]
  | cons z cs ih =>
    obtain ⟨v,s⟩ := s
    simp only [folded, liftSite, addColumn, map_scatter]
    congr 1
    funext a k
    apply ih
    intro b t
    simp only [map_scatter, map_mul, map_one]
    congr 1
    funext c l
    exact h c (l,t)

private theorem map_stack (q d : R) (cs rs : List R)
    (f : Site cs.length → R) (g : Site (cs.map φ).length → S)
    (h : ∀ s, φ (f s) = g (liftSite φ cs s)) (s : Site cs.length) :
    φ (stackRows q d cs rs f s) =
      stackRows (φ q) (φ d) (cs.map φ) (rs.map φ) g (liftSite φ cs s) := by
  induction rs generalizing s with
  | nil => exact h s
  | cons x xs ih =>
    simp only [List.map_cons, stackRows, create]
    apply map_folded
    intro i s
    cases i <;> simp [ih]

/-- 配分函数只由环运算组成，逐个谱参数代入任意环同态保持它的值。 -/
theorem map_domain (q d : R) (xs zs : List R) :
    φ (domainPartition q d xs zs) =
      domainPartition (φ q) (φ d) (xs.map φ) (zs.map φ) := by
  have he : liftSite φ zs (emptySite zs.length) = emptySite (zs.map φ).length := by
    induction zs with
    | nil => rfl
    | cons z zs ih => exact congrArg (fun s => (false,s)) ih
  unfold domainPartition
  rw [← he]
  clear he
  apply map_stack
  intro s
  induction zs with
  | nil => exact map_one φ
  | cons z zs ih =>
    obtain ⟨v,s⟩ := s
    cases v
    · exact map_zero φ
    · exact ih s

end Maps

section Curve

variable {K : Type} [Field K]
abbrev Laurent (K : Type) [Field K] := K[T;T⁻¹]
abbrev CurveField (K : Type) [Field K] := FractionRing (Laurent K)

noncomputable def embed : Laurent K →+* CurveField K := algebraMap _ _
noncomputable def specialize : Laurent K →+* K := eval₂ (RingHom.id K) 1

private theorem emb_inj : Function.Injective (embed (K := K)) :=
  IsFractionRing.injective _ _

noncomputable def mono (a : K) (e : ℤ) : CurveField K := embed (C a * T e)

theorem mono_mul (a b : K) (e f : ℤ) : mono a e * mono b f = mono (a*b) (e+f) := by
  simp only [mono, map_mul, T_add]
  ring

@[simp] theorem mono_one : mono (1:K) 0 = 1 := by simp [mono]

theorem mono_eq_imp {a b : K} {e f : ℤ} (ha : a ≠ 0) (h : mono a e = mono b f) :
    e = f ∧ a = b := by
  have he := emb_inj h
  change C a * T e = C b * T f at he
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T] at he
  exact (AddMonoidAlgebra.single_inj.mp he).resolve_right (fun h0 => ha h0.1)

theorem mono_ne_zero {a : K} (ha : a ≠ 0) (e : ℤ) : mono a e ≠ 0 := by
  intro h
  have he : mono a e = mono 0 e := by simpa [mono] using h
  exact ha (mono_eq_imp ha he).2

theorem mono_inv {a : K} (ha : a ≠ 0) (e : ℤ) : (mono a e)⁻¹ = mono a⁻¹ (-e) := by
  apply inv_eq_of_mul_eq_one_right
  simp [mono_mul, ha]

theorem mono_pow (a : K) (e : ℤ) (k : ℕ) : mono a e ^ k = mono (a^k) (k*e) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih, mono_mul]; push_cast; ring_nf

def tr {F : Type} [Field F] (v : F) := v+v⁻¹

theorem trace_collision {F : Type} [Field F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : tr a = tr b) : a = b ∨ a = b⁻¹ := by
  unfold tr at h
  have hz : (a-b)*(a*b-1) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp hz with he | he
  · exact Or.inl (sub_eq_zero.mp he)
  · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.mp he))

theorem tr_mono_exponent {a b : K} {e f : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : tr (mono a e) = tr (mono b f)) : e = f ∨ e = -f := by
  rcases trace_collision (mono_ne_zero ha _) (mono_ne_zero hb _) h with hm | hm
  · exact Or.inl (mono_eq_imp ha hm).1
  · rw [mono_inv hb] at hm
    exact Or.inr (mono_eq_imp ha hm).1

open OeisA109074.Tsuchiya

variable {n : ℕ}

def rowExp (i : Fin n) : ℤ := (i.val:ℤ)+1
def colExp (i : Fin n) : ℤ := n+(i.val:ℤ)+1

noncomputable def row (q : K) (i : Fin n) := mono q (rowExp i)
noncomputable def col (K : Type) [Field K] (i : Fin n) := mono (1:K) (colExp i)
noncomputable def param (q : K) := mono q 0

private theorem row_pos (i : Fin n) : 0 < rowExp i := by unfold rowExp; omega
private theorem col_pos (i : Fin n) : 0 < colExp i := by unfold colExp; omega
private theorem separated (i j : Fin n) : rowExp i < colExp j := by unfold rowExp colExp; omega
private theorem row_exp_inj : Function.Injective (@rowExp n) := by
  intro i j h; apply Fin.ext; unfold rowExp at h; omega
private theorem col_exp_inj : Function.Injective (@colExp n) := by
  intro i j h; apply Fin.ext; unfold colExp at h; omega

private theorem mono_neg_one (e : ℤ) : mono (-1:K) e = -mono (1:K) e := by simp [mono]

private theorem trace_square (a : K) (e : ℤ) :
    traceSq (mono a e) = tr (mono (a^2) (2*e)) := by
  rw [traceSq, tr, inv_pow, mono_pow]; norm_num

theorem crossing_row {q : K} (hq : q^2+1=q) (i : Fin n) :
    -crossingTrace (param q) (row q i) = tr (mono (1:K) (2*rowExp i)) := by
  have hc : q*q^2 = -1 := by linear_combination (q+1)*hq
  simp only [crossingTrace, param, row, mono_pow, Nat.cast_ofNat, mono_mul, hc, zero_add,
    mono_neg_one, inv_neg, tr]
  ring

theorem trace_col (j : Fin n) : traceSq (col K j) = tr (mono (1:K) (2*colExp j)) := by
  simp [col, trace_square]

private theorem cubic_trace {F : Type} [Field F] {v : F} (hv : v ≠ 0) :
    cubic (tr v) = tr (v^3) := by
  unfold cubic tr
  field_simp
  ring

private theorem cubic_mono (e : ℤ) : cubic (tr (mono (1:K) e)) = tr (mono 1 (3*e)) := by
  rw [cubic_trace (mono_ne_zero one_ne_zero _), mono_pow]; norm_num

theorem row_injective {q : K} (hq : q^2+1=q) :
    Function.Injective (fun i : Fin n => crossingTrace (param q) (row q i)) := by
  intro i j h
  have he := congrArg Neg.neg h
  rw [crossing_row hq, crossing_row hq] at he
  have hdeg := tr_mono_exponent one_ne_zero one_ne_zero he
  apply row_exp_inj
  have := row_pos i
  have := row_pos j
  omega

theorem col_injective : Function.Injective (fun j : Fin n => traceSq (col K j)) := by
  intro i j h
  change traceSq (col K i) = traceSq (col K j) at h
  rw [trace_col, trace_col] at h
  have hdeg := tr_mono_exponent one_ne_zero one_ne_zero h
  apply col_exp_inj
  have := col_pos i
  have := col_pos j
  omega

theorem curve_cross {q : K} (hq : q^2+1=q) (i j : Fin n) :
    traceSq (col K i) ≠ -crossingTrace (param q) (row q j) := by
  rw [trace_col, crossing_row hq]
  intro h
  have he := tr_mono_exponent one_ne_zero one_ne_zero h
  have := separated j i
  have := row_pos j
  omega

theorem cubic_injective {q : K} (hq : q^2+1=q) :
    Function.Injective (fun i : Fin n => cubic (-crossingTrace (param q) (row q i))) := by
  intro i j h
  simp only [crossing_row hq, cubic_mono] at h
  have hdeg := tr_mono_exponent one_ne_zero one_ne_zero h
  apply row_exp_inj
  have := row_pos i
  have := row_pos j
  omega

theorem curve_quad {q : K} (hq : q^2+1=q) (i j : Fin n) :
    quad (-1) (-crossingTrace (param q) (row q i)) (traceSq (col K j)) ≠ 0 := by
  rw [trace_col, crossing_row hq]
  intro h
  have hf := quad_ice (tr (mono (1:K) (2*rowExp i))) (tr (mono (1:K) (2*colExp j)))
  rw [h, mul_zero] at hf
  have he := sub_eq_zero.mp hf.symm
  change cubic _ = cubic _ at he
  rw [cubic_mono, cubic_mono] at he
  have hdeg := tr_mono_exponent one_ne_zero one_ne_zero he
  have := row_pos i
  have := separated i j
  omega

end Curve

end OeisA109074.Specialization

end

section

namespace OeisA109074.Specialization

open OeisA109074.Tsuchiya OeisA109074.Partial.SixVertex
variable {K : Type} [Field K] [CharZero K] {n : Nat}

private theorem root_ne_zero {q : K} (hr : q^2+1=q) : q ≠ 0 := by
  rintro rfl
  norm_num at hr

private theorem sq_ne_one {q : K} (hr : q^2+1=q) : q^2 ≠ 1 := by
  intro h
  rw [h] at hr
  rw [← hr] at h
  norm_num at h

private theorem raw_trace (a : K) (e : ℤ) :
    traceSq (mono a e) = tr (mono (a^2) (2*e)) := by
  rw [traceSq, tr, inv_pow, mono_pow]
  norm_num

theorem curve_trace_disjoint {q : K} (hq : q ≠ 0) (i j : Fin n) :
    traceSq (row q i) ≠ traceSq (col K j) := by
  intro h
  simp only [row, col, raw_trace, one_pow] at h
  have e := tr_mono_exponent (pow_ne_zero _ hq) one_ne_zero h
  unfold rowExp colExp at e
  omega

theorem curve_nodes_inj {q : K} (hq : q ≠ 0) :
    Function.Injective fun r : Fin n × Bool => (node (row q) r)^2 := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  cases s <;> cases t <;>
    simp only [node, Bool.false_eq_true, ite_false, ite_true, row, mono_inv hq, mono_pow,
      Nat.cast_ofNat, Prod.mk.injEq, and_true, and_false] at h ⊢
  all_goals
    have e := (mono_eq_imp (by positivity) h).1
    unfold rowExp at e
    first | exact Fin.ext (by omega) | omega

theorem curve_exchange {q : K} (hr : q^2+1=q) (i j : Fin n) :
    (spectral (param q) (row q i) (row q j)).a *
      (spectral (param q) (row q i * row q j) 1).b ≠ 0 := by
  have hq := root_ne_zero hr
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    change param q * param q * row q i * row q i = row q j * row q j at h
    simp only [param, row, mono_mul, zero_add] at h
    have hc := (mono_eq_imp (by positivity) h).2
    apply sq_ne_one hr
    apply mul_right_cancel₀ (pow_ne_zero 2 hq)
    linear_combination hc
  · change param q * ((row q i * row q j) * (row q i * row q j) - 1*1) ≠ 0
    apply mul_ne_zero (mono_ne_zero hq 0)
    apply sub_ne_zero.mpr
    intro h
    rw [one_mul, ← mono_one (K := K)] at h
    simp only [row, mono_mul] at h
    have he := (mono_eq_imp (by positivity) h).1
    unfold rowExp at he
    omega

/-- Laurent 曲线避开所有插值点碰撞和交换因子的零点。 -/
theorem curve_grid_generic {q : K} (hr : q^2+1=q) :
    GridGeneric (param q) (@row K _ n q) (col K) where
  q0 := mono_ne_zero (root_ne_zero hr) _
  x0 _ := mono_ne_zero (root_ne_zero hr) _
  z0 _ := mono_ne_zero one_ne_zero _
  rows := row_injective hr
  cols := col_injective
  disjoint := curve_trace_disjoint (root_ne_zero hr)
  nodes := curve_nodes_inj (root_ne_zero hr)
  exchange := curve_exchange hr

end OeisA109074.Specialization

end

section

namespace OeisA109074.Specialization

open OeisA109074.Partial.SixVertex OeisA109074.Tsuchiya
open scoped BigOperators LaurentPolynomial
open LaurentPolynomial

section Regular

variable {R : Type} [CommRing R] {K : Type} [Field K] {n : ℕ}

/-- 候选式的标量前因子本身是多项式，可以先放在 Laurent 环中计算。 -/
private def regularPref (q d : R) : {m : ℕ} → (Fin m → R) → (Fin m → R) → R
  | 0, _, _ => 1
  | m+1, x, z => (q*(q^2-1)*(x 0)*(z 0)*((x 0)^4-1)*(d*(z 0)^2-1)) *
      (∏ i : Fin m, -(q^4)*((x 0)*(z 0))^2*((x i.succ)*(z i.succ))^2) *
      regularPref q d (fun i => x i.succ) (fun j => z j.succ)

private theorem map_pref (φ : R →+* K) (q d : R) (x z : Fin n → R) :
    φ (regularPref q d x z) = prefactor (φ q) (φ d) (fun i => φ (x i)) (fun i => φ (z i)) := by
  induction n with
  | zero => simp [regularPref, prefactor]
  | succ n ih => simp [regularPref, prefactor, prefOne, prefPair, ih]

theorem sign_power (K : Type) [Field K] (n : ℕ) : blockSign K n = (-1:K)^(n.choose 2) := by
  induction n with
  | zero => simp [blockSign]
  | succ n ih =>
    rw [blockSign, ih, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

omit [CommRing R] in
private theorem map_interleave {S : Type} (φ : R → S) (x z : Fin n → R) (i : Fin (2*n)) :
    φ (interleave x z i) = interleave (fun j => φ (x j)) (fun j => φ (z j)) i := by
  unfold interleave
  cases (interleaveIndex n).symm i <;> rfl

private noncomputable def regularRight [CharZero K] (q d : Laurent K)
    (x z a b : Fin n → Laurent K) :=
  regularPref q d x z * (-1 : Laurent K)^(n.choose 2) *
    Confluence.normalizedAlternant (interleave a b)
      (fun j => (columns K j.val).map LaurentPolynomial.C)

private theorem map_regularRight [CharZero K] {F : Type} [Field F] [CharZero F]
    (φ : Laurent K →+* F) (q d : Laurent K) (x z a b : Fin n → Laurent K) :
    φ (regularRight q d x z a b) =
      prefactor (φ q) (φ d) (fun i => φ (x i)) (fun j => φ (z j)) * blockSign F n *
        Confluence.normalizedAlternant (interleave (fun i => φ (a i)) (fun j => φ (b j)))
          (fun j => columns F j.val) := by
  simp only [regularRight, map_mul, map_pref, map_pow, map_neg, map_one, sign_power,
    Confluence.normalized_map, map_interleave, columns, Polynomial.map_map]
  congr 2
  funext j
  congr 1
  exact Subsingleton.elim _ _

private noncomputable def rawRow (q : K) (i : Fin n) : Laurent K :=
  C q * T (rowExp i)

private noncomputable def rawCol (K : Type) [Field K] (i : Fin n) : Laurent K :=
  C 1 * T (colExp i)

private noncomputable def rawTrace (K : Type) [Field K] (e : ℤ) : Laurent K :=
  T (2*e) + T (-(2*e))

private theorem embed_trace (e : ℤ) :
    embed (rawTrace K e) = tr (mono (1:K) (2*e)) := by
  rw [tr, mono_inv one_ne_zero]; simp [rawTrace, mono]

private theorem eval_trace (e : ℤ) : specialize (rawTrace K e) = 2 := by
  simp [specialize, rawTrace]; ring

private theorem eval_row (q : K) (i : Fin n) : specialize (rawRow q i) = q := by
  simp [specialize, rawRow]

private theorem eval_col (i : Fin n) : specialize (rawCol K i) = 1 := by
  simp [specialize, rawCol]

private theorem domain_ofFn {S : Type} [CommRing S] (φ : R →+* S) (q d : R)
    (x z : Fin n → R) : φ (domainPartition q d (List.ofFn x) (List.ofFn z)) =
      domainPartition (φ q) (φ d) (List.ofFn fun i => φ (x i)) (List.ofFn fun i => φ (z i)) := by
  simp [map_domain, List.map_ofFn, Function.comp_def]

omit [Field K] in
private theorem interleave_const (v : K) :
    interleave (fun _ : Fin n => v) (fun _ => v) = fun _ => v := by
  funext i
  unfold interleave
  cases (interleaveIndex n).symm i <;> rfl

/-- 先在 Laurent 分式域取互异的迹节点，再用单射反映等式并令 T=1。
    此处对 Newton 归一化后的整式取值，即使所有迹节点合并也成立。 -/
theorem specialize_grid [CharZero K] (q : K) (hq : q^2+1=q) (n : ℕ) :
    domainPartition q (q*q) (List.replicate n q) (List.replicate n 1) =
      prefactor q (q*q) (fun _ : Fin n => q) (fun _ => 1) * blockSign K n *
        (algebraMap ℚ K) (Confluence.normalizedAlternant
          (fun _ : Fin (2*n) => (2:ℚ)) (fun j => Confluence.rawColumn j.val)) := by
  let κ : K →+* CurveField K := embed.comp LaurentPolynomial.C
  letI : CharZero (CurveField K) := ⟨by
    intro m n h
    exact_mod_cast κ.injective (a₁ := (m:K)) (a₂ := (n:K)) (by simpa using h)⟩
  let x := @rawRow K _ n q
  let z := @rawCol n K _
  let a := fun i : Fin n => rawTrace K (rowExp i)
  let b := fun j : Fin n => rawTrace K (colExp j)
  let u : Laurent K := C q
  let L := domainPartition u (u*u) (List.ofFn x) (List.ofFn z)
  let D := regularRight u (u*u) x z a b
  have eu : embed u = param q := by simp [u, param, mono]
  have eqh : (param q)^2+1=param q := by
    rw [← eu]
    change (embed (C q))^2+1=embed (C q)
    simp only [← map_pow, ← map_one embed, ← map_add, ← map_one C, ← map_add, hq]
  have ex (i : Fin n) : embed (x i) = row q i := rfl
  have ez (j : Fin n) : embed (z j) = col K j := rfl
  have ea (i : Fin n) : embed (a i) = -crossingTrace (param q) (row q i) :=
    (embed_trace _).trans (crossing_row hq i).symm
  have eb (j : Fin n) : embed (b j) = traceSq (col K j) :=
    (embed_trace _).trans (trace_col j).symm
  have eL : embed L = grid (n := n) (param q) (param q * param q) (row q) (col K) := by
    simp only [L, domain_ofFn, map_mul, eu, ex, ez, grid]
  have eD : embed D = candidate (n := n) (param q) (param q * param q) (row q) (col K) := by
    simp only [D, map_regularRight, map_mul, eu, ex, ez, ea, eb, candidate, (ice_traces _ eqh).1,
      ice_newton _ _ (row_injective hq) col_injective (curve_cross hq) (cubic_injective hq)
        (curve_quad hq), mul_assoc]
  have eqLD : L = D := by
    apply IsFractionRing.injective (Laurent K) (CurveField K)
    change embed L = embed D
    rw [eL, eD]
    exact grid_eq_candidate _ _ _ (curve_grid_generic (n := n) hq)
  have final := congrArg specialize eqLD
  have su : specialize u = q := by simp [u, specialize]
  have sr (i : Fin n) : specialize (x i) = q := eval_row q i
  have sz (j : Fin n) : specialize (z j) = 1 := eval_col j
  have sa (i : Fin n) : specialize (a i) = 2 := eval_trace _
  have sb (i : Fin n) : specialize (b i) = 2 := eval_trace _
  simp only [L, D, domain_ofFn, map_regularRight, map_mul, su, sr, sz, sa, sb,
    List.ofFn_const, interleave_const] at final
  simpa only [Confluence.normalized_map, map_ofNat, columns] using final

end Regular

end OeisA109074.Specialization

end

section

namespace OeisA109074.Ratio

open Finset Confluence
open scoped BigOperators

private def node (j : ℕ) : ℚ := (j : ℚ) + (j/2 : ℕ) + 1

private def gap (j k : ℕ) : ℚ := (node j)^2 - (node k)^2

private def alt (m : ℕ) : ℚ := ∏ j ∈ range m, node j * ∏ k ∈ range j, gap j k

private def den (m : ℕ) : ℚ := ∏ j ∈ range m, ((2*j+1).factorial : ℚ)

noncomputable def homogeneous (m : ℕ) : ℚ :=
  normalizedAlternant (fun _ : Fin m => (2:ℚ)) (fun j => rawColumn j.val)

private theorem triangle_prod (m : ℕ) :
    (∏ i : Fin m, ∏ j ∈ Ioi i, gap j.val i.val) =
    ∏ j ∈ range m, ∏ k ∈ range j, gap j k := by
  have h (i : Fin m) : (∏ j ∈ Ioi i, gap j.val i.val) =
      ∏ j : Fin m, if i.val < j.val then gap j.val i.val else 1 := by
    classical
    simp [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  simp_rw [h]
  rw [Finset.prod_comm]
  rw [← Fin.prod_univ_eq_prod_range]
  congr 1; ext j
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => if i < j.val then gap j.val i else 1)]
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp
  omega

theorem cleared (m : ℕ) : den m * homogeneous m = alt m := by
  have h := homogeneous_product m
  unfold den homogeneous alt
  rw [Finset.prod_mul_distrib, ← triangle_prod, ← Fin.prod_univ_eq_prod_range,
    ← Fin.prod_univ_eq_prod_range]
  simpa [node, gap] using h

private def packet (k : ℕ) : ℚ :=
  (3*(k:ℚ)+2) * (3*(k:ℚ)+3)^2 * (3*(k:ℚ)+4)

private theorem packets (m : ℕ) :
    (∏ k ∈ range m, packet k) =
      ((3*m+1).factorial : ℚ) * 3^m * (m.factorial : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ih, Nat.factorial_succ m, pow_succ,
      show 3*(m+1)+1 = 3*m+1+1+1+1 by omega]
    simp only [Nat.factorial_succ (3*m+1+1+1), Nat.factorial_succ (3*m+1+1),
      Nat.factorial_succ (3*m+1)]
    unfold packet
    push_cast
    ring

private theorem pair_indexes (m : ℕ) (f : ℕ → ℚ) :
    (∏ k ∈ range (2*m), f k) = ∏ i ∈ range m, f (2*i)*f (2*i+1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, prod_range_succ, prod_range_succ, prod_range_succ, ih]; ring

private theorem node_even (n : ℕ) : node (2*n) = 3*(n:ℚ)+1 := by
  simp [node]; ring
private theorem node_odd (n : ℕ) : node (2*n+1) = 3*(n:ℚ)+2 := by
  unfold node
  rw [show (2*n+1)/2=n by omega]
  push_cast; ring

private theorem cross_factors (n : ℕ) :
    (∏ i ∈ range (2*n), gap (2*n) i * gap (2*n+1) i) =
      ((6*n+1).factorial : ℚ) * 3^(2*n) * ((2*n).factorial : ℚ) := by
  rw [pair_indexes]
  calc
    _ = ∏ k ∈ range n, packet (n-1-k) * packet (n+k) := by
      apply prod_congr rfl
      intro k hk
      have h : k+1 ≤ n := mem_range.mp hk
      have he : n-1-k = n-(k+1) := by omega
      simp only [gap, node_even, node_odd, packet, he, Nat.cast_sub h, Nat.cast_add,
        Nat.cast_one]
      ring
    _ = ∏ k ∈ range (2*n), packet k := by
      rw [prod_mul_distrib, prod_range_reflect, two_mul, prod_range_add]
    _ = _ := by rw [packets, show 3*(2*n)+1=6*n+1 by omega]

private theorem alt_step (n : ℕ) : alt (2*(n+1)) =
    alt (2*n) * (3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) *
      ((6*n+1).factorial : ℚ) * 3^(2*n) * ((2*n+1).factorial : ℚ)) := by
  unfold alt
  rw [Nat.mul_succ, prod_range_succ, prod_range_succ]
  rw [prod_range_succ (fun k => gap (2*n+1) k)]
  have hc := cross_factors n
  rw [prod_mul_distrib] at hc
  simp only [gap, node_even, node_odd] at hc ⊢
  rw [Nat.factorial_succ (2*n)]
  push_cast
  linear_combination (∏ x ∈ range (2*n), node x * ∏ k ∈ range x, ((node x)^2-(node k)^2)) *
    (3*(n:ℚ)+1)*(3*(n:ℚ)+2)*(6*(n:ℚ)+3) * hc

private theorem den_step (n : ℕ) : den (2*(n+1)) =
    den (2*n) * ((4*n+1).factorial : ℚ) * ((4*n+3).factorial : ℚ) := by
  simp only [den, Nat.mul_succ, prod_range_succ]
  rw [show 2*(2*n)+1=4*n+1 by omega, show 2*(2*n)+2+1=4*n+3 by omega]

private theorem frac_cleared (n : ℕ) :
    frac (n+1) * (2 * ((4*n+2).factorial : ℚ) * ((4*n+3).factorial : ℚ)) =
      ((6*n+4).factorial : ℚ) * ((2*n+1).factorial : ℚ) := by
  let k := 2*n+2
  have hkn : k ≤ 6*n+4 := by dsimp [k]; omega
  have hkd : k ≤ 4*n+3 := by dsimp [k]; omega
  have hn := Nat.choose_mul_factorial_mul_factorial hkn
  have hd := Nat.choose_mul_factorial_mul_factorial hkd
  rw [show 6*n+4-k = 4*n+2 by dsimp [k]; omega] at hn
  rw [show 4*n+3-k = 2*n+1 by dsimp [k]; omega] at hd
  have nz : ((4*n+3).choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkd).ne'
  unfold frac
  rw [show 6*(n+1)-2 = 6*n+4 by omega, show 4*(n+1)-1 = 4*n+3 by omega,
    show 2*(n+1)=k by dsimp [k]; omega, ← hn, ← hd]
  push_cast
  field_simp

/-- 已知所有规模的冰点计数时，原题的相邻项比值由两个新增节点的乘积给出。 -/
theorem ratio_of_enumeration
    (count : ∀ n : ℕ, (3:ℚ)^(n*(n-1)) * (b n : ℚ) = homogeneous (2*n))
    (n : ℕ) : frac (n+1) = (b (n+1):ℚ) / (b n:ℚ) := by
  have h := alt_step n
  rw [← cleared, ← cleared, ← count, ← count, den_step] at h
  have exponent : (n+1)*(n+1-1) = n*(n-1) + 2*n := by
    cases n <;> simp <;> ring
  rw [exponent, pow_add] at h
  have hden : den (2*n) ≠ 0 := by unfold den; positivity
  have hb : (b n : ℚ) ≠ 0 := by exact_mod_cast (Partial.count_positive n).ne'
  have hf := frac_cleared n
  rw [show 6*n+4 = (6*n+1)+1+1+1 by omega, Nat.factorial_succ (6*n+1+1+1),
    Nat.factorial_succ (6*n+1+1), Nat.factorial_succ (6*n+1),
    Nat.factorial_succ (4*n+1)] at hf
  push_cast at hf
  apply (eq_div_iff hb).mpr
  have hp : (3:ℚ)^(n*(n-1)) ≠ 0 := by positivity
  have hp' : (3:ℚ)^(2*n) ≠ 0 := by positivity
  apply mul_right_cancel₀ (show (den (2*n) * 3^(n*(n-1)) * 3^(2*n) *
    ((4*n+1).factorial : ℚ) * ((4*n+3).factorial : ℚ) * (4*(n:ℚ)+2)) ≠ 0 by positivity)
  linear_combination
    (den (2*n) * 3^(n*(n-1)) * 3^(2*n) * (b n:ℚ)/2) * hf -
    (4*(n:ℚ)+2) * h

end OeisA109074.Ratio

end

section

namespace OeisA109074.Solution

open Partial.SixVertex Partial.Partition Tsuchiya

private theorem sign_formula {K : Type} [Field K] (n : ℕ) :
    blockSign K n = (-1 : K)^(n.choose 2) := by
  induction n with
  | zero => simp [blockSign]
  | succ n ih => rw [blockSign, ih, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

/-- 将冰点上的网格恒等式还原到原题的有理数计数，并消去所有非零的顶点权。 -/
theorem enumeration_from_partition {K : Type} [Field K] [CharZero K]
    (q : K) (hq : q^2+1=q) (n : ℕ)
    (h : domainPartition q (q*q) (List.replicate n q) (List.replicate n 1) =
      prefactor q (q*q) (fun _ : Fin n => q) (fun _ => 1) * blockSign K n *
      (algebraMap ℚ K) (Ratio.homogeneous (2*n))) :
    (3 : ℚ)^(n*(n-1)) * (b n : ℚ) = Ratio.homogeneous (2*n) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hw : iceWeight q ≠ 0 := by
    intro hz
    have hh := (ice_weights q hq).2
    rw [hz, zero_pow (by decide), zero_eq_mul] at hh
    rcases hh with h | h <;> simp_all
  have hp : prefactor q (q*q) (fun _ : Fin n => q) (fun _ => 1) ≠ 0 := by
    rw [ice_prefactor q hq]
    exact mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ (neg_ne_zero.mpr (pow_ne_zero _ hq0)))
  have hsign : (-1 : K)^(n.choose 2) ≠ 0 := by simp
  rw [sign_formula, domain_counts_vsasm _ (by simpa [sq] using hq)] at h
  have hs := homogeneous_scale q hq n
  have hw_eq : iceWeight q = bulkWeight q := by simp [iceWeight, bulkWeight, sq]
  rw [hw_eq] at hs
  rw [← hs, mul_assoc] at h
  apply (algebraMap ℚ K).injective
  simpa using (mul_left_cancel₀ (mul_ne_zero hp hsign) h)

private noncomputable def icePoint : ℂ := ⟨1/2, Real.sqrt 3 / 2⟩

private theorem icePoint_eq : icePoint^2 + 1 = icePoint := by
  apply Complex.ext <;> simp [icePoint, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]

/-- 在复数域的冰点得到每个规模的精确计数，再取相邻两项的比值。 -/
theorem all_ratios (n : ℕ) : frac (n+1) = (b (n+1) : ℚ) / (b n : ℚ) :=
  Ratio.ratio_of_enumeration (fun m => enumeration_from_partition icePoint icePoint_eq m
    (Specialization.specialize_grid icePoint icePoint_eq m)) n

end OeisA109074.Solution

/-- 对上游 OEIS A109074 命题的独立证明。 -/
theorem OMA.solution : type_of% @OeisA109074.conjecture :=
  OeisA109074.Solution.all_ratios

end
