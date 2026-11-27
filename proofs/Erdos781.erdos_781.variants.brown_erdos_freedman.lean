import FormalConjectures.ErdosProblems.«781»
import Mathlib.Data.List.GetD

/-!
# The Brown–Erdős–Freedman bounds on descending waves

The lower bound uses alternating pairs of shrinking monochromatic blocks.
For the upper bound, use the first monochromatic block after a sequence of
mixed blocks. The quadratic spacing of sampled block indices gives
decreasing gaps and allows the entire last block to be appended.

This formalizes Theorem 4 of Brown, Erdős and Freedman,
*Quasi-progressions and descending waves* (1990).
-/

-- Credit: @ysanatomic

namespace OMA.Erdos781

private theorem append_consecutive {k s b : ℕ} (hsk : s ≤ k)
    (x : Fin s → ℕ) (hx : Erdos781.IsDescendingWave x)
    (hbefore : ∀ i, x i < b)
    (hjoin : ∀ i j : Fin s, (i:ℕ)+1=j → (j:ℕ)+1=s → x i + b ≤ 2*x j)
    (c : ℕ → Fin 2) (γ : Fin 2) (hc : ∀ i, c (x i) = γ)
    (hblock : ∀ a, b ≤ a → a < b+(k-s) → c a = γ) :
    ∃ y : Fin k → ℕ, Erdos781.IsDescendingWave y ∧
      (∀ i, y i < b+(k-s)) ∧ ∀ i, c (y i) = γ := by
  let y (i : Fin k) : ℕ := if h : i.val < s then x ⟨i.val,h⟩ else b+(i.val-s)
  refine ⟨y, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    have hij' : i.val < j.val := hij
    dsimp only [y]
    split_ifs with hi hj hj
    · exact hx.1 hij'
    · have hh := hbefore ⟨i.val,hi⟩
      omega
    · omega
    · omega
  · intro i j l hij hjl
    dsimp only [y]
    by_cases hi : (i : ℕ) < s <;> by_cases hj : (j : ℕ) < s <;> by_cases hl : (l : ℕ) < s <;>
      simp only [hi, hj, hl, dite_true, dite_false]
    · exact hx.2 ⟨i.val,hi⟩ ⟨j.val,hj⟩ ⟨l.val,hl⟩ hij hjl
    · have hls : l.val = s := by omega
      have hjs : j.val + 1 = s := by omega
      have hh := hjoin ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij hjs
      omega
    · omega
    · have hh := hbefore ⟨i.val,hi⟩
      omega
    · omega
    · omega
    · omega
    · omega
  · intro i
    have hi := i.isLt
    dsimp only [y]
    split_ifs with hs
    · have hh := hbefore ⟨i.val,hs⟩
      omega
    · omega
  · intro i
    have hi := i.isLt
    dsimp only [y]
    split_ifs with hs
    · exact hc ⟨i.val,hs⟩
    · exact hblock _ (by omega) (by omega)

private def Forces (k n : ℕ) : Prop :=
  ∀ c : Fin n → Fin 2, ∃ x : Fin k → Fin n,
    Erdos781.IsDescendingWave (fun i ↦ (x i : ℕ)) ∧ ∃ γ, ∀ i, c (x i) = γ

private theorem forces_mono {k n m : ℕ} (hnm : n ≤ m) (h : Forces k n) : Forces k m := by
  intro c
  obtain ⟨x, hx, γ, hγ⟩ := h (fun i ↦ c (Fin.castLE hnm i))
  exact ⟨fun i ↦ Fin.castLE hnm (x i), hx, γ, hγ⟩

private theorem forces_singleton : Forces 1 1 := by
  intro c
  refine ⟨fun _ ↦ 0, ⟨?_, ?_⟩, c 0, fun _ ↦ rfl⟩
  · intro i j hij
    fin_cases i; fin_cases j
    exact (lt_irrefl _ hij).elim
  · intro i j l hij hjl
    norm_num

private theorem lower_singleton : 1 ≤ Erdos781.f 1 := by
  have h : sInf {n : ℕ | Forces 1 n} ∈ {n : ℕ | Forces 1 n} :=
    Nat.sInf_mem ⟨1, forces_singleton⟩
  have h' : Forces 1 (Erdos781.f 1) := h
  obtain ⟨x, _⟩ := h' (fun _ ↦ 0)
  have hpos := (x 0).isLt
  omega

end OMA.Erdos781

namespace OMA.Erdos781

def blockStart (w : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, w j

private theorem blockStart_succ (w : ℕ → ℕ) (i : ℕ) :
    blockStart w (i + 1) = blockStart w i + w i := by
  exact Finset.sum_range_succ w i

private theorem blockStart_mono (w : ℕ → ℕ) : Monotone (blockStart w) :=
  monotone_nat_of_le_succ fun n ↦ by rw [blockStart_succ]; omega

private theorem blockStart_compare (w : ℕ → ℕ) (hAnti : Antitone w)
    (a b n : ℕ) (hab : a ≤ b) :
    blockStart w a + blockStart w (b + n) ≤ blockStart w (a + n) + blockStart w b := by
  have hSum :
      ∑ j ∈ Finset.range n, w (b + j) ≤ ∑ j ∈ Finset.range n, w (a + j) :=
    Finset.sum_le_sum fun j _ ↦ hAnti (Nat.add_le_add_right hab j)
  unfold blockStart
  rw [Finset.sum_range_add, Finset.sum_range_add]
  omega

theorem sampleWave (w : ℕ → ℕ) (hAnti : Antitone w) {s t : ℕ}
    (hs : 0 < s) (hst : s * (s - 1) + 1 ≤ t) (x : Fin t → ℕ)
    (hx : ∀ i : Fin t, blockStart w i ≤ x i ∧ x i < blockStart w ((i : ℕ) + 1)) :
    ∃ y : Fin s → Fin t, Erdos781.IsDescendingWave (x ∘ y) ∧
      (∀ i j : Fin s, i < j → x (y i) + w (t - 1) ≤ x (y j)) ∧
      ∀ j : Fin s, (j : ℕ) + 1 = s → (y j : ℕ) = t - 1 := by
  let offset (r : ℕ) : ℕ := r * (r + 1)
  let rem (i : Fin s) : ℕ := s - 1 - (i : ℕ)
  let idx (i : Fin s) : ℕ := t - 1 - offset (rem i)
  have hoffset_mono : Monotone offset := fun r R hr ↦
    Nat.mul_le_mul hr (Nat.add_le_add_right hr 1)
  have hoffset (i : Fin s) : offset (rem i) ≤ t - 1 := by
    have hrem : rem i ≤ s - 1 := Nat.sub_le _ _
    have hbound := hoffset_mono hrem
    have hTop : offset (s - 1) = s * (s - 1) := by
      unfold offset
      rw [show s - 1 + 1 = s by omega, Nat.mul_comm]
    omega
  have hidx (i : Fin s) : idx i + offset (rem i) = t - 1 :=
    Nat.sub_add_cancel (hoffset i)
  have ht : 0 < t := by omega
  let y (i : Fin s) : Fin t :=
    ⟨idx i, lt_of_le_of_lt (Nat.sub_le _ _) (by omega)⟩
  have hSpacing (i j : Fin s) (hij : i < j) : idx i + 2 ≤ idx j := by
    have hi := i.isLt
    have hj := j.isLt
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hrem : rem j + 1 ≤ rem i := by
      dsimp [rem]
      omega
    have hCompare := hoffset_mono hrem
    have hGain : offset (rem j) + 2 ≤ offset (rem j + 1) := by
      unfold offset
      nlinarith
    have him := hidx i
    have hjm := hidx j
    omega
  have hSecond (i j l : Fin s) (hij : (i : ℕ) + 1 = j) (hjl : (j : ℕ) + 1 = l) :
      idx i + idx l + 2 = 2 * idx j := by
    have hi := i.isLt
    have hj := j.isLt
    have hl := l.isLt
    have hri : rem i = rem j + 1 := by
      dsimp [rem]
      omega
    have hrj : rem j = rem l + 1 := by
      dsimp [rem]
      omega
    have hIdentity : offset (rem i) + offset (rem l) = 2 * offset (rem j) + 2 := by
      rw [hri, hrj]
      unfold offset
      ring
    have him := hidx i
    have hjm := hidx j
    have hlm := hidx l
    omega
  refine ⟨y, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    have hle := hSpacing i j hij
    have hStarts := blockStart_mono w (show idx i + 1 ≤ idx j by omega)
    exact ((hx (y i)).2.trans_le hStarts).trans_le (hx (y j)).1
  · intro i j l hij hjl
    have hij' : i < j := by
      change (i : ℕ) < (j : ℕ)
      omega
    let n := idx j - (idx i + 1)
    have hSpacing' := hSpacing i j hij'
    have hSecond' := hSecond i j l hij hjl
    have hLeft : idx i + 1 + n = idx j := by
      dsimp [n]
      omega
    have hRight : idx j + n = idx l + 1 := by
      dsimp [n]
      omega
    have hStarts := blockStart_compare w hAnti (idx i + 1) (idx j) n (by omega)
    rw [hLeft, hRight] at hStarts
    have hxi : x (y i) < blockStart w (idx i + 1) := (hx (y i)).2
    have hxj : blockStart w (idx j) ≤ x (y j) := (hx (y j)).1
    have hxl : x (y l) < blockStart w (idx l + 1) := (hx (y l)).2
    change x (y i) + x (y l) ≤ 2 * x (y j)
    omega
  · intro i j hij
    have hle := hSpacing i j hij
    have hj : idx j < t := (y j).isLt
    have hw := hAnti (show idx i + 1 ≤ t - 1 by omega)
    have hStarts := blockStart_mono w (show idx i + 1 + 1 ≤ idx j by omega)
    rw [blockStart_succ w (idx i + 1)] at hStarts
    have hxi : x (y i) < blockStart w (idx i + 1) := (hx (y i)).2
    have hxj : blockStart w (idx j) ≤ x (y j) := (hx (y j)).1
    omega

  · intro j hj
    have hRem : rem j = 0 := by
      dsimp [rem]
      omega
    change idx j = t - 1
    simp [idx, hRem, offset]

end OMA.Erdos781

namespace OMA.Waves781

/-- The completed stages before the last singleton block. -/
private def stagePrefix : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => stagePrefix n ++ List.replicate (2 * (n + 1)) (n + 1)

private lemma stagePrefix_length (n : ℕ) : (stagePrefix n).length = n * (n + 1) + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stagePrefix, List.length_append, List.length_replicate, ih]
    ring

private lemma stagePrefix_pos (n : ℕ) : 0 < (stagePrefix n).length := by
  rw [stagePrefix_length]
  omega

private lemma stagePrefix_first (n : ℕ) : (stagePrefix n)[0]'(stagePrefix_pos n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (stagePrefix n ++ List.replicate (2 * (n + 1)) (n + 1))[0] = 0
    rw [List.getElem_append_left (stagePrefix_pos n)]
    exact ih

private lemma stagePrefix_mem_le {n s : ℕ} (hs : s ∈ stagePrefix n) : s ≤ n := by
  induction n with
  | zero => simpa [stagePrefix] using hs
  | succ n ih =>
    rw [stagePrefix, List.mem_append] at hs
    rcases hs with hs | hs
    · exact (ih hs).trans (Nat.le_succ _)
    · exact (List.mem_replicate.mp hs).2.le

private lemma stagePrefix_pairwise (n : ℕ) : (stagePrefix n).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp [stagePrefix]
  | succ n ih =>
    rw [stagePrefix, List.pairwise_append]
    refine ⟨ih, List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
    intro a ha b hb
    rw [(List.mem_replicate.mp hb).2]
    exact (stagePrefix_mem_le ha).trans (Nat.le_succ _)

private lemma stagePrefix_barrier (n j : ℕ) (hj : j < (stagePrefix n).length)
    (hs : 0 < (stagePrefix n)[j]) :
    (stagePrefix n)[j] * ((stagePrefix n)[j] - 1) + 1 ≤ j := by
  induction n with
  | zero =>
    have h : j = 0 := by simpa [stagePrefix] using hj
    subst j
    simp [stagePrefix] at hs
  | succ n ih =>
    simp only [stagePrefix] at hs ⊢
    by_cases hj' : j < (stagePrefix n).length
    · rw [List.getElem_append_left hj'] at hs ⊢
      exact ih hj' hs
    · rw [List.getElem_append_right (Nat.le_of_not_gt hj'), List.getElem_replicate,
        Nat.add_sub_cancel]
      rw [stagePrefix_length] at hj'
      simpa [Nat.mul_comm] using Nat.le_of_not_gt hj'

private lemma stagePrefix_sum (k n : ℕ) (hkn : n ≤ k) :
    (((stagePrefix n).map fun s => k - s).sum : ℚ) =
      k + (k : ℚ) * n * (n + 1) - (n : ℚ) * (n + 1) * (2 * n + 1) / 3 := by
  induction n with
  | zero => simp [stagePrefix]
  | succ n ih =>
    simp only [stagePrefix, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
    rw [ih (by omega), Nat.cast_sub hkn]
    push_cast
    ring

lemma exists_block_layout (k : ℕ) (hk : 2 ≤ k) :
    ∃ (B : ℕ) (width : ℕ → ℕ), Antitone width ∧ 0 < B ∧
      (∀ j, 0 < width j) ∧ width 0 = k ∧ width (B - 1) = 1 ∧
      (∀ j < B, 0 < k - width j → (k - width j) * (k - width j - 1) + 1 ≤ j) ∧
      ((∑ j ∈ Finset.range B, width j) : ℚ) ≤ ((k : ℚ) ^ 3 - 4 * k + 9) / 3 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hk
  have hk' : k = n + 2 := by omega
  clear hn
  subst k
  let L := stagePrefix n ++ [n + 1]
  let B := L.length
  let stage (j : ℕ) := L.getD j (n + 1)
  let width (j : ℕ) := n + 2 - stage j
  have hB : B = (stagePrefix n).length + 1 := by simp [B, L]
  have hL : L.Pairwise (· ≤ ·) := by
    change (stagePrefix n ++ [n + 1]).Pairwise (· ≤ ·)
    rw [List.pairwise_append]
    refine ⟨stagePrefix_pairwise _, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    rw [hb]
    exact (stagePrefix_mem_le ha).trans (Nat.le_succ _)
  have hstage (j : ℕ) : stage j ≤ n + 1 := by
    by_cases hj : j < B
    · have hm : stage j ∈ L := by
        change L.getD j (n + 1) ∈ L
        rw [List.getD_eq_getElem L _ hj]
        exact List.getElem_mem hj
      change stage j ∈ stagePrefix n ++ [n + 1] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact (stagePrefix_mem_le hm).trans (Nat.le_succ _)
      · exact (List.mem_singleton.mp hm).le
    · dsimp only [stage]
      rw [List.getD_eq_default L _ (Nat.le_of_not_gt hj)]
  have hanti : Antitone width := by
    intro i j hij
    apply Nat.sub_le_sub_left _
    by_cases hj : j < B
    · have hi : i < B := hij.trans_lt hj
      dsimp only [stage]
      rw [List.getD_eq_getElem L _ hi, List.getD_eq_getElem L _ hj]
      rcases hij.eq_or_lt with rfl | hij'
      · rfl
      · exact List.pairwise_iff_getElem.mp hL i j hi hj hij'
    · dsimp only [stage]
      rw [List.getD_eq_default L _ (Nat.le_of_not_gt hj)]
      exact hstage i
  have hBpos : 0 < B := by omega
  have hlast : stage (B - 1) = n + 1 := by
    have hj : B - 1 < L.length := by change B - 1 < B; omega
    dsimp only [stage]
    rw [List.getD_eq_getElem L _ hj]
    change (stagePrefix n ++ [n + 1])[B-1] = n + 1
    rw [List.getElem_append_right (by omega)]
    simp
  refine ⟨B, width, hanti, hBpos, fun j => ?_, ?_, ?_, ?_, ?_⟩
  · have := hstage j
    change 0 < n + 2 - stage j
    omega
  · change n + 2 - stage 0 = n + 2
    dsimp only [stage]
    rw [List.getD_eq_getElem L _ hBpos]
    change n + 2 - (stagePrefix n ++ [n + 1])[0] = n + 2
    rw [List.getElem_append_left (stagePrefix_pos n), stagePrefix_first, Nat.sub_zero]
  · change n + 2 - stage (B - 1) = 1
    rw [hlast]
    omega
  · intro j hj hpos
    have hstep : n + 2 - width j = stage j :=
      Nat.sub_sub_self ((hstage j).trans (Nat.le_succ _))
    rw [hstep] at hpos ⊢
    by_cases hj' : j < (stagePrefix n).length
    · dsimp only [stage] at hpos ⊢
      rw [List.getD_eq_getElem L _ hj] at hpos ⊢
      dsimp only [L] at hpos ⊢
      rw [List.getElem_append_left hj'] at hpos ⊢
      exact stagePrefix_barrier n j hj' hpos
    · have hlastj : j = B - 1 := by omega
      rw [hlastj, hlast, Nat.add_sub_cancel, hB, Nat.add_sub_cancel, stagePrefix_length,
        Nat.mul_comm (n + 1) n]
  · have hsum : (∑ j ∈ Finset.range B, width j) = (L.map fun s => n + 2 - s).sum := by
      rw [← Fin.sum_univ_eq_sum_range width B, ← Fin.sum_univ_fun_getElem]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [width, stage, List.getD_eq_getElem L _ j.isLt]
    have hsumlast : (L.map fun s => n + 2 - s).sum =
        ((stagePrefix n).map fun s => n + 2 - s).sum + 1 := by
      simp [L]
    apply le_of_eq
    rw [← Nat.cast_sum, hsum, hsumlast, Nat.cast_add, stagePrefix_sum (n + 2) n (by omega)]
    push_cast
    ring

end OMA.Waves781

namespace OMA.DescendingWaves

private def pairEnd (l : ℕ) : ℕ := l * (l + 1)

private lemma pairEnd_mono : Monotone pairEnd := by
  intro a b hab
  unfold pairEnd
  exact Nat.mul_le_mul hab (by omega)

private def reversed (m : ℕ) (i : Fin (pairEnd m)) : ℕ :=
  pairEnd m - (i.val + 1)

private lemma reversed_strictAnti (m : ℕ) : StrictAnti (reversed m) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  change i.val < j.val at hij
  unfold reversed
  omega

private theorem width_exists (m : ℕ) (i : Fin (pairEnd m)) :
    ∃ l, reversed m i < pairEnd l := by
  refine ⟨m, ?_⟩
  have hi := i.isLt
  unfold reversed
  omega

private noncomputable def width (m : ℕ) (i : Fin (pairEnd m)) : ℕ :=
  Nat.find (width_exists m i)

private lemma reversed_lt_end (m : ℕ) (i : Fin (pairEnd m)) :
    reversed m i < pairEnd (width m i) :=
  Nat.find_spec (width_exists m i)

private lemma width_pos (m : ℕ) (i : Fin (pairEnd m)) : 0 < width m i := by
  by_contra! h
  have hz : width m i = 0 := by omega
  have ht := reversed_lt_end m i
  rw [hz] at ht
  simp [pairEnd] at ht

private lemma width_le (m : ℕ) (i : Fin (pairEnd m)) : width m i ≤ m :=
  by
    apply Nat.find_min' (width_exists m i)
    have hi := i.isLt
    unfold reversed
    omega

private lemma width_anti (m : ℕ) : Antitone (width m) := by
  intro i j hij
  apply Nat.find_min' (width_exists m j)
  exact ((reversed_strictAnti m).antitone hij).trans_lt (reversed_lt_end m i)

private lemma prev_end_le_reversed (m : ℕ) (i : Fin (pairEnd m)) :
    pairEnd (width m i - 1) ≤ reversed m i := by
  apply Nat.le_of_not_gt
  intro h
  have hp := width_pos m i
  have hmin : width m i ≤ width m i - 1 := Nat.find_min' (width_exists m i) h
  omega

private lemma pairEnd_prev {l : ℕ} (hl : 0 < l) :
    pairEnd (l - 1) + l = l ^ 2 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  change q * (q + 1) + (q + 1) = (q + 1) ^ 2
  ring

private lemma pairEnd_eq (l : ℕ) : pairEnd l = l ^ 2 + l := by
  unfold pairEnd
  ring

private noncomputable def blockColor (m : ℕ) (i : Fin (pairEnd m)) : Fin 2 :=
  if reversed m i < width m i ^ 2 then 0 else 1

private def blockBase (l : ℕ) (γ : Fin 2) : ℕ :=
  pairEnd (l - 1) + γ.val * l

private lemma block_bounds {m : ℕ} {i : Fin (pairEnd m)} {γ : Fin 2}
    (hcolor : blockColor m i = γ) :
    blockBase (width m i) γ ≤ reversed m i ∧
      reversed m i < blockBase (width m i) γ + width m i := by
  have hp := pairEnd_prev (width_pos m i)
  have hleft := prev_end_le_reversed m i
  have hright := reversed_lt_end m i
  rw [pairEnd_eq] at hright
  unfold blockColor at hcolor
  split at hcolor
  next h =>
    subst γ
    simpa only [blockBase, Fin.val_zero, zero_mul, add_zero, hp] using And.intro hleft h
  next h =>
    subst γ
    simpa only [blockBase, Fin.val_one, one_mul, hp] using And.intro (Nat.le_of_not_gt h) hright

private lemma same_width_gap {m : ℕ} {i j : Fin (pairEnd m)}
    {γ : Fin 2} (hi : blockColor m i = γ) (hj : blockColor m j = γ)
    (hwidth : width m i = width m j) :
    j.val - i.val < width m i := by
  have hb₁ := block_bounds hi
  have hb₂ := block_bounds hj
  rw [← hwidth] at hb₂
  have hp := width_pos m i
  have hii := i.isLt
  have hjj := j.isLt
  unfold reversed at hb₁ hb₂
  omega

private lemma different_width_gap {m : ℕ} {i j : Fin (pairEnd m)}
    {γ : Fin 2} (hi : blockColor m i = γ) (hj : blockColor m j = γ)
    (hwidth : width m j < width m i) :
    width m i ≤ j.val - i.val := by
  have hb₁ := block_bounds hi
  have hb₂ := block_bounds hj
  have hp := width_pos m i
  have hp' := width_pos m j
  have hwidth' : width m j ≤ width m i - 1 := by omega
  have hmono := pairEnd_mono hwidth'
  have hsquare : width m j ^ 2 ≤ (width m i - 1) ^ 2 := Nat.pow_le_pow_left hwidth' _
  have hpi := pairEnd_prev hp
  have hpj := pairEnd_prev hp'
  have hend := pairEnd_eq (width m i - 1)
  have hend' := pairEnd_eq (width m j)
  have hii := i.isLt
  have hjj := j.isLt
  fin_cases γ
  · simp only [blockBase, zero_mul, add_zero] at hb₁ hb₂
    rw [hpj] at hb₂
    unfold reversed at hb₁ hb₂
    omega
  · simp only [blockBase, one_mul, hpi, hpj] at hb₁ hb₂
    unfold reversed at hb₁ hb₂
    omega

private def waveGap {m N : ℕ} (x : Fin (m + 1) → Fin N) (i : Fin m) : ℕ :=
  (x i.succ).val - (x i.castSucc).val

private lemma waveGap_antitone {m N : ℕ} {x : Fin (m + 1) → Fin N}
    (hx : Erdos781.IsDescendingWave (fun i ↦ (x i : ℕ))) :
    Antitone (waveGap x) := by
  cases m with
  | zero =>
    intro i
    exact Fin.elim0 i
  | succ m =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have hw := hx.2 i.castSucc.castSucc i.succ.castSucc i.succ.succ rfl rfl
    change (x i.castSucc.castSucc).val + (x i.succ.succ).val ≤
      2 * (x i.succ.castSucc).val at hw
    simp only [waveGap, Fin.succ_castSucc]
    omega

private lemma repeat_width {m : ℕ} {x : Fin (m + 1) → Fin (pairEnd m)}
    (hx : Erdos781.IsDescendingWave (fun i ↦ (x i : ℕ)))
    {γ : Fin 2} (hc : ∀ i, blockColor m (x i) = γ)
    {i j : Fin (m + 1)} (hij : i < j)
    (hw : width m (x i) = width m (x j)) :
    width m (x i) = width m (x (Fin.last m)) := by
  have hanti : Antitone (fun i ↦ width m (x i)) := by
    intro i j hij
    exact width_anti m (show x i ≤ x j from hx.1.monotone hij)
  have hival := i.isLt
  have hjval := j.isLt
  have hijval : i.val < j.val := hij
  let iGap : Fin m := ⟨i, by omega⟩
  have hi_eq : iGap.castSucc = i := Fin.ext rfl
  have hinext_le : iGap.succ ≤ j := by
    change i.val + 1 ≤ j.val
    omega
  have hsame : width m (x iGap.castSucc) = width m (x iGap.succ) := by
    have hstep : iGap.castSucc ≤ iGap.succ := by
      change iGap.val ≤ iGap.val + 1
      omega
    have h₁ := hanti hstep
    have h₂ := hanti hinext_le
    change width m (x iGap.succ) ≤ width m (x iGap.castSucc) at h₁
    change width m (x j) ≤ width m (x iGap.succ) at h₂
    rw [hi_eq] at h₁
    rw [hi_eq]
    omega
  have hsmall : waveGap x iGap < width m (x i) := by
    rw [← hi_eq]
    exact same_width_gap (hc _) (hc _) hsame
  have hgaps := waveGap_antitone hx
  have hall (n : ℕ) (hin : i.val ≤ n) (hn : n < m + 1) :
      width m (x ⟨n, hn⟩) = width m (x i) := by
    induction n, hin using Nat.le_induction with
    | base => rfl
    | succ n hin ih =>
      let g : Fin m := ⟨n, by omega⟩
      have hnow : width m (x g.castSucc) = width m (x i) := ih (by omega)
      have hnext : width m (x g.succ) ≤ width m (x g.castSucc) :=
        hanti (show g.castSucc ≤ g.succ by change n ≤ n + 1; omega)
      have hg := hgaps (show iGap ≤ g from hin)
      change width m (x g.succ) = width m (x i)
      by_contra! hne
      have hlt : width m (x g.succ) < width m (x g.castSucc) := by omega
      have hjump : width m (x g.castSucc) ≤ waveGap x g :=
        different_width_gap (hc _) (hc _) hlt
      omega
  exact (hall m (by omega) (by omega)).symm

private lemma lower_obstruction_aux (m : ℕ) :
    ∃ c : Fin (pairEnd m) → Fin 2, ¬ ∃ x : Fin (m + 1) → Fin (pairEnd m),
      Erdos781.IsDescendingWave (fun i ↦ (x i : ℕ)) ∧ ∃ γ, ∀ i, c (x i) = γ := by
  refine ⟨blockColor m, ?_⟩
  rintro ⟨x, hx, γ, hc⟩
  let l := width m (x (Fin.last m))
  have hanti : Antitone (fun i ↦ width m (x i)) := by
    intro i j hij
    exact width_anti m (show x i ≤ x j from hx.1.monotone hij)
  have hl (i : Fin (m + 1)) : l ≤ width m (x i) := hanti (Fin.le_last i)
  have hℓ : 0 < l := width_pos _ _
  let code (i : Fin (m + 1)) : Fin m :=
    if h : width m (x i) = l then
      ⟨m - l + (reversed m (x i) - blockBase l γ), by
        have hb := (block_bounds (hc i)).2
        rw [h] at hb
        have hm := width_le m (x i)
        omega⟩
    else
      ⟨m - width m (x i), Nat.sub_lt (hℓ.trans_le (width_le _ _)) (width_pos _ _)⟩
  have hcode : Function.Injective code := by
    intro i j hij
    have hval := congrArg Fin.val hij
    have hli := hl i
    have hlj := hl j
    have hmi := width_le m (x i)
    have hmj := width_le m (x j)
    by_cases hi : width m (x i) = l
    · by_cases hj : width m (x j) = l
      · simp only [code, dif_pos hi, dif_pos hj] at hval
        have hleft := (block_bounds (hc i)).1
        have hright := (block_bounds (hc j)).1
        rw [hi] at hleft
        rw [hj] at hright
        have hrev : reversed m (x i) = reversed m (x j) := by omega
        exact hx.1.injective (congrArg Fin.val ((reversed_strictAnti m).injective hrev))
      · simp only [code, dif_pos hi, dif_neg hj] at hval
        omega
    · by_cases hj : width m (x j) = l
      · simp only [code, dif_neg hi, dif_pos hj] at hval
        omega
      · simp only [code, dif_neg hi, dif_neg hj] at hval
        have hw : width m (x i) = width m (x j) := by omega
        rcases lt_trichotomy i j with h | h | h
        · exact (hi (repeat_width hx hc h hw)).elim
        · exact h
        · exact (hj (repeat_width hx hc h hw.symm)).elim
  have hcard := Fintype.card_le_of_injective code hcode
  simp only [Fintype.card_fin] at hcard
  omega

lemma lower_obstruction (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : Fin (k ^ 2 - k) → Fin 2, ¬ ∃ x : Fin k → Fin (k ^ 2 - k),
      Erdos781.IsDescendingWave (fun i ↦ (x i : ℕ)) ∧ ∃ γ, ∀ i, c (x i) = γ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : (m + 1)^2 - (m + 1) = pairEnd m := by
    apply Nat.sub_eq_of_eq_add
    unfold pairEnd
    ring
  rw [h]
  exact lower_obstruction_aux m

end OMA.DescendingWaves

namespace OMA.Erdos781

private theorem starts_step (w : ℕ → ℕ) (i : ℕ) :
    blockStart w (i+1) = blockStart w i + w i := Finset.sum_range_succ _ _

private theorem starts_mono (w : ℕ → ℕ) : Monotone (blockStart w) :=
  monotone_nat_of_le_succ (fun i ↦ by rw [starts_step]; omega)

private theorem forces_of_block_layout (k B : ℕ) (w : ℕ → ℕ)
    (hB : 0 < B) (hmono : Antitone w) (hw0 : w 0 = k) (hwlast : w (B-1) = 1)
    (hskip : ∀ j < B, 0 < k-w j → (k-w j)*((k-w j)-1)+1 ≤ j) :
    Forces k (blockStart w B) := by
  intro coloring
  let N := blockStart w B
  let C (a : ℕ) : Fin 2 := if ha : a < N then coloring ⟨a,ha⟩ else 0
  let Mono (j : ℕ) : Prop := ∃ γ : Fin 2, ∀ a : ℕ, blockStart w j ≤ a →
    a < blockStart w (j+1) → C a = γ
  have hLast : Mono (B-1) := by
    refine ⟨C (blockStart w (B-1)), fun a ha hb ↦ ?_⟩
    rw [starts_step, hwlast] at hb
    have he : a = blockStart w (B-1) := by omega
    rw [he]
  have hex : ∃ j, j < B ∧ Mono j := ⟨B-1, by omega, hLast⟩
  let t := Nat.find hex
  have ht : t < B ∧ Mono t := Nat.find_spec hex
  obtain ⟨γ,hγ⟩ := ht.2
  let b := blockStart w t
  let s := k-w t
  have hwk : w t ≤ k := hw0 ▸ hmono (Nat.zero_le t)
  have hsk : s ≤ k := by dsimp [s]; omega
  have hslen : k-s=w t := by dsimp [s]; omega
  have hend : b+(k-s)=blockStart w (t+1) := by rw [starts_step, hslen]
  have hTail (a : ℕ) (ha : b ≤ a) (hb : a < b+(k-s)) : C a=γ :=
    hγ a ha (hend ▸ hb)
  have hPrevious (i : Fin t) :
      ∃ a : ℕ, (blockStart w i ≤ a ∧ a < blockStart w ((i:ℕ)+1)) ∧ C a = γ := by
    by_contra h
    let other : Fin 2 := ⟨1-(γ:ℕ), by omega⟩
    apply Nat.find_min hex i.isLt
    refine ⟨i.isLt.trans ht.1, other, fun a ha hb ↦ ?_⟩
    have hne : C a ≠ γ := fun he ↦ h ⟨a,⟨ha,hb⟩,he⟩
    have hval : (C a : ℕ) ≠ (γ : ℕ) := fun he ↦ hne (Fin.ext he)
    apply Fin.ext
    change (C a : ℕ) = 1-(γ:ℕ)
    omega
  have hPrefix : ∃ x : Fin s → ℕ, Erdos781.IsDescendingWave x ∧
      (∀ i, x i < b) ∧
      (∀ i j : Fin s, (i:ℕ)+1=j → (j:ℕ)+1=s → x i + b ≤ 2*x j) ∧
      ∀ i, C (x i) = γ := by
    rcases Nat.eq_zero_or_pos s with hzero | hspos
    · rw [hzero]
      refine ⟨Fin.elim0, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i
    · choose u hmem hpaint using hPrevious
      have hst : s*(s-1)+1 ≤ t := hskip t ht.1 hspos
      obtain ⟨e, he, hgap, hlast⟩ := sampleWave w hmono hspos hst u hmem
      refine ⟨u ∘ e, he, ?_, ?_, ?_⟩
      · intro i
        exact (hmem (e i)).2.trans_le (starts_mono w (by have h := (e i).isLt; omega))
      · intro i j hij hj
        have hlt : i < j := by change (i:ℕ)<(j:ℕ); omega
        have hgap' := hgap i j hlt
        have hlast' := hlast j hj
        have hlow := (hmem (e j)).1
        rw [hlast'] at hlow
        have htpos : 0<t := by omega
        have hb : b = blockStart w (t-1) + w (t-1) := by
          have htEq : t-1+1=t := by omega
          simpa only [htEq] using (starts_step w (t-1))
        dsimp only [Function.comp_apply]
        omega
      · intro i
        exact hpaint (e i)
  obtain ⟨x,hx,hxb,hjoin,hxγ⟩ := hPrefix
  obtain ⟨y,hy,hyBound,hyColor⟩ :=
    append_consecutive hsk x hx hxb hjoin C γ hxγ hTail
  have hyN (i : Fin k) : y i < N := (hyBound i).trans_le (by
    change b+(k-s) ≤ blockStart w B
    rw [hend]
    exact starts_mono w (by omega))
  refine ⟨fun i ↦ ⟨y i, hyN i⟩, hy, γ, fun i ↦ ?_⟩
  have hh := hyColor i
  simpa only [C, dif_pos (hyN i)] using hh

end OMA.Erdos781

namespace OMA.Erdos781

private theorem descending_wave_bounds
    (lower : ∀ k ≥ 2, ∃ c : Fin (k^2-k) → Fin 2,
      ¬ ∃ x : Fin k → Fin (k^2-k), Erdos781.IsDescendingWave (fun i ↦ (x i:ℕ)) ∧
        ∃ γ, ∀ i, c (x i) = γ)
    (k : ℕ) (hk : 1 ≤ k) :
    k^2-k+1 ≤ Erdos781.f k ∧ (Erdos781.f k:ℚ) ≤ ((k:ℚ)^3-4*k+9)/3 := by
  by_cases hk1 : k = 1
  · subst k
    have hu : Erdos781.f 1 ≤ 1 := Nat.sInf_le (s := {n : ℕ | Forces 1 n}) forces_singleton
    have hq : (Erdos781.f 1 : ℚ) ≤ 1 := by exact_mod_cast hu
    constructor
    · simpa using lower_singleton
    · norm_num
      linarith
  have hk2 : 2 ≤ k := by omega
  obtain ⟨B, w, hw, hB, _, hw0, hwlast, hskip, hsum⟩ := OMA.Waves781.exists_block_layout k hk2
  let N := blockStart w B
  have hforce : Forces k N := forces_of_block_layout k B w hB hw hw0 hwlast hskip
  have hu : Erdos781.f k ≤ N := Nat.sInf_le (s := {n : ℕ | Forces k n}) hforce
  have hf : sInf {n : ℕ | Forces k n} ∈ {n : ℕ | Forces k n} := Nat.sInf_mem ⟨N, hforce⟩
  have htotal : (N:ℚ) ≤ ((k:ℚ)^3-4*k+9)/3 := by
    simpa only [N, blockStart, Nat.cast_sum] using hsum
  refine ⟨?_, (Nat.cast_le.mpr hu).trans htotal⟩
  by_contra! hbad
  have hle : Erdos781.f k ≤ k^2-k := by omega
  obtain ⟨c, hc⟩ := lower k hk2
  exact hc (forces_mono hle (show Forces k (Erdos781.f k) from hf) c)

end OMA.Erdos781

theorem OMA.solution : type_of% @Erdos781.erdos_781.variants.brown_erdos_freedman := by
  exact OMA.Erdos781.descending_wave_bounds OMA.DescendingWaves.lower_obstruction
