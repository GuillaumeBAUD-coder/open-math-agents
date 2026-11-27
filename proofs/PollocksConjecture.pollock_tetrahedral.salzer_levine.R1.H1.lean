import OMAReductions.R_PollocksConjecture_pollock_tetrahedral_salzer_levine_R1

-- Step PollocksConjecture.pollock_tetrahedral.salzer_levine.R1.H1: hypothesis H1 of reduction PollocksConjecture.pollock_tetrahedral.salzer_levine.R1
-- Credit: @Jeffreyyvdb
-- H1 := (343867 : ℕ) ∈ PollocksConjecture.NotSumOfFourTetrahedral

/-
Salzer and Levine: 343867 is not a sum of four tetrahedral numbers.

Each summand is at most T(126) = 341376, because T is monotone and T(127) = 349504 > 343867.
That leaves a finite check, done by meeting in the middle: `mask` has bit s set exactly when
s = T(a) + T(b) for some a, b <= 126, and `check` says that for every such two-sum s <= 343867
the bit 343867 - s of `mask` is clear. The kernel evaluates `check`.
-/

namespace OMA.PollockSalzerLevine

open PollocksConjecture

lemma tetrahedral_mono {a b : ℕ} (h : a ≤ b) : tetrahedral a ≤ tetrahedral b := by
  unfold tetrahedral
  exact Nat.div_le_div_right (Nat.mul_le_mul (Nat.mul_le_mul h (by omega)) (by omega))

lemma tetrahedral_127 : tetrahedral 127 = 349504 := by
  unfold tetrahedral
  norm_num

lemma le_126 {x : ℕ} (h : tetrahedral x ≤ 343867) : x ≤ 126 := by
  by_contra hx
  have h127 : 127 ≤ x := by omega
  have hmono := tetrahedral_mono h127
  rw [tetrahedral_127] at hmono
  omega

/-- The tetrahedral numbers T(0), ..., T(126). -/
def tets : List ℕ := (List.range 127).map tetrahedral

lemma mem_tets {x : ℕ} (h : x ≤ 126) : tetrahedral x ∈ tets :=
  List.mem_map.mpr ⟨x, List.mem_range.mpr (by omega), rfl⟩

/-- Bit `x + y` is set for every `y` in `tets`. -/
def rowMask (x : ℕ) : ℕ := (tets.map fun y => 2 ^ (x + y)).foldr Nat.lor 0

/-- Bit `s` is set when `s` is a sum of two of the numbers in `tets`. -/
def mask : ℕ := (tets.map rowMask).foldr Nat.lor 0

def rowOk (x : ℕ) : Bool :=
  tets.all fun y => decide (343867 < x + y) || !(mask.testBit (343867 - (x + y)))

def check : Bool := tets.all rowOk

lemma foldr_lor_testBit (ws : List ℕ) (i : ℕ) :
    (ws.foldr Nat.lor 0).testBit i = true ↔ ∃ w ∈ ws, w.testBit i = true := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    change (w ||| ws.foldr Nat.lor 0).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨v, hv, hbit⟩)
      · exact ⟨w, List.mem_cons_self, h⟩
      · exact ⟨v, List.mem_cons_of_mem _ hv, hbit⟩
    · rintro ⟨v, hv, hbit⟩
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact Or.inl hbit
      · exact Or.inr ⟨v, hmem, hbit⟩

lemma mask_testBit {c d : ℕ} (hc : c ≤ 126) (hd : d ≤ 126) :
    mask.testBit (tetrahedral c + tetrahedral d) = true := by
  unfold mask
  rw [foldr_lor_testBit]
  refine ⟨rowMask (tetrahedral c), List.mem_map.mpr ⟨tetrahedral c, mem_tets hc, rfl⟩, ?_⟩
  unfold rowMask
  rw [foldr_lor_testBit]
  exact ⟨2 ^ (tetrahedral c + tetrahedral d),
    List.mem_map.mpr ⟨tetrahedral d, mem_tets hd, rfl⟩, Nat.testBit_two_pow_self⟩

set_option maxRecDepth 100000 in
lemma check_true : check = true := by decide +kernel

lemma no_rep (a b c d : ℕ) :
    tetrahedral a + tetrahedral b + tetrahedral c + tetrahedral d ≠ 343867 := by
  intro h
  have ha : a ≤ 126 := le_126 (by omega)
  have hb : b ≤ 126 := le_126 (by omega)
  have hc : c ≤ 126 := le_126 (by omega)
  have hd : d ≤ 126 := le_126 (by omega)
  have h1 : tets.all rowOk = true := check_true
  rw [List.all_eq_true] at h1
  have h2 : rowOk (tetrahedral a) = true := h1 _ (mem_tets ha)
  unfold rowOk at h2
  rw [List.all_eq_true] at h2
  have h3 := h2 _ (mem_tets hb)
  have e : 343867 - (tetrahedral a + tetrahedral b) = tetrahedral c + tetrahedral d := by omega
  have hbit := mask_testBit hc hd
  simp only [e, hbit, Bool.not_true, Bool.or_false, decide_eq_true_eq] at h3
  omega

end OMA.PollockSalzerLevine

theorem OMA.solution : OMA.R_PollocksConjecture_pollock_tetrahedral_salzer_levine_R1.H1 := by
  change ∀ f : Fin 4 → ℕ, (343867 : ℕ) ≠ ∑ i, PollocksConjecture.tetrahedral (f i)
  intro f h
  rw [Fin.sum_univ_four] at h
  exact OMA.PollockSalzerLevine.no_rep (f 0) (f 1) (f 2) (f 3) h.symm
