import OMAStatements.S_arxiv_1803_00823

namespace NJ

open OMA.S_arxiv_1803_00823

def rows : List ℕ := [
  7140, 13224, 7140, 13692, 19776, 13692, 7140, 13224, 7140, 7140, 1368, 7452, 13692, 19776, 11664, 6984, 13224, 7296, 7140, 1056,
  7140, 7140, 11508, 11508, 7140, 7140, 7140, 13728, 19812, 13728, 20280, 26364, 20280, 13728, 19812, 13728, 13728, 14040, 14040, 13416,
  26364, 18252, 13416, 17628, 5124, 13728, 13728, 13728, 13728, 13728, 18096, 13728, 17784, 552, 7140, 13224, 7140, 13692, 19776, 13692,
  7140, 13224, 7140, 7140, 13224, 7296, 276, 19776, 13692, 6828, 11040, 6984, 7140, 7140, 7140, 588, 11196, 7140, 7140, 11196,
  7140, 7476, 1392, 7140, 14028, 14028, 13692, 7308, 13224, 7140, 7476, 1056, 7452, 13692, 7608, 11664, 6984, 6984, 6636, 7140,
  1056, 6636, 7140, 6636, 11004, 7140, 6636, 6636, 11700, 19812, 13728, 18252, 26364, 13356, 13728, 19812, 216, 11700, 7644, 13728,
  13260, 26364, 13188, 6660, 8844, 60, 9336, 7140, 6636, 588, 13224, 11004, 6804, 48, 48, 7308, 13224, 6972, 5100, 17580,
  13356, 6972, 11028, 6804, 6672, 6972, 6972, 108, 8844, 6648, 6660, 8844, 6648, 6972, 6972, 6636, 252, 8832, 6636, 6804,
  8832, 6636, 7140, 1056, 7140, 13692, 13692, 13692, 7140, 7140, 7140, 6672, 1056, 7140, 6672, 7140, 9324, 6672, 6984, 6984,
  7140, 1056, 7140, 7140, 5112, 9324, 7140, 5112, 7140, 11532, 11532, 7140, 18084, 13692, 13692, 7140, 11196, 552, 11064, 6672,
  7140, 11064, 13224, 552, 6672, 8856, 240, 9336, 5112, 7140, 588, 5112, 552, 7140, 552, 552, 7140, 7140, 7140, 588,
  17748, 13692, 7140, 11196, 7140, 6672, 6672, 7140, 120, 120, 6828, 6672, 8856, 6828, 7140, 5112, 7140, 588, 588, 7140,
  7140, 9168, 7140, 7152, 4788, 7128, 13692, 17580, 11496, 7128, 13200, 7116, 7608, 1356, 7440, 7128, 9468, 9468, 7128, 7272,
  7272, 7128, 1032, 7116, 7128, 9300, 9300, 7104, 7104, 7104, 11544, 17628, 13728, 20280, 26364, 20280, 13728, 13200, 528, 11544,
  14196, 7440, 7176, 26364, 9468, 13728, 13188, 684, 9336, 1056, 7116, 7140, 13692, 516, 7104, 11160, 516, 7164, 13248, 7152,
  612, 13248, 13692, 7140, 13224, 7140, 7164, 13224, 7296, 588, 6672, 7296, 6828, 11040, 7104, 7140, 7140, 7140, 588, 7104,
  7104, 7104, 11160, 7104, 7488, 1404, 7644, 7488, 14196, 11496, 7308, 13224, 7116, 8112, 2028, 8112, 7176, 2028, 9468, 7140,
  7608, 6600, 7644, 1032, 6612, 7644, 1020, 8796, 7104, 3048, 6600, 9516, 9516, 7152, 9516, 26364, 7104, 7308, 6636, 552,
  9516, 2028, 7104, 156, 7140, 12, 6636, 12, 12, 9336, 552, 6636, 552, 12, 12, 7104, 12, 12, 7332, 7332,
  7152, 780, 13260, 13692, 7176, 11028, 6804, 6708, 7644, 7140, 156, 156, 6672, 6708, 8844, 6600, 7176, 7176, 6636, 252,
  84, 2268, 6768, 8796, 6600, 7164, 1080, 7152, 7164, 1056, 9324, 7140, 7140, 7140, 6696, 1080, 7608, 6672, 588, 9324,
  6672, 7104, 7104, 7140, 1056, 7140, 2772, 900, 7104, 7104, 3048, 7104, 9360, 9360, 7152, 624, 13728, 7140, 7176, 7176,
  552, 8892, 1092, 7608, 156, 156, 588, 2280, 84, 240, 7176, 888, 2748, 624, 732, 516, 2712, 684, 516, 7176,
  7176, 7176, 624, 11232, 7176, 7176, 11232, 7176, 6708, 3120, 7176, 156, 156, 7176, 6708, 8892, 6864, 7176, 3120, 7176,
  624, 780, 2808, 7176, 9492, 7104, 7140, 1056, 7140, 7140, 17592, 11508, 7140, 13224, 7140, 7608, 1524, 7608, 7608, 1524,
  9636, 7140, 7452, 7452, 7140, 1056, 7140, 4956, 1056, 9324, 7140, 7140, 7140, 11532, 17616, 7140, 11532, 13224, 11508, 7140,
  13224, 552, 12000, 12000, 7608, 7608, 13692, 9636, 7140, 552, 864, 9336, 1056, 7140, 4956, 4956, 552, 7140, 552, 552,
  7140, 13224, 7140, 588, 13224, 7140, 7140, 13224, 7140, 7608, 7608, 7608, 588, 7140, 7296, 7140, 9168, 7296, 7140, 7140,
  7140, 588, 4956, 4956, 7140, 9168, 7140, 7644, 1560, 7644, 7644, 12012, 12012, 7644, 7644, 7644, 8112, 2028, 8112, 3276,
  2028, 10140, 7644, 7644, 7956, 7644, 1560, 7644, 3276, 1404, 9180, 7644, 3588, 6636, 9672, 1560, 7644, 9672, 13728, 7644,
  7308, 7140, 552, 10140, 2028, 3216, 1092, 2028, 1020, 6672, 1056, 864, 7644, 1560, 2244, 576, 732, 60, 2748, 48,
  48, 7476, 7476, 7140, 924, 588, 7140, 7308, 9168, 7140, 7944, 7608, 7608, 924, 1056, 6636, 6672, 9168, 6636, 7140,
  3084, 6636, 588, 744, 2268, 7140, 6636, 6636, 7140, 1056, 7140, 7140, 1056, 9324, 7140, 7140, 7140, 7608, 1524, 7608,
  2304, 1524, 7608, 6672, 3084, 7140, 7140, 1056, 7140, 2772, 900, 4956, 7140, 3084, 7140, 9336, 1056, 4944, 588, 4944,
  4944, 4944, 4944, 552, 9156, 1356, 3216, 108, 732, 564, 2280, 720, 552, 4944, 888, 2748, 576, 732, 564, 2748,
  720, 552, 7140, 7140, 7140, 588, 588, 7140, 7140, 9168, 7140, 6672, 3552, 7608, 120, 120, 2772, 6672, 6672, 7140,
  7140, 3084, 7140, 588, 744, 2772, 7140, 5112, 7140]

def fL : List (List ℕ) := [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

def gL : List (List ℕ) := [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 3, 1, 2], [0, 2, 3, 1], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2], [2, 0, 1, 3], [3, 0, 1, 2], [2, 0, 3, 1], [3, 0, 2, 1], [1, 2, 0, 3], [1, 3, 0, 2], [2, 1, 0, 3], [3, 1, 0, 2], [2, 3, 0, 1], [3, 2, 0, 1], [1, 2, 3, 0], [1, 3, 2, 0], [2, 1, 3, 0], [3, 1, 2, 0], [2, 3, 1, 0], [3, 2, 1, 0]]

/-- Twelve times the probability of player `p` in row `s` of the lottery table. -/
def tabN (s p : ℕ) : ℕ := (rows.getD s 0 / 13 ^ p) % 13

/-- Digit `k` of the state `s`: the number of wins of the smaller player of pair `k` (0, 1 or 2). -/
def dig (k s : ℕ) : ℕ := (s / 3 ^ k) % 3

/-- The state after the smaller player of pair `m` wins one more match. -/
def upd (s m : ℕ) : ℕ := if dig m s < 2 then s + 3 ^ m else s

def loN (k : ℕ) : ℕ := [0, 0, 0, 1, 1, 2].getD k 0

def hiN (k : ℕ) : ℕ := [1, 2, 3, 2, 3, 3].getD k 3

/-- The smaller player of pair `k`. -/
def lo (k : ℕ) : Fin 4 := ⟨loN k % 4, Nat.mod_lt _ (by decide)⟩

/-- The larger player of pair `k`. -/
def hi (k : ℕ) : Fin 4 := ⟨hiN k % 4, Nat.mod_lt _ (by decide)⟩

/-- `s'` is `s`, or `s` with digit `k` raised by one. -/
def S (k s s' : ℕ) : Prop := s' = s ∨ (dig k s < 2 ∧ s' = s + 3 ^ k)

theorem F_sum : ∀ s < 729, ∑ t : Fin 4, tabN s t = 12 := by decide +kernel

theorem F_upd : ∀ s < 729, ∀ m < 6, upd s m < 729 := by decide +kernel

theorem F_mono : ∀ s < 729, ∀ k < 6, dig k s < 2 →
    tabN s (loN k % 4) ≤ tabN (s + 3 ^ k) (loN k % 4) ∧
      tabN (s + 3 ^ k) (hiN k % 4) ≤ tabN s (hiN k % 4) := by decide +kernel

theorem F_S : ∀ s < 729, ∀ k < 6, ∀ m < 6, dig k s < 2 →
    (upd (s + 3 ^ k) m = upd s m ∨
      (dig k (upd s m) < 2 ∧ upd (s + 3 ^ k) m = upd s m + 3 ^ k)) := by decide +kernel

theorem lo_ne_hi : ∀ m < 6, lo m ≠ hi m := by decide

/-- The lottery: player `t` wins with probability `tabN s t / 12`. -/
noncomputable def leaf (s : ℕ) : Tournament 4 :=
  .chance 4 (fun t => (tabN s t : ℝ) / 12) (fun t => .declare t)

/-- Play the pairs of the list `l` in order, starting from state `s`, then run the lottery. -/
noncomputable def rr : List ℕ → ℕ → Tournament 4
  | [], s => leaf s
  | m :: l, s => .play (lo m) (hi m) (rr l (upd s m)) (rr l s)

theorem leaf_wp (P : Matrix (Fin 4) (Fin 4) ℝ) (s : ℕ) (p : Fin 4) :
    (leaf s).winProb P p = (tabN s p : ℝ) / 12 := by
  simp [leaf, Tournament.winProb]

theorem mono (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : P ∈ matchMatrices 4) :
    ∀ l : List ℕ, (∀ m ∈ l, m < 6) → ∀ k, k < 6 → ∀ s s', s < 729 → S k s s' →
      (rr l s).winProb P (lo k) ≤ (rr l s').winProb P (lo k) ∧
        (rr l s').winProb P (hi k) ≤ (rr l s).winProb P (hi k) := by
  intro l
  induction l with
  | nil =>
    intro _ k hk s s' hs hS
    rcases hS with rfl | ⟨hd, rfl⟩
    · exact ⟨le_rfl, le_rfl⟩
    · obtain ⟨h1, h2⟩ := F_mono s hs k hk hd
      have h1' : (tabN s (lo k) : ℝ) ≤ (tabN (s + 3 ^ k) (lo k) : ℝ) := by exact_mod_cast h1
      have h2' : (tabN (s + 3 ^ k) (hi k) : ℝ) ≤ (tabN s (hi k) : ℝ) := by exact_mod_cast h2
      simp only [rr, leaf_wp]
      constructor <;> linarith
  | cons m l ih =>
    intro hl k hk s s' hs hS
    have hm : m < 6 := hl m (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x < 6 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hS' : S k (upd s m) (upd s' m) := by
      rcases hS with rfl | ⟨hd, rfl⟩
      · exact Or.inl rfl
      · exact F_S s hs k hk m hm hd
    obtain ⟨a1, a2⟩ := ih hl' k hk (upd s m) (upd s' m) (F_upd s hs m hm) hS'
    obtain ⟨b1, b2⟩ := ih hl' k hk s s' hs hS
    have h0 := (hP.1 (lo m) (hi m)).1
    have h0' := (hP.1 (hi m) (lo m)).1
    simp only [rr, Tournament.winProb]
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left a1 h0) (mul_le_mul_of_nonneg_left b1 h0'),
      add_le_add (mul_le_mul_of_nonneg_left a2 h0) (mul_le_mul_of_nonneg_left b2 h0')⟩

theorem honest_rr : ∀ l : List ℕ, (∀ m ∈ l, m < 6) → ∀ s, s < 729 → (rr l s).Honest := by
  intro l
  induction l with
  | nil =>
    intro _ s _
    simp [rr, leaf, Tournament.Honest]
  | cons m l ih =>
    intro hl s hs
    have hm : m < 6 := hl m (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x < 6 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hS : S m s (upd s m) := by
      unfold upd
      split_ifs with h
      · exact Or.inr ⟨h, rfl⟩
      · exact Or.inl rfl
    simp only [rr, Tournament.Honest]
    exact ⟨fun P hP => mono P hP l hl' m hm s (upd s m) hs hS,
      ih hl' _ (F_upd s hs m hm), ih hl' s hs⟩

theorem wf_rr : ∀ l : List ℕ, (∀ m ∈ l, m < 6) → ∀ s, s < 729 → (rr l s).WellFormed := by
  intro l
  induction l with
  | nil =>
    intro _ s hs
    simp only [rr, leaf, Tournament.WellFormed]
    refine ⟨fun t => by positivity, ?_, fun t => trivial⟩
    rw [← Finset.sum_div, ← Nat.cast_sum, F_sum s hs]
    norm_num
  | cons m l ih =>
    intro hl s hs
    have hm : m < 6 := hl m (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x < 6 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [rr, Tournament.WellFormed]
    exact ⟨lo_ne_hi m hm, ih hl' _ (F_upd s hs m hm), ih hl' s hs⟩

/-- Rename the players of a tournament. -/
noncomputable def relabel (σ : Equiv.Perm (Fin 4)) : Tournament 4 → Tournament 4
  | .declare w => .declare (σ w)
  | .chance k wt next => .chance k wt (fun t => relabel σ (next t))
  | .play i j a b => .play (σ i) (σ j) (relabel σ a) (relabel σ b)

theorem relabel_wp (σ : Equiv.Perm (Fin 4)) (P : Matrix (Fin 4) (Fin 4) ℝ) (T : Tournament 4)
    (k : Fin 4) :
    (relabel σ T).winProb (P.submatrix σ.symm σ.symm) (σ k) = T.winProb P k := by
  induction T with
  | declare w => simp [relabel, Tournament.winProb]
  | chance n wt next ih =>
    simp only [relabel, Tournament.winProb]
    exact Finset.sum_congr rfl (fun t _ => by rw [ih t])
  | play i j a b iha ihb =>
    simp only [relabel, Tournament.winProb, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rw [iha, ihb]

theorem relabel_mul (σ τ : Equiv.Perm (Fin 4)) (T : Tournament 4) :
    relabel (σ * τ) T = relabel σ (relabel τ T) := by
  induction T with
  | declare w => simp [relabel]
  | chance n wt next ih =>
    simp only [relabel]
    congr 1
    funext t
    exact ih t
  | play i j a b iha ihb => simp [relabel, iha, ihb]

theorem wf_relabel (σ : Equiv.Perm (Fin 4)) (T : Tournament 4) (h : T.WellFormed) :
    (relabel σ T).WellFormed := by
  induction T with
  | declare w => simp [relabel, Tournament.WellFormed]
  | chance n wt next ih =>
    simp only [relabel, Tournament.WellFormed] at h ⊢
    exact ⟨h.1, h.2.1, fun t => ih t (h.2.2 t)⟩
  | play i j a b iha ihb =>
    simp only [relabel, Tournament.WellFormed] at h ⊢
    exact ⟨fun e => h.1 (σ.injective e), iha h.2.1, ihb h.2.2⟩

theorem honest_relabel (σ : Equiv.Perm (Fin 4)) (T : Tournament 4) (h : T.Honest) :
    (relabel σ T).Honest := by
  induction T with
  | declare w => simp [relabel, Tournament.Honest]
  | chance n wt next ih =>
    simp only [relabel, Tournament.Honest] at h ⊢
    exact fun t ht => ih t (h t ht)
  | play i j a b iha ihb =>
    simp only [relabel, Tournament.Honest] at h ⊢
    refine ⟨fun P hP => ?_, iha h.2.1, ihb h.2.2⟩
    have hQ : P.submatrix σ σ ∈ matchMatrices 4 :=
      ⟨fun x y => hP.1 _ _, fun x y => hP.2 _ _⟩
    have e : P = (P.submatrix σ σ).submatrix σ.symm σ.symm := by
      ext x y
      simp
    rw [e, relabel_wp, relabel_wp, relabel_wp, relabel_wp]
    exact h.1 _ hQ

def fN (t x : ℕ) : ℕ := (fL.getD t []).getD x 0

def gN (t x : ℕ) : ℕ := (gL.getD t []).getD x 0

theorem F_perm : ∀ t < 24, ∀ x < 4,
    fN t x < 4 ∧ gN t x < 4 ∧ gN t (fN t x) = x ∧ fN t (gN t x) = x := by decide +kernel

theorem F_inj : ∀ t < 24, ∀ t' < 24, (∀ x < 4, fN t x = fN t' x) → t = t' := by decide +kernel

/-- The 24 relabellings. -/
def phi (t : Fin 24) : Equiv.Perm (Fin 4) where
  toFun x := ⟨fN t x, (F_perm t t.isLt x x.isLt).1⟩
  invFun x := ⟨gN t x, (F_perm t t.isLt x x.isLt).2.1⟩
  left_inv x := Fin.ext (F_perm t t.isLt x x.isLt).2.2.1
  right_inv x := Fin.ext (F_perm t t.isLt x x.isLt).2.2.2

theorem phi_bij : Function.Bijective phi := by
  refine (Fintype.bijective_iff_injective_and_card phi).2 ⟨?_, ?_⟩
  · intro t t' h
    apply Fin.ext
    apply F_inj t t.isLt t' t'.isLt
    intro x hx
    have h2 := congrArg (fun e : Equiv.Perm (Fin 4) => ((e ⟨x, hx⟩ : Fin 4) : ℕ)) h
    exact h2
  · simp [Fintype.card_perm, Nat.factorial]

def sched : List ℕ := [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5]

theorem sched_lt : ∀ m ∈ sched, m < 6 := by decide

/-- The double round robin with the lottery. -/
noncomputable def T0 : Tournament 4 := rr sched 0

/-- The double round robin played after a uniformly random relabelling of the players. -/
noncomputable def T1 : Tournament 4 :=
  .chance 24 (fun _ => 1 / 24) (fun t => relabel (phi t) T0)

theorem wf_T1 : T1.WellFormed := by
  simp only [T1, Tournament.WellFormed]
  refine ⟨fun _ => by norm_num, by simp, fun t => ?_⟩
  exact wf_relabel _ _ (wf_rr sched sched_lt 0 (by norm_num))

theorem honest_T1 : T1.Honest := by
  simp only [T1, Tournament.Honest]
  exact fun t _ => honest_relabel _ _ (honest_rr sched sched_lt 0 (by norm_num))

theorem sym_T1 : T1.Symmetric := by
  intro P _ σ i
  have h1 : ∀ F : Equiv.Perm (Fin 4) → ℝ, ∑ t, F (phi t) = ∑ τ, F τ :=
    fun F => Equiv.sum_comp (Equiv.ofBijective phi phi_bij) F
  have h3 : ∀ F : Equiv.Perm (Fin 4) → ℝ, ∑ τ, F (σ * τ) = ∑ τ, F τ :=
    fun F => Equiv.sum_comp (Equiv.mulLeft σ) F
  have h4 : ∀ τ : Equiv.Perm (Fin 4),
      (relabel (σ * τ) T0).winProb (P.submatrix σ.symm σ.symm) (σ i) =
        (relabel τ T0).winProb P i := by
    intro τ
    rw [relabel_mul]
    exact relabel_wp σ P (relabel τ T0) i
  simp only [T1, Tournament.winProb]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rw [h1 (fun τ => (relabel τ T0).winProb P i),
    h1 (fun τ => (relabel τ T0).winProb (P.submatrix σ.symm σ.symm) (σ i)),
    ← h3 (fun τ => (relabel τ T0).winProb (P.submatrix σ.symm σ.symm) (σ i))]
  exact Finset.sum_congr rfl (fun τ _ => (h4 τ).symm)

/-- Twice the entries of the matrix `P0`. -/
def p0N (i j : ℕ) : ℕ := ([[1, 1, 2, 2], [1, 1, 2, 2], [0, 0, 1, 1], [0, 0, 1, 1]].getD i []).getD j 0

/-- Two equal strong players (0 and 1) who always beat two equal weak players (2 and 3). -/
noncomputable def P0 : Matrix (Fin 4) (Fin 4) ℝ := fun i j => (p0N i j : ℝ) / 2

theorem F_p0 : ∀ i < 4, ∀ j < 4, p0N i j ≤ 2 ∧ p0N i j + p0N j i = 2 ∧
    (∀ i' < 4, i ≤ i' → p0N i' j ≤ p0N i j) ∧ (∀ j' < 4, j ≤ j' → p0N i j ≤ p0N i j') := by
  decide

theorem P0_mem : P0 ∈ doublyMonotonic 4 := by
  refine ⟨⟨fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩, fun i i' j hi => ?_, fun i j j' hj => ?_⟩
  · show (0 : ℝ) ≤ (p0N i j : ℝ) / 2
    positivity
  · have h : (p0N i j : ℝ) ≤ 2 := by exact_mod_cast (F_p0 i i.isLt j j.isLt).1
    show (p0N i j : ℝ) / 2 ≤ 1
    linarith
  · have h : ((p0N i j : ℝ)) + (p0N j i : ℝ) = 2 := by
      exact_mod_cast (F_p0 i i.isLt j j.isLt).2.1
    show (p0N i j : ℝ) / 2 + (p0N j i : ℝ) / 2 = 1
    linarith
  · have h : (p0N i' j : ℝ) ≤ (p0N i j : ℝ) := by
      exact_mod_cast (F_p0 i i.isLt j j.isLt).2.2.1 i' i'.isLt hi
    show (p0N i' j : ℝ) / 2 ≤ (p0N i j : ℝ) / 2
    linarith
  · have h : (p0N i j : ℝ) ≤ (p0N i j' : ℝ) := by
      exact_mod_cast (F_p0 i i.isLt j j.isLt).2.2.2 j' j'.isLt hj
    show (p0N i j : ℝ) / 2 ≤ (p0N i j' : ℝ) / 2
    linarith

/-- Exact evaluation of `rr` when the matrix has entries `wA m / 2` and `wB m / 2` on pair `m`. -/
def evalN (wA wB : ℕ → ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], s, p => tabN s p
  | m :: l, s, p =>
    if wB m = 0 then wA m * evalN wA wB l (upd s m) p
    else if wA m = 0 then wB m * evalN wA wB l s p
    else wA m * evalN wA wB l (upd s m) p + wB m * evalN wA wB l s p

theorem eval_rr (P : Matrix (Fin 4) (Fin 4) ℝ) (wA wB : ℕ → ℕ)
    (hA : ∀ m < 6, P (lo m) (hi m) = (wA m : ℝ) / 2)
    (hB : ∀ m < 6, P (hi m) (lo m) = (wB m : ℝ) / 2) :
    ∀ l : List ℕ, (∀ m ∈ l, m < 6) → ∀ (s : ℕ) (p : Fin 4),
      (rr l s).winProb P p = (evalN wA wB l s p : ℝ) / (2 ^ l.length * 12) := by
  intro l
  induction l with
  | nil =>
    intro _ s p
    simp [rr, leaf_wp, evalN]
  | cons m l ih =>
    intro hl s p
    have hm : m < 6 := hl m (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x < 6 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [rr, Tournament.winProb, evalN, List.length_cons]
    rw [ih hl' (upd s m) p, ih hl' s p, hA m hm, hB m hm]
    split_ifs with h1 h2
    · rw [h1]
      push_cast
      ring
    · rw [h2]
      push_cast
      ring
    · push_cast
      ring

/-- The numerator of the win probability of player 0 in the branch with relabelling `t`. -/
def E (t : ℕ) : ℕ :=
  evalN (fun m => p0N (fN t (loN m % 4)) (fN t (hiN m % 4)))
    (fun m => p0N (fN t (hiN m % 4)) (fN t (loN m % 4))) sched 0 (gN t 0)

theorem F_E : ∀ t < 24, E t = 11264 := by decide +kernel

theorem branch_val (t : Fin 24) : (relabel (phi t) T0).winProb P0 0 = 11 / 48 := by
  have e : (P0.submatrix (phi t) (phi t)).submatrix (phi t).symm (phi t).symm = P0 := by
    ext x y
    simp
  have h := relabel_wp (phi t) (P0.submatrix (phi t) (phi t)) T0 ((phi t).symm 0)
  rw [e, Equiv.apply_symm_apply] at h
  rw [h]
  have h2 := eval_rr (P0.submatrix (phi t) (phi t))
    (fun m => p0N (fN t (loN m % 4)) (fN t (hiN m % 4)))
    (fun m => p0N (fN t (hiN m % 4)) (fN t (loN m % 4)))
    (fun m _ => rfl) (fun m _ => rfl) sched sched_lt 0 ((phi t).symm 0)
  have h3 : evalN (fun m => p0N (fN t (loN m % 4)) (fN t (hiN m % 4)))
      (fun m => p0N (fN t (hiN m % 4)) (fN t (loN m % 4))) sched 0 ((phi t).symm 0 : Fin 4) =
        11264 := F_E t t.isLt
  show (rr sched 0).winProb (P0.submatrix (phi t) (phi t)) ((phi t).symm 0) = 11 / 48
  rw [h2, h3]
  norm_num [sched]

theorem x1_val : T1.winProb P0 0 = 11 / 48 := by
  simp only [T1, Tournament.winProb, branch_val]
  simp

theorem star_bound (v : Fin 4 → ℝ) (hv : v ∈ setAStar 4) : (1 : ℝ) / 4 ≤ v 0 := by
  have hsub : starPoints 4 ⊆ {w : Fin 4 → ℝ | (1 : ℝ) / 4 ≤ w 0} := by
    rintro w ⟨a, b, hab, hw⟩
    have ha : a 0 = 0 := le_antisymm (hab 0).1 (Fin.zero_le _)
    have hb : b 0 = 0 := le_antisymm (hab 0).2.1 (Fin.zero_le _)
    have h1 : 1 ≤ (Finset.univ.filter fun k => a k = 0).card :=
      Finset.card_pos.2 ⟨0, by simp [ha]⟩
    have h2 : 1 ≤ (Finset.univ.filter fun k => b k = 0).card :=
      Finset.card_pos.2 ⟨0, by simp [hb]⟩
    have h1' : (1 : ℝ) ≤ ((Finset.univ.filter fun k => a k = 0).card : ℝ) := by exact_mod_cast h1
    have h2' : (1 : ℝ) ≤ ((Finset.univ.filter fun k => b k = 0).card : ℝ) := by exact_mod_cast h2
    show (1 : ℝ) / 4 ≤ w 0
    rw [hw 0]
    have h8 : (2 : ℝ) * ((4 : ℕ) : ℝ) = 8 := by norm_num
    rw [h8]
    linarith
  have hconv : Convex ℝ {w : Fin 4 → ℝ | (1 : ℝ) / 4 ≤ w 0} := by
    intro x hx y hy a b ha hb hab
    have hx' : (1 : ℝ) / 4 ≤ x 0 := hx
    have hy' : (1 : ℝ) / 4 ≤ y 0 := hy
    show (1 : ℝ) / 4 ≤ a * x 0 + b * y 0
    nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]
  exact convexHull_min hsub hconv hv

end NJ

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_1803_00823.main) := by
  intro h
  have h4 := h 4 (by norm_num)
  have hx : NJ.T1.winProb NJ.P0 ∈ OMA.S_arxiv_1803_00823.setA 4 :=
    subset_closure ⟨NJ.T1, NJ.wf_T1, NJ.sym_T1, NJ.honest_T1, NJ.P0, NJ.P0_mem, rfl⟩
  rw [← h4] at hx
  have h5 := NJ.star_bound _ hx
  rw [NJ.x1_val] at h5
  norm_num at h5
