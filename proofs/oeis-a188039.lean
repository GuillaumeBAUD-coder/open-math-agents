import OMAStatements.S_oeis_a188039

namespace OMA.S_oeis_a188039

/-! ### sqrt 2 -/

lemma r_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma r_pos : 0 < Real.sqrt 2 := by positivity

lemma one_lt_r : 1 < Real.sqrt 2 := by nlinarith [r_sq, r_pos]

lemma r_lt : Real.sqrt 2 < 3 / 2 := by nlinarith [r_sq, r_pos]

lemma unit : (3 + 2 * Real.sqrt 2) * (3 - 2 * Real.sqrt 2) = 1 := by nlinarith [r_sq]

lemma floor_two_r : ⌊2 * Real.sqrt 2⌋ = 2 := by
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> nlinarith [one_lt_r, r_lt]

/-! ### The zeros of A188038 -/

lemma s_one : s 1 = 1 := by
  unfold s
  have h1 : ⌊((1 : ℕ) : ℝ) * Real.sqrt 2⌋ = 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith [one_lt_r, r_lt]
  have h2 : ⌊((1 : ℕ) : ℝ) * Real.sqrt 2 - 2 * Real.sqrt 2⌋ = -2 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith [one_lt_r, r_lt]
  rw [h1, h2, floor_two_r]
  norm_num

lemma s_add_two (m : ℕ) :
    s (m + 2) = 0 ↔ Int.fract ((m : ℝ) * Real.sqrt 2) < 3 - 2 * Real.sqrt 2 := by
  unfold s
  have hf0 := Int.fract_nonneg ((m : ℝ) * Real.sqrt 2)
  have hf1 := Int.fract_lt_one ((m : ℝ) * Real.sqrt 2)
  have e1 : ((m + 2 : ℕ) : ℝ) * Real.sqrt 2 - 2 * Real.sqrt 2 = (m : ℝ) * Real.sqrt 2 := by
    push_cast
    ring
  have e2 : ((m + 2 : ℕ) : ℝ) * Real.sqrt 2 = (⌊(m : ℝ) * Real.sqrt 2⌋ : ℝ) +
      (Int.fract ((m : ℝ) * Real.sqrt 2) + 2 * Real.sqrt 2) := by
    rw [← add_assoc, Int.floor_add_fract]
    push_cast
    ring
  rw [e1, e2, Int.floor_intCast_add, floor_two_r]
  rcases lt_or_ge (Int.fract ((m : ℝ) * Real.sqrt 2)) (3 - 2 * Real.sqrt 2) with h | h
  · have h2 : ⌊Int.fract ((m : ℝ) * Real.sqrt 2) + 2 * Real.sqrt 2⌋ = 2 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> nlinarith [one_lt_r]
    rw [h2]
    exact ⟨fun _ => h, fun _ => by ring⟩
  · have h3 : ⌊Int.fract ((m : ℝ) * Real.sqrt 2) + 2 * Real.sqrt 2⌋ = 3 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> nlinarith [r_lt]
    rw [h3]
    exact ⟨fun h' => by omega, fun h' => absurd h' (not_lt.mpr h)⟩

/-! ### The set {m : frac(m sqrt 2) < 3 - 2 sqrt 2} -/

/-- g(k) = 3k + 2 floor(k sqrt 2); the zeros of A188038 are the g(k) + 2. -/
noncomputable def g (k : ℕ) : ℕ := 3 * k + 2 * ⌊(k : ℝ) * Real.sqrt 2⌋₊

lemma fract_g (k : ℕ) : Int.fract ((g k : ℝ) * Real.sqrt 2) < 3 - 2 * Real.sqrt 2 := by
  have hp0 : (⌊(k : ℝ) * Real.sqrt 2⌋₊ : ℝ) ≤ k * Real.sqrt 2 := Nat.floor_le (by positivity)
  have hp1 : (k : ℝ) * Real.sqrt 2 < ⌊(k : ℝ) * Real.sqrt 2⌋₊ + 1 := Nat.lt_floor_add_one _
  have hε : 0 < 3 - 2 * Real.sqrt 2 := by linarith [r_lt]
  have hfr : Int.fract ((g k : ℝ) * Real.sqrt 2) =
      (3 - 2 * Real.sqrt 2) * ((k : ℝ) * Real.sqrt 2 - ⌊(k : ℝ) * Real.sqrt 2⌋₊) := by
    rw [Int.fract_eq_iff]
    refine ⟨mul_nonneg hε.le (by linarith), ?_, 4 * k + 3 * ⌊(k : ℝ) * Real.sqrt 2⌋₊, ?_⟩
    · nlinarith [one_lt_r]
    · unfold g
      push_cast
      linear_combination (2 * (k : ℝ)) * r_sq
  rw [hfr]
  exact mul_lt_of_lt_one_right hε (by linarith)

lemma exists_g (m : ℕ) (h : Int.fract ((m : ℝ) * Real.sqrt 2) < 3 - 2 * Real.sqrt 2) :
    ∃ k, g k = m := by
  have hγ0 := Int.fract_nonneg ((m : ℝ) * Real.sqrt 2)
  have hdef : (m : ℝ) * Real.sqrt 2 =
      (⌊(m : ℝ) * Real.sqrt 2⌋ : ℝ) + Int.fract ((m : ℝ) * Real.sqrt 2) :=
    (Int.floor_add_fract _).symm
  have hq0 : (⌊(m : ℝ) * Real.sqrt 2⌋ : ℝ) ≤ m * Real.sqrt 2 := Int.floor_le _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- (3m - 2q) r - (3q - 4m) = (3 + 2r) frac(m r), which lies in [0, 1)
  have key : (3 * (m : ℝ) - 2 * ⌊(m : ℝ) * Real.sqrt 2⌋) * Real.sqrt 2 -
      (3 * ⌊(m : ℝ) * Real.sqrt 2⌋ - 4 * (m : ℝ)) =
      (3 + 2 * Real.sqrt 2) * Int.fract ((m : ℝ) * Real.sqrt 2) := by
    rw [show Int.fract ((m : ℝ) * Real.sqrt 2) =
      (m : ℝ) * Real.sqrt 2 - ⌊(m : ℝ) * Real.sqrt 2⌋ by linarith]
    linear_combination (-2 * (m : ℝ)) * r_sq
  have hlt : (3 + 2 * Real.sqrt 2) * Int.fract ((m : ℝ) * Real.sqrt 2) < 1 := by
    have := mul_lt_mul_of_pos_left h (by linarith [r_pos] : (0 : ℝ) < 3 + 2 * Real.sqrt 2)
    linarith [unit]
  have hge : 0 ≤ (3 + 2 * Real.sqrt 2) * Int.fract ((m : ℝ) * Real.sqrt 2) :=
    mul_nonneg (by linarith [r_pos]) hγ0
  have hK : 0 ≤ 3 * (m : ℤ) - 2 * ⌊(m : ℝ) * Real.sqrt 2⌋ := by
    have : (2 * ⌊(m : ℝ) * Real.sqrt 2⌋ : ℝ) ≤ 3 * m := by nlinarith [r_lt]
    have h' : 2 * ⌊(m : ℝ) * Real.sqrt 2⌋ ≤ 3 * (m : ℤ) := by exact_mod_cast this
    omega
  have hP : 0 ≤ 3 * ⌊(m : ℝ) * Real.sqrt 2⌋ - 4 * (m : ℤ) := by
    have hKr : (0 : ℝ) ≤ (3 * (m : ℝ) - 2 * ⌊(m : ℝ) * Real.sqrt 2⌋) * Real.sqrt 2 := by
      have : (0 : ℝ) ≤ 3 * (m : ℝ) - 2 * ⌊(m : ℝ) * Real.sqrt 2⌋ := by exact_mod_cast hK
      exact mul_nonneg this r_pos.le
    have : (-1 : ℝ) < 3 * ⌊(m : ℝ) * Real.sqrt 2⌋ - 4 * (m : ℝ) := by linarith
    have h' : (-1 : ℤ) < 3 * ⌊(m : ℝ) * Real.sqrt 2⌋ - 4 * (m : ℤ) := by exact_mod_cast this
    omega
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hK
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le hP
  have hk' : (k : ℝ) = 3 * (m : ℝ) - 2 * ⌊(m : ℝ) * Real.sqrt 2⌋ := by
    have : ((k : ℤ) : ℝ) = ((3 * (m : ℤ) - 2 * ⌊(m : ℝ) * Real.sqrt 2⌋ : ℤ) : ℝ) := by rw [hk]
    push_cast at this
    exact this
  have hp' : (p : ℝ) = 3 * ⌊(m : ℝ) * Real.sqrt 2⌋ - 4 * (m : ℝ) := by
    have : ((p : ℤ) : ℝ) = ((3 * ⌊(m : ℝ) * Real.sqrt 2⌋ - 4 * (m : ℤ) : ℤ) : ℝ) := by rw [hp]
    push_cast at this
    exact this
  have hfl : ⌊(k : ℝ) * Real.sqrt 2⌋₊ = p := by
    rw [Nat.floor_eq_iff (by positivity), hk', hp']
    constructor <;> linarith
  refine ⟨k, ?_⟩
  unfold g
  rw [hfl]
  omega

lemma g_strictMono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold g
  have : ⌊(k : ℝ) * Real.sqrt 2⌋₊ ≤ ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt 2⌋₊ :=
    Nat.floor_le_floor (by push_cast; nlinarith [r_pos])
  omega

lemma zero_iff (n : ℕ) : (1 ≤ n ∧ s n = 0) ↔ ∃ k, g k + 2 = n := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
      rcases n with _ | _ | m
      · omega
      · rw [s_one] at h2
        norm_num at h2
      · exact ⟨m, rfl⟩
    obtain ⟨k, hk⟩ := exists_g m ((s_add_two m).mp h2)
    exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨by omega, (s_add_two (g k)).mpr (fract_g k)⟩

theorem nth_zero_eq (n : ℕ) : Nat.nth (fun n => 1 ≤ n ∧ s n = 0) n = g n + 2 := by
  have hmono : StrictMono (fun k => g k + 2) := fun i j hij => by
    have := g_strictMono hij
    show g i + 2 < g j + 2
    omega
  have hinf : (Set.ofPred (fun n => 1 ≤ n ∧ s n = 0)).Infinite :=
    Set.infinite_of_injective_forall_mem hmono.injective
      (fun k => show 1 ≤ g k + 2 ∧ s (g k + 2) = 0 from (zero_iff _).mpr ⟨k, rfl⟩)
  have h := Nat.nth_comp_of_strictMono (p := fun n => 1 ≤ n ∧ s n = 0) (n := n) hmono
    (fun k hk => by
      obtain ⟨j, hj⟩ := (zero_iff k).mp hk
      exact ⟨j, hj⟩)
    (fun hfi => absurd hfi hinf)
  have htrue : (fun i => 1 ≤ g i + 2 ∧ s (g i + 2) = 0) = fun _ => True := by
    funext i
    exact propext ⟨fun _ => trivial, fun _ => (zero_iff _).mpr ⟨i, rfl⟩⟩
  simp only [htrue, Nat.nth_true] at h
  exact h.symm

theorem conjecture : ∀ n : ℕ, 1 ≤ n → a (1 + n) = f n := by
  intro n _
  unfold a f
  rw [show 1 + n - 1 = n by omega, nth_zero_eq]
  unfold g
  ring

end OMA.S_oeis_a188039

theorem OMA.solution : type_of% @OMA.S_oeis_a188039.main :=
  OMA.S_oeis_a188039.conjecture
