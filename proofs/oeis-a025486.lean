import OMAStatements.S_oeis_a025486



namespace A025486Scratch

/-- The least natural square root whose square is at least `k`. -/
def ceilRoot (k : ℕ) : ℕ :=
  if k = 0 then 0 else Nat.sqrt (k - 1) + 1

/-- Distance from `k` to the first square at or above it. -/
def squareComplement (k : ℕ) : ℕ := ceilRoot k ^ 2 - k

theorem complement_lt_twice {u k : ℕ} (hu : 0 < u) (hk : k ≤ u ^ 2) :
    squareComplement k < 2 * u := by
  by_cases hz : k = 0
  · simp [squareComplement, ceilRoot, hz, hu]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hz
    have hr : Nat.sqrt (k - 1) < u := by
      apply (Nat.sqrt_lt').2
      omega
    have hlo : (Nat.sqrt (k - 1)) ^ 2 < k := by
      have h := Nat.sqrt_le' (k - 1)
      omega
    have hbound : (Nat.sqrt (k - 1) + 1) ^ 2 < k + 2 * u := by
      nlinarith
    simp only [squareComplement, ceilRoot, if_neg hz]
    omega

theorem complement_after_square (u : ℕ) :
    squareComplement (u ^ 2 + 1) = 2 * u := by
  have hn : u ^ 2 + 1 ≠ 0 := by omega
  simp only [squareComplement, ceilRoot, if_neg hn, Nat.add_sub_cancel,
    Nat.sqrt_eq']
  simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-- The least input of the next depth, from the exact one-step rule and a minimality
    hypothesis for the previous depth.  No recurrence for the least inputs is assumed. -/
theorem least_depth_successor
    (depth : ℕ → ℕ)
    (hbase : ∀ k, k ≤ 2 → depth k = 0)
    (hstep : ∀ k, 2 < k → depth k = depth (squareComplement k) + 1)
    {u n : ℕ} (hu : 2 ≤ u)
    (hdepth : depth (2 * u) = n)
    (hminimal : ∀ k, k < 2 * u → depth k ≠ n) :
    IsLeast {k : ℕ | depth k = n + 1} (u ^ 2 + 1) := by
  have hu2 : 2 < u ^ 2 + 1 := by nlinarith
  constructor
  · change depth (u ^ 2 + 1) = n + 1
    rw [hstep _ hu2, complement_after_square, hdepth]
  · intro k hk
    change depth k = n + 1 at hk
    by_contra h
    have hkb : k ≤ u ^ 2 := by omega
    by_cases hkbase : k ≤ 2
    · rw [hbase k hkbase] at hk
      omega
    · have hkt : 2 < k := by omega
      rw [hstep k hkt] at hk
      have hfx : squareComplement k < 2 * u := complement_lt_twice (by omega) hkb
      have hne := hminimal (squareComplement k) hfx
      omega

theorem sInf_depth_successor
    (depth : ℕ → ℕ)
    (hbase : ∀ k, k ≤ 2 → depth k = 0)
    (hstep : ∀ k, 2 < k → depth k = depth (squareComplement k) + 1)
    {u n : ℕ} (hu : 2 ≤ u)
    (hdepth : depth (2 * u) = n)
    (hminimal : ∀ k, k < 2 * u → depth k ≠ n) :
    sInf {k : ℕ | depth k = n + 1} = u ^ 2 + 1 := by
  exact (least_depth_successor depth hbase hstep hu hdepth hminimal).csInf_eq

/-- Outside the terminal set, a step of square complementation strictly decreases. -/
theorem complement_lt_self {k : ℕ} (hk : 2 < k) : squareComplement k < k := by
  by_cases hsmall : k < 5
  · interval_cases k <;> norm_num [squareComplement, ceilRoot, Nat.sqrt]
  · have hk5 : 5 ≤ k := by omega
    have hk0 : k ≠ 0 := by omega
    have hr : 2 ≤ Nat.sqrt (k - 1) := (Nat.le_sqrt').2 (by omega)
    have hlo : Nat.sqrt (k - 1) ^ 2 < k := by
      have hh := Nat.sqrt_le' (k - 1)
      omega
    simp only [squareComplement, ceilRoot, if_neg hk0]
    have hbound : (Nat.sqrt (k - 1) + 1) ^ 2 < k + k := by nlinarith
    omega

def Reaches (k : ℕ) : Prop := ∃ n, (squareComplement^[n]) k ≤ 2

theorem reaches_all (k : ℕ) : Reaches k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k ≤ 2
    · exact ⟨0, by simpa using hk⟩
    · have hlt : squareComplement k < k := complement_lt_self (by omega)
      obtain ⟨n, hn⟩ := ih (squareComplement k) hlt
      exact ⟨n + 1, by simpa [Function.iterate_succ_apply] using hn⟩

noncomputable def hit (k : ℕ) : ℕ := sInf {n : ℕ | (squareComplement^[n]) k ≤ 2}

theorem hit_spec (k : ℕ) : (squareComplement^[hit k]) k ≤ 2 :=
  Nat.sInf_mem (reaches_all k)

theorem hit_le {k n : ℕ} (h : (squareComplement^[n]) k ≤ 2) : hit k ≤ n :=
  Nat.sInf_le h

theorem hit_zero {k : ℕ} (h : k ≤ 2) : hit k = 0 := by
  have h' : hit k ≤ 0 := hit_le (n := 0) (by simpa using h)
  omega

theorem hit_step {k : ℕ} (hk : 2 < k) : hit k = hit (squareComplement k) + 1 := by
  have hupper : hit k ≤ hit (squareComplement k) + 1 := by
    apply hit_le
    simpa [Function.iterate_succ_apply] using hit_spec (squareComplement k)
  have hpos : 0 < hit k := by
    by_contra h
    have hzero : hit k = 0 := Nat.eq_zero_of_not_pos h
    have hs := hit_spec k
    simp [hzero] at hs
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hle : hit (squareComplement k) ≤ j := by
    apply hit_le
    have hs := hit_spec k
    simpa [hj, Function.iterate_succ_apply] using hs
  omega

theorem actual_hit_minimal_next {u n : ℕ} (hu : 2 ≤ u)
    (hdepth : hit (2 * u) = n)
    (hminimal : ∀ k, k < 2 * u → hit k ≠ n) :
    IsLeast {k : ℕ | hit k = n + 1} (u ^ 2 + 1) := by
  exact least_depth_successor hit (fun _ h => hit_zero h) (fun _ h => hit_step h)
    hu hdepth hminimal

theorem actual_hit_sInf_next {u n : ℕ} (hu : 2 ≤ u)
    (hdepth : hit (2 * u) = n)
    (hminimal : ∀ k, k < 2 * u → hit k ≠ n) :
    sInf {k : ℕ | hit k = n + 1} = u ^ 2 + 1 :=
  (actual_hit_minimal_next hu hdepth hminimal).csInf_eq

theorem initial_depth_three : IsLeast {k : ℕ | hit k = 3} 10 := by
  have f3 : squareComplement 3 = 1 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have f4 : squareComplement 4 = 0 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have f5 : squareComplement 5 = 4 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have f6 : squareComplement 6 = 3 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have f7 : squareComplement 7 = 2 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have f8 : squareComplement 8 = 1 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have f9 : squareComplement 9 = 0 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have f10 : squareComplement 10 = 6 := by norm_num [squareComplement, ceilRoot, Nat.sqrt]
  have h3 : hit 3 = 1 := by rw [hit_step (k := 3) (by omega), f3, hit_zero (by omega)]
  have h4 : hit 4 = 1 := by rw [hit_step (k := 4) (by omega), f4, hit_zero (by omega)]
  have h5 : hit 5 = 2 := by rw [hit_step (k := 5) (by omega), f5, h4]
  have h6 : hit 6 = 2 := by rw [hit_step (k := 6) (by omega), f6, h3]
  have h7 : hit 7 = 1 := by rw [hit_step (k := 7) (by omega), f7, hit_zero (by omega)]
  have h8 : hit 8 = 1 := by rw [hit_step (k := 8) (by omega), f8, hit_zero (by omega)]
  have h9 : hit 9 = 1 := by rw [hit_step (k := 9) (by omega), f9, hit_zero (by omega)]
  have h10 : hit 10 = 3 := by rw [hit_step (k := 10) (by omega), f10, h6]
  constructor
  · exact h10
  · intro k hk
    by_contra h
    have hlt : k < 10 := by omega
    interval_cases k <;> simp_all [hit_zero]

theorem first_hit_three : sInf {k : ℕ | hit k = 3} = 10 :=
  initial_depth_three.csInf_eq

/-- Parity invariant needed to iterate the least-preimage construction. -/
theorem next_even_invariant {u : ℕ} (hu : 2 ≤ u) (hodd : u % 2 = 1) :
    4 ≤ u ^ 2 + 1 ∧ (u ^ 2 + 1) % 4 = 2 := by
  have hres : u % 4 = 1 ∨ u % 4 = 3 := by omega
  constructor
  · nlinarith
  · rcases hres with h | h <;> simp [Nat.add_mod, Nat.pow_mod, h]

noncomputable def leastHit (n : ℕ) : ℕ := sInf {k : ℕ | hit k = n}

theorem leastHit_invariant (n : ℕ) :
    IsLeast {k : ℕ | hit k = n + 3} (leastHit (n + 3)) ∧
      4 ≤ leastHit (n + 3) ∧ leastHit (n + 3) % 4 = 2 := by
  induction n with
  | zero =>
    have h3 : leastHit 3 = 10 := first_hit_three
    change IsLeast {k : ℕ | hit k = 3} (leastHit 3) ∧
      4 ≤ leastHit 3 ∧ leastHit 3 % 4 = 2
    rw [h3]
    exact ⟨initial_depth_three, by omega, by decide⟩
  | succ n ih =>
    let m := leastHit (n + 3)
    let u := m / 2
    have hm : 2 * u = m := by dsimp [u, m] at *; omega
    have hu : 2 ≤ u := by dsimp [u, m] at *; omega
    have hodd : u % 2 = 1 := by dsimp [u, m] at *; omega
    have hdepth : hit (2 * u) = n + 3 := by rw [hm]; exact ih.1.1
    have hminimal : ∀ k, k < 2 * u → hit k ≠ n + 3 := by
      intro k hk hhit
      have hle : m ≤ k := ih.1.2 hhit
      omega
    have hnext := actual_hit_minimal_next hu hdepth hminimal
    have hnext_eq : leastHit (n + 3 + 1) = u ^ 2 + 1 := hnext.csInf_eq
    have hindex : n + 1 + 3 = n + 3 + 1 := by omega
    change IsLeast {k : ℕ | hit k = n + 1 + 3} (leastHit (n + 1 + 3)) ∧
      4 ≤ leastHit (n + 1 + 3) ∧ leastHit (n + 1 + 3) % 4 = 2
    rw [hindex, hnext_eq]
    exact ⟨hnext, next_even_invariant hu hodd⟩

theorem leastHit_recurrence (n : ℕ) :
    leastHit (n + 4) = (leastHit (n + 3) / 2) ^ 2 + 1 := by
  have ih := leastHit_invariant n
  let m := leastHit (n + 3)
  let u := m / 2
  have hm : 2 * u = m := by dsimp [u, m] at *; omega
  have hu : 2 ≤ u := by dsimp [u, m] at *; omega
  have hdepth : hit (2 * u) = n + 3 := by rw [hm]; exact ih.1.1
  have hminimal : ∀ k, k < 2 * u → hit k ≠ n + 3 := by
    intro k hk hhit
    have hle : m ≤ k := ih.1.2 hhit
    omega
  have hnext := actual_hit_sInf_next hu hdepth hminimal
  have hindex : n + 4 = n + 3 + 1 := by omega
  change sInf {k : ℕ | hit k = n + 4} = u ^ 2 + 1
  rw [hindex]
  exact hnext

end A025486Scratch


namespace A025486Greedy

/-- The remainder in one greedy subtraction of the largest square. -/
def step (k : ℕ) : ℕ := k - (Nat.sqrt k) ^ 2

/-- The least integer with greedy-square remainder `y`. -/
def predecessor (y : ℕ) : ℕ := y + ((y + 1) / 2) ^ 2

theorem predecessor_step (y : ℕ) : step (predecessor y) = y := by
  let s := (y + 1) / 2
  have hbound : y ≤ s + s := by
    dsimp [s]
    omega
  have hs : Nat.sqrt (s ^ 2 + y) = s := Nat.sqrt_add_eq' s hbound
  unfold step predecessor
  change y + s ^ 2 - (Nat.sqrt (y + s ^ 2)) ^ 2 = y
  rw [Nat.add_comm y (s ^ 2), hs]
  omega

theorem predecessor_min (y k : ℕ) (h : step k = y) : predecessor y ≤ k := by
  let s := Nat.sqrt k
  have hs : s ^ 2 ≤ k := Nat.sqrt_le' k
  have htop : k < (s + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have heq : s ^ 2 + y = k := by
    change k - s ^ 2 = y at h
    omega
  have hy : y ≤ s + s := by nlinarith
  have hhalf : (y + 1) / 2 ≤ s := by omega
  unfold predecessor
  have hsq : ((y + 1) / 2) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hhalf 2
  omega

theorem predecessor_isLeast (y : ℕ) :
    IsLeast {k : ℕ | step k = y} (predecessor y) := by
  exact ⟨predecessor_step y, fun _ hk => predecessor_min y _ hk⟩

theorem predecessor_strictMono : StrictMono predecessor := by
  intro m n hmn
  have hhalf : (m + 1) / 2 ≤ (n + 1) / 2 := by omega
  have hsq := Nat.pow_le_pow_left hhalf 2
  dsimp [predecessor]
  omega

theorem step_lt (k : ℕ) (hk : 0 < k) : step k < k := by
  have hs : 0 < Nat.sqrt k := Nat.sqrt_pos.mpr hk
  have hsq : 0 < (Nat.sqrt k) ^ 2 := pow_pos hs 2
  have hle := Nat.sqrt_le' k
  dsimp [step]
  omega

/-- Number of greedy-square subtractions needed to reach zero. -/
def height : ℕ → ℕ
  | 0 => 0
  | k + 1 => height (step (k + 1)) + 1
termination_by k => k
decreasing_by
  exact step_lt _ (by omega)

theorem height_of_pos (k : ℕ) (hk : 0 < k) :
    height k = height (step k) + 1 := by
  cases k with
  | zero => omega
  | succ k => rw [height]

/-- Candidate least starting value requiring exactly `t` greedy steps. -/
def first : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | t + 2 => predecessor (first (t + 1))

theorem first_pos (t : ℕ) : 0 < first (t + 1) := by
  induction t with
  | zero => simp [first]
  | succ t ih =>
    rw [first]
    dsimp [predecessor]
    omega

theorem first_correct (t : ℕ) :
    height (first t) = t ∧ ∀ k, height k = t → first t ≤ k := by
  induction t with
  | zero =>
    constructor
    · simp [first, height]
    · intro k _
      exact Nat.zero_le k
  | succ t ih =>
    cases t with
    | zero =>
      constructor
      · norm_num [first, height, step]
      · intro k hk
        cases k with
        | zero => simp [height] at hk
        | succ k => simp [first]
    | succ t =>
      have hp : 0 < first (t + 1) := first_pos t
      have hpp : 0 < predecessor (first (t + 1)) := by
        dsimp [predecessor]
        omega
      constructor
      · rw [first, height_of_pos _ hpp, predecessor_step, ih.1]
      · intro k hk
        have hkpos : 0 < k := by
          cases k with
          | zero => simp [height] at hk
          | succ k => omega
        have hstep : height (step k) = t + 1 := by
          rw [height_of_pos _ hkpos] at hk
          omega
        have hmin := ih.2 (step k) hstep
        have hmono := predecessor_strictMono.monotone hmin
        have hkmin := predecessor_min (step k) k rfl
        rw [first]
        exact le_trans hmono hkmin

theorem first_isLeast (t : ℕ) :
    IsLeast {k : ℕ | height k = t} (first t) := by
  exact ⟨(first_correct t).1, (first_correct t).2⟩

/-- The recursive height agrees with the first zero of the iterated map. -/
theorem iterate_step_zero_iff (t k : ℕ) :
    (step^[t]) k = 0 ↔ height k ≤ t := by
  induction t generalizing k with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    constructor
    · intro hk
      subst k
      simp [height]
    · intro hk
      by_contra h
      have hp : 0 < k := Nat.pos_of_ne_zero h
      have hh := height_of_pos k hp
      omega
  | succ t ih =>
    rw [Function.iterate_succ_apply, ih]
    by_cases hk : k = 0
    · subst k
      simp [step, height]
    · have hp : 0 < k := Nat.pos_of_ne_zero hk
      rw [height_of_pos k hp]
      omega

theorem firstHit_eq_height (k : ℕ) :
    sInf {t : ℕ | (step^[t]) k ≤ 0} = height k := by
  apply IsLeast.csInf_eq
  constructor
  · exact Nat.le_zero.mpr ((iterate_step_zero_iff _ _).2 le_rfl)
  · intro t ht
    exact (iterate_step_zero_iff _ _).1 (Nat.eq_zero_of_le_zero ht)

theorem reaches_zero (k : ℕ) : ∃ t : ℕ, (step^[t]) k ≤ 0 := by
  exact ⟨height k, Nat.le_zero.mpr ((iterate_step_zero_iff _ _).2 le_rfl)⟩

theorem first_four : first 4 = 7 := by
  norm_num [first, predecessor]

theorem leastInput_without_reaches_eq_first (t : ℕ) :
    sInf {k : ℕ | sInf {j : ℕ | (step^[j]) k ≤ 0} = t} = first t := by
  apply IsLeast.csInf_eq
  constructor
  · change sInf {j : ℕ | (step^[j]) (first t) ≤ 0} = t
    rw [firstHit_eq_height]
    exact (first_correct t).1
  · intro k hk
    apply (first_correct t).2 k
    have hk' : sInf {j : ℕ | (step^[j]) k ≤ 0} = t := hk
    rw [firstHit_eq_height] at hk'
    exact hk'

theorem fourth_firstInput :
    sInf {k : ℕ | sInf {j : ℕ | (step^[j]) k ≤ 0} = 4} = 7 := by
  rw [leastInput_without_reaches_eq_first, first_four]

theorem leastInput_eq_first (t : ℕ) :
    sInf {k : ℕ | (∃ j : ℕ, (step^[j]) k ≤ 0) ∧
      sInf {j : ℕ | (step^[j]) k ≤ 0} = t} = first t := by
  apply IsLeast.csInf_eq
  constructor
  · constructor
    · exact ⟨height (first t), Nat.le_zero.mpr ((iterate_step_zero_iff _ _).2 le_rfl)⟩
    · rw [firstHit_eq_height]
      exact (first_correct t).1
  · intro k hk
    apply (first_correct t).2 k
    have hhit : sInf {j : ℕ | (step^[j]) k ≤ 0} = t := hk.2
    rw [firstHit_eq_height] at hhit
    exact hhit

end A025486Greedy


namespace A025486Compare

def cpred (x : ℕ) : ℕ := (x / 2) ^ 2 + 1
def gpred (y : ℕ) : ℕ := y + ((y + 1) / 2) ^ 2

theorem cpred_mod_four {x : ℕ} (hx : x % 4 = 2) : cpred x % 4 = 2 := by
  unfold cpred
  have h : (x / 2) % 4 = 1 ∨ (x / 2) % 4 = 3 := by omega
  rw [pow_two, Nat.add_mod, Nat.mul_mod]
  rcases h with h | h <;> norm_num [h]

theorem pred_agree {x y : ℕ} (hxy : x = y + 3) (hx : x % 2 = 0) :
    cpred x = gpred y + 3 := by
  unfold cpred gpred
  have hh : x / 2 = (y + 1) / 2 + 1 := by omega
  rw [hh]
  have hy : y + 1 = 2 * ((y + 1) / 2) := by omega
  nlinarith

theorem compare (a b : ℕ → ℕ) (ha : a 3 = 10) (hb : b 4 = 7)
    (hstepA : ∀ n, 3 ≤ n → a (n + 1) = cpred (a n))
    (hstepB : ∀ n, 4 ≤ n → b (n + 1) = gpred (b n)) :
    ∀ n, 3 ≤ n → a n = b (n + 1) + 3 := by
  have aux : ∀ k, a (k + 3) = b (k + 4) + 3 ∧ a (k + 3) % 4 = 2 := by
    intro k
    induction k with
    | zero => simp [ha, hb]
    | succ k ih =>
      have hA := hstepA (k + 3) (by omega)
      have hB := hstepB (k + 4) (by omega)
      have h : a (k + 3 + 1) = b (k + 4 + 1) + 3 := by
        rw [hA, hB]
        exact pred_agree ih.1 (by omega)
      have hm : a (k + 3 + 1) % 4 = 2 := by
        rw [hA]
        exact cpred_mod_four ih.2
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro h hm
  intro n hn
  have h := aux (n - 3)
  have h1 : n - 3 + 3 = n := by omega
  have h2 : n - 3 + 4 = n + 1 := by omega
  simpa only [h1, h2] using h.1

end A025486Compare

namespace A025486Bridge

open OMA.S_oeis_a025486

lemma complement_eq (n : ℕ) : leastInput complement 2 n = A025486Scratch.leastHit n := by
  unfold leastInput A025486Scratch.leastHit
  apply congrArg sInf
  ext k
  change ((∃ t, (A025486Scratch.squareComplement^[t]) k ≤ 2) ∧
    A025486Scratch.hit k = n) ↔ A025486Scratch.hit k = n
  exact ⟨And.right, fun h => ⟨A025486Scratch.reaches_all k, h⟩⟩

lemma greedy_eq (n : ℕ) : leastInput subtractSquare 0 n = A025486Greedy.first n := by
  change sInf {k : ℕ | (∃ j : ℕ, (A025486Greedy.step^[j]) k ≤ 0) ∧
    sInf {j : ℕ | (A025486Greedy.step^[j]) k ≤ 0} = n} = A025486Greedy.first n
  exact A025486Greedy.leastInput_eq_first n

lemma complement_step (n : ℕ) (hn : 3 ≤ n) :
    A025486Scratch.leastHit (n + 1) = A025486Compare.cpred (A025486Scratch.leastHit n) := by
  have h := A025486Scratch.leastHit_recurrence (n - 3)
  have h1 : n - 3 + 3 = n := by omega
  have h2 : n - 3 + 4 = n + 1 := by omega
  simpa only [h1, h2, A025486Compare.cpred] using h

lemma greedy_step (n : ℕ) (hn : 4 ≤ n) :
    A025486Greedy.first (n + 1) = A025486Compare.gpred (A025486Greedy.first n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  change A025486Greedy.first ((m + 3) + 2) =
    A025486Compare.gpred (A025486Greedy.first ((m + 3) + 1))
  rfl

theorem result : ∀ n : ℕ, 3 ≤ n →
    leastInput complement 2 n = leastInput subtractSquare 0 (n + 1) + 3 := by
  intro n hn
  rw [complement_eq, greedy_eq]
  exact A025486Compare.compare A025486Scratch.leastHit A025486Greedy.first
    A025486Scratch.first_hit_three A025486Greedy.first_four complement_step greedy_step n hn

end A025486Bridge


theorem OMA.solution : type_of% @OMA.S_oeis_a025486.main := by
  exact A025486Bridge.result
