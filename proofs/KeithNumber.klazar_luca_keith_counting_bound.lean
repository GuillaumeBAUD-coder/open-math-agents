import FormalConjectures.Wikipedia.KeithNumber

-- Problem: Keith numbers — klazar luca keith counting bound
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/KeithNumber.lean:180 (declaration KeithNumber.klazar_luca_keith_counting_bound)
-- Credit: @DomTheDeveloper (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Original proof (written for this submission).

A window of length `n` is a function `ℕ → ℕ` supported on `[0, n)`; `stp` is one step of the Keith
recurrence and `S n m w` is the sum of the window after `m` steps, which is the last entry after
`m + 1` steps.  A number `N` with `n` digits `d` is Keith iff `S n m d = N` for some `m`.

* `S n m` is additive, so `S n m d = ∑ d_j ω_j` with `ω_j = S n m (unit j)`, and
  `ω_0 ≤ ω_j ≤ 2 ω_0`, `ω_j` nondecreasing in `j`.
* For a fixed `m` the place values `10 ^ (n - 1 - j)` decrease while the `ω_j` increase, so on the
  top `h = (n - 1) / 2` positions or on the bottom `h` positions the differences have one strict
  sign.  Splitting the digits there as `2 e + b` and applying Sperner's theorem to the bits `b`
  shows that at most `C(h, h/2) 5 ^ h 10 ^ (n - h)` digit vectors solve `S n m d = value d`.
* If the digit sum is at least `n`, the index `m` satisfies `n ω_0 < 10 ^ n ≤ 180 n ω_0`, which
  leaves at most `16` values of `m` because `ω_0` doubles every two steps.  At most `4 ^ n` digit
  vectors have digit sum below `n`.
Hence there are `O(10 ^ n / √n)` Keith numbers with `n` digits, and summing over `n` gives the bound.
-/

/-- One step of the Keith recurrence on windows `ℕ → ℕ` supported on `[0, n)`. -/
def OMA.stp (n : ℕ) (w : ℕ → ℕ) : ℕ → ℕ :=
  fun j => if j + 1 < n then w (j + 1) else if j + 1 = n then ∑ t ∈ Finset.range n, w t else 0

/-- The sum of the window after `m` steps. -/
def OMA.S (n m : ℕ) (w : ℕ → ℕ) : ℕ := ∑ t ∈ Finset.range n, (OMA.stp n)^[m] w t

/-- The unit window. -/
def OMA.unit (i : ℕ) : ℕ → ℕ := fun j => if j = i then 1 else 0

/-- The value of a window read as base-10 digits, most significant first. -/
def OMA.valr : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, w => w n + 10 * OMA.valr n w

theorem OMA.stp_add (n : ℕ) (u v : ℕ → ℕ) :
    OMA.stp n (u + v) = OMA.stp n u + OMA.stp n v := by
  funext j
  simp only [OMA.stp, Pi.add_apply]
  split_ifs
  · rfl
  · exact Finset.sum_add_distrib
  · rfl

theorem OMA.stp_zero (n : ℕ) : OMA.stp n 0 = 0 := by
  funext j
  simp [OMA.stp]

theorem OMA.iter_add (n : ℕ) : ∀ (m : ℕ) (u v : ℕ → ℕ),
    (OMA.stp n)^[m] (u + v) = (OMA.stp n)^[m] u + (OMA.stp n)^[m] v := by
  intro m
  induction m with
  | zero => intro u v; rfl
  | succ m ih =>
    intro u v
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      OMA.stp_add, ih]

theorem OMA.S_add (n m : ℕ) (u v : ℕ → ℕ) : OMA.S n m (u + v) = OMA.S n m u + OMA.S n m v := by
  unfold OMA.S
  rw [OMA.iter_add, ← Finset.sum_add_distrib]
  rfl

theorem OMA.S_zero (n m : ℕ) : OMA.S n m 0 = 0 := by
  unfold OMA.S
  rw [Function.iterate_fixed (OMA.stp_zero n)]
  simp

theorem OMA.S_sum {ι : Type} (n m : ℕ) (D : Finset ι) (f : ι → ℕ → ℕ) :
    OMA.S n m (∑ i ∈ D, f i) = ∑ i ∈ D, OMA.S n m (f i) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [OMA.S_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, OMA.S_add, ih]

theorem OMA.S_smul (n m c : ℕ) (v : ℕ → ℕ) : OMA.S n m (c • v) = c * OMA.S n m v := by
  induction c with
  | zero => simp [OMA.S_zero]
  | succ c ih =>
    rw [succ_nsmul, OMA.S_add, ih]
    ring

theorem OMA.S_mono (n m : ℕ) (u v : ℕ → ℕ) (huv : ∀ j, u j ≤ v j) : OMA.S n m u ≤ OMA.S n m v := by
  have h : v = u + fun j => v j - u j := by
    funext j
    have := huv j
    simp only [Pi.add_apply]
    omega
  rw [h, OMA.S_add]
  exact Nat.le_add_right _ _

theorem OMA.S_succ_eq (n m : ℕ) (v : ℕ → ℕ) : OMA.S n (m + 1) v = OMA.S n m (OMA.stp n v) := by
  unfold OMA.S
  rw [Function.iterate_succ_apply]

theorem OMA.sum_stp (n : ℕ) (hn : 1 ≤ n) (w : ℕ → ℕ) :
    (∑ t ∈ Finset.range n, OMA.stp n w t) + w 0 = 2 * ∑ t ∈ Finset.range n, w t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : ∑ t ∈ Finset.range k, OMA.stp (k + 1) w t = ∑ t ∈ Finset.range k, w (t + 1) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t < k := Finset.mem_range.mp ht
    simp [OMA.stp, ht']
  have h2 : OMA.stp (k + 1) w k = ∑ t ∈ Finset.range (k + 1), w t := by
    simp [OMA.stp]
  have h3 := Finset.sum_range_succ' w k
  rw [Finset.sum_range_succ, h1, h2]
  omega

/-- `S (m+1) + W_m(0) = 2 S m`. -/
theorem OMA.S_rec (n m : ℕ) (hn : 1 ≤ n) (w : ℕ → ℕ) :
    OMA.S n (m + 1) w + (OMA.stp n)^[m] w 0 = 2 * OMA.S n m w := by
  unfold OMA.S
  rw [Function.iterate_succ_apply']
  exact OMA.sum_stp n hn _

theorem OMA.S_double (n m : ℕ) (hn : 1 ≤ n) (w : ℕ → ℕ) : OMA.S n (m + 1) w ≤ 2 * OMA.S n m w := by
  have := OMA.S_rec n m hn w
  omega

theorem OMA.S_le_succ (n m : ℕ) (hn : 1 ≤ n) (w : ℕ → ℕ) : OMA.S n m w ≤ OMA.S n (m + 1) w := by
  have h1 := OMA.S_rec n m hn w
  have h2 : (OMA.stp n)^[m] w 0 ≤ OMA.S n m w := by
    unfold OMA.S
    exact Finset.single_le_sum (f := fun t => (OMA.stp n)^[m] w t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hn)
  omega

theorem OMA.S_le_of_le (n : ℕ) (hn : 1 ≤ n) (w : ℕ → ℕ) (m m' : ℕ) (h : m ≤ m') :
    OMA.S n m w ≤ OMA.S n m' w := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (OMA.S_le_succ n _ hn w)

/-- The window sum at least doubles every two steps. -/
theorem OMA.S_growth (n m : ℕ) (hn : 2 ≤ n) (w : ℕ → ℕ) :
    2 * OMA.S n m w ≤ OMA.S n (m + 2) w := by
  have h1 := OMA.S_rec n m (by omega) w
  have h2 : OMA.S n (m + 2) w + (OMA.stp n)^[m + 1] w 0 = 2 * OMA.S n (m + 1) w :=
    OMA.S_rec n (m + 1) (by omega) w
  have h3 : (OMA.stp n)^[m + 1] w 0 = (OMA.stp n)^[m] w 1 := by
    rw [Function.iterate_succ_apply']
    simp only [OMA.stp]
    rw [if_pos (by omega)]
  have h4 : (OMA.stp n)^[m] w 0 + (OMA.stp n)^[m] w 1 ≤ OMA.S n m w := by
    unfold OMA.S
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range n := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_range]
      omega
    have hpair : ∑ t ∈ ({0, 1} : Finset ℕ), (OMA.stp n)^[m] w t
        = (OMA.stp n)^[m] w 0 + (OMA.stp n)^[m] w 1 := Finset.sum_pair (by norm_num)
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset hsub
  omega

theorem OMA.S_growth_pow (n : ℕ) (hn : 2 ≤ n) (w : ℕ → ℕ) (m : ℕ) :
    ∀ t, 2 ^ t * OMA.S n m w ≤ OMA.S n (m + 2 * t) w := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have h := OMA.S_growth n (m + 2 * t) hn w
    have e : m + 2 * (t + 1) = m + 2 * t + 2 := by ring
    rw [e, pow_succ]
    calc 2 ^ t * 2 * OMA.S n m w = 2 * (2 ^ t * OMA.S n m w) := by ring
      _ ≤ 2 * OMA.S n (m + 2 * t) w := Nat.mul_le_mul_left 2 ih
      _ ≤ OMA.S n (m + 2 * t + 2) w := h

theorem OMA.sum_unit (n i : ℕ) (hi : i < n) : ∑ t ∈ Finset.range n, OMA.unit i t = 1 := by
  unfold OMA.unit
  rw [Finset.sum_ite_eq' (Finset.range n) i (fun _ => 1), if_pos (Finset.mem_range.mpr hi)]

theorem OMA.S_zero_unit (n i : ℕ) (hi : i < n) : OMA.S n 0 (OMA.unit i) = 1 := by
  unfold OMA.S
  exact OMA.sum_unit n i hi

theorem OMA.stp_unit_zero (n : ℕ) (hn : 1 ≤ n) : OMA.stp n (OMA.unit 0) = OMA.unit (n - 1) := by
  funext j
  unfold OMA.stp
  by_cases h1 : j + 1 < n
  · rw [if_pos h1]
    unfold OMA.unit
    split_ifs <;> omega
  · rw [if_neg h1]
    by_cases h2 : j + 1 = n
    · rw [if_pos h2, OMA.sum_unit n 0 (by omega)]
      unfold OMA.unit
      split_ifs <;> omega
    · rw [if_neg h2]
      unfold OMA.unit
      split_ifs <;> omega

theorem OMA.stp_unit_succ (n i : ℕ) (hi1 : 1 ≤ i) (hin : i < n) :
    OMA.stp n (OMA.unit i) = OMA.unit (i - 1) + OMA.unit (n - 1) := by
  funext j
  rw [Pi.add_apply]
  unfold OMA.stp
  by_cases h1 : j + 1 < n
  · rw [if_pos h1]
    unfold OMA.unit
    split_ifs <;> omega
  · rw [if_neg h1]
    by_cases h2 : j + 1 = n
    · rw [if_pos h2, OMA.sum_unit n i hin]
      unfold OMA.unit
      split_ifs <;> omega
    · rw [if_neg h2]
      unfold OMA.unit
      split_ifs <;> omega

/-- `S n m (unit i)` is nondecreasing in `i`. -/
theorem OMA.S_unit_step (n : ℕ) : ∀ i, i + 1 < n → ∀ m,
    OMA.S n m (OMA.unit i) ≤ OMA.S n m (OMA.unit (i + 1)) := by
  intro i
  induction i with
  | zero =>
    intro hi m
    cases m with
    | zero =>
      exact le_of_eq (by rw [OMA.S_zero_unit n 0 (by omega), OMA.S_zero_unit n (0 + 1) (by omega)])
    | succ m =>
      rw [OMA.S_succ_eq, OMA.S_succ_eq, OMA.stp_unit_zero n (by omega),
        OMA.stp_unit_succ n (0 + 1) (by omega) (by omega), OMA.S_add]
      exact Nat.le_add_left _ _
  | succ i ih =>
    intro hi m
    cases m with
    | zero =>
      exact le_of_eq (by
        rw [OMA.S_zero_unit n (i + 1) (by omega), OMA.S_zero_unit n (i + 1 + 1) (by omega)])
    | succ m =>
      rw [OMA.S_succ_eq, OMA.S_succ_eq, OMA.stp_unit_succ n (i + 1) (by omega) (by omega),
        OMA.stp_unit_succ n (i + 1 + 1) (by omega) (by omega), OMA.S_add, OMA.S_add]
      have h := ih (by omega) m
      simp only [Nat.add_sub_cancel]
      exact Nat.add_le_add_right h _

theorem OMA.S_unit_mono (n m : ℕ) : ∀ i j, i ≤ j → j < n →
    OMA.S n m (OMA.unit i) ≤ OMA.S n m (OMA.unit j) := by
  intro i j hij
  induction hij with
  | refl => intro _; exact le_refl _
  | step hle ih =>
    intro hj
    exact le_trans (ih (by omega)) (OMA.S_unit_step n _ (by omega) m)

theorem OMA.S_unit_le (n m i : ℕ) (hi : i < n) :
    OMA.S n m (OMA.unit i) ≤ 2 * OMA.S n m (OMA.unit 0) := by
  have h1 := OMA.S_unit_mono n m i (n - 1) (by omega) (by omega)
  have h2 : OMA.S n m (OMA.unit (n - 1)) = OMA.S n (m + 1) (OMA.unit 0) := by
    rw [OMA.S_succ_eq, OMA.stp_unit_zero n (by omega)]
  have h3 := OMA.S_double n m (by omega) (OMA.unit 0)
  omega

/-- Expansion of `S n m` along the unit windows. -/
theorem OMA.S_expand (n m : ℕ) (v : ℕ → ℕ) (hv : ∀ j, n ≤ j → v j = 0) :
    OMA.S n m v = ∑ j ∈ Finset.range n, v j * OMA.S n m (OMA.unit j) := by
  have hv' : v = ∑ j ∈ Finset.range n, v j • OMA.unit j := by
    funext k
    rw [Finset.sum_apply]
    have hterm : ∀ j ∈ Finset.range n, (v j • OMA.unit j) k = if k = j then v j else 0 := by
      intro j _
      simp [OMA.unit]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    by_cases hk : k < n
    · rw [if_pos (Finset.mem_range.mpr hk)]
    · rw [if_neg (fun h => hk (Finset.mem_range.mp h)), hv k (by omega)]
  conv_lhs => rw [hv']
  rw [OMA.S_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [OMA.S_smul]

theorem OMA.valr_add (n : ℕ) (u v : ℕ → ℕ) : OMA.valr n (u + v) = OMA.valr n u + OMA.valr n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OMA.valr, ih, Pi.add_apply]
    ring

theorem OMA.valr_zero (n : ℕ) : OMA.valr n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [OMA.valr, ih]

theorem OMA.valr_sum {ι : Type} (n : ℕ) (D : Finset ι) (f : ι → ℕ → ℕ) :
    OMA.valr n (∑ i ∈ D, f i) = ∑ i ∈ D, OMA.valr n (f i) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [OMA.valr_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, OMA.valr_add, ih]

theorem OMA.valr_unit_ge (n i : ℕ) (hi : n ≤ i) : OMA.valr n (OMA.unit i) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OMA.valr, ih (by omega), OMA.unit]
    rw [if_neg (by omega)]

theorem OMA.valr_unit (n i : ℕ) (hi : i < n) : OMA.valr n (OMA.unit i) = 10 ^ (n - 1 - i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [OMA.valr]
    by_cases h : i = n
    · subst h
      rw [OMA.valr_unit_ge i i (le_refl i)]
      simp [OMA.unit]
    · have hi' : i < n := by omega
      rw [ih hi']
      have e : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
      rw [e, pow_succ]
      simp only [OMA.unit]
      rw [if_neg (by omega)]
      ring

theorem OMA.valr_lt (n : ℕ) (v : ℕ → ℕ) (hv : ∀ j, v j ≤ 9) : OMA.valr n v < 10 ^ n := by
  induction n with
  | zero => simp [OMA.valr]
  | succ n ih =>
    simp only [OMA.valr]
    have := hv n
    rw [pow_succ]
    omega

theorem OMA.list_sum_range (n : ℕ) (w : ℕ → ℕ) :
    ((List.range n).map w).sum = ∑ t ∈ Finset.range n, w t := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, ih, Finset.sum_range_succ]

theorem OMA.list_eq_map (L : List ℕ) :
    L = (List.range L.length).map (fun j => L.getD j 0) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have h1 : ((fun j => (a :: t).getD j 0) ∘ Nat.succ) = fun j => t.getD j 0 := by
      funext j
      simp
    rw [h1, ← ih]
    simp

theorem OMA.kws_map (n : ℕ) (hn : 1 ≤ n) (w : ℕ → ℕ) :
    KeithNumber.keithWindowStep ((List.range n).map w) = (List.range n).map (OMA.stp n w) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold KeithNumber.keithWindowStep
  rw [OMA.list_sum_range]
  have h1 : ((List.range (k + 1)).map w).tail = (List.range k).map (fun j => w (j + 1)) := by
    rw [List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
    rfl
  have h2 : (List.range (k + 1)).map (OMA.stp (k + 1) w)
      = (List.range k).map (fun j => w (j + 1)) ++ [∑ t ∈ Finset.range (k + 1), w t] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro j hj
      have hj' : j < k := List.mem_range.mp hj
      simp [OMA.stp, hj']
    · simp [OMA.stp]
  rw [h1, h2]

theorem OMA.kws_iter (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (w : ℕ → ℕ) :
    (KeithNumber.keithWindowStep^[m]) ((List.range n).map w)
      = (List.range n).map ((OMA.stp n)^[m] w) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, OMA.kws_map n hn, Function.iterate_succ_apply']

theorem OMA.getLast_map (k : ℕ) (u : ℕ → ℕ) :
    ((List.range (k + 1)).map u).getLast? = some (u k) := by
  rw [List.range_succ, List.map_append, List.map_singleton, List.getLast?_concat]

theorem OMA.ofDigits_map (n : ℕ) (w : ℕ → ℕ) :
    Nat.ofDigits 10 ((List.range n).map w).reverse = OMA.valr n w := by
  induction n with
  | zero => simp [OMA.valr]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, Nat.ofDigits_cons, ih]
    simp [OMA.valr]

/-- A Keith number solves `S n m d = value d` for its own digit window `d`. -/
theorem OMA.keith_model (N : ℕ) (hK : KeithNumber.IsKeithNumber N) :
    (∃ m, OMA.S (Nat.digits 10 N).length m (fun j => (Nat.digits 10 N).reverse.getD j 0) = N) ∧
      OMA.valr (Nat.digits 10 N).length (fun j => (Nat.digits 10 N).reverse.getD j 0) = N := by
  obtain ⟨-, hN, m, hm, hlast⟩ := hK
  have hpos : 1 ≤ (Nat.digits 10 N).length := by
    have h1 := Nat.lt_base_pow_length_digits (b := 10) (m := N) (by norm_num)
    by_contra h
    have h0 : (Nat.digits 10 N).length = 0 := by omega
    rw [h0] at h1
    omega
  have hLmap : (Nat.digits 10 N).reverse
      = (List.range (Nat.digits 10 N).length).map (fun j => (Nat.digits 10 N).reverse.getD j 0) := by
    have h := OMA.list_eq_map (Nat.digits 10 N).reverse
    rw [List.length_reverse] at h
    exact h
  have hval : OMA.valr (Nat.digits 10 N).length (fun j => (Nat.digits 10 N).reverse.getD j 0)
      = N := by
    rw [← OMA.ofDigits_map, ← hLmap, List.reverse_reverse, Nat.ofDigits_digits]
  refine ⟨?_, hval⟩
  rw [hLmap, OMA.kws_iter _ hpos] at hlast
  obtain ⟨k, hk⟩ : ∃ k, (Nat.digits 10 N).length = k + 1 :=
    ⟨(Nat.digits 10 N).length - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨m', ?_⟩
  rw [hk] at hlast ⊢
  rw [OMA.getLast_map, Function.iterate_succ_apply'] at hlast
  have h3 := Option.some.inj hlast
  have h4 : ∀ W : ℕ → ℕ, OMA.stp (k + 1) W k = ∑ t ∈ Finset.range (k + 1), W t := by
    intro W
    simp [OMA.stp]
  rw [h4] at h3
  unfold OMA.S
  exact h3

/-- A digit vector as a window. -/
def OMA.hat (n : ℕ) (d : Fin n → Fin 10) : ℕ → ℕ :=
  fun j => if h : j < n then ((d ⟨j, h⟩ : Fin 10) : ℕ) else 0

/-- Round a digit down to an even digit. -/
def OMA.evn (a : Fin 10) : Fin 10 := ⟨2 * ((a : ℕ) / 2), by have := a.isLt; omega⟩

/-- Round the digits in the block down to even digits. -/
def OMA.rho {n h : ℕ} (blk : Fin h → Fin n) (d : Fin n → Fin 10) : Fin n → Fin 10 :=
  fun j => if j ∈ Finset.univ.image blk then OMA.evn (d j) else d j

/-- The set of block positions carrying an odd digit. -/
def OMA.sig {n h : ℕ} (blk : Fin h → Fin n) (d : Fin n → Fin 10) : Finset (Fin h) :=
  Finset.univ.filter (fun i => ((d (blk i) : Fin 10) : ℕ) % 2 = 1)

theorem OMA.hat_lt (n : ℕ) (d : Fin n → Fin 10) (j : ℕ) (hj : j < n) :
    OMA.hat n d j = ((d ⟨j, hj⟩ : Fin 10) : ℕ) := by
  unfold OMA.hat
  rw [dif_pos hj]

theorem OMA.hat_ge (n : ℕ) (d : Fin n → Fin 10) (j : ℕ) (hj : n ≤ j) : OMA.hat n d j = 0 := by
  unfold OMA.hat
  rw [dif_neg (by omega)]

theorem OMA.hat_le (n : ℕ) (d : Fin n → Fin 10) (j : ℕ) : OMA.hat n d j ≤ 9 := by
  by_cases hj : j < n
  · rw [OMA.hat_lt n d j hj]
    have := (d ⟨j, hj⟩).isLt
    omega
  · rw [OMA.hat_ge n d j (by omega)]
    omega

theorem OMA.hat_sum (n : ℕ) (d : Fin n → Fin 10) :
    ∑ j ∈ Finset.range n, OMA.hat n d j = ∑ j : Fin n, ((d j : Fin 10) : ℕ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => OMA.hat_lt n d j j.isLt

theorem OMA.rho_blk {n h : ℕ} (blk : Fin h → Fin n) (d : Fin n → Fin 10) (i : Fin h) :
    OMA.rho blk d (blk i) = OMA.evn (d (blk i)) := by
  unfold OMA.rho
  rw [if_pos (Finset.mem_image_of_mem blk (Finset.mem_univ i))]

theorem OMA.rho_not {n h : ℕ} (blk : Fin h → Fin n) (d : Fin n → Fin 10) (j : Fin n)
    (hj : j ∉ Finset.univ.image blk) : OMA.rho blk d j = d j := by
  unfold OMA.rho
  rw [if_neg hj]

theorem OMA.mem_sig {n h : ℕ} (blk : Fin h → Fin n) (d : Fin n → Fin 10) (i : Fin h) :
    i ∈ OMA.sig blk d ↔ ((d (blk i) : Fin 10) : ℕ) % 2 = 1 := by
  unfold OMA.sig
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩

theorem OMA.half_eq {n h : ℕ} (blk : Fin h → Fin n) (d d' : Fin n → Fin 10)
    (hrho : OMA.rho blk d = OMA.rho blk d') (i : Fin h) :
    ((d (blk i) : Fin 10) : ℕ) / 2 = ((d' (blk i) : Fin 10) : ℕ) / 2 := by
  have h1 := congrFun hrho (blk i)
  rw [OMA.rho_blk, OMA.rho_blk] at h1
  have h2 : 2 * (((d (blk i) : Fin 10) : ℕ) / 2) = 2 * (((d' (blk i) : Fin 10) : ℕ) / 2) :=
    congrArg Fin.val h1
  omega

/-- Two digit vectors in the same cube differ by the indicator of the new odd positions. -/
theorem OMA.hat_cube {n h : ℕ} (blk : Fin h → Fin n) (hblk : Function.Injective blk)
    (d d' : Fin n → Fin 10) (hrho : OMA.rho blk d = OMA.rho blk d')
    (hsub : OMA.sig blk d ⊆ OMA.sig blk d') :
    OMA.hat n d' = OMA.hat n d + ∑ i ∈ OMA.sig blk d' \ OMA.sig blk d, OMA.unit (blk i) := by
  funext j
  rw [Pi.add_apply, Finset.sum_apply]
  by_cases hj : j < n
  · rw [OMA.hat_lt n d' j hj, OMA.hat_lt n d j hj]
    by_cases hex : ∃ i, i ∈ OMA.sig blk d' \ OMA.sig blk d ∧ ((blk i : Fin n) : ℕ) = j
    · obtain ⟨i, hi, hij⟩ := hex
      have hsum : ∑ i' ∈ OMA.sig blk d' \ OMA.sig blk d, OMA.unit (blk i') j = 1 := by
        rw [Finset.sum_eq_single_of_mem i hi]
        · unfold OMA.unit
          rw [if_pos hij.symm]
        · intro i' _ hne
          unfold OMA.unit
          rw [if_neg]
          intro h'
          exact hne (hblk (Fin.ext (h'.symm.trans hij.symm)))
      rw [hsum]
      have he : (⟨j, hj⟩ : Fin n) = blk i := Fin.ext hij.symm
      rw [he]
      obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.mp hi
      rw [OMA.mem_sig] at hi1 hi2
      have hhalf := OMA.half_eq blk d d' hrho i
      omega
    · have hsum : ∑ i' ∈ OMA.sig blk d' \ OMA.sig blk d, OMA.unit (blk i') j = 0 := by
        apply Finset.sum_eq_zero
        intro i' hi'
        unfold OMA.unit
        rw [if_neg]
        intro h'
        exact hex ⟨i', hi', h'.symm⟩
      rw [hsum, Nat.add_zero]
      by_cases himg : (⟨j, hj⟩ : Fin n) ∈ Finset.univ.image blk
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp himg
        have hhalf := OMA.half_eq blk d d' hrho i
        have hpar : i ∈ OMA.sig blk d' → i ∈ OMA.sig blk d := by
          intro h1
          by_contra h2
          exact hex ⟨i, Finset.mem_sdiff.mpr ⟨h1, h2⟩, by rw [hi]⟩
        have hpar' : i ∈ OMA.sig blk d → i ∈ OMA.sig blk d' := fun h1 => hsub h1
        rw [OMA.mem_sig, OMA.mem_sig] at hpar hpar'
        rw [← hi]
        omega
      · have h1 := congrFun hrho ⟨j, hj⟩
        rw [OMA.rho_not blk d _ himg, OMA.rho_not blk d' _ himg] at h1
        rw [h1]
  · rw [OMA.hat_ge n d' j (by omega), OMA.hat_ge n d j (by omega)]
    symm
    rw [Nat.zero_add]
    apply Finset.sum_eq_zero
    intro i' _
    unfold OMA.unit
    rw [if_neg]
    have := (blk i').isLt
    omega

/-- In one cube the solutions form an antichain, so Sperner's theorem bounds their number. -/
theorem OMA.lo_fiber (n h : ℕ) (blk : Fin h → Fin n) (hblk : Function.Injective blk)
    (A B : (ℕ → ℕ) → ℕ)
    (hA : ∀ (D : Finset (Fin h)) (v : ℕ → ℕ),
      A (v + ∑ i ∈ D, OMA.unit (blk i)) = A v + ∑ i ∈ D, A (OMA.unit (blk i)))
    (hB : ∀ (D : Finset (Fin h)) (v : ℕ → ℕ),
      B (v + ∑ i ∈ D, OMA.unit (blk i)) = B v + ∑ i ∈ D, B (OMA.unit (blk i)))
    (hsign : (∀ i, B (OMA.unit (blk i)) < A (OMA.unit (blk i))) ∨
      (∀ i, A (OMA.unit (blk i)) < B (OMA.unit (blk i))))
    (F : Fin n → Fin 10) (fib : Finset (Fin n → Fin 10))
    (hfib : ∀ d ∈ fib, A (OMA.hat n d) = B (OMA.hat n d) ∧ OMA.rho blk d = F) :
    fib.card ≤ h.choose (h / 2) := by
  classical
  have hinj : Set.InjOn (OMA.sig blk) (fib : Set (Fin n → Fin 10)) := by
    intro d hd d' hd' hsig
    have hrho : OMA.rho blk d = OMA.rho blk d' :=
      (hfib d (Finset.mem_coe.mp hd)).2.trans (hfib d' (Finset.mem_coe.mp hd')).2.symm
    funext j
    by_cases hj : j ∈ Finset.univ.image blk
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
      have h1 := OMA.half_eq blk d d' hrho i
      have h2 : i ∈ OMA.sig blk d ↔ i ∈ OMA.sig blk d' := by rw [hsig]
      rw [OMA.mem_sig, OMA.mem_sig] at h2
      apply Fin.ext
      omega
    · have h1 := congrFun hrho j
      rw [OMA.rho_not blk d j hj, OMA.rho_not blk d' j hj] at h1
      exact h1
  rw [← Finset.card_image_of_injOn hinj]
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (fib.image (OMA.sig blk))) := by
    refine fun S hS S' hS' hne hsub => ?_
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS)
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS')
    obtain ⟨hsol, hdF⟩ := hfib d hd
    obtain ⟨hsol', hdF'⟩ := hfib d' hd'
    have hrho : OMA.rho blk d = OMA.rho blk d' := hdF.trans hdF'.symm
    have hcube := OMA.hat_cube blk hblk d d' hrho hsub
    have hne' : (OMA.sig blk d' \ OMA.sig blk d).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      exact hne (Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp hempty))
    rw [hcube, hA, hB] at hsol'
    rcases hsign with hs | hs
    · have hlt := Finset.sum_lt_sum_of_nonempty hne' (fun i _ => hs i)
      omega
    · have hlt := Finset.sum_lt_sum_of_nonempty hne' (fun i _ => hs i)
      omega
  have h1 := hanti.sperner
  rwa [Fintype.card_fin] at h1

/-- Anti-concentration: few digit vectors solve `A d = B d`. -/
theorem OMA.lo (n h : ℕ) (blk : Fin h → Fin n) (hblk : Function.Injective blk)
    (A B : (ℕ → ℕ) → ℕ)
    (hA : ∀ (D : Finset (Fin h)) (v : ℕ → ℕ),
      A (v + ∑ i ∈ D, OMA.unit (blk i)) = A v + ∑ i ∈ D, A (OMA.unit (blk i)))
    (hB : ∀ (D : Finset (Fin h)) (v : ℕ → ℕ),
      B (v + ∑ i ∈ D, OMA.unit (blk i)) = B v + ∑ i ∈ D, B (OMA.unit (blk i)))
    (hsign : (∀ i, B (OMA.unit (blk i)) < A (OMA.unit (blk i))) ∨
      (∀ i, A (OMA.unit (blk i)) < B (OMA.unit (blk i)))) :
    (Finset.univ.filter (fun d : Fin n → Fin 10 => A (OMA.hat n d) = B (OMA.hat n d))).card
      ≤ h.choose (h / 2) * (5 ^ h * 10 ^ (n - h)) := by
  classical
  have hE : (Finset.univ.image OMA.evn : Finset (Fin 10)).card = 5 := by decide
  have himg : (Finset.univ.image blk).card = h := by
    rw [Finset.card_image_of_injective _ hblk, Finset.card_univ, Fintype.card_fin]
  have hhn : h ≤ n := by
    have h1 := Finset.card_le_univ (Finset.univ.image blk)
    rw [himg, Fintype.card_fin] at h1
    exact h1
  have hT : (Fintype.piFinset (fun j : Fin n =>
      if j ∈ Finset.univ.image blk then (Finset.univ.image OMA.evn : Finset (Fin 10))
      else Finset.univ)).card = 5 ^ h * 10 ^ (n - h) := by
    rw [Fintype.card_piFinset]
    have hprod : ∀ j : Fin n, (if j ∈ Finset.univ.image blk
        then (Finset.univ.image OMA.evn : Finset (Fin 10)) else Finset.univ).card
        = if j ∈ Finset.univ.image blk then 5 else 10 := by
      intro j
      split_ifs
      · exact hE
      · simp
    rw [Finset.prod_congr rfl (fun j _ => hprod j), Finset.prod_ite, Finset.prod_const,
      Finset.prod_const]
    have h1 : (Finset.univ.filter (fun j : Fin n => j ∈ Finset.univ.image blk)).card = h := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter, himg]
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => j ∈ Finset.univ.image blk)
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (Finset.univ.filter (fun j : Fin n => ¬ j ∈ Finset.univ.image blk)).card = n - h := by
      omega
    rw [h1, h3]
  rw [← hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := OMA.rho blk) ?_ (h.choose (h / 2)) ?_
  · intro d _
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j ∈ Finset.univ.image blk
    · rw [if_pos hj]
      unfold OMA.rho
      rw [if_pos hj]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · rw [if_neg hj]
      exact Finset.mem_univ _
  · intro F _
    exact OMA.lo_fiber n h blk hblk A B hA hB hsign F _ (fun d hd =>
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2, (Finset.mem_filter.mp hd).2⟩)

/-- For each `m`, few digit vectors solve `S n m d = value d`. -/
theorem OMA.lo_main (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    (Finset.univ.filter (fun d : Fin n → Fin 10 =>
      OMA.S n m (OMA.hat n d) = OMA.valr n (OMA.hat n d))).card
      ≤ ((n - 1) / 2).choose ((n - 1) / 2 / 2) * (5 ^ ((n - 1) / 2) * 10 ^ (n - (n - 1) / 2)) := by
  have hh : 2 * ((n - 1) / 2) + 1 ≤ n := by omega
  have hadd : ∀ (blk : Fin ((n - 1) / 2) → Fin n) (D : Finset (Fin ((n - 1) / 2))) (v : ℕ → ℕ),
      OMA.S n m (v + ∑ i ∈ D, OMA.unit (blk i))
        = OMA.S n m v + ∑ i ∈ D, OMA.S n m (OMA.unit (blk i)) := by
    intro blk D v
    rw [OMA.S_add, OMA.S_sum]
  have hadd' : ∀ (blk : Fin ((n - 1) / 2) → Fin n) (D : Finset (Fin ((n - 1) / 2))) (v : ℕ → ℕ),
      OMA.valr n (v + ∑ i ∈ D, OMA.unit (blk i))
        = OMA.valr n v + ∑ i ∈ D, OMA.valr n (OMA.unit (blk i)) := by
    intro blk D v
    rw [OMA.valr_add, OMA.valr_sum]
  by_cases hmid : OMA.valr n (OMA.unit ((n - 1) / 2)) ≤ OMA.S n m (OMA.unit ((n - 1) / 2))
  · refine OMA.lo n ((n - 1) / 2)
      (fun i => ⟨n - (n - 1) / 2 + (i : ℕ), by have := i.isLt; omega⟩) ?_
      (OMA.S n m) (OMA.valr n) (hadd _) (hadd' _) (Or.inl ?_)
    · intro i i' hii
      have e : n - (n - 1) / 2 + (i : ℕ) = n - (n - 1) / 2 + (i' : ℕ) := congrArg Fin.val hii
      exact Fin.ext (by omega)
    · intro i
      have hi := i.isLt
      show OMA.valr n (OMA.unit (n - (n - 1) / 2 + (i : ℕ)))
        < OMA.S n m (OMA.unit (n - (n - 1) / 2 + (i : ℕ)))
      have h1 : OMA.valr n (OMA.unit (n - (n - 1) / 2 + (i : ℕ)))
          < OMA.valr n (OMA.unit ((n - 1) / 2)) := by
        rw [OMA.valr_unit n _ (by omega), OMA.valr_unit n _ (by omega)]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 := OMA.S_unit_mono n m ((n - 1) / 2) (n - (n - 1) / 2 + (i : ℕ)) (by omega) (by omega)
      omega
  · refine OMA.lo n ((n - 1) / 2) (fun i => ⟨(i : ℕ), by have := i.isLt; omega⟩) ?_
      (OMA.S n m) (OMA.valr n) (hadd _) (hadd' _) (Or.inr ?_)
    · intro i i' hii
      have e : (i : ℕ) = (i' : ℕ) := congrArg (@Fin.val n) hii
      exact Fin.ext e
    · intro i
      have hi := i.isLt
      show OMA.S n m (OMA.unit (i : ℕ)) < OMA.valr n (OMA.unit (i : ℕ))
      have h1 : OMA.valr n (OMA.unit ((n - 1) / 2)) < OMA.valr n (OMA.unit (i : ℕ)) := by
        rw [OMA.valr_unit n _ (by omega), OMA.valr_unit n _ (by omega)]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 := OMA.S_unit_mono n m (i : ℕ) ((n - 1) / 2) (by omega) (by omega)
      omega

/-- At most `4 ^ n` digit vectors have digit sum below `n`. -/
theorem OMA.card_atyp (n : ℕ) :
    (Finset.univ.filter (fun d : Fin n → Fin 10 => ∑ j, ((d j : Fin 10) : ℕ) < n)).card
      ≤ 4 ^ n := by
  have hw : ∑ a : Fin 10, 2 ^ (9 - (a : ℕ)) = 1023 := by decide
  have htot : ∑ d : Fin n → Fin 10, ∏ j, 2 ^ (9 - ((d j : Fin 10) : ℕ)) = 1023 ^ n := by
    have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 10)))
      (fun _ a => 2 ^ (9 - (a : ℕ)))
    rw [Fintype.piFinset_univ] at h
    rw [← h, Finset.prod_congr rfl (fun _ _ => hw), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hweight : ∀ d ∈ Finset.univ.filter (fun d : Fin n → Fin 10 =>
      ∑ j, ((d j : Fin 10) : ℕ) < n), 2 ^ (8 * n) ≤ ∏ j, 2 ^ (9 - ((d j : Fin 10) : ℕ)) := by
    intro d hd
    have hσ := (Finset.mem_filter.mp hd).2
    rw [Finset.prod_pow_eq_pow_sum]
    apply Nat.pow_le_pow_right (by norm_num)
    have hs : ∑ j : Fin n, (9 - ((d j : Fin 10) : ℕ)) + ∑ j : Fin n, ((d j : Fin 10) : ℕ)
        = 9 * n := by
      rw [← Finset.sum_add_distrib]
      have hj : ∀ j : Fin n, 9 - ((d j : Fin 10) : ℕ) + ((d j : Fin 10) : ℕ) = 9 := by
        intro j
        have := (d j).isLt
        omega
      rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_comm]
    omega
  have h1 := Finset.card_nsmul_le_sum _ _ _ hweight
  rw [smul_eq_mul] at h1
  have h2 : ∑ d ∈ Finset.univ.filter (fun d : Fin n → Fin 10 =>
      ∑ j, ((d j : Fin 10) : ℕ) < n), ∏ j, 2 ^ (9 - ((d j : Fin 10) : ℕ)) ≤ 1023 ^ n := by
    rw [← htot]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h3 : (1023 : ℕ) ^ n ≤ 4 ^ n * 2 ^ (8 * n) := by
    have e : (4 : ℕ) ^ n * 2 ^ (8 * n) = 1024 ^ n := by
      rw [pow_mul, ← mul_pow]
      norm_num
    rw [e]
    exact Nat.pow_le_pow_left (by norm_num) n
  exact Nat.le_of_mul_le_mul_right (le_trans h1 (le_trans h2 h3)) (by positivity)

/-- A nondecreasing sequence that doubles every two steps stays in a window of ratio `180` for at
most `16` indices. -/
theorem OMA.range_bound (n : ℕ) (U : ℕ → ℕ) (hmono : ∀ m, U m ≤ U (m + 1))
    (hgrow : ∀ m t, 2 ^ t * U m ≤ U (m + 2 * t)) :
    ∃ m₀, ∀ m, n * U m < 10 ^ n → 10 ^ (n - 1) ≤ 18 * n * U m → m₀ ≤ m ∧ m < m₀ + 16 := by
  classical
  by_cases hex : ∃ m, 10 ^ (n - 1) ≤ 18 * n * U m
  · refine ⟨Nat.find hex, fun m h1 h2 => ⟨Nat.find_min' hex h2, ?_⟩⟩
    by_contra hge
    have hm0 := Nat.find_spec hex
    have hle : U (Nat.find hex + 2 * 8) ≤ U m := monotone_nat_of_le_succ hmono (by omega)
    have hg := hgrow (Nat.find hex) 8
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso
        rw [h0] at h2
        simp at h2
      · exact h0
    have e : 10 ^ n = 10 * 10 ^ (n - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ, mul_comm]
    have hP : 1 ≤ 10 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have h256 : 256 * U (Nat.find hex) ≤ U m := by
      have e2 : (2 : ℕ) ^ 8 = 256 := by norm_num
      rw [e2] at hg
      exact le_trans hg hle
    have h3 : 256 * (n * U (Nat.find hex)) ≤ n * U m := by
      calc 256 * (n * U (Nat.find hex)) = n * (256 * U (Nat.find hex)) := by ring
        _ ≤ n * U m := Nat.mul_le_mul_left n h256
    have h4 : 18 * n * U (Nat.find hex) = 18 * (n * U (Nat.find hex)) := by ring
    rw [h4] at hm0
    rw [e] at h1
    omega
  · exact ⟨0, fun m _ h2 => absurd ⟨m, h2⟩ hex⟩

/-- The index of a solution with digit sum at least `n` is confined by `ω_0`. -/
theorem OMA.index_bounds (n : ℕ) (d : Fin n → Fin 10) (m : ℕ)
    (hm : OMA.S n m (OMA.hat n d) = OMA.valr n (OMA.hat n d))
    (hσ : n ≤ ∑ j, ((d j : Fin 10) : ℕ))
    (hval : 10 ^ (n - 1) ≤ OMA.valr n (OMA.hat n d)) :
    n * OMA.S n m (OMA.unit 0) < 10 ^ n ∧ 10 ^ (n - 1) ≤ 18 * n * OMA.S n m (OMA.unit 0) := by
  have hexp := OMA.S_expand n m (OMA.hat n d) (fun j hj => OMA.hat_ge n d j hj)
  have hsum := OMA.hat_sum n d
  have hlt := OMA.valr_lt n (OMA.hat n d) (OMA.hat_le n d)
  have hlow : (∑ j ∈ Finset.range n, OMA.hat n d j) * OMA.S n m (OMA.unit 0)
      ≤ OMA.S n m (OMA.hat n d) := by
    rw [hexp, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => Nat.mul_le_mul_left _
      (OMA.S_unit_mono n m 0 j (Nat.zero_le j) (Finset.mem_range.mp hj))
  have hup : OMA.S n m (OMA.hat n d)
      ≤ (∑ j ∈ Finset.range n, OMA.hat n d j) * (2 * OMA.S n m (OMA.unit 0)) := by
    rw [hexp, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => Nat.mul_le_mul_left _
      (OMA.S_unit_le n m j (Finset.mem_range.mp hj))
  have hσ9 : ∑ j ∈ Finset.range n, OMA.hat n d j ≤ 9 * n := by
    calc ∑ j ∈ Finset.range n, OMA.hat n d j ≤ ∑ _j ∈ Finset.range n, 9 :=
          Finset.sum_le_sum fun j _ => OMA.hat_le n d j
      _ = 9 * n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  rw [← hsum] at hσ
  constructor
  · have a1 : n * OMA.S n m (OMA.unit 0)
        ≤ (∑ j ∈ Finset.range n, OMA.hat n d j) * OMA.S n m (OMA.unit 0) :=
      Nat.mul_le_mul_right _ hσ
    exact lt_of_le_of_lt (le_trans a1 (le_trans hlow (le_of_eq hm))) hlt
  · calc 10 ^ (n - 1) ≤ OMA.valr n (OMA.hat n d) := hval
      _ = OMA.S n m (OMA.hat n d) := hm.symm
      _ ≤ (∑ j ∈ Finset.range n, OMA.hat n d j) * (2 * OMA.S n m (OMA.unit 0)) := hup
      _ ≤ 9 * n * (2 * OMA.S n m (OMA.unit 0)) := Nat.mul_le_mul_right _ hσ9
      _ = 18 * n * OMA.S n m (OMA.unit 0) := by ring

/-- The number of digit vectors of length `n` that solve the Keith equation. -/
theorem OMA.card_keith_vec (n : ℕ) (hn : 2 ≤ n) (X : Finset (Fin n → Fin 10))
    (hX : ∀ d ∈ X, (∃ m, OMA.S n m (OMA.hat n d) = OMA.valr n (OMA.hat n d)) ∧
      10 ^ (n - 1) ≤ OMA.valr n (OMA.hat n d)) :
    X.card ≤ 4 ^ n + 16 * (((n - 1) / 2).choose ((n - 1) / 2 / 2)
      * (5 ^ ((n - 1) / 2) * 10 ^ (n - (n - 1) / 2))) := by
  classical
  obtain ⟨m₀, hm₀⟩ := OMA.range_bound n (fun m => OMA.S n m (OMA.unit 0))
    (fun m => OMA.S_le_succ n m (by omega) (OMA.unit 0))
    (fun m t => OMA.S_growth_pow n hn (OMA.unit 0) m t)
  have hcover : X ⊆ (Finset.univ.filter (fun d : Fin n → Fin 10 =>
      ∑ j, ((d j : Fin 10) : ℕ) < n)) ∪
      (Finset.range 16).biUnion (fun t => Finset.univ.filter (fun d : Fin n → Fin 10 =>
        OMA.S n (m₀ + t) (OMA.hat n d) = OMA.valr n (OMA.hat n d))) := by
    intro d hd
    obtain ⟨⟨m, hm⟩, hval⟩ := hX d hd
    by_cases hσ : ∑ j, ((d j : Fin 10) : ℕ) < n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩)
    · refine Finset.mem_union_right _ ?_
      have hidx := OMA.index_bounds n d m hm (by omega) hval
      obtain ⟨h1, h2⟩ := hm₀ m hidx.1 hidx.2
      refine Finset.mem_biUnion.mpr ⟨m - m₀, Finset.mem_range.mpr (by omega),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [show m₀ + (m - m₀) = m by omega]
      exact hm
  refine le_trans (Finset.card_le_card hcover) (le_trans (Finset.card_union_le _ _) ?_)
  refine Nat.add_le_add (OMA.card_atyp n) ?_
  refine le_trans Finset.card_biUnion_le ?_
  exact le_trans (Finset.sum_le_sum (fun t _ => OMA.lo_main n hn (m₀ + t)))
    (le_of_eq (by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]))

/-- The digit vector of `N`. -/
def OMA.dig (n N : ℕ) : Fin n → Fin 10 :=
  fun j => ⟨(Nat.digits 10 N).reverse.getD j 0 % 10, Nat.mod_lt _ (by norm_num)⟩

theorem OMA.hat_dig (n N : ℕ) (hlen : (Nat.digits 10 N).length = n) :
    OMA.hat n (OMA.dig n N) = fun j => (Nat.digits 10 N).reverse.getD j 0 := by
  funext j
  by_cases hj : j < n
  · rw [OMA.hat_lt n _ j hj]
    show (Nat.digits 10 N).reverse.getD j 0 % 10 = (Nat.digits 10 N).reverse.getD j 0
    apply Nat.mod_eq_of_lt
    rw [List.getD_reverse j (by rw [hlen]; exact hj), Nat.getD_digits _ _ (by norm_num)]
    exact Nat.mod_lt _ (by norm_num)
  · rw [OMA.hat_ge n _ j (by omega)]
    symm
    apply List.getD_eq_default
    rw [List.length_reverse, hlen]
    omega

/-- The number of Keith numbers with exactly `n` digits. -/
theorem OMA.card_keith_len (n : ℕ) (hn : 2 ≤ n) (K : Finset ℕ)
    (hK : ∀ N ∈ K, KeithNumber.IsKeithNumber N ∧ (Nat.digits 10 N).length = n) :
    K.card ≤ 4 ^ n + 16 * (((n - 1) / 2).choose ((n - 1) / 2 / 2)
      * (5 ^ ((n - 1) / 2) * 10 ^ (n - (n - 1) / 2))) := by
  classical
  have hvalN : ∀ N ∈ K, OMA.valr n (OMA.hat n (OMA.dig n N)) = N := by
    intro N hN
    obtain ⟨hk, hlen⟩ := hK N hN
    have h1 := (OMA.keith_model N hk).2
    rw [hlen, ← OMA.hat_dig n N hlen] at h1
    exact h1
  have hinj : Set.InjOn (OMA.dig n) (K : Set ℕ) := by
    intro N hN N' hN' hdd
    calc N = OMA.valr n (OMA.hat n (OMA.dig n N)) := (hvalN N (Finset.mem_coe.mp hN)).symm
      _ = OMA.valr n (OMA.hat n (OMA.dig n N')) := by rw [hdd]
      _ = N' := hvalN N' (Finset.mem_coe.mp hN')
  rw [← Finset.card_image_of_injOn hinj]
  apply OMA.card_keith_vec n hn
  intro d hd
  obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hk, hlen⟩ := hK N hN
  obtain ⟨m, hm⟩ := (OMA.keith_model N hk).1
  rw [hlen, ← OMA.hat_dig n N hlen] at hm
  have hval := hvalN N hN
  refine ⟨⟨m, by rw [hm, hval]⟩, ?_⟩
  rw [hval]
  have h10 := Nat.base_pow_length_digits_le 10 N (by norm_num) (by have := hk.2.1; omega)
  rw [hlen] at h10
  have e : 10 ^ n = 10 * 10 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_comm]
  omega

theorem OMA.cb_bound (j : ℕ) : (2 * j + 1) * (Nat.centralBinom j) ^ 2 ≤ 16 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.succ_mul_centralBinom_succ j
    have key : (j + 1) ^ 2 * ((2 * (j + 1) + 1) * (Nat.centralBinom (j + 1)) ^ 2)
        ≤ (j + 1) ^ 2 * 16 ^ (j + 1) := by
      have e : (j + 1) ^ 2 * ((2 * (j + 1) + 1) * (Nat.centralBinom (j + 1)) ^ 2)
          = (2 * (j + 1) + 1) * ((j + 1) * Nat.centralBinom (j + 1)) ^ 2 := by ring
      have e2 : (2 * (j + 1) + 1) * (2 * (2 * j + 1) * Nat.centralBinom j) ^ 2
          = 4 * (2 * j + 3) * (2 * j + 1) * ((2 * j + 1) * (Nat.centralBinom j) ^ 2) := by ring
      have h3 : 4 * (2 * j + 3) * (2 * j + 1) ≤ 16 * (j + 1) ^ 2 := by nlinarith
      rw [e, h, e2]
      calc 4 * (2 * j + 3) * (2 * j + 1) * ((2 * j + 1) * (Nat.centralBinom j) ^ 2)
          ≤ 4 * (2 * j + 3) * (2 * j + 1) * 16 ^ j := Nat.mul_le_mul_left _ ih
        _ ≤ 16 * (j + 1) ^ 2 * 16 ^ j := Nat.mul_le_mul_right _ h3
        _ = (j + 1) ^ 2 * 16 ^ (j + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- The middle binomial coefficient is at most `2 ^ h / √(h + 1)`. -/
theorem OMA.mid_bound (h : ℕ) : (h + 1) * (h.choose (h / 2)) ^ 2 ≤ 4 ^ h := by
  have h16 : (4 : ℕ) ^ 2 = 16 := by norm_num
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' h
  · subst hj
    have h1 := OMA.cb_bound j
    rw [Nat.centralBinom_eq_two_mul_choose] at h1
    have e1 : 2 * j / 2 = j := by omega
    have e2 : (4 : ℕ) ^ (2 * j) = 16 ^ j := by rw [pow_mul, h16]
    rw [e1, e2]
    exact h1
  · subst hj
    have h1 := OMA.cb_bound (j + 1)
    have hcb : Nat.centralBinom (j + 1) = 2 * (2 * j + 1).choose j := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
        Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    have e1 : (2 * j + 1) / 2 = j := by omega
    have e2 : (4 : ℕ) ^ (2 * j + 1) = 4 * 16 ^ j := by rw [pow_succ, pow_mul, h16, mul_comm]
    have e3 : (16 : ℕ) ^ (j + 1) = 16 * 16 ^ j := by ring
    rw [e1, e2]
    rw [hcb, e3] at h1
    nlinarith [h1, Nat.zero_le (((2 * j + 1).choose j) ^ 2)]

theorem OMA.num_a (n : ℕ) : 16 ^ n * n ≤ 100 ^ n := by
  have h0 : n < 2 ^ n := Nat.lt_two_pow_self
  have h1 : n ≤ 6 ^ n := le_trans h0.le (Nat.pow_le_pow_left (by norm_num) n)
  calc 16 ^ n * n ≤ 16 ^ n * 6 ^ n := Nat.mul_le_mul_left _ h1
    _ = (16 * 6) ^ n := (mul_pow 16 6 n).symm
    _ ≤ 100 ^ n := Nat.pow_le_pow_left (by norm_num) n

theorem OMA.num_b (n : ℕ) (hn : 1 ≤ n) :
    (((n - 1) / 2).choose ((n - 1) / 2 / 2) * (5 ^ ((n - 1) / 2) * 10 ^ (n - (n - 1) / 2))) ^ 2 * n
      ≤ 4 * 100 ^ n := by
  have hmid := OMA.mid_bound ((n - 1) / 2)
  obtain ⟨h, hh⟩ : ∃ h, h = (n - 1) / 2 := ⟨_, rfl⟩
  rw [← hh] at hmid ⊢
  obtain ⟨C, hC⟩ : ∃ C, C = h.choose (h / 2) := ⟨_, rfl⟩
  rw [← hC] at hmid ⊢
  have hle : h ≤ n := by omega
  have hn2 : n ≤ 2 * (h + 1) := by omega
  have e1 : (C * (5 ^ h * 10 ^ (n - h))) ^ 2 = C ^ 2 * (25 ^ h * 100 ^ (n - h)) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_mul', pow_mul']
    norm_num
  have e2 : (4 : ℕ) ^ h * (25 ^ h * 100 ^ (n - h)) = 100 ^ n := by
    calc (4 : ℕ) ^ h * (25 ^ h * 100 ^ (n - h)) = (4 * 25) ^ h * 100 ^ (n - h) := by
          rw [mul_pow, mul_assoc]
      _ = 100 ^ h * 100 ^ (n - h) := by norm_num
      _ = 100 ^ (h + (n - h)) := (pow_add 100 h (n - h)).symm
      _ = 100 ^ n := by rw [Nat.add_sub_cancel' hle]
  rw [e1]
  calc C ^ 2 * (25 ^ h * 100 ^ (n - h)) * n
      ≤ C ^ 2 * (25 ^ h * 100 ^ (n - h)) * (2 * (h + 1)) := Nat.mul_le_mul_left _ hn2
    _ = 2 * ((h + 1) * C ^ 2 * (25 ^ h * 100 ^ (n - h))) := by ring
    _ ≤ 2 * (4 ^ h * (25 ^ h * 100 ^ (n - h))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hmid)
    _ = 2 * 100 ^ n := by rw [e2]
    _ ≤ 4 * 100 ^ n := Nat.mul_le_mul_right _ (by norm_num)

theorem OMA.per_len_real (n : ℕ) (hn : 2 ≤ n) :
    ((4 ^ n + 16 * (((n - 1) / 2).choose ((n - 1) / 2 / 2)
      * (5 ^ ((n - 1) / 2) * 10 ^ (n - (n - 1) / 2))) : ℕ) : ℝ)
      ≤ 33 * ((10 : ℝ) ^ n / Real.sqrt n) := by
  have ha := OMA.num_a n
  have hb := OMA.num_b n (by omega)
  generalize ((n - 1) / 2).choose ((n - 1) / 2 / 2)
    * (5 ^ ((n - 1) / 2) * 10 ^ (n - (n - 1) / 2)) = LO at hb ⊢
  have hr : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hA : (4 : ℝ) ^ n * Real.sqrt n ≤ 10 ^ n := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
    have h1 : ((4 : ℝ) ^ n * Real.sqrt n) ^ 2 = (16 : ℝ) ^ n * n := by
      rw [mul_pow, hsq, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    have h2 : ((10 : ℝ) ^ n) ^ 2 = (100 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    rw [h1, h2]
    exact_mod_cast ha
  have hB : (LO : ℝ) * Real.sqrt n ≤ 2 * 10 ^ n := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
    have h1 : ((LO : ℝ) * Real.sqrt n) ^ 2 = (LO : ℝ) ^ 2 * n := by
      rw [mul_pow, hsq]
    have h2 : (2 * (10 : ℝ) ^ n) ^ 2 = 4 * (100 : ℝ) ^ n := by
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    rw [h1, h2]
    exact_mod_cast hb
  push_cast
  rw [← mul_div_assoc, le_div_iff₀ hr]
  nlinarith [hA, hB]

theorem OMA.geo (L : ℕ) (hL : 1 ≤ L) :
    ∑ n ∈ Finset.Icc 1 L, (10 : ℝ) ^ n / Real.sqrt n ≤ 2 * ((10 : ℝ) ^ L / Real.sqrt L) := by
  induction L, hL using Nat.le_induction with
  | base => norm_num [Finset.Icc_self]
  | succ L hL ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpos : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L))
    have hpos' : (0 : ℝ) < Real.sqrt ((L + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt ((L + 1 : ℕ) : ℝ) ≤ 5 * Real.sqrt L := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg L)]
      push_cast
      have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
      linarith
    have hstep : 2 * ((10 : ℝ) ^ L / Real.sqrt L)
        ≤ (10 : ℝ) ^ (L + 1) / Real.sqrt ((L + 1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hpos hpos', pow_succ]
      have h10 : (0 : ℝ) < 10 ^ L := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq h10.le]
    linarith

theorem OMA.solution : type_of% @KeithNumber.klazar_luca_keith_counting_bound := by
  classical
  refine ⟨1980, by norm_num, fun x hx => ?_⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Finset ℕ,
      K = (Finset.Icc 10 x).filter (fun N => KeithNumber.IsKeithNumber N) := ⟨_, rfl⟩
  have hmemK : ∀ N, N ∈ K ↔ (10 ≤ N ∧ N ≤ x) ∧ KeithNumber.IsKeithNumber N := by
    intro N
    rw [hKdef, Finset.mem_filter, Finset.mem_Icc]
  have hset : {N : ℕ | N ≤ x ∧ KeithNumber.IsKeithNumber N} = (K : Set ℕ) := by
    ext N
    rw [Finset.mem_coe, hmemK]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2.2.1, h1⟩, h2⟩
    · rintro ⟨⟨_, h1⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [hset, Set.ncard_coe_finset]
  obtain ⟨L, hLdef⟩ : ∃ L, L = (Nat.digits 10 x).length := ⟨_, rfl⟩
  have hxL : x < 10 ^ L := by
    rw [hLdef]
    exact Nat.lt_base_pow_length_digits (by norm_num)
  have hL1 : 1 ≤ L := by
    by_contra h
    have h0 : L = 0 := by omega
    rw [h0] at hxL
    omega
  have hlenN : ∀ N ∈ K, (Nat.digits 10 N).length ∈ Finset.Icc 2 L := by
    intro N hN
    obtain ⟨⟨h10, hNx⟩, -⟩ := (hmemK N).mp hN
    rw [Finset.mem_Icc]
    constructor
    · by_contra h
      have h1 : (Nat.digits 10 N).length ≤ 1 := by omega
      have h2 := Nat.lt_base_pow_length_digits (b := 10) (m := N) (by norm_num)
      have h3 : 10 ^ (Nat.digits 10 N).length ≤ 10 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      omega
    · rw [hLdef]
      exact Nat.le_length_digits_le 10 N x hNx
  have hcard : K.card = ∑ n ∈ Finset.Icc 2 L,
      (K.filter (fun N => (Nat.digits 10 N).length = n)).card :=
    Finset.card_eq_sum_card_fiberwise hlenN
  have hper : ∀ n ∈ Finset.Icc 2 L,
      ((K.filter (fun N => (Nat.digits 10 N).length = n)).card : ℝ)
        ≤ 33 * ((10 : ℝ) ^ n / Real.sqrt n) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have h1 := OMA.card_keith_len n hn2 (K.filter (fun N => (Nat.digits 10 N).length = n))
      (fun N hN => ⟨((hmemK N).mp (Finset.mem_filter.mp hN).1).2, (Finset.mem_filter.mp hN).2⟩)
    exact le_trans (Nat.cast_le.mpr h1) (OMA.per_len_real n hn2)
  have hLpos : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr (by exact_mod_cast hL1)
  have hcount : (K.card : ℝ) ≤ 66 * ((10 : ℝ) ^ L / Real.sqrt L) := by
    rw [hcard]
    push_cast
    calc ∑ n ∈ Finset.Icc 2 L, ((K.filter (fun N => (Nat.digits 10 N).length = n)).card : ℝ)
        ≤ ∑ n ∈ Finset.Icc 2 L, 33 * ((10 : ℝ) ^ n / Real.sqrt n) := Finset.sum_le_sum hper
      _ ≤ ∑ n ∈ Finset.Icc 1 L, 33 * ((10 : ℝ) ^ n / Real.sqrt n) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (by norm_num))
            (fun n _ _ => by positivity)
      _ = 33 * ∑ n ∈ Finset.Icc 1 L, (10 : ℝ) ^ n / Real.sqrt n := by rw [Finset.mul_sum]
      _ ≤ 33 * (2 * ((10 : ℝ) ^ L / Real.sqrt L)) :=
          mul_le_mul_of_nonneg_left (OMA.geo L hL1) (by norm_num)
      _ = 66 * ((10 : ℝ) ^ L / Real.sqrt L) := by ring
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hspos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have h10L : (10 : ℝ) ^ L ≤ 10 * x := by
    have h := Nat.base_pow_length_digits_le 10 x (by norm_num) (by omega)
    rw [← hLdef] at h
    exact_mod_cast h
  have hlogle : Real.log (x : ℝ) ≤ 9 * L := by
    have hxlt : (x : ℝ) ≤ (10 : ℝ) ^ L := by exact_mod_cast hxL.le
    have h1 := Real.log_le_log hxpos hxlt
    rw [Real.log_pow] at h1
    have h2 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)
      linarith
    have h3 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have hs3 : Real.sqrt (Real.log (x : ℝ)) ≤ 3 * Real.sqrt L := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg L)]
    linarith
  have hfin : 66 * ((10 : ℝ) ^ L / Real.sqrt L)
      ≤ 1980 * ((x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
    have e1 : (10 : ℝ) ^ L / Real.sqrt L ≤ 10 * x / Real.sqrt L :=
      div_le_div_of_nonneg_right h10L hLpos.le
    have e2 : 10 * (x : ℝ) / Real.sqrt L ≤ 30 * ((x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
      rw [div_le_iff₀ hLpos]
      have h1 : (x : ℝ) / Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ)) = x :=
        div_mul_cancel₀ _ hspos.ne'
      have h2 : 0 ≤ (x : ℝ) / Real.sqrt (Real.log (x : ℝ)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hs3 h2]
    linarith
  exact le_trans hcount hfin
