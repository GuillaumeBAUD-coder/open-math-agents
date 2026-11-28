import OMAStatements.S_oeis_a277216

namespace OMA.A277216

-- Read the decimal digits from left to right. The four exponents factor their product.
structure Prefix where
  value : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def start : Prefix := ⟨0, 0, 0, 0, 0⟩

def product (s : Prefix) : ℕ := 2^s.a * 3^s.b * 5^s.c * 7^s.d

def push (s : Prefix) (x : ℕ) : Prefix :=
  ⟨10 * s.value + x,
   s.a + (if x = 8 then 3 else if x = 4 then 2 else if x = 2 ∨ x = 6 then 1 else 0),
   s.b + (if x = 9 then 2 else if x = 3 ∨ x = 6 then 1 else 0),
   s.c + (if x = 5 then 1 else 0), s.d + (if x = 7 then 1 else 0)⟩

-- Clearing the four prime-power denominators multiplies the divisor sum by 48.
def scaledSigma (s : Prefix) : ℕ :=
  (2 * 2^s.a - 1) * (3 * 3^s.b - 1) * (5 * 5^s.c - 1) * (7 * 7^s.d - 1)

lemma product_push (s : Prefix) (x : ℕ) (h₁ : 1 ≤ x) (h₉ : x ≤ 9) :
    product (push s x) = product s * x := by
  interval_cases x <;> simp [push, product, pow_add] <;> ring

lemma sigma_factor (p e : ℕ) (hp : p.Prime) :
    (p - 1) * ArithmeticFunction.sigma 1 (p^e) = p * p^e - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]
  have h := geom_sum_mul_of_one_le (R := ℕ) hp.one_le (e+1)
  rw [Nat.geomSum_eq hp.two_le] at h
  simpa [mul_comm, pow_succ] using h

lemma scaled_correct (s : Prefix) : 48 * ArithmeticFunction.sigma 1 (product s) = scaledSigma s := by
  let σ := ArithmeticFunction.sigma 1
  have mul {x y : ℕ} (h : Nat.Coprime x y) : σ (x*y) = σ x * σ y :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h
  have cop {p q i j : ℕ} (h : Nat.Coprime p q) : Nat.Coprime (p^i) (q^j) :=
    (h.pow_left i).pow_right j
  have h23 : Nat.Coprime (2^s.a) (3^s.b) := cop (by decide : Nat.Coprime 2 3)
  have h5 : Nat.Coprime (2^s.a * 3^s.b) (5^s.c) :=
    (cop (by decide : Nat.Coprime 2 5)).mul_left (cop (by decide : Nat.Coprime 3 5))
  have h7 : Nat.Coprime (2^s.a * 3^s.b * 5^s.c) (7^s.d) :=
    ((cop (by decide : Nat.Coprime 2 7)).mul_left (cop (by decide : Nat.Coprime 3 7))).mul_left
      (cop (by decide : Nat.Coprime 5 7))
  change 48 * σ (2^s.a * 3^s.b * 5^s.c * 7^s.d) = _
  rw [mul h7, mul h5, mul h23]
  dsimp [σ, scaledSigma]
  rw [← sigma_factor 2 s.a (by decide), ← sigma_factor 3 s.b (by decide),
      ← sigma_factor 5 s.c (by decide), ← sigma_factor 7 s.d (by decide)]
  norm_num
  ring

-- The product of 2/1, 3/2, 5/4 and 7/6 is 35/8.
lemma bound (s : Prefix) : 8 * ArithmeticFunction.sigma 1 (product s) ≤ 35 * product s := by
  have h : scaledSigma s ≤ (2*2^s.a) * (3*3^s.b) * (5*5^s.c) * (7*7^s.d) := by
    unfold scaledSigma
    gcongr <;> omega
  rw [← scaled_correct] at h
  change _ ≤ 35 * (2^s.a * 3^s.b * 5^s.c * 7^s.d)
  nlinarith only [h]

def allowed (xs : List ℕ) : Prop := ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 9

lemma run_product (xs : List ℕ) (hs : allowed xs) (s : Prefix) :
    product (xs.foldl push s) = product s * xs.prod := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    have hx := hs x (by simp)
    have hxs : allowed xs := fun y hy => hs y (by simp [hy])
    simp [List.foldl_cons, ih hxs, product_push s x hx.1 hx.2, Nat.mul_assoc]

lemma run_value (xs : List ℕ) (s : Prefix) :
    (xs.reverse.foldl push s).value = Nat.ofDigits 10 xs + 10^xs.length * s.value := by
  induction xs with
  | nil => simp [Nat.ofDigits]
  | cons x xs ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_cons, Nat.ofDigits_cons, pow_succ]
    change 10 * (xs.reverse.foldl push s).value + x = _
    rw [ih]
    ring

-- Appending a digit multiplies the value by at least ten and the digit product by at most nine.
lemma branch_dead (xs : List ℕ) (hs : allowed xs) (s : Prefix)
    (h : 35 * product s < 8 * s.value) :
    35 * product (xs.foldl push s) < 8 * (xs.foldl push s).value := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
    have hx := hs x (by simp)
    apply ih (fun y hy => hs y (by simp [hy]))
    rw [product_push _ _ hx.1 hx.2]
    change 35 * (product s * x) < 8 * (10 * s.value + x)
    have hxle := Nat.mul_le_mul_left (product s) (show x ≤ 10 by omega)
    omega

-- A rejected prefix excludes all of its descendants. At depth zero the inequality must reject it.
def audit : ℕ → Prefix → Bool
  | 0, s => decide (35 * product s < 8 * s.value)
  | fuel + 1, s =>
    if 35 * product s < 8 * s.value then true else
      decide (48 * s.value ≠ scaledSigma s ∨ product s = 1 ∨ product s = 210) &&
      ([1,2,3,4,5,6,7,8,9] : List ℕ).all (fun x => audit fuel (push s x))

lemma audit_sound (fuel : ℕ) (s : Prefix) (h : audit fuel s = true)
    (xs : List ℕ) (hs : allowed xs) :
    let t := xs.foldl push s
    8*t.value ≤ 35*product t → 48*t.value = scaledSigma t → product t = 1 ∨ product t = 210 := by
  dsimp only
  intro hb he
  induction fuel generalizing s xs with
  | zero =>
    have hd : 35 * product s < 8 * s.value := of_decide_eq_true h
    exact False.elim ((Nat.not_lt_of_ge hb) (branch_dead xs hs s hd))
  | succ fuel ih =>
    by_cases hd : 35 * product s < 8 * s.value
    · exact False.elim ((Nat.not_lt_of_ge hb) (branch_dead xs hs s hd))
    simp only [audit, if_neg hd, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    cases xs with
    | nil => exact h.1.resolve_left (not_not_intro he)
    | cons x xs =>
      have hx := hs x (by simp)
      obtain ⟨hx1, hx9⟩ := hx
      have hm : x ∈ ([1,2,3,4,5,6,7,8,9] : List ℕ) := by interval_cases x <;> decide
      exact ih (push s x) (h.2 x hm) xs (fun y hy => hs y (by simp [hy])) hb he

-- The remaining tree is small enough for the kernel to check directly.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
lemma checked : audit 15 start = true := by decide +kernel

theorem fixed (n : ℕ) (hn : 0 < n) :
    (Nat.digits 10 (ArithmeticFunction.sigma 1 n)).prod = n ↔ n = 1 ∨ n = 210 := by
  constructor
  · intro h
    let v := ArithmeticFunction.sigma 1 n
    let ds := Nat.digits 10 v
    have hd : ds.prod = n := h
    have ha : allowed ds.reverse := by
      intro x hx
      have hmem : x ∈ ds := List.mem_reverse.mp hx
      have ht := Nat.digits_lt_base (by decide : 1 < 10) hmem
      have hz : x ≠ 0 := by
        rintro rfl
        have he : ds.prod = 0 := List.prod_eq_zero hmem
        omega
      omega
    let t := ds.reverse.foldl push start
    have hp : product t = n := by
      change product (ds.reverse.foldl push start) = n
      rw [run_product _ ha, List.prod_reverse, show product start = 1 by decide, one_mul, hd]
    have hv : t.value = v := by
      change (ds.reverse.foldl push start).value = v
      rw [run_value, show start.value = 0 by rfl, Nat.mul_zero, Nat.add_zero]
      exact Nat.ofDigits_digits 10 v
    have hr := audit_sound 15 start checked ds.reverse ha
    change (8*t.value ≤ 35*product t) → (48*t.value = scaledSigma t) → _ at hr
    have hbound := bound t
    have hscale := scaled_correct t
    rw [hp] at hbound hscale
    have hb' : 8*t.value ≤ 35*product t := by rw [hv, hp]; exact hbound
    have he' : 48*t.value = scaledSigma t := by rw [hv]; exact hscale
    rw [← hp]
    exact hr hb' he'
  · rintro (rfl | rfl) <;> decide +kernel

end OMA.A277216

theorem OMA.solution : type_of% @OMA.S_oeis_a277216.main := OMA.A277216.fixed
