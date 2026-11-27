import FormalConjectures.ErdosProblems.«686»

-- Problem: Erdős Problem 686 — four three
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/686.lean:93 (declaration Erdos686.erdos_686.variants.four_three)
-- Credit: @sebastianbachmaier (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E686

structure T where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq

namespace T

theorem ext3 {x y : T} (h1 : x.a = y.a) (h2 : x.b = y.b) (h3 : x.c = y.c) : x = y := by
  cases x; cases y; simp_all

instance : Zero T := ⟨⟨0, 0, 0⟩⟩
instance : One T := ⟨⟨1, 0, 0⟩⟩
instance : Add T := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg T := ⟨fun x => ⟨-x.a, -x.b, -x.c⟩⟩
instance : Sub T := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c⟩⟩
instance : Mul T := ⟨fun x y => ⟨x.a * y.a + 2 * (x.b * y.c + x.c * y.b),
  x.a * y.b + x.b * y.a + 2 * (x.c * y.c), x.a * y.c + x.b * y.b + x.c * y.a⟩⟩

@[simp] lemma zero_a : (0 : T).a = 0 := rfl
@[simp] lemma zero_b : (0 : T).b = 0 := rfl
@[simp] lemma zero_c : (0 : T).c = 0 := rfl
@[simp] lemma one_a : (1 : T).a = 1 := rfl
@[simp] lemma one_b : (1 : T).b = 0 := rfl
@[simp] lemma one_c : (1 : T).c = 0 := rfl
@[simp] lemma add_a (x y : T) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : T) : (x + y).b = x.b + y.b := rfl
@[simp] lemma add_c (x y : T) : (x + y).c = x.c + y.c := rfl
@[simp] lemma neg_a (x : T) : (-x).a = -x.a := rfl
@[simp] lemma neg_b (x : T) : (-x).b = -x.b := rfl
@[simp] lemma neg_c (x : T) : (-x).c = -x.c := rfl
@[simp] lemma sub_a (x y : T) : (x - y).a = x.a - y.a := rfl
@[simp] lemma sub_b (x y : T) : (x - y).b = x.b - y.b := rfl
@[simp] lemma sub_c (x y : T) : (x - y).c = x.c - y.c := rfl
@[simp] lemma mul_a (x y : T) : (x * y).a = x.a * y.a + 2 * (x.b * y.c + x.c * y.b) := rfl
@[simp] lemma mul_b (x y : T) : (x * y).b = x.a * y.b + x.b * y.a + 2 * (x.c * y.c) := rfl
@[simp] lemma mul_c (x y : T) : (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a := rfl

instance : SMul ℕ T := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c⟩⟩
instance : SMul ℤ T := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c⟩⟩
@[simp] lemma nsmul_a' (n : ℕ) (x : T) : (n • x).a = n * x.a := rfl
@[simp] lemma nsmul_b' (n : ℕ) (x : T) : (n • x).b = n * x.b := rfl
@[simp] lemma nsmul_c' (n : ℕ) (x : T) : (n • x).c = n * x.c := rfl
@[simp] lemma zsmul_a' (n : ℤ) (x : T) : (n • x).a = n * x.a := rfl
@[simp] lemma zsmul_b' (n : ℤ) (x : T) : (n • x).b = n * x.b := rfl
@[simp] lemma zsmul_c' (n : ℤ) (x : T) : (n • x).c = n * x.c := rfl

instance : NatCast T := ⟨fun n => ⟨n, 0, 0⟩⟩
instance : IntCast T := ⟨fun n => ⟨n, 0, 0⟩⟩
@[simp] lemma natCast_a (n : ℕ) : (n : T).a = n := rfl
@[simp] lemma natCast_b (n : ℕ) : (n : T).b = 0 := rfl
@[simp] lemma natCast_c (n : ℕ) : (n : T).c = 0 := rfl
@[simp] lemma intCast_a (n : ℤ) : (n : T).a = n := rfl
@[simp] lemma intCast_b (n : ℤ) : (n : T).b = 0 := rfl
@[simp] lemma intCast_c (n : ℤ) : (n : T).c = 0 := rfl

instance : CommRing T where
  add_assoc x y z := by apply ext3 <;> simp <;> ring
  zero_add x := by apply ext3 <;> simp
  add_zero x := by apply ext3 <;> simp
  nsmul n x := n • x
  nsmul_zero x := by apply ext3 <;> simp
  nsmul_succ n x := by apply ext3 <;> simp <;> ring
  zsmul n x := n • x
  zsmul_zero' x := by apply ext3 <;> simp
  zsmul_succ' n x := by apply ext3 <;> simp <;> ring
  zsmul_neg' n x := by apply ext3 <;> simp [Int.negSucc_eq] <;> ring
  sub_eq_add_neg x y := by apply ext3 <;> simp <;> ring
  neg_add_cancel x := by apply ext3 <;> simp
  add_comm x y := by apply ext3 <;> simp <;> ring
  left_distrib x y z := by apply ext3 <;> simp <;> ring
  right_distrib x y z := by apply ext3 <;> simp <;> ring
  zero_mul x := by apply ext3 <;> simp
  mul_zero x := by apply ext3 <;> simp
  mul_assoc x y z := by apply ext3 <;> simp <;> ring
  one_mul x := by apply ext3 <;> simp
  mul_one x := by apply ext3 <;> simp
  natCast_zero := by apply ext3 <;> simp
  natCast_succ n := by apply ext3 <;> simp
  intCast_ofNat n := by apply ext3 <;> simp
  intCast_negSucc n := by apply ext3 <;> simp [Int.negSucc_eq]
  mul_comm x y := by apply ext3 <;> simp <;> ring

end T

open T

def ε : T := ⟨1, 1, 1⟩
def εi : T := ⟨-1, 1, 0⟩

def tp (x : T) : ℕ → T
  | 0 => ⟨1, 0, 0⟩
  | n + 1 => tp x n * x

lemma tp_eq (x : T) (n : ℕ) : tp x n = x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tp, ih, pow_succ]

def Ec : ℤ → T
  | Int.ofNat n => tp ε n
  | Int.negSucc n => tp εi (n + 1)

def Nm (x : T) : ℤ := x.a * x.a * x.a + 2 * (x.b * x.b * x.b) + 4 * (x.c * x.c * x.c)
  - 6 * (x.a * x.b * x.c)

def params : ℕ → ℕ × ℕ
  | 1 => (3, 3) | 4 => (3, 3) | 5 => (3, 3) | 20 => (3, 3)
  | 3 => (5, 8) | 15 => (5, 8) | 60 => (11, 40)
  | 2 => (2, 4) | 6 => (2, 4) | 10 => (2, 4) | 30 => (2, 4)
  | 12 => (9, 9) | _ => (3, 3)

def gam (m : ℤ) (e : T) : T := ⟨(e.a - 1) / m, e.b / m, e.c / m⟩

def lift (m : ℤ) (g : T) : T := ⟨1 + m * g.a, m * g.b, m * g.c⟩

def finalOK (β : T) : Bool :=
  decide (|β.a + 4 * β.c| ≤ 60) && (decide (β.a < 1) || decide (-β.c < 1) ||
    (List.range 61).all fun g => !(decide ((g : ℤ) * g * Nm β = β.a + 4 * β.c) &&
      decide (3 ≤ (g : ℤ) * (β.a + β.c))))

def classOK (h : T) : Bool :=
  let N := Nm h
  let m := (params N.natAbs).1
  let K := (params N.natAbs).2
  let g1 := gam m (tp ε K)
  let g2 := gam m (tp εi K)
  decide (0 < K) && decide (2 ≤ m) && decide (tp ε K = lift m g1) &&
  decide (tp εi K = lift m g2) &&
  (List.range K).all fun r =>
    let v := h * tp ε r
    decide (v.b % m ≠ 0) ||
    (List.range m).all (fun g => decide (((g : ℤ) * g * N - (v.a + 4 * v.c)) % m ≠ 0)) ||
    decide (Int.gcd (Int.gcd v.a v.c) m ≠ 1) ||
    (decide (m = 3 ∨ m = 5 ∨ m = 11) && [(r : ℤ) + K, r, r - K, r - 2 * K].any fun r0 =>
      let β := h * Ec r0
      decide (β.b = 0) && decide ((β * g1).b % m ≠ 0) && decide ((β * g2).b % m ≠ 0) &&
        finalOK β)

def boxOK : Bool :=
  (List.range 13).all fun i => (List.range 11).all fun j => (List.range 9).all fun k =>
    let h : T := ⟨(i : ℤ) - 6, (j : ℤ) - 5, (k : ℤ) - 4⟩
    decide (Nm h = 0) || decide (60 % Nm h ≠ 0) || classOK h

theorem boxOK_true : boxOK = true := by decide +kernel


section Skolem
variable {R : Type*} [CommRing R]

lemma cong_pow (m γ : R) (t : ℕ) : ∃ ρ, (1 + m * γ) ^ t = 1 + m * ρ := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨ρ + γ + m * ρ * γ, by rw [pow_succ, hρ]; ring⟩

lemma powB (q δ : R) (j u : ℕ) :
    ∃ σ, (1 + q ^ (j + 1) * δ) ^ u = 1 + q ^ (j + 1) * (u * δ + q * σ) := by
  induction u with
  | zero => exact ⟨0, by simp⟩
  | succ u ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨σ + q ^ j * (u * δ + q * σ) * δ, ?_⟩
    rw [pow_succ, hσ]; push_cast; ring

lemma powA (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (j : ℕ) (δ : R) :
    ∃ δ', (1 + (p : R) ^ (j + 1) * δ) ^ p = 1 + (p : R) ^ (j + 2) * (δ + p * δ') := by
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  set x := (p : R) ^ (j + 1) * δ with hx
  have e1 : (1 + x) ^ p = ∑ i ∈ Finset.range (p + 1), x ^ i * (p.choose i : R) := by
    rw [add_comm, add_pow]; simp only [one_pow, mul_one]
  have e2 : p + 1 = p' + 1 + 1 + 1 := by omega
  rw [e2, Finset.sum_range_succ', Finset.sum_range_succ'] at e1
  have hdvd : (p : R) ^ (j + 3) ∣
      ∑ i ∈ Finset.range (p' + 1), x ^ (i + 1 + 1) * (p.choose (i + 1 + 1) : R) := by
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hx, mul_pow, ← pow_mul]
    rcases Nat.lt_or_ge i p' with h | h
    · obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := i + 1 + 1) (by omega) (by omega)
      rw [hc]
      refine (pow_dvd_pow (p : R) (show j + 3 ≤ (j + 1) * (i + 1 + 1) + 1 by nlinarith)).trans
        ⟨δ ^ (i + 1 + 1) * c, ?_⟩
      push_cast; ring
    · have hi' : i + 1 + 1 = p := by omega
      rw [hi', Nat.choose_self]
      refine (pow_dvd_pow (p : R) (show j + 3 ≤ (j + 1) * p by nlinarith)).trans
        ⟨δ ^ p, ?_⟩
      push_cast; ring
  obtain ⟨S, hS⟩ := hdvd
  refine ⟨S, ?_⟩
  rw [e1, hS]
  simp only [zero_add, pow_one, pow_zero, Nat.choose_one_right, Nat.choose_zero_right,
    Nat.cast_one, mul_one, hx]
  ring

lemma skPow (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (γ : R) (v : ℕ) :
    ∃ ρ, (1 + (p : R) * γ) ^ (p ^ v) = 1 + (p : R) ^ (v + 1) * (γ + p * ρ) := by
  induction v with
  | zero => exact ⟨0, by simp⟩
  | succ v ih =>
    obtain ⟨ρ, hρ⟩ := ih
    obtain ⟨δ', hδ'⟩ := powA p hp hp3 v (γ + p * ρ)
    exact ⟨ρ + δ', by rw [pow_succ, pow_mul, hρ, hδ']; ring⟩

end Skolem

lemma ncm_b (n : ℕ) (x : T) : ((n : T) * x).b = n * x.b := by simp
lemma ncm_a (n : ℕ) (x : T) : ((n : T) * x).a = n * x.a := by simp
lemma ncm_c (n : ℕ) (x : T) : ((n : T) * x).c = n * x.c := by simp

lemma skolem (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (γ β : T) (hβ : β.b = 0)
    (hl : (β * γ).b % p ≠ 0) (t : ℕ) (h : (β * (1 + (p : T) * γ) ^ t).b = 0) : t = 0 := by
  by_contra ht
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht p hp.ne_one
  obtain ⟨ρ, hρ⟩ := skPow p hp hp3 γ v
  obtain ⟨σ, hσ⟩ := powB (p : T) (γ + p * ρ) v u
  rw [pow_mul, hρ, hσ] at h
  have e : β * (1 + (p : T) ^ (v + 1) * (u * (γ + p * ρ) + p * σ)) =
      β + ((p ^ (v + 1) : ℕ) : T) * ((u : T) * (β * γ) + (p : T) * (β * ((u : T) * ρ + σ))) := by
    push_cast; ring
  rw [e] at h
  generalize β * γ = w1 at h hl
  generalize β * ((u : T) * ρ + σ) = w2 at h
  rw [add_b, ncm_b, add_b, ncm_b, ncm_b, hβ, zero_add] at h
  have hpv : ((p ^ (v + 1) : ℕ) : ℤ) ≠ 0 := by positivity
  have h2 : (u : ℤ) * w1.b + p * w2.b = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hpv
    · exact h
  have h3 : (p : ℤ) ∣ (u : ℤ) * w1.b := ⟨-w2.b, by linarith⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h3 with h4 | h4
  · exact hu (Int.natCast_dvd_natCast.mp h4)
  · exact hl (Int.emod_eq_zero_of_dvd h4)

/-! Units -/

lemma ε_mul_εi : ε * εi = 1 := by decide
lemma εi_mul_ε : εi * ε = 1 := by decide

def εU : Tˣ := ⟨ε, εi, ε_mul_εi, εi_mul_ε⟩

def E (n : ℤ) : T := ((εU ^ n : Tˣ) : T)

lemma E_add (m n : ℤ) : E (m + n) = E m * E n := by
  simp [E, zpow_add]

lemma E_zero : E 0 = 1 := by simp [E]

lemma E_nat (k : ℕ) : E k = ε ^ k := by
  simp [E, εU]

lemma E_negSucc (k : ℕ) : E (Int.negSucc k) = εi ^ (k + 1) := by
  rw [E, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
  rfl

lemma E_eq_Ec (n : ℤ) : E n = Ec n := by
  cases n with
  | ofNat k => rw [Ec, tp_eq]; exact E_nat k
  | negSucc k => rw [Ec, tp_eq]; exact E_negSucc k


lemma Nm_mul (x y : T) : Nm (x * y) = Nm x * Nm y := by
  simp only [Nm, T.mul_a, T.mul_b, T.mul_c]; ring

def NmHom : T →* ℤ where
  toFun := Nm
  map_one' := by decide
  map_mul' := Nm_mul

lemma Nm_E (n : ℤ) : Nm (E n) = 1 := by
  cases n with
  | ofNat k =>
    have := E_nat k
    simp only [Int.ofNat_eq_natCast] at *
    rw [this]
    change NmHom (ε ^ k) = 1
    rw [map_pow]; simp [NmHom, Nm, ε]
  | negSucc k =>
    rw [E_negSucc]
    change NmHom (εi ^ (k + 1)) = 1
    rw [map_pow]; simp [NmHom, Nm, εi]

lemma E_mul (K : ℕ) (q : ℤ) :
    (E (K * q) = (tp ε K) ^ q.toNat ∧ 0 ≤ q) ∨ (E (K * q) = (tp εi K) ^ (-q).toNat ∧ q < 0) := by
  rcases le_or_gt 0 q with hq | hq
  · left
    refine ⟨?_, hq⟩
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [show ((K : ℤ) * (k : ℤ)) = ((K * k : ℕ) : ℤ) by push_cast; ring, E_nat, tp_eq,
      Int.toNat_natCast, pow_mul]
  · right
    refine ⟨?_, hq⟩
    obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hq.le
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    subst hk
    have : ((K : ℤ) * -((k' + 1 : ℕ) : ℤ)) = -((K * (k' + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [this, tp_eq, neg_neg, Int.toNat_natCast, ← pow_mul]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp [E_zero]
    · obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
      rw [show ((K' + 1) * (k' + 1) : ℕ) = (K' * (k' + 1) + k') + 1 by ring]
      rw [show -(((K' * (k' + 1) + k') + 1 : ℕ) : ℤ) = Int.negSucc (K' * (k' + 1) + k') by
        rfl]
      rw [E_negSucc]

lemma lift_eq (m : ℕ) (g : T) : lift m g = 1 + (m : T) * g := by
  apply ext3 <;> simp [lift]

lemma finalOK_sound (β : T) (hf : finalOK β = true) (a b g : ℤ) (ha : a = β.a) (hb : -b = β.c)
    (hg : 1 ≤ g) (hN : g ^ 2 * Nm β = a - 4 * b) (hN0 : Nm β ≠ 0) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hx : 3 ≤ g * (a - b)) : False := by
  unfold finalOK at hf
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hf
  obtain ⟨h60, (h1 | h2) | h3⟩ := hf
  · omega
  · omega
  · rw [← ha, ← hb] at h60 h3
    have habs : |g ^ 2 * Nm β| ≤ 60 := by rw [hN]; convert h60 using 2; ring
    have hN1 : 1 ≤ |Nm β| := Int.one_le_abs hN0
    have hg60 : g < 61 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ g ^ 2)] at habs
      nlinarith
    have := h3 g.toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at this
    rcases this with h | h
    · exact h (by rw [← sq, hN]; ring)
    · exact h (by linarith)


theorem classOK_sound (h : T) (hc : classOK h = true) (n : ℤ) (a b g : ℤ)
    (hη : E n * h = ⟨a, 0, -b⟩) (hg : 1 ≤ g) (hN : g ^ 2 * Nm h = a - 4 * b) (hN0 : Nm h ≠ 0)
    (hab : IsCoprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 3 ≤ g * (a - b)) : False := by
  unfold classOK at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, List.any_eq_true, List.mem_cons, List.not_mem_nil, or_false] at hc
  generalize (params (Nm h).natAbs).1 = m at hc
  generalize (params (Nm h).natAbs).2 = K at hc
  obtain ⟨⟨⟨⟨hK0, hm2⟩, h1⟩, h2⟩, hr⟩ := hc
  rw [lift_eq] at h1 h2
  generalize gam m (tp ε K) = g1 at h1 hr
  generalize gam m (tp εi K) = g2 at h2 hr
  have hKz : (K : ℤ) ≠ 0 := by exact_mod_cast hK0.ne'
  have hr0 : 0 ≤ n % K := Int.emod_nonneg n hKz
  have hrK : n % K < K := Int.emod_lt_of_pos n (by exact_mod_cast hK0)
  set r := (n % K).toNat with hrdef
  set q := n / K with hq
  have hn : n = (r : ℤ) + K * q := by
    rw [hrdef, Int.toNat_of_nonneg hr0]; exact (Int.emod_add_mul_ediv n K).symm
  have hrK' : r < K := by omega
  specialize hr r hrK'
  have hE : E n * h = h * tp ε r * E (K * q) := by
    rw [hn, E_add, E_nat, tp_eq]; ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ, E (K * q) = 1 + (m : T) * ρ := by
    rcases E_mul K q with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he, h1]; exact cong_pow _ _ _
    · rw [he, h2]; exact cong_pow _ _ _
  have hcomp : (⟨a, 0, -b⟩ : T) = h * tp ε r + (m : T) * (h * tp ε r * ρ) := by
    rw [← hη, hE, hρ]; ring
  generalize h * tp ε r * ρ = w at hcomp
  have hNm : Nm h = a ^ 3 - 4 * b ^ 3 := by
    have := congrArg Nm hη
    rw [Nm_mul, Nm_E, one_mul] at this
    rw [this]; simp [Nm]; ring
  have hca := congrArg T.a hcomp
  have hcb := congrArg T.b hcomp
  have hcc := congrArg T.c hcomp
  simp only [T.add_a, T.add_b, T.add_c, ncm_a, ncm_b, ncm_c] at hca hcb hcc
  generalize h * tp ε r = v at hca hcb hcc hr
  rcases hr with ((k1 | k2) | k3) | ⟨hm, r0, hr0mem, ⟨⟨hβb, hl1⟩, hl2⟩, hfin⟩
  · apply k1
    have : v.b = (m : ℤ) * (-w.b) := by linarith
    rw [this]; exact Int.mul_emod_right _ _
  · have hgm : 0 ≤ g % m := Int.emod_nonneg g (by exact_mod_cast (by omega : m ≠ 0))
    have hgm' : g % m < m := Int.emod_lt_of_pos g (by exact_mod_cast (by omega : 0 < m))
    apply k2 (g % m).toNat (by omega)
    rw [Int.toNat_of_nonneg hgm]
    have e : g % ↑m * (g % ↑m) * Nm h - (v.a + 4 * v.c) =
        (m : ℤ) * (-2 * g * (g / m) * Nm h + m * (g / m) ^ 2 * Nm h + w.a + 4 * w.c) := by
      rw [Int.emod_def]
      linear_combination hN + hca + 4 * hcc
    rw [e]; exact Int.mul_emod_right _ _
  · apply k3
    set d : ℕ := Int.gcd (Int.gcd v.a v.c) m
    have hd1 : (d : ℤ) ∣ v.a := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    have hd2 : (d : ℤ) ∣ v.c := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    have hd3 : (d : ℤ) ∣ (m : ℤ) := Int.gcd_dvd_right _ _
    have hda : (d : ℤ) ∣ a := by rw [hca]; exact dvd_add hd1 (dvd_mul_of_dvd_left hd3 _)
    have hdb : (d : ℤ) ∣ b := by
      have : b = -(v.c + m * w.c) := by linarith
      rw [this]; exact (dvd_add hd2 (dvd_mul_of_dvd_left hd3 _)).neg_right
    have hu := hab.isUnit_of_dvd' hda hdb
    rcases Int.isUnit_iff.mp hu with h' | h'
    · exact_mod_cast h'
    · omega
  · -- base point case
    have hp : m.Prime ∧ 3 ≤ m := by
      rcases hm with rfl | rfl | rfl <;> norm_num
    obtain ⟨j0, hj0⟩ : ∃ j0 : ℤ, r0 = r + K * j0 := by
      rcases hr0mem with h' | h' | h' | h'
      · exact ⟨1, by rw [h']; ring⟩
      · exact ⟨0, by rw [h']; ring⟩
      · exact ⟨-1, by rw [h']; ring⟩
      · exact ⟨-2, by rw [h']; ring⟩
    rw [← E_eq_Ec] at hβb hl1 hl2 hfin
    have hE2 : E n * h = h * E r0 * E (K * (q - j0)) := by
      rw [show n = r0 + K * (q - j0) by rw [hn, hj0]; ring, E_add]; ring
    have hb0 : (E n * h).b = 0 := by rw [hη]
    have ht : q - j0 = 0 := by
      rcases E_mul K (q - j0) with ⟨he, hq0⟩ | ⟨he, hq0⟩
      · rw [hE2, he, h1] at hb0
        have := skolem m hp.1 hp.2 g1 _ hβb hl1 _ hb0
        omega
      · rw [hE2, he, h2] at hb0
        have := skolem m hp.1 hp.2 g2 _ hβb hl2 _ hb0
        omega
    rw [ht, mul_zero, E_zero, mul_one] at hE2
    rw [hE2] at hη
    have hNb : Nm (h * E r0) = Nm h := by rw [Nm_mul, Nm_E, mul_one]
    refine finalOK_sound _ hfin a b g (by rw [hη]) (by rw [hη]) hg (by rw [hNb]; exact hN)
      (by rw [hNb]; exact hN0) ha hb hx


theorem box_sound (h : T) (ha1 : -6 ≤ h.a) (ha2 : h.a ≤ 6) (hb1 : -5 ≤ h.b) (hb2 : h.b ≤ 5)
    (hc1 : -4 ≤ h.c) (hc2 : h.c ≤ 4) (hN0 : Nm h ≠ 0) (hd : Nm h ∣ 60) : classOK h = true := by
  have H := boxOK_true
  unfold boxOK at H
  simp only [List.all_eq_true, List.mem_range] at H
  have H2 := H (h.a + 6).toNat (by omega) (h.b + 5).toNat (by omega) (h.c + 4).toNat (by omega)
  have e : (⟨((h.a + 6).toNat : ℤ) - 6, ((h.b + 5).toNat : ℤ) - 5, ((h.c + 4).toNat : ℤ) - 4⟩ : T)
      = h := by
    apply ext3 <;> simp <;> omega
  rw [e] at H2
  simp only [Bool.or_eq_true, decide_eq_true_eq] at H2
  rcases H2 with (h1 | h2) | h3
  · exact absurd h1 hN0
  · exact absurd (Int.emod_eq_zero_of_dvd hd) h2
  · exact h3

/-! Real embedding -/

noncomputable def α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

lemma α3 : α ^ 3 = 2 := by
  rw [α, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

lemma αpos : 0 < α := by unfold α; positivity

lemma αlo : 1.25 < α := by
  by_contra hc
  push Not at hc
  have := pow_le_pow_left₀ αpos.le hc 3
  rw [α3] at this; norm_num at this

lemma αhi : α < 1.26 := by
  by_contra hc
  push Not at hc
  have := pow_le_pow_left₀ (by norm_num) hc 3
  rw [α3] at this; norm_num at this

noncomputable def ev (x : T) : ℝ := x.a + x.b * α + x.c * α ^ 2

lemma ev_mul (x y : T) : ev (x * y) = ev x * ev y := by
  simp only [ev, T.mul_a, T.mul_b, T.mul_c]
  push_cast
  linear_combination (-(x.b * y.c + x.c * y.b : ℝ) - x.c * y.c * α) * α3

lemma ev_one : ev 1 = 1 := by simp [ev]

noncomputable def evHom : T →* ℝ where
  toFun := ev
  map_one' := ev_one
  map_mul' := ev_mul

noncomputable def er : ℝ := ev ε

lemma er_eq : er = 1 + α + α ^ 2 := by simp [er, ev, ε]

lemma er_gt : 1 < er := by rw [er_eq]; nlinarith [αpos]

lemma er_lt : er < 3.85 := by rw [er_eq]; nlinarith [αhi, αpos]

lemma ev_εi : ev εi = er⁻¹ := by
  have : ev ε * ev εi = 1 := by rw [← ev_mul, ε_mul_εi, ev_one]
  rw [er]; exact eq_inv_of_mul_eq_one_right this

lemma ev_E (n : ℤ) : ev (E n) = er ^ n := by
  cases n with
  | ofNat k =>
    have := E_nat k
    simp only [Int.ofNat_eq_natCast] at *
    rw [this, zpow_natCast]
    change evHom (ε ^ k) = _
    rw [map_pow]; rfl
  | negSucc k =>
    rw [E_negSucc, zpow_negSucc]
    change evHom (εi ^ (k + 1)) = _
    rw [map_pow]
    change ev εi ^ (k + 1) = _
    rw [ev_εi, inv_pow]

def adj (x : T) : T := ⟨x.a ^ 2 - 2 * x.b * x.c, 2 * x.c ^ 2 - x.a * x.b, x.b ^ 2 - x.a * x.c⟩

lemma ev_adj (x : T) : ev x * ev (adj x) = Nm x := by
  rw [← ev_mul]
  simp only [ev, adj, Nm, T.mul_a, T.mul_b, T.mul_c]
  push_cast; ring

lemma Q_id (x : T) : 3 * ((x.a : ℝ) ^ 2 + α ^ 2 * x.b ^ 2 + 2 * α * x.c ^ 2)
    = ev x ^ 2 + 2 * ev (adj x) := by
  simp only [ev, adj]
  push_cast
  linear_combination (-(2 * x.b * x.c : ℝ) - x.c ^ 2 * α) * α3

theorem box_exists (η : T) (hN0 : Nm η ≠ 0) (hN : |Nm η| ≤ 60) :
    ∃ n : ℤ, ∃ h : T, E n * h = η ∧ Nm h = Nm η ∧ -6 ≤ h.a ∧ h.a ≤ 6 ∧ -5 ≤ h.b ∧ h.b ≤ 5 ∧
      -4 ≤ h.c ∧ h.c ≤ 4 := by
  have hev : ev η ≠ 0 := by
    intro h0
    have := ev_adj η
    rw [h0, zero_mul] at this
    exact hN0 (by exact_mod_cast this.symm)
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (abs_pos.mpr hev) er_gt
  refine ⟨n, E (-n) * η, ?_, ?_, ?_⟩
  · rw [← mul_assoc, ← E_add, add_neg_cancel, E_zero, one_mul]
  · rw [Nm_mul, Nm_E, one_mul]
  set h := E (-n) * η with hh
  have hevh : ev h = er ^ (-n) * ev η := by rw [hh, ev_mul, ev_E]
  have erpos : 0 < er := lt_trans one_pos er_gt
  have hpn : 0 < er ^ (-n) := zpow_pos erpos _
  have hinv : er ^ (-n) * er ^ n = 1 := by
    rw [← zpow_add₀ erpos.ne', neg_add_cancel, zpow_zero]
  have hu1 : 1 ≤ |ev h| := by
    rw [hevh, abs_mul, abs_of_pos hpn]
    calc (1 : ℝ) = er ^ (-n) * er ^ n := hinv.symm
      _ ≤ er ^ (-n) * |ev η| := by gcongr
  have hu2 : |ev h| < er := by
    rw [hevh, abs_mul, abs_of_pos hpn]
    calc er ^ (-n) * |ev η| < er ^ (-n) * er ^ (n + 1) := by gcongr
      _ = er := by rw [zpow_add_one₀ erpos.ne', ← mul_assoc, hinv, one_mul]
  have hNh : Nm h = Nm η := by rw [hh, Nm_mul, Nm_E, one_mul]
  have hw : |ev (adj h)| ≤ 60 := by
    have e := ev_adj h
    have e2 : |ev h| * |ev (adj h)| = |(Nm h : ℝ)| := by rw [← abs_mul, e]
    have e3 : |(Nm h : ℝ)| ≤ 60 := by rw [hNh]; exact_mod_cast hN
    nlinarith [abs_nonneg (ev (adj h))]
  have hQ := Q_id h
  have hsq : ev h ^ 2 < er ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ hu2 (abs_nonneg _) (by norm_num)
  have hw' : ev (adj h) ≤ 60 := (abs_le.mp hw).2
  have her2 : er ^ 2 < 3.85 ^ 2 := pow_lt_pow_left₀ er_lt (by linarith) (by norm_num)
  have hQb : (h.a : ℝ) ^ 2 + α ^ 2 * h.b ^ 2 + 2 * α * h.c ^ 2 < 45 := by nlinarith
  have ta : (0 : ℝ) ≤ h.a ^ 2 := sq_nonneg _
  have tb : (0 : ℝ) ≤ α ^ 2 * h.b ^ 2 := by positivity
  have tc : (0 : ℝ) ≤ 2 * α * h.c ^ 2 := by have := αpos; positivity
  have hα2 : (1.5625 : ℝ) < α ^ 2 := by nlinarith [αlo]
  have ra : ((h.a ^ 2 : ℤ) : ℝ) < 45 := by push_cast; linarith
  have rb : ((h.b ^ 2 : ℤ) : ℝ) < 29 := by
    push_cast
    by_contra hc; push Not at hc
    nlinarith
  have rc : ((h.c ^ 2 : ℤ) : ℝ) < 18 := by
    push_cast
    by_contra hc; push Not at hc
    nlinarith [αlo]
  have ia : h.a ^ 2 < 45 := by exact_mod_cast ra
  have ib : h.b ^ 2 < 29 := by exact_mod_cast rb
  have ic : h.c ^ 2 < 18 := by exact_mod_cast rc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end OMA.E686

open OMA.E686

theorem OMA.solution : type_of% @Erdos686.erdos_686.variants.four_three := by
  rintro ⟨n, m, hm, h⟩
  simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 3),
    Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self, Finset.prod_singleton] at h
  rw [eq_div_iff (by positivity)] at h
  push_cast at h
  have h' : ((m:ℤ)+1)*((m:ℤ)+2)*((m:ℤ)+3) = 4*(((n:ℤ)+1)*((n:ℤ)+2)*((n:ℤ)+3)) := by
    have : ((m:ℚ)+1)*((m:ℚ)+2)*((m:ℚ)+3) = 4*(((n:ℚ)+1)*((n:ℚ)+2)*((n:ℚ)+3)) := by
      linear_combination -h
    exact_mod_cast this
  have hm' : (n : ℤ) + 3 ≤ m := by exact_mod_cast hm
  obtain ⟨X, hXdef⟩ : ∃ X : ℤ, X = m + 2 := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℤ, Y = n + 2 := ⟨_, rfl⟩
  have hXY : X ^ 3 - X = 4 * (Y ^ 3 - Y) := by rw [hXdef, hYdef]; linear_combination h'
  have hY : 2 ≤ Y := by rw [hYdef]; have := Int.natCast_nonneg n; linarith
  have hX : Y + 3 ≤ X := by rw [hXdef, hYdef]; linarith
  have hgpos : 0 < Int.gcd X Y := Int.gcd_pos_of_ne_zero_left _ (by omega)
  obtain ⟨a, b, hab1, hXa, hYb⟩ := Int.exists_gcd_one hgpos
  obtain ⟨g, hgdef⟩ : ∃ g : ℤ, g = Int.gcd X Y := ⟨_, rfl⟩
  rw [← hgdef] at hXa hYb
  have hg : 1 ≤ g := by rw [hgdef]; exact_mod_cast hgpos
  have ha : 1 ≤ a := by
    by_contra hc; push Not at hc; nlinarith
  have hb : 1 ≤ b := by
    by_contra hc; push Not at hc; nlinarith
  have hab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab1
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = a ^ 3 - 4 * b ^ 3 := ⟨_, rfl⟩
  have hN : g ^ 2 * N = a - 4 * b := by
    have e : g * (g ^ 2 * N - (a - 4 * b)) = 0 := by
      rw [hXa, hYb] at hXY; rw [hNdef]; linear_combination hXY
    rcases mul_eq_zero.mp e with e | e
    · omega
    · linarith
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hN
    have : a = 4 * b := by linarith
    rw [this, h0] at hNdef
    have : 0 < b ^ 3 := by positivity
    nlinarith
  have hdiv : N ∣ 60 := by
    have hcop : IsCoprime N (b ^ 3) := by
      have h1 : IsCoprime (a ^ 3) b := hab.pow_left
      have h2 : IsCoprime (a ^ 3 + b * (-4 * b ^ 2)) b := h1.add_mul_left_left _
      have e : a ^ 3 + b * (-4 * b ^ 2) = N := by rw [hNdef]; ring
      rw [e] at h2
      exact h2.pow_right
    have : N ∣ 60 * b ^ 3 := ⟨1 - 48 * b ^ 2 * g ^ 2 - 12 * b * g ^ 4 * N - g ^ 6 * N ^ 2, by
      linear_combination (-1) * hNdef + (a ^ 2 + a * (4 * b + g ^ 2 * N) +
        (4 * b + g ^ 2 * N) ^ 2) * hN⟩
    exact hcop.dvd_of_dvd_mul_right this
  have hNη : Nm ⟨a, 0, -b⟩ = N := by rw [hNdef]; simp [Nm]; ring
  have habs : |N| ≤ 60 := Int.le_of_dvd (by norm_num) ((abs_dvd N 60).mpr hdiv)
  obtain ⟨k, h0, hE, hNm, b1, b2, b3, b4, b5, b6⟩ :=
    box_exists ⟨a, 0, -b⟩ (by rw [hNη]; exact hN0) (by rw [hNη]; exact habs)
  rw [hNη] at hNm
  have hx : 3 ≤ g * (a - b) := by rw [hXa, hYb] at hX; linarith
  exact classOK_sound h0 (box_sound h0 b1 b2 b3 b4 b5 b6 (by rw [hNm]; exact hN0)
    (by rw [hNm]; exact hdiv)) k a b g hE hg (by rw [hNm]; exact hN) (by rw [hNm]; exact hN0)
    hab ha hb hx
