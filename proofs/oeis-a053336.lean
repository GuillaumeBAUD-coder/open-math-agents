import OMAStatements.S_oeis_a053336
import Mathlib

/-!
Proof sketch. `G S n m` says `m` is the value of a length `n` digit list with digits in `S`.
An `(n+1)`-digit value is `a + 10 ^ n * d` with `a` an `n`-digit value. Since `10 ^ n = 2 ^ n * 5 ^ n`
with `5 ^ n` odd, divisibility by `2 ^ (n+1)` of `a + 10 ^ n * d` (with `a = 2 ^ n * k`) is the
parity condition `k + d` even. Uniqueness: induction, the two candidate digits differ in parity.
Existence: joint induction from `n = 1` (6 and 4) keeping `a + b = 10 ^ n`, choosing digits
`d` and `9 - d`. The third conjunct follows from uniqueness.
-/

namespace R053336
open OMA.S_oeis_a053336

def G (S : ℕ → Prop) (n m : ℕ) : Prop :=
  ∃ L : List ℕ, L.length = n ∧ (∀ x ∈ L, S x) ∧ Nat.ofDigits 10 L = m

theorem G_zero {S : ℕ → Prop} {m : ℕ} (h : G S 0 m) : m = 0 := by
  obtain ⟨L, hl, -, rfl⟩ := h
  rw [List.length_eq_zero_iff] at hl
  subst hl
  rfl

theorem G_succ (S : ℕ → Prop) (n m : ℕ) :
    G S (n + 1) m ↔ ∃ a d, G S n a ∧ S d ∧ m = a + 10 ^ n * d := by
  constructor
  · rintro ⟨L, hl, hs, rfl⟩
    have hne : L ≠ [] := by
      rintro rfl
      simp at hl
    obtain ⟨L', d, rfl⟩ : ∃ L' d, L = L' ++ [d] :=
      ⟨L.dropLast, L.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    simp only [List.length_append, List.length_singleton] at hl
    have hl' : L'.length = n := by omega
    refine ⟨Nat.ofDigits 10 L', d, ⟨L', hl', fun x hx => hs x (List.mem_append_left _ hx), rfl⟩,
      hs d (by simp), ?_⟩
    rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hl']
  · rintro ⟨a, d, ⟨L, hl, hs, rfl⟩, hd, rfl⟩
    refine ⟨L ++ [d], by simp [hl], ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hs x h
      · rw [List.mem_singleton] at h
        subst h
        exact hd
    · rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hl]

theorem ten_pow (n : ℕ) : (10 : ℕ) ^ n = 2 ^ n * 5 ^ n := by
  rw [← mul_pow]
  norm_num

theorem uniq (S : ℕ → Prop) (hS : ∀ d d', S d → S d' → d % 2 = d' % 2 → d = d') :
    ∀ n m m', G S n m → G S n m' → 2 ^ n ∣ m → 2 ^ n ∣ m' → m = m' := by
  intro n
  induction n with
  | zero =>
    intro m m' h h' _ _
    rw [G_zero h, G_zero h']
  | succ n ih =>
    intro m m' h h' hm hm'
    obtain ⟨a, d, ha, hd, rfl⟩ := (G_succ S n m).1 h
    obtain ⟨a', d', ha', hd', rfl⟩ := (G_succ S n m').1 h'
    have hpos : 0 < 2 ^ n := by positivity
    have h10 : ∀ y, 2 ^ n ∣ 10 ^ n * y := fun y =>
      Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (by norm_num) n) y
    have hlow : ∀ x y, 2 ^ (n + 1) ∣ x + 10 ^ n * y → 2 ^ n ∣ x := by
      intro x y hxy
      have h1 : 2 ^ n ∣ x + 10 ^ n * y := (pow_dvd_pow 2 (Nat.le_succ n)).trans hxy
      exact (Nat.dvd_add_left (h10 y)).mp h1
    have haa : a = a' := ih a a' ha ha' (hlow _ _ hm) (hlow _ _ hm')
    subst haa
    obtain ⟨k, rfl⟩ := hlow _ _ hm
    obtain ⟨j, hj⟩ : Odd (5 ^ n) := Odd.pow (by decide)
    have par : ∀ y, 2 ^ (n + 1) ∣ 2 ^ n * k + 10 ^ n * y → (k + y) % 2 = 0 := by
      intro y hy
      rw [ten_pow, hj, pow_succ,
        show 2 ^ n * k + 2 ^ n * (2 * j + 1) * y = 2 ^ n * (k + 2 * (j * y) + y) by ring] at hy
      have := Nat.dvd_of_mul_dvd_mul_left hpos hy
      omega
    have e1 := par d hm
    have e2 := par d' hm'
    rw [hS d d' hd hd' (by omega)]

theorem exist (n : ℕ) (hn : 1 ≤ n) :
    ∃ a b, G (fun d => d = 5 ∨ d = 6) n a ∧ G (fun d => d = 3 ∨ d = 4) n b ∧
      2 ^ n ∣ a ∧ 2 ^ n ∣ b ∧ a + b = 10 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨6, 4, ⟨[6], rfl, by simp, Nat.ofDigits_singleton⟩,
      ⟨[4], rfl, by simp, Nat.ofDigits_singleton⟩, by norm_num, by norm_num, by norm_num⟩
  | succ n hn ih =>
    obtain ⟨a, b, ha, hb, hda, hdb, hab⟩ := ih
    obtain ⟨k1, rfl⟩ := hda
    obtain ⟨k2, rfl⟩ := hdb
    have hpos : 0 < 2 ^ n := by positivity
    have hk : k1 + k2 = 5 ^ n := by
      have : 2 ^ n * (k1 + k2) = 2 ^ n * 5 ^ n := by rw [mul_add, hab, ten_pow]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    obtain ⟨j, hj⟩ : Odd (5 ^ n) := Odd.pow (by decide)
    rw [hj] at hk
    have key : ∀ x d, (x + d) % 2 = 0 → 2 ^ (n + 1) ∣ 2 ^ n * x + 10 ^ n * d := by
      intro x d hx
      rw [ten_pow, hj, pow_succ,
        show 2 ^ n * x + 2 ^ n * (2 * j + 1) * d = 2 ^ n * (x + 2 * (j * d) + d) by ring]
      exact mul_dvd_mul_left _ (by omega)
    have hsum : ∀ d1 d2, d1 + d2 = 9 →
        2 ^ n * k1 + 10 ^ n * d1 + (2 ^ n * k2 + 10 ^ n * d2) = 10 ^ (n + 1) := by
      intro d1 d2 h12
      rw [pow_succ]
      have : 2 ^ n * k1 + 10 ^ n * d1 + (2 ^ n * k2 + 10 ^ n * d2)
          = (2 ^ n * k1 + 2 ^ n * k2) + 10 ^ n * (d1 + d2) := by ring
      rw [this, hab, h12]
      ring
    rcases Nat.mod_two_eq_zero_or_one k2 with h | h
    · exact ⟨2 ^ n * k1 + 10 ^ n * 5, 2 ^ n * k2 + 10 ^ n * 4, (G_succ _ n _).2 ⟨_, 5, ha, Or.inl rfl, rfl⟩,
        (G_succ _ n _).2 ⟨_, 4, hb, Or.inr rfl, rfl⟩,
        key _ _ (by omega), key _ _ (by omega), hsum 5 4 rfl⟩
    · exact ⟨2 ^ n * k1 + 10 ^ n * 6, 2 ^ n * k2 + 10 ^ n * 3, (G_succ _ n _).2 ⟨_, 6, ha, Or.inr rfl, rfl⟩,
        (G_succ _ n _).2 ⟨_, 3, hb, Or.inl rfl, rfl⟩,
        key _ _ (by omega), key _ _ (by omega), hsum 6 3 rfl⟩

theorem isA_iff (S : ℕ → Prop) (hS : ∀ x, S x → 0 < x ∧ x < 10) (n m : ℕ) :
    ((Nat.digits 10 m).length = n ∧ (∀ d ∈ Nat.digits 10 m, S d) ∧ 2 ^ n ∣ m) ↔
      (G S n m ∧ 2 ^ n ∣ m) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨_, h1, h2, Nat.ofDigits_digits 10 m⟩, h3⟩
  · rintro ⟨⟨L, hl, hs, rfl⟩, h3⟩
    have hd : Nat.digits 10 (Nat.ofDigits 10 L) = L :=
      Nat.digits_ofDigits 10 (by norm_num) L (fun l hl => (hS l (hs l hl)).2)
        (fun h => (hS _ (hs _ (List.getLast_mem h))).1.ne')
    rw [hd]
    exact ⟨hl, hs, h3⟩

end R053336

open R053336

theorem OMA.solution : type_of% @OMA.S_oeis_a053336.main := by
  intro n hn
  have e5 : ∀ m, OMA.S_oeis_a053336.IsA053336 n m ↔
      G (fun d => d = 5 ∨ d = 6) n m ∧ 2 ^ n ∣ m :=
    fun m => isA_iff (fun d => d = 5 ∨ d = 6) (fun x hx => by rcases hx with h | h <;> omega) n m
  have e3 : ∀ m, OMA.S_oeis_a053336.IsA035014 n m ↔
      G (fun d => d = 3 ∨ d = 4) n m ∧ 2 ^ n ∣ m :=
    fun m => isA_iff (fun d => d = 3 ∨ d = 4) (fun x hx => by rcases hx with h | h <;> omega) n m
  have u5 := uniq (fun d => d = 5 ∨ d = 6)
    (fun d d' hd hd' h => by rcases hd with hd | hd <;> rcases hd' with hd' | hd' <;> omega) n
  have u3 := uniq (fun d => d = 3 ∨ d = 4)
    (fun d d' hd hd' h => by rcases hd with hd | hd <;> rcases hd' with hd' | hd' <;> omega) n
  obtain ⟨a, b, ha, hb, hda, hdb, hab⟩ := exist n hn
  refine ⟨⟨a, (e5 a).2 ⟨ha, hda⟩, fun m hm => ?_⟩, ⟨b, (e3 b).2 ⟨hb, hdb⟩, fun m hm => ?_⟩,
    fun m₁ m₂ h1 h2 => ?_⟩
  · obtain ⟨g, d⟩ := (e5 m).1 hm
    exact u5 m a g ha d hda
  · obtain ⟨g, d⟩ := (e3 m).1 hm
    exact u3 m b g hb d hdb
  · obtain ⟨g1, d1⟩ := (e5 m₁).1 h1
    obtain ⟨g2, d2⟩ := (e3 m₂).1 h2
    have r1 := u5 m₁ a g1 ha d1 hda
    have r2 := u3 m₂ b g2 hb d2 hdb
    omega
