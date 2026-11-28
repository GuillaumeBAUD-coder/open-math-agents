import OMAStatements.S_oeis_a347293
import Mathlib

-- h = mu * f (Dirichlet convolution), written as a divisor sum
noncomputable def a347293_h (f : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) * f (d / e)

-- Moebius inversion: f m is the divisor sum of h
theorem a347293_inv (f : ℕ → ℂ) (m : ℕ) (hm : 0 < m) :
    ∑ e ∈ m.divisors, a347293_h f e = f m := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := a347293_h f) (g := f)).2
    (fun n _ => Nat.sum_divisorsAntidiagonal
      (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℂ) * f b))
  exact key m hm

theorem a347293_split (f : ℕ → ℂ) (A n : ℕ) (hn : 0 < n) :
    f (Nat.gcd A n) = ∑ e ∈ n.divisors, if e ∣ A then a347293_h f e else 0 := by
  have hg : 0 < Nat.gcd A n := Nat.gcd_pos_of_pos_right A hn
  rw [← a347293_inv f _ hg, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨h1, _⟩
    exact ⟨⟨h1.trans (Nat.gcd_dvd_right A n), hn.ne'⟩, h1.trans (Nat.gcd_dvd_left A n)⟩
  · rintro ⟨⟨h2, _⟩, h1⟩
    exact ⟨Nat.dvd_gcd h1 h2, hg.ne'⟩

theorem a347293_reindex {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, g (i - 1) = ∑ x ∈ Finset.range n, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    simp

theorem a347293_period (F : ℕ → ℕ) (e q : ℕ) :
    ∑ x ∈ Finset.range (e * q), F (x % e) = q * ∑ a ∈ Finset.range e, F a := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [mul_add_one, Finset.sum_range_add, ih, add_one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem a347293_modcond (e x y : ℕ) : (e ∣ 1 + x * y) ↔ (e ∣ 1 + (x % e) * (y % e)) := by
  have h : (1 + x * y) % e = (1 + (x % e) * (y % e)) % e :=
    Nat.ModEq.add_left 1 (Nat.ModEq.mul (Nat.mod_modEq x e).symm (Nat.mod_modEq y e).symm)
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h]

-- for a fixed a, the number of b mod e with e | 1 + a b
theorem a347293_row (e a : ℕ) (he : 0 < e) :
    ∑ b ∈ Finset.range e, (if e ∣ 1 + a * b then 1 else 0) = if Nat.Coprime e a then 1 else 0 := by
  rw [← Finset.card_filter]
  split_ifs with hc
  · rw [Finset.card_eq_one]
    rcases Nat.lt_or_ge e 2 with he1 | he2
    · have h1 : e = 1 := by omega
      subst h1
      refine ⟨0, ?_⟩
      ext b
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.one_dvd, and_true]
      omega
    · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc.symm he2
      refine ⟨(e - 1) * m % e, ?_⟩
      have : NeZero e := ⟨by omega⟩
      have hm' : (a : ZMod e) * (m : ZMod e) = 1 := by
        have h := congrArg (fun t : ℕ => (t : ZMod e)) hm
        simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at h
        exact h
      have he1' : ((e - 1 : ℕ) : ZMod e) = -1 := by
        have h0 : ((e - 1 + 1 : ℕ) : ZMod e) = 0 := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ e)]
          exact ZMod.natCast_self e
        rw [Nat.cast_add, Nat.cast_one] at h0
        linear_combination h0
      ext b
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hb, hdiv⟩
        have h0 : ((1 + a * b : ℕ) : ZMod e) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdiv
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at h0
        have key : (b : ZMod e) = (((e - 1) * m % e : ℕ) : ZMod e) := by
          rw [ZMod.natCast_mod, Nat.cast_mul, he1']
          linear_combination (-(b : ZMod e)) * hm' + (m : ZMod e) * h0
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb, Nat.mod_mod] at key
        exact key
      · rintro rfl
        refine ⟨Nat.mod_lt _ (by omega), ?_⟩
        rw [← ZMod.natCast_eq_zero_iff]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, ZMod.natCast_mod]
        rw [he1']
        linear_combination (-1 : ZMod e) * hm'
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hdiv
    apply hc
    have h1 : Nat.gcd e a ∣ 1 + a * b := (Nat.gcd_dvd_left e a).trans hdiv
    have h2 : Nat.gcd e a ∣ a * b := (Nat.gcd_dvd_right e a).trans (dvd_mul_right a b)
    have h3 : Nat.gcd e a ∣ 1 := (Nat.dvd_add_left h2).mp h1
    exact Nat.dvd_one.mp h3

-- the number of pairs (x, y) mod n with e | 1 + x y is (n/e)^2 phi(e)
theorem a347293_count (n e : ℕ) (hn : 0 < n) (he : e ∣ n) :
    ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, (if e ∣ 1 + x * y then 1 else 0) =
      (n / e) ^ 2 * Nat.totient e := by
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hn
  obtain ⟨q, rfl⟩ := he
  rw [Nat.mul_div_cancel_left q hepos]
  have h1 : ∀ x, ∑ y ∈ Finset.range (e * q), (if e ∣ 1 + x * y then 1 else 0) =
      q * ∑ b ∈ Finset.range e, (if e ∣ 1 + (x % e) * b then 1 else 0) := by
    intro x
    calc ∑ y ∈ Finset.range (e * q), (if e ∣ 1 + x * y then 1 else 0)
        = ∑ y ∈ Finset.range (e * q),
            (fun t => if e ∣ 1 + (x % e) * t then 1 else 0) (y % e) := by
          apply Finset.sum_congr rfl
          intro y _
          simp only [a347293_modcond e x y]
      _ = q * ∑ b ∈ Finset.range e, (fun t => if e ∣ 1 + (x % e) * t then 1 else 0) b :=
          a347293_period (fun t => if e ∣ 1 + (x % e) * t then 1 else 0) e q
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum,
    a347293_period (fun a => ∑ b ∈ Finset.range e, if e ∣ 1 + a * b then 1 else 0) e q,
    Finset.sum_congr rfl (fun a _ => a347293_row e a hepos), ← Finset.card_filter,
    ← Nat.totient_eq_card_coprime]
  ring

theorem a347293_part1 (f : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n) =
      ∑ d ∈ n.divisors, (((n / d) ^ 2 : ℕ) : ℂ) * ((Nat.totient d : ℂ) * a347293_h f d) := by
  have hn' : 0 < n := hn
  calc ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n)
      = ∑ i ∈ Finset.Icc 1 n, ∑ y ∈ Finset.range n, f (Nat.gcd (1 + (i - 1) * y) n) := by
        apply Finset.sum_congr rfl
        intro i _
        exact a347293_reindex (fun y => f (Nat.gcd (1 + (i - 1) * y) n)) n
    _ = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, f (Nat.gcd (1 + x * y) n) :=
        a347293_reindex (fun x => ∑ y ∈ Finset.range n, f (Nat.gcd (1 + x * y) n)) n
    _ = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ e ∈ n.divisors,
          (if e ∣ 1 + x * y then a347293_h f e else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        exact a347293_split f (1 + x * y) n hn'
    _ = ∑ x ∈ Finset.range n, ∑ e ∈ n.divisors, ∑ y ∈ Finset.range n,
          (if e ∣ 1 + x * y then a347293_h f e else 0) :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = ∑ e ∈ n.divisors, ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
          (if e ∣ 1 + x * y then a347293_h f e else 0) := Finset.sum_comm
    _ = ∑ e ∈ n.divisors, a347293_h f e *
          ((∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
            (if e ∣ 1 + x * y then 1 else 0) : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro e _
        push_cast
        simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
    _ = ∑ e ∈ n.divisors, a347293_h f e * (((n / e) ^ 2 * Nat.totient e : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [a347293_count n e hn' (Nat.dvd_of_mem_divisors he)]
    _ = ∑ d ∈ n.divisors, (((n / d) ^ 2 : ℕ) : ℂ) * ((Nat.totient d : ℂ) * a347293_h f d) := by
        apply Finset.sum_congr rfl
        intro d _
        push_cast
        ring

noncomputable def a347293_F (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun k => if k = 0 then 0 else f k, by simp⟩

noncomputable def a347293_Phi : ArithmeticFunction ℂ :=
  ⟨fun k => (Nat.totient k : ℂ), by simp⟩

theorem a347293_F_apply (f : ℕ → ℂ) (k : ℕ) : a347293_F f k = if k = 0 then 0 else f k := rfl

theorem a347293_Phi_apply (k : ℕ) : a347293_Phi k = (Nat.totient k : ℂ) := rfl

theorem a347293_F_mult (f : ℕ → ℂ) (h1 : f 1 = 1)
    (hm : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) :
    (a347293_F f).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [a347293_F_apply]
    simp [h1]
  · intro m n hmn
    rw [a347293_F_apply, a347293_F_apply, a347293_F_apply]
    by_cases hm0 : m = 0
    · simp [hm0]
    · by_cases hn0 : n = 0
      · simp [hn0]
      · simp [hm0, hn0, hm m n hmn]

theorem a347293_Phi_mult : a347293_Phi.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [a347293_Phi_apply]
    simp
  · intro m n hmn
    rw [a347293_Phi_apply, a347293_Phi_apply, a347293_Phi_apply, Nat.totient_mul hmn]
    push_cast
    ring

noncomputable def a347293_P (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.pow 2 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
    (a347293_Phi.pmul
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
        a347293_F f))

theorem a347293_H_apply (f : ℕ → ℂ) (d : ℕ) (hd : 0 < d) :
    (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
      a347293_F f) d = a347293_h f d := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun a b =>
    (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) a) *
      a347293_F f b)]
  unfold a347293_h
  apply Finset.sum_congr rfl
  intro e he
  rw [ArithmeticFunction.intCoe_apply, a347293_F_apply]
  have hdiv := Nat.dvd_of_mem_divisors he
  have hne : d / e ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hd hdiv) (Nat.pos_of_mem_divisors he)).ne'
  simp [hne]

theorem a347293_P_apply (f : ℕ → ℂ) (N : ℕ) :
    a347293_P f N =
      ∑ d ∈ N.divisors, (((N / d) ^ 2 : ℕ) : ℂ) * ((Nat.totient d : ℂ) * a347293_h f d) := by
  unfold a347293_P
  rw [ArithmeticFunction.mul_apply, ← Nat.sum_divisorsAntidiagonal' (fun a b =>
    (((a ^ 2 : ℕ) : ℂ) * ((Nat.totient b : ℂ) * a347293_h f b)))]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hprod, hN⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  have hx2 : 0 < x.2 := by
    rcases Nat.eq_zero_or_pos x.2 with h | h
    · rw [h, mul_zero] at hprod
      exact absurd hprod.symm hN
    · exact h
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.pow_apply,
    ArithmeticFunction.pmul_apply, a347293_H_apply f x.2 hx2, a347293_Phi_apply]
  simp

theorem a347293_P_mult (f : ℕ → ℂ) (h1 : f 1 = 1)
    (hm : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) :
    (a347293_P f).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_pow.natCast.mul
    (a347293_Phi_mult.pmul
      (ArithmeticFunction.isMultiplicative_moebius.intCast.mul (a347293_F_mult f h1 hm)))

theorem a347293_h_id (d : ℕ) (hd : 0 < d) : a347293_h (fun m => (m : ℂ)) d = (Nat.totient d : ℂ) := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun k => (Nat.totient k : ℂ)) (g := fun k => (k : ℂ))).1
    (fun k _ => by exact_mod_cast Nat.sum_totient k)
  rw [← key d hd]
  unfold a347293_h
  exact (Nat.sum_divisorsAntidiagonal
    (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℂ) * (b : ℂ))).symm

theorem OMA.solution : type_of% @OMA.S_oeis_a347293.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro f n hn
    exact a347293_part1 f n hn
  · rintro f ⟨h1, hm⟩
    refine ⟨?_, ?_⟩
    · simp [h1]
    · intro m n hm1 hn1 hmn
      rw [a347293_part1 f (m * n) (Nat.one_le_iff_ne_zero.2 (by positivity)),
        a347293_part1 f m hm1, a347293_part1 f n hn1, ← a347293_P_apply, ← a347293_P_apply,
        ← a347293_P_apply]
      exact (a347293_P_mult f h1 hm).map_mul_of_coprime hmn
  · intro n hn
    have h1 : ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
        ((Nat.gcd (1 + (i - 1) * (k - 1)) n : ℕ) : ℂ) =
        ∑ d ∈ n.divisors, (((n / d) ^ 2 : ℕ) : ℂ) *
          ((Nat.totient d : ℂ) * a347293_h (fun m => (m : ℂ)) d) :=
      a347293_part1 (fun m => (m : ℂ)) n hn
    apply Nat.cast_injective (R := ℂ)
    rw [Finset.sum_comm]
    push_cast
    rw [h1]
    apply Finset.sum_congr rfl
    intro d hd
    rw [a347293_h_id d (Nat.pos_of_mem_divisors hd)]
    push_cast
    ring
