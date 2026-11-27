import FormalConjectures.ErdosProblems.«711»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Bertrand

/-!
# Erdős Problem 711(i): prime and composite cofactor matchings

Split each modulus at a prime cutoff and use a separate interval for each
cofactor class. The rough output condition lets us recover the small-prime
part from a chosen multiple, so different small-prime parts cannot collide.
-/

-- Credit: @firecake

namespace OMA.R_Erdos711_erdos_711_parts_i_R1

open Filter Asymptotics
open scoped Topology

private theorem split_factors (y d : ℕ) (hd : 0 < d) :
    ∃ s a : ℕ, 0 < s ∧ 0 < a ∧ d = s * a ∧
      (∀ p : ℕ, p.Prime → p ∣ s → p ≤ y) ∧
      (∀ p : ℕ, p.Prime → p ∣ a → y < p) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hr : ∀ p : ℕ, p.Prime → p ∣ d → y < p
    · exact ⟨1, d, by decide, hd, by simp, fun q hq hq1 => (hq.not_dvd_one hq1).elim, hr⟩
    · push Not at hr
      obtain ⟨p, hp, hpd, hpy⟩ := hr
      obtain ⟨z, rfl⟩ := hpd
      have hz : 0 < z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at hd)
      have hzd : z < p * z := by
        simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hz
      obtain ⟨s, a, hs, ha, hza, hsy, hay⟩ := ih z hzd hz
      refine ⟨p * s, a, Nat.mul_pos hp.pos hs, ha, ?_, ?_, hay⟩
      · rw [hza, Nat.mul_assoc]
      · intro q hq hqps
        rcases hq.dvd_mul.mp hqps with hqp | hqs
        · rwa [(Nat.prime_dvd_prime_iff_eq hq hp).mp hqp]
        · exact hsy q hq hqs

private theorem supported_coprime {y s v : ℕ}
    (hs : ∀ p : ℕ, p.Prime → p ∣ s → p ≤ y)
    (hv : ∀ p : ℕ, p.Prime → p ∣ v → y < p) :
    s.Coprime v := by
  change s.gcd v = 1
  by_contra h
  obtain ⟨p, hp, hg⟩ := Nat.exists_prime_and_dvd h
  have hps := hs p hp (dvd_trans hg (Nat.gcd_dvd_left s v))
  have hpv := hv p hp (dvd_trans hg (Nat.gcd_dvd_right s v))
  omega

set_option maxHeartbeats 1000000 in
private theorem assemble (n y B : ℕ)
    (hPrime : ∀ X : ℕ, X ≤ n → ∀ m : ℕ,
      ∃ f : {a : ℕ // a ≤ X ∧ y < a ∧ a.Prime} → ℕ,
        Function.Injective f ∧ ∀ a,
          m < f a ∧ f a ≤ m + B * X ∧ a.val ∣ f a ∧
            (∀ p : ℕ, p.Prime → p ∣ f a → y < p))
    (hComposite : ∀ X : ℕ, X ≤ n → ∀ m : ℕ,
      ∃ f : {a : ℕ // a ≤ X ∧ 2 ≤ a ∧ ¬ a.Prime ∧
        (∀ p : ℕ, p.Prime → p ∣ a → y < p)} → ℕ,
        Function.Injective f ∧ ∀ a,
          m < f a ∧ f a ≤ m + B * X ∧ a.val ∣ f a ∧
            (∀ p : ℕ, p.Prime → p ∣ f a → y < p))
    (hn : 2 ≤ n) (hCut : 2 * y ≤ n)
    (m : ℕ) : Erdos711.HasDivisibleDistinctTuple n m (3 * (B * n) + 1) := by
  classical
  obtain ⟨p, hp, hyp, hpn⟩ : ∃ p : ℕ, p.Prime ∧ y < p ∧ p ≤ n := by
    by_cases hy : y = 0
    · exact ⟨2, Nat.prime_two, by omega, hn⟩
    · obtain ⟨p, hp, hyp, hpy⟩ := Nat.exists_prime_lt_and_le_two_mul y hy
      exact ⟨p, hp, hyp, hpy.trans hCut⟩
  -- Match p in a scaled interval and divide by p to get a rough integer.
  have hRough (start : ℕ) :
      ∃ x : ℕ, start < x ∧ x ≤ start + B ∧
        (∀ q : ℕ, q.Prime → q ∣ x → y < q) := by
    obtain ⟨g, _, hg⟩ := hPrime p hpn (p * start)
    let i : {a : ℕ // a ≤ p ∧ y < a ∧ a.Prime} := ⟨p, le_rfl, hyp, hp⟩
    obtain ⟨hlo, hhi, hdiv, hy⟩ := hg i
    obtain ⟨x, hx⟩ := hdiv
    change g i = p * x at hx
    refine ⟨x, ?_, ?_, fun q hq hqx => hy q hq ?_⟩
    · rw [hx] at hlo
      exact Nat.lt_of_mul_lt_mul_left hlo
    · rw [hx, Nat.mul_comm B p, ← Nat.mul_add] at hhi
      exact Nat.le_of_mul_le_mul_left hhi hp.pos
    · rw [hx, Nat.mul_comm p x]
      exact dvd_mul_of_dvd_left hqx p
  let block : ℕ → ℕ := fun k => m + k * (B * n)
  let classOf : ℕ → ℕ := fun a => if a = 1 then 0 else if a.Prime then 1 else 2
  have hMatch (s k : ℕ) (hs : 0 < s) (hsn : s ≤ n) (hk : k ≤ 2) :
      ∃ f : {a : ℕ // a ≤ n / s ∧ 0 < a ∧
          (∀ p : ℕ, p.Prime → p ∣ a → y < p) ∧ classOf a = k} → ℕ,
        Function.Injective f ∧ ∀ a,
          block k / s < f a ∧ f a ≤ block k / s + B * (n / s) ∧ a.val ∣ f a ∧
            (∀ p : ℕ, p.Prime → p ∣ f a → y < p) := by
    have one_of_class (a : ℕ) (ha : classOf a = 0) : a = 1 := by
      by_contra h
      by_cases hp : a.Prime <;> simp [classOf, h, hp] at ha
    have prime_of_class (a : ℕ) (ha : classOf a = 1) : a.Prime := by
      by_contra h
      by_cases he : a = 1 <;> simp [classOf, he, h] at ha
    have composite_of_class (a : ℕ) (ha : classOf a = 2) : a ≠ 1 ∧ ¬ a.Prime := by
      by_cases he : a = 1
      · simp [classOf, he] at ha
      · by_cases hp : a.Prime
        · simp [classOf, he, hp] at ha
        · exact ⟨he, hp⟩
    have hX : n / s ≤ n := Nat.div_le_self n s
    interval_cases k
    · obtain ⟨x, hxlo, hxhi, hxy⟩ := hRough (block 0 / s)
      have hn : 1 ≤ n / s := (Nat.le_div_iff_mul_le hs).2 (by simpa using hsn)
      refine ⟨fun _ => x, ?_, ?_⟩
      · intro a b _
        exact Subtype.ext ((one_of_class a.val a.property.2.2.2).trans
          (one_of_class b.val b.property.2.2.2).symm)
      · intro a
        refine ⟨hxlo, hxhi.trans ?_, ?_, hxy⟩
        · exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left B hn) _
        · rw [one_of_class a.val a.property.2.2.2]
          exact one_dvd _
    · obtain ⟨g, hgInj, hg⟩ := hPrime (n / s) hX (block 1 / s)
      let inc (a : {a : ℕ // a ≤ n / s ∧ 0 < a ∧
          (∀ p : ℕ, p.Prime → p ∣ a → y < p) ∧ classOf a = 1}) :
          {a : ℕ // a ≤ n / s ∧ y < a ∧ a.Prime} :=
        ⟨a.val, a.property.1,
          a.property.2.2.1 a.val (prime_of_class a.val a.property.2.2.2) (dvd_refl _),
          prime_of_class a.val a.property.2.2.2⟩
      have hInc : Function.Injective inc := by
        intro a b h
        have hVal := congrArg Subtype.val h
        exact Subtype.ext hVal
      exact ⟨g ∘ inc, hgInj.comp hInc, fun a => hg (inc a)⟩
    · obtain ⟨g, hgInj, hg⟩ := hComposite (n / s) hX (block 2 / s)
      let inc (a : {a : ℕ // a ≤ n / s ∧ 0 < a ∧
          (∀ p : ℕ, p.Prime → p ∣ a → y < p) ∧ classOf a = 2}) :
          {a : ℕ // a ≤ n / s ∧ 2 ≤ a ∧ ¬ a.Prime ∧
              (∀ p : ℕ, p.Prime → p ∣ a → y < p)} :=
        ⟨a.val, a.property.1, by
          have h := (composite_of_class a.val a.property.2.2.2).1
          have ha := a.property.2.1
          omega, (composite_of_class a.val a.property.2.2.2).2, a.property.2.2.1⟩
      have hInc : Function.Injective inc := by
        intro a b h
        have hVal := congrArg Subtype.val h
        exact Subtype.ext hVal
      exact ⟨g ∘ inc, hgInj.comp hInc, fun a => hg (inc a)⟩
  choose s a hs ha hd hsy hay using
    fun i : Fin n => split_factors y (i.val + 1) (Nat.succ_pos _)
  have hsn (i : Fin n) : s i ≤ n := by
    calc
      s i = s i * 1 := by simp
      _ ≤ s i * a i := Nat.mul_le_mul_left _ (ha i)
      _ = i.val + 1 := (hd i).symm
      _ ≤ n := i.isLt
  have han (i : Fin n) : a i ≤ n / s i := by
    apply (Nat.le_div_iff_mul_le (hs i)).2
    rw [Nat.mul_comm, ← hd i]
    exact i.isLt
  have hk (v : ℕ) : classOf v ≤ 2 := by
    by_cases h : v = 1 <;> by_cases hp : v.Prime <;> simp [classOf, h, hp]
  let Key := {sk : ℕ × ℕ // 0 < sk.1 ∧ sk.1 ≤ n ∧ sk.2 ≤ 2}
  let Args (sk : Key) := {v : ℕ // v ≤ n / sk.val.1 ∧ 0 < v ∧
    (∀ p : ℕ, p.Prime → p ∣ v → y < p) ∧ classOf v = sk.val.2}
  let key (i : Fin n) : Key := ⟨(s i, classOf (a i)), hs i, hsn i, hk (a i)⟩
  choose g hgInj hg using
    fun sk : Key => hMatch sk.val.1 sk.val.2 sk.property.1 sk.property.2.1 sk.property.2.2
  let arg (i : Fin n) : Args (key i) := ⟨a i, han i, ha i, hay i, rfl⟩
  let v (i : Fin n) := g (key i) (arg i)
  let out (i : Fin n) := s i * v i
  have hv (i : Fin n) : block (classOf (a i)) / s i < v i ∧
      v i ≤ block (classOf (a i)) / s i + B * (n / s i) ∧ a i ∣ v i ∧
      (∀ p : ℕ, p.Prime → p ∣ v i → y < p) := hg (key i) (arg i)
  have hOut (i : Fin n) :
      block (classOf (a i)) < out i ∧ out i ≤ block (classOf (a i) + 1) := by
    have hl := (hv i).1
    have hu := (hv i).2.1
    refine ⟨?_, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul (hs i)).mp hl |>.trans_eq (Nat.mul_comm _ _)
    · change s i * v i ≤ m + (classOf (a i) + 1) * (B * n)
      calc
        s i * v i ≤ s i * (block (classOf (a i)) / s i + B * (n / s i)) :=
          Nat.mul_le_mul_left _ hu
        _ = s i * (block (classOf (a i)) / s i) + B * (s i * (n / s i)) := by ring
        _ ≤ block (classOf (a i)) + B * n :=
          Nat.add_le_add (Nat.mul_div_le (block (classOf (a i))) (s i))
            (Nat.mul_le_mul_left B (Nat.mul_div_le n (s i)))
        _ = m + (classOf (a i) + 1) * (B * n) := by simp [block, Nat.add_mul, Nat.add_assoc]
  refine ⟨out, ?_, ?_⟩
  · intro i j hij
    have hsij : s i = s j := by
      apply Nat.dvd_antisymm
      · have h : s i ∣ out j := by
          rw [← hij]
          exact dvd_mul_right (s i) (v i)
        exact (supported_coprime (hsy i) (hv j).2.2.2).dvd_of_dvd_mul_right h
      · have h : s j ∣ out i := by
          rw [hij]
          exact dvd_mul_right (s j) (v j)
        exact (supported_coprime (hsy j) (hv i).2.2.2).dvd_of_dvd_mul_right h
    have hBlock (b c : ℕ) (h : b ≤ c) : block b ≤ block c :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
    have hkij : classOf (a i) = classOf (a j) := by
      apply le_antisymm
      · by_contra! h
        have hji := (hOut j).2.trans (hBlock _ _ (show classOf (a j) + 1 ≤ classOf (a i) from h))
        rw [← hij] at hji
        exact (not_lt_of_ge hji) (hOut i).1
      · by_contra! h
        have hij' := (hOut i).2.trans (hBlock _ _ (show classOf (a i) + 1 ≤ classOf (a j) from h))
        rw [hij] at hij'
        exact (not_lt_of_ge hij') (hOut j).1
    have hkey : key i = key j := Subtype.ext (Prod.ext hsij hkij)
    have hvij : v i = v j := by
      change s i * v i = s j * v j at hij
      rw [← hsij] at hij
      exact Nat.eq_of_mul_eq_mul_left (hs i) hij
    have haij : a i = a j := by
      have congr_inputs (ki kj : Key) (x : Args ki) (z : Args kj)
          (heq : ki = kj) (hv : g ki x = g kj z) : x.val = z.val := by
        subst kj
        exact congrArg Subtype.val (hgInj ki hv)
      exact congr_inputs _ _ (arg i) (arg j) hkey hvij
    apply Fin.ext
    have hh : i.val + 1 = j.val + 1 := by
      calc
        i.val + 1 = s i * a i := hd i
        _ = s j * a j := by rw [hsij, haij]
        _ = j.val + 1 := (hd j).symm
    omega
  · intro i
    have hlo : m ≤ block (classOf (a i)) := Nat.le_add_right _ _
    have hhi : block (classOf (a i) + 1) ≤ m + 3 * (B * n) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have := hk (a i); omega)) _
    refine ⟨hlo.trans_lt (hOut i).1, ?_, ?_⟩
    · have := (hOut i).2.trans hhi
      omega
    · rw [hd i]
      exact Nat.mul_dvd_mul_left _ (hv i).2.2.1

private theorem eventually_block_bound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((3 * (⌈(n : ℝ) ^ (ε / 2)⌉₊ * n) + 1 : ℕ) : ℝ) ≤
        (n : ℝ) ^ (1 + ε) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually (eventually_ge_atTop 7), eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le (ε / 2))
  calc
    ((3 * (⌈(n : ℝ) ^ (ε / 2)⌉₊ * n) + 1 : ℕ) : ℝ)
        ≤ 7 * ((n : ℝ) * (n : ℝ) ^ (ε / 2)) := by
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hc.le hnpos.le,
            mul_le_mul_of_nonneg_left hn hnpos.le]
    _ ≤ (n : ℝ) * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by
      have h := mul_le_mul_of_nonneg_right hn
        (mul_nonneg hnpos.le (Real.rpow_nonneg hnpos.le (ε / 2)))
      nlinarith only [h]
    _ = (n : ℝ) ^ (1 + ε) := by
      rw [← Real.rpow_add hnpos, show ε / 2 + ε / 2 = ε by ring,
        Real.rpow_add hnpos, Real.rpow_one]

/-- Prime cofactors can be matched to integers with no prime divisor at most the cutoff. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    let y := ⌊(n : ℝ) ^ (η / 4)⌋₊
    let B := ⌈(n : ℝ) ^ η⌉₊
    ∀ X : ℕ, X ≤ n → ∀ m : ℕ,
      ∃ f : {a : ℕ // a ≤ X ∧ y < a ∧ a.Prime} → ℕ,
        Function.Injective f ∧ ∀ a,
          m < f a ∧ f a ≤ m + B * X ∧ a.val ∣ f a ∧
            (∀ p : ℕ, p.Prime → p ∣ f a → y < p)

/-- Composite cofactors can be matched within the same rough integers. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    let y := ⌊(n : ℝ) ^ (η / 4)⌋₊
    let B := ⌈(n : ℝ) ^ η⌉₊
    ∀ X : ℕ, X ≤ n → ∀ m : ℕ,
      ∃ f : {a : ℕ // a ≤ X ∧ 2 ≤ a ∧ ¬ a.Prime ∧
        (∀ p : ℕ, p.Prime → p ∣ a → y < p)} → ℕ,
        Function.Injective f ∧ ∀ a,
          m < f a ∧ f a ≤ m + B * X ∧ a.val ∣ f a ∧
            (∀ p : ℕ, p.Prime → p ∣ f a → y < p)

theorem main : H1 → H2 → type_of% @Erdos711.erdos_711.parts.i := by
  classical
  intro hPrime hComposite
  have hRate (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop, ∃ L : ℕ, (∀ m, Erdos711.HasDivisibleDistinctTuple n m L) ∧
        (L : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
    let e := min ε 1
    have he : 0 < e := lt_min hε one_pos
    have heta : 0 < e / 2 := by positivity
    have hsqrt : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp tendsto_natCast_atTop_atTop
    filter_upwards [hPrime (e / 2) heta, hComposite (e / 2) heta,
      eventually_block_bound he, hsqrt.eventually (eventually_ge_atTop 2),
      eventually_ge_atTop (2 : ℕ)] with n hp hc hb hs hn
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hnonneg : 0 ≤ (n : ℝ) := by positivity
    have hCut : 2 * ⌊(n : ℝ) ^ (e / 2 / 4)⌋₊ ≤ n := by
      have hpow : (n : ℝ) ^ (e / 2 / 4) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        have := min_le_right ε (1 : ℝ)
        linarith
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
        rw [← Real.rpow_add (by positivity : 0 < (n : ℝ))]
        norm_num
      have hfloor := Nat.floor_le (Real.rpow_nonneg hnonneg (e / 2 / 4))
      have hs' : 2 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hs
      have hbound := mul_le_mul_of_nonneg_right hs' (Real.rpow_nonneg hnonneg (1 / 2 : ℝ))
      rw [hsq] at hbound
      exact_mod_cast (show 2 * (⌊(n : ℝ) ^ (e / 2 / 4)⌋₊ : ℝ) ≤ (n : ℝ) by linarith)
    refine ⟨_, assemble n _ _ hp hc hn hCut, hb.trans ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hn1 (add_le_add_right (min_le_left ε 1) 1)
  let length (n : ℕ) : ℕ :=
    if h : ∃ L, ∀ m, Erdos711.HasDivisibleDistinctTuple n m L then Nat.find h else 1
  have hSpec (n : ℕ) (h : ∃ L, ∀ m, Erdos711.HasDivisibleDistinctTuple n m L) :
      ∀ m, Erdos711.HasDivisibleDistinctTuple n m (length n) := by
    simpa [length, dif_pos h] using Nat.find_spec h
  have hMin (n L : ℕ) (hL : ∀ m, Erdos711.HasDivisibleDistinctTuple n m L) :
      length n ≤ L := by
    have h : ∃ L, ∀ m, Erdos711.HasDivisibleDistinctTuple n m L := ⟨L, hL⟩
    simpa [length, dif_pos h] using Nat.find_min' h hL
  have hPos (n : ℕ) (hn : 2 ≤ n)
      (h : ∃ L, ∀ m, Erdos711.HasDivisibleDistinctTuple n m L) : 0 < length n := by
    obtain ⟨f, _, hf⟩ := hSpec n h 0
    have hf0 := (hf ⟨0, by omega⟩).2.1
    omega
  let err (n : ℕ) : ℝ := max 0 (Real.log (length n) / Real.log n - 1)
  have hLog (n : ℕ) (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hErr (n : ℕ) : 0 ≤ err n := le_max_left _ _
  refine ⟨err, ?_, ?_⟩
  · rw [isLittleO_iff]
    intro ε hε
    filter_upwards [hRate ε hε, eventually_ge_atTop (2 : ℕ)] with n ⟨L, hL, hb⟩ hn
    have hlen : 0 < (length n : ℝ) :=
      Nat.cast_pos.mpr (hPos n hn ⟨L, hL⟩)
    have hLn : (length n : ℝ) ≤ (n : ℝ) ^ (1 + ε) :=
      (Nat.cast_le.mpr (hMin n L hL)).trans hb
    have hlog := Real.log_le_log hlen hLn
    rw [Real.log_rpow (by positivity : 0 < (n : ℝ))] at hlog
    have hratio := (div_le_iff₀ (hLog n hn)).2 hlog
    rw [Real.norm_of_nonneg (hErr n), norm_one, mul_one]
    exact max_le hε.le (by linarith)
  · filter_upwards [hRate 1 one_pos, eventually_ge_atTop (2 : ℕ)] with n ⟨L, hL, _⟩ hn
    have h : ∃ L, ∀ m, Erdos711.HasDivisibleDistinctTuple n m L := ⟨L, hL⟩
    have hlen : 0 < (length n : ℝ) := Nat.cast_pos.mpr (hPos n hn h)
    intro m
    refine ⟨length n, hSpec n h m, ?_⟩
    change (length n : ℝ) ≤ (n : ℝ) ^ (1 + err n)
    rw [Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ)), ← Real.exp_log hlen]
    apply Real.exp_le_exp.mpr
    have hratio : Real.log (length n) / Real.log (n : ℝ) ≤ 1 + err n := by
      have hmax := le_max_right (0 : ℝ) (Real.log (length n) / Real.log n - 1)
      change _ ≤ 1 + max 0 (Real.log (length n) / Real.log n - 1)
      linarith
    simpa [mul_comm] using (div_le_iff₀ (hLog n hn)).1 hratio

end OMA.R_Erdos711_erdos_711_parts_i_R1
