import OMAStatements.S_oeis_a006014

/-!
# Kurkov's dyadic prefix identity for A006014

Credit: @CubeJerry.

The auxiliary finite binomial identity for A379818 is adapted from agchua's
prior proof, PR24658. The new result connects that identity to the canonical
A006014 recurrence using a finite operator calculation and formal power series.
The statement's array definitions are unchanged.
-/

open scoped BigOperators

open OMA.S_oeis_a006014 Finset

namespace A006014Arrays

theorem getD_push_lt (t : Array ℕ) (v i : ℕ) (hi : i<t.size) :
    (t.push v).getD i 0=t.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hi]

theorem getD_push_size (t : Array ℕ) (v : ℕ) :
    (t.push v).getD t.size 0=v := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]

theorem firstTable_size : ∀ n : ℕ, (firstTable n).size=n+1
  | 0 => rfl
  | 1 => rfl
  | n+2 => by simp only [firstTable, Array.size_push, firstTable_size (n+1)]

theorem secondTable_size : ∀ n : ℕ, (secondTable n).size=n+1
  | 0 => rfl
  | n+1 => by
    simp only [secondTable]
    split <;> simp only [Array.size_push, secondTable_size n]

theorem firstTable_push (n : ℕ) : ∃ v, firstTable (n+1)=(firstTable n).push v := by
  cases n with
  | zero => exact ⟨1,rfl⟩
  | succ n => exact ⟨_,rfl⟩

theorem secondTable_push (n : ℕ) : ∃ v, secondTable (n+1)=(secondTable n).push v := by
  simp only [secondTable]
  split <;> exact ⟨_,rfl⟩

theorem firstTable_getD {m n : ℕ} (hn : n ≤ m) :
    (firstTable m).getD n 0=a006014 n := by
  induction m with
  | zero =>
    have : n=0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases he : n=m+1
    · subst n; rfl
    · have hnm : n ≤ m := by omega
      obtain ⟨v,hv⟩ := firstTable_push m
      rw [hv, getD_push_lt _ _ _ (by rw [firstTable_size]; omega)]
      exact ih hnm

theorem secondTable_getD {m n : ℕ} (hn : n ≤ m) :
    (secondTable m).getD n 0=a379818 n := by
  induction m with
  | zero =>
    have : n=0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases he : n=m+1
    · subst n; rfl
    · have hnm : n ≤ m := by omega
      obtain ⟨v,hv⟩ := secondTable_push m
      rw [hv, getD_push_lt _ _ _ (by rw [secondTable_size]; omega)]
      exact ih hnm

@[simp] theorem a006014_zero : a006014 0=0 := rfl
@[simp] theorem a006014_one : a006014 1=1 := rfl
@[simp] theorem a379818_zero : a379818 0=1 := rfl

theorem first_recurrence (n : ℕ) :
    a006014 (n+2)=(n+2)*a006014 (n+1)+
      ∑ i ∈ range n, a006014 (i+1)*a006014 (n-i) := by
  change ((firstTable (n+1)).push _).getD (n+2) 0=_
  conv_lhs => arg 2; rw [← firstTable_size (n+1)]
  rw [getD_push_size, firstTable_getD (by omega)]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [firstTable_getD (by omega), firstTable_getD (by omega)]

theorem a025480_le (n : ℕ) : a025480 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [a025480]
    split_ifs with hn
    · omega
    · have hp : 0<n := by omega
      exact (ih (n/2) (by omega)).trans (by omega)

theorem a025480_even (n : ℕ) : a025480 (2*n)=n := by
  rw [a025480, if_pos (by omega)]
  omega

theorem a025480_odd (n : ℕ) : a025480 (2*n+1)=a025480 n := by
  rw [a025480, if_neg (by omega)]
  congr 1
  omega

theorem a025480_shift (e k : ℕ) : a025480 (2^e*(2*k+1)-1)=k := by
  induction e with
  | zero => simpa using a025480_even k
  | succ e ih =>
    have hp : 0<2^e*(2*k+1) := by positivity
    have he : 2^(e+1)*(2*k+1)-1=2*(2^e*(2*k+1)-1)+1 := by
      rw [pow_succ]
      rw [show 2^e*2*(2*k+1)=2*(2^e*(2*k+1)) by ring]
      omega
    rw [he, a025480_odd, ih]

theorem second_odd (k : ℕ) : a379818 (2*k+1)=a379818 k := by
  change (secondTable (2*k+1)).getD (2*k+1) 0=_
  rw [secondTable, if_pos (by omega)]
  conv_lhs => arg 2; rw [←secondTable_size (2*k)]
  rw [getD_push_size]
  rw [show (2*k+1)/2=k by omega, secondTable_getD (by omega)]

theorem second_even (k : ℕ) (hk : 0<k) :
    a379818 (2*k)=a379818 k+a379818 (k-2^(k.factorization 2))+
      a379818 (2*k-2^(k.factorization 2))+a379818 (a025480 (k-1)) := by
  have hk2 : 2*k=(2*k-1)+1 := by omega
  change (secondTable (2*k)).getD (2*k) 0=_
  rw [hk2, secondTable]
  simp only [←hk2, if_neg (show ¬2*k%2=1 by omega), show 2*k/2=k by omega]
  conv_lhs => arg 2; rw [hk2, ←secondTable_size (2*k-1)]
  rw [getD_push_size]
  have hp : 0<2^(k.factorization 2) := Nat.two_pow_pos _
  have ha := a025480_le (k-1)
  rw [secondTable_getD (by omega), secondTable_getD (by omega),
      secondTable_getD (by omega), secondTable_getD (by omega)]

theorem factorization_odd_mul (e k : ℕ) : (2^e*(2*k+1)).factorization 2=e := by
  rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (show ¬2∣2*k+1 by omega), add_zero]

end A006014Arrays

/-!
The finite binomial identity below is adapted from the checked proof of
A379818 by agchua, PR24658. We instantiate its argument directly against the
canonical array-defined sequence of A006014, and use rational coefficients.
This known auxiliary identity is credited prior work, not the new dyadic-sum result.
-/

open OMA.S_oeis_a006014 A006014Arrays

namespace A006014Binomial

/-- The coefficient binomial(p+2, j+1) - binomial(p, j). -/
def c (p j : ℕ) : ℚ := (((Nat.choose (p + 2) (j + 1) : ℕ) : ℚ) - ((Nat.choose p j : ℕ) : ℚ))

theorem c_base : c 0 0 = 1 := by norm_num [c]

theorem c_zero (p : ℕ) : c (p + 1) 0 = c p 0 + 1 := by
  rw [c, c, zero_add, Nat.choose_one_right, Nat.choose_one_right, Nat.choose_zero_right,
    Nat.choose_zero_right]
  push_cast
  ring

theorem c_succ (p j : ℕ) : c (p + 1) (j + 1) = c p j + c p (j + 1) := by
  rw [c, c, c, show p + 1 + 2 = p + 2 + 1 by ring, Nat.choose_succ_succ' (p + 2) (j + 1),
    Nat.choose_succ_succ' p j]
  push_cast
  ring

theorem c_top (p : ℕ) : c p (p + 1) = 1 := by
  rw [c, show p + 1 + 1 = p + 2 by ring, Nat.choose_self,
    Nat.choose_eq_zero_of_lt (show p < p + 1 by omega), Nat.cast_one, Nat.cast_zero, sub_zero]

theorem comb_step (p : ℕ) (X : ℕ → ℚ) :
    ∑ j ∈ Finset.range (p + 1 + 1), c (p + 1) j * X j =
      ∑ j ∈ Finset.range (p + 1), c p j * X j + X (p + 1) +
        ∑ j ∈ Finset.range (p + 1), c p j * X (j + 1) + X 0 := by
  rw [Finset.sum_range_succ' (fun j => c (p + 1) j * X j) (p + 1)]
  simp only [c_succ, c_zero, add_mul, Finset.sum_add_distrib]
  have h2 : ∑ j ∈ Finset.range (p + 1), c p (j + 1) * X (j + 1) + c p 0 * X 0 =
      ∑ j ∈ Finset.range (p + 1), c p j * X j + X (p + 1) := by
    rw [← Finset.sum_range_succ' (fun j => c p j * X j) (p + 1), Finset.sum_range_succ, c_top,
      one_mul]
  linear_combination h2

theorem binomial_identity (m : ℕ) : ∀ k : ℕ, (a379818 (2 ^ m * (2 * k + 1)) : ℚ) =
    ∑ j ∈ Finset.range (m + 1), c m j * (a379818 (2 ^ j * k) : ℚ) := by
  induction m with
  | zero =>
    intro k
    simp [second_odd, c_base]
  | succ p ih =>
    intro k
    have hpos : 0 < 2 ^ p * (2 * k + 1) := by positivity
    have hN : 2 ^ (p + 1) * (2 * k + 1) = 2 * (2 ^ p * (2 * k + 1)) := by ring
    have e2 : 2 ^ p * (2 * k + 1) - 2 ^ p = 2 ^ (p + 1) * k := Nat.sub_eq_of_eq_add (by ring)
    have e3 : 2 * (2 ^ p * (2 * k + 1)) - 2 ^ p = 2 ^ p * (2 * (2 * k) + 1) :=
      Nat.sub_eq_of_eq_add (by ring)
    have h4 : ∑ j ∈ Finset.range (p + 1), c p j * (a379818 (2 ^ j * (2 * k)) : ℚ) =
        ∑ j ∈ Finset.range (p + 1), c p j * (a379818 (2 ^ (j + 1) * k) : ℚ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show 2 ^ j * (2 * k) = 2 ^ (j + 1) * k by ring]
    have h5 : (a379818 (2 ^ 0 * k) : ℚ) = a379818 k := by
      rw [pow_zero, one_mul]
    rw [hN, second_even _ hpos, factorization_odd_mul, a025480_shift, e2, e3, Nat.cast_add, Nat.cast_add,
      Nat.cast_add, ih k, ih (2 * k), comb_step p (fun j => (a379818 (2 ^ j * k) : ℚ)), h4]
    linear_combination -h5


end A006014Binomial

open Finset

namespace A006014Operator

def coeff (j r : ℕ) : ℚ := ((j+2).choose (r+1) : ℚ) - (j.choose r : ℚ)

def op (v : ℕ → ℚ) (j : ℕ) : ℚ :=
  v (j+1) + ∑ r ∈ range (j+1), coeff j r * v r

def u : ℕ → ℚ
  | 0 => 1
  | n+1 => ((n : ℚ)^2+n+1)*u n/(n+1)

@[simp] lemma u_zero : u 0 = 1 := rfl

lemma u_rec (n : ℕ) : ((n+1 : ℕ) : ℚ)*u (n+1)=((n:ℚ)^2+n+1)*u n := by
  have hn : (n : ℚ)+1 ≠ 0 := by positivity
  rw [u]
  push_cast
  field_simp

def dyadic (B : ℕ → ℚ) (n j : ℕ) : ℚ :=
  ∑ k ∈ range (2^n), B (2^j*k)

lemma sum_range_twice (g : ℕ → ℚ) (n : ℕ) :
    (∑ k ∈ range (2*n), g k) = ∑ k ∈ range n, (g (2*k)+g (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    rw [sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

lemma prefix_zero (B : ℕ → ℚ) (h0 : B 0 = 1) (j : ℕ) : dyadic B 0 j = 1 := by
  simp [dyadic, h0]

lemma prefix_succ (B : ℕ → ℚ)
    (hbin : ∀ j k : ℕ, B (2^j*(2*k+1)) =
      ∑ r ∈ range (j+1), coeff j r * B (2^r*k)) (n j : ℕ) :
    dyadic B (n+1) j = op (dyadic B n) j := by
  unfold dyadic op
  rw [pow_succ', sum_range_twice]
  simp_rw [hbin, sum_add_distrib]
  congr 1
  · apply sum_congr rfl
    intro k hk
    congr 1
    rw [pow_succ]
    ring
  · rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    rw [mul_sum]

lemma op_power_succ (x : ℚ) (j : ℕ) :
    op (fun r => x^r) (j+1) = (x+1)*op (fun r => x^r) j+1 := by
  have h := A006014Binomial.comb_step j (fun r => x^r)
  change (∑ r ∈ range (j+1+1), coeff (j+1) r*x^r) = _ at h
  have hs : (∑ r ∈ range (j+1), A006014Binomial.c j r*x^(r+1)) =
      x*∑ r ∈ range (j+1), coeff j r*x^r := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    change coeff j r*x^(r+1) = x*(coeff j r*x^r)
    ring
  unfold op
  rw [h, hs]
  change x^(j+1+1) + ((∑ r ∈ range (j+1), coeff j r*x^r) + x^(j+1) +
    x*(∑ r ∈ range (j+1), coeff j r*x^r) + x^0) = _
  ring

lemma op_power (x : ℚ) (j : ℕ) :
    x*op (fun r => x^r) j+1=(x^2+x+1)*(x+1)^j := by
  induction j with
  | zero => norm_num [op, coeff]; ring
  | succ j ih =>
    rw [op_power_succ, pow_succ]
    linear_combination (x+1)*ih

lemma op_sum_mul (a : ℕ → ℚ) (v : ℕ → ℕ → ℚ) (n j : ℕ) :
    op (fun k => ∑ r ∈ range n, a r*v r k) j =
      ∑ r ∈ range n, a r*op (v r) j := by
  unfold op
  simp_rw [mul_sum, mul_add, sum_add_distrib]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  ring

lemma op_mul (a : ℚ) (v : ℕ → ℚ) (j : ℕ) :
    op (fun k => a*v k) j = a*op v j := by
  unfold op
  rw [mul_add, mul_sum]
  congr 1
  apply sum_congr rfl
  intro r hr
  ring

lemma convolution_of_rec (F : ℕ → ℕ → ℚ)
    (h0 : ∀ j, F 0 j = 1)
    (hrec : ∀ n j, F (n+1) j = op (F n) j) (n : ℕ) :
    ∀ j : ℕ, (∑ r ∈ range (n+1), u r*F (n-r) j) =
      ((n+1 : ℕ) : ℚ)*u (n+1)*((n+1 : ℕ) : ℚ)^j := by
  induction n with
  | zero => intro j; simp [h0, u]
  | succ n ih =>
    intro j
    rw [sum_range_succ]
    have hs : (∑ r ∈ range (n+1), u r*F (n+1-r) j) =
        op (fun k => ∑ r ∈ range (n+1), u r*F (n-r) k) j := by
      rw [op_sum_mul]
      apply sum_congr rfl
      intro r hr
      have hr' := Finset.mem_range.mp hr
      rw [show n+1-r=(n-r)+1 by omega, hrec]
    rw [hs, show n+1-(n+1)=0 by omega, h0]
    have hfun : (fun k => ∑ r ∈ range (n+1), u r*F (n-r) k) =
        (fun k => ((n+1 : ℕ) : ℚ)*u (n+1)*((n+1 : ℕ) : ℚ)^k) := funext ih
    rw [hfun, op_mul]
    have hp := congrArg (fun z : ℚ => u (n+1)*z) (op_power ((n+1 : ℕ) : ℚ) j)
    have hu := congrArg (fun z : ℚ => z*(((n+1+1 : ℕ):ℚ)^j)) (u_rec (n+1))
    simp only [Nat.cast_add, Nat.cast_one] at *
    nlinarith [hp, hu]

lemma prefix_convolution (B : ℕ → ℚ) (h0 : B 0=1)
    (hbin : ∀ j k : ℕ, B (2^j*(2*k+1)) =
      ∑ r ∈ range (j+1), coeff j r*B (2^r*k)) (n : ℕ) :
    (∑ r ∈ range (n+1), u r*dyadic B (n-r) 0) = ((n+1 : ℕ):ℚ)*u (n+1) := by
  simpa only [pow_zero, mul_one] using
    convolution_of_rec (dyadic B) (prefix_zero B h0) (prefix_succ B hbin) n 0

end A006014Operator

open OMA.S_oeis_a006014 A006014Arrays Finset

namespace A006014Uniqueness

def dyadic (n : ℕ) : ℚ := ∑ k ∈ range (2^n), (a379818 k:ℚ)

@[simp] theorem dyadic_zero : dyadic 0=1 := by simp [dyadic]

theorem eq_shifted (S : ℕ→ℚ) (h0 : S 0=1)
    (hrec : ∀ n, S (n+1)=((n:ℚ)+2)*S n+
      ∑ i ∈ range n, S i*S (n-1-i)) :
    ∀ n, (a006014 (n+1):ℚ)=S n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using h0.symm
    | succ m =>
      rw [show m+1+1=m+2 by omega, first_recurrence, hrec m]
      push_cast
      rw [ih m (by omega)]
      congr 1
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [ih i (by omega)]
      rw [show m-i=(m-1-i)+1 by omega, ih (m-1-i) (by omega)]

theorem solution_of_recurrence
    (hrec : ∀ n, dyadic (n+1)=((n:ℚ)+2)*dyadic n+
      ∑ i ∈ range n, dyadic i*dyadic (n-1-i)) :
    ∀ n : ℕ, 1 ≤ n → a006014 n=∑ k ∈ range (2^(n-1)), a379818 k := by
  intro n hn
  have h := eq_shifted dyadic dyadic_zero hrec (n-1)
  rw [show n-1+1=n by omega] at h
  unfold dyadic at h
  exact_mod_cast h

end A006014Uniqueness

open OMA.S_oeis_a006014 Finset

namespace A006014Bridge

theorem convolution (n : ℕ) :
    (∑ r ∈ range (n+1), A006014Operator.u r*A006014Uniqueness.dyadic (n-r)) =
      ((n : ℚ)+1)*A006014Operator.u (n+1) := by
  have h := A006014Operator.prefix_convolution
    (fun k => (a379818 k : ℚ)) (by simp) A006014Binomial.binomial_identity n
  simpa only [A006014Operator.dyadic, A006014Uniqueness.dyadic,
    pow_zero, one_mul, Nat.cast_add, Nat.cast_one] using h

end A006014Bridge

open PowerSeries Finset

namespace A006014FPS

noncomputable abbrev D := PowerSeries.derivative ℚ

lemma coeff_X_mul' (F : PowerSeries ℚ) (n : ℕ) :
    coeff n (X*F)=if 1 ≤ n then coeff (n-1) F else 0 := by
  simpa using coeff_X_pow_mul' F 1 n

theorem recurrence (u S : ℕ→ℚ) (hu0 : u 0=1)
    (hrec : ∀ n : ℕ, ((n:ℚ)+1)*u (n+1)=((n:ℚ)^2+n+1)*u n)
    (hconv : ∀ n : ℕ, (∑ r ∈ range (n+1), u r*S (n-r))=((n:ℚ)+1)*u (n+1)) :
    ∀ n : ℕ, S (n+1)=((n:ℚ)+2)*S n+∑ i ∈ range n, S i*S (n-1-i) := by
  let U : PowerSeries ℚ := mk u
  let G : PowerSeries ℚ := mk S
  have hUG : U*G=D U := by
    ext n
    rw [coeff_mul, coeff_derivative,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i U*coeff j G)]
    simp only [U, G, coeff_mk]
    rw [hconv n]
    ring
  have hU : U≠0 := by
    intro h
    have hc := congrArg (coeff 0) h
    simp [U, hu0] at hc
  have hODE : D U=U+C 2*(X*D U)+X^2*D (D U) := by
    ext n
    cases n with
    | zero =>
      simpa [coeff_X_mul', coeff_X_pow_mul', coeff_derivative, U] using hrec 0
    | succ n =>
      cases n with
      | zero =>
        have h := hrec 1
        norm_num [coeff_X_mul', coeff_X_pow_mul', coeff_derivative, U] at h ⊢
        linarith
      | succ n =>
        have h := hrec (n+2)
        have h2 : 2 ≤ n+2 := by omega
        simp [coeff_X_pow_mul', coeff_derivative, U, h2]
        push_cast at h
        nlinarith [h]
  have hDD : D (D U)=U*(G^2+D G) := by
    rw [←hUG, Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [←hUG]
    ring
  have hRiccati : G=1+C 2*(X*G)+X^2*D G+X^2*G^2 := by
    apply mul_left_cancel₀ hU
    calc
      U*G=D U := hUG
      _=U+C 2*(X*D U)+X^2*D (D U) := hODE
      _=U*(1+C 2*(X*G)+X^2*D G+X^2*G^2) := by
        rw [hDD, ←hUG]
        ring
  have hsquare (n : ℕ) : coeff n (G^2)=
      ∑ i ∈ range (n+1), S i*S (n-i) := by
    rw [pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i G*coeff j G)]
    simp only [G, coeff_mk]
  intro n
  have hc := congrArg (coeff (n+1)) hRiccati
  cases n with
  | zero =>
    simpa [coeff_X_mul', coeff_X_pow_mul', coeff_derivative, G] using hc
  | succ n =>
    have h2 : 2 ≤ n+2 := by omega
    simp [coeff_X_pow_mul', coeff_derivative, hsquare, G, h2] at hc
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    linear_combination hc

end A006014FPS

open OMA.S_oeis_a006014

namespace A006014Final

theorem solution : ∀ n : ℕ, 1  ≤  n →
    a006014 n = ∑ k ∈ Finset.range (2^(n-1)), a379818 k := by
  apply A006014Uniqueness.solution_of_recurrence
  apply A006014FPS.recurrence A006014Operator.u A006014Uniqueness.dyadic
    A006014Operator.u_zero
  · intro n
    simpa only [Nat.cast_add, Nat.cast_one] using A006014Operator.u_rec n
  · exact A006014Bridge.convolution

end A006014Final

theorem OMA.solution : type_of% @OMA.S_oeis_a006014.main := by
  exact A006014Final.solution
