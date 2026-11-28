import OMAStatements.S_mo_268590
-- Credit: @PanoramicaSystems

namespace CoffeeMonkey.DigitDrop

theorem moment_nil : ((([] : List Int).tails.tail.map List.sum).sum : Int) = 0 := rfl

/-- The sum of all proper suffix sums weights each digit by its index. -/
theorem moment_cons (x : Int) (s : List Int) :
    (((x :: s).tails.tail.map List.sum).sum : Int) =
      s.sum + (s.tails.tail.map List.sum).sum := by
  cases s <;> simp [List.tails]

theorem moment_append (a b : List Int) :
    ((a ++ b).tails.tail.map List.sum).sum = (a.tails.tail.map List.sum).sum + (b.tails.tail.map List.sum).sum + (a.length : Int) * b.sum := by
  induction a with
  | nil => simp
  | cons x a ih =>
    simp only [List.cons_append, moment_cons, List.sum_append, ih, List.length_cons, Int.natCast_add,
      Int.natCast_one]
    grind

theorem moment_reverse (s : List Int) :
    (s.reverse.tails.tail.map List.sum).sum + (s.tails.tail.map List.sum).sum = ((s.length : Int) - 1) * s.sum := by
  induction s with
  | nil => simp
  | cons x s ih =>
    simp only [List.reverse_cons, moment_append, moment_cons, moment_nil, List.sum_cons, List.sum_nil,
      List.length_reverse, List.length_cons, Int.natCast_add, Int.natCast_one]
    grind

theorem palindrome_moment {s : List Int} (h : s.reverse = s) :
    2 * (s.tails.tail.map List.sum).sum = ((s.length : Int) - 1) * s.sum := by
  have aux := moment_reverse s
  rw [h] at aux
  omega

/-- The quotient is integral; no restriction on word length or coefficients. -/
theorem taylor_first_order (b : Int) (s : List Int) :
    ∃ q : Int, s.foldr (fun x y => x + (b + 1) * y) 0 = s.sum + b * (s.tails.tail.map List.sum).sum + b^2 * q := by
  induction s with
  | nil => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(s.tails.tail.map List.sum).sum + (b + 1) * q, ?_⟩
    simp only [List.foldr, List.sum_cons, moment_cons, hq]
    grind

/-- Arithmetic core of the digit drop exclusion. The leading two digits in the
smaller palindrome are 1 and a, and its evaluation therefore has the given low
digits. Bounds on a and t are hypotheses. -/
theorem digit_drop_obstruction (b p a t r : Int) (s : List Int)
    (hlen : (s.length : Int) = p) (hpal : s.reverse = s)
    (heval : s.foldr (fun x y => x + (b + 1) * y) 0 = 1 + b * a + b^2 * r)
    (hsum : s.sum = 1 + b * t)
    (_hp : 0 < p) (hpar : p % 2 = 0) (hb : 3 * p ≤ b)
    (ha : 0 ≤ a) (ha' : 2 * a < 3 * p)
    (ht : 0 ≤ t) (ht' : t < p) : False := by
  have hd := palindrome_moment hpal
  obtain ⟨q, hq⟩ := taylor_first_order b s
  rw [heval, hsum] at hq
  rw [hlen, hsum] at hd
  have hb0 : b ≠ 0 := by omega
  have hz : b * (a - t - (s.tails.tail.map List.sum).sum + b * (r - q)) = 0 := by
    clear hd heval hsum hpar ha hb ha' ht ht' _hp hb0 hpal hlen
    grind
  have hk : a - t - (s.tails.tail.map List.sum).sum + b * (r - q) = 0 := by
    rcases Int.mul_eq_zero.mp hz with h | h
    · contradiction
    · exact h
  let k := (p - 1) * t + 2 * (q - r)
  have he : 2 * a - 2 * t - (p - 1) = b * k := by
    dsimp [k]
    clear hq hz heval hsum hpar ha hb ha' ht ht' _hp hb0 hpal hlen
    grind
  have hlo : -b < 2 * a - 2 * t - (p - 1) := by omega
  have hhi : 2 * a - 2 * t - (p - 1) < b := by omega
  have hk0 : k = 0 := by
    by_cases hn : k < 0
    · have h := Int.mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (show 0 ≤ b by omega)
      simp at h
      omega
    by_cases hpos : 0 < k
    · have h := Int.mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (show 0 ≤ b by omega)
      simp at h
      omega
    omega
  rw [hk0, Int.mul_zero] at he
  omega

end CoffeeMonkey.DigitDrop

namespace CoffeeMonkey.DigitDrop

theorem eval_nat_cast (b : Nat) (s : List Nat) :
    (s.map fun k : Nat => (k : Int)).foldr (fun x y => x + (b : Int) * y) 0 = (Nat.ofDigits b s : Nat) := by
  induction s with
  | nil => simp
  | cons a s ih => simp [Nat.ofDigits_cons, ih]

theorem digit_sum_bounds (b : Int) (s : List Int)
    (h : ∀ k ∈ s, 0 ≤ k ∧ k ≤ b) :
    0 ≤ s.sum ∧ s.sum ≤ (s.length : Int) * b := by
  induction s with
  | nil => simp
  | cons x s ih =>
    have hx := h x (by simp)
    have ht := ih (fun k hk => h k (by simp [hk]))
    simp only [List.sum_cons, List.length_cons, Int.natCast_add, Int.natCast_one,
      Int.add_mul, Int.one_mul]
    omega

/-- Larger-side hypotheses refer directly to the canonical digit expansion. -/
theorem canonical_obstruction (b p a N : Nat) (r : Int)
    (hlen : (Nat.digits (b+1) N).length = p)
    (hpal : (Nat.digits (b+1) N).reverse = Nat.digits (b+1) N)
    (heval : (N : Int) = 1 + (b : Int)*a + (b : Int)^2*r)
    (hp : 0 < p) (hpar : p%2 = 0) (hb : 3*p ≤ b) (ha : 2*a < 3*p) : False := by
  let s := (Nat.digits (b + 1) N).map fun k : Nat => (k : Int)
  have hslen : s.length = p := by simpa [s] using hlen
  have hrev : s.reverse = s := by simp only [s, ← List.map_reverse, hpal]
  have he : s.foldr (fun x y => x + ((b : Int) + 1) * y) 0 = (N : Int) := by
    have h := eval_nat_cast (b+1) (Nat.digits (b+1) N)
    simpa only [Nat.ofDigits_digits, Int.natCast_add, Int.natCast_one] using h
  have hbounds := digit_sum_bounds (b : Int) s (by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hk
    have hd := Nat.digits_lt_base (by omega : 1 < b+1) hv
    exact ⟨by omega, by omega⟩)
  rw [hslen] at hbounds
  obtain ⟨q, hq⟩ := taylor_first_order (b : Int) s
  rw [he, heval] at hq
  let t := (a : Int) - (s.tails.tail.map List.sum).sum + b * (r - q)
  have hsum : s.sum = 1 + b*t := by
    dsimp [t]
    clear hbounds hrev hpal he heval hp hpar hb ha
    grind
  have hbpos : (0 : Int) < b := by omega
  have ht : 0 ≤ t := by
    by_contra! hn
    have hm := Int.mul_le_mul_of_nonneg_left (show t ≤ -1 by omega) (show 0 ≤ (b : Int) by omega)
    simp only [Int.mul_neg, Int.mul_one] at hm
    omega
  have ht' : t < p := by
    by_contra! hn
    have hm := Int.mul_le_mul_of_nonneg_left hn (show 0 ≤ (b : Int) by omega)
    rw [Int.mul_comm (p : Int) (b : Int)] at hbounds
    omega
  exact digit_drop_obstruction (b : Int) (p : Int) (a : Int) t r s (by omega)
    hrev (he.trans heval) hsum (by omega) (by omega) (by omega) (by omega) (by omega) ht ht'

end CoffeeMonkey.DigitDrop

namespace CoffeeMonkey.DigitDrop

theorem adjacent_power_upper (b n : Nat) :
    (b+1)^(n+1) ≤ b^(n+1) + (n+1)*(b+1)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.mul_le_mul_left b ih
    simp only [Nat.pow_succ] at *
    grind

theorem adjacent_power_ratio (b p : Nat) (hbp : 3*p ≤ b) :
    2*(b+1)^p ≤ 3*b^p := by
  cases p with
  | zero => simp
  | succ n =>
    have hd := adjacent_power_upper b n
    have h := Nat.mul_le_mul_left (3*(b+1)) hd
    have ht := Nat.mul_le_mul_right ((b+1)^(n+1)) (show 3 * (n+1) ≤ b+1 by omega)
    apply Nat.le_of_mul_le_mul_left (c := b+1) _ (by omega)
    simp only [Nat.pow_succ] at *
    grind

theorem adjacent_power_gap (b p : Nat) (hp : 0 < p) (hbp : 3*p ≤ b) :
    2*(b+1)^p ≤ 2*b^p + 3*p*b^(p-1) := by
  cases p with
  | zero => omega
  | succ n =>
    have h := adjacent_power_upper b n
    have hr := adjacent_power_ratio b n (by omega)
    have ht := Nat.mul_le_mul_left (n+1) hr
    simp
    grind

theorem leading_pair_bounds (b p N : Nat)
    (hp : 0 < p) (hbp : 3*p ≤ b)
    (hlo : b^p ≤ N) (hhi : N < (b+1)^p)
    (htop : N/b^p = N%b)
    (htwo : N/b^(p-1) = N/b%b + b*(N%b)) :
    N%b = 1 ∧ 2*(N/b%b) < 3*p := by
  have hb : 0 < b := by omega
  have hratio := adjacent_power_ratio b p hbp
  have hpos : 0 < b^p := Nat.pow_pos hb
  have hdiv : N/b^p = 1 := Nat.div_eq_of_lt_le (by simpa using hlo) (by omega)
  have hlead : N%b = 1 := htop.symm.trans hdiv
  refine ⟨hlead, ?_⟩
  rw [hlead, Nat.mul_one] at htwo
  have hv := Nat.div_mul_le_self N (b^(p-1))
  rw [htwo] at hv
  have hs : (p-1).succ = p := by omega
  have he : b^(p-1) * b = b^p := by rw [← Nat.pow_succ, hs]
  have hgap := adjacent_power_gap b p hp hbp
  apply Nat.lt_of_mul_lt_mul_right (a := b^(p-1))
  grind

end CoffeeMonkey.DigitDrop

namespace CoffeeMonkey

theorem palindrome_ends {b n p : ℕ} (hb : 2 ≤ b) (hp : 0 < p)
    (hlen : (b.digits n).length = p+1) (hpal : (b.digits n).reverse = b.digits n) :
    0 < n % b ∧ n / b^p = n%b ∧
      n / b^(p-1) = n/b%b + b*(n%b) ∧
      n % b^2 = n%b + b*(n/b%b) := by
  cases hd : b.digits n with
  | nil => simp [hd] at hlen
  | cons u tail =>
    cases ht : tail with
    | nil => simp [hd, ht] at hlen; omega
    | cons v rest =>
      have h : b.digits n = u :: v :: rest := by simpa [ht] using hd
      have hl : rest.length + 1 = p := by simp [h] at hlen; omega
      have hr : b.digits n = rest.reverse ++ [v, u] := by
        calc b.digits n = (b.digits n).reverse := hpal.symm
             _ = rest.reverse ++ [v, u] := by simp [h, List.reverse_cons, List.append_assoc]
      have hu : u = n%b := by simpa [h] using Nat.getD_digits n 0 hb
      have hv : v = n/b%b := by simpa [h] using Nat.getD_digits n 1 hb
      have hn : n ≠ 0 := by rintro rfl; simp at h
      have huPos : 0 < u := by
        have hx := Nat.getLast_digit_ne_zero b hn
        have hlast : (b.digits n).getLast! = u := by simp [hr]
        rw [List.getLast!_of_getLast? (List.getLast?_eq_some_getLast
          (Nat.digits_ne_nil_iff_ne_zero.mpr hn))] at hlast
        omega
      refine ⟨hu ▸ huPos, ?_, ?_, ?_⟩
      · rw [Nat.self_div_pow_eq_ofDigits_drop p n hb, hr, ← hl, List.drop_append]
        have hdrop : rest.reverse.drop (rest.length + 1) = [] := List.drop_eq_nil_of_le (by simp)
        simp [hdrop, hu]
      · rw [Nat.self_div_pow_eq_ofDigits_drop (p-1) n hb, hr, ← hl]
        simp [Nat.ofDigits_cons, hu, hv]
      · rw [Nat.self_mod_pow_eq_ofDigits_take 2 n hb, h]
        simp [Nat.ofDigits_cons, hu, hv]

/-- If the longer representation has p+1 digits, the power-ratio inequality
    forces any drop across the adjacent bases to be exactly one digit. -/
theorem one_digit_drop {b n p : ℕ} (hb : 2 ≤ b) (hp : 0 < p)
    (hs : 2*(b+1)^p ≤ 3*b^p) (hlen : (b.digits n).length = p+1)
    (hdrop : ((b+1).digits n).length < (b.digits n).length) :
    ((b+1).digits n).length = p ∧ b^p ≤ n ∧ n < (b+1)^p := by
  have hlo : b^p ≤ n := (Nat.lt_digits_length_iff hb n).mp (by omega)
  have hhi : n < (b+1)^p := (Nat.digits_length_le_iff (by omega : 1 < b+1) n).mp (by omega)
  refine ⟨?_, hlo, hhi⟩
  cases p with
  | zero => omega
  | succ k =>
    have hb' : 2 ≤ b+1 := by omega
    have hmm := Nat.mul_le_mul_left ((b+1)^k) hb'
    rw [pow_succ] at hs
    have hlowpow : (b+1)^k ≤ b^(k+1) := by
      have hts : 2*((b+1)^k*2) ≤ 3*b^(k+1) := (Nat.mul_le_mul_left 2 hmm).trans hs
      omega
    have hlowlen := (Nat.lt_digits_length_iff (by omega : 1 < b+1) n).mpr (hlowpow.trans hlo)
    omega

theorem low_two_decomposition {b n a : ℕ} (h : n % b^2 = 1 + b*a) :
    (n : ℤ) = 1 + (b : ℤ)*a + (b : ℤ)^2*(n / b^2 : ℕ) := by
  have hv := Nat.mod_add_div n (b^2)
  rw [h] at hv
  exact_mod_cast hv.symm

end CoffeeMonkey

namespace CoffeeMonkey.DigitDrop

/-- In an adjacent palindromic pair, a drop from an odd digit count p+1
forces the starting base to be smaller than three times p. -/
theorem adjacent_palindrome_drop {b N p : ℕ} (hb : 2 ≤ b) (hp : 0 < p)
    (heven : p % 2 = 0) (hlen : (Nat.digits b N).length = p+1)
    (hs : (Nat.digits b N).reverse = Nat.digits b N)
    (hl : (Nat.digits (b+1) N).reverse = Nat.digits (b+1) N)
    (hdrop : (Nat.digits (b+1) N).length < (Nat.digits b N).length) : b < 3*p := by
  by_contra! hbig
  obtain ⟨hlen', hlo, hhi⟩ := CoffeeMonkey.one_digit_drop hb hp
    (adjacent_power_ratio b p hbig) hlen hdrop
  obtain ⟨_, hf, htwo, hlow⟩ := CoffeeMonkey.palindrome_ends hb hp hlen hs
  obtain ⟨hone, ha⟩ := leading_pair_bounds b p N hp hbig hlo hhi hf htwo
  rw [hone] at hlow
  exact canonical_obstruction b p (N/b%b) N (N/b^2 : ℕ)
    hlen' hl (CoffeeMonkey.low_two_decomposition hlow) hp heven hbig ha

end CoffeeMonkey.DigitDrop
namespace OMA.R_mo_268590_R2

open OMA.S_mo_268590

-- The parity argument is adapted from @wtho704's reduction, PR 20687.
private lemma even_palindrome_dvd_succ {b N : ℕ} (h : NontrivPalindrome b N)
    (he : Even (Nat.digits b N).length) : b + 1 ∣ N := by
  let dig := (Nat.digits b N).map (fun d : ℕ => (d : ℤ))
  have hp : dig.Palindrome := (List.Palindrome.of_reverse_eq h.2).map _
  have he' : Even dig.length := by simpa [dig] using he
  have hdiv : ((b + 1 : ℕ) : ℤ) ∣ (b : ℤ) - (-1) := ⟨1, by push_cast; ring⟩
  rw [Nat.dvd_iff_dvd_ofDigits (b + 1) b (-1) hdiv, Nat.ofDigits_neg_one]
  refine ⟨0, (show dig.alternatingSum = 0 from ?_)⟩
  have hrev := dig.alternatingSum_reverse
  rw [hp.reverse_eq, pow_succ', he'.neg_one_pow, mul_one, neg_one_zsmul] at hrev
  exact eq_zero_of_neg_eq hrev.symm

private lemma palindrome_ne_zero {b N : ℕ} (h : NontrivPalindrome b N) : N ≠ 0 := by
  intro hN
  simpa [hN] using h.1

private lemma odd_length_of_next_palindrome {b N : ℕ} (hb : 2 ≤ b)
    (h : NontrivPalindrome b N) (hnext : NontrivPalindrome (b + 1) N) :
    Odd (Nat.digits b N).length := by
  rcases Nat.even_or_odd (Nat.digits b N).length with he | ho
  · exfalso
    have hdiv := even_palindrome_dvd_succ h he
    have hn := palindrome_ne_zero hnext
    have hhead : (Nat.digits (b + 1) N).head! = 0 := by
      rw [Nat.head!_digits (by omega : b + 1 ≠ 1), Nat.mod_eq_zero_of_dvd hdiv]
    have hlast := congrArg List.head? hnext.2
    rw [List.head?_reverse, List.getLast?_eq_some_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hn)] at hlast
    exact Nat.getLast_digit_ne_zero (b + 1) hn ((List.head!_of_head? hlast.symm).symm.trans hhead)
  · exact ho

private lemma digit_length_antitone {b c N : ℕ} (hb : 1 < b) (hbc : b ≤ c) :
    (Nat.digits c N).length ≤ (Nat.digits b N).length := by
  apply (Nat.digits_length_le_iff (hb.trans_le hbc) N).mpr
  exact (Nat.lt_base_pow_length_digits hb).trans_le (Nat.pow_le_pow_left hbc _)

-- The four palindromes have the same length.
def H1 : Prop :=
  ∀ N b : ℕ, 2 ≤ b →
    (∀ i < 4, (Nat.digits (b+i) N).length = (Nat.digits b N).length) →
    ¬ (∀ i < 4, NontrivPalindrome (b+i) N)

-- The digit count falls, and the starting base is strictly bounded by the initial length.
def H2 : Prop :=
  ∀ N b : ℕ, 2 ≤ b →
    (Nat.digits (b+3) N).length < (Nat.digits b N).length →
    b < 3*((Nat.digits b N).length-1) →
    ¬ (∀ i < 4, NontrivPalindrome (b+i) N)

theorem main : H1 → H2 → type_of% @OMA.S_mo_268590.main := by
  intro hequal hirreg
  rintro ⟨N,b,hb,hpals⟩
  let d := fun i => (Nat.digits (b+i) N).length
  have mono {i j : ℕ} (hij : i ≤ j) : d j ≤ d i :=
    digit_length_antitone (by omega : 1 < b+i) (by omega : b+i ≤ b+j)
  by_cases last : d 3 < d 0
  · have someDrop : ∃ i < 3, d (i+1) < d i := by
      by_contra! h
      have h0 : d 0 ≤ d 1 := h 0 (by decide)
      have h1 : d 1 ≤ d 2 := h 1 (by decide)
      have h2 : d 2 ≤ d 3 := h 2 (by decide)
      omega
    obtain ⟨i,hi,hdrop⟩ := someDrop
    have first := hpals i (by omega)
    have next : NontrivPalindrome ((b+i)+1) N := by
      simpa [Nat.add_assoc] using hpals (i+1) (by omega)
    obtain ⟨k,hk⟩ := odd_length_of_next_palindrome (by omega) first next
    have hlen : (Nat.digits (b+i) N).length = 2*k+1 := by omega
    have hpos : 0 < 2*k := by have := first.1; omega
    have hdrop' : (Nat.digits ((b+i)+1) N).length < (Nat.digits (b+i) N).length := by
      simpa [d, Nat.add_assoc] using hdrop
    have hcut := CoffeeMonkey.DigitDrop.adjacent_palindrome_drop
      (by omega : 2 ≤ b+i) hpos (show 2*k%2=0 by omega) hlen first.2 next.2 hdrop'
    have hmono : d i ≤ d 0 := mono (by omega)
    simp [d] at hmono last
    exact hirreg N b hb last (by omega) hpals
  · apply hequal N b hb _ hpals
    intro i hi
    have h := mono (i:=i) (j:=3) (by omega)
    have h' := mono (i:=0) (j:=i) (by omega)
    have he : d i = d 0 := by omega
    simpa [d] using he

end OMA.R_mo_268590_R2
