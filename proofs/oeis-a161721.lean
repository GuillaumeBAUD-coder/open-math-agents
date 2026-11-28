import OMAStatements.S_oeis_a161721

/-! The two digit restrictions for the primes in OEIS A161721.
The middle column of an odd-length palindromic product contains the sum of
the squares of the digits (compare Ezerman, Meyer and Solé, JIS 18 (2015), Proposition 10). Both outer digits of a multi-digit term are odd. -/

namespace A161721

open Nat OMA.S_oeis_a161721

/-- Carrying leaves the forward value unchanged and decreases the reversed
value strictly whenever any column needs a carry. Both lists have fixed width. -/
private theorem carry_bound {b : ℕ} (hb : 1 < b) (digits raw : List ℕ)
    (len : raw.length = digits.length) (good : ∀ d ∈ digits, d < b)
    (value : ofDigits b raw = ofDigits b digits) :
    ofDigits b digits.reverse ≤ ofDigits b raw.reverse ∧
    (ofDigits b raw.reverse ≤ ofDigits b digits.reverse → raw = digits) := by
  induction digits generalizing raw with
  | nil =>
    have empty : raw = [] := by simpa using len
    subst raw
    simp
  | cons d ds ih =>
    cases raw with
    | nil => simp at len
    | cons x xs =>
      have hd := good d (by simp)
      cases ds with
      | nil =>
        have empty : xs = [] := by simpa using len
        subst xs
        have xd : x = d := by simpa using value
        simp [xd]
      | cons v vs =>
        cases xs with
        | nil => simp at len
        | cons u us =>
          have lengthEq : us.length = vs.length := by simpa using len
          let h := x/b
          have rem : x%b = d := by
            simpa [ofDigits_cons, Nat.mod_eq_of_lt hd] using congrArg (fun z => z%b) value
          have hx : x = d+b*h := by simpa only [h,rem] using (Nat.mod_add_div x b).symm
          have step : ofDigits b ((u+h)::us) = ofDigits b (v::vs) := by
            apply Nat.eq_of_mul_eq_mul_left (show 0 < b by omega)
            simp only [ofDigits_cons] at value ⊢
            rw [hx] at value
            nlinarith only [value]
          obtain ⟨bound,strict⟩ := ih ((u+h)::us) (by simpa using lengthEq)
            (fun z hz => good z (List.mem_cons_of_mem _ hz)) step
          have restore : b^2-1+1 = b^2 := Nat.sub_add_cancel (by nlinarith)
          have id : ofDigits b (x::u::us).reverse = ofDigits b ((u+h)::us).reverse +
              b^(v::vs).length*d + (b^2-1)*b^us.length*h := by
            simp only [ofDigits_reverse_cons, List.length_cons, ← lengthEq, hx]
            rw [pow_succ b us.length]
            nlinarith only [congrArg (fun k => k*(b^us.length*h)) restore]
          rw [id, ofDigits_reverse_cons (v::vs) d]
          refine ⟨by omega, fun le => ?_⟩
          have zero : h = 0 := by
            by_contra! nz
            have part : 0 < b^2-1 := by nlinarith
            have pos : 0 < (b^2-1)*b^us.length*h := by positivity
            omega
          have same := strict (by omega)
          simp only [zero,Nat.add_zero] at same
          have xd : x = d := by simpa [zero] using hx
          exact congrArg₂ List.cons xd same

private def mass (l : List ℕ) : ℕ := (l.map (fun d => d^2)).sum

private theorem scale (b x : ℕ) (l : List ℕ) :
    ofDigits b (l.map (x*·)) = x*ofDigits b l := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, ofDigits_cons, ih]; ring

private theorem block_value (b c : ℕ) (l : List ℕ) :
    ofDigits b (l ++ c::l.reverse) =
      ofDigits b l + b^l.length*(c+b*ofDigits b l.reverse) := by
  rw [ofDigits_append, ofDigits_cons]

/-- The uncarried product is a symmetric list whose central coefficient is the digit-square sum. -/
private theorem columns (b : ℕ) (l : List ℕ) (ne : l ≠ []) :
    ∃ half : List ℕ, half.length+1 = l.length ∧
      ofDigits b (half ++ mass l :: half.reverse) = ofDigits b l * ofDigits b l.reverse := by
  induction l with
  | nil => contradiction
  | cons x l ih =>
    by_cases empty : l = []
    · subst l
      exact ⟨[],rfl,by simp [mass,pow_two]⟩
    obtain ⟨m,lm,prev⟩ := ih empty
    let row := l.reverse.map (x*·)
    let half := row.zipWith (·+·) (0::m)
    have len : row.length = (0::m).length := by simpa [row] using lm.symm
    have lh : half.length = l.length := by simp [half,List.length_zipWith,row,← lm]
    have low : ofDigits b half = x * ofDigits b l.reverse + b * ofDigits b m := by
      rw [show ofDigits b half = _ from (ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq len).symm]
      simp only [row, scale, ofDigits_cons, zero_add]
    have high : ofDigits b half.reverse = x * ofDigits b l + ofDigits b m.reverse := by
      rw [show half.reverse = _ from List.reverse_zipWith len,
        ← ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simpa using len)]
      simp [row, ← List.map_reverse, scale, List.reverse_cons]
    refine ⟨half,by simp [lh],?_⟩
    rw [block_value,lh,low,high,ofDigits_cons,ofDigits_reverse_cons]
    rw [block_value] at prev
    have mass_cons : mass (x::l) = x^2+mass l := by simp [mass]
    rw [mass_cons,← lm,pow_succ]
    nlinarith only [congrArg (b*·) prev]

private theorem middle_digit_bound {n r : ℕ}
    (rev : digits 10 r = (digits 10 n).reverse) (hn : n ≠ 0)
    (pal : (digits 10 (n*r)).Palindrome) (odd : ¬ Even (digits 10 (n*r)).length) :
    mass (digits 10 n) < 10 := by
  let l := digits 10 n
  let D := digits 10 (n*r)
  have ne : l ≠ [] := digits_ne_nil_iff_ne_zero.mpr hn
  obtain ⟨half,lh,prod⟩ := columns 10 l ne
  let k := half.length
  have ln : (digits 10 n).length = k+1 := lh.symm
  have lr : (digits 10 r).length = k+1 := by simp [rev,ln]
  have lower (z : ℕ) (ez : (digits 10 z).length = k+1) : 10^k ≤ z :=
    (lt_digits_length_iff (by decide) _).mp (by omega)
  have upper (z : ℕ) (ez : (digits 10 z).length = k+1) : z < 10^(k+1) :=
    (digits_length_le_iff (by decide) _).mp ez.le
  have lo : 10^(2*k) ≤ n*r := by
    rw [two_mul,pow_add]
    exact Nat.mul_le_mul (lower n ln) (lower r lr)
  have hi : n*r < 10^(2*k+2) := by
    rw [show 2*k+2 = (k+1)+(k+1) by omega,pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (upper n ln) (upper r lr)
  have dLo := (lt_digits_length_iff (by decide : 1 < 10) _).mpr lo
  have dHi := (digits_length_le_iff (by decide : 1 < 10) _).mpr hi
  have width : D.length = 2*k+1 := by
    change (digits 10 (n*r)).length = _
    by_contra! bad
    exact odd ⟨k+1,by omega⟩
  let raw := half ++ mass l :: half.reverse
  have symm : raw.reverse = raw := by simp [raw,List.reverse_append,List.reverse_cons,List.append_assoc]
  have same : ofDigits 10 raw = ofDigits 10 D := by
    rw [ofDigits_digits]
    change ofDigits 10 (half ++ mass l :: half.reverse) = _
    rw [prod,show ofDigits 10 l = n from ofDigits_digits ..]
    rw [show l.reverse = digits 10 r from rev.symm,ofDigits_digits]
  have eq := (carry_bound (by decide : 1 < 10) D raw
    (by simpa [raw,k,two_mul,Nat.add_assoc] using width.symm)
    (fun _ h => digits_lt_base (by decide) h) same).2 (by rw [symm,pal.reverse_eq,same])
  have mem : mass l ∈ raw := by simp [raw]
  exact digits_lt_base (by decide : 1 < 10) (eq ▸ mem : mass l ∈ D)

private theorem square_le_mass {d : ℕ} {l : List ℕ} (hd : d ∈ l) : d^2 ≤ mass l := by
  induction l with
  | nil => simp at hd
  | cons x xs ih =>
    have eq : mass (x::xs) = x^2 + mass xs := by simp [mass]
    rw [eq]
    rcases List.mem_cons.mp hd with h | h
    · subst d; omega
    · exact (ih h).trans (Nat.le_add_left ..)

private theorem twos_le_mass (l : List ℕ) : 4*l.count 2 ≤ mass l := by
  induction l with
  | nil => simp [mass]
  | cons x xs ih =>
    have eq : mass (x::xs) = x^2+mass xs := by simp [mass]
    rw [eq]
    by_cases h : x = 2
    · subst x; simp only [List.count_cons_self,Nat.mul_add]; omega
    · simpa [List.count_cons,h] using ih.trans (Nat.le_add_left (mass xs) (x^2))

/-- Both conjectures in the OEIS entry, including the exception at the prime three. -/
theorem digit_restrictions (p : ℕ) (hp : p.Prime) (hr : (digitalReverse p).Prime)
    (pal : (digits 10 (p*digitalReverse p)).Palindrome) :
    (p ≠ 3 → ∀ d ∈ digits 10 p, d ≤ 2) ∧ (digits 10 p).count 2 ≤ 1 := by
  by_cases small : p ≤ 11
  · have finite : ∀ z : Fin 12, z.val.Prime →
        (digits 10 (z.val*digitalReverse z.val)).reverse = digits 10 (z.val*digitalReverse z.val) →
        (z.val ≠ 3 → ∀ d ∈ digits 10 z.val, d ≤ 2) ∧ (digits 10 z.val).count 2 ≤ 1 := by
      decide +kernel
    exact finite ⟨p,by omega⟩ hp pal.reverse_eq
  let r := digitalReverse p
  have nz : p%10 ≠ 0 := by
    intro h
    rcases (dvd_prime hp).mp (dvd_of_mod_eq_zero h) with bad | bad <;> omega
  have rd : digits 10 r = (digits 10 p).reverse := by
    apply digits_ofDigits 10 (by decide) _ (fun _ h => digits_lt_base (by decide) (List.mem_reverse.mp h))
    rw [digits_def' (by decide : 1 < 10) hp.pos,List.reverse_cons]
    intro h
    simpa only [List.getLast_concat] using nz
  have back : digitalReverse r = p := by
    unfold digitalReverse
    rw [rd,List.reverse_reverse,ofDigits_digits]
  have r2 : r ≠ 2 := by
    intro eq
    rw [eq] at back
    change 2 = p at back
    omega
  have r11 : r ≠ 11 := by
    intro eq
    rw [eq] at back
    change 11 = p at back
    omega
  have lengthOdd : ¬Even (digits 10 (p*r)).length := by
    intro even
    have prime11 : Nat.Prime 11 := by decide
    rcases prime11.dvd_mul.mp (eleven_dvd_of_palindrome pal even) with left | right
    · have := (prime_dvd_prime_iff_eq prime11 hp).mp left
      omega
    · exact r11 ((prime_dvd_prime_iff_eq prime11 hr).mp right).symm
  have center := middle_digit_bound rd hp.ne_zero pal lengthOdd
  rcases List.eq_nil_or_concat (digits 10 (p/10)) with empty | ⟨mid,y,hm⟩
  · have := digits_eq_nil_iff_eq_zero.mp empty
    omega
  have shape : digits 10 p = p%10 :: (mid ++ [y]) := by
    rw [digits_def' (by decide : 1 < 10) hp.pos,hm,List.concat_eq_append]
  have last : r%10 = y := by
    have h := (head!_digits (b := 10) (n := r) (by decide)).symm
    rw [rd,shape] at h
    simpa [List.reverse_cons,List.reverse_append,List.append_assoc] using h
  have po := hp.eq_two_or_odd.resolve_left (by omega)
  have ro := hr.eq_two_or_odd.resolve_left r2
  change r%2 = 1 at ro
  have frontPos : 1 ≤ (p%10)^2 := Nat.one_le_pow _ _ (by omega)
  have lastPos : 1 ≤ y^2 := Nat.one_le_pow _ _ (by omega)
  have total : (p%10)^2+mass mid+y^2 < 10 := by
    simpa [shape,mass,List.sum_append,Nat.add_assoc] using center
  have three (z : ℕ) (big : 3 ≤ z) : 9 ≤ z^2 := Nat.pow_le_pow_left big 2
  have frontLe : p%10 ≤ 2 := by by_contra! h; have := three _ h; omega
  have lastLe : y ≤ 2 := by by_contra! h; have := three _ h; omega
  refine ⟨fun _ d hd => ?_,?_⟩
  · rw [shape] at hd
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hd
    rcases hd with h | h | h
    · exact h ▸ frontLe
    · by_contra! bad
      have := square_le_mass h
      have := three _ bad
      omega
    · exact h ▸ lastLe
  · have cnt := twos_le_mass mid
    have result : mid.count 2 ≤ 1 := by omega
    have a : p%10 ≠ 2 := by omega
    have z : y ≠ 2 := by omega
    simpa [shape,List.count_cons,a,z] using result

end A161721

theorem OMA.solution : type_of% @OMA.S_oeis_a161721.main := A161721.digit_restrictions
