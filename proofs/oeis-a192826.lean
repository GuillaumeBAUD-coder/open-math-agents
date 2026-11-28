import OMAStatements.S_oeis_a192826

-- Problem: A192826: Molecular topological indices of the folded cube graphs.
-- Upstream: formal-conjectures statements/oeis-a192826.lean:0 (declaration OMA.S_oeis_a192826.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write w(j) = C(j, floor(j/2)). Then (k+1) w(2k+1) = (2k+1) w(2k) and w(2k+2) = 2 w(2k+1), so
all the w-terms of the recurrence are polynomial multiples of the lowest one after multiplying by
the product of the factors k + q. For n ≥ 10 every term is given by the closed form
a(j+3) = 2 * 2^j (j+3)^2 (2 + 4 * 2^j - w(j+2)); the parts with 2^j and 4^j cancel identically and
the w-part cancels by the two relations. The cases n = 2k+10 and n = 2k+11 are treated separately. -/

namespace A192826Aux

open OMA.S_oeis_a192826

/-- w(j) = C(j, floor(j/2)). -/
def w (j : ℕ) : ℚ := (j.choose (j / 2) : ℚ)

theorem wA (k : ℕ) : ((k : ℚ) + 1) * w (2 * k + 1) = (2 * (k : ℚ) + 1) * w (2 * k) := by
  unfold w
  have e1 : (2 * k + 1) / 2 = k := by omega
  have e2 : 2 * k / 2 = k := by omega
  rw [e1, e2]
  have h : (2 * k + 1) * (2 * k).choose k = (2 * k + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (2 * k) k
  have hs : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := Nat.choose_symm_half k
  rw [hs] at h
  have hq : ((2 * k + 1 : ℕ) : ℚ) * ((2 * k).choose k : ℚ) =
      ((2 * k + 1).choose k : ℚ) * ((k + 1 : ℕ) : ℚ) := by
    exact_mod_cast h
  push_cast at hq
  linear_combination -hq

theorem wB (k : ℕ) : w (2 * k + 2) = 2 * w (2 * k + 1) := by
  unfold w
  have e1 : (2 * k + 2) / 2 = k + 1 := by omega
  have e2 : (2 * k + 1) / 2 = k := by omega
  rw [e1, e2]
  have h : (2 * k + 2).choose (k + 1) = (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) :=
    Nat.choose_succ_succ' (2 * k + 1) k
  have hs : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := Nat.choose_symm_half k
  rw [hs] at h
  rw [h]
  push_cast
  ring

theorem af (j : ℕ) : (a (j + 3) : ℚ) =
    2 * (2 : ℚ) ^ j * ((j : ℚ) + 3) ^ 2 * (2 + 4 * (2 : ℚ) ^ j - w (j + 2)) := by
  have h : j + 3 ≠ 2 := by omega
  have e1 : j + 3 - 2 = j + 1 := rfl
  have e2 : j + 3 - 1 = j + 2 := rfl
  unfold a w
  rw [if_neg h, e1, e2]
  push_cast
  ring

theorem pure0 (k : ℕ) (T : ℚ) :
    ((2  *  (k : ℚ)  +  10) - 1) * (3171347 * (2  *  (k : ℚ)  +  10) - 9561097) *
        (2 * (128 * T) * (2 * (k : ℚ) + 10) ^ 2 * (2 + 4 * (128 * T) - w (2 * k + 9))) +
      2 * (-22257061 * (2  *  (k : ℚ)  +  10) ^ 2 + 113080920 * (2  *  (k : ℚ)  +  10) - 124259984) *
        (2 * (64 * T) * (2 * (k : ℚ) + 9) ^ 2 * (2 + 4 * (64 * T) - w (2 * k + 8))) +
      8 * (25480326 * (2  *  (k : ℚ)  +  10) ^ 2 - 186826067 * (2  *  (k : ℚ)  +  10) + 302663821) *
        (2 * (32 * T) * (2 * (k : ℚ) + 8) ^ 2 * (2 + 4 * (32 * T) - w (2 * k + 7))) +
      16 * (-2142117 * (2  *  (k : ℚ)  +  10) ^ 2 + 189489004 * (2  *  (k : ℚ)  +  10) - 548366652) *
        (2 * (16 * T) * (2 * (k : ℚ) + 7) ^ 2 * (2 + 4 * (16 * T) - w (2 * k + 6))) +
      64 * (-46156212 * (2  *  (k : ℚ)  +  10) ^ 2 + 185594099 * (2  *  (k : ℚ)  +  10) - 75953597) *
        (2 * (8 * T) * (2 * (k : ℚ) + 6) ^ 2 * (2 + 4 * (8 * T) - w (2 * k + 5))) +
      1024 * (11001336 * (2  *  (k : ℚ)  +  10) ^ 2 - 74317052 * (2  *  (k : ℚ)  +  10) + 114909451) *
        (2 * (4 * T) * (2 * (k : ℚ) + 5) ^ 2 * (2 + 4 * (4 * T) - w (2 * k + 4))) +
      1024 * (-17489828 * (2  *  (k : ℚ)  +  10) ^ 2 + 145166555 * (2  *  (k : ℚ)  +  10) - 279390145) *
        (2 * (2 * T) * (2 * (k : ℚ) + 4) ^ 2 * (2 + 4 * (2 * T) - w (2 * k + 3))) +
      20480 * (530179 * (2  *  (k : ℚ)  +  10) - 1731202) * ((2  *  (k : ℚ)  +  10) - 6) *
        (2 * (1 * T) * (2 * (k : ℚ) + 3) ^ 2 * (2 + 4 * (1 * T) - w (2 * k + 2))) = 0 := by
  have A4 : ((k : ℚ) + 5) * w (2 * k + 9) = (2 * (k : ℚ) + 9) * w (2 * k + 8) := by
    have h := wA (k + 4)
    have e1 : 2 * (k + 4) + 1 = 2 * k + 9 := by ring
    have e2 : 2 * (k + 4) = 2 * k + 8 := by ring
    rw [e1, e2] at h
    push_cast at h
    linear_combination h
  have A3 : ((k : ℚ) + 4) * w (2 * k + 7) = (2 * (k : ℚ) + 7) * w (2 * k + 6) := by
    have h := wA (k + 3)
    have e1 : 2 * (k + 3) + 1 = 2 * k + 7 := by ring
    have e2 : 2 * (k + 3) = 2 * k + 6 := by ring
    rw [e1, e2] at h
    push_cast at h
    linear_combination h
  have A2 : ((k : ℚ) + 3) * w (2 * k + 5) = (2 * (k : ℚ) + 5) * w (2 * k + 4) := by
    have h := wA (k + 2)
    have e1 : 2 * (k + 2) + 1 = 2 * k + 5 := by ring
    have e2 : 2 * (k + 2) = 2 * k + 4 := by ring
    rw [e1, e2] at h
    push_cast at h
    linear_combination h
  have A1 : ((k : ℚ) + 2) * w (2 * k + 3) = (2 * (k : ℚ) + 3) * w (2 * k + 2) := by
    have h := wA (k + 1)
    have e1 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    have e2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [e1, e2] at h
    push_cast at h
    linear_combination h
  have B3 : w (2 * k + 8) = 2 * w (2 * k + 7) := by
    have h := wB (k + 3)
    have e1 : 2 * (k + 3) + 2 = 2 * k + 8 := by ring
    have e2 : 2 * (k + 3) + 1 = 2 * k + 7 := by ring
    rw [e1, e2] at h
    exact h
  have B2 : w (2 * k + 6) = 2 * w (2 * k + 5) := by
    have h := wB (k + 2)
    have e1 : 2 * (k + 2) + 2 = 2 * k + 6 := by ring
    have e2 : 2 * (k + 2) + 1 = 2 * k + 5 := by ring
    rw [e1, e2] at h
    exact h
  have B1 : w (2 * k + 4) = 2 * w (2 * k + 3) := by
    have h := wB (k + 1)
    have e1 : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
    have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    rw [e1, e2] at h
    exact h
  have hne : ((k : ℚ) + 5) * ((k : ℚ) + 4) * ((k : ℚ) + 3) * ((k : ℚ) + 2) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination (T * (-122493761740800 - 243992476600320 * (k : ℚ) - 204111315346432 * (k : ℚ) ^ 2 - 93192554071040 * (k : ℚ) ^ 3 - 25129744534528 * (k : ℚ) ^ 4 - 4008347558912 * (k : ℚ) ^ 5 - 350629236736 * (k : ℚ) ^ 6 - 12989837312 * (k : ℚ) ^ 7)) * A4 +
    (T * (1931208601927680 + 4453102060240896 * (k : ℚ) + 4426800267159552 * (k : ℚ) ^ 2 + 2481645966601216 * (k : ℚ) ^ 3 + 859116492524544 * (k : ℚ) ^ 4 + 188260929369088 * (k : ℚ) ^ 5 + 25523006045184 * (k : ℚ) ^ 6 + 1958685687808 * (k : ℚ) ^ 7 + 65185247232 * (k : ℚ) ^ 8)) * B3 +
    (T * (-169339699200 - 130315153838080 * (k : ℚ) - 237420550248448 * (k : ℚ) ^ 2 - 176695248465920 * (k : ℚ) ^ 3 - 68878135990272 * (k : ℚ) ^ 4 - 14856854642688 * (k : ℚ) ^ 5 - 1683446288384 * (k : ℚ) ^ 6 - 78364336128 * (k : ℚ) ^ 7)) * A3 +
    (T * (-3410077653319680 - 8118205447704576 * (k : ℚ) - 8329549859780608 * (k : ℚ) ^ 2 - 4813243510747136 * (k : ℚ) ^ 3 - 1713612955598848 * (k : ℚ) ^ 4 - 384889785933824 * (k : ℚ) ^ 5 - 53250151770112 * (k : ℚ) ^ 6 - 4147594993664 * (k : ℚ) ^ 7 - 139180449792 * (k : ℚ) ^ 8)) * B2 +
    (T * (1907927084236800 + 4280510993121280 * (k : ℚ) + 4049624869904384 * (k : ℚ) ^ 2 + 2094980229120000 * (k : ℚ) ^ 3 + 640293907316736 * (k : ℚ) ^ 4 + 115659413602304 * (k : ℚ) ^ 5 + 11437537042432 * (k : ℚ) ^ 6 + 477862477824 * (k : ℚ) ^ 7)) * A2 +
    (T * (-2057103900672000 - 6103386054656000 * (k : ℚ) - 7815867095613440 * (k : ℚ) ^ 2 - 5638479982772224 * (k : ℚ) ^ 3 - 2504735108341760 * (k : ℚ) ^ 4 - 701156503699456 * (k : ℚ) ^ 5 - 120720811188224 * (k : ℚ) ^ 6 - 11682217459712 * (k : ℚ) ^ 7 - 486242156544 * (k : ℚ) ^ 8)) * B1 +
    (T * (210601849651200 + 578516991344640 * (k : ℚ) + 663353506529280 * (k : ℚ) ^ 2 + 411526519521280 * (k : ℚ) ^ 3 + 149178196787200 * (k : ℚ) ^ 4 + 31606263644160 * (k : ℚ) ^ 5 + 3625263595520 * (k : ℚ) ^ 6 + 173729054720 * (k : ℚ) ^ 7)) * A1

theorem pure1 (k : ℕ) (T : ℚ) :
    ((2  *  (k : ℚ)  +  11) - 1) * (3171347 * (2  *  (k : ℚ)  +  11) - 9561097) *
        (2 * (256 * T) * (2 * (k : ℚ) + 11) ^ 2 * (2 + 4 * (256 * T) - w (2 * k + 10))) +
      2 * (-22257061 * (2  *  (k : ℚ)  +  11) ^ 2 + 113080920 * (2  *  (k : ℚ)  +  11) - 124259984) *
        (2 * (128 * T) * (2 * (k : ℚ) + 10) ^ 2 * (2 + 4 * (128 * T) - w (2 * k + 9))) +
      8 * (25480326 * (2  *  (k : ℚ)  +  11) ^ 2 - 186826067 * (2  *  (k : ℚ)  +  11) + 302663821) *
        (2 * (64 * T) * (2 * (k : ℚ) + 9) ^ 2 * (2 + 4 * (64 * T) - w (2 * k + 8))) +
      16 * (-2142117 * (2  *  (k : ℚ)  +  11) ^ 2 + 189489004 * (2  *  (k : ℚ)  +  11) - 548366652) *
        (2 * (32 * T) * (2 * (k : ℚ) + 8) ^ 2 * (2 + 4 * (32 * T) - w (2 * k + 7))) +
      64 * (-46156212 * (2  *  (k : ℚ)  +  11) ^ 2 + 185594099 * (2  *  (k : ℚ)  +  11) - 75953597) *
        (2 * (16 * T) * (2 * (k : ℚ) + 7) ^ 2 * (2 + 4 * (16 * T) - w (2 * k + 6))) +
      1024 * (11001336 * (2  *  (k : ℚ)  +  11) ^ 2 - 74317052 * (2  *  (k : ℚ)  +  11) + 114909451) *
        (2 * (8 * T) * (2 * (k : ℚ) + 6) ^ 2 * (2 + 4 * (8 * T) - w (2 * k + 5))) +
      1024 * (-17489828 * (2  *  (k : ℚ)  +  11) ^ 2 + 145166555 * (2  *  (k : ℚ)  +  11) - 279390145) *
        (2 * (4 * T) * (2 * (k : ℚ) + 5) ^ 2 * (2 + 4 * (4 * T) - w (2 * k + 4))) +
      20480 * (530179 * (2  *  (k : ℚ)  +  11) - 1731202) * ((2  *  (k : ℚ)  +  11) - 6) *
        (2 * (2 * T) * (2 * (k : ℚ) + 4) ^ 2 * (2 + 4 * (2 * T) - w (2 * k + 3))) = 0 := by
  have A4 : ((k : ℚ) + 5) * w (2 * k + 9) = (2 * (k : ℚ) + 9) * w (2 * k + 8) := by
    have h := wA (k + 4)
    have e1 : 2 * (k + 4) + 1 = 2 * k + 9 := by ring
    have e2 : 2 * (k + 4) = 2 * k + 8 := by ring
    rw [e1, e2] at h
    push_cast at h
    linear_combination h
  have A3 : ((k : ℚ) + 4) * w (2 * k + 7) = (2 * (k : ℚ) + 7) * w (2 * k + 6) := by
    have h := wA (k + 3)
    have e1 : 2 * (k + 3) + 1 = 2 * k + 7 := by ring
    have e2 : 2 * (k + 3) = 2 * k + 6 := by ring
    rw [e1, e2] at h
    push_cast at h
    linear_combination h
  have A2 : ((k : ℚ) + 3) * w (2 * k + 5) = (2 * (k : ℚ) + 5) * w (2 * k + 4) := by
    have h := wA (k + 2)
    have e1 : 2 * (k + 2) + 1 = 2 * k + 5 := by ring
    have e2 : 2 * (k + 2) = 2 * k + 4 := by ring
    rw [e1, e2] at h
    push_cast at h
    linear_combination h
  have B4 : w (2 * k + 10) = 2 * w (2 * k + 9) := by
    have h := wB (k + 4)
    have e1 : 2 * (k + 4) + 2 = 2 * k + 10 := by ring
    have e2 : 2 * (k + 4) + 1 = 2 * k + 9 := by ring
    rw [e1, e2] at h
    exact h
  have B3 : w (2 * k + 8) = 2 * w (2 * k + 7) := by
    have h := wB (k + 3)
    have e1 : 2 * (k + 3) + 2 = 2 * k + 8 := by ring
    have e2 : 2 * (k + 3) + 1 = 2 * k + 7 := by ring
    rw [e1, e2] at h
    exact h
  have B2 : w (2 * k + 6) = 2 * w (2 * k + 5) := by
    have h := wB (k + 2)
    have e1 : 2 * (k + 2) + 2 = 2 * k + 6 := by ring
    have e2 : 2 * (k + 2) + 1 = 2 * k + 5 := by ring
    rw [e1, e2] at h
    exact h
  have B1 : w (2 * k + 4) = 2 * w (2 * k + 3) := by
    have h := wB (k + 1)
    have e1 : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
    have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    rw [e1, e2] at h
    exact h
  have hne : ((k : ℚ) + 5) * ((k : ℚ) + 4) * ((k : ℚ) + 3) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination (T * (-941313060864000 - 1503685715558400 * (k : ℚ) - 1021012557383680 * (k : ℚ) ^ 2 - 382213340710912 * (k : ℚ) ^ 3 - 85235270318080 * (k : ℚ) ^ 4 - 11328236296192 * (k : ℚ) ^ 5 - 831156846592 * (k : ℚ) ^ 6 - 25979674624 * (k : ℚ) ^ 7)) * B4 +
    (T * (590217351782400 + 887195608258560 * (k : ℚ) + 551355036174336 * (k : ℚ) ^ 2 + 181360306939904 * (k : ℚ) ^ 3 + 33309510825984 * (k : ℚ) ^ 4 + 3239539228672 * (k : ℚ) ^ 5 + 130370494464 * (k : ℚ) ^ 6)) * A4 +
    (T * (-1310441413017600 - 2685587270860800 * (k : ℚ) - 2294997824126976 * (k : ℚ) ^ 2 - 1065798296162304 * (k : ℚ) ^ 3 - 291598625341440 * (k : ℚ) ^ 4 - 47132646174720 * (k : ℚ) ^ 5 - 4176137109504 * (k : ℚ) ^ 6 - 156728672256 * (k : ℚ) ^ 7)) * B3 +
    (T * (-1910382138163200 - 2755884531220480 * (k : ℚ) - 1630389174530048 * (k : ℚ) ^ 2 - 505476846698496 * (k : ℚ) ^ 3 - 86426918440960 * (k : ℚ) ^ 4 - 7703134748672 * (k : ℚ) ^ 5 - 278360899584 * (k : ℚ) ^ 6)) * A3 +
    (T * (8419686034636800 + 16404667835105280 * (k : ℚ) + 13617628390498304 * (k : ℚ) ^ 2 + 6241720618737664 * (k : ℚ) ^ 3 + 1705716421156864 * (k : ℚ) ^ 4 + 277858359369728 * (k : ℚ) ^ 5 + 24977833132032 * (k : ℚ) ^ 6 + 955724955648 * (k : ℚ) ^ 7)) * B2 +
    (T * (-1801949075865600 - 3171591607255040 * (k : ℚ) - 2300123880669184 * (k : ℚ) ^ 2 - 879857524244480 * (k : ℚ) ^ 3 - 187244499451904 * (k : ℚ) ^ 4 - 21020088664064 * (k : ℚ) ^ 5 - 972484313088 * (k : ℚ) ^ 6)) * A2 +
    (T * (806243598336000 + 1968773388697600 * (k : ℚ) + 2024657661460480 * (k : ℚ) ^ 2 + 1136153397985280 * (k : ℚ) ^ 3 + 375623249428480 * (k : ℚ) ^ 4 + 73155854827520 * (k : ℚ) ^ 5 + 7771714355200 * (k : ℚ) ^ 6 + 347458109440 * (k : ℚ) ^ 7)) * B1

end A192826Aux

open A192826Aux OMA.S_oeis_a192826 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192826.main := by
  intro n hn
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 10 ∨ n = 2 * k + 11 := ⟨(n - 10) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have e1 : 2 * k + 10 - 1 = 2 * k + 9 := rfl
    have e2 : 2 * k + 10 - 2 = 2 * k + 8 := rfl
    have e3 : 2 * k + 10 - 3 = 2 * k + 7 := rfl
    have e4 : 2 * k + 10 - 4 = 2 * k + 6 := rfl
    have e5 : 2 * k + 10 - 5 = 2 * k + 5 := rfl
    have e6 : 2 * k + 10 - 6 = 2 * k + 4 := rfl
    have e7 : 2 * k + 10 - 7 = 2 * k + 3 := rfl
    rw [e1, e2, e3, e4, e5, e6, e7]
    have h0 : (a (2 * k + 10) : ℚ) =
        2 * (128 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 10) ^ 2 * (2 + 4 * (128 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 9)) := by
      have h := af (2 * k + 7)
      have e1 : 2 * k + 7 + 3 = 2 * k + 10 := rfl
      have e2 : 2 * k + 7 + 2 = 2 * k + 9 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h1 : (a (2 * k + 9) : ℚ) =
        2 * (64 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 9) ^ 2 * (2 + 4 * (64 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 8)) := by
      have h := af (2 * k + 6)
      have e1 : 2 * k + 6 + 3 = 2 * k + 9 := rfl
      have e2 : 2 * k + 6 + 2 = 2 * k + 8 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h2 : (a (2 * k + 8) : ℚ) =
        2 * (32 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 8) ^ 2 * (2 + 4 * (32 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 7)) := by
      have h := af (2 * k + 5)
      have e1 : 2 * k + 5 + 3 = 2 * k + 8 := rfl
      have e2 : 2 * k + 5 + 2 = 2 * k + 7 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h3 : (a (2 * k + 7) : ℚ) =
        2 * (16 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 7) ^ 2 * (2 + 4 * (16 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 6)) := by
      have h := af (2 * k + 4)
      have e1 : 2 * k + 4 + 3 = 2 * k + 7 := rfl
      have e2 : 2 * k + 4 + 2 = 2 * k + 6 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h4 : (a (2 * k + 6) : ℚ) =
        2 * (8 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 6) ^ 2 * (2 + 4 * (8 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 5)) := by
      have h := af (2 * k + 3)
      have e1 : 2 * k + 3 + 3 = 2 * k + 6 := rfl
      have e2 : 2 * k + 3 + 2 = 2 * k + 5 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h5 : (a (2 * k + 5) : ℚ) =
        2 * (4 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 5) ^ 2 * (2 + 4 * (4 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 4)) := by
      have h := af (2 * k + 2)
      have e1 : 2 * k + 2 + 3 = 2 * k + 5 := rfl
      have e2 : 2 * k + 2 + 2 = 2 * k + 4 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h6 : (a (2 * k + 4) : ℚ) =
        2 * (2 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 4) ^ 2 * (2 + 4 * (2 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 3)) := by
      have h := af (2 * k + 1)
      have e1 : 2 * k + 1 + 3 = 2 * k + 4 := rfl
      have e2 : 2 * k + 1 + 2 = 2 * k + 3 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h7 : (a (2 * k + 3) : ℚ) =
        2 * (1 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 3) ^ 2 * (2 + 4 * (1 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 2)) := by
      have h := af (2 * k)
      rw [h]
      push_cast
      ring
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    linear_combination pure0 k ((2 : ℚ) ^ (2 * k))
  · have e1 : 2 * k + 11 - 1 = 2 * k + 10 := rfl
    have e2 : 2 * k + 11 - 2 = 2 * k + 9 := rfl
    have e3 : 2 * k + 11 - 3 = 2 * k + 8 := rfl
    have e4 : 2 * k + 11 - 4 = 2 * k + 7 := rfl
    have e5 : 2 * k + 11 - 5 = 2 * k + 6 := rfl
    have e6 : 2 * k + 11 - 6 = 2 * k + 5 := rfl
    have e7 : 2 * k + 11 - 7 = 2 * k + 4 := rfl
    rw [e1, e2, e3, e4, e5, e6, e7]
    have h0 : (a (2 * k + 11) : ℚ) =
        2 * (256 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 11) ^ 2 * (2 + 4 * (256 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 10)) := by
      have h := af (2 * k + 8)
      have e1 : 2 * k + 8 + 3 = 2 * k + 11 := rfl
      have e2 : 2 * k + 8 + 2 = 2 * k + 10 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h1 : (a (2 * k + 10) : ℚ) =
        2 * (128 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 10) ^ 2 * (2 + 4 * (128 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 9)) := by
      have h := af (2 * k + 7)
      have e1 : 2 * k + 7 + 3 = 2 * k + 10 := rfl
      have e2 : 2 * k + 7 + 2 = 2 * k + 9 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h2 : (a (2 * k + 9) : ℚ) =
        2 * (64 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 9) ^ 2 * (2 + 4 * (64 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 8)) := by
      have h := af (2 * k + 6)
      have e1 : 2 * k + 6 + 3 = 2 * k + 9 := rfl
      have e2 : 2 * k + 6 + 2 = 2 * k + 8 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h3 : (a (2 * k + 8) : ℚ) =
        2 * (32 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 8) ^ 2 * (2 + 4 * (32 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 7)) := by
      have h := af (2 * k + 5)
      have e1 : 2 * k + 5 + 3 = 2 * k + 8 := rfl
      have e2 : 2 * k + 5 + 2 = 2 * k + 7 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h4 : (a (2 * k + 7) : ℚ) =
        2 * (16 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 7) ^ 2 * (2 + 4 * (16 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 6)) := by
      have h := af (2 * k + 4)
      have e1 : 2 * k + 4 + 3 = 2 * k + 7 := rfl
      have e2 : 2 * k + 4 + 2 = 2 * k + 6 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h5 : (a (2 * k + 6) : ℚ) =
        2 * (8 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 6) ^ 2 * (2 + 4 * (8 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 5)) := by
      have h := af (2 * k + 3)
      have e1 : 2 * k + 3 + 3 = 2 * k + 6 := rfl
      have e2 : 2 * k + 3 + 2 = 2 * k + 5 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h6 : (a (2 * k + 5) : ℚ) =
        2 * (4 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 5) ^ 2 * (2 + 4 * (4 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 4)) := by
      have h := af (2 * k + 2)
      have e1 : 2 * k + 2 + 3 = 2 * k + 5 := rfl
      have e2 : 2 * k + 2 + 2 = 2 * k + 4 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    have h7 : (a (2 * k + 4) : ℚ) =
        2 * (2 * (2 : ℚ) ^ (2 * k)) * (2 * (k : ℚ) + 4) ^ 2 * (2 + 4 * (2 * (2 : ℚ) ^ (2 * k)) - w (2 * k + 3)) := by
      have h := af (2 * k + 1)
      have e1 : 2 * k + 1 + 3 = 2 * k + 4 := rfl
      have e2 : 2 * k + 1 + 2 = 2 * k + 3 := rfl
      rw [e1, e2] at h
      rw [h]
      push_cast
      ring
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    linear_combination pure1 k ((2 : ℚ) ^ (2 * k))
