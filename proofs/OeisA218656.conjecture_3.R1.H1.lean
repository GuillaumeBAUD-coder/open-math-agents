import OMAReductions.R_OeisA218656_conjecture_3_R1

-- Step OeisA218656.conjecture_3.R1.H1: hypothesis H1 of reduction OeisA218656.conjecture_3.R1

/-! Finite check: for each of the 58 admissible n up to 64 an explicit x is given with
x^8+(2n+1-x)^8 prime. Primality is certified by Pratt certificates (Lucas test with a
primitive root and the prime factors of p-1), checked by kernel evaluation of a fuel-based
binary modular exponentiation. -/

namespace OMA.A218656H1

/-- Binary modular exponentiation with fuel. -/
def powMod (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % p
  | f+1, a, e =>
    if e = 0 then 1 % p
    else if e % 2 = 1 then a * powMod p f (a*a%p) (e/2) % p
    else powMod p f (a*a%p) (e/2)

theorem powMod_eq (p : ℕ) : ∀ f a e : ℕ, e < 2^f → powMod p f a e = a^e % p := by
  intro f
  induction f with
  | zero =>
    intro a e he
    have : e = 0 := by simpa using he
    subst this
    simp [powMod]
  | succ f ih =>
    intro a e he
    rw [powMod]
    by_cases h0 : e = 0
    · simp [h0]
    · have hlt : e/2 < 2^f := by rw [pow_succ] at he; omega
      have key : (a*a%p)^(e/2) % p = (a^2)^(e/2) % p := by
        rw [← Nat.pow_mod, pow_two]
      rw [if_neg h0, ih _ _ hlt, key, ← pow_mul]
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        have he2 : e = 2*(e/2) + 1 := by omega
        conv_rhs => rw [he2, pow_succ, mul_comm]
        rw [Nat.mul_mod_mod]
      · rw [if_neg h1]
        have he2 : e = 2*(e/2) := by omega
        conv_rhs => rw [he2]

def prattCheck (p a : ℕ) (l : List ℕ) : Bool :=
  decide (1 < p) && decide (p < 2^64) && (powMod p 64 a (p-1) == 1) &&
    l.all (fun q => powMod p 64 a ((p-1)/q) != 1) && (l.prod^64 % (p-1) == 0)

theorem pratt (p a : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, Nat.Prime q)
    (hc : prattCheck p a l = true) : Nat.Prime p := by
  simp only [prattCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨hp1, hp64⟩, hpow⟩, hall⟩, hprod⟩ := hc
  have hlt : ∀ e, e ≤ p - 1 → e < 2^64 := fun e he => by omega
  have cast : ∀ e, ((a : ZMod p))^e = 1 → a^e % p = 1 := by
    intro e h
    have h' : ((a^e : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact h
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h'
    rw [this, Nat.mod_eq_of_lt hp1]
  apply lucas_primality p (a : ZMod p)
  · rw [powMod_eq p 64 a (p-1) (hlt _ le_rfl)] at hpow
    have h' : ((a^(p-1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff', hpow, Nat.mod_eq_of_lt hp1]
    exact_mod_cast h'
  · intro q hq hqd h
    have hq1 : q ∣ l.prod := hq.dvd_of_dvd_pow (hqd.trans (Nat.dvd_of_mod_eq_zero hprod))
    obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).1 hq1
    have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hq (hl r hr)).1 hqr
    subst hqr'
    have := hall q hr
    rw [powMod_eq p 64 a _ (hlt _ (Nat.div_le_self _ _))] at this
    exact this (cast _ h)

theorem pp2070241 : Nat.Prime 2070241 :=
  (pratt 2070241 22 [2, 3, 5, 19, 227] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp100006561 : Nat.Prime 100006561 :=
  (pratt 100006561 11 [2, 3, 5, 37, 1877] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp111317 : Nat.Prime 111317 :=
  (pratt 111317 2 [2, 17, 1637] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp815730977 : Nat.Prime 815730977 :=
  (pratt 815730977 3 [2, 229, 111317] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp111317⟩) (by decide +kernel))

theorem pp1475795617 : Nat.Prime 1475795617 :=
  (pratt 1475795617 15 [2, 3, 29, 37, 14327] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp435746497 : Nat.Prime 435746497 :=
  (pratt 435746497 5 [2, 3, 53, 42821] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp832507937 : Nat.Prime 832507937 :=
  (pratt 832507937 5 [2, 13, 59, 107, 317] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp136753 : Nat.Prime 136753 :=
  (pratt 136753 5 [2, 3, 7, 11, 37] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp16983628577 : Nat.Prime 16983628577 :=
  (pratt 16983628577 3 [2, 3881, 136753] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp136753⟩) (by decide +kernel))

theorem pp104119 : Nat.Prime 104119 :=
  (pratt 104119 6 [2, 3, 7, 37, 67] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp4338014017 : Nat.Prime 4338014017 :=
  (pratt 4338014017 5 [2, 3, 7, 31, 104119] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp104119⟩) (by decide +kernel))

theorem pp25605764801 : Nat.Prime 25605764801 :=
  (pratt 25605764801 3 [2, 5, 7, 11, 307, 677] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp222127 : Nat.Prime 222127 :=
  (pratt 222127 3 [2, 3, 37021] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp5110698017 : Nat.Prime 5110698017 :=
  (pratt 5110698017 3 [2, 719, 222127] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp222127⟩) (by decide +kernel))

theorem pp444833 : Nat.Prime 444833 :=
  (pratt 444833 3 [2, 13901] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num)⟩) (by decide +kernel))

theorem pp377802004897 : Nat.Prime 377802004897 :=
  (pratt 377802004897 5 [2, 3, 983, 444833] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp444833⟩) (by decide +kernel))

theorem pp675481 : Nat.Prime 675481 :=
  (pratt 675481 19 [2, 3, 5, 13, 433] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp476889587 : Nat.Prime 476889587 :=
  (pratt 476889587 2 [2, 353, 675481] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp675481⟩) (by decide +kernel))

theorem pp152604667841 : Nat.Prime 152604667841 :=
  (pratt 152604667841 3 [2, 5, 476889587] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp476889587⟩) (by decide +kernel))

theorem pp918899 : Nat.Prime 918899 :=
  (pratt 918899 2 [2, 101, 4549] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp17995718017 : Nat.Prime 17995718017 :=
  (pratt 17995718017 10 [2, 3, 17, 918899] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp918899⟩) (by decide +kernel))

theorem pp32575757441 : Nat.Prime 32575757441 :=
  (pratt 32575757441 3 [2, 5, 23, 79, 109, 257] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp378016357217 : Nat.Prime 378016357217 :=
  (pratt 378016357217 3 [2, 23, 19121, 26861] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp117051071617 : Nat.Prime 117051071617 :=
  (pratt 117051071617 5 [2, 3, 293, 541, 641] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp2251892167841 : Nat.Prime 2251892167841 :=
  (pratt 2251892167841 11 [2, 5, 7, 36809, 54623] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp854366826497 : Nat.Prime 854366826497 :=
  (pratt 854366826497 3 [2, 89, 137, 17107] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp331973 : Nat.Prime 331973 :=
  (pratt 331973 2 [2, 149, 557] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp1786609635617 : Nat.Prime 1786609635617 :=
  (pratt 1786609635617 3 [2, 13, 17, 761, 331973] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp331973⟩) (by decide +kernel))

theorem pp673083563041 : Nat.Prime 673083563041 :=
  (pratt 673083563041 11 [2, 3, 5, 7, 109, 151, 4057] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp555122286497 : Nat.Prime 555122286497 :=
  (pratt 555122286497 3 [2, 179, 5227, 18541] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp1137334487137 : Nat.Prime 1137334487137 :=
  (pratt 1137334487137 11 [2, 3, 673, 1399, 12583] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp1252099518401 : Nat.Prime 1252099518401 :=
  (pratt 1252099518401 3 [2, 5, 433, 1249, 1447] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp181123 : Nat.Prime 181123 :=
  (pratt 181123 3 [2, 3, 30187] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp11692495244897 : Nat.Prime 11692495244897 :=
  (pratt 11692495244897 3 [2, 937, 2153, 181123] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp181123⟩) (by decide +kernel))

theorem pp112603 : Nat.Prime 112603 :=
  (pratt 112603 2 [2, 3, 7, 383] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp2068223441377 : Nat.Prime 2068223441377 :=
  (pratt 2068223441377 5 [2, 3, 37, 5171, 112603] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp112603⟩) (by decide +kernel))

theorem pp6631910985281 : Nat.Prime 6631910985281 :=
  (pratt 6631910985281 3 [2, 5, 7, 37, 79, 683, 1483] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp118273 : Nat.Prime 118273 :=
  (pratt 118273 5 [2, 3, 7, 11] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp2602007 : Nat.Prime 2602007 :=
  (pratt 2602007 5 [2, 11, 118273] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp118273⟩) (by decide +kernel))

theorem pp15612043 : Nat.Prime 15612043 :=
  (pratt 15612043 2 [2, 3, 2602007] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp2602007⟩) (by decide +kernel))

theorem pp2505920246017 : Nat.Prime 2505920246017 :=
  (pratt 2505920246017 5 [2, 3, 11, 19, 15612043] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp15612043⟩) (by decide +kernel))

theorem pp191707314676897 : Nat.Prime 191707314676897 :=
  (pratt 191707314676897 5 [2, 3, 29, 2131, 2741, 11789] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp128063296076897 : Nat.Prime 128063296076897 :=
  (pratt 128063296076897 3 [2, 2531, 34337, 46049] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp105269 : Nat.Prime 105269 :=
  (pratt 105269 2 [2, 26317] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num)⟩) (by decide +kernel))

theorem pp7406491037441 : Nat.Prime 7406491037441 :=
  (pratt 7406491037441 3 [2, 5, 11, 19, 263, 105269] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), pp105269⟩) (by decide +kernel))

theorem pp267193 : Nat.Prime 267193 :=
  (pratt 267193 5 [2, 3, 1237] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp10066079453921 : Nat.Prime 10066079453921 :=
  (pratt 10066079453921 3 [2, 5, 7, 33637, 267193] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp267193⟩) (by decide +kernel))

theorem pp893003 : Nat.Prime 893003 :=
  (pratt 893003 2 [2, 11, 40591] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp62468517475937 : Nat.Prime 62468517475937 :=
  (pratt 62468517475937 3 [2, 11, 13, 15287, 893003] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp893003⟩) (by decide +kernel))

theorem pp704719 : Nat.Prime 704719 :=
  (pratt 704719 37 [2, 3, 7, 17, 47] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp281481952468097 : Nat.Prime 281481952468097 :=
  (pratt 281481952468097 3 [2, 17, 19, 9661, 704719] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp704719⟩) (by decide +kernel))

theorem pp106181 : Nat.Prime 106181 :=
  (pratt 106181 2 [2, 5, 5309] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp26632396569217 : Nat.Prime 26632396569217 :=
  (pratt 26632396569217 7 [2, 3, 641, 1019, 106181] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp106181⟩) (by decide +kernel))

theorem pp21370852274017 : Nat.Prime 21370852274017 :=
  (pratt 21370852274017 5 [2, 3, 7, 43, 13963, 52967] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp294241 : Nat.Prime 294241 :=
  (pratt 294241 7 [2, 3, 5, 613] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp97570202611457 : Nat.Prime 97570202611457 :=
  (pratt 97570202611457 3 [2, 67, 19333, 294241] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp294241⟩) (by decide +kernel))

theorem pp709603 : Nat.Prime 709603 :=
  (pratt 709603 2 [2, 3, 227, 521] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp1113035603185697 : Nat.Prime 1113035603185697 :=
  (pratt 1113035603185697 3 [2, 5059, 9689, 709603] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp709603⟩) (by decide +kernel))

theorem pp271357 : Nat.Prime 271357 :=
  (pratt 271357 5 [2, 3, 22613] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp2173009 : Nat.Prime 2173009 :=
  (pratt 2173009 7 [2, 3, 17, 2663] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp113214951016897 : Nat.Prime 113214951016897 :=
  (pratt 113214951016897 13 [2, 3, 271357, 2173009] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp271357, pp2173009⟩) (by decide +kernel))

theorem pp505231 : Nat.Prime 505231 :=
  (pratt 505231 12 [2, 3, 5, 11, 1531] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp88081730029121 : Nat.Prime 88081730029121 :=
  (pratt 88081730029121 3 [2, 5, 617, 883, 505231] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp505231⟩) (by decide +kernel))

theorem pp121949 : Nat.Prime 121949 :=
  (pratt 121949 2 [2, 43, 709] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp149651547511777 : Nat.Prime 149651547511777 :=
  (pratt 149651547511777 7 [2, 3, 107, 193, 619, 121949] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), pp121949⟩) (by decide +kernel))

theorem pp282881385328897 : Nat.Prime 282881385328897 :=
  (pratt 282881385328897 5 [2, 3, 139, 173, 1951, 2617] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp447829 : Nat.Prime 447829 :=
  (pratt 447829 2 [2, 3, 67, 557] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp447829001 : Nat.Prime 447829001 :=
  (pratt 447829001 3 [2, 5, 447829] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp447829⟩) (by decide +kernel))

theorem pp320430606795521 : Nat.Prime 320430606795521 :=
  (pratt 320430606795521 3 [2, 5, 13, 43, 447829001] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp447829001⟩) (by decide +kernel))

theorem pp2724909545357921 : Nat.Prime 2724909545357921 :=
  (pratt 2724909545357921 3 [2, 5, 17, 23, 67, 83, 433, 18089] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp131476769343937 : Nat.Prime 131476769343937 :=
  (pratt 131476769343937 5 [2, 3, 1103, 4817, 42961] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp892951 : Nat.Prime 892951 :=
  (pratt 892951 3 [2, 3, 5, 5953] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp1934773 : Nat.Prime 1934773 :=
  (pratt 1934773 2 [2, 3, 7, 31, 743] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp6634204742872321 : Nat.Prime 6634204742872321 :=
  (pratt 6634204742872321 7 [2, 3, 5, 892951, 1934773] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp892951, pp1934773⟩) (by decide +kernel))

theorem pp219886593426337 : Nat.Prime 219886593426337 :=
  (pratt 219886593426337 7 [2, 3, 4889, 10007, 46817] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp248789 : Nat.Prime 248789 :=
  (pratt 248789 2 [2, 37, 41] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp497579 : Nat.Prime 497579 :=
  (pratt 497579 2 [2, 248789] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, pp248789⟩) (by decide +kernel))

theorem pp114443171 : Nat.Prime 114443171 :=
  (pratt 114443171 2 [2, 5, 23, 497579] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp497579⟩) (by decide +kernel))

theorem pp2992331858956481 : Nat.Prime 2992331858956481 :=
  (pratt 2992331858956481 3 [2, 5, 101, 809, 114443171] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp114443171⟩) (by decide +kernel))

theorem pp1854119700479617 : Nat.Prime 1854119700479617 :=
  (pratt 1854119700479617 5 [2, 3, 19, 29, 373, 1069, 21977] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp393273536839297 : Nat.Prime 393273536839297 :=
  (pratt 393273536839297 5 [2, 3, 97, 179, 887, 66499] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp183383 : Nat.Prime 183383 :=
  (pratt 183383 5 [2, 91691] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num)⟩) (by decide +kernel))

theorem pp4240451 : Nat.Prime 4240451 :=
  (pratt 4240451 2 [2, 5, 84809] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp24759631763338721 : Nat.Prime 24759631763338721 :=
  (pratt 24759631763338721 3 [2, 5, 199, 183383, 4240451] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp183383, pp4240451⟩) (by decide +kernel))

theorem pp37588592026706177 : Nat.Prime 37588592026706177 :=
  (pratt 37588592026706177 3 [2, 59] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num)⟩) (by decide +kernel))

theorem pp108529 : Nat.Prime 108529 :=
  (pratt 108529 23 [2, 3, 7, 17, 19] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp403057 : Nat.Prime 403057 :=
  (pratt 403057 5 [2, 3, 311] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp3283902509342017 : Nat.Prime 3283902509342017 :=
  (pratt 3283902509342017 7 [2, 3, 17, 23, 108529, 403057] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), pp108529, pp403057⟩) (by decide +kernel))

theorem pp183119 : Nat.Prime 183119 :=
  (pratt 183119 17 [2, 13, 7043] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp366239 : Nat.Prime 366239 :=
  (pratt 366239 11 [2, 183119] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, pp183119⟩) (by decide +kernel))

theorem pp109897 : Nat.Prime 109897 :=
  (pratt 109897 10 [2, 3, 19, 241] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp19561667 : Nat.Prime 19561667 :=
  (pratt 19561667 2 [2, 89, 109897] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp109897⟩) (by decide +kernel))

theorem pp2112660037 : Nat.Prime 2112660037 :=
  (pratt 2112660037 5 [2, 3, 19561667] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp19561667⟩) (by decide +kernel))

theorem pp24759631977306977 : Nat.Prime 24759631977306977 :=
  (pratt 24759631977306977 3 [2, 366239, 2112660037] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, pp366239, pp2112660037⟩) (by decide +kernel))

theorem pp49077072127310497 : Nat.Prime 49077072127310497 :=
  (pratt 49077072127310497 5 [2, 3, 29, 97, 101, 131, 1009, 13613] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp132263 : Nat.Prime 132263 :=
  (pratt 132263 5 [2, 13, 5087] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp1647977 : Nat.Prime 1647977 :=
  (pratt 1647977 3 [2, 11, 61, 307] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp9227824746277537 : Nat.Prime 9227824746277537 :=
  (pratt 9227824746277537 19 [2, 3, 7, 132263, 1647977] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), pp132263, pp1647977⟩) (by decide +kernel))

theorem pp1476118249 : Nat.Prime 1476118249 :=
  (pratt 1476118249 13 [2, 3, 11, 727, 7691] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), (by norm_num), (by norm_num), (by norm_num)⟩) (by decide +kernel))

theorem pp773816612963777 : Nat.Prime 773816612963777 :=
  (pratt 773816612963777 3 [2, 8191, 1476118249] (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨Nat.prime_two, (by norm_num), pp1476118249⟩) (by decide +kernel))

end OMA.A218656H1

open OMA.A218656H1 in
theorem OMA.solution : OMA.R_OeisA218656_conjecture_3_R1.H1 := by
  intro n h1 h64 hex
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hex
  interval_cases n
  · exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  · omega
  · omega
  · exact ⟨5, by norm_num, by norm_num, pp2070241⟩
  · exact ⟨3, by norm_num, by norm_num, pp100006561⟩
  · exact ⟨2, by norm_num, by norm_num, pp815730977⟩
  · exact ⟨3, by norm_num, by norm_num, pp1475795617⟩
  · exact ⟨7, by norm_num, by norm_num, pp435746497⟩
  · exact ⟨8, by norm_num, by norm_num, pp832507937⟩
  · exact ⟨4, by norm_num, by norm_num, pp16983628577⟩
  · exact ⟨9, by norm_num, by norm_num, pp4338014017⟩
  · exact ⟨7, by norm_num, by norm_num, pp25605764801⟩
  · exact ⟨13, by norm_num, by norm_num, pp5110698017⟩
  · exact ⟨3, by norm_num, by norm_num, pp377802004897⟩
  · exact ⟨8, by norm_num, by norm_num, pp152604667841⟩
  · exact ⟨17, by norm_num, by norm_num, pp17995718017⟩
  · exact ⟨17, by norm_num, by norm_num, pp32575757441⟩
  · exact ⟨11, by norm_num, by norm_num, pp378016357217⟩
  · exact ⟨17, by norm_num, by norm_num, pp117051071617⟩
  · exact ⟨8, by norm_num, by norm_num, pp2251892167841⟩
  · exact ⟨14, by norm_num, by norm_num, pp854366826497⟩
  · exact ⟨13, by norm_num, by norm_num, pp1786609635617⟩
  · exact ⟨19, by norm_num, by norm_num, pp673083563041⟩
  · exact ⟨22, by norm_num, by norm_num, pp555122286497⟩
  · exact ⟨21, by norm_num, by norm_num, pp1137334487137⟩
  · omega
  · exact ⟨25, by norm_num, by norm_num, pp1252099518401⟩
  · exact ⟨16, by norm_num, by norm_num, pp11692495244897⟩
  · exact ⟨27, by norm_num, by norm_num, pp2068223441377⟩
  · exact ⟨23, by norm_num, by norm_num, pp6631910985281⟩
  · exact ⟨32, by norm_num, by norm_num, pp2505920246017⟩
  · exact ⟨6, by norm_num, by norm_num, pp191707314676897⟩
  · exact ⟨11, by norm_num, by norm_num, pp128063296076897⟩
  · exact ⟨31, by norm_num, by norm_num, pp7406491037441⟩
  · omega
  · omega
  · exact ⟨37, by norm_num, by norm_num, pp10066079453921⟩
  · exact ⟨26, by norm_num, by norm_num, pp62468517475937⟩
  · exact ⟨17, by norm_num, by norm_num, pp281481952468097⟩
  · exact ⟨36, by norm_num, by norm_num, pp26632396569217⟩
  · exact ⟨42, by norm_num, by norm_num, pp21370852274017⟩
  · exact ⟨31, by norm_num, by norm_num, pp97570202611457⟩
  · exact ⟨13, by norm_num, by norm_num, pp1113035603185697⟩
  · exact ⟨34, by norm_num, by norm_num, pp113214951016897⟩
  · exact ⟨38, by norm_num, by norm_num, pp88081730029121⟩
  · exact ⟨36, by norm_num, by norm_num, pp149651547511777⟩
  · exact ⟨33, by norm_num, by norm_num, pp282881385328897⟩
  · exact ⟨34, by norm_num, by norm_num, pp320430606795521⟩
  · exact ⟨16, by norm_num, by norm_num, pp2724909545357921⟩
  · exact ⟨46, by norm_num, by norm_num, pp131476769343937⟩
  · omega
  · exact ⟨12, by norm_num, by norm_num, pp6634204742872321⟩
  · exact ⟨48, by norm_num, by norm_num, pp219886593426337⟩
  · exact ⟨25, by norm_num, by norm_num, pp2992331858956481⟩
  · exact ⟨32, by norm_num, by norm_num, pp1854119700479617⟩
  · exact ⟨49, by norm_num, by norm_num, pp393273536839297⟩
  · exact ⟨5, by norm_num, by norm_num, pp24759631763338721⟩
  · exact ⟨1, by norm_num, by norm_num, pp37588592026706177⟩
  · exact ⟨34, by norm_num, by norm_num, pp3283902509342017⟩
  · exact ⟨11, by norm_num, by norm_num, pp24759631977306977⟩
  · exact ⟨3, by norm_num, by norm_num, pp49077072127310497⟩
  · exact ⟨28, by norm_num, by norm_num, pp9227824746277537⟩
  · exact ⟨58, by norm_num, by norm_num, pp773816612963777⟩
