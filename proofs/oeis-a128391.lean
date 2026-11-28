import OMAStatements.S_oeis_a128391

namespace OMA.S_oeis_a128391

open PowerSeries




/-! ### Coefficient lists of the truncated product

A list `L` represents a power series `F` up to degree `N` when it has length `N + 1` and its `j`-th
entry is the coefficient of `X ^ j` in `F`. Multiplying by `1 - X ^ a` subtracts the list shifted by
`a`; the product is built from 24 such passes per factor. -/

/-- `L` represents `F` up to degree `N`. -/
def Rep (N : ℕ) (L : List ℤ) (F : PowerSeries ℤ) : Prop :=
  L.length = N + 1 ∧ ∀ j, j ≤ N → L.getD j 0 = coeff j F

/-- One multiplication by `1 - X ^ a`, truncated to the length of `L`: subtract `L` shifted by `a`. -/
def pass (a : ℕ) (L : List ℤ) : List ℤ :=
  List.zipWith (fun x y => x - y) L (List.replicate a 0 ++ L)

theorem pass_length (a : ℕ) (L : List ℤ) : (pass a L).length = L.length := by
  simp [pass]

theorem pass_getD (a : ℕ) (L : List ℤ) (j : ℕ) (hj : j < L.length) :
    (pass a L).getD j 0 = L.getD j 0 - if a ≤ j then L.getD (j - a) 0 else 0 := by
  have h2 : j < (List.replicate a (0 : ℤ) ++ L).length := by simp; omega
  rw [List.getD_eq_getElem _ _ (by simpa [pass_length] using hj), List.getD_eq_getElem _ _ hj]
  simp only [pass, List.getElem_zipWith]
  congr 1
  split_ifs with ha
  · rw [List.getElem_append_right (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
    simp
  · rw [List.getElem_append_left (by simp; omega)]
    simp

/-- `r` multiplications by `1 - X ^ a`. -/
def passes (a : ℕ) : ℕ → List ℤ → List ℤ
  | 0, L => L
  | r + 1, L => pass a (passes a r L)

/-- Coefficients of degrees `0 .. N` of `∏_{i < m} (1 - X ^ (i + 1)) ^ 24`. -/
def coeffs (N : ℕ) : ℕ → List ℤ
  | 0 => (List.range (N + 1)).map (fun j => if j = 0 then 1 else 0)
  | m + 1 => passes (m + 1) 24 (coeffs N m)

theorem getD_map_range (f : ℕ → ℤ) (n j : ℕ) (h : j < n) :
    ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, h]

theorem pass_rep {N a : ℕ} {L : List ℤ} {F : PowerSeries ℤ} (h : Rep N L F) :
    Rep N (pass a L) (F * (1 - X ^ a)) := by
  obtain ⟨hl, hc⟩ := h
  refine ⟨by rw [pass_length, hl], fun j hj => ?_⟩
  rw [pass_getD a L j (by omega), mul_sub, mul_one, map_sub, coeff_mul_X_pow', hc j hj]
  split_ifs with ha
  · rw [hc (j - a) (by omega)]
  · rfl

theorem passes_rep {N a : ℕ} {L : List ℤ} {F : PowerSeries ℤ} (h : Rep N L F) :
    ∀ r, Rep N (passes a r L) (F * (1 - X ^ a) ^ r) := by
  intro r
  induction r with
  | zero => simpa [passes] using h
  | succ r ih =>
    rw [passes, pow_succ, ← mul_assoc]
    exact pass_rep ih

theorem coeffs_spec (N : ℕ) : ∀ m,
    Rep N (coeffs N m) (∏ i ∈ Finset.range m, (1 - (X : PowerSeries ℤ) ^ (i + 1)) ^ 24) := by
  intro m
  induction m with
  | zero =>
    refine ⟨by simp [coeffs], fun j hj => ?_⟩
    rw [coeffs, getD_map_range _ _ _ (by omega), Finset.prod_range_zero, coeff_one]
  | succ m ih =>
    rw [coeffs, Finset.prod_range_succ]
    exact passes_rep ih 24

theorem tau_eq (n : ℕ) : tau (n + 1) = (coeffs n (n + 1)).getD n 0 := by
  unfold tau
  rw [coeff_succ_X_mul, ((coeffs_spec n (n + 1)).2 n le_rfl)]

theorem tau_one : tau 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, tau_eq]
  decide +kernel

theorem tau_two : tau 2 = -24 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, tau_eq]
  decide +kernel

/-- `coeffsFrom s L k` continues the product from `s` factors (list `L`) by `k` more factors. -/
def coeffsFrom (s : ℕ) (L : List ℤ) : ℕ → List ℤ
  | 0 => L
  | k + 1 => passes (s + k + 1) 24 (coeffsFrom s L k)

theorem coeffs_add (N s : ℕ) : ∀ k, coeffs N (s + k) = coeffsFrom s (coeffs N s) k
  | 0 => rfl
  | k + 1 => by
    rw [show s + (k + 1) = s + k + 1 from rfl, coeffs, coeffs_add N s k, coeffsFrom]

/-! The coefficients of degrees `0 .. 58` after `5, 10, ..., 55, 59` factors, each stage checked in
the kernel from the previous one (a single run of all 1416 passes recurses too deeply). -/

theorem st5 : coeffs 58 5 =
    [1, -24, 252, -1472, 4830, -6048, -16720, 83928, -108147, -145752, 620700, -430008, -1038358,
      1961832, 118980, -3272096, 2777526, 2647944, -8861624, 2816304, 19113552, -14917064,
      -29761080, 26283456, 24219093, -26964624, 57605616, 19266088, -284750328, -85192392,
      532895072, 399748488, -237977112, -630555280, -1436451384, -993216360, 3547467674,
      6535874280, -90011028, -11399920928, -15326502042, -4366830048, 26559624348, 56637626592,
      24224818494, -84490357216, -163918538748, -80246163696, 184596368680, 453371919984,
      350593188852, -379079271880, -1264244844198, -1159564051752, 612736063224, 3074772924384,
      3624319937400, -141528533960, -7041529764000] := by
  decide +kernel

theorem st10 : coeffs 58 10 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370920, -578290,
      407352, 1187328, 1073224, -6964998, 2266512, 12228020, -8270592, -8162400, -3942912,
      18628692, 7401744, -29672621, 38525184, -23816340, -92492800, 71144586, 189262560,
      -21359872, -312769824, -177244992, 291206936, 391799112, -20382552, 272458278, -969340104,
      -1756513632, 1326735680, 3119361474, 1906412544, -4091766380, -5743492152, 101443524,
      4170364896, 9577752804, 8121166992, -12493281217, -29730994320, -5158357956, 33909235088,
      48037870266, -913711824, -62793250476, -63285718608, -27773955144, 107762637608,
      178887827904] := by
  rw [show (10 : ℕ) = 5 + 5 from rfl, coeffs_add, st5]
  decide +kernel

theorem st15 : coeffs 58 15 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905910, 2726880, 10666916, -7139592, -4133400, -12889752,
      18182352, 22855560, -26660057, 9922800, -64391304, 24632288, 114526038, -33447888,
      -27867376, -148039248, 17647164, 114118800, 123446220, 200589024, -249062494, -631520064,
      -79377876, 1005047904, 276791682, 356436936, -1408621588, -1596922104, 1559221062,
      910685784, 3089627904, -3486744936, -3686071975, 2095995312, 267563760, 7175222208,
      -400874202, -7897949304, -9328300120, 3420713016, 14387784708, 14600178992, -5967690720] := by
  rw [show (15 : ℕ) = 10 + 5 from rfl, coeffs_add, st10]
  decide +kernel

theorem st20 : coeffs 58 20 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830664,
      18642720, 21294456, -25529057, 13951800, -73338144, 24186248, 129973230, -30372672,
      -56786080, -187818528, 134707344, 151861824, -85109568, 192258288, -133546258, -372949440,
      -197206968, 612295488, 341743290, 33622848, -392706784, -715098336, 33959154, -476944056,
      2991732060, -1206416376, -2566188267, 2844379824, -225337968, 1050872600, -6004531914,
      573545688, 5211172584, -775409256, 7652972736, -1905415080, -11640777156] := by
  rw [show (20 : ℕ) = 15 + 5 from rfl, coeffs_add, st15]
  decide +kernel

theorem st25 : coeffs 58 25 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279056, 24646616, 128412126, -29241672,
      -52757080, -196765368, 134261304, 167309016, -82034352, 163339584, -173325538, -255888960,
      -159470568, 403802352, 333096234, 149934768, -134201068, -838565856, -344638602,
      -413815680, 2619703632, -126823104, -1625108055, 1194773592, -1769484576, 1154018216,
      -3051165438, 895113288, 4800419724, 102247512, 2936334444, -7553914104, -6433605792] := by
  rw [show (25 : ℕ) = 20 + 5 from rfl, coeffs_add, st20]
  decide +kernel

theorem st30 : coeffs 58 30 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
      -52843168, -196706280, 134721672, 165747912, -80903352, 167368584, -182272378, -256335000,
      -144023376, 406877568, 304177530, 110155488, -17140588, -800829456, -553131738, -422462736,
      2736015552, 131682912, -1748582199, 816238488, -1706672520, 782785472, -1971637074,
      1830555072, 3164968152, -1443722328, 2990265720, -4536869160, -6052781748] := by
  rw [show (30 : ℕ) = 25 + 5 from rfl, coeffs_add, st25]
  decide +kernel

theorem st35 : coeffs 58 35 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
      -52843168, -196706304, 134722224, 165742416, -80873520, 167282496, -182213290, -255874632,
      -145584480, 408008568, 308206530, 101208648, -17586628, -785382264, -550056522, -451381440,
      2696236272, 248743392, -1710845799, 607745352, -1715319576, 899097392, -1713131058,
      1707080928, 2786433048, -1380910272, 2619032976, -3457340496, -5117346588] := by
  rw [show (35 : ℕ) = 30 + 5 from rfl, coeffs_add, st30]
  decide +kernel

theorem st40 : coeffs 58 40 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
      -52843168, -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080,
      -145589976, 408038400, 308120442, 101267736, -17126260, -786943368, -548925522, -447352440,
      2687289432, 248297352, -1695398607, 610820568, -1744238280, 859318112, -1596070578,
      1744817328, 2577939912, -1389557328, 2735344896, -3198834480, -5240820732] := by
  rw [show (40 : ℕ) = 35 + 5 from rfl, coeffs_add, st35]
  decide +kernel

theorem st45 : coeffs 58 45 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
      -52843168, -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080,
      -145589976, 408038400, 308120442, 101267712, -17125708, -786948864, -548895690, -447438528,
      2687348520, 248757720, -1696959711, 611951568, -1740209280, 850371272, -1596516618,
      1760264520, 2581015128, -1418476032, 2695565616, -3081774000, -5203084332] := by
  rw [show (45 : ℕ) = 40 + 5 from rfl, coeffs_add, st40]
  decide +kernel

theorem st50 : coeffs 58 50 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
      -52843168, -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080,
      -145589976, 408038400, 308120442, 101267712, -17125708, -786948864, -548895690, -447438528,
      2687348496, 248758272, -1696965207, 611981400, -1740295368, 850430360, -1596056250,
      1758703416, 2582146128, -1414447032, 2686618776, -3082220040, -5187637140] := by
  rw [show (50 : ℕ) = 45 + 5 from rfl, coeffs_add, st45]
  decide +kernel

theorem st55 : coeffs 58 55 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
      -52843168, -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080,
      -145589976, 408038400, 308120442, 101267712, -17125708, -786948864, -548895690, -447438528,
      2687348496, 248758272, -1696965207, 611981400, -1740295368, 850430336, -1596055698,
      1758697920, 2582175960, -1414533120, 2686677864, -3081759672, -5189198244] := by
  rw [show (55 : ℕ) = 50 + 5 from rfl, coeffs_add, st50]
  decide +kernel

theorem st59 : coeffs 58 59 =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
      401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
      18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
      -52843168, -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080,
      -145589976, 408038400, 308120442, 101267712, -17125708, -786948864, -548895690, -447438528,
      2687348496, 248758272, -1696965207, 611981400, -1740295368, 850430336, -1596055698,
      1758697920, 2582175960, -1414533120, 2686677840, -3081759120, -5189203740] := by
  rw [show (59 : ℕ) = 55 + 4 from rfl, coeffs_add, st55]
  decide +kernel

theorem tau_59 : tau 59 = -5189203740 := by
  rw [show (59 : ℕ) = 58 + 1 from rfl, tau_eq, st59]
  rfl

/-! ### The matrix A054523 at 1 and at primes -/

theorem app_one (g : ℕ → ℤ) : app g 1 = g 1 := by
  simp [app, T]

theorem app_prime (g : ℕ → ℤ) (p : ℕ) (hp : p.Prime) : app g p = ((p - 1 : ℕ) : ℤ) * g 1 + g p := by
  have h1 : 1 ≠ p := hp.one_lt.ne
  rw [app, Finset.sum_eq_add 1 p h1]
  · simp [T, Nat.totient_prime hp, Nat.div_self hp.pos]
  · intro c hc hne
    have hc' := Finset.mem_Icc.mp hc
    have : ¬ c ∣ p := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with h | h
      · exact hne.1 h
      · exact hne.2 h
    simp [T, this]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hp.one_lt.le⟩) h
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨hp.one_lt.le, le_rfl⟩) h

theorem iter (p : ℕ) (hp : p.Prime) (k : ℕ) :
    (app^[k] tau) 1 = tau 1 ∧ (app^[k] tau) p = tau p + k * ((p - 1 : ℕ) : ℤ) * tau 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, hp'⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · rw [app_one, h1]
    · rw [app_prime _ p hp, h1, hp']
      push_cast
      ring

/-- Control: the zero of A128391 itself, at n = 2 for k = 24. -/
theorem control : (app^[24] tau) 2 = 0 := by
  rw [(iter 2 Nat.prime_two 24).2, tau_two, tau_one]
  norm_num

theorem disproof : ¬ (∀ k : ℕ, 1 ≤ k → ((∃ n : ℕ, 1 ≤ n ∧ (app^[k] tau) n = 0) ↔ k = 24)) := by
  intro h
  have hz : (app^[89469030] tau) 59 = 0 := by
    rw [(iter 59 (by norm_num) 89469030).2, tau_59, tau_one]
    norm_num
  have := (h 89469030 (by norm_num)).mp ⟨59, by norm_num, hz⟩
  norm_num at this

end OMA.S_oeis_a128391

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128391.main) :=
  OMA.S_oeis_a128391.disproof
