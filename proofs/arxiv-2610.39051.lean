import OMAStatements.S_arxiv_2610_39051

/-!  Disproof of the Fasi-Higham positivity conjecture as stated in
arxiv-2610.39051: the claim is that every Taylor coefficient of the reciprocal
of the Pade denominator qPade k m is positive when m is odd.  Scardino
(arXiv:2610.39051, Thm 8.5) gives the exact counterexample c_38(66,5) < 0; the
proof below derives the coefficient recurrence for an arbitrary inverse c of
qPade 66 5 and evaluates it up to the 38th term in exact rational arithmetic. -/

open PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_39051.main) := by
  intro h
  have hq0 : PowerSeries.coeff 0 (OMA.S_arxiv_2610_39051.qPade 66 5) = 1 := by
    rw [OMA.S_arxiv_2610_39051.qPade]
    simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    norm_num
  have hq1 : PowerSeries.coeff 1 (OMA.S_arxiv_2610_39051.qPade 66 5) = ((-5 : ℚ) / 71) := by
    rw [OMA.S_arxiv_2610_39051.qPade]
    simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    norm_num
  have hq2 : PowerSeries.coeff 2 (OMA.S_arxiv_2610_39051.qPade 66 5) = ((1 : ℚ) / 497) := by
    rw [OMA.S_arxiv_2610_39051.qPade]
    simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    norm_num
  have hq3 : PowerSeries.coeff 3 (OMA.S_arxiv_2610_39051.qPade 66 5) = ((-1 : ℚ) / 34293) := by
    rw [OMA.S_arxiv_2610_39051.qPade]
    simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    norm_num
  have hq4 : PowerSeries.coeff 4 (OMA.S_arxiv_2610_39051.qPade 66 5) = ((1 : ℚ) / 4663848) := by
    rw [OMA.S_arxiv_2610_39051.qPade]
    simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    norm_num
  have hq5 : PowerSeries.coeff 5 (OMA.S_arxiv_2610_39051.qPade 66 5) = ((-1 : ℚ) / 1562389080) := by
    rw [OMA.S_arxiv_2610_39051.qPade]
    simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    norm_num
  have hqdeg : ∀ j, 5 < j → PowerSeries.coeff j (OMA.S_arxiv_2610_39051.qPade 66 5) = 0 := by
    intro j hj
    rw [OMA.S_arxiv_2610_39051.qPade]
    simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
    rw [if_neg (by omega)]
  have hq0c : PowerSeries.constantCoeff (OMA.S_arxiv_2610_39051.qPade 66 5) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hq0
  have hunit : IsUnit (OMA.S_arxiv_2610_39051.qPade 66 5) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hq0c]
    exact isUnit_one
  obtain ⟨c, hc, -⟩ := isUnit_iff_exists.mp hunit
  have h0c : PowerSeries.coeff 0 c = 1 := by
    have h1 : PowerSeries.coeff 0 (OMA.S_arxiv_2610_39051.qPade 66 5 * c) = 1 := by rw [hc]; simp
    rw [PowerSeries.coeff_mul] at h1
    simp at h1
    rw [hq0c] at h1
    simpa using h1
  have hrec : ∀ (c' : PowerSeries ℚ), OMA.S_arxiv_2610_39051.qPade 66 5 * c' = 1 → ∀ n, 1 ≤ n →
      PowerSeries.coeff n c' =
        -∑ j ∈ Finset.range n, PowerSeries.coeff (j+1) (OMA.S_arxiv_2610_39051.qPade 66 5) * PowerSeries.coeff (n-(j+1)) c' := by
    intro c' hc' n hn
    have h1 : PowerSeries.coeff n (OMA.S_arxiv_2610_39051.qPade 66 5 * c') = 0 := by
      rw [hc']
      simp [show n ≠ 0 by omega]
    rw [PowerSeries.coeff_mul] at h1
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (OMA.S_arxiv_2610_39051.qPade 66 5) * PowerSeries.coeff b c') n] at h1
    rw [Finset.sum_range_succ'] at h1
    have h0 : PowerSeries.coeff 0 (OMA.S_arxiv_2610_39051.qPade 66 5) * PowerSeries.coeff (n - 0) c' = PowerSeries.coeff n c' := by
      rw [hq0]; simp
    rw [h0] at h1
    linarith
  have hrecgt : ∀ (c' : PowerSeries ℚ), OMA.S_arxiv_2610_39051.qPade 66 5 * c' = 1 → ∀ n, 5 < n →
      PowerSeries.coeff n c' =
        -∑ j ∈ Finset.range 5, PowerSeries.coeff (j+1) (OMA.S_arxiv_2610_39051.qPade 66 5) * PowerSeries.coeff (n-(j+1)) c' := by
    intro c' hc' n hn
    rw [hrec c' hc' n (by omega)]
    congr 1
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hxnot
      simp only [Finset.mem_range, not_lt] at hx hxnot
      rw [hqdeg (x+1) (by omega), zero_mul]
  have h1 : PowerSeries.coeff 1 c = ((5 : ℚ) / 71) := by
    rw [hrec c hc 1 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, h0c]
    norm_num
  have h2 : PowerSeries.coeff 2 c = ((104 : ℚ) / 35287) := by
    rw [hrec c hc 2 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, h1, h0c]
    norm_num
  have h3 : PowerSeries.coeff 3 c = ((16426 : ℚ) / 172871013) := by
    rw [hrec c hc 3 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, h2, h1, h0c]
    norm_num
  have h4 : PowerSeries.coeff 4 c = ((30386087 : ℚ) / 11684697510696) := by
    rw [hrec c hc 4 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, h3, h2, h1, h0c]
    norm_num
  have h5 : PowerSeries.coeff 5 c = ((17629371097 : ℚ) / 277920530291904360) := by
    rw [hrec c hc 5 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h4, h3, h2, h1, h0c]
    norm_num
  have h6 : PowerSeries.coeff 6 c = ((159068099753 : ℚ) / 112126220532944426088) := by
    rw [hrecgt c hc 6 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h5, h4, h3, h2, h1]
    norm_num
  have h7 : PowerSeries.coeff 7 c = ((20041818509089 : ℚ) / 676681740916319611441080) := by
    rw [hrecgt c hc 7 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h6, h5, h4, h3, h2]
    norm_num
  have h8 : PowerSeries.coeff 8 c = ((26724791796601183 : ℚ) / 45738272232015875176525479360) := by
    rw [hrecgt c hc 8 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h7, h6, h5, h4, h3]
    norm_num
  have h9 : PowerSeries.coeff 9 c = ((2461785873375280559 : ℚ) / 224071795664645772489798323384640) := by
    rw [hrecgt c hc 9 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h8, h7, h6, h5, h4]
    norm_num
  have h10 : PowerSeries.coeff 10 c = ((160696455579142903487 : ℚ) / 811018122156199954145412431563600800) := by
    rw [hrecgt c hc 10 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h9, h8, h7, h6, h5]
    norm_num
  have h11 : PowerSeries.coeff 11 c = ((16288708172590005913 : ℚ) / 4729973548146694732569494645512000380) := by
    rw [hrecgt c hc 11 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h10, h9, h8, h7, h6]
    norm_num
  have h12 : PowerSeries.coeff 12 c = ((715130794182289905312361531 : ℚ) / 12353531496643044923658672579549837091026854400) := by
    rw [hrecgt c hc 12 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h11, h10, h9, h8, h7]
    norm_num
  have h13 : PowerSeries.coeff 13 c = ((827848175231854168681082291 : ℚ) / 877100736261656189579765753148038433462906662400) := by
    rw [hrecgt c hc 13 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h12, h11, h10, h9, h8]
    norm_num
  have h14 : PowerSeries.coeff 14 c = ((283527213250964903697795007 : ℚ) / 18953002866175788096571459970198917453524548313600) := by
    rw [hrecgt c hc 14 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h13, h12, h11, h10, h9]
    norm_num
  have h15 : PowerSeries.coeff 15 c = ((165186158276454314606039149335491 : ℚ) / 715415113823949907244723102345804646340113152661054912000) := by
    rw [hrecgt c hc 15 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h14, h13, h12, h11, h10]
    norm_num
  have h16 : PowerSeries.coeff 16 c = ((6722649020428978604276657659609243 : ℚ) / 1934253534943536885219412957350305106216837128586640944476160) := by
    rw [hrecgt c hc 16 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h15, h14, h13, h12, h11]
    norm_num
  have h17 : PowerSeries.coeff 17 c = ((175381950458140164805700751092034271 : ℚ) / 3433300024524777971264457999296791563534885903241287676445184000) := by
    rw [hrecgt c hc 17 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h16, h15, h14, h13, h12]
    norm_num
  have h18 : PowerSeries.coeff 18 c = ((21600176205953975383567303121320577687 : ℚ) / 29434539435257052742143014542471218272075460569963369572083673728000) := by
    rw [hrecgt c hc 18 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h17, h16, h15, h14, h13]
    norm_num
  have h19 : PowerSeries.coeff 19 c = ((43107429237589416548612681182174839341 : ℚ) / 4179704599806501489384308065030912994634715400934798479235881669376000) := by
    rw [hrecgt c hc 19 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h18, h17, h16, h15, h14]
    norm_num
  have h20 : PowerSeries.coeff 20 c = ((26864964793200995286354354786919764086727059 : ℚ) / 189284777517781102609210980990151545659344287864589882201702848243629936640000) := by
    rw [hrecgt c hc 20 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h19, h18, h17, h16, h15]
    norm_num
  have h21 : PowerSeries.coeff 21 c = ((14200002156277197464367668896357415119006283 : ℚ) / 7418449000476876973460196766966019377481021329989006663249138028364344476794880) := by
    rw [hrecgt c hc 21 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h20, h19, h18, h17, h16]
    norm_num
  have h22 : PowerSeries.coeff 22 c = ((2334226098111054261522383608260982981501722079 : ℚ) / 92174228830925196395242944829552790765201690025113407790870540002426980124176384000) := by
    rw [hrecgt c hc 22 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h21, h20, h19, h18, h17]
    norm_num
  have h23 : PowerSeries.coeff 23 c = ((2153157703197784510566508452710515579322846659 : ℚ) / 6544370246995688944062249082898248144329319991783051953151808340172315588816523264000) := by
    rw [hrecgt c hc 23 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h22, h21, h20, h19, h18]
    norm_num
  have h24 : PowerSeries.coeff 24 c = ((25654618109497274404770517097369406827158333651777 : ℚ) / 6104389617542069978077366452155365762286802077007480657120631004739194742854152878351974400) := by
    rw [hrecgt c hc 24 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h23, h22, h21, h20, h19]
    norm_num
  have h25 : PowerSeries.coeff 25 c = ((27405852592730442578807848462692404588741375787954301 : ℚ) / 518546096618707622959179146658983480914255669291510455105765030170434810567092950755720396800000) := by
    rw [hrecgt c hc 25 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h24, h23, h22, h21, h20]
    norm_num
  have h26 : PowerSeries.coeff 26 c = ((118203975142443801188895881865821970250738785809834437 : ℚ) / 180402187013648382027498425122660353010069547346516487331295653996294270596291637567915126046720000) := by
    rw [hrecgt c hc 26 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h25, h24, h23, h22, h21]
    norm_num
  have h27 : PowerSeries.coeff 27 c = ((17713658258206337794023966845111205715411482277052445173 : ℚ) / 2209475785449658558881786961689782673490826781126460678590043522319614079128081831113040506257203200000) := by
    rw [hrecgt c hc 27 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h26, h25, h24, h23, h22]
    norm_num
  have h28 : PowerSeries.coeff 28 c = ((57864592574438925389498087431328269430955471909194801059609 : ℚ) / 597371549160453285247750977258143161866367855159598920749032887042509419345701228514370535595747514777600000) := by
    rw [hrecgt c hc 28 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h27, h26, h25, h24, h23]
    norm_num
  have h29 : PowerSeries.coeff 29 c = ((2881293040997787676037870373863761006091717224534659385697 : ℚ) / 2494904705317187250152371728548715558383065748019501374893019704706951104326163954383547531017533738188800000) := by
    rw [hrecgt c hc 29 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h28, h27, h26, h25, h24]
    norm_num
  have h30 : PowerSeries.coeff 30 c = ((6601919774533048130913604400216450985857009533219721379175654957 : ℚ) / 487251483403523911994161740598154679555475547703462571897230019357370625686642415077309099265344500134720012288000000) := by
    rw [hrecgt c hc 30 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h29, h28, h27, h26, h25]
    norm_num
  have h31 : PowerSeries.coeff 31 c = ((1075966283330149843090551853212517091912329003792889355969283537 : ℚ) / 6918971064330039550317096716493796449687752777389168520940666274874662884750322294097789209567891901913024174489600000) := by
    rw [hrecgt c hc 31 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h30, h29, h28, h27, h26]
    norm_num
  have h32 : PowerSeries.coeff 32 c = ((4039942862146108914880202767070055032440804278625627053048736539761 : ℚ) / 2338335460900980166425166006306243448136472928646443393337107574256641068530218922513288841265564747170525650010505216000000) := by
    rw [hrecgt c hc 32 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h31, h30, h29, h28, h27]
    norm_num
  have h33 : PowerSeries.coeff 33 c = ((209096695774793384829926523123111623060914616825381518543330877184649 : ℚ) / 11455505422953901835316888264894286652420580877438926183958490006283284594729542501392602033360001696388405159401465053184000000) := by
    rw [hrecgt c hc 33 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h32, h31, h30, h29, h28]
    norm_num
  have h34 : PowerSeries.coeff 34 c = ((126596142197818046022303007984544298837199370801997170343033451939387 : ℚ) / 711673274401011151519061683456557558281628587010893289178421191640349055447572827899015401322490105388129670527816016429056000000) := by
    rw [hrecgt c hc 34 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h33, h32, h31, h30, h29]
    norm_num
  have h35 : PowerSeries.coeff 35 c = ((102238992981566109531250793038816495849208544688860231182772842813134307 : ℚ) / 67708595326512200955523528564056886094914143768216387532434992172662809135282078846312325281821708626626656854016415803060387840000000) := by
    rw [hrecgt c hc 35 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h34, h33, h32, h31, h30]
    norm_num
  have h36 : PowerSeries.coeff 36 c = ((1234264354757133296072326458243427370622216175298390703519672452649310193761 : ℚ) / 126313038758545310160806599058567832039997255834043385024148749349795638823986821145286418256389444853950192126116301124108633482723328000000) := by
    rw [hrecgt c hc 36 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h35, h34, h33, h32, h31]
    norm_num
  have h37 : PowerSeries.coeff 37 c = ((1311402332658709354967161108179637503672420373189750521518234246887628910037 : ℚ) / 44841128759283585107086342665791580374199025821085401683572806019177451782515321506576678481018252923152318204771286899058564886366781440000000) := by
    rw [hrecgt c hc 37 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h36, h35, h34, h33, h32]
    norm_num
  have h38 : PowerSeries.coeff 38 c = ((-625387044196041302769979230262974179147391857970590017827905300559706838051 : ℚ) / 22286040993363941798221912304898415445976915833079444636735684591531193535910114788768609205066071702806702147771329588832106748524290375680000000) := by
    rw [hrecgt c hc 38 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hq1, hq2, hq3, hq4, hq5, h37, h36, h35, h34, h33]
    norm_num
  have hpos := h 66 5 (by decide) c hc 38
  rw [h38] at hpos
  norm_num at hpos
