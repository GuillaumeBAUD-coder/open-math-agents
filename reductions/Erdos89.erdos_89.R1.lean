import FormalConjectures.ErdosProblems.«89»

-- Redução do problema de Erdős nº 89.
-- Crédito pela submissão: @deyvidantonio

open Filter EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1

/-- Para cada número de pontos, há uma configuração que atinge o mínimo e cujas
coordenadas são inteiros algébricos reais. Parta de uma configuração que atinja
o mínimo e introduza duas variáveis por ponto. Exija que as distâncias ao
quadrado entre pontos distintos sejam positivas e que cada igualdade entre
distâncias ao quadrado da configuração original continue válida. Esse sistema
finito de condições polinomiais com coeficientes inteiros tem uma solução real.
Pelo princípio de transferência para corpos reais fechados, ele admite uma
solução em números algébricos reais. Ela preserva o número de pontos e tem no
máximo o número original de distâncias. Uma dilatação por um inteiro positivo
comum torna todas as coordenadas inteiras algébricas e preserva a contagem de
distâncias. A desigualdade inversa decorre da inclusão no plano real. -/
def H1 : Prop :=
  minimalDistinctDistances {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)} =
    minimalDistinctDistances ℝ²

/-- Cota inferior para configurações cujas coordenadas são inteiros algébricos
reais. A constante deve ser uniforme sobre todos os corpos numéricos envolvidos.

Um caso particular é um conjunto A que ocupa uma fração fixa δ de uma grade
inteira de lado L. Tome um inteiro K > 4/δ e ponha M = ⌊L/K⌋. Para cada
distância d da grade de lado M, escolha um vetor v de comprimento d cujas
coordenadas estejam entre 0 e M-1. Os K+1 conjuntos A+jv, para 0 ≤ j ≤ K,
cabem numa grade de lado 2L. A soma das cardinalidades excede 4L², logo dois
deles se intersectam. Assim, kd ocorre como distância em A para algum inteiro
1 ≤ k ≤ K. Cada distância de A pode corresponder a no máximo K valores de d.
A contagem de distâncias da grade pelo teorema de Landau–Ramanujan dá a ordem
pretendida para A, com constante dependente de δ.

Outro caso admite uma cota linear. Seja Λ um reticulado plano de posto dois
cuja matriz de Gram não seja proporcional a uma matriz racional. Se algum
comprimento for realizado por vetores u e v com u ≠ ±v, então u+v e u−v
formam uma base ortogonal do espaço racional gerado por Λ. A razão dos seus
quadrados de comprimento é irracional, pois uma mudança racional de base
preserva a propriedade de a matriz de Gram ser proporcional a uma racional.
Escrevendo os vetores nessa base, a igualdade dos comprimentos força a igualdade
dos quadrados de ambas as coordenadas racionais. Há, portanto, no máximo quatro
vetores de cada comprimento. Se o par u,v não existir, há no máximo dois.
Em qualquer conjunto com n ≥ 2 pontos de uma translação de Λ, escolha o ponto
que minimiza um funcional linear com valores distintos nesses pontos. Os vetores
desse ponto para os demais estão num semiplano aberto. Ele contém no máximo
dois vetores de cada comprimento, pela simetria de sinal. Assim, pelo menos
⌈(n−1)/2⌉ distâncias distintas partem de um único ponto.

No conjunto todo, a cota melhora para n−1. No caso em que cada comprimento
só ocorre com os sinais opostos de um vetor, o ponto extremo já vê n−1.
No outro caso, use as coordenadas na base ortogonal acima. Para cada altura y,
seja X_y o conjunto das abscissas. Para cada diferença vertical absoluta d,
incluindo zero, seja F_d o conjunto das diferenças horizontais absolutas que
ocorrem com d. Ponha Y_k = {y : |X_y| ≥ k}. Cada diferença vertical d entre
duas alturas de Y_k satisfaz |F_d| ≥ k. De fato, as duas linhas têm pelo menos
k abscissas cada. Ordenando-as, obtemos pelo menos 2k−1 diferenças com sinal
e, portanto, pelo menos k valores absolutos. Se Y_k for não vazio, há ao menos
|Y_k| diferenças verticais absolutas, tomando como referência sua menor altura.
Somando em k, obtemos ∑_d |F_d| ≥ ∑_k |Y_k| = n. A razão irracional assegura
que cada par de diferenças absolutas determina um comprimento diferente.
Excluindo o zero, restam pelo menos n−1 distâncias. Uma progressão aritmética
colinear mostra que essa cota é ótima. -/
def H2 : Prop :=
  (fun n : ℕ => n / (n : ℝ).log.sqrt) =O[atTop]
    (fun n => (minimalDistinctDistances
      {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)} n : ℝ))

theorem main : H1 → H2 → type_of% @Erdos89.erdos_89 := by
  intro hMinimo hCota
  unfold H1 at hMinimo
  unfold H2 at hCota
  rw [hMinimo] at hCota
  exact hCota

end OMA.R_Erdos89_erdos_89_R1
