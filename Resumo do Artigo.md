# Resumo #

Dupla:
- João Victor de Souza Albuquerque
- Tiago Vargas Pereira de Oliveira


# Modelando Horários de Funcionários como um _Partial Weighted maxSAT_ #

## 1 - Introdução ##

## 2 - Descrição do Probema ##

Problema: é dificil de encontrar um horario de serviço pra todos os funcionários.

Discussao: como encontrar um horario que satisfaça as preferencias de turno dos funcionários

**hard constraints:** sao as condições que não podem ser violadas (ex. carga horaria maxima e minima semanal)

**soft constraints:** sao as condições que podem ser violadas, se necessario (ex. preferencias de horario/turno dos funcionários)


## 3 - Modelando o Problema Usando maxSAT Parcialmente __Pesado__ ##

<!-- ### The maximum satisfiability problem ### -->

SAT: um problema de satisfatibilidade (resolvido com logica proposicional)

Partial Weighted maxSAT: uma expansao do SAT, que usa clausulas rígidas e flexiveis.

Clasusula rígida: uma clausula que não pode ser violada

Clasusula flexivel: uma clausula que recebe um peso

O objetivo é satisfazer as clasusulas rígidas, minimizando as violações das flexiveis (i.e., minimizando a soma dos pesos das violadas).

A formulas do maxSAT que modelam o problema sao chamadas de codificações.


### Variáveis de Decisão ###

$I$ é o conjunto de todos os funcionários.

$D$ é o conjunto dos dias da semana.

$T$ é o conjunto dos turnos.

$S_{i,d,t}$ é `True` se e somente se o funcionário $i$ está no turno $t$ no dia $d$ (mais precisamente, no $d$-ésimo dia).


$X_{i,d}$ é `True` se e somente se o funcionário $i$ está de folga no dia $d$.

As variáveis $X$ e $S$ estão relacionadas de acordo com a fórmula a seguir:


$\forall{i} \in I, d \in D: X_{i,d} \leftrightarrow \bigwedge_{t \in T}{\lnot S_{i,d,t}}$

> "O funcionário está de folga no dia $d$, _sse_ ele não tiver turno no dia $d$."


### Restrições de Cardinalidade ###

**Restrição de cardinaliade:** Essas restrições definem limites no quantidade de variáveis com o valor verdade definido (i.e. limitam a quantidade de variáveis não livres).

São três tipos:

- $atLeast_k(x_i: x_i \in X)$
	- No mínimo $k$ variáveis setadas (i.e. com valor-verdade definido).
- $exactly_k(x_i : x_i \in X)$
	- Exatamente $k$ variáveis setadas.
- $atMostk (x_i : x_i \in X)$
	- No máximo $k$ variáveis setadas.

> For example if a cardinality constraint limits the number of true valued variables of the set $x_1$, $x_2$, $x_3$ to at most two $atMost_2({x_1, x_2, x_3})$, the assignment $(x_1 , x_2 , x_3) = (1, 1, 0)$
is considered to be feasible, while the assignment $(x_1 , x_2 , x_3) = (1, 1, 1)$ would be considered
as infeasible.

Por exemplo, se uma restrição de cardinalidade limita a quantidade de variáveis que são setadas para `True`, i.e. $atMost_2({x_1, x_2, x_3})$, então $(x_1 , x_2 , x_3) = (1, 1, 0)$ é viável, e $(x_1 , x_2 , x_3) = (1, 1, 1)$ não é viável.

Restrições de cardinalidade rígidas decidem se uma solução é viável ou não.

Restrições de cardinalidade flexíveis penalizam a função objetivo se forem violadas.

Por exemplo, para a restrição $atLeast_2({x_1, x_2, x_3})$ com um peso de $40$, $(x_1 , x_2 , x_3) = (0, 0, 0)$ dá uma penalidade de $40 \times 2 = 80$.


#### 3.3.1 ####
#### 3.3.2 ####
#### 3.3.3 ####


### Modelagem de Retrições Rígidas ###

Essa parte trata de como modelar restrições rígidas usando as variáveis definidas.

> Um funcionário não pode trabalhar mais do que um turno por dia.

- $\forall{i} \in I, d \in D: atMost_1(\set{S_{i,d,1}, S_{i,d,2}, ..., S_{i,d,|T|}})$

	"O funcionário só pode trabalhar um turno num dia."

> _Sequências de turno proibidas:_ É necessário que um funcionário descanse por um tempo depois de trabalhar por um turno.

$\forall{t \in T}, x \in R_t: \bigwedge_{d=1}^{|D|-1}(S_{i,d,t} \rightarrow \lnot S_{i,d+1,x})$

$R_t$ é o conjunto de turnos que não podem suceder o turno $t$.

E.g., se o funcionário trabalha segunda de noite, então ele não pode trabalhar terça de dia (senão trabalha um dia inteiro!).

> _Número máximo de turnos que podem ser atribuidos a um funcionário:_ Alguns funcionários podem ter contratos que permitam eles trabalharem em turnos específicos por um período máximo de dias.

$\forall{i \in I}, t \in T: atMost_{m_{i,t}^{max}} (\set{S_{i,1,t}, S_{i,2,t}, ..., S_{i,|D|,t}})$

onde $m_{i,t}^{max}$ é a quantidade máxima de turnos $t$ que o funcionário $i$ pode ter.

> _Tempo de trabalho máximo e mínimo_ Cada turno atribui uma carga horária aos funcionários associados a ele.

São representados como $b_i^{min}$ e $b_i^{max}$.

> _Número máximo de turnos [em dias] consecutivos_ Um funcionário deve trabalhar por tantos dias de trabalho consecutivos antes de tirar uma folga.

$\forall{i \in I}, d \in \set{1, ..., |D| − c_i^{max}}: \bigvee_{x=0}^{c_i^{max}} X_{i,d+x}$


### Modelagem de Restrições Flexíveis ###

> Alguns funcionários podem preferir trabalhar num turno específico num dia específico.

Como isso não é uma restrição rígida, sua violação vai ser penalizada com um peso. As penalidades dão dadas como os parâmetros $q_{i,d,t}$, com $i \in I$, $t \in T$ e $d \in D$. A restrição é formulada como:

$S_{i,d,t} · q_{i,d,t} \forall{(i,d,t)} where \exists{q_{i,d,t}}$

> Funcionários podem não querer trabalharem em certos turnos em certos dias.

A formulação é baseada nos parâmetros $p_{i,d,t}$ que definem o peso de um turno não preferido:

$\lnot S_{i,d,t} · p_{i,d,t} \forall{(i, d, t)} where \exists{p_{i,d,t}}$

> Os chefes podem preferir tantos funcionários trabalhando num turno num dia específico.

Esse valor preferido é dado como $U_{i,d,t}$. Além disso, pra cada um desses valores, duas penalidades ($v_{d,t}^{min}$ e $v_{d,t}^{max}$) são usadas para penalizar excesso ou escassez de funcionários.

$\forall{d \in D}, t \in T: atMost_{u_{d,t}}(\set{S_{1,d,t}, S_{2,d,t}, ..., S_{|I|,d,t}}) \cdot v_{d,t}^{max}$

$\forall{d \in D}, t \in T: atLeast_{u_{d,t}}(\set{S_{1,d,t}, S_{2,d,t}, ..., S_{|I|,d,t}}) \cdot v_{d,t}^{min}$


### 3.6 - Using maxSAT to Model Nurse Rostering ###


## 4 - Resultados Computacionais ##

### 4.1 - Ambiente Experimental ###

Foram conduzidos uma grande quantidade de experimentos com codificações maxSAT, nas quais os horários planejados poderiam variar de 2 a 52 semanas, e a quantidade de funcionários, de 8 a 150.

Eles usaram dois _solvers_, que obtiveram resultados num tempo muito bom.


### 4.2 - Comparison of different cardinality constraint encodings ###

> We selected the best candidates for
each solver by considering the sums of the results over all instances for each combination
of cardinality encodings. The encodings which led to the minimum of all those sums were
then taken to generate the instances for our final experiments. Therefore, the combinations of
cardinality constraint encodings used for Optiriss were as follows: bit adder encoding for the
cover requirements constraint, cardinality networks for theworkload requirements constraint,
and the sequential encoding for the maximum number of shifts constraint. The combinations

of cardinality constraint encodings for WPM3 on the other hand were: The sequential encod-
ing for the cover requirements constraint as well as the workload requirements constraint, and

the encoding which uses cardinality networks for the maximum number of shifts constraint.

### 4.3-Final experiments and comparison of solvers ###

> Comparing our approach with another existing exact method based on integer program-
ming, which was provided by Curtois and Qu (2014) (last two columns in the table) we can conclude that both maxSAT solvers could not find new unknown optimal results. However
they could provide optimal solutions for instances 1 and 2. Running the maxSAT solvers for
4 h resulted in finding solutions for two of the instances which could not be solved by the
integer programming approach within 1 h on a different environment.

### 4.4- Analyzing the influence of the under-coverage soft-constraint ###

não sei se essa parte é muito util.

## 5-Conclusion ##

> Our results showed that there is a need to experimentally select an
efficient combination of cardinality encodings for each solver separately, as the best encoding
strategy in our experiments varied depending on the used solver. A comparison between the
two solvers could not point out a clear winner for all of the considered benchmark tests. While
WPM3 performed better on smaller instances, Optiriss was able to produce better results for
many of the larger instances.
Currently an exact approach based on integer programming provides better results than
maxSAT for most of the considered instances. However, maxSAT could provide optimal
solutions for two of the instances and obtained solutions for two very large instances within
4 h, which could not be solved by integer programming within 1 h.
We think that the main reason why the results currently cannot compete with
integer programming lies in the intensive use of cardinality constraints that are required to
model the problem. The high significance of choosing good encoding strategies for cardinality
constraints that became apparent during our experiments as well as the discovered influence
of the under-coverage constraint indicate the importance of efficient strategies to deal with
these types of constraints. We therefore conclude that there is a need for improving the
performance of maxSAT solvers, especially regarding cardinality constraints.
# Perguntas #

## O que já existia antes do artigo em questão? ##

## Qual(is) problema(s) o artigo se propõe a resolver? ##

## Qual(is) método(s) (definições, rotina, algoritmo, protocolo, ferramenta, modelagem) foram desenvolvidos e/ou usados? ##

> In this paper we
investigate four different encoding types: combinatorial encoding, sequential encoding, bit
adder encoding, and cardinality networks.


## O que foi apontado como novidade com relação ao que já existia? Por exemplo, qual a novidade do novo algoritmo definido no artigo? ##

> – We provide the first maxSAT formulation for the variant of the employee scheduling
problem introduced by Curtois and Qu (2014). Furthermore, we show how the proposed
maxSAT formulation can be adapted to model another well known variant from nurse
rostering.

> – We experiment with different encodings for cardinality constraints and compare two
leading solvers from the maxSAT evaluation 2015. Additionally, we experiment with a
123Ann Oper Res (2019) 275:79–99
81
simplification of the problem and provide a comparison with the state of the art solu-
tions.

> – We provide challenging instances which can be used by the maxSAT community to test
and improve results of maxSAT solvers.



## Qual(is) resultado(s) foram obtidos? ##

## Que partes do conteúdo da disciplina foram utilizados no artigo? ##

Avaliar problemas de satisfatibilidade.

Fórmulas na CNF.

modelando problemas do dia a dia com logica proprosicional
