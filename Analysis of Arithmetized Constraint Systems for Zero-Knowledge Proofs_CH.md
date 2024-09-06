# Analysis of Arithmetized Constraint Systems for Zero-Knowledge Proofs
## 1. Introduction
近年来，零知识证明（ZKP）技术在密码学和区块链领域取得了前所未有的进展，并成为构建安全、隐私保护和可扩展应用的强大工具。ZKP允许证明者向验证者证明某个陈述的真实性，而无需透露任何关于陈述本身的信息。这一特性使其在各种领域展现出巨大的应用潜力，例如隐私保护交易、可验证计算、安全多方计算以及区块链的可扩展性。
为了实现高效的ZKP，将复杂的计算问题转化成可验证的数学问题至关重要。而约束系统正是解决这一问题的关键，它们提供了一种结构化的框架来描述计算问题，并将其转化为可验证的数学形式。
R1CS (Rank-1 Constraint System)、AIR (Algebraic Intermediate Representation)和 Plonkish 是当前三种重要的约束系统，它们在构 ZKP系统中起着关键作用，并推动了ZKP技术的快速发展。
此外，In<a href="#ref1">[1]</a>，a new constraint system called customizable constraint system (CCS) is introduced. It is a generalization of R1CS that can simultaneously capture R1CS, Plonkish, and AIR without overheads. 
本文旨在为读者提供对R1CS、AIR、Plonkish和CCS在ZKP系统中的原理和发展现状的全面了解。 我们希望能够帮助读者更好地理解ZKP约束系统的工作原理，并为他们选择合适的约束系统来构建安全高效的ZKP应用提供参考。
## 2. R1CS
### 2.1 R1CS与QAP
R1CS是一个一阶约束系统，其本质是一个方程组。在分析R1CS之前要先了解QAP(Qua­dratic Arith­metic Peoblem),QAP 转换不仅可以将函数的代码转换为 QAP，还可以在转换的同时构建一个对应于代码输入的解（又称为 QAP 的 Wit­ness），之后再基于这个wit­ness构建一个实际的零知识证明系统.下面的介绍参考了<a href="#ref2">[2]</a>。
比如，Prover希望向Ver­i­fier证明其知道方程$x^3+x+5=35$的解（P知道$x=3$为方程的解，因此wit­ness为$x=3$），接下来看一下如何进行QAP转换.
第一步我们需要定义一些中间变量：
$$sym_1=x*x$$
$$sym_2=sym_1*x$$
$$sym_3=sym_2+x$$
因此，上面方程的左边可以写为：
$$out=sym_3+5=sym_2+x+5=sym_1*x+x+5=x*x*x+x+5$$
可以看到，中间结果的每一行和和方程左边结果都可以描述为一个数学电路中的逻辑门，这些门仅有加法门和乘法门。

第二步需要将上面的结果转化为R1CS，一个R1CS是由三个向量构成的向量组$(\vec{a},\vec{b},\vec{c})$，假设R1CS的解也是一个向量，记为$\vec{s}$，则$\vec{s}$满足
$$(\vec{s}\cdot\vec{a})*(\vec{s}\cdot\vec{b})-(\vec{s}\cdot\vec{c})=0$$
其中⋅表示向量内积，∗表示算数乘法.

举个例子，假设向量组和解向量分别如下:
$$\vec{a}=[0,1,0,0,0,0]$$
$$\vec{b}=[0,1,0,0,0,0]$$
$$\vec{c}=[0,0,0,1,0,0]$$
$$\vec{s}=[1,3,35,9,27,30]$$
可以验证$(\vec{s}\cdot\vec{a})*(\vec{s}\cdot\vec{b})-(\vec{s}\cdot\vec{c})=0$等式成立，证明$\vec{s}$满足这个R1CS。

这个例子中只有一个约束条件，下面我们将方程$x^3+x+5=35$的每个逻辑门都转化为一个约束。在这里看一下出现的变量有：$x,sym_1,sym_2,sym_3,out$,我们把他们重新排列，并在前面加一个冗余变量1,形成一个新的向量$\vec{s'}=[one,x,out,sym_1,sym_2,sym_3]$.

接下来看第一个逻辑门$sym_1=x∗x$，其等价于$x∗x−sym_1=0$，因此,按照$\vec{s'}$的排列顺序不难得出 R1CS 向量组如下:
$$\vec{a_1}=[0,1,0,0,0,0]$$
$$\vec{b_1}=[0,1,0,0,0,0]$$
$$\vec{c_1}=[0,0,0,1,0,0]$$

第二个逻辑门$sym_2=sym_1∗x$，其等价于
$sym_1∗x−sym_2=0$，得到第二个R1CS向量组:
$$\vec{a_2}=[0,0,0,1,0,0]$$
$$\vec{b_2}=[0,1,0,0,0,0]$$
$$\vec{c_2}=[0,0,0,0,1,0]$$

第三个逻辑门$sym_3=sym_2+x$，其等价于
$(sym_2+x)*1−sym_3=0$，得到第三个R1CS向量组:
$$\vec{a_3}=[0,1,0,0,1,0]$$
$$\vec{b_3}=[1,0,0,0,0,0]$$
$$\vec{c_3}=[0,0,0,0,0,1]$$

最后是第四个逻辑门$out=sym_3+5$ 其等价于$(sym_3+5)∗1−out=0$，得到第四个 R1CS 向量组
$$\vec{a_4}=[5,0,0,0,0,1]$$
$$\vec{b_4}=[1,0,0,0,0,0]$$
$$\vec{c_4}=[0,0,1,0,0,0]$$

此时,wit­ness为$x=3$，带入$\vec{s'}$得到$\vec{s'}=[1,3,35,9,27,30]$.因此，经过R1CS转换后wit­ness转换为使得这四个R1CS同时成立的解向量
$$\vec{s}=\vec{s'}=[1,3,35,9,27,30]$$

将上述结果整理一下，把每个 R1CS 中的三个向量分别整理成向量组:
$$A= \left[\begin{matrix}0&1&0&0&0&0\\0&0&0&1&0&0\\0&1&0&0&1&0\\5&0&0&0&0&1\end{matrix}\right]$$
$$B= \left[\begin{matrix}0&1&0&0&0&0\\0&1&0&0&0&0\\1&0&0&0&0&0\\1&0&0&0&0&0\end{matrix}\right]$$
$$C= \left[\begin{matrix}0&0&0&1&0&0\\0&0&0&0&1&0\\0&0&0&0&0&1\\0&0&1&0&0&0\end{matrix}\right]$$
对于向量组$A,B,C$的每一行，下式成立：
$$(\vec{s}\cdot A_i)*(\vec{s}\cdot B_i)-(\vec{s}\cdot C_i)=0$$


完成R1CS后，接下来就是将R1CS转换QAP形式，**QAP实现了与 R1CS完全相同的逻辑，只不过使用的是多项式而不是向量内积**，这样做的好处是提高验证效率。

多项式可以看成是空间中的曲线，因此点在曲线上就是满足约束。那么问题就转换为如何找到一条曲线，满足和R1CS等价的约束。

首先，将向量组$A,B,C$的每一列转变为多项式曲线上的纵坐标点，横坐标为行索引。例如，向量组$A$的第一列转换为坐标点：$(1,0),(2,0),(3,0),(4,5)$。

然后找到过这些点的曲线，可以使用拉格朗日插值。例如，经过向量组$A$的第一列坐标点的曲线插值结果为：
$$A_1(x)=-5+9.166x-5x^2+0.833x^3$$
不难验证，将$x=1,2,3,4$分别带入上述多项式，可以恢复向量组 $A$的第一个列向量。

同理，可以求出其余向量组对应的插值系数。

### 2.2 Check QAP
从R1CS转化为QAP后，此时可以通过多项式的内积运算来同时检查所有的约束而不是像 R1CS 那样单独的检查每一个约束.

例如在前面的例子中Prover要证明自己知道方程解，那么就需要证明向量组$A,B,C$中的每个行向量与解向量$\vec{s}$的内积之后的值是符合R1CS约束:

$$(\vec{s}\cdot A_i)*(\vec{s}\cdot B_i)-(\vec{s}\cdot C_i)=0$$

在大规模电路下，存在成千上万个电路门，R1CS验证效率会十分低下，于是通过QAP把向量的内积计算转化为多项式的形式，多项式具有良好的性质，可以通过一次计算来验证所有约束的正确性。

用多项式去表示R1CS约束：

$$(\vec{s}* \left[\begin{matrix}A_1(x)\\A_2(x)\\A_3(x)\\A_4(x)\end{matrix}\right])*(\vec{s}* \left[\begin{matrix}B_1(x)\\B_2(x)\\B_3(x)\\B_4(x)\end{matrix}\right])-\vec{s}* \left[\begin{matrix}C_1(x)\\C_2(x)\\C_3(x)\\C_4(x)\end{matrix}\right]=0$$

令上式左边等于$p(x)$，当$x=1$时，即验证第一个门电路$p(1)=0$.当$x=2$时，即验证第二个门电路$p(2)=0$. 当$x=3$时，即验证第三个门电路$p(3)=0$.当$x=4$时，即验证第四个门电路$p(4)=0$

根据多项式的因式分解：一个多项式只要它有解，就可以将它分解成线性多项式. 所以$p(x)$可以表示成：
$$p(x)=t(x)*h(x)$$
其中，$t(x)=(x-1)(x-2)(x-3)(x-4)$。因此，$t(x)$可以整除$p(x)$.这一点告诉我们如何快速验证答案是否正确。

## 3. AIR

### 3.1 AIR的定义

AIR是ZK-STARK中使用的算术化方案。它将问题通过矩阵的形式进行表达。其矩阵的第一行称为输入，最后一行为输出，矩阵中间为代数计算过程中的中间参数。中间计算状态实际上是一堆寄存器数值。因此，AIR产生的是一个低度多项式的集合：

$$P=\{P_1(\vec{X},\vec{Y}),...,P_s(\vec{X},\vec{Y})\}$$

多项式满足以下条件：

(1)低度多项式的系数在域$F$内;

(2)$\vec{X}=(X_1,...,X_w)$代表当前计算状态；

(3)$\vec{Y}=(Y_1,...,Y_w)$代表下一步计算状态；

(4)$w$是证明系统所中某一个计算状态的变量数量;

(5)$P_i$代表转换关系的多项式;

(6)有一对解$(\vec{x},\vec{y})$使得转换关系成立，即只有$(\vec{x},\vec{y})$是$P$的共同的解，$P_1(\vec{x},\vec{y})=P_2(\vec{x},\vec{y})=...=P_s(\vec{x},\vec{y})=0$；

(7)AIR的多项式的度是所有$P_i$中的最大值;

(8)$s$是所有约束的数量.

AIR实际上是用$s$个多项式描述当前执行状态与下一步状态的转化约束。

### 3.2 Execution trace
通过定义可以看出，AIR将程序执行过程中寄存器数值前后变化关系转化成了约束多项式，以便验证者能信任输入x到输出y的完整过程，而不是随便得出的结果或者是伪造的输出结果。这个程序执行过程就称为Execution trace。

执行轨迹是由执行某个计算时，一组机器状态序列构成。也就是说为了执行某个程序，申请了W个寄存器（宽度），执行了N个步骤（长度），那么执行轨迹可以用一张大小为N×W的表来描述。

以斐波那契数列为例，假设我们需要在域$Z_{96769}$上计算斐波那契数列的前512项，根据域上加法和乘法需要模96769，我们有下定义：
$$a_0=1$$
$$a_1=1$$
$$a_{n+2}=(a_{n+1}+a_{n}) mod (96769)$$

根据定义可以列出斐波那契数列的值：
<table border="2" align="center">
	<tr>
		<th align="center" width="20%">a0</th>
		<th align="center" width="20%">a1</th>
        <th align="center" width="20%">a2</th>
        <th align="center" width="20%">a3</th>
        <th align="center" width="20%">a4</th>
        <th align="center" width="20%">...</th>
        <th align="center" width="20%">a509</th>
        <th align="center" width="20%">a510</th>
        <th align="center" width="20%">a511</th>
        </th>
	</tr>
		<tr>
		<th align="center" width="20%">1</th>
		<th align="center" width="20%">1</th>
        <th align="center" width="20%">2</th>
        <th align="center" width="20%">3</th>
        <th align="center" width="20%">5</th>
        <th align="center" width="20%">...</th>
        <th align="center" width="20%">66169</th>
        <th align="center" width="20%">92815</th>
        <th align="center" width="20%">62215</th>
        </th>

</table>

斐波那契数列运算只使用了两个寄存器$s_0$和$s_1$，存放每一个中间状态下的数据，生成的执行轨迹为：
<table border="2" align="center">
	<tr>
		<th align="center" width="20%">s0</th>
		<th align="center" width="20%">s1</th>
        </th>
	</tr>
		<tr>
		<th align="center" width="20%">1</th>
		<th align="center" width="20%">1</th>
        </th>
        <tr>
		<th align="center" width="20%">2</th>
		<th align="center" width="20%">3</th>
        </th>
        <tr>
		<th align="center" width="20%">5</th>
		<th align="center" width="20%">8</th>
        </th>
        <tr>
		<th align="center" width="20%">...</th>
		<th align="center" width="20%">...</th>
        </th>
        <tr>
		<th align="center" width="20%">26646</th>
		<th align="center" width="20%">66169</th>
        </th>
        <tr>
		<th align="center" width="20%">92815</th>
		<th align="center" width="20%">62215</th>
        </th>

</table>

根据斐波那契数列的特性，我们可以得到下列四个约束:

(1)$a_0-1=0$,输入约束；

(2)$a_1-1=0$,输入约束；

(3)$\forall 0\leq i\leq 509:a_{i+2}-a_{i+1}-a_{i}=0$,确保执行轨迹满足斐波那契递归关系;

(4)$a_{511}-62215=0$,输出约束。

### 3.3 Poly­no­mial Con­straints
AIR除了生成执行轨迹，还要将约束转化为多项式约束，然后将这两个生成对象转化为一个低度多项式，因此Prover和Ver­i­fier之间的验证就转化为了Prover和Ver­i­fier在某个被约束的多项式上达成一致，在之后的交互过程中由Prover来说服Ver­i­fier在该执行轨迹上满足多项式约束。

生成多项式约束需要用到前面的拉格朗日插值法，得到

$$\forall 0\leq i\leq 511:f(g^i)=a_i$$

其中，$g$为子群的生成元，然后得到对应的多项式约束:

(1)$f(1)-1=0$,确保第一个元素为1；

(2)$f(g)-1=0$,确保第二个元素为1；

(3)$\forall 0\leq i\leq 509:f(g^{i+2})-f(g^{i+1})-f(g^{i})=0$,确保执行轨迹满足斐波那契递归关系;

(4)$f(g^{511})-62215=0$,输出约束。

构造多项式约束使得：当且仅当执行迹有效（即迹表示一个有效计算）时，所有约束都能得到验证。这些约束是低次多项式，但不一定限于（比如R1CS情况下的）2次多项式。

## 4. Plonkish

Plonkish泛指具有custom gates、RAP（randomized AIR with preprocessing），或TurboPLONK/UltraPLONK的约束系统。它同样用矩阵的形式进行定义，但在矩阵生成形式上AIR有所不同。下面以PAIR(Preprocessed AIR)和RAP进行介绍（TurboPlonk和UltraPlonk是RAP的受限情况）。

### 4.1 PAIR
在一个PAIR的执行轨迹中, 添加了一个额外的参数t, 并且t预定义了一列数据$c_1,…,c_t∈F^n$。除了证明者提供的$w$列外，一个执行轨迹现在还包括 {ci} 。( 我们将证明者提供的列称为执行轨迹的见证部分。)

当$t=1,w=2,n=5$时，我们有以下执行轨迹：
<table border="2" align="center">
	<tr>
		<th align="center" width="20%">c0</th>
		<th align="center" width="20%">a0</th>
        <th align="center" width="20%">b0</th>
        </th>
	</tr>
    <tr>
		<th align="center" width="20%">c1</th>
		<th align="center" width="20%">a1</th>
        <th align="center" width="20%">b1</th>
        </th>
	</tr>
    <tr>
		<th align="center" width="20%">c2</th>
		<th align="center" width="20%">a2</th>
        <th align="center" width="20%">b2</th>
        </th>
	</tr>
    <tr>
		<th align="center" width="20%">c3</th>
		<th align="center" width="20%">a3</th>
        <th align="center" width="20%">b3</th>
        </th>
	</tr>
    <tr>
		<th align="center" width="20%">c4</th>
		<th align="center" width="20%">a4</th>
        <th align="center" width="20%">b4</th>
        </th>
	</tr>
</table>

在这个执行轨迹中，我们不仅希望执行的行值相加（类似与AIR的斐波那契数列）运算，还需要执行一些行值相乘运算。因此，将列$c_0,...,c_4$定义为参与约束的一个因子，当想要执行行相加时值为1，当想要执行行相乘时值为0。约束变为：

$$\forall 1\leq i\leq 4:c_i\cdot(a_i-(a_{i-1}+b_{i-1}))+(1-c_i)\cdot(a_i\cdot (a_{i-1}+b_{i-1}))=0$$

这种预定义的列的方式实现了运算选择，所以它们通常被称为selecors。

### 4.2 RAP
ZKP模型允许多轮交互，其中验证者发送域中随机元素，而证明者接收到这些域元素后可以在执行轨迹中添加更多列，因此，约束多项式可以使用验证者随机性作为附加变量，这就是RAP。

假设有一个$w=2$的AIR执行轨迹，这些列的值为$a_0,...a_{n-1}$和$b_0,...,b_{n-1}$.

From the Schwartz-Zippel Lemma we know that to check they are a permutation of each other it suffices to check that for a uniformly chosen $\gamma∈𝐹$, we have with high probability

$$\prod _{i\in [n]}(a_i+\gamma)=\prod _{i\in [n]}(b_i+\gamma)$$

With high probability over $\gamma$, the factors of the RHS are all non-zero and in that case this is equivalent to

$$\prod _{i\in [n]}(a_i+\gamma)/(b_i+\gamma)=1$$

A RAP of length $𝑛+1$ and total width 3 can easily check this:

* The prover first sends the columns$a_0,...a_{n-1},0$和$b_0,...,b_{n-1},0$.
* The verifier sends random $\gamma \in F$
* The prover send a third column (1,z_1,…,z_{n-1}) such that for each $i \in[n]$
 $$z_i=\prod _{0\leq j \leq i-1}(a_j+\gamma)/(b_j+\gamma)$$

这种随机性使局部约束（相邻行之间）能够验证全局属性（the columns being a permutation of each other）。
### 4.3 Plonkish
Plonkis本质上也是一种PAIR或RAP，同样使用表格设计并记录运算，可以自定义使用多少列以及列的类型，列数越多成本越高。有三种不同的列：
* Advice：隐私值(证明者计算过程整参数)
* Fixed：公开常量(固定值)
* Selector：选择器，用于决定是否在该行启用某种约束；
* Instance：公开输入/输出

此外，还要约束单元格之间关系，又增加了
* 自定义门约束(Custom Gate)：使用等于零的多项式来描述单元格关系；
* 查找表约束(Lookup args) ：单元格值为已知值Lookup列表中的一项；
* 固定值约束(Constance)：单元格值为固定值(常量)。

## 5. CCS
CCS实际上是R1CS的一种扩展，同时参考了、AIR和Plonkish的算术化方案，而且并不会产生额外计算开销。
### 5.1 Definition
A CCS structure consists of:

* size bounds $m, n, N, l, t, q, d$ where $n<l$;
* a sequence of matrices $M_0,...,M_{t−1}\in F^{
m×n}$  with at most $N$ non-zero entries in total;
* a sequence of $q$ multisets $[S_0,..., S_{q−1}]$, where an element in each multiset is from the domain $\{0,....,t-1 \}$ and the cardinality of each multiset is at most $d$.
* a sequence of $q$ constants $[c_0,... ,c_{q−1}]$, where each constant is from $F$.

A CCS instance consists of public input $x \in F$. A CCS witness consists of a vector $w \in F^{n-l-1}$. A CCS structure-instance tuple $(S, x)$ is satisfied by a CCS witness $w$ if
$$\sum _{i=0}^{q-1}c_i\cdot \{\bigcirc _{j\in S_i}M_j\cdot z\}=\mathbf{0}$$
where $z=(w,1,x)\in F^n$, $M_j\cdot z$ denotes matrix-vector multiplication, $\bigcirc$ denotes the Hadamard product between vectors, and $\mathbf{0}$  is an $m$-sized vector with entries equal to the the additive identity in $F$.

### 5.2 Representing R1CS with CCS

我们首先列举一下R1CS约束系统$(A \cdot z)*(B\cdot z)-(C\cdot z)=\mathbf{0}$包含的参数，主要有：
* $A,B,C$: 约束矩阵；
* $z$: 包括witness $w$的构造向量；
* $\mathbf{0}$:为$m$-sized零向量；
* $l$:public input个数；
* $m$:矩阵的行数；
* $n$:矩阵的列数.

令$M_0=A$, $M_1=B$, $M_2=C$,R1CS约束系统可以变为：
$$(M_0\cdot z)*(M_1\cdot z)-(M_2\cdot z)=1\cdot( M_0\cdot z)*(M_1\cdot z)+(-1)\cdot(M_2\cdot z)=\mathbf{0}$$
令$c_0=1,c_1=-1$,$S_0= \{0,1\}$, $S_1= \{2\}$,重写上式：
$$c_0\cdot( M_0\cdot z)*(M_1\cdot z)+c_1\cdot(M_2\cdot z)\\
=c_0\cdot \{\bigcirc* _{j\in S_0}M_j\cdot z\}+c_1\cdot \{\bigcirc* _{j\in S_1}M_j\cdot z\}\\
=\sum _{i=0}^{2-1}c_i\cdot \{\bigcirc _{j\in S_i}M_j\cdot z\}=\mathbf{0}$$
这样R1CS就转换为CCS约束。这里除了R1CS的参数，还增加了：
$t=3$, $q=2$, $d=2$, $S_0= \{0,1\}$, $S_1= \{2\}$, and the sequence of $q$ constants  $\{c_0,c_1\}$
## 6 Conclusions
The newly emerged CCS constraint system, in essence, serves as a unified representation encompassing R1CS, AIR, and PlonkishR. It necessitates at least three matrices to define a circuit and leverages multisets for tailored constraint specification. Programming both matrices and multisets enables CCS to express arbitrary polynomial constraints. CCS marks a significant milestone in the evolution of constraint systems.

## References：

<p name = "ref1">[1]Srinath Setty, Justin Thaler, and Riad Wahby. Customizable constraint systems for succinct arguments.Cryptology {ePrint} Archive, Paper 2023/552. https://eprint.iacr.org/2023/552.

<p name = "ref2">[2]https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649