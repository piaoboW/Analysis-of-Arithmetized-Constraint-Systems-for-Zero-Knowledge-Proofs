# Analysis of Arithmetized Constraint Systems for Zero-Knowledge Proofs
## 1. Introduction
In recent years, zero-knowledge proof (ZKP) technology has witnessed unprecedented advancements in cryptography and blockchain, emerging as a powerful tool for building secure, privacy-preserving, and scalable applications. ZKPs enable a prover to convince a verifier of the truthfulness of a statement without revealing any information about the statement itself. This unique characteristic unlocks immense potential across diverse fields, such as privacy-preserving transactions, verifiable computation, secure multi-party computation, and blockchain scalability.

To achieve efficient ZKPs, transforming complex computational problems into verifiable mathematical problems is crucial. Constraint systems are key to this transformation, providing a structured framework for describing computational problems and translating them into verifiable mathematical forms.

R1CS (Rank-1 Constraint System), AIR (Algebraic Intermediate Representation), and Plonkish are three prominent constraint systems currently playing a pivotal role in constructing ZKP systems, driving rapid advancements in ZKP technology.

Furthermore, <a href="#ref1">[1]</a> introduces a new constraint system called Customizable Constraint System (CCS). CCS is a generalization of R1CS capable of simultaneously capturing R1CS, Plonkish, and AIR without overhead.

This paper aims to provide readers with a comprehensive understanding of the principles and current state of R1CS, AIR, Plonkish, and CCS within the context of ZKP systems. Our goal is to assist readers in comprehending the workings of ZKP constraint systems and equip them with the knowledge necessary to select appropriate constraint systems for building secure and efficient ZKP applications.

## 2. R1CS
### 2.1 R1CS与QAP
R1CS (Rank-1 Constraint System) is a first-order constraint system that essentially represents a system of equations. Before delving into R1CS, understanding QAP (Quadratic Arithmetic Problem) is crucial. QAP conversion not only translates function code into QAP but also constructs a corresponding solution (known as a QAP Witness) representing the input to the code during the conversion process. This witness then forms the foundation for building a practical zero-knowledge proof system.The following explanation draws inspiration from <a href="#ref2">[2]</a>.

For instance, let's say Prover wants to demonstrate to Verifier that they know the solution to the equation $x^3 + x + 5 = 35$ (Prover knows that $x = 3$ is the solution, so the witness is $x = 3$). Let's examine how this can be done using QAP conversion.

Firstly, we need to define some intermediate variables:

$$sym_1=x*x$$

$$sym_2=sym_1*x$$

$$sym_3=sym_2+x$$

Therefore, the left-hand side of the equation can be rewritten as:

$$out=sym_3+5=sym_2+x+5=sym_1*x+x+5=x^3+x+5$$

It's evident that each row of intermediate results, along with the left-hand side of the equation, can be represented as a logical gate within a mathematical circuit. These gates exclusively consist of addition and multiplication operations.

The second step involves converting the aforementioned results into R1CS format. An R1CS is a vector set comprised of three vectors: $(\vec{a},\vec{b},\vec{c})$. Assuming the solution to R1CS is also a vector, denoted as $\vec{s}$, then $\vec{s}$ satisfies the following equation:

$$(\vec{s}\cdot\vec{a})*(\vec{s}\cdot\vec{b})-(\vec{s}\cdot\vec{c})=0$$

where $⋅$ represents the dot product of vectors and $*$ denotes arithmetic multiplication.

As an illustration, suppose the vector set and solution vector are as follows:

$$\vec{a}=[0,1,0,0,0,0]$$

$$\vec{b}=[0,1,0,0,0,0]$$

$$\vec{c}=[0,0,0,1,0,0]$$

$$\vec{s}=[1,3,35,9,27,30]$$

It can be verified that the equation $(\vec{s}\cdot\vec{a})*(\vec{s}\cdot\vec{b})-(\vec{s}\cdot\vec{c})=0$ holds true, thereby demonstrating that $\vec{s}$ satisfies this R1CS.

This example involves only one constraint. We'll now convert each logical gate in the equation $x^3 + x + 5 = 35$ into a constraint.

Let's examine the variables involved: $x, sym_1, sym_2, sym_3, out$. We'll rearrange them, prefixing a redundant variable "1", to form a new vector $\vec{s'} = [one, x, out, sym_1, sym_2, sym_3]$.

Consider the first logical gate: $sym_1 = x * x$. This is equivalent to $x * x - sym_1 = 0$. Based on the order of $\vec{s'}$, we can easily derive the R1CS vector set as follows:

$$\vec{a_1}=[0,1,0,0,0,0]$$

$$\vec{b_1}=[0,1,0,0,0,0]$$

$$\vec{c_1}=[0,0,0,1,0,0]$$

The second logic gate $sym_2=sym_1∗x$, which is equivalent to
$sym_1∗x−sym_2=0$, results in the second R1CS vector set:

$$\vec{a_2}=[0,0,0,1,0,0]$$

$$\vec{b_2}=[0,1,0,0,0,0]$$

$$\vec{c_2}=[0,0,0,0,1,0]$$

The third logic gate $sym_3=sym_2+x$, which is equivalent to
$(sym_2+x)*1−sym_3=0$, results in the third R1CS vector set:

$$\vec{a_3}=[0,1,0,0,1,0]$$

$$\vec{b_3}=[1,0,0,0,0,0]$$

$$\vec{c_3}=[0,0,0,0,0,1]$$

Finally, the fourth logic gate $out=sym_3+5$ which is equivalent to $(sym_3+5)*1-out=0$, results in the fourth R1CS vector set:

$$\vec{a_4}=[5,0,0,0,0,1]$$

$$\vec{b_4}=[1,0,0,0,0,0]$$

$$\vec{c_4}=[0,0,1,0,0,0]$$

At this point, the witness is $x=3$, substituting it into $\vec{s'}$ gives $\vec{s'}=[1,3,35,9,27,30]$. Therefore, after R1CS conversion, the witness is transformed into a solution vector that simultaneously satisfies these four R1CS.

$$\vec{s}=\vec{s'}=[1,3,35,9,27,30]$$

Let's organize the results above, grouping the four vectors in each R1CS into vector sets:

$$
A= \left[\begin{matrix}0&1&0&0&0&0\\
0&0&0&1&0&0\\
0&1&0&0&1&0\\
5&0&0&0&0&1\end{matrix}\right]
$$

$$
B= \left[\begin{matrix}0&1&0&0&0&0\\
0&1&0&0&0&0\\
1&0&0&0&0&0\\
1&0&0&0&0&0\end{matrix}\right]
$$

$$
C= \left[\begin{matrix}0&0&0&1&0&0\\
0&0&0&0&1&0\\
0&0&0&0&0&1\\
0&0&1&0&0&0\end{matrix}\right]
$$

For each row in the vector sets $A, B, C$, the following equation holds:

$$(\vec{s}\cdot A_i)*(\vec{s}\cdot B_i)-(\vec{s}\cdot C_i)=0$$

After R1CS, the next step is to convert it into QAP form. **QAP implements the exact same logic as R1CS, but using polynomials instead of vector inner products.** This approach has the benefit of improving verification efficiency.

Polynomials can be viewed as curves in space, and points on the curve satisfy the constraints. Therefore, the problem transforms into finding a curve that satisfies constraints equivalent to R1CS.

First, each column in the vector sets $A, B, C$ is transformed into the y-coordinate points on a polynomial curve, with the row index as the x-coordinate. For example, the first column of the vector set $A$ is converted to the coordinate points: $(1,0),(2,0),(3,0),(4,5)$.

Then, find the curve passing through these points using Lagrange interpolation. For example, the curve interpolation result passing through the first column coordinates of the vector set $A$ is:

$$A_1(x)=-5+9.166x-5x^2+0.833x^3$$

It is easy to verify that by substituting $x=1,2,3,4$ into the above polynomial, you can recover the first column vector of the vector set $A$.

Similarly, the interpolation coefficients corresponding to other vector sets can be obtained.

### 2.2 Check QAP
After converting from R1CS to QAP, all constraints can be checked simultaneously using polynomial inner product instead of checking each constraint individually as in R1CS.

For example, in the previous example, the Prover needs to prove that they know the solution to the equation, which means proving that the inner product of each row vector in the vector sets $A, B, C$ with the solution vector $\vec{s}$ satisfies the R1CS constraint:

$$(\vec{s}\cdot A_i)*(\vec{s}\cdot B_i)-(\vec{s}\cdot C_i)=0$$

In large-scale circuits with thousands or even millions of logic gates, R1CS verification efficiency would be very low. QAP transforms the vector inner product calculation into polynomial form, leveraging the good properties of polynomials, allowing verification of the correctness of all constraints with a single calculation.

Using polynomials to represent R1CS constraints:

$$
(\vec{s}*{\left[\begin{matrix}
A_1(x)\\
A_2(x)\\
A_3(x)\\
A_4(x)\end{matrix}\right])}*(\vec{s}*{\left[\begin{matrix}
B_1(x)\\
B_2(x)\\
B_3(x)\\
B_4(x)\end{matrix}\right])}-\vec{s}*{\left[\begin{matrix}
C_1(x)\\
C_2(x)\\
C_3(x)\\
C_4(x)\end{matrix}\right]}=0
$$

$$
(\vec{s}*{\left[\begin{matrix}
A_1(x)\\
A_2(x)\\
A_3(x)\\
A_4(x)\end{matrix}\right])}*A\\
(\vec{s}*{\left[\begin{matrix}
A_1(x)\\
A_2(x)\\
A_3(x)\\
A_4(x)\end{matrix}\right])}
$$

Let the left side of the above equation equal $p(x)$. When $x=1$, it verifies the first logic gate $p(1)=0$. When $x=2$, it verifies the second logic gate $p(2)=0$. When $x=3$, it verifies the third logic gate $p(3)=0$. When $x=4$, it verifies the fourth logic gate $p(4)=0$.

Based on polynomial factorization: any polynomial, as long as it has roots, can be factored into linear polynomials. Therefore, $p(x)$ can be represented as:

$$p(x)=t(x)*h(x)$$

where $t(x)=(x-1)(x-2)(x-3)(x-4)$. Therefore, $t(x)$ divides $p(x)$. This point tells us how to quickly verify if the answer is correct.

## 3. AIR

### 3.1 Definition

AIR is the arithmetization scheme used in ZK-STARK. It expresses the problem in a matrix form. The first row of the matrix is called the input, the last row is the output, and the middle of the matrix represents the intermediate parameters in the algebraic computation process. The intermediate computation states are actually a set of register values. Therefore, AIR produces a set of low-degree polynomials:

$$P=\{P_1(\vec{X},\vec{Y}),...,P_s(\vec{X},\vec{Y})\}$$

The polynomials satisfy the following conditions:

(1) The coefficients of the low-degree polynomials are within the field $F$;

(2) $\vec{X}=(X_1,...,X_w)$ represents the current computation state;

(3) $\vec{Y}=(Y_1,...,Y_w)$ represents the next computation state;

(4) $w$ is the number of variables in a computation state of the proving system;

(5) $P_i$ represents the polynomial for the transformation relationship;

(6) There is a pair of solutions $(\vec{x},\vec{y})$ that makes the transformation relationship hold, meaning only $(\vec{x},\vec{y})$ is the common solution for $P$, $P_1(\vec{x},\vec{y})=P_2(\vec{x},\vec{y})=...=P_s(\vec{x},\vec{y})=0$;

(7) The degree of AIR polynomials is the maximum value among all $P_i$;

(8) $s$ is the number of all constraints.

AIR essentially uses $s$ polynomials to describe the transformation constraints between the current execution state and the next state.

### 3.2 Execution trace

As you can see from the definition, AIR converts the relationship between the changes in register values before and after program execution into constraint polynomials, allowing the verifier to trust the entire process from input x to output y, rather than a randomly generated result or a forged output. This program execution process is called the Execution Trace.

The execution trace is a sequence of machine states that are generated when a computation is executed. In other words, to execute a program, we apply $W$ registers (width) and execute $N$ steps (length). The execution trace can be described using a table of size $N×W$.

Take the Fibonacci sequence as an example. Suppose we need to calculate the first 512 terms of the Fibonacci sequence in the field $Z_{96769}$. Based on the field addition and multiplication modulo 96769, we define:

$$a_0=1$$

$$a_1=1$$

$$a_{n+2}=(a_{n+1}+a_{n}) mod (96769)$$

Based on the definition, we can list the values of the Fibonacci sequence:

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

The Fibonacci sequence operation only uses two registers $s_0$ and $s_1$ to store the data in each intermediate state, and the generated execution trace is:

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

Based on the characteristics of the Fibonacci sequence, we can obtain the following four constraints:

* $a_0-1=0$: input constraints；

* $a_1-1=0$: input constraints；

* $\forall 0\leq i\leq 509:a_{i+2}-a_{i+1}-a_{i}=0$: confirm that the execution trace complies with the Fibonacci recursive formula;

* $a_{511}-62215=0$: output constraints.

### 3.3 Poly­no­mial Con­straints

AIR, besides generating an execution trace, also transforms constraints into polynomial constraints. It then combines these two generated objects into a low-degree polynomial. This allows the verification process between Prover and Verifier to be reduced to an agreement on a constrained polynomial. In subsequent interactions, the Prover convinces the Verifier that the execution trace satisfies the polynomial constraints.

To generate polynomial constraints, the previously mentioned Lagrange interpolation method is used, resulting in

$$\forall 0\leq i\leq 511:f(g^i)=a_i$$

Where $g$ is the generator of the subgroup, we obtain the corresponding polynomial constraints:

(1) $f(1) - 1 = 0$, ensuring the first element is 1;

(2) $f(g) - 1 = 0$, ensuring the second element is 1;

(3) $\forall 0 \le i \le 509: f(g^{i+2}) - f(g^{i+1}) - f(g^{i}) = 0$, ensuring the execution trace satisfies the Fibonacci recursive relationship;

(4) $f(g^{511}) - 62215 = 0$, the output constraint.

These polynomial constraints are constructed so that they are all verified if and only if the execution trace is valid (i.e., the trace represents a valid computation). These constraints are low-degree polynomials, but are not necessarily limited to quadratic polynomials (as in the case of R1CS).

## 4. Plonkish

"Plonkish" refers to constraint systems that feature custom gates, RAP (randomized AIR with preprocessing), or TurboPLONK/UltraPLONK. While they are defined in a matrix form, the generation of the matrix differs from traditional AIR. We will introduce this using PAIR (Preprocessed AIR) and RAP (TurboPlonk and UltraPlonk are restricted cases of RAP). 

### 4.1 PAIR
In a PAIR execution trace, an additional parameter $t$ is introduced, and $t$ predefines a column of data $c_1,…,c_t∈F^n$. Besides the $W$ columns provided by the prover, an execution trace now also includes {c_i}. (We refer to the columns provided by the prover as the witness part of the execution trace.)

When $t=1,W=2,N=5$, we have the following execution trace:

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

In this execution trace, we desire not only the addition of values in the execution rows (similar to the Fibonacci sequence in AIR), but also the execution of some row value multiplications. Therefore, we define columns $c_0,...,c_4$ as factors involved in the constraint. When we want to perform row addition, the value is 1, and when we want to perform row multiplication, the value is 0. The constraint becomes:

$$\forall 1\leq i\leq 4:c_i\cdot(a_i-(a_{i-1}+b_{i-1}))+(1-c_i)\cdot(a_i\cdot (a_{i-1}+b_{i-1}))=0$$

This method of defining predefined columns implements selection operations, hence they are often called selectors.

### 4.2 RAP
The ZKP model allows for multi-round interaction, where the verifier sends random elements in the field, and the prover receives these field elements and can add more columns in the execution trace. Therefore, the constraint polynomials can use the verifier randomness as additional variables, which is known as RAP.

Suppose there is an AIR execution trace with $W=2$, whose columns have values $a_0,...,a_{n-1}$ and $b_0,...,b_{n-1}$.

From the Schwartz-Zippel Lemma we know that to check they are a permutation of each other it suffices to check that for a uniformly chosen $\gamma∈𝐹$, we have with high probability

$$\prod _{i\in [n]}(a_i+\gamma)=\prod _{i\in [n]}(b_i+\gamma)$$

With high probability over $\gamma$, the factors of the RHS are all non-zero and in that case this is equivalent to

$$\prod _{i\in [n]}(a_i+\gamma)/(b_i+\gamma)=1$$

A RAP of length $𝑛+1$ and total width 3 can easily check this:

* The prover first sends the columns$a_0,...a_{n-1},0$和$b_0,...,b_{n-1},0$.
* The verifier sends random $\gamma \in F$
* The prover send a third column (1,z_1,…,z_{n-1}) such that for each $i \in[n]$

 $$z_i=\prod _{0\leq j \leq i-1}(a_j+\gamma)/(b_j+\gamma)$$

This randomness enables local constraints (between adjacent rows) to verify global properties (the columns being a permutation of each other).

### 4.3 Plonkish

Plonkish is essentially a PAIR or RAP, also using a table/matrix design and recording operations. It allows for customization of the number of columns and their types, with a higher number of columns leading to a higher cost. There are three different types of columns:

* Advice: Private values (parameters throughout the prover's computation);

* Fixed: Public constants (fixed values);

* Selector: Used to decide whether to enable a certain constraint on that row;

* Instance: Public input/output.

Furthermore, the relationships between cells are constrained through:

* Custom Gate Constraints: Use polynomials that equal zero to describe the cell relationships;
* Lookup Table Constraints: Cell values are items in a known Lookup table;
* Constant Constraints: Cell values are fixed values (constants).

## 5. CCS

CCS is actually an extension of R1CS, referencing the arithmetization schemes of AIR and Plonkish, without incurring any additional computational overhead.

### 5.1 Definition
A CCS structure consists of:

* size bounds $m, n, N, l, t, q, d$ where $n<l$;

* a sequence of matrices $M_0,...,M_{t−1}\in F^{
m×n}$  with at most $N$ non-zero entries in total;

* a sequence of $q$ multisets $[S_0,..., S_{q−1}]$, where an element in each multiset is from the domain $\{0,....,t-1 \}$ and the cardinality of each multiset is at most $d$;
  
* a sequence of $q$ constants $[c_0,... ,c_{q−1}]$, where each constant is from $F$.

A CCS instance consists of public input $x \in F$. A CCS witness consists of a vector $w \in F^{n-l-1}$. A CCS structure-instance tuple $(S, x)$ is satisfied by a CCS witness $w$ if

$$\sum _{i=0}^{q-1}c_i\cdot \{\bigcirc _{j\in S_i}M_j\cdot z\}=\mathbf{0}$$

where $z=(w,1,x)\in F^n$, $M_j\cdot z$ denotes matrix-vector multiplication, $\bigcirc$ denotes the Hadamard product between vectors, and $\mathbf{0}$  is an $m$-sized vector with entries equal to the the additive identity in $F$.

### 5.2 Representing R1CS with CCS

Let's first list the parameters included in the R1CS constraint system $(A \cdot z)*(B\cdot z)-(C\cdot z)=\mathbf{0}$:

* $A,B,C$: Constraint matrices;

* $z$: Constructed vector that includes witness $w$;

* $\mathbf{0}$: A $m$-sized zero vector;

* $l$: Number of public inputs;

* $m$: Number of rows in the matrix;

* $n$: Number of columns in the matrix.

Let $M_0=A$, $M_1=B$, $M_2=C$, the R1CS constraint system can be transformed into:

$$(M_0\cdot z)*(M_1\cdot z)-(M_2\cdot z)=1\cdot( M_0\cdot z)*(M_1\cdot z)+(-1)\cdot(M_2\cdot z)=\mathbf{0}$$

Let $c_0=1,c_1=-1$,$S_0= \{0,1\}$, $S_1= \{2\}$, rewriting the above equation:

$$c_0\cdot( M_0\cdot z)*(M_1\cdot z)+c_1\cdot(M_2\cdot z)\\
=c_0\cdot \{\bigcirc* _{j\in S_0}M_j\cdot z\}+c_1\cdot \{\bigcirc* _{j\in S_1}M_j\cdot z\}\\
=\sum _{i=0}^{2-1}c_i\cdot \{\bigcirc _{j\in S_i}M_j\cdot z\}=\mathbf{0}$$

Thus, R1CS is converted into CCS constraints. Besides the parameters in R1CS, the following are also added:
$t=3$, $q=2$, $d=2$, $S_0= \{0,1\}$, $S_1= \{2\}$, and the sequence of $q$ constants $\{c_0,c_1\}$.

CCS generalizes R1CS, simultaneously capturing the arithmetization of R1CS, Plonkish, and AIR without any additional overhead. Using CCS in conjunction with Spartan IOP results in SuperSpartan, which supports high-dimensional constraints without requiring the prover to incur encryption costs proportional to the constraint order. 

## 6 Conclusions
The newly emerged CCS constraint system, in essence, serves as a unified representation encompassing R1CS, AIR, and PlonkishR. It necessitates at least three matrices to define a circuit and leverages multisets for tailored constraint specification. Programming both matrices and multisets enables CCS to express arbitrary polynomial constraints. CCS marks a significant milestone in the evolution of constraint systems.

## References：

<p name = "ref1">[1]Srinath Setty, Justin Thaler, and Riad Wahby. Customizable constraint systems for succinct arguments.Cryptology {ePrint} Archive, Paper 2023/552. https://eprint.iacr.org/2023/552.

<p name = "ref2">[2]https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649
