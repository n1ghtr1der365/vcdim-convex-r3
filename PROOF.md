# Proof of `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3`

## Theorem

**Theorem (`hasAddVCNDimAtMost_two_two_of_convex_r3`).**
For every convex set $C \subseteq \mathbb{R}^3$, there do **not** exist $u_0, u_1, u_2 \in \mathbb{R}^3$, $v_0, v_1, v_2 \in \mathbb{R}^3$, and translates $\{y_S \in \mathbb{R}^3 : S \subseteq \{0,1,2\}^2\}$ such that for all $S \subseteq \{0,1,2\}^2$ and all $(i, j) \in \{0,1,2\}^2$,
$$y_S + u_i + v_j \in C \iff (i, j) \in S.$$

Equivalently, $\mathrm{VC}_2(\text{convex sets in }\mathbb{R}^3) \le 2$ (and combined with Kenta Kitamura's $2 \times 2$ counterexample, $\mathrm{VC}_2(\text{convex sets in }\mathbb{R}^3) = 2$ **exactly**).

> **Remark (Sharpness):** In contrast, the $2 \times 3$ grid $P_{2 \times 3} = \{0, e_1\} + \{0, e_2, e_3\}$ *is* shatterable by translates of a 13-halfspace integer polytope in $\mathbb{R}^3$ (see `cert_2x3.json`, verified in exact integer arithmetic by `verify_certificate.py`).
>
> **Remark (Elementarity):** The proof below requires **no** topology, **no** Hahn–Banach / separating hyperplane theorem, and **no** closedness assumptions on $C$. It uses only elementary 3D affine linear algebra and explicit 3- and 4-point convex combinations.

---

## Preliminaries

Assume for contradiction that a convex set $C \subseteq \mathbb{R}^3$, vectors $u_0, u_1, u_2 \in \mathbb{R}^3$, $v_0, v_1, v_2 \in \mathbb{R}^3$, and translates $\{y_S\}$ shatter $U + V$. Write $p_{i,j} := u_i + v_j$.

**Observation 1 (Affine invariance).**
For any invertible linear map $A \in \mathrm{GL}_3(\mathbb{R})$ and any translations $t_U, t_V \in \mathbb{R}^3$, replacing $C$ by $A(C)$, $u_i$ by $A(u_i) + t_U$, $v_j$ by $A(v_j) + t_V$, and $y_S$ by $A(y_S) - t_U - t_V$ preserves convexity of $C$ and the shattering condition. Similarly, permuting the indices of $U$ or $V$ (or swapping $U \leftrightarrow V$) preserves shattering.

**Observation 2 (Strict convex position).**
No point $p_{i_0, j_0}$ can be written as a convex combination of $\{p_{i,j} : (i,j) \ne (i_0, j_0)\}$.
*Proof.* If $p_{i_0, j_0} = \sum_{(i,j) \ne (i_0, j_0)} w_{i,j} p_{i,j}$ with $w_{i,j} \ge 0$ and $\sum w_{i,j} = 1$, consider the mask $S = \{0,1,2\}^2 \setminus \{(i_0, j_0)\}$. Then $y_S + p_{i,j} \in C$ for all $(i,j) \ne (i_0, j_0)$, so by convexity of $C$,
$$y_S + p_{i_0, j_0} = \sum_{(i,j) \ne (i_0, j_0)} w_{i,j} (y_S + p_{i,j}) \in C,$$
contradicting $(i_0, j_0) \notin S$. $\square$

---

## Lemma 1 (No Coplanar $2 \times 3$ Subgrid is in Convex Position)

**Lemma 1.** Let $u_0, u_1 \in \mathbb{R}^2$ and $v_0, v_1, v_2 \in \mathbb{R}^2$. Then at least one of the 6 pairs $(i,j) \in \{0,1\} \times \{0,1,2\}$ has $u_i + v_j \in \operatorname{conv}\{u_{i'} + v_{j'} : (i', j') \ne (i, j)\}$.

*Proof.*
If $u_0 = u_1$, then $u_0 + v_0 = 1 \cdot (u_1 + v_0)$, done. Otherwise set $w := u_1 - u_0 \ne 0$, and let $n \in \mathbb{R}^2 \setminus \{0\}$ be perpendicular to $w$ (e.g., $n = (-w_2, w_1)$). Permute $v_0, v_1, v_2$ so that $n \cdot v_0 \le n \cdot v_1 \le n \cdot v_2$.

Choose $\lambda \in [0, 1]$ such that $n \cdot (\lambda v_0 + (1-\lambda) v_2) = n \cdot v_1$ (specifically $\lambda = \frac{n \cdot v_2 - n \cdot v_1}{n \cdot v_2 - n \cdot v_0}$ if $n \cdot v_2 > n \cdot v_0$, else $\lambda = \frac{1}{2}$), and set $p := \lambda v_0 + (1-\lambda) v_2$. Since $n \cdot (v_1 - p) = 0$ and $n \perp w \ne 0$ in $\mathbb{R}^2$, there exists $t \in \mathbb{R}$ such that
$$v_1 - p = t w.$$
Let $q_0 := u_0 + p = \lambda (u_0 + v_0) + (1-\lambda)(u_0 + v_2)$ and $q_1 := u_1 + p = \lambda (u_1 + v_0) + (1-\lambda)(u_1 + v_2)$, noting that $q_1 = q_0 + w$, $u_0 + v_1 = q_0 + t w$, and $u_1 + v_1 = q_0 + (t + 1) w$.

- **Case $0 \le t \le 1$:**
  $$u_0 + v_1 = (1 - t) q_0 + t q_1 \in \operatorname{conv}\{u_0+v_0,\, u_0+v_2,\, u_1+v_0,\, u_1+v_2\}.$$
- **Case $t > 1$:**
  $$u_0 + v_1 = \frac{1}{t + 1} q_0 + \frac{t}{t + 1} (u_1 + v_1) \in \operatorname{conv}\{u_0+v_0,\, u_0+v_2,\, u_1+v_1\}.$$
- **Case $-1 \le t < 0$:** Set $s := -t \in (0, 1]$. Then
  $$u_1 + v_1 = s q_0 + (1 - s) q_1 \in \operatorname{conv}\{u_0+v_0,\, u_0+v_2,\, u_1+v_0,\, u_1+v_2\}.$$
- **Case $t < -1$:** Set $s := -t > 1$. Then
  $$u_1 + v_1 = \frac{1}{s + 1} q_1 + \frac{s}{s + 1} (u_0 + v_1) \in \operatorname{conv}\{u_1+v_0,\, u_1+v_2,\, u_0+v_1\}.$$

In all four cases, the convex combination uses only pairs $(i', j') \ne (i, j)$. $\square$

**Corollary.** No $2 \times 3$ subgrid $\{u_{i_1}, u_{i_2}\} + V$ and no $3 \times 2$ subgrid $U + \{v_{j_1}, v_{j_2}\}$ can lie in a 2-dimensional affine subspace of $\mathbb{R}^3$.

---

## Lemma 2 (Paraboloid Affine Normal Form)

**Lemma 2.** Up to an affine transformation of $\mathbb{R}^3$ and relabeling of $U$ and $V$, there exist real numbers $a_0 < 0 < a_2$, $b_0 < 0 < b_2$, and $c > 0$ such that
$$u_0 = (a_0, 0, 1), \quad u_1 = (0, 0, 0), \quad u_2 = (a_2, 0, 1),$$
$$v_0 = (0, b_0, c), \quad v_1 = (0, 0, 0), \quad v_2 = (0, b_2, c).$$

*Proof.*
1. By the Corollary to Lemma 1, $U$ cannot be collinear (else $U + \{v_0, v_1\}$ lies in a 2D plane), so $W_U := \operatorname{span}\{u_0 - u_1, u_2 - u_1\}$ has $\dim(W_U) = 2$. Likewise $W_V := \operatorname{span}\{v_0 - v_1, v_2 - v_1\}$ has $\dim(W_V) = 2$.
2. We have $W_U \ne W_V$ (else $U + V$ lies in a single 2D affine plane, contradicting Lemma 1). Therefore $\dim(W_U \cap W_V) = \dim W_U + \dim W_V - \dim(W_U + W_V) = 2 + 2 - 3 = 1$.
3. Choose a basis $(e_1, e_2, e_3)$ of $\mathbb{R}^3$ with $e_3 \in (W_U \cap W_V) \setminus \{0\}$, $e_1 \in W_U \setminus W_V$, and $e_2 \in W_V \setminus W_U$. Applying the invertible linear map sending $(e_1, e_2, e_3)$ to the standard basis and translating $U, V$ so $u_1 = v_1 = 0$, we obtain
   $$u_i = (a_i, 0, f_i), \qquad v_j = (0, b_j, g_j) \qquad (i, j \in \{0, 1, 2\}).$$
4. All three $a_i$ are distinct: if $a_{i_1} = a_{i_2}$ ($i_1 \ne i_2$), then $\{u_{i_1}, u_{i_2}\} + V$ lies in the 2D plane $\{x = a_{i_1}\}$, contradicting Lemma 1. Similarly, all three $b_j$ are distinct.
5. Relabel $U$ and $V$ so that $a_0 < a_1 < a_2$ and $b_0 < b_1 < b_2$, and re-translate so $a_1 = f_1 = b_1 = g_1 = 0$ (hence $a_0 < 0 < a_2$ and $b_0 < 0 < b_2$).
6. Apply the invertible linear shear $(x, y, z) \mapsto (x, y, z - s_x x - s_y y)$ with $s_x := \frac{f_2 - f_0}{a_2 - a_0}$ and $s_y := \frac{g_2 - g_0}{b_2 - b_0}$. This preserves the $x$- and $y$-coordinates and maps $f_0, f_2$ to a common value $F := f_0 - s_x a_0 = f_2 - s_x a_2$ and $g_0, g_2$ to a common value $G := g_0 - s_y b_0 = g_2 - s_y b_2$.
7. We have $F \ne 0$ (else $U$ lies on the $x$-axis, collinear) and $G \ne 0$ (else $V$ lies on the $y$-axis, collinear).
8. We claim $F \cdot G > 0$. Suppose instead $F \cdot G < 0$; without loss of generality $F > 0 > G$. Set
   $$\lambda := \frac{a_2}{a_2 - a_0} \in (0, 1), \qquad \mu := \frac{b_2}{b_2 - b_0} \in (0, 1), \qquad t := \frac{-G}{F - G} \in (0, 1).$$
   Then $\lambda a_0 + (1-\lambda) a_2 = 0$, $\mu b_0 + (1-\mu) b_2 = 0$, and $t F + (1-t) G = 0$, so
   $$p_{1,1} = (0, 0, 0) = t\big(\lambda p_{0,1} + (1-\lambda) p_{2,1}\big) + (1-t)\big(\mu p_{1,0} + (1-\mu) p_{1,2}\big),$$
   contradicting Observation 2.
9. Finally, scale the $z$-coordinate by $1/F \ne 0$, setting $c := G / F > 0$. $\square$

---

## Lemma 3 (The 2-Mask Contradiction)

**Lemma 3.** Let $U = \{(a_0, 0, 1), (0, 0, 0), (a_2, 0, 1)\}$ and $V = \{(0, b_0, c), (0, 0, 0), (0, b_2, c)\}$ with $a_0 < 0 < a_2$, $b_0 < 0 < b_2$, and $c > 0$. No convex set $C \subseteq \mathbb{R}^3$ can simultaneously realize the two masks:
- $M_h := \{0,1,2\}^2 \setminus \{(1, 0), (1, 2)\}$ (via translate $y_1 \in \mathbb{R}^3$),
- $M_v := \{0,1,2\}^2 \setminus \{(0, 1), (2, 1)\}$ (via translate $y_2 \in \mathbb{R}^3$).

*Proof.*
Assume for contradiction that $y_1, y_2 \in \mathbb{R}^3$ realize $M_h$ and $M_v$ respectively. In particular:
- All 4 corners $p_{0,0}, p_{0,2}, p_{2,0}, p_{2,2}$ and the center $p_{1,1}$ satisfy $y_1 + p_{i,j} \in C$ and $y_2 + p_{i,j} \in C$.
- $y_1 + p_{0,1}, y_1 + p_{2,1} \in C$ and $y_2 + p_{1,0}, y_2 + p_{1,2} \in C$.
- $y_1 + p_{1,0}, y_1 + p_{1,2} \notin C$ and $y_2 + p_{0,1}, y_2 + p_{2,1} \notin C$.

Set $d = (d_x, d_y, d_z) := y_1 - y_2 \in \mathbb{R}^3$, and define the non-negative piecewise-linear functions
$$\phi_a(d_x) := \max\!\left(\frac{d_x}{a_2},\, \frac{d_x}{a_0}\right) = \begin{cases} d_x / a_2 & d_x \ge 0 \\ d_x / a_0 & d_x < 0 \end{cases} \ge 0,$$
$$\psi_b(d_y) := \max\!\left(-\frac{d_y}{b_0},\, -\frac{d_y}{b_2}\right) = \begin{cases} -d_y / b_0 & d_y \ge 0 \\ -d_y / b_2 & d_y < 0 \end{cases} \ge 0.$$

We split into two exhaustive cases depending on the sign of $d_z - (\phi_a(d_x) - c\,\psi_b(d_y))$.

### Case A: $d_z \ge \phi_a(d_x) - c\,\psi_b(d_y)$

Define
$$\lambda_1 := \frac{a_2 (d_z + c\,\psi_b(d_y)) - d_x}{a_2 - a_0}, \qquad \lambda_2 := \frac{d_x - a_0 (d_z + c\,\psi_b(d_y))}{a_2 - a_0}, \qquad \lambda_3 := \psi_b(d_y), \qquad \lambda_4 := 1.$$
Since $a_2 - a_0 > 0$, $a_2 > 0 > a_0$, and $d_z + c\,\psi_b(d_y) \ge \phi_a(d_x) = \max(d_x/a_2, d_x/a_0)$, we have $\lambda_1 \ge 0$, $\lambda_2 \ge 0$, $\lambda_3 \ge 0$, and $\lambda_4 = 1 > 0$, so $W := \lambda_1 + \lambda_2 + \lambda_3 + 1 \ge 1 > 0$. Moreover, direct expansion gives:
$$\lambda_1 a_0 + \lambda_2 a_2 = d_x, \qquad \lambda_1 + \lambda_2 = d_z + c\,\lambda_3.$$

- **Subcase A1 ($d_y \ge 0$, so $\lambda_3 = -d_y / b_0$):**
  Then $-\lambda_3 b_0 = d_y$, so:
  $$\lambda_1 (a_0, 0, 1) + \lambda_2 (a_2, 0, 1) + \lambda_3 (0, -b_0, -c) + 1 \cdot (-d_x, -d_y, -d_z) = (0, 0, 0).$$
  Adding $W \cdot (y_1 + p_{1,0})$ to both sides and dividing by $W > 0$ yields
  $$y_1 + p_{1,0} = \frac{\lambda_1}{W}(y_1 + p_{0,0}) + \frac{\lambda_2}{W}(y_1 + p_{2,0}) + \frac{\lambda_3}{W}(y_1 + p_{1,1}) + \frac{1}{W}(y_2 + p_{1,0}) \in C,$$
  since all four points on the right lie in $C$ and $C$ is convex. This contradicts $y_1 + p_{1,0} \notin C$.

- **Subcase A2 ($d_y < 0$, so $\lambda_3 = -d_y / b_2$):**
  Then $-\lambda_3 b_2 = d_y$, so:
  $$\lambda_1 (a_0, 0, 1) + \lambda_2 (a_2, 0, 1) + \lambda_3 (0, -b_2, -c) + 1 \cdot (-d_x, -d_y, -d_z) = (0, 0, 0).$$
  Adding $W \cdot (y_1 + p_{1,2})$ and dividing by $W > 0$ yields
  $$y_1 + p_{1,2} = \frac{\lambda_1}{W}(y_1 + p_{0,2}) + \frac{\lambda_2}{W}(y_1 + p_{2,2}) + \frac{\lambda_3}{W}(y_1 + p_{1,1}) + \frac{1}{W}(y_2 + p_{1,2}) \in C,$$
  contradicting $y_1 + p_{1,2} \notin C$.

### Case B: $d_z < \phi_a(d_x) - c\,\psi_b(d_y)$

Define
$$\mu_1 := \frac{b_2 (\phi_a(d_x) - d_z)/c + d_y}{b_2 - b_0}, \qquad \mu_2 := \frac{-d_y - b_0 (\phi_a(d_x) - d_z)/c}{b_2 - b_0}, \qquad \mu_3 := \phi_a(d_x), \qquad \mu_4 := 1.$$
Since $b_2 - b_0 > 0$, $b_2 > 0 > b_0$, $c > 0$, and $(\phi_a(d_x) - d_z)/c > \psi_b(d_y) = \max(-d_y/b_0, -d_y/b_2)$, we have $\mu_1 > 0$, $\mu_2 > 0$, $\mu_3 \ge 0$, and $\mu_4 = 1 > 0$, so $W' := \mu_1 + \mu_2 + \mu_3 + 1 \ge 1 > 0$. Direct expansion gives:
$$\mu_1 b_0 + \mu_2 b_2 = -d_y, \qquad c(\mu_1 + \mu_2) = \mu_3 - d_z.$$

- **Subcase B1 ($d_x \ge 0$, so $\mu_3 = d_x / a_2$):**
  Then $-\mu_3 a_2 = -d_x$, so:
  $$\mu_1 (0, b_0, c) + \mu_2 (0, b_2, c) + \mu_3 (-a_2, 0, -1) + 1 \cdot (d_x, d_y, d_z) = (0, 0, 0).$$
  Adding $W' \cdot (y_2 + p_{2,1})$ and dividing by $W' > 0$ yields
  $$y_2 + p_{2,1} = \frac{\mu_1}{W'}(y_2 + p_{2,0}) + \frac{\mu_2}{W'}(y_2 + p_{2,2}) + \frac{\mu_3}{W'}(y_2 + p_{1,1}) + \frac{1}{W'}(y_1 + p_{2,1}) \in C,$$
  contradicting $y_2 + p_{2,1} \notin C$.

- **Subcase B2 ($d_x < 0$, so $\mu_3 = d_x / a_0$):**
  Then $-\mu_3 a_0 = -d_x$, so:
  $$\mu_1 (0, b_0, c) + \mu_2 (0, b_2, c) + \mu_3 (-a_0, 0, -1) + 1 \cdot (d_x, d_y, d_z) = (0, 0, 0).$$
  Adding $W' \cdot (y_2 + p_{0,1})$ and dividing by $W' > 0$ yields
  $$y_2 + p_{0,1} = \frac{\mu_1}{W'}(y_2 + p_{0,0}) + \frac{\mu_2}{W'}(y_2 + p_{0,2}) + \frac{\mu_3}{W'}(y_2 + p_{1,1}) + \frac{1}{W'}(y_1 + p_{0,1}) \in C,$$
  contradicting $y_2 + p_{0,1} \notin C$.

In every case we obtain a contradiction. $\square$

---

## Proof of Main Theorem

Combine Observation 1, Lemma 1, Lemma 2, and Lemma 3. $\blacksquare$

## Numerical Verification

Both Lemma 1 (10,000 random 2D $2 \times 3$ grids, `max_err = 1.52e-14`) and Lemma 3 (100,000 random paraboloid $3 \times 3$ grids and translate differences, `max_err = 1.48e-14`) were independently verified in `verify_proof.py`.
