# Formal Proof of `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3`

This repository contains a complete, kernel-verified Lean 4 (`v4.35.0-rc2`) formal proof of the open conjecture `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3` from [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/VCDimConvex.lean):

```lean
theorem hasAddVCNDimAtMost_two_two_of_convex_r3 {C : Set ℝ³} (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C 2 2
```

Combined with Kenta Kitamura's $2 \times 2$ lower bound (`hasAddVCNDimAtMost_two_one_of_convex_r3`), this determines the exact 2-dimensional additive VC dimension of convex sets in $\mathbb{R}^3$:

$$\mathrm{VC}_2(\text{convex sets in }\mathbb{R}^3) = 2$$

(improving the previous upper bound of $2^{128} - 1$).

## Verification

```bash
lake exe cache get
lake build VCDimConvexR3
```

`VCDimConvexR3.lean` compiles with **0 errors, 0 warnings, and 0 `sorry`**, and `#print axioms` reports only the standard Lean/Mathlib axioms:

```text
'VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Proof Outline

The proof is completely elementary (no topology, no Hahn–Banach, no closedness assumptions on $C \subseteq \mathbb{R}^3$):

1. **No coplanar $2 \times 3$ grid is in convex position (`exists_convex_comb_2x3_r2`):** Any $2 \times 3$ additive grid in $\mathbb{R}^2$ has a point in the convex hull of the other 5 points (4-case explicit convex combination).
2. **Paraboloid affine normal form (`not_shatters_3x3_r3`):** Any $3 \times 3$ grid in $\mathbb{R}^3$ with no coplanar $2 \times 3$ or $3 \times 2$ subgrid reduces via an explicit invertible 3D cross-product linear map, shear, and scaling to:
   $$U = \{(a_0, 0, 1), (0, 0, 0), (a_2, 0, 1)\}, \qquad V = \{(0, b_0, c), (0, 0, 0), (0, b_2, c)\}$$
   with $a_0 < 0 < a_2$, $b_0 < 0 < b_2$, $c > 0$.
3. **2-mask contradiction (`paraboloid_contradiction`):** No convex set $C \subseteq \mathbb{R}^3$ can simultaneously realize $M_h = \{0,1,2\}^2 \setminus \{(1,0),(1,2)\}$ and $M_v = \{0,1,2\}^2 \setminus \{(0,1),(2,1)\}$; comparing $d_z = (y_1 - y_2)_z$ against $\phi_a(d_x) - c\,\psi_b(d_y)$ gives an explicit 4-point convex combination contradiction.

## Companion Sharpness Certificate ($2 \times 3$ Prism)

As a companion result showing that $3 \times 3$ is minimal, `cert_2x3.json` gives an explicit 13-halfspace exact integer polytope in $\mathbb{R}^3$ whose translates shatter all $2^6 = 64$ subsets of a $2 \times 3$ additive grid:

```bash
python verify_certificate.py cert_2x3.json
# VERIFIED EXACTLY: |U|=2, |V|=3, |P|=6, |halfspaces|=13, all 64/64 subsets shattered!
```

## License

Apache-2.0
