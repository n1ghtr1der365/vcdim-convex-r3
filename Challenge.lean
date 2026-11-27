module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Advertised Statement: `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3`

Every convex set $C \subseteq \mathbb{R}^3$ has additive $\mathrm{VC}_2$-dimension at most $2$:
no family of translates $\{y + C\}$ can shatter any $3 \times 3$ additive grid $U + V \subset \mathbb{R}^3$.

This statement matches `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3` in
`google-deepmind/formal-conjectures` (`FormalConjectures/Other/VCDimConvex.lean`), with
`HasAddVCNDimAtMost` reproduced verbatim from
`FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean`.
-/

namespace VCDimConvex

/-- A set `A` in an additive abelian group has additive $\mathrm{VC}_n$ dimension at most `d` iff
one cannot find sequences `x : Fin n → Fin (d + 1) → G` and `y : Set (Fin n → Fin (d + 1)) → G`
such that `y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s` for all `i` and `s`. -/
def HasAddVCNDimAtMost {G : Type*} [AddCommGroup G] (A : Set G) (n d : ℕ) : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s

/-- Every convex set in $\mathbb{R}^3$ has additive $\mathrm{VC}_2$ dimension at most $2$. -/
theorem hasAddVCNDimAtMost_two_two_of_convex_r3
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C 2 2 := by
  sorry

end VCDimConvex
