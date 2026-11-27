module

public import Mathlib

@[expose] public section

/-!
# Proof of `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3`

Every convex set in $\mathbb{R}^3$ has additive $\mathrm{VC}_2$-dimension at most $2$.
The proof is completely elementary (no topology, no Hahn–Banach, no closedness assumptions):
1. No coplanar $2 \times 3$ grid is in convex position.
2. Any $3 \times 3$ grid in $\mathbb{R}^3$ without coplanar $2 \times 3$ subgrids reduces via an
   explicit invertible affine map to paraboloid normal form.
3. On paraboloid normal form, the two masks missing $\{(1,0),(1,2)\}$ and $\{(0,1),(2,1)\}$
   yield an explicit 4-point convex combination contradiction.
-/

open scoped BigOperators

namespace VCDimConvex

/-- A set `A` in an additive abelian group has additive $\mathrm{VC}_n$ dimension at most `d` iff
one cannot find sequences `x : Fin n → Fin (d + 1) → G` and `y : Set (Fin n → Fin (d + 1)) → G`
such that `y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s` for all `i` and `s`. -/
def HasAddVCNDimAtMost {G : Type*} [AddCommGroup G] (A : Set G) (n d : ℕ) : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s

private abbrev R3 := Fin 3 → ℝ
private abbrev R2 := Fin 2 → ℝ

/- ### Helper: 3D dot product, cross product, and grid shattering -/

private def dot3 (a b : R3) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

private def cross3 (a b : R3) : R3 :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

private def dot2 (a b : R2) : ℝ := a 0 * b 0 + a 1 * b 1

private def ShattersGrid {m n : ℕ} {E : Type*} [AddCommGroup E] (C : Set E)
    (u : Fin m → E) (v : Fin n → E) : Prop :=
  ∃ y : Set (Fin m × Fin n) → E, ∀ i j s, y s + u i + v j ∈ C ↔ (i, j) ∈ s

private lemma dot3_self_ne_zero {a : R3} (ha : a ≠ 0) : dot3 a a ≠ 0 := by
  intro h
  simp only [dot3] at h
  apply ha
  ext k
  fin_cases k
  · show a 0 = 0; nlinarith
  · show a 1 = 0; nlinarith
  · show a 2 = 0; nlinarith

private lemma cross3_self_dot_left (a b : R3) : dot3 (cross3 a b) a = 0 := by
  simp [dot3, cross3]; ring

private lemma cross3_self_dot_right (a b : R3) : dot3 (cross3 a b) b = 0 := by
  simp [dot3, cross3]; ring

private lemma lagrange_dot_cross (m d v : R3) (hmd : dot3 m d = 0) (hc : cross3 d v = 0) :
    dot3 m v * dot3 d d = 0 := by
  have c0 : d 1 * v 2 - d 2 * v 1 = 0 := by simpa [cross3] using congrFun hc 0
  have c1 : d 2 * v 0 - d 0 * v 2 = 0 := by simpa [cross3] using congrFun hc 1
  have c2 : d 0 * v 1 - d 1 * v 0 = 0 := by simpa [cross3] using congrFun hc 2
  simp only [dot3] at hmd ⊢
  have hid : (m 0 * v 0 + m 1 * v 1 + m 2 * v 2) * (d 0 * d 0 + d 1 * d 1 + d 2 * d 2) =
      (m 0 * d 0 + m 1 * d 1 + m 2 * d 2) * (d 0 * v 0 + d 1 * v 1 + d 2 * v 2) -
      (m 1 * d 2 - m 2 * d 1) * (d 1 * v 2 - d 2 * v 1) -
      (m 2 * d 0 - m 0 * d 2) * (d 2 * v 0 - d 0 * v 2) -
      (m 0 * d 1 - m 1 * d 0) * (d 0 * v 1 - d 1 * v 0) := by ring
  rw [hid, hmd, c0, c1, c2]; ring

private lemma cross3_orthog_eq_zero (nU nV x : R3)
    (hV : dot3 nV x = 0) (hU : dot3 nU x = 0) (hE : dot3 (cross3 nU nV) x = 0)
    (he3 : cross3 nU nV ≠ 0) : x = 0 := by
  have hsq : dot3 (cross3 nU nV) (cross3 nU nV) ≠ 0 := dot3_self_ne_zero he3
  simp only [dot3, cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hV hU hE hsq
  set c0 := nU 1 * nV 2 - nU 2 * nV 1
  set c1 := nU 2 * nV 0 - nU 0 * nV 2
  set c2 := nU 0 * nV 1 - nU 1 * nV 0
  ext k
  fin_cases k
  · show x 0 = 0
    have hid : x 0 * (c0 * c0 + c1 * c1 + c2 * c2) =
        (nU 2 * c1 - nU 1 * c2) * (nV 0 * x 0 + nV 1 * x 1 + nV 2 * x 2) +
        (nV 1 * c2 - nV 2 * c1) * (nU 0 * x 0 + nU 1 * x 1 + nU 2 * x 2) +
        c0 * (c0 * x 0 + c1 * x 1 + c2 * x 2) := by dsimp [c0, c1, c2]; ring
    rw [hV, hU, hE] at hid
    exact (mul_eq_zero.mp (by linarith)).resolve_right hsq
  · show x 1 = 0
    have hid : x 1 * (c0 * c0 + c1 * c1 + c2 * c2) =
        (nU 0 * c2 - nU 2 * c0) * (nV 0 * x 0 + nV 1 * x 1 + nV 2 * x 2) +
        (nV 2 * c0 - nV 0 * c2) * (nU 0 * x 0 + nU 1 * x 1 + nU 2 * x 2) +
        c1 * (c0 * x 0 + c1 * x 1 + c2 * x 2) := by dsimp [c0, c1, c2]; ring
    rw [hV, hU, hE] at hid
    exact (mul_eq_zero.mp (by linarith)).resolve_right hsq
  · show x 2 = 0
    have hid : x 2 * (c0 * c0 + c1 * c1 + c2 * c2) =
        (nU 1 * c0 - nU 0 * c1) * (nV 0 * x 0 + nV 1 * x 1 + nV 2 * x 2) +
        (nV 0 * c1 - nV 1 * c0) * (nU 0 * x 0 + nU 1 * x 1 + nU 2 * x 2) +
        c2 * (c0 * x 0 + c1 * x 1 + c2 * x 2) := by dsimp [c0, c1, c2]; ring
    rw [hV, hU, hE] at hid
    exact (mul_eq_zero.mp (by linarith)).resolve_right hsq

/- ### Convex combination helpers -/

private lemma convex_combo4 {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}
    (hC : Convex ℝ C) {p1 p2 p3 p4 q : E} {w1 w2 w3 w4 : ℝ}
    (hp1 : p1 ∈ C) (hp2 : p2 ∈ C) (hp3 : p3 ∈ C) (hp4 : p4 ∈ C)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hw4 : 0 ≤ w4)
    (hW : 0 < w1 + w2 + w3 + w4)
    (hq : q = (w1 / (w1 + w2 + w3 + w4)) • p1 + (w2 / (w1 + w2 + w3 + w4)) • p2 +
              (w3 / (w1 + w2 + w3 + w4)) • p3 + (w4 / (w1 + w2 + w3 + w4)) • p4) :
    q ∈ C := by
  set W := w1 + w2 + w3 + w4
  let pts : Fin 4 → E := ![p1, p2, p3, p4]
  let ws : Fin 4 → ℝ := ![w1 / W, w2 / W, w3 / W, w4 / W]
  have hmem : ∑ k : Fin 4, ws k • pts k ∈ C := by
    apply hC.sum_mem
    · intro k _
      fin_cases k <;> simp [ws] <;> positivity
    · simp only [Fin.sum_univ_four, ws, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      field_simp [hW.ne']
      ring
    · intro k _
      fin_cases k <;> simp [pts, hp1, hp2, hp3, hp4]
  simpa [Fin.sum_univ_four, pts, ws, add_assoc, hq] using hmem

/- ### Invariance properties of `ShattersGrid` -/

private lemma ShattersGrid.not_convex_comb {m n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : Set E} (hC : Convex ℝ C) {u : Fin m → E} {v : Fin n → E}
    (hS : ShattersGrid C u v) (i0 : Fin m) (j0 : Fin n)
    (w : Fin m × Fin n → ℝ) (hw0 : w (i0, j0) = 0)
    (hw_nonneg : ∀ p, 0 ≤ w p) (hw_sum : ∑ p, w p = 1)
    (hcomb : ∑ p, w p • (u p.1 + v p.2) = u i0 + v j0) : False := by
  obtain ⟨y, hy⟩ := hS
  let s : Set (Fin m × Fin n) := {(i0, j0)}ᶜ
  let t : Finset (Fin m × Fin n) := Finset.univ.erase (i0, j0)
  have hsum_w : ∑ p ∈ t, w p = 1 := by
    have := Finset.add_sum_erase Finset.univ w (Finset.mem_univ (i0, j0))
    linarith
  have hmem : ∑ p ∈ t, w p • (y s + u p.1 + v p.2) ∈ C := by
    apply hC.sum_mem (fun p _ ↦ hw_nonneg p) hsum_w
    intro p hp
    exact (hy p.1 p.2 s).mpr (Finset.ne_of_mem_erase hp)
  have heq : ∑ p ∈ t, w p • (y s + u p.1 + v p.2) = y s + u i0 + v j0 := by
    have h1 : ∑ p ∈ t, w p • (y s + u p.1 + v p.2) =
        (∑ p ∈ t, w p) • y s + ∑ p ∈ t, w p • (u p.1 + v p.2) := by
      simp_rw [add_assoc, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have h2 : ∑ p ∈ t, w p • (u p.1 + v p.2) = u i0 + v j0 := by
      have := Finset.add_sum_erase Finset.univ (fun p ↦ w p • (u p.1 + v p.2))
        (Finset.mem_univ (i0, j0))
      rw [hw0, zero_smul, zero_add] at this
      rw [this, hcomb]
    rw [h1, hsum_w, one_smul, h2, add_assoc]
  rw [heq] at hmem
  exact ((hy i0 j0 s).mp hmem) rfl

private lemma ShattersGrid.comp_left {m m' n : ℕ} {E : Type*} [AddCommGroup E] {C : Set E}
    {u : Fin m → E} {v : Fin n → E} (hS : ShattersGrid C u v)
    (f : Fin m' → Fin m) (hf : Function.Injective f) :
    ShattersGrid C (u ∘ f) v := by
  obtain ⟨y, hy⟩ := hS
  refine ⟨fun s ↦ y ((fun p : Fin m' × Fin n ↦ (f p.1, p.2)) '' s), fun i j s ↦ ?_⟩
  dsimp only [Function.comp_apply]
  rw [hy (f i) j]
  constructor
  · rintro ⟨⟨i', j'⟩, hmem, hEq⟩
    have hi : f i' = f i := congrArg Prod.fst hEq
    have hj : j' = j := congrArg Prod.snd hEq
    rw [hf hi, hj] at hmem
    exact hmem
  · intro hmem
    exact ⟨(i, j), hmem, rfl⟩

private lemma ShattersGrid.comp_right {m n n' : ℕ} {E : Type*} [AddCommGroup E] {C : Set E}
    {u : Fin m → E} {v : Fin n → E} (hS : ShattersGrid C u v)
    (g : Fin n' → Fin n) (hg : Function.Injective g) :
    ShattersGrid C u (v ∘ g) := by
  obtain ⟨y, hy⟩ := hS
  refine ⟨fun s ↦ y ((fun p : Fin m × Fin n' ↦ (p.1, g p.2)) '' s), fun i j s ↦ ?_⟩
  dsimp only [Function.comp_apply]
  rw [hy i (g j)]
  constructor
  · rintro ⟨⟨i', j'⟩, hmem, hEq⟩
    have hi : i' = i := congrArg Prod.fst hEq
    have hj : g j' = g j := congrArg Prod.snd hEq
    rw [hi, hg hj] at hmem
    exact hmem
  · intro hmem
    exact ⟨(i, j), hmem, rfl⟩

private lemma ShattersGrid.swap {m n : ℕ} {E : Type*} [AddCommGroup E] {C : Set E}
    {u : Fin m → E} {v : Fin n → E} (hS : ShattersGrid C u v) :
    ShattersGrid C v u := by
  obtain ⟨y, hy⟩ := hS
  refine ⟨fun s ↦ y (Prod.swap '' s), fun j i s ↦ ?_⟩
  have hcomm : y (Prod.swap '' s) + v j + u i = y (Prod.swap '' s) + u i + v j := by abel
  rw [hcomm, hy i j]
  constructor
  · rintro ⟨⟨j', i'⟩, hmem, hEq⟩
    have hi : i' = i := congrArg Prod.fst hEq
    have hj : j' = j := congrArg Prod.snd hEq
    rw [hi, hj] at hmem
    exact hmem
  · intro hmem
    exact ⟨(j, i), hmem, rfl⟩

private lemma ShattersGrid.translate {m n : ℕ} {E : Type*} [AddCommGroup E] {C : Set E}
    {u : Fin m → E} {v : Fin n → E} (hS : ShattersGrid C u v) (tU tV : E) :
    ShattersGrid C (fun i ↦ u i + tU) (fun j ↦ v j + tV) := by
  obtain ⟨y, hy⟩ := hS
  refine ⟨fun s ↦ y s - tU - tV, fun i j s ↦ ?_⟩
  have h : (y s - tU - tV) + (u i + tU) + (v j + tV) = y s + u i + v j := by abel
  rw [h]
  exact hy i j s

private lemma ShattersGrid.linear_image {m n : ℕ} {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {C : Set E} {u : Fin m → E} {v : Fin n → E}
    (hS : ShattersGrid C u v) (L : E →ₗ[ℝ] F) (hL : Function.Injective L) :
    ShattersGrid (L '' C) (fun i ↦ L (u i)) (fun j ↦ L (v j)) := by
  obtain ⟨y, hy⟩ := hS
  refine ⟨fun s ↦ L (y s), fun i j s ↦ ?_⟩
  have h : L (y s) + L (u i) + L (v j) = L (y s + u i + v j) := by
    rw [← map_add, ← map_add]
  rw [h, hL.mem_set_image]
  exact hy i j s

/- ### Lemma 1: No 2×3 grid in ℝ² is in convex position -/

private lemma exists_convex_comb_2x3_r2_sorted (u : Fin 2 → R2) (v : Fin 3 → R2)
    (hw_ne : u 1 ≠ u 0)
    (hsort1 : dot2 ![-((u 1 - u 0) 1), (u 1 - u 0) 0] (v 0) ≤
              dot2 ![-((u 1 - u 0) 1), (u 1 - u 0) 0] (v 1))
    (hsort2 : dot2 ![-((u 1 - u 0) 1), (u 1 - u 0) 0] (v 1) ≤
              dot2 ![-((u 1 - u 0) 1), (u 1 - u 0) 0] (v 2)) :
    ∃ (i0 : Fin 2) (j0 : Fin 3) (w : Fin 2 × Fin 3 → ℝ),
      w (i0, j0) = 0 ∧ (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∑ p, w p • (u p.1 + v p.2) = u i0 + v j0 := by
  set wv : R2 := u 1 - u 0
  set nv : R2 := ![-(wv 1), wv 0]
  have hww : 0 < wv 0 * wv 0 + wv 1 * wv 1 := by
    by_contra h
    push Not at h
    have h0 : wv 0 = 0 := by nlinarith
    have h1 : wv 1 = 0 := by nlinarith
    apply hw_ne
    ext k
    fin_cases k
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
  set n0 := dot2 nv (v 0)
  set n1 := dot2 nv (v 1)
  set n2 := dot2 nv (v 2)
  set lam : ℝ := if n2 = n0 then (1 : ℝ) / 2 else (n2 - n1) / (n2 - n0)
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    split_ifs with h
    · norm_num
    · have hlt : 0 < n2 - n0 := lt_of_le_of_ne (by linarith) (Ne.symm (sub_ne_zero.mpr h))
      exact div_nonneg (by linarith) hlt.le
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    split_ifs with h
    · norm_num
    · have hlt : 0 < n2 - n0 := lt_of_le_of_ne (by linarith) (Ne.symm (sub_ne_zero.mpr h))
      rw [div_le_one hlt]
      linarith
  set p : R2 := lam • v 0 + (1 - lam) • v 2
  have hnp : dot2 nv (v 1 - p) = 0 := by
    have hdot_p : dot2 nv p = lam * n0 + (1 - lam) * n2 := by
      simp [dot2, p, n0, n2]; ring
    have hsub : dot2 nv (v 1 - p) = n1 - dot2 nv p := by
      simp [dot2, n1]; ring
    rw [hsub, hdot_p]
    dsimp [lam]
    split_ifs with h
    · linarith
    · have hne : n2 - n0 ≠ 0 := sub_ne_zero.mpr h
      field_simp [hne]
      ring
  set t : ℝ := dot2 (v 1 - p) wv / (wv 0 * wv 0 + wv 1 * wv 1)
  have hv1 : v 1 - p = t • wv := by
    have hnp' : -(wv 1) * (v 1 0 - p 0) + wv 0 * (v 1 1 - p 1) = 0 := by
      simpa [dot2, nv] using hnp
    ext k
    fin_cases k
    · show v 1 0 - p 0 = dot2 (v 1 - p) wv / (wv 0 * wv 0 + wv 1 * wv 1) * wv 0
      rw [div_mul_eq_mul_div, eq_div_iff hww.ne']
      simp only [dot2, Pi.sub_apply]
      linear_combination -wv 1 * hnp'
    · show v 1 1 - p 1 = dot2 (v 1 - p) wv / (wv 0 * wv 0 + wv 1 * wv 1) * wv 1
      rw [div_mul_eq_mul_div, eq_div_iff hww.ne']
      simp only [dot2, Pi.sub_apply]
      linear_combination wv 0 * hnp'
  have h1lam : 0 ≤ 1 - lam := by linarith
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t ≤ 1
    · let w : Fin 2 × Fin 3 → ℝ := fun q ↦
        if q = (0, 0) then (1 - t) * lam
        else if q = (0, 2) then (1 - t) * (1 - lam)
        else if q = (1, 0) then t * lam
        else if q = (1, 2) then t * (1 - lam)
        else 0
      refine ⟨0, 1, w, by simp [w], ?_, ?_, ?_⟩
      · intro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> simp [w] <;> nlinarith
      · simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w]; ring
      · ext k
        have hvk := congrFun hv1 k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, p, wv, Pi.add_apply] at hvk
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
          Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w,
          Prod.mk.injEq, Fin.isValue, Fin.reduceEq, and_self, and_false, false_and, ↓reduceIte,
          zero_mul, add_zero]
        linarith
    · have ht_pos : 0 < t + 1 := by linarith
      let w : Fin 2 × Fin 3 → ℝ := fun q ↦
        if q = (0, 0) then lam / (t + 1)
        else if q = (0, 2) then (1 - lam) / (t + 1)
        else if q = (1, 1) then t / (t + 1)
        else 0
      refine ⟨0, 1, w, by simp [w], ?_, ?_, ?_⟩
      · intro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> simp [w]
        · exact div_nonneg hlam0 ht_pos.le
        · exact div_nonneg h1lam ht_pos.le
        · exact div_nonneg ht0 ht_pos.le
      · simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w]
        field_simp [ht_pos.ne']; ring
      · ext k
        have hvk := congrFun hv1 k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, p, wv, Pi.add_apply] at hvk
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
          Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w,
          Prod.mk.injEq, Fin.isValue, Fin.reduceEq, and_self, and_false, false_and, ↓reduceIte,
          zero_mul, add_zero, zero_add]
        field_simp [ht_pos.ne']
        linarith
  · push Not at ht0
    set s := -t
    have hs_pos : 0 < s := by linarith
    by_cases hs1 : s ≤ 1
    · let w : Fin 2 × Fin 3 → ℝ := fun q ↦
        if q = (0, 0) then s * lam
        else if q = (0, 2) then s * (1 - lam)
        else if q = (1, 0) then (1 - s) * lam
        else if q = (1, 2) then (1 - s) * (1 - lam)
        else 0
      refine ⟨1, 1, w, by simp [w], ?_, ?_, ?_⟩
      · intro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> simp [w] <;> nlinarith
      · simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w]; ring
      · ext k
        have hvk := congrFun hv1 k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, p, wv, Pi.add_apply] at hvk
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
          Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w,
          Prod.mk.injEq, Fin.isValue, Fin.reduceEq, and_self, and_false, false_and, ↓reduceIte,
          zero_mul, add_zero]
        dsimp [s]
        linarith
    · have hs1_pos : 0 < s + 1 := by linarith
      let w : Fin 2 × Fin 3 → ℝ := fun q ↦
        if q = (1, 0) then lam / (s + 1)
        else if q = (1, 2) then (1 - lam) / (s + 1)
        else if q = (0, 1) then s / (s + 1)
        else 0
      refine ⟨1, 1, w, by simp [w], ?_, ?_, ?_⟩
      · intro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> simp [w]
        · exact div_nonneg hs_pos.le hs1_pos.le
        · exact div_nonneg hlam0 hs1_pos.le
        · exact div_nonneg h1lam hs1_pos.le
      · simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w]
        field_simp [hs1_pos.ne']; ring
      · ext k
        have hvk := congrFun hv1 k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, p, wv, Pi.add_apply] at hvk
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
          Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, w,
          Prod.mk.injEq, Fin.isValue, Fin.reduceEq, and_self, and_false, false_and, ↓reduceIte,
          zero_mul, add_zero, zero_add]
        field_simp [hs1_pos.ne']
        dsimp [s]
        linarith

private lemma exists_perm_sort3 (f : Fin 3 → ℝ) :
    ∃ σ : Equiv.Perm (Fin 3), f (σ 0) ≤ f (σ 1) ∧ f (σ 1) ≤ f (σ 2) := by
  by_cases h01 : f 0 ≤ f 1
  · by_cases h12 : f 1 ≤ f 2
    · exact ⟨Equiv.refl _, h01, h12⟩
    · by_cases h02 : f 0 ≤ f 2
      · refine ⟨Equiv.swap (1 : Fin 3) 2, ?_, ?_⟩
        · change f 0 ≤ f 2; exact h02
        · change f 2 ≤ f 1; linarith
      · refine ⟨Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1, ?_, ?_⟩
        · change f 2 ≤ f 0; linarith
        · change f 0 ≤ f 1; exact h01
  · by_cases h02 : f 0 ≤ f 2
    · refine ⟨Equiv.swap (0 : Fin 3) 1, ?_, ?_⟩
      · change f 1 ≤ f 0; linarith
      · change f 0 ≤ f 2; exact h02
    · by_cases h12 : f 1 ≤ f 2
      · refine ⟨Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2, ?_, ?_⟩
        · change f 1 ≤ f 2; exact h12
        · change f 2 ≤ f 0; linarith
      · refine ⟨Equiv.swap (0 : Fin 3) 2, ?_, ?_⟩
        · change f 2 ≤ f 1; linarith
        · change f 1 ≤ f 0; linarith

private lemma exists_convex_comb_2x3_r2 (u : Fin 2 → R2) (v : Fin 3 → R2) :
    ∃ (i0 : Fin 2) (j0 : Fin 3) (w : Fin 2 × Fin 3 → ℝ),
      w (i0, j0) = 0 ∧ (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∑ p, w p • (u p.1 + v p.2) = u i0 + v j0 := by
  by_cases hEq : u 1 = u 0
  · refine ⟨0, 0, fun q ↦ if q = (1, 0) then 1 else 0, by simp, ?_, ?_, ?_⟩
    · intro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp
    · simp
    · simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, hEq]
  · set nv : R2 := ![-((u 1 - u 0) 1), (u 1 - u 0) 0]
    obtain ⟨σ, h1, h2⟩ := exists_perm_sort3 (fun j ↦ dot2 nv (v j))
    obtain ⟨i0, j0, w, hw0, hwn, hws, hcomb⟩ :=
      exists_convex_comb_2x3_r2_sorted u (v ∘ σ) hEq h1 h2
    refine ⟨i0, σ j0, fun p ↦ w (p.1, σ.symm p.2), by simp [hw0], fun p ↦ hwn _, ?_, ?_⟩
    · have : ∑ p : Fin 2 × Fin 3, w (p.1, σ.symm p.2) = ∑ p : Fin 2 × Fin 3, w p :=
        Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl _) σ.symm) _ _ (fun _ ↦ rfl)
      rw [this, hws]
    · have : ∑ p : Fin 2 × Fin 3, w (p.1, σ.symm p.2) • (u p.1 + v p.2) =
          ∑ p : Fin 2 × Fin 3, w p • (u p.1 + v (σ p.2)) :=
        Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl _) σ.symm) _ _ (fun p ↦ by
          simp [Equiv.prodCongr_apply, Prod.map])
      rw [this]
      exact hcomb

/-- No 2×3 grid in ℝ³ lying in a plane `{x | dot3 n x = 0}` (for `n ≠ 0`) can be shattered. -/
private lemma not_shatters_2x3_plane {C : Set R3} (hC : Convex ℝ C)
    {u : Fin 2 → R3} {v : Fin 3 → R3} (hS : ShattersGrid C u v)
    (n : R3) (hn : n ≠ 0)
    (hu : ∀ i, dot3 n (u i) = 0) (hv : ∀ j, dot3 n (v j) = 0) : False := by
  have hn_cases : n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hn; ext k; fin_cases k <;> simp [h]
  have lift_contra : ∀ (π : R3 → R2) (φ : R2 →ₗ[ℝ] R3),
      (∀ x, dot3 n x = 0 → φ (π x) = x) → False := by
    intro π φ hφ
    obtain ⟨i0, j0, w, hw0, hwn, hws, hcomb⟩ :=
      exists_convex_comb_2x3_r2 (fun i ↦ π (u i)) (fun j ↦ π (v j))
    apply hS.not_convex_comb hC i0 j0 w hw0 hwn hws
    have hmap := congrArg φ hcomb
    rw [map_sum, map_add, hφ _ (hu i0), hφ _ (hv j0)] at hmap
    convert hmap using 2 with p
    rw [map_smul, map_add, hφ _ (hu p.1), hφ _ (hv p.2)]
  rcases hn_cases with h0 | h1 | h2
  · refine lift_contra (fun x ↦ ![x 1, x 2])
      { toFun := fun z ↦ ![-(n 1 * z 0 + n 2 * z 1) / n 0, z 0, z 1]
        map_add' := fun a b ↦ by ext k; fin_cases k <;> simp; ring
        map_smul' := fun r a ↦ by ext k; fin_cases k <;> simp; ring } ?_
    intro x hx
    ext k; fin_cases k
    · show -(n 1 * x 1 + n 2 * x 2) / n 0 = x 0
      simp only [dot3] at hx; field_simp [h0]; linarith
    · rfl
    · rfl
  · refine lift_contra (fun x ↦ ![x 0, x 2])
      { toFun := fun z ↦ ![z 0, -(n 0 * z 0 + n 2 * z 1) / n 1, z 1]
        map_add' := fun a b ↦ by ext k; fin_cases k <;> simp; ring
        map_smul' := fun r a ↦ by ext k; fin_cases k <;> simp; ring } ?_
    intro x hx
    ext k; fin_cases k
    · rfl
    · show -(n 0 * x 0 + n 2 * x 2) / n 1 = x 1
      simp only [dot3] at hx; field_simp [h1]; linarith
    · rfl
  · refine lift_contra (fun x ↦ ![x 0, x 1])
      { toFun := fun z ↦ ![z 0, z 1, -(n 0 * z 0 + n 1 * z 1) / n 2]
        map_add' := fun a b ↦ by ext k; fin_cases k <;> simp; ring
        map_smul' := fun r a ↦ by ext k; fin_cases k <;> simp; ring } ?_
    intro x hx
    ext k; fin_cases k
    · rfl
    · rfl
    · show -(n 0 * x 0 + n 1 * x 1) / n 2 = x 2
      simp only [dot3] at hx; field_simp [h2]; linarith

/- ### Lemma 3: The 2-mask contradiction on Paraboloid Normal Form -/

private lemma paraboloid_contradiction {C : Set R3} (hC : Convex ℝ C)
    {a0 a2 b0 b2 c : ℝ} (ha0 : a0 < 0) (ha2 : 0 < a2) (hb0 : b0 < 0) (hb2 : 0 < b2) (hc : 0 < c)
    (hS : ShattersGrid C
      (![![a0, 0, 1], ![0, 0, 0], ![a2, 0, 1]] : Fin 3 → R3)
      (![![0, b0, c], ![0, 0, 0], ![0, b2, c]] : Fin 3 → R3)) : False := by
  set u : Fin 3 → R3 := ![![a0, 0, 1], ![0, 0, 0], ![a2, 0, 1]]
  set v : Fin 3 → R3 := ![![0, b0, c], ![0, 0, 0], ![0, b2, c]]
  obtain ⟨y, hy⟩ := hS
  let Mh : Set (Fin 3 × Fin 3) := {(1, 0), (1, 2)}ᶜ
  let Mv : Set (Fin 3 × Fin 3) := {(0, 1), (2, 1)}ᶜ
  set y1 := y Mh
  set y2 := y Mv
  set dx := y1 0 - y2 0
  set dy := y1 1 - y2 1
  set dz := y1 2 - y2 2
  set phi_a := if 0 ≤ dx then dx / a2 else dx / a0
  set psi_b := if 0 ≤ dy then -dy / b0 else -dy / b2
  have hphi_nn : 0 ≤ phi_a := by
    dsimp [phi_a]; split_ifs with h
    · exact div_nonneg h ha2.le
    · push Not at h; exact div_nonneg_of_nonpos h.le ha0.le
  have hpsi_nn : 0 ≤ psi_b := by
    dsimp [psi_b]; split_ifs with h
    · exact div_nonneg_of_nonpos (by linarith) hb0.le
    · push Not at h; exact div_nonneg (by linarith) hb2.le
  have hphi_ge_a2 : dx / a2 ≤ phi_a := by
    dsimp [phi_a]; split_ifs with h
    · exact le_rfl
    · push Not at h
      have h1 : dx / a2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h.le ha2.le
      have h2 : 0 ≤ dx / a0 := div_nonneg_of_nonpos h.le ha0.le
      linarith
  have hphi_ge_a0 : dx / a0 ≤ phi_a := by
    dsimp [phi_a]; split_ifs with h
    · have h1 : dx / a0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos h ha0.le
      have h2 : 0 ≤ dx / a2 := div_nonneg h ha2.le
      linarith
    · exact le_rfl
  have hpsi_ge_b0 : -dy / b0 ≤ psi_b := by
    dsimp [psi_b]; split_ifs with h
    · exact le_rfl
    · push Not at h
      have h1 : -dy / b0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hb0.le
      have h2 : 0 ≤ -dy / b2 := div_nonneg (by linarith) hb2.le
      linarith
  have hpsi_ge_b2 : -dy / b2 ≤ psi_b := by
    dsimp [psi_b]; split_ifs with h
    · have h1 : -dy / b2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hb2.le
      have h2 : 0 ≤ -dy / b0 := div_nonneg_of_nonpos (by linarith) hb0.le
      linarith
    · exact le_rfl
  have h_in1 : ∀ i j, (i, j) ≠ (1, 0) → (i, j) ≠ (1, 2) → y1 + u i + v j ∈ C :=
    fun i j h1 h2 ↦ (hy i j Mh).mpr (by simp [Mh, h1, h2])
  have h_in2 : ∀ i j, (i, j) ≠ (0, 1) → (i, j) ≠ (2, 1) → y2 + u i + v j ∈ C :=
    fun i j h1 h2 ↦ (hy i j Mv).mpr (by simp [Mv, h1, h2])
  have ha_diff : 0 < a2 - a0 := by linarith
  have hb_diff : 0 < b2 - b0 := by linarith
  by_cases hcase : phi_a - c * psi_b ≤ dz
  · set S := dz + c * psi_b
    have hS_a2 : dx / a2 ≤ S := by linarith
    have hS_a0 : dx / a0 ≤ S := by linarith
    set l1 := (a2 * S - dx) / (a2 - a0)
    set l2 := (dx - a0 * S) / (a2 - a0)
    set l3 := psi_b
    have hl1 : 0 ≤ l1 := by
      apply div_nonneg _ ha_diff.le
      have := (div_le_iff₀ ha2).mp hS_a2; linarith
    have hl2 : 0 ≤ l2 := by
      apply div_nonneg _ ha_diff.le
      have := (div_le_iff_of_neg ha0).mp hS_a0; linarith
    have hW : 0 < l1 + l2 + l3 + 1 := by linarith
    have hl12_x : l1 * a0 + l2 * a2 = dx := by
      dsimp [l1, l2]; field_simp [ha_diff.ne']; ring
    have hl12_z : l1 + l2 = dz + c * l3 := by
      dsimp [l1, l2, l3, S]; field_simp [ha_diff.ne']; ring
    by_cases hdy : 0 ≤ dy
    · have hl3_y : l3 * b0 = -dy := by
        have : l3 = -dy / b0 := by simp [l3, psi_b, hdy]
        rw [this]; exact div_mul_cancel₀ (-dy) hb0.ne
      have hmem : y1 + u 1 + v 0 ∈ C := by
        apply convex_combo4 hC
          (h_in1 0 0 (by decide) (by decide))
          (h_in1 2 0 (by decide) (by decide))
          (h_in1 1 1 (by decide) (by decide))
          (h_in2 1 0 (by decide) (by decide))
          hl1 hl2 hpsi_nn zero_le_one hW
        ext k; fin_cases k
        · show y1 0 + 0 + 0 = l1 / (l1 + l2 + l3 + 1) * (y1 0 + a0 + 0) +
            l2 / (l1 + l2 + l3 + 1) * (y1 0 + a2 + 0) +
            l3 / (l1 + l2 + l3 + 1) * (y1 0 + 0 + 0) +
            1 / (l1 + l2 + l3 + 1) * (y2 0 + 0 + 0)
          field_simp [hW.ne']; dsimp [dx] at hl12_x; linarith
        · show y1 1 + 0 + b0 = l1 / (l1 + l2 + l3 + 1) * (y1 1 + 0 + b0) +
            l2 / (l1 + l2 + l3 + 1) * (y1 1 + 0 + b0) +
            l3 / (l1 + l2 + l3 + 1) * (y1 1 + 0 + 0) +
            1 / (l1 + l2 + l3 + 1) * (y2 1 + 0 + b0)
          field_simp [hW.ne']; dsimp [dy] at hl3_y; linarith
        · show y1 2 + 0 + c = l1 / (l1 + l2 + l3 + 1) * (y1 2 + 1 + c) +
            l2 / (l1 + l2 + l3 + 1) * (y1 2 + 1 + c) +
            l3 / (l1 + l2 + l3 + 1) * (y1 2 + 0 + 0) +
            1 / (l1 + l2 + l3 + 1) * (y2 2 + 0 + c)
          field_simp [hW.ne']; dsimp [dz] at hl12_z; linarith
      exact ((hy 1 0 Mh).mp hmem) (by simp)
    · have hl3_y : l3 * b2 = -dy := by
        have : l3 = -dy / b2 := by simp [l3, psi_b, hdy]
        rw [this]; field_simp [hb2.ne']
      have hmem : y1 + u 1 + v 2 ∈ C := by
        apply convex_combo4 hC
          (h_in1 0 2 (by decide) (by decide))
          (h_in1 2 2 (by decide) (by decide))
          (h_in1 1 1 (by decide) (by decide))
          (h_in2 1 2 (by decide) (by decide))
          hl1 hl2 hpsi_nn zero_le_one hW
        ext k; fin_cases k
        · show y1 0 + 0 + 0 = l1 / (l1 + l2 + l3 + 1) * (y1 0 + a0 + 0) +
            l2 / (l1 + l2 + l3 + 1) * (y1 0 + a2 + 0) +
            l3 / (l1 + l2 + l3 + 1) * (y1 0 + 0 + 0) +
            1 / (l1 + l2 + l3 + 1) * (y2 0 + 0 + 0)
          field_simp [hW.ne']; dsimp [dx] at hl12_x; linarith
        · show y1 1 + 0 + b2 = l1 / (l1 + l2 + l3 + 1) * (y1 1 + 0 + b2) +
            l2 / (l1 + l2 + l3 + 1) * (y1 1 + 0 + b2) +
            l3 / (l1 + l2 + l3 + 1) * (y1 1 + 0 + 0) +
            1 / (l1 + l2 + l3 + 1) * (y2 1 + 0 + b2)
          field_simp [hW.ne']; dsimp [dy] at hl3_y; linarith
        · show y1 2 + 0 + c = l1 / (l1 + l2 + l3 + 1) * (y1 2 + 1 + c) +
            l2 / (l1 + l2 + l3 + 1) * (y1 2 + 1 + c) +
            l3 / (l1 + l2 + l3 + 1) * (y1 2 + 0 + 0) +
            1 / (l1 + l2 + l3 + 1) * (y2 2 + 0 + c)
          field_simp [hW.ne']; dsimp [dz] at hl12_z; linarith
      exact ((hy 1 2 Mh).mp hmem) (by simp)
  · push Not at hcase
    set T := (phi_a - dz) / c
    have hT_psi : psi_b ≤ T := by rw [le_div_iff₀ hc]; linarith
    have hT_b0 : -dy / b0 ≤ T := le_trans hpsi_ge_b0 hT_psi
    have hT_b2 : -dy / b2 ≤ T := le_trans hpsi_ge_b2 hT_psi
    set m1 := (b2 * T + dy) / (b2 - b0)
    set m2 := (-dy - b0 * T) / (b2 - b0)
    set m3 := phi_a
    have hm1 : 0 ≤ m1 := by
      apply div_nonneg _ hb_diff.le
      have := (div_le_iff₀ hb2).mp hT_b2; linarith
    have hm2 : 0 ≤ m2 := by
      apply div_nonneg _ hb_diff.le
      have := (div_le_iff_of_neg hb0).mp hT_b0; linarith
    have hW : 0 < m1 + m2 + m3 + 1 := by linarith
    have hm12_y : m1 * b0 + m2 * b2 = -dy := by
      dsimp [m1, m2]; field_simp [hb_diff.ne']; ring
    have hm12_z : (m1 + m2) * c = m3 - dz := by
      dsimp [m1, m2, m3, T]; field_simp [hb_diff.ne', hc.ne']; ring
    by_cases hdx : 0 ≤ dx
    · have hm3_x : m3 * a2 = dx := by
        have : m3 = dx / a2 := by simp [m3, phi_a, hdx]
        rw [this]; field_simp [ha2.ne']
      have hmem : y2 + u 2 + v 1 ∈ C := by
        apply convex_combo4 hC
          (h_in2 2 0 (by decide) (by decide))
          (h_in2 2 2 (by decide) (by decide))
          (h_in2 1 1 (by decide) (by decide))
          (h_in1 2 1 (by decide) (by decide))
          hm1 hm2 hphi_nn zero_le_one hW
        ext k; fin_cases k
        · show y2 0 + a2 + 0 = m1 / (m1 + m2 + m3 + 1) * (y2 0 + a2 + 0) +
            m2 / (m1 + m2 + m3 + 1) * (y2 0 + a2 + 0) +
            m3 / (m1 + m2 + m3 + 1) * (y2 0 + 0 + 0) +
            1 / (m1 + m2 + m3 + 1) * (y1 0 + a2 + 0)
          field_simp [hW.ne']; dsimp [dx] at hm3_x; linarith
        · show y2 1 + 0 + 0 = m1 / (m1 + m2 + m3 + 1) * (y2 1 + 0 + b0) +
            m2 / (m1 + m2 + m3 + 1) * (y2 1 + 0 + b2) +
            m3 / (m1 + m2 + m3 + 1) * (y2 1 + 0 + 0) +
            1 / (m1 + m2 + m3 + 1) * (y1 1 + 0 + 0)
          field_simp [hW.ne']; dsimp [dy] at hm12_y; linarith
        · show y2 2 + 1 + 0 = m1 / (m1 + m2 + m3 + 1) * (y2 2 + 1 + c) +
            m2 / (m1 + m2 + m3 + 1) * (y2 2 + 1 + c) +
            m3 / (m1 + m2 + m3 + 1) * (y2 2 + 0 + 0) +
            1 / (m1 + m2 + m3 + 1) * (y1 2 + 1 + 0)
          field_simp [hW.ne']; dsimp [dz] at hm12_z; linarith
      exact ((hy 2 1 Mv).mp hmem) (by simp)
    · have hm3_x : m3 * a0 = dx := by
        have : m3 = dx / a0 := by simp [m3, phi_a, hdx]
        rw [this]; exact div_mul_cancel₀ dx ha0.ne
      have hmem : y2 + u 0 + v 1 ∈ C := by
        apply convex_combo4 hC
          (h_in2 0 0 (by decide) (by decide))
          (h_in2 0 2 (by decide) (by decide))
          (h_in2 1 1 (by decide) (by decide))
          (h_in1 0 1 (by decide) (by decide))
          hm1 hm2 hphi_nn zero_le_one hW
        ext k; fin_cases k
        · show y2 0 + a0 + 0 = m1 / (m1 + m2 + m3 + 1) * (y2 0 + a0 + 0) +
            m2 / (m1 + m2 + m3 + 1) * (y2 0 + a0 + 0) +
            m3 / (m1 + m2 + m3 + 1) * (y2 0 + 0 + 0) +
            1 / (m1 + m2 + m3 + 1) * (y1 0 + a0 + 0)
          field_simp [hW.ne']; dsimp [dx] at hm3_x; linarith
        · show y2 1 + 0 + 0 = m1 / (m1 + m2 + m3 + 1) * (y2 1 + 0 + b0) +
            m2 / (m1 + m2 + m3 + 1) * (y2 1 + 0 + b2) +
            m3 / (m1 + m2 + m3 + 1) * (y2 1 + 0 + 0) +
            1 / (m1 + m2 + m3 + 1) * (y1 1 + 0 + 0)
          field_simp [hW.ne']; dsimp [dy] at hm12_y; linarith
        · show y2 2 + 1 + 0 = m1 / (m1 + m2 + m3 + 1) * (y2 2 + 1 + c) +
            m2 / (m1 + m2 + m3 + 1) * (y2 2 + 1 + c) +
            m3 / (m1 + m2 + m3 + 1) * (y2 2 + 0 + 0) +
            1 / (m1 + m2 + m3 + 1) * (y1 2 + 1 + 0)
          field_simp [hW.ne']; dsimp [dz] at hm12_z; linarith
      exact ((hy 0 1 Mv).mp hmem) (by simp)

/- ### Lemma 2: Reduction of any 3×3 grid in ℝ³ to Paraboloid Normal Form -/

private lemma cross3_ne_zero_of_shatters {C : Set R3} (hC : Convex ℝ C)
    {u' v' : Fin 3 → R3} (hS0 : ShattersGrid C u' v')
    (hu'1 : u' 1 = 0) (hv'1 : v' 1 = 0) : cross3 (u' 0) (u' 2) ≠ 0 := by
  intro h0
  have hcol : ∃ d : R3, (∀ i : Fin 3, ∃ t : ℝ, u' i = t • d) := by
    by_cases hu0 : u' 0 = 0
    · refine ⟨u' 2, fun i ↦ ?_⟩
      fin_cases i
      · exact ⟨0, by simp [hu0]⟩
      · exact ⟨0, by simp [hu'1]⟩
      · exact ⟨1, by simp⟩
    · refine ⟨u' 0, fun i ↦ ?_⟩
      fin_cases i
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hu'1]⟩
      · have hne : dot3 (u' 0) (u' 0) ≠ 0 := dot3_self_ne_zero hu0
        refine ⟨dot3 (u' 2) (u' 0) / dot3 (u' 0) (u' 0), ?_⟩
        have c0 : u' 0 1 * u' 2 2 - u' 0 2 * u' 2 1 = 0 := by simpa [cross3] using congrFun h0 0
        have c1 : u' 0 2 * u' 2 0 - u' 0 0 * u' 2 2 = 0 := by simpa [cross3] using congrFun h0 1
        have c2 : u' 0 0 * u' 2 1 - u' 0 1 * u' 2 0 = 0 := by simpa [cross3] using congrFun h0 2
        ext k; fin_cases k
        · show u' 2 0 = (dot3 (u' 2) (u' 0) / dot3 (u' 0) (u' 0)) * u' 0 0
          field_simp [hne]; simp only [dot3]; linear_combination u' 0 2 * c1 - u' 0 1 * c2
        · show u' 2 1 = (dot3 (u' 2) (u' 0) / dot3 (u' 0) (u' 0)) * u' 0 1
          field_simp [hne]; simp only [dot3]; linear_combination u' 0 0 * c2 - u' 0 2 * c0
        · show u' 2 2 = (dot3 (u' 2) (u' 0) / dot3 (u' 0) (u' 0)) * u' 0 2
          field_simp [hne]; simp only [dot3]; linear_combination u' 0 1 * c0 - u' 0 0 * c1
  obtain ⟨d, hd⟩ := hcol
  have hex_m : ∃ m : R3, m ≠ 0 ∧ dot3 m d = 0 ∧ dot3 m (v' 0) = 0 := by
    by_cases hdv : cross3 d (v' 0) ≠ 0
    · exact ⟨cross3 d (v' 0), hdv, cross3_self_dot_left d (v' 0), cross3_self_dot_right d (v' 0)⟩
    · push Not at hdv
      by_cases hd0 : d = 0
      · by_cases hv0 : v' 0 0 = 0 ∧ v' 0 1 = 0
        · exact ⟨![1, 0, 0], by intro h; simpa using congrFun h 0,
            by simp [dot3, hd0], by simp [dot3, hv0.1]⟩
        · refine ⟨![-(v' 0 1), v' 0 0, 0], ?_, by simp [dot3, hd0], by simp [dot3]; ring⟩
          intro h; have h0' := congrFun h 0; have h1' := congrFun h 1
          simp at h0' h1'; exact hv0 ⟨h1', h0'⟩
      · have hperp : ∃ m : R3, m ≠ 0 ∧ dot3 m d = 0 := by
          by_cases hxy : d 0 = 0 ∧ d 1 = 0
          · exact ⟨![1, 0, 0], by intro h; simpa using congrFun h 0, by simp [dot3, hxy.1]⟩
          · refine ⟨![-(d 1), d 0, 0], ?_, by simp [dot3]; ring⟩
            intro h; have h0' := congrFun h 0; have h1' := congrFun h 1
            simp at h0' h1'; exact hxy ⟨h1', h0'⟩
        obtain ⟨m, hm, hmd⟩ := hperp
        refine ⟨m, hm, hmd, ?_⟩
        have hmul := lagrange_dot_cross m d (v' 0) hmd hdv
        exact (mul_eq_zero.mp hmul).resolve_right (dot3_self_ne_zero hd0)
  obtain ⟨m, hm, hmd, hmv0⟩ := hex_m
  have hS23 := (hS0.comp_right (fun j : Fin 2 ↦ (j.castLE (by omega : 2 ≤ 3) : Fin 3))
    (Fin.castLE_injective (by omega : 2 ≤ 3))).swap
  apply not_shatters_2x3_plane hC hS23 m hm
  · intro j; fin_cases j
    · exact hmv0
    · simp [dot3, hv'1]
  · intro i
    obtain ⟨t, ht⟩ := hd i
    simp only [ht, dot3, Pi.smul_apply, smul_eq_mul]
    have : m 0 * (t * d 0) + m 1 * (t * d 1) + m 2 * (t * d 2) = t * dot3 m d := by
      simp [dot3]; ring
    rw [this, hmd, mul_zero]

private lemma scale_paraboloid_contradiction {C : Set R3} (hC : Convex ℝ C)
    {a0 a2 b0 b2 F G : ℝ}
    (ha0 : a0 < 0) (ha2 : 0 < a2) (hb0 : b0 < 0) (hb2 : 0 < b2)
    (hF_ne : F ≠ 0) (hFG_pos : 0 < F * G)
    (hS : ShattersGrid C
      (![![a0, 0, F], ![0, 0, 0], ![a2, 0, F]] : Fin 3 → R3)
      (![![0, b0, G], ![0, 0, 0], ![0, b2, G]] : Fin 3 → R3)) : False := by
  let Sc : R3 →ₗ[ℝ] R3 :=
    { toFun := fun x ↦ ![x 0, x 1, x 2 / F]
      map_add' := fun a b ↦ by ext k; fin_cases k <;> simp; ring
      map_smul' := fun r a ↦ by ext k; fin_cases k <;> simp; ring }
  have hSc_inj : Function.Injective Sc := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : x 0 = 0 := congrFun hx 0
    have h1 : x 1 = 0 := congrFun hx 1
    have h2 : x 2 / F = 0 := congrFun hx 2
    ext k; fin_cases k
    · exact h0
    · exact h1
    · show x 2 = 0; exact (div_eq_zero_iff.mp h2).resolve_right hF_ne
  have hC4 : Convex ℝ (Sc '' C) := hC.linear_image Sc
  have hS4 := hS.linear_image Sc hSc_inj
  have hU4_eq : (fun i ↦ Sc (![![a0, 0, F], ![0, 0, 0], ![a2, 0, F]] i)) =
      ![![a0, 0, 1], ![0, 0, 0], ![a2, 0, 1]] := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [Sc, div_self hF_ne]
  have hV4_eq : (fun j ↦ Sc (![![0, b0, G], ![0, 0, 0], ![0, b2, G]] j)) =
      ![![0, b0, G / F], ![0, 0, 0], ![0, b2, G / F]] := by
    ext j k; fin_cases j <;> fin_cases k <;> simp [Sc]
  rw [hU4_eq, hV4_eq] at hS4
  have hc_pos : 0 < G / F := by
    rcases lt_or_gt_of_ne hF_ne with hFn | hFp
    · exact div_pos_of_neg_of_neg (by nlinarith) hFn
    · exact div_pos (by nlinarith) hFp
  exact paraboloid_contradiction hC4 ha0 ha2 hb0 hb2 hc_pos hS4

private lemma shear_and_scale_contradiction {C : Set R3} (hC : Convex ℝ C)
    {a0 a2 b0 b2 f0 f2 g0 g2 : ℝ}
    (ha0 : a0 < 0) (ha2 : 0 < a2) (hb0 : b0 < 0) (hb2 : 0 < b2)
    (hS : ShattersGrid C
      (![![a0, 0, f0], ![0, 0, 0], ![a2, 0, f2]] : Fin 3 → R3)
      (![![0, b0, g0], ![0, 0, 0], ![0, b2, g2]] : Fin 3 → R3)) : False := by
  set sx := (f2 - f0) / (a2 - a0)
  set sy := (g2 - g0) / (b2 - b0)
  let Sh : R3 →ₗ[ℝ] R3 :=
    { toFun := fun x ↦ ![x 0, x 1, x 2 - sx * x 0 - sy * x 1]
      map_add' := fun a b ↦ by ext k; fin_cases k <;> simp; ring
      map_smul' := fun r a ↦ by ext k; fin_cases k <;> simp; ring }
  have hSh_inj : Function.Injective Sh := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : x 0 = 0 := congrFun hx 0
    have h1 : x 1 = 0 := congrFun hx 1
    have h2 : x 2 - sx * x 0 - sy * x 1 = 0 := congrFun hx 2
    ext k; fin_cases k
    · exact h0
    · exact h1
    · show x 2 = 0; rw [h0, h1] at h2; linarith
  have hC3 : Convex ℝ (Sh '' C) := hC.linear_image Sh
  have hS3 := hS.linear_image Sh hSh_inj
  set F := f0 - sx * a0
  set G := g0 - sy * b0
  have hF_eq : f2 - sx * a2 = F := by
    dsimp [F, sx]; have hne : a2 - a0 ≠ 0 := by linarith
    field_simp [hne]; ring
  have hG_eq : g2 - sy * b2 = G := by
    dsimp [G, sy]; have hne : b2 - b0 ≠ 0 := by linarith
    field_simp [hne]; ring
  have hU3_eq : (fun i ↦ Sh (![![a0, 0, f0], ![0, 0, 0], ![a2, 0, f2]] i)) =
      ![![a0, 0, F], ![0, 0, 0], ![a2, 0, F]] := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [Sh, F, hF_eq]
  have hV3_eq : (fun j ↦ Sh (![![0, b0, g0], ![0, 0, 0], ![0, b2, g2]] j)) =
      ![![0, b0, G], ![0, 0, 0], ![0, b2, G]] := by
    ext j k; fin_cases j <;> fin_cases k <;> simp [Sh, G, hG_eq]
  rw [hU3_eq, hV3_eq] at hS3
  have hF_ne : F ≠ 0 := by
    intro h0
    have h23 := (hS3.comp_right (fun j : Fin 2 ↦ (j.castLE (by omega : 2 ≤ 3) : Fin 3))
      (Fin.castLE_injective (by omega : 2 ≤ 3))).swap
    apply not_shatters_2x3_plane hC3 h23 ![0, G, -b0]
      (by intro h; have := congrFun h 2; simp at this; linarith)
    · intro j; fin_cases j <;> simp [dot3]; ring
    · intro i; fin_cases i <;> simp [dot3, h0]
  have hG_ne : G ≠ 0 := by
    intro h0
    have h23 := hS3.comp_left (fun i : Fin 2 ↦ (i.castLE (by omega : 2 ≤ 3) : Fin 3))
      (Fin.castLE_injective (by omega : 2 ≤ 3))
    apply not_shatters_2x3_plane hC3 h23 ![F, 0, -a0]
      (by intro h; have := congrFun h 2; simp at this; linarith)
    · intro i; fin_cases i <;> simp [dot3]; ring
    · intro j; fin_cases j <;> simp [dot3, h0]
  have hFG_pos : 0 < F * G := by
    by_contra hle
    push Not at hle
    have hFG_neg : F * G < 0 := lt_of_le_of_ne hle (mul_ne_zero hF_ne hG_ne)
    have hFG_ne : F - G ≠ 0 := by
      intro hEq; have : F = G := sub_eq_zero.mp hEq; rw [this] at hFG_neg; nlinarith
    set lam := a2 / (a2 - a0)
    set mu := b2 / (b2 - b0)
    set t := (-G) / (F - G)
    have hlam0 : 0 ≤ lam := div_nonneg ha2.le (by linarith)
    have hlam1 : lam ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hmu0 : 0 ≤ mu := div_nonneg hb2.le (by linarith)
    have hmu1 : mu ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have ht0 : 0 ≤ t := by
      dsimp [t]
      rcases lt_or_gt_of_ne hF_ne with hFn | hFp
      · have hGp : 0 < G := by nlinarith
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
      · have hGn : G < 0 := by nlinarith
        exact div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rcases lt_or_gt_of_ne hF_ne with hFn | hFp
      · have hGp : 0 < G := by nlinarith
        rw [div_le_one_of_neg (by linarith)]; linarith
      · have hGn : G < 0 := by nlinarith
        rw [div_le_one (by linarith)]; linarith
    obtain ⟨y, hy⟩ := hS3
    let s : Set (Fin 3 × Fin 3) := {(1, 1)}ᶜ
    have hW1 : t * lam + t * (1 - lam) + (1 - t) * mu + (1 - t) * (1 - mu) = 1 := by ring
    have hWpos : 0 < t * lam + t * (1 - lam) + (1 - t) * mu + (1 - t) * (1 - mu) := by linarith
    have hmem : y s + (![![a0, 0, F], ![0, 0, 0], ![a2, 0, F]] : Fin 3 → R3) 1 +
        (![![0, b0, G], ![0, 0, 0], ![0, b2, G]] : Fin 3 → R3) 1 ∈ Sh '' C := by
      apply convex_combo4 hC3
        ((hy 0 1 s).mpr (by decide))
        ((hy 2 1 s).mpr (by decide))
        ((hy 1 0 s).mpr (by decide))
        ((hy 1 2 s).mpr (by decide))
        (mul_nonneg ht0 hlam0) (mul_nonneg ht0 (by linarith))
        (mul_nonneg (by linarith) hmu0) (mul_nonneg (by linarith) (by linarith)) hWpos
      rw [hW1]
      ext k; fin_cases k
      · show y s 0 + 0 + 0 = (t * lam) / 1 * (y s 0 + a0 + 0) +
          (t * (1 - lam)) / 1 * (y s 0 + a2 + 0) +
          ((1 - t) * mu) / 1 * (y s 0 + 0 + 0) +
          ((1 - t) * (1 - mu)) / 1 * (y s 0 + 0 + 0)
        dsimp [lam]
        have hne : a2 - a0 ≠ 0 := by linarith
        field_simp [hne]
        ring
      · show y s 1 + 0 + 0 = (t * lam) / 1 * (y s 1 + 0 + 0) +
          (t * (1 - lam)) / 1 * (y s 1 + 0 + 0) +
          ((1 - t) * mu) / 1 * (y s 1 + 0 + b0) +
          ((1 - t) * (1 - mu)) / 1 * (y s 1 + 0 + b2)
        dsimp [mu]
        have hne : b2 - b0 ≠ 0 := by linarith
        field_simp [hne]
        ring
      · show y s 2 + 0 + 0 = (t * lam) / 1 * (y s 2 + F + 0) +
          (t * (1 - lam)) / 1 * (y s 2 + F + 0) +
          ((1 - t) * mu) / 1 * (y s 2 + 0 + G) +
          ((1 - t) * (1 - mu)) / 1 * (y s 2 + 0 + G)
        dsimp [t, lam, mu]
        have ha : a2 - a0 ≠ 0 := by linarith
        have hb : b2 - b0 ≠ 0 := by linarith
        field_simp [hFG_ne, ha, hb]; ring
    exact ((hy 1 1 s).mp hmem) rfl
  exact scale_paraboloid_contradiction hC3 ha0 ha2 hb0 hb2 hF_ne hFG_pos hS3

private lemma not_shatters_3x3_r3 {C : Set R3} (hC : Convex ℝ C)
    (u v : Fin 3 → R3) (hS : ShattersGrid C u v) : False := by
  have hS0 := hS.translate (-u 1) (-v 1)
  set u' : Fin 3 → R3 := fun i ↦ u i + (-u 1)
  set v' : Fin 3 → R3 := fun j ↦ v j + (-v 1)
  have hu'1 : u' 1 = 0 := by simp [u']
  have hv'1 : v' 1 = 0 := by simp [v']
  set nU := cross3 (u' 0) (u' 2)
  set nV := cross3 (v' 0) (v' 2)
  have hnU : nU ≠ 0 := cross3_ne_zero_of_shatters hC hS0 hu'1 hv'1
  have hnV : nV ≠ 0 := cross3_ne_zero_of_shatters hC hS0.swap hv'1 hu'1
  set e3 := cross3 nU nV
  have he3 : e3 ≠ 0 := by
    intro h0
    have hS23 := hS0.comp_left (fun i : Fin 2 ↦ (i.castLE (by omega : 2 ≤ 3) : Fin 3))
      (Fin.castLE_injective (by omega : 2 ≤ 3))
    apply not_shatters_2x3_plane hC hS23 nU hnU
    · intro i; fin_cases i
      · exact cross3_self_dot_left (u' 0) (u' 2)
      · simp [dot3, hu'1]
    · intro j
      have hdot_nV : dot3 nV (v' j) = 0 := by
        fin_cases j
        · exact cross3_self_dot_left (v' 0) (v' 2)
        · simp [dot3, hv'1]
        · exact cross3_self_dot_right (v' 0) (v' 2)
      have hcross_comm : cross3 nV nU = 0 := by
        have c0 : nU 1 * nV 2 - nU 2 * nV 1 = 0 := by simpa [e3, cross3] using congrFun h0 0
        have c1 : nU 2 * nV 0 - nU 0 * nV 2 = 0 := by simpa [e3, cross3] using congrFun h0 1
        have c2 : nU 0 * nV 1 - nU 1 * nV 0 = 0 := by simpa [e3, cross3] using congrFun h0 2
        ext k; fin_cases k
        · show nV 1 * nU 2 - nV 2 * nU 1 = 0; linarith
        · show nV 2 * nU 0 - nV 0 * nU 2 = 0; linarith
        · show nV 0 * nU 1 - nV 1 * nU 0 = 0; linarith
      have hmul := lagrange_dot_cross (v' j) nV nU
        (by rw [show dot3 (v' j) nV = dot3 nV (v' j) by simp [dot3]; ring]; exact hdot_nV)
        hcross_comm
      have hdot_sym : dot3 nU (v' j) = dot3 (v' j) nU := by simp [dot3]; ring
      rw [hdot_sym]
      exact (mul_eq_zero.mp hmul).resolve_right (dot3_self_ne_zero hnV)
  let L : R3 →ₗ[ℝ] R3 :=
    { toFun := fun x ↦ ![dot3 nV x, dot3 nU x, dot3 e3 x]
      map_add' := fun a b ↦ by ext k; fin_cases k <;> simp [dot3] <;> ring
      map_smul' := fun r a ↦ by ext k; fin_cases k <;> simp [dot3] <;> ring }
  have hL_inj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact cross3_orthog_eq_zero nU nV x (congrFun hx 0) (congrFun hx 1) (congrFun hx 2) he3
  have hC1 : Convex ℝ (L '' C) := hC.linear_image L
  have hS1 := hS0.linear_image L hL_inj
  set U1 : Fin 3 → R3 := fun i ↦ L (u' i)
  set V1 : Fin 3 → R3 := fun j ↦ L (v' j)
  have hU1_y : ∀ i, U1 i 1 = 0 := by
    intro i; fin_cases i
    · exact cross3_self_dot_left (u' 0) (u' 2)
    · simp [U1, L, dot3, hu'1]
    · exact cross3_self_dot_right (u' 0) (u' 2)
  have hV1_x : ∀ j, V1 j 0 = 0 := by
    intro j; fin_cases j
    · exact cross3_self_dot_left (v' 0) (v' 2)
    · simp [V1, L, dot3, hv'1]
    · exact cross3_self_dot_right (v' 0) (v' 2)
  obtain ⟨σU, hU01, hU12⟩ := exists_perm_sort3 (fun i ↦ U1 i 0)
  obtain ⟨σV, hV01, hV12⟩ := exists_perm_sort3 (fun j ↦ V1 j 1)
  have hS2 := ((hS1.comp_left σU σU.injective).comp_right σV σV.injective).translate
    (-(U1 (σU 1))) (-(V1 (σV 1)))
  set U2 : Fin 3 → R3 := fun i ↦ (U1 ∘ σU) i + (-(U1 (σU 1)))
  set V2 : Fin 3 → R3 := fun j ↦ (V1 ∘ σV) j + (-(V1 (σV 1)))
  have hU2_1 : U2 1 = 0 := by simp [U2]
  have hV2_1 : V2 1 = 0 := by simp [V2]
  have hU2_y : ∀ i, U2 i 1 = 0 := fun i ↦ by simp [U2, hU1_y]
  have hV2_x : ∀ j, V2 j 0 = 0 := fun j ↦ by simp [V2, hV1_x]
  have ha0 : U2 0 0 < 0 := by
    have hle : U2 0 0 ≤ 0 := by simp [U2]; linarith
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have h23 := hS2.comp_left (fun i : Fin 2 ↦ (i.castLE (by omega : 2 ≤ 3) : Fin 3)) (Fin.castLE_injective (by omega : 2 ≤ 3))
    apply not_shatters_2x3_plane hC1 h23 ![1, 0, 0] (by intro h; simpa using congrFun h 0)
    · intro i; fin_cases i
      · show dot3 ![1, 0, 0] (U2 0) = 0; simp [dot3, hEq]
      · show dot3 ![1, 0, 0] (U2 1) = 0; simp [dot3, hU2_1]
    · intro j; show dot3 ![1, 0, 0] (V2 j) = 0; simp [dot3, hV2_x]
  have ha2 : 0 < U2 2 0 := by
    have hle : 0 ≤ U2 2 0 := by simp [U2]; linarith
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have h23 := hS2.comp_left (fun i : Fin 2 ↦ if i = 0 then (1 : Fin 3) else 2)
      (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
    apply not_shatters_2x3_plane hC1 h23 ![1, 0, 0] (by intro h; simpa using congrFun h 0)
    · intro i; fin_cases i
      · show dot3 ![1, 0, 0] (U2 1) = 0; simp [dot3, hU2_1]
      · show dot3 ![1, 0, 0] (U2 2) = 0; simp [dot3, ← hEq]
    · intro j; show dot3 ![1, 0, 0] (V2 j) = 0; simp [dot3, hV2_x]
  have hb0 : V2 0 1 < 0 := by
    have hle : V2 0 1 ≤ 0 := by simp [V2]; linarith
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have h23 := (hS2.comp_right (fun j : Fin 2 ↦ (j.castLE (by omega : 2 ≤ 3) : Fin 3))
      (Fin.castLE_injective (by omega : 2 ≤ 3))).swap
    apply not_shatters_2x3_plane hC1 h23 ![0, 1, 0] (by intro h; simpa using congrFun h 1)
    · intro j; fin_cases j
      · show dot3 ![0, 1, 0] (V2 0) = 0; simp [dot3, hEq]
      · show dot3 ![0, 1, 0] (V2 1) = 0; simp [dot3, hV2_1]
    · intro i; show dot3 ![0, 1, 0] (U2 i) = 0; simp [dot3, hU2_y]
  have hb2 : 0 < V2 2 1 := by
    have hle : 0 ≤ V2 2 1 := by simp [V2]; linarith
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have h23 := (hS2.comp_right (fun j : Fin 2 ↦ if j = 0 then (1 : Fin 3) else 2)
      (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)).swap
    apply not_shatters_2x3_plane hC1 h23 ![0, 1, 0] (by intro h; simpa using congrFun h 1)
    · intro j; fin_cases j
      · show dot3 ![0, 1, 0] (V2 1) = 0; simp [dot3, hV2_1]
      · show dot3 ![0, 1, 0] (V2 2) = 0; simp [dot3, ← hEq]
    · intro i; show dot3 ![0, 1, 0] (U2 i) = 0; simp [dot3, hU2_y]
  have hU2_eq : U2 = ![![U2 0 0, 0, U2 0 2], ![0, 0, 0], ![U2 2 0, 0, U2 2 2]] := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [hU2_1, hU2_y]
  have hV2_eq : V2 = ![![0, V2 0 1, V2 0 2], ![0, 0, 0], ![0, V2 2 1, V2 2 2]] := by
    ext j k; fin_cases j <;> fin_cases k <;> simp [hV2_1, hV2_x]
  have hS2' : ShattersGrid (L '' C)
      (![![U2 0 0, 0, U2 0 2], ![0, 0, 0], ![U2 2 0, 0, U2 2 2]] : Fin 3 → R3)
      (![![0, V2 0 1, V2 0 2], ![0, 0, 0], ![0, V2 2 1, V2 2 2]] : Fin 3 → R3) := by
    rw [← hU2_eq, ← hV2_eq]; exact hS2
  exact shear_and_scale_contradiction hC1 ha0 ha2 hb0 hb2 hS2'

/-- Every convex set in $\mathbb{R}^3$ has additive $\mathrm{VC}_2$ dimension at most $2$. -/
theorem hasAddVCNDimAtMost_two_two_of_convex_r3
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C 2 2 := by
  intro x y hxy
  let e : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] R3 := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hC' : Convex ℝ (e '' C) := hC.linear_image e.toLinearMap
  have hS : ShattersGrid (e '' C) (fun i ↦ e (x 0 i)) (fun j ↦ e (x 1 j)) := by
    refine ⟨fun s ↦ e (y ((fun p : Fin 3 × Fin 3 ↦ ![p.1, p.2]) '' s)), fun i j s ↦ ?_⟩
    have hsum : e (y ((fun p : Fin 3 × Fin 3 ↦ ![p.1, p.2]) '' s)) + e (x 0 i) + e (x 1 j) =
        e (y ((fun p : Fin 3 × Fin 3 ↦ ![p.1, p.2]) '' s) + ∑ k : Fin 2, x k (![i, j] k)) := by
      simp [Fin.sum_univ_two, map_add, add_assoc]
    rw [hsum, e.injective.mem_set_image, hxy ![i, j]]
    constructor
    · rintro ⟨⟨i', j'⟩, hmem, hEq⟩
      have hi : i' = i := congrFun hEq 0
      have hj : j' = j := congrFun hEq 1
      rw [hi, hj] at hmem
      exact hmem
    · intro hmem
      exact ⟨(i, j), hmem, rfl⟩
  exact not_shatters_3x3_r3 hC' _ _ hS

end VCDimConvex

#print axioms VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3
