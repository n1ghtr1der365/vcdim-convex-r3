"""Exhaustive numerical verification of the elementary proof of VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3.

Checks:
1. Lemma 1: Explicit 3/4-point convex combination showing no 2x3 additive grid in R^2
   is in convex position (10,000 random 2D grids).
2. Lemma 3: Explicit 4-point convex combination identities across 100,000 random
   paraboloid grids (a0 < 0 < a2, b0 < 0 < b2, c > 0) and random translate differences d = y1 - y2.
"""

import numpy as np


def verify_lemma1(n_trials=10_000, seed=0):
    rng = np.random.default_rng(seed)
    max_err = 0.0
    counts = {"t_in_01": 0, "t_gt_1": 0, "s_in_01": 0, "s_gt_1": 0}

    for _ in range(n_trials):
        u0 = rng.normal(0.0, 10.0, size=2)
        u1 = rng.normal(0.0, 10.0, size=2)
        w = u1 - u0
        if np.dot(w, w) < 1e-12:
            continue
        nv = np.array([-w[1], w[0]])
        V = [rng.normal(0.0, 10.0, size=2) for _ in range(3)]
        V.sort(key=lambda v: float(np.dot(nv, v)))
        n0, n1, n2 = [float(np.dot(nv, v)) for v in V]
        lam = 0.5 if abs(n2 - n0) < 1e-15 else (n2 - n1) / (n2 - n0)
        assert -1e-12 <= lam <= 1.0 + 1e-12
        p = lam * V[0] + (1.0 - lam) * V[2]
        t = float(np.dot(V[1] - p, w) / np.dot(w, w))
        P = [[u + v for v in V] for u in (u0, u1)]

        if t >= 0.0:
            if t <= 1.0:
                counts["t_in_01"] += 1
                ws = np.array([(1 - t) * lam, (1 - t) * (1 - lam), t * lam, t * (1 - lam)])
                pts = [P[0][0], P[0][2], P[1][0], P[1][2]]
                target = P[0][1]
            else:
                counts["t_gt_1"] += 1
                ws = np.array([lam / (t + 1), (1 - lam) / (t + 1), t / (t + 1)])
                pts = [P[0][0], P[0][2], P[1][1]]
                target = P[0][1]
        else:
            s = -t
            if s <= 1.0:
                counts["s_in_01"] += 1
                ws = np.array([s * lam, s * (1 - lam), (1 - s) * lam, (1 - s) * (1 - lam)])
                pts = [P[0][0], P[0][2], P[1][0], P[1][2]]
                target = P[1][1]
            else:
                counts["s_gt_1"] += 1
                ws = np.array([lam / (s + 1), (1 - lam) / (s + 1), s / (s + 1)])
                pts = [P[1][0], P[1][2], P[0][1]]
                target = P[1][1]

        assert np.all(ws >= -1e-12) and abs(np.sum(ws) - 1.0) < 1e-12
        comb = sum(wi * pt for wi, pt in zip(ws, pts))
        err = float(np.linalg.norm(comb - target))
        if err > max_err:
            max_err = err

    print(f"LEMMA 1 VERIFIED ({n_trials:,} random 2D 2x3 grids)! max_err = {max_err:.3e}, case_counts = {counts}")
    assert max_err < 1e-10


def verify_main_lemma(n_trials=100_000, seed=0):
    rng = np.random.default_rng(seed)
    max_err = 0.0
    counts = {"A1": 0, "A2": 0, "B1": 0, "B2": 0}

    for _ in range(n_trials):
        a0 = -rng.uniform(0.05, 10.0)
        a2 = rng.uniform(0.05, 10.0)
        b0 = -rng.uniform(0.05, 10.0)
        b2 = rng.uniform(0.05, 10.0)
        c = rng.uniform(0.05, 10.0)

        y1 = rng.normal(0.0, 10.0, size=3)
        y2 = rng.normal(0.0, 10.0, size=3)
        dx, dy, dz = y1 - y2

        # Grid points p_{i,j} = u_i + v_j
        U = [np.array([a0, 0.0, 1.0]), np.array([0.0, 0.0, 0.0]), np.array([a2, 0.0, 1.0])]
        V = [np.array([0.0, b0, c]), np.array([0.0, 0.0, 0.0]), np.array([0.0, b2, c])]
        P = [[U[i] + V[j] for j in range(3)] for i in range(3)]

        phi_a = dx / a2 if dx >= 0.0 else dx / a0
        psi_b = -dy / b0 if dy >= 0.0 else -dy / b2
        assert phi_a >= -1e-12 and psi_b >= -1e-12

        if dz >= phi_a - c * psi_b:
            if dy >= 0.0:
                counts["A1"] += 1
                # Target: y1 + P[1][0] in conv(y1+P[0][0], y1+P[2][0], y1+P[1][1], y2+P[1][0])
                l3 = -dy / b0
                l1 = (a2 * (dz + c * l3) - dx) / (a2 - a0)
                l2 = (dx - a0 * (dz + c * l3)) / (a2 - a0)
                l4 = 1.0
                ws = np.array([l1, l2, l3, l4])
                assert np.all(ws >= -1e-11), f"Negative weight in A1: {ws}"
                ws = np.maximum(ws, 0.0)
                ws /= np.sum(ws)
                pts = [y1 + P[0][0], y1 + P[2][0], y1 + P[1][1], y2 + P[1][0]]
                comb = sum(w * pt for w, pt in zip(ws, pts))
                err = float(np.linalg.norm(comb - (y1 + P[1][0])))
            else:
                counts["A2"] += 1
                # Target: y1 + P[1][2] in conv(y1+P[0][2], y1+P[2][2], y1+P[1][1], y2+P[1][2])
                l3 = -dy / b2
                l1 = (a2 * (dz + c * l3) - dx) / (a2 - a0)
                l2 = (dx - a0 * (dz + c * l3)) / (a2 - a0)
                l4 = 1.0
                ws = np.array([l1, l2, l3, l4])
                assert np.all(ws >= -1e-11), f"Negative weight in A2: {ws}"
                ws = np.maximum(ws, 0.0)
                ws /= np.sum(ws)
                pts = [y1 + P[0][2], y1 + P[2][2], y1 + P[1][1], y2 + P[1][2]]
                comb = sum(w * pt for w, pt in zip(ws, pts))
                err = float(np.linalg.norm(comb - (y1 + P[1][2])))
        else:
            if dx >= 0.0:
                counts["B1"] += 1
                # Target: y2 + P[2][1] in conv(y2+P[2][0], y2+P[2][2], y2+P[1][1], y1+P[2][1])
                m3 = dx / a2
                m1 = (b2 * (m3 - dz) / c + dy) / (b2 - b0)
                m2 = (-dy - b0 * (m3 - dz) / c) / (b2 - b0)
                m4 = 1.0
                ws = np.array([m1, m2, m3, m4])
                assert np.all(ws >= -1e-11), f"Negative weight in B1: {ws}"
                ws = np.maximum(ws, 0.0)
                ws /= np.sum(ws)
                pts = [y2 + P[2][0], y2 + P[2][2], y2 + P[1][1], y1 + P[2][1]]
                comb = sum(w * pt for w, pt in zip(ws, pts))
                err = float(np.linalg.norm(comb - (y2 + P[2][1])))
            else:
                counts["B2"] += 1
                # Target: y2 + P[0][1] in conv(y2+P[0][0], y2+P[0][2], y2+P[1][1], y1+P[0][1])
                m3 = dx / a0
                m1 = (b2 * (m3 - dz) / c + dy) / (b2 - b0)
                m2 = (-dy - b0 * (m3 - dz) / c) / (b2 - b0)
                m4 = 1.0
                ws = np.array([m1, m2, m3, m4])
                assert np.all(ws >= -1e-11), f"Negative weight in B2: {ws}"
                ws = np.maximum(ws, 0.0)
                ws /= np.sum(ws)
                pts = [y2 + P[0][0], y2 + P[0][2], y2 + P[1][1], y1 + P[0][1]]
                comb = sum(w * pt for w, pt in zip(ws, pts))
                err = float(np.linalg.norm(comb - (y2 + P[0][1])))

        if err > max_err:
            max_err = err

    print(f"VERIFIED {n_trials:,} RANDOM TRIALS! max_err = {max_err:.3e}, case_counts = {counts}")
    assert max_err < 1e-10


if __name__ == "__main__":
    verify_lemma1()
    verify_main_lemma()
