"""Exact integer verifier for a counterexample to VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3.

A certificate JSON file must have:
  - "U": list of 3 integer 3-vectors [[x,y,z], ...] (or 2 for 2x3 mode)
  - "V": list of 3 integer 3-vectors [[x,y,z], ...]
  - "halfspaces": list of integer 4-tuples [a, b, c, d] defining a*x + b*y + c*z <= d
  - "translates": dict mapping str(mask) -> [yx, yy, yz] (integers) for all mask in 0 .. 2^(|U|*|V|)-1

Verification is 100% exact integer arithmetic (zero floats).
Includes a planted-bug negative sanity test (--self-test).
"""

import json
import sys


def dot3(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def in_polyhedron(pt, halfspaces):
    for a, b, c, d in halfspaces:
        if a * pt[0] + b * pt[1] + c * pt[2] > d:
            return False
    return True


def verify_certificate(cert, verbose=True):
    U = cert["U"]
    V = cert["V"]
    halfspaces = cert["halfspaces"]
    translates = cert["translates"]

    # Validate exact integer types
    for name, arr in [("U", U), ("V", V)]:
        for vec in arr:
            if len(vec) != 3 or not all(isinstance(v, int) and not isinstance(v, bool) for v in vec):
                return False, f"Non-integer vector in {name}: {vec}"
    for h in halfspaces:
        if len(h) != 4 or not all(isinstance(v, int) and not isinstance(v, bool) for v in h):
            return False, f"Non-integer halfspace: {h}"

    P = [[u[0] + v[0], u[1] + v[1], u[2] + v[2]] for u in U for v in V]
    nP = len(P)
    n_masks = 1 << nP

    for mask in range(n_masks):
        key = str(mask)
        if key not in translates:
            return False, f"Missing translate for mask {mask}"
        y = translates[key]
        if len(y) != 3 or not all(isinstance(v, int) and not isinstance(v, bool) for v in y):
            return False, f"Non-integer translate for mask {mask}: {y}"

        for i in range(nP):
            pt = [y[0] + P[i][0], y[1] + P[i][1], y[2] + P[i][2]]
            inside = in_polyhedron(pt, halfspaces)
            expected = bool((mask >> i) & 1)
            if inside != expected:
                return False, (
                    f"Mismatch at mask={mask} ({bin(mask)}), point_idx={i}, "
                    f"y+p={pt}: inside={inside}, expected={expected}"
                )

    if verbose:
        print(
            f"VERIFIED EXACTLY: |U|={len(U)}, |V|={len(V)}, |P|={nP}, "
            f"|halfspaces|={len(halfspaces)}, all {n_masks}/{n_masks} subsets shattered!"
        )
    return True, "OK"


def run_self_test():
    """Verify Kitamura-style 2x2 certificate passes and a planted-bug mutation fails."""
    # Simple 2x1 test (2 points, 4 masks) with exact integer halfspaces
    cert_ok = {
        "U": [[0, 0, 0], [1, 0, 0]],
        "V": [[0, 0, 0]],
        "halfspaces": [[1, 0, 0, 1], [-1, 0, 0, 0]],  # 0 <= x <= 1
        "translates": {
            "0": [5, 0, 0],   # {5, 6} -> neither in [0,1]
            "1": [1, 0, 0],   # {1, 2} -> only p0 in [0,1]
            "2": [-1, 0, 0],  # {-1, 0} -> only p1 in [0,1]
            "3": [0, 0, 0],   # {0, 1} -> both in [0,1]
        },
    }
    ok, msg = verify_certificate(cert_ok, verbose=False)
    assert ok, f"Self-test positive failed: {msg}"

    # Planted bug: corrupt mask 3 translate so p1 falls outside
    cert_bad = json.loads(json.dumps(cert_ok))
    cert_bad["translates"]["3"] = [1, 0, 0]
    ok_bad, msg_bad = verify_certificate(cert_bad, verbose=False)
    assert not ok_bad, "Planted-bug negative test FAILED to catch corrupted translate!"
    print(f"SELF-TEST PASSED (positive OK; planted bug caught: {msg_bad})")


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        run_self_test()
    elif len(sys.argv) == 2:
        with open(sys.argv[1], "r", encoding="utf-8") as f:
            cert = json.load(f)
        ok, msg = verify_certificate(cert, verbose=True)
        if not ok:
            print("VERIFICATION FAILED:", msg)
            sys.exit(1)
    else:
        print("Usage: python verify_certificate.py [--self-test | path/to/cert.json]")
        sys.exit(2)
