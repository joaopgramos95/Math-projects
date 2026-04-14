#!/usr/bin/env python3
"""Ball-arithmetic verifier for the local Bessel gap.

This is the first rigorous replacement for the floating computation in
``circle_gap_steps_1_3.py``.  It uses python-flint/Arb balls to enclose

    J_n = int_0^infty J_0(r)^4 J_n(r)^2 r dr

for finitely many n.  The finite interval [0,R] is enclosed by interval
Riemann sums: on each subinterval I, Arb evaluates the integrand on the ball
I and we add |I| * range(f(I)).  The infinite r-tail uses the elementary
asymptotic majorant recorded below; this should eventually be replaced by
the sharper Thiele-style Bessel product estimates used elsewhere in the
project, but it is already enough to test the local gap target.

Important: this script certifies only the finite list 2 <= n <= nmax.  A full
proof of nu_0 >= 0.4 Lambda_0 also needs the separate large-n estimate.
"""

from __future__ import annotations

import argparse
import json
import time
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path

from flint import arb, ctx


def ball(mid: str, rad: str = "0") -> arb:
    if rad == "0":
        return arb(mid)
    return arb(f"{mid} +/- {rad}")


def interval_from_endpoints(a: arb, b: arb) -> arb:
    mid = (a + b) / 2
    rad = (b - a) / 2
    # python-flint does not expose add_error; decimal midpoint/radius input is
    # the most stable public interface here.
    return arb(f"{mid.str(80, radius=False)} +/- {rad.str(80, radius=False)}")


def positive_upper(x: arb) -> arb:
    """Return a nonnegative upper bound for a ball known to enclose f(I)."""
    upper = x.upper()
    if upper < 0:
        return arb(0)
    return upper


def abs_upper(x: arb) -> arb:
    return x.abs_upper()


def decimal_arb(x: Decimal) -> arb:
    return arb(format(x, "f"))


def integral_interval_bessel(n: int, R_text: str, h_text: str) -> arb:
    steps = int((Decimal(R_text) / Decimal(h_text)).to_integral_value(rounding=ROUND_FLOOR))
    if steps < 1:
        raise ValueError("R/h must be at least 1")
    R = arb(R_text)
    h = R / steps
    total = arb(0)
    for k in range(steps):
        a = h * k
        b = h * (k + 1)
        x = interval_from_endpoints(a, b)
        j0 = x.bessel_j(0)
        jn = x.bessel_j(n)
        y = (j0 ** 4) * (jn ** 2) * x
        # Integral over [a,b] lies in width * range(y).  The integrand is
        # nonnegative, but natural interval extension can produce a small
        # negative lower endpoint through dependency, so clip only the lower
        # side by adding the nonnegative upper enclosure and retaining a
        # trivial lower bound of 0 for that subinterval if needed.
        upper = positive_upper(y)
        lower = y.lower()
        if lower < 0:
            lower = arb(0)
        total += (b - a) * interval_from_endpoints(lower, upper)
    return total


def integral_midpoint_derivative(n: int, R_text: str, h_text: str) -> arb:
    """Certified midpoint enclosure using the global derivative bound.

    On an interval centered at c with radius rho, evaluate

        f(r) = r J_0(r)^4 J_n(r)^2

    at c.  Since |J_m| <= 1 and |J'_m| <= 1 for integer m on the real line,
    the suprema on the interval are bounded by the midpoint absolute values
    plus rho.  This gives a Lipschitz bound for f, hence

        f(I) subset f(c) +/- rho * sup_I |f'|.

    This is much sharper than calling Arb's Bessel function directly on the
    whole interval.
    """
    R_dec = Decimal(R_text)
    h_dec = Decimal(h_text)
    steps = int((R_dec / h_dec).to_integral_value(rounding=ROUND_FLOOR))
    if steps < 1:
        raise ValueError("R/h must be at least 1")
    h_dec = R_dec / Decimal(steps)
    h = decimal_arb(h_dec)
    rho_dec = h_dec / 2
    rho = decimal_arb(rho_dec)
    total = arb(0)

    for k in range(steps):
        c_dec = h_dec * (Decimal(k) + Decimal("0.5"))
        c = decimal_arb(c_dec)
        r_sup = decimal_arb(c_dec + rho_dec)
        j0 = c.bessel_j(0)
        jn = c.bessel_j(n)
        fmid = c * (j0 ** 4) * (jn ** 2)

        sup_j0 = min(abs_upper(j0) + rho, arb(1))
        sup_jn = min(abs_upper(jn) + rho, arb(1))
        deriv_bound = (sup_j0 ** 4) * (sup_jn ** 2)
        deriv_bound += r_sup * (
            4 * (sup_j0 ** 3) * (sup_jn ** 2)
            + 2 * (sup_j0 ** 4) * sup_jn
        )
        lower = fmid.lower() - rho * deriv_bound
        upper = fmid.upper() + rho * deriv_bound
        if lower < 0:
            lower = arb(0)
        total += h * interval_from_endpoints(lower, upper)
    return total


def oscillatory_tail_bound(n: int, R: arb) -> arb:
    """Tail bound for int_R^infty J0^4 Jn^2 r dr.

    Conditional analytic input used here:

        |J_m(r)| <= sqrt(2/(pi r))    for r >= R and m in {0,n}.

    Under this hypothesis the tail is at most 8/(pi^3 R).  The command-line
    check enforces R >= 2*n as a crude regime guard, but the displayed JSON
    keeps the hypothesis explicit.  The next mathematical upgrade is to
    replace this with a quoted, mode-uniform Bessel inequality.
    """
    pi = arb.pi()
    if R.lower() <= 0:
        raise ValueError("R must be positive")
    return arb(8) / (pi ** 3 * R)


def enclose_integral(
    n: int, R_text: str, h_text: str, use_tail: bool, method: str
) -> arb:
    R = arb(R_text)
    if method == "interval-bessel":
        finite = integral_interval_bessel(n, R_text, h_text)
    elif method == "midpoint-derivative":
        finite = integral_midpoint_derivative(n, R_text, h_text)
    else:
        raise ValueError(f"unknown integration method: {method}")
    if not use_tail:
        return finite
    tail = oscillatory_tail_bound(n, R)
    return interval_from_endpoints(finite.lower(), finite.upper() + tail)


def as_report(x: arb, digits: int) -> dict[str, str]:
    return {
        "ball": x.str(digits),
        "lower": x.lower().str(digits, radius=False),
        "upper": x.upper().str(digits, radius=False),
        "radius": x.rad().str(digits, radius=False),
    }


def verify(args: argparse.Namespace) -> dict:
    ctx.prec = args.prec
    R = arb(str(args.R))
    target = arb(str(args.target_ratio))

    if args.nmin < 2 or args.nmax < args.nmin:
        raise ValueError("require 2 <= nmin <= nmax")
    if args.tail and R.lower() < 2 * args.nmax:
        raise ValueError("with the current crude tail guard, require R >= 2*nmax")

    t0 = time.time()
    J0 = enclose_integral(0, str(args.R), str(args.h), args.tail, args.method)
    rows = []
    denominator_positive = J0.lower() > 0
    ok = bool(denominator_positive)

    for n in range(args.nmin, args.nmax + 1):
        Jn = enclose_integral(n, str(args.R), str(args.h), args.tail, args.method)
        ratio_upper = Jn.upper() / J0.lower()
        # The target nu_0 >= 0.4 Lambda_0 follows from Jn/J0 <= 0.12 on the
        # 5 I_n branch.  The I_n branch is then much farther from Lambda_0.
        certified = denominator_positive and ratio_upper < target
        ok = ok and bool(certified)
        rows.append(
            {
                "n": n,
                "J_n": as_report(Jn, args.digits),
                "J_n_over_J0_upper": ratio_upper.str(args.digits),
                "certifies_ratio_below_target": bool(certified),
            }
        )

    lambda0_factor = 16 * (arb.pi() ** 4)
    Lambda0 = lambda0_factor * J0

    return {
        "rigorous_finite_mode_certificate": bool(ok),
        "finite_mode_range": [args.nmin, args.nmax],
        "target_ratio": args.target_ratio,
        "meaning": (
            "If every listed ratio is <= 0.12, then the checked finite modes "
            "satisfy |5 I_n - Lambda0| >= 0.4 Lambda0 and "
            "|I_n - Lambda0| >= 0.4 Lambda0."
        ),
        "not_yet_certified": (
            "Large n > nmax still require a separate mode-tail estimate. "
            "The r-tail bound also depends on the stated Bessel majorant."
        ),
        "parameters": {
            "precision_bits": args.prec,
            "R": str(args.R),
            "h": str(args.h),
            "tail_bound_used": bool(args.tail),
            "finite_interval_method": args.method,
            "finite_interval_method_hypotheses": (
                "|J_m(r)| <= 1 and |J'_m(r)| <= 1 for integer m and real r"
                if args.method == "midpoint-derivative"
                else "direct Arb Bessel interval evaluation on each subinterval"
            ),
            "tail_hypothesis": (
                "|J_m(r)| <= sqrt(2/(pi r)) for r >= R and m in {0,n}"
                if args.tail
                else "none"
            ),
        },
        "J0_lower_positive": bool(denominator_positive),
        "J0": as_report(J0, args.digits),
        "Lambda0": as_report(Lambda0, args.digits),
        "rows": rows,
        "elapsed_seconds": time.time() - t0,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nmin", type=int, default=2)
    parser.add_argument("--nmax", type=int, default=8)
    parser.add_argument("--R", type=str, default="200")
    parser.add_argument("--h", type=str, default="0.02")
    parser.add_argument("--prec", type=int, default=128)
    parser.add_argument("--digits", type=int, default=30)
    parser.add_argument("--target-ratio", type=str, default="0.12")
    parser.add_argument("--tail", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument(
        "--method",
        choices=["midpoint-derivative", "interval-bessel"],
        default="midpoint-derivative",
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    report = verify(args)
    text = json.dumps(report, indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
