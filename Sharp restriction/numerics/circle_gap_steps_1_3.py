#!/usr/bin/env python3
"""Prototype numerics for the circle restriction gap programme.

This script is deliberately dependency-light: it only needs the Python
standard library and a system Bessel implementation (GSL if present,
otherwise libm).  It is not an interval-arithmetic certificate.  The goal is
to make Steps 1--3 from ``convolution-equations.tex`` executable and to
produce numbers that can later be replaced by Arb/interval backends.

Implemented:
  Step 1. Floating-point quadrature for J_n = int J_0^4 J_n^2 r dr and the
          linearized gap nu_0 at the constant solution.
  Step 2. Reports the Newton--Kantorovich radius formula; a certified
          Lipschitz constant M_0(r) is still needed.
  Step 3. Floating-point finite-mode variational screen over positive real
          cosine polynomials.  This is a search heuristic, not an exclusion
          proof.  A proof needs interval residuals/Krawczyk boxes.
"""

from __future__ import annotations

import argparse
import ctypes
import json
import math
import random
import time
from pathlib import Path


TWO_PI = 2.0 * math.pi


class BesselBackend:
    def __init__(self) -> None:
        self.name = "libm"
        self._gsl = None
        try:
            self._gsl = ctypes.CDLL("libgsl.so.27")
            self._gsl.gsl_sf_bessel_Jn.argtypes = [ctypes.c_int, ctypes.c_double]
            self._gsl.gsl_sf_bessel_Jn.restype = ctypes.c_double
            self._gsl.gsl_sf_bessel_J0.argtypes = [ctypes.c_double]
            self._gsl.gsl_sf_bessel_J0.restype = ctypes.c_double
            self.name = "gsl"
        except OSError:
            self._gsl = None
            self._libm = ctypes.CDLL("libm.so.6")
            self._libm.j0.argtypes = [ctypes.c_double]
            self._libm.j0.restype = ctypes.c_double
            self._libm.jn.argtypes = [ctypes.c_int, ctypes.c_double]
            self._libm.jn.restype = ctypes.c_double

    def j(self, n: int, x: float) -> float:
        if self._gsl is not None:
            if n == 0:
                return float(self._gsl.gsl_sf_bessel_J0(x))
            return float(self._gsl.gsl_sf_bessel_Jn(n, x))
        if n == 0:
            return float(self._libm.j0(x))
        return float(self._libm.jn(n, x))


def simpson_integral(values: list[float], h: float) -> float:
    """Composite Simpson rule for an even number of subintervals."""
    n = len(values) - 1
    if n % 2 != 0:
        raise ValueError("Simpson rule needs an even number of subintervals")
    odd = sum(values[1:n:2])
    even = sum(values[2:n:2])
    return h * (values[0] + values[n] + 4.0 * odd + 2.0 * even) / 3.0


def integrate_Jn(backend: BesselBackend, n: int, R: float, h: float) -> float:
    steps = int(round(R / h))
    if steps % 2:
        steps += 1
    h = R / steps
    vals: list[float] = []
    for k in range(steps + 1):
        r = k * h
        j0 = backend.j(0, r)
        jn = backend.j(n, r)
        vals.append((j0 * j0 * j0 * j0) * (jn * jn) * r)
    return simpson_integral(vals, h)


def run_step1(backend: BesselBackend, nmax: int, R: float, h: float) -> dict:
    t0 = time.time()
    Js = [integrate_Jn(backend, n, R, h) for n in range(nmax + 1)]
    J0 = Js[0]
    lambda0 = 16.0 * math.pi**4 * J0
    R0 = lambda0 ** (1.0 / 6.0)

    gap_rows = []
    min_ratio = float("inf")
    min_row = None
    for n, Jn in enumerate(Js):
        ratio_I = Jn / J0
        gap_I = abs(ratio_I - 1.0)
        gap_5I = abs(5.0 * ratio_I - 1.0)
        row = {
            "n": n,
            "J_n": Jn,
            "I_n_over_Lambda0": ratio_I,
            "abs_I_minus_Lambda_over_Lambda": gap_I,
            "abs_5I_minus_Lambda_over_Lambda": gap_5I,
        }
        gap_rows.append(row)
        if n >= 2:
            for branch, gap in (("I", gap_I), ("5I", gap_5I)):
                if gap < min_ratio:
                    min_ratio = gap
                    min_row = {"n": n, "branch": branch, "gap_ratio": gap}

    # Translation branch at n=1 is a zero mode, and the orthogonal n=1 branch
    # gives 4/5 Lambda0.  Include it in the slice gap.
    slice_gap_ratio = min(0.8, min_ratio)
    return {
        "backend": backend.name,
        "R": R,
        "h": h,
        "nmax": nmax,
        "J0": J0,
        "Lambda0": lambda0,
        "restriction_norm_at_constant": R0,
        "rows": gap_rows,
        "min_gap_excluding_symmetries": min_row,
        "nu0_over_Lambda0_estimate": slice_gap_ratio,
        "nu0_estimate": slice_gap_ratio * lambda0,
        "elapsed_seconds": time.time() - t0,
        "rigorous": False,
        "warning": "Floating-point quadrature only; no interval/tail certificate.",
    }


def normalize_cos_coeffs(coeffs: list[float]) -> list[float]:
    # f(theta)=b0 + sum_{m>=1} b_m cos(m theta).
    norm2 = TWO_PI * coeffs[0] * coeffs[0]
    norm2 += math.pi * sum(c * c for c in coeffs[1:])
    scale = 1.0 / math.sqrt(norm2)
    return [scale * c for c in coeffs]


def min_on_mesh(coeffs: list[float], mtheta: int) -> float:
    best = float("inf")
    for j in range(mtheta):
        th = TWO_PI * j / mtheta
        val = coeffs[0]
        for m, c in enumerate(coeffs[1:], start=1):
            val += c * math.cos(m * th)
        best = min(best, val)
    return best


def precompute_objective_grid(
    backend: BesselBackend, modes: int, R: float, dr: float, nphi: int
) -> dict:
    rsteps = int(round(R / dr))
    if rsteps % 2:
        rsteps += 1
    dr = R / rsteps

    rvals = [k * dr for k in range(rsteps + 1)]
    rweights = []
    for k, r in enumerate(rvals):
        if k == 0 or k == rsteps:
            w = dr / 3.0
        elif k % 2:
            w = 4.0 * dr / 3.0
        else:
            w = 2.0 * dr / 3.0
        rweights.append(w * r)

    phis = [TWO_PI * j / nphi for j in range(nphi)]
    phi_weight = TWO_PI / nphi
    cos_m_phi = [
        [math.cos(m * ph) for ph in phis]
        for m in range(modes + 1)
    ]
    bessel = [
        [backend.j(m, r) for r in rvals]
        for m in range(modes + 1)
    ]
    i_cycle = [(1.0, 0.0), (0.0, 1.0), (-1.0, 0.0), (0.0, -1.0)]

    return {
        "R": R,
        "dr": dr,
        "nphi": nphi,
        "rvals": rvals,
        "rweights": rweights,
        "phi_weight": phi_weight,
        "cos_m_phi": cos_m_phi,
        "bessel": bessel,
        "i_cycle": i_cycle,
    }


def objective_cos(coeffs: list[float], grid: dict) -> float:
    modes = len(coeffs) - 1
    total = 0.0
    rweights = grid["rweights"]
    phi_weight = grid["phi_weight"]
    cos_m_phi = grid["cos_m_phi"]
    bessel = grid["bessel"]
    i_cycle = grid["i_cycle"]
    nphi = grid["nphi"]

    for ir, rw in enumerate(rweights):
        angular_sum = 0.0
        # m=0 contribution: 2*pi*b0*J0(r), real.
        base = TWO_PI * coeffs[0] * bessel[0][ir]
        for jp in range(nphi):
            re = base
            im = 0.0
            for m in range(1, modes + 1):
                # E(c_m cos(m theta)) = 2*pi*c_m*i^m*J_m(r)*cos(m phi).
                a, b = i_cycle[m % 4]
                term = TWO_PI * coeffs[m] * bessel[m][ir] * cos_m_phi[m][jp]
                re += a * term
                im += b * term
            abs2 = re * re + im * im
            angular_sum += abs2 * abs2 * abs2
        total += rw * phi_weight * angular_sum
    return total


def deterministic_one_mode_scan(
    backend: BesselBackend,
    modes: int,
    grid: dict,
    mesh: int,
    positivity_mesh: int,
) -> dict:
    constant = normalize_cos_coeffs([1.0] + [0.0] * modes)
    lambda_const_quad = objective_cos(constant, grid)
    best = {
        "ratio_to_quadrature_constant": 1.0,
        "lambda_quadrature": lambda_const_quad,
        "coeffs": constant,
        "source": "constant",
        "min_on_mesh": min_on_mesh(constant, positivity_mesh),
    }
    for mode in range(1, modes + 1):
        for i in range(mesh + 1):
            t = -0.98 + 1.96 * i / mesh
            coeffs = [1.0] + [0.0] * modes
            coeffs[mode] = t
            # Sufficient but not necessary positivity for this one-mode family.
            if coeffs[0] <= abs(t):
                continue
            coeffs = normalize_cos_coeffs(coeffs)
            minv = min_on_mesh(coeffs, positivity_mesh)
            if minv < -1e-12:
                continue
            val = objective_cos(coeffs, grid)
            ratio = val / lambda_const_quad
            if ratio > best["ratio_to_quadrature_constant"]:
                best = {
                    "ratio_to_quadrature_constant": ratio,
                    "lambda_quadrature": val,
                    "coeffs": coeffs,
                    "source": f"one-mode-{mode}",
                    "min_on_mesh": minv,
                }
    return best


def random_positive_coeffs(modes: int, rng: random.Random, amplitude: float) -> list[float]:
    # Draw a positive cosine polynomial via the sufficient condition
    # sum_{m>=1} |b_m| <= amplitude*b0 with amplitude<1.
    coeffs = [1.0] + [0.0] * modes
    raw = [rng.uniform(-1.0, 1.0) / (m + 0.5) for m in range(1, modes + 1)]
    s = sum(abs(x) for x in raw)
    if s > 0:
        raw = [x * amplitude / s for x in raw]
    for m, x in enumerate(raw, start=1):
        coeffs[m] = x
    return normalize_cos_coeffs(coeffs)


def run_step3_variational_screen(
    backend: BesselBackend,
    modes: int,
    R: float,
    dr: float,
    nphi: int,
    one_mode_mesh: int,
    samples: int,
    positivity_mesh: int,
    seed: int,
) -> dict:
    t0 = time.time()
    grid = precompute_objective_grid(backend, modes, R, dr, nphi)
    constant = normalize_cos_coeffs([1.0] + [0.0] * modes)
    lambda_const_quad = objective_cos(constant, grid)

    best = deterministic_one_mode_scan(
        backend, modes, grid, one_mode_mesh, positivity_mesh
    )
    rng = random.Random(seed)
    for amplitude in (0.15, 0.35, 0.65, 0.9):
        for _ in range(samples):
            coeffs = random_positive_coeffs(modes, rng, amplitude)
            minv = min_on_mesh(coeffs, positivity_mesh)
            if minv < -1e-12:
                continue
            val = objective_cos(coeffs, grid)
            ratio = val / lambda_const_quad
            if ratio > best["ratio_to_quadrature_constant"]:
                best = {
                    "ratio_to_quadrature_constant": ratio,
                    "lambda_quadrature": val,
                    "coeffs": coeffs,
                    "source": f"random-amplitude-{amplitude}",
                    "min_on_mesh": minv,
                }

    return {
        "modes": modes,
        "R": R,
        "dr": grid["dr"],
        "nphi": nphi,
        "one_mode_mesh": one_mode_mesh,
        "samples_per_amplitude": samples,
        "positivity_mesh": positivity_mesh,
        "seed": seed,
        "lambda_constant_quadrature": lambda_const_quad,
        "best": best,
        "elapsed_seconds": time.time() - t0,
        "rigorous": False,
        "warning": (
            "Floating-point quadrature and random/one-mode sampling only; "
            "this is not an eigenvalue exclusion certificate."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nmax", type=int, default=40)
    parser.add_argument("--bessel-R", type=float, default=2000.0)
    parser.add_argument("--bessel-h", type=float, default=0.02)
    parser.add_argument("--modes", type=int, default=6)
    parser.add_argument("--obj-R", type=float, default=120.0)
    parser.add_argument("--obj-dr", type=float, default=0.1)
    parser.add_argument("--nphi", type=int, default=96)
    parser.add_argument("--one-mode-mesh", type=int, default=160)
    parser.add_argument("--samples", type=int, default=80)
    parser.add_argument("--positivity-mesh", type=int, default=512)
    parser.add_argument("--seed", type=int, default=20260414)
    parser.add_argument("--output", type=Path, default=Path("numerics/results/circle_gap_steps_1_3.json"))
    args = parser.parse_args()

    backend = BesselBackend()
    print(f"backend: {backend.name}")

    print("\nSTEP 1: floating Bessel gap scan")
    step1 = run_step1(backend, args.nmax, args.bessel_R, args.bessel_h)
    print(f"  Lambda0 ~= {step1['Lambda0']:.15g}")
    print(f"  Lambda0^(1/6) ~= {step1['restriction_norm_at_constant']:.15g}")
    print(f"  nu0/Lambda0 estimate ~= {step1['nu0_over_Lambda0_estimate']:.12g}")
    print(f"  minimizer row ~= {step1['min_gap_excluding_symmetries']}")
    print("  WARNING: not interval-certified")

    print("\nSTEP 2: Newton radius bookkeeping")
    print("  Need a certified Lipschitz bound M0(r).")
    print("  Once known, any r0 <= nu_lower/(2*M0(r0)) certifies local isolation.")
    print(f"  Floating target nu_lower=0.4*Lambda0 ~= {0.4 * step1['Lambda0']:.12g}")

    print("\nSTEP 3: finite-mode variational screen (not a proof)")
    step3 = run_step3_variational_screen(
        backend,
        args.modes,
        args.obj_R,
        args.obj_dr,
        args.nphi,
        args.one_mode_mesh,
        args.samples,
        args.positivity_mesh,
        args.seed,
    )
    best = step3["best"]
    print(f"  modes = {args.modes}")
    print(f"  quadrature constant value ~= {step3['lambda_constant_quadrature']:.15g}")
    print(f"  best sampled ratio to constant quadrature ~= {best['ratio_to_quadrature_constant']:.12g}")
    print(f"  best source = {best['source']}")
    print(f"  best coefficients = {[round(x, 12) for x in best['coeffs']]}")
    print("  WARNING: not an exclusion certificate")

    result = {
        "step1": step1,
        "step2": {
            "rigorous": False,
            "nu_lower_target": 0.4 * step1["Lambda0"],
            "radius_condition": "r0 <= nu_lower/(2*M0(r0))",
            "missing": "certified Lipschitz constant M0(r)",
        },
        "step3": step3,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True))
    print(f"\nwrote {args.output}")


if __name__ == "__main__":
    main()
