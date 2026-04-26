# Promotion notes (orchestrator)

## State

| File                    | Axioms |
|-------------------------|-------:|
| Basic.lean              |      0 |
| Bump.lean               |      0 |
| Potential.lean          |      0 |
| Normalization.lean      |      7 |
| TestFunction.lean       |      1 |
| OneDimensional.lean     |      5 |
| HigherDimensional.lean  |      5 |
| **Total**               | **18** |

`lake build L2Counterexample` succeeds. Zero `sorry` remaining.

## Cumulative axiom history

```
61  → initial
35  → previous round (measurability, rho_S as withDensity, MemLp.mul',
                       Z_S_pos, integrals via Gamma, q_S_abs_le_two,
                       HigherDim aliasing, etc.)
31  → previous round (t_S_asymp, q_S_asymp, one_div_tildeS_asymp,
                       exp_neg_phi_boundary_asymp)
30  → g_S_continuous (FTC for primitives + Continuous.if_le)
23  → previous round (hasDerivAt_g_S_layer_pos, hasDerivAt_g_S_layer_neg,
                       A_S_symm, layerLebesgueEnergyPos_eq,
                       layerLebesgueEnergyNeg_eq, E_phi_g_S_eq)
21  → integral_g_S_eq_q_plus_error, integral_g_S_sq_eq_q_plus_error
       (rho_S/volume conversion + partition of ℝ + tail symmetry)
20  → Var_phi_g_S_expansion (algebraic q(1−q) expansion + IsBigO algebra)
19  → Var_f_S_asymp (Var_f_S = Var_phi g_S via probability-measure
       linearity; bridge IsBigO → BigOInv1D)
18  → tail_gaussian_bound (1 - exp(-v) ≤ v with v = η u²/2;
       integrate ∫ exp(-S̃u) · η u²/2 = η/S̃³ via Gamma-function helper)
```

## Axioms discharged in this round

* `TestFunction.hasDerivAt_g_S_layer_pos` proved via FTC for primitives
  (`intervalIntegral.integral_hasDerivAt_right`) and chain rule with
  `|·|` (which equals `id` near `x > 0`), then `congr_of_eventuallyEq`
  to transport from `N_S(|·|)/A_S` to `g_S` on `layerPos`.
* `TestFunction.hasDerivAt_g_S_layer_neg` proved analogously using
  `|·| = -·` near `x < 0` (gives sign flip), `phi_S_even` and
  `phiDer2_S_even` to express the derivative at `-x` in terms of `x`.
* `TestFunction.A_S_symm` proved by:
  `∫_{Ioo(-1-ε,-1+ε)} φ''·exp(φ) = ∫_{(-1-ε)..(-1+ε)} φ''·exp(φ)`
  (set-to-interval), then change of variables `t ↦ -t` via
  `intervalIntegral.integral_comp_neg` plus evenness of `φ_S, φ''_S`.
* `TestFunction.layerLebesgueEnergyPos_eq` proved by pointwise
  simplification of the integrand on `layerPos` using
  `g_S' = phiDer2_S · exp(phi_S)/A_S`, `Real.exp_neg`, and `field_simp`,
  reducing the integral to `(1/A_S²) · A_S = 1/A_S`.
* `TestFunction.layerLebesgueEnergyNeg_eq` analogous, using `A_S_symm`.
* `TestFunction.E_phi_g_S_eq` proved by:
  - `withDensity` rewrite (`integral_withDensity_eq_integral_toReal_smul`)
    of the `ρ_S` integral as `(Z_S)⁻¹` times a Lebesgue integral;
  - `ENNReal.toReal_ofReal` + `smul_eq_mul` to expose the density factor;
  - splitting the volume integral over `layerPos ∪ layerNeg` (where the
    integrand vanishes off the layers via `g_S'_off_layers`); and
  - identifying each piece with the corresponding layer Lebesgue energy.

### Earlier in current sequence (already at axiom count 30)

* `TestFunction.g_S_continuous` proved via FTC for primitives applied to
  `N_S` and `Continuous.if_le` for the nested piecewise gluing.

To preserve the topological order required by Lean (definitions before
uses), `q_S_asymp` and `t_S_asymp` are placed at the end of
`Normalization.lean` (after `exists_S_Z_S_ge_one`), and
`exists_S_q_S_lt_one` is moved after `q_S_asymp`.

## What remains as axioms (23)

### TestFunction.lean (4 remaining)

* `A_S_asymp` — `A_S − S = O(S⁻¹)` as `S → ∞`. Genuinely asymptotic.
* `integral_g_S_eq_q_plus_error` — expansion of `∫ g_S dρ_S = q_S + R`
  with `|R| ≤ t_S`. Requires splitting over core / layers / exterior,
  using `g_S = 0` on core and `g_S = 1` on exterior, plus the symmetry
  identity `tailInt_S(left) = tailInt_S(right)` from `phi_S_even`.
* `integral_g_S_sq_eq_q_plus_error` — analogous for `g_S²`.
* `Var_phi_g_S_expansion` — derivable from `Var_phi_g_S_isBigO` and
  `q_S_isBigO`; previous attempts failed on `Asymptotics.IsBigO`
  bookkeeping.

### Normalization.lean (8 remaining)

* `phi_S_tail`, `phi_S_boundary_small`, `phi_S_layer_small`,
  `tailInt_S_tail_eq`, `tail_gaussian_bound`, `tailInt_S_asymp`,
  `Z_S_asymp` — change-of-variables and asymptotic bookkeeping for
  the partition function.
* `exp_negPhiS_integrable` — Gaussian-domination integrability.

### OneDimensional.lean (6 remaining)

* `rho_S_isProb`, `rho_S_reflection_invariant` — proofs sketched in
  comments; the unconditional form needs `0 < S` for measurability.
* `phiDer_S_memL2`, `g_S_memL2` — L² membership for inner products.
* `EE_phi_S_asymp`, `Var_f_S_asymp` — final asymptotics.

### HigherDimensional.lean (5 remaining)

* `stdGaussian`, `stdGaussian_isProb`, `stdGaussian_first_moment`,
  `integral_prod_first_coord`, `integral_prod_separable`,
  `prodSpace_iso_euclidean` — Mathlib has `gaussianReal`,
  `Measure.pi`, `MeasureTheory.integral_prod`; lifting to this file's
  forms is a substantial task.

## Naming canon

(Unchanged; reproduced for completeness.)

| Concept                        | Canonical name      | Defined in           |
|--------------------------------|---------------------|----------------------|
| Smooth bump                    | `kappa`             | `Bump.lean`          |
| ε, η parameters                | `eps_S, eta_S`      | `Potential.lean`     |
| Potential, derivatives         | `phi_S, phiDer_S, phiDer2_S` | `Potential.lean` |
| Evenness / oddness             | `phi_S_even, phiDer_S_odd, phiDer2_S_even` | `Potential.lean` |
| Quadratic lower bound          | `phi_S_quadratic_lower` | `Potential.lean` |
| Core formula                   | `phi_S_core`        | `Potential.lean`     |
| Partition function             | `Z_S`               | `Normalization.lean` |
| Right-tail integral            | `tailInt_S`         | `Normalization.lean` |
| Layer normalizer (blueprint A) | `A_S`               | `TestFunction.lean`  |
| Tail / layer masses            | `q_S, t_S`          | `Normalization.lean` |
| Probability measure            | `rho_S`             | `TestFunction.lean`  |
| Test function stack            | `g_S, ff_S, cc_S`   | TF / OneDim          |
| Functionals                    | `EE_phi_S, Var_f_S, delta_phi_S` | `OneDimensional.lean` |

## WIP files

Each `WIP_*.lean` is identical to its canonical counterpart. Future
agents edit the WIP files; the orchestrator promotes by `cp` and
re-runs `lake build`.
