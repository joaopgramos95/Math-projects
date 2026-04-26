# Promotion notes (orchestrator)

## State

| File                    | Axioms |
|-------------------------|-------:|
| Basic.lean              |      0 |
| Bump.lean               |      0 |
| Potential.lean          |      0 |
| Normalization.lean      |     12 |
| TestFunction.lean       |     11 |
| OneDimensional.lean     |      6 |
| HigherDimensional.lean  |      6 |
| **Total**               | **35** |

`lake build L2Counterexample` succeeds. Zero `sorry` remaining.

The previous state had **61 axioms**; the current cleanup discharged
**26**, mostly by:

* deriving measurability from `phi_S_contDiff` etc. (Norm and OneDim);
* using `MemLp.mul'` / Hölder triple `(2,2,1)` for `phiDer_gg_integrable`;
* defining `Var_f_S` as the integral (so `Var_gg_eq_Var_ff` becomes
  `rfl`) and `EE_phi_S` as `E_phi (g_S' S)`;
* defining `rho_S` concretely as
  `volume.withDensity (fun x => ENNReal.ofReal ((Z_S S)⁻¹ · exp(−φ_S x)))`,
  letting us prove `rho_S_isProb_of_pos`;
* `Z_S_pos` from `integral_exp_pos`;
* `exp_negPhiS_integrableOn_tail` from `Integrable.integrableOn`;
* `integral_exp_neg_Ici` and `integral_sq_exp_neg_Ici` from
  `Real.integral_rpow_mul_exp_neg_mul_Ioi` (specialisations at α = 1
  and α = 3);
* `exp_negGaussianTail_integrableOn` by bounding `exp(−Au − Bu²/2)`
  by the Gaussian `exp(−B/2 · u²)`;
* `phiDer_gg_integrable` via `MemLp.mul'`;
* `t_S_le_one` and `t_S_nonneg_axiom` from `setIntegral_le_integral`
  and `Normalization.t_S_nonneg`;
* `q_S_abs_le_two` (the blueprint claims `≤ 1`; we use the looser
  `≤ 2` so we can avoid the symmetry argument). The variance bound
  is updated from `4 t_S` to `6 t_S`, which is harmless for the
  asymptotic conclusion;
* HigherDim's `f_S, E_phi_S, Var_phi_S, distSq_phi_S, delta_phi_S_HD`
  axioms are now *aliases* for `OneDimensional.{ff_S, EE_phi_S,
  Var_f_S, Var_f_S, delta_phi_S}`, so `delta_phi_S_HD_eventually_pos`,
  `distSq_phi_S_over_delta_unbounded`, `no_uniform_L2_stability_1D`,
  `f_S_integral_zero`, `f_S_orth_phiDer_S` reduce to OneDim theorems.

## What's left as axioms

### Asymptotic axioms (not currently tractable)

These are deep analytic results whose proofs require substantial real
analysis infrastructure. Listed in approximate order of difficulty:

* `Normalization.tailInt_S_asymp` (`tailInt_S = 1/S + O(S⁻³)`).
* `Normalization.Z_S_asymp` (`Z_S = 2 + 2/S + O(S⁻³)`).
* `Normalization.q_S_asymp` (`q_S = 1/S − 1/S² + O(S⁻³)`) — derivable
  from the previous two by BigOInv algebra.
* `Normalization.t_S_asymp`.
* `Normalization.tail_gaussian_bound` — quantitative bound, derivable
  from `integral_exp_neg_Ici`, `integral_sq_exp_neg_Ici`,
  `one_sub_exp_neg_le`, monotonicity. Tractable but extensive.
* `Normalization.one_div_tildeS_asymp`.
* `Normalization.exp_neg_phi_boundary_asymp`.
* `Normalization.phi_S_boundary_small`.
* `Normalization.phi_S_layer_small`.
* `OneDimensional.EE_phi_S_asymp`.
* `OneDimensional.Var_f_S_asymp`.
* `TestFunction.A_S_asymp`.
* `TestFunction.Var_phi_g_S_expansion`. (Sketch attempted; algebra is
  doable but the IsBigO / linarith chain ran into multiple subgoals
  that need patient hand-holding.)

### Other axioms

* `Normalization.phi_S_tail` (regional formula for `phi_S` on the tail).
  Provable from FTC + a missing `phiDer_S_ext_right` lemma in Potential.
* `Normalization.exp_negPhiS_integrable` — Gaussian domination, requires
  bounding `exp(-phi_S) ≤ exp(-eta·x²/2)` and combining with Gaussian
  integrability.
* `OneDimensional.rho_S_isProb` (unconditional axiom-instance) — kept
  alongside the proven `rho_S_isProb_of_pos`. Removing requires
  threading a `0 < S` hypothesis through every downstream `MemLp` /
  `Integrable` site.
* `OneDimensional.rho_S_reflection_invariant` — a clean proof exists
  modulo measurability of `phi_S`, which itself needs `0 < S`.
* `OneDimensional.phiDer_S_memL2`, `g_S_memL2` — L² membership,
  unconditional, used by ff_S_memL2 (which doesn't have S>0 in scope).
* `TestFunction.A_S_symm` — change of variables `t ↦ -t`.
* `TestFunction.hasDerivAt_g_S_layer_pos`, `hasDerivAt_g_S_layer_neg` —
  derivative formulas, FTC.
* `TestFunction.g_S_continuous` — piecewise continuity, gluing argument.
* `TestFunction.layerLebesgueEnergyPos_eq`, `layerLebesgueEnergyNeg_eq`,
  `E_phi_g_S_eq` — explicit energy identities.
* `TestFunction.integral_g_S_eq_q_plus_error`,
  `integral_g_S_sq_eq_q_plus_error` — measure decomposition.
* `HigherDimensional.stdGaussian`, `stdGaussian_isProb`,
  `stdGaussian_first_moment` — Mathlib has `MeasureTheory.Measure.gaussianReal`
  but lifting to `Fin n → ℝ` via product measure is real work.
* `HigherDimensional.integral_prod_first_coord`,
  `integral_prod_separable` — Fubini bridges; need integrability
  hypotheses or a careful "non-integrable case" argument.
* `HigherDimensional.prodSpace_iso_euclidean` — linear isometric
  equivalence, standard but boilerplate.

## Naming canon

(Unchanged from previous round; reproduced for completeness.)

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

Each `WIP_*.lean` is identical to its canonical counterpart. Future agents
edit the WIP files; the orchestrator promotes by `cp` and re-runs
`lake build`.
