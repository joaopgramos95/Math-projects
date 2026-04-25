# Promotion notes (orchestrator)

State after the most recent promotion round:

| File                    | Status        |
|-------------------------|---------------|
| Basic.lean              | promoted      |
| Bump.lean               | promoted      |
| Potential.lean          | promoted      |
| Normalization.lean      | **stub** (revert below) |
| TestFunction.lean       | stub          |
| OneDimensional.lean     | stub          |
| HigherDimensional.lean  | stub          |

`lake build L2Counterexample` succeeds, and every `WIP_*.lean` still
compiles standalone. Promotion of the four downstream files is blocked
on architectural decisions described below.

## What works

`Basic.lean`, `Bump.lean`, `Potential.lean` together provide the smooth
bump `kappa` and the scaled potential family `phi_Sc, phiP_S, phiPP_S`
(with parameters `eps_S, eta_S`). The `kappa*` axioms originally present
in `WIP_Potential.lean` were removed during promotion since `Bump.lean`
provides real definitions.

## What doesn't (and why Normalization promotion was reverted)

Promoting `Normalization.lean` verbatim from `WIP_Normalization.lean`
typechecks against `Potential.lean` (no name clash with `phi_Sc, eps_S,
eta_S`) and lake builds. But the downstream `WIP_TestFunction.lean`,
`WIP_OneDimensional.lean`, `WIP_HigherDimensional.lean` then fail to
compile because they re-axiomatise the same names. More importantly,
some of those names refer to **different mathematical objects**:

### 1. `A_S` — name reused for two distinct integrals

- `WIP_Normalization.lean`: `A_S S = ∫ x in Set.Ici (1 + epsS S),
  Real.exp (-(phi_S S x))` — the right-tail integral, `~ 1/S`.
- `WIP_TestFunction.lean`: `A_S` is axiomatised as the layer normalizer
  `∫_{(1-ε)..(1+ε)} φ''_S(t) · exp(φ_S(t)) dt`, `~ S`.

The blueprint reserves `A_S` for the layer normalizer (TestFunction's
reading). `Normalization.lean`'s right-tail integral should be renamed
(e.g., `tailIntegral_S`) before promotion, otherwise downstream code
silently picks up the wrong meaning.

### 2. `Z_S_pos` — incompatible hypotheses

- Normalization: `Z_S_pos (S : ℝ) (hS : 0 < S) : 0 < Z_S S`.
- TestFunction: `Z_S_pos {S : ℝ} (hS_large : 1 < S) : 0 < Z_S S`.

Same name, different signatures. After promoting Normalization's, every
TestFunction call site `Z_S_pos hS_large` must become
`Z_S_pos (lt_trans zero_lt_one hS_large)`.

### 3. Asymptotic axioms in two different formalisations

- Normalization uses the local `BigOInv` predicate (a finitary
  `∃ C S₀, ∀ S ≥ S₀, |f S − g S| ≤ C·S^(−k)`).
- TestFunction uses Mathlib's `Asymptotics.IsBigO` with `Filter.atTop`.

These are equivalent but not definitionally; promoting Normalization
requires writing a one-shot bridge lemma `BigOInv f g k →
(fun S => f S − g S) =O[atTop] (· ^ (-k:ℤ))`, then re-deriving each
`*_asymp` axiom in TestFunction.

### 4. Naming inconsistencies between upstream and downstream

| Concept           | Potential.lean | downstream WIP files      |
|-------------------|----------------|---------------------------|
| Potential         | `phi_Sc`       | `phi_S` (Norm/TF/OneD)    |
| First derivative  | `phiP_S`       | `phi_S'` / `phiDer_S`     |
| Second derivative | `phiPP_S`      | `phi_S''` / `phiDer2_S`   |
| ε parameter       | `eps_S`        | `epsS` / `epsOf`          |
| η parameter       | `eta_S`        | `etaS` / `etaOf`          |

Without a consistent naming scheme, the `phi_S` axiomatised in
Normalization and the `phi_Sc` defined in Potential remain
mathematically unconnected.

## Recommended path before further promotion

1. Decide on canonical names project-wide (likely `phi_Sc, phiP_S,
   phiPP_S, eps_S, eta_S, A_layer_S, tailIntegral_S, ...`).
2. In `Normalization`'s WIP file: rename `A_S` → `tailIntegral_S` (or
   inline it into `q_S`'s definition); rename `phi_S` → `phi_Sc`,
   `epsS` → `eps_S`, `etaS` → `eta_S`; weaken `Z_S_pos` to
   `0 < S`; pick one of `BigOInv`/`IsBigO` and convert.
3. In each downstream WIP file: apply matching renames, remove the
   axioms now provided by the upstream canonical files, and adjust call
   sites.
4. Promote in dependency order with `lake build` at each step.

The work in step 2–3 is mostly mechanical, but it is several hundred
edits and changes the public API of each file. It should be coordinated
with the project authors before being applied.
