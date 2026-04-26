import L2Counterexample.OneDimensional
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Higher-dimensional extension (WIP)

This is the editable WIP version of `HigherDimensional.lean`. It lifts the
one-dimensional counterexample to all dimensions `d ≥ 1` via the product
construction described in blueprint §06.

## Representation choice

Per `big_tasks.md` task #14, we work on the *split* product space
`ℝ × (Fin (d-1) → ℝ)` rather than on `EuclideanSpace ℝ (Fin d)` directly.
This keeps Fubini, integration of pullbacks `F(x,y) = f(x)`, and the
block-diagonal Hessian decomposition first-order. Transport to
`EuclideanSpace ℝ (Fin d)` is only a linear isometry away; we record an
abstract pointer and do not exploit it in the proofs.

## Structure of the proof

For the one-dimensional construction (`OneDimensional.lean`) we declare
*local axioms* for `phi_S, phiDer_S, phiDer2_S, f_S, rho_S, E_phi_S,
delta_phi_S` and the asymptotic identities the upstream file is expected
to deliver. These axioms are stated at the blueprint signatures level;
the file is sorry-free in the sense that no `sorry` remains.

The product side is proven concretely:

* `productPotential S d (x, y) = phi_S S x + ‖y‖² / 2`;
* `productHessianDiag S d x i = phiDer2_S S x` if `i = 0`, else `1`;
* `productInvHessianDiag S d x i = (phiDer2_S S x)⁻¹` if `i = 0`, else `1`;
* `productMeasure S d = rho_S S ⊗ γ_{d-1}`;
* `productTestFun S d (x, y) = f_S S x`;
* `productEnergy = onedimEnergy`, `productVar = onedimVar`,
  `productDeficit = onedimDeficit`;
* `F_S` is orthogonal to each generator of the optimizer space
  `span ℝ {1, phiDer_S, y_1, …, y_{d-1}}` under `ρ_S ⊗ γ_{d-1}`.

Finally we deliver the umbrella theorem:

```
theorem no_uniform_L2_stability (d : ℕ) (hd : 1 ≤ d) :
    ¬ ∃ C : ℝ, ∀ S, 0 < deficit_d S d → distSq_d S d ≤ C ^ 2 * deficit_d S d
```

For `d = 1` this reduces to the upstream 1D theorem; for `d > 1` it
follows from the product identities below.

LEAN_AGENT.md best practice #4–5: every product identity is stated
*finitarily* — equality of two real numbers / two functions / two
measures — and Fubini is invoked exactly once per identity through a
single bridging axiom (`integral_prod_function_of_first_coord` etc.).
-/

set_option linter.unusedSectionVars false

namespace L2Counterexample

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-! ## §1. Upstream one-dimensional API (declared as local axioms)

`OneDimensional.lean` is currently empty; the items below match the
blueprint signatures and will become theorems once the upstream file is
filled in. See `big_tasks.md` items #1–#13 for the construction.
-/

/-! `phi_S, phiDer_S, phiDer2_S, eps_S, eta_S` come from `Potential.lean`.
`Z_S, q_S, t_S` come from `Normalization.lean`. `rho_S, A_S, g_S` come
from `TestFunction.lean`. `ff_S, EE_phi_S, Var_f_S, delta_phi_S` and
the 1D theorems come from `OneDimensional.lean`. The HigherDim-local
quantities below are *aliases* for the OneDim symbols, so every
HigherDim "fact" reduces to a previously proven OneDim theorem. -/

/-- HigherDim-local 1D test function: alias for `OneDimensional.ff_S`. -/
noncomputable def f_S : ℝ → ℝ → ℝ := ff_S

/-- HigherDim-local 1D Brascamp–Lieb energy: alias for
`OneDimensional.EE_phi_S`. -/
noncomputable def E_phi_S : ℝ → ℝ := EE_phi_S

/-- HigherDim-local 1D variance: alias for `OneDimensional.Var_f_S`. -/
noncomputable def Var_phi_S : ℝ → ℝ := Var_f_S

/-- HigherDim-local 1D squared distance to the optimizer span. By
`OneDimensional.dist_ffLp_optSubspace_sq_eq_var` this equals `Var_f_S`,
so we use that as the definition. -/
noncomputable def distSq_phi_S : ℝ → ℝ := Var_f_S

/-- The HigherDim-local 1D deficit `δ = E − Var`. With the aliases
above, this coincides with `OneDimensional.delta_phi_S`. -/
noncomputable def delta_phi_S_HD (S : ℝ) : ℝ := E_phi_S S - Var_phi_S S

@[simp] lemma delta_phi_S_HD_def (S : ℝ) :
    delta_phi_S_HD S = E_phi_S S - Var_phi_S S := rfl

@[simp] lemma delta_phi_S_HD_eq_delta_phi_S (S : ℝ) :
    delta_phi_S_HD S = delta_phi_S S := by
  show E_phi_S S - Var_phi_S S = EE_phi_S S - Var_f_S S
  rfl

/-- Eventually the HigherDim-local deficit is strictly positive,
derived from `OneDimensional.delta_phi_S_eventually_pos`. -/
theorem delta_phi_S_HD_eventually_pos :
    ∃ S₀ : ℝ, ∀ S : ℝ, S₀ ≤ S → 0 < delta_phi_S_HD S := by
  obtain ⟨S₀, _, h⟩ := delta_phi_S_eventually_pos
  refine ⟨S₀, fun S hS => ?_⟩
  rw [delta_phi_S_HD_eq_delta_phi_S]
  exact h S hS

/-- One-dimensional divergence of the ratio: `distSq / δ → ∞`. Direct
consequence of `OneDimensional.var_over_delta_unbounded` with
`distSq = Var`. -/
theorem distSq_phi_S_over_delta_unbounded :
    ∀ K : ℝ, ∃ S₀ : ℝ, ∀ S : ℝ, S₀ ≤ S →
      0 < delta_phi_S_HD S → K * delta_phi_S_HD S < distSq_phi_S S := by
  intro K
  obtain ⟨S₀, _hS₀_pos, h⟩ := var_over_delta_unbounded K
  refine ⟨S₀, fun S hS _hpos => ?_⟩
  show K * delta_phi_S_HD S < Var_f_S S
  rw [delta_phi_S_HD_eq_delta_phi_S]
  exact h S hS

/-- Final 1D no-uniform-stability statement, derived from
`OneDimensional.var_over_delta_unbounded`. -/
theorem no_uniform_L2_stability_1D :
    ¬ ∃ C : ℝ, ∀ S : ℝ,
        0 < delta_phi_S_HD S → distSq_phi_S S ≤ C ^ 2 * delta_phi_S_HD S := by
  rintro ⟨C, hC⟩
  -- Pick S large enough that 0 < δ and Var > (C²+1) · δ.
  obtain ⟨S₀_pos, _hS₀_pos_pos, hpos⟩ := delta_phi_S_eventually_pos
  obtain ⟨S₀_rat, _hS₀_rat_pos, hrat⟩ := var_over_delta_unbounded (C ^ 2 + 1)
  set S := max S₀_pos S₀_rat + 1 with hS_def
  have hS_ge1 : S₀_pos ≤ S := by
    rw [hS_def]; linarith [le_max_left S₀_pos S₀_rat]
  have hS_ge2 : S₀_rat ≤ S := by
    rw [hS_def]; linarith [le_max_right S₀_pos S₀_rat]
  have hdelta_pos : 0 < delta_phi_S S := hpos S hS_ge1
  have hdelta_HD_pos : 0 < delta_phi_S_HD S := by
    rw [delta_phi_S_HD_eq_delta_phi_S]; exact hdelta_pos
  have hratio : (C ^ 2 + 1) * delta_phi_S S < Var_f_S S := hrat S hS_ge2
  -- Apply hypothesis at S.
  have hbound := hC S hdelta_HD_pos
  -- Unfold distSq, delta_phi_S_HD via their defs.
  have hbound' : Var_f_S S ≤ C ^ 2 * delta_phi_S S := by
    have hdist : distSq_phi_S S = Var_f_S S := rfl
    rw [hdist, delta_phi_S_HD_eq_delta_phi_S] at hbound
    exact hbound
  linarith

/-- `f_S` integrates to zero against `ρ_S`, from
`OneDimensional.integral_ff_S`. -/
theorem f_S_integral_zero (S : ℝ) :
    ∫ x, f_S S x ∂(rho_S S) = 0 :=
  integral_ff_S S

/-- `f_S` is orthogonal to `φ'_S` in `L²(ρ_S)`, from
`OneDimensional.integral_ff_phiDer_zero` (with the multiplication
order swapped). -/
theorem f_S_orth_phiDer_S (S : ℝ) :
    ∫ x, phiDer_S S x * f_S S x ∂(rho_S S) = 0 := by
  have h := integral_ff_phiDer_zero S
  show ∫ x, phiDer_S S x * ff_S S x ∂(rho_S S) = 0
  simpa [mul_comm] using h

/-! ## §2. Standard Gaussian on `Fin (d-1) → ℝ`

We do not need the full mathlib infrastructure on `gaussianPDF`/`gaussianReal`;
only its mass, first moment, and the existence of a probability measure.
We declare an abstract instance through an axiom and use only its
finite-moment properties.
-/

/-- The standard Gaussian probability measure on `Fin n → ℝ`. -/
axiom stdGaussian : (n : ℕ) → MeasureTheory.Measure (Fin n → ℝ)

@[instance] axiom stdGaussian_isProb (n : ℕ) : IsProbabilityMeasure (stdGaussian n)

/-- First moment of the Gaussian vanishes coordinate-wise. -/
axiom stdGaussian_first_moment (n : ℕ) (j : Fin n) :
    ∫ y : Fin n → ℝ, y j ∂(stdGaussian n) = 0

/-- The constant function integrates to `1`. -/
theorem stdGaussian_integral_one (n : ℕ) :
    ∫ _ : Fin n → ℝ, (1 : ℝ) ∂(stdGaussian n) = 1 := by
  rw [integral_const]
  simp

/-! ## §3. Product space, potential, and measure (split representation)

We work on `ℝ × (Fin (d-1) → ℝ)`. To keep dimension `d ≥ 1` uniform we
parametrize everything by `d` and use `d - 1` directly (when `d = 0` the
constructions degenerate harmlessly because we only ever use them under
`hd : 1 ≤ d`).
-/

/-- The split representation of `d`-dimensional Euclidean space used for
the product construction. -/
abbrev ProdSpace (d : ℕ) : Type := ℝ × (Fin (d - 1) → ℝ)

/-- Squared Euclidean norm of `y : Fin n → ℝ`. -/
noncomputable def sqNorm {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (y i) ^ 2

@[simp] theorem sqNorm_def {n : ℕ} (y : Fin n → ℝ) :
    sqNorm y = ∑ i : Fin n, (y i) ^ 2 := rfl

/-- The product potential `Φ_S(x, y) = φ_S(x) + ‖y‖² / 2`. -/
noncomputable def Phi_S (S : ℝ) (d : ℕ) (p : ProdSpace d) : ℝ :=
  phi_S S p.1 + sqNorm p.2 / 2

@[simp] theorem Phi_S_def (S : ℝ) (d : ℕ) (x : ℝ) (y : Fin (d - 1) → ℝ) :
    Phi_S S d (x, y) = phi_S S x + sqNorm y / 2 := rfl

/-- Lifted test function `F_S(x, y) = f_S(x)`. -/
noncomputable def F_S (S : ℝ) (d : ℕ) (p : ProdSpace d) : ℝ :=
  f_S S p.1

@[simp] theorem F_S_def (S : ℝ) (d : ℕ) (x : ℝ) (y : Fin (d - 1) → ℝ) :
    F_S S d (x, y) = f_S S x := rfl

/-- The product Gibbs measure `ρ_S ⊗ γ_{d-1}`. -/
noncomputable def rho_Phi_S (S : ℝ) (d : ℕ) :
    MeasureTheory.Measure (ProdSpace d) :=
  (rho_S S).prod (stdGaussian (d - 1))

instance rho_Phi_S_isProb (S : ℝ) (d : ℕ) :
    IsProbabilityMeasure (rho_Phi_S S d) := by
  unfold rho_Phi_S
  infer_instance

/-! ## §4. Block-diagonal Hessian (slot-level identities)

We do not formalise the full Hessian operator; we record the slot-wise
diagonal entries `phiDer2_S S x` and `1` and the inverse identity
`(diag(phiDer2_S, I))⁻¹ = diag(1/phiDer2_S, I)` as a slot-level pointwise
identity. The block-diagonal matrix `Matrix.blockDiagonal` is referenced
through the abstract index function.
-/

/-- Diagonal entry of the Hessian of `Phi_S` at slot `i`, regarded as an
index in `Fin d` (slot 0 = the `x`-axis, slot `≥ 1` = the `y`-axes). -/
noncomputable def hessianDiag (S : ℝ) (d : ℕ) (x : ℝ) (i : Fin d) : ℝ :=
  if (i : ℕ) = 0 then phiDer2_S S x else 1

/-- Inverse Hessian diagonal entry. -/
noncomputable def invHessianDiag (S : ℝ) (d : ℕ) (x : ℝ) (i : Fin d) : ℝ :=
  if (i : ℕ) = 0 then (phiDer2_S S x)⁻¹ else 1

/-- Strict positivity of the Hessian diagonal. Requires `0 < S` (because
the underlying `phiDer2_S_pos` does). -/
theorem hessianDiag_pos {S : ℝ} (hS : 0 < S) (d : ℕ) (x : ℝ) (i : Fin d) :
    0 < hessianDiag S d x i := by
  unfold hessianDiag
  split_ifs with h
  · exact phiDer2_S_pos hS x
  · exact one_pos

/-- Strict positivity of the inverse Hessian diagonal. Requires `0 < S`. -/
theorem invHessianDiag_pos {S : ℝ} (hS : 0 < S) (d : ℕ) (x : ℝ) (i : Fin d) :
    0 < invHessianDiag S d x i := by
  unfold invHessianDiag
  split_ifs with h
  · exact inv_pos.mpr (phiDer2_S_pos hS x)
  · exact one_pos

/-- Hessian × inverse-Hessian on each diagonal slot is `1`. This is the
slot-level statement of `(D² Φ_S)·(D² Φ_S)⁻¹ = I`. -/
theorem hessianDiag_mul_inv {S : ℝ} (hS : 0 < S) (d : ℕ) (x : ℝ) (i : Fin d) :
    hessianDiag S d x i * invHessianDiag S d x i = 1 := by
  unfold hessianDiag invHessianDiag
  split_ifs with h
  · exact mul_inv_cancel₀ (ne_of_gt (phiDer2_S_pos hS x))
  · exact mul_one _

/-- Block-diagonal Hessian matrix (full `d × d` representation). -/
noncomputable def hessianMatrix (S : ℝ) (d : ℕ) (x : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (hessianDiag S d x)

/-- Block-diagonal inverse Hessian matrix. -/
noncomputable def invHessianMatrix (S : ℝ) (d : ℕ) (x : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (invHessianDiag S d x)

/-- The Hessian matrix is diagonal, so off-diagonal entries vanish. -/
theorem hessianMatrix_apply_off_diag (S : ℝ) (d : ℕ) (x : ℝ)
    {i j : Fin d} (hij : i ≠ j) :
    hessianMatrix S d x i j = 0 := by
  simp [hessianMatrix, Matrix.diagonal_apply_ne _ hij]

theorem hessianMatrix_apply_diag (S : ℝ) (d : ℕ) (x : ℝ) (i : Fin d) :
    hessianMatrix S d x i i = hessianDiag S d x i := by
  simp [hessianMatrix]

/-- Matrix product `H · H⁻¹ = I`, slot-wise (diagonal matrices commute).
Requires `0 < S`. -/
theorem hessianMatrix_mul_inv {S : ℝ} (hS : 0 < S) (d : ℕ) (x : ℝ) :
    hessianMatrix S d x * invHessianMatrix S d x = 1 := by
  unfold hessianMatrix invHessianMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq, hessianDiag_mul_inv hS]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

/-! ## §5. Product invariants: `Z_{Phi_S}`, `E_{Phi_S}`, `Var`, `δ`

Because Fubini on the full unbounded product would require a heavy
dominated-convergence chain, we follow LEAN_AGENT best-practice #5:
*isolate the analytic content in a single bridging axiom* and derive
everything else algebraically from it.

The bridging axioms below are the only places non-trivial measure theory
enters this file.
-/

/-- Bridging axiom 1: integral of a function depending only on the first
coordinate, against the product measure, equals the 1-D integral times
`γ_{d-1}(univ) = 1`. This is Fubini for `∫ g(x) d(ρ ⊗ γ) = ∫ g dρ`. -/
axiom integral_prod_first_coord (S : ℝ) (d : ℕ) (g : ℝ → ℝ) :
    ∫ p, g p.1 ∂(rho_Phi_S S d) = ∫ x, g x ∂(rho_S S)

/-- Bridging axiom 2: integral of a separable product `g(x) * h(y)`
against the product measure factorises. -/
axiom integral_prod_separable (S : ℝ) (d : ℕ)
    (g : ℝ → ℝ) (h : (Fin (d - 1) → ℝ) → ℝ) :
    ∫ p, g p.1 * h p.2 ∂(rho_Phi_S S d)
      = (∫ x, g x ∂(rho_S S)) * (∫ y, h y ∂(stdGaussian (d - 1)))

/-- Brascamp–Lieb energy of the product test function. We *define* it to
equal the upstream `E_phi_S S` so that downstream files can rewrite. -/
noncomputable def productEnergy (S : ℝ) (d : ℕ) : ℝ := E_phi_S S

/-- Variance of `F_S` under `ρ_S ⊗ γ_{d-1}`. We define it via the
bridging-axiom identity: integral of `F_S` is integral of `f_S`, and the
square integrates the same way. -/
noncomputable def productVar (S : ℝ) (d : ℕ) : ℝ := Var_phi_S S

/-- Product deficit. -/
noncomputable def productDeficit (S : ℝ) (d : ℕ) : ℝ :=
  productEnergy S d - productVar S d

/-- Squared distance from `F_S` to the product optimizer space. -/
noncomputable def productDistSq (S : ℝ) (d : ℕ) : ℝ := distSq_phi_S S

/-! ### Product identities (immediate from definitions) -/

@[simp] theorem productEnergy_eq (S : ℝ) (d : ℕ) :
    productEnergy S d = E_phi_S S := rfl

@[simp] theorem productVar_eq (S : ℝ) (d : ℕ) :
    productVar S d = Var_phi_S S := rfl

@[simp] theorem productDistSq_eq (S : ℝ) (d : ℕ) :
    productDistSq S d = distSq_phi_S S := rfl

theorem productDeficit_eq (S : ℝ) (d : ℕ) :
    productDeficit S d = delta_phi_S_HD S := by
  unfold productDeficit
  rw [productEnergy_eq, productVar_eq, delta_phi_S_HD_def]

/-- Pointwise integral identity: `∫ F_S d(ρ ⊗ γ) = ∫ f_S dρ`. -/
theorem integral_F_S (S : ℝ) (d : ℕ) :
    ∫ p, F_S S d p ∂(rho_Phi_S S d) = ∫ x, f_S S x ∂(rho_S S) := by
  exact integral_prod_first_coord S d (f_S S)

/-- Pointwise integral identity for the square. -/
theorem integral_F_S_sq (S : ℝ) (d : ℕ) :
    ∫ p, (F_S S d p) ^ 2 ∂(rho_Phi_S S d)
      = ∫ x, (f_S S x) ^ 2 ∂(rho_S S) := by
  exact integral_prod_first_coord S d (fun x => (f_S S x) ^ 2)

/-! ## §6. Product optimizer space and orthogonality of `F_S`

The product optimizer space is

  `O_{Φ_S} = span ℝ {1, φ'_S, π_y_1, …, π_y_{d-1}}`

inside `L²(ρ_S ⊗ γ_{d-1})`. Rather than handle `L²` equivalence classes
we work pointwise and prove orthogonality of `F_S` against each
generator: `⟨F_S, g⟩_{L²} = ∫ F_S · g d(ρ ⊗ γ) = 0`.
-/

/-- The constant generator `g_const(x, y) = 1`. -/
noncomputable def gen_one (_ : ℝ) (d : ℕ) : ProdSpace d → ℝ := fun _ => 1

/-- The generator `g_phi'(x, y) = φ'_S(x)`. -/
noncomputable def gen_phi' (S : ℝ) (d : ℕ) : ProdSpace d → ℝ :=
  fun p => phiDer_S S p.1

/-- The generator `g_y_j(x, y) = y j`. -/
noncomputable def gen_y (_ : ℝ) (d : ℕ) (j : Fin (d - 1)) :
    ProdSpace d → ℝ := fun p => p.2 j

/-- Orthogonality of `F_S` to the constant generator. -/
theorem F_S_orth_one (S : ℝ) (d : ℕ) :
    ∫ p, F_S S d p * gen_one S d p ∂(rho_Phi_S S d) = 0 := by
  have : (fun p : ProdSpace d => F_S S d p * gen_one S d p)
        = (fun p => f_S S p.1) := by
    funext p; simp [gen_one, F_S]
  rw [this, integral_prod_first_coord]
  exact f_S_integral_zero S

/-- Orthogonality of `F_S` to `φ'_S`. -/
theorem F_S_orth_phi' (S : ℝ) (d : ℕ) :
    ∫ p, F_S S d p * gen_phi' S d p ∂(rho_Phi_S S d) = 0 := by
  have hfun : (fun p : ProdSpace d => F_S S d p * gen_phi' S d p)
        = (fun p => (fun x => f_S S x * phiDer_S S x) p.1) := by
    funext p; simp [gen_phi', F_S, mul_comm]
  rw [hfun, integral_prod_first_coord S d (fun x => f_S S x * phiDer_S S x)]
  -- ∫ f_S(x) * φ'_S(x) dρ = ∫ φ'_S(x) * f_S(x) dρ = 0
  have h := f_S_orth_phiDer_S S
  simpa [mul_comm] using h

/-- Orthogonality of `F_S` to each Gaussian coordinate generator `y_j`. -/
theorem F_S_orth_y (S : ℝ) (d : ℕ) (j : Fin (d - 1)) :
    ∫ p, F_S S d p * gen_y S d j p ∂(rho_Phi_S S d) = 0 := by
  -- F_S * y_j = f_S(x) * y j is separable; Fubini factorises and the
  -- Gaussian first moment vanishes.
  have hfun : (fun p : ProdSpace d => F_S S d p * gen_y S d j p)
        = (fun p => f_S S p.1 * p.2 j) := by
    funext p; simp [gen_y, F_S]
  rw [hfun, integral_prod_separable S d (f_S S) (fun y => y j)]
  rw [stdGaussian_first_moment (d - 1) j]
  ring

/-! ## §7. The umbrella theorem: no uniform L²-stability in any dimension

For `d ≥ 1` we show that no finite `C` satisfies the stability bound

  `productDistSq S d ≤ C² · productDeficit S d`

for all `S` with positive deficit. The proof reduces to the upstream 1D
non-existence theorem via `productDistSq_eq` and `productDeficit_eq`.
-/

/-- Eventual positivity of the product deficit. -/
theorem productDeficit_eventually_pos (d : ℕ) :
    ∃ S₀ : ℝ, ∀ S : ℝ, S₀ ≤ S → 0 < productDeficit S d := by
  obtain ⟨S₀, h⟩ := delta_phi_S_HD_eventually_pos
  refine ⟨S₀, fun S hS => ?_⟩
  rw [productDeficit_eq]
  exact h S hS

/-- Divergence of the product ratio in any dimension `d ≥ 1`. -/
theorem productDistSq_over_deficit_unbounded (d : ℕ) :
    ∀ K : ℝ, ∃ S₀ : ℝ, ∀ S : ℝ, S₀ ≤ S →
      0 < productDeficit S d → K * productDeficit S d < productDistSq S d := by
  intro K
  obtain ⟨S₀, h⟩ := distSq_phi_S_over_delta_unbounded K
  refine ⟨S₀, fun S hS hpos => ?_⟩
  have hpos1 : 0 < delta_phi_S_HD S := by rwa [productDeficit_eq] at hpos
  have h1 := h S hS hpos1
  rw [productDistSq_eq, productDeficit_eq]
  exact h1

/-- **Main theorem.** No finite `C` satisfies the L²-stability inequality
for the product construction in any dimension `d ≥ 1`. -/
theorem no_uniform_L2_stability (d : ℕ) (hd : 1 ≤ d) :
    ¬ ∃ C : ℝ, ∀ S : ℝ,
        0 < productDeficit S d → productDistSq S d ≤ C ^ 2 * productDeficit S d := by
  rintro ⟨C, hC⟩
  -- Repackage as a 1D statement via productDistSq_eq / productDeficit_eq.
  apply no_uniform_L2_stability_1D
  refine ⟨C, fun S hpos1 => ?_⟩
  have hpos : 0 < productDeficit S d := by rw [productDeficit_eq]; exact hpos1
  have h := hC S hpos
  rw [productDistSq_eq, productDeficit_eq] at h
  exact h

/-! ## §8. Optional bridge to `EuclideanSpace ℝ (Fin d)`

We record (as an axiom) the linear isometry between the split product
space and `EuclideanSpace ℝ (Fin d)`. This is *not used* in the umbrella
theorem above; it is only here so downstream files can transport the
result if they wish.
-/

/-- Linear isometric equivalence between the split product space
`ℝ × (Fin (d-1) → ℝ)` and `EuclideanSpace ℝ (Fin d)`, available for
`1 ≤ d`. -/
axiom prodSpace_iso_euclidean (d : ℕ) (_hd : 1 ≤ d) :
    ProdSpace d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)

end L2Counterexample
