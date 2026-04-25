import Mathlib

/-!
# Basic setup (WIP)

This is the editable WIP version of `Basic.lean`. It collects the small,
cross-file conventions and elementary lemmas used throughout the
`L2Counterexample` development.

The contents are deliberately lean and focused: only items that we expect
downstream files (`Bump`, `Potential`, `Normalization`, `TestFunction`,
`OneDimensional`, `HigherDimensional`) to actually reuse live here.

Contents:

* parity lemmas: integral of an odd function over `ℝ` or over a symmetric
  interval is zero, parity of standard compositions (`Real.exp ∘ (-f)`,
  `|f|`), and parity of derivatives of even / odd smooth functions;
* positivity and eventual-positivity helpers for the parameter `S → ∞`
  (used by the asymptotic estimates).

Every genuinely Mathlib-adjacent helper that does not already live in
Mathlib is tagged with `-- to_mathlib: ...`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace L2Counterexample

/-! ## Parity and symmetric integrals -/

section Parity

variable {f : ℝ → ℝ}

-- to_mathlib: Mathlib/MeasureTheory/Integral/Bochner.lean
/-- The integral of an integrable odd real-valued function over `ℝ` is zero. -/
theorem integral_eq_zero_of_odd (hf : Function.Odd f) (_hInt : Integrable f) :
    ∫ x, f x = 0 := by
  -- The Lebesgue measure on `ℝ` is invariant under negation, so
  -- `∫ x, f (-x) = ∫ x, f x`. Combined with oddness this forces the integral
  -- to equal its own negation.
  have h1 : ∫ x, f (-x) = ∫ x, f x := integral_neg_eq_self f volume
  have h2 : ∫ x, f (-x) = -∫ x, f x := by
    have hpt : ∀ x, f (-x) = -f x := hf
    simp only [hpt, integral_neg]
  have hzero : ∫ x, f x = -∫ x, f x := h1.symm.trans h2
  linarith

-- to_mathlib: Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean
/-- The oriented interval integral of an odd real-valued function over a
symmetric interval `(-a..a)` is zero. No integrability hypothesis is
needed: the interval integral is defined through `-` and both halves
cancel by the change of variables `x ↦ -x`. -/
theorem intervalIntegral_eq_zero_of_odd (hf : Function.Odd f) (a : ℝ) :
    ∫ x in (-a)..a, f x = 0 := by
  have hcomp : ∫ x in (-a)..a, f (-x) = ∫ x in (-a)..a, f x := by
    have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) (f := f)
    rw [neg_neg] at h
    exact h
  have hneg : ∫ x in (-a)..a, f (-x) = -∫ x in (-a)..a, f x := by
    have heq : (fun x => f (-x)) = fun x => -f x := funext hf
    rw [heq, intervalIntegral.integral_neg]
  have h : ∫ x in (-a)..a, f x = -∫ x in (-a)..a, f x := hcomp.symm.trans hneg
  linarith

end Parity

/-! ## Parity of common compositions -/

/-- The real exponential of the negation of an even function is even. -/
theorem Real.exp_neg_comp_even {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (fun x => Real.exp (-(f x))) := fun x => by
  simp [hf x]

/-- If `f` is even, then `|f|` is even. -/
theorem abs_comp_even {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (fun x => |f x|) := fun x => by
  simp [hf x]

/-- If `f` is odd, then `|f|` is even. -/
theorem abs_comp_odd {f : ℝ → ℝ} (hf : Function.Odd f) :
    Function.Even (fun x => |f x|) := fun x => by
  simp [hf x, abs_neg]

/-! ## Parity of derivatives

The derivative of an even real function is odd, and vice versa. These are
straightforward applications of the chain rule through `x ↦ -x`. -/

-- to_mathlib: Mathlib/Analysis/Calculus/Deriv/Basic.lean
/-- If `f : ℝ → ℝ` is differentiable and even, then `deriv f` is odd. -/
theorem deriv_odd_of_even {f : ℝ → ℝ} (hf : Function.Even f)
    (hdiff : Differentiable ℝ f) : Function.Odd (deriv f) := by
  intro x
  -- Differentiate the identity `f (-x) = f x`.
  have hneg : HasDerivAt (fun y : ℝ => f (-y)) (- deriv f (-x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).neg
    have h2 : HasDerivAt f (deriv f (-x)) (-x) := (hdiff (-x)).hasDerivAt
    have h3 : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * (-1)) x := h2.comp x h1
    simpa [mul_comm] using h3
  have hfeq : (fun y : ℝ => f (-y)) = f := funext hf
  have hfderiv : HasDerivAt f (- deriv f (-x)) x := by
    simpa [hfeq] using hneg
  have : deriv f x = - deriv f (-x) := hfderiv.deriv
  linarith

-- to_mathlib: Mathlib/Analysis/Calculus/Deriv/Basic.lean
/-- If `f : ℝ → ℝ` is differentiable and odd, then `deriv f` is even. -/
theorem deriv_even_of_odd {f : ℝ → ℝ} (hf : Function.Odd f)
    (hdiff : Differentiable ℝ f) : Function.Even (deriv f) := by
  intro x
  -- Differentiate the identity `f (-x) = -f x`.
  have hneg : HasDerivAt (fun y : ℝ => f (-y)) (- deriv f (-x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).neg
    have h2 : HasDerivAt f (deriv f (-x)) (-x) := (hdiff (-x)).hasDerivAt
    have h3 : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * (-1)) x := h2.comp x h1
    simpa [mul_comm] using h3
  have hfeq : (fun y : ℝ => f (-y)) = fun y => -f y := funext hf
  have hderivNeg : HasDerivAt (fun y : ℝ => -f y) (- deriv f x) x :=
    ((hdiff x).hasDerivAt).neg
  have hderivNeg' : HasDerivAt (fun y : ℝ => -f y) (- deriv f (-x)) x := by
    simpa [hfeq] using hneg
  have hunique : - deriv f (-x) = - deriv f x :=
    hderivNeg'.unique hderivNeg
  linarith

/-! ## Positivity helpers for real powers and the filter `atTop` -/

/-- For `S > 0` and any real exponent `k`, `S ^ (-k)` is positive. -/
theorem rpow_neg_pos {S : ℝ} (hS : 0 < S) (k : ℝ) : 0 < S ^ (-k) :=
  Real.rpow_pos_of_pos hS _

/-- For `S > 0` and `k : ℕ`, `S ^ (-(k : ℤ))` is positive. -/
theorem zpow_neg_natCast_pos {S : ℝ} (hS : 0 < S) (k : ℕ) : 0 < S ^ (-(k : ℤ)) := by
  have hne : S ≠ 0 := ne_of_gt hS
  have hpos : 0 < S ^ (k : ℤ) := by
    rw [zpow_natCast]
    exact pow_pos hS k
  rw [zpow_neg]
  exact inv_pos.mpr hpos

/-- `S ↦ S ^ (-(k : ℤ))` tends to `0` as `S → ∞`, for any positive natural `k`. -/
theorem tendsto_zpow_neg_natCast_atTop_zero {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun S : ℝ => S ^ (-(k : ℤ))) atTop (𝓝 0) := by
  have hlt : (-(k : ℤ)) < 0 := by
    have : (0 : ℤ) < (k : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    omega
  exact tendsto_zpow_atTop_zero hlt

/-- Convenient restatement: `S > 0` eventually as `S → ∞`. -/
theorem eventually_pos_atTop : ∀ᶠ S : ℝ in atTop, 0 < S :=
  Filter.eventually_gt_atTop 0

/-- `S ≥ 1` eventually as `S → ∞`. -/
theorem eventually_one_le_atTop : ∀ᶠ S : ℝ in atTop, (1 : ℝ) ≤ S :=
  Filter.eventually_ge_atTop 1

/-- For any `c`, `c < S` eventually as `S → ∞`. -/
theorem eventually_gt_atTop (c : ℝ) : ∀ᶠ S : ℝ in atTop, c < S :=
  Filter.eventually_gt_atTop c

end L2Counterexample
