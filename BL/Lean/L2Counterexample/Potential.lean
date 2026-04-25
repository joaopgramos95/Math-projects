import L2Counterexample.Bump

/-!
# One-dimensional potential

This file defines:

* the generic `psi`, `phi` reconstructions of a smooth function `h` from an
  oriented-interval integral chain (`big_tasks.md` task #2);
* the scaled potential family `phi''_S`, `phi'_S`, `phi_S` associated to the
  parameters `epsilon = S^{-3}`, `eta = S^{-4}`
  (`big_tasks.md` task #3, `sections/02_construction_and_profile.md` items 2–8).

The smooth even probability bump `kappa` is imported from
`L2Counterexample.Bump`.
-/

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped Topology ContDiff

namespace L2Counterexample

/-! ## Generic reconstruction from a prescribed second derivative

For a smooth `h : ℝ → ℝ` we set

    psi h x = ∫ t in (0)..x, h t,
    phi h x = ∫ u in (0)..x, psi h u.
-/

/-- First antiderivative of `h`, normalised to vanish at `0`. -/
def psi (h : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, h t

/-- Second antiderivative of `h`, normalised to vanish at `0`. -/
def phi (h : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, psi h u

@[simp] lemma psi_zero (h : ℝ → ℝ) : psi h 0 = 0 := by
  unfold psi; simp

@[simp] lemma phi_zero (h : ℝ → ℝ) : phi h 0 = 0 := by
  unfold phi; simp

/-! ### Derivatives -/

/-- `psi h` has derivative `h x` at every point, when `h` is continuous. -/
lemma hasDerivAt_psi {h : ℝ → ℝ} (hcont : Continuous h) (x : ℝ) :
    HasDerivAt (psi h) (h x) x := by
  have hint : IntervalIntegrable h volume 0 x := hcont.intervalIntegrable _ _
  have hmeas : StronglyMeasurableAtFilter h (𝓝 x) :=
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter
  exact integral_hasDerivAt_right hint hmeas hcont.continuousAt

lemma deriv_psi_apply {h : ℝ → ℝ} (hcont : Continuous h) (x : ℝ) :
    deriv (psi h) x = h x :=
  (hasDerivAt_psi hcont x).deriv

lemma deriv_psi {h : ℝ → ℝ} (hcont : Continuous h) :
    deriv (psi h) = h :=
  funext fun x => deriv_psi_apply hcont x

lemma psi_differentiable {h : ℝ → ℝ} (hcont : Continuous h) :
    Differentiable ℝ (psi h) :=
  fun x => (hasDerivAt_psi hcont x).differentiableAt

lemma psi_continuous {h : ℝ → ℝ} (hcont : Continuous h) : Continuous (psi h) :=
  (psi_differentiable hcont).continuous

/-- `phi h` has derivative `psi h x` at every point, when `h` is continuous. -/
lemma hasDerivAt_phi {h : ℝ → ℝ} (hcont : Continuous h) (x : ℝ) :
    HasDerivAt (phi h) (psi h x) x := by
  have hcont_psi : Continuous (psi h) := psi_continuous hcont
  have hint : IntervalIntegrable (psi h) volume 0 x :=
    hcont_psi.intervalIntegrable _ _
  have hmeas : StronglyMeasurableAtFilter (psi h) (𝓝 x) :=
    hcont_psi.stronglyMeasurable.stronglyMeasurableAtFilter
  exact integral_hasDerivAt_right hint hmeas hcont_psi.continuousAt

lemma deriv_phi_apply {h : ℝ → ℝ} (hcont : Continuous h) (x : ℝ) :
    deriv (phi h) x = psi h x :=
  (hasDerivAt_phi hcont x).deriv

lemma deriv_phi {h : ℝ → ℝ} (hcont : Continuous h) :
    deriv (phi h) = psi h :=
  funext fun x => deriv_phi_apply hcont x

lemma phi_differentiable {h : ℝ → ℝ} (hcont : Continuous h) :
    Differentiable ℝ (phi h) :=
  fun x => (hasDerivAt_phi hcont x).differentiableAt

lemma phi_continuous {h : ℝ → ℝ} (hcont : Continuous h) : Continuous (phi h) :=
  (phi_differentiable hcont).continuous

/-- Second derivative of `phi h` equals `h`. -/
lemma deriv_deriv_phi {h : ℝ → ℝ} (hcont : Continuous h) :
    deriv (deriv (phi h)) = h := by
  rw [deriv_phi hcont, deriv_psi hcont]

/-! ### Smoothness -/

lemma psi_contDiff {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (psi h) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨psi_differentiable hsmooth.continuous, ?_⟩
  rw [deriv_psi hsmooth.continuous]
  exact hsmooth

lemma phi_contDiff {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (phi h) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨phi_differentiable hsmooth.continuous, ?_⟩
  rw [deriv_phi hsmooth.continuous]
  exact psi_contDiff hsmooth

/-! ### Parity

If `h` is even then `psi h` is odd and `phi h` is even. -/

/-- If `h` is even then `psi h` is odd. -/
lemma psi_neg_of_even {h : ℝ → ℝ} (heven : ∀ x, h (-x) = h x) (x : ℝ) :
    psi h (-x) = -psi h x := by
  -- `psi h (-x) = ∫ t in 0..(-x), h t`.
  unfold psi
  -- Rewrite the target integral using `integral_symm`: `∫ in 0..(-x) = - ∫ in (-x)..0`.
  have hsym : ∫ t in (0:ℝ)..(-x), h t = - ∫ t in (-x:ℝ)..0, h t :=
    integral_symm (-x) 0
  rw [hsym]
  -- And `∫ t in -x..0, h t = ∫ t in 0..x, h (-t)` by `integral_comp_neg`.
  have hcomp : ∫ t in (0:ℝ)..x, h (-t) = ∫ t in (-x:ℝ)..(-0), h t := by
    simpa using integral_comp_neg (a := 0) (b := x) (f := h)
  have hcomp' : ∫ t in (-x:ℝ)..0, h t = ∫ t in (0:ℝ)..x, h (-t) := by
    have := hcomp
    simpa using this.symm
  rw [hcomp']
  -- Now use evenness pointwise.
  have heq : ∫ t in (0:ℝ)..x, h (-t) = ∫ t in (0:ℝ)..x, h t := by
    apply integral_congr
    intro t _
    exact heven t
  rw [heq]

/-- If `h` is even then `phi h` is even. -/
lemma phi_neg_of_even {h : ℝ → ℝ} (heven : ∀ x, h (-x) = h x) (x : ℝ) :
    phi h (-x) = phi h x := by
  unfold phi
  -- `phi h (-x) = ∫ u in 0..(-x), psi h u`.
  have hsym : ∫ u in (0:ℝ)..(-x), psi h u = - ∫ u in (-x:ℝ)..0, psi h u :=
    integral_symm (-x) 0
  rw [hsym]
  have hcomp' : ∫ u in (-x:ℝ)..0, psi h u = ∫ u in (0:ℝ)..x, psi h (-u) := by
    have := (integral_comp_neg (a := 0) (b := x) (f := psi h))
    -- `integral_comp_neg`: `∫ t in a..b, f (-t) = ∫ t in -b..-a, f t`
    -- so `∫ u in 0..x, psi h (-u) = ∫ u in -x..0, psi h u`.
    simpa using this.symm
  rw [hcomp']
  -- Substitute `psi h (-u) = - psi h u`.
  have heq : ∫ u in (0:ℝ)..x, psi h (-u) = ∫ u in (0:ℝ)..x, - psi h u := by
    apply integral_congr
    intro u _
    exact psi_neg_of_even heven u
  rw [heq]
  rw [intervalIntegral.integral_neg]
  ring

/-! ### Strict convexity and quadratic lower bound

If `h x ≥ η > 0` everywhere then `phi h` is strictly convex and
`phi h x ≥ η·x^2/2`. -/

/-- Strict convexity of `phi h` from a strict lower bound on `h`. -/
lemma strictConvexOn_phi {h : ℝ → ℝ} {η : ℝ} (hcont : Continuous h)
    (hη : 0 < η) (hlb : ∀ x, η ≤ h x) :
    StrictConvexOn ℝ Set.univ (phi h) := by
  refine strictConvexOn_of_deriv2_pos (convex_univ) ?_ ?_
  · exact (phi_continuous hcont).continuousOn
  · intro x _
    -- `deriv^[2] (phi h) x = h x ≥ η > 0`.
    have h1 : deriv^[2] (phi h) x = h x := by
      show deriv (deriv (phi h)) x = h x
      rw [deriv_deriv_phi hcont]
    rw [h1]
    exact lt_of_lt_of_le hη (hlb x)

/-- Quadratic lower bound: if `h ≥ η > 0` then `phi h x ≥ η x²/2`. -/
lemma phi_ge_quadratic {h : ℝ → ℝ} {η : ℝ} (hcont : Continuous h)
    (hη : 0 ≤ η) (hlb : ∀ x, η ≤ h x) (x : ℝ) :
    η * x ^ 2 / 2 ≤ phi h x := by
  -- Strategy: show `g x := phi h x - η x² / 2` is nonnegative, via `g(0)=0`,
  -- `g'(0)=0` and `g'' ≥ 0`, equivalently `g` is convex with minimum at `0`.
  -- We'll instead directly bound using FTC twice:
  --   `psi h x ≥ η * x` when `x ≥ 0` and `psi h x ≤ η * x` when `x ≤ 0`.
  --   hence `phi h x ≥ η * x² / 2`.
  rcases le_or_gt 0 x with hx | hx
  · -- x ≥ 0 case.
    -- Step 1: `psi h t ≥ η t` for `t ≥ 0`.
    have hpsi_lb : ∀ t, 0 ≤ t → η * t ≤ psi h t := by
      intro t ht
      unfold psi
      -- `∫ s in 0..t, h s ≥ ∫ s in 0..t, η = η t`.
      have hint_h : IntervalIntegrable h volume 0 t := hcont.intervalIntegrable _ _
      have hint_c : IntervalIntegrable (fun _ : ℝ => η) volume 0 t :=
        continuous_const.intervalIntegrable _ _
      have hmono := integral_mono_on (a := 0) (b := t) (f := fun _ => η) (g := h)
        ht hint_c hint_h (fun s _ => hlb s)
      have hconst : ∫ _ in (0:ℝ)..t, (η : ℝ) = η * t := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      calc η * t = ∫ _ in (0:ℝ)..t, (η : ℝ) := hconst.symm
        _ ≤ ∫ s in (0:ℝ)..t, h s := hmono
    -- Step 2: `phi h x = ∫ u in 0..x, psi h u ≥ ∫ u in 0..x, η u = η x²/2`.
    unfold phi
    have hint_psi : IntervalIntegrable (psi h) volume 0 x :=
      (psi_continuous hcont).intervalIntegrable _ _
    have hint_l : IntervalIntegrable (fun u : ℝ => η * u) volume 0 x :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hmono := integral_mono_on (a := 0) (b := x) (f := fun u => η * u) (g := psi h)
      hx hint_l hint_psi (fun u hu => hpsi_lb u hu.1)
    have hlin : ∫ u in (0:ℝ)..x, η * u = η * x ^ 2 / 2 := by
      have : ∫ u in (0:ℝ)..x, η * u = η * ∫ u in (0:ℝ)..x, u := by
        rw [intervalIntegral.integral_const_mul]
      rw [this]
      rw [integral_id]
      ring
    calc η * x ^ 2 / 2 = ∫ u in (0:ℝ)..x, η * u := hlin.symm
      _ ≤ ∫ u in (0:ℝ)..x, psi h u := hmono
  · -- x < 0 case. Use the analogous bound on the negative side.
    -- Step 1': `psi h t ≤ η t` for `t ≤ 0`  (equivalently `-ψ(-t) ≤ -η t` ...).
    -- Simpler: use the same integral argument but with reversed bounds.
    -- `∫ s in 0..t, h s ≤ ∫ s in 0..t, η = η t` when `t ≤ 0`.
    have hxle : x ≤ 0 := le_of_lt hx
    have hpsi_ub : ∀ t, t ≤ 0 → psi h t ≤ η * t := by
      intro t ht
      unfold psi
      have hint_h : IntervalIntegrable h volume t 0 := hcont.intervalIntegrable _ _
      have hint_c : IntervalIntegrable (fun _ : ℝ => η) volume t 0 :=
        continuous_const.intervalIntegrable _ _
      have hmono := integral_mono_on (a := t) (b := 0) (f := fun _ => η) (g := h)
        ht hint_c hint_h (fun s _ => hlb s)
      have hconst : ∫ _ in (t:ℝ)..0, (η : ℝ) = η * (0 - t) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      -- Flip endpoints on both sides using `integral_symm`.
      have flip1 : ∫ _ in (0:ℝ)..t, (η : ℝ) = -(∫ _ in t..0, (η : ℝ)) :=
        integral_symm t 0
      have flip2 : ∫ s in (0:ℝ)..t, h s = -(∫ s in (t:ℝ)..0, h s) :=
        integral_symm t 0
      rw [flip2]
      have hneg : -(∫ s in (t:ℝ)..0, h s) ≤ -(∫ _ in (t:ℝ)..0, (η : ℝ)) := by
        linarith
      calc -(∫ s in (t:ℝ)..0, h s) ≤ -(∫ _ in (t:ℝ)..0, (η : ℝ)) := hneg
        _ = -(η * (0 - t)) := by rw [hconst]
        _ = η * t := by ring
    -- Step 2': `∫ u in 0..x, psi h u ≥ ∫ u in 0..x, η u = η x²/2` (with flipped bounds).
    unfold phi
    -- `∫ u in 0..x, psi h u = -∫ u in x..0, psi h u`
    -- and similarly for `η u`; then use `integral_mono_on` on `[x, 0]`.
    have hint_psi : IntervalIntegrable (psi h) volume x 0 :=
      (psi_continuous hcont).intervalIntegrable _ _
    have hint_l : IntervalIntegrable (fun u : ℝ => η * u) volume x 0 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hmono := integral_mono_on (a := x) (b := 0) (f := psi h) (g := fun u => η * u)
      hxle hint_psi hint_l (fun u hu => hpsi_ub u hu.2)
    have hlin : ∫ u in (x:ℝ)..0, η * u = -(η * x ^ 2 / 2) := by
      have h1 : ∫ u in (x:ℝ)..0, η * u = η * ∫ u in x..0, u := by
        rw [intervalIntegral.integral_const_mul]
      rw [h1]
      rw [integral_id]
      ring
    -- Now flip both sides.
    have hflip_psi : ∫ u in (0:ℝ)..x, psi h u = -(∫ u in x..0, psi h u) :=
      integral_symm x 0
    have hflip_lin : ∫ u in (0:ℝ)..x, η * u = -(∫ u in x..0, η * u) :=
      integral_symm x 0
    have hlin_neg : ∫ u in (0:ℝ)..x, η * u = η * x ^ 2 / 2 := by
      rw [hflip_lin, hlin]; ring
    -- From `hmono`: `∫ u in x..0, psi h u ≤ ∫ u in x..0, η u = -(η x²/2)`.
    have : ∫ u in x..0, psi h u ≤ -(η * x ^ 2 / 2) := by
      calc ∫ u in x..0, psi h u ≤ ∫ u in x..0, η * u := hmono
        _ = -(η * x ^ 2 / 2) := hlin
    have : η * x ^ 2 / 2 ≤ -(∫ u in x..0, psi h u) := by linarith
    rw [hflip_psi]
    exact this

/-! ## The scaled potential family `phi_S`

Parameters `epsilon S = S^{-3}`, `eta S = S^{-4}`. We define
`phi''_S` (as `phiPP_S`), its antiderivative `phi'_S` (`phiP_S`), and the
potential `phi_S` itself. -/

/-- Parameter `ε_S = S^{-3}`. -/
def eps_S (S : ℝ) : ℝ := S ^ (-(3 : ℤ))

/-- Parameter `η_S = S^{-4}`. -/
def eta_S (S : ℝ) : ℝ := S ^ (-(4 : ℤ))

lemma eps_S_pos {S : ℝ} (hS : 0 < S) : 0 < eps_S S := by
  unfold eps_S
  exact zpow_pos hS _

lemma eta_S_pos {S : ℝ} (hS : 0 < S) : 0 < eta_S S := by
  unfold eta_S
  exact zpow_pos hS _

/-- Scaled second derivative
`phi''_S x = η_S + (S/ε_S) · κ((x-1)/ε_S) + (S/ε_S) · κ((x+1)/ε_S)`. -/
def phiPP_S (S x : ℝ) : ℝ :=
  eta_S S
    + (S / eps_S S) * kappa ((x - 1) / eps_S S)
    + (S / eps_S S) * kappa ((x + 1) / eps_S S)

/-- Scaled first derivative `phi'_S`, defined as the oriented integral of
`phi''_S` from `0`. -/
def phiP_S (S : ℝ) : ℝ → ℝ := psi (phiPP_S S)

/-- Scaled potential `phi_S`, defined as the oriented integral of `phi'_S`
from `0`. -/
def phi_Sc (S : ℝ) : ℝ → ℝ := phi (phiPP_S S)

/-! ### Smoothness and identities for `phiPP_S`, `phiP_S`, `phi_Sc` -/

/-- `phi''_S` is smooth (for `S ≠ 0`, the shift-rescaled bumps are smooth). -/
lemma phiPP_S_contDiff {S : ℝ} (hS : 0 < S) : ContDiff ℝ ∞ (phiPP_S S) := by
  unfold phiPP_S
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => (x - 1) / eps_S S) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => (x + 1) / eps_S S) := by fun_prop
  have hk1 : ContDiff ℝ ∞ (fun x : ℝ => kappa ((x - 1) / eps_S S)) :=
    kappa_contDiff.comp h1
  have hk2 : ContDiff ℝ ∞ (fun x : ℝ => kappa ((x + 1) / eps_S S)) :=
    kappa_contDiff.comp h2
  have hs1 : ContDiff ℝ ∞ (fun x : ℝ => (S / eps_S S) * kappa ((x - 1) / eps_S S)) :=
    contDiff_const.mul hk1
  have hs2 : ContDiff ℝ ∞ (fun x : ℝ => (S / eps_S S) * kappa ((x + 1) / eps_S S)) :=
    contDiff_const.mul hk2
  exact (contDiff_const.add hs1).add hs2

lemma phiPP_S_continuous {S : ℝ} (hS : 0 < S) : Continuous (phiPP_S S) :=
  (phiPP_S_contDiff hS).continuous

lemma phiP_S_contDiff {S : ℝ} (hS : 0 < S) : ContDiff ℝ ∞ (phiP_S S) :=
  psi_contDiff (phiPP_S_contDiff hS)

lemma phi_Sc_contDiff {S : ℝ} (hS : 0 < S) : ContDiff ℝ ∞ (phi_Sc S) :=
  phi_contDiff (phiPP_S_contDiff hS)

@[simp] lemma phiP_S_zero (S : ℝ) : phiP_S S 0 = 0 := psi_zero _
@[simp] lemma phi_Sc_zero (S : ℝ) : phi_Sc S 0 = 0 := phi_zero _

lemma deriv_phi_Sc {S : ℝ} (hS : 0 < S) : deriv (phi_Sc S) = phiP_S S := by
  unfold phi_Sc phiP_S
  exact deriv_phi (phiPP_S_continuous hS)

lemma deriv_phiP_S {S : ℝ} (hS : 0 < S) : deriv (phiP_S S) = phiPP_S S := by
  unfold phiP_S
  exact deriv_psi (phiPP_S_continuous hS)

lemma deriv_deriv_phi_Sc {S : ℝ} (hS : 0 < S) :
    deriv (deriv (phi_Sc S)) = phiPP_S S := by
  rw [deriv_phi_Sc hS, deriv_phiP_S hS]

/-! ### Lower bound `phi''_S ≥ η_S` -/

/-- The quadratic layer term is nonnegative, since `κ ≥ 0` and `S/ε_S > 0`. -/
lemma phiPP_S_ge_eta {S : ℝ} (hS : 0 < S) (x : ℝ) :
    eta_S S ≤ phiPP_S S x := by
  unfold phiPP_S
  have heps_pos : 0 < eps_S S := eps_S_pos hS
  have hS_over : 0 ≤ S / eps_S S := div_nonneg hS.le heps_pos.le
  have h1 : 0 ≤ (S / eps_S S) * kappa ((x - 1) / eps_S S) :=
    mul_nonneg hS_over (kappa_nonneg _)
  have h2 : 0 ≤ (S / eps_S S) * kappa ((x + 1) / eps_S S) :=
    mul_nonneg hS_over (kappa_nonneg _)
  linarith

/-! ### Evenness of `phi''_S`, odd of `phi'_S`, evenness of `phi_Sc` -/

/-- `phi''_S` is even. -/
lemma phiPP_S_even {S : ℝ} (hS : 0 < S) (x : ℝ) : phiPP_S S (-x) = phiPP_S S x := by
  unfold phiPP_S
  have heps_ne : eps_S S ≠ 0 := (eps_S_pos hS).ne'
  -- `(-x - 1)/ε = -(x+1)/ε`, so its κ-value equals κ((x+1)/ε) by evenness.
  have ha : kappa ((-x - 1) / eps_S S) = kappa ((x + 1) / eps_S S) := by
    have : (-x - 1) / eps_S S = -((x + 1) / eps_S S) := by ring
    rw [this]
    exact kappa_even _
  have hb : kappa ((-x + 1) / eps_S S) = kappa ((x - 1) / eps_S S) := by
    have : (-x + 1) / eps_S S = -((x - 1) / eps_S S) := by ring
    rw [this]
    exact kappa_even _
  rw [show ((-x) - 1) / eps_S S = (-x - 1) / eps_S S from by ring,
      show ((-x) + 1) / eps_S S = (-x + 1) / eps_S S from by ring,
      ha, hb]
  ring

/-- `phi'_S` is odd. -/
lemma phiP_S_neg {S : ℝ} (hS : 0 < S) (x : ℝ) : phiP_S S (-x) = -phiP_S S x := by
  unfold phiP_S
  exact psi_neg_of_even (phiPP_S_even hS) x

/-- `phi_S` is even. -/
lemma phi_Sc_neg {S : ℝ} (hS : 0 < S) (x : ℝ) : phi_Sc S (-x) = phi_Sc S x := by
  unfold phi_Sc
  exact phi_neg_of_even (phiPP_S_even hS) x

/-! ### Regional formulas for `phi''_S`

**Core region**: for `|x| ≤ 1 - ε_S` (with `ε_S < 1`) both bumps vanish and
`phi''_S x = η_S`. -/

lemma phiPP_S_core {S x : ℝ} (hS : 0 < S) (hx : |x| ≤ 1 - eps_S S) :
    phiPP_S S x = eta_S S := by
  have heps_pos : 0 < eps_S S := eps_S_pos hS
  have heps_ne : eps_S S ≠ 0 := heps_pos.ne'
  -- From `|x| ≤ 1 - ε_S` we get `|x - 1|/ε_S ≥ 1` and `|x + 1|/ε_S ≥ 1`,
  -- so both bump arguments have absolute value ≥ 1, hence κ = 0.
  have habs : |x| ≤ 1 - eps_S S := hx
  have hxl : -(1 - eps_S S) ≤ x := (abs_le.mp habs).1
  have hxr : x ≤ 1 - eps_S S := (abs_le.mp habs).2
  -- `|x - 1| ≥ ε_S`: indeed `1 - x ≥ ε_S`.
  have h1 : eps_S S ≤ |x - 1| := by
    have : 1 - x ≥ eps_S S := by linarith
    have hx_le_one : x ≤ 1 := by linarith [heps_pos]
    have : x - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos this]
    linarith
  have h2 : eps_S S ≤ |x + 1| := by
    -- `x + 1 ≥ ε_S`: from `-(1 - ε_S) ≤ x` we get `x + 1 ≥ ε_S`.
    have hx1_nn : 0 ≤ x + 1 := by linarith [heps_pos]
    rw [abs_of_nonneg hx1_nn]
    linarith
  -- Therefore `|(x-1)/ε_S| ≥ 1`.
  have habs1 : 1 ≤ |(x - 1) / eps_S S| := by
    rw [abs_div, abs_of_pos heps_pos]
    rw [le_div_iff₀ heps_pos]
    rw [one_mul]
    exact h1
  have habs2 : 1 ≤ |(x + 1) / eps_S S| := by
    rw [abs_div, abs_of_pos heps_pos]
    rw [le_div_iff₀ heps_pos]
    rw [one_mul]
    exact h2
  have hk1 : kappa ((x - 1) / eps_S S) = 0 := kappa_eq_zero_of_abs_ge_one habs1
  have hk2 : kappa ((x + 1) / eps_S S) = 0 := kappa_eq_zero_of_abs_ge_one habs2
  unfold phiPP_S
  rw [hk1, hk2]
  ring

/-- Exterior region right: for `x ≥ 1 + ε_S`, both bumps vanish and
`phi''_S x = η_S`. -/
lemma phiPP_S_ext_right {S x : ℝ} (hS : 0 < S) (hx : 1 + eps_S S ≤ x) :
    phiPP_S S x = eta_S S := by
  have heps_pos : 0 < eps_S S := eps_S_pos hS
  have heps_ne : eps_S S ≠ 0 := heps_pos.ne'
  -- `x - 1 ≥ ε_S > 0` so `|x - 1| = x - 1 ≥ ε_S`, hence `|(x-1)/ε_S| ≥ 1`.
  have h1 : eps_S S ≤ x - 1 := by linarith
  have h1' : 0 ≤ x - 1 := by linarith
  have habs1 : 1 ≤ |(x - 1) / eps_S S| := by
    rw [abs_div, abs_of_pos heps_pos, abs_of_nonneg h1']
    rw [le_div_iff₀ heps_pos, one_mul]
    exact h1
  -- `x + 1 ≥ 2 + ε_S ≥ 1 + ε_S`; so `|(x+1)/ε_S| ≥ (1+ε_S)/ε_S ≥ 1`.
  have h2 : eps_S S ≤ x + 1 := by linarith
  have h2' : 0 ≤ x + 1 := by linarith
  have habs2 : 1 ≤ |(x + 1) / eps_S S| := by
    rw [abs_div, abs_of_pos heps_pos, abs_of_nonneg h2']
    rw [le_div_iff₀ heps_pos, one_mul]
    exact h2
  have hk1 : kappa ((x - 1) / eps_S S) = 0 := kappa_eq_zero_of_abs_ge_one habs1
  have hk2 : kappa ((x + 1) / eps_S S) = 0 := kappa_eq_zero_of_abs_ge_one habs2
  unfold phiPP_S
  rw [hk1, hk2]; ring

/-- Exterior region left: for `x ≤ -1 - ε_S`, both bumps vanish and
`phi''_S x = η_S`. -/
lemma phiPP_S_ext_left {S x : ℝ} (hS : 0 < S) (hx : x ≤ -1 - eps_S S) :
    phiPP_S S x = eta_S S := by
  -- Use evenness: `phi''_S x = phi''_S (-x)`, and `-x ≥ 1 + ε_S`.
  have hnx : 1 + eps_S S ≤ -x := by linarith
  have := phiPP_S_ext_right (S := S) (x := -x) hS hnx
  rw [phiPP_S_even hS] at this
  exact this

/-! ### Support scaling identities

If `κ` is supported in `[-1, 1]`, then the translated rescaled bump
`(S/ε) · κ((x-1)/ε)` is supported in `[1-ε, 1+ε]`, and
`∫_{1-ε}^{1+ε} (S/ε) · κ((x-1)/ε) dx = S`. Similarly on the left. -/

lemma kappa_scaled_integral_right {S : ℝ} (hS : 0 < S) :
    ∫ x in (1 - eps_S S)..(1 + eps_S S),
        (S / eps_S S) * kappa ((x - 1) / eps_S S) = S := by
  have heps_pos : 0 < eps_S S := eps_S_pos hS
  have heps_ne : eps_S S ≠ 0 := heps_pos.ne'
  -- Step 1: shift by `1`.
  have step1 :
      ∫ x in (1 - eps_S S)..(1 + eps_S S),
        (S / eps_S S) * kappa ((x - 1) / eps_S S)
      = ∫ x in -eps_S S..eps_S S,
          (S / eps_S S) * kappa (x / eps_S S) := by
    have h := intervalIntegral.integral_comp_sub_right
                (f := fun u => (S / eps_S S) * kappa (u / eps_S S))
                (a := 1 - eps_S S) (b := 1 + eps_S S) (d := 1)
    -- `h : ∫ x in (1-ε)..(1+ε), (S/ε) κ ((x-1)/ε)
    --      = ∫ x in (1-ε) - 1..(1+ε) - 1, (S/ε) κ (x/ε)`
    have heq1 : (1 - eps_S S) - 1 = -eps_S S := by ring
    have heq2 : (1 + eps_S S) - 1 = eps_S S := by ring
    rw [heq1, heq2] at h
    exact h
  rw [step1]
  rw [intervalIntegral.integral_const_mul]
  -- Step 3: rescale
  have step3 :
      ∫ x in -eps_S S..eps_S S, kappa (x / eps_S S)
      = eps_S S • ∫ x in (-1 : ℝ)..1, kappa x := by
    have h := intervalIntegral.integral_comp_div
                (f := kappa) (a := -eps_S S) (b := eps_S S)
                (c := eps_S S) heps_ne
    have heq1 : (-eps_S S) / eps_S S = -1 := by
      rw [neg_div, div_self heps_ne]
    have heq2 : eps_S S / eps_S S = 1 := div_self heps_ne
    rw [heq1, heq2] at h
    exact h
  rw [step3]
  rw [smul_eq_mul]
  have step4 : ∫ x in (-1:ℝ)..1, kappa x = 1 :=
    kappa_intervalIntegral (-1) 1 le_rfl le_rfl
  rw [step4, mul_one]
  field_simp

lemma kappa_scaled_integral_left {S : ℝ} (hS : 0 < S) :
    ∫ x in (-1 - eps_S S)..(-1 + eps_S S),
        (S / eps_S S) * kappa ((x + 1) / eps_S S) = S := by
  have heps_pos : 0 < eps_S S := eps_S_pos hS
  have heps_ne : eps_S S ≠ 0 := heps_pos.ne'
  -- Use the substitution `u = x + 1`, i.e. `x = u - 1`.
  -- `integral_comp_sub_right` with `d = -1` matches `f (x - (-1)) = f (x + 1)`.
  -- Use the additive shift `x ↦ x + 1`: `∫ x, f(x+1) = ∫ x in a+1..b+1, f(x)`.
  have step1 :
      ∫ x in (-1 - eps_S S)..(-1 + eps_S S),
        (S / eps_S S) * kappa ((x + 1) / eps_S S)
      = ∫ x in -eps_S S..eps_S S,
          (S / eps_S S) * kappa (x / eps_S S) := by
    -- `integral_comp_add_right`: `(∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x`.
    have h := intervalIntegral.integral_comp_add_right
                (f := fun u => (S / eps_S S) * kappa (u / eps_S S))
                (a := -1 - eps_S S) (b := -1 + eps_S S) (d := (1 : ℝ))
    have heq1 : (-1 - eps_S S) + 1 = -eps_S S := by ring
    have heq2 : (-1 + eps_S S) + 1 = eps_S S := by ring
    rw [heq1, heq2] at h
    exact h
  rw [step1]
  rw [intervalIntegral.integral_const_mul]
  have step3 :
      ∫ x in -eps_S S..eps_S S, kappa (x / eps_S S)
      = eps_S S • ∫ x in (-1 : ℝ)..1, kappa x := by
    have h := intervalIntegral.integral_comp_div
                (f := kappa) (a := -eps_S S) (b := eps_S S)
                (c := eps_S S) heps_ne
    have heq1 : (-eps_S S) / eps_S S = -1 := by
      rw [neg_div, div_self heps_ne]
    have heq2 : eps_S S / eps_S S = 1 := div_self heps_ne
    rw [heq1, heq2] at h
    exact h
  rw [step3]
  rw [smul_eq_mul]
  have step4 : ∫ x in (-1:ℝ)..1, kappa x = 1 :=
    kappa_intervalIntegral (-1) 1 le_rfl le_rfl
  rw [step4, mul_one]
  field_simp

/-! ### Regional formulas for `phi'_S` and `phi_S`

On the core region `[-(1-ε), 1-ε]` both bumps vanish, so `phi''_S = η_S`
and `phi'_S(x) = η_S · x`, `phi_S(x) = η_S · x²/2`.

On the right tail `x ≥ 1 + ε`, the right-hand bump has integrated to `S`,
so `phi'_S(x) = η_S · x + S`.

For the tail formula for `phi_S` itself, we use the fundamental theorem of
calculus (`phi'_S` is continuous and its antiderivative from `1+ε` to `x`
equals `phi_S(x) - phi_S(1+ε)`).
-/

/-- Core formula: `phi'_S(x) = η_S · x` for `|x| ≤ 1 - ε_S`. -/
lemma phiP_S_core {S x : ℝ} (hS : 0 < S) (hx : |x| ≤ 1 - eps_S S) :
    phiP_S S x = eta_S S * x := by
  -- On the whole interval `[-|x|, |x|] ⊆ [-(1-ε), 1-ε]`, `phi''_S = η_S`.
  unfold phiP_S psi
  -- `∫ t in 0..x, phi''_S t = ∫ t in 0..x, η_S`, since on the integration
  -- range `t` satisfies `|t| ≤ |x| ≤ 1 - ε_S`.
  have hcore_eq : ∀ t ∈ Set.uIcc (0:ℝ) x, phiPP_S S t = eta_S S := by
    intro t ht
    apply phiPP_S_core hS
    have habs_t : |t| ≤ |x| := by
      rcases le_or_gt 0 x with hx_sgn | hx_sgn
      · -- x ≥ 0: uIcc 0 x = Icc 0 x.
        have huicc : Set.uIcc (0:ℝ) x = Set.Icc 0 x := by
          rw [Set.uIcc_of_le hx_sgn]
        rw [huicc, Set.mem_Icc] at ht
        rw [abs_of_nonneg hx_sgn]
        exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      · -- x < 0: uIcc 0 x = Icc x 0.
        have huicc : Set.uIcc (0:ℝ) x = Set.Icc x 0 := by
          rw [Set.uIcc_comm, Set.uIcc_of_le hx_sgn.le]
        rw [huicc, Set.mem_Icc] at ht
        rw [abs_of_neg hx_sgn]
        exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith [habs_t, hx]
  have hint_eq : ∫ t in (0:ℝ)..x, phiPP_S S t = ∫ t in (0:ℝ)..x, eta_S S := by
    apply integral_congr
    exact hcore_eq
  rw [hint_eq]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Core formula for `phi_S`: `phi_S(x) = η_S · x² / 2` for `|x| ≤ 1 - ε_S`. -/
lemma phi_Sc_core {S x : ℝ} (hS : 0 < S) (hx : |x| ≤ 1 - eps_S S) :
    phi_Sc S x = eta_S S * x ^ 2 / 2 := by
  unfold phi_Sc phi
  -- `phi_Sc S x = ∫ u in 0..x, psi (phiPP_S S) u = ∫ u in 0..x, η_S u`.
  -- On the integration range, `|u| ≤ |x| ≤ 1 - ε_S`, so by `phiP_S_core`,
  -- `psi (phiPP_S S) u = η_S · u`.
  have hcore_eq : ∀ u ∈ Set.uIcc (0:ℝ) x, psi (phiPP_S S) u = eta_S S * u := by
    intro u hu
    have habs_u : |u| ≤ 1 - eps_S S := by
      rcases le_or_gt 0 x with hx_sgn | hx_sgn
      · have huicc : Set.uIcc (0:ℝ) x = Set.Icc 0 x := Set.uIcc_of_le hx_sgn
        rw [huicc, Set.mem_Icc] at hu
        have habs_u_x : |u| ≤ x := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
        have hxabs : |x| = x := abs_of_nonneg hx_sgn
        linarith [habs_u_x, (abs_le.mp hx).2, hxabs]
      · have huicc : Set.uIcc (0:ℝ) x = Set.Icc x 0 := by
          rw [Set.uIcc_comm, Set.uIcc_of_le hx_sgn.le]
        rw [huicc, Set.mem_Icc] at hu
        have habs_u_negx : |u| ≤ -x := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have : |u| ≤ |x| := by rw [abs_of_neg hx_sgn]; exact habs_u_negx
        linarith [this, hx]
    -- The core formula `psi (phiPP_S S) u = phiP_S S u = eta_S * u` follows.
    have := phiP_S_core hS habs_u
    -- `phiP_S S u = psi (phiPP_S S) u` by definition.
    unfold phiP_S at this
    exact this
  have hint_eq : ∫ u in (0:ℝ)..x, psi (phiPP_S S) u =
      ∫ u in (0:ℝ)..x, eta_S S * u := by
    apply integral_congr
    exact hcore_eq
  rw [hint_eq]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_id]
  ring

/-! ### Additional useful positivity -/

/-- `phi''_S > 0` for `S > 0`. -/
lemma phiPP_S_pos {S : ℝ} (hS : 0 < S) (x : ℝ) : 0 < phiPP_S S x :=
  lt_of_lt_of_le (eta_S_pos hS) (phiPP_S_ge_eta hS x)

/-- Strict convexity of `phi_S`. -/
lemma strictConvexOn_phi_Sc {S : ℝ} (hS : 0 < S) :
    StrictConvexOn ℝ Set.univ (phi_Sc S) := by
  unfold phi_Sc
  exact strictConvexOn_phi (phiPP_S_continuous hS) (eta_S_pos hS)
    (phiPP_S_ge_eta hS)

/-- Quadratic lower bound for `phi_S`. -/
lemma phi_Sc_ge_quadratic {S : ℝ} (hS : 0 < S) (x : ℝ) :
    eta_S S * x ^ 2 / 2 ≤ phi_Sc S x :=
  phi_ge_quadratic (phiPP_S_continuous hS) (eta_S_pos hS).le (phiPP_S_ge_eta hS) x

end L2Counterexample
