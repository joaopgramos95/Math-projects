import L2Counterexample.Basic

/-!
# Smooth bump (WIP)

This is the editable WIP version of `Bump.lean`. It constructs the
one-dimensional even smooth probability bump `kappa : ℝ → ℝ` used in the
potential construction (`big_tasks.md` task #1,
`02_construction_and_profile.md` item 1).

Target data:

* a nonnegative compactly supported smooth function `kappa : ℝ → ℝ`;
* support contained in `[-1, 1]`;
* evenness;
* integral equal to `1`;
* boundedness used for the constants in the paper.

The construction reuses Mathlib's `ContDiffBump` centered at `0` with radii
`rIn = 1/2` and `rOut = 1`, and the `ContDiffBump.normed` construction that
divides by the integral so the result integrates to `1`. All of the smoothness,
support, evenness and integrability properties are then immediate from the
mathlib API in `Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace L2Counterexample

/-! ## Underlying mathlib bump

We pick `rIn = 1/2`, `rOut = 1` so that the normalised bump is supported in
`[-1, 1]` and is positive on `(-1/2, 1/2)`. The radii are otherwise immaterial.
-/

/-- The underlying (unnormalised) `ContDiffBump` centered at `0 : ℝ` with
`rIn = 1/2` and `rOut = 1`. -/
def kappaBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Smooth compactly supported even probability bump used throughout the
paper. It is the `ContDiffBump` `kappaBump` normalised so that its integral
is `1`. -/
def kappa : ℝ → ℝ :=
  kappaBump.normed volume

/-! ## Smoothness, support, evenness and integrability -/

/-- `kappa` is nonnegative. -/
theorem kappa_nonneg (x : ℝ) : 0 ≤ kappa x :=
  kappaBump.nonneg_normed x

/-- `kappa` is smooth of every order. -/
theorem kappa_contDiff : ContDiff ℝ ∞ kappa :=
  kappaBump.contDiff_normed

/-- `kappa` is continuous. -/
theorem kappa_continuous : Continuous kappa :=
  kappaBump.continuous_normed

/-- `kappa` has compact support. -/
theorem kappa_hasCompactSupport : HasCompactSupport kappa :=
  kappaBump.hasCompactSupport_normed

/-- The support of `kappa` is the open interval `(-1, 1)`. -/
theorem kappa_support_eq : Function.support kappa = Set.Ioo (-1 : ℝ) 1 := by
  have h : Function.support kappa = Metric.ball (0 : ℝ) kappaBump.rOut :=
    kappaBump.support_normed_eq (μ := volume)
  rw [h]
  -- `Metric.ball (0 : ℝ) 1 = Set.Ioo (-1) 1`
  show Metric.ball (0 : ℝ) (1 : ℝ) = Set.Ioo (-1 : ℝ) 1
  rw [Real.ball_eq_Ioo]
  ring_nf

/-- The topological support of `kappa` is the closed interval `[-1, 1]`. -/
theorem kappa_tsupport_eq : tsupport kappa = Set.Icc (-1 : ℝ) 1 := by
  have h : tsupport kappa = Metric.closedBall (0 : ℝ) kappaBump.rOut :=
    kappaBump.tsupport_normed_eq (μ := volume)
  rw [h]
  show Metric.closedBall (0 : ℝ) (1 : ℝ) = Set.Icc (-1 : ℝ) 1
  rw [Real.closedBall_eq_Icc]
  ring_nf

/-- `kappa` is supported in `[-1, 1]`. -/
theorem kappa_tsupport_subset : tsupport kappa ⊆ Set.Icc (-1 : ℝ) 1 := by
  rw [kappa_tsupport_eq]

/-- `kappa` is an even function. -/
theorem kappa_even (x : ℝ) : kappa (-x) = kappa x :=
  kappaBump.normed_neg x

/-- `kappa` integrates to `1`. -/
theorem kappa_integral : ∫ x, kappa x = 1 :=
  kappaBump.integral_normed

/-- `kappa` is integrable with respect to the Lebesgue measure. -/
theorem kappa_integrable : Integrable kappa :=
  kappaBump.integrable_normed

/-- `kappa x = 0` whenever `1 ≤ |x|`, i.e. outside `(-1, 1)`. -/
theorem kappa_eq_zero_of_abs_ge_one {x : ℝ} (hx : 1 ≤ |x|) : kappa x = 0 := by
  -- It suffices to show that `x` is not in the support.
  have hx_notin : x ∉ Function.support kappa := by
    rw [kappa_support_eq]
    intro hmem
    obtain ⟨h1, h2⟩ := hmem
    have : |x| < 1 := abs_lt.mpr ⟨h1, h2⟩
    exact (not_le.mpr this) hx
  simpa [Function.mem_support, not_not] using hx_notin

/-- `kappa x = 0` whenever `|x| > 1`. -/
theorem kappa_eq_zero_of_abs_gt_one {x : ℝ} (hx : 1 < |x|) : kappa x = 0 :=
  kappa_eq_zero_of_abs_ge_one hx.le

/-! ## Boundedness -/

/-- `kappa` is bounded above by `1 / volume.real (closedBall 0 (1/2))`. -/
theorem kappa_le_div_measure (x : ℝ) :
    kappa x ≤ 1 / (volume.real (Metric.closedBall (0 : ℝ) (1 / 2))) :=
  kappaBump.normed_le_div_measure_closedBall_rIn volume x

/-- There is a nonnegative upper bound `M` such that `kappa x ≤ M` for all `x`.
-/
theorem kappa_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, kappa x ≤ M := by
  refine ⟨1 / (volume.real (Metric.closedBall (0 : ℝ) (1 / 2))), ?_, ?_⟩
  · positivity
  · intro x; exact kappa_le_div_measure x

/-! ## Interval integrals

The interval integral of `kappa` over any closed interval containing
`[-1, 1]` equals `1`, because `kappa` vanishes off `[-1, 1]`. -/

/-- The Lebesgue integral of `kappa` over a Borel set containing `[-1, 1]` (in
the form of complement support) equals `1`. We use this to derive interval
integral identities below. -/
private theorem kappa_setIntegral_Icc (a b : ℝ) (ha : a ≤ -1) (hb : 1 ≤ b) :
    ∫ x in Set.Icc a b, kappa x = 1 := by
  -- Write `∫ kappa = ∫_{Icc a b} kappa + ∫_{(Icc a b)ᶜ} kappa`.
  -- On the complement `kappa = 0`, so the second integral is `0`.
  classical
  have h_meas : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have h_zero_outside : ∀ x ∈ (Set.Icc a b)ᶜ, kappa x = 0 := by
    intro x hx
    have hx_not : x ∉ Set.Icc a b := hx
    -- Then either x < a or x > b.
    rcases lt_or_ge x a with hlt | hge
    · -- x < a ≤ -1, so x < -1, hence |x| > 1.
      have hx_lt_neg : x < -1 := lt_of_lt_of_le hlt ha
      have habs : 1 < |x| := by
        have hxneg : x < 0 := by linarith
        have habs_eq : |x| = -x := abs_of_neg hxneg
        rw [habs_eq]; linarith
      exact kappa_eq_zero_of_abs_gt_one habs
    · -- x ≥ a; combined with x ∉ [a, b] we get x > b ≥ 1.
      have hx_gt_b : b < x := by
        by_contra h
        push_neg at h
        exact hx_not ⟨hge, h⟩
      have hx_gt_one : 1 < x := lt_of_le_of_lt hb hx_gt_b
      have habs : 1 < |x| := by
        have hxpos : 0 < x := lt_trans zero_lt_one hx_gt_one
        rw [abs_of_pos hxpos]; exact hx_gt_one
      exact kappa_eq_zero_of_abs_gt_one habs
  have h_split :
      (∫ x in Set.Icc a b, kappa x) + ∫ x in (Set.Icc a b)ᶜ, kappa x =
        ∫ x, kappa x :=
    MeasureTheory.integral_add_compl h_meas kappa_integrable
  have h_compl_zero : ∫ x in (Set.Icc a b)ᶜ, kappa x = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero h_zero_outside
  have hk_int : (∫ x, kappa x) = 1 := kappa_integral
  rw [h_compl_zero, add_zero, hk_int] at h_split
  exact h_split

/-- Interval integral of `kappa` over any closed interval `[a, b]` containing
`[-1, 1]` equals `1`. -/
theorem kappa_intervalIntegral (a b : ℝ) (ha : a ≤ -1) (hb : 1 ≤ b) :
    ∫ x in a..b, kappa x = 1 := by
  have hab : a ≤ b := le_trans ha (le_trans (by norm_num : (-1 : ℝ) ≤ 1) hb)
  have h := kappa_setIntegral_Icc a b ha hb
  rw [intervalIntegral.integral_of_le hab]
  rw [← h]
  -- Convert `Icc a b` to `Ioc a b`: they differ by the singleton `{a}` which
  -- has measure zero.
  refine MeasureTheory.setIntegral_congr_set ?_
  exact Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)

/-! ## Existence statement

The existence form of the bump, useful for downstream code that prefers an
existential statement to a concrete definition. -/

/-- Existence of a smooth, even, compactly supported probability bump. -/
theorem bump_exists :
    ∃ κ : ℝ → ℝ,
      ContDiff ℝ ∞ κ ∧
      (∀ x, 0 ≤ κ x) ∧
      (∀ x, 1 < |x| → κ x = 0) ∧
      (∀ x, κ (-x) = κ x) ∧
      (∫ x, κ x) = 1 ∧
      (∃ M, ∀ x, κ x ≤ M) := by
  refine ⟨kappa, kappa_contDiff, kappa_nonneg, ?_, kappa_even, kappa_integral, ?_⟩
  · intro x hx; exact kappa_eq_zero_of_abs_gt_one hx
  · obtain ⟨M, _, hM⟩ := kappa_bounded
    exact ⟨M, hM⟩

end L2Counterexample
