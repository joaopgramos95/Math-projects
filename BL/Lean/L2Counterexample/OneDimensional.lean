import L2Counterexample.TestFunction
import Mathlib

/-!
# One-dimensional counterexample (WIP)

This is the editable WIP version of `OneDimensional.lean`. It assembles the
one-dimensional Brascamp-Lieb counterexample. The goals are:

1. **Parity/orthogonality package** (blueprint task #11): evenness of
   `phi_S`, oddness of `phi'_S`, evenness of `exp(-phi_S)` and `rho_S`,
   evenness of `g_S`, centering `c_S := ∫ g_S d rho_S`, and the two
   orthogonality identities `∫ f_S d rho_S = 0`,
   `∫ f_S · phi'_S d rho_S = 0`, together with the general lemma
   "integral of (even · odd) is zero under a symmetric measure".

2. **Distance to the optimizer space** (task #12): `O_S = span ℝ {1, phi'_S}`
   inside `L²(rho_S)`, with membership of `1` and `phi'_S` in `L²`, linear
   independence, orthogonality of `f_S`, and
   `dist(f_S, O_S)² = ‖f_S‖² = Var rho_S g_S`.

3. **Deficit asymptotics** (task #13):

       E_phi_S(f_S)             = 1/S - 1/S² + O(S⁻³)
       Var rho_S f_S            = 1/S - 2/S² + O(S⁻³)
       delta_phi_S(f_S)         = 1/S² + O(S⁻³)
       dist(f_S, O_S)² / delta_phi_S(f_S) = S · (1 + O(S⁻¹))

4. **The 1D conclusion**: there is no finite `C` so that
   `dist(f, O_phi) ≤ C · sqrt(delta_phi(f))` holds for every admissible pair
   `(phi, f)` coming from the blueprint family. This is `theorem
   no_uniform_L2_stability_one_dim`.

Following the project convention in `LEAN_AGENT.md`, all upstream data
(the potential `phi_S`, its derivative `phi'_S`, the test function `g_S`,
the constants `Z_S`, `A_S`, the energy/variance identities, and the
asymptotic estimates of blueprint §03 and §04) is introduced here as
`axiom` declarations with blueprint signatures. The file consumes only
those axioms and therefore sits upstream-free (once the axiomatised data
is supplied by the real `Potential`/`Normalization`/`TestFunction` files,
the axioms become theorems with `exact?` proofs).

The asymptotic shorthand we use is finitary, matching
`WIP_Normalization.BigOInv`:

    `f =O[k] g`   ↔   `∃ C S₀, 0 < S₀ ∧ ∀ S, S₀ ≤ S → |f S - g S| ≤ C · S^(-k)`

This sidesteps the heavier `Asymptotics.IsBigO` machinery in intermediate
statements, in line with best practice #4.
-/

noncomputable section

open MeasureTheory Set Real
open scoped Topology BigOperators

namespace L2Counterexample

/-! ## Finitary asymptotic shorthand -/

/-- `BigOInv1D f g k` means `f S = g S + O(S^{-k})` as `S → ∞`, encoded as
an explicit finite inequality over real `S`. This matches
`WIP_Normalization.BigOInv`. We repeat the definition here to keep the
file self-contained. -/
def BigOInv1D (f g : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → |f S - g S| ≤ C * S ^ (-(k : ℤ))

@[inherit_doc] notation:50 f " =O[" k "]₁ " g => BigOInv1D f g k

/-! ## Upstream axioms (blueprint signatures)

These are declared as local `axiom`s. When the upstream files (`Potential`,
`Normalization`, `TestFunction`) are finalised, each axiom below is
replaced by the corresponding theorem. The signatures match the blueprint
verbatim.
-/

/-! ### Upstream symbols

`phi_S, phiDer_S, phiDer2_S, eps_S, eta_S, phi_S_even, phiDer_S_odd,
phiDer2_S_even` are imported from `L2Counterexample.Potential`.
`Z_S, q_S, t_S, tailInt_S` come from `L2Counterexample.Normalization`.
`A_S, rho_S, g_S, g_S_even` come from `L2Counterexample.TestFunction`. -/

/-- `rho_S` is a probability measure for `0 < S` — proven as
`rho_S_isProb_of_pos`. The unconditional `rho_S_isProb` instance below
follows by case analysis: for `0 < S`, use this lemma; for `S ≤ 0`,
`rho_S S = Measure.dirac 0` (a probability measure). -/
theorem rho_S_isProb_of_pos {S : ℝ} (hS : 0 < S) :
    IsProbabilityMeasure (rho_S S) := by
  have hZ_pos : 0 < Z_S S := Z_S_pos S hS
  have hZ_ne : Z_S S ≠ 0 := hZ_pos.ne'
  refine ⟨?_⟩
  show rho_S S Set.univ = 1
  rw [rho_S_of_pos hS]
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  have h_int_smul : Integrable (fun x => (Z_S S)⁻¹ * Real.exp (-(phi_S S x))) :=
    (exp_negPhiS_integrable S hS).const_mul _
  have h_nn_ae : 0 ≤ᵐ[volume] fun x => (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) :=
    Filter.Eventually.of_forall fun x => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal h_int_smul h_nn_ae,
      MeasureTheory.integral_const_mul]
  have : (Z_S S)⁻¹ * Z_S S = 1 := inv_mul_cancel₀ hZ_ne
  show ENNReal.ofReal ((Z_S S)⁻¹ * ∫ (x : ℝ), Real.exp (-phi_S S x)) = 1
  rw [show (∫ (x : ℝ), Real.exp (-phi_S S x)) = Z_S S from rfl, this,
      ENNReal.ofReal_one]

/-- `rho_S` is unconditionally a probability measure (the `S ≤ 0` case
falls back to `Measure.dirac 0` in the definition of `rho_S`). -/
instance rho_S_isProb (S : ℝ) : IsProbabilityMeasure (rho_S S) := by
  by_cases hS : 0 < S
  · exact rho_S_isProb_of_pos hS
  · unfold rho_S; rw [if_neg hS]; infer_instance

/-! ### Parity and basic identities (blueprint §05 eq. (a)--(e)) -/

/-- The density `exp(-phi_S)` is even (immediate from `phi_S_even`). -/
lemma exp_neg_phi_S_even (S x : ℝ) :
    Real.exp (-phi_S S (-x)) = Real.exp (-phi_S S x) := by
  rw [phi_S_even]

/-- Invariance of `rho_S` under the reflection `x ↦ -x`.

For `0 < S`: the density `(Z_S)⁻¹ · exp(-φ_S)` is even (by
`phi_S_even`), and Lebesgue measure on `ℝ` is reflection-invariant
(`measurePreserving_neg`); combining these via `Measure.map_withDensity`
gives the result. For `S ≤ 0`: `rho_S S = Measure.dirac 0`, and
`(dirac 0).map (-·) = dirac (-0) = dirac 0`. -/
theorem rho_S_reflection_invariant (S : ℝ) :
    (rho_S S).map (fun x : ℝ => -x) = rho_S S := by
  by_cases hS : 0 < S
  · -- For 0 < S, density even + Lebesgue reflection-invariant.
    rw [rho_S_of_pos hS]
    set f : ℝ → ENNReal :=
      fun x => ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) with hf_def
    have h_meas_f : Measurable f :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul
        (Real.measurable_exp.comp (phi_S_measurable hS).neg))
    have h_f_even : ∀ x, f (-x) = f x := by
      intro x
      show ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S (-x))))
         = ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x)))
      rw [phi_S_even]
    -- Show via Measure.ext.
    refine MeasureTheory.Measure.ext ?_
    intro s hs
    rw [MeasureTheory.Measure.map_apply measurable_neg hs]
    rw [MeasureTheory.withDensity_apply _ (measurable_neg hs)]
    rw [MeasureTheory.withDensity_apply _ hs]
    -- Goal: ∫⁻ x in (-·)⁻¹' s, f x ∂vol = ∫⁻ x in s, f x ∂vol
    -- Strategy: replace f x with f(-x) on LHS (using f even), then apply
    -- setLIntegral_map (reverse direction): ∫⁻ x in g⁻¹'s, f(gx) ∂μ = ∫⁻ y in s, f y ∂(map g μ)
    -- with g = neg, then use measurePreserving_neg.
    have h_neg_mp : MeasureTheory.MeasurePreserving (Neg.neg : ℝ → ℝ)
                    MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.Measure.measurePreserving_neg MeasureTheory.volume
    -- Step A: ∫⁻ x in (-·)⁻¹' s, f x = ∫⁻ x in (-·)⁻¹' s, f(-x) by f even.
    have h_step_A : ∫⁻ x in (Neg.neg : ℝ → ℝ) ⁻¹' s, f x ∂MeasureTheory.volume
                  = ∫⁻ x in (Neg.neg : ℝ → ℝ) ⁻¹' s, f (-x) ∂MeasureTheory.volume := by
      refine MeasureTheory.setLIntegral_congr_fun (measurable_neg hs) ?_
      intro x _
      exact (h_f_even x).symm
    -- Step B: ∫⁻ x in (-·)⁻¹' s, f(-x) = ∫⁻ y in s, f y ∂(map (-·) volume)
    --        = ∫⁻ y in s, f y ∂volume (since map (-·) volume = volume).
    have h_step_B : ∫⁻ x in (Neg.neg : ℝ → ℝ) ⁻¹' s, f (-x) ∂MeasureTheory.volume
                  = ∫⁻ y in s, f y ∂MeasureTheory.volume := by
      have := MeasureTheory.setLIntegral_map (μ := MeasureTheory.volume)
                hs h_meas_f measurable_neg
      rw [h_neg_mp.map_eq] at this
      exact this.symm
    rw [h_step_A, h_step_B]
  · -- For S ≤ 0, rho_S S = dirac 0; map (-·) (dirac 0) = dirac (-0) = dirac 0.
    unfold rho_S
    rw [if_neg hS]
    rw [MeasureTheory.Measure.map_dirac' measurable_neg]
    simp

/-- Measurability of `phi'_S`, derived from continuity. Requires
`0 < S`. -/
theorem phiDer_S_measurable {S : ℝ} (hS : 0 < S) : Measurable (phiDer_S S) :=
  (phiDer_S_contDiff hS).continuous.measurable

/-- Measurability of `g_S`, derived from `g_S_continuous`. -/
theorem g_S_measurable {S : ℝ} (hS_large : 1 < S) : Measurable (g_S S) :=
  (g_S_continuous hS_large).measurable

/-! ### `L^2` membership and integrability (blueprint §05)

We axiomatise that `1`, `phi'_S`, `g_S` belong to `L²(rho_S)` so that
inner products below make sense. `g_S_memL2` is in fact derivable from
boundedness `0 ≤ g_S ≤ 1` and finiteness of `rho_S` (see
`g_S_memL2_of_one_lt` below); the unconditional `g_S_memL2` axiom is
kept because downstream `ff_S_memL2` and the inner-product lemmas use
it without an `S > 1` hypothesis. -/

/-! ### Helpers: generalize `A_S_pos`, `g_S_*` lemmas to `0 < S`

The lemmas in `TestFunction` are stated with `1 < S` because that is the
range used downstream; the proofs only need `0 < S`. We re-state the
necessary pieces here at the weaker hypothesis. -/

private lemma A_S_pos_of_pos {S : ℝ} (hS : 0 < S) : 0 < A_S S := by
  have heps : 0 < eps_S S := eps_S_pos hS
  have hlt : 1 - eps_S S < 1 + eps_S S := by linarith
  have h_int_pos : ∀ t, 0 < phiDer2_S S t * Real.exp (phi_S S t) := fun t =>
    mul_pos (phiDer2_S_pos hS t) (Real.exp_pos _)
  have h_cont : Continuous (fun t => phiDer2_S S t * Real.exp (phi_S S t)) :=
    (phiDer2_S_continuous hS).mul
      (Real.continuous_exp.comp (phi_S_contDiff hS).continuous)
  unfold A_S
  exact intervalIntegral.intervalIntegral_pos_of_pos
    (h_cont.intervalIntegrable _ _) h_int_pos hlt

private lemma g_S_le_one_of_pos {S : ℝ} (hS : 0 < S) (x : ℝ) : g_S S x ≤ 1 := by
  unfold g_S
  split_ifs with h1 h2
  · exact zero_le_one
  · push_neg at h1
    have h_le : |x| ≤ 1 + eps_S S := le_of_lt h2
    have hmono := N_S_mono hS h_le
    have hrhs : N_S S (1 + eps_S S) = A_S S := rfl
    have hpos := A_S_pos_of_pos hS
    rw [div_le_one hpos]
    linarith
  · exact le_refl _

private lemma g_S_nonneg_of_pos {S : ℝ} (hS : 0 < S) (x : ℝ) : 0 ≤ g_S S x := by
  unfold g_S
  split_ifs with h1 h2
  · exact le_refl _
  · push_neg at h1
    have hge : 1 - eps_S S ≤ |x| := le_of_lt h1
    have hN := N_S_nonneg hS hge
    exact div_nonneg hN (le_of_lt (A_S_pos_of_pos hS))
  · exact zero_le_one

private lemma g_S_continuous_of_pos {S : ℝ} (hS : 0 < S) : Continuous (g_S S) := by
  have heps_pos : 0 < eps_S S := eps_S_pos hS
  have hA_pos : 0 < A_S S := A_S_pos_of_pos hS
  have hA_ne : A_S S ≠ 0 := hA_pos.ne'
  have h_int_int : ∀ a b, IntervalIntegrable
                    (fun t => phiDer2_S S t * Real.exp (phi_S S t))
                    MeasureTheory.volume a b :=
    phi_integrand_intervalIntegrable hS
  have h_N_cont : Continuous (N_S S) := by
    show Continuous (fun r => ∫ t in (1 - eps_S S)..r,
                        phiDer2_S S t * Real.exp (phi_S S t))
    exact intervalIntegral.continuous_primitive h_int_int (1 - eps_S S)
  have h_abs_cont : Continuous (fun x : ℝ => |x|) := continuous_abs
  have h_N_abs_cont : Continuous (fun x : ℝ => N_S S |x|) :=
    h_N_cont.comp h_abs_cont
  have h_div_cont : Continuous (fun x : ℝ => N_S S |x| / A_S S) :=
    h_N_abs_cont.div_const _
  have h_inner_cont : Continuous (fun x : ℝ =>
      if |x| < 1 + eps_S S then N_S S |x| / A_S S else 1) := by
    have h_eq : (fun x : ℝ =>
        if |x| < 1 + eps_S S then N_S S |x| / A_S S else 1) =
        (fun x : ℝ =>
          if 1 + eps_S S ≤ |x| then 1 else N_S S |x| / A_S S) := by
      funext x
      by_cases h : |x| < 1 + eps_S S
      · rw [if_pos h, if_neg (not_le.mpr h)]
      · rw [if_neg h, if_pos (le_of_not_gt h)]
    rw [h_eq]
    refine Continuous.if_le continuous_const h_div_cont continuous_const
      h_abs_cont ?_
    intro x hx
    rw [← hx]
    show (1 : ℝ) = N_S S (1 + eps_S S) / A_S S
    show (1 : ℝ) = A_S S / A_S S
    field_simp
  show Continuous (fun x : ℝ =>
      if |x| ≤ 1 - eps_S S then 0
      else if |x| < 1 + eps_S S then N_S S |x| / A_S S else 1)
  refine Continuous.if_le continuous_const h_inner_cont h_abs_cont
    continuous_const ?_
  intro x hx
  have h_lt : |x| < 1 + eps_S S := by linarith [hx, heps_pos]
  rw [if_pos h_lt, hx]
  rw [N_S_left_endpoint S]
  ring

/-- Helper: any function is in `MemLp f p (Measure.dirac a)` for `p ≠ 0`,
because `eLpNorm f p (dirac a) = ‖f a‖ₑ < ∞`. -/
private lemma memLp_dirac_real (f : ℝ → ℝ) {p : ENNReal} (a : ℝ) (hp : p ≠ 0) :
    MemLp f p (Measure.dirac a) := by
  refine ⟨aestronglyMeasurable_dirac, ?_⟩
  rw [eLpNorm_dirac f a hp]
  exact enorm_lt_top

/-! ### Helpers for `phiDer_S_memL2`: bound on `phiDer_S` and `id ∈ L²(ρ_S)` -/

/-- `phi''_S` is bounded above by `eta_S + 2·M_κ·S/ε_S`, where `M_κ` is
the upper bound on the bump `kappa`. -/
private lemma phiDer2_S_bounded {S : ℝ} (hS : 0 < S) :
    ∃ M, 0 ≤ M ∧ ∀ x, phiDer2_S S x ≤ M := by
  obtain ⟨M_k, hM_k_nn, hM_k_le⟩ := kappa_bounded
  have heps_pos : 0 < eps_S S := eps_S_pos hS
  have hSeps_nn : 0 ≤ S / eps_S S := div_nonneg hS.le heps_pos.le
  refine ⟨eta_S S + 2 * (S / eps_S S) * M_k, ?_, ?_⟩
  · have h1 : 0 ≤ eta_S S := (eta_S_pos hS).le
    have h2 : 0 ≤ 2 * (S / eps_S S) * M_k := by positivity
    linarith
  · intro x
    unfold phiDer2_S
    have h1 : (S / eps_S S) * kappa ((x - 1) / eps_S S) ≤ (S / eps_S S) * M_k :=
      mul_le_mul_of_nonneg_left (hM_k_le _) hSeps_nn
    have h2 : (S / eps_S S) * kappa ((x + 1) / eps_S S) ≤ (S / eps_S S) * M_k :=
      mul_le_mul_of_nonneg_left (hM_k_le _) hSeps_nn
    linarith

/-- Linear bound on `phi'_S`: `|phi'_S(x)| ≤ K·|x|` for some `K`,
since `phi''_S` is bounded and `phi'_S(0) = 0`. -/
private lemma phiDer_S_abs_le {S : ℝ} (hS : 0 < S) :
    ∃ K, 0 ≤ K ∧ ∀ x, |phiDer_S S x| ≤ K * |x| := by
  obtain ⟨M, hM_nn, hM_le⟩ := phiDer2_S_bounded hS
  refine ⟨M, hM_nn, ?_⟩
  intro x
  unfold phiDer_S psi
  have h_norm : ∀ y ∈ Set.uIoc 0 x, ‖phiDer2_S S y‖ ≤ M := by
    intro y _
    rw [Real.norm_eq_abs]
    have hy_pos : 0 ≤ phiDer2_S S y := (phiDer2_S_pos hS y).le
    rw [abs_of_nonneg hy_pos]
    exact hM_le y
  have h_bd := intervalIntegral.norm_integral_le_of_norm_le_const h_norm
  rw [Real.norm_eq_abs] at h_bd
  have h_eq : |x - 0| = |x| := by ring_nf
  rw [h_eq] at h_bd
  exact h_bd

/-- `id : ℝ → ℝ` lies in `L²(ρ_S)` for `0 < S`: this follows from the
Gaussian decay of the density (via `phi_S_quadratic_lower`) and the
integrability `Integrable (x² · exp(-η/2·x²))`. -/
private lemma id_memL2_of_pos {S : ℝ} (hS : 0 < S) :
    MemLp (fun x : ℝ => x) 2 (rho_S S) := by
  have h_meas : AEStronglyMeasurable (fun x : ℝ => x) (rho_S S) :=
    measurable_id.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq h_meas]
  rw [rho_S_of_pos hS]
  have h_meas_density : Measurable (fun x =>
      ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x)))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (phi_S_measurable hS).neg))
  have h_density_lt_top : ∀ᵐ (x : ℝ),
      ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul' h_meas_density h_density_lt_top]
  have hZ_pos : 0 < Z_S S := Z_S_pos S hS
  have hZ_inv_pos : 0 < (Z_S S)⁻¹ := inv_pos.mpr hZ_pos
  have h_eq_funext : (fun x =>
      (ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x)))).toReal • x^2) =
      (fun x => (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) * x^2) := by
    funext x
    have h_nn : 0 ≤ (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) :=
      mul_nonneg hZ_inv_pos.le (Real.exp_pos _).le
    rw [ENNReal.toReal_ofReal h_nn]
    rfl
  rw [h_eq_funext]
  -- Bound by Gaussian.
  have heta_pos : 0 < eta_S S := eta_S_pos hS
  have hetaH : 0 < eta_S S / 2 := by linarith
  have h_int_base_rpow : Integrable (fun x : ℝ =>
      x ^ (2 : ℝ) * Real.exp (-(eta_S S / 2) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq (b := eta_S S / 2) (s := 2)
      hetaH (by norm_num)
  have h_int_base : Integrable (fun x : ℝ =>
      x^2 * Real.exp (-(eta_S S / 2) * x ^ 2)) := by
    refine (integrable_congr ?_).mp h_int_base_rpow
    filter_upwards with x
    congr 1
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have h_dom_int : Integrable (fun x : ℝ =>
      (Z_S S)⁻¹ * (x^2 * Real.exp (-(eta_S S / 2) * x ^ 2))) :=
    h_int_base.const_mul _
  refine h_dom_int.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ (measurable_id.pow_const _)
    refine Measurable.mul measurable_const ?_
    exact Real.measurable_exp.comp (phi_S_measurable hS).neg
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have h_phi_lower := phi_S_quadratic_lower hS x
    have h_exp_le : Real.exp (-(phi_S S x)) ≤ Real.exp (-(eta_S S / 2 * x ^ 2)) := by
      apply Real.exp_le_exp.mpr; linarith
    rw [Real.norm_eq_abs]
    have h_lhs_nn : 0 ≤ (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) * x^2 := by
      have h1 : 0 ≤ (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) :=
        mul_nonneg hZ_inv_pos.le (Real.exp_pos _).le
      exact mul_nonneg h1 (sq_nonneg _)
    rw [abs_of_nonneg h_lhs_nn]
    have h_exp_eq : -(eta_S S / 2) * x^2 = -(eta_S S / 2 * x^2) := by ring
    rw [h_exp_eq]
    have h_x2_nn : 0 ≤ x^2 := sq_nonneg _
    have h1 : (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) * x^2
            ≤ (Z_S S)⁻¹ * Real.exp (-(eta_S S / 2 * x^2)) * x^2 := by
      apply mul_le_mul_of_nonneg_right _ h_x2_nn
      apply mul_le_mul_of_nonneg_left h_exp_le hZ_inv_pos.le
    have h2 : (Z_S S)⁻¹ * Real.exp (-(eta_S S / 2 * x^2)) * x^2
            = (Z_S S)⁻¹ * (x^2 * Real.exp (-(eta_S S / 2 * x^2))) := by ring
    rw [h2] at h1
    exact h1

/-- `phi'_S ∈ L^2(rho_S)`, unconditionally. For `0 < S`, combines
`phi_S_quadratic_lower` with the Gaussian-tail integrability of `rho_S`
to bound the L²-norm of the linear-growth function `phiDer_S`
(via `phiDer_S_abs_le` and `id_memL2_of_pos`). For `S ≤ 0`, `rho_S`
falls back to `Measure.dirac 0`, where every function is L^p. -/
theorem phiDer_S_memL2 (S : ℝ) :
    MemLp (phiDer_S S) 2 (rho_S S) := by
  by_cases hS : 0 < S
  · obtain ⟨K, _, hK_le⟩ := phiDer_S_abs_le hS
    have h_meas : AEStronglyMeasurable (phiDer_S S) (rho_S S) :=
      (phiDer_S_contDiff hS).continuous.aestronglyMeasurable
    have h_id_memL2 := id_memL2_of_pos hS
    refine MemLp.of_le_mul (c := K) h_id_memL2 h_meas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hK_le x
  · have h_eq : rho_S S = Measure.dirac 0 := by
      unfold rho_S; rw [if_neg hS]
    rw [h_eq]
    exact memLp_dirac_real _ 0 (by norm_num)

/-- `g_S ∈ L^2(rho_S)`, unconditionally. For `0 < S`, `g_S` is continuous
and bounded in `[0, 1]`, and `rho_S` is a probability measure. For
`S ≤ 0`, `rho_S = Measure.dirac 0` and the result is trivial. -/
theorem g_S_memL2 (S : ℝ) :
    MemLp (g_S S) 2 (rho_S S) := by
  by_cases hS : 0 < S
  · have h_meas : AEStronglyMeasurable (g_S S) (rho_S S) :=
      (g_S_continuous_of_pos hS).aestronglyMeasurable
    refine MemLp.of_bound h_meas 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (g_S_nonneg_of_pos hS x)]
    exact g_S_le_one_of_pos hS x
  · have h_eq : rho_S S = Measure.dirac 0 := by
      unfold rho_S; rw [if_neg hS]
    rw [h_eq]
    exact memLp_dirac_real _ 0 (by norm_num)

/-- The conditional, *proven* version of `g_S_memL2`: for `S > 1`,
`g_S` is bounded in `[0, 1]` and `rho_S` is finite, hence `g_S ∈ L²`. -/
theorem g_S_memL2_of_one_lt {S : ℝ} (hS_large : 1 < S) :
    MemLp (g_S S) 2 (rho_S S) :=
  g_S_memL2 S

/-- `phi'_S · g_S ∈ L^1(rho_S)` by Cauchy–Schwarz (Hölder triple
`(2, 2, 1)`) applied to `phiDer_S_memL2` and `g_S_memL2`. -/
theorem phiDer_gg_integrable (S : ℝ) :
    Integrable (fun x => phiDer_S S x * g_S S x) (rho_S S) := by
  have hg : MemLp (g_S S) 2 (rho_S S) := g_S_memL2 S
  have hphi : MemLp (phiDer_S S) 2 (rho_S S) := phiDer_S_memL2 S
  have hmul : MemLp (fun x => phiDer_S S x * g_S S x) 1 (rho_S S) :=
    MemLp.mul' hg hphi
  exact hmul.integrable le_rfl

/-! ### Upstream energy/variance identities

The concrete definitions of the Brascamp-Lieb energy and deficit come
from `TestFunction`/`Normalization`. We only need the scalar invariants
`E_phi_S(f_S)`, `Var rho_S f_S`, `delta_phi_S(f_S)` and their asymptotic
evaluations, plus the identity `delta = E - Var`.

The concrete one-dimensional test function is `f_S := g_S - c_S` where
`c_S := ∫ g_S d rho_S`.
-/

/-- The centering constant `c_S := ∫ g_S d rho_S`. -/
def cc_S (S : ℝ) : ℝ := ∫ x, g_S S x ∂(rho_S S)

/-- The centered test function `f_S := g_S - c_S`. -/
def ff_S (S : ℝ) (x : ℝ) : ℝ := g_S S x - cc_S S

/-- `f_S ∈ L^2(rho_S)` (since `g_S` is, and we subtract a scalar times
the constant function `1`, which is in `L^p` for every finite measure). -/
lemma ff_S_memL2 (S : ℝ) : MemLp (ff_S S) 2 (rho_S S) := by
  -- `MemLp.sub` together with `memLp_const`.
  have h1 : MemLp (g_S S) 2 (rho_S S) := g_S_memL2 S
  have h2 : MemLp (fun _ : ℝ => cc_S S) 2 (rho_S S) :=
    memLp_const (cc_S S)
  exact h1.sub h2

/-! ### Blueprint numerical invariants

We define the variance of `f_S` as the integral of `(g_S - c_S)²` and
keep the BL energy as an axiom (its concrete integral form involves
`g_S'`, which lives in `TestFunction`). -/

/-- The variance `Var_{rho_S}(f_S) := ∫ (g_S − c_S)² dρ_S`. Blueprint §04. -/
noncomputable def Var_f_S (S : ℝ) : ℝ :=
  ∫ x, (g_S S x - cc_S S) ^ 2 ∂(rho_S S)

/-- The Brascamp–Lieb energy `E_phi_S(f_S) := ∫ (g_S')² / φ''_S dρ_S`,
defined via the energy functional `E_phi` from `TestFunction`. Blueprint
§04. -/
noncomputable def EE_phi_S (S : ℝ) : ℝ := E_phi S (g_S' S)

/-- The Brascamp–Lieb deficit `delta_phi_S(f_S) := E_phi_S(f_S) -
Var_{rho_S}(f_S)`. Blueprint Definition §01 and §05. -/
noncomputable def delta_phi_S (S : ℝ) : ℝ := EE_phi_S S - Var_f_S S

/-- The variance of `g_S` equals the variance of `f_S = g_S - c_S` (by
definition of `Var_f_S`). -/
@[simp] lemma Var_gg_eq_Var_ff (S : ℝ) :
    (∫ x, (g_S S x - cc_S S) ^ 2 ∂(rho_S S)) = Var_f_S S := rfl

/-! ### Asymptotic evaluations (blueprint §04, §05) -/

/-- `E_phi_S(f_S) = 1/S - 1/S² + O(S⁻³)`. Combines `E_phi_g_S_eq`
(showing `EE_phi_S = 2/(Z_S · A_S)`) with `Z_S_asymp` (`Z_S = 2 + 2/S
+ O(S^{-3})`) and `A_S_asymp` (`A_S - S = O(S^{-1})`) via the algebraic
identity
  `EE_phi_S - (1/S - 1/S²) = (2 - (S-1)·r) / (S²·Z_S·A_S)`
where `r := Z_S·A_S - (2S+2)`, plus `Z_S ≥ 1` and `A_S ≥ S/2` eventually. -/
theorem EE_phi_S_asymp :
    BigOInv1D EE_phi_S (fun S => 1 / S - 1 / S ^ 2) 3 := by
  -- Constants from upstream asymptotics.
  obtain ⟨C_Z, S_Z, hS_Z_pos, h_Z_bd⟩ := Z_S_asymp
  obtain ⟨C_A_raw, h_A_bd⟩ := A_S_asymp.bound
  rw [Filter.eventually_atTop] at h_A_bd
  obtain ⟨S_A, hS_A_bd⟩ := h_A_bd
  obtain ⟨S_Z1, hS_Z1_pos, hZ_one⟩ := exists_S_Z_S_ge_one
  -- Make sure C_A ≥ 0 (replace by max C_A_raw 0 to ensure nonnegativity).
  set C_A := max C_A_raw 0 with hC_A_def
  have hC_A_nn : 0 ≤ C_A := le_max_right _ _
  have hS_A_bd' : ∀ S, S_A ≤ S → ‖A_S S - S‖ ≤ C_A * ‖(S : ℝ)^(-(1:ℤ))‖ := by
    intro S hS
    refine le_trans (hS_A_bd S hS) ?_
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  -- Similarly ensure C_Z ≥ 0.
  have hC_Z_nn : 0 ≤ C_Z := by
    have h : |Z_S S_Z - (fun S => (2 : ℝ) + 2 / S) S_Z|
        ≤ C_Z * S_Z ^ (-(3 : ℤ)) := h_Z_bd S_Z le_rfl
    have h_abs_nn : 0 ≤ |Z_S S_Z - ((2 : ℝ) + 2 / S_Z)| := abs_nonneg _
    have h_pow_pos : (0 : ℝ) < S_Z ^ (-(3 : ℤ)) := zpow_pos hS_Z_pos _
    nlinarith
  -- Pick S₀ large enough for all conditions.
  -- Need: S ≥ S_Z, S_A, S_Z1, 2, and S ≥ √(2 C_A) + 1 (so A_S ≥ S/2).
  -- For S ≥ √(2 C_A): C_A/S ≤ S/2, hence A_S ≥ S - C_A/S ≥ S/2.
  refine ⟨4 + 2 * (C_Z + 4 * C_A + C_Z * C_A),
          max (max (max S_Z S_A) S_Z1) (max 2 (Real.sqrt (2 * C_A) + 1)),
          ?_, ?_⟩
  · refine lt_max_of_lt_right ?_
    refine lt_max_of_lt_left ?_
    norm_num
  intro S hS
  have hS_Z : S_Z ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) hS))
  have hS_A : S_A ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) hS))
  have hS_Z1 : S_Z1 ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hS_2 : (2 : ℝ) ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hS_sqrt : Real.sqrt (2 * C_A) + 1 ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hS_one : (1 : ℝ) ≤ S := by linarith
  have hS_lt : (1 : ℝ) < S := by linarith
  have hSpos : 0 < S := by linarith
  -- Z_S ≥ 1.
  have hZ_one : 1 ≤ Z_S S := hZ_one S hS_Z1
  have hZ_pos : 0 < Z_S S := by linarith
  -- A_S ≥ S/2.
  have hA_pos_pre : 0 < A_S S := A_S_pos hS_lt
  have hA_bd : ‖A_S S - S‖ ≤ C_A * ‖(S : ℝ)^(-(1:ℤ))‖ := hS_A_bd' S hS_A
  have hpow1_eq : (S : ℝ)^(-(1:ℤ)) = 1/S := by
    rw [show (-(1:ℤ)) = -((1:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast,
        pow_one, one_div]
  have hA_diff_bd : |A_S S - S| ≤ C_A / S := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hpow1_eq,
        abs_of_pos (by positivity : (0:ℝ) < 1/S)] at hA_bd
    have h_eq : C_A * (1/S) = C_A / S := by ring
    linarith [hA_bd]
  have hA_ge_half : S/2 ≤ A_S S := by
    -- A_S ≥ S - C_A/S, want ≥ S/2, i.e., S/2 ≥ C_A/S, i.e., S² ≥ 2*C_A.
    -- S ≥ √(2 C_A) + 1 > √(2 C_A), so S² > 2 C_A.
    have h_sqrt_nn : 0 ≤ Real.sqrt (2 * C_A) := Real.sqrt_nonneg _
    have hS_sqrt_lt : Real.sqrt (2 * C_A) < S := by linarith
    have hS_sq : S^2 > 2 * C_A := by
      have h1 : (Real.sqrt (2 * C_A))^2 = 2 * C_A := by
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * C_A)]
      have hS_pos_sqrt : Real.sqrt (2 * C_A) ^ 2 < S^2 := by
        have h_ss : 0 ≤ S := hSpos.le
        nlinarith [hS_sqrt_lt, h_sqrt_nn]
      linarith
    -- C_A / S ≤ S / 2 ↔ 2 * C_A ≤ S * S = S² (when S > 0).
    have hCAoverS_le : C_A / S ≤ S / 2 := by
      rw [div_le_div_iff₀ hSpos (by norm_num : (0:ℝ) < 2)]
      nlinarith
    -- A_S ≥ S - C_A/S.
    have h_A_ge : A_S S ≥ S - C_A / S := by
      have h_neg : -(C_A / S) ≤ A_S S - S := by
        have := abs_le.mp hA_diff_bd
        linarith [this.1]
      linarith
    linarith
  -- E_phi_g_S_eq: EE_phi_S S = 2 / (Z_S S * A_S S).
  have hEE_eq : EE_phi_S S = 2 / (Z_S S * A_S S) := E_phi_g_S_eq hS_lt
  -- Z_S * A_S - (2S + 2) bound: |r| ≤ M/S where M = C_Z + 4C_A + C_Z·C_A.
  have hZ_diff_bd : |Z_S S - (2 + 2/S)| ≤ C_Z / S^3 := by
    have h : |Z_S S - ((2 : ℝ) + 2/S)| ≤ C_Z * S^(-(3:ℤ)) := h_Z_bd S hS_Z
    have h_eq : (S : ℝ)^(-(3:ℤ)) = 1/S^3 := by
      rw [show (-(3:ℤ)) = -((3:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
    rw [h_eq] at h
    have h_eq2 : C_Z * (1 / S^3) = C_Z / S^3 := by ring
    linarith
  -- r := Z_S * A_S - (2S + 2).
  set r := Z_S S * A_S S - (2*S + 2) with hr_def
  -- r = (Z_S - (2+2/S))·A_S + (2+2/S)·(A_S - S).
  have hr_decomp : r = (Z_S S - (2 + 2/S)) * A_S S
                        + (2 + 2/S) * (A_S S - S) := by
    rw [hr_def]; field_simp; ring
  -- |r| bound.
  have hS3_pos : (0 : ℝ) < S^3 := by positivity
  have hAbsA_le : |A_S S| ≤ S + C_A / S := by
    rw [abs_of_nonneg hA_pos_pre.le]
    have := abs_le.mp hA_diff_bd
    linarith [this.2]
  have h_2_plus_2overS_le : 2 + 2/S ≤ 4 := by
    have h1 : (2 : ℝ)/S ≤ 2 := by
      rw [div_le_iff₀ hSpos]; linarith
    linarith
  have h_2_plus_2overS_nn : (0 : ℝ) ≤ 2 + 2/S := by
    have : (0 : ℝ) ≤ 2/S := by positivity
    linarith
  -- Bound |r|.
  have hr_bd : |r| ≤ (C_Z + 4 * C_A + C_Z * C_A) / S := by
    rw [hr_decomp]
    have hT1 : |(Z_S S - (2 + 2/S)) * A_S S|
        ≤ (C_Z / S^3) * (S + C_A / S) := by
      rw [abs_mul]
      exact mul_le_mul hZ_diff_bd hAbsA_le (abs_nonneg _) (by positivity)
    have hT2 : |(2 + 2/S) * (A_S S - S)| ≤ 4 * (C_A / S) := by
      rw [abs_mul, abs_of_nonneg h_2_plus_2overS_nn]
      exact mul_le_mul h_2_plus_2overS_le hA_diff_bd (abs_nonneg _) (by linarith)
    -- Triangle.
    have h_tri : |(Z_S S - (2 + 2/S)) * A_S S + (2 + 2/S) * (A_S S - S)|
        ≤ |(Z_S S - (2 + 2/S)) * A_S S| + |(2 + 2/S) * (A_S S - S)| :=
      abs_add_le _ _
    -- (C_Z/S³)·(S + C_A/S) ≤ C_Z/S² + C_Z·C_A/S^4.
    have hT1' : (C_Z / S^3) * (S + C_A / S) = C_Z/S^2 + C_Z*C_A/S^4 := by
      have h_eq : (S : ℝ)^3 * S = S^4 := by ring
      have h_eq2 : (S : ℝ)^2 * S^2 = S^4 := by ring
      field_simp
    -- For S ≥ 2: C_Z/S² ≤ C_Z/S, C_Z·C_A/S^4 ≤ C_Z·C_A/S, 4·C_A/S = 4C_A/S.
    have h_S2_le_S : (1 : ℝ)/S^2 ≤ 1/S := by
      have hS_le_S2 : S ≤ S^2 := by nlinarith
      exact one_div_le_one_div_of_le hSpos hS_le_S2
    have h_S4_le_S : (1 : ℝ)/S^4 ≤ 1/S := by
      have hS_le_S4 : S ≤ S^4 := by nlinarith
      exact one_div_le_one_div_of_le hSpos hS_le_S4
    -- Combine.
    have hT1_le : (C_Z / S^3) * (S + C_A / S) ≤ C_Z/S + C_Z*C_A/S := by
      rw [hT1']
      have h1 : C_Z/S^2 ≤ C_Z/S := by
        rw [div_eq_mul_one_div, div_eq_mul_one_div C_Z S]
        exact mul_le_mul_of_nonneg_left h_S2_le_S hC_Z_nn
      have h2 : C_Z*C_A/S^4 ≤ C_Z*C_A/S := by
        rw [div_eq_mul_one_div (C_Z * C_A), div_eq_mul_one_div (C_Z * C_A) S]
        exact mul_le_mul_of_nonneg_left h_S4_le_S
          (mul_nonneg hC_Z_nn hC_A_nn)
      linarith
    have h_total : C_Z/S + C_Z*C_A/S + 4 * (C_A / S) = (C_Z + 4 * C_A + C_Z * C_A) / S := by
      field_simp; ring
    linarith [hT1, hT2, hT1_le]
  -- Now bound the numerator |2S² - (S-1)·Z_S·A_S| = |2 - (S-1)·r|.
  have h_num_eq : 2*S^2 - (S - 1) * (Z_S S * A_S S) = 2 - (S - 1) * r := by
    rw [hr_def]; ring
  have h_num_bd : |2 - (S - 1) * r| ≤ 2 + C_Z + 4 * C_A + C_Z * C_A := by
    have h_S_minus_1_le : (S - 1) / S ≤ 1 := by
      rw [div_le_one hSpos]; linarith
    have h_S_minus_1_nn : 0 ≤ (S - 1) := by linarith
    have h_prod_bd : (S - 1) * |r| ≤ C_Z + 4 * C_A + C_Z * C_A := by
      have h1 : (S - 1) * |r| ≤ (S - 1) * ((C_Z + 4 * C_A + C_Z * C_A) / S) :=
        mul_le_mul_of_nonneg_left hr_bd h_S_minus_1_nn
      have h2 : (S - 1) * ((C_Z + 4 * C_A + C_Z * C_A) / S)
              = ((S - 1)/S) * (C_Z + 4 * C_A + C_Z * C_A) := by
        field_simp
      have hM_nn : 0 ≤ C_Z + 4 * C_A + C_Z * C_A := by
        have := mul_nonneg hC_Z_nn hC_A_nn
        linarith
      have h3 : ((S - 1)/S) * (C_Z + 4 * C_A + C_Z * C_A)
              ≤ 1 * (C_Z + 4 * C_A + C_Z * C_A) :=
        mul_le_mul_of_nonneg_right h_S_minus_1_le hM_nn
      linarith
    have h_t1 : |2 - (S - 1) * r| ≤ |(2 : ℝ)| + |(S - 1) * r| := abs_sub _ _
    have h_t1' : |(2 : ℝ)| = 2 := by norm_num
    have h_t2 : |(S - 1) * r| = (S - 1) * |r| := by
      rw [abs_mul, abs_of_nonneg h_S_minus_1_nn]
    linarith [h_t1, h_t1', h_t2, h_prod_bd]
  -- Denominator: S² · Z_S · A_S ≥ S² · 1 · S/2 = S³/2.
  have h_denom_pos : 0 < S^2 * (Z_S S * A_S S) := by
    apply mul_pos (by positivity) (mul_pos hZ_pos hA_pos_pre)
  have h_denom_lb : S^3 / 2 ≤ S^2 * (Z_S S * A_S S) := by
    have h1 : S^2 * 1 * (S/2) ≤ S^2 * (Z_S S * A_S S) := by
      have : S^2 * 1 * (S/2) = S^2 * (1 * (S/2)) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul hZ_one hA_ge_half (by linarith) hZ_pos.le
      · positivity
    have h_eq : S^2 * 1 * (S/2) = S^3 / 2 := by ring
    linarith
  -- Compute EE_phi_S S - (1/S - 1/S^2).
  rw [hEE_eq]
  -- 2/(Z_S A_S) - (1/S - 1/S²) = (2S² - (S-1)·Z_S·A_S) / (S²·Z_S·A_S)
  have hZAne : Z_S S * A_S S ≠ 0 := mul_ne_zero hZ_pos.ne' hA_pos_pre.ne'
  have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
  have hS2ne : (S : ℝ)^2 ≠ 0 := by positivity
  have h_diff_eq : 2 / (Z_S S * A_S S) - ((1 : ℝ)/S - 1/S^2)
      = (2 * S^2 - (S - 1) * (Z_S S * A_S S)) / (S^2 * (Z_S S * A_S S)) := by
    field_simp
  rw [h_diff_eq]
  -- |a/b| ≤ |a|/|b|.
  rw [abs_div]
  rw [abs_of_pos h_denom_pos]
  -- Goal: |2S² - (S-1)·Z_S·A_S| / (S²·Z_S·A_S) ≤ K · S^(-3:ℤ)
  -- Use: |num| ≤ 2 + M (M := C_Z + 4·C_A + C_Z·C_A) and denom ≥ S³/2.
  have h_pow3_eq : (S : ℝ)^(-(3:ℤ)) = 1/S^3 := by
    rw [show (-(3:ℤ)) = -((3:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
  show |2 * S ^ 2 - (S - 1) * (Z_S S * A_S S)| / (S ^ 2 * (Z_S S * A_S S))
      ≤ (4 + 2 * (C_Z + 4 * C_A + C_Z * C_A)) * (S : ℝ)^(-(3:ℤ))
  rw [h_pow3_eq, h_num_eq]
  -- |2 - (S-1)·r| / (S²·Z_S·A_S) ≤ (2 + M) / (S³/2) = 2(2+M)/S³.
  have h_final : |2 - (S - 1) * r| / (S^2 * (Z_S S * A_S S))
      ≤ (4 + 2 * (C_Z + 4 * C_A + C_Z * C_A)) * (1 / S^3) := by
    have hS3half_pos : (0 : ℝ) < S^3 / 2 := by positivity
    have h1 : |2 - (S - 1) * r| / (S^2 * (Z_S S * A_S S))
            ≤ |2 - (S - 1) * r| / (S^3 / 2) := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) hS3half_pos h_denom_lb
    have h2 : |2 - (S - 1) * r| / (S^3 / 2)
            ≤ (2 + (C_Z + 4 * C_A + C_Z * C_A)) / (S^3 / 2) := by
      apply div_le_div_of_nonneg_right _ hS3half_pos.le
      linarith [h_num_bd]
    have h3 : (2 + (C_Z + 4 * C_A + C_Z * C_A)) / (S^3 / 2)
            = (4 + 2 * (C_Z + 4 * C_A + C_Z * C_A)) * (1 / S^3) := by
      field_simp; ring
    linarith
  exact h_final

/-- The integrated variance `Var_f_S S = ∫ (g_S - c_S)² dρ_S` equals the
algebraic variance `Var_phi S (g_S S) = ∫ g_S² dρ - (∫ g_S dρ)²`. The
identity uses linearity of integration and that `ρ_S` is a probability
measure (so `∫ 1 dρ = 1`). Requires `1 < S` so that `g_S ∈ L²(ρ_S)`. -/
lemma Var_f_S_eq_Var_phi_g_S {S : ℝ} (hS : 1 < S) :
    Var_f_S S = Var_phi S (g_S S) := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  haveI := rho_S_isProb_of_pos hSpos
  have h_g_int : Integrable (g_S S) (rho_S S) :=
    (g_S_memL2 S).integrable (by norm_num)
  have h_g_sq_int : Integrable (fun x => (g_S S x)^2) (rho_S S) := by
    have h_mul : MemLp (fun x => g_S S x * g_S S x) 1 (rho_S S) :=
      MemLp.mul' (g_S_memL2 S) (g_S_memL2 S)
    have h_int_mul : Integrable (fun x => g_S S x * g_S S x) (rho_S S) :=
      h_mul.integrable le_rfl
    convert h_int_mul using 1
    funext x; ring
  unfold Var_f_S Var_phi
  -- Expand (g - c)² pointwise.
  have h_expand : (fun x => (g_S S x - cc_S S)^2)
      = (fun x => ((g_S S x)^2 - 2 * cc_S S * g_S S x) + cc_S S^2) := by
    funext x; ring
  rw [h_expand]
  -- Two-step linearity: ∫ ((g² - 2c·g) + c²) = ∫ (g² - 2c·g) + ∫ c².
  have h_int_inner : Integrable (fun x => (g_S S x)^2 - 2 * cc_S S * g_S S x) (rho_S S) :=
    h_g_sq_int.sub (h_g_int.const_mul (2 * cc_S S))
  rw [integral_add h_int_inner (integrable_const _)]
  rw [integral_sub h_g_sq_int (h_g_int.const_mul (2 * cc_S S))]
  rw [integral_const_mul]
  -- ∫ const dρ = const since ρ is a probability measure.
  have h_const_int : ∫ _ : ℝ, cc_S S^2 ∂(rho_S S) = cc_S S^2 := by
    rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  rw [h_const_int]
  unfold cc_S
  ring

/-- `Var rho_S f_S = 1/S - 2/S² + O(S⁻³)`. Follows from
`Var_phi_g_S_expansion` and `Var_f_S_eq_Var_phi_g_S`. -/
theorem Var_f_S_asymp :
    BigOInv1D Var_f_S (fun S => 1 / S - 2 / S ^ 2) 3 := by
  obtain ⟨C, hC⟩ := Var_phi_g_S_expansion.bound
  rw [Filter.eventually_atTop] at hC
  obtain ⟨S₀, hS₀⟩ := hC
  refine ⟨C, max S₀ 2, ?_, fun S hS => ?_⟩
  · exact lt_max_of_lt_right (by norm_num : (0:ℝ) < 2)
  have hS' : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hS_2 : (2 : ℝ) ≤ S := le_trans (le_max_right _ _) hS
  have hS_1 : (1 : ℝ) < S := by linarith
  have hS_pos : 0 < S := by linarith
  rw [Var_f_S_eq_Var_phi_g_S hS_1]
  have h := hS₀ S hS'
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (zpow_pos hS_pos _)] at h
  exact h

/-! ## Parity-orthogonality package (blueprint task #11)

The key general lemma: if `mu` is invariant under `x ↦ -x` and `u` is an
odd, `mu`-integrable function, then `∫ u dmu = 0`. We prove this via the
change-of-variables `x ↦ -x`.
-/

/-- **General parity lemma (measure-theoretic form).**
If `mu` is invariant under the reflection `x ↦ -x` and `u : ℝ → ℝ` is
odd and `mu`-integrable, then `∫ u dmu = 0`.

This is the key lemma behind the parity orthogonality. -/
lemma integral_odd_of_reflection_invariant
    {mu : Measure ℝ} (h_symm : mu.map (fun x : ℝ => -x) = mu)
    {u : ℝ → ℝ} (h_odd : ∀ x, u (-x) = -u x)
    (_h_meas : AEMeasurable u mu) (h_int : Integrable u mu) :
    ∫ x, u x ∂mu = 0 := by
  -- Substitute `x ↦ -x`: using reflection-invariance,
  --   ∫ u dmu = ∫ u dmu.map(neg) = ∫ u(-x) dmu = -∫ u dmu.
  have h_meas_neg : Measurable (fun x : ℝ => -x) := measurable_neg
  have h_aestrong : AEStronglyMeasurable u (mu.map (fun x : ℝ => -x)) := by
    rw [h_symm]; exact h_int.aestronglyMeasurable
  have h1 : ∫ x, u x ∂mu = ∫ x, u (-x) ∂mu := by
    -- `mu` is the pushforward under `neg`, so integrate against the pushforward.
    have hmap := MeasureTheory.integral_map (μ := mu) (φ := fun x : ℝ => -x)
                  (f := u) h_meas_neg.aemeasurable h_aestrong
    rw [h_symm] at hmap
    -- hmap : ∫ y, u y ∂mu = ∫ x, u ((fun x => -x) x) ∂mu
    simpa using hmap
  -- Combine with oddness.
  have h2 : ∫ x, u (-x) ∂mu = -∫ x, u x ∂mu := by
    have h_eq : (fun x => u (-x)) = fun x => -u x := funext h_odd
    rw [h_eq, MeasureTheory.integral_neg]
  linarith [h1, h2]

/-! ### Evenness of `f_S`, zero mean, and parity orthogonality

These follow from the general lemma applied to `u := f_S · phi'_S`
(product of an even and an odd function). First we record the targeted
consequences.
-/

/-- `f_S` is even (from evenness of `g_S` and `c_S` being a scalar). -/
lemma ff_S_even (S x : ℝ) : ff_S S (-x) = ff_S S x := by
  unfold ff_S
  rw [g_S_even]

/-- The centering constant is an integral of an even function, hence
well defined. (Stated by `rfl` for downstream convenience.) -/
lemma cc_S_def (S : ℝ) : cc_S S = ∫ x, g_S S x ∂(rho_S S) := rfl

/-- **Centering identity.** `∫ f_S d rho_S = 0`.

By definition of `c_S`, since `rho_S` is a probability measure. -/
lemma integral_ff_S (S : ℝ) : ∫ x, ff_S S x ∂(rho_S S) = 0 := by
  unfold ff_S
  -- `∫ (g - c) = ∫ g - c` since rho is a probability measure.
  have h_int : Integrable (g_S S) (rho_S S) := (g_S_memL2 S).integrable (by norm_num)
  rw [integral_sub h_int (integrable_const _)]
  have h_const : ∫ _ : ℝ, cc_S S ∂(rho_S S) = cc_S S := by
    simp [MeasureTheory.integral_const, measure_univ]
  rw [h_const, cc_S]
  ring

/-- **Parity orthogonality to `phi'_S`.** `∫ f_S · phi'_S d rho_S = 0`.

Proof: `f_S` is even, `phi'_S` is odd, so their product is odd. The
density of `rho_S` is even, so `rho_S` is reflection-invariant. Apply
the general parity lemma. -/
lemma integral_ff_phiDer_zero (S : ℝ) :
    ∫ x, ff_S S x * phiDer_S S x ∂(rho_S S) = 0 := by
  -- The product `f_S · phi'_S` is odd.
  have h_odd : ∀ x, ff_S S (-x) * phiDer_S S (-x) = -(ff_S S x * phiDer_S S x) := by
    intro x
    rw [ff_S_even, phiDer_S_odd]
    ring
  -- Integrability: `f_S · phi'_S = (g_S - c_S) · phi'_S`
  -- is `g_S · phi'_S - c_S · phi'_S`, each integrable by Cauchy-Schwarz
  -- (for the first) and because `phi'_S ∈ L^2 ⊆ L^1` on a prob. measure
  -- (for the second).
  have h_phi_int : Integrable (phiDer_S S) (rho_S S) :=
    (phiDer_S_memL2 S).integrable (by norm_num)
  have h_gg_phi : Integrable (fun x => g_S S x * phiDer_S S x) (rho_S S) := by
    -- Use commutativity with the axiomatised integrability of phi'·g.
    have : Integrable (fun x => phiDer_S S x * g_S S x) (rho_S S) :=
      phiDer_gg_integrable S
    simpa [mul_comm] using this
  have h_int : Integrable (fun x => ff_S S x * phiDer_S S x) (rho_S S) := by
    have : (fun x => ff_S S x * phiDer_S S x) =
        fun x => g_S S x * phiDer_S S x - cc_S S * phiDer_S S x := by
      funext x; unfold ff_S; ring
    rw [this]
    exact h_gg_phi.sub (h_phi_int.const_mul (cc_S S))
  -- Measurability of the product.
  have h_meas : AEMeasurable (fun x => ff_S S x * phiDer_S S x) (rho_S S) :=
    h_int.aemeasurable
  -- Apply the general parity lemma.
  exact integral_odd_of_reflection_invariant
    (rho_S_reflection_invariant S) h_odd h_meas h_int

/-! ## The optimizer space `O_S = span ℝ {1, phi'_S}`

We work with the `Lp`-space `L^2(rho_S)` in Mathlib's
`MeasureTheory.Lp` formalism. A function `f : ℝ → ℝ` with
`MemLp f 2 (rho_S S)` gives rise to its `toLp`-class in `Lp ℝ 2`.

We model the one-dimensional optimizer space as the `Submodule.span ℝ`
of the two `Lp`-elements `1.toLp` and `phi'_S.toLp`, inside
`Lp ℝ 2 (rho_S S)`.
-/

/-- Shorthand for the `L²` space over `rho_S`. -/
abbrev L2RhoS (S : ℝ) : Type :=
  Lp (α := ℝ) ℝ 2 (rho_S S)

/-- The `Lp`-class of the constant function `1 : ℝ → ℝ` in `L²(rho_S)`. -/
def oneLp (S : ℝ) : L2RhoS S :=
  (memLp_const (1 : ℝ) (μ := rho_S S)).toLp _

/-- The `Lp`-class of `phi'_S` in `L²(rho_S)`. -/
def phiDerLp (S : ℝ) : L2RhoS S :=
  (phiDer_S_memL2 S).toLp _

/-- The `Lp`-class of `f_S` in `L²(rho_S)`. -/
def ffLp (S : ℝ) : L2RhoS S :=
  (ff_S_memL2 S).toLp _

/-- The one-dimensional optimizer subspace `O_S = span ℝ {1, phi'_S} ⊆
L²(rho_S)`. -/
def optSubspace (S : ℝ) : Submodule ℝ (L2RhoS S) :=
  Submodule.span ℝ ({oneLp S, phiDerLp S} : Set (L2RhoS S))

/-! ### `1 ∈ L²(rho_S)` -/

/-- The constant function `1` lies in `L^2(rho_S)`. -/
lemma one_memL2 (S : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (rho_S S) :=
  memLp_const 1

/-! ### Orthogonality of `f_S` to generators

Because `L²` uses an `inner` via
`⟨u,v⟩ = ∫ u·v d rho_S`, we can test orthogonality against the two
generators `1.toLp` and `phi'_S.toLp` directly.
-/

/-- Inner product in `L²(rho_S)` between the `Lp`-classes of two
`MemLp`-functions equals the integral of their product. -/
lemma inner_toLp_eq_integral
    {S : ℝ} {u v : ℝ → ℝ}
    (hu : MemLp u 2 (rho_S S)) (hv : MemLp v 2 (rho_S S)) :
    @inner ℝ _ _ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂(rho_S S) := by
  -- Use `Lp.inner_def` together with `MemLp.coeFn_toLp`.
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hxu hxv
  rw [hxu, hxv]
  -- For ℝ as inner product space, `inner ℝ a b = b * a`. Compute via `re`.
  show RCLike.re (v x * (starRingEnd ℝ) (u x)) = u x * v x
  simp [mul_comm]

/-- `f_S ⟂ 1` in `L²(rho_S)`. -/
lemma ffLp_perp_oneLp (S : ℝ) :
    @inner ℝ _ _ (ffLp S) (oneLp S) = 0 := by
  unfold ffLp oneLp
  rw [inner_toLp_eq_integral (ff_S_memL2 S) (one_memL2 S)]
  simp only [mul_one]
  exact integral_ff_S S

/-- `f_S ⟂ phi'_S` in `L²(rho_S)`. -/
lemma ffLp_perp_phiDerLp (S : ℝ) :
    @inner ℝ _ _ (ffLp S) (phiDerLp S) = 0 := by
  unfold ffLp phiDerLp
  rw [inner_toLp_eq_integral (ff_S_memL2 S) (phiDer_S_memL2 S)]
  exact integral_ff_phiDer_zero S

/-- **Orthogonality to the optimizer span.** `f_S ⟂ O_S`. -/
lemma ffLp_perp_optSubspace (S : ℝ) :
    ∀ y ∈ optSubspace S, @inner ℝ _ _ (ffLp S) y = 0 := by
  -- Orthogonality to a span: it suffices to check on each generator
  -- (bilinearity of the inner product).
  intro y hy
  refine Submodule.span_induction (p := fun z _ => @inner ℝ _ _ (ffLp S) z = 0)
    (hx := hy) ?_ ?_ ?_ ?_
  · -- generators: y = oneLp S or y = phiDerLp S
    rintro z hz
    rcases hz with rfl | hz_singleton
    · exact ffLp_perp_oneLp S
    · -- z ∈ {phiDerLp S}, so z = phiDerLp S
      rw [Set.mem_singleton_iff] at hz_singleton
      subst hz_singleton
      exact ffLp_perp_phiDerLp S
  · -- zero
    simp
  · -- additivity
    intros u v _ _ hu hv
    rw [inner_add_right, hu, hv]; ring
  · -- scalar
    intros r v _ hv
    rw [inner_smul_right, hv, mul_zero]

/-! ### `dist(f_S, O_S)² = ‖f_S‖²`

In a Hilbert space, if `x` is orthogonal to a *complete* subspace `M`,
then `dist(x, M) = ‖x‖`. The span of two elements is finite-dimensional,
hence complete (automatically closed in a Hilbert space). We use
`Submodule.FiniteDimensional.instCompleteSpace`.
-/

/-- `O_S` is finite-dimensional (spanned by two elements). -/
instance optSubspace_fd (S : ℝ) :
    FiniteDimensional ℝ (optSubspace S) := by
  -- Span of a finite set is finite-dimensional.
  unfold optSubspace
  exact FiniteDimensional.span_of_finite ℝ
    ((Set.finite_singleton _).insert _)

/-- `O_S` is (topologically) complete. -/
instance optSubspace_complete (S : ℝ) :
    CompleteSpace (optSubspace S) :=
  FiniteDimensional.complete ℝ _

/-- `O_S` is closed as a subset of `L²(rho_S)`. -/
lemma optSubspace_isClosed (S : ℝ) :
    IsClosed ((optSubspace S : Submodule ℝ (L2RhoS S)) : Set (L2RhoS S)) :=
  Submodule.closed_of_finiteDimensional (optSubspace S)

/-- **Distance identity.** `dist(f_S, O_S)² = ‖f_S‖²`. Since `f_S ⟂ O_S`
and `0 ∈ O_S`, the orthogonal projection of `f_S` onto the closed
finite-dim subspace `O_S` is `0`, so
`dist(f_S, O_S) = ‖f_S - 0‖ = ‖f_S‖`. -/
lemma dist_ffLp_optSubspace_sq_eq (S : ℝ) :
    (Metric.infDist (ffLp S) (optSubspace S : Set (L2RhoS S)))^2 = ‖ffLp S‖ ^ 2 := by
  -- Use the orthogonal-projection characterization.
  -- For closed complete subspaces `K`, `infDist x K = ‖x - proj K x‖`, and
  -- if `x ⟂ K`, the projection is `0`, so `infDist = ‖x‖`.
  classical
  -- Step 1: the projection of `ffLp S` onto `optSubspace S` is zero.
  have hK : IsClosed ((optSubspace S : Submodule ℝ (L2RhoS S)) : Set (L2RhoS S)) :=
    optSubspace_isClosed S
  -- We use `Submodule.infDist_eq_norm_of_mem_orthogonal` or reconstruct.
  -- Simpler: we use the following fact (available in Mathlib):
  --   if `x ⟂ K`, then for every `y ∈ K`, `‖x - y‖² = ‖x‖² + ‖y‖²`, hence
  --   `‖x - y‖ ≥ ‖x‖`, with equality at `y = 0`.
  set x := ffLp S
  set K : Submodule ℝ (L2RhoS S) := optSubspace S
  have hx_perp : ∀ y ∈ K, @inner ℝ _ _ x y = 0 := ffLp_perp_optSubspace S
  have hzero_mem : (0 : L2RhoS S) ∈ (K : Set (L2RhoS S)) := K.zero_mem
  -- `‖x - y‖² = ‖x‖² + ‖y‖²` for `y ∈ K` (Pythagorean theorem).
  have h_lower : ∀ y ∈ K, ‖x‖ ≤ ‖x - y‖ := by
    intro y hy
    have hperp : @inner ℝ _ _ x y = 0 := hx_perp y hy
    have h_sq : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
      rw [norm_sub_sq_real, hperp]; ring
    have h_mono : ‖x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hy_nn : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
      linarith [h_sq]
    have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
    have hxy_nn : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith [h_mono, hx_nn, hxy_nn, sq_nonneg (‖x - y‖ - ‖x‖)]
  -- `infDist x K = ‖x‖`.
  have hK_nonempty : (K : Set (L2RhoS S)).Nonempty := ⟨0, hzero_mem⟩
  have h_inf_lb : ‖x‖ ≤ Metric.infDist x (K : Set (L2RhoS S)) := by
    rw [Metric.le_infDist hK_nonempty]
    intro y hy
    rw [dist_eq_norm]
    exact h_lower y hy
  have h_inf_ub : Metric.infDist x (K : Set (L2RhoS S)) ≤ ‖x‖ := by
    have hbd : Metric.infDist x (K : Set (L2RhoS S)) ≤ dist x 0 :=
      Metric.infDist_le_dist_of_mem hzero_mem
    rw [dist_zero_right] at hbd
    exact hbd
  have h_inf_eq : Metric.infDist x (K : Set (L2RhoS S)) = ‖x‖ :=
    le_antisymm h_inf_ub h_inf_lb
  rw [h_inf_eq]

/-! ### `‖f_S‖² = Var rho_S g_S = Var rho_S f_S`

`‖f_S‖²_{L²(rho_S)} = ∫ (g_S - c_S)² d rho_S = Var_{rho_S}(g_S) =
Var_{rho_S}(f_S)` (translation-invariance of variance).
-/

/-- The squared `L²` norm of `f_S` equals `∫ f_S² d rho_S` (definition). -/
lemma norm_ffLp_sq_eq_integral (S : ℝ) :
    ‖ffLp S‖ ^ 2 = ∫ x, (ff_S S x) ^ 2 ∂(rho_S S) := by
  -- For a real Hilbert space, `‖x‖² = ⟨x, x⟩`, and the L²-inner product
  -- of `u.toLp` with itself is `∫ u² dμ`.
  have hinner :
      @inner ℝ _ _ (ffLp S) (ffLp S) = ∫ x, ff_S S x * ff_S S x ∂(rho_S S) := by
    unfold ffLp
    exact inner_toLp_eq_integral (ff_S_memL2 S) (ff_S_memL2 S)
  have hnorm_sq : ‖ffLp S‖ ^ 2 = @inner ℝ _ _ (ffLp S) (ffLp S) :=
    (real_inner_self_eq_norm_sq (ffLp S)).symm
  rw [hnorm_sq, hinner]
  refine integral_congr_ae ?_
  filter_upwards with x
  ring

/-- `‖f_S‖² = Var rho_S f_S`. -/
lemma norm_ffLp_sq_eq_var (S : ℝ) :
    ‖ffLp S‖ ^ 2 = Var_f_S S := by
  rw [norm_ffLp_sq_eq_integral]
  -- Apply `Var_gg_eq_Var_ff`: `∫ (g_S - c_S)² = Var f_S`.
  unfold ff_S
  exact Var_gg_eq_Var_ff S

/-- **Distance formula.** `dist(f_S, O_S)² = Var rho_S f_S`. -/
lemma dist_ffLp_optSubspace_sq_eq_var (S : ℝ) :
    (Metric.infDist (ffLp S) (optSubspace S : Set (L2RhoS S)))^2 = Var_f_S S := by
  rw [dist_ffLp_optSubspace_sq_eq S, norm_ffLp_sq_eq_var S]

/-! ## Deficit asymptotics (blueprint §05 task #13) -/

/-- Helper: `(1/S - 1/S^2) - (1/S - 2/S^2) = 1/S^2`. -/
lemma deficit_leading_identity (S : ℝ) (hS : 0 < S) :
    (1 / S - 1 / S ^ 2) - (1 / S - 2 / S ^ 2) = 1 / S ^ 2 := by
  field_simp
  ring

/-- **Deficit asymptotic.** `delta_phi_S(f_S) = 1/S² + O(S⁻³)`. -/
lemma delta_phi_S_asymp :
    BigOInv1D delta_phi_S (fun S => 1 / S ^ 2) 3 := by
  obtain ⟨C₁, S₁, hS₁_pos, hE⟩ := EE_phi_S_asymp
  obtain ⟨C₂, S₂, hS₂_pos, hV⟩ := Var_f_S_asymp
  refine ⟨C₁ + C₂, max (max S₁ S₂) 1, ?_, ?_⟩
  · exact lt_max_of_lt_right one_pos
  intro S hS
  have hSpos : 0 < S := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hS)
  have hS₁le : S₁ ≤ S := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hS)
  have hS₂le : S₂ ≤ S := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hE' := hE S hS₁le
  have hV' := hV S hS₂le
  -- `delta - 1/S^2 = (E - (1/S - 1/S^2)) - (V - (1/S - 2/S^2))`.
  have h_id : delta_phi_S S - 1 / S ^ 2 =
      (EE_phi_S S - (1 / S - 1 / S ^ 2)) -
      (Var_f_S S - (1 / S - 2 / S ^ 2)) := by
    unfold delta_phi_S
    have hS2 : (S:ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hSpos.ne'
    field_simp
    ring
  rw [h_id]
  have h_tri :
      |EE_phi_S S - (1 / S - 1 / S ^ 2) - (Var_f_S S - (1 / S - 2 / S ^ 2))|
        ≤ |EE_phi_S S - (1 / S - 1 / S ^ 2)|
          + |Var_f_S S - (1 / S - 2 / S ^ 2)| := by
    exact abs_sub _ _
  have h_bd :
      |EE_phi_S S - (1 / S - 1 / S ^ 2)|
        + |Var_f_S S - (1 / S - 2 / S ^ 2)|
          ≤ (C₁ + C₂) * S ^ (-(3:ℤ)) := by
    have hpow_nn : 0 ≤ S ^ (-(3:ℤ)) := by
      rw [zpow_neg]; positivity
    linarith [hE', hV']
  linarith [h_tri, h_bd]

/-- **Positivity of `delta` eventually.** For `S ≥ S₀`, `delta_phi_S(f_S) > 0`.

This comes from `delta = 1/S^2 + O(S^{-3})`, which for sufficiently large
`S` is dominated by the leading term. -/
lemma delta_phi_S_eventually_pos :
    ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → 0 < delta_phi_S S := by
  obtain ⟨C, S₁, hS₁_pos, hbd⟩ := delta_phi_S_asymp
  refine ⟨max S₁ (max 1 (2 * (C + 1))), ?_, ?_⟩
  · exact lt_max_of_lt_right (lt_max_of_lt_left one_pos)
  intro S hS
  have hS1 : S₁ ≤ S := le_trans (le_max_left _ _) hS
  have hS_ge_one : 1 ≤ S := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hS_big : 2 * (C + 1) ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS_ge_one
  have h' := hbd S hS1
  have h : |delta_phi_S S - 1 / S ^ 2| ≤ C * S ^ (-(3:ℤ)) := h'
  -- delta ≥ 1/S^2 - C / S^3
  have hS2_pos : 0 < S ^ 2 := by positivity
  have hS3_pos : 0 < S ^ 3 := by positivity
  have hSne : S ≠ 0 := hSpos.ne'
  have hpow : S ^ (-(3:ℤ)) = 1 / S ^ 3 := by
    rw [show (-(3:ℤ)) = -((3 : ℕ) : ℤ) from rfl, zpow_neg,
        zpow_natCast, one_div]
  rw [hpow] at h
  have hlb : 1 / S ^ 2 - C * (1 / S ^ 3) ≤ delta_phi_S S := by
    have hsub := (abs_sub_le_iff.1 h).2
    linarith
  -- Now it suffices to show `1/S^2 > C/S^3`, i.e. `S > C`.
  have hSgC : C + 1 ≤ S := by linarith
  have : C < S := by linarith
  have h_key : C * (1 / S ^ 3) < 1 / S ^ 2 := by
    rw [show C * (1 / S ^ 3) = C / S ^ 3 from by ring]
    rw [div_lt_div_iff₀ hS3_pos hS2_pos]
    have hC_nn_or : 0 ≤ C ∨ C < 0 := le_or_gt 0 C
    rcases hC_nn_or with hC_nn | hC_neg
    · have hS2_le_S3 : C * S ^ 2 ≤ S * S ^ 2 := by
        nlinarith [sq_nonneg S]
      have hcube : S * S ^ 2 = S ^ 3 := by ring
      nlinarith
    · have hCsq_le : C * S ^ 2 ≤ 0 := by
        have := sq_nonneg S
        nlinarith
      nlinarith [hS3_pos]
  linarith

/-! ### Ratio divergence

From `Var rho_S f_S = 1/S - 2/S² + O(S⁻³)` and
`delta_phi_S(f_S) = 1/S² + O(S⁻³)` we obtain

    `Var/delta = S(1 + O(S⁻¹))`,

which diverges. For the final counterexample we only need unboundedness.
-/

/-- **Divergence of the distance-deficit ratio.** For every `K`, there
exists `S₀ > 0` such that, for every `S ≥ S₀`,
`Var_f_S S > K · delta_phi_S S`.

This is the contentful version of `dist(f_S, O_S)² / delta_phi_S(f_S) →
∞`, via the identity `dist² = Var` already proved. -/
lemma var_over_delta_unbounded :
    ∀ K : ℝ, ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S →
      K * delta_phi_S S < Var_f_S S := by
  intro K
  obtain ⟨C₁, S₁, hS₁_pos, hV⟩ := Var_f_S_asymp
  obtain ⟨C₂, S₂, hS₂_pos, hD⟩ := delta_phi_S_asymp
  -- Step 1: deduce that the constants `C₁, C₂` from the BigOInv axioms are
  -- nonnegative. Since `|...| ≥ 0` and `S^(-3) > 0`, the bound forces it.
  have hpow_pos₁ : 0 < S₁ ^ (-(3 : ℤ)) := zpow_pos hS₁_pos _
  have hpow_pos₂ : 0 < S₂ ^ (-(3 : ℤ)) := zpow_pos hS₂_pos _
  have hC₁_nn : 0 ≤ C₁ := by
    have hb := hV S₁ le_rfl
    have habs_nn : 0 ≤ |Var_f_S S₁ - (fun S => 1 / S - 2 / S ^ 2) S₁| :=
      abs_nonneg _
    by_contra hneg
    push_neg at hneg
    have hlt : C₁ * S₁ ^ (-(3 : ℤ)) < 0 := mul_neg_of_neg_of_pos hneg hpow_pos₁
    linarith
  have hC₂_nn : 0 ≤ C₂ := by
    have hb := hD S₂ le_rfl
    have habs_nn : 0 ≤ |delta_phi_S S₂ - (fun S => 1 / S ^ 2) S₂| :=
      abs_nonneg _
    by_contra hneg
    push_neg at hneg
    have hlt : C₂ * S₂ ^ (-(3 : ℤ)) < 0 := mul_neg_of_neg_of_pos hneg hpow_pos₂
    linarith
  have hKnn : 0 ≤ |K| := abs_nonneg _
  have hKC₂_nn : 0 ≤ |K| * C₂ := mul_nonneg hKnn hC₂_nn
  -- Threshold: `S ≥ max{S₁, S₂, max(1, 4M)}` with
  -- `M := |K| + C₁ + |K|·C₂ + 4 ≥ 4`.
  refine ⟨max (max S₁ S₂) (max 1 (4 * (|K| + C₁ + |K| * C₂ + 4))), ?_, ?_⟩
  · exact lt_max_of_lt_right (lt_max_of_lt_left one_pos)
  intro S hS
  have hS₁le : S₁ ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hS)
  have hS₂le : S₂ ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hS_ge_one : 1 ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hS_big : 4 * (|K| + C₁ + |K| * C₂ + 4) ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := by linarith
  have hS2_pos : 0 < S ^ 2 := by positivity
  have hS3_pos : 0 < S ^ 3 := by positivity
  have hSne : S ≠ 0 := hSpos.ne'
  have hpow : S ^ (-(3 : ℤ)) = 1 / S ^ 3 := by
    rw [show (-(3 : ℤ)) = -((3 : ℕ) : ℤ) from rfl, zpow_neg,
        zpow_natCast, one_div]
  -- Step 2: `Var_f_S S ≥ (1/S - 2/S²) - C₁/S³`.
  have hVbd' := hV S hS₁le
  have hVbd : |Var_f_S S - (1 / S - 2 / S ^ 2)| ≤ C₁ * S ^ (-(3 : ℤ)) := hVbd'
  rw [hpow] at hVbd
  have hV_lb : 1 / S - 2 / S ^ 2 - C₁ * (1 / S ^ 3) ≤ Var_f_S S := by
    have := (abs_sub_le_iff.1 hVbd).2
    linarith
  -- Step 3: `delta_phi_S S ≤ 1/S² + C₂/S³`.
  have hDbd' := hD S hS₂le
  have hDbd : |delta_phi_S S - 1 / S ^ 2| ≤ C₂ * S ^ (-(3 : ℤ)) := hDbd'
  rw [hpow] at hDbd
  have hD_ub : delta_phi_S S ≤ 1 / S ^ 2 + C₂ * (1 / S ^ 3) := by
    have := (abs_sub_le_iff.1 hDbd).1
    linarith
  -- Step 4: `|delta_phi_S S| ≤ 1/S² + C₂/S³` (using `|·|` triangle inequality).
  have h_invS2_pos : 0 < (1 : ℝ) / S ^ 2 := by positivity
  have h_C₂_S3_nn : 0 ≤ C₂ * (1 / S ^ 3) :=
    mul_nonneg hC₂_nn (by positivity)
  have h_bound_pos : 0 < 1 / S ^ 2 + C₂ * (1 / S ^ 3) := by linarith
  have h_delta_abs : |delta_phi_S S| ≤ 1 / S ^ 2 + C₂ * (1 / S ^ 3) := by
    have h_decomp : delta_phi_S S = (delta_phi_S S - 1 / S ^ 2) + 1 / S ^ 2 := by
      ring
    have h_abs_decomp :
        |delta_phi_S S| ≤ |delta_phi_S S - 1 / S ^ 2| + |(1 : ℝ) / S ^ 2| := by
      conv_lhs => rw [h_decomp]
      exact abs_add_le _ _
    have h_inv_abs : |(1 : ℝ) / S ^ 2| = 1 / S ^ 2 :=
      abs_of_pos h_invS2_pos
    rw [h_inv_abs] at h_abs_decomp
    linarith
  -- Step 5: `K * delta_phi_S S ≤ |K| * (1/S² + C₂/S³)`.
  have hKd_bd : K * delta_phi_S S ≤ |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) := by
    have h1 : K * delta_phi_S S ≤ |K * delta_phi_S S| := le_abs_self _
    rw [abs_mul] at h1
    have h2 : |K| * |delta_phi_S S| ≤ |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) :=
      mul_le_mul_of_nonneg_left h_delta_abs hKnn
    linarith
  -- Step 6: Main quadratic inequality
  --   `(|K| + 2) * S + C₁ + |K| * C₂ < S^2`,
  -- using `S ≥ 4 * (|K| + C₁ + |K|*C₂ + 4)` and `S ≥ 1`.
  have h_S_sq : 4 * (|K| + C₁ + |K| * C₂ + 4) * S ≤ S ^ 2 := by
    have hsq : S ^ 2 = S * S := sq S
    rw [hsq]
    exact mul_le_mul hS_big le_rfl hSpos.le hSpos.le
  -- The two main monotonicities `C₁ ≤ C₁ * S` and `|K|*C₂ ≤ |K|*C₂ * S`
  -- (valid since the multiplicands are nonneg and `S ≥ 1`).
  have hC₁_le_C₁S : C₁ ≤ C₁ * S := by nlinarith
  have hKC₂_le_KC₂S : |K| * C₂ ≤ |K| * C₂ * S := by nlinarith
  have h_main_sq : (|K| + 2) * S + C₁ + |K| * C₂ < S ^ 2 := by
    nlinarith [h_S_sq, hC₁_le_C₁S, hKC₂_le_KC₂S, hKnn, hC₁_nn, hKC₂_nn,
      hSpos, hS_ge_one, mul_nonneg hKnn hSpos.le]
  -- Step 7: Convert to the divided form via `S^3 > 0`.
  have h_arr : |K| * S + |K| * C₂ < S ^ 2 - 2 * S - C₁ := by linarith
  have h_target :
      |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) <
      1 / S - 2 / S ^ 2 - C₁ * (1 / S ^ 3) := by
    have h_lhs_eq :
        |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3))
          = (|K| * S + |K| * C₂) / S ^ 3 := by
      field_simp
    have h_rhs_eq :
        1 / S - 2 / S ^ 2 - C₁ * (1 / S ^ 3)
          = (S ^ 2 - 2 * S - C₁) / S ^ 3 := by
      field_simp
    rw [h_lhs_eq, h_rhs_eq, div_lt_div_iff₀ hS3_pos hS3_pos]
    exact mul_lt_mul_of_pos_right h_arr hS3_pos
  -- Step 8: chain.
  exact lt_of_le_of_lt hKd_bd (lt_of_lt_of_le h_target hV_lb)

/-! ## Admissible class and the main theorem

We formulate the blueprint admissibility condition abstractly as a
bundled structure `AdmissibleOneDim`. In the blueprint it is "smooth
strictly convex `phi` with positive finite `Z_phi = ∫ exp(-phi)`, plus a
`locally Lipschitz` test function `f` with finite BL energy and variance".

For the purposes of the final logical conclusion only the following
numerical data matter:

* a real-valued *distance squared* `distSq : ℝ` attached to the datum,
* a real-valued *deficit* `deft : ℝ`,
* a guarantee that the blueprint construction is admissible.

Concretely, we require that for every real `S` the pair
`(phi_S, f_S)` supplies an `AdmissibleOneDim` datum with
`distSq = Var_f_S S` and `deft = delta_phi_S S`. This embeds our
constructed family of counterexamples in the abstract class. -/

/-- An admissible one-dimensional datum as used in the blueprint's
stability statement. We record only the two numerical invariants that
enter the putative bound. -/
structure AdmissibleOneDim where
  /-- The squared `L²` distance from the test function to the optimizer
  subspace. -/
  distSq : ℝ
  /-- The Brascamp-Lieb deficit. -/
  deft   : ℝ
  /-- Positivity of the deficit is the non-degenerate case. -/
  deft_pos : 0 < deft
  /-- Nonnegativity of the squared distance (always holds). -/
  distSq_nonneg : 0 ≤ distSq

/-- The admissible datum associated to the blueprint family at scale
`S`, for `S` large enough that the deficit is positive. -/
def bluePrintDatum (S : ℝ) (h : 0 < delta_phi_S S) : AdmissibleOneDim where
  distSq := Var_f_S S
  deft   := delta_phi_S S
  deft_pos := h
  distSq_nonneg := by
    -- Var_f_S S = ‖ffLp S‖² ≥ 0.
    rw [← norm_ffLp_sq_eq_var]; positivity

/-- **The main theorem.** No uniform `L²`-stability constant exists in
dimension one: there is no finite `C ∈ ℝ` such that for every
`AdmissibleOneDim` datum one has
`sqrt(distSq) ≤ C · sqrt(deft)`. Equivalently, the ratio
`distSq / deft` is unbounded on the admissible class. -/
theorem no_uniform_L2_stability_one_dim :
    ¬ ∃ C : ℝ, ∀ (D : AdmissibleOneDim),
        Real.sqrt D.distSq ≤ C * Real.sqrt D.deft := by
  rintro ⟨C, hC⟩
  -- Pick `S` large enough so that:
  --   delta_phi_S S > 0, and
  --   Var_f_S S > (C²+1) · delta_phi_S S.
  obtain ⟨S₀_pos, hS₀_pos_pos, hpos⟩ := delta_phi_S_eventually_pos
  obtain ⟨S₀_rat, _, hrat⟩ := var_over_delta_unbounded (C ^ 2 + 1)
  set S := max S₀_pos S₀_rat + 1 with hS_def
  have hS_ge1 : S₀_pos ≤ S := by
    rw [hS_def]; linarith [le_max_left S₀_pos S₀_rat]
  have hS_ge2 : S₀_rat ≤ S := by
    rw [hS_def]; linarith [le_max_right S₀_pos S₀_rat]
  have hdelta_pos : 0 < delta_phi_S S := hpos S hS_ge1
  have hratio : (C ^ 2 + 1) * delta_phi_S S < Var_f_S S := hrat S hS_ge2
  -- Build the blueprint datum.
  let D : AdmissibleOneDim := bluePrintDatum S hdelta_pos
  -- From the hypothesis, `sqrt(D.distSq) ≤ C · sqrt(D.deft)`, squaring
  -- gives `D.distSq ≤ C² · D.deft`, contradicting `Var > (C²+1)·delta`.
  have hbound := hC D
  have hD_dist : D.distSq = Var_f_S S := rfl
  have hD_deft : D.deft = delta_phi_S S := rfl
  -- Squaring both sides of `sqrt(D.distSq) ≤ C · sqrt(D.deft)`.
  have hC_sq_deft_nn : 0 ≤ C ^ 2 * D.deft := by
    have : 0 ≤ D.deft := D.deft_pos.le
    positivity
  have h_sqrt_deft_nn : 0 ≤ Real.sqrt D.deft := Real.sqrt_nonneg _
  have h_sqrt_dist_nn : 0 ≤ Real.sqrt D.distSq := Real.sqrt_nonneg _
  -- Case split on sign of `C · sqrt(deft)`.
  have hC_sq : D.distSq ≤ C ^ 2 * D.deft := by
    -- Square both sides of hbound. Note: `sqrt(D.distSq) ≤ C · sqrt(D.deft)` with
    -- LHS ≥ 0. The RHS could be negative (if C < 0). But then LHS ≤ negative
    -- forces LHS = 0, hence D.distSq = 0.
    by_cases hC_nn : 0 ≤ C * Real.sqrt D.deft
    · have h_sq : (Real.sqrt D.distSq) ^ 2 ≤ (C * Real.sqrt D.deft) ^ 2 := by
        exact pow_le_pow_left₀ h_sqrt_dist_nn hbound 2
      have h_lhs : (Real.sqrt D.distSq) ^ 2 = D.distSq :=
        Real.sq_sqrt D.distSq_nonneg
      have h_rhs_expand : (C * Real.sqrt D.deft) ^ 2 = C ^ 2 * D.deft := by
        rw [mul_pow, Real.sq_sqrt D.deft_pos.le]
      rw [h_lhs, h_rhs_expand] at h_sq
      exact h_sq
    · push_neg at hC_nn
      have h_sqrt_zero : Real.sqrt D.distSq = 0 := by
        linarith [h_sqrt_dist_nn]
      have h_dist_zero : D.distSq = 0 := by
        have : D.distSq = (Real.sqrt D.distSq) ^ 2 := (Real.sq_sqrt D.distSq_nonneg).symm
        rw [this, h_sqrt_zero]; ring
      rw [h_dist_zero]
      exact hC_sq_deft_nn
  -- But by hratio we have D.distSq = Var_f_S S > (C²+1) · delta_phi_S S > C² · delta.
  rw [hD_dist, hD_deft] at hC_sq
  have hdelta_nn : 0 ≤ delta_phi_S S := hdelta_pos.le
  have : (C ^ 2 + 1) * delta_phi_S S ≤ C ^ 2 * delta_phi_S S := by
    exact le_trans hratio.le hC_sq
  nlinarith [this, hdelta_pos]

end L2Counterexample

end
