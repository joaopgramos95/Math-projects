import L2Counterexample.Normalization
import Mathlib

/-!
# Test function (WIP)

This is the editable WIP version of `TestFunction.lean`. It defines the
real-valued piecewise test function `g_S` and proves the elementary facts about
it.

Target statements:

* endpoint values and range bounds;
* evenness;
* a.e. derivative formulas on the core, transition, and tail regions;
* denominator positivity;
* concrete energy/deficit definitions for the constructed family;
* layer energy identity (task #9);
* variance computation (task #10).

The upstream API (normalization constants, potential, region boundaries) is
imported from `L2Counterexample.Normalization` / `L2Counterexample.Potential`.
Because those modules are currently empty stubs, the data we consume from them
is declared here as local `axiom`s with signatures matching the blueprint.
Once the upstream modules are populated, these axioms should be replaced by
`theorem` statements that `exact?` from the real definitions.
-/

namespace L2Counterexample

open MeasureTheory Set Asymptotics

/-! ## Upstream API and additional facts

`phi_S, phiDer_S, phiDer2_S, eps_S, eta_S` come from `Potential.lean`.
`Z_S, q_S, t_S` come from `Normalization.lean`. The remaining facts —
the layer normalizer `A_S`, the probability measure `rho_S`, and the
asymptotic axioms specific to the test function — are recorded here. -/

/-- We require `ε < 1`, which holds for `S > 1`. -/
lemma eps_S_lt_one {S : ℝ} (hS : 1 < S) : eps_S S < 1 := by
  unfold eps_S
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have : (S ^ (3 : ℕ))⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    have h1 : (1 : ℝ) < S ^ (1 : ℕ) := by simpa using hS
    have h2 : S ^ (1 : ℕ) ≤ S ^ (3 : ℕ) := by
      apply pow_le_pow_right₀ (le_of_lt hS) (by norm_num)
    linarith
  simpa [zpow_neg, zpow_natCast] using this

/-- The probability measure `ρ_S` on `ℝ` with density `Z_S^{-1} exp(-φ_S)`.

Defined concretely via `Measure.withDensity` so that downstream
properties (`IsProbabilityMeasure`, reflection invariance) become
*derivable* rather than axiomatic. -/
noncomputable def rho_S (S : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.withDensity
    (fun x => ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))))

/-- The potential is nonneg everywhere. Follows from
`phi_S_quadratic_lower` (`phi_S S x ≥ η_S x²/2 ≥ 0`). -/
theorem phi_S_nonneg {S : ℝ} (hS : 0 < S) (x : ℝ) : 0 ≤ phi_S S x := by
  have hq := phi_S_quadratic_lower hS x
  have h_eta : 0 ≤ eta_S S := (eta_S_pos hS).le
  have h_quad : 0 ≤ eta_S S * x ^ 2 / 2 := by
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg _
    have := mul_nonneg h_eta hx2
    linarith
  linarith

/-- `φ''_S` is strictly positive, from `Potential.phiDer2_S_pos`. -/
theorem phiDer2_S_pos_TF {S : ℝ} (hS : 0 < S) (x : ℝ) : 0 < phiDer2_S S x :=
  phiDer2_S_pos hS x

/-- Continuity of `φ_S` from `phi_S_contDiff`. -/
theorem phi_S_continuous {S : ℝ} (hS : 0 < S) : Continuous (phi_S S) :=
  (phi_S_contDiff hS).continuous

/-- Continuity of `φ''_S` from `phiDer2_S_contDiff`. -/
theorem phiDer2_S_continuous_TF {S : ℝ} (hS : 0 < S) : Continuous (phiDer2_S S) :=
  phiDer2_S_continuous hS

/-- The integrand `φ''_S · exp(φ_S)` is locally integrable. Follows
from continuity of both factors. -/
theorem phi_integrand_intervalIntegrable {S : ℝ} (hS : 0 < S) (a b : ℝ) :
    IntervalIntegrable (fun t => phiDer2_S S t * Real.exp (phi_S S t))
      MeasureTheory.volume a b := by
  refine ((phiDer2_S_continuous hS).mul ?_).intervalIntegrable _ _
  exact (Real.continuous_exp.comp (phi_S_contDiff hS).continuous)

/-- The layer normalizer `A_S := ∫_{1-ε..1+ε} φ''_S(t) · exp(φ_S(t)) dt`.

Note: the blueprint reserves the symbol `A_S` for this layer integral.
The right-tail integral that appears in `Normalization.lean` is named
`tailInt_S` to avoid the clash. -/
noncomputable def A_S (S : ℝ) : ℝ :=
  ∫ t in (1 - eps_S S)..(1 + eps_S S),
      phiDer2_S S t * Real.exp (phi_S S t)

/-- Definitional equality `A_S` ↔ the interval integral. -/
lemma A_S_intervalIntegral_def {S : ℝ} (_hS_large : 1 < S) :
    ∫ t in (1 - eps_S S)..(1 + eps_S S),
        phiDer2_S S t * Real.exp (phi_S S t) = A_S S := rfl

/-- Symmetry of the layer integrals: the integral over `I_S^-` equals the
integral over `I_S^+`. Follows from evenness of `φ_S` and `φ''_S` plus the
change of variables `t ↦ -t`. -/
theorem A_S_symm {S : ℝ} (hS_large : 1 < S) :
    ∫ t in Set.Ioo (-1 - eps_S S) (-1 + eps_S S),
        phiDer2_S S t * Real.exp (phi_S S t) = A_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS_large
  have hε_pos : 0 < eps_S S := eps_S_pos hSpos
  have h_le : -1 - eps_S S ≤ -1 + eps_S S := by linarith
  -- Step 1: convert set integral to interval integral.
  have step1 : ∫ t in Set.Ioo (-1 - eps_S S) (-1 + eps_S S),
                  phiDer2_S S t * Real.exp (phi_S S t)
             = ∫ t in (-1 - eps_S S)..(-1 + eps_S S),
                  phiDer2_S S t * Real.exp (phi_S S t) := by
    rw [intervalIntegral.integral_of_le h_le]
    exact MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc
  -- Step 2: substitute via evenness of the integrand.
  have step2 : ∫ t in (-1 - eps_S S)..(-1 + eps_S S),
                  phiDer2_S S t * Real.exp (phi_S S t)
             = ∫ t in (-1 - eps_S S)..(-1 + eps_S S),
                  phiDer2_S S (-t) * Real.exp (phi_S S (-t)) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp [phiDer2_S_even, phi_S_even]
  -- Step 3: change of variables `t ↦ -t`.
  have step3 : ∫ t in (-1 - eps_S S)..(-1 + eps_S S),
                  phiDer2_S S (-t) * Real.exp (phi_S S (-t))
             = ∫ t in -(-1 + eps_S S)..-(-1 - eps_S S),
                  phiDer2_S S t * Real.exp (phi_S S t) :=
    intervalIntegral.integral_comp_neg
      (fun t => phiDer2_S S t * Real.exp (phi_S S t))
  -- Simplify endpoints and conclude.
  have h_eq1 : -(-1 + eps_S S) = 1 - eps_S S := by ring
  have h_eq2 : -(-1 - eps_S S) = 1 + eps_S S := by ring
  rw [step1, step2, step3, h_eq1, h_eq2]
  rfl

/-- Positivity of the layer normalizer. The integrand
`φ''_S(t) · exp(φ_S(t))` is strictly positive (`phiDer2_S_pos` and
`Real.exp_pos`), and the interval `[1-ε, 1+ε]` has positive length. -/
theorem A_S_pos {S : ℝ} (hS_large : 1 < S) : 0 < A_S S := by
  have hS : 0 < S := lt_trans zero_lt_one hS_large
  have heps : 0 < eps_S S := eps_S_pos hS
  have hlt : 1 - eps_S S < 1 + eps_S S := by linarith
  have h_int_pos : ∀ t, 0 < phiDer2_S S t * Real.exp (phi_S S t) := fun t =>
    mul_pos (phiDer2_S_pos hS t) (Real.exp_pos _)
  have h_cont : Continuous (fun t => phiDer2_S S t * Real.exp (phi_S S t)) :=
    (phiDer2_S_continuous hS).mul (Real.continuous_exp.comp (phi_S_contDiff hS).continuous)
  unfold A_S
  exact intervalIntegral.intervalIntegral_pos_of_pos
    (h_cont.intervalIntegrable _ _) h_int_pos hlt

/-- Bridge: `BigOInv` implies the corresponding `IsBigO` over `atTop`. -/
private lemma BigOInv.toIsBigO_aux {f g : ℝ → ℝ} {k : ℕ} (h : BigOInv f g k) :
    (fun S => f S - g S) =O[Filter.atTop] fun S : ℝ => S ^ (-(k : ℤ)) := by
  obtain ⟨C, S₀, hS₀, hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  rw [Filter.eventually_atTop]
  refine ⟨S₀, fun S hS => ?_⟩
  have hpow_pos : 0 < S ^ (-(k : ℤ)) := zpow_pos (lt_of_lt_of_le hS₀ hS) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpow_pos]
  exact hb S hS

/-- Asymptotic `q_S = 1/S - 1/S^2 + O(S^{-3})`, in `IsBigO` form.
(Bridge from `Normalization.q_S_asymp` which is in `BigOInv` form.) -/
theorem q_S_isBigO :
    (fun S : ℝ => q_S S - (1/S - 1/S^2)) =O[Filter.atTop]
      fun S : ℝ => (S : ℝ)^(-3 : ℤ) :=
  BigOInv.toIsBigO_aux L2Counterexample.q_S_asymp

/-- Asymptotic `t_S = O(S^{-3})`, in `IsBigO` form. -/
theorem t_S_isBigO :
    (fun S : ℝ => t_S S) =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-3 : ℤ) := by
  have h := BigOInv.toIsBigO_aux L2Counterexample.t_S_asymp
  simpa using h

/-- Helper: on `[1 - ε_S, 1 + ε_S]` (with `eps_S ≤ 1`), the second bump
`κ((t+1)/ε_S)` vanishes pointwise. -/
private lemma kappa_shift_right_zero_on_layer {S t : ℝ} (hS : 1 ≤ S)
    (ht : t ∈ Set.uIcc (1 - eps_S S) (1 + eps_S S)) :
    kappa ((t + 1) / eps_S S) = 0 := by
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have heps_le_one : eps_S S ≤ 1 := by
    unfold eps_S
    rw [show ((-(3 : ℤ))) = -((3 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hS)
  have h_le : 1 - eps_S S ≤ 1 + eps_S S := by linarith
  rw [Set.uIcc_of_le h_le, Set.mem_Icc] at ht
  -- t ≥ 1 - ε, so t + 1 ≥ 2 - ε ≥ 1 (since ε ≤ 1).
  have h_t_plus_1 : 1 ≤ (t + 1) / eps_S S := by
    rw [le_div_iff₀ heps_pos]
    linarith [ht.1]
  apply kappa_eq_zero_of_abs_ge_one
  rw [abs_of_pos (by linarith : (0 : ℝ) < (t + 1) / eps_S S)]
  exact h_t_plus_1

/-- Helper: integral of `phi''_S` on the positive layer
`[1-ε, 1+ε]` equals `S + 2·η_S·ε`. -/
private lemma integral_phiDer2_S_layer {S : ℝ} (hS : 1 ≤ S) :
    ∫ t in (1 - eps_S S)..(1 + eps_S S), phiDer2_S S t
      = S + 2 * eta_S S * eps_S S := by
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have heps_ne : eps_S S ≠ 0 := heps_pos.ne'
  -- Replace the integrand with the simplified form (third kappa = 0 on layer).
  have h_eq_on_layer : ∀ t ∈ Set.uIcc (1 - eps_S S) (1 + eps_S S),
      phiDer2_S S t = eta_S S + (S / eps_S S) * kappa ((t - 1) / eps_S S) := by
    intro t ht
    have h3 : kappa ((t + 1) / eps_S S) = 0 :=
      kappa_shift_right_zero_on_layer hS ht
    unfold phiDer2_S
    rw [h3, mul_zero, add_zero]
  rw [intervalIntegral.integral_congr h_eq_on_layer]
  -- Integral of (eta_S + first kappa) = ∫ eta_S + ∫ first kappa.
  have h_int_eta : IntervalIntegrable (fun _ : ℝ => eta_S S) MeasureTheory.volume
      (1 - eps_S S) (1 + eps_S S) :=
    intervalIntegrable_const
  have h_int_kappa : IntervalIntegrable
      (fun t => (S / eps_S S) * kappa ((t - 1) / eps_S S)) MeasureTheory.volume
      (1 - eps_S S) (1 + eps_S S) := by
    refine (continuous_const.mul ?_).intervalIntegrable _ _
    refine kappa_continuous.comp ?_
    continuity
  rw [intervalIntegral.integral_add h_int_eta h_int_kappa]
  -- ∫ eta_S = eta_S · 2ε.
  rw [intervalIntegral.integral_const, smul_eq_mul]
  -- ∫ (S/ε)·κ((t-1)/ε) = S.
  rw [kappa_scaled_integral_right hSpos]
  ring

/-- Asymptotic `A_S - S = O(S^{-1})`.

Decomposition: `A_S = ∫_{1-ε}^{1+ε} phi''_S(t)·exp(phi_S(t)) dt
              = ∫ phi''_S + ∫ phi''_S·(exp(phi_S) - 1)
              = (S + 2·η_S·ε) + R`
where `|R| ≤ (sup |exp(phi_S(t))-1| on layer) · (S + 2·η_S·ε) = O(S^{-2}) · O(S) = O(S^{-1})`. -/
theorem A_S_asymp :
    (fun S : ℝ => A_S S - S) =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-1 : ℤ) := by
  obtain ⟨C_layer, S_layer, hS_layer_pos, h_layer_bd⟩ := phi_S_layer_small
  -- Make C_layer nonneg.
  have hC_layer_nn : 0 ≤ C_layer := by
    have hε_layer : 0 < eps_S S_layer := eps_S_pos hS_layer_pos
    have h := h_layer_bd S_layer le_rfl 1 (by simp; linarith [hε_layer])
    have h_abs_nn : 0 ≤ |Real.exp (-(phi_S S_layer 1)) - 1| := abs_nonneg _
    have h_pow_pos : (0 : ℝ) < S_layer ^ (-(2 : ℤ)) := zpow_pos hS_layer_pos _
    nlinarith
  -- Pick S₀ so that C_layer/S² ≤ 1/2.
  -- Need S² ≥ 2 C_layer, i.e., S ≥ √(2 C_layer).
  refine IsBigO.of_bound (4 * C_layer + 2) ?_
  rw [Filter.eventually_atTop]
  refine ⟨max (max S_layer 2) (Real.sqrt (2 * C_layer) + 1), fun S hS => ?_⟩
  have hS_layer : S_layer ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hS)
  have hS_2 : (2 : ℝ) ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hS_one : (1 : ℝ) ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hS_sqrt : Real.sqrt (2 * C_layer) + 1 ≤ S :=
    le_trans (le_max_right _ _) hS
  -- C_layer / S² ≤ 1/2.
  have hCS2_le_half : C_layer / S^2 ≤ 1/2 := by
    have h_sqrt_nn : 0 ≤ Real.sqrt (2 * C_layer) := Real.sqrt_nonneg _
    have hS_sqrt_lt : Real.sqrt (2 * C_layer) < S := by linarith
    have hS_sq : S^2 ≥ 2 * C_layer := by
      have h1 : (Real.sqrt (2 * C_layer))^2 = 2 * C_layer :=
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * C_layer)
      have h2 : (Real.sqrt (2 * C_layer))^2 < S^2 := by
        nlinarith [hS_sqrt_lt, h_sqrt_nn]
      linarith
    have hS2_pos : (0 : ℝ) < S^2 := by positivity
    rw [div_le_iff₀ hS2_pos]
    linarith
  -- Setup constants.
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have heta_pos : 0 < eta_S S := eta_S_pos hSpos
  have h_le : 1 - eps_S S ≤ 1 + eps_S S := by linarith
  have h_int_layer := integral_phiDer2_S_layer hS_one
  -- exp(-phi_S(t)) ≥ 1/2 on the layer (so exp(phi_S(t)) ≤ 2).
  have h_exp_neg_lb : ∀ t, |t - 1| ≤ eps_S S → 1/2 ≤ Real.exp (-(phi_S S t)) := by
    intro t ht
    have h := h_layer_bd S hS_layer t ht
    have h_phi_nn : 0 ≤ phi_S S t := phi_S_nonneg hSpos t
    have h_exp_le_one : Real.exp (-(phi_S S t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have h_neg_le_zero : Real.exp (-(phi_S S t)) - 1 ≤ 0 := by linarith
    have h_abs_eq : |Real.exp (-(phi_S S t)) - 1| = 1 - Real.exp (-(phi_S S t)) := by
      rw [abs_of_nonpos h_neg_le_zero]; ring
    have h_diff_le : 1 - Real.exp (-(phi_S S t)) ≤ C_layer * S^(-(2:ℤ)) := by
      rw [← h_abs_eq]; exact h
    have h_pow : (S : ℝ)^(-(2:ℤ)) = 1/S^2 := by
      rw [show (-(2:ℤ)) = -((2:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
      exact (one_div _).symm
    rw [h_pow] at h_diff_le
    have h_simp : C_layer * (1/S^2) = C_layer / S^2 := by ring
    linarith [hCS2_le_half]
  -- |exp(phi_S(t)) - 1| ≤ 2 · C_layer/S² on the layer.
  have h_exp_pos_bd : ∀ t, |t - 1| ≤ eps_S S
      → |Real.exp (phi_S S t) - 1| ≤ 2 * (C_layer / S^2) := by
    intro t ht
    have h_neg_lb := h_exp_neg_lb t ht
    have h_phi_nn : 0 ≤ phi_S S t := phi_S_nonneg hSpos t
    have h_exp_pos_pos : 0 < Real.exp (phi_S S t) := Real.exp_pos _
    have h_exp_pos_ge_one : 1 ≤ Real.exp (phi_S S t) := Real.one_le_exp h_phi_nn
    have h_diff_nn : 0 ≤ Real.exp (phi_S S t) - 1 := by linarith
    have h_abs_eq : |Real.exp (phi_S S t) - 1| = Real.exp (phi_S S t) - 1 :=
      abs_of_nonneg h_diff_nn
    rw [h_abs_eq]
    have h_exp_neg_ne : Real.exp (-(phi_S S t)) ≠ 0 := (Real.exp_pos _).ne'
    have h_eq : Real.exp (phi_S S t) - 1
              = (1 - Real.exp (-(phi_S S t))) / Real.exp (-(phi_S S t)) := by
      rw [Real.exp_neg]
      field_simp
    rw [h_eq]
    have h := h_layer_bd S hS_layer t ht
    have h_pow : (S : ℝ)^(-(2:ℤ)) = 1/S^2 := by
      rw [show (-(2:ℤ)) = -((2:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
      exact (one_div _).symm
    rw [h_pow] at h
    have h_simp : C_layer * (1 / S ^ 2) = C_layer / S^2 := by ring
    rw [h_simp] at h
    have h_exp_neg_le_one : Real.exp (-(phi_S S t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have h_neg_le_zero : Real.exp (-(phi_S S t)) - 1 ≤ 0 := by linarith
    have h_abs_one_minus : |Real.exp (-(phi_S S t)) - 1|
                       = 1 - Real.exp (-(phi_S S t)) := by
      rw [abs_of_nonpos h_neg_le_zero]; ring
    rw [h_abs_one_minus] at h
    -- (1 - exp(-phi))/exp(-phi) ≤ (C/S²)/(1/2) = 2(C/S²)
    have h_div_le : (1 - Real.exp (-(phi_S S t))) / Real.exp (-(phi_S S t))
                  ≤ (C_layer / S^2) / (1/2) := by
      have hC_S2_nn : 0 ≤ C_layer / S^2 := by positivity
      have h_half_pos : (0 : ℝ) < 1/2 := by norm_num
      exact div_le_div₀ hC_S2_nn h h_half_pos h_neg_lb
    have h_eq2 : (C_layer / S^2) / (1/2) = 2 * (C_layer / S^2) := by ring
    linarith
  -- A_S - (S + 2 η ε) = ∫ phi''_S · (exp(phi_S) - 1).
  have h_A_decomp : A_S S - (S + 2 * eta_S S * eps_S S)
                  = ∫ t in (1 - eps_S S)..(1 + eps_S S),
                      phiDer2_S S t * (Real.exp (phi_S S t) - 1) := by
    unfold A_S
    have h_pointwise : ∀ t, phiDer2_S S t * Real.exp (phi_S S t)
                          = phiDer2_S S t + phiDer2_S S t * (Real.exp (phi_S S t) - 1) := by
      intro t; ring
    rw [show (fun t => phiDer2_S S t * Real.exp (phi_S S t))
          = (fun t => phiDer2_S S t + phiDer2_S S t * (Real.exp (phi_S S t) - 1))
          from funext h_pointwise]
    have h_int_phi'' : IntervalIntegrable (phiDer2_S S) MeasureTheory.volume
        (1 - eps_S S) (1 + eps_S S) :=
      (phiDer2_S_continuous hSpos).intervalIntegrable _ _
    have h_int_rest : IntervalIntegrable
        (fun t => phiDer2_S S t * (Real.exp (phi_S S t) - 1)) MeasureTheory.volume
        (1 - eps_S S) (1 + eps_S S) := by
      refine (((phiDer2_S_continuous hSpos).mul
        ((Real.continuous_exp.comp (phi_S_contDiff hSpos).continuous).sub
          continuous_const))).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h_int_phi'' h_int_rest]
    rw [h_int_layer]
    ring
  -- Bound the integral on the right.
  have h_R_bd : |∫ t in (1 - eps_S S)..(1 + eps_S S),
                  phiDer2_S S t * (Real.exp (phi_S S t) - 1)|
              ≤ 4 * C_layer / S := by
    -- |∫| ≤ ∫ |·| ≤ ∫ phi''_S · 2C/S² = (S + 2η ε)·(2C/S²) ≤ 2S·2C/S² = 4C/S.
    have h_int_bd : ∀ t ∈ Set.Icc (1 - eps_S S) (1 + eps_S S),
        |phiDer2_S S t * (Real.exp (phi_S S t) - 1)|
          ≤ phiDer2_S S t * (2 * (C_layer / S^2)) := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have htL1 : |t - 1| ≤ eps_S S := abs_le.mpr ⟨by linarith, by linarith⟩
      have h_phi''_nn : 0 ≤ phiDer2_S S t := (phiDer2_S_pos hSpos t).le
      rw [abs_mul, abs_of_nonneg h_phi''_nn]
      exact mul_le_mul_of_nonneg_left (h_exp_pos_bd t htL1) h_phi''_nn
    -- Apply norm_intervalIntegral_le_of_norm_le_const_with_le.
    have h_norm_bd : |∫ t in (1 - eps_S S)..(1 + eps_S S),
                      phiDer2_S S t * (Real.exp (phi_S S t) - 1)|
                  ≤ ∫ t in (1 - eps_S S)..(1 + eps_S S),
                      phiDer2_S S t * (2 * (C_layer / S^2)) := by
      have h_int_orig : IntervalIntegrable
        (fun t => phiDer2_S S t * (Real.exp (phi_S S t) - 1))
        MeasureTheory.volume (1 - eps_S S) (1 + eps_S S) := by
        refine (((phiDer2_S_continuous hSpos).mul
          ((Real.continuous_exp.comp (phi_S_contDiff hSpos).continuous).sub
            continuous_const))).intervalIntegrable _ _
      have h_int_bound : IntervalIntegrable
        (fun t => phiDer2_S S t * (2 * (C_layer / S^2)))
        MeasureTheory.volume (1 - eps_S S) (1 + eps_S S) :=
        ((phiDer2_S_continuous hSpos).mul continuous_const).intervalIntegrable _ _
      -- Use abs_integral_le_integral_abs.
      have h_abs_le : |∫ t in (1 - eps_S S)..(1 + eps_S S),
                        phiDer2_S S t * (Real.exp (phi_S S t) - 1)|
                    ≤ ∫ t in (1 - eps_S S)..(1 + eps_S S),
                        |phiDer2_S S t * (Real.exp (phi_S S t) - 1)| :=
        intervalIntegral.abs_integral_le_integral_abs h_le
      refine le_trans h_abs_le ?_
      exact intervalIntegral.integral_mono_on h_le h_int_orig.abs h_int_bound h_int_bd
    refine le_trans h_norm_bd ?_
    -- ∫ phi''_S · 2C/S² = (2C/S²) · ∫ phi''_S = (2C/S²) · (S + 2 η ε)
    rw [intervalIntegral.integral_mul_const]
    rw [h_int_layer]
    -- (S + 2 η ε) · (2C/S²) ≤ 4C/S.
    have h_eta_eps_small : 2 * eta_S S * eps_S S ≤ S := by
      -- 2 · eta_S · eps = 2 · S^{-4} · S^{-3} = 2/S^7 ≤ S for S ≥ 1.
      have h_eta_eq : eta_S S = 1/S^4 := by
        unfold eta_S
        rw [show (-(4:ℤ)) = -((4:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
      have h_eps_eq : eps_S S = 1/S^3 := by
        unfold eps_S
        rw [show (-(3:ℤ)) = -((3:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
      rw [h_eta_eq, h_eps_eq]
      have hS3_pos : (0 : ℝ) < S^3 := by positivity
      have hS4_pos : (0 : ℝ) < S^4 := by positivity
      have h_eq : 2 * (1 / S^4) * (1 / S^3) = 2 / S^7 := by
        have hS_ne : (S : ℝ) ≠ 0 := hSpos.ne'
        have h_pow : (S : ℝ)^4 * S^3 = S^7 := by ring
        field_simp
      rw [h_eq]
      -- 2/S^7 ≤ S iff 2 ≤ S^8 (for S > 0). For S ≥ 2: S^8 ≥ 256 ≥ 2.
      have hS7_pos : (0 : ℝ) < S^7 := by positivity
      rw [div_le_iff₀ hS7_pos]
      have h_S8_ge : (256 : ℝ) ≤ S^8 := by
        have : (2 : ℝ)^8 = 256 := by norm_num
        rw [← this]
        exact pow_le_pow_left₀ (by linarith) hS_2 8
      nlinarith
    have h_key : (S + 2 * eta_S S * eps_S S) * (2 * (C_layer / S^2))
              ≤ (2 * S) * (2 * (C_layer / S^2)) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · positivity
    have h_simp : (2 * S) * (2 * (C_layer / S^2)) = 4 * C_layer / S := by
      have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
      field_simp
      ring
    linarith
  -- Final: |A_S - S| ≤ |2 η ε| + |R| ≤ 2/S^7 + 4C/S ≤ (4C + 2)/S.
  have h_A_diff : A_S S - S = 2 * eta_S S * eps_S S
      + (∫ t in (1 - eps_S S)..(1 + eps_S S),
          phiDer2_S S t * (Real.exp (phi_S S t) - 1)) := by linarith [h_A_decomp]
  have h_2eta_eps_bd : |2 * eta_S S * eps_S S| ≤ 2 / S := by
    have h_pos : 0 ≤ 2 * eta_S S * eps_S S := by positivity
    rw [abs_of_nonneg h_pos]
    have h_eta_eq : eta_S S = 1/S^4 := by
      unfold eta_S
      rw [show (-(4:ℤ)) = -((4:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
    have h_eps_eq : eps_S S = 1/S^3 := by
      unfold eps_S
      rw [show (-(3:ℤ)) = -((3:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
    rw [h_eta_eq, h_eps_eq]
    have h_eq : 2 * (1 / S^4) * (1 / S^3) = 2 / S^7 := by
      have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
      have h_pow : (S : ℝ)^4 * S^3 = S^7 := by ring
      field_simp
    rw [h_eq]
    -- 2/S^7 ≤ 2/S for S ≥ 1.
    have hS7_pos : (0 : ℝ) < S^7 := by positivity
    have h_S_le_S7 : S ≤ S^7 := by
      have h_S1 : S^1 = S := by ring
      have h_pow : S^1 ≤ S^7 := by
        have hS6_ge_one : (1 : ℝ) ≤ S^6 := one_le_pow₀ hS_one
        have h_eq : S^7 = S * S^6 := by ring
        nlinarith
      linarith [h_pow, h_S1]
    have h_div : (2 : ℝ) / S^7 ≤ 2 / S := by
      apply div_le_div_of_nonneg_left (by norm_num) hSpos h_S_le_S7
    exact h_div
  -- Now combine.
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hpow_eq : (S : ℝ)^(-(1:ℤ)) = 1/S := by
    rw [show (-(1:ℤ)) = -((1:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, pow_one, one_div]
  rw [hpow_eq, abs_of_pos (by positivity : (0:ℝ) < 1/S)]
  rw [h_A_diff]
  have h_tri : |2 * eta_S S * eps_S S
              + (∫ t in (1 - eps_S S)..(1 + eps_S S),
                  phiDer2_S S t * (Real.exp (phi_S S t) - 1))|
            ≤ |2 * eta_S S * eps_S S|
              + |∫ t in (1 - eps_S S)..(1 + eps_S S),
                  phiDer2_S S t * (Real.exp (phi_S S t) - 1)| := abs_add_le _ _
  have h_total : |2 * eta_S S * eps_S S|
                + |∫ t in (1 - eps_S S)..(1 + eps_S S),
                    phiDer2_S S t * (Real.exp (phi_S S t) - 1)|
              ≤ 2/S + 4 * C_layer / S := by linarith [h_2eta_eps_bd, h_R_bd]
  have h_eq_final : 2/S + 4 * C_layer / S = (4 * C_layer + 2) * (1/S) := by
    field_simp; ring
  linarith

/-- Positivity of `Z_S` for `S > 1`. Follows from
`Normalization.Z_S_pos` (which only requires `0 < S`). -/
theorem Z_S_pos_TF {S : ℝ} (hS_large : 1 < S) : 0 < Z_S S :=
  Z_S_pos S (lt_trans zero_lt_one hS_large)

/-! ## Regions -/

/-- The core `C_S = [-1+ε, 1-ε]`. -/
def coreRegion (S : ℝ) : Set ℝ := Set.Icc (-1 + eps_S S) (1 - eps_S S)

/-- The positive layer `I_S^+ = (1-ε, 1+ε)`. -/
def layerPos (S : ℝ) : Set ℝ := Set.Ioo (1 - eps_S S) (1 + eps_S S)

/-- The negative layer `I_S^- = (-1-ε, -1+ε)`. -/
def layerNeg (S : ℝ) : Set ℝ := Set.Ioo (-1 - eps_S S) (-1 + eps_S S)

/-- The full transition `T_S := I_S^+ ∪ I_S^-`. -/
def transitionRegion (S : ℝ) : Set ℝ := layerPos S ∪ layerNeg S

/-- The exterior `E_S := ℝ \ (C_S ∪ T_S)`, i.e. `{|x| > 1+ε}` (as a set). -/
def exteriorRegion (S : ℝ) : Set ℝ := {x | 1 + eps_S S < |x|}

/-! ## The test function `g_S` -/

/-- The antiderivative numerator `N_S(r) := ∫_{1-ε}^r φ''_S(t) exp(φ_S(t)) dt`
for `r ∈ [1-ε, 1+ε]`. -/
noncomputable def N_S (S : ℝ) (r : ℝ) : ℝ :=
  ∫ t in (1 - eps_S S)..r, phiDer2_S S t * Real.exp (phi_S S t)

/-- The real-valued test function
`g_S(x) = 0` on `C_S`,
`g_S(x) = N_S(|x|) / A_S(S)` on `T_S`,
`g_S(x) = 1` on `E_S`.

We assemble this piecewise via the value of `|x|`, using the layer formula also
at the endpoints (where, by Lemma 4.3 in the blueprint, it evaluates to `0`
and `1`). -/
noncomputable def g_S (S : ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ 1 - eps_S S then 0
  else if |x| < 1 + eps_S S then N_S S |x| / A_S S
  else 1

/-! ## Endpoint values and range bounds -/

section EndpointAndRange

variable {S : ℝ}

/-- On the core, `g_S ≡ 0`. -/
lemma g_S_core_eq_zero (hS : 0 < S) {x : ℝ}
    (hx : x ∈ coreRegion S) : g_S S x = 0 := by
  unfold g_S
  have hxabs : |x| ≤ 1 - eps_S S := by
    rcases hx with ⟨h1, h2⟩
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]; exact h2
    · rw [abs_of_neg hx0]; linarith
  classical
  rw [if_pos hxabs]

/-- On the exterior, `g_S ≡ 1`. -/
lemma g_S_exterior_eq_one (hS : 0 < S) {x : ℝ}
    (hx : x ∈ exteriorRegion S) : g_S S x = 1 := by
  unfold g_S exteriorRegion at *
  have hxabs : 1 + eps_S S < |x| := hx
  have h1 : ¬ |x| ≤ 1 - eps_S S := by
    intro h
    have : eps_S S < 0 := by
      have hh : 1 + eps_S S < 1 - eps_S S := lt_of_lt_of_le hxabs h
      linarith
    linarith [eps_S_pos hS]
  have h2 : ¬ |x| < 1 + eps_S S := not_lt.mpr (le_of_lt hxabs)
  classical
  rw [if_neg h1, if_neg h2]

/-- On the positive layer, `g_S(x) = N_S(|x|) / A_S`. -/
lemma g_S_layer_pos_eq (hS : 1 < S) {x : ℝ} (hx : x ∈ layerPos S) :
    g_S S x = N_S S |x| / A_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  rcases hx with ⟨h1, h2⟩
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  have hx_pos : 0 < x := by linarith
  have hxabs : |x| = x := abs_of_pos hx_pos
  unfold g_S
  have hnotle : ¬ |x| ≤ 1 - eps_S S := by
    rw [hxabs]; push_neg; exact h1
  have hlt : |x| < 1 + eps_S S := by rw [hxabs]; exact h2
  classical
  rw [if_neg hnotle, if_pos hlt]

/-- On the negative layer, `g_S(x) = N_S(|x|) / A_S`. -/
lemma g_S_layer_neg_eq (hS : 1 < S) {x : ℝ} (hx : x ∈ layerNeg S) :
    g_S S x = N_S S |x| / A_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  rcases hx with ⟨h1, h2⟩
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  have hx_neg : x < 0 := by linarith
  have hxabs : |x| = -x := abs_of_neg hx_neg
  unfold g_S
  have hnotle : ¬ |x| ≤ 1 - eps_S S := by
    rw [hxabs]; push_neg; linarith
  have hlt : |x| < 1 + eps_S S := by rw [hxabs]; linarith
  classical
  rw [if_neg hnotle, if_pos hlt]

/-- Endpoint value: `N_S(1 - ε) = 0`. -/
lemma N_S_left_endpoint (S : ℝ) : N_S S (1 - eps_S S) = 0 := by
  unfold N_S
  exact intervalIntegral.integral_same

/-- Endpoint value: `N_S(1 + ε) = A_S`. -/
lemma N_S_right_endpoint {S : ℝ} (hS : 1 < S) :
    N_S S (1 + eps_S S) = A_S S := by
  unfold N_S
  exact A_S_intervalIntegral_def hS

/-- `g_S` at the left layer boundary equals `0`. -/
lemma g_S_at_left_layer_boundary (hS : 1 < S) :
    g_S S (1 - eps_S S) = 0 := by
  -- `|1 - ε| = 1 - ε ≤ 1 - ε`.
  unfold g_S
  have hle : |1 - eps_S S| ≤ 1 - eps_S S := by
    have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
    have h_nonneg : 0 ≤ 1 - eps_S S := by linarith
    rw [abs_of_nonneg h_nonneg]
  classical
  rw [if_pos hle]

/-- `g_S` at the negative left boundary equals `0`. -/
lemma g_S_at_neg_left_layer_boundary (hS : 1 < S) :
    g_S S (-(1 - eps_S S)) = 0 := by
  unfold g_S
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  have h_nonneg : 0 ≤ 1 - eps_S S := by linarith
  have hle : |-(1 - eps_S S)| ≤ 1 - eps_S S := by
    rw [abs_neg, abs_of_nonneg h_nonneg]
  classical
  rw [if_pos hle]

/-- `g_S` at the right layer boundary equals `1`. -/
lemma g_S_at_right_layer_boundary (hS : 1 < S) :
    g_S S (1 + eps_S S) = 1 := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  have heps : 0 < eps_S S := eps_S_pos hSpos
  have hpos : 0 ≤ 1 + eps_S S := by linarith
  have habs : |1 + eps_S S| = 1 + eps_S S := abs_of_nonneg hpos
  have h1 : ¬ |1 + eps_S S| ≤ 1 - eps_S S := by
    rw [habs]; linarith
  have h2 : ¬ |1 + eps_S S| < 1 + eps_S S := by
    rw [habs]; linarith
  classical
  rw [if_neg h1, if_neg h2]

/-- `g_S` at the negative right boundary equals `1`. -/
lemma g_S_at_neg_right_layer_boundary (hS : 1 < S) :
    g_S S (-(1 + eps_S S)) = 1 := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  have heps : 0 < eps_S S := eps_S_pos hSpos
  have hpos : 0 ≤ 1 + eps_S S := by linarith
  have habs : |-(1 + eps_S S)| = 1 + eps_S S := by
    rw [abs_neg, abs_of_nonneg hpos]
  have h1 : ¬ |-(1 + eps_S S)| ≤ 1 - eps_S S := by
    rw [habs]; linarith
  have h2 : ¬ |-(1 + eps_S S)| < 1 + eps_S S := by
    rw [habs]; linarith
  classical
  rw [if_neg h1, if_neg h2]

end EndpointAndRange

/-! ## Evenness -/

/-- `g_S` is even in `x`. -/
lemma g_S_even (S : ℝ) : Function.Even (g_S S) := by
  intro x
  unfold g_S
  simp [abs_neg]

/-! ## Denominator positivity -/

/-- `A_S` is positive for large `S`. -/
lemma denom_pos {S : ℝ} (hS : 1 < S) : 0 < A_S S := A_S_pos hS

/-- `Z_S` is positive for large `S`. -/
lemma Z_S_positive {S : ℝ} (hS : 1 < S) : 0 < Z_S S := Z_S_pos_TF hS

/-! ## Range bounds `0 ≤ g_S ≤ 1` -/

/-- `N_S` is nonneg on `[1-ε, ∞)` (since the integrand is positive). -/
lemma N_S_nonneg {S : ℝ} (hS : 0 < S) {r : ℝ}
    (hr : 1 - eps_S S ≤ r) :
    0 ≤ N_S S r := by
  unfold N_S
  apply intervalIntegral.integral_nonneg hr
  intro t _
  have h1 := phiDer2_S_pos hS t
  have h2 := Real.exp_pos (phi_S S t)
  exact le_of_lt (mul_pos h1 h2)

/-- For `r ≤ r'`, `N_S` is monotone. -/
lemma N_S_mono {S : ℝ} (hS : 0 < S) {r r' : ℝ}
    (hrr' : r ≤ r') :
    N_S S r ≤ N_S S r' := by
  unfold N_S
  -- Write `∫ (1-ε)..r'` = `∫ (1-ε)..r` + `∫ r..r'`.
  have h_add :
    (∫ t in (1 - eps_S S)..r, phiDer2_S S t * Real.exp (phi_S S t)) +
    (∫ t in r..r', phiDer2_S S t * Real.exp (phi_S S t))
    = ∫ t in (1 - eps_S S)..r', phiDer2_S S t * Real.exp (phi_S S t) := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact phi_integrand_intervalIntegrable hS _ _
    · exact phi_integrand_intervalIntegrable hS _ _
  have h_tail_nonneg :
      0 ≤ ∫ t in r..r', phiDer2_S S t * Real.exp (phi_S S t) := by
    apply intervalIntegral.integral_nonneg hrr'
    intro t _
    exact le_of_lt (mul_pos (phiDer2_S_pos hS t) (Real.exp_pos _))
  linarith

/-- Range bound: `0 ≤ g_S x`. -/
lemma g_S_nonneg {S : ℝ} (hS : 1 < S) (x : ℝ) : 0 ≤ g_S S x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  split_ifs with h1 h2
  · exact le_refl _
  · -- layer: N_S(|x|) / A_S ≥ 0
    push_neg at h1
    have hge : 1 - eps_S S ≤ |x| := le_of_lt h1
    have hN := N_S_nonneg hSpos hge
    exact div_nonneg hN (le_of_lt (A_S_pos hS))
  · exact zero_le_one

/-- Range bound: `g_S x ≤ 1`. -/
lemma g_S_le_one {S : ℝ} (hS : 1 < S) (x : ℝ) : g_S S x ≤ 1 := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  split_ifs with h1 h2
  · exact zero_le_one
  · -- layer: N_S(|x|) ≤ A_S since A_S = N_S(1+ε) and N_S is monotone.
    push_neg at h1
    have h_le : |x| ≤ 1 + eps_S S := le_of_lt h2
    have hmono := N_S_mono hSpos h_le
    have hrhs : N_S S (1 + eps_S S) ≤ A_S S := by
      rw [N_S_right_endpoint hS]
    have hfinal : N_S S |x| ≤ A_S S := le_trans hmono hrhs
    have hpos := A_S_pos hS
    rw [div_le_one hpos]
    exact hfinal
  · exact le_refl _

/-! ## A.e. derivative formulas

The derivative of `g_S` on the layers is the FTC consequence of `N_S`. We
state both as axioms because the full formal derivation requires
`intervalIntegral.integral_hasDerivAt_right` together with the chain rule for
absolute value, which lies in upstream measure-theoretic infrastructure. -/

/-- Derivative formula on the positive layer: for `x ∈ (1-ε, 1+ε)`,
`(g_S)'(x) = φ''_S(x) · exp(φ_S(x)) / A_S`.

Proof: on `layerPos S`, `g_S y = N_S S |y| / A_S` (definition).
Since `x > 0`, `|y| = y` in a neighborhood of `x`, so
`g_S = (N_S ∘ id) / A_S` near `x`. By FTC, `N_S` has derivative
`φ''_S · exp(φ_S)` at `x`; dividing by the constant `A_S` gives the
claim. -/
theorem hasDerivAt_g_S_layer_pos {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : x ∈ layerPos S) :
    HasDerivAt (g_S S)
      (phiDer2_S S x * Real.exp (phi_S S x) / A_S S) x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have heps_lt_one : eps_S S < 1 := eps_S_lt_one hS
  -- `x > 0` since `1-ε < x` and `0 < 1-ε`.
  have hx_pos : 0 < x := by
    have h1 : 1 - eps_S S < x := hx.1
    linarith
  have habs_x : |x| = x := abs_of_pos hx_pos
  -- Continuity of the integrand.
  have h_integrand_cont : Continuous
      (fun t => phiDer2_S S t * Real.exp (phi_S S t)) :=
    (phiDer2_S_continuous hSpos).mul
      (Real.continuous_exp.comp (phi_S_contDiff hSpos).continuous)
  -- FTC for `N_S`.
  have h_int_int : ∀ a b, IntervalIntegrable
                      (fun t => phiDer2_S S t * Real.exp (phi_S S t))
                      MeasureTheory.volume a b :=
    phi_integrand_intervalIntegrable hSpos
  have h_FTC : HasDerivAt (N_S S)
                (phiDer2_S S x * Real.exp (phi_S S x)) x := by
    show HasDerivAt
      (fun r => ∫ t in (1 - eps_S S)..r, phiDer2_S S t * Real.exp (phi_S S t))
      (phiDer2_S S x * Real.exp (phi_S S x)) x
    refine intervalIntegral.integral_hasDerivAt_right (h_int_int _ _) ?_ ?_
    · exact h_integrand_cont.stronglyMeasurable.stronglyMeasurableAtFilter
    · exact h_integrand_cont.continuousAt
  -- For y > 0, `|y| = y`, so `N_S ∘ |·| = N_S` near x.
  have h_abs_id_eq : (fun y : ℝ => |y|) =ᶠ[nhds x] (fun y => y) := by
    filter_upwards [Ioi_mem_nhds hx_pos] with y hy
    exact abs_of_pos hy
  have h_abs : HasDerivAt (fun y : ℝ => |y|) 1 x :=
    (hasDerivAt_id x).congr_of_eventuallyEq h_abs_id_eq
  -- Chain rule: `N_S ∘ |·|` has derivative `integrand(|x|) * 1 = integrand(x)` at x.
  have h_FTC_at_abs : HasDerivAt (N_S S)
                        (phiDer2_S S x * Real.exp (phi_S S x)) (|x|) := by
    rw [habs_x]; exact h_FTC
  have h_comp : HasDerivAt (fun y => N_S S |y|)
                  (phiDer2_S S x * Real.exp (phi_S S x) * 1) x :=
    h_FTC_at_abs.comp x h_abs
  -- Divide by A_S.
  have h_div : HasDerivAt (fun y => N_S S |y| / A_S S)
                  (phiDer2_S S x * Real.exp (phi_S S x) * 1 / A_S S) x :=
    h_comp.div_const _
  -- `g_S y = N_S(|y|) / A_S` for y in `layerPos S` (in particular near x).
  have h_layer_open : IsOpen (layerPos S) := isOpen_Ioo
  have h_nhd : layerPos S ∈ nhds x := h_layer_open.mem_nhds hx
  have h_g_eq : (g_S S) =ᶠ[nhds x] (fun y => N_S S |y| / A_S S) := by
    filter_upwards [h_nhd] with y hy
    exact g_S_layer_pos_eq hS hy
  -- Conclude via congruence.
  have h_final : HasDerivAt (g_S S)
                  (phiDer2_S S x * Real.exp (phi_S S x) * 1 / A_S S) x :=
    h_div.congr_of_eventuallyEq h_g_eq
  simpa using h_final

/-- Derivative formula on the negative layer: for `x ∈ (-1-ε, -1+ε)`,
`(g_S)'(x) = -φ''_S(x) · exp(φ_S(x)) / A_S`.

(The minus sign comes from `d|x|/dx = -1` on `(-∞, 0)`.) -/
theorem hasDerivAt_g_S_layer_neg {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : x ∈ layerNeg S) :
    HasDerivAt (g_S S)
      (-(phiDer2_S S x * Real.exp (phi_S S x)) / A_S S) x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have heps_lt_one : eps_S S < 1 := eps_S_lt_one hS
  -- `x < 0` since `x < -1 + ε < 0`.
  have hx_neg : x < 0 := by
    have h2 : x < -1 + eps_S S := hx.2
    linarith
  have habs_x : |x| = -x := abs_of_neg hx_neg
  have hnegx_pos : 0 < -x := neg_pos.mpr hx_neg
  -- Continuity of the integrand.
  have h_integrand_cont : Continuous
      (fun t => phiDer2_S S t * Real.exp (phi_S S t)) :=
    (phiDer2_S_continuous hSpos).mul
      (Real.continuous_exp.comp (phi_S_contDiff hSpos).continuous)
  -- FTC for `N_S` at `-x`.
  have h_int_int : ∀ a b, IntervalIntegrable
                      (fun t => phiDer2_S S t * Real.exp (phi_S S t))
                      MeasureTheory.volume a b :=
    phi_integrand_intervalIntegrable hSpos
  have h_FTC_at_negx : HasDerivAt (N_S S)
                (phiDer2_S S (-x) * Real.exp (phi_S S (-x))) (-x) := by
    show HasDerivAt
      (fun r => ∫ t in (1 - eps_S S)..r, phiDer2_S S t * Real.exp (phi_S S t))
      (phiDer2_S S (-x) * Real.exp (phi_S S (-x))) (-x)
    refine intervalIntegral.integral_hasDerivAt_right (h_int_int _ _) ?_ ?_
    · exact h_integrand_cont.stronglyMeasurable.stronglyMeasurableAtFilter
    · exact h_integrand_cont.continuousAt
  -- Use evenness to rewrite the values at `-x` as values at `x`.
  have h_phi_eq : phi_S S (-x) = phi_S S x := phi_S_even S x
  have h_phiDer2_eq : phiDer2_S S (-x) = phiDer2_S S x := phiDer2_S_even S x
  have h_FTC_at_negx' : HasDerivAt (N_S S)
                (phiDer2_S S x * Real.exp (phi_S S x)) (-x) := by
    rw [← h_phi_eq, ← h_phiDer2_eq]; exact h_FTC_at_negx
  -- For y < 0, `|y| = -y`, so `|·|` has derivative `-1` at x.
  have h_abs_neg_eq : (fun y : ℝ => |y|) =ᶠ[nhds x] (fun y => -y) := by
    filter_upwards [Iio_mem_nhds hx_neg] with y hy
    exact abs_of_neg hy
  have h_neg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have h_abs : HasDerivAt (fun y : ℝ => |y|) (-1) x :=
    h_neg.congr_of_eventuallyEq h_abs_neg_eq
  -- Chain rule: at `(|x|) = -x`, `N_S` has derivative `integrand(x)`,
  -- and `|·|` has derivative `-1` at `x`, so the composite has derivative
  -- `integrand(x) * (-1) = -integrand(x)`.
  have h_FTC_at_abs : HasDerivAt (N_S S)
                        (phiDer2_S S x * Real.exp (phi_S S x)) (|x|) := by
    rw [habs_x]; exact h_FTC_at_negx'
  have h_comp : HasDerivAt (fun y => N_S S |y|)
                  (phiDer2_S S x * Real.exp (phi_S S x) * (-1)) x :=
    h_FTC_at_abs.comp x h_abs
  -- Divide by A_S.
  have h_div : HasDerivAt (fun y => N_S S |y| / A_S S)
                  (phiDer2_S S x * Real.exp (phi_S S x) * (-1) / A_S S) x :=
    h_comp.div_const _
  -- `g_S y = N_S(|y|) / A_S` for y in `layerNeg S` (in particular near x).
  have h_layer_open : IsOpen (layerNeg S) := isOpen_Ioo
  have h_nhd : layerNeg S ∈ nhds x := h_layer_open.mem_nhds hx
  have h_g_eq : (g_S S) =ᶠ[nhds x] (fun y => N_S S |y| / A_S S) := by
    filter_upwards [h_nhd] with y hy
    exact g_S_layer_neg_eq hS hy
  -- Conclude via congruence.
  have h_final : HasDerivAt (g_S S)
                  (phiDer2_S S x * Real.exp (phi_S S x) * (-1) / A_S S) x :=
    h_div.congr_of_eventuallyEq h_g_eq
  -- Rearrange `a * (-1) / b = -(a) / b`.
  have h_rewrite : phiDer2_S S x * Real.exp (phi_S S x) * (-1) / A_S S
                 = -(phiDer2_S S x * Real.exp (phi_S S x)) / A_S S := by
    ring
  rw [← h_rewrite]; exact h_final

/-- On the open core `(-1+ε, 1-ε)`, `g_S` is locally constant, so
`(g_S)'(x) = 0`. -/
lemma hasDerivAt_g_S_core {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 + eps_S S) (1 - eps_S S)) :
    HasDerivAt (g_S S) 0 x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  -- On a neighbourhood of `x`, `g_S = 0`.
  have h_nbhd : ∀ᶠ y in nhds x, g_S S y = 0 := by
    rcases hx with ⟨hx1, hx2⟩
    have heps_pos : 0 < eps_S S := eps_S_pos hSpos
    -- choose radius r small enough so |y| stays in the core
    set r := min (x - (-1 + eps_S S)) ((1 - eps_S S) - x)
    have hr_pos : 0 < r := by
      apply lt_min
      · linarith
      · linarith
    have hball : Metric.ball x r ⊆ coreRegion S := by
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      refine ⟨?_, ?_⟩
      · have : x - r ≤ y := by
          have h_lb : x - r ≤ y := by
            have : -r < y - x := by
              have := abs_lt.mp hy
              linarith [this.1]
            linarith
          exact h_lb
        have hrle : r ≤ x - (-1 + eps_S S) := min_le_left _ _
        linarith
      · have hlt : y - x < r := (abs_lt.mp hy).2
        have hrle : r ≤ (1 - eps_S S) - x := min_le_right _ _
        linarith
    filter_upwards [Metric.ball_mem_nhds x hr_pos] with y hy
    exact g_S_core_eq_zero hSpos (hball hy)
  -- derivative of a function that is eventually 0 is 0.
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [h_nbhd] with y hy using hy)

/-- On the open exterior `(1+ε, ∞)` or `(-∞, -1-ε)`, `g_S` is locally `1`, so
`(g_S)'(x) = 0`. -/
lemma hasDerivAt_g_S_exterior {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : 1 + eps_S S < |x|) :
    HasDerivAt (g_S S) 0 x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  -- On a neighbourhood of `x`, `g_S = 1`.
  have h_nbhd : ∀ᶠ y in nhds x, g_S S y = 1 := by
    -- Either `x > 1+ε` or `x < -(1+ε)`.
    rcases lt_or_gt_of_ne
        (show x ≠ 0 from by
          intro hx0; rw [hx0, abs_zero] at hx; linarith) with hxneg | hxpos
    · -- x < 0, so |x| = -x > 1+ε means x < -(1+ε).
      have hxlt : x < -(1 + eps_S S) := by
        have := abs_of_neg hxneg
        rw [this] at hx; linarith
      set r := -(1 + eps_S S) - x
      have hr_pos : 0 < r := by linarith
      have h_sub : Metric.ball x r ⊆ exteriorRegion S := by
        intro y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hlt : y - x < r := (abs_lt.mp hy).2
        have hyneg : y < 0 := by linarith
        show 1 + eps_S S < |y|
        rw [abs_of_neg hyneg]; linarith
      filter_upwards [Metric.ball_mem_nhds x hr_pos] with y hy
      exact g_S_exterior_eq_one hSpos (h_sub hy)
    · -- x > 0, so x > 1+ε.
      have hxgt : 1 + eps_S S < x := by
        have := abs_of_pos hxpos
        rw [this] at hx; exact hx
      set r := x - (1 + eps_S S)
      have hr_pos : 0 < r := by linarith
      have h_sub : Metric.ball x r ⊆ exteriorRegion S := by
        intro y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hgt : -r < y - x := (abs_lt.mp hy).1
        have hypos : 0 < y := by linarith
        show 1 + eps_S S < |y|
        rw [abs_of_pos hypos]; linarith
      filter_upwards [Metric.ball_mem_nhds x hr_pos] with y hy
      exact g_S_exterior_eq_one hSpos (h_sub hy)
  exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [h_nbhd] with y hy using hy)

/-! ## Continuity of `g_S`

The function `g_S` is continuous on the whole real line.  The proof at the
core endpoints uses that `N_S(1-ε)/A_S = 0` and at the exterior endpoints
that `N_S(1+ε)/A_S = 1`. Continuity in the open regions follows from
each piece being continuous (constants, or the antiderivative of a
continuous function). The full local-piecewise glue via standard mathlib
lemmas is encapsulated by the following axiom; the elementary statement is
"piecewise functions agreeing at the boundaries of contiguous intervals are
continuous". -/

/-- `g_S` is continuous as a function of `x`. The proof glues two
nested `if-then-else` pieces via `Continuous.if_le`, using that:

* `N_S` is continuous (FTC for primitives of continuous functions);
* `|·|` is continuous;
* the boundary values match: `N_S(1−ε)/A_S = 0/A_S = 0` and
  `N_S(1+ε)/A_S = A_S/A_S = 1`. -/
theorem g_S_continuous {S : ℝ} (hS : 1 < S) : Continuous (g_S S) := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have hA_pos : 0 < A_S S := A_S_pos hS
  have hA_ne : A_S S ≠ 0 := hA_pos.ne'
  -- Step 1: `N_S` is continuous via FTC.
  have h_int_int : ∀ a b, IntervalIntegrable
                    (fun t => phiDer2_S S t * Real.exp (phi_S S t))
                    MeasureTheory.volume a b :=
    phi_integrand_intervalIntegrable hSpos
  have h_N_cont : Continuous (N_S S) := by
    show Continuous (fun r => ∫ t in (1 - eps_S S)..r,
                        phiDer2_S S t * Real.exp (phi_S S t))
    exact intervalIntegral.continuous_primitive h_int_int (1 - eps_S S)
  have h_abs_cont : Continuous (fun x : ℝ => |x|) := continuous_abs
  have h_N_abs_cont : Continuous (fun x : ℝ => N_S S |x|) :=
    h_N_cont.comp h_abs_cont
  have h_div_cont : Continuous (fun x : ℝ => N_S S |x| / A_S S) :=
    h_N_abs_cont.div_const _
  -- Step 2: the inner if-then-else is continuous.
  -- Convert `if |x| < 1+ε then ... else 1` to `if 1+ε ≤ |x| then 1 else ...`
  -- so we can apply `Continuous.if_le`.
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
    -- hx : 1 + eps_S S = |x|; show 1 = N_S |x| / A_S.
    rw [← hx]
    rw [N_S_right_endpoint hS]
    field_simp
  -- Step 3: the outer if-then-else is continuous.
  show Continuous (fun x : ℝ =>
      if |x| ≤ 1 - eps_S S then 0
      else if |x| < 1 + eps_S S then N_S S |x| / A_S S else 1)
  refine Continuous.if_le continuous_const h_inner_cont h_abs_cont
    continuous_const ?_
  intro x hx
  -- hx : |x| = 1 - eps_S S; show 0 = (inner expression).
  -- Since 1 - eps < 1 + eps, the inner branch is N_S(|x|)/A_S = 0/A_S = 0.
  have h_lt : |x| < 1 + eps_S S := by linarith [hx, heps_pos]
  rw [if_pos h_lt, hx]
  rw [N_S_left_endpoint S]
  ring

/-! ## Concrete energy/deficit definitions for the constructed family

(Task #7.) We define the weighted Dirichlet energy, the variance, and the
deficit functional for the explicit derivative representative `g'_S` chosen
piecewise according to the formulas above. -/

/-- The piecewise derivative representative of `g_S`. -/
noncomputable def g_S' (S : ℝ) (x : ℝ) : ℝ :=
  open Classical in
  if x ∈ layerPos S then phiDer2_S S x * Real.exp (phi_S S x) / A_S S
  else if x ∈ layerNeg S then -(phiDer2_S S x * Real.exp (phi_S S x)) / A_S S
  else 0

lemma g_S'_layer_pos {S : ℝ} {x : ℝ} (hx : x ∈ layerPos S) :
    g_S' S x = phiDer2_S S x * Real.exp (phi_S S x) / A_S S := by
  classical
  unfold g_S'
  rw [if_pos hx]

lemma g_S'_layer_neg {S : ℝ} {x : ℝ}
    (hx : x ∈ layerNeg S) (hxnotpos : x ∉ layerPos S) :
    g_S' S x = -(phiDer2_S S x * Real.exp (phi_S S x)) / A_S S := by
  classical
  unfold g_S'
  rw [if_neg hxnotpos, if_pos hx]

lemma g_S'_layers_disjoint {S : ℝ} (hS : 1 < S) (x : ℝ) :
    ¬ (x ∈ layerPos S ∧ x ∈ layerNeg S) := by
  intro ⟨hpos, hneg⟩
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  rcases hpos with ⟨h1, _⟩
  rcases hneg with ⟨_, h2⟩
  -- 1 - ε < x < -1 + ε is impossible because 1 - ε > -1 + ε.
  linarith

lemma g_S'_off_layers {S : ℝ} {x : ℝ}
    (hxnotpos : x ∉ layerPos S) (hxnotneg : x ∉ layerNeg S) :
    g_S' S x = 0 := by
  classical
  unfold g_S'
  rw [if_neg hxnotpos, if_neg hxnotneg]

/-- The Brascamp--Lieb energy of an integrand with respect to `ρ_φ`,
specialised to our piecewise derivative representative. -/
noncomputable def E_phi (S : ℝ) (f' : ℝ → ℝ) : ℝ :=
  ∫ x, (f' x)^2 / phiDer2_S S x ∂(rho_S S)

/-- The variance of a real-valued function under `ρ_S`. -/
noncomputable def Var_phi (S : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x, (f x)^2 ∂(rho_S S)) - (∫ x, f x ∂(rho_S S))^2

/-- The deficit `δ_φ(f) = E_φ(f') - Var ρ_φ f`. -/
noncomputable def delta_phi (S : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) : ℝ :=
  E_phi S f' - Var_phi S f

/-! ## Layer energy identity (task #9)

We record the direct identity
  `∫_{I_S^+} (g'_S)^2 / φ''_S · exp(-φ_S) = 1 / A_S`,
its analogue on `I_S^-`, and the corollary
  `E_{φ_S}(g_S) = 2 / (Z_S · A_S)`.

These integrals are over the unweighted Lebesgue measure; the factor
`exp(-φ_S)` in the integrand encodes the density of `ρ_S` (up to the
normalising constant `Z_S`).
-/

/-- The Lebesgue layer energy on `I_S^+`. -/
noncomputable def layerLebesgueEnergyPos (S : ℝ) : ℝ :=
  ∫ x in layerPos S, (g_S' S x)^2 / phiDer2_S S x * Real.exp (-(phi_S S x))

/-- The Lebesgue layer energy on `I_S^-`. -/
noncomputable def layerLebesgueEnergyNeg (S : ℝ) : ℝ :=
  ∫ x in layerNeg S, (g_S' S x)^2 / phiDer2_S S x * Real.exp (-(phi_S S x))

/-- **Layer energy identity** on `I_S^+`. The integrand on `I_S^+` simplifies
because `(g'_S)^2 = (φ''_S · exp(φ_S))^2 / A_S^2`, hence
`(g'_S)^2 / φ''_S · exp(-φ_S) = φ''_S · exp(φ_S) / A_S^2`, whose integral
over `I_S^+` is `A_S / A_S^2 = 1 / A_S`. -/
theorem layerLebesgueEnergyPos_eq {S : ℝ} (hS : 1 < S) :
    layerLebesgueEnergyPos S = 1 / A_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have hε_pos : 0 < eps_S S := eps_S_pos hSpos
  have hA_pos : 0 < A_S S := A_S_pos hS
  have hA_ne : A_S S ≠ 0 := hA_pos.ne'
  have h_le : 1 - eps_S S ≤ 1 + eps_S S := by linarith
  -- Pointwise simplification of the integrand on `layerPos S`.
  have h_simp : ∀ x ∈ layerPos S,
      (g_S' S x)^2 / phiDer2_S S x * Real.exp (-(phi_S S x))
        = phiDer2_S S x * Real.exp (phi_S S x) / (A_S S)^2 := by
    intro x hx
    have hphi_pos : 0 < phiDer2_S S x := phiDer2_S_pos hSpos x
    have hphi_ne : phiDer2_S S x ≠ 0 := hphi_pos.ne'
    have hexp_ne : Real.exp (phi_S S x) ≠ 0 := (Real.exp_pos _).ne'
    rw [g_S'_layer_pos hx, Real.exp_neg]
    field_simp
  -- Apply congruence on the integral.
  unfold layerLebesgueEnergyPos
  rw [show layerPos S = Set.Ioo (1 - eps_S S) (1 + eps_S S) from rfl]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h_simp]
  -- Pull out the constant denominator `(A_S)^2`.
  rw [MeasureTheory.integral_div]
  -- The set integral over Ioo equals A_S.
  have h_set_to_int :
      ∫ x in Set.Ioo (1 - eps_S S) (1 + eps_S S),
          phiDer2_S S x * Real.exp (phi_S S x) = A_S S := by
    show ∫ x in Set.Ioo (1 - eps_S S) (1 + eps_S S),
            phiDer2_S S x * Real.exp (phi_S S x) =
          ∫ x in (1 - eps_S S)..(1 + eps_S S),
            phiDer2_S S x * Real.exp (phi_S S x)
    rw [intervalIntegral.integral_of_le h_le]
    exact MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [h_set_to_int]
  rw [pow_two]
  field_simp

/-- Analogous identity on `I_S^-` using the symmetry of `φ_S`, `φ''_S`. -/
theorem layerLebesgueEnergyNeg_eq {S : ℝ} (hS : 1 < S) :
    layerLebesgueEnergyNeg S = 1 / A_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have hε_pos : 0 < eps_S S := eps_S_pos hSpos
  have hA_pos : 0 < A_S S := A_S_pos hS
  have hA_ne : A_S S ≠ 0 := hA_pos.ne'
  -- On `layerNeg S` we have `g_S' x = -(phiDer2_S x * exp(phi_S x)) / A_S`,
  -- and squaring kills the sign, so the integrand has the same form as on
  -- `layerPos`. Reduce to the previous theorem via `A_S_symm`.
  have h_simp : ∀ x ∈ layerNeg S,
      (g_S' S x)^2 / phiDer2_S S x * Real.exp (-(phi_S S x))
        = phiDer2_S S x * Real.exp (phi_S S x) / (A_S S)^2 := by
    intro x hx
    have hphi_pos : 0 < phiDer2_S S x := phiDer2_S_pos hSpos x
    have hphi_ne : phiDer2_S S x ≠ 0 := hphi_pos.ne'
    have hexp_ne : Real.exp (phi_S S x) ≠ 0 := (Real.exp_pos _).ne'
    -- `x` is not in `layerPos` since the layers are disjoint.
    have hxnotpos : x ∉ layerPos S := by
      intro hxpos
      exact g_S'_layers_disjoint hS x ⟨hxpos, hx⟩
    rw [g_S'_layer_neg hx hxnotpos, Real.exp_neg]
    field_simp
  unfold layerLebesgueEnergyNeg
  rw [show layerNeg S = Set.Ioo (-1 - eps_S S) (-1 + eps_S S) from rfl]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h_simp]
  rw [MeasureTheory.integral_div]
  -- The set integral over `Ioo (-1-ε) (-1+ε)` equals `A_S` by `A_S_symm`.
  rw [A_S_symm hS]
  rw [pow_two]
  field_simp

/-- **Energy identity.** The Brascamp--Lieb energy of `g_S` (with the
specified derivative representative) equals `2 / (Z_S · A_S)`.

Proof outline: rewrite the `ρ_S` integral as a Lebesgue integral with
density factor `(Z_S)⁻¹·exp(-φ_S)` (via `withDensity`), pull the constant
out, and observe that the integrand vanishes outside `layerPos ∪ layerNeg`.
The split over the disjoint layers reduces to
`layerLebesgueEnergyPos + layerLebesgueEnergyNeg = 2/A_S`. -/
theorem E_phi_g_S_eq {S : ℝ} (hS : 1 < S) :
    E_phi S (g_S' S) = 2 / (Z_S S * A_S S) := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have hZ_pos : 0 < Z_S S := Z_S_pos_TF hS
  have hZ_ne : Z_S S ≠ 0 := hZ_pos.ne'
  have hA_pos : 0 < A_S S := A_S_pos hS
  have hA_ne : A_S S ≠ 0 := hA_pos.ne'
  have hε_pos : 0 < eps_S S := eps_S_pos hSpos
  -- Step 1: rewrite the `ρ_S` integral via `withDensity`.
  unfold E_phi rho_S
  have h_meas_density : Measurable fun x =>
        ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine measurable_const.mul ?_
    exact Real.measurable_exp.comp (phi_S_measurable hSpos).neg
  have h_lt_top : ∀ᵐ x ∂(volume : Measure ℝ),
        ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul h_meas_density h_lt_top]
  -- Define the Lebesgue integrand `h`.
  set h := fun x => (g_S' S x)^2 / phiDer2_S S x * Real.exp (-(phi_S S x))
    with h_def
  -- Step 2: simplify the integrand and pull `(Z_S)⁻¹` out.
  have h_pointwise : ∀ x,
      (ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x)))).toReal •
        ((g_S' S x)^2 / phiDer2_S S x)
      = (Z_S S)⁻¹ * h x := by
    intro x
    have h_nn : 0 ≤ (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) :=
      mul_nonneg (inv_nonneg.mpr hZ_pos.le) (Real.exp_pos _).le
    rw [smul_eq_mul, ENNReal.toReal_ofReal h_nn]
    show (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) * ((g_S' S x)^2 / phiDer2_S S x) =
         (Z_S S)⁻¹ * h x
    simp only [h_def]; ring
  rw [show (fun x => (ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x)))).toReal •
            ((g_S' S x)^2 / phiDer2_S S x))
        = (fun x => (Z_S S)⁻¹ * h x) from funext h_pointwise]
  rw [MeasureTheory.integral_const_mul]
  -- Step 3: show that `∫ h ∂volume = 2/A_S`.
  -- 3.1: `h` vanishes off `layerPos ∪ layerNeg`.
  have h_off : ∀ x, x ∉ layerPos S ∪ layerNeg S → h x = 0 := by
    intro x hx
    rw [Set.mem_union, not_or] at hx
    simp [h_def, g_S'_off_layers hx.1 hx.2]
  -- 3.2: closed-form rewrite of `h` on each layer.
  have h_simp_pos : ∀ x ∈ layerPos S,
      h x = phiDer2_S S x * Real.exp (phi_S S x) / (A_S S)^2 := by
    intro x hx
    have hphi_ne : phiDer2_S S x ≠ 0 := (phiDer2_S_pos hSpos x).ne'
    have hexp_ne : Real.exp (phi_S S x) ≠ 0 := (Real.exp_pos _).ne'
    simp only [h_def]
    rw [g_S'_layer_pos hx, Real.exp_neg]
    field_simp
  have h_simp_neg : ∀ x ∈ layerNeg S,
      h x = phiDer2_S S x * Real.exp (phi_S S x) / (A_S S)^2 := by
    intro x hx
    have hphi_ne : phiDer2_S S x ≠ 0 := (phiDer2_S_pos hSpos x).ne'
    have hexp_ne : Real.exp (phi_S S x) ≠ 0 := (Real.exp_pos _).ne'
    have hxnotpos : x ∉ layerPos S := fun hxpos =>
      g_S'_layers_disjoint hS x ⟨hxpos, hx⟩
    simp only [h_def]
    rw [g_S'_layer_neg hx hxnotpos, Real.exp_neg]
    field_simp
  -- 3.3: integrability of the closed form on Icc, hence on each layer.
  have h_form_cont : Continuous
      (fun x => phiDer2_S S x * Real.exp (phi_S S x) / (A_S S)^2) :=
    ((phiDer2_S_continuous hSpos).mul
      (Real.continuous_exp.comp (phi_S_contDiff hSpos).continuous)).div_const _
  have h_form_int_pos : IntegrableOn
      (fun x => phiDer2_S S x * Real.exp (phi_S S x) / (A_S S)^2)
      (layerPos S) :=
    (h_form_cont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have h_form_int_neg : IntegrableOn
      (fun x => phiDer2_S S x * Real.exp (phi_S S x) / (A_S S)^2)
      (layerNeg S) :=
    (h_form_cont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  -- Transfer to `h` via `IntegrableOn.congr_fun`.
  have h_int_h_pos : IntegrableOn h (layerPos S) :=
    (h_form_int_pos.congr_fun (fun x hx => (h_simp_pos x hx).symm)
      measurableSet_Ioo)
  have h_int_h_neg : IntegrableOn h (layerNeg S) :=
    (h_form_int_neg.congr_fun (fun x hx => (h_simp_neg x hx).symm)
      measurableSet_Ioo)
  -- 3.4: split `∫ h` over `layerPos ∪ layerNeg` and the complement.
  -- Since `h = 0` off the union, ∫ over the complement is 0; and
  -- the union splits via disjointness.
  have h_disj : Disjoint (layerPos S) (layerNeg S) := by
    rw [Set.disjoint_iff_inter_eq_empty]; ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hp hn => g_S'_layers_disjoint hS x ⟨hp, hn⟩
  have h_meas_pos : MeasurableSet (layerPos S) := measurableSet_Ioo
  have h_meas_neg : MeasurableSet (layerNeg S) := measurableSet_Ioo
  have h_meas_union : MeasurableSet (layerPos S ∪ layerNeg S) :=
    h_meas_pos.union h_meas_neg
  have h_int_h_union : IntegrableOn h (layerPos S ∪ layerNeg S) :=
    h_int_h_pos.union h_int_h_neg
  -- `h` is integrable on `ℝ`: it equals its restriction to the
  -- bounded set, and the integrand on the complement is 0.
  have h_h_integrable : Integrable h := by
    -- h equals the indicator of (layerPos ∪ layerNeg) applied to itself;
    -- the indicator is integrable iff the restriction is.
    have h_eq_indic : h = (layerPos S ∪ layerNeg S).indicator h := by
      funext x
      by_cases hx : x ∈ layerPos S ∪ layerNeg S
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, h_off x hx]
    rw [h_eq_indic]
    exact (integrable_indicator_iff h_meas_union).mpr h_int_h_union
  have h_split : ∫ x, h x = (∫ x in layerPos S, h x) + (∫ x in layerNeg S, h x) := by
    have h1 : ∫ x, h x = ∫ x in layerPos S ∪ layerNeg S, h x := by
      rw [← integral_add_compl h_meas_union h_h_integrable]
      have h_compl_zero : ∫ x in (layerPos S ∪ layerNeg S)ᶜ, h x = 0 := by
        apply integral_eq_zero_of_ae
        refine (ae_restrict_iff' h_meas_union.compl).mpr ?_
        exact Filter.Eventually.of_forall (fun x hx => h_off x hx)
      rw [h_compl_zero, add_zero]
    rw [h1]
    exact setIntegral_union h_disj h_meas_neg h_int_h_pos h_int_h_neg
  -- Reduce each set integral via the closed-form rewrite.
  have h_int_pos_eq : (∫ x in layerPos S, h x) = layerLebesgueEnergyPos S := rfl
  have h_int_neg_eq : (∫ x in layerNeg S, h x) = layerLebesgueEnergyNeg S := rfl
  rw [h_split, h_int_pos_eq, h_int_neg_eq,
      layerLebesgueEnergyPos_eq hS, layerLebesgueEnergyNeg_eq hS]
  -- Final algebra: (Z_S)⁻¹ * (1/A_S + 1/A_S) = 2/(Z_S * A_S).
  field_simp
  ring

/-- Sum of the two layer Lebesgue energies equals `2 / A_S`. -/
lemma layer_lebesgue_energy_sum {S : ℝ} (hS : 1 < S) :
    layerLebesgueEnergyPos S + layerLebesgueEnergyNeg S = 2 / A_S S := by
  rw [layerLebesgueEnergyPos_eq hS, layerLebesgueEnergyNeg_eq hS]
  ring

/-- **Asymptotic form of the energy.** Using `A_S = S + O(S^{-1})` and the
expansion of `Z_S` from `Normalization`, we record
`E_{φ_S}(g_S) ∼ 2/(Z_S · S) · (1 + O(S^{-2}))`. We state this in the
finitary form: the difference between `E_phi · Z_S · A_S` and `2` is `0`. -/
lemma E_phi_g_S_mul {S : ℝ} (hS : 1 < S) :
    E_phi S (g_S' S) * (Z_S S * A_S S) = 2 := by
  rw [E_phi_g_S_eq hS]
  have hZ : Z_S S ≠ 0 := (Z_S_pos_TF hS).ne'
  have hA : A_S S ≠ 0 := (A_S_pos hS).ne'
  field_simp

/-! ## Variance computation (task #10)

We record the three target identities in finitary form, with the
asymptotic remainder `O(S^{-3})` packaged as the upstream axiom
`q_S_asymp` and `t_S_asymp`. -/

/-- `|q_S S| ≤ 2` for `S > 1`. Follows from `q_S = 2·tailInt_S/Z_S` with
`tailInt_S ≤ Z_S` (the tail integral of a nonneg function is at most
the full integral). The blueprint actually has `q_S ≤ 1` via the
left/right symmetry of `exp(-φ_S)`, but the looser `|q_S| ≤ 2` suffices
for the variance bound below. -/
theorem q_S_abs_le_two {S : ℝ} (hS_large : 1 < S) : |q_S S| ≤ 2 := by
  have hS : 0 < S := lt_trans zero_lt_one hS_large
  have hZ_pos : 0 < Z_S S := Z_S_pos S hS
  have h_int : Integrable (fun x => Real.exp (-(phi_S S x))) :=
    exp_negPhiS_integrable S hS
  have h_nn : 0 ≤ᵐ[volume] fun x => Real.exp (-(phi_S S x)) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  -- `tailInt_S ≤ Z_S` because the tail integral is a set integral of
  -- a nonneg function.
  have h_tail_le : tailInt_S S ≤ Z_S S :=
    setIntegral_le_integral h_int h_nn
  -- `q_S = 2·tailInt_S / Z_S ≥ 0` and ≤ 2·Z_S/Z_S = 2.
  have hq_nn : 0 ≤ q_S S := q_S_nonneg S hS
  have hq_ub : q_S S ≤ 2 := by
    show 2 * tailInt_S S / Z_S S ≤ 2
    rw [div_le_iff₀ hZ_pos]
    linarith
  rw [abs_of_nonneg hq_nn]
  exact hq_ub

/-- `t_S S ≤ 1` for `S > 1`. Derived from `∫_{T_S} exp(−φ) ≤ ∫_ℝ exp(−φ)
  = Z_S`. -/
theorem t_S_le_one {S : ℝ} (hS_large : 1 < S) : t_S S ≤ 1 := by
  have hS : 0 < S := lt_trans zero_lt_one hS_large
  have hZ_pos : 0 < Z_S S := Z_S_pos S hS
  have h_int : Integrable (fun x => Real.exp (-(phi_S S x))) :=
    exp_negPhiS_integrable S hS
  have h_nn : 0 ≤ᵐ[volume] fun x => Real.exp (-(phi_S S x)) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have h_le : ∫ x in T_S S, Real.exp (-(phi_S S x)) ≤ Z_S S :=
    setIntegral_le_integral h_int h_nn
  have h_div : (∫ x in T_S S, Real.exp (-(phi_S S x))) / Z_S S ≤ Z_S S / Z_S S :=
    div_le_div_of_nonneg_right h_le hZ_pos.le |>.trans_eq (by rfl)
  have h_one : Z_S S / Z_S S = 1 := div_self hZ_pos.ne'
  show t_S S ≤ 1
  unfold t_S
  rw [← h_one]
  exact div_le_div_of_nonneg_right h_le hZ_pos.le

/-- `t_S S ≥ 0` for `S` large; derived from `Normalization.t_S_nonneg`. -/
theorem t_S_nonneg_axiom {S : ℝ} (hS : 1 < S) : 0 ≤ t_S S :=
  t_S_nonneg S (lt_trans zero_lt_one hS)

/-- Helper: integral against `ρ_S` rewritten as a Lebesgue integral with
the density factor `(Z_S)⁻¹·exp(-φ_S)`. -/
private lemma integral_rho_S_eq {S : ℝ} (hS : 1 < S) (f : ℝ → ℝ) :
    ∫ x, f x ∂(rho_S S)
      = ∫ x, ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) * f x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have hZ_pos : 0 < Z_S S := Z_S_pos_TF hS
  unfold rho_S
  have h_meas_density : Measurable fun x =>
        ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine measurable_const.mul ?_
    exact Real.measurable_exp.comp (phi_S_measurable hSpos).neg
  have h_lt_top : ∀ᵐ x ∂(volume : Measure ℝ),
        ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul h_meas_density h_lt_top]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h_nn : 0 ≤ (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) :=
    mul_nonneg (inv_nonneg.mpr hZ_pos.le) (Real.exp_pos _).le
  show (ENNReal.ofReal ((Z_S S)⁻¹ * Real.exp (-(phi_S S x)))).toReal • f x
       = (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) * f x
  rw [smul_eq_mul, ENNReal.toReal_ofReal h_nn]

/-- Helper (set version): set integral against `ρ_S` rewritten as a
Lebesgue set integral with density factor `(Z_S)⁻¹·exp(-φ_S)`. -/
private lemma setIntegral_rho_S_eq {S : ℝ} (hS : 1 < S) (s : Set ℝ)
    (hs : MeasurableSet s) (f : ℝ → ℝ) :
    ∫ x in s, f x ∂(rho_S S)
      = ∫ x in s, ((Z_S S)⁻¹ * Real.exp (-(phi_S S x))) * f x := by
  rw [(integral_indicator hs).symm, integral_rho_S_eq hS,
      ← integral_indicator hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- Helper: `ρ_S` measure of a measurable set equals
`(1/Z_S) · ∫_s exp(-φ_S)`. -/
private lemma rho_S_set_eq {S : ℝ} (hS : 1 < S) (s : Set ℝ)
    (hs : MeasurableSet s) :
    ∫ _ in s, (1 : ℝ) ∂(rho_S S)
      = (Z_S S)⁻¹ * ∫ x in s, Real.exp (-(phi_S S x)) := by
  rw [setIntegral_rho_S_eq hS s hs]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x; ring

/-- Helper: `g_S` evaluates to `1` whenever `1+ε_S ≤ |x|` (including
the boundary case, which is *not* covered by `g_S_exterior_eq_one`). -/
lemma g_S_eq_one_of_ge {S : ℝ} (hS : 0 < S) {x : ℝ}
    (hx : 1 + eps_S S ≤ |x|) : g_S S x = 1 := by
  unfold g_S
  have h1 : ¬ |x| ≤ 1 - eps_S S := by
    intro hle
    have : (1 + eps_S S) ≤ 1 - eps_S S := le_trans hx hle
    linarith [eps_S_pos hS]
  have h2 : ¬ |x| < 1 + eps_S S := not_lt.mpr hx
  classical
  rw [if_neg h1, if_neg h2]

/-- Helper: symmetry of the right tail integral via `phi_S_even` and
`integral_comp_neg_Iic`. -/
private lemma integral_left_tail_eq_tailInt {S : ℝ} (hS : 0 < S) :
    ∫ x in Set.Iic (-(1 + eps_S S)), Real.exp (-(phi_S S x))
      = tailInt_S S := by
  -- Step 1: rewrite using phi_S_even: exp(-phi(x)) = exp(-phi(-x)).
  have h_eq : ∀ x, Real.exp (-(phi_S S x)) = Real.exp (-(phi_S S (-x))) := by
    intro x; rw [phi_S_even]
  rw [show (fun x => Real.exp (-(phi_S S x))) =
        (fun x => (fun t => Real.exp (-(phi_S S t))) (-x)) from by
        funext x; exact h_eq x]
  -- Step 2: apply integral_comp_neg_Iic.
  rw [integral_comp_neg_Iic (-(1 + eps_S S))
        (fun t => Real.exp (-(phi_S S t)))]
  -- Step 3: simplify -(-c) = c and convert Ioi to Ici (null set).
  show ∫ x in Set.Ioi (-(-(1 + eps_S S))), Real.exp (-(phi_S S x))
       = tailInt_S S
  rw [neg_neg]
  unfold tailInt_S
  exact (integral_Ici_eq_integral_Ioi).symm

/-- Helper: ρ_S-measure of the closed exterior `E = {|x| ≥ 1+ε}` equals
`q_S`. -/
private lemma rho_S_exterior_eq_q_S {S : ℝ} (hS : 1 < S) :
    ∫ _ in {x : ℝ | 1 + eps_S S ≤ |x|}, (1 : ℝ) ∂(rho_S S) = q_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have hZ_pos : 0 < Z_S S := Z_S_pos_TF hS
  have hZ_ne : Z_S S ≠ 0 := hZ_pos.ne'
  have hε_pos : 0 < eps_S S := eps_S_pos hSpos
  set E := {x : ℝ | 1 + eps_S S ≤ |x|}
  have hE_meas : MeasurableSet E :=
    measurableSet_le measurable_const continuous_abs.measurable
  rw [rho_S_set_eq hS E hE_meas]
  -- E = Iic (-(1+ε)) ∪ Ici (1+ε) (disjoint).
  have hE_eq : E = Set.Iic (-(1 + eps_S S)) ∪ Set.Ici (1 + eps_S S) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, E]
    constructor
    · intro h
      rcases le_or_gt 0 x with hxnn | hxneg
      · right; rw [abs_of_nonneg hxnn] at h; exact h
      · left; rw [abs_of_neg hxneg] at h; linarith
    · rintro (h | h)
      · have hxnp : x ≤ 0 := by linarith
        rw [abs_of_nonpos hxnp]; linarith
      · have hxnn : (0 : ℝ) ≤ x := by linarith
        rw [abs_of_nonneg hxnn]; exact h
  have h_disj : Disjoint (Set.Iic (-(1 + eps_S S))) (Set.Ici (1 + eps_S S)) := by
    rw [Set.disjoint_iff_inter_eq_empty]; ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · intro h; exact h.elim
  have h_int_full : Integrable (fun x => Real.exp (-(phi_S S x))) :=
    exp_negPhiS_integrable S hSpos
  have h_int_left : IntegrableOn (fun x => Real.exp (-(phi_S S x)))
      (Set.Iic (-(1 + eps_S S))) := h_int_full.integrableOn
  have h_int_right : IntegrableOn (fun x => Real.exp (-(phi_S S x)))
      (Set.Ici (1 + eps_S S)) := h_int_full.integrableOn
  rw [hE_eq, setIntegral_union h_disj measurableSet_Ici h_int_left h_int_right]
  rw [integral_left_tail_eq_tailInt hSpos]
  -- ∫_{Ici (1+ε)} exp(-phi) = tailInt_S by definition.
  show (Z_S S)⁻¹ * (tailInt_S S + tailInt_S S) = 2 * tailInt_S S / Z_S S
  field_simp; ring

/-- The integral of `g_S` against `ρ_S` decomposed via the partition
`{|x| ≤ 1-ε} ∪ ((1-ε, 1+ε) ∪ (-1-ε, -1+ε)) ∪ {|x| ≥ 1+ε}`:
the core contributes `0`, the layers contribute the remainder `R`,
and the exterior contributes `q_S` (by symmetry). -/
theorem integral_g_S_eq_q_plus_error {S : ℝ} (hS : 1 < S) :
    ∃ R : ℝ, |R| ≤ t_S S ∧ ∫ x, g_S S x ∂(rho_S S) = q_S S + R := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have hZ_pos : 0 < Z_S S := Z_S_pos_TF hS
  have hZ_ne : Z_S S ≠ 0 := hZ_pos.ne'
  have hε_pos : 0 < eps_S S := eps_S_pos hSpos
  have hε_lt : eps_S S < 1 := eps_S_lt_one hS
  -- Setup: closed exterior E, transition T, and density d.
  set E := {x : ℝ | 1 + eps_S S ≤ |x|} with hE_def
  set T := transitionRegion S with hT_def
  set d : ℝ → ℝ := fun x => (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) with hd_def
  have hE_meas : MeasurableSet E :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hT_meas : MeasurableSet T :=
    measurableSet_Ioo.union measurableSet_Ioo
  have hd_nn : ∀ x, 0 ≤ d x := fun x =>
    mul_nonneg (inv_nonneg.mpr hZ_pos.le) (Real.exp_pos _).le
  have hd_int : Integrable d :=
    (exp_negPhiS_integrable S hSpos).const_mul _
  have hg_cont : Continuous (g_S S) := g_S_continuous hS
  have hg_meas : Measurable (g_S S) := hg_cont.measurable
  have hg_nn : ∀ x, 0 ≤ g_S S x := g_S_nonneg hS
  have hg_le_one : ∀ x, g_S S x ≤ 1 := g_S_le_one hS
  -- The integrand `d * g_S` is integrable on volume.
  have hdg_meas : AEStronglyMeasurable (fun x => d x * g_S S x) volume :=
    hd_int.aestronglyMeasurable.mul hg_cont.aestronglyMeasurable
  have hdg_bound : ∀ x, ‖d x * g_S S x‖ ≤ ‖d x‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_of_nonneg (hg_nn x)]; exact hg_le_one x
  have hdg_int : Integrable (fun x => d x * g_S S x) :=
    hd_int.mono hdg_meas (Filter.Eventually.of_forall hdg_bound)
  -- Witness R = ∫_T g_S dρ_S.
  refine ⟨∫ x in T, g_S S x ∂(rho_S S), ?_, ?_⟩
  · -- Bound: |R| ≤ t_S.
    have hR_eq_vol : ∫ x in T, g_S S x ∂(rho_S S) = ∫ x in T, d x * g_S S x :=
      setIntegral_rho_S_eq hS T hT_meas (g_S S)
    rw [hR_eq_vol]
    have hR_nn : 0 ≤ ∫ x in T, d x * g_S S x := by
      apply setIntegral_nonneg hT_meas
      intro x _
      exact mul_nonneg (hd_nn x) (hg_nn x)
    rw [abs_of_nonneg hR_nn]
    -- Step 1: ∫_T d * g_S ≤ ∫_T d * 1 = ∫_T d.
    have h1 : ∫ x in T, d x * g_S S x ≤ ∫ x in T, d x := by
      have h_mono : ∫ x in T, d x * g_S S x ≤ ∫ x in T, d x * 1 :=
        setIntegral_mono_on hdg_int.integrableOn
          (by simpa using hd_int.integrableOn) hT_meas (fun x _ => by
            have hd_x_nn : 0 ≤ d x := hd_nn x
            nlinarith [hg_nn x, hg_le_one x])
      simpa using h_mono
    -- Step 2: ∫_T d ≤ ∫_{T_S} d  (since T ⊆ T_S).
    have hT_sub : T ⊆ T_S S := by
      intro x hx
      rcases hx with hx_pos | hx_neg
      · right
        rcases hx_pos with ⟨hx1, hx2⟩
        exact ⟨le_of_lt hx1, le_of_lt hx2⟩
      · left
        rcases hx_neg with ⟨hx1, hx2⟩
        exact ⟨le_of_lt hx1, le_of_lt hx2⟩
    have h2 : ∫ x in T, d x ≤ ∫ x in T_S S, d x := by
      apply setIntegral_mono_set hd_int.integrableOn
      · exact Filter.Eventually.of_forall fun x => hd_nn x
      · exact Filter.Eventually.of_forall hT_sub
    -- Step 3: ∫_{T_S} d = t_S.
    have h3 : ∫ x in T_S S, d x = t_S S := by
      simp only [d, hd_def]
      rw [MeasureTheory.integral_const_mul]
      unfold t_S
      ring
    linarith
  · -- Equality: ∫ g_S dρ = q_S + R.
    -- Convert LHS to volume integral.
    rw [integral_rho_S_eq hS (g_S S)]
    -- Convert R to volume.
    rw [setIntegral_rho_S_eq hS T hT_meas (g_S S)]
    -- Split ∫ d * g_S over T and Tᶜ.
    rw [← integral_add_compl hT_meas hdg_int]
    -- Reduce to: ∫_Tᶜ d * g_S = q_S.
    have h_compl_eq : ∫ x in Tᶜ, d x * g_S S x = q_S S := by
      -- On Tᶜ: g_S = E.indicator 1 (case analysis).
      -- So d * g_S = E.indicator d on Tᶜ.
      have h_eq_on_Tcompl : ∀ x ∈ Tᶜ,
          d x * g_S S x = E.indicator d x := by
        intro x hx
        rw [Set.mem_compl_iff] at hx
        -- x ∉ T = layerPos ∪ layerNeg
        have hx_outside : ¬ (1 - eps_S S < |x| ∧ |x| < 1 + eps_S S) := by
          intro ⟨h1, h2⟩
          apply hx
          rcases le_or_gt 0 x with hxnn | hxneg
          · left
            rw [abs_of_nonneg hxnn] at h1 h2
            exact ⟨h1, h2⟩
          · right
            rw [abs_of_neg hxneg] at h1 h2
            refine ⟨by linarith, by linarith⟩
        push_neg at hx_outside
        by_cases hxE : x ∈ E
        · -- x ∈ E: |x| ≥ 1+ε, so g_S = 1.
          rw [Set.indicator_of_mem hxE]
          rw [g_S_eq_one_of_ge hSpos hxE, mul_one]
        · -- x ∉ E: |x| < 1+ε. Combined with ¬(1-ε < |x| < 1+ε), so |x| ≤ 1-ε.
          have hxE' : ¬ (1 + eps_S S ≤ |x|) := hxE
          have hxabs_lt : |x| < 1 + eps_S S := lt_of_not_ge hxE'
          have hxcore : |x| ≤ 1 - eps_S S := by
            by_contra h
            push_neg at h
            exact absurd (hx_outside h) (not_le.mpr hxabs_lt)
          rw [Set.indicator_of_notMem hxE]
          rw [g_S_core_eq_zero hSpos ?_, mul_zero]
          -- coreRegion = Icc (-1+ε) (1-ε); from |x| ≤ 1-ε.
          refine ⟨?_, ?_⟩
          · have : -|x| ≤ x := neg_abs_le x
            linarith [abs_nonneg x]
          · exact le_trans (le_abs_self x) hxcore
      rw [setIntegral_congr_fun hT_meas.compl h_eq_on_Tcompl]
      -- ∫_Tᶜ E.indicator d = ∫_{Tᶜ ∩ E} d = ∫_E d (since E ⊆ Tᶜ).
      rw [setIntegral_indicator hE_meas]
      -- Now goal: ∫_{Tᶜ ∩ E} d = q_S.
      have hTcomplE : Tᶜ ∩ E = E := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, and_iff_right_iff_imp]
        intro hx_E
        have hx_E' : 1 + eps_S S ≤ |x| := hx_E
        intro hx_T
        rcases hx_T with hxL | hxL
        · rcases hxL with ⟨h1, h2⟩
          have hxpos : 0 < x := by linarith
          have habs : |x| < 1 + eps_S S := by rw [abs_of_pos hxpos]; exact h2
          linarith
        · rcases hxL with ⟨h1, h2⟩
          have hxneg : x < 0 := by linarith
          have habs : |x| < 1 + eps_S S := by rw [abs_of_neg hxneg]; linarith
          linarith
      rw [hTcomplE]
      -- ∫_E d = (1/Z_S) ∫_E exp(-phi)
      have h_unfold_d : ∫ x in E, d x = (Z_S S)⁻¹ * ∫ x in E, Real.exp (-(phi_S S x)) := by
        simp only [d, hd_def]
        rw [MeasureTheory.integral_const_mul]
      rw [h_unfold_d]
      -- Use rho_S_exterior_eq_q_S to get q_S, working backwards:
      -- rho_S_exterior_eq_q_S says ∫ _ in E, 1 ∂rho = q_S
      -- And ∫ _ in E, 1 ∂rho = (1/Z_S) ∫_E exp(-phi) by rho_S_set_eq.
      have h_set := rho_S_set_eq hS E hE_meas
      have h_rho_E := rho_S_exterior_eq_q_S hS
      rw [h_set] at h_rho_E
      exact h_rho_E
    rw [h_compl_eq]
    ring

/-- **Second moment of `g_S`**: `∫ g_S^2 ∂ρ_S = q_S + O(S^{-3})`.

Proof analogous to `integral_g_S_eq_q_plus_error` since `g_S² = g_S` on
core (where both equal `0`) and on exterior (where both equal `1`); on
the layers, `g_S² ∈ [0, 1]` so the same `t_S`-bound applies. -/
theorem integral_g_S_sq_eq_q_plus_error {S : ℝ} (hS : 1 < S) :
    ∃ R : ℝ, |R| ≤ t_S S ∧ ∫ x, (g_S S x)^2 ∂(rho_S S) = q_S S + R := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have hZ_pos : 0 < Z_S S := Z_S_pos_TF hS
  have hZ_ne : Z_S S ≠ 0 := hZ_pos.ne'
  have hε_pos : 0 < eps_S S := eps_S_pos hSpos
  have hε_lt : eps_S S < 1 := eps_S_lt_one hS
  -- Setup.
  set E := {x : ℝ | 1 + eps_S S ≤ |x|} with hE_def
  set T := transitionRegion S with hT_def
  set d : ℝ → ℝ := fun x => (Z_S S)⁻¹ * Real.exp (-(phi_S S x)) with hd_def
  have hE_meas : MeasurableSet E :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hT_meas : MeasurableSet T :=
    measurableSet_Ioo.union measurableSet_Ioo
  have hd_nn : ∀ x, 0 ≤ d x := fun x =>
    mul_nonneg (inv_nonneg.mpr hZ_pos.le) (Real.exp_pos _).le
  have hd_int : Integrable d :=
    (exp_negPhiS_integrable S hSpos).const_mul _
  have hg_cont : Continuous (g_S S) := g_S_continuous hS
  have hg_meas : Measurable (g_S S) := hg_cont.measurable
  have hg_nn : ∀ x, 0 ≤ g_S S x := g_S_nonneg hS
  have hg_le_one : ∀ x, g_S S x ≤ 1 := g_S_le_one hS
  have hg_sq_nn : ∀ x, 0 ≤ (g_S S x)^2 := fun x => sq_nonneg _
  have hg_sq_le_one : ∀ x, (g_S S x)^2 ≤ 1 := fun x => by
    have h := pow_le_pow_left₀ (hg_nn x) (hg_le_one x) 2
    simpa using h
  -- The integrand `d * g_S^2` is integrable on volume.
  have hgsq_cont : Continuous (fun x => (g_S S x)^2) := hg_cont.pow 2
  have hdg_meas : AEStronglyMeasurable (fun x => d x * (g_S S x)^2) volume :=
    hd_int.aestronglyMeasurable.mul hgsq_cont.aestronglyMeasurable
  have hdg_bound : ∀ x, ‖d x * (g_S S x)^2‖ ≤ ‖d x‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_of_nonneg (hg_sq_nn x)]; exact hg_sq_le_one x
  have hdg_int : Integrable (fun x => d x * (g_S S x)^2) :=
    hd_int.mono hdg_meas (Filter.Eventually.of_forall hdg_bound)
  -- Witness R = ∫_T g_S^2 dρ_S.
  refine ⟨∫ x in T, (g_S S x)^2 ∂(rho_S S), ?_, ?_⟩
  · -- Bound: |R| ≤ t_S.
    have hR_eq_vol : ∫ x in T, (g_S S x)^2 ∂(rho_S S)
                   = ∫ x in T, d x * (g_S S x)^2 :=
      setIntegral_rho_S_eq hS T hT_meas (fun x => (g_S S x)^2)
    rw [hR_eq_vol]
    have hR_nn : 0 ≤ ∫ x in T, d x * (g_S S x)^2 := by
      apply setIntegral_nonneg hT_meas
      intro x _
      exact mul_nonneg (hd_nn x) (hg_sq_nn x)
    rw [abs_of_nonneg hR_nn]
    have h1 : ∫ x in T, d x * (g_S S x)^2 ≤ ∫ x in T, d x := by
      have h_mono : ∫ x in T, d x * (g_S S x)^2 ≤ ∫ x in T, d x * 1 :=
        setIntegral_mono_on hdg_int.integrableOn
          (by simpa using hd_int.integrableOn) hT_meas (fun x _ => by
            have hd_x_nn : 0 ≤ d x := hd_nn x
            nlinarith [hg_sq_nn x, hg_sq_le_one x])
      simpa using h_mono
    have hT_sub : T ⊆ T_S S := by
      intro x hx
      rcases hx with hx_pos | hx_neg
      · right
        rcases hx_pos with ⟨hx1, hx2⟩
        exact ⟨le_of_lt hx1, le_of_lt hx2⟩
      · left
        rcases hx_neg with ⟨hx1, hx2⟩
        exact ⟨le_of_lt hx1, le_of_lt hx2⟩
    have h2 : ∫ x in T, d x ≤ ∫ x in T_S S, d x := by
      apply setIntegral_mono_set hd_int.integrableOn
      · exact Filter.Eventually.of_forall fun x => hd_nn x
      · exact Filter.Eventually.of_forall hT_sub
    have h3 : ∫ x in T_S S, d x = t_S S := by
      simp only [d, hd_def]
      rw [MeasureTheory.integral_const_mul]
      unfold t_S
      ring
    linarith
  · -- Equality: ∫ g_S^2 dρ = q_S + R.
    rw [integral_rho_S_eq hS (fun x => (g_S S x)^2)]
    rw [setIntegral_rho_S_eq hS T hT_meas (fun x => (g_S S x)^2)]
    rw [← integral_add_compl hT_meas hdg_int]
    have h_compl_eq : ∫ x in Tᶜ, d x * (g_S S x)^2 = q_S S := by
      have h_eq_on_Tcompl : ∀ x ∈ Tᶜ,
          d x * (g_S S x)^2 = E.indicator d x := by
        intro x hx
        rw [Set.mem_compl_iff] at hx
        have hx_outside : ¬ (1 - eps_S S < |x| ∧ |x| < 1 + eps_S S) := by
          intro ⟨h1, h2⟩
          apply hx
          rcases le_or_gt 0 x with hxnn | hxneg
          · left
            rw [abs_of_nonneg hxnn] at h1 h2
            exact ⟨h1, h2⟩
          · right
            rw [abs_of_neg hxneg] at h1 h2
            refine ⟨by linarith, by linarith⟩
        push_neg at hx_outside
        by_cases hxE : x ∈ E
        · -- x ∈ E: g_S = 1, so g_S^2 = 1.
          rw [Set.indicator_of_mem hxE]
          rw [g_S_eq_one_of_ge hSpos hxE]
          ring
        · -- x ∉ E: g_S = 0 on core.
          have hxE' : ¬ (1 + eps_S S ≤ |x|) := hxE
          have hxabs_lt : |x| < 1 + eps_S S := lt_of_not_ge hxE'
          have hxcore : |x| ≤ 1 - eps_S S := by
            by_contra h
            push_neg at h
            exact absurd (hx_outside h) (not_le.mpr hxabs_lt)
          rw [Set.indicator_of_notMem hxE]
          have hg_zero : g_S S x = 0 := g_S_core_eq_zero hSpos ⟨by
            have : -|x| ≤ x := neg_abs_le x; linarith [abs_nonneg x],
            le_trans (le_abs_self x) hxcore⟩
          rw [hg_zero]; ring
      rw [setIntegral_congr_fun hT_meas.compl h_eq_on_Tcompl]
      rw [setIntegral_indicator hE_meas]
      have hTcomplE : Tᶜ ∩ E = E := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, and_iff_right_iff_imp]
        intro hx_E
        have hx_E' : 1 + eps_S S ≤ |x| := hx_E
        intro hx_T
        rcases hx_T with hxL | hxL
        · rcases hxL with ⟨h1, h2⟩
          have hxpos : 0 < x := by linarith
          have habs : |x| < 1 + eps_S S := by rw [abs_of_pos hxpos]; exact h2
          linarith
        · rcases hxL with ⟨h1, h2⟩
          have hxneg : x < 0 := by linarith
          have habs : |x| < 1 + eps_S S := by rw [abs_of_neg hxneg]; linarith
          linarith
      rw [hTcomplE]
      have h_unfold_d : ∫ x in E, d x = (Z_S S)⁻¹ * ∫ x in E, Real.exp (-(phi_S S x)) := by
        simp only [d, hd_def]
        rw [MeasureTheory.integral_const_mul]
      rw [h_unfold_d]
      have h_set := rho_S_set_eq hS E hE_meas
      have h_rho_E := rho_S_exterior_eq_q_S hS
      rw [h_set] at h_rho_E
      exact h_rho_E
    rw [h_compl_eq]
    ring

/-- **Variance of `g_S`** equals `q_S(1-q_S) + O(S^{-3})`.

The remainder is bounded by `6 t_S S`: this combines `|q_S| ≤ 2`,
`|R₁| ≤ t_S`, `|R₂| ≤ t_S`, and `t_S ≤ 1`. (The blueprint's tighter
`|q_S| ≤ 1` would give the bound `4 t_S`, but the looser `|q_S| ≤ 2`
suffices for the `IsBigO` conclusion downstream.) -/
lemma Var_phi_g_S {S : ℝ} (hS : 1 < S) :
    ∃ R : ℝ, |R| ≤ 6 * t_S S ∧
      Var_phi S (g_S S) = q_S S * (1 - q_S S) + R := by
  obtain ⟨R₁, hR₁, hint₁⟩ := integral_g_S_eq_q_plus_error hS
  obtain ⟨R₂, hR₂, hint₂⟩ := integral_g_S_sq_eq_q_plus_error hS
  refine ⟨R₂ - 2 * q_S S * R₁ - R₁^2, ?_, ?_⟩
  · have hq_le_two : |q_S S| ≤ 2 := q_S_abs_le_two hS
    have ht_le_one : t_S S ≤ 1 := t_S_le_one hS
    have ht_nn : 0 ≤ t_S S := t_S_nonneg_axiom hS
    have hR1_abs : |R₁| ≤ t_S S := hR₁
    have hR2_abs : |R₂| ≤ t_S S := hR₂
    have hR1_nn : 0 ≤ |R₁| := abs_nonneg _
    have hR2_nn : 0 ≤ |R₂| := abs_nonneg _
    have hq_nn : 0 ≤ |q_S S| := abs_nonneg _
    -- Bound each term.
    have hT1 : |R₂| ≤ t_S S := hR2_abs
    have hT2 : |2 * q_S S * R₁| ≤ 4 * t_S S := by
      have heq : |2 * q_S S * R₁| = 2 * |q_S S| * |R₁| := by
        rw [show (2 : ℝ) * q_S S * R₁ = 2 * (q_S S * R₁) from by ring,
            abs_mul, abs_mul]
        rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
        ring
      rw [heq]
      nlinarith
    have hT3_abs : |R₁^2| ≤ t_S S := by
      rw [abs_of_nonneg (sq_nonneg _)]
      -- R₁² = R₁ * R₁, and |R₁ * R₁| = |R₁| * |R₁|, so
      -- R₁² ≤ |R₁| * |R₁| ≤ t_S · t_S ≤ t_S · 1 = t_S.
      have h_R1_le : |R₁| ≤ t_S S := hR1_abs
      have h_R1_nn : 0 ≤ |R₁| := abs_nonneg _
      have h_sq_abs : R₁ * R₁ ≤ |R₁| * |R₁| := by
        have h1 : R₁ ≤ |R₁| := le_abs_self _
        have h2 : -R₁ ≤ |R₁| := neg_le_abs _
        nlinarith
      have hR1_sq_eq : R₁^2 = R₁ * R₁ := by ring
      rw [hR1_sq_eq]
      nlinarith
    -- Now combine with triangle inequality.
    have h_step1 : |R₂ - 2 * q_S S * R₁| ≤ |R₂| + |2 * q_S S * R₁| :=
      abs_sub _ _
    have h_step2 :
        |R₂ - 2 * q_S S * R₁ - R₁^2| ≤ |R₂ - 2 * q_S S * R₁| + |R₁^2| :=
      abs_sub _ _
    linarith
  · rw [Var_phi, hint₁, hint₂]
    ring

/-- The variance and `q_S(1-q_S)` differ by `O(S^{-3})`. -/
lemma Var_phi_g_S_isBigO :
    (fun S : ℝ => Var_phi S (g_S S) - q_S S * (1 - q_S S))
      =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-3 : ℤ) := by
  -- Step 1: |Var − q(1−q)| ≤ 3 · t_S for S > 1.
  have hbound :
      ∀ᶠ S in Filter.atTop,
        ‖Var_phi S (g_S S) - q_S S * (1 - q_S S)‖ ≤ 6 * ‖t_S S‖ := by
    rw [Filter.eventually_atTop]
    refine ⟨2, fun S hS => ?_⟩
    have hS' : (1 : ℝ) < S := by linarith
    obtain ⟨R, hR, hVar⟩ := Var_phi_g_S hS'
    have hnn : 0 ≤ t_S S := t_S_nonneg_axiom hS'
    have hkey : Var_phi S (g_S S) - q_S S * (1 - q_S S) = R := by
      rw [hVar]; ring
    simp only [Real.norm_eq_abs]
    rw [hkey, abs_of_nonneg hnn]
    exact hR
  -- Step 2: combine with t_S = O(S^{-3}).
  exact (IsBigO.of_bound (6 : ℝ) hbound).trans t_S_isBigO

/-- Combining `Var_phi_g_S_isBigO` with `q_S_asymp` and the algebraic
expansion of `q(1-q)` we obtain `Var ρ_S g_S = 1/S - 2/S^2 + O(S^{-3})`. -/
theorem Var_phi_g_S_expansion :
    (fun S : ℝ => Var_phi S (g_S S) - (1/S - 2/S^2))
      =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-3 : ℤ) := by
  -- Decompose: Var − (1/S − 2/S²) = (Var − q(1−q)) + (q(1−q) − (1/S − 2/S²)).
  have h_split : (fun S : ℝ => Var_phi S (g_S S) - (1/S - 2/S^2))
      = (fun S => (Var_phi S (g_S S) - q_S S * (1 - q_S S))
          + (q_S S * (1 - q_S S) - (1/S - 2/S^2))) := by
    funext S; ring
  rw [h_split]
  refine IsBigO.add Var_phi_g_S_isBigO ?_
  -- Second piece: bound |q(1−q) − (1/S − 2/S²)| ≤ K · S^{−3} for S large.
  obtain ⟨C, S₀, hS₀_pos, hr_b⟩ := q_S_asymp
  -- C is necessarily nonneg.
  have hC_nn : 0 ≤ C := by
    have h := hr_b S₀ le_rfl
    have h_abs_nn : 0 ≤ |q_S S₀ - (1/S₀ - 1/S₀^2)| := abs_nonneg _
    have hS₀_pow_pos : 0 < S₀^(-(3:ℤ)) := zpow_pos hS₀_pos _
    nlinarith
  -- Witness K = 3 + 5C + C².
  refine IsBigO.of_bound (3 + 5*C + C^2) ?_
  rw [Filter.eventually_atTop]
  refine ⟨max S₀ 1, fun S hS => ?_⟩
  have hS_S₀ : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hS_1 : (1 : ℝ) ≤ S := le_trans (le_max_right _ _) hS
  have hS_pos : 0 < S := by linarith
  have hSnz : S ≠ 0 := hS_pos.ne'
  -- The bound from q_S_asymp.
  have hr_bound := hr_b S hS_S₀
  set r := q_S S - (1/S - 1/S^2) with hr_def
  have hS3_pos : (0 : ℝ) < S^3 := by positivity
  have hS4_pos : (0 : ℝ) < S^4 := by positivity
  have hS6_pos : (0 : ℝ) < S^6 := by positivity
  -- Translate the BigOInv bound to `|r| ≤ C / S^3`.
  have h_zpow : (S : ℝ)^(-(3:ℤ)) = 1 / S^3 := by
    rw [show (-(3:ℤ)) = -((3:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
    rw [one_div]
  have hr_bound' : |r| ≤ C / S^3 := by
    calc |r| ≤ C * (S : ℝ)^(-(3:ℤ)) := hr_bound
      _ = C * (1 / S^3) := by rw [h_zpow]
      _ = C / S^3 := by ring
  -- Algebraic identity.
  have h_alg : q_S S * (1 - q_S S) - (1/S - 2/S^2)
      = 2/S^3 - 1/S^4 + r * (1 - 2*(1/S - 1/S^2)) - r^2 := by
    rw [hr_def]; ring
  -- Bound |B(S)| ≤ 5 where B(S) := 1 - 2(1/S - 1/S²).
  have hB_bound : |1 - 2*(1/S - 1/S^2)| ≤ 5 := by
    have h2 : (1 : ℝ)/S ≤ 1 := by rw [div_le_one hS_pos]; exact hS_1
    have h4 : (1 : ℝ)/S^2 ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < S^2)]
      nlinarith
    have h1 : (0 : ℝ) ≤ 1/S := by positivity
    have h3 : (0 : ℝ) ≤ 1/S^2 := by positivity
    rw [abs_le]; refine ⟨by nlinarith, by nlinarith⟩
  -- ‖S^{-3}‖ = 1/S³.
  have h_norm_eq : ‖(S : ℝ)^(-(3:ℤ))‖ = 1/S^3 := by
    rw [Real.norm_eq_abs, h_zpow, abs_of_pos (by positivity : (0:ℝ) < 1/S^3)]
  -- Power inequalities.
  have h_s4_le_s3 : (1 : ℝ)/S^4 ≤ 1/S^3 := by
    rw [div_le_div_iff_of_pos_left one_pos hS4_pos hS3_pos]
    nlinarith
  have h_s6_le_s3 : (1 : ℝ)/S^6 ≤ 1/S^3 := by
    rw [div_le_div_iff_of_pos_left one_pos hS6_pos hS3_pos]
    have hS3_ge_1 : (1 : ℝ) ≤ S^3 := by nlinarith [hS_1]
    have hSS : S^6 = S^3 * S^3 := by ring
    nlinarith [hS3_ge_1, hSS]
  -- Bound each piece.
  have habs2 : |(2 : ℝ)/S^3| = 2/S^3 := abs_of_pos (by positivity)
  have habs3 : |(1 : ℝ)/S^4| = 1/S^4 := abs_of_pos (by positivity)
  have habs_rB : |r * (1 - 2*(1/S - 1/S^2))| ≤ (C / S^3) * 5 := by
    rw [abs_mul]
    exact mul_le_mul hr_bound' hB_bound (abs_nonneg _) (by positivity)
  have habs_rsq : |r^2| ≤ C^2 / S^3 := by
    rw [show r^2 = r * r from sq r, abs_mul]
    have h1 : |r| * |r| ≤ (C / S^3) * (C / S^3) :=
      mul_le_mul hr_bound' hr_bound' (abs_nonneg _) (by positivity)
    have h_eq : (C / S^3) * (C / S^3) = C^2 * (1/S^6) := by
      field_simp
    rw [h_eq] at h1
    refine le_trans h1 ?_
    have h2 : C^2 * (1/S^6) ≤ C^2 * (1/S^3) :=
      mul_le_mul_of_nonneg_left h_s6_le_s3 (by positivity)
    have h3 : C^2 * (1/S^3) = C^2 / S^3 := by field_simp
    linarith
  -- Triangle inequality decomposition.
  rw [Real.norm_eq_abs, h_alg, h_norm_eq]
  have h_tri1 : |2/S^3 - 1/S^4 + r * (1 - 2*(1/S - 1/S^2)) - r^2|
              ≤ |2/S^3 - 1/S^4 + r * (1 - 2*(1/S - 1/S^2))| + |r^2| :=
    abs_sub _ _
  have h_tri2 : |2/S^3 - 1/S^4 + r * (1 - 2*(1/S - 1/S^2))|
              ≤ |2/S^3 - 1/S^4| + |r * (1 - 2*(1/S - 1/S^2))| :=
    abs_add_le _ _
  have h_tri3 : |2/S^3 - 1/S^4| ≤ |2/S^3| + |1/S^4| := abs_sub _ _
  -- Now combine: bound is at most 2/S³ + 1/S³ + 5C/S³ + C²/S³.
  have h_combined : |2/S^3 - 1/S^4 + r * (1 - 2*(1/S - 1/S^2)) - r^2|
              ≤ 2/S^3 + 1/S^3 + (C / S^3) * 5 + C^2 / S^3 := by
    have h_s4_part : |1/S^4| ≤ 1/S^3 := by rw [habs3]; exact h_s4_le_s3
    linarith
  -- Final: equate to (3 + 5C + C²) * (1/S³).
  have h_final_eq : 2/S^3 + 1/S^3 + (C / S^3) * 5 + C^2 / S^3
                  = (3 + 5*C + C^2) * (1/S^3) := by
    field_simp; ring
  linarith

/-! ## Ratio estimate pieces -/

/-- The ratio `Var / Energy` used in the 1D contradiction. -/
noncomputable def varEnergyRatio (S : ℝ) : ℝ :=
  Var_phi S (g_S S) / E_phi S (g_S' S)

/-- For large `S`, the ratio is well-defined (energy positive). -/
lemma varEnergyRatio_eq {S : ℝ} (hS : 1 < S) :
    varEnergyRatio S = Var_phi S (g_S S) * (Z_S S * A_S S) / 2 := by
  unfold varEnergyRatio
  rw [E_phi_g_S_eq hS, div_div_eq_mul_div]

end L2Counterexample
