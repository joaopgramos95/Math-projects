import L2Counterexample.Potential

/-!
# Normalization and asymptotics (WIP)

This is the editable WIP version of `Normalization.lean`. It formalises the
normalising constants `Z_S`, `tailInt_S`, `q_S`, `t_S` of section 3 of the
counterexample paper, together with their tail asymptotic expansions.

## Layered approach

`Potential.lean` is currently a stub.  Following the project rule that WIP
files may axiomatise the upstream API while keeping the present file
sorry-free, we declare:

1.  The potential family `phi_S`, the parameters `eps_S`, `eta_S`, and the
    qualitative facts about `phi_S` (measurability, evenness, the quadratic
    lower bound, the regional formulas) used in section 3 of the paper.
2.  The two analytic black-box facts that depend on `phi_S` and would
    otherwise pull in heavy measure-theoretic / change-of-variables
    arguments:
    - the change-of-variables identity for the tail integral
      (`tailInt_S_tail_eq`);
    - the symmetric decomposition `Z_S = 2 (∫_core + ∫_layer + tailInt_S)`
      (`Z_S_decomposition`).
3.  Two elementary exponential integrals (Laplace transforms `1/a` and
    `2/a^3`) that should land in `Mathlib`.

Asymptotic expansions are encoded by the explicit finitary inequality

  `BigOInv f g k := ∃ C S₀, 0 < S₀ ∧ ∀ S ≥ S₀, |f S - g S| ≤ C·S^(-k)`,

which keeps the proofs inside `linarith` / `nlinarith` reach and avoids the
overhead of `Asymptotics.IsBigO` for development.  The upstream "blueprint"
asymptotic estimates from section 3 are stated and used as axioms here; once
`Potential.lean` is filled in they will be discharged.
-/

noncomputable section

open MeasureTheory Real
open scoped Topology

namespace L2Counterexample

/-! ## Asymptotic shorthand -/

/-- `BigOInv f g k` means `f S = g S + O(S^{-k})` as `S → ∞`, encoded as an
explicit finitary inequality over real `S`. -/
def BigOInv (f g : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → |f S - g S| ≤ C * S ^ (-(k : ℤ))

lemma bigOInv_zero_iff (f : ℝ → ℝ) (k : ℕ) :
    BigOInv f (fun _ => 0) k ↔
      ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → |f S| ≤ C * S ^ (-(k : ℤ)) := by
  unfold BigOInv
  simp

/-! ### Algebra of `BigOInv` -/

lemma BigOInv.add {f g f' g' : ℝ → ℝ} {k : ℕ}
    (h : BigOInv f g k) (h' : BigOInv f' g' k) :
    BigOInv (fun S => f S + f' S) (fun S => g S + g' S) k := by
  obtain ⟨C, S₀, hS₀, hC⟩ := h
  obtain ⟨C', S₀', hS₀', hC'⟩ := h'
  refine ⟨C + C', max S₀ S₀', lt_max_of_lt_left hS₀, fun S hS => ?_⟩
  have hSS₀ : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hSS₀' : S₀' ≤ S := le_trans (le_max_right _ _) hS
  have h1 := hC S hSS₀
  have h2 := hC' S hSS₀'
  have habs : |f S + f' S - (g S + g' S)| ≤ |f S - g S| + |f' S - g' S| := by
    have hrw : f S + f' S - (g S + g' S) = (f S - g S) + (f' S - g' S) := by ring
    rw [hrw]
    exact abs_add_le _ _
  calc |f S + f' S - (g S + g' S)|
      ≤ |f S - g S| + |f' S - g' S| := habs
    _ ≤ C * S ^ (-(k : ℤ)) + C' * S ^ (-(k : ℤ)) := by linarith
    _ = (C + C') * S ^ (-(k : ℤ)) := by ring

lemma BigOInv.sub {f g f' g' : ℝ → ℝ} {k : ℕ}
    (h : BigOInv f g k) (h' : BigOInv f' g' k) :
    BigOInv (fun S => f S - f' S) (fun S => g S - g' S) k := by
  obtain ⟨C, S₀, hS₀, hC⟩ := h
  obtain ⟨C', S₀', hS₀', hC'⟩ := h'
  refine ⟨C + C', max S₀ S₀', lt_max_of_lt_left hS₀, fun S hS => ?_⟩
  have hSS₀ : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hSS₀' : S₀' ≤ S := le_trans (le_max_right _ _) hS
  have h1 := hC S hSS₀
  have h2 := hC' S hSS₀'
  have habs : |f S - f' S - (g S - g' S)| ≤ |f S - g S| + |f' S - g' S| := by
    have hrw : f S - f' S - (g S - g' S) = (f S - g S) - (f' S - g' S) := by ring
    rw [hrw]
    exact abs_sub _ _
  calc |f S - f' S - (g S - g' S)|
      ≤ |f S - g S| + |f' S - g' S| := habs
    _ ≤ C * S ^ (-(k : ℤ)) + C' * S ^ (-(k : ℤ)) := by linarith
    _ = (C + C') * S ^ (-(k : ℤ)) := by ring

lemma BigOInv.const_mul {f g : ℝ → ℝ} {k : ℕ} (c : ℝ) (h : BigOInv f g k) :
    BigOInv (fun S => c * f S) (fun S => c * g S) k := by
  obtain ⟨C, S₀, hS₀, hC⟩ := h
  refine ⟨|c| * C, S₀, hS₀, fun S hS => ?_⟩
  have hb := hC S hS
  have habs : |c * f S - c * g S| = |c| * |f S - g S| := by
    rw [show c * f S - c * g S = c * (f S - g S) from by ring, abs_mul]
  rw [habs]
  have h1 : |c| * |f S - g S| ≤ |c| * (C * S ^ (-(k : ℤ))) := by
    apply mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  linarith [h1]

/-! ## Parameters

`eps_S` and `eta_S` are imported from `L2Counterexample.Potential`. We
collect a few elementary positivity / nonnegativity lemmas about them
here for downstream convenience. -/

lemma eps_S_nonneg {S : ℝ} (hS : 0 < S) : 0 ≤ eps_S S := (eps_S_pos hS).le

lemma eta_S_nonneg {S : ℝ} (hS : 0 < S) : 0 ≤ eta_S S := (eta_S_pos hS).le

/-- Helper: `S ^ (-k:ℤ) = 1 / S^k` for `S ≠ 0`. -/
lemma zpow_negNat (S : ℝ) (k : ℕ) (_hS : S ≠ 0) :
    S ^ (-(k : ℤ)) = 1 / S ^ k := by
  rw [zpow_neg, zpow_natCast, one_div]

/-! ## Potential interface (extra facts not provided by `Potential.lean`)

`phi_S` itself, evenness `phi_S_even`, the quadratic lower bound
`phi_S_quadratic_lower`, and the core region formula `phi_S_core` are
already provided by `L2Counterexample.Potential`. Here we record the
remaining facts needed for the asymptotic estimates of section 3. -/

/-- `phi_S S ·` is measurable, derived from continuity (which itself
follows from `phi_S_contDiff`). Requires `0 < S`. -/
theorem phi_S_measurable {S : ℝ} (hS : 0 < S) :
    Measurable (fun x => phi_S S x) :=
  (phi_S_contDiff hS).continuous.measurable

/-- Tail region formula (the right-half analogue of `phi_S_core` for
`x ≥ 1 + ε_S`). Not yet derived from `Potential.lean`'s building
blocks. -/
axiom phi_S_tail (S x : ℝ) (hS : 0 < S) (hx : 1 + eps_S S ≤ x) :
    phi_S S x
      = phi_S S (1 + eps_S S)
        + S * (x - 1 - eps_S S)
        + eta_S S / 2 * (x ^ 2 - (1 + eps_S S) ^ 2)

/-- Smallness at the layer boundary: `phi_S S (1+ε_S) = O(S^{-2})`. -/
axiom phi_S_boundary_small :
    BigOInv (fun S => phi_S S (1 + eps_S S)) (fun _ => 0) 2

/-- Helper: `phiDer_S` is nonneg on `[0, ∞)` (since it has `phiDer_S 0 = 0`
and `phiDer2_S ≥ 0`). -/
private lemma phiDer_S_nonneg_of_nonneg {S : ℝ} (hS : 0 < S) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ phiDer_S S t := by
  -- phiDer_S t - phiDer_S 0 = ∫_0^t phiDer2_S, which is nonneg.
  have h_eq : phiDer_S S t = phiDer_S S 0 + ∫ s in (0 : ℝ)..t, phiDer2_S S s := by
    rw [phiDer_S_zero, zero_add]
    show psi (phiDer2_S S) t = ∫ s in (0:ℝ)..t, phiDer2_S S s
    unfold psi; rfl
  rw [h_eq, phiDer_S_zero, zero_add]
  apply intervalIntegral.integral_nonneg ht
  intros s _
  exact (phiDer2_S_pos hS s).le

/-- Helper: `phi_S` is non-decreasing on `[0, ∞)`. -/
private lemma phi_S_le_of_le {S : ℝ} (hS : 0 < S) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : phi_S S a ≤ phi_S S b := by
  -- phi_S b - phi_S a = ∫_a^b phi'_S(t) dt ≥ 0 since phi'_S ≥ 0 on [0, ∞).
  have h_phi_eq : ∀ c : ℝ, phi_S S c = ∫ t in (0:ℝ)..c, phiDer_S S t := fun c => rfl
  have h_int_int : IntervalIntegrable (phiDer_S S) MeasureTheory.volume 0 b :=
    (phiDer_S_contDiff hS).continuous.intervalIntegrable 0 b
  have h_int_int_a : IntervalIntegrable (phiDer_S S) MeasureTheory.volume 0 a :=
    (phiDer_S_contDiff hS).continuous.intervalIntegrable 0 a
  have h_int_int_ab : IntervalIntegrable (phiDer_S S) MeasureTheory.volume a b :=
    (phiDer_S_contDiff hS).continuous.intervalIntegrable a b
  have h_int_eq := (intervalIntegral.integral_add_adjacent_intervals
                       h_int_int_a h_int_int_ab).symm
  have h_eq : phi_S S b = phi_S S a + ∫ t in a..b, phiDer_S S t := by
    rw [h_phi_eq b, h_int_eq, h_phi_eq a]
  rw [h_eq]
  have h_int_nn : 0 ≤ ∫ t in a..b, phiDer_S S t := by
    apply intervalIntegral.integral_nonneg hab
    intros t ht
    exact phiDer_S_nonneg_of_nonneg hS (le_trans ha ht.1)
  linarith

/-- Uniform smallness on the layer for `exp(-phi_S)`: `|exp(-phi_S(x)) - 1| =
O(S^{-2})` when `|x-1| ≤ ε_S`. Derived from `phi_S_boundary_small` plus
the monotonicity of `phi_S` on `[0, ∞)`. -/
theorem phi_S_layer_small :
    ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → ∀ x,
      |x - 1| ≤ eps_S S → |Real.exp (-(phi_S S x)) - 1| ≤ C * S ^ (-(2 : ℤ)) := by
  obtain ⟨C, S₀, hS₀_pos, h_bd⟩ := phi_S_boundary_small
  refine ⟨C, max S₀ 1, lt_max_of_lt_right one_pos, ?_⟩
  intro S hS x hx
  have hS₀_le : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hS_one : 1 ≤ S := le_trans (le_max_right _ _) hS
  have hSpos : 0 < S := by linarith
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have hx_le : x ≤ 1 + eps_S S := by
    have := (abs_le.mp hx).2; linarith
  have hx_ge : 1 - eps_S S ≤ x := by
    have := (abs_le.mp hx).1; linarith
  -- For x in [1-ε, 1+ε], phi_S(x) ≤ phi_S(1+ε) by monotonicity on [0, ∞).
  -- For S ≥ 1, eps_S = 1/S^3 ≤ 1, so x ≥ 1 - ε ≥ 0.
  have heps_le_one : eps_S S ≤ 1 := by
    unfold eps_S
    rw [show ((-(3 : ℤ))) = -((3 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hS_one)
  have hx_nn : 0 ≤ x := by linarith
  have h_phi_le : phi_S S x ≤ phi_S S (1 + eps_S S) :=
    phi_S_le_of_le hSpos hx_nn hx_le
  -- phi_S nonneg via quadratic lower bound.
  have h_phi_x_nn : 0 ≤ phi_S S x := by
    have h_q := phi_S_quadratic_lower hSpos x
    have h_quad_nn : 0 ≤ eta_S S * x ^ 2 / 2 := by
      have := eta_S_pos hSpos
      positivity
    linarith
  have h_phi_1eps_nn : 0 ≤ phi_S S (1 + eps_S S) := by
    have h_q := phi_S_quadratic_lower hSpos (1 + eps_S S)
    have h_quad_nn : 0 ≤ eta_S S * (1 + eps_S S) ^ 2 / 2 := by
      have := eta_S_pos hSpos
      positivity
    linarith
  -- |exp(-phi) - 1| = 1 - exp(-phi) ≤ phi_S ≤ phi_S(1+ε) ≤ C * S^(-2).
  have h_one_sub_le : 1 - Real.exp (-(phi_S S x)) ≤ phi_S S x := by
    have h := Real.add_one_le_exp (-(phi_S S x))
    linarith
  have h_exp_le_one : Real.exp (-(phi_S S x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have h_neg_le_zero : Real.exp (-(phi_S S x)) - 1 ≤ 0 := by linarith
  have h_abs_eq : |Real.exp (-(phi_S S x)) - 1| = 1 - Real.exp (-(phi_S S x)) := by
    rw [abs_of_nonpos h_neg_le_zero]; ring
  rw [h_abs_eq]
  -- |phi_S(1+ε) - 0| ≤ C * S^(-2)
  have h_phi_bd_raw : |phi_S S (1 + eps_S S) - 0| ≤ C * S ^ (-(2 : ℤ)) :=
    h_bd S hS₀_le
  have h_phi_bd : phi_S S (1 + eps_S S) ≤ C * S ^ (-(2 : ℤ)) := by
    rw [sub_zero] at h_phi_bd_raw
    rw [abs_of_nonneg h_phi_1eps_nn] at h_phi_bd_raw
    exact h_phi_bd_raw
  linarith

/-! ## Integrability -/

/-- Integrability of `exp(-phi_S S)` (Gaussian domination).

Proof: `phi_S(x) ≥ η_S · x² / 2` (`phi_S_quadratic_lower`), so
`exp(-phi_S(x)) ≤ exp(-η_S · x² / 2)`, which is Gaussian and integrable
on `ℝ` by `integrable_exp_neg_mul_sq`. Apply Mathlib's domination
criterion. -/
theorem exp_negPhiS_integrable (S : ℝ) (hS : 0 < S) :
    Integrable (fun x => Real.exp (-(phi_S S x))) := by
  have heta_pos : 0 < eta_S S := eta_S_pos hS
  have heta_half_pos : 0 < eta_S S / 2 := by linarith
  -- Bound: exp(-phi_S(x)) ≤ exp(-(η_S/2) · x²).
  have h_bd : ∀ x, Real.exp (-(phi_S S x))
                  ≤ Real.exp (-(eta_S S / 2) * x ^ 2) := by
    intro x
    apply Real.exp_le_exp.mpr
    have h_q := phi_S_quadratic_lower hS x
    -- η_S/2 * x² ≤ phi_S(x), so -phi_S(x) ≤ -η_S/2 * x², so -phi_S(x) ≤ -(η_S/2)·x².
    have h_eq : eta_S S * x^2 / 2 = (eta_S S / 2) * x^2 := by ring
    linarith [h_q, h_eq]
  -- Gaussian integrability.
  have h_gauss : Integrable (fun x : ℝ => Real.exp (-(eta_S S / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq heta_half_pos
  -- Apply domination.
  have h_meas : AEStronglyMeasurable (fun x => Real.exp (-(phi_S S x))) volume :=
    (Real.continuous_exp.comp (phi_S_contDiff hS).continuous.neg).aestronglyMeasurable
  refine h_gauss.mono h_meas (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  exact h_bd x

/-- Integrability on the tail half-line, derived from full integrability. -/
theorem exp_negPhiS_integrableOn_tail (S : ℝ) (hS : 0 < S) :
    IntegrableOn (fun x => Real.exp (-(phi_S S x))) (Set.Ici (1 + eps_S S)) :=
  (exp_negPhiS_integrable S hS).integrableOn

/-- Integrability of the Gaussian-tail integrand on `[0,∞)`. The
integrand is bounded by `exp(-B/2 · u²)` (a Gaussian, integrable on
all of `ℝ`), so it is integrable on any subset. -/
theorem exp_negGaussianTail_integrableOn (A B : ℝ) (_hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (fun u => Real.exp (-(A * u) - B * u ^ 2 / 2)) (Set.Ici (0 : ℝ)) := by
  -- Bound by exp(-(B/2) * u^2), which is integrable on all of ℝ.
  have hB2 : (0 : ℝ) < B / 2 := by linarith
  have h_gauss : Integrable (fun u : ℝ => Real.exp (-(B / 2) * u ^ 2)) :=
    integrable_exp_neg_mul_sq hB2
  have h_gauss_on : IntegrableOn (fun u : ℝ => Real.exp (-(B / 2) * u ^ 2))
      (Set.Ici 0) := h_gauss.integrableOn
  -- Measurability of the integrand.
  have h_meas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-(A * u) - B * u ^ 2 / 2))
      (volume.restrict (Set.Ici (0 : ℝ))) := by
    refine (Real.continuous_exp.comp (Continuous.sub ?_ ?_)).aestronglyMeasurable
    · exact (continuous_const.mul continuous_id).neg
    · exact ((continuous_const.mul (continuous_id.pow 2)).div_const 2)
  -- Bound: for `u ∈ Ici 0`, `|exp(-Au - Bu²/2)| ≤ exp(-(B/2) u²)`.
  refine Integrable.mono h_gauss_on h_meas ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
  intro u hu
  have hu0 : 0 ≤ u := hu
  have h_lhs_pos : 0 < Real.exp (-(A * u) - B * u ^ 2 / 2) := Real.exp_pos _
  have h_rhs_pos : 0 < Real.exp (-(B / 2) * u ^ 2) := Real.exp_pos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos h_lhs_pos, abs_of_pos h_rhs_pos]
  apply Real.exp_le_exp.mpr
  -- Show: -(A*u) - B*u²/2 ≤ -(B/2)*u²
  -- i.e. -A*u ≤ 0  ⇔  A*u ≥ 0 (since u ≥ 0 and A > 0).
  have h_Au_nn : 0 ≤ A * u := mul_nonneg _hA.le hu0
  nlinarith

/-! ## Core constants -/

/-- The partition function `Z_S = ∫_ℝ exp(-phi_S S) dx`. -/
def Z_S (S : ℝ) : ℝ := ∫ x, Real.exp (-(phi_S S x))

/-- The right-tail exponential integral
`tailInt_S = ∫_{1+ε_S}^{∞} exp(-phi_S S) dx`. -/
def tailInt_S (S : ℝ) : ℝ := ∫ x in Set.Ici (1 + eps_S S), Real.exp (-(phi_S S x))

/-- The tail probability mass `q_S = (2/Z_S) · tailInt_S`. -/
def q_S (S : ℝ) : ℝ := 2 * tailInt_S S / Z_S S

/-- The two-sided layer set `T_S = [-1-ε_S, -1+ε_S] ∪ [1-ε_S, 1+ε_S]`. -/
def T_S (S : ℝ) : Set ℝ :=
  Set.Icc (-1 - eps_S S) (-1 + eps_S S) ∪ Set.Icc (1 - eps_S S) (1 + eps_S S)

/-- The layer mass `t_S = ρ_S(T_S)`. -/
def t_S (S : ℝ) : ℝ :=
  (∫ x in T_S S, Real.exp (-(phi_S S x))) / Z_S S

/-! ## Positivity -/

lemma exp_negPhiS_pos (S x : ℝ) : 0 < Real.exp (-(phi_S S x)) :=
  Real.exp_pos _

lemma exp_negPhiS_nonneg (S x : ℝ) : 0 ≤ Real.exp (-(phi_S S x)) :=
  (exp_negPhiS_pos S x).le

/-- `Z_S` is strictly positive: the integrand `exp(-phi_S)` is everywhere
strictly positive and integrable (`exp_negPhiS_integrable`), and
`volume` on `ℝ` has nonzero measure, so the integral is strictly positive.
Direct application of `integral_exp_pos`. -/
theorem Z_S_pos (S : ℝ) (hS : 0 < S) : 0 < Z_S S := by
  unfold Z_S
  exact integral_exp_pos (exp_negPhiS_integrable S hS)

lemma Z_S_ne_zero (S : ℝ) (hS : 0 < S) : Z_S S ≠ 0 := (Z_S_pos S hS).ne'

lemma tailInt_S_nonneg (S : ℝ) (hS : 0 < S) : 0 ≤ tailInt_S S := by
  unfold tailInt_S
  exact setIntegral_nonneg measurableSet_Ici (fun x _ => exp_negPhiS_nonneg S x)

lemma q_S_nonneg (S : ℝ) (hS : 0 < S) : 0 ≤ q_S S := by
  unfold q_S
  have h1 : 0 ≤ 2 * tailInt_S S := by
    have := tailInt_S_nonneg S hS
    positivity
  exact div_nonneg h1 (Z_S_pos S hS).le

lemma t_S_nonneg (S : ℝ) (hS : 0 < S) : 0 ≤ t_S S := by
  unfold t_S
  refine div_nonneg ?_ (Z_S_pos S hS).le
  refine setIntegral_nonneg ?_ (fun x _ => exp_negPhiS_nonneg S x)
  exact measurableSet_Icc.union measurableSet_Icc

/-! ## Half-line exponential integrals (Laplace transforms)

These two identities (`∫₀^∞ e^{-au} du = 1/a` and `∫₀^∞ u² e^{-au} du = 2/a^3`)
should sit in Mathlib; they are recorded here as axioms with explicit
`to_mathlib` markers. -/

/-- `∫₀^∞ e^{-a u} du = 1/a` for `a > 0`. Specialisation of
`Real.integral_rpow_mul_exp_neg_mul_Ioi` at the exponent `α = 1`,
with `t^(1-1) = 1` and `Γ(1) = 1`. -/
theorem integral_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    ∫ u in Set.Ici (0 : ℝ), Real.exp (-(a * u)) = 1 / a := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := a)
              zero_lt_one ha
  simp only [sub_self, Real.rpow_zero, one_mul, Real.Gamma_one,
    mul_one, Real.rpow_one] at h
  exact h

/-- `∫₀^∞ u² e^{-a u} du = 2/a^3` for `a > 0`. Specialisation of
`Real.integral_rpow_mul_exp_neg_mul_Ioi` at `α = 3` (so the integrand
becomes `t² · e^{-a t}`, with `Γ(3) = 2!`). -/
theorem integral_sq_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    ∫ u in Set.Ici (0 : ℝ), u ^ 2 * Real.exp (-(a * u)) = 2 / a ^ 3 := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := a)
              (by norm_num) ha
  -- Convert `t ^ (3 - 1 : ℝ) = t^2` (using `t > 0` in `Ioi`).
  have h_int_eq : ∫ t in Set.Ioi (0 : ℝ), t ^ ((3 : ℝ) - 1) * Real.exp (-(a * t))
                = ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * Real.exp (-(a * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht_pos : 0 < t := ht
    have : t ^ ((3 : ℝ) - 1) = t ^ 2 := by
      rw [show (3 : ℝ) - 1 = (2 : ℕ) from by norm_num]
      exact Real.rpow_natCast t 2
    rw [this]
  rw [h_int_eq] at h
  -- `(1/a)^3 * Γ(3) = (1/a)^3 * 2 = 2/a^3`
  have hΓ : Real.Gamma 3 = 2 := by
    have h1 : (3 : ℝ) = (2 : ℕ) + 1 := by norm_num
    rw [h1, Real.Gamma_nat_eq_factorial 2]
    norm_num
  rw [hΓ] at h
  rw [h]
  have hane : a ≠ 0 := ha.ne'
  -- `(1/a)^(3 : ℝ)` is `Real.rpow`; convert to natural power.
  have hrpow : (1 / a : ℝ) ^ (3 : ℝ) = (1 / a) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rw [hrpow]
  rw [div_pow, one_pow]
  field_simp

/-! ## Elementary inequality `1 - e^{-v} ≤ v` -/

/-- For `v ≥ 0`, `0 ≤ 1 - exp(-v) ≤ v`. -/
lemma one_sub_exp_neg_le (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ 1 - Real.exp (-v) ∧ 1 - Real.exp (-v) ≤ v := by
  refine ⟨?_, ?_⟩
  · have h : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  · have h := Real.add_one_le_exp (-v)
    have hexp_pos := Real.exp_pos (-v)
    have hmul : Real.exp (-v) * Real.exp v = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos v, hexp_pos, h]

/-- Reformulation using `v = a u`. -/
lemma one_sub_exp_neg_mul_le {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    1 - Real.exp (-(a * u)) ≤ a * u :=
  (one_sub_exp_neg_le (a * u) (mul_nonneg ha hu)).2

/-! ## Tail integral computation

After translation `u = x - 1 - ε_S` and the tail formula for `phi_S`, the
integrand becomes
`exp(-phi_S (1+ε_S)) · exp(-(S+η(1+ε)) u - η u^2 / 2)`. -/

/-- Exponent in the transformed tail integrand. -/
def tildeS (S : ℝ) : ℝ := S + eta_S S * (1 + eps_S S)

lemma tildeS_pos {S : ℝ} (hS : 1 ≤ S) : 0 < tildeS S := by
  unfold tildeS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have h1 : 0 ≤ eta_S S * (1 + eps_S S) :=
    mul_nonneg (eta_S_pos hSpos).le (by linarith [(eps_S_pos hSpos).le])
  linarith

/-- Lower bound `S ≤ tildeS S` (the perturbation is nonneg). -/
lemma le_tildeS {S : ℝ} (hS : 1 ≤ S) : S ≤ tildeS S := by
  unfold tildeS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have : 0 ≤ eta_S S * (1 + eps_S S) :=
    mul_nonneg (eta_S_pos hSpos).le (by linarith [(eps_S_pos hSpos).le])
  linarith

/-- Change-of-variables identity for the tail integral.

Substitute `u = x - (1+ε_S)` (so `x = u + 1+ε_S`) on `Ici(1+ε_S)`, then
expand `phi_S(1+ε_S+u)` via `phi_S_tail` to get
`phi_S(1+ε_S) + tildeS·u + η/2·u²`, and pull the constant
`exp(-phi_S(1+ε_S))` out. -/
theorem tailInt_S_tail_eq (S : ℝ) (hS : 1 ≤ S) :
    tailInt_S S
      = Real.exp (-(phi_S S (1 + eps_S S)))
          * ∫ u in Set.Ici (0 : ℝ),
              Real.exp (-(tildeS S * u) - eta_S S * u ^ 2 / 2) := by
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have heta_pos : 0 < eta_S S := eta_S_pos hSpos
  -- Step 1: change of variables x = u + (1+ε_S) on Ici(1+ε_S).
  have h_meas_preserve : MeasureTheory.MeasurePreserving
      (fun u : ℝ => u + (1 + eps_S S)) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume (1 + eps_S S)
  have h_meas_emb : MeasurableEmbedding (fun u : ℝ => u + (1 + eps_S S)) :=
    (Homeomorph.addRight (1 + eps_S S)).isClosedEmbedding.measurableEmbedding
  have h_preimage : (fun u : ℝ => u + (1 + eps_S S)) ⁻¹' Set.Ici (1 + eps_S S)
                  = Set.Ici 0 := by
    ext u
    simp [Set.mem_Ici, Set.mem_preimage]
  have h_change : tailInt_S S
                = ∫ u in Set.Ici (0 : ℝ),
                    Real.exp (-(phi_S S (u + (1 + eps_S S)))) := by
    unfold tailInt_S
    rw [← h_preimage]
    exact (h_meas_preserve.setIntegral_preimage_emb h_meas_emb _ _).symm
  rw [h_change]
  -- Step 2: phi_S_tail simplification.
  have h_int_eq : ∫ u in Set.Ici (0 : ℝ),
                    Real.exp (-(phi_S S (u + (1 + eps_S S))))
                = ∫ u in Set.Ici (0 : ℝ),
                    Real.exp (-(phi_S S (1 + eps_S S)))
                      * Real.exp (-(tildeS S * u) - eta_S S * u ^ 2 / 2) := by
    refine setIntegral_congr_fun measurableSet_Ici ?_
    intro u hu
    have hu_nn : 0 ≤ u := hu
    -- u + (1 + ε_S) ≥ 1 + ε_S, so apply phi_S_tail.
    have h_x_ge : 1 + eps_S S ≤ u + (1 + eps_S S) := by linarith
    have h_phi := phi_S_tail S (u + (1 + eps_S S)) hSpos h_x_ge
    show Real.exp (-(phi_S S (u + (1 + eps_S S))))
       = Real.exp (-(phi_S S (1 + eps_S S)))
         * Real.exp (-(tildeS S * u) - eta_S S * u^2 / 2)
    rw [h_phi]
    -- Now need: exp(-(A + B + C)) = exp(-A) · exp(-(B' + C'))
    -- where B' = tildeS · u, C' = η · u²/2.
    -- After phi_S_tail: phi_S(1+ε+u) = phi_S(1+ε) + S·u + η/2·((u+1+ε)² - (1+ε)²)
    -- = phi_S(1+ε) + S·u + η/2·(u² + 2u(1+ε))
    -- = phi_S(1+ε) + S·u + η·(1+ε)·u + η·u²/2
    -- = phi_S(1+ε) + (S + η(1+ε))·u + η·u²/2
    -- = phi_S(1+ε) + tildeS·u + η·u²/2
    have h_arg_eq : phi_S S (1 + eps_S S)
        + S * (u + (1 + eps_S S) - 1 - eps_S S)
        + eta_S S / 2 * ((u + (1 + eps_S S))^2 - (1 + eps_S S)^2)
        = phi_S S (1 + eps_S S) + tildeS S * u + eta_S S * u^2 / 2 := by
      unfold tildeS
      ring
    rw [h_arg_eq]
    rw [show -(phi_S S (1 + eps_S S) + tildeS S * u + eta_S S * u^2 / 2)
          = -(phi_S S (1 + eps_S S)) + (-(tildeS S * u) - eta_S S * u^2 / 2)
          from by ring]
    rw [Real.exp_add]
  rw [h_int_eq]
  -- Step 3: pull constant out of integral.
  rw [← MeasureTheory.integral_const_mul]

/-! ## Asymptotics of the Gaussian-tail integral

The two-sided bound
    `0 ≤ 1/S̃ - ∫₀^∞ exp(-S̃ u - η u²/2) du ≤ η / S̃³`
is a direct consequence of `1 - e^{-v} ≤ v` applied pointwise to
`v = η u²/2`. -/

/-- Helper: `IntegrableOn (exp(-(a · u))) (Ici 0)` for `a > 0`. -/
private lemma integrableOn_exp_neg_mul_Ici {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u => Real.exp (-(a * u))) (Set.Ici (0 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h_int :
      IntegrableOn (fun u : ℝ => u ^ (0 : ℝ) * Real.exp (-a * u ^ (1 : ℝ)))
        (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1 : ℝ) < 0) (le_refl 1) ha
  refine h_int.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hu_pos : 0 < u := hu
  show u ^ (0 : ℝ) * Real.exp (-a * u ^ (1 : ℝ)) = Real.exp (-(a * u))
  rw [Real.rpow_zero, Real.rpow_one, one_mul, neg_mul]

theorem tail_gaussian_bound (S : ℝ) (hS : 1 ≤ S) :
    let I := ∫ u in Set.Ici (0 : ℝ),
                Real.exp (-(tildeS S * u) - eta_S S * u ^ 2 / 2)
    0 ≤ 1 / tildeS S - I ∧ 1 / tildeS S - I ≤ eta_S S / tildeS S ^ 3 := by
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have htildeS_pos : 0 < tildeS S := tildeS_pos hS
  have heta_pos : 0 < eta_S S := eta_S_pos hSpos
  have heta_nn : 0 ≤ eta_S S := heta_pos.le
  have htildeS_nn : 0 ≤ tildeS S := htildeS_pos.le
  -- J(u) := exp(-(tildeS · u)), the "no Gaussian factor" integrand.
  -- h(u) := exp(-(tildeS · u) - eta · u² / 2), the actual integrand.
  set J : ℝ → ℝ := fun u => Real.exp (-(tildeS S * u)) with hJ_def
  set h : ℝ → ℝ := fun u =>
    Real.exp (-(tildeS S * u) - eta_S S * u ^ 2 / 2) with hh_def
  -- Integrability.
  have h_int_J : IntegrableOn J (Set.Ici (0 : ℝ)) :=
    integrableOn_exp_neg_mul_Ici htildeS_pos
  have h_int_h : IntegrableOn h (Set.Ici (0 : ℝ)) :=
    exp_negGaussianTail_integrableOn (tildeS S) (eta_S S) htildeS_pos heta_pos
  -- Pointwise: J - h = exp(-(tildeS u)) · (1 - exp(-η u²/2)) ≥ 0.
  have h_diff_eq : ∀ u : ℝ,
      J u - h u
        = Real.exp (-(tildeS S * u)) * (1 - Real.exp (-(eta_S S * u^2 / 2))) := by
    intro u
    simp only [J, h, hJ_def, hh_def]
    rw [show -(tildeS S * u) - eta_S S * u^2 / 2
          = -(tildeS S * u) + (-(eta_S S * u^2 / 2)) from by ring,
        Real.exp_add]
    ring
  have h_diff_nn : ∀ u, 0 ≤ J u - h u := by
    intro u
    rw [h_diff_eq u]
    refine mul_nonneg (Real.exp_pos _).le ?_
    have hv_nn : 0 ≤ eta_S S * u^2 / 2 := by
      have : 0 ≤ u^2 := sq_nonneg _
      positivity
    exact (one_sub_exp_neg_le _ hv_nn).1
  -- Pointwise: J - h ≤ exp(-(tildeS u)) · (η u² / 2).
  have h_diff_ub : ∀ u, J u - h u
      ≤ Real.exp (-(tildeS S * u)) * (eta_S S * u^2 / 2) := by
    intro u
    rw [h_diff_eq u]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have hv_nn : 0 ≤ eta_S S * u^2 / 2 := by positivity
    exact (one_sub_exp_neg_le _ hv_nn).2
  -- The integral 1/S̃ - I = ∫ (J - h).
  have h_int_diff : (1 : ℝ) / tildeS S - ∫ u in Set.Ici 0, h u
      = ∫ u in Set.Ici 0, J u - h u := by
    rw [integral_sub h_int_J h_int_h]
    -- ∫ J = 1/tildeS S
    have h_J_int : ∫ u in Set.Ici 0, J u = 1 / tildeS S :=
      integral_exp_neg_Ici (tildeS S) htildeS_pos
    rw [h_J_int]
  -- Lower bound (a): 0 ≤ 1/S̃ - I.
  refine ⟨?_, ?_⟩
  · rw [h_int_diff]
    apply setIntegral_nonneg measurableSet_Ici
    intro u _
    exact h_diff_nn u
  -- Upper bound (b): 1/S̃ - I ≤ η/S̃³.
  · rw [h_int_diff]
    -- ∫ (J - h) ≤ ∫ exp(-tildeS u) · (η u²/2)
    have h_ub : ∫ u in Set.Ici 0, J u - h u
        ≤ ∫ u in Set.Ici 0, Real.exp (-(tildeS S * u)) * (eta_S S * u^2 / 2) := by
      apply setIntegral_mono_on (h_int_J.sub h_int_h)
        ?_ measurableSet_Ici (fun u _ => h_diff_ub u)
      -- Integrability of the upper bound function.
      have h_factor : (fun u : ℝ => Real.exp (-(tildeS S * u)) * (eta_S S * u^2 / 2))
                    = (fun u => (eta_S S / 2) * (u^2 * Real.exp (-(tildeS S * u)))) := by
        funext u; ring
      rw [h_factor]
      refine Integrable.const_mul ?_ _
      -- u^2 · exp(-tildeS u) is integrable on Ici 0
      have h_intGamma : IntegrableOn
          (fun u : ℝ => u ^ (2 : ℝ) * Real.exp (-tildeS S * u ^ (1 : ℝ)))
          (Set.Ioi 0) :=
        integrableOn_rpow_mul_exp_neg_mul_rpow
          (by norm_num : (-1 : ℝ) < 2) (le_refl 1) htildeS_pos
      have h_intGamma_Ici :
          IntegrableOn (fun u : ℝ => u^2 * Real.exp (-(tildeS S * u))) (Set.Ici (0 : ℝ)) := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        refine h_intGamma.congr_fun ?_ measurableSet_Ioi
        intro u hu
        have hu_pos : 0 < u := hu
        show u ^ (2 : ℝ) * Real.exp (-tildeS S * u ^ (1 : ℝ))
              = u^2 * Real.exp (-(tildeS S * u))
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num,
            Real.rpow_natCast, Real.rpow_one, neg_mul]
      exact h_intGamma_Ici
    -- Compute the upper bound integral: (η/2) · ∫ u² exp(-tildeS u) = (η/2) · (2/tildeS³) = η/tildeS³.
    have h_compute : ∫ u in Set.Ici 0,
        Real.exp (-(tildeS S * u)) * (eta_S S * u^2 / 2)
        = eta_S S / tildeS S ^ 3 := by
      have h_factor : (fun u : ℝ => Real.exp (-(tildeS S * u)) * (eta_S S * u^2 / 2))
                    = (fun u => (eta_S S / 2) * (u^2 * Real.exp (-(tildeS S * u)))) := by
        funext u; ring
      rw [h_factor, integral_const_mul,
          integral_sq_exp_neg_Ici (tildeS S) htildeS_pos]
      field_simp
    linarith [h_ub, h_compute]

/-! ## Asymptotic blueprint lemmas

Two ingredients package the analytic content of section 3 into BigO
statements: -/

/-- `1/tildeS S = 1/S + O(S^{-6})`. The perturbation
`tildeS S − S = η_S(1 + ε_S) ≤ 2·S^{-4}` (for `S ≥ 1`, where
`ε_S ≤ 1`), and `S · tildeS S ≥ S²`, so
`|1/tildeS - 1/S| = |S - tildeS|/(S·tildeS) ≤ 2/S^6`. -/
theorem one_div_tildeS_asymp :
    BigOInv (fun S => 1 / tildeS S) (fun S => 1 / S) 6 := by
  refine ⟨2, 1, one_pos, ?_⟩
  intro S hS
  -- hS : 1 ≤ S
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have htildeS_pos : 0 < tildeS S := tildeS_pos hS
  have htildeS_ge_S : S ≤ tildeS S := le_tildeS hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have heta_pos : 0 < eta_S S := eta_S_pos hSpos
  have hS_ne : S ≠ 0 := hSpos.ne'
  have htildeS_ne : tildeS S ≠ 0 := htildeS_pos.ne'
  -- ε_S ≤ 1 for S ≥ 1.
  have heps_le_one : eps_S S ≤ 1 := by
    unfold eps_S
    rw [show ((-(3 : ℤ))) = -((3 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
    rw [inv_le_one_iff₀]
    right
    have hpow : S ^ 0 ≤ S ^ 3 := pow_le_pow_right₀ hS (by norm_num)
    simpa using hpow
  -- Perturbation: tildeS S - S = η_S * (1 + ε_S) ≤ 2 * η_S = 2 * S^(-4).
  have h_pert : tildeS S - S = eta_S S * (1 + eps_S S) := by
    unfold tildeS; ring
  have h_pert_le : tildeS S - S ≤ 2 * eta_S S := by
    rw [h_pert]
    have h1 : 1 + eps_S S ≤ 2 := by linarith
    have h2 : 0 ≤ eta_S S := heta_pos.le
    nlinarith
  have h_pert_nn : 0 ≤ tildeS S - S := by linarith
  -- |1/tildeS - 1/S| = |S - tildeS|/(S * tildeS) = (tildeS - S)/(S * tildeS)
  have h_diff : 1 / tildeS S - 1 / S = -(tildeS S - S) / (S * tildeS S) := by
    field_simp; ring
  -- Algebra: pow eq.
  have h_pow_eq : S ^ (-((6 : ℕ) : ℤ)) = 1 / S ^ 6 :=
    zpow_negNat S 6 hSpos.ne'
  rw [h_pow_eq, h_diff]
  rw [abs_div, abs_neg, abs_of_nonneg h_pert_nn,
      abs_of_pos (mul_pos hSpos htildeS_pos)]
  -- Goal: (tildeS S - S) / (S * tildeS S) ≤ 2 * (1 / S^6).
  rw [div_le_iff₀ (mul_pos hSpos htildeS_pos)]
  -- Goal: (tildeS S - S) ≤ 2 * (1/S^6) * (S * tildeS S)
  --     = 2 * tildeS S / S^5 (= 2 * tildeS / S^5).
  -- Use: tildeS - S ≤ 2 * eta_S = 2 * S^-4.
  -- So we want: 2 * S^-4 ≤ 2 * (1/S^6) * S * tildeS = 2 * tildeS / S^5.
  -- i.e., S^-4 ≤ tildeS / S^5, i.e., 1/S^4 ≤ tildeS/S^5, i.e., S ≤ tildeS. ✓
  have heta_eq : eta_S S = 1 / S ^ 4 := by
    unfold eta_S
    rw [show ((-(4 : ℤ))) = -((4 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast,
        one_div]
  have h_pert_le' : tildeS S - S ≤ 2 / S ^ 4 := by
    rw [show (2 : ℝ) / S^4 = 2 * (1 / S^4) from by ring, ← heta_eq]
    exact h_pert_le
  have hS4_pos : (0 : ℝ) < S ^ 4 := by positivity
  have hS5_pos : (0 : ℝ) < S ^ 5 := by positivity
  have hS6_pos : (0 : ℝ) < S ^ 6 := by positivity
  -- Show: 2/S^4 ≤ 2 * (1/S^6) * (S * tildeS S)
  -- ⇔ 1/S^4 ≤ tildeS S / S^5 (after dividing by 2 and rearranging)
  -- ⇔ S^5 ≤ tildeS S * S^4 ... no wait let me redo.
  -- 2 * (1/S^6) * (S * tildeS S) = 2 * S * tildeS S / S^6 = 2 * tildeS S / S^5.
  have h_target_eq :
      2 * (1 / S ^ 6) * (S * tildeS S) = 2 * tildeS S / S ^ 5 := by
    field_simp
  rw [h_target_eq]
  -- Goal: tildeS S - S ≤ 2 * tildeS S / S^5
  -- 2 * tildeS / S^5 ≥ 2 * S / S^5 = 2/S^4 ≥ tildeS - S.
  calc tildeS S - S ≤ 2 / S ^ 4 := h_pert_le'
    _ = 2 * S / S ^ 5 := by field_simp
    _ ≤ 2 * tildeS S / S ^ 5 := by
        rw [div_le_div_iff₀ hS5_pos hS5_pos]
        nlinarith [htildeS_ge_S, hSpos.le]

/-- `exp(-phi_S S (1+ε_S)) = 1 + O(S^{-2})`. From
`phi_S_boundary_small` (`phi_S(1+ε_S) = O(S^{-2})`) and the elementary
inequality `1 - exp(-v) ≤ v` for `v ≥ 0`, with `phi_S ≥ 0`. -/
theorem exp_neg_phi_boundary_asymp :
    BigOInv (fun S => Real.exp (-(phi_S S (1 + eps_S S)))) (fun _ => 1) 2 := by
  obtain ⟨C, S₀, hS₀_pos, hbd⟩ := phi_S_boundary_small
  refine ⟨C, max S₀ 1, lt_max_of_lt_right one_pos, ?_⟩
  intro S hS
  have hS₀_le : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hS_one : 1 ≤ S := le_trans (le_max_right _ _) hS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  -- `phi_S(1+ε_S) ≥ 0`.
  have h_phi_nn : 0 ≤ phi_S S (1 + eps_S S) := by
    have hq := phi_S_quadratic_lower hSpos (1 + eps_S S)
    have h_eta_nn : 0 ≤ eta_S S := (eta_S_pos hSpos).le
    have h_quad_nn : 0 ≤ eta_S S * (1 + eps_S S) ^ 2 / 2 := by
      have hsq : 0 ≤ (1 + eps_S S) ^ 2 := sq_nonneg _
      have := mul_nonneg h_eta_nn hsq
      linarith
    linarith
  -- `1 - exp(-v) ≤ v` for `v ≥ 0`.
  have hone_sub_le := (one_sub_exp_neg_le (phi_S S (1 + eps_S S)) h_phi_nn).2
  -- `exp(-v) - 1 = -(1 - exp(-v))`.
  -- `|exp(-v) - 1| = 1 - exp(-v)` (since `exp(-v) ≤ 1`).
  have hexp_le_one : Real.exp (-(phi_S S (1 + eps_S S))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [h_phi_nn])
  have habs_eq : |Real.exp (-(phi_S S (1 + eps_S S))) - 1|
               = 1 - Real.exp (-(phi_S S (1 + eps_S S))) := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  rw [habs_eq]
  -- `1 - exp(-phi_S) ≤ phi_S ≤ C * S^-2`.
  have hphi_bd := hbd S hS₀_le
  -- hphi_bd : |phi_S S (1 + eps_S S) - 0| ≤ C * S^(-(2:ℤ))
  have hphi_le : phi_S S (1 + eps_S S) ≤ C * S ^ (-((2 : ℕ) : ℤ)) := by
    have : |phi_S S (1 + eps_S S) - (fun _ => (0 : ℝ)) S|
            ≤ C * S ^ (-((2 : ℕ) : ℤ)) := hphi_bd
    simp only at this
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ phi_S S (1 + eps_S S) - 0)] at this
    linarith
  linarith [hone_sub_le, hphi_le]

/-! ## Lemma (a): right-tail integral asymptotic

`tailInt_S = 1/S + O(S^{-3})`. -/

/-- `tailInt_S S = 1/S + O(S^{-3})`. Combines:
* `tailInt_S_tail_eq`: `tailInt_S = exp(-φ_S(1+ε)) · I` where I is the
  Gaussian-tail integral;
* `tail_gaussian_bound`: `0 ≤ 1/S̃ - I ≤ η/S̃³`;
* `one_div_tildeS_asymp`: `|1/S̃ - 1/S| ≤ 2/S^6`;
* `exp_neg_phi_boundary_asymp`: `|exp(-φ_S(1+ε)) - 1| ≤ C/S²`. -/
theorem tailInt_S_asymp : BigOInv tailInt_S (fun S => 1 / S) 3 := by
  obtain ⟨C_φ, S_φ, hS_φ_pos, h_φ_bd⟩ := exp_neg_phi_boundary_asymp
  obtain ⟨C_oot, S_oot, hS_oot_pos, h_oot_bd⟩ := one_div_tildeS_asymp
  -- C constant for the bound on |C_φ| nonnegativity (extracted from positive eval).
  have hC_φ_nn : 0 ≤ C_φ := by
    have h : |Real.exp (-(phi_S S_φ (1 + eps_S S_φ))) - 1|
        ≤ C_φ * S_φ ^ (-(2 : ℤ)) := h_φ_bd S_φ le_rfl
    have h_abs_nn : 0 ≤ |Real.exp (-(phi_S S_φ (1 + eps_S S_φ))) - 1| := abs_nonneg _
    have h_pow_pos : (0 : ℝ) < S_φ ^ (-(2 : ℤ)) := zpow_pos hS_φ_pos _
    nlinarith
  have hC_oot_nn : 0 ≤ C_oot := by
    have h : |1 / tildeS S_oot - 1 / S_oot| ≤ C_oot * S_oot ^ (-(6 : ℤ)) :=
      h_oot_bd S_oot le_rfl
    have h_abs_nn : 0 ≤ |1 / tildeS S_oot - 1 / S_oot| := abs_nonneg _
    have h_pow_pos : (0 : ℝ) < S_oot ^ (-(6 : ℤ)) := zpow_pos hS_oot_pos _
    nlinarith
  refine ⟨1 + C_φ + C_oot, max (max S_φ S_oot) 1,
          lt_max_of_lt_right one_pos, ?_⟩
  intro S hS
  have hS_φ : S_φ ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hS)
  have hS_oot : S_oot ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hS_one : (1 : ℝ) ≤ S := le_trans (le_max_right _ _) hS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  have htildeS_pos : 0 < tildeS S := tildeS_pos hS_one
  have hS_le_tildeS : S ≤ tildeS S := le_tildeS hS_one
  have heta_pos : 0 < eta_S S := eta_S_pos hSpos
  have hS3_pos : (0 : ℝ) < S^3 := by positivity
  have hS4_pos : (0 : ℝ) < S^4 := by positivity
  have hS6_pos : (0 : ℝ) < S^6 := by positivity
  have hS7_pos : (0 : ℝ) < S^7 := by positivity
  -- Convert S^(-k:ℤ) to 1/S^k.
  have h_S2_eq : (S : ℝ)^(-(2:ℤ)) = 1/S^2 := by
    rw [show (-(2:ℤ)) = -((2:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
  have h_S3_eq : (S : ℝ)^(-(3:ℤ)) = 1/S^3 := by
    rw [show (-(3:ℤ)) = -((3:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
  have h_S6_eq : (S : ℝ)^(-(6:ℤ)) = 1/S^6 := by
    rw [show (-(6:ℤ)) = -((6:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
  -- Apply tailInt_S_tail_eq.
  rw [tailInt_S_tail_eq S hS_one]
  set A := Real.exp (-(phi_S S (1 + eps_S S))) with hA_def
  set I := ∫ u in Set.Ici (0 : ℝ),
              Real.exp (-(tildeS S * u) - eta_S S * u ^ 2 / 2) with hI_def
  -- Bounds.
  have hA_bd_raw : |A - (fun _ : ℝ => (1 : ℝ)) S| ≤ C_φ * S^(-(2:ℤ)) :=
    h_φ_bd S hS_φ
  have hA_bd : |A - 1| ≤ C_φ * (1/S^2) := by
    rw [show (fun _ : ℝ => (1 : ℝ)) S = 1 from rfl, h_S2_eq] at hA_bd_raw
    exact hA_bd_raw
  have hr1_bd_raw : |1/tildeS S - 1/S| ≤ C_oot * S^(-(6:ℤ)) :=
    h_oot_bd S hS_oot
  have hr1_bd : |1/tildeS S - 1/S| ≤ C_oot * (1/S^6) := by
    rw [h_S6_eq] at hr1_bd_raw; exact hr1_bd_raw
  have ⟨h_diff_nn, h_diff_ub⟩ := tail_gaussian_bound S hS_one
  -- I ≥ 0 (integrand positive).
  have hI_nn : 0 ≤ I := by
    apply setIntegral_nonneg measurableSet_Ici
    intros u _
    exact (Real.exp_pos _).le
  -- I ≤ 1/tildeS (from the lower bound h_diff_nn).
  have hI_le_tilde : I ≤ 1/tildeS S := by linarith
  -- 1/tildeS ≤ 1/S.
  have h_tilde_le_S : 1/tildeS S ≤ 1/S := one_div_le_one_div_of_le hSpos hS_le_tildeS
  -- |I| ≤ 1/S.
  have hI_abs : |I| ≤ 1/S := by
    rw [abs_of_nonneg hI_nn]; linarith
  -- Decomposition.
  have h_decomp : A * I - 1/S
      = (A - 1) * I + (I - 1/tildeS S) + (1/tildeS S - 1/S) := by ring
  -- Triangle inequality.
  have h_tri : |A * I - 1/S|
      ≤ |A - 1| * |I| + |I - 1/tildeS S| + |1/tildeS S - 1/S| := by
    rw [h_decomp]
    have h1 := abs_add_le ((A - 1) * I + (I - 1/tildeS S)) (1/tildeS S - 1/S)
    have h2 := abs_add_le ((A - 1) * I) (I - 1/tildeS S)
    have h3 : |(A - 1) * I| = |A - 1| * |I| := abs_mul _ _
    linarith
  -- Bound 1: |A-1|·|I| ≤ (C_φ/S²)·(1/S) = C_φ/S³.
  have hbound1 : |A - 1| * |I| ≤ C_φ * (1/S^3) := by
    have h1 : |A - 1| * |I| ≤ (C_φ * (1/S^2)) * (1/S) := by
      refine mul_le_mul hA_bd hI_abs (abs_nonneg _) ?_
      have : (0 : ℝ) ≤ 1/S^2 := by positivity
      exact mul_nonneg hC_φ_nn this
    have h_eq : (C_φ * (1/S^2)) * (1/S) = C_φ * (1/S^3) := by
      have : (S : ℝ)^2 * S = S^3 := by ring
      field_simp
    linarith
  -- Bound 2: |I - 1/tildeS| ≤ 1/S^3.
  -- |I - 1/tildeS| = 1/tildeS - I ≤ eta/tildeS^3 = (1/S^4)/tildeS^3 ≤ 1/S^7 ≤ 1/S^3.
  have hbound2 : |I - 1/tildeS S| ≤ 1/S^3 := by
    -- |I - 1/tildeS| = 1/tildeS - I
    have h_abs_eq : |I - 1/tildeS S| = 1/tildeS S - I := by
      rw [show I - 1/tildeS S = -(1/tildeS S - I) from by ring, abs_neg,
          abs_of_nonneg h_diff_nn]
    -- ≤ eta/tildeS^3
    have h_le_eta : 1/tildeS S - I ≤ eta_S S / tildeS S^3 := h_diff_ub
    -- eta_S S = 1/S^4
    have h_eta_eq : eta_S S = 1/S^4 := by
      unfold eta_S
      rw [show (-(4:ℤ)) = -((4:ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, one_div]
    -- 1/S^4 / tildeS^3 ≤ 1/S^7
    have htildeS3_pos : (0 : ℝ) < tildeS S ^ 3 := by positivity
    have hS_le_tildeS_3 : S^3 ≤ tildeS S ^ 3 := by
      have h := pow_le_pow_left₀ hSpos.le hS_le_tildeS 3
      exact h
    have h_inv_le : (1 : ℝ)/(tildeS S ^ 3) ≤ 1/S^3 :=
      one_div_le_one_div_of_le hS3_pos hS_le_tildeS_3
    have h_eta_inv : eta_S S / tildeS S ^ 3 = (1/S^4) * (1/tildeS S^3) := by
      rw [h_eta_eq]
      field_simp
    have h_step1 : (1/S^4) * (1/tildeS S^3) ≤ (1/S^4) * (1/S^3) := by
      have : (0 : ℝ) ≤ 1/S^4 := by positivity
      exact mul_le_mul_of_nonneg_left h_inv_le this
    have h_step2 : (1/S^4) * (1/S^3) = 1/S^7 := by
      have h_eq : (S : ℝ)^4 * S^3 = S^7 := by ring
      field_simp
    have h_S7_le_S3 : (1 : ℝ)/S^7 ≤ 1/S^3 := by
      have hS_pow : S^3 ≤ S^7 := by
        have h_S3_pow : S^3 ≤ S^3 * S^4 := by
          have hS4_ge_one : (1 : ℝ) ≤ S^4 := one_le_pow₀ hS_one
          nlinarith
        have heq : S^3 * S^4 = S^7 := by ring
        linarith
      exact one_div_le_one_div_of_le hS3_pos hS_pow
    -- chain
    rw [h_abs_eq]
    calc 1/tildeS S - I ≤ eta_S S / tildeS S ^ 3 := h_le_eta
      _ = (1/S^4) * (1/tildeS S^3) := h_eta_inv
      _ ≤ (1/S^4) * (1/S^3) := h_step1
      _ = 1/S^7 := h_step2
      _ ≤ 1/S^3 := h_S7_le_S3
  -- Bound 3: |1/tildeS - 1/S| ≤ C_oot/S^6 ≤ C_oot/S^3.
  have hbound3 : |1/tildeS S - 1/S| ≤ C_oot * (1/S^3) := by
    refine le_trans hr1_bd ?_
    have h_S6_le_S3 : (1 : ℝ)/S^6 ≤ 1/S^3 := by
      have h_S3_pow : S^3 ≤ S^3 * S^3 := by
        have hS3_ge_one : (1 : ℝ) ≤ S^3 := one_le_pow₀ hS_one
        nlinarith
      have heq : S^3 * S^3 = S^6 := by ring
      have hS_pow : S^3 ≤ S^6 := by linarith
      exact one_div_le_one_div_of_le hS3_pos hS_pow
    exact mul_le_mul_of_nonneg_left h_S6_le_S3 hC_oot_nn
  -- Sum: |A·I - 1/S| ≤ (C_φ + 1 + C_oot) * (1/S^3) = (1 + C_φ + C_oot) * (1/S^3).
  have h_total : |A * I - 1/S| ≤ (1 + C_φ + C_oot) * (1/S^3) := by
    have : |A - 1| * |I| + |I - 1/tildeS S| + |1/tildeS S - 1/S|
         ≤ C_φ * (1/S^3) + 1/S^3 + C_oot * (1/S^3) := by linarith
    linarith [h_tri, this]
  -- Convert (1/S^3) back to S^(-3:ℤ).
  show |A * I - 1/S| ≤ (1 + C_φ + C_oot) * S^(-(3:ℤ))
  rw [h_S3_eq]
  exact h_total

/-! ## Lemma (b): normalisation constant asymptotic

`Z_S = 2 + 2/S + O(S^{-3})`. -/

axiom Z_S_asymp :
    BigOInv Z_S (fun S => 2 + 2 / S) 3

/-! ## Lemma (c): tail probability and layer mass

`q_S = 1/S - 1/S^2 + O(S^{-3})`  and  `t_S = O(S^{-3})`. -/

-- `q_S_asymp` and `t_S_asymp` are *proven* (not axiomatised); see the
-- end of this file. Their proofs depend on `exists_S_Z_S_ge_one`,
-- hence the placement.

/-! ## Derived corollaries

For downstream modules the main facts needed are:

* `Z_S S ≥ 1` for sufficiently large `S` (used to invert `Z_S`);
* `q_S S → 0`, `t_S S → 0` as `S → ∞` (used to derive contradictions).

These follow from the asymptotic lemmas above by elementary real arithmetic.
-/

lemma exists_S_Z_S_ge_one : ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → 1 ≤ Z_S S := by
  obtain ⟨C, S₁, hS₁, hbd⟩ := Z_S_asymp
  refine ⟨max S₁ (max 2 (2 * C + 2)), ?_, ?_⟩
  · exact lt_max_of_lt_right (lt_max_of_lt_left (by norm_num))
  intro S hS
  have hS₁le : S₁ ≤ S := le_trans (le_max_left _ _) hS
  have hS2 : (2 : ℝ) ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hS2
  have hSlarge : 2 * C + 2 ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hb := hbd S hS₁le
  have habs : |Z_S S - (2 + 2 / S)| ≤ C * S ^ (-(3 : ℤ)) := hb
  have hpow : S ^ (-(3 : ℤ)) = 1 / S ^ 3 := zpow_negNat S 3 hSpos.ne'
  rw [hpow] at habs
  have hinvS_nn : 0 ≤ 2 / S := by positivity
  have hZlb : 2 + 2 / S - C * (1 / S ^ 3) ≤ Z_S S := by
    have := (abs_sub_le_iff.1 habs).2
    linarith
  have hS3_pos : 0 < S ^ 3 := by positivity
  have hC_bd : C * (1 / S ^ 3) ≤ 1 := by
    by_cases hC : C ≤ 0
    · calc C * (1 / S ^ 3) ≤ 0 := by
            have : 0 ≤ 1 / S ^ 3 := by positivity
            nlinarith
          _ ≤ 1 := by norm_num
    · push_neg at hC
      have hSgeC : C ≤ S := by linarith
      have hSS : S ≤ S ^ 3 := by
        have h1 : 1 ≤ S := le_trans (by norm_num) hS2
        have hSpow : S ^ 1 ≤ S ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
        simpa using hSpow
      have hCleS3 : C ≤ S ^ 3 := le_trans hSgeC hSS
      have hrecip : C / S ^ 3 ≤ 1 := by
        rw [div_le_one hS3_pos]; exact hCleS3
      calc C * (1 / S ^ 3) = C / S ^ 3 := by ring
        _ ≤ 1 := hrecip
  linarith

/-! `exists_S_q_S_lt_one` (which uses `q_S_asymp`) is proven at the
end of the file, after `q_S_asymp` itself. -/

/-! ## Sanity: the four constants are well-defined reals. -/

example (S : ℝ) : Z_S S = ∫ x, Real.exp (-(phi_S S x)) := rfl
example (S : ℝ) : tailInt_S S = ∫ x in Set.Ici (1 + eps_S S), Real.exp (-(phi_S S x)) := rfl
example (S : ℝ) : q_S S = 2 * tailInt_S S / Z_S S := rfl

/-! ## Proofs of `q_S_asymp` and `t_S_asymp`

These two BigOInv statements depend on `exists_S_Z_S_ge_one`, hence
their proofs sit at the end of the file. -/

/-- `q_S = 1/S − 1/S² + O(S⁻³)`. Derived from `tailInt_S_asymp` and
`Z_S_asymp` plus the algebraic identity
`q_S − (1/S − 1/S²) = −((1/S − 1/S²) · Z_S − 2·tailInt_S) / Z_S`. -/
theorem q_S_asymp : BigOInv q_S (fun S => 1 / S - 1 / S ^ 2) 3 := by
  obtain ⟨C_Z, S_Z, hS_Z_pos, hZ_bd⟩ := Z_S_asymp
  obtain ⟨C_T, S_T, hS_T_pos, hT_bd⟩ := tailInt_S_asymp
  obtain ⟨S₀_Z, _hS₀_Z_pos, hZ_ge_one⟩ := exists_S_Z_S_ge_one
  refine ⟨2 + C_Z + 2 * C_T, max (max S_Z S_T) (max S₀_Z 1), ?_, ?_⟩
  · refine lt_max_of_lt_right (lt_max_of_lt_right one_pos)
  intro S hS
  have hS_Z_le : S_Z ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hS)
  have hS_T_le : S_T ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hS₀_Z_le : S₀_Z ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hS_one : 1 ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  have hZ_one : 1 ≤ Z_S S := hZ_ge_one S hS₀_Z_le
  have hZ_pos : 0 < Z_S S := lt_of_lt_of_le zero_lt_one hZ_one
  have hZ_ne : Z_S S ≠ 0 := hZ_pos.ne'
  -- Bounds on R_Z = Z_S - (2 + 2/S) and R_T = tailInt_S - 1/S.
  have h_pow_eq : S ^ (-((3 : ℕ) : ℤ)) = 1 / S ^ 3 :=
    zpow_negNat S 3 hSpos.ne'
  have hZ' : |Z_S S - (2 + 2 / S)| ≤ C_Z * (1 / S ^ 3) := by
    have := hZ_bd S hS_Z_le
    rwa [h_pow_eq] at this
  have hT' : |tailInt_S S - 1 / S| ≤ C_T * (1 / S ^ 3) := by
    have := hT_bd S hS_T_le
    rwa [h_pow_eq] at this
  -- Algebraic identity: q_S - (1/S - 1/S²) = -((1/S - 1/S²)·Z_S - 2·tailInt_S) / Z_S.
  have h_eq : q_S S - (1 / S - 1 / S ^ 2)
             = -((1 / S - 1 / S ^ 2) * Z_S S - 2 * tailInt_S S) / Z_S S := by
    unfold q_S
    have hSne : S ≠ 0 := hSpos.ne'
    field_simp
    ring
  -- Bound the numerator of the RHS by triangle inequality.
  -- (1/S - 1/S²)·Z_S - 2·tailInt_S
  -- = (1/S - 1/S²)·(2 + 2/S + (Z_S - (2 + 2/S))) - 2·(1/S + (tailInt_S - 1/S))
  -- = -2/S³ + (1/S - 1/S²)·R_Z - 2·R_T.
  set RZ := Z_S S - (2 + 2 / S) with hRZ_def
  set RT := tailInt_S S - 1 / S with hRT_def
  have h_num_eq :
      (1 / S - 1 / S ^ 2) * Z_S S - 2 * tailInt_S S
        = -(2 / S ^ 3) + (1 / S - 1 / S ^ 2) * RZ - 2 * RT := by
    rw [hRZ_def, hRT_def]
    have hSne : S ≠ 0 := hSpos.ne'
    field_simp
    ring
  rw [h_pow_eq, h_eq]
  -- Goal: |−num/Z_S| ≤ (2 + C_Z + 2 C_T) * (1/S³).
  rw [abs_div, abs_neg, abs_of_pos hZ_pos]
  rw [div_le_iff₀ hZ_pos]
  rw [h_num_eq]
  -- |−2/S³ + (1/S − 1/S²)·RZ − 2·RT|
  -- ≤ 2/S³ + |1/S − 1/S²|·|RZ| + 2·|RT|
  -- ≤ 2/S³ + 1·C_Z/S³ + 2·C_T/S³ = (2 + C_Z + 2 C_T)/S³.
  have h_tri₁ :
      |(-(2 / S ^ 3)) + (1 / S - 1 / S ^ 2) * RZ - 2 * RT|
        ≤ |(-(2 / S ^ 3)) + (1 / S - 1 / S ^ 2) * RZ| + |2 * RT| := abs_sub _ _
  have h_tri₂ :
      |(-(2 / S ^ 3)) + (1 / S - 1 / S ^ 2) * RZ|
        ≤ |(-(2 / S ^ 3))| + |(1 / S - 1 / S ^ 2) * RZ| := abs_add_le _ _
  have h_abs_2_S3 : |(-(2 : ℝ) / S ^ 3)| = 2 / S ^ 3 := by
    rw [neg_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 / S^3)]
  have h_abs_2_S3' : |(-((2 : ℝ) / S ^ 3))| = 2 / S ^ 3 := by
    rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 / S^3)]
  have h_abs_RZ : |(1 / S - 1 / S ^ 2) * RZ| ≤ C_Z * (1 / S ^ 3) := by
    rw [abs_mul]
    have h_abs_diff : |(1 : ℝ) / S - 1 / S ^ 2| ≤ 1 := by
      have h1 : (0 : ℝ) < 1 / S := by positivity
      have h2 : (0 : ℝ) < 1 / S ^ 2 := by positivity
      have h3 : (1 : ℝ) / S ≤ 1 := by
        rw [div_le_one hSpos]; exact hS_one
      have h4 : (1 : ℝ) / S ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      have h5 : (1 / S - 1 / S^2 : ℝ) ≤ 1 := by linarith
      have h6 : (-1 : ℝ) ≤ 1 / S - 1 / S^2 := by linarith
      rw [abs_le]; exact ⟨h6, h5⟩
    have hRZ_pos : (0 : ℝ) ≤ |RZ| := abs_nonneg _
    have hh : |(1 / S - (1 : ℝ) / S^2)| * |RZ| ≤ 1 * (C_Z * (1 / S^3)) := by
      apply mul_le_mul h_abs_diff hZ' hRZ_pos
      linarith
    linarith
  have h_abs_RT : |(2 : ℝ) * RT| ≤ 2 * (C_T * (1 / S ^ 3)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [hT']
  -- Combine.
  have h_total : |(-(2 / S ^ 3)) + (1 / S - 1 / S ^ 2) * RZ - 2 * RT|
                  ≤ 2 / S ^ 3 + C_Z * (1 / S ^ 3) + 2 * (C_T * (1 / S ^ 3)) := by
    calc |(-(2 / S ^ 3)) + (1 / S - 1 / S ^ 2) * RZ - 2 * RT|
        ≤ |(-(2 / S ^ 3)) + (1 / S - 1 / S ^ 2) * RZ| + |2 * RT| := h_tri₁
      _ ≤ (|(-(2 / S ^ 3))| + |(1 / S - 1 / S ^ 2) * RZ|) + |2 * RT| := by
          linarith [h_tri₂]
      _ = (2/S^3 + |(1 / S - 1 / S ^ 2) * RZ|) + |2 * RT| := by rw [h_abs_2_S3']
      _ ≤ (2/S^3 + C_Z * (1/S^3)) + 2 * (C_T * (1/S^3)) := by linarith
  -- Compare with (2 + C_Z + 2 C_T) * (1/S^3) * Z_S.
  have h_RHS_eq :
      (2 + C_Z + 2 * C_T) * (1 / S ^ 3)
        = 2 / S ^ 3 + C_Z * (1 / S ^ 3) + 2 * (C_T * (1 / S ^ 3)) := by ring
  -- Goal: |...| ≤ (2 + C_Z + 2 C_T) * (1/S^3) * Z_S.
  have h_RHS_ge :
      (2 + C_Z + 2 * C_T) * (1 / S ^ 3)
        ≤ (2 + C_Z + 2 * C_T) * (1 / S ^ 3) * Z_S S := by
    have h_nn : 0 ≤ (2 + C_Z + 2 * C_T) * (1 / S ^ 3) := by
      -- We need (2 + C_Z + 2 C_T) ≥ 0. This requires C_Z, C_T ≥ 0.
      -- C_Z ≥ 0 from BigOInv (axiom values are nonneg).
      -- We could deduce this, but it's also OK if not — adjust constant.
      -- Let's use ‖(2 + C_Z + 2 C_T)/S^3 * Z_S‖ ≥ ... instead.
      -- For simplicity: max with 0.
      have h_S3_pos : (0 : ℝ) < 1 / S^3 := by positivity
      -- We need (2 + C_Z + 2 C_T) ≥ 0.
      -- Derive C_Z ≥ 0 from `|... | ≤ C_Z * S^(-3)` at S = S_Z (already showed
      -- earlier this trick).
      have hCZ_nn : 0 ≤ C_Z := by
        have hb := hZ_bd S_Z le_rfl
        have habs_nn : (0 : ℝ) ≤ |Z_S S_Z - (fun S => 2 + 2/S) S_Z| := abs_nonneg _
        have hpow_pos : (0 : ℝ) < S_Z ^ (-((3 : ℕ) : ℤ)) :=
          zpow_pos hS_Z_pos _
        by_contra hneg
        push_neg at hneg
        have hprod : C_Z * S_Z ^ (-((3 : ℕ) : ℤ)) < 0 :=
          mul_neg_of_neg_of_pos hneg hpow_pos
        exact absurd (le_trans habs_nn hb) (not_le_of_gt hprod)
      have hCT_nn : 0 ≤ C_T := by
        have hb := hT_bd S_T le_rfl
        have habs_nn : (0 : ℝ) ≤ |tailInt_S S_T - (fun S => 1/S) S_T| :=
          abs_nonneg _
        have hpow_pos : (0 : ℝ) < S_T ^ (-((3 : ℕ) : ℤ)) :=
          zpow_pos hS_T_pos _
        by_contra hneg
        push_neg at hneg
        have hprod : C_T * S_T ^ (-((3 : ℕ) : ℤ)) < 0 :=
          mul_neg_of_neg_of_pos hneg hpow_pos
        exact absurd (le_trans habs_nn hb) (not_le_of_gt hprod)
      have hsum_nn : 0 ≤ 2 + C_Z + 2 * C_T := by linarith
      exact mul_nonneg hsum_nn h_S3_pos.le
    nlinarith [h_nn, hZ_one]
  linarith [h_RHS_eq, h_RHS_ge, h_total]

/-! ## Proof of `t_S_asymp`

`t_S = O(S^{-3})`. From `t_S = (∫_{T_S} exp(−φ_S)) / Z_S` and the
bounds `∫_{T_S} exp(−φ_S) ≤ vol(T_S) ≤ 4·ε_S = 4·S^{-3}` (using
`exp(−φ_S) ≤ 1` because `φ_S ≥ 0`) and `Z_S ≥ 1` eventually
(from `exists_S_Z_S_ge_one`), we get `t_S ≤ 4·S^{-3}`. -/
theorem t_S_asymp : BigOInv t_S (fun _ => 0) 3 := by
  obtain ⟨S₀_Z, _hS₀_Z_pos, hZ_ge_one⟩ := exists_S_Z_S_ge_one
  refine ⟨4, max S₀_Z 1, lt_max_of_lt_right one_pos, ?_⟩
  intro S hS
  have hS_Z : S₀_Z ≤ S := le_trans (le_max_left _ _) hS
  have hS_one : 1 ≤ S := le_trans (le_max_right _ _) hS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  have hZ_one : 1 ≤ Z_S S := hZ_ge_one S hS_Z
  have hZ_pos : 0 < Z_S S := lt_of_lt_of_le zero_lt_one hZ_one
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have ht_nn : 0 ≤ t_S S := t_S_nonneg S hSpos
  simp only [sub_zero]
  rw [abs_of_nonneg ht_nn]
  -- `phi_S(x) ≥ 0`, so `exp(-phi_S(x)) ≤ 1`.
  have h_phi_nn : ∀ x, 0 ≤ phi_S S x := by
    intro x
    have hq := phi_S_quadratic_lower hSpos x
    have h_eta_nn : 0 ≤ eta_S S := (eta_S_pos hSpos).le
    have h_quad_nn : 0 ≤ eta_S S * x ^ 2 / 2 := by
      have hx2 : 0 ≤ x ^ 2 := sq_nonneg _
      have := mul_nonneg h_eta_nn hx2
      linarith
    linarith
  have h_exp_le : ∀ x, ‖Real.exp (-(phi_S S x))‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith [h_phi_nn x])
  -- `vol(T_S) ≤ 4·ε_S`.
  have h_vol_neg :
      volume.real (Set.Icc (-1 - eps_S S) (-1 + eps_S S)) = 2 * eps_S S := by
    rw [Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [heps_pos.le])]
    ring
  have h_vol_pos :
      volume.real (Set.Icc (1 - eps_S S) (1 + eps_S S)) = 2 * eps_S S := by
    rw [Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [heps_pos.le])]
    ring
  have h_vol_TS : volume.real (T_S S) ≤ 4 * eps_S S := by
    have h_union := measureReal_union_le (μ := volume)
      (Set.Icc (-1 - eps_S S) (-1 + eps_S S))
      (Set.Icc (1 - eps_S S) (1 + eps_S S))
    rw [show T_S S = Set.Icc (-1 - eps_S S) (-1 + eps_S S) ∪
                      Set.Icc (1 - eps_S S) (1 + eps_S S) from rfl]
    linarith [h_vol_neg, h_vol_pos]
  -- `T_S` has finite measure.
  have h_T_meas_lt_top : volume (T_S S) < ⊤ := by
    have h_sub : T_S S ⊆ Set.Icc (-1 - eps_S S) (1 + eps_S S) := by
      intro x hx
      rcases hx with hx | hx
      · refine ⟨hx.1, ?_⟩
        have := hx.2
        linarith
      · refine ⟨?_, hx.2⟩
        have := hx.1
        linarith
    calc volume (T_S S) ≤ volume (Set.Icc (-1 - eps_S S) (1 + eps_S S)) :=
          measure_mono h_sub
      _ = ENNReal.ofReal ((1 + eps_S S) - (-1 - eps_S S)) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- Bound the set integral by `1 · vol(T_S)`.
  have h_int_bound :
      ‖∫ x in T_S S, Real.exp (-(phi_S S x))‖ ≤ 1 * volume.real (T_S S) :=
    norm_setIntegral_le_of_norm_le_const h_T_meas_lt_top (fun x _ => h_exp_le x)
  have h_T_meas : MeasurableSet (T_S S) :=
    measurableSet_Icc.union measurableSet_Icc
  have h_int_nn : 0 ≤ ∫ x in T_S S, Real.exp (-(phi_S S x)) :=
    setIntegral_nonneg h_T_meas (fun x _ => (Real.exp_pos _).le)
  -- Convert to `t_S ≤ 4 · S^{-3}` where the ℝ-power is `eps_S S`.
  show t_S S ≤ 4 * S ^ (-((3 : ℕ) : ℤ))
  have h_pow_eq : S ^ (-((3 : ℕ) : ℤ)) = eps_S S := by
    show S ^ (-(((3 : ℕ) : ℤ))) = S ^ (-(3 : ℤ))
    rfl
  rw [h_pow_eq]
  unfold t_S
  rw [div_le_iff₀ hZ_pos]
  have h_num_le : (∫ x in T_S S, Real.exp (-(phi_S S x))) ≤ 4 * eps_S S := by
    have hb := h_int_bound
    rw [Real.norm_eq_abs, abs_of_nonneg h_int_nn, one_mul] at hb
    linarith
  have h_4eps_nn : 0 ≤ 4 * eps_S S := by linarith [heps_pos.le]
  calc (∫ x in T_S S, Real.exp (-(phi_S S x)))
      ≤ 4 * eps_S S := h_num_le
    _ = 4 * eps_S S * 1 := by ring
    _ ≤ 4 * eps_S S * Z_S S :=
        mul_le_mul_of_nonneg_left hZ_one h_4eps_nn

/-- For sufficiently large `S`, `q_S S < 1` (the tail probability is bounded
away from `1`).  This is used downstream to derive nontrivial mass on the
core. -/
lemma exists_S_q_S_lt_one : ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → q_S S < 1 := by
  obtain ⟨C, S₁, hS₁, hbd⟩ := q_S_asymp
  refine ⟨max S₁ (max 2 (max (2 * |C| + 2) 4)), ?_, ?_⟩
  · refine lt_max_of_lt_right (lt_max_of_lt_left ?_); norm_num
  intro S hS
  have hS₁le : S₁ ≤ S := le_trans (le_max_left _ _) hS
  have hS2 : (2 : ℝ) ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hS2
  have hb' := hbd S hS₁le
  have hb : |q_S S - (1 / S - 1 / S ^ 2)| ≤ C * S ^ (-(3 : ℤ)) := hb'
  have hpow : S ^ (-(3 : ℤ)) = 1 / S ^ 3 := zpow_negNat S 3 hSpos.ne'
  rw [hpow] at hb
  have hupper := (abs_sub_le_iff.1 hb).1
  have hS3_pos : 0 < S ^ 3 := by positivity
  have hSge4 : (4:ℝ) ≤ S :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS))
  have hSge2C : 2 * |C| + 2 ≤ S :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS))
  -- 1/S ≤ 1/4
  have h_one_S' : (1:ℝ) / S ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hSpos (by norm_num : (0:ℝ) < 4)]; linarith
  -- |C|/S^3 ≤ 1/2.
  have habs_C_S3_bd : |C| / S ^ 3 ≤ 1 / 2 := by
    have habs_nn : 0 ≤ |C| := abs_nonneg _
    have hS_ge_C : |C| ≤ S := by linarith
    have hS3_ge_S : S ≤ S ^ 3 := by nlinarith
    have hS3_ge_2C2 : 2 * |C| + 2 ≤ S ^ 3 := le_trans hSge2C hS3_ge_S
    rw [div_le_div_iff₀ hS3_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith
  -- 1/S² ≥ 0
  have hS2sq_pos : 0 < S ^ 2 := by positivity
  have h_invS2_nn : 0 ≤ (1:ℝ) / S ^ 2 := by positivity
  have h_C_S3 : C * (1 / S ^ 3) ≤ |C| * (1 / S ^ 3) := by
    have : 0 ≤ 1 / S ^ 3 := by positivity
    nlinarith [le_abs_self C]
  -- Combine
  have q_le : q_S S ≤ 1 / S - 1 / S ^ 2 + C * (1 / S ^ 3) := by linarith
  have h_lhs_bd : 1 / S - 1 / S ^ 2 + C * (1 / S ^ 3)
        ≤ 1 / S + |C| * (1 / S ^ 3) := by linarith
  have h_lhs_bd' : 1 / S + |C| * (1 / S ^ 3) ≤ 1 / 4 + 1 / 2 := by
    have h_abs_eq : |C| * (1 / S ^ 3) = |C| / S ^ 3 := by ring
    rw [h_abs_eq]
    linarith
  linarith

end L2Counterexample

end
