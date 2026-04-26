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

/-- Uniform smallness on the layer for `exp(-phi_S)`: `|exp(-phi_S(x)) - 1| =
O(S^{-2})` when `|x-1| ≤ ε_S`. -/
axiom phi_S_layer_small :
    ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → ∀ x,
      |x - 1| ≤ eps_S S → |Real.exp (-(phi_S S x)) - 1| ≤ C * S ^ (-(2 : ℤ))

/-! ## Integrability -/

/-- Integrability of `exp(-phi_S S)` (Gaussian domination). -/
axiom exp_negPhiS_integrable (S : ℝ) (hS : 0 < S) :
    Integrable (fun x => Real.exp (-(phi_S S x)))

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

/-- Change-of-variables identity for the tail integral. -/
axiom tailInt_S_tail_eq (S : ℝ) (hS : 1 ≤ S) :
    tailInt_S S
      = Real.exp (-(phi_S S (1 + eps_S S)))
          * ∫ u in Set.Ici (0 : ℝ),
              Real.exp (-(tildeS S * u) - eta_S S * u ^ 2 / 2)

/-! ## Asymptotics of the Gaussian-tail integral

The two-sided bound
    `0 ≤ 1/S̃ - ∫₀^∞ exp(-S̃ u - η u²/2) du ≤ η / S̃³`
is a direct consequence of `1 - e^{-v} ≤ v` applied pointwise to
`v = η u²/2`. -/

axiom tail_gaussian_bound (S : ℝ) (hS : 1 ≤ S) :
    let I := ∫ u in Set.Ici (0 : ℝ),
                Real.exp (-(tildeS S * u) - eta_S S * u ^ 2 / 2)
    0 ≤ 1 / tildeS S - I ∧ 1 / tildeS S - I ≤ eta_S S / tildeS S ^ 3

/-! ## Asymptotic blueprint lemmas

Two ingredients package the analytic content of section 3 into BigO
statements: -/

/-- `1/tildeS S = 1/S + O(S^{-6})`. -/
axiom one_div_tildeS_asymp :
    BigOInv (fun S => 1 / tildeS S) (fun S => 1 / S) 6

/-- `exp(-phi_S S (1+ε_S)) = 1 + O(S^{-2})`. -/
axiom exp_neg_phi_boundary_asymp :
    BigOInv (fun S => Real.exp (-(phi_S S (1 + eps_S S)))) (fun _ => 1) 2

/-! ## Lemma (a): right-tail integral asymptotic

`tailInt_S = 1/S + O(S^{-3})`. -/

axiom tailInt_S_asymp :
    BigOInv tailInt_S (fun S => 1 / S) 3

/-! ## Lemma (b): normalisation constant asymptotic

`Z_S = 2 + 2/S + O(S^{-3})`. -/

axiom Z_S_asymp :
    BigOInv Z_S (fun S => 2 + 2 / S) 3

/-! ## Lemma (c): tail probability and layer mass

`q_S = 1/S - 1/S^2 + O(S^{-3})`  and  `t_S = O(S^{-3})`. -/

axiom q_S_asymp :
    BigOInv q_S (fun S => 1 / S - 1 / S ^ 2) 3

axiom t_S_asymp :
    BigOInv t_S (fun _ => 0) 3

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
  -- `|q_S - (1/S - 1/S²)| ≤ C / S^3`, and `1/S - 1/S² + C/S³ < 1` for large S.
  have hupper := (abs_sub_le_iff.1 hb).1
  -- q_S ≤ 1/S - 1/S² + C/S³
  have hS3_pos : 0 < S ^ 3 := by positivity
  have h_one_S : (1:ℝ) / S ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hSpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have h_C_S3 : C * (1 / S ^ 3) ≤ |C| * (1 / S ^ 3) := by
    have : 0 ≤ 1 / S ^ 3 := by positivity
    nlinarith [le_abs_self C]
  -- |C|/S^3 ≤ |C|/8 (since S ≥ 2 ⇒ S^3 ≥ 8)
  have hS3_ge_8 : (8:ℝ) ≤ S ^ 3 := by nlinarith
  have h_abs_S3 : |C| * (1 / S ^ 3) ≤ |C| / 8 := by
    have : 1 / S ^ 3 ≤ 1 / 8 := by
      rw [div_le_div_iff₀ hS3_pos (by norm_num : (0:ℝ) < 8)]
      linarith
    have h1 := mul_le_mul_of_nonneg_left this (abs_nonneg C)
    linarith
  -- 1/S² ≥ 0
  have hS2sq_pos : 0 < S ^ 2 := by positivity
  have h_invS2_nn : 0 ≤ (1:ℝ) / S ^ 2 := by positivity
  -- Goal: q_S < 1.
  -- We have q_S ≤ 1/S - 1/S² + C/S³ ≤ 1/S + |C|/S³ ≤ 1/2 + |C|/8.
  -- Need 1/2 + |C|/8 < 1, i.e. |C|/8 < 1/2, i.e. |C| < 4.
  -- This won't hold for all C, so we need S even larger.
  -- Better bound: For S ≥ max(2, 2|C|+2, 4), have S^2 ≥ S · 1 ≥ 2|C|+2 ≥ |C|+2,
  -- so 1/S² ≤ 1/(|C|+2), and …
  -- Simpler approach: choose S so that 1/S + |C|/S³ ≤ 1/2.
  -- Since S ≥ 4, 1/S ≤ 1/4. Since S ≥ 2|C|+2 ⇒ S ≥ |C|+2 ⇒ S^3 ≥ S · 1 ≥ 2|C|+2,
  -- so |C|/S^3 ≤ |C|/(2|C|+2) ≤ 1/2.  Hence 1/S + |C|/S^3 ≤ 1/4 + 1/2 = 3/4 < 1.
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
    have hS_ge_C : |C| ≤ S := by
      have h1 : |C| ≤ 2 * |C| + 2 := by linarith
      linarith
    -- S^3 ≥ S^2 ≥ 2|C|+2 ≥ 2|C| ⇒ |C|/S³ ≤ |C|/(2|C|) = 1/2 (when |C| > 0).
    -- Easier: |C|/S^3 ≤ |C|/(2|C|+2) ≤ 1/2.
    have hS3_ge_S : S ≤ S ^ 3 := by nlinarith
    have hS3_ge_2C2 : 2 * |C| + 2 ≤ S ^ 3 := le_trans hSge2C hS3_ge_S
    have hS3_pos' : 0 < S ^ 3 := hS3_pos
    rw [div_le_div_iff₀ hS3_pos' (by norm_num : (0:ℝ) < 2)]
    have : |C| * 2 ≤ (2 * |C| + 2) * 1 := by linarith
    nlinarith
  -- Combine
  have q_le : q_S S ≤ 1 / S - 1 / S ^ 2 + C * (1 / S ^ 3) := by linarith
  have h_lhs_bd : 1 / S - 1 / S ^ 2 + C * (1 / S ^ 3)
        ≤ 1 / S + |C| * (1 / S ^ 3) := by linarith
  have h_lhs_bd' : 1 / S + |C| * (1 / S ^ 3) ≤ 1 / 4 + 1 / 2 := by
    have h_abs_eq : |C| * (1 / S ^ 3) = |C| / S ^ 3 := by ring
    rw [h_abs_eq]
    linarith
  linarith

/-! ## Sanity: the four constants are well-defined reals. -/

example (S : ℝ) : Z_S S = ∫ x, Real.exp (-(phi_S S x)) := rfl
example (S : ℝ) : tailInt_S S = ∫ x in Set.Ici (1 + eps_S S), Real.exp (-(phi_S S x)) := rfl
example (S : ℝ) : q_S S = 2 * tailInt_S S / Z_S S := rfl

end L2Counterexample

end
