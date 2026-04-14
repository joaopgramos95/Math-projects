import QuantitativePR.Imported.RademacherTools

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace QuantitativePR

axiom exists_linear_probe
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξ : Ω → ℝ) (A : ℝ)
    (hmean : ∫ ω, ξ ω ∂μ = 0)
    (hl1 : A ≤ ∫ ω, |ξ ω| ∂μ) :
    ∃ S : Ω → ℝ,
      AEStronglyMeasurable S μ ∧
      (∫ ω, S ω ∂μ = 0) ∧
      (∫ ω, ξ ω * S ω ∂μ = 1) ∧
      (∀ᵐ ω ∂μ, |S ω| ≤ 2 / A)

axiom exists_quadratic_probe
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξ : Ω → ℝ) (B : ℝ)
    (hmean : ∫ ω, ξ ω ∂μ = 0)
    (hl2 : ∫ ω, ξ ω ^ (2 : ℕ) ∂μ = 1)
    (hl1_upper : ∫ ω, |ξ ω| ∂μ ≤ B)
    (hB : B < 1) :
    ∃ T : Ω → ℝ,
      AEStronglyMeasurable T μ ∧
      (∫ ω, T ω ∂μ = 0) ∧
      (∫ ω, (ξ ω ^ (2 : ℕ) - 1) * T ω ∂μ = 1) ∧
      (∀ᵐ ω ∂μ, |T ω| ≤ 2 / (1 - B))

theorem probe_entry_bound_constant (A B : ℝ) :
    max ((2 / A) ^ (2 : ℕ)) (2 / (1 - B)) ≤ K A B := by
  unfold K
  refine max_le_iff.mpr ?_
  constructor
  · have hsq : (2 / A) ^ (2 : ℕ) = 4 / A ^ (2 : ℕ) := by
      ring
    exact hsq ▸ le_max_left (4 / A ^ (2 : ℕ)) (2 / (1 - B))
  · exact le_max_right (4 / A ^ (2 : ℕ)) (2 / (1 - B))

axiom finite_indep_sum_l1_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (ζ : Fin n → Ω → ℝ) (c : Fin n → ℝ)
    (A : ℝ) :
    (A / (2 * Real.sqrt 2)) * Real.sqrt (∑ i, c i ^ (2 : ℕ))
      ≤ randL1Norm μ (fun ω => ∑ i, c i * ζ i ω)

axiom indep_sum_l1_lower
    {A B : ℝ} (qd : QuantitativeData A B)
    (c : ℕ → ℝ)
    (hc : Summable fun i => c i ^ (2 : ℕ)) :
    letI := qd.mΩ
    (A / (2 * Real.sqrt 2)) * coeffL2Norm c ≤ randL1Norm qd.μ (linComb qd c)

axiom two_sided_mass_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {U : Ω → ℝ} (m σ : ℝ)
    (hmean : ∫ ω, U ω ∂μ = 0)
    (hl2 : randL2Norm μ U = σ)
    (hl1 : m * σ ≤ randL1Norm μ U)
    (hm : 0 < m) :
    smallBallMass μ U ((m / 4) * σ) ((m / 4) * σ) ≥ m ^ (2 : ℕ) / 16

axiom projected_sum_two_sided_mass
    {A B : ℝ} (qd : QuantitativeData A B)
    (c : ℕ → ℝ)
    (hc : Summable fun i => c i ^ (2 : ℕ)) :
    letI := qd.mΩ
    smallBallMass qd.μ (linComb qd c) ((A / (8 * Real.sqrt 2)) * coeffL2Norm c)
      ((A / (8 * Real.sqrt 2)) * coeffL2Norm c) ≥ A ^ (2 : ℕ) / 128

end QuantitativePR
