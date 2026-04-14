import QuantitativePR.Main.UniformAB

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace QuantitativePR.Showcase

structure Data (A B : ℝ) where
  Ω : Type*
  mΩ : MeasurableSpace Ω
  μ : Measure Ω
  ξ : ℕ → Ω → ℝ
  aestronglyMeasurable : ∀ i, AEStronglyMeasurable (ξ i) μ
  indep : Pairwise (fun i j => IndepFun (ξ i) (ξ j) μ)
  mean_zero : ∀ i, ∫ ω, ξ i ω ∂μ = 0
  second_moment : ∀ i, ∫ ω, (ξ i ω) ^ (2 : ℕ) ∂μ = 1
  l1_lower : ∀ i, A ≤ ∫ ω, |ξ i ω| ∂μ
  l1_upper : ∀ i, ∫ ω, |ξ i ω| ∂μ ≤ B

def admissibleParameters (A B : ℝ) : Prop :=
  0 < A ∧ A ≤ B ∧ B < 1

def linComb {A B : ℝ} (data : Data A B) (c : ℕ → ℝ) : data.Ω → ℝ :=
  fun ω => ∑' i, c i * data.ξ i ω

def absGap {A B : ℝ} (data : Data A B) (a b : ℕ → ℝ) : data.Ω → ℝ :=
  fun ω => |linComb data a ω| - |linComb data b ω|

def phaseDistance (a b : ℕ → ℝ) : ℝ :=
  min (coeffL2Norm (fun i => a i - b i)) (coeffL2Norm (fun i => a i + b i))

def modulusGap {A B : ℝ} (data : Data A B) (a b : ℕ → ℝ) : ℝ :=
  letI := data.mΩ
  Real.sqrt <| ∫ ω, |absGap data a b ω| ^ (2 : ℕ) ∂data.μ

def c (A B : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    min
      (A ^ (8 : ℕ) / (2 : ℝ) ^ (55 : ℕ))
      (A ^ (2 : ℕ) /
        ((2 : ℝ) ^ (8 : ℕ) *
          (2 + (2 : ℝ) ^ (41 : ℕ) / A ^ (6 : ℕ)) *
          max (4 / A ^ (2 : ℕ)) (2 / (1 - B))))

def SPR {A B : ℝ} (data : Data A B) (C : ℝ) : Prop :=
  ∀ a b : ℕ → ℝ,
    Summable (fun i => a i ^ (2 : ℕ)) →
    Summable (fun i => b i ^ (2 : ℕ)) →
    phaseDistance a b ≤ C * modulusGap data a b

def ReducedHypotheses {A : ℝ} (a b : ℕ → ℝ) : Prop :=
  Summable (fun i => a i ^ (2 : ℕ)) ∧
  Summable (fun i => b i ^ (2 : ℕ)) ∧
  coeffL2Sq a = 1 ∧
  coeffL2Sq b = 1 ∧
  coeffInner a b = 0 ∧
  (∀ i, max (|aTail A a b i|) (|bTail A a b i|) ≤ lambda A)

def ReducedSPR {A B : ℝ} (data : Data A B) (c : ℝ) : Prop :=
  ∀ a b : ℕ → ℝ, ReducedHypotheses (A := A) a b → c ≤ modulusGap data a b

lemma c_eq_cOrth (A B : ℝ) : c A B = cOrth A B := by
  rfl

private def internalData {A B : ℝ} (data : Data A B) : QuantitativeData A B where
  Ω := data.Ω
  mΩ := data.mΩ
  μ := data.μ
  ξ := data.ξ
  aestronglyMeasurable := data.aestronglyMeasurable
  indep := data.indep
  mean_zero := data.mean_zero
  second_moment := data.second_moment
  l1_lower := data.l1_lower
  l1_upper := data.l1_upper

private lemma modulusGap_eq_internal {A B : ℝ} (data : Data A B) (a b : ℕ → ℝ) :
    modulusGap data a b = QuantitativePR.modulusGap (internalData data) a b := rfl

theorem reduced_stable_phase_retrieval
    {A B : ℝ} (data : Data A B) (hAB : admissibleParameters A B) :
    ReducedSPR data (c A B) := by
  rcases hAB with ⟨hA, _, hB⟩
  intro a b h
  rcases h with ⟨haSummable, hbSummable, haNorm, hbNorm, hab, hMax⟩
  rw [modulusGap_eq_internal, c_eq_cOrth]
  exact QuantitativePR.orthogonal_modulus_lower_bound (internalData data) a b hA hB
    haSummable hbSummable haNorm hbNorm hab hMax

end QuantitativePR.Showcase
