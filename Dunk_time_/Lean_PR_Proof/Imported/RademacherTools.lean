import QuantitativePR.Core.Setup

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace QuantitativePR

def signed (ε : Bool) : ℝ := if ε then 1 else -1

def weightedSignSum {n : ℕ} (b : Fin n → ℝ) (ε : Fin n → Bool) : ℝ :=
  ∑ i, signed (ε i) * b i

axiom rademacher_l1_lower (n : ℕ) (x : Fin n → ℝ) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i, x i ^ (2 : ℕ))
      ≤ (∑ ε : Fin n → Bool, |weightedSignSum x ε|) / (2 : ℝ) ^ n

axiom indep_symmetric_sum_l1_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (Z : Fin n → Ω → ℝ) (c : Fin n → ℝ) :
    (1 / Real.sqrt 2) * randL1Norm μ (fun ω => Real.sqrt (∑ i, (c i * Z i ω) ^ (2 : ℕ)))
      ≤ randL1Norm μ (fun ω => ∑ i, c i * Z i ω)

axiom weighted_sign_interval_antichain
    (n : ℕ) (b : Fin n → ℝ) (a : ℝ)
    (hb : ∀ i, a ≤ b i) (ha : 0 < a)
    (I : Set ℝ) :
    True

axiom weighted_sign_interval_prob_le_inv_sqrt
    (n : ℕ) (b : Fin n → ℝ) (I : Set ℝ)
    (hlarge : 256 ≤ n) :
    True

end QuantitativePR
