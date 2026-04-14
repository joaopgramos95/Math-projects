import QuantitativePR.Tail.SignMismatch

noncomputable section

open scoped BigOperators

namespace QuantitativePR

axiom rank_one_sign_selection
    (x y : ℕ → ℝ) :
    coeffL2Sq (fun i => x i - y i) * coeffL2Sq (fun i => x i + y i)
      ≤ 2 * frobeniusNormSq (D x y)

axiom rank_one_sign_selection_tau
    (H : Finset ℕ) (a b : ℕ → ℝ) (τ : ℝ)
    (hτ : τ = 1 ∨ τ = -1) :
    coeffL2Sq (fun i => trunc H a i - τ * trunc H b i) *
        coeffL2Sq (fun i => trunc H a i + τ * trunc H b i)
      ≤ 2 * frobeniusNormSq (DH H a b)

axiom head_sign_selection
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (a b : ℕ → ℝ) (τ : ℝ)
    (hEntry : ∀ i ∈ H, ∀ j ∈ H, |DH H a b i j| ≤ K A B * eps qd a b)
    (hTau : τ = 1 ∨ τ = -1)
    (hBeta : coeffL2Norm (fun i => tail H a i - τ * tail H b i) ≤ theta A / 64) :
    coeffL2Norm (fun i => trunc H a i + τ * trunc H b i) ≤
      2 * (H.card : ℝ) * K A B * eps qd a b

axiom beta_small_implies_denominator_ge_one
    (A β : ℝ) (hA : 0 < A) (hA1 : A < 1)
    (hBeta : β ≤ theta A / 64) :
    1 ≤ Real.sqrt (2 - β ^ (2 : ℕ))

axiom one_line_branch
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (a b : ℕ → ℝ) (τ : ℝ)
    (hEntry : ∀ i ∈ H, ∀ j ∈ H, |DH H a b i j| ≤ K A B * eps qd a b)
    (hTau : τ = 1 ∨ τ = -1)
    (hTail : coeffL2Norm (fun i => tail H a i - τ * tail H b i) ≤ theta A / 64)
    (hCard : (H.card : ℝ) ≤ dStar A) :
    eps qd a b ≥ cLine A B

theorem headSet_one_line_branch
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ) (τ : ℝ)
    (hA : 0 < A) (hTau : τ = 1 ∨ τ = -1)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hTail : coeffL2Norm (fun i => aTail A a b i - τ * bTail A a b i) ≤ theta A / 64) :
    eps qd a b ≥ cLine A B := by
  apply one_line_branch qd (headSet A a b) a b τ
  · intro i hi j hj
    exact head_entry_bound qd a b (headSet A a b) hi hj
  · exact hTau
  · simpa [aTail, bTail]
      using hTail
  · exact card_headSet_le_dStar a b hA haSummable hbSummable (by linarith) (by linarith)

end QuantitativePR
