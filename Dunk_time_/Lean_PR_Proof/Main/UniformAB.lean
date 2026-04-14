import QuantitativePR.Tail.OneLine

noncomputable section

open scoped BigOperators

namespace QuantitativePR

axiom tail_sign_dichotomy
    (A : ℝ) (H : Finset ℕ) (a b : ℕ → ℝ)
    (hMass : 1 / 100 < coeffL2Sq (tail H a) + coeffL2Sq (tail H b)) :
    (4 * s0 A ≤ coeffL2Sq (fun i => tail H a i - tail H b i) ∧
      4 * s0 A ≤ coeffL2Sq (fun i => tail H a i + tail H b i))
    ∨
      (∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
        coeffL2Norm (fun i => tail H a i - τ * tail H b i) < theta A / 64)

axiom diffuse_cross_branch
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (a b : ℕ → ℝ)
    (hMinus : 4 * s0 A ≤ coeffL2Sq (fun i => tail H a i - tail H b i))
    (hPlus : 4 * s0 A ≤ coeffL2Sq (fun i => tail H a i + tail H b i))
    (hMax : ∀ i, max (|tail H a i|) (|tail H b i|) ≤ lambda A) :
    eps qd a b ≥ cCross A

theorem one_line_branch_main
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ) (τ : ℝ)
    (hA : 0 < A) (hTau : τ = 1 ∨ τ = -1)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hTail : coeffL2Norm (fun i => aTail A a b i - τ * bTail A a b i) < theta A / 64) :
    eps qd a b ≥ cLine A B := by
  apply headSet_one_line_branch qd a b τ hA hTau haSummable hbSummable haNorm hbNorm
  exact le_of_lt hTail

axiom cLine_le_headBound
    (A B : ℝ) (hA : 0 < A) (hB : B < 1) :
    cLine A B ≤ 1 / (dStar A * K A B)

theorem orthogonal_eps_lower_bound
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ)
    (hA : 0 < A) (hB : B < 1)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hab : coeffInner a b = 0)
    (hMax : ∀ i, max (|aTail A a b i|) (|bTail A a b i|) ≤ lambda A) :
    eps qd a b ≥ min (cCross A) (cLine A B) := by
  by_cases hSmall : coeffL2Sq (aTail A a b) + coeffL2Sq (bTail A a b) ≤ 1 / 100
  · have hHead :
      eps qd a b ≥ 1 / (dStar A * K A B) :=
        threshold_head_lower_bound qd a b hA hB haSummable hbSummable haNorm hbNorm hab hSmall
    have hLine : cLine A B ≤ eps qd a b := by
      have h0 := cLine_le_headBound A B hA hB
      linarith
    exact le_trans (min_le_right (cCross A) (cLine A B)) hLine
  · have hMass :
        1 / 100 < coeffL2Sq (aTail A a b) + coeffL2Sq (bTail A a b) := by
      linarith
    rcases tail_sign_dichotomy A (headSet A a b) a b hMass with hDiffuse | hOneLine
    · rcases hDiffuse with ⟨hMinus, hPlus⟩
      have hCross :
          eps qd a b ≥ cCross A :=
        diffuse_cross_branch qd (headSet A a b) a b hMinus hPlus
          (by simpa [aTail, bTail] using hMax)
      exact le_trans (min_le_left (cCross A) (cLine A B)) hCross
    · rcases hOneLine with ⟨τ, hTau, hTail⟩
      have hLine :
          eps qd a b ≥ cLine A B :=
        one_line_branch_main qd a b τ hA hTau haSummable hbSummable haNorm hbNorm
          (by simpa [aTail, bTail] using hTail)
      exact le_trans (min_le_right (cCross A) (cLine A B)) hLine

theorem orthogonal_modulus_lower_bound
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ)
    (hA : 0 < A) (hB : B < 1)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hab : coeffInner a b = 0)
    (hMax : ∀ i, max (|aTail A a b i|) (|bTail A a b i|) ≤ lambda A) :
    cOrth A B ≤ modulusGap qd a b := by
  have hEps :
      min (cCross A) (cLine A B) ≤ eps qd a b :=
    orthogonal_eps_lower_bound qd a b hA hB haSummable hbSummable haNorm hbNorm hab hMax
  have hGap := eps_le_two_mul_modulusGap qd a b
  have : (1 / 2 : ℝ) * min (cCross A) (cLine A B) ≤ modulusGap qd a b := by
    nlinarith
  simpa [cOrth] using this

axiom stable_phase_retrieval_constant
    {A B : ℝ} (qd : QuantitativeData A B)
    (hA : 0 < A) (hB : B < 1) :
    ∀ a b : ℕ → ℝ,
      Summable (fun i => a i ^ (2 : ℕ)) →
      Summable (fun i => b i ^ (2 : ℕ)) →
      phaseDistance a b ≤ Cexplicit A B * modulusGap qd a b

end QuantitativePR
