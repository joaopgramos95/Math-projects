import QuantitativePR.Imported.ElementaryBounds

noncomputable section

open scoped BigOperators

namespace QuantitativePR

axiom diag_entry_bound
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ) (H : Finset ℕ) {i : ℕ} (hH : i ∈ H) :
    |DH H a b i i| ≤ K A B * eps qd a b

axiom offDiag_entry_bound
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ) (H : Finset ℕ) {i j : ℕ}
    (hHi : i ∈ H) (hHj : j ∈ H) (hij : i ≠ j) :
    |DH H a b i j| ≤ K A B * eps qd a b

theorem head_entry_bound
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ) (H : Finset ℕ) {i j : ℕ}
    (hHi : i ∈ H) (hHj : j ∈ H) :
    |DH H a b i j| ≤ K A B * eps qd a b := by
  by_cases hij : i = j
  · subst hij
    exact diag_entry_bound qd a b H hHi
  · exact offDiag_entry_bound qd a b H hHi hHj hij

axiom head_frobenius_ge_one
    (H : Finset ℕ) (a b : ℕ → ℝ)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hab : coeffInner a b = 0)
    (hrho : coeffL2Sq (tail H a) + coeffL2Sq (tail H b) ≤ 1 / 100) :
    1 ≤ frobeniusNorm (DH H a b)

axiom exists_large_head_entry
    (H : Finset ℕ) (a b : ℕ → ℝ)
    (hF : 1 ≤ frobeniusNorm (DH H a b)) :
    ∃ i ∈ H, ∃ j ∈ H, 1 / (H.card : ℝ) ≤ |DH H a b i j|

axiom head_dominant_lower_bound
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (a b : ℕ → ℝ)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hab : coeffInner a b = 0)
    (hrho : coeffL2Sq (tail H a) + coeffL2Sq (tail H b) ≤ 1 / 100) :
    eps qd a b ≥ 1 / ((H.card : ℝ) * K A B)

axiom threshold_head_lower_bound
    {A B : ℝ} (qd : QuantitativeData A B)
    (a b : ℕ → ℝ)
    (hA : 0 < A) (hB : B < 1)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hab : coeffInner a b = 0)
    (hrho : coeffL2Sq (aTail A a b) + coeffL2Sq (bTail A a b) ≤ 1 / 100) :
    eps qd a b ≥ 1 / (dStar A * K A B)

end QuantitativePR
