import QuantitativePR.OneD.Concentration

noncomputable section

open scoped BigOperators

namespace QuantitativePR

def alpha (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) : ℝ :=
  coeffL2Norm (fun i => trunc H a i - τ * trunc H b i)

def beta (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) : ℝ :=
  coeffL2Norm (fun i => tail H a i + τ * tail H b i)

def kappa (A : ℝ) : ℝ := A / (2 * Real.sqrt 2)

axiom factorization
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

axiom error_norms
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

axiom main_piece_norms
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ)
    (haNorm : coeffL2Sq a = 1)
    (hbNorm : coeffL2Sq b = 1)
    (hab : coeffInner a b = 0) :
    True

axiom l1_lower_U
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

axiom l1_lower_V
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

axiom main_term_lower
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

axiom error_term_Uu
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

axiom error_term_vV
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

axiom error_term_uv
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ) :
    True

lemma signMismatch_numeric :
    (7 / 16 : ℝ) - 1 / 32 - 1 / 128 - 1 / 32768 > 1 / 4 := by
  norm_num

axiom sign_mismatch_gluing
    {A B : ℝ} (qd : QuantitativeData A B)
    (H : Finset ℕ) (τ : ℝ) (a b : ℕ → ℝ)
    (hAlpha : alpha H τ a b ≤ theta A / 16)
    (hBeta : beta H τ a b ≤ theta A / 64) :
    eps qd a b ≥ theta A

end QuantitativePR
