import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace QuantitativePR

structure QuantitativeData (A B : ℝ) where
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

def K (A B : ℝ) : ℝ := max (4 / A ^ (2 : ℕ)) (2 / (1 - B))

def theta (A : ℝ) : ℝ := A ^ (2 : ℕ) / 8

def s0 (A : ℝ) : ℝ := theta A ^ (2 : ℕ) / 16384

def lambda (A : ℝ) : ℝ := A ^ (3 : ℕ) / (2 : ℝ) ^ (20 : ℕ)

def dStar (A : ℝ) : ℝ := 2 + (2 : ℝ) ^ (41 : ℕ) / A ^ (6 : ℕ)

def cCross (A : ℝ) : ℝ := A ^ (8 : ℕ) / (2 : ℝ) ^ (55 : ℕ)

def cLine (A B : ℝ) : ℝ := A ^ (2 : ℕ) / ((2 : ℝ) ^ (8 : ℕ) * dStar A * K A B)

def cOrth (A B : ℝ) : ℝ := (1 / 2 : ℝ) * min (cCross A) (cLine A B)

def Cexplicit (A B : ℝ) : ℝ :=
  max ((2 : ℝ) ^ (56 : ℕ) / A ^ (8 : ℕ))
    ((2 : ℝ) ^ (9 : ℕ) * dStar A * K A B / A ^ (2 : ℕ))

lemma theta_eq (A : ℝ) : theta A = A ^ (2 : ℕ) / 8 := rfl

lemma s0_eq (A : ℝ) : s0 A = A ^ (4 : ℕ) / (2 : ℝ) ^ (20 : ℕ) := by
  unfold s0 theta
  ring

lemma lambda_eq (A : ℝ) : lambda A = A ^ (3 : ℕ) / (2 : ℝ) ^ (20 : ℕ) := rfl

lemma lambda_sq (A : ℝ) : lambda A ^ (2 : ℕ) = A ^ (6 : ℕ) / (2 : ℝ) ^ (40 : ℕ) := by
  unfold lambda
  ring

def coeffL2Sq (c : ℕ → ℝ) : ℝ := ∑' i, c i ^ (2 : ℕ)

def coeffL2Norm (c : ℕ → ℝ) : ℝ := Real.sqrt (coeffL2Sq c)

def coeffInner (a b : ℕ → ℝ) : ℝ := ∑' i, a i * b i

def trunc (H : Finset ℕ) (a : ℕ → ℝ) : ℕ → ℝ := fun i => if i ∈ H then a i else 0

def tail (H : Finset ℕ) (a : ℕ → ℝ) : ℕ → ℝ := fun i => a i - trunc H a i

def thresholdSet (A : ℝ) (a b : ℕ → ℝ) : Set ℕ :=
  {i | lambda A < max (|a i|) (|b i|)}

noncomputable def headSet (A : ℝ) (a b : ℕ → ℝ) : Finset ℕ := by
  classical
  exact if h : (thresholdSet A a b).Finite then h.toFinset else ∅

def aHead (A : ℝ) (a b : ℕ → ℝ) : ℕ → ℝ := trunc (headSet A a b) a

def bHead (A : ℝ) (a b : ℕ → ℝ) : ℕ → ℝ := trunc (headSet A a b) b

def aTail (A : ℝ) (a b : ℕ → ℝ) : ℕ → ℝ := tail (headSet A a b) a

def bTail (A : ℝ) (a b : ℕ → ℝ) : ℕ → ℝ := tail (headSet A a b) b

@[simp] lemma trunc_of_mem {H : Finset ℕ} {a : ℕ → ℝ} {i : ℕ} (hi : i ∈ H) :
    trunc H a i = a i := by
  simp [trunc, hi]

@[simp] lemma trunc_of_not_mem {H : Finset ℕ} {a : ℕ → ℝ} {i : ℕ} (hi : i ∉ H) :
    trunc H a i = 0 := by
  simp [trunc, hi]

@[simp] lemma tail_of_mem {H : Finset ℕ} {a : ℕ → ℝ} {i : ℕ} (hi : i ∈ H) :
    tail H a i = 0 := by
  simp [tail, hi]

@[simp] lemma tail_of_not_mem {H : Finset ℕ} {a : ℕ → ℝ} {i : ℕ} (hi : i ∉ H) :
    tail H a i = a i := by
  simp [tail, hi]

lemma trunc_add_tail (H : Finset ℕ) (a : ℕ → ℝ) :
    trunc H a + tail H a = a := by
  funext i
  by_cases hi : i ∈ H
  · simp [tail, hi]
  · simp [tail, hi]

lemma tail_add_trunc (H : Finset ℕ) (a : ℕ → ℝ) :
    tail H a + trunc H a = a := by
  simpa [Pi.add_def, add_comm] using trunc_add_tail H a

def D (a b : ℕ → ℝ) : Matrix ℕ ℕ ℝ := fun i j => a i * a j - b i * b j

def DH (H : Finset ℕ) (a b : ℕ → ℝ) : Matrix ℕ ℕ ℝ := D (trunc H a) (trunc H b)

def frobeniusNormSq (M : Matrix ℕ ℕ ℝ) : ℝ := ∑' i, ∑' j, M i j ^ (2 : ℕ)

def frobeniusNorm (M : Matrix ℕ ℕ ℝ) : ℝ := Real.sqrt (frobeniusNormSq M)

def randL1Norm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, |f ω| ∂μ

def randL2Sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, |f ω| ^ (2 : ℕ) ∂μ

def randL2Norm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt (randL2Sq μ f)

def linComb {A B : ℝ} (qd : QuantitativeData A B) (c : ℕ → ℝ) : qd.Ω → ℝ :=
  fun ω => ∑' i, c i * qd.ξ i ω

def eps {A B : ℝ} (qd : QuantitativeData A B) (a b : ℕ → ℝ) : ℝ :=
  letI := qd.mΩ
  randL1Norm qd.μ (fun ω => (linComb qd a ω) ^ (2 : ℕ) - (linComb qd b ω) ^ (2 : ℕ))

def modulusGap {A B : ℝ} (qd : QuantitativeData A B) (a b : ℕ → ℝ) : ℝ :=
  letI := qd.mΩ
  randL2Norm qd.μ (fun ω => |linComb qd a ω| - |linComb qd b ω|)

def phaseDistance (a b : ℕ → ℝ) : ℝ :=
  min (coeffL2Norm (fun i => a i - b i)) (coeffL2Norm (fun i => a i + b i))

def smallBallMass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (r t : ℝ) : ℝ :=
  (μ {ω | |X ω - t| ≤ r}).toReal

def concFn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (r : ℝ) : ℝ :=
  sSup (Set.range fun t : ℝ => smallBallMass μ X r t)

axiom card_headSet_le_dStar
    {A : ℝ} (a b : ℕ → ℝ)
    (hA : 0 < A)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (ha : coeffL2Sq a ≤ 1)
    (hb : coeffL2Sq b ≤ 1) :
    ((headSet A a b).card : ℝ) ≤ dStar A

axiom frobenius_rank_one_diff
    (a b : ℕ → ℝ)
    (haSummable : Summable fun i => a i ^ (2 : ℕ))
    (hbSummable : Summable fun i => b i ^ (2 : ℕ))
    (habSummable : Summable fun i => a i * b i)
    (ha : coeffL2Sq a = 1)
    (hb : coeffL2Sq b = 1)
    (hab : coeffInner a b = 0) :
    frobeniusNormSq (D a b) = 2

axiom frobenius_truncation_error
    (H : Finset ℕ) (a b : ℕ → ℝ) :
    frobeniusNorm (D a b - DH H a b)
      ≤ 2 * coeffL2Norm (tail H a) + 2 * coeffL2Norm (tail H b)
        + coeffL2Sq (tail H a) + coeffL2Sq (tail H b)

axiom concFn_add_indep_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U R : Ω → ℝ) (r : ℝ)
    (h_indep : IndepFun U R μ) :
    concFn μ (fun ω => U ω + R ω) r ≤ concFn μ U r

axiom exists_finite_mass_capture
    (c : ℕ → ℝ) (s : ℝ)
    (hc : Summable fun i => c i ^ (2 : ℕ))
    (hs : s ≤ coeffL2Sq c) :
    ∃ F : Finset ℕ, s ≤ ∑ i ∈ F, c i ^ (2 : ℕ)

axiom eps_le_two_mul_modulusGap
    {A B : ℝ} (qd : QuantitativeData A B) (a b : ℕ → ℝ) :
    eps qd a b ≤ 2 * modulusGap qd a b

end QuantitativePR
