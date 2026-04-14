import QuantitativePR.Head.HeadMatrix

noncomputable section

open scoped BigOperators

namespace QuantitativePR

def M (A : ℝ) : ℕ := Nat.ceil ((2 : ℝ) ^ (18 : ℕ) / A ^ (2 : ℕ))

def etaBlock (A s : ℝ) : ℝ := s / (4 * M A)

def lambda0 (A s : ℝ) : ℝ := A * Real.sqrt s / 1024

def r0 (A s : ℝ) : ℝ := A ^ (2 : ℕ) * Real.sqrt s / 65536

lemma etaBlock_eq (A s : ℝ) : etaBlock A s = s / (4 * M A) := rfl

axiom four_etaBlock_M
    (A s : ℝ) (hA : 0 < A) :
    4 * (M A : ℝ) * etaBlock A s = s

axiom exists_block_partition
    {n : ℕ} (A s : ℝ) (a : Fin n → ℝ)
    (hs : s ≤ ∑ i, a i ^ (2 : ℕ))
    (hmax : ∀ i, a i ^ (2 : ℕ) ≤ etaBlock A s) :
    ∃ G : Fin (M A) → Finset (Fin n),
      Pairwise fun j k => Disjoint (G j) (G k)

axiom finite_concentration
    {A B : ℝ} (qd : QuantitativeData A B)
    {n : ℕ} (s : ℝ) (a : Fin n → ℝ)
    (hs : s ≤ ∑ i, a i ^ (2 : ℕ))
    (hmax : ∀ i, |a i| ≤ lambda0 A s) :
    letI := qd.mΩ
    ∀ t : ℝ, smallBallMass qd.μ (fun ω => ∑ i, a i * qd.ξ i ω) (r0 A s) t ≤ 3 / 8

axiom binomial_many_active
    (A : ℝ) (hA : 0 < A) (hA1 : A < 1) :
    True

axiom concentration
    {A B : ℝ} (qd : QuantitativeData A B)
    (c : ℕ → ℝ) (s : ℝ)
    (hc : Summable fun i => c i ^ (2 : ℕ))
    (hs : s ≤ coeffL2Sq c)
    (hmax : ∀ i, |c i| ≤ lambda0 A s) :
    letI := qd.mΩ
    ∀ t : ℝ, smallBallMass qd.μ (linComb qd c) (r0 A s) t ≤ 3 / 8

axiom cross_anticoncentration
    {A B : ℝ} (qd : QuantitativeData A B)
    (c d : ℕ → ℝ) (s : ℝ)
    (hc : Summable fun i => c i ^ (2 : ℕ))
    (hd : Summable fun i => d i ^ (2 : ℕ))
    (hc_var : s ≤ coeffL2Sq c)
    (hd_var : s ≤ coeffL2Sq d)
    (hmax : ∀ i, max (|c i|) (|d i|) ≤ lambda0 A s) :
    letI := qd.mΩ
    ∀ u v : ℝ,
      1 / 4 ≤ smallBallMass qd.μ (linComb qd c) (r0 A s) u +
        smallBallMass qd.μ (linComb qd d) (r0 A s) v

axiom cross_min_expectation
    {A B : ℝ} (qd : QuantitativeData A B)
    (c d : ℕ → ℝ) (s u v : ℝ)
    (hc : Summable fun i => c i ^ (2 : ℕ))
    (hd : Summable fun i => d i ^ (2 : ℕ))
    (hc_var : s ≤ coeffL2Sq c)
    (hd_var : s ≤ coeffL2Sq d)
    (hmax : ∀ i, max (|c i|) (|d i|) ≤ lambda0 A s) :
    letI := qd.mΩ
    r0 A s / 4 ≤
      ∫ ω, min (|linComb qd c ω - u|) (|linComb qd d ω - v|) ∂qd.μ

end QuantitativePR
