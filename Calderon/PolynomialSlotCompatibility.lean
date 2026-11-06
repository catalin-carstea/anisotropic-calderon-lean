import Calderon.FischerConnectionTransport

noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.PolynomialSlotCompatibility
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial CurvatureSkew
  MovingFrameConnection FischerConnectionTransport

lemma polynomialMatrixVectorField_partial_commutator (c : Fin 3 → Fin 3 → ℝ)
    (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    -polynomialMatrixVectorField c (pderiv i p) - pderiv i (-polynomialMatrixVectorField c p) =
      ∑ a : Fin 3, C (c a i) * pderiv a p := by
  fin_cases i <;>
    simp [polynomialMatrixVectorField,Fin.sum_univ_three,pderiv_mul,
      pderiv_pderiv_comm (0:Fin 3) 1 p,pderiv_pderiv_comm (0:Fin 3) 2 p,
      pderiv_pderiv_comm (1:Fin 3) 2 p] <;> ring

lemma polynomialMatrixVectorField_multiplication_commutator (c : Fin 3 → Fin 3 → ℝ)
    (hc : ∀ a b, c a b = -c b a) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    -polynomialMatrixVectorField c (X i * p) - X i * (-polynomialMatrixVectorField c p) =
      ∑ a : Fin 3, C (c a i) * (X a * p) := by
  have hd (a : Fin 3) : c a a = 0 := by have h := hc a a; linarith
  fin_cases i <;>
    simp [polynomialMatrixVectorField,Fin.sum_univ_three,pderiv_mul,hd] <;>
    rw [hc 1 0,hc 2 0,hc 2 1] <;>
    simp only [map_neg] <;> ring

lemma referenceFrameAngularPolynomial_partial_commutator (g : MatrixField)
    (L lam : ℝ) (x X : R3) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    referenceFrameAngularPolynomial g L lam x X (pderiv i p) -
      pderiv i (referenceFrameAngularPolynomial g L lam x X p) =
      ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x X a i) * pderiv a p :=
  polynomialMatrixVectorField_partial_commutator _ p i

lemma referenceFrameAngularPolynomial_multiplication_commutator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x V : R3) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    referenceFrameAngularPolynomial g L lam x V (X i * p) -
      X i * referenceFrameAngularPolynomial g L lam x V p =
      ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x V a i) * (X a * p) :=
  polynomialMatrixVectorField_multiplication_commutator _
    (fun a b => referenceFrameConnectionCoefficient_skew g hg L lam x V a b) p i

variable {ι : Type*} [Fintype ι]

lemma finitePolynomialField_partial (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x : R3) (i : Fin 3) :
    finitePolynomialField (fun j => pderiv i (b j)) c x = pderiv i (finitePolynomialField b c x) := by
  simp only [finitePolynomialField,map_sum,smul_eq_C_mul,pderiv_C_mul]

lemma finitePolynomialField_multiplication (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x : R3) (i : Fin 3) :
    finitePolynomialField (fun j => X i * b j) c x = X i * finitePolynomialField b c x := by
  simp only [finitePolynomialField,smul_eq_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma finitePolynomialFieldDerivative_partial (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    finitePolynomialFieldDerivative (fun j => pderiv i (b j)) c x V =
      pderiv i (finitePolynomialFieldDerivative b c x V) :=
  finitePolynomialField_partial b (fun _ => fderiv ℝ c x V) x i

lemma finitePolynomialFieldDerivative_multiplication (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    finitePolynomialFieldDerivative (fun j => X i * b j) c x V =
      X i * finitePolynomialFieldDerivative b c x V :=
  finitePolynomialField_multiplication b (fun _ => fderiv ℝ c x V) x i

def referenceCovectorPolynomialDerivative (g : MatrixField) (L lam : ℝ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    MvPolynomial (Fin 3) ℝ :=
  referenceCovariantPolynomialDerivative g L lam (fun j => b j i) c x V -
    ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x V a i) *
      finitePolynomialField (fun j => b j a) c x

theorem referenceCovectorPolynomialDerivative_partial (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam (fun j a => pderiv a (b j)) c x V i =
      pderiv i (referenceCovariantPolynomialDerivative g L lam b c x V) := by
  have h := referenceFrameAngularPolynomial_partial_commutator g L lam x V (finitePolynomialField b c x) i
  simp only [referenceCovectorPolynomialDerivative,referenceCovariantPolynomialDerivative,
    finitePolynomialField_partial,finitePolynomialFieldDerivative_partial,map_add]
  linear_combination h

theorem referenceCovectorPolynomialDerivative_multiplication (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam (fun j a => X a * b j) c x V i =
      X i * referenceCovariantPolynomialDerivative g L lam b c x V := by
  have h := referenceFrameAngularPolynomial_multiplication_commutator g hg L lam x V (finitePolynomialField b c x) i
  simp only [referenceCovectorPolynomialDerivative,referenceCovariantPolynomialDerivative,
    finitePolynomialField_multiplication,finitePolynomialFieldDerivative_multiplication,mul_add]
  linear_combination h

end OAI.AnisotropicCalderon.PolynomialSlotCompatibility
