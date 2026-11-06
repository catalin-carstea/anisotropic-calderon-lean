import Calderon.PolynomialSlotCompatibility

noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.HarmonicCoordinateCompatibility
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial CurvatureSkew
  MovingFrameConnection FischerConnectionTransport PolynomialSlotCompatibility SphereHarmonic

def coordinateHarmonicRaising (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := X i * p - C ((2*(k:ℝ)+1)⁻¹) * radiusSq * pderiv i p

lemma coordinateHarmonicRaising_eq_harmonicRaising (k : ℕ) (hk : 1 ≤ k) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    coordinateHarmonicRaising k i p = harmonicRaising (k-1) (Pi.single i p) := by
  have hcoef : 2 / (4*((k-1:ℕ):ℝ)+2*(Fintype.card (Fin 3):ℝ)) = (2*(k:ℝ)+1)⁻¹ := by
    have hden : 4*((k-1:ℕ):ℝ)+2*(Fintype.card (Fin 3):ℝ) = 2*(2*(k:ℝ)+1) := by
      rw [Nat.cast_sub hk]
      simp only [Nat.cast_one,Fintype.card_fin,Nat.cast_ofNat]
      ring
    rw [hden]
    simp only [div_eq_mul_inv,mul_inv_rev]
    norm_num
    ring
  have hdiv : polynomialDivergence (Pi.single i p) = pderiv i p := by
    simp [polynomialDivergence,Pi.single_apply,apply_ite]
  rw [harmonicRaising,hcoef,hdiv]
  simp [coordinateHarmonicRaising,polynomialRaising,Pi.single_apply]

theorem coordinateHarmonicRaising_harmonicHomogeneous (k : ℕ) (hk : 1 ≤ k) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    coordinateHarmonicRaising k i p ∈ harmonicHomogeneous (k+1) := by
  have hh : ∀ j : Fin 3, ((Pi.single i p : Fin 3 → MvPolynomial (Fin 3) ℝ) j).IsHomogeneous k := by
    intro j
    by_cases hj : j=i
    · subst j;simpa using hp.1
    · have hz : (0 : MvPolynomial (Fin 3) ℝ).IsHomogeneous k :=
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ k).zero_mem
      simpa only [Pi.single_apply,if_neg hj] using hz
  have hl : ∀ j : Fin 3, laplacian ((Pi.single i p : Fin 3 → MvPolynomial (Fin 3) ℝ) j) = 0 := by
    intro j
    by_cases hj : j=i
    · subst j;simpa using hp.2
    · simp [Pi.single_apply,hj,laplacian]
  rw [coordinateHarmonicRaising_eq_harmonicRaising k hk]
  exact ⟨harmonicRaising_isHomogeneous hk _ hh,
    laplacian_harmonicRaising _ hh hl (ne_of_gt (radiusSq_laplacian_coefficient_pos (k-1)))⟩

lemma polynomialMatrixVectorField_radiusSq_mul (c : Fin 3 → Fin 3 → ℝ)
    (hc : ∀ a b,c a b = -c b a) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialMatrixVectorField c (radiusSq*p) = radiusSq*polynomialMatrixVectorField c p := by
  have hd (a : Fin 3) : c a a = 0 := by have h:=hc a a;linarith
  simp only [polynomialMatrixVectorField,Fin.sum_univ_three,pderiv_mul,pderiv_radiusSq]
  rw [hd 0,hd 1,hd 2,hc 1 0,hc 2 0,hc 2 1]
  simp only [map_zero,map_neg,zero_mul,mul_zero,zero_add,add_zero]
  ring

lemma referenceFrameAngularPolynomial_radiusSq_mul (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x V : R3) (p : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x V (radiusSq*p) =
      radiusSq*referenceFrameAngularPolynomial g L lam x V p := by
  rw [referenceFrameAngularPolynomial,referenceFrameAngularPolynomial,
    polynomialMatrixVectorField_radiusSq_mul _
      (fun a b=>referenceFrameConnectionCoefficient_skew g hg L lam x V a b) p]
  ring

lemma referenceFrameAngularPolynomial_C_mul (g : MatrixField) (L lam : ℝ) (x V : R3)
    (r : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x V (C r*p) =
      C r*referenceFrameAngularPolynomial g L lam x V p := by
  simpa only [smul_eq_C_mul] using referenceFrameAngularPolynomial_smul g L lam x V r p

lemma referenceFrameAngularPolynomial_sub (g : MatrixField) (L lam : ℝ) (x V : R3)
    (p q : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x V (p-q) =
      referenceFrameAngularPolynomial g L lam x V p - referenceFrameAngularPolynomial g L lam x V q :=
  map_sub (referenceAngularPolynomialLinearMap g L lam x V) p q

lemma referenceFrameAngularPolynomial_coordinateHarmonicRaising_commutator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x V : R3) (k : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x V (coordinateHarmonicRaising k i p) -
      coordinateHarmonicRaising k i (referenceFrameAngularPolynomial g L lam x V p) =
      ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x V a i) * coordinateHarmonicRaising k a p := by
  have hm:=referenceFrameAngularPolynomial_multiplication_commutator g hg L lam x V p i
  have hd:=referenceFrameAngularPolynomial_partial_commutator g L lam x V p i
  have hcorr : referenceFrameAngularPolynomial g L lam x V
      (C ((2*(k:ℝ)+1)⁻¹)*radiusSq*pderiv i p) =
      C ((2*(k:ℝ)+1)⁻¹)*radiusSq*referenceFrameAngularPolynomial g L lam x V (pderiv i p) := by
    rw [mul_assoc,referenceFrameAngularPolynomial_C_mul,referenceFrameAngularPolynomial_radiusSq_mul g hg]
    ring
  simp only [coordinateHarmonicRaising]
  rw [referenceFrameAngularPolynomial_sub,hcorr]
  simp only [Fin.sum_univ_three] at hm hd ⊢
  linear_combination hm - C ((2*(k:ℝ)+1)⁻¹)*radiusSq*hd

variable {ι : Type*} [Fintype ι]

lemma finitePolynomialField_coordinateHarmonicRaising (k : ℕ) (i : Fin 3)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x : R3) :
    finitePolynomialField (fun j=>coordinateHarmonicRaising k i (b j)) c x =
      coordinateHarmonicRaising k i (finitePolynomialField b c x) := by
  simp only [coordinateHarmonicRaising,finitePolynomialField,smul_eq_C_mul,map_sum,
    pderiv_C_mul,Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

lemma finitePolynomialFieldDerivative_coordinateHarmonicRaising (k : ℕ) (i : Fin 3)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x V : R3) :
    finitePolynomialFieldDerivative (fun j=>coordinateHarmonicRaising k i (b j)) c x V =
      coordinateHarmonicRaising k i (finitePolynomialFieldDerivative b c x V) :=
  finitePolynomialField_coordinateHarmonicRaising k i b (fun _=>fderiv ℝ c x V) x

theorem referenceCovectorPolynomialDerivative_coordinateHarmonicRaising (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam (fun j a=>coordinateHarmonicRaising k a (b j)) c x V i =
      coordinateHarmonicRaising k i (referenceCovariantPolynomialDerivative g L lam b c x V) := by
  have h:=referenceFrameAngularPolynomial_coordinateHarmonicRaising_commutator g hg L lam x V k i
    (finitePolynomialField b c x)
  simp only [referenceCovectorPolynomialDerivative,referenceCovariantPolynomialDerivative,
    finitePolynomialField_coordinateHarmonicRaising,finitePolynomialFieldDerivative_coordinateHarmonicRaising]
  simp only [coordinateHarmonicRaising,map_add,mul_add,pderiv_C_mul] at h ⊢
  linear_combination h

end OAI.AnisotropicCalderon.HarmonicCoordinateCompatibility
