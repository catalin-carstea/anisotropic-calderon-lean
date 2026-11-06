import Calderon.ActualDensitySigmaMixedCoefficient
import Calderon.ActualPhysicalPureAngular
import Calderon.ActualNativeMovingAdjointFiniteJ

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic NormalizedPrincipalMetric ReferenceDensityBounds
  ActualPhysicalMixedNative ActualPhysicalPureAngular

lemma referenceDensityPrincipalFrameCoefficient_sub_kronecker_div_radius_eq_physicalPureAngularCoefficient
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (L q δ R : ℝ) (p : ℕ) (y : R3) (i j : Fin 3) :
    (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
      (if i = j then (1 : ℝ) else 0)) / ConformalDepth.referenceRadius δ R p L y =
      physicalPureAngularCoefficient g L q δ R p
        (referenceNormalizedPrincipalDifference g g2 L q) i j y := by
  rw [referenceDensityPrincipalFrameCoefficient_sub_kronecker_eq_physicalMixedFrameCoefficient
    g g2 hg L q y i j]
  simp only [physicalMixedFrameCoefficient, physicalPureAngularCoefficient,
    Fin.sum_univ_three, div_eq_mul_inv]
  ring

lemma referenceDensitySigmaDoubleAngularAction_eq_physicalPureAngularCoefficient_sum
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (L q δ R : ℝ) (p : ℕ) (y : R3) (u : SphereSobolev (3/2 : ℝ)) :
    (ConformalDepth.referenceRadius δ R p L y)⁻¹ •
      (∑ i : Fin 3, ∑ j : Fin 3,
        (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
          (if i = j then (1 : ℝ) else 0)) •
          SphereHarmonic.sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
            (SphereHarmonic.sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        physicalPureAngularCoefficient g L q δ R p
          (referenceNormalizedPrincipalDifference g g2 L q) i j y •
          SphereHarmonic.sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
            (SphereHarmonic.sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u) := by
  simp_rw [← referenceDensityPrincipalFrameCoefficient_sub_kronecker_div_radius_eq_physicalPureAngularCoefficient
    g g2 hg L q δ R p y]
  simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
