import Calderon.ActualDensityAngularBoundaryAction
import Calderon.ActualPhysicalMixedReferenceCancellation

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open NormalizedPrincipalMetric ReferenceDensityBounds ActualPhysicalMixedNative
  ActualPhysicalMixedReferenceCancellation

lemma referenceDensityPrincipalFrameCoefficient_eq_physicalMixedQFrameCoefficient
    (g g2 : MatrixField) (L q : ℝ) (y : R3) (i j : Fin 3) :
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j =
      physicalMixedQFrameCoefficient g L q
        (referenceNormalizedPrincipalDifference g g2 L q) i j y := by
  simp only [referenceDensityPrincipalFrameCoefficient, physicalMixedQFrameCoefficient,
    referenceNormalizedPrincipalDifference, normalizedPrincipalDifference,
    referenceNormalizedPrincipalMatrix, referenceInverseEntryFamily,
    Matrix.sub_apply, Fin.sum_univ_three]
  ring

lemma referenceDensityPrincipalFrameCoefficient_sub_kronecker_eq_physicalMixedFrameCoefficient
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (y : R3) (i j : Fin 3) :
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
      (if i = j then (1 : ℝ) else 0) =
      physicalMixedFrameCoefficient g L q
        (referenceNormalizedPrincipalDifference g g2 L q) i j y := by
  rw [referenceDensityPrincipalFrameCoefficient_eq_physicalMixedQFrameCoefficient g g2 L q y i j,
    physicalMixedQFrameCoefficient_decomposition g hg L q
      (referenceNormalizedPrincipalDifference g g2 L q) i j y]
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
