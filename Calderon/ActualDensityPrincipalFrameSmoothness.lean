import Calderon.ActualDensityAngularBoundaryAction

/-! The same actual Q, finite scalar contraction. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge

lemma contDiff_referenceDensityPrincipalFrameCoefficient_joint
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 i j) := by
  unfold referenceDensityPrincipalFrameCoefficient
  exact ContDiff.sum (fun k _ => ContDiff.sum (fun l _ =>
    ((contDiff_referenceNormalizedPrincipalMatrix_entry_joint g g2 hg hg2 L k l).mul
      (contDiff_referenceCoFrameEntry g hg L k i)).mul
        (contDiff_referenceCoFrameEntry g hg L l j)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceDensityPrincipalFrameCoefficient_joint
