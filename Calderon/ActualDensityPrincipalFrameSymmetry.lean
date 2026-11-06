import Calderon.ActualDensityAngularBoundaryAction

/-! Before-source expansion: actual-physical-principal-symmetry-author-oct16-v001/
EXPANSION-v001.md. Real principal symmetry, no operator reordering. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open NormalizedPrincipalMetric MetricVolume ActualHorizontalNormBridge

lemma referenceDensityPrincipalFrameCoefficient_symm
    (g g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (y : R3) (i j : Fin 3) :
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j =
      referenceDensityPrincipalFrameCoefficient g g2 L q y j i := by
  have hP : (referenceNormalizedPrincipalMatrix g g2 L q y).IsHermitian :=
    normalizedPrincipalMatrix_isHermitian _ _ (ConformalDepth.dilatedMetric_posDef g2 hg2 q y)
  have hEntry (k l : Fin 3) : referenceNormalizedPrincipalMatrix g g2 L q y k l =
      referenceNormalizedPrincipalMatrix g g2 L q y l k := by
    simpa only [star_trivial] using (hP.apply k l).symm
  unfold referenceDensityPrincipalFrameCoefficient
  calc
    _ = ∑ l : Fin 3, ∑ k : Fin 3,
        referenceNormalizedPrincipalMatrix g g2 L q y k l *
          referenceCoFrameEntry g L k i (q,y) * referenceCoFrameEntry g L l j (q,y) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro k hk
      rw [hEntry k l]
      ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityPrincipalFrameCoefficient_symm
