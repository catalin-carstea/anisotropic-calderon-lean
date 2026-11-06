import Calderon.ActualReferenceAdjointZeroCoefficient
import Calderon.ActualReferenceFullAdjunction

/-!
Source-only candidate for the exact full reference T-adjoint split.
Frozen target: OAI.AnisotropicCalderon.main, d1205fb493b3fbe04e55f72b76c6ff0761fb5a03.
EXPANSION-v001.md and all literal helper types were frozen before authoring.
This file does not identify the reference zero field with physical U†−U.
No compilation, kernel replay, foundation, review or acceptance claim.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualReferenceAdjointDecomposition
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields
  SmoothAngularApplication AmbientAngularShift AmbientReferenceRaising
  ReferenceDensityBounds ActualBalancedFirstPrincipalError
  ActualUnboundedFirstPrincipalNormalForm ActualReferenceAdjointZeroCoefficient
  ActualPrincipalErrorCoefficient ActualRawMixedPrincipalCollection
  ActualReferenceDecomposition ActualReferenceFullAdjunction ConformalDepth

lemma referenceCoordinateLowering_eq_actualFrameFirstBase
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceCoordinateLowering hF hO hD g L lam G hG x =
      actualFrameFirstBase hF hO hD g L lam G hG x := by
  rfl

lemma referenceProfileLowering_sub_defect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceProfileLowering hF hO hD g L lam f G hG x -
      referenceAllModeDefect hF hO hD g L lam f G hG x =
      ∑ b : Fin 3, referenceFrameDerivative g L lam b f x •
        degreeMinusOneDerivativeField hF hO hD b G hG x := by
  unfold referenceProfileLowering referenceAllModeDefect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ambientDegreeBesselField, ambientDerivativeField,
    degreeMinusOneDerivativeField, degreeMinusOneBesselField,
    map_sub, map_smul, smul_sub, smul_smul]
  module

lemma referenceAdjointZeroField_eq_connection_shiftedDegree
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceAdjointZeroField hF hO hD g L lam f G hG x =
      referenceConnectionLowering hF hO hD g L lam G hG x +
      ∑ b : Fin 3, referenceFrameDerivative g L lam b f x •
        degreeMinusOneDerivativeField hF hO hD b G hG x := by
  have hhalf : -(1/2 : ℝ) = (-1/2 : ℝ) := by ring
  simp only [referenceAdjointZeroField, Fintype.sum_sum_type,
    Fintype.sum_prod_type, referenceZeroCoefficient, referenceZeroOutput,
    referenceConnectionLowering, referenceConnectionEntry,
    Finset.smul_sum, smul_smul, hhalf]

/-- The complete native all-degree adjoint is the checked negative-frame
first-base output plus the derived connection/profile zero output. -/
theorem referenceAllModeAdjointExpression_eq_first_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG x =
      actualFrameFirstBase hF hO hD g L lam G hG x +
        referenceAdjointZeroField hF hO hD g L lam f G hG x := by
  have hd := referenceAllModeLowering_sub_adjointExpression hF hO hD g hg L lam f G hG x
  have he : referenceAllModeAdjointExpression hF hO hD g hg L lam f G hG x =
      referenceAllModeLowering hF hO hD g hg L lam f G hG x -
        referenceAllModeDefect hF hO hD g L lam f G hG x := by
    rw [sub_eq_iff_eq_add.mp hd]
    module
  rw [he, referenceAllModeLowering_decomposition hF hO hD g hg L lam f G hG x,
    referenceCoordinateLowering_eq_actualFrameFirstBase hF hO hD g L lam G hG x,
    referenceAdjointZeroField_eq_connection_shiftedDegree hF hO hD g L lam f G hG x,
    ← referenceProfileLowering_sub_defect hF hO hD g L lam f G hG x]
  module

/-- Genuine native reference-volume/probability-sphere adjunction on the
smooth compact core. The H1-to-H0 endpoint is inherited from the full
native adjunction and is not removed by a mean-zero condition. -/
theorem compact_referenceAllModeRaising_adjoint_first_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪referenceAllModeRaising hF hO hD g hg L lam f G hG x,
        ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,
          actualFrameFirstBase hF hO hD g L lam H hH x +
            referenceAdjointZeroField hF hO hD g L lam f H hH x⟫_ℝ := by
  have h := compact_referenceAllModeRaising_adjointExpression hF hO hD g hg L lam
    f hf G H hG hH K J hK hJ hzG hzH
  simp_rw [referenceAllModeAdjointExpression_eq_first_zero hF hO hD g hg L lam f H hH] at h
  exact h

theorem compact_actual_referenceAllModeRaising_adjoint_first_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪referenceAllModeRaising hF hO hD g hg L lam (referenceLogRadius δ R p L)
          G hG x, ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,
          actualFrameFirstBase hF hO hD g L lam H hH x +
            referenceAdjointZeroField hF hO hD g L lam
              (referenceLogRadius δ R p L) H hH x⟫_ℝ :=
  compact_referenceAllModeRaising_adjoint_first_zero hF hO hD g hg L lam _
    (contDiff_referenceLogRadius_actual δ R L p hδ hR) G H hG hH K J hK hJ hzG hzH

end OAI.AnisotropicCalderon.ActualReferenceAdjointDecomposition
