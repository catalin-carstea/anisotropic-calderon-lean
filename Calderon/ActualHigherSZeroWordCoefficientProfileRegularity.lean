import Calderon.ActualHigherSZeroWordCoefficientRegularity
import Calderon.ActualHigherSIntegratedPairing
set_option autoImplicit false
set_option diagnostics true
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualHigherSQuadraticZeroWords ActualNormalizedSecondMetricDrift ReferenceDensityBounds
  ActualScalarPrincipalAdjoint ConformalDepth SmoothMetricFrame MovingFrameConnection

/-! Complete scalar contract module; no endpoint data or analytic callback.
Before-source expansion: coefficient-profile-regularity-upfront-nov03-v002/MATHEMATICS.md.
The connection reads only the base (q,x) coordinates of the original profile.
All original 207 ordered coefficients and all original parameters are retained.
UNCOMPILED until the parent's maintained focused/full checks succeed. -/

lemma contDiff_coefficientParameterSlice (q : ℝ) :
    ContDiff ℝ ∞ (fun x : R3 => (q,x)) :=
  contDiff_const.prodMk contDiff_id

lemma contDiff_coefficientFixedSlice (F : (ℝ × R3) → ℝ)
    (hF : ContDiff ℝ ∞ F) (q : ℝ) :
    ContDiff ℝ ∞ (fun x : R3 => F (q,x)) :=
  ContDiff.fun_comp (g := F) (f := fun x : R3 => (q,x)) hF
    (contDiff_coefficientParameterSlice q)

lemma actualWordConnection_eq_baseSlice (g : MatrixField) (L dr Ar : ℝ) (p : ℕ)
    (q : ℝ) (x : R3) (i a b : Fin 3) :
    ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b
      (ActualHigherSFormation.higherSParam L dr Ar p q x) =
    ActualHorizontalNormBridge.referenceFrameConnectionJoint g L (fun y => referenceMetricGramFrame g L y i)
      (q,x) a b := rfl

lemma actualWordCoefficient_eq_baseComponents (g g2 : MatrixField) (L dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) (z : ZeroWord) :
    actualWordCoefficient g L g2 dr Ar p q x z =
    wordCoefficient (referenceRadius dr Ar p L x)
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
      (fun i a b => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
        (fun y => referenceMetricGramFrame g L y i) (q,x) a b) z := rfl

lemma contDiff_actualWordPrincipal_scalar (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) (L q : ℝ)
    (i j : Fin 3) :
    ContDiff ℝ ∞
      (fun x : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q x i j) :=
  contDiff_coefficientFixedSlice
    (fun z : ℝ × R3 => referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 i j)
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j) q

lemma contDiff_actualWordLog_scalar (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 =>
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i) :=
  ActualHigherSIntegratedPairing.contDiff_logDerivative_slice
    (g := g) (L := L) (q := q) (R := referenceRadius dr Ar p L) hg
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr)
    (fun x => ne_of_gt (referenceRadius_pos dr Ar p L x hdr hAr)) i

lemma contDiff_actualWordConnection_scalar (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i a b : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
      (fun y => referenceMetricGramFrame g L y i) (q,x) a b) :=
  contDiff_coefficientFixedSlice
    (fun z : ℝ × R3 => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
      (fun y => referenceMetricGramFrame g L y i) z a b)
    (ActualHorizontalNormBridge.contDiff_referenceFrameConnectionJoint g hg L _
      (contDiff_referenceMetricGramFrame g hg L i) a b) q

lemma contDiff_actualWordCoefficient_baseComponents
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (z : ZeroWord) :
    ContDiff ℝ ∞ (fun x : R3 =>
      wordCoefficient (referenceRadius dr Ar p L x)
        (referenceDensityPrincipalFrameCoefficient g g2 L q x)
        (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
        (fun i a b => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
          (fun y => referenceMetricGramFrame g L y i) (q,x) a b) z) :=
  contDiff_wordCoefficient_of_components
    (referenceRadius dr Ar p L)
    (fun x => referenceDensityPrincipalFrameCoefficient g g2 L q x)
    (fun x => referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
    (fun x i a b => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
      (fun y => referenceMetricGramFrame g L y i) (q,x) a b)
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr)
    (contDiff_actualWordPrincipal_scalar g g2 hg hg2 L q)
    (contDiff_actualWordLog_scalar g hg L dr Ar p hdr hAr q)
    (contDiff_actualWordConnection_scalar g hg L q) z

lemma contDiff_actualWordCoefficient_scalar
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (z : ZeroWord) :
    ContDiff ℝ ∞ (fun x : R3 => actualWordCoefficient g L g2 dr Ar p q x z) := by
  have he : (fun x : R3 => actualWordCoefficient g L g2 dr Ar p q x z) =
      (fun x : R3 => wordCoefficient (referenceRadius dr Ar p L x)
        (referenceDensityPrincipalFrameCoefficient g g2 L q x)
        (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
        (fun i a b => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
          (fun y => referenceMetricGramFrame g L y i) (q,x) a b) z) :=
    funext (fun x => actualWordCoefficient_eq_baseComponents g g2 L dr Ar p q x z)
  rw [he]
  exact contDiff_actualWordCoefficient_baseComponents g g2 hg hg2 L dr Ar p hdr hAr q z

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
