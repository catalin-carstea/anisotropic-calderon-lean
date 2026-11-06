import Calderon.AmbientSmoothWeightedCore
import Calderon.CovariantHarmonicEnergy

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.AmbientReferenceCovariantCore
open SphereHarmonic SpectralCoreRegularity SmoothSphereFields SmoothMovingFrameFields
  AngularWeightedCore AmbientSmoothWeightedCore CovariantHarmonicEnergy
  MovingFrameConnection SmoothMetricFrame MetricOperator ConformalDepth RadiusProfile

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric referenceFrameConnectionCoefficient
  referenceHarmonicCovariantDerivative

/-- Smoothness is proved for the source's actual reference coefficients. -/
lemma contDiff_referenceFrameConnectionCoefficient_field (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => referenceFrameConnectionCoefficient g L lam x (X x) i j) := by
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hM : ContDiff ℝ ∞ (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) :=
    (contDiff_referenceMetricOperator_joint g hg L).comp hpair
  have hΓ : ContDiff ℝ ∞ (fun y => referenceConnectionFamily g L (lam,y)) :=
    (contDiff_referenceConnectionFamily g hg L).comp hpair
  simpa only [referenceFrameConnectionCoefficient] using
    contDiff_frameConnectionCoefficient_field
      (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
      (fun y => referenceConnectionFamily g L (lam,y))
      (fun y => referenceMetricGramFrame g L (lam,y)) hM hΓ
      (fun a => contDiff_referenceMetricGramFrame_slice g hg L lam a) X hX i j

lemma referenceFrameHorizontalLift_mem_sphereSmoothWeightedCore
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2
      (ambientFrameHorizontal (fun y => referenceFrameConnectionCoefficient g L lam y (X y)) X G)
      (contDiff_ambientFrameHorizontal _
        (fun i j => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX i j)
        X hX G hG) x ∈ sphereSmoothWeightedCore hO hD :=
  frameHorizontalLift_mem_sphereSmoothWeightedCore hO hD _
    (fun i j => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX i j)
    X hX G hG x

/-- Exact reference covariant coordinates for an actual smooth field, in every degree. -/
lemma sphereHarmonicCoordinate_referenceFrameHorizontal
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD k
      (ambientSphereL2
        (ambientFrameHorizontal (fun y => referenceFrameConnectionCoefficient g L lam y (X y)) X G)
        (contDiff_ambientFrameHorizontal _
          (fun i j => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX i j)
          X hX G hG) x) =
      referenceHarmonicCovariantDerivative g L lam k
        (fun y => sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG y)) x (X x) := by
  simpa only [referenceHarmonicCovariantDerivative] using
    sphereHarmonicCoordinate_frameHorizontal hO hD k _
      (fun i j => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX i j)
      (fun y i j => referenceFrameConnectionCoefficient_skew g hg L lam y (X y) i j)
      X hX G hG x

/-- The actual source Gram-frame directions give smooth fields in the exact core. -/
lemma referenceGramFrameHorizontalLift_mem_sphereSmoothWeightedCore
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2
      (ambientFrameHorizontal
        (fun y => referenceFrameConnectionCoefficient g L lam y
          (referenceMetricGramFrame g L (lam,y) i))
        (fun y => referenceMetricGramFrame g L (lam,y) i) G)
      (contDiff_ambientFrameHorizontal _
        (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
          (contDiff_referenceMetricGramFrame_slice g hg L lam i) a b)
        _ (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG) x ∈
      sphereSmoothWeightedCore hO hD :=
  referenceFrameHorizontalLift_mem_sphereSmoothWeightedCore hO hD g hg L lam _
    (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG x

end OAI.AnisotropicCalderon.AmbientReferenceCovariantCore
