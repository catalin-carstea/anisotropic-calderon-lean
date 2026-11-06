import Calderon.ActualNativePhysicalModelInputDictionary
import Calderon.ActualFiniteHarmonicModelError
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient SpectralWeightedGraph
  SmoothSphereFields ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients CoordinateBootstrapJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
def nativeModelRaising
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  2*nativeT hO hD hF g1 hg1 L lam δ R p hδ hR+
    nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR

def nativeModelRaisingDrift (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) (L lam : ℝ) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, coreScalar hO hD (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y))
    ((contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
      (contDiff_const.prodMk contDiff_id))*coreRaising hO hD hF a

def nativeNormalizedSecondReferenceModel
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  nativeModelRaising hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR+
    nativeModelRaisingDrift hO hD hF g1 g2 hg1 hg2 L lam

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
