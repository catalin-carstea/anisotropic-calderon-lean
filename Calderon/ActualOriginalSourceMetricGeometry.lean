import Calderon.ActualNativePacketPhysicalChart
import Calderon.ActualReferencePhysicalCoefficientNativeIdentity
import Calderon.MetricPullbackComposition

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError MetricVolume MetricOperator ConformalDepth

def originalSourcePacketMetricModel
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (y : R3) (r : ℝ) : MatrixField :=
  conformalMatrix (fun z => P.H ((lam,(y,r)),z))
    (fun z => Real.log (lam*r) + L*referenceRescaledDepth S.g1 L P.Phi (lam,(y,r)) z)

theorem originalSourcePacketMetricModel_smooth_positive
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (y : R3) (r : ℝ) :
    (∀ i j, ContDiff ℝ ∞ (fun z => originalSourcePacketMetricModel S L P lam y r z i j)) ∧
    ∀ z, (originalSourcePacketMetricModel S L P lam y r z).PosDef := by
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ (fun z => packetEndpoint S L P lam y r z) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have ht : ContDiff ℝ ∞ (fun z => referenceRescaledDepth S.g1 L P.Phi (lam,(y,r)) z) :=
    contDiff_conformalReferenceCoordinateDepth.comp hX
  rcases P.native_data.1 with ⟨_,_,_,_,_,_,hH,hPos,_,_,_,_,_,_,_⟩
  have hHs : ContDiff ℝ ∞ (fun z => P.H ((lam,(y,r)),z)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ∞ (fun z => Real.log (lam*r) +
      L*referenceRescaledDepth S.g1 L P.Phi (lam,(y,r)) z) :=
    contDiff_const.add (contDiff_const.mul ht)
  constructor
  · exact conformalMatrix_smooth_entries _ _
      (fun i j => contDiff_pi.mp (contDiff_pi.mp hHs i) j) hf
  · exact conformalMatrix_posDef _ _ (fun z => hPos ((lam,(y,r)),z))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
