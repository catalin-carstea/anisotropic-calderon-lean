import Calderon.ActualFixedChartPhysicalHarmonicTransport
import Calderon.PositiveCoefficientHarmonicNeighborhoodTraceDensity
import Calderon.SmoothHalfTraceGermCongruence
import Calderon.SphereSobolevPairing

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge MetricVolume MetricOperator ConnectionError DirichletFamily
  DirichletFamily.DriftBootstrap SphereHarmonic NativeSmoothSharpTraceCompletion

def actualPacketPhysicalHarmonicHalfTraceSet
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (q : ℝ) (y : R3) (r : ℝ) : Set (SphereSobolev (1/2 : ℝ)) :=
  {z | ∃ u : SmoothData, ∃ V : Set R3, IsOpen V ∧
    packetEndpoint S L P q y r '' closedBall (0 : R3) 1 ⊆ V ∧
    (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (q • x)) u.1) x = 0) ∧
    z = smoothHalfTrace hF hO hD τ0
      (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B P.native_data.1.1.1 q y r u)}

theorem dense_actualPacketPhysicalHarmonicHalfTraceSet
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling) :
    Dense (actualPacketPhysicalHarmonicHalfTraceSet hF hO hD τ0 S L (cover.packet i) q y r) := by
  let P := cover.packet i
  let A := referencePhysicalNormalizedPrincipalCoefficient S.g1 L P.Phi P.H (q,(y,r))
  have hSmooth : ContDiff ℝ ∞ A := contDiff_referencePhysicalNormalizedPrincipalCoefficient
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data (q,(y,r))
  have hPositive : ∀ z : R3, (A z).PosDef :=
    referencePhysicalNormalizedPrincipalCoefficient_posDef S.g1 L P.y0 P.Phi P.B P.epsGeo
      P.Cgeo P.rho P.H P.a P.w P.native_data (q,(y,r))
  have hDense := dense_positiveCoefficientHarmonicNeighborhoodHalfTraceSet
    hcalc hreg hF hO hD τ0 A hSmooth hPositive
  have hSub : positiveCoefficientHarmonicNeighborhoodHalfTraceSet hF hO hD τ0 A ⊆
      actualPacketPhysicalHarmonicHalfTraceSet hF hO hD τ0 S L P q y r := by
    rintro z ⟨v,O,hOpen,hKO,hDouble,hPDE,hTrace⟩
    obtain ⟨u,V,_,hV,hCover,hPhysical,hNear⟩ :=
      exists_actual_packet_physical_harmonic_neighborhood_of_normalized
        S L cover i q hq y hy r hrpos hrceil v O hOpen hKO hDouble hPDE
    have hTraceEq := smoothHalfTrace_eq_of_eventuallyEq_closedBall hF hO hD τ0
      (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B P.native_data.1.1.1 q y r u)
      v hNear
    exact ⟨u,V,hV,hCover,hPhysical,hTrace.trans hTraceEq.symm⟩
  intro z
  exact closure_mono hSub (hDense z)

theorem eq_zero_of_actualPacketPhysicalHarmonicHalfTrace_pairing_eq_zero
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling)
    (F : SphereSobolev (-(1/2 : ℝ)))
    (hZero : ∀ z ∈ actualPacketPhysicalHarmonicHalfTraceSet hF hO hD τ0 S L (cover.packet i) q y r,
      sphereSobolevDualPairing (-(1/2 : ℝ)) F z = 0) : F = 0 := by
  have hDense := dense_actualPacketPhysicalHarmonicHalfTraceSet
    hcalc hreg hF hO hD τ0 S L cover i q hq y hy r hrpos hrceil
  have hContinuous : Continuous (fun z : SphereSobolev (1/2 : ℝ) =>
      sphereSobolevDualPairing (-(1/2 : ℝ)) F z) := (innerSL ℝ F).continuous
  have hClosed : IsClosed {z : SphereSobolev (1/2 : ℝ) |
      sphereSobolevDualPairing (-(1/2 : ℝ)) F z = 0} := isClosed_eq hContinuous continuous_const
  have hAll (z : SphereSobolev (1/2 : ℝ)) : sphereSobolevDualPairing (-(1/2 : ℝ)) F z = 0 :=
    closure_minimal hZero hClosed (hDense z)
  exact inner_self_eq_zero.mp (hAll F)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
