import Calderon.ActualSameSourcePhysicalHalfGraph
import Calderon.ActualSameSourceWeightedSphereGraph
import Calderon.ActualSameRoomFiniteDensityGraph
import Calderon.ActualFiniteFirstSectionGraphLimits
import Calderon.ActualPhysicalDensityHigherFirstSectionDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAngularL referenceMetricGramFrame referenceRadialEndpointInvertibleLocus
  referenceFramedNormalizedJacobian referenceFrameConnectionCoefficient
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint sphereSobolevInclusionL referencePhysicalDensityHalfFromFirstSections
  referencePhysicalDensityOperator referenceDensityCovariantSecondAction


attribute [local irreducible] referenceFiveHalfDensityFirstActionInRoom referenceFiniteGaugeDensityFirstSection
  sphereSobolevPartialSumL referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceLowerDensityFirstAction referenceWeakDirichletEnergyFamily
private lemma weakInverse_of_endpointSourceRoom (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible := by
  unfold referenceRadialEndpointInvertibleLocus at hp
  exact hp.2.1

theorem exists_reference_commonRadius_same_physicalDensityWeightedSphereGraph
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ dX : ℝ, 0 < dX ∧ dX ≤ ρ ∧
      ∃ G : ReferenceGaugeNormalReciprocalRoom g L Φ a
        (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)),
      ∃ E : ReferenceJacobiCompactExtensionRoom
        (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData)
        (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)),
      ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ dX ∧
      ∀ (q : ℝ), q ∈ Icc (0:ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (5/2:ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) →
    let v : R3 → SphereSobolev (3/2:ℝ) := fun y =>
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
    let etaInf : Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun j y =>
      referenceFiveHalfDensityFirstActionInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y j
    let Wlim : R3 → SphereSobolev (1/2:ℝ) := fun y => referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R etaInf y
    let F : ℕ → R3 → SphereL2 := fun n y => sphereSobolevHalfToSphereL2L hO hD
      (referenceFiniteGaugePhysicalDensityHalfSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y)
    let f : R3 → SphereL2 := fun y => sphereSobolevHalfToSphereL2L hO hD (Wlim y)
    (∀ n, ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧
      MemLp (F n) 2 (referenceBaseMeasure g L q) ∧
      (fun y => sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (F n y))) =
      (fun y => referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) y)) ∧
    ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ MemLp f 2 (referenceBaseMeasure g L q) ∧
    (fun y => sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (f y))) =
      (fun y => referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y) ∧
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) * ‖F n y - f y‖^2)
      atTop (𝓝 0) := by
  obtain ⟨dX,hdX,hdXrho,G,E,d0,hd0,hd0X,hSpec⟩ :=
    exists_reference_commonRadius_same_finiteDensityGraph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
  refine ⟨dX,hdX,hdXrho,G,E,d0,hd0,hd0X,?_⟩
  intro q hq R hR u hu hc hSupport
  have hAt (j : Fin 3) := hSpec q hq R hR u hu hc hSupport j
  have hGeometry : ∀ y ∈ tsupport u, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible := by
    have h := hAt 0
    extract_lets v eta etaInf at h
    exact h.2.2.2.2.2.2.2.2.2
  have hCommon : ∀ y ∈ tsupport u,
      (q,(y,R y)) ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX) ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible := by
    intro y hy
    refine ⟨?_,weakInverse_of_endpointSourceRoom
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) (hGeometry y hy).2.1⟩
    refine ⟨hq,?_,abs_le.mp ((hSupport y hy).2.1.le.trans hd0X)⟩
    simpa only [mem_closedBall,dist_eq_norm] using (hSupport y hy).1.le
  exact referenceFiniteGaugePhysicalDensityOperator_weighted_sphereL2_graph_of_same_source
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E
      g2 hg2 hreg q R hR u hu hc
      (fun n j => ((hAt j).2.2.1 n).1)
      (fun n j => ((hAt j).2.2.1 n).2.2.1) hCommon hGeometry

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
