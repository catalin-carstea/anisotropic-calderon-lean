import Calderon.ActualSameSourcePhysicalHalfGraph
import Calderon.SupportedWeightedSphereL2Graph
import Calderon.ActualFiniteFirstSectionGraphLimits
import Calderon.ActualPhysicalDensityHigherFirstSectionDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
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
variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

theorem referenceFiniteGaugePhysicalDensityOperator_weighted_sphereL2_graph_of_same_source
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hSmooth : ∀ (n : ℕ) (j : Fin 3), ContDiff ℝ ∞ (fun y => referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R
        (fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z)) y j))
    (hGraph : ∀ (n : ℕ) (j : Fin 3),
      (fun y => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
        (referenceFiniteGaugeDensityFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R
            (fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z)) y j)) =
      (fun y => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n
            (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z))) y j))
    (hCommon : ∀ y ∈ tsupport u, (q,(y,R y)) ∈ KJ ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (hGeometry : ∀ y ∈ tsupport u, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible) :
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
  extract_lets v etaInf Wlim F f
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Eta : ℕ → Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun n j y =>
    referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v y j
  let W : ℕ → R3 → SphereSobolev (1/2:ℝ) := fun n y =>
    referenceFiniteGaugePhysicalDensityHalfSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y
  have hHalf := referenceFiniteGaugePhysicalDensityHalfSection_graphLimit_of_same_source
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E
      g2 hg2 hreg q R hR u hu hc hSmooth hGraph hCommon hGeometry
  extract_lets v0 etaInf0 Wlim0 at hHalf
  have hVSupp : tsupport v ⊆ tsupport u := tsupport_comp_subset (map_zero Iin) u
  have hEtaSupp (n : ℕ) (j : Fin 3) : tsupport (Eta n j) ⊆ tsupport u :=
    (tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v j).trans hVSupp
  have hWEq (n : ℕ) :
      (fun y => referencePhysicalDensityHalfFromFirstSections
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R (Eta n) y) = W n :=
    funext (fun y => referencePhysicalDensityHalfFromFirstSections_eq_finiteGauge
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y)
  have hWSmooth (n : ℕ) : ContDiff ℝ ∞ (W n) := by
    have h := contDiff_referencePhysicalDensityHalfFromFirstSections_of_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg q R hR
        (Eta n) (hSmooth n) (tsupport u) (hEtaSupp n) hGeometry
    exact (congrArg (fun V : R3 → SphereSobolev (1/2:ℝ) => ContDiff ℝ ∞ V) (hWEq n)).mp h
  have hWSupp (n : ℕ) : tsupport (W n) ⊆ tsupport u :=
    (tsupport_referenceFiniteGaugePhysicalDensityHalfSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v).trans hVSupp
  exact supported_weighted_half_graph_to_sphereL2
    g hg L q hO hD (tsupport u) hc W Wlim hWSmooth hHalf.1 hWSupp hHalf.2.2.1
      (fun n y => referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) y)
      (fun y => referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y)
      hHalf.2.2.2.2.1 hHalf.2.2.2.1 hHalf.2.2.2.2.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
