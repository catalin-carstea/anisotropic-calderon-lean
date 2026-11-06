import Calderon.ActualPhysicalHalfFirstSectionGraphDictionary
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

theorem referenceFiniteGaugePhysicalDensityHalfSection_graphLimit_of_same_source
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
    ContDiff ℝ ∞ Wlim ∧ HasCompactSupport Wlim ∧ tsupport Wlim ⊆ tsupport u ∧
    (fun y => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (Wlim y)) =
      (fun y => referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y) ∧
    (∀ n : ℕ,
      (fun y => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceFiniteGaugePhysicalDensityHalfSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y)) =
      (fun y => referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) y)) ∧
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖referenceFiniteGaugePhysicalDensityHalfSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y - Wlim y‖^2)
      atTop (𝓝 0) := by
  extract_lets v etaInf Wlim
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Eta : ℕ → Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun n j y =>
    referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v y j
  have hNew (j : Fin 3) := referenceFiniteGaugeDensityFirstSection_graphLimits_of_same_source
    g L y0 Φ B ε C ρ H a w hData hg E G hcalc hF hO hD τ0 hreg q R u hu hc hR j
      (fun n => hGraph n j) hCommon (fun y hy => ⟨(hGeometry y hy).1,(hGeometry y hy).2.1⟩)
  have hVSupp : tsupport v ⊆ tsupport u := tsupport_comp_subset (map_zero Iin) u
  have hESupp (n : ℕ) (j : Fin 3) : tsupport (Eta n j) ⊆ tsupport u :=
    (tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v j).trans hVSupp
  have hLimSupp (j : Fin 3) : tsupport (etaInf j) ⊆ tsupport u :=
    tsupport_referenceFiveHalfDensityFirstActionInRoom_subset
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u j
  have hLimSmooth (j : Fin 3) : ContDiff ℝ ∞ (etaInf j) := (hNew j).1
  have hWeakGeometry : ∀ y ∈ tsupport u,
      (∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible) ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible :=
    fun y hy => ⟨(hGeometry y hy).2.2,(hCommon y hy).2⟩
  have hLimFirst (j : Fin 3) := referenceDensityFirstActionInRoom_global_compatibility_of_support
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R u hu j hCommon
  have hLimitGraph := sphereSobolevInclusionL_referencePhysicalDensityHalfFromFirstSections_global
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R v etaInf
      (tsupport u) (isClosed_tsupport u) hVSupp hLimSupp hLimSmooth hLimFirst hWeakGeometry
  have hCutSupp (n : ℕ) : tsupport (fun y => sphereSobolevPartialSumL (3/2:ℝ) n (v y)) ⊆ tsupport u :=
    (tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (3/2:ℝ) n)) v).trans hVSupp
  have hFiniteGraph (n : ℕ) := sphereSobolevInclusionL_referencePhysicalDensityHalfFromFirstSections_global
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R
      (fun y => sphereSobolevPartialSumL (3/2:ℝ) n (v y)) (Eta n)
      (tsupport u) (isClosed_tsupport u) (hCutSupp n) (hESupp n) (hSmooth n) (hGraph n) hWeakGeometry
  have hFinite (n : ℕ) :
      (fun y => referencePhysicalDensityHalfFromFirstSections
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R (Eta n) y) =
      (fun y => referenceFiniteGaugePhysicalDensityHalfSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y) :=
    funext (fun y => referencePhysicalDensityHalfFromFirstSections_eq_finiteGauge
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y)
  have hWSmooth : ContDiff ℝ ∞ Wlim := contDiff_referencePhysicalDensityHalfFromFirstSections_of_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg q R hR
      etaInf hLimSmooth (tsupport u) hLimSupp hGeometry
  have hWSupp : tsupport Wlim ⊆ tsupport u := tsupport_referencePhysicalDensityHalfFromFirstSections_subset
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R etaInf
      (tsupport u) (isClosed_tsupport u) hLimSupp
  have hConv := tendsto_integral_referencePhysicalDensityHalfFromFirstSections
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg q R hR (tsupport u) hc
      Eta etaInf hSmooth hLimSmooth hESupp hLimSupp hGeometry
      (fun j => (hNew j).2.2.2.1) (fun j => (hNew j).2.2.2.2)
  constructor
  · exact hWSmooth
  constructor
  · exact hc.of_isClosed_subset (isClosed_tsupport Wlim) hWSupp
  constructor
  · exact hWSupp
  constructor
  · exact hLimitGraph
  constructor
  · intro n
    exact (congrArg (fun F : R3 → SphereSobolev (1/2:ℝ) => fun y => J (F y)) (hFinite n)).symm.trans
      (hFiniteGraph n)
  · have hSeq :
        (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
          ‖referencePhysicalDensityHalfFromFirstSections
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R (Eta n) y - Wlim y‖^2) =
        (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
          ‖referenceFiniteGaugePhysicalDensityHalfSection
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y - Wlim y‖^2) := by
      funext n
      exact congrArg (fun F : R3 → SphereSobolev (1/2:ℝ) =>
        ∫ y, referenceDensityFamily g L (q,y) * ‖F y - Wlim y‖^2) (hFinite n)
    exact (congrArg (fun f : ℕ → ℝ => Tendsto f atTop (𝓝 (0:ℝ))) hSeq).mp hConv

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
