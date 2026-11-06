import Calderon.ActualFiniteFirstSectionFiveHalfIdentity
import Calderon.ActualFiveHalfDensityFirstGraph
import Calderon.ActualPhysicalDensityOperatorLocality

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier SmoothMetricFrame
attribute [local irreducible] referenceRadialEndpointInvertibleLocus referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  referenceFiveHalfAdjointCoordinateBoundaryFamily referenceHighAdjointCoordinateBoundaryFamily
  ReferenceJacobiCompactExtensionRoom.fiveHalfMultiplierFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)

attribute [local irreducible] referenceFiveHalfAdjointJacobiBoundaryInRoom

attribute [local irreducible] referenceFiveHalfAdjointMovingBoundaryInRoom referenceFiveHalfHorizontalAngularL referenceMetricGramFrame

open ActualFiniteHarmonicCore ReferenceDensityBounds ConformalDepth WeightedBaseSpectral
variable {KG : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
attribute [local irreducible] referenceFiveHalfDensityFirstActionInRoom referenceFiniteGaugeDensityFirstSection
  referenceHighDensityFirstAction sphereSobolevInclusionL sphereSobolevPartialSumL

lemma referenceDensityFirstActionInRoom_global_compatibility_of_support
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (i : Fin 3)
    (hCommon : ∀ y ∈ tsupport u, (q,(y,R y)) ∈ K ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    (fun y => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (referenceFiveHalfDensityFirstActionInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i)) =
    (fun y => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z)) y i) := by
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let v : R3 → SphereSobolev (3/2:ℝ) := fun y => Iin (u y)
  let eta : R3 → SphereSobolev (3/2:ℝ) := fun y => referenceFiveHalfDensityFirstActionInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i
  let X : R3 → SphereSobolev (1/2:ℝ) := fun y => referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i
  have hEtaSupp : tsupport eta ⊆ tsupport u :=
    tsupport_referenceFiveHalfDensityFirstActionInRoom_subset
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u i
  have hVSupp : tsupport v ⊆ tsupport u := tsupport_comp_subset (map_zero Iin) u
  have hXSupp : tsupport X ⊆ tsupport u :=
    (tsupport_referenceHighDensityFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v i).trans hVSupp
  funext y
  by_cases hy : y ∈ tsupport u
  · exact referenceDensityFirstActionInRoom_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R u y i
        (hu.contDiffAt.differentiableAt (by simp)) (hCommon y hy).1 (hCommon y hy).2
  · have hEtaZero : eta y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hEtaSupp h))
    have hXZero : X y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hXSupp h))
    change Iout (eta y) = X y
    exact (congrArg Iout hEtaZero).trans ((map_zero Iout).trans hXZero.symm)

lemma referenceFiniteGaugeDensityFirstSection_graphLimits_of_same_source
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hR : ContDiff ℝ ∞ R) (i : Fin 3)
    (hGraph : ∀ n : ℕ,
      (fun y => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
        (referenceFiniteGaugeDensityFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R
            (fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z)) y i)) =
      (fun y => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n
            (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z))) y i))
    (hCommon : ∀ y ∈ tsupport u, (q,(y,R y)) ∈ K ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (hRegular : ∀ y ∈ tsupport u, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let v : R3 → SphereSobolev (3/2:ℝ) := fun y =>
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
    let eta : ℕ → R3 → SphereSobolev (3/2:ℝ) := fun n y =>
      referenceFiniteGaugeDensityFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v y i
    let etaInf : R3 → SphereSobolev (3/2:ℝ) := fun y =>
      referenceFiveHalfDensityFirstActionInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i
    ContDiff ℝ ∞ etaInf ∧ HasCompactSupport etaInf ∧
    (∀ n : ℕ, eta n = fun y => referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y i) ∧
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) * ‖eta n y - etaInf y‖^2)
      atTop (𝓝 0) ∧
    ∀ X : R3, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖fderiv ℝ (eta n) y X - fderiv ℝ etaInf y X‖^2) atTop (𝓝 0) := by
  let v : R3 → SphereSobolev (3/2:ℝ) := fun y =>
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
  let eta : ℕ → R3 → SphereSobolev (3/2:ℝ) := fun n y =>
    referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v y i
  have hEq (n : ℕ) : eta n = fun y => referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y i :=
    referenceFiniteGaugeDensityFirstSection_eq_fiveHalfInRoom_of_graph
      g L y0 Φ B ε C ρ H a w hData hg E G hcalc hF hO hD τ0 hreg n q R u hu i (hGraph n) hCommon
  let etaInf : R3 → SphereSobolev (3/2:ℝ) := fun y =>
    referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i
  have hLimit := tendsto_integral_referenceFiveHalfDensityFirstActionInRoom_partialSum
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R u hu hc hR i hRegular
  refine ⟨contDiff_referenceFiveHalfDensityFirstActionInRoom_of_support
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R u i hu hR hRegular,
    hasCompactSupport_referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u i hc,hEq,?_,?_⟩
  · have hSeq : (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) * ‖eta n y - etaInf y‖^2) =
        (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
          ‖referenceFiveHalfDensityFirstActionInRoom
            g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
              (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y i - etaInf y‖^2) := by
      funext n
      exact congrArg (fun f : R3 → SphereSobolev (3/2:ℝ) =>
        ∫ y, referenceDensityFamily g L (q,y) * ‖f y - etaInf y‖^2) (hEq n)
    exact (congrArg (fun f : ℕ → ℝ => Tendsto f atTop (𝓝 (0:ℝ))) hSeq).mpr hLimit.1
  · intro X
    have hSeq : (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
        ‖fderiv ℝ (eta n) y X - fderiv ℝ etaInf y X‖^2) =
        (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
          ‖fderiv ℝ (fun y => referenceFiveHalfDensityFirstActionInRoom
            g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
              (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y i) y X -
              fderiv ℝ etaInf y X‖^2) := by
      funext n
      exact congrArg (fun f : R3 → SphereSobolev (3/2:ℝ) =>
        ∫ y, referenceDensityFamily g L (q,y) * ‖fderiv ℝ f y X - fderiv ℝ etaInf y X‖^2) (hEq n)
    exact (congrArg (fun f : ℕ → ℝ => Tendsto f atTop (𝓝 (0:ℝ))) hSeq).mpr (hLimit.2 X)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
