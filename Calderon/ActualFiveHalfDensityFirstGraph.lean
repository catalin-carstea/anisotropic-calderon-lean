import Calderon.ActualFiveHalfDensityFirstInRoom
import Calderon.FirstOrderFrameCoordinateDictionary
import Calderon.FirstOrderCoordinateSpectralConvergence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral

private def coefficientSum {F : Type*} [AddCommGroup F] (a b : F) : F := a+b
private lemma contDiffAt_coefficientSum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : R3 → F) (y : R3) (ha : ContDiffAt ℝ ∞ a y) (hb : ContDiffAt ℝ ∞ b y) :
    ContDiffAt ℝ ∞ (fun z => coefficientSum (a z) (b z)) y := ha.add hb

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)
attribute [local irreducible] referenceFiveHalfAdjointMovingBoundaryInRoom
  referenceFiveHalfHorizontalAngularL referenceMetricGramFrame referenceRadialEndpointInvertibleLocus

def referenceFiveHalfDensityZerothInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  coefficientSum (referenceFiveHalfHorizontalAngularL g L q y i)
    (referenceFiveHalfAdjointMovingBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i)

lemma contDiffAt_referenceFiveHalfDensityZerothInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z => referenceFiveHalfDensityZerothInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R z i) y := by
  have hOmega := (contDiff_referenceFiveHalfHorizontalAngularL g hg L q i).contDiffAt (x := y)
  have hMove := (contDiffAt_referenceFiveHalfAdjointMovingBoundaryInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg R (q,y) i hR hr hp).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  exact contDiffAt_coefficientSum _ _ y hOmega hMove

lemma referenceFiveHalfDensityFirstActionInRoom_coordinate_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (5/2:ℝ)) (y : R3) (i : Fin 3) :
    referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i =
    firstOrderCoordinateAction
      (fun k z => (referenceMetricGramFrame g L (q,z) i) k •
        sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))
      (fun z => referenceFiveHalfDensityZerothInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R z i) u y := by
  have hFrame := firstOrderCoordinateAction_frame_eq
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))
    (fun z => referenceMetricGramFrame g L (q,z) i)
    (fun z => referenceFiveHalfDensityZerothInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R z i) u y
  have hRhs : firstOrderCoordinateAction
      (fun k z => (referenceMetricGramFrame g L (q,z) i) k •
        sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))
      (fun z => referenceFiveHalfDensityZerothInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R z i) u y =
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
        (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i)) +
      (referenceFiveHalfHorizontalAngularL g L q y i (u y) +
        referenceFiveHalfAdjointMovingBoundaryInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i (u y)) := by
    simpa only [referenceFiveHalfDensityZerothInRoom,coefficientSum,
      ContinuousLinearMap.add_apply] using hFrame
  have hDef : referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i =
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
        (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i)) +
        referenceFiveHalfHorizontalAngularL g L q y i (u y)) +
        referenceFiveHalfAdjointMovingBoundaryInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i (u y) := rfl
  exact hDef.trans ((add_assoc _ _ _).trans hRhs.symm)

lemma tendsto_integral_referenceFiveHalfDensityFirstActionInRoom_partialSum
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hR : ContDiff ℝ ∞ R) (i : Fin 3)
    (hRoom : ∀ y ∈ tsupport u, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖referenceFiveHalfDensityFirstActionInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
            (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y i -
        referenceFiveHalfDensityFirstActionInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i‖^2)
      atTop (𝓝 0) ∧
    ∀ X : R3, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖fderiv ℝ (fun y => referenceFiveHalfDensityFirstActionInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
            (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y i) y X -
        fderiv ℝ (fun y => referenceFiveHalfDensityFirstActionInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i) y X‖^2)
      atTop (𝓝 0) := by
  let A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
    fun k z => (referenceMetricGramFrame g L (q,z) i) k •
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Z : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
    fun z => referenceFiveHalfDensityZerothInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R z i
  have hA (k : Fin 3) : ContDiff ℝ ∞ (A k) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp
      (contDiff_referenceMetricGramFrame_slice g hg L q i)).smul contDiff_const
  have hZ (y : R3) (hy : y ∈ tsupport u) : ContDiffAt ℝ ∞ Z y :=
    contDiffAt_referenceFiveHalfDensityZerothInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R y i
        hR.contDiffAt (hRoom y hy).1 (hRoom y hy).2
  have hFun (v : R3 → SphereSobolev (5/2:ℝ)) :
      (fun y => referenceFiveHalfDensityFirstActionInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R v y i) =
      firstOrderCoordinateAction A Z v := funext (fun y =>
        referenceFiveHalfDensityFirstActionInRoom_coordinate_eq
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R v y i)
  constructor
  · have h := tendsto_integral_firstOrderCoordinateAction_partialSum_sub_sq
      g hg L q A Z u hu hc (fun k y hy => (hA k).continuous.continuousAt)
        (fun y hy => (hZ y hy).continuousAt)
    simpa only [← hFun] using h
  · intro X
    have h := tendsto_integral_fderiv_firstOrderCoordinateAction_partialSum_sub_sq
      g hg L q A Z u hu hc (fun k y hy => (hA k).contDiffAt)
        (fun y hy => hZ y hy) X
    simpa only [← hFun] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
