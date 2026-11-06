import Calderon.ActualFiveHalfAdjointMovingInRoomCompatibility
import Calderon.ActualCovariantDensityFirstActions

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

def referenceFiveHalfDensityFirstActionInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (5/2:ℝ)) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2:ℝ) :=
  referenceFiveHalfHorizontalAction g L q u y i +
    referenceFiveHalfAdjointMovingBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R (q,y) i (u y)

lemma referenceDensityFirstActionInRoom_fivehalf_threehalf_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (5/2:ℝ)) (y : R3) (i : Fin 3)
    (hu : DifferentiableAt ℝ u y) (hp : (q,(y,R y)) ∈ K)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (referenceFiveHalfDensityFirstActionInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i) =
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u x)) y i := by
  have hH := referenceHorizontalAction_fivehalf_threehalf_compatibility g L q u y i hu
  have hM := DFunLike.congr_fun
    (referenceAdjointMovingBoundaryInRoom_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg R (q,y) i hp hWeak) (u y)
  exact (map_add (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) _ _).trans
    (congrArg₂ (fun a b : SphereSobolev (1/2:ℝ) => a+b) hH hM)

lemma contDiffAt_referenceFiveHalfDensityFirstActionInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (5/2:ℝ)) (y : R3) (i : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun x => referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u x i) y := by
  have hHorizontal := contDiffAt_referenceFiveHalfHorizontalAction g hg L q u y i hu
  have hMoving := (contDiffAt_referenceFiveHalfAdjointMovingBoundaryInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg R (q,y) i hR hr hp).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  exact hHorizontal.add (hMoving.clm_apply hu)

lemma tsupport_referenceFiveHalfDensityFirstActionInRoom_subset
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (5/2:ℝ)) (i : Fin 3) :
    tsupport (fun y => referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i) ⊆ tsupport u := by
  classical
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hValue : u y = 0 := image_eq_zero_of_notMem_tsupport hOutside
  have hDerivative : fderiv ℝ u y = 0 := fderiv_of_notMem_tsupport ℝ hOutside
  apply hy
  simp only [referenceFiveHalfDensityFirstActionInRoom,referenceFiveHalfHorizontalAction,
    hValue,hDerivative,ContinuousLinearMap.zero_apply,map_zero,add_zero]

lemma contDiff_referenceFiveHalfDensityFirstActionInRoom_of_support
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (5/2:ℝ)) (i : Fin 3)
    (hu : ContDiff ℝ ∞ u) (hR : ContDiff ℝ ∞ R)
    (hRoom : ∀ y ∈ tsupport u, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiff ℝ ∞ (fun y => referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i) := by
  let η : R3 → SphereSobolev (3/2:ℝ) := fun y => referenceFiveHalfDensityFirstActionInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i
  have hSupp : tsupport η ⊆ tsupport u :=
    tsupport_referenceFiveHalfDensityFirstActionInRoom_subset
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u i
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport u
  · exact contDiffAt_referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R u y i
        hu.contDiffAt hR.contDiffAt (hRoom y hy).1 (hRoom y hy).2
  · have hyη : y ∉ tsupport η := fun h => hy (hSupp h)
    have hZero : η =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (3/2:ℝ))) :=
      notMem_tsupport_iff_eventuallyEq.mp hyη
    exact (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : R3 => (0 : SphereSobolev (3/2:ℝ))) y).congr_of_eventuallyEq hZero

lemma hasCompactSupport_referenceFiveHalfDensityFirstActionInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (5/2:ℝ)) (i : Fin 3)
    (hu : HasCompactSupport u) :
    HasCompactSupport (fun y => referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y i) :=
  hu.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_referenceFiveHalfDensityFirstActionInRoom_subset
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
