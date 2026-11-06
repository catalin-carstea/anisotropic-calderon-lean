import Calderon.ActualReferenceHighAdjointRadialNativeJets
import Calderon.ActualAdjointMovingBoundaryAction
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ClmInheritedStructureData
import Calderon.InheritedNormedStructureData
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual lower coordinate and Fhalf first jets, derived on the original domain. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


attribute [local irreducible] referenceAdjointHalfRadialFamily
  referenceLowerAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus
  sphereSobolevRadialDriftAdjointL sphereSobolevLinearCoordinateMulL
  referenceNativeMovingAdjointParametricCorrection

lemma deriv_referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_nativeFirstCorrection
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3) :
    deriv (fun t : ℝ => referenceLowerAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t)) i) 0 =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        ((sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ)
          (referenceCenterDrift g L q y)).comp
          (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
            (EuclideanSpace.single i 1))) := by
  let S := fun t : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let D := sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)
  let M := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)
  let T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    -(∑ j : Fin 3, (sphereSobolevRotationL (1/2 : ℝ) j i).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)))
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hParam : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hSmooth : ContDiffAt ℝ ∞ S 0 :=
    ((contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
        (hOpen.mem_nhds hp)).comp 0 hParam.contDiffAt
  have hValue : deriv S 0 = J.comp D :=
    deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hS : HasDerivAt S (J.comp D) 0 :=
    ((hSmooth.differentiableAt (by simp)).hasDerivAt).congr_deriv hValue
  have hProduct := hS.clm_comp (hasDerivAt_const (0 : ℝ) M)
  have hAll := (hasDerivAt_const (0 : ℝ) T).add hProduct
  have hAllPoint := hAll.congr_of_eventuallyEq
    (f₁ := fun t : ℝ => T + (S t).comp M)
    (Filter.Eventually.of_forall (fun _ => rfl))
  have hDerived := hAllPoint.deriv
  have hDerivative : deriv (fun t : ℝ => referenceLowerAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t)) i) 0 =
      (J.comp D).comp M := by
    simpa (config := { instances := true }) only
      [referenceLowerAdjointCoordinateBoundaryFamily,S,T,M,Pi.add_apply,
        ContinuousLinearMap.comp_zero,add_zero,zero_add,
        real_nontriviallyNormedField_normedField_eq,
        clm_normedAddCommGroup_seminormedAddCommGroup_eq,
        clm_seminormedAddCommGroup_topologicalSpace_eq,
        clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq]
      using hDerived
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => A u) hDerivative
  simpa (config := { instances := true }) only
    [ContinuousLinearMap.comp_apply,J,D,M] using hu

lemma referenceLowerAdjointMoving_firstJet_eq_nativeParametricCorrection
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (hr : R y ≠ 0) (i : Fin 3) :
    (deriv (fun t : ℝ => referenceLowerAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t)) i) 0) +
      (R y * referenceRadiusHorizontalLogDerivative g L q R y i) •
        (deriv (fun t : ℝ => referenceAdjointHalfRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0) =
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
        ((q,y),fderiv ℝ R y) i) := by
  have hCoordinate := deriv_referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
  have hRadial := deriv_referenceAdjointHalfRadialFamily_zero_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hScalar := referenceRadius_mul_horizontalLogDerivative_eq_fderiv g L q R hR y hr i
  apply ContinuousLinearMap.ext
  intro u
  have hC := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => A u) hCoordinate
  have hS := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ]
    SphereSobolev (-(1/2 : ℝ)) => A u) hRadial
  simp (config := { instances := true }) only [ContinuousLinearMap.comp_apply] at hC hS
  have hValue := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) =>
    x + (R y * referenceRadiusHorizontalLogDerivative g L q R y i) • z) hC hS
  have hWeight := congrArg (fun c : ℝ =>
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
      ((sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ)
        (referenceCenterDrift g L q y))
        ((sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single i 1)) u)) +
      c • (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
        ((sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ)
          (referenceCenterDrift g L q y)) u)) hScalar
  have hEnd := hValue.trans hWeight
  simpa (config := { instances := true }) only
    [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,referenceNativeMovingAdjointParametricCorrection,
      map_add,map_smul] using hEnd

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.deriv_referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_nativeFirstCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMoving_firstJet_eq_nativeParametricCorrection
