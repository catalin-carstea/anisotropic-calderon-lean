import Calderon.ActualHighAdjointMovingTraceNativeDecomposition
import Calderon.ActualNativeLeadingAngularCancellation
import Calderon.ActualPhysicalDensityOperator

/-! Actual low zero and high base germ, then genuine zero covariant derivative. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceAdjointHalfRadialFamily referenceLowerRadialEndpointFamily
  referenceRadialEndpointInvertibleLocus referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily sphereSobolevAngularCoordinateTransposeL
  sphereLowerDistributionalTranspose referenceHighHorizontalAngularL referenceLowerHorizontalAngularL

lemma referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3) :
    referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hpFields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp
  unfold referenceRadialEndpointInvertibleLocus at hpFields
  have hTranspose := sphereLowerDistributionalTranspose_referenceLowerRadial
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,0)) hpFields.2.1
  have hPrimal := referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hValue : referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) :=
    hTranspose.symm.trans ((congrArg sphereLowerDistributionalTranspose hPrimal).trans
      sphereLowerDistributionalTranspose_shiftedDegree_half)
  have hCoordinate := congrArg
    (fun S : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      -(∑ j : Fin 3, (sphereSobolevRotationL (1/2 : ℝ) j i).comp
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1))) +
      S.comp (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single i 1))) hValue
  simpa (config := { instances := true }) only
    [referenceLowerAdjointCoordinateBoundaryFamily,sphereSobolevAngularCoordinateTransposeL]
    using hCoordinate

lemma referenceHighAdjointCoordinateBoundaryFamily_zero_eventually_eq_angularTranspose
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ < ρ) (i : Fin 3) :
    (fun x : R3 => referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,0)) i) =ᶠ[𝓝 y]
      (fun _ : R3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i) := by
  have hContinuous : Continuous (fun x : R3 => ‖x-y0‖) :=
    (continuous_id.sub continuous_const).norm
  have hOpen : IsOpen {x : R3 | ‖x-y0‖ < ρ} := isOpen_lt hContinuous continuous_const
  filter_upwards [hOpen.mem_nhds hy] with x hx
  have hZero := referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq x hx.le i
  simpa (config := { instances := true }) only
    [sphereHighHarmonicDerivativeTransposeL,sphereSobolevAngularCoordinateTransposeL] using hZero

lemma referenceAdjointCoordinateBoundaryFamily_zero_covariantDerivative_eq_zero
    (hg : IsAdmissibleMetric g) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ < ρ)
    (i j : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      ((fderiv ℝ (fun x : R3 => referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,0)) j) y
          (referenceMetricGramFrame g L (q,y) i)) u) +
    referenceLowerHorizontalAngularL g L q y i
      (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j u) -
    referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
      (referenceHighHorizontalAngularL g L q y i u) -
    (∑ k : Fin 3,
      referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j •
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) k u)) = 0 := by
  let I := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let X := referenceMetricGramFrame g L (q,y) i
  let high := fun k : Fin 3 => referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) k
  let low := referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
  let A := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
  let Al := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j
  let Oh := referenceHighHorizontalAngularL g L q y i
  let Ol := referenceLowerHorizontalAngularL g L q y i
  let gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y X k j
  have hNear := referenceHighAdjointCoordinateBoundaryFamily_zero_eventually_eq_angularTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy j
  have hCurveDeriv := hNear.fderiv_eq (𝕜 := ℝ)
  have hConstant : fderiv ℝ
      (fun _ : R3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j) y = 0 :=
    fderiv_const_apply _
  have hCurveZero := hCurveDeriv.trans hConstant
  have hDerivative : I ((fderiv ℝ (fun x : R3 => referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,0)) j) y X) u) = 0 := by
    have h := congrArg
      (fun T : R3 →L[ℝ] (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) =>
        I ((T X) u)) hCurveZero
    simpa (config := { instances := true }) only [ContinuousLinearMap.zero_apply,map_zero] using h
  have hHigh (k : Fin 3) : high k = A k :=
    (referenceHighAdjointCoordinateBoundaryFamily_zero_eventually_eq_angularTranspose
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy k).eq_of_nhds
  have hLow : low = Al := referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy.le j
  have h1 := congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    Ol (T u)) (hHigh j)
  have h2 := congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
    T (Oh u)) hLow
  have hLeft := congrArg₂ (fun v z : SphereSobolev (-(1/2 : ℝ)) => v-z) h1 h2
  have hRight : (∑ k : Fin 3, gamma k • I (high k u)) =
      ∑ k : Fin 3, gamma k • I (A k u) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      gamma k • I (T u)) (hHigh k)
  have hNative := referenceHorizontalAngular_angularTranspose_commutator hF hO hD
    g hg L q y i j u
  have hAngular : Ol (high j u)-low (Oh u) = ∑ k : Fin 3, gamma k • I (high k u) :=
    hLeft.trans (hNative.trans hRight.symm)
  have hSub := congrArg (fun d : SphereSobolev (-(1/2 : ℝ)) =>
    d + Ol (high j u)-low (Oh u)-(∑ k : Fin 3, gamma k • I (high k u))) hDerivative
  have hEnd : (0 : SphereSobolev (-(1/2 : ℝ))) + Ol (high j u)-low (Oh u)-
      (∑ k : Fin 3, gamma k • I (high k u)) = 0 := by
    simpa only [zero_add] using (sub_eq_zero.mpr hAngular)
  simpa (config := { instances := true }) only [I,X,high,low,Oh,Ol,gamma]
    using hSub.trans hEnd

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointCoordinateBoundaryFamily_zero_eventually_eq_angularTranspose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointCoordinateBoundaryFamily_zero_covariantDerivative_eq_zero
