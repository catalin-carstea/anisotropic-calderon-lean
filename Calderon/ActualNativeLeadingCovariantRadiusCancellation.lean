import Calderon.ActualNativeZeroCoordinateCovariantTransport
import Calderon.ActualNativeMovingAdjointFiniteJ

/-! Exact original frame/covector cancellation, with no jet, gain or image premise. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  NormalCoordinatesFrame

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointMovingBoundaryActionFamily
  referenceLowerAdjointMovingBoundaryActionFamily referenceRadiusHorizontalLogDerivative
  sphereHighHarmonicDerivativeTransposeL sphereSobolevAngularCoordinateTransposeL
  sphereSobolevShiftedDegreeL sphereSobolevInclusionL
  referenceNativeMovingAdjointParametricCorrection


attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus
  referenceHighHorizontalAction referenceLowerHorizontalAction
  referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceMetricGramFrame referenceFrameConnectionCoefficient

include hData hg hcalc τ0

lemma referenceLeadingRadiusAngularAction_covariant_cancellation
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (i j : Fin 3) (hr : R y ≠ 0)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (hu : DifferentiableAt ℝ u y) :
    referenceLowerHorizontalAction g L q
      (fun x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL
        hF hO hD (3/2 : ℝ) j (u x)) y i +
    referenceRadiusHorizontalLogDerivative g L q R y i •
      sphereSobolevShiftedDegreeL (1/2 : ℝ)
        ((R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y)) -
    (∑ k : Fin 3,
      referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j •
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          ((R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u y))) =
    (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j
      (referenceHighHorizontalAction g L q u y i +
        referenceRadiusHorizontalLogDerivative g L q R y i •
          sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ah := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
  let Al := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j
  let X := referenceMetricGramFrame g L (q,y) i
  let f := referenceRadiusHorizontalLogDerivative g L q R y i
  let V := fun x : R3 => (R x)⁻¹ • Ah j (u x)
  let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y X k j
  let G : SphereSobolev (-(1/2 : ℝ)) := ∑ k : Fin 3, Gamma k • Iout (Ah k (u y))
  have hFrame : conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i) = X :=
    (congrArg (fun T : R3 →L[ℝ] R3 => T (coordinateVector i))
      (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,y))).trans
        ((frameOperator_coordinateVector _ i).trans
          (conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q y i))
  have hf : f = (R y)⁻¹ * fderiv ℝ R y X := by
    dsimp only [f]
    unfold referenceRadiusHorizontalLogDerivative
    rw [fderiv_log_radius_apply R hR y _ hr,hFrame]
  have hInvScalar : -(R y ^ 2)⁻¹ * fderiv ℝ R y X = -((R y)⁻¹ * f) := by
    rw [hf]
    rw [← inv_pow]
    ring
  have hRDerivative := (hR.differentiable (by simp) y).hasFDerivAt
  have hInvDerivative := (hasDerivAt_inv hr).comp_hasFDerivAt y hRDerivative
  have hASection := (Ah j).hasFDerivAt.comp y hu.hasFDerivAt
  have hProduct := hInvDerivative.smul hASection
  have hEval := congrArg
    (fun T : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) => Iout (T X)) hProduct.fderiv
  have hDerivative : Iout (fderiv ℝ V y X) =
      (R y)⁻¹ • Iout (Ah j (fderiv ℝ u y X)) +
        (-((R y)⁻¹*f)) • Iout (Ah j (u y)) := by
    simpa (config := { instances := true }) only
      [Function.comp_def,Pi.smul_def',V,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,
        map_add,map_smul,smul_eq_mul,hInvScalar] using hEval
  have hp0 := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hp0Fields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp0
  unfold referenceRadialEndpointInvertibleLocus at hp0Fields
  have hHighZero : referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j = Ah j := by
    simpa (config := { instances := true }) only
      [sphereHighHarmonicDerivativeTransposeL,sphereSobolevAngularCoordinateTransposeL,Ah]
      using (referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy j)
  have hLowZero := referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy j
  have hCoord := referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,0)) j hp0Fields.2.1
  have hA (v : SphereSobolev (3/2 : ℝ)) : Iout (Ah j v) = Al (Iin v) := by
    have h1 := congrArg Iout (congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T v) hHighZero)
    have h2 := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v) hCoord
    have h3 := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (Iin v)) hLowZero
    exact h1.symm.trans (h2.trans h3)
  have hOmega : referenceLowerHorizontalAngularL g L q y i (Ah j (u y)) =
      G + Al (referenceHighHorizontalAngularL g L q y i (u y)) :=
    (sub_eq_iff_eq_add).mp (referenceHorizontalAngular_angularTranspose_commutator
      hF hO hD g hg L q y i j (u y))
  have hDegree : sphereSobolevShiftedDegreeL (1/2 : ℝ) (Ah j (u y)) =
      Iout (Ah j (u y)) + Al (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)) :=
    (sub_eq_iff_eq_add).mp (sphereSobolevShiftedDegree_angularTranspose_commutator
      hF hO hD j (u y))
  have hHorizontal : referenceLowerHorizontalAction g L q V y i =
      (R y)⁻¹ • Iout (Ah j (fderiv ℝ u y X)) +
      (-((R y)⁻¹*f)) • Iout (Ah j (u y)) +
      (R y)⁻¹ • referenceLowerHorizontalAngularL g L q y i (Ah j (u y)) := by
    have h := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      z + referenceLowerHorizontalAngularL g L q y i ((R y)⁻¹ • Ah j (u y))) hDerivative
    simpa (config := { instances := true }) only
      [referenceLowerHorizontalAction,V,X,Iout,map_smul] using h
  have hConnection : (∑ k : Fin 3, Gamma k • Iout ((R y)⁻¹ • Ah k (u y))) =
      (R y)⁻¹ • G := by
    simp only [G,map_smul,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact smul_comm (Gamma k) (R y)⁻¹ _
  have hLeft := congrArg₂ (fun z c : SphereSobolev (-(1/2 : ℝ)) => z-c)
    (congrArg₂ (fun h b : SphereSobolev (-(1/2 : ℝ)) => h+f • b)
      hHorizontal ((sphereSobolevShiftedDegreeL (1/2 : ℝ)).map_smul
        (R y)⁻¹ (Ah j (u y)))) hConnection
  have hRight : (R y)⁻¹ • Al (referenceHighHorizontalAction g L q u y i +
      f • sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)) =
      (R y)⁻¹ • (Iout (Ah j (fderiv ℝ u y X)) +
        Al (referenceHighHorizontalAngularL g L q y i (u y)) +
        f • Al (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y))) := by
    simp (config := { instances := true }) only
      [referenceHighHorizontalAction,map_add,map_smul,X,← hA,Iin]
  have hAlgebra :
      ((R y)⁻¹ • Iout (Ah j (fderiv ℝ u y X)) +
        (-((R y)⁻¹*f)) • Iout (Ah j (u y)) +
        (R y)⁻¹ • referenceLowerHorizontalAngularL g L q y i (Ah j (u y)) +
        f • ((R y)⁻¹ • sphereSobolevShiftedDegreeL (1/2 : ℝ) (Ah j (u y)))) -
        (R y)⁻¹ • G =
      (R y)⁻¹ • (Iout (Ah j (fderiv ℝ u y X)) +
        Al (referenceHighHorizontalAngularL g L q y i (u y)) +
        f • Al (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y))) := by
    have hOmegaScaled := congrArg
      (fun v : SphereSobolev (-(1/2 : ℝ)) => (R y)⁻¹ • v) hOmega
    have hDegreeScaled := congrArg
      (fun v : SphereSobolev (-(1/2 : ℝ)) => f • ((R y)⁻¹ • v)) hDegree
    have hReplace := congrArg₂
      (fun v z : SphereSobolev (-(1/2 : ℝ)) =>
        ((R y)⁻¹ • Iout (Ah j (fderiv ℝ u y X)) +
          (-((R y)⁻¹*f)) • Iout (Ah j (u y)) + v + z) - (R y)⁻¹ • G)
      hOmegaScaled hDegreeScaled
    exact hReplace.trans (by module)
  simpa (config := { instances := true }) only [V,Ah,Al,X,G,Gamma,Iin,Iout,f]
    using hLeft.trans (hAlgebra.trans hRight.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLeadingRadiusAngularAction_covariant_cancellation
