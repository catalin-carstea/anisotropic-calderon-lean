import Calderon.ActualNativeMovingAdjointMixedJRealization
import Calderon.ActualNativeLeadingCovariantRadiusCancellation

/-! The mixed J at the negative physical endpoint. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus
  sphereHighHarmonicDerivativeTransposeL sphereSobolevAngularCoordinateTransposeL
  referenceNativeMovingAdjointParametricCorrection referenceNativeMovingAdjointHighMixedCorrection
  sphereSobolevInclusionL referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint

include hData hcalc τ0 in
lemma referenceAngularCoordinateTranspose_high_lower_inclusion
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3) (v : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i v) =
    sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ah := sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let Al := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
  have hp0 := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hp0Fields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp0
  unfold referenceRadialEndpointInvertibleLocus at hp0Fields
  have hHighZero : referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i = Ah := by
    simpa (config := { instances := true }) only
      [sphereHighHarmonicDerivativeTransposeL,sphereSobolevAngularCoordinateTransposeL,Ah]
      using (referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i)
  have hLowZero := referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
  have hCoord := referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,0)) i hp0Fields.2.1
  have h1 := congrArg Iout (congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T v) hHighZero)
  have h2 := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v) hCoord
  have h3 := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (Iin v)) hLowZero
  exact h1.symm.trans (h2.trans h3)

lemma referenceNativeMovingAdjointHighMixedCorrection_negative_inclusion
    (g2 : MatrixField) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (ell : R3 →L[ℝ] ℝ) (u : SphereSobolev (3/2 : ℝ)) :
    let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Ah := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
    let Al := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
    let Fh := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,y),ell) k
    let Fl := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),ell) k
    Iout (referenceNativeMovingAdjointHighMixedCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y ell u) =
    (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (Al i (Iin (Fh j u))+Iout (Fl i (Ah j u)))) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • Iout (Ah i u) := by
  dsimp only
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ah := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
  let Al := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
  let Fh := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,y),ell) k
  let Fl := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),ell) k
  let C0 := fun k : Fin 3 => referenceHighAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) k
  have hZero (i : Fin 3) : C0 i = Ah i := by
    simpa (config := { instances := true }) only
      [sphereHighHarmonicDerivativeTransposeL,sphereSobolevAngularCoordinateTransposeL,Ah,C0]
      using (referenceHighAdjointCoordinateBoundaryFamily_zero_eq_harmonicDerivativeTranspose
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i)
  have hAF (i j : Fin 3) : Iout (C0 i (Fh j u)) = Al i (Iin (Fh j u)) :=
    (congrArg Iout (congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T (Fh j u))
      (hZero i))).trans
      (referenceAngularCoordinateTranspose_high_lower_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i (Fh j u))
  have hFA (i j : Fin 3) : Iout (Fl i (C0 j u)) = Iout (Fl i (Ah j u)) :=
    congrArg (fun v : SphereSobolev (1/2 : ℝ) => Iout (Fl i v))
      (congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u) (hZero j))
  have hA (i : Fin 3) : Iout (C0 i u) = Iout (Ah i u) :=
    congrArg Iout (congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u) (hZero i))
  simp (config := { instances := true }) only
    [referenceNativeMovingAdjointHighMixedCorrection,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
      map_add,map_smul,map_sum]
  apply congrArg₂ (fun v z : SphereSobolev (-(1/2 : ℝ)) => v+z)
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg
      (fun v : SphereSobolev (-(1/2 : ℝ)) => referenceDensityPrincipalFrameCoefficient g g2 L q y i j • v)
      (congrArg₂ (fun v z : SphereSobolev (-(1/2 : ℝ)) => v+z) (hAF i j) (hFA i j))
  · apply Finset.sum_congr rfl
    intro i hi
    exact congrArg
      (fun v : SphereSobolev (-(1/2 : ℝ)) => normalizedSecondDriftFrameJoint g g2 L i (q,y) • v)
      (hA i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
