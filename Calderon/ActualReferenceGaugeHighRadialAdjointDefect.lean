import Calderon.ActualReferenceGaugeHalfTangentDefect
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.ActualReferenceRadialInvertibleEndpointCompatibility

/-! Genuine endpoint coherence, with the right reciprocal retained. -/
set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily referenceSharpRadialTraceFamily
  referenceLowerRadialEndpointFamily referenceGaugeNormalHalfCommutatorFamily
  referenceGaugeTangentSecondEndpointFamily referenceGaugeNormalHalfMultiplierFamily
  referenceRadialEndpointInvertibleLocus sphereSobolevInclusionL sphereLowerDistributionalTranspose

lemma referenceAdjointThreeHalfRadialFamily_sub_sharp_lower_defect
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ)
    (hp : (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (3/2 : ℝ)) :
    let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let T := referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))
    J (referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) f -
      referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) f) =
    J (referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) (I f)) +
    r^2 • ((T-sphereLowerDistributionalTranspose T)
      ((referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))).inverse (I f))) := by
  let p := (q,(y,r))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let A := referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let S := referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Sadj := referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hRoom := hp
  unfold referenceRadialEndpointInvertibleLocus at hRoom
  have hAdjoint : J (Sadj f) = sphereLowerDistributionalTranspose A (I f) :=
    (congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z f)
      (referenceAdjointRadialEndpointFamily_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p hRoom.2.1)).trans
      (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z (I f))
        (sphereLowerDistributionalTranspose_referenceLowerRadial
          g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD p hRoom.2.1).symm)
  have hPrimal : J (S f) = A (I f) :=
    congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z f)
      (referenceSharpRadialTraceFamily_lower_compatibility_of_isInvertible
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hRoom.2.2 hRoom.1 hRoom.2.1)
  have hDefect := congrArg
    (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z (I f))
    (referenceLowerRadialEndpoint_distributionalTranspose_sub_eq_half_add_tangent_second
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel q hq y hy r hp)
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply] at hDefect
  exact (J.map_sub (Sadj f) (S f)).trans
    ((congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z) hAdjoint hPrimal).trans hDefect)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointThreeHalfRadialFamily_sub_sharp_lower_defect
