import Calderon.ActualReferenceNormalizedAdjointDefect
import Calderon.ActualReferenceGaugeTangentReciprocalSkew

/-! Actual positive scalar residual retained. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceGaugeNormalHalfSecondRemainder
  referenceGaugeTangentReciprocalResidualHalfFamily referenceGaugeTangentReciprocalResidualNegativeFamily
  referenceGaugeTangentReciprocalSkewFamily referenceGaugeTangentSecondDefectFamily
  referenceLowerRadialTraceSecondRemainder sphereLowerDistributionalTranspose sphereSobolevInclusionL
  referenceRadialEndpointInvertibleLocus

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Q : Set (ℝ × (R3 × ℝ))) (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)

def referenceNormalizedAdjointHalfDefectFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  referenceGaugeNormalHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 +
    referenceGaugeTangentReciprocalResidualHalfFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p

attribute [local irreducible] referenceNormalizedAdjointHalfDefectFamily

theorem referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_skew_add_half
    (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hReciprocal : (q,(y,r)) ∈ R.parameterRoom) :
    sphereLowerDistributionalTranspose (referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r) -
      referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r =
    referenceGaugeTangentReciprocalSkewFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r)) +
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceNormalizedAdjointHalfDefectFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r))) := by
  let p := (q,(y,r))
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Dn := referenceGaugeNormalHalfSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r
  let Bh := referenceGaugeTangentReciprocalResidualHalfFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p
  let Bn := referenceGaugeTangentReciprocalResidualNegativeFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p
  let V := referenceGaugeTangentReciprocalSkewFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p
  let U := referenceGaugeTangentSecondDefectFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hBase := referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_normal_add_tangent
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel q hq y hy r hSegment
  have hU : U = V+Bn.comp J := by
    dsimp only [U]
    unfold referenceGaugeTangentSecondDefectFamily
    exact referenceGaugeTangentSecond_right_inverse_defect_eq_skew_add_residual
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p hReciprocal
  have hCompat : J.comp Bh = Bn.comp J :=
    referenceGaugeTangentReciprocalResidual_half_negative_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p
  have hAdd : J.comp (Dn+Bh) = J.comp Dn+J.comp Bh := by
    apply ContinuousLinearMap.ext
    intro u
    exact J.map_add (Dn u) (Bh u)
  have hAlgebra : J.comp Dn+U = V+J.comp (Dn+Bh) :=
    (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) => J.comp Dn+Z) hU).trans
      ((congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => J.comp Dn+(V+Z)) hCompat.symm).trans
          ((add_left_comm (J.comp Dn) V (J.comp Bh)).trans
            (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ]
              SphereSobolev (-(1/2 : ℝ)) => V+Z) hAdd.symm)))
  unfold referenceNormalizedAdjointHalfDefectFamily
  exact hBase.trans hAlgebra

theorem sphereSobolevDualPairing_referenceNormalizedAdjointHalfDefect_skew
    (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hReciprocal : (q,(y,r)) ∈ R.parameterRoom)
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceNormalizedAdjointHalfDefectFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r)) u)) v =
    -sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceNormalizedAdjointHalfDefectFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r)) v)) u := by
  let E := referenceLowerRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let D := referenceNormalizedAdjointHalfDefectFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r))
  let V := referenceGaugeTangentReciprocalSkewFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r))
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hDef := referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_skew_add_half
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R hKernel q hq y hy r hSegment hReciprocal
  have hU : sphereLowerDistributionalTranspose E u-E u = V u+J (D u) :=
    congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z u) hDef
  have hV : sphereLowerDistributionalTranspose E v-E v = V v+J (D v) :=
    congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z v) hDef
  have hPairU := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => inner ℝ v z) hU
  have hPairV := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => inner ℝ u z) hV
  have hTU := sphereSobolevDualPairing_lower_distributionalTranspose E v u
  have hTV := sphereSobolevDualPairing_lower_distributionalTranspose E u v
  have hSkew := sphereSobolevDualPairing_referenceGaugeTangentReciprocalSkew
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r)) u v
  change inner ℝ v (V u) = -inner ℝ u (V v) at hSkew
  change inner ℝ u (E v) = inner ℝ v (sphereLowerDistributionalTranspose E u) at hTU
  change inner ℝ v (E u) = inner ℝ u (sphereLowerDistributionalTranspose E v) at hTV
  simp only [inner_sub_right,inner_add_right] at hPairU hPairV
  change inner ℝ (J (D u)) v = -inner ℝ (J (D v)) u
  rw [real_inner_comm v (J (D u)),real_inner_comm u (J (D v))]
  linarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalizedAdjointHalfDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_skew_add_half
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceNormalizedAdjointHalfDefect_skew
