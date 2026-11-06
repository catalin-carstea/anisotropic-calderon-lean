import Calderon.ActualReferenceTwoAngleLowerTranspose
import Calderon.ActualReferenceTwoAngleMidpointCore
import Calderon.SphereSobolevMidpointPhysicalAdjunction

/-! Actual pointwise graphs and pivot of the paired two-angle adjoint midpoint. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace) (i j k l : Fin 3)

def referenceTwoAngleAdjointRadialEndpointPairFamily
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SphereSobolevEndpointPair :=
  (referenceTwoAngleAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t,
   referenceTwoAngleAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)

include hreg in
lemma referenceTwoAngleAdjointRadialEndpointPairFamily_mem_compatible
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    referenceTwoAngleAdjointRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t ∈ sphereSobolevCompatibleEndpoints := by
  let DH := referenceTwoAngleAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  change (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp DH = _
  have hNotation := sphereSobolevInclusionL_negative_half_notation_eq (1/2:ℝ) (by norm_num) (by norm_num)
  have hNotationComp := congrArg
    (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A.comp DH) hNotation
  have hOriginal := hp.1.2.2
  exact hNotationComp.trans
    (referenceTwoAngleAdjointRadial_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l hreg t hOriginal.2.1 hp.2)

def referenceTwoAngleAdjointMidpointRadialFamily :
    (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  sphereSobolevCompatibleInterpolationFamily
    (referenceTwoAngleAdjointRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleAdjointRadialEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l)

lemma referenceTwoAngleAdjointMidpointRadialFamily_lower_inclusion
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (referenceTwoAngleAdjointMidpointRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t) =
    (referenceTwoAngleAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).comp
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let A := referenceTwoAngleAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let DH := referenceTwoAngleAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let hCompat := referenceTwoAngleAdjointRadialEndpointPairFamily_mem_compatible
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t hp
  have hValue := sphereSobolevCompatibleInterpolationFamily_of_mem
    (referenceTwoAngleAdjointRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleAdjointRadialEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l) t hp
  have hMap := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T) hValue
  have hNotation := sphereSobolevInclusionL_negative_half_notation_eq (0:ℝ) (by norm_num) (by norm_num)
  have hNotationComp := congrArg
    (fun J : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      J.comp (sphereSobolevMidpointL A DH hCompat)) hNotation.symm
  exact hMap.trans (hNotationComp.trans (sphereSobolevInclusionL_midpoint A DH hCompat))

lemma referenceTwoAngleAdjointMidpointRadialFamily_upper_inclusion
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    (referenceTwoAngleAdjointMidpointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (referenceTwoAngleAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t) := by
  have hValue := sphereSobolevCompatibleInterpolationFamily_of_mem
    (referenceTwoAngleAdjointRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleAdjointRadialEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l) t hp
  have hMap := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hValue
  exact hMap.trans (sphereSobolevMidpointL_inclusion _ _ _)

lemma inner_probability_referenceTwoAngleMidpointRadial_adjoint
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (u v : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
        (referenceTwoAngleSharpMidpointRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t u),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv hO hD).symm
        (referenceTwoAngleAdjointMidpointRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t v)⟫_ℝ := by
  let A := referenceTwoAngleLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let D := referenceTwoAngleAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let M := referenceTwoAngleSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let MA := referenceTwoAngleAdjointMidpointRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t
  have hM := referenceTwoAngleSharpMidpointRadialTraceFamily_lower_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hp
  have hMA := referenceTwoAngleAdjointMidpointRadialFamily_lower_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t hp
  have hPair (f z : SphereSobolev (1/2:ℝ)) :
      sphereSobolevDualPairing (1/2:ℝ) z (A f)=sphereSobolevDualPairing (1/2:ℝ) f (D z) :=
    sphereSobolevDualPairing_referenceTwoAngleLowerRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t f z
  exact inner_probability_midpoint_of_half_dual_pairing hO hD A D M MA hM hMA hPair u v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointRadialEndpointPairFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointRadialEndpointPairFamily_mem_compatible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMidpointRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMidpointRadialFamily_lower_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMidpointRadialFamily_upper_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_probability_referenceTwoAngleMidpointRadial_adjoint
