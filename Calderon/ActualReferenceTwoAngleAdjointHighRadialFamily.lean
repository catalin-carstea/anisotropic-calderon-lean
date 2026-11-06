import Calderon.ActualReferenceTwoAngleAdjointSharpConormalFamily
import Calderon.ActualReferenceTwoAngleNormalDriftEndpointFamilies
import Calderon.ActualReferenceTwoAngleTangentialAdjointEndpointFamilies
import Calderon.ActualReferenceTwoAngleNormalEndpointInverseFamilies
import Calderon.NativeHalfTraceRightInverse
import Calderon.NativeZeroValueTrace

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-actual-high-adjoint-v098.md. RIGHT ordinary normal reciprocal. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace NativeHalfTraceRightInverse
  NativeHarmonicH1LiftCompletion
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (i j k l : Fin 3)

def referenceTwoAngleAdjointThreeHalfRadialFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (referenceTwoAngleAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t +
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceTwoAngleNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData i j k l hcalc hF hO hD τ0 t) -
    referenceTwoAngleTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData i j k l hcalc hF hO hD τ0 t).comp
      (referenceTwoAngleNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).inverse

lemma contDiffOn_referenceTwoAngleAdjointThreeHalfRadialFamily_invertibleLocus
    (hreg : FixedDirichletRegularity) :
    ContDiffOn ℝ ∞ (referenceTwoAngleAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
      (Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) := by
  let Ω : Set (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :=
    Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  have hN := contDiffOn_referenceTwoAngleAdjointHighConormalFamily_invertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l
  have hB := (contDiff_referenceTwoAngleNormalDriftThreeHalfMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData i j k l hcalc hF hO hD τ0).contDiffOn (s := Ω)
  have hT := (contDiff_referenceTwoAngleTangentialAdjointThreeHalfFamily
    g L y0 Φ B ε C ρ H a w hData i j k l hcalc hF hO hD τ0).contDiffOn (s := Ω)
  have hI := (contDiff_referenceTwoAngleNormalThreeHalfMultiplierFamily_inverse
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l).contDiffOn (s := Ω)
  unfold referenceTwoAngleAdjointThreeHalfRadialFamily
  exact ((hN.add (contDiffOn_const.clm_comp hB)).sub hT).clm_comp hI

lemma nativeHalfTraceL_firstOrder_referenceTwoAngleAdjointH2LiftFamily
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (f : SphereSobolev (3/2:ℝ)) :
    nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1
      (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f)) =
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f := by
  let f0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U : BallH1 := TauCeti.Wkp.firstOrder 1 (referenceTwoAngleAdjointH2LiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f)
  let E0 : BallH1 := harmonicFirstOrderLiftCompletion hF f0
  have hz : E0-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceTwoAngleAdjointH2LiftFamily_zero_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l t f
  let c : BallH1Zero := ⟨E0-U,hz⟩
  have ht := nativeHalfTraceL_zeroDirichlet hF hO hD τ0 c
  change nativeHalfTraceL hF hO hD τ0 (E0-U)=0 at ht
  have hsub : nativeHalfTraceL hF hO hD τ0 E0-nativeHalfTraceL hF hO hD τ0 U=0 := by
    simpa only [map_sub] using ht
  exact (sub_eq_zero.mp hsub).symm.trans
    (nativeHalfTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 f0)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointThreeHalfRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleAdjointThreeHalfRadialFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_firstOrder_referenceTwoAngleAdjointH2LiftFamily
