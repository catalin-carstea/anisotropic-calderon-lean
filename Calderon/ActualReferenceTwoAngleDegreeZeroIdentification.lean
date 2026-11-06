import Calderon.ActualReferenceTwoAngleDegreeExtraction
import Calderon.ActualReferenceDegreeHalfChosenSmoothness
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Full upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-degree-zero-identification-v131.md. SAME original chosen C. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceTwoAngleDegreeCommutatorHalfFamily
  referenceRadialDegreeCommutatorHalfFamily referenceTwoAngleLowerRadialEndpointFamily
  referenceLowerRadialEndpointFamily referenceTwoAngleSharpRadialTraceFamily
  referenceSharpRadialTraceFamily sphereSobolevInclusionL sphereSobolevShiftedDegreeL

lemma referenceTwoAngleDegreeCommutatorHalfFamily_zero_angle
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p) =
    referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := by
  have hz := referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p hp
  have hPoint : (0,(0,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l :=
    Set.mem_iInter.mp hz (0,0)
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let AA := referenceTwoAngleLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(0,p))
  let RR := referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let SS := referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hSharp := (referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l 0 p).trans
      (referenceRotationSharpRadialTraceFamily_zero_angle
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p)
  have hLow : AA = RR := by
    apply ContinuousLinearMap.ext
    intro f
    apply denseRange_clm_apply_eq I
      (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) AA RR
    intro u
    have hAA := (congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (referenceTwoAngleSharpRadialTraceFamily_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(0,p))
          hp.2.2 hp.2.1 hPoint.2)).symm
    have hRR := (congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (referenceSharpRadialTraceFamily_lower_compatibility_on_locus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)).symm
    have hSame := congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => J (T u)) hSharp
    exact hAA.trans (hSame.trans hRR.symm)
  apply ContinuousLinearMap.ext
  intro f
  apply denseRange_clm_apply_eq I
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p))
    (referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
  intro u
  have hNew := referenceTwoAngleDegreeCommutatorHalfFamily_raw_high_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p) hz u
  have hOriginal := referenceRadialDegreeCommutatorHalfFamily_high_graph_on_locus
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp u
  have hPointwise : sphereSobolevShiftedDegreeL (1/2:ℝ)
      (referenceTwoAngleSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(0,p)) u) -
      AA (sphereSobolevShiftedDegreeL (3/2:ℝ) u) =
      sphereSobolevShiftedDegreeL (1/2:ℝ) (SS u) -
      RR (sphereSobolevShiftedDegreeL (3/2:ℝ) u) :=
    congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x-y)
      (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
        sphereSobolevShiftedDegreeL (1/2:ℝ) (T u)) hSharp)
      (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
        T (sphereSobolevShiftedDegreeL (3/2:ℝ) u)) hLow)
  have hOriginalValue : referenceRadialDegreeCommutatorHighL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u =
      sphereSobolevShiftedDegreeL (1/2:ℝ) (SS u) -
        RR (sphereSobolevShiftedDegreeL (3/2:ℝ) u) := by
    simp only [referenceRadialDegreeCommutatorHighL,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, SS, RR]
  exact hNew.trans (hPointwise.trans (hOriginal.trans hOriginalValue).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeCommutatorHalfFamily_zero_angle
