import Calderon.ActualAdjointMovingBoundaryFamilyFoundation
import Calderon.ActualReferenceGaugeAdjointIdentity
import Calderon.ActualReferenceGaugeNormalHalfCommutator
import Calderon.ActualReferenceGaugeTangentOperator

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-gauge-half-tangent-defect-v018.md. SAME actual operators, right inverse. -/
set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceLowerRadialEndpointFamily
  referenceGaugeNormalHalfMultiplierFamily referenceGaugeNormalNegativeHalfMultiplierFamily
  referenceGaugeNormalCommutatorFamily referenceGaugeNormalHalfCommutatorFamily
  referenceGaugeTangentEndpointFamily referenceGaugeTangentSecondEndpointFamily
  sphereLowerDistributionalTranspose sphereLowerDistributionalTransposeL
  referenceRadialEndpointInvertibleLocus ContinuousLinearMap.inverse

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

set_option diagnostics true in
theorem referenceLowerRadialEndpoint_distributionalTranspose_sub_eq_half_add_tangent_second
    (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ)
    (hp : (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    sphereLowerDistributionalTranspose (referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) -
      referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) =
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeNormalHalfCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))) +
    r^2 • ((referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) -
      sphereLowerDistributionalTranspose (referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)))).comp
      (referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))).inverse) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_enter"
    out.flush
  let p := (q,(y,r))
  let A := referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let M := referenceGaugeNormalHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let Mn := referenceGaugeNormalNegativeHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let T := referenceGaugeTangentEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let T2 := referenceGaugeTangentSecondEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let K := referenceGaugeNormalHalfCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hRoom := hp
  unfold referenceRadialEndpointInvertibleLocus at hRoom
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_before-defect"
    out.flush
  have hDef : sphereLowerDistributionalTranspose A-A =
      (Mn.comp A-A.comp M+T-sphereLowerDistributionalTranspose T).comp M.inverse :=
    referenceLowerRadialEndpoint_distributionalTranspose_sub_gaugeNormal_inverse
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p hRoom.2.2 hRoom.1 hRoom.2.1
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_after-defect"
    out.flush
  have hT : T = r^2 • T2 :=
    referenceGaugeTangentEndpointFamily_eq_radius_sq_smul_second
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q hq y hy r
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_after-tangent"
    out.flush
  have hTt : sphereLowerDistributionalTranspose T = r^2 • sphereLowerDistributionalTranspose T2 := by
    have hLinear := sphereLowerDistributionalTransposeL.map_smul (r^2) T2
    have hNamed : sphereLowerDistributionalTranspose (r^2 • T2) =
        r^2 • sphereLowerDistributionalTranspose T2 :=
      (sphereLowerDistributionalTransposeL_apply _).symm.trans
        (hLinear.trans (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ]
          SphereSobolev (-(1/2 : ℝ)) => r^2 • Z) (sphereLowerDistributionalTransposeL_apply T2)))
    exact (congrArg sphereLowerDistributionalTranspose hT).trans hNamed
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_after-transpose"
    out.flush
  have hK (u : SphereSobolev (1/2 : ℝ)) :
      J (K u) = Mn (A (M.inverse u))-A (M (M.inverse u)) := by
    have hRaw : J (K u) = referenceGaugeNormalCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u :=
      referenceGaugeNormalHalfCommutatorFamily_lower_agreement
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel p hp u
    have hLowerPoint : referenceGaugeNormalCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u =
          Mn (A (M.inverse u))-A (M (M.inverse u)) := by
      unfold referenceGaugeNormalCommutatorFamily
      simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,Mn,A,M]
    exact hRaw.trans hLowerPoint
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_after-K-point"
    out.flush
  apply ContinuousLinearMap.ext
  intro u
  have hPoint := congrArg
    (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z u) hDef
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply] at hPoint
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_after-point-application"
    out.flush
  change sphereLowerDistributionalTranspose A u-A u =
    J (K u)+r^2 • ((T2-sphereLowerDistributionalTranspose T2) (M.inverse u))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_before-point-algebra"
    out.flush
  let v : SphereSobolev (1/2 : ℝ) := M.inverse u
  have hTPoint : T v = r^2 • T2 v :=
    congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z v) hT
  have hTtPoint : sphereLowerDistributionalTranspose T v =
      r^2 • sphereLowerDistributionalTranspose T2 v :=
    congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z v) hTt
  have hNormalPoint : Mn (A v)-A (M v) = J (K u) := (hK u).symm
  have hReplace : (Mn (A v)-A (M v)+T v)-sphereLowerDistributionalTranspose T v =
      (J (K u)+r^2 • T2 v)-r^2 • sphereLowerDistributionalTranspose T2 v :=
    congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
      (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z) hNormalPoint hTPoint)
      hTtPoint
  have hCombined : sphereLowerDistributionalTranspose A u-A u =
      (J (K u)+r^2 • T2 v)-r^2 • sphereLowerDistributionalTranspose T2 v :=
    hPoint.trans hReplace
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HALF_TANGENT_point-replacements-ready"
    out.flush
  have hAssociate : (J (K u)+r^2 • T2 v)-r^2 • sphereLowerDistributionalTranspose T2 v =
      J (K u)+(r^2 • T2 v-r^2 • sphereLowerDistributionalTranspose T2 v) :=
    add_sub_assoc _ _ _
  have hScalar : J (K u)+(r^2 • T2 v-r^2 • sphereLowerDistributionalTranspose T2 v) =
      J (K u)+r^2 • (T2 v-sphereLowerDistributionalTranspose T2 v) :=
    congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => J (K u)+z)
      (smul_sub (r^2) (T2 v) (sphereLowerDistributionalTranspose T2 v)).symm
  have hSubPoint : (T2-sphereLowerDistributionalTranspose T2) v =
      T2 v-sphereLowerDistributionalTranspose T2 v := rfl
  have hTarget : J (K u)+r^2 • ((T2-sphereLowerDistributionalTranspose T2) (M.inverse u)) =
      J (K u)+r^2 • (T2 v-sphereLowerDistributionalTranspose T2 v) :=
    congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => J (K u)+r^2 • z) hSubPoint
  exact hCombined.trans (hAssociate.trans (hScalar.trans hTarget.symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpoint_distributionalTranspose_sub_eq_half_add_tangent_second
