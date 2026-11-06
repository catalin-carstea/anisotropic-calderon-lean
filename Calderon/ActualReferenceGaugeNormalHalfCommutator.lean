import Calderon.ActualReferenceGaugeNormalCommutatorFirstJet
import Calderon.ActualReferenceSmoothMultiplierLowerCommutator
import Calderon.ActualReferenceSmoothMultiplierJointTopology
import Calderon.NativeSmoothMultiplierCommonSupportJets
import Calderon.SequenceLpInheritedStructureData
import Calderon.ClmInheritedStructureData

/-! Full upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-actual-gauge-normal-half-gain-v070.md. Native B has sign [Lambda,alpha].
The half gain is constructed before transporting the actual lower firstjet. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  OperatorCurveDerivative

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

lemma referenceGaugeNormalCoefficientJetsFamily_lowerJets (p : ℝ × (R3 × ℝ)) :
    smoothMultiplierLowerJets
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p) =
    referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p := by
  exact smoothMultiplierLowerJets_commonSupport (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData) p

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeNormalHalfCommutatorFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  -((referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p) p).comp
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse)

attribute [local irreducible] referenceGaugeNormalHalfCommutatorFamily
  referenceGaugeNormalCommutatorFamily referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceLowerRadialEndpointFamily referenceRadialEndpointInvertibleLocus
  referenceGaugeNormalHalfMultiplierFamily referenceGaugeNormalNegativeHalfMultiplierFamily
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  referenceCenterDrift referenceGaugeNormalCoefficientJetsFamily smoothMultiplierLowerJets
  sphereSobolevInclusionL

set_option diagnostics true in
lemma referenceGaugeNormalHalfCommutatorFamily_lower_agreement
    (hKernel : UnitBallValueTraceKernel τ0)
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceGaugeNormalHalfCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u) =
    referenceGaugeNormalCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u := by
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower enter"
    h.flush
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let P : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let N : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let G : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p) p
  let Q3 : SmoothCoefficientJets 3 :=
    referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p
  let Q2 : SmoothCoefficientJets 2 :=
    referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p
  let v : SphereSobolev (1/2 : ℝ) := P.inverse u
  have hJets : smoothMultiplierLowerJets Q3 = Q2 :=
    referenceGaugeNormalCoefficientJetsFamily_lowerJets g L y0 Φ B ε C ρ H a w hData hg p
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower after-jets"
    h.flush
  have hLower : I (G v) =
      A (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q3) v) -
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q3) (A v) :=
    referenceSmoothMultiplierBoundaryCommutatorFamily_lower_agreement
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q3 p hp v
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower after-lower-graph"
    h.flush
  have hP : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q3) = P := by
    have h := congrArg (fun Q : SmoothCoefficientJets 2 =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q) hJets
    have hWrapper : nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 = P := by
      unfold P referenceGaugeNormalHalfMultiplierFamily
      rfl
    exact h.trans hWrapper
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower after-half-wrapper"
    h.flush
  have hN : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q3) = N := by
    have h := congrArg (fun Q : SmoothCoefficientJets 2 =>
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q) hJets
    have hWrapper : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 = N := by
      unfold N referenceGaugeNormalNegativeHalfMultiplierFamily
      rfl
    exact h.trans hWrapper
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower after-negative-wrapper"
    h.flush
  have hPvalue := congrArg
    (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A (M v)) hP
  have hNvalue := congrArg
    (fun M : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => M (A v)) hN
  have hGraph : I (G (P.inverse u)) = A (P (P.inverse u)) - N (A (P.inverse u)) :=
    hLower.trans (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z) hPvalue hNvalue)
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower after-value-graph"
    h.flush
  have hHalfPoint : referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u = -(G (P.inverse u)) := by
    unfold referenceGaugeNormalHalfCommutatorFamily
    simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,G,P]
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower half-point-ready"
    h.flush
  have hLowerPoint : referenceGaugeNormalCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u =
        N (A (P.inverse u)) - A (P (P.inverse u)) := by
    unfold referenceGaugeNormalCommutatorFamily
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,N,A,P]
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "Khalf lower lower-point-ready"
    h.flush
  have hImage := congrArg I hHalfPoint
  have hNegative : -(A (P (P.inverse u)) - N (A (P.inverse u))) =
      N (A (P.inverse u)) - A (P (P.inverse u)) := neg_sub _ _
  exact hImage.trans ((I.map_neg _).trans
    ((congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => -z) hGraph).trans
      (hNegative.trans hLowerPoint.symm)))


lemma contDiffAt_referenceGaugeNormalHalfCommutatorFamily
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) p := by
  have hRoom := hp
  unfold referenceRadialEndpointInvertibleLocus at hRoom
  have hJoint := contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData)
    hcalc hF hO hD τ0 p p hRoom.1 hRoom.2.1
  have hDiag : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) => (t,t)) p :=
    contDiffAt_id.prodMk contDiffAt_id
  have hB : ContDiffAt ℝ ∞ (fun t => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 t) t) p := by
    simpa only [referenceGaugeNormalCoefficientJetsFamily,Function.comp_def] using
      hJoint.comp (f := fun t : ℝ × (R3 × ℝ) => (t,t)) p hDiag
  have hW := (contDiff_referenceGaugeNormalHalfMultiplierFamily_inverse
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).contDiffAt (x := p)
  unfold referenceGaugeNormalHalfCommutatorFamily
  exact (hB.clm_comp hW).neg

lemma referenceGaugeNormalHalfCommutatorFamily_zero_radial_jet
    (hKernel : UnitBallValueTraceKernel τ0) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0)) = 0 ∧
    HasDerivAt (fun r : ℝ => referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)))
      (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y) -
        sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)) 0 := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let A : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun r =>
    referenceGaugeNormalHalfCommutatorFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))
  let K : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun r =>
    referenceGaugeNormalCommutatorFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))
  let F : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y) -
    sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hSmooth : ContDiffAt ℝ ∞ A 0 :=
    (contDiffAt_referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0)) hp).comp
        (f := fun r : ℝ => (q,(y,r))) 0
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hA : DifferentiableAt ℝ A 0 := hSmooth.differentiableAt (by simp)
  have hKJet : K 0 = 0 ∧ HasDerivAt K (I.comp F) 0 :=
    referenceGaugeNormalCommutatorFamily_zero_radial_jet
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq y hy
  have hK0 : K 0 = 0 := hKJet.1
  have hK : HasDerivAt K (I.comp F) 0 := hKJet.2
  have hNear : ∀ᶠ r : ℝ in 𝓝 0, (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
      ((isOpen_referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  have hZero : A 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    have h := referenceGaugeNormalHalfCommutatorFamily_lower_agreement
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel (q,(y,0)) hp u
    change I (A 0 u) = K 0 u at h
    have hKValue : K 0 u = 0 := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u) hK0
    exact h.trans (hKValue.trans I.map_zero.symm)
  have hDerivative : deriv A 0 = F := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    have hLeft := I.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_clm_fixed_argument_of_differentiableAt A 0 hA u)
    have hRight : HasDerivAt (fun r => K r u) (I (F u)) 0 := by
      simpa only [map_zero,add_zero,ContinuousLinearMap.comp_apply] using
        hK.clm_apply (hasDerivAt_const (0 : ℝ) u)
    have hEq : (fun r => I (A r u)) =ᶠ[𝓝 (0 : ℝ)] (fun r => K r u) := by
      filter_upwards [hNear] with r hr
      exact referenceGaugeNormalHalfCommutatorFamily_lower_agreement
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel (q,(y,r)) hr u
    exact hLeft.unique (hRight.congr_of_eventuallyEq hEq)
  constructor
  · exact hZero
  · have h := hA.hasFDerivAt.hasDerivAt
    change HasDerivAt A (deriv A 0) 0 at h
    have hSlope : HasDerivAt A F 0 :=
      Eq.mp (congrArg (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        HasDerivAt A M 0) hDerivative) h
    exact hSlope

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalCoefficientJetsFamily_lowerJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHalfCommutatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHalfCommutatorFamily_lower_agreement
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceGaugeNormalHalfCommutatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHalfCommutatorFamily_zero_radial_jet
