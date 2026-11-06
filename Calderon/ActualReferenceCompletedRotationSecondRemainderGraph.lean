import Calderon.ActualReferenceRotationSignedRemainder
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Mathlib.Topology.DenseEmbedding

set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

lemma referenceLowerRadialRotationSecondRemainder_completed_graph
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Rh := sphereSobolevRotationL (3/2 : ℝ) i j
    let Rl := sphereSobolevRotationL (1/2 : ℝ) i j
    let C2 := referenceLowerRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r
    let Sh := referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    let Sl := referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    ∀ u : SphereSobolev (3/2 : ℝ), C2 (I u) = Rl (Sh u)-Sl (Rh u) := by
  intro I Rh Rl C2 Sh Sl
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let I25 := sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
  let R25 := sphereSobolevRotationL (5/2 : ℝ) i j
  have hRotMap := sphereSobolevRotationL_inclusion_comm
    (5/2 : ℝ) (3/2 : ℝ) (by norm_num) i j
  have hOrders :
      sphereSobolevInclusionL ((5/2 : ℝ)-1) ((3/2 : ℝ)-1) (by norm_num) = I := by
    have hDelta : ((3/2 : ℝ)-1)-((5/2 : ℝ)-1) = (1/2 : ℝ)-(3/2 : ℝ) := by
      norm_num
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext k
    have hLeft := sphereSobolevInclusionL_apply
      ((5/2 : ℝ)-1) ((3/2 : ℝ)-1) (by norm_num) v k
    have hRight := sphereSobolevInclusionL_apply (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v k
    exact hLeft.trans ((congrArg
      (fun a : ℝ => SpectralWeightedGraph.besselWeight a k • v k) hDelta).trans hRight.symm)
  have hRot (f : SphereSobolev (5/2 : ℝ)) : Rh (I25 f) = I (R25 f) := by
    have hValue := congrArg
      (fun A : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A f) hRotMap
    exact (by simpa only [hOrders,ContinuousLinearMap.comp_apply] using hValue.symm)
  have hCompat := referenceSharpRadialTraceSecondRemainder_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
  have hCompatValue (v : SphereSobolev (3/2 : ℝ)) : Sl (I v) = J (Sh v) := by
    have hValue := congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v) hCompat
    exact (by simpa only [ContinuousLinearMap.comp_apply] using hValue.symm)
  let Left : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := C2.comp I
  let Right : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    Rl.comp Sh-Sl.comp Rh
  have hCore (f : SphereSobolev (5/2 : ℝ)) : Left (I25 f) = Right (I25 f) := by
    have hRaw := referenceLowerRadialRotationSecondRemainder_graph_agreement
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r hSegment f
    have hMiddle : Sl (Rh (I25 f)) = J (Sh (R25 f)) :=
      (congrArg Sl (hRot f)).trans (hCompatValue (R25 f))
    change C2 (I (I25 f)) = Rl (Sh (I25 f))-Sl (Rh (I25 f))
    exact hRaw.symm.trans (congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => Rl (Sh (I25 f))-z) hMiddle.symm)
  have hTests : Left ∘ I25 = Right ∘ I25 := funext hCore
  have hAll : (fun u => Left u) = (fun u => Right u) :=
    (denseRange_sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)).equalizer
      Left.continuous Right.continuous hTests
  intro u
  exact congrFun hAll u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialRotationSecondRemainder_completed_graph
