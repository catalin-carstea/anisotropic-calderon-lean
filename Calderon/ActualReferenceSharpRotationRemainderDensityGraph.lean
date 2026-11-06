import Calderon.ActualReferenceRotationSignedRemainder
import Calderon.ActualReferenceSharpRotationRemainderDefinition
import Calderon.SphereSobolevConormalRotationDerivative

/-! Genuine normalized rotation graph on all of H3half, obtained by density, without a
finite-core output premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceSharpRadialRotationSecondRemainder
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  referenceLowerRadialRotationSecondRemainder referenceRadialEndpointInvertibleLocus
  referenceSharpRadialRotationCommutatorL referenceSharpRadialTraceFamily
  sphereSobolevInclusionL sphereSobolevRotationL secondTaylorRemainder

lemma referenceSharpRadialRotationSecondRemainder_weak_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceSharpRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r u) =
    sphereSobolevRotationL (1/2 : ℝ) i j
      (referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r u) -
    referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
        (sphereSobolevRotationL (3/2 : ℝ) i j u) := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Inc : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
  let U2 : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let A2 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let K2 : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r
  let L2 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceLowerRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r
  let Rh : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevRotationL (1/2 : ℝ) i j
  let R3 : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevRotationL (3/2 : ℝ) i j
  let R5 : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    sphereSobolevRotationL (5/2 : ℝ) i j
  let W : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    Rh.comp U2 - A2.comp R3
  let Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := J.comp K2
  have hW (x : SphereSobolev (3/2 : ℝ)) : W x = Rh (U2 x) - A2 (R3 x) := rfl
  have hZ (x : SphereSobolev (3/2 : ℝ)) : Z x = J (K2 x) := rfl
  have hTrace : J.comp U2 = A2.comp I :=
    referenceSharpRadialTraceSecondRemainder_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
  have hRot : J.comp K2 = L2.comp I := by
    unfold K2 referenceSharpRadialRotationSecondRemainder
    exact referenceLowerRadialRotationSecondRemainder_upper_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r hSegment
  have hOn (f : SphereSobolev (5/2 : ℝ)) : W (Inc f) = Z (Inc f) := by
    have hIndexMap (s s' t t' : ℝ) (hst : t ≤ s) (hst' : t' ≤ s')
        (hs : s = s') (ht : t = t') :
        sphereSobolevInclusionL s t hst = sphereSobolevInclusionL s' t' hst' := by
      cases hs
      cases ht
      rfl
    have hOrders : sphereSobolevInclusionL ((5/2 : ℝ)-1) ((3/2 : ℝ)-1) (by norm_num) = I :=
      hIndexMap ((5/2 : ℝ)-1) (3/2 : ℝ) ((3/2 : ℝ)-1) (1/2 : ℝ)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hNativeRot : R3 (Inc f) =
        sphereSobolevInclusionL ((5/2 : ℝ)-1) ((3/2 : ℝ)-1) (by norm_num) (R5 f) :=
      congrArg (fun T : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T f)
        (sphereSobolevRotationL_inclusion (5/2 : ℝ) (3/2 : ℝ) (by norm_num) i j)
    have hInput : R3 (Inc f) = I (R5 f) :=
      hNativeRot.trans (congrArg
        (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T (R5 f)) hOrders)
    have hTraceValue : J (U2 (R5 f)) = A2 (I (R5 f)) :=
      congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (R5 f)) hTrace
    have hMiddle : J (U2 (R5 f)) = A2 (R3 (Inc f)) :=
      hTraceValue.trans (congrArg A2 hInput.symm)
    have hOld : Rh (U2 (Inc f)) - J (U2 (R5 f)) = L2 (I (Inc f)) :=
      referenceLowerRadialRotationSecondRemainder_graph_agreement
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r hSegment f
    have hSameLeft : Rh (U2 (Inc f)) - A2 (R3 (Inc f)) =
        Rh (U2 (Inc f)) - J (U2 (R5 f)) :=
      congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => Rh (U2 (Inc f))-z) hMiddle.symm
    have hRotValue : J (K2 (Inc f)) = L2 (I (Inc f)) :=
      congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (Inc f)) hRot
    exact (hW _).trans (hSameLeft.trans (hOld.trans (hRotValue.symm.trans (hZ _).symm)))
  have hFunctions : (fun x : SphereSobolev (3/2 : ℝ) => W x) =
      (fun x : SphereSobolev (3/2 : ℝ) => Z x) :=
    (denseRange_sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)).equalizer
      W.continuous Z.continuous (funext hOn)
  exact (hZ u).symm.trans ((congrFun hFunctions u).symm.trans (hW u))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationSecondRemainder_weak_graph
