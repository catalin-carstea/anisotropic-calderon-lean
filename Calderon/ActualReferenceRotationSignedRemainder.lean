import Calderon.ActualReferenceLowerRadialTraceSecondRemainder
import Calderon.ActualReferenceRadialRotationCommutatorJointJets
import Calderon.SignedTaylorFixedLinearTransport
import Calderon.SignedTaylorOperatorIntertwining
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData

/-! Literal paired signed remainders; genuine normalized rotation graph on the existing
smooth domain. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
attribute [local irreducible] referenceLowerRadialEndpointFamily referenceSharpRadialTraceFamily
  referenceLowerRadialRotationCommutatorL referenceSharpRadialRotationCommutatorL
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  referenceLowerRadialTraceSecondRemainder sphereSobolevInclusionL sphereSobolevRotationL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceSharpRadialTraceSecondRemainder
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (s : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  secondTaylorRemainder (fun z : ℝ => referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,z))) r

def referenceLowerRadialRotationSecondRemainder
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (s : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  secondTaylorRemainder (fun z : ℝ => referenceLowerRadialRotationCommutatorL
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,z))) r

attribute [local irreducible] referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialRotationSecondRemainder

local instance referenceRotationSignedRemainderHalfCompleteSpace : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceRotationSignedRemainderNegativeHalfCompleteSpace : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

set_option diagnostics true in
lemma referenceSharpRadialTraceSecondRemainder_lower_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (s : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (s,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r) =
    (referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let U : ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z : ℝ => referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,z))
  let A : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z : ℝ => referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,z))
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hUS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ U (θ*r) := by
    have hi := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact (contDiffAt_referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,θ*r)) hi.1).comp (f := fun z : ℝ => (s,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) := by
    have hi := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,θ*r)) hi.2.2 hi.2.1).comp (f := fun z : ℝ => (s,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun z => J.comp (U z)) =ᶠ[𝓝 (θ*r)] (fun z => (A z).comp I) := by
    have hNear : ∀ᶠ z : ℝ in 𝓝 (θ*r), (s,(y,z)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with z hz
    exact referenceSharpRadialTraceFamily_lower_compatibility_on_locus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,z)) hz
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "actual rotation abstract segment-1-ready"
    out.flush
  have hLaw := secondTaylorRemainder_operator_intertwining
    (X := SphereSobolev (3/2 : ℝ)) (Y := SphereSobolev (1/2 : ℝ))
    (Z := SphereSobolev (-(1/2 : ℝ)))
  simp (config := { instances := true }) only [real_nontriviallyNormedField_normedField_eq,
    sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,sequenceLp_normedSpace_module_eq_natural,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hLaw
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "actual rotation abstract certificate-1-ready"
    out.flush
  have hTransport : J.comp (secondTaylorRemainder U r) = (secondTaylorRemainder A r).comp I :=
    hLaw U A I J r hUS hAS hEq
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "actual rotation abstract transport-1-ready"
    out.flush
  have hUpper : referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r = secondTaylorRemainder U r := by
    unfold referenceSharpRadialTraceSecondRemainder
    rfl
  have hLower : referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r = secondTaylorRemainder A r := by
    unfold referenceLowerRadialTraceSecondRemainder
    rfl
  exact (congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => J.comp T) hUpper).trans
    (hTransport.trans
      (congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T.comp I) hLower.symm))

set_option diagnostics true in
lemma referenceLowerRadialRotationSecondRemainder_upper_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3)
    (s : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (s,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (secondTaylorRemainder (fun z : ℝ => referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,z))) r) =
    (referenceLowerRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j s y r).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let U : ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z : ℝ => referenceSharpRadialRotationCommutatorL
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,z))
  let A : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z : ℝ => referenceLowerRadialRotationCommutatorL
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,z))
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hUS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ U (θ*r) := by
    have hi := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact (contDiffAt_referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,θ*r)) hi.1 hi.2.1).comp (f := fun z : ℝ => (s,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) := by
    have hi := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact (contDiffAt_referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,θ*r)) hi.2.2 hi.2.1).comp (f := fun z : ℝ => (s,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun z => J.comp (U z)) =ᶠ[𝓝 (θ*r)] (fun z => (A z).comp I) := by
    have hNear : ∀ᶠ z : ℝ in 𝓝 (θ*r), (s,(y,z)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with z hz
    unfold referenceRadialEndpointInvertibleLocus at hz
    exact referenceLowerRadialRotationCommutatorL_upper_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,z)) hz.2.2 hz.1 hz.2.1
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "actual rotation abstract segment-2-ready"
    out.flush
  have hLaw := secondTaylorRemainder_operator_intertwining
    (X := SphereSobolev (3/2 : ℝ)) (Y := SphereSobolev (1/2 : ℝ))
    (Z := SphereSobolev (-(1/2 : ℝ)))
  simp (config := { instances := true }) only [real_nontriviallyNormedField_normedField_eq,
    sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,sequenceLp_normedSpace_module_eq_natural,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hLaw
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "actual rotation abstract certificate-2-ready"
    out.flush
  have hTransport : J.comp (secondTaylorRemainder U r) = (secondTaylorRemainder A r).comp I :=
    hLaw U A I J r hUS hAS hEq
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "actual rotation abstract transport-2-ready"
    out.flush
  have hLower : referenceLowerRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j s y r = secondTaylorRemainder A r := by
    unfold referenceLowerRadialRotationSecondRemainder
    rfl
  exact hTransport.trans
    (congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T.comp I) hLower.symm)

lemma referenceLowerRadialRotationSecondRemainder_graph_agreement
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3)
    (s : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (s,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (5/2 : ℝ)) :
    sphereSobolevRotationL (1/2 : ℝ) i j
      (referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r
          (sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) f)) -
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r
          (sphereSobolevRotationL (5/2 : ℝ) i j f)) =
    referenceLowerRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j s y r
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) f)) := by
  let U : ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z : ℝ => referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,z))
  let C1 : ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z : ℝ => referenceSharpRadialRotationCommutatorL
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,z))
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let I25 : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
  let Rhalf : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevRotationL (1/2 : ℝ) i j
  let R25 : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := sphereSobolevRotationL (5/2 : ℝ) i j
  let Ef : (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) :=
    Rhalf.comp (ContinuousLinearMap.apply ℝ (SphereSobolev (1/2 : ℝ)) (I25 f)) -
    J.comp (ContinuousLinearMap.apply ℝ (SphereSobolev (1/2 : ℝ)) (R25 f))
  let Cf : (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →L[ℝ]
      SphereSobolev (-(1/2 : ℝ)) :=
    J.comp (ContinuousLinearMap.apply ℝ (SphereSobolev (1/2 : ℝ)) (I25 f))
  have hUS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ U (θ*r) := by
    have hi := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact (contDiffAt_referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,θ*r)) hi.1).comp
        (f := fun z : ℝ => (s,(y,z))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hCS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ C1 (θ*r) := by
    have hi := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact (contDiffAt_referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,θ*r)) hi.1 hi.2.1).comp
        (f := fun z : ℝ => (s,(y,z))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun z => Ef (U z)) =ᶠ[𝓝 (θ*r)] (fun z => Cf (C1 z)) := by
    have hNear : ∀ᶠ z : ℝ in 𝓝 (θ*r), (s,(y,z)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with z hz
    unfold referenceRadialEndpointInvertibleLocus at hz
    exact referenceSharpRadialRotationCommutatorL_graph_agreement
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (s,(y,z)) hz.1 hz.2.1 f
  have hGraph : Ef (secondTaylorRemainder U r) = Cf (secondTaylorRemainder C1 r) :=
    (secondTaylorRemainder_fixed_linear_map U Ef r hUS).trans
      ((secondTaylorRemainder_eq_of_locallyEq_on_segment
        (fun z => Ef (U z)) (fun z => Cf (C1 z)) r hEq).trans
          (secondTaylorRemainder_fixed_linear_map C1 Cf r hCS).symm)
  have hCompat := referenceLowerRadialRotationSecondRemainder_upper_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j s y r hSegment
  have hEvalRaw := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I25 f)) hCompat
  have hEval : J ((secondTaylorRemainder C1 r) (I25 f)) =
      referenceLowerRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j s y r
          ((sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) (I25 f)) := by
    simpa only [ContinuousLinearMap.comp_apply] using hEvalRaw
  have hEf (T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :
      Ef T = Rhalf (T (I25 f)) - J (T (R25 f)) := rfl
  have hCf (T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :
      Cf T = J (T (I25 f)) := rfl
  have hUpper : referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r = secondTaylorRemainder U r := by
    unfold referenceSharpRadialTraceSecondRemainder
    rfl
  have hUpperEval := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      Rhalf (T (I25 f)) - J (T (R25 f))) hUpper
  exact hUpperEval.trans ((hEf _).symm.trans (hGraph.trans ((hCf _).trans hEval)))


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialTraceSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialRotationSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialTraceSecondRemainder_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialRotationSecondRemainder_upper_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialRotationSecondRemainder_graph_agreement
