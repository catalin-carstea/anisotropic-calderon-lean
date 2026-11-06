import Calderon.ActualReferenceAdjointRadialSignedRemainder
import Calderon.ActualReferenceAdjointRadialEndpointFamilies
import Calderon.SignedTaylorOperatorIntertwining
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData

/-! Full before-source: actual-high-first-output-domain-plan-oct16-v001/
EXPANSION-actual-literal-paired-R2-pivot-domain-v005.md, section2.
Literal genuine adjoint endpoints, fixed I/J Taylor transport on actual Omega. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

local instance referenceAdjointSignedRemainderHalfCompleteSpace : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceAdjointSignedRemainderNegativeHalfCompleteSpace : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily secondTaylorRemainder sphereSobolevInclusionL

lemma referenceAdjointRadialSecondRemainder_high_half_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) =
    (secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let U : ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun t =>
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let A : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun t =>
    referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hOpen : IsOpen Ω :=
    isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSlice : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hUS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ U (θ*r) := by
    have hJoint := (contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt (hOpen.mem_nhds (hSegment θ hθ))
    exact hJoint.comp (θ*r) hSlice.contDiffAt
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) := by
    have hJoint := (contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt (hOpen.mem_nhds (hSegment θ hθ))
    exact hJoint.comp (θ*r) hSlice.contDiffAt
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => J.comp (U t)) =ᶠ[𝓝 (θ*r)] (fun t => (A t).comp I) := by
    have hNear : ∀ᶠ t : ℝ in 𝓝 (θ*r), (q,(y,t)) ∈ Ω :=
      hSlice.continuous.continuousAt.eventually (hOpen.mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with t ht
    have htFields := ht
    change (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 at htFields
    unfold referenceRadialEndpointInvertibleLocus at htFields
    exact referenceAdjointRadialEndpointFamily_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,t)) htFields.2.1
  have hLaw := secondTaylorRemainder_operator_intertwining
    (X := SphereSobolev (3/2 : ℝ)) (Y := SphereSobolev (1/2 : ℝ))
    (Z := SphereSobolev (-(1/2 : ℝ)))
  simp (config := { instances := true }) only [real_nontriviallyNormedField_normedField_eq,
    sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,sequenceLp_normedSpace_module_eq_natural,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hLaw
  exact hLaw U A I J r hUS hAS hEq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointRadialSecondRemainder_high_half_compatibility
