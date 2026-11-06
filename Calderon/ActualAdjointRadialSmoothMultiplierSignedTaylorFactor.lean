import Calderon.ActualAdjointRadialSmoothMultiplierSliceTopology
import Calderon.ActualAdjointRadialSmoothMultiplierNegativeFactor
import Calderon.ActualReferenceSmoothMultiplierJointTopology
import Calderon.ActualReferenceAdjointRadialSignedRemainder
import Calderon.SignedTaylorFixedBimoduleTransport
import Calderon.ClmNaturalStructureData

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

local instance referenceSmoothCommutatorR2HalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceSmoothCommutatorR2NegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (Km : Set R3) (hKm : IsCompact Km)
  (hmz : ∀ t x, x ∉ Km → m (t,x)=0)

lemma referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (q : ℝ) (y : R3) (r : ℝ) (t : T)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let Q := commonSupportCoefficientFamily 3 m hm Km hKm hmz t
    let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let M := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
    let Mn := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
    let S : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      fun tau => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,tau))
    let G : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
      fun tau => referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,tau))
    let Tl2 := secondTaylorRemainder S r
    let G2 := secondTaylorRemainder G r
    (∀ u : SphereSobolev (1/2 : ℝ), Tl2 (M u)-Mn (Tl2 u) =
      -(realHalfOperatorAdjointL G2 (J u))) ∧
    Tl2 = sphereLowerDistributionalTranspose (secondTaylorRemainder
      (fun tau => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,tau))) r) := by
  intro Q J M Mn S G Tl2 G2
  let Ω := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hOpen : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSlice : ContDiff ℝ ∞ (fun tau : ℝ => (q,(y,tau))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ S (θ*r) :=
    contDiffAt_referenceAdjointHalfRadialFamily_radialSlice
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (θ*r) (hSegment θ hθ)
  have hG (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ G (θ*r) :=
    contDiffAt_referenceSmoothMultiplierBoundaryCommutator_radialSlice
      g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0
        q y (θ*r) t (hSegment θ hθ)
  have hSmoothCLM := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (F := SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) (n := ∞)
  simp (config := { instances := true }) only
    [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq_natural,
      clm_seminormedAddCommGroup_addCommMonoid_eq_natural,
      clm_normedSpace_module_eq_natural] at hSmoothCLM
  have hAdjointSmooth : ContDiff ℝ ∞
      (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        realHalfOperatorAdjointL A) := hSmoothCLM realHalfOperatorAdjointL
  have hAdjG (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun tau => realHalfOperatorAdjointL (G tau)) (θ*r) := by
    have hComp := hAdjointSmooth.contDiffAt.comp (θ*r) (hG θ hθ)
    simpa only [Function.comp_def] using hComp
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun tau => (S tau).comp M-Mn.comp (S tau)) =ᶠ[𝓝 (θ*r)]
        (fun tau => (-1 : ℝ) • (realHalfOperatorAdjointL (G tau)).comp J) := by
    have hNear : ∀ᶠ tau in 𝓝 (θ*r), (q,(y,tau)) ∈ Ω :=
      hSlice.continuous.continuousAt.eventually (hOpen.mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with tau htau
    apply ContinuousLinearMap.ext
    intro u
    have hPoint := referenceAdjointHalfRadial_smoothMultiplier_commutator_negative_factor
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q (q,(y,tau)) htau u
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply,neg_one_smul] using hPoint
  have hLeft := secondTaylorRemainder_fixed_commutator S M Mn r hS
  have hMiddle := secondTaylorRemainder_eq_of_locallyEq_on_segment
    (fun tau => (S tau).comp M-Mn.comp (S tau))
    (fun tau => (-1 : ℝ) • (realHalfOperatorAdjointL (G tau)).comp J) r hEq
  have hRight := secondTaylorRemainder_const_smul_precomp
    (fun tau => realHalfOperatorAdjointL (G tau)) J (-1 : ℝ) r hAdjG
  have hFixedLinear := secondTaylorRemainder_fixed_linear_map
    (V := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (W := SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
  simp (config := { instances := true }) only
    [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq_natural,
      clm_seminormedAddCommGroup_addCommMonoid_eq_natural,
      clm_normedSpace_module_eq_natural] at hFixedLinear
  have hAdj := hFixedLinear G realHalfOperatorAdjointL r hG
  have hAdjValue := congrArg
    (fun K : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      (-1 : ℝ) • K.comp J) hAdj.symm
  have hAll := hLeft.symm.trans (hMiddle.trans (hRight.trans hAdjValue))
  constructor
  · intro u
    have hValue := congrArg
      (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K u) hAll
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply,neg_one_smul] using hValue
  · exact secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
