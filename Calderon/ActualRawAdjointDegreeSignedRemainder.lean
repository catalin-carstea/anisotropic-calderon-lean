import Calderon.ActualRawAdjointDegreePivot
import Calderon.ActualReferenceDegreeHalfChosenRadialValueCorrespondence
import Calderon.ActualReferenceAdjointDegreeSecondRemainderGraph
import Calderon.NativeLowerTransposeSignedTaylor
import Calderon.SignedTaylorOperatorIntertwining
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.RawAdjointDegreeGainDraft
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local instance] rawAdjointDegreeHalfCompleteSpace rawAdjointDegreeNegativeCompleteSpace

local notation "Csharp" => referenceRadialDegreeCommutatorHalfFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Wsharp" => referenceTwoAngleDegreeRotationDerivativeFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
local notation "Qsharp" => referenceTwoAngleDegreeCommutatorHalfFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-! ## Negative-transpose low families and the explicit high lift -/

local notation "Ct" => lowFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Wt" => rotationDerivativeFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

local notation "Gt" => gainedHighFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

lemma secondTaylorRemainder_neg_curve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (F : ℝ → V) (r : ℝ) :
    secondTaylorRemainder (fun t => -F t) r = -secondTaylorRemainder F r := by
  have hD : deriv (-F) = -deriv F := funext fun x => deriv.neg
  have hDD : deriv (deriv (-F)) = -deriv (deriv F) := by
    rw [hD]
    exact funext fun x => deriv.neg
  change secondTaylorRemainder (-F) r = -secondTaylorRemainder F r
  unfold secondTaylorRemainder
  rw [hDD, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Pi.neg_apply, smul_neg]

def gainedHighSecondRemainder (q : ℝ) (y : R3) (r : ℝ) : Hi →L[ℝ] Half :=
  secondTaylorRemainder (fun z : ℝ => Gt (q,(y,z))) r

local notation "Gt2" => gainedHighSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

lemma gainedHighSecondRemainder_lower_compatibility (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ Ω) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Gt2 q y r) =
      (secondTaylorRemainder (fun z : ℝ => Ct (q,(y,z))) r).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let U : ℝ → Hi →L[ℝ] Half := fun z => Gt (q,(y,z))
  let A : ℝ → Half →L[ℝ] NegH := fun z => Ct (q,(y,z))
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hUS (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ U (θ*r) :=
    (contDiffAt_gainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,θ*r)) (hSegment θ hθ)).comp
        (f := fun z : ℝ => (q,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) :=
    (contDiffAt_lowFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,θ*r)) (hSegment θ hθ)).comp
        (f := fun z : ℝ => (q,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) :
      (fun z => J.comp (U z)) =ᶠ[𝓝 (θ*r)] (fun z => (A z).comp I) := by
    have hNear : ∀ᶠ z : ℝ in 𝓝 (θ*r), (q,(y,z)) ∈ Ω :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with z hz
    exact gainedHighFamily_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,z)) hz
  have hLaw := secondTaylorRemainder_operator_intertwining
    (X := SphereSobolev (3/2:ℝ)) (Y := SphereSobolev (1/2:ℝ)) (Z := SphereSobolev (-(1/2:ℝ)))
  try simp (config := { instances := true }) only [real_nontriviallyNormedField_normedField_eq,
    sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,sequenceLp_normedSpace_module_eq_natural,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hLaw
  exact hLaw U A I J r hUS hAS hEq

include hreg in
lemma lowFamily_secondRemainder_eq_neg_transpose (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ Ω) :
    secondTaylorRemainder (fun z : ℝ => Ct (q,(y,z))) r =
      -sphereLowerDistributionalTranspose
        (referenceRadialDegreeCommutatorHalfSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r) := by
  let A : ℝ → Half →L[ℝ] NegH := fun z =>
    referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))
  have hA (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) :=
    (contDiffAt_referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,θ*r)) (hSegment θ hθ)).comp
        (f := fun z : ℝ => (q,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hNeg := secondTaylorRemainder_neg_curve
    (fun z : ℝ => sphereLowerDistributionalTranspose (A z)) r
  have hT : sphereLowerDistributionalTranspose (secondTaylorRemainder A r) =
      secondTaylorRemainder (fun t => sphereLowerDistributionalTranspose (A t)) r :=
    sphereLowerDistributionalTranspose_secondTaylorRemainder A r hA
  have hNamed := referenceRadialDegreeCommutatorHalfSecondRemainder_eq_chosen_remainder
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSegment
  calc
    secondTaylorRemainder (fun z : ℝ => Ct (q,(y,z))) r =
        secondTaylorRemainder (fun z : ℝ => -sphereLowerDistributionalTranspose (A z)) r := rfl
    _ = -secondTaylorRemainder (fun z : ℝ => sphereLowerDistributionalTranspose (A z)) r := hNeg
    _ = -sphereLowerDistributionalTranspose (secondTaylorRemainder A r) :=
      congrArg (fun T : Half →L[ℝ] NegH => -T) hT.symm
    _ = _ := congrArg (fun T : Half →L[ℝ] NegH => -sphereLowerDistributionalTranspose T)
      hNamed.symm

/- The exact signed graph `J CTsecond u = Dlow (Th u) - Tl (Dhigh u)`, where Th/Tl are
the signed second remainders of the actual adjoint radial families. -/
theorem gainedHighSecondRemainder_signed_adjoint_degree_graph (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ Ω) (u : Hi) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (Gt2 q y r u) =
      sphereSobolevShiftedDegreeL (1/2:ℝ)
        (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r u) -
      secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
        (sphereSobolevShiftedDegreeL (3/2:ℝ) u) := by
  have h1 := congrArg (fun A : Hi →L[ℝ] NegH => A u)
    (gainedHighSecondRemainder_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSegment)
  have h2 := lowFamily_secondRemainder_eq_neg_transpose
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSegment
  have h3 := neg_transpose_referenceRadialDegreeCommutatorHalfSecondRemainder_genuine_adjoint_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSegment
  exact h1.trans ((congrArg (fun T : Half →L[ℝ] NegH =>
    T (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) h2).trans (h3 u))

lemma contDiffAt_gainedHighSecondRemainder_of_segment (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => Gt2 z.1 z.2.1 z.2.2) (q,(y,r)) := by
  let F : (ℝ × R3) × ℝ → Hi →L[ℝ] Half := fun z => Gt (z.1.1,(z.1.2,z.2))
  let Ωs : Set ((ℝ × R3) × ℝ) := {z | (z.1.1,(z.1.2,z.2)) ∈ Ω}
  have hΩs : IsOpen Ωs := (isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hFSmooth : ContDiffOn ℝ ∞ F Ωs := by
    intro z hz
    have hi : (z.1.1,(z.1.2,z.2)) ∈ Ω := hz
    exact ((contDiffAt_gainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (z.1.1,(z.1.2,z.2)) hi).comp
      (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) z
        (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hR : ContDiffAt ℝ ∞
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) ((q,y),r) :=
    contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ωs hΩs hFSmooth (q,y) r hSegment
  have hOut := hR.comp (f := fun z : ℝ × (R3 × ℝ) => ((z.1,z.2.1),z.2.2)) (q,(y,r))
    ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  simpa only [gainedHighSecondRemainder,Function.comp_def,F] using hOut

/-! ## Uniform compact caps

All constants depend only on the fixed geometry and witnesses, the compact room and the
jet order. They are chosen before any q, profile, input or cutoff. -/

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.RawAdjointDegreeGainDraft
