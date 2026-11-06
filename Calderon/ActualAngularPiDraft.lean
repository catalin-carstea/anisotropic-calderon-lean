import Calderon.ActualAngularFirstOrderMaps
import Calderon.ActualAngularRadialRemainderTopology
import Calderon.ActualAngularPiCancellations
import Calderon.ActualAngularPiRotationCoefficientTopology
import Calderon.ActualAngularPiRawZeroTopologyTransferJointRegularity
import Calderon.ActualAngularHighDraft
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.SignedTaylorFixedLinearTransport
import Calderon.ActualHighSmoothMultiplierBoundaryCommutator
import Calderon.ActualHighSmoothMultiplierFixedTopology
import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderTopologyCoercivity
import Calderon.ActualReferenceUpperRotationCommutatorJointJets
import Calderon.ActualReferenceSharpRotationRemainderDefinition
import Calderon.ActualHighAdjointSmoothMultiplierBoundaryGraph
import Calderon.ActualReferenceHighAdjointRadialNativeJets
import Calderon.ActualReferenceSmoothMultiplierBoundaryCommutator
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.NativeThreeHalfRotationMultiplierProductRule
import Calderon.NativeCoefficientRotationProductRule
import Calderon.NativeNegativeHalfCoefficientCoordinateProduct
import Calderon.SphereSobolevInclusion
import Calderon.ActualPiNativeOperatorGerms

/-! DRAFT NOT CHECKED (claude-actual-angular-Pi-2026-10-28-v013, Claude Opus 5.5, author
only, nothing compiled or run). Full before-source mathematics: output/MATHEMATICS.md.
v025 repair (author only, not compiled): explicit equality elimination replaces the
coordinate-jet `rw … at h`, `obtain` acts only on free variables, and the sharp rotation
smoothness uses an explicit function equality instead of `simpa [comp_def]`.

* Part I (namespace `ActualAngularHighDraft`, provisional parent reused): successor of the
  exposed sharp multiplier graph (the original definition owner collides with the Coercivity
  owner, so the signed transport is reproduced), and the UNCONDITIONAL actual `[A,S]` ALL-Hi
  graph, joint smoothness and compact within-jet caps on ONE common room, intersected with
  the parent `[a,T]` room. The `[a,T]` gains/graphs are retained, and their caps recomputed
  on the shared room.
* Part II (namespace `ActualAngularPiDraft`): raw zero-radial degree–multiplier producers,
  raw sharp zero = shifted degree, rotation-derivative jets, coordinate commutation, the true
  `E[a,Pi] : Hi → Hi` and `E[Pi,A] : Half → Half`, and the two mixed high maps with literal
  graphs for the ACTUAL Pi coefficient frozen at the current `(p, ℓ)`, `‖ℓ‖ ≤ 1`.
* NOT claimed: caps for the Pi mixed maps (MISSING-SOURCES §2), D_Q, L, cross, coercivity,
  density, Main. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

local instance v013ASHighComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v013ASHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v013ASNegativeComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v013ASHighHighClmComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance v013ASHighHalfClmComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
  (EuclideanSpace.single j (1 : ℝ))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hreg : FixedDirichletRegularity) (hg : IsAdmissibleMetric g)
  (hKernel : UnitBallValueTraceKernel τ0)

local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-! ### §1 Finite physical room guard and the successor sharp multiplier graph -/

/-- The five conjuncts of `exists_reference_commonRadius_finitePhysicalDomain_room`. -/
abbrev finiteRoomGuard (lam Lam : ℝ) (p : Pphys) : Prop :=
  TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam ∧
  UnitBallSmallDriftData (fun z => a (p,z))
    (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam ∧
  p ∈ Ω ∧
  ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible ∧
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) ∧
  ∀ x : UnitSphere, (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible

local notation "Guard" => finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData

include hreg in
lemma exists_finiteRoomGuard :
    ∃ lam Lam d : ℝ, 0 < lam ∧ 0 < d ∧ d ≤ ρ ∧
      ∀ p ∈ commonRoom y0 ρ d, Guard lam Lam p :=
  exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceStrongDriftFamily referenceSharpRadialTraceFamily

include hreg hKernel in
/-- Lemma S1: successor of `exists_reference_commonRadius_highSmoothMultiplierSecondRemainder_sharp_graph`,
against the Coercivity definition owner, with the strict radius stated directly. -/
lemma sharpMultiplierRemainder_graph_of_guard (lam Lam d : ℝ)
    (hFin : ∀ p ∈ commonRoom y0 ρ d, Guard lam Lam p)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : y ∈ closedBall y0 ρ) (r : ℝ) (hr : |r| < d)
    (Q : SmoothCoefficientJets 3) (f : Hi) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q q y r f) =
    referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q f) -
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
      (referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r f) := by
  have hAt (t : ℝ) (ht : |t| ≤ d) : Guard lam Lam (q,(y,t)) :=
    hFin (q,(y,t))
      (show (q,(y,t)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) from
        ⟨hq,hy,abs_le.mp ht⟩)
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| < d := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*r| ≤ |r| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)
    linarith
  let A : ℝ → Hi →L[ℝ] Hi := fun t =>
    referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))
  let S : ℝ → Hi →L[ℝ] Half := fun t =>
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let Post : (Hi →L[ℝ] Hi) →L[ℝ] Half := I.comp (ContinuousLinearMap.apply ℝ Hi f)
  let Contrast : (Hi →L[ℝ] Half) →L[ℝ] Half :=
    ContinuousLinearMap.apply ℝ Half (MH f) - ML.comp (ContinuousLinearMap.apply ℝ Half f)
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) :=
    (contDiffAt_referenceHighSmoothMultiplierBoundaryCommutatorFamily_fixed
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,θ*r))
        (hAt (θ*r) (hScaled θ hθ).le).2.2.2.1.1
        (hAt (θ*r) (hScaled θ hθ).le).2.2.2.1.2).comp
          (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hSS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ S (θ*r) :=
    (contDiffAt_referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,θ*r))
        (hAt (θ*r) (hScaled θ hθ).le).2.2.2.1.2).comp
          (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => Post (A t)) =ᶠ[𝓝 (θ*r)] (fun t => Contrast (S t)) := by
    have hOpen : IsOpen {t : ℝ | |t| < d} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hOpen.mem_nhds (hScaled θ hθ)] with t ht
    have hWeak := isInvertible_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t)) lam (hAt t ht.le).2.1
    exact referenceHighSmoothMultiplierBoundaryCommutatorFamily_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel Q (q,(y,t)) lam Lam
        (hAt t ht.le).1 (hAt t ht.le).2.1.1 hWeak f
  have hSame : Post (secondTaylorRemainder A r) = Contrast (secondTaylorRemainder S r) :=
    (secondTaylorRemainder_fixed_linear_map A Post r hAS).trans
      ((secondTaylorRemainder_eq_of_locallyEq_on_segment
        (fun t => Post (A t)) (fun t => Contrast (S t)) r hEq).trans
          (secondTaylorRemainder_fixed_linear_map S Contrast r hSS).symm)
  simpa only [referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder,
    referenceSharpRadialTraceSecondRemainder,Post,Contrast,A,S,I,MH,ML,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.sub_apply] using hSame

/-! ### §2 Actual `[A,S]` pieces as functions of the room point -/

/-- The sharp Hi→Hi coordinate multiplier gain `Gh_j(p)` (Coercivity owner). -/
def sharpMultiplierGain (j : Fin 3) (p : Pphys) : Hi →L[ℝ] Hi :=
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets j) p.1 p.2.1 p.2.2

/-- Formula (1) of the parent, as a function of the room point. -/
def raisingCommutator (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  raisingAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
    i p.1 p.2.1 p.2.2

local notation "ShS" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "SlS" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "GhS" => sharpMultiplierGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CAS" => raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CaT" => loweringAngularHighCommutator hcalc hF hO hD τ0
  g L y0 Φ B ε C ρ H a w hData hreg

lemma contDiffAt_sharpRotationGain (j i : Fin 3) (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun z : Pphys => referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i z.1 z.2.1 z.2.2) p := by
  let F : (ℝ × R3) × ℝ → Hi →L[ℝ] Half := fun z =>
    referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i (z.1.1,(z.1.2,z.2))
  let Ωs : Set ((ℝ × R3) × ℝ) := {z | (z.1.1,(z.1.2,z.2)) ∈ Ω}
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hΩs : IsOpen Ωs :=
    hOpen.preimage (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hFSmooth : ContDiffOn ℝ ∞ F Ωs := by
    intro z hz
    have hi : (z.1.1,(z.1.2,z.2)) ∈ Ω := hz
    exact ((contDiffAt_referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i (z.1.1,(z.1.2,z.2)) hi.1 hi.2.1).comp
      (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) z
        (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hR : ContDiffAt ℝ ∞
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2)
        ((p.1,p.2.1),p.2.2) :=
    contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ωs hΩs hFSmooth (p.1,p.2.1) p.2.2 hSeg
  have hOut := hR.comp (f := fun z : Pphys => ((z.1,z.2.1),z.2.2)) p
    ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  -- explicit function equality (projections of pairs and one definition unfolding)
  have hFun : (fun z : Pphys => referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i z.1 z.2.1 z.2.2) =
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) ∘
        (fun z : Pphys => ((z.1,z.2.1),z.2.2)) := by
    funext x
    rfl
  rw [hFun]
  exact hOut

lemma contDiffAt_sharpMultiplierGain (lam Lam d : ℝ)
    (hFin : ∀ p ∈ commonRoom y0 ρ d, Guard lam Lam p)
    (j : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ d) (hr : |p.2.2| < d) :
    ContDiffAt ℝ ∞ (GhS j) p := by
  have hSeg : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1
        (p.2.1,θ*p.2.2)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1
        (p.2.1,θ*p.2.2)).IsInvertible := by
    intro θ hθ
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*p.2.2| ≤ |p.2.2| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)).trans_eq (one_mul _)
    have hGd : Guard lam Lam (p.1,(p.2.1,θ*p.2.2)) := hFin (p.1,(p.2.1,θ*p.2.2))
      (show (p.1,(p.2.1,θ*p.2.2)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) from
        ⟨hp.1,hp.2.1,abs_le.mp (show |θ*p.2.2| ≤ d by linarith)⟩)
    exact hGd.2.2.2.1
  have hJoint := contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
    g L y0 Φ B ε C ρ H a w hData (T := ℝ) (coordinateCoefficient j)
    (contDiff_coordinateCoefficient j) (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
    (coordinateCoefficient_support j) hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 0 hSeg
  have hOut := hJoint.comp (f := fun z : Pphys => (z,(0 : ℝ))) p
    (contDiffAt_id.prodMk contDiffAt_const)
  exact hOut

/-! ### §2 Final actual theorem: BOTH angular high commutators on ONE room -/

include hreg hg hKernel in
theorem exists_reference_commonRadius_angularHigh_both_graph_caps :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ j : Fin 3, ContDiffOn ℝ ∞ (G j) (commonRoom y0 ρ δ)) ∧
      (∀ j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ v : Half,
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G j p v) =
          Tl p ((Ml j) v) - (Mn j) (Tl p v)) ∧
      (∀ i : Fin 3,
        (∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CaT G i p u) =
            loweringLow hF hO hD i (Th p u) - Tl p (loweringHigh hF hO hD i u)) ∧
        ContDiffOn ℝ ∞ (CaT G i) (commonRoom y0 ρ δ) ∧
        ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ commonRoom y0 ρ δ,
          ‖iteratedFDerivWithin ℝ n (CaT G i) (commonRoom y0 ρ δ) p‖ ≤ M) ∧
      (∀ j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
        sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (GhS j p u) =
          ShS p ((Mh j) u) - (Ml j) (ShS p u)) ∧
      ∀ i : Fin 3,
        (∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CAS i p u) =
            raisingLow hF hO hD i (ShS p u) - SlS p (raisingHigh hF hO hD i u)) ∧
        ContDiffOn ℝ ∞ (CAS i) (commonRoom y0 ρ δ) ∧
        ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ commonRoom y0 ρ δ,
          ‖iteratedFDerivWithin ℝ n (CAS i) (commonRoom y0 ρ δ) p‖ ≤ M := by
  have hρ : 0 < ρ := hData.1.2.1
  -- the parent `[a,T]` room and its exact gains, retained (destructured as a free variable)
  have hParent := exists_reference_commonRadius_loweringAngularHigh_graph_caps
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
  obtain ⟨δ1,hδ1,hδ1ρ,hRoom1,G,hGOn1,hGg1,hCaT1⟩ := hParent
  -- the actual finite physical room (raw multiplier guards)
  have hGuard := exists_finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  obtain ⟨lam,Lam,d,_hlam,hd,_hdρ,hFin⟩ := hGuard
  -- ONE shared room, chosen before any q, profile, input or cutoff
  let δ : ℝ := min δ1 (d/2)
  have hδ : 0 < δ := lt_min hδ1 (by positivity)
  have hδ1le : δ ≤ δ1 := min_le_left _ _
  have hδd : δ ≤ d/2 := min_le_right _ _
  have hSub1 : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ1 := commonRoom_mono y0 ρ hδ1le
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := hSub1.trans hRoom1
  have hSubd : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ d := commonRoom_mono y0 ρ (by linarith)
  have hrd (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) : |p.2.2| < d := by
    have h := abs_le.mpr hp.2.2
    linarith
  have hSeg (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom p hp
  have hUD : UniqueDiffOn ℝ (commonRoom y0 ρ δ) := uniqueDiffOn_commonRoom y0 ρ hρ hδ
  have hK : IsCompact (commonRoom y0 ρ δ) := isCompact_commonRoom y0 ρ δ
  -- sharp multiplier graph (discharged, no hypothesis)
  have hSharp (j : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) (f : Hi) :=
    sharpMultiplierRemainder_graph_of_guard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      hreg hKernel lam Lam d hFin p.1 (hSubd hp).1 p.2.1 (hSubd hp).2.1 p.2.2 (hrd p hp)
      (coordinateJets j) f
  have hGh (j : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) (u : Hi) :
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (GhS j p u) =
        ShS p ((Mh j) u) - (Ml j) (ShS p u) :=
    -- explicit equality elimination instead of a `rw` motive over the physical statement
    (hSharp j p hp u).trans
      (congrArg₂ (fun (A : Hi →L[ℝ] Hi) (A' : Half →L[ℝ] Half) => ShS p (A u) - A' (ShS p u))
        (coordinateJets_threeHalf hcalc hF hO hD τ0 j) (coordinateJets_half hcalc hF hO hD τ0 j))
  -- the unconditional `[A,S]` graph
  have hCASg (i : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) (u : Hi) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CAS i p u) =
        raisingLow hF hO hD i (ShS p u) - SlS p (raisingHigh hF hO hD i u) :=
    raisingAngularHighCommutator_graph_of_sharpMultiplierGraph
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg i p.1 p.2.1 p.2.2 (hSeg p hp)
      (fun j f => hSharp j p hp f) u
  -- joint smoothness of every `[A,S]` term on the room
  have hGhOn (j : Fin 3) : ContDiffOn ℝ ∞ (GhS j) (commonRoom y0 ρ δ) := fun p hp =>
    (contDiffAt_sharpMultiplierGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      lam Lam d hFin j p (hSubd hp) (hrd p hp)).contDiffWithinAt
  have hCrSOn (j i : Fin 3) : ContDiffOn ℝ ∞ (fun z : Pphys =>
      referenceSharpRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i z.1 z.2.1 z.2.2)
      (commonRoom y0 ρ δ) := fun p hp =>
    (contDiffAt_sharpRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      j i p (hSeg p hp)).contDiffWithinAt
  have hCdSOn : ContDiffOn ℝ ∞ (fun z : Pphys =>
      referenceRadialDegreeCommutatorGainedHighSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 z.1 z.2.1 z.2.2)
      (commonRoom y0 ρ δ) := fun p hp =>
    (contDiffAt_referenceRadialDegreeCommutatorGainedHighSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2
        (hSeg p hp)).contDiffWithinAt
  have hCASOn (i : Fin 3) : ContDiffOn ℝ ∞ (CAS i) (commonRoom y0 ρ δ) := by
    have hEq : CAS i = fun p : Pphys =>
        (∑ j : Fin 3, ((sphereSobolevRotationL (3/2 : ℝ) j i).comp (GhS j p) -
          (referenceSharpRadialRotationSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i p.1 p.2.1 p.2.2).comp (Mh j))) -
        (sphereSobolevShiftedDegreeL (3/2 : ℝ)).comp (GhS i p) +
        (referenceRadialDegreeCommutatorGainedHighSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2).comp (Mh i) := rfl
    rw [hEq]
    apply ContDiffOn.add
    · apply ContDiffOn.sub
      · apply ContDiffOn.sum
        intro j _
        exact (contDiffOn_const.clm_comp (hGhOn j)).sub ((hCrSOn j i).clm_comp contDiffOn_const)
      · exact contDiffOn_const.clm_comp (hGhOn i)
    · exact hCdSOn.clm_comp contDiffOn_const
  have hCaTOn (i : Fin 3) : ContDiffOn ℝ ∞ (CaT G i) (commonRoom y0 ρ δ) :=
    (hCaT1 i).2.1.mono hSub1
  refine ⟨δ,hδ,hδ1le.trans hδ1ρ,hRoom,G,fun j => (hGOn1 j).mono hSub1,?_,?_,?_,?_⟩
  · intro j p hp v
    exact (hGg1 j p (hSub1 hp)).2 v
  · intro i
    refine ⟨fun p hp u => (hCaT1 i).1 p (hSub1 hp) u,hCaTOn i,?_⟩
    intro N
    exact exists_compact_iteratedFDerivWithin_bound (CaT G i) (commonRoom y0 ρ δ) hK hUD
      (hCaTOn i) N
  · exact hGh
  · intro i
    refine ⟨hCASg i,hCASOn i,?_⟩
    intro N
    exact exists_compact_iteratedFDerivWithin_bound (CAS i) (commonRoom y0 ρ δ) hK hUD
      (hCASOn i) N

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft

/-! ## Part II: actual Pi mixed gains -/

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation MetricOperator
  NormalCoordinatesFrame NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier NativeNegativeHalfSmoothMultiplier ActualAngularHighDraft

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)

local instance v013PiHighComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v013PiHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v013PiNegativeComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

/-! ### Generic typed cancellations (MATHEMATICS.md §6–§7) -/



/-! ### §5 Rotation-derivative jets with the SAME sphere values -/

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
  (EuclideanSpace.single j (1 : ℝ))
local notation "natH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "natL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "natN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "low" => smoothMultiplierLowerJets

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevLinearCoordinateMulL

/-- (14) high rotation product rule at the index pair `(j,i)`. -/
lemma rotation_high_product (Q : SmoothCoefficientJets 3) (j i : Fin 3) (u : Hi) :
    sphereSobolevRotationL (3/2 : ℝ) j i (natH Q u) =
      natL (low Q) (sphereSobolevRotationL (3/2 : ℝ) j i u) + IH (natH (rotationJets Q j i) u) :=
  congrArg (fun A : Hi →L[ℝ] Half => A u)
    (sphereSobolevRotationL_nativeThreeHalfCoefficient_product_rule hcalc hF hO hD τ0
      Q (rotationJets Q j i) (low Q) (low (rotationJets Q j i))
      (coefficientValue_smoothMultiplierLowerJets Q).symm
      (coefficientValue_smoothMultiplierLowerJets (rotationJets Q j i)).symm j i
      (rotationJets_lower_sphere Q j i))

/-- (14') half rotation product rule at `(j,i)`, with `MN_G J = J ML_G`. -/
lemma rotation_half_product (Q : SmoothCoefficientJets 3) (j i : Fin 3) (v : Half) :
    sphereSobolevRotationL (1/2 : ℝ) j i (natL (low Q) v) =
      natN (low Q) (sphereSobolevRotationL (1/2 : ℝ) j i v) +
        JL (natL (low (rotationJets Q j i)) v) := by
  have h := congrArg (fun A : Half →L[ℝ] NegH => A v)
    (sphereSobolevRotationL_nativeCoefficient_product_rule hcalc hF hO hD τ0
      (low Q) (low (rotationJets Q j i)) j i (rotationJets_lower_sphere Q j i))
  have hJ := congrArg (fun A : Half →L[ℝ] NegH => A v)
    (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
      (low (rotationJets Q j i)))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] at h hJ
  exact h.trans (congrArg (fun z : NegH => natN (low Q) (sphereSobolevRotationL (1/2 : ℝ) j i v) + z) hJ.symm)

/-! ### Lemma C: native multipliers commute with coordinate multipliers -/

lemma negativeHalf_native_coordinate_comm (F : SmoothCoefficientJets 2) (j : Fin 3) (u : NegH) :
    natN F ((Mn j) u) = (Mn j) (natN F u) := by
  let J0 : SphereSobolev 0 →L[ℝ] NegH := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let X0 := sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single j (1 : ℝ))
  let MNF := natN F
  let CF := sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F))
  let CX := sphereContinuousScalarMulL (sphereCoordinate j)
  have hX0 (v : SphereL2) : X0 (Z v) = Z (CX v) := by
    have he := sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD
      (EuclideanSpace.single j (1 : ℝ)) v
    simp only [sphereLinearCoordinateMulL_single,sphereCoordinateMulL_eq_scalarMulL] at he
    exact he
  have hX0' (z : SphereSobolev 0) : X0 z = Z (CX (Z.symm z)) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hX0 (Z.symm z)
  have hComm (v : SphereL2) : CF (CX v) = CX (CF v) := by
    show sphereContinuousScalarMulL _ (sphereContinuousScalarMulL _ v) =
      sphereContinuousScalarMulL _ (sphereContinuousScalarMulL _ v)
    rw [sphereContinuousScalarMulL_mul_apply, sphereContinuousScalarMulL_mul_apply, mul_comm]
  have hMN (z : SphereSobolev 0) : MNF (J0 z) = J0 (Z (CF (Z.symm z))) :=
    NativeNegativeHalfCoefficientCoordinateProduct.nativeNegativeHalfCoefficientMulL_zero_inclusion
      hcalc hF hO hD τ0 F z
  have hMn (z : SphereSobolev 0) : (Mn j) (J0 z) = J0 (X0 z) :=
    (sphereSobolevInclusionL_linearCoordinateMul hF hO hD 0 (-(1/2 : ℝ)) (by norm_num)
      (EuclideanSpace.single j (1 : ℝ)) z).symm
  have hAll : MNF.comp (Mn j) = (Mn j).comp MNF := by
    apply ContinuousLinearMap.ext
    intro x
    refine (denseRange_sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).induction_on x
      (isClosed_eq (MNF.comp (Mn j)).continuous ((Mn j).comp MNF).continuous) ?_
    intro z
    change MNF ((Mn j) (J0 z)) = (Mn j) (MNF (J0 z))
    have hSym : Z.symm (X0 z) = CX (Z.symm z) := by
      rw [hX0' z]
      exact Z.symm_apply_apply _
    calc
      MNF ((Mn j) (J0 z)) = MNF (J0 (X0 z)) := congrArg MNF (hMn z)
      _ = J0 (Z (CF (Z.symm (X0 z)))) := hMN (X0 z)
      _ = J0 (Z (CF (CX (Z.symm z)))) := congrArg (fun y : SphereL2 => J0 (Z (CF y))) hSym
      _ = J0 (Z (CX (CF (Z.symm z)))) := congrArg (fun y : SphereL2 => J0 (Z y)) (hComm (Z.symm z))
      _ = J0 (X0 (Z (CF (Z.symm z)))) := congrArg J0 (hX0 (CF (Z.symm z))).symm
      _ = (Mn j) (J0 (Z (CF (Z.symm z)))) := (hMn _).symm
      _ = (Mn j) (MNF (J0 z)) := congrArg (Mn j) (hMN z).symm
  exact congrArg (fun A : NegH →L[ℝ] NegH => A u) hAll

lemma half_native_coordinate_comm (F : SmoothCoefficientJets 2) (j : Fin 3) (v : Half) :
    natL F ((Ml j) v) = (Ml j) (natL F v) := by
  have hJ (x : Half) : JL (natL F x) = natN F (JL x) :=
    congrArg (fun A : Half →L[ℝ] NegH => A x)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 F)
  have hC (x : Half) : JL ((Ml j) x) = (Mn j) (JL x) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (EuclideanSpace.single j (1 : ℝ)) x
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  exact (hJ ((Ml j) v)).trans
    ((congrArg (natN F) (hC v)).trans
      ((negativeHalf_native_coordinate_comm hcalc hF hO hD τ0 F j (JL v)).trans
        ((congrArg (Mn j) (hJ v).symm).trans (hC (natL F v)).symm)))

/-! ### §4 Raw zero-radial producers (operator radial variable `s = 0`) -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hreg : FixedDirichletRegularity) (hg : IsAdmissibleMetric g)
  (hKernel : UnitBallValueTraceKernel τ0)

local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Guard" => finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

include hreg in
/-- Lemma Z2: raw SHARP zero equals the shifted degree. -/
lemma sharp_zero_eq_shiftedDegree (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3)
    (hy : y ∈ closedBall y0 ρ) (hp : (q,(y,(0 : ℝ))) ∈ Ω) :
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) =
      sphereSobolevShiftedDegreeL (3/2 : ℝ) := by
  have hy' : ‖y-y0‖ ≤ ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have h1 := congrArg (fun A : Hi →L[ℝ] NegH => A f)
    (referenceSharpRadialTraceFamily_lower_compatibility_on_locus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp)
  have h2 := congrArg (fun A : Hi →L[ℝ] NegH => A f)
    sphereSobolevShiftedDegree_high_half_compatibility
  simp only [ContinuousLinearMap.comp_apply] at h1 h2
  rw [h1, referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy', h2]

include hreg hKernel in
/-- Lemma H, formula (13): `I HQ^h = Bh MH_Q − ML_Q Bh`, a RAW bracket at `s = 0`. -/
lemma degree_high_multiplier (lam Lam : ℝ) (Q : SmoothCoefficientJets 3) (q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : y ∈ closedBall y0 ρ)
    (hG : Guard lam Lam (q,(y,0))) (u : Hi) :
    IH (rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q q y u) =
      sphereSobolevShiftedDegreeL (3/2 : ℝ) (natH Q u) -
        natL (low Q) (sphereSobolevShiftedDegreeL (3/2 : ℝ) u) := by
  have hρ : 0 < ρ := hData.1.2.1
  have hy' : ‖y-y0‖ ≤ ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by linarith
  have hWeak := isInvertible_referenceWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,(0 : ℝ))) lam hG.2.1
  have h := referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel Q q hq y hy2 0 lam Lam
      hG.1 hG.2.1.1 hWeak hG.2.2.1 u
  rw [referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy'] at h
  exact h

include hreg hKernel in
/-- Lemma L: `J HL_Q = Bl ML_Q − MN_Q Bl` on ALL of Half, by density of `I`. -/
lemma degree_half_multiplier (lam Lam : ℝ) (Q : SmoothCoefficientJets 3) (q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : y ∈ closedBall y0 ρ)
    (hG : Guard lam Lam (q,(y,0))) (v : Half) :
    JL (rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q q y v) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (natL (low Q) v) -
        natN (low Q) (sphereSobolevShiftedDegreeL (1/2 : ℝ) v) := by
  let HL := rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q q y
  let Bh := sphereSobolevShiftedDegreeL (3/2 : ℝ)
  let Bl := sphereSobolevShiftedDegreeL (1/2 : ℝ)
  have hWeak := isInvertible_referenceWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,(0 : ℝ))) lam hG.2.1
  have hS0 := sharp_zero_eq_shiftedDegree hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
    q hq y hy hG.2.2.1
  have hUp (f : Hi) : HL (IH f) = Bh (natH Q f) - natL (low Q) (Bh f) := by
    have h := referenceSmoothMultiplierBoundaryCommutatorFamily_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q (q,(y,0))
        hG.2.2.2.1.2 hWeak f
    rw [hS0] at h
    exact h
  have hI (f : Hi) : IH (natH Q f) = natL (low Q) (IH f) :=
    congrArg (fun A : Hi →L[ℝ] Half => A f)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q (low Q)
        (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hJ (x : Half) : JL (natL (low Q) x) = natN (low Q) (JL x) :=
    congrArg (fun A : Half →L[ℝ] NegH => A x)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (low Q))
  have hB (f : Hi) : JL (Bh f) = Bl (IH f) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A f) sphereSobolevShiftedDegree_high_half_compatibility
  let A1 : Half →L[ℝ] NegH := (JL).comp HL
  let A2 : Half →L[ℝ] NegH := Bl.comp (natL (low Q)) - (natN (low Q)).comp Bl
  have hA : A1 = A2 := by
    apply ContinuousLinearMap.ext
    intro x
    refine (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).induction_on x
      (isClosed_eq A1.continuous A2.continuous) ?_
    intro f
    change JL (HL (IH f)) = Bl (natL (low Q) (IH f)) - natN (low Q) (Bl (IH f))
    exact (congrArg (fun z : Half => JL z) (hUp f)).trans
      (((JL).map_sub (Bh (natH Q f)) (natL (low Q) (Bh f))).trans
        (congrArg₂ (fun x y : NegH => x - y)
          ((hB (natH Q f)).trans (congrArg Bl (hI f)))
          ((hJ (Bh f)).trans (congrArg (natN (low Q)) (hB f)))))
  exact congrArg (fun A : Half →L[ℝ] NegH => A v) hA

/-! ### §6 True `E[a,Q] : Hi → Hi` and `E[Q,A] : Half → Half` -/

/-- `E[a,Q]_i = Σ_j Mh_j MH_{G_{ji}} + Mh_i HQ^h`. -/
def loweringPiGain (Q : SmoothCoefficientJets 3) (i : Fin 3) (q : ℝ) (y : R3) : Hi →L[ℝ] Hi :=
  (∑ j : Fin 3, (Mh j).comp (natH (rotationJets Q j i))) +
    (Mh i).comp (rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q q y)

/-- `E[Q,A]_i = Σ_j ML_{G_{ji}} Ml_j − HL_Q Ml_i`. -/
def raisingPiGain (Q : SmoothCoefficientJets 3) (i : Fin 3) (q : ℝ) (y : R3) :
    Half →L[ℝ] Half :=
  (∑ j : Fin 3, (natL (low (rotationJets Q j i))).comp (Ml j)) -
    (rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q q y).comp (Ml i)

include hreg hKernel in
lemma loweringPiGain_graph (lam Lam : ℝ) (Q : SmoothCoefficientJets 3) (i : Fin 3) (q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : y ∈ closedBall y0 ρ)
    (hG : Guard lam Lam (q,(y,0))) (u : Hi) :
    IH (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q i q y u) =
      loweringHigh hF hO hD i (natH Q u) - natL (low Q) (loweringHigh hF hO hD i u) := by
  exact lowering_multiplier_cancellation IH (fun j => sphereSobolevRotationL (3/2 : ℝ) j i)
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)) (fun j => Mh j) (fun j => Ml j) (natH Q)
    (natL (low Q)) (fun j => natH (rotationJets Q j i))
    (rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q q y) i
    (fun j x => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single j (1 : ℝ)) x)
    (fun j x => (half_native_coordinate_comm hcalc hF hO hD τ0 (low Q) j x).symm)
    (fun j x => rotation_high_product hcalc hF hO hD τ0 Q j i x)
    (fun x => degree_high_multiplier hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg
      hKernel lam Lam Q q hq y hy hG x) u

include hreg hKernel in
lemma raisingPiGain_graph (lam Lam : ℝ) (Q : SmoothCoefficientJets 3) (i : Fin 3) (q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : y ∈ closedBall y0 ρ)
    (hG : Guard lam Lam (q,(y,0))) (v : Half) :
    JL (raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q i q y v) =
      natN (low Q) (raisingLow hF hO hD i v) - raisingLow hF hO hD i (natL (low Q) v) := by
  exact raising_multiplier_cancellation JL (fun j => sphereSobolevRotationL (1/2 : ℝ) j i)
    (sphereSobolevShiftedDegreeL (1/2 : ℝ)) (fun j => Ml j) (natL (low Q)) (natN (low Q))
    (fun j => natL (low (rotationJets Q j i)))
    (rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q q y) i
    (fun j x => (half_native_coordinate_comm hcalc hF hO hD τ0 (low Q) j x).symm)
    (fun j x => rotation_half_product hcalc hF hO hD τ0 Q j i x)
    (fun x => degree_half_multiplier hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
      hKernel lam Lam Q q hq y hy hG x) v

/-! ### §7 Mixed high maps on the original common room -/

local notation "ShS" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "SlS" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CAS" => raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CaT" => loweringAngularHighCommutator hcalc hF hO hD τ0
  g L y0 Φ B ε C ρ H a w hData hreg

/-- `C[a_i, T Pi] = CaT_i PiH + Th E[a,Pi]_i`, with `Q` the frozen Pi jets. -/
def loweringMixed (G : Fin 3 → Pphys → Half →L[ℝ] Half) (Q : SmoothCoefficientJets 3)
    (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  (CaT G i p).comp (natH Q) +
    (Th p).comp (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q i p.1 p.2.1)

/-- `C[Pi S, A_i] = −PiL CAS_i + E[Pi,A]_i Sh`. -/
def raisingMixed (Q : SmoothCoefficientJets 3) (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  -((natL (low Q)).comp (CAS i p)) +
    (raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q i p.1 p.2.1).comp (ShS p)

include hreg hg hKernel in
/-- Theorem E + Theorem M: actual Pi gains and the literal mixed graphs, ALL inputs, on ONE
common room; the Pi coefficient is frozen at the CURRENT `(p, ℓ)` with `‖ℓ‖ ≤ 1`, while the
degree/multiplier operators are RAW at the separate operator radial variable `s = 0`. -/
theorem exists_reference_commonRadius_actualPi_mixed_graphs :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k)) (Km : Set R3)
      (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0),
      ∀ i k : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ ell ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1,
        let Q := commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (p,ell)
        (natH Q = PiH k (p,ell) ∧ natL (low Q) = PiL k (p,ell) ∧
          natN (low Q) = PiN k (p,ell)) ∧
        (∀ u : Hi,
          IH (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q i p.1 p.2.1 u) =
            loweringHigh hF hO hD i (PiH k (p,ell) u) -
              PiL k (p,ell) (loweringHigh hF hO hD i u)) ∧
        (∀ v : Half,
          JL (raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q i p.1 p.2.1 v) =
            PiN k (p,ell) (raisingLow hF hO hD i v) -
              raisingLow hF hO hD i (PiL k (p,ell) v)) ∧
        (∀ u : Hi,
          JL (loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg G Q i p u) =
            loweringLow hF hO hD i (Th p (PiH k (p,ell) u)) -
              Tl p (PiL k (p,ell) (loweringHigh hF hO hD i u))) ∧
        (∀ u : Hi,
          JL (raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Q i p u) =
            PiN k (p,ell) (SlS p (raisingHigh hF hO hD i u)) -
              raisingLow hF hO hD i (PiL k (p,ell) (ShS p u))) := by
  -- v025: every existential producer is first bound to a free variable, then destructured
  have hBoth := exists_reference_commonRadius_angularHigh_both_graph_caps
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
  obtain ⟨δA,hδA,hδAρ,hRoomA,G,_hGOn,_hGlow,hCaT,_hGh,hCAS⟩ := hBoth
  have hGuard := exists_finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  obtain ⟨lam,Lam,d,_hlam,hd,_hdρ,hFin⟩ := hGuard
  have hGerms := exists_referencePi_commonSupport_native_operator_germs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨dP,hdP,_hdPρ,m,hm,Km,hKm,hmz,hGerm⟩ := hGerms
  -- ONE room: the `[a,T]`/`[A,S]` room intersected with the Pi germ room
  let δ : ℝ := min δA dP
  have hδ : 0 < δ := lt_min hδA hdP
  have hSubA : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δA := commonRoom_mono y0 ρ (min_le_left _ _)
  have hSubP : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dP := commonRoom_mono y0 ρ (min_le_right _ _)
  refine ⟨δ,hδ,(min_le_left _ _).trans hδAρ,hSubA.trans hRoomA,G,m,hm,Km,hKm,hmz,?_⟩
  intro i k p hp ell hell Q
  have hpA := hSubA hp
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hRoomA p hpA
  -- raw guards at the ZERO radial operator point, from the same finite room
  have hG0 : Guard lam Lam (p.1,(p.2.1,0)) := hFin (p.1,(p.2.1,0))
    (show (p.1,(p.2.1,(0 : ℝ))) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) from
      ⟨hpA.1,hpA.2.1,(show (0 : ℝ) ∈ Icc (-d) d from Set.mem_Icc.mpr ⟨by linarith,by linarith⟩)⟩)
  -- actual Pi identification at the CURRENT point, `‖ℓ‖ ≤ 1`
  have hId : natH Q = PiH k (p,ell) ∧ natL (low Q) = PiL k (p,ell) ∧
      natN (low Q) = PiN k (p,ell) :=
    (hGerm k (p,ell) (Set.mk_mem_prod (hSubP hp) hell)).self_of_nhds
  obtain ⟨hIdH,hIdL,hIdN⟩ := hId
  have hEa (u : Hi) := loweringPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hreg hg hKernel lam Lam Q i p.1 hpA.1 p.2.1 hpA.2.1 hG0 u
  have hEA (v : Half) := raisingPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hreg hKernel lam Lam Q i p.1 hpA.1 p.2.1 hpA.2.1 hG0 v
  refine ⟨⟨hIdH,hIdL,hIdN⟩,?_,?_,?_,?_⟩
  · intro u
    exact (hEa u).trans (congrArg₂
      (fun (PH : Hi →L[ℝ] Hi) (PL : Half →L[ℝ] Half) =>
        loweringHigh hF hO hD i (PH u) - PL (loweringHigh hF hO hD i u)) hIdH hIdL)
  · intro v
    exact (hEA v).trans (congrArg₂
      (fun (PN : NegH →L[ℝ] NegH) (PL : Half →L[ℝ] Half) =>
        PN (raisingLow hF hO hD i v) - raisingLow hF hO hD i (PL v)) hIdN hIdL)
  · intro u
    have hMixed := mixed_lowering_cancellation IH JL (CaT G i p) (Th p) (Tl p) (natH Q) (natL (low Q))
      (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q i p.1 p.2.1)
      (loweringHigh hF hO hD i) (loweringLow hF hO hD i)
      (fun x => (hCaT i).1 p hpA x)
      (fun x => congrArg (fun A : Hi →L[ℝ] NegH => A x)
        (referenceAdjointRadialSecondRemainder_high_half_compatibility
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p.1 p.2.1 p.2.2 hSeg))
      hEa u
    exact hMixed.trans (congrArg₂
      (fun (PH : Hi →L[ℝ] Hi) (PL : Half →L[ℝ] Half) =>
        loweringLow hF hO hD i (Th p (PH u)) - Tl p (PL (loweringHigh hF hO hD i u))) hIdH hIdL)
  · intro u
    have hMixed := mixed_raising_cancellation JL (CAS i p) (ShS p) (SlS p) (natL (low Q)) (natN (low Q))
      (raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q i p.1 p.2.1)
      (raisingHigh hF hO hD i) (raisingLow hF hO hD i)
      (fun x => (hCAS i).1 p hpA x)
      (fun x => congrArg (fun A : Half →L[ℝ] NegH => A x)
        (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (low Q)))
      hEA u
    exact hMixed.trans (congrArg₂
      (fun (PN : NegH →L[ℝ] NegH) (PL : Half →L[ℝ] Half) =>
        PN (SlS p (raisingHigh hF hO hD i u)) - raisingLow hF hO hD i (PL (ShS p u))) hIdN hIdL)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft.sharpMultiplierRemainder_graph_of_guard
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft.exists_reference_commonRadius_angularHigh_both_graph_caps
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.negativeHalf_native_coordinate_comm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.sharp_zero_eq_shiftedDegree
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.degree_half_multiplier
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.loweringPiGain_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.raisingPiGain_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.exists_reference_commonRadius_actualPi_mixed_graphs
