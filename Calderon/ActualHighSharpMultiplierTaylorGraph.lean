import Calderon.ActualRaisingEHighGraph
import Calderon.ActualHighSmoothMultiplierFixedTopology
import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.ActualFinitePhysicalDomainCommonRoom

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualAngularPiDraft NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  sphereSobolevInclusionL referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  secondTaylorRemainder

/-- The literal sharp high multiplier graph survives its second radial Taylor
remainder on an actual elliptic/small-drift tube. This internal tube is discharged below. -/
lemma referenceHighMultiplier_signedTaylor_inclusion_of_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r d lam Lam : ℝ)
    (hr : |r| < d)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z => a ((q,(y,t)),z)) lam Lam ∧
      UnitBallSmallDriftData (fun z => a ((q,(y,t)),z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)) lam) :
    (IH).comp
      (secondTaylorRemainder (fun t : ℝ => referenceHighSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r) =
      (secondTaylorRemainder (fun t : ℝ => referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q)-
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)).comp
        (secondTaylorRemainder (fun t : ℝ => referenceSharpRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) := by
  let A : ℝ → Hi →L[ℝ] Hi := fun t =>
    referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))
  let S : ℝ → Hi →L[ℝ] Half := fun t =>
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| < d := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*r| ≤ |r| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)
    exact hMul.trans_lt hr
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) := by
    have hAt := hTube (θ*r) (hScaled θ hθ)
    have hHi := referenceStrongDriftFamily_isInvertible_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg 1 q (y,θ*r) lam Lam hAt.1 hAt.2.1
    have hLo := referenceStrongDriftFamily_isInvertible_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q (y,θ*r) lam Lam hAt.1 hAt.2.1
    exact (contDiffAt_referenceHighSmoothMultiplierBoundaryCommutatorFamily_fixed
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,θ*r)) hHi hLo).comp
      (θ*r) (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hSS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ S (θ*r) := by
    have hAt := hTube (θ*r) (hScaled θ hθ)
    have hLo := referenceStrongDriftFamily_isInvertible_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q (y,θ*r) lam Lam hAt.1 hAt.2.1
    exact (contDiffAt_referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,θ*r)) hLo).comp
      (θ*r) (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => (IH).comp (A t)) =ᶠ[𝓝 (θ*r)]
        (fun t => (S t).comp MH-ML.comp (S t)) := by
    have hOpen : IsOpen {t : ℝ | |t| < d} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hOpen.mem_nhds (hScaled θ hθ)] with t ht
    have hAt := hTube t ht
    have hWeak := isInvertible_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t)) lam hAt.2
    apply ContinuousLinearMap.ext
    intro f
    exact referenceHighSmoothMultiplierBoundaryCommutatorFamily_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel Q
        (q,(y,t)) lam Lam hAt.1 hAt.2.1 hWeak f
  exact secondTaylorRemainder_included_commutator A S IH MH ML r hAS hSS hEq

/-- One original common radius, before all multiplier jets and all angular inputs,
discharges every ellipticity/inverse premise in the sharp signed Taylor graph. -/
theorem exists_reference_commonRadius_highSmoothMultiplierSecondRemainder_graph
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ δ →
        ∀ (Q : SmoothCoefficientJets 3) (f : Hi),
          IH (referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q q y r f) =
          referenceSharpRadialTraceSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
              (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q f)-
          nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
            (referenceSharpRadialTraceSecondRemainder
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r f) := by
  obtain ⟨lam,Lam,d,_hlam,hd,hdρ,hRoom⟩ :=
    exists_reference_commonRadius_finitePhysicalDomain_room
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d/2,by positivity,(by linarith),?_⟩
  intro q hq y hy r hr Q f
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hrStrict : |r| < d := by linarith
  have hTube (t : ℝ) (ht : |t| < d) := hRoom (q,(y,t)) ⟨hq,hyBall,abs_le.mp ht.le⟩
  have hGraph := referenceHighMultiplier_signedTaylor_inclusion_of_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel Q q y r d lam Lam
    hrStrict (fun t ht => ⟨(hTube t ht).1,(hTube t ht).2.1⟩)
  have hValue := congrArg (fun T : Hi →L[ℝ] Half => T f) hGraph
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
    referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder,
    referenceSharpRadialTraceSecondRemainder] using hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
