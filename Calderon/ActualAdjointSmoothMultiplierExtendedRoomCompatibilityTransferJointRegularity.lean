import Calderon.ActualAdjointHighMultiplierExtendedRoomTaylor
import Calderon.ActualHighAdjointSmoothMultiplierBoundaryGraph
import Calderon.ActualAdjointHighCommonSupportGainTopologyTransferJointRegularity
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.ActualAdjointRadialSmoothMultiplierSignedTaylorFactor
import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.CollaboratorUnitBallValueTraceKernelOct17

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator
open NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily secondTaylorRemainder
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  realHalfOperatorAdjointL sphereSobolevInclusionL

/-- Original endpoint compatibility on a strict radial subroom of the same larger-centre data. -/
lemma referenceAdjointSmoothMultiplierSecondRemainder_compatible_of_extended_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (lam Lam d0 d : ℝ) (hdd0strict : d < d0)
    (hRoom : ∀ p : ℝ × (R3 × ℝ), p.1 ∈ Icc (0 : ℝ) 1 →
      p.2.1 ∈ closedBall y0 (3*ρ/2) → |p.2.2| ≤ d0 →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam ∧
      UnitBallSmallDriftData (fun z => a (p,z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam ∧
      p ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      p ∈ referenceGaugeNormalHighInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc)
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x) = 0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3)
    (hy : y ∈ closedBall y0 (3*ρ/2)) (r : ℝ) (hr : |r| ≤ d)
    (t : T) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (secondTaylorRemainder (fun tau : ℝ =>
        referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            (commonSupportCoefficientFamily 3 m hm Km hKm hmz t)
            (q,(y,tau))) r u) =
    (-realHalfOperatorAdjointL (secondTaylorRemainder (fun tau : ℝ =>
        referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
            (commonSupportCoefficientFamily 3 m hm Km hKm hmz t)
            (q,(y,tau))) r))
      (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u) := by
  classical
  have hρ : 0 < ρ := hData.1.2.1
  let Hi := SphereSobolev (3/2 : ℝ)
  let Half := SphereSobolev (1/2 : ℝ)
  let Neg := SphereSobolev (-(1/2 : ℝ))
  let Q := commonSupportCoefficientFamily 3 m hm Km hKm hmz t
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let K := sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Rh := secondTaylorRemainder (fun tau : ℝ =>
    referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,tau))) r
  let RS := secondTaylorRemainder (fun tau : ℝ =>
    referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,tau))) r
  let Gn := -realHalfOperatorAdjointL RS
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  have hK (v : Hi) : K v = J (I v) :=
    (congrArg (fun A : Hi →L[ℝ] Neg => A v)
      (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) (-(1/2 : ℝ))
        (by norm_num) (by norm_num))).symm
  have hSegment (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      (q,(y,θ*r)) ∈ referenceGaugeNormalHighInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hθr : |θ*r| ≤ d0 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans
        ((one_mul _).le.trans (hr.trans hdd0strict.le))
    have h := hRoom (q,(y,θ*r)) hq hy hθr
    exact ⟨h.2.2.1,h.2.2.2⟩
  let U0 : ℝ → Hi →L[ℝ] Half := fun tau =>
    referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (q,(y,tau))
  let V0 : ℝ → Half →L[ℝ] Neg := fun tau =>
    referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (q,(y,tau))
  let U2 := secondTaylorRemainder U0 r
  let V2 := secondTaylorRemainder V0 r
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by
    have hy3 : ‖y-y0‖ ≤ 3*ρ/2 := by
      simpa only [mem_closedBall,dist_eq_norm] using hy
    linarith
  have hr0 : |r| < d0 :=
    hr.trans_lt hdd0strict
  have hR2 := referenceAdjointHighMultiplier_signedTaylor_inclusion_of_extended_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
    (unitBallValueTraceKernel τ0) hg Q q hq y hy2
    r d0 lam Lam hr0
    (fun tau htau => hRoom (q,(y,tau)) hq hy htau.le)
  have hGhigh (v : Hi) : I (Rh v) = U2 (MH v)-ML (U2 v) := by
    have h := congrArg (fun A : Hi →L[ℝ] Half => A v) hR2
    simpa only [U2,U0,Q,Rh,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply] using h
  have hMH (v : Hi) : I (MH v) = ML (I v) :=
    congrArg (fun A : Hi →L[ℝ] Half => A v)
      (NativeOrderOneCoefficientMultiplier.nativeCoefficientMulL_high_half_compatibility
        hcalc hF hO hD τ0 Q (smoothMultiplierLowerJets Q)
        (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hML (v : Half) : J (ML v) = MN (J v) :=
    congrArg (fun A : Half →L[ℝ] Neg => A v)
      (nativeCoefficientMulL_half_negative_compatibility
        hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q))
  have hUV (v : Hi) : J (U2 v) = V2 (I v) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A v)
      (referenceAdjointRadialSecondRemainder_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
        q y r (fun θ hθ => (hSegment θ hθ).1))
  have hNegative := referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0
    (unitBallValueTraceKernel τ0) q y r t
    (fun θ hθ => (hSegment θ hθ).1)
  have hGneg (v : Half) : V2 (ML v)-MN (V2 v) = Gn (J v) := by
    simpa only [Q,V2,V0,ML,MN,RS,Gn,ContinuousLinearMap.neg_apply] using hNegative.1 v
  change K (Rh u) = Gn (K u)
  calc
    K (Rh u) = J (I (Rh u)) := hK _
    _ = J (U2 (MH u)-ML (U2 u)) := congrArg J (hGhigh u)
    _ = J (U2 (MH u))-J (ML (U2 u)) := J.map_sub _ _
    _ = V2 (I (MH u))-MN (J (U2 u)) :=
      congrArg₂ (fun a b : Neg => a-b) (hUV (MH u)) (hML (U2 u))
    _ = V2 (ML (I u))-MN (V2 (I u)) :=
      congrArg₂ (fun a b : Neg => a-b) (congrArg V2 (hMH u)) (congrArg MN (hUV u))
    _ = Gn (J (I u)) := hGneg (I u)
    _ = Gn (K u) := congrArg (Gn) (hK u).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
