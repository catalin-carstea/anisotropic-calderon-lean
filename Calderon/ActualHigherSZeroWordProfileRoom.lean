import Calderon.ActualFullEPhysicalEndpoints
import Calderon.ActualHigherSAdjointFormation
import Calderon.FixedParameterProfilePullback
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ReferenceWeightedApproximation
  ConformalDepth FixedParameterProfilePullback
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)


/-- All original profile hypotheses imply membership in the same retained formation room. -/
def SamePacketZeroWordProfileRoom (dA etaWord : ℝ) : Prop :=
  ∀ q ∈ Icc (0 : ℝ) 1,
  ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,∀ p : ℕ,1 ≤ p →
  ∀ eta : ℝ,0 ≤ eta → eta ≤ etaWord → ∀ x ∈ closedBall y0 ρ,x ∈ ball y0 ρ →
  1 ≤ actualReferenceBeta g L q dr Ar p x →
  referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    (Tq dr Ar p q) x ∈ ParamRoom dA

/-- Derive the complete retained room and its uniform profile guard before any profiles.
The original adjoint contract is retained with its original witness and provenance. -/
theorem exists_same_packet_zero_word_profile_room (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ etaWord : ℝ, 0 < etaWord ∧ etaWord ≤ data.eta0 ∧
    ∃ dA : ℝ, 0 < dA ∧ dA ≤ data.δ0 ∧ dA ≤ ρ ∧
      CRoom hreg data.δ0 data.germs dA ∧
      (∀ z ∈ commonRoom y0 ρ dA, Jac z) ∧
      ActualHigherSAdjointFormation.HigherSAdjointContract
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dA ∧
      SamePacketZeroWordProfileRoom g L y0 ρ dA etaWord := by
  obtain ⟨dA,hdA,hdA0,hdArho,Cm,hJac,hAdj⟩ :=
    ActualHigherSAdjointFormation.exists_retained_higherS_adjoint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨epsG,hepsG,hepsG1,hGuard⟩ :=
    exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ dA hdA
      (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨min data.eta0 epsG,lt_min data.eta0_pos hepsG,min_le_left _ _,
    dA,hdA,hdA0,hdArho,Cm,hJac,hAdj,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs
  have hgprofile := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta
    (heta0.trans (min_le_right _ _)) x hx hxBall hb hs
  exact (higherSParam_eventually_mem y0 ρ dA L dr Ar q p hdr hAr x hgprofile).self_of_nhds
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
