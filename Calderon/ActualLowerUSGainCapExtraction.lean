import Calderon.ActualLowerUSSecondRowCoefficients
import Calderon.FixedParameterProfileBudgets

/-!
Concrete first physical caps of the retained low gains used by the T derivative.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualMixedAngularPairedGains FixedParameterProfilePullback FixedParameterProfileBudgets
  ConformalDepth ReferenceWeightedApproximation

local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
/-- Extract only the actual paired-generator low-family first caps. The
three-family imported projection is eliminated at this module boundary. -/
theorem exists_generatorLow_joint_first_cap (δ : ℝ) (gen : GRoom δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ V : Generator, ∀ a : Fin 3,
      ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom δ,
      ‖iteratedFDerivWithin ℝ n (gen.low V a) (ParamRoom δ) t‖ ≤ M := by
  let cap := gen.finiteCaps 1
  refine ⟨Classical.choose cap,(Classical.choose_spec cap).1,?_⟩
  intro V a n hn t ht
  exact ((Classical.choose_spec cap).2 V a n hn t ht).2.2

/-- Extract only the actual mixed Bl first caps, on the original retained W. -/
theorem exists_mixedLow_joint_first_cap (mixed : MRoom) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b a : Fin 3,
      ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom mixed.δ,
      ‖iteratedFDerivWithin ℝ n (mixed.Bl b a) (ParamRoom mixed.δ) t‖ ≤ M := by
  let cap := mixed.joint_caps 1
  refine ⟨Classical.choose cap,(Classical.choose_spec cap).1,?_⟩
  intro b a n hn t ht
  exact ((Classical.choose_spec cap).2 b a n hn t ht).2.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
