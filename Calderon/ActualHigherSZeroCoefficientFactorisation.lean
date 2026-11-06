import Calderon.ActualHigherSZeroCanonicalIdentity
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
open ReferenceDensityBounds ActualHigherSZeroCoefficientJetBounds
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ConformalDepth ReferenceWeightedApproximation ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualGeneratorRadialGainedRows ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms SphereHarmonic.DegreeGraphLifting ActualHorizontalNormBridge NormalCoordinatesFrame
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def factorHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighNormed
@[instance_reducible] private def factorHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighSpace
@[instance_reducible] private def factorLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowNormed
@[instance_reducible] private def factorLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowSpace
@[instance_reducible] private def factorZeroNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroNormed
@[instance_reducible] private def factorZeroSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroSpace
@[instance_reducible] private def factorParameterNormed : NormedAddCommGroup Tpar := inferInstance
attribute [local instance] factorParameterNormed
@[instance_reducible] private def factorParameterSpace : NormedSpace ℝ Tpar := inferInstance
attribute [local instance] factorParameterSpace
@[instance_reducible] private def factorDerivativeNormed : NormedAddCommGroup (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeNormed
@[instance_reducible] private def factorDerivativeSpace : NormedSpace ℝ (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeSpace

attribute [local irreducible] ActualHigherSCoefficientExtraction.zeroCoefficient
attribute [local irreducible] canonicalHigh canonicalLow referenceDensityPrincipalFrameCoefficient
 normalizedSecondDriftFrameJoint referenceMetricGramFrame

section Native
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "XP" => parameterGramFrame g L
local notation "GP" => parameterConnection g L
local notation "OL" => parameterLowerAngular g L
local notation "OH" => parameterHighAngular g L
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QP" g2:max i:max j:max t:max => referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i j
local notation "DP" g2:max i:max t:max => normalizedSecondDriftFrameJoint g g2 L i (t.1.1,t.1.2.1)

local notation "ZR" => regularZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => logarithmicZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PHI" => zeroParameterFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PSI" => zeroHessianFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] ActualHigherSCoefficientExtraction.secondZeroRow
 ActualHigherSCoefficientExtraction.profileHigh regularZeroRow logarithmicZeroRow parameterGramFrame


attribute [local irreducible] zeroParameterFactor zeroHessianFactor
  ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient

/-- Actual factors, with eventual equality derived from ambient C1 neighborhoods, not closed-room equality. -/
theorem canonicalZeroFactorisation_actual
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    CanonicalZeroFactorisation g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ g2 := by
  refine ⟨PHI g2,PSI g2,?_,?_,?_⟩
  · intro t ht
    exact (canonical_zero_factor_germs g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 t ht).1
  · intro mk t ht
    exact (canonical_zero_factor_germs g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 t ht).2 mk
  · intro δr Ar p hδr hAr q hq x hx
    have hNear (j : Fin 3) : ∀ᶠ z in 𝓝 ((Tq δr Ar p q) x), DifferentiableAt ℝ (EH j) z := by
      have h1 : ContDiffAt ℝ (1 : ℕ∞ω) (EH j) ((Tq δr Ar p q) x) :=
        (Cm.germHigh j _ hx).of_le (by simp)
      exact (h1.eventually (by simp)).mono (fun z hz => hz.differentiableAt (by simp))
    have hAll : ∀ᶠ z in 𝓝 ((Tq δr Ar p q) x), ∀ j : Fin 3, DifferentiableAt ℝ (EH j) z :=
      Filter.eventually_all.2 hNear
    have hTP : ContDiff ℝ ∞ (Tq δr Ar p q) := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q
    have hPull : ∀ᶠ y in 𝓝 x, ∀ j : Fin 3, DifferentiableAt ℝ (EH j) ((Tq δr Ar p q) y) :=
      (Continuous.continuousAt (ContDiff.continuous hTP)).tendsto.eventually hAll
    filter_upwards [hPull] with y hy
    exact canonical_zero_factor_identity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 δr Ar p hδr hAr q y hy

/-- Unconditional actual canonical zero-coefficient two-jets, with all native quantifiers unchanged. -/
theorem canonicalZeroCoefficientJetTarget_actual
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ActualHigherSZeroCoefficientJets.CanonicalZeroCoefficientJetTarget
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ g2 :=
  canonicalZeroCoefficientJetTarget_of_factorisation g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
      (canonicalZeroFactorisation_actual g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm g2 hg2)

/-- One retained common room before g2, profiles, inputs and angular degree. -/
theorem exists_retained_canonical_zero_coefficient_uniform_two_jet_bound
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        ActualHigherSZeroCoefficientJets.CanonicalZeroCoefficientJetTarget
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact canonicalZeroCoefficientJetTarget_actual g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2

end Native
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
