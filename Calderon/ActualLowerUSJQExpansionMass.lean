import Calderon.ActualLowerUSJQPresentation

/-! Exact complete physical J/Q reduction to the restricted actual lower quadratic
words, with the genuine fixed Js and the full nonfinite Qout. No analytical
cap callback or replacement physical operator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJQExpansionMass
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  NormalizedPrincipalMetric
  ActualHigherSZeroPhysicalGraph ActualLowerUSZeroAngularSum ActualLowerUSJQPresentation
  ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

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
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UF" => ActualHigherSFormation.higherSInput hO hD


local notation "Qout" => nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Word" => lowerQuadraticWord hO hD hF
local notation "WordStar" => lowerQuadraticWordAdjoint hO hD hF

variable (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)

/-- Original-profile mass and exact physical JQ reduction are produced together.
No analytically estimated word commutator is postulated here. This is the
presentation producer consumed by the still separate gained five-group bound. -/
theorem exists_nativeJQ_lower_word_expansion_uniform_mass (hL : 0 < L) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → ∀ x ∈ closedBall y0 ρ,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∃ (c : (LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) → R3 → ℝ)
        (hc : ∀ ij, ContDiff ℝ ∞ (c ij)),
        nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr =
          coreScalarCombination hO hD Word c hc ∧
        (∑ ij, |c ij x|) ≤ CJ*eta ∧
        ∀ (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
          (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
          (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
          (F G : smoothCompactFiniteSphereCore hO hD)
          (hTG : ∀ y ∈ tsupport G.val, (Tq dr Ar p q) y ∈ ParamRoom δ),
        ⟪(nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2
            L q dr Ar p hdr hAr F).val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q G x⟫_ℝ -
          ⟪F.val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q
            (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr G) x⟫_ℝ =
        ∑ ij, c ij x *
          (⟪(WordStar ij F).val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q G x⟫_ℝ -
            ⟪F.val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q (Word ij G) x⟫_ℝ) := by
  obtain ⟨CJ,hCJ,hMass⟩ := exists_nativeULowerAdjointZero_lower_uniform_mass
    hO hD hF g g2 hg hg2 L hL y0 ρ
  refine ⟨CJ,hCJ,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs
  obtain ⟨c,hc,hJ,hcMass⟩ := hMass q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs
  refine ⟨c,hc,hJ,hcMass,?_⟩
  intro hreg δ0 W δ Cm hJac F G hTG
  exact nativeJQ_eq_lower_word_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 hg2 dr Ar p hdr hAr q hreg δ0 W δ Cm hJac hq c hc hJ F G hTG x

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJQExpansionMass
