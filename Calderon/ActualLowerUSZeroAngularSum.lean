import Calderon.ActualLowerUSZeroAngularLocality
import Calderon.ActualLowerUSAdjointPresentation

/-! Exact finite-sum reduction of the full physical zero output. The coefficient
presentation may be selected at the point where its mass is bounded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroAngularSum
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  ActualHigherSZeroPhysicalGraph ActualLowerUSZeroAngularLocality
  ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

lemma finiteCoreSobolevLift_sum
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    {ι : Type*} [Fintype ι] (s : ℝ)
    (F : ι → smoothCompactFiniteSphereCore hO hD) (x : R3) :
    finiteCoreSobolevLift hO hD s (∑ i, F i) x =
      ∑ i, finiteCoreSobolevLift hO hD s (F i) x := by
  unfold finiteCoreSobolevLift
  simp only [map_sum,Submodule.coe_sum,Finset.sum_apply]

lemma finiteCoreSobolevLift_presentation
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    {ι : Type*} [Fintype ι] (s : ℝ)
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    finiteCoreSobolevLift hO hD s (coreScalarCombination hO hD T c hc F) x =
      ∑ i, c i x • finiteCoreSobolevLift hO hD s (T i F) x := by
  simp only [coreScalarCombination,LinearMap.sum_apply,Module.End.mul_apply]
  rw [finiteCoreSobolevLift_sum]
  simp only [finiteCoreSobolevLift_coreScalar]

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


local notation "ZH" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZO" => nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Full physical Q preserves any exact finite scalar relation at the point.
The hypotheses are actual canonical-graph room memberships, not cap premises. -/
theorem nativeZeroHalf_weighted_sum_of_lift_eq
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (F : ι → smoothCompactFiniteSphereCore hO hD)
    (hT0 : ∀ y ∈ tsupport F0.val, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (hT : ∀ i, ∀ y ∈ tsupport (F i).val, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (x : R3) (he : UF F0 x = ∑ i, c i • UF (F i) x) :
    ZH hreg δ0 W g2 dr Ar p hdr hAr q F0 x =
      ∑ i, c i • ZH hreg δ0 W g2 dr Ar p hdr hAr q (F i) x := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  rw [nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F0 hT0 x,he]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq (F i) (hT i) x]

/-- The finite-sum law for Qout uses the actual full SphereL2 realization. -/
theorem nativeZeroOut_weighted_sum_of_lift_eq
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (F : ι → smoothCompactFiniteSphereCore hO hD)
    (hT0 : ∀ y ∈ tsupport F0.val, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (hT : ∀ i, ∀ y ∈ tsupport (F i).val, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (x : R3) (he : UF F0 x = ∑ i, c i • UF (F i) x) :
    ZO hreg δ0 W g2 dr Ar p hdr hAr q F0 x =
      ∑ i, c i • ZO hreg δ0 W g2 dr Ar p hdr hAr q (F i) x := by
  unfold nativeZeroOut
  rw [nativeZeroHalf_weighted_sum_of_lift_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq c F0 F hT0 hT x he]
  simp only [map_sum,map_smul]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroAngularSum
