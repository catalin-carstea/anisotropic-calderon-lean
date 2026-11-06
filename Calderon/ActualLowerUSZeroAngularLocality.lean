import Calderon.ActualHigherSZeroPhysicalGraph
import Calderon.ActualFiniteHarmonicModelScalarExpansion

/-! Native Q angular locality follows from its canonical negative graph.
No finite physical output or analytic cap is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroAngularLocality
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  ActualHigherSZeroPhysicalGraph SpectralWeightedGraph
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Scalar multiplication at the base point commutes with the exact finite lift. -/
lemma finiteCoreSobolevLift_coreScalar
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    finiteCoreSobolevLift hO hD s (coreScalar hO hD c hc F) x =
      c x • finiteCoreSobolevLift hO hD s F x := by
  have hWeight := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => (T F).val x)
    (scalarCentral_coreWeightOperator hO hD (besselWeight s) c hc).eq
  change (coreWeightOperator hO hD (besselWeight s) (coreScalar hO hD c hc F)).val x =
    c x • (coreWeightOperator hO hD (besselWeight s) F).val x at hWeight
  unfold finiteCoreSobolevLift
  rw [hWeight,map_smul]

/-- A scalar coefficient cannot enlarge a genuine finite input support. -/
lemma tsupport_coreScalar_subset
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (F : smoothCompactFiniteSphereCore hO hD) :
    tsupport (coreScalar hO hD c hc F).val ⊆ tsupport F.val := by
  apply closure_mono
  intro x hx hz
  apply hx
  change c x • F.val x = 0
  rw [hz,smul_zero]

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
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0


local notation "ZH" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZO" => nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The apparent base derivatives in the residual definition cancel exactly:
the actual full Half output depends only on the finite high input at x. -/
theorem nativeZeroHalf_eq_of_finite_lift_eq
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F G : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ tsupport G.val, (Tq dr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (he : UF F x = UF G x) :
    ZH hreg δ0 W g2 dr Ar p hdr hAr q F x =
      ZH hreg δ0 W g2 dr Ar p hdr hAr q G x := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  rw [nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF x,
    nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq G hTG x,he]

/-- Angular scalar centrality is proved through the canonical negative graph,
not by treating the cancelled residual derivatives as angular operators. -/
theorem nativeZeroHalf_coreScalar
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    ZH hreg δ0 W g2 dr Ar p hdr hAr q (coreScalar hO hD c hc F) x =
      c x • ZH hreg δ0 W g2 dr Ar p hdr hAr q F x := by
  have hTc : ∀ y ∈ tsupport (coreScalar hO hD c hc F).val,
      (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hTF y (tsupport_coreScalar_subset hO hD c hc F hy)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  rw [map_smul,
    nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq (coreScalar hO hD c hc F) hTc x,
    nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF x]
  have hLift : UF (coreScalar hO hD c hc F) x = c x • UF F x :=
    finiteCoreSobolevLift_coreScalar hO hD (3/2 : ℝ) c hc F x
  rw [hLift,map_smul]

/-- The same scalar centrality for the genuine SphereL2 physical output. -/
theorem nativeZeroOut_coreScalar
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    ZO hreg δ0 W g2 dr Ar p hdr hAr q (coreScalar hO hD c hc F) x =
      c x • ZO hreg δ0 W g2 dr Ar p hdr hAr q F x := by
  unfold nativeZeroOut
  rw [nativeZeroHalf_coreScalar g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq c hc F hTF x,map_smul]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroAngularLocality
