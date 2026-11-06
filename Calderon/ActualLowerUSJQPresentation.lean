import Calderon.ActualLowerUSZeroAngularSum
import Calderon.ActualLowerUSLowerWordAdjoints
import Calderon.ActualLowerUSAdjointCore

/-! Author-support GPT-6.1 Sol. Before-code ../gained-jq-upfront.md.
Exact complete physical J/Q reduction to the restricted actual lower quadratic
words, with the genuine fixed Js and the full nonfinite Qout. No analytical
cap callback or replacement physical operator. No compilation by author. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJQPresentation
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  ActualHigherSZeroPhysicalGraph ActualLowerUSZeroAngularSum
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
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
local notation "J" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Js" => nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr

/-- Exact bilinear expansion against full physical Qout. Only genuine finite
inputs JG and Word_ij G are supplied to Qout; its outputs are not declared finite. -/
theorem nativeJQ_eq_lower_word_sum
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1)
    (c : (LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) → R3 → ℝ)
    (hc : ∀ ij, ContDiff ℝ ∞ (c ij))
    (hJ : J = coreScalarCombination hO hD Word c hc)
    (F G : smoothCompactFiniteSphereCore hO hD)
    (hTG : ∀ y ∈ tsupport G.val, (Tq dr Ar p q) y ∈ ParamRoom δ) (x : R3) :
    ⟪(Js F).val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q G x⟫_ℝ -
      ⟪F.val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q (J G) x⟫_ℝ =
    ∑ ij, c ij x *
      (⟪(WordStar ij F).val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q G x⟫_ℝ -
        ⟪F.val x,Qout hreg δ0 W g2 dr Ar p hdr hAr q (Word ij G) x⟫_ℝ) := by
  have hTJ : ∀ y ∈ tsupport (J G).val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hTG y ((finiteCoreSupportPreserving_nativeULowerAdjointZeroCoefficient
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr G) hy)
  have hTW : ∀ ij, ∀ y ∈ tsupport (Word ij G).val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun ij y hy => hTG y ((finiteCoreSupportPreserving_lowerQuadraticWord hO hD hF ij G) hy)
  have hLift : UF (J G) x = ∑ ij, c ij x • UF (Word ij G) x := by
    rw [hJ]
    exact finiteCoreSobolevLift_presentation hO hD (3/2 : ℝ) Word c hc G x
  have hQ := nativeZeroOut_weighted_sum_of_lift_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq
    (fun ij => c ij x) (J G) (fun ij => Word ij G) hTJ hTW x hLift
  have hStar := nativeJs_inner_eq_presentation_sum hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
    Word WordStar (lowerQuadraticWord_inner_adjoint hO hD hF) c hc hJ F x
    (Qout hreg δ0 W g2 dr Ar p hdr hAr q G x)
  rw [hStar,hQ]
  simp only [inner_sum,real_inner_smul_right,mul_sub,Finset.sum_sub_distrib]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJQPresentation
