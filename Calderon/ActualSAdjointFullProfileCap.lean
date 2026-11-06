import Calderon.ActualSAdjointSecondProfileCaps
import Calderon.ActualSAdjointAngularDoubleProfileCaps

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointFullProfileCap
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualGeneratorEPairedGainedEndpoints
  ActualHigherSSecondAdjoint ActualSAdjointSecondNegative ActualSAdjointSecondPointwiseBound
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift ActualHorizontalNormBridge
  ActualSecondGeometryCaps ActualSecondDensityProfileCaps ActualSScalarCoefficientBounds
  ActualReverseEOrdinaryCaps ActualCommonFirstWordQuadraticAdjoint ActualBalancedFirstPrincipalError
  ActualSAdjointSecondProfileCaps ActualSAdjointAngularDoubleNegative ActualSAdjointAngularDoubleProfileCaps

private lemma norm_three_add {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a+b+c‖ ≤ ‖a‖+‖b‖+‖c‖ := by
  have h1 := norm_add_le (a+b) c
  have h2 := norm_add_le a b
  linarith

private lemma map_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (u : E) (M : ℝ) (hA : ‖A‖ ≤ M) :
    ‖A u‖ ≤ M*‖u‖ :=
  (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg u))

private lemma norm_second_angular_double {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (s : Y) (A D : X →L[ℝ] Y) (u : X) (Cs Ca r beta G : ℝ)
    (hCs : 0 ≤ Cs) (hCa : 0 ≤ Ca) (hr : 0 ≤ r) (hb : 0 ≤ beta) (hG : 0 ≤ G)
    (hS : ‖s‖ ≤ Cs*(r^2*G+r^2*beta*‖u‖))
    (hA : ‖A‖ ≤ Ca*r) (hD : ‖D‖ ≤ Ca*r^3) :
    ‖s+A u+D u‖ ≤ (Cs+Ca)*(r^2*G+(r+r^2*beta+r^3)*‖u‖) := by
  let v : ℝ := r^2*G+r^2*beta*‖u‖
  let z : ℝ := (r+r^3)*‖u‖
  have hv : 0 ≤ v := add_nonneg (mul_nonneg (sq_nonneg r) hG)
    (mul_nonneg (mul_nonneg (sq_nonneg r) hb) (norm_nonneg u))
  have hz : 0 ≤ z := mul_nonneg (add_nonneg hr (pow_nonneg hr 3)) (norm_nonneg u)
  have hAn : ‖A u‖ ≤ Ca*r*‖u‖ := map_bound A u (Ca*r) hA
  have hDn : ‖D u‖ ≤ Ca*r^3*‖u‖ := map_bound D u (Ca*r^3) hD
  have hNorm : ‖s+A u+D u‖ ≤ Cs*v+Ca*r*‖u‖+Ca*r^3*‖u‖ := by
    have hn := norm_three_add s (A u) (D u)
    linarith only [hn,hS,hAn,hDn]
  have hExtra : 0 ≤ Ca*v+Cs*z := add_nonneg (mul_nonneg hCa hv) (mul_nonneg hCs hz)
  have hScale : Cs*v+Ca*r*‖u‖+Ca*r^3*‖u‖ ≤
      (Cs+Ca)*(r^2*G+(r+r^2*beta+r^3)*‖u‖) := by
    dsimp only [v,z] at hExtra ⊢
    nlinarith only [hExtra]
  exact hNorm.trans hScale

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace
@[instance_reducible] private def highNegativeNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def highNegativeSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] highNegativeNormed highNegativeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Uin" => higherSInput hO hD
local notation "PC" => SecondPointwiseCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] reverseEHigh reverseELow sphereSobolevInclusionL
  sphereSobolevShiftedDegreeL referenceHighWeightedHorizontalAction referenceLowerHorizontalAngularL
  referenceHighHorizontalAngularL

/-- Full original Sdag negative norm, with every actual cap produced before profiles. Fixed g2. -/
theorem exists_fullAdjoint_uniform_profile_norm_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 ∧ ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∃ Cs : ℝ, 0 < Cs ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖fullAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x‖ ≤
        Cs*((referenceRadius dr Ar p L x)^2*
          (∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F) x (coordinateDirection k))‖)+
          (referenceRadius dr Ar p L x+(referenceRadius dr Ar p L x)^2*
            actualReferenceBeta g L q dr Ar p x+(referenceRadius dr Ar p L x)^3)*‖Uin F x‖) := by
  obtain ⟨es,hes,hes1,hSecond⟩ := exists_secondAdjoint_uniform_profile_norm_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg δ0 W δ Cm
  obtain ⟨ea,hea,hea1,hAD⟩ := exists_angularDouble_profile_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg δ0 W δ Cm
  refine ⟨min es ea,lt_min hes hea,(min_le_left _ _).trans hes1,?_⟩
  intro g2 hg2
  obtain ⟨Cs,hCs,hS⟩ := hSecond g2 hg2
  obtain ⟨Ca,hCa,hA⟩ := hAD g2 hg2
  refine ⟨Cs+Ca,add_pos hCs hCa,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs F
  have hSx := hS q hq dr hdr hdr1 Ar hAr p hp eta heta
    (heta0.trans (min_le_left _ _)) x hx hxBall hb hs F
  have hADx := hA q hq dr hdr hdr1 Ar hAr p hp eta heta
    (heta0.trans (min_le_right _ _)) x hx hxBall hb hs
  rw [fullAdjointNegative]
  exact norm_second_angular_double _ _ _ _ Cs Ca
    (referenceRadius dr Ar p L x) (actualReferenceBeta g L q dr Ar p x)
    (∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F) x (coordinateDirection k))‖)
    hCs.le hCa.le (referenceRadius_pos dr Ar p L x hdr hAr).le (zero_le_one.trans hb)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hSx hADx.1 hADx.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointFullProfileCap
