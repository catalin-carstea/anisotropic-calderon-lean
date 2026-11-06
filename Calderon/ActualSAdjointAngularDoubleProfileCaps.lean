import Calderon.ActualSAdjointAngularDoubleNegative
import Calderon.ActualReverseEOrdinaryCaps

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointAngularDoubleProfileCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualGeneratorEPairedGainedEndpoints
  ActualCommonFirstWordQuadraticAdjoint ActualReverseEOrdinaryCaps
  ActualSAdjointAngularDoubleNegative ReferenceWeightedApproximation ReferenceDensityBounds
  ConformalDepth SmoothMetricFrame ActualNormalizedSecondMetricDrift

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace

private theorem exists_Q_sum_cap (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (y0 : R3) (rho : ℝ) :
    ∃ MQ : ℝ, 0 < MQ ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 rho,
      (∑ i : Fin 3, ∑ j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j|) ≤ MQ := by
  let Qsum : ℝ × R3 → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 i j|
  have hCont : Continuous Qsum := by
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).continuous.abs
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_closedBall y0 rho)).exists_bound_of_continuousOn
    hCont.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro q hq x hx
  have hAbs : |Qsum (q,x)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (q,x) ⟨hq,hx⟩
  exact ((le_abs_self _).trans hAbs).trans (le_max_right _ _)

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
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "Tq" dr:max Ar:max p:max q:max => higherSParam L dr Ar p q
local notation "AN" => angularAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DN" => doubleAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BA" => angularBudget g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BD" => doubleBudget g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] reverseEHigh reverseELow loweringHigh loweringLow

/-- Actual angular and quadratic profile caps. Threshold before g2; constant fixed-g2. -/
theorem exists_angularDouble_profile_caps (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 ∧ ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∃ C_AD : ℝ, 0 < C_AD ∧ ∀ q ∈ Icc (0 : ℝ) 1,
        ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
        ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
        ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
        1 ≤ actualReferenceBeta g L q dr Ar p x →
        referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
        ‖AN g2 dr Ar p q x‖ ≤ C_AD*referenceRadius dr Ar p L x ∧
          ‖DN g2 dr Ar p q x‖ ≤ C_AD*(referenceRadius dr Ar p L x)^3 := by
  classical
  let data := Classical.choice (exists_reverseEOrdinaryPhysicalCaps g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hL hreg δ0 W δ Cm)
  let KA : ℝ := 1+∑ i : Fin 3, (‖aH i‖+‖aL i‖)
  have hKA : 0 < KA := by
    have hn : 0 ≤ ∑ i : Fin 3, (‖aH i‖+‖aL i‖) :=
      Finset.sum_nonneg (fun i _ => add_nonneg (norm_nonneg (aH i)) (norm_nonneg (aL i)))
    dsimp [KA]
    linarith
  have hAH (i : Fin 3) : ‖aH i‖ ≤ KA := by
    have hi := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin 3 => ‖aH j‖+‖aL j‖)
      (fun j _ => add_nonneg (norm_nonneg (aH j)) (norm_nonneg (aL j))) (Finset.mem_univ i)
    have hnon := norm_nonneg (aL i)
    dsimp [KA]
    linarith
  have hAL (i : Fin 3) : ‖aL i‖ ≤ KA := by
    have hi := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin 3 => ‖aH j‖+‖aL j‖)
      (fun j _ => add_nonneg (norm_nonneg (aH j)) (norm_nonneg (aL j))) (Finset.mem_univ i)
    have hnon := norm_nonneg (aH i)
    dsimp [KA]
    linarith
  refine ⟨data.eta0,data.eta0_pos,data.eta0_le,?_⟩
  intro g2 hg2
  obtain ⟨MQ,hMQ,hQcap⟩ := exists_Q_sum_cap g g2 hg hg2 L y0 ρ
  let A0 : ℝ := MQ*(2*KA*data.M)
  let D0 : ℝ := MQ*data.M^2
  let C_AD : ℝ := 1+A0+D0
  have hA0 : 0 ≤ A0 := mul_nonneg hMQ.le
    (mul_nonneg (mul_nonneg (by norm_num) hKA.le) data.M_nonneg)
  have hD0 : 0 ≤ D0 := mul_nonneg hMQ.le (sq_nonneg data.M)
  have hCAD : 0 < C_AD := by dsimp [C_AD]; linarith
  have hCA : A0 ≤ C_AD := by dsimp [C_AD]; linarith
  have hCD : D0 ≤ C_AD := by dsimp [C_AD]; linarith
  refine ⟨C_AD,hCAD,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs
  have physical := data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs
  have hEH (i : Fin 3) : ‖eH i ((Tq dr Ar p q) x)‖ ≤ data.M := (physical.2 i).1.2.1
  have hEL (j : Fin 3) : ‖eL j ((Tq dr Ar p q) x)‖ ≤ data.M := (physical.2 j).2.2.1
  let S : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j|
  have hS : S ≤ MQ := hQcap q hq x hx
  have hBA : BA g2 q x ((Tq dr Ar p q) x) ≤ A0 := by
    unfold angularBudget
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| *(2*KA*data.M) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hOne := mul_le_mul (hEL j) (hAH i) (norm_nonneg (aH i)) data.M_nonneg
        have hTwo := mul_le_mul (hAL j) (hEH i)
          (norm_nonneg (eH i ((Tq dr Ar p q) x))) hKA.le
        nlinarith only [hOne,hTwo]
      _ = S*(2*KA*data.M) := by dsimp [S]; simp only [Finset.sum_mul]
      _ ≤ MQ*(2*KA*data.M) :=
        mul_le_mul_of_nonneg_right hS
          (mul_nonneg (mul_nonneg (by norm_num) hKA.le) data.M_nonneg)
  have hBD : BD g2 q x ((Tq dr Ar p q) x) ≤ D0 := by
    unfold doubleBudget
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| *data.M^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have ht := mul_le_mul (hEL j) (hEH i)
          (norm_nonneg (eH i ((Tq dr Ar p q) x))) data.M_nonneg
        simpa only [pow_two] using ht
      _ = S*data.M^2 := by dsimp [S]; simp only [Finset.sum_mul]
      _ ≤ MQ*data.M^2 := mul_le_mul_of_nonneg_right hS (sq_nonneg data.M)
  have hr : 0 < referenceRadius dr Ar p L x := referenceRadius_pos dr Ar p L x hdr hAr
  constructor
  · calc
      ‖AN g2 dr Ar p q x‖ ≤ |referenceRadius dr Ar p L x| *BA g2 q x ((Tq dr Ar p q) x) :=
        norm_angularAdjointNegative_le g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
      _ = referenceRadius dr Ar p L x*BA g2 q x ((Tq dr Ar p q) x) := by rw [abs_of_pos hr]
      _ ≤ referenceRadius dr Ar p L x*A0 := mul_le_mul_of_nonneg_left hBA hr.le
      _ ≤ referenceRadius dr Ar p L x*C_AD := mul_le_mul_of_nonneg_left hCA hr.le
      _ = C_AD*referenceRadius dr Ar p L x := mul_comm _ _
  · have hr3 : 0 < (referenceRadius dr Ar p L x)^3 := pow_pos hr _
    calc
      ‖DN g2 dr Ar p q x‖ ≤ |(referenceRadius dr Ar p L x)^3| *BD g2 q x ((Tq dr Ar p q) x) :=
        norm_doubleAdjointNegative_le g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
      _ = (referenceRadius dr Ar p L x)^3*BD g2 q x ((Tq dr Ar p q) x) := by rw [abs_of_pos hr3]
      _ ≤ (referenceRadius dr Ar p L x)^3*D0 := mul_le_mul_of_nonneg_left hBD hr3.le
      _ ≤ (referenceRadius dr Ar p L x)^3*C_AD := mul_le_mul_of_nonneg_left hCD hr3.le
      _ = C_AD*(referenceRadius dr Ar p L x)^3 := mul_comm _ _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointAngularDoubleProfileCaps
