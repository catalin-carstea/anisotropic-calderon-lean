import Calderon.ActualTSZeroCorrectionQuadratic
import Calderon.ActualTZeroNegativeProfileCap
import Calderon.ActualHigherSLinearZeroCaps

/-!
Before-code: ../T-S-L00-weighted-assembly-before-source-nov03-night-v001/.
The two original S-linear remainders in the retained signed T/S zero/zero row.
Both raw original T maps, including the original adjoint N-1, are retained.
No bounded quadratic Hi->Half map or finite angular S-output is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLinearRemainder
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTSZeroCorrectionQuadratic ActualTZeroNegativeGraph ActualTZeroNegativeProfileCap
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
local notation "PN" => ActualHigherSPairingNormDiagnostic.standardPairingNorm PL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highNormed highSpace

private lemma abs_native_pair_le (v : Half) (z : Neg) :
    |PL v z| ≤ PN*‖v‖*‖z‖ := by
  rw [ActualHigherSPairingNormDiagnostic.native_pairing_norm_eq_generic]
  simpa only [ActualHigherSPairingNormDiagnostic.genericBilinearNorm,Real.norm_eq_abs] using
    ContinuousLinearMap.le_opNorm₂ PL v z

private lemma original_pair_bound (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Half) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ‖JL a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    |⟪sphereSobolevHalfToSphereL2L hO hD a,
       sphereSobolevHalfToSphereL2L hO hD b⟫_ℝ| ≤ PN*B*A := by
  have heq :
      ⟪sphereSobolevHalfToSphereL2L hO hD a,
        sphereSobolevHalfToSphereL2L hO hD b⟫_ℝ = PL b (JL a) :=
    (real_inner_comm _ _).trans
      (ActualHigherSZeroAtomTransport.half_pairing_inner hO hD b a).symm
  rw [heq]
  exact (abs_native_pair_le b (JL a)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hb
      ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg) ha
      (norm_nonneg _) (mul_nonneg
        ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg hB))

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "Td0" => rawAdjointZeroHalf hF hO hD g L hg
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The exact original forward finite T-zero Half value. -/
def rawForwardZeroHalf (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  finiteCoreSobolevLift hO hD (1/2 : ℝ)
    (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x
local notation "T0" => rawForwardZeroHalf hF hO hD g L hg

/-- Literal positive-four forward and negative-four raw-adjoint S-linear terms. -/
def signedLinearZeroCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  (4 : ℝ)*⟪KL (T0 q dr Ar p hdr hAr F x),KL (Z1 g2 dr Ar p q x (UF F x))⟫_ℝ
    -(4 : ℝ)*⟪KL (Td0 q dr Ar p hdr hAr F x),KL (T1 g2 dr Ar p q x (UF F x))⟫_ℝ
local notation "LD" => signedLinearZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] rawForwardZeroHalf rawAdjointZeroHalf signedLinearZeroCrossDensity
  sphereSobolevInclusionL sphereSobolevHalfToSphereL2L ActualHigherSFormation.higherSInput
  ActualHigherSLinearZero.linearZeroHigh ActualHigherSLinearZero.linearAdjointZeroHigh
  referenceZeroNegative referenceAdjointZeroNegative finiteCoreSobolevLift
  nativeReferenceZeroCoefficient nativeReferenceAdjointZeroCoefficient

/-- Both original linear remainders, uniformly in all later profiles and finite inputs. -/
theorem exists_original_signed_linear_zero_bound
    (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Clinear etaLinear : ℝ, 0 < Clinear ∧ 0 < etaLinear ∧ etaLinear ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaLinear →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ x ∈ tsupport F.val,
      |LD g2 dr Ar p hdr hAr q F x| ≤ Clinear*eta*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨CT,hCT,hT⟩ := exists_reference_zero_negative_uniform_beta_bound
    hF hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨CL,hCL,hLinear⟩ := ActualHigherSLinearZero.exists_linear_zero_high_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  let Dlinear : ℝ := 8*PN*CL*CT
  let Clinear : ℝ := 1+Dlinear
  let etaLinear : ℝ := min data.eta0 1
  have hPN : 0 ≤ PN := ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  have hDlinear : 0 ≤ Dlinear := by dsimp only [Dlinear]; positivity
  have hClinear : 0 < Clinear := by dsimp only [Clinear]; linarith only [hDlinear]
  have hDC : Dlinear ≤ Clinear := by dsimp only [Clinear]; linarith
  refine ⟨Clinear,etaLinear,hClinear,lt_min data.eta0_pos zero_lt_one,min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heLinear K hK hKball F hsupp hb hs x hx
  have he0 : eta ≤ data.eta0 := heLinear.trans (min_le_left _ _)
  have he1 : eta ≤ 1 := heLinear.trans (min_le_right _ _)
  have hxK := hsupp hx
  have hxBall := hKball hxK
  have hxClosed := ball_subset_closedBall hxBall
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let U := UF F x
  have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hbX : 1 ≤ beta := hb x hxK
  have hb0 : 0 ≤ beta := zero_le_one.trans hbX
  have hLin := hLinear q hq dr hdr hdr1 Ar hAr p hp eta heta he0 x hxClosed hxBall hbX (hs x hxK)
  have hZ : ‖Z1 g2 dr Ar p q x U‖ ≤ CL*r^2*beta*‖U‖ :=
    ((Z1 g2 dr Ar p q x).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right hLin.1 (norm_nonneg U))
  have hT1 : ‖T1 g2 dr Ar p q x U‖ ≤ CL*r^2*beta*‖U‖ :=
    ((T1 g2 dr Ar p q x).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right hLin.2 (norm_nonneg U))
  have hRaw := hT q hq dr hdr hdr1 Ar hAr p hp x hxClosed hbX U
  dsimp only [U] at hRaw
  unfold ActualHigherSFormation.higherSInput at hRaw
  have hGraph := native_zero_negative_graph hO hD hF g hg L q dr Ar p hdr hAr F x
  have hAdjGraph := native_adjoint_zero_negative_graph hO hD hF g hg L q dr Ar p hdr hAr F x
  have hT0 : ‖JL (T0 q dr Ar p hdr hAr F x)‖ ≤ CT*beta*‖U‖ := by
    simpa only [rawForwardZeroHalf,ActualHigherSFormation.higherSInput,U] using
      (congrArg (fun v : Neg => ‖v‖) hGraph).le.trans hRaw.1
  have hTd0 : ‖JL (Td0 q dr Ar p hdr hAr F x)‖ ≤ CT*beta*‖U‖ := by
    simpa only [rawAdjointZeroHalf,ActualHigherSFormation.higherSInput,U] using
      (congrArg (fun v : Neg => ‖v‖) hAdjGraph).le.trans hRaw.2
  have hForward := original_pair_bound hO hD
    (T0 q dr Ar p hdr hAr F x) (Z1 g2 dr Ar p q x U)
    (CT*beta*‖U‖) (CL*r^2*beta*‖U‖) (by positivity) (by positivity) hT0 hZ
  have hReverse := original_pair_bound hO hD
    (Td0 q dr Ar p hdr hAr F x) (T1 g2 dr Ar p q x U)
    (CT*beta*‖U‖) (CL*r^2*beta*‖U‖) (by positivity) (by positivity) hTd0 hT1
  have hSigned : |LD g2 dr Ar p hdr hAr q F x| ≤ Dlinear*(r^2*beta^2)*‖U‖^2 := by
    unfold signedLinearZeroCrossDensity
    exact (abs_sub _ _).trans ((add_le_add
      (by simpa only [abs_mul,show |(4 : ℝ)|=4 by norm_num] using
        mul_le_mul_of_nonneg_left hForward (by norm_num : (0:ℝ)≤4))
      (by simpa only [abs_mul,show |(4 : ℝ)|=4 by norm_num] using
        mul_le_mul_of_nonneg_left hReverse (by norm_num : (0:ℝ)≤4))).trans_eq
          (by dsimp only [Dlinear]; ring))
  have hRsmall : r*beta^2 ≤ eta := hs x hxK
  have hr1 : r ≤ 1 := by
    calc
      r = r*1 := (mul_one r).symm
      _ ≤ r*beta^2 := mul_le_mul_of_nonneg_left
        (by nlinarith only [hbX] : (1:ℝ)≤beta^2) hr
      _ ≤ eta := hRsmall
      _ ≤ 1 := he1
  have hSmall : r^2*beta^2 ≤ eta := by
    calc
      _ = r*(r*beta^2) := by ring
      _ ≤ 1*eta := mul_le_mul hr1 hRsmall (mul_nonneg hr (sq_nonneg _)) (by norm_num)
      _ = eta := one_mul _
  have hEnergy := ActualLowerSSelfFormation.norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta hbX F x
  calc
    _ ≤ Dlinear*(r^2*beta^2)*‖U‖^2 := hSigned
    _ ≤ Dlinear*eta*‖U‖^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSmall hDlinear) (sq_nonneg _)
    _ ≤ Clinear*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x :=
      mul_le_mul (mul_le_mul_of_nonneg_right hDC heta) hEnergy (sq_nonneg _)
        (mul_nonneg hClinear.le heta)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLinearRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLinearRemainder.exists_original_signed_linear_zero_bound
