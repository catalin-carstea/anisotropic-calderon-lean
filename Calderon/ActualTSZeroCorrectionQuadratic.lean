import Calderon.ActualTSZeroNegativeBudget
import Calderon.ActualTZeroCorrectionUniform
import Calderon.ActualHigherSQuadraticZeroNegativeProfileGraphs
import Calderon.ActualLowerSSelfFormation

/-!
Before-code: ../T-S-L00-weighted-assembly-before-source-nov03-night-v001/.
The original negative-four raw-adjoint correction/quadratic-S term.
No correction is reassigned to Z, no quadratic Hi->Half bound is used,
and the remaining S-linear and literal S-zero dictionaries are still required.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroCorrectionQuadratic
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualTZeroGenuineReverse ActualTZeroCorrectionUniform
  ActualTSZeroNegativeBudget ActualHigherSQuadraticZeroWords ActualHigherSQuadraticZeroNegativeGraphs
  ActualReferenceZeroECommutators ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth AmbientReferenceRaising

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
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d


local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "RHalf" => genuineReferenceZeroReverseHalf hF hO hD g L
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Corr" => referenceZeroAdjointCorrection
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

/-- Exact original finite raw N-1 adjoint-zero Half field, with no changed convention. -/
def rawAdjointZeroHalf (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  finiteCoreSobolevLift hO hD (1/2 : ℝ)
    (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x
local notation "Td0" => rawAdjointZeroHalf hF hO hD g L hg

/-- The original negative-four correction term in the signed T/S zero/zero row. -/
def negativeCorrectionQuadraticDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  (-4 : ℝ)*⟪KL (Td0 q dr Ar p hdr hAr F x-RHalf q dr Ar p F x),
    KL (T2 g2 dr Ar p q F x)⟫_ℝ
local notation "CD" => negativeCorrectionQuadraticDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] rawAdjointZeroHalf negativeCorrectionQuadraticDensity
  referenceZeroAdjointCorrection sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSInput ActualHigherSQuadraticZeroQuartic.actualT2Half
  ActualHigherSQuadraticZeroWords.quadraticZeroNegative
  ActualHigherSQuadraticZeroWords.quadraticZeroReverseNegative

/-- Full original raw correction budget, with constants/room chosen before profiles. -/
theorem exists_original_correction_quadratic_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cerror etaError : ℝ, 0 < Cerror ∧ 0 < etaError ∧ etaError ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaError →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ x ∈ tsupport F.val,
      |CD g2 dr Ar p hdr hAr q F x| ≤ Cerror*eta*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨radius,hradius,_hrD,_hr0,_hrrho,_hInv,⟨P⟩⟩ :=
    ActualAllAngularAtomGainedRoom.exists_same_packet_allAngularAtom_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  obtain ⟨Ccorr,hCcorr,hCorr⟩ := exists_original_correction_uniform_beta_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    hL P (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨Cneg,hCneg,hNeg⟩ := exists_original_quadratic_zero_negative_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL g2 hg2 P
  let G := Classical.choice (ActualHigherSQuarticFactorization.exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL hKernel radius hradius)
  let Derror : ℝ := 4*PN*Ccorr*Cneg
  let Cerror : ℝ := 1+Derror
  let etaError : ℝ := min data.eta0 (min 1 G.epsG)
  have hPN : 0 ≤ PN := ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  have hDerror : 0 ≤ Derror := by dsimp only [Derror]; positivity
  have hCerror : 0 < Cerror := by dsimp only [Cerror]; linarith only [hDerror]
  have hDC : Derror ≤ Cerror := by dsimp only [Cerror]; linarith
  refine ⟨Cerror,etaError,hCerror,lt_min data.eta0_pos (lt_min zero_lt_one G.epsG_pos),
    min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heError K hK hKball F hsupp hb hs x hx
  have he1 : eta ≤ 1 := heError.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heG : eta ≤ G.epsG := heError.trans ((min_le_right _ _).trans (min_le_right _ _))
  have rooms := G.members q hq dr hdr hdr1 Ar hAr p hp eta heta heG K hK hKball F hsupp hb hs
  have ht := rooms.1 x hx
  have hxK := hsupp hx
  have hxClosed := ball_subset_closedBall (hKball hxK)
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let U := UF F x
  have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hbX : 1 ≤ beta := hb x hxK
  have hb0 : 0 ≤ beta := zero_le_one.trans hbX
  have hCorrOp := hCorr q hq dr hdr hdr1 Ar hAr p hp x hxClosed ht hbX
  have hCorrValue : ‖Corr P q dr Ar p x U‖ ≤ Ccorr*beta*‖U‖ :=
    ((Corr P q dr Ar p x).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right hCorrOp (norm_nonneg U))
  have hNormNeg := (hNeg q hq dr hdr hdr1 Ar hAr p hp x hxClosed ht hbX
    ((hs x hxK).trans he1) U).2
  unfold reverseQuadraticNegativeValueNorm at hNormNeg
  dsimp only [U] at hNormNeg
  have hGraph := (actualZ2T2_negative_graphs_at
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P G.commonRadius G.common g2 dr Ar p hdr hAr q F rooms.2 x ht).2
  have hT2Value : ‖JL (T2 g2 dr Ar p q F x)‖ ≤ Cneg*r*‖U‖ :=
    (congrArg (fun v : Neg => ‖v‖) hGraph).le.trans hNormNeg
  have hRaw : Td0 q dr Ar p hdr hAr F x =
      RHalf q dr Ar p F x+Corr P q dr Ar p x U := by
    simpa only [rawAdjointZeroHalf,ActualHigherSFormation.higherSInput,U] using
      native_raw_adjoint_zero_half_eq_genuine_reverse_add_correction
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
        P q dr Ar p hdr hAr F x ht
  have hDiff : Td0 q dr Ar p hdr hAr F x-RHalf q dr Ar p F x=Corr P q dr Ar p x U := by
    rw [hRaw]
    abel
  have hPair :
      ⟪KL (Td0 q dr Ar p hdr hAr F x-RHalf q dr Ar p F x),KL (T2 g2 dr Ar p q F x)⟫_ℝ =
      PL (Corr P q dr Ar p x U) (JL (T2 g2 dr Ar p q F x)) :=
    (ActualHigherSZeroAtomTransport.half_pairing_inner hO hD _ _).symm.trans
      (congrArg (fun v : Half => PL v (JL (T2 g2 dr Ar p q F x))) hDiff)
  have hPairBound :
      |⟪KL (Td0 q dr Ar p hdr hAr F x-RHalf q dr Ar p F x),KL (T2 g2 dr Ar p q F x)⟫_ℝ| ≤
        PN*(Ccorr*beta*‖U‖)*(Cneg*r*‖U‖) := by
    rw [hPair]
    exact (abs_native_pair_le _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hCorrValue hPN) hT2Value
      (norm_nonneg _) (by positivity))
  have hSigned : |CD g2 dr Ar p hdr hAr q F x| ≤ Derror*(r*beta)*‖U‖^2 := by
    unfold negativeCorrectionQuadraticDensity
    rw [abs_mul,show |(-4 : ℝ)|=4 by norm_num]
    exact (mul_le_mul_of_nonneg_left hPairBound (by norm_num)).trans_eq (by dsimp only [Derror]; ring)
  have hSmall : r*beta ≤ eta :=
    (mul_le_mul_of_nonneg_left (by nlinarith only [hbX] : beta ≤ beta^2) hr).trans (hs x hxK)
  have hEnergy := ActualLowerSSelfFormation.norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta hbX F x
  calc
    _ ≤ Derror*(r*beta)*‖U‖^2 := hSigned
    _ ≤ Derror*eta*‖U‖^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSmall hDerror) (sq_nonneg _)
    _ ≤ Cerror*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x :=
      mul_le_mul (mul_le_mul_of_nonneg_right hDC heta) hEnergy (sq_nonneg _)
        (mul_nonneg hCerror.le heta)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroCorrectionQuadratic
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroCorrectionQuadratic.exists_original_correction_quadratic_bound
