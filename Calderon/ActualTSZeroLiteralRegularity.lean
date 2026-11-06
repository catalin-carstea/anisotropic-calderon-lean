import Calderon.ActualTSZeroLiteralPointwise
import Calderon.ActualHigherSQuadraticZeroQuarticRegularity
import Calderon.ActualHigherSLinearZeroCaps
import Calderon.ActualHigherSCommonProfileRoomData

/-!
Genuine global continuity/support/integrability of the original grouped L00.
No ambient smoothness is inferred from a closed-room ContDiffOn statement.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralRegularity
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTSZeroLiteralPointwise ActualSZeroPhysicalWordDictionary
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth
local notation "Half" => SphereSobolev (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
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
local notation "S0" => ActualHigherSZeroPhysicalGraph.nativeZeroHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
local notation "Sd0" => ActualSFirstPhysicalDictionary.nativeAdjointZeroHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
local notation "Z2" => ActualHigherSQuadraticZeroQuartic.actualZ2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "D00" => originalZeroZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] originalZeroZeroCrossDensity
  ActualHigherSZeroPhysicalGraph.nativeZeroHalf ActualSFirstPhysicalDictionary.nativeAdjointZeroHalf
  ActualHigherSFormation.higherSInput ActualHigherSQuadraticZeroQuartic.actualZ2Half
  ActualHigherSQuadraticZeroQuartic.actualT2Half ActualHigherSLinearZero.linearZeroHigh
  ActualHigherSLinearZero.linearAdjointZeroHigh sphereSobolevHalfToSphereL2L
  nativeReferenceZeroCoefficient nativeReferenceAdjointZeroCoefficient

/-- Actual original grouped L00 is continuous, supported, and genuinely integrable. -/
theorem exists_original_zero_zero_regularity
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ etaRegular : ℝ, 0 < etaRegular ∧ etaRegular ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRegular →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Continuous (D00 g2 dr Ar p hdr hAr q F) ∧
      (∀ x ∉ tsupport F.val, D00 g2 dr Ar p hdr hAr q F x=0) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*D00 g2 dr Ar p hdr hAr q F x) := by
  obtain ⟨dF,hdF,_hdF0,_hdFrho,Cm,_hJac,_hAdj⟩ :=
    ActualHigherSAdjointFormation.exists_retained_higherS_adjoint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  let G := Classical.choice (ActualHigherSQuarticFactorization.exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL hKernel dF hdF)
  obtain ⟨CL,etaLinear,_hCL,heLinear,_heLinear0,hLinear⟩ :=
    ActualHigherSLinearZero.exists_linear_zero_high_contract
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  obtain ⟨etaDictionary,heDictionary,heDictionary0,hDictionary⟩ :=
    exists_original_zero_physical_word_dictionary
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  let etaRegular := min etaDictionary (min etaLinear G.epsG)
  refine ⟨etaRegular,lt_min heDictionary (lt_min heLinear G.epsG_pos),
    (min_le_left _ _).trans heDictionary0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have heD : eta ≤ etaDictionary := he.trans (min_le_left _ _)
  have heL : eta ≤ etaLinear := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heG : eta ≤ G.epsG := he.trans ((min_le_right _ _).trans (min_le_right _ _))
  have rooms := G.members q hq dr hdr hdr1 Ar hAr p hp eta heta heG K hK hKball F hsupp hb hs
  have hQuadratic := ActualHigherSQuadraticZeroQuarticBounds.actualZ2T2_contDiff_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm g2 hg2 dr Ar p hdr hAr q F rooms.1
  have hLinFields := (hLinear q hq dr hdr hdr1 Ar hAr p hp eta heta heL K hK hKball F hsupp hb hs).2
  have hZeroDict := hDictionary q hq dr hdr hdr1 Ar hAr p hp eta heta heD K hK hKball F hsupp hb hs
  have hS :
      (fun x => KL (S0 g2 dr Ar p hdr hAr q F x)) =
        (fun x => KL (Z2 g2 dr Ar p q F x)+KL (Z1 g2 dr Ar p q x (UF F x))) :=
    funext (fun x => (hZeroDict x).1)
  have hSd :
      (fun x => KL (Sd0 g2 dr Ar p hdr hAr q F x)) =
        (fun x => KL (T2 g2 dr Ar p q F x)+KL (T1 g2 dr Ar p q x (UF F x))) :=
    funext (fun x => (hZeroDict x).2)
  have hScont : Continuous (fun x => KL (S0 g2 dr Ar p hdr hAr q F x)) :=
    hS.symm ▸ (((KL).continuous.comp hQuadratic.1.continuous).add
      ((KL).continuous.comp hLinFields.1.continuous))
  have hSdcont : Continuous (fun x => KL (Sd0 g2 dr Ar p hdr hAr q F x)) :=
    hSd.symm ▸ (((KL).continuous.comp hQuadratic.2.1.continuous).add
      ((KL).continuous.comp hLinFields.2.1.continuous))
  have hDcont : Continuous (D00 g2 dr Ar p hdr hAr q F) := by
    unfold originalZeroZeroCrossDensity
    exact continuous_const.mul
      (((nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.inner
          hScont).sub
        ((nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.inner
          hSdcont))
  have hOff (x : R3) (hx : x ∉ tsupport F.val) : D00 g2 dr Ar p hdr hAr q F x=0 := by
    have hZ2 : Z2 g2 dr Ar p q F x=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (hQuadratic.2.2.1 h))
    have hT2 : T2 g2 dr Ar p q F x=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (hQuadratic.2.2.2 h))
    have hU : UF F x=0 := ActualHigherSZeroScalarNativeForm.highInput_eq_zero_off hO hD F x hx
    have hSzero : KL (S0 g2 dr Ar p hdr hAr q F x)=0 := by
      simpa only [hZ2,hU,map_zero,add_zero] using (hZeroDict x).1
    have hSdzero : KL (Sd0 g2 dr Ar p hdr hAr q F x)=0 := by
      simpa only [hT2,hU,map_zero,add_zero] using (hZeroDict x).2
    unfold originalZeroZeroCrossDensity
    rw [hSzero,hSdzero,inner_zero_right,inner_zero_right,sub_self,mul_zero]
  have hmu : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hCompact : HasCompactSupport
      (fun x => referenceDensityFamily g L (q,x)*D00 g2 dr Ar p hdr hAr q F x) :=
    HasCompactSupport.intro F.property.2.1 (by
      intro x hx
      rw [hOff x hx,mul_zero])
  exact ⟨hDcont,hOff,(hmu.mul hDcont).integrable_of_hasCompactSupport hCompact⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralRegularity
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralRegularity.exists_original_zero_zero_regularity
