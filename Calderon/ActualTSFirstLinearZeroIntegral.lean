import Calderon.ActualTSFirstLinearZeroPointwise

/-! Original-energy integral estimate for the first-T/linear-zero-S component,
retaining its quadratic companion through the D10 identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstLinearZeroIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTFirstPhysicalDictionary ActualTSLowerZeroZeroBinding ActualTSFirstLinearZeroPointwise
  ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorNativeForm
  ActualHigherSZeroScalarCommutatorForm ActualHigherSZeroScalarNativeForm
  ActualTSPrincipalLowerReferenceOrders PrincipalCommutator
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
private lemma grouped_integral_bound (mu f e : R3 → ℝ) (A : ℝ)
    (hmu : ∀ x, 0 ≤ mu x)
    (hf : Integrable (fun x => mu x*f x))
    (he : Integrable (fun x => mu x*e x))
    (hpoint : ∀ x, |f x| ≤ A*e x) :
    |∫ x, mu x*f x| ≤ A*∫ x, mu x*e x := by
  have hAbs : Integrable (fun x => |mu x*f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  calc
    _ ≤ ∫ x, |mu x*f x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, A*(mu x*e x) := by
      apply integral_mono hAbs (he.const_mul A)
      intro x
      change |mu x*f x| ≤ A*(mu x*e x)
      rw [abs_mul,abs_of_nonneg (hmu x)]
      exact (mul_le_mul_of_nonneg_left (hpoint x) (hmu x)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

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
local notation "TF" => referenceFirstHalf hO hD hF g L
local notation "TD" => referenceAdjointFirstHalf hO hD hF g L
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LD" => firstLinearZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "QD" => firstQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "D10" => originalFirstZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] firstLinearZeroCrossDensity firstQuadraticZeroCrossDensity
  originalFirstZeroCrossDensity finiteCoreReferenceProfileEnergy
  referenceFirstHalf referenceAdjointFirstHalf ActualHigherSFormation.higherSInput

include hg in
private lemma original_first_physical_continuous (q dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD) :
    Continuous (fun x => KL (TF q (UF F) x)) ∧
      Continuous (fun x => KL (TD q (UF F) x)) := by
  have hFwd : (fun x => KL (TF q (UF F) x)) =
      (fun x => (nativeT hO hD hF g hg L q dr Ar p hdr hAr F).val x-
        (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x) := by
    funext x
    have h := nativeT_eq_first_and_original_zero hO hD hF g hg L q dr Ar p hdr hAr F x
    simpa only [ActualHigherSFormation.higherSInput] using eq_sub_of_add_eq h.symm
  have hRev : (fun x => KL (TD q (UF F) x)) =
      (fun x => (nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F).val x-
        (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x) := by
    funext x
    have h := nativeTdag_eq_first_and_original_zero hO hD hF g hg L q dr Ar p hdr hAr F x
    simpa only [ActualHigherSFormation.higherSInput] using eq_sub_of_add_eq h.symm
  constructor
  · rw [hFwd]
    exact (nativeT hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.sub
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous
  · rw [hRev]
    exact (nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.sub
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous

/-- Actual integral and exact original-row split; no quadratic bound is claimed. -/
theorem exists_original_first_linear_zero_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Clinear etaLinear : ℝ, 0 < Clinear ∧ 0 < etaLinear ∧ etaLinear ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaLinear →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*LD g2 dr Ar p q F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*LD g2 dr Ar p q F x| ≤
        Clinear*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x ∧
      (∀ x, D10 g2 dr Ar p hdr hAr q F x=QD g2 dr Ar p q F x+LD g2 dr Ar p q F x) := by
  obtain ⟨Cp,etaPoint,hCp,hePoint,hePoint0,hPoint⟩ :=
    exists_original_first_linear_zero_pointwise_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨CL,etaReg,_hCL,heReg,_heReg0,hRegular⟩ :=
    ActualHigherSLinearZero.exists_linear_zero_high_contract
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  obtain ⟨Cr,hCr,hReference⟩ := exists_highInput_inclusion_reference_integral_bound
    hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨Cp*Cr,min etaPoint etaReg,mul_pos hCp hCr,lt_min hePoint heReg,
    (min_le_left _ _).trans hePoint0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have heP : eta ≤ etaPoint := he.trans (min_le_left _ _)
  have heR : eta ≤ etaReg := he.trans (min_le_right _ _)
  have hP := hPoint q hq dr hdr hdr1 Ar hAr p hp eta heta heP K hK hKball F hsupp hb hs
  have hFields := (hRegular q hq dr hdr hdr1 Ar hAr p hp eta heta heR K hK hKball F hsupp hb hs).2
  have hFirst := original_first_physical_continuous hF hO hD g L hg q dr Ar p hdr hAr F
  have hCont : Continuous (LD g2 dr Ar p q F) := by
    unfold firstLinearZeroCrossDensity
    exact (continuous_const.mul (hFirst.1.inner ((KL).continuous.comp hFields.1.continuous))).sub
      (continuous_const.mul (hFirst.2.inner ((KL).continuous.comp hFields.2.1.continuous)))
  have hOff (x : R3) (hx : x ∉ tsupport F.val) : LD g2 dr Ar p q F x=0 := by
    have hU := highInput_eq_zero_off hO hD F x hx
    unfold firstLinearZeroCrossDensity
    simp only [hU,map_zero,inner_zero_right,mul_zero,sub_self]
  let U := UF F
  let beta := actualReferenceBeta g L q dr Ar p
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let e : R3 → ℝ := fun x => inclusionEnergyDensity IH (beta x) U x
  have hMuCont : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hMu (x : R3) : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
  have hCompact : HasCompactSupport (fun x => mu x*LD g2 dr Ar p q F x) :=
    HasCompactSupport.intro F.property.2.1 (by intro x hx; rw [hOff x hx,mul_zero])
  have hI : Integrable (fun x => mu x*LD g2 dr Ar p q F x) :=
    (hMuCont.mul hCont).integrable_of_hasCompactSupport hCompact
  have hBetaCont : Continuous beta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hBetaPos (x : R3) : 0 < beta x := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  have hUSmooth : ContDiff ℝ ∞ U := by
    dsimp only [U]
    unfold ActualHigherSFormation.higherSInput
    exact contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hUOff (x : R3) (hx : x ∉ tsupport F.val) : U x=0 := highInput_eq_zero_off hO hD F x hx
  have hEI : Integrable (fun x => mu x*e x) :=
    inclusionEnergy_integrable IH mu beta U (tsupport F.val) F.property.2.1
      hMuCont hBetaCont (fun x => (hBetaPos x).ne') hUSmooth hUOff
  have hGlobal (x : R3) : |LD g2 dr Ar p q F x| ≤ Cp*eta*e x := by
    by_cases hx : x ∈ tsupport F.val
    · exact hP.1 x hx
    · rw [hOff x hx,abs_zero]
      exact mul_nonneg (mul_nonneg hCp.le heta)
        (inclusionEnergyDensity_nonneg IH (beta x) U x (hBetaPos x).le)
  have hBound := grouped_integral_bound mu (LD g2 dr Ar p q F) e (Cp*eta)
    hMu hI hEI hGlobal
  have hFclosed : tsupport F.val ⊆ closedBall y0 ρ := hsupp.trans (hKball.trans ball_subset_closedBall)
  have hRef : (∫ x, mu x*e x) ≤ Cr*(∫ x, mu x*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) :=
    hReference q hq dr Ar p hdr hAr hp F hFclosed (fun x hx => hb x (hsupp hx))
  have hScale := mul_le_mul_of_nonneg_left hRef (mul_nonneg hCp.le heta)
  refine ⟨hI,?_,hP.2⟩
  exact hBound.trans (hScale.trans_eq (by ring))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstLinearZeroIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstLinearZeroIntegral.exists_original_first_linear_zero_integral_bound
