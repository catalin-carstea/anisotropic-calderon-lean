import Calderon.ActualSSelfErrorInterface
import Calderon.ActualTZSRawIntegralAdapter
import Calderon.ActualLowerUSOriginalEnergyBound
import Calderon.ActualFiniteCoverCoercivityScalar

/-! Forward-independent packet signed base. Exact original same-data signs, factors and energy. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPacketSignedBase
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ConformalDepth ReferenceWeightedApproximation ReferenceDensityBounds NormalizedPrincipalMetric
  ActualModelSMixedComparison

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
  (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)

local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "ED" => ActualLowerSSelfRemainder.originalEnergyDensity g L hg hO hD
local notation "RS" => ActualLowerSSelfRemainder.originalLowerSSelfRemainder
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "Lo" => nativeULowerSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
local notation "Rem" => actualModelSUnestimatedDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
local notation "MR" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeModelRaising
  hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "MD" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeModelAdjoint
  hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "ZZ" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeZ hO hD hF g hg L q dr Ar p hdr hAr
local notation "TT" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeT hO hD hF g hg L q dr Ar p hdr hAr
local notation "TD" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeTdag hO hD hF g hg L q dr Ar p hdr hAr
local notation "SO" dr:max Ar:max p:max hdr:max hAr:max q:max => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" dr:max Ar:max p:max hdr:max hAr:max q:max => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs g2 dr Ar p hdr hAr q

/-- Internally select the exact original signed packet budgets before profiles.
The later local input is the cofinal signed model gap. No physical graph or
adjunction is used to turn this into the positive model/higher-S base bound. -/
theorem exists_uniform_same_packet_model_higherS_base_norm_lower
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) (cRaise : ℝ)
    (hcRaise : 0 < cRaise) :
    ∃ etaBase : ℝ, 0 < etaBase ∧ etaBase ≤ data.eta0 ∧ etaBase ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaBase →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : FC, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta * referenceRadius dr Ar p L x) →
      let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
      let E : ℝ := ∫ x, ED dr Ar p q F x
      let cross : R3 → ℝ := fun x =>
        ⟪((TT dr Ar p hdr hAr q) F).val x,(SO dr Ar p hdr hAr q) F x⟫_ℝ -
        ⟪(((TD dr Ar p hdr hAr q) F)+((ZZ dr Ar p hdr hAr q) F)).val x,
          (SD dr Ar p hdr hAr q) F x⟫_ℝ
      cRaise*E ≤
        (∫ x, mu x*‖((MR dr Ar p hdr hAr q) F).val x‖^2) -
        (∫ x, mu x*‖(((MD dr Ar p hdr hAr q) F)+(2:ℝ) • ((ZZ dr Ar p hdr hAr q) F)).val x‖^2) →
      (cRaise/2)*E ≤ (∫ x, mu x*‖((MR dr Ar p hdr hAr q) F).val x+(SO dr Ar p hdr hAr q) F x‖^2) ∧
      Integrable (fun x => mu x*cross x) ∧
      Integrable (fun x => mu x*Lo dr Ar p hdr hAr q F x) ∧
      Integrable (fun x => mu x*(2*Lo dr Ar p hdr hAr q F x)) ∧
      Integrable (ED dr Ar p q F) := by
  obtain ⟨CS,CE,etaI,dMix,dQ,hdMix,hdQ,Pmix,PQ,hCS,hCE,hEtaI,hEtaI0,hEtaI1,HSelf⟩ :=
    ActualSSelfErrorInterface.exists_uniform_model_S_s_self_error_interface
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CTZS,etaT,hCTZS,hEtaT,_hEtaT0,HTZS⟩ :=
    ActualTZSRawIntegralAdapter.exists_original_signed_TZS_raw_integral_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  have hUSFor := ActualLowerUSEnergyBound.exists_actual_lower_US_original_energy_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  unfold ActualLowerUSEnergyBound.FixedMetricLowerUSOriginalEnergyBound at hUSFor
  obtain ⟨CUS,hCUS,etaU,hEtaU,_hEtaU0,_hEtaU1,HUS⟩ := hUSFor
  let CRem : ℝ := CS+CTZS+CUS
  have hCRem : 0 ≤ CRem := (add_pos (add_pos hCS hCTZS) hCUS).le
  let etaA : ℝ := cRaise/(2*(CE+CRem+1))
  have HAbs : 0 < etaA ∧ ∀ t : ℝ, 0 ≤ t → t ≤ etaA → (CE+CRem)*t ≤ cRaise/2 :=
    OAI.AnisotropicCalderon.MixedKernelConstructionTask.MainPhysicalCoercivityAssembly.remainder_absorption_budget
      CE CRem cRaise hCE.le hCRem hcRaise
  let etaBase : ℝ := min etaI (min etaT (min etaU etaA))
  have hBaseI : etaBase ≤ etaI := min_le_left _ _
  have hBaseT : etaBase ≤ etaT := (min_le_right _ _).trans (min_le_left _ _)
  have hBaseU : etaBase ≤ etaU :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hBaseA : etaBase ≤ etaA :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨etaBase,lt_min hEtaI (lt_min hEtaT (lt_min hEtaU HAbs.1)),
    hBaseI.trans hEtaI0,hBaseI.trans hEtaI1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaBase K hK hKball F hSupp hBeta hScale hH8
  dsimp only
  intro hModel
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let E : ℝ := ∫ x, ED dr Ar p q F x
  let cross : R3 → ℝ := fun x =>
    ⟪((TT dr Ar p hdr hAr q) F).val x,(SO dr Ar p hdr hAr q) F x⟫_ℝ -
    ⟪(((TD dr Ar p hdr hAr q) F)+((ZZ dr Ar p hdr hAr q) F)).val x,
      (SD dr Ar p hdr hAr q) F x⟫_ℝ
  let TZS : ℝ := 4*(∫ x, mu x*cross x)
  let ULS : ℝ := 2*(∫ x, mu x*Lo dr Ar p hdr hAr q F x)
  let SSelf : ℝ := RS dr Ar p hdr hAr q F
  let Err : ℝ := ∫ x, mu x*Rem dr Ar p hdr hAr q F x
  have hSelf := HSelf q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaBase.trans hBaseI)
    K hK hKball F hSupp hBeta hScale hH8
  have hIdentity : Err = SSelf+TZS+ULS := hSelf.2.2.2
  have hPrimary := hSelf.1.1
  rcases hPrimary with ⟨_h01,_h02,_h03,_h04,_h05,_h06,_h07,_h08,_h09,_h10,_h11,
    _h12,_h13,_h14,_h15,_h16,_h17,_h18,_h19,_h20,_h21,_h22,_h23,_h24,_h25,_h26,hSS0⟩
  have hSS : |SSelf| ≤ CS*eta*E := hSS0
  obtain ⟨hCrossInt,hTZS0⟩ := HTZS q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaBase.trans hBaseT)
    K hK hKball F hSupp hBeta hScale hH8
  have hTZS : |TZS| ≤ CTZS*eta*E := hTZS0
  have hUS := HUS q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaBase.trans hBaseU)
    K hK hKball F hSupp hBeta hScale hH8
  unfold ActualLowerUSEnergyBound.LowerUSOriginalEnergyConclusion at hUS
  obtain ⟨hLoInt,hLoTwiceInt,hEInt,hUS0⟩ := hUS
  have hTwo : (fun x => mu x*(2*Lo dr Ar p hdr hAr q F x)) =
      (fun x => (2:ℝ)*(mu x*Lo dr Ar p hdr hAr q F x)) := by
    funext x
    ring
  have hULS : |ULS| ≤ CUS*eta*E := by
    change |∫ x, mu x*(2*Lo dr Ar p hdr hAr q F x)| ≤ CUS*eta*E at hUS0
    rw [hTwo,integral_const_mul] at hUS0
    exact hUS0
  have hRem : |Err| ≤ CRem*eta*E := by
    rw [hIdentity]
    calc
      _ ≤ |SSelf|+|TZS|+|ULS| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ CS*eta*E+CTZS*eta*E+CUS*eta*E := add_le_add (add_le_add hSS hTZS) hULS
      _ = _ := by dsimp only [CRem]; ring
  have hAbs := actual_model_S_positive_signed_absorption
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q hL hp CE CRem cRaise eta hcRaise F hSelf.2.1 hRem hModel
    (HAbs.2 eta heta (hetaBase.trans hBaseA))
  exact ⟨hAbs.2.2,hCrossInt,hLoInt,hLoTwiceInt,hEInt⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPacketSignedBase
