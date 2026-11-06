import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualHigherSAdjointFormation
import Calderon.FixedParameterProfilePullback
import Calderon.FiniteCoreH1BesselNorm

/-! Author source after archived upfront expansion. UNCHECKED in this artifact.
Same data.delta0/data.germs; one profile-independent smaller threshold.
No finite angular output premise and no cap/adjunction callback.
This proves only formation and the exact original-energy domination prerequisite,
not the assigned first/zero/quartic remainder or Transfer's leading identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSSelfFormation
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  FixedParameterProfilePullback ActualScalarPrincipalAdjoint SpectralWeightedGraph
  SectionFiveErrorForms ConformalDepth
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

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

local notation "SF" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "TF" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max =>
  ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" d:max =>
  Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- A smaller threshold derives both genuine full physical formations from the
original beta/radius hypotheses, on exactly one retained endpoint packet. -/
theorem exists_uniform_same_packet_higherS_formation (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) :
    ∃ etaFormation : ℝ, 0 < etaFormation ∧ etaFormation ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaFormation →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x *
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ActualHigherSFormation.HigherSOutputConclusions
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F ∧
      ContDiff ℝ ∞ (TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F) ∧
      HasCompactSupport (TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ‖SF dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x‖^2) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ‖TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x‖^2) := by
  obtain ⟨dA, hdA, hdA0, hdAρ, Cm, hJac, hAdj⟩ :=
    ActualHigherSAdjointFormation.exists_retained_higherS_adjoint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨epsG, hepsG, hepsG1, hGuard⟩ :=
    exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ dA hdA
      (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨min data.eta0 epsG, lt_min data.eta0_pos hepsG, min_le_left _ _, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaForm K hK hKball F hsupp hb hs
  have hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dA := by
    intro x hx
    have hxK : x ∈ K := hsupp hx
    have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta
      (hetaForm.trans (min_le_right _ _)) x
      (ball_subset_closedBall (hKball hxK)) (hKball hxK) (hb x hxK) (hs x hxK)
    exact (higherSParam_eventually_mem y0 ρ dA L dr Ar q p hdr hAr x hguard).self_of_nhds
  obtain ⟨hout, hAH, hAO, hsAH, hcAH, hcAO, hadj⟩ :=
    hAdj g2 hg2 dr Ar p hdr hAr q hq F hT
  have hmu : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hreverse := integrable_weighted_norm_sq_of_continuous_compact
    (fun x : R3 => referenceDensityFamily g L (q,x)) hmu
    (TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F) hAO.continuous hcAO
  exact ⟨hout, hAO, hcAO, hout.2.2.2.2.2.2.2, hreverse⟩

/-- The original energy already contains beta times the exact three-half input
norm; this is the checked finite-core Bessel norm identity, with no size factor. -/
lemma beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy (q beta : ℝ)
    (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta * ‖ActualHigherSFormation.higherSInput hO hD F x‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  change beta * ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 ≤ _
  rw [norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x]
  have hHorizontal : 0 ≤ ∑ i : Fin 3,
      ‖(coreReferenceHorizontal hO hD g hg L q i F).val x‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hOne : 0 ≤ beta^2 *
      ‖(coreWeightOperator hO hD (besselWeight 1) F).val x‖^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHalf : 0 ≤ beta⁻¹ * (∑ i : Fin 3,
      ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreReferenceHorizontal hO hD g hg L q i F)).val x‖^2) :=
    mul_nonneg (inv_nonneg.mpr hb) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  unfold finiteCoreReferenceProfileEnergy sourceNormSquareIntegrand
  linarith only [hHorizontal, hOne, hHalf]

/-- Under the original beta lower bound, the exact Hi norm is dominated by the
original profile energy; no inverse Sobolev inclusion or angular-size cap. -/
lemma norm_higherSInput_sq_le_referenceProfileEnergy (q beta : ℝ)
    (hb : 1 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖ActualHigherSFormation.higherSInput hO hD F x‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  have hnorm : 0 ≤ ‖ActualHigherSFormation.higherSInput hO hD F x‖^2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hb hnorm
  have henergy := beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta (zero_le_one.trans hb) F x
  simpa only [one_mul] using hmul.trans henergy

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSSelfFormation
