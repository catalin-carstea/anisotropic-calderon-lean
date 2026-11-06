import Calderon.ActualTSZeroFirstLiteralWords
import Calderon.ActualTSPrincipalGreen

/-! Genuine original D01 integrability, using the actual first S fields and
the original compact input support. Before code: ../UPFRONT.md and
../integral-UPFRONT.md. No room membership is required outside the support.
Root authored the factory; d01_scalar repaired terminal-map reduction boundaries.
Repair expansion: ../regularity-repair-UPFRONT.md; exact model/effort unexposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstRegularity
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualSFirstPhysicalDictionary ActualHigherSFormation
  ActualTSZeroFirstLiteralWords ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingBracketGain ActualHigherSZeroScalarNativeForm
  ActualTSPrincipalGreen ActualTSPrincipalPhysicalGreen PrincipalCommutator
  ActualScalarPrincipalAdjoint ActualHigherSAdjointLeadingCoordinate
  ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorCoefficients
  FixedParameterProfilePullback FixedParameterProfileBudgets
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
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
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "Tq" => higherSParam L
local notation "UF" => higherSInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "S1" => referenceSFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sd1" => referenceSAdjointFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "D01" => ActualTSLowerZeroZeroBinding.originalZeroFirstCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] canonicalHigh orderedReverseHigh
  nativeReferenceZeroCoefficient nativeReferenceAdjointZeroCoefficient sphereSobolevHalfToSphereL2L

/-- Same-room actual local smoothness is pulled back through the strict guard,
then compact input support produces the full original integrable density. -/
theorem exists_original_zero_first_regularity
    (hL : 0 < L) {d : ℝ} (hd : 0 < d) (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ etaReg : ℝ, 0 < etaReg ∧ etaReg ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaReg →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ContDiff ℝ ∞ (S1 g2 dr Ar p q (UF F)) ∧
      ContDiff ℝ ∞ (Sd1 g2 dr Ar p q (UF F)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*D01 g2 dr Ar p hdr hAr q F x) := by
  obtain ⟨etaReg,heReg,heReg1,hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ d hd (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨etaReg,heReg,heReg1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hSupp hb hs
  let u := UF F
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hu0 (x : R3) (hx : x ∉ K) : u x=0 :=
    highInput_eq_zero_off hO hD F x (fun hy => hx (hSupp hy))
  have hv (k : Fin 3) : ContDiff ℝ ∞ (directionalFDeriv (coordinateDirection k) u) :=
    contDiff_directionalFDeriv (coordinateDirection k) u hu
  have hv0 (k : Fin 3) (x : R3) (hx : x ∉ K) :
      directionalFDeriv (coordinateDirection k) u x=0 :=
    directional_eq_zero_off u K hK.isClosed hu0 (coordinateDirection k) x hx
  have hAtoms (x : R3) (hx : x ∈ K) (j : Fin 3) :
      ContDiffAt ℝ ∞ (fun y => AH ((Tq dr Ar p q) y) (Sum.inl j)) x ∧
      ContDiffAt ℝ ∞ (fun y => RH ((Tq dr Ar p q) y) (Sum.inl j)) x := by
    have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta he x
      (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx)
    exact ⟨(higherSParam_pullback (fun t => AH t (Sum.inl j)) y0 ρ d L dr Ar q p
      hdr hAr x (P.atomSmooth (Sum.inl j)).1 hguard).1,
      (higherSParam_pullback (fun t => RH t (Sum.inl j)) y0 ρ d L dr Ar q p
        hdr hAr x (P.atomSmooth (Sum.inl j)).2.2.1 hguard).1⟩
  have hApply (k j : Fin 3) :
      ContDiff ℝ ∞ (fun x => AH ((Tq dr Ar p q) x) (Sum.inl j)
        (directionalFDeriv (coordinateDirection k) u x)) ∧
      ContDiff ℝ ∞ (fun x => RH ((Tq dr Ar p q) x) (Sum.inl j)
        (directionalFDeriv (coordinateDirection k) u x)) :=
    ⟨contDiff_supported_operator_apply _ _ K hK.isClosed (hv k) (hv0 k)
      (fun x hx => (hAtoms x hx j).1),
      contDiff_supported_operator_apply _ _ K hK.isClosed (hv k) (hv0 k)
        (fun x hx => (hAtoms x hx j).2)⟩
  have hScalar (k j : Fin 3) : ContDiff ℝ ∞ (fun x =>
      firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x)) := by
    rw [physical_firstCoordinateWeight_eq_base]
    exact (contDiff_coordinateWeightBase g g2 hg hg2 L k j).comp
      (contDiff_const.prodMk contDiff_id)
  have hr : ContDiff ℝ ∞ (referenceRadius dr Ar p L) :=
    contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hForward : ContDiff ℝ ∞ (S1 g2 dr Ar p q u) := by
    have hSmooth := (hr.pow 2).smul (ContDiff.sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) =>
      ContDiff.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
        (hScalar k j).smul (hApply k j).1)))
    have hEq : S1 g2 dr Ar p q u = (fun x => (referenceRadius dr Ar p L x)^2 •
        ∑ k : Fin 3, ∑ j : Fin 3, firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x) •
          AH ((Tq dr Ar p q) x) (Sum.inl j) (directionalFDeriv (coordinateDirection k) u x)) := rfl
    exact hEq.symm ▸ hSmooth
  have hReverse : ContDiff ℝ ∞ (Sd1 g2 dr Ar p q u) := by
    have hSmooth := ((hr.pow 2).smul (ContDiff.sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) =>
      ContDiff.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
        (hScalar k j).smul (hApply k j).2)))).neg
    have hEq : Sd1 g2 dr Ar p q u = (fun x => -((referenceRadius dr Ar p L x)^2 •
        ∑ k : Fin 3, ∑ j : Fin 3, firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x) •
          RH ((Tq dr Ar p q) x) (Sum.inl j) (directionalFDeriv (coordinateDirection k) u x))) := rfl
    exact hEq.symm ▸ hSmooth
  have hDCont : Continuous (D01 g2 dr Ar p hdr hAr q F) := by
    unfold ActualTSLowerZeroZeroBinding.originalZeroFirstCrossDensity
    exact continuous_const.mul
      (((nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.inner
          ((KL).continuous.comp hForward.continuous)).sub
        ((nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).property.1.continuous.inner
          ((KL).continuous.comp hReverse.continuous)))
  have hMu : Continuous (fun x => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  have hCompact : HasCompactSupport (fun x => referenceDensityFamily g L (q,x)*D01 g2 dr Ar p hdr hAr q F x) :=
    HasCompactSupport.intro F.property.2.1 (by
      intro x hx
      rw [original_zero_first_eq_zero_off_tsupport hF hO hD g L y0 Φ B ε C ρ H a w hData
        hg hcalc τ0 g2 dr Ar p hdr hAr q F x hx,mul_zero])
  exact ⟨hForward,hReverse,(hMu.mul hDCont).integrable_of_hasCompactSupport hCompact⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstRegularity
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstRegularity.exists_original_zero_first_regularity
