import Calderon.ActualTSZeroLiteralRegularity
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral
import Calderon.ReferenceWeightedApproximation

/-!
Genuine integral estimate for the exact original signed T/S zero/zero row.
Before-code: ../T-S-zero-literal-integral-before-source-nov03-night-v001/.
Both grouped integrands are genuinely integrable; no termwise integral split.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTSZeroLiteralPointwise ActualTSZeroLiteralRegularity
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

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
local notation "D00" => originalZeroZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
attribute [local irreducible] originalZeroZeroCrossDensity finiteCoreReferenceProfileEnergy

/-- Original signed factor-four L00, with internally closed integrability and original energy. -/
theorem exists_original_zero_zero_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Czero etaZero : ℝ, 0 < Czero ∧ 0 < etaZero ∧ etaZero ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaZero →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*D00 g2 dr Ar p hdr hAr q F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*D00 g2 dr Ar p hdr hAr q F x| ≤
        Czero*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨Czero,etaPoint,hCzero,hePoint,hePoint0,hPoint⟩ := exists_original_zero_zero_pointwise_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨etaRegular,heRegular,_heRegular0,hRegular⟩ := exists_original_zero_zero_regularity
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  refine ⟨Czero,min etaPoint etaRegular,hCzero,lt_min hePoint heRegular,
    (min_le_left _ _).trans hePoint0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have heP : eta ≤ etaPoint := he.trans (min_le_left _ _)
  have heR : eta ≤ etaRegular := he.trans (min_le_right _ _)
  have hReg := hRegular q hq dr hdr hdr1 Ar hAr p hp eta heta heR K hK hKball F hsupp hb hs
  have hP := hPoint q hq dr hdr hdr1 Ar hAr p hp eta heta heP K hK hKball F hsupp hb hs
  have hBeta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hBetaPos (x : R3) : 0 < actualReferenceBeta g L q dr Ar p x :=
    actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  have hEnergy : Integrable (fun x => referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) :=
    integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p) hBeta hBetaPos F
  have hGlobal (x : R3) :
      |D00 g2 dr Ar p hdr hAr q F x| ≤ Czero*eta*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
    by_cases hx : x ∈ tsupport F.val
    · exact hP x hx
    · rw [hReg.2.1 x hx,abs_zero]
      exact mul_nonneg (mul_nonneg hCzero.le heta)
        (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q
          (actualReferenceBeta g L q dr Ar p x) (hBetaPos x).le F x)
  exact ⟨hReg.2.2,grouped_integral_bound (fun x => referenceDensityFamily g L (q,x))
    (D00 g2 dr Ar p hdr hAr q F)
    (fun x => finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)
    (Czero*eta) (fun x => (referenceDensityFamily_pos g hg L (q,x)).le)
    hReg.2.2 hEnergy hGlobal⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralIntegral.exists_original_zero_zero_integral_bound
