import Calderon.ActualTSFirstQuadraticOriginalIntegral
import Calderon.ActualTSFirstLinearZeroIntegral

/-! Complete original first-T/zero-S D10 integral assembly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstZeroOriginalIntegral
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


open ActualTSFirstLinearZeroIntegral ActualTSFirstQuadraticOriginalIntegral

/-- Complete literal original D10, including both its quadratic and linear
zero-S parts, with genuine integrability and original energy. -/
theorem exists_original_first_zero_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cfirst etaFirst : ℝ, 0 < Cfirst ∧ 0 < etaFirst ∧ etaFirst ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaFirst →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*D10 g2 dr Ar p hdr hAr q F x) ∧
        |∫ x, referenceDensityFamily g L (q,x)*D10 g2 dr Ar p hdr hAr q F x| ≤
          Cfirst*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
            hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨Cq,eq,hCq,heq,heq0,hQ⟩ := exists_original_first_quadratic_zero_integral_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨Cl,el,hCl,hel,hel0,hLin⟩ := exists_original_first_linear_zero_integral_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  refine ⟨Cq+Cl,min eq el,add_pos hCq hCl,lt_min heq hel,(min_le_left _ _).trans heq0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have hQuad := hQ q hq dr hdr hdr1 Ar hAr p hp eta heta
    (he.trans (min_le_left _ _)) K hK hKball F hsupp hb hs
  have hLinear := hLin q hq dr hdr hdr1 Ar hAr p hp eta heta
    (he.trans (min_le_right _ _)) K hK hKball F hsupp hb hs
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  have hEq : (fun x => mu x*D10 g2 dr Ar p hdr hAr q F x)=
      (fun x => mu x*QD g2 dr Ar p q F x+mu x*LD g2 dr Ar p q F x) := by
    funext x
    have h := congrArg (fun t : ℝ => mu x*t) (hLinear.2.2 x)
    exact h.trans (mul_add _ _ _)
  have hI : Integrable (fun x => mu x*D10 g2 dr Ar p hdr hAr q F x) :=
    hEq.symm ▸ hQuad.1.add hLinear.1
  have hIntegral :
      (∫ x, mu x*D10 g2 dr Ar p hdr hAr q F x)=
      (∫ x, mu x*QD g2 dr Ar p q F x)+(∫ x, mu x*LD g2 dr Ar p q F x) :=
    (congrArg (fun f : R3 → ℝ => ∫ x, f x) hEq).trans (integral_add hQuad.1 hLinear.1)
  refine ⟨hI,?_⟩
  calc
    _ = |(∫ x, mu x*QD g2 dr Ar p q F x)+(∫ x, mu x*LD g2 dr Ar p q F x)| :=
      congrArg abs hIntegral
    _ ≤ |∫ x, mu x*QD g2 dr Ar p q F x|+|∫ x, mu x*LD g2 dr Ar p q F x| := abs_add_le _ _
    _ ≤ Cq*eta*(∫ x, mu x*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)+
        Cl*eta*(∫ x, mu x*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) :=
      add_le_add hQuad.2 hLinear.2.1
    _ = _ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstZeroOriginalIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstZeroOriginalIntegral.exists_original_first_zero_integral_bound
