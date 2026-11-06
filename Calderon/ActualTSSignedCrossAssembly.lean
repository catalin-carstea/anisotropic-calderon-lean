import Calderon.ActualTSPrincipalFixedDataIntegral
import Calderon.ActualTSFirstZeroOriginalIntegral
import Calderon.ActualTSZeroLiteralIntegral
import Calderon.ActualZSAdjointFixedDataIntegral
import Calderon.ActualTSFullLowerAssembly

/-! Exact original signed T/S assembly, explicitly conditional on original D01 until third delivery. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossAssembly
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  PrincipalCommutator ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

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



open ActualHigherSFormation ActualHigherSAdjointFormation ActualTSFullLowerAssembly
  ActualTSPrincipalFirstPhysical ActualTSPrincipalFixedDataIntegral
  ActualTSLowerZeroZeroBinding ActualTSFirstZeroOriginalIntegral ActualTSZeroLiteralIntegral
  ActualZSAdjointFixedDataIntegral
local notation "UF" => higherSInput hO hD
local notation "FC" => firstPhysicalCross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "Lower" => lowerPhysicalCross g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs
local notation "D10" => originalFirstZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "D01" => originalZeroFirstCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "D00" => ActualTSZeroLiteralPointwise.originalZeroZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "ZD" => originalSignedZAdjointDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "SO" => nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "SD" => higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The exact original physical signed T/S cross, with its sole Z correction. -/
def originalSignedTSPhysicalDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*(⟪(nativeT hO hD hF g hg L q dr Ar p hdr hAr F).val x,
        SO dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x⟫_ℝ-
      ⟪((nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F)+
          nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
        SD hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x⟫_ℝ)
local notation "TSD" => originalSignedTSPhysicalDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

private lemma scalar_signed_split (a b c z : ℝ) (h : a=b+c-z) :
    4*a=4*b+4*c+(-4)*z := by linarith only [h]

theorem original_signed_TS_physical_eq_rows (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    TSD g2 dr Ar p hdr hAr q F x=
      (4*FC g2 dr Ar p q (UF F) x+4*Lower g2 dr Ar p hdr hAr q F x)+
        ZD g2 dr Ar p hdr hAr q F x := by
  unfold originalSignedTSPhysicalDensity originalSignedZAdjointDensity
  exact scalar_signed_split _ _ _ _
    (native_TS_cross_eq_principal_lower_and_Z g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x)

abbrev OriginalProfileCrossRow := ∀ (q dr Ar : ℝ) (p : ℕ),
  0 < dr → 0 < Ar → smoothCompactFiniteSphereCore hO hD → R3 → ℝ
local notation "Row" => OriginalProfileCrossRow hO hD

/-- Exact common original profile/energy contract, including genuine integrability. -/
def OriginalProfileIntegralBound (f : Row) : Prop :=
  ∃ Cb etaRoom : ℝ, 0 < Cb ∧ 0 < etaRoom ∧ etaRoom ≤ data.eta0 ∧
    ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRoom →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    Integrable (fun x => referenceDensityFamily g L (q,x)*f q dr Ar p hdr hAr F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*f q dr Ar p hdr hAr F x| ≤
        Cb*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x
local notation "PB" => OriginalProfileIntegralBound
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

private lemma profile_integral_bound_add {f₁ f₂ : Row} (h₁ : PB f₁) (h₂ : PB f₂) :
    PB (fun q dr Ar p hdr hAr F x => f₁ q dr Ar p hdr hAr F x+f₂ q dr Ar p hdr hAr F x) := by
  unfold OriginalProfileIntegralBound at h₁ h₂ ⊢
  obtain ⟨C₁,e₁,hC₁,he₁,he₁0,H₁⟩ := h₁
  obtain ⟨C₂,e₂,hC₂,he₂,he₂0,H₂⟩ := h₂
  refine ⟨C₁+C₂,min e₁ e₂,add_pos hC₁ hC₂,lt_min he₁ he₂,
    (min_le_left _ _).trans he₁0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have hA := H₁ q hq dr hdr hdr1 Ar hAr p hp eta heta
    (he.trans (min_le_left _ _)) K hK hKball F hsupp hb hs
  have hB := H₂ q hq dr hdr hdr1 Ar hAr p hp eta heta
    (he.trans (min_le_right _ _)) K hK hKball F hsupp hb hs
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let a : R3 → ℝ := f₁ q dr Ar p hdr hAr F
  let b : R3 → ℝ := f₂ q dr Ar p hdr hAr F
  have hEq : (fun x => mu x*(a x+b x))=(fun x => mu x*a x+mu x*b x) :=
    funext (fun x => mul_add (mu x) (a x) (b x))
  have hI : Integrable (fun x => mu x*(a x+b x)) := hEq.symm ▸ hA.1.add hB.1
  have hInt : (∫ x, mu x*(a x+b x))=(∫ x, mu x*a x)+(∫ x, mu x*b x) :=
    (congrArg (fun f : R3 → ℝ => ∫ x, f x) hEq).trans (integral_add hA.1 hB.1)
  refine ⟨hI,?_⟩
  let J : ℝ := ∫ x, mu x*finiteCoreReferenceProfileEnergy
    hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x
  calc
    _ = |(∫ x, mu x*a x)+(∫ x, mu x*b x)| := congrArg abs hInt
    _ ≤ |∫ x, mu x*a x|+|∫ x, mu x*b x| := abs_add_le _ _
    _ ≤ C₁*eta*J+C₂*eta*J := add_le_add hA.2 hB.2
    _ = _ := by change C₁*eta*J+C₂*eta*J=(C₁+C₂)*eta*J; ring
local notation "BA" => profile_integral_bound_add
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

/-- Exact original lower T/S estimate, pending only the third thread's literal D01. -/
theorem original_lower_TS_integral_bound_of_D01
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (h01 : PB (fun q dr Ar p hdr hAr F x => D01 g2 dr Ar p hdr hAr q F x)) :
    PB (fun q dr Ar p hdr hAr F x => 4*Lower g2 dr Ar p hdr hAr q F x) := by
  let f10 : Row := fun q dr Ar p hdr hAr F x => D10 g2 dr Ar p hdr hAr q F x
  let f01 : Row := fun q dr Ar p hdr hAr F x => D01 g2 dr Ar p hdr hAr q F x
  let f00 : Row := fun q dr Ar p hdr hAr F x => D00 g2 dr Ar p hdr hAr q F x
  have h10 : PB f10 := exists_original_first_zero_integral_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  have h00 : PB f00 := exists_original_zero_zero_integral_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  have hD01 : PB f01 := h01
  have hAll := BA (BA h10 hD01) h00
  have hEq :
      (fun q dr Ar p hdr hAr F x => 4*Lower g2 dr Ar p hdr hAr q F x)=
      (fun q dr Ar p hdr hAr F x => f10 q dr Ar p hdr hAr F x+
        f01 q dr Ar p hdr hAr F x+f00 q dr Ar p hdr hAr F x) := by
    funext q dr Ar p hdr hAr F x
    exact original_lower_cross_eq_three_signed_rows hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      Room hreg data g2 dr Ar p hdr hAr q F x
  exact hEq.symm ▸ hAll

/-- Complete physical signed T/S assembly CONDITIONAL on the exact original D01
integral estimate. No D01 proof or acceptance is asserted by this theorem. -/
theorem original_signed_TS_integral_bound_of_D01
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (h01 : PB (fun q dr Ar p hdr hAr F x => D01 g2 dr Ar p hdr hAr q F x)) :
    PB (fun q dr Ar p hdr hAr F x => TSD g2 dr Ar p hdr hAr q F x) := by
  let fP : Row := fun q dr Ar p _hdr _hAr F x => 4*FC g2 dr Ar p q (UF F) x
  let fL : Row := fun q dr Ar p hdr hAr F x => 4*Lower g2 dr Ar p hdr hAr q F x
  let fZ : Row := fun q dr Ar p hdr hAr F x => ZD g2 dr Ar p hdr hAr q F x
  have hP : PB fP := exists_original_principal_TS_integral_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  have hLower : PB fL := original_lower_TS_integral_bound_of_D01
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2 h01
  have hZ : PB fZ := exists_original_signed_Z_adjoint_integral_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  have hAll := BA (BA hP hLower) hZ
  have hEq :
      (fun q dr Ar p hdr hAr F x => TSD g2 dr Ar p hdr hAr q F x)=
      (fun q dr Ar p hdr hAr F x => fP q dr Ar p hdr hAr F x+
        fL q dr Ar p hdr hAr F x+fZ q dr Ar p hdr hAr F x) := by
    funext q dr Ar p hdr hAr F x
    exact original_signed_TS_physical_eq_rows
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data g2 dr Ar p hdr hAr q F x
  exact hEq.symm ▸ hAll

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossAssembly
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossAssembly.original_signed_TS_physical_eq_rows
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossAssembly.original_signed_TS_integral_bound_of_D01
