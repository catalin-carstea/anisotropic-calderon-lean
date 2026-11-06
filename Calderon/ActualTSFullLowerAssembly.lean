import Calderon.ActualTSPrincipalFirstPhysical
import Calderon.ActualZSAdjointPhysicalPairing
import Calderon.ActualModelSErrorDecomposition

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFullLowerAssembly
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualHigherSFormation ActualHigherSAdjointFormation ActualHigherSLeadingBracketGain
  ActualTFirstPhysicalDictionary ActualSFirstPhysicalDictionary ActualTSPrincipalFirstPhysical
  ActualModelSMixedComparison ActualHigherSZeroPhysicalGraph ReferenceDensityBounds ConformalDepth

private lemma split_cross {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t1 t0 td1 td0 s1 s0 sd1 sd0 z : E) :
    ⟪t1+t0,s1+s0⟫_ℝ-⟪td1+td0+z,sd1+sd0⟫_ℝ =
      (⟪t1,s1⟫_ℝ-⟪td1,sd1⟫_ℝ)+
      ((⟪t1,s0⟫_ℝ-⟪td1,sd0⟫_ℝ)+
        (⟪t0,s1⟫_ℝ-⟪td0,sd1⟫_ℝ)+
        (⟪t0,s0⟫_ℝ-⟪td0,sd0⟫_ℝ))-⟪z,sd1+sd0⟫_ℝ := by
  simp only [inner_add_left,inner_add_right]
  ring

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => higherSInput hO hD
local notation "T1" => referenceFirstHalf hO hD hF g L
local notation "Td1" => referenceAdjointFirstHalf hO hD hF g L
local notation "S1" => referenceSFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sd1" => referenceSAdjointFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "S0" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sd0" => nativeAdjointZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FC" => firstPhysicalCross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "SO" => nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "SD" => higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- All three genuine lower T/S pairs, retaining the original raw zero coefficients. -/
def lowerPhysicalCross (hreg : FixedDirichletRegularity) (d0 : ℝ) (germs : CoeffRoom d0)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  let t1 := KL (T1 q (UF F) x)
  let td1 := KL (Td1 q (UF F) x)
  let t0 := (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x
  let td0 := (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x
  let s1 := KL (S1 g2 dr Ar p q (UF F) x)
  let sd1 := KL (Sd1 g2 dr Ar p q (UF F) x)
  let s0 := KL (S0 hreg d0 germs g2 dr Ar p hdr hAr q F x)
  let sd0 := KL (Sd0 hreg d0 germs g2 dr Ar p hdr hAr q F x)
  (⟪t1,s0⟫_ℝ-⟪td1,sd0⟫_ℝ)+(⟪t0,s1⟫_ℝ-⟪td0,sd1⟫_ℝ)+
    (⟪t0,s0⟫_ℝ-⟪td0,sd0⟫_ℝ)

local notation "Lower" => lowerPhysicalCross g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] nativeT nativeTdag nativeZ nativeReferenceZeroCoefficient
  nativeReferenceAdjointZeroCoefficient nativeHigherSHalf higherSAdjointHalf nativeZeroHalf
  referenceSFirstHalf referenceSAdjointFirstHalf higherSInput finiteCoreSobolevLift

/-- Exact full physical cross: raw N-1 is unchanged, and Z occurs once with its minus sign. -/
theorem native_TS_cross_eq_principal_lower_and_Z (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪(nativeT hO hD hF g hg L q dr Ar p hdr hAr F).val x,
      SO dr Ar p hdr hAr q hreg d0 germs g2 F x⟫_ℝ-
      ⟪((nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F)+
        (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F)).val x,
        SD hreg d0 germs g2 dr Ar p hdr hAr q F x⟫_ℝ =
      FC g2 dr Ar p q (UF F) x+Lower hreg d0 germs g2 dr Ar p hdr hAr q F x-
        ⟪(nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
          SD hreg d0 germs g2 dr Ar p hdr hAr q F x⟫_ℝ := by
  have ht := nativeT_eq_first_and_original_zero hO hD hF g hg L q dr Ar p hdr hAr F x
  have htd := nativeTdag_eq_first_and_original_zero hO hD hF g hg L q dr Ar p hdr hAr F x
  have hs := nativeS_eq_first_and_original_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 germs g2 dr Ar p hdr hAr q F x
  have hsd := nativeSdag_eq_first_and_original_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 germs g2 dr Ar p hdr hAr q F x
  have hsp : SO dr Ar p hdr hAr q hreg d0 germs g2 F x =
      KL (S1 g2 dr Ar p q (UF F) x)+KL (S0 hreg d0 germs g2 dr Ar p hdr hAr q F x) := by
    simpa only [nativeHigherSOut,map_add] using congrArg KL hs
  have hsdp : SD hreg d0 germs g2 dr Ar p hdr hAr q F x =
      KL (Sd1 g2 dr Ar p q (UF F) x)+KL (Sd0 hreg d0 germs g2 dr Ar p hdr hAr q F x) := by
    simpa only [higherSAdjointOut,map_add] using congrArg KL hsd
  rw [hsp,hsdp]
  simp only [Submodule.coe_add,Pi.add_apply]
  rw [ht,htd]
  simpa only [higherSInput,firstPhysicalCross,lowerPhysicalCross] using
    split_cross
      (KL (T1 q (UF F) x))
      ((nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x)
      (KL (Td1 q (UF F) x))
      ((nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x)
      (KL (S1 g2 dr Ar p q (UF F) x))
      (KL (S0 hreg d0 germs g2 dr Ar p hdr hAr q F x))
      (KL (Sd1 g2 dr Ar p q (UF F) x))
      (KL (Sd0 hreg d0 germs g2 dr Ar p hdr hAr q F x))
      ((nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x)

/-- Literal full-error rows preserve Main's norm defect and the third thread's factor 2. -/
theorem actual_model_S_unestimated_eq_rows
    (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    actualModelSUnestimatedDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F x =
      (‖SO dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x‖^2-
        ‖SD hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x‖^2-
        ⟪F.val x,actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          Room hreg data g2 dr Ar p q F x⟫_ℝ)+
      4*FC g2 dr Ar p q (UF F) x+
      4*Lower hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x-
      4*⟪(nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
        SD hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x⟫_ℝ+
      2*nativeULowerSCrossDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F x := by
  unfold actualModelSUnestimatedDensity
  rw [native_TS_cross_eq_principal_lower_and_Z g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0]
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFullLowerAssembly

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFullLowerAssembly.native_TS_cross_eq_principal_lower_and_Z
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFullLowerAssembly.actual_model_S_unestimated_eq_rows
