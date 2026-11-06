import Calderon.ActualModelSErrorDecomposition

/-!
Author: GPT-6.1 Sol, lower U/S authoring support.
Upfront expansion and exact target: lower-u-s-nov03-v001/upfront-v001.
This module proves only integrability and exact integral bookkeeping. It
asserts no quantitative estimate for the remaining lower U/S group.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSIntegralSplit
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualModelSMixedComparison ConformalDepth
  ReferenceWeightedApproximation ReferenceDensityBounds NormalizedPrincipalMetric

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
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)

local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
  dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "UF" => nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "UD" => nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "Sc" => ActualScalarSAdjointCross.nativeScalarSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
  g2 dr Ar p hdr hAr q (referenceNormalizedPrincipalDifference g g2 L q)
local notation "Lo" => nativeULowerSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
  g2 hg2 dr Ar p hdr hAr q

/-- The full physical U/S density splits into the checked scalar density and
the existing literal B/C,V/W,density-corrected lower density. -/
theorem nativeUSCrossDensity_eq_scalar_add_lower
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪(UF F).val x,SO F x⟫_ℝ - ⟪(UD F).val x,SD F x⟫_ℝ = Sc F x + Lo F x := by
  exact nativeU_scalar_signed_pairing_split hO hD hF g g2 hg hg2
    L q dr Ar p hdr hAr F x (SO F x) (SD F x)

/-- Integrability and the exact signed integral split, including the original
factor two. No bound on the lower integral is part of this proposition. -/
def LowerUSIntegralSplit (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let full : R3 → ℝ := fun x => ⟪(UF F).val x,SO F x⟫_ℝ - ⟪(UD F).val x,SD F x⟫_ℝ
  Integrable (fun x => mu x * Lo F x) ∧
  Integrable (fun x => mu x * (2 * Lo F x)) ∧
  Integrable (fun x => mu x * finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x) ∧
  Integrable (fun x => mu x * full x) ∧
  Integrable (fun x => mu x * Sc F x) ∧
  (∫ x, mu x * full x) = (∫ x, mu x * Sc F x) + (∫ x, mu x * Lo F x) ∧
  (∫ x, mu x * (2 * full x)) =
    (∫ x, mu x * (2 * Sc F x)) + (∫ x, mu x * (2 * Lo F x)) ∧
  (∫ x, mu x * (2 * Lo F x)) = 2 * (∫ x, mu x * Lo F x)

/-- The checked original decomposition supplies lower and original-energy
integrability; the exact scalar split then supplies all integral bookkeeping. -/
theorem lowerUSIntegralSplit_of_decomposition
    (CErr eta : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (hDecomp : ActualModelSErrorDecomposition
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q CErr eta F) :
    LowerUSIntegralSplit g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let fu : R3 → ℝ := fun x => mu x *
    (⟪(UF F).val x,SO F x⟫_ℝ - ⟪(UD F).val x,SD F x⟫_ℝ)
  let fs : R3 → ℝ := fun x => mu x * Sc F x
  let fl : R3 → ℝ := fun x => mu x * Lo F x
  rcases hDecomp with ⟨hMixed,hLo,_hRem,_hKnown,hEnergy,_hEq,_hBound⟩
  rcases hMixed with ⟨_hFullF,_hFullD,_hMF,_hMD,_hSF,_hSD,_hT,hFull,_hMixedEq⟩
  have he : fu = fun x => fs x + fl x := by
    funext x
    have hp := nativeUSCrossDensity_eq_scalar_add_lower
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F x
    dsimp only [fu,fs,fl]
    rw [hp]
    ring
  have heSub : fs = fun x => fu x - fl x := by
    funext x
    have hp := congrFun he x
    linarith only [hp]
  have hScalar : Integrable fs :=
    Eq.mpr (congrArg (fun f : R3 → ℝ => Integrable f) heSub) (hFull.sub hLo)
  have hi : (∫ x, fu x) = (∫ x, fs x) + (∫ x, fl x) :=
    (congrArg (fun f : R3 → ℝ => ∫ x, f x) he).trans (integral_add hScalar hLo)
  have hTwice : (fun x => mu x * (2 * Lo F x)) = fun x => 2 * fl x := by
    funext x
    dsimp only [fl]
    ring
  have hTwiceLo : Integrable (fun x => mu x * (2 * Lo F x)) := by
    rw [hTwice]
    exact hLo.const_mul 2
  have hiTwiceLo : (∫ x, mu x * (2 * Lo F x)) = 2 * (∫ x, fl x) := by
    rw [hTwice,integral_const_mul]
  have hTwiceFull :
      (fun x => mu x * (2 *
        (⟪(UF F).val x,SO F x⟫_ℝ - ⟪(UD F).val x,SD F x⟫_ℝ))) =
        fun x => 2 * fu x := by
    funext x
    dsimp only [fu]
    ring
  have hTwiceScalar : (fun x => mu x * (2 * Sc F x)) = fun x => 2 * fs x := by
    funext x
    dsimp only [fs]
    ring
  refine ⟨hLo,hTwiceLo,hEnergy,hFull,hScalar,hi,?_,hiTwiceLo⟩
  change (∫ x, mu x * (2 *
      (⟪(UF F).val x,SO F x⟫_ℝ - ⟪(UD F).val x,SD F x⟫_ℝ))) =
    (∫ x, mu x * (2 * Sc F x)) + (∫ x, mu x * (2 * Lo F x))
  rw [hTwiceFull,hTwiceScalar,hiTwiceLo,integral_const_mul,integral_const_mul,hi]
  ring

/-- One positive threshold precedes every original profile and finite input.
This is only the exact-integral milestone, with no lower U/S smallness claim. -/
theorem exists_lowerUSIntegralSplit
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ etaUS : ℝ, 0 < etaUS ∧ etaUS ≤ data.eta0 ∧ etaUS ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaUS →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x *
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta * referenceRadius dr Ar p L x) →
      LowerUSIntegralSplit g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F := by
  obtain ⟨CErr,_hCErr,etaUS,hEtaUS,hEtaUS0,hEtaUS1,hDecomp⟩ :=
    exists_actual_model_S_error_decomposition
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 hL hKernel
  refine ⟨etaUS,hEtaUS,hEtaUS0,hEtaUS1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaUS K hK hBall F hsupp hb hs hH8
  exact lowerUSIntegralSplit_of_decomposition
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q CErr eta F
    (hDecomp q hq dr hdr hdr1 Ar hAr p hp eta heta hetaUS K hK hBall F hsupp hb hs hH8)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSIntegralSplit
