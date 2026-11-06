import Calderon.ActualPhysicalUFirstIntegralCap
import Calderon.ActualMixedJProfileAbsorption

/-! Root continuation, before-source expansion in the UFirst integral Root archive.
The exact native mixed correction already includes the model drift. This sum is
therefore relative to nativeModelRaising, not a second copy of normalized drift.
No physical graph is asserted by this integral estimate. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth

/-- The literal canonical full mixed correction, with its original H¹ input inclusion. -/
def nativeMixedJOut (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g g2 : MatrixField) (L q δ A : ℝ) (p : ℕ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : SphereL2 :=
  (sphereSobolevZeroEquiv hO hD).symm
    (referenceNativeMovingAdjointParametricJ hF hO hD g g2 L
      ((q,y), fderiv ℝ (referenceRadius δ A p L) y)
      (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)))

/-- The actual low output: full mixed correction plus the literal first-correction error. -/
def nativeMixedFirstCorrectionLowOut (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (L q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : SphereL2 :=
  nativeMixedJOut hF hO hD g g2 L q δ A p F0 y +
    nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 y

attribute [local irreducible] referenceNativeMovingAdjointParametricJ
  sphereSobolevInclusionL sphereSobolevZeroEquiv finiteCoreSobolevLift nativeUFirstOut

lemma nativeMixedJOut_smooth_compact (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (L q δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (nativeMixedJOut hF hO hD g g2 L q δ A p F0) ∧
      HasCompactSupport (nativeMixedJOut hF hO hD g g2 L q δ A p F0) := by
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F0
  have hPrep := referenceNativeMovingAdjointParametricJ_lift_smooth_compact
    hF hO hD g g2 hg hg2 L q (referenceRadius δ A p L) hR
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) hRep.1 hRep.2.1
  exact ⟨hPrep.2.2.2.1, hPrep.2.2.2.2.2.1⟩

lemma nativeMixedFirstCorrectionLowOut_smooth_compact (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (L q δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A) (F0 : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (nativeMixedFirstCorrectionLowOut hF hO hD g hg g2 L q δ A p hδ hA F0) ∧
      HasCompactSupport (nativeMixedFirstCorrectionLowOut hF hO hD g hg g2 L q δ A p hδ hA F0) := by
  have hJ := nativeMixedJOut_smooth_compact hF hO hD g hg g2 hg2 L q δ A p hδ hA F0
  have hU := contDiff_nativeUFirstOut hF hO hD g hg g2 hg2 L q δ A p hδ hA F0
  have hUSupport := (tsupport_nativeUFirstOut_subset hF hO hD g hg g2 L q δ A p hδ hA F0).2.2
  exact ⟨hJ.1.add hU, hJ.2.add hUSupport⟩

/-- A before-profile constant controls the actual complete native low output.
All integrability and support-ball premises of the reused mixed-J estimate are discharged. -/
theorem exists_nativeMixedFirstCorrectionLowOut_uniform_integral_cap
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C_low : ℝ, 0 < C_low ∧ ∀ hreg : FixedDirichletRegularity,
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ δ A : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      ∀ hA : 0 < A, ∀ p : ℕ, 2 ≤ p →
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 → ∀ BF : ℝ, 1 ≤ BF →
      ∀ F0 : smoothCompactFiniteSphereCore hO hD, tsupport F0.val ⊆ K →
      (∀ y ∈ K, BF ≤ actualReferenceBeta g L q δ A p y) →
      (∀ y ∈ K, ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ 1) →
      (∀ y ∈ K, referenceRadius δ A p L y *
        actualReferenceBeta g L q δ A p y ^ 2 ≤ eta) →
      (∫ y : R3, referenceDensityFamily g L (q,y) *
        ‖nativeMixedFirstCorrectionLowOut hF hO hD g hg g2 L q δ A p hδ hA F0 y‖ ^ 2) ≤
      C_low * ((BF ^ 2)⁻¹ + eta ^ 2 * (BF ^ 4)⁻¹) *
        ∫ y : R3, referenceDensityFamily g L (q,y) *
          finiteCoreReferenceProfileEnergy hO hD g hg L q
            (actualReferenceBeta g L q δ A p y) F0 y := by
  obtain ⟨D, hD0, hDcap⟩ := exists_nonneg_norm_le_of_isCompact hK continuous_id
  let radius : ℝ := D + 1
  obtain ⟨CJ, hCJ, hJCap⟩ := exists_referenceNativeMixedJ_uniform_profile_energy_bound
    g L (0 : R3) radius hg hF hO hD g2 hg2 hL
  obtain ⟨CU, hCU, hUCap⟩ := exists_nativeUFirstOut_uniform_integral_cap
    hF hO hD g hg g2 hg2 L hL K hK
  refine ⟨2 * (CJ + CU), by positivity, ?_⟩
  intro hreg q hq δ A hδ hδ1 hA p hp eta hEta hEta1 BF hBF F0 hSupport hBetaFloor hDerivative hRoom
  have hp1 : 1 ≤ p := by omega
  have hBF0 : 0 < BF := zero_lt_one.trans_le hBF
  have hBF2 : 0 < BF ^ 2 := sq_pos_of_pos hBF0
  let J : R3 → SphereL2 := nativeMixedJOut hF hO hD g g2 L q δ A p F0
  let U : R3 → SphereL2 := nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0
  let rho : R3 → ℝ := fun y => referenceDensityFamily g L (q,y)
  let IE : ℝ := ∫ y : R3, rho y * finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q δ A p y) F0 y
  let IJ : ℝ := ∫ y : R3, rho y * ‖J y‖ ^ 2
  let IU : ℝ := ∫ y : R3, rho y * ‖U y‖ ^ 2
  have hSupportRoom (y : R3) (hy : y ∈ tsupport F0.val) :
      ‖y - (0 : R3)‖ ≤ radius ∧
      ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ 1 ∧
      BF ≤ actualReferenceBeta g L q δ A p y := by
    have hyK := hSupport hy
    have hBound : ‖y‖ ≤ radius := (hDcap y hyK).trans (by dsimp only [radius]; linarith)
    exact ⟨by simpa only [sub_zero] using hBound, hDerivative y hyK, hBetaFloor y hyK⟩
  have hJScaled := hJCap hreg q hq δ A p hδ hA hp1 BF hBF F0 hSupportRoom
  change BF ^ 2 * IJ ≤ CJ * IE at hJScaled
  have hJ : IJ ≤ CJ * ((BF ^ 2)⁻¹ * IE) := by
    have hDiv : IJ ≤ (CJ * IE) / BF ^ 2 := (le_div_iff₀ hBF2).2 (by
      simpa only [mul_comm] using hJScaled)
    convert hDiv using 1 <;> simp only [div_eq_mul_inv] <;> ring
  have hU : IU ≤ (CU * (eta ^ 2 * (BF ^ 4)⁻¹)) * IE :=
    hUCap q hq δ A hδ hδ1 hA p hp eta hEta hEta1 BF hBF F0 hSupport
      hBetaFloor hDerivative hRoom
  have hIENonneg : 0 ≤ IE := by
    apply integral_nonneg
    intro y
    exact mul_nonneg (referenceDensityFamily_pos g hg L (q,y)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q
        (actualReferenceBeta g L q δ A p y)
        (actualReferenceBeta_pos g hg L q δ A p hL hδ hA hp1 y).le F0 y)
  have hRho : Continuous rho := WeightedBaseSpectral.continuous_referenceBaseDensity g hg L q
  have hJSmooth := nativeMixedJOut_smooth_compact hF hO hD g hg g2 hg2 L q δ A p hδ hA F0
  have hLowSmooth := nativeMixedFirstCorrectionLowOut_smooth_compact
    hF hO hD g hg g2 hg2 L q δ A p hδ hA F0
  have hJIntegral : Integrable (fun y : R3 => rho y * ‖J y‖ ^ 2) :=
    integrable_weighted_norm_sq_of_continuous_compact rho hRho J hJSmooth.1.continuous hJSmooth.2
  have hUIntegral : Integrable (fun y : R3 => rho y * ‖U y‖ ^ 2) :=
    integrable_weighted_norm_sq_nativeUFirstOut hF hO hD g hg g2 hg2 L q δ A p hδ hA F0 rho hRho
  have hLowIntegral : Integrable (fun y : R3 => rho y * ‖J y + U y‖ ^ 2) :=
    integrable_weighted_norm_sq_of_continuous_compact rho hRho _
      hLowSmooth.1.continuous hLowSmooth.2
  have hTriangle (y : R3) : rho y * ‖J y + U y‖ ^ 2 ≤
      2 * (rho y * ‖J y‖ ^ 2) + 2 * (rho y * ‖U y‖ ^ 2) := by
    have hNorm := norm_add_le (J y) (U y)
    have hSquare : ‖J y + U y‖ ^ 2 ≤ 2 * ‖J y‖ ^ 2 + 2 * ‖U y‖ ^ 2 := by
      nlinarith [norm_nonneg (J y), norm_nonneg (U y), norm_nonneg (J y + U y),
        sq_nonneg (‖J y‖ - ‖U y‖)]
    have hWeighted := mul_le_mul_of_nonneg_left hSquare
      (referenceDensityFamily_pos g hg L (q,y)).le
    nlinarith [hWeighted]
  have hLow : (∫ y : R3, rho y * ‖J y + U y‖ ^ 2) ≤ 2 * IJ + 2 * IU := by
    calc
      _ ≤ ∫ y : R3, 2 * (rho y * ‖J y‖ ^ 2) + 2 * (rho y * ‖U y‖ ^ 2) :=
        integral_mono hLowIntegral ((hJIntegral.const_mul 2).add (hUIntegral.const_mul 2)) hTriangle
      _ = 2 * IJ + 2 * IU := by
        rw [integral_add (hJIntegral.const_mul 2) (hUIntegral.const_mul 2), integral_const_mul,
          integral_const_mul]
  have hX : 0 ≤ (BF ^ 2)⁻¹ * IE := mul_nonneg (inv_nonneg.mpr (sq_nonneg BF)) hIENonneg
  have hY : 0 ≤ eta ^ 2 * (BF ^ 4)⁻¹ * IE := by positivity
  have hCJsum : CJ ≤ CJ + CU := by linarith
  have hCUsum : CU ≤ CJ + CU := by linarith
  have hJCommon := hJ.trans (mul_le_mul_of_nonneg_right hCJsum hX)
  have hUCommon : IU ≤ (CJ + CU) * (eta ^ 2 * (BF ^ 4)⁻¹ * IE) := by
    calc IU ≤ (CU * (eta ^ 2 * (BF ^ 4)⁻¹)) * IE := hU
      _ = CU * (eta ^ 2 * (BF ^ 4)⁻¹ * IE) := by ring
      _ ≤ (CJ + CU) * (eta ^ 2 * (BF ^ 4)⁻¹ * IE) :=
        mul_le_mul_of_nonneg_right hCUsum hY
  change (∫ y : R3, rho y * ‖J y + U y‖ ^ 2) ≤
    (2 * (CJ + CU)) * ((BF ^ 2)⁻¹ + eta ^ 2 * (BF ^ 4)⁻¹) * IE
  calc
    _ ≤ 2 * IJ + 2 * IU := hLow
    _ ≤ 2 * ((CJ + CU) * ((BF ^ 2)⁻¹ * IE)) +
          2 * ((CJ + CU) * (eta ^ 2 * (BF ^ 4)⁻¹ * IE)) := by linarith
    _ = _ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeMixedFirstCorrectionLowOut_uniform_integral_cap
