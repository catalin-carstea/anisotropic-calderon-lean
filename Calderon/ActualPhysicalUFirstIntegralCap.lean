import Calderon.ActualPhysicalUFirstPointwiseCap
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral
import Calderon.ReferenceWeightedApproximation

/-! Root continuation of the exact Opus v033 pointwise statement.
Before-source: actual-coercivity-UFirst-integral-Root-day-oct29-v001/before-source-v001.
Actual weighted integrability and support are derived, never assumed. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth

attribute [local irreducible] nativeUFirstOut referenceRadius actualReferenceBeta
  finiteCoreReferenceProfileEnergy referenceDensityFamily

private lemma radius_sq_le_eta_sq_inv_floor_four {r beta BF eta : ℝ}
    (hr : 0 < r) (hBF : 0 < BF) (hBeta : BF ≤ beta)
    (hRoom : r * beta ^ 2 ≤ eta) :
    r ^ 2 ≤ eta ^ 2 * (BF ^ 4)⁻¹ := by
  have hBeta0 : 0 ≤ beta := hBF.le.trans hBeta
  have hSquare : BF ^ 2 ≤ beta ^ 2 :=
    (sq_le_sq₀ hBF.le hBeta0).2 hBeta
  have hFloorRoom : r * BF ^ 2 ≤ eta :=
    (mul_le_mul_of_nonneg_left hSquare hr.le).trans hRoom
  have hBF2 : 0 < BF ^ 2 := sq_pos_of_pos hBF
  have hEta0 : 0 ≤ eta := (mul_nonneg hr.le (sq_nonneg BF)).trans hFloorRoom
  have hDiv : r ≤ eta / BF ^ 2 := (le_div_iff₀ hBF2).2 hFloorRoom
  have hDiv0 : 0 ≤ eta / BF ^ 2 := div_nonneg hEta0 hBF2.le
  calc
    r ^ 2 ≤ (eta / BF ^ 2) ^ 2 := (sq_le_sq₀ hr.le hDiv0).2 hDiv
    _ = eta ^ 2 * (BF ^ 4)⁻¹ := by
      field_simp
      <;> ring

/-- The actual native first-correction error has a uniform weighted integral cap.
The constant precedes every profile parameter and the finite input. -/
theorem exists_nativeUFirstOut_uniform_integral_cap
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C_UF : ℝ, 0 < C_UF ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ δ A : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      ∀ hA : 0 < A, ∀ p : ℕ, 2 ≤ p →
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 → ∀ BF : ℝ, 1 ≤ BF →
      ∀ F0 : smoothCompactFiniteSphereCore hO hD, tsupport F0.val ⊆ K →
      (∀ y ∈ K, BF ≤ actualReferenceBeta g L q δ A p y) →
      (∀ y ∈ K, ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ 1) →
      (∀ y ∈ K, referenceRadius δ A p L y *
        actualReferenceBeta g L q δ A p y ^ 2 ≤ eta) →
      (∫ y : R3, referenceDensityFamily g L (q,y) *
        ‖nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0 y‖ ^ 2) ≤
      (C_UF * (eta ^ 2 * (BF ^ 4)⁻¹)) *
        ∫ y : R3, referenceDensityFamily g L (q,y) *
          finiteCoreReferenceProfileEnergy hO hD g hg L q
            (actualReferenceBeta g L q δ A p y) F0 y := by
  obtain ⟨CU, hCU, hPoint⟩ :=
    exists_nativeUFirstOut_uniform_pointwise_cap hF hO hD g hg g2 hg2 L hL K hK
  refine ⟨CU, hCU, ?_⟩
  intro q hq δ A hδ hδ1 hA p hp eta hEta hEta1 BF hBF F0 hSupport hBetaFloor hDerivative hRoom
  have hp1 : 1 ≤ p := by omega
  have hBF0 : 0 < BF := zero_lt_one.trans_le hBF
  let beta : R3 → ℝ := actualReferenceBeta g L q δ A p
  let rho : R3 → ℝ := fun y => referenceDensityFamily g L (q,y)
  let U : R3 → SphereL2 := nativeUFirstOut hF hO hD g hg g2 L q δ A p hδ hA F0
  let E : R3 → ℝ := fun y => finiteCoreReferenceProfileEnergy hO hD g hg L q (beta y) F0 y
  let coeff : ℝ := CU * (eta ^ 2 * (BF ^ 4)⁻¹)
  have hCoeff : 0 ≤ coeff := by dsimp only [coeff]; positivity
  have hBetaContinuous : Continuous beta :=
    continuous_actualReferenceBeta g hg L q δ A p hL hδ hA
  have hBetaPositive (y : R3) : 0 < beta y :=
    actualReferenceBeta_pos g hg L q δ A p hL hδ hA hp1 y
  have hRhoContinuous : Continuous rho :=
    WeightedBaseSpectral.continuous_referenceBaseDensity g hg L q
  have hRhoNonneg (y : R3) : 0 ≤ rho y :=
    (referenceDensityFamily_pos g hg L (q,y)).le
  have hENonneg (y : R3) : 0 ≤ E y :=
    finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta y)
      (hBetaPositive y).le F0 y
  have hOutputSupport : tsupport U ⊆ K :=
    (tsupport_nativeUFirstOut_subset hF hO hD g hg g2 L q δ A p hδ hA F0).2.1.trans hSupport
  have hOutputIntegral : Integrable (fun y : R3 => rho y * ‖U y‖ ^ 2) :=
    integrable_weighted_norm_sq_nativeUFirstOut hF hO hD g hg g2 hg2 L q δ A p hδ hA
      F0 rho hRhoContinuous
  have hEnergyIntegral : Integrable (fun y : R3 => rho y * E y) :=
    integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hBetaContinuous
      hBetaPositive F0
  have hGlobal (y : R3) : ‖U y‖ ^ 2 ≤ coeff * E y := by
    by_cases hy : y ∈ K
    · have hLocal := hPoint q hq δ A hδ hδ1 hA p hp eta hEta hEta1 BF hBF F0 y hy
        (hBetaFloor y hy) (hDerivative y hy) (hRoom y hy)
      have hRadius := radius_sq_le_eta_sq_inv_floor_four
        (referenceRadius_pos δ A p L y hδ hA) hBF0 (hBetaFloor y hy) (hRoom y hy)
      change ‖U y‖ ^ 2 ≤ CU * referenceRadius δ A p L y ^ 2 * E y at hLocal
      calc
        ‖U y‖ ^ 2 ≤ CU * referenceRadius δ A p L y ^ 2 * E y := hLocal
        _ = (CU * E y) * referenceRadius δ A p L y ^ 2 := by ring
        _ ≤ (CU * E y) * (eta ^ 2 * (BF ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left hRadius (mul_nonneg hCU.le (hENonneg y))
        _ = coeff * E y := by dsimp only [coeff]; ring
    · have hZero : U y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hs => hy (hOutputSupport hs))
      rw [hZero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg hCoeff (hENonneg y)
  have hWeighted (y : R3) : rho y * ‖U y‖ ^ 2 ≤ coeff * (rho y * E y) := by
    calc
      rho y * ‖U y‖ ^ 2 ≤ rho y * (coeff * E y) :=
        mul_le_mul_of_nonneg_left (hGlobal y) (hRhoNonneg y)
      _ = coeff * (rho y * E y) := by ring
  calc
    (∫ y : R3, rho y * ‖U y‖ ^ 2) ≤ ∫ y : R3, coeff * (rho y * E y) :=
      integral_mono hOutputIntegral (hEnergyIntegral.const_mul coeff) hWeighted
    _ = coeff * ∫ y : R3, rho y * E y := integral_const_mul coeff _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeUFirstOut_uniform_integral_cap
