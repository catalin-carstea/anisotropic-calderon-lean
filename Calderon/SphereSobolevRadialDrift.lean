import Calderon.SphereSobolevCompletion
import Calderon.BoundedRadialDriftTrace

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SphereHilbertDecomposition SpectralWeightedGraph BoundedSpectralMultiplier
  HarmonicDerivativeOperator BoundedAngularShift
  OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-! Real weighted extension of the existing radialDriftTraceL. The L2 conduit
uses normalized lp coefficients, not an unscaled negative-order representative.
Degree one lowers to degree zero; no positive-mode projection is inserted. -/


def radialDriftSobolevBound (s : ℝ) : ℝ := max 1 ((2 : ℝ) ^ (-s))

def radialDriftSobolevRatio (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else ((k : ℝ) / (1 + (k : ℝ))) ^ s

theorem abs_radialDriftSobolevRatio_le (s : ℝ) (k : ℕ) :
    |radialDriftSobolevRatio s k| ≤ radialDriftSobolevBound s := by
  by_cases hk : k = 0
  · simp only [radialDriftSobolevRatio, hk, if_true, abs_one]
    exact le_max_left _ _
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  have hd : 0 < 1 + (k : ℝ) := by positivity
  have hratio : 0 < (k : ℝ) / (1 + (k : ℝ)) :=
    div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hk1) hd
  have hupper : (k : ℝ) / (1 + (k : ℝ)) ≤ 1 := by
    apply (div_le_one (a := (k : ℝ)) (b := 1 + (k : ℝ)) hd).mpr
    linarith
  have hlower : (1 / 2 : ℝ) ≤ (k : ℝ) / (1 + (k : ℝ)) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  rw [radialDriftSobolevRatio, if_neg hk,
    abs_of_pos (Real.rpow_pos_of_pos hratio s)]
  by_cases hs : 0 ≤ s
  · calc
      _ ≤ (1 : ℝ) ^ s := Real.rpow_le_rpow hratio.le hupper hs
      _ = 1 := Real.one_rpow s
      _ ≤ radialDriftSobolevBound s := le_max_left _ _
  · have hs0 : s ≤ 0 := (lt_of_not_ge hs).le
    calc
      _ ≤ (1 / 2 : ℝ) ^ s :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hlower hs0
      _ = (2 : ℝ) ^ (-s) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
          ← Real.rpow_neg_eq_inv_rpow]
      _ ≤ radialDriftSobolevBound s := le_max_right _ _

theorem radialDriftSobolevRatio_mul_weight (s : ℝ) (m : ℕ) :
    radialDriftSobolevRatio s (m + 1) * besselWeight s (m + 1) = besselWeight s m := by
  rw [radialDriftSobolevRatio, if_neg (by omega : m + 1 ≠ 0)]
  rw [Real.div_rpow (Nat.cast_nonneg (m + 1)) (by positivity :
    (0 : ℝ) ≤ 1 + ((m + 1 : ℕ) : ℝ))]
  unfold besselWeight
  rw [div_mul_cancel₀ _
    (Real.rpow_pos_of_pos (by positivity : 0 < 1 + ((m + 1 : ℕ) : ℝ)) s).ne']
  congr 1
  push_cast
  ring

def radialDriftSobolevMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) : SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD (radialDriftSobolevRatio s) (radialDriftSobolevBound s)
    (le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_max_left _ _))
    (abs_radialDriftSobolevRatio_le s)

def radialDriftBlockL (hF : SphereFischerInner) (d : R3) (m : ℕ) :
    harmonicSphereSubspace (m + 1) →L[ℝ] harmonicSphereSubspace m :=
  (-(2 * ((m + 1 : ℕ) : ℝ) + 1)⁻¹) •
    ∑ i : Fin 3, (d i) • harmonicDerivative hF m i

theorem radialDriftTraceL_subtype (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (m : ℕ) (a : harmonicSphereSubspace (m + 1)) :
    radialDriftTraceL hF hO hD d (a : SphereL2) =
      (radialDriftBlockL hF d m a : SphereL2) := by
  have hw : radialDriftWeight (m + 1) * inverseDegreeWeight (m + 1) =
      (2 * ((m + 1 : ℕ) : ℝ) + 1)⁻¹ := by
    unfold radialDriftWeight inverseDegreeWeight
    have h1 : (1 : ℝ) + ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h2 : (2 : ℝ) * ((m + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp [h1, h2]
    <;> ring
  simp only [radialDriftTraceL, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, radialDriftMultiplier_single, map_smul,
    normalizedDerivative_single, smul_smul, hw]
  change -∑ i : Fin 3, (d i * (2 * ((m + 1 : ℕ) : ℝ) + 1)⁻¹) •
      (harmonicDerivative hF m i a : SphereL2) =
    ((-(2 * ((m + 1 : ℕ) : ℝ) + 1)⁻¹) •
      (∑ i : Fin 3, (d i) • harmonicDerivative hF m i a : harmonicSphereSubspace m) :
      SphereL2)
  simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.smul_sum,
    smul_smul, ← Finset.sum_neg_distrib, ← neg_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

def sphereSobolevRadialDriftL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  (sphereHarmonicDecomposition hO hD).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((radialDriftTraceL hF hO hD d).comp
      ((radialDriftSobolevMultiplier hO hD s).comp
        (sphereHarmonicDecomposition hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem norm_sphereSobolevRadialDriftL_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) :
    ‖sphereSobolevRadialDriftL hF hO hD s d‖ ≤
      (2 * ∑ i : Fin 3, |d i|) * radialDriftSobolevBound s := by
  have hC : 0 ≤ (2 : ℝ) * ∑ i : Fin 3, |d i| :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i hi => abs_nonneg (d i))
  have hR : 0 ≤ radialDriftSobolevBound s :=
    le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_max_left _ _)
  refine (sphereSobolevRadialDriftL hF hO hD s d).opNorm_le_bound
    (mul_nonneg hC hR) ?_
  intro u
  change ‖sphereHarmonicDecomposition hO hD
    (radialDriftTraceL hF hO hD d
      (radialDriftSobolevMultiplier hO hD s
        ((sphereHarmonicDecomposition hO hD).symm u)))‖ ≤
    (2 * ∑ i : Fin 3, |d i|) * radialDriftSobolevBound s * ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  have hM : ‖radialDriftSobolevMultiplier hO hD s
      ((sphereHarmonicDecomposition hO hD).symm u)‖ ≤
      radialDriftSobolevBound s * ‖(sphereHarmonicDecomposition hO hD).symm u‖ := by
    exact norm_boundedSpectralOutput_le hO hD (radialDriftSobolevRatio s)
      (radialDriftSobolevBound s) hR (abs_radialDriftSobolevRatio_le s) _
  calc
    _ ≤ ‖radialDriftTraceL hF hO hD d‖ *
        ‖radialDriftSobolevMultiplier hO hD s
          ((sphereHarmonicDecomposition hO hD).symm u)‖ :=
      (radialDriftTraceL hF hO hD d).le_opNorm _
    _ ≤ (2 * ∑ i : Fin 3, |d i|) *
        ‖radialDriftSobolevMultiplier hO hD s
          ((sphereHarmonicDecomposition hO hD).symm u)‖ :=
      mul_le_mul_of_nonneg_right (norm_radialDriftTraceL_le hF hO hD d) (norm_nonneg _)
    _ ≤ (2 * ∑ i : Fin 3, |d i|) *
        (radialDriftSobolevBound s * ‖(sphereHarmonicDecomposition hO hD).symm u‖) :=
      mul_le_mul_of_nonneg_left hM hC
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

theorem sphereSobolevRadialDriftL_single (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (m : ℕ) (a : harmonicSphereSubspace (m + 1)) :
    sphereSobolevRadialDriftL hF hO hD s d (sphereSobolevSingleL s (m + 1) a) =
      sphereSobolevSingleL s m (radialDriftBlockL hF d m a) := by
  have hM : radialDriftSobolevMultiplier hO hD s (a : SphereL2) =
      radialDriftSobolevRatio s (m + 1) • (a : SphereL2) := by
    exact boundedSpectralMultiplier_single hO hD (radialDriftSobolevRatio s)
      (radialDriftSobolevBound s)
      (le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_max_left _ _))
      (abs_radialDriftSobolevRatio_le s) (m + 1) a
  change sphereHarmonicDecomposition hO hD
      (radialDriftTraceL hF hO hD d
        (radialDriftSobolevMultiplier hO hD s
          ((sphereHarmonicDecomposition hO hD).symm
            (besselWeight s (m + 1) • lp.single (E := fun j : ℕ => harmonicSphereSubspace j) 2 (m + 1) a)))) =
    besselWeight s m • lp.single (E := fun j : ℕ => harmonicSphereSubspace j) 2 m (radialDriftBlockL hF d m a)
  rw [← sphereHarmonicDecomposition_subtype hO hD (m + 1) a,
    ← (sphereHarmonicDecomposition hO hD).map_smul,
    LinearIsometryEquiv.symm_apply_apply]
  simp only [map_smul, hM, smul_smul, radialDriftTraceL_subtype,
    sphereHarmonicDecomposition_subtype]
  rw [mul_comm (besselWeight s (m + 1)), radialDriftSobolevRatio_mul_weight]

theorem sphereSobolevRadialDriftL_constant (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (a : harmonicSphereSubspace 0) :
    sphereSobolevRadialDriftL hF hO hD s d (sphereSobolevSingleL s 0 a) = 0 := by
  have hM : radialDriftSobolevMultiplier hO hD s (a : SphereL2) =
      radialDriftSobolevRatio s 0 • (a : SphereL2) := by
    exact boundedSpectralMultiplier_single hO hD (radialDriftSobolevRatio s)
      (radialDriftSobolevBound s)
      (le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_max_left _ _))
      (abs_radialDriftSobolevRatio_le s) 0 a
  change sphereHarmonicDecomposition hO hD
      (radialDriftTraceL hF hO hD d
        (radialDriftSobolevMultiplier hO hD s
          ((sphereHarmonicDecomposition hO hD).symm
            (besselWeight s 0 • lp.single (E := fun j : ℕ => harmonicSphereSubspace j) 2 0 a)))) = 0
  rw [besselWeight_zero_degree, one_smul,
    ← sphereHarmonicDecomposition_subtype hO hD 0 a,
    LinearIsometryEquiv.symm_apply_apply, hM, map_smul,
    radialDriftTraceL_constant, smul_zero, map_zero]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.abs_radialDriftSobolevRatio_le

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.radialDriftSobolevRatio_mul_weight

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.radialDriftTraceL_subtype

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevRadialDriftL_le

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRadialDriftL_single

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRadialDriftL_constant
