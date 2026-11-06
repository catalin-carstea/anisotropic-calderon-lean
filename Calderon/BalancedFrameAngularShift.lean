import Calderon.BalancedAngularShift
import Calderon.SmoothMetricFrame
import Mathlib.Analysis.Calculus.ContDiff.WithLp

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.BalancedFrameAngularShift
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  BalancedAngularShift SmoothMetricFrame

def balancedDerivativeCombination (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ i, c i • balancedDerivative hF hO hD i

def balancedRaisingCombination (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ i, c i • balancedRaising hF hO hD i

lemma norm_balancedDerivativeCombination_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (c : Fin 3 → ℝ) :
    ‖balancedDerivativeCombination hF hO hD c‖ ≤ 4 * ∑ i, |c i| := by
  calc
    ‖balancedDerivativeCombination hF hO hD c‖ ≤
        ∑ i, ‖c i • balancedDerivative hF hO hD i‖ := norm_sum_le _ _
    _ ≤ ∑ i, 4 * |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,Real.norm_eq_abs]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (norm_balancedDerivative_le hF hO hD i) (abs_nonneg (c i))
    _ = 4 * ∑ i, |c i| := by rw [Finset.mul_sum]

lemma norm_balancedRaisingCombination_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (c : Fin 3 → ℝ) :
    ‖balancedRaisingCombination hF hO hD c‖ ≤ 2 * ∑ i, |c i| := by
  calc
    ‖balancedRaisingCombination hF hO hD c‖ ≤
        ∑ i, ‖c i • balancedRaising hF hO hD i‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,Real.norm_eq_abs]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (norm_balancedRaising_le hF hO hD i) (abs_nonneg (c i))
    _ = 2 * ∑ i, |c i| := by rw [Finset.mul_sum]

lemma balancedDerivativeCombination_of_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u U : SphereL2) (v : Fin 3 → SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hv : ∀ i, (u,v i) ∈ sphereDerivativeGraph hF hO hD i) :
    balancedDerivativeCombination hF hO hD c U =
      halfDegreeMultiplier hO hD (∑ i, c i • v i) := by
  simp only [balancedDerivativeCombination,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [balancedDerivative_of_graph hF hO hD i u U (v i) hU (hv i)]

lemma balancedRaisingCombination_of_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u U : SphereL2) (v : Fin 3 → SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hv : ∀ i, (u,v i) ∈ sphereRaisingGraph hF hO hD i) :
    balancedRaisingCombination hF hO hD c U =
      halfDegreeMultiplier hO hD (∑ i, c i • v i) := by
  simp only [balancedRaisingCombination,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [balancedRaising_of_graph hF hO hD i u U (v i) hU (hv i)]

/-- The actual Gram-frame coefficients of the angular first-order part at base coordinate k. -/
def referenceCoordinateBalancedDerivative (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (k : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  balancedDerivativeCombination hF hO hD
    (fun i => referenceMetricGramFrame g L (lam,x) i k)

def referenceCoordinateBalancedRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (k : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  balancedRaisingCombination hF hO hD
    (fun i => referenceMetricGramFrame g L (lam,x) i k)

lemma contDiff_referenceCoordinateBalancedDerivative (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : Fin 3) :
    ContDiff ℝ ∞ (referenceCoordinateBalancedDerivative hF hO hD g L lam k) := by
  unfold referenceCoordinateBalancedDerivative balancedDerivativeCombination
  apply ContDiff.sum
  intro i hi
  exact ((contDiff_piLp_apply (p := (2 : ℝ≥0∞)) (i := k) :
    ContDiff ℝ ∞ (fun v : R3 => v k)).comp
    (contDiff_referenceMetricGramFrame_slice g hg L lam i)).smul contDiff_const

lemma contDiff_referenceCoordinateBalancedRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : Fin 3) :
    ContDiff ℝ ∞ (referenceCoordinateBalancedRaising hF hO hD g L lam k) := by
  unfold referenceCoordinateBalancedRaising balancedRaisingCombination
  apply ContDiff.sum
  intro i hi
  exact ((contDiff_piLp_apply (p := (2 : ℝ≥0∞)) (i := k) :
    ContDiff ℝ ∞ (fun v : R3 => v k)).comp
    (contDiff_referenceMetricGramFrame_slice g hg L lam i)).smul contDiff_const

/-- Pointwise actual geometry bound; uniform family bounds still require the geometry adapter. -/
lemma norm_referenceCoordinateBalancedDerivative_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (k : Fin 3) (x : R3) :
    ‖referenceCoordinateBalancedDerivative hF hO hD g L lam k x‖ ≤
      4 * ∑ i, |referenceMetricGramFrame g L (lam,x) i k| :=
  norm_balancedDerivativeCombination_le hF hO hD _

lemma norm_referenceCoordinateBalancedRaising_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (k : Fin 3) (x : R3) :
    ‖referenceCoordinateBalancedRaising hF hO hD g L lam k x‖ ≤
      2 * ∑ i, |referenceMetricGramFrame g L (lam,x) i k| :=
  norm_balancedRaisingCombination_le hF hO hD _


lemma balancedDerivativeCombination_inner_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u U : SphereL2) (du : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hdu : ∀ i, (u,du i) ∈ sphereDerivativeGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    ⟪∑ i, c i • du i,v⟫_ℝ = ⟪balancedDerivativeCombination hF hO hD c U,V⟫_ℝ := by
  rw [balancedDerivativeCombination_of_graph hF hO hD c u U du hU hdu]
  exact inner_eq_halfDegreeMultiplier hO hD _ v V hV

lemma abs_inner_derivativeCombination_le_half_norm (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u U : SphereL2) (du : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hdu : ∀ i, (u,du i) ∈ sphereDerivativeGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    |⟪∑ i, c i • du i,v⟫_ℝ| ≤ (4 * ∑ i, |c i|) * ‖U‖ * ‖V‖ := by
  rw [balancedDerivativeCombination_inner_realization hF hO hD c u U du v V hU hdu hV]
  have hb : ‖balancedDerivativeCombination hF hO hD c U‖ ≤ (4 * ∑ i, |c i|) * ‖U‖ :=
    ((balancedDerivativeCombination hF hO hD c).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right (norm_balancedDerivativeCombination_le hF hO hD c)
        (norm_nonneg U))
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg V))

lemma balancedRaisingCombination_inner_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u U : SphereL2) (ru : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hru : ∀ i, (u,ru i) ∈ sphereRaisingGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    ⟪∑ i, c i • ru i,v⟫_ℝ = ⟪balancedRaisingCombination hF hO hD c U,V⟫_ℝ := by
  rw [balancedRaisingCombination_of_graph hF hO hD c u U ru hU hru]
  exact inner_eq_halfDegreeMultiplier hO hD _ v V hV

lemma abs_inner_raisingCombination_le_half_norm (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (u U : SphereL2) (ru : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hru : ∀ i, (u,ru i) ∈ sphereRaisingGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    |⟪∑ i, c i • ru i,v⟫_ℝ| ≤ (2 * ∑ i, |c i|) * ‖U‖ * ‖V‖ := by
  rw [balancedRaisingCombination_inner_realization hF hO hD c u U ru v V hU hru hV]
  have hb : ‖balancedRaisingCombination hF hO hD c U‖ ≤ (2 * ∑ i, |c i|) * ‖U‖ :=
    ((balancedRaisingCombination hF hO hD c).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right (norm_balancedRaisingCombination_le hF hO hD c)
        (norm_nonneg U))
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg V))

end OAI.AnisotropicCalderon.BalancedFrameAngularShift
