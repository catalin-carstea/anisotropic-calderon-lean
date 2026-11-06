import Calderon.ActualUniformDensityFromFinitePhysicalCoercivity
import Calderon.SphereSobolevInclusion
import Calderon.SphereSobolevPartialSumOperator
import Calderon.WeightedAngularConvergence
import Calderon.WeightedBaseSpectral
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  WeightedAngularConvergence WeightedBaseSpectral ReferenceDensityBounds ActualFiniteHarmonicCore
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevPartialSumL referenceBaseLift

theorem sphereSobolevZeroEquiv_sphereHarmonicPartialSum
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (n:ℕ) (u:SphereL2):
    sphereSobolevZeroEquiv hO hD (sphereHarmonicPartialSum hO hD n u)=
      sphereSobolevPartialSumL 0 n (sphereSobolevZeroEquiv hO hD u) := by
  apply sphereSobolev_ext 0
  intro k
  simp only [sphereSobolevCoefficientL_zeroEquiv, sphereSobolevPartialSumL_apply,
    sphereSobolevCoefficientL_partialSum, sphereHarmonicCoordinate_partialSum]

theorem sphereSobolevInclusionL_spectralCutoff_commutes
    (s t:ℝ) (hts:t ≤ s) (n:ℕ) (u:SphereSobolev s):
    sphereSobolevInclusionL s t hts (sphereSobolevPartialSumL s n u)=
      sphereSobolevPartialSumL t n (sphereSobolevInclusionL s t hts u) := by
  apply sphereSobolev_ext t
  intro k
  simp only [sphereSobolevCoefficientL_inclusion, sphereSobolevPartialSumL_apply,
    sphereSobolevCoefficientL_partialSum]

theorem negative_sobolev_graph_of_sphereHarmonicPartialSum
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (n:ℕ)
    (v:SphereL2) (f:SphereSobolev (-(1/2:ℝ)))
    (hGraph:sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v)=f):
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (sphereHarmonicPartialSum hO hD n v))=
      sphereSobolevPartialSumL (-(1/2:ℝ)) n f := by
  rw [sphereSobolevZeroEquiv_sphereHarmonicPartialSum,
    sphereSobolevInclusionL_spectralCutoff_commutes,hGraph]

def nativePhysicalOutputPartialSumCore
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (n:ℕ)
    (V:R3→SphereL2) (hV:ContDiff ℝ ∞ V) (hVc:HasCompactSupport V):
    smoothCompactFiniteSphereCore hO hD :=
  ⟨fun y=>sphereHarmonicPartialSum hO hD n (V y),
    (sphereHarmonicPartialSum hO hD n).contDiff.comp hV,
    hVc.comp_left (map_zero (sphereHarmonicPartialSum hO hD n)),n,by
      intro y k hk
      rw [sphereHarmonicCoordinate_partialSum,ite_eq_right (not_lt.mpr hk)]⟩

theorem tsupport_nativePhysicalOutputPartialSumCore_subset
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (n:ℕ)
    (V:R3→SphereL2) (hV:ContDiff ℝ ∞ V) (hVc:HasCompactSupport V):
    tsupport (nativePhysicalOutputPartialSumCore hO hD n V hV hVc:R3→SphereL2)⊆tsupport V := by
  exact tsupport_comp_subset (map_zero (sphereHarmonicPartialSum hO hD n)) V

theorem integral_referenceDensity_partialSum_norm_sq_le
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q:ℝ)
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (n:ℕ)
    (V:R3→SphereL2) (hV:Continuous V) (hVc:HasCompactSupport V):
    (∫ y,referenceDensityFamily g L (q,y)*‖sphereHarmonicPartialSum hO hD n (V y)‖^2) ≤
      ∫ y,referenceDensityFamily g L (q,y)*‖V y‖^2 := by
  have hPC:Continuous (fun y=>sphereHarmonicPartialSum hO hD n (V y)) :=
    (sphereHarmonicPartialSum hO hD n).continuous.comp hV
  have hPComp:HasCompactSupport (fun y=>sphereHarmonicPartialSum hO hD n (V y)) :=
    hVc.comp_left (map_zero (sphereHarmonicPartialSum hO hD n))
  apply integral_mono (integrable_referenceBase_norm_sq g hg L q _ hPC hPComp)
    (integrable_referenceBase_norm_sq g hg L q V hV hVc)
  intro y
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_sphereHarmonicPartialSum_le hO hD n (V y)))
    (referenceDensityFamily_pos g hg L (q,y)).le

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
