import Calderon.SupportedWeightedSphereL2Graph

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

theorem tendsto_integral_referenceDensity_norm_sq_of_error_tendsto
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (U : ℕ → R3 → SphereL2) (u : R3 → SphereL2)
    (hU : ∀ n, Continuous (U n)) (hu : Continuous u)
    (hUc : ∀ n, HasCompactSupport (U n)) (huc : HasCompactSupport u)
    (hLimit : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖U n y-u y‖^2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) * ‖U n y‖^2) atTop
      (𝓝 (∫ y, referenceDensityFamily g L (q,y) * ‖u y‖^2)) := by
  have hF := tendsto_referenceBaseLift_of_weighted_sq_tendsto
    g hg L q U u hU hu hUc huc hLimit
  have hNorm : Tendsto
      (fun n : ℕ => ‖referenceBaseLift g hg L q (U n) (hU n) (hUc n)‖^2) atTop
      (𝓝 (‖referenceBaseLift g hg L q u hu huc‖^2)) :=
    ((continuous_norm.tendsto _).comp hF).pow 2
  simpa only [norm_sq_referenceBaseLift] using hNorm

/-- The SAME finite coercivity constant survives the original source/output
graph limit. The finite estimate itself remains an explicit obligation. -/
theorem weighted_physical_coercive_bound_of_graph_limits
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q c : ℝ)
    (U : ℕ → R3 → SphereL2) (u : R3 → SphereL2)
    (V : ℕ → R3 → SphereL2) (v : R3 → SphereL2)
    (hU : ∀ n, Continuous (U n)) (hu : Continuous u)
    (hV : ∀ n, Continuous (V n)) (hv : Continuous v)
    (hUc : ∀ n, HasCompactSupport (U n)) (huc : HasCompactSupport u)
    (hVc : ∀ n, HasCompactSupport (V n)) (hvc : HasCompactSupport v)
    (hSource : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖U n y-u y‖^2) atTop (𝓝 0))
    (hOutput : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖V n y-v y‖^2) atTop (𝓝 0))
    (hFinite : ∀ n : ℕ, c*(∫ y, referenceDensityFamily g L (q,y) * ‖U n y‖^2) ≤
      ∫ y, referenceDensityFamily g L (q,y) * ‖V n y‖^2) :
    c*(∫ y, referenceDensityFamily g L (q,y) * ‖u y‖^2) ≤
      ∫ y, referenceDensityFamily g L (q,y) * ‖v y‖^2 := by
  exact le_of_tendsto_of_tendsto
    ((tendsto_integral_referenceDensity_norm_sq_of_error_tendsto g hg L q U u hU hu hUc huc hSource).const_mul c)
    (tendsto_integral_referenceDensity_norm_sq_of_error_tendsto g hg L q V v hV hv hVc hvc hOutput)
    (Filter.Eventually.of_forall hFinite)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
