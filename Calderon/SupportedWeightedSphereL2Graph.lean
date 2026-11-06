import Calderon.SphereSobolevHalfWeightedGraphLowering

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

/-- Weighted square-error convergence gives convergence in the ORIGINAL
referenceBaseLift L2 space. -/
theorem tendsto_referenceBaseLift_of_weighted_sq_tendsto
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (U : ℕ → R3 → SphereL2) (u : R3 → SphereL2)
    (hU : ∀ n, Continuous (U n)) (hu : Continuous u)
    (hUc : ∀ n, HasCompactSupport (U n)) (huc : HasCompactSupport u)
    (hLimit : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖U n y - u y‖^2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L q (U n) (hU n) (hUc n)) atTop
      (𝓝 (referenceBaseLift g hg L q u hu huc)) := by
  let F (n : ℕ) := referenceBaseLift g hg L q (U n) (hU n) (hUc n)
  let f := referenceBaseLift g hg L q u hu huc
  have hSq (n : ℕ) : ‖F n - f‖^2 =
      ∫ y, referenceDensityFamily g L (q,y) * ‖U n y - u y‖^2 := by
    rw [←referenceBaseLift_sub]
    exact norm_sq_referenceBaseLift g hg L q _ _ _
  have hs : Tendsto (fun n : ℕ => ‖F n - f‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [hSq] using hLimit
  have hn : Tendsto (fun n : ℕ => ‖F n - f‖) atTop (𝓝 (0:ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    change Tendsto (fun n : ℕ => Real.sqrt (‖F n - f‖^2)) atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using h
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hn

theorem supported_weighted_half_graph_to_sphereL2
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (S : Set R3) (hS : IsCompact S)
    (W : ℕ → R3 → SphereSobolev (1/2:ℝ)) (w : R3 → SphereSobolev (1/2:ℝ))
    (hW : ∀ n, ContDiff ℝ ∞ (W n)) (hw : ContDiff ℝ ∞ w)
    (hSuppW : ∀ n, tsupport (W n) ⊆ S) (hSuppw : tsupport w ⊆ S)
    (P : ℕ → R3 → SphereSobolev (-(1/2:ℝ))) (p : R3 → SphereSobolev (-(1/2:ℝ)))
    (hP : ∀ n, (fun y => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (W n y)) = P n)
    (hp : (fun y => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (w y)) = p)
    (hLimit : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖W n y - w y‖^2) atTop (𝓝 0)) :
    let F : ℕ → R3 → SphereL2 := fun n y => sphereSobolevHalfToSphereL2L hO hD (W n y)
    let f : R3 → SphereL2 := fun y => sphereSobolevHalfToSphereL2L hO hD (w y)
    (∀ n, ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧
      MemLp (F n) 2 (referenceBaseMeasure g L q) ∧
      (fun y => sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (F n y))) = P n) ∧
    ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ MemLp f 2 (referenceBaseMeasure g L q) ∧
    (fun y => sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (f y))) = p ∧
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) * ‖F n y - f y‖^2)
      atTop (𝓝 0) := by
  extract_lets F f
  let T := sphereSobolevHalfToSphereL2L hO hD
  have hFSmooth (n : ℕ) : ContDiff ℝ ∞ (F n) := T.contDiff.comp (hW n)
  have hfSmooth : ContDiff ℝ ∞ f := T.contDiff.comp hw
  have hFSupp (n : ℕ) : tsupport (F n) ⊆ S :=
    (tsupport_comp_subset (map_zero T) (W n)).trans (hSuppW n)
  have hfSupp : tsupport f ⊆ S := (tsupport_comp_subset (map_zero T) w).trans hSuppw
  have hFCompact (n : ℕ) : HasCompactSupport (F n) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hFSupp n)
  have hfCompact : HasCompactSupport f := hS.of_isClosed_subset (isClosed_tsupport _) hfSupp
  have hFGraph (n : ℕ) :
      (fun y => sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (F n y))) = P n :=
    (funext (fun y => sphereSobolevHalfToSphereL2L_negative_compatibility hO hD (W n y))).trans (hP n)
  have hfGraph :
      (fun y => sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (f y))) = p :=
    (funext (fun y => sphereSobolevHalfToSphereL2L_negative_compatibility hO hD (w y))).trans hp
  have hConv := (weighted_half_graph_limits_in_zero_and_sphereL2
    g hg L q hO hD S hS W w (fun n => (hW n).continuous) hw.continuous hSuppW hSuppw hLimit).2
  constructor
  · intro n
    exact ⟨hFSmooth n,hFCompact n,
      memLp_referenceBase g hg L q (F n) (hFSmooth n).continuous (hFCompact n),hFGraph n⟩
  constructor
  · exact hfSmooth
  constructor
  · exact hfCompact
  constructor
  · exact memLp_referenceBase g hg L q f hfSmooth.continuous hfCompact
  constructor
  · exact hfGraph
  · exact hConv

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
