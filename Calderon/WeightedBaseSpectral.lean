import Calderon.PositiveSpectralCore
import Calderon.ReferenceDensityBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.WeightedBaseSpectral
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  PositiveSpectralCore ReferenceDensityBounds

def referenceBaseMeasure (g : MatrixField) (L lam : ℝ) : Measure R3 :=
  volume.withDensity (fun x => ENNReal.ofReal (referenceDensityFamily g L (lam,x)))

lemma continuous_referenceBaseDensity (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) : Continuous (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
  (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)

lemma integral_referenceBaseMeasure (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) :
    (∫ x, f x ∂referenceBaseMeasure g L lam) =
      ∫ x, referenceDensityFamily g L (lam,x) * f x := by
  unfold referenceBaseMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_referenceBaseDensity g hg L lam).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [ENNReal.toReal_ofReal (referenceDensityFamily_pos g hg L (lam,x)).le]
  rfl

lemma integrable_referenceBase_norm_sq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U : R3 → SphereL2) (hU : Continuous U)
    (hcomp : HasCompactSupport U) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2) := by
  have hc : HasCompactSupport (fun x => ‖U x‖ ^ 2) :=
    hcomp.comp_left (g := fun u : SphereL2 => ‖u‖ ^ 2) (by simp)
  have hprod : HasCompactSupport (fun x => referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2) := hc.mul_left
  exact ((continuous_referenceBaseDensity g hg L lam).mul (hU.norm.pow 2)).integrable_of_hasCompactSupport hprod

lemma memLp_referenceBase (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U : R3 → SphereL2) (hU : Continuous U)
    (hcomp : HasCompactSupport U) : MemLp U 2 (referenceBaseMeasure g L lam) := by
  apply (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mpr
  unfold referenceBaseMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (continuous_referenceBaseDensity g hg L lam).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have he : (fun x => (ENNReal.ofReal (referenceDensityFamily g L (lam,x))).toReal • ‖U x‖^2) =
      (fun x => referenceDensityFamily g L (lam,x) * ‖U x‖^2) := by
    funext x
    rw [ENNReal.toReal_ofReal (referenceDensityFamily_pos g hg L (lam,x)).le]
    rfl
  rw [he]
  exact integrable_referenceBase_norm_sq g hg L lam U hU hcomp

def referenceBaseLift (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U : R3 → SphereL2) (hU : Continuous U)
    (hcomp : HasCompactSupport U) : Lp SphereL2 2 (referenceBaseMeasure g L lam) :=
  (memLp_referenceBase g hg L lam U hU hcomp).toLp U

theorem inner_referenceBaseLift (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U V : R3 → SphereL2) (hU : Continuous U) (hV : Continuous V)
    (hUc : HasCompactSupport U) (hVc : HasCompactSupport V) :
    ⟪referenceBaseLift g hg L lam U hU hUc,
      referenceBaseLift g hg L lam V hV hVc⟫_ℝ =
      ∫ x, referenceDensityFamily g L (lam,x) * ⟪U x,V x⟫_ℝ := by
  rw [L2.inner_def]
  have hfirst := (memLp_referenceBase g hg L lam U hU hUc).coeFn_toLp
  have hsecond := (memLp_referenceBase g hg L lam V hV hVc).coeFn_toLp
  have he : (∫ x, ⟪referenceBaseLift g hg L lam U hU hUc x,
      referenceBaseLift g hg L lam V hV hVc x⟫_ℝ ∂referenceBaseMeasure g L lam) =
      ∫ x, ⟪U x,V x⟫_ℝ ∂referenceBaseMeasure g L lam := by
    apply integral_congr_ae
    filter_upwards [hfirst,hsecond] with x hx hy
    exact congrArg₂ (fun u v : SphereL2 => ⟪u,v⟫_ℝ) hx hy
  exact he.trans (integral_referenceBaseMeasure g hg L lam _)

theorem norm_sq_referenceBaseLift (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U : R3 → SphereL2) (hU : Continuous U)
    (hcomp : HasCompactSupport U) :
    ‖referenceBaseLift g hg L lam U hU hcomp‖ ^ 2 =
      ∫ x, referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_referenceBaseLift]
  simp only [real_inner_self_eq_norm_sq]

lemma norm_sum_sphereHarmonicCoordinates_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : Finset ℕ) (u : SphereL2) :
    ‖∑ k ∈ s, (sphereHarmonicDecomposition hO hD u k : SphereL2)‖ ≤ ‖u‖ := by
  have hs : HasSum (fun k : ℕ => ‖sphereHarmonicDecomposition hO hD u k‖ ^ 2)
      (‖u‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num)
        (sphereHarmonicDecomposition hO hD u)
  have hsum := (orthogonalFamily_harmonicSphereSubspaces hO).norm_sum
    (sphereHarmonicDecomposition hO hD u) s
  have he : ‖∑ k ∈ s, (sphereHarmonicDecomposition hO hD u k : SphereL2)‖ ^ 2 =
      ∑ k ∈ s, ‖sphereHarmonicDecomposition hO hD u k‖ ^ 2 := by
    simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] using hsum
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [he]
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) hs

lemma norm_spherePositivePartialSum_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    ‖spherePositivePartialSum hO hD n u‖ ≤ ‖u‖ := by
  classical
  rw [spherePositivePartialSum_apply]
  have he : (∑ k ∈ (Finset.range n).image (fun k : ℕ => k+1),
      (sphereHarmonicDecomposition hO hD u k : SphereL2)) =
      ∑ k ∈ Finset.range n, (sphereHarmonicDecomposition hO hD u (k+1) : SphereL2) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  rw [← he]
  exact norm_sum_sphereHarmonicCoordinates_le hO hD _ u

lemma norm_spherePositiveProjection_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    ‖spherePositiveProjection hO hD u‖ ≤ ‖u‖ :=
  le_of_tendsto' (tendsto_spherePositivePartialSum hO hD u).norm
    (fun n => norm_spherePositivePartialSum_le hO hD n u)

theorem tendsto_integral_spherePositivePartialSum_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : Continuous U) (hcomp : HasCompactSupport U) :
    Tendsto (fun n : ℕ => ∫ x, referenceDensityFamily g L (lam,x) *
      ‖spherePositivePartialSum hO hD n (U x) - spherePositiveProjection hO hD (U x)‖ ^ 2)
      atTop (𝓝 0) := by
  have hc (n : ℕ) : Continuous (fun x => referenceDensityFamily g L (lam,x) *
      ‖spherePositivePartialSum hO hD n (U x) - spherePositiveProjection hO hD (U x)‖ ^ 2) :=
    (continuous_referenceBaseDensity g hg L lam).mul
      ((((spherePositivePartialSum hO hD n).continuous.comp hU).sub
        ((spherePositiveProjection hO hD).continuous.comp hU)).norm.pow 2)
  have hb : Integrable (fun x => 4 *
      (referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2)) :=
    (integrable_referenceBase_norm_sq g hg L lam U hU hcomp).const_mul 4
  have hbound (n : ℕ) : ∀ᵐ x, ‖referenceDensityFamily g L (lam,x) *
      ‖spherePositivePartialSum hO hD n (U x) - spherePositiveProjection hO hD (U x)‖ ^ 2‖ ≤
      4 * (referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2) := by
    apply Filter.Eventually.of_forall
    intro x
    have hr := le_of_lt (referenceDensityFamily_pos g hg L (lam,x))
    have hn : ‖spherePositivePartialSum hO hD n (U x) - spherePositiveProjection hO hD (U x)‖ ≤
        2 * ‖U x‖ := by
      calc
        _ ≤ ‖spherePositivePartialSum hO hD n (U x)‖ +
            ‖spherePositiveProjection hO hD (U x)‖ := norm_sub_le _ _
        _ ≤ ‖U x‖ + ‖U x‖ := add_le_add
          (norm_spherePositivePartialSum_le hO hD n _) (norm_spherePositiveProjection_le hO hD _)
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (sq_nonneg _))]
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [mul_le_mul_of_nonneg_left hs hr]
  have hlim : ∀ᵐ x, Tendsto (fun n : ℕ => referenceDensityFamily g L (lam,x) *
      ‖spherePositivePartialSum hO hD n (U x) - spherePositiveProjection hO hD (U x)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro x
    simpa using (((tendsto_spherePositivePartialSum hO hD (U x)).sub_const
      (spherePositiveProjection hO hD (U x))).norm.pow 2).const_mul
        (referenceDensityFamily g L (lam,x))
  simpa using tendsto_integral_of_dominated_convergence
    (fun x => 4 * (referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2))
    (fun n => (hc n).aestronglyMeasurable) hb hbound hlim

lemma referenceBaseLift_sub (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U V : R3 → SphereL2) (hU : Continuous U) (hV : Continuous V)
    (hUc : HasCompactSupport U) (hVc : HasCompactSupport V) :
    referenceBaseLift g hg L lam (fun x => U x - V x) (hU.sub hV) (hUc.sub hVc) =
      referenceBaseLift g hg L lam U hU hUc - referenceBaseLift g hg L lam V hV hVc := by
  exact MemLp.toLp_sub (memLp_referenceBase g hg L lam U hU hUc)
    (memLp_referenceBase g hg L lam V hV hVc)

theorem tendsto_referenceBaseLift_spherePositivePartialSum
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : Continuous U) (hcomp : HasCompactSupport U) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => spherePositivePartialSum hO hD n (U x))
      ((spherePositivePartialSum hO hD n).continuous.comp hU)
      (hcomp.comp_left (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => spherePositiveProjection hO hD (U x))
        ((spherePositiveProjection hO hD).continuous.comp hU)
        (hcomp.comp_left (map_zero _)))) := by
  let S (n : ℕ) := referenceBaseLift g hg L lam
    (fun x => spherePositivePartialSum hO hD n (U x))
    ((spherePositivePartialSum hO hD n).continuous.comp hU)
    (hcomp.comp_left (map_zero _))
  let V := referenceBaseLift g hg L lam (fun x => spherePositiveProjection hO hD (U x))
    ((spherePositiveProjection hO hD).continuous.comp hU)
    (hcomp.comp_left (map_zero _))
  have he (n : ℕ) : ‖S n - V‖ ^ 2 = ∫ x, referenceDensityFamily g L (lam,x) *
      ‖spherePositivePartialSum hO hD n (U x) - spherePositiveProjection hO hD (U x)‖ ^ 2 := by
    rw [← referenceBaseLift_sub]
    exact norm_sq_referenceBaseLift g hg L lam _ _ _
  have hs : Tendsto (fun n : ℕ => ‖S n - V‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [he]
    exact tendsto_integral_spherePositivePartialSum_sub_sq g hg L lam hO hD U hU hcomp
  have hn : Tendsto (fun n : ℕ => ‖S n - V‖) atTop (𝓝 (0 : ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    change Tendsto (fun n : ℕ => Real.sqrt (‖S n - V‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simpa only [dist_eq_norm] using hn

theorem tendsto_referenceBaseLift_spherePositivePartialSum_of_meanZero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : Continuous U) (hcomp : HasCompactSupport U)
    (hmean : ∀ x, sphereMean (U x) = 0) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => spherePositivePartialSum hO hD n (U x))
      ((spherePositivePartialSum hO hD n).continuous.comp hU)
      (hcomp.comp_left (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam U hU hcomp)) := by
  have he : (fun x => spherePositiveProjection hO hD (U x)) = U :=
    funext (fun x => spherePositiveProjection_eq_self hO hD (U x) (hmean x))
  simpa only [he] using tendsto_referenceBaseLift_spherePositivePartialSum
    g hg L lam hO hD U hU hcomp

lemma continuous_pureDerivative (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U) (X : R3) :
    Continuous (fun x => fderiv ℝ U x X) :=
  ((hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous

lemma hasCompactSupport_pureDerivative (U : R3 → SphereL2)
    (hcomp : HasCompactSupport U) (X : R3) :
    HasCompactSupport (fun x => fderiv ℝ U x X) := hcomp.fderiv_apply ℝ X

theorem tendsto_referenceBaseLift_pureDerivative_spectral
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U) (hcomp : HasCompactSupport U)
    (hmean : ∀ x, sphereMean (U x) = 0) (X : R3) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => spherePositivePartialSum hO hD n (fderiv ℝ U x X))
      ((spherePositivePartialSum hO hD n).continuous.comp (continuous_pureDerivative U hU X))
      ((hasCompactSupport_pureDerivative U hcomp X).comp_left (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => fderiv ℝ U x X)
        (continuous_pureDerivative U hU X) (hasCompactSupport_pureDerivative U hcomp X))) := by
  apply tendsto_referenceBaseLift_spherePositivePartialSum_of_meanZero
  intro x
  exact sphereMean_fderiv_eq_zero U x X (hU.differentiable (by simp) x) hmean

lemma pureDerivative_positivePartialSum_eq (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (n : ℕ) (x X : R3) :
    fderiv ℝ (fun y => spherePositivePartialSum hO hD n (U y)) x X =
      spherePositivePartialSum hO hD n (fderiv ℝ U x X) := by
  rw [fderiv_spherePositivePartialSum hO hD n U x (hU.differentiable (by simp) x)]
  rfl

end OAI.AnisotropicCalderon.WeightedBaseSpectral
