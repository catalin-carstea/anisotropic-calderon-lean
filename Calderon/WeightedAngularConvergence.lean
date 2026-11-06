import Calderon.WeightedBaseSpectral
import Calderon.BoundedSpectralMultiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.WeightedAngularConvergence
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph SpectralWeightComparison BoundedSpectralMultiplier
  WeightedBaseSpectral ReferenceDensityBounds

lemma norm_sphereHarmonicPartialSum_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (u : SphereL2) :
    ‖sphereHarmonicPartialSum hO hD n u‖ ≤ ‖u‖ := by
  rw [sphereHarmonicPartialSum_apply]
  exact norm_sum_sphereHarmonicCoordinates_le hO hD (Finset.range n) u

lemma boundedSpectralMultiplier_partialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (n : ℕ) (u : SphereL2) :
    boundedSpectralMultiplier hO hD w C hC hw (sphereHarmonicPartialSum hO hD n u) =
      sphereHarmonicPartialSum hO hD n (boundedSpectralMultiplier hO hD w C hC hw u) := by
  apply spectralGraph_output_unique hO hD w (sphereHarmonicPartialSum hO hD n u)
  · exact boundedSpectralMultiplier_mem hO hD w C hC hw _
  · exact spectralGraph_partialSum hO hD w (u,boundedSpectralMultiplier hO hD w C hC hw u)
      (boundedSpectralMultiplier_mem hO hD w C hC hw u) n

lemma casimirBesselMultiplier_partialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2) (n : ℕ) (u : SphereL2) :
    casimirBesselMultiplier hO hD s hs (sphereHarmonicPartialSum hO hD n u) =
      sphereHarmonicPartialSum hO hD n (casimirBesselMultiplier hO hD s hs u) :=
  boundedSpectralMultiplier_partialSum hO hD (casimirBesselRatio s) 2 (by norm_num)
    (abs_casimirBesselRatio_le_two s hs) n u

theorem tendsto_integral_sphereHarmonicPartialSum_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : Continuous U) (hcomp : HasCompactSupport U) :
    Tendsto (fun n : ℕ => ∫ x, referenceDensityFamily g L (lam,x) *
      ‖sphereHarmonicPartialSum hO hD n (U x) - U x‖ ^ 2)
      atTop (𝓝 0) := by
  have hc (n : ℕ) : Continuous (fun x => referenceDensityFamily g L (lam,x) *
      ‖sphereHarmonicPartialSum hO hD n (U x) - U x‖ ^ 2) :=
    (continuous_referenceBaseDensity g hg L lam).mul
      ((((sphereHarmonicPartialSum hO hD n).continuous.comp hU).sub
        hU).norm.pow 2)
  have hb : Integrable (fun x => 4 *
      (referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2)) :=
    (integrable_referenceBase_norm_sq g hg L lam U hU hcomp).const_mul 4
  have hbound (n : ℕ) : ∀ᵐ x, ‖referenceDensityFamily g L (lam,x) *
      ‖sphereHarmonicPartialSum hO hD n (U x) - U x‖ ^ 2‖ ≤
      4 * (referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2) := by
    apply Filter.Eventually.of_forall
    intro x
    have hr := le_of_lt (referenceDensityFamily_pos g hg L (lam,x))
    have hn : ‖sphereHarmonicPartialSum hO hD n (U x) - U x‖ ≤
        2 * ‖U x‖ := by
      calc
        _ ≤ ‖sphereHarmonicPartialSum hO hD n (U x)‖ +
            ‖U x‖ := norm_sub_le _ _
        _ ≤ ‖U x‖ + ‖U x‖ := add_le_add
          (norm_sphereHarmonicPartialSum_le hO hD n _) (le_refl _)
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (sq_nonneg _))]
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [mul_le_mul_of_nonneg_left hs hr]
  have hlim : ∀ᵐ x, Tendsto (fun n : ℕ => referenceDensityFamily g L (lam,x) *
      ‖sphereHarmonicPartialSum hO hD n (U x) - U x‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro x
    simpa using (((tendsto_sphereHarmonicPartialSum hO hD (U x)).sub_const
      (U x)).norm.pow 2).const_mul
        (referenceDensityFamily g L (lam,x))
  simpa using tendsto_integral_of_dominated_convergence
    (fun x => 4 * (referenceDensityFamily g L (lam,x) * ‖U x‖ ^ 2))
    (fun n => (hc n).aestronglyMeasurable) hb hbound hlim

theorem tendsto_referenceBaseLift_sphereHarmonicPartialSum
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : Continuous U) (hcomp : HasCompactSupport U) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (U x))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp hU)
      (hcomp.comp_left (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam U hU hcomp)) := by
  let S (n : ℕ) := referenceBaseLift g hg L lam
    (fun x => sphereHarmonicPartialSum hO hD n (U x))
    ((sphereHarmonicPartialSum hO hD n).continuous.comp hU)
    (hcomp.comp_left (map_zero _))
  let V := referenceBaseLift g hg L lam U hU hcomp
  have he (n : ℕ) : ‖S n - V‖ ^ 2 = ∫ x, referenceDensityFamily g L (lam,x) *
      ‖sphereHarmonicPartialSum hO hD n (U x) - U x‖ ^ 2 := by
    rw [← referenceBaseLift_sub]
    exact norm_sq_referenceBaseLift g hg L lam _ _ _
  have hs : Tendsto (fun n : ℕ => ‖S n - V‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [he]
    exact tendsto_integral_sphereHarmonicPartialSum_sub_sq g hg L lam hO hD U hU hcomp
  have hn : Tendsto (fun n : ℕ => ‖S n - V‖) atTop (𝓝 (0 : ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    change Tendsto (fun n : ℕ => Real.sqrt (‖S n - V‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simpa only [dist_eq_norm] using hn

theorem casimirBesselMultiplier_partialSum_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2) (n : ℕ) (u v : SphereL2)
    (hv : (u,v) ∈ spectralGraph hO hD casimirWeight) :
    (sphereHarmonicPartialSum hO hD n u,
      sphereHarmonicPartialSum hO hD n (casimirBesselMultiplier hO hD s hs v)) ∈
        sphereBesselGraph hO hD s := by
  rw [← casimirBesselMultiplier_partialSum]
  exact casimirBesselMultiplier_graph hO hD s hs _ _
    (spectralGraph_partialSum hO hD casimirWeight (u,v) hv n)

theorem tendsto_referenceBaseLift_casimirBesselMultiplier
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) (V : R3 → SphereL2)
    (hV : Continuous V) (hcomp : HasCompactSupport V) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (casimirBesselMultiplier hO hD s hs (V x)))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp
        ((casimirBesselMultiplier hO hD s hs).continuous.comp hV))
      ((hasCompactSupport_casimirBesselMultiplier hO hD s hs V hcomp).comp_left (map_zero _)))
      atTop (𝓝 (referenceBaseLift g hg L lam
        (fun x => casimirBesselMultiplier hO hD s hs (V x))
        ((casimirBesselMultiplier hO hD s hs).continuous.comp hV)
        (hasCompactSupport_casimirBesselMultiplier hO hD s hs V hcomp))) :=
  tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD _
    ((casimirBesselMultiplier hO hD s hs).continuous.comp hV)
    (hasCompactSupport_casimirBesselMultiplier hO hD s hs V hcomp)

theorem tendsto_referenceBaseLift_casimirBesselMultiplier_partialSum
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) (V : R3 → SphereL2)
    (hV : Continuous V) (hcomp : HasCompactSupport V) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => casimirBesselMultiplier hO hD s hs (sphereHarmonicPartialSum hO hD n (V x)))
      ((casimirBesselMultiplier hO hD s hs).continuous.comp
        ((sphereHarmonicPartialSum hO hD n).continuous.comp hV))
      (hasCompactSupport_casimirBesselMultiplier hO hD s hs _
        (hasCompactSupport_sphereHarmonicPartialSum hO hD n V hcomp)))
      atTop (𝓝 (referenceBaseLift g hg L lam
        (fun x => casimirBesselMultiplier hO hD s hs (V x))
        ((casimirBesselMultiplier hO hD s hs).continuous.comp hV)
        (hasCompactSupport_casimirBesselMultiplier hO hD s hs V hcomp))) := by
  simpa only [casimirBesselMultiplier_partialSum] using
    tendsto_referenceBaseLift_casimirBesselMultiplier g hg L lam hO hD s hs V hV hcomp

lemma contDiff_pureDerivative (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U) (X : R3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ U x X) :=
  (hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem tendsto_referenceBaseLift_pureDerivative_full
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (hcomp : HasCompactSupport U) (X : R3) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (fderiv ℝ U x X))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp (continuous_pureDerivative U hU X))
      ((hasCompactSupport_pureDerivative U hcomp X).comp_left (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => fderiv ℝ U x X)
        (continuous_pureDerivative U hU X) (hasCompactSupport_pureDerivative U hcomp X))) :=
  tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD _
    (continuous_pureDerivative U hU X) (hasCompactSupport_pureDerivative U hcomp X)

theorem tendsto_referenceBaseLift_secondPureDerivative_full
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (hcomp : HasCompactSupport U) (X Y : R3) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => sphereHarmonicPartialSum hO hD n (fderiv ℝ (fun y => fderiv ℝ U y X) x Y))
      ((sphereHarmonicPartialSum hO hD n).continuous.comp
        (continuous_pureDerivative _ (contDiff_pureDerivative U hU X) Y))
      ((hasCompactSupport_pureDerivative _ (hasCompactSupport_pureDerivative U hcomp X) Y).comp_left
        (map_zero _))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => fderiv ℝ (fun y => fderiv ℝ U y X) x Y)
        (continuous_pureDerivative _ (contDiff_pureDerivative U hU X) Y)
        (hasCompactSupport_pureDerivative _ (hasCompactSupport_pureDerivative U hcomp X) Y))) :=
  tendsto_referenceBaseLift_pureDerivative_full g hg L lam hO hD _
    (contDiff_pureDerivative U hU X) (hasCompactSupport_pureDerivative U hcomp X) Y

lemma pureDerivative_harmonicPartialSum_eq (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (n : ℕ) (x X : R3) :
    fderiv ℝ (fun y => sphereHarmonicPartialSum hO hD n (U y)) x X =
      sphereHarmonicPartialSum hO hD n (fderiv ℝ U x X) := by
  rw [fderiv_sphereHarmonicPartialSum hO hD n U x (hU.differentiable (by simp) x)]
  rfl

lemma secondPureDerivative_harmonicPartialSum_eq (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (U : R3 → SphereL2) (hU : ContDiff ℝ ∞ U)
    (n : ℕ) (x X Y : R3) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => sphereHarmonicPartialSum hO hD n (U z)) y X) x Y =
      sphereHarmonicPartialSum hO hD n (fderiv ℝ (fun y => fderiv ℝ U y X) x Y) := by
  have he : (fun y => fderiv ℝ (fun z => sphereHarmonicPartialSum hO hD n (U z)) y X) =
      (fun y => sphereHarmonicPartialSum hO hD n (fderiv ℝ U y X)) :=
    funext (fun y => pureDerivative_harmonicPartialSum_eq hO hD U hU n y X)
  rw [he]
  exact pureDerivative_harmonicPartialSum_eq hO hD _ (contDiff_pureDerivative U hU X) n x Y

lemma sphereHarmonicPartialSum_base_smul (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (n : ℕ) (a : R3 → ℝ) (U : R3 → SphereL2) (x : R3) :
    sphereHarmonicPartialSum hO hD n (a x • U x) =
      a x • sphereHarmonicPartialSum hO hD n (U x) := map_smul _ _ _

theorem tendsto_referenceBaseLift_base_smul
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a : R3 → ℝ) (ha : Continuous a) (U : R3 → SphereL2)
    (hU : Continuous U) (hcomp : HasCompactSupport U) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => a x • sphereHarmonicPartialSum hO hD n (U x))
      (ha.smul ((sphereHarmonicPartialSum hO hD n).continuous.comp hU))
      ((hasCompactSupport_sphereHarmonicPartialSum hO hD n U hcomp).smul_left (f := a))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => a x • U x)
        (ha.smul hU) (hcomp.smul_left (f := a)))) := by
  simpa only [map_smul] using
    tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD
      (fun x => a x • U x) (ha.smul hU) (hcomp.smul_left (f := a))

theorem tendsto_referenceBaseLift_base_rpow_smul
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta : R3 → ℝ) (hb : Continuous beta) (hpos : ∀ x, 0 < beta x) (t : ℝ)
    (U : R3 → SphereL2) (hU : Continuous U) (hcomp : HasCompactSupport U) :
    Tendsto (fun n : ℕ => referenceBaseLift g hg L lam
      (fun x => beta x ^ t • sphereHarmonicPartialSum hO hD n (U x))
      ((hb.rpow_const (fun x => Or.inl (hpos x).ne')).smul
        ((sphereHarmonicPartialSum hO hD n).continuous.comp hU))
      ((hasCompactSupport_sphereHarmonicPartialSum hO hD n U hcomp).smul_left
        (f := fun x => beta x ^ t))) atTop
      (𝓝 (referenceBaseLift g hg L lam (fun x => beta x ^ t • U x)
        ((hb.rpow_const (fun x => Or.inl (hpos x).ne')).smul hU)
          (hcomp.smul_left (f := fun x => beta x ^ t)))) :=
  tendsto_referenceBaseLift_base_smul g hg L lam hO hD (fun x => beta x ^ t)
    (hb.rpow_const (fun x => Or.inl (hpos x).ne')) U hU hcomp

end OAI.AnisotropicCalderon.WeightedAngularConvergence
