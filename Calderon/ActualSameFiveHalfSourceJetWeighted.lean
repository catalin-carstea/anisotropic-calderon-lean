import Calderon.ActualMixedKernelGlobalNativeFiveHalfDensity
import Calderon.ActualFiniteCutoffCoreCorrespondence
import Calderon.WeightedBaseSpectral
import Calderon.SphereSobolevPartialSumOperator

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  WeightedBaseSpectral ReferenceDensityBounds

private lemma norm_sphereSobolevPartialSumL_le
    (s : ℝ) (n : ℕ) (u : SphereSobolev s) :
    ‖sphereSobolevPartialSumL s n u‖ ≤ ‖u‖ := by
  rw [sphereSobolevPartialSumL_apply, sphereSobolevPartialSum_eq]
  have hsum := lp.norm_sum_single (E := fun k : ℕ => harmonicSphereSubspace k)
    (p := (2 : ℝ≥0∞)) (by norm_num) (fun k => u k) (Finset.range n)
  have hsplit := lp.norm_sub_norm_compl_sub_single
    (E := fun k : ℕ => harmonicSphereSubspace k) (p := (2 : ℝ≥0∞))
    (by norm_num) u (Finset.range n)
  norm_num at hsum hsplit
  nlinarith [sq_nonneg ‖u - ∑ k ∈ Finset.range n,
    lp.single (E := fun k : ℕ => harmonicSphereSubspace k) 2 k (u k)‖,
    norm_nonneg u, norm_nonneg (∑ k ∈ Finset.range n,
    lp.single (E := fun k : ℕ => harmonicSphereSubspace k) 2 k (u k))]

private theorem tendsto_sphereSobolevPartialSumL
    (s : ℝ) (u : SphereSobolev s) :
    Tendsto (fun n : ℕ => sphereSobolevPartialSumL s n u) atTop (𝓝 u) := by
  simpa only [sphereSobolevPartialSumL_apply] using tendsto_sphereSobolevPartialSum s u

private theorem tendsto_integral_sphereSobolevPartialSumL_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (V : R3 → SphereSobolev (5/2 : ℝ))
    (hV : Continuous V) (hcomp : HasCompactSupport V) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖sphereSobolevPartialSumL (5/2 : ℝ) n (V y) - V y‖ ^ 2)
      atTop (𝓝 0) := by
  have hc (n : ℕ) : Continuous (fun y => referenceDensityFamily g L (lam,y) *
      ‖sphereSobolevPartialSumL (5/2 : ℝ) n (V y) - V y‖ ^ 2) :=
    (continuous_referenceBaseDensity g hg L lam).mul
      ((((sphereSobolevPartialSumL (5/2 : ℝ) n).continuous.comp hV).sub
        hV).norm.pow 2)
  have hbase : Integrable (fun y => referenceDensityFamily g L (lam,y) * ‖V y‖ ^ 2) := by
    have hs : HasCompactSupport (fun y => ‖V y‖ ^ 2) :=
      hcomp.comp_left (g := fun v : SphereSobolev (5/2 : ℝ) => ‖v‖ ^ 2) (by simp)
    exact ((continuous_referenceBaseDensity g hg L lam).mul
      (hV.norm.pow 2)).integrable_of_hasCompactSupport hs.mul_left
  have hb : Integrable (fun y => 4 *
      (referenceDensityFamily g L (lam,y) * ‖V y‖ ^ 2)) := hbase.const_mul 4
  have hbound (n : ℕ) : ∀ᵐ y, ‖referenceDensityFamily g L (lam,y) *
      ‖sphereSobolevPartialSumL (5/2 : ℝ) n (V y) - V y‖ ^ 2‖ ≤
      4 * (referenceDensityFamily g L (lam,y) * ‖V y‖ ^ 2) := by
    apply Filter.Eventually.of_forall
    intro y
    have hr := le_of_lt (referenceDensityFamily_pos g hg L (lam,y))
    have hn : ‖sphereSobolevPartialSumL (5/2 : ℝ) n (V y) - V y‖ ≤
        2 * ‖V y‖ := by
      calc
        _ ≤ ‖sphereSobolevPartialSumL (5/2 : ℝ) n (V y)‖ + ‖V y‖ := norm_sub_le _ _
        _ ≤ ‖V y‖ + ‖V y‖ := add_le_add
          (norm_sphereSobolevPartialSumL_le (5/2 : ℝ) n _) (le_refl _)
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (sq_nonneg _))]
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [mul_le_mul_of_nonneg_left hs hr]
  have hlim : ∀ᵐ y, Tendsto (fun n : ℕ => referenceDensityFamily g L (lam,y) *
      ‖sphereSobolevPartialSumL (5/2 : ℝ) n (V y) - V y‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro y
    simpa using (((tendsto_sphereSobolevPartialSumL (5/2 : ℝ) (V y)).sub_const
      (V y)).norm.pow 2).const_mul (referenceDensityFamily g L (lam,y))
  simpa using tendsto_integral_of_dominated_convergence
    (fun y => 4 * (referenceDensityFamily g L (lam,y) * ‖V y‖ ^ 2))
    (fun n => (hc n).aestronglyMeasurable) hb hbound hlim

lemma contDiff_sphereSobolevPartialSumL_fiveHalf
    (U : R3 → SphereSobolev (5/2 : ℝ)) (hU : ContDiff ℝ ∞ U) (n : ℕ) :
    ContDiff ℝ ∞ (fun y => sphereSobolevPartialSumL (5/2 : ℝ) n (U y)) :=
  (sphereSobolevPartialSumL (5/2 : ℝ) n).contDiff.comp hU

lemma hasCompactSupport_sphereSobolevPartialSumL_fiveHalf
    (U : R3 → SphereSobolev (5/2 : ℝ)) (hcomp : HasCompactSupport U) (n : ℕ) :
    HasCompactSupport (fun y => sphereSobolevPartialSumL (5/2 : ℝ) n (U y)) :=
  hcomp.comp_left (map_zero _)

lemma fderiv_sphereSobolevPartialSumL_fiveHalf
    (U : R3 → SphereSobolev (5/2 : ℝ)) (hU : ContDiff ℝ ∞ U)
    (n : ℕ) (y X : R3) :
    fderiv ℝ (fun z => sphereSobolevPartialSumL (5/2 : ℝ) n (U z)) y X =
      sphereSobolevPartialSumL (5/2 : ℝ) n (fderiv ℝ U y X) := by
  have hderiv := ((sphereSobolevPartialSumL (5/2 : ℝ) n).hasFDerivAt.comp y
    ((hU.differentiable (by simp) y).hasFDerivAt)).fderiv
  change (fderiv ℝ (sphereSobolevPartialSumL (5/2 : ℝ) n ∘ U) y) X = _
  rw [hderiv]
  rfl

lemma secondFderiv_sphereSobolevPartialSumL_fiveHalf
    (U : R3 → SphereSobolev (5/2 : ℝ)) (hU : ContDiff ℝ ∞ U)
    (n : ℕ) (y X Y : R3) :
    fderiv ℝ (fun z => fderiv ℝ
        (fun z' => sphereSobolevPartialSumL (5/2 : ℝ) n (U z')) z X) y Y =
      sphereSobolevPartialSumL (5/2 : ℝ) n
        (fderiv ℝ (fun z => fderiv ℝ U z X) y Y) := by
  have hEq : (fun z => fderiv ℝ
      (fun z' => sphereSobolevPartialSumL (5/2 : ℝ) n (U z')) z X) =
      (fun z => sphereSobolevPartialSumL (5/2 : ℝ) n (fderiv ℝ U z X)) :=
    funext (fun z => fderiv_sphereSobolevPartialSumL_fiveHalf U hU n z X)
  have hEqF := congrArg (fun f : R3 → SphereSobolev (5/2 : ℝ) =>
    fderiv ℝ f y Y) hEq
  exact hEqF.trans (fderiv_sphereSobolevPartialSumL_fiveHalf _
    ((hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) n y Y)

theorem tendsto_integral_sphereSobolevPartialSumL_fiveHalf_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (U : R3 → SphereSobolev (5/2 : ℝ))
    (hU : ContDiff ℝ ∞ U) (hcomp : HasCompactSupport U) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖sphereSobolevPartialSumL (5/2 : ℝ) n (U y) - U y‖ ^ 2)
      atTop (𝓝 0) :=
  tendsto_integral_sphereSobolevPartialSumL_sub_sq g hg L lam U hU.continuous hcomp

theorem tendsto_integral_fderiv_sphereSobolevPartialSumL_fiveHalf_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (U : R3 → SphereSobolev (5/2 : ℝ))
    (hU : ContDiff ℝ ∞ U) (hcomp : HasCompactSupport U) (X : R3) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖fderiv ℝ (fun z => sphereSobolevPartialSumL (5/2 : ℝ) n (U z)) y X -
        fderiv ℝ U y X‖ ^ 2) atTop (𝓝 0) := by
  simp_rw [fderiv_sphereSobolevPartialSumL_fiveHalf U hU]
  have hV : ContDiff ℝ ∞ (fun y => fderiv ℝ U y X) :=
    (hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact tendsto_integral_sphereSobolevPartialSumL_sub_sq g hg L lam _
    hV.continuous (hcomp.fderiv_apply ℝ X)

theorem tendsto_integral_secondFderiv_sphereSobolevPartialSumL_fiveHalf_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (U : R3 → SphereSobolev (5/2 : ℝ))
    (hU : ContDiff ℝ ∞ U) (hcomp : HasCompactSupport U) (X Y : R3) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖fderiv ℝ (fun z => fderiv ℝ
          (fun z' => sphereSobolevPartialSumL (5/2 : ℝ) n (U z')) z X) y Y -
        fderiv ℝ (fun z => fderiv ℝ U z X) y Y‖ ^ 2) atTop (𝓝 0) := by
  simp_rw [secondFderiv_sphereSobolevPartialSumL_fiveHalf U hU]
  have hV : ContDiff ℝ ∞ (fun y => fderiv ℝ U y X) :=
    (hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hVV : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => fderiv ℝ U z X) y Y) :=
    (hV.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact tendsto_integral_sphereSobolevPartialSumL_sub_sq g hg L lam _
    hVV.continuous ((hcomp.fderiv_apply ℝ X).fderiv_apply ℝ Y)


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
