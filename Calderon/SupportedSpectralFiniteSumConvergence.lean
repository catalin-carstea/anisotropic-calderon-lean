import Calderon.ActualSameFiveHalfSourceJetWeighted

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

private lemma norm_partialSumL_le (n : ℕ) (u : SphereSobolev (5/2:ℝ)) :
    ‖sphereSobolevPartialSumL (5/2:ℝ) n u‖ ≤ ‖u‖ := by
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

private lemma tendsto_partialSumL (u : SphereSobolev (5/2:ℝ)) :
    Tendsto (fun n : ℕ => sphereSobolevPartialSumL (5/2:ℝ) n u) atTop (𝓝 u) := by
  simpa only [sphereSobolevPartialSumL_apply] using tendsto_sphereSobolevPartialSum (5/2:ℝ) u

/-- Finite local operator coefficients acting on the same high source jets.
The compact bound is derived here; it is not a uniform density constant. -/
theorem tendsto_integral_supported_finite_clm_partialSum_error
    {ι : Type*} [Fintype ι] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (S : Set R3) (hS : IsCompact S)
    (U : ι → R3 → SphereSobolev (5/2:ℝ)) (hU : ∀ k, Continuous (U k))
    (hSupp : ∀ k, tsupport (U k) ⊆ S)
    (A : ι → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (hA : ∀ k, ∀ y ∈ S, ContinuousAt (A k) y) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖∑ k, A k y (sphereSobolevPartialSumL (5/2:ℝ) n (U k y) - U k y)‖ ^ 2)
      atTop (𝓝 0) := by
  classical
  let E : ℕ → R3 → W := fun n y =>
    ∑ k, A k y (sphereSobolevPartialSumL (5/2:ℝ) n (U k y) - U k y)
  let b : R3 → ℝ := fun y => ∑ k, ‖A k y‖
  have hb : ContinuousOn b S := by
    apply continuousOn_finset_sum
    intro k hk
    have hNorm : Continuous (fun T : SphereSobolev (5/2:ℝ) →L[ℝ] W => ‖T‖) := continuous_norm
    exact hNorm.comp_continuousOn (show ContinuousOn (A k) S from fun y hy => (hA k y hy).continuousWithinAt)
  obtain ⟨C0,hC0⟩ := hS.exists_bound_of_continuousOn hb
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hAC (k : ι) (y : R3) (hy : y ∈ S) : ‖A k y‖ ≤ C := by
    have hSingle : ‖A k y‖ ≤ b y :=
      Finset.single_le_sum (fun j hj => norm_nonneg (A j y)) (Finset.mem_univ k)
    have hbn : 0 ≤ b y := Finset.sum_nonneg (fun j hj => norm_nonneg (A j y))
    have hbc : b y ≤ C0 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hbn] using hC0 y hy
    exact hSingle.trans (hbc.trans (le_max_left _ _))
  have hE (n : ℕ) : Continuous (E n) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hy : y ∈ S
    · apply tendsto_finsetSum
      intro k hk
      exact (hA k y hy).clm_apply
        (((sphereSobolevPartialSumL (5/2:ℝ) n).continuous.continuousAt.comp
          (hU k).continuousAt).sub (hU k).continuousAt)
    · have hZero : E n =ᶠ[𝓝 y] (fun _ => (0 : W)) := by
        have hEach : ∀ᶠ z in 𝓝 y, ∀ k : ι, U k z = 0 := by
          apply Filter.eventually_all.mpr
          intro k
          exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hSupp k h))
        filter_upwards [hEach] with z hz
        simp only [E,hz,map_zero,sub_zero,Finset.sum_const_zero]
      exact continuousAt_const.congr_of_eventuallyEq hZero
  let M : R3 → ℝ := fun y => ∑ k, ‖U k y‖
  have hM : Continuous M := continuous_finset_sum _ (fun k hk => (hU k).norm)
  have hMSupp : tsupport M ⊆ S := by
    apply closure_minimal ?_ hS.isClosed
    intro y hy
    by_contra hOutside
    have hz (k : ι) : U k y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hOutside (hSupp k h))
    exact hy (by simp [M,hz])
  have hMComp : HasCompactSupport M := hS.of_isClosed_subset (isClosed_tsupport M) hMSupp
  have hDom : Integrable (fun y => referenceDensityFamily g L (lam,y) * (2*C*M y)^2) := by
    have hComp : HasCompactSupport (fun y => (2*C*M y)^2) :=
      hMComp.comp_left (g := fun t : ℝ => (2*C*t)^2) (by simp)
    exact ((continuous_referenceBaseDensity g hg L lam).mul
      ((continuous_const.mul hM).pow 2)).integrable_of_hasCompactSupport hComp.mul_left
  have hBound (n : ℕ) : ∀ᵐ y, ‖referenceDensityFamily g L (lam,y) * ‖E n y‖^2‖ ≤
      referenceDensityFamily g L (lam,y) * (2*C*M y)^2 := by
    apply Filter.Eventually.of_forall
    intro y
    have hMN : 0 ≤ M y := Finset.sum_nonneg (fun k hk => norm_nonneg (U k y))
    have hNorm : ‖E n y‖ ≤ 2*C*M y := by
      by_cases hy : y ∈ S
      · calc
          ‖E n y‖ ≤ ∑ k, ‖A k y (sphereSobolevPartialSumL (5/2:ℝ) n (U k y) - U k y)‖ := norm_sum_le _ _
          _ ≤ ∑ k, C*(2*‖U k y‖) := by
            apply Finset.sum_le_sum
            intro k hk
            have hCut : ‖sphereSobolevPartialSumL (5/2:ℝ) n (U k y) - U k y‖ ≤ 2*‖U k y‖ :=
              (norm_sub_le _ _).trans (by linarith [norm_partialSumL_le n (U k y)])
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul (hAC k y hy) hCut (norm_nonneg _) hC)
          _ = 2*C*M y := by simp only [M,← Finset.mul_sum]; ring
      · have hz (k : ι) : U k y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hSupp k h))
        simp only [E,M,hz,map_zero,sub_zero,Finset.sum_const_zero,norm_zero,mul_zero,le_refl]
    have hw : 0 ≤ referenceDensityFamily g L (lam,y) := (referenceDensityFamily_pos g hg L (lam,y)).le
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hNorm) hw
  have hPoint : ∀ᵐ y, Tendsto (fun n : ℕ => referenceDensityFamily g L (lam,y) * ‖E n y‖^2) atTop (𝓝 (0:ℝ)) := by
    apply Filter.Eventually.of_forall
    intro y
    have hEach (k : ι) : Tendsto (fun n : ℕ =>
        A k y (sphereSobolevPartialSumL (5/2:ℝ) n (U k y) - U k y)) atTop (𝓝 0) := by
      have hZero : Tendsto (fun n : ℕ => sphereSobolevPartialSumL (5/2:ℝ) n (U k y) - U k y) atTop (𝓝 0) := by
        simpa using (tendsto_partialSumL (U k y)).sub_const (U k y)
      have hz := ((A k y).continuous.tendsto 0).comp hZero
      simpa only [Function.comp_def,map_zero] using hz
    have hSum : Tendsto (fun n => E n y) atTop (𝓝 0) := by
      simpa only [E,Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun k hk => hEach k)
    simpa using (hSum.norm.pow 2).const_mul (referenceDensityFamily g L (lam,y))
  simpa only [E,Pi.mul_apply,Pi.pow_apply,integral_zero] using tendsto_integral_of_dominated_convergence
    (fun y => referenceDensityFamily g L (lam,y) * (2*C*M y)^2)
    (fun n => ((continuous_referenceBaseDensity g hg L lam).mul ((hE n).norm.pow 2)).aestronglyMeasurable)
    hDom hBound hPoint

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
