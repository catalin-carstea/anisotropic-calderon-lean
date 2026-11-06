import Calderon.SupportedSpectralFiniteSumConvergence
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

/-- Finite local operator coefficients preserve weighted L2 convergence on one
compact support. The derived bound is for this support and these coefficients. -/
theorem tendsto_integral_supported_finite_clm_of_integral_tendsto
    {ι V W : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (S : Set R3) (hS : IsCompact S)
    (U : ι → ℕ → R3 → V) (hU : ∀ i n, Continuous (U i n))
    (hSupp : ∀ i n, tsupport (U i n) ⊆ S)
    (A : ι → R3 → V →L[ℝ] W) (hA : ∀ i, ∀ y ∈ S, ContinuousAt (A i) y)
    (hLimit : ∀ i, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖U i n y‖^2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖∑ i, A i y (U i n y)‖^2) atTop (𝓝 0) := by
  classical
  let E : ℕ → R3 → W := fun n y => ∑ i, A i y (U i n y)
  let b : R3 → ℝ := fun y => ∑ i, ‖A i y‖
  have hb : ContinuousOn b S := by
    apply continuousOn_finsetSum
    intro i hi
    have hNorm : Continuous (fun T : V →L[ℝ] W => ‖T‖) := continuous_norm
    exact hNorm.comp_continuousOn
      (show ContinuousOn (A i) S from fun y hy => (hA i y hy).continuousWithinAt)
  obtain ⟨C0,hC0⟩ := hS.exists_bound_of_continuousOn hb
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hAC (i : ι) (y : R3) (hy : y ∈ S) : ‖A i y‖ ≤ C := by
    have hSingle : ‖A i y‖ ≤ b y :=
      Finset.single_le_sum (fun j hj => norm_nonneg (A j y)) (Finset.mem_univ i)
    have hbn : 0 ≤ b y := Finset.sum_nonneg (fun j hj => norm_nonneg (A j y))
    have hbc : b y ≤ C0 := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hbn] using hC0 y hy
    exact hSingle.trans (hbc.trans (le_max_left _ _))
  have hE (n : ℕ) : Continuous (E n) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hy : y ∈ S
    · apply tendsto_finsetSum
      intro i hi
      exact (hA i y hy).clm_apply (hU i n).continuousAt
    · have hZero : E n =ᶠ[𝓝 y] (fun _ => (0 : W)) := by
        have hEach : ∀ᶠ z in 𝓝 y, ∀ i : ι, U i n z = 0 := by
          apply Filter.eventually_all.mpr
          intro i
          exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hSupp i n h))
        filter_upwards [hEach] with z hz
        simp only [E,hz,map_zero,Finset.sum_const_zero]
      exact continuousAt_const.congr_of_eventuallyEq hZero
  have hESupp (n : ℕ) : tsupport (E n) ⊆ S := by
    apply closure_minimal ?_ hS.isClosed
    intro y hy
    by_contra hOutside
    have hz (i : ι) : U i n y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hOutside (hSupp i n h))
    exact hy (by simp only [E,hz,map_zero,Finset.sum_const_zero])
  have hEi (n : ℕ) : Integrable (fun y => referenceDensityFamily g L (lam,y) * ‖E n y‖^2) := by
    have hComp : HasCompactSupport (E n) := hS.of_isClosed_subset (isClosed_tsupport _) (hESupp n)
    have hSq : HasCompactSupport (fun y => ‖E n y‖^2) :=
      hComp.comp_left (g := fun v : W => ‖v‖^2) (by simp)
    exact ((continuous_referenceBaseDensity g hg L lam).mul ((hE n).norm.pow 2)).integrable_of_hasCompactSupport hSq.mul_left
  have hUi (i : ι) (n : ℕ) : Integrable (fun y => referenceDensityFamily g L (lam,y) * ‖U i n y‖^2) := by
    have hComp : HasCompactSupport (U i n) := hS.of_isClosed_subset (isClosed_tsupport _) (hSupp i n)
    have hSq : HasCompactSupport (fun y => ‖U i n y‖^2) :=
      hComp.comp_left (g := fun v : V => ‖v‖^2) (by simp)
    exact ((continuous_referenceBaseDensity g hg L lam).mul ((hU i n).norm.pow 2)).integrable_of_hasCompactSupport hSq.mul_left
  let K : ℝ := C^2 * (Fintype.card ι : ℝ)
  have hNorm (n : ℕ) (y : R3) : ‖E n y‖ ≤ C * ∑ i, ‖U i n y‖ := by
    by_cases hy : y ∈ S
    · calc
        _ ≤ ∑ i, ‖A i y (U i n y)‖ := norm_sum_le _ _
        _ ≤ ∑ i, C*‖U i n y‖ := Finset.sum_le_sum (fun i hi =>
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hAC i y hy) (norm_nonneg _)))
        _ = _ := (Finset.mul_sum _ _ _).symm
    · have hz (i : ι) : U i n y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hy (hSupp i n h))
      simp only [E,hz,map_zero,Finset.sum_const_zero,norm_zero,mul_zero,le_refl]
  have hSq (n : ℕ) (y : R3) : ‖E n y‖^2 ≤ K * ∑ i, ‖U i n y‖^2 := by
    have hSum : 0 ≤ ∑ i, ‖U i n y‖ := Finset.sum_nonneg (fun i hi => norm_nonneg _)
    have hCS : (∑ i, ‖U i n y‖)^2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖U i n y‖^2 := by
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : ι => ‖U i n y‖))
    calc
      _ ≤ (C * ∑ i, ‖U i n y‖)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hSum)).mpr (hNorm n y)
      _ = C^2 * (∑ i, ‖U i n y‖)^2 := mul_pow _ _ _
      _ ≤ C^2 * ((Fintype.card ι : ℝ) * ∑ i, ‖U i n y‖^2) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ = K * ∑ i, ‖U i n y‖^2 := by dsimp only [K]; ring
  have hBound (n : ℕ) :
      (∫ y, referenceDensityFamily g L (lam,y) * ‖E n y‖^2) ≤
      K * ∑ i, ∫ y, referenceDensityFamily g L (lam,y) * ‖U i n y‖^2 := by
    have hRhsI : Integrable (fun y => K * ∑ i, referenceDensityFamily g L (lam,y) * ‖U i n y‖^2) :=
      (integrable_finsetSum Finset.univ (fun i hi => hUi i n)).const_mul K
    calc
      _ ≤ ∫ y, K * ∑ i, referenceDensityFamily g L (lam,y) * ‖U i n y‖^2 := by
        apply integral_mono (hEi n) hRhsI
        intro y
        have hw : 0 ≤ referenceDensityFamily g L (lam,y) := (referenceDensityFamily_pos g hg L (lam,y)).le
        have h := mul_le_mul_of_nonneg_left (hSq n y) hw
        simpa only [Finset.mul_sum,mul_left_comm,mul_assoc] using h
      _ = _ := by
        rw [integral_const_mul,integral_finsetSum Finset.univ (fun i hi => hUi i n)]
  have hUpper : Tendsto (fun n : ℕ => K * ∑ i,
      ∫ y, referenceDensityFamily g L (lam,y) * ‖U i n y‖^2) atTop (𝓝 0) := by
    have h := (tendsto_finsetSum Finset.univ (fun i hi => hLimit i)).const_mul K
    simpa only [Finset.sum_const_zero,mul_zero] using h
  exact squeeze_zero (fun n => integral_nonneg (fun y => mul_nonneg
    ((referenceDensityFamily_pos g hg L (lam,y)).le) (sq_nonneg _))) hBound hUpper

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
