import MixedKernelNativeCrossSeries
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

theorem product_rowIntegral_data (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω)
    (F : R3 × R3 → ℝ) (hF : ContDiffOn ℝ ∞ F Ω)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ Ω)
    (q : R3 → ℝ) (hq : MemLp q 2 ((volume : Measure R3).restrict U)) :
    ContDiffOn ℝ ∞ (fun y => ∫ x, F (x,y) * q x
        ∂((volume : Measure R3).restrict U)) V ∧
    (∀ y ∈ V, ∀ v : R3, fderiv ℝ (fun y => ∫ x, F (x,y) * q x
        ∂((volume : Measure R3).restrict U)) y v =
      ∫ x, q x * fderiv ℝ (fun y => F (x,y)) y v
        ∂((volume : Measure R3).restrict U)) ∧
    (∀ y ∈ V, ∀ v w : R3, fderiv ℝ (fderiv ℝ (fun y => ∫ x, F (x,y) * q x
        ∂((volume : Measure R3).restrict U))) y v w =
      ∫ x, q x * fderiv ℝ (fderiv ℝ (fun y => F (x,y))) y v w
        ∂((volume : Measure R3).restrict U)) ∧
    (∀ y ∈ V, ∀ v : R3, Integrable (fun x =>
      q x * fderiv ℝ (fun y => F (x,y)) y v)
        ((volume : Measure R3).restrict U)) ∧
    (∀ y ∈ V, ∀ v w : R3, Integrable (fun x =>
      q x * fderiv ℝ (fderiv ℝ (fun y => F (x,y))) y v w)
        ((volume : Measure R3).restrict U)) := by
  set m : Measure R3 := (volume : Measure R3).restrict U with hm
  haveI : IsFiniteMeasure m :=
    isFiniteMeasure_restrict.mpr ((measure_mono hUK).trans_lt hK.measure_lt_top).ne
  have hq1 : Integrable q m := hq.integrable (by norm_num)
  choose B _hB0 hB using fun n : ℕ =>
    exists_bound_partialSecondJet n F (Ω) hΩ hF K J hK hJ hcross
  have hmem : ∀ x ∈ U, ∀ y ∈ V, (x,y) ∈ Ω :=
    fun x hx y hy => hcross ⟨hUK hx, hVJ hy⟩
  have hRow : ∀ᵐ x ∂m, ContDiffOn ℝ ∞ (fun y => F (x,y)) V := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => hmem x hx y hy)
  have hmeas : ∀ n : ℕ, ∀ y ∈ V, AEStronglyMeasurable
      (fun x => q x • iteratedFDeriv ℝ n (fun y => F (x,y)) y) m := by
    intro n y hy
    have hc : ContinuousOn (fun x => partialSecondJet n F (x,y)) U :=
      (continuousOn_partialSecondJet n F _ hΩ hF).comp
        (continuousOn_id.prodMk continuousOn_const) (fun x hx => hmem x hx y hy)
    exact hq.aestronglyMeasurable.smul (hc.aestronglyMeasurable hU.measurableSet)
  have hBound : ∀ n : ℕ, ∀ᵐ x ∂m, ∀ y ∈ V,
      ‖q x • iteratedFDeriv ℝ n (fun y => F (x,y)) y‖ ≤ B n * |q x| := by
    intro n
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx y hy
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB n x (hUK hx) y (hVJ hy)) (abs_nonneg _)
  have hbInt : ∀ n : ℕ, Integrable (fun x => B n * |q x|) m :=
    fun n => hq1.abs.const_mul (B n)
  have hInt : ∀ (n : ℕ) (y : R3), y ∈ V →
      Integrable (fun x => q x • iteratedFDeriv ℝ n (fun y => F (x,y)) y) m := by
    intro n y hy
    refine Integrable.mono' (hbInt n) (hmeas n y hy) ?_
    filter_upwards [hBound n] with x hx using hx y hy
  have hmain := ExteriorSource.contDiffOn_integral_and_fderiv_of_dominated_iteratedFDeriv
    m V hV (fun x y => F (x,y)) q hRow hInt (fun n x => B n * |q x|) hbInt hBound
  obtain ⟨hs, hd1, hd2⟩ := hmain
  refine ⟨hs, hd1, hd2, ?_, ?_⟩
  · intro y hy v
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => R3) ℝ
      (fun _ => v)).integrable_comp (hInt 1 y hy)
    refine h.congr (Eventually.of_forall fun x => ?_)
    change (q x • iteratedFDeriv ℝ 1 (fun y => F (x,y)) y) (fun _ => v) = _
    rw [ContinuousMultilinearMap.smul_apply, iteratedFDeriv_one_apply, smul_eq_mul]
  · intro y hy v w
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => R3) ℝ
      ![v, w]).integrable_comp (hInt 2 y hy)
    refine h.congr (Eventually.of_forall fun x => ?_)
    change (q x • iteratedFDeriv ℝ 2 (fun y => F (x,y)) y) ![v, w] = _
    rw [ContinuousMultilinearMap.smul_apply, iteratedFDeriv_two_apply, smul_eq_mul]
    rfl

theorem product_rowIntegral_secondPDE (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (F : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lam F Ω)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ Ω)
    (q : R3 → ℝ) (hq : MemLp q 2 ((volume : Measure R3).restrict U)) :
    ContDiffOn ℝ ∞ (fun y => ∫ x, F (x,y) * q x
        ∂((volume : Measure R3).restrict U)) V ∧
    ∀ y ∈ V, normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => ∫ x,
      F (x,y) * q x ∂((volume : Measure R3).restrict U)) y = 0 := by
  obtain ⟨hs, hd1, hd2, hi1, hi2⟩ :=
    product_rowIntegral_data Ω hΩ F hF.1 U V K J hU hV hK hJ hUK hVJ hcross q hq
  refine ⟨hs, fun y hy => ?_⟩
  have hA : ∀ i j : Fin 3, DifferentiableAt ℝ
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i j) y :=
    fun i j => (contDiff_dilatedSecondPrincipal S lam i j).differentiable (by simp) y
  have hT : DifferentiableAt ℝ (fderiv ℝ (fun y => ∫ x, F (x,y) * q x
      ∂((volume : Measure R3).restrict U))) y :=
    ((hs.contDiffAt (hV.mem_nhds hy)).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have hH : ∀ᵐ x ∂((volume : Measure R3).restrict U),
      DifferentiableAt ℝ (fderiv ℝ (fun y => F (x,y))) y := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have hrow : ContDiffOn ℝ ∞ (fun y => F (x,y)) V :=
      hF.1.comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => hcross ⟨hUK hx, hVJ hy⟩)
    exact ((hrow.contDiffAt (hV.mem_nhds hy)).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have hzero : ∀ᵐ x ∂((volume : Measure R3).restrict U),
      normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => F (x,y)) y = 0 := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hF.2.2 (x,y)
      (hcross ⟨hUK hx, hVJ hy⟩)
  have hI := divCoeffGrad_integral ((volume : Measure R3).restrict U)
    (principalCoefficient (dilatedMetric S.g2 lam)) y hA _
    (fun x y => F (x,y)) q hT hH (hd1 y hy) (hd2 y hy) (hi1 y hy) (hi2 y hy)
  rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad,
    hI, ← integral_const_mul]
  have hz : (fun x => normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam,y) *
      (vol (dilatedMetric S.g2 lam) y)⁻¹ *
      (q x * divCoeffGrad (principalCoefficient (dilatedMetric S.g2 lam))
        (fun y => F (x,y)) y)) =ᵐ[(volume : Measure R3).restrict U]
      fun _ => (0 : ℝ) := by
    filter_upwards [hzero] with x hx
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv,
      coordinateFluxDivergence_eq_divCoeffGrad] at hx
    calc _ = q x * (normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam,y) *
          (vol (dilatedMetric S.g2 lam) y)⁻¹ *
          divCoeffGrad (principalCoefficient (dilatedMetric S.g2 lam))
            (fun y => F (x,y)) y) := by ring
      _ = 0 := by rw [hx, mul_zero]
  rw [integral_congr_ae hz, integral_zero]

theorem product_integralCoefficient_secondPDE (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (F : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lam F Ω)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ Ω) (q : R3 → ℝ)
    (hq : MemLp q 2 ((volume : Measure R3).restrict U)) (c : ℝ) :
    ContDiffOn ℝ ∞ (integralCoefficient ((volume : Measure R3).restrict U) F q c) V ∧
    ∀ y ∈ V, normalizedSecondLaplacian S.g1 S.g2 L lam
      (integralCoefficient ((volume : Measure R3).restrict U) F q c) y = 0 := by
  have heq : integralCoefficient ((volume : Measure R3).restrict U) F q c =
      fun y => ∫ x, F (x,y) * (c * q x) ∂((volume : Measure R3).restrict U) := by
    funext y
    rw [integralCoefficient, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [heq]
  exact product_rowIntegral_secondPDE S L lam Ω hΩ F hF U V K J hU hV hK hJ hUK hVJ hcross
    _ (hq.const_mul c)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
