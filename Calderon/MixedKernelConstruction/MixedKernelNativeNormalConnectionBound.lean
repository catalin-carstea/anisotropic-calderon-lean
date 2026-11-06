import Calderon.MixedKernelConstruction.MixedKernelNativeMetricQuadraticRemainder
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator
open scoped ContDiff InnerProductSpace Topology

/-- Actual full-room metric coercivity supplies its genuine inverse and a uniform norm bound. -/
theorem packet_nativeMetric_inverse_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-P.y0‖ ≤ 4*P.rho) (r : ℝ) (hr : |r| ≤ 4*P.rho)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    let G := conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),z))
    G.IsInvertible ∧ ‖Ring.inverse G‖ ≤ 2 := by
  intro G
  have hData : ConformalReferenceFramedMetricData S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo := P.native_data.1.1
  rcases hData with ⟨_,_,_,_,_,_,hRoom,_⟩
  have hsmall : 4*P.rho ≤ P.epsGeo := P.native_data.1.2.2.1
  obtain ⟨_,_,_,_,_,_,hLower,_⟩ := hRoom lam hlam y (hy.trans hsmall) r (hr.trans hsmall) z hz
  have hInv : G.IsInvertible := by
    apply isInvertible_compactChart_endomorphism
    intro U V heq
    have hz0 : G (U-V) = 0 := by rw [map_sub,heq,sub_self]
    have hh := hLower (U-V)
    change (1/2 : ℝ)*‖U-V‖^2 ≤ ⟪G (U-V),U-V⟫_ℝ at hh
    rw [hz0,inner_zero_left] at hh
    have hn : ‖U-V‖ = 0 := by nlinarith [norm_nonneg (U-V)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  refine ⟨hInv,?_⟩
  rw [ContinuousLinearMap.ringInverse_eq_inverse]
  apply ContinuousLinearMap.opNorm_le_bound (ContinuousLinearMap.inverse G) (by norm_num)
  intro U
  have hh := hLower (ContinuousLinearMap.inverse G U)
  change (1/2 : ℝ)*‖ContinuousLinearMap.inverse G U‖^2 ≤
    ⟪G (ContinuousLinearMap.inverse G U),ContinuousLinearMap.inverse G U⟫_ℝ at hh
  rw [hInv.self_apply_inverse] at hh
  have hc := real_inner_le_norm U (ContinuousLinearMap.inverse G U)
  by_cases hn : ‖ContinuousLinearMap.inverse G U‖ = 0
  · rw [hn]
    positivity
  · have hnpos : 0 < ‖ContinuousLinearMap.inverse G U‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hm : ‖ContinuousLinearMap.inverse G U‖*‖ContinuousLinearMap.inverse G U‖ ≤
        (2*‖U‖)*‖ContinuousLinearMap.inverse G U‖ := by nlinarith
    exact (mul_le_mul_iff_left₀ hnpos).mp hm

/-- The exact smooth remainder controls the derivative of the ACTUAL spatial metric slice. -/
theorem exists_packet_nativeMetric_spatial_derivative_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho → ∀ r : ℝ, |r| ≤ 4*P.rho →
      ∀ z : R3, ‖z‖ < 2 →
        ‖fderiv ℝ (fun w : R3 => conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w))) z‖ ≤
          r^2*D := by
  obtain ⟨D,hD,H⟩ := exists_nativeMetricQuadraticRemainder_compact_bounds S L P 1
  have hA : ContDiff ℝ ∞ (nativeMetricQuadraticRemainder S L P) := contDiff_nativeMetricQuadraticRemainder S L P
  refine ⟨D,hD,?_⟩
  intro lam hlam y hy r hr z hz
  let a : ReferenceEndpointVariables := (lam,((y,r),z))
  let AS : R3 → R3 →L[ℝ] R3 := fun w => nativeMetricQuadraticRemainder S L P (lam,((y,r),w))
  have ha : a ∈ conformalReferenceFramedMetricRoom P.y0 (4*P.rho) := by
    refine ⟨hlam,⟨⟨?_,abs_le.mp hr⟩,?_⟩⟩
    · simpa only [mem_closedBall,dist_eq_norm] using hy
    · simpa only [mem_closedBall,dist_zero_right] using hz.le
  have hDA : ‖fderiv ℝ (nativeMetricQuadraticRemainder S L P) a‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_one] using H 1 le_rfl a ha
  have hMap := (hasFDerivAt_const (𝕜 := ℝ) lam z).prodMk
    ((hasFDerivAt_const (𝕜 := ℝ) (y,r) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
  have hAS := (hA.differentiable (by simp) a).hasFDerivAt.comp z hMap
  simp only [Function.comp_def,id_eq] at hAS
  change HasFDerivAt AS _ z at hAS
  have hASnorm : ‖fderiv ℝ AS z‖ ≤ D := by
    apply ContinuousLinearMap.opNorm_le_bound (fderiv ℝ AS z) hD
    intro V
    rw [hAS.fderiv]
    change ‖fderiv ℝ (nativeMetricQuadraticRemainder S L P) a ((0 : ℝ),(((0 : R3),(0 : ℝ)),V))‖ ≤ D*‖V‖
    have hh := (fderiv ℝ (nativeMetricQuadraticRemainder S L P) a).le_opNorm
      ((0 : ℝ),(((0 : R3),(0 : ℝ)),V))
    have hinorm : ‖((0 : ℝ),(((0 : R3),(0 : ℝ)),V))‖ = ‖V‖ := by simp [Prod.norm_def]
    rw [hinorm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hDA (norm_nonneg V))
  have hModel := (hasFDerivAt_const (ContinuousLinearMap.id ℝ R3) z).add
    ((hAS.differentiableAt.hasFDerivAt).const_smul (r^2))
  have hNear : (fun w : R3 => conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w))) =ᶠ[𝓝 z]
      (fun w : R3 => ContinuousLinearMap.id ℝ R3+r^2 • AS w) := by
    have hNb : ∀ᶠ w : R3 in 𝓝 z, w ∈ ball (0 : R3) 2 :=
      isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hz)
    filter_upwards [hNb] with w hw
    exact native_normal_metric_eq_id_add_radius_sq S L P lam hlam y hy r w (ball_subset_closedBall hw)
  have hActual := hModel.congr_of_eventuallyEq hNear
  rw [hActual.fderiv]
  simp only [zero_add]
  change ‖(r^2 : ℝ) • fderiv ℝ AS z‖ ≤ r^2*D
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sq_nonneg r) hD)
  intro U
  change ‖(r^2 : ℝ) • (fderiv ℝ AS z U)‖ ≤ (r^2*D)*‖U‖
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (sq_nonneg r) hD) (norm_nonneg U))
  intro V
  change ‖(r^2 : ℝ) • fderiv ℝ AS z U V‖ ≤ (r^2*D)*‖U‖*‖V‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
  have hEval : ‖fderiv ℝ AS z U V‖ ≤ D*‖U‖*‖V‖ :=
    ((fderiv ℝ AS z U).le_opNorm V).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ AS z).le_opNorm U).trans
        (mul_le_mul_of_nonneg_right hASnorm (norm_nonneg U))) (norm_nonneg V))
  calc
    r^2*‖fderiv ℝ AS z U V‖ ≤ r^2*(D*‖U‖*‖V‖) := mul_le_mul_of_nonneg_left hEval (sq_nonneg r)
    _ = _ := by ring

/-- The literal native coordinate connection is uniformly quadratic in the signed radius. -/
theorem exists_packet_native_normal_connection_quadratic_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho → ∀ r : ℝ, |r| ≤ 4*P.rho →
      ∀ z : R3, ‖z‖ < 2 →
        let G : R3 → R3 →L[ℝ] R3 := fun w =>
          conformalReferenceFramedNormalMetric S.g1 L P.Phi (lam,((y,r),w))
        ‖coordinateConnectionField (inverseMetricField G) G z‖ ≤ C*r^2 := by
  obtain ⟨D,hD,H⟩ := exists_packet_nativeMetric_spatial_derivative_bound S L P
  refine ⟨3*D+1,by positivity,?_⟩
  intro lam hlam y hy r hr z hz G
  have hI := (packet_nativeMetric_inverse_bound S L P lam hlam y hy r hr z
    (by simpa only [mem_closedBall,dist_zero_right] using hz.le)).2
  have hDG := H lam hlam y hy r hr z hz
  change ‖fderiv ℝ G z‖ ≤ r^2*D at hDG
  have hh := norm_coordinateConnectionLinearMap_le (inverseMetricField G z) (fderiv ℝ G z)
  change ‖coordinateConnectionField (inverseMetricField G) G z‖ ≤
    (3/2 : ℝ)*‖inverseMetricField G z‖*‖fderiv ℝ G z‖ at hh
  have hi : ‖inverseMetricField G z‖ ≤ 2 := hI
  have hmul := mul_le_mul hi hDG (norm_nonneg (fderiv ℝ G z)) (by norm_num : (0 : ℝ) ≤ 2)
  have hmul' := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 3/2)
  rw [← mul_assoc] at hmul'
  have hh' := hh.trans hmul'
  nlinarith [sq_nonneg r]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
