import Calderon.ActualScaledCoordinateChartGeometry
import Calderon.ActualGeneralGreenInverseDistance
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise NNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError ExteriorSource DirichletFamily
attribute [local instance] Classical.propDecidable

theorem exists_uniform_dilated_original_kernel_inverse_distance
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (X : R3 → R3) (U : Set R3) (hU : IsOpen U) (h0 : (0:R3) ∈ U)
    (hX : ContDiffOn ℝ ∞ X U)
    (hJ : IsUnit (coordinateJacobianMatrix X 0).det)
    (hXR : ∀ x ∈ U, X x ∈ (radiusTwoOpens : Set R3))
    (B : ℝ) (hB : 0 < B) :
    ∃ (lambda0 M : ℝ), 0 < lambda0 ∧ lambda0 ≤ 1 ∧ 0 < M ∧
      ∀ lambda ∈ Ioc (0:ℝ) lambda0, ∀ x y : R3, ‖x‖ ≤ B → ‖y‖ ≤ B → x ≠ y →
        ∃ (hx : lambda • x ∈ U) (hy : lambda • y ∈ U),
          |lambda * G ⟨X (lambda • y),hXR _ hy⟩ (X (lambda • x))| ≤ M / dist x y := by
  obtain ⟨lambda0,c,b,hl,hl1,hc,hb,hb2,hImage,hSep⟩ :=
    exists_scaled_coordinate_chart_geometry X U hU h0 hX hJ (hXR 0 h0) B hB
  obtain ⟨C,hC,hGreen⟩ := exists_uniform_radiusTwoSourceKernel_compact_inverse_distance_bound
    hreg hcalc g hg K G hData b hb hb2
  refine ⟨lambda0,C/c,hl,hl1,div_pos hC hc,?_⟩
  intro lambda hlambda x y hxB hyB hxy
  obtain ⟨hx,hxImage⟩ := hImage lambda hlambda x hxB
  obtain ⟨hy,hyImage⟩ := hImage lambda hlambda y hyB
  refine ⟨hx,hy,?_⟩
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hsep := hSep lambda hlambda x y hxB hyB
  have hdX : 0 < dist (X (lambda • x)) (X (lambda • y)) :=
    lt_of_lt_of_le (mul_pos (mul_pos hc hlambda.1) hd) hsep
  have hne : (⟨X (lambda • y),hXR _ hy⟩ : ↥(radiusTwoOpens : Set R3)) ≠
      ⟨X (lambda • x),hXR _ hx⟩ := by
    intro heq
    have hv := congrArg Subtype.val heq
    have : dist (X (lambda • x)) (X (lambda • y)) = 0 := dist_eq_zero.mpr hv.symm
    linarith
  have hGreenBound := hGreen ⟨X (lambda • y),hXR _ hy⟩
    ⟨X (lambda • x),hXR _ hx⟩ hyImage hxImage hne
  rw [dist_comm] at hGreenBound
  rw [abs_mul,abs_of_pos hlambda.1]
  calc
    _ ≤ lambda * (C / dist (X (lambda • x)) (X (lambda • y))) :=
      mul_le_mul_of_nonneg_left hGreenBound hlambda.1.le
    _ = lambda * C / dist (X (lambda • x)) (X (lambda • y)) := by ring
    _ ≤ (C/c)/dist x y := by
      apply (div_le_div_iff₀ hdX hd).mpr
      have hm := mul_le_mul_of_nonneg_left hsep (div_nonneg hC.le hc.le)
      calc
        lambda * C * dist x y = C/c * (c*lambda*dist x y) := by field_simp
        _ ≤ C/c * dist (X (lambda • x)) (X (lambda • y)) := hm

theorem exists_uniform_initialKernel_inverse_distance_bound
    (S : KnownSideSourceData) (B : ℝ) (hB : 0 < B) :
    ∃ (lambda0 M : ℝ), 0 < lambda0 ∧ lambda0 ≤ 1 ∧ 0 < M ∧
      ∀ lambda ∈ Ioc (0:ℝ) lambda0, ∀ v : R3 × R3,
      ‖v.1‖ ≤ B → ‖v.2‖ ≤ B → v.1 ≠ v.2 →
        |initialKernel S lambda v| ≤ M/dist v.1 v.2 := by
  obtain ⟨l1,M1,hl1,hl11,hM1,h1⟩ := exists_uniform_dilated_original_kernel_inverse_distance
    S.hreg S.hcalc S.original1 S.original1_admissible S.K1 S.G1 S.kernel1.1
    S.Xi1 S.coordinateRoom S.coordinateRoom_open S.origin_mem S.Xi1_smooth
    (S.Xi1_jacobian 0 S.origin_mem) S.Xi1_room B hB
  obtain ⟨l2,M2,hl2,hl21,hM2,h2⟩ := exists_uniform_dilated_original_kernel_inverse_distance
    S.hreg S.hcalc S.original2 S.original2_admissible S.K2 S.G2 S.kernel2.1
    S.Xi2 S.coordinateRoom S.coordinateRoom_open S.origin_mem S.Xi2_smooth
    (S.Xi2_jacobian 0 S.origin_mem) S.Xi2_room B hB
  refine ⟨min l1 l2,max M1 M2,lt_min hl1 hl2,(min_le_left _ _).trans hl11,
    hM1.trans_le (le_max_left _ _),?_⟩
  intro lambda hlambda v hxB hyB hxy
  have hli1 : lambda ∈ Ioc (0:ℝ) l1 := ⟨hlambda.1,hlambda.2.trans (min_le_left _ _)⟩
  have hli2 : lambda ∈ Ioc (0:ℝ) l2 := ⟨hlambda.1,hlambda.2.trans (min_le_right _ _)⟩
  have hd : 0 < dist v.1 v.2 := dist_pos.mpr hxy
  by_cases hW : lambda • v.2 ∈ S.W
  · obtain ⟨hx,hy,hbound⟩ := h1 lambda hli1 v.1 v.2 hxB hyB hxy
    simp only [initialKernel,if_pos hW,dilatedKernel1,coordinateKernel1,dif_pos hy]
    exact hbound.trans (div_le_div_of_nonneg_right (le_max_left _ _) hd.le)
  · obtain ⟨hx,hy,hbound⟩ := h2 lambda hli2 v.1 v.2 hxB hyB hxy
    simp only [initialKernel,if_neg hW,dilatedKernel2,coordinateKernel2,dif_pos hy]
    exact hbound.trans (div_le_div_of_nonneg_right (le_max_right _ _) hd.le)

theorem exists_uniform_initialKernel_fixed_separation_bound
    (S : KnownSideSourceData) (B d : ℝ) (hB : 0 < B) (hd : 0 < d) :
    ∃ (lambda0 M : ℝ), 0 < lambda0 ∧ lambda0 ≤ 1 ∧ 0 < M ∧
      ∀ lambda ∈ Ioc (0:ℝ) lambda0, ∀ v ∈ fixedSeparationSet B d,
        |initialKernel S lambda v| ≤ M := by
  obtain ⟨lambda0,M,hl,hl1,hM,hBound⟩ := exists_uniform_initialKernel_inverse_distance_bound S B hB
  refine ⟨lambda0,M/d,hl,hl1,div_pos hM hd,?_⟩
  intro lambda hlambda v hv
  rcases hv with ⟨hx,hy,hsep⟩
  have hdxy : 0 < dist v.1 v.2 := hd.trans_le (by simpa only [dist_eq_norm] using hsep)
  have h := hBound lambda hlambda v hx hy (dist_pos.mp hdxy)
  exact h.trans (div_le_div_of_nonneg_left hM.le hd (by simpa only [dist_eq_norm] using hsep))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
