import Calderon.MixedKernelConstruction.MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  ExteriorSource ConnectionError MetricOperator MetricVolume
  ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
  CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open OAI.AnisotropicCalderon.MixedKernelConstructionTask.Geometry
attribute [local instance] Classical.propDecidable

theorem exists_uniform_coarse_closed_products_known_cross
    (S : KnownSideSourceData) (B s0 s1 α : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1)
    (hα : 0 < α) (hα4 : α ≤ 1/4) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ lam ∈ Ioc (0:ℝ) lambda0,
      ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lam • p) = 0 → ∀ s ∈ Icc s0 s1,
      let η := s/20
      let c := p-η • EuclideanSpace.single (2:Fin 3) (1:ℝ)
      (closedBall c ((1-α/2)*η) ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆ initialCross S lam) ∧
      (closedBall c (3*η) ×ˢ closedBall (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8) ⊆ initialCross S lam) := by
  have hs1 : 0 < s1 := hs0.trans_le hss
  have he : 0 < α*s0/80 := by positivity
  obtain ⟨l1,hl1,Hsep⟩ := exists_uniform_scaled_separating_error S (B+2*s1+1) (α*s0/80) (by positivity) he
  obtain ⟨l2,hl2,Hcross⟩ := exists_uniform_original_lower_cross S (B+2*s1+1) (α*s0/80) (by positivity) he
  refine ⟨min l1 l2,lt_min hl1 hl2,?_⟩
  intro lam hlamI p hp hp0 s hs
  have hlam := hlamI.1
  have hl1' : lam ≤ l1 := hlamI.2.trans (min_le_left _ _)
  have hl2' : lam ≤ l2 := hlamI.2.trans (min_le_right _ _)
  have hspos : 0 < s := hs0.trans_le hs.1
  have hpB : ‖p‖ ≤ B + 2 * s1 + 1 := by linarith
  have hp2 : |p 2| ≤ α * s0 / 80 / 2 := by
    have h := (Hsep lam hlam hl1' p hpB).2.1
    rw [hp0, zero_sub, abs_neg, abs_mul, abs_of_pos hlam, mul_div_assoc] at h
    exact le_of_mul_le_mul_left h hlam
  have hp2' := (abs_le.mp hp2).2
  set η : ℝ := s / 20 with hη_def
  have hη : 0 < η := by positivity
  set c : R3 := p - η • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) with hc_def
  have he2n : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by
    rw [EuclideanSpace.norm_single, norm_one]
  have hpc : ‖p - c‖ = η := by
    rw [hc_def, sub_sub_cancel, norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hη, mul_one]
  have hcB : ‖c‖ ≤ B + s1 / 20 := by
    have h := norm_sub_le p (η • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    rw [norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hη, mul_one] at h
    rw [hc_def]
    linarith [hs.2]
  have hηI : η ∈ Icc (s0 / 20) (s1 / 20) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hc2 : c 2 = p 2 - η := by simp [hc_def, PiLp.sub_apply, PiLp.smul_apply]
  have hαη : α * η = α * s / 20 := by rw [hη_def]; ring
  have hαη0 : 0 ≤ α * η := by positivity
  have hαs : α * s0 ≤ α * s := mul_le_mul_of_nonneg_left hs.1 hα.le
  have hαs0 : α * s0 ≤ 1 / 4 * s0 := mul_le_mul_of_nonneg_right hα4 hs0.le
  have hrow : closedBall c ((1 - α / 2) * η) ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s} ⊆ initialCross S lam := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hxc : ‖x - c‖ ≤ (1 - α / 2) * η := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    have hxp : ‖x - p‖ ≤ ‖x - c‖ + ‖p - c‖ := by
      have hh := norm_sub_le (x - c) (p - c)
      rwa [sub_sub_sub_cancel_right] at hh
    obtain ⟨hy1, hy2⟩ := hy
    have hcoord : (x - c) 2 ≤ ‖x - c‖ := (abs_le.mp (abs_coord_le_norm (x - c) 2)).2
    have hsum : x 2 = (x - c) 2 + c 2 := by simp only [PiLp.sub_apply]; ring
    have hx2 : x 2 ≤ -(α * s0 / 80) := by linarith
    have hxn : ‖x‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le x p
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le y p
      linarith [hs.2]
    have hne : x ≠ y := by
      intro hxy
      rw [← hxy] at hy1
      linarith
    exact Hcross lam hlam hl2' (x, y) hxn hyn hne (Or.inl hx2)
  have hobs : closedBall c (3 * η) ×ˢ
      closedBall (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s / 8) ⊆ initialCross S lam := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hxc : ‖x - c‖ ≤ 3 * η := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    have hxp : ‖x - p‖ ≤ ‖x - c‖ + ‖p - c‖ := by
      have hh := norm_sub_le (x - c) (p - c)
      rwa [sub_sub_sub_cancel_right] at hh
    have hyc : ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ≤ s / 8 := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    have hse : ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = s := by
      rw [norm_smul, he2n, Real.norm_eq_abs, abs_of_pos hspos, mul_one]
    have hyp1 : ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤
        ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ + ‖y - p‖ := by
      have hh := norm_sub_le (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) (y - p)
      have he' : y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) - (y - p) =
          s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by abel
      rwa [he'] at hh
    have hyp2 : ‖y - p‖ ≤ ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ +
        ‖s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ := by
      have hh := norm_sub_le (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
        (s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      have he' : y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) -
          s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) = y - p := by abel
      rwa [he'] at hh
    have hcoord : (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) 2 ≤
        ‖y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ :=
      (abs_le.mp (abs_coord_le_norm _ 2)).2
    have hj2 : (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 = p 2 - s := by
      simp [PiLp.sub_apply, PiLp.smul_apply]
    have hsum : y 2 = (y - (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) 2 +
        (p - s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 := by
      simp only [PiLp.sub_apply]; ring
    have hy2 : y 2 ≤ -(α * s0 / 80) := by linarith [hs.1]
    have hxn : ‖x‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le x p
      linarith [hs.2]
    have hyn : ‖y‖ ≤ B + 2 * s1 + 1 := by
      have h := norm_sub_norm_le y p
      linarith [hs.2]
    have hne : x ≠ y := by
      intro hxy
      rw [← hxy] at hyp1 hyc
      linarith
    exact Hcross lam hlam hl2' (x, y) hxn hyn hne (Or.inr hy2)
  exact ⟨hrow,hobs⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
